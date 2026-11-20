#!/usr/bin/env python3
"""
UK COUNCIL VOTEWATCH — AUTOMATED MODERN.GOV INGESTION PIPELINE
1. sync-roster        -> Syncs councillors & date-stamped tenures via Modern.Gov XML
2. crawl-divisions    -> Pulls 2019–2026 Council meetings & minutes via Modern.Gov XML + PDF fallback
3. generate-briefings -> Generates 4-part journalistic briefings with automatic free-tier rate pacing
4. full-sync          -> Runs all three stages sequentially
"""

import argparse
import html
import io
import json
import logging
import os
import re
import sys
import time
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urljoin

import pdfplumber
import psycopg
from bs4 import BeautifulSoup
from curl_cffi import requests as cffi_requests
from dotenv import load_dotenv
from psycopg.rows import dict_row
from psycopg.types.json import Jsonb

try:
    from google import genai
    from google.genai import types
except ImportError:
    genai = None
    types = None

load_dotenv()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("votewatch-worker")

BROWSER_HEADERS = {
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-GB,en;q=0.9",
}

KNOWN_COUNCIL_CIDS = {
    "E06000033": [131],  # Southend-on-Sea: 'The Council'
}


def create_http_session() -> cffi_requests.Session:
    proxy = os.environ.get("PROXY_URL")
    proxies = {"http": proxy, "https": proxy} if proxy else None
    return cffi_requests.Session(impersonate="chrome", headers=BROWSER_HEADERS, proxies=proxies)


def get_db_connection():
    db_url = os.environ.get("DATABASE_URL")
    if not db_url:
        log.error("DATABASE_URL environment variable is missing.")
        sys.exit(1)
    return psycopg.connect(db_url.strip(), row_factory=dict_row)


def normalize_ward_key(name: str) -> str:
    s = (name or "").lower().replace("’", "").replace("'", "").strip()
    s = re.sub(r"\s+ward$", "", s).strip()
    return s


def normalize_party_and_group(raw_party: str) -> Tuple[str, str]:
    p = (raw_party or "").strip()
    low = p.lower()
    if "labour" in low:
        return (p or "Labour", "Labour Group")
    if "conservative" in low:
        return (p or "Conservative", "Conservative Group")
    if "reform" in low:
        return (p or "Reform UK", "Reform UK Group")
    if "liberal democrat" in low or "lib dem" in low:
        return (p or "Liberal Democrats", "Liberal Democrat Group")
    if "green" in low:
        return (p or "Green", "Green Group")
    if "rochford" in low or "southend east" in low:
        return ("Independent", "Rochford & Southend East Independents Group")
    if "independent" in low or "non-aligned" in low or "not aligned" in low:
        return (p or "Independent (Non-Aligned)", "Not Aligned")
    return (p or "Independent", p or "Not Aligned")


def extract_surname(full_name: str) -> str:
    clean = re.sub(r"^(Councillor|Cllr|Doctor|Dr|Prof|Rev|Sir|Dame)\s+", "", full_name.strip(), flags=re.I)
    parts = clean.replace("’", "'").split()
    return parts[-1].lower() if parts else ""


def generate_name_aliases(full_name: str, allow_bare_surname: bool = True) -> List[str]:
    clean = re.sub(r"^(Councillor|Cllr|Doctor|Dr|Prof|Rev|Sir|Dame)\s+", "", full_name.strip(), flags=re.I)
    clean = clean.replace("’", "'")
    parts = clean.split()
    aliases = {full_name.strip(), clean}
    if len(parts) >= 2:
        surname = parts[-1]
        first_initial = parts[0][0]
        if allow_bare_surname:
            aliases.add(surname)
        aliases.add(f"{first_initial} {surname}")
        aliases.add(f"{first_initial}. {surname}")
        if "doctor" in full_name.lower() or "dr " in full_name.lower():
            aliases.add(f"Dr {surname}")
        if len(parts) >= 3:
            initials = " ".join(p[0] for p in parts[:-1])
            aliases.add(f"{initials} {surname}")
            aliases.add(f"{parts[0]} {surname}")
    return sorted(aliases)


def classify_motion_category(title: str, context: str = "") -> str:
    text = f"{title} {context}".lower()
    if any(k in text for k in ["budget", "council tax", "revenue", "capital programme", "precept", "treasury", "medium term financial"]):
        return "Budget & Finance"
    if any(k in text for k in ["green belt", "local plan", "development plan", "planning", "housing target", "greenfield"]):
        return "Green Belt & Planning"
    if any(k in text for k in ["parking", "highways", "traffic", "transport", "bus", "cycle", "seafront", "20mph", "pothole"]):
        return "Highways & Transport"
    if any(k in text for k in ["social care", "nhs", "hospital", "children", "send", "homelessness", "public health"]):
        return "Health & Social Care"
    return "Governance & Civic"


def strip_xml_namespaces(xml_bytes: bytes) -> ET.Element:
    root = ET.fromstring(xml_bytes)
    for elem in root.iter():
        if "}" in elem.tag:
            elem.tag = elem.tag.split("}", 1)[1]
    return root


# =========================================================================
# STAGE 1: MODERN.GOV ROSTER & TENURE SYNCER
# =========================================================================
def parse_moderngov_xml_councillors(xml_bytes: bytes) -> List[Dict[str, Any]]:
    root = strip_xml_namespaces(xml_bytes)
    results = []
    for ward_el in root.findall(".//ward"):
        ward_name = (ward_el.findtext("wardtitle") or "").strip()
        for cllr_el in ward_el.findall(".//councillor"):
            uid = (cllr_el.findtext("councillorid") or "").strip()
            full_name = (cllr_el.findtext("fullusername") or "").strip()
            party = (cllr_el.findtext("politicalpartytitle") or "").strip()
            photo = (cllr_el.findtext("photobigurl") or cllr_el.findtext("photosmallurl") or "").strip()
            term_end_raw = (cllr_el.findtext("termofofficeenddate") or "").strip()
            next_year = None
            m = re.search(r"(20\d{2})", term_end_raw)
            if m:
                next_year = int(m.group(1))
            if full_name and ward_name:
                results.append({
                    "external_cms_id": uid or full_name.lower().replace(" ", "-"),
                    "canonical_name": re.sub(r"^(Councillor|Cllr)\s+", "", full_name, flags=re.I).strip(),
                    "ward_name": ward_name,
                    "raw_party": party,
                    "photo_url": photo or None,
                    "next_election_year": next_year,
                })
    return results


def sync_authority_roster(conn, session: cffi_requests.Session, authority: Dict[str, Any]):
    ons_code = authority["ons_code"]
    base_url = authority["base_url"].rstrip("/")
    log.info(f"[{ons_code}] Syncing councillor roster from {base_url}...")

    councillors_data = []
    xml_url = f"{base_url}/mgWebService.asmx/GetCouncillorsByWard"
    try:
        resp = session.get(xml_url, timeout=30)
        if resp.status_code == 200 and b"<" in resp.content:
            councillors_data = parse_moderngov_xml_councillors(resp.content)
            log.info(f"[{ons_code}] Retrieved {len(councillors_data)} councillors via Modern.Gov XML API.")
    except Exception as exc:
        log.warning(f"[{ons_code}] XML endpoint error: {exc}")

    if not councillors_data:
        log.warning(f"[{ons_code}] No councillors extracted. Skipping roster update.")
        return

    surname_counts = Counter(extract_surname(c["canonical_name"]) for c in councillors_data)

    with conn.cursor() as cur:
        cur.execute("SELECT ons_ward_code, name FROM wards WHERE authority_ons_code = %s", (ons_code,))
        ward_lookup = {normalize_ward_key(row["name"]): row["ons_ward_code"] for row in cur.fetchall()}

        today_str = date.today().isoformat()
        synced_count = 0

        for item in councillors_data:
            ward_key = normalize_ward_key(item["ward_name"])
            ward_id = ward_lookup.get(ward_key)
            if not ward_id:
                log.warning(f"[{ons_code}] Unmapped ward '{item['ward_name']}' for {item['canonical_name']}")
                continue

            cms_id = item["external_cms_id"]
            party_name, group_name = normalize_party_and_group(item["raw_party"])
            s_name = extract_surname(item["canonical_name"])
            aliases = generate_name_aliases(item["canonical_name"], allow_bare_surname=(surname_counts[s_name] == 1))

            cur.execute(
                """
                INSERT INTO councillors (authority_code, canonical_name, external_cms_id, aliases, photo_url)
                VALUES (%s, %s, %s, %s, %s)
                ON CONFLICT (authority_code, external_cms_id) DO UPDATE SET
                    canonical_name = EXCLUDED.canonical_name,
                    photo_url = COALESCE(EXCLUDED.photo_url, councillors.photo_url),
                    aliases = EXCLUDED.aliases
                RETURNING id
                """,
                (ons_code, item["canonical_name"], cms_id, Jsonb(aliases), item["photo_url"]),
            )
            cllr_id = cur.fetchone()["id"]

            cur.execute(
                "SELECT id, ward_id, group_name FROM tenures WHERE councillor_id = %s AND end_date IS NULL",
                (cllr_id,),
            )
            open_tenure = cur.fetchone()

            if open_tenure:
                if open_tenure["ward_id"] != ward_id or open_tenure["group_name"] != group_name:
                    cur.execute("UPDATE tenures SET end_date = %s WHERE id = %s", (today_str, open_tenure["id"]))
                    cur.execute(
                        """
                        INSERT INTO tenures (councillor_id, ward_id, party_name, group_name, start_date, next_election_year)
                        VALUES (%s, %s, %s, %s, %s, %s)
                        """,
                        (cllr_id, ward_id, party_name, group_name, today_str, item["next_election_year"]),
                    )
                elif item["next_election_year"]:
                    cur.execute(
                        "UPDATE tenures SET next_election_year = %s WHERE id = %s",
                        (item["next_election_year"], open_tenure["id"]),
                    )
            else:
                cur.execute(
                    """
                    INSERT INTO tenures (councillor_id, ward_id, party_name, group_name, start_date, next_election_year)
                    VALUES (%s, %s, %s, %s, %s, %s)
                    """,
                    (cllr_id, ward_id, party_name, group_name, "2019-05-01", item["next_election_year"]),
                )
            synced_count += 1

    conn.commit()
    log.info(f"[{ons_code}] Roster & tenures synchronized ({synced_count} members mapped to wards).")


# =========================================================================
# STAGE 2: 2019–2026 MINUTES CRAWLER & RECORDED DIVISION PARSER
# =========================================================================
DIVISION_BLOCK_REGEX = re.compile(
    r"((?:Votes\s+)?For(?:\s+[A-Za-z0-9'’\-]+){0,6}(?:\s*\(\d+\))?\s*:\s*(?:Councillors?|Cllrs?|None|Nil)\b.*?)\n+"
    r"((?:Votes\s+)?Against(?:\s+[A-Za-z0-9'’\-]+){0,6}(?:\s*\(\d+\))?\s*:\s*(?:Councillors?|Cllrs?|None|Nil)\b.*?)\n+"
    r"(Abst(?:entions?|ain)(?:\s+[A-Za-z0-9'’\-]+){0,4}(?:\s*\(\d+\))?\s*:\s*.*?)"
    r"(?:\n+(No\s+Vote(?:\s*\(\d+\))?\s*:?\s*.*?))?"
    r"(?:\n+(Absent(?:\s+for\s+the\s+vote)?(?:\s*\(\d+\))?\s*:?\s*.*?))?"
    r"(?=\n\n|\Z)",
    re.IGNORECASE | re.DOTALL,
)


def parse_bucket_line(line: str) -> Tuple[List[str], Optional[int]]:
    if not line:
        return ([], 0)
    flat = re.sub(r"\s+", " ", line).strip()

    m_head_cnt = re.match(
        r"^(?:Votes\s+)?(?:For|Against|Abstentions?|Abstain|No\s+Vote|Absent(?:\s+for\s+the\s+vote)?)(?:\s+[A-Za-z0-9'’\-]+){0,6}\s*\((\d+)\)",
        flat,
        flags=re.I,
    )
    m_tail_cnt = re.search(r"\((\d+)\)\s*\.?\s*$", flat)
    expected = int(m_head_cnt.group(1)) if m_head_cnt else (int(m_tail_cnt.group(1)) if m_tail_cnt else None)

    body = re.sub(
        r"^(?:Votes\s+)?(?:For|Against|Abstentions?|Abstain|No\s+Vote|Absent(?:\s+for\s+the\s+vote)?)(?:\s+[A-Za-z0-9'’\-]+){0,6}(?:\s*\(\d+\))?\s*:\s*",
        "",
        flat,
        flags=re.I,
    )
    body = re.sub(r"\((\d+)\)\s*\.?\s*$", "", body).strip()
    body = re.sub(r"^(Councillors|Councillor|Cllrs|Cllr)\s+", "", body, flags=re.I).strip()

    if not body or re.match(r"^(None|Nil)\.?$", body, flags=re.I):
        return ([], 0 if expected is None else expected)

    body = re.sub(r"\s+and\s+", ", ", body, flags=re.I)
    tokens = []
    for raw_tok in body.split(","):
        tok = re.sub(r"^(Councillors|Councillor|Cllrs|Cllr)\s+", "", raw_tok.strip(), flags=re.I)
        tok = tok.replace("’", "'").rstrip(".").strip()
        if tok:
            tokens.append(tok)
    return (tokens, expected)


def extract_text_from_pdf(pdf_bytes: bytes) -> str:
    pages_text = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for page in pdf.pages:
            txt = page.extract_text() or ""
            pages_text.append(txt)
    return "\n".join(pages_text)


def parse_flexible_date(raw_dt: str) -> Optional[date]:
    clean = re.sub(r"(\d+)(st|nd|rd|th)", r"\1", (raw_dt or "").strip())
    for fmt in ("%d/%m/%Y", "%Y-%m-%d", "%d %B %Y", "%d %b %Y"):
        try:
            return datetime.strptime(clean[:20].strip(), fmt).date()
        except ValueError:
            continue
    m = re.search(r"(\d{1,2})\s+(January|February|March|April|May|June|July|August|September|October|November|December)\s+(20\d{2})", clean)
    if m:
        return datetime.strptime(f"{m.group(1)} {m.group(2)} {m.group(3)}", "%d %B %Y").date()
    return None


def fetch_meetings_via_xml(session: cffi_requests.Session, base_url: str, cids: List[int], start_year: int, end_year: int) -> List[Dict[str, Any]]:
    meetings = {}
    s_from = f"01/01/{start_year}"
    s_to = f"31/12/{end_year}"

    for cid in cids:
        url = f"{base_url}/mgWebService.asmx/GetMeetings?lCommitteeId={cid}&sFromDate={s_from}&sToDate={s_to}"
        try:
            resp = session.get(url, timeout=30)
            if resp.status_code != 200 or b"<" not in resp.content:
                continue
            root = strip_xml_namespaces(resp.content)
            for m_el in root.findall(".//meeting"):
                mid = (m_el.findtext("meetingid") or "").strip()
                raw_date = (m_el.findtext("meetingdate") or "").strip()
                title = (m_el.findtext("meetingtitle") or m_el.findtext("committeetitle") or "The Council").strip()
                m_dt = parse_flexible_date(raw_date)
                if mid and m_dt:
                    meetings[mid] = {
                        "mid": mid,
                        "meeting_date": m_dt,
                        "title": title,
                        "source_url": f"{base_url}/ieListDocuments.aspx?CId={cid}&MId={mid}",
                    }
        except Exception as exc:
            log.warning(f"XML GetMeetings error (CId={cid}): {exc}")

    return sorted(meetings.values(), key=lambda x: x["meeting_date"])


def fetch_single_meeting_minutes(base_url: str, mtg: Dict[str, Any]) -> Dict[str, Any]:
    session = create_http_session()
    mid = mtg["mid"]
    url = f"{base_url}/mgWebService.asmx/GetMeeting?lMeetingId={mid}"
    minutes_text = ""
    pdf_url = None

    try:
        resp = session.get(url, timeout=30)
        if resp.status_code == 200 and b"<" in resp.content:
            root = strip_xml_namespaces(resp.content)
            chunks = []

            for item in root.findall(".//agendaitem"):
                num = (item.findtext("agendaitemnumber") or "").strip()
                title = (item.findtext("agendaitemtitle") or "").strip()
                if num or title:
                    chunks.append(f"{num}. {title}".strip())

                for child in item:
                    tag_low = child.tag.lower()
                    if any(k in tag_low for k in ("minute", "decision", "vote", "text")) and child.text:
                        unescaped = html.unescape(child.text)
                        plain = BeautifulSoup(unescaped, "html.parser").get_text("\n")
                        if plain.strip():
                            chunks.append(plain.strip())

            for doc in root.findall(".//document"):
                d_title = (doc.findtext("title") or "").lower()
                d_url = (doc.findtext("url") or "").strip()
                if d_url and ("minute" in d_title or "printed minutes" in d_title):
                    pdf_url = urljoin(base_url + "/", d_url)
                    break

            minutes_text = "\n\n".join(chunks)

        if (not minutes_text or not DIVISION_BLOCK_REGEX.search(minutes_text)) and pdf_url:
            pdf_resp = session.get(pdf_url, timeout=45)
            if pdf_resp.status_code == 200 and pdf_resp.content[:4] == b"%PDF":
                minutes_text = extract_text_from_pdf(pdf_resp.content)

    except Exception as exc:
        log.warning(f"Fetch error on MId={mid}: {exc}")
    finally:
        session.close()

    return {
        "mtg": mtg,
        "minutes_text": minutes_text,
        "minutes_source_url": pdf_url or mtg["source_url"],
    }


def crawl_authority_divisions(conn, session: cffi_requests.Session, authority: Dict[str, Any], start_year: int = 2019, end_year: int = 2026):
    ons_code = authority["ons_code"]
    base_url = authority["base_url"].rstrip("/")
    log.info(f"[{ons_code}] Crawling Full Council meetings from {start_year} to {end_year}...")

    with conn.cursor() as cur:
        cur.execute(
            """
            SELECT c.id, c.canonical_name, c.aliases, t.group_name, t.start_date, t.end_date
            FROM councillors c
            LEFT JOIN tenures t ON t.councillor_id = c.id
            WHERE c.authority_code = %s
            """,
            (ons_code,),
        )
        roster_rows = cur.fetchall()

    def match_token_for_date(token: str, meeting_dt: date) -> Optional[Dict[str, Any]]:
        clean = token.lower().replace("’", "'").strip()
        candidates = []
        for r in roster_rows:
            aliases = [a.lower().replace("’", "'") for a in (r["aliases"] or [])]
            if clean in aliases:
                s_dt = r["start_date"] or date(2000, 1, 1)
                e_dt = r["end_date"] or date(2099, 12, 31)
                in_tenure = s_dt <= meeting_dt <= e_dt
                candidates.append((in_tenure, r))
        if not candidates:
            return None
        candidates.sort(key=lambda x: x[0], reverse=True)
        return candidates[0][1]

    cids = KNOWN_COUNCIL_CIDS.get(ons_code, [131])
    meetings = fetch_meetings_via_xml(session, base_url, cids, start_year, end_year)
    log.info(f"[{ons_code}] Scanning {len(meetings)} Council meetings ({start_year}–{end_year}) in parallel...")

    fetched_results = []
    with ThreadPoolExecutor(max_workers=6) as pool:
        futures = [pool.submit(fetch_single_meeting_minutes, base_url, m) for m in meetings]
        for fut in as_completed(futures):
            fetched_results.append(fut.result())

    fetched_results.sort(key=lambda x: x["mtg"]["meeting_date"])
    total_divisions_found = 0

    for item in fetched_results:
        mtg = item["mtg"]
        mid = mtg["mid"]
        meeting_dt = mtg["meeting_date"]
        minutes_text = item["minutes_text"]
        minutes_source_url = item["minutes_source_url"]

        if not minutes_text:
            continue

        matches = list(DIVISION_BLOCK_REGEX.finditer(minutes_text))
        if not matches:
            continue

        total_divisions_found += len(matches)
        log.info(f"[{ons_code}] {meeting_dt} (MId={mid}): Detected {len(matches)} recorded division(s).")

        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO meetings (authority_ons_code, external_meeting_id, committee_name, meeting_date, minutes_url)
                    VALUES (%s, %s, %s, %s, %s)
                    ON CONFLICT (authority_ons_code, external_meeting_id) DO UPDATE SET
                        minutes_url = EXCLUDED.minutes_url,
                        scraped_at = NOW()
                    RETURNING id
                    """,
                    (ons_code, mid, mtg["title"][:120], meeting_dt, minutes_source_url),
                )
                meeting_uuid = cur.fetchone()["id"]

                for idx, m in enumerate(matches, start=1):
                    raw_block = m.group(0).strip()
                    preceding = minutes_text[max(0, m.start() - 600):m.start()]
                    following = minutes_text[m.end():min(len(minutes_text), m.end() + 250)]

                    min_ref_match = re.findall(r"(?:Minute\s+)?(\d{1,3})\.\s+([^\n]{6,140})", preceding)
                    if min_ref_match:
                        minute_ref, div_title = min_ref_match[-1][0], min_ref_match[-1][1].strip()
                    else:
                        minute_ref = f"Div-{idx}"
                        lines_before = [ln.strip() for ln in preceding.splitlines() if len(ln.strip()) > 8]
                        div_title = lines_before[-1][:140] if lines_before else f"Recorded Division {idx}"

                    buckets_raw = {
                        "for": m.group(1),
                        "against": m.group(2),
                        "abstain": m.group(3),
                        "no_vote": m.group(4),
                        "absent": m.group(5),
                    }

                    expected_tallies = {}
                    parsed_tallies = {}
                    unmatched_tokens = []
                    vote_records = []

                    for vote_key, line_txt in buckets_raw.items():
                        tokens, exp_cnt = parse_bucket_line(line_txt)
                        expected_tallies[vote_key] = exp_cnt if exp_cnt is not None else len(tokens)
                        matched_cnt = 0
                        for tok in tokens:
                            cllr = match_token_for_date(tok, meeting_dt)
                            if cllr:
                                matched_cnt += 1
                                vote_records.append((cllr["id"], vote_key, cllr["group_name"] or "Not Aligned"))
                            else:
                                unmatched_tokens.append({"token": tok, "bucket": vote_key})
                        parsed_tallies[vote_key] = matched_cnt

                    checksum_ok = (len(unmatched_tokens) == 0) and all(
                        parsed_tallies[k] == expected_tallies[k] for k in ["for", "against", "abstain"]
                    )
                    status = "verified" if checksum_ok else "needs_review"

                    if "carried" in following.lower() or "resolved" in following.lower():
                        outcome = "Passed"
                    elif "lost" in following.lower() or "fell" in following.lower() or "rejected" in following.lower():
                        outcome = "Rejected"
                    else:
                        outcome = "Passed" if parsed_tallies["for"] > parsed_tallies["against"] else "Rejected"

                    category = classify_motion_category(div_title, preceding)

                    cur.execute(
                        """
                        INSERT INTO divisions (
                            meeting_id, minute_ref, title, category, outcome,
                            raw_text, expected_tallies, parsed_tallies, unmatched_tokens, status
                        )
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                        ON CONFLICT (meeting_id, minute_ref, title) DO UPDATE SET
                            outcome = EXCLUDED.outcome,
                            parsed_tallies = EXCLUDED.parsed_tallies,
                            unmatched_tokens = EXCLUDED.unmatched_tokens,
                            status = EXCLUDED.status
                        RETURNING id
                        """,
                        (
                            meeting_uuid, minute_ref, div_title, category, outcome,
                            raw_block, Jsonb(expected_tallies), Jsonb(parsed_tallies),
                            Jsonb(unmatched_tokens), status,
                        ),
                    )
                    division_uuid = cur.fetchone()["id"]

                    group_votes: Dict[str, Dict[str, int]] = {}
                    for _, v_cast, grp in vote_records:
                        group_votes.setdefault(grp, {"for": 0, "against": 0})
                        if v_cast in ("for", "against"):
                            group_votes[grp][v_cast] += 1

                    group_majority: Dict[str, Optional[str]] = {}
                    for grp, counts in group_votes.items():
                        if grp == "Not Aligned" or (counts["for"] + counts["against"]) < 2:
                            group_majority[grp] = None
                        elif counts["for"] > counts["against"]:
                            group_majority[grp] = "for"
                        elif counts["against"] > counts["for"]:
                            group_majority[grp] = "against"
                        else:
                            group_majority[grp] = "tied"

                    for cllr_id, v_cast, grp in vote_records:
                        maj = group_majority.get(grp)
                        is_rebel = bool(
                            maj and v_cast in ("for", "against") and (maj == "tied" or v_cast != maj)
                        )
                        cur.execute(
                            """
                            INSERT INTO votes (division_id, councillor_id, vote_cast, group_at_vote, is_rebel)
                            VALUES (%s, %s, %s, %s, %s)
                            ON CONFLICT (division_id, councillor_id) DO UPDATE SET
                                vote_cast = EXCLUDED.vote_cast,
                                group_at_vote = EXCLUDED.group_at_vote,
                                is_rebel = EXCLUDED.is_rebel
                            """,
                            (division_uuid, cllr_id, v_cast, grp, is_rebel),
                        )

            conn.commit()
        except Exception as exc:
            conn.rollback()
            log.warning(f"[{ons_code}] Error saving MId={mid}: {exc}")

    log.info(f"[{ons_code}] Finished crawl: {total_divisions_found} recorded division(s) extracted.")


# =========================================================================
# STAGE 3: GEMINI JOURNALISTIC BRIEFING GENERATOR (PACED + FREE-TIER FALLBACK)
# =========================================================================
def generate_missing_briefings(conn, limit: int = 60):
    api_key = os.environ.get("GEMINI_API_KEY")
    if not api_key or genai is None:
        log.info("GEMINI_API_KEY not set; skipping AI journalistic briefing generation.")
        return

    client = genai.Client(api_key=api_key.strip())

    with conn.cursor() as cur:
        cur.execute(
            """
            SELECT d.id, d.title, d.minute_ref, d.outcome, d.raw_text, d.expected_tallies,
                   m.meeting_date, a.name AS authority_name
            FROM divisions d
            JOIN meetings m ON m.id = d.meeting_id
            JOIN authorities a ON a.ons_code = m.authority_ons_code
            LEFT JOIN briefings b ON b.division_id = d.id
            WHERE d.status IN ('verified', 'needs_review') AND b.division_id IS NULL
            ORDER BY m.meeting_date DESC
            LIMIT %s
            """,
            (limit,),
        )
        pending = cur.fetchall()

    if not pending:
        log.info("All extracted divisions already have journalistic briefings.")
        return

    log.info(f"Generating journalistic briefings for {len(pending)} division(s)...")

    grounding_enabled = True
    primary_exhausted = False

    for idx, div in enumerate(pending):
        if idx > 0:
            # Pace under 15 RPM (Flash-Lite limit) or 5 RPM (3.8 Flash limit)
            time.sleep(4.5 if primary_exhausted else 12.5)

        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT v.vote_cast, v.group_at_vote, v.is_rebel, c.canonical_name
                FROM votes v
                JOIN councillors c ON c.id = v.councillor_id
                WHERE v.division_id = %s
                """,
                (div["id"],),
            )
            vote_rows = cur.fetchall()

        rebels = [f"Cllr {r['canonical_name']} ({r['group_at_vote']}) voted {r['vote_cast'].upper()}" for r in vote_rows if r["is_rebel"]]
        prompt = f"""You are a British local government political journalist covering {div['authority_name']}.
Analyse the recorded council vote below and combine it with local British local government context:

Authority: {div['authority_name']}
Meeting Date: {div['meeting_date']} (Minute {div['minute_ref']})
Motion Title: {div['title']}
Outcome: {div['outcome']}
Tallies: {json.dumps(div['expected_tallies'])}
Party Whip Deviations / Rebels: {', '.join(rebels) if rebels else 'None'}
Official Minute Record:
{(div['raw_text'] or '')[:1800]}

Return ONLY a valid JSON object (no markdown fences) with these exact 5 keys in objective British English:
{{
  "headline_summary": "1-sentence punchy summary of the outcome and key political split",
  "core_question": "Plain-English explanation of what voting For or Against practically meant",
  "context_and_stakeholders": "Local background, triggers, and affected resident/stakeholder groups",
  "political_calculus": "Underlying party strategy, coalition dynamics, or wedge tactics",
  "anatomy_of_split": "Breakdown of how each party group voted, naming any rebels or abstainers"
}}"""

        response = None

        # 1. Try grounded gemini-3.8-flash (works automatically on paid Tier 1 keys)
        if grounding_enabled and not primary_exhausted:
            try:
                response = client.models.generate_content(
                    model="gemini-3.8-flash",
                    contents=prompt,
                    config=types.GenerateContentConfig(
                        tools=[types.Tool(google_search=types.GoogleSearch())],
                        temperature=0.3,
                    ),
                )
            except Exception as exc:
                if "429" in str(exc) or "RESOURCE_EXHAUSTED" in str(exc):
                    log.info("Google Search grounding unavailable on current tier; switching to standard synthesis.")
                    grounding_enabled = False
                else:
                    log.warning(f"Grounded request error for {div['id']}: {exc}")

        # 2. Try ungrounded gemini-3.8-flash (free tier: 5 RPM, 20 RPD)
        if response is None and not primary_exhausted:
            try:
                response = client.models.generate_content(
                    model="gemini-3.8-flash",
                    contents=prompt,
                    config=types.GenerateContentConfig(temperature=0.3),
                )
            except Exception as exc:
                if "429" in str(exc) or "RESOURCE_EXHAUSTED" in str(exc):
                    log.info("gemini-3.8-flash free daily quota reached; routing remaining divisions to gemini-3.5-flash-lite.")
                    primary_exhausted = True
                else:
                    log.warning(f"gemini-3.8-flash error for {div['id']}: {exc}")

        # 3. Overflow to gemini-3.5-flash-lite (free tier: 15 RPM, 500 RPD)
        if response is None:
            try:
                response = client.models.generate_content(
                    model="gemini-3.5-flash-lite",
                    contents=prompt,
                    config=types.GenerateContentConfig(temperature=0.3),
                )
            except Exception as exc:
                if "429" in str(exc) or "RESOURCE_EXHAUSTED" in str(exc):
                    log.warning("All free-tier daily quotas exhausted for today; remaining briefings will run next cycle.")
                    break
                log.warning(f"Briefing generation failed for {div['id']}: {exc}")
                continue

        try:
            raw_text = (response.text if response else "") or ""
            match = re.search(r"\{[\s\S]*\}", raw_text)
            if not match:
                continue
            brief = json.loads(match.group(0))

            citations = []
            cand = response.candidates[0] if response and response.candidates else None
            if cand and getattr(cand, "grounding_metadata", None):
                chunks = getattr(cand.grounding_metadata, "grounding_chunks", None) or []
                for ch in chunks:
                    if getattr(ch, "web", None):
                        citations.append({"title": ch.web.title, "uri": ch.web.uri})

            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO briefings (
                        division_id, headline_summary, core_question,
                        context_and_stakeholders, political_calculus, anatomy_of_split, citations
                    )
                    VALUES (%s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (division_id) DO UPDATE SET
                        headline_summary = EXCLUDED.headline_summary,
                        core_question = EXCLUDED.core_question,
                        context_and_stakeholders = EXCLUDED.context_and_stakeholders,
                        political_calculus = EXCLUDED.political_calculus,
                        anatomy_of_split = EXCLUDED.anatomy_of_split,
                        citations = EXCLUDED.citations,
                        generated_at = NOW()
                    """,
                    (
                        div["id"],
                        brief.get("headline_summary", ""),
                        brief.get("core_question", ""),
                        brief.get("context_and_stakeholders", ""),
                        brief.get("political_calculus", ""),
                        brief.get("anatomy_of_split", ""),
                        Jsonb(citations),
                    ),
                )
            conn.commit()
            log.info(f"[{idx + 1}/{len(pending)}] Generated briefing for {div['meeting_date']} Min {div['minute_ref']}")
        except Exception as db_exc:
            conn.rollback()
            log.warning(f"Database save failed for briefing {div['id']}: {db_exc}")


# =========================================================================
# CLI ENTRYPOINT
# =========================================================================
def main():
    parser = argparse.ArgumentParser(description="UK Council VoteWatch Automated Modern.Gov Worker")
    parser.add_argument("command", choices=["sync-roster", "crawl-divisions", "generate-briefings", "full-sync"])
    parser.add_argument("--authority", default="E06000033", help="ONS authority code (default: Southend E06000033)")
    parser.add_argument("--start-year", type=int, default=2019, help="Earliest meeting year to crawl (default: 2019)")
    parser.add_argument("--end-year", type=int, default=2026, help="Latest meeting year to crawl (default: 2026)")
    args = parser.parse_args()

    session = create_http_session()

    with get_db_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("SELECT * FROM authorities WHERE ons_code = %s", (args.authority,))
            authority = cur.fetchone()
            if not authority:
                log.error(f"Authority {args.authority} not found in database.")
                sys.exit(1)

        if args.command in ("sync-roster", "full-sync"):
            sync_authority_roster(conn, session, authority)

        if args.command in ("crawl-divisions", "full-sync"):
            crawl_authority_divisions(conn, session, authority, start_year=args.start_year, end_year=args.end_year)

        if args.command in ("generate-briefings", "full-sync"):
            generate_missing_briefings(conn)


if __name__ == "__main__":
    main()
