#!/usr/bin/env python3
"""
UK COUNCIL VOTEWATCH — AUTOMATED MODERN.GOV INGESTION PIPELINE
Uses Chrome TLS/HTTP2 impersonation (curl_cffi) + XML/HTML dual roster extraction.
"""

import argparse
import io
import json
import logging
import os
import re
import sys
import xml.etree.ElementTree as ET
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
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "en-GB,en;q=0.9",
    "Upgrade-Insecure-Requests": "1",
}

KNOWN_COUNCIL_CIDS = {
    "E06000033": [131],  # Southend-on-Sea: 'The Council'
}


def create_http_session() -> cffi_requests.Session:
    proxy = os.environ.get("PROXY_URL")
    proxies = {"http": proxy, "https": proxy} if proxy else None
    session = cffi_requests.Session(impersonate="chrome", headers=BROWSER_HEADERS, proxies=proxies)
    return session


def get_db_connection():
    db_url = os.environ.get("DATABASE_URL")
    if not db_url:
        log.error("DATABASE_URL environment variable is missing.")
        sys.exit(1)
    return psycopg.connect(db_url, row_factory=dict_row)


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


def generate_name_aliases(full_name: str) -> List[str]:
    clean = re.sub(r"^(Councillor|Cllr|Dr|Prof|Rev|Sir|Dame)\s+", "", full_name.strip(), flags=re.I)
    clean = clean.replace("’", "'")
    parts = clean.split()
    aliases = {full_name.strip(), clean}
    if len(parts) >= 2:
        surname = parts[-1]
        first_initial = parts[0][0]
        aliases.add(surname)
        aliases.add(f"{first_initial} {surname}")
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


# =========================================================================
# STAGE 1: MODERN.GOV ROSTER & TENURE SYNCER (XML + HTML TABLE FALLBACK)
# =========================================================================
def parse_moderngov_xml_councillors(xml_bytes: bytes) -> List[Dict[str, Any]]:
    root = ET.fromstring(xml_bytes)
    for elem in root.iter():
        if "}" in elem.tag:
            elem.tag = elem.tag.split("}", 1)[1]

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


def parse_moderngov_html_councillors(html_text: str) -> List[Dict[str, Any]]:
    """Parses Modern.Gov mgMemberIndex.aspx?VW=TABLE&PIC=0 HTML table."""
    soup = BeautifulSoup(html_text, "html.parser")
    results = []
    for tr in soup.find_all("tr"):
        user_link = tr.find("a", href=re.compile(r"mgUserInfo\.aspx\?UID=\d+", re.I))
        if not user_link:
            continue
        cells = [td.get_text(" ", strip=True) for td in tr.find_all(["td", "th"])]
        if len(cells) < 3:
            continue
        m_uid = re.search(r"UID=(\d+)", user_link["href"], re.I)
        uid = m_uid.group(1) if m_uid else ""
        full_name = re.sub(r"^(Councillor|Cllr)\s+", "", user_link.get_text(" ", strip=True), flags=re.I).strip()

        # Standard Modern.Gov columns: Name | Party | Ward | Term of Office
        party = cells[1] if len(cells) > 1 else ""
        ward = cells[2] if len(cells) > 2 else ""
        term_str = cells[3] if len(cells) > 3 else ""
        years = re.findall(r"(20\d{2})", term_str)
        next_year = int(years[-1]) if years else None

        if full_name and ward:
            results.append({
                "external_cms_id": uid or full_name.lower().replace(" ", "-"),
                "canonical_name": full_name,
                "ward_name": ward,
                "raw_party": party,
                "photo_url": None,
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
        log.info(f"[{ons_code}] XML endpoint status: HTTP {resp.status_code}")
        if resp.status_code == 200 and b"<" in resp.content:
            councillors_data = parse_moderngov_xml_councillors(resp.content)
            log.info(f"[{ons_code}] Retrieved {len(councillors_data)} councillors via Modern.Gov XML API.")
    except Exception as exc:
        log.warning(f"[{ons_code}] XML endpoint error: {exc}")

    if not councillors_data:
        html_url = f"{base_url}/mgMemberIndex.aspx?VW=TABLE&PIC=0"
        try:
            resp = session.get(html_url, timeout=30)
            log.info(f"[{ons_code}] HTML directory status: HTTP {resp.status_code}")
            if resp.status_code == 200:
                councillors_data = parse_moderngov_html_councillors(resp.text)
                log.info(f"[{ons_code}] Retrieved {len(councillors_data)} councillors via HTML directory.")
            elif resp.status_code == 403:
                log.error(f"[{ons_code}] WAF blocked request (HTTP 403). If running from cloud CI, set PROXY_URL or run locally.")
        except Exception as exc:
            log.warning(f"[{ons_code}] HTML directory error: {exc}")

    if not councillors_data:
        log.warning(f"[{ons_code}] No councillors extracted. Skipping roster update.")
        return

    with conn.cursor() as cur:
        cur.execute("SELECT ons_ward_code, name FROM wards WHERE authority_ons_code = %s", (ons_code,))
        ward_lookup = {row["name"].lower().replace("’", "'"): row["ons_ward_code"] for row in cur.fetchall()}

        today_str = date.today().isoformat()

        for item in councillors_data:
            ward_key = item["ward_name"].lower().replace("’", "'")
            ward_id = ward_lookup.get(ward_key)
            if not ward_id:
                log.warning(f"[{ons_code}] Unmapped ward '{item['ward_name']}' for {item['canonical_name']}")
                continue

            cms_id = item["external_cms_id"]
            party_name, group_name = normalize_party_and_group(item["raw_party"])
            aliases = generate_name_aliases(item["canonical_name"])

            cur.execute(
                """
                INSERT INTO councillors (authority_code, canonical_name, external_cms_id, aliases, photo_url)
                VALUES (%s, %s, %s, %s, %s)
                ON CONFLICT (authority_code, external_cms_id) DO UPDATE SET
                    canonical_name = EXCLUDED.canonical_name,
                    photo_url = COALESCE(EXCLUDED.photo_url, councillors.photo_url),
                    aliases = (
                        SELECT jsonb_agg(DISTINCT val)
                        FROM jsonb_array_elements_text(councillors.aliases || EXCLUDED.aliases) AS val
                    )
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

    conn.commit()
    log.info(f"[{ons_code}] Roster & tenures synchronized ({len(councillors_data)} members).")


# =========================================================================
# STAGE 2: 2019–2026 MINUTES CRAWLER & RECORDED DIVISION PARSER
# =========================================================================
DIVISION_BLOCK_REGEX = re.compile(
    r"(For\s*:\s*Councillors?.*?)\n+"
    r"(Against\s*:\s*Councillors?.*?)\n+"
    r"(Abst(?:entions|ain)\s*:.*?)(?:\n+"
    r"(No\s+Vote\s*:.*?))?(?:\n+"
    r"(Absent(?:\s+for\s+the\s+vote)?\s*:.*?))?(?=\n\n|\Z)",
    re.IGNORECASE | re.DOTALL,
)


def parse_bucket_line(line: str) -> Tuple[List[str], Optional[int]]:
    if not line:
        return ([], 0)
    flat = re.sub(r"\s+", " ", line).strip()
    m_count = re.search(r"\((\d+)\)\s*\.?\s*$", flat)
    expected = int(m_count.group(1)) if m_count else None
    body = re.sub(r"^(For|Against|Abstentions|Abstain|No\s+Vote|Absent(?:\s+for\s+the\s+vote)?)\s*:\s*", "", flat, flags=re.I)
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


def discover_council_committee_ids(session: cffi_requests.Session, base_url: str, ons_code: str) -> List[int]:
    if ons_code in KNOWN_COUNCIL_CIDS:
        return KNOWN_COUNCIL_CIDS[ons_code]
    resp = session.get(f"{base_url}/mgListCommittees.aspx", timeout=30)
    soup = BeautifulSoup(resp.text, "html.parser")
    cids = []
    for a in soup.find_all("a", href=re.compile(r"mgCommitteeDetails\.aspx\?ID=\d+", re.I)):
        label = a.get_text(" ", strip=True).lower()
        if label in ("the council", "full council", "council"):
            m = re.search(r"ID=(\d+)", a["href"], re.I)
            if m:
                cids.append(int(m.group(1)))
    return sorted(set(cids)) or [131]


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

    cids = discover_council_committee_ids(session, base_url, ons_code)
    meeting_links = {}

    for cid in cids:
        for yr in range(start_year, end_year + 1):
            list_url = f"{base_url}/ieListMeetings.aspx?CId={cid}&Year={yr}"
            try:
                resp = session.get(list_url, timeout=30)
                if resp.status_code != 200:
                    log.warning(f"[{ons_code}] Year {yr} returned HTTP {resp.status_code}")
                    continue
                soup = BeautifulSoup(resp.text, "html.parser")
                for a in soup.find_all("a", href=re.compile(r"ieListDocuments\.aspx\?CId=\d+&MId=\d+", re.I)):
                    href = urljoin(base_url + "/", a["href"])
                    m_mid = re.search(r"MId=(\d+)", href, re.I)
                    if m_mid:
                        meeting_links[m_mid.group(1)] = href
            except Exception as exc:
                log.warning(f"[{ons_code}] Failed listing year {yr}: {exc}")

    log.info(f"[{ons_code}] Found {len(meeting_links)} candidate Council meetings ({start_year}–{end_year}).")

    for mid, doc_url in sorted(meeting_links.items()):
        try:
            m_resp = session.get(doc_url, timeout=30)
            if m_resp.status_code != 200:
                continue
            m_soup = BeautifulSoup(m_resp.text, "html.parser")
            page_title = m_soup.title.get_text(" ", strip=True) if m_soup.title else "The Council"

            date_match = re.search(
                r"(\d{1,2})(?:st|nd|rd|th)?\s+(January|February|March|April|May|June|July|August|September|October|November|December)\s+(20\d{2})",
                m_soup.get_text(" "),
            )
            if not date_match:
                continue
            dt_str = f"{date_match.group(1)} {date_match.group(2)} {date_match.group(3)}"
            meeting_dt = datetime.strptime(dt_str, "%d %B %Y").date()

            minutes_text = ""
            minutes_source_url = doc_url
            for link in m_soup.find_all("a", href=True):
                txt = link.get_text(" ", strip=True).lower()
                href = link["href"]
                if ("minute" in txt or "printed minutes" in txt) and (".pdf" in href.lower() or "mgconvert2pdf" in href.lower()):
                    minutes_source_url = urljoin(base_url + "/", href)
                    pdf_resp = session.get(minutes_source_url, timeout=45)
                    if pdf_resp.status_code == 200 and pdf_resp.content[:4] == b"%PDF":
                        minutes_text = extract_text_from_pdf(pdf_resp.content)
                        break

            if not minutes_text:
                for link in m_soup.find_all("a", href=re.compile(r"mgAi\.aspx\?ID=\d+", re.I)):
                    if "minute" in link.get_text(" ", strip=True).lower():
                        ai_url = urljoin(base_url + "/", link["href"])
                        ai_resp = session.get(ai_url, timeout=30)
                        if ai_resp.status_code == 200:
                            minutes_text += "\n" + BeautifulSoup(ai_resp.text, "html.parser").get_text("\n")

            if not minutes_text:
                continue

            matches = list(DIVISION_BLOCK_REGEX.finditer(minutes_text))
            if not matches:
                continue

            log.info(f"[{ons_code}] {meeting_dt} (MId={mid}): Detected {len(matches)} recorded division(s).")

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
                    (ons_code, mid, page_title[:120], meeting_dt, minutes_source_url),
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
            log.warning(f"[{ons_code}] Error processing MId={mid}: {exc}")


# =========================================================================
# STAGE 3: GEMINI SEARCH-GROUNDED JOURNALISTIC BRIEFING GENERATOR
# =========================================================================
def generate_missing_briefings(conn, limit: int = 25):
    api_key = os.environ.get("GEMINI_API_KEY")
    if not api_key or genai is None:
        log.info("GEMINI_API_KEY not set; skipping AI journalistic briefing generation.")
        return

    client = genai.Client(api_key=api_key)

    with conn.cursor() as cur:
        cur.execute(
            """
            SELECT d.id, d.title, d.minute_ref, d.outcome, d.parsed_tallies,
                   m.meeting_date, a.name AS authority_name
            FROM divisions d
            JOIN meetings m ON m.id = d.meeting_id
            JOIN authorities a ON a.ons_code = m.authority_ons_code
            LEFT JOIN briefings b ON b.division_id = d.id
            WHERE d.status = 'verified' AND b.division_id IS NULL
            ORDER BY m.meeting_date DESC
            LIMIT %s
            """,
            (limit,),
        )
        pending = cur.fetchall()

    if not pending:
        log.info("All verified divisions already have journalistic briefings.")
        return

    log.info(f"Generating Google Search-grounded journalistic briefings for {len(pending)} division(s)...")

    for div in pending:
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
Use Google Search to find verified local news, council reports, or petitions relating to this recorded council vote, and combine that context with the exact mathematical voting record below:

Authority: {div['authority_name']}
Meeting Date: {div['meeting_date']} (Minute {div['minute_ref']})
Motion Title: {div['title']}
Outcome: {div['outcome']}
Tallies: {json.dumps(div['parsed_tallies'])}
Party Whip Deviations / Rebels: {', '.join(rebels) if rebels else 'None'}

Return ONLY a valid JSON object (no markdown fences) with these exact 5 keys in objective British English:
{{
  "headline_summary": "1-sentence punchy summary of the outcome and key political split",
  "core_question": "Plain-English explanation of what voting For or Against practically meant",
  "context_and_stakeholders": "Local background, triggers, and affected resident/stakeholder groups",
  "political_calculus": "Underlying party strategy, coalition dynamics, or wedge tactics",
  "anatomy_of_split": "Breakdown of how each party group voted, naming any rebels or abstainers"
}}"""

        try:
            response = client.models.generate_content(
                model="gemini-2.5-flash",
                contents=prompt,
                config=types.GenerateContentConfig(
                    tools=[types.Tool(google_search=types.GoogleSearch())],
                    temperature=0.3,
                ),
            )
            raw_text = response.text or ""
            match = re.search(r"\{[\s\S]*\}", raw_text)
            if not match:
                continue
            brief = json.loads(match.group(0))

            citations = []
            cand = response.candidates[0] if response.candidates else None
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
            log.info(f"Generated briefing for {div['meeting_date']} Min {div['minute_ref']}")
        except Exception as exc:
            conn.rollback()
            log.warning(f"Briefing generation failed for {div['id']}: {exc}")


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
