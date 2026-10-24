#!/usr/bin/env python3
"""Guadalupe NHS Numeracy Drill: LAN live polling. Run: python3 numeracy.py [port]
Teacher opens the HOST link printed below. Students open the JOIN link.
ONE FILE, THREE STAGES: PRE-TEST (students open /test) -> all the drills and actions in this file -> POST-TEST (/test again).
The teacher runs all three from the dashboard: /host for the drills, /test/host for the tests (button "Pre / Post test" in Reports).

EVIDENCE-BASED NUMERACY BY DESIGN. Each rule is a design decision, with the research it rests on:
  1. Retrieval practice: students recall and answer, not re-read (Roediger & Karpicke 2006; Adesope et al. 2017).
  2. Interleaving: topics are mixed, not blocked (Rohrer, Dedrick & Stershic 2015; Rohrer et al. 2020, Grade 7 classroom RCT).
  3. Spacing + targeting: topics the class is weak at, or has not seen for a while, come up more often (Cepeda et al. 2006).
  4. Immediate corrective feedback with a worked solution after EVERY answer (Hattie & Timperley 2007; Sweller & Cooper 1985; Booth et al. 2013).
  5. Error diagnosis: wrong answers are classed (sign, slip, place value, wrong operation) so feedback and re-teaching are specific (Brown & Burton 1978).
  6. Productive success: the host is told when class accuracy leaves a 70-90% band so difficulty can be re-tuned (Vygotsky's ZPD; Wilson et al. 2019, used here as a heuristic).
  7. Accuracy over speed: points do not depend on answer speed. Time pressure loads working memory and raises maths anxiety (Ashcraft & Kirk 2001; Ramirez et al. 2013).
  8. Local context and language: peso, jeepney and sari-sari problems and Taglish wording lower the language barrier on word problems.
  9. Skill-level grading: addition, subtraction, multiplication and division are graded one by one for every student
     (strengths, weaknesses, mistake pattern, trend, pre/post test), so re-teaching targets the exact skill, not just the topic.
Switches for 2, 3, 6 and 7 are in the EVIDENCE SETTINGS block below."""
import atexit, getpass, hashlib, hmac, json, math, os, random, re, secrets, socket, struct, sys, threading, time, zlib
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs

# Folder for all saved files (data, PIN, tests, reports). The apps set NUMERACY_DATA; running the file directly keeps the old behaviour.
DATA_DIR = os.environ.get('NUMERACY_DATA') or os.path.dirname(os.path.abspath(__file__))
try: os.makedirs(DATA_DIR, exist_ok=True)
except Exception: pass

PORT = next((int(a) for a in sys.argv[1:] if a.isdigit()), 8000)
KEY = secrets.token_urlsafe(18)   # session token: only handed out after the correct teacher PIN, new on every start
FILE = os.path.join(DATA_DIR, 'gnhs-data.json')
lock = threading.Lock()

# ---- Teacher PIN (stored only as a salted hash in gnhs-pin.json) ----
PINFILE = os.path.join(DATA_DIR, 'gnhs-pin.json')
PIN_REC = None      # (salt bytes, hash hex)
FAILS = {}          # client ip -> [wrong attempts, locked-until time]
def _phash(pin, salt): return hashlib.pbkdf2_hmac('sha256', pin.encode('utf-8'), salt, 200000).hex()
def make_pin(pin): salt = os.urandom(16); return salt, _phash(pin, salt)
def save_pin(rec):
    try: json.dump({'salt': rec[0].hex(), 'hash': rec[1]}, open(PINFILE, 'w'))
    except Exception: pass
def load_pin():
    try: j = json.load(open(PINFILE)); return bytes.fromhex(j['salt']), j['hash']
    except Exception: return None
def keyok(k): return hmac.compare_digest(str(k).encode('utf-8'), KEY.encode('utf-8'))

# ======================= LOCKED PDF (A4 portrait, standard library only) =======================
# Tables are drawn by hand (Helvetica) and the file is encrypted with the PDF standard handler (RC4 128-bit).
# No password is needed to open it; printing is allowed, editing / copying / annotating are not (random owner password, never shown).
_PAD = bytes.fromhex('28BF4E5E4E758A4164004E56FFFA01082E2E00B6D0683E802F0CA9FE6453697A')
def _rc4(key, data):
    S = list(range(256)); j = 0
    for i in range(256):
        j = (j + S[i] + key[i % len(key)]) & 255; S[i], S[j] = S[j], S[i]
    out = bytearray(); i = j = 0
    for b in data:
        i = (i + 1) & 255; j = (j + S[i]) & 255; S[i], S[j] = S[j], S[i]; out.append(b ^ S[(S[i] + S[j]) & 255])
    return bytes(out)
def _pdf_keys(owner_pw, P, ID):
    h = hashlib.md5((owner_pw + _PAD)[:32]).digest()
    for _ in range(50): h = hashlib.md5(h).digest()
    ok = h[:16]; O = _rc4(ok, _PAD)
    for i in range(1, 20): O = _rc4(bytes(b ^ i for b in ok), O)
    h = hashlib.md5(_PAD + O + struct.pack('<I', P & 0xFFFFFFFF) + ID).digest()
    for _ in range(50): h = hashlib.md5(h[:16]).digest()
    key = h[:16]; u = _rc4(key, hashlib.md5(_PAD + ID).digest())
    for i in range(1, 20): u = _rc4(bytes(b ^ i for b in key), u)
    return key, O, u + b'\0' * 16
def _wrap(text, w, size, bold=False):
    n = max(1, int(w / (size * (0.58 if bold else 0.54)))); lines = []
    for para in str(text).split('\n'):
        cur = ''
        for word in para.split(' '):
            while len(word) > n:
                if cur: lines.append(cur); cur = ''
                lines.append(word[:n]); word = word[n:]
            if cur and len(cur) + 1 + len(word) > n: lines.append(cur); cur = word
            else: cur = (cur + ' ' + word) if cur else word
        lines.append(cur)
    return lines
def make_pdf(title, sub, cols, rows, weights):
    W, H, M, PAD, LH = 595.28, 841.89, 34.0, 3.0, 10.0
    uw = W - 2 * M
    def mkcw(cs, ws):
        n = len(cs) or len(ws); wt = [max(0.1, float(x)) for x in ws][:n]; wt += [1.0] * (n - len(wt)); tot = sum(wt) or 1
        return [uw * x / tot for x in wt]
    cw = mkcw(cols, weights)
    pages = []; ops = []; st = {'y': M}
    def txt(x, y, s, size, bold=False, rgb='0.1 0.09 0.23'):
        b = str(s).encode('cp1252', 'replace').replace(b'\\', b'\\\\').replace(b'(', b'\\(').replace(b')', b'\\)')
        ops.append(b'BT /F%d %.1f Tf %s rg %.2f %.2f Td (' % (2 if bold else 1, size, rgb.encode(), x, H - y) + b + b') Tj ET')
    def rect(x, y, w, h, rgb): ops.append(b'%s rg %.2f %.2f %.2f %.2f re f' % (rgb.encode(), x, H - y - h, w, h))
    def newpage():
        nonlocal ops
        if ops: pages.append(b'\n'.join(ops))
        ops = []; st['y'] = M
    def row(cells, bold, fill, size, rgb='0.1 0.09 0.23'):
        L = [_wrap(c, cw[i] - 2 * PAD, size, bold) for i, c in enumerate(cells[:len(cw)])]
        h = max(len(x) for x in L) * LH + 2 * PAD
        if st['y'] + h > H - M - 14: newpage(); header()
        if fill: rect(M, st['y'], uw, h, fill)
        x = M
        for i, lines in enumerate(L):
            for k, ln in enumerate(lines): txt(x + PAD, st['y'] + PAD + (k + 1) * LH - 2.5, ln, size, bold, rgb)
            x += cw[i]
        st['y'] += h
    def header():
        if cols: row(cols, True, '0.93 0.9 1', 6.6)
    txt(M, st['y'] + 14, title, 15, True, '0.36 0.13 0.71'); txt(M, st['y'] + 28, sub, 8.5, False, '0.42 0.44 0.5'); st['y'] += 38
    z = 0
    if not (rows and isinstance(rows[0], (str, dict))): header()
    for ri, r in enumerate(rows):
        if r == '\f': newpage(); z = 0; continue   # explicit page break
        if isinstance(r, dict):   # switch to another set of columns (and draw its header)
            cols = [str(c) for c in r.get('cols', [])]; cw = mkcw(cols, r.get('w') or []); z = 0
            if cols:
                if st['y'] + 30 > H - M - 14: newpage()
                header()
            continue
        if isinstance(r, str):
            if st['y'] + 40 > H - M - 14: newpage()
            st['y'] += 6; rect(M, st['y'], uw, 16, '0.86 0.8 0.99'); txt(M + PAD + 2, st['y'] + 11.5, r, 9.5, True, '0.36 0.13 0.71'); st['y'] += 16; nx = rows[ri + 1] if ri + 1 < len(rows) else None; z = 0
            if nx is not None and not isinstance(nx, (dict, str)): header()
        else: z += 1; row(list(r), False, '0.975 0.965 1' if z % 2 == 0 else None, 8)
    pages.append(b'\n'.join(ops)); n = len(pages)
    for i in range(n):
        ops = []; txt(W / 2 - 22, H - 18, 'Page %d of %d' % (i + 1, n), 7.5, False, '0.5 0.5 0.6'); pages[i] += b'\n' + b'\n'.join(ops)
    return _pdf_pack(pages)
def _pdf_pack(pages):   # A4 pages (content streams) -> one print-only encrypted PDF
    n = len(pages)
    P = 0xFFFFF0C0 | 4 | 2048                                  # print only
    ID = secrets.token_bytes(16); key, O, U = _pdf_keys(secrets.token_hex(16).encode(), P, ID)
    objs = {}; N = 4 + 2 * n + 1
    objs[1] = b'<< /Type /Catalog /Pages 2 0 R >>'
    objs[2] = b'<< /Type /Pages /Kids [' + b' '.join(b'%d 0 R' % (5 + 2 * i) for i in range(n)) + b'] /Count %d >>' % n
    objs[3] = b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>'
    objs[4] = b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>'
    for i in range(n):
        po, co = 5 + 2 * i, 6 + 2 * i
        objs[po] = b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 595.28 841.89] /Resources << /Font << /F1 3 0 R /F2 4 0 R >> >> /Contents %d 0 R >>' % co
        data = _rc4(hashlib.md5(key + struct.pack('<I', co)[:3] + b'\0\0').digest()[:16], zlib.compress(pages[i]))
        objs[co] = b'<< /Length %d /Filter /FlateDecode >>\nstream\n' % len(data) + data + b'\nendstream'
    eo = N
    objs[eo] = b'<< /Filter /Standard /V 2 /R 3 /Length 128 /P %d /O <%s> /U <%s> >>' % (P - (1 << 32), O.hex().encode(), U.hex().encode())
    out = bytearray(b'%PDF-1.4\n'); off = {}
    for k in sorted(objs): off[k] = len(out); out += b'%d 0 obj\n' % k + objs[k] + b'\nendobj\n'
    x = len(out); out += b'xref\n0 %d\n0000000000 65535 f \n' % (eo + 1)
    for k in range(1, eo + 1): out += b'%010d 00000 n \n' % off[k]
    out += b'trailer\n<< /Size %d /Root 1 0 R /Encrypt %d 0 R /ID [<%s> <%s>] >>\nstartxref\n%d\n%%%%EOF\n' % (eo + 1, eo, ID.hex().encode(), ID.hex().encode(), x)
    return bytes(out)
_PM = {'\u20b1': 'P', '\u2212': '-', '\u2192': '->', '\u2713': 'Yes', '\u2714': 'Yes', '\u2717': 'No', '\u2718': 'No', '\u221a': 'sqrt', '\u03c0': 'pi', '\u2264': '<=', '\u2265': '>=', '\u2260': '!=', '\u2248': '~', '\u2044': '/'}
def _pdfclean(x):   # Helvetica only has Windows-1252: swap the maths symbols it lacks and drop emoji
    x = str(x)
    for k, v in _PM.items(): x = x.replace(k, v)
    x = ''.join(c for c in x if c == '\f' or (ord(c) < 256 and (c >= ' ' or c == '\n')) or c in '\u2013\u2014\u2018\u2019\u201c\u201d\u2022\u20ac\u2026')
    return x if x == '\f' else re.sub(r'[ \t]{2,}', ' ', x).strip()
def _pdfrow(r):
    if isinstance(r, str): return r if r == '\f' else (_pdfclean(r) or None)
    if isinstance(r, dict): return {'cols': [_pdfclean(c) for c in (r.get('cols') or [])][:30], 'w': [x for x in (r.get('w') or []) if isinstance(x, (int, float)) and not isinstance(x, bool)][:30]}
    c = [_pdfclean(c) for c in r][:30]; return c if any(c) else None
def pin_ok(pin):
    if not PIN_REC: return False
    return hmac.compare_digest(_phash(str(pin)[:100], PIN_REC[0]), PIN_REC[1])
def setup_pin():
    global PIN_REC
    env = os.environ.get('MENTI_PIN', '')
    if len(env) >= 4: PIN_REC = make_pin(env); return '  Teacher PIN: taken from the MENTI_PIN setting.'
    if '--reset-pin' not in sys.argv:
        PIN_REC = load_pin()
        if PIN_REC: return '  Teacher PIN: saved (run with --reset-pin to change it).'
    if sys.stdin.isatty():
        print('\n  Set a teacher PIN / password (at least 4 characters).')
        while True:
            a = getpass.getpass('  New PIN: ')
            if len(a) < 4: print('  Too short, try again.'); continue
            if getpass.getpass('  Repeat PIN: ') != a: print('  They do not match, try again.'); continue
            PIN_REC = make_pin(a); save_pin(PIN_REC); return '  Teacher PIN saved.'
    a = ''.join(random.choices('0123456789', k=6)); PIN_REC = make_pin(a); save_pin(PIN_REC)
    return '  Teacher PIN (generated, shown only now): ' + a
SEEN = {}
RIDS = set()   # (client id, request id) of submits already applied, so a retry after a lost reply never counts twice
CLAIM = {}   # (section, roster name) -> client id that joined with it; cleared on every server start
CLAIM_TTL = 120   # a claimed name is freed if that device has not been seen for this many seconds
def is_roster(sec, name): return sec in ROSTER and name in ROSTER[sec]
def live_set():
    # (section, name) of students whose device has been seen in the last 8 seconds = present
    now = time.time(); return {(D['secs'].get(c), D['names'].get(c)) for c, t in SEEN.items() if now - t < 8}
def claimed_other(sec, name, cid):
    c = CLAIM.get((sec, name))
    return bool(c) and c != cid and time.time() - SEEN.get(c, 0) < CLAIM_TTL
def claim(sec, name, cid):
    for k in [k for k, c in CLAIM.items() if c == cid]: del CLAIM[k]
    if is_roster(sec, name): CLAIM[(sec, name)] = cid
SESSION = ''.join(random.choices('abcdefghijklmnopqrstuvwxyz0123456789', k=10))   # new on every server start
# ---- EVIDENCE SETTINGS ----
SPEED_WEIGHTED = False   # False = a correct answer earns the same however fast it is sent. True = old behaviour (faster = more points / harder boss hit)
SMART_MIX = True         # True = with several topics ticked, weaker / less recently practised topics are drawn more often (every topic still appears)
TARGET_LO, TARGET_HI = 0.70, 0.90   # productive-success band; the host gets a notice when the last TRACK_N answers fall outside it
TRACK_N = 30
TOPICS = ['Basic Operations', 'Integers', 'Fractions', 'Word Problem', 'Algebra', 'Percent & Ratio', 'Geometry & Data']
# Class roster (GNHS S.Y. 2026-2027) embedded from the Excel file
ROSTER = {
    "Grade 7 – Bonifacio": ["Rhenz Bedayo", "Lance Costillas", "Carl Ivanne Dela Cerna", "Lorence Maldo", "Ruziel Nuñez", "Emanuel Olay", "Cristian John Paloga", "Chris William Parayno", "Achilles Gabriel Ranes", "Tyrone Jayden Sereguilla", "Meyjun James Tangpuz", "Nathaniel Terwel", "Aslen Jane Arañez", "Zaria Baleros", "Jelyn Briz", "Rhienzel Damole", "Angel Duarte", "Hannah Jane Maike", "Denise Erika Mantilla", "Jan Desiree Padayao", "Arianne Sagarino"],
    "Grade 7 – Rizal": ["Luis Edrich Agcol", "Aldren Bandayanon", "Mark John Briz", "Nigel Kent Catandijan", "Brent Cloma", "Nico Alexis Corbilla", "Ruel Dolera", "Francis Ryan Doron", "Charles Gabriel Lamera", "Mark Uzziah Lastra", "Mathew Macaldo", "Vince Anthony Maturan", "John Aldrin Paler", "John Euseb Piquero", "John Rhileiy San Gabriel", "Jenjen Aguilar", "Bea Blasabas", "Kylie Briz", "Alexa Eunice Caberte", "Rosemarie Dolera", "Shelden Louise Doron", "Charmine Melchor", "Ruby Ann Reyes", "Xhai Emmabelle Telen"],
    "Grade 8 – Aquino": ["Nathan Johnly Agcaoili", "Jude Norlvin Corvilia", "Mark Clifford Costillas", "Jonathan Doron", "Hirroh Matthew Kirong", "Cedrick France Mandao", "Chead Mantilla", "Jerwhin Markines", "James Gabriel Padrones", "Jarred Sabenorio", "Renan Sagarino", "Izzy Rose Balili", "Yllona Kate Bayud", "Cyrell Jacey Briz", "Ashley Jane Caberte", "Kristine Angel Canaya", "Celine Cheng", "Jolie Iyana Cusio", "Hanniyah Florentino", "Nickey Galanza", "Brishel Doraine Lleno", "Lianne Jhane Noya", "Kia Monique Piquero", "Ayeisha Mhe Sagarino"],
    "Grade 8 – Jacinto": ["Marvin Jr Abainza", "Karl Angelo Doron", "Joseph Magpatoc", "Marco Medina", "Rex Pacuancuan", "Franz Kristian Sabalo", "Mark Joseph Saga", "Jay Lord Solis", "Rhexine Dave Vismanos", "Claire Asupan", "Ezhelle Jean Baluran", "Junice Caberte", "Kris Kate Lee Cailing", "Kia Mae Casten", "Bianca Louise Catanghal", "Quisha Wenseslane Damole", "Mary Margaux Dancis", "Janine Evangelio", "Rica Joy Evangelio", "Samantha Galo", "Menie Rose Llever", "Sofia Monique Magbanua", "Arria Jean Maike", "Larah Maldo", "Ma. Vienne Amparo Pelin", "Allyza Reyes"],
    "Grade 8 – Mabini": ["Chadrick Arañez", "Mark Kevin Ardan", "Jingfel Bartolome", "Mhon Cantoneros", "Rency Costillas", "Nathan Louie Dorias", "Hansel James Gaviola", "Kenn Lean Masalaysay", "Lance Kean Masalaysay", "John Clark Padecio", "Liniel Punay", "Arianne Kim Barcenas", "Mariza Briz", "Samantha Canales", "Lezly Venize Costillas", "Ezra Seidel Cutamora", "Savrhina Cutanda", "Jussiel Del Rosario", "Cathllea Shanna Doron", "Nheyca Doron", "Ma. Faith Angel Evangelio", "Hossana Reign Maglupay", "Chloe Maike", "Melanie Maique", "Vance Karylle Mangaliman", "Catherine Markines", "Rhicca Ella Mayorca"],
    "Grade 9 – Del Pilar": ["John Jaeden Aguilar", "Charles Caberte", "Nikko Caberte", "Kian Emmanuel Costillas", "Warren Costillas", "Ranz Jade Doron", "Jennifer Evangelio", "Gavi Galo", "Jhanlee Gonzales", "Justine Gonzales", "Zeus Jireh Grafe", "Rico Lagunay", "Eujon Lucino", "Jared Saga", "Dylan Sagarino", "Kent Evans Sanico", "Joshua Taguinod", "Mary Jane Barte", "Shekhinah Glory Buhian", "Ma Carissa Cipres", "Kristie Mae Doron", "Yllyreh Charm Doron", "Ellaizah Venice Kirong", "Aleah Lerio", "Jenalyn Paquidongan", "Kylie Loraine Piquero", "Margareth Sumaya", "Abygail Vanzuela"],
    "Grade 9 – Juan Luna": ["Jenry Abusca", "Lorjon Aranas", "Charles Jhon Timothy Aroy", "Alvin Bandayanon", "Steeve John Bhatkar", "Charles Dela Luz", "Mark Anthony Doron", "Ramil Evangelio", "John Kenneth Gumaru", "Emmanuel John Lamera", "Seth Eleazar Layola", "Vann Aiken Masalaysay", "Daniel Quirequire", "Khean James Quirong", "Prince Lawrence Rico", "Kristoff Sanico", "Herbert Toledo", "Dimples Ante", "Charise Buscayan", "Jelian Costillas", "Precious Pearl Costillas", "Aliza Doron", "Allana Abegail Doron", "Abigail Latorre", "Trishia Mae Moralde", "Je-Ann Olay", "Khesha Quirong"],
    "Grade 10 – Dagohoy": ["Alec Lester Abangon", "John Nico Briz", "John Doron", "Joey Dalugdugan", "Ezrah Nathaniel Dorias", "Jay Entuna", "Almer June Jorjieo", "King Vincent Pagare", "Jimmy Quirong", "Reynaldo Yadao", "Jasmin Baluran", "Aubrey Caberte", "Kathlyn Kate Clava", "Maekyla Doron", "Johanna Chlouie Guarte", "Jela Mantilla", "Angella Grace Maturan"],
    "Grade 10 – Silang": ["Marlon Ardan", "Jemmie Del Rosario", "Christian Evangelio", "Jade Xavier Inajenes", "Mart Orland Llever", "Randy Pacuancuan", "Far East John Pates", "Sean Kyle Quirong", "Aldrich Talay", "Charmille Arañez", "Janine Balmoria", "Khevy Briz", "Nikki Shayne Catandijan", "Piel Costillas", "Ricel Mae Costillas", "Arianne Mantilla", "Lyza Mae Mantilla", "Rhein Maturan", "Irene Mae Pagal", "Marie Therese Panelo"],
}
voters = {}  # slide id -> {client id: choice or count}

def blank(t, i):
    o = {'mc': ['Option 1', 'Option 2'], 'quiz': ['A', 'B', 'C', 'D']}.get(t, [])
    return {'id': i, 'type': t, 'q': 'New question', 'opts': o, 'votes': {}, 'words': {}, 'answers': [],
            'ans': '', 'time': 0, 'start': 0, 'rev': False, 'by': {}, 'turn': '', 'log': [], 'topic': TOPICS[0]}

OLD_DEFAULTS = {'125 + 238 = ?', '47 × 6 = ?', 'Evaluate: 8 × 3', 'Which is the same as 7 × 8?', '144 ÷ 12 = ?', 'Explain: how can you check the answer to 72 ÷ 6 using multiplication?', '-5 + -5 = ?', '7 + (-12) = ?', 'Which number is the greatest?', '(-6) × (-4) = ?', '-20 ÷ 4 = ?', 'How do you subtract a negative number? Show it with -3 - (-7).', '1/2 + 1/4 = ?', 'Which fraction is equivalent to 2/3?', '3/5 × 10 = ?', 'Which fraction is the greatest?', '5/6 - 1/3 = ?', 'How do you add 1/3 + 1/4? What is the first step?', 'Ana has 24 mangoes. She gives 1/3 of them to her friend. How many mangoes does she have left?', 'A notebook costs 35 pesos. How much do 6 notebooks cost?', 'A pizza is cut into 8 equal slices. Ben eats 3 slices. What fraction of the pizza is left?', 'The temperature was -4 degrees in the morning and rose by 9 degrees. What is the temperature now?', 'Maria walked 2.5 km on Monday and 3.75 km on Tuesday. How many km did she walk altogether?', 'Write a word problem for 12 × 5, then explain how you would solve it.'}  # built-in sample questions from older versions; removed on startup

FRESH = False
try:
    D = json.load(open(FILE))
except Exception:
    s = blank('mc', 1); s.update(q='What should we learn next?', opts=['Design', 'Code', 'Data'])
    D = {'slides': [], 'cur': 0, 'open': True, 'nid': 1}; FRESH = True

_rs = {str(k): [str(n) for n in v] for k, v in (D.get('roster') or {}).items() if isinstance(v, list)} if isinstance(D.get('roster'), dict) else {}
if _rs: ROSTER.clear(); ROSTER.update(_rs)   # the Roster tab edits the saved copy; the list embedded in this file is only the starting point
D['roster'] = ROSTER
D.setdefault('bon', {})   # bon: bonus points a boss battle gave (+); pen below is what was taken off (-)
D.setdefault('noisy', {}); D.setdefault('nlog', []); D.setdefault('pen', {})   # pen: points actually taken off for noise
D.setdefault('prof', {})   # prof['section|name'] = {av, th, mo}: the student's avatar / colour / motto, kept on the server so it follows them to any device
D.setdefault('names', {}); D.setdefault('secs', {}); D.setdefault('scores', {}); D.setdefault('board', False)
D.setdefault('section', next(iter(ROSTER))); D.setdefault('picked', []); D.setdefault('rp', {'n': 0, 'name': '', 'sec': '', 'wrapped': False})
D.setdefault('rtime', 30); D.setdefault('rcount', 1); D.setdefault('goal', 0); D.setdefault('ok', {}); D.setdefault('notice', ''); D.setdefault('announced', None); D.setdefault('back', []); D.setdefault('ann', {}); D.setdefault('level', 1); D.setdefault('shape', {})   # shape: topic -> digit code like '22' (2-digit by 2-digit); '' = mixed by grade level
if D.get('lvv') != 2: D['level'] = {1: 2, 2: 6}.get(D.get('level'), 2); D['lvv'] = 2   # level code is now 1..8 (grade band x difficulty); old saved 1 / 2 become 'Grade 7-8 average' / 'Grade 9-10 average'
D.setdefault('att', {})   # att[key] = {session~token: topic}: cumulative ATTEMPTS per topic (same shape as life, which holds the points)
D.setdefault('life', {}); D['lsn'] = D.get('lsn', 0) + 1   # life[key] = {session~token: topic}: cumulative correct answers per topic, kept across sessions (never cleared by goalreset); lsn = session number
D.setdefault('lastq', {})   # lastq[key] = the last question each student answered (for the study review)
D.setdefault('lfuse', {})   # lifelines used per student this session: lfuse[key] = {'pass': n, 'friend': n}
D.setdefault('sk', {}); D.setdefault('skerr', {})   # sk[key] = {session~token: 'add'|'sub'|'mul'|'div'}: the operation skill of every graded attempt; skerr[key][skill][tag] = wrong answers by error type
D.setdefault('err', {}); D.setdefault('recent', {}); D.setdefault('tlast', {})   # err[section][topic][tag] = wrong answers by error type; recent[section] = last answers (1/0); tlast[section][topic] = when last practised
D.setdefault('boss', None)   # boss battle state (see boss_start)
D.setdefault('mix', list(TOPICS))   # (fresh installs start interleaved) topics ticked on the dashboard: picks / new questions / team game draw randomly from these (empty = use the highlighted tab)
D.setdefault('tgoal', 0); D.setdefault('tann', []); D.setdefault('tleft', {})   # tleft[section] = teams the teacher let leave the room: [{id, name, m, tot (final score)}]
D.setdefault('tgoal', 0)   # tgoal = points a team needs before it may leave (0 = off); tann = teams already announced as finished
D.setdefault('onlyon', False); D.setdefault('tloop', False); D['tloop'] = False   # team auto-question loop (always off after a restart)
D.setdefault('teams', {}); D.setdefault('tmode', False); D.setdefault('tadj', {}); D.setdefault('tlog', []); D.setdefault('thist', [])   # teams[section] = [{id, name, m: [names]}]; tadj = teacher bonus/deduction per team; thist = points per team for each finished round
for _k, _v in {'ans': '', 'mark': None, 'tstart': 0, 'tdur': 30, 'tfz': None, 'show': False, 'picks': []}.items(): D['rp'].setdefault(_k, _v)
for _x in D['slides']:
    for _k, _v in blank('mc', 0).items(): _x.setdefault(_k, _v)
D['slides'] = [x for x in D['slides'] if x.get('auto') or x['q'] not in OLD_DEFAULTS]
D['cur'] = max(0, min(D['cur'], len(D['slides']) - 1))

_DIRTY = threading.Event()

def save():
    # called after every answer: do NOT write the file here (30 students answering at once would write it 30 times while
    # everybody waits). Just flag it; one background thread writes it a moment later, once for the whole burst.
    _DIRTY.set()

def _write_now():
    try:
        with lock: data = json.dumps(D, separators=(',', ':'))   # compact: less time holding the lock
        tmp = FILE + '.tmp'
        with open(tmp, 'w') as f: f.write(data)
        os.replace(tmp, FILE)          # never leaves a half-written data file
    except Exception: pass

def _saver():
    # json.dumps(D) runs while holding the lock, so during a burst of answers it must not run often: wait 2 s, then write once
    while True:
        _DIRTY.wait(); time.sleep(5.0); _DIRTY.clear(); _write_now()   # one write per 5 s however many answers arrive

threading.Thread(target=_saver, daemon=True).start()
import atexit; atexit.register(_write_now)

def ips():
    found = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); s.connect(('10.255.255.255', 1)); found.append(s.getsockname()[0])
    except Exception: pass
    try: found += socket.gethostbyname_ex(socket.gethostname())[2]
    except Exception: pass
    out = []
    for i in found:
        if not i.startswith('127.') and i not in out: out.append(i)
    return out or ['localhost']
IPS = ips()

def cur(): return D['slides'][D['cur']]

def mixpool(): return [t for t in TOPICS if t in D.get('mix', [])]
def pretest_acc(sec):
    # class pre-test result per topic {topic: [correct, items]} from the PRE-TEST section below (TD); the starting point for targeting
    out = {}
    _TD = globals().get('TD', {}); _src = [_TD.get('resp', {}).get('pre', {})] + [sn.get('pre', {}) for sn in ((_TD.get('sets', {}).get(sec)) or {}).get('items', {}).values()]   # also the pre-tests of the section's other tests
    for key, r in [kv for m_ in _src for kv in m_.items()]:
        if key.split('|', 1)[0] != sec or not r.get('res'): continue
        for t, (c, n) in r['res']['per'].items(): o = out.setdefault(t, [0, 0]); o[0] += c; o[1] += n
    return out
def sec_acc(sec, pre=False):
    # class accuracy per topic over all sessions: {topic: (correct, attempts)}; pre=True also counts the pre-test (used for targeting only)
    ok = {t: 0 for t in TOPICS}; at = {t: 0 for t in TOPICS}
    if pre:
        for t, v in pretest_acc(sec).items():
            if t in ok: ok[t] += v[0]; at[t] += v[1]
    for n in ROSTER.get(sec, []):
        k = skey(sec, n)
        for t in D['life'].get(k, {}).values():
            if t in ok: ok[t] += 1
        for t in D['att'].get(k, {}).values():
            if t in at: at[t] += 1
    return {t: (ok[t], at[t]) for t in TOPICS}
def topic_weights(sec, pool):
    # weight = 1 (floor, so every ticked topic keeps appearing = interleaving) + up to 3 for weakness + up to 1 for time since last practised (spacing)
    acc = sec_acc(sec, True); last = D['tlast'].get(sec, {}); now = time.time(); w = []
    for t in pool:
        c, a = acc[t]; p = (c + 2.25) / (a + 3.0)   # smoothed so 1 lucky / unlucky answer does not swing it
        weak = max(0.0, 0.9 - p) / 0.9
        gap = min(1.0, (now - last.get(t, 0)) / 1800.0)
        w.append(1.0 + 3.0 * weak + gap)
    return w
def pick_topic(default, avoid=None):
    # one of the ticked topics (not the same as last time when there is a choice); nothing ticked = the given default
    m = mixpool()
    if not m: return default
    pool = [t for t in m if t != avoid] or m
    sec = D.get('section')
    t = random.choices(pool, weights=topic_weights(sec, pool))[0] if SMART_MIX and len(pool) > 1 else random.choice(pool)
    D['tlast'].setdefault(sec, {})[t] = time.time()
    return t

def isq(s): return s['type'] in ('quiz', 'num')

def left(s):
    if not s['time']: return None
    if not s['start']: return s['time']
    return max(0, s['time'] - (time.time() - s['start']))

def canvote(s):
    if not D['open'] or s['rev']: return False
    if s['time']: return bool(s['start']) and time.time() - s['start'] < s['time'] + 1
    return True

def numval(x):
    # tolerant number parser: accepts −, ₱, %, units (km, pesos), 1,000 / 3,5, (-5), fractions like 3/4
    try:
        x = str(x).strip().lower().replace('−', '-').replace('–', '-').replace('₱', '').replace('%', '')
        x = re.sub(r'[()\s]', '', x); x = re.sub(r'^(php|x=|=)', '', x); x = re.sub(r'[a-z²³°]+$', '', x)
        x = x.replace(',', '') if re.fullmatch(r'-?\d{1,3}(,\d{3})+(\.\d+)?', x) else x.replace(',', '.')
        if '/' in x: a, b = x.split('/', 1); return float(a) / float(b)
        return float(x)
    except Exception: return None

def correct(s, v):
    if s['type'] == 'quiz': return v == s['ans']
    a, b = numval(v), numval(s['ans'])
    if a is None or b is None: return str(v).strip().lower() == str(s['ans']).strip().lower()
    return abs(a - b) <= 1e-6 * max(1, abs(b))

def skey(sec, name): return '%s|%s' % (sec, name)

# ---------------- Lifelines (cold-call rounds) ----------------
# Every student gets LIFE_USES uses of EACH lifeline per session (a new session / goal reset gives them back):
#   'pass'   = pass the question to a classmate. The classmate answers on their own device and EARNS the point.
#   'friend' = ask a friend. The friend answers on their own device, but the point goes to the student who was picked.
LIFE_USES = 2
LIFE_WINDOW = 5   # decision phase: seconds between the pick and the START of the answer timer. Picked students may choose a lifeline now; nobody can answer yet, so everyone then answers on the same clock
def dec_for(p):
    # a fresh round (nobody answered / used a lifeline yet) gets the decision phase before its timer
    return LIFE_WINDOW if p.get('picks') and not any(str(q.get('ans', '')).strip() or q.get('lf') for q in p['picks']) else 0
def pkey(q):
    # the student who earns the point of this pick
    lf = q.get('lf')
    if lf and lf.get('k') == 'pass': return skey(lf['sec'], lf['to'])
    return skey(q['sec'], q['name'])
def hidx(cid):
    # index of the pick this student is helping with (None = not a helper)
    p = D['rp']
    if not (p.get('show') and p.get('picks')): return None
    k = (D['secs'].get(cid), D['names'].get(cid))
    for i, q in enumerate(p['picks']):
        lf = q.get('lf')
        if lf and (lf['sec'], lf['to']) == k: return i
    return None
def lf_left(key):
    u = D['lfuse'].get(key, {}); return {'pass': max(0, LIFE_USES - u.get('pass', 0)), 'friend': max(0, LIFE_USES - u.get('friend', 0))}
def lf_can(q):
    p = D['rp']
    if q.get('lf') or q.get('mark') or str(q.get('ans', '')).strip() or p.get('fin'): return False
    if p.get('tdur') and p.get('tstart') and time.time() - p['tstart'] >= p['tdur'] + 1: return False
    if p.get('tdur') and (p.get('tfz') is not None or (p.get('tstart') and time.time() >= p['tstart'] + 0.5)): return False   # decision phase is over (timer running or paused)
    return True
def lf_opts(ri):
    # classmates (same section, online) who can still be asked: not picked, not already helping, not finished
    p = D['rp']; q = p['picks'][ri]; sec = q['sec']; now = time.time()
    busy = {(x['sec'], x['name']) for x in p['picks']} | {(x['lf']['sec'], x['lf']['to']) for x in p['picks'] if x.get('lf')}
    out = []
    for c, t in SEEN.items():
        n = D['names'].get(c)
        if now - t < 8 and D['secs'].get(c) == sec and n and n not in out and (sec, n) not in busy and not is_out(skey(sec, n)) \
           and not any(n in t_['m'] for t_ in D['tleft'].get(sec, [])): out.append(n)
    return sorted(out)
def lifeline(d):
    cid = str(d.get('cid', ''))[:40]; kind = d.get('k'); to = str(d.get('to', ''))[:40]
    if kind not in ('pass', 'friend') or cid not in D['names']: return
    ri = ridx(cid)
    if ri is None or ri < 0: return
    q = D['rp']['picks'][ri]; key = ckey(cid)
    if not lf_can(q) or lf_left(key)[kind] <= 0 or to not in lf_opts(ri): return
    q['lf'] = {'k': kind, 'to': to, 'sec': q['sec']}
    D['lfuse'].setdefault(key, {})[kind] = D['lfuse'].get(key, {}).get(kind, 0) + 1
    D['notice'] = ('🙋 %s passed the question to %s' if kind == 'pass' else '📞 %s asked a friend: %s') % (q['name'], to); D['noticet'] = time.time()
    save()
def ckey(c): return skey(D['secs'].get(c, ''), D['names'].get(c, ''))
def qtok(sl): return '%s:%s:%s' % (sl.get('id'), sl.get('gv', 0), sl.get('q'))
def credit(key, tok, yes, topic=None):
    t = D['ok'].setdefault(key, [])
    if yes and tok not in t: t.append(tok)
    if not yes and tok in t: t.remove(tok)
    lt = '%s~%s' % (D['lsn'], tok); L_ = D['life'].setdefault(key, {})   # cumulative tally (all sessions)
    if yes: L_.setdefault(lt, topic or cur()['topic'])
    else: L_.pop(lt, None)
def attempt(key, tok, yes=True, topic=None, q=None):
    # one graded attempt (right or wrong). Idempotent per session~token, like credit()
    # q = the question text: when it is a plain two-number operation the attempt is also filed under its skill (add / sub / mul / div)
    lt = '%s~%s' % (D['lsn'], tok); A_ = D['att'].setdefault(key, {})
    if yes:
        A_.setdefault(lt, topic or cur()['topic'])
        if q is not None:
            sk_ = skill_of(q, A_[lt])
            if sk_: D['sk'].setdefault(key, {}).setdefault(lt, sk_)
    else:
        A_.pop(lt, None); (D['sk'].get(key) or {}).pop(lt, None)
def rattempts(p, force=False):
    # students who made an attempt in this cold-call round:
    #  - the picked student ALWAYS (using a lifeline, pass or friend, counts as an attempt that is automatically a miss; a point can still come
    #    back to them when the friend answered correctly)
    #  - the classmate who took a PASS (they answered in the picked student's place, right or wrong)
    #  - a FRIEND only helps, so a friend never gets an attempt
    out = []
    for q in p.get('picks', []):
        done = bool(q.get('mark')) or bool(p.get('fin')) or force; lf = q.get('lf')
        if done or lf: out.append(skey(q['sec'], q['name']))
        if lf and lf.get('k') == 'pass' and done: out.append(skey(lf['sec'], lf['to']))
    return out
def life_att(key):
    # attempts per topic over ALL sessions (+ the current cold-call round that is not committed yet)
    out = {t: 0 for t in TOPICS}; toks = dict(D['att'].get(key, {})); p = D['rp']
    if key in rattempts(p): toks['%s~%s' % (D['lsn'], rtok(p))] = p.get('topic') or cur()['topic']
    for t in toks.values():
        if t in out: out[t] += 1
    return out
def life(key):
    # correct answers per topic over ALL sessions (+ the current cold-call round that is not committed yet)
    out = {t: 0 for t in TOPICS}; toks = dict(D['life'].get(key, {})); p = D['rp']
    for q in p.get('picks', []):
        if q.get('mark') == 'ok' and pkey(q) == key: toks['%s~%s' % (D['lsn'], rtok(p))] = p.get('topic') or cur()['topic']
    for t in toks.values():
        if t in out: out[t] += 1
    return out
def rtok(p): return '%s@r%s' % (p.get('tok') or 'r', p.get('n'))   # unique per cold-call round: every correct answer counts, even if the same question is asked again
def okcount(key):
    # correct answers = committed (previous rounds / device answers) + current cold-call round marks
    toks = set(D['ok'].get(key, [])); p = D['rp']
    for q in p.get('picks', []):
        if q.get('mark') == 'ok' and pkey(q) == key: toks.add(rtok(p))
    return max(0, len(toks) + D['bon'].get(key, 0) - D['pen'].get(key, 0))
def tm_member(key):
    # team mode ON and this student belongs to a team (or to a team that already left): leaving is decided per TEAM, never per student
    if not D.get('tmode'): return False
    sec, name = split_key(key)
    return any(name in t_['m'] for t_ in D['teams'].get(sec, []) + D['tleft'].get(sec, []))
def left_team(key):
    sec, name = split_key(key)
    return next((t_ for t_ in D['tleft'].get(sec, []) if name in t_['m']), None)
def classmode(): return D.get('mode') == 'class' or boss_live()   # class (boss battle) mode has NO goal: nobody leaves the room
def reached(key): return D['goal'] > 0 and not classmode() and not tm_member(key) and okcount(key) >= D['goal']
def is_out(key): return reached(key) and key not in D['back']
def all_out():
    ks = {skey(k, n) for k in ROSTER for n in ROSTER[k]} | set(D['ok'])
    return sorted(k for k in ks if is_out(k))
def all_reached():
    ks = {skey(k, n) for k in ROSTER for n in ROSTER[k]} | set(D['ok'])
    return sorted(k for k in ks if reached(k))
def nkey(e): return e if isinstance(e, str) else e[0]
def split_key(k):
    sec, _, name = k.partition('|'); return sec, name
def check_finished(silent=False):
    # announce students who just reached the goal (once each); silent = just re-sync after the goal changed
    now = set(all_out())
    if silent or D.get('announced') is None or D['goal'] <= 0:
        D['announced'] = sorted(now); return
    new = sorted(now - set(D['announced']))
    D['announced'] = sorted(now)   # students who dropped below the goal get announced again if they re-qualify
    if new:
        D['ann'] = {'id': D.get('ann', {}).get('id', 0) + 1, 't': time.time(),
                    'names': [{'n': split_key(k)[1], 's': split_key(k)[0], 'got': okcount(k)} for k in new]}
        save()

def commit_round():
    record_round()
    p = D['rp']
    for q in p.get('picks', []):
        if q.get('mark') == 'ok': credit(pkey(q), rtok(p), True, p.get('topic'))
    # the round is being closed or replaced: every picked student made an attempt, even one who never answered (a skip is a wrong attempt)
    for k_ in rattempts(p, force=bool(p.get('show') and p.get('picks'))): attempt(k_, rtok(p), True, p.get('topic'), _rq(p, k_))

# ---------------- Boss battle ----------------
# Whole class vs one boss. Correct answer = damage (faster = harder hit only when SPEED_WEIGHTED), wrong answer = heals the boss.
# Runs on the auto-question loop; damage is applied once per question inside reveal().
BOSS_DMG = 10      # damage of one correct answer (plus up to +5 for a fast answer)
BOSS_HEAL = 5      # HP the boss regains for each wrong answer
RUSH_SEC = 3      # a WRONG answer sent within this many seconds of the question appearing counts as a rushed guess; it counts toward the inactive streak (no point penalty)
IDLE_AT = 3        # this many skips in a row = flagged as inactive on the host panel
FAST_SEC = 10      # a correct answer sent within this many seconds earns the 'fast answer' bonus
def bp_cid(k):
    for c in D['names']:
        if ckey(c) == k: return c
    return None
BOSS_NAMES = ['Count Dracula-Zero', 'The Fraction Dragon', 'Lord Negatron', 'Sir Divides-a-Lot', 'The Integer Kraken', 'Baron Von Remainder']
DBL_SEC = 15       # length of a "double damage" power-up round
BOSS_SAY = {
    'start': ['Foolish students! Your math cannot touch me!', 'Another class dares to challenge me? Bring it!', 'I have eaten a thousand worksheets. Yours are next!'],
    'enrage': ["NOW YOU'VE MADE ME ANGRY!", 'Grrr! I was only warming up!', 'You will regret that! I heal even faster now!'],
    'heal': ['Ha ha! Wrong again. I feel better already!', 'Mmm, delicious mistakes!', 'Check your work next time!'],
    'low': ["No... I'm almost beaten! Please don't finish me!", 'I can feel my HP slipping away...'],
    'dbl': ['⚡ POWER-UP! Every correct answer hits TWICE as hard!', '⚡ The boss is glitching! DOUBLE DAMAGE, hit it now!'],
    'won': ['Impossible... defeated by a class of mathematicians!', 'You win this time... but I will be back!'],
    'lost': ['Bwahaha! Time is up and I am still standing!', 'Better luck next time, little mathematicians!'],
}
BOSS_OWN = {
    'Count Dracula-Zero': {'start': ['I vant to zero your scores!'], 'lost': ['Zero for you! Bwahaha!']},
    'The Fraction Dragon': {'start': ['I will split your hopes into halves!'], 'lost': ['Only half of you were really trying!']},
    'Lord Negatron': {'start': ['Everything you add, I subtract!'], 'lost': ['Negative points for everyone!']},
    'Sir Divides-a-Lot': {'start': ['I divide and I conquer!'], 'lost': ['You were divided, and I conquered!']},
    'The Integer Kraken': {'start': ['Positive or negative, you all sink!'], 'lost': ['Back to the deep with you!']},
    'Baron Von Remainder': {'start': ['There is always something left over: ME!'], 'lost': ['I am the remainder you could not remove!']},
}
def boss_say(b, ev, force=True):
    # a short taunt / victory line shown on the boss bubble (soft events are rate limited)
    now = time.time()
    if not force and now - b.get('sayt', 0) < 6: return
    pool = list(BOSS_SAY.get(ev, [])) + BOSS_OWN.get(b['name'].split(' ', 1)[-1], {}).get(ev, [])
    if not pool: return
    b['sn'] = b.get('sn', 0) + 1; b['sayt'] = now
    b['say'] = {'id': '%s:%s' % (b.get('sd'), b['sn']), 't': random.choice(pool), 'ev': ev}
def boss_enraged(b): return 0 < b['hp'] <= b['max'] * 0.5
def boss_dbl(b): return time.time() < b.get('dbl', 0)
def boss_mult(b): return 2 if boss_dbl(b) else 1
def boss_heal(b): return BOSS_HEAL + (3 if boss_enraged(b) else 0)   # an angry boss heals more for each wrong answer
def boss_phase(b):
    if b['hp'] <= 0: return
    if b['hp'] <= b['max'] * 0.5:
        if not b.get('enr'): b['enr'] = True; boss_say(b, 'enrage')
        if b['hp'] <= b['max'] * 0.15 and not b.get('lowsaid'): b['lowsaid'] = True; boss_say(b, 'low')
    else: b['enr'] = False; b['lowsaid'] = False
def boss_powerup():
    # now and then the boss "glitches": a short DOUBLE DAMAGE round where every correct answer hits twice as hard
    b = D.get('boss'); now = time.time()
    if b and b.get('st') == 'fight' and now >= b.get('nd', 0) and now >= b.get('dbl', 0) and b['end'] - now > DBL_SEC + 5:
        b['dbl'] = now + DBL_SEC; b['nd'] = now + DBL_SEC + random.randint(50, 80); boss_say(b, 'dbl'); save()
def boss_live(): b = D.get('boss'); return bool(b and b.get('st') == 'fight')
def boss_off():
    b = D.get('boss')
    if b and b.get('st') in ('fight', 'won', 'lost'): b['st'] = 'idle'
    D['tloop'] = False
LOOK_ENUM = {'head': ['none', 'horns', 'ears', 'spikes', 'crown', 'helmet', 'tophat', 'party', 'viking', 'pirate', 'wizard', 'chef', 'bunny', 'halo', 'antenna'],
             'eyes': ['angry', 'round', 'sleepy', 'cyclops', 'hearts', 'stars', 'dizzy', 'cat', 'robot', 'wink', 'three'],
             'mouth': ['grin', 'fangs', 'smile', 'tongue'], 'face': ['none', 'baron', 'glasses', 'eyepatch', 'stache', 'shades', 'mask', 'clown', 'scar'],
             'neck': ['none', 'bowtie', 'cape', 'badge'], 'legs': ['feet', 'tent']}
def boss_look(l):
    # teacher's custom boss look: only whitelisted choices, #rrggbb colours and a 2-character symbol get through
    out = {}
    if not isinstance(l, dict): return out
    for k, ok in LOOK_ENUM.items():
        if l.get(k) in ok: out[k] = l[k]
    for k in ('body', 'line', 'eyec', 'mouthc', 'hc'):
        v = l.get(k)
        if isinstance(v, str) and re.fullmatch(r'#[0-9a-fA-F]{6}', v): out[k] = v
    if isinstance(l.get('sym'), str): out['sym'] = re.sub(r'[^\w±÷×½¼¾+=%?!-]', '', l['sym'])[:2]
    return out
def adj_val(v):
    # teacher's point change for one situation: whole number from -10 to +10
    try: return max(-10, min(10, int(float(v or 0))))
    except Exception: return 0
def bp_pts(k, c, delta):
    # give (+) or take off (-) points of one student in a paced battle. A deduction never takes them below 0. Returns the change really applied.
    if not delta: return 0
    c = c if c in D['names'] else next((c_ for c_ in D['names'] if ckey(c_) == k), None)
    if delta > 0: got = delta; D['bon'][k] = D['bon'].get(k, 0) + got
    else:
        got = -min(-delta, okcount(k))
        if got: D['pen'][k] = D['pen'].get(k, 0) - got
    if got and c is not None: D['scores'][c] = max(0, D['scores'].get(c, 0) + got)
    if got: check_finished(True)
    return got
def boss_start(d):
    sec = D['section']; n = max(1, sum(1 for (s_, _n) in live_set() if s_ == sec))
    hpp = max(1, min(60, int(float(d.get('hpp') or 5)))); mins = max(1, min(60, float(d.get('mins') or 10)))
    hp = n * hpp * BOSS_DMG   # automatic: students present x correct answers each x damage
    try:   # teacher typed an exact boss HP -> use it instead of the automatic value
        _c = d.get('bhp')
        if _c not in (None, ''): hp = max(1, min(100000, int(float(_c))))
    except (ValueError, TypeError, OverflowError): pass
    D['boss'] = {'st': 'fight', 'name': '👹 ' + (d.get('bname') if d.get('bname') in BOSS_NAMES else random.choice(BOSS_NAMES)), 'hp': hp, 'max': hp, 'end': time.time() + mins * 60,
                 't0': int(time.time() * 1000), 'dealt': {}, 'last': None, 'hits': 0, 'mix': bool(d.get('mix')), 'var': bool(d.get('var')), 'n': 0,
                 'pace': bool(d.get('pace')), 'sd': random.randint(1, 10 ** 9), 'qt': max(5, min(300, int(float(d.get('qsec') or 30)))), 'lv': D.get('level', 1), 'stu': {}, 'look': boss_look(d.get('look')),
                 'adj': {'bad': adj_val(d.get('adjb')), 'skip': adj_val(d.get('adjs')), 'idle': adj_val(d.get('adji')), 'ok': max(0, adj_val(d.get('adjo'))), 'fast': max(0, adj_val(d.get('adjf')))}, 'enr': False, 'dbl': 0, 'nd': time.time() + random.randint(40, 70), 'sn': 0, 'say': None, 'sayt': 0, 'lowsaid': False}
    D['boss']['topic'] = d.get('topic') if d.get('topic') in TOPICS else cur()['topic']
    pl = [t for t in TOPICS if t in d['topics']] if isinstance(d.get('topics'), list) else []
    if pl: D['boss']['pool'] = pl; D['boss']['mix'] = len(pl) > 1; D['boss']['topic'] = pl[0]
    boss_say(D['boss'], 'start')
    D['tloop'] = False; D['rp']['show'] = False; D['shown'] = True
    g = make(random.choice(D['boss'].get('pool') or [D['boss']['topic']]), 'num', D.get('level', 1))
    if not D['boss']['var']: g['var'] = False   # same question for everyone -> it can be shown on the projector
    g['time'] = int(D['rtime']) or 30; g['start'] = time.time()
    if D['boss']['pace']: g['var'] = False; g['start'] = 0   # paced battle: every student runs their own question clock (see bp_*)
# ---- paced battle: each student has their own question stream. They answer, hit the boss at once and get the next question ----
def bp_ev(b, k, ok, dmg, heal):
    # one entry per answer (stone = correct, bandage = wrong); the projector animates every entry once
    ev = b.setdefault('ev', []); ev.append({'n': b['n'], 'who': split_key(k)[1], 'a': avof(k), 'ok': int(bool(ok)), 'dmg': dmg, 'heal': heal}); del ev[:-40]
def bp_q(b, k, n):
    # the n-th question of student k: deterministic, so nothing but the counter has to be stored
    r = random.Random(zlib.crc32(('%s|%s|%s' % (b['sd'], n, k if b['var'] else '')).encode()))
    t_ = r.choice(b.get('pool') or TOPICS) if b['mix'] else b['topic']
    q, a = gen_seeded(t_, b['lv'], r.randint(1, 10 ** 9), D['shape'].get(t_, ''))
    return q, a, t_
def bp_st(b, k):
    now = time.time(); st = b['stu'].get(k)
    if st is None: st = b['stu'][k] = {'n': 0, 'start': now, 'res': None, 'ok': 0, 'bad': 0, 'skip': 0, 'streak': 0, 'dmg': 0}
    elif now >= st['start'] + b['qt'] + 1.2:   # ran out of time without answering: counts as WRONG (boss heals), next question
        if b.get('st') == 'fight':
            q, a, t_ = bp_q(b, k, st['n']); tok = 'bp%s:%s' % (b['sd'], st['n'])
            attempt(k, tok, True, t_, q)
            hl_ = boss_heal(b); b['hp'] = min(b['max'], b['hp'] + hl_); b['hits'] += 1; b['n'] += 1; boss_phase(b)
            b['last'] = {'dmg': 0, 'heal': hl_, 'ok': 0, 'bad': 1, 'n': b['n'], 'who': split_key(k)[1], 'a': avof(k)}; bp_ev(b, k, False, 0, hl_)
            st['skip'] = st.get('skip', 0) + 1; st['streak'] = st.get('streak', 0) + 1
            aj = b.get('adj') or {}; pt = bp_pts(k, None, aj.get('skip', 0) + (aj.get('idle', 0) if st['streak'] % IDLE_AT == 0 else 0))
            st['res'] = {'ok': False, 'dmg': 0, 'heal': hl_, 'ans': a, 'timeout': True, 'streak': st['streak'], 'pt': pt}
        else: st['res'] = {'ok': None}
        st['n'] += 1; st['start'] = now; save()
    return st
def bp_answer(b, c, v, gv):
    k = ckey(c); st = bp_st(b, k)
    if gv is not None and str(gv) != str(st['n']): return   # answer to an old question
    now = time.time(); q, a, t_ = bp_q(b, k, st['n'])
    p = int(500 + 500 * max(0, b['qt'] - (now - st['start'])) / b['qt'])
    ok = correct({'type': 'num', 'q': q, 'ans': a}, v); tok = 'bp%s:%s' % (b['sd'], st['n'])
    attempt(k, tok, True, t_, q)
    if not ok: note_skerr(k, t_, diagnose(q, a, v), q)
    dmg = heal = 0; rush = (not ok) and (now - st['start']) < RUSH_SEC
    st['streak'] = st.get('streak', 0) + 1 if rush else 0; st['ok' if ok else 'bad'] = st.get('ok' if ok else 'bad', 0) + 1
    if rush: st['rush'] = st.get('rush', 0) + 1
    if ok:
        dmg = (BOSS_DMG + (int(round(5 * (max(500, min(1000, p)) - 500) / 500.0)) if SPEED_WEIGHTED else 0)) * boss_mult(b); b['dealt'][k] = b['dealt'].get(k, 0) + dmg; st['dmg'] = st.get('dmg', 0) + dmg
        D['scores'][c] = D['scores'].get(c, 0) + 1; credit(k, tok, True, t_)
    else: heal = boss_heal(b)
    b['hp'] = max(0, min(b['max'], b['hp'] - dmg + heal)); b['hits'] += 1; b['n'] += 1
    b['last'] = {'dmg': dmg, 'heal': heal, 'ok': int(ok), 'bad': int(not ok), 'n': b['n'], 'who': split_key(k)[1], 'a': avof(k)}; bp_ev(b, k, ok, dmg, heal)
    aj = b.get('adj') or {}; pt = 0
    fast = False
    if not ok: pt = bp_pts(k, c, aj.get('bad', 0) + (aj.get('idle', 0) if rush and st['streak'] % IDLE_AT == 0 else 0))
    else:
        fast = (now - st['start']) < FAST_SEC; pt = bp_pts(k, c, aj.get('ok', 0) + (aj.get('fast', 0) if fast else 0))
    st['res'] = {'ok': ok, 'dmg': dmg, 'heal': heal, 'ans': '' if ok else a, 'rush': rush, 'streak': st['streak'], 'pt': pt, 'x2': bool(ok and boss_mult(b) == 2), 'fast': bool(ok and fast and aj.get('fast', 0) > 0)}; st['n'] += 1; st['start'] = now
    if not ok: boss_say(b, 'heal', False)
    boss_phase(b)
    if b['hp'] <= 0: boss_say(b, 'won')
    if b['hp'] <= 0: b['st'] = 'won'; D['tloop'] = False
    save()
def boss_hit(s):
    # called from reveal(): apply this question's damage and healing to the boss
    b = D.get('boss')
    if not (b and b.get('st') == 'fight') or not isq(s): return
    dmg = heal = nok = nbad = 0
    for c, (v, p) in s['by'].items():
        if correct(sfor(s, c), v):
            d_ = (BOSS_DMG + int(round(5 * (max(500, min(1000, p)) - 500) / 500.0))) * boss_mult(b); dmg += d_; nok += 1
            k = ckey(c); b['dealt'][k] = b['dealt'].get(k, 0) + d_
        else: heal += boss_heal(b); nbad += 1
    b['hp'] = max(0, min(b['max'], b['hp'] - dmg + heal)); b['hits'] += 1; b['n'] += 1
    b['last'] = {'dmg': dmg, 'heal': heal, 'ok': nok, 'bad': nbad, 'n': b['n']}
    boss_phase(b)
    if b['hp'] <= 0: boss_say(b, 'won')
    if b['hp'] <= 0: b['st'] = 'won'; D['tloop'] = False
def boss_tick():
    boss_powerup()
    b = D.get('boss')
    if b and b.get('st') == 'fight' and time.time() >= b['end']:
        b['st'] = 'lost'; D['tloop'] = False; boss_say(b, 'lost'); save()
        s = cur()
        if isq(s) and s['start'] and not s['rev']: reveal(s)
def bossview(host=False):
    b = D.get('boss')
    if not b: return None
    ct = None
    if b.get('pace') and (host or b['st'] in ('won', 'lost')):
        ct = sorted(({'n': split_key(k)[1], 'ok': v.get('ok', 0), 'bad': v.get('bad', 0), 'skip': v.get('skip', 0), 'streak': v.get('streak', 0), 'rush': v.get('rush', 0),
                      'd': v.get('dmg', 0), 'idle': v.get('streak', 0) >= IDLE_AT, 'a': avof(k)} for k, v in b['stu'].items()), key=lambda x: (-x['d'], x['skip'], x['n']))
    top = sorted(b['dealt'].items(), key=lambda x: -x[1])[:3]
    return {'st': b['st'], 'name': b['name'], 'hp': b['hp'], 'max': b['max'], 'last': b['last'], 'pace': b.get('pace', False),
            'left': round(max(0, b['end'] - time.time()), 1) if b['st'] == 'fight' else 0,
            'top': [{'n': split_key(k)[1], 'd': v, 'a': avof(k)} for k, v in top], 'ct': ct, 'look': b.get('look') or None, 'dmin': BOSS_DMG, 'dmax': BOSS_DMG + 5,
            'bno': b.get('t0', 0), 'ev': (b.get('ev') or []) if (host and b.get('pace')) else None, 'bid': b.get('sd') if host else None,
            'enr': bool(b['st'] == 'fight' and boss_enraged(b)), 'dbl': round(max(0, b.get('dbl', 0) - time.time()), 1) if b['st'] == 'fight' else 0, 'say': b.get('say')}

def skippers(s):
    # students who were online in this section while the question ran but never submitted: a skip counts as a wrong attempt
    p = D['rp']
    if not s.get('start') or (p.get('show') and p.get('picks')): return set()   # question never ran / cold-call round (only the picked students answer)
    now = time.time(); out = set()
    for c, t in SEEN.items():
        if now - t >= 8 or c not in D['names'] or c in s['by'] or D['secs'].get(c) != D['section']: continue
        k = ckey(c)
        if is_out(k) or (D.get('tmode') and left_team(k)): continue
        out.add(k)
    return out

# ---------------- Operation skills: addition / subtraction / multiplication / division graded one by one ----------------
# Only plain two-number questions on the Basic Operations and Integers tabs are filed under a skill, for example 48 + 17 = ?, (-6) x 4 = ?, 72 / 8 = ?
# (the other tabs mix several skills in one question, so they stay in the topic report only). History starts from the day this feature is installed.
SKILLS = [('add', 'Addition', '+'), ('sub', 'Subtraction', '−'), ('mul', 'Multiplication', '×'), ('div', 'Division', '÷')]
SKILL_KEYS = [s[0] for s in SKILLS]
SKILL_TOPICS = ('Basic Operations', 'Integers')
_SKOP = {'+': 'add', '−': 'sub', '-': 'sub', '×': 'mul', '*': 'mul', 'x': 'mul', '÷': 'div', '/': 'div'}
_SKRE = re.compile(r'^\s*\(?-?\d+\)?\s+([+−\-×÷*/x])\s+\(?-?\d+\)?\s*=\s*\?\s*$')
def skill_of(q, topic=None):
    # 'add' | 'sub' | 'mul' | 'div', or None when the question is not a plain two-number operation
    if topic is not None and topic not in SKILL_TOPICS: return None
    m = _SKRE.match(str(q or '')); return _SKOP.get(m.group(1)) if m else None
def note_skerr(key, topic, tag, q):
    sk_ = skill_of(q, topic)
    if tag and sk_: e = D['skerr'].setdefault(key, {}).setdefault(sk_, {}); e[tag] = e.get(tag, 0) + 1
def _rq(p, k):
    # the question that student k answers in the current cold-call round (the picked student, or the classmate who took a pass)
    for q in p.get('picks', []):
        if pkey(q) == k: return q.get('q', cur()['q'])
    return None

ERR_HINT = {
    'sign': 'Your digits are right but the sign is opposite. Re-check the rules for positive and negative numbers.',
    'slip': 'So close, you are off by just 1. Re-check your last step of arithmetic.',
    'place': 'The digits are right but the size is off by a power of 10. Re-check place value, zeros or the decimal point.',
    'operation': 'Your answer matches a different operation on these numbers. Re-read what the question asks and which operation fits.',
    'format': 'Please type your answer as a number (for example 12, -5, 3/4 or 0.5).',
    'other': 'Compare each step of the worked solution with your own working to find where it changed.'}
ERR_LABEL = {'sign': 'Sign errors', 'slip': 'Off-by-one slips', 'place': 'Place-value errors', 'operation': 'Wrong operation', 'format': 'Not a number', 'other': 'Other'}
def diagnose(q, ans, given):
    # class of a WRONG numeric answer (None if it is actually right or cannot be judged). A hint tag, not a verdict.
    a, g = numval(ans), numval(given)
    if a is None: return None
    if g is None: return 'format'
    if abs(g - a) <= 1e-6 * max(1, abs(a)): return None
    if a != 0 and abs(g + a) < 1e-6 * max(1, abs(a)): return 'sign'
    if abs(abs(g - a) - 1) < 1e-9: return 'slip'
    if a != 0 and g != 0 and any(abs(g / a - f) < 1e-9 for f in (10, 100, 0.1, 0.01)): return 'place'
    nums = [float(x) for x in re.findall(r'(?<![\d.])\d+(?:\.\d+)?', str(q))][:4]
    for i in range(len(nums)):
        for j in range(len(nums)):
            if i == j: continue
            x, y = nums[i], nums[j]
            alt = {x + y, x * y, abs(x - y)} | ({x / y} if y else set())
            if any(abs(g - v) < 1e-6 for v in alt) and abs(g - a) > 1e-6: return 'operation'
    return 'other'
def note_err(key, topic, tag, q=None):
    if not tag or not topic: return
    if q is not None: note_skerr(key, topic, tag, q)
    sec = split_key(key)[0]; e = D['err'].setdefault(sec, {}).setdefault(topic, {}); e[tag] = e.get(tag, 0) + 1
def track(sec, outcomes):
    # keep the last TRACK_N right/wrong outcomes of the class; when the window is full and outside the 70-90% band tell the host once
    if not outcomes: return
    r = D['recent'].setdefault(sec, []); r.extend(1 if o else 0 for o in outcomes); del r[:-TRACK_N]
    if len(r) < TRACK_N: return
    acc = sum(r) / float(len(r))
    msg = ('📈 Class accuracy is %d%% over the last %d answers: above the %d-%d%% learning band. Consider a higher level or harder topic.' if acc > TARGET_HI else
           '📉 Class accuracy is %d%% over the last %d answers: below the %d-%d%% learning band. Consider an easier level or re-teaching the worked solutions.' if acc < TARGET_LO else '')
    if msg:
        D['notice'] = msg % (round(acc * 100), len(r), round(TARGET_LO * 100), round(TARGET_HI * 100)); D['noticet'] = time.time(); r.clear()

def reveal(s):
    if s['rev']: return
    s['rev'] = True
    if isq(s):
        for k_ in skippers(s): attempt(k_, qtok(s), True, None, sfor(s, k_)['q'])
    outs = []
    for c, (v, p) in s['by'].items():
        sx_ = sfor(s, c); attempt(ckey(c), qtok(s), True, None, sx_['q'])
        good = correct(sx_, v); outs.append(good)
        if not good and s.get('type') == 'num': note_err(ckey(c), s.get('topic'), diagnose(sx_['q'], sx_['ans'], v), sx_['q'])
        if good: D['scores'][c] = D['scores'].get(c, 0) + p; credit(ckey(c), qtok(s), True)
    if isq(s) and outs: track(D['section'], outs)
    boss_hit(s)
    record_round()

def score_of(c): return D['scores'].get(c, 0)

def avof(key):
    # the student's chosen avatar (emoji) from the saved profile, '' when they use the initials
    a = (D.get('prof', {}).get(key) or {}).get('av', '')
    return a if isinstance(a, str) and 0 < len(a) <= 12 else ''

def top():
    r = sorted(((c, score_of(c)) for c in D['scores']), key=lambda x: -x[1])[:8]
    return [{'n': D['names'].get(c, '?'), 's': int(v), 'a': avof(ckey(c))} for c, v in r]

def rleft(p):
    if p.get('tstart'):
        el = time.time() - p['tstart']
        if el < 0: return float(p['tdur']), False   # decision phase: timer not counting yet
        return max(0.0, p['tdur'] - el), True
    if p.get('tfz') is not None: return p['tfz'], False
    return p['tdur'], False

def rfreeze():
    p = D['rp']
    if p.get('tstart'): p['tfz'] = rleft(p)[0]; p['tstart'] = 0

def finish_round():
    # check every submitted answer against the slide's answer, reveal it, close the round
    p = D['rp']
    if p.get('show') and p.get('picks') and not p.get('fin'):
        sl = cur()
        for q in p['picks']:
            sx = pkq(sl, q)
            if str(q.get('ans', '')).strip() and not q.get('mark') and sx.get('ans'):
                q['mark'] = 'ok' if correct(sx, str(q['ans']).strip()) else 'no'
                if q['mark'] == 'no' and sl.get('type') == 'num': note_err(skey(q['sec'], q['name']), p.get('topic') or sl.get('topic'), diagnose(sx['q'], sx['ans'], q['ans']), sx['q'])
                track(q['sec'], [q['mark'] == 'ok'])
        reveal(sl)
        p['fin'] = time.time()
        save()

LOOP_PAUSE = 5   # seconds the answers stay on screen before the next random question appears

def auto_loop():
    # team auto-loop: everyone gets their own random question -> timer -> reveal -> short pause -> next question
    if not (boss_live() or (D.get('tloop') and D['tmode'] and D['teams'].get(D['section']))): return
    if boss_live() and D['boss'].get('pace'): return   # paced battle: no shared question clock
    s = cur()
    if s.get('type') != 'num' or not s.get('auto'): return
    now = time.time()
    if not s['rev']:
        if not s['start']:
            if not s['time']: s['time'] = int(D['rtime']) or 30
            D['rp']['show'] = False; s['start'] = now; save()
        elif now - s['start'] >= s['time'] + 1.2:
            reveal(s); s['revt'] = now; save()
    else:
        s.setdefault('revt', now)
        if now - s['revt'] >= LOOP_PAUSE:
            t_ = s['time']; g = make(random.choice(D['boss'].get('pool') or TOPICS) if boss_live() and D['boss'].get('mix') else pick_topic(s['topic'], s['topic']) if (mixpool() and not boss_live()) else s['topic'], 'num', D.get('level', 1)); g['time'] = t_; g['start'] = now
            if boss_live() and not D['boss'].get('var'): g['var'] = False
            D['rp']['show'] = False; save()

def auto_finish():
    boss_tick()
    auto_loop()
    # don't depend on the host's browser: end the round on the server as soon as the timer runs out
    p = D['rp']
    if p.get('show') and p.get('picks') and p.get('tdur') and p.get('tstart') and not p.get('fin') and time.time() - p['tstart'] >= p['tdur'] + 1.2:
        finish_round()

def rpv():
    p = dict(D['rp']); l, run = rleft(D['rp']); p['rleft'] = round(l, 2); p['run'] = run
    now = time.time(); live = {(D['secs'].get(c), D['names'].get(c)) for c, t in SEEN.items() if now - t < 8}
    p['picks'] = [dict(q, on=(q['sec'], q['name']) in live, got=okcount(skey(q['sec'], q['name'])), out=is_out(skey(q['sec'], q['name']))) for q in D['rp'].get('picks', [])]
    p['goal'] = D['goal']; p['dec'] = round(max(0.0, p['tstart'] - now), 2) if p.get('tstart') and p.get('tdur') else 0
    return p

def ridx(cid):
    # None = round not active (everyone may answer); -1 = viewer; >=0 = index of the selected student
    p = D['rp']
    if not (p.get('show') and p.get('picks')): return None
    k = (D['secs'].get(cid), D['names'].get(cid))
    for i, q in enumerate(p['picks']):
        if (q['sec'], q['name']) == k: return i
    return -1

def rtimer_ok():
    p = D['rp']
    if not p.get('tdur'): return True
    if p.get('tstart'): return 0 <= time.time() - p['tstart'] < p['tdur'] + 1   # not before the timer really starts
    return False

def pkq(s, q):
    # the question/answer that belongs to ONE selected student (falls back to the slide's own)
    return dict(s, q=q.get('q', s['q']), ans=q.get('qa', s.get('ans', '')))

def rrec(ri, s, v):
    if ri is None or ri < 0: return
    p = D['rp']; q = p['picks'][ri]; q['ans'] = v[:80]
    if p.get('tdur') and not p.get('fin'): return  # timed round: marks appear only when time is up ('rfinish')
    sx = pkq(s, q)
    if (isq(s) or s['type'] == 'pick') and sx.get('ans'): q['mark'] = 'ok' if correct(sx, v) else 'no'
    if all(x['mark'] for x in p['picks']): rfreeze()

# ---------------- Team mode ----------------
# A team's score = sum of its members' correct answers (1 point each, same count as the goal system, noisy penalties included)
# + whatever the teacher added / deducted for the whole team.
TNAMES = [('🔥', 'Fire'), ('🦈', 'Sharks'), ('🐯', 'Tigers'), ('🦅', 'Eagles'), ('🐉', 'Dragons'), ('🐬', 'Dolphins'), ('🦁', 'Lions'), ('🐺', 'Wolves'), ('⚡', 'Thunder'), ('🌟', 'Stars'), ('🐼', 'Pandas'), ('🦊', 'Foxes')]
TB = {}   # short-lived cache of team boards (cleared after every POST)

def team_of(sec, name):
    for t in D['teams'].get(sec, []):
        if name in t['m']: return t

def round_set(sec):
    # students of this section who got the CURRENT question / cold-call round right
    out = set(); p = D['rp']; s = cur()
    if p.get('show') and p.get('picks'):
        for q in p['picks']:
            if q.get('mark') == 'ok' and split_key(pkey(q))[0] == sec: out.add(split_key(pkey(q))[1])
    elif isq(s) and s['rev']:
        for c, (v, pt) in s['by'].items():
            if D['secs'].get(c) == sec and correct(sfor(s, c), v): out.add(D['names'].get(c, ''))
    return out

def tboard(sec):
    c = TB.get(sec)
    if c and time.time() - c[0] < 0.8: return c[1]
    rs = round_set(sec); L = []
    for t in D['teams'].get(sec, []):
        raw = sum(okcount(skey(sec, n)) for n in t['m']); adj = D['tadj'].get(skey(sec, t['id']), 0)
        L.append({'id': t['id'], 'name': t['name'], 'm': t['m'], 'mc': {n: okcount(skey(sec, n)) for n in t['m']}, 'raw': raw, 'adj': adj, 'tot': max(0, raw + adj), 'done': D.get('tgoal', 0) > 0 and max(0, raw + adj) >= D['tgoal'], 'rnd': sum(1 for n in t['m'] if n in rs)})
    L.sort(key=lambda x: (-x['tot'], x['name']))
    for x in L: x['rank'] = 1 + sum(1 for y in L if y['tot'] > x['tot'])
    TB[sec] = (time.time(), L); return L

def tclean(sec):
    # forget team adjustments / history of one section (teams were rebuilt, removed or reset)
    pre = sec + '|'
    D['tadj'] = {k: v for k, v in D['tadj'].items() if not k.startswith(pre)}
    D['tlog'] = [e for e in D['tlog'] if not e[0].startswith(pre)]
    for x in D['thist']: x['s'].pop(sec, None)
    D['thist'] = [x for x in D['thist'] if x['s']]
    D['tleft'].pop(sec, None)

def record_round():
    # store each team's points for the round that just ended (same round is updated, never duplicated)
    if not D['tmode'] or not D['teams']: return
    p = D['rp']; s = cur()
    if p.get('show') and p.get('picks'): k = 'r%s' % p.get('n')
    elif isq(s) and s['rev']: k = 'q%s:%s' % (s['id'], s.get('gv', 0))
    else: return
    ent = {'k': k, 't': time.time(), 's': {}}
    for sec, L in D['teams'].items():
        rs = round_set(sec); ent['s'][sec] = {t['id']: sum(1 for n in t['m'] if n in rs) for t in L}
    H = D['thist']; i = next((j for j, x in enumerate(H) if x['k'] == k), None)
    if i is None: H.append(ent); del H[:-40]
    else: H[i] = ent

def podium_data():
    sec = D['section']; b = D.get('boss')
    if b and b.get('st') in ('won', 'lost') and b.get('dealt'):
        rows = [{'n': split_key(k)[1], 'v': v, 'u': ' dmg'} for k, v in sorted(b['dealt'].items(), key=lambda x: -x[1])[:3]]
        return {'t': '🎉 Boss defeated!' if b['st'] == 'won' else '💀 The boss survived', 's': 'Top hitters', 'rows': rows}
    if D.get('tmode') and (D['teams'].get(sec) or D['tleft'].get(sec)):
        L = [{'n': t['name'], 'v': t['tot'], 'u': ' pts'} for t in tboard(sec)] + [{'n': t['name'], 'v': t['tot'], 'u': ' pts'} for t in D['tleft'].get(sec, [])]
        L.sort(key=lambda x: -x['v']); return {'t': '🏆 Top teams', 's': sec, 'rows': [x for x in L if x['v'] > 0][:3]}
    L = sorted(((n, okcount(skey(sec, n))) for n in ROSTER[sec]), key=lambda x: (-x[1], x[0]))
    return {'t': '🏆 Top students', 's': sec, 'rows': [{'n': n, 'v': v, 'u': ' correct'} for n, v in L if v > 0][:3]}

def state(host, cid=''):
    auto_finish()
    s0 = cur(); s = {k: v for k, v in s0.items() if k != 'by'}
    if isq(s0) and not s0['rev'] and not host: s.update(votes={}, words={}, ans='')
    if not host: s['answers'] = []
    if s0['type'] == 'pick' and not host: s['ans'] = ''
    s['turnName'] = D['names'].get(s0.get('turn', ''), '')
    if s0.get('var') and s0['type'] == 'num':
        if not host:
            s.pop('sd', None)
            if cid: q_, a_ = vq(s0, cid); s['q'] = q_; s['ans'] = a_ if s0['rev'] else ''
        elif s0['rev']:
            s['nok'] = sum(1 for c_, (v_, p_) in s0['by'].items() if correct(sfor(s0, c_), v_)); s['nby'] = len(s0['by'])
    n = len(s0['by']) if isq(s0) else len(voters.get(s0['id'], {}))
    sc = D['scores']; me = None
    if cid in D['names']: me = {'s': int(score_of(cid)), 'r': 1 + sum(1 for c_ in sc if score_of(c_) > score_of(cid))}
    ok = pts = None
    if s0['rev'] and cid in s0['by']:
        ok = correct(sfor(s0, cid), s0['by'][cid][0]); pts = s0['by'][cid][1] if ok else 0
    fb = None
    if s0['rev'] and cid in s0['by'] and s0['type'] == 'num' and not host:
        sx_ = sfor(s0, cid); tg_ = None if ok else diagnose(sx_['q'], sx_['ans'], s0['by'][cid][0])
        fb = {'steps': explain(sx_['q'], sx_['ans']), 'hint': ERR_HINT.get(tg_, '') if tg_ else ''}
    r = {'cur': D['cur'], 'n': len(D['slides']), 'fb': fb, 'open': canvote(s0), 'gate': D['open'],
         'wait': bool(s0['time'] and not s0['start'] and not s0['rev']), 'run': bool(s0['start'] and not s0['rev']),
         'left': left(s0), 'slide': s, 'respondents': n, 'board': D['board'], 'top': top(), 'me': me, 'ok': ok, 'pts': pts, 'yours': bool(cid) and s0.get('turn') == cid}
    mk = ckey(cid) if cid in D['names'] else ''
    r['mygoal'] = {'n': 0 if classmode() else D['goal'], 'got': okcount(mk) if mk else 0, 'out': bool(mk) and is_out(mk)}
    r['mylife'] = life(mk) if mk else None; r['myatt'] = life_att(mk) if mk else None; r['topics'] = TOPICS; r['myhp'], r['myhps'] = hp_of(mk) if mk else (0, 0)
    lt_ = left_team(mk) if mk and D.get('tmode') else None
    if lt_: r['mygoal'].update(out=True, got=lt_['tot'], team=lt_['name'])   # the whole team leaves together, showing the team score
    ri = ridx(cid); r['sess'] = SESSION
    r['myprof'] = D['prof'].get(ckey(cid)) if cid in D['names'] else None
    r['mynoisy'] = D['noisy'].get(ckey(cid), 0) if cid in D['names'] else 0
    r['taken'] = {}
    for (sec_, nm_), c_ in CLAIM.items():
        if c_ != cid and time.time() - SEEN.get(c_, 0) < CLAIM_TTL: r['taken'].setdefault(sec_, []).append(nm_)
    r['role'] = 'all' if ri is None else 'player' if ri >= 0 else 'viewer'
    r['picked'] = [q['name'] for q in D['rp']['picks']] if ri is not None else []
    r['myans'] = D['rp']['picks'][ri].get('ans', '') if ri is not None and ri >= 0 else ''
    r['mymark'] = D['rp']['picks'][ri].get('mark') if ri is not None and ri >= 0 else None
    r['myq'] = D['rp']['picks'][ri].get('q') if ri is not None and ri >= 0 else None
    r['multiq'] = ri is not None and any(x.get('q') for x in D['rp']['picks'])
    if ri == -1 and cid in D['names']:
        hi_ = hidx(cid)
        if hi_ is not None:   # a classmate / friend who was asked to answer for the selected student
            pq_ = D['rp']['picks'][hi_]; r['role'] = 'helper'
            r.update(hq=pq_.get('q') or s0['q'], hfrom=pq_['name'], hans=pq_.get('ans', ''), hmark=pq_.get('mark'), hk=pq_['lf']['k'])
    if r['role'] == 'player':
        q_ = D['rp']['picks'][ri]; can_ = lf_can(q_)
        r['lf'] = {'left': lf_left(mk), 'can': can_, 'opts': lf_opts(ri) if can_ else [], 'used': q_.get('lf')}
    r['tmode'] = D['tmode']; r['tloop'] = D.get('tloop', False)
    if D['tmode'] and cid in D['names']:
        sec_ = D['secs'].get(cid, ''); me_ = team_of(sec_, D['names'][cid])
        if me_:
            b_ = tboard(sec_); x_ = next((y for y in b_ if y['id'] == me_['id']), None)
            if x_: r['myteam'] = dict(x_, n=len(b_))
    r['idle'] = (not host) and not D.get('shown')
    if r['idle']:   # nothing started yet: hide the preset question completely
        s['q'] = ''; s['opts'] = []; s['ans'] = ''; r.update(open=False, wait=False, left=None, board=False, top=[])
    if r['role'] == 'viewer':
        r['open'] = False
        if mk and mk in D.get('lastq', {}): r['review'] = D['lastq'][mk]   # not picked this round: show the last question they answered
    elif r['role'] in ('player', 'helper'):
        p = D['rp']; r['open'] = r['open'] and rtimer_ok()
        r['wait'] = r['wait'] or bool(p['tdur'] and ((not p.get('tstart') and p.get('tfz') is None) or (p.get('tstart') and time.time() < p['tstart'])))
    if host:
        r['slides'] = [{'id': x['id'], 'type': x['type'], 'q': x['q'], 'topic': x['topic'], 'auto': x.get('auto', False)} for x in D['slides']]
        r['topics'] = TOPICS
        r['allq'] = []
        if s0.get('var') and s0['type'] == 'num':
            # EVERY student of the section (joined or not) with the question they get
            _best = {}
            for c_, nm_ in D['names'].items():
                if D['secs'].get(c_) == D['section'] and (nm_ not in _best or SEEN.get(c_, 0) > SEEN.get(_best[nm_], 0)): _best[nm_] = c_
            for nm_ in ROSTER[D['section']]:
                if is_out(skey(D['section'], nm_)): continue
                q_, a_ = vq(s0, skey(D['section'], nm_)); t_ = team_of(D['section'], nm_) if D['tmode'] else None
                c_ = _best.get(nm_); by_ = s0['by'].get(c_) if c_ else None
                r['allq'].append({'n': nm_, 't': t_['name'] if t_ else '', 'q': q_, 'a': a_ if s0['rev'] else '',
                                  'v': by_[0] if by_ else '', 'ok': (correct(dict(s0, q=q_, ans=a_), by_[0]) if by_ and s0['rev'] else None)})
            r['allq'].sort(key=lambda x: (x['t'] == '', x['t'], x['n'].lower()))
        ks = secs(); done = {tuple(x) for x in D['picked']}; _lv = live_set() if D.get('onlyon') else None
        r['roster'] = {'sections': list(ROSTER), 'section': ks[0], 'level': D.get('level', 1), 'lang': D.get('lang', 'en'), 'shapes': D.get('shape', {}), 'rp': rpv(), 'rtime': D['rtime'], 'rcount': D['rcount'], 'names': [n for k in ks for n in ROSTER[k]],
                       'left': sum(1 for k in ks for n in ROSTER[k] if (k, n) not in done and not is_out(skey(k, n)) and (_lv is None or (k, n) in _lv)), 'total': sum(1 for k in ks for n in ROSTER[k] if not is_out(skey(k, n)) and (_lv is None or (k, n) in _lv)), 'goal': D['goal'], 'onlyon': bool(D.get('onlyon'))}
        r['online'] = sorted(({'c': c, 'n': D['names'].get(c, '?'), 's': D['secs'].get(c, '')} for c, t in SEEN.items() if time.time() - t < 8), key=lambda x: x['n'].lower())
        _live = {(o['s'], o['n']) for o in r['online']}
        r['bysec'] = [{'sec': k, 'total': len(ROSTER[k]), 'on': [n for n in ROSTER[k] if (k, n) in _live],
                       'off': [n for n in ROSTER[k] if (k, n) not in _live]} for k in ROSTER]
        _known = {(k, n) for k in ROSTER for n in ROSTER[k]}
        for b in r['bysec']:
            b['cnt'] = {n: okcount(skey(b['sec'], n)) for n in b['on'] + b['off']}
            b['out'] = [n for n in b['cnt'] if is_out(skey(b['sec'], n))]
        check_finished()
        r['fin'] = [{'n': split_key(k)[1], 's': split_key(k)[0], 'got': okcount(k), 'back': k in D['back']} for k in all_reached()]
        a = D.get('ann') or {}
        r['ann'] = dict(a, age=round(time.time() - a.get('t', 0), 1)) if a else None
        r['goal'] = 0 if classmode() else D['goal']; r['notice'] = D['notice'] if time.time() - D.get('noticet', 0) < 6 else ''
        r['unlisted'] = [o['n'] + (' (' + o['s'] + ')' if o['s'] else '') for o in r['online'] if (o['s'], o['n']) not in _known]
        r['join'] = 'http://%s:%d' % (IPS[0], PORT)
        r['noisy'] = D['noisy']; r['nlast'] = split_key(nkey(D['nlog'][-1]))[1] if D['nlog'] else ''
        r['tboard'] = tboard(D['section']); r['tlast'] = D['tlog'][-1][2] if D['tlog'] else ''
        r['tgoal'] = D.get('tgoal', 0); r['tleft'] = D['tleft'].get(D['section'], []); r['podium'] = podium_data(); r['mix'] = mixpool()
        if r['tgoal'] > 0:
            _pre = D['section'] + '|'; _dn = {skey(D['section'], t['id']) for t in r['tboard'] if t['done']}
            _new = [t for t in r['tboard'] if t['done'] and skey(D['section'], t['id']) not in D['tann']]
            _keep = [k for k in D['tann'] if not k.startswith(_pre) or k in _dn]   # a team that drops below the goal can be announced again
            if _new or len(_keep) != len(D['tann']):
                D['tann'] = _keep + [skey(D['section'], t['id']) for t in _new]
                if _new: D['notice'] = '🎉 Reached the goal, can leave: ' + ', '.join(t['name'] for t in _new); D['noticet'] = time.time(); r['notice'] = D['notice']
                save()
        _h = [x['s'][D['section']] for x in D['thist'] if D['section'] in x['s']]
        r['thist'] = [{'n': i + 1, 'v': v} for i, v in enumerate(_h)]
    r['boss'] = bossview(host); r['mode'] = D.get('mode', 'individual')
    b_ = D.get('boss')
    if b_ and b_.get('st') == 'fight' and b_.get('pace'):
        if host: s['q'] = 'Battle! Every student answers at their own pace'; r.update(wait=False, run=False, left=None, open=False)
        elif cid in D['names'] and D['shown']:
            k_ = ckey(cid); st_ = bp_st(b_, k_); q_, a_, t_ = bp_q(b_, k_, st_['n'])
            s.update(q=q_, ans='', gv=st_['n'], var=False, rev=False)
            r.update(open=bool(D['open']) and not is_out(k_), wait=False, run=True, ok=None, pts=None, bres=st_['res'],
                     left=round(max(0, b_['qt'] - (time.time() - st_['start'])), 2))
    return r

from fractions import Fraction as Fr
NAMES = ['Ana', 'Ben', 'Carlo', 'Dina', 'Eli', 'Maria', 'Jose', 'Liza']
def fs(f): return str(f.numerator) if f.denominator == 1 else '%d/%d' % (f.numerator, f.denominator)
def pn(n): return '(%d)' % n if n < 0 else str(n)
def nz(a, b):
    n = 0
    while n == 0: n = random.randint(a, b)
    return n

SHAPES = ['', '11', '12', '13', '22', '23', '33']
SHAPE_TOPICS = ('Basic Operations', 'Integers', 'Word Problem')   # tabs that honour the digit option
def dnum(d): return random.randint(2, 9) if d == 1 else random.randint(10 ** (d - 1), 10 ** d - 1)
def gen_shape(topic, sh):
    if topic == 'Word Problem' and D.get('lang') == 'tl': return gen_shape_tl(sh)
    ri = random.randint; R = random.choice; A, B = int(sh[0]), int(sh[1])
    if topic == 'Word Problem':
        N = R(NAMES); t = R([0, 3, 6, 7]); a, b = dnum(A), dnum(B)
        if R([0, 1]): a, b = b, a
        if t == 0:
            it = R(['notebooks', 'pens', 'rulers', 'bottles of juice'])
            return '%s buys %d %s at ₱%d each. How much does %s pay in all?' % (N, b, it, a, N), str(a * b)
        if t == 3: return 'A jeepney travels at %d km/h for %d hours. How far does it travel (in km)?' % (a, b), str(a * b)
        if t == 6: return 'A rectangular garden is %d m long and %d m wide. What is its area in square meters?' % (a, b), str(a * b)
        return '%s has %d stickers and gets %d more. How many stickers does %s have now?' % (N, a, b, N), str(a + b)
    sg = (lambda: R([-1, 1])) if topic == 'Integers' else (lambda: 1)
    op = R(['+', '−', '×', '÷'])
    if op == '÷':
        hi, lo = max(A, B), min(A, B)
        lob = 2 if lo == 1 else 10 ** (lo - 1); hib = min(10 ** lo - 1, (10 ** hi - 1) // 2)
        b = ri(lob, max(lob, hib)); qmax = max(2, (10 ** hi - 1) // b)
        qlo = 2 if hi == 1 else max(2, -(-10 ** (hi - 1) // b)); q = ri(min(qlo, qmax), qmax)
        b2, q2 = b * sg(), q * sg()
        return '%d ÷ %s = ?' % (b2 * q2, pn(b2)), str(q2)
    if op == '−' and topic != 'Integers':
        x, y = dnum(max(A, B)), dnum(min(A, B))
        while x == y: y = dnum(min(A, B))
        if x < y: x, y = y, x
        return '%d − %d = ?' % (x, y), str(x - y)
    a, b = dnum(A) * sg(), dnum(B) * sg()
    if R([0, 1]): a, b = b, a
    if op == '+': return '%s + %s = ?' % (pn(a), pn(b)), str(a + b)
    if op == '−': return '%s − %s = ?' % (pn(a), pn(b)), str(a - b)
    return '%s × %s = ?' % (pn(a), pn(b)), str(a * b)

def lvparts(lv):
    # level code 1..8 = grade band x difficulty. 1-4 = Grade 7-8, 5-8 = Grade 9-10.
    # Within a band: 1 = easy, 2 = average, 3 = difficult, 4 = mixed (a random one of the three for every question).
    # (old saved slides used 1 / 2, which still read as "Grade 7-8 easy / average")
    try: lv = max(1, min(8, int(lv)))
    except Exception: lv = 2
    df = (lv - 1) % 4 + 1
    if df == 4: df = random.choice([1, 2, 3])
    return lv > 4, df

def lvclean(v):
    try: return max(1, min(8, int(float(v))))
    except Exception: return 2

def gen(topic, lv, sh=''):
    if topic in EXTRA_TOPICS: return gen_extra(topic, lv)
    if sh in SHAPES and sh and topic in SHAPE_TOPICS: return gen_shape(topic, sh)
    h, df = lvparts(lv); ri = random.randint; R = random.choice; N = R(NAMES)
    if topic == 'Basic Operations':
        # ONE operation only
        k = 2 if h else 1
        if df == 1:
            aR, bR, mR, nR, cR, sR, rR, cbR, PS, nM = (5, 25), (2, 9), (2, 9), (2, 9), (2, 9), (2, 10), (2, 10), (2, 4), [10, 50], (2, 10)
            pool = [0, 1, 2, 3] + ([4, 6] if h else [])
        elif df == 2:
            aR, bR, mR, nR, cR, sR, rR, cbR, PS, nM = (5, 50 * k), (2, 12 * k), (2, 12 * k), (2, 12), (2, 12), (2, 12 * k), (2, 15), (2, 6), [10, 20, 25, 40, 50, 75], (2, 30)
            pool = list(range(8)) if h else list(range(5))
        else:
            aR, bR, mR, nR, cR, sR, rR, cbR, PS, nM = (50, 400 * k), (10, 40 * k), (11, 30 * k), (11, 25), (11, 25), (11, 25 * k), (12, 30), (3, 9), [5, 15, 35, 45, 60, 80], (5, 40)
            pool = list(range(8))
        t = R(pool)
        a, b = ri(*aR), ri(*bR)
        if t == 0: return '%d + %d = ?' % (a, b), str(a + b)
        if t == 1: return '%d − %d = ?' % (a + b, b), str(a)
        if t == 2: m, n2 = ri(*mR), ri(*nR); return '%d × %d = ?' % (m, n2), str(m * n2)
        if t == 3: c = ri(*cR); return '%d ÷ %d = ?' % (c * b, b), str(c)
        if t == 4: m = ri(*sR); return '%d^2 = ?' % m, str(m * m)
        if t == 5: x = ri(*rR); return 'sqrt(%d) = ?' % (x * x), str(x)
        if t == 6:
            p = R(PS); n = ri(*nM) * 20
            return 'What is %d%% of %d?' % (p, n), str(p * n // 100)
        x = ri(*cbR); return '%d^3 = ?' % x, str(x ** 3)
    if topic == 'Integers':
        if df == 1: m, cm, pool = (12 if h else 9), 5, ([0, 1, 2, 3] if h else [0, 1])
        elif df == 2: m, cm, pool = (20 if h else 12), 9, ([0, 1, 2, 3, 5, 6] if h else [0, 1, 2, 3])
        else: m, cm, pool = (30 if h else 20), 12, ([2, 3, 4, 5, 6, 7] if h else [0, 1, 2, 3, 4])
        a, b, c = nz(-m, m), nz(-m, m), nz(-cm, cm)
        t = R(pool)
        if t == 0: return '%s + %s = ?' % (pn(a), pn(b)), str(a + b)
        if t == 1: return '%s − %s = ?' % (pn(a), pn(b)), str(a - b)
        if t == 2: return '%s × %s = ?' % (pn(a), pn(c)), str(a * c)
        if t == 3: return '%d ÷ %s = ?' % (a * c, pn(c)), str(a)
        if t == 4: return '%s + %s − %s = ?' % (pn(a), pn(b), pn(c)), str(a + b - c)
        if t == 5: return 'Evaluate 3x − 5 when x = %s' % pn(c), str(3 * c - 5)
        if t == 7: return 'Evaluate x^2 − 3x when x = %s' % pn(c), str(c * c - 3 * c)
        return '|%d − %d| = ?' % (a, b), str(abs(a - b))
    if topic == 'Fractions':
        DS = [2, 3, 4, 5, 6] if df == 1 else [2, 3, 4, 5, 6, 8, 10, 12] if df == 2 else [3, 4, 5, 6, 8, 9, 10, 12, 15]
        def rf():
            d = R(DS); return ri(1, d - 1), d
        (a, b), (c, d) = rf(), rf(); x, y = Fr(a, b), Fr(c, d)
        if df == 1: pool = [0, 1, 2] if h else [0, 1]
        elif df == 2: pool = [2, 3, 4, 5] if h else [0, 1, 2, 3]
        else: pool = [3, 4, 5, 6] if h else [1, 2, 3, 4, 6]
        t = R(pool)
        if t == 0: return '%d/%d + %d/%d = ?' % (a, b, c, d), fs(x + y)
        if t == 1:
            if x < y: a, b, c, d, x, y = c, d, a, b, y, x
            return '%d/%d − %d/%d = ?' % (a, b, c, d), fs(x - y)
        if t == 2: return '%d/%d × %d/%d = ?' % (a, b, c, d), fs(x * y)
        if t == 3: return '%d/%d ÷ %d/%d = ?' % (a, b, c, d), fs(x / y)
        if t == 4:
            n = (ri(2, 6) if df == 1 else ri(6, 30) if df == 3 else ri(2, 12)) * b
            return 'What is %d/%d of %d?' % (a, b, n), fs(x * n)
        if t == 6:
            q_ = ri(2, 9); fr = Fr(ri(1, q_ - 1), q_); f_ = ri(2, 9)
            return 'Simplify %d/%d.' % (fr.numerator * f_, fr.denominator * f_), fs(fr)
        e = R([2, 4, 5] if df == 1 else [8, 16, 20, 25, 40] if df == 3 else [2, 4, 5, 8, 10, 20]); f = ri(1, e - 1); return 'Write %d/%d as a decimal.' % (f, e), '%g' % (f / e)
    # Word Problem (English or Taglish, chosen by the teacher)
    tl = D.get('lang') == 'tl'
    if df == 1: pool = [0, 2, 3, 7, 14]
    elif df == 2: pool = (list(range(8)) if h else list(range(5))) + [12, 13, 14]
    else: pool = [1, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14]
    t = R(pool); easy, hard = df == 1, df == 3
    ITEMS = ['notebook', 'ballpen', 'ruler', 'bote ng juice'] if tl else ['notebooks', 'pens', 'rulers', 'bottles of juice']
    def out(en, tg, ans, **kw): return (tg if tl else en).format(N=N, **kw), str(ans)
    if t == 0:
        it = R(ITEMS); p, n = (ri(5, 25), ri(2, 6)) if easy else (ri(8, 60), ri(3, 12))
        return out('{N} buys {n} {it} at ₱{p} each. How much does {N} pay in all?', 'Bumili si {N} ng {n} {it} na ₱{p} bawat isa. Magkano lahat ang kanyang binayaran?', n * p, n=n, it=it, p=p)
    if t == 1:
        b = R([3, 4, 5, 6, 8, 9] if hard else [3, 4, 5, 6, 8]); a = ri(1, b - 1); tot = b * (ri(8, 30) if hard else ri(3, 12))
        return out('{N} has {tot} marbles. {a}/{b} of them are red. How many marbles are red?', 'May {tot} na holen si {N}. {a}/{b} nito ay pula. Ilang holen ang pula?', tot * a // b, tot=tot, a=a, b=b)
    if t == 2:
        cost = ri(21, 99); pay = (cost // 100 + 1) * 100
        return out('{N} buys a snack for ₱{cost} and pays ₱{pay}. How much is the change?', 'Bumili si {N} ng meryenda na ₱{cost} at nagbayad ng ₱{pay}. Magkano ang sukli?', pay - cost, cost=cost, pay=pay)
    if t == 3:
        v, hr = (ri(20, 50), ri(2, 4)) if easy else (ri(30, 60), ri(2, 5))
        return out('A jeepney travels at {v} km/h for {hr} hours. How far does it travel (in km)?', 'Ang jeep ay bumibiyahe nang {v} km/h sa loob ng {hr} oras. Gaano kalayo ang nalakbay nito (sa km)?', v * hr, v=v, hr=hr)
    if t == 4:
        s0, ch = (-ri(5, 25), ri(15, 40)) if hard else (-ri(2, 12), ri(5, 20))
        return out('The temperature was {s0} degrees in the morning, then rose by {ch} degrees. What is the temperature now?', 'Ang temperatura ay {s0} degrees kaninang umaga, tapos tumaas ng {ch} degrees. Ano na ang temperatura ngayon?', s0 + ch, s0=s0, ch=ch)
    if t == 5:
        p, d = (ri(5, 50) * 100, R([5, 15, 30, 35, 40, 60])) if hard else (ri(2, 20) * 100, R([10, 20, 25, 50]))
        return out('A bag costs ₱{p} and is on sale at {d}% off. How much is the discount (in pesos)?', 'Ang bag ay nagkakahalaga ng ₱{p} at may sale na {d}% off. Magkano ang diskwento (sa piso)?', p * d // 100, p=p, d=d)
    if t == 6:
        l, w = (ri(15, 60), ri(10, 45)) if hard else (ri(5, 25), ri(3, 20))
        return out('A rectangular garden is {l} m long and {w} m wide. What is its area in square meters?', 'Ang hardin ay {l} m ang haba at {w} m ang lapad. Ano ang area nito sa square meters?', l * w, l=l, w=w)
    if t == 8:
        p, d = ri(2, 20) * 100, R([10, 15, 20, 25, 30, 40, 50])
        return out('A pair of shoes costs ₱{p} and is on sale at {d}% off. What is the sale price (in pesos)?', 'Ang sapatos ay nagkakahalaga ng ₱{p} at may sale na {d}% off. Ano ang presyo ngayon (sa piso)?', p - p * d // 100, p=p, d=d)
    if t == 9:
        it = R(ITEMS); n, p = ri(3, 9), ri(15, 85); tot = n * p; pay = (tot // 500 + 1) * 500
        return out('{N} buys {n} {it} at ₱{p} each and pays with ₱{pay}. How much is the change?', 'Bumili si {N} ng {n} {it} na ₱{p} bawat isa at nagbayad ng ₱{pay}. Magkano ang sukli?', pay - tot, n=n, it=it, p=p, pay=pay)
    if t == 10:
        l, w = ri(8, 40), ri(5, 30)
        return out('A rectangular garden is {l} m long and {w} m wide. How many meters of fence are needed to go around it?', 'Ang hardin ay {l} m ang haba at {w} m ang lapad. Ilang metro ng bakod ang kailangan para palibutan ito?', 2 * (l + w), l=l, w=w)
    if t == 11:
        v, hr = ri(30, 80), ri(2, 9)
        return out('A bus travels at {v} km/h. How many hours does it take to travel {d} km?', 'Ang bus ay bumibiyahe nang {v} km/h. Ilang oras ang kailangan para sa {d} km?', hr, v=v, d=v * hr)
    if t == 12:
        b, c, d = ri(10, 20), ri(2, 6), ri(3, 10)
        return out('The tricycle fare is ₱{b} for the first 2 km plus ₱{c} for each additional km. How much is the fare for a {d} km trip?', 'Ang pamasahe sa tricycle ay ₱{b} para sa unang 2 km at dagdag na ₱{c} sa bawat karagdagang km. Magkano ang pamasahe sa {d} km na biyahe?', b + c * (d - 2), b=b, c=c, d=d)
    if t == 13:
        n1, p1, n2, p2 = ri(2, 8), ri(5, 15), ri(1, 5), ri(15, 40)
        return out('{N} buys {n1} packs of noodles at ₱{p1} each and {n2} bottles of soda at ₱{p2} each at the sari-sari store. How much does {N} pay in all?', 'Bumili si {N} ng {n1} pakete ng noodles na ₱{p1} bawat isa at {n2} bote ng soda na ₱{p2} bawat isa sa sari-sari store. Magkano lahat ang kanyang binayaran?', n1 * p1 + n2 * p2, n1=n1, p1=p1, n2=n2, p2=p2)
    if t == 14:
        c, n = ri(2, 10), ri(3, 12); tot = c * n + ri(0, c - 1)
        return out('{N} has ₱{tot} load. Each call costs ₱{c}. How many whole calls can {N} make?', 'May ₱{tot} na load si {N}. Ang bawat tawag ay ₱{c}. Ilang buong tawag ang kaya niyang bayaran?', tot // c, tot=tot, c=c)
    a, b = (ri(5, 40), ri(5, 40)) if easy else (ri(10, 60), ri(10, 60))
    return out('{N} has {a} stickers and gets {b} more. How many stickers does {N} have now?', 'May {a} na stickers si {N} at nakakuha pa ng {b}. Ilan na ang stickers ni {N} ngayon?', a + b, a=a, b=b)

EXTRA_TOPICS = ('Algebra', 'Percent & Ratio', 'Geometry & Data')
PY3 = [(3, 4, 5), (5, 12, 13), (8, 15, 17), (7, 24, 25)]

def gen_shape_tl(sh):
    # Taglish version of the digit-controlled word problems
    R = random.choice; A, B = int(sh[0]), int(sh[1])
    N = R(NAMES); t = R([0, 3, 6, 7]); a, b = dnum(A), dnum(B)
    if R([0, 1]): a, b = b, a
    if t == 0:
        it = R(['notebook', 'ballpen', 'ruler', 'bote ng juice'])
        return 'Bumili si %s ng %d %s na ₱%d bawat isa. Magkano lahat ang kanyang binayaran?' % (N, b, it, a), str(a * b)
    if t == 3: return 'Ang jeep ay bumibiyahe nang %d km/h sa loob ng %d oras. Gaano kalayo ang nalakbay nito (sa km)?' % (a, b), str(a * b)
    if t == 6: return 'Ang hardin ay %d m ang haba at %d m ang lapad. Ano ang area nito sa square meters?' % (a, b), str(a * b)
    return 'May %d na stickers si %s at nakakuha pa ng %d. Ilan na ang stickers ni %s ngayon?' % (a, N, b, N), str(a + b)

def _nums(n, lo, hi, mean=False):
    # n whole numbers between lo and hi (when mean=True their sum is divisible by n, so the mean is a whole number)
    ri = random.randint; xs = [ri(lo, hi) for _ in range(n - 1)]
    if mean: last = random.choice([x for x in range(lo, hi + 1) if (sum(xs) + x) % n == 0])
    else: last = ri(lo, hi)
    xs.append(last); random.shuffle(xs); return xs

def gen_extra(topic, lv):
    from decimal import Decimal
    h, df = lvparts(lv); ri = random.randint; R = random.choice
    if topic == 'Algebra':
        if df == 1: pool = ['a1', 'a2'] + (['a3', 'e1'] if h else [])
        elif df == 2: pool = ['a1', 'a2', 'a3'] + (['a4', 'e1', 'e2', 'e4'] if h else [])
        else: pool = ['a3', 'a4', 'e1', 'e2'] if not h else ['a4', 'a5', 'e3', 'e4', 'e5', 'e6']
        t = R(pool); sm = 9 if df == 1 else 12 if df == 2 else 15
        x = nz(-sm, sm) if (h and df > 1) else ri(1, sm)
        if t == 'a1':
            a, b = ri(2, 5 if df == 1 else 9), ri(1, 15 if df == 1 else 30)
            return 'Solve for x: %dx + %d = %d' % (a, b, a * x + b), str(x)
        if t == 'a2':
            a, b = ri(2, 5 if df == 1 else 9), ri(1, 15 if df == 1 else 30)
            return 'Solve for x: %dx − %d = %d' % (a, b, a * x - b), str(x)
        if t == 'a3':
            a, b = ri(2, 9), ri(1, 12); xx = nz(-9, 9) if (h and df > 1) else ri(1, 9)
            return 'Solve for x: x/%d + %d = %d' % (a, b, xx + b), str(a * xx)
        if t == 'a4':
            a, b = ri(2, 9), ri(1, 9)
            return 'Solve for x: %d(x + %d) = %d' % (a, b, a * (x + b)), str(x)
        if t == 'a5':
            a = ri(3, 9); c = ri(1, a - 1); b = ri(1, 20); xp = ri(1, 12)
            return 'Solve for x: %dx + %d = %dx + %d' % (a, b, c, b + (a - c) * xp), str(xp)
        if t == 'e1':
            bs = R([2, 3, 5, 10]); p, q = ri(2, 9), ri(2, 9)
            return '%d^%d × %d^%d = %d^n. Find n.' % (bs, p, bs, q, bs), str(p + q)
        if t == 'e2':
            bs = R([2, 3, 5, 10]); p = ri(5, 12); q = ri(2, p - 2)
            return '%d^%d ÷ %d^%d = %d^n. Find n.' % (bs, p, bs, q, bs), str(p - q)
        if t == 'e3':
            bs = R([2, 3, 5]); p, q = ri(2, 6), ri(2, 5)
            return '(%d^%d)^%d = %d^n. Find n.' % (bs, p, q, bs), str(p * q)
        if t == 'e4':
            bs = R([2, 3, 4, 5]); e = ri(1, 4 if df == 3 else 3)
            return 'What is %d^-%d as a fraction?' % (bs, e), fs(Fr(1, bs ** e))
        if t == 'e5':
            d10 = ri(11, 99); e = ri(2, 6)
            return 'Write %.1f × 10^%d as a whole number.' % (d10 / 10, e), str(d10 * 10 ** (e - 1))
        d10 = ri(11, 99); e = ri(2, 5)
        return 'Write %.1f × 10^-%d as a decimal.' % (d10 / 10, e), format(Decimal(d10) / Decimal(10) ** (e + 1), 'f')
    if topic == 'Percent & Ratio':
        if df == 1: pool = ['p1', 'p4', 'r2']
        elif df == 2: pool = ['p1', 'p2', 'p4', 'r1', 'r2', 'r3']
        else: pool = ['p2', 'p3', 'p4', 'r1', 'r3', 'r4']
        t = R(pool)
        if t in ('p1', 'p2'):
            P = ri(2, 30 if df == 3 else 20) * 100; p = R([10, 20, 50] if df == 1 else [5, 12, 15, 35, 45] if df == 3 else [10, 20, 25, 50])
            up = t == 'p1'
            return 'An item costs ₱%d. Its price goes %s by %d%%. What is the new price (in pesos)?' % (P, 'up' if up else 'down', p), str(P + P * p // 100 if up else P - P * p // 100)
        if t == 'p3':
            b = ri(2, 10) * 20
            if R([0, 1]):
                p = R([10, 20, 25, 50]); return 'A price went from ₱%d to ₱%d. What is the percent increase?' % (b, b + b * p // 100), str(p)
            p = R([10, 20, 25, 40, 50]); return 'A price went from ₱%d to ₱%d. What is the percent decrease?' % (b, b - b * p // 100), str(p)
        if t == 'p4':
            n = ri(2, 20) * 20; p = R([10, 25, 50] if df == 1 else [15, 35, 45, 60, 80] if df == 3 else [10, 20, 25, 40, 50])
            return 'What percent of %d is %d?' % (n, n * p // 100), str(p)
        if t == 'r1':
            a, b = R([(1, 2), (1, 3), (2, 3), (3, 4), (2, 5), (3, 5), (1, 4), (4, 5)]); k = ri(5, 50)
            return 'Share ₱%d between two students in the ratio %d : %d. How much is the bigger share?' % ((a + b) * k, a, b), str(max(a, b) * k)
        if t == 'r2':
            u = ri(5, 30); n1, n2 = ri(2, 6), ri(7, 12)
            return '%d notebooks cost ₱%d. How much do %d notebooks cost?' % (n1, n1 * u, n2), str(n2 * u)
        if t == 'r3':
            a, b, k = ri(2, 9), ri(2, 9), ri(2, 9)
            while b == a: b = ri(2, 9)
            return 'Solve the proportion %d : %d = %d : x' % (a, b, a * k), str(b * k)
        s, d = ri(5, 50), ri(2, 25)
        return 'On a map, 1 cm stands for %d km. Two towns are %d cm apart on the map. What is the actual distance (in km)?' % (s, d), str(s * d)
    # Geometry & Data
    if df == 1: pool = ['s1', 's6', 's5', 'g4', 'g5']
    elif df == 2: pool = ['s1', 's2', 's4', 's5', 'g4', 'g5'] + (['g1', 'g2'] if h else ['s6'])
    else: pool = ['s2', 's3', 's4', 'g1', 'g3'] + (['g2'] if h else [])
    t = R(pool); lo, hi = (1, 10) if df == 1 else (10, 60) if df == 3 else (5, 30)
    if t == 's1':
        n = ri(3, 4) if df == 1 else ri(4, 6); xs = _nums(n, lo, hi, True)
        return 'Find the mean of %s.' % ', '.join(map(str, xs)), str(sum(xs) // n)
    if t == 's2':
        n = R([3, 5] if df == 1 else [5, 7]); xs = _nums(n, lo, hi)
        return 'Find the median of %s.' % ', '.join(map(str, xs)), str(sorted(xs)[n // 2])
    if t == 's3':
        n = R([4, 6]); xs = _nums(n, lo, hi); s = sorted(xs)
        return 'Find the median of %s.' % ', '.join(map(str, xs)), '%g' % ((s[n // 2 - 1] + s[n // 2]) / 2)
    if t == 's6':
        xs = _nums(5, lo, hi)
        return 'Find the range of %s.' % ', '.join(map(str, xs)), str(max(xs) - min(xs))
    if t == 's4':
        cols = ['red', 'blue', 'green']; cnt = [ri(1, 9), ri(1, 9), ri(1, 9)]; i = ri(0, 2)
        return 'A bag has %d red, %d blue and %d green marbles. One marble is picked at random. What is the probability of picking a %s marble? (as a fraction)' % (cnt[0], cnt[1], cnt[2], cols[i]), fs(Fr(cnt[i], sum(cnt)))
    if t == 's5':
        w, c = R([('an even number', 3), ('a number greater than 4', 2), ('a number less than 3', 2), ('a prime number', 3), ('a multiple of 3', 2), ('a number less than 5', 4)])
        return 'A fair six-sided die is rolled. What is the probability of getting %s? (as a fraction)' % w, fs(Fr(c, 6))
    if t == 'g4':
        b, hh = ri(2, 15 if df == 3 else 10) * 2, ri(2, 20 if df == 3 else 15)
        return 'A triangle has a base of %d cm and a height of %d cm. What is its area in square centimeters?' % (b, hh), str(b * hh // 2)
    if t == 'g5':
        l, w, hh = (ri(2, 6), ri(2, 6), ri(2, 6)) if df == 1 else (ri(3, 12), ri(3, 10), ri(2, 9))
        return 'A box is %d cm long, %d cm wide and %d cm high. What is its volume in cubic centimeters?' % (l, w, hh), str(l * w * hh)
    a, b, c = R(PY3[:2] if df == 2 else PY3); k = ri(1, 4 if df == 3 else 3); a, b, c = a * k, b * k, c * k
    if R([0, 1]): a, b = b, a
    if t == 'g1': return 'A right triangle has legs %d and %d. How long is the hypotenuse?' % (a, b), str(c)
    if t == 'g2': return 'A right triangle has a hypotenuse of %d and one leg of %d. How long is the other leg?' % (c, a), str(b)
    return 'A %d m ladder leans against a wall. Its foot is %d m from the wall. How high up the wall does it reach (in m)?' % (c, a), str(b)

def gen_seeded(topic, lv, seed, sh=''):
    st = random.getstate(); random.seed(seed)
    try: return gen(topic, lv, sh)
    finally: random.setstate(st)

# ---------------- Study review: the last question each student answered ----------------
# A student who has just answered is (by the fair cycle) not picked again for a while. While they wait, their phone shows
# the LAST question they answered, their own answer, the correct answer and a short worked solution, so they can study it.
def _P(n): return '(%d)' % n if n < 0 else str(n)

def _add_steps(a, b):
    r = a + b
    if a == 0 or b == 0: return ['Adding 0 changes nothing: %s + %s = %d.' % (_P(a), _P(b), r)]
    if a > 0 and b > 0: return ['Add the numbers: %d + %d = %d.' % (a, b, r)]
    if (a < 0) == (b < 0):
        return ['Same signs: add the numbers and ignore the signs: %d + %d = %d.' % (abs(a), abs(b), abs(a) + abs(b)),
                'Keep the negative sign, so the answer is %d.' % r]
    big, small = max(abs(a), abs(b)), min(abs(a), abs(b)); owner = a if abs(a) > abs(b) else b
    st = ['Different signs: subtract the smaller number from the larger and ignore the signs: %d \u2212 %d = %d.' % (big, small, big - small)]
    st.append('They cancel out, so the answer is 0.' if r == 0 else 'Use the sign of the number that is farther from zero (%s), so the answer is %d.' % (_P(owner), r))
    return st

def _frac_finish(n, m):
    r = Fr(n, m); st = ['So the result is %d/%d.' % (n, m)]
    if r.denominator != m: st.append('Simplify: %d/%d = %s.' % (n, m, fs(r)))
    return st

def _explain(q, ans):
    from math import gcd
    NUM = r'\(?(-?\d+)\)?'
    m = re.fullmatch(NUM + r' ([+\u2212\u00d7\u00f7]) ' + NUM + r' = \?', q)
    if m:
        a, op, b = int(m[1]), m[2], int(m[3])
        if op == '+': return _add_steps(a, b)
        if op == '\u2212':
            if a >= 0 and b >= 0 and a >= b: return ['Subtract: %d \u2212 %d = %d.' % (a, b, a - b)]
            return ['Subtracting a number is the same as adding its opposite: %s \u2212 %s = %s + %s.' % (_P(a), _P(b), _P(a), _P(-b))] + _add_steps(a, -b)
        if op == '\u00d7':
            r = a * b
            if a >= 0 and b >= 0: return ['Multiply: %d \u00d7 %d = %d.' % (a, b, r)]
            return ['Multiply the numbers and ignore the signs: %d \u00d7 %d = %d.' % (abs(a), abs(b), abs(r)),
                    'Same signs give a positive answer, different signs give a negative answer. Here the signs are %s, so the answer is %d.' % ('the same' if (a < 0) == (b < 0) else 'different', r)]
        if b != 0:
            r = a // b
            st = ['Divide the numbers and ignore the signs: %d \u00f7 %d = %d.' % (abs(a), abs(b), abs(r))]
            if a < 0 or b < 0: st.append('Same signs give a positive answer, different signs give a negative answer. Here the signs are %s, so the answer is %d.' % ('the same' if (a < 0) == (b < 0) else 'different', r))
            return st + ['Check by multiplying: %d \u00d7 %s = %d.' % (r, _P(b), a)]
    m = re.fullmatch(NUM + r' \+ ' + NUM + r' \u2212 ' + NUM + r' = \?', q)
    if m:
        a, b, c = int(m[1]), int(m[2]), int(m[3])
        return ['Work from left to right. First: %s + %s = %d.' % (_P(a), _P(b), a + b),
                'Then subtract %s: %d \u2212 %s = %d.' % (_P(c), a + b, _P(c), a + b - c)]
    m = re.fullmatch(r'(\d+)\^2 = \?', q)
    if m: x = int(m[1]); return ['Squaring means multiplying a number by itself: %d \u00d7 %d = %d.' % (x, x, x * x)]
    m = re.fullmatch(r'(\d+)\^3 = \?', q)
    if m: x = int(m[1]); return ['Cubing means multiplying the number three times: %d \u00d7 %d \u00d7 %d.' % (x, x, x), '%d \u00d7 %d = %d, then %d \u00d7 %d = %d.' % (x, x, x * x, x * x, x, x ** 3)]
    m = re.fullmatch(r'sqrt\((\d+)\) = \?', q)
    if m: n = int(m[1]); x = int(round(n ** 0.5)); return ['Find the number that gives %d when multiplied by itself.' % n, '%d \u00d7 %d = %d, so the square root is %d.' % (x, x, n, x)]
    m = re.fullmatch(r'What is (\d+)% of (\d+)\?', q)
    if m: p, n = int(m[1]), int(m[2]); return ['Percent means "per 100", so %d%% = %d/100.' % (p, p), 'Multiply: %d/100 \u00d7 %d = %d.' % (p, n, p * n // 100)]
    m = re.fullmatch(r'What is (\d+)/(\d+) of (\d+)\?', q)
    if m:
        a, b, n = int(m[1]), int(m[2]), int(m[3])
        return ['"Of" means multiply. First find 1/%d of %d by dividing: %d \u00f7 %d = %d.' % (b, n, n, b, n // b), 'Then multiply by %d: %d \u00d7 %d = %s.' % (a, n // b, a, ans)]
    m = re.fullmatch(r'Write (\d+)/(\d+) as a decimal\.', q)
    if m: return ['A fraction is a division: divide the top by the bottom.', '%s \u00f7 %s = %s.' % (m[1], m[2], ans)]
    m = re.fullmatch(r'(\d+)/(\d+) ([+\u2212\u00d7\u00f7]) (\d+)/(\d+) = \?', q)
    if m:
        a, b, op, c, d = int(m[1]), int(m[2]), m[3], int(m[4]), int(m[5])
        if op in '+\u2212':
            L = b * d // gcd(b, d); n1, n2 = a * (L // b), c * (L // d); res = n1 + n2 if op == '+' else n1 - n2
            return ['Make the denominators the same. A common denominator of %d and %d is %d.' % (b, d, L),
                    '%d/%d = %d/%d and %d/%d = %d/%d.' % (a, b, n1, L, c, d, n2, L),
                    '%s the numerators and keep the denominator: %d %s %d = %d.' % ('Add' if op == '+' else 'Subtract', n1, op, n2, res)] + _frac_finish(res, L)
        if op == '\u00f7':
            return ['Keep the first fraction, change \u00f7 to \u00d7, and flip the second fraction: %d/%d \u00d7 %d/%d.' % (a, b, d, c),
                    'Multiply the tops: %d \u00d7 %d = %d. Multiply the bottoms: %d \u00d7 %d = %d.' % (a, d, a * d, b, c, b * c)] + _frac_finish(a * d, b * c)
        return ['Multiply the tops: %d \u00d7 %d = %d.' % (a, c, a * c), 'Multiply the bottoms: %d \u00d7 %d = %d.' % (b, d, b * d)] + _frac_finish(a * c, b * d)
    m = re.fullmatch(r'Evaluate 3x \u2212 5 when x = \(?(-?\d+)\)?', q)
    if m:
        c = int(m[1])
        return ['Replace x with %s: 3 \u00d7 %s \u2212 5.' % (_P(c), _P(c)), 'Multiply first: 3 \u00d7 %s = %d.' % (_P(c), 3 * c), 'Then subtract 5: %s \u2212 5 = %s.' % (_P(3 * c), ans)]
    m = re.fullmatch(r'\|(-?\d+) \u2212 (-?\d+)\| = \?', q)
    if m:
        a, b = int(m[1]), int(m[2])
        return ['Work out the inside first: %s \u2212 %s = %d.' % (_P(a), _P(b), a - b), 'Absolute value is the distance from zero, so it is never negative: |%d| = %d.' % (a - b, abs(a - b))]
    m = re.fullmatch(r'\w+ buys (\d+) (.+?) at \u20b1(\d+) each\. How much does \w+ pay in all\?', q)
    if m: n, p = int(m[1]), int(m[3]); return ['Total cost = number of items \u00d7 price of each.', '%d \u00d7 \u20b1%d = \u20b1%d.' % (n, p, n * p)]
    m = re.fullmatch(r'\w+ buys a snack for \u20b1(\d+) and pays \u20b1(\d+)\. How much is the change\?', q)
    if m: c, p = int(m[1]), int(m[2]); return ['Change = money paid \u2212 cost.', '\u20b1%d \u2212 \u20b1%d = \u20b1%d.' % (p, c, p - c)]
    m = re.fullmatch(r'\w+ has (\d+) marbles\. (\d+)/(\d+) of them are red\. How many marbles are red\?', q)
    if m:
        t, a, b = int(m[1]), int(m[2]), int(m[3])
        return ['Find 1/%d of the marbles: %d \u00f7 %d = %d.' % (b, t, b, t // b), 'Red marbles are %d parts, so multiply: %d \u00d7 %d = %d.' % (a, t // b, a, t // b * a)]
    m = re.fullmatch(r'A jeepney travels at (\d+) km/h for (\d+) hours\. How far does it travel \(in km\)\?', q)
    if m: v, t = int(m[1]), int(m[2]); return ['Distance = speed \u00d7 time.', '%d km/h \u00d7 %d hours = %d km.' % (v, t, v * t)]
    m = re.fullmatch(r'The temperature was (-?\d+) degrees in the morning, then rose by (\d+) degrees\. What is the temperature now\?', q)
    if m:
        s0, ch = int(m[1]), int(m[2])
        return ['Rising means adding: %s + %d.' % (_P(s0), ch)] + _add_steps(s0, ch)
    m = re.fullmatch(r'A bag costs \u20b1(\d+) and is on sale at (\d+)% off\. How much is the discount \(in pesos\)\?', q)
    if m: p, d = int(m[1]), int(m[2]); return ['Discount = price \u00d7 rate. %d%% = %d/100.' % (d, d), '\u20b1%d \u00d7 %d/100 = \u20b1%d.' % (p, d, p * d // 100)]
    m = re.fullmatch(r'A rectangular garden is (\d+) m long and (\d+) m wide\. What is its area in square meters\?', q)
    if m: l, w = int(m[1]), int(m[2]); return ['Area of a rectangle = length \u00d7 width.', '%d m \u00d7 %d m = %d square meters.' % (l, w, l * w)]
    m = re.fullmatch(r'\w+ has (\d+) stickers and gets (\d+) more\. How many stickers does \w+ have now\?', q)
    if m: a, b = int(m[1]), int(m[2]); return ['"Gets more" means add: %d + %d = %d.' % (a, b, a + b)]
    m = re.fullmatch(r'Simplify (\d+)/(\d+)\.', q)
    if m:
        n, d = int(m[1]), int(m[2]); g = gcd(n, d)
        return ['Find the greatest common factor of %d and %d. It is %d.' % (n, d, g), 'Divide the top and the bottom by %d: %d ÷ %d = %d and %d ÷ %d = %d.' % (g, n, g, n // g, d, g, d // g), 'The simplified fraction is %s.' % ans]
    m = re.fullmatch(r'Evaluate x\^2 − 3x when x = \(?(-?\d+)\)?', q)
    if m:
        c = int(m[1])
        return ['Replace x with %s: %s^2 − 3 × %s.' % (_P(c), _P(c), _P(c)), 'Square first: %s^2 = %d, and 3 × %s = %d.' % (_P(c), c * c, _P(c), 3 * c), 'Then subtract: %d − %s = %s.' % (c * c, _P(3 * c), ans)]
    m = re.fullmatch(r'A pair of shoes costs ₱(\d+) and is on sale at (\d+)% off\. What is the sale price \(in pesos\)\?', q)
    if m: p, d = int(m[1]), int(m[2]); return ['First find the discount: %d%% of ₱%d = ₱%d.' % (d, p, p * d // 100), 'Sale price = price − discount: ₱%d − ₱%d = ₱%d.' % (p, p * d // 100, p - p * d // 100)]
    m = re.fullmatch(r'\w+ buys (\d+) (.+?) at ₱(\d+) each and pays with ₱(\d+)\. How much is the change\?', q)
    if m: n, p, pay = int(m[1]), int(m[3]), int(m[4]); return ['First find the total cost: %d × ₱%d = ₱%d.' % (n, p, n * p), 'Change = money paid − total cost: ₱%d − ₱%d = ₱%d.' % (pay, n * p, pay - n * p)]
    m = re.fullmatch(r'A rectangular garden is (\d+) m long and (\d+) m wide\. How many meters of fence are needed to go around it\?', q)
    if m: l, w = int(m[1]), int(m[2]); return ['The fence goes around the garden, so we need the perimeter: 2 × (length + width).', '2 × (%d + %d) = 2 × %d = %d meters.' % (l, w, l + w, 2 * (l + w))]
    m = re.fullmatch(r'A bus travels at (\d+) km/h\. How many hours does it take to travel (\d+) km\?', q)
    if m: v, d = int(m[1]), int(m[2]); return ['Time = distance ÷ speed.', '%d km ÷ %d km/h = %d hours.' % (d, v, d // v)]
    m = re.fullmatch(r'Solve for x: (\d+)x \+ (\d+) = (-?\d+)', q)
    if m: a, b, c = int(m[1]), int(m[2]), int(m[3]); return ['Subtract %d from both sides: %dx = %d − %d = %d.' % (b, a, c, b, c - b), 'Divide both sides by %d: x = %d ÷ %d = %s.' % (a, c - b, a, ans)]
    m = re.fullmatch(r'Solve for x: (\d+)x − (\d+) = (-?\d+)', q)
    if m: a, b, c = int(m[1]), int(m[2]), int(m[3]); return ['Add %d to both sides: %dx = %d + %d = %d.' % (b, a, c, b, c + b), 'Divide both sides by %d: x = %d ÷ %d = %s.' % (a, c + b, a, ans)]
    m = re.fullmatch(r'Solve for x: x/(\d+) \+ (\d+) = (-?\d+)', q)
    if m: a, b, c = int(m[1]), int(m[2]), int(m[3]); return ['Subtract %d from both sides: x/%d = %d − %d = %d.' % (b, a, c, b, c - b), 'Multiply both sides by %d: x = %d × %d = %s.' % (a, c - b, a, ans)]
    m = re.fullmatch(r'Solve for x: (\d+)\(x \+ (\d+)\) = (-?\d+)', q)
    if m: a, b, c = int(m[1]), int(m[2]), int(m[3]); return ['Divide both sides by %d: x + %d = %d.' % (a, b, c // a), 'Subtract %d from both sides: x = %d − %d = %s.' % (b, c // a, b, ans)]
    m = re.fullmatch(r'Solve for x: (\d+)x \+ (\d+) = (\d+)x \+ (\d+)', q)
    if m: a, b, c, d = int(m[1]), int(m[2]), int(m[3]), int(m[4]); return ['Get the x terms on one side: %dx − %dx = %d − %d, so %dx = %d.' % (a, c, d, b, a - c, d - b), 'Divide both sides by %d: x = %s.' % (a - c, ans)]
    m = re.fullmatch(r'(\d+)\^(\d+) × (\d+)\^(\d+) = (\d+)\^n\. Find n\.', q)
    if m: p, r = int(m[2]), int(m[4]); return ['Same base, so add the exponents when multiplying: n = %d + %d = %d.' % (p, r, p + r)]
    m = re.fullmatch(r'(\d+)\^(\d+) ÷ (\d+)\^(\d+) = (\d+)\^n\. Find n\.', q)
    if m: p, r = int(m[2]), int(m[4]); return ['Same base, so subtract the exponents when dividing: n = %d − %d = %d.' % (p, r, p - r)]
    m = re.fullmatch(r'\((\d+)\^(\d+)\)\^(\d+) = (\d+)\^n\. Find n\.', q)
    if m: p, r = int(m[2]), int(m[3]); return ['A power of a power: multiply the exponents. n = %d × %d = %d.' % (p, r, p * r)]
    m = re.fullmatch(r'What is (\d+)\^-(\d+) as a fraction\?', q)
    if m: b, e = int(m[1]), int(m[2]); return ['A negative exponent means "one over": %d^-%d = 1/%d^%d.' % (b, e, b, e), '%d^%d = %d, so the answer is 1/%d.' % (b, e, b ** e, b ** e)]
    m = re.fullmatch(r'Write ([\d.]+) × 10\^(\d+) as a whole number\.', q)
    if m: return ['Multiplying by 10^%s moves the decimal point %s places to the right.' % (m[2], m[2]), 'So the answer is %s.' % ans]
    m = re.fullmatch(r'Write ([\d.]+) × 10\^-(\d+) as a decimal\.', q)
    if m: return ['Multiplying by 10^-%s moves the decimal point %s places to the left.' % (m[2], m[2]), 'So the answer is %s.' % ans]
    m = re.fullmatch(r'An item costs ₱(\d+)\. Its price goes (up|down) by (\d+)%\. What is the new price \(in pesos\)\?', q)
    if m:
        P, p = int(m[1]), int(m[3]); ch = P * p // 100
        return ['Find the change: %d%% of ₱%d = ₱%d.' % (p, P, ch), ('Add it to the price: ₱%d + ₱%d = ₱%s.' if m[2] == 'up' else 'Subtract it from the price: ₱%d − ₱%d = ₱%s.') % (P, ch, ans)]
    m = re.fullmatch(r'A price went from ₱(\d+) to ₱(\d+)\. What is the percent (increase|decrease)\?', q)
    if m: a, b = int(m[1]), int(m[2]); return ['Find the change: |%d − %d| = %d.' % (b, a, abs(b - a)), 'Percent change = change ÷ original price × 100: %d ÷ %d × 100 = %s%%.' % (abs(b - a), a, ans)]
    m = re.fullmatch(r'What percent of (\d+) is (\d+)\?', q)
    if m: n, part = int(m[1]), int(m[2]); return ['Percent = part ÷ whole × 100.', '%d ÷ %d × 100 = %s%%.' % (part, n, ans)]
    m = re.fullmatch(r'Share ₱(\d+) between two students in the ratio (\d+) : (\d+)\. How much is the bigger share\?', q)
    if m:
        tot, a, b = int(m[1]), int(m[2]), int(m[3])
        return ['Add the parts: %d + %d = %d parts.' % (a, b, a + b), 'One part = ₱%d ÷ %d = ₱%d.' % (tot, a + b, tot // (a + b)), 'The bigger share has %d parts: %d × ₱%d = ₱%s.' % (max(a, b), max(a, b), tot // (a + b), ans)]
    m = re.fullmatch(r'(\d+) notebooks cost ₱(\d+)\. How much do (\d+) notebooks cost\?', q)
    if m: n1, c, n2 = int(m[1]), int(m[2]), int(m[3]); return ['Find the cost of one: ₱%d ÷ %d = ₱%d.' % (c, n1, c // n1), 'Multiply by %d: %d × ₱%d = ₱%s.' % (n2, n2, c // n1, ans)]
    m = re.fullmatch(r'Solve the proportion (\d+) : (\d+) = (\d+) : x', q)
    if m: a, b, c = int(m[1]), int(m[2]), int(m[3]); return ['Find what the first number was multiplied by: %d ÷ %d = %d.' % (c, a, c // a), 'Do the same to the second number: %d × %d = %s.' % (b, c // a, ans)]
    m = re.fullmatch(r'On a map, 1 cm stands for (\d+) km\. Two towns are (\d+) cm apart on the map\. What is the actual distance \(in km\)\?', q)
    if m: s, d = int(m[1]), int(m[2]); return ['Each cm on the map is %d km, so multiply: %d × %d = %s km.' % (s, d, s, ans)]
    m = re.fullmatch(r'Find the mean of (.+)\.', q)
    if m: xs = [int(v) for v in m[1].split(', ')]; return ['Add all the numbers: %s = %d.' % (' + '.join(map(str, xs)), sum(xs)), 'Divide by how many numbers there are (%d): %d ÷ %d = %s.' % (len(xs), sum(xs), len(xs), ans)]
    m = re.fullmatch(r'Find the median of (.+)\.', q)
    if m: xs = sorted(int(v) for v in m[1].split(', ')); return ['Arrange the numbers in order: %s.' % ', '.join(map(str, xs)), ('The median is the middle number: %s.' if len(xs) % 2 else 'There are two middle numbers. Find their average: %s.') % ans]
    m = re.fullmatch(r'Find the range of (.+)\.', q)
    if m: xs = [int(v) for v in m[1].split(', ')]; return ['Range = biggest − smallest.', '%d − %d = %s.' % (max(xs), min(xs), ans)]
    m = re.fullmatch(r'A bag has (\d+) red, (\d+) blue and (\d+) green marbles\. .* picking a (\w+) marble\? \(as a fraction\)', q)
    if m: tot = int(m[1]) + int(m[2]) + int(m[3]); return ['Probability = favourable outcomes ÷ all outcomes.', 'All marbles: %d. Simplify the fraction if you can: %s.' % (tot, ans)]
    m = re.fullmatch(r'A fair six-sided die is rolled\. What is the probability of getting (.+)\? \(as a fraction\)', q)
    if m: return ['A die has 6 equally likely outcomes: 1, 2, 3, 4, 5, 6.', 'Count the outcomes that are %s, then write that number over 6 and simplify: %s.' % (m[1], ans)]
    m = re.fullmatch(r'A right triangle has legs (\d+) and (\d+)\. How long is the hypotenuse\?', q)
    if m: a, b = int(m[1]), int(m[2]); return ['Pythagorean theorem: c² = a² + b².', 'c² = %d² + %d² = %d + %d = %d.' % (a, b, a * a, b * b, a * a + b * b), 'c = √%d = %s.' % (a * a + b * b, ans)]
    m = re.fullmatch(r'A right triangle has a hypotenuse of (\d+) and one leg of (\d+)\. How long is the other leg\?', q)
    if m: c, a = int(m[1]), int(m[2]); return ['Pythagorean theorem: a² + b² = c², so b² = c² − a².', 'b² = %d² − %d² = %d − %d = %d.' % (c, a, c * c, a * a, c * c - a * a), 'b = √%d = %s.' % (c * c - a * a, ans)]
    m = re.fullmatch(r'A (\d+) m ladder leans against a wall\. Its foot is (\d+) m from the wall\. How high up the wall does it reach \(in m\)\?', q)
    if m: c, a = int(m[1]), int(m[2]); return ['The ladder, wall and ground make a right triangle. The ladder is the hypotenuse: a² + b² = c².', 'b² = %d² − %d² = %d − %d = %d.' % (c, a, c * c, a * a, c * c - a * a), 'b = √%d = %s m.' % (c * c - a * a, ans)]
    m = re.fullmatch(r'A triangle has a base of (\d+) cm and a height of (\d+) cm\. What is its area in square centimeters\?', q)
    if m: b, hh = int(m[1]), int(m[2]); return ['Area of a triangle = ½ × base × height.', '½ × %d × %d = %s square cm.' % (b, hh, ans)]
    m = re.fullmatch(r'A box is (\d+) cm long, (\d+) cm wide and (\d+) cm high\. What is its volume in cubic centimeters\?', q)
    if m: l, w, hh = int(m[1]), int(m[2]), int(m[3]); return ['Volume = length × width × height.', '%d × %d × %d = %s cubic cm.' % (l, w, hh, ans)]
    m = re.fullmatch(r'The tricycle fare is ₱(\d+) for the first 2 km plus ₱(\d+) for each additional km\. How much is the fare for a (\d+) km trip\?', q)
    if m: b, c, d = int(m[1]), int(m[2]), int(m[3]); return ['Extra distance: %d − 2 = %d km.' % (d, d - 2), 'Extra fare: %d × ₱%d = ₱%d.' % (d - 2, c, (d - 2) * c), 'Total fare: ₱%d + ₱%d = ₱%s.' % (b, (d - 2) * c, ans)]
    m = re.fullmatch(r'\w+ buys (\d+) packs of noodles at ₱(\d+) each and (\d+) bottles of soda at ₱(\d+) each at the sari-sari store\. How much does \w+ pay in all\?', q)
    if m: n1, p1, n2, p2 = int(m[1]), int(m[2]), int(m[3]), int(m[4]); return ['Noodles: %d × ₱%d = ₱%d.' % (n1, p1, n1 * p1), 'Soda: %d × ₱%d = ₱%d.' % (n2, p2, n2 * p2), 'Add them: ₱%d + ₱%d = ₱%s.' % (n1 * p1, n2 * p2, ans)]
    m = re.fullmatch(r'\w+ has ₱(\d+) load\. Each call costs ₱(\d+)\. How many whole calls can \w+ make\?', q)
    if m: tot, c = int(m[1]), int(m[2]); return ['Divide the load by the cost of one call: %d ÷ %d.' % (tot, c), '%d calls cost ₱%d, and the leftover is less than one call, so the answer is %s calls.' % (tot // c, c * (tot // c), ans)]
    return []

_EXC = {}
def explain(q, ans):
    # short worked solution (list of steps); an empty list means "no steps known", the review then shows only the correct answer
    k = (str(q), str(ans))
    if k not in _EXC:
        if len(_EXC) > 3000: _EXC.clear()
        try: _EXC[k] = _explain(*k)
        except Exception: _EXC[k] = []
    return _EXC[k]

def archive_round():
    # called just before a new cold-call round replaces the old one: keep each student's last answered question
    p = D['rp']; sl = cur(); L = D.setdefault('lastq', {})
    for q in p.get('picks', []):
        mine = str(q.get('ans', '')).strip()
        if not mine or q.get('lf'): continue   # no answer, or somebody else answered for them (lifeline): nothing of their own to study
        if not q.get('q') and p.get('tok') != qtok(sl): continue   # teacher-written slide that has since changed
        sx = pkq(sl, q)
        if not sx.get('ans'): continue
        L[skey(q['sec'], q['name'])] = {'n': p.get('n'), 'q': sx['q'], 'a': sx['ans'], 'mine': mine[:80],
                                       'mark': 'ok' if correct(sx, mine) else 'no', 'ex': explain(sx['q'], sx['ans'])}

def vq(s, c):
    # (question, answer) this client sees; "everyone answers" slides give each student their own numbers
    if s.get('var') and s.get('type') == 'num' and s.get('topic') and c:
        c = ckey(c) if c in D['names'] else c   # a student keeps the same question on any device; unjoined students get theirs by 'section|name'
        return gen_seeded(s['topic'], s.get('lv', 1), zlib.crc32(('%s|%s|%s' % (s.get('sd'), s.get('gv', 0), c)).encode()), s.get('sh', ''))
    return s['q'], s.get('ans', '')

def sfor(s, c):
    q, a = vq(s, c); return dict(s, q=q, ans=a)

# ---------------- Topic mastery report: this session vs the last 10 earlier sessions ----------------
def _toks(key):
    # correct-answer tokens and attempt tokens of one student (all sessions), including the cold-call round that is not committed yet
    p = D['rp']; ok = dict(D['life'].get(key, {})); at = dict(D['att'].get(key, {}))
    t_ = p.get('topic') or cur()['topic']; tk = '%s~%s' % (D['lsn'], rtok(p))
    for q in p.get('picks', []):
        if q.get('mark') == 'ok' and pkey(q) == key: ok[tk] = t_
    if key in rattempts(p): at[tk] = t_
    return ok, at
def hp_of(key):
    # HP (level points): every SESSION (one run of the program) earns that session's accuracy = correct / items answered.
    # 100% = 1 HP, 10% = 0.10 HP, so 10 HP = 100% in 10 sessions. The current session counts live. Returns (total HP, this session's HP).
    ok, at = _toks(key); per = {}
    for t in at: per.setdefault(t.split('~', 1)[0], [0, 0])[1] += 1
    for t in ok: per.setdefault(t.split('~', 1)[0], [0, 0])[0] += 1
    tot = now = 0.0
    for s, (c, a) in per.items():
        a = max(a, c)
        if a:
            h = c / float(a); tot += h
            if s == str(D['lsn']): now = h
    return round(tot, 3), round(now, 3)
def mastery_of(key):
    # per topic (and 'All'): {now: [correct, attempts], prev: [correct, attempts] summed over the last 10 earlier sessions the student attempted, n: sessions counted, tr: accuracy % of each of those sessions}
    ok, at = _toks(key); S = {}
    for tokmap, i in ((ok, 0), (at, 1)):
        for lt, t in tokmap.items():
            try: sn = int(str(lt).split('~', 1)[0])
            except Exception: continue
            S.setdefault(sn, {}).setdefault(t, [0, 0])[i] += 1
    out = {}
    for t in TOPICS + ['All']:
        rows = []
        for sn in sorted(S):
            a = [sum(v[0] for v in S[sn].values()), sum(v[1] for v in S[sn].values())] if t == 'All' else S[sn].get(t, [0, 0])
            rows.append((sn, a[0], a[1]))
        now = next(((o_, a_) for sn, o_, a_ in rows if sn == D['lsn']), (0, 0))
        prev = [r for r in rows if r[0] != D['lsn'] and r[2] > 0][-10:]
        out[t] = {'now': list(now), 'prev': [sum(r[1] for r in prev), sum(r[2] for r in prev)], 'n': len(prev),
                  'tr': [min(100, round(100 * r[1] / r[2])) for r in prev]}
    return out

def skills_of(key):
    # one student's grade in each operation skill: all = [correct, attempts] over every session, now = this session, prev = the last 10 earlier sessions
    # (n sessions, tr = accuracy % of each), bo / in = split by tab (Basic Operations = whole numbers, Integers = with negatives), err = mistakes by type
    sk = dict(D['sk'].get(key, {})); ok = set(D['life'].get(key, {})); tp = dict(D['att'].get(key, {})); p = D['rp']
    if key in rattempts(p):   # the cold-call round that is not committed yet counts live
        tk = '%s~%s' % (D['lsn'], rtok(p)); t_ = p.get('topic') or cur()['topic']; s_ = skill_of(_rq(p, key), t_)
        if s_:
            sk[tk] = s_; tp[tk] = t_
            if any(q.get('mark') == 'ok' and pkey(q) == key for q in p.get('picks', [])): ok.add(tk)
    S = {k: {} for k in SKILL_KEYS}
    out = {k: {'all': [0, 0], 'bo': [0, 0], 'in': [0, 0], 'err': dict(D['skerr'].get(key, {}).get(k, {}))} for k in SKILL_KEYS}
    for lt, s_ in sk.items():
        if s_ not in S: continue
        try: sn = int(str(lt).split('~', 1)[0])
        except Exception: continue
        good = 1 if lt in ok else 0; r = S[s_].setdefault(sn, [0, 0]); r[0] += good; r[1] += 1
        for a in (out[s_]['all'], out[s_]['bo' if tp.get(lt) == 'Basic Operations' else 'in']): a[0] += good; a[1] += 1
    for k in SKILL_KEYS:
        prev = [r for r in sorted(S[k].items()) if r[0] != D['lsn'] and r[1][1] > 0][-10:]
        out[k].update(now=list(S[k].get(D['lsn'], [0, 0])), prev=[sum(r[1][0] for r in prev), sum(r[1][1] for r in prev)], n=len(prev),
                      tr=[min(100, round(100 * r[1][0] / r[1][1])) for r in prev])
    return out
def t_skill_sec(sec):
    # PRE / POST test results per skill for one section: {name: {'pre': {skill: [correct, items]}, 'post': {...}}}
    out = {}
    try:
        for name, o in t_sheets(sec).items():
            r = {}
            for ph, v in o.items():
                per = {}
                for it in v['rows']:
                    sk_ = skill_of(it['q'], it['t'])
                    if sk_: x = per.setdefault(sk_, [0, 0]); x[1] += 1; x[0] += 1 if it['ok'] else 0
                r[ph] = per
            if r: out[name] = r
    except Exception: return {}
    return out

def secs():
    x = D.get('section'); return [x if x in ROSTER else next(iter(ROSTER))]   # always exactly ONE section

def make(t, k, lv):
    # create/refresh the one auto-generated slide for this tab (topic) + kind, and jump to it
    S = D['slides']; sh = D['shape'].get(t, ''); q, ans = gen(t, lv, sh)
    g = next((x for x in S if x.get('auto') and x['topic'] == t and x['type'] == k), None)
    if not g: g = blank(k, D['nid']); D['nid'] += 1; g.update(topic=t, auto=True); S.append(g)
    g.update(q=q, ans=ans, votes={}, words={}, answers=[], start=0, rev=False, by={}, turn='', log=[], gv=g.get('gv', 0) + 1,
             var=(k == 'num'), sd=random.randint(1, 10 ** 9), lv=lv, sh=sh); g.pop('revt', None); voters.pop(g['id'], None)
    D['cur'] = S.index(g); return g

# ======================= ROSTER EDITING (dashboard: Roster tab) =======================
# Sections and students are edited from the dashboard. The list is kept in D['roster'] (gnhs-data.json) and, once saved there,
# replaces the list embedded above. Removing a student or a section never deletes their saved results (scores, mastery, tests):
# adding the same section / name again brings them back. Renaming a section moves everything saved for it to the new name.
R_MAX_SEC, R_MAX_STU, R_NAME = 40, 200, 60
def _rname(x, n=R_NAME): return re.sub(r'\s+', ' ', str(x if x is not None else '').replace('|', '/')).strip()[:n]
def _rfind(L, name):   # position of a name in a list, ignoring upper / lower case (-1 = not there)
    k = name.casefold(); return next((i for i, x in enumerate(L) if x.casefold() == k), -1)
def _ren(o, old, new):   # copy of o with the section name replaced in every key ('old', 'old|student') and every value equal to it
    pre = old + '|'
    def f(x): return new if x == old else (new + '|' + x[len(pre):] if x.startswith(pre) else x)
    if isinstance(o, dict): return {(f(k) if isinstance(k, str) else k): _ren(v, old, new) for k, v in o.items()}
    if isinstance(o, list): return [_ren(v, old, new) for v in o]
    if isinstance(o, tuple): return tuple(_ren(v, old, new) for v in o)
    return f(o) if isinstance(o, str) else o
def roster_rename(old, new):
    _its = [(new if k == old else k, v) for k, v in ROSTER.items()]; ROSTER.clear(); ROSTER.update(_its)   # same place in the list
    for k in [k for k in D if k not in ('roster', 'slides')]: D[k] = _ren(D[k], old, new)
    for k in list(TD): TD[k] = _ren(TD[k], old, new)
    pre = old + '|'
    for x in [x for x in TPAUSE if x.startswith(pre)]: TPAUSE.discard(x); TPAUSE.add(new + '|' + x[len(pre):])
    sk = lambda k: (new, k[1]) if k[0] == old else k
    for dct, f in ((CLAIM, sk), (TCLAIM, sk), (TOPEN, lambda k: (k[0], new + '|' + k[1][len(pre):]) if k[1].startswith(pre) else k)):
        for k in list(dct):
            nk = f(k)
            if nk != k: dct[nk] = dct.pop(k)
def _rdrop(sec, name):   # a student leaves the class list: out of the teams, the pick list and the join list (saved results stay)
    if sec in D['teams']:
        for t in D['teams'][sec]:
            if name in t['m']: t['m'].remove(name)
        D['teams'][sec] = [t for t in D['teams'][sec] if t['m']]   # a team with nobody left disappears
    D['picked'] = [x for x in D['picked'] if not (x[0] == sec and x[1] == name)]
    for c in [c for c in D['names'] if D['names'].get(c) == name and D['secs'].get(c) == sec]:
        D['names'].pop(c, None); D['secs'].pop(c, None); SEEN.pop(c, None)
    CLAIM.pop((sec, name), None)
def roster_action(d):
    a = d.get('a'); sec = d.get('sec'); msg = ''; sel = None; undo = None; ok = False
    if a == 'addsec':
        n = _rname(d.get('name'))
        if not n: msg = 'Type a section name first.'
        elif _rfind(list(ROSTER), n) >= 0: msg = 'There is already a section called "%s".' % n
        elif len(ROSTER) >= R_MAX_SEC: msg = 'That is the most sections allowed (%d).' % R_MAX_SEC
        else: ROSTER[n] = []; sel = n; ok = True; msg = 'Added the section "%s". Now add its students.' % n
    elif a == 'get': pass
    elif sec not in ROSTER: msg = 'That section no longer exists.'
    elif a == 'rensec':
        n = _rname(d.get('name'))
        if not n: msg = 'Type the new section name.'
        elif n == sec: pass
        elif _rfind([k for k in ROSTER if k != sec], n) >= 0: msg = 'There is already a section called "%s".' % n
        else: roster_rename(sec, n); sel = n; ok = True; msg = 'Renamed "%s" to "%s". Everything saved for it moved with it.' % (sec, n)
    elif a == 'delsec':
        if len(ROSTER) < 2: msg = 'Keep at least one section.'
        else:
            for nm in list(ROSTER[sec]): _rdrop(sec, nm)
            del ROSTER[sec]
            if D.get('section') == sec: D['section'] = next(iter(ROSTER))
            ok = True; msg = 'Removed the section "%s". Its saved results are kept and come back if you add the same section again.' % sec
    elif a == 'add':
        n = _rname(d.get('name')); L = ROSTER[sec]
        if not n: msg = 'Type the student\'s name first.'
        elif _rfind(L, n) >= 0: msg = '%s is already in %s.' % (L[_rfind(L, n)], sec)
        elif len(L) >= R_MAX_STU: msg = 'A section can have at most %d students.' % R_MAX_STU
        else:
            at = d.get('at')
            if isinstance(at, int) and not isinstance(at, bool) and 0 <= at <= len(L): L.insert(at, n)
            else: L.append(n)
            ok = True; msg = 'Added %s to %s.' % (n, sec)
    elif a == 'del':
        n = str(d.get('name', '')); L = ROSTER[sec]
        if n not in L: msg = 'That student is not in the list.'
        else:
            i = L.index(n); L.pop(i); _rdrop(sec, n); ok = True; undo = {'sec': sec, 'name': n, 'at': i}
            msg = 'Removed %s from %s. Saved results are kept.' % (n, sec)
    elif a == 'sort':
        ROSTER[sec].sort(key=lambda x: x.casefold()); ok = True; msg = 'Sorted %s A to Z.' % sec
    elif a == 'paste':
        raw = [_rname(x) for x in (d.get('names') if isinstance(d.get('names'), list) else [])[:2000]]
        names = []; seen = set()
        for n in raw:
            if n and n.casefold() not in seen: seen.add(n.casefold()); names.append(n)
        L = ROSTER[sec]
        if not names: msg = 'No names found in the pasted text.'
        elif d.get('mode') == 'replace':
            names = names[:R_MAX_STU]; keep = {x.casefold() for x in names}; spell = {x.casefold(): x for x in L}   # an existing student keeps the exact spelling, so saved results still match
            gone = [x for x in L if x.casefold() not in keep]
            for x in gone: _rdrop(sec, x)
            L[:] = [spell.get(n.casefold(), n) for n in names]; ok = True
            msg = 'The list of %s is now %d students%s.' % (sec, len(L), (' (%d removed)' % len(gone)) if gone else '')
        else:
            have = {x.casefold() for x in L}; new = [n for n in names if n.casefold() not in have][:max(0, R_MAX_STU - len(L))]
            L.extend(new); ok = bool(new)
            msg = ('Added %d to %s' % (len(new), sec) if new else 'Nobody added: every name was already in %s' % sec) + ('; skipped %d already in the list.' % (len(names) - len(new)) if new and len(names) > len(new) else '.')
    if ok: save(); t_save(); TB.clear(); _SP.clear()   # _SP: the student page is cached with the class list inside it
    return {'sections': {k: list(v) for k, v in ROSTER.items()}, 'msg': msg, 'ok': ok, 'sel': sel, 'undo': undo}

def host_action(a, d):
    S = D['slides']
    # students only see a question once the teacher PICKS someone (individual / roster pick) or turns the team auto-questions ON.
    # Browsing slides, generating, adding, toggling or revealing on the dashboard must NOT expose the preset question.
    if a == 'rpick' or a == 'bossstart' or (a == 'tloop' and (bool(d['v']) if 'v' in d else not D.get('tloop'))): D['shown'] = True
    if a in ('goto', 'gen', 'add'): record_round(); D['rp']['show'] = False
    if a == 'add':
        x = blank(d['type'], D['nid']); x['topic'] = d.get('topic') if d.get('topic') in TOPICS else TOPICS[0]
        S.append(x); D['nid'] += 1; D['cur'] = len(S) - 1
    elif a == 'goto': D['cur'] = max(0, min(len(S) - 1, int(d['i'])))
    elif a == 'toggle': D['open'] = not D['open']
    elif a == 'board': D['board'] = not D['board']
    elif a == 'section':
        if d.get('sec') in ROSTER: D['section'] = d['sec']
    elif a == 'shape':
        if d.get('topic') in TOPICS and d.get('v') in SHAPES: D['shape'][d['topic']] = d['v']
    elif a == 'level': D['level'] = lvclean(d.get('v'))
    elif a == 'mix': D['mix'] = [t for t in TOPICS if t in d['v']] if isinstance(d.get('v'), list) else []
    elif a == 'lang': D['lang'] = 'tl' if d.get('v') == 'tl' else 'en'
    elif a == 'rreset':
        ks = set(secs()); D['picked'] = [x for x in D['picked'] if x[0] not in ks]
    elif a == 'rpick':
        if boss_live():
            D['notice'] = '\U0001F3F0 Class battle is running. Stop it (Class button) to pick individual students.'; D['noticet'] = time.time(); save(); return
        ks = secs(); done = {tuple(x) for x in D['picked']}
        cnt = D['rcount']; out = lambda k, n: is_out(skey(k, n))
        gone = lambda k, n: any(n in t_['m'] for t_ in D['tleft'].get(k, []))   # member of a team that already left the room
        lv_ = live_set() if D.get('onlyon') else None
        absent = lambda k, n: lv_ is not None and (k, n) not in lv_   # option: skip students who are not online
        pool = [(k, n) for k in ks for n in ROSTER[k] if (k, n) not in done and not out(k, n) and not gone(k, n) and not absent(k, n)]
        if not any(not out(k, n) for k in ks for n in ROSTER[k]):
            D['notice'] = '🏁 Everyone in this section already reached the goal of %d correct.' % D['goal']; D['noticet'] = time.time(); save(); return
        if not any(not out(k, n) and not gone(k, n) for k in ks for n in ROSTER[k]):
            D['notice'] = '\U0001F6AA Everyone left in this section has already reached the goal or left the room.'; D['noticet'] = time.time(); save(); return
        if not any(not out(k, n) and not gone(k, n) and not absent(k, n) for k in ks for n in ROSTER[k]):
            D['notice'] = '\U0001F440 No present students to pick from (nobody in this section is online).'; D['noticet'] = time.time(); save(); return
        elig = sum(1 for k in ks for n in ROSTER[k] if not out(k, n) and not gone(k, n) and not absent(k, n))
        # FAIR CYCLE RULE: everyone eligible is picked once before anyone is picked again.
        # 1) draw from students not yet picked in this cycle; 2) when they run out, start a NEW cycle and
        # fill the remaining slots from everyone else. Only picks made in the new cycle count toward it.
        random.shuffle(pool); chosen = pool[:cnt]; wrap = len(chosen) < min(cnt, elig)
        carry = list(chosen)   # picked in the cycle that just finished
        newcycle = []
        if wrap:
            D['picked'] = [x for x in D['picked'] if x[0] not in set(ks)]
            rest = [(k, n) for k in ks for n in ROSTER[k] if (k, n) not in set(chosen) and not out(k, n) and not gone(k, n) and not absent(k, n)]
            random.shuffle(rest); newcycle = rest[:cnt - len(chosen)]; chosen += newcycle
        archive_round()
        commit_round()
        c0 = cur(); t0 = pick_topic(d.get('topic') if d.get('topic') in TOPICS else c0['topic'], D['rp'].get('topic'))
        qlist = None
        if c0.get('auto') or t0 != c0['topic']:   # fresh random question for EACH selected student (teacher-written slides are left alone)
            lv_ = D.get('level', 1); g_ = make(t0, 'pick', lv_); qlist = [(g_['q'], g_['ans'])]
            while len(qlist) < len(chosen):
                x_ = gen(t0, lv_, D['shape'].get(t0, ''))
                for _ in range(8):
                    if x_ not in qlist: break
                    x_ = gen(t0, lv_, D['shape'].get(t0, ''))
                qlist.append(x_)
            g_['ans'] = ''   # the answers live on each student's own card
        for k, n in (newcycle if wrap else chosen): D['picked'].append([k, n])   # on a wrap, the leftovers of the old cycle are not counted again
        D['rp'] = {'n': D['rp']['n'] + 1, 'wrapped': wrap,
                   'picks': [dict({'name': n, 'sec': k, 'ans': '', 'mark': None}, **({'q': qlist[i][0], 'qa': qlist[i][1]} if qlist else {})) for i, (k, n) in enumerate(chosen)],
                   'tstart': 0, 'tdur': D['rtime'], 'tfz': None, 'show': True, 'tok': qtok(cur()), 'topic': t0}
    elif a == 'goal': D['goal'] = max(0, min(50, int(float(d.get('v') or 0)))); check_finished(True)
    elif a == 'goalreset':
        D['ok'] = {}; D['bon'] = {}; D['pen'] = {}; D['back'] = []; D['lfuse'] = {}; D['lastq'] = {}; D['lsn'] += 1   # new session: the cumulative totals are kept
        for q in D['rp'].get('picks', []): q['mark'] = None
        check_finished(True)
    elif a == 'liferesetall': D['life'] = {}; D['att'] = {}; D['sk'] = {}; D['skerr'] = {}   # teacher wiped ALL cumulative totals
    elif a == 'noisy':
        # a noisy student automatically loses 1 point (never below 0) from their correct-answer count
        nm_ = str(d.get('name', ''))[:40]
        if nm_:
            k_ = skey(str(d.get('sec', ''))[:40], nm_); before = okcount(k_); hit = before > 0
            D['noisy'][k_] = D['noisy'].get(k_, 0) + 1
            if hit: D['pen'][k_] = D['pen'].get(k_, 0) + 1
            D['nlog'] = (D['nlog'] + [[k_, hit]])[-50:]
            D['notice'] = ('🔇 −1 point: %s (now %d)' % (nm_, before - 1)) if hit else ('🔇 %s marked noisy (already at 0 points)' % nm_)
            D['noticet'] = time.time(); check_finished(True); save()
    elif a == 'noisyundo':
        if D['nlog']:
            e_ = D['nlog'].pop(); k_ = nkey(e_); hit = e_[1] if not isinstance(e_, str) else False
            if D['noisy'].get(k_, 0) > 1: D['noisy'][k_] -= 1
            else: D['noisy'].pop(k_, None)
            if hit:
                if D['pen'].get(k_, 0) > 1: D['pen'][k_] -= 1
                else: D['pen'].pop(k_, None)
            D['notice'] = '↩ Undid noisy mark: %s' % split_key(k_)[1]; D['noticet'] = time.time(); check_finished(True); save()
    elif a == 'tgoal':
        D['tgoal'] = max(0, min(500, int(float(d.get('v') or 0)))); TB.clear()
        D['tann'] = [skey(sec_, t_['id']) for sec_ in D['teams'] for t_ in tboard(sec_) if t_['done']]   # teams already above a new goal are not announced
    elif a == 'trelease':
        # the team reached the goal: take it out of the live team session (its final score is kept in the 'left the room' list)
        sec = D['section']; L_ = D['teams'].get(sec, [])
        t_ = next((x for x in L_ if x['id'] == d.get('id')), None); b_ = next((x for x in tboard(sec) if x['id'] == d.get('id')), None)
        if t_ and b_:
            D['tleft'].setdefault(sec, []).append({'id': t_['id'], 'name': t_['name'], 'm': list(t_['m']), 'tot': b_['tot']})
            D['teams'][sec] = [x for x in L_ if x is not t_]; TB.clear()
            D['notice'] = '\U0001F6AA %s can leave the room (final score %d)' % (t_['name'], b_['tot']); D['noticet'] = time.time()
    elif a == 'trestore':
        sec = D['section']; L_ = D['tleft'].get(sec, []); e_ = next((x for x in L_ if x['id'] == d.get('id')), None)
        if e_ and not any(x['id'] == e_['id'] for x in D['teams'].get(sec, [])):
            D['tleft'][sec] = [x for x in L_ if x is not e_]
            if not D['tleft'][sec]: D['tleft'].pop(sec)
            D['teams'].setdefault(sec, []).append({'id': e_['id'], 'name': e_['name'], 'm': list(e_['m'])}); TB.clear()
            D['notice'] = '\u21A9 %s is back in the session' % e_['name']; D['noticet'] = time.time()
    elif a == 'tmode':
        D['tmode'] = bool(d['v']) if 'v' in d else not D['tmode']
        if D['tmode']: boss_off()
        D['mode'] = 'team' if D['tmode'] else 'individual'; check_finished(True)
    elif a == 'mode':
        # three play categories: individual (cold-call picks), team, class (boss battle)
        m_ = d.get('v')
        if m_ in ('individual', 'team', 'class'):
            if m_ != 'class': boss_off()
            D['tloop'] = False
            D['tmode'] = (m_ == 'team'); D['mode'] = m_; TB.clear(); check_finished(True)
    elif a == 'bossstart': boss_start(d); D['mode'] = 'class'; D['tmode'] = False; TB.clear(); check_finished(True)
    elif a == 'bossstop':
        if D.get('boss'): D['boss']['st'] = 'idle'
        D['tloop'] = False
    elif a == 'tloop':
        D['tloop'] = bool(d['v']) if 'v' in d else not D['tloop']
        if D['tloop'] and not D['teams'].get(D['section']):
            host_action('tmake', {'size': d.get('size') or 4, 'online': d.get('online')})   # no teams yet: make them first so the game can really start
            if not D['teams'].get(D['section']): D['tloop'] = False; save(); return          # not enough students: notice already set by tmake
            D['tloop'] = True   # tmake calls boss_off(), which switches the loop off: turn it back on
        if D['tloop']:
            D['tmode'] = True; D['mode'] = 'team'; boss_off(); D['tloop'] = True; D['rp']['show'] = False
            make(pick_topic(d.get('topic') if d.get('topic') in TOPICS else cur()['topic']), 'num', D.get('level', 1))
    elif a == 'tmake':
        sec = D['section']; size = max(2, min(8, int(float(d.get('size') or 4)))); names = list(ROSTER[sec])
        if d.get('online'):
            live = {D['names'].get(c) for c, t_ in SEEN.items() if time.time() - t_ < 8 and D['secs'].get(c) == sec}
            names = [n for n in names if n in live]
        if len(names) < 2:
            D['notice'] = '👥 Not enough students to make teams.'; D['noticet'] = time.time(); save(); return
        random.shuffle(names); k_ = min(len(names), max(1, int(len(names) / size + 0.5)))
        grp = [[] for _ in range(k_)]
        for i_, n_ in enumerate(names): grp[i_ % k_].append(n_)   # balanced: sizes differ by at most 1
        tn = TNAMES[:]; random.shuffle(tn); tclean(sec)
        D['teams'][sec] = [{'id': 't%d' % (i_ + 1), 'name': ('%s %s' % tn[i_]) if i_ < len(tn) else '👥 Team %d' % (i_ + 1), 'm': sorted(g_)} for i_, g_ in enumerate(grp)]
        D['tmode'] = True; D['mode'] = 'team'; boss_off(); D['notice'] = '👥 %d teams ready for %s' % (k_, sec); D['noticet'] = time.time(); check_finished(True)
    elif a == 'tclear': D['teams'].pop(D['section'], None); tclean(D['section']); check_finished(True)
    elif a == 'tdel':
        # remove one team for good - works for a live team AND for a team that already left the room (session done)
        sec = D['section']; tid = d.get('id'); key = skey(sec, tid)
        for dk in ('teams', 'tleft'):
            D[dk][sec] = [x for x in D[dk].get(sec, []) if x['id'] != tid]
            if not D[dk][sec]: D[dk].pop(sec, None)
        D['tadj'].pop(key, None); D['tlog'] = [e for e in D['tlog'] if e[0] != key]
        for x in D['thist']:
            if sec in x['s']:
                x['s'][sec].pop(tid, None)
                if not x['s'][sec]: x['s'].pop(sec)
        D['thist'] = [x for x in D['thist'] if x['s']]
        TB.clear(); check_finished(True)
    elif a == 'tadj':
        # teacher adds / deducts points for a whole team (a team can never drop below 0)
        sec = D['section']; t_ = next((x for x in D['teams'].get(sec, []) if x['id'] == d.get('id')), None)
        if t_:
            dl = max(-50, min(50, int(float(d.get('v') or 0)))); key = skey(sec, t_['id']); old = D['tadj'].get(key, 0)
            raw = sum(okcount(skey(sec, n)) for n in t_['m'])
            new = max(old + dl, min(old, -raw)) if dl < 0 else old + dl; dl = new - old
            if dl:
                D['tadj'][key] = new; D['tlog'] = (D['tlog'] + [[key, dl, t_['name']]])[-50:]
                D['notice'] = '👥 %s%d points: %s' % ('+' if dl > 0 else '−', abs(dl), t_['name'])
            else: D['notice'] = '👥 %s is already at 0 points' % t_['name']
            D['noticet'] = time.time()
    elif a == 'tundo':
        if D['tlog']:
            key, dl, nm_ = D['tlog'].pop(); D['tadj'][key] = D['tadj'].get(key, 0) - dl
            if not D['tadj'][key]: D['tadj'].pop(key)
            D['notice'] = '↩ Undid %+d for %s' % (dl, nm_); D['noticet'] = time.time()
    elif a == 'trename':
        t_ = next((x for x in D['teams'].get(D['section'], []) if x['id'] == d.get('id')), None); nm_ = str(d.get('name', '')).strip()[:30]
        if t_ and nm_: t_['name'] = nm_
    elif a == 'tmove':
        sec = D['section']; nm_ = str(d.get('name', ''))
        if nm_ in ROSTER.get(sec, []):
            to = next((x for x in D['teams'].get(sec, []) if x['id'] == d.get('to')), None)
            if to:
                for t_ in D['teams'][sec]:
                    if nm_ in t_['m']: t_['m'].remove(nm_)
                to['m'].append(nm_); to['m'].sort()
                D['teams'][sec] = [x for x in D['teams'][sec] if x['m']]   # a team that lost its last member disappears
    elif a == 'treset':
        # new game: team scores back to 0 (members' correct counts + teacher points + round history) for this section
        sec = D['section']
        for t_ in D['teams'].get(sec, []):
            for n_ in t_['m']: D['ok'].pop(skey(sec, n_), None); D['pen'].pop(skey(sec, n_), None); D['bon'].pop(skey(sec, n_), None)
        tclean(sec)
        for q in D['rp'].get('picks', []):
            if q['sec'] == sec: q['mark'] = None
        check_finished(True)
    elif a == 'onlyon': D['onlyon'] = bool(d['v']) if 'v' in d else not D.get('onlyon', False)
    elif a == 'rcount': D['rcount'] = max(1, min(13, int(float(d.get('v') or 1))))   # up to 13 students at once
    elif a == 'rtime':
        try: v = max(0, min(600, int(float(d.get('v') or 0))))
        except Exception: v = 30
        D['rtime'] = v; p = D['rp']
        if d.get('start') and p.get('picks'):
            p.update(tstart=(time.time() + dec_for(p)) if v else 0, tdur=v, tfz=None, fin=None)
            for q in p['picks']: q['mark'] = None
        elif not p.get('tstart') and p.get('tfz') is None: p['tdur'] = v
    elif a == 'rstart':
        if D['rtime']:
            D['rp'].update(tstart=time.time() + dec_for(D['rp']), tdur=D['rtime'], tfz=None, fin=None)
            if not d.get('auto'):
                for q in D['rp']['picks']: q['mark'] = None
    elif a in ('rans', 'rmark'):
        p = D['rp']
        try: q = p['picks'][int(d.get('i', 0))]
        except Exception: q = None
        if q is not None:
            if a == 'rans':
                q['ans'] = str(d.get('v', ''))[:80]
                if d.get('check') and q['ans'].strip():
                    sl = pkq(cur(), q)
                    if sl.get('ans'): q['mark'] = 'ok' if correct(sl, q['ans'].strip()) else 'no'
            else:
                m = d.get('m') if d.get('m') in ('ok', 'no') else None
                q['mark'] = None if q.get('mark') == m else m
            if p['picks'] and all(x['mark'] for x in p['picks']): rfreeze()
    elif a == 'lfundo':
        # teacher cancels the lifeline of one selected student: it is refunded and the student answers again
        try: q = D['rp']['picks'][int(d.get('i', 0))]
        except Exception: q = None
        if q and q.get('lf'):
            u = D['lfuse'].get(skey(q['sec'], q['name']), {}); kd = q['lf']['k']
            if u.get(kd, 0) > 0: u[kd] -= 1
            q.pop('lf'); q['ans'] = ''; q['mark'] = None
            D['notice'] = '↩ Lifeline cancelled for %s' % q['name']; D['noticet'] = time.time()
    elif a == 'back':
        # toggle: a student who reached the goal goes back into the picker list (or leaves again)
        k = skey(str(d.get('sec', '')), str(d.get('name', '')))
        if k in D['back']: D['back'].remove(k)
        elif reached(k): D['back'].append(k)
        check_finished(True)
    elif a == 'backall':
        ks = all_reached()
        if ks and all(k in D['back'] for k in ks): D['back'] = [k for k in D['back'] if k not in ks]
        else: D['back'] = sorted(set(D['back']) | set(ks))
        check_finished(True)
    elif a == 'rpause':
        p = D['rp']
        if p.get('tstart'): rfreeze()
        elif p.get('tfz') is not None and p.get('tdur') and not p.get('fin'):
            p['tstart'] = time.time() - (p['tdur'] - p['tfz']); p['tfz'] = None
    elif a == 'rtreset':
        p = D['rp']
        if p.get('picks'):
            p.update(tstart=0, tfz=None, fin=None, tdur=D['rtime'])
            for q in p['picks']: q['mark'] = None
    elif a == 'rclear': D['rp']['show'] = False
    elif a == 'rwait':
        # "Pick a student" opens Settings first: every student back on the waiting screen, nothing picked yet
        if not boss_live() and not (D.get('tloop') and D.get('tmode')):
            record_round(); D['rp']['show'] = False; D['shown'] = False
    elif a == 'rfinish': finish_round()
    elif a == 'gen':
        t = pick_topic(d.get('topic') if d.get('topic') in TOPICS else TOPICS[0], cur()['topic'] if S else None); k = 'num' if d.get('kind') == 'num' else 'pick'
        D['level'] = lvclean(d.get('level'))
        make(t, k, D['level'])
    elif a == 'del' and len(S) > 1:
        S[:] = [x for x in S if x['id'] != d['id']]; D['cur'] = min(D['cur'], len(S) - 1)
    else:
        sl = next((x for x in S if x['id'] == d.get('id')), None)
        if not sl: return
        if a == 'edit':
            if 'q' in d:
                if str(d['q'])[:200] != sl['q']: sl['var'] = False   # teacher rewrote it: same question for everyone
                sl['q'] = str(d['q'])[:200]
            if 'ans' in d:
                if str(d['ans'])[:80] != sl.get('ans'): sl['var'] = False
                sl['ans'] = str(d['ans'])[:80]
            if d.get('topic') in TOPICS: sl['topic'] = d['topic']
            if 'time' in d: sl['time'] = max(0, min(600, int(float(d['time'] or 0))))
            if 'opts' in d and sl['type'] in ('mc', 'quiz'):
                sl['opts'] = [str(o)[:80] for o in d['opts'] if str(o).strip()]
                sl['votes'] = {k: v for k, v in sl['votes'].items() if k in sl['opts']}
        elif a == 'reset':
            sl.update(votes={}, words={}, answers=[], start=0, rev=False, by={}, turn='', log=[]); voters.pop(sl['id'], None)
        elif a == 'start': sl['start'] = time.time(); sl['rev'] = False
        elif a == 'reveal': reveal(sl)
        elif a == 'pick' and sl['type'] == 'pick':
            c = d.get('cid') or ''
            if not c:
                on = [k for k, t in SEEN.items() if time.time() - t < 8]
                pool = [k for k in on if k not in {x['c'] for x in sl['log']}] or on
                c = random.choice(pool) if pool else ''
            if c: sl['turn'] = c; sl['log'].append({'c': c, 'n': D['names'].get(c, '?'), 'a': None, 'm': None})
        elif a == 'mark':
            c = d.get('cid'); e = next((x for x in reversed(sl['log']) if x['c'] == c), None)
            if e:
                if e['m'] == 'ok': D['scores'][c] = D['scores'].get(c, 0) - 1000
                e['m'] = None if d.get('m') == e['m'] else d.get('m')
                if e['m'] == 'ok': D['scores'][c] = D['scores'].get(c, 0) + 1000
                credit(ckey(c), qtok(sl) + '#%s' % sl['log'].index(e), e['m'] == 'ok')
                attempt(ckey(c), qtok(sl) + '#%s' % sl['log'].index(e), e['m'] is not None, None, sl['q'])
        elif a == 'clear': sl['turn'] = ''
    save()

if not D['slides']:
    host_action('gen', {'topic': TOPICS[0], 'kind': 'num', 'level': 1})
    save()
if '--keep' not in sys.argv:
    # every normal start is a NEW class session: forget who finished / left the room, points, noisy marks and team scores.
    # (cumulative totals in D['life'] are kept.)  Run with --keep to resume after a crash in the middle of a lesson.
    D['ok'] = {}; D['bon'] = {}; D['back'] = []; D['lfuse'] = {}; D['pen'] = {}; D['noisy'] = {}; D['nlog'] = []; D['scores'] = {}; D['lastq'] = {}
    D['boss'] = None; D['tleft'] = {}; D['tann'] = []; D['tadj'] = {}; D['tlog'] = []; D['thist'] = []; D['picked'] = []; D['announced'] = None; D['ann'] = {}
    D['rp'].update(show=False, picks=[], tstart=0, tfz=None, fin=None)
    save()
D['mode'] = 'class' if boss_live() else ('team' if D.get('tmode') else 'individual')   # play category: individual / team / class (boss battle)
D['shown'] = False   # every server start: students joining see an EMPTY screen until the teacher starts a question

def vote(d):
    s = cur(); cid = str(d.get('cid', ''))[:40]; v = str(d.get('v', '')).strip()[:200]
    nm = str(d.get('name', '')).strip()[:40]
    sc0 = str(d.get('sec', ''))[:40]
    if cid and nm and not is_roster(sc0, nm): return   # roster names only, no nicknames
    if cid and nm and claimed_other(sc0, nm, cid): return
    if cid and nm: D['names'][cid] = nm; D['secs'][cid] = sc0; SEEN[cid] = time.time(); claim(sc0, nm, cid)
    b_ = D.get('boss')
    if boss_live() and b_.get('pace'):   # paced battle: grade at once, damage the boss, next question
        if v and cid in D['names'] and D['open'] and d.get('id') == s['id'] and not is_out(ckey(cid)): bp_answer(b_, cid, v, d.get('gv'))
        return
    ri = ridx(cid)
    if ri == -1:
        hi = hidx(cid)
        if hi is not None and v and d.get('id') == s['id'] and rtimer_ok() and canvote(s) and not D['rp'].get('fin'):
            if not D['rp']['picks'][hi].get('mark'): rrec(hi, s, v); save()
        return
    if ri is not None and ri >= 0 and D['rp']['picks'][ri].get('lf'): return   # already handed the question over
    if ri is not None and not rtimer_ok(): return
    if not canvote(s) or d.get('id') != s['id'] or not cid or not v: return
    if cid in D['names'] and (is_out(ckey(cid)) or (D.get('tmode') and left_team(ckey(cid)))): return
    if s['type'] == 'pick':
        if ri is not None and ri >= 0:   # selected from the roster: answer from their own device
            if not D['rp']['picks'][ri].get('mark'): rrec(ri, s, v); save()
            return
        e = next((x for x in reversed(s['log']) if x['c'] == cid), None)
        if s['turn'] == cid and e and e['a'] is None:
            e['a'] = v
            if s.get('ans'):
                e['m'] = 'ok' if correct(s, v) else 'no'
                if e['m'] == 'ok': D['scores'][cid] = D['scores'].get(cid, 0) + 1000; credit(ckey(cid), qtok(s) + '#%s' % s['log'].index(e), True)
                attempt(ckey(cid), qtok(s) + '#%s' % s['log'].index(e), True, None, s['q'])
            save()
        return
    if isq(s):
        if cid in s['by'] or (s['type'] == 'quiz' and v not in s['opts']): return
        lf = left(s); s['by'][cid] = [v, int(1000 if (lf is None or not SPEED_WEIGHTED) else 500 + 500 * lf / s['time'])]
        if s['type'] == 'quiz': s['votes'][v] = s['votes'].get(v, 0) + 1
        else: k = v.lower().replace(' ', ''); s['words'][k] = s['words'].get(k, 0) + 1
        rrec(ri, s, v); save(); return
    vs = voters.setdefault(s['id'], {})
    if s['type'] in ('mc', 'scale'):
        if v not in (s['opts'] if s['type'] == 'mc' else list('12345')): return
        old = vs.get(cid)
        if old: s['votes'][old] = max(0, s['votes'].get(old, 1) - 1)
        s['votes'][v] = s['votes'].get(v, 0) + 1; vs[cid] = v
    else:
        if vs.get(cid, 0) >= 3: return
        vs[cid] = vs.get(cid, 0) + 1
        if s['type'] == 'cloud': w = v.lower()[:40]; s['words'][w] = s['words'].get(w, 0) + 1
        else: s['answers'].append(v)
    rrec(ri, s, v); save()

def logout_cid(d):
    # a student pressed Log out: free the name at once so they can join from another device
    cid = str(d.get('cid', ''))[:40]
    if not cid: return
    for k in [k for k, c in CLAIM.items() if c == cid]: del CLAIM[k]
    SEEN.pop(cid, None)
def set_profile(d):
    cid = str(d.get('cid', ''))[:40]; nm = str(d.get('name', '')).strip()[:40]; sc = str(d.get('sec', ''))[:40]
    if not (cid and is_roster(sc, nm)) or claimed_other(sc, nm, cid): return
    p = d.get('p') if isinstance(d.get('p'), dict) else {}; o = {}
    if isinstance(p.get('av'), str) and len(p['av']) <= 12: o['av'] = p['av']
    if isinstance(p.get('th'), int) and not isinstance(p.get('th'), bool) and 0 <= p['th'] < 40: o['th'] = p['th']
    if isinstance(p.get('mo'), str): o['mo'] = p['mo'].strip()[:60]
    if not o: return
    k = skey(sc, nm); D['prof'][k] = dict(D['prof'].get(k, {}), **o); save()

class Srv(ThreadingHTTPServer):
    request_queue_size = 256   # the default is 5: with 30 phones connecting together the rest were dropped and retried a second later
    daemon_threads = True

def make_server(port, host='0.0.0.0'):
    return Srv((host, port), H)

_SP = []
def student_page():
    # the student page is built (and gzipped) once, not once per phone: 50 phones opening it together cost almost nothing
    if not _SP:
        raw = STUDENT.replace('/*ROSTER*/null', json.dumps(ROSTER, ensure_ascii=False)).encode('utf-8')
        c = zlib.compressobj(6, zlib.DEFLATED, 31); _SP.append((raw, c.compress(raw) + c.flush()))
    return _SP[0]

class H(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'      # keep-alive: a phone reuses one connection instead of opening a new one for every poll and every submit
    timeout = 60                       # a dead / sleeping phone releases its server thread after 60 s
    disable_nagle_algorithm = True     # small replies leave at once (no 40 ms wait)
    wbufsize = 65536                   # headers + body go out in one packet burst
    def log_message(self, *a): pass
    def _out(self, b, ct, enc=None, code=200):
        self.send_response(code)
        self.send_header('Content-Type', ct + '; charset=utf-8'); self.send_header('Content-Length', str(len(b)))
        if enc: self.send_header('Content-Encoding', enc); self.send_header('Vary', 'Accept-Encoding')
        self.send_header('Cache-Control', 'no-store'); self.end_headers(); self.wfile.write(b)
    def send(self, body, ct='application/json'): self._out(body.encode('utf-8'), ct)
    def _fail(self):
        # an error inside a handler must still answer, otherwise the phone waits until its own timeout and the answer looks lost
        try: self._out(b'{}', 'application/json', code=500)
        except Exception: self.close_connection = True
    def do_GET(self):
        try: self._get()
        except (BrokenPipeError, ConnectionResetError, TimeoutError): self.close_connection = True
        except Exception: self._fail()
    def do_POST(self):
        try: self._post()
        except (BrokenPipeError, ConnectionResetError, TimeoutError): self.close_connection = True
        except Exception: self._fail()
    def _get(self):
        u = urlparse(self.path); q = parse_qs(u.query)
        if u.path == '/':
            raw, gz = student_page()
            if 'gzip' in self.headers.get('Accept-Encoding', ''): self._out(gz, 'text/html', 'gzip')
            else: self._out(raw, 'text/html')
        elif u.path == '/host': self.send(HOST if keyok(q.get('key', [''])[0]) else LOGIN, 'text/html')
        elif u.path == '/api/check': self.send(json.dumps({'ok': keyok(q.get('key', [''])[0])}))
        elif u.path == '/api/life':
            if not keyok(q.get('key', [''])[0]): self.send_error(403); return
            with lock: self.send(json.dumps({'topics': TOPICS, 'life': {k: {n: life(skey(k, n)) for n in ROSTER[k]} for k in ROSTER}, 'att': {k: {n: life_att(skey(k, n)) for n in ROSTER[k]} for k in ROSTER}}))
        elif u.path == '/api/mastery':
            if not keyok(q.get('key', [''])[0]): self.send_error(403); return
            with lock: self.send(json.dumps({'err': D['err'], 'lab': ERR_LABEL, 'acc': {k: sec_acc(k) for k in ROSTER}, 'topics': TOPICS, 'lsn': D['lsn'], 'm': {k: {n: mastery_of(skey(k, n)) for n in ROSTER[k]} for k in ROSTER}}))
        elif u.path == '/api/skills':
            if not keyok(q.get('key', [''])[0]): self.send_error(403); return
            with lock: self.send(json.dumps({'skills': SKILLS, 'lab': ERR_LABEL, 'lsn': D['lsn'], 'm': {k: {n: skills_of(skey(k, n)) for n in ROSTER[k]} for k in ROSTER}, 'tests': {k: t_skill_sec(k) for k in ROSTER}}))
        elif u.path == '/api/state':
            cid = q.get('cid', [''])[0]; nm = q.get('name', [''])[0].strip()[:40]
            legacy = bool(cid) and 'v' not in q   # a student page opened before this server start (older code, no version marker)
            with lock:
                if legacy:
                    r = state(False, '')
                    r['slide'] = dict(r['slide'], q='🔄 The session was restarted. Please refresh this page to join again.', type='open', opts=[], rev=False, turn='', log=[], votes={}, words={}, answers=[])
                    r.update(open=False, wait=False, role='all', me=None, picked=[], yours=False, mygoal={'n': 0, 'got': 0, 'out': False})
                    self.send(json.dumps(r)); return
                dup = False; sc0 = q.get('sec', [''])[0][:40]
                if cid and nm and is_roster(sc0, nm):
                    if claimed_other(sc0, nm, cid): dup = True   # another device already joined with this name
                    else: D['names'][cid] = nm; D['secs'][cid] = sc0; SEEN[cid] = time.time(); claim(sc0, nm, cid)
                r = state(keyok(q.get('key', [''])[0]), '' if dup else cid); r['dup'] = dup
                if dup: r['taken'] = state(False, cid)['taken']
                self.send(json.dumps(r))
        else: self.send_error(404)
    def login(self, d):
        ip = self.client_address[0]; now = time.time()
        with lock: f = FAILS.get(ip, [0, 0])
        if now < f[1]: self.send(json.dumps({'ok': False, 'wait': int(f[1] - now) + 1})); return
        ok = pin_ok(d.get('pin', ''))
        with lock:
            f = FAILS.get(ip, [0, 0])
            if ok: FAILS.pop(ip, None)
            else:
                f[0] += 1
                if f[0] >= 5: f = [0, time.time() + 60]   # 5 wrong tries = locked out for 60 s
                FAILS[ip] = f
        if ok: self.send(json.dumps({'ok': True, 'key': KEY})); return
        w = max(0, int(f[1] - time.time()) + 1) if f[1] > time.time() else 0
        self.send(json.dumps({'ok': False, 'left': 0 if w else 5 - f[0], 'wait': w}))
    def _post(self):
        try: d = json.loads(self.rfile.read(int(self.headers.get('Content-Length', 0))) or '{}')
        except Exception: d = {}
        if not isinstance(d, dict): d = {}
        if self.path == '/api/login': self.login(d); return
        if self.path in ('/api/pdf', '/api/pdf/student'):   # locked A4 PDF; the student route needs no key (it only formats text the student already sees)
            stu = self.path.endswith('/student')
            if not stu and not keyok(d.get('key')): self._out(b'{}', 'application/json', code=403); return
            cols = [_pdfclean(c) for c in (d.get('cols') or [])][:30]
            rows = [x for x in (_pdfrow(r) for r in (d.get('rows') or [])[:(500 if stu else 6000)] if isinstance(r, (str, list, dict))) if x is not None]
            self._out(make_pdf(_pdfclean(d.get('title', ''))[:120], _pdfclean(d.get('sub', ''))[:160], cols, rows, [x for x in (d.get('w') or []) if isinstance(x, (int, float))]), 'application/pdf'); return
        if self.path == '/api/t/savepdf':
            if not keyok(d.get('key')): self._out(b'{}', 'application/json', code=403); return
            with lock: ok = t_save_pdf(d)
            self.send(json.dumps({'ok': ok})); return
        if self.path == '/api/roster':   # Roster tab: sections and students
            if not keyok(d.get('key')): self._out(b'{}', 'application/json', code=403); return
            with lock: r = roster_action(d)
            self.send(json.dumps(r)); return
        with lock:
            if self.path == '/api/vote':
                rid = str(d.get('rid', ''))[:24]; rk = (str(d.get('cid', ''))[:40], rid)
                if d.get('cv') == 2 and not (rid and rk in RIDS):   # ignore votes from stale pages and retries that were already applied
                    vote(d); TB.clear()
                    if rid:
                        if len(RIDS) > 20000: RIDS.clear()
                        RIDS.add(rk)
            elif self.path == '/api/profile':
                set_profile(d)
            elif self.path == '/api/logout':
                logout_cid(d); TB.clear()
            elif self.path == '/api/lifeline':
                lifeline(d); TB.clear()
            elif self.path == '/api/host' and keyok(d.get('key', '')):
                try: host_action(d.get('action'), d); TB.clear()
                except Exception: pass
        self.send('{}')

COMMON = r"""
const $=i=>document.getElementById(i);const PAL=['#6366f1','#ec4899','#f59e0b','#10b981','#06b6d4','#a855f7','#ef4444','#84cc16'];
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
/* ===== person avatars: code = '@' + 7 digits (gender, skin, hairstyle, hair colour, eye colour, outfit colour, extra) ===== */
const AV={sk:['#ffdfc4','#f5c9a1','#e0ac7c','#c68642','#8d5524','#5c3a21'],hc:['#1f1a17','#5b3a24','#c0572a','#e8c05a','#b8bcc4','#ec4899','#3b82f6'],ec:['#6b3e1f','#1f1f2b','#2f7fd8','#2e9d57','#a8742f'],oc:['#ef4444','#f97316','#eab308','#22c55e','#3b82f6','#8b5cf6','#ec4899'],hs:['Short','Spiky','Curly','Long','Ponytail','Bun']};
const AVDEF='@0101040';
function avP(c){const d=String(c||AVDEF).slice(1).split('').map(Number),n=(i,m)=>{const v=d[i];return v>=0&&v<m?v:0};return{g:n(0,2),sk:n(1,6),hs:n(2,6),hc:n(3,7),ec:n(4,5),oc:n(5,7),ac:n(6,3)}}
function avMake(o){return '@'+[o.g,o.sk,o.hs,o.hc,o.ec,o.oc,o.ac].join('')}
function avSvg(c,m,ov){const p=Object.assign(avP(c),ov||{}),sk=AV.sk[p.sk],hc=AV.hc[p.hc],oc=AV.oc[p.oc],ec=AV.ec[p.ec],g=p.g,hs=p.hs,dk='#2d2a4a',cap=p.ac==2;
 let b='',f='';
 if(hs==3)b+=`<path d="M29 30Q27 8 50 8Q73 8 71 30L73 74Q50 80 27 74Z" fill="${hc}"/>`;
 if(hs==4)b+=`<path d="M64 24Q88 22 82 54Q80 64 74 52Q78 38 64 34Z" fill="${hc}"/>`;
 if(hs==5&&!cap)b+=`<circle cx="50" cy="8" r="8" fill="${hc}"/>`;
 if(hs==1)f+=`<path d="M31 30L33 14L40 22L45 9L51 21L58 9L61 22L67 14L69 30Q66 22 50 21Q34 22 31 30Z" fill="${hc}"/>`;
 else if(hs==2)f+=[[34,22,8],[42,15,9],[52,13,9],[62,16,9],[67,25,8],[31,31,6],[69,31,6]].map(a=>`<circle cx="${a[0]}" cy="${a[1]}" r="${a[2]}" fill="${hc}"/>`).join('');
 else f+=`<path d="M31 34Q29 11 50 10Q71 11 69 34Q64 21 50 22Q36 21 31 34Z" fill="${hc}"/>`;
 const arms=[20,68].map(x=>`<rect x="${x}" y="60" width="12" height="36" rx="6" fill="${sk}"/><rect x="${x}" y="58" width="12" height="18" rx="6" fill="${oc}"/><circle cx="${x+6}" cy="98" r="6.5" fill="${sk}"/>`).join('');
 const legs=g?`<rect x="37" y="100" width="10" height="36" rx="5" fill="${sk}"/><rect x="53" y="100" width="10" height="36" rx="5" fill="${sk}"/>`:`<rect x="35" y="98" width="13" height="38" rx="5" fill="#2f3a6b"/><rect x="52" y="98" width="13" height="38" rx="5" fill="#2f3a6b"/>`;
 const shoes=[40,60].map(x=>`<ellipse cx="${x}" cy="140" rx="10" ry="5.5" fill="#fff" stroke="${dk}" stroke-width="2"/>`).join('');
 const torso=g?`<rect x="34" y="56" width="32" height="40" rx="11" fill="${oc}"/><path d="M34 84L66 84L74 110L26 110Z" fill="${oc}" stroke="rgba(0,0,0,.18)" stroke-width="1.5"/>`:`<rect x="32" y="56" width="36" height="46" rx="11" fill="${oc}"/><rect x="32" y="96" width="36" height="4" fill="rgba(0,0,0,.2)"/>`;
 const neck=`<rect x="44" y="48" width="12" height="16" rx="4" fill="${sk}"/><path d="M43 57L50 66L57 57Z" fill="${sk}"/>`;
 const head=`<circle cx="31" cy="37" r="4.2" fill="${sk}"/><circle cx="69" cy="37" r="4.2" fill="${sk}"/><ellipse cx="50" cy="35" rx="19" ry="21" fill="${sk}"/>`;
 const eyes=[43,57].map(x=>`<ellipse cx="${x}" cy="36" rx="4.2" ry="4.8" fill="#fff"/><circle cx="${x}" cy="36.5" r="3" fill="${ec}"/><circle cx="${x}" cy="36.5" r="1.4" fill="#111"/><circle cx="${x+1.2}" cy="35.2" r="1" fill="#fff"/>`).join('');
 const brows=`<path d="M38.5 29.5Q43 26.5 47.5 29" stroke="${hc}" stroke-width="2" fill="none" stroke-linecap="round"/><path d="M52.5 29Q57 26.5 61.5 29.5" stroke="${hc}" stroke-width="2" fill="none" stroke-linecap="round"/>`;
 const lash=g?`<path d="M38.8 34L36.6 32.4M61.2 34L63.4 32.4" stroke="#222" stroke-width="1.5" stroke-linecap="round"/>`:'';
 const face=`<circle cx="37.5" cy="44" r="3.6" fill="#ff6b81" opacity=".28"/><circle cx="62.5" cy="44" r="3.6" fill="#ff6b81" opacity=".28"/>${eyes}${brows}${lash}<path d="M49.5 38.5Q52.5 43 49 43" stroke="rgba(0,0,0,.25)" stroke-width="1.4" fill="none" stroke-linecap="round"/><path d="M43.5 47Q50 53.5 56.5 47" stroke="#8a2f3a" stroke-width="2" fill="none" stroke-linecap="round"/>`;
 const gl=p.ac==1?`<circle cx="43" cy="36" r="6.8" fill="rgba(255,255,255,.22)" stroke="#222" stroke-width="1.6"/><circle cx="57" cy="36" r="6.8" fill="rgba(255,255,255,.22)" stroke="#222" stroke-width="1.6"/><path d="M49.8 35.5Q50 34.5 50.2 35.5M36.2 35L31.5 34M63.8 35L68.5 34" stroke="#222" stroke-width="1.6" fill="none"/>`:'';
 const cp=cap?`<path d="M30 27Q30 6 50 6Q70 6 70 27Z" fill="${oc}"/><rect x="27" y="25" width="48" height="5.5" rx="2.7" fill="${oc}" stroke="rgba(0,0,0,.22)" stroke-width="1"/>`:'';
 const vb=m=='f'?'10 0 80 148':'17 0 66 70';
 return `<svg class="avs" viewBox="${vb}" xmlns="http://www.w3.org/2000/svg">${b}${arms}${legs}${shoes}${torso}${neck}${head}${f}${face}${gl}${cp}</svg>`}
const avh=(a,m)=>a&&a[0]=='@'?avSvg(a,m||'h'):esc(a||'');
const avi=a=>a?(a[0]=='@'?'<span class="avi">'+avSvg(a,'h')+'</span>':esc(a)+' '):'';
(function(){try{const st=document.createElement('style');st.textContent='.avs{display:block;width:100%;height:100%}.avi{display:inline-block;width:2.6em;height:2.6em;border-radius:50%;overflow:hidden;vertical-align:middle;margin-right:.4em;background:rgba(124,58,237,.18)}';document.head.appendChild(st)}catch(e){}})();
function mx(s){return esc(s).replace(/sqrt\(/g,'√(').replace(/\^(-?\d+|n)/g,(m,e)=>[...e].map(c=>c=='-'?'⁻':c=='n'?'ⁿ':'⁰¹²³⁴⁵⁶⁷⁸⁹'[c]).join('')).replace(/\bpi\b/g,'π').replace(/&lt;=/g,'≤').replace(/&gt;=/g,'≥').replace(/!=/g,'≠').replace(/\+-/g,'±')}
const bar=(l,v,t,c)=>'<div class="bar"><div class="n">'+l+'</div><div class="t"><div class="f" style="width:'+(t?v/t*100:0)+'%;background:'+c+'"></div></div><div class="v">'+v+'</div></div>';
const board=T=>(T.length?T.map((t,i)=>bar((i+1)+'. '+avi(t.a)+esc(t.n),t.s,T[0].s,PAL[i%PAL.length])).join(''):'<p class="mute">No scores yet. Reveal a quiz answer first.</p>');
function confetti(n){n=n||120;const C=['#f43f5e','#f59e0b','#22c55e','#06b6d4','#6366f1','#ec4899','#fde047'];
 for(let i=0;i<n;i++){const e=document.createElement('i'),z=6+Math.random()*9;
  e.style.cssText='position:fixed;top:-3vh;left:'+Math.random()*100+'vw;width:'+z+'px;height:'+z*1.6+'px;background:'+C[i%C.length]+';z-index:10001;pointer-events:none;border-radius:2px';
  document.body.appendChild(e);
  e.animate([{transform:'translate(0,0) rotate(0deg)',opacity:1},{transform:'translate('+((Math.random()-.5)*30)+'vw,108vh) rotate('+(360+Math.random()*720)+'deg)',opacity:.9}],{duration:2200+Math.random()*2200,delay:Math.random()*700,easing:'cubic-bezier(.2,.6,.4,1)',fill:'forwards'}).onfinish=()=>e.remove()}}
let TS=null,T0=0;function tmr(st){TS=st;T0=Date.now()}
let BS=null,BT0=0,BN=-1;
/* ===== boss character: drawn SVG per boss, reacts to hits / heals / low HP / win / loss ===== */
const BL={head:[['none','None'],['horns','Horns'],['ears','Pointy ears'],['spikes','Spikes'],['crown','Crown'],['helmet','Helmet'],['tophat','Top hat'],['party','Party hat'],['viking','Viking helmet'],['pirate','Pirate hat'],['wizard','Wizard hat'],['chef','Chef hat'],['bunny','Bunny ears'],['halo','Halo'],['antenna','Antenna']],eyes:[['angry','Angry'],['round','Round'],['sleepy','Sleepy'],['cyclops','One big eye'],['hearts','Heart eyes'],['stars','Star eyes'],['dizzy','Dizzy spirals'],['cat','Cat eyes'],['robot','Robot eyes'],['wink','Wink'],['three','Three eyes']],mouth:[['grin','Grin'],['fangs','Fangs'],['smile','Smile'],['tongue','Tongue out']],face:[['none','None'],['baron','Monocle + mustache'],['glasses','Glasses'],['eyepatch','Eye patch'],['stache','Mustache'],['shades','Sunglasses'],['mask','Bandit mask'],['clown','Clown nose'],['scar','Scar']],neck:[['none','None'],['bowtie','Bow tie'],['cape','Cape'],['badge','Gold badge']],legs:[['feet','Feet'],['tent','Tentacles']]};
const BK={'Count Dracula-Zero':{body:'#7c3aed',line:'#3b0764',eyec:'#111111',mouthc:'#2b0a0a',hc:'#7c3aed',sym:'0',head:'ears',eyes:'angry',mouth:'fangs',face:'none',legs:'feet'},
'The Fraction Dragon':{body:'#16a34a',line:'#14532d',eyec:'#111111',mouthc:'#2b0a0a',hc:'#facc15',sym:'½',head:'crown',eyes:'angry',mouth:'grin',face:'none',legs:'feet'},
'Lord Negatron':{body:'#475569',line:'#0f172a',eyec:'#ef4444',mouthc:'#2b0a0a',hc:'#fde68a',sym:'−',head:'horns',eyes:'angry',mouth:'grin',face:'none',legs:'feet'},
'Sir Divides-a-Lot':{body:'#64748b',line:'#1e293b',eyec:'#111111',mouthc:'#2b0a0a',hc:'#cbd5e1',sym:'÷',head:'helmet',eyes:'angry',mouth:'grin',face:'none',legs:'feet'},
'The Integer Kraken':{body:'#0d9488',line:'#134e4a',eyec:'#111111',mouthc:'#2b0a0a',hc:'#fde68a',sym:'±',head:'none',eyes:'angry',mouth:'grin',face:'none',legs:'tent'},
'Baron Von Remainder':{body:'#b91c1c',line:'#450a0a',eyec:'#111111',mouthc:'#2b0a0a',hc:'#fde68a',sym:'R',head:'horns',eyes:'angry',mouth:'grin',face:'baron',legs:'feet'}};
function bossLook(nm){return Object.assign({neck:'none'},BK[String(nm).replace(/^\S+\s/,'')]||BK['Lord Negatron'])}
function star(cx,cy,r){const p=[];for(let i=0;i<10;i++){const a=-Math.PI/2+i*Math.PI/5,q=i%2?r*.45:r;p.push((cx+q*Math.cos(a)).toFixed(1)+','+(cy+q*Math.sin(a)).toFixed(1))}return p.join(' ')}
function bossSVG(nm,lk){const k=Object.assign(bossLook(nm),lk||{}),c=k.body,d=k.line,hc=k.hc,mc=k.mouthc,st='stroke="'+d+'" stroke-width="5" stroke-linejoin="round"',cy=k.eyes=='cyclops';
 let hd='';
 if(k.head=='horns')hd='<path d="M46 66 L30 10 L80 50Z M154 66 L170 10 L120 50Z" fill="'+hc+'" '+st+'/>';
 if(k.head=='ears')hd='<path d="M38 84 L18 26 L74 58Z M162 84 L182 26 L126 58Z" fill="'+hc+'" '+st+'/>';
 if(k.head=='spikes')hd='<path d="M66 62 L78 14 L94 56Z M88 56 L100 2 L112 56Z M106 56 L122 14 L134 62Z" fill="'+hc+'" '+st+'/>';
 if(k.head=='crown')hd='<path d="M56 64 L52 22 L78 44 L100 14 L122 44 L148 22 L144 64Z" fill="'+hc+'" '+st+'/><circle cx="100" cy="44" r="6" fill="#ef4444"/>';
 if(k.head=='tophat')hd='<rect x="62" y="4" width="76" height="52" rx="5" fill="'+hc+'" '+st+'/><rect x="62" y="40" width="76" height="11" fill="#ef4444"/><rect x="38" y="52" width="124" height="14" rx="7" fill="'+hc+'" '+st+'/>';
 if(k.head=='party')hd='<path d="M68 64 L100 0 L132 64Z" fill="'+hc+'" '+st+'/><path d="M80 40 L120 40 M74 54 L126 54" stroke="#fff" stroke-width="5"/><circle cx="100" cy="2" r="9" fill="#f472b6" '+st+'/>';
 if(k.head=='viking')hd='<path d="M48 74 Q14 72 20 30 Q38 54 56 58Z M152 74 Q186 72 180 30 Q162 54 144 58Z" fill="#f1e8c8" '+st+'/><path d="M50 74 Q50 26 100 26 Q150 26 150 74 Q100 62 50 74Z" fill="'+hc+'" '+st+'/><path d="M100 28 L100 64" stroke="'+d+'" stroke-width="5"/>';
 if(k.head=='pirate')hd='<path d="M26 72 Q44 18 100 24 Q156 18 174 72 Q100 54 26 72Z" fill="'+hc+'" '+st+'/><path d="M84 54 L116 32 M116 54 L84 32" stroke="#fff" stroke-width="4" stroke-linecap="round"/><circle cx="100" cy="41" r="9" fill="#fff"/><circle cx="96" cy="40" r="2.2" fill="#111"/><circle cx="104" cy="40" r="2.2" fill="#111"/>';
 if(k.head=='wizard')hd='<ellipse cx="100" cy="70" rx="64" ry="11" fill="'+hc+'" '+st+'/><path d="M58 70 Q78 40 94 2 Q124 34 142 70Z" fill="'+hc+'" '+st+'/><path d="M62 62 Q100 74 138 62 L140 70 Q100 80 60 70Z" fill="#facc15"/><polygon points="'+star(106,36,9)+'" fill="#fde047" stroke="#b45309" stroke-width="1.5"/>';
 if(k.head=='chef')hd='<circle cx="70" cy="34" r="20" fill="'+hc+'" '+st+'/><circle cx="100" cy="22" r="22" fill="'+hc+'" '+st+'/><circle cx="130" cy="34" r="20" fill="'+hc+'" '+st+'/><rect x="68" y="38" width="64" height="30" fill="'+hc+'"/><path d="M68 38 L68 68 L132 68 L132 38" fill="none" stroke="'+d+'" stroke-width="5" stroke-linejoin="round"/>';
 if(k.head=='bunny')hd='<ellipse cx="68" cy="22" rx="15" ry="38" transform="rotate(-10 68 22)" fill="'+hc+'" '+st+'/><ellipse cx="132" cy="22" rx="15" ry="38" transform="rotate(10 132 22)" fill="'+hc+'" '+st+'/><ellipse cx="68" cy="24" rx="7" ry="26" transform="rotate(-10 68 24)" fill="#f9a8d4"/><ellipse cx="132" cy="24" rx="7" ry="26" transform="rotate(10 132 24)" fill="#f9a8d4"/>';
 if(k.head=='halo')hd='<ellipse cx="100" cy="30" rx="36" ry="10" fill="none" stroke="'+d+'" stroke-width="13"/><ellipse cx="100" cy="30" rx="36" ry="10" fill="none" stroke="'+hc+'" stroke-width="7"/>';
 if(k.head=='antenna')hd='<path d="M100 62 L100 22" stroke="'+d+'" stroke-width="6" stroke-linecap="round"/><circle cx="100" cy="14" r="11" fill="'+hc+'" '+st+'/><circle cx="96" cy="10" r="3" fill="#fff" opacity=".7"/>';
 const helmet=k.head=='helmet'?'<path d="M32 92 Q32 22 100 22 Q168 22 168 92 L148 84 Q100 70 52 84Z" fill="'+hc+'" '+st+'/><path d="M100 22 L100 4" stroke="#ef4444" stroke-width="9" stroke-linecap="round"/>':'';
 const legs=k.legs=='tent'?'<path d="M40 186 Q22 228 54 224 Q72 220 64 196Z M82 198 Q72 236 100 230 Q118 226 114 198Z M136 196 Q130 228 150 228 Q178 224 160 186Z" fill="'+c+'" '+st+'/>':'<ellipse cx="66" cy="214" rx="26" ry="14" fill="'+d+'"/><ellipse cx="134" cy="214" rx="26" ry="14" fill="'+d+'"/>';
 const brows=k.eyes!='angry'||k.head=='helmet'?'':(cy?'<path d="M58 60 L100 72 L142 60" fill="none" stroke="'+d+'" stroke-width="9" stroke-linecap="round" stroke-linejoin="round"/>':'<path d="M48 64 L90 82 M152 64 L110 82" stroke="'+d+'" stroke-width="9" stroke-linecap="round"/>');
 const E=cy?[[100,92,30,13]]:k.eyes=='three'?[[72,94,18,8],[128,94,18,8],[100,66,12,5]]:[[72,94,19,8],[128,94,19,8]];
 const one=(q,i)=>{const x=q[0],y=q[1],r=q[2],t=k.eyes,w='<circle cx="'+x+'" cy="'+y+'" r="'+r+'" fill="#fff" '+st+'/>';
  if(t=='hearts')return w+'<path d="M'+x+' '+(y+11)+' C'+(x-20)+' '+(y-2)+' '+(x-9)+' '+(y-17)+' '+x+' '+(y-6)+' C'+(x+9)+' '+(y-17)+' '+(x+20)+' '+(y-2)+' '+x+' '+(y+11)+'Z" fill="#ef4444"/>';
  if(t=='stars')return w+'<polygon points="'+star(x,y+1,r-3)+'" fill="#f59e0b" stroke="#b45309" stroke-width="1.5"/>';
  if(t=='dizzy')return w+'<path d="M'+x+' '+y+' a3 3 0 0 1 6 0 a6 6 0 0 1 -12 0 a9 9 0 0 1 18 0 a12 12 0 0 1 -24 0" fill="none" stroke="'+k.eyec+'" stroke-width="3" stroke-linecap="round"/>';
  if(t=='cat')return '<circle cx="'+x+'" cy="'+y+'" r="'+r+'" fill="#fde047" '+st+'/><ellipse cx="'+x+'" cy="'+y+'" rx="4" ry="'+(r-3)+'" fill="'+k.eyec+'"/>';
  if(t=='robot')return '<rect x="'+(x-r)+'" y="'+(y-r*.8)+'" width="'+(2*r)+'" height="'+(1.6*r)+'" rx="5" fill="#0f172a" '+st+'/><rect x="'+(x-r+5)+'" y="'+(y-r*.8+5)+'" width="'+(2*r-10)+'" height="'+(1.6*r-10)+'" rx="3" fill="#22d3ee"/><path d="M'+(x-r+8)+' '+y+' L'+(x+r-8)+' '+y+'" stroke="#0f172a" stroke-width="3"/>';
  if(t=='wink'&&i==1)return '<path d="M'+(x-r)+' '+(y+4)+' Q'+x+' '+(y-16)+' '+(x+r)+' '+(y+4)+'" fill="none" stroke="'+d+'" stroke-width="7" stroke-linecap="round"/>';
  return w+'<circle cx="'+(x+(x<100?5:x>100?-5:0))+'" cy="'+(y+4)+'" r="'+q[3]+'" fill="'+k.eyec+'"/><circle cx="'+(x+(x<100?8:x>100?-8:4))+'" cy="'+(y+1)+'" r="3" fill="#fff"/>'};
 const eyes=E.map(one).join('');
 const lids=k.eyes=='sleepy'?E.map(q=>'<path d="M'+(q[0]-q[2])+' '+q[1]+' a'+q[2]+' '+q[2]+' 0 0 1 '+(2*q[2])+' 0Z" fill="'+c+'" '+st+'/>').join(''):'';
 const xs=cy?'M82 74 L118 110 M118 74 L82 110':'M60 82 L84 106 M84 82 L60 106 M116 82 L140 106 M140 82 L116 106';
 const teeth=k.mouth=='fangs'?'<path d="M74 130 L82 156 L94 134Z M106 134 L118 156 L126 130Z" fill="#fff" stroke="#000" stroke-width="1.5"/>':k.mouth=='smile'?'':'<path d="M78 131 L85 146 L93 136Z M107 136 L115 146 L122 131Z" fill="#fff"/>';
 const mouth=k.mouth=='smile'?'<path d="M72 128 Q100 162 128 128Z" fill="'+mc+'" '+st+'/>':'<path d="M68 128 Q100 164 132 128 Q100 138 68 128Z" fill="'+mc+'" '+st+'/>'+(k.mouth=='tongue'?'<path d="M90 140 Q100 170 114 142Z" fill="#f87171" stroke="'+d+'" stroke-width="3"/>':'');
 const R=cy?[[100,92,34]]:[[72,94,24],[128,94,24]];
 let fx='';
 if(k.face=='baron'||k.face=='stache')fx+='<path d="M62 124 Q82 110 100 122 Q118 110 138 124 Q118 132 100 128 Q82 132 62 124Z" fill="'+d+'"/>';
 if(k.face=='baron'){const q=R[R.length-1];fx+='<circle cx="'+q[0]+'" cy="'+q[1]+'" r="'+q[2]+'" fill="none" stroke="#fbbf24" stroke-width="4"/><path d="M'+(q[0]+q[2]-4)+' '+(q[1]+16)+' Q'+(q[0]+q[2]+10)+' '+(q[1]+42)+' '+(q[0]+q[2]+2)+' '+(q[1]+60)+'" fill="none" stroke="#fbbf24" stroke-width="3"/>'}
 if(k.face=='glasses')fx+=R.map(q=>'<circle cx="'+q[0]+'" cy="'+q[1]+'" r="'+q[2]+'" fill="#fff" fill-opacity=".18" stroke="#111" stroke-width="5"/>').join('')+(cy?'':'<path d="M96 92 L104 92" stroke="#111" stroke-width="5"/>');
 if(k.face=='eyepatch'&&!cy)fx+='<path d="M40 70 L104 112" stroke="#111" stroke-width="5"/><ellipse cx="72" cy="94" rx="23" ry="21" fill="#111"/>';
 if(k.face=='shades')fx+=R.map(q=>'<rect x="'+(q[0]-q[2]-3)+'" y="'+(q[1]-q[2]+5)+'" width="'+(2*q[2]+6)+'" height="'+(1.5*q[2])+'" rx="9" fill="#111"/>').join('')+(cy?'':'<path d="M96 92 L104 92" stroke="#111" stroke-width="5"/>')+R.map(q=>'<path d="M'+(q[0]-q[2]+4)+' '+(q[1]-q[2]+13)+' l9 -5" stroke="#fff" stroke-opacity=".5" stroke-width="4" stroke-linecap="round"/>').join('');
 if(k.face=='mask'&&!cy)fx+='<path fill-rule="evenodd" d="M48 82 Q100 46 152 82 L164 118 Q100 124 36 118Z M51 94 a21 21 0 1 0 42 0 a21 21 0 1 0 -42 0Z M107 94 a21 21 0 1 0 42 0 a21 21 0 1 0 -42 0Z" fill="#111"/>';
 if(k.face=='clown')fx+='<circle cx="100" cy="116" r="12" fill="#ef4444" stroke="'+d+'" stroke-width="3"/><circle cx="96" cy="112" r="3.5" fill="#fff" opacity=".7"/>';
 if(k.face=='scar')fx+='<path d="M62 70 L92 120" stroke="#7f1d1d" stroke-width="5" stroke-linecap="round"/><path d="M68 92 L82 85 M75 106 L89 99" stroke="#7f1d1d" stroke-width="3" stroke-linecap="round"/>';
 const nb=k.neck=='cape'?'<path d="M38 100 Q-4 170 6 232 Q54 214 100 222 Q146 214 194 232 Q204 170 162 100Z" fill="'+hc+'" '+st+'/>':'';
 const nf=k.neck=='bowtie'?'<path d="M100 168 L76 156 L76 180Z M100 168 L124 156 L124 180Z" fill="'+hc+'" '+st+'/><circle cx="100" cy="168" r="6" fill="'+hc+'" '+st+'/>':k.neck=='badge'?'<path d="M54 180 L48 206 L62 198 L76 206 L70 180Z" fill="#ef4444" stroke="#7f1d1d" stroke-width="2"/><circle cx="62" cy="170" r="14" fill="#facc15" stroke="#b45309" stroke-width="3"/><polygon points="'+star(62,170,9)+'" fill="#fff7ed" stroke="#b45309" stroke-width="1.2"/>':'';
 return '<svg viewBox="0 0 200 240" xmlns="http://www.w3.org/2000/svg"><ellipse cx="100" cy="228" rx="70" ry="9" fill="#000" opacity=".3"/>'+nb+legs
 +'<ellipse cx="30" cy="150" rx="16" ry="32" transform="rotate(22 30 150)" fill="'+c+'" '+st+'/><ellipse cx="170" cy="150" rx="16" ry="32" transform="rotate(-22 170 150)" fill="'+c+'" '+st+'/>'
 +'<ellipse cx="100" cy="135" rx="70" ry="78" fill="'+c+'" '+st+'/>'+hd+helmet
 +'<circle cx="100" cy="188" r="25" fill="#fff" fill-opacity=".22"/><text x="100" y="202" text-anchor="middle" font-size="38" font-weight="900" font-family="Georgia,serif" fill="'+d+'">'+esc(String(k.sym==null?'':k.sym).slice(0,2))+'</text>'
 +nf+'<g class="eo">'+eyes+lids+'</g><g class="ex" stroke="'+d+'" stroke-width="7" stroke-linecap="round"><path d="'+xs+'"/></g>'+brows
 +'<g class="mi">'+mouth+teeth+'</g>'
 +'<g class="mh"><ellipse cx="100" cy="140" rx="18" ry="21" fill="'+mc+'" '+st+'/><ellipse cx="100" cy="152" rx="11" ry="7" fill="#f87171"/></g>'
 +'<path class="md" d="M70 142 Q85 128 100 142 Q115 156 130 142" fill="none" stroke="'+d+'" stroke-width="6" stroke-linecap="round"/>'+fx
 +'<g class="bd"><rect x="118" y="46" width="34" height="13" rx="3" transform="rotate(-22 135 52)" fill="#fde68a" stroke="#b45309" stroke-width="2"/></g><g class="ag"><text x="128" y="74" font-size="40">💢</text></g></svg>'}
const BSCSS=`.bsw{position:relative}.bsw .bz{width:100%;height:100%;transform-origin:50% 100%;animation:bsbob 2.4s ease-in-out infinite}.bsw svg{width:100%;height:100%;overflow:visible}
.bsw .ex,.bsw .mh,.bsw .md,.bsw .bd,.bsw .ag{display:none}.bsw.enr .ag{display:block;animation:bsag .5s ease-in-out infinite alternate}.bsw.hit .mi,.bsw.won .mi{display:none}.bsw.hit .mh{display:block}.bsw.won .eo{display:none}.bsw.won .ex,.bsw.won .md{display:block}.bsw.low .bd{display:block}
.bsw.low .bz{animation-duration:.8s}.bsw.enr .bz{animation-duration:.6s;filter:drop-shadow(0 0 12px #ef4444) saturate(1.5)}.bsw.hit .bz{animation:bshit .55s}.bsw.heal .bz{animation:bsheal .75s}.bsw.lost .bz{animation:bslaugh .5s ease-in-out infinite}
.bsw.won .bz{animation:none;transform:rotate(-80deg) translate(14%,6%);filter:grayscale(1) brightness(.75);transition:transform 1s,filter 1s}
@keyframes bsbob{0%,100%{transform:translateY(0) scale(1,1)}50%{transform:translateY(-3%) scale(1.02,.98)}}
@keyframes bshit{0%{transform:none;filter:brightness(2.4) saturate(.2)}20%{transform:translateX(-9%) rotate(-6deg)}45%{transform:translateX(8%) rotate(4deg);filter:none}70%{transform:translateX(-4%)}100%{transform:none}}
@keyframes bsheal{0%,100%{filter:none}40%{filter:drop-shadow(0 0 20px #4ade80) brightness(1.3)}}
@keyframes bslaugh{0%,100%{transform:translateY(0)}50%{transform:translateY(-7%) scale(1.04)}}
.hpb{position:relative;height:clamp(28px,4.4vh,46px);border-radius:99px;background:rgba(0,0,0,.55);border:3px solid rgba(255,255,255,.35);overflow:hidden}
.hpb::after{content:"";position:absolute;inset:0;pointer-events:none;background-image:repeating-linear-gradient(90deg,transparent 0,transparent calc(var(--sw,10%) - 2px),rgba(0,0,0,.55) calc(var(--sw,10%) - 2px),rgba(0,0,0,.55) var(--sw,10%))}
.hpf{height:100%;transition:width .6s;background:linear-gradient(90deg,#dc2626,#f97316 60%,#facc15);box-shadow:0 0 18px rgba(249,115,22,.7)}
#bossbar .bbs{display:none}body.proj #bossbar .bbc{display:none}body.proj #bossbar .bbs{display:block}
body.proj #bossbar{left:2vw!important;right:auto!important;top:11vh!important;bottom:auto!important;transform:none!important;width:31vw!important;padding:1.6vh 1.4vw!important;text-align:center}
@keyframes bsag{to{transform:scale(1.25) rotate(8deg);transform-origin:130px 60px}}@keyframes bsdbl{to{transform:scale(1.08)}}
#bossbar .bdb{display:none;font-weight:900;color:#1e1b4b;background:linear-gradient(90deg,#fde047,#f97316);border-radius:99px;padding:2px 14px;margin:4px auto;width:max-content;max-width:100%;animation:bsdbl .5s ease-in-out infinite alternate}#bossbar .bdb.on{display:block}
#bossbar .bsy{font-style:italic;color:#fde68a;min-height:1.3em;font-size:clamp(14px,1.5vw,24px);transition:opacity .6s}
#bossbar.enr{border-color:#ef4444;box-shadow:0 0 34px rgba(239,68,68,.8)}#bossbar.dbl{border-color:#facc15}
#bossbar .bn{font-size:clamp(18px,2vw,34px);font-weight:900}#bossbar .bsw.big{width:min(24vw,34vh);aspect-ratio:200/240;margin:1vh auto}
#bossbar .hpl{display:flex;justify-content:space-between;font-size:clamp(16px,1.8vw,30px);margin-bottom:.6vh}#bossbar .nd{font-size:clamp(14px,1.5vw,24px);margin-top:1vh;color:#fde68a;min-height:1.4em}#bossbar .bm{font-size:clamp(13px,1.3vw,20px);margin-top:.6vh;min-height:1.4em}
body.proj.hasboss #app{padding-left:34vw;max-width:none}
/* ===== boss-only projector screen (paced battle): only the big boss + HP + the Dashboard button ===== */
body.proj.bossonly #app,body.proj.bossonly #hint,body.proj.bossonly #cnt,body.proj.bossonly #fab,body.proj.bossonly #gear,body.proj.bossonly #nzb,body.proj.bossonly #cmb,body.proj.bossonly #tmb,body.proj.bossonly #tstrip,body.proj.bossonly #turn,body.proj.bossonly #fstrip,body.proj.bossonly #pickbar,body.proj.bossonly #who,body.proj.bossonly #toast{display:none!important}
body.proj.bossonly #bossbar{left:50%!important;right:auto!important;top:52%!important;bottom:auto!important;transform:translate(-50%,-50%)!important;width:min(90vw,1200px)!important;max-height:90vh;padding:2vh 3vw!important;text-align:center;border-width:4px}
body.proj.bossonly #bossbar .bn{font-size:clamp(28px,4.4vw,72px)}
body.proj.bossonly #bossbar .bsw.big{width:min(36vw,38vh);margin:1vh auto 2vh}
body.proj.bossonly #bossbar .hpl{font-size:clamp(26px,3.6vw,64px);margin-bottom:1vh}
body.proj.bossonly #bossbar .hpb{height:clamp(36px,7vh,80px)}
body.proj.bossonly #bossbar .nd{font-size:clamp(20px,2.4vw,40px);margin-top:1.4vh}
body.proj.bossonly #bossbar .bm{font-size:clamp(16px,1.8vw,30px)}
/* ===== full-screen boss (teacher panel): button or key F; only the big boss + HP bar fill the screen ===== */
#bfsb{position:fixed;right:14px;top:14px;z-index:80;font-weight:800;padding:9px 16px;border-radius:99px;background:rgba(255,255,255,.2);color:#fff;border:1px solid rgba(255,255,255,.5);backdrop-filter:blur(6px);cursor:pointer}
#bfsb:hover{background:rgba(255,255,255,.35)}
body.bossfs{background:radial-gradient(circle at 50% 40%,#3b1030,#0a081e)!important;overflow:hidden}
body.bossfs>*:not(#bossbar):not(#bfsb):not(i):not(script):not(style){display:none!important}
body.bossfs #bossbar{display:block!important;left:50%!important;right:auto!important;top:50%!important;bottom:auto!important;transform:translate(-50%,-50%)!important;width:96vw!important;max-width:none!important;max-height:96vh;padding:2vh 3vw!important;text-align:center;border-width:5px;box-sizing:border-box}
body.bossfs #bossbar .bbc{display:none!important}body.bossfs #bossbar .bbs{display:block!important}
body.bossfs #bossbar .bn{font-size:clamp(32px,5vw,96px)}
body.bossfs #bossbar .bsw.big{width:min(40vw,46vh);margin:1vh auto 2vh}
body.bossfs #bossbar .hpl{font-size:clamp(28px,4vw,76px);margin-bottom:1vh}
body.bossfs #bossbar .hpb{height:clamp(40px,8vh,96px)}
body.bossfs #bossbar .nd{font-size:clamp(22px,2.8vw,48px);margin-top:1.4vh}
body.bossfs #bossbar .bm{font-size:clamp(18px,2.2vw,38px)}
body.bossfs #bossbar .bsy{font-size:clamp(18px,2vw,34px)}
body.bossfs #bfsb{opacity:.45}body.bossfs #bfsb:hover{opacity:1}
/* student phone: a slim boss bar so it never covers the answer box */
#bossbar.stu{width:min(400px,94vw)!important;padding:4px 10px!important;border-radius:12px!important;bottom:6px!important;box-shadow:0 4px 14px rgba(0,0,0,.45)!important}
#bossbar.stu .bsw{width:30px!important;height:36px!important}
#bossbar.stu #bsn{font-size:12px!important;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-width:0}#bossbar.stu #bst{font-size:12px!important;white-space:nowrap}
#bossbar.stu .hpb{height:9px!important;margin:3px 0!important;border-width:2px!important}
#bossbar.stu #bsm{font-size:11px!important;min-height:0!important;line-height:1.25}
#bossbar.stu .bsy{font-size:11px!important;min-height:0!important}
#bossbar.stu .bdb{font-size:11px!important;padding:0 10px!important;margin:2px auto!important}
body.stuboss{padding-bottom:0!important}
/* the boss is shown on the teacher's projected screen: no boss bar on the student phones */
#bossbar.stu{display:none!important}`;
function bstate(c){document.querySelectorAll('.bsw').forEach(w=>{w.classList.remove('hit','heal');void w.offsetWidth;w.classList.add(c);setTimeout(()=>w.classList.remove(c),c=='hit'?550:750)})}
function bpop(t,col){document.querySelectorAll('.bsw').forEach(w=>{if(!w.offsetParent)return;const p=document.createElement('span');p.textContent=t;p.style.cssText='position:absolute;left:'+(25+Math.random()*40)+'%;top:18%;font:900 clamp(22px,3.4vw,56px) system-ui;color:'+col+';text-shadow:0 2px 0 #000,0 0 14px '+col+';pointer-events:none;z-index:3';w.appendChild(p);p.animate([{transform:'translateY(0) scale(.6)',opacity:0},{transform:'translateY(-30%) scale(1.2)',opacity:1,offset:.25},{transform:'translateY(-130%) scale(1)',opacity:0}],{duration:1400,easing:'ease-out'}).onfinish=()=>p.remove()})}
function bfly(ev){
 const tg=[].slice.call(document.querySelectorAll('.bsw')).find(w=>w.offsetParent);if(!tg)return;
 const r=tg.getBoundingClientRect(),W=innerWidth,H=innerHeight,ok=!!ev.ok,sz=Math.max(46,Math.min(90,W*.05));
 const e=document.createElement('div');e.style.cssText='position:fixed;left:0;top:0;z-index:80;pointer-events:none;display:flex;flex-direction:column;align-items:center;gap:4px;will-change:transform';
 e.innerHTML='<div class="fi" style="font-size:'+sz+'px;line-height:1;filter:drop-shadow(0 4px 6px rgba(0,0,0,.6))">'+(ok?'🪨':'🩹')+'</div><div style="font:800 clamp(16px,2vw,34px) system-ui;color:#fff;white-space:nowrap;padding:2px 14px;border-radius:99px;background:'+(ok?'rgba(220,38,38,.88)':'rgba(22,163,74,.9)')+';border:2px solid rgba(255,255,255,.7);text-shadow:0 2px 0 rgba(0,0,0,.4)">'+(ev.a?esc(ev.a)+' ':'')+esc(ev.who||'?')+'</div>';
 document.body.appendChild(e);
 const w=e.offsetWidth,h=e.offsetHeight,L=Math.random()<.5,
  x0=(L?W*(.03+Math.random()*.12):W*(.85+Math.random()*.1))-w/2,y0=H*(.25+Math.random()*.55)-h/2,
  x1=r.left+r.width*(.3+Math.random()*.4)-w/2,y1=r.top+r.height*(.3+Math.random()*.4)-h/2,
  xm=(x0+x1)/2,ym=Math.min(y0,y1)-H*.14,T=(x,y,s)=>'translate('+x+'px,'+y+'px) scale('+s+')';
 e.querySelector('.fi').animate([{transform:'rotate(0deg)'},{transform:'rotate('+(L?540:-540)+'deg)'}],{duration:950,easing:'linear'});
 e.animate([{transform:T(x0,y0,.6),opacity:0},{transform:T(xm,ym,1.1),opacity:1,offset:.45},{transform:T(x1,y1,.9),opacity:1}],{duration:950,easing:'ease-in',fill:'forwards'}).onfinish=()=>{e.remove();
  bstate(ok?'hit':'heal');bpop(ok?'\u2212'+ev.dmg:'+'+ev.heal,ok?'#fb7185':'#4ade80')}}
function bossFS(on){const b=document.body,was=b.classList.contains('bossfs');if(on===undefined)on=!was;
 b.classList.toggle('bossfs',on);const x=$('bfsb');if(x)x.textContent=on?'\u2715 Exit full screen':'\u26F6 Full screen boss';
 try{if(on&&!document.fullscreenElement)document.documentElement.requestFullscreen().catch(()=>{});if(!on&&document.fullscreenElement)document.exitFullscreen().catch(()=>{})}catch(e){}}
document.addEventListener('fullscreenchange',()=>{if(!document.fullscreenElement&&document.body.classList.contains('bossfs'))bossFS(false)});
document.addEventListener('keydown',e=>{if(!window.HOSTV||!$('bfsb'))return;const t=e.target.tagName;if(t=='INPUT'||t=='TEXTAREA'||t=='SELECT'||e.ctrlKey||e.metaKey||e.altKey)return;if(e.key=='f'||e.key=='F'){e.preventDefault();bossFS()}else if(e.key=='Escape'&&document.body.classList.contains('bossfs'))bossFS(false)});
function bossdraw(b){window.BSP=!!(b&&b.pace&&b.st=='fight');let e=$('bossbar');
 {const pv=window.BPST;window.BPST=b?b.st:null;if(b&&pv==='fight'&&(b.st==='won'||b.st==='lost')){if(b.st==='won'){confetti(240);setTimeout(()=>confetti(140),900)}if(window.onBossEnd)window.onBossEnd(b)}}
 if(!$('bsstyle')){const s=document.createElement('style');s.id='bsstyle';s.textContent=BSCSS;document.head.appendChild(s)}
 document.body.classList.toggle('stuboss',!!(!window.HOSTV&&b&&b.st&&b.st!='idle'));
 document.body.classList.toggle('hasboss',!!(window.HOSTV&&b&&b.st&&b.st!='idle'));
 document.body.classList.toggle('bossonly',!!(window.HOSTV&&b&&b.pace&&b.st&&b.st!='idle'));
 if(!b||b.st=='idle'){if(e)e.remove();{const x=$('bfsb');if(x)x.remove()}if(document.body.classList.contains('bossfs'))bossFS(false);BN=-1;window.BEN=null;return}
 if(!e){e=document.createElement('div');e.id='bossbar';e.style.cssText='position:fixed;left:50%;transform:translateX(-50%);width:min(760px,94vw);z-index:70;padding:10px 16px;border-radius:18px;color:#fff;font-weight:800;background:linear-gradient(135deg,#1e1b4b,#7f1d1d);box-shadow:0 8px 30px rgba(0,0,0,.5);border:2px solid #fca5a5;'+(window.HOSTV?'top:1.5vh':'bottom:8px');
  e.innerHTML='<div class="bbc"><div style="display:flex;align-items:center;gap:10px"><div class="bsw" id="bsa" style="width:54px;height:65px;flex:none"><div class="bz"></div></div><div style="flex:1;min-width:0"><div style="display:flex;justify-content:space-between;gap:10px;font-size:18px"><span id="bsn"></span><span id="bst"></span></div><div class="hpb" style="height:22px;margin:6px 0"><div class="hpf" id="bsf"></div></div><div id="bsm" style="font-size:15px;min-height:20px"></div><div class="bsy" id="bsy"></div><div class="bdb" id="bdb"></div></div></div></div>'
  +'<div class="bbs"><div class="bn" id="bn2"></div><div class="bsw big" id="bsc"><div class="bz"></div></div><div class="hpl"><span id="hp2"></span><span id="bst2"></span></div><div class="hpb"><div class="hpf" id="bsf2"></div></div><div class="nd" id="nd2"></div><div class="bdb" id="bdb2"></div><div class="bsy" id="bsy2"></div><div class="bm" id="bsm2"></div></div>';if(!window.HOSTV)e.classList.add('stu');document.body.appendChild(e)}
 if(window.HOSTV&&!$('bfsb')){const f=document.createElement('button');f.id='bfsb';f.textContent=document.body.classList.contains('bossfs')?'\u2715 Exit full screen':'\u26F6 Full screen boss';f.onclick=()=>bossFS();document.body.appendChild(f)}
 const lkk=b.name+JSON.stringify(b.look||0);if(e.dataset.nm!=lkk){e.dataset.nm=lkk;const g=bossSVG(b.name,b.look);e.querySelectorAll('.bz').forEach(z=>z.innerHTML=g)}
 BS=b;BT0=Date.now();const pc=b.max?Math.round(b.hp/b.max*100):0,lo=b.dmin||10,hi=b.dmax||15,sg=b.max/lo;
 e.style.setProperty('--sw',(sg<=60?100/sg:10)+'%');
 let need='';if(b.st=='fight'&&b.hp>0){const a=Math.ceil(b.hp/hi),z=Math.ceil(b.hp/lo);need=(a==z?a:a+'–'+z)}
 $('bsn').textContent=b.name+'  '+b.hp+' / '+b.max+' HP'+(need?' · ≈'+need+' hits to go':'');$('bn2').textContent=b.name.replace(/^\S+\s/,'');$('hp2').textContent='❤ '+b.hp+' / '+b.max+' HP';
 $('bsf').style.width=pc+'%';$('bsf2').style.width=pc+'%';
 $('nd2').innerHTML=need?'🎯 Needs about <b>'+need+'</b> more correct answers':'';
 let m='';if(b.last&&b.pace)m='⚔ '+avi(b.last.a)+esc(b.last.who||'')+(b.last.ok?' hit the boss for '+b.last.dmg+' HP':' missed. The boss healed +'+b.last.heal+' HP');else if(b.last)m='💥 Last question: −'+b.last.dmg+' HP ('+b.last.ok+' correct)'+(b.last.bad?'  🩹 +'+b.last.heal+' healed ('+b.last.bad+' wrong)':'');
 if(b.st=='won')m='🎉 BOSS DEFEATED! The class wins!'+(b.top.length?'  Top hitters: '+b.top.map(x=>avi(x.a)+esc(x.n)+' ('+x.d+')').join(', '):'');
 if(b.st=='lost')m='💀 Time is up. The boss survived with '+b.hp+' HP. Try again!';
 $('bsm').innerHTML=m;$('bsm2').innerHTML=m;
 document.querySelectorAll('.bsw').forEach(w=>{w.classList.toggle('won',b.st=='won');w.classList.toggle('lost',b.st=='lost');w.classList.toggle('low',b.st=='fight'&&pc<=30);w.classList.toggle('enr',b.st=='fight'&&!!b.enr)});
 e.classList.toggle('enr',b.st=='fight'&&!!b.enr);e.classList.toggle('dbl',b.st=='fight'&&b.dbl>0);window.BDL=b.dbl||0;window.BDT=Date.now();
 if(b.say&&b.say.id!==window.BSID){window.BSID=b.say.id;window.BST=Date.now();window.BSKEEP=(b.say.ev=='won'||b.say.ev=='lost');['bsy','bsy2'].forEach(i=>{const x=$(i);if(x){x.textContent='💬 '+b.say.t;x.style.opacity=1}})}
 if(window.HOSTV&&b.pace&&b.ev){if(window.BID!==b.bid){window.BID=b.bid;window.BEN=null}
  const mx=b.ev.reduce((m,x)=>Math.max(m,x.n),0);
  if(window.BEN==null)window.BEN=mx;else{const fr=b.ev.filter(x=>x.n>window.BEN).sort((p,q)=>p.n-q.n);window.BEN=Math.max(window.BEN,mx);const sh=fr.slice(-10),gp=Math.min(350,3000/Math.max(1,sh.length));sh.forEach((x,i)=>setTimeout(()=>bfly(x),i*gp))}}
 if(b.last&&b.last.n!==BN){if(BN!==-1&&!(window.HOSTV&&b.pace)){const l=b.last;if(l.dmg>0){bstate('hit');bpop('−'+l.dmg,'#fb7185')}if(l.heal>0)setTimeout(()=>{bstate('heal');bpop('+'+l.heal,'#4ade80')},l.dmg>0?650:0)}BN=b.last.n}}
setInterval(()=>{const l=(window.BDL||0)-(Date.now()-(window.BDT||0))/1000,on=!!BS&&BS.st=='fight'&&l>0;['bdb','bdb2'].forEach(i=>{const x=$(i);if(x){x.classList.toggle('on',on);if(on)x.textContent='⚡ DOUBLE DAMAGE! '+Math.ceil(l)+'s'}});
 if(window.BST&&!window.BSKEEP&&Date.now()-window.BST>8000)['bsy','bsy2'].forEach(i=>{const x=$(i);if(x)x.style.opacity=0})},250);
setInterval(()=>{const e=$('bst'),f=$('bst2');if(!e||!BS)return;if(BS.st!='fight'){e.textContent=f.textContent=BS.st=='won'?'🏆':'⌛';return}
 const l=Math.max(0,BS.left-(Date.now()-BT0)/1000);e.textContent=f.textContent='⏱ '+Math.floor(l/60)+':'+String(Math.floor(l%60)).padStart(2,'0')},250);

setInterval(()=>{const e=$('tm');if(!e)return;const st=TS;if(!st||st.left==null||st.slide.rev){e.textContent='';return}
 let l=st.left;if(st.run)l=Math.max(0,l-(Date.now()-T0)/1000);e.textContent='⏱ '+Math.ceil(l)+'s'},200);
function results(s){
 if(window.BSP)return '<p class="mute">⚔ Students answer at their own pace. Watch the boss HP!</p>';
 if((s.type=='quiz'||s.type=='num')&&!s.rev)return '<p class="mute">🔒 '+(window.N||0)+' answered… waiting for the reveal'+(s.var&&s.type=='num'&&window.HOSTV?'<br>🔀 Everyone has different numbers on their own device':'')+'</p>';
 if(s.type=='num'&&s.var&&s.nok!=null)return '<p style="font-size:2em">✅ <b>'+s.nok+' of '+s.nby+'</b> answered correctly</p><p class="mute">Everyone had different numbers, so each answer is checked against that student\'s own question.</p>';
 if(s.type=='mc'||s.type=='scale'||s.type=='quiz'){const L=s.type=='scale'?['1','2','3','4','5']:s.opts;
  const t=L.reduce((a,l)=>a+(s.votes[l]||0),0);
  let r=L.map((l,i)=>bar(mx(l)+(s.rev&&l==s.ans?' ✓':''),s.votes[l]||0,t,s.rev&&s.type=='quiz'?(l==s.ans?'#10b981':'#64748b'):PAL[i%PAL.length])).join('');
  r+='<p class="mute">'+t+' response'+(t==1?'':'s')+(s.type=='scale'&&t?' · average '+(L.reduce((a,l)=>a+l*(s.votes[l]||0),0)/t).toFixed(2):'')+'</p>';return r}
 if(s.type=='num'){const e=Object.entries(s.words).sort((a,b)=>b[1]-a[1]).slice(0,6),t=e.reduce((a,x)=>a+x[1],0);
  return '<p style="font-size:2em">✅ Correct answer: <b>'+mx(s.ans)+'</b></p>'+e.map(([w,c],i)=>bar(esc(w),c,t,PAL[i%PAL.length])).join('')+'<p class="mute">Most common answers. The wrong ones make great discussion!</p>'}
 if(s.type=='pick'){const L=s.log||[],ic=m=>m=='ok'?'✅':m=='no'?'❌':'';
  const c=s.turn?L.filter(x=>x.c==s.turn).pop():null;
  let h=(s.rev&&s.ans?'<p style="font-size:2em">✅ Correct answer: <b>'+mx(s.ans)+'</b></p>':'')+(c?'<div class="spot"><b>'+esc(c.n)+'</b> '+ic(c.m)+(c.a?'<div class="ans">'+mx(c.a)+'</div>':' <span class="mute">is answering…</span>')+'</div>':'');
  const old=L.filter(x=>x!==c&&x.a).slice(-4);
  return h+(old.length?'<p class="mute" style="margin-top:20px">Earlier</p>'+old.map(x=>'<div class="ans"><b>'+esc(x.n)+'</b> '+ic(x.m)+': '+mx(x.a)+'</div>').join(''):'')}
 if(s.type=='cloud'){const e=Object.entries(s.words),m=Math.max(1,...e.map(x=>x[1]));
  return '<div class="cloud">'+(e.sort().map(([w,c])=>'<span style="font-size:'+(16+c/m*48)+'px;font-weight:700;color:hsl('+([...w].reduce((a,ch)=>a+ch.charCodeAt(0)*37,0)%360)+',65%,50%)">'+esc(w)+'</span>').join('')||'<span class="mute">Waiting for words…</span>')+'</div>'}
 return s.answers.map(a=>'<div class="ans">'+esc(a)+'</div>').join('')||'<span class="mute">Waiting for responses…</span>'}
"""
CSS = """<style>:root{--bg:#f4f5f7;--card:#fff;--ink:#1b1d29;--mute:#6b7080;--ac:#4f46e5;--line:#e3e5ea}
@media(prefers-color-scheme:dark){:root{--bg:#14151c;--card:#1e2029;--ink:#f1f2f6;--mute:#9a9eb0;--line:#2e313e}}
*{box-sizing:border-box}body{margin:0;font:16px system-ui,sans-serif;background:var(--bg);color:var(--ink)}
button,input{font:inherit;color:inherit}button{cursor:pointer;border:1px solid var(--line);background:var(--card);padding:8px 14px;border-radius:8px}
button.p{background:var(--ac);color:#fff;border-color:var(--ac)}input{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px 12px;width:100%}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:20px}.mute{color:var(--mute);font-size:14px}
.bar{display:flex;align-items:center;gap:10px;margin:10px 0}.bar .n{width:30%}.bar .t{flex:1;background:var(--line);border-radius:6px;height:34px;overflow:hidden}
.bar .f{height:100%;background:var(--ac);transition:width .4s}.bar .v{width:56px;text-align:right}
.cloud{display:flex;flex-wrap:wrap;gap:6px 18px;justify-content:center;align-items:center;min-height:160px}.ans{padding:10px 14px;background:var(--bg);border-radius:8px;margin:6px 0}#tm{font-size:28px;font-weight:800;color:var(--ac)}.big{font-size:22px;font-weight:700;margin:12px 0}.spot{font-size:1.5em;margin:10px 0}</style>"""

STUDENT = """<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Join</title>""" + CSS + """
<style>body{padding:16px;max-width:560px;margin:auto}h2{margin:0 0 16px}.ch{display:block;width:100%;margin:8px 0;padding:14px;font-size:18px;text-align:left}.ch.on{background:var(--ac);color:#fff}select{width:100%;padding:12px;margin:8px 0;font-size:18px;border-radius:8px;background:var(--card);color:var(--ink);border:1px solid var(--line)}a{color:var(--ac)}</style>
<style>/* ===== vibrant theme ===== */
:root{--bg:#f6f3ff;--card:#fff;--ink:#1e1b3a;--mute:#6f6a94;--ac:#7c3aed;--ac2:#ec4899;--ac3:#06b6d4;--line:#e4defa;--grad:linear-gradient(135deg,#7c3aed 0%,#ec4899 100%);--shadow:0 8px 28px rgba(124,58,237,.14)}
@media(prefers-color-scheme:dark){:root{--bg:#120f2b;--card:#1d1942;--ink:#f5f3ff;--mute:#a9a4d6;--line:#352f69;--shadow:0 8px 28px rgba(0,0,0,.45)}}
body{font-family:Inter,"Segoe UI",system-ui,-apple-system,sans-serif;background:radial-gradient(circle at 0% 0%,rgba(236,72,153,.16),transparent 38%),radial-gradient(circle at 100% 0%,rgba(6,182,212,.16),transparent 40%),radial-gradient(circle at 50% 100%,rgba(124,58,237,.14),transparent 50%),var(--bg);background-attachment:fixed}
button{border-radius:12px;font-weight:600;transition:transform .12s,box-shadow .15s,background .15s,filter .15s}
button:hover{transform:translateY(-2px);box-shadow:0 6px 16px rgba(124,58,237,.25);border-color:var(--ac)}button:active{transform:translateY(0) scale(.97)}
button.p,#tabs button.on{background:var(--grad);border-color:transparent;color:#fff;box-shadow:0 4px 14px rgba(236,72,153,.35)}button.p:hover{filter:brightness(1.1)}
input,select{border-radius:12px;border:2px solid var(--line);transition:border-color .15s,box-shadow .15s}input:focus,select:focus{outline:0;border-color:var(--ac);box-shadow:0 0 0 4px rgba(124,58,237,.18)}
.card{border-radius:20px;border:1px solid var(--line);box-shadow:var(--shadow)}
header{background:var(--grad)!important;color:#fff;border:0!important;box-shadow:0 6px 24px rgba(124,58,237,.35)}header b{font-weight:800;letter-spacing:-.01em}
header button.p{background:#fff;color:#7c3aed;box-shadow:0 4px 14px rgba(0,0,0,.2)}
#tabs button{border-radius:99px;padding:9px 18px;background:var(--card)}
.sl{border-radius:14px;border:2px solid transparent;box-shadow:0 2px 10px rgba(124,58,237,.08);transition:transform .12s,box-shadow .15s}.sl:hover{transform:translateX(3px);box-shadow:0 4px 16px rgba(124,58,237,.2)}
.sl.on{background:linear-gradient(135deg,rgba(124,58,237,.12),rgba(236,72,153,.12));border-color:var(--ac);box-shadow:0 0 0 3px rgba(124,58,237,.2)}
#big{background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;font-size:26px;font-weight:800}
#q{font-weight:800}#tm{background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.bar .t{border-radius:99px;height:38px;background:rgba(124,58,237,.1)}.bar .f{border-radius:99px;background:linear-gradient(90deg,#7c3aed,#ec4899)}
.bar:nth-child(5n+2) .f{background:linear-gradient(90deg,#06b6d4,#3b82f6)}.bar:nth-child(5n+3) .f{background:linear-gradient(90deg,#f59e0b,#ef4444)}
.bar:nth-child(5n+4) .f{background:linear-gradient(90deg,#10b981,#84cc16)}.bar:nth-child(5n+5) .f{background:linear-gradient(90deg,#8b5cf6,#06b6d4)}
.ans{border-radius:14px;border-left:5px solid var(--ac2)}
#bysec details{border-radius:14px;border:2px solid var(--line);background:var(--card);transition:border-color .15s}#bysec details[open],#bysec details:hover{border-color:var(--ac)}
#bysec .bc{background:rgba(16,185,129,.15);padding:2px 12px;border-radius:99px}#bysec .bc.z{background:rgba(124,58,237,.08)}
#fab{background:var(--grad);box-shadow:0 8px 30px rgba(236,72,153,.55);animation:pulse 2.4s ease-in-out infinite}
@keyframes pulse{50%{box-shadow:0 8px 42px rgba(124,58,237,.8);transform:scale(1.04)}}
.ch{border-radius:16px!important;border:2px solid var(--line)!important;background:var(--card)}.ch:hover{border-color:var(--ac)!important}.ch.on{background:var(--grad)!important;border-color:transparent!important;box-shadow:0 6px 18px rgba(236,72,153,.4)}
h2{font-weight:800}
/* projector */
body.proj{background:#1b1147}
body.proj::before{content:"";position:fixed;inset:-25%;z-index:-1;pointer-events:none;filter:blur(70px);opacity:.95;animation:drift 20s ease-in-out infinite alternate;background:radial-gradient(circle at 15% 20%,#ec4899 0,transparent 32%),radial-gradient(circle at 85% 15%,#06b6d4 0,transparent 32%),radial-gradient(circle at 70% 85%,#7c3aed 0,transparent 38%),radial-gradient(circle at 20% 85%,#f59e0b 0,transparent 26%)}
@keyframes drift{to{transform:translate(4%,-3%) rotate(8deg) scale(1.12)}}
body.proj h2{color:#fff;text-shadow:0 4px 40px rgba(0,0,0,.35),0 0 60px rgba(236,72,153,.45)}
body.proj #tm{background:none;-webkit-text-fill-color:#fde047;color:#fde047;text-shadow:0 0 30px rgba(253,224,71,.6)}
body.proj #cnt{background:rgba(255,255,255,.18);border:1px solid rgba(255,255,255,.35);box-shadow:0 6px 24px rgba(0,0,0,.25)}
body.proj .bar .t{background:rgba(255,255,255,.14)}body.proj .bar .f{box-shadow:0 0 30px rgba(255,255,255,.3),0 0 24px rgba(255,255,255,.2) inset}
body.proj .ans{background:rgba(255,255,255,.16);backdrop-filter:blur(6px);border-left-color:#fde047}
body.proj #pickbar button.p,body.proj #rp button.p{background:var(--grad)}
.tc{background:rgba(255,255,255,.12);backdrop-filter:blur(8px);box-shadow:0 8px 30px rgba(0,0,0,.25)}
.tc.ok{box-shadow:0 0 34px rgba(16,185,129,.55)}.tc.no{box-shadow:0 0 34px rgba(239,68,68,.5)}
#tt{text-shadow:0 0 36px rgba(253,224,71,.65)}
#spb button:hover,#spm button:hover{background:var(--grad)}
#rp,#sp{background:rgba(24,12,66,.88)}
.slot.done,#rpn.done{color:#fde047;text-shadow:0 0 50px rgba(253,224,71,.8)}
</style>
<style>/* ===== student polish ===== */
html{-webkit-text-size-adjust:100%}
body{box-sizing:border-box;min-height:100vh;min-height:100dvh;padding:max(16px,env(safe-area-inset-top)) max(16px,env(safe-area-inset-right)) max(20px,env(safe-area-inset-bottom)) max(16px,env(safe-area-inset-left));-webkit-tap-highlight-color:transparent}
body.jn{display:flex;flex-direction:column;justify-content:center;max-width:min(880px,94vw)}body.jn #app{padding:clamp(18px,3vh,40px) clamp(24px,5vw,60px);border-radius:36px}.join .logo{width:clamp(80px,12vh,130px)!important;height:clamp(80px,12vh,130px)!important;border-radius:30px!important;font-size:clamp(40px,6vh,64px)!important;margin-bottom:12px!important}.join h1{font-size:clamp(34px,6vh,60px)!important}.join .sub{font-size:clamp(17px,2.8vh,24px)!important;margin:6px 0 14px!important}.join label{font-size:clamp(14px,2.2vh,19px)!important;margin:clamp(10px,2vh,20px) 6px 8px!important}.join select,.join input{font-size:clamp(20px,3.4vh,30px)!important;padding:clamp(12px,2.2vh,24px) 22px!important;border-radius:20px!important;padding-right:64px!important}.join .row{margin-top:clamp(18px,3vh,32px)!important}.join .row button{font-size:clamp(22px,3.6vh,32px)!important;padding:clamp(14px,2.6vh,26px)!important;border-radius:20px!important}.join .alt{font-size:clamp(15px,2.4vh,21px)!important;margin-top:18px!important}
button{touch-action:manipulation;cursor:pointer}button:disabled{opacity:.55;cursor:not-allowed;transform:none!important;box-shadow:none!important}
#app{padding:24px 22px;animation:rise .4s ease both}
#app>*{animation:fadein .28s ease both}
@keyframes rise{from{opacity:0;transform:translateY(14px)}}
@keyframes fadein{from{opacity:0}}
#app h2{font-size:clamp(22px,6vw,30px);line-height:1.25;margin:0 0 16px}
.mute{line-height:1.45}
#tm:empty,#me:empty{display:none}
#me{text-align:center;padding:8px 14px;border-radius:99px;background:rgba(124,58,237,.1);font-weight:600}
#ti{width:100%;box-sizing:border-box;padding:15px 16px;font-size:18px;margin:8px 0;border-radius:14px;background:var(--card);color:var(--ink)}
.ch{padding:16px 18px!important;font-size:18px;min-height:56px;line-height:1.3}.ch:active{transform:scale(.98)}
.big{line-height:1.3}
/* join screens */
.join{text-align:center}
.join .logo{width:76px;height:76px;margin:0 auto 14px;border-radius:24px;background:var(--grad);display:grid;place-items:center;font-size:38px;box-shadow:0 12px 28px rgba(236,72,153,.4);animation:float 3s ease-in-out infinite}
@keyframes float{50%{transform:translateY(-6px)}}
.join h1{margin:0;font-size:clamp(26px,8vw,34px);font-weight:800;letter-spacing:-.02em;background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.join .sub{margin:6px 0 20px;color:var(--mute);font-size:16px}
.join label{display:block;text-align:left;font-size:12px;font-weight:800;letter-spacing:.08em;text-transform:uppercase;color:var(--mute);margin:16px 4px 6px}
.join select,.join input{width:100%;box-sizing:border-box;margin:0;padding:15px 16px;font-size:18px;border-radius:14px;background-color:var(--card);color:var(--ink);border:2px solid var(--line)}
.join select{-webkit-appearance:none;appearance:none;padding-right:46px;background-repeat:no-repeat;background-position:right 16px center;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='18' height='18' viewBox='0 0 24 24' fill='none' stroke='%237c3aed' stroke-width='3' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M6 9l6 6 6-6'/%3E%3C/svg%3E")}
.join .row{display:flex;margin-top:24px}.join .row button{width:100%;padding:16px;font-size:19px;border-radius:14px}
.join .alt{margin:20px 0 0;font-size:15px}.join .alt a{font-weight:600;text-decoration:none}.join .alt a:hover{text-decoration:underline}
.join .hint{margin:10px 4px 0;font-size:13px;text-align:left}
@media(hover:none){button:hover{transform:none;box-shadow:none}}
@media(min-width:600px){#app{padding:34px 32px}}
.tmc{margin-top:12px;padding:12px 14px;border-radius:16px;background:linear-gradient(135deg,rgba(6,182,212,.16),rgba(124,58,237,.16));border:2px solid var(--line);text-align:center}.tmc .tmn{font-weight:800;font-size:18px}.tmc .tmp{margin:4px 0;font-size:16px}.tmc .tmp b{font-size:22px;color:var(--ac)}.tmc .tmp em{font-style:normal;color:#059669;font-weight:700}.tmc .tmm{font-size:13px;color:var(--mute)}
/* ===== student big / vibrant / personal layout ===== */
:root{--ac3:#06b6d4}
#hdr{display:none}
body.in{max-width:none;margin:0;padding:0;display:flex;flex-direction:column;min-height:100vh;min-height:100dvh;overflow-x:hidden}
body.in::before{content:'';position:fixed;inset:-20%;z-index:-1;pointer-events:none;filter:blur(80px);opacity:.55;animation:drift 22s ease-in-out infinite alternate;background:radial-gradient(circle at 12% 18%,var(--ac2) 0,transparent 30%),radial-gradient(circle at 88% 12%,var(--ac3) 0,transparent 30%),radial-gradient(circle at 75% 88%,var(--ac) 0,transparent 36%),radial-gradient(circle at 18% 85%,#f59e0b 0,transparent 24%)}
body.in #hdr{display:flex;align-items:center;gap:clamp(10px,2vw,22px);flex-wrap:wrap;margin:max(12px,env(safe-area-inset-top)) clamp(12px,3vw,40px) 0;padding:clamp(10px,1.6vw,18px) clamp(14px,2.4vw,28px);border-radius:28px;background:var(--grad);color:#fff;box-shadow:0 10px 34px rgba(0,0,0,.2)}
#hdr .av{overflow:hidden;width:clamp(120px,14vw,210px);height:clamp(120px,14vw,210px);flex:none;border-radius:50%;background:rgba(255,255,255,.25);border:3px solid #fff;display:grid;place-items:center;font-size:clamp(28px,5vw,50px);font-weight:800;color:#fff;padding:0;box-shadow:0 6px 18px rgba(0,0,0,.25)}
#hdr .hn{flex:1;min-width:140px}#hdr .hn b{display:block;font-size:clamp(24px,3.9vw,56px);font-weight:800;line-height:1.1}#hdr .hn span{opacity:.92;font-size:clamp(15px,1.9vw,26px)}
#hdr .chips{display:flex;gap:12px;flex-wrap:wrap;align-items:center}
#hdr .chip{background:rgba(255,255,255,.22);border-radius:22px;padding:8px 20px;text-align:center;min-width:96px}#hdr .chip b{display:block;font-size:clamp(26px,3.8vw,54px);font-weight:800;line-height:1.1}#hdr .chip small{font-size:clamp(12px,1.4vw,18px);letter-spacing:.07em;text-transform:uppercase;opacity:.92}
#hdr .lobtn{background:rgba(255,255,255,.22);color:#fff;border:2px solid rgba(255,255,255,.7);border-radius:99px;padding:12px 22px;font-size:clamp(16px,1.9vw,26px)}
#hdr .czbtn{background:rgba(255,255,255,.22);color:#fff;border:2px solid rgba(255,255,255,.7);border-radius:99px;padding:12px 22px;font-size:clamp(16px,1.9vw,26px)}
#hdr .lv{flex:1 0 100%;display:flex;flex-wrap:wrap;align-items:center;gap:8px 14px;margin-top:14px;font-family:ui-rounded,'Nunito','Baloo 2','Trebuchet MS','Segoe UI',system-ui,sans-serif}
#hdr .lv .lb{font-weight:900;font-size:clamp(18px,2.5vw,36px);color:#fff;background:rgba(0,0,0,.22);border-radius:99px;padding:4px 20px;white-space:nowrap}
#hdr .lv .xb{flex:1 1 160px;height:clamp(18px,2vw,28px);border-radius:99px;background:rgba(255,255,255,.28);overflow:hidden;border:2px solid rgba(255,255,255,.6)}
#hdr .lv .xb i{display:block;height:100%;background:linear-gradient(90deg,#fde047,#f59e0b);border-radius:99px;transition:width .6s}
#hdr .lv .xt{font-weight:800;color:#fff;font-size:clamp(14px,1.8vw,26px);white-space:nowrap}
#lvt{position:fixed;left:50%;top:14px;transform:translateX(-50%);z-index:99999;padding:12px 26px;border-radius:99px;font-weight:900;font-size:clamp(18px,3vw,30px);color:#7c2d12;background:linear-gradient(90deg,#fde047,#f59e0b);box-shadow:0 8px 28px rgba(0,0,0,.35);animation:lvin .5s ease-out}
@keyframes lvin{from{transform:translate(-50%,-80px);opacity:0}to{transform:translate(-50%,0);opacity:1}}
#hdr .lf{flex:1 0 100%;display:flex;flex-wrap:wrap;align-items:center;gap:8px 12px;margin-top:2px;padding-top:10px;border-top:2px dashed rgba(255,255,255,.55);font-family:ui-rounded,'Nunito','Baloo 2','Trebuchet MS','Segoe UI',system-ui,sans-serif}
#hdr .lf .lt{font-size:clamp(22px,3.2vw,48px);font-weight:900;letter-spacing:.01em;color:#fff;text-shadow:0 2px 0 rgba(0,0,0,.18),0 0 18px rgba(255,255,255,.55)}
#hdr .lf .lt em{font-style:normal;display:inline-block;margin-left:6px;padding:0 16px;border-radius:16px;background:#fde047;color:#7c2d12;text-shadow:none;box-shadow:0 4px 0 #f59e0b,0 6px 14px rgba(0,0,0,.25);transform:rotate(-2deg)}
#hdr .lf .tp{display:inline-flex;align-items:center;gap:8px;padding:6px 16px;border-radius:99px;font-size:clamp(15px,1.85vw,28px);font-weight:800;color:#fff;box-shadow:0 3px 0 rgba(0,0,0,.2),0 6px 14px rgba(0,0,0,.18)}
#hdr .lf .tp b{display:inline-block;min-width:1.6em;padding:0 8px;border-radius:99px;background:#fff;color:#1e1b3a;text-align:center;font-size:1.05em}
#hdr .lf .tp.c0{background:linear-gradient(135deg,#06b6d4,#3b82f6)}
#hdr .lf .tp.c1{background:linear-gradient(135deg,#22c55e,#14b8a6)}
#hdr .lf .tp.c2{background:linear-gradient(135deg,#f97316,#ef4444)}
#hdr .lf .tp.c3{background:linear-gradient(135deg,#a855f7,#6366f1)}
body.in #app{flex:1;margin:clamp(12px,2vw,24px) clamp(12px,3vw,40px) max(clamp(12px,3vw,40px),env(safe-area-inset-bottom));padding:clamp(20px,4vw,56px);display:flex;flex-direction:column;justify-content:center;text-align:center;border:0;border-radius:36px;font-size:clamp(18px,2.4vw,28px);box-shadow:0 18px 60px rgba(0,0,0,.16)}
body.in #app h2{font-size:clamp(44px,min(12.5vw,15vh),210px);line-height:1.1;margin:0 0 .35em;font-weight:900;background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;overflow-wrap:anywhere}
body.in #app .big{font-size:clamp(24px,5vw,56px);font-weight:800;margin:.3em 0}
body.in #app .big.sel{display:inline-block;align-self:center;background:var(--grad);color:#fff;border-radius:99px;padding:.25em 1.1em;animation:selpulse 1.6s ease-in-out infinite}
@keyframes selpulse{50%{transform:scale(1.06);box-shadow:0 0 40px var(--ac2)}}
body.in #app .mute{font-size:clamp(18px,min(2.8vw,3.6vh),42px)}
body.in #tm{font-size:clamp(40px,min(9.5vw,10.5vh),150px);font-weight:900;margin:.15em 0}
body.in #ti{font-size:clamp(32px,min(6.6vw,7.5vh),100px);text-align:center;padding:.35em .5em;border-radius:28px;border:5px solid var(--line);max-width:1200px;width:100%;margin:12px auto}
body.in #ti:focus{border-color:var(--ac2);box-shadow:0 0 0 8px rgba(124,58,237,.16)}
body.in #app .row{display:flex;justify-content:center}
body.in #app .row button{font-size:clamp(26px,min(4.6vw,5.5vh),70px);padding:.45em 1.8em;border-radius:28px;min-width:min(100%,520px)}body.in #ti::placeholder{font-size:.5em}
body.in .ch{width:100%;max-width:1000px;margin:10px auto;min-height:clamp(72px,12vh,140px);font-size:clamp(24px,4.6vw,56px);font-weight:800;text-align:center;color:#fff;text-shadow:0 2px 8px rgba(0,0,0,.25);border-radius:28px!important;border-color:transparent!important}
body.in .ch:nth-of-type(4n+1){background:linear-gradient(135deg,#6366f1,#8b5cf6)}
body.in .ch:nth-of-type(4n+2){background:linear-gradient(135deg,#ec4899,#f43f5e)}
body.in .ch:nth-of-type(4n+3){background:linear-gradient(135deg,#f59e0b,#f97316)}
body.in .ch:nth-of-type(4n+4){background:linear-gradient(135deg,#10b981,#06b6d4)}
body.in .ch.on{outline:6px solid #fde047;outline-offset:3px}body.in .ch.on:disabled{opacity:1}
body.in #me{display:none}
body.in #res{max-width:1000px;width:100%;margin:0 auto;text-align:left}
body.in .tmc{max-width:900px;margin:22px auto 0;font-size:clamp(16px,2vw,26px)}body.in .tmc .tmn{font-size:1.25em}body.in .tmc .tmp b{font-size:1.4em}body.in .tmc .tmm{font-size:.8em}
.idle .wv{font-size:clamp(90px,22vw,230px);line-height:1;animation:float 3s ease-in-out infinite}.idle .wv .avs{width:clamp(190px,34vh,360px);height:clamp(350px,63vh,667px);margin:0 auto}
.dots::after{content:'';animation:dots 1.4s steps(1) infinite}
@keyframes dots{0%{content:''}25%{content:'.'}50%{content:'..'}75%{content:'...'}}
#cz{position:fixed;inset:0;z-index:50;background:rgba(20,10,60,.72);display:none;place-items:center;padding:16px}#cz.on{display:grid}
#cz .czb{background:var(--card);color:var(--ink);border-radius:28px;padding:clamp(12px,2vh,24px) 28px;max-width:980px;width:100%;max-height:97vh;overflow:auto;text-align:center;box-shadow:0 20px 70px rgba(0,0,0,.4)}
#cz h3{margin:0 0 6px;font-size:clamp(22px,4vh,34px);font-weight:800}#cz .czl{font-size:12px;font-weight:800;letter-spacing:.08em;text-transform:uppercase;color:var(--mute);margin:16px 0 8px}
#cz .czg{display:flex;flex-wrap:wrap;gap:6px}#cz .czg button{font-size:20px;padding:4px;border-radius:12px}#cz .czg button.sel{outline:3px solid var(--ac);outline-offset:1px}
#cz{--sw:clamp(32px,5.6vh,50px)}#cz .czg button.sw{width:var(--sw);height:var(--sw);padding:0;border:0;border-radius:50%}#cz .czw{display:flex;gap:28px;align-items:center;text-align:left}#cz .avpv{height:clamp(300px,58vh,520px);width:calc(clamp(300px,58vh,520px)*.54);flex:none;border-radius:28px;background:var(--bg);overflow:hidden}#cz .czr{flex:1;min-width:0}#cz .cr{display:flex;align-items:center;gap:12px;margin:clamp(6px,1.2vh,12px) 0}#cz .cr .czl{width:112px;flex:none;margin:0;text-align:left;font-size:clamp(12px,1.9vh,16px)}#cz .czg button.ht{width:clamp(46px,8.4vh,76px);height:clamp(46px,8.4vh,76px);padding:0;overflow:hidden;border-radius:16px}#cz .czg button.tx{font-size:clamp(14px,2.3vh,19px);font-weight:700;padding:clamp(6px,1.2vh,12px) clamp(10px,1.6vh,18px)}#cz .czbot .cr{justify-content:flex-start}#cz .czbot .cr .czl{width:112px}@media(max-width:700px){#cz .czw{flex-direction:column;gap:10px}#cz .avpv{height:240px;width:130px}#cz .cr .czl{width:80px}}
#cz input{text-align:left;font-size:clamp(15px,2.4vh,20px);padding:clamp(6px,1.2vh,12px) 14px;flex:1;min-width:0}#cz .row{display:flex;margin-top:clamp(8px,1.6vh,16px)}#cz .row button{width:100%;padding:clamp(10px,1.8vh,16px);font-size:clamp(17px,2.8vh,24px)}
.cf{position:fixed;top:-8vh;z-index:60;pointer-events:none;animation:fall 2.4s ease-in forwards}
@keyframes fall{to{transform:translateY(112vh) rotate(540deg);opacity:.9}}
/* ===== level titles: each title has its own icon, colours and glow ===== */
#hdr .lv.l1{--a:#bbf7d0;--b:#4ade80;--t:#064e3b;--g:rgba(0,0,0,0)}
#hdr .lv.l2{--a:#bae6fd;--b:#38bdf8;--t:#0c4a6e;--g:rgba(0,0,0,0)}
#hdr .lv.l3{--a:#99f6e4;--b:#14b8a6;--t:#042f2e;--g:rgba(0,0,0,0)}
#hdr .lv.l4{--a:#fed7aa;--b:#fb923c;--t:#7c2d12;--g:rgba(251,146,60,.55)}
#hdr .lv.l5{--a:#374151;--b:#4c1d95;--t:#ffffff;--g:rgba(167,139,250,.9)}
#hdr .lv.l6{--a:#fca5a5;--b:#dc2626;--t:#ffffff;--g:rgba(248,113,113,.9)}
#hdr .lv.l7{--a:#c4b5fd;--b:#7c3aed;--t:#ffffff;--g:rgba(196,181,253,1)}
#hdr .lv.l8{--a:#f9a8d4;--b:#be185d;--t:#ffffff;--g:rgba(249,168,212,1)}
#hdr .lv.l9{--a:#fde047;--b:#f97316;--t:#4a1d00;--g:rgba(253,224,71,1)}
#hdr .lv.l10{--a:#fde047;--b:#f472b6;--t:#1e1b3a;--g:rgba(255,255,255,1)}
#hdr .lv .lb{background:linear-gradient(135deg,var(--a,#fde047),var(--b,#f59e0b));color:var(--t,#3b2300);border:2px solid #fff;box-shadow:0 0 14px var(--g,transparent),0 3px 8px rgba(0,0,0,.28);letter-spacing:.02em}
#hdr .lv .lb em{font-style:normal;margin-right:.25em}
#hdr .lv .xb i{background:linear-gradient(90deg,var(--a,#fde047),var(--b,#f59e0b))}
#hdr .lv.l8 .lb,#hdr .lv.l9 .lb{box-shadow:0 0 20px var(--g),0 3px 8px rgba(0,0,0,.28)}
#hdr .lv.l9 .lb{background:linear-gradient(110deg,#fde047,#fb923c,#fde047,#fb923c,#fde047);background-size:200% 100%;animation:lvshine2 3s linear infinite}
#hdr .lv.l10 .lb{background:linear-gradient(110deg,#fde047,#f472b6,#a78bfa,#38bdf8,#4ade80,#fde047);background-size:300% 100%;animation:lvshine3 4s linear infinite;box-shadow:0 0 24px rgba(255,255,255,.9),0 0 0 3px rgba(253,224,71,.8),0 3px 8px rgba(0,0,0,.3)}
#hdr .lv.l10 .xb i{background:linear-gradient(90deg,#fde047,#f472b6,#a78bfa,#38bdf8,#4ade80,#fde047);background-size:200% 100%;animation:lvshine2 4s linear infinite}
@keyframes lvshine2{to{background-position:200% 0}}@keyframes lvshine3{to{background-position:150% 0}}
@media(prefers-reduced-motion:reduce){#hdr .lv .lb,#hdr .lv .xb i{animation:none!important}}
</style><style>/* ===== lifelines: Pass on the left, Ask a friend on the right of the question ===== */
.lfw{display:grid;grid-template-columns:minmax(210px,1fr) minmax(0,2.4fr) minmax(210px,1fr);gap:clamp(10px,2vw,28px);align-items:center;width:100%}
.lfm{min-width:0}.lfs{min-width:0;font-size:clamp(15px,1.5vw,20px)}
body.in #app h2.qx{font-size:clamp(52px,min(9vw,17vh),220px);line-height:1.02;margin:.05em 0 .15em}
body.in #app h2.ql{font-size:clamp(34px,min(6vw,12vh),130px);margin:.1em 0 .2em}
body.in #app h2.qm{font-size:clamp(24px,min(3.8vw,7.5vh),80px);margin:.1em 0 .2em}
body.in #app .big.sel{font-size:clamp(14px,1.6vw,20px);padding:.2em 1em;margin:0 auto .5em;white-space:nowrap;animation:none;box-shadow:0 4px 12px rgba(0,0,0,.18)}
@media(max-width:900px){.lfw{grid-template-columns:1fr}.lfm{order:0}.lfs{order:1}}
/* lifeline cards */
.lfc{--c1:#06b6d4;--c2:#3b82f6;position:relative;overflow:hidden;text-align:left;padding:16px 16px 14px;border-radius:22px;background:var(--card);border:2px solid transparent;background-clip:padding-box;box-shadow:0 10px 28px rgba(0,0,0,.12),0 0 0 2px color-mix(in srgb,var(--c1) 35%,transparent);transition:transform .15s,box-shadow .2s}
.lfc.friend{--c1:#f97316;--c2:#ec4899}
.lfc::before{content:"";position:absolute;left:0;right:0;top:0;height:7px;background:linear-gradient(90deg,var(--c1),var(--c2))}
.lfc::after{content:"";position:absolute;right:-30px;bottom:-30px;width:110px;height:110px;border-radius:50%;background:radial-gradient(circle,color-mix(in srgb,var(--c1) 22%,transparent),transparent 70%);pointer-events:none}
.lfc.can:hover{transform:translateY(-3px);box-shadow:0 16px 34px rgba(0,0,0,.18),0 0 0 2px var(--c1)}
.lfc.can{animation:lfglow 2.6s ease-in-out infinite}
@keyframes lfglow{50%{box-shadow:0 12px 32px color-mix(in srgb,var(--c1) 45%,transparent),0 0 0 2px var(--c1)}}
.lfc.off{opacity:.55;filter:grayscale(.5)}
.lfc.used{box-shadow:0 12px 30px color-mix(in srgb,var(--c1) 40%,transparent),0 0 0 3px var(--c1)}
.lfh{display:flex;align-items:center;gap:12px;margin:6px 0 12px}
.lfh b{display:block;font-size:1.15em;font-weight:800;line-height:1.15}.lfh small{display:block;margin-top:2px;font-size:.72em;font-weight:600;color:var(--mute)}
.lfi{flex:none;width:2.4em;height:2.4em;border-radius:50%;display:grid;place-items:center;font-size:1.35em;color:#fff;background:linear-gradient(135deg,var(--c1),var(--c2));box-shadow:0 6px 14px color-mix(in srgb,var(--c1) 50%,transparent)}
.lfc select{width:100%;margin:0 0 10px;padding:11px 12px;font-size:16px;font-weight:600;border-radius:14px;border:2px solid color-mix(in srgb,var(--c1) 45%,var(--line));background:var(--card);color:var(--ink)}
.lfc select:focus{outline:0;border-color:var(--c1);box-shadow:0 0 0 4px color-mix(in srgb,var(--c1) 22%,transparent)}
.lfb{width:100%;display:flex;flex-direction:column;align-items:center;gap:2px;padding:12px;border-radius:14px;font-size:1em;font-weight:800;color:#fff;border:0;background:linear-gradient(135deg,var(--c1),var(--c2));box-shadow:0 8px 18px color-mix(in srgb,var(--c1) 45%,transparent)}
.lfb:disabled{background:rgba(120,120,150,.18);color:var(--mute);box-shadow:none}
.lfb .lfn{font-size:.75em;font-weight:700;opacity:.9}
.lftip{margin-top:10px;font-size:.78em;line-height:1.35;color:var(--mute)}
.lftm{margin-top:8px;display:inline-block;padding:3px 12px;border-radius:99px;font-size:.72em;font-weight:800;color:var(--c2);background:color-mix(in srgb,var(--c1) 14%,transparent)}
.lfmsg{font-size:.9em;line-height:1.4;color:var(--ink)}
/* compact header: more room for the question and the lifelines */
body.in #hdr{margin:max(8px,env(safe-area-inset-top)) clamp(8px,2vw,24px) 0;padding:8px clamp(10px,1.6vw,18px);border-radius:20px;gap:6px clamp(8px,1.4vw,16px)}
body.in #hdr .av{width:clamp(44px,5vw,64px);height:clamp(44px,5vw,64px);font-size:clamp(16px,2vw,24px);border-width:2px}
body.in #hdr .hn{min-width:110px}body.in #hdr .hn b{font-size:clamp(17px,2vw,26px)}body.in #hdr .hn span{font-size:clamp(11px,1.1vw,14px)}
body.in #hdr .chips{gap:8px}body.in #hdr .chip{padding:3px 12px;min-width:64px;border-radius:14px}body.in #hdr .chip b{font-size:clamp(16px,1.9vw,24px)}body.in #hdr .chip small{font-size:10px}
body.in #hdr .czbtn,body.in #hdr .lobtn{padding:6px 14px;font-size:clamp(12px,1.2vw,15px)}
body.in #hdr .lv{margin-top:2px;gap:4px 10px}body.in #hdr .lv .lb{font-size:clamp(12px,1.3vw,16px);padding:2px 12px}body.in #hdr .lv .xb{height:12px;flex-basis:100px}body.in #hdr .lv .xt{font-size:clamp(11px,1.1vw,14px)}
body.in #hdr .lf{margin-top:0;padding-top:6px;gap:4px 8px;border-top-width:1px}
body.in #hdr .lf .lt{font-size:clamp(13px,1.4vw,18px)}body.in #hdr .lf .lt em{padding:0 8px;border-radius:10px;box-shadow:0 2px 0 #f59e0b}
body.in #hdr .lf .tp{padding:2px 10px;font-size:clamp(11px,1.1vw,14px);gap:5px}
body.in #app{margin-top:clamp(8px,1.2vw,14px);padding:clamp(12px,2vw,28px)}
</style><style>/* ===== level title shown as a badge: round medal + ribbon ===== */
body.in #hdr .lv .lb{display:inline-flex;align-items:center;gap:0;padding:0;background:none!important;border:0;box-shadow:none!important;animation:none!important;position:relative;flex:none}
body.in #hdr .lv .lb .bdg{position:relative;z-index:2;flex:none;width:clamp(58px,6.4vw,84px);aspect-ratio:1;border-radius:50%;display:flex;flex-direction:column;align-items:center;justify-content:center;line-height:1;color:var(--t,#3b2300);background:radial-gradient(circle at 32% 26%,#fff 0,var(--a,#fde047) 28%,var(--b,#f59e0b) 100%);border:3px solid #fff;box-shadow:0 0 0 3px var(--b,#f59e0b),0 0 0 5px rgba(255,255,255,.9),0 0 18px var(--g,transparent),0 6px 14px rgba(0,0,0,.35)}
body.in #hdr .lv .lb .bdg::before{content:'';position:absolute;inset:4px;border-radius:50%;border:2px dashed rgba(255,255,255,.8);pointer-events:none}
body.in #hdr .lv .lb .bdg em{font-style:normal;margin:0;font-size:clamp(22px,2.6vw,34px);filter:drop-shadow(0 2px 2px rgba(0,0,0,.3))}
body.in #hdr .lv .lb .bdg small{font-size:clamp(9px,.95vw,12px);font-weight:900;letter-spacing:.12em;text-transform:uppercase;margin-top:3px}
body.in #hdr .lv .lb .rb{position:relative;z-index:1;margin-left:-18px;padding:6px 24px 6px 28px;font-size:clamp(13px,1.5vw,20px);font-weight:900;letter-spacing:.07em;text-transform:uppercase;white-space:nowrap;color:var(--t,#3b2300);background:linear-gradient(135deg,var(--a,#fde047),var(--b,#f59e0b));border:2px solid #fff;border-left:0;border-radius:0 99px 99px 0;box-shadow:0 0 12px var(--g,transparent),0 4px 10px rgba(0,0,0,.28)}
body.in #hdr .lv.l9 .lb .rb{background:linear-gradient(110deg,#fde047,#fb923c,#fde047,#fb923c,#fde047);background-size:200% 100%;animation:lvshine2 3s linear infinite!important}
body.in #hdr .lv.l10 .lb .rb{background:linear-gradient(110deg,#fde047,#f472b6,#a78bfa,#38bdf8,#4ade80,#fde047);background-size:300% 100%;animation:lvshine3 4s linear infinite!important}
body.in #hdr .lv.l10 .lb .bdg{background:conic-gradient(#fde047,#f472b6,#a78bfa,#38bdf8,#4ade80,#fde047);box-shadow:0 0 0 3px #fde047,0 0 0 5px #fff,0 0 24px rgba(255,255,255,.95),0 6px 14px rgba(0,0,0,.35)}
@media(prefers-reduced-motion:reduce){body.in #hdr .lv .lb .rb{animation:none!important}}
</style><style>/* ===== compact header: badge beside the name ===== */
body.in #hdr .hn{flex:0 1 auto;min-width:0}
body.in #hdr .lv.lvb{flex:0 0 auto;display:block;margin:0;padding:0;gap:0}
body.in #hdr .chips{margin-left:auto}
body.in #hdr .lv.lvb .lb .bdg{width:clamp(52px,5vw,64px);border-width:2px}
body.in #hdr .lv.lvb .lb .bdg em{font-size:clamp(16px,1.6vw,21px);line-height:1}
body.in #hdr .lv.lvb .lb .bdg small{font-size:clamp(8px,.8vw,10px);margin-top:3px;letter-spacing:.06em}
body.in #hdr .lv.lvb .lb .bdg::before{inset:3px}
body.in #hdr .lv.lvb .lb .rb{margin-left:-14px;padding:4px 18px 4px 22px;font-size:clamp(11px,1.2vw,16px)}
body.in #hdr .lv{margin-top:0}
@media(max-width:640px){
body.in #hdr .hn{flex:1 1 0;min-width:0}
body.in #hdr .hn b{font-size:clamp(15px,4.4vw,19px);line-height:1.15;overflow-wrap:anywhere}
body.in #hdr .hn span{font-size:11px}
body.in #hdr .lv.lvb{flex:0 0 auto}
body.in #hdr .lv.lvb .lb .rb{margin-left:-12px;padding:3px 10px 3px 22px;font-size:10px;letter-spacing:.04em}
body.in #hdr .lv.lvb .lb .bdg{width:48px}
body.in #hdr .chips{margin-left:0;flex:1 0 100%;gap:6px}
body.in #hdr .chip{min-width:56px;padding:2px 10px}
body.in #hdr .czbtn,body.in #hdr .lobtn{padding:5px 11px;font-size:12px}
}
</style></head>
<body><div id="hdr"></div><div class="card" id="app">Connecting…</div><script>""" + COMMON + r"""
let cid;try{cid=localStorage.cid||(localStorage.cid=Math.random().toString(36).slice(2))}catch(e){cid=Math.random().toString(36).slice(2)}
let nm='';try{nm=localStorage.nm||''}catch(e){}
let sc='';try{sc=localStorage.sc||''}catch(e){}
const ROSTER=/*ROSTER*/null;
if(nm&&!(ROSTER&&ROSTER[sc]&&ROSTER[sc].includes(nm))){nm='';sc='';try{localStorage.nm='';localStorage.sc=''}catch(e){}}
const THEMES=[{n:'Violet Pop',a:'#7c3aed',b:'#ec4899',c:'#06b6d4'},{n:'Ocean',a:'#2563eb',b:'#06b6d4',c:'#22c55e'},{n:'Sunset',a:'#f97316',b:'#ef4444',c:'#f59e0b'},{n:'Jungle',a:'#059669',b:'#84cc16',c:'#0ea5e9'},{n:'Candy',a:'#db2777',b:'#a855f7',c:'#f472b6'},{n:'Galaxy',a:'#4338ca',b:'#9333ea',c:'#22d3ee'}];
/* levels: HP. Every session earns its accuracy (correct / items answered): 100% = 1 HP, 10% = 0.10 HP (the server adds them up).
   HP needed to pass a level: Lv 1-4 cost 1 HP each, Lv 5-9 cost 2 HP each (1 HP = 100% in one session).
   So Lv 6 is reached at 6 HP and Lv 10 (Grandmaster, the maximum) at 14 HP. */
const HPC=n=>n<=4?1:2,LVI=['🌱','🔢','🧮','🧩','🥷','🦸','🧙','🧠','🔥','👑'],LVN=['Rookie','Counter','Calculator','Problem Solver','Number Ninja','Math Hero','Math Wizard','Brainiac','Legend','Grandmaster'];
function lvInfo(hp,now){hp=Math.max(0,+hp||0);now=Math.max(0,+now||0);const MX=LVN.length,fm=v=>String(Math.round(v*100)/100);let lv=1,lo=0;
 while(lv<MX&&hp>=lo+HPC(lv)-1e-9){lo+=HPC(lv);lv++}   /* Level 10 is the highest level */
 const top=lv>=MX,need=HPC(lv),into=Math.max(0,hp-lo);
 return{lv,hp,ready:true,pct:top?100:Math.max(0,Math.min(100,Math.round(100*into/need))),title:LVN[lv-1],icon:LVI[lv-1],
  txt:top?'🏆 MAX LEVEL · total '+fm(hp)+' HP'+(now>0?' · this session +'+fm(now):''):fm(into)+' / '+need+' HP to Lv '+(lv+1)+(lv>1?' · total '+fm(hp)+' HP':'')+(now>0?' · this session +'+fm(now):'')}}
function lvCheck(i){if(!i.ready)return;try{const k='lv2:'+sc+'|'+nm,o=parseInt(localStorage.getItem(k)||'0')||0;
 if(o&&i.lv>o){confetti(160);const t=document.createElement('div');t.id='lvt';t.textContent=i.icon+' Level up! Lv '+i.lv+' · '+i.title;document.body.appendChild(t);setTimeout(()=>t.remove(),4500)}
 localStorage.setItem(k,String(Math.max(o,i.lv)))}catch(e){}}
const pfk=()=>'pf:'+sc+'|'+nm;
function pf(){try{return nm?JSON.parse(localStorage.getItem(pfk())||'{}'):{}}catch(e){return{}}}
function pushPf(){clearTimeout(window.pfT);window.pfPend=1;window.pfT=setTimeout(async()=>{try{await fetch('/api/profile',{method:'POST',body:JSON.stringify({cid,name:nm,sec:sc,p:pf()})})}catch(e){}window.pfPend=0},500)}
function savePf(o){try{localStorage.setItem(pfk(),JSON.stringify(Object.assign(pf(),o)))}catch(e){}if(nm)pushPf()}
/* the server keeps the profile: on a new device / cleared browser it is restored from there; a profile made before this update is uploaded once */
function syncPf(){try{if(!nm||!S||S.myprof===undefined||window.pfPend)return;const sp=S.myprof,lp=pf(),k=pfk();
 if(sp){const same=['av','th','mo'].every(f=>(sp[f]===undefined?lp[f]===undefined:sp[f]===lp[f]));if(!same){localStorage.setItem(k,JSON.stringify(Object.assign({},lp,sp)));window.pfK='';const h=$('hdr');if(h)h.dataset.k=''}}
 else if(Object.keys(lp).length&&window.pfUp!==k){window.pfUp=k;pushPf()}}catch(e){}}
function applyTheme(){const p=pf(),t=THEMES[p.th]||THEMES[0],r=document.documentElement.style;r.setProperty('--ac',t.a);r.setProperty('--ac2',t.b);r.setProperty('--ac3',t.c);r.setProperty('--grad','linear-gradient(135deg,'+t.a+' 0%,'+t.b+' 100%)')}
async function logout(){if(!nm)return;
 if(!confirm("Log out "+nm+"? Your points are saved. You can join again on any device by choosing your name."))return;
 const c=cid,tell=()=>{try{fetch("/api/logout",{method:"POST",body:JSON.stringify({cid:c})})}catch(e){}};
 try{await fetch("/api/logout",{method:"POST",body:JSON.stringify({cid:c})})}catch(e){}
 nm="";sc="";mine={};window.nick=0;shown=null;try{localStorage.nm="";localStorage.sc=""}catch(e){}
 setTimeout(tell,2500);   /* a poll that was already in flight could re-register the name: release it once more */
 build()}
function renderHdr(){const h=$('hdr');if(!h)return;if(!nm){h.innerHTML='';h.dataset.k='';return}
 const p=pf(),me=S&&S.me,g=S&&S.mygoal,ml=S&&S.mylife,li0=(S&&S.mylife)?lvInfo(S&&S.myhp,S&&S.myhps):null,ma=(S&&S.myatt)||{},tp=(S&&S.topics)||[],key=[nm,sc,p.av,p.mo,me?me.r+'|'+me.s:'',g&&g.n?g.got+'/'+g.n:'',ml?tp.map(t=>(ml[t]||0)+'/'+(ma[t]||0)).join(','):'',S&&S.myhp!=null?S.myhp+'/'+S.myhps:''].join('~');
 if(h.dataset.k===key)return;h.dataset.k=key;
 const ini=nm.split(' ').filter(Boolean).slice(0,2).map(x=>x[0]).join('').toUpperCase();
 h.innerHTML='<button class=\"av\" id=\"avb\" title=\"Customize\">'+(p.av?avh(p.av,'h'):esc(ini))+'</button><div class=\"hn\"><b>'+esc(nm)+'</b><span>'+esc(sc)+(p.mo?' · “'+esc(p.mo)+'”':'')+'</span></div>'+(li0?'<div class=\"lv lvb l'+li0.lv+'\"><span class=lb><span class=bdg><em>'+li0.icon+'</em><small>Lv '+li0.lv+'</small></span><span class=rb>'+esc(li0.title)+'</span></span></div>':'')+'<div class=\"chips\">'+(me?'<div class=\"chip\"><b>#'+me.r+'</b><small>Rank</small></div><div class=\"chip\"><b>'+me.s+'</b><small>Points</small></div>':'')+(g&&g.n?'<div class=\"chip\"><b>'+g.got+'/'+g.n+'</b><small>Goal</small></div>':'')+'<button class=\"czbtn\" id=\"czb\">🎨 Customize</button><button class=\"lobtn\" id=\"lob\" title=\"Log out to join from another device\">🚪 Log out</button></div>';
 if(ml){const lf=document.createElement('div');lf.className='lf';
  lf.innerHTML='<span class=lt>📚 Your total (all sessions):<em>'+tp.reduce((a,t)=>a+(ml[t]||0),0)+'/'+tp.reduce((a,t)=>a+(ma[t]||0),0)+'</em></span>'+tp.map((t,i)=>'<span class="tp c'+(i%4)+'">'+esc(t)+' <b>'+(ml[t]||0)+'/'+(ma[t]||0)+'</b></span>').join('');
  {const li=li0,lv=document.createElement('div');lv.className='lv l'+li.lv;
   lv.innerHTML=`<div class=xb><i style="width:${li.pct}%"></i></div><span class=xt>${li.txt}</span>`;
   h.appendChild(lv);lvCheck(li)}
  h.appendChild(lf)}
 $('avb').onclick=$('czb').onclick=openCz;$('lob').onclick=logout}
function openCz(){let z=$('cz');if(!z){z=document.createElement('div');z.id='cz';document.body.appendChild(z);z.onclick=e=>{if(e.target===z)closeCz()}}
 const old=z.querySelector('.czb'),st=old?old.scrollTop:0;
 const p=pf(),cur=avP(p.av&&p.av[0]=='@'?p.av:AVDEF),code=avMake(cur);
 const sw=(k,arr)=>`<div class="czg">`+arr.map((c,i)=>`<button data-k="${k}" data-v="${i}" class="sw ${cur[k]==i?'sel':''}" style="background:${c}"></button>`).join('')+`</div>`;
 const tx=(k,arr)=>`<div class="czg">`+arr.map((t,i)=>`<button data-k="${k}" data-v="${i}" class="tx ${cur[k]==i?'sel':''}">${t}</button>`).join('')+`</div>`;
 const row=(l,inner,extra)=>`<div class="cr"><span class="czl">${l}</span>${inner}</div>`;
 z.innerHTML=`<div class="czb"><h3>Make it yours ✨</h3><div class="czw"><div class="avpv">${avSvg(code,'f')}</div><div class="czr" id="cza">`
  +row('Gender',tx('g',['👦 Boy','👧 Girl']))
  +row('Skin',sw('sk',AV.sk))
  +row('Hairstyle',`<div class="czg">`+AV.hs.map((n,i)=>`<button data-k="hs" data-v="${i}" title="${n}" class="ht ${cur.hs==i?'sel':''}">${avSvg(code,'h',{hs:i})}</button>`).join('')+`</div>`)
  +row('Hair color',sw('hc',AV.hc))
  +row('Eyes',sw('ec',AV.ec))
  +row('Outfit',sw('oc',AV.oc))
  +row('Extras',tx('ac',['None','👓 Glasses','🧢 Cap']))
  +`<div class="cr"><button data-k="x" class="tx ${!p.av?'sel':''}" style="border-radius:12px">Use my initials instead</button></div></div></div>`
  +`<div class="czbot"><div class="cr"><span class="czl">Theme</span><div class="czg" id="czt">`+THEMES.map((t,i)=>`<button data-t="${i}" title="${t.n}" class="sw ${(p.th||0)==i?'sel':''}" style="background:linear-gradient(135deg,${t.a},${t.b})"></button>`).join('')+`</div></div><div class="cr"><span class="czl">Motto</span><input id="czm" maxlength="30" placeholder="e.g. Math is my superpower" value="${esc(p.mo||'')}"></div></div><div class="row"><button class="p" id="czd">Done</button></div></div>`;
 z.classList.add('on');const nb=z.querySelector('.czb');if(nb)nb.scrollTop=st;
 z.querySelectorAll('#cza button').forEach(b=>b.onclick=()=>{const k=b.dataset.k;if(k=='x')savePf({av:''});else{const o=Object.assign({},cur);o[k]=+b.dataset.v;savePf({av:avMake(o)})}applyTheme();renderHdr();openCz()});
 z.querySelectorAll('#czt button').forEach(b=>b.onclick=()=>{savePf({th:+b.dataset.t});applyTheme();renderHdr();openCz()});
 $('czm').oninput=e=>savePf({mo:e.target.value.trim()});$('czd').onclick=closeCz}
function closeCz(){const z=$('cz');if(z)z.classList.remove('on');applyTheme();renderHdr();shown=null}
function boom(){const E=['🎉','⭐','✨','🎊','💜','🌟'];for(let i=0;i<46;i++){const e=document.createElement('span');e.className='cf';e.textContent=E[i%E.length];e.style.left=Math.random()*100+'vw';e.style.animationDelay=Math.random()*.6+'s';e.style.fontSize=(18+Math.random()*26)+'px';document.body.appendChild(e);setTimeout(()=>e.remove(),3200)}}
let mine={},shown=null,S=null;
const isQ=s=>s.type=='quiz'||s.type=='num';
const kk=()=>S.slide.id+'|'+(S.slide.gv||0)+'|'+S.slide.q+'|'+S.open+'|'+S.slide.rev+'|'+S.wait+'|'+nm+'|'+S.slide.turn+'|'+(S.slide.log||[]).filter(x=>x.c==cid&&x.a).length+'|'+S.role+'|'+(S.lf?(S.lf.can?1:0)+JSON.stringify(S.lf.used||0)+JSON.stringify(S.lf.left):'')+'|'+S.hq+'|'+S.hans+'|'+S.hmark+'|'+(S.picked||[]).length+'|'+(S.mygoal&&S.mygoal.out)+'|'+S.myans+'|'+S.mymark+'|'+S.myq+'|'+S.multiq+'|'+S.idle+'|'+(S.review?S.review.n+'|'+S.review.q:'');
function fbh(F,ok){if(!F)return '';const st=F.steps||[];if(!st.length&&!F.hint)return '';
 return '<div style="margin-top:14px;text-align:left;padding:12px 14px;border-radius:14px;border:2px solid '+(ok?'#16a34a':'#f59e0b')+';background:rgba(124,58,237,.07)">'
  +(F.hint?'<div style="margin-bottom:8px">💡 '+esc(F.hint)+'</div>':'')
  +(st.length?'<div style="font-weight:700">'+(ok?'Check your reasoning:':'How to solve it:')+'</div>'+st.map((x,i)=>'<div style="margin-top:3px">'+(i+1)+'. '+esc(x)+'</div>').join(''):'')+'</div>'}
function rv(R){const ok=R.mark=='ok',ex=R.ex||[];
 return '<div style="margin-top:16px;text-align:left;padding:14px 16px;border-radius:16px;border:2px solid '+(ok?'#16a34a':'#dc2626')+';background:rgba(124,58,237,.07)">'
 +'<div style="font-weight:800;margin-bottom:8px">📖 Study your last question</div>'
 +'<div style="margin-bottom:8px">'+mx(R.q)+'</div>'
 +'<div>'+(ok?'✅':'❌')+' Your answer: <b>'+(R.mine?esc(R.mine):'(none)')+'</b></div>'
 +'<div>🎯 Correct answer: <b>'+mx(R.a)+'</b></div>'
 +(ex.length?'<div style="margin-top:10px;font-weight:700">How to solve it:</div>'+ex.map((x,i)=>'<div style="margin-top:3px">'+(i+1)+'. '+esc(x)+'</div>').join(''):'')
 +(ok?'<div class="mute" style="margin-top:10px">Nice! Read it again to make sure you really know why.</div>':'<div class="mute" style="margin-top:10px">Compare each step with how you solved it. Where did your working go differently?</div>')+'</div>'}
function build(){const s=S.slide;shown=kk();document.body.classList.toggle('jn',!nm);document.body.classList.toggle('in',!!nm);applyTheme();renderHdr();
 if(!nm){const secs=Object.keys(ROSTER||{});
  $('app').innerHTML='<div class="join"><div class="logo">📊</div><h1>Join the class</h1><p class="sub">Choose your section, then your name</p><label for="ss">Section</label><select id="ss">'+secs.map(x=>'<option>'+esc(x)+'</option>').join('')+'</select><label for="sn">Your name</label><select id="sn"></select><div class="row"><button class="p" id="go">Join</button></div><p class="alt mute">Can\'t find your name? Ask your teacher.</p></div>';
  const fill=()=>{const sn=$('sn');if(!sn||document.activeElement===sn)return;   /* never touch the list while it is open */
   const keep=sn.value,tk=(S.taken||{})[$('ss').value]||[],L=ROSTER[$('ss').value].filter(x=>!tk.includes(x)),
    html=L.length?L.map(x=>'<option>'+esc(x)+'</option>').join(''):'<option value="" disabled selected>(everyone here has already joined)</option>';
   if(sn.dataset.h===html)return;   /* unchanged: leave the dropdown alone (the 1.5s refresh used to close it) */
   sn.dataset.h=html;sn.innerHTML=html;if(keep&&L.includes(keep))sn.value=keep};window.fillNames=fill;fill();$('ss').onchange=fill;
  $('go').onclick=()=>{if(!$('sn').value)return;nm=$('sn').value;sc=$('ss').value;try{localStorage.nm=nm;localStorage.sc=sc}catch(x){}build()};
  return}
 if(S.mygoal&&S.mygoal.out){$('app').innerHTML='<p class="big">🎉 Great job, '+esc(nm)+'!</p><h2>'+(S.mygoal.team?'Your team '+esc(S.mygoal.team)+' scored '+S.mygoal.got+' points.':'You got '+S.mygoal.got+' correct answers.')+'</h2><p class="big">🚪 You may leave now.</p><p class="mute">Please show this screen to your teacher.</p><div class=\"mute\">'+(S.mylife?'<b>📚 Your total (all sessions): '+(S.topics||[]).reduce((a,t)=>a+(S.mylife[t]||0),0)+'</b><br>'+(S.topics||[]).map(t=>esc(t)+' '+(S.mylife[t]||0)).join(' · '):'')+'</div>';return}
 if(S.idle){$('app').innerHTML='<div class="idle"><div class="wv">'+(pf().av?avh(pf().av,'f'):'👋')+'</div><p class="big">Welcome, '+esc(nm)+'!</p><p class="mute dots">Waiting for your teacher to start</p></div><div id="res"></div><p class="mute" id="me" style="margin-top:14px"></p><div id="myteam"></div><div id="mylife" class="mute"></div>';return}
 let h=(S.role=='player'?'<p class="big sel">You are selected!</p>':S.role=='helper'?'<p class="big sel">🙋 '+esc(S.hfrom)+' needs your help!</p>':'')+(function(t){return '<h2 class="'+(t.length<=24?'qx':t.length<=70?'ql':'qm')+'">'+mx(t)+'</h2>'})(S.role=='player'&&S.myq?S.myq:S.role=='helper'?S.hq:S.multiq?'':s.q)+'<div id="tm"></div>';const m=mine[s.id+':'+(s.gv||0)];
 if(S.role=="helper")h+=S.hmark?(S.hmark=="ok"?"<p class='big'>✅ Correct! "+(S.hk=="pass"?"+1 point for you!":"Your friend earns the point.")+"</p>":"<p class='big'>❌ Not quite.</p>")+"<p class='mute'>Your answer: "+esc(S.hans)+"</p>":S.hans?"<p class='big'>✅ Answer sent!</p><p class='mute'>Your answer: "+esc(S.hans)+"</p>":S.wait?"<p class='mute'>Waiting for the host to start the timer…</p>":!S.open?"<p class='mute'>⏰ Time is up.</p>":"<input id='ti' maxlength='200' placeholder='Type your answer…' autocomplete='off'><div class='row' style='margin-top:8px'><button class='p' id='sb'>Send</button></div><p class='mute'>"+(S.hk=="pass"?"You answer this question and earn the point.":"You help "+esc(S.hfrom)+" — they earn the point.")+"</p>";
 else if(S.role=='viewer')h+='<p class="big">👀 You are watching</p><p class="mute">Only the selected students can answer this round.</p>'+(S.picked&&S.picked.length?'<p class="mute">Answering: <b>'+S.picked.map(esc).join(', ')+'</b></p>':'')+(S.review?rv(S.review):'');
 else if(s.rev&&isQ(s))h+=(S.ok==null?'<p class="big">⏰ No answer submitted</p>':S.ok?'<p class="big">✅ Correct! +'+S.pts+' points</p>':'<p class="big">❌ Not quite. The answer was '+mx(s.ans)+'</p>')+fbh(S.fb,S.ok);
 else if(s.type=='pick'){const e=(s.log||[]).filter(x=>x.c==cid).pop();
  if(S.role=='player')h+=S.mymark?mmsg()+'<p class="mute">Your answer: '+esc(S.myans)+'</p>':S.lf&&S.lf.used?(S.myans?"<p class='big'>✅ "+esc(S.lf.used.to)+" answered!</p><p class='mute'>Waiting for the result…</p>":"<p class='big'>⏳ "+esc(S.lf.used.to)+" is answering…</p>"):S.myans?'<p class="big">✅ Answer sent!</p><p class="mute">Your answer: '+esc(S.myans)+'</p>':S.wait?'<p class="mute">Waiting for the host to start the timer…</p>':!S.open?'<p class="mute">⏰ Time is up.</p>':'<input id="ti" maxlength="200" placeholder="Type your answer…" autocomplete="off"><div class="row" style="margin-top:8px"><button class="p" id="sb">Send</button></div>';
  else h+=S.yours?(e&&e.a?'<p class="big">✅ Answer sent!</p><p class="mute">Your teacher will respond.</p>':'<input id="ti" maxlength="200" placeholder="Type your answer…"><div class="row" style="margin-top:8px"><button class="p" id="sb">Send</button></div>'):(s.turn?'<p class="mute">'+esc(s.turnName)+' is answering…</p>':'<p class="mute">Think about it! Your teacher will pick someone.</p>')}
 else if(S.wait)h+='<p class="mute">Waiting for the host to start the timer…</p>';
 else if(!S.open&&!(isQ(s)&&m!=null))h+='<p class="mute">Voting is closed.</p>';
 else if(s.type=='mc'||s.type=='scale'||s.type=='quiz'){const L=s.type=='scale'?['1','2','3','4','5']:s.opts,lock=s.type=='quiz'&&m!=null;
  h+=L.map(l=>'<button class="ch '+(m==l?'on':'')+'" data-v="'+esc(l)+'" '+(lock?'disabled':'')+'>'+mx(l)+'</button>').join('')+(m!=null?'<p class="mute">'+(lock?'🔒 Answer locked in!':'Vote recorded. You can change it.')+'</p>':'')}
 else{const num=s.type=='num',lim=num?1:3,n=num?(m!=null?1:0):(m||0);
  h+=(S.bres?(S.bres.timeout?'<p class="mute" style="color:#fca5a5">⏰ No answer. Counted as wrong: the boss healed +'+S.bres.heal+'. No point for this one.'+(S.bres.streak>=2?'<br><b>⚠ '+S.bres.streak+' skipped in a row. Your classmates are carrying you. Please answer!</b>':'')+'</p>':S.bres.ok===null?'<p class="mute">⏱ Time ran out on the last question.</p>':S.bres.ok?'<p class="big">✅ Hit! −'+S.bres.dmg+' HP to the boss'+(S.bres.x2?' ⚡ DOUBLE!':'')+'</p>':'<p class="mute">❌ Not quite. The answer was '+mx(S.bres.ans)+'. The boss healed +'+S.bres.heal+'</p>'+(S.bres.rush?'<p class="mute" style="color:#fca5a5">⚡ Too fast: that looks like a guess. Take your time and solve it.'+(S.bres.streak>=2?'<br><b>⚠ '+S.bres.streak+' skipped/guessed in a row. Please really try!</b>':'')+'</p>':'')):'')+(S.bres&&S.bres.pt?'<p class="mute" style="color:'+(S.bres.pt>0?'#86efac':'#fca5a5')+'">'+(S.bres.pt>0?'\u2795 +':'\u2796 \u2212')+Math.abs(S.bres.pt)+' point'+(Math.abs(S.bres.pt)>1?'s':'')+(S.bres.fast?' ⚡ fast answer!':'')+'</p>':'')+(n<lim?'<input id="ti" maxlength="60" placeholder="'+(num?'Your answer (e.g. 12, 3/4, 2.5)':'Type here and press Enter')+'"><div class="row" style="margin-top:10px"><button class="p" id="sb">Submit ✔</button></div><p class="mute">'+n+'/'+lim+' submitted</p>':'<p class="mute">'+(num?'🔒 Answer locked in!':'Thanks! You have used all 3 responses.')+'</p>')}
 h+='<div id="res"></div><p class="mute" id="me" style="margin-top:14px"></p><div id="myteam"></div><div id="mylife" class="mute"></div>';if(S.role=='player')h='<div class="lfw"><div class="lfs" id="lfp_pass"></div><div class="lfm">'+h+'</div><div class="lfs" id="lfp_friend"></div></div>';$('app').innerHTML=h;if((s.rev&&isQ(s)&&S.ok)||(S.bres&&S.bres.ok)||(S.role=='player'&&S.mymark=='ok'&&!(S.lf&&S.lf.used&&S.lf.used.k=='pass'))||(S.role=="helper"&&S.hmark=="ok"))boom();
 document.querySelectorAll('.ch').forEach(b=>b.onclick=()=>send(b.dataset.v));
 const ti=$('ti');if(ti){ti.onkeydown=e=>{if(e.key=='Enter'&&ti.value.trim())send(ti.value)};ti.focus();const b=$('sb');if(b)b.onclick=()=>ti.value.trim()&&send(ti.value)}}
/* who earns the point: PASS = the classmate who answered; ASK A FRIEND = the student who was picked (the friend only helps) */
function mmsg(){const U=S.lf&&S.lf.used;
 if(S.mymark!='ok')return "<p class='big'>❌ Not quite.</p>"+(U?"<p class='mute'>"+(U.k=='pass'?"No point for "+esc(U.to)+".":"No point for you this time.")+"</p>":"");
 if(U&&U.k=='pass')return "<p class='big'>✅ Correct! "+esc(U.to)+" earns the point.</p>";
 if(U)return "<p class='big'>✅ Correct! Your friend "+esc(U.to)+" helped, and YOU earn the point.</p>";
 return "<p class='big'>✅ Correct!</p>"}
var LFSEL={pass:"",friend:""};
function lfpanel(){const L=S&&S.role=="player"?S.lf:null;["pass","friend"].forEach(k=>lfone(k,L))}
/* each lifeline has its own card: PASS on the left of the question, ASK A FRIEND on the right (stacked under the question on a narrow phone) */
function lfone(k,L){const el=$("lfp_"+k);if(!el)return;
 const mode=!L?"":L.used?"used":L.can?"can":"lock";
 const key=!L?"":mode=="used"?"u"+L.used.k+"|"+L.used.to:mode+L.left[k];
 const T=k=="pass"?{ic:"🙋",ti:"Pass it to",sub:"A classmate answers instead",verb:"Pass the question",tip:"They answer and earn the point."}:{ic:"📞",ti:"Ask a friend",sub:"They help, you keep the point",verb:"Ask this friend",tip:"They answer, but YOU earn the point."};
 const hd="<div class='lfh'><span class='lfi'>"+T.ic+"</span><div><b>"+T.ti+"</b><small>"+T.sub+"</small></div></div>";
 const card=(cls,inner)=>"<div class='lfc "+k+" "+cls+"'>"+inner+"</div>";
 if(el.dataset.k!==key){
  el.dataset.k=key;let h="";
  if(mode=="used"){
   if(L.used.k==k)h=card("used",hd+"<div class='lfmsg'>"+(k=="pass"?"You passed this question to <b>"+esc(L.used.to)+"</b>. They earn the point if correct.":"Your friend <b>"+esc(L.used.to)+"</b> is helping. You earn the point if correct.")+"</div>");
   else h=card("off",hd+"<div class='lfmsg'>Not available: you already used a lifeline.</div>");
  }
  else if(mode=="can")h=card("can",hd+"<select id='lfto_"+k+"'></select><button id='lf_"+k+"' class='lfb' disabled>"+T.verb+" <span class='lfn'>"+L.left[k]+" left</span></button><div class='lftip'>"+T.tip+"</div><div class='lftm'>⏱ 5 seconds to decide</div>");
  else if(mode=="lock")h=card("off",hd+"<button class='lfb' disabled>"+T.verb+" <span class='lfn'>"+L.left[k]+" left</span></button><div class='lftip'>🔒 Locked. Answer the question yourself.</div>");
  el.innerHTML=h;
  if(mode=="can"){
   const sel=$("lfto_"+k),btn=$("lf_"+k);
   sel.onchange=()=>{LFSEL[k]=sel.value;btn.disabled=!sel.value||!L.left[k]};
   btn.onclick=async()=>{const to=sel.value;if(!to)return;btn.disabled=true;
    await fetch("/api/lifeline",{method:"POST",body:JSON.stringify({cid,k,to})});LFSEL[k]="";await tick();build()};
  }
 }
 if(mode!="can")return;
 /* the dropdown is refreshed with the students who are online right now (a dropdown that is open is left alone) */
 const sig=L.opts.join("|"),sel=$("lfto_"+k),btn=$("lf_"+k);if(!sel||!btn)return;
 if(document.activeElement!==sel&&sel.dataset.o!==sig){
  const keep=LFSEL[k];sel.innerHTML="";
  sel.appendChild(new Option(L.opts.length?"— choose who will answer —":"— no classmate is online right now —",""));
  L.opts.forEach(x=>sel.appendChild(new Option(x,x)));
  sel.dataset.o=sig;sel.value=L.opts.includes(keep)?keep:"";LFSEL[k]=sel.value;
 }
 btn.disabled=!sel.value||!L.left[k];
}
function net(on){let e=$('net');if(!e){e=document.createElement('div');e.id='net';e.style.cssText='position:fixed;left:50%;bottom:14px;transform:translateX(-50%);padding:8px 16px;border-radius:999px;background:#b45309;color:#fff;font:600 14px system-ui,sans-serif;z-index:99;display:none;max-width:92vw;text-align:center';document.body.appendChild(e)}
 if(on){e.textContent=typeof on=='string'?on:'Reconnecting\u2026';e.style.display='block'}else e.style.display='none'}
const SENDING={};
async function send(v){const s=S.slide,k=s.id+':'+(s.gv||0);
 if(SENDING[k])return;SENDING[k]=1;   /* a second tap while the first is on its way does nothing */
 const prev=mine[k];mine[k]=['mc','scale','quiz','num'].includes(s.type)?v:(prev||0)+1;build();   /* the screen reacts at once, before the network answers */
 const body=JSON.stringify({cv:2,cid,id:s.id,gv:s.gv||0,v:v,name:nm,sec:sc,rid:Math.random().toString(36).slice(2,12)});let ok=false;
 for(let i=0;i<6&&!ok;i++){   /* the same request id is re-sent, so the server counts it once even if only the reply was lost */
  try{const ac=new AbortController(),to=setTimeout(()=>ac.abort(),8000);try{const r=await fetch('/api/vote',{method:'POST',body:body,signal:ac.signal});ok=r.ok}finally{clearTimeout(to)}}catch(e){}
  if(!ok)await new Promise(r=>setTimeout(r,250*(i+1)+Math.random()*250))}
 SENDING[k]=0;
 if(!ok){if(prev===undefined)delete mine[k];else mine[k]=prev;net('Answer not sent. Check the Wi-Fi and tap Submit again.');build();return}
 net(0);tick().then(build)}
let TSEQ=0,TAPP=0;
async function getState(){const my=++TSEQ,ac=new AbortController(),to=setTimeout(()=>ac.abort(),7000);
 try{const r=await fetch('/api/state?v=2&cid='+cid+'&name='+encodeURIComponent(nm)+'&sec='+encodeURIComponent(sc),{signal:ac.signal});if(!r.ok)throw 0;const J=await r.json();
  if(my<TAPP)return null;TAPP=my;return J}finally{clearTimeout(to)}}   /* an older reply never overwrites a newer one */
async function tick(){try{{const J=await getState();if(!J)return;S=J}net(0);window.N=S.respondents;tmr(S);bossdraw(S.boss);
 {const bb=S.boss,bi=bb&&bb.bno?bb.bno:0,pst=window.PBS;window.PBS=bb?bb.st:null;
  if(pst==='fight'&&(!bb||bb.st==='idle')&&nm&&!window.rld){window.rld=1;location.reload();return}   /* teacher stopped the battle: refresh so nothing stays locked */
  if(window.PBI===undefined)window.PBI=bi;
  if(bi!==window.PBI){window.PBI=bi;mine={};shown=null}}   /* a new battle: forget the answers of the old one */
 {const o=!!(S.mygoal&&S.mygoal.out);if(window.pout===false&&o)confetti(180);window.pout=o;const d=!!(S.myteam&&S.myteam.done);if(window.ptd===false&&d)confetti(180);window.ptd=d}
 if(S.dup){nm='';sc='';mine={};window.nick=0;shown=null;try{localStorage.nm='';localStorage.sc=''}catch(e){}build();$('app').insertAdjacentHTML('afterbegin','<p class=\"big\">⚠️ That name was already taken. Please pick again.</p>');return}
 if(!nm&&window.fillNames&&$('sn'))window.fillNames();
 {let old=null;try{old=localStorage.sess}catch(e){}
  if(old!==S.sess&&S.sess!==window.sess0){   /* server was restarted: forget the old session, force a fresh join */
   cid=Math.random().toString(36).slice(2);nm='';sc='';mine={};window.nick=0;shown=null;
   try{const KP=[];for(let i=0;i<localStorage.length;i++){const k=localStorage.key(i);if(k.indexOf('pf:')==0)KP.push([k,localStorage.getItem(k)])}localStorage.clear();KP.forEach(x=>localStorage.setItem(x[0],x[1]));localStorage.cid=cid;localStorage.sess=S.sess}catch(e){}
  }
  window.sess0=S.sess}
 if(S.mygoal&&S.mygoal.out&&nm){   /* reached the goal and may leave: log out automatically after 1 minute */
   if(!window.outT)window.outT=setTimeout(()=>{window.outT=0;if(!(S&&S.mygoal&&S.mygoal.out))return;nm='';sc='';mine={};window.nick=0;shown=null;try{localStorage.nm='';localStorage.sc=''}catch(x){}build()},60000)}
  else if(window.outT){clearTimeout(window.outT);window.outT=0}   /* teacher called the student back: cancel the logout */
  syncPf();if(shown!=kk())build();applyTheme();renderHdr();lfpanel();const s=S.slide;
 if($('me'))$('me').textContent=S.me?'🏆 '+nm+' · rank #'+S.me.r+' · '+S.me.s+' pts'+(S.mygoal&&S.mygoal.n?' · ✅ '+S.mygoal.got+'/'+S.mygoal.n:'')+(S.mynoisy?' · 🔇 '+S.mynoisy+' noisy':''):'';
 
  if($('myteam'))$('myteam').innerHTML=S.myteam?'<div class="tmc"><div class="tmn">👥 '+esc(S.myteam.name)+'</div><div class="tmp"><b>'+S.myteam.tot+'</b> pts'+(S.myteam.rnd?' <em>+'+S.myteam.rnd+' this round</em>':'')+' · #'+S.myteam.rank+' of '+S.myteam.n+'</div><div class="tmm">'+S.myteam.m.map(x=>esc(x)+' <b>'+((S.myteam.mc||{})[x]||0)+'</b>').join(' · ')+'</div></div>':'';
 if($('res'))$('res').innerHTML=S.idle?'':s.type=='open'||s.type=='pick'?'':isQ(s)?(s.rev?results(s):''):((mine[s.id+':'+(s.gv||0)]!=null||!S.open)?'<hr style="border:0;border-top:1px solid var(--line);margin:16px 0">'+results(s):'')}catch(e){if(!S)$('app').textContent='Reconnecting\u2026';else net(1)}}   /* keep what the student typed; only show a small notice */
/* auto-submit: whatever is typed in the answer box is sent just before the timer reaches 0, so a student who typed an answer but ran out of time is not counted as "No answer" */
function autoSub(){try{if(!S||!S.open||!S.run||S.left==null||!S.slide||S.slide.rev||S.slide.type!='num')return;
 const l=S.left-(Date.now()-T0)/1000;if(l>(window.AJ||(window.AJ=0.2+Math.random()*0.5)))return;   /* each phone sends at its own moment in the last 0.7 s, so 50 auto-submits do not hit the server in the same millisecond */
 const k=S.slide.id+':'+(S.slide.gv||0);if(window.AS===k||mine[k]!=null)return;
 const ti=$('ti');if(!ti)return;const v=ti.value.trim();if(!v)return;
 window.AS=k;send(v)}catch(e){}}
setInterval(autoSub,200);
(async function loop(){await tick();setTimeout(loop,1300+Math.random()*500)})();   /* next poll starts only after the last one finished, with a random offset */</script></body></html>"""

HOST = """<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Host</title>""" + CSS + """
<style>header{display:flex;gap:8px;align-items:center;flex-wrap:wrap;padding:12px 20px;background:var(--card);border-bottom:1px solid var(--line)}header b{margin-right:auto;font-size:20px}
#app{display:grid;grid-template-columns:220px 1fr;gap:16px;padding:16px;max-width:1200px;margin:auto}.sl{padding:10px;border:1px solid var(--line);background:var(--card);border-radius:8px;margin-bottom:6px;cursor:pointer;font-size:14px}.sl.on{border-color:var(--ac);box-shadow:0 0 0 2px var(--ac)}
.row{display:flex;gap:8px;margin:6px 0}label{font-size:13px;color:var(--mute);display:block;margin:12px 0 4px}h2{margin:0 0 12px}
body.proj{background:radial-gradient(ellipse at top,#3730a3 0%,#14122e 55%,#0b0a1a 100%);color:#fff;min-height:100vh}
body.proj header,body.proj #tabs,body.proj #gen,body.proj #side,body.proj #ed,body.proj #join,body.proj hr,body.proj .ctl,body.proj #app>div:first-child{display:none}
body.proj #app{display:block;max-width:1400px;padding:6vh 6vw}body.proj .card{background:transparent;border:0;padding:0;min-height:84vh;display:flex;flex-direction:column;justify-content:center;text-align:center}
body.proj h2{text-align:center;line-height:1.12;margin:0 0 6vh;font-weight:800;letter-spacing:-.02em;font-size:clamp(34px,6vw,96px)}body.proj h2.xl{font-size:clamp(48px,10vw,170px)}body.proj h2.lg{font-size:clamp(40px,7vw,120px)}body.proj h2.md{font-size:clamp(32px,4.5vw,76px)}body.proj .spot{font-size:1.8em}body.proj .bar .n{text-align:left}
body.proj #res{font-size:clamp(18px,2.4vw,34px)}body.proj .mute{color:#b9bce0;font-size:clamp(14px,1.4vw,20px)}
body.proj .bar{margin:2.4vh 0;gap:2vw}body.proj .bar .n{width:22%;font-weight:600}
body.proj .bar .t{height:clamp(44px,8vh,80px);background:rgba(255,255,255,.09);border-radius:16px}
body.proj .bar .f{border-radius:16px;box-shadow:0 0 24px rgba(255,255,255,.12) inset}body.proj .bar .v{width:80px;font-weight:800;font-size:1.2em}
body.proj .ans{background:rgba(255,255,255,.1);border-radius:14px;padding:16px 22px}
body.proj #cnt{position:fixed;top:3vh;right:4vw;background:rgba(255,255,255,.12);backdrop-filter:blur(6px);padding:10px 20px;border-radius:99px;color:#fff;font-size:clamp(14px,1.5vw,22px)}
body.proj #tm{font-size:clamp(28px,4vw,60px);color:#fbbf24;margin-bottom:2vh}#pickbar{display:flex;flex-wrap:wrap;gap:6px;margin-top:16px}body.proj #pickbar{position:fixed;left:4vw;right:4vw;bottom:3vh;opacity:.3;transition:opacity .2s;margin:0}body.proj #pickbar:hover{opacity:1}body.proj #pickbar button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}body.proj #pickbar button.p{background:var(--ac)}#tabs{display:flex;gap:6px;padding:12px 20px 0;max-width:1200px;margin:auto;flex-wrap:wrap}#tabs button.on{background:var(--ac);color:#fff;border-color:var(--ac)}#gen{display:flex;gap:8px;align-items:center;padding:10px 20px;max-width:1200px;margin:auto;flex-wrap:wrap}#gen select{padding:9px;border-radius:8px;background:var(--card);color:var(--ink);border:1px solid var(--line)}#rp{display:none;position:fixed;inset:0;z-index:20;background:rgba(10,8,30,.9);backdrop-filter:blur(8px);align-items:center;justify-content:center;color:#fff}#rp.on{display:flex}#rpn{font-size:clamp(40px,9vw,150px);font-weight:800;line-height:1.1;padding:0 4vw}#rps{font-size:clamp(18px,2.4vw,36px);color:#b9bce0;margin-top:2vh}#rp button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}#rp button.p{background:var(--ac)}#hint{display:none}body.proj #hint{display:block;position:fixed;top:3vh;left:4vw;color:#8b8eb8;font-size:13px}
#big{font-size:20px;font-weight:700;color:var(--ac)}
#fab{position:fixed;right:3vw;bottom:3vh;z-index:10;font-size:clamp(16px,1.8vw,26px);font-weight:700;padding:14px 26px;border-radius:99px;background:var(--ac);color:#fff;border:0;box-shadow:0 6px 24px rgba(79,70,229,.5)}
#fab:hover{filter:brightness(1.15)}#gear{position:fixed;right:3vw;bottom:calc(3vh + 4.6em);z-index:10;font-size:clamp(14px,1.4vw,20px);font-weight:700;padding:10px 20px;border-radius:99px;background:rgba(255,255,255,.16);color:#fff;border:1px solid rgba(255,255,255,.3);backdrop-filter:blur(6px)}#gear:hover{background:rgba(255,255,255,.28)}body.proj #pickbar{right:calc(3vw + 280px)}
#rpn{transition:transform .08s,color .2s}#rpn.spin{opacity:.85;transform:scale(.97)}#rpn.done{color:#fbbf24;transform:scale(1.08);text-shadow:0 0 40px rgba(251,191,36,.6)}
#sp{display:none;position:fixed;inset:0;z-index:30;background:rgba(10,8,30,.93);backdrop-filter:blur(8px);align-items:center;justify-content:center;color:#fff;padding:4vh 4vw}#sp.on{display:flex}
#spt{font-size:clamp(24px,3.4vw,52px);font-weight:800;margin-bottom:4vh}#spb{display:grid;grid-template-columns:repeat(3,1fr);gap:2vh 1.5vw;margin-bottom:4vh}
#spb button{font-size:clamp(16px,2vw,30px);font-weight:700;padding:2.4vh 1vw;border-radius:16px;background:rgba(255,255,255,.12);color:#fff;border:2px solid transparent}
#spb button:hover{background:var(--ac)}#spb button.cur{border-color:#fbbf24}#spb button.all{grid-column:1/-1;background:rgba(251,191,36,.2)}#sp>div>button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}
#who{display:none;position:fixed;top:11vh;left:50%;transform:translateX(-50%);z-index:5;background:rgba(251,191,36,.16);border:2px solid #fbbf24;color:#fbbf24;padding:1.2vh 2.4vw;border-radius:99px;font-size:clamp(18px,2.6vw,40px);font-weight:800;white-space:nowrap;box-shadow:0 0 40px rgba(251,191,36,.25)}#who.on{display:block}#who small{color:#e9d7a0;font-weight:500;font-size:.55em;margin-left:.8em}
#turn{display:none;position:fixed;left:2vw;top:50%;transform:translateY(-50%);width:26vw;min-width:280px;max-height:95vh;overflow-y:auto;z-index:6;color:#fff;text-align:center;--fn:clamp(22px,2.8vw,48px);--fa:clamp(22px,3vw,52px);scrollbar-width:none}
#turn.on{display:block}body:not(.proj) #turn{display:none!important}body.proj.hasturn #app{padding-left:31vw}
#turn.c2,#turn.c3{--fn:clamp(18px,2.2vw,36px);--fa:clamp(16px,2.2vw,36px)}#turn.c3:not(.mixed) .ts,#turn.c4:not(.mixed) .ts,#turn.c5:not(.mixed) .ts{display:none}#turn.c4,#turn.c5{--fn:clamp(14px,min(1.7vw,2.7vh),28px);--fa:clamp(13px,min(1.7vw,2.6vh),26px)}#turn.c4 .tc,#turn.c5 .tc{padding:.7vh .7vw;margin-bottom:.8vh}#turn.c4 .tcc input,#turn.c5 .tcc input{padding:.4vh .6vw;font-size:min(14px,1.8vh)}#turn.c4 .tcc button,#turn.c5 .tcc button{padding:.4vh .9vw}
#tt{font-size:clamp(44px,6.4vw,110px);font-weight:800;color:#fbbf24;font-variant-numeric:tabular-nums;line-height:1;margin-bottom:1.4vh}#turn.c4 #tt,#turn.c5 #tt{font-size:clamp(30px,min(4.4vw,7vh),72px)}
#tt.low{color:#fb923c}#tt.up{color:#ef4444;animation:bl .6s infinite alternate}@keyframes bl{to{opacity:.3}}
.tc{padding:1.2vh .9vw;border-radius:18px;background:rgba(255,255,255,.07);border:3px solid rgba(255,255,255,.18);margin-bottom:1.2vh;transition:background .3s,border-color .3s}
.tc.ok{background:rgba(16,185,129,.30);border-color:#10b981}.tc.no{background:rgba(239,68,68,.30);border-color:#ef4444}
.tn{font-size:var(--fn);font-weight:800;line-height:1.1}.ts{font-size:clamp(11px,1vw,16px);color:#b9bce0;margin:.3vh 0}.ta{font-size:var(--fa);font-weight:700;min-height:1.1em;word-break:break-word}
.tv{font-size:clamp(13px,1.3vw,24px);font-weight:800}.tr{display:flex;justify-content:center;align-items:baseline;gap:.8vw;flex-wrap:wrap;min-height:1.2em}.tc.ok .tv{color:#34d399}.tc.no .tv{color:#f87171}
.tl{font-size:.55em;font-weight:700;color:#fbbf24;min-height:0}.tcc{display:flex;gap:5px;margin-top:.6vh;opacity:.35;transition:opacity .2s}#turn:hover .tcc,#turn:focus-within .tcc{opacity:1}.tcc input{padding:6px 8px;min-width:0;flex:1;background:rgba(0,0,0,.35);color:#fff;border-color:rgba(255,255,255,.25)}
.tcc button{padding:6px 11px;color:#fff;border-color:transparent}.tcc button.g{background:#059669}.tcc button.rd{background:#dc2626}
#tctl{margin-top:1vh;opacity:.35;transition:opacity .2s}#turn:hover #tctl,#turn:focus-within #tctl{opacity:1}
#tctl button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent;padding:5px 10px}#tctl .row{margin:3px 0}#tctl button.cur{outline:2px solid #fbbf24}
#tctl input{background:rgba(0,0,0,.35);color:#fff;border-color:rgba(255,255,255,.25)}
#rpn.n2,#rpn.n3,#rpn.n4,#rpn.n5{display:flex;flex-wrap:wrap;justify-content:center;gap:2vh 3vw;font-size:clamp(28px,6vw,100px)}#rpn.n3{font-size:clamp(26px,5vw,84px)}#rpn.n4,#rpn.n5{font-size:clamp(22px,3.8vw,64px)}
.slot{padding:0 1vw;transition:transform .15s,color .2s}.slot.spin{opacity:.85}.slot.done{color:#fbbf24;transform:scale(1.06);text-shadow:0 0 40px rgba(251,191,36,.55)}.slot small{display:block;font-size:.3em;font-weight:500;color:#b9bce0;text-shadow:none}
#bysec{margin:12px 0}#bysec details{border:1px solid var(--line);border-radius:10px;padding:6px 10px;margin-bottom:6px}#bysec summary{cursor:pointer;font-weight:600;display:flex;justify-content:space-between;gap:8px}#bysec .bc{font-weight:700;color:#34d399}#bysec .bc.z{color:var(--mute);font-weight:500}#bysec .nm{display:flex;flex-wrap:wrap;gap:6px;margin-top:8px}#bysec .nm span{padding:3px 9px;border-radius:999px;font-size:13px}#bysec .nm .on{background:rgba(52,211,153,.18);color:#6ee7b7}#bysec .nm .off{background:rgba(255,255,255,.05);color:var(--mute)}#bysec .nm .fin{background:rgba(251,191,36,.18);color:#fbbf24;font-weight:600}#bysec h4{margin:0 0 6px;font-size:14px}#fin{position:fixed;inset:0;z-index:9999;background:radial-gradient(circle at 50% 35%,#6b4a05,#0a081e);display:none;align-items:center;justify-content:center;text-align:center;color:#fff;cursor:pointer;padding:4vh 4vw}#fin.on{display:flex}#fin .ft{font-size:clamp(18px,2.4vw,36px);letter-spacing:.25em;text-transform:uppercase;color:#fbbf24;margin-bottom:3vh}#fin .fn{font-size:clamp(34px,7vw,120px);font-weight:800;line-height:1.1;text-shadow:0 0 50px rgba(251,191,36,.55)}#fin .fn small{display:block;font-size:.28em;font-weight:500;color:#fde68a;text-shadow:none;margin-top:.4vh}#fin .fn+.fn{margin-top:2.5vh}#fin .fs{font-size:clamp(20px,3vw,48px);margin-top:4vh;color:#fff}#fin .fh{font-size:clamp(12px,1.2vw,18px);margin-top:5vh;color:#b9bce0}
#fstrip{position:fixed;right:2vw;top:12vh;max-width:24vw;max-height:60vh;overflow:hidden;column-width:11vw;column-gap:1vw;z-index:5;display:none;background:rgba(251,191,36,.12);border:1px solid rgba(251,191,36,.4);border-radius:14px;padding:1.2vh 1.2vw;color:#fde68a;font-size:clamp(12px,1.25vw,20px)}body.proj #fstrip.has{display:block}#fstrip b{display:block;color:#fbbf24;margin-bottom:.6vh}#fstrip div{padding:.2vh 0}#fstrip b .bk{background:rgba(255,255,255,.14);color:#fde68a;border:0;border-radius:6px;padding:1px 7px;cursor:pointer;font-size:.8em}#fstrip div{display:flex;align-items:center;justify-content:space-between;gap:.6vw;break-inside:avoid}#fstrip .bkd .nm2{opacity:.45;text-decoration:line-through}#fstrip .tg{position:relative;width:34px;height:18px;flex:none;cursor:pointer}#fstrip .tg input{opacity:0;position:absolute;inset:0;margin:0;cursor:pointer;z-index:1}#fstrip .tg i{position:absolute;inset:0;background:rgba(255,255,255,.2);border-radius:18px;transition:.15s}#fstrip .tg i:before{content:'';position:absolute;left:2px;top:2px;width:14px;height:14px;border-radius:50%;background:#fff;transition:.15s}#fstrip .tg input:checked+i{background:#22c55e}#fstrip .tg input:checked+i:before{left:18px}
#toast{position:fixed;left:50%;top:20px;transform:translateX(-50%);background:#fbbf24;color:#1a1a2e;font-weight:700;padding:12px 22px;border-radius:12px;z-index:99;display:none;font-size:18px}body.proj #bysec{display:none}
#spm{margin-bottom:4vh}#spm .mute{color:#b9bce0}#spm button{font-size:clamp(14px,1.6vw,24px);font-weight:700;padding:1.4vh 1.2vw;border-radius:12px;background:rgba(255,255,255,.12);color:#fff;border:2px solid transparent}#spm button:hover{background:var(--ac)}#spm button.cur{border-color:#fbbf24}
#rpt{font-size:clamp(16px,2vw,28px);color:#b9bce0;margin-bottom:3vh;letter-spacing:.2em;text-transform:uppercase}</style>
<style>/* ===== vibrant theme ===== */
:root{--bg:#f6f3ff;--card:#fff;--ink:#1e1b3a;--mute:#6f6a94;--ac:#7c3aed;--ac2:#ec4899;--ac3:#06b6d4;--line:#e4defa;--grad:linear-gradient(135deg,#7c3aed 0%,#ec4899 100%);--shadow:0 8px 28px rgba(124,58,237,.14)}
@media(prefers-color-scheme:dark){:root{--bg:#120f2b;--card:#1d1942;--ink:#f5f3ff;--mute:#a9a4d6;--line:#352f69;--shadow:0 8px 28px rgba(0,0,0,.45)}}
body{font-family:Inter,"Segoe UI",system-ui,-apple-system,sans-serif;background:radial-gradient(circle at 0% 0%,rgba(236,72,153,.16),transparent 38%),radial-gradient(circle at 100% 0%,rgba(6,182,212,.16),transparent 40%),radial-gradient(circle at 50% 100%,rgba(124,58,237,.14),transparent 50%),var(--bg);background-attachment:fixed}
button{border-radius:12px;font-weight:600;transition:transform .12s,box-shadow .15s,background .15s,filter .15s}
button:hover{transform:translateY(-2px);box-shadow:0 6px 16px rgba(124,58,237,.25);border-color:var(--ac)}button:active{transform:translateY(0) scale(.97)}
button.p,#tabs button.on{background:var(--grad);border-color:transparent;color:#fff;box-shadow:0 4px 14px rgba(236,72,153,.35)}button.p:hover{filter:brightness(1.1)}
input,select{border-radius:12px;border:2px solid var(--line);transition:border-color .15s,box-shadow .15s}input:focus,select:focus{outline:0;border-color:var(--ac);box-shadow:0 0 0 4px rgba(124,58,237,.18)}
.card{border-radius:20px;border:1px solid var(--line);box-shadow:var(--shadow)}
header{background:var(--grad)!important;color:#fff;border:0!important;box-shadow:0 6px 24px rgba(124,58,237,.35)}header b{font-weight:800;letter-spacing:-.01em}
header button.p{background:#fff;color:#7c3aed;box-shadow:0 4px 14px rgba(0,0,0,.2)}
#tabs button{border-radius:99px;padding:9px 18px;background:var(--card)}
.sl{border-radius:14px;border:2px solid transparent;box-shadow:0 2px 10px rgba(124,58,237,.08);transition:transform .12s,box-shadow .15s}.sl:hover{transform:translateX(3px);box-shadow:0 4px 16px rgba(124,58,237,.2)}
.sl.on{background:linear-gradient(135deg,rgba(124,58,237,.12),rgba(236,72,153,.12));border-color:var(--ac);box-shadow:0 0 0 3px rgba(124,58,237,.2)}
#big{background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;font-size:26px;font-weight:800}
#q{font-weight:800}#tm{background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.bar .t{border-radius:99px;height:38px;background:rgba(124,58,237,.1)}.bar .f{border-radius:99px;background:linear-gradient(90deg,#7c3aed,#ec4899)}
.bar:nth-child(5n+2) .f{background:linear-gradient(90deg,#06b6d4,#3b82f6)}.bar:nth-child(5n+3) .f{background:linear-gradient(90deg,#f59e0b,#ef4444)}
.bar:nth-child(5n+4) .f{background:linear-gradient(90deg,#10b981,#84cc16)}.bar:nth-child(5n+5) .f{background:linear-gradient(90deg,#8b5cf6,#06b6d4)}
.ans{border-radius:14px;border-left:5px solid var(--ac2)}
#bysec details{border-radius:14px;border:2px solid var(--line);background:var(--card);transition:border-color .15s}#bysec details[open],#bysec details:hover{border-color:var(--ac)}
#bysec .bc{background:rgba(16,185,129,.15);padding:2px 12px;border-radius:99px}#bysec .bc.z{background:rgba(124,58,237,.08)}
#fab{background:var(--grad);box-shadow:0 8px 30px rgba(236,72,153,.55);animation:pulse 2.4s ease-in-out infinite}
@keyframes pulse{50%{box-shadow:0 8px 42px rgba(124,58,237,.8);transform:scale(1.04)}}
.ch{border-radius:16px!important;border:2px solid var(--line)!important;background:var(--card)}.ch:hover{border-color:var(--ac)!important}.ch.on{background:var(--grad)!important;border-color:transparent!important;box-shadow:0 6px 18px rgba(236,72,153,.4)}
h2{font-weight:800}
/* projector */
body.proj{background:#1b1147}
body.proj::before{content:"";position:fixed;inset:-25%;z-index:-1;pointer-events:none;filter:blur(70px);opacity:.95;animation:drift 20s ease-in-out infinite alternate;background:radial-gradient(circle at 15% 20%,#ec4899 0,transparent 32%),radial-gradient(circle at 85% 15%,#06b6d4 0,transparent 32%),radial-gradient(circle at 70% 85%,#7c3aed 0,transparent 38%),radial-gradient(circle at 20% 85%,#f59e0b 0,transparent 26%)}
@keyframes drift{to{transform:translate(4%,-3%) rotate(8deg) scale(1.12)}}
body.proj h2{color:#fff;text-shadow:0 4px 40px rgba(0,0,0,.35),0 0 60px rgba(236,72,153,.45)}
body.proj #tm{background:none;-webkit-text-fill-color:#fde047;color:#fde047;text-shadow:0 0 30px rgba(253,224,71,.6)}
body.proj #cnt{background:rgba(255,255,255,.18);border:1px solid rgba(255,255,255,.35);box-shadow:0 6px 24px rgba(0,0,0,.25)}
body.proj .bar .t{background:rgba(255,255,255,.14)}body.proj .bar .f{box-shadow:0 0 30px rgba(255,255,255,.3),0 0 24px rgba(255,255,255,.2) inset}
body.proj .ans{background:rgba(255,255,255,.16);backdrop-filter:blur(6px);border-left-color:#fde047}
body.proj #pickbar button.p,body.proj #rp button.p{background:var(--grad)}
.tc{background:rgba(255,255,255,.12);backdrop-filter:blur(8px);box-shadow:0 8px 30px rgba(0,0,0,.25)}
.tc.ok{box-shadow:0 0 34px rgba(16,185,129,.55)}.tc.no{box-shadow:0 0 34px rgba(239,68,68,.5)}
#tt{text-shadow:0 0 36px rgba(253,224,71,.65)}
#spb button:hover,#spm button:hover{background:var(--grad)}
#rp,#sp{background:rgba(24,12,66,.88)}
.slot.done,#rpn.done{color:#fde047;text-shadow:0 0 50px rgba(253,224,71,.8)}
#back{display:none}body.proj #back{display:block;position:fixed;top:2.5vh;left:2vw;z-index:12;font-size:clamp(14px,1.4vw,20px);font-weight:700;padding:10px 20px;border-radius:99px;background:rgba(255,255,255,.18);color:#fff;border:1px solid rgba(255,255,255,.4);backdrop-filter:blur(6px);opacity:.55;transition:opacity .2s,background .2s}
body.proj #back:hover{opacity:1;background:var(--grad);border-color:transparent}body.proj #hint{top:10vh}
#rpn.n2,#rpn.n3,#rpn.n4,#rpn.n5{gap:1vh 2vw;line-height:1.05;padding:0 2vw}#rpn.n2{font-size:clamp(36px,9vw,160px)}#rpn.n3{font-size:clamp(32px,7.6vw,132px)}#rpn.n4,#rpn.n5{font-size:clamp(28px,6vw,104px)}.slot{padding:0 .6vw}
/* selected-names overlay: one clearly separated card per student */
#rpn.n2,#rpn.n3,#rpn.n4,#rpn.n5{flex-direction:column;flex-wrap:nowrap;align-items:center;justify-content:center;gap:2vh;padding:0 3vw;line-height:1.1}
#rpn.n2{font-size:clamp(28px,min(6.2vw,10vh),110px)}#rpn.n3{font-size:clamp(26px,min(5.2vw,8vh),92px)}#rpn.n4{font-size:clamp(24px,min(4.4vw,6.6vh),76px)}#rpn.n5{font-size:clamp(22px,min(3.8vw,5.6vh),64px)}
#rpn.n2 .slot,#rpn.n3 .slot,#rpn.n4 .slot,#rpn.n5 .slot{width:min(88vw,1200px);padding:.35em .9em;border-radius:.4em;background:rgba(255,255,255,.1);border:.07em solid rgba(255,255,255,.28);box-shadow:0 8px 30px rgba(0,0,0,.3)}
#rpn.n2 .slot.done,#rpn.n3 .slot.done,#rpn.n4 .slot.done,#rpn.n5 .slot.done{background:rgba(251,191,36,.14);border-color:#fbbf24;transform:none}
/* patch: keep the question readable on the projector */
body.proj.hasturn #app{max-width:none}
body.proj h2.xl{font-size:clamp(48px,min(10vw,22vh),170px)}
body.proj h2.lg{font-size:clamp(36px,min(7vw,12vh),120px)}
body.proj h2.md{font-size:clamp(28px,min(4.5vw,8vh),76px)}
body.proj h2{overflow-wrap:anywhere}
/* patch: bigger, screen-centred question; smaller name panels */
body.proj h2{margin:0 0 5vh}
body.proj h2.xl{font-size:clamp(60px,min(13vw,28vh),240px)}
body.proj h2.lg{font-size:clamp(46px,min(9vw,17vh),160px)}
body.proj h2.md{font-size:clamp(34px,min(6vw,11vh),104px)}
body.proj.hasturn #app{max-width:none;padding-left:24vw;padding-right:24vw}
#turn{width:22vw;min-width:240px;--fn:clamp(15px,1.8vw,30px);--fa:clamp(18px,2.4vw,40px)}
#turn.c2,#turn.c3{--fn:clamp(14px,1.5vw,24px);--fa:clamp(15px,1.9vw,30px)}
#turn.c4,#turn.c5{--fn:clamp(12px,min(1.25vw,2vh),19px);--fa:clamp(12px,min(1.4vw,2.2vh),22px)}
#fstrip{max-width:20vw;column-width:9vw;font-size:clamp(9px,.9vw,14px);padding:.8vh .8vw}
#fstrip .tg{width:26px;height:14px}#fstrip .tg i:before{width:10px;height:10px}#fstrip .tg input:checked+i:before{left:14px}
#nzb{display:none}body.proj #nzb{display:block;position:fixed;right:3vw;bottom:calc(3vh + 8.4em);z-index:10;font-size:clamp(14px,1.4vw,20px);font-weight:700;padding:10px 20px;border-radius:99px;background:rgba(239,68,68,.4);color:#fff;border:1px solid rgba(255,255,255,.3);backdrop-filter:blur(6px)}
#nz{display:none;position:fixed;inset:0;z-index:31;background:rgba(10,8,30,.93);backdrop-filter:blur(8px);align-items:center;justify-content:center;color:#fff;padding:4vh 4vw}#nz.on{display:flex}
#nzt{font-size:clamp(20px,2.6vw,40px);font-weight:800;margin-bottom:1vh}#nzs{max-width:60vw;margin:1vh 0;padding:10px;font-size:clamp(14px,1.6vw,22px)}
#nzg{display:grid;grid-template-columns:repeat(4,1fr);gap:1.2vh 1vw;margin:2vh 0 3vh;max-height:58vh;overflow-y:auto;padding:4px}
#nzg button{font-size:clamp(13px,1.5vw,22px);font-weight:700;padding:1.4vh .8vw;border-radius:12px;background:rgba(255,255,255,.12);color:#fff;border:2px solid transparent}#nzg button:hover{background:#dc2626}#nzg button.on{border-color:#34d399}
#nz .row button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}
#nz>div{display:flex;flex-direction:column;max-height:92vh;max-width:1500px!important}
#nzg{flex:1 1 auto;min-height:0;max-height:none;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));align-content:start;grid-auto-rows:min-content;margin:1.5vh 0 2vh;padding:6px 10px 6px 6px;scrollbar-width:thin;scrollbar-color:rgba(255,255,255,.45) transparent}
#nzg button{flex-shrink:0}
#nzg::-webkit-scrollbar{width:10px}#nzg::-webkit-scrollbar-thumb{background:rgba(255,255,255,.4);border-radius:8px}
#nz .row{flex:0 0 auto}
body.proj h2.mq{font-size:clamp(30px,min(5.6vw,11vh),110px);text-align:center;line-height:1.15;margin:0}
body.proj h2.mq.m4{font-size:clamp(24px,min(3.8vw,8vh),72px)}
body.proj h2.aq{display:grid;grid-template-columns:repeat(auto-fill,minmax(15vw,1fr));gap:.8vh .7vw;width:92vw;max-width:92vw;box-sizing:border-box;align-self:center;max-height:62vh;overflow-y:auto;margin:0;font-size:clamp(14px,1.9vw,34px);font-weight:800;line-height:1.1;text-align:center;scrollbar-width:none}
body.proj.hast h2.aq{margin-top:13vh;max-height:54vh}
.aqt{grid-column:1/-1;text-align:left;color:#fde047;font-size:.9em;font-weight:800;margin-top:.6vh;border-bottom:1px solid rgba(255,255,255,.25)}
.aqc{padding:.8vh .5vw;border-radius:12px;background:rgba(255,255,255,.12);border:2px solid rgba(255,255,255,.22)}.aqc small{display:block;color:#fde047;font-size:.55em;font-weight:700;margin-bottom:.2vh}
.aqc.got{border-color:#60a5fa}.aqc.ok{border-color:#22c55e;background:rgba(34,197,94,.18)}.aqc.no{border-color:#ef4444;background:rgba(239,68,68,.18)}.aqc .qa{display:block;color:#34d399;font-size:.8em}
.qi{text-align:center;margin:1.6vh 0;padding:1.6vh 1.6vw;border-radius:16px;background:rgba(255,255,255,.12);border:2px solid rgba(255,255,255,.25)}
.qi small{display:block;color:#fde047;font-size:.42em;font-weight:700;letter-spacing:.04em;margin-bottom:.3vh}
.qi .qa{color:#34d399;margin-left:.6em;white-space:nowrap}
#rpq{display:none;font-size:clamp(22px,3.4vw,56px);font-weight:800;color:#fde047;margin:4vh auto 0;max-width:85vw;line-height:1.15}
body:not(.proj) #app{display:block;max-width:none;width:100%;box-sizing:border-box;padding:12px 2vw}body:not(.proj) #tabs,body:not(.proj) #gen{max-width:none;box-sizing:border-box;padding-left:2vw;padding-right:2vw}body:not(.proj) header{padding-left:2vw;padding-right:2vw}body:not(.proj) .card{box-sizing:border-box;min-height:calc(100vh - 230px)}body:not(.proj) #bysec .nm{gap:10px 12px}body:not(.proj) #bysec .nm span{font-size:clamp(14px,1.6vw,26px);padding:6px 16px}body:not(.proj) #bysec h4{font-size:clamp(18px,2.2vw,34px);margin-bottom:12px}html,body{min-height:100vh}
body:not(.proj) #side,body:not(.proj) #join,body:not(.proj) #cnt,body:not(.proj) #q,body:not(.proj) #tm,body:not(.proj) #res,body:not(.proj) #pickbar,body:not(.proj) .ctl,body:not(.proj) #ed,body:not(.proj) #app hr{display:none}
body:not(.proj) #fab,body:not(.proj) #gear{display:none!important}
header #jn{margin-right:14px;color:#fff;opacity:.95}
#bysec h4{font-size:20px;margin:0 0 12px}#bysec .nm{gap:10px}#bysec .nm span{font-size:16px;padding:6px 14px}
#bysec .nm .sel{outline:3px solid var(--ac2);font-weight:700}
#spb{grid-template-columns:1fr;max-width:560px;margin-left:auto;margin-right:auto}
body.proj.idle #q,body.proj.idle #tm,body.proj.idle #res,body.proj.idle #pickbar,body.proj.idle #cnt{display:none}
<style>/* ===== host dashboard redesign (Projector view untouched) ===== */
:root{--glass:rgba(255,255,255,.72);--glass-line:rgba(255,255,255,.95)}
@media(prefers-color-scheme:dark){:root{--glass:rgba(29,25,66,.72);--glass-line:rgba(255,255,255,.12)}}
body:not(.proj){background:linear-gradient(160deg,#f5f0ff 0%,#fff0f8 45%,#e8fbff 100%);background-attachment:fixed}
@media(prefers-color-scheme:dark){body:not(.proj){background:linear-gradient(160deg,#120f2b 0%,#1a1040 55%,#0e1a35 100%)}}
body:not(.proj)::before{content:'';position:fixed;inset:-20%;z-index:-1;pointer-events:none;filter:blur(90px);opacity:.5;animation:drift 26s ease-in-out infinite alternate;background:radial-gradient(circle at 12% 18%,#f472b6 0,transparent 30%),radial-gradient(circle at 88% 12%,#22d3ee 0,transparent 30%),radial-gradient(circle at 78% 88%,#a78bfa 0,transparent 34%),radial-gradient(circle at 18% 86%,#fbbf24 0,transparent 24%)}
@keyframes hue{to{background-position:100% 0}}
/* header */
body:not(.proj) header{position:sticky;top:0;z-index:20;padding:14px 2vw;border-radius:0 0 28px 28px;background:linear-gradient(110deg,#6d28d9,#c026d3,#ec4899,#f97316)!important;background-size:230% 100%!important;animation:hue 14s ease-in-out infinite alternate;box-shadow:0 12px 36px rgba(192,38,211,.4)}
header b{display:flex;align-items:center;gap:14px;font-size:clamp(20px,2vw,30px);line-height:1.1}
header b .lg{width:58px;height:58px;flex:none;border-radius:50%;display:grid;place-items:center;background:none;box-shadow:0 0 0 2px rgba(255,255,255,.85),0 6px 16px rgba(0,0,0,.28)}header b .lg img{display:block;width:100%;height:100%;border-radius:50%}
header b .ttl{flex:1 1 auto;min-width:0;font-size:clamp(18px,2.7vw,40px);line-height:1.1;letter-spacing:-.01em}
header b small{display:block;margin-top:3px;font-size:11px;font-weight:700;letter-spacing:.18em;text-transform:uppercase;opacity:.85}
header #jn{padding:9px 18px;border-radius:99px;background:rgba(255,255,255,.2);border:1px solid rgba(255,255,255,.4);backdrop-filter:blur(8px);margin-right:6px}
header button.p{border-radius:99px;padding:11px 22px;font-size:15px}
/* tabs */
body:not(.proj) #tabs{padding:20px 2vw 0;gap:10px}
body:not(.proj) #tabs button{--g:linear-gradient(135deg,#7c3aed,#ec4899);display:flex;align-items:center;gap:9px;padding:11px 22px;font-size:16px;font-weight:700;border-radius:99px;color:var(--ink);background:var(--glass);border:2px solid var(--glass-line);backdrop-filter:blur(8px);box-shadow:0 4px 14px rgba(124,58,237,.1)}
body:not(.proj) #tabs button::before{content:'';width:11px;height:11px;border-radius:50%;background:var(--g)}
body:not(.proj) #tabs button:nth-child(4n+2){--g:linear-gradient(135deg,#06b6d4,#3b82f6)}
body:not(.proj) #tabs button:nth-child(4n+3){--g:linear-gradient(135deg,#f59e0b,#ef4444)}
body:not(.proj) #tabs button:nth-child(4n+4){--g:linear-gradient(135deg,#10b981,#84cc16)}
body:not(.proj) #tabs button.on{background:var(--g)!important;color:#fff;border-color:transparent;transform:translateY(-2px);box-shadow:0 12px 28px rgba(124,58,237,.35)}
body:not(.proj) #tabs button.on::before{background:#fff}
/* toolbar */
body:not(.proj) #gen{margin:16px 2vw 0;padding:14px 18px;gap:10px 14px;width:auto;box-sizing:border-box;border-radius:26px;background:var(--glass);border:2px solid var(--glass-line);backdrop-filter:blur(12px);box-shadow:var(--shadow)}
#gen .mute{font-size:13px;font-weight:800;letter-spacing:.02em;color:var(--ink)}
#gen select{-webkit-appearance:none;appearance:none;padding:10px 40px 10px 16px;border-radius:99px;font-size:15px;font-weight:600;cursor:pointer;color:var(--ink);border:2px solid var(--line);background:var(--card) url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='%237c3aed' stroke-width='3' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M6 9l6 6 6-6'/%3E%3C/svg%3E") no-repeat right 14px center}
#gen select:hover{border-color:var(--ac)}
#gen button{padding:11px 18px;border-radius:99px;font-size:15px;color:var(--ink);background:var(--card);border:2px solid var(--line)}
#gen button.p{padding:13px 26px;font-size:17px;color:#fff;border-color:transparent;background:linear-gradient(110deg,#7c3aed,#ec4899,#f97316);background-size:220% 100%;animation:hue 7s ease-in-out infinite alternate;box-shadow:0 10px 26px rgba(236,72,153,.45)}
#gen #rleft{margin-left:auto;padding:8px 16px;border-radius:99px;background:rgba(124,58,237,.12);color:var(--ac);font-weight:700}#gen #rleft:empty{display:none}
/* main panel */
body:not(.proj) #app{padding:18px 2vw 28px}
body:not(.proj) .card{min-height:calc(100vh - 300px);padding:clamp(18px,2.4vw,34px);border-radius:32px;background:var(--glass);border:2px solid var(--glass-line);backdrop-filter:blur(14px);box-shadow:0 20px 56px rgba(124,58,237,.16)}
/* class panel */
#bysec{margin:0}
#bysec .bh{display:flex;align-items:flex-end;justify-content:space-between;gap:20px;flex-wrap:wrap}
#bysec .bt small{display:block;font-size:12px;font-weight:800;letter-spacing:.18em;text-transform:uppercase;color:var(--mute)}
body:not(.proj) #bysec h4{margin:2px 0 0;font-size:clamp(28px,3.2vw,50px);font-weight:900;letter-spacing:-.02em;line-height:1.1;background:linear-gradient(110deg,#6d28d9,#ec4899,#f97316);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
#bysec .stats{display:flex;gap:12px;flex-wrap:wrap}
#bysec .st{min-width:104px;padding:10px 20px;border-radius:20px;text-align:center;background:var(--card);border:2px solid var(--line);box-shadow:0 4px 14px rgba(124,58,237,.08)}
#bysec .st b{display:block;font-size:clamp(24px,2.5vw,36px);font-weight:900;line-height:1.1}
#bysec .st span{font-size:11px;font-weight:800;letter-spacing:.08em;text-transform:uppercase;color:var(--mute)}
#bysec .st.g{background:linear-gradient(135deg,#10b981,#84cc16);border-color:transparent;box-shadow:0 10px 24px rgba(16,185,129,.35)}
#bysec .st.y{background:linear-gradient(135deg,#f59e0b,#f97316);border-color:transparent;box-shadow:0 10px 24px rgba(245,158,11,.35)}
#bysec .st.v{background:linear-gradient(135deg,#7c3aed,#ec4899);border-color:transparent;box-shadow:0 10px 24px rgba(236,72,153,.35)}
#bysec .st.g b,#bysec .st.g span,#bysec .st.y b,#bysec .st.y span,#bysec .st.v b,#bysec .st.v span{color:#fff}
#bysec .pg{height:12px;margin:20px 0 24px;border-radius:99px;overflow:hidden;background:rgba(124,58,237,.12)}
#bysec .pg i{display:block;height:100%;border-radius:99px;background:linear-gradient(90deg,#06b6d4,#10b981,#84cc16);transition:width .5s}
#bysec .nm{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:14px;margin:0}
#bysec .nm>div{display:flex;align-items:center;gap:12px;min-width:0;padding:12px 14px;border-radius:22px;background:var(--card);color:var(--ink);border:2px solid var(--line);box-shadow:0 4px 14px rgba(124,58,237,.07);transition:transform .15s,box-shadow .15s}
#bysec .nm>div:hover{transform:translateY(-3px);box-shadow:0 12px 26px rgba(124,58,237,.18)}
#bysec .av{flex:none;width:48px;height:48px;border-radius:17px;display:grid;place-items:center;font-style:normal;font-size:21px;font-weight:800;color:#fff;background:linear-gradient(135deg,hsl(var(--h) 85% 58%),hsl(var(--h2) 85% 52%));box-shadow:0 6px 14px hsl(var(--h) 85% 55%/.4)}
#bysec .tx{display:flex;flex-direction:column;gap:2px;min-width:0;font-weight:400}
#bysec .tx b{font-size:clamp(15px,1.15vw,19px);font-weight:700;line-height:1.2}
#bysec .tx em{font-style:normal;font-size:12px;font-weight:700;letter-spacing:.04em;color:var(--mute)}
#bysec .nm>div.on{border-color:#10b981;background:linear-gradient(135deg,rgba(16,185,129,.16),var(--card) 65%);box-shadow:0 8px 22px rgba(16,185,129,.22)}
#bysec .nm>div.on em{color:#059669}#bysec .nm>div.on em::before{content:'● '}
#bysec .nm>div.off{opacity:.6}#bysec .nm>div.off .av{filter:grayscale(.85)}
#bysec .nm>div.fin{border-color:#f59e0b;background:linear-gradient(135deg,rgba(245,158,11,.22),var(--card) 65%);box-shadow:0 8px 22px rgba(245,158,11,.25)}
#bysec .nm>div.fin em{color:#d97706}
#bysec .nm>div.sel{opacity:1;border-color:#ec4899;animation:glow 1.6s ease-in-out infinite;outline:0}
@keyframes glow{50%{box-shadow:0 0 0 6px rgba(236,72,153,.22),0 14px 30px rgba(236,72,153,.4)}}
#bysec .nm>div.sel em{color:#db2777}
#bysec .sc,#bysec .nz{margin-left:auto;flex:none;text-decoration:none;padding:4px 11px;border-radius:99px;font-size:13px;font-weight:800;background:rgba(124,58,237,.12);color:var(--ac)}
#bysec .nz+.sc,#bysec .sc+.nz{margin-left:6px}#bysec .nz{background:rgba(239,68,68,.14);color:#dc2626}
</style>
<style>/* ===== team mode ===== */
#tmb{display:none}body.proj #tmb{display:block;position:fixed;right:3vw;bottom:calc(3vh + 12.2em);z-index:10;font-size:clamp(14px,1.4vw,20px);font-weight:700;padding:10px 20px;border-radius:99px;background:rgba(14,165,233,.5);color:#fff;border:1px solid rgba(255,255,255,.3);backdrop-filter:blur(6px)}
#tstrip{display:none}body.proj #tstrip.has{display:flex;position:fixed;top:2.2vh;left:50%;transform:translateX(-50%);max-width:56vw;flex-wrap:wrap;justify-content:center;gap:.6vh .7vw;z-index:6}
.tsc{padding:.5vh 1vw;border-radius:99px;background:rgba(255,255,255,.14);border:1px solid rgba(255,255,255,.3);backdrop-filter:blur(6px);color:#fff;font-size:clamp(12px,1.3vw,21px);font-weight:700;white-space:nowrap}
.tsc i{font-style:normal;margin-right:.3em}.tsc b{color:#fde047;margin-left:.3em}.tsc em{font-style:normal;color:#34d399;margin-left:.3em;font-size:.85em}.tsc.r1{border-color:#fbbf24;background:rgba(251,191,36,.2)}
#tmo{display:none;position:fixed;inset:0;z-index:32;background:rgba(10,8,30,.94);backdrop-filter:blur(8px);align-items:center;justify-content:center;color:#fff;padding:3vh 3vw}#tmo.on{display:flex}
.tmw{width:100%;max-width:1300px;max-height:94vh;overflow-y:auto;text-align:center}#tmo .mute{color:#b9bce0}
#tmt{font-size:clamp(22px,2.8vw,42px);font-weight:800}
.tmhd{margin-bottom:12px}#tmsub{font-size:15px;color:#b9bce0;margin-top:4px}
.tmtop{display:grid;grid-template-columns:3fr 2fr;gap:14px;text-align:left;margin-bottom:16px}@media(max-width:820px){.tmtop{grid-template-columns:1fr}}
.tmcard{padding:16px 18px;border-radius:18px;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.16)}
.tmct{font-size:18px;font-weight:800;margin-bottom:10px;display:flex;align-items:center;gap:10px}
.tmstep{display:inline-flex;width:26px;height:26px;border-radius:50%;background:var(--grad);align-items:center;justify-content:center;font-size:14px}
.tmlab{font-size:12px;font-weight:800;letter-spacing:.08em;text-transform:uppercase;color:#b9bce0;margin:4px 0 6px}
.tmszr{display:flex;gap:8px;flex-wrap:wrap}.tmszr button{min-width:52px;padding:10px 0;font-size:20px;font-weight:800;border-radius:12px;background:rgba(255,255,255,.14);color:#fff;border-color:transparent}.tmszr button.cur{outline:3px solid #fbbf24;background:rgba(251,191,36,.18)}
.tmhint{font-size:14px;color:#fde047;margin:8px 0 10px;min-height:18px}
.tmrow{margin:12px 0 0}.tmrow button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}.tmrow button.p{background:var(--grad)}.tmrow button.big{width:100%;padding:14px 16px;font-size:18px;font-weight:800;border-radius:14px}
.tmnote{font-size:13px;color:#b9bce0;margin:6px 2px 0}
.tmgoal{border-top:1px solid rgba(255,255,255,.12);padding-top:12px}
#tmgl{width:76px;padding:6px 8px;font-size:16px;font-weight:700;color:#111;background:#fff;border-radius:10px;text-align:center}
.tmfoot{display:flex;flex-wrap:wrap;gap:14px 22px;align-items:flex-end;justify-content:center;margin-top:20px;padding-top:16px;border-top:1px solid rgba(255,255,255,.14)}
.tmgrp{display:flex;gap:8px;align-items:center;flex-wrap:wrap}.tmgrp .tmlab{margin:0 4px 0 0}
.tmfoot button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}.tmfoot button.p{background:var(--grad)}.tmfoot button.dng{background:rgba(220,38,38,.22);color:#fecaca}
.tmclose{margin-left:auto}
.tmbar{display:flex;gap:10px;align-items:center;justify-content:center;flex-wrap:wrap;margin:14px 0}
.tmbar button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}.tmbar button.p{background:var(--grad)}.tmbar button.cur{outline:2px solid #fbbf24}
.tmck{font-size:14px;display:flex;gap:6px;align-items:center;margin:0;color:#fff}.tmck input{width:auto}
#tmg{display:grid;grid-template-columns:repeat(auto-fill,minmax(270px,1fr));gap:14px;text-align:left}
.tmc2{padding:14px;border-radius:18px;background:rgba(255,255,255,.1);border:2px solid rgba(255,255,255,.22)}
.tmn{font-size:20px;font-weight:800}.tmn .tmr{color:#fbbf24}.tmn button{padding:2px 8px;background:transparent;color:#fff;border:0;opacity:.6}
.tmpts{font-size:15px;margin:4px 0 8px;color:#b9bce0}.tmpts b{font-size:30px;color:#fde047}.tmpts em{font-style:normal;color:#34d399;font-weight:700}
.tmm{display:flex;flex-wrap:wrap;gap:6px}.tmch{padding:3px 10px;border-radius:99px;background:rgba(255,255,255,.12);font-size:13px;cursor:pointer}.tmch.sel{background:#ec4899;outline:2px solid #fbbf24}
.tma{display:flex;gap:6px;flex-wrap:wrap;margin-top:10px}.tma button{padding:5px 10px;color:#fff;border-color:transparent;background:rgba(255,255,255,.14)}.tma button.g{background:#059669}.tma button.rd{background:#dc2626}
#tmf{margin-top:16px;text-align:left}#tmh{overflow:auto;max-height:40vh}
.tmht{margin:18px auto 0;border-collapse:collapse;font-size:14px}.tmht th,.tmht td{padding:6px 12px;border:1px solid rgba(255,255,255,.18)}.tmht tr.tot td{font-weight:800;color:#fde047}.tmc2.done{border-color:#22c55e;box-shadow:0 0 0 2px rgba(34,197,94,.45)}.tmrel{margin-top:10px;width:100%;background:#16a34a;color:#fff;font-weight:800}.tmlf{background:rgba(34,197,94,.18)}.tmlf button{padding:0 6px;margin-left:4px}.tmok{font-size:.55em;font-weight:800;color:#86efac;background:rgba(34,197,94,.18);padding:2px 8px;border-radius:99px;vertical-align:middle}
</style><style>/* ===== team scoreboard (projected to the class) ===== */
#tsbb{display:none}body.proj.hast #tsbb{display:block;position:fixed;right:3vw;bottom:calc(3vh + 19.8em);z-index:10;font-size:clamp(14px,1.4vw,20px);font-weight:700;padding:10px 20px;border-radius:99px;background:rgba(124,58,237,.65);color:#fff;border:1px solid rgba(255,255,255,.3);backdrop-filter:blur(6px)}
body.proj.bossonly #tsbb{display:none!important}
#tsb{display:none;position:fixed;inset:0;z-index:33;background:rgba(10,8,30,.97);backdrop-filter:blur(8px);color:#fff;padding:3vh 3vw;flex-direction:column;align-items:center}#tsb.on{display:flex}
#tsb .tsh{width:100%;max-width:1500px;display:flex;align-items:center;justify-content:space-between;gap:2vw}
#tst{font-size:clamp(26px,3.6vw,64px);font-weight:800;line-height:1.1}
#tssub{font-size:clamp(13px,1.35vw,24px);color:#b9bce0;margin-top:.6vh}
#tsx{background:rgba(255,255,255,.14);color:#fff;border:1px solid rgba(255,255,255,.3);border-radius:99px;padding:10px 20px;font-size:clamp(14px,1.3vw,20px);font-weight:700;opacity:.6;cursor:pointer;white-space:nowrap}#tsx:hover{opacity:1}
#tsl{width:100%;max-width:1500px;height:76vh;margin-top:2.4vh;display:grid;grid-template-columns:repeat(var(--c,1),minmax(0,1fr));grid-template-rows:repeat(var(--r,1),minmax(0,1fr));gap:1.2vh 1.6vw;grid-auto-flow:row}
.tsr{display:flex;align-items:center;gap:1.4vw;padding:0 1.6vw;border-radius:2.2vh;background:rgba(255,255,255,.08);border:2px solid rgba(255,255,255,.18);min-height:0;overflow:hidden}
.tsr.r1{background:rgba(251,191,36,.16);border-color:#fbbf24}.tsr.lf{opacity:.78;border-color:rgba(34,197,94,.7)}
.tsr.up{animation:tsup 1.4s ease-out}@keyframes tsup{0%{box-shadow:0 0 0 0 rgba(52,211,153,.9);background:rgba(52,211,153,.35)}100%{box-shadow:0 0 0 2.4vh rgba(52,211,153,0)}}
.tsk{flex:0 0 auto;min-width:2.2em;text-align:center;font-weight:800;color:#fbbf24;font-size:clamp(20px,min(3.4vw,calc(76vh / var(--r,1) * .46)),74px)}
.tsm{flex:1 1 auto;min-width:0}
.tsn{font-weight:800;line-height:1.1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-size:clamp(16px,min(2.6vw,calc(76vh / var(--r,1) * .3)),54px)}
.tsx{font-size:.5em;font-weight:800;color:#86efac;background:rgba(34,197,94,.2);padding:.15em .6em;border-radius:99px;vertical-align:middle}
.tsbar{height:max(6px,calc(76vh / var(--r,1) * .1));margin:.7vh 0 .5vh;border-radius:99px;background:rgba(255,255,255,.14);overflow:hidden}
.tsbar i{display:block;height:100%;border-radius:99px;background:linear-gradient(90deg,#7c3aed,#ec4899);transition:width .8s ease}.tsr.r1 .tsbar i{background:linear-gradient(90deg,#f59e0b,#fde047)}.tsr.lf .tsbar i{background:#22c55e}
.tsmem{color:#b9bce0;font-size:clamp(11px,min(1.1vw,calc(76vh / var(--r,1) * .16)),20px);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.tsp{flex:0 0 auto;text-align:right;white-space:nowrap;min-width:min(17vw,calc(76vh / var(--r,1) * 1.7))}
.tsp b{color:#fde047;font-weight:800;line-height:1;font-size:clamp(24px,min(4.6vw,calc(76vh / var(--r,1) * .56)),96px)}
.tsp small{color:#b9bce0;font-size:clamp(12px,min(1.5vw,calc(76vh / var(--r,1) * .2)),28px);margin-left:.3em}
.tsp em{font-style:normal;color:#34d399;font-weight:800;margin-left:.35em;font-size:clamp(14px,min(2vw,calc(76vh / var(--r,1) * .26)),38px)}
.tse{margin:auto;text-align:center;color:#b9bce0;font-size:clamp(18px,2.2vw,36px)}
</style><style>/* ===== play modes: individual / team / class ===== */
#modes{display:inline-flex;gap:6px}
#gen button.mb.cur{background:linear-gradient(135deg,#7c3aed,#ec4899);color:#fff;border-color:transparent;box-shadow:0 6px 16px rgba(236,72,153,.4)}
#cmb{display:none}body.proj #cmb{display:block;position:fixed;right:3vw;bottom:calc(3vh + 16em);z-index:10;font-size:clamp(14px,1.4vw,20px);font-weight:700;padding:10px 20px;border-radius:99px;background:rgba(239,68,68,.5);color:#fff;border:1px solid rgba(255,255,255,.3);backdrop-filter:blur(6px)}
#clo{display:none;position:fixed;inset:0;z-index:32;background:rgba(10,8,30,.94);backdrop-filter:blur(8px);align-items:center;justify-content:center;color:#fff;padding:3vh 3vw}#clo.on{display:flex}
#clo .tmw{max-width:760px;width:100%;max-height:94vh;overflow-y:auto;text-align:center}#clo .mute{color:#b9bce0}
#clt{font-size:clamp(22px,2.8vw,42px);font-weight:800}
.clbig{font-size:clamp(26px,3.4vw,52px);font-weight:800;margin:14px 0 4px}
.clf{display:grid;grid-template-columns:1fr 1fr;gap:12px 18px;text-align:left;margin:18px 0}
.clf label{display:flex;flex-direction:column;gap:4px;font-size:14px;color:#e5e7fb;margin:0}
.clf input,.clf select{padding:10px;font-size:16px;background:rgba(0,0,0,.35);color:#fff;border:2px solid rgba(255,255,255,.25);border-radius:12px}
.clf label.ck{flex-direction:row;align-items:center;grid-column:1/-1;gap:8px}.clf label.ck input{width:auto}
#clo button{background:rgba(255,255,255,.14);color:#fff;border-color:transparent}#clo button.p{background:var(--grad)}
#qtm:disabled,#qts:disabled,#qbb:disabled{opacity:.4!important;cursor:not-allowed!important;filter:grayscale(.7);transform:none!important;box-shadow:none!important}
#clo .tmw{max-width:900px}#clb{text-align:left}
.clintro{text-align:center;margin:6px 0 14px}
.clsec{padding:14px 16px;border-radius:16px;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.15);margin:0 0 12px}
.clsec .tmct{margin-bottom:10px}.clsec .clf{margin:10px 0 0}.clsec .tmlab{margin-top:0}
.clrow{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-bottom:12px;align-items:start}.clrow .clsec{margin:0}
@media(max-width:760px){.clrow{grid-template-columns:1fr}}
.clcol{grid-template-columns:1fr!important}
.clf small,.cltog small{font-weight:400;color:#b9bce0;font-size:12.5px;line-height:1.3}
.clchips{display:flex;flex-wrap:wrap;gap:8px}
.clchip{cursor:pointer}.clchip input{display:none}.clchip span{display:inline-block;padding:8px 14px;border-radius:99px;background:rgba(255,255,255,.1);border:2px solid transparent;font-weight:700;font-size:15px}
.clchip input:checked+span{background:rgba(52,211,153,.2);border-color:#34d399}.clchip input:checked+span::before{content:"✓ "}
.clq2{display:flex;gap:6px;margin:0 0 10px}#clo button.mini{padding:4px 12px;font-size:12px;border-radius:99px}
.clseg{display:flex;gap:8px;flex-wrap:wrap;align-items:center}.clseg button{padding:8px 12px;border-radius:12px;font-weight:700}#clo .clseg button.cur{outline:3px solid #fbbf24;background:rgba(251,191,36,.18)}
.clseg input{width:78px;padding:9px;font-size:16px;background:rgba(0,0,0,.35);color:#fff;border:2px solid rgba(255,255,255,.25);border-radius:12px}
.cltog{display:flex;gap:12px;align-items:flex-start;padding:10px 0;cursor:pointer}.cltog+.cltog{border-top:1px solid rgba(255,255,255,.12)}.cltog input{width:22px;height:22px;margin-top:2px;flex:none}.cltog b{display:block}.cltog small{display:block}
details.clsec>summary{cursor:pointer;font-weight:800;display:flex;align-items:center;gap:10px;list-style:none}details.clsec>summary::-webkit-details-marker{display:none}details.clsec>summary small{font-weight:400;color:#b9bce0}
details.clsec>summary::after{content:"▸";margin-left:auto}details.clsec[open]>summary::after{content:"▾"}
.clsec details{margin:0!important}
details.clsec:not([open])>summary{margin-bottom:0}
.clsm{font-weight:400;font-size:14px;color:#b9bce0;margin-left:4px;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#clo .clchip span,#clo .cltog b{color:#fff}
.clfoot{position:sticky;bottom:0;display:flex;gap:10px;justify-content:center;padding:18px 0 4px;background:linear-gradient(rgba(10,8,30,0),rgba(10,8,30,.97) 35%)}
#clo #clstart{padding:14px 30px;font-size:18px;font-weight:800;border-radius:14px}
</style>
<style>/* ===== podium ===== */
#pod{display:none;position:fixed;inset:0;z-index:10000;background:rgba(10,8,30,.93);backdrop-filter:blur(8px);color:#fff;flex-direction:column;align-items:center;justify-content:flex-end;padding:4vh 4vw 0;cursor:pointer;text-align:center}
#pod.on{display:flex}
#pod .pt{font-size:clamp(28px,4.4vw,70px);font-weight:900;text-shadow:0 0 40px rgba(251,191,36,.6)}
#pod .ps{color:#b9bce0;font-size:clamp(14px,1.8vw,26px);margin:.6vh 0 auto}
#pod .pc{display:flex;align-items:flex-end;justify-content:center;gap:1.4vw;width:min(92vw,1100px)}
#pod .pcol{flex:1;display:flex;flex-direction:column;align-items:center;min-width:0}
#pod .pn{display:flex;flex-direction:column;align-items:center;margin-bottom:1vh;opacity:0;font-size:clamp(40px,6vw,90px);animation:pfade .6s both}
#pod .pn b{font-size:clamp(18px,2.8vw,44px);overflow-wrap:anywhere}#pod .pn span{font-size:clamp(14px,1.8vw,28px);color:#fde047}
#pod .pbar{width:100%;height:0;border-radius:18px 18px 0 0;display:grid;place-items:start center;animation:prise .8s ease-out both}
#pod .pbar em{font-style:normal;font-size:clamp(30px,5vw,80px);font-weight:900;color:rgba(0,0,0,.45);padding-top:1vh}
#pod .ph{position:absolute;bottom:1vh;font-size:12px;color:#8b8eb8}
@keyframes prise{from{height:0}to{height:var(--h)}}@keyframes pfade{from{opacity:0;transform:translateY(20px) scale(.7)}to{opacity:1;transform:none}}
</style>
<style>/* ===== host dashboard v2 (dashboard only, projector view untouched) ===== */
body:not(.proj) header{padding:12px 2vw}
header>button{padding:10px 18px!important;font-size:15px;font-weight:700}
body:not(.proj) #tabs{padding:18px 2vw 0}
body:not(.proj) #gen{display:flex;flex-wrap:wrap;align-items:flex-end;gap:14px 24px;padding:16px 22px}
#gen .gp{display:flex;flex-direction:column;gap:6px;min-width:0}
#gen .gp>label{margin:0;font-size:11px;font-weight:800;letter-spacing:.1em;text-transform:uppercase;color:var(--mute)}
#gen .gp-r{margin-left:auto;align-items:flex-end}
#gen label.chk{display:flex;align-items:center;gap:8px;font-size:14px;font-weight:700;letter-spacing:0;text-transform:none;color:var(--ink);cursor:pointer}
#gen label.chk input{width:auto}
#gen #rleft{margin-left:0}
#gen .gact{display:flex;gap:10px;align-items:center}
#modes{display:inline-flex;padding:4px;border-radius:99px;background:rgba(124,58,237,.1);gap:2px}
#gen #modes button:not(.cur){border-color:transparent;background:transparent;box-shadow:none}
#gen #modes button{padding:9px 16px}
body:not(.proj) #app{display:grid;grid-template-columns:minmax(0,1fr) 330px;gap:20px;align-items:start;padding:18px 2vw 36px}
body:not(.proj) #app>.card{min-height:55vh}
#dock{display:none}
body:not(.proj) #dock{display:flex;flex-direction:column;gap:14px;position:sticky;top:106px}
.dk{padding:16px 18px;border-radius:24px;background:var(--glass);border:2px solid var(--glass-line);box-shadow:var(--shadow);backdrop-filter:blur(12px)}
.dk h5{margin:0 0 10px;font-size:11px;font-weight:800;letter-spacing:.14em;text-transform:uppercase;color:var(--mute)}
.jurl{font-size:clamp(17px,1.5vw,22px);font-weight:900;word-break:break-all;background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.qa{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.qa button{display:flex;flex-direction:column;align-items:center;gap:4px;padding:12px 6px;border-radius:16px;font-size:13px;font-weight:700;background:var(--card);border:2px solid var(--line)}
.qa button i{font-style:normal;font-size:22px}
.qa:not(.two) button:first-child{grid-column:1/-1;flex-direction:row;justify-content:center;gap:10px;font-size:16px;color:#fff;border-color:transparent;background:linear-gradient(110deg,#7c3aed,#ec4899,#f97316)}
.lg2{display:grid;grid-template-columns:1fr 1fr;gap:8px 12px;font-size:13px;font-weight:600}.lg2 i{display:inline-block;width:12px;height:12px;border-radius:50%;margin-right:7px;vertical-align:-1px}
#bysec .nm>div.off{opacity:.8}#bysec .nm>div.off .av{filter:grayscale(.45)}
#bysec .gh{display:flex;align-items:center;gap:10px;margin:24px 0 12px;font-size:clamp(16px,1.5vw,22px);font-weight:800;color:var(--ink)}#bysec .gh::after{content:'';flex:1;height:2px;border-radius:2px;background:var(--line)}#bysec .gh b{padding:2px 12px;border-radius:99px;font-size:.85em;background:rgba(124,58,237,.12);color:var(--ac)}#bysec .gh.on b{background:rgba(16,185,129,.18);color:#059669}#bysec .ge{padding:14px 18px;border-radius:16px;border:2px dashed var(--line);color:var(--mute);font-weight:600}
#mro>.card,#lfo>.card{background:var(--card);backdrop-filter:none;min-height:0;color:var(--ink)}
#bysec .tx b{font-size:clamp(14px,1vw,17px)}
#bysec .nm{grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:10px}
#bysec .nm>div{position:relative;padding:7px 12px;gap:10px;border-radius:16px}
#bysec .av{width:38px;height:38px;border-radius:13px;font-size:17px}
#bysec .tx{flex:1}
#bysec .dt{flex:none;order:3;width:14px;height:14px;border-radius:50%;text-decoration:none;box-shadow:0 0 0 3px rgba(255,255,255,.85)}
#bysec .dt.g{background:#22c55e;box-shadow:0 0 0 3px rgba(34,197,94,.25),0 0 8px rgba(34,197,94,.7)}
#bysec .dt.r{background:#ef4444;box-shadow:0 0 0 3px rgba(239,68,68,.22)}
#bysec .nm>div .sc,#bysec .nm>div .nz{order:2}
#bysec .nm>div,#bysec .nm>div.on,#bysec .nm>div.fin{color:var(--ink)!important}#bysec .nm>div.off .tx b{color:var(--mute)}
@media(max-width:1150px){body:not(.proj) #app{grid-template-columns:1fr}body:not(.proj) #dock{position:static;display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr))}}
</style>
<style>/* ===== 6 to 13 students at once ===== */
#rpn.ng{display:grid;grid-template-columns:repeat(var(--cols,3),minmax(0,1fr));gap:1.6vh 1.4vw;width:min(94vw,1500px);margin:0 auto;padding:0;line-height:1.1;align-items:stretch}
#rpn.ng2{--cols:2;font-size:clamp(18px,min(3.4vw,6vh),60px)}
#rpn.ng3{--cols:3;font-size:clamp(16px,min(2.6vw,5vh),46px)}
#rpn.ng4{--cols:4;font-size:clamp(14px,min(2vw,4.4vh),38px)}
#rpn.ng .slot{display:flex;flex-direction:column;align-items:center;justify-content:center;padding:.4em .5em;border-radius:.4em;background:rgba(255,255,255,.1);border:.06em solid rgba(255,255,255,.28);box-shadow:0 6px 22px rgba(0,0,0,.3);overflow-wrap:break-word}
#rpn.ng .slot.done{background:rgba(251,191,36,.14);border-color:#fbbf24;transform:none}
#turn.cm{width:38vw;min-width:0;--fn:clamp(11px,min(1.1vw,1.9vh),17px);--fa:clamp(11px,min(1.2vw,2vh),19px)}
#turn.cm:not(.mixed) .ts{display:none}
#turn.cm #tt{font-size:clamp(26px,min(3.4vw,5.6vh),56px);margin-bottom:.8vh}
#turn.cm #tcards{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:.6vh .5vw}
#turn.cm .tc{padding:.5vh .5vw;margin-bottom:0;border-width:2px;border-radius:12px}
#turn.cm .tcc{margin-top:.3vh;gap:3px;opacity:.6}
#turn.cm .tcc input{padding:.3vh .4vw;font-size:min(12px,1.6vh)}
#turn.cm .tcc button{padding:.3vh .6vw;font-size:min(12px,1.6vh)}
#turn.cm .tl{font-size:.7em}
body.proj.hasturn.turncm #app{padding-left:41vw;padding-right:3vw}
body.proj.turncm:has(#fstrip.has) #app{padding-right:22vw}
body.proj h2.mq.m6{display:grid;grid-template-columns:repeat(auto-fill,minmax(15vw,1fr));gap:1vh .8vw;align-content:center;max-height:80vh;overflow-y:auto;scrollbar-width:none;font-size:clamp(14px,min(2vw,3.6vh),38px)}
body.proj h2.mq.m6 .qi{margin:0;padding:1vh .6vw}
</style><style>/* ===== settings panel ===== */
/* projector view: these actions live in the dashboard, so hide the floating buttons (keyboard shortcuts still work) */
#fab,#gear,#nzb,#cmb,#tmb,#hint{display:none!important}
#sp{background:radial-gradient(900px 500px at 15% 10%,rgba(124,58,237,.45),transparent 60%),radial-gradient(800px 500px at 90% 95%,rgba(236,72,153,.35),transparent 60%),rgba(14,9,40,.94)!important}
#sp>div{max-width:760px!important;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.16);border-radius:28px;padding:clamp(20px,3.5vh,40px) clamp(18px,3vw,40px);box-shadow:0 30px 80px rgba(0,0,0,.5),inset 0 1px 0 rgba(255,255,255,.12);backdrop-filter:blur(18px);animation:spin .28s ease-out}
@keyframes spin{from{opacity:0;transform:translateY(14px) scale(.98)}to{opacity:1;transform:none}}
#spt{font-size:clamp(22px,2.6vw,36px)!important;margin-bottom:2.2vh!important;background:linear-gradient(90deg,#fff,#f9a8d4,#c4b5fd);-webkit-background-clip:text;background-clip:text;color:transparent}
#spb{display:flex!important;justify-content:center;margin-bottom:2.4vh!important}
#spb button{font-size:15px!important;padding:8px 20px!important;border-radius:999px!important;background:rgba(251,191,36,.16)!important;border:1.5px solid #fbbf24!important;pointer-events:none}
#spm{margin-bottom:2.6vh!important;text-align:left}
.spg2{display:grid;grid-template-columns:1fr 1fr;gap:16px 18px}.spw,.spx{grid-column:1/-1}
.spf{display:flex;flex-direction:column;gap:7px;font-size:13px;font-weight:600;color:#cfd0f5;letter-spacing:.02em}
.spf select{appearance:none;-webkit-appearance:none;font-family:inherit;font-size:16px;font-weight:700;color:#fff;padding:13px 42px 13px 16px;border-radius:14px;border:1.5px solid rgba(255,255,255,.18);cursor:pointer;background:rgba(255,255,255,.1) url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='14' height='9' viewBox='0 0 14 9'%3E%3Cpath d='M1 1l6 6 6-6' fill='none' stroke='%23fff' stroke-width='2' stroke-linecap='round'/%3E%3C/svg%3E") no-repeat right 16px center;transition:.15s}
.spf select:hover{background-color:rgba(255,255,255,.16);border-color:rgba(255,255,255,.35)}
.spf select:focus{outline:none;border-color:#f472b6;box-shadow:0 0 0 4px rgba(244,114,182,.22)}
.spf select option{background:#1d1942;color:#fff}
.spx{display:flex;gap:14px;align-items:flex-end;flex-wrap:wrap}
.spn{display:flex;flex-direction:column;gap:6px;font-size:13px;font-weight:600;color:#cfd0f5}
.spn input{width:150px;font-family:inherit;font-size:16px;font-weight:700;padding:11px 14px;border-radius:12px;border:1.5px solid rgba(255,255,255,.25);background:#fff;color:#1e1b3a}
#spm .spr{margin-left:auto;font-size:14px!important;padding:11px 16px!important;background:transparent!important;border:1.5px dashed rgba(255,255,255,.3)!important;color:#cfd0f5!important}
#spm .spr:hover{background:rgba(239,68,68,.25)!important;border-color:#f87171!important;color:#fff!important}
#spf{display:flex;gap:12px;justify-content:center}
#sp #spf button{font-family:inherit;font-weight:800;border-radius:14px;cursor:pointer;transition:.15s;border:1.5px solid transparent}
#sp .spc{padding:14px 26px;font-size:16px;background:rgba(255,255,255,.1)!important;color:#fff;border-color:rgba(255,255,255,.2)!important}
#sp .spc:hover{background:rgba(255,255,255,.2)!important}
#sp .spg{padding:14px 34px;font-size:18px;background:linear-gradient(135deg,#7c3aed,#ec4899)!important;color:#fff;box-shadow:0 10px 28px rgba(236,72,153,.4)}
#sp .spg:hover{transform:translateY(-2px);box-shadow:0 14px 34px rgba(236,72,153,.55)}
@media(max-width:620px){.spg2{grid-template-columns:1fr}}
</style>
<style>/* ===== LIGHT THEME for the 3 settings screens: Individual (#sp), Team (#tmo), Class (#clo) ===== */
#sp,#tmo,#clo{color:#2a2347!important;backdrop-filter:blur(6px)}
/* ---------- Individual settings: lavender + pink ---------- */
#sp{background:radial-gradient(900px 500px at 15% 10%,rgba(167,139,250,.45),transparent 60%),radial-gradient(800px 500px at 90% 95%,rgba(244,114,182,.35),transparent 60%),rgba(246,243,255,.97)!important}
#sp>div{background:rgba(255,255,255,.85)!important;border:1px solid rgba(255,255,255,.95)!important;box-shadow:0 24px 60px rgba(80,60,140,.18),inset 0 1px 0 #fff!important}
#spt{background:linear-gradient(90deg,#6d28d9,#db2777)!important;-webkit-background-clip:text!important;background-clip:text!important;color:transparent!important}
#spb button{background:#fff4d6!important;border-color:#e8b84a!important;color:#4a3a14!important}
.spf,.spn{color:#5b5384!important}
.spf select{color:#2a2347!important;background-color:#faf8ff!important;border-color:#ddd5f3!important;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='14' height='9' viewBox='0 0 14 9'%3E%3Cpath d='M1 1l6 6 6-6' fill='none' stroke='%236b6290' stroke-width='2' stroke-linecap='round'/%3E%3C/svg%3E")!important;background-repeat:no-repeat!important;background-position:right 16px center!important}
.spf select:hover{background-color:#f3eeff!important;border-color:#c4b5fd!important}
.spf select:focus{border-color:#7c3aed!important;box-shadow:0 0 0 4px rgba(124,58,237,.18)!important}
.spf select option{background:#fff!important;color:#2a2347!important}
.spn input{background:#faf8ff!important;color:#2a2347!important;border-color:#ddd5f3!important}
#spm .spr{color:#6b6290!important;border-color:#c9bfe6!important}
#spm .spr:hover{background:#fee2e2!important;border-color:#f87171!important;color:#991b1b!important}
#sp .spc{background:#fff!important;color:#2a2347!important;border-color:#ddd5f3!important}
#sp .spc:hover{background:#f3eeff!important}
#sp .spg{box-shadow:0 10px 26px rgba(236,72,153,.3)!important}

/* ---------- Team settings: sky blue + mint ---------- */
#tmo{background:radial-gradient(900px 500px at 15% 10%,rgba(125,211,252,.5),transparent 60%),radial-gradient(800px 500px at 90% 95%,rgba(110,231,183,.4),transparent 60%),rgba(240,249,255,.97)}
#tmo .mute,#tmsub,#tmo .tmlab,#tmo .tmnote,#tmo .tmpts,#tmo .tmpts small{color:#4b6a85!important}
#tmo .tmct,#tmo .tmn,#tmo .tmck,#tmo b{color:#17324d}
#tmo .tmcard,#tmo .tmc2{background:rgba(255,255,255,.88);border:1px solid #cfe6f5;box-shadow:0 6px 18px rgba(14,116,144,.1)}
#tmo .tmc2{border-width:2px}#tmo .tmc2.done{border-color:#22c55e}
#tmo .tmstep{background:linear-gradient(135deg,#0891b2,#2563eb);color:#fff}
#tmo .tmhint{color:#b45309}
#tmo .tmszr button,#tmo .tmrow button,#tmo .tmfoot button,#tmo .tmbar button,#tmo .tma button{background:#e6f3fb;color:#17324d;border:1px solid #bcdcee}
#tmo .tmszr button:hover,#tmo .tmrow button:hover,#tmo .tmfoot button:hover,#tmo .tmbar button:hover,#tmo .tma button:hover{background:#d3eaf7}
#tmo .tmszr button.cur{outline:3px solid #f59e0b;background:#fff3d1}
#tmo .tmbar button.cur{outline:2px solid #f59e0b}
#tmo .tmrow button.p,#tmo .tmfoot button.p,#tmo .tmbar button.p{background:linear-gradient(135deg,#0891b2,#2563eb);color:#fff;border-color:transparent}
#tmo .tmfoot button.dng{background:#fee2e2;color:#991b1b;border-color:#fecaca}
#tmo .tma button.g{background:#059669;color:#fff;border-color:transparent}
#tmo .tma button.rd{background:#dc2626;color:#fff;border-color:transparent}
#tmo .tmrel{background:#16a34a;color:#fff}
#tmo .tmgoal,#tmo .tmfoot{border-color:#cfe6f5}
#tmo .tmpts b{color:#d97706}#tmo .tmpts em{color:#059669}
#tmo .tmn .tmr{color:#d97706}#tmo .tmn button{color:#17324d}
#tmo .tmch{background:#e6f3fb;color:#17324d}#tmo .tmch.sel{background:#2563eb;color:#fff;outline:2px solid #f59e0b}
#tmo .tmlf{background:#dcfce7}
#tmo .tmht th,#tmo .tmht td{border-color:#cfe6f5}#tmo .tmht tr.tot td{color:#b45309}
#tmo select,#tmo input[type=text],#tmo input[type=number]{background:#fff;color:#17324d;border:1.5px solid #bcdcee;border-radius:10px}

/* ---------- Class settings: peach + coral ---------- */
#clo{background:radial-gradient(900px 500px at 15% 10%,rgba(253,186,116,.5),transparent 60%),radial-gradient(800px 500px at 90% 95%,rgba(252,165,165,.4),transparent 60%),rgba(255,248,240,.97)}
#clo .mute,#clo .clf small,#clo .cltog small,#clo .clsm,details.clsec>summary small{color:#8a5a3c!important}
#clt,#clo .clbig,#clo b{color:#4a2410}
#clo .clf label{color:#5c3a24}
#clo .clf input,#clo .clf select,#clo .clseg input{background:#fff;color:#4a2410;border:1.5px solid #f3cfae}
#clo .clsec{background:rgba(255,255,255,.88);border:1px solid #f3d9bf;box-shadow:0 6px 18px rgba(194,65,12,.08)}
#clo .clchip span{background:#fff0e0;color:#4a2410;border-color:transparent}
#clo .clchip input:checked+span{background:#d1fae5;border-color:#10b981}
#clo .cltog+.cltog{border-color:#f3d9bf}
#clo button{background:#fff0e0;color:#4a2410;border:1px solid #f3cfae}
#clo button:hover{background:#ffe3c7}
#clo button.p,#clo #clstart{background:linear-gradient(135deg,#ea580c,#e11d48);color:#fff;border-color:transparent}
#clo .clseg button.cur{outline:3px solid #f59e0b;background:#fff3d1}
#clo .clchip span,#clo .cltog b{color:#4a2410}
.clfoot{background:linear-gradient(rgba(255,248,240,0),rgba(255,248,240,.97) 35%)!important}
</style>
<style>/* ===== LIGHT THEME for projector screens: Podium (#pod), Team scores (#tsb), Boss battle (#bossbar) ===== */
/* ---------- Podium: lavender + gold ---------- */
#pod{background:radial-gradient(900px 500px at 15% 10%,rgba(196,181,253,.55),transparent 60%),radial-gradient(800px 500px at 90% 95%,rgba(253,224,71,.35),transparent 60%),rgba(250,247,255,.97)!important;color:#2a2347!important}
#pod .pt{color:#2a2347;text-shadow:0 2px 24px rgba(245,158,11,.35)}
#pod .ps{color:#6b6290}
#pod .pn b{color:#2a2347}#pod .pn span{color:#b45309}
#pod .pbar em{color:rgba(42,35,71,.55)}
#pod .ph{color:#8b84b0}
/* ---------- Team scoreboard: sky blue + mint ---------- */
#tsb{background:radial-gradient(900px 500px at 15% 10%,rgba(125,211,252,.5),transparent 60%),radial-gradient(800px 500px at 90% 95%,rgba(110,231,183,.4),transparent 60%),rgba(240,249,255,.98)!important;color:#17324d!important}
#tst{color:#17324d}#tssub,.tse{color:#4b6a85}
#tsx{background:#fff;color:#17324d;border-color:#bcdcee}
.tsr{background:rgba(255,255,255,.9);border-color:#cfe6f5;color:#17324d;box-shadow:0 4px 14px rgba(14,116,144,.08)}
.tsr.r1{background:#fff7dc;border-color:#f59e0b}.tsr.lf{border-color:#22c55e}
.tsk{color:#d97706}
.tsx{color:#166534;background:#dcfce7}
.tsbar{background:#e1eef7}
.tsr.r1 .tsbar i{background:linear-gradient(90deg,#f59e0b,#fbbf24)}
.tsmem,.tsp small{color:#4b6a85}
.tsp b{color:#d97706}.tsp em{color:#059669}
/* ---------- Boss battle: soft rose + peach card ---------- */
body.proj #bossbar,body.bossfs #bossbar{background:linear-gradient(135deg,#fff5f5,#ffe8d9)!important;color:#4a1d1d!important;border-color:#f87171!important;box-shadow:0 10px 34px rgba(220,38,38,.18)!important}
body.proj #bossbar.enr,body.bossfs #bossbar.enr{border-color:#dc2626!important;box-shadow:0 0 34px rgba(220,38,38,.55)!important}
body.proj #bossbar.dbl,body.bossfs #bossbar.dbl{border-color:#f59e0b!important}
body.proj #bossbar .bsy,body.proj #bossbar .nd,body.bossfs #bossbar .bsy,body.bossfs #bossbar .nd{color:#b45309}
body.proj #bossbar .hpb,body.bossfs #bossbar .hpb{background:#ffe4e6;border-color:#fecdd3}
body.proj #bossbar .hpb::after,body.bossfs #bossbar .hpb::after{background-image:repeating-linear-gradient(90deg,transparent 0,transparent calc(var(--sw,10%) - 2px),rgba(255,255,255,.95) calc(var(--sw,10%) - 2px),rgba(255,255,255,.95) var(--sw,10%))}
body.bossfs{background:radial-gradient(circle at 50% 40%,#ffe8d9,#fdf2f8)!important}
body.proj.bossonly{background:radial-gradient(circle at 50% 40%,#ffe8d9,#fdf2f8)!important}
body.proj.bossonly::before{opacity:.25}
#bfsb{background:#fff;color:#4a1d1d;border-color:#f3cfae}#bfsb:hover{background:#ffe8d9}
</style>
<style>/* ===== highlighted card for the Pick-a-student settings (#sp) ===== */
#sp>div{border:3px solid transparent!important;background:linear-gradient(#fff,#fdfbff) padding-box,linear-gradient(135deg,#7c3aed,#ec4899 55%,#f59e0b) border-box!important;
box-shadow:0 0 0 6px rgba(167,139,250,.18),0 0 48px rgba(236,72,153,.28),0 28px 70px rgba(80,60,140,.25)!important;position:relative;animation:spin .28s ease-out,spglow 3.5s ease-in-out .3s infinite alternate}
@keyframes spglow{from{box-shadow:0 0 0 6px rgba(167,139,250,.16),0 0 34px rgba(124,58,237,.22),0 28px 70px rgba(80,60,140,.22)}to{box-shadow:0 0 0 9px rgba(244,114,182,.2),0 0 60px rgba(236,72,153,.38),0 28px 70px rgba(80,60,140,.28)}}
#sp>div::before{content:"";position:absolute;left:12%;right:12%;top:-3px;height:6px;border-radius:0 0 99px 99px;background:linear-gradient(90deg,#7c3aed,#ec4899,#f59e0b);filter:blur(.3px)}
.spf select{box-shadow:0 2px 0 rgba(124,58,237,.08);transition:border-color .15s,box-shadow .15s,transform .15s}
.spf select:hover{border-color:#a78bfa!important;box-shadow:0 6px 16px rgba(124,58,237,.16)!important;transform:translateY(-1px)}
.spf select:focus{border-color:#7c3aed!important;box-shadow:0 0 0 4px rgba(124,58,237,.2),0 8px 18px rgba(124,58,237,.18)!important}
#spb button{box-shadow:0 4px 14px rgba(245,158,11,.3)}
#sp .spc:hover,#spm .spr:hover{box-shadow:0 6px 16px rgba(124,58,237,.18)}
</style>
</head>
<body><header><b><span class="lg"><img src="data:image/png;base64,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" alt="Guadalupe National High School"></span><span class="ttl">Guadalupe NHS Numeracy Drill</span></b><span id="jn" style="font-weight:600"></span>
<button onclick="location.href='/test/host?key='+encodeURIComponent(K)" class="p">📝 Pre / Post test</button>
<button onclick="try{sessionStorage.mk=''}catch(e){};location.replace('/host')" style="background:rgba(255,255,255,.18);color:#fff;border:1px solid rgba(255,255,255,.45);border-radius:99px;padding:11px 18px">🔒 Lock</button><button onclick="document.body.classList.toggle('proj')" class="p">📽 Projector view</button></header><div id="tabs"></div><div id="gen">
<div class="gp" id="gpm"><label>🎮 Mode</label><span id="modes"><button class="mb" data-m="individual">👤 Individual</button><button class="mb" data-m="team">👥 Team</button><button class="mb" data-m="class">🏰 Class</button><button class="rb" id="rbtn" onclick="rosToggle()" title="Add, rename or remove sections and students, or paste a class list">👥 Roster</button></span></div>
<div class="gp"><label>👥 Section</label><select id="sec" onchange="api('section',{sec:this.value})"></select></div>
<div class="gp"><label>🎲 Grade level</label><select id="lg" onchange="setLv()"><option value="1">Grade 7–8</option><option value="2">Grade 9–10</option></select></div>
<div class="gp"><label>📶 Difficulty</label><select id="ld" onchange="setLv()"><option value="1">🟢 Easy</option><option value="2">🟡 Average</option><option value="3">🔴 Difficult</option><option value="4">🔀 Mixed (all three)</option></select></div>
<div class="gp" id="lgg"><label>🇵🇭 Word problem language</label><select id="lang" onchange="api('lang',{v:this.value})"><option value="en">English</option><option value="tl">Taglish / Filipino</option></select></div>
<div class="gp" id="shg"><label id="shl">🔢 Digits (this tab)</label><select id="sh" onchange="api('shape',{topic:tab,v:this.value})"><option value="">Mixed (grade level)</option><option value="11">1-digit × 1-digit</option><option value="12">2-digit × 1-digit</option><option value="22">2-digit × 2-digit</option></select></div>
<div class="gp gp-r"><label class="chk"><input type="checkbox" id="onlyon" onchange="api('onlyon',{v:this.checked})"> 👀 Pick only online students</label><span class="mute" id="rleft"></span></div>
</div>
<style>
#rostv{display:none;padding:14px 2vw 40px}
body.rosv #rostv{display:block}
body.rosv #app{display:none!important}
body.rosv #gen>.gp:not(#gpm){display:none!important}
body.proj #rostv{display:none!important}
#gen #modes button.rb.cur{background:linear-gradient(135deg,#7c3aed,#ec4899);color:#fff;border-color:transparent;box-shadow:0 6px 16px rgba(236,72,153,.4)}
body.rosv #gen #modes button.mb.cur{background:transparent;color:var(--ink);box-shadow:none}
.rs{display:grid;grid-template-columns:270px 1fr;gap:16px;align-items:start;max-width:1400px;margin:0 auto}
.rs h2{margin:0;font-size:22px}.rs h3{margin:0 0 10px;font-size:15px}.rs p{margin:0 0 8px}
.rs-c{background:var(--card);border:1px solid var(--line);border-radius:18px;padding:16px;box-shadow:var(--shadow)}
.rs-sl{display:flex;flex-direction:column;gap:6px;margin-bottom:12px}
.rs-s{display:flex;justify-content:space-between;align-items:center;gap:8px;text-align:left;border-radius:12px;padding:10px 12px}
.rs-s.on{background:var(--grad);color:#fff;border-color:transparent}.rs-s b{font-size:12px;opacity:.85}
.rs-new{display:flex;gap:8px;margin-bottom:10px}
.rs-new input,#rsta{flex:1;min-width:0;padding:10px 12px;border-radius:12px;border:2px solid var(--line);background:var(--card);color:var(--ink);font:inherit}
#rsta{width:100%;box-sizing:border-box;resize:vertical}
.rs-hd{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;margin-bottom:14px}
.rs-hb{display:flex;gap:8px;flex-wrap:wrap}
button.rsd{background:rgba(220,38,38,.12);color:#dc2626;border-color:rgba(220,38,38,.35)}
.rs-cols{display:grid;grid-template-columns:1fr 1fr;gap:16px;align-items:start}
.rs-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:6px;max-height:58vh;overflow:auto}
.rs-st{display:flex;align-items:center;gap:8px;padding:6px 8px;border:1px solid var(--line);border-radius:10px}
.rs-no{font-size:11px;color:var(--mute);min-width:22px;text-align:right}
.rs-nm{flex:1;min-width:0;overflow-wrap:anywhere}
.rs-x{padding:2px 8px;border-radius:8px;line-height:1.2}
.rs-mode{display:flex;gap:16px;flex-wrap:wrap;margin:10px 0}
.rs-mode label{display:flex;align-items:center;gap:6px;margin:0;width:auto}.rs-mode input{width:auto;margin:0}
.rs-nsec{flex-direction:column}
.rs-msg{padding:10px 14px;border-radius:12px;margin-bottom:14px;font-weight:600;border:2px solid;background:var(--card);color:var(--ink)}
.rs-msg.ok{border-color:#10b981}.rs-msg.bad{border-color:#f59e0b}.rs-msg button{margin-left:10px}
@media(max-width:1000px){.rs-cols{grid-template-columns:1fr}}
@media(max-width:820px){.rs{grid-template-columns:1fr}}
</style><div id="rostv"></div><div id="app"><div id="side"></div><div class="card"><div id="join"><div class="mute">Students join at</div><div id="big">…</div></div><div class="mute" id="cnt"></div><div id="bysec"></div><div id="toast"></div><div id="fin"></div><div id="fstrip"></div><hr style="border:0;border-top:1px solid var(--line)">
<h2 id="q"></h2><div id="tm"></div><div id="res"></div><div id="pickbar"></div><div class="row ctl" style="margin-top:16px"><button onclick="nav(-1)">←</button><button onclick="nav(1)">→</button><button id="tg" onclick="api('toggle')"></button><button onclick="api('start',{id:st.slide.id})">⏱ Start timer</button><button onclick="api('reveal',{id:st.slide.id})">✅ Reveal</button><button onclick="api('board')">🏆 Leaderboard</button><button onclick="api('reset',{id:st.slide.id})">Reset</button></div>
<div id="ed"></div></div>
<aside id="dock">

<section class="dk"><h5>Quick actions</h5><div class="qa">
<button onclick="document.body.classList.add('proj');api('rwait');spopen()"><i>🎯</i>Pick a student</button>
<button id="qtm" onclick="tmopen()"><i>👥</i>Teams</button>
<button id="qts" onclick="tsbopen()"><i>📊</i>Team scores</button>
<button id="qbb" onclick="clopen()"><i>🏰</i>Boss battle</button>
<button onclick="nzopen()"><i>🔇</i>Noisy student</button>
</div></section>
<section class="dk"><h5>Reports</h5><div class="qa two"><button onclick="lfopen()"><i>📚</i>Totals</button><button onclick="mropen()"><i>📈</i>Mastery</button><button onclick="skopen()"><i>🧮</i>Skills</button><button onclick="location.href='/test/host?key='+encodeURIComponent(K)"><i>📝</i>Pre / Post test</button></div></section>


</aside></div><button id="back" onclick="document.body.classList.remove('proj')">⬅ Dashboard</button><button id="gear" onclick="spopen()">⚙ Settings</button><button id="fab" onclick="spopen()">🎯 Pick a student</button><div id="turn"><div id="tt"></div><div id="tcards"></div><div id="tctl"><div class="row" id="tpre" style="justify-content:center;flex-wrap:wrap"></div><div class="row" style="justify-content:center"><button id="tgo">▶ Start timer</button><button id="tpz">⏸ Pause</button><button id="trs">↺ Reset</button><button id="tx">Hide</button></div></div></div><button id="nzb" onclick="nzopen()">🔇 Noisy</button><button id="cmb" onclick="clopen()">🏰 Class</button><div id="clo"><div class="tmw"><div id="clt">🏰 Class battle · Boss</div><div class="mute" id="clsub"></div><div id="clb"></div></div></div><button id="tmb" onclick="tmopen()">👥 Teams</button><button id="tsbb" onclick="tsbopen()">📊 Team scores</button><div id="tsb"><div class="tsh"><div><div id="tst">📊 Team scores</div><div id="tssub"></div></div><button id="tsx" onclick="tsbclose()">✕ Close</button></div><div id="tsl"></div></div><div id="tstrip"></div><div id="tmo"><div class="tmw">
<div class="tmhd"><div id="tmt">👥 Teams</div><div id="tmsub"></div></div>
<div class="tmtop">
<div class="tmcard"><div class="tmct"><span class="tmstep">1</span>Set up teams</div>
<div class="tmlab">Students per team</div><div id="tmsz" class="tmszr"></div><div id="tmhint" class="tmhint"></div>
<label class="tmck"><input type="checkbox" id="tmon"> Only include students who are online</label>
<div class="tmrow"><button class="p big" id="tmmk">🎲 Make random teams</button></div>
<div class="tmrow tmgoal"><label class="tmck">🏁 Team goal <input type="number" id="tmgl" min="0" max="500" placeholder="0"> points <span class="mute">(0 = no goal)</span></label></div>
</div>
<div class="tmcard"><div class="tmct"><span class="tmstep">2</span>Play</div>
<div class="tmrow"><button class="p big" id="tml"></button></div>
<div class="tmnote">Makes teams if there are none yet, then opens the projector.</div>
<div class="tmrow"><button id="tmtg"></button></div>
<div class="tmnote">Team mode ON: correct answers add points to the student's team.</div>
</div>
</div>
<div id="tmg"></div><div id="tmf"></div><div id="tmh"></div>
<div class="tmfoot">
<div class="tmgrp"><span class="tmlab">Scores</span><button class="p" id="tsbo">📊 Project scores to class</button><button id="tmdl">📄 Download PDF</button></div>
<div class="tmgrp"><span class="tmlab">Fix mistakes</span><button id="tmu">↩ Undo last</button></div>
<div class="tmgrp"><span class="tmlab">Danger zone</span><button class="dng" id="tmrs">↺ New game (reset scores)</button><button class="dng" id="tmcl">🗑 Remove teams</button></div>
<div class="tmgrp tmclose"><button id="tmx">Close</button></div>
</div>
</div></div><div id="nz"><div style="text-align:center;width:100%;max-width:1200px"><div id="nzt"></div><div class="mute">Tap a name: they automatically lose 1 point. Tap Undo if it was a mistake.</div><select id="nzs"></select><div id="nzg"></div><div class="row" style="justify-content:center"><button id="nzu">↩ Undo last</button><button onclick="nzclose()">Close</button></div></div></div><div id="sp"><div style="text-align:center;width:100%;max-width:1200px"><div id="spt">⚙ Settings · pick a section to start</div><div id="spb"></div><div id="spm"></div><div id="spf"><button class="spc" onclick="spclose();document.body.classList.remove('proj')">Cancel</button><button class="spc" onclick="if(confirm('Make all students eligible to be picked again?'))api('rreset')">↺ Reset picked</button><button class="spg" onclick="choose(st.roster.section)">🎯 Start picking</button></div></div></div><div id="rp"><div style="text-align:center"><div id="rpt">Who will answer?</div><div id="rpn"></div><div id="rps"></div><div id="rpq"></div><div class="row" style="justify-content:center;margin-top:3vh"><button class="p" onclick="api('rpick')">Next ▶ (same section)</button><button onclick="rpclose();spopen()">⚙ Settings</button><button onclick="rpclose()">Close</button></div></div></div><div id="pod"></div><div id="hint">← → slide · S timer · R reveal · B board · C settings / pick · P pick online student · N new random question · A answer · Y ✅ · X ❌ · T start timer · M noisy student · O podium · G teams · V team scores · K class battle · Space pause/resume · 0 reset timer · Esc exit</div><script>""" + COMMON + r"""
window.HOSTV=1;const K=new URLSearchParams(location.search).get('key')||'';try{sessionStorage.mk=K;history.replaceState(null,'','/host')}catch(e){}let st=null,edId=null,t=null,tab=null,lastId=null,showAns=false;
async function dlpdf(title,sub,cols,rows,w,name){const r=await fetch('/api/pdf',{method:'POST',body:JSON.stringify({key:K,title:title,sub:sub,cols:cols,rows:rows,w:w})});if(!r.ok){alert('Could not make the PDF.');return}const a=document.createElement('a');a.href=URL.createObjectURL(await r.blob());a.download=name;document.body.appendChild(a);a.click();a.remove()}
async function api(a,d={}){await fetch('/api/host',{method:'POST',body:JSON.stringify({key:K,action:a,...(a=='rpick'&&tab?{topic:tab}:{}),...d})});await poll()}
function sendOpts(){const rows=[...document.querySelectorAll('.orow')],o=rows.map(r=>r.querySelector('.oi').value),ci=rows.findIndex(r=>r.querySelector('.ca')&&r.querySelector('.ca').checked);
 api('edit',{id:edId,opts:o,...(ci>=0?{ans:o[ci]}:{})})}
function orow(v,q,on){return '<div class="row orow">'+(q?'<input type="radio" name="ca" class="ca" title="Correct answer" '+(on?'checked':'')+' style="width:auto">':'')+'<input class="oi" value="'+esc(v)+'"><button class="rm">✕</button></div>'}
function editor(){const s=st.slide,q=s.type=='quiz';edId=s.id;
 let h='<label>Question <span class="mute">(x^2, sqrt(x), pi, &lt;=, &gt;=, != and +- show as math symbols)</span></label><input id="qi" value="'+esc(s.q)+'">';
 if(s.type=='mc'||q)h+='<label>Options'+(q?' (tick the correct one)':'')+'</label><div id="ol">'+s.opts.map(o=>orow(o,q,o==s.ans)).join('')+'</div><button id="ao">+ Option</button>';
 if(s.type=='num')h+='<label>Correct answer (number, decimal or fraction like 3/4)</label><input id="ai" value="'+esc(s.ans||'')+'">';
 if(q||s.type=='num')h+='<label>Time limit in seconds (0 = none)</label><input id="ti" type="number" min="0" value="'+(s.time||0)+'" style="width:120px">';
 h+=topicSel(s);h+='<div class="row" style="margin-top:14px"><button id="dl">Delete slide</button></div>';$('ed').innerHTML=h;
 $('qi').oninput=e=>{clearTimeout(t);t=setTimeout(()=>api('edit',{id:edId,q:e.target.value}),400)};
 const wire=()=>{document.querySelectorAll('.oi,.ca').forEach(i=>i.onchange=sendOpts);document.querySelectorAll('.rm').forEach(b=>b.onclick=()=>{b.parentNode.remove();sendOpts()})};wire();
 if($('ao'))$('ao').onclick=()=>{$('ol').insertAdjacentHTML('beforeend',orow('',q,false));wire();$('ol').lastChild.querySelector('.oi').focus()};
 if($('ai'))$('ai').oninput=e=>{clearTimeout(t);t=setTimeout(()=>api('edit',{id:edId,ans:e.target.value}),400)};
 if($('ti'))$('ti').onchange=e=>api('edit',{id:edId,time:e.target.value});
 $('tp').onchange=e=>{tab=e.target.value;api('edit',{id:edId,topic:tab})};
 $('dl').onclick=()=>confirm('Delete this slide?')&&api('del',{id:edId})}
const TN={mc:'Poll',cloud:'Word cloud',open:'Open',scale:'Scale',quiz:'Quiz',num:'Number',pick:'Cold call'};
async function tabClick(n){if(window.ROSV){rosOff();return}const eff=(st.mix&&st.mix.length)?st.mix.slice():[tab];let m;
 if(eff.includes(n)){m=eff.filter(x=>x!=n);if(!m.length)m=[n]}else m=eff.concat(n);   /* at least one topic stays ticked */
 await api('mix',{v:m});setTab(m.includes(n)?n:m[0])}
function setTab(n){tab=n;const i=st.slides.findIndex(x=>x.topic==n);if(i>=0&&st.slide.topic!=n)api('goto',{i});else poll()}
function add(t){api('add',{type:t,topic:tab||st.topics[0]})}
function nav(d){const ix=st.slides.map((x,i)=>x.topic==st.slide.topic?i:-1).filter(i=>i>=0),n=ix[ix.indexOf(st.cur)+d];if(n!=null)api('goto',{i:n})}
function topicSel(s){return '<label>Topic (tab)</label><select id="tp" style="padding:9px;border-radius:8px;background:var(--card);color:var(--ink);border:1px solid var(--line)">'+st.topics.map(n=>'<option '+(n==s.topic?'selected':'')+'>'+esc(n)+'</option>').join('')+'</select>'}
let rpN=null,spin=null,back=null,spinning=false,pendingStart=false,RPS=null,PT=0,tdb={},tN=-1,spinTimers=[];
function roster(R){const se=$('sec');
 if(Array.from(se.options).map(o=>o.value).join('\n')!=R.sections.join('\n'))se.innerHTML=R.sections.map(x=>'<option>'+esc(x)+'</option>').join('');
 if(document.activeElement!==se)se.value=R.section;if(document.activeElement!==$('lg')&&document.activeElement!==$('ld')){$('lg').value=R.level>4?2:1;$('ld').value=(R.level-1)%4+1}
 {const ok=['Basic Operations','Integers','Word Problem'].includes(tab);$('shg').style.display=ok?'':'none';if(ok&&document.activeElement!==$('sh'))$('sh').value=(R.shapes||{})[tab]||''}
 $('lgg').style.display=tab=='Word Problem'?'':'none';if(document.activeElement!==$('lang'))$('lang').value=R.lang||'en';
 $('rleft').textContent=(R.onlyon&&!R.total)?'👀 Nobody online yet':R.left+' of '+R.total+' not picked yet'+(R.onlyon?' (online only)':'');if(document.activeElement!==$('onlyon'))$('onlyon').checked=!!R.onlyon;
 if(rpN===null){rpN=R.rp.n;turnui(R);return}
 if(R.rp.n==rpN){turnui(R);return}rpN=R.rp.n;spinning=true;pendingStart=true;turnui(R);
 $('rp').classList.add('on');$('rps').textContent='';spinTimers.forEach(clearTimeout);clearTimeout(back);
 const P=R.names.length?R.names:[''],F=R.rp.picks,rn=$('rpn'),one=F.length==1,mixedSec=new Set(F.map(q=>q.sec)).size>1;$('rpt').textContent='Picking…';
 rn.className='n'+F.length+(F.length>=6?' ng ng'+Math.min(4,Math.ceil(F.length/4)):'');rn.innerHTML=F.map((f,i)=>'<div class="slot spin" id="sl'+i+'"></div>').join('');let left=F.length;
 F.forEach((f,i)=>{let k=0;const N=24+i*4,el=$('sl'+i);
  const step=()=>{if(k>=N){el.className='slot done';el.innerHTML=esc(f.name)+(mixedSec?'<small>'+esc(f.sec)+'</small>':'');
   if(--left==0){$('rpt').textContent='🎉 Selected!';$('rps').textContent=(one&&mixedSec?f.sec:'')+(R.rp.wrapped?(one&&mixedSec?' · ':'')+'everyone has been picked, starting over':'');spinning=false;turnui(st.roster);back=setTimeout(rpclose,4500)}return}
   el.textContent=P[Math.floor(Math.random()*P.length)];k++;spinTimers[i]=setTimeout(step,40+Math.pow(k/N,3)*330)};step()})}
let spCust={g:0,t:0};
function spm(){const R=st.roster,t=R.rtime,c=R.rcount,g=R.goal,PT=[0,10,20,30,45,60,90],PG=[0,1,2,3,5,10];
 const gC=spCust.g||!PG.includes(g),tC=spCust.t||!PT.includes(t);
 const sel=(id,ico,lab,opts)=>'<label class="spf"><span>'+ico+' '+lab+'</span><select id="'+id+'">'+opts+'</select></label>';
 const op=(v,l,on)=>'<option value="'+v+'"'+(on?' selected':'')+'>'+l+'</option>';
 $('spm').innerHTML='<div class="spg2">'
 +'<div class="spw">'+sel('sw','👀','Who can be picked?',op(0,'Everyone in the class list',!R.onlyon)+op(1,'Present (online) only · '+oc(R.section)+' online now',R.onlyon))+'</div>'
 +sel('sc','👥','Students at once',[1,2,3,4,5,6,7,8,9,10,11,12,13].map(v=>op(v,v+(v==1?' student':' students'),c==v)).join(''))
 +sel('sg','🏁','Can leave after correct answers',PG.map(v=>op(v,v?v+' correct':'Off',!gC&&g==v)).join('')+op('x','Custom…',gC))
 +sel('st','⏱','Time for each round',PT.map(v=>op(v,v?v+' seconds':'No timer',!tC&&t==v)).join('')+op('x','Custom…',tC))
 +'<div class="spx">'+(gC?'<label class="spn">Correct answers<input id="sgc" type="number" min="0" max="50" value="'+g+'"></label>':'')+(tC?'<label class="spn">Seconds<input id="spc" type="number" min="0" max="600" value="'+t+'"></label>':'')+'<button id="sgr" class="spr">↺ Reset progress</button></div></div>';
 $('sw').onchange=async e=>{await api('onlyon',{v:e.target.value=='1'});spm()};
 $('sc').onchange=async e=>{await api('rcount',{v:+e.target.value});spm()};
 $('sg').onchange=async e=>{if(e.target.value=='x'){spCust.g=1;spm();const i=$('sgc');if(i)i.focus()}else{spCust.g=0;await api('goal',{v:+e.target.value});spm()}};
 $('st').onchange=async e=>{if(e.target.value=='x'){spCust.t=1;spm();const i=$('spc');if(i)i.focus()}else{spCust.t=0;await api('rtime',{v:+e.target.value});spm()}};
 if($('sgc'))$('sgc').onchange=async e=>{await api('goal',{v:+e.target.value});spm()};
 if($('spc'))$('spc').onchange=async e=>{await api('rtime',{v:+e.target.value});spm()};
 $('sgr').onclick=async()=>{if(confirm('Reset everyone\'s correct-answer progress?')){await api('goalreset');spm()}}}
function fmt(l){const n=Math.ceil(l);return n>=60?Math.floor(n/60)+':'+String(n%60).padStart(2,'0'):String(n)}
const REVEAL_SECS=5,AUTO_PICK_NEXT=true;let finKey='';
async function roundEnd(n,ts){await api('rfinish');
 setTimeout(async()=>{const r=st&&st.roster&&st.roster.rp;if(!r||r.n!=n||r.tstart!=ts||!r.fin)return;
  if(!st.slide.auto)await gen('pick');if(AUTO_PICK_NEXT)api('rpick')},REVEAL_SECS*1000)}
function tick2(){const p=RPS,e=$('tt');if(!p||!p.tdur){e.textContent='';e.className='';return}
 if(p.dec>0&&!p.fin){const dd=p.dec-(Date.now()-PT)/1000;if(dd>0){e.textContent='🆘 '+Math.ceil(dd);e.className='';return}}
 let l=p.rleft;if(p.run)l=Math.max(0,l-(Date.now()-PT)/1000);
 if(p.run&&l<=0&&!p.fin&&finKey!==p.n+':'+p.tstart){finKey=p.n+':'+p.tstart;roundEnd(p.n,p.tstart)}
 const pz=!p.run&&p.tfz!=null&&!p.fin;e.textContent=p.run&&l<=0?'⏰ Time!':(pz?'⏸ ':'')+fmt(l);e.className=p.run&&l<=0?'up':p.run&&l<=10?'low':''}
function tbuild(p){$('tcards').innerHTML=p.picks.map((f,i)=>'<div class="tc" id="tc'+i+'"><div class="tn">'+esc(f.name)+'<span id="dt'+i+'"></span></div><div class="ts">'+esc(f.sec)+'</div><div class="tl" id="tl'+i+'"></div><div class="tr"><div class="ta" id="ta'+i+'"></div><div class="tv" id="tv'+i+'"></div></div><div class="tcc"><input class="tai" data-i="'+i+'" maxlength="80" placeholder="Answer (Enter = check)"><button class="g" data-i="'+i+'" data-m="ok">✓</button><button class="rd" data-i="'+i+'" data-m="no">✗</button><button data-i="'+i+'" data-lf="1" title="Cancel lifeline (refund)">↩ LL</button></div></div>').join('');tN=p.n}
function turnui(R){const p=R.rp,el=$('turn'),on=!!(p.show&&p.picks&&p.picks.length&&!spinning);
 document.body.classList.toggle('hasturn',on);document.body.classList.toggle('turncm',on&&p.picks.length>=6);el.className=on?'on c'+p.picks.length+(new Set(p.picks.map(q=>q.sec)).size>1?' mixed':'')+(p.picks.length>=6?' cm':''):'';if(!on)return;
 RPS=p;PT=Date.now();if(tN!==p.n)tbuild(p);
 p.picks.forEach((f,i)=>{const c=$('tc'+i);c.classList.toggle('ok',f.mark=='ok');c.classList.toggle('no',f.mark=='no');
  $('tl'+i).textContent=f.lf?(f.lf.k=='pass'?'🙋 Passed to '+f.lf.to+' · '+f.lf.to+' earns the point':'📞 Friend: '+f.lf.to+' · '+f.name+' earns the point'):'';
  $('dt'+i).textContent=f.on?' 📱':'';$('tv'+i).textContent=(f.mark=='ok'?'✅ Correct!':f.mark=='no'?'❌ Wrong':'')+(p.goal?' · '+f.got+'/'+p.goal:'')+(f.out?' 🏁 can leave!':'');
  const ai=c.querySelector('.tai');if(document.activeElement!==ai){ai.value=f.ans||'';$('ta'+i).textContent=f.ans||''}});
 const paused=!p.run&&p.tfz!=null&&!p.fin&&!!p.tdur;
 $('tgo').textContent=p.run||paused?'↻ Restart timer':'▶ Start timer';
 $('tpz').textContent=paused?'▶ Resume':'⏸ Pause';$('tpz').style.display=p.tdur?'':'none';$('trs').style.display=p.tdur?'':'none';$('tpz').disabled=!(p.run||paused);
 document.querySelectorAll('#tpre button').forEach(b=>b.classList.toggle('cur',+b.dataset.t==R.rtime));tick2()}
setInterval(()=>{if($('turn').classList.contains('on'))tick2()},200);
function oc(x){const b=(st.bysec||[]).find(y=>y.sec==x);return b?b.on.length:0}
function spopen(){if(!st||!st.roster)return;const R=st.roster;spCust={g:0,t:0};
 $('spt').textContent='⚙ Settings · '+R.section;$('spb').innerHTML=[R.section].map(x=>'<button data-s="'+esc(x)+'" class="'+(R.section==x?'cur':'')+'">'+esc(x)+(oc(x)?' <small>🟢 '+oc(x)+'</small>':'')+'</button>').join('');
 document.querySelectorAll('#spb button').forEach(b=>b.onclick=()=>choose(b.dataset.s));spm();$('sp').classList.add('on')}
const bsOpen=new Set();let bsC='';let finId=null,finT=0,fstC='';
document.addEventListener('click',e=>{const b=e.target.closest&&e.target.closest('#fstrip .bk');if(!b)return;e.stopPropagation();
 if(b.dataset.all)api('backall');else api('back',{sec:b.dataset.s,name:b.dataset.n})});
function finHide(){$('fin').classList.remove('on');clearTimeout(finT)}
function fin(S){const A=S.ann,F=S.fin||[];
 const nl=F.filter(x=>!x.back).length,sh=F.length&&S.goal?'<b>🏁 Left the room ('+nl+'/'+F.length+') <button class="bk" data-all="1" title="Toggle all">⇄ all</button></b>'+F.map(x=>'<div class="'+(x.back?'bkd':'')+'"><span class="nm2">'+esc(x.n)+'<span style="opacity:.6"> · '+esc(x.s.replace(/^Grade /,'G'))+'</span></span> <label class="tg" title="'+(x.back?'In the picker list':'Out of the picker list')+'"><input type="checkbox" class="bk" data-s="'+esc(x.s)+'" data-n="'+esc(x.n)+'"'+(x.back?' checked':'')+'><i></i></label></div>').join('')+'<div class="mute" style="font-size:.8em;opacity:.7">toggle on = back in the picker list</div>':'';
 if(sh!==fstC){fstC=sh;$('fstrip').innerHTML=sh;$('fstrip').classList.toggle('has',!!sh)}
 if(A&&A.id!==finId){const first=finId===null;finId=A.id;if(first&&A.age>12)return;
  $('fin').innerHTML='<div><div class="ft">🏁 Goal reached · '+S.goal+' correct</div>'+A.names.map(x=>'<div class="fn">'+esc(x.n)+'<small>'+esc(x.s)+'</small></div>').join('')+'<div class="fs">🚪 You may leave now!</div><div class="fh">click or press Esc to close</div></div>';
  confetti(200);$('fin').classList.add('on');clearTimeout(finT);finT=setTimeout(finHide,12000)}
 else if(finId===null&&A===null)finId=0}
function bysec(S){if(!S.bysec)return;const R=S.roster,sec=R.section,x=S.bysec.find(y=>y.sec==sec);if(!x)return;
 const G=S.goal,o=new Set(x.out||[]),on=new Set(x.on),N=S.noisy||{},sel=new Set(R.rp.show?R.rp.picks.map(q=>q.name):[]);
 const hu=n=>[...n].reduce((a,c)=>(a*31+c.charCodeAt(0))%360,7),tot=x.total||0,pct=tot?Math.round(100*x.on.length/tot):0;
 const card=n=>{const c=o.has(n)?'fin':on.has(n)?'on':'off',nz=N[sec+'|'+n],H=hu(n),S=sel.has(n);
  return '<div class="'+c+(S?' sel':'')+'"><i class="av" style="--h:'+H+';--h2:'+((H+45)%360)+'">'+esc((n.trim().charAt(0)||'?').toUpperCase())+'</i><strong class="tx"><b>'+esc(n)+'</b>'+(S||c=='fin'?'<em>'+(S?'Selected':'🏁 Goal reached')+'</em>':'')+'</strong><s class=\"dt '+(on.has(n)?'g':'r')+'\" title=\"'+(on.has(n)?'Online':'Offline')+'\"></s>'+(G?'<u class="sc">'+((x.cnt||{})[n]||0)+'/'+G+'</u>':'')+(nz?'<u class="nz">🔇'+nz+'</u>':'')+'</div>'};
 const f=window.bfl||'all',q=(window.bq||'').toLowerCase();
 const vis=R.names.filter(n=>{const c=o.has(n)?'fin':on.has(n)?'on':'off';return (f=='all'||(f=='on'?on.has(n):f=='off'?!on.has(n):f==c))&&(!q||n.toLowerCase().includes(q))});
 const grp=(t,cls,arr,e)=>'<div class="gh '+cls+'"><span>'+t+'</span><b>'+arr.length+'</b></div>'+(arr.length?'<div class="nm">'+arr.map(card).join('')+'</div>':'<div class="ge">'+(q?'No student matches your search.':e)+'</div>');
 const body=f=='all'?grp('🟢 Online','on',vis.filter(n=>on.has(n)),'Nobody is online yet.')+grp('⚪ Offline','off',vis.filter(n=>!on.has(n)),'Everyone is online.'):'<div class="nm">'+vis.map(card).join('')+'</div>';
 const h='<div class="bh"><div class="bt"><small>Class</small><h4>'+esc(sec)+'</h4></div><div class="stats"><div class="st g"><b>'+x.on.length+'</b><span>Online</span></div><div class="st"><b>'+Math.max(0,tot-x.on.length)+'</b><span>Waiting</span></div>'+(G?'<div class="st y"><b>'+o.size+'</b><span>Reached goal</span></div>':'')+'<div class="st v"><b>'+(R.left!=null?R.left:'–')+'</b><span>Not picked</span></div></div></div><div class="pg"><i style="width:'+pct+'%"></i></div>'+body;
 if(h===bsC)return;bsC=h;$('bysec').innerHTML=h}
function celeb(S){const k=S.roster.section;if(window.pds!==k){window.pds=k;window.pdn=null}
 const dn=(S.tboard||[]).filter(t=>t.done).length+(S.tleft||[]).length;if(window.pdn!=null&&dn>window.pdn)confetti(220);window.pdn=dn}
function podium(t,s,rows){rows=rows.slice(0,3);if(!rows.length)return;const o=$('pod'),hs=[34,24,17],cs=['#fbbf24','#cbd5e1','#d9a066'],md=['🥇','🥈','🥉'];
 o.innerHTML='<div class="pt">'+esc(t)+'</div><div class="ps">'+esc(s||'')+'</div><div class="pc">'+[1,0,2].filter(i=>rows[i]).map(i=>{const r=rows[i];
  return '<div class="pcol"><div class="pn" style="animation-delay:'+(0.7+(2-i)*.5)+'s">'+md[i]+'<b>'+esc(r.n)+'</b><span>'+r.v+esc(r.u||'')+'</span></div><div class="pbar" style="--h:'+hs[i]+'vh;background:linear-gradient(180deg,'+cs[i]+',rgba(255,255,255,.15));animation-delay:'+((2-i)*.5)+'s"><em>'+(i+1)+'</em></div></div>'}).join('')+'</div><div class="ph">click to close</div>';
 o.classList.add('on');o.onclick=()=>o.classList.remove('on');setTimeout(()=>confetti(160),1500);clearTimeout(window.pdt);window.pdt=setTimeout(()=>o.classList.remove('on'),15000)}
function podiumNow(){const P=st&&st.podium;if(!P||!P.rows.length){alert('No scores to show yet.');return}podium(P.t,P.s,P.rows)}
window.onBossEnd=b=>{if(b.top&&b.top.length)setTimeout(()=>podium(b.st=='won'?'🎉 Boss defeated!':'💀 The boss survived','Top hitters',b.top.map(x=>({n:x.n,v:x.d,u:' dmg'}))),b.st=='won'?2500:600)};
function spclose(){$('sp').classList.remove('on')}
function nzclose(){$('nz').classList.remove('on')}
function nzgrid(){const sec=$('nzs').value,b=(st.bysec||[]).find(x=>x.sec==sec)||{on:[],off:[]},on=new Set(b.on),N=st.noisy||{};
 $('nzt').textContent='🔇 Noisy student · −1 point';
 $('nzg').innerHTML=b.on.concat(b.off).map(n=>{const c=N[sec+'|'+n]||0,g=st.goal?' · '+((b.cnt||{})[n]||0)+'/'+st.goal:'';return '<button class="'+(on.has(n)?'on':'')+'" data-n="'+esc(n)+'">'+(on.has(n)?'● ':'')+esc(n)+g+(c?' 🔇×'+c:'')+'</button>'}).join('');
 $('nzu').textContent='↩ Undo last'+(st.nlast?' ('+st.nlast+')':'')}
function nzopen(){if(!st||!st.roster)return;const R=st.roster,s=$('nzs');
 if(Array.from(s.options).map(o=>o.value).join('\n')!=R.sections.join('\n'))s.innerHTML=R.sections.map(x=>'<option>'+esc(x)+'</option>').join('');
 if(!window.nzsec)window.nzsec=R.section!='*'?R.section:R.sections[0];s.value=window.nzsec;nzgrid();$('nz').classList.add('on')}
document.addEventListener('click',async e=>{if(e.target.id=='nzu'){await api('noisyundo');nzgrid();return}
 const b=e.target.closest&&e.target.closest('#nzg button');if(b){await api('noisy',{sec:$('nzs').value,name:b.dataset.n});nzclose()}});
document.addEventListener('change',e=>{if(e.target.id=='nzs'){window.nzsec=e.target.value;nzgrid()}});
document.addEventListener('keydown',e=>{if(e.key=='Escape'&&$('nz').classList.contains('on')){nzclose();e.stopImmediatePropagation()}},true);
async function choose(sec){spclose();await api('section',{sec});api('rpick')}
function rpclose(){spinTimers.forEach(clearTimeout);clearTimeout(back);$('rp').classList.remove('on');spinning=false;if(st&&st.roster)turnui(st.roster);if(pendingStart){pendingStart=false;api('rstart',{auto:1})}}
function lvVal(){return ($('lg').value-1)*4+(+$('ld').value)}
function setLv(){api('level',{v:lvVal()})}
async function gen(k){showAns=false;window.pbc=null;const r=await api('gen',{topic:tab||st.topics[0],level:lvVal(),kind:k});document.body.classList.add('proj');return r}
function pickbar(){const s=st.slide;if(s.type!='pick'||st.board)return '';const I=s.id;
 const chips='';
 return '<button class="p" onclick="api(\'pick\',{id:'+I+',cid:\'\'})">🎲 Random</button>'+chips+(s.turn?'<button onclick="api(\'mark\',{id:'+I+',cid:\''+s.turn+'\',m:\'ok\'})">✅ Correct</button><button onclick="api(\'mark\',{id:'+I+',cid:\''+s.turn+'\',m:\'no\'})">❌ Wrong</button><button onclick="api(\'clear\',{id:'+I+'})">Clear</button>':'')}
async function poll(){try{st=await (await fetch('/api/state?key='+K)).json()}catch(e){return}
 if(!st.slides){try{sessionStorage.mk=''}catch(e){}location.replace('/host');return}
 if(lastId!==st.slide.id){lastId=st.slide.id;tab=st.slide.topic}
 if(!tab)tab=st.topics[0];
 {const eff=(st.mix&&st.mix.length)?st.mix:[tab];$('tabs').innerHTML=st.topics.map(n=>'<button class="'+(eff.includes(n)&&!window.ROSV?'on':'')+'" onclick="tabClick(this.dataset.n)" data-n="'+esc(n)+'" title="Click to tick or untick this topic. Ticked topics are mixed.">'+(eff.includes(n)?'☑ ':'☐ ')+esc(n)+' ('+st.slides.filter(x=>x.topic==n).length+')</button>').join('')}
 $('side').innerHTML=st.slides.map((s,i)=>s.topic!=tab?'':'<div class="sl '+(i==st.cur?'on':'')+'" onclick="api(\'goto\',{i:'+i+'})">'+(s.auto?'🎲 ':'')+esc(s.q)+'<small class="mute"> · '+TN[s.type]+'</small></div>').join('')||'<p class="mute">No questions in this tab yet. Use the + buttons above.</p>';
 $('big').textContent=st.join;$('jn').textContent='📱 Students join: '+st.join;$('cnt').textContent=st.respondents+' participant'+(st.respondents==1?'':'s')+' on this slide';
 window.N=st.respondents;bysec(st);fin(st);tstrip(st);celeb(st);if($("tmo").classList.contains("on"))tmdraw();if($("tsb").classList.contains("on"))tsbdraw();if($("clo").classList.contains("on"))cldraw();document.querySelectorAll("#modes .mb").forEach(x=>x.classList.toggle("cur",x.dataset.m==st.mode));[["qtm","team","Teams"],["qts","team","Team scores"],["qbb","class","Boss battle"]].forEach(a=>{const q=$(a[0]);if(q){const off=st.mode!=a[1];q.disabled=off;q.title=off?"Switch Mode to "+(a[1]=="team"?"Team":"Class")+" to use "+a[2]:""}});{const T=$('toast');T.textContent=st.notice||'';T.style.display=st.notice?'block':'none'}tmr(st);bossdraw(st.boss);roster(st.roster);{const L=st.slide.q.length;$('q').className=st.board||L<45?'xl':L<110?'lg':'md'}$('q').innerHTML=st.board?(st.tmode&&(st.tboard||[]).length?'🏆 Team leaderboard':'🏆 Leaderboard'):mx(st.slide.q);
 {const r0=st.roster.rp;document.body.classList.toggle('idle',!st.board&&!(r0.show&&r0.picks&&r0.picks.length)&&!(st.tloop&&st.tmode)&&!(st.boss&&st.boss.st=='fight'))}
 {const rr=st.roster.rp;if(!st.board&&!spinning&&rr.show&&rr.picks&&rr.picks.some(x=>x.q)){
  $('q').className='mq'+(rr.picks.length>=4?' m4':'')+(rr.picks.length>=6?' m6':'');
  $('q').innerHTML=rr.picks.map(x=>'<div class="qi"><small>'+esc(x.name)+(new Set(rr.picks.map(y=>y.sec)).size>1?' · '+esc(x.sec):'')+'</small>'+mx(x.q||'')+(rr.fin?'<span class="qa">= '+mx(x.qa||'')+'</span>':'')+'</div>').join('')}}
{const aq=st.allq||[];if(!st.board&&!spinning&&!(st.roster.rp.show&&st.roster.rp.picks&&st.roster.rp.picks.length)&&((st.tmode&&st.tloop)||(st.boss&&st.boss.st=='fight'))&&st.slide.var&&aq.length){
  let last=null,h='';aq.forEach(x=>{if(x.t!==last){last=x.t;if(x.t||st.tmode)h+='<div class=\"aqt\">'+esc(x.t||'No team')+'</div>'}
   h+='<div class=\"aqc'+(x.ok===true?' ok':x.ok===false?' no':x.v!==''?' got':'')+'\"><small>'+esc(x.n)+(x.v!==''?' ✎':'')+'</small>'+mx(x.q)+(x.a!==''?'<span class=\"qa\">= '+mx(x.a)+'</span>':'')+'</div>'});
  {const q=$('q'),k=h+'|'+innerWidth+'x'+innerHeight+'|'+document.body.classList.contains('hast');if(q.className!=='aq'||q.dataset.aqk!==k){q.className='aq';q.innerHTML=h;q.dataset.aqk=k;q.style.fontSize='';q.style.gridTemplateColumns='';
   if(document.body.classList.contains('hast')){let fs=parseFloat(getComputedStyle(q).fontSize)||30;q.style.gridTemplateColumns='repeat(auto-fill,minmax(8.5em,1fr))';while(q.scrollHeight>q.clientHeight+1&&fs>9){fs-=1;q.style.fontSize=fs+'px'}}}}}}
$('res').innerHTML=st.board?(st.tmode&&(st.tboard||[]).length?tbd(st.tboard):board(st.top)):results(st.slide);const pb=pickbar()+(st.slide.type=='pick'&&st.slide.ans&&!st.board?'<button onclick="showAns=!showAns;window.pbc=null;poll()">👁 '+(showAns?esc(st.slide.ans):'Answer')+'</button>':'');if(window.pbc!==pb){window.pbc=pb;$('pickbar').innerHTML=pb}$('tg').textContent=st.gate?'⏸ Close voting':'▶ Open voting';
 if(edId!==st.slide.id)editor()}
document.addEventListener('keydown',e=>{if(e.key=='Escape'&&$('fin').classList.contains('on')){finHide();e.stopImmediatePropagation()}},true);
document.addEventListener('keydown',e=>{if(e.target.tagName=='INPUT'||!document.body.classList.contains('proj'))return;
 if(e.key=='ArrowRight')nav(1);if(e.key=='ArrowLeft')nav(-1);if(e.key=='r')api('reveal',{id:st.slide.id});if(e.key=='s')api('start',{id:st.slide.id});if(e.key=='b')api('board');if(e.key=='n')gen(st.slide.auto?st.slide.type:'pick');if(e.key=='a'){showAns=!showAns;window.pbc=null;poll()}if(e.key=='p')api('pick',{id:st.slide.id,cid:''});if(e.key=='y'||e.key=='x'){const m=e.key=='y'?'ok':'no';if($('turn').classList.contains('on')&&!(st.slide.type=='pick'&&st.slide.turn)){const K2=st.roster.rp.picks;let i=K2.findIndex(q=>!q.mark);if(i<0)i=K2.length-1;api('rmark',{i,m})}else api('mark',{id:st.slide.id,cid:st.slide.turn,m})}if(e.key=='m')nzopen();if(e.key=='o')podiumNow();if(e.key=='t')api('rstart');if(e.key==' '){e.preventDefault();api('rpause')}if(e.key=='0')api('rtreset');if(e.key=='c')spopen();if(e.key=='Escape'){if($('sp').classList.contains('on'))spclose();else if($('rp').classList.contains('on'))rpclose();else document.body.classList.remove('proj')}});
$('tpre').innerHTML=[10,20,30,60].map(v=>'<button data-t="'+v+'">'+v+'s</button>').join('')+'<input id="tcu" type="number" min="0" max="600" placeholder="sec" style="width:64px">';
document.querySelectorAll('#tpre button').forEach(b=>b.onclick=()=>api('rtime',{v:+b.dataset.t,start:1}));
$('tcu').onchange=e=>api('rtime',{v:+e.target.value,start:1});
$('tgo').onclick=()=>api('rstart');$('tpz').onclick=()=>api('rpause');$('trs').onclick=()=>api('rtreset');$('tx').onclick=()=>api('rclear');
$('fin').onclick=finHide;
$('tcards').onclick=e=>{const b=e.target.closest('button');if(b&&b.dataset.m)api('rmark',{i:+b.dataset.i,m:b.dataset.m});else if(b&&b.dataset.lf)api('lfundo',{i:+b.dataset.i})};
$('tcards').oninput=e=>{const t=e.target;if(!t.classList.contains('tai'))return;const i=+t.dataset.i;$('ta'+i).textContent=t.value;clearTimeout(tdb[i]);tdb[i]=setTimeout(()=>api('rans',{i,v:t.value}),400)};
$('tcards').onkeydown=e=>{if(e.key=='Enter'&&e.target.classList.contains('tai')){const i=+e.target.dataset.i;clearTimeout(tdb[i]);api('rans',{i,v:e.target.value,check:1})}};
let tmSel=null,tmSize=4,tmC="",tsC="";
const tbd=B=>{const T=B.slice().sort((a,b)=>b.tot-a.tot||a.name.localeCompare(b.name));return T.map((t,i)=>bar((i+1)+". "+esc(t.name),t.tot,T[0].tot,PAL[i%PAL.length])).join("")};
function tmopen(){if(!st||!st.roster||st.mode!="team")return;$("tmo").classList.add("on");tmC="";tmdraw()}
function tmclose(){$("tmo").classList.remove("on")}
function tmdraw(){if(!st||!st.roster)return;const S=st,B=S.tboard||[],R=S.roster,H=S.thist||[];
 $("tmsub").textContent=R.section+" · 1 point per correct answer · team mode "+(S.tmode?"ON":"OFF")+(B.length?" · "+B.length+" teams":" · no teams yet");
 {const N=R.names.length,h=$("tmhint");if(h)h.textContent=N?(N+" students → about "+Math.ceil(N/tmSize)+" teams of "+tmSize+($("tmon")&&$("tmon").checked?" (fewer if some are offline)":"")):""}
 const ord=B.slice().sort((a,b)=>(+a.id.slice(1))-(+b.id.slice(1))),used=new Set();B.forEach(t=>t.m.forEach(n=>used.add(n)));
 const free=R.names.filter(n=>!used.has(n)),chip=(n,t)=>'<span class="tmch'+(tmSel==n?" sel":"")+'" data-n="'+esc(n)+'">'+esc(n)+(t&&t.mc?' · <b>'+(t.mc[n]||0)+'</b>':'')+'</span>';
 const sz=[2,3,4,5,6].map(v=>'<button data-sz="'+v+'" class="'+(tmSize==v?"cur":"")+'">'+v+'</button>').join("");
 const g=ord.map(t=>'<div class="tmc2'+(t.done?' done':'')+'" data-t="'+t.id+'"><div class="tmn"><span class="tmr">#'+t.rank+'</span> '+esc(t.name)+' <button data-ren="'+t.id+'" title="Rename">✏</button> <button data-del="'+t.id+'" title="Remove this team">🗑</button></div><div class="tmpts"><b>'+t.tot+'</b>'+(S.tgoal>0?' / '+S.tgoal:'')+' pts'+(t.done?' <span class="tmok">✅ Can leave</span>':'')+(t.rnd?' <em>+'+t.rnd+' this round</em>':"")+' <small>(members '+t.raw+(t.adj?' '+(t.adj>0?'+':'−')+Math.abs(t.adj)+' teacher':'')+')</small>'+'</div><div class="tmm">'+t.m.map(n=>chip(n,t)).join("")+'</div><div class="tma">'+[-5,-3,-1,1,3,5].map(v=>'<button data-a="'+t.id+'" data-v="'+v+'" class="'+(v<0?"rd":"g")+'">'+(v>0?"+":"−")+Math.abs(v)+'</button>').join("")+'<button data-a="'+t.id+'" data-v="x">±…</button></div>'+(t.done?'<button class="tmrel" data-rel="'+t.id+'">🚪 Let this team leave</button>':'')+'</div>').join("")||'<p class="mute" style="grid-column:1/-1;text-align:center">No teams yet for '+esc(R.section)+'. Choose how many students per team in step 1, then press Make random teams.</p>';
 const f=free.length&&B.length?'<b>Not in a team ('+free.length+')</b> <span class="mute">tap a name, then tap a team card to move them</span><div class="tmm" style="margin-top:6px">'+free.map(n=>chip(n)).join("")+'</div>':"";
 const tb=ord.length?'<table class="tmht"><tr><th></th>'+ord.map(t=>"<th>"+esc(t.name)+"</th>").join("")+"</tr>"+H.map(h=>"<tr><td>Round "+h.n+"</td>"+ord.map(t=>"<td>+"+((h.v||{})[t.id]||0)+"</td>").join("")+"</tr>").join("")+"<tr><td>Teacher</td>"+ord.map(t=>"<td>"+(t.adj>0?"+":"")+t.adj+"</td>").join("")+'</tr><tr class="tot"><td>Total</td>'+ord.map(t=>"<td>"+t.tot+"</td>").join("")+"</tr></table>":"";
 const LL=S.tleft||[],lf=LL.length?'<div style="margin-top:12px"><b>🚪 Left the room ('+LL.length+')</b><div class="tmm" style="margin-top:6px">'+LL.map(e=>'<span class="tmch tmlf">'+esc(e.name)+' · '+e.tot+' pts <button data-back="'+e.id+'" title="Bring back into the session">↩</button> <button data-del="'+e.id+'" title="Remove this team">🗑</button></span>').join("")+'</div></div>':"";
 const key=sz+g+f+lf+tb+S.tmode+S.tlast+S.tloop;if(key===tmC)return;tmC=key;
 $("tmsz").innerHTML=sz;{const gi=$("tmgl");if(gi&&document.activeElement!==gi)gi.value=S.tgoal||0}$("tmg").innerHTML=g;$("tmf").innerHTML=f+lf;$("tmh").innerHTML=tb;
 $("tml").textContent=S.tloop?"⏹ Stop team game":"▶ Start team game";$("tmtg").textContent=S.tmode?"⏸ Turn team mode off":"▶ Turn team mode on";$("tmu").textContent="↩ Undo last"+(S.tlast?" ("+S.tlast+")":"")}
let tsbC="",tsbPrev={};
let tsbWasProj=false;
function tsbopen(){if(!st||!st.roster||st.mode!="team")return;if(!$("tsb").classList.contains("on"))tsbWasProj=document.body.classList.contains("proj");document.body.classList.add("proj");$("tmo").classList.remove("on");$("tsb").classList.add("on");tsbC="";tsbdraw()}
function tsbclose(){$("tsb").classList.remove("on");tsbPrev={};if(!tsbWasProj)document.body.classList.remove("proj")}
function tsbdraw(){if(!st||!st.roster)return;const S=st,sec=S.roster.section,goal=+S.tgoal||0;
 const A=(S.tboard||[]).map(t=>({id:t.id,name:t.name,tot:t.tot,rnd:t.rnd||0,done:!!t.done,m:t.m||[],left:false})).concat((S.tleft||[]).map(t=>({id:t.id,name:t.name,tot:t.tot||0,rnd:0,done:true,m:t.m||[],left:true})));
 A.sort((a,b)=>b.tot-a.tot||a.name.localeCompare(b.name));A.forEach(x=>x.rank=1+A.filter(y=>y.tot>x.tot).length);
 const key=sec+"|"+goal+"|"+S.tmode+"|"+A.map(x=>[x.id,x.name,x.tot,x.rnd,x.done,x.left,x.m.length].join(":")).join(",");
 if(key===tsbC)return;tsbC=key;
 const n=A.length,c=n<=5?1:n<=12?2:3,r=Math.max(1,Math.ceil(n/c)),mx=Math.max(goal,1,...A.map(x=>x.tot)),MD=["🥇","🥈","🥉"];
 $("tssub").textContent=sec+" · running totals, updated live · 1 point per correct answer"+(goal>0?" · goal "+goal+" pts":"")+(S.tmode?"":" · team mode is OFF");
 const L=$("tsl");L.style.setProperty("--c",c);L.style.setProperty("--r",r);
 L.innerHTML=n?A.map(x=>{const up=tsbPrev[x.id]!=null&&x.tot>tsbPrev[x.id],pct=Math.max(x.tot>0?3:0,Math.min(100,Math.round(100*x.tot/mx)));
  return '<div class="tsr'+(x.rank==1&&x.tot>0?" r1":"")+(x.left?" lf":"")+(up?" up":"")+'"><div class="tsk">'+(x.tot>0&&x.rank<=3?MD[x.rank-1]:"#"+x.rank)+'</div><div class="tsm"><div class="tsn">'+esc(x.name)+(x.left?' <span class="tsx">🚪 left the room</span>':x.done?' <span class="tsx">✅ goal reached</span>':"")+'</div><div class="tsbar"><i style="width:'+pct+'%"></i></div>'+(n>8?"":'<div class="tsmem">'+x.m.map(esc).join(" · ")+"</div>")+'</div><div class="tsp"><b>'+x.tot+"</b>"+(goal>0?"<small>/ "+goal+"</small>":"<small>pts</small>")+(x.rnd?"<em>+"+x.rnd+"</em>":"")+"</div></div>"}).join(""):'<div class="tse">No teams yet for '+esc(sec)+'.<br>Open 👥 Teams and press ▶ Start team game (or Make random teams).</div>';
 tsbPrev={};A.forEach(x=>tsbPrev[x.id]=x.tot)}
function tstrip(S){const B=(S.tboard||[]).slice().sort((a,b)=>b.tot-a.tot||a.name.localeCompare(b.name)),on=S.tmode&&B.length>0;
 const h=on?B.map(t=>'<span class="tsc'+(t.rank==1?" r1":"")+'"><i>'+(t.rank==1?"🥇":t.rank==2?"🥈":t.rank==3?"🥉":"")+"</i>"+esc(t.name)+" <b>"+t.tot+"</b>"+(S.tgoal>0?"/"+S.tgoal:"")+(t.done?" ✅":"")+(t.rnd?"<em>+"+t.rnd+"</em>":"")+"</span>").join(""):"";
 document.body.classList.toggle("hast",!!on);if(h===tsC)return;tsC=h;$("tstrip").innerHTML=h;$("tstrip").classList.toggle("has",!!on)}
document.addEventListener("click",async e=>{const T=e.target;if(!T.closest||!T.closest("#tmo"))return;
 const b=T.closest("button"),ch=T.closest(".tmch"),cd=T.closest(".tmc2");
 if(b&&b.dataset.sz){tmSize=+b.dataset.sz;tmC="";tmdraw();return}
 if(b&&b.dataset.rel){await api("trelease",{id:b.dataset.rel});tmC="";tmdraw();return}
 if(b&&b.dataset.back){await api("trestore",{id:b.dataset.back});tmC="";tmdraw();return}
 if(b&&b.dataset.del){if(confirm("Remove this team? Its points and history will be deleted.")){await api("tdel",{id:b.dataset.del});}tmC="";tmdraw();return}
 if(b&&b.dataset.a){let v=b.dataset.v;if(v=="x"){v=prompt("Points for this team (use - for a deduction, e.g. -4):","-1");if(v==null)return;v=parseFloat(String(v).replace("−","-"));if(!v)return}await api("tadj",{id:b.dataset.a,v:+v});tmdraw();return}
 if(b&&b.dataset.ren){const t=(st.tboard||[]).find(x=>x.id==b.dataset.ren),n=prompt("Team name:",t?t.name:"");if(n)await api("trename",{id:b.dataset.ren,name:n});tmdraw();return}
 if(ch){tmSel=tmSel==ch.dataset.n?null:ch.dataset.n;tmC="";tmdraw();return}
 if(cd&&tmSel&&!b){await api("tmove",{name:tmSel,to:cd.dataset.t});tmSel=null;tmC="";tmdraw()}});
$("tmmk").onclick=async()=>{if((st.tboard||[]).length&&!confirm("Replace the existing teams for this section? Team scores from teacher points and round history will be cleared."))return;await api("tmake",{size:tmSize,online:$("tmon").checked?1:0});tmC="";tmdraw()};
$("tmtg").onclick=async()=>{await api("tmode");tmC="";tmdraw()};$("tmon").onchange=()=>tmdraw();
$("tml").onclick=async()=>{const on=!st.tloop;await api("tloop",{topic:tab,size:tmSize,online:$("tmon").checked?1:0});if(on){tmclose();document.body.classList.add("proj")}tmC="";tmdraw()};
$("tmu").onclick=async()=>{await api("tundo");tmC="";tmdraw()};
$("tmgl").onchange=async e=>{await api("tgoal",{v:+e.target.value||0});tmC="";tmdraw()};
$("tmdl").onclick=()=>{if(!st||!st.roster)return;const B=(st.tboard||[]).slice().sort((a,b)=>(+a.id.slice(1))-(+b.id.slice(1))),H=st.thist||[],NL=String.fromCharCode(10);
 if(!B.length&&!(st.tleft||[]).length){alert("No teams to export yet.");return}
 const q=v=>{v=String(v==null?"":v);return /[",]/.test(v)||v.indexOf(NL)>=0?'"'+v.replace(/"/g,'""')+'"':v};
 const rows=[["Section","Team","Members"].concat(H.map(h=>"Round "+h.n),["Teacher adjustment","Total","Status"])];
 B.forEach(t=>rows.push([st.roster.section,t.name,t.m.map(n=>n+" ("+((t.mc||{})[n]||0)+")").join("; ")].concat(H.map(h=>(h.v||{})[t.id]||0),[t.adj||0,t.tot,t.done?"Goal reached":"In session"])));
 (st.tleft||[]).forEach(e=>rows.push([st.roster.section,e.name,e.m.join("; ")].concat(H.map(()=>""),["",e.tot,"Left the room"])));
 const d=new Date(),ds=d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0")+"-"+String(d.getDate()).padStart(2,"0");
 dlpdf("Team scores",st.roster.section+" · "+new Date().toLocaleDateString(),rows[0].slice(1),rows.slice(1).map(r=>r.slice(1)),[2,5].concat(H.map(()=>1),[1.3,1,1.6]),"team-scores-"+st.roster.section.replace(/[^A-Za-z0-9]+/g,"-")+"-"+ds+".pdf")};

$("tmrs").onclick=async()=>{if(confirm("New game: reset ALL team scores for this section (members' correct answers, teacher points and round history)?")){await api("treset");tmC="";tmdraw()}};
$("tmcl").onclick=async()=>{if(confirm("Remove all teams for this section?")){await api("tclear");tmC="";tmdraw()}};
let clC="";
function clopen(){if(!st||st.mode!="class")return;$("clo").classList.add("on");clC="";cldraw()}
function clclose(){$("clo").classList.remove("on")}
let LKD=false;const LKC=[['body','Body'],['line','Outline & brows'],['eyec','Eyes'],['mouthc','Mouth'],['hc','Accessory']],LKS=[['head','Headgear'],['eyes','Eyes'],['mouth','Mouth'],['face','Face accessory'],['neck','Chest accessory'],['legs','Legs']];
function lkbase(){return $("lk_base").value||'Lord Negatron'}
function lkGet(){const o={sym:$("lk_sym").value};LKC.forEach(x=>o[x[0]]=$("lk_"+x[0]).value);LKS.forEach(x=>o[x[0]]=$("lk_"+x[0]).value);return o}
function lkPrev(){const z=$("lkp");if(z)z.firstChild.innerHTML=bossSVG(lkbase(),lkGet())}
function lkInit(){if(!$("lk_base"))return;const k=bossLook(lkbase());LKC.concat(LKS).forEach(x=>$("lk_"+x[0]).value=k[x[0]]);$("lk_sym").value=k.sym;LKD=false;lkPrev()}
function lkForm(){const sel=(id,l)=>'<label>'+l[1]+'<select id="lk_'+l[0]+'">'+BL[l[0]].map(o=>'<option value="'+o[0]+'">'+o[1]+'</option>').join('')+'</select></label>';
 return '<details style="margin:10px 0;text-align:left"><summary style="cursor:pointer;font-weight:800">🎨 Customize the boss (face, colors, accessories)</summary><div style="display:flex;gap:16px;flex-wrap:wrap;align-items:flex-start;margin-top:10px"><div id="lkp" class="bsw" style="width:150px;height:180px;flex:none"><div class="bz"></div></div><div class="clf" style="flex:1;min-width:250px"><label>Character<select id="lk_base"><option value="">🎲 Random</option>'+Object.keys(BK).map(n=>'<option>'+esc(n)+'</option>').join('')+'</select></label>'+LKS.map(l=>sel('',l)).join('')+LKC.map(l=>'<label>'+l[1]+' color<input type="color" id="lk_'+l[0]+'"></label>').join('')+'<label>Belly symbol (up to 2 characters)<input id="lk_sym" maxlength="2"></label><div><button id="lk_rand">🎲 Surprise me</button> <button id="lk_reset">↺ Reset look</button></div></div></div></details>'}
document.addEventListener("input",e=>{const id=e.target.id||"";if(id=="lk_base")lkInit();else if(id.startsWith("lk_")){LKD=true;lkPrev()}});
function ctab(b){if(!b||!b.ct||!b.ct.length)return '';const idle=b.ct.filter(x=>x.idle).length;
 return '<div class="mute" style="margin:12px 0 4px">📋 Who is contributing'+(idle?' · <b style="color:#fca5a5">⚠ '+idle+' inactive</b>':'')+'</div><div style="max-height:34vh;overflow:auto;text-align:left"><table style="width:100%;border-collapse:collapse;font-size:14px"><tr class="mute"><th align="left">Student</th><th>✅ Correct</th><th>❌ Wrong</th><th>⏰ Skipped</th><th>⚡ Rushed</th><th>💥 Damage</th></tr>'+b.ct.map(x=>'<tr style="border-top:1px solid rgba(255,255,255,.1);'+(x.idle?'background:rgba(239,68,68,.18)':x.skip&&x.skip>=x.ok&&x.skip>1?'background:rgba(245,158,11,.12)':'')+'"><td>'+(x.idle?'⚠ ':'')+avi(x.a)+esc(x.n)+'</td><td align="center">'+x.ok+'</td><td align="center">'+x.bad+'</td><td align="center">'+x.skip+'</td><td align="center">'+(x.rush||0)+(x.streak>1?' <small>('+x.streak+' in a row)</small>':'')+'</td><td align="center">'+x.d+'</td></tr>').join('')+'</table></div>'}
function clseg(){const v=$("clh")&&$("clh").value;[3,5,8].forEach(n=>{const b=$("clh"+n);if(b)b.classList.toggle("cur",v==n)});clsum()}
function clsum(){if(!$("cls1")||!$("clh"))return;const T=[...document.querySelectorAll("#clo .clt")],on=T.filter(x=>x.checked).map(x=>x.value);
 $("cls1").textContent=!on.length?"none selected":on.length==T.length?"All topics ("+T.length+")":on.length<=2?on.join(", "):on.slice(0,2).join(", ")+" +"+(on.length-2)+" more";
 const h=+$("clh").value||5;$("cls2").textContent=({3:"Easy",5:"Normal",8:"Hard"}[h]||"Custom")+" · "+h+" per student"+($("clhp").value?" · HP "+$("clhp").value:"");
 $("cls3").textContent=($("clq").value||30)+" s per question · "+($("clm").value||60)+" min";
 $("cls4").textContent=($("clp").checked?"Own pace":"Together")+($("clv").checked?" · different numbers":"");
 $("cls5").textContent=["cla_o","cla_f","cla_b","cla_s","cla_i"].some(i=>+$(i).value)?"customised":"optional · by default no points change"}
document.addEventListener("input",e=>{if(e.target&&e.target.id=="clh")clseg();else if(e.target&&e.target.closest&&e.target.closest("#clo"))clsum()});
document.addEventListener("change",e=>{if(e.target&&e.target.closest&&e.target.closest("#clo"))clsum()});
function posSel(id,l){let o='';for(let v=0;v<=10;v++)o+='<option value="'+v+'">'+(v?'+'+v:'0 (no bonus)')+'</option>';return '<label>'+l+'<select id="'+id+'">'+o+'</select></label>'}
function adjSel(id,l){let o='';for(let v=10;v>=-10;v--)o+='<option value="'+v+'"'+(v==0?' selected':'')+'>'+(v>0?'+'+v:v<0?'\u2212'+(-v):'0 (no change)')+'</option>';return '<label>'+l+'<select id="'+id+'">'+o+'</select></label>'}
function cldraw(){const b=st.boss,S=st;$("clsub").textContent=(S.roster?S.roster.section:"")+" · the whole class plays together against one boss";
 let h="",key;
 if(b&&b.st=="fight"){key="f"+b.hp+"/"+b.max+"|"+(b.last?b.last.n:0);
  h='<div class="clbig">'+esc(b.name)+'</div><div class="mute">'+b.hp+' / '+b.max+' HP · the battle is running</div><div class="tmbar"><button class="p" id="clgo">📽 Go to projector</button><button id="clst">⏹ Stop battle</button><button id="clcx">Close</button></div>'+ctab(b)}
 else if(b&&(b.st=="won"||b.st=="lost")){key=b.st+"|"+b.hp;
  h='<div class="clbig">'+(b.st=="won"?"🎉 Boss defeated! The class wins!":"💀 Time is up. The boss survived with "+b.hp+" HP.")+'</div>'+(b.top&&b.top.length?'<div class="mute">Top hitters: '+b.top.map(x=>esc(x.n)+' ('+x.d+')').join(", ")+'</div>':'')+'<div class="tmbar"><button class="p" id="clnew">🔁 New battle</button><button id="clcx">Close</button></div>'+ctab(b)}
 else{key="idle";
  const chip=n=>'<label class="clchip"><input type="checkbox" class="clt" value="'+esc(n)+'"'+(((S.mix||[]).length?(S.mix||[]).includes(n):n==tab)?' checked':'')+'><span>'+esc(n)+'</span></label>';
  h='<div class="mute clintro">Every correct answer damages the boss (a faster answer hits harder) and every wrong answer heals it. The class wins by defeating the boss before the time runs out.</div>'
  +'<details class="clsec" open><summary class="tmct"><span class="tmstep">1</span>Topics to practise<small class="clsm" id="cls1"></small></summary><div class="clq2"><button class="mini" id="clall">Select all</button><button class="mini" id="clnone">Clear</button></div><div class="clchips">'+S.topics.map(chip).join("")+'</div></details>'
  +'<div class="clrow"><details class="clsec" open><summary class="tmct"><span class="tmstep">2</span>Boss difficulty<small class="clsm" id="cls2"></small></summary><div class="tmlab">Correct answers needed per student</div><div class="clseg"><button id="clh3">😊 Easy · 3</button><button id="clh5">⚔️ Normal · 5</button><button id="clh8">🔥 Hard · 8</button><input id="clh" type="number" min="1" max="60" value="5" title="Custom"></div><div class="clf clcol"><label>Exact boss HP (optional)<input id="clhp" type="number" min="1" max="100000" step="1" placeholder="Auto"><small>Leave empty to calculate it from the difficulty.</small></label></div></details>'
  +'<details class="clsec" open><summary class="tmct"><span class="tmstep">3</span>Time<small class="clsm" id="cls3"></small></summary><div class="clf clcol"><label>Seconds per question<input id="clq" type="number" min="5" max="300" value="30"><small>No answer in time counts as wrong. Answering early brings the next question at once.</small></label><label>Battle time limit (minutes, max 60)<input id="clm" type="number" min="1" max="60" value="60"></label></div></details></div>'
  +'<details class="clsec" open><summary class="tmct"><span class="tmstep">4</span>How students play<small class="clsm" id="cls4"></small></summary><label class="cltog"><input type="checkbox" id="clp" checked><span><b>Each student plays at their own pace</b><small>A correct answer hits the boss right away and the next question appears at once.</small></span></label><label class="cltog"><input type="checkbox" id="clv"><span><b>Everyone gets different numbers</b><small>Each student has their own version of the question.</small></span></label></details>'
  +'<details class="clsec"><summary><span class="tmstep">5</span>Points for each student <small class="clsm" id="cls5">optional · by default no points change</small></summary><div class="mute" style="margin-top:8px">+ gives points, − takes points off (never below 0).</div><div class="clf">'+posSel('cla_o','✅ Correct answer')+posSel('cla_f','⚡ Fast correct answer (under 10 seconds), extra')+adjSel('cla_b','❌ Wrong answer')+adjSel('cla_s','⏰ Skipped (no answer in time)')+adjSel('cla_i','😴 3 rounds in a row without a real answer (skipped or guessed), extra each time')+'</div></details>'
  +'<div class="clsec">'+lkForm()+'</div>'
  +'<div class="clfoot"><button class="p" id="clstart">⚔️ Start battle</button><button id="clcx">Close</button></div>'}
 if(key===clC)return;clC=key;$("clb").innerHTML=h;if(key=="idle"){lkInit();clseg()}}
document.addEventListener("click",async e=>{const b=e.target.closest&&e.target.closest("#clo button");if(!b)return;const id=b.id;
 if(id=="lk_rand"){const R_=a=>a[Math.floor(Math.random()*a.length)],hx=()=>'#'+Math.floor(Math.random()*16777215).toString(16).padStart(6,'0');LKS.forEach(x=>$("lk_"+x[0]).value=R_(BL[x[0]])[0]);['body','hc'].forEach(n=>$("lk_"+n).value=hx());LKD=true;lkPrev();return}
 if(id=="lk_reset"){lkInit();return}
 if(id=="clall"||id=="clnone"){document.querySelectorAll("#clo .clt").forEach(x=>x.checked=id=="clall");clsum();return}
 if(/^clh[358]$/.test(id)){$("clh").value=id.slice(3);clseg();return}
 if(id=="clcx"){clclose();return}
 if(id=="clgo"){clclose();document.body.classList.add("proj");return}
 if(id=="clst"){if(confirm("Stop the boss battle?")){await api("bossstop");clC="";cldraw()}return}
 if(id=="clnew"){await api("bossstop");clC="";cldraw();return}
 if(id=="clstart"){const ts=[...document.querySelectorAll("#clo .clt:checked")].map(x=>x.value);if(!ts.length){alert("Tick at least one topic.");return}await api("bossstart",{bname:$("lk_base").value,look:LKD?lkGet():null,mins:Math.max(1,Math.min(60,+$("clm").value||60)),hpp:+$("clh").value||5,bhp:$("clhp").value,qsec:+$("clq").value||30,pace:$("clp").checked,adjo:+$("cla_o").value,adjf:+$("cla_f").value,adjb:+$("cla_b").value,adjs:+$("cla_s").value,adji:+$("cla_i").value,mix:ts.length>1,var:$("clv").checked,topic:ts[0],topics:ts});clclose();document.body.classList.add("proj");clC=""}});
document.addEventListener("click",async e=>{const b=e.target.closest&&e.target.closest("#modes .mb");if(!b)return;const m=b.dataset.m;
 if(st&&m!=st.mode)await api("mode",{v:m});
 });
document.addEventListener("keydown",e=>{if(e.key=="Escape"&&$("clo").classList.contains("on")){clclose();e.stopImmediatePropagation()}},true);
$("tmx").onclick=tmclose;$("tsbo").onclick=tsbopen;
document.addEventListener("keydown",e=>{if(e.key=="Escape"&&$("tsb").classList.contains("on")){tsbclose();e.stopImmediatePropagation()}},true);
document.addEventListener("keydown",e=>{if(e.key=="Escape"&&$("tmo").classList.contains("on")){tmclose();e.stopImmediatePropagation()}},true);
document.addEventListener("keydown",e=>{if(e.target.tagName=="INPUT"||!document.body.classList.contains("proj")||e.ctrlKey||e.metaKey)return;if(e.key=="g")tmopen();if(e.key=="k")clopen();if(e.key=="v"){if($("tsb").classList.contains("on"))tsbclose();else tsbopen()}});
let MRD=null,MRS="",MRT="All";
function errh(){const E=(MRD.err||{})[MRS]||{},A=(MRD.acc||{})[MRS]||{},L=MRD.lab||{},T=MRD.topics;
 const rows=T.filter(t=>E[t]&&Object.keys(E[t]).length).map(t=>'<div style="margin-top:3px"><b>'+esc(t)+'</b>'+(A[t]&&A[t][1]?' ('+Math.round(100*A[t][0]/A[t][1])+'% correct): ':': ')+Object.keys(E[t]).sort((a,b)=>E[t][b]-E[t][a]).map(k=>esc(L[k]||k)+' x'+E[t][k]).join(', ')+'</div>').join('');
 return '<div style="margin:0 0 12px;padding:10px 14px;border-radius:14px;background:rgba(124,58,237,.08)"><b>🔎 Common mistakes in this section</b> <small class="mute">(from wrong answers, all sessions: use them to choose what to re-teach)</small>'+(rows||'<div class="mute" style="margin-top:3px">No wrong answers recorded yet.</div>')+'</div>'}
function mrcalc(d){const pc=(o,a)=>a?Math.min(100,Math.round(100*o/a)):null,np=pc(d.now[0],d.now[1]),pp=pc(d.prev[0],d.prev[1]),dl=np!=null&&pp!=null?np-pp:null;
 const s=np==null?"— no attempts now":pp==null?"🆕 No history yet":dl>=5?"▲ Improved":dl<=-5?"▼ Declined":"＝ Steady";
 const b=d.now[1]<3?"—":np>=85?"🏅 Mastered":np>=70?"Proficient":np>=50?"Developing":"Needs support";
 return {np,pp,dl,s,b}}
function mrspark(d){const bar=(p,t,c,m)=>'<i title="'+t+'" style="width:7px;height:'+Math.max(3,Math.round(p*.3))+'px;background:'+c+';border-radius:2px;'+(m||'')+'"></i>',np=d.now[1]?Math.min(100,Math.round(100*d.now[0]/d.now[1])):null;
 return '<span style="display:inline-flex;align-items:flex-end;gap:2px;height:30px">'+d.tr.map(p=>bar(p,p+'%','#a78bfa')).join("")+(np!=null?bar(np,'Now '+np+'%','#ec4899','margin-left:5px'):'')+'</span>'}
async function mropen(){let o=$("mro");if(!o){o=document.createElement("div");o.id="mro";o.style.cssText="position:fixed;top:0;left:0;right:0;bottom:0;z-index:80;background:rgba(10,8,30,.82);display:flex;align-items:center;justify-content:center;padding:16px";o.onclick=e=>{if(e.target===o)o.style.display="none"};document.body.appendChild(o)}
 o.style.display="flex";o.innerHTML='<div class="card" style="max-width:1100px;width:100%;max-height:92vh;overflow:auto">Loading...</div>';
 try{MRD=await (await fetch("/api/mastery?key="+encodeURIComponent(K))).json()}catch(e){o.firstChild.textContent="Cannot load the report.";return}
 if(!MRS||!MRD.m[MRS])MRS=(st&&st.roster&&MRD.m[st.roster.section]?st.roster.section:Object.keys(MRD.m)[0]);mrrender()}
function mrrender(){const o=$("mro"),T=MRD.topics,M=MRD.m[MRS]||{},so=window.mrsort||"now";
 const rows=Object.keys(M).map(n=>{const d=M[n][MRT];return {n:n,d:d,c:mrcalc(d)}});
 rows.sort(so=="name"?(a,b)=>a.n.localeCompare(b.n):so=="chg"?(a,b)=>((a.c.dl==null)-(b.c.dl==null))||((a.c.dl||0)-(b.c.dl||0))||a.n.localeCompare(b.n):(a,b)=>((b.c.np==null?-1:b.c.np)-(a.c.np==null?-1:a.c.np))||a.n.localeCompare(b.n));
 const cn=[0,0],cp=[0,0];let im=0,de=0,sd=0;rows.forEach(r=>{cn[0]+=r.d.now[0];cn[1]+=r.d.now[1];cp[0]+=r.d.prev[0];cp[1]+=r.d.prev[1];const f=r.c.s[0];if(f=="▲")im++;else if(f=="▼")de++;else if(f=="＝")sd++});
 const cs=mrcalc({now:cn,prev:cp}),fp=v=>v==null?"–":v+"%",col=v=>v==null?"":v>0?"color:#059669;font-weight:700":v<0?"color:#dc2626;font-weight:700":"",chg=v=>v==null?"–":(v>0?"+":"")+v+" pts";
 const chip=(b,l,x)=>'<div style="padding:8px 16px;border-radius:14px;background:rgba(124,58,237,.12);text-align:center"><b style="font-size:22px;'+(x||"")+'">'+b+'</b><br><small>'+l+'</small></div>';
 o.innerHTML='<div class="card" style="max-width:1100px;width:100%;max-height:92vh;overflow:auto"><h2 style="margin:0 0 6px">📈 Topic mastery report</h2><p class="mute" style="margin:0 0 10px">Accuracy in this session (#'+MRD.lsn+') compared with the average of the last 10 earlier sessions each student took part in. A pass or ask-a-friend counts as an attempt. Change of 5 points or more counts as improved or declined.</p>'
 +'<div class="row" style="flex-wrap:wrap;gap:8px;margin-bottom:10px"><select id="mrs">'+Object.keys(MRD.m).map(k=>'<option'+(k==MRS?" selected":"")+'>'+esc(k)+'</option>').join("")+'</select><select id="mrt"><option value="All"'+(MRT=="All"?" selected":"")+'>All topics</option>'+T.map(t=>'<option'+(t==MRT?" selected":"")+'>'+esc(t)+'</option>').join("")+'</select><select id="mro2"><option value="now"'+(so=="now"?" selected":"")+'>Sort: highest score now</option><option value="chg"'+(so=="chg"?" selected":"")+'>Sort: biggest drop first</option><option value="name"'+(so=="name"?" selected":"")+'>Sort: name</option></select><button class="p" id="mrd">📄 Download PDF (all sections)</button><button id="mrx">Close</button></div>'
 +'<div style="display:flex;gap:10px;flex-wrap:wrap;margin:0 0 12px">'+chip(fp(cs.np),"Class now")+chip(fp(cs.pp),"Class, last 10 sessions")+chip(chg(cs.dl),"Change",col(cs.dl))+chip(im,"▲ Improved")+chip(sd,"＝ Steady")+chip(de,"▼ Declined")+'</div>'+errh()
 +'<table class="tmht" style="margin:0;width:100%"><tr><th style="text-align:left">Student</th><th>Now</th><th>Last 10 sessions</th><th>Trend<br><small>(violet = past, pink = now)</small></th><th>Change</th><th>Status</th><th>Level now</th></tr>'
 +rows.map(r=>{const d=r.d,c=r.c;return '<tr><td style="text-align:left">'+esc(r.n)+'</td><td>'+d.now[0]+'/'+d.now[1]+(c.np!=null?' · <b>'+c.np+'%</b>':'')+'</td><td>'+(d.n?(d.prev[0]/d.n).toFixed(1)+' correct/session · <b>'+c.pp+'%</b> <small>('+d.n+' sess.)</small>':'–')+'</td><td>'+mrspark(d)+'</td><td style="'+col(c.dl)+'">'+chg(c.dl)+'</td><td>'+c.s+'</td><td>'+c.b+'</td></tr>'}).join("")+'</table></div>';
 $("mrs").onchange=e=>{MRS=e.target.value;mrrender()};$("mrt").onchange=e=>{MRT=e.target.value;mrrender()};$("mro2").onchange=e=>{window.mrsort=e.target.value;mrrender()};$("mrx").onclick=()=>{o.style.display="none"};
 $("mrd").onclick=()=>{const cols=["Student"].concat(T,["Overall now","Change","Status"]),rows=[];
  Object.keys(MRD.m).forEach(k=>{rows.push(k);Object.keys(MRD.m[k]).forEach(n=>{const cc=mrcalc(MRD.m[k][n]["All"]);rows.push([n].concat(T.map(t=>{const c=mrcalc(MRD.m[k][n][t]);return c.np==null?"-":c.np+"%"}),[cc.np==null?"-":cc.np+"%",cc.dl==null?"-":(cc.dl>0?"+":"")+cc.dl,cc.s]))})});
  dlpdf("Topic mastery","Session "+MRD.lsn+" · "+new Date().toLocaleDateString(),cols,rows,[3.2].concat(T.map(()=>1.15),[1.2,1,1.5]),"topic-mastery-"+new Date().toISOString().slice(0,10)+".pdf")}}
let SKD=null,SKS="",SKN="",SKO="name";
const SKTIP={add:'Practise column addition and carrying (regrouping). Check by adding the numbers in a different order.',sub:'Practise borrowing (regrouping). Check by adding the answer to the number taken away.',mul:'Review the times tables, then break big numbers into tens and ones and add the partial products.',div:'Think of division as the opposite of multiplication. Check by multiplying the answer by the divisor.'};
const SKERRTXT={sign:'sign rules (positive and negative numbers)',slip:'small off-by-one slips: ask for a re-check of the last step',place:'place value and zeros: line up the digits and estimate the size first',operation:'choosing the wrong operation: re-read what the question asks',format:'typing answers that are not numbers',other:'mixed mistakes: compare the worked solution step by step'};
function skpc(a){return a&&a[1]?Math.min(100,Math.round(100*a[0]/a[1])):null}
function skrate(p,n){
 if(p==null||n<3)return {t:'Not enough data',i:'–',c:'#6b7080',bg:'rgba(107,112,128,.12)',k:0};
 if(p>=85)return {t:'Strength',i:'🏅',c:'#047857',bg:'rgba(16,185,129,.2)',k:4};
 if(p>=70)return {t:'Proficient',i:'✅',c:'#15803d',bg:'rgba(132,204,22,.2)',k:3};
 if(p>=50)return {t:'Developing',i:'🔧',c:'#b45309',bg:'rgba(245,158,11,.22)',k:2};
 return {t:'Weakness',i:'⚠️',c:'#b91c1c',bg:'rgba(239,68,68,.2)',k:1}}
function sktop(e){const ks=Object.keys(e||{}).filter(t=>e[t]>0);if(!ks.length)return null;const pr=ks.filter(t=>t!='other'&&t!='format'),pool=pr.length?pr:ks;pool.sort((a,b)=>e[b]-e[a]);return {t:pool[0],n:e[pool[0]]}}
function sktag(d){const c={};SKD.skills.forEach(s=>{const e=d[s[0]].err;Object.keys(e).forEach(t=>{c[t]=(c[t]||0)+e[t]})});return sktop(c)}
function sksum(M){const o={};SKD.skills.forEach(s=>{const k=s[0];let c=0,a=0,st=0,wk=0;Object.keys(M).forEach(nm=>{const d=M[nm][k],r=skrate(skpc(d.all),d.all[1]);c+=d.all[0];a+=d.all[1];if(r.k>=3)st++;if(r.k==1||r.k==2)wk++});o[k]={c:c,a:a,p:a?Math.round(100*c/a):null,st:st,wk:wk}});return o}
function skstu(d){const L=SKD.skills.map(s=>{const k=s[0],a=d[k].all,p=skpc(a);return {k:k,l:s[1],y:s[2],p:p,c:a[0],a:a[1],r:skrate(p,a[1])}});
 return {L:L,st:L.filter(x=>x.r.k>=3).sort((a,b)=>b.p-a.p),wk:L.filter(x=>x.r.k==1||x.r.k==2).sort((a,b)=>a.p-b.p),na:L.filter(x=>x.r.k==0)}}
function skavg(s){const e=s.L.filter(x=>x.r.k);return e.length?e.reduce((a,x)=>a+x.p,0)/e.length:null}
function skadvice(x,e){
 if(x.r.k==0)return 'Give more '+x.l.toLowerCase()+' questions (at least 3 attempts) so this skill can be graded.';
 const t=[];
 if(x.r.k==4)t.push('Strong skill. Move to harder levels or mixed problems; this student can help classmates.');
 else if(x.r.k==3)t.push('Good. A few more correct answers will make this a strength.');
 else t.push(SKTIP[x.k]);
 const te=sktop(e.err);if(x.r.k<=2&&te)t.push('Most mistakes are about '+SKERRTXT[te.t]+'.');
 const b=skpc(e.bo),n=skpc(e['in']);if(x.r.k<=3&&e.bo[1]>=3&&e['in'][1]>=3&&b-n>=20)t.push('Whole numbers are fine, but negative numbers are weaker: review the sign rules.');
 return t.join(' ')}
function sktrend(e){const now=skpc(e.now),pv=skpc(e.prev),dl=now!=null&&pv!=null?now-pv:null;
 return now==null?'No attempts this session':pv==null?'This session '+now+'% ('+e.now[0]+'/'+e.now[1]+') · no earlier sessions yet':'This session '+now+'% ('+e.now[0]+'/'+e.now[1]+') vs earlier sessions '+pv+'% · '+(dl>=5?'▲ Improved':dl<=-5?'▼ Declined':'＝ Steady')}
function sktp(T,k){const a=T&&T.pre&&T.pre[k],b=T&&T.post&&T.post[k],f=v=>v?v[0]+'/'+v[1]+' ('+skpc(v)+'%)':'';return {a:f(a),b:f(b),g:a&&b?skpc(b)-skpc(a):null}}
function sktest(T,k){const x=sktp(T,k);if(!x.a&&!x.b)return null;if(!x.b)return 'Pre-test '+x.a;if(!x.a)return 'Post-test '+x.b;return 'Pre-test '+x.a+' → Post-test '+x.b+(x.g==null?'':' · '+(x.g>0?'+':'')+x.g+' pts')}
function skmix(e){const b=skpc(e.bo),n=skpc(e['in']);if(b==null&&n==null)return null;
 return 'Whole numbers '+(b==null?'–':b+'% ('+e.bo[0]+'/'+e.bo[1]+')')+' · With negatives '+(n==null?'–':n+'% ('+e['in'][0]+'/'+e['in'][1]+')')}
async function skopen(){let o=$('sko');if(!o){o=document.createElement('div');o.id='sko';o.style.cssText='position:fixed;top:0;left:0;right:0;bottom:0;z-index:80;background:rgba(10,8,30,.82);display:flex;align-items:center;justify-content:center;padding:16px';o.onclick=e=>{if(e.target===o)o.style.display='none'};document.body.appendChild(o)}
 o.style.display='flex';o.innerHTML='<div class="card" style="max-width:1100px;width:100%;max-height:92vh;overflow:auto">Loading...</div>';
 try{SKD=await (await fetch('/api/skills?key='+encodeURIComponent(K))).json()}catch(e){o.firstChild.textContent='Cannot load the report.';return}
 if(!SKS||!SKD.m[SKS])SKS=(st&&st.roster&&SKD.m[st.roster.section]?st.roster.section:Object.keys(SKD.m)[0]);SKN='';skrender()}
function skrender(){const o=$('sko'),M=SKD.m[SKS]||{};
 if(SKN&&M[SKN]){skind(o,M[SKN],SKN);return}
 SKN='';const rows=Object.keys(M).map(n=>({n:n,d:M[n],s:skstu(M[n])})),av=r=>skavg(r.s);
 rows.sort(SKO=='name'?(a,b)=>a.n.localeCompare(b.n):SKO=='low'?(a,b)=>((av(a)==null)-(av(b)==null))||((av(a)||0)-(av(b)||0))||a.n.localeCompare(b.n):(a,b)=>((av(b)==null?-1:av(b))-(av(a)==null?-1:av(a)))||a.n.localeCompare(b.n));
 const C=sksum(M),tile=s=>{const c=C[s[0]],r=skrate(c.p,c.a);return '<div style="flex:1;min-width:150px;padding:10px 14px;border-radius:14px;background:'+r.bg+'"><b>'+esc(s[1])+' '+s[2]+'</b><br><b style="font-size:24px;color:'+r.c+'">'+(c.p==null?'–':c.p+'%')+'</b> <small>'+c.c+'/'+c.a+'</small><br><small>'+r.i+' '+r.t+'</small><br><small>'+c.st+' strong · '+c.wk+' need support</small></div>'};
 const ce=SKD.skills.filter(s=>C[s[0]].a>=3).sort((a,b)=>C[b[0]].p-C[a[0]].p),
  head=ce.length>=2?'Class strongest: <b>'+esc(ce[0][1])+'</b> ('+C[ce[0][0]].p+'%) · Needs the most work: <b>'+esc(ce[ce.length-1][1])+'</b> ('+C[ce[ce.length-1][0]].p+'%)':'Not enough answers yet to compare the skills. Run more Basic Operations and Integers questions.';
 const cell=x=>'<td style="background:'+x.r.bg+'">'+(x.p==null?'<small>–</small>':'<b style="color:'+x.r.c+'">'+x.p+'%</b><br><small>'+x.c+'/'+x.a+'</small>')+'</td>',
  nm=l=>l.length?l.map(x=>esc(x.l)).join(', '):'–';
 o.innerHTML='<div class="card" style="max-width:1100px;width:100%;max-height:92vh;overflow:auto"><h2 style="margin:0 0 6px">🧮 Operation skills report</h2><p class="mute" style="margin:0 0 10px">Every student is graded separately in addition, subtraction, multiplication and division (all sessions together). Only plain two-number questions on the Basic Operations and Integers tabs are counted, for example 48 + 17 or -6 × 4. A skill needs at least 3 attempts to be graded. 🏅 Strength 85%+ · ✅ Proficient 70-84% · 🔧 Developing 50-69% · ⚠️ Weakness below 50%. Click a student for the individual report.</p>'
 +'<div class="row" style="flex-wrap:wrap;gap:8px;margin-bottom:10px"><select id="sks">'+Object.keys(SKD.m).map(k=>'<option'+(k==SKS?' selected':'')+'>'+esc(k)+'</option>').join('')+'</select><select id="sko2"><option value="name"'+(SKO=='name'?' selected':'')+'>Sort: name</option><option value="low"'+(SKO=='low'?' selected':'')+'>Sort: needs support first</option><option value="high"'+(SKO=='high'?' selected':'')+'>Sort: strongest first</option></select><button class="p" id="skd">📄 Download PDF (all sections)</button><button id="skx">Close</button></div>'
 +'<div style="display:flex;gap:10px;flex-wrap:wrap;margin:0 0 10px">'+SKD.skills.map(tile).join('')+'</div><p style="margin:0 0 10px">'+head+'</p>'
 +'<table class="tmht" style="margin:0;width:100%"><tr><th style="text-align:left">Student</th>'+SKD.skills.map(s=>'<th>'+esc(s[1])+' '+s[2]+'</th>').join('')+'<th>Strong in</th><th>Needs work</th><th>Most common mistake</th></tr>'
 +rows.map((r,i)=>{const tg=sktag(r.d);return '<tr class="skr" data-i="'+i+'" style="cursor:pointer"><td style="text-align:left"><b>'+esc(r.n)+'</b></td>'+r.s.L.map(cell).join('')+'<td>'+nm(r.s.st)+'</td><td>'+nm(r.s.wk)+'</td><td>'+(tg?esc(SKD.lab[tg.t]||tg.t)+' <small>×'+tg.n+'</small>':'–')+'</td></tr>'}).join('')+'</table></div>';
 $('sks').onchange=e=>{SKS=e.target.value;skrender()};$('sko2').onchange=e=>{SKO=e.target.value;skrender()};$('skx').onclick=()=>{o.style.display='none'};
 document.querySelectorAll('#sko .skr').forEach(tr=>tr.onclick=()=>{SKN=rows[+tr.dataset.i].n;skrender()});
 $('skd').onclick=()=>{const cols=['Student'].concat(SKD.skills.map(s=>s[1]),['Strong in','Needs work']),pr=[];
  Object.keys(SKD.m).forEach(k=>{pr.push(k);const MM=SKD.m[k],CC=sksum(MM);pr.push(['Class'].concat(SKD.skills.map(s=>{const c=CC[s[0]];return c.p==null?'-':c.p+'% ('+c.c+'/'+c.a+')'}),['','']));
   Object.keys(MM).forEach(n=>{const S=skstu(MM[n]);pr.push([n].concat(S.L.map(x=>x.p==null?'-':x.p+'% '+x.r.t),[S.st.map(x=>x.l).join(', ')||'-',S.wk.map(x=>x.l).join(', ')||'-']))})});
  dlpdf('Operation skills report','Session '+SKD.lsn+' · '+new Date().toLocaleDateString(),cols,pr,[3,2,2,2.3,2,2.2,2.2],'skills-report-'+new Date().toISOString().slice(0,10)+'.pdf')}}
function skind(o,d,nm){const S=skstu(d),T=((SKD.tests||{})[SKS]||{})[nm]||{},ER=SKD.lab,list=l=>l.length?l.map(x=>esc(x.l)+' ('+x.p+'%)').join(', '):'none yet';
 const card=x=>{const e=d[x.k],te=sktop(e.err),ts=sktest(T,x.k),mx=skmix(e);
  return '<div style="padding:12px 14px;border-radius:14px;background:'+x.r.bg+';min-width:240px;flex:1"><div style="display:flex;justify-content:space-between;align-items:baseline"><b style="font-size:16px">'+esc(x.l)+' '+x.y+'</b><b style="color:'+x.r.c+'">'+x.r.i+' '+x.r.t+'</b></div>'
  +'<div style="font-size:28px;font-weight:800;color:'+x.r.c+'">'+(x.p==null?'–':x.p+'%')+' <small style="font-size:13px;font-weight:400">'+x.c+' correct of '+x.a+'</small></div>'
  +'<div style="height:8px;border-radius:6px;background:rgba(0,0,0,.1);margin:4px 0 8px"><div style="height:8px;border-radius:6px;background:'+x.r.c+';width:'+(x.p||0)+'%"></div></div>'
  +'<small>'+sktrend(e)+'</small>'+(mx?'<br><small>'+mx+'</small>':'')+(ts?'<br><small>'+ts+'</small>':'')
  +(te?'<br><small>Most common mistake: <b>'+esc(ER[te.t]||te.t)+'</b> ×'+te.n+'</small>':'')+'<br><small><b>What to do:</b> '+esc(skadvice(x,e))+'</small></div>'};
 o.innerHTML='<div class="card" style="max-width:1100px;width:100%;max-height:92vh;overflow:auto"><h2 style="margin:0 0 6px">🧮 Skill report: '+esc(nm)+'</h2><p class="mute" style="margin:0 0 10px">'+esc(SKS)+' · Session #'+SKD.lsn+' · '+new Date().toLocaleDateString()+'</p>'
 +'<div class="row" style="flex-wrap:wrap;gap:8px;margin-bottom:10px"><button id="skb">← All students</button><button class="p" id="skp">📄 Download this report (PDF)</button><button id="skx">Close</button></div>'
 +'<div style="padding:10px 14px;border-radius:14px;background:rgba(124,58,237,.1);margin-bottom:12px;line-height:1.7"><b>💪 Strengths:</b> '+list(S.st)+'<br><b>🎯 Needs work:</b> '+list(S.wk)+(S.na.length?'<br><b>ℹ️ Not enough data yet:</b> '+S.na.map(x=>esc(x.l)).join(', '):'')+'</div>'
 +'<div style="display:flex;gap:10px;flex-wrap:wrap">'+S.L.map(card).join('')+'</div></div>';
 $('skb').onclick=()=>{SKN='';skrender()};$('skx').onclick=()=>{o.style.display='none'};
 $('skp').onclick=()=>{const cols=['Skill','Score','Rating','This session','Whole / negatives','Pre → Post test','Common mistake','What to do'],pr=S.L.map(x=>{const e=d[x.k],te=sktop(e.err),mx=skmix(e),ts=sktest(T,x.k);
   return [x.l,x.p==null?'-':x.p+'% ('+x.c+'/'+x.a+')',x.r.t,sktrend(e),mx||'-',(x=>x.a||x.b?(x.a+(x.b?' > '+x.b:'')):'-')(sktp(T,x.k)),te?(ER[te.t]||te.t)+' x'+te.n:'-',skadvice(x,e)]});
  pr.unshift(('Strengths: '+(S.st.map(x=>x.l).join(', ')||'none yet')+'  |  Needs work: '+(S.wk.map(x=>x.l).join(', ')||'none')).slice(0,100));
  dlpdf('Skill report: '+nm,SKS+' · Session '+SKD.lsn+' · '+new Date().toLocaleDateString(),cols,pr,[1.5,1.5,1.2,2.6,2.2,2,1.8,4],'skill-report-'+nm.replace(/[^A-Za-z0-9]+/g,'-')+'.pdf')}}

let LFD=null,LFS="";
async function lfopen(){let o=$("lfo");if(!o){o=document.createElement("div");o.id="lfo";o.style.cssText="position:fixed;top:0;left:0;right:0;bottom:0;z-index:80;background:rgba(10,8,30,.82);display:flex;align-items:center;justify-content:center;padding:16px";o.onclick=e=>{if(e.target===o)o.style.display="none"};document.body.appendChild(o)}
 o.style.display="flex";o.innerHTML='<div class="card" style="max-width:900px;width:100%;max-height:90vh;overflow:auto">Loading...</div>';
 try{LFD=await (await fetch("/api/life?key="+encodeURIComponent(K))).json()}catch(e){o.firstChild.textContent="Cannot load the totals.";return}
 if(!LFS||!LFD.life[LFS])LFS=(st&&st.roster&&st.roster.section&&LFD.life[st.roster.section]?st.roster.section:Object.keys(LFD.life)[0]);lfrender()}
function lfrender(){const o=$("lfo"),T=LFD.topics,tot=r=>T.reduce((a,t)=>a+(r[t]||0),0),M=LFD.life[LFS]||{},AT=(LFD.att||{})[LFS]||{},att=n=>{const a=AT[n]||{};return T.reduce((x,t)=>x+(a[t]||0),0)};
 const rows=Object.keys(M).map(n=>({n:n,r:M[n],t:tot(M[n])})).sort((a,b)=>b.t-a.t||a.n.localeCompare(b.n));
 o.innerHTML='<div class="card" style="max-width:900px;width:100%;max-height:90vh;overflow:auto"><h2 style="margin:0 0 6px">📚 Cumulative scores (all sessions)</h2><p class="mute" style="margin:0 0 10px">Points / attempts per topic (for example 5/8 = 5 points from 8 attempts). A pass or an ask-a-friend counts as an attempt for the picked student. They keep adding up every session, even after the goal progress is reset.</p>'
 +'<div class="row" style="flex-wrap:wrap;gap:8px;margin-bottom:10px"><select id="lfs">'+Object.keys(LFD.life).map(k=>'<option'+(k==LFS?" selected":"")+'>'+esc(k)+'</option>').join("")+'</select><button class="p" id="lfd">📄 Download PDF (all sections)</button><button id="lfr">Reset all totals</button><button id="lfx">Close</button></div>'
 +'<table class="tmht" style="margin:0;width:100%"><tr><th style="text-align:left">Student</th>'+T.map(t=>'<th>'+esc(t)+'</th>').join("")+'<th>Total</th></tr>'
 +rows.map(x=>'<tr><td style="text-align:left">'+esc(x.n)+'</td>'+T.map(t=>'<td>'+(x.r[t]||0)+'/'+((AT[x.n]||{})[t]||0)+'</td>').join("")+'<td><b>'+x.t+'/'+att(x.n)+'</b></td></tr>').join("")+'</table></div>';
 $("lfs").onchange=e=>{LFS=e.target.value;lfrender()};$("lfx").onclick=()=>{o.style.display="none"};
 $("lfr").onclick=async()=>{if(confirm("Erase the cumulative totals of ALL students in ALL sections? This cannot be undone.")){await api("liferesetall");await lfopen()}};
 $("lfd").onclick=()=>{const cols=["Student"].concat(T,["Total"]),rows=[];
  Object.keys(LFD.life).forEach(k=>{rows.push(k);Object.keys(LFD.life[k]).forEach(n=>{const r=LFD.life[k][n],a=((LFD.att||{})[k]||{})[n]||{};rows.push([n].concat(T.map(t=>(r[t]||0)+"/"+(a[t]||0)),[tot(r)+"/"+tot(a)]))})});
  dlpdf("Cumulative scores (all sessions)","Points / attempts per topic · "+new Date().toLocaleDateString(),cols,rows,[3.2].concat(T.map(()=>1.1),[1.2]),"cumulative-scores-"+new Date().toISOString().slice(0,10)+".pdf")}}
/* ===== Roster tab: add / rename / remove sections, add / remove students, paste a class list ===== */
window.ROSV=false;let RSD=null,RSS='',RSMSG=null,RSUN=null,RSQ='';
async function rsApi(a,d){try{const r=await fetch('/api/roster',{method:'POST',body:JSON.stringify(Object.assign({key:K,a:a},d||{}))});const j=await r.json();
 if(j&&j.sections){RSD=j.sections;if(j.sel)RSS=j.sel}RSMSG=j&&j.msg?{t:j.msg,ok:!!j.ok}:null;RSUN=(j&&j.undo)||null;return j}
 catch(e){RSMSG={t:'Could not reach the server.',ok:false};RSUN=null;return{}}}
function rosBtn(){const b=$('rbtn');if(b)b.classList.toggle('cur',!!window.ROSV)}
document.addEventListener('click',e=>{if(window.ROSV&&e.target.closest&&e.target.closest('#modes .mb'))rosOff()});   /* picking a mode leaves the roster */
async function rosToggle(){window.ROSV=!window.ROSV;document.body.classList.toggle('rosv',window.ROSV);rosBtn();
 if(window.ROSV){await rsApi('get');RSMSG=null;rosDraw()}poll()}
function rosOff(){window.ROSV=false;document.body.classList.remove('rosv');rosBtn();poll()}
function rsParse(t){let L=String(t||'').replace(/\r/g,'').split('\n');
 if(L.filter(x=>x.trim()).length==1&&(L.join('').match(/[,;]/g)||[]).length>=2)L=L.join(' ').split(/[,;]/);else L=L.flatMap(x=>x.split(';'));   /* one line with several names; a single comma stays as 'Last, First' */
 const seen=new Set(),out=[];
 for(let x of L){if(x.includes('\t'))x=(x.split('\t').find(c=>/[A-Za-z\u00C0-\u024F]/.test(c))||'');
  x=x.replace(/^\s*(?:\d+\s*[.)\-:]\s*|[\u2022*\u00B7\-\u2013]\s+)/,'').replace(/\s+/g,' ').trim();
  if(!x||/^(no\.?|name|names|student|students|#)$/i.test(x))continue;
  const k=x.toLowerCase();if(seen.has(k))continue;seen.add(k);out.push(x.slice(0,60))}
 return out}
function rosList(){const el=$('rsl');if(!el)return;const L=(RSD||{})[RSS]||[],q=RSQ.trim().toLowerCase();
 const rows=L.map((n,i)=>[n,i]).filter(x=>!q||x[0].toLowerCase().includes(q));
 el.innerHTML=rows.length?'<div class="rs-grid">'+rows.map(x=>'<div class="rs-st"><span class="rs-no">'+(x[1]+1)+'</span><span class="rs-nm">'+esc(x[0])+'</span><button class="rs-x" data-n="'+esc(x[0])+'" title="Remove this student">\u2715</button></div>').join('')+'</div>'
  :'<p class="mute">'+(L.length?'No student matches that search.':'No students yet. Add one above or paste a class list.')+'</p>';
 el.querySelectorAll('.rs-x').forEach(b=>b.onclick=async()=>{await rsApi('del',{sec:RSS,name:b.dataset.n});rosDraw();poll()})}
function rosMsg(){const el=$('rsmsg');if(!el)return;if(!RSMSG){el.innerHTML='';return}
 el.innerHTML='<div class="rs-msg '+(RSMSG.ok?'ok':'bad')+'">'+esc(RSMSG.t)+(RSUN?'<button id="rsundo">\u21A9 Undo</button>':'')+'</div>';
 if(RSUN)$('rsundo').onclick=async()=>{const u=RSUN;await rsApi('add',{sec:u.sec,name:u.name,at:u.at});rosDraw();poll()}}
function rosPv(){const el=$('rspv'),b=$('rspaste');if(!el)return;const names=rsParse($('rsta').value),L=(RSD||{})[RSS]||[],have=new Set(L.map(x=>x.toLowerCase())),
 rep=document.querySelector('input[name=rsm]:checked').value=='replace',dup=names.filter(n=>have.has(n.toLowerCase())).length;
 b.disabled=!names.length;
 el.innerHTML=!names.length?'Nothing pasted yet.':rep?'<b>'+names.length+'</b> names found. The list will become exactly these ('+L.length+' now).'
  :'<b>'+names.length+'</b> names found'+(dup?': '+(names.length-dup)+' new, '+dup+' already in the list (skipped).':', all new.')}
function rosDraw(){const box=$('rostv');if(!box||!st)return;const R=RSD||{},ks=Object.keys(R);
 if(!ks.includes(RSS))RSS=ks.includes(st.roster.section)?st.roster.section:(ks[0]||'');
 const L=R[RSS]||[];
 box.innerHTML='<div class="rs"><div class="rs-c"><h3>\uD83D\uDC65 Sections</h3><div class="rs-sl">'
  +ks.map(k=>'<button class="rs-s'+(k==RSS?' on':'')+'" data-k="'+esc(k)+'"><span>'+esc(k)+'</span><b>'+R[k].length+'</b></button>').join('')+'</div>'
  +'<div class="rs-new rs-nsec"><input id="rsns" maxlength="60" placeholder="New section, e.g. Grade 7 \u2013 Luna" autocomplete="off"><button class="p" id="rsna">\uFF0B Add</button></div></div>'
  +'<div><div class="rs-c rs-hd"><div><h2>'+esc(RSS)+'</h2><span class="mute">'+L.length+' student'+(L.length==1?'':'s')+'</span></div>'
  +'<div class="rs-hb"><button id="rsren">\u270F Rename</button><button class="rsd" id="rsdel">\uD83D\uDDD1 Remove section</button></div></div>'
  +'<div id="rsmsg"></div><div class="rs-cols">'
  +'<div class="rs-c"><h3>Students</h3><div class="rs-new"><input id="rsnm" maxlength="60" placeholder="Add one student: full name" autocomplete="off"><button class="p" id="rsadd">\uFF0B Add</button></div>'
  +'<div class="rs-new"><input id="rsq" type="search" placeholder="Find a student" autocomplete="off" value="'+esc(RSQ)+'"><button id="rssort" title="Sort this list A to Z">A\u2192Z</button></div><div id="rsl"></div></div>'
  +'<div class="rs-c"><h3>Paste a class list</h3><p class="mute">One name per line, for example a column copied from Excel or Word. Numbers and bullets at the start of a line are ignored.</p>'
  +'<textarea id="rsta" rows="10" placeholder="Juan Dela Cruz&#10;Maria Santos&#10;..." spellcheck="false"></textarea>'
  +'<div class="rs-mode"><label><input type="radio" name="rsm" value="add" checked> Add to this list</label><label><input type="radio" name="rsm" value="replace"> Replace the whole list</label></div>'
  +'<div id="rspv" class="mute" style="margin-bottom:10px"></div><button class="p" id="rspaste" disabled>\uD83D\uDCCB Import names</button></div></div></div></div>';
 box.querySelectorAll('.rs-s').forEach(b=>b.onclick=()=>{RSS=b.dataset.k;RSQ='';RSMSG=null;RSUN=null;rosDraw()});
 const go=async(a,d)=>{await rsApi(a,Object.assign({sec:RSS},d||{}));rosDraw();poll()};
 $('rsna').onclick=async()=>{await rsApi('addsec',{name:$('rsns').value});rosDraw();poll()};
 $('rsns').onkeydown=e=>{if(e.key=='Enter')$('rsna').click()};
 $('rsnm').onkeydown=e=>{if(e.key=='Enter')$('rsadd').click()};
 $('rsadd').onclick=async()=>{await rsApi('add',{sec:RSS,name:$('rsnm').value});rosDraw();poll();$('rsnm').focus()};
 $('rsq').oninput=e=>{RSQ=e.target.value;rosList()};
 $('rssort').onclick=()=>go('sort');
 $('rsren').onclick=async()=>{const n=prompt('New name for the section "'+RSS+'":',RSS);if(n==null)return;await go('rensec',{name:n})};
 $('rsdel').onclick=async()=>{if(!confirm('Remove the section "'+RSS+'" ('+L.length+' student'+(L.length==1?'':'s')+') from the class list?\n\nTheir saved scores and test results are kept in the data file and come back if you add the same section and names again.'))return;await go('delsec')};
 const ta=$('rsta');ta.oninput=rosPv;document.querySelectorAll('input[name=rsm]').forEach(x=>x.onchange=rosPv);
 $('rspaste').onclick=async()=>{const names=rsParse(ta.value),rep=document.querySelector('input[name=rsm]:checked').value=='replace';if(!names.length)return;
  if(rep&&!confirm('Replace the whole list of "'+RSS+'" ('+L.length+' now) with these '+names.length+' names?\n\nStudents who are not in the new list leave the class list; their saved results are kept.'))return;
  await rsApi('paste',{sec:RSS,names:names,mode:rep?'replace':'add'});rosDraw();poll()};
 rosList();rosPv();rosMsg()}
poll();setInterval(poll,1000);</script></body></html>"""

if not SPEED_WEIGHTED: HOST = HOST.replace(' (a faster answer hits harder)', '')

LOGIN = """<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Teacher login</title>
<style>:root{--ink:#1e1b3a;--mute:#6f6a94;--card:#fff;--line:#e4defa;--grad:linear-gradient(135deg,#7c3aed,#ec4899)}
@media(prefers-color-scheme:dark){:root{--ink:#f5f3ff;--mute:#a9a4d6;--card:#1d1942;--line:#352f69}}
*{box-sizing:border-box}html,body{min-height:100vh;margin:0}
body{display:grid;place-items:center;padding:20px;font-family:Inter,"Segoe UI",system-ui,-apple-system,sans-serif;color:var(--ink);background:radial-gradient(circle at 0% 0%,rgba(236,72,153,.25),transparent 40%),radial-gradient(circle at 100% 0%,rgba(6,182,212,.25),transparent 42%),radial-gradient(circle at 50% 100%,rgba(124,58,237,.25),transparent 50%),#f6f3ff}
@media(prefers-color-scheme:dark){body{background-color:#120f2b}}
.card{width:100%;max-width:min(760px,94vw);text-align:center;padding:clamp(32px,6vh,64px) clamp(26px,5vw,64px);border-radius:40px;background:var(--card);border:1px solid var(--line);box-shadow:0 20px 56px rgba(124,58,237,.22)}
.logo{width:clamp(100px,17vh,150px);height:clamp(100px,17vh,150px);margin:0 auto 22px;border-radius:38px;background:var(--grad);display:grid;place-items:center;font-size:clamp(52px,9vh,80px);box-shadow:0 12px 28px rgba(236,72,153,.4)}
h1{margin:0;font-size:clamp(40px,7.5vh,68px);font-weight:800;letter-spacing:-.02em;background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
p.sub{margin:10px 0 clamp(26px,5vh,44px);color:var(--mute);font-size:clamp(18px,3vh,28px)}
input{width:100%;padding:clamp(18px,3vh,30px) 20px;font-size:clamp(24px,4vh,38px);text-align:center;letter-spacing:.2em;border-radius:22px;border:2px solid var(--line);background:var(--card);color:var(--ink)}
input:focus{outline:0;border-color:#7c3aed;box-shadow:0 0 0 4px rgba(124,58,237,.18)}
#msg{min-height:30px;margin:18px 0 8px;color:#dc2626;font-weight:600;font-size:clamp(16px,2.6vh,22px)}
button{width:100%;padding:clamp(18px,3.2vh,30px);font-size:clamp(22px,3.8vh,34px);font-weight:700;color:#fff;border:0;border-radius:22px;cursor:pointer;background:var(--grad);box-shadow:0 8px 22px rgba(236,72,153,.4)}
button:disabled{opacity:.6;cursor:wait}</style></head>
<body><div class="card"><div class="logo">🔒</div><h1>Teacher login</h1><p class="sub">Enter your PIN to open the host dashboard</p>
<input id="pin" type="password" autocomplete="current-password" placeholder="PIN" autofocus><p id="msg"></p><button id="go">Unlock</button></div>
<script>const $=i=>document.getElementById(i);let busy=false;
try{const k=sessionStorage.mk;if(k)fetch('/api/check?key='+encodeURIComponent(k)).then(r=>r.json()).then(j=>{if(j.ok)location.replace('/host?key='+encodeURIComponent(k))}).catch(()=>{})}catch(e){}
async function go(){if(busy)return;const pin=$('pin').value;if(!pin)return;busy=true;$('go').disabled=true;
 try{const j=await (await fetch('/api/login',{method:'POST',body:JSON.stringify({pin})})).json();
  if(j.ok){try{sessionStorage.mk=j.key}catch(e){}location.replace('/host?key='+encodeURIComponent(j.key));return}
  $('msg').textContent=j.wait?'Too many wrong tries. Wait '+j.wait+' seconds.':'Wrong PIN'+(j.left?' ('+j.left+' tries left)':'');$('pin').value='';$('pin').focus()
 }catch(e){$('msg').textContent='Cannot reach the server.'}
 busy=false;$('go').disabled=false}
$('go').onclick=go;$('pin').onkeydown=e=>{if(e.key=='Enter')go()};</script></body></html>"""

T_CSS = r"""<style>:root{--ink:#1e1b3a;--mute:#6f6a94;--card:#fff;--line:#e4defa;--grad:linear-gradient(135deg,#7c3aed,#ec4899);--bg:#f6f3ff;--ok:#16a34a;--no:#dc2626}
@media(prefers-color-scheme:dark){:root{--ink:#f5f3ff;--mute:#a9a4d6;--card:#1d1942;--line:#352f69;--bg:#120f2b}}
*{box-sizing:border-box}body{margin:0;min-height:100vh;font-family:Inter,"Segoe UI",system-ui,sans-serif;color:var(--ink);background:var(--bg);padding:16px}
.card{max-width:760px;margin:0 auto 14px;background:var(--card);border:1px solid var(--line);border-radius:22px;padding:22px;box-shadow:0 10px 30px rgba(124,58,237,.12)}
h1,h2{margin:0 0 8px}h1{background:var(--grad);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.mute{color:var(--mute)}select,input{width:100%;padding:12px;font-size:18px;border-radius:14px;border:2px solid var(--line);background:var(--card);color:var(--ink);margin:6px 0 12px}
button{padding:12px 18px;font-size:16px;font-weight:700;border:0;border-radius:14px;cursor:pointer;background:var(--line);color:var(--ink)}button.p{background:var(--grad);color:#fff}button:disabled{opacity:.5}
.row{display:flex;gap:8px;flex-wrap:wrap;align-items:center}.q{font-size:clamp(24px,6vw,40px);font-weight:800;margin:18px 0;word-break:break-word}
.dots{display:flex;flex-wrap:wrap;gap:5px;margin:10px 0}.dots i{width:14px;height:14px;border-radius:50%;background:var(--line);cursor:pointer}.dots i.a{background:#a78bfa}.dots i.c{outline:3px solid #ec4899}
table{border-collapse:collapse;width:100%;font-size:14px}td,th{border-bottom:1px solid var(--line);padding:6px 8px;text-align:center}td:first-child,th:first-child{text-align:left}
.chip{display:inline-block;padding:6px 14px;border-radius:12px;background:rgba(124,58,237,.12);margin:3px;text-align:center}.pos{color:var(--ok);font-weight:700}.neg{color:var(--no);font-weight:700}</style>"""

T_STUDENT = r"""<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Numeracy Test</title>""" + T_CSS + r"""<style>
/* ===== student test: big, bright, friendly ===== */
:root{--a:#7c3aed;--b:#ec4899;--c:#06b6d4;--d:#f59e0b;--e:#10b981;--card:#fff;--ink:#1e1b3a;--mute:#6f6a94;--line:#e4defa}
@media(prefers-color-scheme:dark){:root{--card:#1d1942;--ink:#f5f3ff;--mute:#b3aee0;--line:#3a3478}}
html{-webkit-text-size-adjust:100%}
body{padding:0;min-height:100vh;min-height:100dvh;font-family:ui-rounded,"Nunito","Baloo 2","Trebuchet MS","Segoe UI",system-ui,sans-serif;background:#f6f3ff;overflow-x:hidden}
@media(prefers-color-scheme:dark){body{background:#120f2b}}
body::before{content:"";position:fixed;inset:-20%;z-index:-1;pointer-events:none;filter:blur(80px);opacity:.6;animation:drift 22s ease-in-out infinite alternate;background:radial-gradient(circle at 12% 18%,var(--b) 0,transparent 30%),radial-gradient(circle at 88% 12%,var(--c) 0,transparent 30%),radial-gradient(circle at 75% 88%,var(--a) 0,transparent 36%),radial-gradient(circle at 18% 85%,var(--d) 0,transparent 24%)}
@keyframes drift{to{transform:translate(4%,-3%) rotate(8deg) scale(1.12)}}
#app{width:100%;max-width:none;margin:0 auto;padding:clamp(8px,1.2vw,18px) clamp(8px,1.6vw,24px);display:flex;flex-direction:column;gap:clamp(8px,1.2vw,14px);height:100vh;height:100dvh;box-sizing:border-box}
.stage{flex:1;min-height:0;display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:clamp(10px,1.6vw,24px);align-items:stretch}
.mid{min-width:0;min-height:0;display:flex;flex-direction:column;gap:clamp(8px,1.2vw,14px)}
.mid .qcard{min-height:0;overflow:auto}
@media(max-width:900px){#app{height:auto;min-height:100dvh}.stage{grid-template-columns:1fr}.mid{order:1}.nums.L{order:2}.nums.R{order:3}}
.pop{animation:pop .35s ease both}@keyframes pop{from{opacity:0;transform:translateY(14px) scale(.98)}}
.bar{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:clamp(10px,2vw,18px);padding:clamp(10px,1.6vw,16px) clamp(14px,2.4vw,26px);border-radius:28px;color:#fff;background:linear-gradient(135deg,var(--a),var(--b));box-shadow:0 10px 30px rgba(124,58,237,.35)}
.av{flex:none;width:clamp(48px,8vw,72px);height:clamp(48px,8vw,72px);border-radius:50%;display:grid;place-items:center;font-size:clamp(20px,3.4vw,30px);font-weight:900;background:rgba(255,255,255,.25);border:3px solid #fff}
.who{min-width:0;text-align:center}.who b{display:block;font-size:clamp(22px,3.6vw,44px);line-height:1.1;overflow-wrap:anywhere}.who span{font-size:clamp(13px,1.8vw,20px);opacity:.95}.bar .av{justify-self:start}.bar .pill{justify-self:end}
.pill{flex:none;padding:8px 18px;border-radius:99px;background:rgba(255,255,255,.22);font-weight:900;font-size:clamp(14px,2.2vw,20px);white-space:nowrap}
.prog{height:clamp(14px,2.2vw,20px);border-radius:99px;background:rgba(124,58,237,.16);overflow:hidden;border:2px solid #fff}
.prog i{display:block;height:100%;border-radius:99px;background:linear-gradient(90deg,var(--c),var(--e),var(--d));transition:width .4s}
.note{padding:clamp(10px,1.6vw,16px) clamp(14px,2.4vw,24px);border-radius:22px;background:var(--card);border:2px dashed var(--line);font-size:clamp(14px,2.2vw,19px);line-height:1.4;color:var(--ink)}
.qcard{--g1:var(--a);--g2:var(--b);flex:1;display:flex;flex-direction:column;justify-content:center;text-align:center;position:relative;overflow:hidden;padding:clamp(18px,4vw,52px);border-radius:36px;background:var(--card);border:4px solid transparent;background-clip:padding-box;box-shadow:0 18px 56px rgba(124,58,237,.22),0 0 0 4px color-mix(in srgb,var(--g1) 45%,transparent)}
.qcard::before{content:"";position:absolute;left:0;right:0;top:0;height:14px;background:linear-gradient(90deg,var(--g1),var(--g2))}
.qcard.c1{--g1:#06b6d4;--g2:#3b82f6}.qcard.c2{--g1:#f59e0b;--g2:#ef4444}.qcard.c3{--g1:#10b981;--g2:#84cc16}.qcard.c4{--g1:#ec4899;--g2:#a855f7}
.qn{display:inline-block;align-self:center;margin:6px 0 4px;padding:6px 22px;border-radius:99px;font-weight:900;font-size:clamp(14px,2.4vw,22px);color:#fff;background:linear-gradient(135deg,var(--g1),var(--g2));box-shadow:0 6px 16px rgba(0,0,0,.2)}
.q{margin:.3em 0 .5em;font-size:clamp(48px,min(14vw,24vh),230px);line-height:1.12;font-weight:900;letter-spacing:-.01em;color:var(--ink);overflow-wrap:anywhere}
.q.long{font-size:clamp(32px,min(6.8vw,11vh),100px);line-height:1.25}
.q sup{font-size:.6em}
input#a{width:100%;max-width:1000px;align-self:center;margin:6px auto 4px;padding:clamp(14px,2.4vw,26px) 20px;font-family:inherit;font-weight:900;text-align:center;font-size:clamp(34px,min(8vw,11vh),100px);border-radius:28px;border:5px solid var(--line);background:var(--card);color:var(--ink);transition:border-color .15s,box-shadow .15s}
input#a:focus{outline:0;border-color:var(--g1);box-shadow:0 0 0 8px color-mix(in srgb,var(--g1) 22%,transparent)}
input#a::placeholder{font-size:.42em;font-weight:700;color:var(--mute)}
.hint{margin-top:8px;font-size:clamp(13px,2vw,18px);color:var(--mute)}
.cheer{min-height:1.6em;margin-top:6px;font-weight:900;font-size:clamp(16px,2.6vw,26px);color:var(--e)}
.nav{display:flex;gap:clamp(10px,2vw,20px)}
.nav button{flex:1;padding:clamp(16px,3vw,28px);font-family:inherit;font-weight:900;font-size:clamp(20px,4vw,36px);border:0;border-radius:26px;cursor:pointer;transition:transform .12s,filter .15s;touch-action:manipulation}
.nav button:active{transform:scale(.97)}.nav button:hover{filter:brightness(1.08)}
.nav .bk{flex:.6;color:var(--a);background:var(--card);border:3px solid var(--line)}
.nav .nx{color:#fff;background:linear-gradient(135deg,var(--a),var(--b));box-shadow:0 12px 28px rgba(236,72,153,.45)}
.nav .sb{color:#fff;background:linear-gradient(135deg,#10b981,#06b6d4);box-shadow:0 12px 28px rgba(16,185,129,.45);animation:pulse 2s ease-in-out infinite}
.nav button:disabled{opacity:.4;cursor:not-allowed;box-shadow:none;animation:none}
@keyframes pulse{50%{transform:scale(1.03)}}
.nums{--t:clamp(46px,min(5.6vw,9.6vh),88px);display:grid;grid-template-columns:repeat(2,var(--t));grid-auto-rows:var(--t);gap:clamp(6px,.9vw,12px);align-content:center;padding:clamp(8px,1.2vw,16px);border-radius:26px;background:var(--card);border:2px solid var(--line);box-shadow:0 10px 28px rgba(124,58,237,.14)}
.nums button{width:100%;height:100%;padding:0;border-radius:18px;font-family:inherit;font-weight:900;font-size:clamp(17px,min(2.2vw,3.4vh),30px);border:3px solid var(--line);background:var(--card);color:var(--mute);cursor:pointer;transition:transform .12s}
.nums button:hover{transform:scale(1.07)}
.nums button.a{background:linear-gradient(135deg,#10b981,#06b6d4);color:#fff;border-color:transparent}
.nums button.cu{outline:5px solid var(--b);outline-offset:2px;transform:scale(1.08)}
@media(max-width:900px){.nums{display:flex;flex-wrap:wrap;justify-content:center;--t:44px}.nums button{width:44px;height:44px}}
.big{padding:clamp(24px,5vw,60px);border-radius:36px;background:var(--card);text-align:center;box-shadow:0 18px 56px rgba(124,58,237,.22);border:2px solid var(--line)}
.big .em{font-size:clamp(70px,16vw,160px);line-height:1;animation:float 3s ease-in-out infinite}@keyframes float{50%{transform:translateY(-8px)}}
.big h1{margin:.2em 0 .1em;font-size:clamp(34px,7vw,68px);font-weight:900;background:linear-gradient(135deg,var(--a),var(--b));-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.big p{font-size:clamp(16px,2.8vw,26px);color:var(--mute);margin:.4em 0}
.big label{display:block;text-align:left;margin:16px 6px 6px;font-weight:900;font-size:clamp(13px,2vw,17px);letter-spacing:.08em;text-transform:uppercase;color:var(--mute)}
.big select{width:100%;padding:clamp(14px,2.6vw,24px) 20px;font-family:inherit;font-weight:800;font-size:clamp(20px,3.6vw,32px);border-radius:22px;border:4px solid var(--line);background:var(--card);color:var(--ink);margin:0}
.big select:focus{outline:0;border-color:var(--a);box-shadow:0 0 0 8px rgba(124,58,237,.18)}
.big .go{width:100%;margin-top:22px;padding:clamp(16px,3vw,28px);font-family:inherit;font-weight:900;font-size:clamp(22px,4.4vw,38px);border:0;border-radius:26px;color:#fff;cursor:pointer;background:linear-gradient(135deg,var(--a),var(--b));box-shadow:0 12px 28px rgba(236,72,153,.45)}
.err{min-height:1.4em;margin-top:10px;color:var(--no);font-weight:800;font-size:clamp(14px,2.2vw,20px)}
.dots3::after{content:"";animation:dt 1.4s steps(1) infinite}@keyframes dt{0%{content:""}25%{content:"."}50%{content:".."}75%{content:"..."}}
.score{display:flex;flex-wrap:wrap;gap:12px;justify-content:center;margin:14px 0}
.score div{min-width:140px;padding:14px 22px;border-radius:24px;color:#fff;background:linear-gradient(135deg,var(--a),var(--b))}.score div:nth-child(2){background:linear-gradient(135deg,#06b6d4,#10b981)}
.score b{display:block;font-size:clamp(34px,7vw,64px);line-height:1.1}.score small{font-weight:800;letter-spacing:.06em;text-transform:uppercase}
.tt{width:100%;border-collapse:separate;border-spacing:0 8px;font-size:clamp(15px,2.4vw,22px)}.tt td,.tt th{padding:10px 14px;border:0;text-align:center;background:rgba(124,58,237,.08)}.tt td:first-child,.tt th:first-child{text-align:left;border-radius:16px 0 0 16px;font-weight:800}.tt td:last-child,.tt th:last-child{border-radius:0 16px 16px 0}
.mod{position:fixed;inset:0;z-index:50;display:grid;place-items:center;padding:16px;background:rgba(20,10,60,.7)}
.mod .box{max-width:560px;width:100%;text-align:center;padding:clamp(22px,4vw,40px);border-radius:30px;background:var(--card);color:var(--ink);box-shadow:0 20px 70px rgba(0,0,0,.4)}
.mod h2{margin:0 0 8px;font-size:clamp(26px,5vw,40px)}.mod p{font-size:clamp(16px,2.6vw,22px);color:var(--mute);margin:6px 0 18px}
.mod .row{display:flex;gap:12px}.mod button{flex:1;padding:16px;font-family:inherit;font-weight:900;font-size:clamp(17px,3vw,24px);border:0;border-radius:20px;cursor:pointer;background:var(--line);color:var(--ink)}.mod button.p{color:#fff;background:linear-gradient(135deg,#10b981,#06b6d4)}
.cf{position:fixed;top:-8vh;z-index:60;pointer-events:none;animation:fall 2.6s ease-in forwards}@keyframes fall{to{transform:translateY(112vh) rotate(540deg)}}
@media(prefers-reduced-motion:reduce){body::before,.big .em,.nav .sb{animation:none}}
.rep{width:100%;max-width:1200px;margin:0 auto;display:flex;flex-direction:column;gap:clamp(12px,2vw,22px)}
.rcard{padding:clamp(16px,3vw,32px);border-radius:30px;background:var(--card);border:3px solid var(--line);box-shadow:0 14px 40px rgba(124,58,237,.16)}
.rcard h2{margin:0 0 10px;font-size:clamp(22px,3.6vw,38px);font-weight:900}
.rcard.g{border-color:#10b981;background:linear-gradient(135deg,rgba(16,185,129,.14),var(--card) 60%)}.rcard.r{border-color:#ef4444;background:linear-gradient(135deg,rgba(239,68,68,.12),var(--card) 60%)}.rcard.y{border-color:#f59e0b;background:linear-gradient(135deg,rgba(245,158,11,.14),var(--card) 60%)}.rcard.v{border-color:var(--a)}
.rc{display:inline-block;margin:4px 6px 4px 0;padding:8px 18px;border-radius:99px;font-weight:800;font-size:clamp(15px,2.4vw,22px);color:#fff}.rc.g{background:linear-gradient(135deg,#10b981,#06b6d4)}.rc.r{background:linear-gradient(135deg,#ef4444,#f97316)}.rc.y{background:linear-gradient(135deg,#f59e0b,#eab308)}
.rrow{display:grid;grid-template-columns:minmax(120px,1.2fr) 3fr auto;gap:12px;align-items:center;margin:10px 0;font-size:clamp(15px,2.4vw,22px);font-weight:800}
.rbar{height:clamp(16px,2.4vw,24px);border-radius:99px;background:rgba(124,58,237,.14);overflow:hidden}.rbar i{display:block;height:100%;border-radius:99px}
.rrow small{display:block;font-weight:600;color:var(--mute);font-size:.7em}
.rtip{margin:8px 0;padding:12px 16px;border-radius:18px;background:rgba(124,58,237,.08);font-size:clamp(15px,2.3vw,21px);line-height:1.4}.rtip b{color:var(--a)}
.rbtn{padding:clamp(14px,2.4vw,22px) 28px;font-family:inherit;font-weight:900;font-size:clamp(18px,3vw,28px);border:0;border-radius:22px;cursor:pointer;color:#fff;background:linear-gradient(135deg,var(--a),var(--b));box-shadow:0 10px 24px rgba(236,72,153,.4)}
@media print{body{background:#fff!important}body::before,.noprint{display:none!important}#app{height:auto!important;max-width:none}.rcard,.bar{box-shadow:none!important;break-inside:avoid}.bar{-webkit-print-color-adjust:exact;print-color-adjust:exact}.rc,.rbar i,.score div{-webkit-print-color-adjust:exact;print-color-adjust:exact}}
</style></head><body><div id="app"></div>
<script>
const $=i=>document.getElementById(i),esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const mx=s=>esc(s).replace(/\^(\d+)/g,'<sup>$1</sup>').replace(/sqrt\(/g,'√(');
let cid=localStorage.tcid||(localStorage.tcid=Math.random().toString(36).slice(2)+Date.now().toString(36)),sec=localStorage.tsec||'',nm=localStorage.tnm||'',V=null,cur=0,ans={},ROSTER=null,stageKey='';
const API=async(p,d)=>{try{return await (await fetch(p,d?{method:'POST',body:JSON.stringify(d)}:{})).json()}catch(e){return null}};
const CH=['Nice one! 🌟','Great! Keep going 💪','Awesome! 🚀','You got this! 🔥','Super! ⭐','Way to go! 🎉'];
function boom(){const E=['🎉','⭐','✨','🎊','💜','🌟'];for(let i=0;i<40;i++){const e=document.createElement('span');e.className='cf';e.textContent=E[i%E.length];e.style.left=Math.random()*100+'vw';e.style.animationDelay=Math.random()*.6+'s';e.style.fontSize=(20+Math.random()*28)+'px';document.body.appendChild(e);setTimeout(()=>e.remove(),3400)}}
const TEM={'Basic Operations':'🔢','Integers':'➕','Fractions':'🍕','Word Problem':'📖','Algebra':'🧮','Percent & Ratio':'💯','Geometry & Data':'📐'};
const TTIP={'Basic Operations':'Practise your times tables, and check each answer by doing the opposite operation.','Integers':'Draw a number line. Same signs: add and keep the sign. Different signs: subtract and use the sign of the bigger number.','Fractions':'Find a common denominator first, then add or subtract the tops. Always simplify at the end.','Word Problem':'Underline the numbers and the question. Decide the operation before you calculate.','Algebra':'Do the same step to both sides. Undo + and − first, then × and ÷.','Percent & Ratio':'Percent means "per 100". Change it to a fraction first, then multiply.','Geometry & Data':'Write the formula first, then put in the numbers. Draw a quick sketch.'};
const SKL=[['add','Addition','➕'],['sub','Subtraction','➖'],['mul','Multiplication','✖️'],['div','Division','➗']];
const SKTIPS={add:'Line up the digits by place value. Add from the right and carry when you reach 10 or more. Check by adding in a different order.',sub:'Line up the digits and borrow when the top digit is smaller. Check by adding your answer to the number you took away.',mul:'Learn your times tables, then break big numbers into tens and ones. Estimate first to check your answer.',div:'Ask: what times the divisor gives this number? Check by multiplying your answer by the divisor.'};
const skcol=p=>p>=75?'linear-gradient(90deg,#10b981,#06b6d4)':p>=50?'linear-gradient(90deg,#f59e0b,#eab308)':'linear-gradient(90deg,#ef4444,#f97316)';
const skchip=(a,c)=>a.map(x=>'<span class="rc '+c+'">'+x.e+' '+x.n+' · '+x.p+'% <small>('+x.c+'/'+x.t+')</small></span>').join('');
const skh='<h2 style="margin-top:14px;font-size:clamp(18px,2.8vw,28px)">🧮 By skill</h2>',skno='<span style="color:var(--mute);font-weight:700">None this time</span>';
function skdata(L){const sk=L.sk||{},o={L:[]};SKL.forEach(s=>{const v=sk[s[0]];if(v&&v[1])o.L.push({k:s[0],n:s[1],e:s[2],c:v[0],t:v[1],p:Math.round(100*v[0]/v[1]),dr:(L.drill||{})[s[0]]})});
 o.S=o.L.filter(x=>x.p>=75);o.W=o.L.filter(x=>x.p<50);o.M=o.L.filter(x=>x.p>=50&&x.p<75);o.err=L.skerr||{};
 o.steps=o.L.filter(x=>x.p<75).sort((a,b)=>a.p-b.p).map(x=>'<div class="rtip"><b>'+x.e+' '+x.n+'</b> · '+SKTIPS[x.k]+'</div>').join('');return o}
function skS(K){return K.L.length?skh+(K.S.length?skchip(K.S,'g'):skno):''}
function skN(K){return K.L.length?skh+(K.W.length?skchip(K.W,'r'):'')+(K.M.length?'<br>'+skchip(K.M,'y'):'')+(K.W.length||K.M.length?'':skno):''}
function skCard(K){if(!K.L.length)return '';return '<div class="rcard v"><h2>🧮 My operation skills</h2>'+K.L.map(x=>'<div class="rrow"><div>'+x.e+' '+x.n+(x.dr&&x.dr[1]?'<small>Practice so far: '+x.dr[0]+'/'+x.dr[1]+' ('+Math.round(100*x.dr[0]/x.dr[1])+'%)</small>':'')+'</div><div class="rbar"><i style="width:'+Math.max(x.p,2)+'%;background:'+skcol(x.p)+'"></i></div><div>'+x.c+'/'+x.t+'</div></div>').join('')+'<p style="margin:8px 0 0;color:var(--mute)">Only the test questions that were one plain operation are counted here.</p></div>'}
function skMerge(E,K){SKL.forEach(s=>{const t=K.err[s[0]]||{};Object.keys(t).forEach(k=>{const e=E[k];if(e&&e.t.indexOf(s[1])<0)e.t.push(s[1])})})}
function skSW(L){const K=skdata(L);return K.L.length?'<br><b>🧮 By skill</b><br>'+K.L.map(x=>skchip([x],x.p>=75?'g':x.p>=50?'y':'r')).join(''):''}
function skComp(A,B){const f=(L,k)=>{const v=L.sk&&L.sk[k];return v&&v[1]?Math.round(100*v[0]/v[1]):null},rows=SKL.filter(s=>f(A,s[0])!=null||f(B,s[0])!=null);if(!rows.length)return '';
 return '<div class="rcard v"><h2>🧮 Operation skills: Pre-test vs Post-test</h2>'+rows.map(s=>{const a=f(A,s[0]),b=f(B,s[0]),c=a!=null&&b!=null?b-a:null;return '<div class="rrow2"><div>'+s[2]+' '+s[1]+'</div><div><div class="rbar" style="margin-bottom:4px"><i style="width:'+Math.max(a||0,2)+'%;background:'+skcol(a||0)+';opacity:.55"></i></div><div class="rbar"><i style="width:'+Math.max(b||0,2)+'%;background:'+skcol(b||0)+'"></i></div></div><div style="text-align:right">'+(a==null?'–':a+'%')+' → <b>'+(b==null?'–':b+'%')+'</b>'+(c==null?'':'<br><span style="color:'+(c>=0?'#059669':'#dc2626')+'">'+(c>=0?'+':'')+c+'</span>')+'</div></div>'}).join('')+'<p style="color:var(--mute);margin:8px 0 0">Faded bar = pre-test, solid bar = post-test. Each skill has only a few test questions, so read it as a guide.</p></div>'}
const ETIP={sign:['➖','Sign mistakes','Your digits were right but the sign was opposite. Slow down on positive and negative numbers.'],slip:['🔍','Small slips','Some answers were off by just 1. Re-check your last step before you answer.'],place:['🔟','Place value','Some answers had the right digits but the wrong size. Check zeros and the decimal point.'],operation:['🔀','Wrong operation','Some answers matched a different operation. Re-read the question and decide which operation it asks for.'],format:['✏️','Answer format','Some answers were not numbers. Type numbers like 12, -5, 3/4 or 0.5.'],other:['🧩','Other mistakes','Compare each step of your working to find where it changed.'],blank:['⬜','Blank answers','Some questions were left blank. In practice, always try: a good guess is better than nothing.']};
function report(R){
 const ph=R.post?'post':'pre',L=R[ph],P=L.per,T=Object.keys(P),pc=t=>P[t][1]?Math.round(100*P[t][0]/P[t][1]):0;
 const S=T.filter(t=>pc(t)>=75),W=T.filter(t=>pc(t)<50),M=T.filter(t=>pc(t)>=50&&pc(t)<75);
 const chips=(a,c)=>a.length?a.map(t=>'<span class="rc '+c+'">'+(TEM[t]||'')+' '+esc(t)+' · '+pc(t)+'%</span>').join(''):'<span style="color:var(--mute);font-weight:700">None this time</span>';
 const E={};Object.keys(L.err||{}).forEach(t=>Object.keys(L.err[t]).forEach(k=>{const e=E[k]||(E[k]={n:0,t:[]});e.n+=L.err[t][k];if(e.t.indexOf(t)<0)e.t.push(t)}));
 const ek=Object.keys(E).filter(k=>ETIP[k]).sort((a,b)=>E[b].n-E[a].n).slice(0,4);
 const prac=T.filter(t=>pc(t)<75).sort((a,b)=>pc(a)-pc(b)).slice(0,3),K=skdata(L);skMerge(E,K);
 const col=p=>p>=75?'linear-gradient(90deg,#10b981,#06b6d4)':p>=50?'linear-gradient(90deg,#f59e0b,#eab308)':'linear-gradient(90deg,#ef4444,#f97316)';
 let h='<div class="rep pop"><div class="big" style="padding:clamp(18px,3vw,34px)"><div class="em" style="font-size:clamp(50px,9vw,90px)">📋</div><h1>My Personal Report</h1><p>'+(R.post?'After your post-test':'After your pre-test')+' · '+esc(nm)+' · '+esc(sec)+'</p>';
 h+='<div class="score">'+Object.keys(R).map(x=>'<div><b>'+R[x].pct+'%</b><small>'+(x=='pre'?'Pre-test':'Post-test')+'</small></div>').join('')+'</div>';
 if(R.pre&&R.post)h+='<p><b>'+(R.post.pct>=R.pre.pct?'📈 You grew by '+(R.post.pct-R.pre.pct)+' points. Your practice is working!':'Your score dipped this time. Practise the topics below.')+'</b></p>';
 h+='</div>';
 h+='<div class="rcard g"><h2>💪 My strengths</h2>'+chips(S,'g')+'<p style="margin:8px 0 0;color:var(--mute)">Topics where you scored 75% or more. Keep it up!</p>'+skS(K)+'</div>';
 h+='<div class="rcard r"><h2>🎯 Needs more practice</h2>'+chips(W,'r')+(M.length?'<h2 style="margin-top:14px;font-size:clamp(18px,2.8vw,28px)">🌱 Getting there</h2>'+chips(M,'y'):'')+'<p style="margin:8px 0 0;color:var(--mute)">Red: below 50%. Yellow: 50% to 74%.</p>'+skN(K)+'</div>';
 h+='<div class="rcard v"><h2>📊 All topics</h2>'+T.map(t=>'<div class="rrow"><div>'+(TEM[t]||'')+' '+esc(t)+(R.pre&&R.post?'<small>Pre-test: '+(R.pre.per[t][1]?Math.round(100*R.pre.per[t][0]/R.pre.per[t][1]):0)+'%</small>':'')+'</div><div class="rbar"><i style="width:'+Math.max(pc(t)?pc(t):2,2)+'%;background:'+col(pc(t))+'"></i></div><div>'+P[t][0]+'/'+P[t][1]+'</div></div>').join('')+'</div>';
 h+=skCard(K);
 if(ek.length)h+='<div class="rcard y"><h2>🔎 Mistake patterns</h2>'+ek.map(k=>'<div class="rtip">'+ETIP[k][0]+' <b>'+ETIP[k][1]+'</b> ('+E[k].n+') · '+ETIP[k][2]+'<br><small style="color:var(--mute)">Seen in: '+E[k].t.map(esc).join(', ')+'</small></div>').join('')+'</div>';
 h+='<div class="rcard v"><h2>🚀 My next steps</h2>'+K.steps+(prac.length||K.steps?prac.map((t,i)=>'<div class="rtip"><b>'+(i+1)+'. '+(TEM[t]||'')+' '+esc(t)+'</b> · '+(TTIP[t]||'')+'</div>').join(''):'<div class="rtip">🏆 Excellent work! Challenge yourself with harder problems and help a classmate.</div>')+'</div>';
 h+='<div class="noprint" style="text-align:center;padding-bottom:20px"><button class="rbtn" onclick="window.print()">🖨 Print / Save as PDF</button> <button class="rbtn" onclick="dlMy()">⬇ Download PDF</button></div></div>';
 return h}
/*PDFJS*/
function dlMy(){const d=new Date();pdfSave('/api/pdf/student',{title:'My Numeracy Report',sub:nm+' · '+sec+' · '+d.toLocaleDateString(),cols:[],w:[],rows:pdfRows($('app'))},'my-numeracy-report-'+nm.replace(/[^A-Za-z0-9]+/g,'-')+'-'+d.toISOString().slice(0,10)+'.pdf')}
let BOOT=null,PA=null,PC=0,CL=false;
async function bootId(){try{return (await (await fetch('/api/t/boot')).json()).boot}catch(e){return null}}
function dropLogin(msg){PA=null;CL=false;sec=nm='';V=null;cur=0;ans={};stageKey='';try{localStorage.tsec=localStorage.tnm=''}catch(e){}join();if(msg&&$('m'))$('m').textContent=msg}
async function logout(){if(!confirm('Log out? Your saved answers are kept. You can log in again later.'))return;try{if(V&&V.items&&V.items.length&&V.phase&&!V.done){const it=V.items[cur];if(it&&ans[it.i]!=null)await API('/api/t/save',{sec,name:nm,cid,i:it.i,v:ans[it.i]||''})}}catch(e){}await API('/api/t/logout',{sec,name:nm,cid});dropLogin()}
async function boot(){const r=await fetch('/api/t/roster');ROSTER=await r.json();BOOT=await bootId();let old='';try{old=localStorage.tboot||''}catch(e){}try{if(BOOT)localStorage.tboot=BOOT}catch(e){}if(BOOT&&old!==BOOT){sec=nm='';try{localStorage.tsec=localStorage.tnm=''}catch(e){}}if(sec&&nm)await load();else join()}
function join(){const ss=Object.keys(ROSTER);
 $('app').innerHTML='<div class="big pop" style="margin:auto;width:100%"><div class="em">📝</div><h1>Numeracy Test</h1><p>Choose your section, then your name.</p><label for="s">Section</label><select id="s">'+ss.map(x=>'<option'+(x==sec?' selected':'')+'>'+esc(x)+'</option>').join('')+'</select><label for="n">Your name</label><select id="n"></select><button class="go" id="go">Join ▶</button><div class="err" id="m"></div></div>';
 const f=()=>{$('n').innerHTML=ROSTER[$('s').value].map(x=>'<option'+(x==nm?' selected':'')+'>'+esc(x)+'</option>').join('')};f();$('s').onchange=f;
 $('go').onclick=async()=>{sec=$('s').value;nm=$('n').value;const ok=await load();if(ok)try{localStorage.tsec=sec;localStorage.tnm=nm}catch(e){}}}
async function load(){const r=await API('/api/t/test?sec='+encodeURIComponent(sec)+'&name='+encodeURIComponent(nm)+'&cid='+cid);
 if(!r||r.err){if(r&&r.err=='claimed'&&$('m'))$('m').textContent='That name is already in use on another device.';else if($('m'))$('m').textContent='Cannot join. Check the Wi-Fi.';if(!$('m')){sec=nm='';try{localStorage.tsec=localStorage.tnm=''}catch(e){}join()}return false}
 if(V&&V.phase&&!V.done&&!r.phase)CL=true;if(r.phase)CL=false;if(!r.phase||r.paused)document.querySelectorAll('.mod').forEach(x=>x.remove());const k=r.stage+'|'+r.done+'|'+r.released+'|'+(r.paused?1:0)+'|'+(r.gen==null?'':r.gen);if(r.paused&&V&&!V.paused&&V.items&&V.items.length){PA=Object.assign({},ans);PC=cur}if(r.done)PA=null;if(!V||k!=stageKey||!V.items.length){V=r;ans=Object.assign({},r.ans);stageKey=k;cur=0;if(!r.paused&&!r.done&&PA){ans=Object.assign(ans,PA);cur=Math.min(PC,Math.max(0,r.items.length-1));PA=null}}else V.stage_txt=r.stage_txt;render();return true}
function pageHdr(v){const ini=nm.split(' ').filter(Boolean).slice(0,2).map(x=>x[0]).join('').toUpperCase();
 return '<div class="bar pop"><div class="av">'+esc(ini)+'</div><div class="who"><b>'+esc(nm)+'</b><span>'+esc(sec)+'</span></div><div style="justify-self:end;display:flex;align-items:center;gap:8px">'+(v?'<div class="pill">'+v+'</div>':'')+'<button type="button" onclick="logout()" title="Log out" aria-label="Log out" style="flex:none;background:rgba(255,255,255,.22);color:#fff;border:1px solid rgba(255,255,255,.55);border-radius:99px;padding:8px 16px;font:inherit;font-weight:900;font-size:clamp(13px,2vw,18px);cursor:pointer;white-space:nowrap">Log out</button></div></div>'}
function render(){const v=V;
 if(v.paused&&v.phase&&!v.done){document.querySelectorAll('.mod').forEach(x=>x.remove());$('app').innerHTML=pageHdr('')+'<div class="big pop" style="margin:auto;width:100%"><div class="em">⏸️</div><h1>Test paused</h1><p>Your teacher stopped your test for now. Put your pencil down and wait. This page will continue by itself<span class="dots3"></span></p></div>';return}
 if((!v.phase||v.done)&&v.released&&v.result&&Object.keys(v.result).length){$('app').innerHTML=pageHdr('')+report(v.result);window.scrollTo(0,0);return}
 if(!v.phase||v.done){let h=pageHdr('');
  h+='<div class="big pop" style="margin:auto;width:100%"><div class="em">'+(v.done?'🎉':'⏳')+'</div><h1>'+(v.done?'Test submitted!':esc(v.stage_txt))+'</h1><p>'+(v.done?'Great job! Your teacher will share the results.':(CL?'Your teacher closed the test. Your saved answers are kept. Please wait for your teacher.':'The test is not open yet. This page will start by itself<span class="dots3"></span>'))+'</p>';
  if(v.released&&v.result){const R=v.result;h+='<div class="score">'+Object.keys(R).map(ph=>'<div><b>'+R[ph].pct+'%</b><small>'+(ph=='pre'?'Pre-test':'Post-test')+'</small></div>').join('')+'</div>';
   const P=(R.pre||R.post).per;h+='<table class="tt"><tr><th>Topic</th>'+(R.pre?'<th>Pre</th>':'')+(R.post?'<th>Post</th>':'')+'</tr>'+Object.keys(P).map(t=>'<tr><td>'+esc(t)+'</td>'+['pre','post'].filter(x=>R[x]).map(x=>'<td>'+R[x].per[t][0]+'/'+R[x].per[t][1]+'</td>').join('')+'</tr>').join('')+'</table>';
   if(R.pre&&R.post)h+='<p><b>'+(R.post.pct>=R.pre.pct?'📈 You grew by '+(R.post.pct-R.pre.pct)+' points. Your practice is working!':'Your score dipped this time. Practise the topics above next.')+'</b></p>'}
  $('app').innerHTML=h+'</div>';return}
 const n=v.items.length,it=v.items[cur],done=Object.keys(ans).filter(i=>String(ans[i]).trim()).length,cc=cur%5;
 let h=pageHdr('Q '+(cur+1)+' / '+n);
 h+='<div class="prog pop"><i style="width:'+Math.round(100*done/n)+'%"></i></div>';
 if(cur==0)h+='<div class="note pop">'+(v.phase=='pre'?'👋 This pre-test is <b>not graded</b>. It shows what to practise. Do your best and skip what you are unsure of.':'🏆 Post-test: show what you have learned. Take your time, no timer.')+'</div>';
 const btns=v.items.map((x,i)=>'<button class="'+(String(ans[x.i]||'').trim()?'a ':'')+(i==cur?'cu':'')+'" onclick="go('+i+')">'+(i+1)+'</button>'),half=Math.ceil(n/2);
 const qc='<div class="qcard c'+cc+' pop"><div class="qn">Question '+(cur+1)+' of '+n+'</div><div class="q'+(it.q.length>34?' long':'')+'">'+mx(it.q)+'</div><input id="a" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" enterkeyhint="'+(cur<n-1?'next':'done')+'" placeholder="Type your answer here" value="'+esc(ans[it.i]||'')+'"><div class="hint">Examples: 12 · -5 · 3/4 · 0.5</div><div class="cheer" id="ch"></div></div>';
 const nv='<div class="nav"><button class="bk" id="pv"'+(cur?'':' disabled')+'>◀ Back</button>'+(cur<n-1?'<button class="nx" id="nx">Next ▶</button>':'<button class="sb" id="sb">✅ Submit</button>')+'</div>';
 h+='<div class="stage"><div class="nums L">'+btns.slice(0,half).join('')+'</div><div class="mid">'+qc+nv+'</div><div class="nums R">'+btns.slice(half).join('')+'</div></div>';
 $('app').innerHTML=h;const a=$('a');if(!/Mobi|Android/i.test(navigator.userAgent))a.focus();
 a.oninput=()=>{ans[it.i]=a.value;clearTimeout(window.st);window.st=setTimeout(()=>keep(it.i),500);const c=$('ch');if(c)c.textContent=a.value.trim()?CH[(cur*7+a.value.length)%CH.length]:''};
 a.onkeydown=e=>{if(e.key=='Enter'){e.preventDefault();if(cur<n-1)go(cur+1)}};$('pv').onclick=()=>go(cur-1);if($('nx'))$('nx').onclick=()=>go(cur+1);if($('sb'))$('sb').onclick=submit}
function keep(i){API('/api/t/save',{sec,name:nm,cid,i,v:ans[i]||''})}
function go(i){const it=V.items[cur];if(ans[it.i]!=null)keep(it.i);cur=Math.max(0,Math.min(V.items.length-1,i));render();window.scrollTo({top:0,behavior:'smooth'})}
function submit(){const un=V.items.filter(x=>!String(ans[x.i]||'').trim()).length,m=document.createElement('div');m.className='mod';
 m.innerHTML='<div class="box pop"><h2>'+(un?'⚠️ '+un+' blank':'🎯 Ready?')+'</h2><p>'+(un?'You left '+un+' question'+(un>1?'s':'')+' blank. Go back to answer them, or submit anyway. You cannot change answers afterwards.':'Submit your test? You cannot change answers afterwards.')+'</p><div class="row"><button id="mn">Go back</button><button class="p" id="my">Submit ✔</button></div></div>';
 document.body.appendChild(m);$('mn').onclick=()=>m.remove();
 $('my').onclick=async()=>{$('my').disabled=true;const r=await API('/api/t/submit',{sec,name:nm,cid,all:ans});m.remove();if(r&&r.ok){boom();V.done=true;await load()}else alert('Could not submit. Check the connection and try again.')}}
boot();setInterval(()=>{if(V&&nm&&!(V.phase&&!V.done&&V.items.length))load()},3000);setInterval(async()=>{if(!V||!nm||!V.phase||V.done||V.paused)return;const r=await API('/api/t/pstate?sec='+encodeURIComponent(sec)+'&name='+encodeURIComponent(nm));if(r&&(r.paused||r.phase!==V.phase||(r.gen!=null&&V.gen!=null&&r.gen!==V.gen)))load()},2000);setInterval(async()=>{const b=await bootId();if(b&&BOOT&&b!==BOOT){BOOT=b;try{localStorage.tboot=b}catch(e){}dropLogin('The server was restarted. Please log in again.')}},4000);
</script></body></html>"""

T_HOST = r"""<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Test dashboard</title>""" + T_CSS + r"""<style>:root{--a:#7c3aed;--b:#ec4899}
.pop{animation:pop .3s ease both}@keyframes pop{from{opacity:0;transform:translateY(10px)}}
.big{padding:24px;border-radius:30px;background:var(--card);text-align:center;border:2px solid var(--line);box-shadow:0 14px 40px rgba(124,58,237,.16)}
.big .em{line-height:1}.big h1{margin:.2em 0 .1em;font-size:clamp(30px,5vw,56px);font-weight:900}.big p{font-size:clamp(15px,2.2vw,22px);color:var(--mute);margin:.4em 0}
.score{display:flex;flex-wrap:wrap;gap:12px;justify-content:center;margin:14px 0}.score div{min-width:140px;padding:14px 22px;border-radius:24px;color:#fff;background:linear-gradient(135deg,var(--a),var(--b))}.score div:nth-child(2){background:linear-gradient(135deg,#06b6d4,#10b981)}
.score b{display:block;font-size:clamp(30px,6vw,56px);line-height:1.1}.score small{font-weight:800;letter-spacing:.06em;text-transform:uppercase}
.rep{width:100%;max-width:1200px;margin:0 auto;display:flex;flex-direction:column;gap:clamp(12px,2vw,22px)}
.rcard{padding:clamp(16px,3vw,32px);border-radius:30px;background:var(--card);border:3px solid var(--line);box-shadow:0 14px 40px rgba(124,58,237,.16)}
.rcard h2{margin:0 0 10px;font-size:clamp(22px,3.6vw,38px);font-weight:900}
.rcard.g{border-color:#10b981;background:linear-gradient(135deg,rgba(16,185,129,.14),var(--card) 60%)}.rcard.r{border-color:#ef4444;background:linear-gradient(135deg,rgba(239,68,68,.12),var(--card) 60%)}.rcard.y{border-color:#f59e0b;background:linear-gradient(135deg,rgba(245,158,11,.14),var(--card) 60%)}.rcard.v{border-color:var(--a)}
.rc{display:inline-block;margin:4px 6px 4px 0;padding:8px 18px;border-radius:99px;font-weight:800;font-size:clamp(15px,2.4vw,22px);color:#fff}.rc.g{background:linear-gradient(135deg,#10b981,#06b6d4)}.rc.r{background:linear-gradient(135deg,#ef4444,#f97316)}.rc.y{background:linear-gradient(135deg,#f59e0b,#eab308)}
.rrow{display:grid;grid-template-columns:minmax(120px,1.2fr) 3fr auto;gap:12px;align-items:center;margin:10px 0;font-size:clamp(15px,2.4vw,22px);font-weight:800}
.rbar{height:clamp(16px,2.4vw,24px);border-radius:99px;background:rgba(124,58,237,.14);overflow:hidden}.rbar i{display:block;height:100%;border-radius:99px}
.rrow small{display:block;font-weight:600;color:var(--mute);font-size:.7em}
.rtip{margin:8px 0;padding:12px 16px;border-radius:18px;background:rgba(124,58,237,.08);font-size:clamp(15px,2.3vw,21px);line-height:1.4}.rtip b{color:var(--a)}
.rbtn{padding:clamp(14px,2.4vw,22px) 28px;font-family:inherit;font-weight:900;font-size:clamp(18px,3vw,28px);border:0;border-radius:22px;cursor:pointer;color:#fff;background:linear-gradient(135deg,var(--a),var(--b));box-shadow:0 10px 24px rgba(236,72,153,.4)}
@media print{body{background:#fff!important}body::before,.noprint{display:none!important}#app{height:auto!important;max-width:none}.rcard,.bar{box-shadow:none!important;break-inside:avoid}.bar{-webkit-print-color-adjust:exact;print-color-adjust:exact}.rc,.rbar i,.score div{-webkit-print-color-adjust:exact;print-color-adjust:exact}}
body.pr #app{display:none!important}
@media print{body.pr{background:#fff!important;padding:0}#ov{position:static!important;overflow:visible!important;background:#fff!important;padding:0!important}.rpage{break-after:page}.noprint{display:none!important}.big,.rcard,.score div{-webkit-print-color-adjust:exact;print-color-adjust:exact}}
.two{display:grid;grid-template-columns:1fr 1fr;gap:clamp(12px,2vw,22px)}@media(max-width:800px){.two{grid-template-columns:1fr}}.rrow2{display:grid;grid-template-columns:minmax(120px,1.2fr) 3fr minmax(110px,auto);gap:12px;align-items:center;margin:12px 0;font-size:clamp(14px,2vw,20px);font-weight:800}.tt2{width:100%;border-collapse:collapse;font-size:clamp(13px,1.8vw,18px)}.tt2 td,.tt2 th{padding:7px 10px;border-bottom:1px solid var(--line);text-align:center}.tt2 td:first-child,.tt2 th:first-child{text-align:left}
</style>
<style>/* ===== teacher dashboard redesign ===== */
:root{--v:#7c3aed;--pk:#ec4899;--soft:#f1ecff;--soft2:#f9f7ff;--okc:#047857;--wnbg:#fff0cc;--wnc:#92400e;--erc:#b91c1c;--shadow:0 1px 2px rgba(60,30,120,.06),0 14px 34px rgba(88,40,200,.10)}
@media(prefers-color-scheme:dark){:root{--soft:#2a2457;--soft2:#221d4b;--okc:#4ade80;--wnbg:#3a2c0c;--wnc:#fbbf24;--erc:#fca5a5;--shadow:0 14px 34px rgba(0,0,0,.4)}}
body{padding:20px 16px 56px;background:radial-gradient(900px 420px at 0% -10%,rgba(236,72,153,.16),transparent 60%),radial-gradient(800px 420px at 100% -5%,rgba(6,182,212,.16),transparent 60%),var(--bg)}
.dh{max-width:1080px;margin:0 auto;display:grid;gap:16px}.dh :focus-visible{outline:3px solid var(--v);outline-offset:2px}.d-hero :focus-visible{outline-color:#fff}
.d-hero{color:#fff;border-radius:28px;padding:clamp(20px,3.2vw,32px);background:radial-gradient(520px 240px at 92% 0%,rgba(255,255,255,.22),transparent 70%),linear-gradient(120deg,#5b21b6,#7c3aed 45%,#db2777);box-shadow:0 18px 44px rgba(124,58,237,.35)}
.d-top{display:flex;gap:16px;justify-content:space-between;align-items:flex-start;flex-wrap:wrap}
.d-hero h1{margin:0;font-size:clamp(26px,4vw,38px);font-weight:850;letter-spacing:-.02em;background:none;-webkit-text-fill-color:#fff;color:#fff}
.d-join{margin-top:8px;font-size:15px}.d-join b{background:rgba(255,255,255,.2);padding:3px 11px;border-radius:99px;white-space:nowrap}
.d-btn{display:inline-flex;align-items:center;gap:8px;padding:11px 16px;border-radius:14px;font:700 15px/1.2 inherit;border:0;cursor:pointer;background:var(--soft);color:var(--ink)}
.d-btn:hover{filter:brightness(.96)}.d-btn:active{transform:translateY(1px)}.d-btn:disabled{opacity:.45;cursor:not-allowed}
.d-btn.pri{background:linear-gradient(135deg,var(--v),var(--pk));color:#fff;box-shadow:0 8px 20px rgba(236,72,153,.32)}
.d-btn.glass{background:rgba(255,255,255,.2);color:#fff}
.d-btn.sm{padding:7px 12px;font-size:14px;border-radius:11px}
.d-btn.ghost{background:transparent;color:var(--mute);box-shadow:inset 0 0 0 1.5px var(--line)}
.d-sel{display:grid;gap:5px;margin-top:20px;max-width:420px;font-size:14px;font-weight:600}
.d-sel select{margin:0;padding:11px 14px;border-radius:14px;border:0;font-size:17px;font-weight:700;background:#fff;color:#1e1b3a}
.d-steps{display:flex;flex-wrap:wrap;gap:8px;margin-top:18px}
.d-step{display:flex;align-items:center;gap:9px;padding:11px 22px;border-radius:99px;border:0;cursor:pointer;font:700 15px/1.2 inherit;color:#fff;background:rgba(255,255,255,.16)}
.d-step:hover{background:rgba(255,255,255,.26)}
.d-step i{display:grid;place-items:center;width:26px;height:26px;border-radius:50%;background:rgba(255,255,255,.25);font-style:normal;font-size:13px}
.d-step.done i{background:#34d399;color:#064e3b}
.d-step.on,.d-step.on:hover{background:#fff;color:#5b21b6;box-shadow:0 6px 18px rgba(0,0,0,.2)}.d-step.on i{background:linear-gradient(135deg,var(--v),var(--pk));color:#fff}
.d-hint{margin:14px 0 0;font-size:16px;line-height:1.45;max-width:70ch}
.d-card{background:var(--card);border:1px solid var(--line);border-radius:22px;box-shadow:var(--shadow);padding:clamp(16px,2.4vw,22px)}
.d-grid{display:grid;grid-template-columns:1fr 1fr 1.3fr;gap:16px}
.d-bpg{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:14px 18px;margin-top:6px}.d-bpf .d-stp{margin:4px 0 8px}.d-bpf select,.d-bpf input{width:100%;margin:0}.d-seg{display:flex;gap:8px}.d-seg .d-btn{flex:1;justify-content:center}.d-tot{margin-left:auto;font-weight:700;font-size:13px;color:var(--mute);background:var(--soft);border-radius:99px;padding:4px 12px}.d-bpbar{display:flex;flex-wrap:wrap;gap:10px;margin:18px 0 4px;padding-top:16px;border-top:1px dashed var(--line)}.d-sub{margin:20px 0 8px;font-size:15px;font-weight:800}
.dh .d-grid>.d-card:nth-child(1){background:linear-gradient(rgba(124,58,237,.15),rgba(124,58,237,.15)),var(--card);border-color:rgba(124,58,237,.45)}
.dh .d-grid>.d-card:nth-child(2){background:linear-gradient(rgba(6,182,212,.15),rgba(6,182,212,.15)),var(--card);border-color:rgba(6,182,212,.45)}
.dh .d-grid>.d-card:nth-child(3){background:linear-gradient(rgba(245,158,11,.15),rgba(245,158,11,.15)),var(--card);border-color:rgba(245,158,11,.45)}
.dh>section.d-card:nth-of-type(1){background:linear-gradient(rgba(236,72,153,.15),rgba(236,72,153,.15)),var(--card);border-color:rgba(236,72,153,.45)}
.dh>section.d-card:nth-of-type(2){background:linear-gradient(rgba(59,130,246,.15),rgba(59,130,246,.15)),var(--card);border-color:rgba(59,130,246,.45)}
.dh>section.d-card:nth-of-type(3){background:linear-gradient(rgba(249,115,22,.15),rgba(249,115,22,.15)),var(--card);border-color:rgba(249,115,22,.45)}
.dh>section.d-card:nth-of-type(4){background:linear-gradient(rgba(20,184,166,.15),rgba(20,184,166,.15)),var(--card);border-color:rgba(20,184,166,.45)}
@media(max-width:900px){.d-grid{grid-template-columns:1fr 1fr}.d-share{grid-column:1/-1}}@media(max-width:560px){.d-grid{grid-template-columns:1fr}}
.d-prog{display:flex;align-items:center;gap:16px}
.d-ring{flex:none;position:relative;display:grid;place-items:center;width:88px;height:88px;border-radius:50%;background:conic-gradient(var(--c1),var(--c2) calc(var(--p)*1%),var(--soft) 0)}
.d-ring::before{content:"";position:absolute;inset:11px;border-radius:50%;background:var(--card)}.d-ring b{position:relative;font-size:22px}.d-ring small{font-size:13px;color:var(--mute)}
.d-pinfo h2{margin:0;font-size:19px}.d-pinfo p{margin:2px 0 8px;color:var(--mute);font-size:15px}.d-tags{display:flex;flex-wrap:wrap;gap:6px}
.d-pill{display:inline-flex;align-items:center;gap:6px;padding:4px 11px;border-radius:99px;font-size:13px;font-weight:700;background:var(--soft);color:var(--ink)}
.d-pill.fin{background:rgba(16,185,129,.16);color:var(--okc)}.d-pill.live{background:var(--wnbg);color:var(--wnc)}.d-pill.live i{width:8px;height:8px;border-radius:50%;background:currentColor;animation:dp 1.4s infinite}@keyframes dp{50%{opacity:.25}}
@media(prefers-reduced-motion:reduce){.d-pill.live i{animation:none}}
.d-switch{display:flex;align-items:center;gap:12px;cursor:pointer;font-weight:700;font-size:15px;position:relative;margin-bottom:14px}
.dh .d-switch input{position:absolute;opacity:0;width:0;height:0;margin:0;padding:0;border:0}
.d-switch .t{flex:none;width:46px;height:28px;border-radius:99px;background:var(--line);position:relative}
.d-switch .t::after{content:"";position:absolute;top:3px;left:3px;width:22px;height:22px;border-radius:50%;background:#fff;box-shadow:0 1px 3px rgba(0,0,0,.3);transition:transform .15s}
.d-switch input:checked+.t{background:linear-gradient(135deg,#10b981,#06b6d4)}.d-switch input:checked+.t::after{transform:translateX(18px)}
.d-switch input:focus-visible+.t{outline:3px solid var(--v);outline-offset:2px}
.d-btns{display:flex;flex-wrap:wrap;gap:8px}
.d-ch{display:flex;gap:12px;align-items:center;justify-content:space-between;flex-wrap:wrap;margin-bottom:10px}.d-ch h2{margin:0;font-size:20px}.d-ch small{color:var(--mute);font-weight:600;font-size:15px;margin-left:8px}
.d-fold{display:flex;align-items:center;gap:10px;background:none;border:0;padding:0;cursor:pointer;color:inherit;font:inherit;text-align:left}.d-chev{display:grid;place-items:center;width:30px;height:30px;border-radius:10px;background:var(--soft);transition:transform .15s}.d-fold[aria-expanded=false] .d-chev{transform:rotate(-90deg)}.d-sum{color:var(--mute);font-size:14.5px;margin:0}
.d-bp .d-chips{display:flex;flex-wrap:wrap;gap:8px;margin:12px 0 14px}.d-chip{display:inline-flex;align-items:center;gap:8px;padding:9px 14px 9px 9px;border-radius:99px;border:2px solid var(--line);background:var(--card);color:var(--ink);font:700 14.5px/1.2 inherit;cursor:pointer}.d-chip i{display:grid;place-items:center;width:20px;height:20px;border-radius:50%;border:2px solid var(--line);font-style:normal;font-size:12px;color:#fff}.d-chip.on{border-color:var(--v);background:var(--soft)}.d-chip.on i{background:linear-gradient(135deg,var(--v),var(--pk));border-color:transparent}.d-chip:disabled{opacity:.6;cursor:not-allowed}
.d-bpr{display:flex;flex-wrap:wrap;gap:14px;align-items:center}.d-bpn{display:flex;align-items:center;gap:8px;font-weight:700;font-size:15px}.d-bpn select{width:auto;margin:0;padding:8px 12px;font-size:15px;border-radius:12px}.d-bpt{font-size:15px}.d-stp{display:flex;align-items:center;gap:10px;font-weight:800;font-size:15px;margin:18px 0 8px}.d-stp i{display:inline-grid;place-items:center;width:26px;height:26px;border-radius:50%;background:#7c3aed;color:#fff;font-style:normal;font-size:13px;flex:none}
.d-chr{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-left:auto}.d-find{width:min(100%,280px);margin:0;padding:10px 14px;border-radius:14px;font-size:15px}
.d-table{width:100%;border-collapse:collapse;font-size:15px}
.d-table th{position:sticky;top:0;z-index:2;background:var(--card);text-align:left;font-size:13.5px;color:var(--mute);font-weight:700;padding:8px 10px;border-bottom:2px solid var(--line)}
.d-table td{text-align:left;padding:9px 10px;border-bottom:1px solid var(--line);vertical-align:middle}.d-table tbody tr:last-child td{border-bottom:0}.d-table tbody tr:hover td{background:var(--soft2)}
.d-name{display:flex;align-items:center;gap:12px;font-weight:700}
.d-av{flex:none;width:36px;height:36px;border-radius:50%;display:grid;place-items:center;color:#fff;font-size:13px;font-weight:800;background:hsl(var(--h) 62% 44%)}
.d-score{display:flex;align-items:center;gap:10px}.d-score b{min-width:42px;font-size:16px}
.d-bar{flex:1;max-width:90px;height:8px;border-radius:99px;background:var(--soft);overflow:hidden}.d-bar i{display:block;height:100%;border-radius:99px}
.d-score.g i{background:linear-gradient(90deg,#10b981,#06b6d4)}.d-score.y i{background:linear-gradient(90deg,#f59e0b,#eab308)}.d-score.r i{background:linear-gradient(90deg,#ef4444,#f97316)}
.d-none{color:var(--mute);opacity:.65;font-size:14px}.d-gain{font-weight:800}.d-gain.up{color:var(--okc)}.d-gain.dn{color:var(--erc)}
.d-act{text-align:right!important;white-space:nowrap}.d-act .d-btn{margin-left:6px}.d-empty{text-align:center!important;color:var(--mute);padding:28px 10px!important}
.d-foot,.d-note{margin:0;color:var(--mute);font-size:14.5px;line-height:1.55;max-width:80ch}
.d-tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:12px;margin:6px 0 14px}
.d-tile{padding:14px 16px;border-radius:18px;background:var(--soft2);border:1px solid var(--line)}.d-tile b{display:block;font-size:27px;line-height:1.15}.d-tile small{color:var(--mute);font-weight:600}
.d-grow h3{margin:20px 0 8px;font-size:17px}.d-scroll{overflow-x:auto}
@media(max-width:720px){.c-gain{display:none}.d-act{white-space:normal!important}}
/* ===== reports: A4 portrait, same size on screen and in the PDF ===== */
@page{size:A4 portrait;margin:10mm}.pbrk{height:0}@media print{.pbrk{break-after:page}}
#ov .rpage,#ov .noprint{max-width:794px!important}#ov .rpage{margin:0 auto 20px!important}
#ov .rep{gap:8px}
#ov .big{padding:10px 14px!important;border-radius:16px;border-width:1.5px}#ov .big .em{font-size:28px!important}#ov .big h1{font-size:20px;margin:.1em 0}#ov .big p{font-size:12px;margin:.2em 0}
#ov .score{gap:8px;margin:8px 0}#ov .score div{min-width:90px;padding:6px 12px;border-radius:14px}#ov .score b{font-size:22px}#ov .score small{font-size:10px}
#ov .rcard{padding:10px 14px;border-radius:16px;border-width:1.5px;break-inside:avoid}#ov .rcard h2{font-size:14px;margin:0 0 6px}
#ov .rc{font-size:11px;padding:3px 10px;margin:2px 4px 2px 0}
#ov .rrow,#ov .rrow2{font-size:11px;gap:8px;margin:5px 0}#ov .rbar{height:10px}
#ov .rtip{font-size:11px;padding:6px 10px;margin:4px 0;border-radius:10px;line-height:1.35}
#ov .tt2{font-size:10.5px}#ov .tt2 td,#ov .tt2 th{padding:3px 6px}#ov .rcard p{font-size:11px}
#ov .d-card{box-shadow:none;padding:12px 14px;border-radius:16px;-webkit-print-color-adjust:exact;print-color-adjust:exact}#ov .d-table{font-size:11px}#ov .d-table th{position:static}#ov .d-tile{-webkit-print-color-adjust:exact;print-color-adjust:exact}#ov .d-tile b{font-size:20px}#ov .d-note{font-size:11px}#ov .d-grow h3{font-size:14px;margin:12px 0 6px}#ov .d-scroll{overflow:visible}
@media print,(min-width:600px){#ov .two{grid-template-columns:1fr 1fr!important;gap:8px}}
@media print{#ov .rpage{margin:0!important;break-after:page}#ov .rpage:last-child{break-after:auto}}
</style>
</head><body><div id="app"></div>
<script>
const $=i=>document.getElementById(i),esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const TEM={'Basic Operations':'🔢','Integers':'➕','Fractions':'🍕','Word Problem':'📖','Algebra':'🧮','Percent & Ratio':'💯','Geometry & Data':'📐'};
const TTIP={'Basic Operations':'Practise your times tables, and check each answer by doing the opposite operation.','Integers':'Draw a number line. Same signs: add and keep the sign. Different signs: subtract and use the sign of the bigger number.','Fractions':'Find a common denominator first, then add or subtract the tops. Always simplify at the end.','Word Problem':'Underline the numbers and the question. Decide the operation before you calculate.','Algebra':'Do the same step to both sides. Undo + and − first, then × and ÷.','Percent & Ratio':'Percent means "per 100". Change it to a fraction first, then multiply.','Geometry & Data':'Write the formula first, then put in the numbers. Draw a quick sketch.'};
const SKL=[['add','Addition','➕'],['sub','Subtraction','➖'],['mul','Multiplication','✖️'],['div','Division','➗']];
const SKTIPS={add:'Line up the digits by place value. Add from the right and carry when you reach 10 or more. Check by adding in a different order.',sub:'Line up the digits and borrow when the top digit is smaller. Check by adding your answer to the number you took away.',mul:'Learn your times tables, then break big numbers into tens and ones. Estimate first to check your answer.',div:'Ask: what times the divisor gives this number? Check by multiplying your answer by the divisor.'};
const skcol=p=>p>=75?'linear-gradient(90deg,#10b981,#06b6d4)':p>=50?'linear-gradient(90deg,#f59e0b,#eab308)':'linear-gradient(90deg,#ef4444,#f97316)';
const skchip=(a,c)=>a.map(x=>'<span class="rc '+c+'">'+x.e+' '+x.n+' · '+x.p+'% <small>('+x.c+'/'+x.t+')</small></span>').join('');
const skh='<h2 style="margin-top:14px;font-size:clamp(18px,2.8vw,28px)">🧮 By skill</h2>',skno='<span style="color:var(--mute);font-weight:700">None this time</span>';
function skdata(L){const sk=L.sk||{},o={L:[]};SKL.forEach(s=>{const v=sk[s[0]];if(v&&v[1])o.L.push({k:s[0],n:s[1],e:s[2],c:v[0],t:v[1],p:Math.round(100*v[0]/v[1]),dr:(L.drill||{})[s[0]]})});
 o.S=o.L.filter(x=>x.p>=75);o.W=o.L.filter(x=>x.p<50);o.M=o.L.filter(x=>x.p>=50&&x.p<75);o.err=L.skerr||{};
 o.steps=o.L.filter(x=>x.p<75).sort((a,b)=>a.p-b.p).map(x=>'<div class="rtip"><b>'+x.e+' '+x.n+'</b> · '+SKTIPS[x.k]+'</div>').join('');return o}
function skS(K){return K.L.length?skh+(K.S.length?skchip(K.S,'g'):skno):''}
function skN(K){return K.L.length?skh+(K.W.length?skchip(K.W,'r'):'')+(K.M.length?'<br>'+skchip(K.M,'y'):'')+(K.W.length||K.M.length?'':skno):''}
function skCard(K){if(!K.L.length)return '';return '<div class="rcard v"><h2>🧮 My operation skills</h2>'+K.L.map(x=>'<div class="rrow"><div>'+x.e+' '+x.n+(x.dr&&x.dr[1]?'<small>Practice so far: '+x.dr[0]+'/'+x.dr[1]+' ('+Math.round(100*x.dr[0]/x.dr[1])+'%)</small>':'')+'</div><div class="rbar"><i style="width:'+Math.max(x.p,2)+'%;background:'+skcol(x.p)+'"></i></div><div>'+x.c+'/'+x.t+'</div></div>').join('')+'<p style="margin:8px 0 0;color:var(--mute)">Only the test questions that were one plain operation are counted here.</p></div>'}
function skMerge(E,K){SKL.forEach(s=>{const t=K.err[s[0]]||{};Object.keys(t).forEach(k=>{const e=E[k];if(e&&e.t.indexOf(s[1])<0)e.t.push(s[1])})})}
function skSW(L){const K=skdata(L);return K.L.length?'<br><b>🧮 By skill</b><br>'+K.L.map(x=>skchip([x],x.p>=75?'g':x.p>=50?'y':'r')).join(''):''}
function skComp(A,B){const f=(L,k)=>{const v=L.sk&&L.sk[k];return v&&v[1]?Math.round(100*v[0]/v[1]):null},rows=SKL.filter(s=>f(A,s[0])!=null||f(B,s[0])!=null);if(!rows.length)return '';
 return '<div class="rcard v"><h2>🧮 Operation skills: Pre-test vs Post-test</h2>'+rows.map(s=>{const a=f(A,s[0]),b=f(B,s[0]),c=a!=null&&b!=null?b-a:null;return '<div class="rrow2"><div>'+s[2]+' '+s[1]+'</div><div><div class="rbar" style="margin-bottom:4px"><i style="width:'+Math.max(a||0,2)+'%;background:'+skcol(a||0)+';opacity:.55"></i></div><div class="rbar"><i style="width:'+Math.max(b||0,2)+'%;background:'+skcol(b||0)+'"></i></div></div><div style="text-align:right">'+(a==null?'–':a+'%')+' → <b>'+(b==null?'–':b+'%')+'</b>'+(c==null?'':'<br><span style="color:'+(c>=0?'#059669':'#dc2626')+'">'+(c>=0?'+':'')+c+'</span>')+'</div></div>'}).join('')+'<p style="color:var(--mute);margin:8px 0 0">Faded bar = pre-test, solid bar = post-test. Each skill has only a few test questions, so read it as a guide.</p></div>'}
const ETIP={sign:['➖','Sign mistakes','Your digits were right but the sign was opposite. Slow down on positive and negative numbers.'],slip:['🔍','Small slips','Some answers were off by just 1. Re-check your last step before you answer.'],place:['🔟','Place value','Some answers had the right digits but the wrong size. Check zeros and the decimal point.'],operation:['🔀','Wrong operation','Some answers matched a different operation. Re-read the question and decide which operation it asks for.'],format:['✏️','Answer format','Some answers were not numbers. Type numbers like 12, -5, 3/4 or 0.5.'],other:['🧩','Other mistakes','Compare each step of your working to find where it changed.'],blank:['⬜','Blank answers','Some questions were left blank. In practice, always try: a good guess is better than nothing.']};
function report(R,nm,sec,title){
 const ph=R.post?'post':'pre',L=R[ph],P=L.per,T=Object.keys(P),pc=t=>P[t][1]?Math.round(100*P[t][0]/P[t][1]):0;
 const S=T.filter(t=>pc(t)>=75),W=T.filter(t=>pc(t)<50),M=T.filter(t=>pc(t)>=50&&pc(t)<75);
 const chips=(a,c)=>a.length?a.map(t=>'<span class="rc '+c+'">'+(TEM[t]||'')+' '+esc(t)+' · '+pc(t)+'%</span>').join(''):'<span style="color:var(--mute);font-weight:700">None this time</span>';
 const E={};Object.keys(L.err||{}).forEach(t=>Object.keys(L.err[t]).forEach(k=>{const e=E[k]||(E[k]={n:0,t:[]});e.n+=L.err[t][k];if(e.t.indexOf(t)<0)e.t.push(t)}));
 const ek=Object.keys(E).filter(k=>ETIP[k]).sort((a,b)=>E[b].n-E[a].n).slice(0,4);
 const prac=T.filter(t=>pc(t)<75).sort((a,b)=>pc(a)-pc(b)).slice(0,3),K=skdata(L);skMerge(E,K);
 const col=p=>p>=75?'linear-gradient(90deg,#10b981,#06b6d4)':p>=50?'linear-gradient(90deg,#f59e0b,#eab308)':'linear-gradient(90deg,#ef4444,#f97316)';
 let h='<div class="rep pop"><div class="big" style="padding:clamp(18px,3vw,34px)"><div class="em" style="font-size:clamp(50px,9vw,90px)">📋</div><h1>'+(title||'My Personal Report')+'</h1><p>'+(R.post?'After your post-test':'After your pre-test')+' · '+esc(nm)+' · '+esc(sec)+'</p>';
 h+='<div class="score">'+Object.keys(R).map(x=>'<div><b>'+R[x].pct+'%</b><small>'+(x=='pre'?'Pre-test':'Post-test')+'</small></div>').join('')+'</div>';
 if(R.pre&&R.post)h+='<p><b>'+(R.post.pct>=R.pre.pct?'📈 You grew by '+(R.post.pct-R.pre.pct)+' points. Your practice is working!':'Your score dipped this time. Practise the topics below.')+'</b></p>';
 h+='</div>';
 h+='<div class="rcard g"><h2>💪 My strengths</h2>'+chips(S,'g')+'<p style="margin:8px 0 0;color:var(--mute)">Topics where you scored 75% or more. Keep it up!</p>'+skS(K)+'</div>';
 h+='<div class="rcard r"><h2>🎯 Needs more practice</h2>'+chips(W,'r')+(M.length?'<h2 style="margin-top:14px;font-size:clamp(18px,2.8vw,28px)">🌱 Getting there</h2>'+chips(M,'y'):'')+'<p style="margin:8px 0 0;color:var(--mute)">Red: below 50%. Yellow: 50% to 74%.</p>'+skN(K)+'</div>';
 h+='<div class="rcard v"><h2>📊 All topics</h2>'+T.map(t=>'<div class="rrow"><div>'+(TEM[t]||'')+' '+esc(t)+(R.pre&&R.post?'<small>Pre-test: '+(R.pre.per[t][1]?Math.round(100*R.pre.per[t][0]/R.pre.per[t][1]):0)+'%</small>':'')+'</div><div class="rbar"><i style="width:'+Math.max(pc(t)?pc(t):2,2)+'%;background:'+col(pc(t))+'"></i></div><div>'+P[t][0]+'/'+P[t][1]+'</div></div>').join('')+'</div>';
 h+=skCard(K);
 if(ek.length)h+='<div class="rcard y"><h2>🔎 Mistake patterns</h2>'+ek.map(k=>'<div class="rtip">'+ETIP[k][0]+' <b>'+ETIP[k][1]+'</b> ('+E[k].n+') · '+ETIP[k][2]+'<br><small style="color:var(--mute)">Seen in: '+E[k].t.map(esc).join(', ')+'</small></div>').join('')+'</div>';
 h+='<div class="rcard v"><h2>🚀 My next steps</h2>'+K.steps+(prac.length||K.steps?prac.map((t,i)=>'<div class="rtip"><b>'+(i+1)+'. '+(TEM[t]||'')+' '+esc(t)+'</b> · '+(TTIP[t]||'')+'</div>').join(''):'<div class="rtip">🏆 Excellent work! Challenge yourself with harder problems and help a classmate.</div>')+'</div>';
 return h}
function reportT(R,nm,sec){
 if(!(R.pre&&R.post))return report(R,nm,sec,R.pre?'Pre-test Report':'Post-test Report');
 const br='<div class="pbrk"></div>';
 return report({pre:R.pre},nm,sec,'Part 1 · Pre-test only')+br+report({post:R.post},nm,sec,'Part 2 · Post-test only')+br+cmpT(R,nm,sec)}
const pcT=(per,t)=>per[t]&&per[t][1]?Math.round(100*per[t][0]/per[t][1]):0;
const colT=p=>p>=75?'linear-gradient(90deg,#10b981,#06b6d4)':p>=50?'linear-gradient(90deg,#f59e0b,#eab308)':'linear-gradient(90deg,#ef4444,#f97316)';
const chipT=(a,c,f)=>a.length?a.map(t=>'<span class="rc '+c+'">'+(TEM[t]||'')+' '+esc(t)+' · '+f(t)+'%</span>').join(''):'<span style="color:var(--mute);font-weight:700">None</span>';
function errAgg(L){const E={};Object.keys(L.err||{}).forEach(t=>Object.keys(L.err[t]).forEach(k=>{const e=E[k]||(E[k]={n:0,t:[]});e.n+=L.err[t][k];if(e.t.indexOf(t)<0)e.t.push(t)}));return E}
function errHtml(E,max){const ek=Object.keys(E).filter(k=>ETIP[k]).sort((a,b)=>E[b].n-E[a].n).slice(0,max);return ek.length?ek.map(k=>'<div class="rtip">'+ETIP[k][0]+' <b>'+ETIP[k][1]+'</b> ('+E[k].n+') · '+ETIP[k][2]+'<br><small style="color:var(--mute)">Seen in: '+E[k].t.map(esc).join(', ')+'</small></div>').join(''):'<div class="rtip">No mistake details recorded.</div>'}
function cmpT(R,nm,sec){
 const A=R.pre,B=R.post,T=Object.keys(B.per),d=B.pct-A.pct;
 let h='<div class="rep pop"><div class="big" style="padding:clamp(18px,3vw,34px)"><div class="em" style="font-size:clamp(50px,9vw,80px)">📋</div><h1>Part 3 · Comparison: Pre-test vs Post-test</h1><p><b>'+esc(nm)+'</b> · '+esc(sec)+'</p><div class="score"><div><b>'+A.pct+'%</b><small>Pre-test</small></div><div><b>'+B.pct+'%</b><small>Post-test</small></div><div style="background:linear-gradient(135deg,'+(d>=0?'#10b981,#84cc16':'#ef4444,#f97316')+')"><b>'+(d>=0?'+':'')+d+'</b><small>Change (pts)</small></div></div></div>';
 const sw=(L,lab)=>{const S=T.filter(t=>pcT(L.per,t)>=75),W=T.filter(t=>pcT(L.per,t)<50),M=T.filter(t=>pcT(L.per,t)>=50&&pcT(L.per,t)<75),f=t=>pcT(L.per,t);
  return '<div class="rcard v"><h2>'+lab+' · '+L.pct+'%</h2><b>💪 Strengths</b><br>'+chipT(S,'g',f)+'<br><b>🌱 Getting there</b><br>'+chipT(M,'y',f)+'<br><b>🎯 Needs practice</b><br>'+chipT(W,'r',f)+skSW(L)+'</div>'};
 h+='<div class="two">'+sw(A,'Pre-test')+sw(B,'Post-test')+'</div>';
 h+='<div class="rcard v"><h2>📊 Pre-test vs Post-test by topic</h2>'+T.map(t=>{const a=pcT(A.per,t),b=pcT(B.per,t),c=b-a;
  return '<div class="rrow2"><div>'+(TEM[t]||'')+' '+esc(t)+'</div><div><div class="rbar" style="margin-bottom:4px"><i style="width:'+Math.max(a,2)+'%;background:'+colT(a)+';opacity:.55"></i></div><div class="rbar"><i style="width:'+Math.max(b,2)+'%;background:'+colT(b)+'"></i></div></div><div style="text-align:right">'+a+'% → <b>'+b+'%</b><br><span style="color:'+(c>=0?'#059669':'#dc2626')+'">'+(c>=0?'+':'')+c+'</span></div></div>'}).join('')+'<p style="color:var(--mute);margin:8px 0 0">Faded bar = pre-test, solid bar = post-test.</p></div>';
 h+=skComp(A,B);
 h+='<div class="two"><div class="rcard y"><h2>🔎 Pre-test mistakes</h2>'+errHtml(errAgg(A),3)+'</div><div class="rcard y"><h2>🔎 Post-test mistakes</h2>'+errHtml(errAgg(B),3)+'</div></div>';
 const imp=T.map(t=>[t,pcT(B.per,t)-pcT(A.per,t)]).sort((x,y)=>y[1]-x[1]),best=imp.filter(x=>x[1]>0).slice(0,2),drop=imp.filter(x=>x[1]<0).slice(-2),prac=T.filter(t=>pcT(B.per,t)<75).sort((x,y)=>pcT(B.per,x)-pcT(B.per,y)).slice(0,3);
 h+='<div class="rcard v"><h2>🚀 Summary and next steps</h2>'+(best.length?'<div class="rtip">📈 <b>Grew most:</b> '+best.map(x=>(TEM[x[0]]||'')+' '+esc(x[0])+' (+'+x[1]+')').join(', ')+'</div>':'')+(drop.length?'<div class="rtip">📉 <b>Went down:</b> '+drop.map(x=>(TEM[x[0]]||'')+' '+esc(x[0])+' ('+x[1]+')').join(', ')+'</div>':'')+(prac.length?prac.map((t,i)=>'<div class="rtip"><b>'+(i+1)+'. Practise '+(TEM[t]||'')+' '+esc(t)+'</b> · '+(TTIP[t]||'')+'</div>').join(''):'<div class="rtip">🏆 Excellent work. Challenge with harder problems.</div>')+'</div></div>';
 return h}
const IA_M=75,IA_N=50,IA_L=['🏅 Mastered','🟡 Nearly Mastered','🔴 Not Mastered'],IA_C=['#10b981','#f59e0b','#ef4444'],IA_BG=['#d1fae5','#fef3c7','#fee2e2'];
const iaP=x=>x&&x[1]?Math.round(100*x[0]/x[1]):null,iaB=p=>p==null?-1:p>=IA_M?0:p>=IA_N?1:2;
const iaPill=p=>{const b=iaB(p);return b<0?'<span style="color:#9ca3af">–</span>':'<span style="display:inline-block;padding:1px 8px;border-radius:99px;font-weight:800;background:'+IA_BG[b]+';color:#1e1b3a;-webkit-print-color-adjust:exact;print-color-adjust:exact">'+IA_L[b]+'</span>'};
function iaCount(items,ph){const o=[0,0,0];items.forEach(it=>{const b=iaB(iaP(it[ph]));if(b>=0)o[b]++});return o}
function iaCard(IA){const it=IA&&IA.items?IA.items:[];if(!it.length)return '';
 const hasPre=it.some(x=>x.pre[1]),hasPost=it.some(x=>x.post[1]),phs=['pre','post'].filter(p=>p=='pre'?hasPre:hasPost),LB={pre:'Pre-test',post:'Post-test'};
 const sum=phs.map(p=>{const c=iaCount(it,p),N=c[0]+c[1]+c[2];return '<div style="margin:8px 0"><b>'+LB[p]+'</b> ('+N+' items)'+[0,1,2].map(i=>'<div class="rrow" style="grid-template-columns:minmax(150px,1.4fr) 3fr auto"><div>'+IA_L[i]+' ('+(i==0?IA_M+'%+':i==1?IA_N+'–'+(IA_M-1)+'%':'below '+IA_N+'%')+')</div><div class="rbar"><i style="width:'+(N&&c[i]?Math.max(100*c[i]/N,3):0)+'%;background:'+IA_C[i]+'"></i></div><div>'+c[i]+'</div></div>').join('')+'</div>'}).join('');
 let cur=null;const rows=it.map((x,k)=>{let g='';if(x.t!=cur){cur=x.t;g='<tr><td colspan="'+(2+phs.length*2)+'" style="background:#ddd2fd;font-weight:800;color:#5b21b6;-webkit-print-color-adjust:exact;print-color-adjust:exact">'+esc((TEM[x.t]||'')+' '+x.t)+'</td></tr>'}
  return g+'<tr style="break-inside:avoid"><td>'+(k+1)+'</td><td>'+esc(x.q)+' <small style="color:var(--mute)">(ans: '+esc(x.a)+')</small></td>'+phs.map(p=>{const v=iaP(x[p]);return '<td>'+(v==null?'–':v+'% <small style="color:var(--mute)">('+x[p][0]+'/'+x[p][1]+')</small>')+'</td><td>'+iaPill(v)+'</td>'}).join('')+'</tr>'}).join('');
 const lst=(ph,b)=>{const a=it.filter(x=>iaB(iaP(x[ph]))==b).sort((p,q)=>b==0?iaP(q[ph])-iaP(p[ph]):iaP(p[ph])-iaP(q[ph]));
  return a.length?a.map(x=>'<div class="rtip" style="border-left:4px solid '+IA_C[b]+';break-inside:avoid"><b>Q'+(it.indexOf(x)+1)+'.</b> '+esc(x.q)+' → <b>'+esc(x.a)+'</b> · <b>'+iaP(x[ph])+'%</b> ('+x[ph][0]+'/'+x[ph][1]+') · <small>'+esc((TEM[x.t]||'')+' '+x.t)+'</small></div>').join(''):'<div class="rtip">None</div>'};
 const hint=['Easiest first','Review these','Hardest first: re-teach these'],cls=['g','y','r'];
 const lists=phs.map(p=>'<h3 style="margin:14px 0 4px">'+LB[p]+': questions by level</h3>'+[2,1,0].map(b=>'<div class="rcard '+cls[b]+'"><h2>'+IA_L[b]+' ('+iaCount(it,p)[b]+') <small style="font-weight:600;color:var(--mute)">· '+hint[b]+'</small></h2>'+lst(p,b)+'</div>').join('')).join('');
 return '<div class="rcard v"><h2>🧪 Item Analysis (Mastered · Nearly Mastered · Not Mastered)</h2><p style="color:var(--mute);margin:0 0 6px">Each question is judged by the share of tested students who answered it correctly: Mastered '+IA_M+'% or more, Nearly Mastered '+IA_N+'–'+(IA_M-1)+'%, Not Mastered below '+IA_N+'%.</p>'+sum
  +'<table class="tt2" style="width:100%;margin-top:8px"><tr><th>#</th><th>Question</th>'+phs.map(p=>'<th>'+LB[p]+' % correct</th><th>'+LB[p]+' level</th>').join('')+'</tr>'+rows+'</table></div>'+lists}
function iaStu(IA,nm){const it=IA&&IA.items?IA.items:[],S=(IA&&IA.stu&&IA.stu[nm])||{};if(!it.length||!(S.pre||S.post))return '';
 const phs=['pre','post'].filter(p=>S[p]),LB={pre:'Pre-test',post:'Post-test'};let cur=null;
 const rows=it.map((x,k)=>{const id=String(x.id);if(!phs.some(p=>S[p][id]!=null))return '';let g='';if(x.t!=cur){cur=x.t;g='<tr><td colspan="'+(2+phs.length*2)+'" style="background:#ddd2fd;font-weight:800;color:#5b21b6;-webkit-print-color-adjust:exact;print-color-adjust:exact">'+esc((TEM[x.t]||'')+' '+x.t)+'</td></tr>'}
  return g+'<tr style="break-inside:avoid"><td>'+(k+1)+'</td><td>'+esc(x.q)+'</td>'+phs.map(p=>{const v=S[p][id];return '<td style="text-align:center;font-weight:900;color:'+(v?'#16a34a':'#dc2626')+'">'+(v==null?'–':v?'✓':'✗')+'</td><td>'+iaPill(iaP(x[p]))+'</td>'}).join('')+'</tr>'}).join('');
 return '<div class="rcard v"><h2>🧪 Item Analysis</h2><p style="color:var(--mute);margin:0 0 6px">✓ = this student got it right, ✗ = wrong or blank. The level beside each mark shows how the whole section did on that question (Mastered '+IA_M+'%+, Nearly Mastered '+IA_N+'–'+(IA_M-1)+'%, Not Mastered below '+IA_N+'%).</p><table class="tt2" style="width:100%"><tr><th>#</th><th>Question</th>'+phs.map(p=>'<th>'+LB[p]+'</th><th>Section level</th>').join('')+'</tr>'+rows+'</table></div>'}
const iaWrap=(html,extra)=>extra?html.replace(/<\/div>\s*$/,extra+'</div>'):html;
function classRep(d,names,sec){
 const ok=names.filter(n=>d[n]&&Object.keys(d[n]).length),pre=ok.filter(n=>d[n].pre),post=ok.filter(n=>d[n].post),both=ok.filter(n=>d[n].pre&&d[n].post);
 if(!ok.length)return '';
 const T=Object.keys((d[ok[0]].post||d[ok[0]].pre).per),avg=a=>a.length?Math.round(a.reduce((x,y)=>x+y,0)/a.length):null,fm=v=>v==null?'–':v+'%';
 const hp=post.length>0,ph=hp?'post':'pre',lat=n=>d[n].post||d[n].pre;
 const tp=p=>{const o={};T.forEach(t=>{let c=0,m=0;ok.forEach(n=>{const r=d[n][p];if(r){c+=r.per[t][0];m+=r.per[t][1]}});o[t]=m?Math.round(100*c/m):null});return o};
 const TP=tp('pre'),TQ=tp('post'),TL=ph=='post'?TQ:TP;
 const mp=avg(pre.map(n=>d[n].pre.pct)),mq=avg(post.map(n=>d[n].post.pct)),mb=avg(both.map(n=>d[n].post.pct-d[n].pre.pct));
 const band=p=>p>=85?0:p>=70?1:p>=50?2:3,BL=['🏅 Mastered (85%+)','✅ Proficient (70–84%)','🌱 Developing (50–69%)','🆘 Needs support (below 50%)'],BC=['#10b981','#06b6d4','#f59e0b','#ef4444'];
 const dist=(arr,get)=>{const o=[0,0,0,0];arr.forEach(n=>o[band(get(n))]++);return o},DP=dist(pre,n=>d[n].pre.pct),DQ=dist(post,n=>d[n].post.pct);
 const S=T.filter(t=>TL[t]!=null&&TL[t]>=75),W=T.filter(t=>TL[t]!=null&&TL[t]<50);
 const E={};ok.forEach(n=>{const e=errAgg(lat(n));Object.keys(e).forEach(k=>{const x=E[k]||(E[k]={n:0,t:[]});x.n+=e[k].n;e[k].t.forEach(t=>{if(x.t.indexOf(t)<0)x.t.push(t)})})});
 const weakest=n=>{const L=lat(n);return T.slice().sort((a,b)=>pcT(L.per,a)-pcT(L.per,b))[0]};
 const support=ok.filter(n=>lat(n).pct<50).sort((a,b)=>lat(a).pct-lat(b).pct).slice(0,10),grew=both.filter(n=>d[n].post.pct>d[n].pre.pct).sort((a,b)=>(d[b].post.pct-d[b].pre.pct)-(d[a].post.pct-d[a].pre.pct)).slice(0,5);
 const reteach=T.filter(t=>TL[t]!=null&&TL[t]<60).sort((a,b)=>TL[a]-TL[b]);
 const missing=names.filter(n=>!ok.includes(n));
 const dh=(a,N)=>BL.map((l,i)=>'<div class="rrow" style="grid-template-columns:minmax(150px,1.6fr) 3fr auto"><div>'+l+'</div><div class="rbar"><i style="width:'+(N?Math.max(a[i]?100*a[i]/N:0,a[i]?3:0):0)+'%;background:'+BC[i]+'"></i></div><div>'+a[i]+'</div></div>').join('');
 let h='<div class="rep pop"><div class="big" style="padding:clamp(18px,3vw,34px)"><div class="em" style="font-size:clamp(50px,9vw,80px)">🏫</div><h1>Class Report</h1><p><b>'+esc(sec)+'</b> · '+new Date().toLocaleDateString()+'</p><div class="score"><div><b>'+pre.length+'/'+names.length+'</b><small>Took pre-test</small></div>'+(hp?'<div><b>'+post.length+'/'+names.length+'</b><small>Took post-test</small></div>':'')+'<div><b>'+fm(mp)+'</b><small>Pre-test average</small></div>'+(hp?'<div style="background:linear-gradient(135deg,#f59e0b,#ef4444)"><b>'+fm(mq)+'</b><small>Post-test average</small></div>':'')+(mb!=null?'<div style="background:linear-gradient(135deg,'+(mb>=0?'#10b981,#84cc16':'#ef4444,#f97316')+')"><b>'+(mb>=0?'+':'')+mb+'</b><small>Avg gain ('+both.length+' took both)</small></div>':'')+'</div></div>';
 h+='<div class="two"><div class="rcard g"><h2>💪 Class strengths</h2>'+chipT(S,'g',t=>TL[t])+'<p style="color:var(--mute);margin:8px 0 0">Topics at 75% or more ('+(ph=='post'?'post-test':'pre-test')+').</p></div><div class="rcard r"><h2>🎯 Class weaknesses</h2>'+chipT(W,'r',t=>TL[t])+'<p style="color:var(--mute);margin:8px 0 0">Topics below 50%.</p></div></div>';
 h+='<div class="rcard v"><h2>📊 Class average by topic</h2>'+T.map(t=>{const a=TP[t],b=TQ[t],x=b!=null?b:a,c=a!=null&&b!=null?b-a:null;return '<div class="rrow2"><div>'+(TEM[t]||'')+' '+esc(t)+'</div><div>'+(a!=null?'<div class="rbar" style="margin-bottom:4px"><i style="width:'+Math.max(a,2)+'%;background:'+colT(a)+';opacity:.55"></i></div>':'')+(b!=null?'<div class="rbar"><i style="width:'+Math.max(b,2)+'%;background:'+colT(b)+'"></i></div>':'')+'</div><div style="text-align:right">'+fm(a)+(b!=null?' → <b>'+b+'%</b>':'')+(c!=null?'<br><span style="color:'+(c>=0?'#059669':'#dc2626')+'">'+(c>=0?'+':'')+c+'</span>':'')+'</div></div>'}).join('')+'<p style="color:var(--mute);margin:8px 0 0">Faded bar = pre-test, solid bar = post-test.</p></div>';
 h+='<div class="two"><div class="rcard v"><h2>👥 Pre-test levels</h2>'+dh(DP,pre.length)+'</div>'+(hp?'<div class="rcard v"><h2>👥 Post-test levels</h2>'+dh(DQ,post.length)+'</div>':'')+'</div>';
 h+='<div class="rcard y"><h2>🔎 Most common mistakes</h2>'+errHtml(E,4)+'</div>';
 h+='<div class="rcard r"><h2>🧑‍🏫 What to re-teach</h2>'+(reteach.length?reteach.map((t,i)=>'<div class="rtip"><b>'+(i+1)+'. '+(TEM[t]||'')+' '+esc(t)+' ('+TL[t]+'%)</b> · '+(TTIP[t]||'')+'</div>').join(''):'<div class="rtip">🏆 No topic is below 60%. Move on to harder problems.</div>')+'</div>';
 h+='<div class="two"><div class="rcard y"><h2>🆘 Students who need support</h2>'+(support.length?support.map(n=>'<div class="rtip"><b>'+esc(n)+'</b> · '+lat(n).pct+'% · weakest: '+(TEM[weakest(n)]||'')+' '+esc(weakest(n))+'</div>').join(''):'<div class="rtip">Nobody is below 50%. 🎉</div>')+'</div>'+(hp?'<div class="rcard g"><h2>📈 Most improved</h2>'+(grew.length?grew.map(n=>'<div class="rtip"><b>'+esc(n)+'</b> · '+d[n].pre.pct+'% → '+d[n].post.pct+'% (+'+(d[n].post.pct-d[n].pre.pct)+')</div>').join(''):'<div class="rtip">No post-test gains to show yet.</div>')+'</div>':'')+'</div>';
 h+='<div class="rcard v"><h2>📋 All students</h2><table class="tt2"><tr><th>Student</th><th>Pre</th>'+(hp?'<th>Post</th><th>Change</th>':'')+'<th>Weakest topic</th></tr>'+ok.slice().sort((a,b)=>lat(b).pct-lat(a).pct).map(n=>{const c=d[n].pre&&d[n].post?d[n].post.pct-d[n].pre.pct:null;return '<tr><td>'+esc(n)+'</td><td>'+(d[n].pre?d[n].pre.pct+'%':'–')+'</td>'+(hp?'<td>'+(d[n].post?d[n].post.pct+'%':'–')+'</td><td style="color:'+(c==null?'inherit':c>=0?'#059669':'#dc2626')+'">'+(c==null?'–':(c>=0?'+':'')+c)+'</td>':'')+'<td>'+(TEM[weakest(n)]||'')+' '+esc(weakest(n))+'</td></tr>'}).join('')+'</table>'+(missing.length?'<p style="color:var(--mute)">Not yet tested: '+missing.map(esc).join(', ')+'</p>':'')+'</div></div>';
 return h}
async function openRep(one,mode){const d=await J('/api/t/reports?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec)),IA=await J('/api/t/items?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec));const all=Object.keys(d),got=n=>d[n]&&Object.keys(d[n]).length,names=(one?[one]:all).filter(got);
 if(!names.length){alert('No submitted tests to show yet.');return}
 let o=$('ov');if(!o){o=document.createElement('div');o.id='ov';document.body.appendChild(o)}
 o.style.cssText='position:fixed;inset:0;z-index:80;background:var(--bg);overflow:auto;padding:16px';
 const pg=x=>'<div class="rpage" style="max-width:1200px;margin:0 auto 20px">'+x+'</div>';
 let body='';if(one)body=pg(iaWrap(reportT(d[one],one,secLab()),iaStu(IA,one)));else{body=pg(iaWrap(classRep(d,all,secLab()),iaCard(IA)));if(mode!='class')body+=names.map(n=>pg(iaWrap(reportT(d[n],n,secLab()),iaStu(IA,n)))).join('')}
 o.innerHTML='<div class="noprint" style="max-width:1200px;margin:0 auto 12px;display:flex;gap:8px;justify-content:flex-end"><button class="p" onclick="window.print()">📄 Save as PDF · A4 portrait'+(one?'':mode=='class'?' (class report)':' ('+(names.length+1)+' pages)')+'</button><button onclick="dlRep(\'class-and-student-reports\')">⬇ Download PDF</button><button onclick="closeRep()">✕ Close</button></div>'+body;document.body.classList.add('pr')}
/*PDFJS*/
function dlRep(kind){const o=$('ov');if(!o)return;const L={'class-and-student-reports':'Class and student reports','item-analysis':'Item analysis','answer-sheets':'Answer sheets','growth-report':'Growth report','test-report':'Pre-test and Post-test report'};
 pdfSave('/api/pdf',{key:K,title:L[kind]||'Report',sub:secLab()+' · '+new Date().toLocaleDateString(),cols:[],w:[],rows:pdfRows(o)},'gnhs-'+kind+'-'+(RSEC||sec).replace(/[^A-Za-z0-9]+/g,'-')+'-'+new Date().toISOString().slice(0,10)+'.pdf')}
function closeRep(){RSEC='';const o=$('ov');if(o)o.remove();document.body.classList.remove('pr')}
async function openItems(){const IA=await J('/api/t/items?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec)),it=IA&&IA.items?IA.items:[];
 if(!it.length){alert('No submitted tests to show yet.');return}
 const hasPre=it.some(x=>x.pre[1]),hasPost=it.some(x=>x.post[1]),ph=hasPost?'post':'pre',LB={pre:'Pre-test',post:'Post-test'};
 const rk=it.filter(x=>x[ph][1]).map(x=>({x:x,p:iaP(x[ph]),n:it.indexOf(x)+1})).sort((a,b)=>a.p-b.p||a.n-b.n);
 const both=hasPre&&hasPost,row=(r,i)=>'<tr style="break-inside:avoid"><td>'+(i+1)+'</td><td style="text-align:left"><b>'+esc(r.x.q)+'</b><br><small style="color:var(--mute)">Answer: '+esc(r.x.a)+' · '+esc((TEM[r.x.t]||'')+' '+r.x.t)+' · Q'+r.n+'</small></td><td><b>'+r.p+'%</b><br><small>('+r.x[ph][0]+'/'+r.x[ph][1]+')</small></td>'+(both?'<td>'+(r.x.pre[1]?iaP(r.x.pre)+'%':'–')+'</td><td>'+(r.x.pre[1]&&r.x.post[1]?(()=>{const d=iaP(r.x.post)-iaP(r.x.pre);return '<b style="color:'+(d>0?'#16a34a':d<0?'#dc2626':'inherit')+'">'+(d>0?'+':'')+d+'</b>'})():'–')+'</td>':'')+'<td>'+iaPill(r.p)+'</td></tr>';
 const tbl=(L,off)=>'<table class="tt2" style="width:100%"><tr><th>#</th><th style="text-align:left">Question</th><th>'+(both?'Post %':'% correct')+'</th>'+(both?'<th>Pre %</th><th>Change</th>':'')+'<th>Level</th></tr>'+L.map((r,i)=>row(r,i+off)).join('')+'</table>';
 const k=Math.min(5,Math.ceil(rk.length/2)),hard=rk.slice(0,k),easy=rk.slice(-k).reverse();
 let o=$('ov');if(!o){o=document.createElement('div');o.id='ov';document.body.appendChild(o)}
 o.style.cssText='position:fixed;inset:0;z-index:80;background:var(--bg);overflow:auto;padding:16px';
 o.innerHTML='<div class="noprint" style="max-width:794px;margin:0 auto 12px;display:flex;gap:8px;justify-content:flex-end"><button class="p" onclick="window.print()">📄 Save as PDF · A4 portrait</button><button onclick="dlRep(\'item-analysis\')">⬇ Download PDF</button><button onclick="closeRep()">✕ Close</button></div><div class="rpage"><div class="rep"><div class="big"><h1>Item Analysis</h1><p><b>'+esc(secLab())+'</b> · '+LB[ph]+' · '+new Date().toLocaleDateString()+'</p></div>'
 +'<div class="rcard r"><h2>🔴 Hardest questions (re-teach these)</h2>'+tbl(hard,0)+'</div><div class="rcard g"><h2>🏅 Easiest questions</h2>'+tbl(easy,0)+'</div>'
 +'<div class="rcard v"><h2>All questions ranked: hardest to easiest ('+LB[ph]+')</h2>'+tbl(rk,0)+'</div>'+iaCard(IA)+'</div></div>';document.body.classList.add('pr')}
function itemsHtml(IA){const it=IA&&IA.items?IA.items:[];if(!it.length)return '';
 const hasPre=it.some(x=>x.pre[1]),hasPost=it.some(x=>x.post[1]),ph=hasPost?'post':'pre',LB={pre:'Pre-test',post:'Post-test'};
 const rk=it.filter(x=>x[ph][1]).map(x=>({x:x,p:iaP(x[ph]),n:it.indexOf(x)+1})).sort((a,b)=>a.p-b.p||a.n-b.n);
 const both=hasPre&&hasPost,row=(r,i)=>'<tr style="break-inside:avoid"><td>'+(i+1)+'</td><td style="text-align:left"><b>'+esc(r.x.q)+'</b><br><small style="color:var(--mute)">Answer: '+esc(r.x.a)+' · '+esc((TEM[r.x.t]||'')+' '+r.x.t)+' · Q'+r.n+'</small></td><td><b>'+r.p+'%</b><br><small>('+r.x[ph][0]+'/'+r.x[ph][1]+')</small></td>'+(both?'<td>'+(r.x.pre[1]?iaP(r.x.pre)+'%':'–')+'</td><td>'+(r.x.pre[1]&&r.x.post[1]?(()=>{const d=iaP(r.x.post)-iaP(r.x.pre);return '<b style="color:'+(d>0?'#16a34a':d<0?'#dc2626':'inherit')+'">'+(d>0?'+':'')+d+'</b>'})():'–')+'</td>':'')+'<td>'+iaPill(r.p)+'</td></tr>';
 const tbl=(L,off)=>'<table class="tt2" style="width:100%"><tr><th>#</th><th style="text-align:left">Question</th><th>'+(both?'Post %':'% correct')+'</th>'+(both?'<th>Pre %</th><th>Change</th>':'')+'<th>Level</th></tr>'+L.map((r,i)=>row(r,i+off)).join('')+'</table>';
 const k=Math.min(5,Math.ceil(rk.length/2)),hard=rk.slice(0,k),easy=rk.slice(-k).reverse();
 return '<div class="rpage"><div class="rep"><div class="big"><h1>Item Analysis</h1><p><b>'+esc(secLab())+'</b> · '+LB[ph]+' · '+new Date().toLocaleDateString()+'</p></div>'
 +'<div class="rcard r"><h2>🔴 Hardest questions (re-teach these)</h2>'+tbl(hard,0)+'</div><div class="rcard g"><h2>🏅 Easiest questions</h2>'+tbl(easy,0)+'</div>'
 +'<div class="rcard v"><h2>All questions ranked: hardest to easiest ('+LB[ph]+')</h2>'+tbl(rk,0)+'</div>'+iaCard(IA)+'</div></div>'}
function phaseIA(IA,ph){const o=ph=='pre'?'post':'pre';return {items:(IA&&IA.items||[]).filter(x=>x[ph][1]).map(x=>{const y=Object.assign({},x);y[o]=[0,0];return y}),stu:IA&&IA.stu}}
function itemsCmp(IA){const all=IA&&IA.items?IA.items:[],it=all.filter(x=>x.pre[1]&&x.post[1]);if(!it.length)return '';
 const d=x=>iaP(x.post)-iaP(x.pre),n=x=>all.indexOf(x)+1,col=v=>v>0?'#16a34a':v<0?'#dc2626':'inherit',sg=v=>(v>0?'+':'')+v;
 const up=it.filter(x=>d(x)>=5).length,dn=it.filter(x=>d(x)<=-5).length,same=it.length-up-dn,c0=iaCount(it,'pre'),c1=iaCount(it,'post');
 const row=x=>'<tr style="break-inside:avoid"><td>'+n(x)+'</td><td style="text-align:left"><b>'+esc(x.q)+'</b><br><small style="color:var(--mute)">Answer: '+esc(x.a)+' · '+esc((TEM[x.t]||'')+' '+x.t)+'</small></td><td>'+iaP(x.pre)+'%<br><small>('+x.pre[0]+'/'+x.pre[1]+')</small></td><td>'+iaP(x.post)+'%<br><small>('+x.post[0]+'/'+x.post[1]+')</small></td><td><b style="color:'+col(d(x))+'">'+sg(d(x))+'</b></td><td>'+iaPill(iaP(x.pre))+' → '+iaPill(iaP(x.post))+'</td></tr>';
 const tbl=L=>'<table class="tt2" style="width:100%"><tr><th>#</th><th style="text-align:left">Question</th><th>Pre %</th><th>Post %</th><th>Change</th><th>Level (pre → post)</th></tr>'+L.map(row).join('')+'</table>';
 const byD=it.slice().sort((a,b)=>d(b)-d(a)||n(a)-n(b)),k=Math.min(5,Math.ceil(it.length/2)),best=byD.slice(0,k).filter(x=>d(x)>0),worst=byD.slice().reverse().slice(0,k).filter(x=>d(x)<=0);
 return '<div class="rpage"><div class="rep"><div class="big"><h1>Item Analysis · Pre-test vs Post-test</h1><p><b>'+esc(secLab())+'</b> · '+new Date().toLocaleDateString()+'</p></div>'
 +'<div class="rcard v"><h2>Summary</h2><p style="margin:4px 0">'+it.length+' questions were in both tests: <b style="color:#16a34a">'+up+' improved</b> (+5 points or more) · <b>'+same+' about the same</b> · <b style="color:#dc2626">'+dn+' declined</b> (−5 points or more).</p>'
 +[0,1,2].map(i=>'<p style="margin:2px 0">'+IA_L[i]+': pre '+c0[i]+' → post '+c1[i]+'</p>').join('')+'</div>'
 +(best.length?'<div class="rcard g"><h2>🏅 Biggest gains</h2>'+tbl(best)+'</div>':'')
 +(worst.length?'<div class="rcard r"><h2>🔴 No gain or dropped (re-teach these)</h2>'+tbl(worst)+'</div>':'')
 +'<div class="rcard v"><h2>All questions: pre vs post (in test order)</h2>'+tbl(it)+'</div></div></div>'}
async function openStoredRep(name){
 const r=await fetch('/api/t/rfile?key='+encodeURIComponent(K)+'&name='+encodeURIComponent(name)+'&ext=full');
 if(!r.ok){alert('That report is not saved yet. Press 💾 Save report on the dashboard first.');return}
 showFullRep(await r.json())}
function repKind(n){const m=/__(ALL|PRE|POST|COMPARE)-report$/.exec(n||'');return m?m[1]:'ALL'}
async function openFullRep(){const r=await fetch('/api/t/fullnow?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec));if(!r.ok){alert('Could not build the report.');return}showFullRep(await r.json())}
function fullParts(F){
 const KD=F.kind||'ALL',d=F.reports||{},IA=F.items||{},SH=F.sheets||{},sm=F.summary,all=Object.keys(d),names=all.filter(n=>d[n]&&Object.keys(d[n]).length);
 if(!names.length)return null;
 const pg=x=>'<div class="rpage" style="max-width:1200px;margin:0 auto 20px">'+x+'</div>',L=secLab(),M=v=>v==null?'–':v+'%',ph1=(lb,s)=>'<p style="margin:4px 0"><b>'+lb+':</b> '+(s.started?s.taken+' of '+sm.total+' took it · class mean <b>'+M(s.mean)+'</b>':'not started yet')+'</p>'+(s.absent.length?'<p style="margin:2px 0 6px;color:#b45309">Absent / not taken ('+s.absent.length+'): '+s.absent.map(esc).join(', ')+'</p>':'');
 const hasG=!!(F.growth&&F.growth.sum&&F.growth.sum.pairs);
 const head=pg('<div class="rcard v"><h2>'+(({PRE:'📝 Pre-test report',POST:'📝 Post-test report',COMPARE:'📊 Pre vs Post comparison'})[KD]||'📝 Pre-test and Post-test report')+' · '+esc(F.test)+'</h2><p style="margin:4px 0">'+esc(L)+' · stored '+esc(F.updated.slice(0,16))+'</p>'+(KD=='PRE'||KD=='COMPARE'||(KD=='ALL'&&(sm.pre.taken||!sm.post.taken))?ph1('Pre-test',sm.pre):'')+(KD=='POST'||KD=='COMPARE'||(KD=='ALL'&&sm.post.taken)?ph1('Post-test',sm.post):'')
  +(KD!='PRE'&&KD!='POST'&&sm.gain!=null?'<p style="margin:4px 0"><b>Average gain:</b> '+(sm.gain>=0?'+':'')+sm.gain+' points ('+sm.both+' students took both)</p>':'')
  +'<p style="margin:6px 0 0;color:var(--mute)">This report has: class report · item analysis · each student’s report'+(KD=='COMPARE'?'':' · answer sheets')+(hasG?' · growth report':'')+'.</p></div>');
 const cls=pg(iaWrap(classRep(d,all,L),iaCard(IA)));
 const iPre=itemsHtml(phaseIA(IA,'pre')),iPost=itemsHtml(phaseIA(IA,'post')),iCmp=itemsCmp(IA),items=KD=='PRE'?iPre:KD=='POST'?iPost:KD=='COMPARE'?iCmp:iPre+iPost+iCmp;
 const students=names.map(n=>pg(iaWrap(reportT(d[n],n,L),iaStu(IA,n)))).join('');
 const sh=names.filter(n=>SH[n]).map(n=>['pre','post'].filter(p=>SH[n][p]).map(p=>shPage(n,SH[n],p)).join('')).join('');
 let growth='';if(hasG){const old=rep;rep=F.growth;try{growth=pg('<p style="margin:0 0 8px;color:var(--mute);font-weight:700">Growth report · '+esc(L)+'</p>'+repHtml())}finally{rep=old}}
 return {head,cls,items,iPre,iPost,iCmp,students,sheets:sh?SHCSS+sh:'',growth}}
function showFullRep(F){
 const P=fullParts(F);if(!P){alert('No submitted tests to show yet.');return}
 RSEC=F.section;
 let o=$('ov');if(!o){o=document.createElement('div');o.id='ov';document.body.appendChild(o)}
 o.style.cssText='position:fixed;inset:0;z-index:80;background:var(--bg);overflow:auto;padding:16px';
 o.innerHTML='<div class="noprint" style="max-width:1200px;margin:0 auto 12px;display:flex;gap:8px;justify-content:flex-end"><button class="p" onclick="window.print()">📄 Save as PDF · A4 portrait</button><button onclick="dlRep(\'test-report\')">⬇ Download PDF</button><button onclick="closeRep()">✕ Close</button></div>'+P.head+P.cls+P.items+P.students+P.sheets+P.growth;document.body.classList.add('pr')}
async function saveReport(){
 const b=$('psave');if(b){b.disabled=true;b.textContent='Saving…'}
 try{
  const r=await J('/api/t/hostact',{a:'savereport',sec});if(r.msg!=='ok'){alert(r.msg||'Could not save the report.');return}
  let fails=0,saved=[];
  const host=document.createElement('div');host.style.cssText='position:fixed;left:-99999px;top:0;width:1200px';document.body.appendChild(host);
  try{for(const rk of ['PRE','POST','COMPARE']){
   const fr=await fetch('/api/t/fullnow?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec)+'&kind='+rk),F=fr.ok?await fr.json():null,P=F&&F.reports?fullParts(F):null;
   if(!P)continue;saved.push({PRE:'Pre-test',POST:'Post-test',COMPARE:'Comparison'}[rk]);
   const sub=secLab()+' · '+F.test+' · '+new Date().toLocaleDateString(),lst=rk=='PRE'?[['class','Class report: Pre-test',P.head+P.cls],['items_pre','Item analysis: Pre-test',P.iPre],['students','Individual student reports: Pre-test',P.students]]:rk=='POST'?[['class','Class report: Post-test',P.head+P.cls],['items_post','Item analysis: Post-test',P.iPost],['students','Individual student reports: Post-test',P.students]]:[['class','Comparison: class report',P.head+P.cls+P.growth],['items_cmp','Item analysis: Pre vs Post comparison',P.iCmp],['students','Comparison: individual student reports',P.students]];
   for(const [kind,title,html] of lst){
    if(!html)continue;host.innerHTML=html;
    const x=await fetch('/api/t/savepdf',{method:'POST',body:JSON.stringify({key:K,sec,rk,kind,title,sub,cols:[],w:[],rows:pdfRows(host)})});if(!x.ok)fails++}}}
  finally{host.remove()}
  alert((fails?'Saved, but '+fails+' PDF file(s) could not be made.\n':'Saved. ')+(saved.length?saved.join(', ')+' report'+(saved.length>1?'s are':' is')+' now in Stored reports.':''));
 }finally{if(b){b.disabled=false;b.textContent='💾 Save report'}LAST='';await poll()}}
function rp(b){openRep(b.dataset.n)}
const SHCSS='<style>.shp{background:#fff;color:#1e1b3a;border:1px solid #e4defa;border-radius:12px;padding:14px 16px;font-size:11px}.shh{display:flex;justify-content:space-between;align-items:center;gap:12px;border-bottom:2px solid #7c3aed;padding-bottom:8px;margin-bottom:8px}.shh h1{font-size:18px;margin:0}.shh p{margin:2px 0 0;font-size:12px}.shs{text-align:center;background:linear-gradient(135deg,#7c3aed,#ec4899);color:#fff;border-radius:12px;padding:6px 16px;-webkit-print-color-adjust:exact;print-color-adjust:exact}.shs b{font-size:22px;display:block}.shs small{font-size:11px}.sht{width:100%;border-collapse:collapse;margin-top:8px;table-layout:fixed}.sht th{text-align:left;background:#eee9ff;padding:4px 6px;font-size:10px;-webkit-print-color-adjust:exact;print-color-adjust:exact}.sht td{padding:3px 6px;border-bottom:1px solid #eee;vertical-align:top;overflow-wrap:anywhere}.sht tr{break-inside:avoid}.sht tr.g td{background:#ddd2fd;font-weight:800;color:#5b21b6;-webkit-print-color-adjust:exact;print-color-adjust:exact}.sht td.y{color:#16a34a;font-weight:900;text-align:center}.sht td.n{color:#dc2626;font-weight:900;text-align:center}.shf{margin-top:8px;font-size:11px;color:#6f6a94}@media print{.shp{border:0;padding:0}}</style>';
function shPage(n,o,ph){const x=o[ph],lab=ph=='pre'?'Pre-test':'Post-test',tp={};
 x.rows.forEach(r=>{const a=tp[r.t]||(tp[r.t]=[0,0]);a[1]++;if(r.ok)a[0]++});
 let cur=null;const rows=x.rows.map((r,k)=>{let g='';if(r.t!=cur){cur=r.t;g='<tr class="g"><td colspan="5">'+esc((TEM[r.t]||'')+' '+r.t)+' · '+tp[r.t][0]+'/'+tp[r.t][1]+'</td></tr>'}
  return g+'<tr><td>'+(k+1)+'</td><td>'+esc(r.q)+'</td><td>'+(r.v?esc(r.v):'<i style="color:#9ca3af">blank</i>')+'</td><td>'+esc(r.a)+'</td><td class="'+(r.ok?'y':'n')+'">'+(r.ok?'✓':'✗')+'</td></tr>'}).join('');
 const sm=['pre','post'].filter(p=>o[p]).map(p=>(p=='pre'?'Pre-test ':'Post-test ')+o[p].c+'/'+o[p].n+' ('+o[p].pct+'%)').join(' · ');
 return '<div class="rpage shp"><div class="shh"><div><h1>Answer sheet · '+lab+'</h1><p><b>'+esc(n)+'</b> · '+esc(secLab())+' · '+new Date().toLocaleDateString()+'</p></div><div class="shs"><b>'+x.c+'/'+x.n+'</b><small>'+x.pct+'%</small></div></div><table class="sht"><colgroup><col style="width:6%"><col style="width:48%"><col style="width:18%"><col style="width:20%"><col style="width:8%"></colgroup><thead><tr><th>#</th><th>Question</th><th>Student’s answer</th><th>Correct answer</th><th>Mark</th></tr></thead><tbody>'+rows+'</tbody></table><p class="shf">Scores: '+sm+'. ✓ = correct, ✗ = wrong or blank.</p></div>'}
async function openSheets(one){const d=await J('/api/t/sheets?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec)),names=(one?[one]:Object.keys(d)).filter(n=>d[n]);
 if(!names.length){alert('No submitted tests to show yet.');return}
 let pg=0;const body=names.map(n=>['pre','post'].filter(p=>d[n][p]).map(p=>{pg++;return shPage(n,d[n],p)}).join('')).join('');
 let o=$('ov');if(!o){o=document.createElement('div');o.id='ov';document.body.appendChild(o)}
 o.style.cssText='position:fixed;inset:0;z-index:80;background:var(--bg);overflow:auto;padding:16px';
 o.innerHTML=SHCSS+'<div class="noprint" style="max-width:794px;margin:0 auto 12px;display:flex;gap:8px;justify-content:flex-end"><button class="p" onclick="window.print()">📄 Save as PDF · A4 portrait ('+pg+' page'+(pg==1?'':'s')+')</button><button onclick="dlRep(\'answer-sheets\')">⬇ Download PDF</button><button onclick="closeRep()">✕ Close</button></div>'+body;document.body.classList.add('pr')}
function pz(a,b){act({a,name:b.dataset.n})}
function sh1(b){openSheets(b.dataset.n)}

const K=new URLSearchParams(location.search).get('key');try{sessionStorage.mk=K}catch(e){}let S=null,sec=localStorage.hsec||'',rep=null,showRep=false,RSEC='';
const J=async(p,d)=>(await fetch(p,d?{method:'POST',body:JSON.stringify(Object.assign({key:K},d))}:{})).json();
const act=async d=>{await J('/api/t/hostact',Object.assign({sec},d));await poll()};
async function poll(){S=await J('/api/t/hstate?key='+encodeURIComponent(K));if(!S.secs[sec])sec=Object.keys(S.secs)[0];if(showRep)rep=await J('/api/t/report?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec));if(document.activeElement&&(document.activeElement.id=='s'||document.activeElement.id=='bpname'||document.activeElement.id=='bwsec'||document.activeElement.id=='bwpick'||document.activeElement.id=='tset'||document.activeElement.id=='setnm'))return;draw()}
let CVS='',BPN=null,CV=null,CVO=false,CVF='A',CVA=false,Q='',LAST='',BPD=null,SO=false,OP={bp:false,cp:false,lib:false};
function fold(k,html){const i=html.indexOf('<div class="d-ch">'),j=html.indexOf('</div>',i)+6,e=html.lastIndexOf('</section>'),o=!!OP[k];
 return html.slice(0,i)+html.slice(i,j).replace(/<h2>[\s\S]*?<\/h2>/,m=>'<button class="d-fold" data-k="'+k+'" aria-expanded="'+o+'" title="'+(o?'Collapse':'Expand')+'"><span class="d-chev">▾</span>'+m+'</button>')+(o?html.slice(j,e):'')+'</section>'}
const STG_HINT={off:"Tests are closed, so students can't start. Open the pre-test when the class is ready.",pre:"The pre-test is open. Switch to Closed when everyone has finished, then run your drills.",post:"The post-test is open. Release results once everyone has finished."};
const STG3=['off','pre','post'];
const dBand=p=>p>=75?'g':p>=50?'y':'r',dIni=n=>{const w=n.trim().split(/\s+/);return ((w[0]||'')[0]||'')+(w.length>1?w[w.length-1][0]:'')},dHue=n=>{let h=0;for(const ch of n)h=(h*31+ch.charCodeAt(0))%360;return h};
function scoreCell(c,ph,n){const p=c[ph].pct[n];
 if(p!=null)return '<span class="d-pill fin">✓ Finished</span>';
 return c[ph].inprog.includes(n)?(c.paused.includes(n)?'<span class="d-pill" style="background:#fef3c7;color:#92400e">⏸ Paused</span>':'<span class="d-pill live"><i></i>In progress</span>'):'<span class="d-none">Not started</span>'}
function rowsHtml(c){const q=Q.trim().toLowerCase(),L=c.names.filter(n=>!q||n.toLowerCase().includes(q));
 if(!L.length)return `<tr><td colspan="4" class="d-empty">${c.names.length?'No student matches “'+esc(Q)+'”. Check the spelling.':'No students in this section yet.'}</td></tr>`;
 return L.map(n=>{const a=c.pre.pct[n],b=c.post.pct[n],has=a!=null||b!=null,en=esc(n),live=c.pre.inprog.includes(n)||c.post.inprog.includes(n),pb=c.paused.includes(n)?`<button class="d-btn pri sm" title="Let this student continue" onclick="pz('resume',this)" data-n="${en}">▶ Continue</button>`:live?`<button class="d-btn soft sm" title="Stop this student's test for now" onclick="pz('pause',this)" data-n="${en}">⏸ Stop</button>`:'';
  const rb=ph=>c[ph].pct[n]!=null||c[ph].inprog.includes(n)?`<button class="d-btn ghost sm" title="Erase this student's ${ph}-test so they can retake it" onclick="rs('${ph}',this)" data-n="${en}">↺ ${ph=='pre'?'Pre':'Post'}</button>`:'';
  return `<tr><td><div class="d-name"><span class="d-av" style="--h:${dHue(n)}">${esc(dIni(n))}</span>${en}</div></td><td>${scoreCell(c,'pre',n)}</td><td>${scoreCell(c,'post',n)}</td><td class="d-act">${pb}<button class="d-btn soft sm" onclick="rp(this)" data-n="${en}"${has?'':' disabled title="Available after the student submits a test"'}>📋 Report</button><button class="d-btn soft sm" onclick="sh1(this)" data-n="${en}"${has?'':' disabled title="Available after the student submits a test"'}>🧾 Sheet</button>${rb('pre')}${rb('post')}</td></tr>`}).join('')}
function ringCard(c,ph,label,c1,c2){const p=c[ph],v=Object.values(p.pct).filter(x=>x!=null),avg=v.length?Math.round(v.reduce((x,y)=>x+y,0)/v.length):null,share=c.total?Math.round(100*p.done/c.total):0;
 return `<section class="d-card d-prog" style="--c1:${c1};--c2:${c2}"><div class="d-ring" style="--p:${share}"><b>${p.done}<small>/${c.total}</small></b></div><div class="d-pinfo"><h2>${label}</h2><p>${c.total&&p.done==c.total?'Everyone has submitted':p.done+' of '+c.total+' submitted'}</p><div class="d-tags">${ph=='post'?'<button class="d-btn sm" id="tupp" title="Load the saved pre-test copy so the post-test uses exactly the same blueprint and questions">⬆ Upload test copy</button>':''}${p.prog?`<span class="d-pill live"><i></i>${p.prog} in progress</span>`:''}</div></div></section>`}
const isPer=()=>S.mode=='per',cb=()=>isPer()?S.secs[sec].bp:null,bpCur=()=>{const b=cb();return b?{t:b.topics.slice(),c:Object.assign({},b.counts)}:{t:S.topics.slice(),c:Object.assign({},S.counts)}},NOPT=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20];
function secLab(){if(RSEC)return RSEC;const c=S&&S.secs&&S.secs[sec];return sec+(c&&c.sets&&c.sets.multi?' · '+c.sets.active:'')}
function tsetSel(c){return '';return `<label class="d-sel"><span>Test for this section (e.g. one per topic)</span><select id="tset">${c.sets.list.map(x=>`<option value="${esc(x.name)}"${x.active?' selected':''}>${esc(x.name)} · ${x.total} items · pre ${x.pre}/${c.total}, post ${x.post}/${c.total}</option>`).join('')}</select></label>`}
function setsBlock(){const c=S.secs[sec],L=c.sets.list,d=BPD||bpCur();
 return `<h3 class="d-sub">Saved blueprints</h3><div class="d-scroll"><table class="d-table"><thead><tr><th>Test</th><th>Topics</th><th>Pre done</th><th>Post done</th><th></th></tr></thead><tbody>`+L.map(x=>`<tr><td><b>${esc(x.name)}</b>${x.active?' <span class="d-pill live"><i></i>Active</span>':''}</td><td>${x.topics.map(t=>esc(t)+' ×'+x.counts[t]).join(', ')} = ${x.total}</td><td>${x.pre}/${c.total}</td><td>${x.post}/${c.total}</td><td class="d-act">${x.active?'':`<button class="d-btn soft sm" onclick="setUse(this.dataset.n)" data-n="${esc(x.name)}">Use this test</button>`}<button class="d-btn ghost sm" onclick="setRen(this.dataset.n)" data-n="${esc(x.name)}">✏ Rename</button>${x.active?'':`<button class="d-btn ghost sm" title="Delete this test and its results" onclick="setDel(this.dataset.n)" data-n="${esc(x.name)}">🗑</button>`}</td></tr>`).join('')+`</tbody></table></div>`}
async function setUse(n){const r=await J('/api/t/hostact',{a:'setuse',sec,name:n});if(r.msg)alert(r.msg);BPD=null;BPN=null;CV=null;LAST='';await poll()}
async function setRen(n){const v=prompt('New name for this test:',n);if(!v)return;const r=await J('/api/t/hostact',{a:'setren',sec,old:n,name:v});if(r.msg)alert(r.msg);LAST='';await poll()}
async function setDel(n){if(!confirm('Delete the test "'+n+'" and all its pre-test and post-test results for this section? This cannot be undone.'))return;const pw=prompt('Enter the delete password to confirm:');if(pw==null||pw==='')return;const r=await J('/api/t/hostact',{a:'setdel',sec,name:n,pw});if(r.msg)alert(r.msg);LAST='';await poll()}
function modeBlock(){const lk=S.mlocked,p=isPer(),b=cb();
 let h=`<div class="d-bpr" style="margin:8px 0;gap:8px"><button class="d-btn ${p?'':'pri'}" ${lk?'disabled':''} onclick="bpMode('same')" aria-pressed="${!p}">Same for all sections</button><button class="d-btn ${p?'pri':''}" ${lk?'disabled':''} onclick="bpMode('per')" aria-pressed="${p}">Individual per section</button>${lk?'<span class="d-none">Locked: reset the students’ tests first to change this.</span>':''}</div>`;
 if(!p)return h;
 const o=Object.keys(S.secs).filter(x=>x!=sec);
 h+=`<p class="d-note" style="margin:6px 0">Blueprint for <b>${esc(sec)}</b>: ${b.own?'its own blueprint':'uses the all-sections blueprint'}. Change the topics below and save to give this section its own pre-test blueprint, or copy another section’s blueprint (the questions are still generated separately for each section).</p>
<div class="d-bpr"><label class="d-bpn">Same blueprint as <select id="bpsrc" ${b.locked?'disabled':''}><option value="">choose…</option>${b.own?'<option value="all">All-sections blueprint</option>':''}${o.map(x=>`<option value="${esc(x)}">${esc(x)}</option>`).join('')}</select></label></div>
`;
 return h+setsBlock()}
async function bpMode(v){if(v==(isPer()?'per':'same'))return;const r=await J('/api/t/hostact',{a:'bpmode',v});if(r.msg)alert(r.msg);BPD=null;LAST='';await poll()}
async function bpUse(src){const r=await J('/api/t/hostact',{a:'bpuse','for':sec,src});if(r.msg)alert(r.msg);BPD=null;LAST='';await poll()}
let BW={ph:'pre',name:'',t:[],c:{},pick:''};
function bwList(){const c=S.secs[sec];return c&&c.sets?c.sets.list:[]}
function bwPick(){const L=bwList();if(BW.pick&&L.some(x=>x.name==BW.pick))return BW.pick;const a=L.find(x=>x.active);return a?a.name:(L[0]?L[0].name:'')}
function bwPh(p){BW.ph=p;draw()}
function bwTog(b){const t=b.dataset.t;BW.t=BW.t.includes(t)?BW.t.filter(x=>x!=t):S.all.filter(x=>BW.t.includes(x)||x==t);if(BW.c[t]==null)BW.c[t]=4;draw()}
async function bwSave(){const nm=(BW.name||'').trim();if(!nm||!BW.t.length)return;
 if(!confirm('Save the blueprint "'+nm+'" for '+sec+'?\n\nIt becomes the test students of this section take. A second, identical copy is saved for the post-test. The test the section used before is kept in the list and can be switched back to.'))return;
 const r=await J('/api/t/hostact',{a:'bpsave',sec,name:nm,topics:BW.t,counts:Object.fromEntries(BW.t.map(t=>[t,BW.c[t]||4]))});
 if(!r.msg||r.msg.slice(0,3)!='ok:'){alert(r.msg||'Could not save the blueprint.');await poll();return}
 const f=r.msg.slice(3);BW={ph:'pre',name:'',t:[],c:{},pick:''};CV=null;LAST='';alert('Saved for '+sec+':\n'+f+'-PRE.json\n'+f+'-POST.json (identical copy for the post-test)');await poll()}
function bpCard(){const post=BW.ph=='post',L=bwList(),pk=post?L.find(x=>x.name==bwPick()):null,t=post?(pk?pk.topics:[]):BW.t,cn=x=>post?((pk&&pk.counts[x])||0):(BW.c[x]||4),tot=t.reduce((a,x)=>a+cn(x),0),nm=post?bwPick():(BW.name||'').trim(),lk=S.mode!='per'&&S.mlocked,ok=!post&&!lk&&nm&&t.length,fn=nm||'(file name)';
 return `<section class="d-card d-bp"><div class="d-ch"><h2>Test blueprint<small>${esc(sec)}</small></h2></div>
<div class="d-bpg">
<div class="d-bpf"><div class="d-stp"><i>1</i>Section</div><select id="bwsec" aria-label="Section">${Object.keys(S.secs).map(x=>`<option${x==sec?' selected':''}>${esc(x)}</option>`).join('')}</select></div>
<div class="d-bpf"><div class="d-stp"><i>2</i>File name</div>${post?`<select id="bwpick" aria-label="Saved blueprint">${L.map(x=>`<option${x.name==nm?' selected':''}>${esc(x.name)}</option>`).join('')}</select>`:`<input id="bpname" maxlength="60" placeholder="e.g. Q1-Numeracy" value="${esc(BW.name)}" aria-label="File name">`}</div>
<div class="d-bpf"><div class="d-stp"><i>3</i>Test</div><div class="d-seg"><button class="d-btn ${post?'':'pri'}" onclick="bwPh('pre')" aria-pressed="${!post}">Pre-test</button><button class="d-btn ${post?'pri':''}" onclick="bwPh('post')" aria-pressed="${post}">Post-test</button></div></div>
</div>
<div class="d-stp"><i>4</i>Topics</div><div class="d-chips">${S.all.map(x=>`<button class="d-chip ${t.includes(x)?'on':''}" ${post?'disabled':''} aria-pressed="${t.includes(x)}" onclick="bwTog(this)" data-t="${esc(x)}"><i>${t.includes(x)?'✓':''}</i>${esc((TEM[x]||'')+' '+x)}</button>`).join('')}</div>
<div class="d-stp"><i>5</i>Items for each topic<span class="d-tot">${t.length} topic${t.length==1?'':'s'} · ${tot} items per test</span></div>
${t.length?`<div class="d-bpr" style="gap:10px 12px">${t.map(x=>`<label class="d-bpn">${esc((TEM[x]||'')+' '+x)} <select class="bpc" data-t="${esc(x)}" ${post?'disabled':''}>${NOPT.map(n=>`<option${n==cn(x)?' selected':''}>${n}</option>`).join('')}</select></label>`).join('')}</div>`:''}
<div class="d-bpbar">${post?`<button class="d-btn pri" id="bwdl" ${nm?'':'disabled'}>⬇ Download ${esc(fn)}-POST.json</button>`:`<button class="d-btn pri" id="bps" ${ok?'':'disabled'}>💾 Save as blueprint</button>`}<button class="d-btn" id="tdl" title="Saves the PRE-test copy (blueprint, questions and answer key) as a file">⬇ PRE copy</button><button class="d-btn" id="tup" ${S.locked?'disabled title="Locked: students have already started a test"':'title="Load a saved test copy so the pre-test and post-test use exactly those questions"'}>⬆ Upload copy</button><input type="file" id="bpf" accept=".json,application/json" hidden><button class="d-btn" id="tpp" title="One A4 PDF: the test paper for the selected section's grade band, followed by the answer key on its own page(s). Print only the first pages for students.">🖨 Paper + key (PDF)</button></div>
${lk?'<p class="d-note" style="margin:8px 0 0">Locked: students have started a test. Reset their tests first.</p>':''}
${setsBlock()}</section>`}
function repBtns(e){const L=(S.reports||[]).filter(x=>String(x.test).split('~')[0]==e.name);
 if(!L.length)return `<button class="d-btn ghost sm" style="opacity:.6" data-m="No saved report yet. Press 💾 Save report on the dashboard after the students have taken the test." onclick="alert(this.dataset.m)">📊 Report</button>`;
 return L.map(x=>{const k=x.kind||'ALL',lb={PRE:'Pre-test',POST:'Post-test',COMPARE:'Comparison',ALL:'Report'}[k];return `<button class="d-btn soft sm" title="Open the stored ${lb.toLowerCase()} report${L.length>3?' of '+esc(x.sec):''} (pre ${x.pre.taken} of ${x.total}, post ${x.post.taken} of ${x.total} took it)" data-n="${esc(x.name)}" onclick="openStoredRep(this.dataset.n)">📊 ${lb}${L.length>3?' · '+esc(x.sec):''}</button>`}).join('')}
function cpk(e,k,cur){const en=esc(e.name),ok=(e.files||[]).includes(k),lb=k=='PRE'?'Pre-test':'Post-test';
 if(!ok)return '<span class="d-pill" style="background:#fee2e2;color:#991b1b">✗ Missing</span>';
 return '<span class="d-pill fin">✓ '+lb+'</span> '+(cur?'':'<button class="d-btn soft sm" onclick="loadcopy(this.dataset.n,this.dataset.k)" data-n="'+en+'" data-k="'+k+'">Load</button> ')+'<button class="d-btn ghost sm" title="Download '+en+'-'+k+'.json" onclick="dlcopy(this.dataset.n,this.dataset.k)" data-n="'+en+'" data-k="'+k+'">⬇</button>'}
function libCard(){const L=S.copies||[];
 let h='<section class="d-card d-lib"><div class="d-ch"><h2>Saved test copies<small>'+L.length+'</small></h2></div>';
 if(!L.length)return h+'<p class="d-note">No copies yet. Each blueprint you save appears here. Use Load to make it the current test.</p></section>';
 h+='<table class="d-table"><thead><tr><th>Name</th><th>Blueprint</th><th>Saved</th><th>Pre-test</th><th>Post-test</th><th></th></tr></thead><tbody>'+L.map(e=>{const cur=e.name==S.name,en=esc(e.name);
  return '<tr><td><b>'+en+'</b>'+(cur?' <span class="d-pill live"><i></i>In use</span>':'')+'</td><td>'+(e.sec?'<b>'+esc(e.sec)+'</b>: ':'')+(e.topics.length?e.topics.map(t=>esc(t)+' ×'+(e.counts[t]||0)).join(', ')+' = '+e.total+' items'+(e.mode=='per'?' (+ individual section blueprints)':''):'-')+'</td><td>'+esc(e.saved)+'</td><td>'+cpk(e,'PRE',cur)+'</td><td>'+cpk(e,'POST',cur)+'</td><td class="d-act"><button class="d-btn ghost sm" title="Delete this saved copy (testing only)" onclick="delcopy(this.dataset.n)" data-n="'+en+'">🗑 Delete</button></td></tr>'}).join('')+'</tbody></table><p class="d-note">The PRE and POST files are in the <b>gnhs-test-copies</b> folder next to numeracy.py. Reports are in Stored reports below.</p></section>';
 return h}
function rptCard(){const L=S.reports||[];
 const M=v=>v==null?'-':v+'%',ab=(lb,s)=>s.started&&s.absent.length?'<br><small title="'+esc(s.absent.join(', '))+'">'+s.absent.length+' absent ('+lb+')</small>':'';
 const PN={class:'Class report (with growth report)',items_pre:'Item analysis: Pre-test',items_post:'Item analysis: Post-test',items_cmp:'Item analysis: Pre vs Post comparison',scores:'Scores per student',students:'Individual student reports',sheets:'Answer sheets'},PL={class:'Class',items_pre:'Items Pre',items_post:'Items Post',items_cmp:'Items Compare',scores:'Scores',students:'Students',sheets:'Sheets'};
 const row=e=>{const en=esc(e.name),k=e.kind||'ALL';
  const taken=k=='POST'?'Post '+(e.post.taken+'/'+e.total)+ab('post',e.post):k=='PRE'?'Pre '+(e.pre.started?e.pre.taken+'/'+e.total:'–')+ab('pre',e.pre):'Pre '+(e.pre.started?e.pre.taken+'/'+e.total:'–')+(e.post.taken?' · Post '+e.post.taken+'/'+e.total:'')+ab('pre',e.pre)+(e.post.taken?ab('post',e.post):'');
  const mean=k=='POST'?M(e.post.mean):k=='PRE'?M(e.pre.mean):M(e.pre.mean)+(e.post.taken?' → '+M(e.post.mean):'')+(e.gain!=null?'<br><small>'+(e.gain>=0?'+':'')+e.gain+' avg gain</small>':'');
  return '<tr><td><b>'+esc(e.test)+'</b></td><td>'+esc(e.sec)+'</td><td>'+taken+'</td><td>'+mean+'</td><td>'+esc(e.updated.slice(0,16))+'</td><td class="d-act"><button class="d-btn soft sm" onclick="openStoredRep(this.dataset.n)" data-n="'+en+'">📊 Open</button>'+(e.pdfs||[]).map(x=>'<button class="d-btn ghost sm" title="'+PN[x]+' · A4 PDF, locked" onclick="dlrep(this.dataset.n,\''+x+'\')" data-n="'+en+'">⬇ '+PL[x]+'</button>').join('')+['csv','json'].map(x=>'<button class="d-btn ghost sm" onclick="dlrep(this.dataset.n,\''+x+'\')" data-n="'+en+'">⬇ '+x.toUpperCase()+'</button>').join('')+'</td></tr>'};
 const CL={PRE:['#2563eb','#eff6ff','#bfdbfe'],POST:['#ea580c','#fff7ed','#fed7aa'],COMPARE:['#059669','#ecfdf5','#a7f3d0']};
 const part=(k,ico,ttl,note,empty)=>{const A=L.filter(e=>(e.kind||'ALL')==k),c=CL[k]||CL.PRE;
  return '<div style="margin:14px 0 6px;padding:12px 14px;border-radius:14px;border:1px solid '+c[2]+';border-left:6px solid '+c[0]+';background:linear-gradient(135deg,'+c[1]+',transparent 70%)"><h3 style="margin:0 0 2px;font-size:16px;color:'+c[0]+'">'+ico+' '+ttl+' <small style="background:'+c[0]+';color:#fff;border-radius:999px;padding:1px 9px;font-size:12px">'+A.length+'</small></h3><p class="d-note" style="margin:0 0 6px">'+note+'</p>'
   +(A.length?'<table class="d-table"><thead><tr><th>Test</th><th>Section</th><th>Taken</th><th>Mean</th><th>Updated</th><th></th></tr></thead><tbody>'+A.map(row).join('')+'</tbody></table>':'<p class="d-note" style="margin:0;padding:10px 12px;border-radius:10px;border:2px dashed '+c[0]+';background:'+c[1]+';color:'+c[0]+';font-weight:700">'+empty+'</p>')+'</div>'};
 let h='<section class="d-card d-lib"><div class="d-ch"><h2>Stored reports<small>'+L.length+'</small></h2></div>';
 h+=part('PRE','📝','Pre-test report','Saved once students have submitted the pre-test.','Not saved yet. It appears here after students submit the pre-test and you press 💾 Save report.');
 h+=part('POST','📝','Post-test report','Saved once students have submitted the post-test.','Not saved yet. It appears here after students submit the post-test and you press 💾 Save report.');
 h+=part('COMPARE','📊','Comparison (pre vs post)','Saved once at least one student has taken both tests.','Not saved yet. It appears here once a student has both a pre-test and a post-test.');
 return h+'<p class="d-note" style="margin-top:10px">Files are in the <b>gnhs-test-reports</b> folder next to numeracy.py, as locked A4 PDFs plus CSV and JSON. Absent students are listed as "Absent (not taken)".</p></section>'}
async function dlrep(name,ext){const r=await fetch('/api/t/rfile?key='+encodeURIComponent(K)+'&name='+encodeURIComponent(name)+'&ext='+ext);if(!r.ok){alert('That report was not found.');return}const b=await r.blob(),a=document.createElement('a');a.href=URL.createObjectURL(b);a.download=name+'.'+ext+(['csv','json','full'].includes(ext)?'':'.pdf');document.body.appendChild(a);a.click();a.remove()}
function copyCard(c){const k=S.copy;
 if(!k)return '<section class="d-card"><div class="d-ch"><h2>Post-test copy<small>Not saved yet</small></h2></div><p class="d-note">Save the blueprint or open the pre-test and an identical copy of the test will appear here, ready for the post-test.</p></section>';
 const st=c.stage=='post'?['d-pill live','<i></i>Post-test open']:c.post.done?['d-pill fin','✓ Post-test taken']:['d-pill" style="background:#fef3c7;color:#92400e','⏳ Pending'];
 let h='<section class="d-card d-cp"><div class="d-ch"><h2>Post-test copy<small>'+esc((k.name||'')+'-POST.json')+'</small></h2><span class="'+st[0]+'">'+st[1]+'</span></div>';
  const TS=(k.tests||[]).filter(x=>x.sec==sec);
 if((k.tests||[]).length){h+='<div class="d-scroll"><table class="d-table"><tr><th>Section</th><th>Test</th><th>Items</th></tr>'+k.tests.map(x=>'<tr><td>'+esc(x.sec)+'</td><td>'+esc(x.name)+(x.active?' <span class="d-pill live"><i></i>Active</span>':'')+'</td><td>'+x.n+'</td></tr>').join('')+'</table></div>'}
 if(TS.length&&CVO){h+='<label class="d-sel"><span>Preview test for '+esc(sec)+'</span><select id="cvs">'+TS.map(x=>'<option value="'+(x.active?'':esc(x.name))+'"'+((x.active?'':x.name)==CVS?' selected':'')+'>'+esc(x.name)+(x.active?' (active)':'')+'</option>').join('')+'</select></label>'}
 h+='<div class="d-bpr"><button class="d-btn" id="tdp" '+(k.name?'':'disabled')+'>⬇ Download POST copy</button>'+repBtns({name:k.name})+'<button class="d-btn" id="cvt">'+(CVO?'Hide questions':'👁 Preview questions')+'</button>'+(CVO?'<label class="d-none"><input type="checkbox" id="cva"'+(CVA?' checked':'')+'> Show answers</label>':'')+'</div>';
 if(CVO){if(!CV)h+='<p class="d-note">Loading…</p>';else if(CV.none)h+='<p class="d-note">No saved copy found.</p>';else{const L=CV[CVF]||[];let cur=null;h+='<div class="d-scroll"><table class="d-table"><tr><th>#</th><th>Question</th>'+(CVA?'<th>Answer</th>':'')+'</tr>'+L.map((it,i)=>{let r='';if(it.t!=cur){cur=it.t;r='<tr><td colspan="'+(CVA?3:2)+'"><b>'+esc((TEM[it.t]||'')+' '+it.t)+'</b></td></tr>'}return r+'<tr><td>'+(i+1)+'</td><td>'+esc(it.q)+'</td>'+(CVA?'<td>'+esc(String(it.a))+'</td>':'')+'</tr>'}).join('')+'</table></div><p class="d-note">Grade '+(CV.band=='9'?'9-10':'7-8')+' version (follows the selected section). Every student gets exactly these questions in the pre-test and the post-test; the live quiz shuffles the order for each student.</p>'}}
 return h+'</section>'}
async function cvload(){CV=await J('/api/t/copyview?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec)+'&set='+encodeURIComponent(CVS));draw()}
function cvf(b){CVF=b.dataset.f;draw()}
function bpTog(b){const d=BPD||bpCur(),t=b.dataset.t,c=Object.assign({},d.c);if(c[t]==null)c[t]=4;BPD={c,t:d.t.includes(t)?d.t.filter(x=>x!=t):S.all.filter(x=>d.t.includes(x)||x==t)};draw()}
function draw(){const c=S.secs[sec];
 const sig=JSON.stringify([S,rep,sec,Q,showRep,SO,OP,BPD,BPN,BW,CV,CVO,CVF,CVA]);if(sig===LAST&&$('s'))return;LAST=sig;
 const fq=document.activeElement&&document.activeElement.id=='q',cp=fq?document.activeElement.selectionStart:0,cs=STG3.includes(c.stage)?c.stage:'off';
 let h=`<div class="dh"><header class="d-hero"><div class="d-top"><div><h1>Pre-test / Post-test</h1><div class="d-join">Students join at <b>${esc(location.host)}/test</b></div></div><button class="d-btn glass" onclick="location.href='/host?key='+encodeURIComponent(K)">← Drill dashboard</button></div>
<label class="d-sel"><span>Class section</span><select id="s">${Object.keys(S.secs).map(x=>`<option${x==sec?' selected':''}>${esc(x)}</option>`).join('')}</select></label>${tsetSel(c)}
<div class="d-steps" role="group" aria-label="Test stage">${STG3.map(x=>`<button class="d-step ${x==cs?'on':''}"${x==cs?' aria-current="true"':''} onclick="act({a:'stage',v:'${x}'})">${esc(S.txt[x])}</button>`).join('')}</div><p class="d-hint">${STG_HINT[cs]}</p></header>`;
 h+=`<div class="d-grid">${ringCard(c,'pre','Pre-test','#7c3aed','#ec4899')}${ringCard(c,'post','Post-test','#06b6d4','#10b981')}<section class="d-card d-share"><label class="d-switch"><input type="checkbox" id="rl"${c.release?' checked':''}><span class="t"></span>Release results to students</label><div class="d-btns"><button class="d-btn pri" id="pfull" title="One report with everything: class report, item analysis, every student's report, answer sheets and the growth report (pre-test and post-test together)">📊 Report</button></div></section></div>`;
 h+=fold('bp',bpCard())+fold('lib',libCard())+fold('rpt',rptCard());
 h+=`<section class="d-card"><div class="d-ch"><button class="d-fold" id="sf" aria-expanded="${SO}" title="${SO?'Collapse':'Expand'} the student list"><span class="d-chev">▾</span><h2>Students<small>${c.names.length}</small></h2></button><div class="d-chr"><input id="q" class="d-find" type="search" placeholder="Find a student" aria-label="Find a student" value="${esc(Q)}" autocomplete="off"><button class="d-btn pri" id="psave" title="Store this report (pre-test and post-test together) in Stored reports. Press it again to update the stored copy.">💾 Save report</button></div></div>${SO||Q.trim()?`<table class="d-table"><thead><tr><th>Student</th><th>Pre-test</th><th>Post-test</th><th></th></tr></thead><tbody>${rowsHtml(c)}</tbody></table>`:`<p class="d-sum">${c.pre.done} finished pre-test, ${c.post.done} finished post-test${c.pre.prog+c.post.prog?', '+(c.pre.prog+c.post.prog)+' in progress':''}${c.paused.length?', '+c.paused.length+' paused':''}. Type a name above to find one student, or expand the list.</p>`}</section>`;
 h+=`<p class="d-foot">Each test has ${isPer()?c.bp.total:S.total} items (set per topic above), untimed, with no feedback during the test. Each student gets the same questions in the pre-test and the post-test, in a shuffled order.</p>`;
 if(showRep&&rep)h+=repHtml();
 $('app').innerHTML=h+'</div>';
 $('s').onchange=e=>{sec=e.target.value;localStorage.hsec=sec;BPD=null;CVS='';e.target.blur();CV=null;if(CVO)cvload();if(showRep)poll();else draw()};
 if($('tset'))$('tset').onchange=async e=>{const r=await J('/api/t/hostact',{a:'setuse',sec,name:e.target.value});if(r.msg)alert(r.msg);BPD=null;BPN=null;CV=null;LAST='';e.target.blur();await poll()};if($('setadd'))$('setadd').onclick=async()=>{const nm=($('setnm').value||'').trim();if(!nm){alert('Type a name for the new test.');return}const d=BPD||bpCur(),r=await J('/api/t/hostact',{a:'setnew',sec,name:nm,topics:d.t,counts:Object.fromEntries(d.t.map(t=>[t,d.c[t]||4]))});if(r.msg){alert(r.msg);await poll();return}BPD=null;BPN=null;CV=null;LAST='';await poll()};
 if($('tdp'))$('tdp').onclick=()=>dlcopy(S.copy.name,'POST');if($('cvt'))$('cvt').onclick=()=>{CVO=!CVO;if(CVO&&!CV)cvload();else draw()};if($('cva'))$('cva').onchange=e=>{CVA=e.target.checked;draw()};if($('cvs'))$('cvs').onchange=e=>{CVS=e.target.value;CV=null;cvload()};if($('tdl'))$('tdl').onclick=tdl;if($('tupp'))$('tupp').onclick=()=>{$('bpf').value='';$('bpf').click()};if($('tpp'))$('tpp').onclick=tpdf;if($('tup'))$('tup').onclick=()=>{$('bpf').value='';$('bpf').click()};if($('bpf'))$('bpf').onchange=e=>tup(e.target.files[0]);document.querySelectorAll('.bpc').forEach(el=>el.onchange=e=>{BW.c[e.target.dataset.t]=+e.target.value;draw()});if($('bwsec'))$('bwsec').onchange=e=>{sec=e.target.value;localStorage.hsec=sec;BW.pick='';CVS='';e.target.blur();CV=null;if(CVO)cvload();if(showRep)poll();else draw()};if($('bwpick'))$('bwpick').onchange=e=>{BW.pick=e.target.value;e.target.blur();draw()};if($('bpname'))$('bpname').oninput=e=>{BW.name=e.target.value;if($('bps'))$('bps').disabled=!(BW.name.trim()&&BW.t.length)};if($('bwdl'))$('bwdl').onclick=()=>dlcopy(bwPick(),'POST');if($('bps'))$('bps').onclick=bwSave;
 $('sf').onclick=()=>{SO=!SO;draw()};document.querySelectorAll('.d-fold[data-k]').forEach(b=>b.onclick=()=>{OP[b.dataset.k]=!OP[b.dataset.k];draw()});$('q').oninput=e=>{Q=e.target.value;draw()};
 $('rl').onchange=e=>act({a:'release',v:e.target.checked});$('pfull').onclick=openFullRep;$('psave').onclick=saveReport;
 if(fq){const e=$('q');e.focus();e.setSelectionRange(cp,cp)}}
async function dlcopy(name,kind){const r=await fetch('/api/t/copyfile?key='+encodeURIComponent(K)+'&name='+encodeURIComponent(name)+'&kind='+kind);if(!r.ok){alert('That copy file was not found.');return}const b=await r.blob(),a=document.createElement('a');a.href=URL.createObjectURL(b);a.download=name+'-'+kind+'.json';document.body.appendChild(a);a.click();a.remove();await poll()}
async function tdl(){await poll();if(!S.name){alert('Save the blueprint first so the test has a name.');return}dlcopy(S.name,'PRE')}
async function delcopy(name){if(!confirm('Delete the saved test copy "'+name+'" (PRE and POST files)? This cannot be undone.'))return;const pw=prompt('Enter the delete password to confirm:');if(pw==null||pw==='')return;const r=await J('/api/t/hostact',{a:'delcopy',name,pw});if(r.msg!=='ok'){alert(r.msg||'Could not delete it.');return}CV=null;CVO=false;BPD=null;BPN=null;LAST='';await poll()}
async function loadcopy(name,kind){if(!confirm('Make "'+name+'" the current test? Students will get these questions.'))return;const r=await J('/api/t/hostact',{a:'loadcopy',name,kind});alert(r.msg==='ok'?'Loaded "'+name+'".':(r.msg||'Could not load it.'));BPD=null;BPN=null;LAST='';await poll()}
async function tpdf(){const r=await fetch('/api/t/paper?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec));if(!r.ok){alert('Could not make the PDF.');return}const x=document.createElement('a');x.href=URL.createObjectURL(await r.blob());x.download=(S.name||'gnhs-test')+'-paper-and-key-'+sec.replace(/[^A-Za-z0-9]+/g,'_')+'.pdf';document.body.appendChild(x);x.click();x.remove()}
async function tup(f){if(!f)return;let o;try{o=JSON.parse(await f.text())}catch(e){alert('That file is not a test copy.');return}const r=await J('/api/t/hostact',{a:'import',data:o});alert(r.msg==='ok'?'Test copy loaded. Students will get exactly these questions.':(r.msg||'Could not load that file.'));BPD=null;LAST='';await poll()}
async function openGrowth(){const r=await J('/api/t/report?key='+encodeURIComponent(K)+'&sec='+encodeURIComponent(sec)),old=rep;rep=r;const body=repHtml();rep=old;
 let o=$('ov');if(!o){o=document.createElement('div');o.id='ov';document.body.appendChild(o)}
 o.style.cssText='position:fixed;inset:0;z-index:80;background:var(--bg);overflow:auto;padding:16px';
 o.innerHTML='<div class="noprint" style="max-width:794px;margin:0 auto 12px;display:flex;gap:8px;justify-content:flex-end"><button class="p" onclick="window.print()">📄 Save as PDF · A4 portrait</button><button onclick="dlRep(\'growth-report\')">⬇ Download PDF</button><button onclick="closeRep()">✕ Close</button></div><div class="rpage"><p style="margin:0 0 8px;color:var(--mute);font-weight:700">'+esc(secLab())+' · '+new Date().toLocaleDateString()+'</p>'+body+'</div>';document.body.classList.add('pr')}
function rs(ph,b){const n=b.dataset.n;if(confirm('Erase '+n+"'s "+ph+'-test so they can retake it?'))act({a:'reset',ph,name:n})}
function repHtml(){const R=rep,s=R.sum,f=x=>x==null?'–':x,st=s.stats,tile=(v,l,c)=>`<div class="d-tile"><b class="${c||''}">${v}</b><small>${l}</small></div>`;
 let h='<section class="d-card d-grow"><div class="d-ch"><h2>📈 Growth report</h2></div>';
 if(!s.pairs)return h+'<p class="d-note">No student has finished both tests yet. This report fills in after a student submits the pre-test and the post-test.</p></section>';
 h+='<div class="d-tiles">'+tile(s.pairs,'took both')+tile(s.mean_pre+'%','pre-test mean')+tile(s.mean_post+'%','post-test mean')+tile(st?(st.mean>=0?'+':'')+st.mean.toFixed(1)+' pts':'–','mean gain',st&&st.mean>=0?'pos':'neg')+tile(f(s.class_g),'class normalised gain g')+'</div>';
 if(st&&st.p!=null)h+='<p class="d-note">Paired t('+st.df+') = '+st.t.toFixed(2)+', p '+(st.p<.001?'< .001':'= '+st.p.toFixed(3))+', effect size d<sub>z</sub> = '+st.dz.toFixed(2)+' (0.2 small, 0.5 medium, 0.8 large). With one section the sample is small and there is no comparison group, so read this as evidence of improvement, not proof the drills caused it. Normalised gain g (Hake 1998): below 0.3 low, 0.3–0.7 medium, above 0.7 high; those bands come from physics classes, so treat them as rough.</p>';
 h+='<h3>By topic (students who took both)</h3><div class="d-scroll"><table class="d-table"><tr><th>Topic</th><th>Pre</th><th>Post</th><th>Change</th></tr>'+Object.keys(s.topics).map(t=>{const d=s.topics[t][1]-s.topics[t][0];return '<tr><td>'+esc(t)+'</td><td>'+s.topics[t][0]+'%</td><td>'+s.topics[t][1]+'%</td><td class="'+(d>=0?'pos':'neg')+'">'+(d>=0?'+':'')+d+'</td></tr>'}).join('')+'</table></div>';
 h+='<h3>By student</h3><div class="d-scroll"><table class="d-table"><tr><th>Student</th><th>Pre</th><th>Post</th><th>Gain</th><th>g</th><th title="Drill attempts made after the pre-test">Drill attempts</th><th>Forms</th></tr>'+R.rows.map(r=>'<tr><td>'+esc(r.n)+'</td><td>'+f(r.pre)+'</td><td>'+(r.post==null?'':r.post)+'</td><td class="'+(r.gain==null?'':r.gain>=0?'pos':'neg')+'">'+(r.gain==null?'':(r.gain>=0?'+':'')+r.gain)+'</td><td>'+(r.g==null?'':r.g)+'</td><td>'+f(r.dose)+'</td><td>'+r.form+'</td></tr>').join('')+'</table></div></section>';return h}
poll();setInterval(poll,3000);
</script></body></html>"""

PDFJS = r"""function pdfRows(root){const rows=[],T=s=>String(s==null?'':s).replace(/\s+/g,' ').trim();let mode='';
 const line=s=>{s=T(s);if(!s)return;if(mode!=='t'){rows.push({cols:[],w:[1]});mode='t'}rows.push([s])};
 const tbl=t=>{let head=[],body=[],n=0;
  t.querySelectorAll('tr').forEach(tr=>{const cs=[...tr.children];if(!cs.length)return;
   if(cs.every(c=>c.tagName==='TH')){if(!head.length)head=cs.map(c=>T(c.innerText));return}
   n=Math.max(n,cs.length);body.push(cs)});
  const k=head.length||n;if(!k)return;const rr=[],w=Array.from({length:k},(_,j)=>Math.max(4,String(head[j]||'').length));
  body.forEach(cs=>{if(cs.length===1&&k>1){rr.push(T(cs[0].innerText));return}
   const v=[];for(let j=0;j<k;j++)v.push(T(cs[j]?cs[j].innerText:''));v.forEach((x,j)=>{w[j]=Math.max(w[j],Math.min(40,x.length))});rr.push(v)});
  rows.push({cols:head,w:w});rr.forEach(x=>rows.push(x));mode='x'};
 const walk=e=>{if(e.nodeType===3){line(e.textContent);return}
  if(e.nodeType===1&&e.matches('.pbrk')){rows.push('\f');mode='';return}
  if(e.nodeType!==1||/^(STYLE|SCRIPT|COLGROUP|BR|BUTTON|INPUT|SELECT)$/.test(e.tagName)||e.matches('.noprint,.em,.bar,.prog'))return;
  const tg=e.tagName;
  if(tg==='TABLE'){tbl(e);return}
  if(/^H[1-3]$/.test(tg)){const s=T(e.innerText);if(s)rows.push(s);return}
  if(e.matches('.rrow,.rrow2')){const c=[...e.children];line(T(c[0]&&c[0].innerText)+': '+T(c.length>1&&c[c.length-1].innerText));return}
  if(e.matches('.score')){line([...e.children].map(c=>T(c.innerText)).join('  |  '));return}
  if(e.matches('.rtip,p,.d-tile,b,small')){line(e.innerText);return}
  let ch=[];const fl=()=>{if(ch.length){line(ch.join('; '));ch=[]}};
  e.childNodes.forEach(c=>{if(c.nodeType===1&&c.classList.contains('rc')){ch.push(T(c.innerText));return}fl();walk(c)});fl()};
 const pg=root.querySelectorAll('.rpage'),L=pg.length?[...pg]:[root];
 L.forEach((p,i)=>{if(i)rows.push('\f');mode='';walk(p)});return rows}
async function pdfSave(url,body,name){let r;try{r=await fetch(url,{method:'POST',body:JSON.stringify(body)})}catch(e){}
 if(!r||!r.ok){alert('Could not make the PDF. Check the connection and try again.');return}
 const a=document.createElement('a');a.href=URL.createObjectURL(await r.blob());a.download=name;document.body.appendChild(a);a.click();a.remove()}
"""
T_HOST = T_HOST.replace("/*PDFJS*/", PDFJS); T_STUDENT = T_STUDENT.replace("/*PDFJS*/", PDFJS)



# ======================= PRE-TEST / POST-TEST (same program, same port) =======================
# Cycle:  PRE-TEST (/test)  ->  all the drills / actions above (/)  ->  POST-TEST (/test).  Teacher dashboard: /test/host
# EVIDENCE-BASED TEST DESIGN
#   1. Identical forms: the post-test is a COPY of the pre-test (same topics, same questions); the live quiz shuffles the order for each student and for each test. Gain is measured on exactly the same questions.
#      Trade-off: students may remember questions, so treat gains with some caution.
#   2. ONE test for every student (per grade band). Only the live quiz order is shuffled per student and per test, to prevent copying.
#   3. Low stakes, no timer, no feedback during the test: removes time pressure (Ashcraft & Kirk 2001) so the score measures knowledge, not speed.
#   4. Gain reporting: raw change, Hake's normalised gain g = (post - pre) / (100 - pre) (Hake 1998), paired t-test and effect size (Cohen's dz), only over students who took BOTH tests.
#   5. Feeds the drill: pre-test results are the starting point for the drill's topic targeting (weak topics practised more).
#   6. Dose: the report shows each student's drill attempts between the two tests, so gain can be read against practice.
# Not a high-stakes instrument: items are generated, not psychometrically calibrated. Use results to guide teaching.
T_FILE = os.path.join(DATA_DIR, 'gnhs-tests.json')
T_DELETE_PW = '303457guad'   # password asked before a saved test copy can be deleted (checked on the server, never sent to the browser)
T_MAXN = 20          # most items one topic can have
T_ITEMS = 4          # default items per topic (each topic can now have its own number)
T_STAGES = ['off', 'pre', 'drill', 'post', 'done']
T_STAGE_TXT = {'off': 'Closed', 'pre': 'Pre-test open', 'drill': 'Drills', 'post': 'Post-test open', 'done': 'Finished'}
try: TD = json.load(open(T_FILE, encoding='utf-8'))
except Exception: TD = {}
for _k, _v in {'stage': {}, 'forms': {}, 'resp': {'pre': {}, 'post': {}}, 'release': {}, 'bps': {}, 'bpmode': 'same'}.items(): TD.setdefault(_k, _v)
_T_DIRTY = threading.Event()
TCLAIM = {}
TOPEN = {}      # (phase, student key) -> last time that student's test page was seen open (so "In progress" shows before the first answer)
TPAUSE = set()  # student keys whose test the teacher has stopped for now
T_BOOT = secrets.token_hex(8)   # new on every server start: a student page that remembers an older one is logged out
def t_save(): _T_DIRTY.set()
def t_per(): return TD.get('bpmode') == 'per'   # option: an individual pre-test blueprint for each section
def t_own(sec): return bool(sec) and t_per() and isinstance(TD.get('bps'), dict) and sec in TD['bps']   # this section has its OWN blueprint
def t_bp(sec=None):   # the test blueprint of a section (its own one, or the all-sections one), the same for the pre-test and the post-test
    b = (TD['bps'][sec] if t_own(sec) else TD.get('bp')) or {}; tp = [t for t in TOPICS if t in (b.get('topics') or TOPICS)] or list(TOPICS)
    c = b.get('counts') if isinstance(b.get('counts'), dict) else {}
    n0 = b.get('ipt') if isinstance(b.get('ipt'), int) and 1 <= b['ipt'] <= T_MAXN else T_ITEMS   # old saves had ONE number for every topic
    cnt = {}
    for t in tp:
        v = c.get(t); cnt[t] = v if isinstance(v, int) and not isinstance(v, bool) and 1 <= v <= T_MAXN else n0
    return tp, cnt   # topics in order, and the number of items for EACH topic
def t_total(cnt): return sum(cnt.values())
def t_bp_txt(tp, cnt): return ', '.join('%s x%d' % (t, cnt[t]) for t in tp)
def t_any_resp(): return any(TD['resp'][p] for p in ('pre', 'post'))
def t_bp_locked(sec=None):   # locked as soon as one student has started either test (per section when a section is named; the all-sections blueprint ignores sections with their own)
    if sec: return any(k.startswith(sec + '|') for p in ('pre', 'post') for k in TD['resp'][p])
    if t_per(): return any(k.startswith(s_ + '|') for s_ in ROSTER if not t_own(s_) for p in ('pre', 'post') for k in TD['resp'][p])
    return t_any_resp()
def t_secbp(sec): tp, cnt = t_bp(sec); return {'own': t_own(sec), 'topics': tp, 'counts': cnt, 'total': t_total(cnt), 'locked': t_bp_locked(sec) if t_per() else t_bp_locked()}
def t_fid(f, sec, glob=False): return f + t_band(sec) + ('@' + sec if not glob and t_own(sec) else '')   # form id: by grade band, or by section when it has its own blueprint
def t_write_now():
    try:
        with lock: data = json.dumps(TD, separators=(',', ':'), ensure_ascii=False)
        tmp = T_FILE + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f: f.write(data)
        os.replace(tmp, T_FILE)
    except Exception: pass
def _t_saver():
    while True: _T_DIRTY.wait(); time.sleep(2.0); _T_DIRTY.clear(); t_write_now()
threading.Thread(target=_t_saver, daemon=True).start(); atexit.register(t_write_now)

def t_band(sec): return '9' if re.match(r'Grade (9|10)\b', sec) else '7'   # 7 = Grade 7-8, 9 = Grade 9-10
def t_level(sec): return 8 if t_band(sec) == '9' else 4                   # mixed difficulty of that grade band
def t_form_of(key, phase):
    # ONE TEST FOR EVERYONE: every student gets Form A in the pre-test and again in the post-test (only the live order is shuffled).
    # A student who already started under the old A/B split keeps the form they started with, so their answers still match their questions.
    for ph in ('pre', 'post'):
        r = TD['resp'][ph].get(key)
        if r: return r['form'] if r.get('form') in ('A', 'B') else ('A', 'B')[zlib.crc32(key.encode('utf-8')) % 2]
    return 'A'
def t_get_form(f, sec, glob=False):
    fid = t_fid(f, sec, glob); own = not glob and t_own(sec)
    if fid in TD['forms']: return TD['forms'][fid]
    seen = set(x['q'] for x in TD['forms'].get(t_fid('B' if f == 'A' else 'A', sec, glob), []))
    items = []; tp, cnt = t_bp(None if glob else sec)
    for t in tp:
        for i in range(cnt[t]):
            for tries in range(60):
                q, a = gen_seeded(t, t_level(sec), zlib.crc32(('%s|%s|%s|%s|%d' % (f, t_band(sec) + ('@' + sec if own else ''), t, i, tries)).encode()))
                if q not in seen: break
            seen.add(q); items.append({'t': t, 'q': q, 'a': a})
    TD['forms'][fid] = items; t_save(); return items
def t_gen(form): return zlib.crc32('\n'.join(x['q'] for x in form).encode('utf-8'))   # fingerprint of a student's questions: it changes when the test is replaced
def t_order(key, phase, n):
    idx = list(range(n)); random.Random(zlib.crc32((key + phase).encode())).shuffle(idx); return idx   # shuffled per student AND per test: same questions, different order in the pre-test and the post-test
def t_grade(items, ans):
    per = {t: [0, 0] for t in TOPICS if any(x['t'] == t for x in items)}; err = {}
    for i, it in enumerate(items):
        per[it['t']][1] += 1; v = str(ans.get(str(i), '')).strip()
        if v and correct({'type': 'num', 'ans': it['a']}, v): per[it['t']][0] += 1
        else:
            tag = (diagnose(it['q'], it['a'], v) if v else 'blank') or 'other'; e = err.setdefault(it['t'], {}); e[tag] = e.get(tag, 0) + 1
    return {'per': per, 'c': sum(v[0] for v in per.values()), 'n': len(items), 'err': err}
def t_skill_res(sec, key, ph):
    # a finished test split by operation skill: ({skill: [correct, items]}, {skill: {mistake type: n}}); recomputed from the saved answers
    r = TD['resp'][ph].get(key); sk, er = {}, {}
    if not r or not r.get('done') or not r.get('res'): return sk, er
    try:
        items = t_get_form(t_form_of(key, ph), sec); ans = r.get('ans', {})
        for i, it in enumerate(items):
            s_ = skill_of(it['q'], it['t'])
            if not s_: continue
            v = str(ans.get(str(i), '')).strip(); good = bool(v) and bool(correct({'type': 'num', 'ans': it['a']}, v))
            x = sk.setdefault(s_, [0, 0]); x[1] += 1; x[0] += 1 if good else 0
            if not good: tag = (diagnose(it['q'], it['a'], v) if v else 'blank') or 'other'; e = er.setdefault(s_, {}); e[tag] = e.get(tag, 0) + 1
    except Exception: pass
    return sk, er
def t_skill_extra(sec, key, ph):
    sk, er = t_skill_res(sec, key, ph)
    return {'sk': sk, 'skerr': er, 'drill': {k: v['all'] for k, v in skills_of(key).items() if v['all'][1]}}
def t_pct(r): return None if not r or not r.get('res') else 100.0 * r['res']['c'] / max(1, r['res']['n'])
def _t_betacf(a, b, x):
    qab, qap, qam = a + b, a + 1, a - 1; c = 1.0; d = 1 - qab * x / qap; d = 1 / (d if abs(d) > 1e-30 else 1e-30); h = d
    for m in range(1, 200):
        m2 = 2 * m; aa = m * (b - m) * x / ((qam + m2) * (a + m2)); d = 1 + aa * d; c = 1 + aa / c
        d = 1 / (d if abs(d) > 1e-30 else 1e-30); c = c if abs(c) > 1e-30 else 1e-30; h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2)); d = 1 + aa * d; c = 1 + aa / c
        d = 1 / (d if abs(d) > 1e-30 else 1e-30); c = c if abs(c) > 1e-30 else 1e-30; de = d * c; h *= de
        if abs(de - 1) < 1e-10: break
    return h
def _t_betai(a, b, x):
    if x <= 0: return 0.0
    if x >= 1: return 1.0
    bt = math.exp(math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log(1 - x))
    return bt * _t_betacf(a, b, x) / a if x < (a + 1) / (a + b + 2) else 1 - bt * _t_betacf(b, a, 1 - x) / b
def t_paired(diffs):
    n = len(diffs)
    if n < 2: return None
    m = sum(diffs) / n; sd = math.sqrt(sum((d - m) ** 2 for d in diffs) / (n - 1))
    if sd == 0: return {'n': n, 'mean': m, 'sd': 0, 'dz': None, 't': None, 'df': n - 1, 'p': None}
    t = m / (sd / math.sqrt(n)); df = n - 1
    return {'n': n, 'mean': m, 'sd': sd, 'dz': m / sd, 't': t, 'df': df, 'p': _t_betai(df / 2.0, 0.5, df / (df + t * t))}

def t_report(sec):
    rows = []
    for name in ROSTER.get(sec, []):
        key = skey(sec, name); pre = TD['resp']['pre'].get(key); post = TD['resp']['post'].get(key)
        a, b = t_pct(pre), t_pct(post); gain = (b - a) if a is not None and b is not None else None
        ng = ((b - a) / (100 - a)) if gain is not None and a < 100 else None
        topics = {}
        for t in TOPICS:
            x = pre['res']['per'].get(t) if a is not None else None; y = post['res']['per'].get(t) if b is not None else None
            topics[t] = [None if not x else round(100.0 * x[0] / x[1]), None if not y else round(100.0 * y[0] / y[1])]
        dose = len(D['att'].get(key, {})) - pre['att0'] if pre and pre.get('att0') is not None else None   # drill attempts since the pre-test
        rows.append({'n': name, 'pre': None if a is None else round(a, 1), 'post': None if b is None else round(b, 1), 'gain': None if gain is None else round(gain, 1),
                     'g': None if ng is None else round(ng, 2), 'topics': topics, 'dose': dose, 'form': t_form_of(key, 'pre') + '→' + t_form_of(key, 'post')})
    pr = [r for r in rows if r['gain'] is not None]; S = {'pairs': len(pr)}
    if pr:
        mp = sum(r['pre'] for r in pr) / len(pr); mq = sum(r['post'] for r in pr) / len(pr)
        S.update(mean_pre=round(mp, 1), mean_post=round(mq, 1), class_g=None if mp >= 100 else round((mq - mp) / (100 - mp), 2), stats=t_paired([r['gain'] for r in pr]), topics={})
        for t in TOPICS:
            ps = [(r['topics'][t][0], r['topics'][t][1]) for r in pr if r['topics'][t][0] is not None and r['topics'][t][1] is not None]
            if ps: S['topics'][t] = [round(sum(x for x, _ in ps) / len(ps)), round(sum(y for _, y in ps) / len(ps))]
    return {'rows': rows, 'sum': S}

def t_student_view(sec, name):
    key = skey(sec, name); st = TD['stage'].get(sec, 'off'); phase = {'pre': 'pre', 'post': 'post'}.get(st)
    out = {'stage': st, 'stage_txt': T_STAGE_TXT[st], 'phase': phase, 'done': False, 'items': [], 'ans': {}, 'paused': False, 'released': bool(TD['release'].get(sec))}
    if phase:
        r = TD['resp'][phase].get(key) or {}; out['done'] = bool(r.get('done')); out['ans'] = r.get('ans', {})
        if not out['done']:
            TOPEN[(phase, key)] = time.time()
            form = t_get_form(t_form_of(key, phase), sec); out['gen'] = t_gen(form)
            if key in TPAUSE: out['paused'] = True   # stopped by the teacher: no questions are sent while paused
            else: out['items'] = [{'i': i, 'q': form[i]['q']} for i in t_order(key, phase, len(form))]
    if out['released']:
        res = {}
        for ph in ('pre', 'post'):
            r = TD['resp'][ph].get(key)
            if r and r.get('res'): res[ph] = dict({'pct': round(t_pct(r)), 'per': {t: [c, n] for t, (c, n) in r['res']['per'].items()}, 'err': r['res'].get('err', {})}, **t_skill_extra(sec, key, ph))
        out['result'] = res
    return out
def t_results(sec, name):
    key = skey(sec, name); res = {}
    for ph in ('pre', 'post'):
        r = TD['resp'][ph].get(key)
        if r and r.get('res'): res[ph] = dict({'pct': round(t_pct(r)), 'per': {t: [c, n] for t, (c, n) in r['res']['per'].items()}, 'err': r['res'].get('err', {})}, **t_skill_extra(sec, key, ph))
    return res
def t_claim_ok(sec, name, cid):
    c = TCLAIM.get((sec, name))
    if c and c[0] != cid and time.time() - c[1] < 120: return False
    TCLAIM[(sec, name)] = (cid, time.time()); return True

def t_student_post(sec, name, d, submit):
    key = skey(sec, name); ph = {'pre': 'pre', 'post': 'post'}.get(TD['stage'].get(sec, 'off'))
    if not ph or key in TPAUSE: return False
    r = TD['resp'][ph].setdefault(key, {'ans': {}, 'done': 0, 'form': t_form_of(key, ph)})   # the form is fixed when the student starts
    if r.get('done'): return False
    items = t_get_form(t_form_of(key, ph), sec)
    if not submit:
        i = str(d.get('i', ''))
        if i.isdigit() and int(i) < len(items): r['ans'][i] = str(d.get('v', ''))[:40]
    else:
        for i, v in (d.get('all') or {}).items():
            if str(i).isdigit() and int(i) < len(items): r['ans'][str(i)] = str(v)[:40]
        r['res'] = t_grade(items, r['ans']); r['done'] = time.time(); TOPEN.pop((ph, key), None)
        if ph == 'pre': r['att0'] = len(D['att'].get(key, {}))   # drill attempts so far = the starting point for "practice between the tests"
    t_save()
    return True
# ---- STORED REPORTS: THREE separate reports per test and section: PRE (pre-test), POST (post-test) and COMPARE (pre vs post) ----
# gnhs-test-reports/<test>__<section>__<PRE|POST|COMPARE>-report.(json|csv|full.json|*.pdf); the scores PDF is made from the JSON on download.
# Each one is written only when its data exists (PRE: someone submitted the pre-test, POST: the post-test, COMPARE: someone submitted both).
# Older combined ALL-report files are still listed and opened, but are no longer written.
# Written ONLY when the teacher presses "Save report" on the dashboard (action 'savereport', called with the lock held);
# pressing it again overwrites the stored report with the latest data. The student list always includes the ABSENT students (status "Absent (not taken)").
T_RDIR = os.path.join(DATA_DIR, 'gnhs-test-reports')
T_KINDS = ('PRE', 'POST', 'COMPARE')
T_RNAME = re.compile(r'^[A-Za-z0-9._\-]+__[A-Za-z0-9._\-]+__(?:ALL|PRE|POST|COMPARE)-report$')
def t_rsafe(x): return re.sub(r'[^A-Za-z0-9._\-]+', '-', str(x or '')).strip('.-')[:60] or 'x'
def t_rtest(sec):   # the name of the test this section is on (plus its set name when the section has several tests)
    S_ = (TD.get('sets') or {}).get(sec) or {}
    return t_name() + ('~' + str(S_['active']) if S_.get('items') and S_.get('active') else '')
def t_rbase(sec, kind='COMPARE'): return '%s__%s__%s-report' % (t_rsafe(t_rtest(sec)), t_rsafe(sec), kind)
T_KPH = {'PRE': ['pre'], 'POST': ['post'], 'COMPARE': ['pre', 'post'], 'ALL': None}   # the tests each kind of report covers
def t_phase_report(sec, ph):
    rows = []; topics = list(t_bp(sec)[0])
    for name in ROSTER.get(sec, []):
        key = skey(sec, name); r = TD['resp'][ph].get(key); done = bool(r and r.get('done') and r.get('res'))
        st = 'Submitted' if done else ('In progress' if r or (ph, key) in TOPEN else 'Absent (not taken)')
        row = {'n': name, 'status': st, 'c': None, 'items': None, 'pct': None, 'submitted': '', 'topics': {}, 'skills': {}}
        if done:
            try: when = time.strftime('%Y-%m-%d %H:%M', time.localtime(float(r['done'])))
            except Exception: when = ''
            row.update(c=r['res']['c'], items=r['res']['n'], pct=round(t_pct(r), 1), submitted=when)
            row['topics'] = {t: [c, n] for t, (c, n) in r['res']['per'].items()}
            row['skills'] = {k: list(v) for k, v in t_skill_res(sec, key, ph)[0].items()}
            for t in row['topics']:
                if t not in topics: topics.append(t)
        rows.append(row)
    got = [x for x in rows if x['pct'] is not None]
    tmean = {}
    for t in topics:
        ps = [x['topics'][t] for x in got if t in x['topics'] and x['topics'][t][1]]
        tmean[t] = round(100.0 * sum(a for a, _ in ps) / sum(b for _, b in ps), 1) if ps else None
    return {'test': t_rtest(sec), 'section': sec, 'phase': ph, 'updated': time.strftime('%Y-%m-%d %H:%M:%S'), 'topics': topics,
            'summary': {'total': len(rows), 'taken': len(got), 'absent': [x['n'] for x in rows if x['status'].startswith('Absent')],
                        'in_progress': [x['n'] for x in rows if x['status'] == 'In progress'],
                        'mean': round(sum(x['pct'] for x in got) / len(got), 1) if got else None, 'topic_mean': tmean},
            'rows': rows}
def t_all_report(sec, kind='ALL'):   # the pre-test and the post-test of ONE section side by side, one row per student (kind PRE / POST: just that test)
    P = {ph: t_phase_report(sec, ph) for ph in ('pre', 'post')}
    started = {ph: any(k.startswith(sec + '|') for k in TD['resp'][ph]) for ph in P}
    topics = list(P['pre']['topics'])
    for t in P['post']['topics']:
        if t not in topics: topics.append(t)
    rows = []; gains = []
    for a, b in zip(P['pre']['rows'], P['post']['rows']):
        pa = {k: v for k, v in a.items() if k != 'n'}; pb = {k: v for k, v in b.items() if k != 'n'}
        if not started['pre']: pa['status'] = 'Not started'
        if not started['post']: pb['status'] = 'Not started'
        g = round(b['pct'] - a['pct'], 1) if a['pct'] is not None and b['pct'] is not None else None
        if g is not None: gains.append(g)
        rows.append({'n': a['n'], 'pre': pa, 'post': pb, 'gain': g})
    sm = {'total': len(rows), 'both': len(gains), 'gain': round(sum(gains) / len(gains), 1) if gains else None}
    phases = list(T_KPH.get(kind) or []) or [ph for ph in ('pre', 'post') if P[ph]['summary']['taken']] or ['pre']   # ALL: only the tests somebody has actually submitted
    sm['phases'] = phases
    if len(phases) < 2:
        sm['gain'] = None
        for x in rows:
            x['gain'] = None
            for ph in ('pre', 'post'):
                if ph not in phases: x.pop(ph, None)
    for ph in P:
        s = dict(P[ph]['summary']); s['started'] = started[ph]
        if not started[ph]: s['absent'] = []
        if kind in T_KPH and T_KPH[kind] and ph not in T_KPH[kind]: s.update(started=False, taken=0, mean=None, absent=[], in_progress=[], topic_mean={})   # a PRE / POST report says nothing about the other test
        sm[ph] = s
    return {'test': P['pre']['test'], 'section': sec, 'kind': kind, 'updated': P['pre']['updated'], 'topics': topics, 'summary': sm, 'rows': rows}
def t_report_csv(rep):
    tp = rep['topics']; phs = rep['summary'].get('phases') or ['pre', 'post']; head = ['Test', 'Section', 'Student']
    for ph in phs: head += ['%s status' % ph.capitalize(), '%s submitted' % ph.capitalize(), '%s correct' % ph.capitalize(), '%s items' % ph.capitalize(), '%s %%' % ph.capitalize()]
    if len(phs) > 1: head += ['Gain (points)']
    head += sum([['%s %s %%' % (t, ph.capitalize()) for ph in phs] for t in tp], [])
    tpc = lambda x, t: None if t not in x['topics'] or not x['topics'][t][1] else round(100.0 * x['topics'][t][0] / x['topics'][t][1])
    L = [head]
    for x in rep['rows']:
        r = [rep['test'], rep['section'], x['n']]
        for ph in phs:
            y = x[ph]; r += [y['status'], y['submitted'], y['c'], y['items'], y['pct']]
        if len(phs) > 1: r.append(x['gain'])
        for t in tp: r += [tpc(x[ph], t) for ph in phs]
        L.append(r)
    cell = lambda v: ('"' + str(v).replace('"', '""') + '"') if re.search(r'[",\n]', str(v)) else ('' if v is None else str(v))
    return '\ufeff' + '\n'.join(','.join(cell(c) for c in row) for row in L)
def t_full_report(sec, kind='COMPARE'):   # everything the dashboard needs to redraw ONE report (PRE / POST / COMPARE) even when this test is no longer in use
    rep = t_all_report(sec, kind); phs = T_KPH.get(kind) or ['pre', 'post']
    R = {}
    for n in ROSTER.get(sec, []):
        r = t_results(sec, n); r = {ph: r[ph] for ph in phs if ph in r}
        if kind == 'COMPARE' and len(r) < 2: r = {}
        R[n] = r
    SH = {}
    for n, o in t_sheets(sec).items():
        o = {ph: o[ph] for ph in phs if ph in o}
        if o: SH[n] = o
    return {'test': rep['test'], 'section': sec, 'kind': kind, 'updated': rep['updated'], 'summary': rep['summary'],
            'reports': R, 'items': t_items(sec), 'sheets': SH, 'growth': t_report(sec) if kind in ('COMPARE', 'ALL') else None}
def t_kind_data(sec):   # which of the three reports have data right now
    def done(ph): return {n for n in ROSTER.get(sec, []) if (lambda r: bool(r and r.get('done') and r.get('res')))(TD['resp'][ph].get(skey(sec, n)))}
    a, b = done('pre'), done('post')
    return {'PRE': bool(a), 'POST': bool(b), 'COMPARE': bool(a & b)}

def t_sheets_pdf(sec, per_row=2, phases=('pre', 'post')):   # the answer sheets of a section: 4 students' sheets on each A4 portrait page (2 x 2), print-only locked PDF
    W, H, M, G, FOOT = 595.28, 841.89, 22.0, 10.0, 16.0
    cw, ch = (W - 2 * M - G) / 2, (H - 2 * M - FOOT - G) / 2
    S = t_sheets(sec); groups = [g for g in ([(n, ph, o[ph]) for n, o in S.items() if ph in o] for ph in phases) if g]   # 4 different students per page: all pre-test sheets first, then the post-test sheets on new pages
    if not groups: return None
    chunks = [g[i:i + 4] for g in groups for i in range(0, len(g), 4)]
    test = t_rtest(sec); today = time.strftime('%Y-%m-%d'); fr = [0.07, 0.43, 0.21, 0.21, 0.08]
    def txt(ops, x, y, s, size, bold=False, rgb='0.1 0.09 0.23'):
        b = _pdfclean(s).encode('cp1252', 'replace').replace(b'\\', b'\\\\').replace(b'(', b'\\(').replace(b')', b'\\)')
        ops.append(b'BT /F%d %.1f Tf %s rg %.2f %.2f Td (' % (2 if bold else 1, size, rgb.encode(), x, H - y) + b + b') Tj ET')
    def rect(ops, x, y, w, h, rgb): ops.append(b'%s rg %.2f %.2f %.2f %.2f re f' % (rgb.encode(), x, H - y - h, w, h))
    def box(ops, x, y, w, h): ops.append(b'0.8 0.76 0.95 RG 0.6 w %.2f %.2f %.2f %.2f re S' % (x, H - y - h, w, h))
    def sheet(ops, cx, cy, n, ph, o):
        box(ops, cx, cy, cw, ch)
        rect(ops, cx, cy, cw, 26, '0.93 0.9 1')
        txt(ops, cx + 5, cy + 11, n, 9, True, '0.36 0.13 0.71')
        txt(ops, cx + 5, cy + 21, '%s - %s - %s' % ('Pre-test' if ph == 'pre' else 'Post-test', sec, test), 5.8, False, '0.42 0.44 0.5')
        sc = '%s/%s  %s%%' % (o['c'], o['n'], o['pct']); txt(ops, cx + cw - 5 - len(sc) * 5.2, cy + 16, sc, 9.5, True, '0.36 0.13 0.71')
        ws = [cw * f for f in fr]; top = cy + 28; room = ch - 28 - 4
        for size in (6.6, 6.0, 5.4, 4.8, 4.2, 3.8):
            LH = size * 1.2; pad = 1.2
            cells = [[_wrap(_pdfclean(c), ws[j] - 2 * pad, size) for j, c in enumerate((str(i + 1), r['q'], r['v'] if r['v'] else '(blank)', r['a'], ''))] for i, r in enumerate(o['rows'])]
            hs = [max(len(x) for x in c) * LH + 2 * pad for c in cells]
            if LH + 2 * pad + sum(hs) <= room: break
        y = top; hh = LH + 2 * pad; rect(ops, cx, y, cw, hh, '0.97 0.95 1'); x = cx
        for j, lab in enumerate(('#', 'Question', 'Answer', 'Correct', 'Mark')): txt(ops, x + pad, y + pad + LH - 1.5, lab, size, True); x += ws[j]
        y += hh
        for i, r in enumerate(o['rows']):
            if y + hs[i] > cy + ch - 2: break
            if i % 2: rect(ops, cx, y, cw, hs[i], '0.985 0.98 1')
            x = cx
            for j in range(4):
                for k, ln in enumerate(cells[i][j]): txt(ops, x + pad, y + pad + (k + 1) * LH - 1.5, ln, size, False, '0.1 0.09 0.23' if j != 2 or r['ok'] else '0.86 0.15 0.15')
                x += ws[j]
            txt(ops, x + pad, y + pad + LH - 1.5, 'OK' if r['ok'] else 'X', size, True, '0.09 0.64 0.29' if r['ok'] else '0.86 0.15 0.15')
            y += hs[i]
    pages = []; N = len(chunks)
    for pi in range(N):
        ops = []
        for k, (n, ph, o) in enumerate(chunks[pi]): sheet(ops, M + (k % 2) * (cw + G), M + (k // 2) * (ch + G), n, ph, o)
        txt(ops, W / 2 - 70, H - 14, 'Answer sheets - page %d of %d - %s' % (pi + 1, N, today), 7, False, '0.5 0.5 0.6')
        pages.append(b'\n'.join(ops))
    return _pdf_pack(pages)
T_PDFKINDS = ('class', 'items_pre', 'items_post', 'items_cmp', 'scores', 'students', 'sheets')   # the stored PDF reports (locked A4)
def t_save_pdf(d):   # one browser-rendered report (class / items / students) made into a locked A4 PDF and stored next to the other report files
    sec, kind, rk = d.get('sec'), d.get('kind'), d.get('rk', 'COMPARE')
    if sec not in ROSTER or rk not in T_KINDS or kind not in ('class', 'items_pre', 'items_post', 'items_cmp', 'students'): return False
    try:
        os.makedirs(T_RDIR, exist_ok=True)
        cols = [_pdfclean(c) for c in (d.get('cols') or [])][:30]
        rows = [x for x in (_pdfrow(r) for r in (d.get('rows') or [])[:20000] if isinstance(r, (str, list, dict))) if x is not None]
        pdf = make_pdf(_pdfclean(d.get('title', ''))[:120], _pdfclean(d.get('sub', ''))[:160], cols, rows, [x for x in (d.get('w') or []) if isinstance(x, (int, float))])
        path = os.path.join(T_RDIR, t_rbase(sec, rk) + '.' + kind + '.pdf'); tmp = path + '.tmp'
        with open(tmp, 'wb') as f: f.write(pdf)
        os.replace(tmp, path); return True
    except Exception: return False
def t_store_reports(sec):   # saves the PRE, POST and COMPARE reports, each only when its data exists; saving again overwrites with the latest data
    if sec not in ROSTER: return 'Pick a class section first.'
    try:
        has = t_kind_data(sec)
        if not any(has.values()): return 'Nothing to save yet: no student has submitted the pre-test or the post-test in this section.'
        os.makedirs(T_RDIR, exist_ok=True)
        def put(path, data, mode='w'):
            tmp = path + '.tmp'
            with (open(tmp, 'wb') if mode == 'wb' else open(tmp, 'w', encoding='utf-8', newline='')) as f: f.write(data)
            os.replace(tmp, path)
        for kind in T_KINDS:
            if not has[kind]: continue
            rep = t_all_report(sec, kind); nm = t_rbase(sec, kind); base = os.path.join(T_RDIR, nm)
            put(base + '.json', json.dumps(rep, ensure_ascii=False, indent=1)); put(base + '.csv', t_report_csv(rep))
            try:   # the scores-per-student PDF (locked A4)
                x = t_rfile(nm, 'pdf')
                if x: put(base + '.scores.pdf', x[0], 'wb')
            except Exception: pass
            if kind != 'COMPARE':
                try:   # answer sheets: 4 students per A4 page, made on the server (they belong to the pre-test and to the post-test)
                    x = t_sheets_pdf(sec, phases=tuple(T_KPH[kind]))
                    if x: put(base + '.sheets.pdf', x, 'wb')
                except Exception: pass
            try: put(base + '.full.json', json.dumps(t_full_report(sec, kind), ensure_ascii=False, separators=(',', ':')))
            except Exception: pass
        return 'ok'
    except Exception as e: return 'Could not save the report: %s' % e
def t_rlist():   # the stored reports for the dashboard (newest first)
    out = []
    try:
        for f in os.listdir(T_RDIR):
            m = re.match(r'^(.+-report)\.json$', f)
            if not m or not T_RNAME.match(m.group(1)): continue
            if m.group(1).endswith('__ALL-report'): continue   # the older combined reports are no longer shown
            try:
                o = json.load(open(os.path.join(T_RDIR, f), encoding='utf-8')); sm = o['summary']
                out.append({'name': m.group(1), 'kind': (re.search(r'__(ALL|PRE|POST|COMPARE)-report$', m.group(1)) or [0, 'ALL'])[1], 'test': o['test'], 'sec': o['section'], 'total': sm['total'], 'both': sm['both'], 'gain': sm['gain'],
                            'pre': {k: sm['pre'][k] for k in ('started', 'taken', 'mean', 'absent')}, 'post': {k: sm['post'][k] for k in ('started', 'taken', 'mean', 'absent')}, 'updated': o['updated'], 'pdfs': [k for k in T_PDFKINDS if os.path.exists(os.path.join(T_RDIR, m.group(1) + '.' + k + '.pdf'))]})
            except Exception: pass
    except Exception: pass
    return sorted(out, key=lambda e: (e['updated'], ('ALL', 'PRE', 'POST', 'COMPARE').index(e['kind'])), reverse=True)
def t_rfile(name, ext):   # (bytes, content type) of one stored report, or None
    if not T_RNAME.match(str(name or '')) or ext not in ('csv', 'json', 'pdf', 'full') + T_PDFKINDS: return None
    try:
        if ext in T_PDFKINDS: return open(os.path.join(T_RDIR, name + '.' + ext + '.pdf'), 'rb').read(), 'application/pdf'
        if ext == 'full': return open(os.path.join(T_RDIR, name + '.full.json'), 'rb').read(), 'application/json'
        if ext != 'pdf': return open(os.path.join(T_RDIR, name + '.' + ext), 'rb').read(), ('text/csv' if ext == 'csv' else 'application/json')
        rep = json.load(open(os.path.join(T_RDIR, name + '.json'), encoding='utf-8')); tp = rep['topics']; sm = rep['summary']
        phs = sm.get('phases') or ['pre', 'post']; two = len(phs) > 1; LB = {'pre': 'Pre', 'post': 'Post'}
        P = lambda y: ('%g%%' % y['pct']) if y['pct'] is not None else ('-' if y['status'] == 'Not started' else y['status'].replace(' (not taken)', ''))
        T = lambda y, t: '' if t not in y['topics'] or not y['topics'][t][1] else '%d%%' % round(100.0 * y['topics'][t][0] / y['topics'][t][1])
        G = lambda g: '' if g is None else ('%+g' % g)
        M = lambda v: '-' if v is None else '%g%%' % v
        rows = [[_pdfsafe(x['n'])] + [P(x[ph]) for ph in phs] + ([G(x['gain'])] if two else []) + [' > '.join(T(x[ph], t) or '-' for ph in phs) for t in tp] for x in rep['rows']]
        pad = [''] * (len(phs) + (1 if two else 0)); fill = lambda lab, vals: [lab] + vals + [''] * (len(phs) + (1 if two else 0) - len(vals))
        rows.append('SUMMARY')
        rows.append(fill('Taken', ['%s %d of %d' % (LB[ph], sm[ph]['taken'], sm['total']) for ph in phs]) + [''] * len(tp))
        rows.append(fill('Class mean', [M(sm[ph]['mean']) for ph in phs] + ([G(sm['gain'])] if two else [])) + [' > '.join(M(sm[ph]['topic_mean'].get(t)) for ph in phs) for t in tp])
        for ph in phs:
            if sm[ph]['absent']: rows.append(fill('Absent ' + LB[ph].lower(), [_pdfsafe(', '.join(sm[ph]['absent']))]) + [''] * len(tp))
        ttl = 'Pre-test and Post-test Report' if two and name.endswith('ALL-report') else 'Pre vs Post Comparison Report' if two else ('Pre-test Report' if phs == ['pre'] else 'Post-test Report')
        nw = 0.06 if two else 0
        pdf = make_pdf(ttl, _pdfsafe('%s - %s - updated %s' % (rep['section'], rep['test'], rep['updated'][:16])), ['Student'] + [LB[ph] for ph in phs] + (['Gain'] if two else []) + [_pdfsafe(t) + (' (pre > post)' if two else '') for t in tp], rows, [0.2] + [0.09] * len(phs) + ([0.06] if two else []) + [(1 - 0.2 - 0.09 * len(phs) - nw) / max(1, len(tp))] * len(tp))
        return pdf, 'application/pdf'
    except Exception: return None
_PDF_MAP = {'\u20b1': 'P', '\u2212': '-', '\u2013': '-', '\u2014': '-', '\u221a': 'sqrt', '\u03c0': 'pi', '\u2264': '<=', '\u2265': '>=', '\u2260': '!=', '\u2248': '~', '\u2220': 'angle ', '\u2044': '/'}
def _pdfsafe(x):   # the PDF font is Helvetica (Windows-1252): swap the few maths symbols it lacks
    x = str(x)
    for k, v in _PDF_MAP.items(): x = x.replace(k, v)
    return x.encode('cp1252', 'replace').decode('cp1252')
def t_paper(sec, ans=None):   # ONE A4 locked PDF: the test paper first, then the teacher's answer key on its own page(s)
    band = '9' if t_band(sec) == '9' else '7'; items = t_get_form('A', sec)
    rows = []; cur = None
    for i, it in enumerate(items):
        if it['t'] != cur: cur = it['t']; rows.append(_pdfsafe(cur))
        rows.append([str(i + 1), _pdfsafe(it['q']), '\n\n'])
    rows.append('\f'); cur = None
    for i, it in enumerate(items):
        if it['t'] != cur: cur = it['t']; rows.append('ANSWER KEY (teacher only) - ' + _pdfsafe(cur))
        rows.append([str(i + 1), _pdfsafe(it['q']), _pdfsafe(it['a'])])
    tp, cnt = t_bp(sec); lab = 'Grade 9-10' if band == '9' else 'Grade 7-8'
    return make_pdf('Numeracy Test (Pre-test / Post-test)',
        'Name: ______________________   Section: ____________   Date: ____________   %s - %d items. The answer key is on the last page(s): print the test pages only for students.' % (lab, t_total(cnt)),
        ['No.', 'Question', 'Answer'], rows, [0.08, 0.62, 0.30])
T_DIR = os.path.join(DATA_DIR, 'gnhs-test-copies')   # every named copy lives here: <name>-PRE.json and <name>-POST.json
def t_cname(x): return re.sub(r'[^A-Za-z0-9 _.\-]+', '', str(x or '')).strip().replace(' ', '-')[:60].strip('.-')
def t_name():   # the current test's name (file name stem); a dated default is made the first time one is needed
    n = t_cname(TD.get('name'))
    if not n: n = time.strftime('Numeracy-Test-%Y-%m-%d-%H%M'); TD['name'] = n; t_save()
    return n
def t_cpath(name, kind): return os.path.join(T_DIR, '%s-%s.json' % (name, kind))
def t_export():   # a full copy of the test: blueprint(s) + every form (with the answer key), so it can be loaded back later
    for f in 'AB':
        for s_ in ('Grade 7', 'Grade 9'): t_get_form(f, s_, True)
        for s_ in ROSTER:
            if t_own(s_): t_get_form(f, s_)
    tp, cnt = t_bp(); o = {'app': 'gnhs-test-copy', 'v': 3, 'name': t_name(), 'saved': time.strftime('%Y-%m-%d %H:%M'), 'bp': {'topics': tp, 'counts': cnt}}
    bps = {}
    if t_per():
        o['mode'] = 'per'
        for s_ in ROSTER:
            if t_own(s_): bps[s_] = dict(zip(('topics', 'counts'), t_bp(s_)))
        o['bps'] = bps
    o['forms'] = {k: v for k, v in TD['forms'].items() if '@' not in k or k.split('@', 1)[1] in bps}
    sets = {}; act = {}
    for s_, S_ in TD.get('sets', {}).items():   # the other tests of a section (the active one is already in 'forms')
        if s_ in ROSTER and S_.get('items'):
            act[s_] = S_['active']
            sets[s_] = {n_: {'bp': sn.get('bp'), 'forms': dict(sn.get('forms') or {})} for n_, sn in S_['items'].items()}
    if sets: o['sets'] = sets; o['setact'] = act
    return o
def t_import(o):  # load a downloaded test copy back in; returns 'ok' or a message for the teacher
    if TD['resp']['post']: return "Some students have already started the post-test, so a test copy cannot be loaded now. Reset their post-tests first."
    def one(bp):
        tp = [t for t in TOPICS if t in bp['topics']]
        cnt = {t: bp['counts'][t] for t in tp} if isinstance(bp.get('counts'), dict) else {t: bp['ipt'] for t in tp}   # files from before had one 'ipt' for all topics
        if not tp or len(tp) != len(bp['topics']) or any(isinstance(v, bool) or not isinstance(v, int) or not 1 <= v <= T_MAXN for v in cnt.values()): raise ValueError
        return tp, cnt
    try:
        tp, cnt = one(o['bp']); forms = o['forms']; sb = {}
        if o.get('mode') == 'per' and isinstance(o.get('bps'), dict):
            for s_, b_ in o['bps'].items():
                if s_ in ROSTER: sb[s_] = one(b_)
        if not isinstance(forms, dict) or not forms: raise ValueError
        clean = {}
        for fid, items in forms.items():
            m = re.match(r'^([AB][79])(?:@(.+))?$', str(fid))
            if not m: raise ValueError
            if m.group(2) is None: w_tp, w_cnt = tp, cnt
            elif m.group(2) in sb: w_tp, w_cnt = sb[m.group(2)]
            else: continue   # a section this class list does not have
            want = [t for t in w_tp for _ in range(w_cnt[t])]
            if not isinstance(items, list) or len(items) != len(want): raise ValueError
            for i, it in enumerate(items):
                if not isinstance(it, dict) or it.get('t') != want[i] or not isinstance(it.get('q'), str) or not it['q'] or len(it['q']) > 2000 or isinstance(it.get('a'), bool) or not isinstance(it.get('a'), (int, float, str)): raise ValueError
            clean[fid] = [{'t': it['t'], 'q': it['q'], 'a': it['a']} for it in items]
        if not clean: raise ValueError
    except Exception: return 'That file is not a valid test copy.'
    for s_ in ROSTER:
        if any(k.startswith(s_ + '|') for k in TD['resp']['pre']) and sb.get(s_, (tp, cnt)) != t_bp(s_):
            return 'The pre-test was already taken in %s with a different blueprint (%s). This copy must have the same topics and the same items for each topic in that section.' % (s_, t_bp_txt(*t_bp(s_)))
    TD['bp'] = {'topics': tp, 'counts': cnt}; TD['forms'] = clean
    TD['bpmode'] = 'per' if o.get('mode') == 'per' else 'same'; TD['bps'] = {s_: {'topics': b[0], 'counts': b[1]} for s_, b in sb.items()}
    nm = t_cname(o.get('name')) if isinstance(o.get('name'), str) else ''
    if nm and not TD['resp']['pre']: TD['name'] = nm
    try: t_import_sets(o)
    except Exception: pass
    t_save(); return 'ok'
def t_import_sets(o):   # restore a section's other tests from a copy (never touches a test that already has student answers)
    if not isinstance(o.get('sets'), dict) or not t_per(): return
    act = o.get('setact') if isinstance(o.get('setact'), dict) else {}
    for s_, items in o['sets'].items():
        if s_ not in ROSTER or not isinstance(items, dict): continue
        S = t_set_state(s_)
        for n_, sn in items.items():
            n_ = t_set_clean(n_)
            if not n_ or n_ == S['active'] or not isinstance(sn, dict) or not isinstance(sn.get('forms'), dict): continue
            old = S['items'].get(n_)
            if old and (old.get('pre') or old.get('post')): continue
            if len(S['items']) >= 30 and not old: continue
            forms = {}
            for fid, its in sn['forms'].items():
                if not re.match(r'^[AB][79](?:@.+)?$', str(fid)) or not isinstance(its, list): continue
                if all(isinstance(it, dict) and isinstance(it.get('q'), str) and it['q'] and it.get('t') in TOPICS and isinstance(it.get('a'), (int, float, str)) and not isinstance(it.get('a'), bool) for it in its): forms[fid] = [{'t': it['t'], 'q': it['q'], 'a': it['a']} for it in its]
            if not forms: continue
            bp = None
            if isinstance(sn.get('bp'), dict):
                tp, cnt = t_bp_parse(sn['bp']); bp = {'topics': tp, 'counts': cnt}
            if old: old['forms'] = forms; old['bp'] = bp
            else: S['items'][n_] = {'bp': bp, 'forms': forms, 'pre': {}, 'post': {}, 'stage': 'off', 'release': False}
        a_ = t_set_clean(act.get(s_))
        if a_ and a_ != S['active'] and a_ not in S['items'] and not any(k.startswith(s_ + '|') for k in list(TD['resp']['pre']) + list(TD['resp']['post'])): S['active'] = a_
T_COPY = os.path.join(DATA_DIR, 'gnhs-test-copy.json')   # written by the server itself: the post-test copy
def t_snap(force=False):   # save an identical copy of the test (blueprint + all forms) as <name>-PRE.json and <name>-POST.json. Frozen once any student has started the pre-test
    if TD['resp']['pre'] and not force: return
    try:
        data = json.dumps(t_export(), ensure_ascii=False, indent=1); name = t_name(); os.makedirs(T_DIR, exist_ok=True)
        for kind in ('PRE', 'POST'):
            tmp = t_cpath(name, kind) + '.tmp'
            with open(tmp, 'w', encoding='utf-8') as f: f.write(data)
            os.replace(tmp, t_cpath(name, kind))
    except Exception: pass
def t_snap_load():   # the pending post-test copy of the current test
    n = t_cname(TD.get('name'))
    for path in ([t_cpath(n, 'POST')] if n else []) + [os.path.join(DATA_DIR, 'gnhs-test-copy.json')]:
        try: return json.load(open(path, encoding='utf-8'))
        except Exception: pass
    return None
def t_copy_repair():   # every saved copy must have BOTH a PRE and a POST file: if one is missing, rebuild it from the other
    try:
        names = {}
        for f in os.listdir(T_DIR):
            m = re.match(r'^(.+)-(PRE|POST)\.json$', f)
            if m: names.setdefault(m.group(1), set()).add(m.group(2))
        for n, ks in names.items():
            if len(ks) == 2: continue
            have = next(iter(ks)); miss = 'POST' if have == 'PRE' else 'PRE'
            tmp = t_cpath(n, miss) + '.tmp'
            with open(t_cpath(n, have), 'rb') as a_, open(tmp, 'wb') as b_: b_.write(a_.read())
            os.replace(tmp, t_cpath(n, miss))
    except Exception: pass
def t_copy_list():   # the library of named copies for the dashboard
    out = {}
    t_copy_repair()
    try:
        for f in os.listdir(T_DIR):
            m = re.match(r'^(.+)-(PRE|POST)\.json$', f)
            if not m: continue
            e = out.setdefault(m.group(1), {'name': m.group(1), 'files': [], 'saved': '', 'topics': [], 'counts': {}, 'total': 0, 'mode': 'same'})
            e['files'].append(m.group(2))
            try:
                o = json.load(open(os.path.join(T_DIR, f), encoding='utf-8')); e['saved'] = o.get('saved', ''); e['topics'] = o['bp']['topics']; bc = o['bp'].get('counts')
                e['counts'] = bc if isinstance(bc, dict) else {t: o['bp']['ipt'] for t in e['topics']}; e['total'] = sum(e['counts'].get(t, 0) for t in e['topics']); e['mode'] = 'per' if o.get('mode') == 'per' else 'same'
                mt = (TD.get('bpmeta') or {}).get(m.group(1))
                if mt and isinstance(o.get('bps'), dict) and mt.get('sec') in o['bps']: sb = o['bps'][mt['sec']]; e['sec'] = mt['sec']; e['topics'] = sb['topics']; e['counts'] = sb['counts']; e['total'] = sum(sb['counts'].get(t, 0) for t in sb['topics'])
            except Exception: pass
    except Exception: pass
    return sorted(out.values(), key=lambda e: e['saved'], reverse=True)
def t_copy_file(name, kind):   # bytes of one named copy file (None when missing)
    name = t_cname(name)
    if not name or kind not in ('PRE', 'POST'): return None
    if not os.path.exists(t_cpath(name, kind)) and name == t_cname(TD.get('name')): t_snap()
    try: return open(t_cpath(name, kind), 'rb').read()
    except Exception: return None
def t_load_copy(name, kind):   # make a saved copy the current test
    b = t_copy_file(name, kind if kind in ('PRE', 'POST') else 'POST')
    if not b: return 'That saved copy was not found.'
    try: o = json.loads(b.decode('utf-8'))
    except Exception: return 'That saved copy is damaged.'
    r = t_import(o)
    if r == 'ok' and not TD['resp']['pre']: TD['name'] = t_cname(name); t_save()
    return r
def t_restore():   # when the post-test opens, make sure it uses exactly the saved copy (a no-op when nothing changed)
    if any(x.get('items') for x in TD.get('sets', {}).values()): return   # several tests per section: each test keeps its own questions
    o = t_snap_load()
    if o: t_import(o)
def t_copy_info():   # what the dashboard shows about the pending post-test copy
    o = t_snap_load()
    if not isinstance(o, dict): return None
    try:
        tp = o['bp']['topics']; cnt = o['bp']['counts'] if isinstance(o['bp'].get('counts'), dict) else {t: o['bp']['ipt'] for t in tp}
        return {'name': t_cname(TD.get('name')), 'saved': o.get('saved', ''), 'topics': tp, 'counts': cnt, 'n': sum(cnt.get(t, 0) for t in tp), 'match': all(TD['forms'].get(k) == v for k, v in o['forms'].items()), 'mode': 'per' if o.get('mode') == 'per' else 'same', 'secs': {s_: {'topics': b_.get('topics', []), 'counts': b_.get('counts', {})} for s_, b_ in (o.get('bps') or {}).items()} if o.get('mode') == 'per' else {}, 'tests': t_copy_tests(o)}
    except Exception: return None
def t_copy_tests(o):   # every test (per section) stored in the saved copy
    out = []
    for s_, items in (o.get('sets') or {}).items():
        if s_ not in ROSTER: continue
        act = (o.get('setact') or {}).get(s_, 'Set 1'); bp = (o.get('bps') or {}).get(s_) or o.get('bp') or {}
        def row(n_, b_, a_):
            try:
                tp = b_['topics']; cnt = b_['counts'] if isinstance(b_.get('counts'), dict) else {t: b_['ipt'] for t in tp}
                return {'sec': s_, 'name': n_, 'active': a_, 'n': sum(cnt.get(t, 0) for t in tp), 'topics': tp}
            except Exception: return {'sec': s_, 'name': n_, 'active': a_, 'n': 0, 'topics': []}
        out.append(row(act, bp, True))
        for n_, sn in items.items(): out.append(row(n_, sn.get('bp') or o.get('bp') or {}, False))
    return out
def t_copy_view(sec, setn=None):   # the saved copy's questions for the selected section's grade band
    o = t_snap_load(); band = t_band(sec)
    if not isinstance(o, dict) or not isinstance(o.get('forms'), dict): return {'none': 1}
    sn = ((o.get('sets') or {}).get(sec) or {}).get(setn) if setn else None
    if isinstance(sn, dict) and isinstance(sn.get('forms'), dict):   # one of the section's other tests
        sfx = '@' + sec if any(k.endswith('@' + sec) for k in sn['forms']) else ''
        return dict({'band': band, 'own': bool(sfx)}, **{f: sn['forms'].get(f + band + sfx) or o['forms'].get(f + band) or [] for f in 'AB'})
    sfx = '@' + sec if o.get('mode') == 'per' and sec in (o.get('bps') or {}) else ''
    return dict({'band': band, 'own': bool(sfx)}, **{f: o['forms'].get(f + band + sfx) or [] for f in 'AB'})

# ---- several tests (blueprints) per section: e.g. one pre-test + post-test per topic. The ACTIVE test lives in the normal structures; the others are stashed in TD['sets'][sec]['items'] ----
def t_bp_parse(b):
    b = b or {}; tp = [t for t in TOPICS if t in (b.get('topics') or TOPICS)] or list(TOPICS); c = b.get('counts') if isinstance(b.get('counts'), dict) else {}
    n0 = b.get('ipt') if isinstance(b.get('ipt'), int) and 1 <= b['ipt'] <= T_MAXN else T_ITEMS; cnt = {}
    for t in tp:
        v = c.get(t); cnt[t] = v if isinstance(v, int) and not isinstance(v, bool) and 1 <= v <= T_MAXN else n0
    return tp, cnt
def t_set_state(sec):
    S = TD.setdefault('sets', {}).get(sec)
    if not S: S = TD['sets'][sec] = {'active': 'Set 1', 'items': {}}
    return S
def t_set_clean(x): return re.sub(r'\s+', ' ', re.sub(r'[^\w &\-.,()+]', '', str(x or ''))).strip()[:40]
def t_set_done(R, sec): return sum(1 for k, r in R.items() if k.startswith(sec + '|') and r.get('done'))
def t_sets_info(sec):
    S = TD.get('sets', {}).get(sec) or {'active': 'Set 1', 'items': {}}; tp, cnt = t_bp(sec)
    L = [{'name': S['active'], 'active': True, 'pre': t_set_done(TD['resp']['pre'], sec), 'post': t_set_done(TD['resp']['post'], sec), 'stage': TD['stage'].get(sec, 'off'), 'topics': tp, 'counts': cnt, 'total': t_total(cnt)}]
    for n, sn in S['items'].items():
        tp2, cnt2 = t_bp_parse(sn.get('bp') or TD.get('bp'))
        L.append({'name': n, 'active': False, 'pre': t_set_done(sn['pre'], sec), 'post': t_set_done(sn['post'], sec), 'stage': sn.get('stage', 'off'), 'topics': tp2, 'counts': cnt2, 'total': t_total(cnt2)})
    return {'active': S['active'], 'multi': len(L) > 1, 'list': L}
def t_stash(sec, S):   # move the active test of this section out of the live structures
    pre = '%s|' % sec
    snap = {'bp': dict(TD['bps'][sec]) if sec in TD['bps'] else None, 'forms': {k: TD['forms'].pop(k) for k in [k for k in TD['forms'] if k.endswith('@' + sec)]},
            'pre': {k: TD['resp']['pre'].pop(k) for k in [k for k in TD['resp']['pre'] if k.startswith(pre)]},
            'post': {k: TD['resp']['post'].pop(k) for k in [k for k in TD['resp']['post'] if k.startswith(pre)]},
            'stage': TD['stage'].get(sec, 'off'), 'release': bool(TD['release'].get(sec))}
    TD['bps'].pop(sec, None); TD['stage'][sec] = 'off'; TD['release'][sec] = False
    for k in [k for k in TOPEN if k[1].startswith(pre)]: del TOPEN[k]
    S['items'][S['active']] = snap
def t_unstash(sec, snap):
    if snap.get('bp'): TD['bps'][sec] = snap['bp']
    else: TD['bps'].pop(sec, None)
    TD['forms'].update(snap.get('forms', {})); TD['resp']['pre'].update(snap.get('pre', {})); TD['resp']['post'].update(snap.get('post', {}))
    TD['stage'][sec] = snap.get('stage', 'off'); TD['release'][sec] = bool(snap.get('release'))
def t_set_action(sec, a, d):
    if not t_per(): return 'Switch on "Individual per section" first.'
    S = t_set_state(sec); nm = t_set_clean(d.get('name'))
    if a == 'setuse':
        if nm == S['active']: return
        if nm not in S['items']: return 'That test was not found.'
        snap = S['items'].pop(nm); t_stash(sec, S); t_unstash(sec, snap); S['active'] = nm; return
    if a == 'setnew':
        if not nm: return 'Type a name for the new test.'
        if nm == S['active'] or nm in S['items']: return 'This section already has a test with that name.'
        if len(S['items']) >= 30: return 'Too many tests in this section.'
        tp = [t for t in TOPICS if t in (d.get('topics') or [])]; dc = d.get('counts') if isinstance(d.get('counts'), dict) else {}
        cnt = {t: dc.get(t, T_ITEMS) for t in tp}
        if not tp or any(isinstance(v, bool) or not isinstance(v, int) or not 1 <= v <= T_MAXN for v in cnt.values()): return 'Pick at least one topic and a number of items for each.'
        t_stash(sec, S); TD['bps'][sec] = {'topics': tp, 'counts': cnt}; S['active'] = nm; return
    if a == 'setren':
        old = t_set_clean(d.get('old')) or S['active']
        if not nm: return 'Type a name.'
        if nm != old and (nm == S['active'] or nm in S['items']): return 'This section already has a test with that name.'
        if old == S['active']: S['active'] = nm
        elif old in S['items']: S['items'][nm] = S['items'].pop(old)
        return
    if a == 'setdel':
        if not hmac.compare_digest(str(d.get('pw', '')).encode('utf-8'), T_DELETE_PW.encode('utf-8')): return 'Wrong password. Nothing was deleted.'
        if nm == S['active']: return 'Switch to another test first, then delete this one.'
        if nm not in S['items']: return 'That test was not found.'
        del S['items'][nm]; return
def t_host_act(d):
    sec = d.get('sec'); a = d.get('a')
    if a == 'savereport': return t_store_reports(sec)
    if a == 'loadcopy': return t_load_copy(d.get('name'), d.get('kind'))
    if a == 'delcopy':   # remove a saved copy (both the PRE and POST file); meant for clearing out test runs
        if not hmac.compare_digest(str(d.get('pw', '')).encode('utf-8'), T_DELETE_PW.encode('utf-8')): return 'Wrong password. Nothing was deleted.'
        nm = t_cname(d.get('name'))
        if not nm: return 'That saved copy was not found.'
        cur = nm == t_cname(TD.get('name'))
        if cur and t_bp_locked(): return 'Students have already started this test, so it cannot be deleted. Reset their pre-test and post-test first.'
        for kind in ('PRE', 'POST'):
            try: os.remove(t_cpath(nm, kind))
            except OSError: pass
        if cur:
            TD['name'] = ''; TD['forms'].clear()
            for s_ in list(TD['stage']): TD['stage'][s_] = 'off'   # the exam no longer exists: close it everywhere, so students are sent out
            t_save()   # nobody has started it: forget the questions too, so a new test starts clean
        return 'ok'
    if a == 'import':
        r = t_import(d.get('data') or {})
        if r == 'ok': t_snap(True)   # an upload also rebuilds the dashboard copy, even after the pre-test was taken (the blueprint was checked to match)
        return r
    if a == 'bpmode':   # same blueprint for every section, or an individual blueprint for each section
        if d.get('v') not in ('same', 'per'): return
        if t_any_resp(): return "Students have already started a test, so this option is locked. Reset every student's tests first."
        if d['v'] == 'same' and any(x.get('items') for x in TD.get('sets', {}).values()): return 'Some sections have several tests. Delete the extra tests first.'
        TD['bpmode'] = d['v']; t_save(); t_snap(True); return
    if a == 'bpuse':   # give a section the SAME blueprint as another section (or back to the all-sections one)
        tgt, src = d.get('for'), d.get('src')
        if not t_per() or tgt not in ROSTER: return 'Switch on "Individual per section" first.'
        if t_bp_locked(tgt): return 'Students in %s have already started a test, so its blueprint is locked. Reset their tests first.' % tgt
        if src == tgt: return
        if src == 'all': TD['bps'].pop(tgt, None)
        elif src in ROSTER: tp, cnt = t_bp(src); TD['bps'][tgt] = {'topics': tp, 'counts': dict(cnt)}
        else: return
        for k in [k for k in TD['forms'] if k.endswith('@' + tgt)]: del TD['forms'][k]
        t_save(); t_snap(True); return
    if a == 'bpsave':   # blueprint builder: a section + a file name + topics and items per topic -> a named test for that section, saved as <name>-PRE.json and an identical <name>-POST.json
        tgt = d.get('sec') if d.get('sec') in ROSTER else None
        if not tgt: return 'Choose a section first.'
        nm = t_cname(d.get('name'))
        if not nm: return 'Type a file name for the blueprint.'
        tp = [t for t in TOPICS if t in (d.get('topics') or [])]; dc = d.get('counts') if isinstance(d.get('counts'), dict) else {}
        cnt = {t: dc.get(t) for t in tp}
        if not tp or any(isinstance(v, bool) or not isinstance(v, int) or not 1 <= v <= T_MAXN for v in cnt.values()): return 'Pick at least one topic and a number of items for each.'
        if not t_per():
            if t_any_resp(): return "Students have already started a test, so a section blueprint cannot be added now. Reset every student's tests first."
            TD['bpmode'] = 'per'
        S = t_set_state(tgt); bp = {'topics': tp, 'counts': cnt}
        def drop_forms(): [TD['forms'].pop(k) for k in [k for k in TD['forms'] if k.endswith('@' + tgt)]]
        if nm == S['active']:   # change a blueprint that nobody has started yet
            if t_bp_locked(tgt): return 'Students in %s have already started "%s", so it cannot be changed. Choose another file name.' % (tgt, nm)
            TD['bps'][tgt] = bp; drop_forms()
        elif nm in S['items']:
            sn = S['items'][nm]
            if sn.get('pre') or sn.get('post'): return 'Students in %s have already started "%s", so it cannot be changed. Choose another file name.' % (tgt, nm)
            sn['bp'] = bp; sn['forms'] = {}
        else:
            if os.path.exists(t_cpath(nm, 'PRE')): return 'A saved file named "%s" already exists. Choose another file name.' % nm
            if len(S['items']) >= 30: return 'Too many tests in this section.'
            if S['active'] == 'Set 1' and not t_bp_locked(tgt): S['active'] = nm; TD['bps'][tgt] = bp; drop_forms()   # the untouched default test is simply replaced
            else: t_stash(tgt, S); TD['bps'][tgt] = bp; S['active'] = nm   # the previous test is kept in the list
        TD['name'] = nm; TD.setdefault('bpmeta', {})[nm] = {'sec': tgt}
        t_save(); t_snap(True); return 'ok:' + nm
    if a == 'bp':
        tp = [t for t in TOPICS if t in (d.get('topics') or [])]; dc = d.get('counts') if isinstance(d.get('counts'), dict) else {}
        cnt = {t: dc.get(t, d.get('ipt')) for t in tp}; tgt = d.get('for') if d.get('for') in ROSTER else None
        if tgt and not t_per(): return 'Switch on "Individual per section" first.'
        if not t_bp_locked(tgt) and tp and all(isinstance(v, int) and not isinstance(v, bool) and 1 <= v <= T_MAXN for v in cnt.values()):
            nm = (t_cname(d.get('name')) or t_name()) if not t_any_resp() else t_name()   # no renaming once students have started
            if nm != t_cname(TD.get('name')) and os.path.exists(t_cpath(nm, 'PRE')): return 'A saved copy named "%s" already exists. Choose another name, or load it from the saved copies list.' % nm
            if tgt:
                TD['bps'][tgt] = {'topics': tp, 'counts': cnt}
                for k in [k for k in TD['forms'] if k.endswith('@' + tgt)]: del TD['forms'][k]
            else:
                TD['bp'] = {'topics': tp, 'counts': cnt}; TD['forms'] = {k: v for k, v in TD['forms'].items() if '@' in k}   # keep the sections' own questions
            TD['name'] = nm; t_save(); t_snap(True)
        return
    if sec not in ROSTER: return
    if a in ('setuse', 'setnew', 'setren', 'setdel'):
        m = t_set_action(sec, a, d); t_save()
        if not m: t_snap(True)
        return m
    if a == 'stage' and d.get('v') in T_STAGES:
        TD['stage'][sec] = d['v']
        if d['v'] == 'pre': t_snap()
        elif d['v'] == 'post': t_restore()
    elif a == 'release': TD['release'][sec] = bool(d.get('v'))
    elif a in ('pause', 'resume') and is_roster(sec, d.get('name', '')):   # stop / continue ONE student's test (to stop copying from a seatmate)
        (TPAUSE.add if a == 'pause' else TPAUSE.discard)(skey(sec, d['name']))
    elif a == 'reset' and d.get('ph') in ('pre', 'post') and is_roster(sec, d.get('name', '')): TD['resp'][d['ph']].pop(skey(sec, d['name']), None); TOPEN.pop((d['ph'], skey(sec, d['name'])), None)
    t_save()

def t_sheets(sec):   # every finished test of a section with each question, the student's answer, the right answer and the mark (for printing)
    out = {}
    for name in ROSTER.get(sec, []):
        key = skey(sec, name); o = {}
        for ph in ('pre', 'post'):
            r = TD['resp'][ph].get(key)
            if not r or not r.get('done') or not r.get('res'): continue
            items = t_get_form(t_form_of(key, ph), sec); ans = r.get('ans', {}); rows = []
            for i, it in enumerate(items):
                v = str(ans.get(str(i), '')).strip()
                rows.append({'t': it['t'], 'q': it['q'], 'a': str(it['a']), 'v': v, 'ok': bool(v) and bool(correct({'type': 'num', 'ans': it['a']}, v))})
            o[ph] = {'rows': rows, 'c': r['res']['c'], 'n': r['res']['n'], 'pct': round(t_pct(r))}
        if o: out[name] = o
    return out
def t_items(sec):   # ITEM ANALYSIS: for every test question, how many students got it right in the pre-test and in the post-test (+ each student's own mark per item)
    items, idx, stu = [], {}, {}
    for name in ROSTER.get(sec, []):
        key = skey(sec, name)
        for ph in ('pre', 'post'):
            r = TD['resp'][ph].get(key)
            if not r or not r.get('done') or not r.get('res'): continue
            form = t_get_form(t_form_of(key, ph), sec); ans = r.get('ans', {})
            for i, it in enumerate(form):
                k = it['t'] + '\u241f' + it['q']
                if k not in idx: idx[k] = len(items); items.append({'id': len(items), 't': it['t'], 'q': it['q'], 'a': str(it['a']), 'pre': [0, 0], 'post': [0, 0]})
                v = str(ans.get(str(i), '')).strip(); good = bool(v) and bool(correct({'type': 'num', 'ans': it['a']}, v))
                x = items[idx[k]][ph]; x[1] += 1; x[0] += 1 if good else 0
                stu.setdefault(name, {}).setdefault(ph, {})[str(idx[k])] = 1 if good else 0
    order = {t: n for n, t in enumerate(TOPICS)}
    items.sort(key=lambda x: (order.get(x['t'], 99), x['id']))
    return {'items': items, 'stu': stu}
def t_get(self, u, q):
    # returns True when the request belonged to the pre/post test
    g = lambda k: q.get(k, [''])[0]
    if u.path == '/test': self.send(T_STUDENT, 'text/html')
    elif u.path == '/test/host':
        self.send(T_HOST if keyok(g('key')) else LOGIN.replace('/host?key=', '/test/host?key=').replace('Enter your PIN to open the host dashboard', 'Enter your PIN to open the test dashboard'), 'text/html')
    elif u.path == '/api/t/roster': self.send(json.dumps(ROSTER))
    elif u.path == '/api/t/boot': self.send(json.dumps({'boot': T_BOOT}))
    elif u.path == '/api/t/pstate':   # a student's page asks every 2 s whether the teacher stopped the test
        sec, name = g('sec')[:60], g('name')[:60]
        if not is_roster(sec, name): self.send(json.dumps({'paused': False}))
        else:
            k = skey(sec, name); ph = {'pre': 'pre', 'post': 'post'}.get(TD['stage'].get(sec, 'off'))
            gen = None
            if ph and not (TD['resp'][ph].get(k) or {}).get('done'):
                TOPEN[(ph, k)] = time.time()
                with lock: gen = t_gen(t_get_form(t_form_of(k, ph), sec))
            self.send(json.dumps({'paused': k in TPAUSE, 'phase': ph, 'gen': gen}))
    elif u.path == '/api/t/test':
        sec, name = g('sec')[:60], g('name')[:60]
        if not is_roster(sec, name): self.send(json.dumps({'err': 'roster'})); return True
        with lock:
            if not t_claim_ok(sec, name, g('cid')[:40]): self.send(json.dumps({'err': 'claimed'})); return True
            self.send(json.dumps(t_student_view(sec, name), ensure_ascii=False))
    elif u.path.startswith('/api/t/'):
        if not keyok(g('key')): self.send_error(403); return True
        with lock:
            if u.path == '/api/t/hstate':
                secs = {}
                for sec in ROSTER:
                    names = ROSTER[sec]; row = {}
                    for ph in ('pre', 'post'):
                        R = TD['resp'][ph]; ds = [n for n in names if (R.get(skey(sec, n)) or {}).get('done')]
                        ip = [n for n in names if n not in ds and ((R.get(skey(sec, n)) or {}).get('ans') or time.time() - TOPEN.get((ph, skey(sec, n)), 0) < 30)]
                        row[ph] = {'done': len(ds), 'prog': len(ip), 'pct': {n: round(t_pct(R[skey(sec, n)])) for n in ds}, 'inprog': ip}
                    secs[sec] = dict({'stage': TD['stage'].get(sec, 'off'), 'total': len(names), 'names': names, 'release': bool(TD['release'].get(sec)), 'bp': t_secbp(sec), 'paused': [n for n in names if skey(sec, n) in TPAUSE], 'sets': t_sets_info(sec)}, **row)
                self.send(json.dumps({'secs': secs, 'stages': T_STAGES, 'txt': T_STAGE_TXT, 'topics': t_bp()[0], 'counts': t_bp()[1], 'total': t_total(t_bp()[1]), 'mode': 'per' if t_per() else 'same', 'mlocked': t_any_resp(), 'all': TOPICS, 'locked': t_bp_locked(), 'copy': t_copy_info(), 'name': t_cname(TD.get('name')), 'copies': t_copy_list(), 'reports': t_rlist()}, ensure_ascii=False))
            elif u.path == '/api/t/paper': self._out(t_paper(g('sec') if g('sec') in ROSTER else next(iter(ROSTER), 'Grade 7')), 'application/pdf')
            elif u.path == '/api/t/copyview': self.send(json.dumps(t_copy_view(g('sec') if g('sec') in ROSTER else next(iter(ROSTER), 'Grade 7'), g('set')), ensure_ascii=False))
            elif u.path == '/api/t/copyfile':
                b = t_copy_file(g('name'), g('kind'))
                if b is None: self.send_error(404)
                else: self._out(b, 'application/json')
            elif u.path == '/api/t/fullnow': self.send(json.dumps(t_full_report(g('sec'), g('kind') if g('kind') in T_KINDS else 'ALL'), ensure_ascii=False) if g('sec') in ROSTER else '{}')
            elif u.path == '/api/t/rfile':
                x = t_rfile(g('name'), g('ext'))
                if x is None: self.send_error(404)
                else: self._out(x[0], x[1])
            elif u.path == '/api/t/export': self.send(json.dumps(t_export(), ensure_ascii=False, indent=1))
            elif u.path == '/api/t/report': self.send(json.dumps(t_report(g('sec')), ensure_ascii=False))
            elif u.path == '/api/t/sheets': self.send(json.dumps(t_sheets(g('sec') if g('sec') in ROSTER else ''), ensure_ascii=False))
            elif u.path == '/api/t/items': self.send(json.dumps(t_items(g('sec') if g('sec') in ROSTER else ''), ensure_ascii=False))
            elif u.path == '/api/t/reports': self.send(json.dumps({n: t_results(g('sec'), n) for n in ROSTER.get(g('sec'), [])}, ensure_ascii=False))
            elif u.path == '/api/t/csv':
                L = [['Section', 'Student', 'Forms (pre>post)', 'Pre %', 'Post %', 'Gain (pts)', 'Normalised gain g', 'Drill attempts between tests'] + ['%s pre %%' % t for t in TOPICS] + ['%s post %%' % t for t in TOPICS]]
                for sec in ROSTER:
                    for r in t_report(sec)['rows']: L.append([sec, r['n'], r['form'], r['pre'], r['post'], r['gain'], r['g'], r['dose']] + [r['topics'][t][0] for t in TOPICS] + [r['topics'][t][1] for t in TOPICS])
                cell = lambda v: ('"' + str(v).replace('"', '""') + '"') if re.search(r'[",\n]', str(v)) else ('' if v is None else str(v))
                self.send('\ufeff' + '\n'.join(','.join(cell(c) for c in row) for row in L), 'text/csv')
            else: self.send_error(404)
    else: return False
    return True
def t_post(self, d):
    if self.path in ('/api/t/save', '/api/t/submit'):
        sec, name, cid = str(d.get('sec', ''))[:60], str(d.get('name', ''))[:60], str(d.get('cid', ''))[:40]
        with lock:
            ok = is_roster(sec, name) and t_claim_ok(sec, name, cid) and t_student_post(sec, name, d, self.path == '/api/t/submit')
        self.send(json.dumps({'ok': bool(ok)}))
    elif self.path == '/api/t/logout':   # a student logs out: free the name so it can be used again on any device
        sec, name, cid = str(d.get('sec', ''))[:60], str(d.get('name', ''))[:60], str(d.get('cid', ''))[:40]
        with lock:
            c = TCLAIM.get((sec, name))
            if c and c[0] == cid:
                TCLAIM.pop((sec, name), None)
                for ph_ in ('pre', 'post'): TOPEN.pop((ph_, skey(sec, name)), None)
        self.send(json.dumps({'ok': True}))
    elif self.path == '/api/t/hostact':
        if not keyok(d.get('key', '')): self.send_error(403); return True
        with lock: msg = t_host_act(d)
        self.send(json.dumps({'ok': True, 'msg': msg}))
    else: return False
    return True
_h_get, _h_post = H._get, H._post
def _hook_get(self):
    u = urlparse(self.path)
    if u.path == '/test' or u.path.startswith('/test/') or u.path.startswith('/api/t/'):
        if t_get(self, u, parse_qs(u.query)): return
    _h_get(self)
def _hook_post(self):
    if self.path.startswith('/api/t/'):
        try: d = json.loads(self.rfile.read(int(self.headers.get('Content-Length', 0))) or '{}')
        except Exception: d = {}
        if t_post(self, d if isinstance(d, dict) else {}): return
        self.send_error(404); return
    _h_post(self)
H._get, H._post = _hook_get, _hook_post



if __name__ == '__main__':
    pin_msg = setup_pin()
    print('\n  Guadalupe NHS Numeracy Drill running\n')
    for ip in IPS: print('  STUDENTS join:  http://%s:%d' % (ip, PORT))
    print('  TEACHER (you):  http://%s:%d/host   <- asks for your PIN' % (IPS[0], PORT))
    for ip in IPS: print('  PRE/POST TEST:  http://%s:%d/test   (students)  ·  http://%s:%d/test/host   (teacher)' % (ip, PORT, ip, PORT))
    print(pin_msg + '\n')
    print('  Ctrl+C to stop. Data is saved in gnhs-data.json\n')
    srv = make_server(PORT)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print('\n\n  Server stopped. Data saved in gnhs-data.json\n')
        try: _write_now(); t_write_now()
        except Exception: pass
        try: srv.server_close()
        except Exception: pass
