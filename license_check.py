"""LICENSE LOCK - GNHS Numeracy Drill (teacher side).
Copyright (c) Julius Celio. All Rights Reserved.

This is a Python port of server/license-check.js from the GNHS Quiz system, so BOTH apps
use the SAME approved-computers list and the SAME machine ID:

  * The machine ID is sha256(hardware id)[:24]. It is computed exactly like the Quiz app,
    so a computer approved for GNHS Quiz is automatically approved here too.
  * The list (allowlist.json) is SIGNED with Julius's private Ed25519 key. This file holds
    only the PUBLIC key, which can check a list but can never make one.
  * A copy of the list is bundled in the app (bundled_allowlist.py) and the newest signed
    copy is downloaded from GitHub (the same URL the Quiz app uses). Approving or removing
    a computer is done ONCE, with the Quiz tools (Manage-Teachers.command); it never needs
    a new version of this app.
  * The newest VALID list wins, so an old list can't be swapped in to "un-cancel" someone.

No third-party packages: the Ed25519 check is plain Python (RFC 8032), so the PyInstaller
build needs nothing extra.
"""
import os, sys, re, json, hashlib, base64, subprocess, uuid, ssl, calendar, time
from urllib.request import Request, urlopen

# Same PUBLIC key as GNHS Quiz (server/license-check.js). Safe to commit.
PUBLIC_KEY = """-----BEGIN PUBLIC KEY-----
MCowBQYDK2VwAyEAKK+r3ZINqQFuFxBDUcK+LbzN+cZSsm3m+ripw562DZw=
-----END PUBLIC KEY-----"""

# What gets signed. Must match admin/manage-allowlist.js in the Quiz project.
ALLOWLIST_PREFIX = "GNHS-ALLOWLIST-v1|"

# The Quiz project's published list (permanent GitHub release kept up to date by Julius).
ALLOWLIST_URL = "https://github.com/juliuscelio-del/quiz_server/releases/download/allowlist/allowlist.json"

CONTACT = "Julius Celio"


# ---------------------------------------------------------------- Ed25519 verify (RFC 8032, pure Python)
_P = 2 ** 255 - 19
_Q = 2 ** 252 + 27742317777372353535851937790883648493
_D = (-121665 * pow(121666, _P - 2, _P)) % _P
_SQRT_M1 = pow(2, (_P - 1) // 4, _P)


def _recover_x(y, sign):
    if y >= _P:
        return None
    x2 = (y * y - 1) * pow(_D * y * y + 1, _P - 2, _P) % _P
    if x2 == 0:
        return None if sign else 0
    x = pow(x2, (_P + 3) // 8, _P)
    if (x * x - x2) % _P:
        x = x * _SQRT_M1 % _P
    if (x * x - x2) % _P:
        return None
    if (x & 1) != sign:
        x = _P - x
    return x


def _decompress(b):
    if len(b) != 32:
        return None
    y = int.from_bytes(b, "little")
    sign = y >> 255
    y &= (1 << 255) - 1
    x = _recover_x(y, sign)
    if x is None:
        return None
    return (x, y, 1, x * y % _P)


def _add(a, b):
    A = (a[1] - a[0]) * (b[1] - b[0]) % _P
    B = (a[1] + a[0]) * (b[1] + b[0]) % _P
    C = 2 * a[3] * b[3] * _D % _P
    D = 2 * a[2] * b[2] % _P
    E, F, G, H = B - A, D - C, D + C, B + A
    return (E * F % _P, G * H % _P, F * G % _P, E * H % _P)


def _mul(s, pt):
    r = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            r = _add(r, pt)
        pt = _add(pt, pt)
        s >>= 1
    return r


def _same(a, b):
    return (a[0] * b[2] - b[0] * a[2]) % _P == 0 and (a[1] * b[2] - b[1] * a[2]) % _P == 0


_GY = 4 * pow(5, _P - 2, _P) % _P
_GX = _recover_x(_GY, 0)
_G = (_GX, _GY, 1, _GX * _GY % _P)


def ed25519_verify(public32, message, sig64):
    """True only if sig64 is a valid Ed25519 signature of message under public32."""
    try:
        if len(public32) != 32 or len(sig64) != 64:
            return False
        A = _decompress(public32)
        R = _decompress(sig64[:32])
        if A is None or R is None:
            return False
        s = int.from_bytes(sig64[32:], "little")
        if s >= _Q:
            return False
        h = int.from_bytes(hashlib.sha512(sig64[:32] + public32 + message).digest(), "little") % _Q
        return _same(_mul(s, _G), _add(R, _mul(h, A)))
    except Exception:
        return False


def _public_bytes():
    """The raw 32-byte key inside the PEM (SPKI = 12 header bytes + 32 key bytes)."""
    body = "".join(l for l in PUBLIC_KEY.strip().splitlines() if not l.startswith("-----"))
    der = base64.b64decode(body)
    return der[-32:]


# ---------------------------------------------------------------- machine ID (same as the Quiz app)
def data_dir():
    """Same folder the app uses for its data (see app_core.default_data_dir)."""
    env = os.environ.get("NUMERACY_DATA")
    if env:
        return env
    docs = os.path.join(os.path.expanduser("~"), "Documents")
    base = docs if os.path.isdir(docs) else os.path.expanduser("~")
    return os.path.join(base, "GNHS-Numeracy-Data")


def _run(args):
    kw = {}
    if sys.platform.startswith("win"):
        kw["creationflags"] = 0x08000000          # CREATE_NO_WINDOW: no console flash in the windowed app
    return subprocess.run(args, capture_output=True, text=True, timeout=10, **kw).stdout


def _hardware_id():
    """A stable hardware identifier. Deliberately NOT the MAC address or hostname (macOS rotates
    Wi-Fi MACs and renames hosts), so it never changes when the network does."""
    try:
        if sys.platform == "darwin":
            m = re.search(r'"IOPlatformUUID"\s*=\s*"([^"]+)"', _run(["/usr/sbin/ioreg", "-rd1", "-c", "IOPlatformExpertDevice"]))
            if m:
                return m.group(1)
        elif sys.platform.startswith("win"):
            m = re.search(r"MachineGuid\s+REG_SZ\s+([0-9a-fA-F-]+)",
                          _run([os.path.join(os.environ.get("SystemRoot", r"C:\Windows"), "System32", "reg.exe"), "query", r"HKLM\SOFTWARE\Microsoft\Cryptography", "/v", "MachineGuid"]))
            if m:
                return m.group(1)
        elif sys.platform.startswith("linux"):
            if os.path.exists("/etc/machine-id"):
                with open("/etc/machine-id", "r") as f:
                    v = f.read().strip()
                if v:
                    return v
    except Exception:
        pass
    # Fallback: a random ID made once and cached, so it stays stable across restarts.
    cache = os.path.join(data_dir(), ".machine-id-cache")
    try:
        if os.path.exists(cache):
            with open(cache, "r") as f:
                v = f.read().strip()
            if v:
                return v
    except Exception:
        pass
    v = str(uuid.uuid4())
    try:
        os.makedirs(data_dir(), exist_ok=True)
        with open(cache, "w") as f:
            f.write(v)
    except Exception:
        pass
    return v


_MACHINE_ID = None


def get_machine_id():
    """The 24-character ID Julius needs to approve this computer (identical to the Quiz app's)."""
    global _MACHINE_ID
    if _MACHINE_ID is None:
        _MACHINE_ID = hashlib.sha256(_hardware_id().encode("utf-8")).hexdigest()[:24]
    return _MACHINE_ID


# ---------------------------------------------------------------- the signed list
def _cached_path():
    return os.path.join(data_dir(), "allowlist.json")


def _issued_ts(s):
    """ISO time like 2026-11-18T03:57:43.081Z -> seconds since 1970 (None if unreadable)."""
    try:
        m = re.match(r"^(\d{4})-(\d\d)-(\d\d)T(\d\d):(\d\d):(\d\d)(?:\.(\d+))?Z$", str(s))
        if not m:
            return None
        y, mo, d, h, mi, se = [int(m.group(i)) for i in range(1, 7)]
        frac = float("0." + m.group(7)) if m.group(7) else 0.0
        return calendar.timegm((y, mo, d, h, mi, se)) + frac
    except Exception:
        return None


def _verified(lst):
    """Returns the list ONLY if its signature is valid, else None."""
    try:
        if not isinstance(lst, dict) or not isinstance(lst.get("machines"), list) or not lst.get("issuedAt") or not lst.get("sig"):
            return None
        if not all(isinstance(m, dict) and isinstance(m.get("id"), str) for m in lst["machines"]):
            return None
        if _issued_ts(lst["issuedAt"]) is None:
            return None
        ids = sorted(m["id"] for m in lst["machines"])
        payload = (ALLOWLIST_PREFIX + str(lst["issuedAt"]) + "|" + ",".join(ids)).encode("utf-8")
        sig = base64.b64decode(str(lst["sig"]), validate=True)
        return lst if ed25519_verify(_public_bytes(), payload, sig) else None
    except Exception:
        return None


def _read_file(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return _verified(json.load(f))
    except Exception:
        return None


def _read_bundled():
    """The copy that ships inside the app (bundled_allowlist.py), or allowlist.json next to the code."""
    try:
        import bundled_allowlist
        lst = _verified(bundled_allowlist.ALLOWLIST)
        if lst:
            return lst
    except Exception:
        pass
    return _read_file(os.path.join(os.path.dirname(os.path.abspath(__file__)), "allowlist.json"))


def best_allowlist():
    """Newest valid list wins, so an old list can't be swapped in to 'un-cancel' someone."""
    lists = [l for l in (_read_bundled(), _read_file(_cached_path())) if l]
    lists.sort(key=lambda l: _issued_ts(l["issuedAt"]), reverse=True)
    return lists[0] if lists else None


def _ctx():
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return ssl.create_default_context()


def refresh_allowlist(timeout=8):
    """Downloads the latest signed list and keeps it ONLY if the signature is valid and it is
    newer than what we already have. Returns True if a newer list was saved. Never raises."""
    if not ALLOWLIST_URL:
        return False
    try:
        req = Request(ALLOWLIST_URL, headers={"User-Agent": "GNHS-Numeracy-Teacher"})
        with urlopen(req, timeout=timeout, context=_ctx()) as r:      # follows GitHub's redirects
            if r.status != 200:
                return False
            body = r.read(1024 * 1024).decode("utf-8")
        incoming = _verified(json.loads(body))
        if not incoming:
            return False
        current = best_allowlist()
        if current and _issued_ts(incoming["issuedAt"]) <= _issued_ts(current["issuedAt"]):
            return False
        os.makedirs(data_dir(), exist_ok=True)
        tmp = _cached_path() + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(body)
        os.replace(tmp, _cached_path())
        return True
    except Exception:
        return False


# ---------------------------------------------------------------- the checks
def check():
    """(True, "") if this computer is approved, else (False, reason)."""
    lst = best_allowlist()
    if lst is None:
        return False, "The approved-computers list could not be verified."
    me = get_machine_id()
    if any(m["id"] == me for m in lst["machines"]):
        return True, ""
    return False, "This computer is not on the approved list."


def is_allowed():
    return check()[0]


class LicenseError(Exception):
    """Raised when something tries to start the teacher server on an unapproved computer."""


def require():
    ok, reason = check()
    if not ok:
        raise LicenseError(reason)
