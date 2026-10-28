"""GNHS Numeracy Drill: self-updater (GitHub Releases). No GUI code in this file.

The update check does NOT use the GitHub API (which allows only 60 requests per hour per IP, so a whole
school on one Wi-Fi hits the limit). Instead it reads the redirect of the public 'latest release' page,
which carries the newest tag, and builds the download links from the fixed file names."""
import os, sys, ssl, subprocess, tempfile
from urllib.request import Request, urlopen, build_opener, HTTPRedirectHandler, HTTPSHandler
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin, unquote

REPO = "juliuscelio-del/numeracy-mac"
RELEASES_PAGE = "https://github.com/%s/releases/latest" % REPO
DOWNLOAD_BASE = "https://github.com/%s/releases/download" % REPO

# file names the GitHub build uploads to every release
WIN_FILE = "GNHS-Numeracy-Drill.exe"
MAC_FILE = "GNHS-Numeracy-Drill-Mac.dmg"

try:
    from app_version import VERSION          # written by the GitHub build (1.1.<build number>)
except Exception:
    VERSION = "0.0.0"

IS_WIN = sys.platform.startswith("win")
IS_MAC = sys.platform == "darwin"


class UpdateError(Exception):
    def __init__(self, kind, detail=""):
        Exception.__init__(self, detail or kind)
        self.kind = kind                      # "offline" | "rate" | "error"


# ---------- network
def _ctx():
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return ssl.create_default_context()


def _open(url, timeout, api=True):
    headers = {"User-Agent": "GNHS-Numeracy-Updater"}
    return urlopen(Request(url, headers=headers), timeout=timeout, context=_ctx())


class _NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, *a, **k):
        return None                           # do not follow: we only want the Location header


def latest_release(timeout=8):
    """Returns the latest release as a dict (tag_name, html_url, assets), or None if no release exists yet.
    Uses the public release page, not the rate-limited API."""
    opener = build_opener(_NoRedirect, HTTPSHandler(context=_ctx()))
    req = Request(RELEASES_PAGE, headers={"User-Agent": "GNHS-Numeracy-Updater"})
    try:
        opener.open(req, timeout=timeout).close()
        return None                           # answered without a redirect: no release yet
    except HTTPError as e:
        if e.code in (301, 302, 303, 307, 308):
            loc = urljoin(RELEASES_PAGE, e.headers.get("Location", "") or "")
            if "/releases/tag/" not in loc:
                return None                   # redirected to the releases list: nothing published yet
            tag = unquote(loc.rstrip("/").split("/")[-1])
            base = "%s/%s/" % (DOWNLOAD_BASE, tag)
            return {
                "tag_name": tag,
                "html_url": loc,
                "assets": [
                    {"name": WIN_FILE, "browser_download_url": base + WIN_FILE},
                    {"name": MAC_FILE, "browser_download_url": base + MAC_FILE},
                ],
            }
        if e.code == 404:
            return None
        if e.code in (403, 429):
            raise UpdateError("rate", str(e))
        raise UpdateError("error", str(e))
    except URLError as e:
        if isinstance(getattr(e, "reason", None), ssl.SSLError):
            raise UpdateError("error", str(e))
        raise UpdateError("offline", str(e))
    except Exception as e:
        raise UpdateError("error", str(e))


# ---------- versions / assets
def _parts(v):
    out = []
    for p in str(v).lstrip("vV").split(".")[:3]:
        digits = "".join(c for c in p if c.isdigit())
        out.append(int(digits) if digits else 0)
    while len(out) < 3:
        out.append(0)
    return out


def is_newer(a, b):
    return _parts(a) > _parts(b)


def find_asset(release):
    ext = ".exe" if IS_WIN else ".dmg"
    for a in (release or {}).get("assets", []) or []:
        if str(a.get("name", "")).lower().endswith(ext):
            return a
    return None


# ---------- where is the installed app?
def app_path():
    """Path of the running app (the .exe on Windows, the .app bundle on Mac). None when run from source."""
    if not getattr(sys, "frozen", False):
        return None
    if IS_WIN:
        return os.path.abspath(sys.executable)
    if IS_MAC:
        p = os.path.abspath(os.path.join(os.path.dirname(sys.executable), "..", ".."))
        return p if p.endswith(".app") else None
    return None


def can_install():
    p = app_path()
    return bool(p) and os.access(os.path.dirname(p), os.W_OK)


def download_target():
    if IS_WIN:
        return app_path() + ".new"
    return os.path.join(tempfile.gettempdir(), "GNHS-Numeracy-Update.dmg")


def download(url, dest, progress=None, timeout=30):
    tmp = dest + ".part"
    try:
        with _open(url, timeout, api=False) as r, open(tmp, "wb") as f:
            total = int(r.headers.get("Content-Length") or 0)
            done = 0
            while True:
                chunk = r.read(65536)
                if not chunk:
                    break
                f.write(chunk)
                done += len(chunk)
                if progress:
                    progress(done, total)
        if total and done != total:
            raise UpdateError("error", "incomplete download")
        os.replace(tmp, dest)
    except UpdateError:
        _rm(tmp)
        raise
    except Exception as e:
        _rm(tmp)
        raise UpdateError("error", str(e))


def _rm(p):
    try:
        os.remove(p)
    except Exception:
        pass


# ---------- install (the helper keeps running after this app quits)
def _clean_env():
    env = dict(os.environ)
    env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"      # new copy must not reuse this copy's temp folder
    env.pop("_MEIPASS2", None)
    return env


def windows_script(new_file, exe):
    return ("@echo off\r\nchcp 65001 >nul\r\nset N=0\r\n:retry\r\nping 127.0.0.1 -n 2 >nul\r\n"
            'move /y "%s" "%s" >nul 2>&1\r\n'
            "if not errorlevel 1 goto done\r\n"
            "set /a N+=1\r\n"
            "if %%N%% LSS 60 goto retry\r\n"
            "exit /b 1\r\n"
            ":done\r\n"
            'start "" "%s"\r\n'
            '(goto) 2>nul & del "%%~f0"\r\n') % (new_file, exe, exe)


def install_windows(new_file):
    exe = app_path()
    bat = os.path.join(tempfile.gettempdir(), "gnhs_numeracy_update.bat")
    with open(bat, "w", encoding="utf-8", newline="") as f:
        f.write(windows_script(new_file, exe))
    # waits for this app to close, swaps the .exe, starts the new one
    subprocess.Popen(["cmd", "/c", bat], creationflags=0x00000008 | 0x08000000,
                     close_fds=True, env=_clean_env(), cwd=os.path.dirname(exe))


MAC_SCRIPT = r'''
while kill -0 "$1" 2>/dev/null; do sleep 0.5; done
ditto "$3" "$2.updating" && rm -rf "$2" && mv "$2.updating" "$2" && xattr -cr "$2"
rm -rf "$4" "$5"
open "$2"
'''


def install_mac(dmg):
    bundle = app_path()
    mnt = tempfile.mkdtemp(prefix="gnhsmnt")
    stage = tempfile.mkdtemp(prefix="gnhsnew")
    subprocess.run(["hdiutil", "attach", "-nobrowse", "-quiet", "-readonly", "-mountpoint", mnt, dmg],
                   check=True, timeout=180)
    try:
        src = None
        for n in os.listdir(mnt):
            if n.endswith(".app"):
                src = os.path.join(mnt, n)
                break
        if not src:
            raise UpdateError("error", "no app inside the download")
        newapp = os.path.join(stage, os.path.basename(src))
        subprocess.run(["ditto", src, newapp], check=True, timeout=300)
    finally:
        subprocess.run(["hdiutil", "detach", "-quiet", "-force", mnt])
    subprocess.Popen(["/bin/sh", "-c", MAC_SCRIPT, "sh", str(os.getpid()), bundle, newapp, stage, dmg],
                     start_new_session=True, close_fds=True)


def install(downloaded):
    if IS_WIN:
        install_windows(downloaded)
    elif IS_MAC:
        install_mac(downloaded)
    else:
        raise UpdateError("error", "unsupported system")
