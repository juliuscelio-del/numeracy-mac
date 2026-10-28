"""Guadalupe NHS Numeracy Drill: desktop app (Windows + Mac).
Opens a start screen: TEACHER (PIN, runs the drill for the class) or STUDENT (joins the teacher automatically)."""
import sys
if "--webview" in sys.argv:
    # Child mode: show one page in a native app window (WebKit on Mac, Edge WebView2 on Windows), then exit.
    _i = sys.argv.index("--webview")
    _url = sys.argv[_i + 1]
    _title = sys.argv[_i + 2] if len(sys.argv) > _i + 2 else "Numeracy Drill"
    import webview
    try:
        webview.settings["ALLOW_DOWNLOADS"] = True   # PDF / report downloads
    except Exception:
        pass
    try:
        webview.create_window(_title, _url, width=1200, height=820, min_size=(700, 500), text_select=True,
                              maximized=True)       # open filling the whole screen
    except TypeError:                               # older pywebview without 'maximized'
        webview.create_window(_title, _url, width=1200, height=820, min_size=(700, 500), text_select=True)
    webview.start()
    sys.exit(0)

import io, os, subprocess, threading, base64, webbrowser, time
import tkinter as tk
from tkinter import messagebox, ttk
from tkinter import font as tkfont
from PIL import Image, ImageTk

import app_core as core
import app_updater

try:
    from logo_data import LOGO_B64
    LOGO_PNG = base64.b64decode(LOGO_B64)
except Exception:
    LOGO_PNG = None

BG, BLUE, INK, MUTED, RED, GREEN, PURPLE = "#e4f1ff", "#2f6df6", "#12306b", "#5f78a8", "#ff5a5f", "#1fc76a", "#8b5cf6"

# ---- update popup (same look and wording as the GNHS Quiz app)
GREEN_D, GREEN_L, WARN, CARD = "#2e7d32", "#66bb6a", "#ef6c00", "#f0f9f2"
CHECKING_TITLE = "paabot kadali....mangita tag update..."
UPTODATE_TITLE = "Okie pa ag version. Updated pa ne. Padajun gamit"
UP_TO_DATE_MS, NOTICE_MS, SEARCH_MS = 5000, 4000, 10000   # 'up to date' shows 5 s; the searching popup shows at least 10 s


# ---- update popup look: colorful gradient card
def _rgb(c):
    return tuple(int(c[i:i + 2], 16) for i in (1, 3, 5))


def _mix(c1, c2, t):
    a, b = _rgb(c1), _rgb(c2)
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def _gradient(cv, x0, y0, x1, y1, c1, c2):
    """Left-to-right color gradient drawn as thin strips."""
    span = max(1, x1 - x0)
    for x in range(0, span, 2):
        cv.create_rectangle(x0 + x, y0, x0 + x + 2, y1, fill=_mix(c1, c2, x / float(span)), outline="")


def _round_rect(cv, x0, y0, x1, y1, r, **kw):
    pts = [x0 + r, y0, x0 + r, y0, x1 - r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y0 + r, x1, y1 - r,
           x1, y1 - r, x1, y1, x1 - r, y1, x1 - r, y1, x0 + r, y1, x0 + r, y1, x0, y1, x0, y1 - r,
           x0, y1 - r, x0, y0 + r, x0, y0 + r, x0, y0]
    return cv.create_polygon(pts, smooth=True, **kw)


# kind -> (gradient start, gradient end, accent color)
THEMES = {
    "check":    ("#11998e", "#38ef7d", "#19b36b"),   # green / mint: all good
    "download": ("#2f6df6", "#8b5cf6", "#4f6df0"),   # blue / purple: update available
    "alert":    ("#ff9a3c", "#ff5a5f", "#ff6b4a"),   # orange / coral: problem
    "spin":     ("#36d1dc", "#5b86e5", "#3f8fe0"),   # cyan / blue: searching
}
INK_T, MUTED_T = "#12306b", "#5f78a8"


class Popup:
    """A centered, colorful card shown over the app window. One card at a time.
    By default the card is LOCKED: no X button, no title bar, the window's own close button is disabled,
    and the main window cannot be clicked until the card closes (timer or button)."""
    W = 380

    def __init__(self, root):
        self.root = root
        self.win = None
        self.msg = None
        self.pbar = None
        self._cover = None
        self._pw = 0
        self._timer = None
        self._anim = None

    def close(self):
        for attr in ("_timer", "_anim"):
            t = getattr(self, attr)
            if t is not None:
                try:
                    self.root.after_cancel(t)
                except Exception:
                    pass
                setattr(self, attr, None)
        if self.win is not None:
            try:
                self.win.grab_release()
            except Exception:
                pass
            try:
                self.win.destroy()
            except Exception:
                pass
        self.win = self.msg = self.pbar = self._cover = None

    def _click(self, b):
        self.close()
        if b.get("onClick"):
            b["onClick"]()

    def set_progress(self, pct, text=None):
        if self.pbar is not None and self._cover is not None:
            pct = max(0, min(100, pct))
            try:
                self.pbar.coords(self._cover, int(self._pw * pct / 100.0), 0, self._pw, 14)
            except tk.TclError:
                pass
        if self.msg is not None and text:
            self.msg.config(text=text)

    def _button(self, parent, b, accent):
        prim = bool(b.get("primary"))
        font = tkfont.Font(root=self.root, family="Helvetica", size=12, weight="bold")
        bw, bh = font.measure(b["label"]) + 60, 42
        cv = tk.Canvas(parent, width=bw + 4, height=bh + 4, bg="white", highlightthickness=0, cursor="hand2")
        base = accent if prim else "white"
        hover = _mix(accent, "#000000", 0.14) if prim else _mix(accent, "#ffffff", 0.88)
        shape = _round_rect(cv, 2, 2, bw + 2, bh + 2, 20, fill=base, outline=accent, width=2)
        cv.create_text((bw + 4) // 2, (bh + 4) // 2, text=b["label"], font=font, fill="white" if prim else accent)
        cv.bind("<Enter>", lambda e: cv.itemconfigure(shape, fill=hover))
        cv.bind("<Leave>", lambda e: cv.itemconfigure(shape, fill=base))
        cv.bind("<Button-1>", lambda e: self._click(b))
        return cv

    def show(self, title, message=None, icon="check", spinner=False, progress=False, buttons=(), auto_ms=0, lock=True):
        self.close()
        kind = "spin" if spinner else ("download" if progress else icon)
        c1, c2, accent = THEMES.get(kind, THEMES["check"])
        w = tk.Toplevel(self.root)
        self.win = w
        w.title("Update")
        w.configure(bg=c1)                       # the 2px frame around the card takes the theme color
        w.resizable(False, False)
        # locked: remove the title bar completely so no X / close button is visible at all
        if lock:
            try:
                if sys.platform.startswith("win"):
                    w.overrideredirect(True)
                elif sys.platform == "darwin":
                    w.tk.call("::tk::unsupported::MacWindowStyle", "style", w._w, "plain", "none")
            except Exception:
                pass
        # locked: the window's own close button does nothing (backup in case the title bar stays)
        w.protocol("WM_DELETE_WINDOW", (lambda: None) if lock else self.close)
        try:
            w.transient(self.root)
        except Exception:
            pass

        CW = self.W - 4
        card = tk.Frame(w, bg="white")
        card.pack(padx=2, pady=2)

        # ---- gradient header with the round icon badge
        BH, R = 84, 36
        H = BH + R + 14
        cv = tk.Canvas(card, width=CW, height=H, bg="white", highlightthickness=0)
        cv.pack()
        _gradient(cv, 0, 0, CW, BH, c1, c2)
        cv.create_oval(-40, -55, 80, 45, fill=_mix(c1, "#ffffff", 0.22), outline="")
        cv.create_oval(CW - 120, -10, CW + 40, 120, fill=_mix(c2, "#ffffff", 0.2), outline="")
        cv.create_oval(CW // 2 - 40, -70, CW // 2 + 60, 20, fill=_mix(c1, c2, 0.5), outline="")
        cv.create_rectangle(0, BH, CW, H, fill="white", outline="")       # clip the decoration to the banner
        cx, cy = CW // 2, BH
        cv.create_oval(cx - R - 9, cy - R - 4, cx + R + 9, cy + R + 12, fill="#e9eef7", outline="")   # soft shadow
        cv.create_oval(cx - R - 6, cy - R - 6, cx + R + 6, cy + R + 6, fill="white", outline="")      # white ring
        arc = None
        if kind == "spin":
            cv.create_oval(cx - R + 8, cy - R + 8, cx + R - 8, cy + R - 8, outline="#dfe9fb", width=6)
            arc = cv.create_arc(cx - R + 8, cy - R + 8, cx + R - 8, cy + R - 8, start=90, extent=110,
                                style="arc", outline=accent, width=6)
        else:
            cv.create_oval(cx - R, cy - R, cx + R, cy + R, fill=accent, outline="")
            kw = dict(fill="white", width=6, capstyle=tk.ROUND, joinstyle=tk.ROUND)
            if kind == "download":
                cv.create_line(cx, cy - 17, cx, cy + 8, **kw)
                cv.create_line(cx - 12, cy - 2, cx, cy + 10, cx + 12, cy - 2, **kw)
                cv.create_line(cx - 15, cy + 19, cx + 15, cy + 19, **kw)
            elif kind == "alert":
                cv.create_line(cx, cy - 17, cx, cy + 4, **kw)
                cv.create_oval(cx - 4, cy + 11, cx + 4, cy + 19, fill="white", outline="")
            else:
                cv.create_line(cx - 15, cy + 1, cx - 5, cy + 11, cx + 15, cy - 10, **kw)
        if not lock:                                                       # the X only exists when NOT locked
            cv.create_text(CW - 18, 16, text="\u00d7", fill="white", font=("Helvetica", 20, "bold"), tags="x")
            cv.tag_bind("x", "<Button-1>", lambda e: self.close())
            cv.configure(cursor="arrow")

        # ---- text
        tk.Label(card, text=title, font=("Helvetica", 15, "bold"), fg=INK_T, bg="white",
                 wraplength=CW - 64, justify="center").pack(padx=32, pady=(8, 0))
        if message:
            self.msg = tk.Label(card, text=message, font=("Helvetica", 12), fg=MUTED_T, bg="white",
                                wraplength=CW - 64, justify="center")
            self.msg.pack(padx=32, pady=(8, 0))

        # ---- colorful progress bar (download)
        if progress:
            self._pw = CW - 90
            bar = tk.Canvas(card, width=self._pw, height=14, bg="white", highlightthickness=0)
            bar.pack(pady=(16, 0))
            _gradient(bar, 0, 0, self._pw, 14, c1, c2)
            self._cover = bar.create_rectangle(0, 0, self._pw, 14, fill="#e6ecfa", outline="")
            self.pbar = bar

        # ---- buttons
        if buttons:
            row = tk.Frame(card, bg="white")
            row.pack(pady=(18, 0))
            for b in buttons:
                self._button(row, b, accent).pack(side="left", padx=6)

        tk.Frame(card, bg="white", height=24).pack()

        # ---- auto-close countdown strip (gradient that shrinks)
        if auto_ms:
            cb = tk.Canvas(card, width=CW, height=7, bg="white", highlightthickness=0)
            cb.pack()
            _gradient(cb, 0, 0, CW, 7, c1, c2)
            cover = cb.create_rectangle(CW, 0, CW, 7, fill="white", outline="")
            steps = max(1, auto_ms // 100)

            def tick(i=0):
                if self.win is not w:
                    return
                if i >= steps:
                    self.close()
                    return
                cb.coords(cover, int(CW * (1.0 - i / float(steps))), 0, CW, 7)
                self._timer = self.root.after(100, lambda: tick(i + 1))
            tick()

        # ---- spinning ring while searching
        if arc is not None:
            def spin(a=90):
                if self.win is not w:
                    return
                try:
                    cv.itemconfigure(arc, start=a)
                except tk.TclError:
                    return
                self._anim = self.root.after(35, lambda: spin((a - 16) % 360))
            spin()

        w.update_idletasks()

        def place():
            # Center on the SCREEN. Give the full size AND position: a window without a title bar
            # (overrideredirect) on Windows ignores a bare "+x+y" and lands in the top-left corner.
            try:
                ww, hh = w.winfo_reqwidth(), w.winfo_reqheight()
                px = max((w.winfo_screenwidth() - ww) // 2, 0)
                py = max((w.winfo_screenheight() - hh) // 2, 0)
                w.geometry("%dx%d+%d+%d" % (ww, hh, px, py))
            except Exception:
                pass
        place()
        try:
            w.lift()
            w.attributes("-topmost", True)
        except Exception:
            pass
        # re-apply once the window is really on screen (Windows may reset it while mapping)
        try:
            w.after(30, place)
            w.after(250, place)
        except Exception:
            pass
        # locked: block all clicks on the main window until this card closes
        if lock:
            try:
                w.update()
                place()                               # window is on screen now: set the centered position again
                w.grab_set()
                w.focus_force()
            except Exception:
                pass


def make_qr(text):
    import qrcode
    qr = qrcode.QRCode(border=2, box_size=8, error_correction=qrcode.constants.ERROR_CORRECT_M)
    qr.add_data(text)
    qr.make(fit=True)
    img = qr.make_image(fill_color="#0a2a66", back_color="white")
    return getattr(img, "get_image", lambda: img)().convert("RGB")


def sweep_subnet(timeout=0.3):
    """Fallback when the broadcast is blocked (Windows firewall, some routers): ask every computer on the
    same network directly whether the drill is running on ports 8000-8009. Only outgoing connections are
    used, so no firewall permission is needed on the student laptop."""
    import socket, json
    from concurrent.futures import ThreadPoolExecutor
    from urllib.request import urlopen
    mine = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        mine.append(s.getsockname()[0])
        s.close()
    except Exception:
        pass
    try:
        mine += socket.gethostbyname_ex(socket.gethostname())[2]
    except Exception:
        pass
    bases = []
    for ip in mine:
        p = ip.split(".")
        if len(p) == 4 and not ip.startswith("127.") and not ip.startswith("169.254."):
            b = ".".join(p[:3])
            if b not in bases:
                bases.append(b)
    targets = [("%s.%d" % (b, h), port) for b in bases for h in range(1, 255) for port in range(core.DEFAULT_PORT, core.DEFAULT_PORT + 10)]

    def probe(t):
        ip, port = t
        try:
            c = socket.create_connection((ip, port), timeout=timeout)
            c.close()
        except Exception:
            return None
        try:
            j = json.loads(urlopen("http://%s:%d/api/t/boot" % (ip, port), timeout=1.5).read().decode("utf-8", "replace"))
            if "boot" in j:                      # only our drill server answers this
                return ("Teacher (%s)" % ip, "http://%s:%d" % (ip, port))
        except Exception:
            pass
        return None

    out = []
    try:
        with ThreadPoolExecutor(max_workers=120) as ex:
            for r in ex.map(probe, targets):
                if r and r not in out:
                    out.append(r)
    except Exception:
        pass
    return out


class App:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("%s - %s" % (core.SCHOOL, core.APP_NAME))
        self.root.configure(bg=BG)
        self.root.resizable(False, False)
        self.srv = None
        self.host = None
        self.pages = []
        self.logo_small = None
        self._scan_token = None      # identifies the student screen that is currently searching
        self.popup = Popup(self.root)
        if LOGO_PNG:
            try:
                pil = Image.open(io.BytesIO(LOGO_PNG)).convert("RGBA")
                self.root._icon = ImageTk.PhotoImage(pil)
                self.root.iconphoto(True, self.root._icon)
                self.logo_small = ImageTk.PhotoImage(pil.resize((84, 84), Image.LANCZOS))
            except Exception:
                pass
        self.body = None
        self.root.protocol("WM_DELETE_WINDOW", self.quit)
        self.home()
        self.center_root()                            # open in the middle of the screen
        self.root.after(700, self.update_flow)       # update popup every time the app opens
        self.root.mainloop()

    # ---------- updates
    def update_flow(self):
        pop = self.popup
        pop.show(CHECKING_TITLE, spinner=True)
        t0 = time.time()

        def work():
            try:
                res = (None, app_updater.latest_release())
            except app_updater.UpdateError as e:
                res = (e, None)
            except Exception as e:
                res = (app_updater.UpdateError("error", str(e)), None)
            # keep the "searching" popup on screen for at least SEARCH_MS, even if the check finishes sooner
            delay = max(0, SEARCH_MS - int((time.time() - t0) * 1000))
            try:
                self.root.after(delay, lambda: self._update_result(res))
            except Exception:
                pass
        threading.Thread(target=work, daemon=True).start()

    def _update_result(self, res):
        pop = self.popup
        err, rel = res
        cur = app_updater.VERSION
        if err is not None:
            if err.kind == "offline":
                pop.show("No internet connection",
                         "The app works offline. It will check again next time you open the app.",
                         icon="alert", auto_ms=NOTICE_MS)
            elif err.kind == "rate":
                pop.show("Couldn't check for updates", "Too many checks right now. Try again in a little while.",
                         icon="alert", auto_ms=NOTICE_MS)
            else:
                pop.show("Couldn't check for updates", "Check your internet connection.",
                         icon="alert", auto_ms=NOTICE_MS)
            return
        if not rel:
            pop.show(UPTODATE_TITLE, icon="check", auto_ms=UP_TO_DATE_MS)
            return
        latest = str(rel.get("tag_name") or "").lstrip("vV")
        asset = app_updater.find_asset(rel)
        if asset and app_updater.is_newer(latest, cur):
            # FORCED update: only the Update button, no "Later", no X
            pop.show("Update",
                     "Pislita ag update basin naa Updated na App (v%s \u2192 v%s)" % (cur, latest),
                     icon="download",
                     buttons=[{"label": "Update", "primary": True,
                               "onClick": lambda: self._update_download(rel, asset)}])
        else:
            pop.show(UPTODATE_TITLE, icon="check", auto_ms=UP_TO_DATE_MS)

    def _update_download(self, rel, asset):
        pop = self.popup
        page = rel.get("html_url") or app_updater.RELEASES_PAGE
        if not app_updater.can_install():
            webbrowser.open(page)        # running from source, or the app's folder is read-only
            return
        pop.show("Update", "Nag-download\u2026 0%", progress=True)

        def prog(done, total):
            pct = int(done * 100 / total) if total else 0
            try:
                self.root.after(0, lambda: pop.set_progress(pct, "Nag-download\u2026 %d%%" % pct))
            except Exception:
                pass

        def failed():
            # no "Later": the student can retry or open the download page
            pop.show("Couldn't update", "Open the download page and install the new version yourself.",
                     icon="alert",
                     buttons=[{"label": "Retry", "onClick": lambda: self._update_download(rel, asset)},
                              {"label": "Open page", "primary": True, "onClick": lambda: webbrowser.open(page)}])

        def work():
            try:
                dest = app_updater.download_target()
                app_updater.download(asset["browser_download_url"], dest, prog)
                self.root.after(0, lambda: pop.show("Update", "Nag-install ug nag-restart ang app\u2026 hulat kadali.", spinner=True))
                app_updater.install(dest)
                self.root.after(800, lambda: self.quit(force=True))
            except Exception:
                try:
                    self.root.after(0, failed)
                except Exception:
                    pass
        threading.Thread(target=work, daemon=True).start()

    # ---------- helpers
    def open_page(self, url, title="Numeracy Drill"):
        """Open the page inside an app window (a small helper process); fall back to the browser."""
        try:
            import webview  # noqa: F401  (only to check it is installed)
            cmd = [sys.executable]
            if not getattr(sys, "frozen", False):
                cmd.append(os.path.abspath(__file__))
            self.pages.append(subprocess.Popen(cmd + ["--webview", url, title]))
        except Exception:
            webbrowser.open(url)

    def open_student_page(self, url, title="Numeracy Drill"):
        """Student: the drill REPLACES the app window (one window on screen, not two).
        The start window is hidden while the drill is open and comes back when the drill window is closed."""
        try:
            import webview  # noqa: F401  (only to check it is installed)
            cmd = [sys.executable]
            if not getattr(sys, "frozen", False):
                cmd.append(os.path.abspath(__file__))
            proc = subprocess.Popen(cmd + ["--webview", url, title])
        except Exception:
            webbrowser.open(url)
            return
        self.pages.append(proc)
        self.popup.close()
        self.root.withdraw()                          # hide the start window while the drill is open

        def watch():
            if proc.poll() is None:
                self.root.after(500, watch)
                return
            try:
                self.pages.remove(proc)
            except ValueError:
                pass
            try:
                self.root.deiconify()                 # drill closed: bring the start window back
                self.home()
                self.center_root()
            except tk.TclError:
                pass
        watch()

    def center_root(self):
        """Put the app window in the middle of the screen."""
        try:
            self.root.update_idletasks()
            w, h = self.root.winfo_reqwidth(), self.root.winfo_reqheight()
            x = (self.root.winfo_screenwidth() - w) // 2
            y = (self.root.winfo_screenheight() - h) // 2 - 20
            self.root.geometry("+%d+%d" % (max(x, 0), max(y, 0)))
        except Exception:
            pass

    def clear(self):
        self.root.after_idle(self.center_root)     # keep the window centered when the screen changes size
        self._scan_token = None      # leaving a screen stops any search that was running on it
        if self.body is not None:
            self.body.destroy()
        self.body = tk.Frame(self.root, bg=BG)
        self.body.pack(padx=34, pady=22)
        head = tk.Frame(self.body, bg=BG)
        head.pack()
        if self.logo_small:
            lg = tk.Label(head, image=self.logo_small, bg=BG)
            lg.pack(side="left", padx=(0, 14))
        box = tk.Frame(head, bg=BG)
        box.pack(side="left")
        tk.Label(box, text=core.SCHOOL, font=("Helvetica", 24, "bold"), fg=BLUE, bg=BG).pack(anchor="w")
        tk.Label(box, text=core.APP_NAME, font=("Helvetica", 13), fg=MUTED, bg=BG).pack(anchor="w")
        return self.body

    def button(self, parent, text, color, cmd, width=26):
        b = tk.Label(parent, text=text, font=("Helvetica", 14, "bold"), fg="white", bg=color,
                     padx=18, pady=10, cursor="hand2", width=width)
        b.bind("<Button-1>", lambda e: cmd())
        return b

    def label(self, parent, text, size=12, color=INK, bold=False, mono=False):
        f = ("Courier" if mono else "Helvetica", size, "bold" if bold else "normal")
        return tk.Label(parent, text=text, font=f, fg=color, bg=BG)

    def entry(self, parent, show=None, width=22):
        e = tk.Entry(parent, font=("Helvetica", 16), width=width, justify="center", show=show,
                     relief="solid", bd=2)
        return e

    # ---------- screens
    def home(self):
        b = self.clear()
        self.label(b, "Who is using this app?", 17, INK, True).pack(pady=(18, 12))
        self.button(b, "I am the TEACHER (PIN)", BLUE, self.teacher_screen).pack(pady=6)
        self.button(b, "I am a STUDENT", GREEN, self.student_screen).pack(pady=6)
        self.label(b, "Teacher: runs the drill for the class.\nStudent: joins the teacher's drill automatically.", 11, MUTED).pack(pady=(14, 4))
        self.label(b, "Version %s" % app_updater.VERSION, 10, MUTED).pack(pady=(6, 0))

    def student_screen(self):
        b = self.clear()
        token = object()
        self._scan_token = token
        state = {"joined": False}

        self.label(b, "Join the teacher's drill", 17, INK, True).pack(pady=(16, 4))
        status = self.label(b, "Looking for your teacher...", 12, MUTED)
        status.pack()
        found = tk.Frame(b, bg=BG)
        found.pack(pady=6)

        def active():
            return self._scan_token is token

        def join_url(url, name=""):
            state["joined"] = True
            try:
                for w in found.winfo_children():
                    w.destroy()
                status.config(text="Joined %s. If you closed the window, press Search again." % (name or "your teacher"))
            except tk.TclError:
                pass
            self.open_student_page(url, "Numeracy Drill - Student")

        def show(res):
            if not active() or state["joined"]:
                return
            try:
                for w in found.winfo_children():
                    w.destroy()
                if len(res) == 1:
                    name, url = res[0]
                    status.config(text="Found %s. Joining..." % name)
                    join_url(url, name)                       # ONE teacher open: join without any tap
                elif res:
                    status.config(text="Several teachers are open. Tap yours:")
                    for name, url in res:
                        self.button(found, "%s  (%s)" % (name, url.replace("http://", "")), GREEN,
                                    lambda u=url, n=name: join_url(u, n), width=34).pack(pady=3)
                else:
                    status.config(text="Looking for your teacher... (waiting for the teacher to open the drill)")
                    self.root.after(300, scan)                 # keep searching until the teacher opens it
            except tk.TclError:
                pass

        def scan():
            if not active() or state["joined"]:
                return

            def work():
                res = core.discover(2.0)
                if not res:
                    res = sweep_subnet()              # broadcast heard nothing: ask the computers directly
                try:
                    self.root.after(0, lambda: show(res))
                except Exception:
                    pass
            threading.Thread(target=work, daemon=True).start()

        def search_again():
            state["joined"] = False
            try:
                for w in found.winfo_children():
                    w.destroy()
                status.config(text="Looking for your teacher...")
            except tk.TclError:
                return
            scan()

        self.button(b, "Search again", BLUE, search_again, width=16).pack(pady=(4, 10))
        self.label(b, "Not finding it? Type the address shown on the teacher's screen:", 11, MUTED).pack()
        e = self.entry(b, width=26)
        e.insert(0, "192.168.")
        e.pack(pady=6)
        err = self.label(b, "", 11, RED)
        err.pack()

        def join(_=None):
            url = core.clean_address(e.get())
            if not url or url.endswith("192.168.:8000"):
                err.config(text="Please type the full address.")
                return
            join_url(url)
        e.bind("<Return>", join)
        self.button(b, "Join", GREEN, join, width=16).pack(pady=6)
        self.button(b, "Back", MUTED, self.home, width=10).pack(pady=(2, 4))
        scan()

    def teacher_screen(self):
        b = self.clear()
        self.label(b, "Loading...", 14, MUTED).pack(pady=30)
        self.root.update()
        try:
            if self.srv is None:
                self.srv = core.load_server()
            first = not core.has_saved_pin(self.srv)
        except Exception as ex:
            messagebox.showerror(core.APP_NAME, "Could not start the drill:\n%s" % ex)
            self.home()
            return
        b = self.clear()
        self.label(b, "Create your teacher PIN" if first else "Teacher PIN", 17, INK, True).pack(pady=(16, 4))
        if first:
            self.label(b, "First time: choose a PIN (at least 4 characters).\nYou will use it to open the teacher dashboard.", 11, MUTED).pack(pady=(0, 8))
        e1 = self.entry(b, show="*")
        e1.pack(pady=4)
        e1.focus_set()
        e2 = None
        if first:
            self.label(b, "Type it again:", 11, MUTED).pack()
            e2 = self.entry(b, show="*")
            e2.pack(pady=4)
        err = self.label(b, "", 11, RED)
        err.pack()

        def go(_=None):
            pin = e1.get()
            if first:
                if len(pin) < 4:
                    err.config(text="At least 4 characters.")
                    return
                if pin != e2.get():
                    err.config(text="The two PINs do not match.")
                    return
                core.create_pin(self.srv, pin)
            elif not core.check_pin(self.srv, pin):
                err.config(text="Wrong PIN.")
                return
            self.start_host()
        e1.bind("<Return>", go)
        if e2 is not None:
            e2.bind("<Return>", go)
        self.button(b, "Start", BLUE, go).pack(pady=8)
        self.button(b, "Back", MUTED, self.home, width=10).pack(pady=(2, 4))

    def start_host(self):
        try:
            self.host = core.Host(self.srv)
        except Exception as ex:
            messagebox.showerror(core.APP_NAME, "Could not start the server:\n%s" % ex)
            self.home()
            return
        b = self.clear()
        urls = self.host.join_urls()
        self.label(b, "Drill is running", 17, GREEN, True).pack(pady=(14, 0))
        self.label(b, "Students: scan, or type this address\n(same Wi-Fi / hotspot as this computer)", 11, MUTED).pack(pady=(2, 6))
        try:
            photo = ImageTk.PhotoImage(make_qr(urls[0]).resize((230, 230), Image.NEAREST))
            card = tk.Frame(b, bg="white", highlightbackground=BLUE, highlightcolor=BLUE, highlightthickness=4)
            card.pack(pady=6)
            ql = tk.Label(card, image=photo, bg="white")
            ql.image = photo
            ql.pack(padx=8, pady=8)
        except Exception:
            pass
        for u in urls[:3]:
            self.label(b, u, 16, INK, True, mono=True).pack()
        nu = self.host.name_url()
        if nu:
            self.label(b, "or (does not change): " + nu, 11, MUTED).pack(pady=(2, 0))
        self.label(b, "Student laptops join automatically: no address needed.", 10, MUTED).pack(pady=(4, 0))
        self.label(b, "Your data is saved in:\n%s" % core.default_data_dir(), 9, MUTED).pack(pady=(8, 8))
        self.button(b, "Open TEACHER dashboard", BLUE, lambda: self.open_page(self.host.teacher_url(), "Numeracy Drill - Teacher")).pack(pady=4)
        self.button(b, "Open Pre / Post test (teacher)", PURPLE, lambda: self.open_page(self.host.test_url(), "Pre / Post test - Teacher")).pack(pady=4)
        self.button(b, "Stop and close", RED, self.quit).pack(pady=(10, 4))
        self.open_page(self.host.teacher_url(), "Numeracy Drill - Teacher")

    def quit(self, force=False):
        self._scan_token = None
        if self.host is not None:
            if not force and not messagebox.askyesno(core.APP_NAME, "Stop the drill for the students and close?"):
                return
            self.host.stop()
        for p in self.pages:
            try: p.terminate()
            except Exception: pass
        self.root.destroy()


if __name__ == "__main__":
    App()
