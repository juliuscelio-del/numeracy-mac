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
    webview.create_window(_title, _url, width=1200, height=820, min_size=(700, 500), text_select=True)
    webview.start()
    sys.exit(0)

import io, os, subprocess, threading, base64, webbrowser
import tkinter as tk
from tkinter import messagebox, ttk
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
UP_TO_DATE_MS, NOTICE_MS = 15000, 4000


class Popup:
    """A centered card shown over the app window. One card at a time.
    By default the card is LOCKED: no X button, the window's own close button is disabled,
    and the main window cannot be clicked until the card closes (timer or button)."""

    def __init__(self, root):
        self.root = root
        self.win = None
        self.msg = None
        self.pbar = None
        self._timer = None

    def close(self):
        if self._timer is not None:
            try:
                self.root.after_cancel(self._timer)
            except Exception:
                pass
            self._timer = None
        if self.win is not None:
            try:
                self.win.grab_release()
            except Exception:
                pass
            try:
                self.win.destroy()
            except Exception:
                pass
        self.win = self.msg = self.pbar = None

    def _click(self, b):
        self.close()
        if b.get("onClick"):
            b["onClick"]()

    def set_progress(self, pct, text=None):
        if self.pbar is not None and str(self.pbar.cget("mode")) == "determinate":
            self.pbar["value"] = pct
        if self.msg is not None and text:
            self.msg.config(text=text)

    def show(self, title, message=None, icon="check", spinner=False, progress=False, buttons=(), auto_ms=0, lock=True):
        self.close()
        w = tk.Toplevel(self.root)
        self.win = w
        w.title("Update")
        w.configure(bg=CARD)
        w.resizable(False, False)
        # locked: the window's own close button does nothing
        w.protocol("WM_DELETE_WINDOW", (lambda: None) if lock else self.close)
        try:
            w.transient(self.root)
        except Exception:
            pass
        tk.Frame(w, bg=GREEN_D, height=6).pack(fill="x")
        body = tk.Frame(w, bg=CARD)
        body.pack(padx=34, pady=(20, 26))

        if spinner or progress:
            self.pbar = ttk.Progressbar(body, length=210, maximum=100,
                                        mode="determinate" if progress else "indeterminate")
            self.pbar.pack(pady=(6, 18))
            if not progress:
                self.pbar.start(12)
        else:
            c = tk.Canvas(body, width=68, height=68, bg=CARD, highlightthickness=0)
            c.pack(pady=(0, 12))
            c.create_oval(2, 2, 66, 66, fill=WARN if icon == "alert" else GREEN_D, outline="")
            kw = dict(fill="white", width=5, capstyle=tk.ROUND, joinstyle=tk.ROUND)
            if icon == "download":
                c.create_line(34, 16, 34, 42, **kw)
                c.create_line(22, 32, 34, 44, 46, 32, **kw)
                c.create_line(20, 53, 48, 53, **kw)
            elif icon == "alert":
                c.create_line(34, 18, 34, 38, **kw)
                c.create_oval(31, 45, 37, 51, fill="white", outline="")
            else:
                c.create_line(20, 36, 30, 46, 48, 24, **kw)

        tk.Label(body, text=title, font=("Helvetica", 15, "bold"), fg="#1b4332", bg=CARD,
                 wraplength=290, justify="center").pack()
        if message:
            self.msg = tk.Label(body, text=message, font=("Helvetica", 12), fg="#5b6b61", bg=CARD,
                                wraplength=290, justify="center")
            self.msg.pack(pady=(8, 0))

        if buttons:
            row = tk.Frame(body, bg=CARD)
            row.pack(pady=(18, 0))
            for b in buttons:
                prim = bool(b.get("primary"))
                lab = tk.Label(row, text=b["label"], font=("Helvetica", 13, "bold"),
                               fg="white" if prim else "#2e5d3a", bg=GREEN_D if prim else "white",
                               padx=20, pady=8, cursor="hand2",
                               highlightthickness=1, highlightbackground=GREEN_D if prim else "#cfe3d4")
                lab.pack(side="left", padx=5)
                lab.bind("<Button-1>", lambda e, b=b: self._click(b))

        # The X button only exists when the popup is NOT locked
        if not lock:
            x = tk.Label(w, text="\u00d7", font=("Helvetica", 20), fg="#8a9a8f", bg=CARD, cursor="hand2")
            x.place(relx=1.0, x=-12, y=8, anchor="ne")
            x.bind("<Button-1>", lambda e: self.close())

        if auto_ms:
            bar = tk.Frame(w, bg=GREEN_L)
            bar.place(relx=0, rely=1.0, anchor="sw", relwidth=1.0, height=5)
            steps = max(1, auto_ms // 100)

            def tick(i=0):
                if self.win is not w:
                    return
                if i >= steps:
                    self.close()
                    return
                bar.place_configure(relwidth=1.0 - i / float(steps))
                self._timer = self.root.after(100, lambda: tick(i + 1))
            tick()

        w.update_idletasks()
        try:
            px = self.root.winfo_rootx() + (self.root.winfo_width() - w.winfo_reqwidth()) // 2
            py = self.root.winfo_rooty() + (self.root.winfo_height() - w.winfo_reqheight()) // 2
            w.geometry("+%d+%d" % (max(px, 0), max(py, 0)))
        except Exception:
            pass
        try:
            w.lift()
            w.attributes("-topmost", True)
        except Exception:
            pass
        # locked: block all clicks on the main window until this card closes
        if lock:
            try:
                w.update()
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
        self.root.after(700, self.update_flow)       # update popup every time the app opens
        self.root.mainloop()

    # ---------- updates
    def update_flow(self):
        pop = self.popup
        pop.show(CHECKING_TITLE, spinner=True)

        def work():
            try:
                res = (None, app_updater.latest_release())
            except app_updater.UpdateError as e:
                res = (e, None)
            except Exception as e:
                res = (app_updater.UpdateError("error", str(e)), None)
            try:
                self.root.after(0, lambda: self._update_result(res))
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

    def clear(self):
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
            self.open_page(url, "Numeracy Drill - Student")

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
