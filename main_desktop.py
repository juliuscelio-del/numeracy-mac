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
from tkinter import messagebox
from PIL import Image, ImageTk

import app_core as core

try:
    from logo_data import LOGO_B64
    LOGO_PNG = base64.b64decode(LOGO_B64)
except Exception:
    LOGO_PNG = None

BG, BLUE, INK, MUTED, RED, GREEN, PURPLE = "#e4f1ff", "#2f6df6", "#12306b", "#5f78a8", "#ff5a5f", "#1fc76a", "#8b5cf6"


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
        self.root.mainloop()

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

    def quit(self):
        self._scan_token = None
        if self.host is not None:
            if not messagebox.askyesno(core.APP_NAME, "Stop the drill for the students and close?"):
                return
            self.host.stop()
        for p in self.pages:
            try: p.terminate()
            except Exception: pass
        self.root.destroy()


if __name__ == "__main__":
    App()
