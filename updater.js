/* GNHS Quiz — Student app updater
   Shows the update popup EVERY time the app opens, whether or not there is an update.
   - Android: checks GitHub Releases for a newer APK (also when the app returns
     from the background and internet comes back).
   - Windows: shows the status reported by electron-updater (see preload.js / main.js).
   Does nothing in a normal browser. */
(function () {
  var REPO = 'juliuscelio-del/GNHS_Quiz';
  var UP_TO_DATE_MS = 15000;        // "Okie pa ag version..." popup
  var NOTICE_MS = 4000;             // offline / error popups
  var FETCH_TIMEOUT_MS = 8000;      // don't hang forever on a network with no internet
  var RECHECK_MS = 10 * 60 * 1000;  // Android: re-check when resuming if last check was this long ago

  var CHECKING_TITLE = 'paabot kadali....mangita tag update...';
  var UPTODATE_TITLE = 'Okie pa ag version. Updated pa ne. Padajun gamit';

  var checking = false, finished = false, shownOffline = false, closeTimer = null, lastCheckAt = 0;

  // ── Capacitor plugins (no bundler needed) ─────────────────────────────────
  function plugin(name) {
    var C = window.Capacitor;
    return C && C.Plugins && C.Plugins[name] ? C.Plugins[name] : null;
  }

  // ── Styles ────────────────────────────────────────────────────────────────
  var css = '\
  #gnhs-upd{position:fixed;inset:0;z-index:2147483647;display:flex;align-items:center;justify-content:center;\
    background:rgba(15,40,25,.45);font-family:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}\
  #gnhs-upd .card{position:relative;width:min(340px,88vw);border-radius:22px;overflow:hidden;text-align:center;\
    padding:30px 24px 32px;background:linear-gradient(165deg,#fff 0%,#f0f9f2 100%);border:1px solid #dcefe2;\
    box-shadow:0 18px 50px rgba(20,60,35,.35);animation:gu-pop .28s ease-out both}\
  #gnhs-upd .card:before{content:"";position:absolute;top:0;left:0;right:0;height:6px;\
    background:linear-gradient(90deg,#2e7d32,#66bb6a,#2e7d32)}\
  @keyframes gu-pop{from{opacity:0;transform:scale(.93) translateY(10px)}to{opacity:1;transform:none}}\
  #gnhs-upd .x{position:absolute;top:12px;right:14px;width:30px;height:30px;border:none;border-radius:50%;\
    background:transparent;color:#8a9a8f;font-size:20px;line-height:30px;padding:0;cursor:pointer}\
  #gnhs-upd .icon{width:68px;height:68px;border-radius:50%;margin:0 auto 14px;display:flex;align-items:center;\
    justify-content:center;background:linear-gradient(135deg,#43a047,#2e7d32);box-shadow:0 8px 20px rgba(46,125,50,.35)}\
  #gnhs-upd .icon.warn{background:linear-gradient(135deg,#ffa726,#ef6c00);box-shadow:0 8px 20px rgba(239,108,0,.35)}\
  #gnhs-upd .ring{width:56px;height:56px;margin:6px auto 20px;border-radius:50%;border:5px solid #d7ecdc;\
    border-top-color:#2e7d32;animation:gu-spin .9s linear infinite}\
  @keyframes gu-spin{to{transform:rotate(360deg)}}\
  #gnhs-upd h2{margin:0 0 8px;font-size:19px;line-height:1.35;font-weight:700;color:#1b4332}\
  #gnhs-upd p{margin:0 0 4px;color:#5b6b61;font-size:14px;line-height:1.5}\
  #gnhs-upd .row{margin-top:18px;display:flex;gap:10px;justify-content:center}\
  #gnhs-upd .row button{padding:11px 26px;border:1px solid #cfe3d4;border-radius:999px;background:#fff;color:#2e5d3a;\
    font-size:15px;font-weight:600;cursor:pointer}\
  #gnhs-upd .row button.p{background:linear-gradient(135deg,#43a047,#2e7d32);color:#fff;border-color:#2e7d32;\
    box-shadow:0 6px 16px rgba(46,125,50,.35)}\
  #gnhs-upd .cd{position:absolute;left:0;bottom:0;height:5px;background:linear-gradient(90deg,#66bb6a,#2e7d32);\
    animation:gu-cd linear forwards}\
  @keyframes gu-cd{from{width:100%}to{width:0}}';

  function svg(path) {
    return '<svg width="34" height="34" viewBox="0 0 24 24" fill="none" stroke="#fff" stroke-width="2.6" ' +
           'stroke-linecap="round" stroke-linejoin="round">' + path + '</svg>';
  }
  var ICONS = {
    check: svg('<path d="M5 12.5l4.5 4.5L19 7.5"/>'),
    download: svg('<path d="M12 4v11M7 11l5 5 5-5M5 20h14"/>'),
    alert: svg('<path d="M12 6v7M12 17.5v.5"/>')
  };

  function addStyle() {
    if (document.getElementById('gnhs-upd-css')) return;
    var s = document.createElement('style');
    s.id = 'gnhs-upd-css';
    s.textContent = css;
    document.head.appendChild(s);
  }

  // ── Popup (centered on the screen) ────────────────────────────────────────
  function closePopup() {
    clearTimeout(closeTimer);
    var el = document.getElementById('gnhs-upd');
    if (el) el.remove();
  }

  function show(opts, autoCloseMs) {
    closePopup();
    addStyle();
    var overlay = document.createElement('div');
    overlay.id = 'gnhs-upd';
    var card = document.createElement('div');
    card.className = 'card';

    var x = document.createElement('button');
    x.className = 'x';
    x.innerHTML = '&times;';
    x.onclick = closePopup;
    card.appendChild(x);

    var top = document.createElement('div');
    if (opts.spinner) {
      top.className = 'ring';
    } else {
      top.className = 'icon' + (opts.icon === 'alert' ? ' warn' : '');
      top.innerHTML = ICONS[opts.icon] || ICONS.check;
    }
    card.appendChild(top);

    var h = document.createElement('h2');
    h.textContent = opts.title;
    card.appendChild(h);

    if (opts.message) {
      var p = document.createElement('p');
      p.className = 'msg';
      p.textContent = opts.message;
      card.appendChild(p);
    }

    if (opts.buttons && opts.buttons.length) {
      var row = document.createElement('div');
      row.className = 'row';
      opts.buttons.forEach(function (b) {
        var btn = document.createElement('button');
        btn.textContent = b.label;
        if (b.primary) btn.className = 'p';
        btn.onclick = function () { closePopup(); if (b.onClick) b.onClick(); };
        row.appendChild(btn);
      });
      card.appendChild(row);
    }

    if (autoCloseMs) {
      var cd = document.createElement('div');
      cd.className = 'cd';
      cd.style.animationDuration = autoCloseMs + 'ms';
      card.appendChild(cd);
      closeTimer = setTimeout(closePopup, autoCloseMs);
    }

    overlay.appendChild(card);
    document.body.appendChild(overlay);
  }

  function showUpToDate() {
    show({ title: UPTODATE_TITLE, icon: 'check' }, UP_TO_DATE_MS);
  }

  // ═════════════════════════════ WINDOWS ═══════════════════════════════════
  // main.js runs electron-updater and reports its status through preload.js.
  function startDesktop() {
    var D = window.gnhsUpdater;
    var progressShown = false;

    D.onStatus(function (s) {
      if (s.state !== 'progress') progressShown = false;

      if (s.state === 'checking') {
        show({ title: CHECKING_TITLE, spinner: true });
      } else if (s.state === 'none') {
        showUpToDate();
      } else if (s.state === 'available') {
        show({
          title: 'Update',
          message: 'Nag-download na sa update (v' + s.current + ' \u2192 v' + s.version + ')…',
          spinner: true
        });
      } else if (s.state === 'progress') {
        var msg = 'Nag-download… ' + s.percent + '%';
        var el = document.querySelector('#gnhs-upd p.msg');
        if (progressShown && el) {
          el.textContent = msg;               // update in place, no flicker
        } else {
          show({ title: 'Update', message: msg, spinner: true });
          progressShown = true;
        }
      } else if (s.state === 'downloaded') {
        show({
          title: 'Update',
          message: 'Na-download na ang v' + s.version + '. I-restart ang app para ma-install, o ma-install gihapon inig close sa app.',
          icon: 'download',
          buttons: [
            { label: 'Later' },
            { label: 'Restart now', primary: true, onClick: function () { D.install(); } }
          ]
        });
      } else if (s.state === 'error') {
        show({ title: "Couldn't check for updates", message: 'Check your internet connection.', icon: 'alert' }, NOTICE_MS);
      }
    });

    D.check();   // every time the app opens
  }

  // ═════════════════════════════ ANDROID ═══════════════════════════════════
  // Version compare (1.2.3 style)
  function isNewer(a, b) {
    var x = String(a).split('.').map(Number), y = String(b).split('.').map(Number);
    for (var i = 0; i < 3; i++) {
      if ((x[i] || 0) > (y[i] || 0)) return true;
      if ((x[i] || 0) < (y[i] || 0)) return false;
    }
    return false;
  }

  function openUrl(url) {
    var B = plugin('Browser');
    if (B && B.open) B.open({ url: url });
    else window.open(url, '_system');
  }

  // Fetch the latest release, with a timeout
  function fetchLatestRelease() {
    var ctrl = window.AbortController ? new AbortController() : null;
    var timer = ctrl ? setTimeout(function () { ctrl.abort(); }, FETCH_TIMEOUT_MS) : null;
    return fetch('https://api.github.com/repos/' + REPO + '/releases/latest', {
      headers: { Accept: 'application/vnd.github+json' },
      signal: ctrl ? ctrl.signal : undefined
    }).then(function (r) {
      if (timer) clearTimeout(timer);
      if (r.status === 404) return null;                       // no release published yet
      if (r.status === 403 || r.status === 429) {
        var e = new Error('rate limit'); e.rateLimited = true; throw e;
      }
      if (!r.ok) throw new Error('bad response');
      return r.json();
    }, function (err) {
      if (timer) clearTimeout(timer);
      throw err;
    });
  }

  function check() {
    if (finished || checking) return;
    var App = plugin('App');
    if (!App || !App.getInfo) return;        // not the installed app (e.g. opened in a browser)

    lastCheckAt = Date.now();

    if (!navigator.onLine) {
      if (!shownOffline) {
        shownOffline = true;
        show({ title: 'No internet connection',
               message: 'The app works offline. It will check again when internet returns.',
               icon: 'alert' }, NOTICE_MS);
      }
      return;
    }

    checking = true;
    show({ title: CHECKING_TITLE, spinner: true });

    Promise.all([App.getInfo(), fetchLatestRelease()]).then(function (res) {
      var current = res[0].version, release = res[1];
      finished = true;

      if (!release) { showUpToDate(); return; }

      var latest = String(release.tag_name || '').replace(/^v/, '');
      var apk = (release.assets || []).filter(function (a) { return /\.apk$/i.test(a.name); })[0];

      if (apk && isNewer(latest, current)) {
        show({
          title: 'Update',
          message: 'Pislita ag update basin naa Updated na App (v' + current + ' \u2192 v' + latest + ')',
          icon: 'download',
          buttons: [
            { label: 'Later' },
            { label: 'Update', primary: true, onClick: function () { openUrl(apk.browser_download_url); } }
          ]
        });
      } else {
        showUpToDate();
      }
    }).catch(function (err) {
      show({
        title: "Couldn't check for updates",
        message: err && err.rateLimited
          ? 'Too many checks right now. Try again in a little while.'
          : 'Check your internet connection.',
        icon: 'alert'
      }, NOTICE_MS);
    }).then(function () { checking = false; });
  }

  function startAndroid() {
    check();                                          // every time the app opens
    window.addEventListener('online', check);         // when internet returns

    // Coming back from the background: show the popup again (if the last check
    // was a while ago), since the app isn't restarted when it's reopened.
    var App = plugin('App');
    if (App && App.addListener) {
      App.addListener('appStateChange', function (st) {
        if (st && st.isActive && Date.now() - lastCheckAt > RECHECK_MS) {
          finished = false; shownOffline = false;
          check();
        }
      });
    }
  }

  function start() {
    if (window.gnhsUpdater) startDesktop();           // Windows (Electron)
    else startAndroid();                              // Android (Capacitor); no-op in a browser
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start);
  else start();
})();
