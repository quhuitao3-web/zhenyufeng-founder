/* =========================================================
   桢昱烽 · 主理人版 V2 —— 演示舞台、灵魂导演与实时音频合成引擎
   ========================================================= */
(function (global) {
  'use strict';

  var STAGE_W = 1920;
  var STAGE_H = 1080;
  var WHEEL_LOCK_MS = 700;
  var WHEEL_THRESHOLD = 25;
  var SWIPE_THRESHOLD = 50;
  var SCORE_CROSSFADE_SEC = 1.5;
  var SCORE_DUCK_GAIN = 0.16;

  var SILENT_WAV =
    'data:audio/wav;base64,UklGRigAAABXQVZFZm10IBIAAAABAAEARKwAAIhYAQACABAAAABkYXRhAgAAAAEA';

  var ENGINE_ROOT_URL = (function () {
    try {
      if (document.currentScript && document.currentScript.src) {
        return new global.URL('.', document.currentScript.src).href;
      }
    } catch (_) {}
    return '';
  })();

  function resolveEngineAsset(relPath) {
    if (ENGINE_ROOT_URL) {
      try {
        return new global.URL(relPath, ENGINE_ROOT_URL).href;
      } catch (_) {}
    }
    return relPath;
  }

  var NAV_BLOCKED_SELECTOR =
    '.no-nav, button, input, select, textarea, a, video, [data-nav-stop], #deckModal, #deckRail, #deckControls, #startGate';

  var VOID_TAGS = {
    AREA: 1, BASE: 1, BR: 1, COL: 1, EMBED: 1, HR: 1, IMG: 1,
    INPUT: 1, LINK: 1, META: 1, PARAM: 1, SOURCE: 1, TRACK: 1, WBR: 1
  };

  var hooks = Object.create(null);
  var inlineEntries = [];
  var activeLoops = new Set();
  var slideCleanups = new WeakMap();
  var transientNodes = new Set();
  var charTimersMap = new WeakMap();
  var countUpCancelMap = new WeakMap();
  var writeOnCancelMap = new WeakMap();

  var viewportEl = null;
  var stageEl = null;
  var slides = [];
  var currentIndex = -1;
  var beatIndex = 0;
  var started = false;

  var gateEl = null;
  var gateActive = false;
  var gateHideTimer = null;

  var railEl = null;
  var railDots = [];
  var controlsEl = null;
  var muteBtnEl = null;
  var fsBtnEl = null;
  var toastEl = null;
  var toastTimer = null;

  var modalEl = null;
  var modalTitleEl = null;
  var modalVideoEl = null;
  var modalOpen = false;

  var lastWheelAt = 0;
  var lastSwipeAt = 0;
  var touchStart = null;
  var clickSnapshot = { idx: -1, beat: 0 };

  var ctx = null;
  var masterGain = null;
  var scoreBusGain = null;
  var noiseBuffer = null;
  var gloryReverbBuffer = null;
  var silentAudioEl = null;
  var userMuted = false;
  var btnUnlockStamp = 0;

  var currentAmbient = null;

  var currentCueName = null;
  var activeScoreTrack = null;
  var scoreManifest = null;
  var manifestRequested = false;
  var manualDuck = false;
  var isDucked = false;

  var activeShakeAnim = null;
  var activeShakeEl = null;
  var activeShakeTimer = null;

  /* ---------- 工具函数 ---------- */
  function clamp01(v) {
    var n = Number(v);
    if (!Number.isFinite(n)) return 0;
    return n < 0 ? 0 : n > 1 ? 1 : n;
  }

  function isNavBlocked(target) {
    if (!target || !target.closest) return false;
    return Boolean(target.closest(NAV_BLOCKED_SELECTOR));
  }

  function isTypingTarget(target) {
    if (!target) return false;
    var tag = target.tagName;
    return (
      tag === 'INPUT' ||
      tag === 'TEXTAREA' ||
      tag === 'SELECT' ||
      Boolean(target.isContentEditable)
    );
  }

  function hasNoGateFlag() {
    try {
      if (typeof global.URLSearchParams === 'function') {
        return new global.URLSearchParams(global.location.search).get('nogate') === '1';
      }
    } catch (_) {}
    return /[?&]nogate=1(?:&|$)/.test(String((global.location && global.location.search) || ''));
  }

  function getSlideTheme(slideEl) {
    if (!slideEl) return 'dark';
    var cls = slideEl.classList;
    if (cls.contains('on-photo') || cls.contains('dark') || cls.contains('black')) {
      return 'dark';
    }
    if (cls.contains('light') || cls.contains('white')) {
      return 'light';
    }
    return 'dark';
  }

  function getEffectiveCueAt(idx) {
    for (var i = idx; i >= 0; i--) {
      if (slides[i]) {
        var c = slides[i].getAttribute('data-cue');
        if (c && c.trim()) return c.trim();
      }
    }
    return null;
  }

  function showToast(msg) {
    if (!toastEl) return;
    toastEl.textContent = msg;
    toastEl.classList.add('show');
    if (toastTimer) clearTimeout(toastTimer);
    toastTimer = setTimeout(function () {
      if (toastEl) toastEl.classList.remove('show');
    }, 2200);
  }

  function invokeWeixin(cb) {
    try {
      if (
        global.WeixinJSBridge &&
        typeof global.WeixinJSBridge.invoke === 'function'
      ) {
        global.WeixinJSBridge.invoke('getNetworkType', {}, function () {
          if (typeof cb === 'function') cb();
        });
        return true;
      }
    } catch (_) {}
    return false;
  }

  function registerSlideCleanup(slideEl, fn) {
    var target = slideEl || (currentIndex >= 0 ? slides[currentIndex] : null);
    if (!target || typeof fn !== 'function') return fn;
    var list = slideCleanups.get(target);
    if (!list) {
      list = [];
      slideCleanups.set(target, list);
    }
    list.push(fn);
    return fn;
  }

  function cleanupSlideFx(slideEl) {
    if (activeShakeAnim) {
      try {
        activeShakeAnim.cancel();
      } catch (_) {}
      activeShakeAnim = null;
    }
    if (activeShakeTimer) {
      clearTimeout(activeShakeTimer);
      activeShakeTimer = null;
    }
    if (activeShakeEl) {
      activeShakeEl.classList.remove('fx-shaking');
      activeShakeEl = null;
    }
    if (!slideEl) return;
    var list = slideCleanups.get(slideEl);
    if (list && list.length) {
      for (var i = 0; i < list.length; i++) {
        try {
          list[i]();
        } catch (_) {}
      }
      list.length = 0;
    }
    var leftover = slideEl.querySelectorAll(
      '.fx-sweep-box, .fx-sparks-layer, .fx-particles-canvas, .fx-lightning-svg'
    );
    for (var j = 0; j < leftover.length; j++) {
      if (leftover[j].parentNode) leftover[j].parentNode.removeChild(leftover[j]);
    }
  }

  function removeTransientNode(node) {
    if (!node) return;
    transientNodes.delete(node);
    if (node.parentNode) node.parentNode.removeChild(node);
  }

  /* ---------- 舞台缩放（绝不覆写为非等比缩放） ---------- */
  function updateScale() {
    if (!stageEl) return;
    var vw = (viewportEl && viewportEl.clientWidth) || global.innerWidth || STAGE_W;
    var vh = (viewportEl && viewportEl.clientHeight) || global.innerHeight || STAGE_H;
    var s = Math.min(vw / STAGE_W, vh / STAGE_H);
    stageEl.style.transform = 'translate(-50%, -50%) scale(' + s + ')';
  }

  /* ---------- 全屏控制 ---------- */
  function isFullscreenSupported() {
    var docEl = document.documentElement;
    return Boolean(
      document.fullscreenEnabled ||
        document.webkitFullscreenEnabled ||
        (docEl && (docEl.requestFullscreen || docEl.webkitRequestFullscreen))
    );
  }

  function getFullscreenElement() {
    return document.fullscreenElement || document.webkitFullscreenElement || null;
  }

  function syncFsUI() {
    if (!fsBtnEl) return;
    fsBtnEl.textContent = getFullscreenElement() ? '退出' : '全屏';
  }

  function toggleFullscreen() {
    if (!isFullscreenSupported()) {
      showToast('当前环境不支持全屏');
      return;
    }
    var docEl = document.documentElement;
    if (getFullscreenElement()) {
      var exitFn = document.exitFullscreen || document.webkitExitFullscreen;
      if (exitFn) {
        try {
          var pExit = exitFn.call(document);
          if (pExit && typeof pExit.catch === 'function') {
            pExit.catch(function () {});
          }
        } catch (_) {}
      }
      return;
    }
    var reqFn = docEl.requestFullscreen || docEl.webkitRequestFullscreen;
    if (!reqFn) {
      showToast('当前环境不支持全屏');
      return;
    }
    try {
      var pReq = reqFn.call(docEl);
      if (pReq && typeof pReq.catch === 'function') {
        pReq.catch(function () {
          showToast('当前浏览器不支持全屏');
        });
      }
    } catch (_) {
      showToast('当前浏览器不支持全屏');
    }
  }

  /* ---------- 音频上下文解锁与静音状态 ---------- */
  function ensureSilentAudioEl() {
    if (silentAudioEl) return silentAudioEl;
    var el = document.createElement('audio');
    el.setAttribute('playsinline', '');
    el.setAttribute('webkit-playsinline', 'true');
    el.setAttribute('x5-playsinline', 'true');
    el.preload = 'auto';
    el.src = SILENT_WAV;
    silentAudioEl = el;
    return el;
  }

  function ensureNoiseBuffer() {
    if (!ctx) return null;
    if (noiseBuffer) return noiseBuffer;
    var len = Math.floor(ctx.sampleRate * 2);
    var buf = ctx.createBuffer(1, len, ctx.sampleRate);
    var data = buf.getChannelData(0);
    for (var i = 0; i < len; i++) {
      data[i] = Math.random() * 2 - 1;
    }
    noiseBuffer = buf;
    return noiseBuffer;
  }

  function ensureGloryReverbBuffer() {
    if (!ctx) return null;
    if (gloryReverbBuffer) return gloryReverbBuffer;
    var len = Math.floor(ctx.sampleRate * 2.8);
    var buf = ctx.createBuffer(2, len, ctx.sampleRate);
    for (var ch = 0; ch < 2; ch++) {
      var data = buf.getChannelData(ch);
      for (var i = 0; i < len; i++) {
        data[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / len, 2.6);
      }
    }
    gloryReverbBuffer = buf;
    return gloryReverbBuffer;
  }

  function syncMuteUI() {
    var active = Boolean(Deck.audioReady && !userMuted);
    if (muteBtnEl) {
      muteBtnEl.classList.toggle('on', active);
      muteBtnEl.textContent = active ? '🔊 声音已开' : '🔇 开启声音';
      muteBtnEl.setAttribute('aria-pressed', active ? 'true' : 'false');
    }
    if (masterGain && ctx) {
      try {
        masterGain.gain.setTargetAtTime(active ? 1 : 0, ctx.currentTime, 0.02);
      } catch (_) {}
    }
    if (activeScoreTrack && typeof activeScoreTrack.syncMute === 'function') {
      activeScoreTrack.syncMute();
    }
  }

  function syncActiveSlideMediaOnMuteChange() {
    var muted = userMuted || !Deck.audioReady;
    if (modalOpen && modalVideoEl) {
      modalVideoEl.muted = muted;
      if (!muted) modalVideoEl.volume = 1;
    }
    if (currentIndex < 0 || !slides[currentIndex]) return;
    var activeSlide = slides[currentIndex];
    for (var i = 0; i < inlineEntries.length; i++) {
      var entry = inlineEntries[i];
      if (entry.slideEl === activeSlide) {
        entry.videoEl.muted = muted;
        if (!muted) {
          entry.videoEl.volume = 1;
          entry.unmutedIntent = true;
          entry.videoEl.play().catch(function () {
            entry.unmutedIntent = false;
            syncAutoDuck();
          });
        } else {
          entry.unmutedIntent = false;
        }
        if (entry.soundBtn) {
          entry.soundBtn.classList.toggle('on', !entry.videoEl.muted);
        }
      }
    }
    syncAutoDuck();
  }

  function resumePendingScoreIfNeeded() {
    if (!ctx || !currentCueName || currentCueName === 'silence') return;
    if (!activeScoreTrack || activeScoreTrack.name !== currentCueName) {
      activeScoreTrack = startScoreTrack(currentCueName, SCORE_CROSSFADE_SEC);
      applyDuckGain();
    }
  }

  function unlockAudio(e) {
    try {
      if (navigator.audioSession && navigator.audioSession.type !== 'playback') {
        navigator.audioSession.type = 'playback';
      }
    } catch (_) {}

    var wasReady = Deck.audioReady;
    if (e && e.target && e.target.closest) {
      var onMuteBtn = Boolean(muteBtnEl && e.target.closest('#deckMuteBtn'));
      if (!wasReady && onMuteBtn) {
        btnUnlockStamp = Date.now();
      } else if (wasReady && !onMuteBtn) {
        btnUnlockStamp = 0;
      }
    }

    if (!ctx) {
      var AC = global.AudioContext || global.webkitAudioContext;
      if (AC) {
        try {
          ctx = new AC();
          masterGain = ctx.createGain();
          masterGain.gain.value = userMuted ? 0 : 1;

          scoreBusGain = ctx.createGain();
          scoreBusGain.gain.value = isDucked ? SCORE_DUCK_GAIN : 1;

          var comp = ctx.createDynamicsCompressor();
          comp.threshold.value = -12;
          comp.knee.value = 18;
          comp.ratio.value = 4;
          comp.attack.value = 0.003;
          comp.release.value = 0.15;

          scoreBusGain.connect(masterGain);
          masterGain.connect(comp);
          comp.connect(ctx.destination);

          ctx.onstatechange = function () {
            if (ctx && ctx.state === 'running') {
              if (!Deck.audioReady) {
                Deck.audioReady = true;
                syncMuteUI();
              }
              resumePendingScoreIfNeeded();
            }
          };
          ensureNoiseBuffer();
        } catch (_) {
          ctx = null;
        }
      }
    }

    if (ctx) {
      try {
        if (ctx.state === 'suspended' && typeof ctx.resume === 'function') {
          ctx
            .resume()
            .then(function () {
              if (ctx && ctx.state === 'running') {
                Deck.audioReady = true;
                syncMuteUI();
                resumePendingScoreIfNeeded();
              }
            })
            .catch(function () {});
        }
        var buf = ctx.createBuffer(1, 1, 22050);
        var src = ctx.createBufferSource();
        src.buffer = buf;
        src.connect(ctx.destination);
        src.start(0);
      } catch (_) {}
      Deck.audioReady = true;
    }

    try {
      var audioEl = ensureSilentAudioEl();
      var p = audioEl.play();
      if (p && typeof p.catch === 'function') p.catch(function () {});
    } catch (_) {}

    syncMuteUI();
    resumePendingScoreIfNeeded();
  }

  function handleMuteButtonClick(e) {
    if (e) e.stopPropagation();
    var justUnlockedByBtn =
      btnUnlockStamp > 0 && Date.now() - btnUnlockStamp < 1000;
    btnUnlockStamp = 0;

    if (justUnlockedByBtn) {
      userMuted = false;
    } else if (!Deck.audioReady) {
      unlockAudio(e);
      userMuted = false;
    } else {
      userMuted = !userMuted;
    }

    if (!userMuted && ctx && ctx.state === 'suspended') {
      ctx.resume().catch(function () {});
    }

    syncMuteUI();
    syncActiveSlideMediaOnMuteChange();
  }

  /* ---------- Web Audio 一次性音效 (Deck.sfx) ---------- */
  function createNoiseSource(startTime, duration) {
    var src = ctx.createBufferSource();
    src.buffer = ensureNoiseBuffer();
    src.loop = true;
    src.start(startTime, Math.random() * 0.5);
    src.stop(startTime + duration + 0.03);
    return src;
  }

  function playSfx(name, arg) {
    if (!ctx || !Deck.audioReady || Deck.isMuted()) return;
    if (ctx.state === 'suspended') {
      ctx.resume().catch(function () {});
    }
    var now = ctx.currentTime;

    switch (name) {
      case 'whoosh': {
        var dur = 0.28;
        var nSrc = createNoiseSource(now, dur);
        var bp = ctx.createBiquadFilter();
        bp.type = 'bandpass';
        bp.Q.value = 1.8;
        bp.frequency.setValueAtTime(220, now);
        bp.frequency.exponentialRampToValueAtTime(1800, now + 0.11);
        bp.frequency.exponentialRampToValueAtTime(400, now + dur);

        var g = ctx.createGain();
        g.gain.setValueAtTime(0.001, now);
        g.gain.linearRampToValueAtTime(0.42, now + 0.08);
        g.gain.exponentialRampToValueAtTime(0.0001, now + dur);

        nSrc.connect(bp);
        bp.connect(g);
        g.connect(masterGain);
        break;
      }

      case 'overtake': {
        var dur2 = 0.45;
        var o1 = ctx.createOscillator();
        var o2 = ctx.createOscillator();
        o1.type = 'sawtooth';
        o2.type = 'triangle';
        o1.frequency.setValueAtTime(120, now);
        o1.frequency.exponentialRampToValueAtTime(520, now + 0.17);
        o1.frequency.exponentialRampToValueAtTime(180, now + dur2);
        o2.frequency.setValueAtTime(124, now);
        o2.frequency.exponentialRampToValueAtTime(528, now + 0.17);
        o2.frequency.exponentialRampToValueAtTime(182, now + dur2);

        var lp = ctx.createBiquadFilter();
        lp.type = 'lowpass';
        lp.Q.value = 3.2;
        lp.frequency.setValueAtTime(500, now);
        lp.frequency.exponentialRampToValueAtTime(2800, now + 0.17);
        lp.frequency.exponentialRampToValueAtTime(460, now + dur2);

        var og = ctx.createGain();
        og.gain.setValueAtTime(0.001, now);
        og.gain.linearRampToValueAtTime(0.24, now + 0.14);
        og.gain.exponentialRampToValueAtTime(0.0001, now + dur2);

        o1.connect(lp);
        o2.connect(lp);
        lp.connect(og);
        og.connect(masterGain);
        o1.start(now);
        o2.start(now);
        o1.stop(now + dur2 + 0.02);
        o2.stop(now + dur2 + 0.02);

        var air = createNoiseSource(now, dur2);
        var airBp = ctx.createBiquadFilter();
        airBp.type = 'bandpass';
        airBp.Q.value = 1.6;
        airBp.frequency.setValueAtTime(300, now);
        airBp.frequency.exponentialRampToValueAtTime(2400, now + 0.17);
        airBp.frequency.exponentialRampToValueAtTime(340, now + dur2);
        var airG = ctx.createGain();
        airG.gain.setValueAtTime(0.001, now);
        airG.gain.linearRampToValueAtTime(0.26, now + 0.15);
        airG.gain.exponentialRampToValueAtTime(0.0001, now + dur2);
        air.connect(airBp);
        airBp.connect(airG);
        airG.connect(masterGain);
        break;
      }

      case 'stamp': {
        var sub = ctx.createOscillator();
        sub.type = 'triangle';
        sub.frequency.setValueAtTime(160, now);
        sub.frequency.exponentialRampToValueAtTime(36, now + 0.24);
        var sg = ctx.createGain();
        sg.gain.setValueAtTime(0.001, now);
        sg.gain.linearRampToValueAtTime(0.72, now + 0.006);
        sg.gain.exponentialRampToValueAtTime(0.0001, now + 0.26);
        sub.connect(sg);
        sg.connect(masterGain);
        sub.start(now);
        sub.stop(now + 0.28);

        var body = ctx.createOscillator();
        body.type = 'sine';
        body.frequency.setValueAtTime(240, now);
        body.frequency.exponentialRampToValueAtTime(52, now + 0.08);
        var bg = ctx.createGain();
        bg.gain.setValueAtTime(0.45, now);
        bg.gain.exponentialRampToValueAtTime(0.0001, now + 0.09);
        body.connect(bg);
        bg.connect(masterGain);
        body.start(now);
        body.stop(now + 0.11);

        var impact = createNoiseSource(now, 0.11);
        var impF = ctx.createBiquadFilter();
        impF.type = 'bandpass';
        impF.Q.value = 1.1;
        impF.frequency.setValueAtTime(1100, now);
        impF.frequency.exponentialRampToValueAtTime(220, now + 0.09);
        var ig = ctx.createGain();
        ig.gain.setValueAtTime(0.55, now);
        ig.gain.exponentialRampToValueAtTime(0.0001, now + 0.1);
        impact.connect(impF);
        impF.connect(ig);
        ig.connect(masterGain);
        break;
      }

      case 'type': {
        var jitter = 0.94 + Math.random() * 0.12;
        var click = ctx.createOscillator();
        click.type = 'triangle';
        click.frequency.setValueAtTime(950 * jitter, now);
        click.frequency.exponentialRampToValueAtTime(320 * jitter, now + 0.022);
        var cg = ctx.createGain();
        cg.gain.setValueAtTime(0.28, now);
        cg.gain.exponentialRampToValueAtTime(0.0001, now + 0.025);
        click.connect(cg);
        cg.connect(masterGain);
        click.start(now);
        click.stop(now + 0.03);

        var snap = createNoiseSource(now, 0.028);
        var hp = ctx.createBiquadFilter();
        hp.type = 'bandpass';
        hp.frequency.value = 2400 * jitter;
        hp.Q.value = 1.5;
        var ng = ctx.createGain();
        ng.gain.setValueAtTime(0.26, now);
        ng.gain.exponentialRampToValueAtTime(0.0001, now + 0.028);
        snap.connect(hp);
        hp.connect(ng);
        ng.connect(masterGain);
        break;
      }

      case 'ding': {
        var partials = [
          { f: 2093, a: 0.28, d: 0.45 },
          { f: 4186, a: 0.12, d: 0.34 },
          { f: 3136, a: 0.05, d: 0.24 }
        ];
        for (var i = 0; i < partials.length; i++) {
          var p = partials[i];
          var osc = ctx.createOscillator();
          osc.type = 'sine';
          osc.frequency.setValueAtTime(p.f, now);
          var dg = ctx.createGain();
          dg.gain.setValueAtTime(0.0001, now);
          dg.gain.linearRampToValueAtTime(p.a, now + 0.003);
          dg.gain.exponentialRampToValueAtTime(0.0001, now + p.d);
          osc.connect(dg);
          dg.connect(masterGain);
          osc.start(now);
          osc.stop(now + p.d + 0.02);
        }
        break;
      }

      case 'chime': {
        var notes = [523.25, 659.25, 783.99, 1046.5];
        for (var j = 0; j < notes.length; j++) {
          var t = now + j * 0.055;
          var co = ctx.createOscillator();
          var co2 = ctx.createOscillator();
          co.type = 'sine';
          co2.type = 'triangle';
          co.frequency.setValueAtTime(notes[j], t);
          co2.frequency.setValueAtTime(notes[j] * 2, t);
          var g1 = ctx.createGain();
          var g2 = ctx.createGain();
          g1.gain.setValueAtTime(0.0001, t);
          g1.gain.linearRampToValueAtTime(0.18, t + 0.008);
          g1.gain.exponentialRampToValueAtTime(0.0001, t + 0.42);
          g2.gain.setValueAtTime(0.0001, t);
          g2.gain.linearRampToValueAtTime(0.05, t + 0.006);
          g2.gain.exponentialRampToValueAtTime(0.0001, t + 0.22);
          co.connect(g1);
          co2.connect(g2);
          g1.connect(masterGain);
          g2.connect(masterGain);
          co.start(t);
          co2.start(t);
          co.stop(t + 0.45);
          co2.stop(t + 0.25);
        }
        break;
      }

      case 'coin': {
        var steps = [
          { f: 987.77, t: 0, dur: 0.085, amp: 0.24 },
          { f: 1318.51, t: 0.075, dur: 0.34, amp: 0.26 }
        ];
        for (var k = 0; k < steps.length; k++) {
          var st = steps[k];
          var t0 = now + st.t;
          var mo = ctx.createOscillator();
          var mo2 = ctx.createOscillator();
          mo.type = 'sine';
          mo2.type = 'sine';
          mo.frequency.setValueAtTime(st.f, t0);
          mo2.frequency.setValueAtTime(st.f * 2, t0);
          var mg = ctx.createGain();
          var mg2 = ctx.createGain();
          mg.gain.setValueAtTime(0.0001, t0);
          mg.gain.linearRampToValueAtTime(st.amp, t0 + 0.004);
          mg.gain.exponentialRampToValueAtTime(0.0001, t0 + st.dur);
          mg2.gain.setValueAtTime(0.0001, t0);
          mg2.gain.linearRampToValueAtTime(st.amp * 0.18, t0 + 0.003);
          mg2.gain.exponentialRampToValueAtTime(0.0001, t0 + st.dur * 0.65);
          mo.connect(mg);
          mo2.connect(mg2);
          mg.connect(masterGain);
          mg2.connect(masterGain);
          mo.start(t0);
          mo2.start(t0);
          mo.stop(t0 + st.dur + 0.02);
          mo2.stop(t0 + st.dur + 0.02);
        }
        break;
      }

      case 'eagle': {
        var durE = 0.86;
        var saw = ctx.createOscillator();
        var whistle = ctx.createOscillator();
        saw.type = 'sawtooth';
        whistle.type = 'sine';

        saw.frequency.setValueAtTime(1820, now);
        saw.frequency.exponentialRampToValueAtTime(3220, now + 0.18);
        saw.frequency.exponentialRampToValueAtTime(2900, now + 0.44);
        saw.frequency.exponentialRampToValueAtTime(2280, now + durE);

        whistle.frequency.setValueAtTime(1828, now);
        whistle.frequency.exponentialRampToValueAtTime(3232, now + 0.18);
        whistle.frequency.exponentialRampToValueAtTime(2912, now + 0.44);
        whistle.frequency.exponentialRampToValueAtTime(2290, now + durE);

        var vib = ctx.createOscillator();
        var vibG = ctx.createGain();
        vib.type = 'sine';
        vib.frequency.value = 26;
        vibG.gain.setValueAtTime(0, now);
        vibG.gain.linearRampToValueAtTime(48, now + 0.16);
        vibG.gain.linearRampToValueAtTime(22, now + durE);
        vib.connect(vibG);
        vibG.connect(saw.frequency);
        vibG.connect(whistle.frequency);

        var formant = ctx.createBiquadFilter();
        formant.type = 'bandpass';
        formant.Q.value = 4.2;
        formant.frequency.setValueAtTime(1900, now);
        formant.frequency.exponentialRampToValueAtTime(3350, now + 0.2);
        formant.frequency.exponentialRampToValueAtTime(2250, now + durE);

        var eg = ctx.createGain();
        eg.gain.setValueAtTime(0.0001, now);
        eg.gain.linearRampToValueAtTime(0.28, now + 0.07);
        eg.gain.linearRampToValueAtTime(0.22, now + 0.48);
        eg.gain.exponentialRampToValueAtTime(0.0001, now + durE);

        saw.connect(formant);
        whistle.connect(formant);
        formant.connect(eg);
        eg.connect(masterGain);

        var breath = createNoiseSource(now, durE);
        var bF = ctx.createBiquadFilter();
        bF.type = 'bandpass';
        bF.Q.value = 3.5;
        bF.frequency.setValueAtTime(2800, now);
        bF.frequency.exponentialRampToValueAtTime(2100, now + durE);
        var bG = ctx.createGain();
        bG.gain.setValueAtTime(0.0001, now);
        bG.gain.linearRampToValueAtTime(0.08, now + 0.09);
        bG.gain.exponentialRampToValueAtTime(0.0001, now + durE);
        breath.connect(bF);
        bF.connect(bG);
        bG.connect(masterGain);

        saw.start(now);
        whistle.start(now);
        vib.start(now);
        saw.stop(now + durE + 0.02);
        whistle.stop(now + durE + 0.02);
        vib.stop(now + durE + 0.02);
        break;
      }

      case 'pop': {
        var po = ctx.createOscillator();
        po.type = 'sine';
        po.frequency.setValueAtTime(320, now);
        po.frequency.exponentialRampToValueAtTime(540, now + 0.065);
        var pg = ctx.createGain();
        pg.gain.setValueAtTime(0.0001, now);
        pg.gain.linearRampToValueAtTime(0.24, now + 0.004);
        pg.gain.exponentialRampToValueAtTime(0.0001, now + 0.07);
        po.connect(pg);
        pg.connect(masterGain);
        po.start(now);
        po.stop(now + 0.085);
        break;
      }

      case 'thud': {
        var to = ctx.createOscillator();
        to.type = 'sine';
        to.frequency.setValueAtTime(110, now);
        to.frequency.exponentialRampToValueAtTime(42, now + 0.19);
        var tlp = ctx.createBiquadFilter();
        tlp.type = 'lowpass';
        tlp.frequency.value = 320;
        var tg = ctx.createGain();
        tg.gain.setValueAtTime(0.0001, now);
        tg.gain.linearRampToValueAtTime(0.45, now + 0.005);
        tg.gain.exponentialRampToValueAtTime(0.0001, now + 0.21);
        to.connect(tlp);
        tlp.connect(tg);
        tg.connect(masterGain);
        to.start(now);
        to.stop(now + 0.23);
        break;
      }

      /* ---------- 灵魂层新增 16 种合成音效 ---------- */
      case 'impact': {
        var impSub = ctx.createOscillator();
        impSub.type = 'sine';
        impSub.frequency.setValueAtTime(128, now);
        impSub.frequency.exponentialRampToValueAtTime(28, now + 0.56);
        var impSubG = ctx.createGain();
        impSubG.gain.setValueAtTime(0.001, now);
        impSubG.gain.linearRampToValueAtTime(0.75, now + 0.008);
        impSubG.gain.exponentialRampToValueAtTime(0.0001, now + 0.62);
        impSub.connect(impSubG);
        impSubG.connect(masterGain);
        impSub.start(now);
        impSub.stop(now + 0.65);

        var impMid = ctx.createOscillator();
        impMid.type = 'triangle';
        impMid.frequency.setValueAtTime(220, now);
        impMid.frequency.exponentialRampToValueAtTime(48, now + 0.18);
        var impMidG = ctx.createGain();
        impMidG.gain.setValueAtTime(0.42, now);
        impMidG.gain.exponentialRampToValueAtTime(0.0001, now + 0.22);
        impMid.connect(impMidG);
        impMidG.connect(masterGain);
        impMid.start(now);
        impMid.stop(now + 0.24);

        var impBurst = createNoiseSource(now, 0.45);
        var impLp = ctx.createBiquadFilter();
        impLp.type = 'lowpass';
        impLp.frequency.setValueAtTime(1800, now);
        impLp.frequency.exponentialRampToValueAtTime(110, now + 0.42);
        var impBg = ctx.createGain();
        impBg.gain.setValueAtTime(0.48, now);
        impBg.gain.exponentialRampToValueAtTime(0.0001, now + 0.44);
        impBurst.connect(impLp);
        impLp.connect(impBg);
        impBg.connect(masterGain);
        break;
      }

      case 'riser': {
        var durMs = Number(arg);
        if (!Number.isFinite(durMs) || durMs <= 0) durMs = 3000;
        var durR = Math.max(0.35, Math.min(durMs / 1000, 12));

        var rOut = ctx.createGain();
        rOut.gain.setValueAtTime(0.0001, now);
        rOut.gain.exponentialRampToValueAtTime(0.32, now + durR * 0.92);
        rOut.gain.linearRampToValueAtTime(0.0001, now + durR + 0.04);
        rOut.connect(masterGain);

        var r1 = ctx.createOscillator();
        var r2 = ctx.createOscillator();
        r1.type = 'sawtooth';
        r2.type = 'sawtooth';
        r1.frequency.setValueAtTime(85, now);
        r1.frequency.exponentialRampToValueAtTime(680, now + durR);
        r2.frequency.setValueAtTime(170.8, now);
        r2.frequency.exponentialRampToValueAtTime(1366, now + durR);

        var rLp = ctx.createBiquadFilter();
        rLp.type = 'lowpass';
        rLp.Q.value = 3.2;
        rLp.frequency.setValueAtTime(220, now);
        rLp.frequency.exponentialRampToValueAtTime(4800, now + durR);

        var rOscG = ctx.createGain();
        rOscG.gain.value = 0.42;
        r1.connect(rLp);
        r2.connect(rLp);
        rLp.connect(rOscG);
        rOscG.connect(rOut);

        var rNoise = createNoiseSource(now, durR + 0.04);
        var rBp = ctx.createBiquadFilter();
        rBp.type = 'bandpass';
        rBp.Q.setValueAtTime(1.2, now);
        rBp.Q.linearRampToValueAtTime(4.5, now + durR);
        rBp.frequency.setValueAtTime(260, now);
        rBp.frequency.exponentialRampToValueAtTime(4200, now + durR);
        var rNg = ctx.createGain();
        rNg.gain.setValueAtTime(0.18, now);
        rNg.gain.linearRampToValueAtTime(0.72, now + durR * 0.92);
        rNoise.connect(rBp);
        rBp.connect(rNg);
        rNg.connect(rOut);

        r1.start(now);
        r2.start(now);
        r1.stop(now + durR + 0.05);
        r2.stop(now + durR + 0.05);

        registerSlideCleanup(null, function () {
          try {
            rOut.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.03);
          } catch (_) {}
          setTimeout(function () {
            try {
              r1.stop();
              r2.stop();
              rNoise.stop();
              rOut.disconnect();
            } catch (_) {}
          }, 90);
        });
        break;
      }

      case 'gong': {
        var baseG = 128;
        var ratios = [
          { m: 1.0, a: 0.28, d: 2.5 },
          { m: 1.54, a: 0.16, d: 2.1 },
          { m: 2.18, a: 0.11, d: 1.7 },
          { m: 2.86, a: 0.08, d: 1.35 },
          { m: 3.71, a: 0.05, d: 1.0 }
        ];
        for (var gi = 0; gi < ratios.length; gi++) {
          var rp = ratios[gi];
          var go = ctx.createOscillator();
          go.type = gi === 0 ? 'triangle' : 'sine';
          go.frequency.setValueAtTime(baseG * rp.m, now);
          go.frequency.linearRampToValueAtTime(baseG * rp.m * 0.992, now + rp.d);
          var gg = ctx.createGain();
          gg.gain.setValueAtTime(0.0001, now);
          gg.gain.linearRampToValueAtTime(rp.a, now + 0.025);
          gg.gain.exponentialRampToValueAtTime(0.0001, now + rp.d);
          go.connect(gg);
          gg.connect(masterGain);
          go.start(now);
          go.stop(now + rp.d + 0.04);
        }
        var mallet = createNoiseSource(now, 0.18);
        var mBp = ctx.createBiquadFilter();
        mBp.type = 'bandpass';
        mBp.frequency.value = 620;
        mBp.Q.value = 1.4;
        var mG = ctx.createGain();
        mG.gain.setValueAtTime(0.28, now);
        mG.gain.exponentialRampToValueAtTime(0.0001, now + 0.16);
        mallet.connect(mBp);
        mBp.connect(mG);
        mG.connect(masterGain);
        break;
      }

      case 'tick': {
        var tkOsc = ctx.createOscillator();
        tkOsc.type = 'sine';
        tkOsc.frequency.setValueAtTime(1600, now);
        tkOsc.frequency.exponentialRampToValueAtTime(680, now + 0.018);
        var tkG = ctx.createGain();
        tkG.gain.setValueAtTime(0.16, now);
        tkG.gain.exponentialRampToValueAtTime(0.0001, now + 0.022);
        tkOsc.connect(tkG);
        tkG.connect(masterGain);
        tkOsc.start(now);
        tkOsc.stop(now + 0.028);

        var tkN = createNoiseSource(now, 0.018);
        var tkBp = ctx.createBiquadFilter();
        tkBp.type = 'bandpass';
        tkBp.frequency.value = 3200;
        tkBp.Q.value = 2.0;
        var tkNg = ctx.createGain();
        tkNg.gain.setValueAtTime(0.14, now);
        tkNg.gain.exponentialRampToValueAtTime(0.0001, now + 0.018);
        tkN.connect(tkBp);
        tkBp.connect(tkNg);
        tkNg.connect(masterGain);
        break;
      }

      case 'rewind': {
        var rwDur = 0.52;
        var rwOsc = ctx.createOscillator();
        rwOsc.type = 'sawtooth';
        rwOsc.frequency.setValueAtTime(165, now);
        rwOsc.frequency.exponentialRampToValueAtTime(980, now + 0.34);
        rwOsc.frequency.exponentialRampToValueAtTime(420, now + rwDur);

        var rwBp = ctx.createBiquadFilter();
        rwBp.type = 'bandpass';
        rwBp.Q.value = 2.2;
        rwBp.frequency.setValueAtTime(320, now);
        rwBp.frequency.exponentialRampToValueAtTime(2200, now + 0.36);
        rwBp.frequency.exponentialRampToValueAtTime(850, now + rwDur);

        var rwG = ctx.createGain();
        rwG.gain.setValueAtTime(0.001, now);
        rwG.gain.exponentialRampToValueAtTime(0.24, now + rwDur - 0.05);
        rwG.gain.exponentialRampToValueAtTime(0.0001, now + rwDur);
        rwOsc.connect(rwBp);
        rwBp.connect(rwG);
        rwG.connect(masterGain);
        rwOsc.start(now);
        rwOsc.stop(now + rwDur + 0.02);

        var rwNoise = createNoiseSource(now, rwDur);
        var rwNp = ctx.createBiquadFilter();
        rwNp.type = 'highpass';
        rwNp.frequency.setValueAtTime(700, now);
        rwNp.frequency.exponentialRampToValueAtTime(2800, now + rwDur);
        var rwNg = ctx.createGain();
        rwNg.gain.setValueAtTime(0.001, now);
        rwNg.gain.exponentialRampToValueAtTime(0.28, now + rwDur - 0.04);
        rwNg.gain.exponentialRampToValueAtTime(0.0001, now + rwDur);
        rwNoise.connect(rwNp);
        rwNp.connect(rwNg);
        rwNg.connect(masterGain);
        break;
      }

      case 'shutter': {
        var clicks = [0, 0.068];
        for (var si = 0; si < clicks.length; si++) {
          var ct = now + clicks[si];
          var shN = createNoiseSource(ct, 0.032);
          var shBp = ctx.createBiquadFilter();
          shBp.type = 'bandpass';
          shBp.frequency.value = si === 0 ? 3100 : 2500;
          shBp.Q.value = 1.6;
          var shNg = ctx.createGain();
          shNg.gain.setValueAtTime(0.42, ct);
          shNg.gain.exponentialRampToValueAtTime(0.0001, ct + 0.028);
          shN.connect(shBp);
          shBp.connect(shNg);
          shNg.connect(masterGain);

          var shO = ctx.createOscillator();
          shO.type = 'triangle';
          shO.frequency.setValueAtTime(si === 0 ? 1100 : 880, ct);
          shO.frequency.exponentialRampToValueAtTime(240, ct + 0.024);
          var shOg = ctx.createGain();
          shOg.gain.setValueAtTime(0.24, ct);
          shOg.gain.exponentialRampToValueAtTime(0.0001, ct + 0.026);
          shO.connect(shOg);
          shOg.connect(masterGain);
          shO.start(ct);
          shO.stop(ct + 0.032);
        }
        break;
      }

      case 'siren': {
        var srDur = 0.92;
        var sr1 = ctx.createOscillator();
        var sr2 = ctx.createOscillator();
        sr1.type = 'sawtooth';
        sr2.type = 'triangle';
        sr1.frequency.setValueAtTime(600, now);
        sr1.frequency.exponentialRampToValueAtTime(980, now + 0.36);
        sr1.frequency.exponentialRampToValueAtTime(620, now + srDur);
        sr2.frequency.setValueAtTime(603, now);
        sr2.frequency.exponentialRampToValueAtTime(985, now + 0.36);
        sr2.frequency.exponentialRampToValueAtTime(623, now + srDur);

        var srBp = ctx.createBiquadFilter();
        srBp.type = 'bandpass';
        srBp.frequency.value = 1100;
        srBp.Q.value = 1.6;
        var srG = ctx.createGain();
        srG.gain.setValueAtTime(0.001, now);
        srG.gain.linearRampToValueAtTime(0.22, now + 0.08);
        srG.gain.linearRampToValueAtTime(0.18, now + 0.55);
        srG.gain.exponentialRampToValueAtTime(0.0001, now + srDur);
        sr1.connect(srBp);
        sr2.connect(srBp);
        srBp.connect(srG);
        srG.connect(masterGain);
        sr1.start(now);
        sr2.start(now);
        sr1.stop(now + srDur + 0.03);
        sr2.stop(now + srDur + 0.03);
        break;
      }

      case 'drumroll': {
        var hits = 16;
        var span = 0.9;
        for (var di = 0; di < hits; di++) {
          var prog = di / (hits - 1);
          var dt = now + Math.pow(prog, 0.85) * span;
          var amp = 0.06 + prog * 0.28;
          var sn = createNoiseSource(dt, 0.055);
          var snBp = ctx.createBiquadFilter();
          snBp.type = 'bandpass';
          snBp.frequency.value = 1900 + prog * 700;
          snBp.Q.value = 1.3;
          var snG = ctx.createGain();
          snG.gain.setValueAtTime(amp, dt);
          snG.gain.exponentialRampToValueAtTime(0.0001, dt + 0.05);
          sn.connect(snBp);
          snBp.connect(snG);
          snG.connect(masterGain);

          var bodyO = ctx.createOscillator();
          bodyO.type = 'triangle';
          bodyO.frequency.setValueAtTime(210, dt);
          bodyO.frequency.exponentialRampToValueAtTime(125, dt + 0.035);
          var bodyG = ctx.createGain();
          bodyG.gain.setValueAtTime(amp * 0.65, dt);
          bodyG.gain.exponentialRampToValueAtTime(0.0001, dt + 0.042);
          bodyO.connect(bodyG);
          bodyG.connect(masterGain);
          bodyO.start(dt);
          bodyO.stop(dt + 0.048);
        }
        break;
      }

      case 'cymbal': {
        var cyDur = 1.65;
        var cyN = createNoiseSource(now, cyDur);
        var cyHp = ctx.createBiquadFilter();
        cyHp.type = 'highpass';
        cyHp.frequency.value = 3400;
        var cyG = ctx.createGain();
        cyG.gain.setValueAtTime(0.001, now);
        cyG.gain.linearRampToValueAtTime(0.32, now + 0.01);
        cyG.gain.exponentialRampToValueAtTime(0.0001, now + cyDur);
        cyN.connect(cyHp);
        cyHp.connect(cyG);
        cyG.connect(masterGain);

        var cFreqs = [3420, 4750, 6120, 7890];
        for (var ci = 0; ci < cFreqs.length; ci++) {
          var co = ctx.createOscillator();
          co.type = 'square';
          co.frequency.setValueAtTime(cFreqs[ci], now);
          var cBp = ctx.createBiquadFilter();
          cBp.type = 'bandpass';
          cBp.frequency.value = cFreqs[ci];
          cBp.Q.value = 3.5;
          var cg = ctx.createGain();
          cg.gain.setValueAtTime(0.05, now);
          cg.gain.exponentialRampToValueAtTime(0.0001, now + cyDur * 0.75);
          co.connect(cBp);
          cBp.connect(cg);
          cg.connect(masterGain);
          co.start(now);
          co.stop(now + cyDur * 0.8);
        }
        break;
      }

      case 'taiko': {
        var tkSub = ctx.createOscillator();
        tkSub.type = 'sine';
        tkSub.frequency.setValueAtTime(118, now);
        tkSub.frequency.exponentialRampToValueAtTime(42, now + 0.34);
        var tkSubG = ctx.createGain();
        tkSubG.gain.setValueAtTime(0.001, now);
        tkSubG.gain.linearRampToValueAtTime(0.75, now + 0.006);
        tkSubG.gain.exponentialRampToValueAtTime(0.0001, now + 0.62);
        tkSub.connect(tkSubG);
        tkSubG.connect(masterGain);
        tkSub.start(now);
        tkSub.stop(now + 0.65);

        var tkHead = ctx.createOscillator();
        tkHead.type = 'triangle';
        tkHead.frequency.setValueAtTime(340, now);
        tkHead.frequency.exponentialRampToValueAtTime(84, now + 0.055);
        var tkHeadG = ctx.createGain();
        tkHeadG.gain.setValueAtTime(0.45, now);
        tkHeadG.gain.exponentialRampToValueAtTime(0.0001, now + 0.075);
        tkHead.connect(tkHeadG);
        tkHeadG.connect(masterGain);
        tkHead.start(now);
        tkHead.stop(now + 0.09);

        var tkSkin = createNoiseSource(now, 0.12);
        var tkLp = ctx.createBiquadFilter();
        tkLp.type = 'bandpass';
        tkLp.frequency.value = 640;
        tkLp.Q.value = 1.2;
        var tkSnG = ctx.createGain();
        tkSnG.gain.setValueAtTime(0.35, now);
        tkSnG.gain.exponentialRampToValueAtTime(0.0001, now + 0.11);
        tkSkin.connect(tkLp);
        tkLp.connect(tkSnG);
        tkSnG.connect(masterGain);
        break;
      }

      case 'sting': {
        // 戏剧感“噔-噔-噔——”四击悬念重音
        var stabs = [
          { t: 0, dur: 0.16, notes: [164.81, 233.08, 329.63, 466.16], amp: 0.22 },
          { t: 0.21, dur: 0.16, notes: [174.61, 246.94, 349.23, 493.88], amp: 0.24 },
          { t: 0.42, dur: 0.16, notes: [185.0, 261.63, 369.99, 523.25], amp: 0.26 },
          { t: 0.64, dur: 0.95, notes: [196.0, 277.18, 392.0, 554.37], amp: 0.3 }
        ];
        for (var sti = 0; sti < stabs.length; sti++) {
          var sb = stabs[sti];
          var stT = now + sb.t;
          var sLp = ctx.createBiquadFilter();
          sLp.type = 'lowpass';
          sLp.frequency.setValueAtTime(2400, stT);
          sLp.frequency.exponentialRampToValueAtTime(950, stT + sb.dur);
          var sGain = ctx.createGain();
          sGain.gain.setValueAtTime(0.0001, stT);
          sGain.gain.linearRampToValueAtTime(sb.amp, stT + 0.012);
          sGain.gain.exponentialRampToValueAtTime(0.0001, stT + sb.dur);
          sLp.connect(sGain);
          sGain.connect(masterGain);
          for (var ni = 0; ni < sb.notes.length; ni++) {
            var bo = ctx.createOscillator();
            bo.type = ni % 2 === 0 ? 'sawtooth' : 'triangle';
            bo.frequency.setValueAtTime(sb.notes[ni], stT);
            bo.connect(sLp);
            bo.start(stT);
            bo.stop(stT + sb.dur + 0.04);
          }
        }
        break;
      }

      case 'thunder': {
        var crack = createNoiseSource(now, 0.22);
        var crBp = ctx.createBiquadFilter();
        crBp.type = 'bandpass';
        crBp.frequency.setValueAtTime(2100, now);
        crBp.frequency.exponentialRampToValueAtTime(420, now + 0.18);
        crBp.Q.value = 1.1;
        var crG = ctx.createGain();
        crG.gain.setValueAtTime(0.45, now);
        crG.gain.exponentialRampToValueAtTime(0.0001, now + 0.2);
        crack.connect(crBp);
        crBp.connect(crG);
        crG.connect(masterGain);

        var rumbleDur = 1.75;
        var rum = createNoiseSource(now + 0.04, rumbleDur);
        var rumLp = ctx.createBiquadFilter();
        rumLp.type = 'lowpass';
        rumLp.Q.value = 1.6;
        rumLp.frequency.setValueAtTime(220, now + 0.04);
        rumLp.frequency.exponentialRampToValueAtTime(75, now + rumbleDur);
        var rumG = ctx.createGain();
        rumG.gain.setValueAtTime(0.001, now + 0.04);
        rumG.gain.linearRampToValueAtTime(0.55, now + 0.24);
        rumG.gain.linearRampToValueAtTime(0.32, now + 0.72);
        rumG.gain.exponentialRampToValueAtTime(0.0001, now + rumbleDur);
        rum.connect(rumLp);
        rumLp.connect(rumG);
        rumG.connect(masterGain);
        break;
      }

      case 'brush': {
        var brDur = 0.42;
        var brN = createNoiseSource(now, brDur);
        var brBp = ctx.createBiquadFilter();
        brBp.type = 'bandpass';
        brBp.Q.value = 1.5;
        brBp.frequency.setValueAtTime(850, now);
        brBp.frequency.exponentialRampToValueAtTime(2500, now + 0.16);
        brBp.frequency.exponentialRampToValueAtTime(1050, now + brDur);
        var brG = ctx.createGain();
        brG.gain.setValueAtTime(0.001, now);
        brG.gain.linearRampToValueAtTime(0.28, now + 0.07);
        brG.gain.exponentialRampToValueAtTime(0.0001, now + brDur);
        brN.connect(brBp);
        brBp.connect(brG);
        brG.connect(masterGain);
        break;
      }

      case 'zap': {
        var zDur = 0.22;
        var zOsc = ctx.createOscillator();
        zOsc.type = 'sawtooth';
        zOsc.frequency.setValueAtTime(1450, now);
        zOsc.frequency.exponentialRampToValueAtTime(160, now + zDur);

        var zMod = ctx.createOscillator();
        var zModG = ctx.createGain();
        zMod.type = 'square';
        zMod.frequency.value = 58;
        zModG.gain.value = 320;
        zMod.connect(zModG);
        zModG.connect(zOsc.frequency);

        var zBp = ctx.createBiquadFilter();
        zBp.type = 'bandpass';
        zBp.frequency.value = 1900;
        zBp.Q.value = 1.8;

        var zG = ctx.createGain();
        zG.gain.setValueAtTime(0.34, now);
        zG.gain.exponentialRampToValueAtTime(0.0001, now + zDur);
        zOsc.connect(zBp);
        zBp.connect(zG);
        zG.connect(masterGain);
        zOsc.start(now);
        zMod.start(now);
        zOsc.stop(now + zDur + 0.02);
        zMod.stop(now + zDur + 0.02);

        var zAir = createNoiseSource(now, 0.14);
        var zHp = ctx.createBiquadFilter();
        zHp.type = 'highpass';
        zHp.frequency.value = 2800;
        var zAg = ctx.createGain();
        zAg.gain.setValueAtTime(0.26, now);
        zAg.gain.exponentialRampToValueAtTime(0.0001, now + 0.13);
        zAir.connect(zHp);
        zHp.connect(zAg);
        zAg.connect(masterGain);
        break;
      }

      case 'hit': {
        var hSub = ctx.createOscillator();
        hSub.type = 'triangle';
        hSub.frequency.setValueAtTime(155, now);
        hSub.frequency.exponentialRampToValueAtTime(40, now + 0.16);
        var hSg = ctx.createGain();
        hSg.gain.setValueAtTime(0.55, now);
        hSg.gain.exponentialRampToValueAtTime(0.0001, now + 0.18);
        hSub.connect(hSg);
        hSg.connect(masterGain);
        hSub.start(now);
        hSub.stop(now + 0.2);

        var hCrack = createNoiseSource(now, 0.08);
        var hBp = ctx.createBiquadFilter();
        hBp.type = 'bandpass';
        hBp.frequency.setValueAtTime(1600, now);
        hBp.frequency.exponentialRampToValueAtTime(420, now + 0.07);
        var hCg = ctx.createGain();
        hCg.gain.setValueAtTime(0.42, now);
        hCg.gain.exponentialRampToValueAtTime(0.0001, now + 0.075);
        hCrack.connect(hBp);
        hBp.connect(hCg);
        hCg.connect(masterGain);
        break;
      }

      case 'news': {
        var nNotes = [
          { f: 392.0, t: 0, d: 0.14 },
          { f: 392.0, t: 0.16, d: 0.14 },
          { f: 523.25, t: 0.32, d: 0.16 },
          { f: 659.25, t: 0.5, d: 0.45 }
        ];
        for (var nwi = 0; nwi < nNotes.length; nwi++) {
          var nn = nNotes[nwi];
          var nt = now + nn.t;
          var brO = ctx.createOscillator();
          var blO = ctx.createOscillator();
          brO.type = 'sawtooth';
          blO.type = 'triangle';
          brO.frequency.setValueAtTime(nn.f, nt);
          blO.frequency.setValueAtTime(nn.f * 2, nt);

          var nLp = ctx.createBiquadFilter();
          nLp.type = 'lowpass';
          nLp.frequency.value = 2100;

          var ng1 = ctx.createGain();
          ng1.gain.setValueAtTime(0.0001, nt);
          ng1.gain.linearRampToValueAtTime(0.18, nt + 0.01);
          ng1.gain.exponentialRampToValueAtTime(0.0001, nt + nn.d);

          var ng2 = ctx.createGain();
          ng2.gain.setValueAtTime(0.0001, nt);
          ng2.gain.linearRampToValueAtTime(0.09, nt + 0.006);
          ng2.gain.exponentialRampToValueAtTime(0.0001, nt + nn.d * 0.85);

          brO.connect(nLp);
          nLp.connect(ng1);
          blO.connect(ng2);
          ng1.connect(masterGain);
          ng2.connect(masterGain);
          brO.start(nt);
          blO.start(nt);
          brO.stop(nt + nn.d + 0.03);
          blO.stop(nt + nn.d + 0.03);
        }
        break;
      }

      case 'glory': {
        var glSources = [];
        var glOut = ctx.createGain();
        glOut.gain.setValueAtTime(0.9, now);
        glOut.connect(masterGain);

        var glBus = ctx.createGain();
        glBus.gain.value = 1;

        var glDry = ctx.createGain();
        glDry.gain.value = 0.8;
        glBus.connect(glDry);
        glDry.connect(glOut);

        var revBuf = ensureGloryReverbBuffer();
        if (revBuf) {
          var glConv = ctx.createConvolver();
          glConv.buffer = revBuf;
          var glWet = ctx.createGain();
          glWet.gain.value = 0.38;
          glBus.connect(glConv);
          glConv.connect(glWet);
          glWet.connect(glOut);
        }

        // 1) 定音鼓滚奏 0..1.2s + 1.2s 重击
        var glRollN = createNoiseSource(now, 1.35);
        glSources.push(glRollN);
        var glRollLp = ctx.createBiquadFilter();
        glRollLp.type = 'lowpass';
        glRollLp.frequency.value = 200;
        glRollLp.Q.value = 0.8;
        var glRollNG = ctx.createGain();
        glRollNG.gain.setValueAtTime(0.02, now);
        glRollNG.gain.linearRampToValueAtTime(0.35, now + 1.2);
        glRollNG.gain.exponentialRampToValueAtTime(0.0001, now + 1.26);
        glRollN.connect(glRollLp);
        glRollLp.connect(glRollNG);
        glRollNG.connect(glBus);

        var glRollTone = ctx.createOscillator();
        glRollTone.type = 'sine';
        glRollTone.frequency.setValueAtTime(65, now);
        var glRollToneG = ctx.createGain();
        glRollToneG.gain.setValueAtTime(0.22, now);
        var glLfo = ctx.createOscillator();
        glLfo.type = 'sine';
        glLfo.frequency.value = 14;
        var glLfoDepth = ctx.createGain();
        glLfoDepth.gain.value = 0.12;
        glLfo.connect(glLfoDepth);
        glLfoDepth.connect(glRollToneG.gain);
        var glRollEnv = ctx.createGain();
        glRollEnv.gain.setValueAtTime(0.0001, now);
        glRollEnv.gain.linearRampToValueAtTime(1.0, now + 1.2);
        glRollEnv.gain.exponentialRampToValueAtTime(0.0001, now + 1.26);
        glRollTone.connect(glRollToneG);
        glRollToneG.connect(glRollEnv);
        glRollEnv.connect(glBus);
        glRollTone.start(now);
        glLfo.start(now);
        glRollTone.stop(now + 1.28);
        glLfo.stop(now + 1.28);
        glSources.push(glRollTone, glLfo);

        var glHit = ctx.createOscillator();
        glHit.type = 'sine';
        glHit.frequency.setValueAtTime(90, now + 1.2);
        glHit.frequency.exponentialRampToValueAtTime(48, now + 1.8);
        var glHitG = ctx.createGain();
        glHitG.gain.setValueAtTime(0.0001, now + 1.2);
        glHitG.gain.linearRampToValueAtTime(0.55, now + 1.215);
        glHitG.gain.exponentialRampToValueAtTime(0.0001, now + 2.6);
        glHit.connect(glHitG);
        glHitG.connect(glBus);
        glHit.start(now + 1.2);
        glHit.stop(now + 2.65);
        glSources.push(glHit);

        var glHitN = createNoiseSource(now + 1.2, 0.36);
        glSources.push(glHitN);
        var glHitNLp = ctx.createBiquadFilter();
        glHitNLp.type = 'lowpass';
        glHitNLp.frequency.value = 900;
        var glHitNG = ctx.createGain();
        glHitNG.gain.setValueAtTime(0.25, now + 1.2);
        glHitNG.gain.exponentialRampToValueAtTime(0.0001, now + 1.55);
        glHitN.connect(glHitNLp);
        glHitNLp.connect(glHitNG);
        glHitNG.connect(glBus);

        // 2) 铜管 + 合唱和弦推进 (G -> A -> Dadd9)
        var glChFilter = ctx.createBiquadFilter();
        glChFilter.type = 'lowpass';
        glChFilter.Q.value = 0.7;
        glChFilter.frequency.setValueAtTime(500, now + 1.2);
        glChFilter.frequency.exponentialRampToValueAtTime(2600, now + 3.4);
        glChFilter.frequency.exponentialRampToValueAtTime(3400, now + 4.2);
        glChFilter.connect(glBus);

        var chords = [
          { t0: 1.2, fadeAt: 2.4, stopAt: 3.5, notes: [196.0, 246.94, 293.66, 392.0], perVoice: 0.0375 },
          { t0: 2.4, fadeAt: 3.4, stopAt: 4.5, notes: [220.0, 277.18, 329.63, 440.0], perVoice: 0.0375 },
          { t0: 3.4, fadeAt: null, stopAt: 6.55, notes: [146.83, 220.0, 293.66, 369.99, 440.0, 659.25], perVoice: 0.0325 }
        ];
        var detuneCents = [-6, 6];
        for (var ci = 0; ci < chords.length; ci++) {
          var ch = chords[ci];
          var cg = ctx.createGain();
          cg.gain.setValueAtTime(0.0001, now + ch.t0);
          cg.gain.linearRampToValueAtTime(1.0, now + ch.t0 + 0.35);
          if (ch.fadeAt !== null) {
            cg.gain.setTargetAtTime(0.0001, now + ch.fadeAt, 0.18);
          } else {
            cg.gain.setValueAtTime(1.0, now + 5.0);
            cg.gain.exponentialRampToValueAtTime(0.0001, now + 6.5);
          }
          cg.connect(glChFilter);

          for (var ni = 0; ni < ch.notes.length; ni++) {
            var nFreq = ch.notes[ni];
            for (var di = 0; di < detuneCents.length; di++) {
              var vo = ctx.createOscillator();
              vo.type = 'sawtooth';
              vo.frequency.setValueAtTime(nFreq, now + ch.t0);
              vo.detune.setValueAtTime(detuneCents[di], now + ch.t0);
              var vg = ctx.createGain();
              vg.gain.value = ch.perVoice;
              vo.connect(vg);
              vg.connect(cg);
              vo.start(now + ch.t0);
              vo.stop(now + ch.stopAt);
              glSources.push(vo);
            }
          }
        }

        // Dadd9 低音支点 73.42Hz
        var glSubD = ctx.createOscillator();
        glSubD.type = 'sine';
        glSubD.frequency.setValueAtTime(73.42, now + 3.4);
        var glSubDG = ctx.createGain();
        glSubDG.gain.setValueAtTime(0.0001, now + 3.4);
        glSubDG.gain.linearRampToValueAtTime(0.18, now + 3.75);
        glSubDG.gain.setValueAtTime(0.18, now + 5.0);
        glSubDG.gain.exponentialRampToValueAtTime(0.0001, now + 6.5);
        glSubD.connect(glSubDG);
        glSubDG.connect(glBus);
        glSubD.start(now + 3.4);
        glSubD.stop(now + 6.55);
        glSources.push(glSubD);

        // 3) 钟琴琶音 3.4s 起
        var bellNotes = [587.33, 739.99, 880.0, 1174.66, 1479.98];
        for (var bi = 0; bi < bellNotes.length; bi++) {
          var bt = now + 3.4 + bi * 0.11;
          var bf = bellNotes[bi];
          var b1 = ctx.createOscillator();
          b1.type = 'sine';
          b1.frequency.setValueAtTime(bf, bt);
          var bg1 = ctx.createGain();
          bg1.gain.setValueAtTime(0.0001, bt);
          bg1.gain.linearRampToValueAtTime(0.14, bt + 0.008);
          bg1.gain.exponentialRampToValueAtTime(0.0001, bt + 1.6);
          b1.connect(bg1);
          bg1.connect(glBus);
          b1.start(bt);
          b1.stop(bt + 1.64);
          glSources.push(b1);

          var b2 = ctx.createOscillator();
          b2.type = 'sine';
          b2.frequency.setValueAtTime(bf * 2.76, bt);
          var bg2 = ctx.createGain();
          bg2.gain.setValueAtTime(0.0001, bt);
          bg2.gain.linearRampToValueAtTime(0.14 * 0.3, bt + 0.006);
          bg2.gain.exponentialRampToValueAtTime(0.0001, bt + 1.45);
          b2.connect(bg2);
          bg2.connect(glBus);
          b2.start(bt);
          b2.stop(bt + 1.5);
          glSources.push(b2);
        }

        // 4) 吊镲 3.4s
        var glCy = createNoiseSource(now + 3.4, 2.65);
        glSources.push(glCy);
        var glCyHp = ctx.createBiquadFilter();
        glCyHp.type = 'highpass';
        glCyHp.frequency.value = 4000;
        var glCyG = ctx.createGain();
        glCyG.gain.setValueAtTime(0.0001, now + 3.4);
        glCyG.gain.linearRampToValueAtTime(0.22, now + 3.42);
        glCyG.gain.exponentialRampToValueAtTime(0.0001, now + 6.0);
        glCy.connect(glCyHp);
        glCyHp.connect(glCyG);
        glCyG.connect(glBus);

        registerSlideCleanup(null, function () {
          try {
            glOut.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.05);
          } catch (_) {}
          setTimeout(function () {
            for (var si = 0; si < glSources.length; si++) {
              try {
                glSources[si].stop();
              } catch (_) {}
            }
            try {
              glOut.disconnect();
            } catch (_) {}
          }, 90);
        });
        break;
      }

      case 'ignite': {
        var igSources = [];
        var igOut = ctx.createGain();
        igOut.gain.setValueAtTime(0.88, now);
        igOut.connect(masterGain);

        var igBus = ctx.createGain();
        igBus.gain.value = 1;
        var igDry = ctx.createGain();
        igDry.gain.value = 0.82;
        igBus.connect(igDry);
        igDry.connect(igOut);

        var igRevBuf = ensureGloryReverbBuffer();
        if (igRevBuf) {
          var igConv = ctx.createConvolver();
          igConv.buffer = igRevBuf;
          var igWet = ctx.createGain();
          igWet.gain.value = 0.34;
          igBus.connect(igConv);
          igConv.connect(igWet);
          igWet.connect(igOut);
        }

        var igSub = ctx.createOscillator();
        igSub.type = 'sine';
        igSub.frequency.setValueAtTime(70, now);
        igSub.frequency.exponentialRampToValueAtTime(38, now + 1.2);
        var igSubG = ctx.createGain();
        igSubG.gain.setValueAtTime(0.0001, now);
        igSubG.gain.linearRampToValueAtTime(0.6, now + 0.014);
        igSubG.gain.exponentialRampToValueAtTime(0.0001, now + 1.2);
        igSub.connect(igSubG);
        igSubG.connect(igBus);
        igSub.start(now);
        igSub.stop(now + 1.25);
        igSources.push(igSub);

        var igArc = createNoiseSource(now, 0.28);
        igSources.push(igArc);
        var igBp = ctx.createBiquadFilter();
        igBp.type = 'bandpass';
        igBp.Q.value = 2.0;
        igBp.frequency.setValueAtTime(600, now);
        igBp.frequency.exponentialRampToValueAtTime(5000, now + 0.25);
        var igArcG = ctx.createGain();
        igArcG.gain.setValueAtTime(0.001, now);
        igArcG.gain.linearRampToValueAtTime(0.42, now + 0.03);
        igArcG.gain.exponentialRampToValueAtTime(0.0001, now + 0.26);
        igArc.connect(igBp);
        igBp.connect(igArcG);
        igArcG.connect(igBus);

        var dingFreqs = [1760, 2640];
        for (var di2 = 0; di2 < dingFreqs.length; di2++) {
          var dgO = ctx.createOscillator();
          dgO.type = 'sine';
          dgO.frequency.setValueAtTime(dingFreqs[di2], now + 0.05);
          var dgG = ctx.createGain();
          dgG.gain.setValueAtTime(0.0001, now + 0.05);
          dgG.gain.linearRampToValueAtTime(di2 === 0 ? 0.12 : 0.06, now + 0.058);
          dgG.gain.exponentialRampToValueAtTime(0.0001, now + 1.45);
          dgO.connect(dgG);
          dgG.connect(igBus);
          dgO.start(now + 0.05);
          dgO.stop(now + 1.5);
          igSources.push(dgO);
        }

        registerSlideCleanup(null, function () {
          try {
            igOut.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.04);
          } catch (_) {}
          setTimeout(function () {
            for (var si = 0; si < igSources.length; si++) {
              try {
                igSources[si].stop();
              } catch (_) {}
            }
            try {
              igOut.disconnect();
            } catch (_) {}
          }, 90);
        });
        break;
      }

      case 'boost': {
        var boSources = [];
        var boOut = ctx.createGain();
        boOut.gain.setValueAtTime(0.9, now);
        boOut.connect(masterGain);

        var boLp = ctx.createBiquadFilter();
        boLp.type = 'lowpass';
        boLp.Q.value = 1.6;
        boLp.frequency.setValueAtTime(600, now);
        boLp.frequency.exponentialRampToValueAtTime(6000, now + 1.5);
        var boSawG = ctx.createGain();
        boSawG.gain.setValueAtTime(0.0001, now);
        boSawG.gain.linearRampToValueAtTime(0.22, now + 0.35);
        boSawG.gain.exponentialRampToValueAtTime(0.0001, now + 1.65);
        boLp.connect(boSawG);
        boSawG.connect(boOut);

        var boPair = [
          { f0: 180, f1: 1400 },
          { f0: 181.5, f1: 1410 }
        ];
        for (var bi2 = 0; bi2 < boPair.length; bi2++) {
          var boO = ctx.createOscillator();
          boO.type = 'sawtooth';
          boO.frequency.setValueAtTime(boPair[bi2].f0, now);
          boO.frequency.exponentialRampToValueAtTime(boPair[bi2].f1, now + 1.5);
          boO.connect(boLp);
          boO.start(now);
          boO.stop(now + 1.68);
          boSources.push(boO);
        }

        var boCrack = createNoiseSource(now, 0.1);
        boSources.push(boCrack);
        var boHp = ctx.createBiquadFilter();
        boHp.type = 'highpass';
        boHp.frequency.value = 2500;
        var boCg = ctx.createGain();
        boCg.gain.setValueAtTime(0.3, now);
        boCg.gain.exponentialRampToValueAtTime(0.0001, now + 0.08);
        boCrack.connect(boHp);
        boHp.connect(boCg);
        boCg.connect(boOut);

        var boTail = createNoiseSource(now + 1.4, 0.36);
        boSources.push(boTail);
        var boBp = ctx.createBiquadFilter();
        boBp.type = 'bandpass';
        boBp.Q.value = 1.8;
        boBp.frequency.setValueAtTime(280, now + 1.4);
        boBp.frequency.exponentialRampToValueAtTime(2100, now + 1.54);
        boBp.frequency.exponentialRampToValueAtTime(420, now + 1.75);
        var boTg = ctx.createGain();
        boTg.gain.setValueAtTime(0.001, now + 1.4);
        boTg.gain.linearRampToValueAtTime(0.32, now + 1.49);
        boTg.gain.exponentialRampToValueAtTime(0.0001, now + 1.75);
        boTail.connect(boBp);
        boBp.connect(boTg);
        boTg.connect(boOut);

        registerSlideCleanup(null, function () {
          try {
            boOut.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.04);
          } catch (_) {}
          setTimeout(function () {
            for (var si = 0; si < boSources.length; si++) {
              try {
                boSources[si].stop();
              } catch (_) {}
            }
            try {
              boOut.disconnect();
            } catch (_) {}
          }, 90);
        });
        break;
      }

      case 'bullet': {
        var buSources = [];
        var buOut = ctx.createGain();
        buOut.gain.setValueAtTime(0.9, now);
        buOut.connect(masterGain);

        var buN = createNoiseSource(now, 1.18);
        buSources.push(buN);
        var buLp = ctx.createBiquadFilter();
        buLp.type = 'lowpass';
        buLp.Q.value = 1.2;
        buLp.frequency.setValueAtTime(300, now);
        buLp.frequency.exponentialRampToValueAtTime(2500, now + 1.1);
        var buNG = ctx.createGain();
        buNG.gain.setValueAtTime(0.0001, now);
        buNG.gain.exponentialRampToValueAtTime(0.35, now + 1.1);
        buNG.gain.linearRampToValueAtTime(0.0001, now + 1.15);
        buN.connect(buLp);
        buLp.connect(buNG);
        buNG.connect(buOut);

        var buHum = ctx.createOscillator();
        buHum.type = 'sine';
        buHum.frequency.setValueAtTime(55, now);
        var buHG = ctx.createGain();
        buHG.gain.setValueAtTime(0.0001, now);
        buHG.gain.linearRampToValueAtTime(0.25, now + 1.08);
        buHG.gain.linearRampToValueAtTime(0.0001, now + 1.15);
        buHum.connect(buHG);
        buHG.connect(buOut);
        buHum.start(now);
        buHum.stop(now + 1.18);
        buSources.push(buHum);

        var buDrop = ctx.createOscillator();
        buDrop.type = 'sine';
        buDrop.frequency.setValueAtTime(110, now + 1.1);
        buDrop.frequency.exponentialRampToValueAtTime(72, now + 1.55);
        var buDG = ctx.createGain();
        buDG.gain.setValueAtTime(0.0001, now + 1.1);
        buDG.gain.linearRampToValueAtTime(0.4, now + 1.11);
        buDG.gain.exponentialRampToValueAtTime(0.0001, now + 1.6);
        buDrop.connect(buDG);
        buDG.connect(buOut);
        buDrop.start(now + 1.1);
        buDrop.stop(now + 1.64);
        buSources.push(buDrop);

        registerSlideCleanup(null, function () {
          try {
            buOut.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.04);
          } catch (_) {}
          setTimeout(function () {
            for (var si = 0; si < buSources.length; si++) {
              try {
                buSources[si].stop();
              } catch (_) {}
            }
            try {
              buOut.disconnect();
            } catch (_) {}
          }, 90);
        });
        break;
      }

      default:
        break;
    }
  }

  /* ---------- 持续循环音 (Deck.loop) ---------- */
  function createLoop(name) {
    if (!ctx) {
      return { stop: function () {}, set: function () {} };
    }
    if (ctx.state === 'suspended' && !Deck.isMuted()) {
      ctx.resume().catch(function () {});
    }

    var now = ctx.currentTime;
    var stopped = false;
    var loopOut = ctx.createGain();
    loopOut.gain.setValueAtTime(0.0001, now);
    loopOut.connect(masterGain);

    var sources = [];
    var timers = [];
    var setHandler = null;

    if (name === 'charge') {
      var hum = ctx.createOscillator();
      var sub = ctx.createOscillator();
      var inv = ctx.createOscillator();
      hum.type = 'sawtooth';
      sub.type = 'sine';
      inv.type = 'sine';
      hum.frequency.setValueAtTime(55, now);
      sub.frequency.setValueAtTime(110, now);
      inv.frequency.setValueAtTime(1400, now);

      var humFilter = ctx.createBiquadFilter();
      humFilter.type = 'lowpass';
      humFilter.frequency.setValueAtTime(240, now);

      var invGain = ctx.createGain();
      invGain.gain.setValueAtTime(0.03, now);

      var air = ctx.createBufferSource();
      air.buffer = ensureNoiseBuffer();
      air.loop = true;
      var airFilter = ctx.createBiquadFilter();
      airFilter.type = 'bandpass';
      airFilter.Q.value = 1.4;
      airFilter.frequency.setValueAtTime(520, now);
      var airGain = ctx.createGain();
      airGain.gain.setValueAtTime(0.04, now);

      hum.connect(humFilter);
      sub.connect(humFilter);
      humFilter.connect(loopOut);
      inv.connect(invGain);
      invGain.connect(loopOut);
      air.connect(airFilter);
      airFilter.connect(airGain);
      airGain.connect(loopOut);

      hum.start(now);
      sub.start(now);
      inv.start(now);
      air.start(now);
      sources.push(hum, sub, inv, air);

      setHandler = function (val) {
        var t = ctx.currentTime;
        hum.frequency.setTargetAtTime(55 + val * 55, t, 0.06);
        sub.frequency.setTargetAtTime(110 + val * 110, t, 0.06);
        humFilter.frequency.setTargetAtTime(240 + val * 680, t, 0.06);
        inv.frequency.setTargetAtTime(1400 + val * 2200, t, 0.06);
        invGain.gain.setTargetAtTime(0.025 + val * 0.07, t, 0.06);
        airFilter.frequency.setTargetAtTime(520 + val * 1100, t, 0.06);
        airGain.gain.setTargetAtTime(0.03 + val * 0.08, t, 0.06);
        loopOut.gain.setTargetAtTime(0.08 + val * 0.24, t, 0.06);
      };
      setHandler(0.25);
    } else if (name === 'motor') {
      var m1 = ctx.createOscillator();
      var m2 = ctx.createOscillator();
      m1.type = 'sawtooth';
      m2.type = 'triangle';
      m1.frequency.setValueAtTime(110, now);
      m2.frequency.setValueAtTime(220, now);

      var mFilter = ctx.createBiquadFilter();
      mFilter.type = 'lowpass';
      mFilter.Q.value = 2.0;
      mFilter.frequency.setValueAtTime(360, now);

      var m2Gain = ctx.createGain();
      m2Gain.gain.setValueAtTime(0.35, now);

      m1.connect(mFilter);
      m2.connect(m2Gain);
      m2Gain.connect(mFilter);
      mFilter.connect(loopOut);

      m1.start(now);
      m2.start(now);
      sources.push(m1, m2);

      setHandler = function (val) {
        var t = ctx.currentTime;
        var base = 110 + val * 310;
        m1.frequency.setTargetAtTime(base, t, 0.06);
        m2.frequency.setTargetAtTime(base * 2, t, 0.06);
        mFilter.frequency.setTargetAtTime(360 + val * 2040, t, 0.06);
        loopOut.gain.setTargetAtTime(0.06 + val * 0.2, t, 0.06);
      };
      setHandler(0.2);
    } else if (name === 'rain') {
      var rBed = ctx.createBufferSource();
      rBed.buffer = ensureNoiseBuffer();
      rBed.loop = true;
      var rBp = ctx.createBiquadFilter();
      rBp.type = 'bandpass';
      rBp.frequency.setValueAtTime(1400, now);
      rBp.Q.value = 0.7;
      var rBedG = ctx.createGain();
      rBedG.gain.value = 0.55;

      var rTop = ctx.createBufferSource();
      rTop.buffer = ensureNoiseBuffer();
      rTop.loop = true;
      var rHp = ctx.createBiquadFilter();
      rHp.type = 'highpass';
      rHp.frequency.setValueAtTime(3200, now);
      var rTopG = ctx.createGain();
      rTopG.gain.value = 0.25;

      rBed.connect(rBp);
      rBp.connect(rBedG);
      rBedG.connect(loopOut);
      rTop.connect(rHp);
      rHp.connect(rTopG);
      rTopG.connect(loopOut);

      rBed.start(now);
      rTop.start(now, 0.7);
      sources.push(rBed, rTop);

      var rainDropTimer = setInterval(function () {
        if (stopped || !ctx) return;
        if (Math.random() > 0.65) {
          var t = ctx.currentTime;
          var dropO = ctx.createOscillator();
          dropO.type = 'sine';
          var df = 1200 + Math.random() * 1400;
          dropO.frequency.setValueAtTime(df, t);
          dropO.frequency.exponentialRampToValueAtTime(df * 1.4, t + 0.025);
          var dg = ctx.createGain();
          dg.gain.setValueAtTime(0.001, t);
          dg.gain.linearRampToValueAtTime(0.04, t + 0.003);
          dg.gain.exponentialRampToValueAtTime(0.0001, t + 0.045);
          dropO.connect(dg);
          dg.connect(loopOut);
          dropO.start(t);
          dropO.stop(t + 0.055);
        }
      }, 150);
      timers.push(rainDropTimer);

      setHandler = function (val) {
        var t = ctx.currentTime;
        rBp.frequency.setTargetAtTime(950 + val * 1400, t, 0.12);
        loopOut.gain.setTargetAtTime(0.08 + val * 0.24, t, 0.12);
      };
      setHandler(0.5);
    } else if (name === 'heartbeat') {
      var hbLevel = 0.5;
      var nextBeat = now + 0.04;

      function triggerBeat(t, amp) {
        var o = ctx.createOscillator();
        o.type = 'sine';
        o.frequency.setValueAtTime(92, t);
        o.frequency.exponentialRampToValueAtTime(36, t + 0.14);
        var g = ctx.createGain();
        g.gain.setValueAtTime(0.001, t);
        g.gain.linearRampToValueAtTime(amp, t + 0.012);
        g.gain.exponentialRampToValueAtTime(0.0001, t + 0.18);
        o.connect(g);
        g.connect(loopOut);
        o.start(t);
        o.stop(t + 0.2);
      }

      var hbTimer = setInterval(function () {
        if (stopped || !ctx) return;
        var period = 1.05 - hbLevel * 0.5;
        while (nextBeat < ctx.currentTime + 0.25) {
          triggerBeat(nextBeat, 0.62);
          triggerBeat(nextBeat + 0.21, 0.42);
          nextBeat += period;
        }
      }, 90);
      timers.push(hbTimer);

      setHandler = function (val) {
        hbLevel = val;
        loopOut.gain.setTargetAtTime(0.2 + val * 0.55, ctx.currentTime, 0.08);
      };
      setHandler(0.5);
    } else if (name === 'clock') {
      var ckLevel = 0.5;
      var ckStep = 0;
      var nextTick = now + 0.04;

      function triggerTick(t, isTick) {
        var f = isTick ? 2450 : 1950;
        var n = ctx.createBufferSource();
        n.buffer = ensureNoiseBuffer();
        n.loop = true;
        var bp = ctx.createBiquadFilter();
        bp.type = 'bandpass';
        bp.frequency.value = f;
        bp.Q.value = 3.2;
        var g = ctx.createGain();
        g.gain.setValueAtTime(0.35, t);
        g.gain.exponentialRampToValueAtTime(0.0001, t + 0.024);
        n.connect(bp);
        bp.connect(g);
        g.connect(loopOut);
        n.start(t, Math.random() * 0.4);
        n.stop(t + 0.032);
      }

      var ckTimer = setInterval(function () {
        if (stopped || !ctx) return;
        var stepSec = 0.72 - ckLevel * 0.28;
        while (nextTick < ctx.currentTime + 0.25) {
          triggerTick(nextTick, ckStep % 2 === 0);
          ckStep++;
          nextTick += stepSec;
        }
      }, 80);
      timers.push(ckTimer);

      setHandler = function (val) {
        ckLevel = val;
        loopOut.gain.setTargetAtTime(0.15 + val * 0.35, ctx.currentTime, 0.08);
      };
      setHandler(0.5);
    } else {
      return { stop: function () {}, set: function () {} };
    }

    var handle = {
      set: function (v) {
        if (stopped || !ctx) return;
        setHandler(clamp01(v));
      },
      stop: function () {
        if (stopped) return;
        stopped = true;
        activeLoops.delete(handle);
        for (var ti = 0; ti < timers.length; ti++) {
          clearInterval(timers[ti]);
        }
        timers.length = 0;
        if (!ctx) return;
        var t = ctx.currentTime;
        try {
          loopOut.gain.setTargetAtTime(0.0001, t, 0.02);
        } catch (_) {}
        setTimeout(function () {
          for (var i = 0; i < sources.length; i++) {
            try {
              sources[i].stop();
              sources[i].disconnect();
            } catch (_) {}
          }
          try {
            loopOut.disconnect();
          } catch (_) {}
        }, 80);
      }
    };

    activeLoops.add(handle);
    return handle;
  }

  function stopAllLoops() {
    if (activeLoops.size === 0) return;
    Array.from(activeLoops).forEach(function (loopHandle) {
      loopHandle.stop();
    });
    activeLoops.clear();
  }

  /* ---------- 背景氛围乐 (Deck.ambient) ---------- */
  function startLoungeAmbient() {
    var ambGain = ctx.createGain();
    ambGain.gain.setValueAtTime(0.0001, ctx.currentTime);
    ambGain.gain.linearRampToValueAtTime(0.32, ctx.currentTime + 0.35);
    ambGain.connect(masterGain);

    var lp = ctx.createBiquadFilter();
    lp.type = 'lowpass';
    lp.frequency.value = 1800;
    lp.connect(ambGain);

    var stepSec = 0.3;
    var chords = [
      { bass: 87.31, pad: [174.61, 220.0, 261.63, 329.63], arp: [349.23, 440.0, 523.25, 659.25] },
      { bass: 82.41, pad: [164.81, 196.0, 246.94, 293.66], arp: [329.63, 392.0, 493.88, 587.33] },
      { bass: 73.42, pad: [146.83, 174.61, 220.0, 261.63], arp: [293.66, 349.23, 440.0, 523.25] },
      { bass: 65.41, pad: [130.81, 164.81, 196.0, 246.94], arp: [261.63, 329.63, 392.0, 493.88] }
    ];
    var arpPattern = [0, 2, 1, 3, 2, 3, 1, 2];

    var stepIndex = 0;
    var nextTime = ctx.currentTime + 0.04;
    var timer = null;
    var stopped = false;

    function triggerPad(freqs, t, dur) {
      for (var i = 0; i < freqs.length; i++) {
        var o = ctx.createOscillator();
        o.type = i % 2 === 0 ? 'sine' : 'triangle';
        o.frequency.setValueAtTime(freqs[i], t);
        var g = ctx.createGain();
        g.gain.setValueAtTime(0.0001, t);
        g.gain.linearRampToValueAtTime(0.075, t + 0.16);
        g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
        o.connect(g);
        g.connect(lp);
        o.start(t);
        o.stop(t + dur + 0.04);
      }
    }

    function triggerPluck(freq, t) {
      var o = ctx.createOscillator();
      o.type = 'triangle';
      o.frequency.setValueAtTime(freq, t);
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(0.09, t + 0.01);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 0.28);
      o.connect(g);
      g.connect(lp);
      o.start(t);
      o.stop(t + 0.32);
    }

    function triggerBass(freq, t) {
      var o = ctx.createOscillator();
      o.type = 'sine';
      o.frequency.setValueAtTime(freq, t);
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(0.16, t + 0.02);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 0.56);
      o.connect(g);
      g.connect(lp);
      o.start(t);
      o.stop(t + 0.6);
    }

    function triggerBrush(t) {
      var n = ctx.createBufferSource();
      n.buffer = ensureNoiseBuffer();
      n.loop = true;
      var hp = ctx.createBiquadFilter();
      hp.type = 'highpass';
      hp.frequency.value = 5200;
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(0.02, t + 0.005);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 0.055);
      n.connect(hp);
      hp.connect(g);
      g.connect(ambGain);
      n.start(t, Math.random());
      n.stop(t + 0.07);
    }

    function schedule() {
      if (stopped || !ctx) return;
      while (nextTime < ctx.currentTime + 0.3) {
        var bar = Math.floor(stepIndex / 8) % chords.length;
        var beatStep = stepIndex % 8;
        var chord = chords[bar];
        if (beatStep === 0) {
          triggerPad(chord.pad, nextTime, stepSec * 8);
        }
        if (beatStep === 0 || beatStep === 4) {
          triggerBass(chord.bass, nextTime);
        }
        if (beatStep % 2 === 1) {
          triggerBrush(nextTime);
        }
        var noteIdx = arpPattern[beatStep];
        triggerPluck(chord.arp[noteIdx], nextTime);
        nextTime += stepSec;
        stepIndex++;
      }
    }

    schedule();
    timer = setInterval(schedule, 110);

    return function stop() {
      if (stopped) return;
      stopped = true;
      if (timer) clearInterval(timer);
      if (ctx) {
        try {
          ambGain.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.05);
        } catch (_) {}
      }
      setTimeout(function () {
        try {
          lp.disconnect();
          ambGain.disconnect();
        } catch (_) {}
      }, 220);
    };
  }

  function startPoemAmbient() {
    var ambGain = ctx.createGain();
    ambGain.gain.setValueAtTime(0.0001, ctx.currentTime);
    ambGain.gain.linearRampToValueAtTime(0.36, ctx.currentTime + 0.6);
    ambGain.connect(masterGain);

    var padFilter = ctx.createBiquadFilter();
    padFilter.type = 'lowpass';
    padFilter.Q.value = 1.4;
    padFilter.frequency.setValueAtTime(340, ctx.currentTime);
    padFilter.connect(ambGain);

    var breathLfo = ctx.createOscillator();
    var breathDepth = ctx.createGain();
    breathLfo.type = 'sine';
    breathLfo.frequency.value = 0.14;
    breathDepth.gain.value = 190;
    breathLfo.connect(breathDepth);
    breathDepth.connect(padFilter.frequency);
    breathLfo.start(ctx.currentTime);

    var progressions = [
      [73.42, 110.0, 146.83, 174.61],
      [65.41, 98.0, 130.81, 164.81],
      [58.27, 87.31, 116.54, 146.83],
      [55.0, 82.41, 110.0, 164.81]
    ];

    var barSec = 3.6;
    var barIdx = 0;
    var nextTime = ctx.currentTime + 0.05;
    var timer = null;
    var stopped = false;

    function triggerStrings(freqs, t, dur) {
      for (var i = 0; i < freqs.length; i++) {
        var o1 = ctx.createOscillator();
        var o2 = ctx.createOscillator();
        o1.type = 'sawtooth';
        o2.type = 'triangle';
        o1.frequency.setValueAtTime(freqs[i], t);
        o2.frequency.setValueAtTime(freqs[i] * 1.003, t);
        var g = ctx.createGain();
        g.gain.setValueAtTime(0.0001, t);
        g.gain.linearRampToValueAtTime(0.07, t + 0.9);
        g.gain.linearRampToValueAtTime(0.055, t + dur - 0.6);
        g.gain.exponentialRampToValueAtTime(0.0001, t + dur + 0.25);
        o1.connect(g);
        o2.connect(g);
        g.connect(padFilter);
        o1.start(t);
        o2.start(t);
        o1.stop(t + dur + 0.3);
        o2.stop(t + dur + 0.3);
      }
    }

    function triggerTimpani(freq, t) {
      var o = ctx.createOscillator();
      o.type = 'sine';
      o.frequency.setValueAtTime(freq * 1.25, t);
      o.frequency.exponentialRampToValueAtTime(freq, t + 0.14);
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(0.28, t + 0.025);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 1.35);
      o.connect(g);
      g.connect(ambGain);
      o.start(t);
      o.stop(t + 1.4);
    }

    function schedule() {
      if (stopped || !ctx) return;
      while (nextTime < ctx.currentTime + 0.5) {
        var chord = progressions[barIdx % progressions.length];
        triggerStrings(chord, nextTime, barSec);
        if (barIdx % 2 === 0) {
          triggerTimpani(chord[0], nextTime);
        }
        nextTime += barSec;
        barIdx++;
      }
    }

    schedule();
    timer = setInterval(schedule, 220);

    return function stop() {
      if (stopped) return;
      stopped = true;
      if (timer) clearInterval(timer);
      if (ctx) {
        try {
          ambGain.gain.setTargetAtTime(0.0001, ctx.currentTime, 0.06);
        } catch (_) {}
      }
      setTimeout(function () {
        try {
          breathLfo.stop();
          breathLfo.disconnect();
          breathDepth.disconnect();
          padFilter.disconnect();
          ambGain.disconnect();
        } catch (_) {}
      }, 250);
    };
  }

  function stopAmbient() {
    if (!currentAmbient) return;
    var prev = currentAmbient;
    currentAmbient = null;
    if (prev.btn) prev.btn.classList.remove('on');
    if (typeof prev.stop === 'function') prev.stop();
    syncAutoDuck();
  }

  function toggleAmbient(name, btn) {
    if (currentAmbient && currentAmbient.name === name) {
      stopAmbient();
      return false;
    }
    stopAmbient();

    if (!ctx) {
      if (btn) btn.classList.add('on');
      currentAmbient = { name: name, btn: btn, stop: null };
      syncAutoDuck();
      return true;
    }

    if (ctx.state === 'suspended' && !Deck.isMuted()) {
      ctx.resume().catch(function () {});
    }

    var stopFn = name === 'poem' ? startPoemAmbient() : startLoungeAmbient();
    if (btn) btn.classList.add('on');
    currentAmbient = { name: name, btn: btn, stop: stopFn };
    syncAutoDuck();
    return true;
  }

  /* ---------- 全程动态配乐系统 (Deck.score) ---------- */
  function loadScoreManifest() {
    if (manifestRequested) return;
    manifestRequested = true;
    if (
      !global.location ||
      typeof global.location.protocol !== 'string' ||
      global.location.protocol.indexOf('http') !== 0 ||
      typeof global.fetch !== 'function'
    ) {
      return;
    }
    try {
      global
        .fetch(resolveEngineAsset('assets/music/manifest.json'), { cache: 'no-cache' })
        .then(function (res) {
          return res && res.ok ? res.json() : [];
        })
        .then(function (data) {
          scoreManifest = data || [];
        })
        .catch(function () {
          scoreManifest = [];
        });
    } catch (_) {
      scoreManifest = [];
    }
  }

  function resolveManifestUrl(cueName) {
    if (!scoreManifest || !cueName) return null;
    if (Array.isArray(scoreManifest)) {
      if (
        scoreManifest.indexOf(cueName) !== -1 ||
        scoreManifest.indexOf(cueName + '.mp3') !== -1
      ) {
        return resolveEngineAsset('assets/music/' + cueName + '.mp3');
      }
      return null;
    }
    if (typeof scoreManifest === 'object') {
      var val = scoreManifest[cueName];
      if (val === true) return resolveEngineAsset('assets/music/' + cueName + '.mp3');
      if (typeof val === 'string' && val.trim()) return resolveEngineAsset(val.trim());
    }
    return null;
  }

  function isAutoDuckActive() {
    if (modalOpen) return true;
    if (currentAmbient) return true;
    if (currentIndex >= 0 && slides[currentIndex]) {
      var activeSlide = slides[currentIndex];
      for (var i = 0; i < inlineEntries.length; i++) {
        var entry = inlineEntries[i];
        if (entry.slideEl === activeSlide && entry.videoEl) {
          var v = entry.videoEl;
          if (!v.muted && (!v.paused || entry.unmutedIntent) && !v.ended) {
            return true;
          }
        }
      }
    }
    return false;
  }

  function applyDuckGain() {
    isDucked = Boolean(manualDuck || isAutoDuckActive());
    if (scoreBusGain && ctx) {
      var target = isDucked ? SCORE_DUCK_GAIN : 1.0;
      try {
        scoreBusGain.gain.cancelScheduledValues(ctx.currentTime);
        scoreBusGain.gain.setTargetAtTime(
          target,
          ctx.currentTime,
          isDucked ? 0.12 : 0.22
        );
      } catch (_) {}
    }
    if (activeScoreTrack && typeof activeScoreTrack.syncDuck === 'function') {
      activeScoreTrack.syncDuck();
    }
  }

  function syncAutoDuck() {
    applyDuckGain();
  }

  function scoreDuck(on) {
    manualDuck = Boolean(on);
    applyDuckGain();
  }

  function createSynthScoreTrack(name, fadeInSec) {
    var now = ctx.currentTime;
    var trackGain = ctx.createGain();
    trackGain.gain.setValueAtTime(0.0001, now);
    trackGain.gain.linearRampToValueAtTime(1.0, now + Math.max(0.08, fadeInSec));
    trackGain.connect(scoreBusGain);

    var timers = [];
    var continuousNodes = [];
    var extraNodes = [];
    var stopped = false;

    function addTimer(fn, ms) {
      var id = setInterval(fn, ms);
      timers.push(id);
      return id;
    }

    function scheduleDrone(freqs, type, lpfStart, lfoHz, lfoDepth, gainVal) {
      var filt = ctx.createBiquadFilter();
      filt.type = 'lowpass';
      filt.Q.value = 1.3;
      filt.frequency.setValueAtTime(lpfStart, now);

      var g = ctx.createGain();
      g.gain.value = gainVal;
      filt.connect(g);
      g.connect(trackGain);
      extraNodes.push(filt, g);

      if (lfoHz > 0 && lfoDepth > 0) {
        var lfo = ctx.createOscillator();
        var lfoG = ctx.createGain();
        lfo.type = 'sine';
        lfo.frequency.value = lfoHz;
        lfoG.gain.value = lfoDepth;
        lfo.connect(lfoG);
        lfoG.connect(filt.frequency);
        lfo.start(now);
        continuousNodes.push(lfo);
        extraNodes.push(lfoG);
      }

      for (var i = 0; i < freqs.length; i++) {
        var o = ctx.createOscillator();
        o.type = type;
        o.frequency.setValueAtTime(freqs[i], now);
        o.connect(filt);
        o.start(now);
        continuousNodes.push(o);
      }
      return { filter: filt, gain: g };
    }

    function playNote(freq, t, dur, type, amp, dest, attack) {
      var o = ctx.createOscillator();
      o.type = type || 'sine';
      o.frequency.setValueAtTime(freq, t);
      var g = ctx.createGain();
      var atk = attack || 0.015;
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(amp, t + atk);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      o.connect(g);
      g.connect(dest || trackGain);
      o.start(t);
      o.stop(t + dur + 0.04);
    }

    function playKick(t, fStart, fEnd, dur, amp) {
      var o = ctx.createOscillator();
      o.type = 'sine';
      o.frequency.setValueAtTime(fStart, t);
      o.frequency.exponentialRampToValueAtTime(fEnd, t + Math.min(0.14, dur * 0.6));
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(amp, t + 0.006);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      o.connect(g);
      g.connect(trackGain);
      o.start(t);
      o.stop(t + dur + 0.03);
    }

    function playNoiseHit(t, dur, fType, freq, q, amp) {
      var n = ctx.createBufferSource();
      n.buffer = ensureNoiseBuffer();
      n.loop = true;
      var f = ctx.createBiquadFilter();
      f.type = fType || 'bandpass';
      f.frequency.setValueAtTime(freq, t);
      if (q) f.Q.value = q;
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.linearRampToValueAtTime(amp, t + 0.004);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      n.connect(f);
      f.connect(g);
      g.connect(trackGain);
      n.start(t, Math.random() * 0.5);
      n.stop(t + dur + 0.03);
    }

    if (name === 'tension') {
      scheduleDrone([36.71, 73.42, 110.0], 'sawtooth', 175, 0.18, 95, 0.22);
      var hbNext = now + 0.06;
      var shimmerStep = 0;
      addTimer(function () {
        if (stopped || !ctx) return;
        while (hbNext < ctx.currentTime + 0.35) {
          playKick(hbNext, 86, 36, 0.2, 0.26);
          playKick(hbNext + 0.22, 74, 34, 0.16, 0.16);
          if (shimmerStep % 2 === 0) {
            playNote(shimmerStep % 4 === 0 ? 1760 : 2637, hbNext + 0.45, 0.42, 'sine', 0.032);
            playNoiseHit(hbNext + 0.45, 0.18, 'bandpass', 3600, 5.0, 0.035);
          }
          hbNext += 0.96;
          shimmerStep++;
        }
      }, 120);
    } else if (name === 'rise') {
      var riseChords = [
        [130.81, 196.0, 246.94, 293.66],
        [146.83, 220.0, 277.18, 329.63],
        [174.61, 261.63, 329.63, 392.0],
        [196.0, 293.66, 369.99, 440.0]
      ];
      var arpSeq = [261.63, 293.66, 329.63, 392.0, 440.0, 493.88, 587.33, 659.25];
      var rStep = 0;
      var rNext = now + 0.05;
      var rLp = ctx.createBiquadFilter();
      rLp.type = 'lowpass';
      rLp.frequency.setValueAtTime(900, now);
      rLp.connect(trackGain);
      extraNodes.push(rLp);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (rNext < ctx.currentTime + 0.35) {
          var bar = Math.floor(rStep / 8) % riseChords.length;
          var pos = rStep % 8;
          if (pos === 0) {
            var ch = riseChords[bar];
            for (var ci = 0; ci < ch.length; ci++) {
              playNote(ch[ci], rNext, 2.9, ci === 0 ? 'triangle' : 'sine', 0.06, rLp, 0.45);
            }
          }
          playNote(arpSeq[pos] * (bar >= 2 ? 1.122 : 1), rNext, 0.52, 'triangle', 0.075, rLp, 0.02);
          rNext += 0.36;
          rStep++;
        }
      }, 110);
    } else if (name === 'drive') {
      // 104 BPM -> 8th note = 60 / 104 / 2 = 0.28846s
      var stepD = 60 / 104 / 2;
      var bassProg = [82.41, 82.41, 98.0, 110.0];
      var dStep = 0;
      var dNext = now + 0.05;
      var dLp = ctx.createBiquadFilter();
      dLp.type = 'lowpass';
      dLp.frequency.value = 680;
      dLp.connect(trackGain);
      extraNodes.push(dLp);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (dNext < ctx.currentTime + 0.3) {
          var bar = Math.floor(dStep / 8) % bassProg.length;
          var pos = dStep % 8;
          var root = bassProg[bar];
          var bassF = pos % 2 === 0 ? root : root * 2;
          playNote(bassF, dNext, 0.22, 'sawtooth', 0.14, dLp, 0.008);
          if (pos === 0 || pos === 4) {
            playKick(dNext, 130, 44, 0.18, 0.28);
          }
          if (pos === 2 || pos === 6) {
            playNoiseHit(dNext, 0.085, 'bandpass', 1800, 1.4, 0.16);
          }
          if (pos % 2 === 1) {
            playNoiseHit(dNext, 0.035, 'highpass', 5800, 1.0, 0.05);
          }
          dNext += stepD;
          dStep++;
        }
      }, 90);
    } else if (name === 'dark') {
      scheduleDrone([65.41, 77.78, 98.0, 123.47], 'sawtooth', 260, 0.12, 130, 0.16);
      var dkStep = 0;
      var dkNext = now + 0.06;
      addTimer(function () {
        if (stopped || !ctx) return;
        while (dkNext < ctx.currentTime + 0.35) {
          playNoiseHit(dkNext, 0.024, 'bandpass', dkStep % 2 === 0 ? 2300 : 1850, 3.0, 0.07);
          if (dkStep % 8 === 0) {
            playNoiseHit(dkNext + 0.1, 1.45, 'lowpass', 120, 1.4, 0.18);
          }
          dkNext += 0.72;
          dkStep++;
        }
      }, 130);
    } else if (name === 'race') {
      var rcStep = 0;
      var rcNext = now + 0.04;
      var rcProg = [82.41, 87.31, 82.41, 98.0, 116.54, 98.0, 87.31, 82.41];
      var rcLp = ctx.createBiquadFilter();
      rcLp.type = 'lowpass';
      rcLp.frequency.value = 820;
      rcLp.connect(trackGain);
      extraNodes.push(rcLp);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (rcNext < ctx.currentTime + 0.28) {
          var f = rcProg[rcStep % rcProg.length];
          playNote(f, rcNext, 0.1, 'sawtooth', 0.15, rcLp, 0.005);
          if (rcStep % 4 === 0) playKick(rcNext, 135, 48, 0.12, 0.24);
          if (rcStep % 4 === 2) playNoiseHit(rcNext, 0.045, 'bandpass', 2600, 1.8, 0.11);
          rcNext += 0.11;
          rcStep++;
        }
      }, 75);
    } else if (name === 'epic') {
      var epChords = [
        [73.42, 110.0, 146.83, 220.0],
        [58.27, 87.31, 116.54, 174.61],
        [65.41, 98.0, 130.81, 196.0],
        [73.42, 110.0, 146.83, 220.0]
      ];
      var epBar = 0;
      var epNext = now + 0.05;
      var epLp = ctx.createBiquadFilter();
      epLp.type = 'lowpass';
      epLp.frequency.value = 720;
      epLp.connect(trackGain);
      extraNodes.push(epLp);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (epNext < ctx.currentTime + 0.45) {
          var ch = epChords[epBar % epChords.length];
          for (var i = 0; i < ch.length; i++) {
            playNote(ch[i], epNext, 3.1, i < 2 ? 'sawtooth' : 'triangle', 0.085, epLp, 0.35);
          }
          playKick(epNext, 108, 36, 0.42, 0.42);
          playKick(epNext + 1.5, 96, 36, 0.34, 0.3);
          playKick(epNext + 2.25, 92, 34, 0.28, 0.26);
          epNext += 3.0;
          epBar++;
        }
      }, 180);
    } else if (name === 'warm') {
      var wmChords = [
        { pad: [174.61, 220.0, 261.63, 329.63], bell: [698.46, 880.0, 1046.5] },
        { pad: [164.81, 196.0, 261.63, 329.63], bell: [659.25, 783.99, 1046.5] },
        { pad: [146.83, 174.61, 220.0, 261.63], bell: [587.33, 698.46, 880.0] },
        { pad: [130.81, 196.0, 246.94, 329.63], bell: [523.25, 783.99, 987.77] }
      ];
      var wStep = 0;
      var wNext = now + 0.05;
      addTimer(function () {
        if (stopped || !ctx) return;
        while (wNext < ctx.currentTime + 0.38) {
          var bar = Math.floor(wStep / 4) % wmChords.length;
          var pos = wStep % 4;
          var entry = wmChords[bar];
          if (pos === 0) {
            for (var i = 0; i < entry.pad.length; i++) {
              playNote(entry.pad[i], wNext, 2.3, 'sine', 0.068, trackGain, 0.3);
            }
          }
          var bNote = entry.bell[(pos + bar) % entry.bell.length];
          playNote(bNote, wNext, 0.72, 'sine', 0.055, trackGain, 0.008);
          playNote(bNote * 2, wNext, 0.35, 'triangle', 0.018, trackGain, 0.006);
          wNext += 0.56;
          wStep++;
        }
      }, 120);
    } else if (name === 'drums') {
      var dmStep = 0;
      var dmNext = now + 0.04;
      var dmBeat = 60 / 112 / 2; // ~0.268s
      scheduleDrone([55.0, 82.41], 'sawtooth', 160, 0.2, 60, 0.14);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (dmNext < ctx.currentTime + 0.3) {
          var pos = dmStep % 8;
          if (pos === 0 || pos === 3 || pos === 4 || pos === 6) {
            playKick(dmNext, pos === 0 ? 124 : 104, 38, 0.24, pos === 0 ? 0.42 : 0.3);
          }
          if (pos === 2 || pos === 5 || pos === 7) {
            playNoiseHit(dmNext, 0.08, 'bandpass', 920, 1.5, 0.16);
          }
          dmNext += dmBeat;
          dmStep++;
        }
      }, 90);
    } else if (name === 'drop') {
      // 极弱环境丝响（突显打字机电报声）
      var silk = ctx.createBufferSource();
      silk.buffer = ensureNoiseBuffer();
      silk.loop = true;
      var sBp = ctx.createBiquadFilter();
      sBp.type = 'bandpass';
      sBp.frequency.value = 2400;
      sBp.Q.value = 1.6;
      var sG = ctx.createGain();
      sG.gain.value = 0.022;
      silk.connect(sBp);
      sBp.connect(sG);
      sG.connect(trackGain);
      silk.start(now);
      continuousNodes.push(silk);
      extraNodes.push(sBp, sG);
      scheduleDrone([48.99], 'sine', 90, 0, 0, 0.032);
    } else if (name === 'anthem') {
      var antChords = [
        [65.41, 130.81, 196.0, 261.63, 329.63],
        [61.74, 123.47, 196.0, 246.94, 392.0],
        [55.0, 110.0, 164.81, 220.0, 329.63],
        [87.31, 130.81, 174.61, 261.63, 349.23]
      ];
      var antBar = 0;
      var antNext = now + 0.05;
      var antLp = ctx.createBiquadFilter();
      antLp.type = 'lowpass';
      antLp.frequency.value = 1350;
      antLp.connect(trackGain);
      extraNodes.push(antLp);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (antNext < ctx.currentTime + 0.45) {
          var ch = antChords[antBar % antChords.length];
          for (var i = 0; i < ch.length; i++) {
            playNote(ch[i], antNext, 2.75, i < 2 ? 'triangle' : 'sine', 0.075, antLp, 0.42);
            if (i === 2 || i === 3) {
              playNote(ch[i] * 1.002, antNext, 2.75, 'sawtooth', 0.028, antLp, 0.5);
            }
          }
          playKick(antNext, 98, 42, 0.35, 0.22);
          antNext += 2.4;
          antBar++;
        }
      }, 170);
    } else if (name === 'lounge') {
      var lgChords = [
        { bass: 87.31, pad: [174.61, 220.0, 261.63, 329.63], arp: [349.23, 440.0, 523.25, 659.25] },
        { bass: 82.41, pad: [164.81, 196.0, 246.94, 293.66], arp: [329.63, 392.0, 493.88, 587.33] },
        { bass: 73.42, pad: [146.83, 174.61, 220.0, 261.63], arp: [293.66, 349.23, 440.0, 523.25] },
        { bass: 65.41, pad: [130.81, 164.81, 196.0, 246.94], arp: [261.63, 329.63, 392.0, 493.88] }
      ];
      var lgPattern = [0, 2, 1, 3, 2, 3, 1, 2];
      var lgStep = 0;
      var lgNext = now + 0.05;
      var lgLp = ctx.createBiquadFilter();
      lgLp.type = 'lowpass';
      lgLp.frequency.value = 1750;
      lgLp.connect(trackGain);
      extraNodes.push(lgLp);
      addTimer(function () {
        if (stopped || !ctx) return;
        while (lgNext < ctx.currentTime + 0.32) {
          var bar = Math.floor(lgStep / 8) % lgChords.length;
          var pos = lgStep % 8;
          var ch = lgChords[bar];
          if (pos === 0) {
            for (var pi = 0; pi < ch.pad.length; pi++) {
              playNote(ch.pad[pi], lgNext, 2.3, pi % 2 === 0 ? 'sine' : 'triangle', 0.055, lgLp, 0.14);
            }
          }
          if (pos === 0 || pos === 4) {
            playNote(ch.bass, lgNext, 0.55, 'sine', 0.13, lgLp, 0.02);
          }
          if (pos % 2 === 1) {
            playNoiseHit(lgNext, 0.045, 'highpass', 5200, 1.0, 0.022);
          }
          playNote(ch.arp[lgPattern[pos]], lgNext, 0.28, 'triangle', 0.075, lgLp, 0.01);
          lgNext += 0.3;
          lgStep++;
        }
      }, 100);
    }

    return {
      name: name,
      isMp3: false,
      stop: function (fadeOutSec) {
        if (stopped) return;
        stopped = true;
        for (var i = 0; i < timers.length; i++) clearInterval(timers[i]);
        timers.length = 0;
        var outDur = Math.max(0.08, fadeOutSec || SCORE_CROSSFADE_SEC);
        if (ctx) {
          try {
            var t = ctx.currentTime;
            trackGain.gain.cancelScheduledValues(t);
            trackGain.gain.setValueAtTime(trackGain.gain.value, t);
            trackGain.gain.linearRampToValueAtTime(0.0001, t + outDur);
          } catch (_) {}
        }
        setTimeout(function () {
          for (var j = 0; j < continuousNodes.length; j++) {
            try {
              continuousNodes[j].stop();
              continuousNodes[j].disconnect();
            } catch (_) {}
          }
          for (var k = 0; k < extraNodes.length; k++) {
            try {
              extraNodes[k].disconnect();
            } catch (_) {}
          }
          try {
            trackGain.disconnect();
          } catch (_) {}
        }, (outDur + 0.1) * 1000);
      }
    };
  }

  function createMp3ScoreTrack(name, url, fadeInSec) {
    var audio = document.createElement('audio');
    audio.src = url;
    audio.loop = true;
    audio.preload = 'auto';
    audio.setAttribute('playsinline', '');
    audio.setAttribute('webkit-playsinline', 'true');
    audio.setAttribute('x5-playsinline', 'true');

    var stopped = false;
    var trackGain = null;
    var mediaSrc = null;
    var fadeTimer = null;

    try {
      mediaSrc = ctx.createMediaElementSource(audio);
      trackGain = ctx.createGain();
      trackGain.gain.setValueAtTime(0.0001, ctx.currentTime);
      trackGain.gain.linearRampToValueAtTime(1.0, ctx.currentTime + Math.max(0.08, fadeInSec));
      mediaSrc.connect(trackGain);
      trackGain.connect(scoreBusGain);
    } catch (_) {
      trackGain = null;
      audio.muted = userMuted || !Deck.audioReady;
      audio.volume = isDucked ? SCORE_DUCK_GAIN : 1;
    }

    audio.onerror = function () {
      if (stopped) return;
      stopped = true;
      if (currentCueName === name) {
        activeScoreTrack = createSynthScoreTrack(name, 0.35);
      }
    };

    var p = audio.play();
    if (p && typeof p.catch === 'function') {
      p.catch(function () {});
    }

    return {
      name: name,
      isMp3: true,
      syncDuck: function () {
        if (!trackGain) {
          audio.volume = isDucked ? SCORE_DUCK_GAIN : 1;
        }
      },
      syncMute: function () {
        if (!trackGain) {
          audio.muted = userMuted || !Deck.audioReady;
        }
      },
      stop: function (fadeOutSec) {
        if (stopped) return;
        stopped = true;
        var outDur = Math.max(0.08, fadeOutSec || SCORE_CROSSFADE_SEC);
        if (trackGain && ctx) {
          try {
            var t = ctx.currentTime;
            trackGain.gain.cancelScheduledValues(t);
            trackGain.gain.setValueAtTime(trackGain.gain.value, t);
            trackGain.gain.linearRampToValueAtTime(0.0001, t + outDur);
          } catch (_) {}
        } else {
          audio.volume = 0;
        }
        fadeTimer = setTimeout(function () {
          try {
            audio.pause();
            audio.removeAttribute('src');
            audio.load();
          } catch (_) {}
          try {
            if (mediaSrc) mediaSrc.disconnect();
            if (trackGain) trackGain.disconnect();
          } catch (_) {}
        }, (outDur + 0.1) * 1000);
        void fadeTimer;
      }
    };
  }

  function startScoreTrack(name, fadeInSec) {
    var mp3Url = resolveManifestUrl(name);
    if (mp3Url) {
      return createMp3ScoreTrack(name, mp3Url, fadeInSec);
    }
    return createSynthScoreTrack(name, fadeInSec);
  }

  function scoreCue(name) {
    if (!name || typeof name !== 'string') return;
    var cueName = name.trim();
    if (!cueName) return;

    if (cueName === currentCueName) {
      if (
        ctx &&
        cueName !== 'silence' &&
        (!activeScoreTrack || activeScoreTrack.name !== cueName)
      ) {
        activeScoreTrack = startScoreTrack(cueName, SCORE_CROSSFADE_SEC);
        applyDuckGain();
      }
      return;
    }

    currentCueName = cueName;

    var isDrop = cueName === 'drop';
    var fadeOutSec = isDrop ? 0.2 : SCORE_CROSSFADE_SEC;
    var fadeInSec = isDrop ? 0.35 : SCORE_CROSSFADE_SEC;

    if (activeScoreTrack) {
      activeScoreTrack.stop(fadeOutSec);
      activeScoreTrack = null;
    }

    if (cueName === 'silence' || !ctx) {
      return;
    }

    if (ctx.state === 'suspended' && !Deck.isMuted()) {
      ctx.resume().catch(function () {});
    }

    activeScoreTrack = startScoreTrack(cueName, fadeInSec);
    applyDuckGain();
  }

  /* ---------- 转场视觉效果 ---------- */
  function spawnStreak() {
    if (!viewportEl) return;
    var wrap = document.createElement('div');
    wrap.className = 'fx-streak';
    var bar = document.createElement('div');
    bar.className = 'fx-streak-bar';
    wrap.appendChild(bar);
    viewportEl.appendChild(wrap);
    transientNodes.add(wrap);
    setTimeout(function () {
      removeTransientNode(wrap);
    }, 620);
  }

  function spawnChapterTransition(chapterText) {
    if (!viewportEl || !chapterText) return;
    var old = viewportEl.querySelectorAll('.fx-chapter');
    for (var i = 0; i < old.length; i++) {
      removeTransientNode(old[i]);
    }
    var wrap = document.createElement('div');
    wrap.className = 'fx-chapter';
    var ch = document.createElement('div');
    ch.className = 'fx-chapter-char';
    ch.textContent = chapterText;
    wrap.appendChild(ch);
    viewportEl.appendChild(wrap);
    transientNodes.add(wrap);
    setTimeout(function () {
      removeTransientNode(wrap);
    }, 950);
  }

  /* ---------- 导演特效库 (Deck.fx) ---------- */
  function getSlideMetric(el) {
    var slideEl =
      (el && el.closest && el.closest('.slide')) ||
      (currentIndex >= 0 ? slides[currentIndex] : null);
    if (!slideEl || !el) return null;
    if (el === slideEl) {
      return {
        slideEl: slideEl,
        left: 0,
        top: 0,
        width: STAGE_W,
        height: STAGE_H,
        cx: STAGE_W / 2,
        cy: STAGE_H / 2
      };
    }
    var sr = slideEl.getBoundingClientRect();
    var er = el.getBoundingClientRect();
    var scale = sr.width > 0 ? sr.width / STAGE_W : 1;
    var left = (er.left - sr.left) / scale;
    var top = (er.top - sr.top) / scale;
    var width = er.width / scale;
    var height = er.height / scale;
    return {
      slideEl: slideEl,
      left: left,
      top: top,
      width: width,
      height: height,
      cx: left + width / 2,
      cy: top + height / 2
    };
  }

  function fxShake(power) {
    var activeSlide = currentIndex >= 0 ? slides[currentIndex] : null;
    if (!activeSlide) return;
    var p = Number(power);
    if (!Number.isFinite(p) || p <= 0) p = 1;
    p = Math.max(0.2, Math.min(p, 4));

    if (activeShakeAnim) {
      try {
        activeShakeAnim.cancel();
      } catch (_) {}
      activeShakeAnim = null;
    }
    if (activeShakeTimer) {
      clearTimeout(activeShakeTimer);
      activeShakeTimer = null;
    }
    if (activeShakeEl) {
      activeShakeEl.classList.remove('fx-shaking');
      activeShakeEl = null;
    }

    if (typeof activeSlide.animate === 'function') {
      activeShakeEl = activeSlide;
      activeShakeAnim = activeSlide.animate(
        [
          { transform: 'translate3d(0, 0, 0)' },
          { transform: 'translate3d(' + (-10 * p) + 'px, ' + (6 * p) + 'px, 0)' },
          { transform: 'translate3d(' + (9 * p) + 'px, ' + (-7 * p) + 'px, 0)' },
          { transform: 'translate3d(' + (-7 * p) + 'px, ' + (-4 * p) + 'px, 0)' },
          { transform: 'translate3d(' + (6 * p) + 'px, ' + (5 * p) + 'px, 0)' },
          { transform: 'translate3d(' + (-3 * p) + 'px, ' + (-2 * p) + 'px, 0)' },
          { transform: 'translate3d(0, 0, 0)' }
        ],
        { duration: 380, easing: 'cubic-bezier(0.36, 0.07, 0.19, 0.97)' }
      );
      activeShakeAnim.onfinish = function () {
        activeShakeAnim = null;
        activeShakeEl = null;
      };
    } else {
      activeShakeEl = activeSlide;
      activeSlide.classList.add('fx-shaking');
      activeShakeTimer = setTimeout(function () {
        if (activeShakeEl) activeShakeEl.classList.remove('fx-shaking');
        activeShakeEl = null;
        activeShakeTimer = null;
      }, 400);
    }
  }

  function fxFlash(color) {
    if (!viewportEl) return;
    var el = document.createElement('div');
    el.className = 'fx-flash';
    el.style.background = color || '#ffffff';
    el.style.opacity = '0.82';
    el.style.transition = 'opacity 0.34s cubic-bezier(0.22, 1, 0.36, 1)';
    viewportEl.appendChild(el);
    transientNodes.add(el);
    global.requestAnimationFrame(function () {
      global.requestAnimationFrame(function () {
        el.style.opacity = '0';
      });
    });
    setTimeout(function () {
      removeTransientNode(el);
    }, 390);
  }

  function fxSweep(el) {
    var m = getSlideMetric(el);
    if (!m || m.width <= 0 || m.height <= 0) return;
    var box = document.createElement('div');
    box.className = 'fx-sweep-box';
    box.style.left = m.left + 'px';
    box.style.top = m.top + 'px';
    box.style.width = m.width + 'px';
    box.style.height = m.height + 'px';
    try {
      box.style.borderRadius = global.getComputedStyle(el).borderRadius || '0px';
    } catch (_) {}

    var beam = document.createElement('div');
    beam.className = 'fx-sweep-beam';
    box.appendChild(beam);
    m.slideEl.appendChild(box);

    var cleaned = false;
    function clean() {
      if (cleaned) return;
      cleaned = true;
      if (box.parentNode) box.parentNode.removeChild(box);
    }
    var tid = setTimeout(clean, 780);
    registerSlideCleanup(m.slideEl, function () {
      clearTimeout(tid);
      clean();
    });
  }

  function fxSparks(el, opts) {
    var m = getSlideMetric(el);
    if (!m) return;
    var o = opts || {};
    var count = Number(o.count) > 0 ? Math.min(Number(o.count), 80) : 18;
    var color = o.color || '#FF5500';

    var layer = document.createElement('div');
    layer.className = 'fx-sparks-layer';
    m.slideEl.appendChild(layer);

    for (var i = 0; i < count; i++) {
      var dot = document.createElement('span');
      dot.className = 'fx-spark';
      var size = 4 + Math.random() * 6;
      var angle = (Math.PI * 2 * i) / count + (Math.random() - 0.5) * 0.45;
      var dist = 70 + Math.random() * 220;
      var dx = Math.cos(angle) * dist;
      var dy = Math.sin(angle) * dist + 24;
      var dur = 500 + Math.random() * 380;

      dot.style.width = size + 'px';
      dot.style.height = size + 'px';
      dot.style.left = m.cx - size / 2 + 'px';
      dot.style.top = m.cy - size / 2 + 'px';
      dot.style.background = color;
      dot.style.boxShadow = '0 0 ' + Math.round(size * 2) + 'px ' + color;
      dot.style.opacity = '1';
      dot.style.transition =
        'transform ' +
        dur +
        'ms cubic-bezier(0.16, 1, 0.3, 1), opacity ' +
        dur +
        'ms ease-out';

      layer.appendChild(dot);
      (function (d, tx, ty) {
        global.requestAnimationFrame(function () {
          d.style.transform = 'translate3d(' + tx + 'px, ' + ty + 'px, 0) scale(0.15)';
          d.style.opacity = '0';
        });
      })(dot, dx, dy);
    }

    var cleaned = false;
    function clean() {
      if (cleaned) return;
      cleaned = true;
      if (layer.parentNode) layer.parentNode.removeChild(layer);
    }
    var tid = setTimeout(clean, 960);
    registerSlideCleanup(m.slideEl, function () {
      clearTimeout(tid);
      clean();
    });
  }

  function fxParticles(el, type) {
    var noop = { stop: function () {} };
    if (!el) return noop;

    var slideEl =
      (el.closest && el.closest('.slide')) ||
      (currentIndex >= 0 ? slides[currentIndex] : null);
    var isVoid = Boolean(VOID_TAGS[el.tagName]);
    var host = isVoid ? slideEl || el.parentElement : el;
    if (!host) return noop;

    var prevPos = null;
    try {
      if (global.getComputedStyle(host).position === 'static') {
        prevPos = host.style.position;
        host.style.position = 'relative';
      }
    } catch (_) {}

    var w = host.clientWidth || host.offsetWidth || STAGE_W;
    var h = host.clientHeight || host.offsetHeight || STAGE_H;

    var canvas = document.createElement('canvas');
    canvas.className = 'fx-particles-canvas';
    canvas.width = w;
    canvas.height = h;
    host.appendChild(canvas);

    var ctx2d = null;
    try {
      ctx2d = canvas.getContext('2d');
    } catch (_) {}

    var kind = type || 'dust';
    var count =
      kind === 'rain' ? 75 : kind === 'fireflies' ? 28 : kind === 'ember' ? 42 : 46;
    var items = [];
    for (var i = 0; i < count; i++) {
      items.push(makeParticle(kind, w, h, true));
    }

    function makeParticle(k, width, height, init) {
      if (k === 'rain') {
        return {
          x: Math.random() * width,
          y: init ? Math.random() * height : -40,
          vx: -1.8 - Math.random() * 1.2,
          vy: 14 + Math.random() * 10,
          len: 18 + Math.random() * 24,
          alpha: 0.16 + Math.random() * 0.28
        };
      }
      if (k === 'ember') {
        return {
          x: Math.random() * width,
          y: init ? Math.random() * height : height + 10,
          vx: (Math.random() - 0.5) * 0.9,
          vy: -(1.1 + Math.random() * 2.1),
          r: 1.5 + Math.random() * 2.8,
          phase: Math.random() * Math.PI * 2,
          alpha: 0.35 + Math.random() * 0.55,
          color: Math.random() > 0.35 ? '#FF5500' : '#FFB366'
        };
      }
      if (k === 'gold') {
        return {
          x: Math.random() * width,
          y: init ? Math.random() * height : height + 10,
          vx: (Math.random() - 0.5) * 0.65,
          vy: -(0.4 + Math.random() * 0.95),
          r: 1.4 + Math.random() * 2.6,
          phase: Math.random() * Math.PI * 2,
          alpha: 0.25 + Math.random() * 0.55
        };
      }
      if (k === 'fireflies') {
        return {
          x: Math.random() * width,
          y: Math.random() * height,
          vx: (Math.random() - 0.5) * 0.7,
          vy: (Math.random() - 0.5) * 0.6,
          r: 2.0 + Math.random() * 2.6,
          phase: Math.random() * Math.PI * 2,
          speed: 0.025 + Math.random() * 0.03,
          color: Math.random() > 0.4 ? '#FFE082' : '#C6FF8E'
        };
      }
      // dust
      return {
        x: Math.random() * width,
        y: Math.random() * height,
        vx: (Math.random() - 0.5) * 0.45,
        vy: -(0.15 + Math.random() * 0.45),
        r: 1.0 + Math.random() * 2.0,
        phase: Math.random() * Math.PI * 2,
        alpha: 0.14 + Math.random() * 0.3
      };
    }

    var rafId = null;
    var stopped = false;

    function tick() {
      if (stopped) return;
      if (ctx2d) {
        ctx2d.clearRect(0, 0, w, h);
        for (var i = 0; i < items.length; i++) {
          var p = items[i];
          if (kind === 'rain') {
            p.x += p.vx;
            p.y += p.vy;
            if (p.y > h + 40 || p.x < -40) {
              items[i] = makeParticle('rain', w, h, false);
              continue;
            }
            ctx2d.strokeStyle = 'rgba(205, 224, 255, ' + p.alpha + ')';
            ctx2d.lineWidth = 1.1;
            ctx2d.beginPath();
            ctx2d.moveTo(p.x, p.y);
            ctx2d.lineTo(p.x + p.vx * 1.4, p.y + p.len);
            ctx2d.stroke();
          } else if (kind === 'ember') {
            p.phase += 0.05;
            p.x += p.vx + Math.sin(p.phase) * 0.45;
            p.y += p.vy;
            if (p.y < -16) {
              items[i] = makeParticle('ember', w, h, false);
              continue;
            }
            var eAlpha = p.alpha * (0.65 + 0.35 * Math.sin(p.phase * 1.7));
            ctx2d.save();
            ctx2d.globalAlpha = eAlpha;
            ctx2d.fillStyle = p.color;
            ctx2d.shadowColor = '#FF5500';
            ctx2d.shadowBlur = 10;
            ctx2d.beginPath();
            ctx2d.arc(p.x, p.y, p.r, 0, Math.PI * 2);
            ctx2d.fill();
            ctx2d.restore();
          } else if (kind === 'gold') {
            p.phase += 0.04;
            p.x += p.vx + Math.sin(p.phase) * 0.3;
            p.y += p.vy;
            if (p.y < -12) {
              items[i] = makeParticle('gold', w, h, false);
              continue;
            }
            var gAlpha = p.alpha * (0.55 + 0.45 * Math.sin(p.phase * 1.9));
            ctx2d.save();
            ctx2d.globalAlpha = gAlpha;
            ctx2d.fillStyle = '#E5B95C';
            ctx2d.shadowColor = '#FFE09A';
            ctx2d.shadowBlur = 8;
            ctx2d.beginPath();
            ctx2d.arc(p.x, p.y, p.r, 0, Math.PI * 2);
            ctx2d.fill();
            ctx2d.restore();
          } else if (kind === 'fireflies') {
            p.phase += p.speed;
            p.x += p.vx + Math.cos(p.phase * 0.8) * 0.35;
            p.y += p.vy + Math.sin(p.phase * 0.9) * 0.35;
            if (p.x < 0) p.x = w;
            if (p.x > w) p.x = 0;
            if (p.y < 0) p.y = h;
            if (p.y > h) p.y = 0;
            var fAlpha = 0.15 + 0.72 * (0.5 + 0.5 * Math.sin(p.phase));
            ctx2d.save();
            ctx2d.globalAlpha = fAlpha;
            ctx2d.fillStyle = p.color;
            ctx2d.shadowColor = p.color;
            ctx2d.shadowBlur = 14;
            ctx2d.beginPath();
            ctx2d.arc(p.x, p.y, p.r, 0, Math.PI * 2);
            ctx2d.fill();
            ctx2d.restore();
          } else {
            p.phase += 0.025;
            p.x += p.vx + Math.sin(p.phase) * 0.2;
            p.y += p.vy;
            if (p.y < -10) p.y = h + 10;
            if (p.x < -10) p.x = w + 10;
            if (p.x > w + 10) p.x = -10;
            ctx2d.fillStyle = 'rgba(255, 255, 255, ' + p.alpha + ')';
            ctx2d.beginPath();
            ctx2d.arc(p.x, p.y, p.r, 0, Math.PI * 2);
            ctx2d.fill();
          }
        }
      }
      rafId = global.requestAnimationFrame(tick);
    }

    rafId = global.requestAnimationFrame(tick);

    function stop() {
      if (stopped) return;
      stopped = true;
      if (rafId) {
        global.cancelAnimationFrame(rafId);
        rafId = null;
      }
      if (canvas.parentNode) canvas.parentNode.removeChild(canvas);
      if (prevPos !== null) {
        host.style.position = prevPos;
      }
    }

    registerSlideCleanup(slideEl, stop);
    return { stop: stop };
  }

  function fxCountUp(el, to, opts) {
    if (!el) return { stop: function () {} };
    var prevCancel = countUpCancelMap.get(el);
    if (typeof prevCancel === 'function') prevCancel();

    var o = opts || {};
    var fromVal = Number.isFinite(Number(o.from)) ? Number(o.from) : 0;
    var toVal = Number.isFinite(Number(to)) ? Number(to) : 0;
    var ms = Number(o.ms) >= 0 ? Number(o.ms) : 1200;
    var useTick = Boolean(o.tick);
    var fmt =
      typeof o.format === 'function'
        ? o.format
        : function (n) {
            return Math.round(n).toLocaleString('en-US');
          };

    var slideEl = el.closest ? el.closest('.slide') : null;
    var rafId = null;
    var stopped = false;
    var startTime = null;
    var lastText = '';
    var lastTickAt = 0;

    function cancel() {
      if (stopped) return;
      stopped = true;
      if (rafId) {
        global.cancelAnimationFrame(rafId);
        rafId = null;
      }
    }

    countUpCancelMap.set(el, cancel);
    registerSlideCleanup(slideEl, cancel);

    if (ms === 0) {
      el.textContent = fmt(toVal);
      return { stop: cancel };
    }

    function step(ts) {
      if (stopped) return;
      if (startTime === null) startTime = ts;
      var p = Math.min(1, (ts - startTime) / ms);
      var eased = 1 - Math.pow(1 - p, 3);
      var val = fromVal + (toVal - fromVal) * eased;
      var text = p >= 1 ? fmt(toVal) : fmt(val);

      if (text !== lastText) {
        el.textContent = text;
        lastText = text;
        if (useTick && p < 1 && ts - lastTickAt >= 62) {
          lastTickAt = ts;
          playSfx('tick');
        }
      }

      if (p < 1) {
        rafId = global.requestAnimationFrame(step);
      } else {
        stopped = true;
      }
    }

    el.textContent = fmt(fromVal);
    rafId = global.requestAnimationFrame(step);
    return { stop: cancel };
  }

  function ensureSplitChars(el) {
    if (!el) return [];
    if (el.dataset.fxSplit === '1') {
      return Array.prototype.slice.call(el.querySelectorAll('.fx-char'));
    }

    function splitNode(node) {
      var children = Array.prototype.slice.call(node.childNodes);
      for (var i = 0; i < children.length; i++) {
        var child = children[i];
        if (child.nodeType === 3) {
          var raw = child.nodeValue || '';
          if (!raw) continue;
          if (/^\s*\n\s*$/.test(raw)) continue;
          var normalized = raw.replace(/\s*\n\s*/g, '');
          var chars = Array.from(normalized);
          var frag = document.createDocumentFragment();
          for (var c = 0; c < chars.length; c++) {
            var ch = chars[c];
            var sp = document.createElement('span');
            if (ch === ' ' || ch === '\u00A0') {
              sp.className = 'fx-char fx-space';
              sp.textContent = ' ';
            } else {
              sp.className = 'fx-char';
              sp.textContent = ch;
            }
            frag.appendChild(sp);
          }
          node.replaceChild(frag, child);
        } else if (child.nodeType === 1) {
          var tag = child.tagName;
          if (tag === 'BR' || tag === 'SCRIPT' || tag === 'STYLE' || tag === 'SVG') {
            continue;
          }
          if (child.classList && child.classList.contains('fx-char')) continue;
          splitNode(child);
        }
      }
    }

    splitNode(el);
    el.dataset.fxSplit = '1';
    return Array.prototype.slice.call(el.querySelectorAll('.fx-char'));
  }

  function clearCharTimers(el) {
    var list = charTimersMap.get(el);
    if (list && list.length) {
      for (var i = 0; i < list.length; i++) {
        clearTimeout(list[i]);
      }
      list.length = 0;
    }
  }

  function fxSlamChars(el, opts) {
    if (!el) return;
    clearCharTimers(el);
    var o = opts || {};
    var sfxName = o.sfx === undefined ? 'hit' : o.sfx;
    var gap = Number(o.gap) >= 0 ? Number(o.gap) : 90;

    var chars = ensureSplitChars(el);
    var solidChars = [];
    for (var i = 0; i < chars.length; i++) {
      var ch = chars[i];
      ch.style.transition = '';
      ch.style.transform = '';
      ch.style.opacity = '';
      ch.classList.remove('is-in', 'is-slam-prep');
      if (ch.classList.contains('fx-space')) {
        ch.classList.add('is-in');
      } else {
        ch.classList.add('is-slam-prep');
        solidChars.push(ch);
      }
    }

    void el.offsetWidth;

    var timers = [];
    charTimersMap.set(el, timers);
    var slideEl = el.closest ? el.closest('.slide') : null;

    for (var j = 0; j < solidChars.length; j++) {
      (function (span, idx) {
        var tid = setTimeout(function () {
          span.classList.remove('is-slam-prep');
          span.classList.add('is-in');
          if (sfxName) playSfx(sfxName);
        }, idx * gap);
        timers.push(tid);
      })(solidChars[j], j);
    }

    registerSlideCleanup(slideEl, function () {
      clearCharTimers(el);
    });
  }

  function fxRewindChars(el) {
    if (!el) return;
    clearCharTimers(el);
    var chars = ensureSplitChars(el);
    var slideEl = el.closest ? el.closest('.slide') : null;

    playSfx('rewind');

    for (var i = 0; i < chars.length; i++) {
      var ch = chars[i];
      ch.classList.remove('is-slam-prep', 'is-in');
      if (ch.classList.contains('fx-space')) continue;
      var rx = Math.round((Math.random() - 0.5) * 240);
      var ry = Math.round((Math.random() - 0.5) * 160);
      var rr = Math.round((Math.random() - 0.5) * 60);
      ch.style.transition = 'none';
      ch.style.opacity = '0.16';
      ch.style.transform =
        'translate3d(' + rx + 'px, ' + ry + 'px, 0) rotate(' + rr + 'deg) scale(1.22)';
    }

    void el.offsetWidth;

    var timers = [];
    charTimersMap.set(el, timers);
    var tid = setTimeout(function () {
      for (var k = 0; k < chars.length; k++) {
        var c = chars[k];
        if (c.classList.contains('fx-space')) continue;
        var delay = Math.min(220, k * 14);
        c.style.transition =
          'transform 0.56s cubic-bezier(0.16, 1, 0.3, 1) ' +
          delay +
          'ms, opacity 0.42s ease ' +
          delay +
          'ms';
        c.style.opacity = '1';
        c.style.transform = 'translate3d(0, 0, 0) rotate(0deg) scale(1)';
      }
    }, 32);
    timers.push(tid);

    registerSlideCleanup(slideEl, function () {
      clearCharTimers(el);
    });
  }

  function fxWriteOn(el, opts) {
    if (!el) return;
    var prevCancel = writeOnCancelMap.get(el);
    if (typeof prevCancel === 'function') prevCancel();

    var o = opts || {};
    var ms = Number(o.ms) >= 0 ? Number(o.ms) : 1800;
    var slideEl = el.closest ? el.closest('.slide') : null;
    var raf1 = null;
    var raf2 = null;
    var cancelled = false;

    function cancel() {
      cancelled = true;
      if (raf1) global.cancelAnimationFrame(raf1);
      if (raf2) global.cancelAnimationFrame(raf2);
    }

    writeOnCancelMap.set(el, cancel);
    registerSlideCleanup(slideEl, cancel);

    el.style.transition = 'none';
    el.style.clipPath = 'inset(0 100% 0 0)';
    void el.offsetWidth;

    raf1 = global.requestAnimationFrame(function () {
      if (cancelled) return;
      raf2 = global.requestAnimationFrame(function () {
        if (cancelled) return;
        el.style.transition =
          'clip-path ' + ms + 'ms cubic-bezier(0.22, 1, 0.36, 1)';
        el.style.clipPath = 'inset(0 0 0 0)';
        if (o.sfx) playSfx(o.sfx);
      });
    });
  }

  function fxLightning(container, opts) {
    var noop = { stop: function () {} };
    if (!container) return noop;
    var o = opts || {};
    var count = Number(o.count) > 0 ? Math.min(Number(o.count), 20) : 5;
    var slideEl =
      (container.closest && container.closest('.slide')) ||
      (currentIndex >= 0 ? slides[currentIndex] : null);

    var prevPos = null;
    try {
      if (global.getComputedStyle(container).position === 'static') {
        prevPos = container.style.position;
        container.style.position = 'relative';
      }
    } catch (_) {}

    var w = container.clientWidth || container.offsetWidth || STAGE_W;
    var h = container.clientHeight || container.offsetHeight || STAGE_H;

    var ns = 'http://www.w3.org/2000/svg';
    var svg = document.createElementNS(ns, 'svg');
    svg.setAttribute('class', 'fx-lightning-svg');
    svg.setAttribute('viewBox', '0 0 ' + w + ' ' + h);

    function buildBoltPoints(x1, y1, x2, y2, disp, depth) {
      if (depth <= 0) return [[x1, y1], [x2, y2]];
      var mx = (x1 + x2) / 2 + (Math.random() - 0.5) * disp;
      var my = (y1 + y2) / 2 + (Math.random() - 0.5) * disp;
      var left = buildBoltPoints(x1, y1, mx, my, disp * 0.55, depth - 1);
      var right = buildBoltPoints(mx, my, x2, y2, disp * 0.55, depth - 1);
      return left.slice(0, -1).concat(right);
    }

    function ptsToPath(pts) {
      var d = 'M ' + pts[0][0].toFixed(1) + ' ' + pts[0][1].toFixed(1);
      for (var i = 1; i < pts.length; i++) {
        d += ' L ' + pts[i][0].toFixed(1) + ' ' + pts[i][1].toFixed(1);
      }
      return d;
    }

    for (var i = 0; i < count; i++) {
      var mode = i % 3;
      var x1, y1, x2, y2;
      if (mode === 0) {
        x1 = w * (0.04 + Math.random() * 0.14);
        y1 = h * (0.14 + Math.random() * 0.72);
        x2 = w * (0.82 + Math.random() * 0.14);
        y2 = h * (0.14 + Math.random() * 0.72);
      } else if (mode === 1) {
        x1 = w * (0.14 + Math.random() * 0.72);
        y1 = h * (0.04 + Math.random() * 0.14);
        x2 = w * (0.14 + Math.random() * 0.72);
        y2 = h * (0.82 + Math.random() * 0.14);
      } else {
        x1 = w * (0.08 + Math.random() * 0.25);
        y1 = h * (0.08 + Math.random() * 0.25);
        x2 = w * (0.68 + Math.random() * 0.24);
        y2 = h * (0.68 + Math.random() * 0.24);
      }

      var pts = buildBoltPoints(x1, y1, x2, y2, Math.min(w, h) * 0.22, 4);
      var paths = [{ pts: pts, width: 2.2, glow: 7 }];
      if (pts.length > 4) {
        var forkIdx = 2 + Math.floor(Math.random() * (pts.length - 4));
        var fp = pts[forkIdx];
        var fx2 = fp[0] + (Math.random() - 0.5) * w * 0.28;
        var fy2 = fp[1] + (Math.random() - 0.5) * h * 0.36;
        paths.push({
          pts: buildBoltPoints(fp[0], fp[1], fx2, fy2, Math.min(w, h) * 0.1, 3),
          width: 1.3,
          glow: 4.5
        });
      }

      for (var pi = 0; pi < paths.length; pi++) {
        var pItem = paths[pi];
        var dStr = ptsToPath(pItem.pts);

        var glow = document.createElementNS(ns, 'path');
        glow.setAttribute('class', 'fx-lightning-bolt');
        glow.setAttribute('d', dStr);
        glow.setAttribute('stroke', o.glowColor || 'rgba(255, 110, 30, 0.52)');
        glow.setAttribute('stroke-width', String(pItem.glow));

        var core = document.createElementNS(ns, 'path');
        core.setAttribute('class', 'fx-lightning-bolt');
        core.setAttribute('d', dStr);
        core.setAttribute('stroke', o.color || '#FFF0D4');
        core.setAttribute('stroke-width', String(pItem.width));

        var firstPt = pItem.pts[0];
        var lastPt = pItem.pts[pItem.pts.length - 1];
        var approxLen = Math.hypot(lastPt[0] - firstPt[0], lastPt[1] - firstPt[1]) * 1.5;
        glow.style.strokeDasharray = String(approxLen);
        glow.style.strokeDashoffset = String(approxLen);
        core.style.strokeDasharray = String(approxLen);
        core.style.strokeDashoffset = String(approxLen);

        var delay = i * 55 + pi * 70;
        glow.style.transition =
          'stroke-dashoffset 0.28s cubic-bezier(0.22, 1, 0.36, 1) ' + delay + 'ms';
        core.style.transition =
          'stroke-dashoffset 0.28s cubic-bezier(0.22, 1, 0.36, 1) ' + delay + 'ms';
        glow.style.animation =
          'deckBoltBreath ' + (1.2 + Math.random() * 0.8).toFixed(2) + 's ease-in-out ' + delay + 'ms infinite';
        core.style.animation =
          'deckBoltBreath ' + (1.2 + Math.random() * 0.8).toFixed(2) + 's ease-in-out ' + delay + 'ms infinite';

        svg.appendChild(glow);
        svg.appendChild(core);

        (function (gEl, cEl) {
          global.requestAnimationFrame(function () {
            gEl.style.strokeDashoffset = '0';
            cEl.style.strokeDashoffset = '0';
          });
        })(glow, core);
      }
    }

    container.appendChild(svg);

    var stopped = false;
    function stop() {
      if (stopped) return;
      stopped = true;
      if (svg.parentNode) svg.parentNode.removeChild(svg);
      if (prevPos !== null) {
        container.style.position = prevPos;
      }
    }

    registerSlideCleanup(slideEl, stop);
    return { stop: stop };
  }

  /* ---------- 页内视频与全屏视频弹窗 ---------- */
  function prepInlineVideoAttributes(v) {
    v.setAttribute('playsinline', '');
    v.setAttribute('webkit-playsinline', 'true');
    v.setAttribute('x5-playsinline', 'true');
    v.playsInline = true;
    v.loop = true;
  }

  function startInlineEntry(entry) {
    if (!entry || !entry.videoEl) return;
    if (entry.slideEl && !entry.slideEl.classList.contains('active')) return;
    var v = entry.videoEl;
    var canPlayWithSound = Boolean(Deck.audioReady && !Deck.isMuted());

    v.muted = !canPlayWithSound;
    entry.unmutedIntent = canPlayWithSound;
    if (canPlayWithSound) v.volume = 1;

    var attempt = function () {
      var p = v.play();
      if (p && typeof p.catch === 'function') {
        p.catch(function () {
          v.muted = true;
          entry.unmutedIntent = false;
          if (entry.soundBtn) entry.soundBtn.classList.remove('on');
          syncAutoDuck();
          var pMuted = v.play();
          if (pMuted && typeof pMuted.catch === 'function') {
            pMuted.catch(function () {
              invokeWeixin(function () {
                v.muted = true;
                entry.unmutedIntent = false;
                v.play().catch(function () {});
              });
            });
          }
        });
      }
      if (entry.soundBtn) {
        entry.soundBtn.classList.toggle('on', !v.muted);
      }
      syncAutoDuck();
    };

    attempt();
  }

  function startInlineVideosForSlide(slideEl) {
    if (!slideEl) return;
    for (var i = 0; i < inlineEntries.length; i++) {
      if (inlineEntries[i].slideEl === slideEl) {
        startInlineEntry(inlineEntries[i]);
      }
    }
  }

  function cleanupSlideVideos(slideEl) {
    if (!slideEl) return;
    var videos = slideEl.querySelectorAll('video');
    for (var i = 0; i < videos.length; i++) {
      try {
        videos[i].pause();
        videos[i].muted = true;
      } catch (_) {}
    }
    for (var j = 0; j < inlineEntries.length; j++) {
      if (inlineEntries[j].slideEl === slideEl) {
        inlineEntries[j].unmutedIntent = false;
        if (inlineEntries[j].soundBtn) {
          inlineEntries[j].soundBtn.classList.remove('on');
        }
      }
    }
    syncAutoDuck();
  }

  function registerInlineVideo(videoEl, soundBtn) {
    if (!videoEl) return null;
    prepInlineVideoAttributes(videoEl);

    var entry = null;
    for (var i = 0; i < inlineEntries.length; i++) {
      if (inlineEntries[i].videoEl === videoEl) {
        entry = inlineEntries[i];
        break;
      }
    }
    if (!entry) {
      entry = {
        videoEl: videoEl,
        soundBtn: soundBtn || null,
        slideEl: videoEl.closest('.slide'),
        unmutedIntent: false
      };
      inlineEntries.push(entry);

      videoEl.addEventListener('play', function () {
        if (!videoEl.muted) entry.unmutedIntent = true;
        syncAutoDuck();
      });
      videoEl.addEventListener('pause', function () {
        entry.unmutedIntent = false;
        syncAutoDuck();
      });
      videoEl.addEventListener('ended', function () {
        entry.unmutedIntent = false;
        syncAutoDuck();
      });
      videoEl.addEventListener('volumechange', function () {
        if (videoEl.muted) {
          entry.unmutedIntent = false;
        } else if (!videoEl.paused) {
          entry.unmutedIntent = true;
        }
        if (entry.soundBtn) {
          entry.soundBtn.classList.toggle('on', !videoEl.muted);
        }
        syncAutoDuck();
      });
    } else if (soundBtn) {
      entry.soundBtn = soundBtn;
    }

    if (soundBtn && !soundBtn.dataset.deckVideoBound) {
      soundBtn.dataset.deckVideoBound = '1';
      soundBtn.addEventListener('click', function (e) {
        e.stopPropagation();
        var nextMuted = !videoEl.muted;
        videoEl.muted = nextMuted;
        entry.unmutedIntent = !nextMuted;
        if (!nextMuted) {
          videoEl.volume = 1;
          if (!Deck.audioReady) unlockAudio(e);
          if (userMuted) {
            userMuted = false;
            syncMuteUI();
          }
        }
        soundBtn.classList.toggle('on', !videoEl.muted);
        syncAutoDuck();
        var playPromise = videoEl.play();
        if (playPromise && typeof playPromise.catch === 'function') {
          playPromise.catch(function () {
            entry.unmutedIntent = false;
            syncAutoDuck();
            invokeWeixin(function () {
              videoEl.play().catch(function () {});
            });
          });
        }
      });
    }

    if (!entry.slideEl || entry.slideEl.classList.contains('active')) {
      startInlineEntry(entry);
    }

    return {
      el: videoEl,
      play: function () {
        startInlineEntry(entry);
      },
      pause: function () {
        entry.unmutedIntent = false;
        videoEl.pause();
        syncAutoDuck();
      },
      setMuted: function (m) {
        videoEl.muted = Boolean(m);
        entry.unmutedIntent = !videoEl.muted && !videoEl.paused;
        if (entry.soundBtn) {
          entry.soundBtn.classList.toggle('on', !videoEl.muted);
        }
        syncAutoDuck();
      }
    };
  }

  function openModal(src, title) {
    if (!modalEl || !modalVideoEl) return;
    if (currentIndex >= 0 && slides[currentIndex]) {
      var vids = slides[currentIndex].querySelectorAll('video');
      for (var i = 0; i < vids.length; i++) {
        try {
          vids[i].pause();
        } catch (_) {}
      }
    }
    modalTitleEl.textContent = title || '';
    modalVideoEl.src = src || '';
    modalVideoEl.muted = Deck.isMuted();
    modalVideoEl.volume = 1;
    modalOpen = true;
    modalEl.classList.add('open');
    modalEl.setAttribute('aria-hidden', 'false');
    syncAutoDuck();

    var p = modalVideoEl.play();
    if (p && typeof p.catch === 'function') {
      p.catch(function () {
        modalVideoEl.muted = true;
        modalVideoEl.play().catch(function () {
          invokeWeixin(function () {
            modalVideoEl.play().catch(function () {});
          });
        });
      });
    }
  }

  function closeModal() {
    if (!modalEl || !modalOpen) return;
    modalOpen = false;
    modalEl.classList.remove('open');
    modalEl.setAttribute('aria-hidden', 'true');
    if (modalVideoEl) {
      try {
        modalVideoEl.pause();
        modalVideoEl.removeAttribute('src');
        modalVideoEl.load();
      } catch (_) {}
    }
    syncAutoDuck();
  }

  /* ---------- UI 构造 ---------- */
  function buildViewportChrome() {
    if (!railEl) {
      railEl = document.createElement('nav');
      railEl.id = 'deckRail';
      railEl.className = 'no-nav';
      railEl.setAttribute('data-nav-stop', 'true');
      railEl.setAttribute('aria-label', '幻灯片进度');
      railDots = slides.map(function (slide, idx) {
        var dot = document.createElement('button');
        dot.type = 'button';
        dot.className = 'deck-dot';
        dot.setAttribute('data-index', String(idx));
        var ch = slide.getAttribute('data-ch');
        var label = '第 ' + (idx + 1) + ' 页' + (ch ? ' · ' + ch : '');
        dot.setAttribute('aria-label', label);
        dot.title = label;
        dot.addEventListener('click', function (e) {
          e.stopPropagation();
          Deck.goTo(idx);
        });
        railEl.appendChild(dot);
        return dot;
      });
      viewportEl.appendChild(railEl);
    }

    if (!controlsEl) {
      controlsEl = document.createElement('div');
      controlsEl.id = 'deckControls';
      controlsEl.className = 'no-nav';
      controlsEl.setAttribute('data-nav-stop', 'true');

      muteBtnEl = document.createElement('button');
      muteBtnEl.type = 'button';
      muteBtnEl.id = 'deckMuteBtn';
      muteBtnEl.className = 'deck-ctrl-btn';
      muteBtnEl.textContent = '🔇 开启声音';
      muteBtnEl.setAttribute('aria-pressed', 'false');
      muteBtnEl.addEventListener('click', handleMuteButtonClick);

      fsBtnEl = document.createElement('button');
      fsBtnEl.type = 'button';
      fsBtnEl.id = 'deckFsBtn';
      fsBtnEl.className = 'deck-ctrl-btn';
      fsBtnEl.textContent = '全屏';
      if (!isFullscreenSupported()) {
        fsBtnEl.classList.add('is-hidden');
      }
      fsBtnEl.addEventListener('click', function (e) {
        e.stopPropagation();
        toggleFullscreen();
      });

      controlsEl.appendChild(muteBtnEl);
      controlsEl.appendChild(fsBtnEl);
      viewportEl.appendChild(controlsEl);
    }

    if (!toastEl) {
      toastEl = document.createElement('div');
      toastEl.id = 'deckToast';
      viewportEl.appendChild(toastEl);
    }

    if (!modalEl) {
      modalEl = document.createElement('div');
      modalEl.id = 'deckModal';
      modalEl.className = 'no-nav';
      modalEl.setAttribute('data-nav-stop', 'true');
      modalEl.setAttribute('aria-hidden', 'true');

      var backdrop = document.createElement('div');
      backdrop.className = 'deck-modal-backdrop';
      backdrop.addEventListener('click', closeModal);

      var shell = document.createElement('div');
      shell.className = 'deck-modal-shell';

      var head = document.createElement('div');
      head.className = 'deck-modal-head';

      modalTitleEl = document.createElement('div');
      modalTitleEl.className = 'deck-modal-title';

      var closeBtn = document.createElement('button');
      closeBtn.type = 'button';
      closeBtn.className = 'deck-modal-close';
      closeBtn.setAttribute('aria-label', '关闭视频');
      closeBtn.textContent = '✕';
      closeBtn.addEventListener('click', function (e) {
        e.stopPropagation();
        closeModal();
      });

      head.appendChild(modalTitleEl);
      head.appendChild(closeBtn);

      var box = document.createElement('div');
      box.className = 'deck-modal-box';

      modalVideoEl = document.createElement('video');
      modalVideoEl.controls = true;
      modalVideoEl.setAttribute('playsinline', '');
      modalVideoEl.setAttribute('webkit-playsinline', 'true');
      modalVideoEl.setAttribute('x5-playsinline', 'true');
      modalVideoEl.preload = 'metadata';

      box.appendChild(modalVideoEl);
      shell.appendChild(head);
      shell.appendChild(box);
      modalEl.appendChild(backdrop);
      modalEl.appendChild(shell);
      viewportEl.appendChild(modalEl);
    }
  }

  function buildStartGate(onEnterCallback) {
    if (gateEl) return gateEl;
    gateEl = document.createElement('div');
    gateEl.id = 'startGate';
    gateEl.className = 'no-nav';
    gateEl.setAttribute('data-nav-stop', 'true');
    gateEl.setAttribute('role', 'dialog');
    gateEl.setAttribute('aria-label', '开场门');

    var eyebrow = document.createElement('div');
    eyebrow.className = 'gate-eyebrow';
    eyebrow.textContent = 'SHANGHAI ZHENYUFENG POWER';

    var title = document.createElement('div');
    title.className = 'gate-title';
    title.textContent = '桢昱烽动力';

    var btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'gate-btn';
    btn.textContent = '点击开始 · 建议开启声音';

    gateEl.appendChild(eyebrow);
    gateEl.appendChild(title);
    gateEl.appendChild(btn);

    function dismiss(e) {
      if (e && e.stopPropagation) e.stopPropagation();
      if (!gateActive) return;
      gateActive = false;

      unlockAudio(e);
      if (userMuted) {
        userMuted = false;
        syncMuteUI();
      }

      gateEl.classList.add('is-leaving');
      if (gateHideTimer) clearTimeout(gateHideTimer);
      gateHideTimer = setTimeout(function () {
        if (gateEl) gateEl.classList.add('is-gone');
      }, 420);

      if (typeof onEnterCallback === 'function') {
        onEnterCallback();
      }
    }

    gateEl.addEventListener('click', dismiss);
    viewportEl.appendChild(gateEl);
    gateActive = true;
    return gateEl;
  }

  function syncThemeAndRail(idx) {
    var slide = slides[idx];
    var theme = getSlideTheme(slide);
    if (railEl) railEl.setAttribute('data-theme', theme);
    if (controlsEl) controlsEl.setAttribute('data-theme', theme);
    for (var i = 0; i < railDots.length; i++) {
      railDots[i].classList.toggle('active', i === idx);
    }
  }

  /* ---------- Hash 解析与同步 ---------- */
  function parseHashIndex() {
    var raw = (global.location.hash || '').replace(/^#/, '').trim();
    if (!raw || slides.length === 0) return 0;
    if (/^\d+$/.test(raw)) {
      var n = parseInt(raw, 10) - 1;
      return n >= 0 && n < slides.length ? n : 0;
    }
    var lower = raw.toLowerCase();
    for (var i = 0; i < slides.length; i++) {
      if (slides[i].id && slides[i].id.toLowerCase() === lower) {
        return i;
      }
    }
    return 0;
  }

  function syncHash(idx) {
    var target = '#' + (idx + 1);
    if (global.location.hash === target) return;
    try {
      global.history.replaceState(null, '', target);
    } catch (_) {
      global.location.hash = target;
    }
  }

  /* ---------- 节拍推进与翻页核心 ---------- */
  function advance() {
    if (gateActive || modalOpen || currentIndex < 0) return;
    var activeEl = slides[currentIndex];
    var hook = activeEl && activeEl.id ? hooks[activeEl.id] : null;
    var beats = hook && Array.isArray(hook.beats) ? hook.beats : null;

    if (beats && beatIndex < beats.length) {
      var fn = beats[beatIndex];
      beatIndex++;
      if (typeof fn === 'function') {
        try {
          fn(activeEl);
        } catch (err) {
          console.error('[Deck.beat]', activeEl.id, beatIndex - 1, err);
        }
      }
      return;
    }

    goTo(currentIndex + 1);
  }

  function activateInitialSlide(initIdx, fromGate) {
    var firstEl = slides[initIdx];
    currentIndex = initIdx;
    beatIndex = 0;

    firstEl.classList.add('active', 'deck-pre');
    void firstEl.offsetWidth;
    global.requestAnimationFrame(function () {
      global.requestAnimationFrame(function () {
        firstEl.classList.remove('deck-pre');
      });
    });

    syncThemeAndRail(initIdx);
    syncHash(initIdx);

    var initCue = getEffectiveCueAt(initIdx);
    if (fromGate) {
      scoreCue(initCue || 'tension');
    } else if (initCue) {
      scoreCue(initCue);
    }

    startInlineVideosForSlide(firstEl);

    var firstHook = firstEl.id ? hooks[firstEl.id] : null;
    if (firstHook && typeof firstHook.enter === 'function') {
      try {
        firstHook.enter(firstEl);
      } catch (err) {
        console.error('[Deck.enter]', firstEl.id, err);
      }
    }
    syncAutoDuck();
  }

  function goTo(index) {
    var targetIdx = Number(index);
    if (
      !Number.isInteger(targetIdx) ||
      targetIdx < 0 ||
      targetIdx >= slides.length
    ) {
      return;
    }
    if (targetIdx === currentIndex) return;

    closeModal();

    var oldEl = currentIndex >= 0 ? slides[currentIndex] : null;
    var newEl = slides[targetIdx];

    if (oldEl) {
      var oldHook = oldEl.id ? hooks[oldEl.id] : null;
      if (oldHook && typeof oldHook.leave === 'function') {
        try {
          oldHook.leave(oldEl);
        } catch (err) {
          console.error('[Deck.leave]', oldEl.id, err);
        }
      }
      stopAllLoops();
      stopAmbient();
      cleanupSlideVideos(oldEl);
      cleanupSlideFx(oldEl);
      oldEl.classList.remove('active', 'deck-pre');
    }

    currentIndex = targetIdx;
    beatIndex = 0;

    void newEl.offsetWidth;
    newEl.classList.add('active');

    syncThemeAndRail(currentIndex);
    syncHash(currentIndex);

    if (oldEl) {
      playSfx('whoosh');
      spawnStreak();
      var chapter = newEl.getAttribute('data-chapter');
      if (chapter && chapter.trim()) {
        fxFlash('#ffffff');
        playSfx('impact');
        spawnChapterTransition(chapter.trim());
      }
    }

    var slideCue = newEl.getAttribute('data-cue');
    if (slideCue && slideCue.trim()) {
      scoreCue(slideCue.trim());
    }

    startInlineVideosForSlide(newEl);

    var newHook = newEl.id ? hooks[newEl.id] : null;
    if (newHook && typeof newHook.enter === 'function') {
      try {
        newHook.enter(newEl);
      } catch (err2) {
        console.error('[Deck.enter]', newEl.id, err2);
      }
    }
    syncAutoDuck();
  }

  /* ---------- 事件绑定 ---------- */
  function bindEvents() {
    global.addEventListener('load', updateScale);
    global.addEventListener('resize', updateScale);
    global.addEventListener('orientationchange', updateScale);
    if (global.visualViewport) {
      global.visualViewport.addEventListener('resize', updateScale);
    }

    document.addEventListener('fullscreenchange', syncFsUI);
    document.addEventListener('webkitfullscreenchange', syncFsUI);

    global.addEventListener('hashchange', function () {
      if (gateActive) return;
      var idx = parseHashIndex();
      if (idx !== currentIndex) goTo(idx);
    });

    // 全局首次手势同步解锁音频（capture 阶段确保先于按钮逻辑执行）
    var unlockEvents = ['pointerdown', 'touchend', 'click', 'keydown'];
    for (var i = 0; i < unlockEvents.length; i++) {
      document.addEventListener(unlockEvents[i], unlockAudio, {
        capture: true,
        passive: true
      });
    }

    // 捕获 click 前状态，防止页面自定义 click（如 P25 回首页）与舞台点击推进冲突
    document.addEventListener(
      'click',
      function () {
        clickSnapshot.idx = currentIndex;
        clickSnapshot.beat = beatIndex;
      },
      true
    );

    if (viewportEl) {
      viewportEl.addEventListener('click', function (e) {
        if (gateActive || modalOpen) return;
        if (e.defaultPrevented) return;
        if (e.button !== undefined && e.button !== 0) return;
        if (Date.now() - lastSwipeAt < 450) return;
        if (currentIndex !== clickSnapshot.idx || beatIndex !== clickSnapshot.beat) {
          return;
        }
        if (isNavBlocked(e.target)) return;
        advance();
      });
    }

    document.addEventListener(
      'WeixinJSBridgeReady',
      function () {
        invokeWeixin(function () {
          unlockAudio();
          if (!gateActive && currentIndex >= 0 && slides[currentIndex]) {
            startInlineVideosForSlide(slides[currentIndex]);
          }
        });
      },
      false
    );

    // 键盘导航
    document.addEventListener('keydown', function (e) {
      if (gateActive) {
        if ((e.key === 'Enter' || e.key === ' ' || e.key === 'Spacebar') && gateEl) {
          e.preventDefault();
          gateEl.click();
        }
        return;
      }

      if (modalOpen) {
        if (e.key === 'Escape') {
          e.preventDefault();
          closeModal();
        }
        return;
      }

      if (isTypingTarget(e.target)) return;

      var key = e.key;
      if (
        key === 'ArrowRight' ||
        key === 'ArrowDown' ||
        key === ' ' ||
        key === 'Spacebar' ||
        key === 'PageDown'
      ) {
        e.preventDefault();
        advance();
      } else if (
        key === 'ArrowLeft' ||
        key === 'ArrowUp' ||
        key === 'PageUp'
      ) {
        e.preventDefault();
        goTo(currentIndex - 1);
      } else if (key === 'Home') {
        e.preventDefault();
        goTo(0);
      } else if (key === 'End') {
        e.preventDefault();
        goTo(slides.length - 1);
      } else if (
        (key === 'f' || key === 'F') &&
        !e.ctrlKey &&
        !e.metaKey &&
        !e.altKey
      ) {
        e.preventDefault();
        toggleFullscreen();
      }
    });

    // 滚轮翻页（700ms 防抖锁，|deltaY| >= 25）
    document.addEventListener(
      'wheel',
      function (e) {
        if (gateActive || modalOpen) return;
        if (Math.abs(e.deltaY) < WHEEL_THRESHOLD) return;
        var now = Date.now();
        if (now - lastWheelAt < WHEEL_LOCK_MS) return;
        lastWheelAt = now;
        if (e.deltaY > 0) {
          advance();
        } else {
          goTo(currentIndex - 1);
        }
      },
      { passive: true }
    );

    // 触摸滑动翻页（水平或垂直 > 50px）
    document.addEventListener(
      'touchstart',
      function (e) {
        if (gateActive || modalOpen || !e.touches || e.touches.length !== 1) {
          touchStart = null;
          return;
        }
        if (isNavBlocked(e.target)) {
          touchStart = null;
          return;
        }
        touchStart = {
          x: e.touches[0].clientX,
          y: e.touches[0].clientY
        };
      },
      { passive: true }
    );

    document.addEventListener(
      'touchend',
      function (e) {
        if (
          gateActive ||
          !touchStart ||
          modalOpen ||
          !e.changedTouches ||
          !e.changedTouches.length
        ) {
          touchStart = null;
          return;
        }
        var t = e.changedTouches[0];
        var dx = t.clientX - touchStart.x;
        var dy = t.clientY - touchStart.y;
        touchStart = null;

        if (Math.abs(dx) <= SWIPE_THRESHOLD && Math.abs(dy) <= SWIPE_THRESHOLD) {
          return;
        }
        lastSwipeAt = Date.now();
        if (Math.abs(dx) >= Math.abs(dy)) {
          if (dx < 0) {
            advance();
          } else {
            goTo(currentIndex - 1);
          }
        } else {
          if (dy < 0) {
            advance();
          } else {
            goTo(currentIndex - 1);
          }
        }
      },
      { passive: true }
    );
  }

  /* ---------- 启动入口 ---------- */
  function start() {
    viewportEl = document.getElementById('viewport');
    stageEl = document.getElementById('stage');
    if (!viewportEl || !stageEl) return;

    slides = Array.prototype.slice.call(stageEl.querySelectorAll('.slide'));
    if (slides.length === 0) return;

    loadScoreManifest();

    if (!started) {
      started = true;
      buildViewportChrome();
      bindEvents();
    }

    updateScale();
    syncFsUI();
    syncMuteUI();

    var initIdx = parseHashIndex();
    currentIndex = initIdx;
    beatIndex = 0;

    if (hasNoGateFlag()) {
      activateInitialSlide(initIdx, false);
      if (global.WeixinJSBridge) {
        invokeWeixin(function () {
          unlockAudio();
          startInlineVideosForSlide(slides[initIdx]);
        });
      }
      return;
    }

    // 默认显示开场门 #startGate，暂不触发首张 enter 与重演动效
    syncThemeAndRail(initIdx);
    syncHash(initIdx);

    buildStartGate(function () {
      activateInitialSlide(initIdx, true);
    });

    if (global.WeixinJSBridge) {
      invokeWeixin(function () {
        unlockAudio();
      });
    }
  }

  /* ---------- 对外公开 API ---------- */
  var scoreApi = {
    cue: scoreCue,
    duck: scoreDuck
  };

  Object.defineProperty(scoreApi, 'current', {
    enumerable: true,
    get: function () {
      return currentCueName;
    }
  });

  Object.defineProperty(scoreApi, 'ducked', {
    enumerable: true,
    get: function () {
      return isDucked;
    }
  });

  var Deck = {
    audioReady: false,

    register: function (id, slideHooks) {
      if (!id) return;
      hooks[id] = {
        enter:
          slideHooks && typeof slideHooks.enter === 'function'
            ? slideHooks.enter
            : null,
        leave:
          slideHooks && typeof slideHooks.leave === 'function'
            ? slideHooks.leave
            : null,
        beats:
          slideHooks && Array.isArray(slideHooks.beats)
            ? slideHooks.beats.slice()
            : []
      };
    },

    start: start,
    goTo: goTo,

    isMuted: function () {
      return userMuted;
    },

    sfx: playSfx,
    loop: createLoop,
    score: scoreApi,

    fx: {
      shake: fxShake,
      flash: fxFlash,
      sweep: fxSweep,
      sparks: fxSparks,
      particles: fxParticles,
      countUp: fxCountUp,
      slamChars: fxSlamChars,
      rewindChars: fxRewindChars,
      writeOn: fxWriteOn,
      lightning: fxLightning
    },

    ambient: {
      toggle: toggleAmbient
    },

    video: {
      inline: registerInlineVideo,
      modal: openModal
    }
  };

  Object.defineProperty(Deck, 'audioState', {
    enumerable: true,
    get: function () {
      return ctx ? ctx.state : 'uninitialized';
    }
  });

  Object.defineProperty(Deck, 'currentIndex', {
    enumerable: true,
    get: function () {
      return currentIndex;
    }
  });

  Object.defineProperty(Deck, 'beatIndex', {
    enumerable: true,
    get: function () {
      return beatIndex;
    }
  });

  global.Deck = Deck;
})(window);
