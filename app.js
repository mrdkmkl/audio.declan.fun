'use strict';

/* ════════════════════════════════════════════════════
   AUDIOPIX — app.js
   Protocol: SYNC → HEADER(res,nColors,ms) → PIXELS → END
   Receiver auto-configures from embedded header
   ════════════════════════════════════════════════════ */

// ─────────────────────────────────────────────────────
//  PROTOCOL CONSTANTS
// ─────────────────────────────────────────────────────
const P = {
  FREQ_LO:      600,   // Hz — lowest data frequency
  FREQ_HI:     4500,   // Hz — highest data frequency

  SYNC_FREQ:    185,   // Hz — sync carrier
  SYNC_DUR:     800,   // ms — sync tone duration

  HDR_START_F: 5750,   // Hz — header-begin marker
  HDR_END_F:   5650,   // Hz — header-end marker
  END_FREQ:    5500,   // Hz — end-of-transmission
  END_DUR:      500,   // ms

  HDR_SIG_DUR:  150,   // ms — marker tone length
  HDR_VAL_DUR:  600,   // ms — each header value tone
  GAP:           20,   // ms — silence between tones
  PX_GAP:         3,   // ms — inter-pixel silence
};

// Header timing offsets from when sync tone ENDS (ms)
const H = (() => {
  const g = P.GAP, sv = P.HDR_SIG_DUR, vv = P.HDR_VAL_DUR;
  const SIG1_S = g;
  const SIG1_E = g + sv;
  const RES_S  = SIG1_E + g;
  const RES_E  = RES_S  + vv;
  const COL_S  = RES_E  + g;
  const COL_E  = COL_S  + vv;
  const TM_S   = COL_E  + g;
  const TM_E   = TM_S   + vv;
  const SIG2_S = TM_E   + g;
  const SIG2_E = SIG2_S + sv;
  const DATA_S = SIG2_E + 30;  // 30ms extra gap before pixels
  return { SIG1_S, SIG1_E, RES_S, RES_E, COL_S, COL_E, TM_S, TM_E, SIG2_S, SIG2_E, DATA_S };
})();
// H.DATA_S ≈ 2230ms total header time after sync

// ─────────────────────────────────────────────────────
//  CONFIG (active) and PENDING (in popup, unapplied)
// ─────────────────────────────────────────────────────
const CFG = { resolution: 32, nColors: 124, timeMs: 50 };
const PND = { ...CFG }; // pending (popup)

// ─────────────────────────────────────────────────────
//  STATE
// ─────────────────────────────────────────────────────
let mode     = 'tx';
let palette  = [];
let txPixels = null;
let origImg  = null;
let isTx     = false;
let isRx     = false;
let txAC     = null;   // TX AudioContext

let rxAC     = null;   // RX AudioContext
let rxStream = null;
let rxAna    = null;   // AnalyserNode
let rxFD     = null;   // Uint8Array frequency data buffer
let rxFR     = 1;      // Hz per FFT bin
let rxTimer  = null;   // setInterval handle
let rxRAF    = null;   // requestAnimationFrame handle
let curTxFreq = 0;     // current TX frequency for spectrum animation

// RX state machine fields
let rxPhase   = 'IDLE';  // IDLE | SYNC | HDR | DATA | DONE
let rxSyncDet = 0;       // timestamp when sync first seen
let rxSyncEnd = 0;       // timestamp when sync ended
let rxSyncDB  = 0;       // debounce timestamp for sync-end
let rxHdrBuf  = null;    // { res:[], col:[], tm:[] }
let rxDetCFG  = null;    // { resolution, nColors, timeMs } decoded from header
let rxDataSt  = 0;       // timestamp when pixel data started
let rxLastPx  = -1;      // last decoded pixel index
let rxPixels  = [];
let rxPxCnt   = 0;

// ─────────────────────────────────────────────────────
//  COLOUR PALETTE
// ─────────────────────────────────────────────────────
function hsl2rgb(h, s, l) {
  s /= 100; l /= 100;
  const k = n => (n + h / 30) % 12;
  const a = s * Math.min(l, 1 - l);
  const f = n => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
  return [~~(f(0) * 255), ~~(f(8) * 255), ~~(f(4) * 255)];
}

function buildPalette(n) {
  palette = [];
  const chromatic = Math.max(0, n - 4);
  // Golden-angle hue distribution across 5 lightness tiers
  const tiers = [[92,20],[85,35],[78,50],[70,65],[62,79]];
  for (let i = 0; i < chromatic; i++) {
    const hue = (i * 137.508) % 360;
    const [s, l] = tiers[i % tiers.length];
    palette.push(hsl2rgb(hue, s, l));
  }
  // Neutral anchors
  palette.push([10,10,12], [80,80,88], [165,165,175], [242,242,248]);
  return palette;
}

function quantize(r, g, b) {
  let best = 0, bestD = Infinity;
  for (let i = 0; i < palette.length; i++) {
    const [pr, pg, pb] = palette[i];
    const d = 0.2126*(r-pr)**2 + 0.7152*(g-pg)**2 + 0.0722*(b-pb)**2;
    if (d < bestD) { bestD = d; best = i; }
  }
  return best;
}

// Frequency ↔ palette index
function idx2freq(i, n)  { return P.FREQ_LO + (i / (n - 1)) * (P.FREQ_HI - P.FREQ_LO); }
function freq2idx(f, n)  { return Math.max(0, Math.min(n-1, Math.round((f - P.FREQ_LO) / (P.FREQ_HI - P.FREQ_LO) * (n - 1)))); }

// Header value encoding: maps a value [lo..hi] → [FREQ_LO..FREQ_HI]
function val2freq(v, lo, hi) { return P.FREQ_LO + (v - lo) / (hi - lo) * (P.FREQ_HI - P.FREQ_LO); }
function freq2val(f, lo, hi) { return lo + (f - P.FREQ_LO) / (P.FREQ_HI - P.FREQ_LO) * (hi - lo); }

// ─────────────────────────────────────────────────────
//  ESTIMATE HELPERS
// ─────────────────────────────────────────────────────
function calcEst(res, nc, ms) {
  const pixels    = res * res;
  const headerMs  = P.SYNC_DUR + H.DATA_S;      // ≈ 3030ms
  const pixelMs   = pixels * (ms + P.PX_GAP);
  const endMs     = P.GAP + P.END_DUR;
  const totalMs   = headerMs + pixelMs + endMs;
  return { pixels, headerMs, pixelMs, totalMs };
}

function fmtTime(ms) {
  if (ms < 1000)        return `${ms.toFixed(0)}ms`;
  if (ms < 60000)       return `${(ms / 1000).toFixed(1)}s`;
  if (ms < 3600000) {
    const m = Math.floor(ms / 60000);
    const s = Math.floor((ms % 60000) / 1000);
    return s ? `${m}m ${s}s` : `${m}m`;
  }
  const h = Math.floor(ms / 3600000);
  const m = Math.floor((ms % 3600000) / 60000);
  return m ? `${h}h ${m}m` : `${h}h`;
}

// ─────────────────────────────────────────────────────
//  ANIMATED BACKGROUND
// ─────────────────────────────────────────────────────
const bgCV = document.getElementById('bgCanvas');
const bgCX = bgCV.getContext('2d');
let   bgT  = 0;

function resizeBg() {
  bgCV.width  = window.innerWidth;
  bgCV.height = window.innerHeight;
}
resizeBg();
window.addEventListener('resize', resizeBg);

(function animBg() {
  const W = bgCV.width, H = bgCV.height;
  bgCX.clearRect(0, 0, W, H);

  const isTxMode = mode === 'tx';
  const colFn    = isTxMode
    ? a => `rgba(255,117,53,${a})`
    : a => `rgba(0,212,200,${a})`;

  for (let w = 0; w < 8; w++) {
    const phase = bgT * 0.00038 + w * 0.85;
    const amp   = 18 + w * 15;
    const freq  = 0.0028 + w * 0.0017;
    const yBase = H * (0.08 + w * 0.12);
    const env   = Math.sin(bgT * 0.00022 + w * 0.44);

    bgCX.beginPath();
    bgCX.moveTo(0, yBase);
    for (let x = 0; x <= W; x += 3) {
      bgCX.lineTo(x, yBase + Math.sin(x * freq + phase) * amp * env);
    }
    bgCX.strokeStyle = colFn(0.018 + w * 0.01);
    bgCX.lineWidth   = 1;
    bgCX.stroke();
  }

  bgT++;
  requestAnimationFrame(animBg);
})();

// ─────────────────────────────────────────────────────
//  MODE SWITCHING
// ─────────────────────────────────────────────────────
function setMode(m) {
  mode = m;
  const tx = m === 'tx';
  document.getElementById('btnTx').className    = 'mode-btn' + (tx  ? ' active-tx' : '');
  document.getElementById('btnRx').className    = 'mode-btn' + (!tx ? ' active-rx' : '');
  document.getElementById('txPanel').className  = 'panel tx-panel' + (tx  ? '' : ' hidden');
  document.getElementById('rxPanel').className  = 'panel rx-panel' + (!tx ? '' : ' hidden');
}

// ─────────────────────────────────────────────────────
//  DEVICE ENUMERATION
// ─────────────────────────────────────────────────────
async function enumDevices() {
  // Prompt for permission first so labels populate
  try {
    const tmp = await navigator.mediaDevices.getUserMedia({ audio: true });
    tmp.getTracks().forEach(t => t.stop());
  } catch (_) { /* ignore */ }

  const devices = await navigator.mediaDevices.enumerateDevices().catch(() => []);

  // Speakers
  const spkSel = document.getElementById('spkSel');
  spkSel.innerHTML = '<option value="">Default Speaker</option>';
  devices.filter(d => d.kind === 'audiooutput').forEach((d, i) => {
    spkSel.add(new Option(d.label || `Speaker ${i + 1}`, d.deviceId));
  });
  spkSel.addEventListener('change', () => setBadge('spkBadge', spkSel));
  setBadge('spkBadge', spkSel);

  // Microphones
  const micSel = document.getElementById('micSel');
  micSel.innerHTML = '';
  devices.filter(d => d.kind === 'audioinput').forEach((d, i) => {
    micSel.add(new Option(d.label || `Microphone ${i + 1}`, d.deviceId));
  });
  micSel.addEventListener('change', () => setBadge('micBadge', micSel));
  setBadge('micBadge', micSel);
}

function setBadge(id, sel) {
  const lbl = sel.options[sel.selectedIndex]?.text || '—';
  document.getElementById(id).textContent = lbl.length > 18 ? lbl.slice(0, 16) + '…' : lbl;
}

function onMicChange() {
  if (isRx) { stopRx(); startRx(); }
}

// ─────────────────────────────────────────────────────
//  IMAGE LOADING
// ─────────────────────────────────────────────────────
const dropZone  = document.getElementById('dropZone');
const fileInput = document.getElementById('fileInput');
const prevCV    = document.getElementById('previewCanvas');
const prevCX    = prevCV.getContext('2d');

dropZone.addEventListener('click', () => fileInput.click());
dropZone.addEventListener('dragover', e => {
  e.preventDefault();
  dropZone.classList.add('drag-over');
});
dropZone.addEventListener('dragleave', e => {
  if (!dropZone.contains(e.relatedTarget)) dropZone.classList.remove('drag-over');
});
dropZone.addEventListener('drop', e => {
  e.preventDefault();
  dropZone.classList.remove('drag-over');
  const f = e.dataTransfer.files[0];
  if (f && f.type.startsWith('image/')) loadFile(f);
});
fileInput.addEventListener('change', e => {
  if (e.target.files[0]) loadFile(e.target.files[0]);
});

function loadFile(file) {
  const reader = new FileReader();
  reader.onload = ev => {
    const img = new Image();
    img.onload = () => {
      origImg = img;
      renderPreview(img);
      processImage(img, CFG.resolution, CFG.nColors);
    };
    img.src = ev.target.result;
  };
  reader.readAsDataURL(file);
}

function renderPreview(img) {
  prevCV.width  = dropZone.offsetWidth  || 500;
  prevCV.height = dropZone.offsetHeight || 188;
  const sc = Math.min(prevCV.width / img.width, prevCV.height / img.height);
  const dw = img.width * sc, dh = img.height * sc;
  prevCX.clearRect(0, 0, prevCV.width, prevCV.height);
  prevCX.drawImage(img, (prevCV.width - dw) / 2, (prevCV.height - dh) / 2, dw, dh);
  dropZone.classList.add('loaded');
}

function processImage(img, res, nc) {
  buildPalette(nc);

  const oc  = document.createElement('canvas');
  oc.width  = oc.height = res;
  const ox  = oc.getContext('2d');
  ox.drawImage(img, 0, 0, res, res);
  const dat = ox.getImageData(0, 0, res, res).data;

  txPixels = new Uint8Array(res * res);
  for (let i = 0; i < res * res; i++) {
    txPixels[i] = quantize(dat[i * 4], dat[i * 4 + 1], dat[i * 4 + 2]);
  }

  document.getElementById('btnTransmit').disabled = false;
  document.getElementById('dropInfo').textContent =
    `${res}×${res} · ${(res * res).toLocaleString()} pixels · ${nc} colors`;
  setTxMsg(`Ready — ${(res * res).toLocaleString()} px`);
}

// ─────────────────────────────────────────────────────
//  TRANSMITTER
// ─────────────────────────────────────────────────────
function toggleTx() { isTx ? stopTx() : startTx(); }

async function startTx() {
  if (!txPixels) return;
  isTx = true;

  const res   = CFG.resolution;
  const nc    = CFG.nColors;
  const toneS = CFG.timeMs / 1000;
  const gapS  = P.PX_GAP   / 1000;

  elById('btnTransmit').textContent = 'STOP TX';
  elById('btnTransmit').classList.add('stopping');
  elById('txLed').className = 'led on-tx';
  setTxMsg('Initialising audio…');

  try {
    txAC = new (window.AudioContext || window.webkitAudioContext)();

    // Try setting output device
    const spkId = elById('spkSel').value;
    if (spkId && txAC.setSinkId) await txAC.setSinkId(spkId).catch(() => {});

    const master = txAC.createGain();
    master.gain.value = 0.88;
    master.connect(txAC.destination);

    // Schedule a single sine-wave tone with smooth attack/release
    function tone(freq, t0, durS, vol = 1) {
      const osc = txAC.createOscillator();
      const g   = txAC.createGain();
      osc.type = 'sine';
      osc.frequency.value = freq;
      osc.connect(g);
      g.connect(master);

      const att = 0.005, rel = 0.005;
      const dur = Math.max(att + rel + 0.001, durS);
      g.gain.setValueAtTime(0, t0);
      g.gain.linearRampToValueAtTime(vol, t0 + att);
      g.gain.setValueAtTime(vol, t0 + dur - rel);
      g.gain.linearRampToValueAtTime(0, t0 + dur);
      osc.start(t0);
      osc.stop(t0 + dur + 0.015);
    }

    let t = txAC.currentTime + 0.06;
    const txStart = t;

    // ── SYNC ──
    tone(P.SYNC_FREQ, t, P.SYNC_DUR / 1000, 0.9);
    t += P.SYNC_DUR / 1000 + P.GAP / 1000;

    // ── HEADER START MARKER ──
    tone(P.HDR_START_F, t, P.HDR_SIG_DUR / 1000, 0.72);
    t += P.HDR_SIG_DUR / 1000 + P.GAP / 1000;

    // ── HEADER VALUES: resolution, nColors, timeMs ──
    tone(val2freq(res,          1,   6000), t, P.HDR_VAL_DUR / 1000, 0.76);
    t += P.HDR_VAL_DUR / 1000 + P.GAP / 1000;
    tone(val2freq(nc,           32,  300),  t, P.HDR_VAL_DUR / 1000, 0.76);
    t += P.HDR_VAL_DUR / 1000 + P.GAP / 1000;
    tone(val2freq(CFG.timeMs,   1,   200),  t, P.HDR_VAL_DUR / 1000, 0.76);
    t += P.HDR_VAL_DUR / 1000 + P.GAP / 1000;

    // ── HEADER END MARKER ──
    tone(P.HDR_END_F, t, P.HDR_SIG_DUR / 1000, 0.72);
    t += P.HDR_SIG_DUR / 1000 + 0.030; // 30ms data gap

    const dataStart = t;

    // ── PIXEL DATA ──
    for (let i = 0; i < txPixels.length; i++) {
      tone(idx2freq(txPixels[i], nc), t, toneS, 0.86);
      t += toneS + gapS;
    }

    // ── END TONE ──
    t += P.GAP / 1000;
    tone(P.END_FREQ, t, P.END_DUR / 1000, 0.72);
    t += P.END_DUR / 1000;

    const totalDur = t - txStart;

    startTxSpec();

    // RAF-based progress tracking (no setInterval needed — AudioContext clock is perfect)
    function trackProgress() {
      if (!isTx) return;
      const now = txAC.currentTime;
      const el  = now - txStart;
      const pct = Math.min(el / totalDur, 1);

      // Figure out current pixel for spectrum
      const pxEl  = now - dataStart;
      const period = toneS + gapS;
      const pxIdx  = Math.floor(pxEl / period);
      if (pxEl > 0 && pxIdx >= 0 && pxIdx < txPixels.length) {
        curTxFreq = idx2freq(txPixels[pxIdx], nc);
      } else if (el < P.SYNC_DUR / 1000) {
        curTxFreq = P.SYNC_FREQ;
      } else {
        curTxFreq = 0;
      }

      setProgress(pct);

      const remMs = Math.max(0, (totalDur - el) * 1000);
      const doneN = Math.max(0, Math.min(pxIdx, txPixels.length));
      elById('progDetail').textContent = pct < 1
        ? `${doneN.toLocaleString()} / ${txPixels.length.toLocaleString()} px — ${fmtTime(remMs)} left`
        : 'Transmission complete ✓';
      setTxMsg(pct < 1 ? 'Transmitting…' : 'Done ✓');

      if (pct < 1) requestAnimationFrame(trackProgress);
      else          finishTx(true);
    }
    requestAnimationFrame(trackProgress);

  } catch (err) {
    setTxMsg(`Error: ${err.message}`);
    finishTx(false);
  }
}

function stopTx() {
  isTx = false;
  if (txAC) { txAC.close().catch(() => {}); txAC = null; }
  finishTx(false);
  setTxMsg('Stopped');
}

function finishTx(ok) {
  isTx      = false;
  curTxFreq = 0;
  stopTxSpec();
  if (txAC && ok) { txAC.close().catch(() => {}); txAC = null; }
  elById('btnTransmit').textContent = 'TRANSMIT';
  elById('btnTransmit').classList.remove('stopping');
  elById('txLed').className = 'led';
  if (!ok) setProgress(0);
}

function setProgress(p) {
  const pct = Math.round(p * 100);
  elById('progFill').style.width = `${pct}%`;
  elById('progPct').textContent  = p > 0 ? `${pct}%` : '—';
}

function setTxMsg(m) { elById('txStatus').textContent = m; }

// TX Spectrum animation
const N_BARS  = 54;
let txSpecRAF = null;

function buildSpecBars() {
  const c = elById('specBars');
  c.innerHTML = '';
  for (let i = 0; i < N_BARS; i++) {
    const b = document.createElement('div');
    b.className = 'spec-bar';
    b.id = `sb${i}`;
    c.appendChild(b);
  }
}

function startTxSpec() {
  function frame() {
    for (let i = 0; i < N_BARS; i++) {
      const f    = P.FREQ_LO + (i / (N_BARS - 1)) * (P.FREQ_HI - P.FREQ_LO);
      const dist = Math.abs(f - curTxFreq);
      const span = (P.FREQ_HI - P.FREQ_LO) / 8;
      const iten = Math.max(0, 1 - dist / span);
      const noise = isTx ? (Math.random() * 4) : 0;
      const h    = Math.max(2, iten * 40 + noise);
      const el   = document.getElementById(`sb${i}`);
      if (!el) continue;
      el.style.height     = `${h}px`;
      el.style.background = `rgba(255,117,53,${0.18 + iten * 0.80})`;
    }
    txSpecRAF = requestAnimationFrame(frame);
  }
  if (txSpecRAF) cancelAnimationFrame(txSpecRAF);
  frame();
}

function stopTxSpec() {
  if (txSpecRAF) { cancelAnimationFrame(txSpecRAF); txSpecRAF = null; }
  document.querySelectorAll('.spec-bar').forEach(b => {
    b.style.height = '2px';
    b.style.background = 'rgba(255,117,53,0.18)';
  });
}

// ─────────────────────────────────────────────────────
//  RECEIVER
// ─────────────────────────────────────────────────────
const rxSpecCV = document.getElementById('rxSpecCanvas');
const rxSpecCX = rxSpecCV.getContext('2d');

function resizeRxSpec() {
  rxSpecCV.width  = rxSpecCV.parentElement.offsetWidth  || 600;
  rxSpecCV.height = rxSpecCV.parentElement.offsetHeight || 88;
}
resizeRxSpec();
window.addEventListener('resize', resizeRxSpec);

function toggleRx() { isRx ? stopRx() : startRx(); }

async function startRx() {
  const micId = elById('micSel').value;
  try {
    rxStream = await navigator.mediaDevices.getUserMedia({
      audio: {
        deviceId:          micId ? { exact: micId } : undefined,
        echoCancellation:  false,
        noiseSuppression:  false,
        autoGainControl:   false,
        sampleRate:        48000,
      }
    });
  } catch (err) {
    setRxMsg(`Microphone error: ${err.message}`);
    return;
  }

  rxAC  = new (window.AudioContext || window.webkitAudioContext)();
  const src = rxAC.createMediaStreamSource(rxStream);
  rxAna = rxAC.createAnalyser();
  rxAna.fftSize              = 8192;
  rxAna.smoothingTimeConstant = 0.0;
  src.connect(rxAna);
  rxFD = new Uint8Array(rxAna.frequencyBinCount);
  rxFR = rxAC.sampleRate / rxAna.fftSize;

  isRx = true;
  resetRxState();

  elById('btnListen').textContent = 'STOP';
  elById('btnListen').classList.add('stopping');
  elById('rxLed').className = 'led on-rx';
  setRxMsg('Scanning for sync signal…');
  setRxPhase('IDLE — AWAITING SYNC', 'Listening on selected microphone');

  rxTimer = setInterval(rxTick, 2);
  drawRxSpectrum();
}

function stopRx() {
  isRx = false;
  if (rxTimer)  { clearInterval(rxTimer);        rxTimer  = null; }
  if (rxRAF)    { cancelAnimationFrame(rxRAF);   rxRAF    = null; }
  if (rxStream) { rxStream.getTracks().forEach(t => t.stop()); rxStream = null; }
  if (rxAC)     { rxAC.close().catch(() => {});  rxAC     = null; }

  elById('btnListen').textContent = 'START LISTENING';
  elById('btnListen').classList.remove('stopping');
  elById('rxLed').className = 'led';
  setRxMsg('Stopped');
}

function resetRxState() {
  rxPhase   = 'IDLE';
  rxSyncDet = 0;
  rxSyncEnd = 0;
  rxSyncDB  = 0;
  rxHdrBuf  = { res: [], col: [], tm: [] };
  rxDetCFG  = null;
  rxDataSt  = 0;
  rxLastPx  = -1;
  rxPixels  = [];
  rxPxCnt   = 0;
}

function clearRx() {
  resetRxState();
  setRxPhase('IDLE — AWAITING SYNC', 'Cleared');
  setRxMsg('Cleared');
  elById('rxPixelCount').textContent = '0 px';
  elById('imgOutput').className = 'img-output';
  elById('autoDetail').textContent = 'Awaiting header…';
  const rc  = elById('rxCanvas');
  rc.getContext('2d').clearRect(0, 0, rc.width, rc.height);
  rc.style.display = 'none';
}

// ── FFT helpers ──
function refreshFD() { rxAna.getByteFrequencyData(rxFD); }

function peakInRange(fLo, fHi) {
  const b0 = Math.max(0, Math.floor(fLo / rxFR));
  const b1 = Math.min(rxFD.length - 1, Math.ceil(fHi / rxFR));
  let maxM = 0, maxB = b0;
  for (let i = b0; i <= b1; i++) {
    if (rxFD[i] > maxM) { maxM = rxFD[i]; maxB = i; }
  }
  return { freq: maxB * rxFR, mag: maxM };
}

function medianOf(arr) {
  if (!arr.length) return P.FREQ_LO + (P.FREQ_HI - P.FREQ_LO) / 2;
  const s = [...arr].sort((a, b) => a - b);
  const m = Math.floor(s.length / 2);
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

// ── RX State machine (called every 2ms) ──
function rxTick() {
  if (!rxAna) return;
  const now = performance.now();
  refreshFD();

  if (rxPhase === 'IDLE') {
    const pk = peakInRange(P.SYNC_FREQ - 38, P.SYNC_FREQ + 38);
    if (pk.mag > 65) {
      if (!rxSyncDet) rxSyncDet = now;
      if (now - rxSyncDet > 80) {
        rxPhase = 'SYNC';
        rxSyncDB = 0;
        setRxPhase('SYNC DETECTED', 'Carrier locked — waiting for header…');
        setRxMsg('Sync tone detected');
      }
    } else {
      rxSyncDet = 0;
    }

  } else if (rxPhase === 'SYNC') {
    const pk = peakInRange(P.SYNC_FREQ - 38, P.SYNC_FREQ + 38);
    if (pk.mag < 42) {
      if (!rxSyncDB) rxSyncDB = now;
      if (now - rxSyncDB > 35) {
        rxPhase   = 'HDR';
        rxSyncEnd = now;
        rxHdrBuf  = { res: [], col: [], tm: [] };
        setRxPhase('READING HEADER', 'Decoding resolution, colors, tone duration…');
        setRxMsg('Header in progress…');
      }
    } else {
      rxSyncDB = 0;
    }

  } else if (rxPhase === 'HDR') {
    const t = now - rxSyncEnd;

    // Sample each value tone during its central 60% window
    const RES_SAMPLE_LO = H.RES_S + P.HDR_VAL_DUR * 0.20;
    const RES_SAMPLE_HI = H.RES_S + P.HDR_VAL_DUR * 0.80;
    const COL_SAMPLE_LO = H.COL_S + P.HDR_VAL_DUR * 0.20;
    const COL_SAMPLE_HI = H.COL_S + P.HDR_VAL_DUR * 0.80;
    const TM_SAMPLE_LO  = H.TM_S  + P.HDR_VAL_DUR * 0.20;
    const TM_SAMPLE_HI  = H.TM_S  + P.HDR_VAL_DUR * 0.80;

    const dataFreqPk = peakInRange(P.FREQ_LO - 30, P.FREQ_HI + 30);

    if (t >= RES_SAMPLE_LO && t < RES_SAMPLE_HI && dataFreqPk.mag > 28)
      rxHdrBuf.res.push(dataFreqPk.freq);
    if (t >= COL_SAMPLE_LO && t < COL_SAMPLE_HI && dataFreqPk.mag > 28)
      rxHdrBuf.col.push(dataFreqPk.freq);
    if (t >= TM_SAMPLE_LO  && t < TM_SAMPLE_HI  && dataFreqPk.mag > 28)
      rxHdrBuf.tm.push(dataFreqPk.freq);

    if (t >= H.DATA_S) {
      // Decode header using median of all samples
      const detRes = clamp(Math.round(freq2val(medianOf(rxHdrBuf.res), 1, 6000)),   1,   6000);
      const detCol = clamp(Math.round(freq2val(medianOf(rxHdrBuf.col), 32, 300)),   32,  300);
      const detTm  = clamp(Math.round(freq2val(medianOf(rxHdrBuf.tm),  1, 200)),    1,   200);

      rxDetCFG = { resolution: detRes, nColors: detCol, timeMs: detTm };
      buildPalette(detCol);
      setupRxCanvas(detRes);

      rxPhase  = 'DATA';
      rxDataSt = now;
      rxLastPx = -1;

      const lbl = `${detRes}×${detRes} · ${detCol}c · ${detTm}ms/px`;
      setRxPhase(`RECEIVING — ${detRes}×${detRes}`, `${detCol} colors · ${detTm}ms/px`);
      setRxMsg(`Receiving ${(detRes * detRes).toLocaleString()} pixels…`);
      elById('autoDetail').textContent = lbl;
    }

  } else if (rxPhase === 'DATA') {
    const cfg    = rxDetCFG;
    const period = cfg.timeMs + P.PX_GAP;
    const elapsed = now - rxDataSt;

    // Check for end tone (above data band)
    const endPk = peakInRange(P.END_FREQ - 130, P.END_FREQ + 130);
    if (endPk.mag > 55 && endPk.freq > 5300) {
      finishRxData();
      return;
    }

    const pxIdx  = Math.floor(elapsed / period);
    const pxOff  = elapsed % period;
    const total  = cfg.resolution * cfg.resolution;

    // Sample in central portion of the tone window
    const sampleLo = cfg.timeMs * 0.28;
    const sampleHi = cfg.timeMs * 0.74;

    if (pxOff >= sampleLo && pxOff <= sampleHi && pxIdx !== rxLastPx && pxIdx < total) {
      rxLastPx = pxIdx;
      const dataPk = peakInRange(P.FREQ_LO - 60, P.FREQ_HI + 60);
      if (dataPk.mag > 30) {
        const ci = freq2idx(dataPk.freq, cfg.nColors);
        rxPixels[pxIdx] = ci;
        drawRxPixel(pxIdx, ci, cfg.resolution);
        rxPxCnt++;
        elById('rxPixelCount').textContent = `${rxPxCnt} / ${total.toLocaleString()} px`;
      }
    }

    if (pxIdx >= total) finishRxData();
  }
}

function finishRxData() {
  rxPhase = 'DONE';
  const total = rxDetCFG ? rxDetCFG.resolution * rxDetCFG.resolution : 0;
  setRxPhase('COMPLETE ✓', `${rxPxCnt.toLocaleString()} of ${total.toLocaleString()} pixels received`);
  setRxMsg(`Received ${rxPxCnt.toLocaleString()} px`);
  elById('imgOutput').classList.add('has-img');
}

function setupRxCanvas(res) {
  const rc  = elById('rxCanvas');
  rc.width  = res;
  rc.height = res;
  const rcx = rc.getContext('2d');
  rcx.fillStyle = '#000';
  rcx.fillRect(0, 0, res, res);
  rc.style.display  = 'block';
  rc.style.imageRendering = 'pixelated';
}

function drawRxPixel(idx, ci, res) {
  const rc  = elById('rxCanvas');
  const rcx = rc.getContext('2d');
  const x   = idx % res;
  const y   = Math.floor(idx / res);
  const [r, g, b] = palette[ci] || [0, 0, 0];
  rcx.fillStyle = `rgb(${r},${g},${b})`;
  rcx.fillRect(x, y, 1, 1);
}

function saveImg() {
  const rc = elById('rxCanvas');
  const a  = document.createElement('a');
  a.download = `audiopix_${Date.now()}.png`;
  a.href = rc.toDataURL('image/png');
  a.click();
}

function setRxMsg(m)           { elById('rxStatus').textContent    = m; }
function setRxPhase(lbl, sub)  {
  elById('rxPhaseLabel').textContent = lbl;
  elById('rxPhaseSub').textContent   = sub || '';
}

// ── RX Spectrum display ──
function drawRxSpectrum() {
  if (!isRx || !rxAna) return;
  rxAna.getByteFrequencyData(rxFD);

  const W    = rxSpecCV.width, H = rxSpecCV.height;
  rxSpecCX.fillStyle = 'rgba(0,0,0,0.4)';
  rxSpecCX.fillRect(0, 0, W, H);

  const maxFreq = 6600;
  const maxBin  = Math.floor(maxFreq / rxFR);
  const nBars   = Math.min(maxBin, Math.floor(W / 1.5));
  const bw      = W / nBars;
  const nc      = (rxDetCFG || CFG).nColors;

  for (let i = 0; i < nBars; i++) {
    const bin  = Math.floor(i * maxBin / nBars);
    const mag  = rxFD[Math.min(bin, rxFD.length - 1)];
    const bh   = (mag / 255) * H;
    const freq = bin * rxFR;

    let col;
    if (Math.abs(freq - P.SYNC_FREQ) < 40) {
      // SYNC tone — yellow
      const a = 0.5 + mag / 512;
      col = `rgba(255,220,0,${a})`;
    } else if (freq > 5400 && freq < 5850) {
      // Control tones — magenta
      const a = 0.45 + mag / 512;
      col = `rgba(220,0,255,${a})`;
    } else if (freq >= P.FREQ_LO && freq <= P.FREQ_HI) {
      // Data band — actual palette colour
      const ci      = freq2idx(freq, nc);
      const [r,g,b] = palette[ci] || [0, 200, 200];
      const a       = 0.55 + mag / 640;
      col = `rgba(${r},${g},${b},${a})`;
    } else {
      // Below/above band — dim teal
      const a = 0.12 + mag / 1200;
      col = `rgba(0,212,200,${a})`;
    }

    rxSpecCX.fillStyle = col;
    rxSpecCX.fillRect(~~(i * bw), H - bh, Math.max(1, bw - 0.4), bh);
  }

  rxRAF = requestAnimationFrame(drawRxSpectrum);
}

// ─────────────────────────────────────────────────────
//  CONTROLS POPUP
// ─────────────────────────────────────────────────────
function openControls() {
  // Sync pending to current config
  PND.resolution = CFG.resolution;
  PND.nColors    = CFG.nColors;
  PND.timeMs     = CFG.timeMs;

  elById('colSlider').value = CFG.nColors;
  elById('resSlider').value = resToSlider(CFG.resolution);
  elById('tmSlider').value  = CFG.timeMs;

  updatePopupUI();
  elById('overlay').classList.remove('hidden');
}

function closeControls() {
  elById('overlay').classList.add('hidden');
}

function overlayClick(e) {
  if (e.target === elById('overlay')) closeControls();
}

function applySettings() {
  CFG.resolution = PND.resolution;
  CFG.nColors    = PND.nColors;
  CFG.timeMs     = PND.timeMs;

  buildPalette(CFG.nColors);
  if (origImg) processImage(origImg, CFG.resolution, CFG.nColors);
  updatePalStrip(CFG.nColors);
  updateBadge();
  closeControls();
}

// Logarithmic slider for resolution (1–6000)
function sliderToRes(v) { return Math.max(1, Math.min(6000, Math.round(Math.pow(6000, v / 100)))); }
function resToSlider(r) { return Math.round(Math.log(Math.max(1, r)) / Math.log(6000) * 100); }

function onColChange(v) { PND.nColors    = parseInt(v);           updatePopupUI(); }
function onResChange(v) { PND.resolution = sliderToRes(parseFloat(v)); updatePopupUI(); }
function onTmChange(v)  { PND.timeMs     = parseInt(v);           updatePopupUI(); }

function updatePopupUI() {
  const { resolution: res, nColors: nc, timeMs: tm } = PND;

  // Value labels
  elById('colVal').textContent = `${nc}`;
  elById('resVal').textContent = `${res}×${res}`;
  elById('tmVal').textContent  = `${tm}ms`;

  // Palette swatch strip
  buildPopPalette(nc);

  // Resolution grid preview
  buildResGrid(res);
  elById('resStats').textContent = `${(res * res).toLocaleString()} pixels`;

  // Speed bar
  const speedPct = (tm / 200) * 100;
  elById('speedFill').style.width = `${speedPct}%`;
  elById('speedLabel').textContent =
    tm <= 10 ? 'Ultrafast' :
    tm <= 25 ? 'Fast' :
    tm <= 60 ? 'Normal' :
    tm <= 120 ? 'Slow' : 'Very slow';

  // Estimate
  const { pixels, headerMs, pixelMs, totalMs } = calcEst(res, nc, tm);

  elById('estPx').textContent    = pixels.toLocaleString();
  elById('estHdr').textContent   = fmtTime(headerMs);
  elById('estTotal').textContent = fmtTime(totalMs);

  elById('estNote').textContent =
    totalMs > 18000000 ? '⚠ Multi-hour transfer' :
    totalMs >  3600000 ? '⏳ Multi-hour transfer' :
    totalMs >   600000 ? '☕ Coffee break needed' :
    totalMs >    60000 ? '⏱ Minutes to complete' :
    totalMs >    10000 ? '⚡ Under a minute' :
                          '🚀 Super fast!';

  // Timeline bar (header vs pixels)
  if (totalMs > 0) {
    const hPct = Math.max(4, (headerMs / totalMs) * 100);
    const pPct = Math.max(0, 100 - hPct);
    elById('etlHdr').style.width = `${hPct}%`;
    elById('etlPix').style.width = `${pPct}%`;
  }
}

function buildPopPalette(n) {
  buildPalette(n);
  const el = elById('palPreview');
  el.innerHTML = '';
  palette.forEach(([r, g, b]) => {
    const s = document.createElement('div');
    s.className = 'pal-swatch';
    s.style.background = `rgb(${r},${g},${b})`;
    el.appendChild(s);
  });
}

function buildResGrid(res) {
  const g = elById('resGrid');
  const n = Math.min(res, 14);
  g.style.gridTemplateColumns = `repeat(${n},1fr)`;
  g.innerHTML = '';
  for (let i = 0; i < n * n; i++) {
    const d = document.createElement('div');
    d.className = 'res-grid-cell';
    d.style.background = `hsl(${(i * 137.508) % 360},62%,${30 + (i % 5) * 10}%)`;
    g.appendChild(d);
  }
}

function updatePalStrip(n) {
  buildPalette(n);
  const strip = elById('palStripTx');
  strip.innerHTML = '';
  palette.forEach(([r, g, b]) => {
    const s = document.createElement('div');
    s.className = 'pal-sw';
    s.style.background = `rgb(${r},${g},${b})`;
    strip.appendChild(s);
  });
  elById('palCountTx').textContent = `${n} colors`;
}

function updateBadge() {
  elById('settingsBadge').textContent =
    `${CFG.resolution}px · ${CFG.nColors}c · ${CFG.timeMs}ms`;
}

// ─────────────────────────────────────────────────────
//  UTILITY
// ─────────────────────────────────────────────────────
function elById(id)         { return document.getElementById(id); }
function clamp(v, lo, hi)   { return Math.max(lo, Math.min(hi, v)); }

// ─────────────────────────────────────────────────────
//  INIT
// ─────────────────────────────────────────────────────
buildPalette(CFG.nColors);
buildSpecBars();
updatePalStrip(CFG.nColors);
updateBadge();
updatePopupUI();
enumDevices();

// Keep idle spectrum bars gently animated
(function idleSpecAnim() {
  if (!isTx) {
    for (let i = 0; i < N_BARS; i++) {
      const b = document.getElementById(`sb${i}`);
      if (b) {
        const h = 2 + Math.sin(Date.now() * 0.002 + i * 0.4) * 1.5;
        b.style.height = `${h}px`;
      }
    }
  }
  requestAnimationFrame(idleSpecAnim);
})();
