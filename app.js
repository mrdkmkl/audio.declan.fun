'use strict';
/* ════════════════════════════════════════════════════════════
   AUDIOPIX — app.js

   PROTOCOL:
     1. SYNC TONE   — 180 Hz for 800 ms  (lock)
     2. HEADER TONE — single tone where:
          frequency = encodes resolution (1-6000)  → FREQ_LO..FREQ_HI
          duration  = encodes toneMs    (1-200 ms) → 400..3000 ms
     3. PIXEL DATA  — n*n tones, each toneMs long, gapped by PX_GAP ms
     4. END TONE    — 5500 Hz for 400 ms

   TX uses a SINGLE oscillator with scheduled frequency/gain changes.
   This guarantees audio always plays regardless of color count.
═════════════════════════════════════════════════════════════ */

// ──────────────────────────────────────────
//  PROTOCOL PARAMETERS
// ──────────────────────────────────────────
const P = {
  FREQ_LO:   600,    // Hz — data band low
  FREQ_HI:  4500,    // Hz — data band high

  SYNC_F:    180,    // Hz — sync carrier
  SYNC_MS:   800,    // ms — sync duration

  END_F:    5500,    // Hz — end marker
  END_MS:    400,    // ms

  PX_GAP:      4,    // ms — silence between pixel tones
  PRE_GAP:    60,    // ms — silence before data starts (after header)
  ATT:       0.005,  // s  — tone attack
  REL:       0.005,  // s  — tone release

  // Header tone duration range (encodes toneMs 1..200)
  HDR_DUR_LO: 400,   // ms when toneMs = 1
  HDR_DUR_HI: 3000,  // ms when toneMs = 200

  // Detection thresholds
  SYNC_TH:    55,    // magnitude threshold for sync detect
  HDR_TH:     30,    // threshold for header tone
  DATA_TH:    28,    // threshold for data tones
  END_TH:     45,    // threshold for end tone
};

// ──────────────────────────────────────────
//  CONFIG
// ──────────────────────────────────────────
const CFG = { resolution: 32, nColors: 124, timeMs: 50 };
const PND = { ...CFG };  // pending (popup, unapplied)

// ──────────────────────────────────────────
//  STATE
// ──────────────────────────────────────────
let mode      = 'tx';
let palette   = [];
let txPixels  = null;
let origImg   = null;
let isTx      = false;
let txAC      = null;   // TX AudioContext

let isRx      = false;
let rxAC      = null;
let rxStream  = null;
let rxAna     = null;
let rxFD      = null;
let rxFR      = 1;      // Hz/bin
let rxTimer   = null;
let rxRAF     = null;

let rxPhase      = 'IDLE';   // IDLE | SYNC | HDR | DATA | DONE
let rxSyncDet    = 0;        // time of first sync sample
let rxSyncGone   = 0;        // time sync first disappeared
let rxHdrStart   = 0;        // time header tone was first detected
let rxHdrFreqs   = [];       // sampled frequencies during header
let rxHdrGone    = 0;        // time header tone first disappeared
let rxDetCFG     = null;     // { resolution, nColors(unused), timeMs } decoded
let rxManCFG     = null;     // manually-entered override
let rxDataStart  = 0;        // time pixel data stream began
let rxLastPx     = -1;
let rxPixels     = [];
let rxPxCnt      = 0;

let curTxFreq    = 0;        // for spectrum animation

// ──────────────────────────────────────────
//  HELPERS
// ──────────────────────────────────────────
const $ = id => document.getElementById(id);
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

// Frequency ↔ index (data band)
function idx2freq(i, n)  { return P.FREQ_LO + (i / (n - 1)) * (P.FREQ_HI - P.FREQ_LO); }
function freq2idx(f, n)  { return clamp(Math.round((f - P.FREQ_LO) / (P.FREQ_HI - P.FREQ_LO) * (n - 1)), 0, n - 1); }

// Encode resolution into header frequency
function res2freq(res)   { return P.FREQ_LO + ((res - 1) / 5999) * (P.FREQ_HI - P.FREQ_LO); }
function freq2res(f)     { return clamp(Math.round(1 + ((f - P.FREQ_LO) / (P.FREQ_HI - P.FREQ_LO)) * 5999), 1, 6000); }

// Encode toneMs into header duration
function ms2hdrDur(ms)   { return P.HDR_DUR_LO + ((ms - 1) / 199) * (P.HDR_DUR_HI - P.HDR_DUR_LO); }
function hdrDur2ms(dur)  { return clamp(Math.round(1 + ((dur - P.HDR_DUR_LO) / (P.HDR_DUR_HI - P.HDR_DUR_LO)) * 199), 1, 200); }

function fmtTime(ms) {
  if (ms < 1000)   return `${ms.toFixed(0)} ms`;
  if (ms < 60000)  return `${(ms / 1000).toFixed(1)} s`;
  const m = Math.floor(ms / 60000), s = Math.floor((ms % 60000) / 1000);
  if (ms < 3600000) return s ? `${m}m ${s}s` : `${m}m`;
  const h = Math.floor(ms / 3600000), rm = Math.floor((ms % 3600000) / 60000);
  return rm ? `${h}h ${rm}m` : `${h}h`;
}

// ──────────────────────────────────────────
//  ESTIMATION
// ──────────────────────────────────────────
function calcEst(res, nc, ms) {
  const pixels  = res * res;
  const syncMs  = P.SYNC_MS;
  const hdrMs   = ms2hdrDur(ms);
  const dataMs  = pixels * (ms + P.PX_GAP);
  const endMs   = P.PRE_GAP + P.END_MS;
  const total   = syncMs + hdrMs + P.PRE_GAP + dataMs + endMs;
  return { pixels, syncMs, hdrMs, dataMs, endMs, total };
}

// ──────────────────────────────────────────
//  PALETTE
// ──────────────────────────────────────────
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
  const tiers = [[92,20],[85,35],[78,50],[70,65],[62,79]];
  for (let i = 0; i < chromatic; i++) {
    const [s, l] = tiers[i % tiers.length];
    palette.push(hsl2rgb((i * 137.508) % 360, s, l));
  }
  palette.push([10,10,12], [80,80,88], [165,165,175], [242,242,248]);
}

function quantize(r, g, b) {
  let best = 0, d = Infinity;
  for (let i = 0; i < palette.length; i++) {
    const [pr, pg, pb] = palette[i];
    const dd = 0.2126*(r-pr)**2 + 0.7152*(g-pg)**2 + 0.0722*(b-pb)**2;
    if (dd < d) { d = dd; best = i; }
  }
  return best;
}

// ──────────────────────────────────────────
//  ANIMATED BACKGROUND
// ──────────────────────────────────────────
const bgCV = $('bgCanvas');
const bgCX = bgCV.getContext('2d');
let bgT = 0;

function resizeBg() { bgCV.width = innerWidth; bgCV.height = innerHeight; }
resizeBg();
addEventListener('resize', resizeBg);

(function animBg() {
  const W = bgCV.width, H = bgCV.height;
  bgCX.clearRect(0, 0, W, H);
  const colFn = mode === 'tx'
    ? a => `rgba(255,117,53,${a})`
    : a => `rgba(0,212,200,${a})`;
  for (let w = 0; w < 8; w++) {
    const ph  = bgT * 0.00038 + w * 0.85;
    const amp = 18 + w * 15;
    const fq  = 0.0028 + w * 0.0017;
    const yb  = H * (0.08 + w * 0.12);
    const env = Math.sin(bgT * 0.00022 + w * 0.44);
    bgCX.beginPath();
    bgCX.moveTo(0, yb);
    for (let x = 0; x <= W; x += 3) bgCX.lineTo(x, yb + Math.sin(x * fq + ph) * amp * env);
    bgCX.strokeStyle = colFn(0.018 + w * 0.01);
    bgCX.lineWidth = 1;
    bgCX.stroke();
  }
  bgT++;
  requestAnimationFrame(animBg);
})();

// ──────────────────────────────────────────
//  MODE
// ──────────────────────────────────────────
function setMode(m) {
  mode = m;
  const tx = m === 'tx';
  $('btnTx').className    = 'mode-btn' + (tx  ? ' active-tx' : '');
  $('btnRx').className    = 'mode-btn' + (!tx ? ' active-rx' : '');
  $('txPanel').className  = 'panel tx-panel' + (tx  ? '' : ' hidden');
  $('rxPanel').className  = 'panel rx-panel' + (!tx ? '' : ' hidden');
}

// ──────────────────────────────────────────
//  DEVICE ENUMERATION
// ──────────────────────────────────────────
async function enumDevices() {
  try { const t = await navigator.mediaDevices.getUserMedia({audio:true}); t.getTracks().forEach(t=>t.stop()); } catch(_) {}
  const devs = await navigator.mediaDevices.enumerateDevices().catch(() => []);

  const spkSel = $('spkSel');
  spkSel.innerHTML = '<option value="">Default Speaker</option>';
  devs.filter(d => d.kind === 'audiooutput').forEach((d, i) => spkSel.add(new Option(d.label || `Speaker ${i+1}`, d.deviceId)));
  spkSel.addEventListener('change', () => badge('spkBadge', spkSel));
  badge('spkBadge', spkSel);

  const micSel = $('micSel');
  micSel.innerHTML = '';
  devs.filter(d => d.kind === 'audioinput').forEach((d, i) => micSel.add(new Option(d.label || `Mic ${i+1}`, d.deviceId)));
  micSel.addEventListener('change', () => badge('micBadge', micSel));
  badge('micBadge', micSel);
}

function badge(id, sel) {
  const l = sel.options[sel.selectedIndex]?.text || '—';
  $(id).textContent = l.length > 18 ? l.slice(0, 16) + '…' : l;
}

function onMicChange() { if (isRx) { stopRx(); startRx(); } }

// ──────────────────────────────────────────
//  IMAGE LOADING
// ──────────────────────────────────────────
const dropZone = $('dropZone');
const fileInEl = $('fileInput');
const prevCV   = $('previewCanvas');
const prevCX   = prevCV.getContext('2d');

dropZone.addEventListener('click', () => fileInEl.click());
dropZone.addEventListener('dragover', e => { e.preventDefault(); dropZone.classList.add('drag-over'); });
dropZone.addEventListener('dragleave', e => { if (!dropZone.contains(e.relatedTarget)) dropZone.classList.remove('drag-over'); });
dropZone.addEventListener('drop', e => {
  e.preventDefault(); dropZone.classList.remove('drag-over');
  const f = e.dataTransfer.files[0];
  if (f && f.type.startsWith('image/')) loadFile(f);
});
fileInEl.addEventListener('change', e => { if (e.target.files[0]) loadFile(e.target.files[0]); });

function loadFile(file) {
  const rd = new FileReader();
  rd.onload = ev => {
    const img = new Image();
    img.onload = () => { origImg = img; renderPreview(img); processImage(img, CFG.resolution, CFG.nColors); };
    img.src = ev.target.result;
  };
  rd.readAsDataURL(file);
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
  const oc = Object.assign(document.createElement('canvas'), { width: res, height: res });
  const ox = oc.getContext('2d');
  ox.drawImage(img, 0, 0, res, res);
  const dat = ox.getImageData(0, 0, res, res).data;
  txPixels = new Uint8Array(res * res);
  for (let i = 0; i < res * res; i++) txPixels[i] = quantize(dat[i*4], dat[i*4+1], dat[i*4+2]);

  $('btnTransmit').disabled = false;
  $('btnPreview').disabled  = false;
  $('dropInfo').textContent = `${res}×${res} · ${(res*res).toLocaleString()} px · ${nc} colors`;
  setTxMsg(`Ready — ${(res*res).toLocaleString()} pixels`);
}

// ──────────────────────────────────────────
//  PREVIEW MODAL
// ──────────────────────────────────────────
function showPreview() {
  if (!txPixels || !origImg) return;
  const res = CFG.resolution;

  // Original thumb (scaled down)
  const DISP = 240;
  const sc   = Math.min(DISP / origImg.width, DISP / origImg.height);
  const ow   = Math.round(origImg.width * sc);
  const oh   = Math.round(origImg.height * sc);
  const origC = $('origThumb');
  origC.width = ow; origC.height = oh;
  origC.style.width  = ow + 'px';
  origC.style.height = oh + 'px';
  origC.getContext('2d').drawImage(origImg, 0, 0, ow, oh);

  // Quantized thumb — render at 1px/pixel then scale via CSS
  const qtC = $('quantThumb');
  qtC.width  = res; qtC.height = res;
  const disp = Math.min(DISP, Math.max(80, res * Math.floor(DISP / res)));
  qtC.style.width  = disp + 'px';
  qtC.style.height = disp + 'px';
  const qtX = qtC.getContext('2d');
  for (let i = 0; i < txPixels.length; i++) {
    const x = i % res, y = Math.floor(i / res);
    const [r, g, b] = palette[txPixels[i]] || [0, 0, 0];
    qtX.fillStyle = `rgb(${r},${g},${b})`;
    qtX.fillRect(x, y, 1, 1);
  }

  const est = calcEst(res, CFG.nColors, CFG.timeMs);
  $('prevMeta').textContent =
    `${res}×${res} px  ·  ${CFG.nColors} colors  ·  ${CFG.timeMs}ms/tone  ·  ${fmtTime(est.total)} total`;
  $('prevOverlay').classList.remove('hidden');
}

function closePreview()    { $('prevOverlay').classList.add('hidden'); }
function closePrevOverlay(e) { if (e.target === $('prevOverlay')) closePreview(); }

// ──────────────────────────────────────────
//  TRANSMITTER — single oscillator
// ──────────────────────────────────────────
async function handleTransmitClick() {
  if (isTx) { stopTx(); return; }

  if (!txPixels) return;

  // Show "loading" for 2 s so browser can finish any pending renders / audio init
  const btn = $('btnTransmit');
  btn.disabled = true;
  $('btnPreview').disabled = true;

  const pctEl = $('progPct');
  pctEl.textContent = 'LOADING';
  pctEl.classList.add('loading');
  setTxMsg('Processing…');
  $('progDetail').textContent = 'Preparing transmission…';

  // Re-process image with current CFG (ensures txPixels is fresh)
  if (origImg) processImage(origImg, CFG.resolution, CFG.nColors);

  await new Promise(r => setTimeout(r, 2000));

  pctEl.classList.remove('loading');
  btn.disabled = false;
  $('btnPreview').disabled = false;

  startTx();
}

function startTx() {
  if (!txPixels) return;
  isTx = true;

  const res    = CFG.resolution;
  const nc     = CFG.nColors;
  const toneS  = CFG.timeMs / 1000;
  const gapS   = P.PX_GAP / 1000;
  const attS   = P.ATT;
  const relS   = P.REL;

  const btn = $('btnTransmit');
  btn.textContent = 'STOP TX';
  btn.classList.add('stopping');
  $('txLed').className = 'led on-tx';
  setTxMsg('Initialising audio…');

  try {
    txAC = new (window.AudioContext || window.webkitAudioContext)();

    const spkId = $('spkSel').value;
    if (spkId && txAC.setSinkId) txAC.setSinkId(spkId).catch(() => {});

    // Master gain
    const master = txAC.createGain();
    master.gain.value = 0.88;
    master.connect(txAC.destination);

    // ── Single oscillator ──
    const osc  = txAC.createOscillator();
    const gain = txAC.createGain();
    osc.type = 'sine';
    osc.connect(gain);
    gain.connect(master);
    gain.gain.setValueAtTime(0, 0);  // start silent

    // Helper: schedule one "note" on the single osc
    function note(freq, t0, durS, vol) {
      const dur = Math.max(attS + relS + 0.002, durS);
      osc.frequency.setValueAtTime(freq, t0);
      gain.gain.setValueAtTime(0, t0);
      gain.gain.linearRampToValueAtTime(vol, t0 + attS);
      gain.gain.setValueAtTime(vol, t0 + dur - relS);
      gain.gain.linearRampToValueAtTime(0, t0 + dur);
    }

    let t = txAC.currentTime + 0.06;
    const txStart = t;

    // 1. SYNC
    note(P.SYNC_F, t, P.SYNC_MS / 1000, 0.9);
    t += P.SYNC_MS / 1000;

    // 2. HEADER TONE: freq=res, dur=toneMs
    const hdrFreq = res2freq(res);
    const hdrDurS = ms2hdrDur(CFG.timeMs) / 1000;
    note(hdrFreq, t, hdrDurS, 0.78);
    t += hdrDurS;

    // 3. Pre-data gap
    t += P.PRE_GAP / 1000;
    const dataStart = t;

    // 4. PIXELS — schedule all at once using single osc parameter automation
    for (let i = 0; i < txPixels.length; i++) {
      const freq = idx2freq(txPixels[i], nc);
      note(freq, t, toneS, 0.86);
      t += toneS + gapS;
    }

    // 5. END
    t += P.PX_GAP / 1000;
    note(P.END_F, t, P.END_MS / 1000, 0.72);
    t += P.END_MS / 1000;

    const totalDur = t - txStart;
    osc.start(txAC.currentTime);
    osc.stop(t + 0.1);

    startTxSpec();
    setTxMsg('Transmitting…');

    function trackProgress() {
      if (!isTx) return;
      const now = txAC.currentTime;
      const el  = now - txStart;
      const pct = clamp(el / totalDur, 0, 1);

      // Update spectrum frequency indicator
      const pxEl   = now - dataStart;
      const period = toneS + gapS;
      const pxIdx  = Math.floor(pxEl / period);
      if (pxEl > 0 && pxIdx >= 0 && pxIdx < txPixels.length) {
        curTxFreq = idx2freq(txPixels[pxIdx], nc);
      } else if (el < P.SYNC_MS / 1000) {
        curTxFreq = P.SYNC_F;
      } else if (el < P.SYNC_MS / 1000 + hdrDurS) {
        curTxFreq = hdrFreq;
      } else {
        curTxFreq = 0;
      }

      setProgress(pct);

      const remMs  = Math.max(0, (totalDur - el) * 1000);
      const doneN  = Math.max(0, Math.min(pxIdx, txPixels.length));
      $('progDetail').textContent = pct < 1
        ? `${doneN.toLocaleString()} / ${txPixels.length.toLocaleString()} px — ${fmtTime(remMs)} left`
        : 'Complete ✓';
      setTxMsg(pct < 1 ? 'Transmitting…' : 'Done ✓');

      if (pct < 1) requestAnimationFrame(trackProgress);
      else          finishTx(true);
    }
    requestAnimationFrame(trackProgress);

  } catch(err) {
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
  isTx = false; curTxFreq = 0;
  stopTxSpec();
  if (txAC && ok) { txAC.close().catch(() => {}); txAC = null; }
  const btn = $('btnTransmit');
  btn.textContent = 'TRANSMIT';
  btn.classList.remove('stopping');
  btn.disabled = false;
  $('btnPreview').disabled = !txPixels;
  $('txLed').className = 'led';
  if (!ok) setProgress(0);
}

function setProgress(p) {
  const pct = Math.round(p * 100);
  $('progFill').style.width = `${pct}%`;
  $('progPct').textContent  = (p > 0 && !$('progPct').classList.contains('loading')) ? `${pct}%` : $('progPct').textContent;
}

function setTxMsg(m) { $('txStatus').textContent = m; }

// TX Spectrum
const N_BARS = 54;
let txSpecRAF = null;

function buildSpecBars() {
  const c = $('specBars');
  c.innerHTML = '';
  for (let i = 0; i < N_BARS; i++) {
    const b = document.createElement('div');
    b.className = 'spec-bar'; b.id = `sb${i}`;
    c.appendChild(b);
  }
}

function startTxSpec() {
  function frame() {
    for (let i = 0; i < N_BARS; i++) {
      const f    = P.FREQ_LO + (i / (N_BARS - 1)) * (P.FREQ_HI - P.FREQ_LO);
      const dist = Math.abs(f - curTxFreq);
      const span = (P.FREQ_HI - P.FREQ_LO) / 7;
      const iten = Math.max(0, 1 - dist / span);
      const h    = Math.max(2, iten * 40 + (isTx ? Math.random() * 3 : 0));
      const el   = document.getElementById(`sb${i}`);
      if (el) {
        el.style.height     = `${h}px`;
        el.style.background = `rgba(255,117,53,${0.18 + iten * 0.80})`;
      }
    }
    txSpecRAF = requestAnimationFrame(frame);
  }
  if (txSpecRAF) cancelAnimationFrame(txSpecRAF);
  frame();
}

function stopTxSpec() {
  if (txSpecRAF) { cancelAnimationFrame(txSpecRAF); txSpecRAF = null; }
  document.querySelectorAll('.spec-bar').forEach(b => { b.style.height = '2px'; b.style.background = 'rgba(255,117,53,.18)'; });
}

// Idle spectrum shimmer
(function idleSpec() {
  if (!isTx) {
    for (let i = 0; i < N_BARS; i++) {
      const b = document.getElementById(`sb${i}`);
      if (b && !b.style.height.startsWith('4')) {
        const h = 2 + Math.sin(Date.now() * 0.0018 + i * 0.42) * 1.2;
        b.style.height = `${h}px`;
      }
    }
  }
  requestAnimationFrame(idleSpec);
})();

// ──────────────────────────────────────────
//  RECEIVER
// ──────────────────────────────────────────
const rxSpecCV = $('rxSpecCanvas');
const rxSpecCX = rxSpecCV.getContext('2d');

function resizeRxSpec() {
  rxSpecCV.width  = rxSpecCV.parentElement.offsetWidth  || 600;
  rxSpecCV.height = rxSpecCV.parentElement.offsetHeight || 88;
}
resizeRxSpec();
addEventListener('resize', resizeRxSpec);

function toggleRx() { isRx ? stopRx() : startRx(); }

async function startRx() {
  const micId = $('micSel').value;
  try {
    rxStream = await navigator.mediaDevices.getUserMedia({
      audio: {
        deviceId:         micId ? { exact: micId } : undefined,
        echoCancellation: false, noiseSuppression: false,
        autoGainControl: false, sampleRate: 48000,
      }
    });
  } catch(e) { setRxMsg(`Mic error: ${e.message}`); return; }

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

  $('btnListen').textContent = 'STOP';
  $('btnListen').classList.add('stopping');
  $('rxLed').className = 'led on-rx';
  setRxMsg('Scanning for signal…');
  setRxPhase('IDLE — AWAITING SYNC', 'Listening on selected microphone');

  rxTimer = setInterval(rxTick, 2);
  drawRxSpec();
}

function stopRx() {
  isRx = false;
  clearInterval(rxTimer);   rxTimer = null;
  cancelAnimationFrame(rxRAF); rxRAF = null;
  if (rxStream) { rxStream.getTracks().forEach(t => t.stop()); rxStream = null; }
  if (rxAC)    { rxAC.close().catch(() => {}); rxAC = null; }
  $('btnListen').textContent = 'START LISTENING';
  $('btnListen').classList.remove('stopping');
  $('rxLed').className = 'led';
  setRxMsg('Stopped');
}

function resetRxState() {
  rxPhase     = 'IDLE';
  rxSyncDet   = 0;
  rxSyncGone  = 0;
  rxHdrStart  = 0;
  rxHdrFreqs  = [];
  rxHdrGone   = 0;
  rxDetCFG    = null;
  rxDataStart = 0;
  rxLastPx    = -1;
  rxPixels    = [];
  rxPxCnt     = 0;
}

function clearRx() {
  resetRxState();
  setRxPhase('IDLE — AWAITING SYNC', 'Cleared');
  setRxMsg('Cleared');
  $('rxPixelCount').textContent = '0 px';
  $('imgOutput').className = 'img-output';
  $('autoDetail').textContent = 'Awaiting header…';
  const rc = $('rxCanvas');
  rc.getContext('2d').clearRect(0, 0, rc.width, rc.height);
  rc.style.display = 'none';
}

// ── Manual override ──
function toggleManual() {
  const body = $('manualBody');
  const sec  = body.parentElement;
  const open = !body.classList.contains('hidden');
  body.classList.toggle('hidden', open);
  sec.classList.toggle('open', !open);
  $('manualChevron').textContent = open ? '▾' : '▴';
}

function applyManual() {
  const sz  = parseInt($('manSize').value);
  const tm  = parseInt($('manTone').value);

  if (!sz || sz < 1 || sz > 6000) {
    $('manualStatus').textContent = '⚠ Enter a size between 1 and 6000';
    $('manualStatus').classList.remove('active');
    return;
  }
  if (!tm || tm < 1 || tm > 200) {
    $('manualStatus').textContent = '⚠ Enter a tone duration between 1 and 200';
    $('manualStatus').classList.remove('active');
    return;
  }

  rxManCFG = { resolution: sz, timeMs: tm };

  // If we're currently in DATA or DONE phase, apply immediately by resetting data
  if (rxPhase === 'DATA' || rxPhase === 'HDR') {
    rxDetCFG    = { ...rxManCFG };
    rxDataStart = performance.now();
    rxLastPx    = -1;
    rxPixels    = [];
    rxPxCnt     = 0;
    setupRxCanvas(sz);
    setRxPhase(`RECEIVING — ${sz}×${sz}`, `Manual · ${tm}ms/px`);
    setRxMsg(`Receiving ${(sz*sz).toLocaleString()} pixels…`);
    $('imgOutput').classList.remove('has-img');
  }

  $('manualStatus').textContent = `✓ Set: ${sz}×${sz} px · ${tm}ms/tone — will use on next sync or now`;
  $('manualStatus').classList.add('active');
  $('autoDetail').textContent   = `Manual: ${sz}×${sz} · ${tm}ms`;
}

// ── FFT helpers ──
function refreshFD() { rxAna.getByteFrequencyData(rxFD); }

function peakIn(fLo, fHi) {
  const b0 = Math.max(0, Math.floor(fLo / rxFR));
  const b1 = Math.min(rxFD.length - 1, Math.ceil(fHi / rxFR));
  let maxM = 0, maxB = b0;
  for (let i = b0; i <= b1; i++) { if (rxFD[i] > maxM) { maxM = rxFD[i]; maxB = i; } }
  return { freq: maxB * rxFR, mag: maxM };
}

function median(arr) {
  if (!arr.length) return (P.FREQ_LO + P.FREQ_HI) / 2;
  const s = [...arr].sort((a,b)=>a-b), m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m-1] + s[m]) / 2;
}

// ── State machine ──
function rxTick() {
  if (!rxAna) return;
  const now = performance.now();
  refreshFD();

  // ── IDLE: wait for sync ──
  if (rxPhase === 'IDLE') {
    const pk = peakIn(P.SYNC_F - 40, P.SYNC_F + 40);
    if (pk.mag > P.SYNC_TH) {
      if (!rxSyncDet) rxSyncDet = now;
      if (now - rxSyncDet > 80) {
        rxPhase = 'SYNC';
        rxSyncGone = 0;
        setRxPhase('SYNC DETECTED', 'Carrier locked — awaiting header tone');
        setRxMsg('Sync tone active');
      }
    } else { rxSyncDet = 0; }
    return;
  }

  // ── SYNC: wait for sync to end ──
  if (rxPhase === 'SYNC') {
    const pk = peakIn(P.SYNC_F - 40, P.SYNC_F + 40);
    if (pk.mag < P.SYNC_TH - 12) {
      if (!rxSyncGone) rxSyncGone = now;
      if (now - rxSyncGone > 30) {
        rxPhase    = 'HDR';
        rxHdrStart = 0;
        rxHdrFreqs = [];
        rxHdrGone  = 0;
        setRxPhase('READING HEADER', 'Measuring frequency & duration of header tone');
        setRxMsg('Header in progress…');
      }
    } else { rxSyncGone = 0; }
    return;
  }

  // ── HDR: detect single header tone, measure freq + duration ──
  if (rxPhase === 'HDR') {
    const pk = peakIn(P.FREQ_LO - 30, P.FREQ_HI + 30);

    if (!rxHdrStart) {
      // Waiting for header tone to begin
      if (pk.mag > P.HDR_TH) {
        rxHdrStart = now;
        rxHdrFreqs = [pk.freq];
      }
    } else {
      // Header tone is in progress
      if (pk.mag > P.HDR_TH) {
        // Still active — collect samples
        rxHdrGone = 0;
        rxHdrFreqs.push(pk.freq);
      } else {
        // Maybe ending — debounce
        if (!rxHdrGone) rxHdrGone = now;
        if (now - rxHdrGone > 25) {
          // Header tone ended — decode
          const durMs  = rxHdrGone - rxHdrStart;
          const medF   = median(rxHdrFreqs);
          const detRes = freq2res(medF);
          const detTm  = hdrDur2ms(durMs);

          // Prefer manual config if set
          const useCFG = rxManCFG
            ? { ...rxManCFG }
            : { resolution: detRes, timeMs: clamp(detTm, 1, 200) };

          rxDetCFG  = useCFG;
          buildPalette(CFG.nColors);  // use current palette (color count not in header)
          setupRxCanvas(useCFG.resolution);

          rxPhase     = 'DATA';
          rxDataStart = now + P.PRE_GAP;   // data starts after pre-gap
          rxLastPx    = -1;

          const lbl = rxManCFG
            ? `${useCFG.resolution}×${useCFG.resolution} (manual) · ${useCFG.timeMs}ms`
            : `${useCFG.resolution}×${useCFG.resolution} · ${useCFG.timeMs}ms/px`;
          setRxPhase(`RECEIVING — ${useCFG.resolution}×${useCFG.resolution}`, lbl);
          setRxMsg(`Receiving ${(useCFG.resolution * useCFG.resolution).toLocaleString()} pixels…`);
          $('autoDetail').textContent = lbl;
        }
      }
    }
    return;
  }

  // ── DATA: receive pixel tones ──
  if (rxPhase === 'DATA') {
    const cfg     = rxDetCFG;
    const period  = cfg.timeMs + P.PX_GAP;
    const elapsed = now - rxDataStart;
    if (elapsed < 0) return;  // still in pre-gap

    // Check for end tone (above data band)
    const endPk = peakIn(P.END_F - 150, P.END_F + 150);
    if (endPk.mag > P.END_TH && endPk.freq > 5200) { finishRxData(); return; }

    const total   = cfg.resolution * cfg.resolution;
    const pxIdx   = Math.floor(elapsed / period);
    const pxOff   = elapsed % period;
    const lo      = cfg.timeMs * 0.25;
    const hi      = cfg.timeMs * 0.76;

    if (pxOff >= lo && pxOff <= hi && pxIdx !== rxLastPx && pxIdx < total) {
      rxLastPx = pxIdx;
      const pk = peakIn(P.FREQ_LO - 50, P.FREQ_HI + 50);
      if (pk.mag > P.DATA_TH) {
        const ci = freq2idx(pk.freq, CFG.nColors);
        rxPixels[pxIdx] = ci;
        drawRxPixel(pxIdx, ci, cfg.resolution);
        rxPxCnt++;
        $('rxPixelCount').textContent = `${rxPxCnt} / ${total.toLocaleString()} px`;
      }
    }
    if (pxIdx >= total) finishRxData();
  }
}

function finishRxData() {
  rxPhase = 'DONE';
  const total = rxDetCFG ? rxDetCFG.resolution ** 2 : 0;
  setRxPhase('COMPLETE ✓', `${rxPxCnt.toLocaleString()} of ${total.toLocaleString()} pixels received`);
  setRxMsg(`Done — ${rxPxCnt.toLocaleString()} px received`);
  $('imgOutput').classList.add('has-img');
}

function setupRxCanvas(res) {
  const rc = $('rxCanvas');
  rc.width = rc.height = res;
  const rcx = rc.getContext('2d');
  rcx.fillStyle = '#060B18';
  rcx.fillRect(0, 0, res, res);
  rc.style.display = 'block';
}

function drawRxPixel(idx, ci, res) {
  const rc = $('rxCanvas');
  const [r, g, b] = palette[ci] || [0, 0, 0];
  const ctx = rc.getContext('2d');
  ctx.fillStyle = `rgb(${r},${g},${b})`;
  ctx.fillRect(idx % res, Math.floor(idx / res), 1, 1);
}

function saveImg() {
  const rc = $('rxCanvas');
  Object.assign(document.createElement('a'), {
    download: `audiopix_${Date.now()}.png`,
    href: rc.toDataURL('image/png'),
  }).click();
}

function setRxMsg(m)          { $('rxStatus').textContent   = m; }
function setRxPhase(lbl, sub) { $('rxPhaseLabel').textContent = lbl; $('rxPhaseSub').textContent = sub || ''; }

// RX spectrum drawing
function drawRxSpec() {
  if (!isRx || !rxAna) return;
  rxAna.getByteFrequencyData(rxFD);
  const W = rxSpecCV.width, H = rxSpecCV.height;
  rxSpecCX.fillStyle = 'rgba(0,0,0,0.4)';
  rxSpecCX.fillRect(0, 0, W, H);

  const maxF  = 6600;
  const maxB  = Math.floor(maxF / rxFR);
  const nBars = Math.min(maxB, Math.floor(W / 1.5));
  const bw    = W / nBars;
  const nc    = CFG.nColors;

  for (let i = 0; i < nBars; i++) {
    const bin  = Math.floor(i * maxB / nBars);
    const mag  = rxFD[Math.min(bin, rxFD.length - 1)];
    const bh   = (mag / 255) * H;
    const freq = bin * rxFR;

    let col;
    if (Math.abs(freq - P.SYNC_F) < 42) {
      col = `rgba(80,200,255,${0.5 + mag/512})`;
    } else if (freq > 5200 && freq < 5800) {
      col = `rgba(200,80,255,${0.45 + mag/512})`;
    } else if (freq >= P.FREQ_LO && freq <= P.FREQ_HI) {
      const ci = freq2idx(freq, nc);
      const [r, g, b] = palette[ci] || [0, 200, 200];
      col = `rgba(${r},${g},${b},${0.55 + mag/640})`;
    } else {
      col = `rgba(0,212,200,${0.10 + mag/1400})`;
    }
    rxSpecCX.fillStyle = col;
    rxSpecCX.fillRect(~~(i * bw), H - bh, Math.max(1, bw - 0.5), bh);
  }
  rxRAF = requestAnimationFrame(drawRxSpec);
}

// ──────────────────────────────────────────
//  CONTROLS POPUP
// ──────────────────────────────────────────
function openControls() {
  PND.resolution = CFG.resolution;
  PND.nColors    = CFG.nColors;
  PND.timeMs     = CFG.timeMs;
  $('colSlider').value = CFG.nColors;
  $('resSlider').value = resToSlider(CFG.resolution);
  $('tmSlider').value  = CFG.timeMs;
  updatePopup();
  $('overlay').classList.remove('hidden');
}

function closeControls() { $('overlay').classList.add('hidden'); }

function overlayClick(e) { if (e.target === $('overlay')) closeControls(); }

function applySettings() {
  CFG.resolution = PND.resolution;
  CFG.nColors    = PND.nColors;
  CFG.timeMs     = PND.timeMs;
  buildPalette(CFG.nColors);
  if (origImg) processImage(origImg, CFG.resolution, CFG.nColors);
  refreshPalStrip(CFG.nColors);
  updateBadge();
  closeControls();
}

function sliderToRes(v) { return Math.max(1, Math.min(6000, Math.round(Math.pow(6000, v / 100)))); }
function resToSlider(r) { return Math.round(Math.log(Math.max(1, r)) / Math.log(6000) * 100); }

function onColChange(v) { PND.nColors    = parseInt(v);             updatePopup(); }
function onResChange(v) { PND.resolution = sliderToRes(parseFloat(v)); updatePopup(); }
function onTmChange(v)  { PND.timeMs     = parseInt(v);             updatePopup(); }

function updatePopup() {
  const { resolution: res, nColors: nc, timeMs: tm } = PND;

  $('colVal').textContent = `${nc}`;
  $('resVal').textContent = `${res}×${res}`;
  $('tmVal').textContent  = `${tm}ms`;

  // Palette swatch
  buildPalette(nc);
  const pp = $('palPreview');
  pp.innerHTML = '';
  palette.forEach(([r,g,b]) => {
    const s = document.createElement('div');
    s.className = 'pal-swatch';
    s.style.background = `rgb(${r},${g},${b})`;
    pp.appendChild(s);
  });

  // Res grid
  const rg = $('resGrid');
  const n  = Math.min(res, 14);
  rg.style.gridTemplateColumns = `repeat(${n},1fr)`;
  rg.innerHTML = '';
  for (let i = 0; i < n * n; i++) {
    const d = document.createElement('div');
    d.className = 'res-grid-cell';
    d.style.background = `hsl(${(i*137.508)%360},60%,${30+(i%5)*10}%)`;
    rg.appendChild(d);
  }
  $('resStats').textContent = `${(res*res).toLocaleString()} pixels`;

  // Speed bar
  $('speedFill').style.width = `${(tm / 200) * 100}%`;
  $('speedLabel').textContent =
    tm <=  8 ? 'Ultrafast' : tm <= 20 ? 'Fast' :
    tm <= 60 ? 'Normal'    : tm <=120 ? 'Slow' : 'Very slow';

  // Estimate
  const { pixels, syncMs, hdrMs, dataMs, endMs, total } = calcEst(res, nc, tm);

  $('estPx').textContent    = pixels.toLocaleString();
  $('estHdr').textContent   = fmtTime(syncMs + hdrMs);
  $('estTotal').textContent = fmtTime(total);

  $('estNote').textContent =
    total > 18000000 ? '⚠ Multi-hour transfer!'  :
    total >  3600000 ? '⏳ Hours to complete'     :
    total >   600000 ? '☕ Coffee break needed'   :
    total >    60000 ? '⏱ Under ' + Math.ceil(total/60000) + ' min' :
    total >    10000 ? '⚡ Under a minute'        :
                       '🚀 Super fast!';

  // Timeline (flex proportions)
  if (total > 0) {
    $('etlSync').style.flex = syncMs;
    $('etlHdr').style.flex  = hdrMs;
    $('etlData').style.flex = dataMs;
    $('etlEnd').style.flex  = endMs;
  }
}

function refreshPalStrip(n) {
  buildPalette(n);
  const strip = $('palStripTx');
  strip.innerHTML = '';
  palette.forEach(([r,g,b]) => {
    const s = document.createElement('div');
    s.className = 'pal-sw';
    s.style.background = `rgb(${r},${g},${b})`;
    strip.appendChild(s);
  });
  $('palCountTx').textContent = `${n} colors`;
}

function updateBadge() {
  $('settingsBadge').textContent = `${CFG.resolution}px · ${CFG.nColors}c · ${CFG.timeMs}ms`;
}

// ──────────────────────────────────────────
//  INIT
// ──────────────────────────────────────────
buildPalette(CFG.nColors);
buildSpecBars();
refreshPalStrip(CFG.nColors);
updateBadge();
updatePopup();
enumDevices();
