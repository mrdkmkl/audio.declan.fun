'use strict';
/* ════════════════════════════════════════════════════════════
   AUDIOPIX — app.js  (Pairing + Modes Edition)

   PROTOCOL:
     1. START TONE  — SYNC_F for SYNC_MS (begin signal)
     2. PRE-GAP     — PRE_GAP ms silence
     3. PIXEL DATA  — n*n tones, each timeMs long, gapped by PX_GAP ms
     4. END TONE    — END_F for END_MS
     5. RESUME TONE — SYNC_F for RESUME_MS (after TX-side pause)

   All parameters (size, colors, tone speed, mode) are exchanged via
   a 9-character transfer code (XXXX-XXXX-X).

   PAIRING — BroadcastChannel on the same device:
     TX opens channel `audiopix-<code>` and announces itself.
     RX joins the same channel when the code is entered.
     Both sides send real-time state messages so:
       • RX pause → TX auto-pauses
       • TX progress → shown live on RX panel
       • TX start/stop/done → shown on RX
       • RX done → shown on TX

   MODES (encoded in code):
     B&W Mode   — 2-color black/white, fastest
     Low Pitch  — 100–700 Hz band, max 20 colors, quieter
═════════════════════════════════════════════════════════════ */

// ──────────────────────────────────────────
//  FREQUENCY BANDS
// ──────────────────────────────────────────
const BAND_NORMAL = {
  SYNC_F:   180, SYNC_TH:  55, SYNC_W: 40,
  FREQ_LO:  600, FREQ_HI: 4500,
  END_F:   5500, END_TH:   45, END_W: 150,
  DATA_TH:   28,
  RESUME_F:  180,
};
const BAND_LP = {
  SYNC_F:    55, SYNC_TH:  50, SYNC_W: 20,
  FREQ_LO:  100, FREQ_HI:  700,
  END_F:    900, END_TH:   40, END_W: 100,
  DATA_TH:   24,
  RESUME_F:  55,
};

// ──────────────────────────────────────────
//  PROTOCOL TIMING
// ──────────────────────────────────────────
const P = {
  SYNC_MS:   400,   // ms — start tone duration (clearly detectable)
  RESUME_MS: 250,   // ms — resume-after-pause marker
  END_MS:    500,   // ms — end marker (longer = reliable detection)
  PX_GAP:      5,   // ms — silence gap between pixel tones
  PRE_GAP:   500,   // ms — silence AFTER start tone, BEFORE first pixel (sync window)
  ATT:       0.004, // s  — tone attack
  REL:       0.004, // s  — tone release
  LOOKAHEAD: 0.12,  // s  — schedule this far ahead
  SCHED_INT:  20,   // ms — scheduler poll interval
};

// ──────────────────────────────────────────
//  CONFIG
// ──────────────────────────────────────────
const CFG = { resolution: 32, nColors: 124, timeMs: 50, bw: false, lowPitch: false };
const PND = { ...CFG };

// Active band — updated when mode changes
let BD = BAND_NORMAL;

function updateBand() { BD = CFG.lowPitch ? BAND_LP : BAND_NORMAL; }

// ──────────────────────────────────────────
//  STATE
// ──────────────────────────────────────────
let mode    = 'tx';
let palette = [];
let txPixels    = null;
let origImg     = null;
let isTx        = false;
let txAC        = null;
let txOsc       = null;
let txGainNode  = null;
let txMaster    = null;
let txCurrentPx = 0;
let txSchedTime = 0;
let txDataAnchorAC = 0;
let txPaused    = false;
let txSchedTimer = null;
let curTxFreq   = 0;

let isRx        = false;
let rxAC        = null;
let rxStream    = null;
let rxAna       = null;
let rxFD        = null;
let rxFR        = 1;
let rxTimer     = null;
let rxRAF       = null;

let rxPhase          = 'IDLE';
let rxSyncDet        = 0;
let rxSyncGone       = 0;
let rxDetCFG         = null;
let rxDataStart      = 0;
let rxLastPx         = -1;
let rxPixels         = [];
let rxPxCnt          = 0;
let rxUserPaused     = false;
let rxPauseAnchor    = 0;
let rxTxPaused       = false;
let rxLastSig        = 0;
let rxResumeSyncStart = 0;
let rxResumeSyncGone  = 0;

// Code / pairing
let rxCode = null;           // decoded from entered code
let pairCh = null;           // BroadcastChannel
let pairConnected = false;
let pairRxPaused  = false;   // TX side: RX told us it paused
let mirrorPx      = 0;
let mirrorTotal   = 0;
let mirrorStatusStr = 'IDLE';
let pairBcastTimer = null;   // throttled TX progress broadcast

// ──────────────────────────────────────────
//  HELPERS
// ──────────────────────────────────────────
const $ = id => document.getElementById(id);
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

function idx2freq(i, n) { return BD.FREQ_LO + (i / Math.max(n - 1, 1)) * (BD.FREQ_HI - BD.FREQ_LO); }
function freq2idx(f, n) { return clamp(Math.round((f - BD.FREQ_LO) / (BD.FREQ_HI - BD.FREQ_LO) * (n - 1)), 0, n - 1); }

function fmtTime(ms) {
  if (ms < 1000) return `${ms.toFixed(0)} ms`;
  if (ms < 60000) return `${(ms / 1000).toFixed(1)} s`;
  const m = Math.floor(ms / 60000), s = Math.floor((ms % 60000) / 1000);
  if (ms < 3600000) return s ? `${m}m ${s}s` : `${m}m`;
  const h = Math.floor(ms / 3600000), rm = Math.floor((ms % 3600000) / 60000);
  return rm ? `${h}h ${rm}m` : `${h}h`;
}

// ──────────────────────────────────────────
//  CODE SYSTEM
//  Format: XXXX-XXXX-X  (9 alphanum + 2 dashes)
//
//  g1 (4): resolution - 1,  range 0–5999
//  g2 (4): flags * 14000 + ncIdx * 200 + tmIdx
//    flags  = (lowPitch?1:0)|(bw?2:0),  0–3
//    ncIdx  = round((nc-4)/4) when bw=0, 0 when bw=1
//             nc range: 2–300 → ncIdx 0–74
//    tmIdx  = tm - 1,  0–199
//    max g2 = 3*14000 + 74*200 + 199 = 42000+14800+199 = 56999 < 36^4=1679616 ✓
//  g3 (1): checksum = Σ base36 values of g1+g2 chars mod 36
// ──────────────────────────────────────────
function encodeCode(res, nc, tm, bw, lp) {
  const g1    = (res - 1).toString(36).toUpperCase().padStart(4, '0');
  const flags = (lp ? 1 : 0) | (bw ? 2 : 0);
  const ncIdx = bw ? 0 : Math.round(Math.max(0, (clamp(nc, 4, 300) - 4)) / 4);
  const tmIdx = clamp(tm - 1, 0, 199);
  const g2    = (flags * 14000 + ncIdx * 200 + tmIdx).toString(36).toUpperCase().padStart(4, '0');
  let cs = 0;
  for (const c of g1 + g2) cs += parseInt(c, 36);
  const g3 = (cs % 36).toString(36).toUpperCase();
  return `${g1}-${g2}-${g3}`;
}

function decodeCode(raw) {
  const clean = raw.replace(/[-\s]/g, '').toUpperCase();
  if (clean.length !== 9) return null;
  if (!/^[0-9A-Z]{9}$/.test(clean)) return null;
  const g1 = clean.slice(0, 4), g2 = clean.slice(4, 8), g3 = clean.slice(8, 9);
  let cs = 0;
  for (const c of g1 + g2) cs += parseInt(c, 36);
  if ((cs % 36).toString(36).toUpperCase() !== g3) return null;

  const res   = parseInt(g1, 36) + 1;
  const g2v   = parseInt(g2, 36);
  const flags = Math.floor(g2v / 14000);
  const rem   = g2v % 14000;
  const ncIdx = Math.floor(rem / 200);
  const tmIdx = rem % 200;
  const lp    = (flags & 1) !== 0;
  const bw    = (flags & 2) !== 0;
  const nc    = bw ? 2 : clamp(ncIdx * 4 + 4, 4, 300);
  const tm    = tmIdx + 1;

  if (res < 1 || res > 6000 || nc < 2 || nc > 300 || tm < 1 || tm > 200) return null;
  return { resolution: res, nColors: nc, timeMs: tm, bw, lowPitch: lp };
}

function describeCode(d) {
  const parts = [];
  if (d.bw) parts.push('B&W');
  if (d.lowPitch) parts.push('Low Pitch');
  return `${d.resolution}×${d.resolution} · ${d.bw ? '2 colors (B&W)' : d.nColors + ' colors'} · ${d.timeMs}ms/tone` +
         (parts.length ? ' · ' + parts.join(' + ') : '');
}

function updateTxCode() {
  const code = encodeCode(CFG.resolution, CFG.nColors, CFG.timeMs, CFG.bw, CFG.lowPitch);
  $('txCodeDisplay').textContent = code;
  if ($('settingsCodeVal')) {
    $('settingsCodeVal').textContent = code;
    $('settingsCodeDesc').textContent = describeCode(CFG);
  }
  // Reopen pair channel on new code
  openPairChannel(code);
}

async function copyCode() {
  const code = $('txCodeDisplay').textContent;
  if (!code || code === '—') return;
  try { await navigator.clipboard.writeText(code); } catch(_) {
    const el = Object.assign(document.createElement('textarea'), { value: code });
    document.body.appendChild(el); el.select(); document.execCommand('copy'); el.remove();
  }
  const btn = $('btnCopyCode');
  btn.classList.add('copied'); btn.textContent = '✓ COPIED';
  setTimeout(() => {
    btn.classList.remove('copied');
    btn.innerHTML = `<svg viewBox="0 0 14 14" fill="none" width="11" height="11"><rect x="1" y="4" width="9" height="9" rx="1.5" stroke="currentColor" stroke-width="1.3"/><path d="M4 4V2.5A1.5 1.5 0 0 1 5.5 1H11.5A1.5 1.5 0 0 1 13 2.5V8.5A1.5 1.5 0 0 1 11.5 10H10" stroke="currentColor" stroke-width="1.3" stroke-linecap="round"/></svg> COPY`;
  }, 1600);
}

// ──────────────────────────────────────────
//  PAIR CHANNEL  (BroadcastChannel, same device)
// ──────────────────────────────────────────
function openPairChannel(code) {
  if (pairCh) { pairCh.close(); pairCh = null; }
  pairConnected = false; pairRxPaused = false;
  updatePairUI();
  try {
    pairCh = new BroadcastChannel('audiopix-' + code.replace(/-/g, ''));
    pairCh.onmessage = handlePairMsg;
    // Announce ourselves
    if (mode === 'tx') pairSend({ t: 'tx-hello', cfg: { res: CFG.resolution, nc: CFG.nColors, tm: CFG.timeMs, bw: CFG.bw, lp: CFG.lowPitch }, txing: isTx, px: txCurrentPx, total: txPixels?.length || 0 });
    else               pairSend({ t: 'rx-hello' });
  } catch(e) { pairCh = null; }
}

function pairSend(msg) { if (pairCh) try { pairCh.postMessage(msg); } catch(_) {} }

function handlePairMsg(e) {
  const msg = e.data;

  if (mode === 'tx') {
    // ── TX receives messages from RX ──
    if (msg.t === 'rx-hello' || msg.t === 'rx-ready') {
      pairConnected = true; pairRxPaused = false;
      pairSend({ t: 'tx-hello', cfg: { res: CFG.resolution, nc: CFG.nColors, tm: CFG.timeMs, bw: CFG.bw, lp: CFG.lowPitch }, txing: isTx, px: txCurrentPx, total: txPixels?.length || 0 });
      updatePairUI();
    }
    if (msg.t === 'rx-pause' && isTx && !txPaused) {
      pairRxPaused = true;
      pauseTx(true);
      updatePairUI();
    }
    if (msg.t === 'rx-resume' && isTx && txPaused && pairRxPaused) {
      pairRxPaused = false;
      resumeTx(true);
      updatePairUI();
    }
    if (msg.t === 'rx-done') {
      if (isTx) {
        // RX finished but TX is still going — something went wrong (timing drift, missed tones)
        showTxError(`RX finished early at pixel ${(msg.px || 0).toLocaleString()} — TX still has ${(txPixels.length - txCurrentPx).toLocaleString()} pixels left. Try increasing Tone Duration in Settings.`);
      }
      updatePairUI('RX DONE ✓');
    }
  } else {
    // ── RX receives messages from TX ──
    if (msg.t === 'tx-hello') {
      pairConnected = true;
      pairSend({ t: 'rx-hello' });
      updatePairUI();
      // Restore mirror
      mirrorTotal = msg.total || 0;
      mirrorPx    = msg.px   || 0;
      if (msg.txing) {
        showMirror('TRANSMITTING', mirrorPx, mirrorTotal);
      } else {
        showMirror('IDLE', 0, mirrorTotal);
      }
    }
    if (msg.t === 'tx-start') {
      mirrorTotal = msg.total || 0; mirrorPx = 0;
      showMirror('TRANSMITTING', 0, mirrorTotal);
      // Auto-start RX when TX begins — if paired and code is set
      if (rxCode && !isRx) startRx();
    }
    if (msg.t === 'tx-progress') {
      mirrorPx = msg.px; mirrorTotal = msg.total;
      showMirror(mirrorStatusStr === 'PAUSED' ? 'PAUSED' : 'TRANSMITTING', mirrorPx, mirrorTotal);
    }
    if (msg.t === 'tx-pause') {
      mirrorStatusStr = 'PAUSED';
      showMirror('PAUSED', mirrorPx, mirrorTotal);
    }
    if (msg.t === 'tx-resume') {
      mirrorStatusStr = 'TRANSMITTING';
      showMirror('TRANSMITTING', mirrorPx, mirrorTotal);
    }
    if (msg.t === 'tx-done') {
      mirrorStatusStr = 'COMPLETE';
      mirrorPx = mirrorTotal;
      showMirror('COMPLETE ✓', mirrorPx, mirrorTotal);
    }
    if (msg.t === 'tx-stop') {
      mirrorStatusStr = 'STOPPED';
      showMirror('STOPPED', mirrorPx, mirrorTotal);
    }
  }
}

function showMirror(status, px, total) {
  mirrorStatusStr = status;
  const el = $('txMirror');
  el.classList.remove('hidden');
  const chip = $('mirrorChip');
  chip.textContent = status;
  chip.className = 'mirror-status-chip' +
    (status === 'TRANSMITTING' ? ' chip-tx' :
     status.includes('PAUSE') ? ' chip-pau' :
     status.includes('COMPLETE') ? ' chip-ok' : '');
  const pct = total > 0 ? clamp(px / total, 0, 1) : 0;
  $('mirrorFill').style.width = `${(pct * 100).toFixed(1)}%`;
  $('mirrorDetail').textContent = total > 0
    ? `${px.toLocaleString()} / ${total.toLocaleString()} px (${Math.round(pct * 100)}%)`
    : 'Waiting for transmission…';
}

function updatePairUI(overrideLabel) {
  // TX pair row
  const txDot   = $('txPairDot');
  const txLabel = $('txPairLabel');
  const txChip  = $('txPairChip');

  if (mode === 'tx') {
    if (pairConnected) {
      txDot.className   = 'pair-dot connected' + (pairRxPaused ? ' rx-paused-dot' : '');
      txLabel.className = 'pair-status-label' + (pairRxPaused ? ' rx-paused-lbl' : ' paired');
      txLabel.textContent = overrideLabel || (pairRxPaused ? 'Receiver paused — TX auto-paused' : 'PAIRED · Receiver connected');
      txChip.className  = 'pair-chip' + (pairRxPaused ? ' warn-chip' : ' show-chip');
      txChip.textContent = pairRxPaused ? 'RX PAUSED' : 'SYNCED';
    } else {
      txDot.className   = 'pair-dot';
      txLabel.className = 'pair-status-label';
      txLabel.textContent = 'Waiting for receiver…';
      txChip.className  = 'pair-chip';
      txChip.textContent = '';
    }
  }

  // RX pair row
  const rxDot   = $('rxPairDot');
  const rxLabel = $('rxPairLabel');
  const rxChip  = $('rxPairChip');
  if (!rxDot) return;

  if (pairConnected) {
    rxDot.className   = 'pair-dot connected';
    rxLabel.className = 'pair-status-label paired';
    rxLabel.textContent = 'PAIRED · Transmitter connected';
    rxChip.className  = 'pair-chip show-chip';
    rxChip.textContent = 'SYNCED';
  } else {
    rxDot.className   = 'pair-dot';
    rxLabel.className = 'pair-status-label';
    rxLabel.textContent = 'Waiting for transmitter…';
    rxChip.className  = 'pair-chip';
    rxChip.textContent = '';
  }
}

// Start throttled TX progress broadcast
function startPairBcast() {
  stopPairBcast();
  pairBcastTimer = setInterval(() => {
    if (pairConnected && isTx) {
      pairSend({ t: 'tx-progress', px: txCurrentPx, total: txPixels?.length || 0 });
    }
  }, 350);
}
function stopPairBcast() { clearInterval(pairBcastTimer); pairBcastTimer = null; }

// ──────────────────────────────────────────
//  CODE ENTRY POPUP
// ──────────────────────────────────────────
function showCodeEntry() {
  $('codeInput').value = '';
  $('codeInputStatus').textContent = '';
  $('codeInputStatus').className   = 'code-input-status';
  $('codeInput').className         = 'code-input';
  $('codeDecodedPreview').className = 'code-decoded-preview';
  $('codeOverlay').classList.remove('hidden');
  setTimeout(() => $('codeInput').focus(), 200);
}
function closeCodeEntry() { $('codeOverlay').classList.add('hidden'); }
function codeOverlayClick(e) { if (e.target === $('codeOverlay')) closeCodeEntry(); }

function formatCodeInput(el) {
  let v = el.value.replace(/[^0-9A-Za-z]/g, '').toUpperCase().slice(0, 9);
  let out = '';
  for (let i = 0; i < v.length; i++) { if (i === 4 || i === 8) out += '-'; out += v[i]; }
  el.value = out;

  const dec = decodeCode(v);
  if (v.length === 9) {
    if (dec) {
      el.className = 'code-input valid';
      $('codeInputStatus').textContent = '✓ Valid code';
      $('codeInputStatus').className   = 'code-input-status ok';
      $('codeDecodedPreview').innerHTML = describeCode(dec).replace(/ · /g, ' &nbsp;·&nbsp; ');
      $('codeDecodedPreview').className = 'code-decoded-preview visible';
    } else {
      el.className = 'code-input invalid';
      $('codeInputStatus').textContent = '✗ Invalid code — check and try again';
      $('codeInputStatus').className   = 'code-input-status err';
      $('codeDecodedPreview').className = 'code-decoded-preview';
    }
  } else {
    el.className = 'code-input';
    $('codeInputStatus').textContent = '';
    $('codeDecodedPreview').className = 'code-decoded-preview';
  }
}

function submitCode() {
  const dec = decodeCode($('codeInput').value);
  if (!dec) {
    $('codeInputStatus').textContent = '✗ Invalid code — check and try again';
    $('codeInputStatus').className   = 'code-input-status err';
    $('codeInput').classList.add('invalid');
    return;
  }
  rxCode = dec;
  // Apply decoded config to BD
  const savedLp = dec.lowPitch;
  BD = savedLp ? BAND_LP : BAND_NORMAL;
  buildPalette(dec.nColors, dec.bw);

  $('rxCodeVal').textContent = $('codeInput').value.toUpperCase();
  setRxMsg(`Paired — ${describeCode(dec)}`);
  setRxPhase('READY', describeCode(dec));

  // Update band frequency labels
  $('rxFreqLo').textContent = BD.FREQ_LO + ' Hz';
  $('rxFreqHi').textContent = BD.FREQ_HI + ' Hz';

  // Show mode tags on RX
  renderModeTags('rxModeTags', dec.bw, dec.lowPitch);

  // Open pair channel
  const code = $('codeInput').value.replace(/[^0-9A-Za-z]/g,'').toUpperCase();
  const formatted = code.slice(0,4)+'-'+code.slice(4,8)+'-'+code.slice(8,9);
  openPairChannel(formatted);

  closeCodeEntry();
}

// ──────────────────────────────────────────
//  MODE TAGS
// ──────────────────────────────────────────
function renderModeTags(elId, bw, lp) {
  const el = $(elId);
  if (!el) return;
  el.innerHTML = '';
  if (bw) {
    const t = document.createElement('div');
    t.className = 'mode-tag bw-tag';
    t.innerHTML = '◑ &nbsp;BLACK &amp; WHITE';
    el.appendChild(t);
  }
  if (lp) {
    const t = document.createElement('div');
    t.className = 'mode-tag lp-tag';
    t.innerHTML = '🔉 &nbsp;LOW PITCH';
    el.appendChild(t);
  }
}

// ──────────────────────────────────────────
//  PALETTE
// ──────────────────────────────────────────
function hsl2rgb(h, s, l) {
  s /= 100; l /= 100;
  const k = n => (n + h / 30) % 12, a = s * Math.min(l, 1 - l);
  const f = n => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
  return [~~(f(0)*255), ~~(f(8)*255), ~~(f(4)*255)];
}

function buildPalette(n, bwOverride) {
  const useBW = bwOverride !== undefined ? bwOverride : CFG.bw;
  palette = [];
  if (useBW) {
    palette = [[10, 10, 12], [242, 242, 248]];
    return;
  }
  // Build chromatic colors then SORT BY HUE so that adjacent palette indices
  // are perceptually similar. This means a small frequency detection error on RX
  // only shifts the color slightly instead of jumping to a random hue.
  // Result: more colors = more coverage = genuinely more accurate image.
  const chromatic = Math.max(0, n - 4);
  const tiers = [[92,20],[85,35],[78,50],[70,65],[62,79]];
  const entries = [];
  for (let i = 0; i < chromatic; i++) {
    const [s, l] = tiers[i % tiers.length];
    const h = (i * 137.508) % 360;          // golden-angle spread for good coverage
    entries.push({ h, rgb: hsl2rgb(h, s, l) });
  }
  entries.sort((a, b) => a.h - b.h);        // sort by hue — key accuracy fix
  entries.forEach(e => palette.push(e.rgb));
  // Neutrals at the end (darkest → lightest = index n-4..n-1)
  palette.push([10,10,12],[80,80,88],[165,165,175],[242,242,248]);
}

function quantize(r, g, b) {
  let best = 0, d = Infinity;
  for (let i = 0; i < palette.length; i++) {
    const [pr,pg,pb] = palette[i];
    const dd = 0.2126*(r-pr)**2 + 0.7152*(g-pg)**2 + 0.0722*(b-pb)**2;
    if (dd < d) { d = dd; best = i; }
  }
  return best;
}

// ──────────────────────────────────────────
//  ESTIMATION
// ──────────────────────────────────────────
function calcEst(res, nc, ms) {
  const pixels  = res * res;
  const startMs = P.SYNC_MS;
  const dataMs  = pixels * (ms + P.PX_GAP);
  const endMs   = P.PRE_GAP + P.END_MS;
  return { pixels, startMs, dataMs, endMs, total: startMs + P.PRE_GAP + dataMs + endMs };
}

// ──────────────────────────────────────────
//  ANIMATED BACKGROUND
// ──────────────────────────────────────────
const bgCV = $('bgCanvas'), bgCX = bgCV.getContext('2d');
let bgT = 0;
function resizeBg() { bgCV.width = innerWidth; bgCV.height = innerHeight; }
resizeBg(); addEventListener('resize', resizeBg);

(function animBg() {
  const W = bgCV.width, H = bgCV.height;
  bgCX.clearRect(0, 0, W, H);
  const colFn = mode === 'tx' ? a => `rgba(255,117,53,${a})` : a => `rgba(0,212,200,${a})`;
  for (let w = 0; w < 8; w++) {
    const ph = bgT * 0.00038 + w * 0.85, amp = 18 + w * 15, fq = 0.0028 + w * 0.0017;
    const yb = H * (0.08 + w * 0.12), env = Math.sin(bgT * 0.00022 + w * 0.44);
    bgCX.beginPath(); bgCX.moveTo(0, yb);
    for (let x = 0; x <= W; x += 3) bgCX.lineTo(x, yb + Math.sin(x * fq + ph) * amp * env);
    bgCX.strokeStyle = colFn(0.018 + w * 0.01); bgCX.lineWidth = 1; bgCX.stroke();
  }
  bgT++; requestAnimationFrame(animBg);
})();

// ──────────────────────────────────────────
//  MODE SWITCHING
// ──────────────────────────────────────────
function setMode(m) {
  mode = m;
  const tx = m === 'tx';
  $('btnTx').className   = 'mode-btn' + (tx  ? ' active-tx' : '');
  $('btnRx').className   = 'mode-btn' + (!tx ? ' active-rx' : '');
  $('txPanel').className = 'panel tx-panel' + (tx  ? '' : ' hidden');
  $('rxPanel').className = 'panel rx-panel' + (!tx ? '' : ' hidden');
  if (!tx && !rxCode) setTimeout(showCodeEntry, 200);
}

// ──────────────────────────────────────────
//  DEVICE ENUMERATION
// ──────────────────────────────────────────
async function enumDevices() {
  try { const t = await navigator.mediaDevices.getUserMedia({audio:true}); t.getTracks().forEach(t=>t.stop()); } catch(_) {}
  const devs = await navigator.mediaDevices.enumerateDevices().catch(() => []);

  const spk = $('spkSel');
  spk.innerHTML = '<option value="">Default Speaker</option>';
  devs.filter(d => d.kind === 'audiooutput').forEach((d, i) => spk.add(new Option(d.label || `Speaker ${i+1}`, d.deviceId)));
  spk.addEventListener('change', () => badge('spkBadge', spk)); badge('spkBadge', spk);

  const mic = $('micSel');
  mic.innerHTML = '';
  devs.filter(d => d.kind === 'audioinput').forEach((d, i) => mic.add(new Option(d.label || `Mic ${i+1}`, d.deviceId)));
  mic.addEventListener('change', () => badge('micBadge', mic)); badge('micBadge', mic);
}

function badge(id, sel) {
  const l = sel.options[sel.selectedIndex]?.text || '—';
  $(id).textContent = l.length > 18 ? l.slice(0, 16) + '…' : l;
}
function onMicChange() { if (isRx) { stopRx(); startRx(); } }

// ──────────────────────────────────────────
//  IMAGE LOADING
// ──────────────────────────────────────────
const dropZone = $('dropZone'), fileInEl = $('fileInput');
const prevCV = $('previewCanvas'), prevCX = prevCV.getContext('2d');

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

// ── Example image (used when no image is loaded) ──
function loadExampleImage() {
  const SIZE = 128;
  const oc = Object.assign(document.createElement('canvas'), { width: SIZE, height: SIZE });
  const cx = oc.getContext('2d');

  // Warm sunset sky gradient
  const sky = cx.createLinearGradient(0, 0, 0, SIZE);
  sky.addColorStop(0,   '#1a0533');
  sky.addColorStop(0.3, '#6b1a6e');
  sky.addColorStop(0.6, '#e8501a');
  sky.addColorStop(0.85,'#f5a623');
  sky.addColorStop(1,   '#ffd47a');
  cx.fillStyle = sky; cx.fillRect(0, 0, SIZE, SIZE);

  // Sun disc
  const sunG = cx.createRadialGradient(64, 80, 0, 64, 80, 24);
  sunG.addColorStop(0, '#fff8c0'); sunG.addColorStop(0.4, '#ffe066'); sunG.addColorStop(1, 'rgba(255,180,0,0)');
  cx.fillStyle = sunG; cx.fillRect(0, 40, SIZE, SIZE);

  // Silhouette hills
  cx.fillStyle = '#0d0820';
  cx.beginPath(); cx.moveTo(0, SIZE);
  cx.quadraticCurveTo(20, 72, 50, 80); cx.quadraticCurveTo(70, 86, 90, 76);
  cx.quadraticCurveTo(110, 68, SIZE, 82); cx.lineTo(SIZE, SIZE); cx.fill();

  // Stars
  for (let i = 0; i < 28; i++) {
    const x = (i * 47.3) % SIZE, y = (i * 31.7) % 55;
    const a = 0.3 + (i % 3) * 0.3;
    cx.fillStyle = `rgba(255,255,255,${a})`;
    cx.fillRect(x, y, 1, 1);
  }

  // Tree silhouettes
  [[12, 92], [22, 86], [100, 88], [112, 94]].forEach(([x, y]) => {
    cx.fillStyle = '#060310';
    cx.beginPath(); cx.moveTo(x, y - 18); cx.lineTo(x - 5, y); cx.lineTo(x + 5, y); cx.fill();
    cx.beginPath(); cx.moveTo(x, y - 26); cx.lineTo(x - 4, y - 14); cx.lineTo(x + 4, y - 14); cx.fill();
  });

  // Foreground water reflection strip
  const ref = cx.createLinearGradient(0, 100, 0, SIZE);
  ref.addColorStop(0, 'rgba(232,80,26,0.35)'); ref.addColorStop(1, 'rgba(20,5,40,0.8)');
  cx.fillStyle = ref; cx.fillRect(0, 100, SIZE, SIZE - 100);

  // Wavy reflection lines
  cx.strokeStyle = 'rgba(245,166,35,0.3)'; cx.lineWidth = 1;
  for (let row = 104; row < SIZE; row += 5) {
    cx.beginPath();
    for (let x = 0; x < SIZE; x++) cx.lineTo(x, row + Math.sin(x * 0.18 + row * 0.4) * 1.5);
    cx.stroke();
  }

  const img = new Image();
  img.onload = () => { origImg = img; renderPreview(img); processImage(img, CFG.resolution, CFG.nColors); };
  img.src = oc.toDataURL();
  setTxMsg('Example image loaded — click TRANSMIT to send');
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
  $('dropInfo').textContent = `${res}×${res} · ${(res*res).toLocaleString()} px · ${CFG.bw ? '2 colors (B&W)' : nc + ' colors'}`;
  if (!$('dropZone').classList.contains('loaded'))
    setTxMsg(`Ready — ${(res*res).toLocaleString()} pixels`);
}

// ──────────────────────────────────────────
//  PREVIEW MODAL
// ──────────────────────────────────────────
function showPreview() {
  if (!txPixels || !origImg) return;
  const res = CFG.resolution, DISP = 240;
  const sc = Math.min(DISP / origImg.width, DISP / origImg.height);
  const ow = Math.round(origImg.width * sc), oh = Math.round(origImg.height * sc);
  const origC = $('origThumb');
  origC.width = ow; origC.height = oh;
  origC.style.cssText = `width:${ow}px;height:${oh}px`;
  origC.getContext('2d').drawImage(origImg, 0, 0, ow, oh);

  const qtC = $('quantThumb');
  qtC.width = res; qtC.height = res;
  const disp = Math.min(DISP, Math.max(80, res * Math.floor(DISP / res)));
  qtC.style.cssText = `width:${disp}px;height:${disp}px`;
  const qtX = qtC.getContext('2d');
  for (let i = 0; i < txPixels.length; i++) {
    const [r,g,b] = palette[txPixels[i]] || [0,0,0];
    qtX.fillStyle = `rgb(${r},${g},${b})`;
    qtX.fillRect(i % res, Math.floor(i / res), 1, 1);
  }
  const est = calcEst(res, CFG.nColors, CFG.timeMs);
  $('prevMeta').textContent = `${res}×${res} px  ·  ${CFG.bw ? '2 colors B&W' : CFG.nColors + ' colors'}  ·  ${CFG.timeMs}ms/tone  ·  ${fmtTime(est.total)} total`;
  $('prevOverlay').classList.remove('hidden');
}
function closePreview()      { $('prevOverlay').classList.add('hidden'); }
function closePrevOverlay(e) { if (e.target === $('prevOverlay')) closePreview(); }

// ──────────────────────────────────────────
//  TRANSMITTER — real-time lookahead scheduler
// ──────────────────────────────────────────
async function handleTransmitClick() {
  if (isTx) { stopTx(); return; }

  // Auto-load example if no image
  if (!origImg) {
    loadExampleImage();
    await new Promise(r => setTimeout(r, 120)); // brief wait for canvas render
  }
  if (!txPixels) return;

  const btn = $('btnTransmit');
  btn.disabled = true; $('btnPreview').disabled = true;
  const pctEl = $('progPct');
  pctEl.textContent = 'READY'; pctEl.classList.add('loading');
  setTxMsg('Processing image…'); $('progDetail').textContent = 'Quantizing…';
  processImage(origImg, CFG.resolution, CFG.nColors);
  await new Promise(r => setTimeout(r, 80));
  pctEl.classList.remove('loading'); btn.disabled = false; $('btnPreview').disabled = false;
  startTx();
}

function startTx() {
  if (!txPixels) return;
  isTx = true; txPaused = false; txCurrentPx = 0;
  $('btnTransmit').textContent = 'STOP TX';
  $('btnTransmit').classList.add('stopping');
  $('btnPauseTx').disabled = false;
  $('btnPauseTx').textContent = '⏸ PAUSE';
  $('btnPauseTx').classList.remove('paused-active');
  $('txLed').className = 'led on-tx';
  setTxMsg('Initialising…');

  pairSend({ t: 'tx-start', total: txPixels.length });
  startPairBcast();
  clearTxError();

  try {
    txAC     = new (window.AudioContext || window.webkitAudioContext)();
    const spkId = $('spkSel').value;
    if (spkId && txAC.setSinkId) txAC.setSinkId(spkId).catch(() => {});

    txMaster = txAC.createGain(); txMaster.gain.value = 0.88; txMaster.connect(txAC.destination);
    txOsc = txAC.createOscillator(); txGainNode = txAC.createGain();
    txOsc.type = 'sine'; txOsc.connect(txGainNode); txGainNode.connect(txMaster);
    txGainNode.gain.setValueAtTime(0, 0); txOsc.start();

    // Schedule start tone then begin real-time scheduler after it + pre-gap
    let t = txAC.currentTime + 0.06;
    schedNote(BD.SYNC_F, t, P.SYNC_MS / 1000, 0.88);
    t += P.SYNC_MS / 1000 + P.PRE_GAP / 1000;
    txDataAnchorAC = t; txSchedTime = t;

    // Start scheduler after start-tone + PRE_GAP has fully elapsed
    txSchedTimer = setTimeout(runScheduler, P.SYNC_MS + P.PRE_GAP + 120);
    startTxSpec(); setTxMsg('Transmitting…');
    trackProgress();
  } catch(err) { setTxMsg(`Error: ${err.message}`); finishTx(false); }
}

function schedNote(freq, t0, durS, vol) {
  const dur = Math.max(P.ATT + P.REL + 0.002, durS);
  txOsc.frequency.setValueAtTime(freq, t0);
  txGainNode.gain.setValueAtTime(0, t0);
  txGainNode.gain.linearRampToValueAtTime(vol, t0 + P.ATT);
  txGainNode.gain.setValueAtTime(vol, t0 + dur - P.REL);
  txGainNode.gain.linearRampToValueAtTime(0, t0 + dur);
}

function runScheduler() {
  if (!isTx || txPaused || !txAC) return;
  const toneS = CFG.timeMs / 1000, gapS = P.PX_GAP / 1000, nc = CFG.nColors;
  const ahead = txAC.currentTime + P.LOOKAHEAD;

  while (txSchedTime < ahead) {
    if (txCurrentPx >= txPixels.length) {
      schedNote(BD.END_F, txSchedTime, P.END_MS / 1000, 0.72);
      const delay = Math.max(50, (txSchedTime - txAC.currentTime + P.END_MS / 1000 + 0.3) * 1000);
      setTimeout(() => finishTx(true), delay);
      txSchedTimer = null; return;
    }
    const freq = CFG.bw
      ? (txPixels[txCurrentPx] === 0 ? BD.FREQ_LO : BD.FREQ_HI)
      : idx2freq(txPixels[txCurrentPx], nc);
    schedNote(freq, txSchedTime, toneS, 0.86);
    txSchedTime += toneS + gapS; txCurrentPx++;
  }
  txSchedTimer = setTimeout(runScheduler, P.SCHED_INT);
}

function togglePauseTx() { txPaused ? resumeTx(false) : pauseTx(false); }

function pauseTx(fromRx = false) {
  if (!isTx || txPaused) return;
  txPaused = true;
  clearTimeout(txSchedTimer); txSchedTimer = null;
  const now = txAC.currentTime + 0.01;
  txGainNode.gain.cancelScheduledValues(now);
  txGainNode.gain.setValueAtTime(0, now);
  txOsc.frequency.cancelScheduledValues(now);
  // Back-calculate real position
  const period = CFG.timeMs / 1000 + P.PX_GAP / 1000;
  const elapsed = txAC.currentTime - txDataAnchorAC;
  txCurrentPx = clamp(Math.floor(elapsed / period), 0, txPixels.length);

  $('btnPauseTx').textContent = '▶ RESUME';
  $('btnPauseTx').classList.add('paused-active');
  $('txLed').className = 'led on-tx paused-led';
  setTxMsg(fromRx ? 'Paused — receiver requested' : 'Paused — press Resume to continue');

  if (!fromRx) pairSend({ t: 'tx-pause' });
  stopPairBcast();
}

function resumeTx(fromRx = false) {
  if (!isTx || !txPaused) return;
  txPaused = false;
  const toneS = CFG.timeMs / 1000, gapS = P.PX_GAP / 1000;
  const period = toneS + gapS;
  const t = txAC.currentTime + 0.05;
  schedNote(BD.SYNC_F, t, P.RESUME_MS / 1000, 0.75);
  // Recalibrate anchor: pixel txCurrentPx starts at t + RESUME_MS + PRE_GAP
  txDataAnchorAC = t + P.RESUME_MS / 1000 + P.PRE_GAP / 1000 - txCurrentPx * period;
  txSchedTime    = t + P.RESUME_MS / 1000 + P.PRE_GAP / 1000;

  $('btnPauseTx').textContent = '⏸ PAUSE';
  $('btnPauseTx').classList.remove('paused-active');
  $('txLed').className = 'led on-tx';
  setTxMsg('Resuming…');

  if (!fromRx) pairSend({ t: 'tx-resume' });
  startPairBcast();
  txSchedTimer = setTimeout(runScheduler, P.RESUME_MS + P.PRE_GAP + 60);
}

function stopTx() {
  isTx = false; txPaused = false;
  clearTimeout(txSchedTimer); txSchedTimer = null;
  if (txOsc) { try { txOsc.stop(); } catch(_) {} txOsc = null; }
  if (txAC)  { txAC.close().catch(() => {}); txAC = null; }
  txGainNode = null; txMaster = null;
  pairSend({ t: 'tx-stop' });
  finishTx(false);
}

function finishTx(ok) {
  isTx = false; txPaused = false; curTxFreq = 0;
  clearTimeout(txSchedTimer); txSchedTimer = null;
  stopPairBcast();
  if (ok) pairSend({ t: 'tx-done', px: txPixels?.length || 0 });
  stopTxSpec();
  if (txAC && ok) { txAC.close().catch(() => {}); txAC = null; }
  $('btnTransmit').textContent = 'TRANSMIT';
  $('btnTransmit').classList.remove('stopping');
  $('btnTransmit').disabled = !txPixels;
  $('btnPreview').disabled = !txPixels;
  $('btnPauseTx').disabled = true;
  $('btnPauseTx').textContent = '⏸ PAUSE';
  $('btnPauseTx').classList.remove('paused-active');
  $('txLed').className = 'led';
  if (!ok) setProgress(0);
}

function trackProgress() {
  if (!isTx) return;
  if (!txPaused) {
    const total = txPixels?.length || 1, cur = clamp(txCurrentPx, 0, total);
    const pct = cur / total;
    setProgress(pct);
    const remMs = Math.max(0, (total - cur) * (CFG.timeMs + P.PX_GAP));
    $('progDetail').textContent = pct < 1
      ? `${cur.toLocaleString()} / ${total.toLocaleString()} px — ${fmtTime(remMs)} left`
      : 'Complete ✓';
    setTxMsg('Transmitting…');
    curTxFreq = cur > 0 && cur < total
      ? (CFG.bw ? (txPixels[cur] === 0 ? BD.FREQ_LO : BD.FREQ_HI) : idx2freq(txPixels[cur], CFG.nColors))
      : (pct === 0 ? BD.SYNC_F : 0);
  }
  requestAnimationFrame(trackProgress);
}

function setProgress(p) {
  $('progFill').style.width = `${Math.round(p * 100)}%`;
  if (!$('progPct').classList.contains('loading'))
    $('progPct').textContent = p > 0 ? `${Math.round(p * 100)}%` : '—';
}
function setTxMsg(m) { $('txStatus').textContent = m; }

// ── TX Error Banner ──
function showTxError(msg) {
  let el = $('txErrorBanner');
  if (!el) {
    el = document.createElement('div');
    el.id = 'txErrorBanner';
    el.className = 'tx-error-banner';
    el.innerHTML = `<span class="err-icon">⚠</span><span class="err-text" id="txErrorText"></span><button class="err-dismiss" onclick="clearTxError()">✕</button>`;
    // Insert after status bar
    const sb = $('txPanel').querySelector('.status-bar');
    sb.parentNode.insertBefore(el, sb.nextSibling);
  }
  $('txErrorText').textContent = msg;
  el.classList.add('visible');
}
function clearTxError() {
  const el = $('txErrorBanner');
  if (el) el.classList.remove('visible');
}

// ──────────────────────────────────────────
//  TX SPECTRUM
// ──────────────────────────────────────────
const N_BARS = 54;
let txSpecRAF = null;

function buildSpecBars() {
  const c = $('specBars'); c.innerHTML = '';
  for (let i = 0; i < N_BARS; i++) {
    const b = document.createElement('div'); b.className = 'spec-bar'; b.id = `sb${i}`; c.appendChild(b);
  }
}

function startTxSpec() {
  function frame() {
    for (let i = 0; i < N_BARS; i++) {
      const f = BD.FREQ_LO + (i / (N_BARS - 1)) * (BD.FREQ_HI - BD.FREQ_LO);
      const dist = Math.abs(f - curTxFreq), span = (BD.FREQ_HI - BD.FREQ_LO) / 7;
      const iten = Math.max(0, 1 - dist / span);
      const h = Math.max(2, iten * 40 + (isTx && !txPaused ? Math.random() * 3 : 0));
      const el = document.getElementById(`sb${i}`);
      if (el) { el.style.height = `${h}px`; el.style.background = `rgba(255,117,53,${0.18 + iten * 0.80})`; }
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

(function idleSpec() {
  if (!isTx) for (let i = 0; i < N_BARS; i++) {
    const b = document.getElementById(`sb${i}`);
    if (b && !b.style.height.startsWith('4')) {
      b.style.height = `${2 + Math.sin(Date.now() * 0.0018 + i * 0.42) * 1.2}px`;
    }
  }
  requestAnimationFrame(idleSpec);
})();

// ──────────────────────────────────────────
//  RECEIVER
// ──────────────────────────────────────────
const rxSpecCV = $('rxSpecCanvas'), rxSpecCX = rxSpecCV.getContext('2d');
function resizeRxSpec() { rxSpecCV.width = rxSpecCV.parentElement.offsetWidth || 600; rxSpecCV.height = rxSpecCV.parentElement.offsetHeight || 88; }
resizeRxSpec(); addEventListener('resize', resizeRxSpec);

function toggleRx() { isRx ? stopRx() : startRx(); }

async function startRx() {
  if (!rxCode) { showCodeEntry(); return; }
  const micId = $('micSel').value;
  try {
    rxStream = await navigator.mediaDevices.getUserMedia({
      audio: { deviceId: micId ? { exact: micId } : undefined, echoCancellation: false, noiseSuppression: false, autoGainControl: false, sampleRate: 48000 }
    });
  } catch(e) { setRxMsg(`Mic error: ${e.message}`); return; }

  rxAC = new (window.AudioContext || window.webkitAudioContext)();
  const src = rxAC.createMediaStreamSource(rxStream);
  rxAna = rxAC.createAnalyser(); rxAna.fftSize = 8192; rxAna.smoothingTimeConstant = 0.0;
  src.connect(rxAna); rxFD = new Uint8Array(rxAna.frequencyBinCount); rxFR = rxAC.sampleRate / rxAna.fftSize;

  isRx = true; rxUserPaused = false; resetRxState();
  clearRxError();
  $('btnListen').textContent = 'STOP'; $('btnListen').classList.add('stopping');
  $('btnPauseRx').disabled = false;
  $('rxLed').className = 'led on-rx';
  setRxMsg('Scanning for start signal…');
  setRxPhase('IDLE — AWAITING START', 'Listening for start tone');

  pairSend({ t: 'rx-ready' });
  rxTimer = setInterval(rxTick, 2); drawRxSpec();
}

function stopRx() {
  isRx = false; rxUserPaused = false;
  clearInterval(rxTimer); rxTimer = null;
  cancelAnimationFrame(rxRAF); rxRAF = null;
  if (rxStream) { rxStream.getTracks().forEach(t => t.stop()); rxStream = null; }
  if (rxAC)    { rxAC.close().catch(() => {}); rxAC = null; }
  $('btnListen').textContent = 'START LISTENING'; $('btnListen').classList.remove('stopping');
  $('btnPauseRx').disabled = true;
  $('btnPauseRx').textContent = '⏸ PAUSE'; $('btnPauseRx').classList.remove('paused-active');
  $('rxLed').className = 'led'; setRxMsg('Stopped');
}

function resetRxState() {
  rxPhase = 'IDLE'; rxSyncDet = 0; rxSyncGone = 0;
  rxDetCFG = null; rxDataStart = 0; rxLastPx = -1;
  rxPixels = []; rxPxCnt = 0; rxUserPaused = false;
  rxPauseAnchor = 0; rxTxPaused = false; rxLastSig = 0;
  rxResumeSyncStart = 0; rxResumeSyncGone = 0;
}

function clearRx() {
  resetRxState();
  setRxPhase('IDLE — AWAITING START', 'Cleared'); setRxMsg('Cleared');
  $('rxPixelCount').textContent = '0 px';
  $('imgOutput').className = 'img-output';
  const rc = $('rxCanvas'); rc.getContext('2d').clearRect(0, 0, rc.width, rc.height); rc.style.display = 'none';
}

function togglePauseRx() { rxUserPaused ? resumeRx() : pauseRx(); }

function pauseRx() {
  if (!isRx || rxUserPaused) return;
  rxUserPaused = true; rxPauseAnchor = performance.now();
  $('btnPauseRx').textContent = '▶ RESUME'; $('btnPauseRx').classList.add('paused-active');
  $('rxLed').className = 'led on-rx paused-led';
  setRxMsg('Paused — press Resume to continue');
  pairSend({ t: 'rx-pause' });  // tell TX to pause too
}

function resumeRx() {
  if (!isRx || !rxUserPaused) return;
  const dur = performance.now() - rxPauseAnchor;
  if (rxPhase === 'DATA' && rxDataStart > 0) rxDataStart += dur;
  rxUserPaused = false;
  $('btnPauseRx').textContent = '⏸ PAUSE'; $('btnPauseRx').classList.remove('paused-active');
  $('rxLed').className = 'led on-rx';
  setRxMsg('Receiving…');
  pairSend({ t: 'rx-resume' }); // tell TX to resume too
}

// ── FFT helpers ──
function refreshFD() { rxAna.getByteFrequencyData(rxFD); }

function peakIn(fLo, fHi) {
  const b0 = Math.max(0, Math.floor(fLo / rxFR)), b1 = Math.min(rxFD.length - 1, Math.ceil(fHi / rxFR));
  let maxM = 0, maxB = b0;
  for (let i = b0; i <= b1; i++) { if (rxFD[i] > maxM) { maxM = rxFD[i]; maxB = i; } }
  return { freq: maxB * rxFR, mag: maxM };
}

// ── State machine ──
function rxTick() {
  if (!rxAna || rxUserPaused) return;
  const now = performance.now();
  refreshFD();

  if (rxPhase === 'IDLE') {
    const pk = peakIn(BD.SYNC_F - BD.SYNC_W, BD.SYNC_F + BD.SYNC_W);
    if (pk.mag > BD.SYNC_TH) {
      if (!rxSyncDet) rxSyncDet = now;
      if (now - rxSyncDet > 80) { rxPhase = 'SYNC'; rxSyncGone = 0; setRxPhase('START DETECTED', 'Sync carrier locked'); setRxMsg('Start signal active…'); }
    } else { rxSyncDet = 0; }
    return;
  }

  if (rxPhase === 'SYNC') {
    const pk = peakIn(BD.SYNC_F - BD.SYNC_W, BD.SYNC_F + BD.SYNC_W);
    if (pk.mag < BD.SYNC_TH - 12) {
      if (!rxSyncGone) rxSyncGone = now;
      if (now - rxSyncGone > 50) {         // 50ms debounce — confirm tone really ended
        const cfg = rxCode
          ? { resolution: rxCode.resolution, nColors: rxCode.nColors, timeMs: rxCode.timeMs, bw: rxCode.bw }
          : { resolution: 32, nColors: 124, timeMs: 50, bw: false };

        rxDetCFG = cfg;
        buildPalette(cfg.nColors, cfg.bw);
        setupRxCanvas(cfg.resolution);

        rxPhase = 'DATA';
        // rxDataStart is anchored to when sync ended + full PRE_GAP
        // We record rxSyncGone as the reference, then add PRE_GAP
        rxDataStart  = rxSyncGone + P.PRE_GAP;
        rxLastPx     = -1; rxLastSig = now; rxTxPaused = false;
        rxResumeSyncStart = 0; rxResumeSyncGone = 0;

        setRxPhase(`RECEIVING — ${cfg.resolution}×${cfg.resolution}`,
          `${cfg.resolution}×${cfg.resolution} · ${cfg.bw ? '2 colors B&W' : cfg.nColors + ' colors'} · ${cfg.timeMs}ms/tone`);
        setRxMsg(`Receiving ${(cfg.resolution * cfg.resolution).toLocaleString()} pixels…`);
      }
    } else { rxSyncGone = 0; }
    return;
  }

  if (rxPhase === 'DATA') {
    const cfg = rxDetCFG;
    const period = cfg.timeMs + P.PX_GAP;

    // End tone check
    const endPk = peakIn(BD.END_F - BD.END_W, BD.END_F + BD.END_W);
    if (endPk.mag > BD.END_TH) { finishRxData(); return; }

    // Resume sync check (TX paused and is now resuming)
    const syncPk = peakIn(BD.SYNC_F - BD.SYNC_W, BD.SYNC_F + BD.SYNC_W);
    if (syncPk.mag > BD.SYNC_TH) {
      if (!rxResumeSyncStart) rxResumeSyncStart = now;
      else if (now - rxResumeSyncStart > 100) {
        rxTxPaused = false; rxResumeSyncGone = 0;
        setRxMsg('TX resuming…');
      }
      return;
    } else if (rxResumeSyncStart > 0) {
      if (!rxResumeSyncGone) rxResumeSyncGone = now;
      if (now - rxResumeSyncGone > 20) {
        // Recalibrate timing
        rxDataStart = rxResumeSyncGone + P.PRE_GAP - rxPxCnt * period;
        rxResumeSyncStart = 0; rxResumeSyncGone = 0;
        rxLastPx = rxPxCnt - 1;
        setRxMsg('Receiving…');
      }
      return;
    }

    // Auto-detect TX silence
    const anyPk = peakIn(BD.FREQ_LO - 100, BD.END_F + 200);
    if (anyPk.mag > BD.DATA_TH) rxLastSig = now;
    if (now - rxLastSig > 600 && rxPxCnt > 0) {
      if (!rxTxPaused) {
        rxTxPaused = true;
        setRxMsg('TX paused — waiting for resume…');
        setRxPhase('TX PAUSED', 'Waiting for transmitter to resume');
      }
      return;
    }
    if (rxTxPaused) {
      rxTxPaused = false; setRxMsg('Receiving…');
      setRxPhase(`RECEIVING — ${cfg.resolution}×${cfg.resolution}`,
        `${cfg.resolution}×${cfg.resolution} · ${cfg.bw ? '2 colors B&W' : cfg.nColors + ' colors'} · ${cfg.timeMs}ms/tone`);
    }

    // Pixel sampling
    const elapsed = now - rxDataStart;
    if (elapsed < 0) return;
    const total = cfg.resolution * cfg.resolution;
    const pxIdx = Math.floor(elapsed / period);
    const pxOff = elapsed % period;
    const lo = cfg.timeMs * 0.25, hi = cfg.timeMs * 0.76;

    if (pxOff >= lo && pxOff <= hi && pxIdx !== rxLastPx && pxIdx < total) {
      rxLastPx = pxIdx;
      const pk = peakIn(BD.FREQ_LO - 50, BD.FREQ_HI + 50);
      if (pk.mag > BD.DATA_TH) {
        const ci = cfg.bw
          ? (Math.abs(pk.freq - BD.FREQ_LO) < Math.abs(pk.freq - BD.FREQ_HI) ? 0 : 1)
          : freq2idx(pk.freq, cfg.nColors);
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
  const complete = rxPxCnt >= total;

  setRxPhase(complete ? 'COMPLETE ✓' : 'ENDED EARLY', `${rxPxCnt.toLocaleString()} of ${total.toLocaleString()} pixels received`);
  setRxMsg(`Done — ${rxPxCnt.toLocaleString()} px received`);
  $('imgOutput').classList.add('has-img');
  $('btnPauseRx').disabled = true;
  pairSend({ t: 'rx-done', px: rxPxCnt, total });

  // If TX mirror shows it's still going, that's a sync error — show warning
  if (mirrorStatusStr === 'TRANSMITTING' && pairConnected) {
    showRxError(`Finished ${(total - rxPxCnt).toLocaleString()} pixels early while TX is still running. Try increasing Tone Duration in Settings.`);
  }
}

function setupRxCanvas(res) {
  const rc = $('rxCanvas'); rc.width = rc.height = res;
  const rcx = rc.getContext('2d'); rcx.fillStyle = '#060B18'; rcx.fillRect(0, 0, res, res);
  rc.style.display = 'block';
}

function drawRxPixel(idx, ci, res) {
  const rc = $('rxCanvas'), [r, g, b] = palette[ci] || [0,0,0];
  const ctx = rc.getContext('2d');
  ctx.fillStyle = `rgb(${r},${g},${b})`;
  ctx.fillRect(idx % res, Math.floor(idx / res), 1, 1);
}

function saveImg() {
  const rc = $('rxCanvas');
  Object.assign(document.createElement('a'), { download: `audiopix_${Date.now()}.png`, href: rc.toDataURL('image/png') }).click();
}

function setRxMsg(m)          { $('rxStatus').textContent = m; }
function setRxPhase(lbl, sub) { $('rxPhaseLabel').textContent = lbl; $('rxPhaseSub').textContent = sub || ''; }

// ── RX Error Banner ──
function showRxError(msg) {
  let el = $('rxErrorBanner');
  if (!el) {
    el = document.createElement('div');
    el.id = 'rxErrorBanner';
    el.className = 'rx-error-banner tx-error-banner';
    el.innerHTML = `<span class="err-icon">⚠</span><span class="err-text" id="rxErrorText"></span><button class="err-dismiss" onclick="clearRxError()">✕</button>`;
    const sb = $('rxPanel').querySelector('.status-bar');
    sb.parentNode.insertBefore(el, sb.nextSibling);
  }
  $('rxErrorText').textContent = msg;
  el.classList.add('visible');
}
function clearRxError() {
  const el = $('rxErrorBanner');
  if (el) el.classList.remove('visible');
}

function drawRxSpec() {
  if (!isRx || !rxAna) return;
  rxAna.getByteFrequencyData(rxFD);
  const W = rxSpecCV.width, H = rxSpecCV.height;
  rxSpecCX.fillStyle = 'rgba(0,0,0,0.4)'; rxSpecCX.fillRect(0, 0, W, H);
  const maxF = BD.END_F + 500, maxB = Math.floor(maxF / rxFR);
  const nBars = Math.min(maxB, Math.floor(W / 1.5)), bw = W / nBars;
  const nc = rxCode ? rxCode.nColors : CFG.nColors;

  for (let i = 0; i < nBars; i++) {
    const bin = Math.floor(i * maxB / nBars);
    const mag = rxFD[Math.min(bin, rxFD.length - 1)];
    const bh  = (mag / 255) * H;
    const freq = bin * rxFR;
    let col;
    if (Math.abs(freq - BD.SYNC_F) < BD.SYNC_W * 1.5) {
      col = `rgba(80,200,255,${0.5 + mag/512})`;
    } else if (Math.abs(freq - BD.END_F) < BD.END_W * 1.5) {
      col = `rgba(200,80,255,${0.45 + mag/512})`;
    } else if (freq >= BD.FREQ_LO && freq <= BD.FREQ_HI) {
      const ci = rxCode?.bw
        ? (Math.abs(freq - BD.FREQ_LO) < (BD.FREQ_HI - BD.FREQ_LO) / 2 ? 0 : 1)
        : freq2idx(freq, nc);
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
  PND.resolution = CFG.resolution; PND.nColors = CFG.nColors; PND.timeMs = CFG.timeMs;
  PND.bw = CFG.bw; PND.lowPitch = CFG.lowPitch;
  $('colSlider').value = CFG.nColors;
  $('resSlider').value = resToSlider(CFG.resolution);
  $('tmSlider').value  = CFG.timeMs;
  $('toggleBW').className = 'toggle-switch' + (CFG.bw ? ' on' : '');
  $('toggleLP').className = 'toggle-switch' + (CFG.lowPitch ? ' on' : '');
  updatePopup();
  $('overlay').classList.remove('hidden');
}
function closeControls() { $('overlay').classList.add('hidden'); }
function overlayClick(e) { if (e.target === $('overlay')) closeControls(); }

function applySettings() {
  CFG.resolution = PND.resolution; CFG.nColors = PND.nColors; CFG.timeMs = PND.timeMs;
  CFG.bw = PND.bw; CFG.lowPitch = PND.lowPitch;
  updateBand();
  buildPalette(CFG.nColors);
  if (origImg) processImage(origImg, CFG.resolution, CFG.nColors);
  refreshPalStrip(CFG.nColors);
  updateBadge(); updateTxCode();
  renderModeTags('txModeTags', CFG.bw, CFG.lowPitch);
  // Update freq labels on TX side too
  $('rxFreqLo') && ($('rxFreqLo').textContent = BD.FREQ_LO + ' Hz');
  $('rxFreqHi') && ($('rxFreqHi').textContent = BD.FREQ_HI + ' Hz');
  closeControls();
}

function toggleBW() {
  PND.bw = !PND.bw;
  $('toggleBW').className = 'toggle-switch' + (PND.bw ? ' on' : '');
  if (PND.bw) { PND.nColors = 2; $('colSlider').value = 2; }
  updatePopup();
}

function toggleLP() {
  PND.lowPitch = !PND.lowPitch;
  $('toggleLP').className = 'toggle-switch' + (PND.lowPitch ? ' on' : '');
  if (PND.lowPitch && !PND.bw && PND.nColors > 20) { PND.nColors = 20; $('colSlider').value = 20; }
  updatePopup();
}

function sliderToRes(v) { return Math.max(1, Math.min(6000, Math.round(Math.pow(6000, v / 100)))); }
function resToSlider(r) { return Math.round(Math.log(Math.max(1, r)) / Math.log(6000) * 100); }

function onColChange(v) {
  let n = parseInt(v);
  if (PND.bw) n = 2;
  if (PND.lowPitch && !PND.bw && n > 20) { n = 20; $('colSlider').value = 20; }
  PND.nColors = n; updatePopup();
}
function onResChange(v) { PND.resolution = sliderToRes(parseFloat(v)); updatePopup(); }
function onTmChange(v)  { PND.timeMs     = parseInt(v);                updatePopup(); }

function updatePopup() {
  const { resolution: res, nColors: nc, timeMs: tm, bw, lowPitch: lp } = PND;

  // B&W locks color count
  const colGroup = $('colGroup');
  if (bw) {
    colGroup.classList.add('locked-group');
    $('colSlider').value = 2;
    $('colVal').textContent = '2 (B&W)';
  } else if (lp) {
    colGroup.classList.remove('locked-group');
    $('colSlider').max = 20;
    $('colVal').textContent = Math.min(nc, 20);
    $('colDesc').textContent = 'Low pitch mode · max 20 colors (100 – 700 Hz)';
    document.querySelector('#colRangeLabels span:last-child').textContent = '20 colors (max)';
  } else {
    colGroup.classList.remove('locked-group');
    $('colSlider').max = 300;
    $('colVal').textContent = nc;
    $('colDesc').textContent = 'Number of distinct palette colors (4 – 300)';
    document.querySelector('#colRangeLabels span:last-child').textContent = '300 colors';
  }

  $('resVal').textContent = `${res}×${res}`;
  $('tmVal').textContent  = `${tm}ms`;

  // Palette preview
  buildPalette(bw ? 2 : Math.min(nc, lp ? 20 : 300), bw);
  const pp = $('palPreview'); pp.innerHTML = '';
  palette.forEach(([r,g,b]) => {
    const s = document.createElement('div'); s.className = 'pal-swatch';
    s.style.background = `rgb(${r},${g},${b})`; pp.appendChild(s);
  });

  // Res grid
  const rg = $('resGrid'), n = Math.min(res, 14);
  rg.style.gridTemplateColumns = `repeat(${n},1fr)`; rg.innerHTML = '';
  for (let i = 0; i < n * n; i++) {
    const d = document.createElement('div'); d.className = 'res-grid-cell';
    d.style.background = `hsl(${(i*137.508)%360},60%,${30+(i%5)*10}%)`; rg.appendChild(d);
  }
  $('resStats').textContent = `${(res*res).toLocaleString()} pixels`;

  // Speed bar
  $('speedFill').style.width = `${(tm / 200) * 100}%`;
  $('speedLabel').textContent = tm <= 8 ? 'Ultrafast' : tm <= 20 ? 'Fast' : tm <= 60 ? 'Normal' : tm <= 120 ? 'Slow' : 'Very slow';

  // Estimate
  const effectiveNc = bw ? 2 : Math.min(nc, lp ? 20 : 300);
  const { pixels, startMs, dataMs, endMs, total } = calcEst(res, effectiveNc, tm);
  $('estPx').textContent    = pixels.toLocaleString();
  $('estHdr').textContent   = fmtTime(startMs);
  $('estTotal').textContent = fmtTime(total);
  $('estNote').textContent  =
    total > 18000000 ? '⚠ Multi-hour transfer!'  :
    total >  3600000 ? '⏳ Hours to complete'     :
    total >   600000 ? '☕ Coffee break needed'   :
    total >    60000 ? '⏱ Under ' + Math.ceil(total/60000) + ' min' :
    total >    10000 ? '⚡ Under a minute'        : '🚀 Super fast!';
  if (total > 0) {
    $('etlSync').style.flex = startMs;
    $('etlData').style.flex = dataMs;
    $('etlEnd').style.flex  = endMs;
  }

  // Code preview
  const previewCode = encodeCode(res, bw ? 2 : Math.min(nc, lp ? 20 : 300), tm, bw, lp);
  if ($('settingsCodeVal')) {
    $('settingsCodeVal').textContent = previewCode;
    const parts = [];
    if (bw) parts.push('B&W');
    if (lp) parts.push('Low Pitch');
    $('settingsCodeDesc').textContent =
      `${res}×${res} · ${bw ? '2 colors (B&W)' : Math.min(nc,lp?20:300) + ' colors'} · ${tm}ms/tone` +
      (parts.length ? ' · ' + parts.join(' + ') : '');
  }
}

function refreshPalStrip(n) {
  buildPalette(n);
  const strip = $('palStripTx'); strip.innerHTML = '';
  palette.forEach(([r,g,b]) => {
    const s = document.createElement('div'); s.className = 'pal-sw'; s.style.background = `rgb(${r},${g},${b})`; strip.appendChild(s);
  });
  $('palCountTx').textContent = CFG.bw ? '2 colors (B&W)' : `${n} colors`;
}

function updateBadge() {
  $('settingsBadge').textContent =
    `${CFG.resolution}px · ${CFG.bw ? 'B&W' : CFG.nColors + 'c'} · ${CFG.timeMs}ms` +
    (CFG.lowPitch ? ' · LP' : '');
}

// ──────────────────────────────────────────
//  INIT
// ──────────────────────────────────────────
buildPalette(CFG.nColors);
buildSpecBars();
refreshPalStrip(CFG.nColors);
updateBadge();
updateTxCode();
updatePopup();
enumDevices();

// Enable transmit right away — example image will load on first click
$('btnTransmit').disabled = false;
setTxMsg('Drop an image or click TRANSMIT for an example');
