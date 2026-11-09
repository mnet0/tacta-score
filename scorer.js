/* Tacta scorer — counts visible dots per deck in a photo of a finished game.
 * Pure pixel analysis, no dependencies. Works in the browser and in Node.
 *
 *   const run = TactaScorer.create({ data, width, height }, ['blue', 'orange']);
 *   for (const step of run.steps) step.run();   // step.label names the stage
 *   run.result  ->  { scores: { blue: n, orange: n }, dots: [{ x, y, r, deck }] }
 *
 * A dot is a round white blob, fully surrounded by deck ink, inside a shape
 * whose white outline is followed by more ink (the card's coloured border).
 * The number badge in the middle of a card fails that last test — past its
 * outline there is only black — and its digit is not round either.
 */
(function (root) {
  'use strict';

  // Typical printed hue (degrees) of each deck's ink.
  const DECKS = {
    red: { hue: 2, css: '#e23b3b' },
    orange: { hue: 35, css: '#f29a1f' },
    green: { hue: 85, css: '#7fb53a' },
    blue: { hue: 218, css: '#5f8fdc' },
    purple: { hue: 264, css: '#8463c9' },
    pink: { hue: 330, css: '#e74c9b' },
  };

  const INK = 1, BLACK = 2; // pixel kinds; 0 = unsaturated and not dark

  function hueOf(r, g, b) {
    const mx = Math.max(r, g, b), mn = Math.min(r, g, b), d = mx - mn;
    if (d === 0) return 0;
    let h;
    if (mx === r) h = ((g - b) / d) % 6;
    else if (mx === g) h = (b - r) / d + 2;
    else h = (r - g) / d + 4;
    h *= 60;
    return h < 0 ? h + 360 : h;
  }

  function hueDist(a, b) {
    const d = Math.abs(a - b) % 360;
    return d > 180 ? 360 - d : d;
  }

  function create(image, deckNames) {
    const { data, width: W, height: H } = image;
    const N = W * H;
    const st = { blobs: [], cand: [] };
    const run = { steps: [], result: null, debug: st };
    let kind, low, levels;

    // ── 1. per pixel: is it saturated ink, card black, or neither ──
    function readColours() {
      kind = new Uint8Array(N);
      low = new Uint8Array(N); // min(r,g,b): high only where a pixel is white
      const hist = new Uint32Array(256);
      for (let i = 0, p = 0; i < N; i++, p += 4) {
        const r = data[p], g = data[p + 1], b = data[p + 2];
        const mx = r > g ? (r > b ? r : b) : g > b ? g : b;
        const mn = r < g ? (r < b ? r : b) : g < b ? g : b;
        low[i] = mn;
        if ((mx - mn) * 5 < mx) hist[mn]++;
      }
      // The brightest unsaturated pixels set the white level of this photo.
      let total = 0;
      for (let v = 90; v < 256; v++) total += hist[v];
      let acc = 0, ref = 255;
      for (let v = 255; v >= 90; v--) {
        acc += hist[v];
        if (acc > total * 0.1) { ref = v; break; }
      }
      const tBlack = Math.max(50, Math.min(100, ref * 0.38));
      levels = [Math.max(100, ref * 0.68), Math.max(70, ref * 0.44)];
      st.whiteRef = ref; st.levels = levels;
      for (let i = 0, p = 0; i < N; i++, p += 4) {
        const r = data[p], g = data[p + 1], b = data[p + 2];
        const mx = r > g ? (r > b ? r : b) : g > b ? g : b;
        const d = mx - low[i];
        if (mx < tBlack) kind[i] = BLACK;
        else if (d * 100 >= mx * 24) kind[i] = INK;
      }
    }

    // ── 2. connected white blobs, keeping only the round ones ──
    function traceShapes() {
      const stack = new Int32Array(N);
      const maxArea = Math.max(400, (Math.max(W, H) / 55) ** 2 * 3.2);
      for (const T of levels) {
        const seen = new Uint8Array(N);
        for (let s = 0; s < N; s++) {
          if (seen[s] || kind[s] || low[s] <= T) continue;
          let top = 0, area = 0, sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0, sl = 0;
          stack[top++] = s; seen[s] = 1;
          while (top) {
            const i = stack[--top];
            const x = i % W, y = (i - x) / W;
            area++; sx += x; sy += y; sxx += x * x; syy += y * y; sxy += x * y; sl += low[i];
            const xa = x > 0 ? x - 1 : x, xb = x < W - 1 ? x + 1 : x;
            const ya = y > 0 ? y - 1 : y, yb = y < H - 1 ? y + 1 : y;
            for (let yy = ya; yy <= yb; yy++) {
              for (let xx = xa; xx <= xb; xx++) {
                const j = yy * W + xx;
                if (!seen[j] && !kind[j] && low[j] > T) { seen[j] = 1; stack[top++] = j; }
              }
            }
          }
          if (area < 9 || area > maxArea) continue;
          const cx = sx / area, cy = sy / area;
          // Second moments → equivalent ellipse. 1/12 is a pixel's own extent.
          const vxx = sxx / area - cx * cx + 1 / 12;
          const vyy = syy / area - cy * cy + 1 / 12;
          const vxy = sxy / area - cx * cy;
          const tr = vxx + vyy, det = vxx * vyy - vxy * vxy;
          const disc = Math.sqrt(Math.max(0, (tr * tr) / 4 - det));
          const l1 = tr / 2 + disc, l2 = Math.max(1e-6, tr / 2 - disc);
          const axis = Math.sqrt(l1 / l2);                         // 1 = circle
          const fill = area / (4 * Math.PI * Math.sqrt(l1 * l2));  // 1 = solid ellipse
          if (axis > 1.45 || fill < 0.93) continue;
          st.blobs.push({ x: cx, y: cy, r: Math.sqrt(area / Math.PI), axis, fill, T, white: sl / area });
        }
      }
    }

    // ── 3. keep blobs that sit in ink, inside an outlined edge shape ──
    function checkDots() {
      const passed = [];
      for (const b of st.blobs) {
        const rIn = b.r * 1.3 + 1, rOut = b.r * 2 + 1.5, R = Math.ceil(rOut);
        const xc = Math.round(b.x), yc = Math.round(b.y);
        let n = 0, nc = 0, sr = 0, sg = 0, sb = 0, sl = 0;
        for (let dy = -R; dy <= R; dy++) {
          const y = yc + dy;
          if (y < 0 || y >= H) { n += 2 * R + 1; continue; }
          for (let dx = -R; dx <= R; dx++) {
            const d2 = dx * dx + dy * dy;
            if (d2 < rIn * rIn || d2 > rOut * rOut) continue;
            n++;
            const x = xc + dx;
            if (x < 0 || x >= W) continue;
            const i = y * W + x;
            if (kind[i] === INK) {
              nc++; sl += low[i]; const p = i * 4;
              sr += data[p]; sg += data[p + 1]; sb += data[p + 2];
            }
          }
        }
        b.ring = n ? nc / n : 0;
        if (b.ring < 0.8) continue;
        b.rgb = [sr / nc, sg / nc, sb / nc];
        b.hue = hueOf(b.rgb[0], b.rgb[1], b.rgb[2]);
        b.sat = 1 - Math.min(...b.rgb) / Math.max(...b.rgb);

        // Walk outward in every direction: dot → ink → white outline → ?
        // Outlines are thin and blur into the ink, so "white" here is judged
        // against this dot's own ink and white levels.
        const inkLow = sl / nc, span = b.white - inkLow;
        const tLine = inkLow + span * 0.4, tInk = inkLow + span * 0.25;
        const reach = b.r * 1.3 + 2; // how far past the outline ink must appear
        const maxT = b.r * 9 + 6;
        let toInk = 0;
        const RAYS = 32;
        for (let k = 0; k < RAYS; k++) {
          const a = (k / RAYS) * 2 * Math.PI, ux = Math.cos(a), uy = Math.sin(a);
          let phase = 0, runLen = 0, t0 = 0;
          for (let t = b.r * 0.6; t < maxT; t += 0.5) {
            const x = Math.round(b.x + ux * t), y = Math.round(b.y + uy * t);
            if (x < 0 || x >= W || y < 0 || y >= H) break;
            const i = y * W + x, c = kind[i];
            if (phase === 0) { if (c === INK) phase = 1; }
            else if (phase === 1) {
              if (c === BLACK) break;
              if (low[i] > tLine) { phase = 2; t0 = t; }
            } else {
              if (c === BLACK || t - t0 > reach) break;
              if (c === INK && low[i] < tInk) { if (++runLen >= 2) { toInk++; break; } } else runLen = 0;
            }
          }
        }
        b.toInk = toInk / RAYS;
        if (b.toInk < 0.12) continue;
        passed.push(b);
      }
      // The same dot can be found at both white levels: keep the fuller one.
      passed.sort((a, b) => b.r - a.r);
      const cand = (st.cand = []);
      for (const b of passed) {
        if (!cand.some(c => (c.x - b.x) ** 2 + (c.y - b.y) ** 2 < c.r * c.r)) cand.push(b);
      }
    }

    // ── 4. decide which deck owns each dot, then count ──
    function count() {
      let cand = st.cand;
      // Dots are all the same physical size: keep the dominant size cluster.
      if (cand.length >= 4) {
        const rs = cand.map(b => b.r).sort((a, b) => a - b);
        let best = 0, bestR = rs[0];
        for (const r of rs) {
          const c = rs.filter(v => v >= r / 1.3 && v <= r * 1.3).length;
          if (c > best) { best = c; bestR = r; }
        }
        const inl = rs.filter(v => v >= bestR / 1.3 && v <= bestR * 1.3);
        const med = (st.dotR = inl[inl.length >> 1]);
        cand = cand.filter(b => b.r >= med / 1.6 && b.r <= med * 1.5);
      }
      const names = deckNames.filter(n => DECKS[n]);
      const centers = {};
      for (const n of names) centers[n] = DECKS[n].hue;
      const nearest = h => {
        let deck = null, d = 1e9;
        for (const n of names) { const v = hueDist(h, centers[n]); if (v < d) { d = v; deck = n; } }
        return { deck, d };
      };
      // Let each deck's hue drift toward what this photo's lighting shows.
      for (let it = 0; it < 4; it++) {
        const acc = {};
        for (const n of names) acc[n] = [0, 0, 0];
        for (const b of cand) {
          const { deck, d } = nearest(b.hue);
          if (!deck || d > 30) continue;
          const a = (b.hue * Math.PI) / 180;
          acc[deck][0] += Math.cos(a); acc[deck][1] += Math.sin(a); acc[deck][2]++;
        }
        for (const n of names) {
          if (acc[n][2] < 3) continue;
          let h = (Math.atan2(acc[n][1], acc[n][0]) * 180) / Math.PI;
          if (h < 0) h += 360;
          if (hueDist(h, DECKS[n].hue) <= 22) centers[n] = h;
        }
      }
      st.centers = centers;
      const byDeck = {};
      for (const n of names) byDeck[n] = [];
      for (const b of cand) {
        const { deck, d } = nearest(b.hue);
        if (deck && d <= 28) byDeck[deck].push(b);
      }
      const dots = [], scores = {};
      for (const n of names) {
        // Ink far paler than the rest of its deck is glare on black, not ink.
        const sats = byDeck[n].map(b => b.sat).sort((a, b) => a - b);
        const floor = sats.length ? sats[sats.length >> 1] * 0.6 : 0;
        const kept = byDeck[n].filter(b => b.sat >= floor);
        scores[n] = kept.length;
        for (const b of kept) dots.push({ x: b.x, y: b.y, r: b.r, deck: n });
      }
      run.result = { scores, dots, dotRadius: st.dotR || 0 };
    }

    run.steps = [
      { label: 'Reading colours', run: readColours },
      { label: 'Tracing shapes', run: traceShapes },
      { label: 'Checking dots', run: checkDots },
      { label: 'Counting points', run: count },
    ];
    return run;
  }

  const api = { create, DECKS };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.TactaScorer = api;
})(typeof self !== 'undefined' ? self : this);
