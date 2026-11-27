// V5: V4 + buffer awal besar (A/B 32K, trace 8M entri) agar case pertama tak kena growth copy. + backtrack ke array angka datar
// + change runs langsung dari backtrack (tanpa array runs / reverse / objek run).
// Implementasi orisinal dari aturan RULES.txt / index.js referensi (dibaca, tidak disalin).
// Koordinat consumed-count: x = garis old terpakai, y = garis new terpakai, k = x - y.
// Trace: depth d menyimpan d+1 entri di offset d*(d+1)/2, indeks (k+d)/2; nilai x atau -1.

const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

// Buffer kerja dipakai ulang: run() dipanggil berurutan per case, tiap run()
// menulis ulang semua sel yang dibacanya (Map di-clear, A/B/trace ditulis penuh
// untuk depth yang dicapai), jadi pemakaian ulang deterministik dan aman.
let _map = new Map();
let _A = new Int32Array(32768);
let _B = new Int32Array(32768);
let _trace = new Int32Array(1 << 23);

export function run(input) {
  const oldText = input.old;
  const newText = input.new;
  const op = oldText.split('\n');
  const np = newText.split('\n');
  const n = op[op.length - 1] === '' ? op.length - 1 : op.length;
  const m = np[np.length - 1] === '' ? np.length - 1 : np.length;
  const oldBare = op[op.length - 1] !== '';
  const newBare = np[np.length - 1] !== '';

  // Trim prefix lalu suffix dari sisanya pada parts mentah — persis referensi.
  // Dua garis sama hanya bila teksnya sama DAN status bare-nya sama.
  const eq = (i, j) =>
    op[i] === np[j] && ((i === n - 1 && oldBare) === (j === m - 1 && newBare));
  let pre = 0;
  while (pre < n && pre < m && eq(pre, pre)) pre++;
  let suf = 0;
  while (suf < n - pre && suf < m - pre && eq(n - 1 - suf, m - 1 - suf)) suf++;
  const n2 = n - pre - suf;
  const m2 = m - pre - suf;

  // Interning hanya bagian tengah, ke buffer pakai ulang (indeks basis 0).
  // Garis bare terakhir dikunci garis+'\n' (takkan sama dengan kunci garis
  // ber-newline, karena hasil split tak mengandung '\n').
  const map = _map;
  map.clear();
  let nextId = 0;
  if (_A.length < n2) _A = new Int32Array(Math.max(n2, _A.length * 2));
  if (_B.length < m2) _B = new Int32Array(Math.max(m2, _B.length * 2));
  const A = _A;
  const B = _B;
  for (let i = 0; i < n2; i++) {
    const ai = pre + i;
    const key = ai === n - 1 && oldBare ? op[ai] + '\n' : op[ai];
    let id = map.get(key);
    if (id === undefined) { id = nextId++; map.set(key, id); }
    A[i] = id;
  }
  for (let i = 0; i < m2; i++) {
    const bi = pre + i;
    const key = bi === m - 1 && newBare ? np[bi] + '\n' : np[bi];
    let id = map.get(key);
    if (id === undefined) { id = nextId++; map.set(key, id); }
    B[i] = id;
  }

  // ---- Myers greedy, trace parity-packed pakai ulang ----
  let trace = _trace;
  const ensure = (need) => {
    if (trace.length < need) {
      let cap = trace.length;
      while (cap < need) cap *= 2;
      const nt = new Int32Array(cap);
      nt.set(trace);
      trace = nt;
      _trace = nt;
    }
  };

  let dF = 0;
  let kF = 0;
  let xF = 0;
  let x = 0;
  let y = 0;
  while (x < n2 && y < m2 && A[x] === B[y]) { x++; y++; }
  trace[0] = x;
  if (x === n2 && y === m2) {
    xF = x;
  } else {
    let done = false;
    for (let d = 1; d <= n2 + m2 && !done; d++) {
      const basePrev = (d - 1) * d / 2;
      const base = d * (d + 1) / 2;
      ensure(base + d + 1);
      // Indeks baca berjalan: saat k naik 2, indeks prevDel dan prevIns naik 1.
      let iDel = basePrev;
      let iIns = basePrev;
      for (let k = -d, j = 0; k <= d; k += 2, j++) {
        const prevDel = k > -d ? trace[iDel++] : -1;
        const prevIns = k < d ? trace[iIns++] : -1;
        const canRemove = prevDel !== -1 && prevDel < n2;
        const canAdd = prevIns !== -1 && prevIns - (k + 1) < m2;
        if (!canRemove && !canAdd) { trace[base + j] = -1; continue; }
        let xx;
        let yy;
        // Tie-break referensi: deletion bila mencapai titik yang sama atau lebih jauh.
        if (canRemove && (!canAdd || prevDel >= prevIns - 1)) { xx = prevDel + 1; yy = xx - k; }
        else { xx = prevIns; yy = xx - k; }
        while (xx < n2 && yy < m2 && A[xx] === B[yy]) { xx++; yy++; }
        trace[base + j] = xx;
        if (xx === n2 && yy === m2) { dF = d; kF = k; xF = xx; done = true; break; }
      }
    }
    if (!done) throw new Error('diff: search ended without reaching both ends');
  }

  // ---- Backtrack dari (dF, kF): kumpulkan runs sebagai angka datar ----
  // rev = [kind, count, kind, count, ...] dalam urutan TERBALIK (akhir -> awal);
  // dibaca mundur tanpa reverse() dan tanpa alokasi objek/array per run.
  const rev = [];
  x = xF;
  let k = kF;
  for (let d = dF; d >= 1; d--) {
    const basePrev = (d - 1) * d / 2;
    const prevDel = k > -d ? trace[basePrev + ((k + d - 2) >> 1)] : -1;
    const prevIns = k < d ? trace[basePrev + ((k + d) >> 1)] : -1;
    const canRemove = prevDel !== -1 && prevDel < n2;
    const canAdd = prevIns !== -1 && prevIns - (k + 1) < m2;
    if (canRemove && (!canAdd || prevDel >= prevIns - 1)) {
      const snake = x - (prevDel + 1);
      if (snake > 0) { rev.push(KEEP, snake); }
      rev.push(DELETE, 1);
      x = prevDel;
      k = k - 1;
    } else {
      const snake = x - prevIns;
      if (snake > 0) { rev.push(KEEP, snake); }
      rev.push(INSERT, 1);
      x = prevIns;
      k = k + 1;
    }
  }
  if (x > 0) rev.push(KEEP, x);

  // ---- Change runs: jalan langsung dari rev (maju) + prefix; suffix tak perlu ----
  const changes = [];
  let o = pre;
  let p = pre;
  let deleted = 0;
  let inserted = 0;
  for (let i = rev.length - 2; i >= 0; i -= 2) {
    const kind = rev[i];
    const count = rev[i + 1];
    if (kind === KEEP) { o += count; p += count; continue; }
    let c = changes[changes.length - 1];
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (kind === DELETE) { c.dels += count; o += count; deleted += count; }
    else { c.ins += count; p += count; inserted += count; }
  }

  // ---- Hunks ----
  const hunks = [];
  for (let i = 0; i < changes.length; i++) {
    const c = changes[i];
    const h = hunks[hunks.length - 1];
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 6) h.push(c);
    else hunks.push([c]);
  }

  // ---- Render ----
  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  const written = (opMark, parts, idx) =>
    idx < parts.length - 1 ? opMark + parts[idx] + '\n' : opMark + parts[idx] + '\n%\n';
  for (let hi = 0; hi < hunks.length; hi++) {
    const h = hunks[hi];
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - 3);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(3, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (let ci = 0; ci < h.length; ci++) {
      const c = h[ci];
      for (; at < c.o; at++) out.push(written('=', op, at));
      for (let t = 0; t < c.dels; t++) out.push(written('-', op, c.o + t));
      for (let t = 0; t < c.ins; t++) out.push(written('+', np, c.p + t));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written('=', op, at));
  }
  return out.join('');
}
