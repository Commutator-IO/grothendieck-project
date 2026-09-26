/**
 * The two computations every network on the Findings tab shares, so that the
 * people, the subjects and the citations are laid out and clustered the same
 * way: Louvain modularity, deterministic, and a seeded Fruchterman–Reingold
 * layout whose largest component fills the canvas while the small ones sit in
 * a row along the foot. See scripts/people-network.mjs for why each choice.
 */

/* ---------- Louvain, one graph, deterministic ---------- */
export function louvain(n, edges) {
  // community of each original node
  let member = Array.from({ length: n }, (_, i) => i);
  let nodes = n;
  let E = edges.map((e) => ({ s: e.s, t: e.t, w: e.w }));
  for (let level = 0; level < 10; level++) {
    // A community's internal weight survives aggregation as a self-loop: it
    // counts in the node's degree, and so in the modularity, but it is not a
    // neighbour to move towards.
    const adj = Array.from({ length: nodes }, () => new Map());
    const k = Array.from({ length: nodes }, () => 0);
    let m2 = 0;
    for (const e of E) {
      if (e.s === e.t) {
        k[e.s] += 2 * e.w;
      } else {
        adj[e.s].set(e.t, (adj[e.s].get(e.t) ?? 0) + e.w);
        adj[e.t].set(e.s, (adj[e.t].get(e.s) ?? 0) + e.w);
        k[e.s] += e.w;
        k[e.t] += e.w;
      }
      m2 += 2 * e.w;
    }
    const comm = Array.from({ length: nodes }, (_, i) => i);
    const tot = [...k];
    let moved = true;
    let any = false;
    for (let pass = 0; moved && pass < 50; pass++) {
      moved = false;
      for (let i = 0; i < nodes; i++) {
        const ci = comm[i];
        const toC = new Map();
        for (const [j, w] of adj[i]) toC.set(comm[j], (toC.get(comm[j]) ?? 0) + w);
        tot[ci] -= k[i];
        let best = ci;
        let gain = (toC.get(ci) ?? 0) - (tot[ci] * k[i]) / m2;
        for (const [c, w] of [...toC].sort((a, b) => a[0] - b[0])) {
          const g = w - (tot[c] * k[i]) / m2;
          if (g > gain + 1e-12) {
            gain = g;
            best = c;
          }
        }
        tot[best] += k[i];
        if (best !== ci) {
          comm[i] = best;
          moved = true;
          any = true;
        }
      }
    }
    if (!any) break;
    const ids = [...new Set(comm)].sort((a, b) => a - b);
    const re = new Map(ids.map((c, i) => [c, i]));
    member = member.map((c) => re.get(comm[c]));
    const agg = new Map();
    for (const e of E) {
      const a = re.get(comm[e.s]);
      const b = re.get(comm[e.t]);
      const key = a < b ? `${a},${b}` : `${b},${a}`;
      agg.set(key, (agg.get(key) ?? 0) + e.w);
    }
    E = [...agg].map(([key, w]) => {
      const [s, t] = key.split(',').map(Number);
      return { s, t, w };
    });
    nodes = ids.length;
  }
  return member;
}

function mulberry32(a) {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** Positions for nodes 0..N−1 on a W×H canvas; links are { s, t, w }. */
export function layout(N, links, { W = 1000, H = 640, seed = 1953, spread = 1.25, foot = 70 } = {}) {
  const rand = mulberry32(seed);
  const pos = Array.from({ length: N }, () => ({ x: rand() * W, y: rand() * H }));
  const area = W * H;
  const kk = Math.sqrt(area / N) * spread;
  const maxW = Math.max(...links.map((l) => l.w));
  let temp = W / 8;
  for (let it = 0; it < 900; it++) {
    const disp = Array.from({ length: N }, () => ({ x: 0, y: 0 }));
    for (let i = 0; i < N; i++)
      for (let j = i + 1; j < N; j++) {
        let dx = pos[i].x - pos[j].x;
        let dy = pos[i].y - pos[j].y;
        const d = Math.max(Math.hypot(dx, dy), 0.01);
        const f = (kk * kk) / d;
        dx /= d;
        dy /= d;
        disp[i].x += dx * f;
        disp[i].y += dy * f;
        disp[j].x -= dx * f;
        disp[j].y -= dy * f;
      }
    for (const l of links) {
      let dx = pos[l.s].x - pos[l.t].x;
      let dy = pos[l.s].y - pos[l.t].y;
      const d = Math.max(Math.hypot(dx, dy), 0.01);
      const f = ((d * d) / kk) * (0.4 + (0.6 * l.w) / maxW);
      dx /= d;
      dy /= d;
      disp[l.s].x -= dx * f;
      disp[l.s].y -= dy * f;
      disp[l.t].x += dx * f;
      disp[l.t].y += dy * f;
    }
    // gravity towards the centre, so separate components do not drift off
    for (let i = 0; i < N; i++) {
      disp[i].x += (W / 2 - pos[i].x) * 0.02 * kk * 0.1;
      disp[i].y += (H / 2 - pos[i].y) * 0.02 * kk * 0.1;
      const d = Math.max(Math.hypot(disp[i].x, disp[i].y), 0.01);
      pos[i].x += (disp[i].x / d) * Math.min(d, temp);
      pos[i].y += (disp[i].y / d) * Math.min(d, temp);
    }
    temp = Math.max(temp * 0.993, 0.5);
  }
  // Connected components. The largest fills the canvas; the small ones — two
  // people named together in a single folder — would otherwise drift to the
  // corners and squeeze everything else, so they sit in a row along the foot.
  const compOf = Array.from({ length: N }, () => -1);
  let nComp = 0;
  for (let i = 0; i < N; i++) {
    if (compOf[i] >= 0) continue;
    const stack = [i];
    compOf[i] = nComp;
    while (stack.length) {
      const v = stack.pop();
      for (const l of links) {
        const u = l.s === v ? l.t : l.t === v ? l.s : -1;
        if (u >= 0 && compOf[u] < 0) {
          compOf[u] = nComp;
          stack.push(u);
        }
      }
    }
    nComp++;
  }
  const compSize = Array.from({ length: nComp }, (_, c) => compOf.filter((x) => x === c).length);
  const giant = compSize.indexOf(Math.max(...compSize));
  const FOOT = foot;
  const M = 70;
  const inGiant = pos.filter((_, i) => compOf[i] === giant);
  const xs = inGiant.map((p) => p.x);
  const ys = inGiant.map((p) => p.y);
  const [x0, x1, y0, y1] = [Math.min(...xs), Math.max(...xs), Math.min(...ys), Math.max(...ys)];
  const fitX = (v) => M + ((v - x0) / Math.max(x1 - x0, 1)) * (W - 2 * M);
  const fitY = (v) => M + ((v - y0) / Math.max(y1 - y0, 1)) * (H - FOOT - 2 * M);
  const small = [...new Set(compOf)].filter((c) => c !== giant).sort((a, b) => a - b);
  const place = pos.map((p, i) => {
    if (compOf[i] === giant) return { x: fitX(p.x), y: fitY(p.y) };
    const c = small.indexOf(compOf[i]);
    const members = Array.from({ length: N }, (_, j) => j).filter((j) => compOf[j] === compOf[i]);
    const k = members.indexOf(i);
    const slotW = (W - 2 * M) / Math.max(small.length, 1);
    return { x: M + slotW * (c + 0.5) + (k - (members.length - 1) / 2) * 70, y: H - FOOT / 2 };
  });
  return place;
}

/** Cluster ids renumbered by size, so the categorical colours go to the largest. */
export function rankClusters(cluster) {
  const sizes = new Map();
  for (const c of cluster) sizes.set(c, (sizes.get(c) ?? 0) + 1);
  const rank = new Map([...sizes].sort((a, b) => b[1] - a[1] || a[0] - b[0]).map(([c], i) => [c, i]));
  return { rank: cluster.map((c) => rank.get(c)), count: sizes.size };
}
