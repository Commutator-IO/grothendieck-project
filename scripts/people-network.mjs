#!/usr/bin/env node
/**
 * Builds the people network the Findings tab draws: who is named together in
 * the same folder.
 *
 *   npm run people-network
 *
 * Reads src/content/people-evidence.json (letters, texts of theirs, and his
 * attributions, each with the file and line it rests on) and writes
 * src/content/people-network.json: nodes with fixed positions and a cluster,
 * and weighted links. Everything is computed here, once, so that the figure is
 * the same on every load and the site gains no dependency — the same choice as
 * the archive's mosaic.
 *
 * The method is the one VOSviewer uses for co-occurrence maps, cut down:
 *   - fractional counting: a folder naming n people gives each pair among them
 *     1/(n−1), so a folder that names twenty people does not outweigh twenty
 *     folders that each name two;
 *   - clusters by modularity (Louvain), deterministic: nodes visited in a fixed
 *     order, ties broken by index;
 *   - positions by a force layout (Fruchterman–Reingold) from a seeded start.
 * Nodes are the people who share a folder with at least one other person; a
 * person named alone in every folder they appear in has nothing to link to.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const IN = resolve(ROOT, 'src/content/people-evidence.json');
const OUT = resolve(ROOT, 'src/content/people-network.json');

const { records } = JSON.parse(readFileSync(IN, 'utf8'));

// person → folders, folder → people
const byPerson = new Map();
const byFolder = new Map();
for (const r of records) {
  if (!byPerson.has(r.person)) byPerson.set(r.person, new Set());
  byPerson.get(r.person).add(r.folder);
  if (!byFolder.has(r.folder)) byFolder.set(r.folder, new Set());
  byFolder.get(r.folder).add(r.person);
}

// Fractional co-occurrence.
const pair = (a, b) => (a < b ? `${a}\u0000${b}` : `${b}\u0000${a}`);
const weight = new Map();
const sharedFolders = new Map();
for (const [folder, people] of byFolder) {
  const list = [...people].sort();
  if (list.length < 2) continue;
  const w = 1 / (list.length - 1);
  for (let i = 0; i < list.length; i++)
    for (let j = i + 1; j < list.length; j++) {
      const k = pair(list[i], list[j]);
      weight.set(k, (weight.get(k) ?? 0) + w);
      if (!sharedFolders.has(k)) sharedFolders.set(k, []);
      sharedFolders.get(k).push(folder);
    }
}

const names = [...new Set([...weight.keys()].flatMap((k) => k.split('\u0000')))].sort();
const idx = new Map(names.map((n, i) => [n, i]));
const N = names.length;
const links = [...weight].map(([k, w]) => {
  const [a, b] = k.split('\u0000');
  return { s: idx.get(a), t: idx.get(b), w, folders: sharedFolders.get(k) };
});

/* ---------- Louvain, one graph, deterministic ---------- */
function louvain(n, edges) {
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

const cluster = louvain(N, links);

/* ---------- Fruchterman–Reingold, seeded ---------- */
function mulberry32(a) {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const rand = mulberry32(1953);
const W = 1000;
const H = 640;
const pos = names.map(() => ({ x: rand() * W, y: rand() * H }));
const area = W * H;
const kk = Math.sqrt(area / N) * 1.25;
const maxW = Math.max(...links.map((l) => l.w));
let temp = W / 8;
for (let it = 0; it < 900; it++) {
  const disp = names.map(() => ({ x: 0, y: 0 }));
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
const FOOT = 70;
const M = 50;
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
  const members = names.map((_, j) => j).filter((j) => compOf[j] === compOf[i]);
  const k = members.indexOf(i);
  const slotW = (W - 2 * M) / Math.max(small.length, 1);
  return { x: M + slotW * (c + 0.5) + (k - (members.length - 1) / 2) * 70, y: H - FOOT / 2 };
});

// Clusters ordered by size, so the categorical colours go to the largest.
const sizes = new Map();
for (const c of cluster) sizes.set(c, (sizes.get(c) ?? 0) + 1);
const rank = new Map(
  [...sizes].sort((a, b) => b[1] - a[1] || a[0] - b[0]).map(([c], i) => [c, i]),
);

const out = {
  $why:
    'Generated by `npm run people-network` from people-evidence.json — do not edit by hand. Positions and clusters are computed once so the figure is the same on every load.',
  built: new Date().toISOString().slice(0, 10),
  width: W,
  height: H,
  nodes: names.map((n, i) => ({
    name: n,
    x: Math.round(place[i].x),
    y: Math.round(place[i].y),
    cluster: rank.get(cluster[i]),
    folders: [...byPerson.get(n)].sort(),
  })),
  links: links.map((l) => ({ s: l.s, t: l.t, w: Number(l.w.toFixed(3)), folders: l.folders.sort() })),
};
writeFileSync(OUT, `${JSON.stringify(out, null, 1)}\n`);
process.stdout.write(
  `${out.nodes.length} people, ${out.links.length} links, ${sizes.size} clusters → src/content/people-network.json\n`,
);
