#!/usr/bin/env node
/**
 * Draws the article's figures from the edition's derived data.
 *
 *   node docs/study/figures.mjs
 *
 * Writes fig-pace.tex, fig-hand.tex and fig-dating.tex beside this file, each
 * a pgfplots figure whose data is inlined, so that the article compiles with
 * nothing but tectonic and the figure states, in its caption, the file it was
 * drawn from and the day. fig-pipeline.tex is drawn by hand, because it states
 * decisions and not data.
 *
 * Sources: git's own history for the pace; src/content/hand.json (npm run
 * hand) for the legibility; src/lib/dating.ts's reading of the inventory and
 * src/content/dated-leaves.json for the dating.
 */
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const root = resolve(here, '../..');
const J = (p) => JSON.parse(readFileSync(resolve(root, p), 'utf8'));
const today = new Date().toISOString().slice(0, 10);

/* ---------------------------------------------------------------- pace */
{
  // The day each batch file first entered the repository, by commit date.
  const log = execFileSync(
    'git',
    ['log', '--diff-filter=A', '--format=@%ad', '--date=short', '--name-only', '--', 'transcripts/*/batch-*.fr.tex'],
    { cwd: root, encoding: 'utf8' },
  );
  const firstSeen = new Map();
  let day = null;
  for (const line of log.split('\n')) {
    if (line.startsWith('@')) day = line.slice(1);
    else if (/batch-\d+\.fr\.tex$/.test(line) && !line.includes('_specimen')) {
      // git log runs newest first: the last date met is the earliest.
      firstSeen.set(line, day);
    }
  }
  const days = [...firstSeen.values()].sort();
  const d0 = new Date(`${days[0]}T00:00:00Z`);
  const dayNo = (d) => Math.round((new Date(`${d}T00:00:00Z`) - d0) / 864e5);
  const last = dayNo(days[days.length - 1]);
  const cum = [];
  let k = 0;
  for (let i = 0; i <= last; i++) {
    const iso = new Date(d0.getTime() + i * 864e5).toISOString().slice(0, 10);
    k += days.filter((d) => d === iso).length;
    cum.push([i, k]);
  }
  const TOTAL = 618; // batches of twenty pages in the whole fonds (catalogue.ts)
  const labelDays = cum.filter(([i]) => i % 7 === 0).map(([i]) => i);
  const fmt = (i) => new Date(d0.getTime() + i * 864e5).toISOString().slice(5, 10).split('-').reverse().join('/');
  writeFileSync(
    resolve(here, 'fig-pace.tex'),
    `\\begin{figure}[htbp]\\centering
\\begin{tikzpicture}
\\begin{axis}[width=13cm,height=6.2cm,xmin=0,xmax=${last + 1},ymin=0,ymax=${TOTAL + 20},
  xtick={${labelDays.join(',')}},xticklabels={${labelDays.map(fmt).join(',')}},
  ylabel={batch files},grid=major,grid style={black!10},tick label style={font=\\footnotesize},
  label style={font=\\footnotesize},axis line style={black!50},clip=false]
\\addplot[black!25,dashed,domain=0:${last + 1}] {${TOTAL}};
\\node[font=\\scriptsize,text=black!55,anchor=south east] at (axis cs:${last + 1},${TOTAL}) {${TOTAL} batches of twenty pages: the whole fonds};
\\addplot[const plot,thick,black!75] coordinates {${cum.map(([i, v]) => `(${i},${v})`).join(' ')}};
\\node[font=\\scriptsize,anchor=south east] at (axis cs:${last},${k}) {${k}};
\\end{axis}
\\end{tikzpicture}
\\caption{Batch files in the repository, day by day, from the first on ${days[0]} to ${days[days.length - 1]}: the date each \\texttt{batch-NN.fr.tex} was first committed, cumulated. Each file is one pass of the model over at most twenty pages. The dashed line is the whole fonds at that rate. From the repository's git history, drawn on ${today} by \\texttt{docs/study/figures.mjs}.}\\label{fig:pace}
\\end{figure}
`,
  );
}

/* ---------------------------------------------------------------- hand */
{
  const hand = J('src/content/hand.json');
  const unread = (f) => f.ill / Math.max(1, f.words + f.ill);
  const dated = hand.folders.filter((f) => f.year !== null);
  const undated = hand.folders.filter((f) => f.year === null).sort((a, b) => unread(b) - unread(a));
  const rows = [
    ...dated.map((f) => [f.year, (100 * unread(f)).toFixed(2), f.pages]),
    ...undated.map((f, i) => [1994 + (i % 3) - 1, (100 * unread(f)).toFixed(2), f.pages]),
  ];
  const tot = hand.folders.reduce((a, f) => ({ ill: a.ill + f.ill, words: a.words + f.words }), { ill: 0, words: 0 });
  writeFileSync(
    resolve(here, 'fig-hand.tex'),
    `\\begin{figure}[htbp]\\centering
\\begin{tikzpicture}
\\begin{axis}[width=13cm,height=7.4cm,xmin=1948,xmax=1996,ymin=0,ymax=40,
  xtick={1950,1955,1960,1965,1970,1975,1980,1985,1990,1994},xticklabels={1950,1955,1960,1965,1970,1975,1980,1985,1990,s.d.},
  ylabel={words left \\texttt{\\textbackslash ill\\{\\}}, per cent},grid=major,grid style={black!10},
  tick label style={font=\\footnotesize},label style={font=\\footnotesize},axis line style={black!50}]
\\draw[black!30,dashed] (axis cs:1992,0) -- (axis cs:1992,40);
\\addplot[scatter,only marks,mark=*,scatter/use mapped color={draw=black!70,fill=black!20},
  visualization depends on={\\thisrow{p} \\as \\p},scatter/@pre marker code/.append style={/tikz/mark size={0.8pt+0.13pt*sqrt(\\p)}},
  point meta=\\thisrow{p}] table[x=y,y=u] {
y u p
${rows.map((r) => r.join(' ')).join('\n')}
};
\\end{axis}
\\end{tikzpicture}
\\caption{The share of words the first pass could not read, folder by folder, against the middle of the inventory's dating; ${undated.length} undated folders stand in the column at the right. A larger dot, more pages transcribed. ${hand.folders.length} folders, ${tot.words.toLocaleString('en-GB')} words read and ${tot.ill.toLocaleString('en-GB')} left illegible (${((100 * tot.ill) / (tot.words + tot.ill)).toFixed(1)} per cent). No trend is drawn: the datings are ranges, often decades wide. The count is of the apparatus, not of the ink. From \\texttt{src/content/hand.json} (${hand.built}), after the site's page \\emph{The hand}.}\\label{fig:hand}
\\end{figure}
`,
  );
}

/* -------------------------------------------------------------- dating */
{
  // The inventory's datings, parsed the way src/lib/dating.ts parses them.
  const cat = readFileSync(resolve(root, 'src/content/catalogue.ts'), 'utf8');
  const datings = [...cat.matchAll(/"id": "([^"]+)",\s*"file": "[^"]+",\s*"date": "([^"]*)"/g)].map((m) => m[2]);
  const Q = { vers: 'vers', 'à partir de': 'from', après: 'after', avant: 'before', années: 'decades' };
  function parse(raw) {
    const ends = [];
    let depth = 0;
    let q = null;
    for (const m of raw.matchAll(/(\[)|(\])|(vers|à partir de|après|avant|années)|(\d{4})/g)) {
      if (m[1]) depth++;
      else if (m[2]) depth = Math.max(0, depth - 1);
      else if (m[3]) q = Q[m[3]];
      else {
        ends.push({ year: Number(m[4]), inferred: depth > 0, q });
        if (q !== 'decades') q = null;
      }
    }
    if (!ends.length) return null;
    const a = ends[0];
    const b = ends[ends.length - 1];
    if (ends.length === 1 && (a.q === 'from' || a.q === 'after')) return { from: a.year, to: a.year + 5, inferred: a.inferred };
    if (ends.length === 1 && a.q === 'before') return { from: a.year - 4, to: a.year, inferred: a.inferred };
    return { from: a.year, to: b.q === 'from' ? b.year + 5 : b.year, inferred: a.inferred || b.inferred };
  }
  const ranges = datings.map(parse).filter(Boolean);
  const leaves = J('src/content/dated-leaves.json').records.filter((l) => l.iso && !(l.kind === 'stamp' || l.hand === 'machine'));
  const years = Array.from({ length: 1992 - 1949 }, (_, i) => 1949 + i);
  const cover = years.map((y) => ranges.filter((r) => r.from <= y && y <= r.to).length);
  const read = years.map((y) => ranges.filter((r) => !r.inferred && r.from <= y && y <= r.to).length);
  const onLeaves = years.map((y) => leaves.filter((l) => Number(l.iso.slice(0, 4)) === y).length);
  const coords = (arr) => arr.map((v, i) => `(${years[i]},${v})`).join(' ');
  const s = datings.filter((d) => !parse(d)).length;
  writeFileSync(
    resolve(here, 'fig-dating.tex'),
    `\\begin{figure}[htbp]\\centering
\\begin{tikzpicture}
\\begin{axis}[name=top,width=13cm,height=4.6cm,xmin=1948,xmax=1992,ymin=0,
  xticklabels={},ylabel={folders},ybar,bar width=4.2pt,grid=major,grid style={black!10},
  tick label style={font=\\footnotesize},label style={font=\\footnotesize},axis line style={black!50},
  legend style={font=\\scriptsize,draw=none,at={(0.5,1.02)},anchor=south},legend columns=2,legend cell align=left]
\\addplot[fill=black!18,draw=none] coordinates {${coords(cover)}};
\\addplot[fill=black!65,draw=none] coordinates {${coords(read)}};
\\legend{dated by the inventory, whole range read on the pages}
\\end{axis}
\\begin{axis}[at={(top.south)},anchor=north,yshift=-4mm,width=13cm,height=3.8cm,xmin=1948,xmax=1992,ymin=0,
  ylabel={leaves},ybar,bar width=4.2pt,grid=major,grid style={black!10},xtick={1950,1955,1960,1965,1970,1975,1980,1985,1990},
  x tick label style={/pgf/number format/1000 sep={}},
  tick label style={font=\\footnotesize},label style={font=\\footnotesize},axis line style={black!50}]
\\addplot[fill=black!65,draw=none] coordinates {${coords(onLeaves)}};
\\end{axis}
\\end{tikzpicture}
\\caption{Two kinds of date on one axis, each on its own scale. Above: for each year, how many of the ${ranges.length} dated folders the inventory's ranges cover (an open end, « à partir de 1982 », counted five years on), and, darker, how many of them rest on a range the archivists read on the pages rather than deduced in their square brackets; ${s} folders are « s.d. ». Below: the ${leaves.length} dates the transcriptions have found written on the leaves themselves, machine stamps on reused paper left out. From \\texttt{src/content/catalogue.ts} and \\texttt{src/content/dated-leaves.json} (${J('src/content/dated-leaves.json').built}), after the site's page \\emph{Timeline}.}\\label{fig:dating}
\\end{figure}
`,
  );
}

process.stdout.write('figures: fig-pace.tex, fig-hand.tex, fig-dating.tex\n');
