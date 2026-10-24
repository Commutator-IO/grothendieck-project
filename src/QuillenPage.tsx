import { lazy, Suspense, useCallback, useEffect, useMemo, useState } from "react";
import { FacsimilePane, type OpenBatch } from "./components/FacsimilePane.tsx";
import { Footer, Header } from "./components/Frame.tsx";
import catalogueRaw from "./content/quillen.json";
import { NOTEBOOK_NOTES, YEAR_NOTES } from "./content/quillen-highlights.ts";

/**
 * Daniel Quillen's research notebooks, beside the Grothendieck fonds.
 *
 * The Clay Mathematics Institute scanned them from 2013 and serves one PDF per
 * notebook, filed by year. This page is their reading room, laid out as the
 * fonds' is: the reading on the left, the facsimile in the same resizable pane
 * on the right — the Clay's own file, framed from claymath.org (the server
 * allows it, so unlike Montpellier no relay is needed). What each notebook
 * holds is told by Glenys Luke's index, which the Clay publishes; the page
 * shows its entry, credited, and searches it.
 *
 * Transcriptions (transcripts-quillen/, rendered by `npm run render --
 * --quillen`) are read in components/QuillenReader.tsx, beside the facsimile,
 * at #<notebook>/<batch>/p<page> (#1968/1968-13/1/p3). That reader is compiled
 * in only in the dev server and in a build made with RENDER_QUILLEN: Quillen
 * died in 2011, the notebooks are in copyright, and nothing transcribed from
 * them goes online before the Clay and the family agree (#36). The
 * transcriptions are git-ignored besides, so no deployed build has any to
 * show. The facsimile needs no switch — it is the Clay's publication, not a
 * copy.
 */

interface Notebook {
  id: string;
  group: string;
  filed?: string;
  label: string;
  url: string;
  bytes: number;
  pages: number | null;
  /** The notebook's entry in Luke's index, when it has one. */
  index: string | null;
}
const CATALOGUE = catalogueRaw as unknown as {
  built: string;
  source: string;
  index: string;
  notebooks: Notebook[];
};
const NOTEBOOKS = CATALOGUE.notebooks;

// Off, the condition is a constant `false` and the lazy import goes with it:
// no reader chunk in the build.
const RENDER_QUILLEN =
  import.meta.env.DEV || import.meta.env.VITE_RENDER_QUILLEN === "true";
const QuillenReader = RENDER_QUILLEN
  ? lazy(() =>
      import("./components/QuillenReader.tsx").then((m) => ({
        default: m.QuillenReader,
      })),
    )
  : null;

const YEARS = Array.from({ length: 2003 - 1968 + 1 }, (_, i) =>
  String(1968 + i),
);
const GROUPS: { id: string; label: string }[] = [
  ...YEARS.map((y) => ({ id: y, label: y })),
  { id: "lectures", label: "Lecture notes" },
  { id: "misc", label: "Miscellaneous" },
];
const inGroup = (g: string) => NOTEBOOKS.filter((n) => n.group === g);
const COUNT = new Map(GROUPS.map((g) => [g.id, inGroup(g.id).length]));
const MAX = Math.max(...YEARS.map((y) => COUNT.get(y) ?? 0));
const totalGB = (NOTEBOOKS.reduce((s, n) => s + n.bytes, 0) / 1e9).toFixed(1);
const totalPages = NOTEBOOKS.reduce((s, n) => s + (n.pages ?? 0), 0).toLocaleString('en');

const mb = (b: number) => `${Math.round(b / 1e6)} MB`;
const short = (n: Notebook) => n.label.replace(new RegExp(`^${n.group}-`), "");
const groupLabel = (g: string) => GROUPS.find((x) => x.id === g)?.label ?? g;

/** The start of an entry, cut at a sentence: what fits under a notebook's name. */
function opening(s: string, max = 280): string {
  if (s.length <= max) return s;
  const cut = s.slice(0, max);
  const stop = cut.lastIndexOf(". ");
  return `${stop > max / 2 ? cut.slice(0, stop + 1) : cut.replace(/\s+\S*$/, "")} …`;
}

const fold = (s: string) =>
  s
    .normalize("NFD")
    .replace(/[\u0300-\u036f]/g, "")
    .toLowerCase();

/**
 * The notebook the fragment names — `#1968/1968-1` — and, for the reading
 * view, a batch and a page: `#1968/1968-13/1/p3`.
 */
function parsed(): { nb: Notebook; batch: number; page?: number } | undefined {
  const h = decodeURIComponent(location.hash.slice(1));
  const whole = NOTEBOOKS.find((n) => n.id === h);
  if (whole) return { nb: whole, batch: 1 };
  const m = /^(.+)\/(\d+)(?:\/p(\d+))?$/.exec(h);
  const nb = m && NOTEBOOKS.find((n) => n.id === m[1]);
  return nb
    ? {
        nb,
        batch: Math.max(1, Number(m[2])),
        page: m[3] ? Number(m[3]) : undefined,
      }
    : undefined;
}
const named = (): Notebook | undefined => parsed()?.nb;
const fromHash = (): Notebook => named() ?? inGroup("1968")[0] ?? NOTEBOOKS[0];

export function QuillenPage() {
  const [nb, setNb] = useState<Notebook>(fromHash);
  const [group, setGroup] = useState(nb.group);
  // The facsimile opens when a notebook is chosen, or when the link names one.
  const [pane, setPane] = useState(() => named() !== undefined);
  const [batch, setBatch] = useState(() => parsed()?.batch ?? 1);
  const [page, setPage] = useState(() => parsed()?.page);
  const [query, setQuery] = useState("");
  const [whole, setWhole] = useState(false);

  useEffect(() => {
    const onHash = () => {
      const n = fromHash();
      setNb(n);
      setGroup(n.group);
      setBatch(parsed()?.batch ?? 1);
      setPage(parsed()?.page);
      setPane(true);
    };
    addEventListener("hashchange", onHash);
    return () => removeEventListener("hashchange", onHash);
  }, []);

  const open = (n: Notebook) => {
    history.replaceState(null, "", `#${n.id}`);
    setNb(n);
    setBatch(1);
    setPage(undefined);
    setWhole(false);
    setPane(true);
  };
  // The reading view's own moves: another batch, the page being read, close.
  const toBatch = useCallback(
    (b: number) => {
      history.replaceState(null, "", `#${nb.id}/${b}`);
      setBatch(b);
      setPage(undefined);
    },
    [nb.id],
  );
  const onPage = useCallback((p: number) => setPage(p), []);
  const closeReader = useCallback(() => {
    history.replaceState(null, "", `#${nb.id}`);
    setPane(false);
  }, [nb.id]);
  const list = useMemo(() => inGroup(group), [group]);
  const q = fold(query.trim());
  const found = useMemo(
    () =>
      q.length < 2
        ? null
        : NOTEBOOKS.filter((n) =>
            fold(`${n.label} ${n.index ?? ""}`).includes(q),
          ),
    [q],
  );
  const foundYears = useMemo(
    () => new Set(found?.map((n) => n.group)),
    [found],
  );

  const facsimile: OpenBatch = {
    cote: nb.id,
    title: `Notebook ${nb.label}`,
    date: groupLabel(nb.group),
    batch,
    pages: nb.pages ?? 0,
    relay: "ready",
    source: {
      file: nb.url,
      original: nb.url,
      heading: `Daniel Quillen · ${groupLabel(nb.group)}`,
      credit:
        "Facsimile: Clay Mathematics Institute, served from claymath.org, not copied here.",
      pageOffset: 0,
    },
  };

  const button = (n: Notebook, withYear = false) => (
    <button
      type="button"
      onClick={() => open(n)}
      aria-current={n.id === nb.id ? "true" : undefined}
      title={`${n.label}${n.pages ? ` · ${n.pages} pages` : ""} · ${mb(n.bytes)}${n.filed ? ` · filed under ${n.filed}` : ""}${NOTEBOOK_NOTES[n.id] ? ` — ${NOTEBOOK_NOTES[n.id]}` : n.index ? ` — ${opening(n.index, 160)}` : ""}`}
      className={`tabular rounded-md border px-2.5 py-1 text-[12.5px] transition ${
        n.id === nb.id
          ? NOTEBOOK_NOTES[n.id]
            ? "border-alerte-600 bg-alerte-50 font-semibold text-alerte-700"
            : "border-brand-600 bg-brand-50 font-semibold text-brand-800"
          : NOTEBOOK_NOTES[n.id]
            ? "border-alerte-500 font-semibold text-alerte-600 hover:bg-alerte-50"
            : "border-ink-200 text-ink-700 hover:border-brand-300 hover:bg-brand-50/50"
      }`}
    >
      {withYear ? n.label : short(n)}
    </button>
  );

  return (
    <>
      {/* The content shifts rather than sliding under the pane, as on the
          fonds' pages; gated on `lg:` exactly as the pane is. */}
      <div
        className={`transition-[padding] duration-150 ${pane ? "lg:pr-[var(--pane,0px)]" : ""}`}
      >
        <Header path="/quillen/" />

        <main className="mx-auto max-w-6xl px-5 py-12">
          <header className="max-w-[46em]">
            <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">
              Quillen
            </p>
            <h1 className="titre mt-2 text-[34px] leading-[1.1] text-ink-900">
              Daniel Quillen's research notebooks, 1968–2003
            </h1>
            <p className="mt-4 text-[15px] leading-relaxed text-ink-600">
              Quillen stands on the other side of exchanges the fonds records:
              Grothendieck's notes on Quillen's lectures of September 1968
              (folders 162-5 and 111), and{" "}
              <em>À la poursuite des champs</em>, which began in 1983 as a
              letter to him. These are Quillen's working notes, kept as a diary,
              year by year. The
              Clay Mathematics Institute has scanned them since 2013 and
              publishes them as {NOTEBOOKS.length} PDFs ({totalGB} GB, {totalPages} pages counted); Glenys
              Luke and Graeme Segal are cataloguing them. Each notebook here is
              the Clay's own file, shown from claymath.org and not copied.
            </p>
          </header>

          <section className="mt-9" aria-labelledby="years">
            <h2
              id="years"
              className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400"
            >
              Notebooks by year
            </h2>
            <div className="mt-3 overflow-x-auto">
              <div
                className="flex min-w-[640px] items-end gap-[3px]"
                role="tablist"
                aria-label="Year"
              >
                {YEARS.map((y) => {
                  const k = COUNT.get(y) ?? 0;
                  const on = y === group;
                  const dim = found !== null && !foundYears.has(y);
                  return (
                    <button
                      key={y}
                      type="button"
                      role="tab"
                      aria-selected={on}
                      title={`${y}: ${k} notebook${k === 1 ? "" : "s"}${YEAR_NOTES[y] ? ` — ${YEAR_NOTES[y]}` : ""}`}
                      onClick={() => setGroup(y)}
                      className={`group flex flex-1 flex-col items-center gap-1 transition-opacity ${dim ? "opacity-25" : ""}`}
                    >
                      <span
                        className={`w-full rounded-t-[3px] transition ${
                          YEAR_NOTES[y]
                            ? on
                              ? "bg-alerte-700"
                              : "bg-alerte-500 group-hover:bg-alerte-600"
                            : on
                              ? "bg-brand-600"
                              : "bg-brand-200 group-hover:bg-brand-400"
                        }`}
                        style={{ height: `${Math.max(3, (64 * k) / MAX)}px` }}
                      />
                      <span
                        className={`tabular text-[10px] ${on ? "font-semibold text-ink-900" : YEAR_NOTES[y] ? "font-semibold text-alerte-600" : "text-ink-400"}`}
                      >
                        {y.slice(2)}
                      </span>
                    </button>
                  );
                })}
              </div>
            </div>
            <p className="mt-2 flex items-center gap-1.5 text-[12px] text-ink-500">
              <span
                aria-hidden="true"
                className="inline-block h-2.5 w-2.5 rounded-sm bg-alerte-500"
              />
              Years and notebooks in red meet the Grothendieck fonds; hover over
              one or open it to see why.
            </p>
            <div className="mt-3 flex flex-wrap gap-2 text-[12.5px]">
              {GROUPS.slice(YEARS.length).map((g) => (
                <button
                  key={g.id}
                  type="button"
                  onClick={() => setGroup(g.id)}
                  aria-pressed={g.id === group}
                  className={`rounded-full border px-3 py-1 transition ${
                    g.id === group
                      ? "border-ink-900 bg-ink-900 text-white"
                      : "border-ink-200 text-ink-600 hover:bg-ink-50"
                  }`}
                >
                  {g.label}{" "}
                  <span className="tabular opacity-70">{COUNT.get(g.id)}</span>
                </button>
              ))}
            </div>

            <p className="mt-5 text-[13px] text-ink-500">
              <span className="font-semibold text-ink-800">
                {GROUPS.find((g) => g.id === group)?.label}
              </span>{" "}
              · {list.length} notebook{list.length === 1 ? "" : "s"}
            </p>
            {YEAR_NOTES[group] && (
              <p className="mt-1 max-w-[52em] border-l-2 border-alerte-500 pl-2.5 text-[12.5px] leading-relaxed text-ink-600">
                {YEAR_NOTES[group]}
              </p>
            )}
            <ul className="mt-2 flex flex-wrap gap-1.5">
              {list.map((n) => (
                <li key={n.id}>{button(n)}</li>
              ))}
            </ul>

            <div className="mt-6 max-w-[40em]">
              <label
                htmlFor="luke"
                className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400"
              >
                Search Luke's index
              </label>
              <input
                id="luke"
                type="search"
                value={query}
                onChange={(e) => setQuery(e.target.value)}
                placeholder="topos, motives, K-theory, cyclic, Grothendieck…"
                className="mt-2 w-full rounded-lg border border-ink-200 bg-white px-3 py-2 text-[14px] text-ink-900 placeholder:text-ink-400 focus:border-brand-500 focus:outline-none"
              />
            </div>
            {found && (
              <div className="mt-3">
                <p className="text-[13px] text-ink-500">
                  {found.length} notebook{found.length === 1 ? "" : "s"} whose
                  entry mentions « {query.trim()} »
                  {found.length
                    ? `, in ${foundYears.size} group${foundYears.size === 1 ? "" : "s"}`
                    : ""}
                </p>
                <ul className="mt-2 flex max-h-[14em] flex-wrap gap-1.5 overflow-y-auto">
                  {found.map((n) => (
                    <li key={n.id}>{button(n, true)}</li>
                  ))}
                </ul>
              </div>
            )}
          </section>

          <section className="card mt-8 max-w-[52em] p-5" aria-label="Reading">
            <div className="flex flex-wrap items-baseline justify-between gap-3">
              <div>
                <p className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
                  {groupLabel(nb.group)}
                </p>
                <p className="titre mt-1 text-[22px] text-ink-900">
                  {nb.label}
                </p>
                <p className="mt-1 text-[12.5px] text-ink-500">
                  {nb.pages ? `${nb.pages} pages · ` : ""}
                  {mb(nb.bytes)}
                  {nb.filed ? ` · filed by the Clay under ${nb.filed}` : ""}
                </p>
              </div>
              {!pane && (
                <button
                  type="button"
                  onClick={() => setPane(true)}
                  className="hidden rounded-lg border border-brand-500 px-3 py-1.5 text-[13px] font-medium text-brand-700 transition hover:bg-brand-50 lg:inline-block"
                >
                  {QuillenReader ? "Open the reading" : "Show the facsimile"}
                </button>
              )}
            </div>

            {NOTEBOOK_NOTES[nb.id] && (
              <p className="mt-4 border-l-2 border-alerte-500 pl-2.5 text-[13px] leading-relaxed text-ink-700">
                {NOTEBOOK_NOTES[nb.id]}
              </p>
            )}

            <div className="mt-4">
              <p className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
                In Luke's index
              </p>
              {nb.index ? (
                <>
                  <p className="mt-1.5 text-[14px] leading-relaxed text-ink-700">
                    {whole ? nb.index : opening(nb.index)}
                  </p>
                  {opening(nb.index) !== nb.index && (
                    <button
                      type="button"
                      onClick={() => setWhole(!whole)}
                      className="mt-1 text-[12.5px] font-medium text-brand-600 hover:text-brand-700"
                    >
                      {whole ? "Less" : "The whole entry"}
                    </button>
                  )}
                </>
              ) : (
                <p className="mt-1.5 text-[13.5px] text-ink-500">
                  The index has no entry under a name of this form.
                </p>
              )}
              <p className="mt-2 text-[12px] text-ink-400">
                From Glenys Luke's index of the notebooks, published by the Clay
                Mathematics Institute (
                <a
                  href={CATALOGUE.index}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
                >
                  PDF ↗
                </a>
                ).
              </p>
            </div>

            <p className="mt-5 text-[14px] leading-relaxed text-ink-600">
              {QuillenReader
                ? "Where a notebook is transcribed, its reading stands below, page by page beside the facsimile, as it does for the Grothendieck fonds. The transcriptions stay on the machine that made them until the Clay Mathematics Institute and Quillen's family agree to their publication."
                : "No notebook is transcribed here. Once the Clay Mathematics Institute and Quillen's family have agreed, a transcribed notebook's reading will stand here, page by page beside the facsimile, as it does for the Grothendieck fonds."}
            </p>
            <p className="mt-3 text-[13px] leading-relaxed text-ink-500">
              Quillen died in 2011: the notebooks are in copyright, and the
              scans are the Clay's. This page stores none of them; the facsimile
              is served by claymath.org.
            </p>
            <p className="mt-5 text-[12.5px]">
              <a
                href={nb.url}
                target="_blank"
                rel="noopener noreferrer"
                className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
              >
                Open this notebook at the Clay ↗
              </a>
              <span className="mx-2 text-ink-300" aria-hidden="true">
                ·
              </span>
              <a
                href={CATALOGUE.source}
                target="_blank"
                rel="noopener noreferrer"
                className="font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700"
              >
                The collection ↗
              </a>
            </p>
          </section>

          {QuillenReader && pane && (
            <Suspense fallback={null}>
              <QuillenReader
                nb={nb}
                heading={groupLabel(nb.group)}
                batch={batch}
                page={page}
                onBatch={toBatch}
                onPage={onPage}
                onClose={closeReader}
              />
            </Suspense>
          )}

          <p className="mt-10 max-w-[46em] text-[12px] leading-relaxed text-ink-400">
            The list of notebooks is read from the Clay's file listing
            (src/content/quillen.json, {CATALOGUE.built}); copies the Clay files
            under a second year are left out. Each notebook is matched to its
            entry in Luke's index by name;{" "}
            {NOTEBOOKS.filter((n) => n.index).length} of {NOTEBOOKS.length} have
            one.
          </p>
        </main>

        <Footer collection="quillen" />
      </div>

      {!QuillenReader && pane && (
        <FacsimilePane
          open={facsimile}
          onClose={() => setPane(false)}
          onBatch={setBatch}
        />
      )}
    </>
  );
}
