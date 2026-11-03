import { lazy, Suspense, useEffect, useRef, useState } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import { Footer, Header } from './components/Frame.tsx';
import catalogueRaw from './content/buffalo.json';
import type { Board } from './components/Blackboard.tsx';
import { buffaloIssueUrl } from './lib/report.ts';
import { commentData, useComments } from './components/Comments.tsx';

// The reconstructed boards are published (2026-11-01): written in the git-ignored
// transcripts-buffalo/, copied to public/buffalo-boards/ by `npm run buffalo-boards`.
// The first tape side of the topos course keeps its edited demonstration copy.
const Blackboard = lazy(() => import('./components/Blackboard.tsx').then((m) => ({ default: m.Blackboard })));
const PUBLIC_BOARDS: Record<string, () => Promise<{ default: unknown }>> = {
  'URU5jgTvjhU-0000': () => import('./content/buffalo-board-URU5jgTvjhU-0000.json'),
};

/** The tape side a second falls in: boards are filed by video and side. */
const sideOf = (v: { segments: { start: number }[] }, t: number) =>
  v.segments.reduce((s, x) => (x.start <= t ? x.start : s), 0);

interface YTPlayer {
  getCurrentTime(): number;
  seekTo(t: number, allow: boolean): void;
  destroy(): void;
}
declare global {
  interface Window {
    YT?: { Player: new (el: HTMLElement, o: object) => YTPlayer };
    onYouTubeIframeAPIReady?: () => void;
  }
}
let api: Promise<void> | null = null;
const loadApi = () =>
  (api ??= new Promise<void>((ok) => {
    if (window.YT?.Player) return ok();
    window.onYouTubeIframeAPIReady = () => ok();
    const s = document.createElement('script');
    s.src = 'https://www.youtube.com/iframe_api';
    document.head.appendChild(s);
  }));

/** The YouTube player, through its API, so that the board can follow it. */
function Player({ id, t, onTime, seek }: { id: string; t: number; onTime: (s: number) => void; seek: { t: number } | null }) {
  const el = useRef<HTMLDivElement>(null);
  const player = useRef<YTPlayer | null>(null);
  useEffect(() => {
    let alive = true;
    let tick = 0;
    loadApi().then(() => {
      if (!alive || !el.current || !window.YT) return;
      player.current = new window.YT.Player(el.current, {
        videoId: id,
        host: 'https://www.youtube-nocookie.com',
        playerVars: { start: t, autoplay: 1, rel: 0 },
      });
      tick = window.setInterval(() => {
        const s = player.current?.getCurrentTime?.();
        if (typeof s === 'number') onTime(Math.floor(s));
      }, 500);
    });
    return () => {
      alive = false;
      clearInterval(tick);
      player.current?.destroy();
      player.current = null;
    };
  }, [id, t, onTime]);
  useEffect(() => {
    if (seek) player.current?.seekTo(seek.t, true);
  }, [seek]);
  return <div ref={el} className="h-full w-full" />;
}


/**
 * The Buffalo lectures of 1973: Grothendieck's three courses at the State
 * University of New York at Buffalo, from April to July 1973, as Erwin
 * The « Erwin Schulhoff » channel (a pseudonym) published the tapes on YouTube (John Duskin's and William
 * Lawvere's copies). The page lists every tape side with its date, from the
 * videos' own descriptions, and plays it from YouTube at that point. No sound
 * is copied, and nothing of the lectures is transcribed here.
 *
 * `#URU5jgTvjhU@2951` opens a video at a given second, as the Conferences tab
 * of the morphology site does.
 */

interface Segment {
  start: number;
  date: string | null;
  tape: string;
  bad: boolean;
  /** Set where the edition dated a new session found inside a side. */
  note?: string;
}
interface Video {
  id: string;
  part: number;
  of: number;
  title: string;
  duration: number;
  segments: Segment[];
}
interface Course {
  id: string;
  title: string;
  videos: Video[];
}
const CAT = catalogueRaw as unknown as { built: string; courses: Course[] };

const hms = (s: number) =>
  [Math.floor(s / 3600), Math.floor((s % 3600) / 60), s % 60].map((x, i) => (i ? String(x).padStart(2, '0') : x)).join(':');
const DAY = new Intl.DateTimeFormat('en-GB', { day: 'numeric', month: 'long', timeZone: 'UTC' });
const day = (d: string) => DAY.format(new Date(`${d}T00:00:00Z`));
const hours = (c: Course) => Math.round(c.videos.reduce((n, v) => n + v.duration, 0) / 3600);
const TOTAL = Math.round(CAT.courses.reduce((n, c) => n + c.videos.reduce((m, v) => m + v.duration, 0), 0) / 3600);

const SEGMENTS = (c: Course) => c.videos.flatMap((v) => v.segments);
const SIDES = CAT.courses.reduce((n, c) => n + SEGMENTS(c).length, 0);
// A session is a course on a day; most fill two to four tape sides.
const SESSIONS = CAT.courses.reduce((n, c) => n + new Set(SEGMENTS(c).flatMap((s) => (s.date ? [s.date] : []))).size, 0);

function fromHash(): { id: string; t: number } | null {
  const m = /^#([\w-]{11})(?:@(\d+))?$/.exec(location.hash);
  return m ? { id: m[1], t: Number(m[2] ?? 0) } : null;
}

const link = 'font-medium text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700';

// The index of results of each course, in our own words: docs/buffalo-*/index.tex, read into
// src/content/buffalo-index.json by scripts/buffalo-index.mjs (the PDF is compiled from the same .tex).
type IndexItem =
  | { k: 'topic'; text: string }
  | { k: 'session'; text: string }
  | { k: 'side'; text: string }
  | { k: 'entry'; v: string; t: number; ts: string; text: string; kind?: Kind; name?: string };
type Kind = 'def' | 'thm' | 'prop' | 'ex' | 'cex' | 'rem' | 'q' | 'disc';
// The kinds of entry, labelled as in a course; the colours are those of the PDF.
const KIND: Record<Kind, { label: string; color: string; italic?: boolean }> = {
  def: { label: 'Definition', color: '#2E6B3F' },
  thm: { label: 'Theorem', color: '#2F4DA8', italic: true },
  prop: { label: 'Proposition', color: '#2F4DA8', italic: true },
  ex: { label: 'Example', color: '#8A5A00' },
  cex: { label: 'Counterexample', color: '#A8322F' },
  rem: { label: 'Remark', color: '#5E5E5E' },
  q: { label: 'Question', color: '#6B3FA0' },
  disc: { label: 'Discussion', color: '#0F766E' },
};
type CourseIndex = { pdf: string; entries: number; items: IndexItem[] };
const loadIndex = () => import('./content/buffalo-index.json').then((m) => m.default as unknown as Record<string, CourseIndex>);

const tex = (s: string) => katex.renderToString(s, { throwOnError: false });
const statement = (s: string) => s.split(/(\$[^$]*\$)/).map((p) => (p.startsWith('$') ? tex(p.slice(1, -1)) : p)).join('');

/*
 * A course index holds hundreds of entries and thousands of formulas; typesetting them all at once froze
 * the page (about 65,000 elements, several long tasks). An entry with a formula shows its plain text
 * until it comes within a screen or two of the viewport, and is typeset then, by one shared observer.
 */
const waiting = new Map<Element, () => void>();
let near: IntersectionObserver | null = null;
const whenNear = (el: Element, run: () => void) => {
  near ??= new IntersectionObserver(
    (es) =>
      es.forEach((e) => {
        if (!e.isIntersecting) return;
        const f = waiting.get(e.target);
        waiting.delete(e.target);
        near?.unobserve(e.target);
        f?.();
      }),
    { rootMargin: '1500px 0px' },
  );
  waiting.set(el, run);
  near.observe(el);
};
const plain = (s: string) => s.replace(/<[^>]+>/g, '');

/** Text whose $…$ is typeset when it is about to be seen. */
function Typeset({ text, prefix = '' }: { text: string; prefix?: string }) {
  const hasMath = text.includes('$');
  const [on, setOn] = useState(!hasMath);
  const ref = useRef<HTMLSpanElement>(null);
  useEffect(() => {
    const el = ref.current;
    if (on || !el) return;
    whenNear(el, () => setOn(true));
    return () => {
      waiting.delete(el);
      near?.unobserve(el);
    };
  }, [on]);
  return on ? <span dangerouslySetInnerHTML={{ __html: prefix + statement(text) }} /> : <span ref={ref}>{prefix + plain(text)}</span>;
}

/** One course's index, typeset like the transcripts' reading view; a timestamp plays the tape there. */
function CourseIndexView({ course, index, playing, onPlay }: { course: string; index: CourseIndex; playing: { id: string; t: number } | null; onPlay: (id: string, t: number) => void }) {
  // Select words in an entry to comment on them in a prefilled issue, as on the reading view.
  const root = useComments<HTMLDivElement>('buffalo', `Buffalo — ${course}`);
  return (
    <div ref={root} className="buffalo-index text-[14.5px] leading-relaxed text-ink-800">
      {index.items.map((i, n) =>
        i.k === 'topic' ? (
          <h3 key={n} className="titre mt-8 border-b border-ink-200 pb-1 text-[18px] text-ink-900 first:mt-0">
            <Typeset text={i.text} />
          </h3>
        ) : i.k === 'session' ? (
          <p key={n} className="mt-5 text-[12px] font-semibold uppercase tracking-[0.06em] text-brand-600">
            <Typeset text={i.text} />
          </p>
        ) : i.k === 'side' ? (
          <p key={n} className="mt-2 text-[12px] italic text-ink-500">
            <Typeset text={i.text} />
          </p>
        ) : (
          <div
            key={n}
            className="group mt-1.5 grid grid-cols-[4.6rem_minmax(0,1fr)_1.5rem] gap-2 [contain-intrinsic-size:auto_2.4rem] [content-visibility:auto]"
            {...commentData({ kind: 'lecture', label: `Buffalo, ${course}, ${i.ts}`, ref: i.ts, link: `https://www.youtube.com/watch?v=${i.v}&t=${i.t}s` })}
          >
            <button
              type="button"
              onClick={() => onPlay(i.v, i.t)}
              aria-current={playing?.id === i.v && playing.t === i.t ? 'true' : undefined}
              title="Play the tape from here"
              className="tabular self-start rounded px-1 py-0.5 text-left font-mono text-[12px] text-brand-600 hover:bg-brand-50 aria-[current=true]:bg-brand-100"
            >
              {i.ts}
            </button>
            <p className={i.kind && KIND[i.kind]?.italic ? 'italic' : undefined}>
              {i.kind && KIND[i.kind] && (
                <b className="mr-1.5 not-italic" style={{ color: KIND[i.kind].color }}>
                  {KIND[i.kind].label}
                  {i.name && <span dangerouslySetInnerHTML={{ __html: ` (${statement(i.name)})` }} />}.
                </b>
              )}
              <Typeset text={i.text} />
            </p>
            <a
              href={buffaloIssueUrl(course, i)}
              target="_blank"
              rel="noopener noreferrer"
              title="Report a problem with this entry (opens a GitHub issue)"
              aria-label="Report a problem with this entry"
              className="self-start pt-0.5 text-center text-[13px] text-ink-300 opacity-0 transition hover:text-brand-600 focus:opacity-100 group-hover:opacity-100"
            >
              ⚑
            </a>
          </div>
        ),
      )}
    </div>
  );
}

export function BuffaloPage() {
  const [playing, setPlaying] = useState(fromHash);
  useEffect(() => {
    const onHash = () => setPlaying(fromHash());
    addEventListener('hashchange', onHash);
    return () => removeEventListener('hashchange', onHash);
  }, []);
  const play = (id: string, t: number) => {
    history.replaceState(null, '', `#${id}@${t}`);
    setPlaying({ id, t });
  };
  const video = playing && CAT.courses.flatMap((c) => c.videos).find((v) => v.id === playing.id);
  const [course, setCourse] = useState(() => CAT.courses.find((c) => c.videos.some((v) => v.id === fromHash()?.id))?.id ?? CAT.courses[0].id);
  const [indexes, setIndexes] = useState<Record<string, CourseIndex> | null>(null);
  useEffect(() => {
    loadIndex().then(setIndexes);
  }, []);
  const close = () => {
    history.replaceState(null, '', location.pathname);
    setPlaying(null);
  };
  useEffect(() => {
    if (!playing) return;
    const onKey = (e: KeyboardEvent) => e.key === 'Escape' && close();
    addEventListener('keydown', onKey);
    return () => removeEventListener('keydown', onKey);
  }, [playing]);
  const [now, setNow] = useState(0);
  const [seek, setSeek] = useState<{ t: number } | null>(null);
  const [board, setBoard] = useState<Board | null>(null);
  const side = video && playing ? sideOf(video, Math.max(now, playing.t)) : null;
  useEffect(() => {
    const key = video && side !== null ? `${video.id}-${String(side).padStart(4, '0')}` : null;
    if (!key) return setBoard(null);
    let alive = true;
    const local = (k: string): Promise<Board | null> =>
      fetch(`/buffalo-boards/${k}.json`).then((r) =>
        r.ok && r.headers.get('content-type')?.includes('json') ? r.json() : null,
      );
    // A « Tape 2, cont. » segment of the catalogue lies inside the previous side's board.
    const prev = video ? video.segments.filter((s) => s.start < (side ?? 0)).at(-1)?.start : undefined;
    const load: Promise<Board | null> =
      key in PUBLIC_BOARDS
        ? PUBLIC_BOARDS[key]().then((m) => m.default as Board)
        : local(key).then((b) =>
            b || prev === undefined ? b : local(`${video!.id}-${String(prev).padStart(4, '0')}`),
          );
    load.then((b) => alive && setBoard(b)).catch(() => alive && setBoard(null));
    return () => {
      alive = false;
    };
  }, [video, side]);

  return (
    <>
      <Header path="/buffalo/" />
      <main className="mx-auto max-w-6xl px-5 py-12">
        <header className="max-w-[46em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.11em] text-brand-600">Buffalo</p>
          <h1 className="titre mt-2 text-[34px] leading-[1.1] text-ink-900">The Buffalo lectures, 1973</h1>
          <p className="mt-4 text-[15px] leading-relaxed text-ink-600">
            From April to July 1973, Grothendieck taught three courses at the State University of New York at
            Buffalo: topos theory, algebraic geometry and the theory of algebraic groups. The tapes were kept by
            John Duskin and William Lawvere, and published in ten videos by the YouTube channel « Erwin Schulhoff » in October 2025. Each
            tape side is listed below with its date and plays from YouTube.
          </p>
          <p className="tabular mt-3 text-[14px] text-ink-700">
            {CAT.courses.length} courses, {SESSIONS} dated sessions on {SIDES} tape sides, {CAT.courses.reduce((n, c) => n + c.videos.length, 0)}{' '}
            videos, about {TOTAL} hours.
          </p>
        </header>

        <aside className="mt-6 max-w-[46em] rounded-xl border border-ink-200 bg-ink-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          The recordings are on the « Erwin Schulhoff » YouTube channel and are played from there; no sound is copied
          to this site, and the lectures are not transcribed here. Beside the player, a blackboard gives notes of
          what was probably written on the board: formulas, statements and steps, in our wording, reconstructed
          from the recordings (automatic captions and speech recognition), not from the board itself. The « bad tape » marks come from the videos'
          descriptions. For the content of the topos course, see Colin McLarty,{' '}
          <a href="https://www.youtube.com/watch?v=5AR55ZsHmKI" target="_blank" rel="noopener noreferrer" className={link}>
            « Grothendieck's 1973 Topos Lectures » ↗
          </a>{' '}
          (ENS, 2018). Montpellier folder 161-4, pp. 22–31, may be notes for the algebraic geometry course; that
          is not checked.
        </aside>

        <details className="mt-3 max-w-[46em] rounded-xl border border-ink-200 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          <summary className="cursor-pointer select-none font-medium text-brand-600 hover:text-brand-700">Who speaks on the tapes</summary>
          <p className="mt-2">
            The recordings do not name the voices in the room. Colin McLarty, who was not there (he gave his talk in 2018), names a few
            from what is said, and we add two inferences of our own.
          </p>
          <ul className="mt-2 list-disc space-y-1.5 pl-5">
            <li>
              <strong className="font-semibold">John Duskin</strong>, who made the tapes, asks whether the universe axiom could be shown
              consistent relative to ZFC; Grothendieck answers that, about ten years earlier, logicians he had asked saw no hope. Video 4,{' '}
              <a href="#ORG14LNb5gE@18997" className={link}>
                5:16:37
              </a>
              . A little earlier in the same video, at{' '}
              <a href="#ORG14LNb5gE@15688" className={link}>
                4:21:28
              </a>
              , someone says Jack understands more than the others and asks him to go to the blackboard: probably Duskin too, our inference, not McLarty's.
            </li>
            <li>
              <strong className="font-semibold">William Lawvere</strong> is credited by McLarty with having helped save the tapes. In video 1,
              Grothendieck compares his own definition of a topos with Lawvere and Tierney's and says he does not know their theory well, at{' '}
              <a href="#URU5jgTvjhU@36055" className={link}>
                10:00:55
              </a>
              .
            </li>
            <li>
              <strong className="font-semibold">An unnamed speaker</strong> remarks in the same discussion that some infinite cardinals
              do not really exist; McLarty places it in a conversation about the Whitehead conjecture.
            </li>
          </ul>
          <p className="mt-2">
            McLarty dates the last topos session, with the news that Deligne has proved the Weil conjectures, to 13 July 1973; the videos'
            descriptions, which our catalogue follows, put the whole of video 4 under 12 July. He counts 33 hours of topos tapes, about 16
            hours of introduction and 17 with a smaller group; our catalogue has {hours(CAT.courses.find((c) => c.id === 'topos')!)} hours for the course, damaged sides included.
            The identifications above are readings of what is said, not labels on the tapes.
          </p>
        </details>

        <nav className="mt-8 flex flex-wrap gap-2" aria-label="Courses">
          {CAT.courses.map((c) => (
            <button
              key={c.id}
              type="button"
              onClick={() => setCourse(c.id)}
              aria-pressed={course === c.id}
              className="rounded-lg border border-ink-200 px-3 py-1 text-[12.5px] text-ink-700 hover:border-brand-500 hover:bg-brand-50 aria-pressed:border-brand-500 aria-pressed:bg-brand-50 aria-pressed:font-semibold"
            >
              {c.title} · {hours(c)} h
            </button>
          ))}
        </nav>

        {CAT.courses
          .filter((c) => c.id === course)
          .map((c) => (
            <section key={c.id} id={c.id} className={`mt-6 grid gap-8 ${board ? 'lg:grid-cols-[minmax(0,1fr)_520px]' : 'lg:grid-cols-[minmax(0,1fr)_360px]'}`}>
              <div className="min-w-0">
                <h2 className="titre text-[24px] text-ink-900">{c.title}</h2>
                <p className="mt-2 max-w-[46em] text-[13px] leading-relaxed text-ink-600">
                  Index of results: one line per result, definition or example, in our own words, with the moment of
                  the tape; an index, not a transcription. Entries marked Discussion point to an exchange with the audience.
                  {indexes?.[c.id] && (
                    <>
                      {' '}
                      {indexes[c.id].entries} entries ·{' '}
                      <a href={indexes[c.id].pdf} target="_blank" rel="noopener noreferrer" className={link}>
                        PDF
                      </a>{' '}
                      ·{' '}
                      <a href={buffaloIssueUrl(c.title)} target="_blank" rel="noopener noreferrer" className={link}>
                        Report a problem
                      </a>
                    </>
                  )}
                </p>

                <details className="mt-4 rounded-xl border border-ink-200 px-4 py-2">
                  <summary className="cursor-pointer text-[13px] font-semibold text-ink-800">
                    Tape sides ({SEGMENTS(c).length})
                  </summary>
                  {c.videos.map((v) => (
                    <div key={v.id} className="mt-3">
                      <p className="text-[12.5px] font-semibold text-ink-800">
                        Part {v.part} of {v.of} · {hms(v.duration)}{' '}
                        <a href={`https://www.youtube.com/watch?v=${v.id}`} target="_blank" rel="noopener noreferrer" className={`ml-1 text-[12px] ${link}`}>
                          YouTube ↗
                        </a>
                      </p>
                      <ul className="mt-1.5 grid gap-1.5 sm:grid-cols-2">
                        {v.segments.map((s) => (
                          <li key={s.start}>
                            <button
                              type="button"
                              onClick={() => play(v.id, s.start)}
                              title={s.note}
                              aria-current={playing?.id === v.id && playing.t === s.start ? 'true' : undefined}
                              className="flex w-full items-baseline justify-between gap-2 rounded-lg border border-ink-200 px-3 py-1.5 text-left text-[12px] text-ink-700 hover:border-brand-500 hover:bg-brand-50 aria-[current=true]:border-brand-500 aria-[current=true]:bg-brand-50"
                            >
                              <span>
                                <span className="font-medium text-ink-900">{s.date ? day(s.date) : 'Undated'}</span> · {s.tape}
                                {s.bad && <span className="text-ink-400"> · bad tape</span>}
                                {s.note && <span className="text-ink-400"> · new session</span>}
                              </span>
                              <span className="tabular shrink-0 text-[11px] text-ink-400">{hms(s.start)}</span>
                            </button>
                          </li>
                        ))}
                      </ul>
                    </div>
                  ))}
                </details>

                <div className="mt-6">
                  {indexes?.[c.id] ? (
                    <CourseIndexView course={c.title} index={indexes[c.id]} playing={playing} onPlay={play} />
                  ) : (
                    <p className="text-[13px] text-ink-400">Loading the index…</p>
                  )}
                </div>
              </div>

              {/* The player, as on the morphology site: sticky beside the index on a large screen, so one reads and
                  listens at once; anchored to the bottom on a phone. */}
              <aside>
                {video && playing ? (
                  <div className="fixed inset-x-0 bottom-0 z-40 border-t border-ink-200 bg-white lg:sticky lg:inset-x-auto lg:bottom-auto lg:top-20 lg:z-auto lg:flex lg:flex-col lg:gap-3 lg:border-0 lg:bg-transparent">
                    {/* The reconstructed blackboard, where one exists for the side being played: on top and wide, since
                        the video is a still photograph over the sound. */}
                    {board && (
                      <div className="hidden h-[64vh] lg:block">
                        <Suspense fallback={null}>
                          <Blackboard board={board} now={now} onSeek={(s) => setSeek({ t: s })} />
                        </Suspense>
                      </div>
                    )}
                    <div className={`overflow-hidden bg-ink-900 lg:rounded-xl ${board ? 'lg:ml-auto lg:w-[300px]' : ''}`}>
                      <div className="aspect-video w-full">
                        <Player id={playing.id} t={playing.t} onTime={setNow} seek={seek} />
                      </div>
                      <div className="flex items-center gap-2 px-3 py-1.5">
                        <p className="min-w-0 flex-1 truncate text-[12.5px] text-ink-100">
                          {video.title}, from {hms(playing.t)}
                        </p>
                        <button
                          type="button"
                          onClick={close}
                          aria-label="Stop the video"
                          title="Stop the video (Esc)"
                          className="flex h-8 w-8 shrink-0 items-center justify-center rounded-full border border-white/30 text-[13px] text-white/75 hover:bg-white/15"
                        >
                          ✕
                        </button>
                      </div>
                    </div>
                  </div>
                ) : (
                  <div className="sticky top-20 hidden rounded-xl border border-dashed border-ink-300 px-4 py-5 text-[13px] leading-relaxed text-ink-500 lg:block">
                    <p className="font-semibold text-ink-700">The player opens here</p>
                    <p className="mt-1">Click a timestamp: the tape plays from that moment beside the index.</p>
                  </div>
                )}
                {video && playing && <div aria-hidden="true" className="lg:hidden" style={{ height: 'calc(56.25vw + 2.75rem)' }} />}
              </aside>
            </section>
          ))}

        <p className="mt-10 text-[12px] text-ink-400">
          Grothendieck at Buffalo 1973, tapes preserved and transmitted by John Duskin and William Lawvere,
          published by the « Erwin Schulhoff » YouTube channel on 27 October 2025. Tape list read from the videos'
          descriptions on {CAT.built}.
        </p>
      </main>
      <Footer collection="buffalo" />
    </>
  );
}
