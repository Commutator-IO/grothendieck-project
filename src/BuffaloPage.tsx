import { lazy, Suspense, useEffect, useRef, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import catalogueRaw from './content/buffalo.json';
import type { Board } from './components/Blackboard.tsx';

// The reconstructed boards (git-ignored transcripts-buffalo/) are shown only
// with RENDER_BUFFALO and in the dev server, with one exception: the first
// tape side of the topos course, published as a demonstration (2026-10-22).
const RENDER_BUFFALO = import.meta.env.DEV || import.meta.env.VITE_RENDER_BUFFALO === 'true';
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
    window.scrollTo({ top: 0, behavior: 'smooth' });
  };
  const video = playing && CAT.courses.flatMap((c) => c.videos).find((v) => v.id === playing.id);
  const [now, setNow] = useState(0);
  const [seek, setSeek] = useState<{ t: number } | null>(null);
  const [board, setBoard] = useState<Board | null>(null);
  const side = video && playing ? sideOf(video, Math.max(now, playing.t)) : null;
  useEffect(() => {
    const key = video && side !== null ? `${video.id}-${String(side).padStart(4, '0')}` : null;
    if (!key || (!RENDER_BUFFALO && !(key in PUBLIC_BOARDS))) return setBoard(null);
    let alive = true;
    const load: Promise<Board | null> =
      key in PUBLIC_BOARDS
        ? PUBLIC_BOARDS[key]().then((m) => m.default as Board)
        : fetch(`/transcripts-buffalo/${key}.json`).then((r) =>
            r.ok && r.headers.get('content-type')?.includes('json') ? r.json() : null,
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
            John Duskin and William Lawvere, and published in ten videos by the YouTube channel « Erwin Schulhoff » in October 2025. This
            page lists each tape side with its date, and plays it from YouTube.
          </p>
          <p className="tabular mt-3 text-[14px] text-ink-700">
            {CAT.courses.length} courses, {SESSIONS} dated sessions on {SIDES} tape sides, {CAT.courses.reduce((n, c) => n + c.videos.length, 0)}{' '}
            videos, about {TOTAL} hours.
          </p>
        </header>

        <aside className="mt-6 max-w-[46em] rounded-xl border border-ink-200 bg-ink-50 px-4 py-3 text-[13px] leading-relaxed text-ink-700">
          The recordings are on the « Erwin Schulhoff » YouTube channel and are played from there; no sound is copied
          to this site, and the lectures are not transcribed here, with one exception: as a demonstration, the
          first tape side of the topos course (4 April, from 0:00:00) opens beside a blackboard reconstructed from
          the recording's automatic captions. Tape sides marked « bad tape » are so marked
          in the videos' descriptions. For the content of the topos course, see Colin McLarty,{' '}
          <a href="https://www.youtube.com/watch?v=5AR55ZsHmKI" target="_blank" rel="noopener noreferrer" className={link}>
            « Grothendieck's 1973 Topos Lectures » ↗
          </a>{' '}
          (ENS, 2018). Montpellier folder 161-4, pp. 22–31, may be notes for the algebraic geometry course; that
          is not checked.
        </aside>

        {video && playing && (
          <section className="mt-8" aria-label="Player">
            <div className="flex items-baseline justify-between gap-3">
              <p className="text-[13px] font-semibold text-ink-800">
                {video.title}, from {hms(playing.t)}
              </p>
              <button
                type="button"
                onClick={() => {
                  history.replaceState(null, '', location.pathname);
                  setPlaying(null);
                }}
                className="rounded-lg border border-ink-200 px-2.5 py-1 text-[12px] text-ink-600 hover:bg-ink-50"
              >
                Close
              </button>
            </div>
            {/* The videos are a still photograph over the sound, so the board gets the room. */}
            <div className={`mt-2 grid gap-4 ${board ? 'lg:grid-cols-[minmax(0,2fr)_minmax(0,3fr)]' : ''}`}>
              <div className="aspect-video w-full self-start overflow-hidden rounded-xl border border-ink-200 bg-ink-900">
                <Player id={playing.id} t={playing.t} onTime={setNow} seek={seek} />
              </div>
              {board && (
                <div className="h-[70vh]">
                  <Suspense fallback={null}>
                    <Blackboard board={board} now={now} onSeek={(s) => setSeek({ t: s })} />
                  </Suspense>
                </div>
              )}
            </div>
          </section>
        )}

        <nav className="mt-8 flex flex-wrap gap-2" aria-label="Courses">
          {CAT.courses.map((c) => (
            <a
              key={c.id}
              href={`#${c.id}`}
              onClick={(e) => {
                e.preventDefault();
                document.getElementById(c.id)?.scrollIntoView({ behavior: 'smooth' });
              }}
              className="rounded-lg border border-ink-200 px-3 py-1 text-[12.5px] text-ink-700 hover:border-brand-500 hover:bg-brand-50"
            >
              {c.title} · {hours(c)} h
            </a>
          ))}
        </nav>

        {CAT.courses.map((c) => (
          <section key={c.id} id={c.id} className="mt-10 scroll-mt-20">
            <h2 className="titre text-[22px] text-ink-900">{c.title}</h2>
            {c.videos.map((v) => (
              <div key={v.id} className="mt-5">
                <p className="text-[13.5px] font-semibold text-ink-800">
                  Part {v.part} of {v.of} · {hms(v.duration)}{' '}
                  <a href={`https://www.youtube.com/watch?v=${v.id}`} target="_blank" rel="noopener noreferrer" className={`ml-1 text-[12px] ${link}`}>
                    YouTube ↗
                  </a>
                </p>
                <ul className="mt-2 grid gap-1.5 sm:grid-cols-2 lg:grid-cols-3">
                  {v.segments.map((s) => (
                    <li key={s.start}>
                      <button
                        type="button"
                        onClick={() => play(v.id, s.start)}
                        aria-current={playing?.id === v.id && playing.t === s.start ? 'true' : undefined}
                        className="flex w-full items-baseline justify-between gap-2 rounded-lg border border-ink-200 px-3 py-1.5 text-left text-[12.5px] text-ink-700 hover:border-brand-500 hover:bg-brand-50 aria-[current=true]:border-brand-500 aria-[current=true]:bg-brand-50"
                      >
                        <span>
                          <span className="font-medium text-ink-900">{s.date ? day(s.date) : 'Undated'}</span> · {s.tape}
                          {s.bad && <span className="text-ink-400"> · bad tape</span>}
                        </span>
                        <span className="tabular shrink-0 text-[11.5px] text-ink-400">{hms(s.start)}</span>
                      </button>
                    </li>
                  ))}
                </ul>
              </div>
            ))}
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
