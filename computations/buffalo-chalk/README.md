# Chalk taps on the Buffalo 1973 tapes (#109)

`taps.json` lists chalk-tap candidates for 115 tape sides of the three 1973 courses (34,842 candidates), in seconds of the YouTube videos of `src/content/buffalo.json`. They were detected on a local copy of the audio split by tape side; its side lengths match the segment boundaries of `buffalo.json`, which gives the alignment. The audio itself was deleted after each side, and only times are kept.

- `taps.py`: the detector. A tap is a jump of at least 12 dB of the 3–7.5 kHz band over its running median, shorter than 40 ms, close to the level of the voice band. The output was checked by ear on Topos, 4 April 1973, tape 1 side A, and was mostly right. The same test for erasing gave mostly false positives and is not used.
- **Corrections:**
  - One boundary is 20 s late in `buffalo.json` (Topos, 4 April, tape 2, between sides A and B); side B is shifted to match.
  - Some files hold a whole tape longer than its segment; their taps after the segment end are dropped.
  - Two undated sides were placed by transcribing clips with Whisper and matching them to the captions; they agree with `buffalo.json`.
  - One undated file of the algebraic groups course could not be placed and is left out.
- **Use:** `npm run buffalo-boards` groups taps 4 s apart or less into bursts of at least three. It gives each board item a writing time `w`, the burst start nearest to its spoken time within −20 s to +10 s. On 4,302 items, 1,415 are timed this way: the median shift is −3 s, and 80 % fall between −15 s and +7 s.
