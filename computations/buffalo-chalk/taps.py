"""Chalk-tap candidates in a Buffalo 1973 tape side (#109).

usage: python taps.py SIDE.wav  ->  one time per line, in seconds from the start of the side

A tap is a jump of at least 12 dB of the 3-7.5 kHz band over its 1-second running median,
shorter than 40 ms, with the high band within 6 dB of the voice band (150-1000 Hz). Checked
by ear on a sample (Topos, 4 April 1973, tape 1 side A): mostly real taps. The same test for
erasing (long, flat high-band noise) gave mostly false positives and is not used.
"""
import sys
import numpy as np
from scipy.io import wavfile
from scipy.ndimage import median_filter
from scipy.signal import butter, sosfilt


def taps(path):
    sr, x = wavfile.read(path)
    x = x.astype(np.float32) / 32768
    hop = int(0.005 * sr)

    def env(lo, hi):
        y = sosfilt(butter(4, [lo, hi], btype='band', fs=sr, output='sos'), x)
        n = len(y) // hop
        return 20 * np.log10(np.sqrt((y[:n * hop].reshape(n, hop) ** 2).mean(1) + 1e-12))

    hi, sp = env(3000, 7500), env(150, 1000)
    d = hi - median_filter(hi, size=200)
    out, i = [], 0
    while i < len(d):
        if d[i] > 12 and d[max(i - 1, 0)] < 6:
            j = i
            while j < len(d) and d[j] > 6:
                j += 1
            if j - i <= 8 and hi[i] > sp[i] - 6:
                out.append(round(i * hop / sr, 2))
            i = j
        i += 1
    return out, len(x) / sr


if __name__ == '__main__':
    ts, dur = taps(sys.argv[1])
    print(f'# duration {dur:.2f}')
    print('\n'.join(map(str, ts)))
