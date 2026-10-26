#!/usr/bin/env python3
"""Compile enum.c, run the three enumerations and the analysis, and write
results.txt.  Usage:

    python3 run.py              # all n<=9, simple n<=9, avoid n<=16 (~5 min)
    python3 run.py --simple10   # also the 312356 simple arrangements of 10
                                # pseudolines (~6 more minutes)
    python3 run.py --quick      # all n<=8 only (seconds)

The per-class files go to out/ (about 45 MB for n=9; not versioned).
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'out')
BIN = os.path.join(OUT, 'enum')

KNOWN_ALL = {3: 1, 4: 2, 5: 4, 6: 17, 7: 143, 8: 4890, 9: 461053}
KNOWN_SIMPLE = {3: 1, 4: 1, 5: 1, 6: 4, 7: 11, 8: 135, 9: 4382, 10: 312356}


def sh(args):
    t = time.time()
    r = subprocess.run(args, capture_output=True, text=True, check=True)
    return r.stdout, time.time() - t


def table(stdout):
    rows = {}
    for line in stdout.splitlines():
        f = line.split()
        if f and f[0].isdigit():
            rows[int(f[0])] = [int(x) for x in f[1:]]
    return rows


def main():
    quick = '--quick' in sys.argv
    nall = 8 if quick else 9
    nsimple = 10 if '--simple10' in sys.argv else (8 if quick else 9)
    os.makedirs(OUT, exist_ok=True)
    subprocess.run(['gcc', '-O2', '-Wall', '-Wextra', '-o', BIN,
                    os.path.join(HERE, 'enum.c')], check=True)
    report = []
    for mode, nmax, known in (('all', nall, KNOWN_ALL),
                              ('simple', nsimple, KNOWN_SIMPLE),
                              ('avoid', 16, None)):
        out, dt = sh([BIN, mode, str(nmax), OUT])
        report.append(out.rstrip() + f'\n(time {dt:.1f} s)\n')
        if known:
            for n, row in table(out).items():
                assert row[0] == known[n], (mode, n, row[0], known[n])
            report.append(f'counts agree with the known values for n<={nmax}\n')
        print(report[-2], report[-1] if known else '', sep='', flush=True)
    out, dt = sh([sys.executable, os.path.join(HERE, 'analyse.py'), OUT, 'all']
                 + [str(n) for n in range(4, nall + 1)])
    report.append('analysis of the bigon-free classes (mode all):\n' + out
                  + f'(time {dt:.1f} s)\n')
    out, dt = sh([sys.executable, os.path.join(HERE, 'analyse.py'), OUT,
                  'simple', str(nsimple)])
    report.append(f'analysis of the simple classes, n={nsimple}:\n' + out
                  + f'(time {dt:.1f} s)\n')
    print(''.join(report[-2:]))
    with open(os.path.join(HERE, 'results.txt'), 'w') as fp:
        fp.write('\n'.join(report))


if __name__ == '__main__':
    main()
