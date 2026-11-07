"""CI time of the repository, job by job, from the GitHub API (#121, #123).

usage: python3 computations/ci/ci_time.py [OWNER/REPO] > jobs.tsv
       python3 computations/ci/ci_time.py --summary jobs.tsv

Writes one line per job: run id, workflow, date, job, seconds. GitHub keeps job
data for recent runs only, so older runs may be missing; the summary says how
many runs had data. Needs the gh CLI, authenticated.
"""
import collections, datetime as d, json, math, subprocess, sys


def gh(path):
    r = subprocess.run(['gh', 'api', path], capture_output=True, text=True)
    return json.loads(r.stdout) if r.returncode == 0 else None


def iso(x):
    return d.datetime.fromisoformat(x.replace('Z', '+00:00'))


def collect(repo):
    runs, page = [], 1
    while page <= 100:
        r = gh(f'repos/{repo}/actions/runs?per_page=100&page={page}')
        if not r or not r['workflow_runs']:
            break
        runs += r['workflow_runs']
        page += 1
    print(f'# {len(runs)} runs', file=sys.stderr)
    for run in runs:
        j = gh(f"repos/{repo}/actions/runs/{run['id']}/jobs?per_page=100")
        for job in (j or {}).get('jobs', []):
            if job.get('started_at') and job.get('completed_at'):
                sec = int((iso(job['completed_at']) - iso(job['started_at'])).total_seconds())
                print(run['id'], run['name'], run['created_at'][:10], job['name'], sec, sep='\t', flush=True)


def summary(path):
    rows = [l.rstrip('\n').split('\t') for l in open(path) if not l.startswith('#')]
    secs = [int(r[4]) for r in rows]
    print(f'{len(rows)} jobs in {len({r[0] for r in rows})} runs: {sum(secs) / 3600:.1f} h '
          f'({sum(math.ceil(s / 60) for s in secs) / 60:.1f} h rounded up per minute)')
    by_wf, by_week = collections.Counter(), collections.Counter()
    for r in rows:
        by_wf[r[1]] += int(r[4])
        y, w, _ = d.date.fromisoformat(r[2]).isocalendar()
        by_week[f'{y}-W{w:02d}'] += int(r[4])
    for k, v in by_wf.most_common():
        print(f'  {k}: {v / 3600:.1f} h')
    for k in sorted(by_week):
        print(f'  {k}: {by_week[k] / 3600:.1f} h')


if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[1] == '--summary':
        summary(sys.argv[2])
    else:
        collect(sys.argv[1] if len(sys.argv) > 1 else 'Commutator-IO/grothendieck-project')
