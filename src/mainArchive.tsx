// The whole fonds moved to the root on 26 September 2026, and on to /fonds/ on 2 November. /archive/ stays as a
// door to it, because every link posted before then — issues, the notebooks'
// « open in the fonds » links, citations — carries /archive/#<folder>/<batch>,
// and the fragment is the part that matters.
location.replace(`/fonds/${location.search}${location.hash}`);
