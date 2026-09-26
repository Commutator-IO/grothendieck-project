// The whole fonds moved to the root on 26 September 2026. /archive/ stays as a
// door to it, because every link posted before then — issues, the notebooks'
// « open in the fonds » links, citations — carries /archive/#<folder>/<batch>,
// and the fragment is the part that matters.
location.replace(`/${location.search}${location.hash}`);
