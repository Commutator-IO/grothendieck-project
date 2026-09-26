/**
 * The carousel of the galleries (diagrams, formulas): one figure at a time,
 * previous and next, the arrow keys, a range to jump, #d<n> in the address.
 *
 * The page is a reading view (scripts/render.mjs's readingPage), so KaTeX and
 * the diagram renderer are already there; this adds the navigation, the
 * styles and the script that shows a figure and redraws its diagram.
 */
export const carouselNav = (n, label) =>
  `<nav class="dg-nav" aria-label="${label}">` +
  `<button type="button" id="dg-prev" aria-label="Précédent">‹</button>` +
  `<span class="dg-count"><span id="dg-i">1</span> / ${n}</span>` +
  `<input type="range" id="dg-range" min="1" max="${n}" value="1" aria-label="Aller à">` +
  `<button type="button" id="dg-next" aria-label="Suivant">›</button>` +
  `</nav>\n`;

export const CAROUSEL_STYLE = `
  /* A carousel: one figure at a time, the others kept out of the flow. */
  .dg { display: none; min-height: 22rem; }
  .dg.on { display: flex; flex-direction: column; }
  .dg .ltx_p { flex: 1; display: flex; align-items: center; justify-content: center; padding: 1.5rem 0; }
  .dg-nav { position: sticky; top: 0; z-index: 2; display: flex; align-items: center; gap: .75rem;
            margin: 0 0 .8rem; padding: .5rem 0; background: #fff; font-size: 13px; color: var(--ink3); }
  .dg-nav button { border: 1px solid var(--rule); background: #fff; border-radius: 999px; width: 2.2rem; height: 2.2rem;
                   font-size: 18px; line-height: 1; color: var(--ink2); cursor: pointer; }
  .dg-nav button:hover { background: var(--surf3); }
  .dg-nav button:disabled { opacity: .35; cursor: default; }
  .dg-nav input { flex: 1; accent-color: #128557; }
  .dg-count { font-variant-numeric: tabular-nums; min-width: 4.5rem; text-align: center; }`;

/**
 * The carousel: shows one figure, redraws its arrows, and follows the hash
 * (#d12), the arrow keys and the range. Registered after the reading view's
 * own DOMContentLoaded handler, which typesets the nodes and draws every
 * diagram — the hidden ones against no geometry, which is why the one shown
 * is drawn again here.
 */
export const SLIDES = `<script>
(function () {
  var figs, cur = 0;
  function show(i) {
    if (!figs.length) return;
    cur = Math.max(0, Math.min(figs.length - 1, i));
    figs.forEach(function (f, j) { f.classList.toggle('on', j === cur); });
    document.getElementById('dg-i').textContent = cur + 1;
    document.getElementById('dg-range').value = cur + 1;
    document.getElementById('dg-prev').disabled = cur === 0;
    document.getElementById('dg-next').disabled = cur === figs.length - 1;
    history.replaceState(null, '', '#d' + (cur + 1));
    var cd = figs[cur].querySelector('.tr-cd');
    if (cd && typeof drawDiagram === 'function') requestAnimationFrame(function () { drawDiagram(cd); });
  }
  document.addEventListener('DOMContentLoaded', function () {
    figs = Array.prototype.slice.call(document.querySelectorAll('.dg'));
    var m = /^#d(\\d+)$/.exec(location.hash);
    document.getElementById('dg-prev').onclick = function () { show(cur - 1); };
    document.getElementById('dg-next').onclick = function () { show(cur + 1); };
    document.getElementById('dg-range').oninput = function (e) { show(Number(e.target.value) - 1); };
    addEventListener('keydown', function (e) {
      if (e.key === 'ArrowLeft') show(cur - 1);
      if (e.key === 'ArrowRight') show(cur + 1);
    });
    addEventListener('resize', function () { show(cur); });
    show(m ? Number(m[1]) - 1 : 0);
  });
})();
</script>`;
export const withSlides = (page) => page.replace('</body>', `${SLIDES}</body>`);
