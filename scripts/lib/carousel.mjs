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
  `<button type="button" id="dg-prev" aria-label="Previous">‹</button>` +
  `<span class="dg-count"><span id="dg-i">1</span> / ${n}</span>` +
  `<input type="range" id="dg-range" min="1" max="${n}" value="1" aria-label="Go to">` +
  `<button type="button" id="dg-next" aria-label="Next">›</button>` +
  `</nav>\n`;

export const CAROUSEL_STYLE = `
  /* A carousel: one figure at a time, the others kept out of the flow. */
  /* Each slide its own stacking context. KaTeX paints some stretchy glyphs
     (the underbrace, the pieces of a tall brace) at a negative z-index, and
     under any slide background they came out as gaps and loose labels. The
     address says #d<n> and the slide's id is slide-<n>, so that ar5iv's
     :target highlight, yellow and blue, never fires on a slide. */
  .dg { isolation: isolate; background: #fff; }
  .dg { display: none; min-height: 22rem; }
  .dg.on { display: flex; flex-direction: column; }
  /* Centred by text alignment, not by flex: a flex container shrank KaTeX's
     stretchy braces (an underbrace, the tall brace of cases) to nothing, and
     centred what was too wide by cutting off its left side. As a block,
     what is wider than the slide overflows to the right and scrolls. */
  .dg .ltx_p { display: block; margin: auto 0; text-align: center; padding: 1.5rem 0; overflow-x: auto; }
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
    requestAnimationFrame(function () { fit(figs[cur]); });
  }
  /**
   * Shrink what is wider than the slide until it fits: a formula by its font
   * size (KaTeX is sized in em), a diagram by its font size and its gaps
   * together, so the arrows keep their proportions; then the diagram is
   * drawn. Never below half size — past that, the slide scrolls instead.
   */
  function fit(fig) {
    var box = fig.querySelector('.ltx_p');
    var cd = fig.querySelector('.tr-cd');
    var draw = function () { if (cd && typeof drawDiagram === 'function') drawDiagram(cd); };
    if (!box) return;
    var avail = box.clientWidth - 8;
    if (cd) {
      var grid = cd.querySelector('.tr-cd-grid');
      if (!cd.dataset.fs) { cd.dataset.fs = parseFloat(cd.style.fontSize) || 15.5; cd.dataset.gs = grid.getAttribute('style'); }
      cd.style.fontSize = cd.dataset.fs + 'px';
      grid.setAttribute('style', cd.dataset.gs);
      draw();
      var k = avail / cd.scrollWidth;
      if (k < 1) {
        k = Math.max(0.5, k);
        cd.style.fontSize = (cd.dataset.fs * k) + 'px';
        grid.setAttribute('style', cd.dataset.gs.replace(/([\d.]+)rem/g, function (_, v) { return (v * k).toFixed(2) + 'rem'; }));
        draw();
      }
      return;
    }
    var math = box.querySelector('.katex-display') || box.firstElementChild;
    if (!math) return;
    box.style.fontSize = '';
    var base = parseFloat(getComputedStyle(box).fontSize);
    for (var n = 0; n < 3; n++) {
      var w = (math.querySelector('.katex') || math).scrollWidth;
      if (w <= avail) break;
      base = Math.max(10, base * avail / w);
      box.style.fontSize = base + 'px';
    }
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
// The galleries' chrome is in English; the reading-view shell they reuse
// heads its pages in French for the transcriptions.
export const withSlides = (page) =>
  page.replace('</body>', `${SLIDES}</body>`).replace('Datation de l’inventaire', 'Inventory dating');
