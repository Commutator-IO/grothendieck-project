/**
 * Items of the Fonds Grothendieck–Illusie whose reading view the deployed site
 * shows even with RENDER_ILLUSIE off: an exception decided by Michel Hua on
 * 22 October 2026 for the letter to Giraud of 13 June 1969 (#85, the origin of
 * « champs »). Only the facsimile is shown, loaded from the IHÉS's server; the
 * page addresses of these items alone are listed here, so the deployed build
 * carries no other item's.
 */
export const PUBLIC_VIEWS: Record<string, { jpg: string[]; pdf: string | null }> = {
  FG_IL_2_GIRAUD69: {
    jpg: Array.from({ length: 8 }, (_, k) => `FG_IL_2_GIRAUD69_${String(k + 1).padStart(2, '0')}.jpg`),
    pdf: 'FG_IL_2_GIRAUD69.pdf',
  },
};
