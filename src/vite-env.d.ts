/// <reference types="vite/client" />

interface ImportMetaEnv {
  readonly VITE_RELAY?: string;
  /** `true` when the build may show transcriptions of Quillen's notebooks (repository variable RENDER_QUILLEN, #36). */
  readonly VITE_RENDER_QUILLEN?: string;
  /** `false` when the transcriptions are switched off (repository variable RENDER_TRANSCRIPTS, #31); the review page then quotes no reading. */
  readonly VITE_RENDER_TRANSCRIPTS?: string;
  /** `true` when the build shows the Illusie transcriptions beside the IHÉS facsimile, which every build shows (repository variable RENDER_ILLUSIE, off by default); the dev server always does. */
  readonly VITE_RENDER_ILLUSIE?: string;
  /** `true` when the build carries the Bourbaki tab's reading view — local transcriptions beside the AHP scan (repository variable RENDER_BOURBAKI, off by default); the dev server always does. */
  readonly VITE_RENDER_BOURBAKI?: string;
}
