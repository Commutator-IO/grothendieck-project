/// <reference types="vite/client" />

interface ImportMetaEnv {
  readonly VITE_RELAY?: string;
  /** `true` when the build may show transcriptions of Quillen's notebooks (repository variable RENDER_QUILLEN, #36). */
  readonly VITE_RENDER_QUILLEN?: string;
}
