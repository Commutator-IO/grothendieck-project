#!/usr/bin/env node
/**
 * Recopie KaTeX depuis `node_modules` vers `public/vendor/katex/`.
 *
 * La transcription s'affiche dans un cadre isolé — un document à part, qui
 * porte la feuille ar5iv verbatim et ne partage rien avec le reste du site.
 * Ce cadre ne passe donc pas par Vite : il lui faut des fichiers servis tels
 * quels. Les recopier à l'installation plutôt que de les charger depuis un CDN
 * garde le site utilisable hors ligne, ce qui compte pour un travail de
 * transcription qui dure des mois.
 *
 * Seules les polices réellement utilisées par KaTeX en WOFF2 sont reprises :
 * le dossier complet pèse 5 Mo en trois formats, dont deux qu'aucun navigateur
 * d'aujourd'hui ne demande.
 */

import { cp, mkdir, readdir } from 'node:fs/promises';
import { resolve } from 'node:path';

const RACINE = resolve(import.meta.dirname, '..');
const SOURCE = resolve(RACINE, 'node_modules', 'katex', 'dist');
const CIBLE = resolve(RACINE, 'public', 'vendor', 'katex');

async function principal() {
  await mkdir(resolve(CIBLE, 'fonts'), { recursive: true });

  for (const f of ['katex.min.css', 'katex.min.js']) {
    await cp(resolve(SOURCE, f), resolve(CIBLE, f));
  }
  await cp(
    resolve(SOURCE, 'contrib', 'auto-render.min.js'),
    resolve(CIBLE, 'auto-render.min.js'),
  );

  const polices = (await readdir(resolve(SOURCE, 'fonts'))).filter((f) => f.endsWith('.woff2'));
  for (const f of polices) {
    await cp(resolve(SOURCE, 'fonts', f), resolve(CIBLE, 'fonts', f));
  }

  process.stdout.write(`KaTeX + ${polices.length} polices → public/vendor/katex/\n`);
}

principal().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
