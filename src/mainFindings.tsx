import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { FindingsPage } from './FindingsPage.tsx';

// The five figures moved to /maps/ on 26 September 2026; links posted before
// then (the #27 thread among them) carry their anchors here.
const MOVED = ['folders-and-print', 'lineage', 'people-network', 'math-map', 'citation-map'];
const hash = location.hash.slice(1);
if (MOVED.includes(hash)) location.replace(`/maps/#${hash}`);

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <FindingsPage />
  </StrictMode>,
);
