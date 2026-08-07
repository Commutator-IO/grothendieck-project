import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { BookPage } from './BookPage.tsx';

// Only this notebook is imported: the bundle split follows the pages, so a
// reader opening the Long March does not download the motives inventory.
createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <BookPage bookKey="motives" />
  </StrictMode>,
);
