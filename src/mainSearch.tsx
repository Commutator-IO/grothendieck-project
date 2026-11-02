import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { SearchPage } from './SearchPage.tsx';

// index.html marks the page when an old link into the fonds is being sent on to /fonds/.
if (!document.documentElement.hasAttribute('data-moved')) {
  createRoot(document.getElementById('root') as HTMLElement).render(
    <StrictMode>
      <SearchPage />
    </StrictMode>,
  );
}
