import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { NotebooksPage } from './NotebooksPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <NotebooksPage />
  </StrictMode>,
);
