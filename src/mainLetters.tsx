import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { LettersPage } from './LettersPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <LettersPage />
  </StrictMode>,
);
