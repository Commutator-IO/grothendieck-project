import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { NoveltiesPage } from './NoveltiesPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <NoveltiesPage />
  </StrictMode>,
);
