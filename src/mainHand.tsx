import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { HandPage } from './HandPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <HandPage />
  </StrictMode>,
);
