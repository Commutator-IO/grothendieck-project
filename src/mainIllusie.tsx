import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { IllusiePage } from './IllusiePage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <IllusiePage />
  </StrictMode>,
);
