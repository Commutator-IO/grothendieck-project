import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { DiagramsPage } from './DiagramsPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <DiagramsPage />
  </StrictMode>,
);
