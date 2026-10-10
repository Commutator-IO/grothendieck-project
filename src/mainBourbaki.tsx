import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { BourbakiPage } from './BourbakiPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <BourbakiPage />
  </StrictMode>,
);
