import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { NoticesPage } from './NoticesPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <NoticesPage />
  </StrictMode>,
);
