import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { MapsPage } from './MapsPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <MapsPage />
  </StrictMode>,
);
