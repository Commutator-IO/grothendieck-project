import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { BuffaloPage } from './BuffaloPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <BuffaloPage />
  </StrictMode>,
);
