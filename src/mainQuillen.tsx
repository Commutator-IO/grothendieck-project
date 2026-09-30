import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { QuillenPage } from './QuillenPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <QuillenPage />
  </StrictMode>,
);
