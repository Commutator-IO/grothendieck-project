import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { BuiltPage } from './BuiltPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <BuiltPage />
  </StrictMode>,
);
