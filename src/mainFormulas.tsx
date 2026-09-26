import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import './index.css';
import { FormulasPage } from './FormulasPage.tsx';

createRoot(document.getElementById('root') as HTMLElement).render(
  <StrictMode>
    <FormulasPage />
  </StrictMode>,
);
