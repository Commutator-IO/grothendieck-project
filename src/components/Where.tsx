export const IHP_CAT = (q: string) =>
  `https://sorbonne-universite.primo.exlibrisgroup.com/discovery/search?query=any,contains,${encodeURIComponent(q)}&tab=Everything&search_scope=MyInst_and_CI&vid=33BSU_INST:33BSU`;
export const NUMDAM = (id: string) => `https://www.numdam.org/item/${id}/`;
export const linkCls = 'text-brand-600 underline decoration-brand-200 underline-offset-2 hover:text-brand-700';
export function Where({ online, ihp }: { online?: [string, string][]; ihp?: string }) {
  const items: [string, string][] = [...(online ?? []), ...(ihp ? [['IHP', IHP_CAT(ihp)] as [string, string]] : [])];
  return (
    <span className="text-[13px] text-ink-500">
      {' '}(
      {items.map(([label, href], i) => (
        <span key={href}>
          {i > 0 && ' · '}
          <a href={href} className={linkCls}>{label}</a>
        </span>
      ))}
      )
    </span>
  );
}
