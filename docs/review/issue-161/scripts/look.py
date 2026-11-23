import json,sys
idx=json.load(open(sys.argv[1]))
for t in sys.argv[2:]:
  v=idx.get(t,[])
  core=[x for x in v if x[0].startswith('StacksCore')]; fr=[x for x in v if x[0].startswith('StacksFrontier')]
  tier='Core' if core else ('Frontier' if fr else 'none')
  print(t,tier,len(core),len(fr),'; '.join(f"{x[2]} ({x[0].split('/',1)[1]}:{x[1]})" for x in (core or fr)[:3]))
