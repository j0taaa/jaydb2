"""Read only metadata of completed staged C artifacts, outside measured API calls."""
import hashlib,json,re,time
from pathlib import Path
OUT=Path('/home/jota/projects/jaydb2-performance/build/performance-setup-followup')
seen=set();records=[]
while True:
 for p in OUT.glob('*-*-*-*/tmp/jaydb2-*/*/checked.c.json'):
  if str(p) in seen:continue
  try:
   report=json.loads(p.read_text());c=p.with_suffix('');manifest=c.parent/'manifest.json'
   if not c.exists() or not manifest.exists():continue
   m=json.loads(manifest.read_text())
   text=c.read_text()
   record={'case':p.parents[3].name,'artifact':p.parent.name,'c_bytes':c.stat().st_size,'c_sha256':hashlib.sha256(text.encode()).hexdigest(),'dependencies':len(m['dependencies']),'dependency_bytes':sum((c.parent/f['path']).stat().st_size for f in m['dependencies']),'stats':dict(re.findall(r'#define\s+(STAT_LEN|BANGS)\s+([^\n]+)',text))}
   if (c.parent/'Client.bend').exists():record['client_sha256']=hashlib.sha256((c.parent/'Client.bend').read_bytes()).hexdigest()
   seen.add(str(p));records.append(record)
   (OUT/'compiled-closure-observations.tmp').write_text(json.dumps(records,indent=2)+'\n');(OUT/'compiled-closure-observations.tmp').replace(OUT/'compiled-closure-observations.json')
  except (FileNotFoundError,json.JSONDecodeError):pass
 if json.loads((OUT/'result.json').read_text())['status']!='running':break
 time.sleep(2)
