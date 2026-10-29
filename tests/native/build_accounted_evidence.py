"""Build from C emitted by the isolated, real same-Book gate (not fixtures)."""
import importlib.util
import json
import hashlib
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
import sys
sys.path.insert(0,str(ROOT))
from tools.service.build_loading import build as build_loading
from tools.service.build_lifecycle import build as build_lifecycle
spec=importlib.util.spec_from_file_location('native_build',ROOT/'tools/native/build.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
e=ROOT/'tests/native/evidence';source=e/'accounted-codec.c'
build_loading(e/'accounted-loading.so')
build_lifecycle(e/'accounted-lifecycle.so')
checked=json.loads(source.with_suffix('.c.checked.json').read_text())
assert checked['primary'] and checked['bendtt'] and checked['sameCheckedBook']
assert hashlib.sha256(source.read_bytes()).hexdigest()==checked['cSha256']
text=source.read_text()
read=re.search(r'^#define (CID_\w*Native_read) \d+$',text,re.M)[1]
write=re.search(r'^#define (CID_\w*Native_write) \d+$',text,re.M)[1]
enter=re.search(r'^#define (CID_\w*Native_enter) \d+$',text,re.M)[1]
for name,fixture in [('production',None),('fixture',ROOT/'tests/native/recipe_fixture.c')]:
    report=b.build_module(source,e/f'accounted-{name}.so',input_cid=read,output_cid=write,enter_cid=enter,recipe_fixture=fixture)
    print(name,report['accountedCodecV3'],report['accountedRecipeAudit']['criticalIsLeaf'],flush=True)
# Exact same emitted legacy program, excluding the staged private control arm.
# It still contains/executes the original Codec in the false branch in legacy
# mode. The counted invocation of this artifact must refuse before decoding.
# Remove the arm's trailing brace before the segment closes.
# Use balanced C braces to locate the selected decoder segment's legacy block
# in the original rather than assuming a constructor/continuation layout.
original=text
fid=b.verify_accounted_lowering(text)['entries'][0]['fid']
at=original.index('WL_CASE('+fid+')')
start=original.index('    if (jaydb_accounted_enabled()) {',at)
else_at=original.index('    } else {\n',start)
i=else_at+len('    } else {\n');depth=1;j=i
while depth:
    if original[j]=='{':depth+=1
    elif original[j]=='}':depth-=1
    j+=1
legacy=original[:start]+original[i:j-1]+original[j:]
legacy=re.sub(r'^// JAYDB_NATIVE_ACCOUNTED_(?:CODEC|ENTRY)_V1 .*\n','',legacy,flags=re.M)
legacy_file=e/'accounted-legacy.c';legacy_file.write_text(legacy)
report=b.build_module(legacy_file,e/'accounted-legacy.so',input_cid=read,output_cid=write,enter_cid=enter)
print('legacy',report['accountedCodecV3'],flush=True)
helper=e/'accounted-helper.c'
if helper.exists():
    checked=json.loads(helper.with_suffix('.c.checked.json').read_text())
    assert checked['primary'] and checked['bendtt'] and checked['sameCheckedBook']
    assert hashlib.sha256(helper.read_bytes()).hexdigest()==checked['cSha256']
    text=helper.read_text()
    assert b.verify_accounted_lowering(text)['uncoveredEntries']
    ids={kind:re.search(r'^#define (CID_\w*Native_'+kind+r') \d+$',text,re.M)[1] for kind in ['read','write','enter']}
    report=b.build_module(helper,e/'accounted-helper.so',input_cid=ids['read'],output_cid=ids['write'],enter_cid=ids['enter'])
    assert not report['accountedCodecV3']
    print('uncovered helper: legacy preserved, private entry refused',flush=True)
empty=e/'accounted-no-codec.c'
if empty.exists():
    checked=json.loads(empty.with_suffix('.c.checked.json').read_text())
    assert checked['primary'] and checked['bendtt'] and checked['sameCheckedBook']
    assert checked['absenceDecodeEstablished'] and not checked['trustedCodecEntryUsesRecipe']
    assert hashlib.sha256(empty.read_bytes()).hexdigest()==checked['cSha256']
    text=empty.read_text()
    ids={kind:re.search(r'^#define (CID_\w*Native_'+kind+r') \d+$',text,re.M) for kind in ['read','write','enter']}
    report=b.build_module(empty,e/'accounted-no-codec.so',
        **{kind+'_cid':match[1] if match else None for kind,match in
            [('input',ids['read']),('output',ids['write']),('enter',ids['enter'])]})
    assert report['accountedModeV3'] and report['accountedDecoderFreeV3'] and not report['accountedCodecV3']
    print('trusted no decoder: accounted mode enabled without recipe or wire fields',flush=True)
