"""Build the trusted first-construction recipe, standalone or relocatable.

The native builder links it for the staged trusted Codec lowering. Production
critical is an audited leaf on an explicit active stack; global completeness
and semantic correspondence are still not claimed.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[2]
NATIVE=ROOT/'native'
CLANG=Path('/usr/bin/clang-19')


def build(output, *, test_fixture=None, object_only=False):
    output=Path(output)
    output.parent.mkdir(parents=True,exist_ok=True)
    flags=['--no-default-config','-std=c11','-O2','-fPIC','-mno-red-zone','-fno-builtin',
           '-fstack-clash-protection','-fno-stack-protector','-fno-asynchronous-unwind-tables','-Wall','-Wextra','-Werror']
    if test_fixture is not None:
        flags+=['-DJAYDB_RECIPE_TEST']
    with tempfile.TemporaryDirectory(prefix='jaydb-field-') as tmp:
        tmp=Path(tmp)
        def compile(extent, *, ir=False):
            target=tmp/('bridge.ll' if ir else 'bridge.o')
            extra=['-S','-emit-llvm'] if ir else ['-fstack-usage','-c']
            subprocess.run([str(CLANG),*flags,f'-DJAYDB_RECIPE_STACK_BYTES={extent}',
                *extra,str(NATIVE/'field_recipe.c'),'-o',str(target)],check=True,capture_output=True)
            return target
        compile(0)
        frames={}
        for line in (tmp/'bridge.su').read_text().splitlines():
            name,size,kind=line.rsplit('\t',2)
            if kind!='static':raise RuntimeError('Unexpected dynamic field frame')
            frames[name.rsplit(':',1)[-1]]=int(size)
        if 'recipe_critical' not in frames:raise RuntimeError('Missing critical stack metadata')
        # No red zone. Assembly creates one return address on the new stack;
        # allow target ABI alignment slack, then account actual page capacity.
        extent=(frames['recipe_critical']+8+15+4095)&~4095
        ir=compile(extent,ir=True).read_text()
        match=re.search(r'^define[^\n]*@recipe_critical\([^\n]*\).*?^}',ir,re.M|re.S)
        if not match:raise RuntimeError('Missing critical LLVM body')
        calls=re.findall(r'\bcall\b[^\n]*',match[0])
        external=[call for call in calls if ' asm ' not in call and not re.search(r'@llvm\.(?:lifetime\.|umax\.i64|umin\.i64)',call)]
        if test_fixture is None and external:
            raise RuntimeError('Production field critical must be a leaf: '+repr(external))
        compile(extent)
        final_frames={line.rsplit('\t',2)[0].rsplit(':',1)[-1]:int(line.rsplit('\t',2)[1])
                      for line in (tmp/'bridge.su').read_text().splitlines()}
        if final_frames['recipe_critical']!=frames['recipe_critical']:
            raise RuntimeError('Unexpected stack metadata change after embedding extent')
        command=[str(CLANG),*flags,f'-DJAYDB_RECIPE_STACK_BYTES={extent}']
        if object_only:
            # One relocatable support object, with no temporary DSO dependency.
            objects=[str(compile(extent))]
            for index,path in enumerate([NATIVE/'field_recipe.S']+([] if test_fixture is None else [Path(test_fixture)])):
                target=tmp/f'support{index}.o'
                subprocess.run([str(CLANG),*flags,'-c',str(path),'-o',str(target)],check=True,capture_output=True)
                objects.append(str(target))
            subprocess.run([str(CLANG),'--no-default-config','-nostdlib','-r',*objects,'-o',str(output)],check=True,capture_output=True)
        else:
            command+=['-shared','-Wl,-z,now,-z,defs,-Bsymbolic']
            if test_fixture is None:command+=['-nostdlib']
            command += [str(NATIVE/'field_recipe.c'),str(NATIVE/'field_recipe.S')]
            if test_fixture is not None:command+=[str(test_fixture)]
            subprocess.run([*command,'-o',str(output)],check=True,capture_output=True)
        assembly=subprocess.check_output(['objdump','-d','--disassemble=recipe_critical',str(output)],text=True)
        if test_fixture is None and re.search(r'\bcall[q]?\s',assembly):
            raise RuntimeError('Final production field object contains a call')
        paths=[NATIVE/name for name in ['field_recipe.h','field_recipe.c','field_recipe.S']]
        paths += [NATIVE/'accounting'/name for name in ['counter.h','window.h','deadline.h']]
        paths += [NATIVE/'field.h',Path(__file__)]
        if test_fixture is not None:paths.append(Path(test_fixture))
        report={'abi':3,'relocatable':object_only,'testFixture':test_fixture is not None,'stackBytes':extent,
            'compilerDriverFlags':['--no-default-config'],'compilerDefaultConfiguration':False,
            'criticalFrameBytes':frames['recipe_critical'],'criticalIsLeaf':not external,
            'finalObjectHasNoCalls':not bool(re.search(r'\bcall[q]?\s',assembly)),
            'nativeStackClashProtection':True,
            'frames':frames,'activeWindowPreserved':True,
            'realBackingBeforeFinalBarrier':True,'effectiveWireLengthCheck':True,
            'nativeDecoderLoweringAvailable':True,'noCounterCompletenessClaim':True,
            'noLengthProvenanceClaim':True,'noFullContractClaim':True,
            'moduleSha256':hashlib.sha256(output.read_bytes()).hexdigest(),
            'compilerSha256':hashlib.sha256(CLANG.read_bytes()).hexdigest(),
            'sources':{str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):
                       hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
        output.with_suffix(output.suffix+'.json').write_text(json.dumps(report,indent=2)+'\n')
        return report


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('output',type=Path)
    build(parser.parse_args().output)
