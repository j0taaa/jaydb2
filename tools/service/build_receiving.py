"""Build the first-byte/scope boundary, without changing the frozen controller."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path('/usr/bin/clang-19')

def build(output,*,test_fixture=None):
    output=Path(output).resolve()
    output.parent.mkdir(parents=True,exist_ok=True)
    from tools.service.build_loading import build as build_loading
    loading_file=output.with_name(output.name+'.loading.so')
    loading_manifest=build_loading(loading_file)
    directory=ROOT/'tools/service'
    sources=[directory/n for n in ('receiving.c','receiving.h','receiving_chunk.c',
                                   'receiving_chunk.h','build_receiving.py')]
    sources+=[ROOT/'native/accounting'/n for n in ('counter.h','window.h','deadline.h')]
    flags=['--no-default-config','-std=c11','-O2','-fPIC','-fno-builtin','-fno-stack-protector',
        '-fstack-clash-protection','-Wall','-Wextra','-Werror','-shared','-Wl,-z,now','-Wl,-z,defs']
    inputs=[directory/'receiving.c',directory/'receiving_chunk.c']
    if test_fixture is None:flags+=['-nostdlib']
    else:
        flags+=['-DJAYDB_RECEIVING_TEST']
        sources.append(Path(test_fixture).resolve());inputs.append(Path(test_fixture).resolve())
    def hashes():
        return {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p):
            hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    source_hashes=hashes()
    compiler_hash=hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    identity=hashlib.sha256(json.dumps({'sources':source_hashes,'compiler':compiler_hash,
        'flags':flags,'testFixture':test_fixture is not None},sort_keys=True,
        separators=(',',':')).encode()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='.receiving-',dir=output.parent) as tmp:
        binary=Path(tmp)/'receiving.so'
        audit_flags=['--no-default-config','-std=c11','-O2','-fno-builtin','-fno-stack-protector',
            '-fstack-clash-protection','-DJAYDB_RECEIVING_BUILD_ID="'+identity+'"']
        ir=Path(tmp)/'receiving.ll'
        subprocess.run([str(COMPILER),*audit_flags,'-S','-emit-llvm',
            str(directory/'receiving.c'),'-o',str(ir)],check=True)
        body=re.search(r'define[^\n]*@jaydb_receiving_begin\([^\n]*\).*?\n}',ir.read_text(),re.S)
        if body is None:raise RuntimeError('Receiving prefix missing from LLVM IR')
        calls=re.findall(r'\bcall\b[^\n]*',body[0])
        unexpected=[line for line in calls if ' asm ' not in line and '@llvm.' not in line]
        if unexpected:raise RuntimeError('Receiving prefix contains a callback/library call: '+repr(unexpected))
        chunk_ir=Path(tmp)/'chunk.ll'
        subprocess.run([str(COMPILER),*audit_flags,'-S','-emit-llvm',
            str(directory/'receiving_chunk.c'),'-o',str(chunk_ir)],check=True)
        chunk_body=re.search(r'define[^\n]*@jaydb_receiving_chunk_read_v1\([^\n]*\).*?\n}',
            chunk_ir.read_text(),re.S)
        if chunk_body is None:raise RuntimeError('Durable receiving chunk missing from LLVM IR')
        chunk_calls=re.findall(r'\bcall\b[^\n]*',chunk_body[0])
        unexpected=[line for line in chunk_calls if ' asm ' not in line and '@llvm.' not in line]
        if unexpected:raise RuntimeError('Receiving chunk contains a callback/library call: '+repr(unexpected))
        subprocess.run([str(COMPILER),*flags,'-DJAYDB_RECEIVING_BUILD_ID="'+identity+'"',
            *map(str,inputs),'-o',str(binary)],check=True)
        if hashes()!=source_hashes or hashlib.sha256(COMPILER.read_bytes()).hexdigest()!=compiler_hash:
            raise RuntimeError('Receiving inputs changed during compilation')
        report={'abi':1,'resultBytes':368,'testFixture':test_fixture is not None,
            'chunkRequestBytes':40,'chunkReceiptBytes':56,
            'buildIdentitySha256':identity,'moduleSha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
            'compilerSha256':compiler_hash,'sources':source_hashes,
            'compilerDriverFlags':['--no-default-config'],'compilerDefaultConfiguration':False,
            'nativePrefixIsLeaf':test_fixture is None,
            'nativePrefixAllocatesBacking':False if test_fixture is None else None,
            'auditedProductionPrefixIsLeaf':True,
            'wholeEntryIntegrated':False,'fullExecutableContractProved':False,
            'loading':{'file':loading_file.name,'manifest':loading_manifest}}
        record=Path(tmp)/'report.json'
        record.write_text(json.dumps(report,indent=2)+'\n')
        os.replace(binary,output)
        os.replace(record,output.with_suffix(output.suffix+'.json'))
    return report

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('output',type=Path)
    build(parser.parse_args().output)
