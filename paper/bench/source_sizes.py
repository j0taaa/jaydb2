"""Reproducible physical nonblank counts; no source edits or compiler estimates."""
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]


def nonblank(path):
    return sum(bool(line.strip()) for line in (ROOT/path).read_text().splitlines())


def counts():
    # In these files every cfg(test) item ends before the next unindented item.
    # Explicit lexical boundary rule avoids counting strings' braces as Rust syntax.
    rust=[]
    for path in sorted((ROOT/'server').glob('*.rs')):
        lines=path.read_text().splitlines();test=False;production=tests=0
        for line in lines:
            if line=='#[cfg(test)]':test=True
            if line.strip():
                if test:tests+=1
                else:production+=1
            if test and line=='}':test=False
        rust.append(dict(file=str(path.relative_to(ROOT)),production=production,tests=tests))
    applications={}
    definitions={
        'indexed':(['applications/indexed/Client.bend'],['applications/indexed/ClientProof.bend','applications/indexed/CheckedActions.bend','applications/indexed/Completion.bend']),
        'voucher':(['applications/vouchers/Client.bend','applications/vouchers/Voucher.bend'],['applications/vouchers/ClientProof.bend'])}
    for name,(program,proof) in definitions.items():
        applications[name]=dict(program_files={p:nonblank(p) for p in program},proof_files={p:nonblank(p) for p in proof},
            client_lines=sum(map(nonblank,program)),proof_lines=sum(map(nonblank,proof)))
    return dict(definition='Nonblank physical lines, including comments/imports/attributes. Rust: server/*.rs; #[cfg(test)] attribute and following top-level item through its unindented closing brace are test lines; all remaining lines are production. Client ratios count Client.bend (plus Voucher.bend for the voucher dispatcher) versus its local certificate/checked-action/completion files only, excluding reusable library, domain/model, configuration, seed, and separately checked functional proofs.',
        rust_files=rust,rust_production_lines=sum(x['production'] for x in rust),rust_test_lines=sum(x['tests'] for x in rust),applications=applications)


if __name__=='__main__':
    import json
    import sys
    result=counts()
    if '--update' in sys.argv:
        from paper.bench.run import metadata,save
        path=ROOT/'paper/evidence/verification.json'
        data=json.loads(path.read_text())
        data['detailed_sizes']=result
        data['size_collection_metadata']=metadata(1)
        data['timing_policy_note']='Original successful verification wall times retained; their historical metadata precedes fixed-clock control. New size_collection_metadata records only source-inventory collection, not a rerun of command wall times.'
        save('verification.json',data)
    else:
        print(json.dumps(result,indent=2))
