"""Adapt the REAL proof prefix to each faulty maintenance implementation.

These are filled, intentionally false certificates; no holes or assumption
certificates. Every changed write's layout and ordinary permission proof is
adapted before the final ExactIndex equality is attempted.
"""
from pathlib import Path

APP = Path(__file__).resolve().parent


def read(t):
    return 'L.Both{{==},' + t + '}'


def write(a, b, ia, ib, t):
    return read('L.Both{M.Laid{' + ','.join((a,b,ia,ib)) + ',{==}},' + t + '}')


def modified_set(proof, kind):
    for who in ('alice', 'bob'):
        start = proof.index(f'def set_{who}(')
        end = proof.index(f'def query_{who}(', start)
        head = proof[start:proof.index('  match new:', start)] + '  match new:\n'
        for val in ('False{}', 'True{}'):
            a, b = (val, 'b') if who == 'alice' else ('a', val)
            tail = 'L.Both{{==},{==}}'  # Actual terminal ExactIndex obligations.
            ea, eb = '[M.entry(a)]', '[M.entry(b)]'
            if kind == 'omitted':
                tail = write(a,b,ea,eb,tail)
            else:
                forged = f'[X.entry("item",[M.tag({val})],"forged")]'
                ia, ib = (forged,eb) if who=='alice' else (ea,forged)
                tail = write(a,b,ia,ib,tail)
                tail = write('a','b',ia,ib,tail)
                ia,ib = ('Nil{}',eb) if who=='alice' else (ea,'Nil{}')
                tail = write('a','b',ia,ib,tail)
            head += f'    case {val}: {tail}\n'
        proof = proof[:start] + head + '\n' + proof[end:]
    if kind == 'omitted':
        start = proof.index('    case Client.Set{+b}:', proof.index('def command_complete'))
        end = proof.index('    case Client.Query', start)
        proof = proof[:start] + '''    case Client.Set{+b}:
      End.finite(2n,Client.command(owner,Client.Set{b}),e,s,ts,End.writes([M.business(b)],1n,D.Application{owner},S.Finish{D.VBool{b}},Unit{}))
''' + proof[end:]
    return proof


def permission_proof(kind):
    """Independent per-access proof on ALL valid initial states, no index post."""
    positive=(APP/'ClientProof.bend').read_text()
    text='''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./CheckedActions.bend as H
import ./Model.bend as M
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Orders.bend as O
import ./Termination.bend as T
import ./Policy.bend as P
'''
    for who, old in [('alice','a'), ('bob','b')]:
        text += f'''def set_{who}(+a:Bool,+b:Bool,+kind:String,new:Bool) ->
  H.Permissions(6n,C.schema(),D.Context{{"{who}",kind}},M.state(a,b),Client.command("{who}",Client.Set{{new}})):
  match new:
'''
        for val in ('False{}','True{}'):
            t='Unit{}'
            for _ in range(1 if kind=='omitted' else 3): t=read(t)
            text+=f'    case {val}: {t}\n'
        text += f'''\ndef query_{who}(+a:Bool,+b:Bool,+kind:String,wanted:Bool) ->
  H.Permissions(6n,C.schema(),D.Context{{"{who}",kind}},M.state(a,b),Client.command("{who}",Client.Query{{wanted}})):
  {read(read(read('Unit{}')))}

def rebuild_{who}(+a:Bool,+b:Bool,+kind:String) ->
  H.Permissions(6n,C.schema(),D.Context{{"{who}",kind}},M.state(a,b),Client.command("{who}",Client.Rebuild{{}})):
  match {old}:
    case False{{}}: {read(read(read(read('Unit{}'))))}
    case True{{}}: {read(read(read(read('Unit{}'))))}

'''
    start=positive.index('def alice_command_safe')
    end=positive.index('def Target',start)
    text+=positive[start:end].replace('H.Safe(', 'H.Permissions(').replace('L.Both{{==},{==}}','Unit{}')
    text+='''
def PermissionAt(+ctx:D.Context,+args:D.Value,+s:D.State) -> Type:
  H.Permissions(6n,C.schema(),ctx,s,S.start(Client.program(),ctx,args))

def normalized(+ctx:D.Context,+args:D.Value,+s:D.State,h:M.Coherent(s)) -> PermissionAt(ctx,args,s):
  match h:
    case M.Exact{+a,+b,eq}:
      %Equal.sym(D.State,s,M.state(a,b),eq) : PermissionAt(ctx,args,_)
      start_safe(a,b,ctx,args)

law permitted_valid_state:
  for +s:D.State
  for +ctx:D.Context
  for +args:D.Value
  for valid:R.Valid(C.config(),s)
  PermissionAt(ctx,args,s)
def permitted_valid_state(s,ctx,args,valid):
  match valid:
    case L.Both{structure,L.Both{layout,L.Both{indexes,Unit{}}}}:
      normalized(ctx,args,s,M.canonical(s,layout,indexes))
'''
    text += '\nlaw permitted_all_prefixes:\n  for +s:D.State\n  for +ctx:D.Context\n  for +args:D.Value\n  for valid:R.Valid(C.config(),s)\n  for +n:Nat\n  P.AllAllowed(ctx,S.events_execution_trace(S.execute(n,Client.program(),C.schema(),s,ctx,args)))\ndef permitted_all_prefixes(s,ctx,args,valid,n):\n  H.allowed_rewind(ctx,S.execute(n,Client.program(),C.schema(),s,ctx,args),T.observe(n,S.start(Client.program(),ctx,args),C.schema(),s,Nil{}),\n    Equal.sym(S.Trace,T.observe(n,S.start(Client.program(),ctx,args),C.schema(),s,Nil{}),S.execute(n,Client.program(),C.schema(),s,ctx,args),T.reference(n,S.start(Client.program(),ctx,args),C.schema(),s)),\n    H.permissions_trace(6n,n,S.start(Client.program(),ctx,args),ctx,C.schema(),s,Nil{},permitted_valid_state(s,ctx,args,valid),Unit{}))\n'
    return text


def variant(kind):
    code=(APP/'Client.bend').read_text()
    proof=(APP/'ClientProof.bend').read_text()
    if kind=='omitted':
        old='''      X.maintain(D.Application{owner ++ "_index"},["item"],[M.entry(b)],
        A.define_rows(D.Application{owner},[M.business(b)],S.Finish{D.VBool{b}}))'''
        new='''      A.define_rows(D.Application{owner},[M.business(b)],S.Finish{D.VBool{b}})'''
        assert code.count(old)==1
        code=code.replace(old,new)
        proof=modified_set(proof,kind)
    elif kind=='forged':
        old='X.maintain(D.Application{owner ++ "_index"},["item"],[M.entry(b)]'
        new='X.maintain(D.Application{owner ++ "_index"},["item"],[X.entry("item",[M.tag(b)],"forged")]'
        assert code.count(old)==1
        code=code.replace(old,new)
        proof=modified_set(proof,kind)
    elif kind=='forbidden':
        old='X.lookup_many(D.Application{owner ++ "_index"}'
        assert code.count(old)==1
        code=code.replace(old,'X.lookup_many(D.Application{"bob_index"}')
    else:
        raise ValueError(kind)
    return code,proof
