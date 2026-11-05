import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Query.bend as Q
import ./Read.bend as R
import ./Index.bend as X
import ./Bench.bend as B

def strings(v:D.Value) -> List<&2,String>:
  match v:
    case D.VList{D.VText{x},rest}: Con{x,strings(rest)}
    case _: Nil{}

def selected(p:B.UniqueResult) -> D.Value:
  match p:
    case B.Found{k}: D.VList{D.VText{k},D.VListEmpty{}}
    case _: D.VListEmpty{}

def visit(wanted:String,key:String,done:Maybe<&2,D.Value> -> S.Action) -> S.Action:
  +id=key
  S.Access{D.ReadCell{D.Application{"base"},id,"email"},B.scan_result(wanted,id,done)}

def indexed(qs:List<&2,String>,done:D.Value -> S.Action) -> S.Action:
  match qs:
    case Nil{}: done(D.VListEmpty{})
    case Con{q,rest}: X.lookup(D.Application{"unique_index"},[q],res => indexed(rest,tail => done(D.VList{selected(B.unique_projection(res)),tail})))

def scanned(+keys:List<&2,String>,qs:List<&2,String>,done:D.Value -> S.Action) -> S.Action:
  match qs:
    case Nil{}: done(D.VListEmpty{})
    case Con{q,rest}: Q.filter_map(~String,~visit,q,keys,item => scanned(keys,rest,tail => done(D.VList{item,tail})))

def choose(indexed_mode:Bool,wants:List<&2,String>) -> S.Action:
  match indexed_mode:
    case True{}: indexed(wants,v => S.Finish{v})
    case False{}: R.keys(D.Application{"base"},keys => scanned(keys,wants,v => S.Finish{v}))

type Command is Data:
  Batch{mode:Bool,queries:List<&2,String>}
  Invalid{}

def parse(args:D.Value) -> Command:
  match args:
    case D.VList{D.VBool{mode},rest}: Batch{mode,strings(rest)}
    case _: Invalid{}

def command(c:Command) -> S.Action:
  match c:
    case Batch{mode,qs}: choose(mode,qs)
    case Invalid{}: S.Refuse{D.VAbsent{}}

def start(args:D.Value) -> S.Action:
  command(parse(args))

def program() -> S.Program:
  S.Program{ctx => args => start(args)}
