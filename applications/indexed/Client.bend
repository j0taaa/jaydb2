import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Model.bend as M
import ./Index.bend as X
import ./Action.bend as A

type Command is Data:
  Set{available:Bool}
  Query{available:Bool}
  Rebuild{}
  Invalid{}

def analyze(args:D.Value) -> Command:
  match args:
    case D.VList{D.VText{"set"},D.VList{D.VBool{b},D.VListEmpty{}}}: Set{b}
    case D.VList{D.VText{"query"},D.VList{D.VBool{b},D.VListEmpty{}}}: Query{b}
    case D.VList{D.VText{"rebuild"},D.VListEmpty{}}: Rebuild{}
    case _: Invalid{}

type Availability is Data:
  Known{available:Bool}
  InvalidAvailability{}

def availability(r:S.Return) -> Availability:
  match r:
    case S.Datum{D.Cell{D.VBool{b}}}: Known{b}
    case _: InvalidAvailability{}

def rebuild_known(owner:String,info:Availability) -> S.Action:
  match info:
    case Known{b}: X.rebuild(D.Application{owner ++ "_index"},[M.entry(b)],S.Finish{D.VText{"rebuilt"}})
    case InvalidAvailability{}: S.Refuse{D.VText{"invalid availability"}}

def command(+owner:String,p:Command) -> S.Action:
  match p:
    case Set{+b}:
      X.maintain(D.Application{owner ++ "_index"},["item"],[M.entry(b)],
        A.define_rows(D.Application{owner},[M.business(b)],S.Finish{D.VBool{b}}))
    case Query{b}: X.scan_equal(D.Application{owner ++ "_index"},[M.tag(b)],v => S.Finish{v})
    case Rebuild{}: S.Access{D.ReadCell{D.Application{owner},"item","available"},r => rebuild_known(owner,availability(r))}
    case Invalid{}: S.Refuse{D.VText{"invalid request"}}

def flags(alice:Bool,bob:Bool,args:D.Value) -> S.Action:
  match alice bob:
    case True{} bob: command("alice",analyze(args))
    case False{} True{}: command("bob",analyze(args))
    case False{} False{}: S.Refuse{D.VText{"unknown principal"}}

def start(ctx:D.Context,args:D.Value) -> S.Action:
  D.Context{+id,kind}=ctx
  flags(String.eq(id,"alice"),String.eq(id,"bob"),args)

def program() -> S.Program:
  S.Program{start}
