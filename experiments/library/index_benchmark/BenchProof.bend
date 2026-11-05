import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Termination.bend as T
import ./Completion.bend as E
import ./Laws.bend as G
import ./Query.bend as Q
import ./Read.bend as R
import ./Index.bend as X
import ./Action.bend as A
import ./Key.bend as K
import ./Bench.bend as B

def found(b:Bool,+wanted:String,key:String,+rest:List<&2,String>,h:T.Finite(G.depth(rest,1n),B.find(wanted,rest))) -> T.Finite(G.depth(rest,1n),B.found(b,key,B.find(wanted,rest))):
  match b rest:
    case True{} Nil{}: Unit{}
    case False{} Nil{}: h
    case True{} Con{x,xs}: Unit{}
    case False{} Con{x,xs}: h

def find(xs:List<&2,String>,+wanted:String) -> T.Finite(G.depth(xs,1n),B.find(wanted,xs)):
  match xs:
    case Nil{}: Unit{}
    case Con{+key,+rest}: r => found(B.matches(wanted,r),wanted,key,rest,find(rest,wanted))

def scan(xs:List<&2,String>,+n:Nat,+wanted:String,-done:D.Value -> S.Action,h:@v:D.Value -> T.Finite(Succ{n},done(v))) -> T.Finite(G.depth(xs,Succ{n}),Q.filter_map(~B.ScanEnv,~B.visit,B.ScanEnv{wanted},xs,done)):
  match xs:
    case Nil{}: h(D.VListEmpty{})
    case Con{+key,+rest}: r => scan(rest,n,wanted,tail => done(Q.include(Bool.pick(Maybe<&2,D.Value>,B.matches(wanted,r),Some{D.VText{key}},None{}),tail)),tail => h(Q.include(Bool.pick(Maybe<&2,D.Value>,B.matches(wanted,r),Some{D.VText{key}},None{}),tail)))

def keys_return(+wanted:String,r:S.Return,+findmode:Bool,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(R.keys_return(Bool.pick(List<&2,String> -> S.Action,findmode,B.find(wanted),B.scan(wanted)),r),e,s,ts):
  match r:
    case S.Datum{D.Keys{+xs}}:
      match findmode:
        case True{}: E.finite(G.depth(xs,1n),B.find(wanted,xs),e,s,ts,find(xs,wanted))
        case False{}: E.finite(G.depth(xs,1n),B.scan(wanted,xs),e,s,ts,scan(xs,0n,wanted,v => S.Finish{v},v => Unit{}))
    case S.Datum{D.RowAbsent{}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Cell{v}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Existence{v}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.Datum{D.Count{v}}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})
    case S.UnitValue{}: E.finite(1n,S.Refuse{D.VText{"unexpected keys return"}},e,s,ts,Unit{})

def unique_finish(result:B.UniqueResult) -> T.Finite(1n,B.unique_finish(result)):
  match result:
    case B.Found{k}: Unit{}
    case B.Absent{}: Unit{}
    case B.InvalidIndex{}: Unit{}

def unique_result(result:Q.Selection) -> T.Finite(1n,B.unique_result(result)):
  unique_finish(B.unique_projection(result))

def probe(r:S.Return) -> T.Finite(1n,B.probe_result(r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{D.Cell{v}}: Unit{}
    case S.Datum{D.RowAbsent{}}: Unit{}
    case S.Datum{D.Keys{xs}}: Unit{}
    case S.Datum{D.Existence{v}}: Unit{}
    case S.Datum{D.Count{v}}: Unit{}

def plan(u:Bool,m:Bool,+k:String,+em:String,+g:String,+p:String,+oe:String,+og:String,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(B.plan(u,m,k,em,g,oe,og,B.business(k,em,g,p)),e,s,ts):
  match u m:
    case True{} m: E.finite(4n,B.plan(True{},m,k,em,g,oe,og,B.business(k,em,g,p)),e,s,ts,E.removes([K.encode([oe])],3n,D.Application{"unique_index"},A.define_rows(D.Application{"unique_index"},[X.unique([em],k)],B.business(k,em,g,p)),E.writes([X.unique([em],k)],2n,D.Application{"unique_index"},B.business(k,em,g,p),E.writes([B.row(k,em,g,p)],1n,D.Application{"base"},S.Finish{D.VText{k}},Unit{}))))
    case False{} True{}: E.finite(4n,B.plan(False{},True{},k,em,g,oe,og,B.business(k,em,g,p)),e,s,ts,E.removes([K.encode([og,k])],3n,D.Application{"many_index"},A.define_rows(D.Application{"many_index"},[X.nonunique([g],k)],B.business(k,em,g,p)),E.writes([X.nonunique([g],k)],2n,D.Application{"many_index"},B.business(k,em,g,p),E.writes([B.row(k,em,g,p)],1n,D.Application{"base"},S.Finish{D.VText{k}},Unit{}))))
    case False{} False{}: E.finite(2n,B.business(k,em,g,p),e,s,ts,E.writes([B.row(k,em,g,p)],1n,D.Application{"base"},S.Finish{D.VText{k}},Unit{}))

def put(+kind:String,+k:String,+em:String,+g:String,+p:String,+oe:String,+og:String,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(B.put(kind,k,em,g,p,oe,og),e,s,ts):
  plan(String.eq(kind,"unique"),String.eq(kind,"many"),k,em,g,p,oe,og,e,s,ts)

def complete(c:B.Command,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> E.Complete(B.start(c),e,s,ts):
  match c:
    case B.Find{+v}: E.access(D.EnumerateKeys{D.Application{"base"}},R.keys_return(B.find(v)),e,s,ts,r => w => events => keys_return(v,r,True{},e,w,events))
    case B.Scan{+v}: E.access(D.EnumerateKeys{D.Application{"base"}},R.keys_return(B.scan(v)),e,s,ts,r => w => events => keys_return(v,r,False{},e,w,events))
    case B.Unique{+v}: E.finite(2n,B.start(B.Unique{v}),e,s,ts,E.reads(["target"],1n,D.Application{"unique_index"},K.encode([v]),B.unique_result,unique_result))
    case B.Many{v}: E.lookup(D.Application{"many_index"},[v],e,s,ts)
    case B.Put{k,id,em,g,p,oe,og}: put(k,id,em,g,p,oe,og,e,s,ts)
    case B.Probe{t,k,c}: E.finite(2n,B.start(B.Probe{t,k,c}),e,s,ts,probe)
    case B.Invalid{}: E.finite(1n,B.start(B.Invalid{}),e,s,ts,Unit{})
