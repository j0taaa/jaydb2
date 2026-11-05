import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Query.bend as Q
import ./Read.bend as R
import ./Index.bend as X
import ./Action.bend as A
import ./Key.bend as K

type Command is Data:
  Find{wanted:String}
  Scan{wanted:String}
  Unique{wanted:String}
  Many{wanted:String}
  Put{kind:String,key:String,email:String,group:String,pad:String,oldemail:String,oldgroup:String}
  Probe{table:String,key:String,column:String}
  Invalid{}

def command(args:D.Value) -> Command:
  match args:
    case D.VList{D.VText{"find"},D.VList{D.VText{v},D.VListEmpty{}}}: Find{v}
    case D.VList{D.VText{"scan"},D.VList{D.VText{v},D.VListEmpty{}}}: Scan{v}
    case D.VList{D.VText{"unique"},D.VList{D.VText{v},D.VListEmpty{}}}: Unique{v}
    case D.VList{D.VText{"many"},D.VList{D.VText{v},D.VListEmpty{}}}: Many{v}
    case D.VList{D.VText{"put"},D.VList{D.VText{kind},D.VList{D.VText{key},D.VList{D.VText{email},D.VList{D.VText{group},D.VList{D.VText{pad},D.VList{D.VText{oe},D.VList{D.VText{og},D.VListEmpty{}}}}}}}}}: Put{kind,key,email,group,pad,oe,og}
    case D.VList{D.VText{"probe"},D.VList{D.VText{t},D.VList{D.VText{k},D.VList{D.VText{c},D.VListEmpty{}}}}}: Probe{t,k,c}
    case _: Invalid{}

def matches(wanted:String,r:S.Return) -> Bool:
  match r:
    case S.Datum{D.Cell{D.VText{v}}}: String.eq(wanted,v)
    case _: False{}

def found(b:Bool,key:String,next:S.Action) -> S.Action:
  match b:
    case True{}: S.Finish{D.VList{D.VText{key},D.VListEmpty{}}}
    case False{}: next


def find(+wanted:String,xs:List<&2,String>) -> S.Action:
  match xs:
    case Nil{}: S.Finish{D.VListEmpty{}}
    case Con{+key,rest}: S.Access{D.ReadCell{D.Application{"base"},key,"email"},r => found(matches(wanted,r),key,find(wanted,rest))}

type ScanEnv is Data:
  ScanEnv{wanted:String}

def scan_result(wanted:String,key:String,done:Maybe<&2,D.Value> -> S.Action,r:S.Return) -> S.Action:
  done(Bool.pick(Maybe<&2,D.Value>,matches(wanted,r),Some{D.VText{key}},None{}))

def visit(env:ScanEnv,key:String,done:Maybe<&2,D.Value> -> S.Action) -> S.Action:
  ScanEnv{wanted}=env
  +id=key
  S.Access{D.ReadCell{D.Application{"base"},id,"group"},scan_result(wanted,id,done)}

def scan(wanted:String,keys:List<&2,String>) -> S.Action:
  Q.filter_map(~ScanEnv,~visit,ScanEnv{wanted},keys,v => S.Finish{v})

type UniqueResult is Data:
  Found{key:String}
  Absent{}
  InvalidIndex{}

def unique_projection(result:Q.Selection) -> UniqueResult:
  match result:
    case Q.Selected{D.VRecord{"target",D.VText{key},D.VRecordEmpty{}}}: Found{key}
    case Q.MissingRow{}: Absent{}
    case _: InvalidIndex{}

def unique_finish(result:UniqueResult) -> S.Action:
  match result:
    case Found{key}: S.Finish{D.VList{D.VText{key},D.VListEmpty{}}}
    case Absent{}: S.Finish{D.VListEmpty{}}
    case InvalidIndex{}: S.Refuse{D.VText{"invalid index"}}

def unique_result(result:Q.Selection) -> S.Action:
  unique_finish(unique_projection(result))

def row(+key:String,email:String,group:String,pad:String) -> D.Row:
  D.Row{key,[D.Field{"email",D.VText{email}},D.Field{"group",D.VText{group}},D.Field{"id",D.VText{key}},D.Field{"pad",D.VText{pad}}]}

def business(+key:String,email:String,group:String,pad:String) -> S.Action:
  A.define_rows(D.Application{"base"},[row(key,email,group,pad)],S.Finish{D.VText{key}})

def plan(u:Bool,m:Bool,+key:String,email:String,group:String,oldemail:String,oldgroup:String,business:S.Action) -> S.Action:
  match u m:
    case True{} m: X.maintain(D.Application{"unique_index"},[K.encode([oldemail])],[X.unique([email],key)],business)
    case False{} True{}: X.maintain(D.Application{"many_index"},[K.encode([oldgroup,key])],[X.nonunique([group],key)],business)
    case False{} False{}: business

def put(+kind:String,+key:String,+email:String,+group:String,pad:String,oldemail:String,oldgroup:String) -> S.Action:
  plan(String.eq(kind,"unique"),String.eq(kind,"many"),key,email,group,oldemail,oldgroup,business(key,email,group,pad))

def probe_result(r:S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{v}}: S.Finish{v}
    case S.Datum{D.RowAbsent{}}: S.Finish{D.VAbsent{}}
    case _: S.Refuse{D.VAbsent{}}

def start(c:Command) -> S.Action:
  match c:
    case Find{v}: R.keys(D.Application{"base"},find(v))
    case Scan{v}: R.keys(D.Application{"base"},scan(v))
    case Unique{v}: X.lookup(D.Application{"unique_index"},[v],unique_result)
    case Many{v}: X.scan_equal(D.Application{"many_index"},[v],v => S.Finish{v})
    case Put{kind,k,e,g,p,oe,og}: put(kind,k,e,g,p,oe,og)
    case Probe{t,k,c}: S.Access{D.ReadCell{D.Application{t},k,c},probe_result}
    case Invalid{}: S.Refuse{D.VText{"bad arguments"}}

def program() -> S.Program:
  S.Program{ctx => args => start(command(args))}
