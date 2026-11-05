# One published availability record per principal, with an ordinary secondary
# index. Index rows are unconstrained by Layout while a transaction executes.
import Base
import ./Data.bend as D
import ./Logic.bend as L
import ./Index.bend as X
import ./TableLaws.bend as TL

def tag(b:Bool) -> String:
  match b:
    case True{}: "ready"
    case False{}: "busy"

def business(b:Bool) -> D.Row:
  D.Row{"item",[D.Field{"available",D.VBool{b}},D.Field{"id",D.VText{"item"}}]}

def entry(b:Bool) -> D.Row:
  X.entry("item",[tag(b)],"item")

def project(rows:List<&2,D.Row>) -> List<&2,D.Row>:
  match rows:
    case Nil{}: Nil{}
    case Con{D.Row{+key,[D.Field{"available",D.VBool{b}},D.Field{"id",D.VText{id}}]},rest}:
      Con{X.entry(key,[tag(b)],key),project(rest)}
    case _: Nil{}

def users() -> List<&2,D.Row>:
  [D.Row{"alice",[D.Field{"credential",D.VText{"alice-token"}},D.Field{"id",D.VText{"alice"}},D.Field{"kind",D.VText{"user"}}]},
   D.Row{"bob",[D.Field{"credential",D.VText{"bob-token"}},D.Field{"id",D.VText{"bob"}},D.Field{"kind",D.VText{"user"}}]}]

def parts(a:Bool,b:Bool,ia:List<&2,D.Row>,ib:List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"alice",[business(a)]},D.Table{"alice_index",ia},D.Table{"bob",[business(b)]},D.Table{"bob_index",ib}],users()}

def state(+a:Bool,+b:Bool) -> D.State:
  parts(a,b,[entry(a)],[entry(b)])

type LayoutProof<-s:D.State> is Data:
  Laid{a:Bool,b:Bool,ia:List<&2,D.Row>,ib:List<&2,D.Row>,same:{s == parts(a,b,ia,ib) : D.State}}

type ExactProof<-s:D.State> is Data:
  Exact{a:Bool,b:Bool,same:{s == state(a,b) : D.State}}

def Layout(s:D.State) -> Data:
  LayoutProof<s>

def Coherent(s:D.State) -> Data:
  ExactProof<s>

def Indexes(+s:D.State) -> Type:
  L.E<TL.ExactIndex(~project,D.Application{"alice"},D.Application{"alice_index"},s),
      TL.ExactIndex(~project,D.Application{"bob"},D.Application{"bob_index"},s)>

def coherent_layout(+s:D.State,h:Coherent(s)) -> Layout(s):
  match h:
    case Exact{+a,+b,eq}: Laid{a,b,[entry(a)],[entry(b)],eq}

def coherent_indexes(+s:D.State,h:Coherent(s)) -> Indexes(s):
  match h:
    case Exact{+a,+b,eq}:
      %Equal.sym(D.State,s,state(a,b),eq) : Indexes(_)
      L.Both{{==},{==}}

def canonical_parts(+a:Bool,+b:Bool,+ia:List<&2,D.Row>,+ib:List<&2,D.Row>,h:Indexes(parts(a,b,ia,ib))) -> Coherent(parts(a,b,ia,ib)):
  match h:
    case L.Both{ea,eb}:
      Exact{a,b,Equal.trans(D.State,parts(a,b,ia,ib),parts(a,b,[entry(a)],ib),state(a,b),
        Equal.cong(List<&2,D.Row>,D.State,r => parts(a,b,r,ib),ia,[entry(a)],ea),
        Equal.cong(List<&2,D.Row>,D.State,r => parts(a,b,[entry(a)],r),ib,[entry(b)],eb))}

def canonical(+s:D.State,h:Layout(s),index:Indexes(s)) -> Coherent(s):
  match h:
    case Laid{+a,+b,+ia,+ib,+eq}:
      %Equal.sym(D.State,s,parts(a,b,ia,ib),eq) : Coherent(_)
      canonical_parts(a,b,ia,ib,(%eq : Indexes(_) index))
