# Algebra for the directory representation, independent of the seed's size.
import Base
import ./Data.bend as D
import ./Logic.bend as L
import ./Model.bend as M
import ./Client.bend as Client
import ./Orders.bend as O
import ./Foundations.bend as F

law suffix_mask:
  for xs: List<&2, Maybe<&2, String>>
  {Client.suffix(M.mask(xs)) == M.suffix(xs) : String}
def suffix_mask(xs):
  match xs:
    case Nil{}: {==}
    case Con{None{}, +rest}:
      Equal.cong(String,String,s => SCon{'a',s},Client.suffix(M.mask(rest)),M.suffix(rest),suffix_mask(rest))
    case Con{Some{t}, +rest}:
      Equal.cong(String,String,s => SCon{'a',s},Client.suffix(M.mask(rest)),M.suffix(rest),suffix_mask(rest))

law key_mask:
  for +p: M.Principal
  for +xs: List<&2, Maybe<&2, String>>
  {Client.key(p,M.mask(xs)) == M.key(p,xs) : String}
def key_mask(p,xs):
  Equal.cong(String,String,s => M.prefix(p) ++ s,Client.suffix(M.mask(xs)),M.suffix(xs),suffix_mask(xs))

law suffix_before:
  for +xs: List<&2, Maybe<&2, String>>
  {String.order(SCon{'a',M.suffix(xs)},M.suffix(xs)) == LT{} : Cmp}
def suffix_before(xs):
  match xs:
    case Nil{}: {==}
    case Con{x,rest}: suffix_before(rest)

law key_before:
  for p: M.Principal
  for +xs: List<&2,Maybe<&2,String>>
  {String.is_lt(M.key(p,Con{None{},xs}),M.key(p,xs)) == True{} : Bool}
def key_before(p,xs):
  match p:
    case M.Alice{}: Equal.cong(Cmp,Bool,Cmp.is_lt,String.order(SCon{'a',M.suffix(xs)},M.suffix(xs)),LT{},suffix_before(xs))
    case M.Bob{}: Equal.cong(Cmp,Bool,Cmp.is_lt,String.order(SCon{'a',M.suffix(xs)},M.suffix(xs)),LT{},suffix_before(xs))

def Above(+k: String, rows: List<&2,D.Row>) -> Data:
  match rows:
    case Nil{}: Unit
    case Con{r,rest}: M.Both<{String.is_lt(k,D.row_key(r)) == True{} : Bool},Above(k,rest)>

def below_notes(+p: M.Principal, xs: List<&2,Maybe<&2,String>>, +k: String, +tail: List<&2,D.Row>,
  lt: {String.is_lt(k,M.key(p,xs)) == True{} : Bool}, +h: Above(k,tail)) -> Above(k,M.notes(p,xs,tail)):
  match xs:
    case Nil{}: h
    case Con{None{},+rest}:
      below_notes(p,rest,k,tail,O.string_lt_trans(k,M.key(p,Con{None{},rest}),M.key(p,rest),lt,key_before(p,rest)),h)
    case Con{Some{t},+rest}:
      +next = O.string_lt_trans(k,M.key(p,Con{Some{t},rest}),M.key(p,rest),lt,key_before(p,rest))
      M.Both{next,below_notes(p,rest,k,tail,next,h)}

def fresh_before_notes(+p: M.Principal, xs: List<&2,Maybe<&2,String>>, +tail: List<&2,D.Row>,
  +h: Above(M.key(p,xs),tail)) -> Above(M.key(p,xs),M.notes(p,xs,tail)):
  match xs:
    case Nil{}: h
    case Con{None{},+rest}: below_notes(p,rest,M.key(p,Con{None{},rest}),tail,key_before(p,rest),h)
    case Con{Some{t},+rest}:
      M.Both{key_before(p,rest),below_notes(p,rest,M.key(p,Con{Some{t},rest}),tail,key_before(p,rest),h)}

law insert_first:
  for +rows: List<&2,D.Row>
  for +new: D.Row
  for h: Above(D.row_key(new),rows)
  {D.insert_row(rows,new) == new <> rows : List<&2,D.Row>}
def insert_first(rows,new,h):
  match rows h:
    case Nil{} Unit{}: {==}
    case Con{r,rest} M.Both{lt,tail}:
      %Equal.sym(Bool,String.is_lt(D.row_key(new),D.row_key(r)),True{},lt) :
        {Bool.pick(List<&2,D.Row>,_,new <> r <> rest,
          Bool.pick(List<&2,D.Row>,String.eq(D.row_key(new),D.row_key(r)),new <> rest,r <> D.insert_row(rest,new))) == new <> r <> rest : List<&2,D.Row>}
      {==}

# Every tombstone consumes an address, but contributes no business key.
def active_keys(+p: M.Principal, mask: String) -> List<&2,String>:
  match mask:
    case SNil{}: Nil{}
    case SCon{'+',+rest}: Client.key(p,rest) <> active_keys(p,rest)
    case SCon{c,rest}: active_keys(p,rest)

law exact_directory_keys:
  for +p: M.Principal
  for +xs: List<&2,Maybe<&2,String>>
  {active_keys(p,M.mask(xs)) == D.keys_rows(M.notes(p,xs,Nil{})) : List<&2,String>}
def exact_directory_keys(p,xs):
  match xs:
    case Nil{}: {==}
    case Con{None{},rest}: exact_directory_keys(p,rest)
    case Con{Some{t},+rest}:
      %Equal.sym(String,Client.key(p,M.mask(rest)),M.key(p,rest),key_mask(p,rest)) :
        {_ <> active_keys(p,M.mask(rest)) == M.key(p,rest) <> D.keys_rows(M.notes(p,rest,Nil{})) : List<&2,String>}
      Equal.cong(List<&2,String>,List<&2,String>,ks => M.key(p,rest) <> ks,
        active_keys(p,M.mask(rest)),D.keys_rows(M.notes(p,rest,Nil{})),exact_directory_keys(p,rest))
