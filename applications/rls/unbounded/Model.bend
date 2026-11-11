# Unbounded slot histories. A '-' is a tombstone, never a listed note.
# Lists here are mathematical finite lists, with no fixed slot bound.
import Base
import ./Data.bend as D

type Principal is Data:
  Alice{}
  Bob{}

def owner(p: Principal) -> String:
  match p:
    case Alice{}: "alice"
    case Bob{}: "bob"

def prefix(p: Principal) -> String:
  match p:
    case Alice{}: "alice/"
    case Bob{}: "bob/"

def directory(p: Principal) -> String:
  match p:
    case Alice{}: "alice/_dir"
    case Bob{}: "bob/_dir"

# More recent allocations sort BEFORE older allocations: z, az, aaz, ... .
def suffix(xs: List<&2, Maybe<&2, String>>) -> String:
  match xs:
    case Nil{}: "z"
    case Con{x, rest}: SCon{'a', suffix(rest)}

def key(p: Principal, xs: List<&2, Maybe<&2, String>>) -> String:
  prefix(p) ++ suffix(xs)

def mask(xs: List<&2, Maybe<&2, String>>) -> String:
  match xs:
    case Nil{}: ""
    case Con{None{}, rest}: SCon{'-', mask(rest)}
    case Con{Some{text}, rest}: SCon{'+', mask(rest)}

def fields(+p: Principal, +key: String, text: String) -> List<&2, D.Field>:
  [D.Field{"id", D.VText{key}}, D.Field{"owner", D.VText{owner(p)}}, D.Field{"text", D.VText{text}}]

def row(+p: Principal, xs: List<&2, Maybe<&2, String>>, text: String) -> D.Row:
  +k = key(p, xs)
  D.Row{k, fields(p, k, text)}

def dir(+p: Principal, text: String) -> D.Row:
  +k = directory(p)
  D.Row{k, fields(p, k, text)}

def notes(+p: Principal, xs: List<&2, Maybe<&2, String>>, +tail: List<&2, D.Row>) -> List<&2, D.Row>:
  match xs:
    case Nil{}: tail
    case Con{None{}, rest}: notes(p, rest, tail)
    case Con{Some{text}, +rest}: row(p, rest, text) <> notes(p, rest, tail)

def user(+id: String, kind: String) -> D.Row:
  D.Row{id, [D.Field{"credential", D.VText{id ++ "-token"}},
    D.Field{"id", D.VText{id}}, D.Field{"kind", D.VText{kind}}]}

def users() -> List<&2, D.Row>:
  [user("admin", "admin"), user("alice", "user"), user("bob", "user")]

def parts(+a: List<&2, Maybe<&2, String>>, +b: List<&2, Maybe<&2, String>>, da: String, db: String) -> D.State:
  D.State{[D.Table{"notes", dir(Alice{}, da) <> notes(Alice{}, a,
    dir(Bob{}, db) <> notes(Bob{}, b, Nil{}))}], users()}

def state(+a: List<&2, Maybe<&2, String>>, +b: List<&2, Maybe<&2, String>>) -> D.State:
  parts(a, b, mask(a), mask(b))

# Prefixes may have arbitrary directory text, including a stale bitmap.
type LayoutProof<-s: D.State> is Data:
  Laid{a: List<&2, Maybe<&2, String>>, b: List<&2, Maybe<&2, String>>,
    da: String, db: String, same: {s == parts(a, b, da, db) : D.State}}

# The exact DIRECTORY/BUSINESS-ROW relationship, with no bound on either list.
# Each '+' has exactly its generated row; each '-' has none; no other rows exist.
type ExactProof<-s: D.State> is Data:
  Exact{a: List<&2, Maybe<&2, String>>, b: List<&2, Maybe<&2, String>>,
    same: {s == state(a, b) : D.State}}

def Layout(s: D.State) -> Data:
  LayoutProof<s>

def Coherent(s: D.State) -> Data:
  ExactProof<s>

# Local proof product used by the directory algebra.
type Both<-P:Data,-Q:Data> is Data:
  Both{left:P,right:Q}
