# Small typed CPS observation adapters. Each emits exactly the named access.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

def keys_return(done: List<&2, String> -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Keys{xs}}: done(xs)
    case _: S.Refuse{D.VText{"unexpected keys return"}}

def keys(c: D.Collection, done: List<&2, String> -> S.Action) -> S.Action:
  S.Access{D.EnumerateKeys{c}, keys_return(done)}

def exists_return(done: Bool -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Existence{b}}: done(b)
    case _: S.Refuse{D.VText{"unexpected existence return"}}

def exists(c: D.Collection, key: String, done: Bool -> S.Action) -> S.Action:
  S.Access{D.ViewExistence{c, key}, exists_return(done)}

def count_return(done: Nat -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Count{n}}: done(n)
    case _: S.Refuse{D.VText{"unexpected count return"}}

def count(c: D.Collection, done: Nat -> S.Action) -> S.Action:
  S.Access{D.CountRows{c}, count_return(done)}
