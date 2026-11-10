import Base
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/Semantics.bend as S
import ../../src/Gate.bend as K
import ../../contract/Theorems.bend as G

def configuration() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, S.Limits{1024n, 1024n, 256n}, "controls"}

def seed() -> D.State:
  D.State{Nil{}, [D.Row{"alice", [D.Field{"credential", D.VText{"token"}},
    D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]}]}

def changed() -> D.State:
  D.State{Nil{}, Nil{}}

def request() -> P.Request:
  P.Request{"token", "refuse", D.VAbsent{}, "certificate"}

def context() -> D.Context:
  D.Context{"alice", "user"}

def spoof() -> D.Context:
  D.Context{"bob", "admin"}

def program() -> S.Program:
  S.Program{ctx => args => S.Refuse{D.VAbsent{}}}

def reject(c: S.Configuration, r: P.Request, ctx: D.Context) -> K.Verdict:
  K.Reject{}

# Each negative uses exactly one of the clauses used inside Core, at a concrete
# wrong transition/output. These positive counterparts rule out malformed setup.
law correct_identity:
  G.Identity(seed(), request(), context())
def correct_identity(): {==}

law correct_refusal:
  G.Publication(S.Response{S.Refusal{}, D.VAbsent{}}, seed(), changed(), seed())
def correct_refusal(): {==}
