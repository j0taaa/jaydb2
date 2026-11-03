import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E

# Example of a propositional law: programs in this instance cannot access data.
# The user registry still exists and authentication is performed by the core.
def NotObserves(h: S.Situation) -> Type:
  match h:
    case S.Stable{s}:
      Unit
    case S.Executing{s, c, p, a, w, ts}:
      {ts == Nil{} : List<&2, S.OperationEvent>}
    case S.Closed{s, c, p, a, w, ts, r}:
      {ts == Nil{} : List<&2, S.OperationEvent>}

def config() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.MoreOneLaw{NotObserves, S.NoneLaw{}},
    S.Limits{32768n, 65536n, 32768n}, E.identity()}
