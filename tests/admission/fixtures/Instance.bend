import Base
import ./Data.bend as D
import ./Semantics.bend as S

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
    S.Limits{256n, 256n, 256n}, "Bend-2.0.39-CPU"}

def context() -> D.Context:
  D.Context{"alice", "user"}

def arguments() -> D.Value:
  D.VInt{0, 42}
