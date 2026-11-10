# An owned-prefix observer follows a fixed number of Access continuations,
# then hands control back as Action. The inductive prefix spine gives constant
# time prepend and additive composition without copying affine Actions.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

type Prefix is Type:
  Stop{remaining: S.Action}
  More{operation: D.Operation,later: Prefix}

def prefix(operations: List<&2,D.Operation>,remaining: S.Action) -> Prefix:
  match operations:
    case Nil{}: Stop{remaining}
    case Con{op,tail}: More{op,prefix(tail,remaining)}

def prepend(operation: D.Operation,later: Prefix) -> Prefix:
  More{operation,later}

def cut(~Env: Data,~reply: Env -> Nat -> S.Return,+env: Env,steps: Nat,+index: Nat,action: S.Action) -> Prefix:
  match steps:
    case 0n: Stop{action}
    case 1n+previous:
      match action:
        case S.Finish{value}: Stop{S.Finish{value}}
        case S.Refuse{value}: Stop{S.Refuse{value}}
        case S.Access{operation,resume}: More{operation,cut(~Env,~reply,env,previous,1n+index,resume(reply(env,index)))}
