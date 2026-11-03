import Base
import ./ClientProof.bend as Proof
import ./Client.bend as Client
import ./Instance.bend as I
import ./Data.bend as D
import ./Semantics.bend as S

def result(a: S.Action) -> D.Value:
  match a:
    case S.Refuse{v}:
      v
    case _:
      D.VAbsent{}

def main() -> D.Value:
  result(S.start(Client.program(), I.context(), I.arguments()))
