import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Instance.bend as I
import ./Client.bend as Client
import ./RequestFacts.bend as F

def code() -> String:
  "import Base\nimport ./Data.bend as D\nimport ./Semantics.bend as S\n\ndef count(xs: List<U32>, acc: U32) -> U32:\n  match xs:\n    case Nil{}:\n      acc\n    case Con{h, t}:\n      count(t, (acc + h : U32))\n\ndef program() -> S.Program:\n  S.Program{c => a => S.Refuse{D.VInt{0, count([1, 2, 3], 0)}}}\n"

law certificate:
  R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())

law terminates:
  F.ProgramTerminates(I.config(), Client.program())
