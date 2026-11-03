import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate(s, valid, identity, n):
  match n:
    case 0n:
      L.Both{L.Both{{==}, Unit{}}, L.Both{{==}, Unit{}}}
    case 1n+m:
      match m:
        case 0n:
          L.Both{L.Both{L.Both{{==}, Unit{}}, L.Both{{==}, Unit{}}},
            L.Both{L.Both{{==}, Unit{}}, Unit{}}}
        case 1n+k:
          L.Both{L.Both{L.Both{{==}, Unit{}}, L.Both{{==}, Unit{}}},
            L.Both{L.Both{{==}, Unit{}}, Unit{}}}

def B.terminates(s, ctx, args):
  (1n, s, Nil{}, S.Response{S.Refusal{}, D.VInt{0, 6}}, {==})
