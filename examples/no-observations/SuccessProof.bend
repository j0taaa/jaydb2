import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def publication_unchanged(r: S.Response, -s: D.State,
  valid: R.Valid(I.config(), s)) -> R.PublicationValid(r, I.config(), s):
  match r:
    case S.Response{S.Success{}, v}:
      valid
    case S.Response{S.Refusal{}, v}:
      Unit{}
    case S.Response{S.Input{}, v}:
      Unit{}
    case S.Response{S.Authentication{}, v}:
      Unit{}
    case S.Response{S.Certificate{}, v}:
      Unit{}
    case S.Response{S.DataError{}, v}:
      Unit{}
    case S.Response{S.Limit{}, v}:
      Unit{}
    case S.Response{S.Failure{}, v}:
      Unit{}

def prefix(-s: D.State) -> R.SafetyPrefix(I.config(), s,
  I.context(), B.code(), I.arguments(), s, Nil{}):
  L.Both{L.Both{{==}, Unit{}}, L.Both{{==}, Unit{}}}

def final(s: D.State, valid: R.Valid(I.config(), s)) ->
  R.SafetyFinal(I.config(), s, I.context(), B.code(), I.arguments(), s,
    Nil{}, R.finalize(S.Response{S.Success{}, D.VInt{0, 6}}, I.config(), s)):
  L.Both{L.Both{{==}, Unit{}},
    publication_unchanged(R.finalize(S.Response{S.Success{}, D.VInt{0, 6}}, I.config(), s), s, valid)}

def B.certificate(s, valid, identity, n):
  match n:
    case 0n:
      prefix(s)
    case 1n+m:
      match m:
        case 0n:
          L.Both{prefix(s), final(s, valid)}
        case 1n+k:
          L.Both{prefix(s), final(s, valid)}

def B.terminates(s, ctx, args):
  (1n, s, Nil{}, S.Response{S.Success{}, D.VInt{0, 6}}, {==})
