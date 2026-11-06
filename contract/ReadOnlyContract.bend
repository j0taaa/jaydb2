# Fixed whole-program read-only predicate, independent of the implementation.
# A finite witness covers every return continuation for each context/argument.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L

def Operation(o: D.Operation) -> Type:
  match o:
    case D.ReadCell{c, k, n}: Unit
    case D.ViewExistence{c, k}: Unit
    case D.CountRows{c}: Unit
    case D.EnumerateKeys{c}: Unit
    case _: Empty

def Prefix(n: Nat, a: S.Action) -> Type:
  match n:
    case 0n: Unit
    case 1n+k:
      match a:
        case S.Finish{v}: Unit
        case S.Refuse{v}: Unit
        case S.Access{o, resume}:
          L.E<Operation(o), @r: S.Return -> Prefix(k, resume(r))>

def Action(n: Nat, a: S.Action) -> Type:
  match n:
    case 0n: Empty
    case 1n+k:
      match a:
        case S.Finish{v}: Unit
        case S.Refuse{v}: Unit
        case S.Access{o, resume}:
          L.E<Operation(o), @r: S.Return -> Action(k, resume(r))>

def Program(-p: S.Program) -> Type:
  @ctx: D.Context -> @args: D.Value -> &n: Nat ->
    Action(n, S.start(p, ctx, args))
