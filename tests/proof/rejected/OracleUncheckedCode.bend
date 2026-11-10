# This oracle accepts even when the request's code fails the installed law.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../contract/Theorems.bend as T
import ../../../contract/Logic.bend as L
import ../../../src/Gate.bend as Gate
import ../Controls.bend as C

def exact_code(h: S.Situation) -> Type:
  match h:
    case S.Executing{s, ctx, code, args, w, ts}: {code == "checked" : String}
    case _: Unit

def config() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.MoreOneLaw{exact_code, S.NoneLaw{}}, S.Limits{1024n, 1024n, 256n}, "oracle-negative"}

def unchecked(c: S.Configuration, r: P.Request, ctx: D.Context) -> Gate.Verdict:
  Gate.Accept{C.program()}

law checked_code_prefix:
  R.SafetyPrefix(config(), C.seed(), C.context(), "checked", D.VAbsent{}, C.seed(), Nil{})
def checked_code_prefix():
  L.Both{L.Both{{==}, Unit{}}, L.Both{Unit{}, Unit{}}}

def certificate(+ctx: D.Context, +code: String, +same: {code == "checked" : String},
  +s: D.State, valid: R.Valid(config(), s), identity: {D.context_present(s, ctx) == True{} : Bool}, n: Nat) ->
  R.SafetyTrace(S.execute(n, C.program(), S.schema(config()), s, ctx, D.VAbsent{}), config(), s, ctx, code, D.VAbsent{}):
  match n:
    case 0n: L.Both{L.Both{same, Unit{}}, L.Both{Unit{}, Unit{}}}
    case 1n+m:
      match m:
        case 0n: L.Both{L.Both{L.Both{same, Unit{}}, L.Both{Unit{}, Unit{}}}, L.Both{L.Both{Unit{}, Unit{}}, Unit{}}}
        case 1n+k: L.Both{L.Both{L.Both{same, Unit{}}, L.Both{Unit{}, Unit{}}}, L.Both{L.Both{Unit{}, Unit{}}, Unit{}}}

law false:
  T.OracleSoundness(config(), C.request(), unchecked)
def false(ctx):
  L.Both{certificate(ctx, Gate.code(C.request()), {==}),
    s => (1n, s, Nil{}, S.Response{S.Refusal{}, D.VAbsent{}}, {==})}
