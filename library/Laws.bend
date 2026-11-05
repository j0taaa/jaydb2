# Templates only: allow is supplied and proved by the APPLICATION. No certificate.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ../src/Termination.bend as T
import ./Query.bend as Q

def Safe(~allow: D.Context -> D.Operation -> Data, d: Nat, +ctx: D.Context, a: S.Action) -> Type:
  match d:
    case Zero{}: Empty
    case Succ{m}:
      match a:
        case S.Finish{v}: Unit
        case S.Refuse{v}: Unit
        case S.Access{op, k}: L.E<allow(ctx, op), @r: S.Return -> Safe(~allow, m, ctx, k(r))>

def depth(xs: List<&2, String>, n: Nat) -> Nat:
  match xs:
    case Nil{}: n
    case Con{x, rest}: Succ{depth(rest, n)}

def ReadPermissions(~allow: D.Context -> D.Operation -> Data, +ctx: D.Context,
  +c: D.Collection, +key: String, xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{name, rest}: L.E<allow(ctx, D.ReadCell{c, key, name}), ReadPermissions(~allow, ctx, c, key, rest)>

def reads(~allow: D.Context -> D.Operation -> Data, xs: List<&2, String>, +n: Nat,
  +ctx: D.Context, +c: D.Collection, +key: String, -done: Q.Selection -> S.Action,
  permission: ReadPermissions(~allow, ctx, c, key, xs),
  h: @result: Q.Selection -> Safe(~allow, n, ctx, done(result))) ->
  Safe(~allow, depth(xs, n), ctx, Q.read_fields(c, key, xs, done)):
  match xs permission:
    case Nil{} Unit{}: h(Q.Selected{D.VRecordEmpty{}})
    case Con{+name, +rest} L.Both{p, tail}:
      L.Both{p, +r => reads(~allow, rest, n, ctx, c, key,
        result => done(Q.combine(name, r, result)), tail,
        result => h(Q.combine(name, r, result)))}

def finite(~allow: D.Context -> D.Operation -> Data, d: Nat, a: S.Action,
  +ctx: D.Context, h: Safe(~allow, d, ctx, a)) -> T.Finite(d, a):
  match d a h:
    case Zero{} a h: L.ex_false(T.Finite(0n, a), h)
    case Succ{m} S.Finish{v} Unit{}: Unit{}
    case Succ{m} S.Refuse{v} Unit{}: Unit{}
    case Succ{m} S.Access{op, k} L.Both{p, cont}: +r => finite(~allow, m, k(r), ctx, cont(r))

# Batch-write construction requires one supplied permission for each row and
# the entire continuation. This is still not an administrator certificate.
def RowPermissions(~allow: D.Context -> D.Operation -> Data, +ctx: D.Context,
  +c: D.Collection, xs: List<&2, D.Row>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{D.Row{k, fs}, rest}: L.E<allow(ctx, D.DefineRow{c, k, fs}), RowPermissions(~allow, ctx, c, rest)>
