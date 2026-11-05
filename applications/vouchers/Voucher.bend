# Frozen administrator specification and ordinary optional helper client.
# Separate rows in each principal's table: r:<request> and v:<request>.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Receipts.bend as H

type Command is Data:
  Issue{request: String, input: String, cancel: Bool}
  Retire{request: String}
  Inspect{request: String}
  Permission{enabled: Bool}
  Invalid{}

def operation() -> String:
  "voucher.issue/v1"

def receipt(request: String) -> String:
  String.append("r:", request)

def voucher(request: String) -> String:
  String.append("v:", request)

# Input is exactly one Unicode text value. Identity encoding is injective;
# no parsing ambiguities, hashing, numeric narrowing, or Unicode normalization.
def canonical(input: String, cancel: Bool) -> String:
  match cancel:
    case False{}: String.append("0:", input)
    case True{}: String.append("1:", input)

def fields(+owner: String, +key: String, input: String, op: String, result: String) -> List<&2, D.Field>:
  [D.Field{"enabled", D.VAbsent{}}, D.Field{"id", D.VText{key}}, D.Field{"input", D.VText{input}},
    D.Field{"operation", D.VText{op}}, D.Field{"owner", D.VText{owner}},
    D.Field{"result", D.VText{result}}]

def finish(cancel: Bool, result: String) -> S.Action:
  match cancel:
    case True{}: S.Refuse{D.VText{"cancelled"}}
    case False{}: S.Finish{D.VText{result}}

def create(+owner: String, +request: String, +input: String, +cancel: Bool) -> S.Action:
  H.put(owner, voucher(request), fields(owner, voucher(request), input, operation(), voucher(request)),
    H.put(owner, receipt(request), fields(owner, receipt(request), canonical(input, cancel), operation(), voucher(request)),
      finish(cancel, voucher(request))))

def finish_result(value: H.Lookup) -> S.Action:
  match value:
    case H.StoredText{v}: S.Finish{D.VText{v}}
    case H.Missing{}: S.Refuse{D.VText{"invalid receipt"}}
    case H.Unexpected{}: S.Refuse{D.VText{"invalid receipt"}}

def result(request: String, r: S.Return) -> S.Action:
  finish_result(H.observed(r))

def operation_seen(+owner: String, +request: String, +input: String, op: S.Return) -> S.Action:
  H.operation_seen(owner, receipt(request), operation(), result(request), op)

def input_seen(+owner: String, +request: String, +input: String, +cancel: Bool, r: S.Return) -> S.Action:
  H.input_seen(owner, receipt(request), operation(), canonical(input, cancel),
    create(owner, request, input, cancel), result(request), r)

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{+cmd}, D.VList{D.VText{+request}, D.VList{D.VText{input}, D.VList{D.VBool{cancel}, D.VListEmpty{}}}}}:
      Bool.pick(Command, String.eq(cmd, "issue"), Issue{request, input, cancel}, Invalid{})
    case D.VList{D.VText{+cmd}, D.VList{D.VBool{enabled}, D.VListEmpty{}}}:
      Bool.pick(Command, String.eq(cmd, "permission"), Permission{enabled}, Invalid{})
    case D.VList{D.VText{+cmd}, D.VList{D.VText{+request}, D.VListEmpty{}}}:
      Bool.pick(Command, String.eq(cmd, "retire"), Retire{request},
        Bool.pick(Command, String.eq(cmd, "inspect"), Inspect{request}, Invalid{}))
    case _: Invalid{}

def inspected_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: v
    case _: D.VAbsent{}

def inspected(r: S.Return) -> S.Action:
  S.Finish{inspected_value(r)}

def command(+owner: String, p: Command) -> S.Action:
  match p:
    case Issue{+request, +input, +cancel}:
      H.bound(owner, receipt(request), operation(), canonical(input, cancel),
        create(owner, request, input, cancel), result(request))
    case Retire{+request}:
      S.Access{D.RemoveRow{D.Application{owner}, receipt(request)}, H.written(
        S.Access{D.RemoveRow{D.Application{owner}, voucher(request)}, H.written(S.Finish{D.VText{"retired"}})})}
    case Inspect{request}:
      S.Access{D.ReadCell{D.Application{owner}, voucher(request), "input"},
        inspected}
    case Permission{enabled}:
      H.put(owner, "permission", [D.Field{"enabled", D.VBool{enabled}},
        D.Field{"id", D.VText{"permission"}}, D.Field{"input", D.VAbsent{}},
        D.Field{"operation", D.VAbsent{}}, D.Field{"owner", D.VText{owner}},
        D.Field{"result", D.VAbsent{}}], S.Finish{D.VText{"permission updated"}})
    case Invalid{}: S.Refuse{D.VText{"invalid request"}}

# Receipt hits need the same present application permission as a fresh issue.
# The mutable ordinary gate row is consulted on every call, including hits.
def enabled(r: S.Return) -> Bool:
  match r:
    case S.Datum{D.Cell{D.VBool{b}}}: b
    case _: False{}

def permit(ok: Bool, owner: String, p: Command) -> S.Action:
  match ok:
    case True{}: command(owner, p)
    case False{}: S.Refuse{D.VText{"permission denied"}}

def permitted(owner: String, p: Command, r: S.Return) -> S.Action:
  permit(enabled(r), owner, p)

def sized(ok: Bool, +owner: String, +request: String, input: String, cancel: Bool) -> S.Action:
  match ok:
    case False{}: S.Refuse{D.VText{"request ID too long"}}
    case True{}:
      S.Access{D.ReadCell{D.Application{owner}, "permission", "enabled"}, permitted(owner, Issue{request, input, cancel})}

def dispatch(+owner: String, p: Command) -> S.Action:
  match p:
    case Permission{enabled}: command(owner, Permission{enabled})
    case Issue{+request, input, cancel}:
      sized(Nat.is_le(String.length(request), 64n), owner, request, input, cancel)
    case Retire{request}:
      S.Access{D.ReadCell{D.Application{owner}, "permission", "enabled"}, permitted(owner, Retire{request})}
    case Inspect{request}:
      S.Access{D.ReadCell{D.Application{owner}, "permission", "enabled"}, permitted(owner, Inspect{request})}
    case Invalid{}: S.Refuse{D.VText{"invalid request"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  dispatch(id, analyze(args))

def program() -> S.Program:
  S.Program{start}
