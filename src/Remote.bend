# State-free execution over the private operation/reply protocol.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../contract/PreparedRegistry.bend as Registry
import ./Codec.bend as Codec
import ./ControlBridge.bend as ControlBridge
import ./Dispatch.bend as Dispatch
import ./Gate.bend as Gate
import ./Input.bend as Input
import ./Resolve.bend as Resolve
import ./Transport.bend as T
import ./Worker.bend as Worker

type Pending is Type:
  AuthenticationReply{credential: String, request: P.Request,
    entries: Maybe<&2, List<&2, Registry.Entry>>, admit: Gate.Oracle()}
  OperationReply{operation: D.Operation, resume: S.Return -> S.Action, limit: Nat}

type Iteration is Type:
  Ask{bytes: List<&2, U32>, pending: Pending}
  Final{bytes: List<&2, U32>}
  Inconsistent{}

def collection(c: D.Collection) -> D.Value:
  match c:
    case D.Users{}: D.VAbsent{}
    case D.Application{name}: D.VText{name}

def operation(o: D.Operation) -> List<&2, D.Field>:
  match o:
    case D.ReadCell{c, key, column}:
      [D.Field{"op", D.VText{"read_cell"}}, D.Field{"collection", collection(c)},
        D.Field{"key", D.VText{key}}, D.Field{"column", D.VText{column}}]
    case D.ViewExistence{c, key}:
      [D.Field{"op", D.VText{"existence"}}, D.Field{"collection", collection(c)}, D.Field{"key", D.VText{key}}]
    case D.CountRows{c}:
      [D.Field{"op", D.VText{"count"}}, D.Field{"collection", collection(c)}]
    case D.EnumerateKeys{c}:
      [D.Field{"op", D.VText{"keys"}}, D.Field{"collection", collection(c)}]
    case D.DefineRow{c, key, fields}:
      [D.Field{"op", D.VText{"define_row"}}, D.Field{"collection", collection(c)},
        D.Field{"key", D.VText{key}}, D.Field{"fields", D.fields_value(fields)}]
    case D.DefineColumn{c, key, column, value}:
      [D.Field{"op", D.VText{"define_column"}}, D.Field{"collection", collection(c)},
        D.Field{"key", D.VText{key}}, D.Field{"column", D.VText{column}}, D.Field{"value", value}]
    case D.RemoveRow{c, key}:
      [D.Field{"op", D.VText{"remove_row"}}, D.Field{"collection", collection(c)}, D.Field{"key", D.VText{key}}]

# Only the outer record has the ABI's fixed order. Encode each field value
# with the checked canonical encoder, including the nested row record.
def fields(fs: List<&2, D.Field>) -> P.Partial:
  match fs:
    case Nil{}: P.Record{0n, Nil{}}
    case Con{D.Field{name, value}, rest}: P.record_cases(P.text(name), P.encode(value), fields(rest))

# A record's payload is a sequence of text-name/value pairs. Reframe the
# outer record as a list of those elements for the canonical decoder. The
# continuation checks the exact list shape, including each name and order.
def answer_fields(ok: Bool, n: U32, rest: List<&2, U32>) -> Codec.Outcome:
  match ok:
    case True{}: Codec.decode(Con{5, B.concatenate(B.be64(0, (n * 2 : U32)), rest)},
      B.Number64{4294967295, 4294967295})
    case False{}: Codec.Input{}

def answer(bytes: List<&2, U32>) -> Codec.Outcome:
  match bytes:
    case Con{6, Con{0, Con{0, Con{0, Con{0, Con{0, Con{0, Con{0, +n <> rest}}}}}}}}:
      answer_fields(U32.is_le(n, 4), n, rest)
    case _: Codec.Input{}

def final_bytes(tag: U32, bytes: Maybe<&2, List<&2, U32>>) -> Iteration:
  match bytes:
    case None{}: Inconsistent{}
    case Some{bs}: Final{Con{tag, bs}}

# 0 keeps, 1 commits after host state validation, and 3 validates the
# proposed success state before keeping the worker's response failure.
def final_response(tag: U32, r: S.Response) -> Iteration:
  final_bytes(tag, P.frame(S.response_value(r)))

def finish_success(+r: S.Response) -> Iteration:
  match r:
    case S.Response{S.Success{}, v}: final_response(1, r)
    case _: final_response(3, r)

def proposed_success(status: S.Status) -> Bool:
  match status:
    case S.Success{}: True{}
    case _: False{}

def checked_response(success: Bool, r: S.Response) -> Iteration:
  match success:
    case True{}: finish_success(r)
    case False{}: final_response(0, r)

def finalize(+status: S.Status, +value: D.Value, +limit: Nat) -> Iteration:
  +r = {S.Response{status, value} : S.Response}
  checked_response(proposed_success(status), R.response_technique_cases(D.value_valid(value),
    R.fits(limit, S.response_value(r)), r))

def error(status: S.Status) -> Iteration:
  final_response(0, S.response_error(status))

# Answers are checked against the particular pending operation. A valid
# data_error ends the request without invoking the program's continuation.
# Bend's native Nat is limited to 48 bits in this toolchain version.
def count(ok: Bool, high: U32, low: U32) -> Maybe<&2, S.Return>:
  match ok:
    case True{}:
      # Convert word literals at runtime to keep the BendTT term compact.
      +half_word = U32.to_nat(65536)
      word = Nat.mul(half_word, half_word)
      Some{S.Datum{D.Count{Nat.add(Nat.mul(U32.to_nat(high), word), U32.to_nat(low))}}}
    case False{}: None{}

def keys(strings: Maybe<&2, List<&2, String>>) -> Maybe<&2, S.Return>:
  match strings:
    case Some{xs}: Some{S.Datum{D.Keys{xs}}}
    case None{}: None{}

def returned(ok: Bool, value: S.Return) -> Maybe<&2, S.Return>:
  match ok:
    case True{}: Some{value}
    case False{}: None{}

def named(result: String, expected: String, field: String, wanted: String) -> Bool:
  String.eq(result, expected) && String.eq(field, wanted)

def keys_result(ok: Bool, value: D.Value) -> Maybe<&2, S.Return>:
  match ok:
    case True{}: keys(ControlBridge.read_strings(value))
    case False{}: None{}

def observed(o: D.Operation, +result: String, fields: D.Value) -> Maybe<&2, S.Return>:
  match o fields:
    case D.ReadCell{_, _, _} D.VListEmpty{}:
      returned(String.eq(result, "row_absent"), S.Datum{D.RowAbsent{}})
    case D.ReadCell{_, _, _} D.VList{D.VText{name}, D.VList{value, D.VListEmpty{}}}:
      returned(named(result, "cell", name, "value"), S.Datum{D.Cell{value}})
    case D.ViewExistence{_, _} D.VList{D.VText{name}, D.VList{D.VBool{exists}, D.VListEmpty{}}}:
      returned(named(result, "existence", name, "exists"), S.Datum{D.Existence{exists}})
    case D.CountRows{_} D.VList{D.VText{name}, D.VList{D.VInt{+high, low}, D.VListEmpty{}}}:
      count(named(result, "count", name, "count") && U32.is_lt(high, 65536), high, low)
    case D.EnumerateKeys{_} D.VList{D.VText{name}, D.VList{xs, D.VListEmpty{}}}:
      keys_result(named(result, "keys", name, "keys"), xs)
    case D.DefineRow{_, _, _} D.VListEmpty{}: returned(String.eq(result, "changed"), S.UnitValue{})
    case D.DefineColumn{_, _, _, _} D.VListEmpty{}: returned(String.eq(result, "changed"), S.UnitValue{})
    case D.RemoveRow{_, _} D.VListEmpty{}: returned(String.eq(result, "changed"), S.UnitValue{})
    case _ _: None{}

def resume(value: Maybe<&2, S.Return>, k: S.Return -> Iteration) -> Iteration:
  match value:
    case Some{r}: k(r)
    case None{}: Inconsistent{}

def operation_result(valid: Bool, data_error: Bool, o: D.Operation, result: String,
  fields: D.Value, k: S.Return -> Iteration) -> Iteration:
  match valid data_error:
    case False{} _: Inconsistent{}
    case True{} True{}: error(S.DataError{})
    case True{} False{}: resume(observed(o, result, fields), k)

def empty_fields(fields: D.Value) -> Bool:
  match fields:
    case D.VListEmpty{}: True{}
    case _: False{}

def answer_operation(o: D.Operation, reply: Codec.Outcome, k: S.Return -> Iteration) -> Iteration:
  match reply:
    case Codec.Decoded{D.VList{D.VText{name}, D.VList{D.VText{+result}, +fields}}}:
      operation_result(String.eq(name, "result"), String.eq(result, "data_error") && empty_fields(fields),
        o, result, fields, k)
    case _: Inconsistent{}

def ask_operation(encoded: Maybe<&2, List<&2, U32>>, pending: Pending) -> Iteration:
  match encoded:
    case None{}: error(S.DataError{})
    case Some{bytes}: Ask{Con{2, bytes}, pending}

def run(a: S.Action, +limit: Nat) -> Iteration:
  match a:
    case S.Finish{v}: finalize(S.Success{}, v, limit)
    case S.Refuse{v}: finalize(S.Refusal{}, v, limit)
    case S.Access{+op, k}:
      ask_operation(P.finalize(fields(operation(op))), OperationReply{op, k, limit})

def admitted(v: Gate.Verdict, ctx: D.Context, args: D.Value, limit: Nat) -> Iteration:
  match v:
    case Gate.Reject{}: error(S.Certificate{})
    case Gate.ToolFailure{}: error(S.Failure{})
    case Gate.Accept{program}: run(S.start(program, ctx, args), limit)

def selected(~c: S.Configuration, selection: Resolve.Selection, +ctx: D.Context,
  admit: Gate.Oracle()) -> Iteration:
  match selection:
    case Resolve.Denied{status}: error(status)
    case Resolve.Selected{+r}: admitted(admit(c, r, ctx), ctx, Gate.arguments(r), R.limit_response(S.limits(c)))

def authenticated(~c: S.Configuration, ctx: Maybe<&2, D.Context>, raw: P.Request,
  entries: Maybe<&2, List<&2, Registry.Entry>>, admit: Gate.Oracle()) -> Iteration:
  match ctx:
    case None{}: error(S.Authentication{})
    case Some{+identity}:
      match entries:
        case None{}: selected(c, Resolve.Selected{raw}, identity, admit)
        case Some{registry}:
          selected(c, Resolve.authenticated(Some{identity}, S.environment(c), registry, raw), identity, admit)

def user_state(+id: String, kind: String, credential: String) -> D.State:
  D.State{Nil{}, [D.Row{id, [D.Field{"credential", D.VText{credential}},
    D.Field{"id", D.VText{id}}, D.Field{"kind", D.VText{kind}}]}]}

def authenticate_user(valid: Bool, id: String, kind: String, token: String,
  credential: String, next: Maybe<&2, D.Context> -> Iteration) -> Iteration:
  match valid:
    case True{}: next(D.authenticate(user_state(id, kind, token), credential))
    case False{}: Inconsistent{}

def no_user(valid: Bool, next: Maybe<&2, D.Context> -> Iteration) -> Iteration:
  match valid:
    case True{}: next(None{})
    case False{}: Inconsistent{}

def answer_authentication(reply: Codec.Outcome, credential: String,
  next: Maybe<&2, D.Context> -> Iteration) -> Iteration:
  match reply:
    case Codec.Decoded{D.VList{D.VText{name}, D.VList{D.VText{result}, D.VListEmpty{}}}}:
      no_user(String.eq(name, "result") && String.eq(result, "no_user"), next)
    case Codec.Decoded{D.VList{D.VText{name}, D.VList{D.VText{result},
      D.VList{D.VText{id_key}, D.VList{D.VText{id}, D.VList{D.VText{kind_key}, D.VList{D.VText{kind},
      D.VList{D.VText{token_key}, D.VList{D.VText{+token}, D.VListEmpty{}}}}}}}}}}:
      authenticate_user(String.eq(name, "result") && String.eq(result, "user") &&
        String.eq(id_key, "id") && String.eq(kind_key, "kind") && String.eq(token_key, "credential") &&
        Bool.not(String.is_empty(token)), id, kind, token, credential, next)
    case _: Inconsistent{}

def ask_authentication(encoded: Maybe<&2, List<&2, U32>>, pending: Pending) -> Iteration:
  match encoded:
    case None{}: Inconsistent{}
    case Some{bytes}: Ask{Con{2, bytes}, pending}

def decoded(input: Input.PreAuthentication,
  entries: Maybe<&2, List<&2, Registry.Entry>>, admit: Gate.Oracle()) -> Iteration:
  match input:
    case Input.ErrorTransport{}: Inconsistent{}
    case Input.ErrorMessage{status}: error(status)
    case Input.InputReady{s, +raw}:
      +credential = Gate.credential(raw)
      ask_authentication(P.finalize(fields([D.Field{"op", D.VText{"authenticate"}}, D.Field{"credential", D.VText{credential}}])),
        AuthenticationReply{credential, raw, entries, admit})

# The existing decoders thread the state through as opaque payload. Supply
# an empty placeholder and discard it. Only D.authenticate sees a user row.
def packet(~c: S.Configuration, bytes: List<&2, U32>, admit: Gate.Oracle()) -> Iteration:
  decoded(Input.read_message(B.nat64(R.limit_message(S.limits(c))), bytes, D.State{Nil{}, Nil{}}),
    None{}, admit)

def registered_packet(~c: S.Configuration, parts: Maybe<&2, T.Parts>, code: String,
  proof: String, admit: Gate.Oracle()) -> Iteration:
  match parts:
    case None{}: Inconsistent{}
    case Some{T.Parts{registry, body}}:
      decoded(Dispatch.execution(Dispatch.received(S.limits(c), body, D.State{Nil{}, Nil{}})),
        Some{Worker.registry_entries(ControlBridge.decode_registry(registry))}, Worker.artifact_oracle(code, proof, admit))

def reply(~c: S.Configuration, pending: Pending, bytes: List<&2, U32>) -> Iteration:
  match pending:
    case AuthenticationReply{credential, raw, entries, admit}:
      answer_authentication(answer(bytes), credential, ctx => authenticated(c, ctx, raw, entries, admit))
    case OperationReply{op, k, limit}:
      answer_operation(op, answer(bytes), r => run(k(r), limit))
