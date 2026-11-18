# A faithful host retains the state while the worker advances through the wire reply.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../src/Codec.bend as Codec
import ../src/ControlBridge.bend as ControlBridge
import ../src/Remote.bend as Remote
import ./ControlTransport.bend as ControlTransport
import ./Foundations.bend as F
import ./RemoteCount.bend as Count
import ./RemoteReplyBytes.bend as Wire

def count_value(n: Maybe<&2, B.Number64>) -> D.Value:
  match n:
    case None{}: D.VAbsent{}
    case Some{B.Number64{high, low}}: D.VInt{high, low}

def host_answer(result: D.ResultOp) -> Wire.Envelope:
  match result:
    case D.FailureData{}: Wire.ResultOnly{"data_error"}
    case D.Changed{w}: Wire.ResultOnly{"changed"}
    case D.Observed{D.RowAbsent{}}: Wire.ResultOnly{"row_absent"}
    case D.Observed{D.Cell{v}}: Wire.ResultWith{"cell", "value", v}
    case D.Observed{D.Existence{exists}}: Wire.ResultWith{"existence", "exists", D.VBool{exists}}
    case D.Observed{D.Count{n}}: Wire.ResultWith{"count", "count", count_value(B.nat64(n))}
    case D.Observed{D.Keys{xs}}: Wire.ResultWith{"keys", "keys", ControlBridge.strings(xs)}

def host_reply(e: D.Schema, w: D.State, op: D.Operation) -> Maybe<&2, List<&2, U32>>:
  Wire.encode(host_answer(D.operate(e, w, op)))

def host_names(result: D.ResultOp) -> Wire.NamesValid(host_answer(result)):
  match result:
    case D.FailureData{}: {==}
    case D.Changed{w}: {==}
    case D.Observed{D.RowAbsent{}}: {==}
    case D.Observed{D.Cell{v}}: ({==}, {==})
    case D.Observed{D.Existence{exists}}: ({==}, {==})
    case D.Observed{D.Count{n}}: ({==}, {==})
    case D.Observed{D.Keys{xs}}: ({==}, {==})

type CountWords<-n: Nat> is Type:
  CountWords{high: U32, low: U32,
    measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>},
    in_range: {U32.is_lt(high, 65536) == True{} : Bool}}

def CountRepresentable(result: D.ResultOp) -> Type:
  match result:
    case D.Observed{D.Count{n}}: CountWords<n>
    case _: Unit

def write_operation(op: D.Operation) -> Bool:
  match op:
    case D.DefineRow{_, _, _}: True{}
    case D.DefineColumn{_, _, _, _}: True{}
    case D.RemoveRow{_, _}: True{}
    case _: False{}

def compatible_observation(op: D.Operation, observed: D.Observation) -> Bool:
  match op observed:
    case D.ReadCell{_, _, _} D.RowAbsent{}: True{}
    case D.ReadCell{_, _, _} D.Cell{_}: True{}
    case D.ViewExistence{_, _} D.Existence{_}: True{}
    case D.CountRows{_} D.Count{_}: True{}
    case D.EnumerateKeys{_} D.Keys{_}: True{}
    case _ _: False{}

def compatible(op: D.Operation, result: D.ResultOp) -> Bool:
  match result:
    case D.FailureData{}: True{}
    case D.Changed{_}: write_operation(op)
    case D.Observed{v}: compatible_observation(op, v)

def field_compatible(+op: D.Operation, found: Maybe<&2, D.Value>,
  cell: @v: D.Value -> {compatible_observation(op, D.Cell{v}) == True{} : Bool}) ->
  {compatible(op, D.result_cell(found)) == True{} : Bool}:
  match found:
    case None{}: {==}
    case Some{v}: cell(v)

def cell_compatible(+op: D.Operation, found: Maybe<&2, D.Column>, row: Maybe<&2, D.Row>, column: String,
  absent: {compatible_observation(op, D.RowAbsent{}) == True{} : Bool},
  cell: @v: D.Value -> {compatible_observation(op, D.Cell{v}) == True{} : Bool}) ->
  {compatible(op, D.read_column(found, row, column)) == True{} : Bool}:
  match found row:
    case None{} _: {==}
    case Some{_} None{}: absent
    case Some{_} Some{D.Row{key, fields}}:
      field_compatible(op, D.find_field(fields, column), cell)

def write_compatible(+op: D.Operation, ok: Bool, c: D.Collection, w: D.State, rows: List<&2, D.Row>,
  writing: {write_operation(op) == True{} : Bool}) ->
  {compatible(op, D.write_se(ok, c, w, rows)) == True{} : Bool}:
  match ok:
    case False{}: {==}
    case True{}: writing

def resolved_compatible(+op: D.Operation, resolved: Maybe<&2, D.Resolved>, w: D.State) ->
  {compatible(op, D.operate_resolved(op, resolved, w)) == True{} : Bool}:
  match op resolved:
    case D.ReadCell{+c, +key, +column} Some{D.Resolved{D.SchemaTable{name, primary, columns}, rows}}:
      cell_compatible(D.ReadCell{c, key, column}, D.find_column(columns, column),
        D.find_row(rows, key), column, {==}, _ => {==})
    case D.ViewExistence{_, _} Some{D.Resolved{_, _}}: {==}
    case D.CountRows{_} Some{D.Resolved{_, _}}: {==}
    case D.EnumerateKeys{_} Some{D.Resolved{_, _}}: {==}
    case D.DefineRow{+c, +key, +fields} Some{D.Resolved{schema, rows}}:
      write_compatible(D.DefineRow{c, key, fields}, D.row_is_valid(schema, D.Row{key, fields}),
        c, w, D.insert_row(rows, D.Row{key, fields}), {==})
    case D.DefineColumn{+c, +key, +column, +v} Some{D.Resolved{D.SchemaTable{name, primary, columns}, rows}}:
      write_compatible(D.DefineColumn{c, key, column, v},
        D.column_write_is_valid(D.find_column(columns, column), primary, key, v),
        c, w, D.substitute_column(rows, key, column, v), {==})
    case D.RemoveRow{_, _} Some{D.Resolved{_, _}}: {==}
    case _ None{}: {==}

def address_compatible(ok: Bool, e: D.Schema, +w: D.State, +op: D.Operation) ->
  {compatible(op, D.operate_address(ok, e, w, op)) == True{} : Bool}:
  match ok:
    case False{}: {==}
    case True{}:
      +c = D.collection_op(op)
      resolved_compatible(op, D.resolve_parts(D.schema_collection(c, e), D.rows_collection(c, w)), w)

law operate_returns_compatible_answer:
  for +e: D.Schema
  for w: D.State
  for +op: D.Operation
  {compatible(op, D.operate(e, w, op)) == True{} : Bool}
def operate_returns_compatible_answer(e, w, op):
  address_compatible(D.address_op_valid(op), e, w, op)

def spec_delivery(-A: Type, result: D.ResultOp, failure: Unit -> A, k: S.Return -> A) -> A:
  match result:
    case D.FailureData{}: failure(Unit{})
    case D.Changed{_}: k(S.UnitValue{})
    case D.Observed{v}: k(S.Datum{v})

def incompatible_answer(-A: Type, -op: D.Operation, -result: D.ResultOp,
  -invalid: A, -failure: Unit -> A, -k: S.Return -> A, impossible: {False{} == True{} : Bool}) ->
  {Remote.decode_operation(A, op, Codec.Decoded{Wire.flattened(host_answer(result))}, invalid, failure, k) ==
    spec_delivery(A, result, failure, k) : A}:
  F.absurd_boolean({Remote.decode_operation(A, op, Codec.Decoded{Wire.flattened(host_answer(result))}, invalid, failure, k) ==
    spec_delivery(A, result, failure, k) : A}, impossible)

def resumed_count(-A: Type, +high: U32, +low: U32, +n: Nat,
  -invalid: A, -k: S.Return -> A,
  measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}) ->
  {Remote.resume(A, Remote.count(True{}, high, low, 65536), invalid, k) == k(S.Datum{D.Count{n}}) : A}:
  Equal.trans(A, Remote.resume(A, Remote.count(True{}, high, low, 65536), invalid, k),
    Remote.resume(A, Some{S.Datum{D.Count{n}}}, invalid, k), k(S.Datum{D.Count{n}}),
    Equal.cong(Maybe<&2, S.Return>, A, v => Remote.resume(A, v, invalid, k),
      Remote.count(True{}, high, low, 65536), Some{S.Datum{D.Count{n}}},
      Count.count_decodes_exact_natural(high, low, n, measured)), {==})

def decoded_host_answer(-A: Type, +op: D.Operation, +result: D.ResultOp,
  range: CountRepresentable(result), correct: {compatible(op, result) == True{} : Bool},
  -invalid: A, -failure: Unit -> A, -k: S.Return -> A) ->
  {Remote.decode_operation(A, op, Codec.Decoded{Wire.flattened(host_answer(result))}, invalid, failure, k) ==
    spec_delivery(A, result, failure, k) : A}:
  match op result:
    case _ D.FailureData{}: {==}
    case D.ReadCell{_, _, _} D.Observed{D.RowAbsent{}}: {==}
    case D.ReadCell{_, _, _} D.Observed{D.Cell{_}}: {==}
    case D.ViewExistence{_, _} D.Observed{D.Existence{_}}: {==}
    case D.CountRows{_} D.Observed{D.Count{+n}}:
      match range:
        case CountWords{+high, +low, +measured, in_range}:
          %Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{B.Number64{high, low}}, measured) :
            {Remote.decode_operation(A, op, Codec.Decoded{D.VList{D.VText{"result"}, D.VList{D.VText{"count"},
              D.VList{D.VText{"count"}, D.VList{count_value(_), D.VListEmpty{}}}}}}, invalid, failure, k) ==
              k(S.Datum{D.Count{n}}) : A}
          %Equal.sym(Bool, U32.is_lt(high, 65536), True{}, in_range) :
            {Remote.resume(A, Remote.count(_, high, low, 65536), invalid, k) == k(S.Datum{D.Count{n}}) : A}
          resumed_count(A, high, low, n, invalid, k, measured)
    case D.EnumerateKeys{_} D.Observed{D.Keys{+xs}}:
      Equal.cong(Maybe<&2, List<&2, String>>, A, v => Remote.resume(A, Remote.keys(v), invalid, k),
        ControlBridge.read_strings(ControlBridge.strings(xs)), Some{xs}, ControlTransport.strings_roundtrip(xs))
    case D.DefineRow{_, _, _} D.Changed{_}: {==}
    case D.DefineColumn{_, _, _, _} D.Changed{_}: {==}
    case D.RemoveRow{_, _} D.Changed{_}: {==}
    case D.ReadCell{_, _, _} D.Observed{D.Existence{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ReadCell{_, _, _} D.Observed{D.Count{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ReadCell{_, _, _} D.Observed{D.Keys{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ReadCell{_, _, _} D.Changed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ViewExistence{_, _} D.Observed{D.RowAbsent{}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ViewExistence{_, _} D.Observed{D.Cell{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ViewExistence{_, _} D.Observed{D.Count{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ViewExistence{_, _} D.Observed{D.Keys{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.ViewExistence{_, _} D.Changed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.CountRows{_} D.Observed{D.RowAbsent{}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.CountRows{_} D.Observed{D.Cell{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.CountRows{_} D.Observed{D.Existence{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.CountRows{_} D.Observed{D.Keys{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.CountRows{_} D.Changed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.EnumerateKeys{_} D.Observed{D.RowAbsent{}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.EnumerateKeys{_} D.Observed{D.Cell{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.EnumerateKeys{_} D.Observed{D.Existence{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.EnumerateKeys{_} D.Observed{D.Count{_}}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.EnumerateKeys{_} D.Changed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.DefineRow{_, _, _} D.Observed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.DefineColumn{_, _, _, _} D.Observed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)
    case D.RemoveRow{_, _} D.Observed{_}: incompatible_answer(A, op, result, invalid, failure, k, correct)

type ReplyAvailable<-result: D.ResultOp, -bytes: List<&2, U32>> is Type:
  ReplyAvailable{body: B.Number64,
    range: CountRepresentable(result),
    encoded: {Wire.encode(host_answer(result)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}}

law faithful_answer_decodes:
  for -A: Type
  for +op: D.Operation
  for +result: D.ResultOp
  for +bytes: List<&2, U32>
  for available: ReplyAvailable<result, bytes>
  for correct: {compatible(op, result) == True{} : Bool}
  for -invalid: A
  for -failure: Unit -> A
  for -k: S.Return -> A
  {Remote.decode_operation(A, op, Remote.answer(bytes), invalid, failure, k) ==
    spec_delivery(A, result, failure, k) : A}
def faithful_answer_decodes(A, op, result, bytes, available, correct, invalid, failure, k):
  match available:
    case ReplyAvailable{body, range, encoded, measured}:
      %Equal.sym(Codec.Outcome, Remote.answer(bytes), Codec.Decoded{Wire.flattened(host_answer(result))},
        Wire.answer_encoding_roundtrip(host_answer(result), host_names(result), bytes,
          body, encoded, measured)) :
        {Remote.decode_operation(A, op, _, invalid, failure, k) == spec_delivery(A, result, failure, k) : A}
      decoded_host_answer(A, op, result, range, correct, invalid, failure, k)

def working_after(result: D.ResultOp, w: D.State) -> D.State:
  match result:
    case D.Changed{next}: next
    case _: w

def returned_step(w: D.State, op: D.Operation, k: S.Return -> S.Action, +value: S.Return) -> S.Step:
  match value:
    case S.Datum{+v}: S.Continue{w, k(S.Datum{v}), S.OperationEvent{op, S.Reading{v}}}
    case S.UnitValue{}: S.Continue{w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}}

def failed_step(w: D.State, op: D.Operation) -> S.Step:
  S.OperationFailed{w, S.OperationEvent{op, S.ErrorOfData{}}}

def pending_step(+op: D.Operation, result: D.ResultOp, +w: D.State, k: S.Return -> S.Action,
  bytes: List<&2, U32>) -> Maybe<&1, S.Step>:
  Remote.decode_operation(Maybe<&1, S.Step>, op, Remote.answer(bytes), None{},
    _ => Some{failed_step(w, op)}, value => Some{returned_step(working_after(result, w), op, k, value)})

def delivered_step(+op: D.Operation, +result: D.ResultOp, +w: D.State, -k: S.Return -> S.Action) ->
  {spec_delivery(Maybe<&1, S.Step>, result, _ => Some{failed_step(w, op)},
    value => Some{returned_step(working_after(result, w), op, k, value)}) ==
    Some{S.apply(result, w, op, k)} : Maybe<&1, S.Step>}:
  match result:
    case D.FailureData{}: {==}
    case D.Changed{_}: {==}
    case D.Observed{_}: {==}

law pending_step_refines_contract:
  for +e: D.Schema
  for +w: D.State
  for +op: D.Operation
  for -k: S.Return -> S.Action
  for +bytes: List<&2, U32>
  for reply: ReplyAvailable<D.operate(e, w, op), bytes>
  {pending_step(op, D.operate(e, w, op), w, k, bytes) ==
    Some{S.step(S.Access{op, k}, e, w)} : Maybe<&1, S.Step>}
def pending_step_refines_contract(e, w, op, k, bytes, reply):
  +result = D.operate(e, w, op)
  Equal.trans(Maybe<&1, S.Step>, pending_step(op, result, w, k, bytes),
    spec_delivery(Maybe<&1, S.Step>, result, _ => Some{failed_step(w, op)},
      value => Some{returned_step(working_after(result, w), op, k, value)}),
    Some{S.apply(result, w, op, k)},
    faithful_answer_decodes(Maybe<&1, S.Step>, op, result, bytes, reply, operate_returns_compatible_answer(e, w, op),
      None{}, _ => Some{failed_step(w, op)}, value => Some{returned_step(working_after(result, w), op, k, value)}),
    delivered_step(op, result, w, k))

# The logical trace retains the proposal. The actual worker renders that
# proposal via its response-side finalizer, or continues with the next action.
def iteration_after_step(step: S.Step, limit: Nat) -> Remote.Iteration:
  match step:
    case S.Continue{_, a, _}: Remote.run(a, limit)
    case S.Stopped{_, S.Response{status, value}}: Remote.finalize(status, value, limit)
    case S.OperationFailed{_, _}: Remote.error(S.DataError{})

def delivered_iteration(result: D.ResultOp, w: D.State, op: D.Operation, -k: S.Return -> S.Action, +limit: Nat) ->
  {spec_delivery(Remote.Iteration, result, _ => Remote.error(S.DataError{}),
    value => Remote.run(k(value), limit)) == iteration_after_step(S.apply(result, w, op, k), limit) : Remote.Iteration}:
  match result:
    case D.FailureData{}: {==}
    case D.Changed{_}: {==}
    case D.Observed{_}: {==}

law worker_pending_reply_refines_contract:
  for +e: D.Schema
  for +w: D.State
  for +op: D.Operation
  for -k: S.Return -> S.Action
  for +limit: Nat
  for +bytes: List<&2, U32>
  for reply: ReplyAvailable<D.operate(e, w, op), bytes>
  {Remote.reply_operation(op, k, limit, bytes) ==
    iteration_after_step(S.step(S.Access{op, k}, e, w), limit) : Remote.Iteration}
def worker_pending_reply_refines_contract(e, w, op, k, limit, bytes, reply):
  +result = D.operate(e, w, op)
  Equal.trans(Remote.Iteration,
    Remote.reply_operation(op, k, limit, bytes),
    spec_delivery(Remote.Iteration, result, _ => Remote.error(S.DataError{}), value => Remote.run(k(value), limit)),
    iteration_after_step(S.apply(result, w, op, k), limit),
    faithful_answer_decodes(Remote.Iteration, op, result, bytes, reply, operate_returns_compatible_answer(e, w, op),
      Remote.Inconsistent{}, _ => Remote.error(S.DataError{}), value => Remote.run(k(value), limit)),
    delivered_iteration(result, w, op, k, limit))

def operation_body(op: D.Operation) -> Maybe<&2, List<&2, U32>>:
  P.finalize(Remote.fields(Remote.operation(op)))

law worker_run_asks_for_operation:
  for +op: D.Operation
  for -k: S.Return -> S.Action
  for +limit: Nat
  for +bytes: List<&2, U32>
  for encoded: {operation_body(op) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {Remote.run(S.Access{op, k}, limit) == Remote.Ask{Con{2, bytes}, Remote.OperationReply{op, k, limit}} : Remote.Iteration}
def worker_run_asks_for_operation(op, k, limit, bytes, encoded):
  Equal.cong(Maybe<&2, List<&2, U32>>, Remote.Iteration,
    out => Remote.ask_operation(out, Remote.OperationReply{op, k, limit}), operation_body(op), Some{bytes}, encoded)

def exchanged(request: Maybe<&2, List<&2, U32>>, reply: Maybe<&2, List<&2, U32>>,
  op: D.Operation, result: D.ResultOp, w: D.State, k: S.Return -> S.Action) -> Maybe<&1, S.Step>:
  match request reply:
    case Some{_} Some{bytes}: pending_step(op, result, w, k, bytes)
    case _ _: None{}

def remote_step(a: S.Action, e: D.Schema, +w: D.State) -> Maybe<&1, S.Step>:
  match a:
    case S.Finish{v}: Some{S.Stopped{w, S.Response{S.Success{}, v}}}
    case S.Refuse{v}: Some{S.Stopped{w, S.Response{S.Refusal{}, v}}}
    case S.Access{+op, k}:
      +result = D.operate(e, w, op)
      exchanged(operation_body(op), Wire.encode(host_answer(result)), op, result, w, k)

type ExchangeAvailable<-e: D.Schema, -w: D.State, -op: D.Operation> is Type:
  ExchangeAvailable{request: List<&2, U32>, reply: List<&2, U32>,
    request_encoded: {operation_body(op) == Some{request} : Maybe<&2, List<&2, U32>>},
    reply_available: ReplyAvailable<D.operate(e, w, op), reply>}

type StepAvailable<-a: S.Action, -e: D.Schema, -w: D.State> is Type:
  FinishAvailable{v: D.Value, action: {a == S.Finish{v} : S.Action}}
  RefuseAvailable{v: D.Value, action: {a == S.Refuse{v} : S.Action}}
  AccessAvailable{op: D.Operation, -k: S.Return -> S.Action, action: {a == S.Access{op, k} : S.Action},
    wire: ExchangeAvailable<e, w, op>}

def exchange_refines_contract(+op: D.Operation, -k: S.Return -> S.Action, +e: D.Schema, +w: D.State,
  available: ExchangeAvailable<e, w, op>) ->
  {remote_step(S.Access{op, k}, e, w) == Some{S.step(S.Access{op, k}, e, w)} : Maybe<&1, S.Step>}:
  match available:
    case ExchangeAvailable{+request, +reply, request_encoded, ReplyAvailable{body, range, +encoded, measured}}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, operation_body(op), Some{request}, request_encoded) :
        {exchanged(_, host_reply(e, w, op), op, D.operate(e, w, op), w, k) ==
          Some{S.step(S.Access{op, k}, e, w)} : Maybe<&1, S.Step>}
      %Equal.sym(Maybe<&2, List<&2, U32>>, host_reply(e, w, op), Some{reply}, encoded) :
        {exchanged(Some{request}, _, op, D.operate(e, w, op), w, k) ==
          Some{S.step(S.Access{op, k}, e, w)} : Maybe<&1, S.Step>}
      pending_step_refines_contract(e, w, op, k, reply, ReplyAvailable{body, range, encoded, measured})

law remote_step_refines_contract:
  for -a: S.Action
  for +e: D.Schema
  for +w: D.State
  for available: StepAvailable<a, e, w>
  {remote_step(a, e, w) == Some{S.step(a, e, w)} : Maybe<&1, S.Step>}
def remote_step_refines_contract(a, e, w, available):
  match available:
    case FinishAvailable{v, action}:
      %Equal.sym(S.Action, a, S.Finish{v}, action) :
        {remote_step(_, e, w) == Some{S.step(_, e, w)} : Maybe<&1, S.Step>}
      {==}
    case RefuseAvailable{v, action}:
      %Equal.sym(S.Action, a, S.Refuse{v}, action) :
        {remote_step(_, e, w) == Some{S.step(_, e, w)} : Maybe<&1, S.Step>}
      {==}
    case AccessAvailable{+op, k, action, wire}:
      %Equal.sym(S.Action, a, S.Access{op, k}, action) :
        {remote_step(_, e, w) == Some{S.step(_, e, w)} : Maybe<&1, S.Step>}
      exchange_refines_contract(op, k, e, w, wire)

law worker_terminal_step_refines_contract:
  for +status_value: D.Value
  for -e: D.Schema
  for -w: D.State
  for -limit: Nat
  {Remote.run(S.Finish{status_value}, limit) == iteration_after_step(S.step(S.Finish{status_value}, e, w), limit) : Remote.Iteration} &
  {Remote.run(S.Refuse{status_value}, limit) == iteration_after_step(S.step(S.Refuse{status_value}, e, w), limit) : Remote.Iteration}
def worker_terminal_step_refines_contract(status_value, e, w, limit):
  ({==}, {==})
