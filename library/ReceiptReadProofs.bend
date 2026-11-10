# Total actual engine meaning of Receipt.bound for ALL input DATA. Each real
# read's result kind is proved internally. Callback actions remain arbitrary;
# owned reads stop at the exact miss/result handoff, refusal or data failure.
import Base
import ./ReceiptReadPlan.bend as M
import ./ReceiptAdapterProofs.bend as Adapter
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Receipts.bend as H
import ./ReadOperationProofs.bend as Failure
import ./QueryReadTrace.bend as History
import ./Proofs.bend as Event
import ../proof/Foundations.bend as F
import ../src/Termination.bend as T

def finish(plan: M.Plan,+remaining: Nat,+schema: D.Schema,+state: D.State,missing: S.Action,done: S.Return -> S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match plan:
    case M.ReceiptMissing{events}: T.observe(2n+remaining,missing,schema,state,History.append_events(events,history))
    case M.ReceiptResult{reply,events}: T.observe(remaining,done(reply),schema,state,History.append_events(events,history))
    case M.ReceiptRefused{reason,events}: S.Final{state,History.append_events(events,history),S.Response{S.Refusal{},reason}}
    case M.ReceiptFailure{events}: S.Final{state,History.append_events(events,history),S.Response{S.DataError{},D.VAbsent{}}}

law prepending_a_receipt_plan_event_is_exact_history_extension:
  for +plan: M.Plan
  for +event: S.OperationEvent
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  {finish(M.prepend(event,plan),remaining,schema,state,missing,done,history) == finish(plan,remaining,schema,state,missing,done,S.append(history,event)) : S.Trace}
def prepending_a_receipt_plan_event_is_exact_history_extension(plan,event,remaining,schema,state,missing,done,history):
  match plan:
    case M.ReceiptMissing{events}: {==}
    case M.ReceiptResult{reply,events}: {==}
    case M.ReceiptRefused{reason,events}: {==}
    case M.ReceiptFailure{events}: {==}

def result_case(+result: D.ResultOp,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,state,M.read(owner,key,"result")) == result : D.ResultOp},kind: Failure.ResultKind(Failure.Cell{},result)) -> {T.observe(1n+remaining,S.Access{M.read(owner,key,"result"),done},schema,state,history) == finish(M.result(owner,key,result),remaining,schema,state,missing,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Failure.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(remaining,schema,state,M.read(owner,key,"result"),done,history,actual)
    case D.Observed{+observation}: Event.read_continuation(remaining,schema,state,M.read(owner,key,"result"),observation,done,history,actual)
    case D.Changed{working}: F.absurd_boolean({T.observe(1n+remaining,S.Access{M.read(owner,key,"result"),done},schema,state,history) == finish(M.result(owner,key,D.Changed{working}),remaining,schema,state,missing,done,history) : S.Trace},kind)

def actual_result(+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>) -> {T.observe(1n+remaining,S.Access{M.read(owner,key,"result"),done},schema,state,history) == finish(M.result_plan(schema,state,owner,key),remaining,schema,state,missing,done,history) : S.Trace}:
  result_case(D.operate(schema,state,M.read(owner,key,"result")),remaining,schema,state,owner,key,missing,done,history,{==},Failure.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Failure.Cell{},schema,state,D.Application{owner},key,"result"))

def operation_boolean(ok: Bool,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>) -> {T.observe(1n+remaining,H.operation_match(ok,owner,key,done),schema,state,history) == finish(Bool.pick(M.Plan,ok,M.result_plan(schema,state,owner,key),M.ReceiptRefused{D.VText{"request conflict"},Nil{}}),remaining,schema,state,missing,done,history) : S.Trace}:
  match ok:
    case True{}: actual_result(remaining,schema,state,owner,key,missing,done,history)
    case False{}: T.stopped(remaining,state,S.Response{S.Refusal{},D.VText{"request conflict"}},schema,history)

def operation_class(value: H.Lookup,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,+expected: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>) -> {T.observe(1n+remaining,H.operation_value(owner,key,expected,done,value),schema,state,history) == finish(M.operation_value(value,expected,M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,history) : S.Trace}:
  match value:
    case H.StoredText{actual}: operation_boolean(String.eq(actual,expected),remaining,schema,state,owner,key,missing,done,history)
    case H.Missing{}: T.stopped(remaining,state,S.Response{S.Refusal{},D.VText{"invalid receipt"}},schema,history)
    case H.Unexpected{}: T.stopped(remaining,state,S.Response{S.Refusal{},D.VText{"invalid receipt"}},schema,history)

def operation_case(+result: D.ResultOp,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,+expected: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,state,M.read(owner,key,"operation")) == result : D.ResultOp},kind: Failure.ResultKind(Failure.Cell{},result)) -> {T.observe(2n+remaining,S.Access{M.read(owner,key,"operation"),H.operation_seen(owner,key,expected,done)},schema,state,history) == finish(M.operation(owner,key,expected,result,M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Failure.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(1n+remaining,schema,state,M.read(owner,key,"operation"),H.operation_seen(owner,key,expected,done),history,actual)
    case D.Changed{working}: F.absurd_boolean({T.observe(2n+remaining,S.Access{M.read(owner,key,"operation"),H.operation_seen(owner,key,expected,done)},schema,state,history) == finish(M.operation(owner,key,expected,D.Changed{working},M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,history) : S.Trace},kind)
    case D.Observed{+observation}:
      Equal.trans(S.Trace,T.observe(2n+remaining,S.Access{M.read(owner,key,"operation"),H.operation_seen(owner,key,expected,done)},schema,state,history),T.observe(1n+remaining,H.operation_seen(owner,key,expected,done,S.Datum{observation}),schema,state,S.append(history,S.OperationEvent{M.read(owner,key,"operation"),S.Reading{observation}})),finish(M.operation(owner,key,expected,D.Observed{observation},M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,history),Event.read_continuation(1n+remaining,schema,state,M.read(owner,key,"operation"),observation,H.operation_seen(owner,key,expected,done),history,actual),Equal.trans(S.Trace,T.observe(1n+remaining,H.operation_seen(owner,key,expected,done,S.Datum{observation}),schema,state,S.append(history,S.OperationEvent{M.read(owner,key,"operation"),S.Reading{observation}})),finish(M.operation_value(H.observed(S.Datum{observation}),expected,M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,S.append(history,S.OperationEvent{M.read(owner,key,"operation"),S.Reading{observation}})),finish(M.operation(owner,key,expected,D.Observed{observation},M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,history),operation_class(H.observed(S.Datum{observation}),remaining,schema,state,owner,key,expected,missing,done,S.append(history,S.OperationEvent{M.read(owner,key,"operation"),S.Reading{observation}})),Equal.sym(S.Trace,finish(M.operation(owner,key,expected,D.Observed{observation},M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,history),finish(M.operation_value(H.observed(S.Datum{observation}),expected,M.result_plan(schema,state,owner,key)),remaining,schema,state,missing,done,S.append(history,S.OperationEvent{M.read(owner,key,"operation"),S.Reading{observation}})),prepending_a_receipt_plan_event_is_exact_history_extension(M.operation_value(H.observed(S.Datum{observation}),expected,M.result_plan(schema,state,owner,key)),S.OperationEvent{M.read(owner,key,"operation"),S.Reading{observation}},remaining,schema,state,missing,done,history))))

def actual_operation(+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,+expected: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>) -> {T.observe(2n+remaining,S.Access{M.read(owner,key,"operation"),H.operation_seen(owner,key,expected,done)},schema,state,history) == finish(M.operation_plan(schema,state,owner,key,expected),remaining,schema,state,missing,done,history) : S.Trace}:
  operation_case(D.operate(schema,state,M.read(owner,key,"operation")),remaining,schema,state,owner,key,expected,missing,done,history,{==},Failure.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Failure.Cell{},schema,state,D.Application{owner},key,"operation"))

def input_boolean(ok: Bool,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>) -> {T.observe(2n+remaining,H.input_match(ok,owner,key,operation,done),schema,state,history) == finish(Bool.pick(M.Plan,ok,M.operation_plan(schema,state,owner,key,operation),M.ReceiptRefused{D.VText{"request conflict"},Nil{}}),remaining,schema,state,missing,done,history) : S.Trace}:
  match ok:
    case True{}: actual_operation(remaining,schema,state,owner,key,operation,missing,done,history)
    case False{}: T.stopped(1n+remaining,state,S.Response{S.Refusal{},D.VText{"request conflict"}},schema,history)

def input_class(value: H.Lookup,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>) -> {T.observe(2n+remaining,H.input_value(owner,key,operation,input,missing,done,value),schema,state,history) == finish(M.input_value(value,input,M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,history) : S.Trace}:
  match value:
    case H.Missing{}: {==}
    case H.StoredText{actual}: input_boolean(String.eq(actual,input),remaining,schema,state,owner,key,operation,missing,done,history)
    case H.Unexpected{}: T.stopped(1n+remaining,state,S.Response{S.Refusal{},D.VText{"invalid receipt"}},schema,history)

def input_case(+result: D.ResultOp,+remaining: Nat,+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,state,M.read(owner,key,"input")) == result : D.ResultOp},kind: Failure.ResultKind(Failure.Cell{},result)) -> {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == finish(M.input(owner,key,input,result,M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,history) : S.Trace}:
  match result:
    case D.FailureData{}: Failure.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(2n+remaining,schema,state,M.read(owner,key,"input"),H.input_seen(owner,key,operation,input,missing,done),history,actual)
    case D.Changed{working}: F.absurd_boolean({T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == finish(M.input(owner,key,input,D.Changed{working},M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,history) : S.Trace},kind)
    case D.Observed{+observation}:
      Equal.trans(S.Trace,T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history),T.observe(2n+remaining,H.input_seen(owner,key,operation,input,missing,done,S.Datum{observation}),schema,state,S.append(history,S.OperationEvent{M.read(owner,key,"input"),S.Reading{observation}})),finish(M.input(owner,key,input,D.Observed{observation},M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,history),Event.read_continuation(2n+remaining,schema,state,M.read(owner,key,"input"),observation,H.input_seen(owner,key,operation,input,missing,done),history,actual),Equal.trans(S.Trace,T.observe(2n+remaining,H.input_seen(owner,key,operation,input,missing,done,S.Datum{observation}),schema,state,S.append(history,S.OperationEvent{M.read(owner,key,"input"),S.Reading{observation}})),finish(M.input_value(H.observed(S.Datum{observation}),input,M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,S.append(history,S.OperationEvent{M.read(owner,key,"input"),S.Reading{observation}})),finish(M.input(owner,key,input,D.Observed{observation},M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,history),input_class(H.observed(S.Datum{observation}),remaining,schema,state,owner,key,operation,input,missing,done,S.append(history,S.OperationEvent{M.read(owner,key,"input"),S.Reading{observation}})),Equal.sym(S.Trace,finish(M.input(owner,key,input,D.Observed{observation},M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,history),finish(M.input_value(H.observed(S.Datum{observation}),input,M.operation_plan(schema,state,owner,key,operation)),remaining,schema,state,missing,done,S.append(history,S.OperationEvent{M.read(owner,key,"input"),S.Reading{observation}})),prepending_a_receipt_plan_event_is_exact_history_extension(M.input_value(H.observed(S.Datum{observation}),input,M.operation_plan(schema,state,owner,key,operation)),S.OperationEvent{M.read(owner,key,"input"),S.Reading{observation}},remaining,schema,state,missing,done,history))))

law actual_bound_has_total_exact_source_state_history_short_circuit_and_callback_behavior:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +operation: String
  for +input: String
  for +remaining: Nat
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == finish(M.plan(schema,state,owner,key,operation,input),remaining,schema,state,missing,done,history) : S.Trace}
def actual_bound_has_total_exact_source_state_history_short_circuit_and_callback_behavior(schema,state,owner,key,operation,input,remaining,missing,done,history):
  input_case(D.operate(schema,state,M.read(owner,key,"input")),remaining,schema,state,owner,key,operation,input,missing,done,history,{==},Failure.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Failure.Cell{},schema,state,D.Application{owner},key,"input"))

law receipt_lookup_emits_exactly_the_named_input_access_before_its_caller:
  for +owner: String
  for +key: String
  for -done: S.Return -> S.Action
  {H.lookup(owner,key,done) == S.Access{M.read(owner,key,"input"),done} : S.Action}
def receipt_lookup_emits_exactly_the_named_input_access_before_its_caller(owner,key,done): {==}
