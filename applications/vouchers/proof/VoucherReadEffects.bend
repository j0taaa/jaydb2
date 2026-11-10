# ALL-FUEL actual receipt and inspection source paths. The named source
# callbacks are proved here for every observed return; no whole-trace premise.
import Base
import ./VoucherSuccessEffects.bend as E
import ./VoucherExecutionSteps.bend as Step
import ./VoucherWriteEffects.bend as Writes
import ../Voucher.bend as V
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../src/Termination.bend as T

def result_class(+fuel: Nat,+initial: D.State,+schema: D.Schema,value: H.Lookup,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,V.finish_result(value),schema,initial,history)):
  match value:
    case H.StoredText{text}: Step.identity_finish(fuel,initial,schema,history,D.VText{text})
    case H.Missing{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid receipt"})
    case H.Unexpected{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid receipt"})

def result_read(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,S.Access{D.ReadCell{D.Application{owner},V.receipt(request),"result"},V.result(request)},schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.cell_read(n,initial,initial,schema,D.Application{owner},V.receipt(request),"result",V.result(request),history,observation => result_class(n,initial,schema,H.observed(S.Datum{observation}),S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.receipt(request),"result"},S.Reading{observation}})))

def operation_boolean(ok: Bool,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,H.operation_match(ok,owner,V.receipt(request),V.result(request)),schema,initial,history)):
  match ok:
    case True{}: result_read(fuel,initial,schema,owner,request,history)
    case False{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"request conflict"})

def operation_class(value: H.Lookup,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,H.operation_value(owner,V.receipt(request),V.operation(),V.result(request),value),schema,initial,history)):
  match value:
    case H.StoredText{actual}: operation_boolean(String.eq(actual,V.operation()),fuel,initial,schema,owner,request,history)
    case H.Missing{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid receipt"})
    case H.Unexpected{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid receipt"})

def operation_read(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,S.Access{D.ReadCell{D.Application{owner},V.receipt(request),"operation"},H.operation_seen(owner,V.receipt(request),V.operation(),V.result(request))},schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.cell_read(n,initial,initial,schema,D.Application{owner},V.receipt(request),"operation",H.operation_seen(owner,V.receipt(request),V.operation(),V.result(request)),history,observation => operation_class(H.observed(S.Datum{observation}),n,initial,schema,owner,request,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.receipt(request),"operation"},S.Reading{observation}})))

def input_boolean(ok: Bool,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,H.input_match(ok,owner,V.receipt(request),V.operation(),V.result(request)),schema,initial,history)):
  match ok:
    case True{}: operation_read(fuel,initial,schema,owner,request,history)
    case False{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"request conflict"})

def input_class(value: H.Lookup,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+input: String,+cancel: Bool,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,H.input_value(owner,V.receipt(request),V.operation(),V.canonical(input,cancel),V.create(owner,request,input,cancel),V.result(request),value),schema,initial,history)):
  match value:
    case H.Missing{}: Writes.actual_create_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,input,cancel,history)
    case H.StoredText{actual}: input_boolean(String.eq(actual,V.canonical(input,cancel)),fuel,initial,schema,owner,request,history)
    case H.Unexpected{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid receipt"})

law actual_issue_command_has_a_derived_success_effect_for_every_fuel_schema_and_state:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.command(owner,V.Issue{request,input,cancel}),schema,initial,history))
def actual_issue_command_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,input,cancel,history):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.cell_read(n,initial,initial,schema,D.Application{owner},V.receipt(request),"input",H.input_seen(owner,V.receipt(request),V.operation(),V.canonical(input,cancel),V.create(owner,request,input,cancel),V.result(request)),history,observation => input_class(H.observed(S.Datum{observation}),n,initial,schema,owner,request,input,cancel,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.receipt(request),"input"},S.Reading{observation}})))

law actual_inspection_has_a_derived_identity_success_effect_for_every_fuel_schema_and_state:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +owner: String
  for +request: String
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.command(owner,V.Inspect{request}),schema,initial,history))
def actual_inspection_has_a_derived_identity_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,history):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.cell_read(n,initial,initial,schema,D.Application{owner},V.voucher(request),"input",V.inspected,history,observation => Step.identity_finish(n,initial,schema,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.voucher(request),"input"},S.Reading{observation}}),V.inspected_value(S.Datum{observation})))
