# ALL-FUEL actual write-path success effects. Every primitive shape is derived
# by Steps/RowShape from actual input DATA. Partial/error/refusal executions are
# NOT mislabeled successful; zero fuel and all intermediate prefixes are covered.
import Base
import ./VoucherSuccessEffects.bend as E
import ../../../library/MutationStateShapeProofs.bend as Shape
import ./VoucherExecutionSteps.bend as Step
import ../../../library/CollectionChangeCompositionProofs.bend as Compose
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ./VoucherLifetimeState.bend as State
import ./VoucherLifetimeRetire.bend as Retire
import ./VoucherLifetimePermission.bend as Gate
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../src/Termination.bend as T

def voucher_transform(+owner: String,+request: String,input: String) -> Shape.Transform:
  Shape.RowUpsert{V.voucher(request),V.fields(owner,V.voucher(request),input,V.operation(),V.voucher(request))}
def receipt_transform(+owner: String,+request: String,input: String,cancel: Bool) -> Shape.Transform:
  Shape.RowUpsert{V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request))}
def first_rows(owner: String,request: String,input: String,old: List<&2,D.Row>) -> List<&2,D.Row>:
  D.insert_row(old,P.voucher_row(owner,request,input))
def first_state(+owner: String,request: String,input: String,initial: D.State,old: List<&2,D.Row>) -> D.State:
  D.swap_collection(D.Application{owner},initial,first_rows(owner,request,input,old))
def receipt_action(+owner: String,+request: String,+input: String,+cancel: Bool) -> S.Action:
  H.put(owner,V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request)),V.finish(cancel,V.voucher(request)))

def after_second(+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+input: String,cancel: Bool,+old: List<&2,D.Row>,+observed: List<&2,D.Row>,+next: D.State,+old_found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},observed_view: {D.rows_collection(D.Application{owner},first_state(owner,request,input,initial,old)) == Some{observed} : Maybe<&2,List<&2,D.Row>>},same: {next == D.swap_collection(D.Application{owner},first_state(owner,request,input,initial,old),Shape.apply(receipt_transform(owner,request,input,cancel),observed)) : D.State},+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,V.finish(cancel,V.voucher(request)),schema,next,history)):
  match cancel:
    case True{}: Step.refusal(fuel,initial,next,schema,history,D.VText{"cancelled"})
    case False{}: Step.changed_finish(fuel,initial,next,schema,history,D.VText{V.voucher(request)},E.TableTransformed{State.PairCreated{request,input},owner,old},old_found,Compose.two_changes(D.Application{owner},initial,old,first_rows(owner,request,input,old),observed,receipt_transform(owner,request,input,False{}),next,old_found,observed_view,same))

def second(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+input: String,+cancel: Bool,+old: List<&2,D.Row>,+old_found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,receipt_action(owner,request,input,cancel),schema,first_state(owner,request,input,initial,old),history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.row_write(n,initial,first_state(owner,request,input,initial,old),schema,D.Application{owner},receipt_transform(owner,request,input,cancel),H.written(V.finish(cancel,V.voucher(request))),history,next => observed => observed_view => same => after_second(n,initial,schema,owner,request,input,cancel,old,observed,next,old_found,observed_view,same,S.append(history,S.OperationEvent{Shape.operation(D.Application{owner},receipt_transform(owner,request,input,cancel)),S.Write{}})))

def after_first(+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+input: String,+cancel: Bool,+old: List<&2,D.Row>,+next: D.State,+found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},same: {next == first_state(owner,request,input,initial,old) : D.State},+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,receipt_action(owner,request,input,cancel),schema,next,history)):
  %Equal.sym(D.State,next,first_state(owner,request,input,initial,old),same) : E.Success(initial,T.observe(fuel,receipt_action(owner,request,input,cancel),schema,_,history))
  second(fuel,initial,schema,owner,request,input,cancel,old,found,history)

law actual_create_has_a_derived_success_effect_for_every_fuel_schema_and_state:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.create(owner,request,input,cancel),schema,initial,history))
def actual_create_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,input,cancel,history):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.row_write(n,initial,initial,schema,D.Application{owner},voucher_transform(owner,request,input),H.written(receipt_action(owner,request,input,cancel)),history,next => old => found => same => after_first(n,initial,schema,owner,request,input,cancel,old,next,found,same,S.append(history,S.OperationEvent{Shape.operation(D.Application{owner},voucher_transform(owner,request,input)),S.Write{}})))

def retire_first_rows(request: String,old: List<&2,D.Row>) -> List<&2,D.Row>: D.remove_row(old,V.receipt(request))
def retire_first_state(+owner: String,request: String,initial: D.State,old: List<&2,D.Row>) -> D.State:
  D.swap_collection(D.Application{owner},initial,retire_first_rows(request,old))
def retire_second_action(+owner: String,request: String) -> S.Action:
  S.Access{D.RemoveRow{D.Application{owner},V.voucher(request)},H.written(S.Finish{D.VText{"retired"}})}

def retire_after_second(+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+old: List<&2,D.Row>,+observed: List<&2,D.Row>,+next: D.State,+old_found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},observed_view: {D.rows_collection(D.Application{owner},retire_first_state(owner,request,initial,old)) == Some{observed} : Maybe<&2,List<&2,D.Row>>},same: {next == D.swap_collection(D.Application{owner},retire_first_state(owner,request,initial,old),D.remove_row(observed,V.voucher(request))) : D.State},+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,S.Finish{D.VText{"retired"}},schema,next,history)):
  Step.changed_finish(fuel,initial,next,schema,history,D.VText{"retired"},E.TableTransformed{State.PairRetired{request},owner,old},old_found,Compose.two_changes(D.Application{owner},initial,old,retire_first_rows(request,old),observed,Shape.RowDelete{V.voucher(request)},next,old_found,observed_view,same))

def retire_second(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+old: List<&2,D.Row>,+old_found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,retire_second_action(owner,request),schema,retire_first_state(owner,request,initial,old),history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.row_write(n,initial,retire_first_state(owner,request,initial,old),schema,D.Application{owner},Shape.RowDelete{V.voucher(request)},H.written(S.Finish{D.VText{"retired"}}),history,next => observed => observed_view => same => retire_after_second(n,initial,schema,owner,request,old,observed,next,old_found,observed_view,same,S.append(history,S.OperationEvent{D.RemoveRow{D.Application{owner},V.voucher(request)},S.Write{}})))

def retire_after_first(+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+old: List<&2,D.Row>,+next: D.State,+found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},same: {next == retire_first_state(owner,request,initial,old) : D.State},+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,retire_second_action(owner,request),schema,next,history)):
  %Equal.sym(D.State,next,retire_first_state(owner,request,initial,old),same) : E.Success(initial,T.observe(fuel,retire_second_action(owner,request),schema,_,history))
  retire_second(fuel,initial,schema,owner,request,old,found,history)

law actual_retirement_has_a_derived_success_effect_for_every_fuel_schema_and_state:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +owner: String
  for +request: String
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.command(owner,V.Retire{request}),schema,initial,history))
def actual_retirement_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,history):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.row_write(n,initial,initial,schema,D.Application{owner},Shape.RowDelete{V.receipt(request)},H.written(retire_second_action(owner,request)),history,next => old => found => same => retire_after_first(n,initial,schema,owner,request,old,next,found,same,S.append(history,S.OperationEvent{D.RemoveRow{D.Application{owner},V.receipt(request)},S.Write{}})))

def fields(row: D.Row) -> List<&2,D.Field>:
  match row:
    case D.Row{key,fields}: fields
def gate_transform(owner: String,enabled: Bool) -> Shape.Transform:
  Shape.RowUpsert{"permission",fields(Gate.row(owner,enabled))}

law actual_permission_update_has_a_derived_success_effect_for_every_fuel_schema_and_state:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +owner: String
  for +enabled: Bool
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.command(owner,V.Permission{enabled}),schema,initial,history))
def actual_permission_update_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,enabled,history):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.row_write(n,initial,initial,schema,D.Application{owner},gate_transform(owner,enabled),H.written(S.Finish{D.VText{"permission updated"}}),history,next => old => found => same => Step.changed_finish(n,initial,next,schema,S.append(history,S.OperationEvent{Shape.operation(D.Application{owner},gate_transform(owner,enabled)),S.Write{}}),D.VText{"permission updated"},E.TableTransformed{State.GateUpdated{enabled},owner,old},found,same))
