# Complete actual command/permission/length/argument dispatch. All fuel values,
# schemas, states, contexts and arguments are covered; no gate/length/decoder
# correctness flag or completed action is assumed at a public boundary.
import Base
import ./VoucherSuccessEffects.bend as E
import ./VoucherExecutionSteps.bend as Step
import ./VoucherWriteEffects.bend as Writes
import ./VoucherReadEffects.bend as Reads
import ../Voucher.bend as V
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Termination.bend as T

def command(+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,command: V.Command,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,V.command(owner,command),schema,initial,history)):
  match command:
    case V.Issue{request,input,cancel}: Reads.actual_issue_command_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,input,cancel,history)
    case V.Retire{request}: Writes.actual_retirement_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,history)
    case V.Inspect{request}: Reads.actual_inspection_has_a_derived_identity_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,request,history)
    case V.Permission{enabled}: Writes.actual_permission_update_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,enabled,history)
    case V.Invalid{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid request"})

def permitted(ok: Bool,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+requested: V.Command,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,V.permit(ok,owner,requested),schema,initial,history)):
  match ok:
    case True{}: command(fuel,initial,schema,owner,requested,history)
    case False{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"permission denied"})

def gate(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+requested: V.Command,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,S.Access{D.ReadCell{D.Application{owner},"permission","enabled"},V.permitted(owner,requested)},schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: Step.cell_read(n,initial,initial,schema,D.Application{owner},"permission","enabled",V.permitted(owner,requested),history,observation => permitted(V.enabled(S.Datum{observation}),n,initial,schema,owner,requested,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{observation}})))

def sized(allowed: Bool,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+input: String,+cancel: Bool,+history: List<&2,S.OperationEvent>) -> E.Success(initial,T.observe(fuel,V.sized(allowed,owner,request,input,cancel),schema,initial,history)):
  match allowed:
    case True{}: gate(fuel,initial,schema,owner,V.Issue{request,input,cancel},history)
    case False{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"request ID too long"})

law actual_dispatch_derives_its_complete_success_effect_for_every_input:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +owner: String
  for requested: V.Command
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.dispatch(owner,requested),schema,initial,history))
def actual_dispatch_derives_its_complete_success_effect_for_every_input(fuel,initial,schema,owner,requested,history):
  match requested:
    case V.Issue{+request,input,cancel}: sized(Nat.is_le(String.length(request),64n),fuel,initial,schema,owner,request,input,cancel,history)
    case V.Retire{request}: gate(fuel,initial,schema,owner,V.Retire{request},history)
    case V.Inspect{request}: gate(fuel,initial,schema,owner,V.Inspect{request},history)
    case V.Permission{enabled}: Writes.actual_permission_update_has_a_derived_success_effect_for_every_fuel_schema_and_state(fuel,initial,schema,owner,enabled,history)
    case V.Invalid{}: Step.refusal(fuel,initial,initial,schema,history,D.VText{"invalid request"})

law actual_start_derives_its_complete_success_effect_for_every_context_and_argument:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for context: D.Context
  for +arguments: D.Value
  for +history: List<&2,S.OperationEvent>
  E.Success(initial,T.observe(fuel,V.start(context,arguments),schema,initial,history))
def actual_start_derives_its_complete_success_effect_for_every_context_and_argument(fuel,initial,schema,context,arguments,history):
  match context:
    case D.Context{owner,kind}: actual_dispatch_derives_its_complete_success_effect_for_every_input(fuel,initial,schema,owner,V.analyze(arguments),history)

law observing_with_empty_history_is_the_ordinary_program_observation:
  for fuel: Nat
  for -action: S.Action
  for -schema: D.Schema
  for -initial: D.State
  {T.observe(fuel,action,schema,initial,Nil{}) == S.observe(fuel,action,schema,initial) : S.Trace}
def observing_with_empty_history_is_the_ordinary_program_observation(fuel,action,schema,initial):
  match fuel:
    case 0n: {==}
    case 1n+n: {==}

law actual_frozen_reference_execution_derives_a_complete_success_effect_for_every_input_and_fuel:
  for +fuel: Nat
  for +initial: D.State
  for +schema: D.Schema
  for +context: D.Context
  for +arguments: D.Value
  E.Success(initial,S.execute(fuel,V.program(),schema,initial,context,arguments))
def actual_frozen_reference_execution_derives_a_complete_success_effect_for_every_input_and_fuel(fuel,initial,schema,context,arguments):
  %observing_with_empty_history_is_the_ordinary_program_observation(fuel,V.start(context,arguments),schema,initial) : E.Success(initial,_)
  actual_start_derives_its_complete_success_effect_for_every_context_and_argument(fuel,initial,schema,context,arguments,Nil{})
