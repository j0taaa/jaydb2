# Exact EXISTING configuration-law-list shape. Ownership and the frozen receipt
# rule are separate conjuncts. This proof is generic over the ownership rule and
# environment VALUE, so it requires no development Environment.identity stub.
# RL.State is existential reachability, not observed network/input history.
# The real Configuration.config is a definitional instance, checked separately
# by the actual flat-package integration; this module does not invent a config.
import Base
import ./VoucherLifetimeProofs.bend as Replay
import ./VoucherConflictProofs.bend as Conflict
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ../Initial.bend as Initial
import ./VoucherLifetimeState.bend as State
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../contract/Logic.bend as L
import ../../../library/ReceiptLaws.bend as RL

def installed(ownership: S.Situation -> Type,+schema: D.Schema,+limits: S.Limits,environment: String) -> S.Configuration:
  S.Configuration{schema,S.MoreOneLaw{ownership,S.MoreOneLaw{RL.Rule(~V.program(),~Initial.origin,schema,limits),S.NoneLaw{}}},limits,environment}

law stable_validity_of_the_installed_receipt_configuration_contains_its_exact_replay_state_witness:
  for -ownership: S.Situation -> Type
  for +schema: D.Schema
  for +limits: S.Limits
  for +environment: String
  for +current: D.State
  for valid: R.Valid(installed(ownership,schema,limits,environment),current)
  RL.State(~V.program(),~Initial.origin,schema,limits,current)
def stable_validity_of_the_installed_receipt_configuration_contains_its_exact_replay_state_witness(ownership,schema,limits,environment,current,valid):
  match valid:
    case L.Both{structure,L.Both{owners,L.Both{history,Unit{}}}}: history

law stable_validity_of_the_installed_receipt_configuration_implies_complete_global_lifetime:
  for -ownership: S.Situation -> Type
  for +schema: D.Schema
  for +limits: S.Limits
  for +environment: String
  for +current: D.State
  for valid: R.Valid(installed(ownership,schema,limits,environment),current)
  State.Global(current)
def stable_validity_of_the_installed_receipt_configuration_implies_complete_global_lifetime(ownership,schema,limits,environment,current,valid):
  Replay.the_unchanged_administrator_replay_state_law_implies_the_independent_global_lifetime_invariant(schema,limits,current,stable_validity_of_the_installed_receipt_configuration_contains_its_exact_replay_state_witness(ownership,schema,limits,environment,current,valid))

# This is a logical consequence of the EXISTING final certificate contract,
# not a proof that an arbitrary submitted program has such a certificate.
law an_installed_successful_final_certificate_implies_complete_published_lifetime:
  for -ownership: S.Situation -> Type
  for +schema: D.Schema
  for +limits: S.Limits
  for +environment: String
  for +initial: D.State
  for +context: D.Context
  for +code: String
  for +arguments: D.Value
  for +working: D.State
  for +events: List<&2,S.OperationEvent>
  for +value: D.Value
  for safe: R.SafetyFinal(installed(ownership,schema,limits,environment),initial,context,code,arguments,working,events,S.Response{S.Success{},value})
  State.Global(working)
def an_installed_successful_final_certificate_implies_complete_published_lifetime(ownership,schema,limits,environment,initial,context,code,arguments,working,events,value,safe):
  match safe:
    case L.Both{closed,publication}: stable_validity_of_the_installed_receipt_configuration_implies_complete_global_lifetime(ownership,schema,limits,environment,working,publication)

law an_installed_closed_success_contains_a_completed_same_input_reference_witness:
  for -ownership: S.Situation -> Type
  for +schema: D.Schema
  for +limits: S.Limits
  for +environment: String
  for +initial: D.State
  for +context: D.Context
  for +code: String
  for +arguments: D.Value
  for +working: D.State
  for +events: List<&2,S.OperationEvent>
  for +value: D.Value
  for laws: S.Satisfies(installed(ownership,schema,limits,environment),S.Closed{initial,context,code,arguments,working,events,S.Response{S.Success{},value}})
  RL.Closed(~V.program(),schema,limits,initial,context,arguments,working,events,S.Response{S.Success{},value})
def an_installed_closed_success_contains_a_completed_same_input_reference_witness(ownership,schema,limits,environment,initial,context,code,arguments,working,events,value,laws):
  match laws:
    case L.Both{owners,L.Both{RL.Both{initial_state,closed},Unit{}}}: closed

# INSTALLED CERTIFICATE LIVE-CONFLICT BOUNDARY

law no_separately_supplied_final_success_certificate_can_authorize_a_live_input_or_cancel_conflict:
  for -ownership: S.Situation -> Type
  for +environment: String
  for +code: String
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +kind: String
  for +request: String
  for +saved: String
  for +requested: String
  for +cancel: Bool
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column: D.Column
  for +limits: S.Limits
  for +working: D.State
  for +events: List<&2,S.OperationEvent>
  for +value: D.Value
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +column_found: {D.find_column(columns,"input") == Some{input_column} : Maybe<&2,D.Column>}
  for +row_found: {D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,saved,False{})} : Maybe<&2,D.Row>}
  for different: L.E<{saved == requested : String},{False{} == cancel : Bool}> -> Empty
  for safe: R.SafetyFinal(installed(ownership,schema,limits,environment),initial,D.Context{owner,kind},code,Conflict.arguments(request,requested,cancel),working,events,S.Response{S.Success{},value})
  Empty
def no_separately_supplied_final_success_certificate_can_authorize_a_live_input_or_cancel_conflict(ownership,environment,code,schema,initial,owner,kind,request,saved,requested,cancel,table_name,primary,columns,rows,input_column,limits,working,events,value,valid_request,schema_found,rows_found,column_found,row_found,different,safe):
  match safe:
    case L.Both{closed_laws,publication}: Conflict.no_closed_frozen_reference_success_witness_exists_for_a_live_conflicting_issue(schema,initial,owner,kind,request,saved,requested,cancel,table_name,primary,columns,rows,input_column,limits,working,events,value,valid_request,schema_found,rows_found,column_found,row_found,different,an_installed_closed_success_contains_a_completed_same_input_reference_witness(ownership,schema,limits,environment,initial,D.Context{owner,kind},code,Conflict.arguments(request,requested,cancel),working,events,value,closed_laws))
