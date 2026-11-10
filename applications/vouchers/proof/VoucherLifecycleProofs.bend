# Complete valid-input retirement and permission effects, supplementing the
# all-input/all-fuel success classification. No operation success is assumed.
import Base
import ./VoucherWriteEffects.bend as W
import ../../../library/MutationStateShapeProofs.bend as Shape
import ../Voucher.bend as V
import ./VoucherLifetimeRetire.bend as Retire
import ./VoucherLifetimePermission.bend as Gate
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../library/MutationPrimitiveProofs.bend as Primitive
import ../../../library/MutationWriteTrace.bend as Write
import ../../../library/CollectionFrameProofs.bend as Frame
import ../../../library/CollectionSwapProofs.bend as Swap
import ../../../src/Termination.bend as T

def retired_state(+owner: String,request: String,initial: D.State,old: List<&2,D.Row>) -> D.State:
  D.swap_collection(D.Application{owner},initial,Retire.rows(request,old))
def retirement_events(+owner: String,+request: String,history: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  S.append(S.append(history,S.OperationEvent{D.RemoveRow{D.Application{owner},V.receipt(request)},S.Write{}}),S.OperationEvent{D.RemoveRow{D.Application{owner},V.voucher(request)},S.Write{}})

# ACTUAL COMPLETE RETIREMENT

law actual_valid_retirement_removes_both_rows_in_order_then_finishes:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +request: String
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +remaining: Nat
  for +history: List<&2,S.OperationEvent>
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  {T.observe(3n+remaining,V.command(owner,V.Retire{request}),schema,initial,history) == T.observe(1n+remaining,S.Finish{D.VText{"retired"}},schema,retired_state(owner,request,initial,old),retirement_events(owner,request,history)) : S.Trace}
def actual_valid_retirement_removes_both_rows_in_order_then_finishes(schema,initial,owner,request,table,old,remaining,history,valid_request,schema_found,rows_found):
  Equal.trans(S.Trace,T.observe(3n+remaining,V.command(owner,V.Retire{request}),schema,initial,history),T.observe(2n+remaining,W.retire_second_action(owner,request),schema,W.retire_first_state(owner,request,initial,old),S.append(history,S.OperationEvent{D.RemoveRow{D.Application{owner},V.receipt(request)},S.Write{}})),T.observe(1n+remaining,S.Finish{D.VText{"retired"}},schema,retired_state(owner,request,initial,old),retirement_events(owner,request,history)),Write.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(2n+remaining,schema,initial,W.retire_first_state(owner,request,initial,old),D.RemoveRow{D.Application{owner},V.receipt(request)},H.written(W.retire_second_action(owner,request)),history,Primitive.removing_a_valid_address_in_an_existing_collection_performs_exact_removal(schema,initial,D.Application{owner},table,old,V.receipt(request),valid_request,schema_found,rows_found)),Equal.trans(S.Trace,T.observe(2n+remaining,W.retire_second_action(owner,request),schema,W.retire_first_state(owner,request,initial,old),S.append(history,S.OperationEvent{D.RemoveRow{D.Application{owner},V.receipt(request)},S.Write{}})),T.observe(1n+remaining,S.Finish{D.VText{"retired"}},schema,D.swap_collection(D.Application{owner},W.retire_first_state(owner,request,initial,old),Retire.rows(request,old)),retirement_events(owner,request,history)),T.observe(1n+remaining,S.Finish{D.VText{"retired"}},schema,retired_state(owner,request,initial,old),retirement_events(owner,request,history)),Write.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(1n+remaining,schema,W.retire_first_state(owner,request,initial,old),D.swap_collection(D.Application{owner},W.retire_first_state(owner,request,initial,old),Retire.rows(request,old)),D.RemoveRow{D.Application{owner},V.voucher(request)},H.written(S.Finish{D.VText{"retired"}}),S.append(history,S.OperationEvent{D.RemoveRow{D.Application{owner},V.receipt(request)},S.Write{}}),Primitive.removing_a_valid_address_in_an_existing_collection_performs_exact_removal(schema,W.retire_first_state(owner,request,initial,old),D.Application{owner},table,W.retire_first_rows(request,old),V.voucher(request),valid_request,schema_found,Frame.replacing_an_existing_collection_has_the_exact_new_row_view(D.Application{owner},initial,old,W.retire_first_rows(request,old),rows_found))),Equal.cong(D.State,S.Trace,w => T.observe(1n+remaining,S.Finish{D.VText{"retired"}},schema,w,retirement_events(owner,request,history)),D.swap_collection(D.Application{owner},W.retire_first_state(owner,request,initial,old),Retire.rows(request,old)),retired_state(owner,request,initial,old),Swap.last_collection_replacement_overrides_every_prior_replacement(D.Application{owner},initial,W.retire_first_rows(request,old),Retire.rows(request,old)))))

law actual_valid_permission_change_upserts_only_the_exact_gate_row_then_finishes:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +enabled: Bool
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +remaining: Nat
  for +history: List<&2,S.OperationEvent>
  for schema_found: {D.schema_collection(D.Application{owner},schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(D.Application{owner},initial) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for valid: {D.row_is_valid(table,Gate.row(owner,enabled)) == True{} : Bool}
  {T.observe(2n+remaining,V.command(owner,V.Permission{enabled}),schema,initial,history) == T.observe(1n+remaining,S.Finish{D.VText{"permission updated"}},schema,D.swap_collection(D.Application{owner},initial,D.insert_row(old,Gate.row(owner,enabled))),S.append(history,S.OperationEvent{Shape.operation(D.Application{owner},W.gate_transform(owner,enabled)),S.Write{}})) : S.Trace}
def actual_valid_permission_change_upserts_only_the_exact_gate_row_then_finishes(schema,initial,owner,enabled,table,old,remaining,history,schema_found,rows_found,valid):
  Write.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(1n+remaining,schema,initial,D.swap_collection(D.Application{owner},initial,D.insert_row(old,Gate.row(owner,enabled))),Shape.operation(D.Application{owner},W.gate_transform(owner,enabled)),H.written(S.Finish{D.VText{"permission updated"}}),history,Primitive.defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert(schema,initial,D.Application{owner},table,old,"permission",W.fields(Gate.row(owner,enabled)),schema_found,rows_found,valid))
