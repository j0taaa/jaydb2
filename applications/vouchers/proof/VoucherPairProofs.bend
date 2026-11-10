# Actual frozen create executes BOTH complete ordinary writes before finishing
# or cancelling. Correspondence is a result derived from valid input rows,
# never an assumed final invariant or assumed successful operation output.
import Base
import ../Voucher.bend as V
import ../../../library/Receipts.bend as H
import ./VoucherKeyProofs.bend as K
import ../../../library/RowLookupProofs.bend as Row
import ../../../library/ReceiptWriteProofs.bend as Put
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../library/CollectionFrameProofs.bend as Frame
import ../../../library/CollectionSwapProofs.bend as Swap
import ../../../src/Termination.bend as T

def voucher_row(owner: String,+request: String,input: String) -> D.Row:
  D.Row{V.voucher(request),V.fields(owner,V.voucher(request),input,V.operation(),V.voucher(request))}
def receipt_row(owner: String,+request: String,input: String,cancel: Bool) -> D.Row:
  D.Row{V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request))}
def rows(+owner: String,+request: String,+input: String,cancel: Bool,before: List<&2,D.Row>) -> List<&2,D.Row>:
  D.insert_row(D.insert_row(before,voucher_row(owner,request,input)),receipt_row(owner,request,input,cancel))
def state(+owner: String,before: D.State,old: List<&2,D.Row>,request: String,input: String,cancel: Bool) -> D.State:
  D.swap_collection(D.Application{owner},before,rows(owner,request,input,cancel,old))
def voucher_op(+owner: String,+request: String,input: String) -> D.Operation:
  D.DefineRow{D.Application{owner},V.voucher(request),V.fields(owner,V.voucher(request),input,V.operation(),V.voucher(request))}
def receipt_op(+owner: String,+request: String,input: String,cancel: Bool) -> D.Operation:
  D.DefineRow{D.Application{owner},V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request))}
def events(+owner: String,+request: String,+input: String,cancel: Bool,history: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  S.append(S.append(history,S.OperationEvent{voucher_op(owner,request,input),S.Write{}}),S.OperationEvent{receipt_op(owner,request,input,cancel),S.Write{}})

def PairRows(+owner: String,+request: String,+input: String,cancel: Bool,+rows: List<&2,D.Row>) -> Type:
  L.E<{D.find_row(rows,V.voucher(request)) == Some{voucher_row(owner,request,input)} : Maybe<&2,D.Row>},{D.find_row(rows,V.receipt(request)) == Some{receipt_row(owner,request,input,cancel)} : Maybe<&2,D.Row>}>
def PairView(+owner: String,+request: String,+input: String,cancel: Bool,view: Maybe<&2,List<&2,D.Row>>) -> Type:
  match view:
    case None{}: Empty
    case Some{rows}: PairRows(owner,request,input,cancel,rows)
def PairState(+owner: String,request: String,input: String,cancel: Bool,state: D.State) -> Type:
  PairView(owner,request,input,cancel,D.rows_collection(D.Application{owner},state))

law the_two_actual_upserts_create_both_exact_corresponding_rows_for_all_input_row_lists:
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +before: List<&2,D.Row>
  PairRows(owner,request,input,cancel,rows(owner,request,input,cancel,before))
def the_two_actual_upserts_create_both_exact_corresponding_rows_for_all_input_row_lists(owner,request,input,cancel,before):
  L.Both{Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(owner,request,input,cancel,before),V.voucher(request)),D.find_row(D.insert_row(before,voucher_row(owner,request,input)),V.voucher(request)),Some{voucher_row(owner,request,input)},Row.an_actual_upsert_preserves_every_other_exact_key_lookup(D.insert_row(before,voucher_row(owner,request,input)),receipt_row(owner,request,input,cancel),V.voucher(request),K.actual_receipt_and_voucher_key_spaces_are_disjoint(request,request)),Row.an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(before,voucher_row(owner,request,input))),Row.an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(D.insert_row(before,voucher_row(owner,request,input)),receipt_row(owner,request,input,cancel))}

law the_computed_replacement_state_contains_both_exact_corresponding_rows:
  for +owner: String
  for +before: D.State
  for +old: List<&2,D.Row>
  for +request: String
  for +input: String
  for +cancel: Bool
  for found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  PairState(owner,request,input,cancel,state(owner,before,old,request,input,cancel))
def the_computed_replacement_state_contains_both_exact_corresponding_rows(owner,before,old,request,input,cancel,found):
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(D.Application{owner},state(owner,before,old,request,input,cancel)),Some{rows(owner,request,input,cancel,old)},Frame.replacing_an_existing_collection_has_the_exact_new_row_view(D.Application{owner},before,old,rows(owner,request,input,cancel,old),found)) : PairView(owner,request,input,cancel,_)
  the_two_actual_upserts_create_both_exact_corresponding_rows_for_all_input_row_lists(owner,request,input,cancel,old)

# ACTUAL CREATE EXECUTION

law actual_frozen_create_has_exact_two_write_evolving_state_history_and_finish:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +remaining: Nat
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for voucher_valid: {D.row_is_valid(table,voucher_row(owner,request,input)) == True{} : Bool}
  for receipt_valid: {D.row_is_valid(table,receipt_row(owner,request,input,cancel)) == True{} : Bool}
  {T.observe(3n+remaining,V.create(owner,request,input,cancel),schema,before,history) == T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,state(owner,before,old,request,input,cancel),events(owner,request,input,cancel,history)) : S.Trace}
def actual_frozen_create_has_exact_two_write_evolving_state_history_and_finish(schema,before,owner,request,input,cancel,table,old,remaining,history,schema_found,rows_found,voucher_valid,receipt_valid):
  Equal.trans(S.Trace,T.observe(3n+remaining,V.create(owner,request,input,cancel),schema,before,history),T.observe(2n+remaining,H.put(owner,V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request)),V.finish(cancel,V.voucher(request))),schema,D.swap_collection(D.Application{owner},before,D.insert_row(old,voucher_row(owner,request,input))),S.append(history,S.OperationEvent{voucher_op(owner,request,input),S.Write{}})),T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,state(owner,before,old,request,input,cancel),events(owner,request,input,cancel,history)),Put.an_actual_valid_receipt_put_upserts_the_complete_input_row_then_hands_off(schema,before,owner,V.voucher(request),V.fields(owner,V.voucher(request),input,V.operation(),V.voucher(request)),table,old,1n+remaining,H.put(owner,V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request)),V.finish(cancel,V.voucher(request))),history,schema_found,rows_found,voucher_valid),Equal.trans(S.Trace,T.observe(2n+remaining,H.put(owner,V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request)),V.finish(cancel,V.voucher(request))),schema,D.swap_collection(D.Application{owner},before,D.insert_row(old,voucher_row(owner,request,input))),S.append(history,S.OperationEvent{voucher_op(owner,request,input),S.Write{}})),T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,D.swap_collection(D.Application{owner},D.swap_collection(D.Application{owner},before,D.insert_row(old,voucher_row(owner,request,input))),rows(owner,request,input,cancel,old)),events(owner,request,input,cancel,history)),T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,state(owner,before,old,request,input,cancel),events(owner,request,input,cancel,history)),Put.an_actual_valid_receipt_put_upserts_the_complete_input_row_then_hands_off(schema,D.swap_collection(D.Application{owner},before,D.insert_row(old,voucher_row(owner,request,input))),owner,V.receipt(request),V.fields(owner,V.receipt(request),V.canonical(input,cancel),V.operation(),V.voucher(request)),table,D.insert_row(old,voucher_row(owner,request,input)),remaining,V.finish(cancel,V.voucher(request)),S.append(history,S.OperationEvent{voucher_op(owner,request,input),S.Write{}}),schema_found,Frame.replacing_an_existing_collection_has_the_exact_new_row_view(D.Application{owner},before,old,D.insert_row(old,voucher_row(owner,request,input)),rows_found),receipt_valid),Equal.cong(D.State,S.Trace,w => T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,w,events(owner,request,input,cancel,history)),D.swap_collection(D.Application{owner},D.swap_collection(D.Application{owner},before,D.insert_row(old,voucher_row(owner,request,input))),rows(owner,request,input,cancel,old)),state(owner,before,old,request,input,cancel),Swap.last_collection_replacement_overrides_every_prior_replacement(D.Application{owner},before,D.insert_row(old,voucher_row(owner,request,input)),rows(owner,request,input,cancel,old)))))

law actual_frozen_create_derives_its_corresponding_business_and_receipt_rows:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +table: D.SchemaTable
  for +old: List<&2,D.Row>
  for +remaining: Nat
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for voucher_valid: {D.row_is_valid(table,voucher_row(owner,request,input)) == True{} : Bool}
  for receipt_valid: {D.row_is_valid(table,receipt_row(owner,request,input,cancel)) == True{} : Bool}
  L.E<{T.observe(3n+remaining,V.create(owner,request,input,cancel),schema,before,history) == T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,state(owner,before,old,request,input,cancel),events(owner,request,input,cancel,history)) : S.Trace},PairState(owner,request,input,cancel,state(owner,before,old,request,input,cancel))>
def actual_frozen_create_derives_its_corresponding_business_and_receipt_rows(schema,before,owner,request,input,cancel,table,old,remaining,history,schema_found,rows_found,voucher_valid,receipt_valid):
  L.Both{actual_frozen_create_has_exact_two_write_evolving_state_history_and_finish(schema,before,owner,request,input,cancel,table,old,remaining,history,schema_found,rows_found,voucher_valid,receipt_valid),the_computed_replacement_state_contains_both_exact_corresponding_rows(owner,before,old,request,input,cancel,rows_found)}
