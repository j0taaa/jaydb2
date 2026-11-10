# Actual command source: receipt absence -> read then both real writes;
# the exact resulting receipt -> an identical repeat with three reads and NO
# second business/receipt write. No completed first execution is assumed.
# This is command-level behavior; dispatch permission and publication are separate.
import Base
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ../../../library/RowLookupProofs.bend as Row
import ../../../library/ReceiptLookupProofs.bend as Binding
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../library/CollectionFrameProofs.bend as Frame
import ../../../library/MutationPrimitiveProofs.bend as Primitive
import ../../../library/QueryReadTrace.bend as History
import ../../../src/Termination.bend as T

def first_history(owner: String,request: String,history: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  S.append(history,Binding.event(owner,V.receipt(request),"input",D.RowAbsent{}))

law actual_issue_command_on_an_absent_receipt_has_one_read_then_the_complete_pair_creation:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +old: List<&2,D.Row>
  for +input_column_value: D.Column
  for +remaining: Nat
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for row_absent: {D.find_row(old,V.receipt(request)) == None{} : Maybe<&2,D.Row>}
  for voucher_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.voucher_row(owner,request,input)) == True{} : Bool}
  for +receipt_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,cancel)) == True{} : Bool}
  {T.observe(4n+remaining,V.command(owner,V.Issue{request,input,cancel}),schema,before,history) == T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,P.state(owner,before,old,request,input,cancel),P.events(owner,request,input,cancel,first_history(owner,request,history))) : S.Trace}
def actual_issue_command_on_an_absent_receipt_has_one_read_then_the_complete_pair_creation(schema,before,owner,request,input,cancel,table_name,primary,columns,old,input_column_value,remaining,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid):
  Equal.trans(S.Trace,T.observe(4n+remaining,V.command(owner,V.Issue{request,input,cancel}),schema,before,history),T.observe(3n+remaining,V.create(owner,request,input,cancel),schema,before,first_history(owner,request,history)),T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,P.state(owner,before,old,request,input,cancel),P.events(owner,request,input,cancel,first_history(owner,request,history))),Binding.an_absent_input_receipt_hands_off_after_its_only_input_read(schema,before,owner,V.receipt(request),table_name,primary,columns,old,input_column_value,V.operation(),V.canonical(input,cancel),1n+remaining,V.create(owner,request,input,cancel),V.result(request),history,Primitive.valid_row_has_a_valid_unicode_address(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,cancel),receipt_valid),schema_found,rows_found,row_absent,input_column),P.actual_frozen_create_has_exact_two_write_evolving_state_history_and_finish(schema,before,owner,request,input,cancel,D.SchemaTable{table_name,primary,columns},old,remaining,first_history(owner,request,history),schema_found,rows_found,voucher_valid,receipt_valid))

law actual_fresh_issue_command_derives_both_corresponding_rows_without_an_output_premise:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +old: List<&2,D.Row>
  for +input_column_value: D.Column
  for +remaining: Nat
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for row_absent: {D.find_row(old,V.receipt(request)) == None{} : Maybe<&2,D.Row>}
  for voucher_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.voucher_row(owner,request,input)) == True{} : Bool}
  for +receipt_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,cancel)) == True{} : Bool}
  L.E<{T.observe(4n+remaining,V.command(owner,V.Issue{request,input,cancel}),schema,before,history) == T.observe(1n+remaining,V.finish(cancel,V.voucher(request)),schema,P.state(owner,before,old,request,input,cancel),P.events(owner,request,input,cancel,first_history(owner,request,history))) : S.Trace},P.PairState(owner,request,input,cancel,P.state(owner,before,old,request,input,cancel))>
def actual_fresh_issue_command_derives_both_corresponding_rows_without_an_output_premise(schema,before,owner,request,input,cancel,table_name,primary,columns,old,input_column_value,remaining,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid):
  L.Both{actual_issue_command_on_an_absent_receipt_has_one_read_then_the_complete_pair_creation(schema,before,owner,request,input,cancel,table_name,primary,columns,old,input_column_value,remaining,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid),P.the_computed_replacement_state_contains_both_exact_corresponding_rows(owner,before,old,request,input,cancel,rows_found)}

law an_identical_repeat_on_the_derived_pair_state_returns_the_result_without_another_write:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +request: String
  for +input: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +old: List<&2,D.Row>
  for +input_column_value: D.Column
  for +operation_column_value: D.Column
  for +result_column_value: D.Column
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for operation_column: {D.find_column(columns,"operation") == Some{operation_column_value} : Maybe<&2,D.Column>}
  for result_column: {D.find_column(columns,"result") == Some{result_column_value} : Maybe<&2,D.Column>}
  for receipt_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,False{})) == True{} : Bool}
  {T.observe(4n,V.command(owner,V.Issue{request,input,False{}}),schema,P.state(owner,before,old,request,input,False{}),history) == S.Final{P.state(owner,before,old,request,input,False{}),History.append_events(Binding.hit_events(owner,V.receipt(request),V.canonical(input,False{}),V.operation(),D.VText{V.voucher(request)}),history),S.Response{S.Success{},D.VText{V.voucher(request)}}} : S.Trace}
def an_identical_repeat_on_the_derived_pair_state_returns_the_result_without_another_write(schema,before,owner,request,input,table_name,primary,columns,old,input_column_value,operation_column_value,result_column_value,history,schema_found,rows_found,input_column,operation_column,result_column,receipt_valid):
  Binding.matching_input_and_operation_return_exactly_the_original_result_after_three_reads(schema,P.state(owner,before,old,request,input,False{}),owner,V.receipt(request),table_name,primary,columns,P.rows(owner,request,input,False{},old),V.fields(owner,V.receipt(request),V.canonical(input,False{}),V.operation(),V.voucher(request)),input_column_value,operation_column_value,result_column_value,V.operation(),V.canonical(input,False{}),D.VText{V.voucher(request)},1n,V.create(owner,request,input,False{}),V.result(request),history,Primitive.valid_row_has_a_valid_unicode_address(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,False{}),receipt_valid),schema_found,Frame.replacing_an_existing_collection_has_the_exact_new_row_view(D.Application{owner},before,old,P.rows(owner,request,input,False{},old),rows_found),Row.an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(D.insert_row(old,P.voucher_row(owner,request,input)),P.receipt_row(owner,request,input,False{})),input_column,operation_column,result_column,{==},{==},{==})
