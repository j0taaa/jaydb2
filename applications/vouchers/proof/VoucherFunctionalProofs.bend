# Actual fresh command completion and the existing finalization/publication
# boundary, with NO assumed successful primitive/final response/publication.
# Cancellation performs the real working writes and unconditionally rolls back.
import Base
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ./VoucherIssueProofs.bend as Issue
import ./VoucherPublicationProofs.bend as Publication
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../contract/Logic.bend as L
import ../../../library/MutationPublicationProofs.bend as Boundary
import ../../../src/Termination.bend as T

law actual_fresh_success_path_keeps_initial_or_publishes_the_complete_corresponding_pair:
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
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for row_absent: {D.find_row(old,V.receipt(request)) == None{} : Maybe<&2,D.Row>}
  for voucher_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.voucher_row(owner,request,input)) == True{} : Bool}
  for +receipt_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,False{})) == True{} : Bool}
  for configuration: S.Configuration
  L.E<{T.observe(4n+0n,V.command(owner,V.Issue{request,input,False{}}),schema,before,history) == T.observe(1n+0n,V.finish(False{},V.voucher(request)),schema,P.state(owner,before,old,request,input,False{}),P.events(owner,request,input,False{},Issue.first_history(owner,request,history))) : S.Trace},Publication.Correct(owner,request,input,False{},before,P.state(owner,before,old,request,input,False{}),R.finalize(S.Response{S.Success{},D.VText{V.voucher(request)}},configuration,P.state(owner,before,old,request,input,False{})))>
def actual_fresh_success_path_keeps_initial_or_publishes_the_complete_corresponding_pair(schema,before,owner,request,input,table_name,primary,columns,old,input_column_value,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid,configuration):
  L.Both{Issue.actual_issue_command_on_an_absent_receipt_has_one_read_then_the_complete_pair_creation(schema,before,owner,request,input,False{},table_name,primary,columns,old,input_column_value,0n,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid),Publication.technical_finalization_keeps_initial_or_publishes_the_complete_computed_pair(configuration,owner,request,input,False{},before,old,S.Response{S.Success{},D.VText{V.voucher(request)}},rows_found)}

law actual_fresh_cancellation_performs_both_working_writes_and_rolls_back_every_publication:
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
  for +history: List<&2,S.OperationEvent>
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for row_absent: {D.find_row(old,V.receipt(request)) == None{} : Maybe<&2,D.Row>}
  for voucher_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.voucher_row(owner,request,input)) == True{} : Bool}
  for +receipt_valid: {D.row_is_valid(D.SchemaTable{table_name,primary,columns},P.receipt_row(owner,request,input,True{})) == True{} : Bool}
  for configuration: S.Configuration
  L.E<{T.observe(4n+0n,V.command(owner,V.Issue{request,input,True{}}),schema,before,history) == T.observe(1n+0n,V.finish(True{},V.voucher(request)),schema,P.state(owner,before,old,request,input,True{}),P.events(owner,request,input,True{},Issue.first_history(owner,request,history))) : S.Trace},{S.publish(R.finalize(S.Response{S.Refusal{},D.VText{"cancelled"}},configuration,P.state(owner,before,old,request,input,True{})),before,P.state(owner,before,old,request,input,True{})) == before : D.State}>
def actual_fresh_cancellation_performs_both_working_writes_and_rolls_back_every_publication(schema,before,owner,request,input,table_name,primary,columns,old,input_column_value,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid,configuration):
  L.Both{Issue.actual_issue_command_on_an_absent_receipt_has_one_read_then_the_complete_pair_creation(schema,before,owner,request,input,True{},table_name,primary,columns,old,input_column_value,0n,history,schema_found,rows_found,input_column,row_absent,voucher_valid,receipt_valid),Boundary.actual_refusal_finalization_cannot_publish_earlier_working_writes(configuration,D.VText{"cancelled"},before,P.state(owner,before,old,request,input,True{}))}
