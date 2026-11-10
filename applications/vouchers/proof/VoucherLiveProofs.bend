# Exact functional meaning of a LIVE receipt instance. These input row facts
# are constructively available from Instances + the unchanged replay law;
# they do not infer global consistency from a successful lookup.
import Base
import ./VoucherWriteEffects.bend as Writes
import ./VoucherLifetimePermission.bend as Gate
import ../../../library/ReceiptInputProofs.bend as Input
import ../../../library/Proofs.bend as Event
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ./VoucherKeyProofs.bend as K
import ../../../library/ReceiptLookupProofs.bend as Binding
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../library/QueryReadTrace.bend as History
import ../../../src/Termination.bend as T

law an_identical_live_issue_returns_the_original_result_without_any_business_or_receipt_write:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +request: String
  for +saved_input: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column_value: D.Column
  for +operation_column_value: D.Column
  for +result_column_value: D.Column
  for +history: List<&2,S.OperationEvent>
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for receipt_found: {D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,saved_input,False{})} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for operation_column: {D.find_column(columns,"operation") == Some{operation_column_value} : Maybe<&2,D.Column>}
  for result_column: {D.find_column(columns,"result") == Some{result_column_value} : Maybe<&2,D.Column>}
  {T.observe(4n,V.command(owner,V.Issue{request,saved_input,False{}}),schema,initial,history) == S.Final{initial,History.append_events(Binding.hit_events(owner,V.receipt(request),V.canonical(saved_input,False{}),V.operation(),D.VText{V.voucher(request)}),history),S.Response{S.Success{},D.VText{V.voucher(request)}}} : S.Trace}
def an_identical_live_issue_returns_the_original_result_without_any_business_or_receipt_write(schema,initial,owner,request,saved_input,table_name,primary,columns,rows,input_column_value,operation_column_value,result_column_value,history,valid_request,schema_found,rows_found,receipt_found,input_column,operation_column,result_column):
  Binding.matching_input_and_operation_return_exactly_the_original_result_after_three_reads(schema,initial,owner,V.receipt(request),table_name,primary,columns,rows,V.fields(owner,V.receipt(request),V.canonical(saved_input,False{}),V.operation(),V.voucher(request)),input_column_value,operation_column_value,result_column_value,V.operation(),V.canonical(saved_input,False{}),D.VText{V.voucher(request)},1n,V.create(owner,request,saved_input,False{}),V.result(request),history,valid_request,schema_found,rows_found,receipt_found,input_column,operation_column,result_column,{==},{==},{==})

law any_different_live_input_or_cancel_flag_refuses_before_operation_result_or_business_access:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +request: String
  for +saved_input: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column_value: D.Column
  for +requested_input: String
  for +requested_cancel: Bool
  for +history: List<&2,S.OperationEvent>
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for receipt_found: {D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,saved_input,False{})} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for different: L.E<{saved_input == requested_input : String},{False{} == requested_cancel : Bool}> -> Empty
  {T.observe(4n,V.command(owner,V.Issue{request,requested_input,requested_cancel}),schema,initial,history) == S.Final{initial,S.append(history,Binding.event(owner,V.receipt(request),"input",D.Cell{D.VText{V.canonical(saved_input,False{})}})),S.Response{S.Refusal{},D.VText{"request conflict"}}} : S.Trace}
def any_different_live_input_or_cancel_flag_refuses_before_operation_result_or_business_access(schema,initial,owner,request,saved_input,table_name,primary,columns,rows,input_column_value,requested_input,requested_cancel,history,valid_request,schema_found,rows_found,receipt_found,input_column,different):
  Binding.a_different_original_input_refuses_before_any_operation_or_result_read(schema,initial,owner,V.receipt(request),table_name,primary,columns,rows,V.fields(owner,V.receipt(request),V.canonical(saved_input,False{}),V.operation(),V.voucher(request)),input_column_value,V.operation(),V.canonical(requested_input,requested_cancel),V.canonical(saved_input,False{}),1n,V.create(owner,request,requested_input,requested_cancel),V.result(request),history,valid_request,schema_found,rows_found,receipt_found,input_column,{==},same => different(K.actual_canonical_input_is_injective_in_both_text_and_cancellation_flag(saved_input,False{},requested_input,requested_cancel,same)))

# CURRENT PERMISSION FUNCTIONAL BINDING

def actual_gate(+schema: D.Schema,+initial: D.State,+owner: String,+table_name: String,+primary: String,+columns: List<&2,D.Column>,+rows: List<&2,D.Row>,+enabled_column_value: D.Column,+enabled: Bool,schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>},rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>},enabled_column: {D.find_column(columns,"enabled") == Some{enabled_column_value} : Maybe<&2,D.Column>},gate_found: {D.find_row(rows,"permission") == Some{Gate.row(owner,enabled)} : Maybe<&2,D.Row>}) -> {D.operate(schema,initial,D.ReadCell{D.Application{owner},"permission","enabled"}) == D.Observed{D.Cell{D.VBool{enabled}}} : D.ResultOp}:
  Input.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,initial,owner,"permission",table_name,primary,columns,rows,Writes.fields(Gate.row(owner,enabled)),"enabled",enabled_column_value,D.VBool{enabled},{==},schema_found,rows_found,enabled_column,gate_found,{==})

law an_identical_live_dispatch_rechecks_current_permission_then_reads_the_complete_receipt_without_writes:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +request: String
  for +saved_input: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column_value: D.Column
  for +operation_column_value: D.Column
  for +result_column_value: D.Column
  for +history: List<&2,S.OperationEvent>
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for receipt_found: {D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,saved_input,False{})} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for operation_column: {D.find_column(columns,"operation") == Some{operation_column_value} : Maybe<&2,D.Column>}
  for result_column: {D.find_column(columns,"result") == Some{result_column_value} : Maybe<&2,D.Column>}
  for +enabled_column_value: D.Column
  for enabled_column: {D.find_column(columns,"enabled") == Some{enabled_column_value} : Maybe<&2,D.Column>}
  for gate_found: {D.find_row(rows,"permission") == Some{Gate.row(owner,True{})} : Maybe<&2,D.Row>}
  for admitted_length: {Nat.is_le(String.length(request),64n) == True{} : Bool}
  {T.observe(5n,V.dispatch(owner,V.Issue{request,saved_input,False{}}),schema,initial,history) == S.Final{initial,History.append_events(Binding.hit_events(owner,V.receipt(request),V.canonical(saved_input,False{}),V.operation(),D.VText{V.voucher(request)}),S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{True{}}}}})),S.Response{S.Success{},D.VText{V.voucher(request)}}} : S.Trace}
def an_identical_live_dispatch_rechecks_current_permission_then_reads_the_complete_receipt_without_writes(schema,initial,owner,request,saved_input,table_name,primary,columns,rows,input_column_value,operation_column_value,result_column_value,history,valid_request,schema_found,rows_found,receipt_found,input_column,operation_column,result_column,enabled_column_value,enabled_column,gate_found,admitted_length):
  %Equal.sym(Bool,Nat.is_le(String.length(request),64n),True{},admitted_length) : {T.observe(5n,V.sized(_,owner,request,saved_input,False{}),schema,initial,history) == S.Final{initial,History.append_events(Binding.hit_events(owner,V.receipt(request),V.canonical(saved_input,False{}),V.operation(),D.VText{V.voucher(request)}),S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{True{}}}}})),S.Response{S.Success{},D.VText{V.voucher(request)}}} : S.Trace}
  Equal.trans(S.Trace,T.observe(5n,V.sized(True{},owner,request,saved_input,False{}),schema,initial,history),T.observe(4n,V.command(owner,V.Issue{request,saved_input,False{}}),schema,initial,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{True{}}}}})),S.Final{initial,History.append_events(Binding.hit_events(owner,V.receipt(request),V.canonical(saved_input,False{}),V.operation(),D.VText{V.voucher(request)}),S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{True{}}}}})),S.Response{S.Success{},D.VText{V.voucher(request)}}},Event.read_continuation(4n,schema,initial,D.ReadCell{D.Application{owner},"permission","enabled"},D.Cell{D.VBool{True{}}},V.permitted(owner,V.Issue{request,saved_input,False{}}),history,actual_gate(schema,initial,owner,table_name,primary,columns,rows,enabled_column_value,True{},schema_found,rows_found,enabled_column,gate_found)),an_identical_live_issue_returns_the_original_result_without_any_business_or_receipt_write(schema,initial,owner,request,saved_input,table_name,primary,columns,rows,input_column_value,operation_column_value,result_column_value,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{True{}}}}}),valid_request,schema_found,rows_found,receipt_found,input_column,operation_column,result_column))

law a_disabled_current_permission_refuses_before_any_receipt_or_business_access:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +request: String
  for +input: String
  for +cancel: Bool
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +enabled_column_value: D.Column
  for +history: List<&2,S.OperationEvent>
  for schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for enabled_column: {D.find_column(columns,"enabled") == Some{enabled_column_value} : Maybe<&2,D.Column>}
  for gate_found: {D.find_row(rows,"permission") == Some{Gate.row(owner,False{})} : Maybe<&2,D.Row>}
  for admitted_length: {Nat.is_le(String.length(request),64n) == True{} : Bool}
  {T.observe(2n,V.dispatch(owner,V.Issue{request,input,cancel}),schema,initial,history) == S.Final{initial,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{False{}}}}}),S.Response{S.Refusal{},D.VText{"permission denied"}}} : S.Trace}
def a_disabled_current_permission_refuses_before_any_receipt_or_business_access(schema,initial,owner,request,input,cancel,table_name,primary,columns,rows,enabled_column_value,history,schema_found,rows_found,enabled_column,gate_found,admitted_length):
  %Equal.sym(Bool,Nat.is_le(String.length(request),64n),True{},admitted_length) : {T.observe(2n,V.sized(_,owner,request,input,cancel),schema,initial,history) == S.Final{initial,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{D.Cell{D.VBool{False{}}}}}),S.Response{S.Refusal{},D.VText{"permission denied"}}} : S.Trace}
  Event.read_continuation(1n,schema,initial,D.ReadCell{D.Application{owner},"permission","enabled"},D.Cell{D.VBool{False{}}},V.permitted(owner,V.Issue{request,input,cancel}),history,actual_gate(schema,initial,owner,table_name,primary,columns,rows,enabled_column_value,False{},schema_found,rows_found,enabled_column,gate_found))
