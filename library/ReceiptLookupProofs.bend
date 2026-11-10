# Source-content corollaries of the TOTAL engine proof. Public heads use only
# initial table/schema/field facts and literal data inequalities. Private
# proof-assembly helpers consume the primitive observations derived below.
import Base
import ./ReceiptReadPlan.bend as M
import ./ReceiptReadProofs.bend as R
import ./ReceiptInputProofs.bend as V
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Receipts.bend as H
import ./QueryReadTrace.bend as History
import ../proof/Orders.bend as O
import ../src/Termination.bend as T

def event(owner: String,key: String,name: String,value: D.Observation) -> S.OperationEvent: S.OperationEvent{M.read(owner,key,name),S.Reading{value}}
def hit_events(+owner: String,+key: String,input: String,operation: String,value: D.Value) -> List<&2,S.OperationEvent>:
  [event(owner,key,"input",D.Cell{D.VText{input}}),event(owner,key,"operation",D.Cell{D.VText{operation}}),event(owner,key,"result",D.Cell{value})]

def from_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,+remaining: Nat,-missing: S.Action,-done: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,+expected: M.Plan,exact: {M.plan(schema,state,owner,key,operation,input) == expected : M.Plan}) -> {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == R.finish(expected,remaining,schema,state,missing,done,history) : S.Trace}:
  Equal.trans(S.Trace,T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history),R.finish(M.plan(schema,state,owner,key,operation,input),remaining,schema,state,missing,done,history),R.finish(expected,remaining,schema,state,missing,done,history),R.actual_bound_has_total_exact_source_state_history_short_circuit_and_callback_behavior(schema,state,owner,key,operation,input,remaining,missing,done,history),Equal.cong(M.Plan,S.Trace,p => R.finish(p,remaining,schema,state,missing,done,history),M.plan(schema,state,owner,key,operation,input),expected,exact))

def hit_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,+value: D.Value,input_read: {D.operate(schema,state,M.read(owner,key,"input")) == D.Observed{D.Cell{D.VText{input}}} : D.ResultOp},operation_read: {D.operate(schema,state,M.read(owner,key,"operation")) == D.Observed{D.Cell{D.VText{operation}}} : D.ResultOp},result_read: {D.operate(schema,state,M.read(owner,key,"result")) == D.Observed{D.Cell{value}} : D.ResultOp}) -> {M.plan(schema,state,owner,key,operation,input) == M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)} : M.Plan}:
  %Equal.sym(D.ResultOp,D.operate(schema,state,M.read(owner,key,"input")),D.Observed{D.Cell{D.VText{input}}},input_read) : {M.input(owner,key,input,_,M.operation_plan(schema,state,owner,key,operation)) == M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)} : M.Plan}
  %Equal.sym(Bool,String.eq(input,input),True{},O.string_eq_refl(input)) : {M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),Bool.pick(M.Plan,_,M.operation_plan(schema,state,owner,key,operation),M.ReceiptRefused{D.VText{"request conflict"},Nil{}})) == M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)} : M.Plan}
  %Equal.sym(D.ResultOp,D.operate(schema,state,M.read(owner,key,"operation")),D.Observed{D.Cell{D.VText{operation}}},operation_read) : {M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),M.operation(owner,key,operation,_,M.result_plan(schema,state,owner,key))) == M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)} : M.Plan}
  %Equal.sym(Bool,String.eq(operation,operation),True{},O.string_eq_refl(operation)) : {M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),M.prepend(event(owner,key,"operation",D.Cell{D.VText{operation}}),Bool.pick(M.Plan,_,M.result_plan(schema,state,owner,key),M.ReceiptRefused{D.VText{"request conflict"},Nil{}}))) == M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)} : M.Plan}
  %Equal.sym(D.ResultOp,D.operate(schema,state,M.read(owner,key,"result")),D.Observed{D.Cell{value}},result_read) : {M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),M.prepend(event(owner,key,"operation",D.Cell{D.VText{operation}}),M.result(owner,key,_))) == M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)} : M.Plan}
  {==}

def missing_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,input_read: {D.operate(schema,state,M.read(owner,key,"input")) == D.Observed{D.RowAbsent{}} : D.ResultOp}) -> {M.plan(schema,state,owner,key,operation,input) == M.ReceiptMissing{[event(owner,key,"input",D.RowAbsent{})]} : M.Plan}:
  Equal.cong(D.ResultOp,M.Plan,r => M.input(owner,key,input,r,M.operation_plan(schema,state,owner,key,operation)),D.operate(schema,state,M.read(owner,key,"input")),D.Observed{D.RowAbsent{}},input_read)

def input_conflict_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,+stored: String,input_read: {D.operate(schema,state,M.read(owner,key,"input")) == D.Observed{D.Cell{D.VText{stored}}} : D.ResultOp},different: {String.eq(stored,input) == False{} : Bool}) -> {M.plan(schema,state,owner,key,operation,input) == M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{stored}})]} : M.Plan}:
  %Equal.sym(D.ResultOp,D.operate(schema,state,M.read(owner,key,"input")),D.Observed{D.Cell{D.VText{stored}}},input_read) : {M.input(owner,key,input,_,M.operation_plan(schema,state,owner,key,operation)) == M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{stored}})]} : M.Plan}
  Equal.cong(Bool,M.Plan,b => M.prepend(event(owner,key,"input",D.Cell{D.VText{stored}}),Bool.pick(M.Plan,b,M.operation_plan(schema,state,owner,key,operation),M.ReceiptRefused{D.VText{"request conflict"},Nil{}})),String.eq(stored,input),False{},different)

def operation_conflict_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,+operation: String,+input: String,+stored: String,input_read: {D.operate(schema,state,M.read(owner,key,"input")) == D.Observed{D.Cell{D.VText{input}}} : D.ResultOp},operation_read: {D.operate(schema,state,M.read(owner,key,"operation")) == D.Observed{D.Cell{D.VText{stored}}} : D.ResultOp},different: {String.eq(stored,operation) == False{} : Bool}) -> {M.plan(schema,state,owner,key,operation,input) == M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{input}}),event(owner,key,"operation",D.Cell{D.VText{stored}})]} : M.Plan}:
  %Equal.sym(D.ResultOp,D.operate(schema,state,M.read(owner,key,"input")),D.Observed{D.Cell{D.VText{input}}},input_read) : {M.input(owner,key,input,_,M.operation_plan(schema,state,owner,key,operation)) == M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{input}}),event(owner,key,"operation",D.Cell{D.VText{stored}})]} : M.Plan}
  %Equal.sym(Bool,String.eq(input,input),True{},O.string_eq_refl(input)) : {M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),Bool.pick(M.Plan,_,M.operation_plan(schema,state,owner,key,operation),M.ReceiptRefused{D.VText{"request conflict"},Nil{}})) == M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{input}}),event(owner,key,"operation",D.Cell{D.VText{stored}})]} : M.Plan}
  %Equal.sym(D.ResultOp,D.operate(schema,state,M.read(owner,key,"operation")),D.Observed{D.Cell{D.VText{stored}}},operation_read) : {M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),M.operation(owner,key,operation,_,M.result_plan(schema,state,owner,key))) == M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{input}}),event(owner,key,"operation",D.Cell{D.VText{stored}})]} : M.Plan}
  Equal.cong(Bool,M.Plan,b => M.prepend(event(owner,key,"input",D.Cell{D.VText{input}}),M.prepend(event(owner,key,"operation",D.Cell{D.VText{stored}}),Bool.pick(M.Plan,b,M.result_plan(schema,state,owner,key),M.ReceiptRefused{D.VText{"request conflict"},Nil{}}))),String.eq(stored,operation),False{},different)

# PUBLIC SOURCE-CONTENT THEOREMS

law matching_input_and_operation_return_exactly_the_original_result_after_three_reads:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +fields: List<&2,D.Field>
  for +input_column_value: D.Column
  for +operation_column_value: D.Column
  for +result_column_value: D.Column
  for +operation: String
  for +input: String
  for +value: D.Value
  for +remaining: Nat
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  for +address: {D.unicode_valid(key) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +row_found: {D.find_row(rows,key) == Some{D.Row{key,fields}} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for operation_column: {D.find_column(columns,"operation") == Some{operation_column_value} : Maybe<&2,D.Column>}
  for result_column: {D.find_column(columns,"result") == Some{result_column_value} : Maybe<&2,D.Column>}
  for input_field: {D.find_field(fields,"input") == Some{D.VText{input}} : Maybe<&2,D.Value>}
  for operation_field: {D.find_field(fields,"operation") == Some{D.VText{operation}} : Maybe<&2,D.Value>}
  for result_field: {D.find_field(fields,"result") == Some{value} : Maybe<&2,D.Value>}
  {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == T.observe(remaining,done(S.Datum{D.Cell{value}}),schema,state,History.append_events(hit_events(owner,key,input,operation,value),history)) : S.Trace}
def matching_input_and_operation_return_exactly_the_original_result_after_three_reads(schema,state,owner,key,table_name,primary,columns,rows,fields,input_column_value,operation_column_value,result_column_value,operation,input,value,remaining,missing,done,history,address,schema_found,rows_found,row_found,input_column,operation_column,result_column,input_field,operation_field,result_field):
  from_plan(schema,state,owner,key,operation,input,remaining,missing,done,history,M.ReceiptResult{S.Datum{D.Cell{value}},hit_events(owner,key,input,operation,value)},hit_plan(schema,state,owner,key,operation,input,value,V.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,"input",input_column_value,D.VText{input},address,schema_found,rows_found,input_column,row_found,input_field),V.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,"operation",operation_column_value,D.VText{operation},address,schema_found,rows_found,operation_column,row_found,operation_field),V.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,"result",result_column_value,value,address,schema_found,rows_found,result_column,row_found,result_field)))

law an_absent_input_receipt_hands_off_after_its_only_input_read:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column_value: D.Column
  for +operation: String
  for +input: String
  for +remaining: Nat
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  for +address: {D.unicode_valid(key) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +row_absent: {D.find_row(rows,key) == None{} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == T.observe(2n+remaining,missing,schema,state,S.append(history,event(owner,key,"input",D.RowAbsent{}))) : S.Trace}
def an_absent_input_receipt_hands_off_after_its_only_input_read(schema,state,owner,key,table_name,primary,columns,rows,input_column_value,operation,input,remaining,missing,done,history,address,schema_found,rows_found,row_absent,input_column):
  from_plan(schema,state,owner,key,operation,input,remaining,missing,done,history,M.ReceiptMissing{[event(owner,key,"input",D.RowAbsent{})]},missing_plan(schema,state,owner,key,operation,input,V.an_absent_input_receipt_row_yields_row_absence_when_the_column_is_declared(schema,state,owner,key,table_name,primary,columns,rows,"input",input_column_value,address,schema_found,rows_found,input_column,row_absent)))

law a_different_original_input_refuses_before_any_operation_or_result_read:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +fields: List<&2,D.Field>
  for +input_column_value: D.Column
  for +operation: String
  for +input: String
  for +stored: String
  for +remaining: Nat
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  for +address: {D.unicode_valid(key) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +row_found: {D.find_row(rows,key) == Some{D.Row{key,fields}} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for input_field: {D.find_field(fields,"input") == Some{D.VText{stored}} : Maybe<&2,D.Value>}
  for different: {stored == input : String} -> Empty
  {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == S.Final{state,S.append(history,event(owner,key,"input",D.Cell{D.VText{stored}})),S.Response{S.Refusal{},D.VText{"request conflict"}}} : S.Trace}
def a_different_original_input_refuses_before_any_operation_or_result_read(schema,state,owner,key,table_name,primary,columns,rows,fields,input_column_value,operation,input,stored,remaining,missing,done,history,address,schema_found,rows_found,row_found,input_column,input_field,different):
  from_plan(schema,state,owner,key,operation,input,remaining,missing,done,history,M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{stored}})]},input_conflict_plan(schema,state,owner,key,operation,input,stored,V.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,"input",input_column_value,D.VText{stored},address,schema_found,rows_found,input_column,row_found,input_field),V.different_literal_texts_have_a_false_string_equality_comparison(stored,input,different)))

law a_different_original_operation_refuses_after_two_reads_before_any_result_read:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +fields: List<&2,D.Field>
  for +input_column_value: D.Column
  for +operation_column_value: D.Column
  for +operation: String
  for +input: String
  for +stored: String
  for +remaining: Nat
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  for +address: {D.unicode_valid(key) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +row_found: {D.find_row(rows,key) == Some{D.Row{key,fields}} : Maybe<&2,D.Row>}
  for input_column: {D.find_column(columns,"input") == Some{input_column_value} : Maybe<&2,D.Column>}
  for operation_column: {D.find_column(columns,"operation") == Some{operation_column_value} : Maybe<&2,D.Column>}
  for input_field: {D.find_field(fields,"input") == Some{D.VText{input}} : Maybe<&2,D.Value>}
  for operation_field: {D.find_field(fields,"operation") == Some{D.VText{stored}} : Maybe<&2,D.Value>}
  for different: {stored == operation : String} -> Empty
  {T.observe(3n+remaining,H.bound(owner,key,operation,input,missing,done),schema,state,history) == S.Final{state,S.append(S.append(history,event(owner,key,"input",D.Cell{D.VText{input}})),event(owner,key,"operation",D.Cell{D.VText{stored}})),S.Response{S.Refusal{},D.VText{"request conflict"}}} : S.Trace}
def a_different_original_operation_refuses_after_two_reads_before_any_result_read(schema,state,owner,key,table_name,primary,columns,rows,fields,input_column_value,operation_column_value,operation,input,stored,remaining,missing,done,history,address,schema_found,rows_found,row_found,input_column,operation_column,input_field,operation_field,different):
  from_plan(schema,state,owner,key,operation,input,remaining,missing,done,history,M.ReceiptRefused{D.VText{"request conflict"},[event(owner,key,"input",D.Cell{D.VText{input}}),event(owner,key,"operation",D.Cell{D.VText{stored}})]},operation_conflict_plan(schema,state,owner,key,operation,input,stored,V.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,"input",input_column_value,D.VText{input},address,schema_found,rows_found,input_column,row_found,input_field),V.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,"operation",operation_column_value,D.VText{stored},address,schema_found,rows_found,operation_column,row_found,operation_field),V.different_literal_texts_have_a_false_string_equality_comparison(stored,operation,different)))
