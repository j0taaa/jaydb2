# Source/schema INPUT facts imply actual named-cell observations. A row/field
# lookup here is an ordinary property of the initial table; no primitive
# operation outcome or completed Receipt action is an input hypothesis.
import Base
import ./ReceiptReadPlan.bend as M
import ../contract/Data.bend as D
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

law a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +fields: List<&2,D.Field>
  for +name: String
  for +column: D.Column
  for +value: D.Value
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(D.Application{owner},state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for column_found: {D.find_column(columns,name) == Some{column} : Maybe<&2,D.Column>}
  for row_found: {D.find_row(rows,key) == Some{D.Row{key,fields}} : Maybe<&2,D.Row>}
  for field_found: {D.find_field(fields,name) == Some{value} : Maybe<&2,D.Value>}
  {D.operate(schema,state,M.read(owner,key,name)) == D.Observed{D.Cell{value}} : D.ResultOp}
def a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,state,owner,key,table_name,primary,columns,rows,fields,name,column,value,address,schema_found,rows_found,column_found,row_found,field_found):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,M.read(owner,key,name)) == D.Observed{D.Cell{value}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(D.Application{owner},schema),Some{D.SchemaTable{table_name,primary,columns}},schema_found) : {D.operate_resolved(M.read(owner,key,name),D.resolve_parts(_,D.rows_collection(D.Application{owner},state)),state) == D.Observed{D.Cell{value}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(D.Application{owner},state),Some{rows},rows_found) : {D.operate_resolved(M.read(owner,key,name),D.resolve_parts(Some{D.SchemaTable{table_name,primary,columns}},_),state) == D.Observed{D.Cell{value}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Column>,D.find_column(columns,name),Some{column},column_found) : {D.read_column(_,D.find_row(rows,key),name) == D.Observed{D.Cell{value}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows,key),Some{D.Row{key,fields}},row_found) : {D.read_row(_,name) == D.Observed{D.Cell{value}} : D.ResultOp}
  Equal.cong(Maybe<&2,D.Value>,D.ResultOp,D.result_cell,D.find_field(fields,name),Some{value},field_found)

law an_absent_input_receipt_row_yields_row_absence_when_the_column_is_declared:
  for +schema: D.Schema
  for +state: D.State
  for +owner: String
  for +key: String
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +name: String
  for +column: D.Column
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(D.Application{owner},state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for column_found: {D.find_column(columns,name) == Some{column} : Maybe<&2,D.Column>}
  for row_absent: {D.find_row(rows,key) == None{} : Maybe<&2,D.Row>}
  {D.operate(schema,state,M.read(owner,key,name)) == D.Observed{D.RowAbsent{}} : D.ResultOp}
def an_absent_input_receipt_row_yields_row_absence_when_the_column_is_declared(schema,state,owner,key,table_name,primary,columns,rows,name,column,address,schema_found,rows_found,column_found,row_absent):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,M.read(owner,key,name)) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(D.Application{owner},schema),Some{D.SchemaTable{table_name,primary,columns}},schema_found) : {D.operate_resolved(M.read(owner,key,name),D.resolve_parts(_,D.rows_collection(D.Application{owner},state)),state) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(D.Application{owner},state),Some{rows},rows_found) : {D.operate_resolved(M.read(owner,key,name),D.resolve_parts(Some{D.SchemaTable{table_name,primary,columns}},_),state) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Column>,D.find_column(columns,name),Some{column},column_found) : {D.read_column(_,D.find_row(rows,key),name) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows,key),None{},row_absent) : {D.read_row(_,name) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  {==}

def unequal_case(equal: Bool,+actual: String,+expected: String,same: {String.eq(actual,expected) == equal : Bool},different: {actual == expected : String} -> Empty) -> {String.eq(actual,expected) == False{} : Bool}:
  match equal:
    case False{}: same
    case True{}: Empty.absurd({String.eq(actual,expected) == False{} : Bool},different(O.string_equal(actual,expected,same)))

law different_literal_texts_have_a_false_string_equality_comparison:
  for +actual: String
  for +expected: String
  for different: {actual == expected : String} -> Empty
  {String.eq(actual,expected) == False{} : Bool}
def different_literal_texts_have_a_false_string_equality_comparison(actual,expected,different): unequal_case(String.eq(actual,expected),actual,expected,{==},different)
