# Independent absence of a key in every original row, then actual named
# primitive observations derived from INPUT schema and table contents.
import Base
import ./IndexEntryProofs.bend as Entry
import ../contract/Data.bend as D
import ./ValueScalarProofs.bend as Pair

def Absent(+key: String,rows: List<&2,D.Row>) -> Data:
  match rows:
    case Nil{}: Unit
    case Con{head,tail}: Pair.Both<{String.eq(D.row_key(head),key) == False{} : Bool},Absent(key,tail)>

law a_key_excluded_from_every_input_row_has_no_actual_lookup_match:
  for +rows: List<&2,D.Row>
  for +key: String
  for absent: Absent(key,rows)
  {D.find_row(rows,key) == None{} : Maybe<&2,D.Row>}
def a_key_excluded_from_every_input_row_has_no_actual_lookup_match(rows,key,absent):
  match rows absent:
    case Nil{} Unit{}: {==}
    case Con{D.Row{+head,+fields},+tail} Pair.Both{different,rest}:
      Equal.trans(Maybe<&2,D.Row>,D.find_row(Con{D.Row{head,fields},tail},key),D.find_row(tail,key),None{},Equal.cong(Bool,Maybe<&2,D.Row>,equal => Bool.pick(Maybe<&2,D.Row>,equal,Some{D.Row{head,fields}},D.find_row(tail,key)),String.eq(head,key),False{},different),a_key_excluded_from_every_input_row_has_no_actual_lookup_match(tail,key,rest))

law input_schema_and_table_views_determine_the_actual_existence_observation:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +key: String
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  {D.operate(schema,state,D.ViewExistence{collection,key}) == D.Observed{D.Existence{D.exists_row(D.find_row(rows,key))}} : D.ResultOp}
def input_schema_and_table_views_determine_the_actual_existence_observation(schema,state,collection,table,rows,key,address,schema_found,rows_found):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,D.ViewExistence{collection,key}) == D.Observed{D.Existence{D.exists_row(D.find_row(rows,key))}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{table},schema_found) : {D.operate_resolved(D.ViewExistence{collection,key},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Observed{D.Existence{D.exists_row(D.find_row(rows,key))}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.ViewExistence{collection,key},D.resolve_parts(Some{table},_),state) == D.Observed{D.Existence{D.exists_row(D.find_row(rows,key))}} : D.ResultOp}
  {==}

law a_key_excluded_from_every_input_row_has_exact_absent_existence:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +key: String
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for absent: Absent(key,rows)
  {D.operate(schema,state,D.ViewExistence{collection,key}) == D.Observed{D.Existence{False{}}} : D.ResultOp}
def a_key_excluded_from_every_input_row_has_exact_absent_existence(schema,state,collection,table,rows,key,address,schema_found,rows_found,absent):
  Equal.trans(D.ResultOp,D.operate(schema,state,D.ViewExistence{collection,key}),D.Observed{D.Existence{D.exists_row(D.find_row(rows,key))}},D.Observed{D.Existence{False{}}},input_schema_and_table_views_determine_the_actual_existence_observation(schema,state,collection,table,rows,key,address,schema_found,rows_found),Equal.cong(Maybe<&2,D.Row>,D.ResultOp,found => D.Observed{D.Existence{D.exists_row(found)}},D.find_row(rows,key),None{},a_key_excluded_from_every_input_row_has_no_actual_lookup_match(rows,key,absent)))

law a_present_input_row_has_exact_occupied_existence:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +key: String
  for +row: D.Row
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for found: {D.find_row(rows,key) == Some{row} : Maybe<&2,D.Row>}
  {D.operate(schema,state,D.ViewExistence{collection,key}) == D.Observed{D.Existence{True{}}} : D.ResultOp}
def a_present_input_row_has_exact_occupied_existence(schema,state,collection,table,rows,key,row,address,schema_found,rows_found,found):
  Equal.trans(D.ResultOp,D.operate(schema,state,D.ViewExistence{collection,key}),D.Observed{D.Existence{D.exists_row(D.find_row(rows,key))}},D.Observed{D.Existence{True{}}},input_schema_and_table_views_determine_the_actual_existence_observation(schema,state,collection,table,rows,key,address,schema_found,rows_found),Equal.cong(Maybe<&2,D.Row>,D.ResultOp,result => D.Observed{D.Existence{D.exists_row(result)}},D.find_row(rows,key),Some{row},found))

law an_excluded_input_key_has_exact_row_absence_for_the_declared_target_cell:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +rows: List<&2,D.Row>
  for +key: String
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for absent: Absent(key,rows)
  {D.operate(schema,state,D.ReadCell{collection,key,"target"}) == D.Observed{D.RowAbsent{}} : D.ResultOp}
def an_excluded_input_key_has_exact_row_absence_for_the_declared_target_cell(schema,state,collection,table_name,rows,key,address,schema_found,rows_found,absent):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,D.ReadCell{collection,key,"target"}) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{Entry.schema(table_name)},schema_found) : {D.operate_resolved(D.ReadCell{collection,key,"target"},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.ReadCell{collection,key,"target"},D.resolve_parts(Some{Entry.schema(table_name)},_),state) == D.Observed{D.RowAbsent{}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows,key),None{},a_key_excluded_from_every_input_row_has_no_actual_lookup_match(rows,key,absent)) : {D.read_row(_,"target") == D.Observed{D.RowAbsent{}} : D.ResultOp}
  {==}
