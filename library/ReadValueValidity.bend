# Source-state invariants imply real observed cell payload validity. This does
# not assume that an operation succeeds or that a selected result is valid.
import Base
import ../contract/Data.bend as D
import ../proof/Foundations.bend as F

def fields(xs: List<&2,D.Field>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{D.Field{name,value},tail}: D.value_valid(value) && fields(tail)

def rows(xs: List<&2,D.Row>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{D.Row{key,fs},tail}: fields(fs) && rows(tail)

def tables(xs: List<&2,D.Table>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{D.Table{name,rs},tail}: rows(rs) && tables(tail)

def state_values(state: D.State) -> Bool:
  match state:
    case D.State{ts,us}: tables(ts) && rows(us)

def kind_implies_value_valid(+kind: D.ColumnKind,+value: D.Value,valid: {D.value_kind(kind,value) == True{} : Bool}) -> {D.value_valid(value) == True{} : Bool}:
  match kind value:
    case D.TextValue{} D.VAbsent{}: F.absurd_boolean({D.value_valid(D.VAbsent{}) == True{} : Bool},valid)
    case D.TextValue{} D.VBool{b}: F.absurd_boolean({D.value_valid(D.VBool{b}) == True{} : Bool},valid)
    case D.TextValue{} D.VInt{high,low}: F.absurd_boolean({D.value_valid(D.VInt{high,low}) == True{} : Bool},valid)
    case D.TextValue{} D.VText{text}: valid
    case D.TextValue{} D.VListEmpty{}: F.absurd_boolean({D.value_valid(D.VListEmpty{}) == True{} : Bool},valid)
    case D.TextValue{} D.VList{head,tail}: F.absurd_boolean({D.value_valid(D.VList{head,tail}) == True{} : Bool},valid)
    case D.TextValue{} D.VRecordEmpty{}: F.absurd_boolean({D.value_valid(D.VRecordEmpty{}) == True{} : Bool},valid)
    case D.TextValue{} D.VRecord{name,head,tail}: F.absurd_boolean({D.value_valid(D.VRecord{name,head,tail}) == True{} : Bool},valid)
    case D.Boolean{} D.VAbsent{}: F.absurd_boolean({D.value_valid(D.VAbsent{}) == True{} : Bool},valid)
    case D.Boolean{} D.VBool{b}: {==}
    case D.Boolean{} D.VInt{high,low}: F.absurd_boolean({D.value_valid(D.VInt{high,low}) == True{} : Bool},valid)
    case D.Boolean{} D.VText{text}: F.absurd_boolean({D.value_valid(D.VText{text}) == True{} : Bool},valid)
    case D.Boolean{} D.VListEmpty{}: F.absurd_boolean({D.value_valid(D.VListEmpty{}) == True{} : Bool},valid)
    case D.Boolean{} D.VList{head,tail}: F.absurd_boolean({D.value_valid(D.VList{head,tail}) == True{} : Bool},valid)
    case D.Boolean{} D.VRecordEmpty{}: F.absurd_boolean({D.value_valid(D.VRecordEmpty{}) == True{} : Bool},valid)
    case D.Boolean{} D.VRecord{name,head,tail}: F.absurd_boolean({D.value_valid(D.VRecord{name,head,tail}) == True{} : Bool},valid)
    case D.Integer{} D.VAbsent{}: F.absurd_boolean({D.value_valid(D.VAbsent{}) == True{} : Bool},valid)
    case D.Integer{} D.VBool{b}: F.absurd_boolean({D.value_valid(D.VBool{b}) == True{} : Bool},valid)
    case D.Integer{} D.VInt{high,low}: {==}
    case D.Integer{} D.VText{text}: F.absurd_boolean({D.value_valid(D.VText{text}) == True{} : Bool},valid)
    case D.Integer{} D.VListEmpty{}: F.absurd_boolean({D.value_valid(D.VListEmpty{}) == True{} : Bool},valid)
    case D.Integer{} D.VList{head,tail}: F.absurd_boolean({D.value_valid(D.VList{head,tail}) == True{} : Bool},valid)
    case D.Integer{} D.VRecordEmpty{}: F.absurd_boolean({D.value_valid(D.VRecordEmpty{}) == True{} : Bool},valid)
    case D.Integer{} D.VRecord{name,head,tail}: F.absurd_boolean({D.value_valid(D.VRecord{name,head,tail}) == True{} : Bool},valid)

def fit_implies_value_valid(+value: D.Value,+kind: D.ColumnKind,+optional: Bool,valid: {D.fits_column(value,kind,optional) == True{} : Bool}) -> {D.value_valid(value) == True{} : Bool}:
  match value:
    case D.VAbsent{}: {==}
    case D.VText{text}: kind_implies_value_valid(kind,D.VText{text},valid)
    case D.VBool{b}: kind_implies_value_valid(kind,D.VBool{b},valid)
    case D.VInt{high,low}: kind_implies_value_valid(kind,D.VInt{high,low},valid)
    case D.VListEmpty{}: {==}
    case D.VList{head,tail}: kind_implies_value_valid(kind,D.VList{head,tail},valid)
    case D.VRecordEmpty{}: {==}
    case D.VRecord{name,head,tail}: kind_implies_value_valid(kind,D.VRecord{name,head,tail},valid)

def fitting_fields_have_valid_values(+cs: List<&2,D.Column>,+fs: List<&2,D.Field>,+valid: {D.fields_all_valid(cs,fs) == True{} : Bool}) -> {fields(fs) == True{} : Bool}:
  match cs fs:
    case Nil{} Nil{}: {==}
    case Nil{} Con{head,tail}: F.absurd_boolean({fields(Con{head,tail}) == True{} : Bool},valid)
    case Con{head,tail} Nil{}: {==}
    case Con{D.Column{+cn,+ct,+co},+cr} Con{D.Field{+fn,+fv},+fr}:
      F.and_boolean_intro(D.value_valid(fv),fields(fr),fit_implies_value_valid(fv,ct,co,F.and_boolean_right(String.eq(cn,fn),D.fits_column(fv,ct,co),F.and_boolean_left(String.eq(cn,fn) && D.fits_column(fv,ct,co),D.fields_all_valid(cr,fr),valid))),fitting_fields_have_valid_values(cr,fr,F.and_boolean_right(String.eq(cn,fn) && D.fits_column(fv,ct,co),D.fields_all_valid(cr,fr),valid)))

def structured_rows_have_valid_values(+rs: List<&2,D.Row>,+schema: D.SchemaTable,+valid: {D.rows_valid_cases(rs,schema) == True{} : Bool}) -> {rows(rs) == True{} : Bool}:
  match rs schema:
    case Nil{} schema: {==}
    case Con{D.Row{+key,+fs},+tail} D.SchemaTable{+name,+primary,+cs}:
      +row_valid = F.and_boolean_left(D.row_is_valid(D.SchemaTable{name,primary,cs},D.Row{key,fs}),D.rows_later(tail,key),F.and_boolean_left(D.row_is_valid(D.SchemaTable{name,primary,cs},D.Row{key,fs}) && D.rows_later(tail,key),D.rows_valid_cases(tail,D.SchemaTable{name,primary,cs}),valid))
      F.and_boolean_intro(fields(fs),rows(tail),fitting_fields_have_valid_values(cs,fs,F.and_boolean_right(D.unicode_valid(key),D.fields_all_valid(cs,fs),F.and_boolean_left(D.unicode_valid(key) && D.fields_all_valid(cs,fs),D.key_correct(D.find_field(fs,primary),key),row_valid))),structured_rows_have_valid_values(tail,D.SchemaTable{name,primary,cs},F.and_boolean_right(D.row_is_valid(D.SchemaTable{name,primary,cs},D.Row{key,fs}) && D.rows_later(tail,key),D.rows_valid_cases(tail,D.SchemaTable{name,primary,cs}),valid)))

def structured_tables_have_valid_values(+es: List<&2,D.SchemaTable>,+ts: List<&2,D.Table>,+valid: {D.tables_valid_cases(es,ts) == True{} : Bool}) -> {tables(ts) == True{} : Bool}:
  match es ts:
    case Nil{} Nil{}: {==}
    case Nil{} Con{head,tail}: F.absurd_boolean({tables(Con{head,tail}) == True{} : Bool},valid)
    case Con{head,tail} Nil{}: {==}
    case Con{+e,+er} Con{D.Table{+name,+rs},+tr}:
      F.and_boolean_intro(rows(rs),tables(tr),structured_rows_have_valid_values(rs,e,F.and_boolean_right(String.eq(D.schema_name(e),name),D.rows_valid_cases(rs,e),F.and_boolean_left(String.eq(D.schema_name(e),name) && D.rows_valid_cases(rs,e),D.tables_valid_cases(er,tr),valid))),structured_tables_have_valid_values(er,tr,F.and_boolean_right(String.eq(D.schema_name(e),name) && D.rows_valid_cases(rs,e),D.tables_valid_cases(er,tr),valid)))

law actual_structured_state_contains_only_valid_field_payloads:
  for +schema: D.Schema
  for +state: D.State
  for +valid: {D.structure(schema,state) == True{} : Bool}
  {state_values(state) == True{} : Bool}
def actual_structured_state_contains_only_valid_field_payloads(schema,state,valid):
  match schema state:
    case D.Schema{+es} D.State{+ts,+us}:
      +both = F.and_boolean_left(D.tables_valid_cases(es,ts) && D.rows_valid_cases(us,D.schema_users()),D.credentials_valid_cases(us),valid)
      F.and_boolean_intro(tables(ts),rows(us),structured_tables_have_valid_values(es,ts,F.and_boolean_left(D.tables_valid_cases(es,ts),D.rows_valid_cases(us,D.schema_users()),both)),structured_rows_have_valid_values(us,D.schema_users(),F.and_boolean_right(D.tables_valid_cases(es,ts),D.rows_valid_cases(us,D.schema_users()),both)))

def FoundValue(value: Maybe<&2,D.Value>) -> Data:
  match value:
    case None{}: Unit
    case Some{value}: {D.value_valid(value) == True{} : Bool}

def value_choice(choice: Bool,+head: D.Value,+tail: Maybe<&2,D.Value>,head_valid: {D.value_valid(head) == True{} : Bool},tail_valid: FoundValue(tail)) -> FoundValue(Bool.pick(Maybe<&2,D.Value>,choice,Some{head},tail)):
  match choice:
    case True{}: head_valid
    case False{}: tail_valid

def field_lookup_preserves_validity(+fs: List<&2,D.Field>,+name: String,+valid: {fields(fs) == True{} : Bool}) -> FoundValue(D.find_field(fs,name)):
  match fs:
    case Nil{}: Unit{}
    case Con{D.Field{+key,+value},+tail}: value_choice(String.eq(key,name),value,D.find_field(tail,name),F.and_boolean_left(D.value_valid(value),fields(tail),valid),field_lookup_preserves_validity(tail,name,F.and_boolean_right(D.value_valid(value),fields(tail),valid)))

def FoundRow(row: Maybe<&2,D.Row>) -> Data:
  match row:
    case None{}: Unit
    case Some{D.Row{key,fs}}: {fields(fs) == True{} : Bool}

def row_choice(choice: Bool,+head: D.Row,+tail: Maybe<&2,D.Row>,head_valid: FoundRow(Some{head}),tail_valid: FoundRow(tail)) -> FoundRow(Bool.pick(Maybe<&2,D.Row>,choice,Some{head},tail)):
  match choice:
    case True{}: head_valid
    case False{}: tail_valid

def row_lookup_preserves_validity(+rs: List<&2,D.Row>,+key: String,+valid: {rows(rs) == True{} : Bool}) -> FoundRow(D.find_row(rs,key)):
  match rs:
    case Nil{}: Unit{}
    case Con{D.Row{+name,+fs},+tail}: row_choice(String.eq(name,key),D.Row{name,fs},D.find_row(tail,key),F.and_boolean_left(fields(fs),rows(tail),valid),row_lookup_preserves_validity(tail,key,F.and_boolean_right(fields(fs),rows(tail),valid)))

def FoundTable(table: Maybe<&2,D.Table>) -> Data:
  match table:
    case None{}: Unit
    case Some{D.Table{name,rs}}: {rows(rs) == True{} : Bool}

def table_choice(choice: Bool,+head: D.Table,+tail: Maybe<&2,D.Table>,head_valid: FoundTable(Some{head}),tail_valid: FoundTable(tail)) -> FoundTable(Bool.pick(Maybe<&2,D.Table>,choice,Some{head},tail)):
  match choice:
    case True{}: head_valid
    case False{}: tail_valid

def table_lookup_preserves_validity(+ts: List<&2,D.Table>,+name: String,+valid: {tables(ts) == True{} : Bool}) -> FoundTable(D.find_table(ts,name)):
  match ts:
    case Nil{}: Unit{}
    case Con{D.Table{+key,+rs},+tail}: table_choice(String.eq(key,name),D.Table{key,rs},D.find_table(tail,name),F.and_boolean_left(rows(rs),tables(tail),valid),table_lookup_preserves_validity(tail,name,F.and_boolean_right(rows(rs),tables(tail),valid)))

def FoundRows(rs: Maybe<&2,List<&2,D.Row>>) -> Data:
  match rs:
    case None{}: Unit
    case Some{rs}: {rows(rs) == True{} : Bool}

def table_rows_preserve_validity(+table: Maybe<&2,D.Table>,valid: FoundTable(table)) -> FoundRows(D.rows_table(table)):
  match table:
    case None{}: Unit{}
    case Some{D.Table{name,rs}}: valid

def collection_rows_preserve_validity(+collection: D.Collection,+state: D.State,+valid: {state_values(state) == True{} : Bool}) -> FoundRows(D.rows_collection(collection,state)):
  match collection state:
    case D.Users{} D.State{ts,us}: F.and_boolean_right(tables(ts),rows(us),valid)
    case D.Application{name} D.State{ts,us}: table_rows_preserve_validity(D.find_table(ts,name),table_lookup_preserves_validity(ts,name,F.and_boolean_left(tables(ts),rows(us),valid)))

def ResolvedValues(resolved: Maybe<&2,D.Resolved>) -> Data:
  match resolved:
    case None{}: Unit
    case Some{D.Resolved{schema,rs}}: {rows(rs) == True{} : Bool}

def resolve_preserves_validity(+schema: Maybe<&2,D.SchemaTable>,+rs: Maybe<&2,List<&2,D.Row>>,valid: FoundRows(rs)) -> ResolvedValues(D.resolve_parts(schema,rs)):
  match schema rs:
    case None{} rs: Unit{}
    case Some{schema} None{}: Unit{}
    case Some{schema} Some{rs}: valid

def ObservationValue(observation: D.Observation) -> Data:
  match observation:
    case D.Cell{value}: {D.value_valid(value) == True{} : Bool}
    case D.RowAbsent{}: Unit
    case D.Keys{keys}: Unit
    case D.Count{count}: Unit
    case D.Existence{exists}: Unit

def ResultValue(result: D.ResultOp) -> Data:
  match result:
    case D.FailureData{}: Unit
    case D.Observed{observation}: ObservationValue(observation)
    case D.Changed{state}: Unit

def result_cell_preserves_validity(+value: Maybe<&2,D.Value>,valid: FoundValue(value)) -> ResultValue(D.result_cell(value)):
  match value:
    case None{}: Unit{}
    case Some{value}: valid

def row_read_preserves_validity(+row: Maybe<&2,D.Row>,+name: String,valid: FoundRow(row)) -> ResultValue(D.read_row(row,name)):
  match row:
    case None{}: Unit{}
    case Some{D.Row{key,fs}}: result_cell_preserves_validity(D.find_field(fs,name),field_lookup_preserves_validity(fs,name,valid))

def column_read_preserves_validity(+column: Maybe<&2,D.Column>,+row: Maybe<&2,D.Row>,+name: String,valid: FoundRow(row)) -> ResultValue(D.read_column(column,row,name)):
  match column:
    case None{}: Unit{}
    case Some{column}: row_read_preserves_validity(row,name,valid)

def resolved_read_preserves_validity(+collection: D.Collection,+key: String,+name: String,+resolved: Maybe<&2,D.Resolved>,+state: D.State,valid: ResolvedValues(resolved)) -> ResultValue(D.operate_resolved(D.ReadCell{collection,key,name},resolved,state)):
  match resolved:
    case None{}: Unit{}
    case Some{D.Resolved{D.SchemaTable{table,primary,cs},rs}}: column_read_preserves_validity(D.find_column(cs,name),D.find_row(rs,key),name,row_lookup_preserves_validity(rs,key,valid))

def addressed_read_preserves_validity(allowed: Bool,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+name: String,+valid: {state_values(state) == True{} : Bool}) -> ResultValue(D.operate_address(allowed,schema,state,D.ReadCell{collection,key,name})):
  match allowed:
    case False{}: Unit{}
    case True{}: resolved_read_preserves_validity(collection,key,name,D.resolve_parts(D.schema_collection(collection,schema),D.rows_collection(collection,state)),state,resolve_preserves_validity(D.schema_collection(collection,schema),D.rows_collection(collection,state),collection_rows_preserve_validity(collection,state,valid)))

law actual_reads_of_structured_states_cannot_return_invalid_cell_payloads:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +name: String
  for +valid: {D.structure(schema,state) == True{} : Bool}
  ResultValue(D.operate(schema,state,D.ReadCell{collection,key,name}))
def actual_reads_of_structured_states_cannot_return_invalid_cell_payloads(schema,state,collection,key,name,valid):
  addressed_read_preserves_validity(D.address_op_valid(D.ReadCell{collection,key,name}),schema,state,collection,key,name,actual_structured_state_contains_only_valid_field_payloads(schema,state,valid))

law actual_observed_read_from_a_structured_state_has_a_valid_cell_payload:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +name: String
  for +observation: D.Observation
  for +valid: {D.structure(schema,state) == True{} : Bool}
  for actual: {D.operate(schema,state,D.ReadCell{collection,key,name}) == D.Observed{observation} : D.ResultOp}
  ObservationValue(observation)
def actual_observed_read_from_a_structured_state_has_a_valid_cell_payload(schema,state,collection,key,name,observation,valid,actual):
  %actual : ResultValue(_)
  actual_reads_of_structured_states_cannot_return_invalid_cell_payloads(schema,state,collection,key,name,valid)
