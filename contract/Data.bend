# JayDB: data universe and reference logical operations.
# Contains no permission policies; no operation in this module
# is a separate public interface outside code-and-proof submission.
import Base

type Value is Data:
  VAbsent{}
  VBool{value: Bool}
  VInt{high: U32, low: U32}
  VText{text: String}
  VListEmpty{}
  VList{head: Value, tail: Value}
  VRecordEmpty{}
  VRecord{name: String, value: Value, rest: Value}

type ColumnKind is Data:
  TextValue{}
  Boolean{}
  Integer{}

type Column is Data:
  Column{name: String, kind: ColumnKind, optional: Bool}

type SchemaTable is Data:
  SchemaTable{name: String, key: String, columns: List<&2, Column>}

type Schema is Data:
  Schema{tables: List<&2, SchemaTable>}

type Field is Data:
  Field{name: String, value: Value}

type Row is Data:
  Row{key: String, fields: List<&2, Field>}

type Table is Data:
  Table{name: String, rows: List<&2, Row>}

type State is Data:
  State{tables: List<&2, Table>, users: List<&2, Row>}

type Context is Data:
  Context{id: String, kind: String}

type Collection is Data:
  Users{}
  Application{name: String}

type Operation is Data:
  ReadCell{collection: Collection, key: String, column: String}
  ViewExistence{collection: Collection, key: String}
  CountRows{collection: Collection}
  EnumerateKeys{collection: Collection}
  DefineRow{collection: Collection, key: String, fields: List<&2, Field>}
  DefineColumn{collection: Collection, key: String, column: String, value: Value}
  RemoveRow{collection: Collection, key: String}

type Observation is Data:
  RowAbsent{}
  Cell{value: Value}
  Existence{exists: Bool}
  Count{number: Nat}
  Keys{keys: List<&2, String>}

type ResultOp is Data:
  FailureData{}
  Observed{observation: Observation}
  Changed{state: State}

# U32 is exact; the two words of VInt represent all 64 bits
# of two's complement. There is no implicit numeric conversion.
def scalar_valid(+n: U32) -> Bool:
  U32.is_lt(n, 1114112) && (U32.is_lt(n, 55296) || U32.is_ge(n, 57344))

def unicode_valid(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{n}, t}:
      scalar_valid(n) && unicode_valid(t)

def start_name(+c: Char) -> Bool:
  Char.is_alpha(c) || Char.is_eq(c, '_')

def rest_name(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      (start_name(h) || Char.is_digit(h)) && rest_name(t)

def name_valid(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      start_name(h) && rest_name(t) && Nat.is_le(String.length(s), 64n)

def is_list(v: Value) -> Bool:
  match v:
    case VListEmpty{}:
      True{}
    case VList{h, t}:
      True{}
    case _:
      False{}

def is_record(v: Value) -> Bool:
  match v:
    case VRecordEmpty{}:
      True{}
    case VRecord{n, v, r}:
      True{}
    case _:
      False{}

def record_later(v: Value, name: String) -> Bool:
  match v:
    case VRecordEmpty{}:
      True{}
    case VRecord{n, x, r}:
      String.is_lt(name, n)
    case _:
      False{}

def value_valid(v: Value) -> Bool:
  match v:
    case VAbsent{}:
      True{}
    case VBool{b}:
      True{}
    case VInt{a, b}:
      True{}
    case VText{s}:
      unicode_valid(s)
    case VListEmpty{}:
      True{}
    case VList{h, +t}:
      value_valid(h) && is_list(t) && value_valid(t)
    case VRecordEmpty{}:
      True{}
    case VRecord{+n, v, +r}:
      name_valid(n) && value_valid(v) && record_later(r, n) && value_valid(r)

def value_kind(t: ColumnKind, v: Value) -> Bool:
  match t v:
    case TextValue{} VText{s}:
      unicode_valid(s)
    case Boolean{} VBool{b}:
      True{}
    case Integer{} VInt{a, b}:
      True{}
    case _ _:
      False{}

def fits_column(v: Value, t: ColumnKind, optional: Bool) -> Bool:
  match v:
    case VAbsent{}:
      optional
    case _:
      value_kind(t, v)

def column_name(c: Column) -> String:
  Column{n, t, o} = c
  n

def field_name(c: Field) -> String:
  Field{n, v} = c
  n

def find_column(xs: List<&2, Column>, +name: String) -> Maybe<&2, Column>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Bool.pick(Maybe<&2, Column>, String.eq(column_name(h), name), Some{h}, find_column(t, name))

def find_field(xs: List<&2, Field>, +name: String) -> Maybe<&2, Value>:
  match xs:
    case Nil{}:
      None{}
    case Con{Field{n, v}, t}:
      Bool.pick(Maybe<&2, Value>, String.eq(n, name), Some{v}, find_field(t, name))

def find_row(xs: List<&2, Row>, +key: String) -> Maybe<&2, Row>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Row{k, fs} = h
      Bool.pick(Maybe<&2, Row>, String.eq(k, key), Some{h}, find_row(t, key))

def find_schema(xs: List<&2, SchemaTable>, +name: String) -> Maybe<&2, SchemaTable>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      SchemaTable{n, k, cs} = h
      Bool.pick(Maybe<&2, SchemaTable>, String.eq(n, name), Some{h}, find_schema(t, name))

def find_table(xs: List<&2, Table>, +name: String) -> Maybe<&2, Table>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Table{n, ls} = h
      Bool.pick(Maybe<&2, Table>, String.eq(n, name), Some{h}, find_table(t, name))

def schema_users() -> SchemaTable:
  SchemaTable{"users", "id", [Column{"credential", TextValue{}, False{}}, Column{"id", TextValue{}, False{}}, Column{"kind", TextValue{}, False{}}]}

def schema_collection(c: Collection, e: Schema) -> Maybe<&2, SchemaTable>:
  match c:
    case Users{}:
      Some{schema_users()}
    case Application{n}:
      Schema{ts} = e
      find_schema(ts, n)

def rows_table(m: Maybe<&2, Table>) -> Maybe<&2, List<&2, Row>>:
  match m:
    case None{}:
      None{}
    case Some{Table{n, ls}}:
      Some{ls}

def rows_collection(c: Collection, s: State) -> Maybe<&2, List<&2, Row>>:
  match c:
    case Users{}:
      State{ts, us} = s
      Some{us}
    case Application{n}:
      State{ts, us} = s
      rows_table(find_table(ts, n))

# Columns, fields, tables and rows use strict canonical order.
# This is the mathematical representation; memory may use another order.
def columns_later(xs: List<&2, Column>, name: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      String.is_lt(name, column_name(h))

def columns_valid_cases(xs: List<&2, Column>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Column{+n, t, o}, +r}:
      name_valid(n) && columns_later(r, n) && columns_valid_cases(r)

def key_column(c: Maybe<&2, Column>) -> Bool:
  match c:
    case Some{Column{n, TextValue{}, False{}}}:
      True{}
    case _:
      False{}

def schema_table_valid(e: SchemaTable) -> Bool:
  SchemaTable{n, k, +cs} = e
  name_valid(n) && columns_valid_cases(cs) && key_column(find_column(cs, k))

def schemas_later(xs: List<&2, SchemaTable>, name: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{SchemaTable{n, k, cs}, t}:
      String.is_lt(name, n)

def schemas_all_valid(xs: List<&2, SchemaTable>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      SchemaTable{n, k, cs} = h
      schema_table_valid(h) && schemas_later(t, n) && schemas_all_valid(t)

def schema_valid(e: Schema) -> Bool:
  Schema{ts} = e
  schemas_all_valid(ts)

def fields_all_valid(cs: List<&2, Column>, fs: List<&2, Field>) -> Bool:
  match cs fs:
    case Nil{} Nil{}:
      True{}
    case Con{Column{cn, ct, co}, cr} Con{Field{fn, fv}, fr}:
      String.eq(cn, fn) && fits_column(fv, ct, co) && fields_all_valid(cr, fr)
    case _ _:
      False{}

def key_correct(v: Maybe<&2, Value>, key: String) -> Bool:
  match v:
    case Some{VText{s}}:
      String.eq(s, key)
    case _:
      False{}

def row_is_valid(e: SchemaTable, l: Row) -> Bool:
  SchemaTable{n, k, cs} = e
  Row{+id, +fs} = l
  unicode_valid(id) && fields_all_valid(cs, fs) && key_correct(find_field(fs, k), id)

def rows_later(xs: List<&2, Row>, key: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Row{k, fs}, t}:
      String.is_lt(key, k)

def rows_valid_cases(xs: List<&2, Row>, +e: SchemaTable) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Row{k, fs} = h
      row_is_valid(e, h) && rows_later(t, k) && rows_valid_cases(t, e)

def schema_name(e: SchemaTable) -> String:
  SchemaTable{n, k, cs} = e
  n

def tables_valid_cases(es: List<&2, SchemaTable>, ts: List<&2, Table>) -> Bool:
  match es ts:
    case Nil{} Nil{}:
      True{}
    case Con{+e, er} Con{Table{n, ls}, tr}:
      String.eq(schema_name(e), n) && rows_valid_cases(ls, e) && tables_valid_cases(er, tr)
    case _ _:
      False{}

def text_field(v: Maybe<&2, Value>) -> String:
  match v:
    case Some{VText{s}}:
      s
    case _:
      ""

def credential_row(l: Row) -> String:
  Row{k, fs} = l
  text_field(find_field(fs, "credential"))

def credential_different(xs: List<&2, Row>, +cred: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.not(String.eq(credential_row(h), cred)) && credential_different(t, cred)

def credentials_valid_cases(xs: List<&2, Row>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, +t}:
      +cred = credential_row(h)
      Bool.not(String.is_empty(cred)) && credential_different(t, cred) && credentials_valid_cases(t)

def structure(e: Schema, s: State) -> Bool:
  Schema{es} = e
  State{ts, +us} = s
  tables_valid_cases(es, ts) && rows_valid_cases(us, schema_users()) && credentials_valid_cases(us)

# Authentication considers only the initial published user registry.
def context_row(l: Row) -> Context:
  Row{id, fs} = l
  Context{id, text_field(find_field(fs, "kind"))}

def authenticate_rows(xs: List<&2, Row>, +credential: String) -> Maybe<&2, Context>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Bool.pick(Maybe<&2, Context>, String.eq(credential_row(h), credential), Some{context_row(h)}, authenticate_rows(t, credential))

def authenticate(s: State, credential: String) -> Maybe<&2, Context>:
  State{ts, us} = s
  authenticate_rows(us, credential)

# The universal proof fixes the authenticated identity, not the credential.
# This predicate requires a user with that ID and type in the initial state.
def context_id(c: Context) -> String:
  Context{id, kind} = c
  id

def context_equal(a: Context, b: Context) -> Bool:
  Context{ai, at} = a
  Context{bi, bt} = b
  String.eq(ai, bi) && String.eq(at, bt)

def context_found(m: Maybe<&2, Row>, c: Context) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{l}:
      context_equal(context_row(l), c)

def context_present(s: State, +c: Context) -> Bool:
  State{ts, us} = s
  context_found(find_row(us, context_id(c)), c)

# Blind updates preserve fields that were not replaced.
def row_key(l: Row) -> String:
  Row{k, fs} = l
  k

def insert_row(xs: List<&2, Row>, +new: Row) -> List<&2, Row>:
  match xs:
    case Nil{}:
      [new]
    case Con{+h, +t}:
      Bool.pick(List<&2, Row>, String.is_lt(row_key(new), row_key(h)), new <> h <> t,
        Bool.pick(List<&2, Row>, String.eq(row_key(new), row_key(h)), new <> t, h <> insert_row(t, new)))

def remove_row(xs: List<&2, Row>, +key: String) -> List<&2, Row>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +rest = remove_row(t, key)
      Bool.pick(List<&2, Row>, String.eq(row_key(h), key), rest, h <> rest)

def substitute_field(xs: List<&2, Field>, +name: String, +value: Value) -> List<&2, Field>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Bool.pick(Field, String.eq(field_name(h), name), Field{name, value}, h) <> substitute_field(t, name, value)

def substitute_in_row(l: Row, name: String, value: Value) -> Row:
  Row{k, fs} = l
  Row{k, substitute_field(fs, name, value)}

def substitute_column(xs: List<&2, Row>, +key: String, +name: String, +value: Value) -> List<&2, Row>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Bool.pick(Row, String.eq(row_key(h), key), substitute_in_row(h, name, value), h) <> substitute_column(t, key, name, value)

def swap_table(xs: List<&2, Table>, +name: String, +rows: List<&2, Row>) -> List<&2, Table>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Table{+n, ls}, t}:
      Bool.pick(Table, String.eq(n, name), Table{n, rows}, Table{n, ls}) <> swap_table(t, name, rows)

def swap_collection(c: Collection, s: State, rows: List<&2, Row>) -> State:
  match c:
    case Users{}:
      State{ts, us} = s
      State{ts, rows}
    case Application{name}:
      State{ts, us} = s
      State{swap_table(ts, name, rows), us}

def keys_rows(xs: List<&2, Row>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Row{k, fs}, t}:
      k <> keys_rows(t)

def exists_row(m: Maybe<&2, Row>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{l}:
      True{}

def result_cell(v: Maybe<&2, Value>) -> ResultOp:
  match v:
    case None{}:
      FailureData{}
    case Some{x}:
      Observed{Cell{x}}

def read_row(m: Maybe<&2, Row>, column: String) -> ResultOp:
  match m:
    case None{}:
      Observed{RowAbsent{}}
    case Some{Row{k, fs}}:
      result_cell(find_field(fs, column))

def read_column(c: Maybe<&2, Column>, l: Maybe<&2, Row>, name: String) -> ResultOp:
  match c:
    case None{}:
      FailureData{}
    case Some{x}:
      read_row(l, name)

def column_write_is_valid(c: Maybe<&2, Column>, +primary: String, +key: String, +v: Value) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{Column{name, t, o}}:
      fits_column(v, t, o) && (Bool.not(String.eq(name, primary)) || key_correct(Some{v}, key))

def write_se(ok: Bool, c: Collection, s: State, rows: List<&2, Row>) -> ResultOp:
  match ok:
    case False{}:
      FailureData{}
    case True{}:
      Changed{swap_collection(c, s, rows)}

type Resolved is Data:
  Resolved{schema: SchemaTable, rows: List<&2, Row>}

def resolve_parts(e: Maybe<&2, SchemaTable>, ls: Maybe<&2, List<&2, Row>>) -> Maybe<&2, Resolved>:
  match e ls:
    case Some{x} Some{ys}:
      Some{Resolved{x, ys}}
    case _ _:
      None{}

def collection_op(o: Operation) -> Collection:
  match o:
    case ReadCell{c, k, n}:
      c
    case ViewExistence{c, k}:
      c
    case CountRows{c}:
      c
    case EnumerateKeys{c}:
      c
    case DefineRow{c, k, fs}:
      c
    case DefineColumn{c, k, n, v}:
      c
    case RemoveRow{c, k}:
      c

def operate_resolved(o: Operation, r: Maybe<&2, Resolved>, s: State) -> ResultOp:
  match o r:
    case ReadCell{c, k, +n} Some{Resolved{SchemaTable{en, pk, cs}, ls}}:
      read_column(find_column(cs, n), find_row(ls, k), n)
    case ViewExistence{c, k} Some{Resolved{e, ls}}:
      Observed{Existence{exists_row(find_row(ls, k))}}
    case CountRows{c} Some{Resolved{e, ls}}:
      Observed{Count{List.length(&2, Row, ls)}}
    case EnumerateKeys{c} Some{Resolved{e, ls}}:
      Observed{Keys{keys_rows(ls)}}
    case DefineRow{c, +k, +fs} Some{Resolved{e, ls}}:
      write_se(row_is_valid(e, Row{k, fs}), c, s, insert_row(ls, Row{k, fs}))
    case DefineColumn{c, +k, +n, +v} Some{Resolved{SchemaTable{en, pk, cs}, ls}}:
      write_se(column_write_is_valid(find_column(cs, n), pk, k, v), c, s, substitute_column(ls, k, n, v))
    case RemoveRow{c, k} Some{Resolved{e, ls}}:
      Changed{swap_collection(c, s, remove_row(ls, k))}
    case _ _:
      FailureData{}

# A program-computed key must also be valid Unicode.
# Rejection of this key depends on the argument, never on row existence.
def address_op_valid(o: Operation) -> Bool:
  match o:
    case ReadCell{c, k, n}:
      unicode_valid(k)
    case ViewExistence{c, k}:
      unicode_valid(k)
    case CountRows{c}:
      True{}
    case EnumerateKeys{c}:
      True{}
    case DefineRow{c, k, fs}:
      unicode_valid(k)
    case DefineColumn{c, k, n, v}:
      unicode_valid(k)
    case RemoveRow{c, k}:
      unicode_valid(k)

def operate_address(ok: Bool, e: Schema, +s: State, +o: Operation) -> ResultOp:
  match ok:
    case False{}:
      FailureData{}
    case True{}:
      +c = collection_op(o)
      operate_resolved(o, resolve_parts(schema_collection(c, e), rows_collection(c, s)), s)

# A write returns neither existence flags nor previous values.
# Address and new-value validation precedes every effect.
def operate(e: Schema, s: State, +o: Operation) -> ResultOp:
  operate_address(address_op_valid(o), e, s, o)

# Canonical form used to measure/publish state; it does not require this
# in-memory representation. A Row stores its key twice
# only in the model; the canonical value stores the fields once.
def fields_value(xs: List<&2, Field>) -> Value:
  match xs:
    case Nil{}:
      VRecordEmpty{}
    case Con{Field{n, v}, t}:
      VRecord{n, v, fields_value(t)}

def rows_value(xs: List<&2, Row>) -> Value:
  match xs:
    case Nil{}:
      VListEmpty{}
    case Con{Row{k, fs}, t}:
      VList{fields_value(fs), rows_value(t)}

def tables_value(xs: List<&2, Table>) -> Value:
  match xs:
    case Nil{}:
      VListEmpty{}
    case Con{Table{n, ls}, t}:
      VList{VRecord{"name", VText{n}, VRecord{"rows", rows_value(ls), VRecordEmpty{}}}, tables_value(t)}

def state_value(s: State) -> Value:
  State{ts, us} = s
  VRecord{"tables", tables_value(ts), VRecord{"users", rows_value(us), VRecordEmpty{}}}
