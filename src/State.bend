# Private state transport. The client sends only arguments and never receives
# access to this value; published state is maintained by the core controller.
import Base
import ../contract/Data.bend as D

def fields_cons(name: String, value: D.Value,
  rest: Maybe<&2, List<&2, D.Field>>) -> Maybe<&2, List<&2, D.Field>>:
  match rest:
    case None{}:
      None{}
    case Some{cs}:
      Some{Con{D.Field{name, value}, cs}}

def fields(v: D.Value) -> Maybe<&2, List<&2, D.Field>>:
  match v:
    case D.VRecordEmpty{}:
      Some{Nil{}}
    case D.VRecord{name, value, rest}:
      fields_cons(name, value, fields(rest))
    case _:
      None{}

def row_key(v: Maybe<&2, D.Value>, cs: List<&2, D.Field>) -> Maybe<&2, D.Row>:
  match v:
    case Some{D.VText{k}}:
      Some{D.Row{k, cs}}
    case _:
      None{}

def row_fields(cs: Maybe<&2, List<&2, D.Field>>, key: String) -> Maybe<&2, D.Row>:
  match cs:
    case None{}:
      None{}
    case Some{+fs}:
      row_key(D.find_field(fs, key), fs)

def join_rows(h: Maybe<&2, D.Row>, t: Maybe<&2, List<&2, D.Row>>) -> Maybe<&2, List<&2, D.Row>>:
  match h t:
    case Some{row} Some{rest}:
      Some{Con{row, rest}}
    case _ _:
      None{}

def rows(v: D.Value, +key: String) -> Maybe<&2, List<&2, D.Row>>:
  match v:
    case D.VListEmpty{}:
      Some{Nil{}}
    case D.VList{h, t}:
      join_rows(row_fields(fields(h), key), rows(t, key))
    case _:
      None{}

def table_rows(ok: Bool, name: String, ls: Maybe<&2, List<&2, D.Row>>) -> Maybe<&2, D.Table>:
  match ok ls:
    case True{} Some{rs}:
      Some{D.Table{name, rs}}
    case _ _:
      None{}

def table(v: D.Value, schema: D.SchemaTable) -> Maybe<&2, D.Table>:
  match v schema:
    case D.VRecord{n0, D.VText{+name}, D.VRecord{n1, ls, D.VRecordEmpty{}}}
      D.SchemaTable{expected, key, cs}:
      table_rows(String.eq(n0, "name") && String.eq(n1, "rows") &&
        String.eq(name, expected), name, rows(ls, key))
    case _ _:
      None{}

def join_tables(h: Maybe<&2, D.Table>, t: Maybe<&2, List<&2, D.Table>>) -> Maybe<&2, List<&2, D.Table>>:
  match h t:
    case Some{table} Some{rest}:
      Some{Con{table, rest}}
    case _ _:
      None{}

def tables(v: D.Value, schemas: List<&2, D.SchemaTable>) -> Maybe<&2, List<&2, D.Table>>:
  match v schemas:
    case D.VListEmpty{} Nil{}:
      Some{Nil{}}
    case D.VList{h, t} Con{is_value, et}:
      join_tables(table(h, is_value), tables(t, et))
    case _ _:
      None{}

def join_state(ok: Bool, ts: Maybe<&2, List<&2, D.Table>>,
  us: Maybe<&2, List<&2, D.Row>>) -> Maybe<&2, D.State>:
  match ok ts us:
    case True{} Some{t} Some{u}:
      Some{D.State{t, u}}
    case _ _ _:
      None{}

def form(v: D.Value, schema: D.Schema) -> Maybe<&2, D.State>:
  match v schema:
    case D.VRecord{n0, ts, D.VRecord{n1, us, D.VRecordEmpty{}}} D.Schema{es}:
      join_state(String.eq(n0, "tables") && String.eq(n1, "users"),
        tables(ts, es), rows(us, "id"))
    case _ _:
      None{}

def verify(ok: Bool, state: D.State) -> Maybe<&2, D.State>:
  match ok:
    case True{}:
      Some{state}
    case False{}:
      None{}

def verify_result(result: Maybe<&2, D.State>, schema: D.Schema) -> Maybe<&2, D.State>:
  match result:
    case None{}:
      None{}
    case Some{+s}:
      verify(D.structure(schema, s), s)

def decode(v: D.Value, +schema: D.Schema) -> Maybe<&2, D.State>:
  verify_result(form(v, schema), schema)
