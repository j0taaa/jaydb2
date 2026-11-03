# Roundtrip of PRIVATE State representation using actual src/State.
# This proof is not soundness of the src/Codec byte parser.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/State.bend as E
import ../src/Request.bend as Q
import ../contract/Protocol.bend as P
import ./Foundations.bend as F
import ./Orders.bend as O

law fields_reconstruct:
  for fs: List<&2, D.Field>
  {E.fields(D.fields_value(fs)) == Some{fs} : Maybe<&2, List<&2, D.Field>>}
def fields_reconstruct(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{D.Field{name, value}, t}:
      %Equal.sym(Maybe<&2, List<&2, D.Field>>, E.fields(D.fields_value(t)), Some{t},
        fields_reconstruct(t)) :
        {E.fields_cons(name, value, _) == Some{Con{D.Field{name, value}, t}} : Maybe<&2, List<&2, D.Field>>}
      {==}

def key_textual_reconstructs(v: D.Value, +k: String, -fs: List<&2, D.Field>,
  correct: {D.key_correct(Some{v}, k) == True{} : Bool}) ->
  {E.row_key(Some{v}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}:
  match v:
    case D.VText{s}:
      %O.string_equal(s, k, correct) : {Some{D.Row{s, fs}} == Some{D.Row{_, fs}} : Maybe<&2, D.Row>}
      {==}
    case D.VAbsent{}:
      F.absurd_boolean({E.row_key(Some{D.VAbsent{}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case D.VBool{b}:
      F.absurd_boolean({E.row_key(Some{D.VBool{b}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case D.VInt{a, b}:
      F.absurd_boolean({E.row_key(Some{D.VInt{a, b}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case D.VListEmpty{}:
      F.absurd_boolean({E.row_key(Some{D.VListEmpty{}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case D.VList{h, t}:
      F.absurd_boolean({E.row_key(Some{D.VList{h, t}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case D.VRecordEmpty{}:
      F.absurd_boolean({E.row_key(Some{D.VRecordEmpty{}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case D.VRecord{n, x, r}:
      F.absurd_boolean({E.row_key(Some{D.VRecord{n, x, r}}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)

def key_reconstructs(v: Maybe<&2, D.Value>, k: String, -fs: List<&2, D.Field>,
  correct: {D.key_correct(v, k) == True{} : Bool}) ->
  {E.row_key(v, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}:
  match v:
    case None{}:
      F.absurd_boolean({E.row_key(None{}, fs) == Some{D.Row{k, fs}} : Maybe<&2, D.Row>}, correct)
    case Some{x}:
      key_textual_reconstructs(x, k, fs, correct)

law row_reconstructs:
  for e: D.SchemaTable
  for +row: D.Row
  for is_valid: {D.row_is_valid(e, row) == True{} : Bool}
  {E.row_fields(E.fields(D.fields_value((fields_row(row)))), key_schema(e)) ==
    Some{row} : Maybe<&2, D.Row>}

def fields_row(row: D.Row) -> List<&2, D.Field>:
  D.Row{k, fs} = row
  fs

def key_schema(e: D.SchemaTable) -> String:
  D.SchemaTable{n, k, cs} = e
  k

def row_reconstructs(e, row, is_valid):
  match e row:
    case D.SchemaTable{n, +k, cs} D.Row{id, fs}:
      correct = F.and_boolean_right(D.unicode_valid(id) && D.fields_all_valid(cs, fs),
        D.key_correct(D.find_field(fs, k), id), is_valid)
      %Equal.sym(Maybe<&2, List<&2, D.Field>>, E.fields(D.fields_value(fs)), Some{fs},
        fields_reconstruct(fs)) :
        {E.row_fields(_, k) == Some{D.Row{id, fs}} : Maybe<&2, D.Row>}
      key_reconstructs(D.find_field(fs, k), id, fs, correct)

law rows_reconstruct:
  for +xs: List<&2, D.Row>
  for +e: D.SchemaTable
  for +is_valid: {D.rows_valid_cases(xs, e) == True{} : Bool}
  {E.rows(D.rows_value(xs), key_schema(e)) == Some{xs} : Maybe<&2, List<&2, D.Row>>}
def rows_reconstruct(xs, e, is_valid):
  match xs e:
    case Nil{} D.SchemaTable{n, k, cs}:
      {==}
    case Con{D.Row{id, fs}, t} D.SchemaTable{n, k, cs}:
      +e0 = {D.SchemaTable{n, k, cs} : D.SchemaTable}
      first = F.and_boolean_left(D.row_is_valid(e0, D.Row{id, fs}) && D.rows_later(t, id),
        D.rows_valid_cases(t, e0), is_valid)
      head = F.and_boolean_left(D.row_is_valid(e0, D.Row{id, fs}), D.rows_later(t, id), first)
      tail = F.and_boolean_right(D.row_is_valid(e0, D.Row{id, fs}) && D.rows_later(t, id), D.rows_valid_cases(t, e0), is_valid)
      %Equal.sym(Maybe<&2, D.Row>, E.row_fields(E.fields(D.fields_value(fs)), k), Some{D.Row{id, fs}},
        row_reconstructs(e0, D.Row{id, fs}, head)) :
        {E.join_rows(_, E.rows(D.rows_value(t), k)) == Some{Con{D.Row{id, fs}, t}} : Maybe<&2, List<&2, D.Row>>}
      %Equal.sym(Maybe<&2, List<&2, D.Row>>, E.rows(D.rows_value(t), k), Some{t}, rows_reconstruct(t, e0, tail)) :
        {E.join_rows(Some{D.Row{id, fs}}, _) == Some{Con{D.Row{id, fs}, t}} : Maybe<&2, List<&2, D.Row>>}
      {==}

law table_reconstructs:
  for +e: D.SchemaTable
  for +t: D.Table
  for name: {String.eq(D.schema_name(e), name_table(t)) == True{} : Bool}
  for rows: {D.rows_valid_cases(rows_table(t), e) == True{} : Bool}
  {E.table(table_value(t), e) == Some{t} : Maybe<&2, D.Table>}

def name_table(t: D.Table) -> String:
  D.Table{n, ls} = t
  n

def rows_table(t: D.Table) -> List<&2, D.Row>:
  D.Table{n, ls} = t
  ls

def table_value(t: D.Table) -> D.Value:
  D.Table{n, ls} = t
  D.VRecord{"name", D.VText{n}, D.VRecord{"rows", D.rows_value(ls), D.VRecordEmpty{}}}

def table_reconstructs(e, t, name, rows):
  match e t:
    case D.SchemaTable{expected, k, cs} D.Table{n, ls}:
      %Equal.sym(Bool, String.eq(n, expected), True{}, O.string_eq_inverse(expected, n, name)) :
        {E.table_rows(_, n, E.rows(D.rows_value(ls), k)) == Some{D.Table{n, ls}} : Maybe<&2, D.Table>}
      %Equal.sym(Maybe<&2, List<&2, D.Row>>, E.rows(D.rows_value(ls), k), Some{ls},
        rows_reconstruct(ls, D.SchemaTable{expected, k, cs}, rows)) :
        {E.table_rows(True{}, n, _) == Some{D.Table{n, ls}} : Maybe<&2, D.Table>}
      {==}

law tables_reconstruct:
  for +es: List<&2, D.SchemaTable>
  for +ts: List<&2, D.Table>
  for +is_valid: {D.tables_valid_cases(es, ts) == True{} : Bool}
  {E.tables(D.tables_value(ts), es) == Some{ts} : Maybe<&2, List<&2, D.Table>>}
def tables_reconstruct(es, ts, is_valid):
  match es ts:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{t, tr}:
      F.absurd_boolean({E.tables(D.tables_value(Con{t, tr}), Nil{}) == Some{Con{t, tr}} : Maybe<&2, List<&2, D.Table>>}, is_valid)
    case Con{e, er} Nil{}:
      F.absurd_boolean({E.tables(D.tables_value(Nil{}), Con{e, er}) == Some{Nil{}} : Maybe<&2, List<&2, D.Table>>}, is_valid)
    case Con{e, er} Con{D.Table{n, ls}, tr}:
      +first = F.and_boolean_left(String.eq(D.schema_name(e), n) && D.rows_valid_cases(ls, e), D.tables_valid_cases(er, tr), is_valid)
      name = F.and_boolean_left(String.eq(D.schema_name(e), n), D.rows_valid_cases(ls, e), first)
      rows = F.and_boolean_right(String.eq(D.schema_name(e), n), D.rows_valid_cases(ls, e), first)
      tail = F.and_boolean_right(String.eq(D.schema_name(e), n) && D.rows_valid_cases(ls, e), D.tables_valid_cases(er, tr), is_valid)
      %Equal.sym(Maybe<&2, D.Table>, E.table(table_value(D.Table{n, ls}), e), Some{D.Table{n, ls}},
        table_reconstructs(e, D.Table{n, ls}, name, rows)) :
        {E.join_tables(_, E.tables(D.tables_value(tr), er)) == Some{Con{D.Table{n, ls}, tr}} : Maybe<&2, List<&2, D.Table>>}
      %Equal.sym(Maybe<&2, List<&2, D.Table>>, E.tables(D.tables_value(tr), er), Some{tr}, tables_reconstruct(er, tr, tail)) :
        {E.join_tables(Some{D.Table{n, ls}}, _) == Some{Con{D.Table{n, ls}, tr}} : Maybe<&2, List<&2, D.Table>>}
      {==}

law form_reconstructs_state:
  for +e: D.Schema
  for +s: D.State
  for +structure: {D.structure(e, s) == True{} : Bool}
  {E.form(D.state_value(s), e) == Some{s} : Maybe<&2, D.State>}
def form_reconstructs_state(e, s, structure):
  match e s:
    case D.Schema{es} D.State{ts, us}:
      +first = F.and_boolean_left(D.tables_valid_cases(es, ts) && D.rows_valid_cases(us, D.schema_users()), D.credentials_valid_cases(us), structure)
      tables = F.and_boolean_left(D.tables_valid_cases(es, ts), D.rows_valid_cases(us, D.schema_users()), first)
      users = F.and_boolean_right(D.tables_valid_cases(es, ts), D.rows_valid_cases(us, D.schema_users()), first)
      %Equal.sym(Maybe<&2, List<&2, D.Table>>, E.tables(D.tables_value(ts), es), Some{ts}, tables_reconstruct(es, ts, tables)) :
        {E.join_state(True{}, _, E.rows(D.rows_value(us), "id")) == Some{D.State{ts, us}} : Maybe<&2, D.State>}
      %Equal.sym(Maybe<&2, List<&2, D.Row>>, E.rows(D.rows_value(us), "id"), Some{us}, rows_reconstruct(us, D.schema_users(), users)) :
        {E.join_state(True{}, Some{ts}, _) == Some{D.State{ts, us}} : Maybe<&2, D.State>}
      {==}

law transport_private_preserves_state:
  for +e: D.Schema
  for +s: D.State
  for +structure: {D.structure(e, s) == True{} : Bool}
  {E.decode(D.state_value(s), e) == Some{s} : Maybe<&2, D.State>}
def transport_private_preserves_state(e, s, structure):
  %Equal.sym(Maybe<&2, D.State>, E.form(D.state_value(s), e), Some{s}, form_reconstructs_state(e, s, structure)) :
    {E.verify_result(_, e) == Some{s} : Maybe<&2, D.State>}
  %Equal.sym(Bool, D.structure(e, s), True{}, structure) : {E.verify(_, s) == Some{s} : Maybe<&2, D.State>}
  {==}

law request_is_valid_preserves_all_os_fields:
  for +r: P.Request
  for is_valid: {D.value_valid(P.request_value(r)) == True{} : Bool}
  {Q.extract(P.request_value(r)) == Some{r} : Maybe<&2, P.Request>}
def request_is_valid_preserves_all_os_fields(r, is_valid):
  %Equal.sym(Bool, D.value_valid(P.request_value(r)), True{}, is_valid) :
    {Q.validate(_, Q.form(P.request_value(r))) == Some{r} : Maybe<&2, P.Request>}
  Q.form_reconstructs_request(r)

def verify_success(b: Bool, +s0: D.State, +s: D.State,
  obtained: {E.verify(b, s0) == Some{s} : Maybe<&2, D.State>}) ->
  L.E<{b == True{} : Bool}, {s0 == s : D.State}>:
  match b:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, {s0 == s : D.State}>, F.none_negative_some(D.State, s, obtained))
    case True{}:
      L.Both{{==}, F.some_injective(D.State, s0, s, obtained)}

def verify_result_faithful(q: Maybe<&2, D.State>, +e: D.Schema, +s: D.State,
  obtained: {E.verify_result(q, e) == Some{s} : Maybe<&2, D.State>}) ->
  {D.structure(e, s) == True{} : Bool}:
  match q:
    case None{}:
      L.ex_false({D.structure(e, s) == True{} : Bool}, F.none_negative_some(D.State, s, obtained))
    case Some{+s0}:
      F.combined_pair({D.structure(e, s) == True{} : Bool}, {D.structure(e, s0) == True{} : Bool},
        {s0 == s : D.State}, verify_success(D.structure(e, s0), s0, s, obtained),
        structure => equality =>
          %equality : {D.structure(e, _) == True{} : Bool}
          structure)

law transport_private_only_returns_state_structured:
  for +v: D.Value
  for +e: D.Schema
  for +s: D.State
  for obtained: {E.decode(v, e) == Some{s} : Maybe<&2, D.State>}
  {D.structure(e, s) == True{} : Bool}
def transport_private_only_returns_state_structured(v, e, s, obtained):
  verify_result_faithful(E.form(v, e), e, s, obtained)

def choose_success(b: Bool, +r0: P.Request, +r: P.Request,
  obtained: {Q.choose(b, r0) == Some{r} : Maybe<&2, P.Request>}) ->
  L.E<{b == True{} : Bool}, {r == r0 : P.Request}>:
  match b:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, {r == r0 : P.Request}>, F.none_negative_some(P.Request, r, obtained))
    case True{}:
      L.Both{{==}, Equal.sym(P.Request, r0, r, F.some_injective(P.Request, r0, r, obtained))}

def names_reconstruct(+n0: String, +n1: String, +n2: String, +n3: String,
  -args: D.Value, -cod: String, -cred: String, -pi: String,
  +correct: {String.eq(n0, "arguments") && String.eq(n1, "code") &&
    String.eq(n2, "credential") && String.eq(n3, "proof") == True{} : Bool}) ->
  {D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred},
    D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(P.Request{cred, cod, args, pi}) : D.Value}:
  +three = F.and_boolean_left(String.eq(n0, "arguments") && String.eq(n1, "code") && String.eq(n2, "credential"), String.eq(n3, "proof"), correct)
  +two = F.and_boolean_left(String.eq(n0, "arguments") && String.eq(n1, "code"), String.eq(n2, "credential"), three)
  e0 = O.string_equal(n0, "arguments", F.and_boolean_left(String.eq(n0, "arguments"), String.eq(n1, "code"), two))
  e1 = O.string_equal(n1, "code", F.and_boolean_right(String.eq(n0, "arguments"), String.eq(n1, "code"), two))
  e2 = O.string_equal(n2, "credential", F.and_boolean_right(String.eq(n0, "arguments") && String.eq(n1, "code"), String.eq(n2, "credential"), three))
  e3 = O.string_equal(n3, "proof", F.and_boolean_right(String.eq(n0, "arguments") && String.eq(n1, "code") && String.eq(n2, "credential"), String.eq(n3, "proof"), correct))
  %Equal.sym(String, n0, "arguments", e0) : {D.VRecord{_, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(P.Request{cred, cod, args, pi}) : D.Value}
  %Equal.sym(String, n1, "code", e1) : {D.VRecord{"arguments", args, D.VRecord{_, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(P.Request{cred, cod, args, pi}) : D.Value}
  %Equal.sym(String, n2, "credential", e2) : {D.VRecord{"arguments", args, D.VRecord{"code", D.VText{cod}, D.VRecord{_, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(P.Request{cred, cod, args, pi}) : D.Value}
  %Equal.sym(String, n3, "proof", e3) : {D.VRecord{"arguments", args, D.VRecord{"code", D.VText{cod}, D.VRecord{"credential", D.VText{cred}, D.VRecord{_, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(P.Request{cred, cod, args, pi}) : D.Value}
  {==}

law envelope_accepted_reconstructs_exactly:
  for +v: D.Value
  for +r: P.Request
  for obtained: {Q.form(v) == Some{r} : Maybe<&2, P.Request>}
  {v == P.request_value(r) : D.Value}
def envelope_accepted_reconstructs_exactly(v, r, obtained):
  match v:
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}}:
      F.combined_pair(
        {D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(r) : D.Value},
        {String.eq(n0, "arguments") && String.eq(n1, "code") && String.eq(n2, "credential") && String.eq(n3, "proof") == True{} : Bool},
        {r == P.Request{cred, cod, args, pi} : P.Request},
        choose_success(String.eq(n0, "arguments") && String.eq(n1, "code") && String.eq(n2, "credential") && String.eq(n3, "proof"), P.Request{cred, cod, args, pi}, r, obtained),
        names => equality =>
          %Equal.sym(P.Request, r, P.Request{cred, cod, args, pi}, equality) :
            {D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecordEmpty{}}}}} == P.request_value(_) : D.Value}
          names_reconstruct(n0, n1, n2, n3, args, cod, cred, pi, names))
    case D.VAbsent{}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VBool{zb}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VInt{za, zb}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VText{zs}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VListEmpty{}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VList{zh, zt}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecordEmpty{}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VAbsent{}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VBool{zb}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VInt{za, zb}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VText{zs}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VListEmpty{}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VList{zh, zt}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecordEmpty{}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VAbsent{}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VBool{zb}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VInt{za, zb}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VListEmpty{}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VList{zh, zt}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VRecordEmpty{}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VRecord{zn, zv, zr}, rest2}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VAbsent{}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VBool{zb}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VInt{za, zb}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VText{zs}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VListEmpty{}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VList{zh, zt}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecordEmpty{}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VAbsent{}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VBool{zb}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VInt{za, zb}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VListEmpty{}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VList{zh, zt}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VRecordEmpty{}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VRecord{zn, zv, zr}, rest3}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VAbsent{}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VBool{zb}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VInt{za, zb}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VText{zs}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VListEmpty{}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VList{zh, zt}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecordEmpty{}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VAbsent{}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VBool{zb}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VInt{za, zb}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VListEmpty{}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VList{zh, zt}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VRecordEmpty{}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VRecord{zn, zv, zr}, bottom}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VAbsent{}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VBool{zb}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VInt{za, zb}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VText{zs}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VListEmpty{}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VList{zh, zt}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))
    case D.VRecord{n0, args, D.VRecord{n1, D.VText{cod}, D.VRecord{n2, D.VText{cred}, D.VRecord{n3, D.VText{pi}, D.VRecord{zn, zv, zr}}}}}:
      L.ex_false({v == P.request_value(r) : D.Value}, F.none_negative_some(P.Request, r, obtained))

def validate_success(b: Bool, -q: Maybe<&2, P.Request>, +r: P.Request,
  obtained: {Q.validate(b, q) == Some{r} : Maybe<&2, P.Request>}) ->
  L.E<{b == True{} : Bool}, {q == Some{r} : Maybe<&2, P.Request>}>:
  match b:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, {q == Some{r} : Maybe<&2, P.Request>}>, F.none_negative_some(P.Request, r, obtained))
    case True{}:
      L.Both{{==}, obtained}

law extract_preserves_value_and_is_valid:
  for +v: D.Value
  for +r: P.Request
  for obtained: {Q.extract(v) == Some{r} : Maybe<&2, P.Request>}
  L.E<{D.value_valid(v) == True{} : Bool}, {v == P.request_value(r) : D.Value}>
def extract_preserves_value_and_is_valid(v, r, obtained):
  F.combined_pair(L.E<{D.value_valid(v) == True{} : Bool}, {v == P.request_value(r) : D.Value}>,
    {D.value_valid(v) == True{} : Bool}, {Q.form(v) == Some{r} : Maybe<&2, P.Request>},
    validate_success(D.value_valid(v), Q.form(v), r, obtained),
    valid => form => L.Both{valid, envelope_accepted_reconstructs_exactly(v, r, form)})
