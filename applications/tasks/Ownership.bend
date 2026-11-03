# Authorized operations preserve task ownership.
import Base
import ./Data.bend as D
import ./Logic.bend as L
import ./Policy.bend as Policy
import ./Orders.bend as O

def Preserves(+ctx: D.Context, r: D.ResultOp) -> Type:
  match r:
    case D.FailureData{}: Unit
    case D.Observed{o}: Unit
    case D.Changed{w}:
      L.E<Policy.Owners(w), {D.context_present(w, ctx) == True{} : Bool}>

def impossible(-A: Type, h: {False{} == True{} : Bool}) -> A:
  L.ex_false(A, (%h : Bool.pick(Type, _, Empty, Unit) Unit{}))

def present_exists(m: Maybe<&2, D.Row>, -ctx: D.Context,
  h: {D.context_found(m, ctx) == True{} : Bool}) ->
  {D.exists_row(m) == True{} : Bool}:
  match m:
    case None{}:
      impossible({False{} == True{} : Bool}, h)
    case Some{l}:
      {==}

def insert_step(a: Bool, b: Bool, +us: List<&2, D.Row>, +name: String,
  +new: D.Row, +l: D.Row, +ls: List<&2, D.Row>,
  hn: Policy.Owner(us, name, new), hl: Policy.Owner(us, name, l),
  ht: Policy.Rows(us, name, ls),
  hr: Policy.Rows(us, name, D.insert_row(ls, new))) ->
  Policy.Rows(us, name, Bool.pick(List<&2, D.Row>, a, new <> l <> ls,
    Bool.pick(List<&2, D.Row>, b, new <> ls, l <> D.insert_row(ls, new)))):
  match a b:
    case True{} _:
      Policy.Both{hn, Policy.Both{hl, ht}}
    case False{} True{}:
      Policy.Both{hn, ht}
    case False{} False{}:
      Policy.Both{hl, hr}

def insert_preserves(+us: List<&2, D.Row>, +name: String,
  ls: List<&2, D.Row>, +new: D.Row,
  +hn: Policy.Owner(us, name, new), h: Policy.Rows(us, name, ls)) ->
  Policy.Rows(us, name, D.insert_row(ls, new)):
  match ls:
    case Nil{}:
      Policy.Both{hn, Unit{}}
    case Con{+l, +rest}:
      Policy.Both{+hl, +ht} = h
      insert_step(String.is_lt(D.row_key(new), D.row_key(l)),
        String.eq(D.row_key(new), D.row_key(l)), us, name, new, l, rest,
        hn, hl, ht, insert_preserves(us, name, rest, new, hn, ht))

def remove_step(b: Bool, +us: List<&2, D.Row>, +name: String,
  +l: D.Row, +ls: List<&2, D.Row>,
  hl: Policy.Owner(us, name, l), ht: Policy.Rows(us, name, ls)) ->
  Policy.Rows(us, name, Bool.pick(List<&2, D.Row>, b, ls, l <> ls)):
  match b:
    case False{}: Policy.Both{hl, ht}
    case True{}: ht

def remove_preserves(+us: List<&2, D.Row>, +name: String,
  ls: List<&2, D.Row>, +key: String, h: Policy.Rows(us, name, ls)) ->
  Policy.Rows(us, name, D.remove_row(ls, key)):
  match ls:
    case Nil{}: Unit{}
    case Con{+l, +rest}:
      Policy.Both{hl, ht} = h
      remove_step(String.eq(D.row_key(l), key), us, name, l,
        D.remove_row(rest, key), hl, remove_preserves(us, name, rest, key, ht))

def swap_step(b: Bool, +us: List<&2, D.Row>, +n: String, +name: String,
  +ls: List<&2, D.Row>, +new: List<&2, D.Row>, +rest: List<&2, D.Table>,
  eq: {String.eq(n, name) == b : Bool}, hl: Policy.Rows(us, n, ls),
  hn: Policy.Rows(us, name, new), ht: Policy.Tables(us, rest)) ->
  Policy.Tables(us, Bool.pick(D.Table, b, D.Table{n, new}, D.Table{n, ls}) <> rest):
  match b:
    case False{}:
      Policy.Both{hl, ht}
    case True{}:
      Policy.Both{(%Equal.sym(String, n, name, O.string_equal(n, name, eq)) :
        Policy.Rows(us, _, new) hn), ht}

def swap_preserves(+us: List<&2, D.Row>, ts: List<&2, D.Table>,
  +name: String, +new: List<&2, D.Row>,
  +hn: Policy.Rows(us, name, new), h: Policy.Tables(us, ts)) ->
  Policy.Tables(us, D.swap_table(ts, name, new)):
  match ts:
    case Nil{}: Unit{}
    case Con{D.Table{+n, +ls}, +rest}:
      Policy.Both{hl, ht} = h
      swap_step(String.eq(n, name), us, n, name, ls, new,
        D.swap_table(rest, name, new), {==}, hl, hn,
        swap_preserves(us, rest, name, new, hn, ht))

def Found(+us: List<&2, D.Row>, +name: String,
  m: Maybe<&2, List<&2, D.Row>>) -> Data:
  match m:
    case None{}: Unit
    case Some{ls}: Policy.Rows(us, name, ls)

def find_step(b: Bool, +us: List<&2, D.Row>, +n: String, +name: String,
  +ls: List<&2, D.Row>, +rest: Maybe<&2, D.Table>,
  eq: {String.eq(n, name) == b : Bool}, hl: Policy.Rows(us, n, ls),
  ht: Found(us, name, D.rows_table(rest))) ->
  Found(us, name, D.rows_table(Bool.pick(Maybe<&2, D.Table>, b,
    Some{D.Table{n, ls}}, rest))):
  match b:
    case False{}: ht
    case True{}:
      %O.string_equal(n, name, eq) : Policy.Rows(us, _, ls)
      hl

def find_preserves(+us: List<&2, D.Row>, ts: List<&2, D.Table>,
  +name: String, h: Policy.Tables(us, ts)) ->
  Found(us, name, D.rows_table(D.find_table(ts, name))):
  match ts:
    case Nil{}: Unit{}
    case Con{D.Table{+n, +ls}, +rest}:
      Policy.Both{hl, ht} = h
      find_step(String.eq(n, name), us, n, name, ls, D.find_table(rest, name),
        {==}, hl, find_preserves(us, rest, name, ht))

def users(s: D.State) -> List<&2, D.Row>:
  D.State{ts, us} = s
  us

def collection_preserves(+ctx: D.Context, +s: D.State, +name: String,
  +ls: List<&2, D.Row>, h: Policy.Owners(s), hn: Policy.Rows(users(s), name, ls),
  aut: {D.context_present(s, ctx) == True{} : Bool}) ->
  Preserves(ctx, D.Changed{D.swap_collection(D.Application{name}, s, ls)}):
  D.State{ts, us} = s
  L.Both{swap_preserves(us, ts, name, ls, hn, h), aut}

def write_preserves(ok: Bool, +ctx: D.Context, +s: D.State, +name: String,
  +ls: List<&2, D.Row>, h: Policy.Owners(s), hn: Policy.Rows(users(s), name, ls),
  aut: {D.context_present(s, ctx) == True{} : Bool}) ->
  Preserves(ctx, D.write_se(ok, D.Application{name}, s, ls)):
  match ok:
    case False{}: Unit{}
    case True{}: collection_preserves(ctx, s, name, ls, h, hn, aut)

def cell_preserves(+ctx: D.Context, v: Maybe<&2, D.Value>) ->
  Preserves(ctx, D.result_cell(v)):
  match v:
    case None{}: Unit{}
    case Some{x}: Unit{}

def read_row_preserves(+ctx: D.Context, m: Maybe<&2, D.Row>, +name: String) ->
  Preserves(ctx, D.read_row(m, name)):
  match m:
    case None{}: Unit{}
    case Some{D.Row{k, fs}}: cell_preserves(ctx, D.find_field(fs, name))

def read_preserves(+ctx: D.Context, c: Maybe<&2, D.Column>,
  +m: Maybe<&2, D.Row>, +name: String) -> Preserves(ctx, D.read_column(c, m, name)):
  match c:
    case None{}: Unit{}
    case Some{x}: read_row_preserves(ctx, m, name)

def Resolved(+us: List<&2, D.Row>, +name: String,
  r: Maybe<&2, D.Resolved>) -> Data:
  match r:
    case None{}: Unit
    case Some{D.Resolved{e, ls}}: Policy.Rows(us, name, ls)

def resolve_preserves(+us: List<&2, D.Row>, +name: String,
  e: Maybe<&2, D.SchemaTable>, ls: Maybe<&2, List<&2, D.Row>>,
  h: Found(us, name, ls)) -> Resolved(us, name, D.resolve_parts(e, ls)):
  match e ls:
    case Some{x} Some{ys}: h
    case Some{x} None{}: Unit{}
    case None{} _: Unit{}

def rows_resolved(+s: D.State, +e: D.Schema, +name: String,
  h: Policy.Owners(s)) ->
  Resolved(users(s), name, D.resolve_parts(
    D.schema_collection(D.Application{name}, e), D.rows_collection(D.Application{name}, s))):
  D.State{ts, us} = s
  resolve_preserves(us, name, D.schema_collection(D.Application{name}, e),
    D.rows_table(D.find_table(ts, name)), find_preserves(us, ts, name, h))

def new_owner(+s: D.State, +ctx: D.Context, +name: String,
  +k: String, +fs: List<&2, D.Field>,
  aut: {D.context_present(s, ctx) == True{} : Bool},
  p: Policy.Allowed(ctx, D.DefineRow{D.Application{name}, k, fs})) ->
  Policy.Owner(users(s), name, D.Row{k, fs}):
  D.State{ts, us} = s
  D.Context{+id, +kind} = ctx
  Policy.Both{eq, owner} = p
  %Equal.sym(String, name, id, eq) : Policy.Owner(us, _, D.Row{k, fs})
  Policy.Both{owner, present_exists(D.find_row(us, id), D.Context{id, kind}, aut)}

def Resolution(+s: D.State, c: D.Collection,
  r: Maybe<&2, D.Resolved>) -> Data:
  match c:
    case D.Users{}: Unit
    case D.Application{name}: Resolved(users(s), name, r)

def forbidden(-ctx: D.Context, -r: D.ResultOp,
  p: {False{} == True{} : Bool}) -> Preserves(ctx, r):
  impossible(Preserves(ctx, r), p)

def resolved_preserves(+s: D.State, +ctx: D.Context, op: D.Operation,
  r: Maybe<&2, D.Resolved>, +h: Policy.Owners(s),
  +aut: {D.context_present(s, ctx) == True{} : Bool},
  p: Policy.Allowed(ctx, op), hr: Resolution(s, D.collection_op(op), r)) ->
  Preserves(ctx, D.operate_resolved(op, r, s)):
  D.Context{+id, +kind} = ctx
  match op r:
    case D.ReadCell{D.Application{name}, k, +n} Some{D.Resolved{D.SchemaTable{en, pk, cs}, ls}}:
      read_preserves(D.Context{id, kind}, D.find_column(cs, n), D.find_row(ls, k), n)
    case D.ViewExistence{D.Application{name}, k} Some{D.Resolved{e, ls}}: Unit{}
    case D.CountRows{D.Application{name}} Some{D.Resolved{e, ls}}: Unit{}
    case D.EnumerateKeys{D.Application{name}} Some{D.Resolved{e, ls}}: Unit{}
    case D.DefineRow{D.Application{+name}, +k, +fs} Some{D.Resolved{+e, +ls}}:
      write_preserves(D.row_is_valid(e, D.Row{k, fs}), D.Context{id, kind}, s, name,
        D.insert_row(ls, D.Row{k, fs}), h,
        insert_preserves(users(s), name, ls, D.Row{k, fs},
          new_owner(s, D.Context{id, kind}, name, k, fs, aut, p), hr), aut)
    case D.RemoveRow{D.Application{+name}, +k} Some{D.Resolved{e, +ls}}:
      collection_preserves(D.Context{id, kind}, s, name, D.remove_row(ls, k), h,
        remove_preserves(users(s), name, ls, k, hr), aut)
    case D.ReadCell{D.Users{}, k, n} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.ReadCell{D.Users{}, k, n}, Some{rr}, s), p)
    case D.ViewExistence{D.Users{}, k} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.ViewExistence{D.Users{}, k}, Some{rr}, s), p)
    case D.CountRows{D.Users{}} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.CountRows{D.Users{}}, Some{rr}, s), p)
    case D.EnumerateKeys{D.Users{}} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.EnumerateKeys{D.Users{}}, Some{rr}, s), p)
    case D.DefineRow{D.Users{}, k, fs} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.DefineRow{D.Users{}, k, fs}, Some{rr}, s), p)
    case D.RemoveRow{D.Users{}, k} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.RemoveRow{D.Users{}, k}, Some{rr}, s), p)
    case D.DefineColumn{c, k, n, v} Some{rr}:
      forbidden(D.Context{id, kind}, D.operate_resolved(D.DefineColumn{c, k, n, v}, Some{rr}, s), p)
    case _ None{}: Unit{}

def resolution_preserves(+s: D.State, +e: D.Schema,
  +c: D.Collection, h: Policy.Owners(s)) ->
  Resolution(s, c, D.resolve_parts(D.schema_collection(c, e), D.rows_collection(c, s))):
  match c:
    case D.Users{}: Unit{}
    case D.Application{name}: rows_resolved(s, e, name, h)

def address_preserves(ok: Bool, +e: D.Schema, +s: D.State,
  +ctx: D.Context, +op: D.Operation, +h: Policy.Owners(s),
  aut: {D.context_present(s, ctx) == True{} : Bool}, p: Policy.Allowed(ctx, op)) ->
  Preserves(ctx, D.operate_address(ok, e, s, op)):
  match ok:
    case False{}: Unit{}
    case True{}:
      resolved_preserves(s, ctx, op, D.resolve_parts(D.schema_collection(D.collection_op(op), e),
        D.rows_collection(D.collection_op(op), s)), h, aut, p, resolution_preserves(s, e, D.collection_op(op), h))

law operation_preserves:
  for +e: D.Schema
  for +s: D.State
  for +ctx: D.Context
  for +op: D.Operation
  for +h: Policy.Owners(s)
  for aut: {D.context_present(s, ctx) == True{} : Bool}
  for p: Policy.Allowed(ctx, op)
  Preserves(ctx, D.operate(e, s, op))
def operation_preserves(e, s, ctx, op, h, aut, p):
  address_preserves(D.address_op_valid(op), e, s, ctx, op, h, aut, p)
