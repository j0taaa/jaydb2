# The identity required by the certificate is derived from the published registry.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./Orders.bend as O

def validity_tail(+h: D.Row, +t: List<&2, D.Row>, +e: D.SchemaTable,
  v: {D.rows_valid_cases(Con{h, t}, e) == True{} : Bool}) ->
  L.E<{D.rows_later(t, D.row_key(h)) == True{} : Bool},
    {D.rows_valid_cases(t, e) == True{} : Bool}>:
  D.Row{k, fs} = h
  F.combined_pair(
    L.E<{D.rows_later(t, k) == True{} : Bool}, {D.rows_valid_cases(t, e) == True{} : Bool}>,
    {D.row_is_valid(e, D.Row{k, fs}) && D.rows_later(t, k) == True{} : Bool},
    {D.rows_valid_cases(t, e) == True{} : Bool},
    F.and_boolean_separate(D.row_is_valid(e, D.Row{k, fs}) && D.rows_later(t, k), D.rows_valid_cases(t, e), v),
    first => tail => L.Both{F.and_boolean_right(D.row_is_valid(e, D.Row{k, fs}), D.rows_later(t, k), first), tail})

def above_cases(b: Bool, +k: String, +fs: List<&2, D.Field>,
  -t: List<&2, D.Row>, -cred: String, +ctx: D.Context, +low: String,
  less: {String.is_lt(low, k) == True{} : Bool},
  rec: {D.authenticate_rows(t, cred) == Some{ctx} : Maybe<&2, D.Context>} ->
    {String.is_lt(k, D.context_id(ctx)) == True{} : Bool},
  aut: {Bool.pick(Maybe<&2, D.Context>, b,
    Some{D.context_row(D.Row{k, fs})}, D.authenticate_rows(t, cred)) ==
      Some{ctx} : Maybe<&2, D.Context>}) ->
  {String.is_lt(low, D.context_id(ctx)) == True{} : Bool}:
  match b:
    case False{}:
      O.string_lt_trans(low, k, D.context_id(ctx), less, rec(aut))
    case True{}:
      %F.some_injective(D.Context, D.context_row(D.Row{k, fs}), ctx, aut) :
        {String.is_lt(low, D.context_id(_)) == True{} : Bool}
      less

law authenticated_above:
  for xs: List<&2, D.Row>
  for +e: D.SchemaTable
  for +cred: String
  for +ctx: D.Context
  for +low: String
  for v: {D.rows_valid_cases(xs, e) == True{} : Bool}
  for d: {D.rows_later(xs, low) == True{} : Bool}
  for aut: {D.authenticate_rows(xs, cred) == Some{ctx} : Maybe<&2, D.Context>}
  {String.is_lt(low, D.context_id(ctx)) == True{} : Bool}
def authenticated_above(xs, e, cred, ctx, low, v, d, aut):
  match xs:
    case Nil{}:
      L.ex_false({String.is_lt(low, D.context_id(ctx)) == True{} : Bool},
        F.none_negative_some(D.Context, ctx, aut))
    case Con{D.Row{+k, +fs}, +t}:
      F.combined_pair({String.is_lt(low, D.context_id(ctx)) == True{} : Bool},
        {D.rows_later(t, k) == True{} : Bool}, {D.rows_valid_cases(t, e) == True{} : Bool},
        validity_tail(D.Row{k, fs}, t, e, v),
        dt => vt => above_cases(String.eq(D.credential_row(D.Row{k, fs}), cred), k, fs, t,
          cred, ctx, low, d, h => authenticated_above(t, e, cred, ctx, k, vt, dt, h), aut))

law context_refl:
  for c: D.Context
  {D.context_equal(c, c) == True{} : Bool}
def context_refl(c):
  match c:
    case D.Context{id, kind}:
      F.and_boolean_intro(String.eq(id, id), String.eq(kind, kind),
        O.string_eq_refl(id), O.string_eq_refl(kind))

def present_cases(b: Bool, +k: String, +fs: List<&2, D.Field>,
  +t: List<&2, D.Row>, +cred: String, +ctx: D.Context,
  rec: {D.authenticate_rows(t, cred) == Some{ctx} : Maybe<&2, D.Context>} ->
    L.E<{D.context_found(D.find_row(t, D.context_id(ctx)), ctx) == True{} : Bool},
      {String.is_lt(k, D.context_id(ctx)) == True{} : Bool}>,
  aut: {Bool.pick(Maybe<&2, D.Context>, b,
    Some{D.context_row(D.Row{k, fs})}, D.authenticate_rows(t, cred)) ==
      Some{ctx} : Maybe<&2, D.Context>}) ->
  {D.context_found(D.find_row(Con{D.Row{k, fs}, t}, D.context_id(ctx)), ctx) == True{} : Bool}:
  match b:
    case False{}:
      F.combined_pair(
        {D.context_found(D.find_row(Con{D.Row{k, fs}, t}, D.context_id(ctx)), ctx) == True{} : Bool},
        {D.context_found(D.find_row(t, D.context_id(ctx)), ctx) == True{} : Bool},
        {String.is_lt(k, D.context_id(ctx)) == True{} : Bool}, rec(aut),
        present => less =>
          %Equal.sym(Bool, String.eq(k, D.context_id(ctx)), False{}, O.string_lt_neq(k, D.context_id(ctx), less)) :
            {D.context_found(Bool.pick(Maybe<&2, D.Row>, _, Some{D.Row{k, fs}}, D.find_row(t, D.context_id(ctx))), ctx) == True{} : Bool}
          present)
    case True{}:
      %F.some_injective(D.Context, D.context_row(D.Row{k, fs}), ctx, aut) :
        {D.context_found(D.find_row(Con{D.Row{k, fs}, t}, D.context_id(_)), _) == True{} : Bool}
      %Equal.sym(Bool, String.eq(k, k), True{}, O.string_eq_refl(k)) :
        {D.context_found(Bool.pick(Maybe<&2, D.Row>, _, Some{D.Row{k, fs}},
          D.find_row(t, k)), D.context_row(D.Row{k, fs})) == True{} : Bool}
      context_refl(D.context_row(D.Row{k, fs}))

# The general proof is declared before its constituent helpers.
law authenticated_present:
  for +xs: List<&2, D.Row>
  for +e: D.SchemaTable
  for +cred: String
  for +ctx: D.Context
  for +v: {D.rows_valid_cases(xs, e) == True{} : Bool}
  for +aut: {D.authenticate_rows(xs, cred) == Some{ctx} : Maybe<&2, D.Context>}
  {D.context_found(D.find_row(xs, D.context_id(ctx)), ctx) == True{} : Bool}

def authenticated_present(xs, e, cred, ctx, v, aut):
  match xs:
    case Nil{}:
      L.ex_false({D.context_found(D.find_row(Nil{}, D.context_id(ctx)), ctx) == True{} : Bool},
        F.none_negative_some(D.Context, ctx, aut))
    case Con{D.Row{k, fs}, t}:
      F.combined_pair(
        {D.context_found(D.find_row(Con{D.Row{k, fs}, t}, D.context_id(ctx)), ctx) == True{} : Bool},
        {D.rows_later(t, k) == True{} : Bool}, {D.rows_valid_cases(t, e) == True{} : Bool},
        validity_tail(D.Row{k, fs}, t, e, v),
        dt => +vt => present_cases(String.eq(D.credential_row(D.Row{k, fs}), cred), k, fs, t, cred, ctx,
          +h => L.Both{authenticated_present(t, e, cred, ctx, vt, h),
            authenticated_above(t, e, cred, ctx, k, vt, dt, h)}, aut))

law authentication_implies_context_present:
  for +e: D.Schema
  for +s: D.State
  for cred: String
  for ctx: D.Context
  for structure: {D.structure(e, s) == True{} : Bool}
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  {D.context_present(s, ctx) == True{} : Bool}
def authentication_implies_context_present(e, s, cred, ctx, structure, aut):
  match e s:
    case D.Schema{es} D.State{ts, us}:
      without_credentials = F.and_boolean_left(
        D.tables_valid_cases(es, ts) && D.rows_valid_cases(us, D.schema_users()),
        D.credentials_valid_cases(us), structure)
      rows = F.and_boolean_right(D.tables_valid_cases(es, ts),
        D.rows_valid_cases(us, D.schema_users()), without_credentials)
      authenticated_present(us, D.schema_users(), cred, ctx, rows, aut)

law compare_combined_empty:
  for s: String
  {String.eq(s, "") == String.is_empty(s) : Bool}
def compare_combined_empty(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{n}, t}:
      {==}

law registry_valid_negative_authenticates_empty:
  for xs: List<&2, D.Row>
  for +valid: {D.credentials_valid_cases(xs) == True{} : Bool}
  {D.authenticate_rows(xs, "") == None{} : Maybe<&2, D.Context>}
def registry_valid_negative_authenticates_empty(xs, valid):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +cred = D.credential_row(h)
      negative_empty = F.and_boolean_left(Bool.not(String.is_empty(cred)), D.credential_different(t, cred),
        F.and_boolean_left(Bool.not(String.is_empty(cred)) && D.credential_different(t, cred),
          D.credentials_valid_cases(t), valid))
      tail = F.and_boolean_right(Bool.not(String.is_empty(cred)) && D.credential_different(t, cred),
        D.credentials_valid_cases(t), valid)
      %Equal.sym(Bool, String.eq(cred, ""), False{},
        Equal.trans(Bool, String.eq(cred, ""), String.is_empty(cred), False{},
          compare_combined_empty(cred), F.negation_true(String.is_empty(cred), negative_empty))) :
          {Bool.pick(Maybe<&2, D.Context>, _, Some{D.context_row(h)}, D.authenticate_rows(t, "")) == None{} : Maybe<&2, D.Context>}
      registry_valid_negative_authenticates_empty(t, tail)

law state_publishable_negative_authenticates_empty:
  for e: D.Schema
  for s: D.State
  for structure: {D.structure(e, s) == True{} : Bool}
  {D.authenticate(s, "") == None{} : Maybe<&2, D.Context>}
def state_publishable_negative_authenticates_empty(e, s, structure):
  match e s:
    case D.Schema{es} D.State{ts, +us}:
      registry_valid_negative_authenticates_empty(us,
        F.and_boolean_right(D.tables_valid_cases(es, ts) && D.rows_valid_cases(us, D.schema_users()),
          D.credentials_valid_cases(us), structure))
