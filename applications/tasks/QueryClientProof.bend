import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Instance.bend as I
import ./Bindings.bend as B

import ./Query.bend as Q
import ./Action.bend as A
import ./Task.bend as Task
import ./Mutation.bend as M
import ./Laws.bend as G
import ./Value.bend as V
import ./ReadProgram.bend as RP

def read_depth(xs: List<&2, String>, n: Nat) -> Nat:
  G.depth(xs, n)

def read_permissions(xs: List<&2, String>, +id: String, +kind: String, +key: String) ->
  G.ReadPermissions(~P.Allowed, D.Context{id, kind}, D.Application{id}, key, xs):
  match xs:
    case Nil{}: Unit{}
    case Con{name, rest}: L.Both{{==}, read_permissions(rest, id, kind, key)}

# Instantiate the library template with ACTUAL administrator permissions.
def reads_safe(+xs: List<&2, String>, +n: Nat, +id: String, +kind: String, +key: String,
  -done: Q.Selection -> S.Action, h: @result: Q.Selection -> H.Safe(n, D.Context{id, kind}, done(result))) ->
  H.Safe(read_depth(xs, n), D.Context{id, kind}, Q.read_fields(D.Application{id}, key, xs, done)):
  G.reads(~P.Allowed, xs, n, D.Context{id, kind}, D.Application{id}, key, done,
    read_permissions(xs, id, kind, key), h)

def projection_safe(+n: Nat, +ctx: D.Context, -done: Maybe<&2, D.Value> -> S.Action,
  h: @item: Maybe<&2, D.Value> -> H.Safe(Succ{n}, ctx, done(item)), p: Client.Projection) ->
  H.Safe(Succ{n}, ctx, Client.finish_projection(done, p)):
  match p:
    case Client.Keep{value}: h(Some{value})
    case Client.Skip{}: h(None{})
    case Client.InvalidProjection{}: Unit{}

def visit_safe(+n: Nat, +id: String, +kind: String, key: String,
  -done: Maybe<&2, D.Value> -> S.Action,
  h: @item: Maybe<&2, D.Value> -> H.Safe(Succ{n}, D.Context{id, kind}, done(item))) ->
  H.Safe(Succ{Succ{Succ{n}}}, D.Context{id, kind}, Client.visit(id, key, done)):
  reads_safe(["completed", "title"], Succ{n}, id, kind, key, Client.projected(done),
    result => projection_safe(n, D.Context{id, kind}, done, h, Client.projection(result)))

def written_safe(+n: Nat, +ctx: D.Context, -a: S.Action,
  h: H.Safe(Succ{n}, ctx, a), r: S.Return) -> H.Safe(Succ{n}, ctx, A.written(a, r)):
  match r:
    case S.UnitValue{}: h
    case S.Datum{obs}: Unit{}

def saved_safe(n: Nat, ctx: D.Context, cancel: Bool, key: String) ->
  H.Safe(Succ{n}, ctx, Task.saved(cancel, key)):
  match cancel:
    case False{}: Unit{}
    case True{}: Unit{}

def inserted_safe(+id: String, +kind: String, +key: String, r: S.Return) ->
  H.Safe(4n, D.Context{id, kind}, M.inserted(D.Application{id}, D.Row{key, Task.fields(id, key, "Once", False{})}, b => S.Finish{D.VBool{b}}, r)):
  match r:
    case S.Datum{D.Existence{False{}}}:
      L.Both{P.Both{{==}, {==}}, r => written_safe(2n, D.Context{id, kind}, S.Finish{D.VBool{True{}}}, Unit{}, r)}
    case S.Datum{D.Existence{True{}}}: Unit{}
    case S.Datum{D.RowAbsent{}}: Unit{}
    case S.Datum{D.Cell{v}}: Unit{}
    case S.Datum{D.Count{n}}: Unit{}
    case S.Datum{D.Keys{xs}}: Unit{}
    case S.UnitValue{}: Unit{}

def replace_choice_safe(b: Bool, +id: String, +kind: String, +key: String) ->
  H.Safe(4n, D.Context{id, kind}, M.replace_choice(b, D.Application{id}, key, Task.fields(id, key, "Replaced", True{}), b => S.Finish{D.VBool{b}})):
  match b:
    case False{}: Unit{}
    case True{}: L.Both{P.Both{{==}, {==}}, r => written_safe(2n, D.Context{id, kind}, S.Finish{D.VBool{True{}}}, Unit{}, r)}

def replace_safe(+id: String, +kind: String, +key: String, r: S.Return) ->
  H.Safe(4n, D.Context{id, kind}, M.replace_received(~Client.is_open, D.Application{id}, D.Row{key, Task.fields(id, key, "Replaced", True{})}, b => S.Finish{D.VBool{b}}, r)):
  match r:
    case S.Datum{obs}: replace_choice_safe(Client.is_open(obs), id, kind, key)
    case S.UnitValue{}: Unit{}

def cas_safe(+id: String, +kind: String, +key: String, expected: Bool, r: S.Return) ->
  H.Safe(4n, D.Context{id, kind}, M.cas_received(D.Application{id}, D.Row{key, Task.fields(id, key, "Replaced", True{})}, D.VBool{expected}, b => S.Finish{D.VBool{b}}, r)):
  match r:
    case S.Datum{D.Cell{v}}: replace_choice_safe(V.equal(v, D.VBool{expected}), id, kind, key)
    case S.Datum{D.RowAbsent{}}: Unit{}
    case S.Datum{D.Existence{b}}: Unit{}
    case S.Datum{D.Count{n}}: Unit{}
    case S.Datum{D.Keys{xs}}: Unit{}
    case S.UnitValue{}: Unit{}

def selected_safe(n: Nat, ctx: D.Context, result: Q.Selection) -> H.Safe(Succ{n}, ctx, RP.selected(result)):
  match result:
    case Q.Selected{v}: Unit{}
    case Q.MissingRow{}: Unit{}
    case Q.InvalidFields{}: Unit{}
    case Q.UnexpectedReturn{}: Unit{}

def command_safe(ctx: D.Context, p: Client.Command) -> H.Safe(5n, ctx, Client.command(D.context_id(ctx), p)):
  match ctx p:
    case D.Context{+id, +kind} Client.Open{a, b}:
      visit_safe(2n, id, kind, a, +item =>
        Q.filter_map(~String, ~Client.visit, id, [b], tail => S.Finish{Q.include(item, tail)}),
        item => visit_safe(0n, id, kind, b,
          tail => S.Finish{Q.include(item, Q.include(tail, D.VListEmpty{}))}, tail => Unit{}))
    case D.Context{+id, +kind} Client.Pair{+a, +b, +cancel}:
      G.write_rows(~P.Allowed, [D.Row{a, Task.fields(id, a, "First", False{})},
        D.Row{b, Task.fields(id, b, "Second", True{})}], 2n, D.Context{id, kind}, D.Application{id}, Task.saved(cancel, a),
        L.Both{P.Both{{==}, {==}}, L.Both{P.Both{{==}, {==}}, Unit{}}}, saved_safe(2n, D.Context{id, kind}, cancel, a))
    case D.Context{+id, +kind} Client.Inspect{key}:
      reads_safe(["completed", "title"], 3n, id, kind, key, RP.selected,
        result => selected_safe(2n, D.Context{id, kind}, result))
    case D.Context{+id, +kind} Client.Insert{+key}: L.Both{{==}, r => inserted_safe(id, kind, key, r)}
    case D.Context{+id, +kind} Client.Replace{+key}: L.Both{{==}, r => replace_safe(id, kind, key, r)}
    case D.Context{+id, +kind} Client.Cas{+key, expected}: L.Both{{==}, r => cas_safe(id, kind, key, expected, r)}
    case D.Context{+id, +kind} Client.Drop{a, b}:
      L.Both{{==}, r => written_safe(3n, D.Context{id, kind},
        M.remove_rows(D.Application{id}, [b], S.Finish{D.VAbsent{}}),
        L.Both{{==}, r => written_safe(2n, D.Context{id, kind}, S.Finish{D.VAbsent{}}, Unit{}, r)}, r)}
    case D.Context{id, kind} Client.Invalid{}: Unit{}

def program_safe(+ctx: D.Context, args: D.Value) -> H.Safe(5n, ctx, S.start(Client.program(), ctx, args)):
  command_safe(ctx, Client.analyze(args))

def owners_initial(-s: D.State, valid: R.Valid(C.config(), s)) -> P.Owners(s):
  match valid:
    case L.Both{structure, L.Both{owners, remaining}}: owners

# The parameterized lemma avoids reevaluating concrete argument reification
# throughout the proof; the target remains the original certificate.
def certify(+ctx: D.Context, +args: D.Value, -code: String, +s: D.State,
  valid: R.Valid(C.config(), s), identity: {D.context_present(s, ctx) == True{} : Bool}, +n: Nat) ->
  R.SafetyTrace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.config(), s, ctx, code, args):
  H.execution_trace(S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), C.environment(), s, ctx, code, args,
    H.rewind(ctx, S.execute(n, Client.program(), C.schema(), s, ctx, args),
      T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
      Equal.sym(S.Trace, T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
        S.execute(n, Client.program(), C.schema(), s, ctx, args),
        T.reference(n, S.start(Client.program(), ctx, args), C.schema(), s)),
      H.safe(5n, n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{},
        program_safe(ctx, args), P.Both{owners_initial(s, valid), P.Both{identity, Unit{}}})))

def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(5n, Client.program(), C.schema(), s, ctx, args,
    H.finite(5n, S.start(Client.program(), ctx, args), ctx, program_safe(ctx, args)))
