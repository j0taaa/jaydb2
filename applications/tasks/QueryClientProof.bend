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

def read_depth(xs: List<&2, String>, n: Nat) -> Nat:
  match xs:
    case Nil{}: n
    case Con{x, rest}: Succ{read_depth(rest, n)}

# Actual ReadCell permission is proved per field, not assumed for a transaction.
def reads_safe(xs: List<&2, String>, +n: Nat, +id: String, +kind: String, +key: String,
  -done: Q.Selection -> S.Action, h: @result: Q.Selection -> H.Safe(n, D.Context{id, kind}, done(result))) ->
  H.Safe(read_depth(xs, n), D.Context{id, kind}, Q.read_fields(D.Application{id}, key, xs, done)):
  match xs:
    case Nil{}: h(Q.Selected{D.VRecordEmpty{}})
    case Con{+name, +rest}:
      L.Both{{==}, +r => reads_safe(rest, n, id, kind, key,
        result => done(Q.combine(name, r, result)),
        result => h(Q.combine(name, r, result)))}

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

def command_safe(ctx: D.Context, p: Client.Command) -> H.Safe(5n, ctx, Client.command(D.context_id(ctx), p)):
  match ctx p:
    case D.Context{+id, +kind} Client.Open{a, b}:
      visit_safe(2n, id, kind, a, +item =>
        Q.filter_map(~String, ~Client.visit, id, [b], tail => S.Finish{Q.include(item, tail)}),
        item => visit_safe(0n, id, kind, b,
          tail => S.Finish{Q.include(item, Q.include(tail, D.VListEmpty{}))}, tail => Unit{}))
    case D.Context{+id, +kind} Client.Pair{+a, b, +cancel}:
      L.Both{P.Both{{==}, {==}}, r => written_safe(3n, D.Context{id, kind},
        A.define_rows(D.Application{id}, [D.Row{b, Task.fields(id, b, "Second", True{})}], Task.saved(cancel, a)),
        L.Both{P.Both{{==}, {==}}, r => written_safe(2n, D.Context{id, kind},
          Task.saved(cancel, a), saved_safe(2n, D.Context{id, kind}, cancel, a), r)}, r)}
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
