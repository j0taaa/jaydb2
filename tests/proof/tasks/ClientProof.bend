import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../contract/Requirements.bend as R
import ../../../src/Termination.bend as T
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Instance.bend as I
import ./Bindings.bend as B

def title_safe(+id: String, kind: String, +key: String, title: Maybe<&2, String>) ->
  H.Safe(2n, D.Context{id, kind}, Client.resume_title(id, key, title)):
  match title:
    case None{}: Unit{}
    case Some{text}: L.Both{{==}, r => Unit{}}

def conclude_safe(+id: String, kind: String, +key: String, title: Maybe<&2, String>) ->
  H.Safe(2n, D.Context{id, kind}, Client.conclude_title(id, key, title)):
  match title:
    case None{}: Unit{}
    case Some{text}: L.Both{P.Both{{==}, {==}}, r => Unit{}}

def saved_safe(n: Nat, ctx: D.Context, cancel: Bool, key: String) ->
  H.Safe(Succ{n}, ctx, Client.saved(cancel, key)):
  match cancel:
    case False{}: Unit{}
    case True{}: Unit{}

def command_safe(ctx: D.Context, p: Client.Command) ->
  H.Safe(3n, ctx, Client.command(D.context_id(ctx), p)):
  match ctx p:
    case D.Context{id, kind} Client.ListTasks{}: L.Both{{==}, r => Unit{}}
    case D.Context{+id, kind} Client.View{key}:
      L.Both{{==}, r => title_safe(id, kind, key, Client.text_received(r))}
    case D.Context{+id, +kind} Client.Save{+key, title, done, +cancel}:
      L.Both{P.Both{{==}, {==}}, r => saved_safe(1n, D.Context{id, kind}, cancel, key)}
    case D.Context{+id, kind} Client.Conclude{key}:
      L.Both{{==}, r => conclude_safe(id, kind, key, Client.text_received(r))}
    case D.Context{id, kind} Client.Remove{key}: L.Both{{==}, r => Unit{}}
    case D.Context{id, kind} Client.Invalid{}: Unit{}

def program_safe(+ctx: D.Context, args: D.Value) -> H.Safe(3n, ctx, S.start(Client.program(), ctx, args)):
  match ctx:
    case D.Context{id, kind}: command_safe(D.Context{id, kind}, Client.analyze(args))

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
      H.safe(3n, n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{},
        program_safe(ctx, args), P.Both{owners_initial(s, valid), P.Both{identity, Unit{}}})))

def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(3n, Client.program(), C.schema(), s, ctx, args,
    H.finite(3n, S.start(Client.program(), ctx, args), ctx, program_safe(ctx, args)))
