import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Orders.bend as O
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Instance.bend as I
import ./Bindings.bend as B

# Authorization witnesses are about keys, independent of stored payloads.
def read_scope(admin: Bool, +id: String, +key: String, h: P.WriteScope(id, key)) ->
  P.ReadScope(admin, id, key):
  match admin:
    case True{}: Unit{}
    case False{}: h

def chosen(b: Bool, +id: String, +first: String, +second: String,
  hf: P.WriteScope(id, first), hs: P.WriteScope(id, second)) ->
  P.WriteScope(id, Bool.pick(String, b, second, first)):
  match b:
    case False{}: hf
    case True{}: hs

def saved_safe(cancel: Bool, ctx: D.Context, key: String) -> H.Safe(2n, ctx, Client.saved(cancel, key)):
  match cancel:
    case False{}: Unit{}
    case True{}: Unit{}

def resume_safe(+id: String, +kind: String, +key: String, owner: Maybe<&2, D.Value>,
  h: P.ReadScope(String.eq(kind, "admin"), id, key)) ->
  H.Safe(2n, D.Context{id, kind}, Client.resume(key, owner)):
  match owner:
    case Some{v}: L.Both{P.Both{{==}, h}, r => Unit{}}
    case None{}: Unit{}

def read_safe(+id: String, +kind: String, +key: String,
  +h: P.ReadScope(String.eq(kind, "admin"), id, key)) ->
  H.Safe(3n, D.Context{id, kind}, Client.read(key)):
  L.Both{P.Both{{==}, h}, r => resume_safe(id, kind, key, Client.owner_received(r), h)}

def command_safe(+id: String, +kind: String, +first: String, +second: String, p: Client.Command,
  +hf: P.WriteScope(id, first), +hs: P.WriteScope(id, second)) ->
  H.Safe(3n, D.Context{id, kind}, Client.command(first, second, p)):
  match p:
    case Client.Save{+b, t, +cancel}:
      L.Both{P.Both{{==}, P.Both{chosen(b, id, first, second, hf, hs), {==}}},
        r => saved_safe(cancel, D.Context{id, kind}, Bool.pick(String, b, second, first))}
    case Client.View{+b}:
      read_safe(id, kind, Bool.pick(String, b, second, first), read_scope(String.eq(kind, "admin"), id,
        Bool.pick(String, b, second, first), chosen(b, id, first, second, hf, hs)))
    case Client.Remove{b}:
      L.Both{P.Both{{==}, chosen(b, id, first, second, hf, hs)}, r => Unit{}}
    case Client.ListNotes{}:
      L.Both{P.Both{{==}, read_scope(String.eq(kind, "admin"), id, first, hf)}, a =>
        L.Both{P.Both{{==}, read_scope(String.eq(kind, "admin"), id, second, hs)}, b => Unit{}}}
    case Client.ReadAny{k}: Unit{}
    case Client.CountAll{}: Unit{}
    case Client.Invalid{}: Unit{}

def admin_safe(+id: String, p: Client.Command) ->
  H.Safe(3n, D.Context{id, "admin"}, Client.admin_command(p)):
  match p:
    case Client.ReadAny{k}: read_safe(id, "admin", k, Unit{})
    case Client.CountAll{}: L.Both{P.Both{{==}, {==}}, r => Unit{}}
    case Client.Save{b, t, cancel}: Unit{}
    case Client.View{b}: Unit{}
    case Client.Remove{b}: Unit{}
    case Client.ListNotes{}: Unit{}
    case Client.Invalid{}: Unit{}

def flags_safe(admin: Bool, alice: Bool, bob: Bool, +id: String, +kind: String, +args: D.Value,
  hm: {String.eq(kind, "admin") == admin : Bool},
  ha: {String.eq(id, "alice") == alice : Bool}, hb: {String.eq(id, "bob") == bob : Bool}) ->
  H.Safe(3n, D.Context{id, kind}, Client.flags(admin, alice, bob, args)):
  match admin alice bob:
    case True{} _ _:
      %Equal.sym(String, kind, "admin", O.string_equal(kind, "admin", hm)) :
        H.Safe(3n, D.Context{id, _}, Client.admin_command(Client.analyze(args)))
      admin_safe(id, Client.analyze(args))
    case False{} True{} _:
      %Equal.sym(String, id, "alice", O.string_equal(id, "alice", ha)) :
        H.Safe(3n, D.Context{_, kind}, Client.command("alice/1", "alice/2", Client.analyze(args)))
      command_safe("alice", kind, "alice/1", "alice/2", Client.analyze(args), P.Both{{==}, {==}}, P.Both{{==}, {==}})
    case False{} False{} True{}:
      %Equal.sym(String, id, "bob", O.string_equal(id, "bob", hb)) :
        H.Safe(3n, D.Context{_, kind}, Client.command("bob/1", "bob/2", Client.analyze(args)))
      command_safe("bob", kind, "bob/1", "bob/2", Client.analyze(args), P.Both{{==}, {==}}, P.Both{{==}, {==}})
    case False{} False{} False{}: Unit{}

def program_safe(ctx: D.Context, args: D.Value) -> H.Safe(3n, ctx, S.start(Client.program(), ctx, args)):
  D.Context{+id, +kind} = ctx
  flags_safe(String.eq(kind, "admin"), String.eq(id, "alice"), String.eq(id, "bob"), id, kind, args, {==}, {==}, {==})

def owners_initial(-s: D.State, valid: R.Valid(C.config(), s)) -> P.Owners(s):
  match valid:
    case L.Both{structure, L.Both{owners, remaining}}: owners

# The quantified state is never copied into the public proof namespace.
def certify(+ctx: D.Context, +args: D.Value, -code: String, +s: D.State,
  valid: R.Valid(C.config(), s), identity: {D.context_present(s, ctx) == True{} : Bool}, +n: Nat,
  h: H.Safe(3n, ctx, S.start(Client.program(), ctx, args))) ->
  R.SafetyTrace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.config(), s, ctx, code, args):
  H.execution_trace(S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), C.environment(), s, ctx, code, args,
    H.rewind(ctx, S.execute(n, Client.program(), C.schema(), s, ctx, args),
      T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
      Equal.sym(S.Trace, T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
        S.execute(n, Client.program(), C.schema(), s, ctx, args),
        T.reference(n, S.start(Client.program(), ctx, args), C.schema(), s)),
      H.safe(3n, n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{},
        h, P.Both{owners_initial(s, valid), P.Both{identity, Unit{}}})))

def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n, program_safe(I.context(), I.arguments()))

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(3n, Client.program(), C.schema(), s, ctx, args,
    H.finite(3n, S.start(Client.program(), ctx, args), ctx, program_safe(ctx, args)))
