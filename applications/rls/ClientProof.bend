import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./RequestFacts.bend as F
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Directory.bend as Dir
import ./Ownership.bend as O
import ./Orders.bend as Ord
import ./Completion.bend as End
import ./MutationStateShapeProofs.bend as Shape
import ./ReadOperationProofs.bend as RO
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Instance.bend as I
import ./Bindings.bend as B

# Per-principal facts; every other step is generic in the principal.
def valid_name(p: Client.Principal) -> {P.named(Client.name(p)) == True{} : Bool}:
  match p:
    case Client.Alice{}: {==}
    case Client.Bob{}: {==}

def dir_writable(p: Client.Principal) -> P.Writable(Client.name(p), P.dir_name(Client.name(p))):
  match p:
    case Client.Alice{}: {==}
    case Client.Bob{}: {==}

def scope(+p: Client.Principal, +k: String, +own: {P.key_owner(k) == Client.name(p) : String}) -> P.WriteScope(Client.name(p), k):
  P.Both{own, (%Equal.sym(String, P.key_owner(k), Client.name(p), own) : {P.named(_) == True{} : Bool} valid_name(p))}

def read_scope(admin: Bool, +id: String, +key: String, h: P.WriteScope(id, key)) -> P.ReadScope(admin, id, key):
  match admin:
    case True{}: Unit{}
    case False{}: h

def keys_scope(admin: Bool, +p: Client.Principal) -> P.KeysScope(admin, Client.name(p), P.dir_name(Client.name(p))):
  match admin:
    case True{}:
      match p:
        case Client.Alice{}: {==}
        case Client.Bob{}: {==}
    case False{}: {==}

def owner_field(+p: Client.Principal, +k: String, +own: {P.key_owner(k) == Client.name(p) : String}) ->
  {Some{D.VText{Client.name(p)}} == Some{D.VText{P.key_owner(k)}} : Maybe<&2, D.Value>}:
  Equal.cong(String, Maybe<&2, D.Value>, x => Some{D.VText{x}}, Client.name(p), P.key_owner(k),
    Equal.sym(String, P.key_owner(k), Client.name(p), own))

def foreign(+id: String, -a: String, -q: String, own: {P.key_owner(id) == a : String},
  ne: {String.eq(a, q) == False{} : Bool}) -> {String.eq(P.key_owner(id), q) == False{} : Bool}:
  %Equal.sym(String, P.key_owner(id), a, own) : {String.eq(_, q) == False{} : Bool}
  ne

def bob_first(+w: D.State, h: L.E<P.Agree("bob", P.rows(P.dir_name("bob"), w), P.rows("notes", w)),
  P.Agree("alice", P.rows(P.dir_name("alice"), w), P.rows("notes", w))>) -> P.Directory(w):
  L.Both{b, a} = h
  L.Both{a, b}

# Directory law after a note write plus its entry write, for each principal.
def saved_directory(p: Client.Principal, +s: D.State, +id: String, +text: String, +ns: List<&2, D.Row>, +ds: List<&2, D.Row>,
  +found1: {D.rows_collection(D.Application{"notes"}, s) == Some{ns} : Maybe<&2, List<&2, D.Row>>},
  +found2: {D.rows_collection(Client.directory(p), Dir.first(s, Shape.RowUpsert{id, Client.note_fields(p, id, text)}, ns)) == Some{ds} : Maybe<&2, List<&2, D.Row>>},
  +own: {P.key_owner(id) == Client.name(p) : String}, dir: P.Directory(s), +owners: P.Owners(s)) ->
  P.Directory(Dir.second(Client.name(p), s, Shape.RowUpsert{id, Client.note_fields(p, id, text)}, ns, Shape.RowUpsert{id, Client.entry_fields(p, id)}, ds)):
  match p:
    case Client.Alice{}:
      L.Both{ha, hb} = dir
      Dir.pair("alice", "bob", s, Shape.RowUpsert{id, Client.note_fields(Client.Alice{}, id, text)}, Shape.RowUpsert{id, Client.entry_fields(Client.Alice{}, id)},
        ns, ds, found1, found2, {==}, {==}, {==}, {==},
        h => Dir.save_same("alice", ds, ns, id, Client.note_fields(Client.Alice{}, id, text), Client.entry_fields(Client.Alice{}, id), {==}, h),
        h => Dir.save_other("bob", P.rows(P.dir_name("bob"), s), ns, id, Client.note_fields(Client.Alice{}, id, text), O.users(s), "notes",
          Dir.notes_rows(s, ns, found1, owners), {==}, foreign(id, "alice", "bob", own, {==}), h), ha, hb)
    case Client.Bob{}:
      L.Both{ha, hb} = dir
      bob_first(Dir.second("bob", s, Shape.RowUpsert{id, Client.note_fields(Client.Bob{}, id, text)}, ns, Shape.RowUpsert{id, Client.entry_fields(Client.Bob{}, id)}, ds),
        Dir.pair("bob", "alice", s, Shape.RowUpsert{id, Client.note_fields(Client.Bob{}, id, text)}, Shape.RowUpsert{id, Client.entry_fields(Client.Bob{}, id)},
        ns, ds, found1, found2, {==}, {==}, {==}, {==},
        h => Dir.save_same("bob", ds, ns, id, Client.note_fields(Client.Bob{}, id, text), Client.entry_fields(Client.Bob{}, id), {==}, h),
        h => Dir.save_other("alice", P.rows(P.dir_name("alice"), s), ns, id, Client.note_fields(Client.Bob{}, id, text), O.users(s), "notes",
          Dir.notes_rows(s, ns, found1, owners), {==}, foreign(id, "bob", "alice", own, {==}), h), hb, ha))

def removed_directory(p: Client.Principal, +s: D.State, +id: String, +ns: List<&2, D.Row>, +ds: List<&2, D.Row>,
  +found1: {D.rows_collection(D.Application{"notes"}, s) == Some{ns} : Maybe<&2, List<&2, D.Row>>},
  +found2: {D.rows_collection(Client.directory(p), Dir.first(s, Shape.RowDelete{id}, ns)) == Some{ds} : Maybe<&2, List<&2, D.Row>>},
  +own: {P.key_owner(id) == Client.name(p) : String}, dir: P.Directory(s), +owners: P.Owners(s)) ->
  P.Directory(Dir.second(Client.name(p), s, Shape.RowDelete{id}, ns, Shape.RowDelete{id}, ds)):
  match p:
    case Client.Alice{}:
      L.Both{ha, hb} = dir
      Dir.pair("alice", "bob", s, Shape.RowDelete{id}, Shape.RowDelete{id}, ns, ds, found1, found2, {==}, {==}, {==}, {==},
        h => Dir.remove_same("alice", ds, ns, id, h),
        h => Dir.remove_other("bob", P.rows(P.dir_name("bob"), s), ns, id, O.users(s), "notes",
          Dir.notes_rows(s, ns, found1, owners), foreign(id, "alice", "bob", own, {==}), h), ha, hb)
    case Client.Bob{}:
      L.Both{ha, hb} = dir
      bob_first(Dir.second("bob", s, Shape.RowDelete{id}, ns, Shape.RowDelete{id}, ds),
        Dir.pair("bob", "alice", s, Shape.RowDelete{id}, Shape.RowDelete{id}, ns, ds, found1, found2, {==}, {==}, {==}, {==},
        h => Dir.remove_same("bob", ds, ns, id, h),
        h => Dir.remove_other("alice", P.rows(P.dir_name("alice"), s), ns, id, O.users(s), "notes",
          Dir.notes_rows(s, ns, found1, owners), foreign(id, "bob", "alice", own, {==}), h), hb, ha))

# Note first, then its directory entry; the pair restores the exact law.
def save_safe(+d: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +s: D.State, +id: String, +text: String,
  -done: S.Action, +own: {P.key_owner(id) == Client.name(p) : String}, dir: P.Directory(s), +owners: P.Owners(s),
  fin: @m: Nat -> @w: D.State -> P.Directory(w) -> H.Safe(m, e, D.Context{Client.name(p), kind}, w, done)) ->
  H.Safe(d, e, D.Context{Client.name(p), kind}, s, Client.save(p, id, text, done)):
  H.access(d, e, D.Context{Client.name(p), kind}, s, D.DefineRow{Client.notes(), id, Client.note_fields(p, id, text)},
    r => Client.entry(p, id, done), P.Both{{==}, P.Both{scope(p, id, own), owner_field(p, id, own)}}, +m =>
    H.written(m, e, D.Context{Client.name(p), kind}, s, Client.notes(), Shape.RowUpsert{id, Client.note_fields(p, id, text)},
      r => Client.entry(p, id, done), +ns => +found1 =>
      H.access(m, e, D.Context{Client.name(p), kind}, Dir.first(s, Shape.RowUpsert{id, Client.note_fields(p, id, text)}, ns),
        D.DefineRow{Client.directory(p), id, Client.entry_fields(p, id)}, r => done,
        P.Both{dir_writable(p), P.Both{scope(p, id, own), owner_field(p, id, own)}}, +m2 =>
        H.written(m2, e, D.Context{Client.name(p), kind}, Dir.first(s, Shape.RowUpsert{id, Client.note_fields(p, id, text)}, ns),
          Client.directory(p), Shape.RowUpsert{id, Client.entry_fields(p, id)}, r => done, +ds => +found2 =>
          fin(m2, Dir.second(Client.name(p), s, Shape.RowUpsert{id, Client.note_fields(p, id, text)}, ns, Shape.RowUpsert{id, Client.entry_fields(p, id)}, ds),
            saved_directory(p, s, id, text, ns, ds, found1, found2, own, dir, owners))))))

def discard_safe(+d: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +s: D.State, +id: String,
  -done: S.Action, +own: {P.key_owner(id) == Client.name(p) : String}, dir: P.Directory(s), +owners: P.Owners(s),
  fin: @m: Nat -> @w: D.State -> P.Directory(w) -> H.Safe(m, e, D.Context{Client.name(p), kind}, w, done)) ->
  H.Safe(d, e, D.Context{Client.name(p), kind}, s, Client.discard(p, id, done)):
  H.access(d, e, D.Context{Client.name(p), kind}, s, D.RemoveRow{Client.notes(), id}, r => Client.unlist(p, id, done),
    P.Both{{==}, scope(p, id, own)}, +m =>
    H.written(m, e, D.Context{Client.name(p), kind}, s, Client.notes(), Shape.RowDelete{id}, r => Client.unlist(p, id, done), +ns => +found1 =>
      H.access(m, e, D.Context{Client.name(p), kind}, Dir.first(s, Shape.RowDelete{id}, ns), D.RemoveRow{Client.directory(p), id}, r => done,
        P.Both{dir_writable(p), scope(p, id, own)}, +m2 =>
        H.written(m2, e, D.Context{Client.name(p), kind}, Dir.first(s, Shape.RowDelete{id}, ns), Client.directory(p), Shape.RowDelete{id}, r => done, +ds => +found2 =>
          fin(m2, Dir.second(Client.name(p), s, Shape.RowDelete{id}, ns, Shape.RowDelete{id}, ds),
            removed_directory(p, s, id, ns, ds, found1, found2, own, dir, owners))))))

def saved_safe(cancel: Bool, +m: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +w: D.State, +id: String, dir: P.Directory(w)) ->
  H.Safe(m, e, D.Context{Client.name(p), kind}, w, Client.saved(cancel, id)):
  match cancel:
    case False{}: dir
    case True{}: Unit{}

def guarded_safe(ok: Bool, +d: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +s: D.State, +id: String, -then: S.Action,
  eq: {Client.mine(p, id) == ok : Bool},
  h: {P.key_owner(id) == Client.name(p) : String} -> H.Safe(d, e, D.Context{Client.name(p), kind}, s, then)) ->
  H.Safe(d, e, D.Context{Client.name(p), kind}, s, Client.guarded(ok, then)):
  match ok:
    case True{}: h(Ord.string_equal(P.key_owner(id), Client.name(p), eq))
    case False{}: Unit{}

def guarded_any(ok: Bool, +d: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, -then: S.Action, h: H.Safe(d, e, ctx, s, then)) ->
  H.Safe(d, e, ctx, s, Client.guarded(ok, then)):
  match ok:
    case True{}: h
    case False{}: Unit{}

# A fresh id is checked against the caller's namespace before any write.
def created_safe(+d: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +s: D.State, +id: String, +text: String, +cancel: Bool,
  dir: P.Directory(s), +owners: P.Owners(s)) -> H.Safe(d, e, D.Context{Client.name(p), kind}, s, Client.created(p, id, text, cancel)):
  guarded_safe(Client.mine(p, id), d, e, kind, p, s, id, Client.save(p, id, text, Client.saved(cancel, id)), {==}, +own =>
    save_safe(d, e, kind, p, s, id, text, Client.saved(cancel, id), own, dir, owners, +m => +w => dw => saved_safe(cancel, m, e, kind, p, w, id, dw)))

def read_safe(+d: Nat, +e: D.Schema, +id: String, +kind: String, +s: D.State, +key: String, -done: D.Value -> S.Action,
  +h: P.ReadScope(String.eq(kind, "admin"), id, key), fin: @m: Nat -> @v: D.Value -> H.Safe(m, e, D.Context{id, kind}, s, done(v))) ->
  H.Safe(d, e, D.Context{id, kind}, s, Client.read(key, done)):
  H.access(d, e, D.Context{id, kind}, s, D.ReadCell{Client.notes(), key, "text"}, r => done(Client.shown(key, r)), P.Both{{==}, h}, +m =>
    H.reading(m, e, D.Context{id, kind}, s, RO.Cell{}, Client.notes(), key, "text", r => done(Client.shown(key, r)), +o =>
      fin(m, Client.shown(key, S.Datum{o}))))

# Listing reads ONLY the caller's directory, then each listed own note.
def list_safe(keys: List<&2, String>, +d: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +s: D.State,
  -done: D.Value -> S.Action, fin: @m: Nat -> @v: D.Value -> H.Safe(m, e, D.Context{Client.name(p), kind}, s, done(v))) ->
  H.Safe(d, e, D.Context{Client.name(p), kind}, s, Client.list(keys, p, done)):
  match keys:
    case Nil{}: fin(d, D.VListEmpty{})
    case Con{+k, +rest}:
      guarded_safe(Client.mine(p, k), d, e, kind, p, s, k, Client.read(k, v => Client.list(rest, p, tail => done(D.VList{v, tail}))), {==}, +own =>
        read_safe(d, e, Client.name(p), kind, s, k, v => Client.list(rest, p, tail => done(D.VList{v, tail})),
          read_scope(String.eq(kind, "admin"), Client.name(p), k, scope(p, k, own)), +m => +v =>
          list_safe(rest, m, e, kind, p, s, tail => done(D.VList{v, tail}), +m2 => +v2 => fin(m2, D.VList{v, v2}))))

def command_safe(+d: Nat, +e: D.Schema, +kind: String, +p: Client.Principal, +s: D.State, cmd: Client.Command,
  dir: P.Directory(s), +owners: P.Owners(s)) -> H.Safe(d, e, D.Context{Client.name(p), kind}, s, Client.command(p, cmd)):
  match cmd:
    case Client.Create{+t, +cancel}:
      H.access(d, e, D.Context{Client.name(p), kind}, s, D.EnumerateKeys{Client.directory(p)},
        r => Client.created(p, Client.fresh(p, Client.keys_of(r)), t, cancel), keys_scope(String.eq(kind, "admin"), p), +m =>
        H.reading(m, e, D.Context{Client.name(p), kind}, s, RO.Keys{}, Client.directory(p), "", "",
          r => Client.created(p, Client.fresh(p, Client.keys_of(r)), t, cancel), +o =>
          created_safe(m, e, kind, p, s, Client.fresh(p, Client.keys_of(S.Datum{o})), t, cancel, dir, owners)))
    case Client.View{+id}:
      guarded_safe(Client.mine(p, id), d, e, kind, p, s, id, Client.read(id, v => S.Finish{v}), {==}, +own =>
        read_safe(d, e, Client.name(p), kind, s, id, v => S.Finish{v},
          read_scope(String.eq(kind, "admin"), Client.name(p), id, scope(p, id, own)), +m => v => dir))
    case Client.Update{+id, +t}:
      guarded_safe(Client.mine(p, id), d, e, kind, p, s, id,
        S.Access{D.ViewExistence{Client.notes(), id}, r => Client.guarded(Client.exists(r), Client.save(p, id, t, S.Finish{D.VText{id}}))}, {==}, +own =>
        H.access(d, e, D.Context{Client.name(p), kind}, s, D.ViewExistence{Client.notes(), id},
          r => Client.guarded(Client.exists(r), Client.save(p, id, t, S.Finish{D.VText{id}})),
          P.Both{{==}, read_scope(String.eq(kind, "admin"), Client.name(p), id, scope(p, id, own))}, +m =>
          H.reading(m, e, D.Context{Client.name(p), kind}, s, RO.ExistenceRead{}, Client.notes(), id, "",
            r => Client.guarded(Client.exists(r), Client.save(p, id, t, S.Finish{D.VText{id}})), +o =>
            guarded_any(Client.exists(S.Datum{o}), m, e, D.Context{Client.name(p), kind}, s, Client.save(p, id, t, S.Finish{D.VText{id}}),
              save_safe(m, e, kind, p, s, id, t, S.Finish{D.VText{id}}, own, dir, owners, +m2 => +w => dw => dw)))))
    case Client.Remove{+id}:
      guarded_safe(Client.mine(p, id), d, e, kind, p, s, id, Client.discard(p, id, S.Finish{D.VText{id}}), {==}, +own =>
        discard_safe(d, e, kind, p, s, id, S.Finish{D.VText{id}}, own, dir, owners, +m => +w => dw => dw))
    case Client.ListNotes{}:
      H.access(d, e, D.Context{Client.name(p), kind}, s, D.EnumerateKeys{Client.directory(p)}, r => Client.list(Client.keys_of(r), p, v => S.Finish{v}),
        keys_scope(String.eq(kind, "admin"), p), +m =>
        H.reading(m, e, D.Context{Client.name(p), kind}, s, RO.Keys{}, Client.directory(p), "", "", r => Client.list(Client.keys_of(r), p, v => S.Finish{v}), +o =>
          list_safe(Client.keys_of(S.Datum{o}), m, e, kind, p, s, v => S.Finish{v}, +m2 => v => dir)))
    case Client.ReadAny{k}: Unit{}
    case Client.CountAll{}: Unit{}
    case Client.Invalid{}: Unit{}

def admin_safe(+d: Nat, +e: D.Schema, +id: String, +s: D.State, cmd: Client.Command, dir: P.Directory(s)) ->
  H.Safe(d, e, D.Context{id, "admin"}, s, Client.admin(cmd)):
  match cmd:
    case Client.ReadAny{+k}: read_safe(d, e, id, "admin", s, k, v => S.Finish{v}, Unit{}, +m => v => dir)
    case Client.CountAll{}:
      H.access(d, e, D.Context{id, "admin"}, s, D.CountRows{Client.notes()}, r => S.Finish{Client.count_value(r)}, P.Both{{==}, {==}}, +m =>
        H.reading(m, e, D.Context{id, "admin"}, s, RO.Count{}, Client.notes(), "", "", r => S.Finish{Client.count_value(r)}, +o => dir))
    case Client.Create{t, cancel}: Unit{}
    case Client.View{k}: Unit{}
    case Client.Update{k, t}: Unit{}
    case Client.Remove{k}: Unit{}
    case Client.ListNotes{}: Unit{}
    case Client.Invalid{}: Unit{}

def flags_safe(admin: Bool, alice: Bool, bob: Bool, +d: Nat, +e: D.Schema, +id: String, +kind: String, +s: D.State, +args: D.Value,
  hm: {String.eq(kind, "admin") == admin : Bool}, ha: {String.eq(id, "alice") == alice : Bool}, hb: {String.eq(id, "bob") == bob : Bool},
  dir: P.Directory(s), +owners: P.Owners(s)) -> H.Safe(d, e, D.Context{id, kind}, s, Client.flags(admin, alice, bob, args)):
  match admin alice bob:
    case True{} _ _:
      %Equal.sym(String, kind, "admin", Ord.string_equal(kind, "admin", hm)) : H.Safe(d, e, D.Context{id, _}, s, Client.admin(Client.analyze(args)))
      admin_safe(d, e, id, s, Client.analyze(args), dir)
    case False{} True{} _:
      %Equal.sym(String, id, "alice", Ord.string_equal(id, "alice", ha)) : H.Safe(d, e, D.Context{_, kind}, s, Client.command(Client.Alice{}, Client.analyze(args)))
      command_safe(d, e, kind, Client.Alice{}, s, Client.analyze(args), dir, owners)
    case False{} False{} True{}:
      %Equal.sym(String, id, "bob", Ord.string_equal(id, "bob", hb)) : H.Safe(d, e, D.Context{_, kind}, s, Client.command(Client.Bob{}, Client.analyze(args)))
      command_safe(d, e, kind, Client.Bob{}, s, Client.analyze(args), dir, owners)
    case False{} False{} False{}: Unit{}

def program_safe(+d: Nat, +e: D.Schema, ctx: D.Context, +args: D.Value, +s: D.State, dir: P.Directory(s), +owners: P.Owners(s)) ->
  H.Safe(d, e, ctx, s, S.start(Client.program(), ctx, args)):
  D.Context{+id, +kind} = ctx
  flags_safe(String.eq(kind, "admin"), String.eq(id, "alice"), String.eq(id, "bob"), d, e, id, kind, s, args, {==}, {==}, {==}, dir, owners)

# The quantified state is never copied into the public proof namespace.
def certify(+ctx: D.Context, +args: D.Value, -code: String, +s: D.State, +owners: P.Owners(s),
  identity: {D.context_present(s, ctx) == True{} : Bool}, +n: Nat,
  h: H.Safe(Succ{n}, C.schema(), ctx, s, S.start(Client.program(), ctx, args))) ->
  R.SafetyTrace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.config(), s, ctx, code, args):
  H.execution_trace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.schema(), C.limits(), C.environment(), s, ctx, code, args,
    H.rewind(ctx, S.execute(n, Client.program(), C.schema(), s, ctx, args), T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
      Equal.sym(S.Trace, T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
        S.execute(n, Client.program(), C.schema(), s, ctx, args), T.reference(n, S.start(Client.program(), ctx, args), C.schema(), s)),
      H.safe(n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{}, h, P.Both{owners, P.Both{identity, Unit{}}})))

# Termination on arbitrary (even invalid) states: listing's bound is the
# actual number of directory keys observed; every other command is bounded.
def guard_finite(ok: Bool, +n: Nat, -then: S.Action, h: T.Finite(Succ{n}, then)) -> T.Finite(Succ{n}, Client.guarded(ok, then)):
  match ok:
    case True{}: h
    case False{}: Unit{}

def saved_finite(cancel: Bool, +id: String) -> T.Finite(1n, Client.saved(cancel, id)):
  match cancel:
    case False{}: Unit{}
    case True{}: Unit{}

def list_depth(keys: List<&2, String>) -> Nat:
  match keys:
    case Nil{}: 1n
    case Con{k, rest}: Succ{list_depth(rest)}

def list_finite(keys: List<&2, String>, +p: Client.Principal, -done: D.Value -> S.Action, h: @v: D.Value -> T.Finite(1n, done(v))) ->
  T.Finite(list_depth(keys), Client.list(keys, p, done)):
  match keys:
    case Nil{}: h(D.VListEmpty{})
    case Con{+k, +rest}:
      guard_finite(Client.mine(p, k), list_depth(rest), Client.read(k, v => Client.list(rest, p, tail => done(D.VList{v, tail}))),
        +r => list_finite(rest, p, tail => done(D.VList{Client.shown(k, r), tail}), v => h(D.VList{Client.shown(k, r), v})))

def create_finite(+p: Client.Principal, +t: String, +cancel: Bool) -> T.Finite(4n, Client.command(p, Client.Create{t, cancel})):
  +r => guard_finite(Client.mine(p, Client.fresh(p, Client.keys_of(r))), 2n,
    Client.save(p, Client.fresh(p, Client.keys_of(r)), t, Client.saved(cancel, Client.fresh(p, Client.keys_of(r)))),
    r2 => r3 => saved_finite(cancel, Client.fresh(p, Client.keys_of(r))))

def view_finite(+p: Client.Principal, +id: String) -> T.Finite(4n, Client.command(p, Client.View{id})):
  guard_finite(Client.mine(p, id), 3n, Client.read(id, v => S.Finish{v}), r => Unit{})

def update_finite(+p: Client.Principal, +id: String, +t: String) -> T.Finite(4n, Client.command(p, Client.Update{id, t})):
  guard_finite(Client.mine(p, id), 3n,
    S.Access{D.ViewExistence{Client.notes(), id}, r => Client.guarded(Client.exists(r), Client.save(p, id, t, S.Finish{D.VText{id}}))},
    +r => guard_finite(Client.exists(r), 2n, Client.save(p, id, t, S.Finish{D.VText{id}}), r2 => r3 => Unit{}))

def remove_finite(+p: Client.Principal, +id: String) -> T.Finite(4n, Client.command(p, Client.Remove{id})):
  guard_finite(Client.mine(p, id), 3n, Client.discard(p, id, S.Finish{D.VText{id}}), r => r2 => Unit{})

def command_complete(+p: Client.Principal, cmd: Client.Command, +e: D.Schema, +s: D.State, +ts: List<&2, S.OperationEvent>) ->
  End.Complete(Client.command(p, cmd), e, s, ts):
  match cmd:
    case Client.ListNotes{}:
      End.access(D.EnumerateKeys{Client.directory(p)}, r => Client.list(Client.keys_of(r), p, v => S.Finish{v}), e, s, ts,
        +r => +w => events => End.finite(list_depth(Client.keys_of(r)), Client.list(Client.keys_of(r), p, v => S.Finish{v}), e, w, events,
          list_finite(Client.keys_of(r), p, v => S.Finish{v}, v => Unit{})))
    case Client.Create{+t, +cancel}: End.finite(4n, Client.command(p, Client.Create{t, cancel}), e, s, ts, create_finite(p, t, cancel))
    case Client.View{+id}: End.finite(4n, Client.command(p, Client.View{id}), e, s, ts, view_finite(p, id))
    case Client.Update{+id, +t}: End.finite(4n, Client.command(p, Client.Update{id, t}), e, s, ts, update_finite(p, id, t))
    case Client.Remove{+id}: End.finite(4n, Client.command(p, Client.Remove{id}), e, s, ts, remove_finite(p, id))
    case Client.ReadAny{k}: End.finite(1n, S.Refuse{D.VText{"unsupported"}}, e, s, ts, Unit{})
    case Client.CountAll{}: End.finite(1n, S.Refuse{D.VText{"unsupported"}}, e, s, ts, Unit{})
    case Client.Invalid{}: End.finite(1n, S.Refuse{D.VText{"unsupported"}}, e, s, ts, Unit{})

def admin_finite(cmd: Client.Command) -> T.Finite(4n, Client.admin(cmd)):
  match cmd:
    case Client.ReadAny{+k}: r => Unit{}
    case Client.CountAll{}: r => Unit{}
    case Client.Create{t, cancel}: Unit{}
    case Client.View{k}: Unit{}
    case Client.Update{k, t}: Unit{}
    case Client.Remove{k}: Unit{}
    case Client.ListNotes{}: Unit{}
    case Client.Invalid{}: Unit{}

def flags_complete(admin: Bool, alice: Bool, bob: Bool, +args: D.Value, +e: D.Schema, +s: D.State, +ts: List<&2, S.OperationEvent>) ->
  End.Complete(Client.flags(admin, alice, bob, args), e, s, ts):
  match admin alice bob:
    case True{} _ _: End.finite(4n, Client.admin(Client.analyze(args)), e, s, ts, admin_finite(Client.analyze(args)))
    case False{} True{} _: command_complete(Client.Alice{}, Client.analyze(args), e, s, ts)
    case False{} False{} True{}: command_complete(Client.Bob{}, Client.analyze(args), e, s, ts)
    case False{} False{} False{}: End.finite(1n, S.Refuse{D.VText{"unknown principal"}}, e, s, ts, Unit{})

def start_complete(ctx: D.Context, +args: D.Value, +e: D.Schema, +s: D.State, +ts: List<&2, S.OperationEvent>) ->
  End.Complete(S.start(Client.program(), ctx, args), e, s, ts):
  D.Context{+id, +kind} = ctx
  flags_complete(String.eq(kind, "admin"), String.eq(id, "alice"), String.eq(id, "bob"), args, e, s, ts)

def terminates_complete(+s: D.State, +ctx: D.Context, +args: D.Value,
  h: End.Complete(S.start(Client.program(), ctx, args), C.schema(), s, Nil{})) -> F.Terminates(Client.program(), C.schema(), s, ctx, args):
  match h:
    case (+n, w, events, r, eq): T.witness_program(n, Client.program(), C.schema(), s, ctx, args, (w, events, r, eq))

def certificate(+ctx: D.Context, +args: D.Value, -code: String, +s: D.State, valid: R.Valid(C.config(), s),
  identity: {D.context_present(s, ctx) == True{} : Bool}, +n: Nat) ->
  R.SafetyTrace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.config(), s, ctx, code, args):
  L.Both{structure, L.Both{+owners, L.Both{dir, rest}}} = valid
  certify(ctx, args, code, s, owners, identity, n, program_safe(Succ{n}, C.schema(), ctx, args, s, dir, owners))

def B.certificate(s, valid, identity, n):
  certificate(I.context(), I.arguments(), B.code(), s, valid, identity, n)

def B.terminates(s, ctx, args):
  +s = s
  +ctx = ctx
  +args = args
  terminates_complete(s, ctx, args, start_complete(ctx, args, C.schema(), s, Nil{}))
