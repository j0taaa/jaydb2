import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Policy.bend as P

type Principal is Data:
  Alice{}
  Bob{}

def name(p: Principal) -> String:
  match p:
    case Alice{}: "alice"
    case Bob{}: "bob"

def notes() -> D.Collection:
  D.Application{"notes"}

def directory(p: Principal) -> D.Collection:
  D.Application{P.dir_name(name(p))}

type Command is Data:
  Create{text: String, cancel: Bool}
  View{id: String}
  Update{id: String, text: String}
  Remove{id: String}
  ListNotes{}
  ReadAny{id: String}
  CountAll{}
  Invalid{}

def word(c: String, +a: String, b: String) -> Command:
  match c:
    case "create": Create{a, False{}}
    case "cancel": Create{a, True{}}
    case "view": View{a}
    case "update": Update{a, b}
    case "remove": Remove{a}
    case "list": ListNotes{}
    case "read": ReadAny{a}
    case "count": CountAll{}
    case _: Invalid{}

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{c}, D.VListEmpty{}}: word(c, "", "")
    case D.VList{D.VText{c}, D.VList{D.VText{a}, D.VListEmpty{}}}: word(c, a, "")
    case D.VList{D.VText{c}, D.VList{D.VText{a}, D.VList{D.VText{b}, D.VListEmpty{}}}}: word(c, a, b)
    case _: Invalid{}

def entry_fields(+p: Principal, +id: String) -> List<&2, D.Field>:
  [D.Field{"id", D.VText{id}}, D.Field{"owner", D.VText{name(p)}}]

def note_fields(+p: Principal, +id: String, text: String) -> List<&2, D.Field>:
  [D.Field{"id", D.VText{id}}, D.Field{"owner", D.VText{name(p)}}, D.Field{"text", D.VText{text}}]

# The note, then its directory entry; only the complete pair publishes.
def entry(+p: Principal, +id: String, done: S.Action) -> S.Action:
  S.Access{D.DefineRow{directory(p), id, entry_fields(p, id)}, r => done}

def save(+p: Principal, +id: String, text: String, done: S.Action) -> S.Action:
  S.Access{D.DefineRow{notes(), id, note_fields(p, id, text)}, r => entry(p, id, done)}

def unlist(+p: Principal, +id: String, done: S.Action) -> S.Action:
  S.Access{D.RemoveRow{directory(p), id}, r => done}

def discard(+p: Principal, +id: String, done: S.Action) -> S.Action:
  S.Access{D.RemoveRow{notes(), id}, r => unlist(p, id, done)}

def largest(keys: List<&2, String>, +best: String) -> String:
  match keys:
    case Nil{}: best
    case Con{+k, rest}: largest(rest, Bool.pick(String, String.is_lt(best, k), k, best))

# Ids are fixed-width decimals; bump adds one to the reversed digits.
def bump(s: String) -> String:
  match s:
    case SNil{}: "1"
    case SCon{Chr{+n}, +t}: Bool.pick(String, U32.is_lt(n, 57), SCon{Chr{(n + 1 : U32)}, t}, SCon{'0', bump(t)})

def fresh(+p: Principal, keys: List<&2, String>) -> String:
  String.reverse(bump(String.reverse(largest(keys, name(p) ++ "/00000000"))))

def keys_of(r: S.Return) -> List<&2, String>:
  match r:
    case S.Datum{D.Keys{ks}}: ks
    case _: Nil{}

def saved(cancel: Bool, id: String) -> S.Action:
  match cancel:
    case False{}: S.Finish{D.VText{id}}
    case True{}: S.Refuse{D.VText{"cancelled"}}

def mine(+p: Principal, +id: String) -> Bool:
  String.eq(P.key_owner(id), name(p))

def guarded(ok: Bool, then: S.Action) -> S.Action:
  match ok:
    case True{}: then
    case False{}: S.Refuse{D.VText{"no such own note"}}

def created(+p: Principal, +id: String, text: String, cancel: Bool) -> S.Action:
  guarded(mine(p, id), save(p, id, text, saved(cancel, id)))

def shown(+key: String, r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: D.VRecord{"id", D.VText{key}, D.VRecord{"text", v, D.VRecordEmpty{}}}
    case _: D.VAbsent{}

def read(+key: String, done: D.Value -> S.Action) -> S.Action:
  S.Access{D.ReadCell{notes(), key, "text"}, r => done(shown(key, r))}

def exists(r: S.Return) -> Bool:
  match r:
    case S.Datum{D.Existence{b}}: b
    case _: False{}

# Reads ONLY the caller's directory, then each listed note.
def list(keys: List<&2, String>, +p: Principal, done: D.Value -> S.Action) -> S.Action:
  match keys:
    case Nil{}: done(D.VListEmpty{})
    case Con{+k, rest}: guarded(mine(p, k), read(k, v => list(rest, p, tail => done(D.VList{v, tail}))))

def command(+p: Principal, cmd: Command) -> S.Action:
  match cmd:
    case Create{t, cancel}:
      S.Access{D.EnumerateKeys{directory(p)}, r => created(p, fresh(p, keys_of(r)), t, cancel)}
    case View{+id}: guarded(mine(p, id), read(id, v => S.Finish{v}))
    case Update{+id, t}:
      guarded(mine(p, id), S.Access{D.ViewExistence{notes(), id}, r => guarded(exists(r), save(p, id, t, S.Finish{D.VText{id}}))})
    case Remove{+id}: guarded(mine(p, id), discard(p, id, S.Finish{D.VText{id}}))
    case ListNotes{}: S.Access{D.EnumerateKeys{directory(p)}, r => list(keys_of(r), p, v => S.Finish{v})}
    case _: S.Refuse{D.VText{"unsupported"}}

def count_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Count{n}}: D.VInt{0, U32.from_nat(n)}
    case _: D.VAbsent{}

def admin(cmd: Command) -> S.Action:
  match cmd:
    case ReadAny{+k}: read(k, v => S.Finish{v})
    case CountAll{}: S.Access{D.CountRows{notes()}, r => S.Finish{count_value(r)}}
    case _: S.Refuse{D.VText{"unsupported"}}

def flags(su: Bool, alice: Bool, bob: Bool, +args: D.Value) -> S.Action:
  match su alice bob:
    case True{} _ _: admin(analyze(args))
    case False{} True{} _: command(Alice{}, analyze(args))
    case False{} False{} True{}: command(Bob{}, analyze(args))
    case False{} False{} False{}: S.Refuse{D.VText{"unknown principal"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{+id, kind} = ctx
  flags(String.eq(kind, "admin"), String.eq(id, "alice"), String.eq(id, "bob"), args)

def program() -> S.Program:
  S.Program{start}
