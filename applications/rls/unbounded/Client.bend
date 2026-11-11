import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Model.bend as M

type Command is Data:
  Create{text: String, cancel: Bool}
  View{key: String}
  Update{key: String, text: String}
  Remove{key: String}
  ListNotes{}
  ReadAny{key: String}
  CountAll{}
  Invalid{}

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{"create"}, D.VList{D.VText{t}, D.VListEmpty{}}}: Create{t, False{}}
    case D.VList{D.VText{"cancel"}, D.VList{D.VText{t}, D.VListEmpty{}}}: Create{t, True{}}
    case D.VList{D.VText{"view"}, D.VList{D.VText{k}, D.VListEmpty{}}}: View{k}
    case D.VList{D.VText{"update"}, D.VList{D.VText{k}, D.VList{D.VText{t}, D.VListEmpty{}}}}: Update{k, t}
    case D.VList{D.VText{"remove"}, D.VList{D.VText{k}, D.VListEmpty{}}}: Remove{k}
    case D.VList{D.VText{"list"}, D.VListEmpty{}}: ListNotes{}
    case D.VList{D.VText{"read"}, D.VList{D.VText{k}, D.VListEmpty{}}}: ReadAny{k}
    case D.VList{D.VText{"count"}, D.VListEmpty{}}: CountAll{}
    case _: Invalid{}

def read_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: v
    case _: D.VAbsent{}

def detail(key: String, owner: D.Value, r: S.Return) -> D.Value:
  D.VRecord{"id", D.VText{key}, D.VRecord{"owner", owner,
    D.VRecord{"text", read_value(r), D.VRecordEmpty{}}}}

def resume(+key: String, r: S.Return, done: D.Value -> S.Action) -> S.Action:
  match r:
    case S.Datum{D.Cell{v}}:
      S.Access{D.ReadCell{D.Application{"notes"}, key, "text"}, r => done(detail(key, v, r))}
    case _: done(D.VAbsent{})

def read(+key: String, done: D.Value -> S.Action) -> S.Action:
  S.Access{D.ReadCell{D.Application{"notes"}, key, "owner"}, r => resume(key, r, done)}

# Every bitmap position has a distinct address. Extending the bitmap gives a
# new address even when earlier positions were deleted. No integer conversion.
def suffix(mask: String) -> String:
  match mask:
    case SNil{}: "z"
    case SCon{c, rest}: SCon{'a', suffix(rest)}

def key(p: M.Principal, mask: String) -> String:
  M.prefix(p) ++ suffix(mask)

def saved(cancel: Bool, key: String) -> S.Action:
  match cancel:
    case False{}: S.Finish{D.VText{key}}
    case True{}: S.Refuse{D.VText{"cancelled"}}

def write_directory(+p: M.Principal, mask: String, done: S.Action) -> S.Action:
  +k = M.directory(p)
  S.Access{D.DefineRow{D.Application{"notes"}, k, M.fields(p, k, mask)}, r => done}

def create(+p: M.Principal, +mask: String, text: String, cancel: Bool) -> S.Action:
  +k = key(p, mask)
  S.Access{D.DefineRow{D.Application{"notes"}, k, M.fields(p, k, text)}, r =>
    write_directory(p, SCon{'+', mask}, saved(cancel, k))}

# A membership test over ONLY the private directory. Its address calculation
# depends on the suffix's length, so deleting a position never renames a note.
def contains(+p: M.Principal, mask: String, +wanted: String) -> Bool:
  match mask:
    case SNil{}: False{}
    case SCon{c, +rest}:
      (Char.is_eq(c, '+') && String.eq(key(p, rest), wanted)) || contains(p, rest, wanted)

def removed(+p: M.Principal, mask: String, +wanted: String) -> String:
  match mask:
    case SNil{}: ""
    case SCon{+c, +rest}:
      SCon{Bool.pick(Char, String.eq(key(p, rest), wanted), '-', c), removed(p, rest, wanted)}

def mutate_known(known: Bool, +p: M.Principal, +mask: String, +wanted: String, text: Maybe<&2, String>) -> S.Action:
  match known:
    case False{}: S.Refuse{D.VText{"unknown own note"}}
    case True{}:
      match text:
        case None{}:
          S.Access{D.RemoveRow{D.Application{"notes"}, wanted}, r =>
            write_directory(p, removed(p, mask, wanted), S.Finish{D.VText{wanted}})}
        case Some{t}:
          S.Access{D.DefineRow{D.Application{"notes"}, wanted, M.fields(p, wanted, t)}, r => S.Finish{D.VText{wanted}}}

def mutate(+p: M.Principal, +mask: String, +wanted: String, text: Maybe<&2, String>) -> S.Action:
  mutate_known(contains(p, mask, wanted), p, mask, wanted, text)

def view_known(known: Bool, +k: String) -> S.Action:
  match known:
    case False{}: S.Finish{D.VAbsent{}}
    case True{}: read(k, v => S.Finish{v})

# Listing reads every active note's owner/text, with no global enumeration and
# no existence tests on other owners. It returns complete note records.
def list(+p: M.Principal, mask: String, done: D.Value -> S.Action) -> S.Action:
  match mask:
    case SNil{}: done(D.VListEmpty{})
    case SCon{'+', +rest}:
      read(key(p, rest), item => list(p, rest, tail => done(D.VList{item, tail})))
    case SCon{c, rest}: list(p, rest, done)

def from_mask(+p: M.Principal, cmd: Command, +mask: String) -> S.Action:
  match cmd:
    case Create{t, cancel}: create(p, mask, t, cancel)
    case View{+k}: view_known(contains(p, mask, k), k)
    case Update{k, t}: mutate(p, mask, k, Some{t})
    case Remove{k}: mutate(p, mask, k, None{})
    case ListNotes{}: list(p, mask, v => S.Finish{v})
    case _: S.Refuse{D.VText{"ordinary command required"}}

def from_directory(+p: M.Principal, cmd: Command, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{D.VText{mask}}}: from_mask(p, cmd, mask)
    case _: S.Refuse{D.VText{"invalid directory"}}

def command(+p: M.Principal, cmd: Command) -> S.Action:
  S.Access{D.ReadCell{D.Application{"notes"}, M.directory(p), "text"}, r => from_directory(p, cmd, r)}

def count_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Count{n}}: D.VInt{0, U32.from_nat(n)}
    case _: D.VAbsent{}

def admin_command(p: Command) -> S.Action:
  match p:
    case ReadAny{k}: read(k, v => S.Finish{v})
    case CountAll{}: S.Access{D.CountRows{D.Application{"notes"}}, r => S.Finish{count_value(r)}}
    case _: S.Refuse{D.VText{"administrator read or count required"}}

def flags(admin: Bool, alice: Bool, bob: Bool, +args: D.Value) -> S.Action:
  match admin alice bob:
    case True{} _ _: admin_command(analyze(args))
    case False{} True{} _: command(M.Alice{}, analyze(args))
    case False{} False{} True{}: command(M.Bob{}, analyze(args))
    case False{} False{} False{}: S.Refuse{D.VText{"unknown principal"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{+id, kind} = ctx
  flags(String.eq(kind, "admin"), String.eq(id, "alice"), String.eq(id, "bob"), args)

def program() -> S.Program:
  S.Program{start}
