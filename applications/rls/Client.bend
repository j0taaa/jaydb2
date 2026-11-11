import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Policy.bend as P

type Command is Data:
  Save{second: Bool, text: String, cancel: Bool}
  View{second: Bool}
  Remove{second: Bool}
  ListNotes{}
  ReadAny{key: String}
  CountAll{}
  Invalid{}

# false selects slot 1; true selects slot 2.
def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{"save"}, D.VList{D.VBool{b}, D.VList{D.VText{t}, D.VListEmpty{}}}}: Save{b, t, False{}}
    case D.VList{D.VText{"cancel"}, D.VList{D.VBool{b}, D.VList{D.VText{t}, D.VListEmpty{}}}}: Save{b, t, True{}}
    case D.VList{D.VText{"view"}, D.VList{D.VBool{b}, D.VListEmpty{}}}: View{b}
    case D.VList{D.VText{"remove"}, D.VList{D.VBool{b}, D.VListEmpty{}}}: Remove{b}
    case D.VList{D.VText{"list"}, D.VListEmpty{}}: ListNotes{}
    case D.VList{D.VText{"read"}, D.VList{D.VText{k}, D.VListEmpty{}}}: ReadAny{k}
    case D.VList{D.VText{"count"}, D.VListEmpty{}}: CountAll{}
    case _: Invalid{}

def fields(+key: String, text: String) -> List<&2, D.Field>:
  [D.Field{"id", D.VText{key}}, D.Field{"owner", D.VText{P.key_owner(key)}}, D.Field{"text", D.VText{text}}]

def read_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: v
    case _: D.VAbsent{}

def owner_received(r: S.Return) -> Maybe<&2, D.Value>:
  match r:
    case S.Datum{D.Cell{v}}: Some{v}
    case _: None{}

def detail(key: String, owner: D.Value, r: S.Return) -> D.Value:
  D.VRecord{"id", D.VText{key}, D.VRecord{"owner", owner,
    D.VRecord{"text", read_value(r), D.VRecordEmpty{}}}}

def resume(+key: String, owner: Maybe<&2, D.Value>) -> S.Action:
  match owner:
    case Some{v}:
      S.Access{D.ReadCell{D.Application{"notes"}, key, "text"}, r => S.Finish{detail(key, v, r)}}
    case None{}: S.Finish{D.VAbsent{}}

def read(+key: String) -> S.Action:
  S.Access{D.ReadCell{D.Application{"notes"}, key, "owner"}, r => resume(key, owner_received(r))}

def saved(cancel: Bool, key: String) -> S.Action:
  match cancel:
    case False{}: S.Finish{D.VText{key}}
    case True{}: S.Refuse{D.VText{"cancelled"}}

def exists(r: S.Return) -> Bool:
  match r:
    case S.Datum{D.Existence{b}}: b
    case _: False{}

def include(b: Bool, key: String, rest: D.Value) -> D.Value:
  match b:
    case False{}: rest
    case True{}: D.VList{D.VText{key}, rest}

# Exhaustive private listing: the invariant admits exactly these two slots.
def list(+first: String, +second: String) -> S.Action:
  S.Access{D.ViewExistence{D.Application{"notes"}, first}, a =>
    S.Access{D.ViewExistence{D.Application{"notes"}, second}, b =>
      S.Finish{include(exists(a), first, include(exists(b), second, D.VListEmpty{}))}}}

def command(+first: String, +second: String, p: Command) -> S.Action:
  match p:
    case Save{b, t, cancel}:
      +key = Bool.pick(String, b, second, first)
      S.Access{D.DefineRow{D.Application{"notes"}, key, fields(key, t)}, r => saved(cancel, key)}
    case View{b}: read(Bool.pick(String, b, second, first))
    case Remove{b}:
      +key = Bool.pick(String, b, second, first)
      S.Access{D.RemoveRow{D.Application{"notes"}, key}, r => S.Finish{D.VText{key}}}
    case ListNotes{}: list(first, second)
    case _: S.Refuse{D.VText{"ordinary command required"}}

def count_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Count{n}}: D.VInt{0, U32.from_nat(n)}
    case _: D.VAbsent{}

def admin_command(p: Command) -> S.Action:
  match p:
    case ReadAny{k}: read(k)
    case CountAll{}: S.Access{D.CountRows{D.Application{"notes"}}, r => S.Finish{count_value(r)}}
    case _: S.Refuse{D.VText{"administrator read or count required"}}

def flags(admin: Bool, alice: Bool, bob: Bool, +args: D.Value) -> S.Action:
  match admin alice bob:
    case True{} _ _: admin_command(analyze(args))
    case False{} True{} _: command("alice/1", "alice/2", analyze(args))
    case False{} False{} True{}: command("bob/1", "bob/2", analyze(args))
    case False{} False{} False{}: S.Refuse{D.VText{"unknown principal"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{+id, kind} = ctx
  flags(String.eq(kind, "admin"), String.eq(id, "alice"), String.eq(id, "bob"), args)

def program() -> S.Program:
  S.Program{start}
