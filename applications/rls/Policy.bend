# Row security on ONE shared notes table plus one directory table per user.
# No implicit administrator exception; every law is checked before execution.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L

type Both<-P: Data, -Q: Data> is Data:
  Both{left: P, right: Q}

def starts(pre: String, k: String) -> Bool:
  match pre:
    case SNil{}: True{}
    case SCon{c, pt}:
      match k:
        case SNil{}: False{}
        case SCon{d, kt}: Char.is_eq(c, d) && starts(pt, kt)

# A note id names its owner: "alice/<anything>" or "bob/<anything>".
def key_owner(+k: String) -> String:
  Bool.pick(String, starts("alice/", k), "alice", Bool.pick(String, starts("bob/", k), "bob", ""))

def named(o: String) -> Bool:
  match o:
    case SNil{}: False{}
    case SCon{c, t}: True{}

def key_valid(+k: String) -> Bool:
  named(key_owner(k))

def dir_name(id: String) -> String:
  id ++ "_dir"

def fields(l: D.Row) -> List<&2, D.Field>:
  D.Row{k, fs} = l
  fs

# Every row of every table (notes and directories) carries its key's owner.
def Owner(+us: List<&2, D.Row>, name: String, +l: D.Row) -> Data:
  Both<{key_valid(D.row_key(l)) == True{} : Bool},
    Both<{D.find_field(fields(l), "owner") == Some{D.VText{key_owner(D.row_key(l))}} : Maybe<&2, D.Value>},
      {D.exists_row(D.find_row(us, key_owner(D.row_key(l)))) == True{} : Bool}>>

def Rows(+us: List<&2, D.Row>, +name: String, ls: List<&2, D.Row>) -> Data:
  match ls:
    case Nil{}: Unit
    case Con{l, rest}: Both<Owner(us, name, l), Rows(us, name, rest)>

def Tables(+us: List<&2, D.Row>, ts: List<&2, D.Table>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{D.Table{name, ls}, rest}: Both<Rows(us, name, ls), Tables(us, rest)>

def Owners(s: D.State) -> Data:
  D.State{ts, us} = s
  Tables(us, ts)

def ReadScope(admin: Bool, id: String, +key: String) -> Data:
  match admin:
    case True{}: Unit
    case False{}: Both<{key_owner(key) == id : String}, {key_valid(key) == True{} : Bool}>

def WriteScope(id: String, +key: String) -> Data:
  Both<{key_owner(key) == id : String}, {key_valid(key) == True{} : Bool}>

# Writes reach only the shared table and the caller's OWN directory.
def Writable(+id: String, +name: String) -> Data:
  {String.eq(name, "notes") || String.eq(name, dir_name(id)) == True{} : Bool}

# Admin enumerates only the three application tables; users only their own directory.
def KeysScope(admin: Bool, +id: String, +name: String) -> Data:
  match admin:
    case True{}: {String.eq(name, "notes") || String.eq(name, "alice_dir") || String.eq(name, "bob_dir") == True{} : Bool}
    case False{}: {name == dir_name(id) : String}

def Allowed(ctx: D.Context, op: D.Operation) -> Data:
  D.Context{+id, +kind} = ctx
  match op:
    case D.ReadCell{D.Application{name}, k, c}:
      Both<{name == "notes" : String}, ReadScope(String.eq(kind, "admin"), id, k)>
    case D.ViewExistence{D.Application{name}, k}:
      Both<{name == "notes" : String}, ReadScope(String.eq(kind, "admin"), id, k)>
    case D.CountRows{D.Application{name}}:
      Both<{name == "notes" : String}, {kind == "admin" : String}>
    case D.EnumerateKeys{D.Application{name}}:
      KeysScope(String.eq(kind, "admin"), id, name)
    case D.DefineRow{D.Application{+name}, +k, fs}:
      Both<Writable(id, name), Both<WriteScope(id, k),
        {D.find_field(fs, "owner") == Some{D.VText{key_owner(k)}} : Maybe<&2, D.Value>}>>
    case D.RemoveRow{D.Application{+name}, k}:
      Both<Writable(id, name), WriteScope(id, k)>
    case _: {False{} == True{} : Bool}

def AllAllowed(+ctx: D.Context, ts: List<&2, S.OperationEvent>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{S.OperationEvent{op, ef}, rest}: Both<Allowed(ctx, op), AllAllowed(ctx, rest)>

def Rule(h: S.Situation) -> Data:
  match h:
    case S.Stable{s}: Owners(s)
    case S.Executing{s, ctx, code, args, w, ts}: Both<Owners(w), AllAllowed(ctx, ts)>
    case S.Closed{s, ctx, code, args, w, ts, r}: Both<Owners(w), AllAllowed(ctx, ts)>

# Directory law. listed: the directory has a row at k; owned: the shared
# table has a row at k whose owner column is p.
def listed(rows: List<&2, D.Row>, +k: String) -> Bool:
  D.exists_row(D.find_row(rows, k))

def owner_is(v: Maybe<&2, D.Value>, +p: String) -> Bool:
  match v:
    case Some{D.VText{o}}: String.eq(o, p)
    case _: False{}

def row_owner(m: Maybe<&2, D.Row>, +p: String) -> Bool:
  match m:
    case None{}: False{}
    case Some{D.Row{k, fs}}: owner_is(D.find_field(fs, "owner"), p)

def owned(+p: String, rows: List<&2, D.Row>, +k: String) -> Bool:
  row_owner(D.find_row(rows, k), p)

def view(m: Maybe<&2, List<&2, D.Row>>) -> List<&2, D.Row>:
  match m:
    case None{}: Nil{}
    case Some{ls}: ls

def rows(+name: String, s: D.State) -> List<&2, D.Row>:
  view(D.rows_collection(D.Application{name}, s))

# For EVERY id k: k is in p's directory exactly when p owns the note at k.
def Agree(+p: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>) -> Type:
  @k: String -> {listed(ds, k) == owned(p, ns, k) : Bool}

def Directory(+s: D.State) -> Type:
  L.E<Agree("alice", rows(dir_name("alice"), s), rows("notes", s)),
    Agree("bob", rows(dir_name("bob"), s), rows("notes", s))>

# A Stable-state law. Publishing a success requires Valid(working), which
# includes this law, so every published state is exact; prefixes may be stale.
# (A Closed clause would repeat that obligation.)
def DirectoryRule(h: S.Situation) -> Type:
  match h:
    case S.Stable{s}: Directory(s)
    case S.Executing{s, ctx, code, args, w, ts}: Unit
    case S.Closed{s, ctx, code, args, w, ts, r}: Unit

def laws() -> S.Laws:
  S.MoreOneLaw{Rule, S.MoreOneLaw{DirectoryRule, S.NoneLaw{}}}

def config(e: D.Schema, lim: S.Limits, environment: String) -> S.Configuration:
  S.Configuration{e, laws(), lim, environment}
