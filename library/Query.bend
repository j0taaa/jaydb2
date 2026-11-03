# Optional ordinary Action composition; no state is available here.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

type Selection is Data:
  Selected{record: D.Value}
  MissingRow{}
  InvalidFields{}
  UnexpectedReturn{}

# Require canonical input instead of sorting or dropping duplicates.
def later(name: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{next, rest}: String.is_lt(name, next)

def fields_valid(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{+name, +rest}:
      D.name_valid(name) && later(name, rest) && fields_valid(rest)

def prepend(name: String, value: D.Value, result: Selection) -> Selection:
  match result:
    case Selected{record}: Selected{D.VRecord{name, value, record}}
    case MissingRow{}: MissingRow{}
    case InvalidFields{}: InvalidFields{}
    case UnexpectedReturn{}: UnexpectedReturn{}

def combine(name: String, r: S.Return, result: Selection) -> Selection:
  match r:
    case S.Datum{D.Cell{value}}: prepend(name, value, result)
    case S.Datum{D.RowAbsent{}}: MissingRow{}
    case _: UnexpectedReturn{}

def received(name: String, done: Selection -> S.Action,
  next: (Selection -> S.Action) -> S.Action, r: S.Return) -> S.Action:
  next(result => done(combine(name, r, result)))

# Internal composition for a validated field list.
def read_fields(+collection: D.Collection, +key: String,
  xs: List<&2, String>, done: Selection -> S.Action) -> S.Action:
  match xs:
    case Nil{}: done(Selected{D.VRecordEmpty{}})
    case Con{+name, rest}:
      S.Access{D.ReadCell{collection, key, name}, received(name, done, next => read_fields(collection, key, rest, next))}

def select_valid(valid: Bool, collection: D.Collection, key: String,
  xs: List<&2, String>, done: Selection -> S.Action) -> S.Action:
  match valid:
    case True{}: read_fields(collection, key, xs, done)
    case False{}: done(InvalidFields{})

def select(collection: D.Collection, key: String, +xs: List<&2, String>,
  done: Selection -> S.Action) -> S.Action:
  select_valid(fields_valid(xs), collection, key, xs, done)

# None is different from a present VAbsent field. The input is a record value,
# not database state; malformed records and duplicate names are rejected.
def find_field(record: D.Value, +name: String) -> Maybe<&2, D.Value>:
  match record:
    case D.VRecord{n, v, rest}:
      Bool.pick(Maybe<&2, D.Value>, String.eq(n, name), Some{v}, find_field(rest, name))
    case _: None{}

def field_valid(valid: Bool, record: D.Value, name: String) -> Maybe<&2, D.Value>:
  match valid:
    case False{}: None{}
    case True{}: find_field(record, name)

def field(+record: D.Value, name: String) -> Maybe<&2, D.Value>:
  field_valid(D.value_valid(record), record, name)

# visit reads through Action and returns None to filter or Some to project.
# Keys and output keep their supplied order, including repetitions.
def include(item: Maybe<&2, D.Value>, tail: D.Value) -> D.Value:
  match item:
    case None{}: tail
    case Some{value}: D.VList{value, tail}

def filter_map(~Env: Data,
  ~visit: Env -> String -> (Maybe<&2, D.Value> -> S.Action) -> S.Action,
  +env: Env, xs: List<&2, String>, done: D.Value -> S.Action) -> S.Action:
  match xs:
    case Nil{}: done(D.VListEmpty{})
    case Con{key, rest}:
      visit(env, key, +item => filter_map(~Env, ~visit, env, rest, tail => done(include(item, tail))))
