# Optional ordinary-table helpers. The caller supplies policy and continuations.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

# Separate fields are compared exactly: no hash, normalization, or handle ID.
def matches(+operation: String, +input: String, op: String, value: String) -> Bool:
  String.eq(operation, op) && String.eq(input, value)

def written(next: S.Action, r: S.Return) -> S.Action:
  match r:
    case S.UnitValue{}: next
    case _: S.Refuse{D.VText{"unexpected write return"}}

def lookup(owner: String, request: String, done: S.Return -> S.Action) -> S.Action:
  S.Access{D.ReadCell{D.Application{owner}, request, "input"}, done}

# A single full-row write; it neither authenticates nor publishes a transaction.
def put(owner: String, request: String, fields: List<&2, D.Field>,
  next: S.Action) -> S.Action:
  S.Access{D.DefineRow{D.Application{owner}, request, fields}, written(next)}

# Bound lookup with caller-selected operation-specific miss and result handlers.
# Reads input, then operation/version, then result; no hit skips these accesses.
def operation_match(ok: Bool, owner: String, key: String,
  done: S.Return -> S.Action) -> S.Action:
  match ok:
    case True{}: S.Access{D.ReadCell{D.Application{owner}, key, "result"}, done}
    case False{}: S.Refuse{D.VText{"request conflict"}}

type Lookup is Data:
  Missing{}
  StoredText{value: String}
  Unexpected{}

def observed(r: S.Return) -> Lookup:
  match r:
    case S.Datum{D.RowAbsent{}}: Missing{}
    case S.Datum{D.Cell{D.VText{value}}}: StoredText{value}
    case _: Unexpected{}

def operation_value(+owner: String, +key: String, expected: String,
  done: S.Return -> S.Action, value: Lookup) -> S.Action:
  match value:
    case StoredText{actual}: operation_match(String.eq(actual, expected), owner, key, done)
    case Missing{}: S.Refuse{D.VText{"invalid receipt"}}
    case Unexpected{}: S.Refuse{D.VText{"invalid receipt"}}

def operation_seen(owner: String, key: String, expected: String,
  done: S.Return -> S.Action, r: S.Return) -> S.Action:
  operation_value(owner, key, expected, done, observed(r))

def input_match(ok: Bool, +owner: String, +key: String, operation: String,
  done: S.Return -> S.Action) -> S.Action:
  match ok:
    case True{}:
      S.Access{D.ReadCell{D.Application{owner}, key, "operation"}, operation_seen(owner, key, operation, done)}
    case False{}: S.Refuse{D.VText{"request conflict"}}

def input_value(+owner: String, +key: String, operation: String, input: String,
  missing: S.Action, done: S.Return -> S.Action, value: Lookup) -> S.Action:
  match value:
    case Missing{}: missing
    case StoredText{actual}: input_match(String.eq(actual, input), owner, key, operation, done)
    case Unexpected{}: S.Refuse{D.VText{"invalid receipt"}}

def input_seen(owner: String, key: String, operation: String, input: String,
  missing: S.Action, done: S.Return -> S.Action, r: S.Return) -> S.Action:
  input_value(owner, key, operation, input, missing, done, observed(r))

def bound(owner: String, key: String, operation: String, input: String,
  missing: S.Action, done: S.Return -> S.Action) -> S.Action:
  +owner = owner
  +key = key
  lookup(owner, key, input_seen(owner, key, operation, input, missing, done))
