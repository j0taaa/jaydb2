# Ordinary CPS writes: no implicit reads beyond those explicitly below.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Action.bend as A
import ./Value.bend as V
import ./Int64.bend as I

def inserted(+c: D.Collection, +row: D.Row, done: Bool -> S.Action, r: S.Return) -> S.Action:
  D.Row{key, fs} = row
  match r:
    case S.Datum{D.Existence{False{}}}:
      S.Access{D.DefineRow{c, key, fs}, r => A.written(done(True{}), r)}
    case S.Datum{D.Existence{True{}}}: done(False{})
    case _: S.Refuse{D.VText{"unexpected existence return"}}

def insert_if_absent(+c: D.Collection, +row: D.Row, done: Bool -> S.Action) -> S.Action:
  D.Row{key, fs} = row
  S.Access{D.ViewExistence{c, key}, inserted(c, row, done)}

def remove_rows(+c: D.Collection, keys: List<&2, String>, done: S.Action) -> S.Action:
  match keys:
    case Nil{}: done
    case Con{key, rest}: S.Access{D.RemoveRow{c, key}, r => A.written(remove_rows(c, rest, done), r)}

def columns(+c: D.Collection, +key: String, fields: List<&2, D.Field>, done: S.Action) -> S.Action:
  match fields:
    case Nil{}: done
    case Con{D.Field{name, value}, rest}:
      S.Access{D.DefineColumn{c, key, name, value}, r => A.written(columns(c, key, rest, done), r)}

# A conditional read/replace; predicate is pure, reads are never erased.
def replace_choice(b: Bool, c: D.Collection, key: String, fs: List<&2, D.Field>, done: Bool -> S.Action) -> S.Action:
  match b:
    case False{}: done(False{})
    case True{}: S.Access{D.DefineRow{c, key, fs}, r => A.written(done(True{}), r)}


def replace_received(~accept: D.Observation -> Bool, +c: D.Collection, row: D.Row,
  done: Bool -> S.Action, r: S.Return) -> S.Action:
  D.Row{key, fs} = row
  match r:
    case S.Datum{obs}: replace_choice(accept(obs), c, key, fs, done)
    case _: S.Refuse{D.VText{"unexpected read return"}}

def replace_if(~accept: D.Observation -> Bool, +c: D.Collection, +row: D.Row,
  column: String, done: Bool -> S.Action) -> S.Action:
  D.Row{key, fs} = row
  S.Access{D.ReadCell{c, key, column}, replace_received(~accept, c, row, done)}

# Read, checked add, write. No implicit initialization of a missing counter.
def counter_result(c: D.Collection, key: String, column: String,
  result: Maybe<&2, V.Int64>, done: V.Int64 -> S.Action) -> S.Action:
  match result:
    case None{}: S.Refuse{D.VText{"counter overflow"}}
    case Some{+x}: S.Access{D.DefineColumn{c, key, column, V.int_value(x)}, r => A.written(done(x), r)}

def counter_read(c: D.Collection, key: String, column: String, delta: V.Int64,
  done: V.Int64 -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{D.VInt{h, l}}}: counter_result(c, key, column, I.add(V.Int64{h, l}, delta), done)
    case _: S.Refuse{D.VText{"counter missing or noninteger"}}

def counter_add(+c: D.Collection, +key: String, +column: String, delta: V.Int64,
  done: V.Int64 -> S.Action) -> S.Action:
  S.Access{D.ReadCell{c, key, column}, counter_read(c, key, column, delta, done)}

def next(c: D.Collection, key: String, column: String, done: V.Int64 -> S.Action) -> S.Action:
  counter_add(c, key, column, V.Int64{0, 1}, done)
