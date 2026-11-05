# Materialize an explicitly computed summary in an ordinary table.
# Schema count:integer,id:text,total:integer. No triggers or hidden source reads.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Value.bend as V
import ./Int64.bend as I
import ./Action.bend as A

type Stats is Data:
  Stats{count: V.Int64, total: V.Int64}

def added_count(result: Maybe<&2, V.Int64>, total: Maybe<&2, V.Int64>) -> Maybe<&2, Stats>:
  match result total:
    case Some{n} Some{s}: Some{Stats{n, s}}
    case _ _: None{}

def add(x: V.Int64, tail: Maybe<&2, Stats>) -> Maybe<&2, Stats>:
  match tail:
    case None{}: None{}
    case Some{Stats{n, s}}: added_count(I.increment(n), I.add(x, s))

def compute(xs: List<&2, V.Int64>) -> Maybe<&2, Stats>:
  match xs:
    case Nil{}: Some{Stats{V.Int64{0, 0}, V.Int64{0, 0}}}
    case Con{x, rest}: add(x, compute(rest))

def row(+key: String, stats: Stats) -> D.Row:
  Stats{n, s} = stats
  D.Row{key, [D.Field{"count", V.int_value(n)}, D.Field{"id", D.VText{key}}, D.Field{"total", V.int_value(s)}]}

def store_result(c: D.Collection, key: String, result: Maybe<&2, Stats>, done: S.Action) -> S.Action:
  match result:
    case None{}: S.Refuse{D.VText{"summary overflow"}}
    case Some{stats}: A.define_rows(c, [row(key, stats)], done)

def store(c: D.Collection, key: String, values: List<&2, V.Int64>, done: S.Action) -> S.Action:
  store_result(c, key, compute(values), done)
