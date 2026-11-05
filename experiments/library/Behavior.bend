import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../library/Sequence.bend as Q
import ../../library/Value.bend as V
import ../../library/Int64.bend as I
import ../../library/Aggregate.bend as G
import ../../library/Relation.bend as J
import ../../library/Mutation.bend as M
import ../../library/Read.bend as R
import ../../library/Index.bend as X
import ../../library/Summary.bend as H

def less(a: D.Value, b: D.Value) -> Bool:
  match a b:
    case D.VText{s} D.VText{t}: String.is_lt(s, t)
    case _ _: False{}

def key(v: D.Value) -> String:
  match v:
    case D.VText{s}: s
    case _: ""

def keep(v: D.Value) -> Bool:
  match v:
    case D.VBool{b}: b
    case _: False{}

law sorted_page:
  {Q.page(1n, 2n, Q.sort(~less, [D.VText{"c"}, D.VText{"a"}, D.VText{"b"}, D.VText{"a"}])) == [D.VText{"a"}, D.VText{"b"}] : List<&2, D.Value>}
def sorted_page(): {==}
law page_past_end:
  {Q.page(5n, 2n, [D.VAbsent{}]) == Nil{} : List<&2, D.Value>}
def page_past_end(): {==}
law filter_values:
  {Q.filter(~keep, [D.VBool{False{}}, D.VBool{True{}}, D.VAbsent{}]) == [D.VBool{True{}}] : List<&2, D.Value>}
def filter_values(): {==}
law grouping_duplicates:
  {Q.group(~key, [D.VText{"a"}, D.VText{"b"}, D.VText{"a"}]) == [Q.Group{"a", [D.VText{"a"}, D.VText{"a"}]}, Q.Group{"b", [D.VText{"b"}]}] : List<&2, Q.Group>}
def grouping_duplicates(): {==}
law join_multiplicity:
  {J.inner(~key, ~key, [D.VText{"a"}, D.VText{"x"}], [D.VText{"a"}, D.VText{"a"}]) == [D.VList{D.VText{"a"}, D.VList{D.VText{"a"}, D.VListEmpty{}}}, D.VList{D.VText{"a"}, D.VList{D.VText{"a"}, D.VListEmpty{}}}] : List<&2, D.Value>}
def join_multiplicity(): {==}
law left_join_missing:
  {J.left_join(~key, ~key, [D.VText{"x"}], Nil{}) == [D.VList{D.VText{"x"}, D.VList{D.VAbsent{}, D.VListEmpty{}}}] : List<&2, D.Value>}
def left_join_missing(): {==}
law aggregate_signed:
  {G.sum([V.Int64{0, 2}, V.Int64{4294967295, 4294967295}]) == Some{V.Int64{0, 1}} : Maybe<&2, V.Int64>}
def aggregate_signed(): {==}
law aggregate_overflow:
  {G.sum([V.Int64{0, 1}, V.Int64{2147483647, 4294967295}]) == None{} : Maybe<&2, V.Int64>}
def aggregate_overflow(): {==}
law summary_signed:
  {H.compute([V.Int64{0, 2}, V.Int64{4294967295, 4294967295}]) == Some{H.Stats{V.Int64{0, 2}, V.Int64{0, 1}}} : Maybe<&2, H.Stats>}
def summary_signed(): {==}

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"counter", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"n", D.Integer{}, False{}}]},
    D.SchemaTable{"index", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"target", D.TextValue{}, False{}}, D.Column{"value", D.TextValue{}, False{}}]}]}

def counter(n: V.Int64) -> D.Row:
  D.Row{"seq", [D.Field{"id", D.VText{"seq"}}, D.Field{"n", V.int_value(n)}]}

def state(n: V.Int64) -> D.State:
  D.State{[D.Table{"counter", [counter(n)]}, D.Table{"index", Nil{}}], Nil{}}

law state_valid:
  {D.structure(schema(), state(V.Int64{0, 0})) == True{} : Bool}
def state_valid(): {==}
law counter_prefix:
  {S.observe(1n, M.next(D.Application{"counter"}, "seq", "n", x => S.Finish{V.int_value(x)}), schema(), state(V.Int64{0, 4294967295})) == S.Prefix{state(V.Int64{0, 4294967295}), [S.OperationEvent{D.ReadCell{D.Application{"counter"}, "seq", "n"}, S.Reading{D.Cell{D.VInt{0, 4294967295}}}}]} : S.Trace}
def counter_prefix(): {==}
law counter_carry_write:
  {S.observe(3n, M.next(D.Application{"counter"}, "seq", "n", x => S.Finish{V.int_value(x)}), schema(), state(V.Int64{0, 4294967295})) == S.Final{state(V.Int64{1, 0}), [S.OperationEvent{D.ReadCell{D.Application{"counter"}, "seq", "n"}, S.Reading{D.Cell{D.VInt{0, 4294967295}}}}, S.OperationEvent{D.DefineColumn{D.Application{"counter"}, "seq", "n", D.VInt{1, 0}}, S.Write{}}], S.Response{S.Success{}, D.VInt{1, 0}}} : S.Trace}
def counter_carry_write(): {==}
law counter_overflow_no_write:
  {S.observe(3n, M.next(D.Application{"counter"}, "seq", "n", x => S.Finish{V.int_value(x)}), schema(), state(V.Int64{2147483647, 4294967295})) == S.Final{state(V.Int64{2147483647, 4294967295}), [S.OperationEvent{D.ReadCell{D.Application{"counter"}, "seq", "n"}, S.Reading{D.Cell{D.VInt{2147483647, 4294967295}}}}], S.Response{S.Refusal{}, D.VText{"counter overflow"}}} : S.Trace}
def counter_overflow_no_write(): {==}

def claim_twice() -> S.Action:
  X.claim(D.Application{"index"}, ["category", "same"], "first", b =>
    X.claim(D.Application{"index"}, ["category", "same"], "second", b => S.Finish{D.VBool{b}}))

def final_value(p: S.Trace) -> D.Value:
  match p:
    case S.Final{s, events, S.Response{status, value}}: value
    case S.Prefix{s, events}: D.VAbsent{}

law unique_conflict:
  {final_value(S.observe(5n, claim_twice(), schema(), state(V.Int64{0, 0}))) == D.VBool{False{}} : D.Value}
def unique_conflict(): {==}

# Nonunique entries differ by target; equality scan returns both targets.
def nonunique_read() -> S.Action:
  X.rebuild(D.Application{"index"}, [X.nonunique(["tag"], "a"), X.nonunique(["tag"], "b"), X.nonunique(["other"], "c")],
    X.lookup_many(D.Application{"index"}, ["tag"], v => S.Finish{v}))

law nonunique_rebuild_query:
  {final_value(S.observe(15n, nonunique_read(), schema(), state(V.Int64{0, 0}))) == D.VList{D.VText{"a"}, D.VList{D.VText{"b"}, D.VListEmpty{}}} : D.Value}
def nonunique_rebuild_query(): {==}
