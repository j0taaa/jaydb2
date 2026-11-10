# Exact checked counter semantics. The numeric spec is independent unbounded
# Nat-difference addition; None excludes EVERY representable signed64 sum.
# A missing/noninteger observed cell is never initialized implicitly.
import Base
import ./MutationDecision.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ./Mutation.bend as M
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A

type CounterContext is Data:
  CounterContext{collection: D.Collection,key: String,column: String,delta: V.Int64}

def outcome(context: CounterContext,result: Maybe<&2,V.Int64>) -> B.Decision<V.Int64>:
  match context result:
    case CounterContext{collection,key,column,delta} Some{+sum}: B.MutationWrite{D.DefineColumn{collection,key,column,V.int_value(sum)},sum}
    case CounterContext{collection,key,column,delta} None{}: B.MutationRefuse{D.VText{"counter overflow"}}

def decode(context: CounterContext,r: S.Return) -> B.Decision<V.Int64>:
  match context r:
    case CounterContext{collection,key,column,+delta} S.Datum{D.Cell{D.VInt{high,low}}}: outcome(CounterContext{collection,key,column,delta},I.add(V.Int64{high,low},delta))
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VAbsent{}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VBool{b}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VText{text}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VListEmpty{}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VList{head,tail}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VRecordEmpty{}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Cell{D.VRecord{name,head,tail}}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.RowAbsent{}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Keys{keys}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Count{count}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.Datum{D.Existence{exists}}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}
    case CounterContext{collection,key,column,delta} S.UnitValue{}: B.MutationRefuse{D.VText{"counter missing or noninteger"}}

law actual_counter_result_has_the_exact_write_payload_or_overflow_refusal:
  for +collection: D.Collection
  for +key: String
  for +column: String
  for +delta: V.Int64
  for +result: Maybe<&2,V.Int64>
  for -done: V.Int64 -> S.Action
  {M.counter_result(collection,key,column,result,done) == B.action(~V.Int64,outcome(CounterContext{collection,key,column,delta},result),done) : S.Action}
def actual_counter_result_has_the_exact_write_payload_or_overflow_refusal(collection,key,column,delta,result,done):
  match result:
    case None{}: {==}
    case Some{sum}: {==}

law actual_counter_decoder_has_the_exact_decision_for_every_return:
  for +collection: D.Collection
  for +key: String
  for +column: String
  for +delta: V.Int64
  for -done: V.Int64 -> S.Action
  for +r: S.Return
  {M.counter_read(collection,key,column,delta,done,r) == B.action(~V.Int64,decode(CounterContext{collection,key,column,delta},r),done) : S.Action}
def actual_counter_decoder_has_the_exact_decision_for_every_return(collection,key,column,delta,done,r):
  match r:
    case S.Datum{D.Cell{D.VInt{+high,+low}}}: actual_counter_result_has_the_exact_write_payload_or_overflow_refusal(collection,key,column,delta,I.add(V.Int64{high,low},delta),done)
    case S.Datum{D.Cell{D.VAbsent{}}}: {==}
    case S.Datum{D.Cell{D.VBool{b}}}: {==}
    case S.Datum{D.Cell{D.VText{text}}}: {==}
    case S.Datum{D.Cell{D.VListEmpty{}}}: {==}
    case S.Datum{D.Cell{D.VList{head,tail}}}: {==}
    case S.Datum{D.Cell{D.VRecordEmpty{}}}: {==}
    case S.Datum{D.Cell{D.VRecord{name,head,tail}}}: {==}
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Keys{keys}}: {==}
    case S.Datum{D.Count{count}}: {==}
    case S.Datum{D.Existence{exists}}: {==}
    case S.UnitValue{}: {==}

def IntegerMeaning(+collection: D.Collection,+key: String,+column: String,+current: V.Int64,+delta: V.Int64,decision: B.Decision<V.Int64>) -> Type:
  match decision:
    case B.MutationWrite{op,+sum}: L.E<{op == D.DefineColumn{collection,key,column,V.int_value(sum)} : D.Operation},A.IntegerSum(A.integer(current),A.integer(delta),A.integer(sum))>
    case B.MutationRefuse{reason}: L.E<{reason == D.VText{"counter overflow"} : D.Value},@candidate: V.Int64 -> A.IntegerSum(A.integer(current),A.integer(delta),A.integer(candidate)) -> Empty>
    case B.MutationReturn{sum}: Empty

def checked_result_meaning(+collection: D.Collection,+key: String,+column: String,+current: V.Int64,+delta: V.Int64,+result: Maybe<&2,V.Int64>,exact: A.AdditionCorrect(current,delta,result)) -> IntegerMeaning(collection,key,column,current,delta,outcome(CounterContext{collection,key,column,delta},result)):
  match result:
    case Some{sum}: L.Both{{==},exact}
    case None{}: L.Both{{==},exact}

law every_integer_cell_counter_decision_is_exact_mathematical_addition_or_complete_overflow_rejection:
  for +collection: D.Collection
  for +key: String
  for +column: String
  for +current: V.Int64
  for +delta: V.Int64
  IntegerMeaning(collection,key,column,current,delta,outcome(CounterContext{collection,key,column,delta},I.add(current,delta)))
def every_integer_cell_counter_decision_is_exact_mathematical_addition_or_complete_overflow_rejection(collection,key,column,current,delta):
  checked_result_meaning(collection,key,column,current,delta,I.add(current,delta),A.checked_add_is_integer_addition(current,delta))

law actual_integer_cell_decoder_has_the_independent_integer_sum_and_exact_write:
  for +collection: D.Collection
  for +key: String
  for +column: String
  for +current: V.Int64
  for +delta: V.Int64
  IntegerMeaning(collection,key,column,current,delta,decode(CounterContext{collection,key,column,delta},S.Datum{D.Cell{V.int_value(current)}}))
def actual_integer_cell_decoder_has_the_independent_integer_sum_and_exact_write(collection,key,column,current,delta):
  match current:
    case V.Int64{high,low}: every_integer_cell_counter_decision_is_exact_mathematical_addition_or_complete_overflow_rejection(collection,key,column,V.Int64{high,low},delta)

law next_delta_is_exactly_the_independent_integer_one:
  {A.integer(V.Int64{0,1}) == A.Integer{1n,0n} : A.Integer}
def next_delta_is_exactly_the_independent_integer_one(): {==}
