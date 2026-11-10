# Independent DATA meaning of a requested field list and supplied Return stream.
# The first non-cell return determines status. Field names and cell payloads
# are materialized separately in original order; no Action or Query.combine
# appears in this model's definitions.
import Base
import ./ValueScalarProofs.bend as Scalar
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Query
import ../proof/Foundations.bend as F

type Problem is Data:
  Clear{}
  Absent{}
  Unexpected{}

def head_problem(reply: S.Return,tail: Problem) -> Problem:
  match reply:
    case S.Datum{D.Cell{value}}: tail
    case S.Datum{D.RowAbsent{}}: Absent{}
    case S.Datum{D.Keys{xs}}: Unexpected{}
    case S.Datum{D.Count{n}}: Unexpected{}
    case S.Datum{D.Existence{b}}: Unexpected{}
    case S.UnitValue{}: Unexpected{}

def payload(reply: S.Return) -> D.Value:
  match reply:
    case S.Datum{D.Cell{value}}: value
    case S.Datum{D.RowAbsent{}}: D.VAbsent{}
    case S.Datum{D.Keys{xs}}: D.VAbsent{}
    case S.Datum{D.Count{n}}: D.VAbsent{}
    case S.Datum{D.Existence{b}}: D.VAbsent{}
    case S.UnitValue{}: D.VAbsent{}

def problem(~Env: Data,~reply: Env -> Nat -> S.Return,+env: Env,names: List<&2,String>,+index: Nat) -> Problem:
  match names:
    case Nil{}: Clear{}
    case Con{name,tail}: head_problem(reply(env,index),problem(~Env,~reply,env,tail,1n+index))

def record(~Env: Data,~reply: Env -> Nat -> S.Return,+env: Env,names: List<&2,String>,+index: Nat) -> D.Value:
  match names:
    case Nil{}: D.VRecordEmpty{}
    case Con{name,tail}: D.VRecord{name,payload(reply(env,index)),record(~Env,~reply,env,tail,1n+index)}

def render(problem: Problem,record: D.Value) -> Query.Selection:
  match problem:
    case Clear{}: Query.Selected{record}
    case Absent{}: Query.MissingRow{}
    case Unexpected{}: Query.UnexpectedReturn{}

def expected(~Env: Data,~reply: Env -> Nat -> S.Return,+env: Env,+index: Nat,+names: List<&2,String>) -> Query.Selection:
  render(problem(~Env,~reply,env,names,index),record(~Env,~reply,env,names,index))

def count(names: List<&2,String>) -> Nat:
  match names:
    case Nil{}: 0n
    case Con{name,tail}: 1n+count(tail)

def operations(+collection: D.Collection,+key: String,names: List<&2,String>) -> List<&2,D.Operation>:
  match names:
    case Nil{}: Nil{}
    case Con{name,tail}: Con{D.ReadCell{collection,key,name},operations(collection,key,tail)}

# This is a proved bridge to the actual combiner, not the model definition.
law independently_classified_and_materialized_selection_obeys_the_actual_combiner:
  for +name: String
  for +returned: S.Return
  for +later_problem: Problem
  for +later_record: D.Value
  {render(head_problem(returned,later_problem),D.VRecord{name,payload(returned),later_record}) == Query.combine(name,returned,render(later_problem,later_record)) : Query.Selection}
def independently_classified_and_materialized_selection_obeys_the_actual_combiner(name,returned,later_problem,later_record):
  match returned later_problem:
    case S.Datum{D.Cell{value}} Clear{}: {==}
    case S.Datum{D.Cell{value}} Absent{}: {==}
    case S.Datum{D.Cell{value}} Unexpected{}: {==}
    case S.Datum{D.RowAbsent{}} later_problem: {==}
    case S.Datum{D.Keys{xs}} later_problem: {==}
    case S.Datum{D.Count{n}} later_problem: {==}
    case S.Datum{D.Existence{b}} later_problem: {==}
    case S.UnitValue{} later_problem: {==}

law independent_selection_meaning_has_exact_head_and_tail_composition:
  for ~Env: Data
  for ~reply: Env -> Nat -> S.Return
  for +env: Env
  for +index: Nat
  for +name: String
  for +tail: List<&2,String>
  {expected(~Env,~reply,env,index,Con{name,tail}) == Query.combine(name,reply(env,index),expected(~Env,~reply,env,1n+index,tail)) : Query.Selection}
def independent_selection_meaning_has_exact_head_and_tail_composition(Env,reply,env,index,name,tail):
  independently_classified_and_materialized_selection_obeys_the_actual_combiner(name,reply(env,index),problem(~Env,~reply,env,tail,1n+index),record(~Env,~reply,env,tail,1n+index))

# This contract is local to returned cell payloads. Unexpected/missing returns
# use a valid absent placeholder in the materialization, but control status
# still excludes them from a Selected result.
def PayloadsValid(~Env: Data,~reply: Env -> Nat -> S.Return,+env: Env,names: List<&2,String>,+index: Nat) -> Data:
  match names:
    case Nil{}: Unit
    case Con{name,tail}: Scalar.Both<{D.value_valid(payload(reply(env,index))) == True{} : Bool},PayloadsValid(~Env,~reply,env,tail,1n+index)>

law materialized_record_next_name_is_exactly_the_requested_next_name:
  for ~Env: Data
  for ~reply: Env -> Nat -> S.Return
  for +env: Env
  for +index: Nat
  for +previous: String
  for +names: List<&2,String>
  {D.record_later(record(~Env,~reply,env,names,index),previous) == Query.later(previous,names) : Bool}
def materialized_record_next_name_is_exactly_the_requested_next_name(Env,reply,env,index,previous,names):
  match names:
    case Nil{}: {==}
    case Con{name,tail}: {==}

law valid_names_and_returned_payloads_materialize_an_exact_canonical_record:
  for ~Env: Data
  for ~reply: Env -> Nat -> S.Return
  for +env: Env
  for +names: List<&2,String>
  for +index: Nat
  for +valid_names: {Query.fields_valid(names) == True{} : Bool}
  for valid_payloads: PayloadsValid(~Env,~reply,env,names,index)
  {D.value_valid(record(~Env,~reply,env,names,index)) == True{} : Bool}
def valid_names_and_returned_payloads_materialize_an_exact_canonical_record(Env,reply,env,names,index,valid_names,valid_payloads):
  match names valid_payloads:
    case Nil{} Unit{}: {==}
    case Con{+name,+tail} Scalar.Both{value,rest}:
      +head_valid = F.and_boolean_left(D.name_valid(name) && Query.later(name,tail),Query.fields_valid(tail),valid_names)
      F.and_boolean_intro(D.name_valid(name) && D.value_valid(payload(reply(env,index))) && D.record_later(record(~Env,~reply,env,tail,1n+index),name),D.value_valid(record(~Env,~reply,env,tail,1n+index)),
        F.and_boolean_intro(D.name_valid(name) && D.value_valid(payload(reply(env,index))),D.record_later(record(~Env,~reply,env,tail,1n+index),name),
          F.and_boolean_intro(D.name_valid(name),D.value_valid(payload(reply(env,index))),F.and_boolean_left(D.name_valid(name),Query.later(name,tail),head_valid),value),
          Equal.trans(Bool,D.record_later(record(~Env,~reply,env,tail,1n+index),name),Query.later(name,tail),True{},materialized_record_next_name_is_exactly_the_requested_next_name(~Env,~reply,env,1n+index,name,tail),F.and_boolean_right(D.name_valid(name),Query.later(name,tail),head_valid))),
        valid_names_and_returned_payloads_materialize_an_exact_canonical_record(~Env,~reply,env,tail,1n+index,F.and_boolean_right(D.name_valid(name) && Query.later(name,tail),Query.fields_valid(tail),valid_names),rest))
