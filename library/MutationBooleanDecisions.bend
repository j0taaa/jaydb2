# Pure decision meanings for insertion, predicate replacement and structural
# compare/exchange. The complete new row is retained, never only the read cell.
import Base
import ./MutationDecision.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Mutation.bend as M
import ./Value.bend as V
import ./ComparisonProofs.bend as Equality

type RowContext is Data:
  RowContext{collection: D.Collection,row: D.Row}

type CompareContext is Data:
  CompareContext{collection: D.Collection,row: D.Row,expected: D.Value}

def choice(context: RowContext,accept: Bool) -> B.Decision<Bool>:
  match context accept:
    case RowContext{collection,D.Row{key,fields}} True{}: B.MutationWrite{D.DefineRow{collection,key,fields},True{}}
    case RowContext{collection,row} False{}: B.MutationReturn{False{}}

def insertion(context: RowContext,r: S.Return) -> B.Decision<Bool>:
  match r:
    case S.Datum{D.Existence{False{}}}: choice(context,True{})
    case S.Datum{D.Existence{True{}}}: choice(context,False{})
    case S.Datum{D.Cell{value}}: B.MutationRefuse{D.VText{"unexpected existence return"}}
    case S.Datum{D.RowAbsent{}}: B.MutationRefuse{D.VText{"unexpected existence return"}}
    case S.Datum{D.Keys{keys}}: B.MutationRefuse{D.VText{"unexpected existence return"}}
    case S.Datum{D.Count{count}}: B.MutationRefuse{D.VText{"unexpected existence return"}}
    case S.UnitValue{}: B.MutationRefuse{D.VText{"unexpected existence return"}}

def replacement(~accept: D.Observation -> Bool,context: RowContext,r: S.Return) -> B.Decision<Bool>:
  match r:
    case S.Datum{observation}: choice(context,accept(observation))
    case S.UnitValue{}: B.MutationRefuse{D.VText{"unexpected read return"}}

def comparison(context: CompareContext,r: S.Return) -> B.Decision<Bool>:
  match context r:
    case CompareContext{collection,row,expected} S.Datum{D.Cell{value}}: choice(RowContext{collection,row},V.equal(value,expected))
    case CompareContext{collection,row,expected} S.Datum{D.RowAbsent{}}: B.MutationReturn{False{}}
    case CompareContext{collection,row,expected} S.Datum{D.Keys{keys}}: B.MutationRefuse{D.VText{"unexpected compare return"}}
    case CompareContext{collection,row,expected} S.Datum{D.Count{count}}: B.MutationRefuse{D.VText{"unexpected compare return"}}
    case CompareContext{collection,row,expected} S.Datum{D.Existence{exists}}: B.MutationRefuse{D.VText{"unexpected compare return"}}
    case CompareContext{collection,row,expected} S.UnitValue{}: B.MutationRefuse{D.VText{"unexpected compare return"}}

law actual_replace_choice_matches_exact_full_row_write_or_false_handoff:
  for +collection: D.Collection
  for +row: D.Row
  for +accept: Bool
  for -done: Bool -> S.Action
  {M.replace_choice(accept,collection,D.row_key(row),row_fields(row),done) == B.action(~Bool,choice(RowContext{collection,row},accept),done) : S.Action}

def row_fields(row: D.Row) -> List<&2,D.Field>:
  match row:
    case D.Row{key,fields}: fields

def actual_replace_choice_matches_exact_full_row_write_or_false_handoff(collection,row,accept,done):
  match row accept:
    case D.Row{key,fields} True{}: {==}
    case D.Row{key,fields} False{}: {==}

law actual_insert_decoder_has_the_exact_decision_for_every_return:
  for +collection: D.Collection
  for +row: D.Row
  for -done: Bool -> S.Action
  for +r: S.Return
  {M.inserted(collection,row,done,r) == B.action(~Bool,insertion(RowContext{collection,row},r),done) : S.Action}
def actual_insert_decoder_has_the_exact_decision_for_every_return(collection,row,done,r):
  match row r:
    case D.Row{key,fields} S.Datum{D.Existence{True{}}}: {==}
    case D.Row{key,fields} S.Datum{D.Existence{False{}}}: {==}
    case D.Row{key,fields} S.Datum{D.Cell{value}}: {==}
    case D.Row{key,fields} S.Datum{D.RowAbsent{}}: {==}
    case D.Row{key,fields} S.Datum{D.Keys{keys}}: {==}
    case D.Row{key,fields} S.Datum{D.Count{count}}: {==}
    case D.Row{key,fields} S.UnitValue{}: {==}

law actual_predicate_replacement_decoder_has_the_exact_decision_for_every_return:
  for ~accept: D.Observation -> Bool
  for +collection: D.Collection
  for +row: D.Row
  for -done: Bool -> S.Action
  for +r: S.Return
  {M.replace_received(~accept,collection,row,done,r) == B.action(~Bool,replacement(~accept,RowContext{collection,row},r),done) : S.Action}
def actual_predicate_replacement_decoder_has_the_exact_decision_for_every_return(accept,collection,row,done,r):
  match row r:
    case D.Row{+key,+fields} S.Datum{+observation}: actual_replace_choice_matches_exact_full_row_write_or_false_handoff(collection,D.Row{key,fields},accept(observation),done)
    case D.Row{key,fields} S.UnitValue{}: {==}

law actual_compare_exchange_decoder_has_the_exact_decision_for_every_return:
  for +collection: D.Collection
  for +row: D.Row
  for +expected: D.Value
  for -done: Bool -> S.Action
  for +r: S.Return
  {M.cas_received(collection,row,expected,done,r) == B.action(~Bool,comparison(CompareContext{collection,row,expected},r),done) : S.Action}
def actual_compare_exchange_decoder_has_the_exact_decision_for_every_return(collection,row,expected,done,r):
  match row r:
    case D.Row{+key,+fields} S.Datum{D.Cell{+value}}: actual_replace_choice_matches_exact_full_row_write_or_false_handoff(collection,D.Row{key,fields},V.equal(value,expected),done)
    case D.Row{key,fields} S.Datum{D.RowAbsent{}}: {==}
    case D.Row{key,fields} S.Datum{D.Keys{keys}}: {==}
    case D.Row{key,fields} S.Datum{D.Count{count}}: {==}
    case D.Row{key,fields} S.Datum{D.Existence{exists}}: {==}
    case D.Row{key,fields} S.UnitValue{}: {==}

# Independent structural equality, not just truth of the implementation's
# comparator. A missing row is separately NEVER a compare/exchange write.
def ExactComparison(+value: D.Value,+expected: D.Value,decision: B.Decision<Bool>) -> Type:
  match decision:
    case B.MutationWrite{op,True{}}: {value == expected : D.Value}
    case B.MutationReturn{False{}}: {value == expected : D.Value} -> Empty
    case B.MutationWrite{op,False{}}: Empty
    case B.MutationReturn{True{}}: Empty
    case B.MutationRefuse{reason}: Empty

def exact_comparison_case(+collection: D.Collection,+row: D.Row,+value: D.Value,+expected: D.Value,equal: Bool,actual: {V.equal(value,expected) == equal : Bool}) -> ExactComparison(value,expected,choice(RowContext{collection,row},equal)):
  match row equal:
    case D.Row{key,fields} True{}: Equality.equal_sound(value,expected,actual)
    case D.Row{key,fields} False{}: Equality.unequal_values_differ(value,expected,actual)

law actual_compare_exchange_cell_decision_uses_literal_value_equality:
  for +collection: D.Collection
  for +row: D.Row
  for +value: D.Value
  for +expected: D.Value
  ExactComparison(value,expected,comparison(CompareContext{collection,row,expected},S.Datum{D.Cell{value}}))
def actual_compare_exchange_cell_decision_uses_literal_value_equality(collection,row,value,expected):
  exact_comparison_case(collection,row,value,expected,V.equal(value,expected),{==})
