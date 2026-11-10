# Public library proofs, including the retained whole-program read helpers.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Q
import ./Action.bend as A
import ./Proofs.bend as P
import ./Receipts.bend as Receipts
import ./ReceiptLaws.bend as ReceiptLaws
import ./Value.bend as V
import ./Int64.bend as I
import ./ComparisonProofs.bend as Comparison
import ./Int64Proofs.bend as Int64Proofs
import ./Int64Subtraction.bend as Int64Subtraction
import ./Int64Multiplication.bend as Int64Multiplication
import ./Int64DivisionProofs.bend as Int64DivisionProofs
import ./AggregateAverageProofs.bend as AggregateAverageProofs
import ./SummaryProofs.bend as SummaryProofs
import ./AggregateExtremaProofs.bend as AggregateExtremaProofs
import ./SequencePaginationProofs.bend as SequencePaginationProofs
import ./SequenceStabilityProofs.bend as SequenceStabilityProofs
import ./SequenceGroupOrder.bend as SequenceGroupOrder
import ./RelationProofs.bend as RelationProofs
import ./KeyDecodeProofs.bend as KeyDecodeProofs
import ./ValueScalarProofs.bend as ValueScalarProofs
import ./ValueListProofs.bend as ValueListProofs
import ./RecordCanonicalProofs.bend as RecordCanonicalProofs
import ./RecordShapeProofs.bend as RecordShapeProofs
import ./RecordLookupProofs.bend as RecordLookupProofs
import ./ReadAdapterProofs.bend as ReadAdapterProofs
import ./QuerySelectionProofs.bend as QuerySelectionProofs
import ./QueryCellVisitorProofs.bend as QueryCellVisitorProofs
import ./QueryFilterMapPositions.bend as QueryFilterMapPositions
import ./QueryReadPlanProperties.bend as QueryReadPlanProperties
import ./MutationOrderedProofs.bend as MutationOrderedProofs
import ./MutationWriteOnly.bend as MutationWriteOnly
import ./MutationPrefixProofs.bend as MutationPrefixProofs
import ./MutationPublicationProofs.bend as MutationPublicationProofs
import ./MutationBooleanProofs.bend as MutationBooleanProofs
import ./MutationCounterProofs.bend as MutationCounterProofs
import ./SummaryStoreProofs.bend as SummaryStoreProofs
import ./IndexKeyProofs.bend as IndexKeyProofs
import ./IndexEntryProofs.bend as IndexEntryProofs
import ./IndexActionProofs.bend as IndexActionProofs
import ./IndexRebuildTrace.bend as IndexRebuildTrace
import ./IndexScanProofs.bend as IndexScanProofs
import ./IndexSourceProofs.bend as IndexSourceProofs
import ./IndexRebuildProofs.bend as IndexRebuildProofs
import ./IndexMaintenanceProofs.bend as IndexMaintenanceProofs
import ./IndexClaimProofs.bend as IndexClaimProofs
import ./IndexLookupProofs.bend as IndexLookupProofs
import ./ReceiptLookupProofs.bend as ReceiptLookupProofs
import ./ReceiptWriteProofs.bend as ReceiptWriteProofs
import ./RowLookupProofs.bend as RowLookupProofs
import ./RowRemovalLookupProofs.bend as RowRemovalLookupProofs
import ./MutationStateShapeProofs.bend as MutationStateShapeProofs
import ./MutationValidatorProofs.bend as MutationValidatorProofs
import ./CollectionChangeCompositionProofs.bend as CollectionChangeCompositionProofs
import ../tests/library/VERIFY.bend as Extensions

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"tasks", "id", [
    D.Column{"completed", D.Boolean{}, False{}}, D.Column{"id", D.TextValue{}, False{}},
    D.Column{"note", D.TextValue{}, True{}}, D.Column{"title", D.TextValue{}, False{}}]}]}

def row(+key: String, title: String, done: Bool) -> D.Row:
  D.Row{key, [D.Field{"completed", D.VBool{done}}, D.Field{"id", D.VText{key}},
    D.Field{"note", D.VAbsent{}}, D.Field{"title", D.VText{title}}]}

def state() -> D.State:
  D.State{[D.Table{"tasks", [row("a", "First", False{}), row("b", "Second", True{})]}], Nil{}}

def projected(done: Maybe<&2, D.Value> -> S.Action, result: Q.Selection) -> S.Action:
  match result:
    case Q.Selected{D.VRecord{"completed", D.VBool{False{}}, D.VRecord{"title", title, D.VRecordEmpty{}}}}:
      done(Some{D.VRecord{"title", title, D.VRecordEmpty{}}})
    case Q.Selected{D.VRecord{"completed", D.VBool{True{}}, D.VRecord{"title", title, D.VRecordEmpty{}}}}:
      done(None{})
    case Q.MissingRow{}: done(None{})
    case _: S.Refuse{D.VAbsent{}}

def visit(collection: D.Collection, key: String, done: Maybe<&2, D.Value> -> S.Action) -> S.Action:
  Q.select(collection, key, ["completed", "title"], projected(done))

def query() -> S.Action:
  Q.filter_map(~D.Collection, ~visit, D.Application{"tasks"}, ["a", "b"], value => S.Finish{value})

def read_event(key: String, column: String, value: D.Value) -> S.OperationEvent:
  S.OperationEvent{D.ReadCell{D.Application{"tasks"}, key, column}, S.Reading{D.Cell{value}}}

law valid_state:
  {D.structure(schema(), state()) == True{} : Bool}
def valid_state(): {==}

# Both selected fields of BOTH rows remain, including the filtered-out row.
law filtered_projection_trace:
  {S.observe(5n, query(), schema(), state()) == S.Final{state(),
    [read_event("a", "completed", D.VBool{False{}}), read_event("a", "title", D.VText{"First"}),
     read_event("b", "completed", D.VBool{True{}}), read_event("b", "title", D.VText{"Second"})],
    S.Response{S.Success{}, D.VList{D.VRecord{"title", D.VText{"First"}, D.VRecordEmpty{}}, D.VListEmpty{}}}} : S.Trace}
def filtered_projection_trace(): {==}

def selection_value(result: Q.Selection) -> S.Action:
  match result:
    case Q.Selected{record}: S.Finish{record}
    case Q.MissingRow{}: S.Refuse{D.VText{"missing"}}
    case Q.InvalidFields{}: S.Refuse{D.VText{"invalid"}}
    case Q.UnexpectedReturn{}: S.Refuse{D.VText{"unexpected"}}

law absent_cell_is_a_field:
  {S.observe(2n, Q.select(D.Application{"tasks"}, "a", ["note"], selection_value), schema(), state()) ==
    S.Final{state(), [read_event("a", "note", D.VAbsent{})], S.Response{S.Success{},
      D.VRecord{"note", D.VAbsent{}, D.VRecordEmpty{}}}} : S.Trace}
def absent_cell_is_a_field(): {==}

law absent_field_lookup:
  {Q.field(D.VRecord{"note", D.VAbsent{}, D.VRecordEmpty{}}, "note") == Some{D.VAbsent{}} : Maybe<&2, D.Value>}
def absent_field_lookup(): {==}

law duplicate_fields_rejected_before_read:
  {S.observe(1n, Q.select(D.Application{"tasks"}, "a", ["title", "title"], selection_value), schema(), state()) ==
    S.Final{state(), Nil{}, S.Response{S.Refusal{}, D.VText{"invalid"}}} : S.Trace}
def duplicate_fields_rejected_before_read(): {==}

law invalid_field_name:
  {Q.fields_valid(["bad-name"]) == False{} : Bool}
def invalid_field_name(): {==}

law unordered_fields:
  {Q.fields_valid(["title", "completed"]) == False{} : Bool}
def unordered_fields(): {==}

law malformed_record_lookup:
  {Q.field(D.VRecord{"title", D.VText{"x"}, D.VRecord{"title", D.VText{"y"}, D.VRecordEmpty{}}}, "title") == None{} : Maybe<&2, D.Value>}
def malformed_record_lookup(): {==}

law unexpected_return:
  {Q.combine("title", S.UnitValue{}, Q.Selected{D.VRecordEmpty{}}) == Q.UnexpectedReturn{} : Q.Selection}
def unexpected_return(): {==}

law missing_row:
  {Q.combine("title", S.Datum{D.RowAbsent{}}, Q.Selected{D.VRecordEmpty{}}) == Q.MissingRow{} : Q.Selection}
def missing_row(): {==}

# The read actually resolves against schema/state; no policy premise is assumed.
law refusal_retains_real_read:
  {S.observe(2n, S.Access{D.ReadCell{D.Application{"tasks"}, "b", "title"}, r => S.Refuse{D.VAbsent{}}}, schema(), state()) ==
    S.Final{state(), [read_event("b", "title", D.VText{"Second"})], S.Response{S.Refusal{}, D.VAbsent{}}} : S.Trace}
def refusal_retains_real_read():
  P.read_then_refuse(schema(), state(), D.ReadCell{D.Application{"tasks"}, "b", "title"}, D.Cell{D.VText{"Second"}}, D.VAbsent{}, Nil{}, {==})

def after_first() -> D.State:
  D.State{[D.Table{"tasks", [row("a", "Changed", False{}), row("b", "Second", True{})]}], Nil{}}

def updates() -> S.Action:
  A.define_rows(D.Application{"tasks"}, [row("a", "Changed", False{}), D.Row{"bad", Nil{}}], S.Finish{D.VAbsent{}})

law second_write_data_error:
  {S.observe(3n, updates(), schema(), state()) == S.Final{after_first(),
    [S.OperationEvent{D.DefineRow{D.Application{"tasks"}, "a", [D.Field{"completed", D.VBool{False{}}},
      D.Field{"id", D.VText{"a"}}, D.Field{"note", D.VAbsent{}}, D.Field{"title", D.VText{"Changed"}}]}, S.Write{}},
     S.OperationEvent{D.DefineRow{D.Application{"tasks"}, "bad", Nil{}}, S.ErrorOfData{}}], S.Response{S.DataError{}, D.VAbsent{}}} : S.Trace}
def second_write_data_error(): {==}

law error_rolls_back_publication:
  {S.publish(S.Response{S.DataError{}, D.VAbsent{}}, state(), after_first()) == state() : D.State}
def error_rolls_back_publication(): {==}

def output(trace: S.Trace) -> D.Value:
  match trace:
    case S.Final{w, events, response}: S.response_value(response)
    case S.Prefix{w, events}: D.VAbsent{}

def main() -> D.Value:
  output(S.observe(5n, query(), schema(), state()))

# Reapply the comparison interfaces to arbitrary actual inputs.
law structural_equality_is_sound:
  for +a: D.Value
  for +b: D.Value
  for h: {V.equal(a, b) == True{} : Bool}
  {a == b : D.Value}
def structural_equality_is_sound(a, b, h):
  Comparison.equal_sound(a, b, h)

law signed_comparison_is_transitive:
  for +a: V.Int64
  for +b: V.Int64
  for +c: V.Int64
  for ab: {I.lt(a, b) == True{} : Bool}
  for bc: {I.lt(b, c) == True{} : Bool}
  {I.lt(a, c) == True{} : Bool}
def signed_comparison_is_transitive(a, b, c, ab, bc):
  Comparison.lt_transitive(a, b, c, ab, bc)

law signed_comparison_has_trichotomy:
  for +a: V.Int64
  for +b: V.Int64
  Comparison.Trichotomy(a, b)
def signed_comparison_has_trichotomy(a, b):
  Comparison.lt_trichotomy(a, b)

law minimum_integer_precedes_zero:
  {I.lt(V.Int64{2147483648, 0}, V.Int64{0, 0}) == True{} : Bool}
def minimum_integer_precedes_zero(): {==}

law maximum_integer_does_not_precede_zero:
  {I.lt(V.Int64{2147483647, 4294967295}, V.Int64{0, 0}) == False{} : Bool}
def maximum_integer_does_not_precede_zero(): {==}
