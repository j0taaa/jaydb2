# Exact public access constructors and complete Return decoding tables. An
# arbitrary continuation is invoked only for the named accepted Return shape;
# its later behavior is not claimed to be read-only or a single operation.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Read.bend as Read
import ./Query.bend as Query
import ./ReadProgram.bend as Program

law keys_emits_exactly_the_named_initial_access:
  for c: D.Collection
  for -done: List<&2,String> -> S.Action
  {Read.keys(c,done) == S.Access{D.EnumerateKeys{c},Read.keys_return(done)} : S.Action}
def keys_emits_exactly_the_named_initial_access(c,done): {==}

law exists_emits_exactly_the_named_initial_access:
  for c: D.Collection
  for key: String
  for -done: Bool -> S.Action
  {Read.exists(c,key,done) == S.Access{D.ViewExistence{c,key},Read.exists_return(done)} : S.Action}
def exists_emits_exactly_the_named_initial_access(c,key,done): {==}

law count_emits_exactly_the_named_initial_access:
  for c: D.Collection
  for -done: Nat -> S.Action
  {Read.count(c,done) == S.Access{D.CountRows{c},Read.count_return(done)} : S.Action}
def count_emits_exactly_the_named_initial_access(c,done): {==}

law cell_emits_exactly_the_named_initial_access:
  for c: D.Collection
  for key: String
  for column: String
  {Program.cell(c,key,column) == S.Access{D.ReadCell{c,key,column},Program.cell_result} : S.Action}
def cell_emits_exactly_the_named_initial_access(c,key,column): {==}


def KeysMeaning(-done: List<&2,String> -> S.Action,r: S.Return,-action: S.Action) -> Type:
  match r:
    case S.Datum{D.Keys{xs}}: {action == done(xs) : S.Action}
    case S.Datum{D.RowAbsent{}}: {action == S.Refuse{D.VText{"unexpected keys return"}} : S.Action}
    case S.Datum{D.Cell{value}}: {action == S.Refuse{D.VText{"unexpected keys return"}} : S.Action}
    case S.Datum{D.Existence{b}}: {action == S.Refuse{D.VText{"unexpected keys return"}} : S.Action}
    case S.Datum{D.Count{n}}: {action == S.Refuse{D.VText{"unexpected keys return"}} : S.Action}
    case S.UnitValue{}: {action == S.Refuse{D.VText{"unexpected keys return"}} : S.Action}

law every_keys_return_variant_has_the_exact_decoding_or_refusal:
  for -done: List<&2,String> -> S.Action
  for +r: S.Return
  KeysMeaning(done,r,Read.keys_return(done,r))
def every_keys_return_variant_has_the_exact_decoding_or_refusal(done,r):
  match r:
    case S.Datum{D.Keys{xs}}: {==}
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Cell{value}}: {==}
    case S.Datum{D.Existence{b}}: {==}
    case S.Datum{D.Count{n}}: {==}
    case S.UnitValue{}: {==}


def ExistsMeaning(-done: Bool -> S.Action,r: S.Return,-action: S.Action) -> Type:
  match r:
    case S.Datum{D.Existence{b}}: {action == done(b) : S.Action}
    case S.Datum{D.RowAbsent{}}: {action == S.Refuse{D.VText{"unexpected existence return"}} : S.Action}
    case S.Datum{D.Cell{value}}: {action == S.Refuse{D.VText{"unexpected existence return"}} : S.Action}
    case S.Datum{D.Keys{xs}}: {action == S.Refuse{D.VText{"unexpected existence return"}} : S.Action}
    case S.Datum{D.Count{n}}: {action == S.Refuse{D.VText{"unexpected existence return"}} : S.Action}
    case S.UnitValue{}: {action == S.Refuse{D.VText{"unexpected existence return"}} : S.Action}

law every_exists_return_variant_has_the_exact_decoding_or_refusal:
  for -done: Bool -> S.Action
  for +r: S.Return
  ExistsMeaning(done,r,Read.exists_return(done,r))
def every_exists_return_variant_has_the_exact_decoding_or_refusal(done,r):
  match r:
    case S.Datum{D.Keys{xs}}: {==}
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Cell{value}}: {==}
    case S.Datum{D.Existence{b}}: {==}
    case S.Datum{D.Count{n}}: {==}
    case S.UnitValue{}: {==}


def CountMeaning(-done: Nat -> S.Action,r: S.Return,-action: S.Action) -> Type:
  match r:
    case S.Datum{D.Count{n}}: {action == done(n) : S.Action}
    case S.Datum{D.RowAbsent{}}: {action == S.Refuse{D.VText{"unexpected count return"}} : S.Action}
    case S.Datum{D.Cell{value}}: {action == S.Refuse{D.VText{"unexpected count return"}} : S.Action}
    case S.Datum{D.Keys{xs}}: {action == S.Refuse{D.VText{"unexpected count return"}} : S.Action}
    case S.Datum{D.Existence{b}}: {action == S.Refuse{D.VText{"unexpected count return"}} : S.Action}
    case S.UnitValue{}: {action == S.Refuse{D.VText{"unexpected count return"}} : S.Action}

law every_count_return_variant_has_the_exact_decoding_or_refusal:
  for -done: Nat -> S.Action
  for +r: S.Return
  CountMeaning(done,r,Read.count_return(done,r))
def every_count_return_variant_has_the_exact_decoding_or_refusal(done,r):
  match r:
    case S.Datum{D.Keys{xs}}: {==}
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Cell{value}}: {==}
    case S.Datum{D.Existence{b}}: {==}
    case S.Datum{D.Count{n}}: {==}
    case S.UnitValue{}: {==}


def CellMeaning(r: S.Return,-action: S.Action) -> Type:
  match r:
    case S.Datum{D.Cell{value}}: {action == S.Finish{value} : S.Action}
    case S.Datum{D.RowAbsent{}}: {action == S.Finish{D.VAbsent{}} : S.Action}
    case S.Datum{D.Keys{xs}}: {action == S.Refuse{D.VText{"unexpected cell return"}} : S.Action}
    case S.Datum{D.Existence{b}}: {action == S.Refuse{D.VText{"unexpected cell return"}} : S.Action}
    case S.Datum{D.Count{n}}: {action == S.Refuse{D.VText{"unexpected cell return"}} : S.Action}
    case S.UnitValue{}: {action == S.Refuse{D.VText{"unexpected cell return"}} : S.Action}

law every_cell_return_variant_has_the_exact_value_or_refusal:
  for +r: S.Return
  CellMeaning(r,Program.cell_result(r))
def every_cell_return_variant_has_the_exact_value_or_refusal(r):
  match r:
    case S.Datum{D.Keys{xs}}: {==}
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Cell{value}}: {==}
    case S.Datum{D.Existence{b}}: {==}
    case S.Datum{D.Count{n}}: {==}
    case S.UnitValue{}: {==}


def SelectedMeaning(result: Query.Selection,-action: S.Action) -> Type:
  match result:
    case Query.Selected{record}: {action == S.Finish{record} : S.Action}
    case Query.MissingRow{}: {action == S.Finish{D.VAbsent{}} : S.Action}
    case Query.InvalidFields{}: {action == S.Refuse{D.VText{"invalid fields"}} : S.Action}
    case Query.UnexpectedReturn{}: {action == S.Refuse{D.VText{"unexpected selection return"}} : S.Action}

law every_selection_variant_has_the_exact_program_completion:
  for +result: Query.Selection
  SelectedMeaning(result,Program.selected(result))
def every_selection_variant_has_the_exact_program_completion(result):
  match result:
    case Query.Selected{record}: {==}
    case Query.MissingRow{}: {==}
    case Query.InvalidFields{}: {==}
    case Query.UnexpectedReturn{}: {==}

# Empty selection observes nothing and does not imply row/collection existence.
law empty_selection_is_exactly_the_empty_record_without_an_access:
  for c: D.Collection
  for key: String
  {Program.select(c,key,Nil{}) == S.Finish{D.VRecordEmpty{}} : S.Action}
def empty_selection_is_exactly_the_empty_record_without_an_access(c,key): {==}

law empty_field_program_with_text_argument_has_no_owned_database_access:
  for ctx: D.Context
  for key: String
  {S.start(Program.program(Nil{}),ctx,D.VText{key}) == S.Finish{D.VRecordEmpty{}} : S.Action}
def empty_field_program_with_text_argument_has_no_owned_database_access(ctx,key): {==}

# Complete argument-domain behavior: only the actual VText constructor starts
# selection. The text itself is not prevalidated by this Action constructor.
def StartMeaning(+fields: List<&2,String>,+ctx: D.Context,args: D.Value,-action: S.Action) -> Type:
  match args:
    case D.VText{key}: {action == Program.select(D.Application{D.context_id(ctx)},key,fields) : S.Action}
    case D.VAbsent{}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}
    case D.VBool{b}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}
    case D.VInt{a,b}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}
    case D.VListEmpty{}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}
    case D.VList{h,t}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}
    case D.VRecordEmpty{}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}
    case D.VRecord{n,v,r}: {action == S.Refuse{D.VText{"expected text key"}} : S.Action}

law every_read_program_argument_variant_has_exact_start_or_refusal:
  for +fields: List<&2,String>
  for +ctx: D.Context
  for +args: D.Value
  StartMeaning(fields,ctx,args,S.start(Program.program(fields),ctx,args))
def every_read_program_argument_variant_has_exact_start_or_refusal(fields,ctx,args):
  match args:
    case D.VText{key}: {==}
    case D.VAbsent{}: {==}
    case D.VBool{b}: {==}
    case D.VInt{a,b}: {==}
    case D.VListEmpty{}: {==}
    case D.VList{h,t}: {==}
    case D.VRecordEmpty{}: {==}
    case D.VRecord{n,v,r}: {==}
