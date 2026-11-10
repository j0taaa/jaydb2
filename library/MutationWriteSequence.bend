# Proof-side normal form of explicitly ordered write callbacks. Public runtime
# helpers are linked to this exact Action, including EVERY supplied Return.
# This is not the functional spec: WritePlan independently evaluates source
# D.operate on each changing working state and records first-stop behavior.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Action.bend as A
import ./Mutation.bend as M

def perform(operations: List<&2,D.Operation>,done: S.Action) -> S.Action:
  match operations:
    case Nil{}: done
    case Con{op,tail}: S.Access{op,r => A.written(perform(tail,done),r)}

def rows(+collection: D.Collection,xs: List<&2,D.Row>) -> List<&2,D.Operation>:
  match xs:
    case Nil{}: Nil{}
    case Con{D.Row{key,fields},tail}: Con{D.DefineRow{collection,key,fields},rows(collection,tail)}

def removals(+collection: D.Collection,xs: List<&2,String>) -> List<&2,D.Operation>:
  match xs:
    case Nil{}: Nil{}
    case Con{key,tail}: Con{D.RemoveRow{collection,key},removals(collection,tail)}

def columns(+collection: D.Collection,+key: String,xs: List<&2,D.Field>) -> List<&2,D.Operation>:
  match xs:
    case Nil{}: Nil{}
    case Con{D.Field{name,value},tail}: Con{D.DefineColumn{collection,key,name,value},columns(collection,key,tail)}

law actual_define_rows_is_exactly_the_ordered_named_write_sequence:
  for +collection: D.Collection
  for +xs: List<&2,D.Row>
  for -done: S.Action
  {A.define_rows(collection,xs,done) == perform(rows(collection,xs),done) : S.Action}
def actual_define_rows_is_exactly_the_ordered_named_write_sequence(collection,xs,done):
  match xs:
    case Nil{}: {==}
    case Con{D.Row{+key,+fields},+tail}:
      Equal.cong(S.Action,S.Action,next => S.Access{D.DefineRow{collection,key,fields},r => A.written(next,r)},A.define_rows(collection,tail,done),perform(rows(collection,tail),done),actual_define_rows_is_exactly_the_ordered_named_write_sequence(collection,tail,done))

law actual_remove_rows_is_exactly_the_ordered_named_write_sequence:
  for +collection: D.Collection
  for +xs: List<&2,String>
  for -done: S.Action
  {M.remove_rows(collection,xs,done) == perform(removals(collection,xs),done) : S.Action}
def actual_remove_rows_is_exactly_the_ordered_named_write_sequence(collection,xs,done):
  match xs:
    case Nil{}: {==}
    case Con{+key,+tail}:
      Equal.cong(S.Action,S.Action,next => S.Access{D.RemoveRow{collection,key},r => A.written(next,r)},M.remove_rows(collection,tail,done),perform(removals(collection,tail),done),actual_remove_rows_is_exactly_the_ordered_named_write_sequence(collection,tail,done))

law actual_columns_is_exactly_the_ordered_named_write_sequence:
  for +collection: D.Collection
  for +key: String
  for +xs: List<&2,D.Field>
  for -done: S.Action
  {M.columns(collection,key,xs,done) == perform(columns(collection,key,xs),done) : S.Action}
def actual_columns_is_exactly_the_ordered_named_write_sequence(collection,key,xs,done):
  match xs:
    case Nil{}: {==}
    case Con{D.Field{+name,+value},+tail}:
      Equal.cong(S.Action,S.Action,next => S.Access{D.DefineColumn{collection,key,name,value},r => A.written(next,r)},M.columns(collection,key,tail,done),perform(columns(collection,key,tail),done),actual_columns_is_exactly_the_ordered_named_write_sequence(collection,key,tail,done))

# Only UnitValue proceeds. In particular no supplied Datum is interpreted as
# a failed primitive: a real D.operate FailureData never invokes this decoder.
def WrittenMeaning(-next: S.Action,r: S.Return,-action: S.Action) -> Type:
  match r:
    case S.UnitValue{}: {action == next : S.Action}
    case S.Datum{D.Cell{value}}: {action == S.Refuse{D.VText{"unexpected write return"}} : S.Action}
    case S.Datum{D.RowAbsent{}}: {action == S.Refuse{D.VText{"unexpected write return"}} : S.Action}
    case S.Datum{D.Keys{keys}}: {action == S.Refuse{D.VText{"unexpected write return"}} : S.Action}
    case S.Datum{D.Count{count}}: {action == S.Refuse{D.VText{"unexpected write return"}} : S.Action}
    case S.Datum{D.Existence{exists}}: {action == S.Refuse{D.VText{"unexpected write return"}} : S.Action}

law every_supplied_write_return_proceeds_or_stops_before_the_next_owned_access:
  for -next: S.Action
  for +r: S.Return
  WrittenMeaning(next,r,A.written(next,r))
def every_supplied_write_return_proceeds_or_stops_before_the_next_owned_access(next,r):
  match r:
    case S.UnitValue{}: {==}
    case S.Datum{D.Cell{value}}: {==}
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Keys{keys}}: {==}
    case S.Datum{D.Count{count}}: {==}
    case S.Datum{D.Existence{exists}}: {==}
