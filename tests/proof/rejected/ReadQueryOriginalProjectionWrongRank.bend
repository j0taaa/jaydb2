# Deliberately false claim: must fail causally at the named law.
import Base
import ../../../library/ReadPrefix.bend as Cut
import ../../../library/QuerySelectionModel.bend as M
import ../../../library/QueryCellVisitorProofs.bend as C
import ../../../library/QueryFilterMapPositions.bend as Pos
import ../../../library/ReadValueValidity.bend as Valid
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Read.bend as Read
import ../../../library/Query.bend as Q
import ../../../library/ReadProgram.bend as P
import ../../../library/SequencePaginationProofs.bend as At
import ../../../src/Termination.bend as T

def context() -> C.Context: C.Context{D.Application{"t"},[S.Datum{D.Cell{D.VText{"first"}}},S.Datum{D.Cell{D.VText{"second"}}}]}
def MaybeItems() -> List<&2,D.Value>: [D.VText{"first"},D.VText{"second"}]

law false_reject_original_projection_wrong_rank:
  {At.at(MaybeItems(),Pos.before(~C.Context,~C.cost,~C.item,context(),["a","b"],1n,0n)) == Some{D.VText{"first"}} : Maybe<&2,D.Value>}
def false_reject_original_projection_wrong_rank(): {==}
