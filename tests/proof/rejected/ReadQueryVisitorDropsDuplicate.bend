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

law false_reject_visitor_drops_duplicate:
  {Cut.cut(~C.Context,~C.reply,C.Context{D.Application{"t"},[S.Datum{D.Cell{D.VText{"first"}}},S.Datum{D.Cell{D.VText{"second"}}}]},2n,0n,Q.filter_map(~C.Context,~C.visit,C.Context{D.Application{"t"},[S.Datum{D.Cell{D.VText{"first"}}},S.Datum{D.Cell{D.VText{"second"}}}]},["a","a"],value => S.Finish{value})) == Cut.prefix([D.ReadCell{D.Application{"t"},"a","value"}],S.Finish{D.VList{D.VText{"first"},D.VListEmpty{}}}) : Cut.Prefix}
def false_reject_visitor_drops_duplicate(): {==}
