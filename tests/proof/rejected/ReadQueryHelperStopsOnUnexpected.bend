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

law false:
  {Cut.cut(~C.Context,~C.reply,C.Context{D.Application{"t"},[S.UnitValue{},S.Datum{D.Cell{D.VAbsent{}}}]},2n,0n,Q.read_fields(D.Application{"t"},"k",["a","b"],P.selected)) == Cut.prefix([D.ReadCell{D.Application{"t"},"k","a"}],S.Refuse{D.VText{"unexpected selection return"}}) : Cut.Prefix}
def false(): {==}
