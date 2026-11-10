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

law false_reject_invalid_selection_reads_first:
  {P.select(D.Application{"t"},"k",["z","a"]) == S.Access{D.ReadCell{D.Application{"t"},"k","z"},r => S.Finish{D.VAbsent{}}} : S.Action}
def false_reject_invalid_selection_reads_first(): {==}
