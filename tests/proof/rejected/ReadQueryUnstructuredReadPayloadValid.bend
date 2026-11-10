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

law false_reject_unstructured_read_payload_valid:
  Valid.ResultValue(D.read_row(Some{D.Row{"k",[D.Field{"a",D.VList{D.VAbsent{},D.VAbsent{}}}]}},"a"))
def false_reject_unstructured_read_payload_valid(): {==}
