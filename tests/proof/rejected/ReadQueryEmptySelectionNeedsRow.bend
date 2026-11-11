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
  {T.observe(1n,P.select(D.Application{"t"},"missing",Nil{}),D.Schema{Nil{}},D.State{Nil{},Nil{}},Nil{}) == S.Final{D.State{Nil{},Nil{}},Nil{},S.Response{S.DataError{},D.VAbsent{}}} : S.Trace}
def false(): {==}
