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

def refusing(env: Unit,key: String,done: Maybe<&2,D.Value> -> S.Action) -> S.Action: S.Refuse{D.VAbsent{}}

law false_reject_visitor_always_continues:
  {Q.filter_map(~Unit,~refusing,Unit{},["a","b"],value => S.Finish{value}) == S.Finish{D.VListEmpty{}} : S.Action}
def false_reject_visitor_always_continues(): {==}
