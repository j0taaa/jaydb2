# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Action.bend as A

def collection() -> D.Collection: D.Application{"t"}

law false_reject_empty_writes_ignore_caller:
  {A.define_rows(collection(),Nil{},S.Access{D.RemoveRow{collection(),"k"},r => S.Finish{D.VAbsent{}}}) == S.Finish{D.VAbsent{}} : S.Action}
def false_reject_empty_writes_ignore_caller(): {==}
