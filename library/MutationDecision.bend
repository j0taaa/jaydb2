# Pure local mutation decision: return a payload, perform one named write and
# return it, or refuse. This records operation/payload/error choice without any
# Action or whole trace, allowing all public decoder paths to be checked.
import Base
import ./MutationWriteSequence.bend as W
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

type Decision<-Out: Data> is Data:
  MutationReturn{result: Out}
  MutationWrite{operation: D.Operation,result: Out}
  MutationRefuse{reason: D.Value}

def action(~Out: Data,decision: Decision<Out>,done: Out -> S.Action) -> S.Action:
  match decision:
    case MutationReturn{result}: done(result)
    case MutationWrite{operation,result}: W.perform([operation],done(result))
    case MutationRefuse{reason}: S.Refuse{reason}
