import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../specification/ServiceLaws.bend as E
import ../model/FrameBounds.bend as B
import ./PreparePhases.bend as V
import ./InvalidationPhases.bend as N
import ./InvalidationEvents.bend as Events

def before() -> E.Snapshot:
  E.Snapshot{"instance", D.State{Nil{}, Nil{}}, [11, 22], [G.Entry{"instance", "handle", "source", "proof", False{}, "seal"}]}

def after() -> E.Snapshot:
  E.Snapshot{"instance", D.State{Nil{}, Nil{}}, [11, 22], Nil{}}

law pending_cleanup_keeps_the_removal:
  {N.snapshot(N.remove_and_cleanup(before(), "handle", [33], N.CleanupPending{}, V.SendComplete{})) == after() : E.Snapshot}
def pending_cleanup_keeps_the_removal(): {==}

law fatal_cleanup_keeps_the_removal:
  {N.snapshot(N.remove_and_cleanup(before(), "handle", [33], N.CleanupFailed{"cleanup", True{}}, V.SendComplete{})) == after() : E.Snapshot}
def fatal_cleanup_keeps_the_removal(): {==}

law fatal_cleanup_still_records_the_removal_event:
  {B.query(N.InvalidationEvent, N.events(N.remove_and_cleanup(before(), "handle", [33], N.CleanupFailed{"cleanup", True{}}, V.SendComplete{})), 0n) ==
    Some{N.RegistryRemoved{"handle", before(), after()}} : Maybe<&2, N.InvalidationEvent>}
def fatal_cleanup_still_records_the_removal_event(): {==}
