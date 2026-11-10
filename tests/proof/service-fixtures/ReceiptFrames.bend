# Concrete phase branches, including stops after the prepared frame. These
# DATA returns do not assert a native checker/file or serial registry origin.
import Base
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Resources.bend as X
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/FrameBounds.bend as B
import ./Resolution.bend as Fixture

def bytes(frame: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match frame:
    case None{}: []
    case Some{bytes}: bytes

law an_actual_pending_seal_already_has_its_prepared_receipt:
  {B.query(V.PreparationEvent, V.events(V.run(Fixture.configuration(), V.ReadMode{}, Fixture.raw(), Fixture.missing(),
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, V.SendComplete{}})), 4n) ==
    Some{V.ReceiptPrepared{W.PreparedReceipt{Fixture.handle()}, bytes(W.frame_receipt(W.PreparedReceipt{Fixture.handle()}))}} : Maybe<&2, V.PreparationEvent>}
def an_actual_pending_seal_already_has_its_prepared_receipt(): {==}

law an_actual_pending_seal_has_no_later_success_or_conclusion:
  {B.query(V.PreparationEvent, V.events(V.run(Fixture.configuration(), V.ReadMode{}, Fixture.raw(), Fixture.missing(),
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, V.SendComplete{}})), 5n) == None{} : Maybe<&2, V.PreparationEvent>}
def an_actual_pending_seal_has_no_later_success_or_conclusion(): {==}

law an_actual_failed_cleanup_does_not_erase_the_prepared_invalidation_receipt:
  {B.query(N.InvalidationEvent, N.events(N.run(Fixture.configuration(), Fixture.before(), Fixture.raw(), N.CleanupFailed{"late", False{}}, V.SendComplete{})), 2n) ==
    Some{N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes(W.frame_receipt(W.InvalidatedReceipt{}))}}} : Maybe<&2, N.InvalidationEvent>}
def an_actual_failed_cleanup_does_not_erase_the_prepared_invalidation_receipt(): {==}
