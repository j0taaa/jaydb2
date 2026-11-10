# Nonempty COMPLETE Engine histories, starting at the true empty boot registry.
# Primitive DATA returns do not assert original native certificates or artifacts.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../proof/SourceService.bend as Source
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/FrameBounds.bend as B
import ../../../proof/service/model/serial/Decode.bend as Decode
import ../../../proof/service/model/serial/Dispatch.bend as Dispatch
import ../../../proof/service/model/serial/ExecutionPhases.bend as Execution
import ../../../proof/service/model/serial/Engine.bend as Engine
import ../../../proof/service/model/serial/PreparationPrelude.bend as Prelude
import ../../../proof/service/laws/serial/header/History.bend as History
import ./Resolution.bend as Fixture

def bytes(frame: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match frame:
    case None{}: []
    case Some{bytes}: bytes

def seed(unit: Unit) -> D.State:
  E.database(Fixture.missing())

def input(operation: W.Operation) -> X.Reception:
  X.BodyReceived{0, 173, bytes(W.encode_body(W.Extension{operation, Fixture.raw()}))}

# The first call uses a short source name; the allocated handle remains the
# same actual 64-character validated handle. This keeps the concrete witness
# within the fixed kernel reduction budget without altering the implementation, laws, or checker budgets.
def preparing() -> X.Reception:
  X.BodyReceived{0, 110, bytes(W.encode_body(W.Extension{W.Prepare{}, P.Request{"secret", "p", D.VAbsent{}, ""}}))}

def forged_invalidation() -> X.Reception:
  X.BodyReceived{0, 0, bytes(W.encode_body(W.Extension{W.Invalidate{}, Fixture.raw()}))}

def pending() -> Dispatch.Primitives:
  Dispatch.Primitives{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, N.CleanupPending{}, Dispatch.ArtifactPending{}, Execution.StartPending{}, V.SendComplete{}}

def stored() -> Dispatch.Primitives:
  Dispatch.Primitives{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealSucceeded{"stored"}, N.CleanupPending{}, Dispatch.ArtifactPending{}, Execution.StartPending{}, V.SendComplete{}}

def cleaning() -> Dispatch.Primitives:
  Dispatch.Primitives{V.CheckerPending{}, V.AllocatorPending{}, V.SealPending{}, N.CleanupFailed{"late", False{}}, Dispatch.ArtifactPending{}, Execution.StartPending{}, V.SendComplete{}}

def preparation_script() -> List<&2, Engine.Job>:
  [Engine.Job{input(W.PrepareRead{}), pending()}]

def invalidation_script(reception: X.Reception) -> List<&2, Engine.Job>:
  [Engine.Job{preparing(), stored()}, Engine.Job{reception, cleaning()}]

law a_true_boot_history_retains_the_preparation_receipt_before_a_pending_seal:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  {B.query(O.Item, History.items(Fixture.configuration(), binding, public, preparation_script(), seed, "fixture"),
    Prelude.phase_index(Decode.frames(Decode.run(Fixture.configuration(), seed(Unit{}), input(W.PrepareRead{}))), 4n)) ==
      Some{O.Item{1n, seed(Unit{}), input(W.PrepareRead{}), O.Preparation{V.ReceiptPrepared{W.PreparedReceipt{Fixture.handle()}, bytes(W.frame_receipt(W.PreparedReceipt{Fixture.handle()}))}}}} : Maybe<&2, O.Item>}
def a_true_boot_history_retains_the_preparation_receipt_before_a_pending_seal(binding, public): {==}

# The concrete full-history query index51 was measured from the original
# first block + second decoder. The literal avoids reducing that whole first
# computation a second time; the kernel still checks the ORIGINAL Engine query.
law a_true_boot_history_registers_then_frames_invalidation_before_failed_cleanup:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  {B.query(O.Item, History.items(Fixture.configuration(), binding, public, invalidation_script(input(W.Invalidate{})), seed, "fixture"), 51n) ==
    Some{O.Item{2n, seed(Unit{}), input(W.Invalidate{}), O.Invalidation{N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes(W.frame_receipt(W.InvalidatedReceipt{}))}}}}} : Maybe<&2, O.Item>}
def a_true_boot_history_registers_then_frames_invalidation_before_failed_cleanup(binding, public): {==}

# A forged declared count is NOT a physical input. The unconstrained pure
# Engine still retains this source event, witnessing why invalidation's native
# boundary is necessary rather than silently deriving physical framing.
law the_actual_pure_source_can_frame_invalidation_with_a_forged_declared_count:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  {B.query(O.Item, History.items(Fixture.configuration(), binding, public, invalidation_script(forged_invalidation()), seed, "fixture"), 51n) ==
    Some{O.Item{2n, seed(Unit{}), forged_invalidation(), O.Invalidation{N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes(W.frame_receipt(W.InvalidatedReceipt{}))}}}}} : Maybe<&2, O.Item>}
def the_actual_pure_source_can_frame_invalidation_with_a_forged_declared_count(binding, public): {==}

law the_forged_declared_count_is_not_a_valid_physical_reception:
  {X.reception_is_valid(forged_invalidation()) == False{} : Bool}
def the_forged_declared_count_is_not_a_valid_physical_reception(): {==}
