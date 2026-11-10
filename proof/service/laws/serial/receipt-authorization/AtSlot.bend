# All local semantic assumptions here are DERIVED at the final public boundary
# from an actual retained block, its exact Job and original receipt observation.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Binding
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ../header/History.bend as History
import ../header/PhaseLocation.bend as PLocation
import ../observed-invalidation/Prelude.bend as NPrelude
import ../observed-invalidation/Location.bend as NLocation
import ../observed-sealing/Recovery.bend as DecodeData
import ../observed-headers/WireRule.bend as Wire
import ../DecodeReception.bend as Reception
import ./Projection.bend as Projection
import ./Source.bend as Source
import ./BlockSource.bend as Block
import ./PhaseItems.bend as Items
import ./PreparationSite.bend as PSite
import ./PreparationRule.bend as PAuth
import ./InvalidationCauses.bend as NCause
import ./InvalidationPrefix.bend as NSite
import ./InvalidationRule.bend as NAuth

def Boundary(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String, receipt: W.Receipt) -> Type:
  match receipt:
    case W.PreparedReceipt{handle}: Unit
    case W.InvalidatedReceipt{}: Wire.PhysicalInputs(c, binding, public, script, seed, instance)

def invalidated_boundary(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +receipt: W.Receipt, same: {receipt == W.InvalidatedReceipt{} : W.Receipt}, native: Boundary(c, binding, public, script, seed, instance, receipt)) -> Wire.PhysicalInputs(c, binding, public, script, seed, instance):
  %same : Boundary(c, binding, public, script, seed, instance, _)
  native

def invalidation_input_valid(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  native: Wire.PhysicalInputs(c, binding, public, script, seed, instance)) -> X.ReceptionValid(input):
  %DecodeData.input_equal(c, binding, public, block, input, primitives, exact) : X.ReceptionValid(_)
  native(owner, block, known)

def preparation_site(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +point: Nat, -item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>},
  hit: &local: Nat -> L.E<{point == Prelude.phase_index(frames, local) : Nat}, {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives))), local) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}>) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), receipt):
  match hit:
    case (+local, L.Both{position, found}):
      %Equal.sym(Nat, point, Prelude.phase_index(frames, local), position) : E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, _)), receipt)
      PAuth.actual(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, mode, raw, frames, receipt, local, known, source,
        PSite.every_actual_queried_prepared_receipt_has_its_exact_earlier_acceptance_and_handle_choice(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives), receipt, bytes, local, found))

def preparation(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +point: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>},
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>}) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), receipt):
  preparation_site(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, mode, raw, frames, point, item, receipt, bytes, known, source,
    Items.preparation(Engine.world(block), input, Chain.block_before(block), raw, frames, V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives)), point, item, receipt, bytes, actual,
      (%source : {B.query(O.Item, _, point) == Some{item} : Maybe<&2, O.Item>} found)))

def invalidation_at(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +raw: P.Request, +frames: List<&2, Q.Frame>, +receipt: W.Receipt, +bytes: List<&2, U32>, +local: Nat,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == NPrelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  physical: Boundary(c, binding, public, script, seed, instance, receipt),
  parsed: {Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), input)) == Decode.Parsed{W.Extension{W.Invalidate{}, raw}} : Decode.Decision},
  position: {local == 2n : Nat},
  cause: NCause.Cause<c, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives), V.ReceiptPrepared{receipt, bytes}>) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, local))), receipt):
  match cause:
    case NCause.Cause{+context, +entry, +prepared, auth, empty, lookup, fits, frame, +payload}:
      %Equal.sym(Nat, local, 2n, position) : E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, _))), receipt)
      %Equal.sym(W.Receipt, receipt, W.InvalidatedReceipt{}, F.some_injective(W.Receipt, receipt, W.InvalidatedReceipt{}, Equal.cong(V.PreparationEvent, Maybe<&2, W.Receipt>, PSite.receipt_of, V.ReceiptPrepared{receipt, bytes}, V.ReceiptPrepared{W.InvalidatedReceipt{}, prepared}, payload))) :
        E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, 2n))), _)
      NAuth.actual(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, raw, context, entry, prepared, frames, known, source, auth, empty, lookup, fits, frame,
        Reception.actual_decoding_of_either_wire_kind_derives_received_without_a_reception_encoding_premise(c, E.database(Chain.block_before(block)), input, W.Extension{W.Invalidate{}, raw},
          invalidation_input_valid(c, binding, public, script, seed, instance, owner, block, input, primitives, exact, known,
            invalidated_boundary(c, binding, public, script, seed, instance, receipt, F.some_injective(W.Receipt, receipt, W.InvalidatedReceipt{}, Equal.cong(V.PreparationEvent, Maybe<&2, W.Receipt>, PSite.receipt_of, V.ReceiptPrepared{receipt, bytes}, V.ReceiptPrepared{W.InvalidatedReceipt{}, prepared}, payload)), physical)), parsed))

def invalidation_site(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +raw: P.Request, +frames: List<&2, Q.Frame>, +point: Nat, -item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == NPrelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  physical: Boundary(c, binding, public, script, seed, instance, receipt),
  +parsed: {Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), input)) == Decode.Parsed{W.Extension{W.Invalidate{}, raw}} : Decode.Decision},
  hit: &local: Nat -> L.E<{point == Prelude.phase_index(frames, local) : Nat}, {B.query(N.InvalidationEvent, N.events(N.run(c, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives))), local) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}>) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), receipt):
  match hit:
    case (+local, L.Both{position, +found}):
      %Equal.sym(Nat, point, Prelude.phase_index(frames, local), position) : E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, _)), receipt)
      invalidation_at(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, raw, frames, receipt, bytes, local, known, source, exact, physical, parsed,
        NSite.every_actual_queried_invalidation_receipt_frame_occurs_before_removal_at_phase_two(c, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives), receipt, bytes, local, found),
        NCause.any_actual_queried_invalidation_receipt_frame_recovers_its_original_guards_without_cleanup_completion(c, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives), local, receipt, bytes, found))

def invalidation(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +raw: P.Request, +frames: List<&2, Q.Frame>, +point: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == NPrelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  physical: Boundary(c, binding, public, script, seed, instance, receipt),
  +parsed: {Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), input)) == Decode.Parsed{W.Extension{W.Invalidate{}, raw}} : Decode.Decision},
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>}) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), receipt):
  invalidation_site(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, raw, frames, point, item, receipt, bytes, known, source, exact, physical, parsed,
    Items.invalidation(Engine.world(block), input, Chain.block_before(block), raw, frames, N.run(c, Chain.block_before(block), raw, NPrelude.cleanup(primitives), Dispatch.send(primitives)), point, item, receipt, bytes, actual,
      (%source : {B.query(O.Item, _, point) == Some{item} : Maybe<&2, O.Item>} found)))

def for_cause(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +point: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  physical: Boundary(c, binding, public, script, seed, instance, receipt),
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>},
  cause: Source.Cause<c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), input)), primitives, receipt, bytes>) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), receipt):
  match cause:
    case Source.PreparationCause{+mode, +raw, parsed, original}:
      preparation(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, mode, raw, Decode.frames(Decode.run(c, E.database(Chain.block_before(block)), input)), point, item, receipt, bytes, known,
        PLocation.source_equation(c, binding, public, block, input, primitives, mode, raw, Decode.frames(Decode.run(c, E.database(Chain.block_before(block)), input)), exact,
          DecodeData.decoded_from_parsed(Decode.run(c, E.database(Chain.block_before(block)), input), W.Extension{V.operation(mode), raw}, parsed)), actual, found)
    case Source.InvalidationCause{+raw, +parsed, original}:
      invalidation(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, raw, Decode.frames(Decode.run(c, E.database(Chain.block_before(block)), input)), point, item, receipt, bytes, known,
        NLocation.source_equation(c, binding, public, block, input, primitives, raw, Decode.frames(Decode.run(c, E.database(Chain.block_before(block)), input)), exact,
          DecodeData.decoded_from_parsed(Decode.run(c, E.database(Chain.block_before(block)), input), W.Extension{W.Invalidate{}, raw}, parsed)), exact, physical, parsed, actual, found)

def actual_job_cause(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +point: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>}) ->
  Source.Cause<c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), input)), primitives, receipt, bytes>:
  %DecodeData.input_equal(c, binding, public, block, input, primitives, exact) : Source.Cause<c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), _)), primitives, receipt, bytes>
  Block.query(c, binding, public, block, input, primitives, point, item, receipt, bytes, exact, found, actual)

def actual(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +point: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  physical: Boundary(c, binding, public, script, seed, instance, receipt),
  +actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  +found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>}) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), receipt):
  for_cause(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, point, item, receipt, bytes, known, exact, physical, actual, found,
    actual_job_cause(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, point, item, receipt, bytes, exact, actual, found))
