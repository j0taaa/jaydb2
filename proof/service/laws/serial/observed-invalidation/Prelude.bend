# Exact actual invalidation source: retained Selection, all decoder frames and
# every invalidation event. No completed outcome or selected trace is assumed.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../PrimitivesService.bend as Micro
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/EventHistory.bend as T
import ../../../model/FrameBounds.bend as B
import ../../../model/InvalidationPrefix.bend as PhaseSource
import ../../../model/ObservationUniqueness.bend as U
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/DecodeEvents.bend as DecodeEvents
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Engine.bend as Engine


def codec_items(+world: Nat, +input: X.Reception, +selected: D.State, +raw: P.Request, frames: List<&2, Q.Frame>) -> List<&2, O.Item>:
  Engine.stamp(world, input, selected, C.core(True{}, I.code(raw), frames))


def with_run(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, run: N.InvalidationRun) -> List<&2, O.Item>:
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  Con{O.Item{world, E.database(before), input, O.Selection{before}},
    T.append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events))}


def source(~c: S.Configuration, world: Nat, input: X.Reception, +before: E.Snapshot,
  +raw: P.Request, cleanup: N.CleanupReturn, send: V.SendReturn, frames: List<&2, Q.Frame>) -> List<&2, O.Item>:
  with_run(world, input, before, raw, frames, N.run(c, before, raw, cleanup, send))


def phase_index(+frames: List<&2, Q.Frame>, index: Nat) -> Nat:
  Succ{Nat.add(B.count(Q.Frame, frames), index)}


def stamp_invalidation(+world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, N.InvalidationEvent>) ->
  {Engine.stamp(world, input, selected, C.invalidate_events(events)) == PhaseSource.phase_items(world, selected, input, events) : List<&2, O.Item>}:
  match events:
    case Nil{}: {==}
    case Con{+event, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, tail => Con{O.Item{world, selected, input, O.Invalidation{event}}, tail},
        Engine.stamp(world, input, selected, C.invalidate_events(rest)), PhaseSource.phase_items(world, selected, input, rest), stamp_invalidation(world, input, selected, rest))


def actual_pipeline_items(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +selected: D.State, +raw: P.Request, +events: List<&2, N.InvalidationEvent>) ->
  {Engine.stamp(world, input, selected, C.append(C.core(True{}, I.code(raw), frames), C.invalidate_events(events))) ==
    T.append(codec_items(world, input, selected, raw, frames), PhaseSource.phase_items(world, selected, input, events)) : List<&2, O.Item>}:
  match frames:
    case Nil{}: stamp_invalidation(world, input, selected, events)
    case Con{+frame, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, tail => Con{O.Item{world, selected, input, O.Core{True{}, I.code(raw), frame}}, tail},
        Engine.stamp(world, input, selected, C.append(C.core(True{}, I.code(raw), rest), C.invalidate_events(events))),
        T.append(codec_items(world, input, selected, raw, rest), PhaseSource.phase_items(world, selected, input, events)),
        actual_pipeline_items(rest, world, input, selected, raw, events))


def phase_query(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +events: List<&2, N.InvalidationEvent>, +index: Nat, +phase: N.InvalidationEvent,
  found: {B.query(N.InvalidationEvent, events, index) == Some{phase} : Maybe<&2, N.InvalidationEvent>}) ->
  {B.query(O.Item, T.append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events)),
      Nat.add(B.count(Q.Frame, frames), index)) == Some{O.Item{world, E.database(before), input, O.Invalidation{phase}}} : Maybe<&2, O.Item>}:
  match frames:
    case Nil{}:
      Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, PhaseSource.phase_items(world, E.database(before), input, events), index),
        PhaseSource.item_result(world, E.database(before), input, B.query(N.InvalidationEvent, events, index)), Some{O.Item{world, E.database(before), input, O.Invalidation{phase}}},
        PhaseSource.exact_removal_phase_query_lifts_to_the_full_observer_item_query(world, E.database(before), input, events, index),
        Equal.cong(Maybe<&2, N.InvalidationEvent>, Maybe<&2, O.Item>, result => PhaseSource.item_result(world, E.database(before), input, result),
          B.query(N.InvalidationEvent, events, index), Some{phase}, found))
    case Con{frame, +rest}: phase_query(rest, world, input, before, raw, events, index, phase, found)


def with_run_query(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +frames: List<&2, Q.Frame>, +run: N.InvalidationRun, +index: Nat, +phase: N.InvalidationEvent,
  found: {B.query(N.InvalidationEvent, N.events(run), index) == Some{phase} : Maybe<&2, N.InvalidationEvent>}) ->
  {B.query(O.Item, with_run(world, input, before, raw, frames, run), phase_index(frames, index)) ==
    Some{O.Item{world, E.database(before), input, O.Invalidation{phase}}} : Maybe<&2, O.Item>}:
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  phase_query(frames, world, input, before, raw, events, index, phase, found)


law every_actual_invalidation_phase_query_retains_its_exact_measured_codec_offset:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  for +frames: List<&2, Q.Frame>
  for +index: Nat
  for +phase: N.InvalidationEvent
  for found: {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index) == Some{phase} : Maybe<&2, N.InvalidationEvent>}
  {B.query(O.Item, source(c, world, input, before, raw, cleanup, send, frames), phase_index(frames, index)) ==
    Some{O.Item{world, E.database(before), input, O.Invalidation{phase}}} : Maybe<&2, O.Item>}
def every_actual_invalidation_phase_query_retains_its_exact_measured_codec_offset(c, world, input, before, raw, cleanup, send, frames, index, phase, found):
  with_run_query(world, input, before, raw, frames, N.run(c, before, raw, cleanup, send), index, phase, found)


def cleanup(primitives: Dispatch.Primitives) -> N.CleanupReturn:
  Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send} = primitives
  cleanup


def decoded_run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, +primitives: Dispatch.Primitives) ->
  {Dispatch.decoded(c, binding, public, before, Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, primitives) ==
    C.prefix(C.core(True{}, I.code(raw), frames), C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)))) : C.CallRun}:
  match primitives:
    case Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}: {==}


def actual_invalidation_block_items(+ordinal: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, +run: N.InvalidationRun) ->
  {Engine.block_items(Engine.Block{ordinal, True{}, input, before, C.prefix(C.core(True{}, I.code(raw), frames), C.invalidation(run))}) ==
    with_run(Succ{ordinal}, input, before, raw, frames, run) : List<&2, O.Item>}:
  N.InvalidationRun{+events, result, snapshot, waiting, closed} = run
  Equal.cong(List<&2, O.Item>, List<&2, O.Item>, tail => Con{O.Item{Succ{ordinal}, E.database(before), input, O.Selection{before}}, tail},
    Engine.stamp(Succ{ordinal}, input, E.database(before), C.append(C.core(True{}, I.code(raw), frames), C.invalidate_events(events))),
    T.append(codec_items(Succ{ordinal}, input, E.database(before), raw, frames), PhaseSource.phase_items(Succ{ordinal}, E.database(before), input, events)),
    actual_pipeline_items(frames, Succ{ordinal}, input, E.database(before), raw, events))


def parsed(run: Decode.DecodeRun) -> Bool:
  match run:
    case Decode.DecodeRun{Decode.Parsed{wire}, frames}: True{}
    case _: False{}


def parsed_selection(~c: S.Configuration, +current: D.State, +disposition: X.Disposition,
  +raw: P.Request, +frames: List<&2, Q.Frame>,
  same: {Decode.disposed(c, current, disposition) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}) ->
  {Engine.selection(disposition) == True{} : Bool}:
  match disposition:
    case X.CloseWithoutResponse{}:
      Equal.cong(Decode.DecodeRun, Bool, parsed, Decode.disposed(c, current, X.CloseWithoutResponse{}), Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, same)
    case X.RefuseClose{+status}:
      Equal.cong(Decode.DecodeRun, Bool, parsed, Decode.disposed(c, current, X.RefuseClose{status}), Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, same)
    case X.RefuseContinue{status}: {==}
    case X.ProcessBody{bytes}: {==}


def block_from_decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +raw: P.Request, +frames: List<&2, Q.Frame>, +primitives: Dispatch.Primitives,
  selected: {Engine.selection(X.decide_reception(c, input)) == True{} : Bool},
  decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}) ->
  {Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) ==
    source(c, Succ{ordinal}, input, before, raw, cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}:
  Equal.trans(List<&2, O.Item>, Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})),
    Engine.block_items(Engine.Block{ordinal, True{}, input, before, Dispatch.run(c, binding, public, before, input, primitives)}),
    source(c, Succ{ordinal}, input, before, raw, cleanup(primitives), Dispatch.send(primitives), frames),
    Equal.cong(Bool, List<&2, O.Item>, selected => Engine.block_items(Engine.Block{ordinal, selected, input, before, Dispatch.run(c, binding, public, before, input, primitives)}),
      Engine.selection(X.decide_reception(c, input)), True{}, selected),
    Equal.trans(List<&2, O.Item>, Engine.block_items(Engine.Block{ordinal, True{}, input, before, Dispatch.run(c, binding, public, before, input, primitives)}),
      Engine.block_items(Engine.Block{ordinal, True{}, input, before, C.prefix(C.core(True{}, I.code(raw), frames), C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives))))}),
      source(c, Succ{ordinal}, input, before, raw, cleanup(primitives), Dispatch.send(primitives), frames),
      Equal.cong(C.CallRun, List<&2, O.Item>, run => Engine.block_items(Engine.Block{ordinal, True{}, input, before, run}),
        Dispatch.run(c, binding, public, before, input, primitives), C.prefix(C.core(True{}, I.code(raw), frames), C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)))),
        Equal.trans(C.CallRun, Dispatch.run(c, binding, public, before, input, primitives),
          Dispatch.decoded(c, binding, public, before, Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, primitives),
          C.prefix(C.core(True{}, I.code(raw), frames), C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)))),
          Equal.cong(Decode.DecodeRun, C.CallRun, run => Dispatch.decoded(c, binding, public, before, run, primitives), Decode.run(c, E.database(before), input),
            Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, decoded), decoded_run(c, binding, public, before, raw, frames, primitives))),
      actual_invalidation_block_items(ordinal, input, before, raw, frames, N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)))))


def block_from_decoded_copies(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +raw: P.Request, +frames: List<&2, Q.Frame>, +primitives: Dispatch.Primitives,
  copies: L.E<{Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun},
    {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}>) ->
  {Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) ==
    source(c, Succ{ordinal}, input, before, raw, cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}:
  match copies:
    case L.Both{for_selection, for_render}:
      block_from_decoded(c, binding, public, ordinal, before, input, raw, frames, primitives,
        parsed_selection(c, E.database(before), X.decide_reception(c, input), raw, frames, for_selection), for_render)


law actual_decoded_invalidation_block_retains_selection_and_every_codec_and_phase_event:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +input: X.Reception
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +primitives: Dispatch.Primitives
  for decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}
  {Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) ==
    source(c, Succ{ordinal}, input, before, raw, cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}
def actual_decoded_invalidation_block_retains_selection_and_every_codec_and_phase_event(c, binding, public, ordinal, before, input, raw, frames, primitives, decoded):
  block_from_decoded_copies(c, binding, public, ordinal, before, input, raw, frames, primitives,
    Q.equality_reopenable(Decode.DecodeRun, Decode.run(c, E.database(before), input), Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, decoded))


def actual_codec_internal(~c: S.Configuration, +before: E.Snapshot, +input: X.Reception,
  +raw: P.Request, +frames: List<&2, Q.Frame>,
  decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}) ->
  Micro.Internal(frames):
  %Equal.cong(Decode.DecodeRun, List<&2, Q.Frame>, Decode.frames, Decode.run(c, E.database(before), input),
    Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames}, decoded) : Micro.Internal(_)
  DecodeEvents.every_actual_decode_prelude_contains_only_internal_frames(c, E.database(before), input)

def codec_has_no_conclusion(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +before: E.Snapshot, +input: X.Reception, +raw: P.Request, +frames: List<&2, Q.Frame>,
  decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}) ->
  U.NoTag(3n, U.values(c, binding, public, codec_items(world, input, E.database(before), raw, frames))):
  DecodeEvents.internal_frames_exclude_nonzero_tags(c, binding, public, frames, world, input, E.database(before), True{}, I.code(raw), 2n,
    actual_codec_internal(c, before, input, raw, frames, decoded))
