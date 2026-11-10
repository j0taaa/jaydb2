# Actual preparation source with its retained Selection+codec prelude. Phase
# indices are measured from real codec frames; no metadata event is erased.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../ProtocolService.bend as Q
import ../../../PrimitivesService.bend as Micro
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ../FrameBounds.bend as B
import ../PreparationCurrent.bend as PhaseSource
import ../PreparationPrefix.bend as Prefix
import ../ObservationUniqueness.bend as U
import ../PreparationUniqueness.bend as Uniqueness
import ./Common.bend as C
import ./Decode.bend as Decode
import ./DecodeEvents.bend as DecodeEvents
import ./Dispatch.bend as Dispatch
import ./Engine.bend as Engine


def codec_items(+world: Nat, +input: X.Reception, +selected: D.State, +raw: P.Request, frames: List<&2, Q.Frame>) -> List<&2, O.Item>:
  Engine.stamp(world, input, selected, C.core(True{}, I.code(raw), frames))


def with_run(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, run: V.PreparationRun) -> List<&2, O.Item>:
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  Con{O.Item{world, E.database(before), input, O.Selection{before}},
    T.append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events))}


def source(~c: S.Configuration, world: Nat, input: X.Reception, +before: E.Snapshot,
  mode: V.Mode, +raw: P.Request, returns: V.Returns, frames: List<&2, Q.Frame>) -> List<&2, O.Item>:
  with_run(world, input, before, raw, frames, V.run(c, mode, raw, before, returns))


def phase_index(+frames: List<&2, Q.Frame>, index: Nat) -> Nat:
  Succ{Nat.add(B.count(Q.Frame, frames), index)}


def stamp_preparation(+world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, V.PreparationEvent>) ->
  {Engine.stamp(world, input, selected, C.prepare_events(events)) == PhaseSource.phase_items(world, selected, input, events) : List<&2, O.Item>}:
  match events:
    case Nil{}: {==}
    case Con{+event, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, tail => Con{O.Item{world, selected, input, O.Preparation{event}}, tail},
        Engine.stamp(world, input, selected, C.prepare_events(rest)), PhaseSource.phase_items(world, selected, input, rest), stamp_preparation(world, input, selected, rest))


def actual_pipeline_items(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +selected: D.State, +raw: P.Request, +events: List<&2, V.PreparationEvent>) ->
  {Engine.stamp(world, input, selected, C.append(C.core(True{}, I.code(raw), frames), C.prepare_events(events))) ==
    T.append(codec_items(world, input, selected, raw, frames), PhaseSource.phase_items(world, selected, input, events)) : List<&2, O.Item>}:
  match frames:
    case Nil{}: stamp_preparation(world, input, selected, events)
    case Con{+frame, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, tail => Con{O.Item{world, selected, input, O.Core{True{}, I.code(raw), frame}}, tail},
        Engine.stamp(world, input, selected, C.append(C.core(True{}, I.code(raw), rest), C.prepare_events(events))),
        T.append(codec_items(world, input, selected, raw, rest), PhaseSource.phase_items(world, selected, input, events)),
        actual_pipeline_items(rest, world, input, selected, raw, events))


def phase_query(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +events: List<&2, V.PreparationEvent>, +index: Nat, +phase: V.PreparationEvent,
  found: {B.query(V.PreparationEvent, events, index) == Some{phase} : Maybe<&2, V.PreparationEvent>}) ->
  {B.query(O.Item, T.append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events)),
      Nat.add(B.count(Q.Frame, frames), index)) == Some{O.Item{world, E.database(before), input, O.Preparation{phase}}} : Maybe<&2, O.Item>}:
  match frames:
    case Nil{}:
      Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, PhaseSource.phase_items(world, E.database(before), input, events), index),
        Prefix.item_result(world, E.database(before), input, B.query(V.PreparationEvent, events, index)), Some{O.Item{world, E.database(before), input, O.Preparation{phase}}},
        Prefix.exact_phase_query_lifts_to_the_full_observer_item_query(world, E.database(before), input, events, index),
        Equal.cong(Maybe<&2, V.PreparationEvent>, Maybe<&2, O.Item>, result => Prefix.item_result(world, E.database(before), input, result),
          B.query(V.PreparationEvent, events, index), Some{phase}, found))
    case Con{frame, +rest}: phase_query(rest, world, input, before, raw, events, index, phase, found)


def with_run_query(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +frames: List<&2, Q.Frame>, +run: V.PreparationRun, +index: Nat, +phase: V.PreparationEvent,
  found: {B.query(V.PreparationEvent, V.events(run), index) == Some{phase} : Maybe<&2, V.PreparationEvent>}) ->
  {B.query(O.Item, with_run(world, input, before, raw, frames, run), phase_index(frames, index)) ==
    Some{O.Item{world, E.database(before), input, O.Preparation{phase}}} : Maybe<&2, O.Item>}:
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  phase_query(frames, world, input, before, raw, events, index, phase, found)


law every_actual_preparation_phase_query_retains_its_exact_measured_codec_offset:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +mode: V.Mode
  for +raw: P.Request
  for +returns: V.Returns
  for +frames: List<&2, Q.Frame>
  for +index: Nat
  for +phase: V.PreparationEvent
  for found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index) == Some{phase} : Maybe<&2, V.PreparationEvent>}
  {B.query(O.Item, source(c, world, input, before, mode, raw, returns, frames), phase_index(frames, index)) ==
    Some{O.Item{world, E.database(before), input, O.Preparation{phase}}} : Maybe<&2, O.Item>}
def every_actual_preparation_phase_query_retains_its_exact_measured_codec_offset(c, world, input, before, mode, raw, returns, frames, index, phase, found):
  with_run_query(world, input, before, raw, frames, V.run(c, mode, raw, before, returns), index, phase, found)


def returns(primitives: Dispatch.Primitives) -> V.Returns:
  Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send} = primitives
  V.Returns{checker, allocation, seal, send}


def decoded_run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +primitives: Dispatch.Primitives) ->
  {Dispatch.decoded(c, binding, public, before, Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, primitives) ==
    C.prefix(C.core(True{}, I.code(raw), frames), C.preparation(V.run(c, mode, raw, before, returns(primitives)))) : C.CallRun}:
  match mode primitives:
    case V.PrepareMode{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}: {==}
    case V.ReadMode{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}: {==}


def actual_preparation_block_items(+ordinal: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, +run: V.PreparationRun) ->
  {Engine.block_items(Engine.Block{ordinal, True{}, input, before, C.prefix(C.core(True{}, I.code(raw), frames), C.preparation(run))}) ==
    with_run(Succ{ordinal}, input, before, raw, frames, run) : List<&2, O.Item>}:
  V.PreparationRun{+events, result, snapshot, waiting, closed} = run
  Equal.cong(List<&2, O.Item>, List<&2, O.Item>, tail => Con{O.Item{Succ{ordinal}, E.database(before), input, O.Selection{before}}, tail},
    Engine.stamp(Succ{ordinal}, input, E.database(before), C.append(C.core(True{}, I.code(raw), frames), C.prepare_events(events))),
    T.append(codec_items(Succ{ordinal}, input, E.database(before), raw, frames), PhaseSource.phase_items(Succ{ordinal}, E.database(before), input, events)),
    actual_pipeline_items(frames, Succ{ordinal}, input, E.database(before), raw, events))


def parsed(run: Decode.DecodeRun) -> Bool:
  match run:
    case Decode.DecodeRun{Decode.Parsed{wire}, frames}: True{}
    case _: False{}


def parsed_selection(~c: S.Configuration, +current: D.State, +disposition: X.Disposition,
  +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>,
  same: {Decode.disposed(c, current, disposition) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}) ->
  {Engine.selection(disposition) == True{} : Bool}:
  match disposition:
    case X.CloseWithoutResponse{}:
      Equal.cong(Decode.DecodeRun, Bool, parsed, Decode.disposed(c, current, X.CloseWithoutResponse{}), Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, same)
    case X.RefuseClose{+status}:
      Equal.cong(Decode.DecodeRun, Bool, parsed, Decode.disposed(c, current, X.RefuseClose{status}), Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, same)
    case X.RefuseContinue{status}: {==}
    case X.ProcessBody{bytes}: {==}


def block_from_decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +primitives: Dispatch.Primitives,
  selected: {Engine.selection(X.decide_reception(c, input)) == True{} : Bool},
  decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}) ->
  {Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) ==
    source(c, Succ{ordinal}, input, before, mode, raw, returns(primitives), frames) : List<&2, O.Item>}:
  Equal.trans(List<&2, O.Item>, Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})),
    Engine.block_items(Engine.Block{ordinal, True{}, input, before, Dispatch.run(c, binding, public, before, input, primitives)}),
    source(c, Succ{ordinal}, input, before, mode, raw, returns(primitives), frames),
    Equal.cong(Bool, List<&2, O.Item>, selected => Engine.block_items(Engine.Block{ordinal, selected, input, before, Dispatch.run(c, binding, public, before, input, primitives)}),
      Engine.selection(X.decide_reception(c, input)), True{}, selected),
    Equal.trans(List<&2, O.Item>, Engine.block_items(Engine.Block{ordinal, True{}, input, before, Dispatch.run(c, binding, public, before, input, primitives)}),
      Engine.block_items(Engine.Block{ordinal, True{}, input, before, C.prefix(C.core(True{}, I.code(raw), frames), C.preparation(V.run(c, mode, raw, before, returns(primitives))))}),
      source(c, Succ{ordinal}, input, before, mode, raw, returns(primitives), frames),
      Equal.cong(C.CallRun, List<&2, O.Item>, run => Engine.block_items(Engine.Block{ordinal, True{}, input, before, run}),
        Dispatch.run(c, binding, public, before, input, primitives), C.prefix(C.core(True{}, I.code(raw), frames), C.preparation(V.run(c, mode, raw, before, returns(primitives)))),
        Equal.trans(C.CallRun, Dispatch.run(c, binding, public, before, input, primitives),
          Dispatch.decoded(c, binding, public, before, Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, primitives),
          C.prefix(C.core(True{}, I.code(raw), frames), C.preparation(V.run(c, mode, raw, before, returns(primitives)))),
          Equal.cong(Decode.DecodeRun, C.CallRun, run => Dispatch.decoded(c, binding, public, before, run, primitives), Decode.run(c, E.database(before), input),
            Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, decoded), decoded_run(c, binding, public, before, mode, raw, frames, primitives))),
      actual_preparation_block_items(ordinal, input, before, raw, frames, V.run(c, mode, raw, before, returns(primitives)))))


def block_from_decoded_copies(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +primitives: Dispatch.Primitives,
  copies: L.E<{Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun},
    {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}>) ->
  {Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) ==
    source(c, Succ{ordinal}, input, before, mode, raw, returns(primitives), frames) : List<&2, O.Item>}:
  match copies:
    case L.Both{for_selection, for_render}:
      block_from_decoded(c, binding, public, ordinal, before, input, mode, raw, frames, primitives,
        parsed_selection(c, E.database(before), X.decide_reception(c, input), mode, raw, frames, for_selection), for_render)


law actual_decoded_preparation_block_retains_selection_and_every_codec_and_phase_event:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +input: X.Reception
  for +mode: V.Mode
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +primitives: Dispatch.Primitives
  for decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}
  {Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) ==
    source(c, Succ{ordinal}, input, before, mode, raw, returns(primitives), frames) : List<&2, O.Item>}
def actual_decoded_preparation_block_retains_selection_and_every_codec_and_phase_event(c, binding, public, ordinal, before, input, mode, raw, frames, primitives, decoded):
  block_from_decoded_copies(c, binding, public, ordinal, before, input, mode, raw, frames, primitives,
    Q.equality_reopenable(Decode.DecodeRun, Decode.run(c, E.database(before), input), Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, decoded))


law a_real_decoded_preparation_equation_proves_the_prelude_is_internal:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +input: X.Reception
  for +mode: V.Mode
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}
  Micro.Internal(frames)
def a_real_decoded_preparation_equation_proves_the_prelude_is_internal(c, before, input, mode, raw, frames, decoded):
  %Equal.cong(Decode.DecodeRun, List<&2, Q.Frame>, Decode.frames, Decode.run(c, E.database(before), input),
    Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames}, decoded) : Micro.Internal(_)
  DecodeEvents.every_actual_decode_prelude_contains_only_internal_frames(c, E.database(before), input)


# Generic DATA replay algebra. This does not assert arbitrary Core frames are
# valid service observations: the public adapter below uses ACTUAL Decode.frames,
# whose complete non-policy exclusions are proved in DecodeEvents.
def quiet_head_properties(+head: O.Item, +rest: List<&2, O.Item>, +before: E.Snapshot, +count: Nat,
  quiet: {O.change(O.event(head)) == None{} : Maybe<&2, O.Change>},
  properties: Prefix.PrefixProperties(rest, before, count)) -> Prefix.PrefixProperties(Con{head, rest}, before, Succ{count}):
  match properties:
    case L.Both{coherent, L.Both{final, measured}}:
      %Equal.sym(Maybe<&2, O.Change>, O.change(O.event(head)), None{}, quiet) :
        L.E<L.E<T.CoherentChange(_, head, before), T.Coherent(T.take(count, rest), T.next(_, before))>,
          L.E<{T.finish(T.take(count, rest), T.next(_, before)) == before : E.Snapshot},
            {Succ{B.count(O.Item, T.take(count, rest))} == Succ{count} : Nat}>>
      L.Both{L.Both{Unit{}, coherent}, L.Both{final,
        Equal.cong(Nat, Nat, n => Succ{n}, B.count(O.Item, T.take(count, rest)), count, measured)}}


def preceding(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+k: k


def remove_selection_properties(+world: Nat, +input: X.Reception, +before: E.Snapshot, +events: List<&2, V.PreparationEvent>, +count: Nat,
  properties: Prefix.PrefixProperties(Con{O.Item{world, E.database(before), input, O.Selection{before}}, PhaseSource.phase_items(world, E.database(before), input, events)}, before, Succ{count})) ->
  Prefix.PrefixProperties(PhaseSource.phase_items(world, E.database(before), input, events), before, count):
  match properties:
    case L.Both{L.Both{selection, coherent}, L.Both{final, measured}}:
      L.Both{coherent, L.Both{final, Equal.cong(Nat, Nat, preceding,
        Succ{B.count(O.Item, T.take(count, PhaseSource.phase_items(world, E.database(before), input, events)))}, Succ{count}, measured)}}


def insert_codec_properties(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +events: List<&2, V.PreparationEvent>, +count: Nat,
  properties: Prefix.PrefixProperties(PhaseSource.phase_items(world, E.database(before), input, events), before, count)) ->
  Prefix.PrefixProperties(T.append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events)), before,
    Nat.add(B.count(Q.Frame, frames), count)):
  match frames:
    case Nil{}: properties
    case Con{+frame, +rest}:
      quiet_head_properties(O.Item{world, E.database(before), input, O.Core{True{}, I.code(raw), frame}},
        T.append(codec_items(world, input, E.database(before), raw, rest), PhaseSource.phase_items(world, E.database(before), input, events)), before, Nat.add(B.count(Q.Frame, rest), count), {==},
        insert_codec_properties(rest, world, input, before, raw, events, count, properties))


def transfer_run_properties(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, +run: V.PreparationRun, +count: Nat,
  properties: Prefix.PrefixProperties(PhaseSource.with_run(world, input, before, run), before, Succ{count})) ->
  Prefix.PrefixProperties(with_run(world, input, before, raw, frames, run), before, phase_index(frames, count)):
  V.PreparationRun{+events, result, snapshot, waiting, closed} = run
  quiet_head_properties(O.Item{world, E.database(before), input, O.Selection{before}},
    T.append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events)), before,
    Nat.add(B.count(Q.Frame, frames), count), {==}, insert_codec_properties(frames, world, input, before, raw, events, count,
      remove_selection_properties(world, input, before, events, count, properties)))


law actual_decode_prelude_preserves_preparation_prefix_properties_at_the_measured_offset:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +mode: V.Mode
  for +raw: P.Request
  for +returns: V.Returns
  for +count: Nat
  for properties: Prefix.PrefixProperties(PhaseSource.source(c, world, input, before, mode, raw, returns), before, Succ{count})
  Prefix.PrefixProperties(source(c, world, input, before, mode, raw, returns, Decode.frames(Decode.run(c, E.database(before), input))), before,
    phase_index(Decode.frames(Decode.run(c, E.database(before), input)), count))
def actual_decode_prelude_preserves_preparation_prefix_properties_at_the_measured_offset(c, world, input, before, mode, raw, returns, count, properties):
  transfer_run_properties(world, input, before, raw, Decode.frames(Decode.run(c, E.database(before), input)), V.run(c, mode, raw, before, returns), count, properties)


law a_real_decoded_preparation_prelude_excludes_all_nonzero_service_tags:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +world: Nat
  for +before: E.Snapshot
  for +input: X.Reception
  for +mode: V.Mode
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +kind: Nat
  for decoded: {Decode.run(c, E.database(before), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}
  U.NoTag(Succ{kind}, U.values(c, binding, public, codec_items(world, input, E.database(before), raw, frames)))
def a_real_decoded_preparation_prelude_excludes_all_nonzero_service_tags(c, binding, public, world, before, input, mode, raw, frames, kind, decoded):
  DecodeEvents.internal_frames_exclude_nonzero_tags(c, binding, public, frames, world, input, E.database(before), True{}, I.code(raw), kind,
    a_real_decoded_preparation_equation_proves_the_prelude_is_internal(c, before, input, mode, raw, frames, decoded))


def plain_codec(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +selected: D.State, +raw: P.Request) ->
  U.AllPlain(codec_items(world, input, selected, raw, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, plain_codec(rest, world, input, selected, raw)}


def plain_append(+prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, first: U.AllPlain(prefix), later: U.AllPlain(suffix)) -> U.AllPlain(T.append(prefix, suffix)):
  match prefix first:
    case Nil{} _: later
    case Con{head, rest} L.Both{plain, following}: L.Both{plain, plain_append(rest, suffix, following, later)}


law every_full_preparation_block_is_plain_even_when_other_blocks_publish:
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +run: V.PreparationRun
  U.AllPlain(with_run(world, input, before, raw, frames, run))
def every_full_preparation_block_is_plain_even_when_other_blocks_publish(world, input, before, raw, frames, run):
  V.PreparationRun{+events, result, snapshot, waiting, closed} = run
  L.Both{Unit{}, plain_append(codec_items(world, input, E.database(before), raw, frames), PhaseSource.phase_items(world, E.database(before), input, events),
    plain_codec(frames, world, input, E.database(before), raw), Uniqueness.plain_phases(world, E.database(before), input, events))}
