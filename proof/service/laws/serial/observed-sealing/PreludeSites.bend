# Reverse query bridge for the REAL Selection + actual codec frames + phase
# source. Every metadata gap is counted. No assumed phase/view equality.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../Foundations.bend as F
import ../../../../ProtocolService.bend as Q
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/EventHistory.bend as T
import ../../../model/FrameBounds.bend as B
import ../../../model/PreparationCurrent.bend as Phase
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ./SealingData.bend as Data


def PhaseHit(+world: Nat, +input: X.Reception, +selected: D.State, -events: List<&2, V.PreparationEvent>, -index: Nat, -item: O.Item) -> Type:
  &phase: V.PreparationEvent ->
    L.E<{B.query(V.PreparationEvent, events, index) == Some{phase} : Maybe<&2, V.PreparationEvent>},
      {item == O.Item{world, selected, input, O.Preparation{phase}} : O.Item}>


def phase_query(+world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, V.PreparationEvent>, index: Nat, +item: O.Item,
  found: {B.query(O.Item, Phase.phase_items(world, selected, input, events), index) == Some{item} : Maybe<&2, O.Item>}) -> PhaseHit(world, input, selected, events, index, item):
  match events index:
    case Nil{} _: L.ex_false(PhaseHit(world, input, selected, Nil{}, index, item), F.none_negative_some(O.Item, item, found))
    case Con{+head, rest} Zero{}:
      (head, L.Both{{==}, Equal.sym(O.Item, O.Item{world, selected, input, O.Preparation{head}}, item,
        F.some_injective(O.Item, O.Item{world, selected, input, O.Preparation{head}}, item, found))})
    case Con{head, +rest} Succ{+prior}: phase_query(world, input, selected, rest, prior, item, found)


def CodecHit(+world: Nat, +input: X.Reception, +before: E.Snapshot, -frames: List<&2, Q.Frame>, -events: List<&2, V.PreparationEvent>, -index: Nat, -item: O.Item) -> Type:
  &local: Nat -> &phase: V.PreparationEvent ->
    L.E<{index == Nat.add(B.count(Q.Frame, frames), local) : Nat},
      L.E<{B.query(V.PreparationEvent, events, local) == Some{phase} : Maybe<&2, V.PreparationEvent>},
        {item == O.Item{world, E.database(before), input, O.Preparation{phase}} : O.Item}>>


def no_codec_item_can_impersonate_a_preparation_site(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frame: Q.Frame, +item: O.Item,
  relevant: Data.Relevant(Data.event(O.event(item))),
  found: {Some{O.Item{world, E.database(before), input, O.Core{True{}, I.code(raw), frame}}} == Some{item} : Maybe<&2, O.Item>}) -> Empty:
  Data.irrelevant(Data.event(O.event(item)), relevant,
    Equal.cong(O.Item, Data.View, i => Data.event(O.event(i)), item, O.Item{world, E.database(before), input, O.Core{True{}, I.code(raw), frame}},
      Equal.sym(O.Item, O.Item{world, E.database(before), input, O.Core{True{}, I.code(raw), frame}}, item,
        F.some_injective(O.Item, O.Item{world, E.database(before), input, O.Core{True{}, I.code(raw), frame}}, item, found))))


def codec_base(+world: Nat, +input: X.Reception, +before: E.Snapshot, -events: List<&2, V.PreparationEvent>, +index: Nat, -item: O.Item,
  hit: PhaseHit(world, input, E.database(before), events, index, item)) -> CodecHit(world, input, before, Nil{}, events, index, item):
  match hit:
    case (phase, query): (index, phase, L.Both{{==}, query})


def codec_step(+frame: Q.Frame, +rest: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +before: E.Snapshot, -events: List<&2, V.PreparationEvent>, +prior: Nat, -item: O.Item,
  hit: CodecHit(world, input, before, rest, events, prior, item)) -> CodecHit(world, input, before, Con{frame, rest}, events, Succ{prior}, item):
  match hit:
    case (+local, phase, L.Both{position, query}):
      (local, phase, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, prior, Nat.add(B.count(Q.Frame, rest), local), position), query})


def codec_query(frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +events: List<&2, V.PreparationEvent>, +index: Nat, +item: O.Item,
  relevant: Data.Relevant(Data.event(O.event(item))),
  found: {B.query(O.Item, T.append(Prelude.codec_items(world, input, E.database(before), raw, frames), Phase.phase_items(world, E.database(before), input, events)), index) == Some{item} : Maybe<&2, O.Item>}) ->
  CodecHit(world, input, before, frames, events, index, item):
  match frames index:
    case Nil{} _:
      codec_base(world, input, before, events, index, item, phase_query(world, input, E.database(before), events, index, item, found))
    case Con{+frame, rest} Zero{}:
      L.ex_false(CodecHit(world, input, before, Con{frame, rest}, events, 0n, item), no_codec_item_can_impersonate_a_preparation_site(world, input, before, raw, frame, item, relevant, found))
    case Con{frame, +rest} Succ{+prior}:
      codec_step(frame, rest, world, input, before, events, prior, item, codec_query(rest, world, input, before, raw, events, prior, item, relevant, found))


def Hit(+world: Nat, +input: X.Reception, +before: E.Snapshot, -frames: List<&2, Q.Frame>, -run: V.PreparationRun, -index: Nat, -item: O.Item) -> Type:
  &local: Nat -> &phase: V.PreparationEvent ->
    L.E<{index == Prelude.phase_index(frames, local) : Nat},
      L.E<{B.query(V.PreparationEvent, V.events(run), local) == Some{phase} : Maybe<&2, V.PreparationEvent>},
        {item == O.Item{world, E.database(before), input, O.Preparation{phase}} : O.Item}>>


def after_selection(+world: Nat, +input: X.Reception, +before: E.Snapshot, +frames: List<&2, Q.Frame>, +run: V.PreparationRun, +prior: Nat, -item: O.Item,
  hit: CodecHit(world, input, before, frames, V.events(run), prior, item)) -> Hit(world, input, before, frames, run, Succ{prior}, item):
  match hit:
    case (+local, phase, L.Both{position, query}):
      (local, phase, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, prior, Nat.add(B.count(Q.Frame, frames), local), position), query})


def query(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, run: V.PreparationRun, +index: Nat, +item: O.Item,
  relevant: Data.Relevant(Data.event(O.event(item))),
  found: {B.query(O.Item, Prelude.with_run(world, input, before, raw, frames, run), index) == Some{item} : Maybe<&2, O.Item>}) ->
  Hit(world, input, before, frames, run, index, item):
  match run index:
    case V.PreparationRun{events, result, snapshot, waiting, closed} Zero{}:
      L.ex_false(Hit(world, input, before, frames, V.PreparationRun{events, result, snapshot, waiting, closed}, 0n, item),
        Data.irrelevant(Data.event(O.event(item)), relevant,
          Equal.cong(O.Item, Data.View, i => Data.event(O.event(i)), item, O.Item{world, E.database(before), input, O.Selection{before}},
            Equal.sym(O.Item, O.Item{world, E.database(before), input, O.Selection{before}}, item,
              F.some_injective(O.Item, O.Item{world, E.database(before), input, O.Selection{before}}, item, found)))))
    case V.PreparationRun{+events, result, snapshot, waiting, closed} Succ{+prior}:
      after_selection(world, input, before, frames, V.PreparationRun{events, result, snapshot, waiting, closed}, prior, item,
        codec_query(frames, world, input, before, raw, events, prior, item, relevant, found))


law an_actual_preparation_site_item_query_recovers_its_same_phase_and_exact_measured_codec_offset:
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +run: V.PreparationRun
  for +index: Nat
  for +item: O.Item
  for relevant: Data.Relevant(Data.event(O.event(item)))
  for found: {B.query(O.Item, Prelude.with_run(world, input, before, raw, frames, run), index) == Some{item} : Maybe<&2, O.Item>}
  Hit(world, input, before, frames, run, index, item)
def an_actual_preparation_site_item_query_recovers_its_same_phase_and_exact_measured_codec_offset(world, input, before, raw, frames, run, index, item, relevant, found):
  query(world, input, before, raw, frames, run, index, item, relevant, found)
