# One reverse codec/selection query bridge shared by both receipt branches.
# The measured offset uses the ORIGINAL PreparationPrelude.phase_index.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../ProtocolService.bend as Q
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/EventHistory.bend as T
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ./Projection.bend as Projection

def Shift(-count: Nat, -tail: List<&2, O.Item>, -index: Nat, -item: O.Item) -> Type:
  &local: Nat -> L.E<{index == Nat.add(count, local) : Nat}, {B.query(O.Item, tail, local) == Some{item} : Maybe<&2, O.Item>}>

def Hit(-frames: List<&2, Q.Frame>, -tail: List<&2, O.Item>, -index: Nat, -item: O.Item) -> Type:
  &local: Nat -> L.E<{index == Prelude.phase_index(frames, local) : Nat}, {B.query(O.Item, tail, local) == Some{item} : Maybe<&2, O.Item>}>

def header_contradiction(+item: O.Item, +header: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  absent: {Projection.event(O.event(header)) == Projection.NoReceipt{} : Projection.View},
  found: {Some{header} == Some{item} : Maybe<&2, O.Item>}) -> Empty:
  %Equal.sym(Projection.View, Projection.Metadata{receipt, bytes}, Projection.NoReceipt{},
    Equal.trans(Projection.View, Projection.Metadata{receipt, bytes}, Projection.event(O.event(item)), Projection.NoReceipt{}, Equal.sym(Projection.View, Projection.event(O.event(item)), Projection.Metadata{receipt, bytes}, actual),
      Equal.trans(Projection.View, Projection.event(O.event(item)), Projection.event(O.event(header)), Projection.NoReceipt{},
        Equal.cong(O.Item, Projection.View, i => Projection.event(O.event(i)), item, header, Equal.sym(O.Item, header, item, F.some_injective(O.Item, header, item, found))), absent))) : Projection.Void(_)
  Unit{}

def step(+frame: Q.Frame, +rest: List<&2, Q.Frame>, -tail: List<&2, O.Item>, +index: Nat, -item: O.Item, hit: Shift(B.count(Q.Frame, rest), tail, index, item)) -> Shift(B.count(Q.Frame, Con{frame, rest}), tail, Succ{index}, item):
  match hit:
    case (+local, L.Both{position, found}): (local, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, index, Nat.add(B.count(Q.Frame, rest), local), position), found})

def codec(frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +selected: D.State, +raw: P.Request, +tail: List<&2, O.Item>, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, T.append(Prelude.codec_items(world, input, selected, raw, frames), tail), index) == Some{item} : Maybe<&2, O.Item>}) -> Shift(B.count(Q.Frame, frames), tail, index, item):
  match frames index:
    case Nil{} index: (index, L.Both{{==}, found})
    case Con{+frame, rest} Zero{}:
      L.ex_false(Shift(B.count(Q.Frame, Con{frame, rest}), tail, 0n, item), header_contradiction(item, O.Item{world, selected, input, O.Core{True{}, I.code(raw), frame}}, receipt, bytes, actual, {==}, found))
    case Con{frame, +rest} Succ{+prior}: step(frame, rest, tail, prior, item, codec(rest, world, input, selected, raw, tail, prior, item, receipt, bytes, actual, found))

def selected_step(+frames: List<&2, Q.Frame>, -tail: List<&2, O.Item>, +index: Nat, -item: O.Item, hit: Shift(B.count(Q.Frame, frames), tail, index, item)) -> Hit(frames, tail, Succ{index}, item):
  match hit:
    case (+local, L.Both{position, found}): (local, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, index, Nat.add(B.count(Q.Frame, frames), local), position), found})

def query(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, +tail: List<&2, O.Item>, index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, Con{O.Item{world, E.database(before), input, O.Selection{before}}, T.append(Prelude.codec_items(world, input, E.database(before), raw, frames), tail)}, index) == Some{item} : Maybe<&2, O.Item>}) -> Hit(frames, tail, index, item):
  match index:
    case Zero{}: L.ex_false(Hit(frames, tail, 0n, item), header_contradiction(item, O.Item{world, E.database(before), input, O.Selection{before}}, receipt, bytes, actual, {==}, found))
    case Succ{+prior}: selected_step(frames, tail, prior, item, codec(frames, world, input, E.database(before), raw, tail, prior, item, receipt, bytes, actual, found))
