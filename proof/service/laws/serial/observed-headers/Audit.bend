# Exact local/global query algebra for retained audit Items. No metadata gap
# or same-slot cofact is erased by these source equalities.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Resources.bend as X
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/EventHistory.bend as T
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/LocalHistory.bend as J
import ./BlockLayout.bend as Block


def stamp_query(+world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  {B.query(O.Item, Engine.stamp(world, input, selected, events), index) == Some{O.Item{world, selected, input, event}} : Maybe<&2, O.Item>}:
  match events index:
    case Nil{} index: L.ex_false({B.query(O.Item, Nil{}, index) == Some{O.Item{world, selected, input, event}} : Maybe<&2, O.Item>}, F.none_negative_some(O.AuditEvent, event, found))
    case Con{+head, rest} 0n:
      Equal.cong(O.AuditEvent, Maybe<&2, O.Item>, e => Some{O.Item{world, selected, input, e}}, head, event, F.some_injective(O.AuditEvent, head, event, found))
    case Con{head, +rest} 1n+previous: stamp_query(world, input, selected, rest, previous, event, found)


def block_items(+block: Engine.Block) ->
  {Engine.block_items(block) == Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block)) : List<&2, O.Item>}:
  match block:
    case Engine.Block{ordinal, selected, input, before, run}: {==}


def block_query(+block: Engine.Block, +index: Nat, +event: O.AuditEvent,
  found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  {B.query(O.Item, Engine.block_items(block), index) == Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}} : Maybe<&2, O.Item>}:
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Engine.block_items(block), index),
    B.query(O.Item, Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block)), index),
    Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}},
    Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, xs => B.query(O.Item, xs, index), Engine.block_items(block),
      Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block)), block_items(block)),
    stamp_query(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), index, event, found))


def first_query(+prefix: List<&2, O.AuditEvent>, +first: O.AuditEvent, +second: O.AuditEvent, +tail: List<&2, O.AuditEvent>) ->
  {B.query(O.AuditEvent, C.append(prefix, Con{first, Con{second, tail}}), Nat.add(B.count(O.AuditEvent, prefix), 0n)) == Some{first} : Maybe<&2, O.AuditEvent>}:
  match prefix:
    case Nil{}: {==}
    case Con{head, +rest}: first_query(rest, first, second, tail)


def second_query(+prefix: List<&2, O.AuditEvent>, +first: O.AuditEvent, +second: O.AuditEvent, +tail: List<&2, O.AuditEvent>) ->
  {B.query(O.AuditEvent, C.append(prefix, Con{first, Con{second, tail}}), Nat.add(B.count(O.AuditEvent, prefix), 1n)) == Some{second} : Maybe<&2, O.AuditEvent>}:
  match prefix:
    case Nil{}: {==}
    case Con{head, +rest}: second_query(rest, first, second, tail)


def from_exact(+events: List<&2, O.AuditEvent>, +prefix: List<&2, O.AuditEvent>, +first: O.AuditEvent, +second: O.AuditEvent, +tail: List<&2, O.AuditEvent>,
  +index: Nat, +event: O.AuditEvent, exact: {events == C.append(prefix, Con{first, Con{second, tail}}) : List<&2, O.AuditEvent>},
  found: {B.query(O.AuditEvent, C.append(prefix, Con{first, Con{second, tail}}), index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}:
  Equal.trans(Maybe<&2, O.AuditEvent>, B.query(O.AuditEvent, events, index), B.query(O.AuditEvent, C.append(prefix, Con{first, Con{second, tail}}), index), Some{event},
    Equal.cong(List<&2, O.AuditEvent>, Maybe<&2, O.AuditEvent>, xs => B.query(O.AuditEvent, xs, index), events, C.append(prefix, Con{first, Con{second, tail}}), exact), found)


def replay_identity_prefix(+world: Nat, +input: X.Reception, +selected: D.State, +before: E.Snapshot,
  +prefix: List<&2, O.AuditEvent>, +first: O.AuditEvent, +second: O.AuditEvent, +tail: List<&2, O.AuditEvent>,
  quiet: J.Quiet(prefix), first_quiet: {O.change(first) == None{} : Maybe<&2, O.Change>}) ->
  {T.finish(T.take(Nat.add(B.count(O.AuditEvent, prefix), 1n), Engine.stamp(world, input, selected, C.append(prefix, Con{first, Con{second, tail}}))), before) == before : E.Snapshot}:
  match prefix quiet:
    case Nil{} unit:
      %Equal.sym(Maybe<&2, O.Change>, O.change(first), None{}, first_quiet) : {T.next(_, before) == before : E.Snapshot}
      {==}
    case Con{+head, +rest} L.Both{head_quiet, later}:
      %Equal.sym(Maybe<&2, O.Change>, O.change(head), None{}, head_quiet) :
        {T.finish(T.take(Nat.add(B.count(O.AuditEvent, rest), 1n), Engine.stamp(world, input, selected, C.append(rest, Con{first, Con{second, tail}}))), T.next(_, before)) == before : E.Snapshot}
      replay_identity_prefix(world, input, selected, before, rest, first, second, tail, later, first_quiet)


def actual_replay(+block: Engine.Block, +prefix: List<&2, O.AuditEvent>, +first: O.AuditEvent, +second: O.AuditEvent, +tail: List<&2, O.AuditEvent>,
  exact: {Block.events(block) == C.append(prefix, Con{first, Con{second, tail}}) : List<&2, O.AuditEvent>},
  quiet: J.Quiet(prefix), first_quiet: {O.change(first) == None{} : Maybe<&2, O.Change>}) ->
  {T.finish(T.take(Nat.add(B.count(O.AuditEvent, prefix), 1n), Engine.block_items(block)), Chain.block_before(block)) == Chain.block_before(block) : E.Snapshot}:
  Equal.trans(E.Snapshot, T.finish(T.take(Nat.add(B.count(O.AuditEvent, prefix), 1n), Engine.block_items(block)), Chain.block_before(block)),
    T.finish(T.take(Nat.add(B.count(O.AuditEvent, prefix), 1n), Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), C.append(prefix, Con{first, Con{second, tail}}))), Chain.block_before(block)), Chain.block_before(block),
    Equal.cong(List<&2, O.Item>, E.Snapshot, xs => T.finish(T.take(Nat.add(B.count(O.AuditEvent, prefix), 1n), xs), Chain.block_before(block)), Engine.block_items(block),
      Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), C.append(prefix, Con{first, Con{second, tail}})),
      Equal.trans(List<&2, O.Item>, Engine.block_items(block), Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block)),
        Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), C.append(prefix, Con{first, Con{second, tail}})), block_items(block),
        Equal.cong(List<&2, O.AuditEvent>, List<&2, O.Item>, xs => Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), xs), Block.events(block), C.append(prefix, Con{first, Con{second, tail}}), exact))),
    replay_identity_prefix(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Chain.block_before(block), prefix, first, second, tail, quiet, first_quiet))
