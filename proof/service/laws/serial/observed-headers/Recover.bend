# A queried real header forces actual extension decoding and recovers its
# exact full quiet prefix, complete payload and authentication computation.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/LocalHistory.bend as J
import ./HeaderData.bend as H
import ./Layout.bend as Layout
import ./BlockLayout.bend as Block
import ./Query.bend as Query


def Seen(+before: E.Snapshot, -events: List<&2, O.AuditEvent>, -decision: Decode.Decision,
  +point: H.Point, -index: Nat, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>) -> Type:
  &wire: W.WireRequest -> &prefix: List<&2, O.AuditEvent> -> &first: O.AuditEvent -> &second: O.AuditEvent -> &tail: List<&2, O.AuditEvent> ->
    L.E<{decision == Decode.Parsed{wire} : Decode.Decision},
      L.E<{events == C.append(prefix, Con{first, Con{second, tail}}) : List<&2, O.AuditEvent>},
        L.E<{index == Nat.add(B.count(O.AuditEvent, prefix), H.offset(point)) : Nat},
          L.E<{H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, D.authenticate(E.database(before), I.credential(W.raw(wire)))) : H.View},
            L.E<J.Quiet(prefix), L.E<{H.event(first) == H.Wire{wire} : H.View},
              L.E<{O.change(first) == None{} : Maybe<&2, O.Change>},
                {H.event(second) == H.Identity{wire, D.authenticate(E.database(before), I.credential(W.raw(wire)))} : H.View}>>>>>>>


def finish(+before: E.Snapshot, -events: List<&2, O.AuditEvent>, -decision: Decode.Decision,
  +point: H.Point, -index: Nat, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>,
  +wire: W.WireRequest, +prefix: List<&2, O.AuditEvent>, +first: O.AuditEvent, +second: O.AuditEvent, +tail: List<&2, O.AuditEvent>,
  parsed: {decision == Decode.Parsed{wire} : Decode.Decision}, exact: {events == C.append(prefix, Con{first, Con{second, tail}}) : List<&2, O.AuditEvent>},
  quiet: J.Quiet(prefix), wire_view: {H.event(first) == H.Wire{wire} : H.View}, wire_quiet: {O.change(first) == None{} : Maybe<&2, O.Change>},
  identity_view: {H.event(second) == H.Identity{wire, D.authenticate(E.database(before), I.credential(W.raw(wire)))} : H.View},
  located: L.E<{index == Nat.add(B.count(O.AuditEvent, prefix), H.offset(point)) : Nat},
    {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, D.authenticate(E.database(before), I.credential(W.raw(wire)))) : H.View}>) ->
  Seen(before, events, decision, point, index, wanted_wire, wanted_context):
  match located:
    case L.Both{position, payload}:
      (wire, prefix, first, second, tail, L.Both{parsed, L.Both{exact, L.Both{position, L.Both{payload, L.Both{quiet, L.Both{wire_view, L.Both{wire_quiet, identity_view}}}}}}})


def from_headers(+before: E.Snapshot, +events: List<&2, O.AuditEvent>, +decision: Decode.Decision,
  +point: H.Point, +index: Nat, +event: O.AuditEvent, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>, +wire: W.WireRequest,
  parsed: {decision == Decode.Parsed{wire} : Decode.Decision},
  source: Layout.Headers(before, wire, events),
  found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>},
  observed: {H.event(event) == H.expected(point, wanted_wire, wanted_context) : H.View}) -> Seen(before, events, decision, point, index, wanted_wire, wanted_context):
  match source:
    case (+prefix, +first, +second, +tail, L.Both{+exact, L.Both{prefix_absent, L.Both{quiet, L.Both{+wire_view, L.Both{wire_quiet, L.Both{+identity_view, tail_absent}}}}}}):
      finish(before, events, decision, point, index, wanted_wire, wanted_context, wire, prefix, first, second, tail, parsed, exact, quiet, wire_view, wire_quiet, identity_view,
        Query.in_prefix(point, wanted_wire, wanted_context, wire, D.authenticate(E.database(before), I.credential(W.raw(wire))), prefix, first, second, tail, index, event,
          prefix_absent, wire_view, identity_view, tail_absent,
          Equal.trans(Maybe<&2, O.AuditEvent>, B.query(O.AuditEvent, C.append(prefix, Con{first, Con{second, tail}}), index), B.query(O.AuditEvent, events, index), Some{event},
            Equal.cong(List<&2, O.AuditEvent>, Maybe<&2, O.AuditEvent>, xs => B.query(O.AuditEvent, xs, index), C.append(prefix, Con{first, Con{second, tail}}), events,
              Equal.sym(List<&2, O.AuditEvent>, events, C.append(prefix, Con{first, Con{second, tail}}), exact)), found), observed))


def from_choice(+before: E.Snapshot, +events: List<&2, O.AuditEvent>, +decision: Decode.Decision,
  +point: H.Point, +index: Nat, +event: O.AuditEvent, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>,
  source: Layout.Choice(before, decision, events),
  found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>},
  observed: {H.event(event) == H.expected(point, wanted_wire, wanted_context) : H.View}) -> Seen(before, events, decision, point, index, wanted_wire, wanted_context):
  match decision:
    case Decode.Parsed{W.Extension{operation, raw}}:
      from_headers(before, events, Decode.Parsed{W.Extension{operation, raw}}, point, index, event, wanted_wire, wanted_context, W.Extension{operation, raw}, {==}, source, found, observed)
    case Decode.Parsed{W.Ordinary{raw}}:
      L.ex_false(Seen(before, events, Decode.Parsed{W.Ordinary{raw}}, point, index, wanted_wire, wanted_context), Query.excluded(events, index, event, source, found, Query.event_relevant(point, wanted_wire, wanted_context, event, observed)))
    case Decode.Shutdown{}:
      L.ex_false(Seen(before, events, Decode.Shutdown{}, point, index, wanted_wire, wanted_context), Query.excluded(events, index, event, source, found, Query.event_relevant(point, wanted_wire, wanted_context, event, observed)))
    case Decode.TransportStopped{}:
      L.ex_false(Seen(before, events, Decode.TransportStopped{}, point, index, wanted_wire, wanted_context), Query.excluded(events, index, event, source, found, Query.event_relevant(point, wanted_wire, wanted_context, event, observed)))
    case Decode.Reject{mode, status, closes}:
      L.ex_false(Seen(before, events, Decode.Reject{mode, status, closes}, point, index, wanted_wire, wanted_context), Query.excluded(events, index, event, source, found, Query.event_relevant(point, wanted_wire, wanted_context, event, observed)))


law every_actual_block_header_query_recovers_its_real_decoding_prefix_and_authentication:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +point: H.Point
  for +index: Nat
  for +event: O.AuditEvent
  for +wire: W.WireRequest
  for +context: Maybe<&2, D.Context>
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>}
  for observed: {H.event(event) == H.expected(point, wire, context) : H.View}
  Seen(Chain.block_before(block), Block.events(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), point, index, wire, context)
def every_actual_block_header_query_recovers_its_real_decoding_prefix_and_authentication(c, binding, public, script, initial_ordinal, initial, owner, block, point, index, event, wire, context, block_found, found, observed):
  from_choice(Chain.block_before(block), Block.events(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), point, index, event, wire, context,
    Block.every_actual_retained_block_derives_its_complete_header_grammar_and_real_decoder_decision(c, binding, public, script, initial_ordinal, initial, owner, block, block_found), found, observed)
