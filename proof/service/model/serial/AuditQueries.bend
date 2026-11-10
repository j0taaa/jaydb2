# Lossless append/prefix query arithmetic for actual audit-event renderers.
import Base
import ../../../../contract/Logic.bend as L
import ../../../Foundations.bend as F
import ../EventObserver.bend as O
import ../FrameBounds.bend as B
import ./Common.bend as C
import ./PublicationDispatch.bend as Absent


def prefix_query(+prefix: List<&2, O.AuditEvent>, -suffix: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  found: {B.query(O.AuditEvent, prefix, index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  {B.query(O.AuditEvent, C.append(prefix, suffix), index) == Some{event} : Maybe<&2, O.AuditEvent>}:
  match prefix index:
    case Nil{} _:
      L.ex_false({B.query(O.AuditEvent, suffix, index) == Some{event} : Maybe<&2, O.AuditEvent>}, F.none_negative_some(O.AuditEvent, event, found))
    case Con{head, rest} 0n: found
    case Con{head, rest} 1n+k: prefix_query(rest, suffix, k, event, found)


def suffix_query(prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, +index: Nat, -event: O.AuditEvent,
  found: {B.query(O.AuditEvent, suffix, index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  {B.query(O.AuditEvent, C.append(prefix, suffix), Nat.add(B.count(O.AuditEvent, prefix), index)) == Some{event} : Maybe<&2, O.AuditEvent>}:
  match prefix:
    case Nil{}: found
    case Con{head, rest}: suffix_query(rest, suffix, index, event, found)


def lift_position(-head: O.AuditEvent, -rest: List<&2, O.AuditEvent>, -suffix: List<&2, O.AuditEvent>, -index: Nat, -event: O.AuditEvent,
  located: &local: Nat -> L.E<{index == Nat.add(B.count(O.AuditEvent, rest), local) : Nat}, {B.query(O.AuditEvent, suffix, local) == Some{event} : Maybe<&2, O.AuditEvent>}>) ->
  &local: Nat -> L.E<{Succ{index} == Nat.add(B.count(O.AuditEvent, Con{head, rest}), local) : Nat}, {B.query(O.AuditEvent, suffix, local) == Some{event} : Maybe<&2, O.AuditEvent>}>:
  match located:
    case (+local, L.Both{position, query}): (local, L.Both{Equal.cong(Nat, Nat, value => Succ{value}, index, Nat.add(B.count(O.AuditEvent, rest), local), position), query})


def strip_publication_prefix(+prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, index: Nat,
  +event: O.AuditEvent,
  silent: Absent.Quiet(prefix), target: {Absent.NoPublication(event) == Empty : Type},
  found: {B.query(O.AuditEvent, C.append(prefix, suffix), index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  &local: Nat -> L.E<{index == Nat.add(B.count(O.AuditEvent, prefix), local) : Nat}, {B.query(O.AuditEvent, suffix, local) == Some{event} : Maybe<&2, O.AuditEvent>}>:
  match prefix index silent:
    case Nil{} index unit: (index, L.Both{{==}, found})
    case Con{+head, rest} 0n L.Both{absent, later}:
      L.ex_false((&local: Nat -> L.E<{0n == Nat.add(B.count(O.AuditEvent, Con{head, rest}), local) : Nat}, {B.query(O.AuditEvent, suffix, local) == Some{event} : Maybe<&2, O.AuditEvent>}>),
        (%target : _
          %F.some_injective(O.AuditEvent, head, event, found) : Absent.NoPublication(_)
          absent))
    case Con{head, rest} 1n+k L.Both{absent, later}:
      lift_position(head, rest, suffix, k, event, strip_publication_prefix(rest, suffix, k, event, later, target, found))
