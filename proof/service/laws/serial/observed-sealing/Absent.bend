# Actual common runtime renderers cannot produce either host header.
# The proof covers every return, retaining all actual events.
import Base
import ../../../../../contract/Logic.bend as L
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C


import ./SealingData.bend as Header


def All(events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Header.NoSite(event), All(rest)>


def Call(run: C.CallRun) -> Type:
  All(C.events(run))


def appended(+first: List<&2, O.AuditEvent>, -last: List<&2, O.AuditEvent>, a: All(first), b: All(last)) -> All(C.append(first, last)):
  match first a:
    case Nil{} unit: b
    case Con{head, +rest} L.Both{first, later}: L.Both{first, appended(rest, last, later, b)}


def prefixed(+prefix: List<&2, O.AuditEvent>, run: C.CallRun, first: All(prefix), later: Call(run)) -> Call(C.prefix(prefix, run)):
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}: appended(prefix, events, first, later)
