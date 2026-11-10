# Shared syntax boundary for ordinary/cached execution and common IO renderers.
# It records the actual event constructors, independent of any particular law.
import Base
import ../../../../contract/Logic.bend as L
import ../../model/EventObserver.bend as O
import ../../model/FrameBounds.bend as B
import ../../../Foundations.bend as F

def Allowed(event: O.AuditEvent) -> Type:
  match event:
    case O.Core{mode, code, frame}: Unit
    case O.BoundCore{mode, origin, frame}: Unit
    case O.Selection{snapshot}: Unit
    case O.Resolution{raw, entry, context}: Unit
    case O.Publication{mode, response, bytes, before, after}: Unit
    case O.Preparation{phase}: Empty
    case O.Invalidation{phase}: Empty

def All(events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Allowed(event), All(rest)>

def query(+events: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  all: All(events), found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) -> Allowed(event):
  match events index all:
    case Nil{} _ unit: L.ex_false(Allowed(event), F.none_negative_some(O.AuditEvent, event, found))
    case Con{+head, rest} Zero{} L.Both{first, later}:
      %F.some_injective(O.AuditEvent, head, event, found) : Allowed(_)
      first
    case Con{head, +rest} Succ{prior} L.Both{first, later}: query(rest, prior, event, later, found)
