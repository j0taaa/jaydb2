# Recover the exact admitted mode certificate from registry lifecycle history.
# Register events carry genuine admission evidence; they are not host traces or
# authentication/ordering proofs. Artifact integrity is checked per call.
import Base
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedRegistry.bend as G
import ../contract/Semantics.bend as S

type RegistryEvent is Data:
  Register{entry: G.Entry}
  Invalidate{handle: String}

def EntryAdmission(~a: I.Environment, ~c: S.Configuration, +entry: G.Entry) -> Type:
  &program: S.Program -> H.ModeCertificateValid(a, c, entry, program)

def EntryProperty(~a: I.Environment, ~c: S.Configuration) -> G.Entry -> Type:
  entry => EntryAdmission(a, c, entry)

def HistoryAdmission(~a: I.Environment, ~c: S.Configuration, events: List<&2, RegistryEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{Register{entry}, rest}:
      L.E<EntryAdmission(a, c, entry), HistoryAdmission(a, c, rest)>
    case Con{Invalidate{handle}, rest}: HistoryAdmission(a, c, rest)

def step(instance: String, event: RegistryEvent, entries: List<&2, G.Entry>) -> List<&2, G.Entry>:
  match event:
    case Register{entry}: G.insert(True{}, instance, entry, entries)
    case Invalidate{handle}: G.remove(instance, handle, entries)

def run(+instance: String, events: List<&2, RegistryEvent>, entries: List<&2, G.Entry>) -> List<&2, G.Entry>:
  match events:
    case Nil{}: entries
    case Con{event, rest}: run(instance, rest, step(instance, event, entries))

law history_preserves_admitted_entries:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for +events: List<&2, RegistryEvent>
  for +before: List<&2, G.Entry>
  for admitted: G.AllEntries(EntryProperty(a, c), before)
  for history: HistoryAdmission(a, c, events)
  G.AllEntries(EntryProperty(a, c), run(instance, events, before))
def history_preserves_admitted_entries(a, c, instance, events, before, admitted, history):
  match events:
    case Nil{}: admitted
    case Con{Register{+entry}, +rest}:
      L.Both{certificate, later} = history
      history_preserves_admitted_entries(a, c, instance, rest, G.insert(True{}, instance, entry, before),
        G.insertion_preserves_registered_entry_properties(EntryProperty(a, c),
          True{}, instance, entry, before, certificate, admitted), later)
    case Con{Invalidate{+handle}, +rest}:
      history_preserves_admitted_entries(a, c, instance, rest, G.remove(instance, handle, before),
        G.removal_preserves_registered_entry_properties(EntryProperty(a, c),
          instance, handle, before, admitted), history)

law history_from_empty_contains_only_admitted_entries:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for +events: List<&2, RegistryEvent>
  for history: HistoryAdmission(a, c, events)
  G.AllEntries(EntryProperty(a, c), run(instance, events, Nil{}))
def history_from_empty_contains_only_admitted_entries(a, c, instance, events, history):
  history_preserves_admitted_entries(a, c, instance, events, Nil{}, Unit{}, history)

law lookup_after_admitted_history_recovers_exact_mode_certificate:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for +events: List<&2, RegistryEvent>
  for +handle: String
  for +entry: G.Entry
  for history: HistoryAdmission(a, c, events)
  for present: {G.lookup(instance, handle, run(instance, events, Nil{})) == Some{entry} : Maybe<&2, G.Entry>}
  EntryAdmission(a, c, entry)
def lookup_after_admitted_history_recovers_exact_mode_certificate(a, c, instance, events, handle, entry, history, present):
  G.lookup_recovers_registered_entry_property(EntryProperty(a, c), instance, handle,
    run(instance, events, Nil{}), entry,
    history_from_empty_contains_only_admitted_entries(a, c, instance, events, history), present)
