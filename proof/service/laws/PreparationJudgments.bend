# The original source/checker judgments are consumed once and split into the
# distinct derivation, universal semantic and read-only obligations. Changing
# only operational observations does not change those logical judgments.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../../HostTransitions.bend as Host
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../model/EventObserver.bend as O

def Payload(-a: I.Environment, -c: S.Configuration, operation: W.Operation, -raw: P.Request, -program: S.Program) -> Type:
  L.E<H.AdmissionDerivation(operation, a, c, raw, program),
    L.E<H.Universal(c, I.code(raw), program), E.ReadModeEvidence(operation, program)>>

law original_declarations_supply_all_preparation_acceptance_judgments:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for checked: Host.PreparationChecked(binding, c, public, raw, V.read_only(mode))
  Payload(Source.environment(binding), c, V.operation(mode), raw,
    Source.program(binding, Host.origin(public, I.code(raw))))
def original_declarations_supply_all_preparation_acceptance_judgments(binding, public, c, mode, raw, checked):
  match mode checked:
    case V.PrepareMode{} L.Both{bound, L.Both{derived, L.Both{universal, read}}}:
      L.Both{L.Both{bound, derived}, L.Both{universal, Unit{}}}
    case V.ReadMode{} L.Both{bound, L.Both{derived, L.Both{universal, L.Both{read_derived, read_property}}}}:
      L.Both{L.Both{bound, L.Both{derived, read_derived}}, L.Both{universal, read_property}}

law the_same_original_judgments_hold_for_the_full_operational_observer:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +mode: V.Mode
  for +raw: P.Request
  for checked: Host.PreparationChecked(binding, c, public, raw, V.read_only(mode))
  Payload(E.core_environment(True{}, O.environment(binding, public, c, seed, pi, artifacts, items, instance)), c,
    V.operation(mode), raw, Source.program(binding, Host.origin(public, I.code(raw))))
def the_same_original_judgments_hold_for_the_full_operational_observer(binding, public, c, seed, pi, artifacts, items,
  instance, mode, raw, checked):
  match mode:
    case V.PrepareMode{}: original_declarations_supply_all_preparation_acceptance_judgments(binding, public, c, V.PrepareMode{}, raw, checked)
    case V.ReadMode{}: original_declarations_supply_all_preparation_acceptance_judgments(binding, public, c, V.ReadMode{}, raw, checked)
