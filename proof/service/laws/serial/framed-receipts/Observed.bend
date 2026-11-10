# Full metadata ReceiptPrepared Rule7 from ANY actual serial observation.
# No physical/semantic/native/current/frame/outcome boundary is assumed.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../HostTransitions.bend as Host
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Binding
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Engine.bend as Engine
import ../header/History.bend as History
import ./Phases.bend as Preparation
import ./Source.bend as Framed
import ./History.bend as FramedHistory


def receipt_kind(fact: E.Fact) -> Bool:
  match fact:
    case E.ReceiptPrepared{receipt, bytes}: True{}
    case _: False{}

def Claim(~c: S.Configuration, fact: E.Fact) -> Type:
  match fact:
    case E.ReceiptPrepared{receipt, bytes}: Preparation.Receipt(c, receipt, bytes)
    case _: Unit

def core(~c: S.Configuration, mode: Bool, -fact: I.Fact) -> Claim(c, E.core_fact(mode, fact)):
  match mode:
    case False{}: Unit{}
    case True{}: Unit{}

def phase(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, event: V.PreparationEvent, properties: Preparation.Claim(c, event)) -> Claim(c, V.fact(c, binding, public, event)):
  match event:
    case V.ReceiptPrepared{receipt, bytes}: properties
    case V.WireReceived{wire}: Unit{}
    case V.IdentityEstablished{wire, context}: Unit{}
    case V.Accepted{wire, context}: Unit{}
    case V.Refuted{wire, context}: Unit{}
    case V.PrimitiveFailed{stage, identifier, fatal}: Unit{}
    case V.HandleChosen{handle}: Unit{}
    case V.ArtifactSealed{entry}: Unit{}
    case V.RegistryChanged{entry, before, after}: Unit{}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Unit{}
    case V.ErrorPrepared{status, bytes}: Unit{}
    case V.ErrorConcluded{status, snapshot, closes}: Unit{}
    case V.Delivered{bytes}: Unit{}
    case V.Interrupted{prefix}: Unit{}
    case V.Closed{}: Unit{}


def event(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, actual: O.AuditEvent, properties: Framed.Claim(c, actual)) -> Claim(c, O.fact(c, binding, public, actual)):
  match actual:
    case O.Core{mode, code, frame}: core(c, mode, Q.fact_of_frame(c, Binding.program(binding, Host.origin(public, code)), frame))
    case O.BoundCore{mode, origin, frame}: core(c, mode, Q.fact_of_frame(c, Binding.program(binding, origin), frame))
    case O.Preparation{value}: phase(c, binding, public, value, properties)
    case O.Invalidation{N.InvalidationBase{value}}: phase(c, binding, public, value, properties)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: Unit{}
    case O.Selection{snapshot}: Unit{}
    case O.Resolution{raw, entry, context}: Unit{}
    case O.Publication{mode, response, bytes, before, after}: Unit{}

def not_equal(+receipt: W.Receipt, +bytes: List<&2, U32>, -other: E.Fact,
  absent: {receipt_kind(other) == False{} : Bool}, equal: {E.ReceiptPrepared{receipt, bytes} == other : E.Fact}) -> Empty:
  F.false_negative_true(Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, receipt_kind(other), False{},
    Equal.cong(E.Fact, Bool, receipt_kind, E.ReceiptPrepared{receipt, bytes}, other, equal), absent)))

def core_not_receipt(mode: Bool, -fact: I.Fact) -> {receipt_kind(E.core_fact(mode, fact)) == False{} : Bool}:
  match mode:
    case False{}: {==}
    case True{}: {==}

def no_cofact(+actual: O.AuditEvent, +receipt: W.Receipt, +bytes: List<&2, U32>, relation: O.PublicationFact(actual, E.ReceiptPrepared{receipt, bytes})) -> Empty:
  match actual:
    case O.Core{mode, code, frame}: relation
    case O.BoundCore{mode, origin, frame}: relation
    case O.Preparation{phase}: relation
    case O.Invalidation{phase}: relation
    case O.Selection{snapshot}: relation
    case O.Resolution{raw, entry, context}: relation
    case O.Publication{+mode, response, publication_bytes, before, +after}: not_equal(receipt, bytes, E.core_fact(mode, I.Published{E.database(after)}), core_not_receipt(mode, I.Published{E.database(after)}), relation)

def relation(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +actual: O.AuditEvent, +receipt: W.Receipt, +bytes: List<&2, U32>,
  properties: Framed.Claim(c, actual), related: O.RelFact(c, binding, public, actual, E.ReceiptPrepared{receipt, bytes})) -> Preparation.Receipt(c, receipt, bytes):
  match related:
    case L.Left{canonical}:
      %Equal.sym(E.Fact, E.ReceiptPrepared{receipt, bytes}, O.fact(c, binding, public, actual), canonical) : Claim(c, _)
      event(c, binding, public, actual, properties)
    case L.Right{cofact}: L.ex_false(Preparation.Receipt(c, receipt, bytes), no_cofact(actual, receipt, bytes, cofact))

def initial_empty(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String, ~instance: String, at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  initial: O.InitialFact(c, seed, pi, instance, at, E.ReceiptPrepared{receipt, bytes})) -> Empty:
  match at:
    case 0n: not_equal(receipt, bytes, E.Ordinary{I.ProofInitialAccepts{}}, {==}, initial)
    case 1n+next:
      match next:
        case 0n: not_equal(receipt, bytes, E.Ordinary{I.InstanceStarted{seed(Unit{})}}, {==}, initial)
        case 1n+later:
          match later:
            case 0n: not_equal(receipt, bytes, E.Boot{E.Snapshot{instance, seed(Unit{}), [], []}}, {==}, initial)
            case 1n+rest: initial

def for_item(~c: S.Configuration, ~a: E.Environment, -k: String, -at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>, item: O.Item,
  property: Preparation.Receipt(c, receipt, bytes)) -> E.Rule7(a, E.ReceiptPrepared{receipt, bytes}, k, O.scenario(c, item), at):
  match item:
    case O.Item{world, selected, input, event}: property

def listed(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String, -x: I.Scenario, -at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: O.ListedObserved(c, binding, public, History.items(c, binding, public, script, seed, instance), x, at, E.ReceiptPrepared{receipt, bytes})) ->
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at):
  match actual:
    case (+global, +item, L.Both{time, L.Both{found, L.Both{scenario, related}}}):
      %Equal.sym(I.Scenario, x, O.scenario(c, item), scenario) : E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), _, at)
      for_item(c, History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), at, receipt, bytes, item,
        relation(c, binding, public, O.event(item), receipt, bytes,
          FramedHistory.query(c, History.items(c, binding, public, script, seed, instance), global, item,
            FramedHistory.every_actual_complete_serial_history_preserves_all_metadata_receipt_frame_encodings_and_bounds(c, binding, public, script, 0n, History.boot(seed, instance)), found), related))

law every_actual_observed_metadata_prepared_receipt_follows_complete_rule7_without_any_native_or_output_premise:
  for ~c: S.Configuration
  for ~binding: Binding.Source
  for ~public: List<&2, Binding.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for -x: I.Scenario
  for +at: Nat
  for +receipt: W.Receipt
  for +bytes: List<&2, U32>
  for observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), x, at, E.ReceiptPrepared{receipt, bytes})
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at)
def every_actual_observed_metadata_prepared_receipt_follows_complete_rule7_without_any_native_or_output_premise(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, observed):
  match observed:
    case L.Both{artifact, L.Left{L.Both{scenario, initial}}}:
      L.ex_false(E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at), initial_empty(c, seed, pi, instance, at, receipt, bytes, initial))
    case L.Both{artifact, L.Right{actual}}: listed(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, actual)
