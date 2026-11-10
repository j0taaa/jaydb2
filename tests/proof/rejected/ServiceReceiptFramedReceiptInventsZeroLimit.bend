import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Semantics.bend as S
import ../../../proof/Foundations.bend as F
import ../../../proof/HostTransitions.bend as Host
import ../../../proof/ProtocolService.bend as Q
import ../../../proof/SourceService.bend as Binding
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/serial/Engine.bend as Engine
import ../../../proof/service/laws/serial/header/History.bend as History
import ../../../proof/service/laws/serial/framed-receipts/Phases.bend as Preparation
import ../../../proof/service/laws/serial/framed-receipts/Source.bend as Framed
import ../../../proof/service/laws/serial/framed-receipts/History.bend as FramedHistory


import ../../../proof/service/laws/serial/framed-receipts/Observed.bend as Actual

import ../../../contract/Requirements.bend as R
law false_negative_FramedReceiptInventsZeroLimit:
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
  {R.fits(0n, W.receipt_value(receipt)) == True{} : Bool}
def false_negative_FramedReceiptInventsZeroLimit(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, observed):
  L.and_right(W.ReceiptEncoding(receipt, bytes), {R.fits(0n, W.receipt_value(receipt)) == True{} : Bool},
    Actual.every_actual_observed_metadata_prepared_receipt_follows_complete_rule7_without_any_native_or_output_premise(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, observed))
