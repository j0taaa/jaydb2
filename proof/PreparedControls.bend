# Construct public prepared-control outcomes from the exact admission,
# authentication, physical reception, size and canonical-frame obligations.
# These proofs construct the actual result/cause; no ControlOutcome,
# MetadataCorrect, OutcomeCause or ProtocolError is supplied as a premise.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S

# Reception is supplied separately because RegistrationReady already owns
# its own physical witness. Neither affine proof is copied or manufactured.
law registration_control_outcome:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -c: S.Configuration
  for -initial: D.State
  for -input: X.Reception
  for -instance: String
  for -before: List<&2, G.Entry>
  for operation: W.Operation
  for -raw: P.Request
  for entry: G.Entry
  for context: D.Context
  for program: S.Program
  for -previous_response: List<&2, U32>
  for -bytes: List<&2, U32>
  for received: W.Received(c, input, W.Extension{operation, raw})
  for ready: H.RegistrationReady(a, artifacts, native, world, time, c, initial, input,
    instance, before, operation, raw, entry, context, program)
  for fits: {R.fits(R.limit_response(S.limits(c)),
    W.receipt_value(W.PreparedReceipt{G.handle(entry)})) == True{} : Bool}
  for framed: P.Message(W.receipt_value(W.PreparedReceipt{G.handle(entry)}), bytes)
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, operation, raw,
    H.ControlResult{initial, Con{entry, before}, H.Metadata{W.PreparedReceipt{G.handle(entry)}}},
    previous_response, previous_response, bytes)
def registration_control_outcome(a, artifacts, native, world, time, c, initial, input,
  instance, before, operation, raw, entry, context, program, previous_response, bytes,
  received, ready, fits, framed):
  L.Both{received,
    L.Both{{==}, L.Both{{==}, L.Both{framed, L.Both{fits,
      (entry, context, program, L.Both{ready, L.Both{{==}, {==}}})}}}}}

law invalidation_control_outcome:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -c: S.Configuration
  for -initial: D.State
  for -input: X.Reception
  for -instance: String
  for -before: List<&2, G.Entry>
  for operation: W.Operation
  for -raw: P.Request
  for entry: G.Entry
  for context: D.Context
  for -previous_response: List<&2, U32>
  for -bytes: List<&2, U32>
  for received: W.Received(c, input, W.Extension{operation, raw})
  for invalidating: {operation == W.Invalidate{} : W.Operation}
  for ready: H.InvalidationReady(c, initial, input, instance, before, raw, entry, context)
  for fits: {R.fits(R.limit_response(S.limits(c)),
    W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool}
  for framed: P.Message(W.receipt_value(W.InvalidatedReceipt{}), bytes)
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, operation, raw,
    H.ControlResult{initial, G.remove(instance, I.code(raw), before), H.Metadata{W.InvalidatedReceipt{}}},
    previous_response, previous_response, bytes)
def invalidation_control_outcome(a, artifacts, native, world, time, c, initial, input,
  instance, before, operation, raw, entry, context, previous_response, bytes,
  received, invalidating, ready, fits, framed):
  L.Both{received,
    L.Both{{==}, L.Both{{==}, L.Both{framed, L.Both{fits,
      (entry, context, L.Both{invalidating, L.Both{ready, {==}}})}}}}}

# Receipt overflow follows genuine admission but precedes the artifact seal.
# The returned error has its own canonical frame and bound; an oversized
# proposed receipt does not establish that a fixed error fits by itself.
law oversized_registration_control_outcome:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -c: S.Configuration
  for -initial: D.State
  for -input: X.Reception
  for -instance: String
  for -before: List<&2, G.Entry>
  for operation: W.Operation
  for -raw: P.Request
  for entry: G.Entry
  for context: D.Context
  for program: S.Program
  for -previous_response: List<&2, U32>
  for -bytes: List<&2, U32>
  for received: W.Received(c, input, W.Extension{operation, raw})
  for candidate: H.RegistrationCandidate(a, c, initial, input, instance, before,
    operation, raw, entry, context, program)
  for oversized: H.ReceiptTooLarge(c, W.PreparedReceipt{G.handle(entry)})
  for fits: {R.fits(R.limit_response(S.limits(c)),
    S.response_value(S.response_error(S.Limit{}))) == True{} : Bool}
  for framed: P.Message(S.response_value(S.response_error(S.Limit{})), bytes)
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, operation, raw, H.ControlResult{initial, before, H.Error{S.Limit{}}},
    previous_response, previous_response, bytes)
def oversized_registration_control_outcome(a, artifacts, native, world, time, c, initial,
  input, instance, before, operation, raw, entry, context, program, previous_response,
  bytes, received, candidate, oversized, fits, framed):
  L.Both{received,
    L.Both{{==}, L.Both{{==}, L.Both{framed, L.Both{fits,
      L.Both{L.Left{(entry, context, program, L.Both{candidate, oversized})}, {==}}}}}}}

law oversized_invalidation_control_outcome:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -c: S.Configuration
  for -initial: D.State
  for -input: X.Reception
  for -instance: String
  for -before: List<&2, G.Entry>
  for operation: W.Operation
  for -raw: P.Request
  for entry: G.Entry
  for context: D.Context
  for -previous_response: List<&2, U32>
  for -bytes: List<&2, U32>
  for received: W.Received(c, input, W.Extension{operation, raw})
  for invalidating: {operation == W.Invalidate{} : W.Operation}
  for ready: H.InvalidationReady(c, initial, input, instance, before, raw, entry, context)
  for oversized: H.ReceiptTooLarge(c, W.InvalidatedReceipt{})
  for fits: {R.fits(R.limit_response(S.limits(c)),
    S.response_value(S.response_error(S.Limit{}))) == True{} : Bool}
  for framed: P.Message(S.response_value(S.response_error(S.Limit{})), bytes)
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, operation, raw, H.ControlResult{initial, before, H.Error{S.Limit{}}},
    previous_response, previous_response, bytes)
def oversized_invalidation_control_outcome(a, artifacts, native, world, time, c, initial,
  input, instance, before, operation, raw, entry, context, previous_response, bytes,
  received, invalidating, ready, oversized, fits, framed):
  L.Both{received,
    L.Both{{==}, L.Both{{==}, L.Both{framed, L.Both{fits,
      L.Both{L.Right{(entry, context,
        L.Both{invalidating, L.Both{ready, oversized}})}, {==}}}}}}}

# Failed current authentication needs no handle lookup, proof-field premise,
# certificate rejection, or artifact-integrity claim.
law authentication_error_control_outcome:
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -c: S.Configuration
  for -initial: D.State
  for -input: X.Reception
  for -instance: String
  for -before: List<&2, G.Entry>
  for operation: W.Operation
  for -raw: P.Request
  for -previous_response: List<&2, U32>
  for -bytes: List<&2, U32>
  for received: W.Received(c, input, W.Extension{operation, raw})
  for authentication: {D.authenticate(initial, I.credential(raw)) == None{} : Maybe<&2, D.Context>}
  for fits: {R.fits(R.limit_response(S.limits(c)),
    S.response_value(S.response_error(S.Authentication{}))) == True{} : Bool}
  for framed: P.Message(S.response_value(S.response_error(S.Authentication{})), bytes)
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time, instance,
    before, operation, raw, H.ControlResult{initial, before, H.Error{S.Authentication{}}},
    previous_response, previous_response, bytes)
def authentication_error_control_outcome(a, artifacts, native, world, time, c, initial,
  input, instance, before, operation, raw, previous_response, bytes,
  received, authentication, fits, framed):
  L.Both{received,
    L.Both{{==}, L.Both{{==}, L.Both{framed, L.Both{fits,
      L.Both{authentication, {==}}}}}}}
