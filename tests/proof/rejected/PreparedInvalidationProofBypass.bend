# Causal negative: skipping the proof-field check would select invalidation for
# a nonempty proof. The deterministic selector rejects exactly that input.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../proof/HostInvalidation.bend as V

law false_omitted_proof_validation_would_still_select_invalidation:
  for -credential: String
  for -handle: String
  for -arguments: D.Value
  for -context: D.Context
  {V.choose_auth(Some{context}, P.Request{credential, handle, arguments, "nonempty"}) == V.Selected{context} : V.Choice}
def false_omitted_proof_validation_would_still_select_invalidation(credential, handle, arguments, context):
  {==}
