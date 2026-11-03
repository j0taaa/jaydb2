# Resolve a prepared handle's public envelope to its frozen source identity.
# The trusted entry supplies code/proof from the admitted registration. This
# function neither looks up handles nor acquires data or execution authority.
import Base
import ../contract/Protocol.bend as P
import ./Input.bend as E

def resolve_request(raw: P.Request, code: String, proof: String) -> P.Request:
  P.Request{credential, handle, arguments, unused_proof} = raw
  P.Request{credential, code, arguments, proof}

def resolve_analysis(input: E.Analysis, code: String, proof: String) -> E.Analysis:
  match input:
    case E.Received{state, raw, context}:
      E.Received{state, resolve_request(raw, code, proof), context}
    case E.Rejected{status}:
      E.Rejected{status}
    case E.TransportInvalid{}:
      E.TransportInvalid{}
