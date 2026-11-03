# Private native-module results for the controller.
# 0 + public response; 1 + private result; 2 = invalid internal transport.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ./Input.bend as E
import ./Generate.bend as G
import ./Transport.bend as T

def prefix(tag: U32, bytes: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match bytes:
    case None{}:
      [2]
    case Some{bs}:
      Con{tag, bs}

def error(status: S.Status) -> List<&2, U32>:
  prefix(0, P.frame(S.response_value(S.response_error(status))))

def framing(result: E.PreAuthentication) -> List<&2, U32>:
  match result:
    case E.InputReady{s, r}:
      [1]
    case E.ErrorMessage{status}:
      error(status)
    case E.ErrorTransport{}:
      [2]

def join(field: List<&2, U32>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match rest:
    case None{}:
      None{}
    case Some{r}:
      T.join(field, r)

def metadata(code: String, proof: String, instance: String,
  links: String) -> List<&2, U32>:
  prefix(1, join(B.utf8(code), join(B.utf8(proof),
    T.join(B.utf8(instance), B.utf8(links)))))

def instance_ready(instance: Maybe<&2, String>, code: String, proof: String,
  links: String) -> List<&2, U32>:
  match instance:
    case None{}:
      [2]
    case Some{source}:
      metadata(code, proof, source, links)

def authentication(result: E.Analysis) -> List<&2, U32>:
  match result:
    case E.Received{state, P.Request{credential, +code, +arguments, +proof}, +context}:
      instance_ready(G.instance(context, arguments), code, proof, G.links(code))
    case E.Rejected{status}:
      error(status)
    case E.TransportInvalid{}:
      [2]
