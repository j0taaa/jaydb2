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

# Explicit principal from actual fresh authentication; never recover it from
# generated source text. Success: 1 || frame(id UTF-8) || prior metadata.
def principal(context: D.Context) -> String:
  D.Context{id, kind} = context
  id

def metadata(id: String, code: String, proof: String, instance: String,
  links: String) -> List<&2, U32>:
  prefix(1, join(B.utf8(id), join(B.utf8(code), join(B.utf8(proof),
    T.join(B.utf8(instance), B.utf8(links))))))

def instance_ready(instance: Maybe<&2, String>, id: String, code: String, proof: String,
  links: String) -> List<&2, U32>:
  match instance:
    case None{}:
      [2]
    case Some{source}:
      metadata(id, code, proof, source, links)

def authentication(result: E.Analysis) -> List<&2, U32>:
  match result:
    case E.Received{state, P.Request{credential, +code, +arguments, +proof}, +context}:
      instance_ready(G.instance(context, arguments), principal(context), code, proof, G.links(code))
    case E.Rejected{status}:
      error(status)
    case E.TransportInvalid{}:
      [2]

# Projection after Dispatch.validated: failed decoding/authentication and a
# nonempty raw prepared proof have no principal, exactly as at old ingress.
def authenticated_principal(result: E.Analysis) -> Maybe<&2, String>:
  match result:
    case E.Received{state, request, context}: Some{principal(context)}
    case _: None{}

type WorkerMetadata is Data:
  WorkerMetadata{environment: String, route: Maybe<&2, String>, principal: Maybe<&2, String>, artifact_matches: Bool, authentication_ready: Bool}

type WorkerResult is Data:
  WorkerResult{metadata: WorkerMetadata, decision: List<&2, U32>}

def worker_environment(metadata: WorkerMetadata) -> String:
  WorkerMetadata{environment, route, principal, matches, ready} = metadata
  environment

def worker_principal(metadata: WorkerMetadata) -> Maybe<&2, String>:
  WorkerMetadata{environment, route, principal, matches, ready} = metadata
  principal

def worker_route(metadata: WorkerMetadata) -> Maybe<&2, String>:
  WorkerMetadata{environment, route, principal, matches, ready} = metadata
  route

def worker_matches(metadata: WorkerMetadata) -> Bool:
  WorkerMetadata{environment, route, principal, matches, ready} = metadata
  matches

def worker_ready(metadata: WorkerMetadata) -> Bool:
  WorkerMetadata{environment, route, principal, matches, ready} = metadata
  ready

# Preserve the original authenticator's tag-2 metadata-generation/framing
# failures too. This checked projection does not invoke another process.
def authentication_output_ready(bytes: List<&2, U32>) -> Bool:
  match bytes:
    case Con{0, rest}: True{}
    case Con{1, rest}: True{}
    case _: False{}

def authentication_ready(analysis: E.Analysis) -> Bool:
  authentication_output_ready(authentication(analysis))

def worker_metadata(environment: String, route: Maybe<&2, String>, matches: Bool,
  +analysis: E.Analysis) -> WorkerMetadata:
  WorkerMetadata{environment, route, authenticated_principal(analysis), matches, authentication_ready(analysis)}

law metadata_transport_failure_is_not_ready:
  {authentication_output_ready([2]) == False{} : Bool}
def metadata_transport_failure_is_not_ready(): {==}

# A concrete metadata-generation failure, not just a fabricated tag byte.
# Ingress cannot decode this malformed typed list, but the old generator is
# genuinely partial and its failure discriminator must remain authoritative.
law failed_argument_reification_is_not_ready:
  for state: D.State
  for credential: String
  for code: String
  for proof: String
  for context: D.Context
  {authentication_ready(E.Received{state,
    P.Request{credential, code, D.VList{D.VAbsent{}, D.VAbsent{}}, proof}, context}) == False{} : Bool}
def failed_argument_reification_is_not_ready(state, credential, code, proof, context): {==}

def worker_decision(result: WorkerResult) -> List<&2, U32>:
  WorkerResult{metadata, decision} = result
  decision

def optional_joined(joined: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match joined:
    case None{}: None{}
    case Some{bs}: Some{Con{1, bs}}

def optional_text(value: Maybe<&2, String>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match value rest:
    case None{} None{}: None{}
    case None{} Some{bs}: Some{Con{0, bs}}
    case Some{text} rest: optional_joined(join(B.utf8(text), rest))

def match_byte(matches: Bool) -> U32:
  match matches:
    case False{}: 0
    case True{}: 1

# Version/tag 6, framed environment, optional route/principal, match/ready flags,
# then the exact existing Commit/Keep bytes. No public protocol change.
def worker_result(result: WorkerResult) -> List<&2, U32>:
  WorkerResult{WorkerMetadata{environment, route, principal, matches, ready}, decision} = result
  prefix(6, join(B.utf8(environment), optional_text(route, optional_text(principal, Some{Con{match_byte(matches), Con{match_byte(ready), decision}}}))))

law worker_principal_is_authenticated_id:
  for state: D.State
  for request: P.Request
  for id: String
  for kind: String
  {authenticated_principal(E.Received{state, request, D.Context{id, kind}}) == Some{id} : Maybe<&2, String>}
def worker_principal_is_authenticated_id(state, request, id, kind): {==}

law worker_envelope_preserves_exact_decision:
  for metadata: WorkerMetadata
  for +decision: List<&2, U32>
  {worker_decision(WorkerResult{metadata, decision}) == decision : List<&2, U32>}
def worker_envelope_preserves_exact_decision(metadata, decision): {==}

# This projection is the exact authenticated principal, including empty IDs.
law principal_is_authenticated_id:
  for id: String
  for kind: String
  {principal(D.Context{id, kind}) == id : String}
def principal_is_authenticated_id(id, kind):
  {==}

# The same actual fresh context binds both the explicit host principal and
# the generated certificate instance; neither is taken from client source.
law authentication_binds_principal_and_instance:
  for state: D.State
  for credential: String
  for +code: String
  for +proof: String
  for +arguments: D.Value
  for +id: String
  for +kind: String
  {authentication(E.Received{state, P.Request{credential, code, arguments, proof}, D.Context{id, kind}}) ==
    instance_ready(G.instance(D.Context{id, kind}, arguments), id, code, proof, G.links(code)) : List<&2, U32>}
def authentication_binds_principal_and_instance(state, credential, code, proof, arguments, id, kind):
  {==}
