# Publication-path correspondence, including success that leaves the root equal
# to the starting value. Keep is classified by non-success, never state equality.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Theorems.bend as T
import ../contract/Logic.bend as L
import ../src/Core.bend as Core
import ../src/Execution.bend as X
import ../src/Gate.bend as Gate
import ../src/Messages.bend as Messages

# The prepared metadata envelope projects the identical publication decision;
# neither route identity nor principal changes Keep/Commit or its root/bytes.
law prepared_envelope_projects_exact_decision:
  for metadata: Messages.WorkerMetadata
  for bytes: List<&2, U32>
  {Messages.worker_decision(Messages.WorkerResult{metadata, bytes}) == bytes : List<&2, U32>}
def prepared_envelope_projects_exact_decision(metadata, bytes): {==}

def status(r: S.Response) -> S.Status:
  S.Response{status, value} = r
  status

def Exact(decision: X.Decision, -s: D.State, -next: D.State,
  -response: S.Response, -bytes: List<&2, U32>) -> Type:
  match decision:
    case X.Keep{sent}:
      L.E<{S.is_success(status(response)) == False{} : Bool},
        L.E<{next == s : D.State}, {sent == bytes : List<&2, U32>}>>
    case X.Commit{root, sent}:
      L.E<{S.is_success(status(response)) == True{} : Bool},
        L.E<{root == next : D.State}, {sent == bytes : List<&2, U32>}>>

law decision_matches_publication_path:
  for +r: S.Response
  for +s: D.State
  for +w: D.State
  for +bytes: List<&2, U32>
  Exact(X.decision(Core.Conclusion{S.publish(r, s, w), r, bytes}), s, S.publish(r, s, w), r, bytes)
def decision_matches_publication_path(r, s, w, bytes):
  match r:
    case S.Response{S.Success{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.Refusal{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.Input{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.Authentication{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.Certificate{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.DataError{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.Limit{}, v}: L.Both{{==}, L.Both{{==}, {==}}}
    case S.Response{S.Failure{}, v}: L.Both{{==}, L.Both{{==}, {==}}}

# Applies directly to the existential next/response/bytes in Completion.
def completion_decision(+r: S.Response, +s: D.State, +w: D.State,
  +next: D.State, +bytes: List<&2, U32>,
  publication: T.Publication(r, s, w, next)) ->
  Exact(X.decision(Core.Conclusion{next, r, bytes}), s, next, r, bytes):
  %Equal.sym(D.State, next, S.publish(r, s, w), publication) :
    Exact(X.decision(Core.Conclusion{_, r, bytes}), s, _, r, bytes)
  decision_matches_publication_path(r, s, w, bytes)

law early_decision_preserves_root_and_bytes:
  for +s: D.State
  for +response: S.Response
  for +bytes: List<&2, U32>
  for early: {Gate.early(response, s) == Some{Core.Conclusion{s, response, bytes}} : Maybe<&2, Core.Conclusion>}
  {X.result(Gate.early(response, s)) == X.encode_decision(X.decision(Core.Conclusion{s, response, bytes})) : X.Iteration}
def early_decision_preserves_root_and_bytes(s, response, bytes, early):
  Equal.cong(Maybe<&2, Core.Conclusion>, X.Iteration, X.result, Gate.early(response, s), Some{Core.Conclusion{s, response, bytes}}, early)

def is_keep(decision: X.Decision) -> Bool:
  match decision:
    case X.Keep{bytes}: True{}
    case X.Commit{root, bytes}: False{}

law keep_iff_non_success:
  for +r: S.Response
  for next: D.State
  for bytes: List<&2, U32>
  {is_keep(X.decision(Core.Conclusion{next, r, bytes})) == Bool.not(S.is_success(status(r))) : Bool}
def keep_iff_non_success(r, next, bytes):
  match r:
    case S.Response{S.Success{}, v}: {==}
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}

# Consume the contract's Completion witness itself: the finisher's actual
# emitted decision has precisely its existential next root, response and bytes.
def completion_emits_exact_decision(-c: S.Configuration, +s: D.State, +w: D.State,
  +events: List<&2, S.OperationEvent>, +proposal: S.Response,
  completion: T.Completion(c, s, w, events, proposal)) ->
  &next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
    L.E<{X.result(Gate.finish(S.Final{w, events, proposal}, c, s)) ==
        X.encode_decision(X.decision(Core.Conclusion{next, response, bytes})) : X.Iteration},
      Exact(X.decision(Core.Conclusion{next, response, bytes}), s, next, response, bytes)>:
  match completion:
    case (+next, +response, +bytes, L.Both{finished, L.Both{finalized, L.Both{publication, rest}}}):
      (next, response, bytes, L.Both{
        Equal.cong(Maybe<&2, Core.Conclusion>, X.Iteration, X.result, Gate.finish(S.Final{w, events, proposal}, c, s), Some{Core.Conclusion{next, response, bytes}}, finished),
        completion_decision(response, s, w, next, bytes, publication)})
