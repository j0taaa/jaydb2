# Proofs about exactly the functions used by the production controller.
import Base
import ./Policy.bend as P
import ./Controller.bend as C
import ../contract/Bytes.bend as B
import ../contract/Semantics.bend as S
import ../src/Transport.bend as T
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O
import ../contract/Logic.bend as L

law rejected_preserves_state:
  for +old: P.Bytes
  {P.publish(old,P.HostRejected{}) == P.Publication{old,P.error(S.Failure{})} : P.Publication}
def rejected_preserves_state(old):
  {==}

law no_proposal_state_preserves_state:
  for +old: P.Bytes
  for +response: P.Bytes
  {P.publish(old,P.HostReady{response,None{}}) == P.Publication{old,response} : P.Publication}
def no_proposal_state_preserves_state(old,response):
  {==}

law complete_proposal_publishes_exact_pair:
  for old: P.Bytes
  for +response: P.Bytes
  for +state: P.Bytes
  {P.publish(old,P.HostReady{response,Some{state}}) == P.Publication{state,response} : P.Publication}
def complete_proposal_publishes_exact_pair(old,response,state):
  {==}

law false_response_guard_cannot_prepare:
  for response: P.Bytes
  for state: Maybe<&2,P.Bytes>
  {P.choose(P.Proposal,False{},u => P.HostReady{response,state},u => P.HostRejected{}) == P.HostRejected{} : P.Proposal}
def false_response_guard_cannot_prepare(response,state):
  {==}

law no_split_never_prepares:
  for response: P.Bytes
  for state: Maybe<&2,P.Bytes>
  for limit: B.Number64
  {P.checked_response(None{},response,state,limit) == P.HostRejected{} : P.Proposal}
def no_split_never_prepares(response,state,limit):
  {==}

law truncated_header_is_input:
  {P.header([0,0,0,0,0,0,0],B.Number64{4294967295,4294967295}) == P.Terminal{S.Input{}} : P.Header}
def truncated_header_is_input():
  {==}

law high_word_is_checked_before_body:
  {P.header([0,0,0,1,0,0,0,0],B.Number64{0,4294967295}) == P.Terminal{S.Limit{}} : P.Header}
def high_word_is_checked_before_body():
  {==}

law exact_header_limit_is_accepted:
  {P.header([0,0,0,0,0,0,0,3],B.Number64{0,3}) == P.Body{B.Number64{0,3}} : P.Header}
def exact_header_limit_is_accepted():
  {==}

law changed_limits_refuse_build:
  {C.build_matches([0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,3],
    P.Limits{B.Number64{0,1},B.Number64{0,2},B.Number64{0,4}},3) == False{} : Bool}
def changed_limits_refuse_build():
  {==}

law concrete_preparation_refused:
  {C.build_matches([0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,3],
    P.Limits{B.Number64{0,1},B.Number64{0,2},B.Number64{0,3}},0) == False{} : Bool}
def concrete_preparation_refused():
  {==}

law malformed_publication_marker_rejected:
  for limits: P.Limits
  {P.proposal([2],limits) == P.HostRejected{} : P.Proposal}
def malformed_publication_marker_rejected(limits):
  {==}

def is_ready(p: P.Proposal) -> Bool:
  match p:
    case P.HostRejected{}:
      False{}
    case P.HostReady{response,state}:
      True{}

law ready_guard_was_true:
  for +ok: Bool
  for -next: Unit -> P.Proposal
  for accepted: {is_ready(P.guard(ok,next)) == True{} : Bool}
  {ok == True{} : Bool}
def ready_guard_was_true(ok,next,accepted):
  match ok:
    case False{}:
      F.absurd_boolean({False{} == True{} : Bool},accepted)
    case True{}:
      {==}

law ready_state_within_limit:
  for +state: P.Bytes
  for +response: P.Bytes
  for +m: B.Number64
  for +s: B.Number64
  for +r: B.Number64
  for accepted: {is_ready(P.check_state(Some{T.Parts{state,response}},P.Limits{m,s,r})) == True{} : Bool}
  {P.fits(state,s) == True{} : Bool}
def ready_state_within_limit(state,response,m,s,r,accepted):
  ready_guard_was_true(P.fits(state,s),u => P.checked_response(T.separate(response),response,Some{state},r),accepted)

law ready_response_within_limit_and_without_trailing_bytes:
  for +body: P.Bytes
  for +rest: P.Bytes
  for +response: P.Bytes
  for +state: Maybe<&2,P.Bytes>
  for +limit: B.Number64
  for accepted: {is_ready(P.checked_response(Some{T.Parts{body,rest}},response,state,limit)) == True{} : Bool}
  L.E<{P.equal(rest,Nil{}) == True{} : Bool},{P.fits(body,limit) == True{} : Bool}>
def ready_response_within_limit_and_without_trailing_bytes(body,rest,response,state,limit,accepted):
  F.and_boolean_separate(P.equal(rest,Nil{}),P.fits(body,limit),
    ready_guard_was_true(P.equal(rest,Nil{}) && P.fits(body,limit),u => P.HostReady{response,state},accepted))

# The registry uses this exact byte comparator, including non-UTF8 handles.

law equal_bytes_reflexive:
  for +bytes: P.Bytes
  {P.equal(bytes,bytes) == True{} : Bool}
def equal_bytes_reflexive(bytes):
  match bytes:
    case Nil{}:
      {==}
    case Con{+h,+t}:
      F.and_boolean_intro(U32.is_eq(h,h),P.equal(t,t),
        Equal.cong(Cmp,Bool,c => Cmp.is_eq(c),U32.cmp(h,h),EQ{},O.u32_refl(h)),equal_bytes_reflexive(t))

law registered_head_resolves_exact_artifact_and_source_proof:
  for +key: P.Bytes
  for +artifact: P.Bytes
  for +code: P.Bytes
  for +proof: P.Bytes
  for +rest: List<&2,C.Handle>
  {C.lookup(key,Con{C.Handle{key,artifact,code,proof},rest}) ==
    Some{C.Handle{key,artifact,code,proof}} : Maybe<&2,C.Handle>}
def registered_head_resolves_exact_artifact_and_source_proof(key,artifact,code,proof,rest):
  Equal.cong(Bool,Maybe<&2,C.Handle>,ok => P.choose(Maybe<&2,C.Handle>,ok,
    u => Some{C.Handle{key,artifact,code,proof}},u => C.lookup(key,rest)),
    P.equal(key,key),True{},equal_bytes_reflexive(key))

law invalidation_removes_registered_head:
  for +key: P.Bytes
  for +artifact: P.Bytes
  for +code: P.Bytes
  for +proof: P.Bytes
  for +rest: List<&2,C.Handle>
  {C.remove(key,Con{C.Handle{key,artifact,code,proof},rest}) == rest : List<&2,C.Handle>}
def invalidation_removes_registered_head(key,artifact,code,proof,rest):
  Equal.cong(Bool,List<&2,C.Handle>,ok => P.choose(List<&2,C.Handle>,ok,
    u => rest,u => Con{C.Handle{key,artifact,code,proof},C.remove(key,rest)}),
    P.equal(key,key),True{},equal_bytes_reflexive(key))
