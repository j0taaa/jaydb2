# Consequences of the actual certificate for the src/Core.bend machine.
# Receives neither Contract, Law1..Law8 nor administrative laws as axioms.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ./Foundations.bend as F
import ./Authentication.bend as A

law certificate_covers_execution_authenticated:
  for c: S.Configuration
  for -code: String
  for p: S.Program
  for +ctx: D.Context
  for +args: D.Value
  for certificate: R.Certifies(c, code, p, ctx, args)
  for +s: D.State
  for valid: R.Valid(c, s)
  for cred: String
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  for +n: Nat
  R.SafetyTrace(N.traverse(n, N.start(p, ctx, args, s), S.schema(c)),
    c, s, ctx, code, args)
def certificate_covers_execution_authenticated(c, code, p, ctx, args, certificate,
  s, valid, cred, aut, n):
  match c:
    case S.Configuration{+e, laws, lim, amb}:
      F.combined_pair(
        R.SafetyTrace(N.traverse(n, N.start(p, ctx, args, s), e),
          S.Configuration{e, laws, lim, amb}, s, ctx, code, args),
        {R.structure(S.Configuration{e, laws, lim, amb}, s) == True{} : Bool},
        S.Satisfies(S.Configuration{e, laws, lim, amb}, S.Stable{s}), valid,
        +structure => stable =>
          %Equal.sym(S.Trace, N.traverse(n, N.start(p, ctx, args, s), e),
            S.execute(n, p, e, s, ctx, args),
            N.fidelity_of_all_os_prefixes(n, p, ctx, args, e, s)) :
              R.SafetyTrace(_, S.Configuration{e, laws, lim, amb}, s, ctx, code, args)
          certificate(s, L.Both{structure, stable},
            A.authentication_implies_context_present(e, s, cred, ctx,
              F.and_boolean_left(D.structure(e, s),
                R.fits(R.limit_state(lim), D.state_value(s)), structure), aut), n))

law certificate_covers_execution_trace_obtained:
  for c: S.Configuration
  for -code: String
  for p: S.Program
  for +ctx: D.Context
  for +args: D.Value
  for certificate: R.Certifies(c, code, p, ctx, args)
  for +s: D.State
  for valid: R.Valid(c, s)
  for cred: String
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  for +n: Nat
  for -execution_trace: S.Trace
  for obtained: {N.traverse(n, N.start(p, ctx, args, s), S.schema(c)) == execution_trace : S.Trace}
  R.SafetyTrace(execution_trace, c, s, ctx, code, args)
def certificate_covers_execution_trace_obtained(c, code, p, ctx, args, certificate,
  s, valid, cred, aut, n, execution_trace, obtained):
  %obtained : R.SafetyTrace(_, c, s, ctx, code, args)
  certificate_covers_execution_authenticated(c, code, p, ctx, args, certificate,
    s, valid, cred, aut, n)

def safety_prefix(execution_trace: S.Trace, -c: S.Configuration, -s: D.State,
  -ctx: D.Context, -code: String, -args: D.Value,
  safe: R.SafetyTrace(execution_trace, c, s, ctx, code, args)) ->
  R.SafetyPrefix(c, s, ctx, code, args,
    S.state_execution_trace(execution_trace), S.events_execution_trace(execution_trace)):
  match execution_trace:
    case S.Prefix{w, ts}:
      safe
    case S.Final{w, ts, proposal}:
      L.and_left(R.SafetyPrefix(c, s, ctx, code, args, w, ts),
        R.SafetyFinal(c, s, ctx, code, args, w, ts, R.finalize(proposal, c, w)), safe)

type Interruption is Data:
  ByFailure{}

def response_interruption(i: Interruption) -> S.Response:
  match i:
    case ByFailure{}:
      S.response_error(S.Failure{})

def laws_of_interruption(i: Interruption, -c: S.Configuration, -s: D.State,
  -ctx: D.Context, -code: String, -args: D.Value, -w: D.State,
  -ts: List<&2, S.OperationEvent>, safe: R.SafetyPrefix(c, s, ctx, code, args, w, ts)) ->
  S.Satisfies(c, S.Closed{s, ctx, code, args, w, ts, response_interruption(i)}):
  match i:
    case ByFailure{}:
      L.and_right(S.Satisfies(c, S.Executing{s, ctx, code, args, w, ts}),
        S.Satisfies(c, S.Closed{s, ctx, code, args, w, ts, S.response_error(S.Failure{})}), safe)

law interruption_negative_publish:
  for i: Interruption
  for -s: D.State
  for -w: D.State
  {S.publish(response_interruption(i), s, w) == s : D.State}
def interruption_negative_publish(i, s, w):
  match i:
    case ByFailure{}:
      {==}

law interruption_certified_preserves_all_as_laws:
  for i: Interruption
  for c: S.Configuration
  for -code: String
  for p: S.Program
  for +ctx: D.Context
  for +args: D.Value
  for certificate: R.Certifies(c, code, p, ctx, args)
  for +s: D.State
  for valid: R.Valid(c, s)
  for cred: String
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  for +n: Nat
  for +execution_trace: S.Trace
  for obtained: {N.traverse(n, N.start(p, ctx, args, s), S.schema(c)) == execution_trace : S.Trace}
  S.Satisfies(c, S.Closed{s, ctx, code, args,
    S.state_execution_trace(execution_trace), S.events_execution_trace(execution_trace), response_interruption(i)})
def interruption_certified_preserves_all_as_laws(i, c, code, p, ctx, args,
  certificate, s, valid, cred, aut, n, execution_trace, obtained):
  laws_of_interruption(i, c, s, ctx, code, args, S.state_execution_trace(execution_trace),
    S.events_execution_trace(execution_trace), safety_prefix(execution_trace, c, s, ctx, code, args,
      certificate_covers_execution_trace_obtained(c, code, p, ctx, args, certificate,
        s, valid, cred, aut, n, execution_trace, obtained)))

def safety_final(-c: S.Configuration, -s: D.State, -ctx: D.Context,
  -code: String, -args: D.Value, -w: D.State, -ts: List<&2, S.OperationEvent>,
  -proposal: S.Response,
  safe: R.SafetyTrace(S.Final{w, ts, proposal}, c, s, ctx, code, args)) ->
  R.SafetyFinal(c, s, ctx, code, args, w, ts, R.finalize(proposal, c, w)):
  L.and_right(R.SafetyPrefix(c, s, ctx, code, args, w, ts),
    R.SafetyFinal(c, s, ctx, code, args, w, ts, R.finalize(proposal, c, w)), safe)

law final_certificate_preserves_all_as_laws:
  for c: S.Configuration
  for -code: String
  for p: S.Program
  for +ctx: D.Context
  for +args: D.Value
  for certificate: R.Certifies(c, code, p, ctx, args)
  for +s: D.State
  for valid: R.Valid(c, s)
  for cred: String
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  for +n: Nat
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -proposal: S.Response
  for obtained: {N.traverse(n, N.start(p, ctx, args, s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}
  R.SafetyFinal(c, s, ctx, code, args, w, ts, R.finalize(proposal, c, w))
def final_certificate_preserves_all_as_laws(c, code, p, ctx, args, certificate,
  s, valid, cred, aut, n, w, ts, proposal, obtained):
  safety_final(c, s, ctx, code, args, w, ts, proposal,
    certificate_covers_execution_trace_obtained(c, code, p, ctx, args, certificate,
      s, valid, cred, aut, n, S.Final{w, ts, proposal}, obtained))

law conclusion_certified_preserves_validity:
  for response: S.Response
  for c: S.Configuration
  for -code: String
  for p: S.Program
  for +ctx: D.Context
  for +args: D.Value
  for certificate: R.Certifies(c, code, p, ctx, args)
  for +s: D.State
  for valid: R.Valid(c, s)
  for cred: String
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  for +n: Nat
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -proposal: S.Response
  for obtained: {N.traverse(n, N.start(p, ctx, args, s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}
  for finalized: {R.finalize(proposal, c, w) == response : S.Response}
  R.Valid(c, S.publish(response, s, w))
def conclusion_certified_preserves_validity(response, c, code, p, ctx, args,
  certificate, s, valid, cred, aut, n, w, ts, proposal, obtained, finalized):
  match response:
    case S.Response{S.Success{}, v}:
      L.and_right(S.Satisfies(c, S.Closed{s, ctx, code, args, w, ts, S.Response{S.Success{}, v}}),
        R.Valid(c, w),
        (%finalized : R.SafetyFinal(c, s, ctx, code, args, w, ts, _)
          final_certificate_preserves_all_as_laws(c, code, p, ctx, args, certificate,
            s, valid, cred, aut, n, w, ts, proposal, obtained)))
    case S.Response{S.Refusal{}, v}:
      valid
    case S.Response{S.Input{}, v}:
      valid
    case S.Response{S.Authentication{}, v}:
      valid
    case S.Response{S.Certificate{}, v}:
      valid
    case S.Response{S.DataError{}, v}:
      valid
    case S.Response{S.Limit{}, v}:
      valid
    case S.Response{S.Failure{}, v}:
      valid
