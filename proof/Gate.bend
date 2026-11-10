import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../src/Gate.bend as K
import ../src/Core.bend as N

law authentication_precedes_admission:
  for -c: S.Configuration
  for -s: D.State
  for -r: P.Request
  for -admit: K.Oracle()
  for absent: {D.authenticate(s, K.credential(r)) == None{} : Maybe<&2, D.Context>}
  {K.begin(c, s, r, admit) == K.Halted{S.response_error(S.Authentication{})} : K.Entry}
def authentication_precedes_admission(c, s, r, admit, absent):
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, K.credential(r)), None{}, absent) :
    {K.authenticated(c, _, r, s, admit) == K.Halted{S.response_error(S.Authentication{})} : K.Entry}
  {==}

law rejected:
  for -ctx: D.Context
  for -args: D.Value
  for -s: D.State
  {K.admitted(K.Reject{}, ctx, args, s) == K.Halted{S.response_error(S.Certificate{})} : K.Entry}
def rejected(ctx, args, s): {==}

law tool_failure:
  for -ctx: D.Context
  for -args: D.Value
  for -s: D.State
  {K.admitted(K.ToolFailure{}, ctx, args, s) == K.Halted{S.response_error(S.Failure{})} : K.Entry}
def tool_failure(ctx, args, s): {==}

law accepted_starts_exactly:
  for -p: S.Program
  for -ctx: D.Context
  for -args: D.Value
  for -s: D.State
  {K.admitted(K.Accept{p}, ctx, args, s) == K.Started{ctx, N.start(p, ctx, args, s)} : K.Entry}
def accepted_starts_exactly(p, ctx, args, s): {==}

law accepted_begin:
  for -c: S.Configuration
  for -s: D.State
  for -r: P.Request
  for -admit: K.Oracle()
  for -ctx: D.Context
  for -p: S.Program
  for authenticated: {D.authenticate(s, K.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
  for accepted: {admit(c, r, ctx) == K.Accept{p} : K.Verdict}
  {K.begin(c, s, r, admit) == K.Started{ctx, N.start(p, ctx, K.arguments(r), s)} : K.Entry}
def accepted_begin(c, s, r, admit, ctx, p, authenticated, accepted):
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, K.credential(r)), Some{ctx}, authenticated) :
    {K.authenticated(c, _, r, s, admit) == K.Started{ctx, N.start(p, ctx, K.arguments(r), s)} : K.Entry}
  %Equal.sym(K.Verdict, admit(c, r, ctx), K.Accept{p}, accepted) :
    {K.admitted(_, ctx, K.arguments(r), s) == K.Started{ctx, N.start(p, ctx, K.arguments(r), s)} : K.Entry}
  {==}
