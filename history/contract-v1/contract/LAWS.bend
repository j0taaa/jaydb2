# JayDB — THE EIGHT CORE LAWS.
#
# A proposition in Bend is a Type. LawN(a, code_native) is an obligation
# about that artifact, under the fixed environment `a`. Defining these types does NOT
# prove them. The implementation must supply a term of Contract(a,k).
# There is no `assumes`, application axiom, circular proof or implementation here.
import Base
import ./Logic.bend as L
import ./Data.bend as D
import ./Bytes.bend as B
import ./Protocol.bend as P
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Resources.bend as X
import ./Interface.bend as I
import ./Links.bend as V

# ----- Law 1 helpers -----

def StartCorrect(x: I.Scenario, -a: I.Environment, -k: String,
  -t: Nat, -published: D.State) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}:
      L.E<I.ConfigurationValid(a, c),
        L.E<I.Derives(a, c, pi, R.Valid(c, s)),
          L.E<R.Valid(c, s),
            L.E<{published == s : D.State}, I.Before(a, k, x, t, I.ProofInitialAccepts{})>>>>
    case I.Serve{world, c, s, input}:
      Empty

def ProofInitialCorrect(x: I.Scenario, -a: I.Environment) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}:
      L.E<I.ConfigurationValid(a, c),
        L.E<I.Derives(a, c, pi, R.Valid(c, s)), R.Valid(c, s)>>
    case I.Serve{world, c, s, input}:
      Empty

def Rule1(f: I.Fact, -a: I.Environment, -k: String, x: I.Scenario, -t: Nat) -> Type:
  match f:
    case I.InstanceStarted{s}:
      StartCorrect(x, a, k, t, s)
    case I.ProofInitialAccepts{}:
      ProofInitialCorrect(x, a)
    case I.ConfigurationInUse{c}:
      {c == I.configuration(x) : S.Configuration}
    case I.InitializationRefused{status}:
      @u: Nat -> @s: D.State -> I.Happens(a, k, x, u, I.InstanceStarted{s}) -> Empty
    case _:
      Unit

# ----- Law 2 helpers -----

def LengthDeclared(r: X.Reception, -n: Nat) -> Type:
  match r:
    case X.BodyTruncated{high, low, body}:
      {X.declared_equal(high, low, n) == True{} : Bool}
    case X.BodyReceived{high, low, body}:
      {X.declared_equal(high, low, n) == True{} : Bool}
    case _:
      Empty

def ReadBounded(x: I.Scenario, -before: Nat, -count: Nat, -declared: Nat) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}:
      Empty
    case I.Serve{world, c, s, input}:
      L.E<LengthDeclared(input, declared),
        L.E<{Nat.is_le(Nat.add(before, count), declared) == True{} : Bool},
          {Nat.is_le(Nat.add(before, count), R.limit_message(S.limits(c))) == True{} : Bool}>>

def Rule2(f: I.Fact, -a: I.Environment, -k: String, x: I.Scenario, -t: Nat) -> Type:
  match f:
    case I.Encoded{v, r}:
      {r == P.encode(v) : Maybe<&2, List<&2, U32>>}
    case I.Decoded{bs, r}:
      I.DecodingCorrect(bs, r)
    case I.Stored{s, representation, abstraction}:
      {abstraction == s : D.State}
    case I.Operated{e, s, o, r}:
      {r == D.operate(e, s, o) : D.ResultOp}
    case I.ReceivedRequest{r}:
      I.RequestReceived(x, r)
    case I.AllocatedField{pos, n, memory}:
      L.E<I.Before(a, k, x, t, I.CheckedLength{pos, n}),
        {Nat.is_le(memory, X.limit(I.configuration(x), X.Memory{})) == True{} : Bool}>
    case I.ReadBody{before, n, declared}:
      ReadBounded(x, before, n, declared)
    case _:
      Unit

# ----- Law 3 helpers -----

def Rule3(f: I.Fact, -a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  match f:
    case I.Authenticated{r, ctx}:
      L.E<{ctx == D.authenticate(I.initial(x), I.credential(r)) : Maybe<&2, D.Context>},
        I.Before(a, k, x, t, I.ReceivedRequest{r})>
    case I.ProgramStarted{r, ctx, p}:
      L.E<{D.authenticate(I.initial(x), I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
        I.Before(a, k, x, t, I.Authenticated{r, Some{ctx}})>
    case _:
      Unit

# ----- Law 4 helpers -----

def Rule4(f: I.Fact, -a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  match f:
    case I.CertificateAccepted{r, ctx, p}:
      L.E<I.Before(a, k, x, t, I.Authenticated{r, Some{ctx}}),
        I.CertificateValid(a, I.configuration(x), r, ctx, p)>
    case I.CertificateRejected{r, ctx}:
      L.E<I.Before(a, k, x, t, I.Authenticated{r, Some{ctx}}),
        I.WithoutCertificate(a, I.configuration(x), r, ctx)>
    case I.ProgramStarted{r, ctx, p}:
      I.Before(a, k, x, t, I.CertificateAccepted{r, ctx, p})
    case _:
      Unit

# ----- Law 5 helpers -----

def PrefixesInOrder(-a: I.Environment, -k: String, -x: I.Scenario, -t: Nat,
  -r: P.Request, -ctx: D.Context, -p: S.Program, -current: S.Trace) -> Type:
  @u: Nat -> @previous: S.Trace ->
    {Nat.is_lt(u, t) == True{} : Bool} ->
    I.Happens(a, k, x, u, I.Evaluated{r, ctx, p, previous}) ->
    L.Prefix(S.OperationEvent, S.events_execution_trace(previous), S.events_execution_trace(current))

def Rule5(f: I.Fact, -a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  match f:
    case I.Evaluated{r, ctx, p, execution_trace}:
      L.E<L.E<V.WithoutConclusionPrevious(a, k, x, t), V.PrefixesNotTerminated(a, k, x, t)>,
        L.E<I.Before(a, k, x, t, I.ProgramStarted{r, ctx, p}),
          L.E<I.ExecutionCorrect(I.configuration(x), I.initial(x), r, ctx, p, execution_trace),
          PrefixesInOrder(a, k, x, t, r, ctx, p, execution_trace)>>>
    case I.ProgramStarted{r, ctx, p}:
      L.E<L.E<I.ConfigurationValid(a, I.configuration(x)),
          L.E<R.Valid(I.configuration(x), I.initial(x)), V.WithoutConclusionPrevious(a, k, x, t)>>,
        @u: Nat -> @r2: P.Request -> @ctx2: D.Context -> @p2: S.Program ->
        I.Happens(a, k, x, u, I.ProgramStarted{r2, ctx2, p2}) ->
          L.E<{u == t : Nat},
            L.E<{r2 == r : P.Request},
              L.E<{ctx2 == ctx : D.Context}, {p2 == p : S.Program}>>>>
    case I.Operated{e, s, o, result}:
      L.E<V.WithoutConclusionPrevious(a, k, x, t),
        L.E<V.PrefixesNotTerminated(a, k, x, t), V.OperationBound(a, k, x, t, e, s, o, result)>>
    case I.InspectionNotModeled{description}:
      Empty
    case I.EffectNotModeled{description}:
      Empty
    case _:
      Unit

# ----- Law 6 helpers -----

def NonePublication(-a: I.Environment, -k: String, -x: I.Scenario) -> Type:
  @t: Nat -> @s: D.State -> I.Happens(a, k, x, t, I.Published{s}) -> Empty

def NotPublishedBefore(-a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  @s: D.State -> I.Before(a, k, x, t, I.Published{s}) -> Empty

def ConclusionAtomic(r: S.Response, -a: I.Environment, -k: String,
  -x: I.Scenario, -t: Nat, -published: D.State) -> Type:
  match r:
    case S.Response{S.Success{}, v}:
      I.Before(a, k, x, t, I.Published{published})
    case _:
      L.E<{published == I.initial(x) : D.State}, NonePublication(a, k, x)>

def Rule6(f: I.Fact, -a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  match f:
    case I.Published{w}:
      L.E<R.Valid(I.configuration(x), w),
        L.E<&v: D.Value -> &bs: List<&2, U32> ->
          L.E<I.Before(a, k, x, t, I.Prepared{S.Response{S.Success{}, v}, bs}),
            I.ResponseOfProgram(a, k, x, t, S.Response{S.Success{}, v}, w)>,
          @u: Nat -> @w2: D.State -> I.Happens(a, k, x, u, I.Published{w2}) ->
            L.E<{u == t : Nat}, {w2 == w : D.State}>>>
    case I.StateVisible{s}:
      L.Disjunction<L.E<{s == I.initial(x) : D.State}, NotPublishedBefore(a, k, x, t)>,
        I.Before(a, k, x, t, I.Published{s})>
    case I.Concluded{r, s, closes}:
      ConclusionAtomic(r, a, k, x, t, s)
    case I.NextCall{previous, next}:
      L.E<{next == previous : D.State},
        &r: S.Response -> &closes: Bool -> I.Before(a, k, x, t, I.Concluded{r, previous, closes})>
    case _:
      Unit

# ----- Law 7 helpers -----

def FailureFatalPrevious(-a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  &stage: X.Stage -> &id: String -> I.Before(a, k, x, t, I.FailedEnvironment{stage, id, True{}})

def ClosingAllowed(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat, -closes: Bool) -> Type:
  L.Disjunction<I.ClosingCorrect(x, closes),
    L.E<{closes == True{} : Bool}, FailureFatalPrevious(a, k, x, t)>>

def WithoutResponseExpected(x: I.Scenario) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}:
      Empty
    case I.Serve{world, c, s, input}:
      {X.decide_reception(c, input) == X.CloseWithoutResponse{} : X.Disposition}

def DeliveryCompleteUnique(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat, -bs: List<&2, U32>) -> Type:
  L.E<@u: Nat -> @other: List<&2, U32> ->
    I.Happens(a, k, x, u, I.DeliveredEverything{other}) ->
      L.E<{u == t : Nat}, {other == bs : List<&2, U32>}>,
    @u: Nat -> @prefix: List<&2, U32> ->
      I.Happens(a, k, x, u, I.DeliveryInterrupted{prefix}) -> Empty>

def DeliveryInterruptedUnique(-a: I.Environment, -k: String, -x: I.Scenario,
  -t: Nat, -bs: List<&2, U32>) -> Type:
  L.E<@u: Nat -> @other: List<&2, U32> ->
    I.Happens(a, k, x, u, I.DeliveryInterrupted{other}) ->
      L.E<{u == t : Nat}, {other == bs : List<&2, U32>}>,
    @u: Nat -> @complete: List<&2, U32> ->
      I.Happens(a, k, x, u, I.DeliveredEverything{complete}) -> Empty>

def CloseEventually(closes: Bool, -a: I.Environment, -k: String, -x: I.Scenario) -> Type:
  match closes:
    case False{}:
      Unit
    case True{}:
      I.Processable(a, x) -> I.InSomeMoment(a, k, x, I.ClosedChannel{})

def Rule7(f: I.Fact, a: I.Environment, k: String, x: I.Scenario, t: Nat) -> Type:
  match f:
    case I.Prepared{r, bs}:
      L.E<I.ErrorFixed(r),
        L.E<P.Message(S.response_value(r), bs),
          L.E<{R.fits(R.limit_response(S.limits(I.configuration(x))), S.response_value(r)) == True{} : Bool},
            I.ResponseJustified(r, a, k, x, t)>>>
    case I.Concluded{r, s, closes}:
      L.E<&bs: List<&2, U32> -> I.Before(a, k, x, t, I.Prepared{r, bs}),
        L.E<L.E<ClosingAllowed(a, k, x, t, closes), CloseEventually(closes, a, k, x)>,
          @u: Nat -> @r2: S.Response -> @s2: D.State -> @f2: Bool ->
            I.Happens(a, k, x, u, I.Concluded{r2, s2, f2}) ->
              L.E<{u == t : Nat}, L.E<{r2 == r : S.Response}, {s2 == s : D.State}>>>>
    case I.DeliveredEverything{bs}:
      &r: S.Response -> &s: D.State -> &closes: Bool ->
        L.E<I.Before(a, k, x, t, I.Concluded{r, s, closes}),
          L.E<I.Before(a, k, x, t, I.Prepared{r, bs}), DeliveryCompleteUnique(a, k, x, t, bs)>>
    case I.DeliveryInterrupted{prefix}:
      &r: S.Response -> &s: D.State -> &closes: Bool -> &bs: List<&2, U32> ->
        L.E<I.Before(a, k, x, t, I.Concluded{r, s, closes}),
          L.E<I.Before(a, k, x, t, I.Prepared{r, bs}),
            L.E<L.Prefix(U32, prefix, bs),
              L.E<DeliveryInterruptedUnique(a, k, x, t, prefix), I.FailureDeliveryReal(a, k, x, t)>>>>
    case I.Measured{m}:
      I.MeasurementReal(a, k, x, t, m)
    case I.FailedEnvironment{stage, id, fatal}:
      I.FailureReal(a, k, x, t, stage, id, fatal)
    case I.ClosedChannel{}:
      L.Disjunction<WithoutResponseExpected(x),
        L.Disjunction<FailureFatalPrevious(a, k, x, t),
          L.Disjunction<&r: S.Response -> &s: D.State -> I.Before(a, k, x, t, I.Concluded{r, s, True{}}),
            &bs: List<&2, U32> -> I.Before(a, k, x, t, I.DeliveryInterrupted{bs})>>>
    case _:
      Unit

# ----- Law 8 helpers -----

def InitializationPossible(-a: I.Environment, -c: S.Configuration,
  -s: D.State, -pi: String) -> Type:
  L.E<I.ConfigurationValid(a, c),
    L.E<I.Derives(a, c, pi, R.Valid(c, s)), R.Valid(c, s)>>

def ServiceTerminates(-a: I.Environment, -k: String, -x: I.Scenario) -> Type:
  L.Disjunction<L.E<WithoutResponseExpected(x), I.InSomeMoment(a, k, x, I.ClosedChannel{})>,
    &r: S.Response -> &s: D.State -> &closes: Bool ->
      L.E<I.InSomeMoment(a, k, x, I.Concluded{r, s, closes}),
        &bs: List<&2, U32> -> I.InSomeMoment(a, k, x, I.DeliveredEverything{bs})>>

def Progress(x: I.Scenario, -a: I.Environment, -k: String) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}:
      InitializationPossible(a, c, s, pi) ->
        I.Processable(a, x) -> I.InSomeMoment(a, k, x, I.InstanceStarted{s})
    case I.Serve{world, c, s, input}:
      I.ConfigurationValid(a, c) -> R.Valid(c, s) -> X.ReceptionValid(input) ->
        I.Processable(a, x) ->
          L.E<ServiceTerminates(a, k, x),
            @r: P.Request -> @ctx: D.Context -> @p: S.Program ->
              I.RequestReceived(x, r) ->
              {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
              L.E<I.Bound(a, c, I.code(r), p),
                I.Derives(a, c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))> ->
                  L.E<I.InSomeMoment(a, k, x, I.CertificateAccepted{r, ctx, p}),
                    I.InSomeMoment(a, k, x, I.ProgramStarted{r, ctx, p})>>

# 1. Faithful initialization and immutable configuration.
def Law1(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule1(f, a, k, x, t)

# 2. Exact representation, exact operations and limits before access.
def Law2(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule2(f, a, k, x, t)

# 3. Identity derived from the credential and initial published state.
def Law3(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule3(f, a, k, x, t)

# 4. Proof for the actual source, dependencies, context and arguments.
def Law4(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule4(f, a, k, x, t)

# 5. Every real observation corresponds to the certified program.
def Law5(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule5(f, a, k, x, t)

# 6. One complete, valid publication; errors preserve the initial state.
def Law6(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule6(f, a, k, x, t)

# 7. Responses, interruptions, delivery and closure correspond to facts.
def Law7(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule7(f, a, k, x, t)

# 8. Under the specified conditions, initialize, admit and conclude.
def Law8(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> Progress(x, a, k)

def Contract(-a: I.Environment, -k: String) -> Type:
  L.E<Law1(a, k),
    L.E<Law2(a, k),
      L.E<Law3(a, k),
        L.E<Law4(a, k),
          L.E<Law5(a, k),
            L.E<Law6(a, k), L.E<Law7(a, k), Law8(a, k)>>>>>>>
