# Boundary between the mathematical contract and a concrete native artifact.
#
# `Environment` is fixed by the project (Bend, compiler, verifier and host).
# It is neither supplied by the client nor chosen by the implementer to make
# a proof pass. Its fields denote semantics, not trust flags.
# `observes` describes ALL real facts of artifact execution; it is not
# a log that the artifact itself may return or omit.
# Every program inspection/effect outside admitted events MUST be
# mapped to InspectionNotModeled/EffectNotModeled. A boundary that
# hides these facts is not an instance of this contract.
# Implementing/proving this correspondence is part of the declared technical boundary.
# `native`/`k` identifies the COMPLETE artifact interpreted by this environment,
# with its pinned dependencies. A name/hash without this binding is insufficient.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Protocol.bend as P
import ./Resources.bend as X
import ./Logic.bend as L

# world distinguishes executions and host choices; it is a semantic index,
# not a new identifier or resource in the database interface.
type Scenario is Type:
  Initialize{world: Nat, configuration: S.Configuration, state: D.State, proof: String}
  Serve{world: Nat, configuration: S.Configuration, state: D.State, input: X.Reception}

def configuration(x: Scenario) -> S.Configuration:
  match x:
    case Initialize{world, c, s, pi}:
      c
    case Serve{world, c, s, input}:
      c

def initial(x: Scenario) -> D.State:
  match x:
    case Initialize{world, c, s, pi}:
      s
    case Serve{world, c, s, input}:
      s

def credential(r: P.Request) -> String:
  P.Request{cred, cod, arg, pi} = r
  cred

def code(r: P.Request) -> String:
  P.Request{cred, cod, arg, pi} = r
  cod

def arguments(r: P.Request) -> D.Value:
  P.Request{cred, cod, arg, pi} = r
  arg

def proof(r: P.Request) -> String:
  P.Request{cred, cod, arg, pi} = r
  pi

type Fact is Type:
  ConfigurationInUse{configuration: S.Configuration}
  InspectionNotModeled{description: String}
  EffectNotModeled{description: String}
  InstanceStarted{state: D.State}
  InitializationRefused{status: S.Status}
  ProofInitialAccepts{}
  Encoded{value: D.Value, result: Maybe<&2, List<&2, U32>>}
  Decoded{bytes: List<&2, U32>, result: Maybe<&2, D.Value>}
  Stored{state: D.State, representation: List<&2, U32>, abstraction: D.State}
  # Logical operation OF THE PROGRAM. Internal authentication or
  # validation reads that do not deliver data to the program are not this event.
  Operated{schema: D.Schema, state: D.State, operation: D.Operation, result: D.ResultOp}
  CheckedLength{position: Nat, count: Nat}
  AllocatedField{position: Nat, count: Nat, memory_later: Nat}
  ReadBody{read_before: Nat, count: Nat, declared: Nat}
  ReceivedRequest{request: P.Request}
  Authenticated{request: P.Request, context: Maybe<&2, D.Context>}
  CertificateAccepted{request: P.Request, context: D.Context, program: S.Program}
  CertificateRejected{request: P.Request, context: D.Context}
  ProgramStarted{request: P.Request, context: D.Context, program: S.Program}
  Evaluated{request: P.Request, context: D.Context, program: S.Program, execution_trace: S.Trace}
  Prepared{response: S.Response, bytes: List<&2, U32>}
  Published{state: D.State}
  StateVisible{state: D.State}
  Measured{measurement: X.Measurement}
  FailedEnvironment{stage: X.Stage, identifier: String, fatal: Bool}
  Concluded{response: S.Response, state: D.State, closes_channel: Bool}
  DeliveredEverything{bytes: List<&2, U32>}
  DeliveryInterrupted{prefix: List<&2, U32>}
  ClosedChannel{}
  NextCall{final_previous: D.State, initial_next: D.State}

type Environment is Type:
  Environment{identity: String,
    elaborates: S.Configuration -> String -> S.Program -> Type,
    derives: S.Configuration -> String -> Type -> Type,
    observes: String -> Scenario -> Nat -> Fact -> Type,
    processable: Scenario -> Type,
    measurement_real: String -> Scenario -> Nat -> X.Measurement -> Type,
    failure_real: String -> Scenario -> Nat -> X.Stage -> String -> Bool -> Type,
    failure_delivery_real: String -> Scenario -> Nat -> Type}

# Complete identity of the environment configuration. This is not a proof
# based merely on equality of client-supplied hashes.
def identity(a: Environment) -> String:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  id

# Elaborates includes syntax/types, dependency closure, exact origin
# of source and executed code, purity, absence of @unsafe/foreign/IO,
# and absence of native-state captures in Action continuations.
def Elaborates(a: Environment, c: S.Configuration, source: String, p: S.Program) -> Type:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  el(c, source, p)

# Derives is the derivation relation of the FIXED logical system, not "the verifier
# answered yes". The environment instance must define it independently
# of the candidate implementation. Client axioms cannot extend it.
def Derives(a: Environment, c: S.Configuration, text: String, target: Type) -> Type:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  de(c, text, target)

def Happens(a: Environment, native: String, x: Scenario, t: Nat, f: Fact) -> Type:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  ob(native, x, t, f)

# Processable is the external contract condition: an operational environment,
# sufficient resources for this input and absence of actual failure.
# It does not receive the candidate artifact: the condition cannot become false
# because it refused, delayed or looped. Its interpretation is fixed
# externally; it cannot become an arbitrary veto inside JayDB.
def Processable(a: Environment, x: Scenario) -> Type:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  pr(x)

def MeasurementReal(a: Environment, native: String, x: Scenario, t: Nat, m: X.Measurement) -> Type:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  mr(native, x, t, m)

def FailureReal(a: Environment, native: String, x: Scenario, t: Nat,
  stage: X.Stage, id: String, fatal: Bool) -> Type:
  Environment{ident, el, de, ob, pr, mr, fr, er} = a
  fr(native, x, t, stage, id, fatal)

def FailureDeliveryReal(a: Environment, native: String, x: Scenario, t: Nat) -> Type:
  Environment{id, el, de, ob, pr, mr, fr, er} = a
  er(native, x, t)

def Before(-a: Environment, -native: String, -x: Scenario, -t: Nat, -f: Fact) -> Type:
  &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool}, Happens(a, native, x, u, f)>

def InSomeMoment(-a: Environment, -native: String, -x: Scenario, -f: Fact) -> Type:
  &t: Nat -> Happens(a, native, x, t, f)

def ConfigurationValid(-a: Environment, -c: S.Configuration) -> Type:
  L.E<{R.configuration_is_valid(c) == True{} : Bool},
    {S.environment(c) == identity(a) : String}>

def Terminates(-p: S.Program, -e: D.Schema, -s: D.State,
  -ctx: D.Context, -args: D.Value) -> Type:
  &n: Nat -> &w: D.State -> &ts: List<&2, S.OperationEvent> -> &r: S.Response ->
    {S.execute(n, p, e, s, ctx, args) == S.Final{w, ts, r} : S.Trace}

def ProgramTerminates(-c: S.Configuration, -p: S.Program) -> Type:
  @s: D.State -> @ctx: D.Context -> @args: D.Value ->
    Terminates(p, S.schema(c), s, ctx, args)

def Bound(-a: Environment, -c: S.Configuration, -source: String, -p: S.Program) -> Type:
  L.E<Elaborates(a, c, source, p), ProgramTerminates(c, p)>

def CertificateValid(-a: Environment, -c: S.Configuration, -r: P.Request,
  -ctx: D.Context, -p: S.Program) -> Type:
  L.E<Bound(a, c, code(r), p),
    L.E<Derives(a, c, proof(r), R.Certifies(c, code(r), p, ctx, arguments(r))),
      R.Certifies(c, code(r), p, ctx, arguments(r))>>

def RequestReceived(x: Scenario, -r: P.Request) -> Type:
  match x:
    case Initialize{world, c, s, pi}:
      Empty
    case Serve{world, c, s, input}:
      &bs: List<&2, U32> ->
        L.E<{X.decide_reception(c, input) == X.ProcessBody{bs} : X.Disposition},
          P.Encoding(P.request_value(r), bs)>

def DecodingCorrect(bs: List<&2, U32>, result: Maybe<&2, D.Value>) -> Type:
  match result:
    case Some{v}:
      P.Decoding(bs, v)
    case None{}:
      @v: D.Value -> P.Decoding(bs, v) -> Empty

def ExecutionCorrect(-c: S.Configuration, -s: D.State, -r: P.Request,
  -ctx: D.Context, -p: S.Program, -execution_trace: S.Trace) -> Type:
  &n: Nat -> {execution_trace ==
    S.execute(n, p, S.schema(c), s, ctx, arguments(r)) : S.Trace}

def ResponseOfProgram(-a: Environment, -native: String, -x: Scenario,
  -t: Nat, -response: S.Response, -working: D.State) -> Type:
  &r: P.Request -> &ctx: D.Context -> &p: S.Program ->
    &ts: List<&2, S.OperationEvent> -> &proposal: S.Response ->
      L.E<Before(a, native, x, t, Evaluated{r, ctx, p, S.Final{working, ts, proposal}}),
        {R.finalize(proposal, configuration(x), working) == response : S.Response}>

def ErrorFixed(r: S.Response) -> Type:
  match r:
    case S.Response{S.Success{}, v}:
      {D.value_valid(v) == True{} : Bool}
    case S.Response{S.Refusal{}, v}:
      {D.value_valid(v) == True{} : Bool}
    case S.Response{s, v}:
      {v == D.VAbsent{} : D.Value}

def WithoutCertificate(-a: Environment, -c: S.Configuration, -r: P.Request,
  -ctx: D.Context) -> Type:
  @p: S.Program ->
    L.E<Bound(a, c, code(r), p),
      Derives(a, c, proof(r), R.Certifies(c, code(r), p, ctx, arguments(r)))> -> Empty

def InputInvalid(x: Scenario) -> Type:
  match x:
    case Initialize{world, c, s, pi}:
      Empty
    case Serve{world, c, s, input}:
      L.Disjunction<
        L.Disjunction<{X.decide_reception(c, input) == X.RefuseClose{S.Input{}} : X.Disposition},
          {X.decide_reception(c, input) == X.RefuseContinue{S.Input{}} : X.Disposition}>,
        &bs: List<&2, U32> ->
          L.E<{X.decide_reception(c, input) == X.ProcessBody{bs} : X.Disposition},
            @r: P.Request -> P.Encoding(P.request_value(r), bs) -> Empty>>

def LimitInInput(x: Scenario) -> Type:
  match x:
    case Initialize{world, c, s, pi}:
      Empty
    case Serve{world, c, s, input}:
      {X.decide_reception(c, input) == X.RefuseClose{S.Limit{}} : X.Disposition}

# The state/response limit is computed on the final proposal, in finalize.
# A temporarily larger working state alone is not that cause.
def LimitOperational(m: X.Measurement, -c: S.Configuration) -> Type:
  match m:
    case X.Measurement{X.Memory{}, n}:
      X.LimitReached(c, m)
    case X.Measurement{X.Time{stage}, n}:
      X.LimitReached(c, m)
    case _:
      Empty

def ResponseJustified(r: S.Response, -a: Environment, -native: String,
  x: Scenario, -t: Nat) -> Type:
  match r:
    case S.Response{S.Input{}, v}:
      InputInvalid(x)
    case S.Response{S.Authentication{}, v}:
      &req: P.Request ->
        L.E<Before(a, native, x, t, Authenticated{req, None{}}), RequestReceived(x, req)>
    case S.Response{S.Certificate{}, v}:
      &req: P.Request -> &ctx: D.Context ->
        Before(a, native, x, t, CertificateRejected{req, ctx})
    case S.Response{S.Limit{}, v}:
      L.Disjunction<LimitInInput(x),
        L.Disjunction<&m: X.Measurement -> L.E<Before(a, native, x, t, Measured{m}),
          LimitOperational(m, configuration(x))>,
          &w: D.State -> ResponseOfProgram(a, native, x, t, S.Response{S.Limit{}, v}, w)>>
    case S.Response{S.Failure{}, v}:
      &stage: X.Stage -> &id: String -> &fatal: Bool ->
        Before(a, native, x, t, FailedEnvironment{stage, id, fatal})
    case S.Response{s, v}:
      &w: D.State -> ResponseOfProgram(a, native, x, t, S.Response{s, v}, w)

def ClosingDisposition(d: X.Disposition, closes: Bool) -> Type:
  match d:
    case X.RefuseClose{s}:
      {closes == True{} : Bool}
    case X.CloseWithoutResponse{}:
      {closes == True{} : Bool}
    case _:
      {closes == False{} : Bool}

def ClosingCorrect(x: Scenario, closes: Bool) -> Type:
  match x:
    case Initialize{world, c, s, pi}:
      Unit
    case Serve{world, c, s, input}:
      ClosingDisposition(X.decide_reception(c, input), closes)
