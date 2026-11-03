# Core order: decode message, authenticate, then admit code.
# State enters only through private transport, never client arguments.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ./Codec.bend as C
import ./Request.bend as Q
import ./State.bend as E
import ./Transport.bend as T

type Analysis is Data:
  Received{state: D.State, request: P.Request, context: D.Context}
  Rejected{status: S.Status}
  TransportInvalid{}

def identity(ctx: Maybe<&2, D.Context>, state: D.State,
  request: P.Request) -> Analysis:
  match ctx:
    case None{}:
      Rejected{S.Authentication{}}
    case Some{c}:
      Received{state, request, c}

def authenticate(request: Maybe<&2, P.Request>, +state: D.State) -> Analysis:
  match request:
    case None{}:
      Rejected{S.Input{}}
    case Some{P.Request{+credential, code, arguments, proof}}:
      identity(D.authenticate(state, credential), state,
        P.Request{credential, code, arguments, proof})

type PreAuthentication is Data:
  InputReady{state: D.State, request: P.Request}
  ErrorMessage{status: S.Status}
  ErrorTransport{}

def envelope(request: Maybe<&2, P.Request>, state: D.State) -> PreAuthentication:
  match request:
    case None{}:
      ErrorMessage{S.Input{}}
    case Some{r}:
      InputReady{state, r}

def message(result: C.Outcome, state: D.State) -> PreAuthentication:
  match result:
    case C.Decoded{v}:
      envelope(Q.extract(v), state)
    case _:
      ErrorMessage{S.Input{}}

# S.Limit depends on the ACTUAL quantity received, never an internal length
# declared by the client. After this check, codec Limit means a malformed
# body and message classifies it as Input.
def message_fits(fits: Bool, bytes: List<&2, U32>, limit: B.Number64,
  state: D.State) -> PreAuthentication:
  match fits:
    case False{}:
      ErrorMessage{S.Limit{}}
    case True{}:
      message(C.decode(bytes, limit), state)

def message_measure(measure: Maybe<&2, B.Number64>, bytes: List<&2, U32>,
  +limit: B.Number64, state: D.State) -> PreAuthentication:
  match measure:
    case None{}:
      ErrorMessage{S.Limit{}}
    case Some{body}:
      message_fits(C.less_equal64(body, limit), bytes, limit, state)

def read_message(limit: Maybe<&2, B.Number64>, +bytes: List<&2, U32>,
  state: D.State) -> PreAuthentication:
  match limit:
    case None{}:
      ErrorTransport{}
    case Some{n}:
      message_measure(B.nat64(B.length(bytes)), bytes, n, state)

def state_read(state: Maybe<&2, D.State>, body: List<&2, U32>,
  limit: Maybe<&2, B.Number64>) -> PreAuthentication:
  match state:
    case None{}:
      ErrorTransport{}
    case Some{s}:
      read_message(limit, body, s)

def state_decoded(result: C.Outcome, schema: D.Schema,
  body: List<&2, U32>, limit: Maybe<&2, B.Number64>) -> PreAuthentication:
  match result:
    case C.Decoded{v}:
      state_read(E.decode(v, schema), body, limit)
    case _:
      ErrorTransport{}

def read_state(limit_state: Maybe<&2, B.Number64>, schema: D.Schema,
  state: List<&2, U32>, body: List<&2, U32>, limit_msg: Maybe<&2, B.Number64>) -> PreAuthentication:
  match limit_state:
    case None{}:
      ErrorTransport{}
    case Some{n}:
      state_decoded(C.decode(state, n), schema, body, limit_msg)

def parts(parts: Maybe<&2, T.Parts>, schema: D.Schema, +limits: S.Limits) -> PreAuthentication:
  match parts:
    case None{}:
      ErrorTransport{}
    case Some{T.Parts{state, body}}:
      read_state(B.nat64(R.limit_state(limits)), schema, state, body,
        B.nat64(R.limit_message(limits)))

def decode(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> PreAuthentication:
  parts(T.separate(bytes), schema, limits)

def authenticate_pre(input: PreAuthentication) -> Analysis:
  match input:
    case InputReady{state, request}:
      authenticate(Some{request}, state)
    case ErrorMessage{status}:
      Rejected{status}
    case ErrorTransport{}:
      TransportInvalid{}

def analyze(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> Analysis:
  authenticate_pre(decode(bytes, schema, limits))
