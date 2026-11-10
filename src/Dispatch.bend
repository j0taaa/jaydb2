# Checked public envelope dispatch before the external admission/tool boundary.
# Private success tags: 1 direct, 3 prepare, 4 execute, 5 invalidate.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ./Input.bend as Input
import ./Messages.bend as Messages
import ./Codec.bend as Codec
import ./Transport.bend as T
import ./Resolve.bend as Resolve

type Routed is Data:
  Routed{tag: U32, input: Input.PreAuthentication}

type Envelope is Data:
  Invalid{}
  Envelope{tag: U32, body: List<&2, U32>}

def opcode(op: U32, body: List<&2, U32>) -> Envelope:
  match op:
    case 0: Envelope{3, body}
    case 1: Envelope{4, body}
    case 2: Envelope{5, body}
    case _: Invalid{}

def envelope(body: List<&2, U32>) -> Envelope:
  match body:
    case Con{7, Con{op, rest}}: opcode(op, rest)
    case Con{7, Nil{}}: Invalid{}
    case other: Envelope{1, other}

def decode_envelope(e: Envelope, state: List<&2, U32>, schema: D.Schema,
  +limits: S.Limits) -> Routed:
  match e:
    case Invalid{}: Routed{0, Input.ErrorMessage{S.Input{}}}
    case Envelope{tag, body}:
      Routed{tag, Input.read_state(B.nat64(R.limit_state(limits)), schema, state, body,
        B.nat64(R.limit_message(limits)))}

def measured(fits: Bool, body: List<&2, U32>, state: List<&2, U32>,
  schema: D.Schema, limits: S.Limits) -> Routed:
  match fits:
    case False{}: Routed{0, Input.ErrorMessage{S.Limit{}}}
    case True{}: decode_envelope(envelope(body), state, schema, limits)

def parts(parts: Maybe<&2, T.Parts>, schema: D.Schema, +limits: S.Limits) -> Routed:
  match parts:
    case None{}: Routed{0, Input.ErrorTransport{}}
    case Some{T.Parts{state, +body}}:
      measured(Nat.is_le(B.length(body), R.limit_message(limits)), body, state, schema, limits)

def decode(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> Routed:
  parts(T.separate(bytes), schema, limits)

def proof_checked(ok: Bool, input: Input.Analysis) -> Input.Analysis:
  match ok:
    case True{}: input
    case False{}: Input.Rejected{S.Input{}}

def validated(+tag: U32, input: Input.Analysis) -> Input.Analysis:
  match input:
    case Input.Received{s, +r, ctx}:
      proof_checked(Bool.not(U32.is_eq(tag, 4) || U32.is_eq(tag, 5)) || String.eq(Resolve.proof(r), ""),
        Input.Received{s, r, ctx})
    case other: other

def retag(tag: U32, bytes: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case Con{1, rest}: Con{tag, rest}
    case other: other

def authenticated(result: Routed) -> List<&2, U32>:
  Routed{+tag, input} = result
  retag(tag, Messages.authentication(validated(tag, Input.authenticate_pre(input))))

def authentication(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> List<&2, U32>:
  authenticated(decode(bytes, schema, limits))

def execution(result: Routed) -> Input.PreAuthentication:
  match result:
    case Routed{4, input}: input
    case Routed{tag, Input.ErrorTransport{}}: Input.ErrorTransport{}
    case Routed{tag, Input.ErrorMessage{status}}: Input.ErrorMessage{status}
    case _: Input.ErrorMessage{S.Input{}}

# Worker variant after the private published root has already been decoded.
def received_envelope(e: Envelope, +s: D.State, limit: Maybe<&2, B.Number64>) -> Routed:
  match e:
    case Invalid{}: Routed{0, Input.ErrorMessage{S.Input{}}}
    case Envelope{tag, body}: Routed{tag, Input.read_message(limit, body, s)}

def received_fits(fits: Bool, body: List<&2, U32>, s: D.State,
  limit: Maybe<&2, B.Number64>) -> Routed:
  match fits:
    case False{}: Routed{0, Input.ErrorMessage{S.Limit{}}}
    case True{}: received_envelope(envelope(body), s, limit)

def received(+limits: S.Limits, +body: List<&2, U32>, s: D.State) -> Routed:
  received_fits(Nat.is_le(B.length(body), R.limit_message(limits)), body, s,
    B.nat64(R.limit_message(limits)))
