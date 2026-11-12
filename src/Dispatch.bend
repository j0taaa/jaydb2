# Checked public envelope dispatch before the external admission/tool boundary.
# Private success tags: 1 direct, 3 prepare, 4 execute, 5 invalidate.
import Base
import ./LimitWords.bend as LimitWords
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
import ./State.bend as State

type Routed is Data:
  Routed{tag: U32, input: Input.PreAuthentication}

type Envelope is Data:
  Invalid{}
  Envelope{tag: U32, body: List<&2, U32>}

def opcode_flags(prepare: Bool, execute: Bool, invalidate: Bool, body: List<&2, U32>) -> Envelope:
  match prepare execute invalidate:
    case True{} _ _: Envelope{3, body}
    case False{} True{} _: Envelope{4, body}
    case False{} False{} True{}: Envelope{5, body}
    case False{} False{} False{}: Invalid{}

def opcode(+op: U32, body: List<&2, U32>) -> Envelope:
  opcode_flags(U32.is_eq(op, 0), U32.is_eq(op, 1), U32.is_eq(op, 2), body)

def prefix(extension: Bool, first: U32, rest: List<&2, U32>) -> Envelope:
  match extension rest:
    case True{} Con{op, body}: opcode(op, body)
    case True{} Nil{}: Invalid{}
    case False{} rest: Envelope{1, Con{first, rest}}

def envelope(body: List<&2, U32>) -> Envelope:
  match body:
    case Con{+first, rest}: prefix(U32.is_eq(first, 7), first, rest)
    case Nil{}: Envelope{1, Nil{}}

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
    LimitWords.convert(R.limit_message(limits), Nat.mul(256n, 256n), B.Number64{0, 65536}, LimitWords.common_literal_exact()))

# Decode the private snapshot once, using exactly the worker's root decoder.
def root_value(value: Codec.Outcome, schema: D.Schema) -> Maybe<&2, D.State>:
  match value:
    case Codec.Decoded{v}: State.decode(v, schema)
    case _: None{}

def root_limit(limit: Maybe<&2, B.Number64>, state: List<&2, U32>, schema: D.Schema) -> Maybe<&2, D.State>:
  match limit:
    case None{}: None{}
    case Some{n}: root_value(Codec.decode(state, n), schema)

def read_root(state: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> Maybe<&2, D.State>:
  root_limit(LimitWords.convert(R.limit_state(limits), Nat.mul(256n, 256n), B.Number64{0, 65536}, LimitWords.common_literal_exact()), state, schema)

def rooted(root: Maybe<&2, D.State>, body: List<&2, U32>, limits: S.Limits) -> Routed:
  match root:
    case None{}: Routed{0, Input.ErrorTransport{}}
    case Some{s}: received(limits, body, s)

def parts(parts: Maybe<&2, T.Parts>, schema: D.Schema, +limits: S.Limits) -> Routed:
  match parts:
    case None{}: Routed{0, Input.ErrorTransport{}}
    case Some{T.Parts{state, body}}: rooted(read_root(state, schema, limits), body, limits)

def decode(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> Routed:
  parts(T.separate(bytes), schema, limits)

def authentication(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> List<&2, U32>:
  authenticated(decode(bytes, schema, limits))
