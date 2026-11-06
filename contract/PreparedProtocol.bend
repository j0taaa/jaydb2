# Optional prepared-program wire vocabulary. Ordinary Value/Request/Status
# encoding is unchanged. A prepared body is exactly two additional bytes
# followed by the canonical ordinary four-field request body.
import Base
import ./Bytes.bend as B
import ./Data.bend as D
import ./Logic.bend as L
import ./Protocol.bend as P
import ./Resources.bend as X
import ./Semantics.bend as S

type Operation is Data:
  Prepare{}
  Execute{}
  Invalidate{}
  PrepareRead{}

def opcode(operation: Operation) -> U32:
  match operation:
    case Prepare{}: 0
    case Execute{}: 1
    case Invalidate{}: 2
    case PrepareRead{}: 3

type WireRequest is Data:
  Ordinary{request: P.Request}
  Extension{operation: Operation, request: P.Request}

def raw(wire: WireRequest) -> P.Request:
  match wire:
    case Ordinary{request}: request
    case Extension{operation, request}: request

def prefix_body(operation: Operation, result: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match result:
    case None{}: None{}
    case Some{bytes}: Some{Con{7, Con{opcode(operation), bytes}}}

def encode_body(wire: WireRequest) -> Maybe<&2, List<&2, U32>>:
  match wire:
    case Ordinary{request}: P.encode(P.request_value(request))
    case Extension{operation, request}:
      prefix_body(operation, P.encode(P.request_value(request)))

def BodyEncoding(wire: WireRequest, bytes: List<&2, U32>) -> Type:
  {encode_body(wire) == Some{bytes} : Maybe<&2, List<&2, U32>>}

# frame_result computes u64be(length(FULL body)), including 7 and opcode.
def frame(wire: WireRequest) -> Maybe<&2, List<&2, U32>>:
  P.frame_result(encode_body(wire))

def Encoding(wire: WireRequest, bytes: List<&2, U32>) -> Type:
  {frame(wire) == Some{bytes} : Maybe<&2, List<&2, U32>>}

# This relation retains the valid actual reception and full physical byte limit.
# ReceptionValid binds the declared length to the actual body; ProcessBody
# alone only checks that declaration. No resolved source request replaces it.
def Received(-configuration: S.Configuration, -input: X.Reception, -wire: WireRequest) -> Type:
  L.E<X.ReceptionValid(input),
    &bytes: List<&2, U32> ->
      L.E<{X.decide_reception(configuration, input) == X.ProcessBody{bytes} : X.Disposition},
        BodyEncoding(wire, bytes)>>

# Dispatch only removes the explicit prefix. Canonical decoding and exact
# four-field request validation still apply to the returned body in all cases.
type Dispatch is Data:
  OrdinaryBody{bytes: List<&2, U32>}
  ExtensionBody{operation: Operation, bytes: List<&2, U32>}
  InvalidExtension{}

def dispatch_opcode(zero: Bool, one: Bool, two: Bool, three: Bool, bytes: List<&2, U32>) -> Dispatch:
  match zero one two three:
    case True{} _ _ _: ExtensionBody{Prepare{}, bytes}
    case False{} True{} _ _: ExtensionBody{Execute{}, bytes}
    case False{} False{} True{} _: ExtensionBody{Invalidate{}, bytes}
    case False{} False{} False{} True{}: ExtensionBody{PrepareRead{}, bytes}
    case False{} False{} False{} False{}: InvalidExtension{}

def strip_extension(bytes: List<&2, U32>) -> Dispatch:
  match bytes:
    case Nil{}: InvalidExtension{}
    case Con{+operation, body}:
      dispatch_opcode(U32.is_eq(operation, 0), U32.is_eq(operation, 1),
        U32.is_eq(operation, 2), U32.is_eq(operation, 3), body)

def dispatch_tag(extension: Bool, tag: U32, rest: List<&2, U32>) -> Dispatch:
  match extension:
    case False{}: OrdinaryBody{Con{tag, rest}}
    case True{}: strip_extension(rest)

def route_dispatch(bytes: List<&2, U32>) -> Dispatch:
  match bytes:
    case Nil{}: OrdinaryBody{Nil{}}
    case Con{+tag, rest}: dispatch_tag(U32.is_eq(tag, 7), tag, rest)

# Receipts are control metadata, outside Semantics.Status and Response.
type Receipt is Data:
  PreparedReceipt{handle: String}
  InvalidatedReceipt{}

def receipt_value(receipt: Receipt) -> D.Value:
  match receipt:
    case PreparedReceipt{handle}:
      D.VRecord{"status", D.VText{"prepared"},
        D.VRecord{"value", D.VText{handle}, D.VRecordEmpty{}}}
    case InvalidatedReceipt{}:
      D.VRecord{"status", D.VText{"invalidated"},
        D.VRecord{"value", D.VAbsent{}, D.VRecordEmpty{}}}

def encode_receipt(receipt: Receipt) -> Maybe<&2, List<&2, U32>>:
  P.encode(receipt_value(receipt))

def frame_receipt(receipt: Receipt) -> Maybe<&2, List<&2, U32>>:
  P.frame(receipt_value(receipt))

def ReceiptEncoding(receipt: Receipt, bytes: List<&2, U32>) -> Type:
  P.Message(receipt_value(receipt), bytes)

law ordinary_body_encoding_unchanged:
  for request: P.Request
  {encode_body(Ordinary{request}) == P.encode(P.request_value(request)) : Maybe<&2, List<&2, U32>>}
def ordinary_body_encoding_unchanged(request):
  {==}

law ordinary_frame_encoding_unchanged:
  for request: P.Request
  {frame(Ordinary{request}) == P.frame(P.request_value(request)) : Maybe<&2, List<&2, U32>>}
def ordinary_frame_encoding_unchanged(request):
  {==}

law extension_body_encoding:
  for +operation: Operation
  for -request: P.Request
  for +bytes: List<&2, U32>
  for encoded: P.Encoding(P.request_value(request), bytes)
  BodyEncoding(Extension{operation, request}, Con{7, Con{opcode(operation), bytes}})
def extension_body_encoding(operation, request, bytes, encoded):
  Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>,
    result => prefix_body(operation, result),
    P.encode(P.request_value(request)), Some{bytes}, encoded)

law known_opcode_dispatch:
  for operation: Operation
  for bytes: List<&2, U32>
  {route_dispatch(Con{7, Con{opcode(operation), bytes}}) == ExtensionBody{operation, bytes} : Dispatch}
def known_opcode_dispatch(operation, bytes):
  match operation:
    case Prepare{}: {==}
    case Execute{}: {==}
    case Invalidate{}: {==}
    case PrepareRead{}: {==}

law truncated_opcode_rejected:
  {route_dispatch([7]) == InvalidExtension{} : Dispatch}
def truncated_opcode_rejected():
  {==}

law extension_prefix_counts_two_bytes:
  for operation: Operation
  for bytes: List<&2, U32>
  {B.length(Con{7, Con{opcode(operation), bytes}}) == 2n+B.length(bytes) : Nat}
def extension_prefix_counts_two_bytes(operation, bytes):
  {==}
