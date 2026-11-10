# Constructive physical-wire lemmas for the optional prepared interface.
# A received extension is tied to its full, actual prefixed reception.
# Resolving its logical source cannot turn that reception into an ordinary one.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../contract/PreparedProtocol.bend as W
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S

# Processing is over the complete physical prefix and body; only the second
# premise describes the canonical inner record. No resolved request is used.
law extension_received_from_physical_prefix:
  for -configuration: S.Configuration
  for -input: X.Reception
  for +operation: W.Operation
  for -request: P.Request
  for +bytes: List<&2, U32>
  for valid: X.ReceptionValid(input)
  for processing: {X.decide_reception(configuration, input) ==
    X.ProcessBody{Con{7, Con{W.opcode(operation), bytes}}} : X.Disposition}
  for encoded: P.Encoding(P.request_value(request), bytes)
  W.Received(configuration, input, W.Extension{operation, request})
def extension_received_from_physical_prefix(configuration, input, operation, request, bytes, valid, processing, encoded):
  L.Both{valid,
    (Con{7, Con{W.opcode(operation), bytes}},
      L.Both{processing, W.extension_body_encoding(operation, request, bytes, encoded)})}

def example_handle() -> String:
  "0000000000000000000000000000000000000000000000000000000000000000"

# Extracting bytes is only a witness constructor. The laws below independently
# prove successful exact encoding, so None cannot masquerade as a valid receipt.
def encoded_body(result: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match result:
    case None{}: Nil{}
    case Some{bytes}: bytes

def receipt_body(receipt: W.Receipt) -> List<&2, U32>:
  encoded_body(W.encode_receipt(receipt))

def ReceiptBodySize(-receipt: W.Receipt, -size: Nat) -> Type:
  &bytes: List<&2, U32> ->
    L.E<P.Encoding(W.receipt_value(receipt), bytes), {B.length(bytes) == size : Nat}>

# Sizes count encoded BODY bytes. The outer u64 length is excluded, exactly as
# required by limit_response; the prepared handle contains 64 ASCII characters.
law prepared_receipt_body_is_128:
  ReceiptBodySize(W.PreparedReceipt{example_handle()}, 128n)
def prepared_receipt_body_is_128():
  (receipt_body(W.PreparedReceipt{example_handle()}), L.Both{{==}, {==}})

law invalidated_receipt_body_is_59:
  ReceiptBodySize(W.InvalidatedReceipt{}, 59n)
def invalidated_receipt_body_is_59():
  (receipt_body(W.InvalidatedReceipt{}), L.Both{{==}, {==}})

law opcode_three_rejected:
  for bytes: List<&2, U32>
  {W.route_dispatch(Con{7, Con{3, bytes}}) == W.InvalidExtension{} : W.Dispatch}
def opcode_three_rejected(bytes):
  {==}

law truncated_opcode_rejected:
  {W.route_dispatch([7]) == W.InvalidExtension{} : W.Dispatch}
def truncated_opcode_rejected():
  W.truncated_opcode_rejected()
