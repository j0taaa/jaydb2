# Controller output framing and the prepared worker use the same registry.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/PreparedProtocol.bend as Receipt
import ../src/Control.bend as C
import ../src/ControlBridge.bend as Wire
import ../src/Messages.bend as Messages
import ../src/Codec.bend as Codec
import ../src/Transport.bend as T
import ./ControlTransport.bend as Values
import ./WireTheorems.bend as Theorems
import ./CodecTrace.bend as Trace

# Successful encoding and representable length are required: failed private
# serialization emits [2], never a registry update. The ceiling is exactly the
# one in ControlBridge.decode_registry, also used by Worker.registered_packet.
law registry_bytes_decode:
  for +reg: C.Registry
  for +bytes: List<&2, U32>
  for +body: B.Number64
  for encoded: P.Encoding(Wire.registry(reg), bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {Codec.less_equal64(body, B.Number64{4294967295, 4294967295}) == True{} : Bool}
  {Wire.decode_registry(bytes) == Some{reg} : Maybe<&2, C.Registry>}
def registry_bytes_decode(reg, bytes, body, encoded, measured, fits):
  match bytes:
    case Nil{}:
      decoded = Theorems.codec_roundtrip()(Wire.registry(reg), Nil{}, body,
        B.Number64{4294967295, 4294967295}, encoded, measured, fits)
      L.ex_false({Wire.decode_registry(Nil{}) == Some{reg} : Maybe<&2, C.Registry>},
        Trace.input_negative_decoded(Wire.registry(reg), decoded))
    case Con{+h, +t}:
      decoded = Theorems.codec_roundtrip()(Wire.registry(reg), Con{h, t}, body,
        B.Number64{4294967295, 4294967295}, encoded, measured, fits)
      Equal.trans(Maybe<&2, C.Registry>, Wire.decode_registry(Con{h, t}),
        Wire.read_registry(Wire.registry(reg)), Some{reg},
        Equal.cong(Codec.Outcome, Maybe<&2, C.Registry>, outcome => Wire.decoded_registry(outcome),
          Codec.decode(Con{h, t}, B.Number64{4294967295, 4294967295}),
          Codec.Decoded{Wire.registry(reg)}, decoded), Values.registry_roundtrip(reg))

# Extract the registry block exactly as Rust's two splits of a metadata output.
def registry_block(parts: Maybe<&2, T.Parts>) -> Maybe<&2, C.Registry>:
  match parts:
    case Some{T.Parts{bytes, receipt}}: Wire.decode_registry(bytes)
    case None{}: None{}

def after_handle(parts: Maybe<&2, T.Parts>) -> Maybe<&2, C.Registry>:
  match parts:
    case Some{T.Parts{handle, rest}}: registry_block(T.separate(rest))
    case None{}: None{}

def output_registry(output: List<&2, U32>) -> Maybe<&2, C.Registry>:
  match output:
    case Con{tag, rest}: after_handle(T.separate(rest))
    case Nil{}: None{}

law ready_registry_decodes:
  for tag: U32
  for +handle: List<&2, U32>
  for +reg: C.Registry
  for +receipt: List<&2, U32>
  for +bytes: List<&2, U32>
  for +inner: List<&2, U32>
  for +outer: List<&2, U32>
  for +body: B.Number64
  for +encoded: {P.encode(Wire.registry(reg)) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {Codec.less_equal64(body, B.Number64{4294967295, 4294967295}) == True{} : Bool}
  for +joined_registry: {T.join(bytes, receipt) == Some{inner} : Maybe<&2, List<&2, U32>>}
  for +joined_handle: {T.join(handle, inner) == Some{outer} : Maybe<&2, List<&2, U32>>}
  for handle_octets: {B.octets_all_valid(handle) == True{} : Bool}
  for bytes_octets: {B.octets_all_valid(bytes) == True{} : Bool}
  for receipt_octets: {B.octets_all_valid(receipt) == True{} : Bool}
  for inner_octets: {B.octets_all_valid(inner) == True{} : Bool}
  {output_registry(Wire.ready(tag, handle, reg, receipt)) == Some{reg} : Maybe<&2, C.Registry>}
def ready_registry_decodes(tag, handle, reg, receipt, bytes, inner, outer, body, encoded,
  measured, fits, joined_registry, joined_handle, handle_octets, bytes_octets, receipt_octets, inner_octets):
  %Equal.sym(Maybe<&2, List<&2, U32>>, P.encode(Wire.registry(reg)), Some{bytes}, encoded) :
    {output_registry(Messages.prefix(tag, Messages.join(handle, Wire.join_encoded(_, receipt)))) == Some{reg} : Maybe<&2, C.Registry>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, T.join(bytes, receipt), Some{inner}, joined_registry) :
    {output_registry(Messages.prefix(tag, Messages.join(handle, _))) == Some{reg} : Maybe<&2, C.Registry>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, T.join(handle, inner), Some{outer}, joined_handle) :
    {output_registry(Messages.prefix(tag, _)) == Some{reg} : Maybe<&2, C.Registry>}
  %Equal.sym(Maybe<&2, T.Parts>, T.separate(outer), Some{T.Parts{handle, inner}},
    Theorems.framing_roundtrip()(handle, inner, outer, handle_octets, inner_octets, joined_handle)) :
    {after_handle(_) == Some{reg} : Maybe<&2, C.Registry>}
  %Equal.sym(Maybe<&2, T.Parts>, T.separate(inner), Some{T.Parts{bytes, receipt}},
    Theorems.framing_roundtrip()(bytes, receipt, inner, bytes_octets, receipt_octets, joined_registry)) :
    {registry_block(_) == Some{reg} : Maybe<&2, C.Registry>}
  registry_bytes_decode(reg, bytes, body, encoded, measured, fits)

# Instantiate this for the actual Control.control result's metadata branch;
# reg is its next registry, the same one tracked by ServiceFoldTheorem.
law control_output_registry_decodes:
  for root: D.State
  for last: List<&2, U32>
  for +reg: C.Registry
  for receipt: Receipt.Receipt
  for +reply: List<&2, U32>
  for +change: C.Change
  for +bytes: List<&2, U32>
  for +inner: List<&2, U32>
  for +outer: List<&2, U32>
  for +body: B.Number64
  for encoded: P.Encoding(Wire.registry(reg), bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {Codec.less_equal64(body, B.Number64{4294967295, 4294967295}) == True{} : Bool}
  for joined_registry: {T.join(bytes, reply) == Some{inner} : Maybe<&2, List<&2, U32>>}
  for joined_handle: {T.join(Wire.delta(change), inner) == Some{outer} : Maybe<&2, List<&2, U32>>}
  for handle_octets: {B.octets_all_valid(Wire.delta(change)) == True{} : Bool}
  for bytes_octets: {B.octets_all_valid(bytes) == True{} : Bool}
  for reply_octets: {B.octets_all_valid(reply) == True{} : Bool}
  for inner_octets: {B.octets_all_valid(inner) == True{} : Bool}
  {output_registry(Wire.output(C.ControlResult{root, last, reg, C.ControlMetadata{receipt, reply, change}})) ==
    Some{reg} : Maybe<&2, C.Registry>}
def control_output_registry_decodes(root, last, reg, receipt, reply, change, bytes, inner, outer, body,
  encoded, measured, fits, joined_registry, joined_handle, handle_octets, bytes_octets, reply_octets, inner_octets):
  match change:
    case C.ControlAdd{e}:
      ready_registry_decodes(1, Wire.delta(C.ControlAdd{e}), reg, reply, bytes, inner, outer, body,
        encoded, measured, fits, joined_registry, joined_handle, handle_octets, bytes_octets, reply_octets, inner_octets)
    case C.ControlRemove{i, h}:
      ready_registry_decodes(3, B.utf8(h), reg, reply, bytes, inner, outer, body,
        encoded, measured, fits, joined_registry, joined_handle, handle_octets, bytes_octets, reply_octets, inner_octets)
