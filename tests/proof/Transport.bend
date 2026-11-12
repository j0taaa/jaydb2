import Base
import ../../proof/TransportScan.bend as GScan
import ../../contract/Bytes.bend as B
import ../../contract/Logic.bend as L
import ../../src/Transport.bend as T
import ../../proof/Transport.bend as G

law all_packet_assembled_separates_os_same_blocks:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for -bs: List<&2, U32>
  for assembled: {T.join(a, b) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for va: {B.octets_all_valid(a) == True{} : Bool}
  for vb: {B.octets_all_valid(b) == True{} : Bool}
  {T.separate(bs) == Some{T.Parts{a, b}} : Maybe<&2, T.Parts>}
def all_packet_assembled_separates_os_same_blocks(a, b, bs, assembled, va, vb):
  G.separate_inverts_all_assembly_is_valid(a, b, bs, assembled, va, vb)

law all_packet_accepted_can_be_reassembled_without_change_one_octet:
  for +bs: List<&2, U32>
  for +parts: T.Parts
  for accepted: {T.separate(bs) == Some{parts} : Maybe<&2, T.Parts>}
  G.SeparationExact(bs, parts)
def all_packet_accepted_can_be_reassembled_without_change_one_octet(bs, parts, accepted):
  G.all_separation_accepts_reconstructs_packet_original(bs, parts, accepted)

# The optimized transport must refine the previous parser on every list,
# without assuming that the native byte bridge supplied octets.
law fused_transport_equals_previous_on_every_input:
  for +bs: List<&2, U32>
  {T.separate(bs) == T.separate_reference(bs) : Maybe<&2, T.Parts>}
def fused_transport_equals_previous_on_every_input(bs):
  GScan.separate_refines_reference(bs)

law non_octet_in_suffix_is_rejected:
  {T.separate([0,0,0,0,0,0,0,1,7,256]) == None{} : Maybe<&2, T.Parts>}
def non_octet_in_suffix_is_rejected(): {==}

law non_octet_in_prefix_is_rejected:
  {T.separate([0,0,0,0,0,0,0,1,256,7]) == None{} : Maybe<&2, T.Parts>}
def non_octet_in_prefix_is_rejected(): {==}

law prefix_validation_defers_suffix_validation:
  {T.complete(T.separate_prefix([0,0,0,0,0,0,0,1,7,256])) == None{} : Maybe<&2, T.Parts>}
def prefix_validation_defers_suffix_validation(): {==}
