import Base
import ./Transport.bend as Transport
import ../contract/Theorems.bend as C
import ./CodecComplete.bend as Complete
import ./CodecAcceptance.bend as Acceptance

def codec_roundtrip() -> C.CodecRoundtrip():
  v => bytes => body => ceiling => encoded => measured => fits =>
    Complete.all_encoding_canonical_representable_and_decoded(v, bytes, body, ceiling, encoded, measured, fits)

def codec_canonical() -> C.CodecCanonical():
  bytes => ceiling => v => decoded =>
    Acceptance.all_acceptance_publish_has_encoding_canonical(bytes, ceiling, v, decoded)


def framing_roundtrip() -> C.FramingRoundtrip():
  first => second => packet => first_valid => second_valid => joined =>
    Transport.separate_inverts_all_assembly_is_valid(first, second, packet, joined, first_valid, second_valid)
