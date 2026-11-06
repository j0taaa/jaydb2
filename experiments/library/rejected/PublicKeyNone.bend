# Deliberately refuse every key: the public roundtrip must reject this decoder.
import Base
import ../../../library/Key.bend as K

def bad_decode(s: String) -> Maybe<&2, List<&2, String>>:
  None{}

law bad_decode_roundtrip:
  for +parts: List<&2, String>
  {bad_decode(K.encode(parts)) == Some{parts} : Maybe<&2, List<&2, String>>}
def bad_decode_roundtrip(parts):
  K.decode_encode(parts)
