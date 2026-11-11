# Discarding the upper counter word cannot inherit the full-word inverse proof.
import Base
import ../../../proof/HandleHex.bend as H
import ../../../proof/CodecSums64.bend as C64
import ../../../proof/CodecWordsWord.bend as W

def wrong_key(+w: Word(64n)) -> String:
  H.handle_word(W.join(32n, 32n, C64.low(32n, 32n, w), Word.zero(32n)))

law false:
  for +w: Word(64n)
  {H.decode_handle(wrong_key(w)) == Some{w} : Maybe<&2, Word(64n)>}
def false(w):
  H.handle_roundtrip(w)
