# Source binding: the actual two-U32 rank is precisely a full-word sign flip.
import Base
import ./Int64WordIntegerOrder.bend as W
import ./Value.bend as V
import ./Int64Proofs.bend as A
import ./ComparisonProofs.bend as Comparison
import ../proof/CodecWordsWord.bend as Words
import ../proof/CodecUTF8Bits.bend as X
import ../proof/Orders.bend as O

law xor_zero_is_identity:
  for +width: Nat
  for +word: Word(width)
  {Word.xor(width,word,Word.zero(width)) == word : Word(width)}
def xor_zero_is_identity(width,word):
  match width:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+p:
      match word:
        case WCon{False{},+tail}: Equal.cong(Word(p),Word(1n+p),t => WCon{False{},t},Word.xor(p,tail,Word.zero(p)),tail,xor_zero_is_identity(p,tail))
        case WCon{True{},+tail}: Equal.cong(Word(p),Word(1n+p),t => WCon{True{},t},Word.xor(p,tail,Word.zero(p)),tail,xor_zero_is_identity(p,tail))

law xor_distributes_over_joined_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +ml: Word(k)
  for +mh: Word(n)
  {Word.xor(Nat.add(k,n),Words.join(k,n,lo,hi),Words.join(k,n,ml,mh)) == Words.join(k,n,Word.xor(k,lo,ml),Word.xor(n,hi,mh)) : Word(Nat.add(k,n))}
def xor_distributes_over_joined_blocks(k,n,lo,hi,ml,mh):
  match k:
    case 0n: {==}
    case 1n+p:
      match lo ml:
        case WCon{+lb,+lt} WCon{+mb,+mt}:
          Equal.cong(Word(Nat.add(p,n)),Word(1n+Nat.add(p,n)),tail => WCon{Bool.xor(lb,mb),tail},Word.xor(Nat.add(p,n),Words.join(p,n,lt,hi),Words.join(p,n,mt,mh)),Words.join(p,n,Word.xor(p,lt,mt),Word.xor(n,hi,mh)),xor_distributes_over_joined_blocks(p,n,lt,hi,mt,mh))

law full_sign_flip_is_high_word_mask:
  for +high: Word(32n)
  for +low: Word(32n)
  {W.flip_sign(64n,Words.join(32n,32n,low,high)) == Words.join(32n,32n,low,Word.xor(32n,high,A.sign_threshold(31n))) : Word(64n)}
def full_sign_flip_is_high_word_mask(high,low):
  Equal.trans(Word(64n),W.flip_sign(64n,Words.join(32n,32n,low,high)),Word.xor(64n,Words.join(32n,32n,low,high),A.sign_threshold(63n)),Words.join(32n,32n,low,Word.xor(32n,high,A.sign_threshold(31n))),W.flip_sign_is_xor_threshold(63n,Words.join(32n,32n,low,high)),
    Equal.trans(Word(64n),Word.xor(64n,Words.join(32n,32n,low,high),A.sign_threshold(63n)),Words.join(32n,32n,Word.xor(32n,low,Word.zero(32n)),Word.xor(32n,high,A.sign_threshold(31n))),Words.join(32n,32n,low,Word.xor(32n,high,A.sign_threshold(31n))),
      xor_distributes_over_joined_blocks(32n,32n,low,high,Word.zero(32n),A.sign_threshold(31n)),
      Equal.cong(Word(32n),Word(64n),lo => Words.join(32n,32n,lo,Word.xor(32n,high,A.sign_threshold(31n))),Word.xor(32n,low,Word.zero(32n)),low,xor_zero_is_identity(32n,low))))

law actual_rank_is_full_flipped_word_comparison:
  for +a: V.Int64
  for +b: V.Int64
  {Comparison.rank_order(a,b) == Word.cmp(64n,W.flip_sign(64n,A.bits(a)),W.flip_sign(64n,A.bits(b))) : Cmp}
def actual_rank_is_full_flipped_word_comparison(a,b):
  match a b:
    case V.Int64{U32{+ah},U32{+al}} V.Int64{U32{+bh},U32{+bl}}:
      Equal.sym(Cmp,Word.cmp(64n,W.flip_sign(64n,Words.join(32n,32n,al,ah)),W.flip_sign(64n,Words.join(32n,32n,bl,bh))),Comparison.rank_order(V.Int64{U32{ah},U32{al}},V.Int64{U32{bh},U32{bl}}),
        Equal.trans(Cmp,Word.cmp(64n,W.flip_sign(64n,Words.join(32n,32n,al,ah)),W.flip_sign(64n,Words.join(32n,32n,bl,bh))),Word.cmp(64n,Words.join(32n,32n,al,Word.xor(32n,ah,A.sign_threshold(31n))),Words.join(32n,32n,bl,Word.xor(32n,bh,A.sign_threshold(31n)))),Comparison.rank_order(V.Int64{U32{ah},U32{al}},V.Int64{U32{bh},U32{bl}}),
          Equal.trans(Cmp,Word.cmp(64n,W.flip_sign(64n,Words.join(32n,32n,al,ah)),W.flip_sign(64n,Words.join(32n,32n,bl,bh))),Word.cmp(64n,Words.join(32n,32n,al,Word.xor(32n,ah,A.sign_threshold(31n))),W.flip_sign(64n,Words.join(32n,32n,bl,bh))),Word.cmp(64n,Words.join(32n,32n,al,Word.xor(32n,ah,A.sign_threshold(31n))),Words.join(32n,32n,bl,Word.xor(32n,bh,A.sign_threshold(31n)))),
            Equal.cong(Word(64n),Cmp,left => Word.cmp(64n,left,W.flip_sign(64n,Words.join(32n,32n,bl,bh))),W.flip_sign(64n,Words.join(32n,32n,al,ah)),Words.join(32n,32n,al,Word.xor(32n,ah,A.sign_threshold(31n))),full_sign_flip_is_high_word_mask(ah,al)),
            Equal.cong(Word(64n),Cmp,right => Word.cmp(64n,Words.join(32n,32n,al,Word.xor(32n,ah,A.sign_threshold(31n))),right),W.flip_sign(64n,Words.join(32n,32n,bl,bh)),Words.join(32n,32n,bl,Word.xor(32n,bh,A.sign_threshold(31n))),full_sign_flip_is_high_word_mask(bh,bl))),
          X.compare_blocks(32n,32n,al,bl,Word.xor(32n,ah,A.sign_threshold(31n)),Word.xor(32n,bh,A.sign_threshold(31n)))))
