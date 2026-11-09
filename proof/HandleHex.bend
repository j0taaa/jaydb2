# Explicit lowercase hexadecimal: independent inverse, fixed width, no format axiom.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ./CodecWordsWord.bend as W
import ./CodecSums64.bend as C64
import ./CodecCounters.bend as Counts
import ./CodecSumsOrder.bend as Order
import ./CodecRelaxArithmeticWord.bend as Measures
import ./Foundations.bend as F

def nibble(w: Word(4n)) -> Char:
  match w:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: '0'
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: '1'
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: '2'
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: '3'
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: '4'
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: '5'
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: '6'
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: '7'
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: '8'
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: '9'
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: 'a'
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: 'b'
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: 'c'
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: 'd'
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: 'e'
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: 'f'

def read_nibble(c: Char) -> Maybe<&2, Word(4n)>:
  match c:
    case '0': Some{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}
    case '1': Some{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}
    case '2': Some{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}
    case '3': Some{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}
    case '4': Some{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}
    case '5': Some{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}
    case '6': Some{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}
    case '7': Some{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}
    case '8': Some{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}
    case '9': Some{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}
    case 'a': Some{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}
    case 'b': Some{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}
    case 'c': Some{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}
    case 'd': Some{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}
    case 'e': Some{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}
    case 'f': Some{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}
    case _: None{}

def is_lower_hex(c: Char) -> Bool:
  match c:
    case '0': True{}
    case '1': True{}
    case '2': True{}
    case '3': True{}
    case '4': True{}
    case '5': True{}
    case '6': True{}
    case '7': True{}
    case '8': True{}
    case '9': True{}
    case 'a': True{}
    case 'b': True{}
    case 'c': True{}
    case 'd': True{}
    case 'e': True{}
    case 'f': True{}
    case _: False{}

law nibble_roundtrip:
  for +w: Word(4n)
  {read_nibble(nibble(w)) == Some{w} : Maybe<&2, Word(4n)>}
def nibble_roundtrip(w):
  match w:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}

law nibble_lowercase:
  for w: Word(4n)
  {is_lower_hex(nibble(w)) == True{} : Bool}
def nibble_lowercase(w):
  match w:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}

law join_split:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  {W.join(k, n, C64.low(k, n, w), C64.high(k, n, w)) == w : Word(Nat.add(k, n))}
def join_split(k, n, w):
  match k:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), v => WCon{b, v},
            W.join(p, n, C64.low(p, n, t), C64.high(p, n, t)), t, join_split(p, n, t))

def encode_byte(+b: Word(8n), tail: String) -> String:
  SCon{nibble(C64.high(4n, 4n, b)), SCon{nibble(C64.low(4n, 4n, b)), tail}}

def encode_bytes(xs: List<&2, Word(8n)>) -> String:
  match xs:
    case Nil{}: SNil{}
    case Con{b, rest}: encode_byte(b, encode_bytes(rest))

def decoded_pair(hi: Maybe<&2, Word(4n)>, lo: Maybe<&2, Word(4n)>, tail: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, List<&2, Word(8n)>>:
  match hi lo tail:
    case Some{h} Some{l} Some{xs}: Some{Con{W.join(4n, 4n, l, h), xs}}
    case _ _ _: None{}

def decode_bytes(s: String) -> Maybe<&2, List<&2, Word(8n)>>:
  match s:
    case SNil{}: Some{Nil{}}
    case SCon{h, SCon{l, rest}}: decoded_pair(read_nibble(h), read_nibble(l), decode_bytes(rest))
    case _: None{}

law bytes_roundtrip:
  for +xs: List<&2, Word(8n)>
  {decode_bytes(encode_bytes(xs)) == Some{xs} : Maybe<&2, List<&2, Word(8n)>>}
def bytes_roundtrip(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      %Equal.sym(Maybe<&2, Word(4n)>, read_nibble(nibble(C64.high(4n, 4n, h))), Some{C64.high(4n, 4n, h)}, nibble_roundtrip(C64.high(4n, 4n, h))) :
        {decoded_pair(_, read_nibble(nibble(C64.low(4n, 4n, h))), decode_bytes(encode_bytes(rest))) == Some{Con{h, rest}} : Maybe<&2, List<&2, Word(8n)>>}
      %Equal.sym(Maybe<&2, Word(4n)>, read_nibble(nibble(C64.low(4n, 4n, h))), Some{C64.low(4n, 4n, h)}, nibble_roundtrip(C64.low(4n, 4n, h))) :
        {decoded_pair(Some{C64.high(4n, 4n, h)}, _, decode_bytes(encode_bytes(rest))) == Some{Con{h, rest}} : Maybe<&2, List<&2, Word(8n)>>}
      %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, decode_bytes(encode_bytes(rest)), Some{rest}, bytes_roundtrip(rest)) :
        {decoded_pair(Some{C64.high(4n, 4n, h)}, Some{C64.low(4n, 4n, h)}, _) == Some{Con{h, rest}} : Maybe<&2, List<&2, Word(8n)>>}
      Equal.cong(Word(8n), Maybe<&2, List<&2, Word(8n)>>, b => Some{Con{b, rest}},
        W.join(4n, 4n, C64.low(4n, 4n, h), C64.high(4n, 4n, h)), h, join_split(4n, 4n, h))

law bytes_injective:
  for +xs: List<&2, Word(8n)>
  for +ys: List<&2, Word(8n)>
  for same: {encode_bytes(xs) == encode_bytes(ys) : String}
  {xs == ys : List<&2, Word(8n)>}
def bytes_injective(xs, ys, same):
  F.some_injective(List<&2, Word(8n)>, xs, ys,
    Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Some{xs}, decode_bytes(encode_bytes(xs)), Some{ys},
      Equal.sym(Maybe<&2, List<&2, Word(8n)>>, decode_bytes(encode_bytes(xs)), Some{xs}, bytes_roundtrip(xs)),
      Equal.trans(Maybe<&2, List<&2, Word(8n)>>, decode_bytes(encode_bytes(xs)), decode_bytes(encode_bytes(ys)), Some{ys},
        Equal.cong(String, Maybe<&2, List<&2, Word(8n)>>, decode_bytes, encode_bytes(xs), encode_bytes(ys), same), bytes_roundtrip(ys))))

def count(xs: List<&2, Word(8n)>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{b, rest}: 1n+count(rest)

law encoded_length:
  for +xs: List<&2, Word(8n)>
  {String.length(encode_bytes(xs)) == Nat.double(count(xs)) : Nat}
def encoded_length(xs):
  match xs:
    case Nil{}: {==}
    case Con{+b, +rest}:
      Equal.cong(Nat, Nat, n => 2n+n, String.length(encode_bytes(rest)), Nat.double(count(rest)), encoded_length(rest))

def LowerDigit(c: Char) -> Type:
  &w: Word(4n) -> {c == nibble(w) : Char}

def LowerHex(s: String) -> Type:
  match s:
    case SNil{}: Unit
    case SCon{h, rest}: L.E<LowerDigit(h), LowerHex(rest)>

law encoded_lowercase:
  for xs: List<&2, Word(8n)>
  LowerHex(encode_bytes(xs))
def encoded_lowercase(xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+b, rest}:
      L.Both{(C64.high(4n, 4n, b), {==}),
        L.Both{(C64.low(4n, 4n, b), {==}), encoded_lowercase(rest)}}

def append(xs: List<&2, Word(8n)>, ys: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}: ys
    case Con{h, rest}: Con{h, append(rest, ys)}

law append_nil:
  for +xs: List<&2, Word(8n)>
  {append(xs, Nil{}) == xs : List<&2, Word(8n)>}
def append_nil(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, ys => Con{h, ys}, append(rest, Nil{}), rest, append_nil(rest))

law append_associative:
  for +xs: List<&2, Word(8n)>
  for +ys: List<&2, Word(8n)>
  for +zs: List<&2, Word(8n)>
  {append(append(xs, ys), zs) == append(xs, append(ys, zs)) : List<&2, Word(8n)>}
def append_associative(xs, ys, zs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, ls => Con{h, ls},
        append(append(rest, ys), zs), append(rest, append(ys, zs)), append_associative(rest, ys, zs))

law count_append:
  for +xs: List<&2, Word(8n)>
  for +ys: List<&2, Word(8n)>
  {count(append(xs, ys)) == Nat.add(count(xs), count(ys)) : Nat}
def count_append(xs, ys):
  match xs:
    case Nil{}: {==}
    case Con{h, +rest}:
      Equal.cong(Nat, Nat, n => 1n+n, count(append(rest, ys)), Nat.add(count(rest), count(ys)), count_append(rest, ys))

def reverse(xs: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  match xs:
    case Nil{}: Nil{}
    case Con{h, rest}: append(reverse(rest), [h])

law reverse_append:
  for +xs: List<&2, Word(8n)>
  for +ys: List<&2, Word(8n)>
  {reverse(append(xs, ys)) == append(reverse(ys), reverse(xs)) : List<&2, Word(8n)>}
def reverse_append(xs, ys):
  match xs:
    case Nil{}:
      Equal.sym(List<&2, Word(8n)>, append(reverse(ys), Nil{}), reverse(ys), append_nil(reverse(ys)))
    case Con{+h, +rest}:
      Equal.trans(List<&2, Word(8n)>, append(reverse(append(rest, ys)), [h]),
        append(append(reverse(ys), reverse(rest)), [h]), append(reverse(ys), append(reverse(rest), [h])),
        Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, ls => append(ls, [h]),
          reverse(append(rest, ys)), append(reverse(ys), reverse(rest)), reverse_append(rest, ys)),
        append_associative(reverse(ys), reverse(rest), [h]))

law reverse_inverse:
  for +xs: List<&2, Word(8n)>
  {reverse(reverse(xs)) == xs : List<&2, Word(8n)>}
def reverse_inverse(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      Equal.trans(List<&2, Word(8n)>, reverse(append(reverse(rest), [h])), Con{h, reverse(reverse(rest))}, Con{h, rest},
        reverse_append(reverse(rest), [h]),
        Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, ls => Con{h, ls}, reverse(reverse(rest)), rest, reverse_inverse(rest)))

law add_one_right:
  for +n: Nat
  {Nat.add(n, 1n) == 1n+n : Nat}
def add_one_right(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n), 1n+p, add_one_right(p))

law count_reverse:
  for +xs: List<&2, Word(8n)>
  {count(reverse(xs)) == count(xs) : Nat}
def count_reverse(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      Equal.trans(Nat, count(append(reverse(rest), [h])), Nat.add(count(reverse(rest)), 1n), 1n+count(rest),
        count_append(reverse(rest), [h]),
        Equal.trans(Nat, Nat.add(count(reverse(rest)), 1n), 1n+count(reverse(rest)), 1n+count(rest),
          add_one_right(count(reverse(rest))),
          Equal.cong(Nat, Nat, n => 1n+n, count(reverse(rest)), count(rest), count_reverse(rest))))

def byte_width(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: 8n+byte_width(p)

# Word is least-significant-bit first; these chunks are least-significant-byte first.
def split_bytes(n: Nat, +w: Word(byte_width(n))) -> List<&2, Word(8n)>:
  match n:
    case 0n: Nil{}
    case 1n+p:
      Con{C64.low(8n, byte_width(p), w), split_bytes(p, C64.high(8n, byte_width(p), w))}

def joined_byte(-n: Nat, h: Word(8n), rest: Maybe<&2, Word(byte_width(n))>) -> Maybe<&2, Word(byte_width(1n+n))>:
  match rest:
    case None{}: None{}
    case Some{w}: Some{W.join(8n, byte_width(n), h, w)}

def join_bytes(n: Nat, xs: List<&2, Word(8n)>) -> Maybe<&2, Word(byte_width(n))>:
  match n xs:
    case 0n Nil{}: Some{WNil{}}
    case 1n+p Con{h, rest}: joined_byte(p, h, join_bytes(p, rest))
    case _ _: None{}

law split_roundtrip:
  for +n: Nat
  for +w: Word(byte_width(n))
  {join_bytes(n, split_bytes(n, w)) == Some{w} : Maybe<&2, Word(byte_width(n))>}
def split_roundtrip(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      %Equal.sym(Maybe<&2, Word(byte_width(p))>, join_bytes(p, split_bytes(p, C64.high(8n, byte_width(p), w))), Some{C64.high(8n, byte_width(p), w)}, split_roundtrip(p, C64.high(8n, byte_width(p), w))) :
        {joined_byte(p, C64.low(8n, byte_width(p), w), _) == Some{w} : Maybe<&2, Word(byte_width(1n+p))>}
      Equal.cong(Word(byte_width(1n+p)), Maybe<&2, Word(byte_width(1n+p))>, v => Some{v},
        W.join(8n, byte_width(p), C64.low(8n, byte_width(p), w), C64.high(8n, byte_width(p), w)), w,
        join_split(8n, byte_width(p), w))

law count_split:
  for +n: Nat
  for w: Word(byte_width(n))
  {count(split_bytes(n, w)) == n : Nat}
def count_split(n, w):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, count(split_bytes(p, C64.high(8n, byte_width(p), w))), p,
        count_split(p, C64.high(8n, byte_width(p), w)))

def padding(n: Nat, s: String) -> String:
  match n:
    case 0n: s
    case 1n+p: SCon{'0', padding(p, s)}

def strip_padding(n: Nat, s: String) -> Maybe<&2, String>:
  match n s:
    case 0n _: Some{s}
    case 1n+p SCon{'0', rest}: strip_padding(p, rest)
    case _ _: None{}

law padding_roundtrip:
  for +n: Nat
  for +s: String
  {strip_padding(n, padding(n, s)) == Some{s} : Maybe<&2, String>}
def padding_roundtrip(n, s):
  match n:
    case 0n: {==}
    case 1n+p: padding_roundtrip(p, s)

law padding_length:
  for +n: Nat
  for +s: String
  {String.length(padding(n, s)) == Nat.add(n, String.length(s)) : Nat}
def padding_length(n, s):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, String.length(padding(p, s)), Nat.add(p, String.length(s)), padding_length(p, s))

law padding_lowercase:
  for +n: Nat
  for +s: String
  for lower: LowerHex(s)
  LowerHex(padding(n, s))
def padding_lowercase(n, s, lower):
  match n:
    case 0n: lower
    case 1n+p: L.Both{(Word.zero(4n), {==}), padding_lowercase(p, s, lower)}

def handle_word(w: Word(64n)) -> String:
  padding(48n, encode_bytes(reverse(split_bytes(8n, w))))

def decoded_chunks(xs: Maybe<&2, List<&2, Word(8n)>>) -> Maybe<&2, Word(64n)>:
  match xs:
    case None{}: None{}
    case Some{bytes}: join_bytes(8n, reverse(bytes))

def decoded_suffix(s: Maybe<&2, String>) -> Maybe<&2, Word(64n)>:
  match s:
    case None{}: None{}
    case Some{suffix}: decoded_chunks(decode_bytes(suffix))

def decode_handle(s: String) -> Maybe<&2, Word(64n)>:
  decoded_suffix(strip_padding(48n, s))

law handle_roundtrip:
  for +w: Word(64n)
  {decode_handle(handle_word(w)) == Some{w} : Maybe<&2, Word(64n)>}
def handle_roundtrip(w):
  %Equal.sym(Maybe<&2, String>, strip_padding(48n, padding(48n, encode_bytes(reverse(split_bytes(8n, w))))), Some{encode_bytes(reverse(split_bytes(8n, w)))}, padding_roundtrip(48n, encode_bytes(reverse(split_bytes(8n, w))))) :
    {decoded_suffix(_) == Some{w} : Maybe<&2, Word(64n)>}
  %Equal.sym(Maybe<&2, List<&2, Word(8n)>>, decode_bytes(encode_bytes(reverse(split_bytes(8n, w)))), Some{reverse(split_bytes(8n, w))}, bytes_roundtrip(reverse(split_bytes(8n, w)))) :
    {decoded_chunks(_) == Some{w} : Maybe<&2, Word(64n)>}
  %Equal.sym(List<&2, Word(8n)>, reverse(reverse(split_bytes(8n, w))), split_bytes(8n, w), reverse_inverse(split_bytes(8n, w))) :
    {join_bytes(8n, _) == Some{w} : Maybe<&2, Word(64n)>}
  split_roundtrip(8n, w)

law handle_word_injective:
  for +a: Word(64n)
  for +b: Word(64n)
  for same: {handle_word(a) == handle_word(b) : String}
  {a == b : Word(64n)}
def handle_word_injective(a, b, same):
  F.some_injective(Word(64n), a, b,
    Equal.trans(Maybe<&2, Word(64n)>, Some{a}, decode_handle(handle_word(a)), Some{b},
      Equal.sym(Maybe<&2, Word(64n)>, decode_handle(handle_word(a)), Some{a}, handle_roundtrip(a)),
      Equal.trans(Maybe<&2, Word(64n)>, decode_handle(handle_word(a)), decode_handle(handle_word(b)), Some{b},
        Equal.cong(String, Maybe<&2, Word(64n)>, decode_handle, handle_word(a), handle_word(b), same), handle_roundtrip(b))))

law handle_word_length:
  for +w: Word(64n)
  {String.length(handle_word(w)) == 64n : Nat}
def handle_word_length(w):
  Equal.trans(Nat, String.length(padding(48n, encode_bytes(reverse(split_bytes(8n, w))))),
    Nat.add(48n, String.length(encode_bytes(reverse(split_bytes(8n, w))))), 64n,
    padding_length(48n, encode_bytes(reverse(split_bytes(8n, w)))),
    Equal.trans(Nat, Nat.add(48n, String.length(encode_bytes(reverse(split_bytes(8n, w))))),
      Nat.add(48n, Nat.double(count(reverse(split_bytes(8n, w))))), 64n,
      Equal.cong(Nat, Nat, n => Nat.add(48n, n), String.length(encode_bytes(reverse(split_bytes(8n, w)))),
        Nat.double(count(reverse(split_bytes(8n, w)))), encoded_length(reverse(split_bytes(8n, w)))),
      Equal.cong(Nat, Nat, n => Nat.add(48n, Nat.double(n)), count(reverse(split_bytes(8n, w))), 8n,
        Equal.trans(Nat, count(reverse(split_bytes(8n, w))), count(split_bytes(8n, w)), 8n,
          count_reverse(split_bytes(8n, w)), count_split(8n, w)))))

law handle_word_lowercase:
  for +w: Word(64n)
  LowerHex(handle_word(w))
def handle_word_lowercase(w):
  padding_lowercase(48n, encode_bytes(reverse(split_bytes(8n, w))), encoded_lowercase(reverse(split_bytes(8n, w))))

def number_key(q: B.Number64) -> String:
  handle_word(C64.bits(q))

def optional_key(q: Maybe<&2, B.Number64>) -> String:
  match q:
    case None{}: ""
    case Some{w}: number_key(w)

def counter_key(n: Nat) -> String:
  optional_key(B.nat64(n))

def nat_from_word(q: Maybe<&2, Word(64n)>) -> Maybe<&2, Nat>:
  match q:
    case None{}: None{}
    case Some{w}: Some{Word.to_nat(64n, w)}

def decode_natural(s: String) -> Maybe<&2, Nat>:
  nat_from_word(decode_handle(s))

def NatDecoded(n: Nat, result: Maybe<&2, Nat>) -> Type:
  match result:
    case None{}: Unit
    case Some{k}: {k == n : Nat}

def natural_of_number(+n: Nat, +q: B.Number64,
  measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}) -> {Word.to_nat(64n, C64.bits(q)) == n : Nat}:
  Counts.nat64_and_injective_in_results_representable(Word.to_nat(64n, C64.bits(q)), n, q,
    Measures.nat64_measures_number(q), measured)

def decoded_counter_case(+n: Nat, result: Maybe<&2, B.Number64>,
  measured: {B.nat64(n) == result : Maybe<&2, B.Number64>}) -> NatDecoded(n, decode_natural(optional_key(result))):
  match result:
    case None{}: Unit{}
    case Some{+q}:
      %Equal.sym(Maybe<&2, Word(64n)>, decode_handle(handle_word(C64.bits(q))), Some{C64.bits(q)}, handle_roundtrip(C64.bits(q))) : NatDecoded(n, nat_from_word(_))
      natural_of_number(n, q, measured)

# Total partial inverse: overflowing Nat inputs map to the invalid empty key;
# every successfully decoded key identifies the ORIGINAL Nat, without wrap.
law decoded_counter_is_original:
  for +n: Nat
  NatDecoded(n, decode_natural(counter_key(n)))
def decoded_counter_is_original(n):
  decoded_counter_case(n, B.nat64(n), {==})

def natural_present(x: Maybe<&2, Nat>) -> Bool:
  match x:
    case None{}: False{}
    case Some{n}: True{}

def number_present(x: Maybe<&2, B.Number64>) -> Bool:
  match x:
    case None{}: False{}
    case Some{n}: True{}

law decoder_presence:
  for +x: Maybe<&2, B.Number64>
  {natural_present(decode_natural(optional_key(x))) == number_present(x) : Bool}
def decoder_presence(x):
  match x:
    case None{}: {==}
    case Some{+q}:
      %Equal.sym(Maybe<&2, Word(64n)>, decode_handle(handle_word(C64.bits(q))), Some{C64.bits(q)}, handle_roundtrip(C64.bits(q))) : {natural_present(nat_from_word(_)) == True{} : Bool}
      {==}

def represented_presence(+x: Maybe<&2, B.Number64>, represented: Order.NumberRepresented<x>) -> {number_present(x) == True{} : Bool}:
  match represented:
    case Order.Represented{q, measured}:
      Equal.cong(Maybe<&2, B.Number64>, Bool, number_present, x, Some{q}, measured)

def inverse_injective(+n: Nat, +m: Nat, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>,
  left_present: {natural_present(a) == True{} : Bool},
  left_correct: NatDecoded(n, a), right_correct: NatDecoded(m, b),
  same: {a == b : Maybe<&2, Nat>}) -> {n == m : Nat}:
  match a b:
    case None{} _:
      F.absurd_boolean({n == m : Nat}, left_present)
    case Some{+x} None{}:
      L.ex_false({n == m : Nat}, F.none_negative_some(Nat, x, Equal.sym(Maybe<&2, Nat>, Some{x}, None{}, same)))
    case Some{+x} Some{+y}:
      Equal.trans(Nat, n, x, m, Equal.sym(Nat, x, n, left_correct),
        Equal.trans(Nat, x, y, m, F.some_injective(Nat, x, y, same), right_correct))

# One represented bound suffices. Distinct inputs cannot collide even if the
# other input was not already known representable, because empty is rejected.
law counter_key_injective_bounded:
  for +limit: Nat
  for +maximum: B.Number64
  for +n: Nat
  for +m: Nat
  for measured: {B.nat64(limit) == Some{maximum} : Maybe<&2, B.Number64>}
  for n_limit: {Nat.is_le(n, limit) == True{} : Bool}
  for same: {counter_key(n) == counter_key(m) : String}
  {n == m : Nat}
def counter_key_injective_bounded(limit, maximum, n, m, measured, n_limit, same):
  presence = represented_presence(B.nat64(n), Order.nat64_representability_closed_for_low(n, limit, maximum, measured, n_limit))
  left_present = Equal.trans(Bool, natural_present(decode_natural(counter_key(n))), number_present(B.nat64(n)), True{}, decoder_presence(B.nat64(n)), presence)
  inverse_injective(n, m, decode_natural(counter_key(n)), decode_natural(counter_key(m)),
    left_present, decoded_counter_is_original(n), decoded_counter_is_original(m),
    Equal.cong(String, Maybe<&2, Nat>, decode_natural, counter_key(n), counter_key(m), same))

def ValidHandle(s: String) -> Type:
  L.E<{String.length(s) == 64n : Nat}, LowerHex(s)>

def represented_key_valid(+x: Maybe<&2, B.Number64>, represented: Order.NumberRepresented<x>) -> ValidHandle(optional_key(x)):
  match x:
    case None{}:
      match represented:
        case Order.Represented{q, impossible}:
          L.ex_false(ValidHandle(""), F.none_negative_some(B.Number64, q, impossible))
    case Some{+q}:
      L.Both{handle_word_length(C64.bits(q)), handle_word_lowercase(C64.bits(q))}

law counter_key_valid_bounded:
  for +limit: Nat
  for +maximum: B.Number64
  for +n: Nat
  for measured: {B.nat64(limit) == Some{maximum} : Maybe<&2, B.Number64>}
  for n_limit: {Nat.is_le(n, limit) == True{} : Bool}
  ValidHandle(counter_key(n))
def counter_key_valid_bounded(limit, maximum, n, measured, n_limit):
  represented_key_valid(B.nat64(n), Order.nat64_representability_closed_for_low(n, limit, maximum, measured, n_limit))

# A concrete two-word bound supplies its own exact Nat representation proof.
# A search can reuse the Data maximum freely, without copying proof values.
def represented_limit(maximum: B.Number64) -> Nat:
  Word.to_nat(64n, C64.bits(maximum))

law counter_key_injective_word_bound:
  for +maximum: B.Number64
  for +n: Nat
  for +m: Nat
  for n_limit: {Nat.is_le(n, represented_limit(maximum)) == True{} : Bool}
  for same: {counter_key(n) == counter_key(m) : String}
  {n == m : Nat}
def counter_key_injective_word_bound(maximum, n, m, n_limit, same):
  counter_key_injective_bounded(represented_limit(maximum), maximum, n, m,
    Measures.nat64_measures_number(maximum), n_limit, same)

law counter_key_valid_word_bound:
  for +maximum: B.Number64
  for +n: Nat
  for n_limit: {Nat.is_le(n, represented_limit(maximum)) == True{} : Bool}
  ValidHandle(counter_key(n))
def counter_key_valid_word_bound(maximum, n, n_limit):
  counter_key_valid_bounded(represented_limit(maximum), maximum, n,
    Measures.nat64_measures_number(maximum), n_limit)

def char_code(c: Char) -> U32:
  Chr{code} = c
  code

law nibble_digit_contract:
  for w: Word(4n)
  {H.hex_digit(char_code(nibble(w))) == True{} : Bool}
def nibble_digit_contract(w):
  match w:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}

law lowercase_digit_contract:
  for +c: Char
  for lower: LowerDigit(c)
  {H.hex_digit(char_code(c)) == True{} : Bool}
def lowercase_digit_contract(c, lower):
  (word, same) = lower
  %Equal.sym(Char, c, nibble(word), same) : {H.hex_digit(char_code(_)) == True{} : Bool}
  nibble_digit_contract(word)

law lowercase_text_contract:
  for +s: String
  for lower: LowerHex(s)
  {H.hex_text(s) == True{} : Bool}
def lowercase_text_contract(s, lower):
  match s:
    case SNil{}: {==}
    case SCon{Chr{+code}, +rest}:
      L.Both{digit, tail} = lower
      F.and_boolean_intro(H.hex_digit(code), H.hex_text(rest),
        lowercase_digit_contract(Chr{code}, digit), lowercase_text_contract(rest, tail))

def handle_contract(+s: String, valid: ValidHandle(s)) -> H.HandleValid(s):
  match valid:
    case L.Both{length, lower}:
      L.Both{length, lowercase_text_contract(s, lower)}

law counter_key_contract_bounded:
  for +limit: Nat
  for +maximum: B.Number64
  for +n: Nat
  for measured: {B.nat64(limit) == Some{maximum} : Maybe<&2, B.Number64>}
  for n_limit: {Nat.is_le(n, limit) == True{} : Bool}
  H.HandleValid(counter_key(n))
def counter_key_contract_bounded(limit, maximum, n, measured, n_limit):
  handle_contract(counter_key(n), counter_key_valid_bounded(limit, maximum, n, measured, n_limit))

law counter_key_contract_word_bound:
  for +maximum: B.Number64
  for +n: Nat
  for n_limit: {Nat.is_le(n, represented_limit(maximum)) == True{} : Bool}
  H.HandleValid(counter_key(n))
def counter_key_contract_word_bound(maximum, n, n_limit):
  handle_contract(counter_key(n), counter_key_valid_word_bound(maximum, n, n_limit))

law bytes32_contract:
  for +xs: List<&2, Word(8n)>
  for fixed: {count(xs) == 32n : Nat}
  H.HandleValid(encode_bytes(xs))
def bytes32_contract(xs, fixed):
  L.Both{Equal.trans(Nat, String.length(encode_bytes(xs)), Nat.double(count(xs)), 64n,
      encoded_length(xs), Equal.cong(Nat, Nat, Nat.double, count(xs), 32n, fixed)),
    lowercase_text_contract(encode_bytes(xs), encoded_lowercase(xs))}

def entropy_word(w: Word(256n)) -> String:
  encode_bytes(reverse(split_bytes(32n, w)))

law entropy_word_contract:
  for +w: Word(256n)
  H.HandleValid(entropy_word(w))
def entropy_word_contract(w):
  bytes32_contract(reverse(split_bytes(32n, w)),
    Equal.trans(Nat, count(reverse(split_bytes(32n, w))), count(split_bytes(32n, w)), 32n,
      count_reverse(split_bytes(32n, w)), count_split(32n, w)))

# Exact native counter bytes: 24 zero bytes followed by u64 big-endian bytes.
def zero_bytes(n: Nat) -> List<&2, Word(8n)>:
  match n:
    case 0n: Nil{}
    case 1n+p: Con{Word.zero(8n), zero_bytes(p)}

def counter_bytes(w: Word(64n)) -> List<&2, Word(8n)>:
  append(zero_bytes(24n), reverse(split_bytes(8n, w)))

law zero_byte_prefix_encoding:
  for +n: Nat
  for +xs: List<&2, Word(8n)>
  {encode_bytes(append(zero_bytes(n), xs)) == padding(Nat.double(n), encode_bytes(xs)) : String}
def zero_byte_prefix_encoding(n, xs):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(String, String, s => SCon{'0', SCon{'0', s}},
        encode_bytes(append(zero_bytes(p), xs)), padding(Nat.double(p), encode_bytes(xs)), zero_byte_prefix_encoding(p, xs))

law counter_bytes_encoding:
  for +w: Word(64n)
  {encode_bytes(counter_bytes(w)) == handle_word(w) : String}
def counter_bytes_encoding(w):
  zero_byte_prefix_encoding(24n, reverse(split_bytes(8n, w)))

law count_zero_bytes:
  for +n: Nat
  {count(zero_bytes(n)) == n : Nat}
def count_zero_bytes(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, count(zero_bytes(p)), p, count_zero_bytes(p))

law counter_bytes_count:
  for +w: Word(64n)
  {count(counter_bytes(w)) == 32n : Nat}
def counter_bytes_count(w):
  Equal.trans(Nat, count(append(zero_bytes(24n), reverse(split_bytes(8n, w)))),
    Nat.add(count(zero_bytes(24n)), count(reverse(split_bytes(8n, w)))), 32n,
    count_append(zero_bytes(24n), reverse(split_bytes(8n, w))),
    Equal.trans(Nat, Nat.add(count(zero_bytes(24n)), count(reverse(split_bytes(8n, w)))),
      Nat.add(24n, count(reverse(split_bytes(8n, w)))), 32n,
      Equal.cong(Nat, Nat, n => Nat.add(n, count(reverse(split_bytes(8n, w)))), count(zero_bytes(24n)), 24n, count_zero_bytes(24n)),
      Equal.cong(Nat, Nat, n => Nat.add(24n, n), count(reverse(split_bytes(8n, w))), 8n,
        Equal.trans(Nat, count(reverse(split_bytes(8n, w))), count(split_bytes(8n, w)), 8n,
          count_reverse(split_bytes(8n, w)), count_split(8n, w)))))

law counter_bytes_contract:
  for +w: Word(64n)
  H.HandleValid(encode_bytes(counter_bytes(w)))
def counter_bytes_contract(w):
  bytes32_contract(counter_bytes(w), counter_bytes_count(w))
