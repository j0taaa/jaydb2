# Checked 65,536-byte u64 literal, with compact Nat indices. Safe expands
# small Nat literals as Peano constructors; keep every literal here <=256.
# Nat.mul(256,256) is the exact guard and compiles as native multiplication.
# All witness arithmetic is checked by the existing u64-addition theorem.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecSums.bend as S

def at_16() -> {B.nat64(16n) == Some{B.Number64{0, 16}} : Maybe<&2, B.Number64>}:
  {==}

def block(+count: Nat, +increment: B.Number64, +n: Nat, +previous: Nat, +q: B.Number64,
  exact_increment: {B.nat64(count) == Some{increment} : Maybe<&2, B.Number64>},
  same: {n == Nat.add(count, previous) : Nat},
  measured: {B.nat64(previous) == Some{q} : Maybe<&2, B.Number64>}) ->
  {B.nat64(n) == C.sum64(increment, q) : Maybe<&2, B.Number64>}:
  %Equal.sym(Nat, n, Nat.add(count, previous), same) :
    {B.nat64(_) == C.sum64(increment, q) : Maybe<&2, B.Number64>}
  Equal.sym(Maybe<&2, B.Number64>, C.sum64(increment, q),
    B.nat64(Nat.add(count, previous)),
    S.sum64_nat64_exact(count, previous, increment, q, exact_increment, measured))

def checked_block(+count: Nat, +increment: B.Number64, +n: Nat, +previous: Nat,
  +q: B.Number64, +result: B.Number64,
  exact_increment: {B.nat64(count) == Some{increment} : Maybe<&2, B.Number64>},
  measured: {B.nat64(previous) == Some{q} : Maybe<&2, B.Number64>},
  same: {n == Nat.add(count, previous) : Nat},
  added: {C.sum64(increment, q) == Some{result} : Maybe<&2, B.Number64>}) ->
  {B.nat64(n) == Some{result} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(n), C.sum64(increment, q), Some{result},
    block(count, increment, n, previous, q, exact_increment, same, measured), added)

def at_32() -> {B.nat64(32n) == Some{B.Number64{0, 32}} : Maybe<&2, B.Number64>}:
  checked_block(16n, B.Number64{0, 16}, 32n, 16n, B.Number64{0, 16}, B.Number64{0, 32}, at_16(), at_16(), {==}, {==})

def at_64() -> {B.nat64(64n) == Some{B.Number64{0, 64}} : Maybe<&2, B.Number64>}:
  checked_block(32n, B.Number64{0, 32}, 64n, 32n, B.Number64{0, 32}, B.Number64{0, 64}, at_32(), at_32(), {==}, {==})

def at_128() -> {B.nat64(128n) == Some{B.Number64{0, 128}} : Maybe<&2, B.Number64>}:
  checked_block(64n, B.Number64{0, 64}, 128n, 64n, B.Number64{0, 64}, B.Number64{0, 128}, at_64(), at_64(), {==}, {==})

def at_256() -> {B.nat64(256n) == Some{B.Number64{0, 256}} : Maybe<&2, B.Number64>}:
  checked_block(128n, B.Number64{0, 128}, 256n, 128n, B.Number64{0, 128}, B.Number64{0, 256}, at_128(), at_128(), {==}, {==})

def measured_equal(+n: Nat, +m: Nat, +q: B.Number64,
  same: {n == m : Nat}, measured: {B.nat64(m) == Some{q} : Maybe<&2, B.Number64>}) ->
  {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}:
  %Equal.sym(Nat, n, m, same) : {B.nat64(_) == Some{q} : Maybe<&2, B.Number64>}
  measured

law multiply_successor:
  for +n: Nat
  for +m: Nat
  {Nat.mul(1n+n, m) == Nat.add(m, Nat.mul(n, m)) : Nat}
def multiply_successor(n, m):
  {==}

def at_multiple_1() -> {B.nat64(Nat.mul(1n, 256n)) == Some{B.Number64{0, 256}} : Maybe<&2, B.Number64>}:
  measured_equal(Nat.mul(1n, 256n), 256n, B.Number64{0, 256}, {==}, at_256())

def at_multiple_2() -> {B.nat64(Nat.mul(2n, 256n)) == Some{B.Number64{0, 512}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(2n, 256n), Nat.mul(1n, 256n), B.Number64{0, 256}, B.Number64{0, 512}, at_256(), at_multiple_1(), multiply_successor(1n, 256n), {==})

def at_multiple_3() -> {B.nat64(Nat.mul(3n, 256n)) == Some{B.Number64{0, 768}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(3n, 256n), Nat.mul(2n, 256n), B.Number64{0, 512}, B.Number64{0, 768}, at_256(), at_multiple_2(), multiply_successor(2n, 256n), {==})

def at_multiple_4() -> {B.nat64(Nat.mul(4n, 256n)) == Some{B.Number64{0, 1024}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(4n, 256n), Nat.mul(3n, 256n), B.Number64{0, 768}, B.Number64{0, 1024}, at_256(), at_multiple_3(), multiply_successor(3n, 256n), {==})

def at_multiple_5() -> {B.nat64(Nat.mul(5n, 256n)) == Some{B.Number64{0, 1280}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(5n, 256n), Nat.mul(4n, 256n), B.Number64{0, 1024}, B.Number64{0, 1280}, at_256(), at_multiple_4(), multiply_successor(4n, 256n), {==})

def at_multiple_6() -> {B.nat64(Nat.mul(6n, 256n)) == Some{B.Number64{0, 1536}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(6n, 256n), Nat.mul(5n, 256n), B.Number64{0, 1280}, B.Number64{0, 1536}, at_256(), at_multiple_5(), multiply_successor(5n, 256n), {==})

def at_multiple_7() -> {B.nat64(Nat.mul(7n, 256n)) == Some{B.Number64{0, 1792}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(7n, 256n), Nat.mul(6n, 256n), B.Number64{0, 1536}, B.Number64{0, 1792}, at_256(), at_multiple_6(), multiply_successor(6n, 256n), {==})

def at_multiple_8() -> {B.nat64(Nat.mul(8n, 256n)) == Some{B.Number64{0, 2048}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(8n, 256n), Nat.mul(7n, 256n), B.Number64{0, 1792}, B.Number64{0, 2048}, at_256(), at_multiple_7(), multiply_successor(7n, 256n), {==})

def at_multiple_9() -> {B.nat64(Nat.mul(9n, 256n)) == Some{B.Number64{0, 2304}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(9n, 256n), Nat.mul(8n, 256n), B.Number64{0, 2048}, B.Number64{0, 2304}, at_256(), at_multiple_8(), multiply_successor(8n, 256n), {==})

def at_multiple_10() -> {B.nat64(Nat.mul(10n, 256n)) == Some{B.Number64{0, 2560}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(10n, 256n), Nat.mul(9n, 256n), B.Number64{0, 2304}, B.Number64{0, 2560}, at_256(), at_multiple_9(), multiply_successor(9n, 256n), {==})

def at_multiple_11() -> {B.nat64(Nat.mul(11n, 256n)) == Some{B.Number64{0, 2816}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(11n, 256n), Nat.mul(10n, 256n), B.Number64{0, 2560}, B.Number64{0, 2816}, at_256(), at_multiple_10(), multiply_successor(10n, 256n), {==})

def at_multiple_12() -> {B.nat64(Nat.mul(12n, 256n)) == Some{B.Number64{0, 3072}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(12n, 256n), Nat.mul(11n, 256n), B.Number64{0, 2816}, B.Number64{0, 3072}, at_256(), at_multiple_11(), multiply_successor(11n, 256n), {==})

def at_multiple_13() -> {B.nat64(Nat.mul(13n, 256n)) == Some{B.Number64{0, 3328}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(13n, 256n), Nat.mul(12n, 256n), B.Number64{0, 3072}, B.Number64{0, 3328}, at_256(), at_multiple_12(), multiply_successor(12n, 256n), {==})

def at_multiple_14() -> {B.nat64(Nat.mul(14n, 256n)) == Some{B.Number64{0, 3584}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(14n, 256n), Nat.mul(13n, 256n), B.Number64{0, 3328}, B.Number64{0, 3584}, at_256(), at_multiple_13(), multiply_successor(13n, 256n), {==})

def at_multiple_15() -> {B.nat64(Nat.mul(15n, 256n)) == Some{B.Number64{0, 3840}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(15n, 256n), Nat.mul(14n, 256n), B.Number64{0, 3584}, B.Number64{0, 3840}, at_256(), at_multiple_14(), multiply_successor(14n, 256n), {==})

def at_multiple_16() -> {B.nat64(Nat.mul(16n, 256n)) == Some{B.Number64{0, 4096}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(16n, 256n), Nat.mul(15n, 256n), B.Number64{0, 3840}, B.Number64{0, 4096}, at_256(), at_multiple_15(), multiply_successor(15n, 256n), {==})

def at_multiple_17() -> {B.nat64(Nat.mul(17n, 256n)) == Some{B.Number64{0, 4352}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(17n, 256n), Nat.mul(16n, 256n), B.Number64{0, 4096}, B.Number64{0, 4352}, at_256(), at_multiple_16(), multiply_successor(16n, 256n), {==})

def at_multiple_18() -> {B.nat64(Nat.mul(18n, 256n)) == Some{B.Number64{0, 4608}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(18n, 256n), Nat.mul(17n, 256n), B.Number64{0, 4352}, B.Number64{0, 4608}, at_256(), at_multiple_17(), multiply_successor(17n, 256n), {==})

def at_multiple_19() -> {B.nat64(Nat.mul(19n, 256n)) == Some{B.Number64{0, 4864}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(19n, 256n), Nat.mul(18n, 256n), B.Number64{0, 4608}, B.Number64{0, 4864}, at_256(), at_multiple_18(), multiply_successor(18n, 256n), {==})

def at_multiple_20() -> {B.nat64(Nat.mul(20n, 256n)) == Some{B.Number64{0, 5120}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(20n, 256n), Nat.mul(19n, 256n), B.Number64{0, 4864}, B.Number64{0, 5120}, at_256(), at_multiple_19(), multiply_successor(19n, 256n), {==})

def at_multiple_21() -> {B.nat64(Nat.mul(21n, 256n)) == Some{B.Number64{0, 5376}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(21n, 256n), Nat.mul(20n, 256n), B.Number64{0, 5120}, B.Number64{0, 5376}, at_256(), at_multiple_20(), multiply_successor(20n, 256n), {==})

def at_multiple_22() -> {B.nat64(Nat.mul(22n, 256n)) == Some{B.Number64{0, 5632}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(22n, 256n), Nat.mul(21n, 256n), B.Number64{0, 5376}, B.Number64{0, 5632}, at_256(), at_multiple_21(), multiply_successor(21n, 256n), {==})

def at_multiple_23() -> {B.nat64(Nat.mul(23n, 256n)) == Some{B.Number64{0, 5888}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(23n, 256n), Nat.mul(22n, 256n), B.Number64{0, 5632}, B.Number64{0, 5888}, at_256(), at_multiple_22(), multiply_successor(22n, 256n), {==})

def at_multiple_24() -> {B.nat64(Nat.mul(24n, 256n)) == Some{B.Number64{0, 6144}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(24n, 256n), Nat.mul(23n, 256n), B.Number64{0, 5888}, B.Number64{0, 6144}, at_256(), at_multiple_23(), multiply_successor(23n, 256n), {==})

def at_multiple_25() -> {B.nat64(Nat.mul(25n, 256n)) == Some{B.Number64{0, 6400}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(25n, 256n), Nat.mul(24n, 256n), B.Number64{0, 6144}, B.Number64{0, 6400}, at_256(), at_multiple_24(), multiply_successor(24n, 256n), {==})

def at_multiple_26() -> {B.nat64(Nat.mul(26n, 256n)) == Some{B.Number64{0, 6656}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(26n, 256n), Nat.mul(25n, 256n), B.Number64{0, 6400}, B.Number64{0, 6656}, at_256(), at_multiple_25(), multiply_successor(25n, 256n), {==})

def at_multiple_27() -> {B.nat64(Nat.mul(27n, 256n)) == Some{B.Number64{0, 6912}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(27n, 256n), Nat.mul(26n, 256n), B.Number64{0, 6656}, B.Number64{0, 6912}, at_256(), at_multiple_26(), multiply_successor(26n, 256n), {==})

def at_multiple_28() -> {B.nat64(Nat.mul(28n, 256n)) == Some{B.Number64{0, 7168}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(28n, 256n), Nat.mul(27n, 256n), B.Number64{0, 6912}, B.Number64{0, 7168}, at_256(), at_multiple_27(), multiply_successor(27n, 256n), {==})

def at_multiple_29() -> {B.nat64(Nat.mul(29n, 256n)) == Some{B.Number64{0, 7424}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(29n, 256n), Nat.mul(28n, 256n), B.Number64{0, 7168}, B.Number64{0, 7424}, at_256(), at_multiple_28(), multiply_successor(28n, 256n), {==})

def at_multiple_30() -> {B.nat64(Nat.mul(30n, 256n)) == Some{B.Number64{0, 7680}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(30n, 256n), Nat.mul(29n, 256n), B.Number64{0, 7424}, B.Number64{0, 7680}, at_256(), at_multiple_29(), multiply_successor(29n, 256n), {==})

def at_multiple_31() -> {B.nat64(Nat.mul(31n, 256n)) == Some{B.Number64{0, 7936}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(31n, 256n), Nat.mul(30n, 256n), B.Number64{0, 7680}, B.Number64{0, 7936}, at_256(), at_multiple_30(), multiply_successor(30n, 256n), {==})

def at_multiple_32() -> {B.nat64(Nat.mul(32n, 256n)) == Some{B.Number64{0, 8192}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(32n, 256n), Nat.mul(31n, 256n), B.Number64{0, 7936}, B.Number64{0, 8192}, at_256(), at_multiple_31(), multiply_successor(31n, 256n), {==})

def at_multiple_33() -> {B.nat64(Nat.mul(33n, 256n)) == Some{B.Number64{0, 8448}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(33n, 256n), Nat.mul(32n, 256n), B.Number64{0, 8192}, B.Number64{0, 8448}, at_256(), at_multiple_32(), multiply_successor(32n, 256n), {==})

def at_multiple_34() -> {B.nat64(Nat.mul(34n, 256n)) == Some{B.Number64{0, 8704}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(34n, 256n), Nat.mul(33n, 256n), B.Number64{0, 8448}, B.Number64{0, 8704}, at_256(), at_multiple_33(), multiply_successor(33n, 256n), {==})

def at_multiple_35() -> {B.nat64(Nat.mul(35n, 256n)) == Some{B.Number64{0, 8960}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(35n, 256n), Nat.mul(34n, 256n), B.Number64{0, 8704}, B.Number64{0, 8960}, at_256(), at_multiple_34(), multiply_successor(34n, 256n), {==})

def at_multiple_36() -> {B.nat64(Nat.mul(36n, 256n)) == Some{B.Number64{0, 9216}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(36n, 256n), Nat.mul(35n, 256n), B.Number64{0, 8960}, B.Number64{0, 9216}, at_256(), at_multiple_35(), multiply_successor(35n, 256n), {==})

def at_multiple_37() -> {B.nat64(Nat.mul(37n, 256n)) == Some{B.Number64{0, 9472}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(37n, 256n), Nat.mul(36n, 256n), B.Number64{0, 9216}, B.Number64{0, 9472}, at_256(), at_multiple_36(), multiply_successor(36n, 256n), {==})

def at_multiple_38() -> {B.nat64(Nat.mul(38n, 256n)) == Some{B.Number64{0, 9728}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(38n, 256n), Nat.mul(37n, 256n), B.Number64{0, 9472}, B.Number64{0, 9728}, at_256(), at_multiple_37(), multiply_successor(37n, 256n), {==})

def at_multiple_39() -> {B.nat64(Nat.mul(39n, 256n)) == Some{B.Number64{0, 9984}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(39n, 256n), Nat.mul(38n, 256n), B.Number64{0, 9728}, B.Number64{0, 9984}, at_256(), at_multiple_38(), multiply_successor(38n, 256n), {==})

def at_multiple_40() -> {B.nat64(Nat.mul(40n, 256n)) == Some{B.Number64{0, 10240}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(40n, 256n), Nat.mul(39n, 256n), B.Number64{0, 9984}, B.Number64{0, 10240}, at_256(), at_multiple_39(), multiply_successor(39n, 256n), {==})

def at_multiple_41() -> {B.nat64(Nat.mul(41n, 256n)) == Some{B.Number64{0, 10496}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(41n, 256n), Nat.mul(40n, 256n), B.Number64{0, 10240}, B.Number64{0, 10496}, at_256(), at_multiple_40(), multiply_successor(40n, 256n), {==})

def at_multiple_42() -> {B.nat64(Nat.mul(42n, 256n)) == Some{B.Number64{0, 10752}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(42n, 256n), Nat.mul(41n, 256n), B.Number64{0, 10496}, B.Number64{0, 10752}, at_256(), at_multiple_41(), multiply_successor(41n, 256n), {==})

def at_multiple_43() -> {B.nat64(Nat.mul(43n, 256n)) == Some{B.Number64{0, 11008}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(43n, 256n), Nat.mul(42n, 256n), B.Number64{0, 10752}, B.Number64{0, 11008}, at_256(), at_multiple_42(), multiply_successor(42n, 256n), {==})

def at_multiple_44() -> {B.nat64(Nat.mul(44n, 256n)) == Some{B.Number64{0, 11264}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(44n, 256n), Nat.mul(43n, 256n), B.Number64{0, 11008}, B.Number64{0, 11264}, at_256(), at_multiple_43(), multiply_successor(43n, 256n), {==})

def at_multiple_45() -> {B.nat64(Nat.mul(45n, 256n)) == Some{B.Number64{0, 11520}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(45n, 256n), Nat.mul(44n, 256n), B.Number64{0, 11264}, B.Number64{0, 11520}, at_256(), at_multiple_44(), multiply_successor(44n, 256n), {==})

def at_multiple_46() -> {B.nat64(Nat.mul(46n, 256n)) == Some{B.Number64{0, 11776}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(46n, 256n), Nat.mul(45n, 256n), B.Number64{0, 11520}, B.Number64{0, 11776}, at_256(), at_multiple_45(), multiply_successor(45n, 256n), {==})

def at_multiple_47() -> {B.nat64(Nat.mul(47n, 256n)) == Some{B.Number64{0, 12032}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(47n, 256n), Nat.mul(46n, 256n), B.Number64{0, 11776}, B.Number64{0, 12032}, at_256(), at_multiple_46(), multiply_successor(46n, 256n), {==})

def at_multiple_48() -> {B.nat64(Nat.mul(48n, 256n)) == Some{B.Number64{0, 12288}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(48n, 256n), Nat.mul(47n, 256n), B.Number64{0, 12032}, B.Number64{0, 12288}, at_256(), at_multiple_47(), multiply_successor(47n, 256n), {==})

def at_multiple_49() -> {B.nat64(Nat.mul(49n, 256n)) == Some{B.Number64{0, 12544}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(49n, 256n), Nat.mul(48n, 256n), B.Number64{0, 12288}, B.Number64{0, 12544}, at_256(), at_multiple_48(), multiply_successor(48n, 256n), {==})

def at_multiple_50() -> {B.nat64(Nat.mul(50n, 256n)) == Some{B.Number64{0, 12800}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(50n, 256n), Nat.mul(49n, 256n), B.Number64{0, 12544}, B.Number64{0, 12800}, at_256(), at_multiple_49(), multiply_successor(49n, 256n), {==})

def at_multiple_51() -> {B.nat64(Nat.mul(51n, 256n)) == Some{B.Number64{0, 13056}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(51n, 256n), Nat.mul(50n, 256n), B.Number64{0, 12800}, B.Number64{0, 13056}, at_256(), at_multiple_50(), multiply_successor(50n, 256n), {==})

def at_multiple_52() -> {B.nat64(Nat.mul(52n, 256n)) == Some{B.Number64{0, 13312}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(52n, 256n), Nat.mul(51n, 256n), B.Number64{0, 13056}, B.Number64{0, 13312}, at_256(), at_multiple_51(), multiply_successor(51n, 256n), {==})

def at_multiple_53() -> {B.nat64(Nat.mul(53n, 256n)) == Some{B.Number64{0, 13568}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(53n, 256n), Nat.mul(52n, 256n), B.Number64{0, 13312}, B.Number64{0, 13568}, at_256(), at_multiple_52(), multiply_successor(52n, 256n), {==})

def at_multiple_54() -> {B.nat64(Nat.mul(54n, 256n)) == Some{B.Number64{0, 13824}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(54n, 256n), Nat.mul(53n, 256n), B.Number64{0, 13568}, B.Number64{0, 13824}, at_256(), at_multiple_53(), multiply_successor(53n, 256n), {==})

def at_multiple_55() -> {B.nat64(Nat.mul(55n, 256n)) == Some{B.Number64{0, 14080}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(55n, 256n), Nat.mul(54n, 256n), B.Number64{0, 13824}, B.Number64{0, 14080}, at_256(), at_multiple_54(), multiply_successor(54n, 256n), {==})

def at_multiple_56() -> {B.nat64(Nat.mul(56n, 256n)) == Some{B.Number64{0, 14336}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(56n, 256n), Nat.mul(55n, 256n), B.Number64{0, 14080}, B.Number64{0, 14336}, at_256(), at_multiple_55(), multiply_successor(55n, 256n), {==})

def at_multiple_57() -> {B.nat64(Nat.mul(57n, 256n)) == Some{B.Number64{0, 14592}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(57n, 256n), Nat.mul(56n, 256n), B.Number64{0, 14336}, B.Number64{0, 14592}, at_256(), at_multiple_56(), multiply_successor(56n, 256n), {==})

def at_multiple_58() -> {B.nat64(Nat.mul(58n, 256n)) == Some{B.Number64{0, 14848}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(58n, 256n), Nat.mul(57n, 256n), B.Number64{0, 14592}, B.Number64{0, 14848}, at_256(), at_multiple_57(), multiply_successor(57n, 256n), {==})

def at_multiple_59() -> {B.nat64(Nat.mul(59n, 256n)) == Some{B.Number64{0, 15104}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(59n, 256n), Nat.mul(58n, 256n), B.Number64{0, 14848}, B.Number64{0, 15104}, at_256(), at_multiple_58(), multiply_successor(58n, 256n), {==})

def at_multiple_60() -> {B.nat64(Nat.mul(60n, 256n)) == Some{B.Number64{0, 15360}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(60n, 256n), Nat.mul(59n, 256n), B.Number64{0, 15104}, B.Number64{0, 15360}, at_256(), at_multiple_59(), multiply_successor(59n, 256n), {==})

def at_multiple_61() -> {B.nat64(Nat.mul(61n, 256n)) == Some{B.Number64{0, 15616}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(61n, 256n), Nat.mul(60n, 256n), B.Number64{0, 15360}, B.Number64{0, 15616}, at_256(), at_multiple_60(), multiply_successor(60n, 256n), {==})

def at_multiple_62() -> {B.nat64(Nat.mul(62n, 256n)) == Some{B.Number64{0, 15872}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(62n, 256n), Nat.mul(61n, 256n), B.Number64{0, 15616}, B.Number64{0, 15872}, at_256(), at_multiple_61(), multiply_successor(61n, 256n), {==})

def at_multiple_63() -> {B.nat64(Nat.mul(63n, 256n)) == Some{B.Number64{0, 16128}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(63n, 256n), Nat.mul(62n, 256n), B.Number64{0, 15872}, B.Number64{0, 16128}, at_256(), at_multiple_62(), multiply_successor(62n, 256n), {==})

def at_multiple_64() -> {B.nat64(Nat.mul(64n, 256n)) == Some{B.Number64{0, 16384}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(64n, 256n), Nat.mul(63n, 256n), B.Number64{0, 16128}, B.Number64{0, 16384}, at_256(), at_multiple_63(), multiply_successor(63n, 256n), {==})

def at_multiple_65() -> {B.nat64(Nat.mul(65n, 256n)) == Some{B.Number64{0, 16640}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(65n, 256n), Nat.mul(64n, 256n), B.Number64{0, 16384}, B.Number64{0, 16640}, at_256(), at_multiple_64(), multiply_successor(64n, 256n), {==})

def at_multiple_66() -> {B.nat64(Nat.mul(66n, 256n)) == Some{B.Number64{0, 16896}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(66n, 256n), Nat.mul(65n, 256n), B.Number64{0, 16640}, B.Number64{0, 16896}, at_256(), at_multiple_65(), multiply_successor(65n, 256n), {==})

def at_multiple_67() -> {B.nat64(Nat.mul(67n, 256n)) == Some{B.Number64{0, 17152}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(67n, 256n), Nat.mul(66n, 256n), B.Number64{0, 16896}, B.Number64{0, 17152}, at_256(), at_multiple_66(), multiply_successor(66n, 256n), {==})

def at_multiple_68() -> {B.nat64(Nat.mul(68n, 256n)) == Some{B.Number64{0, 17408}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(68n, 256n), Nat.mul(67n, 256n), B.Number64{0, 17152}, B.Number64{0, 17408}, at_256(), at_multiple_67(), multiply_successor(67n, 256n), {==})

def at_multiple_69() -> {B.nat64(Nat.mul(69n, 256n)) == Some{B.Number64{0, 17664}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(69n, 256n), Nat.mul(68n, 256n), B.Number64{0, 17408}, B.Number64{0, 17664}, at_256(), at_multiple_68(), multiply_successor(68n, 256n), {==})

def at_multiple_70() -> {B.nat64(Nat.mul(70n, 256n)) == Some{B.Number64{0, 17920}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(70n, 256n), Nat.mul(69n, 256n), B.Number64{0, 17664}, B.Number64{0, 17920}, at_256(), at_multiple_69(), multiply_successor(69n, 256n), {==})

def at_multiple_71() -> {B.nat64(Nat.mul(71n, 256n)) == Some{B.Number64{0, 18176}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(71n, 256n), Nat.mul(70n, 256n), B.Number64{0, 17920}, B.Number64{0, 18176}, at_256(), at_multiple_70(), multiply_successor(70n, 256n), {==})

def at_multiple_72() -> {B.nat64(Nat.mul(72n, 256n)) == Some{B.Number64{0, 18432}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(72n, 256n), Nat.mul(71n, 256n), B.Number64{0, 18176}, B.Number64{0, 18432}, at_256(), at_multiple_71(), multiply_successor(71n, 256n), {==})

def at_multiple_73() -> {B.nat64(Nat.mul(73n, 256n)) == Some{B.Number64{0, 18688}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(73n, 256n), Nat.mul(72n, 256n), B.Number64{0, 18432}, B.Number64{0, 18688}, at_256(), at_multiple_72(), multiply_successor(72n, 256n), {==})

def at_multiple_74() -> {B.nat64(Nat.mul(74n, 256n)) == Some{B.Number64{0, 18944}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(74n, 256n), Nat.mul(73n, 256n), B.Number64{0, 18688}, B.Number64{0, 18944}, at_256(), at_multiple_73(), multiply_successor(73n, 256n), {==})

def at_multiple_75() -> {B.nat64(Nat.mul(75n, 256n)) == Some{B.Number64{0, 19200}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(75n, 256n), Nat.mul(74n, 256n), B.Number64{0, 18944}, B.Number64{0, 19200}, at_256(), at_multiple_74(), multiply_successor(74n, 256n), {==})

def at_multiple_76() -> {B.nat64(Nat.mul(76n, 256n)) == Some{B.Number64{0, 19456}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(76n, 256n), Nat.mul(75n, 256n), B.Number64{0, 19200}, B.Number64{0, 19456}, at_256(), at_multiple_75(), multiply_successor(75n, 256n), {==})

def at_multiple_77() -> {B.nat64(Nat.mul(77n, 256n)) == Some{B.Number64{0, 19712}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(77n, 256n), Nat.mul(76n, 256n), B.Number64{0, 19456}, B.Number64{0, 19712}, at_256(), at_multiple_76(), multiply_successor(76n, 256n), {==})

def at_multiple_78() -> {B.nat64(Nat.mul(78n, 256n)) == Some{B.Number64{0, 19968}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(78n, 256n), Nat.mul(77n, 256n), B.Number64{0, 19712}, B.Number64{0, 19968}, at_256(), at_multiple_77(), multiply_successor(77n, 256n), {==})

def at_multiple_79() -> {B.nat64(Nat.mul(79n, 256n)) == Some{B.Number64{0, 20224}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(79n, 256n), Nat.mul(78n, 256n), B.Number64{0, 19968}, B.Number64{0, 20224}, at_256(), at_multiple_78(), multiply_successor(78n, 256n), {==})

def at_multiple_80() -> {B.nat64(Nat.mul(80n, 256n)) == Some{B.Number64{0, 20480}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(80n, 256n), Nat.mul(79n, 256n), B.Number64{0, 20224}, B.Number64{0, 20480}, at_256(), at_multiple_79(), multiply_successor(79n, 256n), {==})

def at_multiple_81() -> {B.nat64(Nat.mul(81n, 256n)) == Some{B.Number64{0, 20736}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(81n, 256n), Nat.mul(80n, 256n), B.Number64{0, 20480}, B.Number64{0, 20736}, at_256(), at_multiple_80(), multiply_successor(80n, 256n), {==})

def at_multiple_82() -> {B.nat64(Nat.mul(82n, 256n)) == Some{B.Number64{0, 20992}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(82n, 256n), Nat.mul(81n, 256n), B.Number64{0, 20736}, B.Number64{0, 20992}, at_256(), at_multiple_81(), multiply_successor(81n, 256n), {==})

def at_multiple_83() -> {B.nat64(Nat.mul(83n, 256n)) == Some{B.Number64{0, 21248}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(83n, 256n), Nat.mul(82n, 256n), B.Number64{0, 20992}, B.Number64{0, 21248}, at_256(), at_multiple_82(), multiply_successor(82n, 256n), {==})

def at_multiple_84() -> {B.nat64(Nat.mul(84n, 256n)) == Some{B.Number64{0, 21504}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(84n, 256n), Nat.mul(83n, 256n), B.Number64{0, 21248}, B.Number64{0, 21504}, at_256(), at_multiple_83(), multiply_successor(83n, 256n), {==})

def at_multiple_85() -> {B.nat64(Nat.mul(85n, 256n)) == Some{B.Number64{0, 21760}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(85n, 256n), Nat.mul(84n, 256n), B.Number64{0, 21504}, B.Number64{0, 21760}, at_256(), at_multiple_84(), multiply_successor(84n, 256n), {==})

def at_multiple_86() -> {B.nat64(Nat.mul(86n, 256n)) == Some{B.Number64{0, 22016}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(86n, 256n), Nat.mul(85n, 256n), B.Number64{0, 21760}, B.Number64{0, 22016}, at_256(), at_multiple_85(), multiply_successor(85n, 256n), {==})

def at_multiple_87() -> {B.nat64(Nat.mul(87n, 256n)) == Some{B.Number64{0, 22272}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(87n, 256n), Nat.mul(86n, 256n), B.Number64{0, 22016}, B.Number64{0, 22272}, at_256(), at_multiple_86(), multiply_successor(86n, 256n), {==})

def at_multiple_88() -> {B.nat64(Nat.mul(88n, 256n)) == Some{B.Number64{0, 22528}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(88n, 256n), Nat.mul(87n, 256n), B.Number64{0, 22272}, B.Number64{0, 22528}, at_256(), at_multiple_87(), multiply_successor(87n, 256n), {==})

def at_multiple_89() -> {B.nat64(Nat.mul(89n, 256n)) == Some{B.Number64{0, 22784}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(89n, 256n), Nat.mul(88n, 256n), B.Number64{0, 22528}, B.Number64{0, 22784}, at_256(), at_multiple_88(), multiply_successor(88n, 256n), {==})

def at_multiple_90() -> {B.nat64(Nat.mul(90n, 256n)) == Some{B.Number64{0, 23040}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(90n, 256n), Nat.mul(89n, 256n), B.Number64{0, 22784}, B.Number64{0, 23040}, at_256(), at_multiple_89(), multiply_successor(89n, 256n), {==})

def at_multiple_91() -> {B.nat64(Nat.mul(91n, 256n)) == Some{B.Number64{0, 23296}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(91n, 256n), Nat.mul(90n, 256n), B.Number64{0, 23040}, B.Number64{0, 23296}, at_256(), at_multiple_90(), multiply_successor(90n, 256n), {==})

def at_multiple_92() -> {B.nat64(Nat.mul(92n, 256n)) == Some{B.Number64{0, 23552}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(92n, 256n), Nat.mul(91n, 256n), B.Number64{0, 23296}, B.Number64{0, 23552}, at_256(), at_multiple_91(), multiply_successor(91n, 256n), {==})

def at_multiple_93() -> {B.nat64(Nat.mul(93n, 256n)) == Some{B.Number64{0, 23808}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(93n, 256n), Nat.mul(92n, 256n), B.Number64{0, 23552}, B.Number64{0, 23808}, at_256(), at_multiple_92(), multiply_successor(92n, 256n), {==})

def at_multiple_94() -> {B.nat64(Nat.mul(94n, 256n)) == Some{B.Number64{0, 24064}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(94n, 256n), Nat.mul(93n, 256n), B.Number64{0, 23808}, B.Number64{0, 24064}, at_256(), at_multiple_93(), multiply_successor(93n, 256n), {==})

def at_multiple_95() -> {B.nat64(Nat.mul(95n, 256n)) == Some{B.Number64{0, 24320}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(95n, 256n), Nat.mul(94n, 256n), B.Number64{0, 24064}, B.Number64{0, 24320}, at_256(), at_multiple_94(), multiply_successor(94n, 256n), {==})

def at_multiple_96() -> {B.nat64(Nat.mul(96n, 256n)) == Some{B.Number64{0, 24576}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(96n, 256n), Nat.mul(95n, 256n), B.Number64{0, 24320}, B.Number64{0, 24576}, at_256(), at_multiple_95(), multiply_successor(95n, 256n), {==})

def at_multiple_97() -> {B.nat64(Nat.mul(97n, 256n)) == Some{B.Number64{0, 24832}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(97n, 256n), Nat.mul(96n, 256n), B.Number64{0, 24576}, B.Number64{0, 24832}, at_256(), at_multiple_96(), multiply_successor(96n, 256n), {==})

def at_multiple_98() -> {B.nat64(Nat.mul(98n, 256n)) == Some{B.Number64{0, 25088}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(98n, 256n), Nat.mul(97n, 256n), B.Number64{0, 24832}, B.Number64{0, 25088}, at_256(), at_multiple_97(), multiply_successor(97n, 256n), {==})

def at_multiple_99() -> {B.nat64(Nat.mul(99n, 256n)) == Some{B.Number64{0, 25344}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(99n, 256n), Nat.mul(98n, 256n), B.Number64{0, 25088}, B.Number64{0, 25344}, at_256(), at_multiple_98(), multiply_successor(98n, 256n), {==})

def at_multiple_100() -> {B.nat64(Nat.mul(100n, 256n)) == Some{B.Number64{0, 25600}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(100n, 256n), Nat.mul(99n, 256n), B.Number64{0, 25344}, B.Number64{0, 25600}, at_256(), at_multiple_99(), multiply_successor(99n, 256n), {==})

def at_multiple_101() -> {B.nat64(Nat.mul(101n, 256n)) == Some{B.Number64{0, 25856}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(101n, 256n), Nat.mul(100n, 256n), B.Number64{0, 25600}, B.Number64{0, 25856}, at_256(), at_multiple_100(), multiply_successor(100n, 256n), {==})

def at_multiple_102() -> {B.nat64(Nat.mul(102n, 256n)) == Some{B.Number64{0, 26112}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(102n, 256n), Nat.mul(101n, 256n), B.Number64{0, 25856}, B.Number64{0, 26112}, at_256(), at_multiple_101(), multiply_successor(101n, 256n), {==})

def at_multiple_103() -> {B.nat64(Nat.mul(103n, 256n)) == Some{B.Number64{0, 26368}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(103n, 256n), Nat.mul(102n, 256n), B.Number64{0, 26112}, B.Number64{0, 26368}, at_256(), at_multiple_102(), multiply_successor(102n, 256n), {==})

def at_multiple_104() -> {B.nat64(Nat.mul(104n, 256n)) == Some{B.Number64{0, 26624}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(104n, 256n), Nat.mul(103n, 256n), B.Number64{0, 26368}, B.Number64{0, 26624}, at_256(), at_multiple_103(), multiply_successor(103n, 256n), {==})

def at_multiple_105() -> {B.nat64(Nat.mul(105n, 256n)) == Some{B.Number64{0, 26880}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(105n, 256n), Nat.mul(104n, 256n), B.Number64{0, 26624}, B.Number64{0, 26880}, at_256(), at_multiple_104(), multiply_successor(104n, 256n), {==})

def at_multiple_106() -> {B.nat64(Nat.mul(106n, 256n)) == Some{B.Number64{0, 27136}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(106n, 256n), Nat.mul(105n, 256n), B.Number64{0, 26880}, B.Number64{0, 27136}, at_256(), at_multiple_105(), multiply_successor(105n, 256n), {==})

def at_multiple_107() -> {B.nat64(Nat.mul(107n, 256n)) == Some{B.Number64{0, 27392}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(107n, 256n), Nat.mul(106n, 256n), B.Number64{0, 27136}, B.Number64{0, 27392}, at_256(), at_multiple_106(), multiply_successor(106n, 256n), {==})

def at_multiple_108() -> {B.nat64(Nat.mul(108n, 256n)) == Some{B.Number64{0, 27648}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(108n, 256n), Nat.mul(107n, 256n), B.Number64{0, 27392}, B.Number64{0, 27648}, at_256(), at_multiple_107(), multiply_successor(107n, 256n), {==})

def at_multiple_109() -> {B.nat64(Nat.mul(109n, 256n)) == Some{B.Number64{0, 27904}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(109n, 256n), Nat.mul(108n, 256n), B.Number64{0, 27648}, B.Number64{0, 27904}, at_256(), at_multiple_108(), multiply_successor(108n, 256n), {==})

def at_multiple_110() -> {B.nat64(Nat.mul(110n, 256n)) == Some{B.Number64{0, 28160}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(110n, 256n), Nat.mul(109n, 256n), B.Number64{0, 27904}, B.Number64{0, 28160}, at_256(), at_multiple_109(), multiply_successor(109n, 256n), {==})

def at_multiple_111() -> {B.nat64(Nat.mul(111n, 256n)) == Some{B.Number64{0, 28416}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(111n, 256n), Nat.mul(110n, 256n), B.Number64{0, 28160}, B.Number64{0, 28416}, at_256(), at_multiple_110(), multiply_successor(110n, 256n), {==})

def at_multiple_112() -> {B.nat64(Nat.mul(112n, 256n)) == Some{B.Number64{0, 28672}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(112n, 256n), Nat.mul(111n, 256n), B.Number64{0, 28416}, B.Number64{0, 28672}, at_256(), at_multiple_111(), multiply_successor(111n, 256n), {==})

def at_multiple_113() -> {B.nat64(Nat.mul(113n, 256n)) == Some{B.Number64{0, 28928}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(113n, 256n), Nat.mul(112n, 256n), B.Number64{0, 28672}, B.Number64{0, 28928}, at_256(), at_multiple_112(), multiply_successor(112n, 256n), {==})

def at_multiple_114() -> {B.nat64(Nat.mul(114n, 256n)) == Some{B.Number64{0, 29184}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(114n, 256n), Nat.mul(113n, 256n), B.Number64{0, 28928}, B.Number64{0, 29184}, at_256(), at_multiple_113(), multiply_successor(113n, 256n), {==})

def at_multiple_115() -> {B.nat64(Nat.mul(115n, 256n)) == Some{B.Number64{0, 29440}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(115n, 256n), Nat.mul(114n, 256n), B.Number64{0, 29184}, B.Number64{0, 29440}, at_256(), at_multiple_114(), multiply_successor(114n, 256n), {==})

def at_multiple_116() -> {B.nat64(Nat.mul(116n, 256n)) == Some{B.Number64{0, 29696}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(116n, 256n), Nat.mul(115n, 256n), B.Number64{0, 29440}, B.Number64{0, 29696}, at_256(), at_multiple_115(), multiply_successor(115n, 256n), {==})

def at_multiple_117() -> {B.nat64(Nat.mul(117n, 256n)) == Some{B.Number64{0, 29952}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(117n, 256n), Nat.mul(116n, 256n), B.Number64{0, 29696}, B.Number64{0, 29952}, at_256(), at_multiple_116(), multiply_successor(116n, 256n), {==})

def at_multiple_118() -> {B.nat64(Nat.mul(118n, 256n)) == Some{B.Number64{0, 30208}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(118n, 256n), Nat.mul(117n, 256n), B.Number64{0, 29952}, B.Number64{0, 30208}, at_256(), at_multiple_117(), multiply_successor(117n, 256n), {==})

def at_multiple_119() -> {B.nat64(Nat.mul(119n, 256n)) == Some{B.Number64{0, 30464}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(119n, 256n), Nat.mul(118n, 256n), B.Number64{0, 30208}, B.Number64{0, 30464}, at_256(), at_multiple_118(), multiply_successor(118n, 256n), {==})

def at_multiple_120() -> {B.nat64(Nat.mul(120n, 256n)) == Some{B.Number64{0, 30720}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(120n, 256n), Nat.mul(119n, 256n), B.Number64{0, 30464}, B.Number64{0, 30720}, at_256(), at_multiple_119(), multiply_successor(119n, 256n), {==})

def at_multiple_121() -> {B.nat64(Nat.mul(121n, 256n)) == Some{B.Number64{0, 30976}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(121n, 256n), Nat.mul(120n, 256n), B.Number64{0, 30720}, B.Number64{0, 30976}, at_256(), at_multiple_120(), multiply_successor(120n, 256n), {==})

def at_multiple_122() -> {B.nat64(Nat.mul(122n, 256n)) == Some{B.Number64{0, 31232}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(122n, 256n), Nat.mul(121n, 256n), B.Number64{0, 30976}, B.Number64{0, 31232}, at_256(), at_multiple_121(), multiply_successor(121n, 256n), {==})

def at_multiple_123() -> {B.nat64(Nat.mul(123n, 256n)) == Some{B.Number64{0, 31488}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(123n, 256n), Nat.mul(122n, 256n), B.Number64{0, 31232}, B.Number64{0, 31488}, at_256(), at_multiple_122(), multiply_successor(122n, 256n), {==})

def at_multiple_124() -> {B.nat64(Nat.mul(124n, 256n)) == Some{B.Number64{0, 31744}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(124n, 256n), Nat.mul(123n, 256n), B.Number64{0, 31488}, B.Number64{0, 31744}, at_256(), at_multiple_123(), multiply_successor(123n, 256n), {==})

def at_multiple_125() -> {B.nat64(Nat.mul(125n, 256n)) == Some{B.Number64{0, 32000}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(125n, 256n), Nat.mul(124n, 256n), B.Number64{0, 31744}, B.Number64{0, 32000}, at_256(), at_multiple_124(), multiply_successor(124n, 256n), {==})

def at_multiple_126() -> {B.nat64(Nat.mul(126n, 256n)) == Some{B.Number64{0, 32256}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(126n, 256n), Nat.mul(125n, 256n), B.Number64{0, 32000}, B.Number64{0, 32256}, at_256(), at_multiple_125(), multiply_successor(125n, 256n), {==})

def at_multiple_127() -> {B.nat64(Nat.mul(127n, 256n)) == Some{B.Number64{0, 32512}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(127n, 256n), Nat.mul(126n, 256n), B.Number64{0, 32256}, B.Number64{0, 32512}, at_256(), at_multiple_126(), multiply_successor(126n, 256n), {==})

def at_multiple_128() -> {B.nat64(Nat.mul(128n, 256n)) == Some{B.Number64{0, 32768}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(128n, 256n), Nat.mul(127n, 256n), B.Number64{0, 32512}, B.Number64{0, 32768}, at_256(), at_multiple_127(), multiply_successor(127n, 256n), {==})

def at_multiple_129() -> {B.nat64(Nat.mul(129n, 256n)) == Some{B.Number64{0, 33024}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(129n, 256n), Nat.mul(128n, 256n), B.Number64{0, 32768}, B.Number64{0, 33024}, at_256(), at_multiple_128(), multiply_successor(128n, 256n), {==})

def at_multiple_130() -> {B.nat64(Nat.mul(130n, 256n)) == Some{B.Number64{0, 33280}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(130n, 256n), Nat.mul(129n, 256n), B.Number64{0, 33024}, B.Number64{0, 33280}, at_256(), at_multiple_129(), multiply_successor(129n, 256n), {==})

def at_multiple_131() -> {B.nat64(Nat.mul(131n, 256n)) == Some{B.Number64{0, 33536}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(131n, 256n), Nat.mul(130n, 256n), B.Number64{0, 33280}, B.Number64{0, 33536}, at_256(), at_multiple_130(), multiply_successor(130n, 256n), {==})

def at_multiple_132() -> {B.nat64(Nat.mul(132n, 256n)) == Some{B.Number64{0, 33792}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(132n, 256n), Nat.mul(131n, 256n), B.Number64{0, 33536}, B.Number64{0, 33792}, at_256(), at_multiple_131(), multiply_successor(131n, 256n), {==})

def at_multiple_133() -> {B.nat64(Nat.mul(133n, 256n)) == Some{B.Number64{0, 34048}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(133n, 256n), Nat.mul(132n, 256n), B.Number64{0, 33792}, B.Number64{0, 34048}, at_256(), at_multiple_132(), multiply_successor(132n, 256n), {==})

def at_multiple_134() -> {B.nat64(Nat.mul(134n, 256n)) == Some{B.Number64{0, 34304}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(134n, 256n), Nat.mul(133n, 256n), B.Number64{0, 34048}, B.Number64{0, 34304}, at_256(), at_multiple_133(), multiply_successor(133n, 256n), {==})

def at_multiple_135() -> {B.nat64(Nat.mul(135n, 256n)) == Some{B.Number64{0, 34560}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(135n, 256n), Nat.mul(134n, 256n), B.Number64{0, 34304}, B.Number64{0, 34560}, at_256(), at_multiple_134(), multiply_successor(134n, 256n), {==})

def at_multiple_136() -> {B.nat64(Nat.mul(136n, 256n)) == Some{B.Number64{0, 34816}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(136n, 256n), Nat.mul(135n, 256n), B.Number64{0, 34560}, B.Number64{0, 34816}, at_256(), at_multiple_135(), multiply_successor(135n, 256n), {==})

def at_multiple_137() -> {B.nat64(Nat.mul(137n, 256n)) == Some{B.Number64{0, 35072}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(137n, 256n), Nat.mul(136n, 256n), B.Number64{0, 34816}, B.Number64{0, 35072}, at_256(), at_multiple_136(), multiply_successor(136n, 256n), {==})

def at_multiple_138() -> {B.nat64(Nat.mul(138n, 256n)) == Some{B.Number64{0, 35328}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(138n, 256n), Nat.mul(137n, 256n), B.Number64{0, 35072}, B.Number64{0, 35328}, at_256(), at_multiple_137(), multiply_successor(137n, 256n), {==})

def at_multiple_139() -> {B.nat64(Nat.mul(139n, 256n)) == Some{B.Number64{0, 35584}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(139n, 256n), Nat.mul(138n, 256n), B.Number64{0, 35328}, B.Number64{0, 35584}, at_256(), at_multiple_138(), multiply_successor(138n, 256n), {==})

def at_multiple_140() -> {B.nat64(Nat.mul(140n, 256n)) == Some{B.Number64{0, 35840}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(140n, 256n), Nat.mul(139n, 256n), B.Number64{0, 35584}, B.Number64{0, 35840}, at_256(), at_multiple_139(), multiply_successor(139n, 256n), {==})

def at_multiple_141() -> {B.nat64(Nat.mul(141n, 256n)) == Some{B.Number64{0, 36096}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(141n, 256n), Nat.mul(140n, 256n), B.Number64{0, 35840}, B.Number64{0, 36096}, at_256(), at_multiple_140(), multiply_successor(140n, 256n), {==})

def at_multiple_142() -> {B.nat64(Nat.mul(142n, 256n)) == Some{B.Number64{0, 36352}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(142n, 256n), Nat.mul(141n, 256n), B.Number64{0, 36096}, B.Number64{0, 36352}, at_256(), at_multiple_141(), multiply_successor(141n, 256n), {==})

def at_multiple_143() -> {B.nat64(Nat.mul(143n, 256n)) == Some{B.Number64{0, 36608}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(143n, 256n), Nat.mul(142n, 256n), B.Number64{0, 36352}, B.Number64{0, 36608}, at_256(), at_multiple_142(), multiply_successor(142n, 256n), {==})

def at_multiple_144() -> {B.nat64(Nat.mul(144n, 256n)) == Some{B.Number64{0, 36864}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(144n, 256n), Nat.mul(143n, 256n), B.Number64{0, 36608}, B.Number64{0, 36864}, at_256(), at_multiple_143(), multiply_successor(143n, 256n), {==})

def at_multiple_145() -> {B.nat64(Nat.mul(145n, 256n)) == Some{B.Number64{0, 37120}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(145n, 256n), Nat.mul(144n, 256n), B.Number64{0, 36864}, B.Number64{0, 37120}, at_256(), at_multiple_144(), multiply_successor(144n, 256n), {==})

def at_multiple_146() -> {B.nat64(Nat.mul(146n, 256n)) == Some{B.Number64{0, 37376}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(146n, 256n), Nat.mul(145n, 256n), B.Number64{0, 37120}, B.Number64{0, 37376}, at_256(), at_multiple_145(), multiply_successor(145n, 256n), {==})

def at_multiple_147() -> {B.nat64(Nat.mul(147n, 256n)) == Some{B.Number64{0, 37632}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(147n, 256n), Nat.mul(146n, 256n), B.Number64{0, 37376}, B.Number64{0, 37632}, at_256(), at_multiple_146(), multiply_successor(146n, 256n), {==})

def at_multiple_148() -> {B.nat64(Nat.mul(148n, 256n)) == Some{B.Number64{0, 37888}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(148n, 256n), Nat.mul(147n, 256n), B.Number64{0, 37632}, B.Number64{0, 37888}, at_256(), at_multiple_147(), multiply_successor(147n, 256n), {==})

def at_multiple_149() -> {B.nat64(Nat.mul(149n, 256n)) == Some{B.Number64{0, 38144}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(149n, 256n), Nat.mul(148n, 256n), B.Number64{0, 37888}, B.Number64{0, 38144}, at_256(), at_multiple_148(), multiply_successor(148n, 256n), {==})

def at_multiple_150() -> {B.nat64(Nat.mul(150n, 256n)) == Some{B.Number64{0, 38400}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(150n, 256n), Nat.mul(149n, 256n), B.Number64{0, 38144}, B.Number64{0, 38400}, at_256(), at_multiple_149(), multiply_successor(149n, 256n), {==})

def at_multiple_151() -> {B.nat64(Nat.mul(151n, 256n)) == Some{B.Number64{0, 38656}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(151n, 256n), Nat.mul(150n, 256n), B.Number64{0, 38400}, B.Number64{0, 38656}, at_256(), at_multiple_150(), multiply_successor(150n, 256n), {==})

def at_multiple_152() -> {B.nat64(Nat.mul(152n, 256n)) == Some{B.Number64{0, 38912}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(152n, 256n), Nat.mul(151n, 256n), B.Number64{0, 38656}, B.Number64{0, 38912}, at_256(), at_multiple_151(), multiply_successor(151n, 256n), {==})

def at_multiple_153() -> {B.nat64(Nat.mul(153n, 256n)) == Some{B.Number64{0, 39168}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(153n, 256n), Nat.mul(152n, 256n), B.Number64{0, 38912}, B.Number64{0, 39168}, at_256(), at_multiple_152(), multiply_successor(152n, 256n), {==})

def at_multiple_154() -> {B.nat64(Nat.mul(154n, 256n)) == Some{B.Number64{0, 39424}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(154n, 256n), Nat.mul(153n, 256n), B.Number64{0, 39168}, B.Number64{0, 39424}, at_256(), at_multiple_153(), multiply_successor(153n, 256n), {==})

def at_multiple_155() -> {B.nat64(Nat.mul(155n, 256n)) == Some{B.Number64{0, 39680}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(155n, 256n), Nat.mul(154n, 256n), B.Number64{0, 39424}, B.Number64{0, 39680}, at_256(), at_multiple_154(), multiply_successor(154n, 256n), {==})

def at_multiple_156() -> {B.nat64(Nat.mul(156n, 256n)) == Some{B.Number64{0, 39936}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(156n, 256n), Nat.mul(155n, 256n), B.Number64{0, 39680}, B.Number64{0, 39936}, at_256(), at_multiple_155(), multiply_successor(155n, 256n), {==})

def at_multiple_157() -> {B.nat64(Nat.mul(157n, 256n)) == Some{B.Number64{0, 40192}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(157n, 256n), Nat.mul(156n, 256n), B.Number64{0, 39936}, B.Number64{0, 40192}, at_256(), at_multiple_156(), multiply_successor(156n, 256n), {==})

def at_multiple_158() -> {B.nat64(Nat.mul(158n, 256n)) == Some{B.Number64{0, 40448}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(158n, 256n), Nat.mul(157n, 256n), B.Number64{0, 40192}, B.Number64{0, 40448}, at_256(), at_multiple_157(), multiply_successor(157n, 256n), {==})

def at_multiple_159() -> {B.nat64(Nat.mul(159n, 256n)) == Some{B.Number64{0, 40704}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(159n, 256n), Nat.mul(158n, 256n), B.Number64{0, 40448}, B.Number64{0, 40704}, at_256(), at_multiple_158(), multiply_successor(158n, 256n), {==})

def at_multiple_160() -> {B.nat64(Nat.mul(160n, 256n)) == Some{B.Number64{0, 40960}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(160n, 256n), Nat.mul(159n, 256n), B.Number64{0, 40704}, B.Number64{0, 40960}, at_256(), at_multiple_159(), multiply_successor(159n, 256n), {==})

def at_multiple_161() -> {B.nat64(Nat.mul(161n, 256n)) == Some{B.Number64{0, 41216}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(161n, 256n), Nat.mul(160n, 256n), B.Number64{0, 40960}, B.Number64{0, 41216}, at_256(), at_multiple_160(), multiply_successor(160n, 256n), {==})

def at_multiple_162() -> {B.nat64(Nat.mul(162n, 256n)) == Some{B.Number64{0, 41472}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(162n, 256n), Nat.mul(161n, 256n), B.Number64{0, 41216}, B.Number64{0, 41472}, at_256(), at_multiple_161(), multiply_successor(161n, 256n), {==})

def at_multiple_163() -> {B.nat64(Nat.mul(163n, 256n)) == Some{B.Number64{0, 41728}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(163n, 256n), Nat.mul(162n, 256n), B.Number64{0, 41472}, B.Number64{0, 41728}, at_256(), at_multiple_162(), multiply_successor(162n, 256n), {==})

def at_multiple_164() -> {B.nat64(Nat.mul(164n, 256n)) == Some{B.Number64{0, 41984}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(164n, 256n), Nat.mul(163n, 256n), B.Number64{0, 41728}, B.Number64{0, 41984}, at_256(), at_multiple_163(), multiply_successor(163n, 256n), {==})

def at_multiple_165() -> {B.nat64(Nat.mul(165n, 256n)) == Some{B.Number64{0, 42240}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(165n, 256n), Nat.mul(164n, 256n), B.Number64{0, 41984}, B.Number64{0, 42240}, at_256(), at_multiple_164(), multiply_successor(164n, 256n), {==})

def at_multiple_166() -> {B.nat64(Nat.mul(166n, 256n)) == Some{B.Number64{0, 42496}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(166n, 256n), Nat.mul(165n, 256n), B.Number64{0, 42240}, B.Number64{0, 42496}, at_256(), at_multiple_165(), multiply_successor(165n, 256n), {==})

def at_multiple_167() -> {B.nat64(Nat.mul(167n, 256n)) == Some{B.Number64{0, 42752}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(167n, 256n), Nat.mul(166n, 256n), B.Number64{0, 42496}, B.Number64{0, 42752}, at_256(), at_multiple_166(), multiply_successor(166n, 256n), {==})

def at_multiple_168() -> {B.nat64(Nat.mul(168n, 256n)) == Some{B.Number64{0, 43008}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(168n, 256n), Nat.mul(167n, 256n), B.Number64{0, 42752}, B.Number64{0, 43008}, at_256(), at_multiple_167(), multiply_successor(167n, 256n), {==})

def at_multiple_169() -> {B.nat64(Nat.mul(169n, 256n)) == Some{B.Number64{0, 43264}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(169n, 256n), Nat.mul(168n, 256n), B.Number64{0, 43008}, B.Number64{0, 43264}, at_256(), at_multiple_168(), multiply_successor(168n, 256n), {==})

def at_multiple_170() -> {B.nat64(Nat.mul(170n, 256n)) == Some{B.Number64{0, 43520}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(170n, 256n), Nat.mul(169n, 256n), B.Number64{0, 43264}, B.Number64{0, 43520}, at_256(), at_multiple_169(), multiply_successor(169n, 256n), {==})

def at_multiple_171() -> {B.nat64(Nat.mul(171n, 256n)) == Some{B.Number64{0, 43776}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(171n, 256n), Nat.mul(170n, 256n), B.Number64{0, 43520}, B.Number64{0, 43776}, at_256(), at_multiple_170(), multiply_successor(170n, 256n), {==})

def at_multiple_172() -> {B.nat64(Nat.mul(172n, 256n)) == Some{B.Number64{0, 44032}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(172n, 256n), Nat.mul(171n, 256n), B.Number64{0, 43776}, B.Number64{0, 44032}, at_256(), at_multiple_171(), multiply_successor(171n, 256n), {==})

def at_multiple_173() -> {B.nat64(Nat.mul(173n, 256n)) == Some{B.Number64{0, 44288}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(173n, 256n), Nat.mul(172n, 256n), B.Number64{0, 44032}, B.Number64{0, 44288}, at_256(), at_multiple_172(), multiply_successor(172n, 256n), {==})

def at_multiple_174() -> {B.nat64(Nat.mul(174n, 256n)) == Some{B.Number64{0, 44544}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(174n, 256n), Nat.mul(173n, 256n), B.Number64{0, 44288}, B.Number64{0, 44544}, at_256(), at_multiple_173(), multiply_successor(173n, 256n), {==})

def at_multiple_175() -> {B.nat64(Nat.mul(175n, 256n)) == Some{B.Number64{0, 44800}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(175n, 256n), Nat.mul(174n, 256n), B.Number64{0, 44544}, B.Number64{0, 44800}, at_256(), at_multiple_174(), multiply_successor(174n, 256n), {==})

def at_multiple_176() -> {B.nat64(Nat.mul(176n, 256n)) == Some{B.Number64{0, 45056}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(176n, 256n), Nat.mul(175n, 256n), B.Number64{0, 44800}, B.Number64{0, 45056}, at_256(), at_multiple_175(), multiply_successor(175n, 256n), {==})

def at_multiple_177() -> {B.nat64(Nat.mul(177n, 256n)) == Some{B.Number64{0, 45312}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(177n, 256n), Nat.mul(176n, 256n), B.Number64{0, 45056}, B.Number64{0, 45312}, at_256(), at_multiple_176(), multiply_successor(176n, 256n), {==})

def at_multiple_178() -> {B.nat64(Nat.mul(178n, 256n)) == Some{B.Number64{0, 45568}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(178n, 256n), Nat.mul(177n, 256n), B.Number64{0, 45312}, B.Number64{0, 45568}, at_256(), at_multiple_177(), multiply_successor(177n, 256n), {==})

def at_multiple_179() -> {B.nat64(Nat.mul(179n, 256n)) == Some{B.Number64{0, 45824}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(179n, 256n), Nat.mul(178n, 256n), B.Number64{0, 45568}, B.Number64{0, 45824}, at_256(), at_multiple_178(), multiply_successor(178n, 256n), {==})

def at_multiple_180() -> {B.nat64(Nat.mul(180n, 256n)) == Some{B.Number64{0, 46080}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(180n, 256n), Nat.mul(179n, 256n), B.Number64{0, 45824}, B.Number64{0, 46080}, at_256(), at_multiple_179(), multiply_successor(179n, 256n), {==})

def at_multiple_181() -> {B.nat64(Nat.mul(181n, 256n)) == Some{B.Number64{0, 46336}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(181n, 256n), Nat.mul(180n, 256n), B.Number64{0, 46080}, B.Number64{0, 46336}, at_256(), at_multiple_180(), multiply_successor(180n, 256n), {==})

def at_multiple_182() -> {B.nat64(Nat.mul(182n, 256n)) == Some{B.Number64{0, 46592}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(182n, 256n), Nat.mul(181n, 256n), B.Number64{0, 46336}, B.Number64{0, 46592}, at_256(), at_multiple_181(), multiply_successor(181n, 256n), {==})

def at_multiple_183() -> {B.nat64(Nat.mul(183n, 256n)) == Some{B.Number64{0, 46848}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(183n, 256n), Nat.mul(182n, 256n), B.Number64{0, 46592}, B.Number64{0, 46848}, at_256(), at_multiple_182(), multiply_successor(182n, 256n), {==})

def at_multiple_184() -> {B.nat64(Nat.mul(184n, 256n)) == Some{B.Number64{0, 47104}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(184n, 256n), Nat.mul(183n, 256n), B.Number64{0, 46848}, B.Number64{0, 47104}, at_256(), at_multiple_183(), multiply_successor(183n, 256n), {==})

def at_multiple_185() -> {B.nat64(Nat.mul(185n, 256n)) == Some{B.Number64{0, 47360}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(185n, 256n), Nat.mul(184n, 256n), B.Number64{0, 47104}, B.Number64{0, 47360}, at_256(), at_multiple_184(), multiply_successor(184n, 256n), {==})

def at_multiple_186() -> {B.nat64(Nat.mul(186n, 256n)) == Some{B.Number64{0, 47616}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(186n, 256n), Nat.mul(185n, 256n), B.Number64{0, 47360}, B.Number64{0, 47616}, at_256(), at_multiple_185(), multiply_successor(185n, 256n), {==})

def at_multiple_187() -> {B.nat64(Nat.mul(187n, 256n)) == Some{B.Number64{0, 47872}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(187n, 256n), Nat.mul(186n, 256n), B.Number64{0, 47616}, B.Number64{0, 47872}, at_256(), at_multiple_186(), multiply_successor(186n, 256n), {==})

def at_multiple_188() -> {B.nat64(Nat.mul(188n, 256n)) == Some{B.Number64{0, 48128}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(188n, 256n), Nat.mul(187n, 256n), B.Number64{0, 47872}, B.Number64{0, 48128}, at_256(), at_multiple_187(), multiply_successor(187n, 256n), {==})

def at_multiple_189() -> {B.nat64(Nat.mul(189n, 256n)) == Some{B.Number64{0, 48384}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(189n, 256n), Nat.mul(188n, 256n), B.Number64{0, 48128}, B.Number64{0, 48384}, at_256(), at_multiple_188(), multiply_successor(188n, 256n), {==})

def at_multiple_190() -> {B.nat64(Nat.mul(190n, 256n)) == Some{B.Number64{0, 48640}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(190n, 256n), Nat.mul(189n, 256n), B.Number64{0, 48384}, B.Number64{0, 48640}, at_256(), at_multiple_189(), multiply_successor(189n, 256n), {==})

def at_multiple_191() -> {B.nat64(Nat.mul(191n, 256n)) == Some{B.Number64{0, 48896}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(191n, 256n), Nat.mul(190n, 256n), B.Number64{0, 48640}, B.Number64{0, 48896}, at_256(), at_multiple_190(), multiply_successor(190n, 256n), {==})

def at_multiple_192() -> {B.nat64(Nat.mul(192n, 256n)) == Some{B.Number64{0, 49152}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(192n, 256n), Nat.mul(191n, 256n), B.Number64{0, 48896}, B.Number64{0, 49152}, at_256(), at_multiple_191(), multiply_successor(191n, 256n), {==})

def at_multiple_193() -> {B.nat64(Nat.mul(193n, 256n)) == Some{B.Number64{0, 49408}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(193n, 256n), Nat.mul(192n, 256n), B.Number64{0, 49152}, B.Number64{0, 49408}, at_256(), at_multiple_192(), multiply_successor(192n, 256n), {==})

def at_multiple_194() -> {B.nat64(Nat.mul(194n, 256n)) == Some{B.Number64{0, 49664}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(194n, 256n), Nat.mul(193n, 256n), B.Number64{0, 49408}, B.Number64{0, 49664}, at_256(), at_multiple_193(), multiply_successor(193n, 256n), {==})

def at_multiple_195() -> {B.nat64(Nat.mul(195n, 256n)) == Some{B.Number64{0, 49920}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(195n, 256n), Nat.mul(194n, 256n), B.Number64{0, 49664}, B.Number64{0, 49920}, at_256(), at_multiple_194(), multiply_successor(194n, 256n), {==})

def at_multiple_196() -> {B.nat64(Nat.mul(196n, 256n)) == Some{B.Number64{0, 50176}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(196n, 256n), Nat.mul(195n, 256n), B.Number64{0, 49920}, B.Number64{0, 50176}, at_256(), at_multiple_195(), multiply_successor(195n, 256n), {==})

def at_multiple_197() -> {B.nat64(Nat.mul(197n, 256n)) == Some{B.Number64{0, 50432}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(197n, 256n), Nat.mul(196n, 256n), B.Number64{0, 50176}, B.Number64{0, 50432}, at_256(), at_multiple_196(), multiply_successor(196n, 256n), {==})

def at_multiple_198() -> {B.nat64(Nat.mul(198n, 256n)) == Some{B.Number64{0, 50688}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(198n, 256n), Nat.mul(197n, 256n), B.Number64{0, 50432}, B.Number64{0, 50688}, at_256(), at_multiple_197(), multiply_successor(197n, 256n), {==})

def at_multiple_199() -> {B.nat64(Nat.mul(199n, 256n)) == Some{B.Number64{0, 50944}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(199n, 256n), Nat.mul(198n, 256n), B.Number64{0, 50688}, B.Number64{0, 50944}, at_256(), at_multiple_198(), multiply_successor(198n, 256n), {==})

def at_multiple_200() -> {B.nat64(Nat.mul(200n, 256n)) == Some{B.Number64{0, 51200}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(200n, 256n), Nat.mul(199n, 256n), B.Number64{0, 50944}, B.Number64{0, 51200}, at_256(), at_multiple_199(), multiply_successor(199n, 256n), {==})

def at_multiple_201() -> {B.nat64(Nat.mul(201n, 256n)) == Some{B.Number64{0, 51456}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(201n, 256n), Nat.mul(200n, 256n), B.Number64{0, 51200}, B.Number64{0, 51456}, at_256(), at_multiple_200(), multiply_successor(200n, 256n), {==})

def at_multiple_202() -> {B.nat64(Nat.mul(202n, 256n)) == Some{B.Number64{0, 51712}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(202n, 256n), Nat.mul(201n, 256n), B.Number64{0, 51456}, B.Number64{0, 51712}, at_256(), at_multiple_201(), multiply_successor(201n, 256n), {==})

def at_multiple_203() -> {B.nat64(Nat.mul(203n, 256n)) == Some{B.Number64{0, 51968}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(203n, 256n), Nat.mul(202n, 256n), B.Number64{0, 51712}, B.Number64{0, 51968}, at_256(), at_multiple_202(), multiply_successor(202n, 256n), {==})

def at_multiple_204() -> {B.nat64(Nat.mul(204n, 256n)) == Some{B.Number64{0, 52224}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(204n, 256n), Nat.mul(203n, 256n), B.Number64{0, 51968}, B.Number64{0, 52224}, at_256(), at_multiple_203(), multiply_successor(203n, 256n), {==})

def at_multiple_205() -> {B.nat64(Nat.mul(205n, 256n)) == Some{B.Number64{0, 52480}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(205n, 256n), Nat.mul(204n, 256n), B.Number64{0, 52224}, B.Number64{0, 52480}, at_256(), at_multiple_204(), multiply_successor(204n, 256n), {==})

def at_multiple_206() -> {B.nat64(Nat.mul(206n, 256n)) == Some{B.Number64{0, 52736}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(206n, 256n), Nat.mul(205n, 256n), B.Number64{0, 52480}, B.Number64{0, 52736}, at_256(), at_multiple_205(), multiply_successor(205n, 256n), {==})

def at_multiple_207() -> {B.nat64(Nat.mul(207n, 256n)) == Some{B.Number64{0, 52992}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(207n, 256n), Nat.mul(206n, 256n), B.Number64{0, 52736}, B.Number64{0, 52992}, at_256(), at_multiple_206(), multiply_successor(206n, 256n), {==})

def at_multiple_208() -> {B.nat64(Nat.mul(208n, 256n)) == Some{B.Number64{0, 53248}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(208n, 256n), Nat.mul(207n, 256n), B.Number64{0, 52992}, B.Number64{0, 53248}, at_256(), at_multiple_207(), multiply_successor(207n, 256n), {==})

def at_multiple_209() -> {B.nat64(Nat.mul(209n, 256n)) == Some{B.Number64{0, 53504}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(209n, 256n), Nat.mul(208n, 256n), B.Number64{0, 53248}, B.Number64{0, 53504}, at_256(), at_multiple_208(), multiply_successor(208n, 256n), {==})

def at_multiple_210() -> {B.nat64(Nat.mul(210n, 256n)) == Some{B.Number64{0, 53760}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(210n, 256n), Nat.mul(209n, 256n), B.Number64{0, 53504}, B.Number64{0, 53760}, at_256(), at_multiple_209(), multiply_successor(209n, 256n), {==})

def at_multiple_211() -> {B.nat64(Nat.mul(211n, 256n)) == Some{B.Number64{0, 54016}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(211n, 256n), Nat.mul(210n, 256n), B.Number64{0, 53760}, B.Number64{0, 54016}, at_256(), at_multiple_210(), multiply_successor(210n, 256n), {==})

def at_multiple_212() -> {B.nat64(Nat.mul(212n, 256n)) == Some{B.Number64{0, 54272}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(212n, 256n), Nat.mul(211n, 256n), B.Number64{0, 54016}, B.Number64{0, 54272}, at_256(), at_multiple_211(), multiply_successor(211n, 256n), {==})

def at_multiple_213() -> {B.nat64(Nat.mul(213n, 256n)) == Some{B.Number64{0, 54528}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(213n, 256n), Nat.mul(212n, 256n), B.Number64{0, 54272}, B.Number64{0, 54528}, at_256(), at_multiple_212(), multiply_successor(212n, 256n), {==})

def at_multiple_214() -> {B.nat64(Nat.mul(214n, 256n)) == Some{B.Number64{0, 54784}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(214n, 256n), Nat.mul(213n, 256n), B.Number64{0, 54528}, B.Number64{0, 54784}, at_256(), at_multiple_213(), multiply_successor(213n, 256n), {==})

def at_multiple_215() -> {B.nat64(Nat.mul(215n, 256n)) == Some{B.Number64{0, 55040}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(215n, 256n), Nat.mul(214n, 256n), B.Number64{0, 54784}, B.Number64{0, 55040}, at_256(), at_multiple_214(), multiply_successor(214n, 256n), {==})

def at_multiple_216() -> {B.nat64(Nat.mul(216n, 256n)) == Some{B.Number64{0, 55296}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(216n, 256n), Nat.mul(215n, 256n), B.Number64{0, 55040}, B.Number64{0, 55296}, at_256(), at_multiple_215(), multiply_successor(215n, 256n), {==})

def at_multiple_217() -> {B.nat64(Nat.mul(217n, 256n)) == Some{B.Number64{0, 55552}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(217n, 256n), Nat.mul(216n, 256n), B.Number64{0, 55296}, B.Number64{0, 55552}, at_256(), at_multiple_216(), multiply_successor(216n, 256n), {==})

def at_multiple_218() -> {B.nat64(Nat.mul(218n, 256n)) == Some{B.Number64{0, 55808}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(218n, 256n), Nat.mul(217n, 256n), B.Number64{0, 55552}, B.Number64{0, 55808}, at_256(), at_multiple_217(), multiply_successor(217n, 256n), {==})

def at_multiple_219() -> {B.nat64(Nat.mul(219n, 256n)) == Some{B.Number64{0, 56064}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(219n, 256n), Nat.mul(218n, 256n), B.Number64{0, 55808}, B.Number64{0, 56064}, at_256(), at_multiple_218(), multiply_successor(218n, 256n), {==})

def at_multiple_220() -> {B.nat64(Nat.mul(220n, 256n)) == Some{B.Number64{0, 56320}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(220n, 256n), Nat.mul(219n, 256n), B.Number64{0, 56064}, B.Number64{0, 56320}, at_256(), at_multiple_219(), multiply_successor(219n, 256n), {==})

def at_multiple_221() -> {B.nat64(Nat.mul(221n, 256n)) == Some{B.Number64{0, 56576}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(221n, 256n), Nat.mul(220n, 256n), B.Number64{0, 56320}, B.Number64{0, 56576}, at_256(), at_multiple_220(), multiply_successor(220n, 256n), {==})

def at_multiple_222() -> {B.nat64(Nat.mul(222n, 256n)) == Some{B.Number64{0, 56832}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(222n, 256n), Nat.mul(221n, 256n), B.Number64{0, 56576}, B.Number64{0, 56832}, at_256(), at_multiple_221(), multiply_successor(221n, 256n), {==})

def at_multiple_223() -> {B.nat64(Nat.mul(223n, 256n)) == Some{B.Number64{0, 57088}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(223n, 256n), Nat.mul(222n, 256n), B.Number64{0, 56832}, B.Number64{0, 57088}, at_256(), at_multiple_222(), multiply_successor(222n, 256n), {==})

def at_multiple_224() -> {B.nat64(Nat.mul(224n, 256n)) == Some{B.Number64{0, 57344}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(224n, 256n), Nat.mul(223n, 256n), B.Number64{0, 57088}, B.Number64{0, 57344}, at_256(), at_multiple_223(), multiply_successor(223n, 256n), {==})

def at_multiple_225() -> {B.nat64(Nat.mul(225n, 256n)) == Some{B.Number64{0, 57600}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(225n, 256n), Nat.mul(224n, 256n), B.Number64{0, 57344}, B.Number64{0, 57600}, at_256(), at_multiple_224(), multiply_successor(224n, 256n), {==})

def at_multiple_226() -> {B.nat64(Nat.mul(226n, 256n)) == Some{B.Number64{0, 57856}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(226n, 256n), Nat.mul(225n, 256n), B.Number64{0, 57600}, B.Number64{0, 57856}, at_256(), at_multiple_225(), multiply_successor(225n, 256n), {==})

def at_multiple_227() -> {B.nat64(Nat.mul(227n, 256n)) == Some{B.Number64{0, 58112}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(227n, 256n), Nat.mul(226n, 256n), B.Number64{0, 57856}, B.Number64{0, 58112}, at_256(), at_multiple_226(), multiply_successor(226n, 256n), {==})

def at_multiple_228() -> {B.nat64(Nat.mul(228n, 256n)) == Some{B.Number64{0, 58368}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(228n, 256n), Nat.mul(227n, 256n), B.Number64{0, 58112}, B.Number64{0, 58368}, at_256(), at_multiple_227(), multiply_successor(227n, 256n), {==})

def at_multiple_229() -> {B.nat64(Nat.mul(229n, 256n)) == Some{B.Number64{0, 58624}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(229n, 256n), Nat.mul(228n, 256n), B.Number64{0, 58368}, B.Number64{0, 58624}, at_256(), at_multiple_228(), multiply_successor(228n, 256n), {==})

def at_multiple_230() -> {B.nat64(Nat.mul(230n, 256n)) == Some{B.Number64{0, 58880}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(230n, 256n), Nat.mul(229n, 256n), B.Number64{0, 58624}, B.Number64{0, 58880}, at_256(), at_multiple_229(), multiply_successor(229n, 256n), {==})

def at_multiple_231() -> {B.nat64(Nat.mul(231n, 256n)) == Some{B.Number64{0, 59136}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(231n, 256n), Nat.mul(230n, 256n), B.Number64{0, 58880}, B.Number64{0, 59136}, at_256(), at_multiple_230(), multiply_successor(230n, 256n), {==})

def at_multiple_232() -> {B.nat64(Nat.mul(232n, 256n)) == Some{B.Number64{0, 59392}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(232n, 256n), Nat.mul(231n, 256n), B.Number64{0, 59136}, B.Number64{0, 59392}, at_256(), at_multiple_231(), multiply_successor(231n, 256n), {==})

def at_multiple_233() -> {B.nat64(Nat.mul(233n, 256n)) == Some{B.Number64{0, 59648}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(233n, 256n), Nat.mul(232n, 256n), B.Number64{0, 59392}, B.Number64{0, 59648}, at_256(), at_multiple_232(), multiply_successor(232n, 256n), {==})

def at_multiple_234() -> {B.nat64(Nat.mul(234n, 256n)) == Some{B.Number64{0, 59904}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(234n, 256n), Nat.mul(233n, 256n), B.Number64{0, 59648}, B.Number64{0, 59904}, at_256(), at_multiple_233(), multiply_successor(233n, 256n), {==})

def at_multiple_235() -> {B.nat64(Nat.mul(235n, 256n)) == Some{B.Number64{0, 60160}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(235n, 256n), Nat.mul(234n, 256n), B.Number64{0, 59904}, B.Number64{0, 60160}, at_256(), at_multiple_234(), multiply_successor(234n, 256n), {==})

def at_multiple_236() -> {B.nat64(Nat.mul(236n, 256n)) == Some{B.Number64{0, 60416}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(236n, 256n), Nat.mul(235n, 256n), B.Number64{0, 60160}, B.Number64{0, 60416}, at_256(), at_multiple_235(), multiply_successor(235n, 256n), {==})

def at_multiple_237() -> {B.nat64(Nat.mul(237n, 256n)) == Some{B.Number64{0, 60672}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(237n, 256n), Nat.mul(236n, 256n), B.Number64{0, 60416}, B.Number64{0, 60672}, at_256(), at_multiple_236(), multiply_successor(236n, 256n), {==})

def at_multiple_238() -> {B.nat64(Nat.mul(238n, 256n)) == Some{B.Number64{0, 60928}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(238n, 256n), Nat.mul(237n, 256n), B.Number64{0, 60672}, B.Number64{0, 60928}, at_256(), at_multiple_237(), multiply_successor(237n, 256n), {==})

def at_multiple_239() -> {B.nat64(Nat.mul(239n, 256n)) == Some{B.Number64{0, 61184}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(239n, 256n), Nat.mul(238n, 256n), B.Number64{0, 60928}, B.Number64{0, 61184}, at_256(), at_multiple_238(), multiply_successor(238n, 256n), {==})

def at_multiple_240() -> {B.nat64(Nat.mul(240n, 256n)) == Some{B.Number64{0, 61440}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(240n, 256n), Nat.mul(239n, 256n), B.Number64{0, 61184}, B.Number64{0, 61440}, at_256(), at_multiple_239(), multiply_successor(239n, 256n), {==})

def at_multiple_241() -> {B.nat64(Nat.mul(241n, 256n)) == Some{B.Number64{0, 61696}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(241n, 256n), Nat.mul(240n, 256n), B.Number64{0, 61440}, B.Number64{0, 61696}, at_256(), at_multiple_240(), multiply_successor(240n, 256n), {==})

def at_multiple_242() -> {B.nat64(Nat.mul(242n, 256n)) == Some{B.Number64{0, 61952}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(242n, 256n), Nat.mul(241n, 256n), B.Number64{0, 61696}, B.Number64{0, 61952}, at_256(), at_multiple_241(), multiply_successor(241n, 256n), {==})

def at_multiple_243() -> {B.nat64(Nat.mul(243n, 256n)) == Some{B.Number64{0, 62208}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(243n, 256n), Nat.mul(242n, 256n), B.Number64{0, 61952}, B.Number64{0, 62208}, at_256(), at_multiple_242(), multiply_successor(242n, 256n), {==})

def at_multiple_244() -> {B.nat64(Nat.mul(244n, 256n)) == Some{B.Number64{0, 62464}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(244n, 256n), Nat.mul(243n, 256n), B.Number64{0, 62208}, B.Number64{0, 62464}, at_256(), at_multiple_243(), multiply_successor(243n, 256n), {==})

def at_multiple_245() -> {B.nat64(Nat.mul(245n, 256n)) == Some{B.Number64{0, 62720}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(245n, 256n), Nat.mul(244n, 256n), B.Number64{0, 62464}, B.Number64{0, 62720}, at_256(), at_multiple_244(), multiply_successor(244n, 256n), {==})

def at_multiple_246() -> {B.nat64(Nat.mul(246n, 256n)) == Some{B.Number64{0, 62976}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(246n, 256n), Nat.mul(245n, 256n), B.Number64{0, 62720}, B.Number64{0, 62976}, at_256(), at_multiple_245(), multiply_successor(245n, 256n), {==})

def at_multiple_247() -> {B.nat64(Nat.mul(247n, 256n)) == Some{B.Number64{0, 63232}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(247n, 256n), Nat.mul(246n, 256n), B.Number64{0, 62976}, B.Number64{0, 63232}, at_256(), at_multiple_246(), multiply_successor(246n, 256n), {==})

def at_multiple_248() -> {B.nat64(Nat.mul(248n, 256n)) == Some{B.Number64{0, 63488}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(248n, 256n), Nat.mul(247n, 256n), B.Number64{0, 63232}, B.Number64{0, 63488}, at_256(), at_multiple_247(), multiply_successor(247n, 256n), {==})

def at_multiple_249() -> {B.nat64(Nat.mul(249n, 256n)) == Some{B.Number64{0, 63744}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(249n, 256n), Nat.mul(248n, 256n), B.Number64{0, 63488}, B.Number64{0, 63744}, at_256(), at_multiple_248(), multiply_successor(248n, 256n), {==})

def at_multiple_250() -> {B.nat64(Nat.mul(250n, 256n)) == Some{B.Number64{0, 64000}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(250n, 256n), Nat.mul(249n, 256n), B.Number64{0, 63744}, B.Number64{0, 64000}, at_256(), at_multiple_249(), multiply_successor(249n, 256n), {==})

def at_multiple_251() -> {B.nat64(Nat.mul(251n, 256n)) == Some{B.Number64{0, 64256}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(251n, 256n), Nat.mul(250n, 256n), B.Number64{0, 64000}, B.Number64{0, 64256}, at_256(), at_multiple_250(), multiply_successor(250n, 256n), {==})

def at_multiple_252() -> {B.nat64(Nat.mul(252n, 256n)) == Some{B.Number64{0, 64512}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(252n, 256n), Nat.mul(251n, 256n), B.Number64{0, 64256}, B.Number64{0, 64512}, at_256(), at_multiple_251(), multiply_successor(251n, 256n), {==})

def at_multiple_253() -> {B.nat64(Nat.mul(253n, 256n)) == Some{B.Number64{0, 64768}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(253n, 256n), Nat.mul(252n, 256n), B.Number64{0, 64512}, B.Number64{0, 64768}, at_256(), at_multiple_252(), multiply_successor(252n, 256n), {==})

def at_multiple_254() -> {B.nat64(Nat.mul(254n, 256n)) == Some{B.Number64{0, 65024}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(254n, 256n), Nat.mul(253n, 256n), B.Number64{0, 64768}, B.Number64{0, 65024}, at_256(), at_multiple_253(), multiply_successor(253n, 256n), {==})

def at_multiple_255() -> {B.nat64(Nat.mul(255n, 256n)) == Some{B.Number64{0, 65280}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(255n, 256n), Nat.mul(254n, 256n), B.Number64{0, 65024}, B.Number64{0, 65280}, at_256(), at_multiple_254(), multiply_successor(254n, 256n), {==})

def at_multiple_256() -> {B.nat64(Nat.mul(256n, 256n)) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, Nat.mul(256n, 256n), Nat.mul(255n, 256n), B.Number64{0, 65280}, B.Number64{0, 65536}, at_256(), at_multiple_255(), multiply_successor(255n, 256n), {==})
