# Checked fixed 65,536-byte u64 literal. Start at 16 and use the existing
# checked u64 addition theorem. Numeral comparisons unfold at most 4,096
# successors; no full unary nat64(65536) normalization or extra axiom/fuel.
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

def at_32() -> {B.nat64(32n) == Some{B.Number64{0, 32}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(32n),
    C.sum64(B.Number64{0, 16}, B.Number64{0, 16}), Some{B.Number64{0, 32}},
    block(16n, B.Number64{0, 16}, 32n, 16n, B.Number64{0, 16}, at_16(), {==}, at_16()),
    {==})

def at_64() -> {B.nat64(64n) == Some{B.Number64{0, 64}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(64n),
    C.sum64(B.Number64{0, 32}, B.Number64{0, 32}), Some{B.Number64{0, 64}},
    block(32n, B.Number64{0, 32}, 64n, 32n, B.Number64{0, 32}, at_32(), {==}, at_32()),
    {==})

def at_128() -> {B.nat64(128n) == Some{B.Number64{0, 128}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(128n),
    C.sum64(B.Number64{0, 64}, B.Number64{0, 64}), Some{B.Number64{0, 128}},
    block(64n, B.Number64{0, 64}, 128n, 64n, B.Number64{0, 64}, at_64(), {==}, at_64()),
    {==})

def at_256() -> {B.nat64(256n) == Some{B.Number64{0, 256}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(256n),
    C.sum64(B.Number64{0, 128}, B.Number64{0, 128}), Some{B.Number64{0, 256}},
    block(128n, B.Number64{0, 128}, 256n, 128n, B.Number64{0, 128}, at_128(), {==}, at_128()),
    {==})

def at_512() -> {B.nat64(512n) == Some{B.Number64{0, 512}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(512n),
    C.sum64(B.Number64{0, 256}, B.Number64{0, 256}), Some{B.Number64{0, 512}},
    block(256n, B.Number64{0, 256}, 512n, 256n, B.Number64{0, 256}, at_256(), {==}, at_256()),
    {==})

def at_1024() -> {B.nat64(1024n) == Some{B.Number64{0, 1024}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(1024n),
    C.sum64(B.Number64{0, 512}, B.Number64{0, 512}), Some{B.Number64{0, 1024}},
    block(512n, B.Number64{0, 512}, 1024n, 512n, B.Number64{0, 512}, at_512(), {==}, at_512()),
    {==})

def at_2048() -> {B.nat64(2048n) == Some{B.Number64{0, 2048}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(2048n),
    C.sum64(B.Number64{0, 1024}, B.Number64{0, 1024}), Some{B.Number64{0, 2048}},
    block(1024n, B.Number64{0, 1024}, 2048n, 1024n, B.Number64{0, 1024}, at_1024(), {==}, at_1024()),
    {==})

def at_4096() -> {B.nat64(4096n) == Some{B.Number64{0, 4096}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(4096n),
    C.sum64(B.Number64{0, 2048}, B.Number64{0, 2048}), Some{B.Number64{0, 4096}},
    block(2048n, B.Number64{0, 2048}, 4096n, 2048n, B.Number64{0, 2048}, at_2048(), {==}, at_2048()),
    {==})

def at_8192() -> {B.nat64(8192n) == Some{B.Number64{0, 8192}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(8192n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 4096}), Some{B.Number64{0, 8192}},
    block(4096n, B.Number64{0, 4096}, 8192n, 4096n, B.Number64{0, 4096}, at_4096(), {==}, at_4096()),
    {==})

def at_12288() -> {B.nat64(12288n) == Some{B.Number64{0, 12288}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(12288n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 8192}), Some{B.Number64{0, 12288}},
    block(4096n, B.Number64{0, 4096}, 12288n, 8192n, B.Number64{0, 8192}, at_4096(), {==}, at_8192()),
    {==})

def at_16384() -> {B.nat64(16384n) == Some{B.Number64{0, 16384}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(16384n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 12288}), Some{B.Number64{0, 16384}},
    block(4096n, B.Number64{0, 4096}, 16384n, 12288n, B.Number64{0, 12288}, at_4096(), {==}, at_12288()),
    {==})

def at_20480() -> {B.nat64(20480n) == Some{B.Number64{0, 20480}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(20480n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 16384}), Some{B.Number64{0, 20480}},
    block(4096n, B.Number64{0, 4096}, 20480n, 16384n, B.Number64{0, 16384}, at_4096(), {==}, at_16384()),
    {==})

def at_24576() -> {B.nat64(24576n) == Some{B.Number64{0, 24576}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(24576n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 20480}), Some{B.Number64{0, 24576}},
    block(4096n, B.Number64{0, 4096}, 24576n, 20480n, B.Number64{0, 20480}, at_4096(), {==}, at_20480()),
    {==})

def at_28672() -> {B.nat64(28672n) == Some{B.Number64{0, 28672}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(28672n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 24576}), Some{B.Number64{0, 28672}},
    block(4096n, B.Number64{0, 4096}, 28672n, 24576n, B.Number64{0, 24576}, at_4096(), {==}, at_24576()),
    {==})

def at_32768() -> {B.nat64(32768n) == Some{B.Number64{0, 32768}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(32768n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 28672}), Some{B.Number64{0, 32768}},
    block(4096n, B.Number64{0, 4096}, 32768n, 28672n, B.Number64{0, 28672}, at_4096(), {==}, at_28672()),
    {==})

def at_36864() -> {B.nat64(36864n) == Some{B.Number64{0, 36864}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(36864n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 32768}), Some{B.Number64{0, 36864}},
    block(4096n, B.Number64{0, 4096}, 36864n, 32768n, B.Number64{0, 32768}, at_4096(), {==}, at_32768()),
    {==})

def at_40960() -> {B.nat64(40960n) == Some{B.Number64{0, 40960}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(40960n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 36864}), Some{B.Number64{0, 40960}},
    block(4096n, B.Number64{0, 4096}, 40960n, 36864n, B.Number64{0, 36864}, at_4096(), {==}, at_36864()),
    {==})

def at_45056() -> {B.nat64(45056n) == Some{B.Number64{0, 45056}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(45056n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 40960}), Some{B.Number64{0, 45056}},
    block(4096n, B.Number64{0, 4096}, 45056n, 40960n, B.Number64{0, 40960}, at_4096(), {==}, at_40960()),
    {==})

def at_49152() -> {B.nat64(49152n) == Some{B.Number64{0, 49152}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(49152n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 45056}), Some{B.Number64{0, 49152}},
    block(4096n, B.Number64{0, 4096}, 49152n, 45056n, B.Number64{0, 45056}, at_4096(), {==}, at_45056()),
    {==})

def at_53248() -> {B.nat64(53248n) == Some{B.Number64{0, 53248}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(53248n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 49152}), Some{B.Number64{0, 53248}},
    block(4096n, B.Number64{0, 4096}, 53248n, 49152n, B.Number64{0, 49152}, at_4096(), {==}, at_49152()),
    {==})

def at_57344() -> {B.nat64(57344n) == Some{B.Number64{0, 57344}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(57344n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 53248}), Some{B.Number64{0, 57344}},
    block(4096n, B.Number64{0, 4096}, 57344n, 53248n, B.Number64{0, 53248}, at_4096(), {==}, at_53248()),
    {==})

def at_61440() -> {B.nat64(61440n) == Some{B.Number64{0, 61440}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(61440n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 57344}), Some{B.Number64{0, 61440}},
    block(4096n, B.Number64{0, 4096}, 61440n, 57344n, B.Number64{0, 57344}, at_4096(), {==}, at_57344()),
    {==})

def at_65536() -> {B.nat64(65536n) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}:
  Equal.trans(Maybe<&2, B.Number64>, B.nat64(65536n),
    C.sum64(B.Number64{0, 4096}, B.Number64{0, 61440}), Some{B.Number64{0, 65536}},
    block(4096n, B.Number64{0, 4096}, 65536n, 61440n, B.Number64{0, 61440}, at_4096(), {==}, at_61440()),
    {==})
