# Checked fixed 65,536-byte u64 literal. Start at 16 and use the existing
# checked u64 addition theorem. Keep concrete additions at 256 or less so the
# production launcher and the default Node admission stack both check it.
# Explicit endpoint equalities avoid normalizing the accumulated unary Nat.
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

def at_512() -> {B.nat64(512n) == Some{B.Number64{0, 512}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 512n, 256n, B.Number64{0, 256}, B.Number64{0, 512}, at_256(), at_256(), {==}, {==})

def at_768() -> {B.nat64(768n) == Some{B.Number64{0, 768}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 768n, 512n, B.Number64{0, 512}, B.Number64{0, 768}, at_256(), at_512(), {==}, {==})

def at_1024() -> {B.nat64(1024n) == Some{B.Number64{0, 1024}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 1024n, 768n, B.Number64{0, 768}, B.Number64{0, 1024}, at_256(), at_768(), {==}, {==})

def at_1280() -> {B.nat64(1280n) == Some{B.Number64{0, 1280}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 1280n, 1024n, B.Number64{0, 1024}, B.Number64{0, 1280}, at_256(), at_1024(), {==}, {==})

def at_1536() -> {B.nat64(1536n) == Some{B.Number64{0, 1536}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 1536n, 1280n, B.Number64{0, 1280}, B.Number64{0, 1536}, at_256(), at_1280(), {==}, {==})

def at_1792() -> {B.nat64(1792n) == Some{B.Number64{0, 1792}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 1792n, 1536n, B.Number64{0, 1536}, B.Number64{0, 1792}, at_256(), at_1536(), {==}, {==})

def at_2048() -> {B.nat64(2048n) == Some{B.Number64{0, 2048}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 2048n, 1792n, B.Number64{0, 1792}, B.Number64{0, 2048}, at_256(), at_1792(), {==}, {==})

def at_2304() -> {B.nat64(2304n) == Some{B.Number64{0, 2304}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 2304n, 2048n, B.Number64{0, 2048}, B.Number64{0, 2304}, at_256(), at_2048(), {==}, {==})

def at_2560() -> {B.nat64(2560n) == Some{B.Number64{0, 2560}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 2560n, 2304n, B.Number64{0, 2304}, B.Number64{0, 2560}, at_256(), at_2304(), {==}, {==})

def at_2816() -> {B.nat64(2816n) == Some{B.Number64{0, 2816}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 2816n, 2560n, B.Number64{0, 2560}, B.Number64{0, 2816}, at_256(), at_2560(), {==}, {==})

def at_3072() -> {B.nat64(3072n) == Some{B.Number64{0, 3072}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 3072n, 2816n, B.Number64{0, 2816}, B.Number64{0, 3072}, at_256(), at_2816(), {==}, {==})

def at_3328() -> {B.nat64(3328n) == Some{B.Number64{0, 3328}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 3328n, 3072n, B.Number64{0, 3072}, B.Number64{0, 3328}, at_256(), at_3072(), {==}, {==})

def at_3584() -> {B.nat64(3584n) == Some{B.Number64{0, 3584}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 3584n, 3328n, B.Number64{0, 3328}, B.Number64{0, 3584}, at_256(), at_3328(), {==}, {==})

def at_3840() -> {B.nat64(3840n) == Some{B.Number64{0, 3840}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 3840n, 3584n, B.Number64{0, 3584}, B.Number64{0, 3840}, at_256(), at_3584(), {==}, {==})

def at_4096() -> {B.nat64(4096n) == Some{B.Number64{0, 4096}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 4096n, 3840n, B.Number64{0, 3840}, B.Number64{0, 4096}, at_256(), at_3840(), {==}, {==})

def at_4352() -> {B.nat64(4352n) == Some{B.Number64{0, 4352}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 4352n, 4096n, B.Number64{0, 4096}, B.Number64{0, 4352}, at_256(), at_4096(), {==}, {==})

def at_4608() -> {B.nat64(4608n) == Some{B.Number64{0, 4608}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 4608n, 4352n, B.Number64{0, 4352}, B.Number64{0, 4608}, at_256(), at_4352(), {==}, {==})

def at_4864() -> {B.nat64(4864n) == Some{B.Number64{0, 4864}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 4864n, 4608n, B.Number64{0, 4608}, B.Number64{0, 4864}, at_256(), at_4608(), {==}, {==})

def at_5120() -> {B.nat64(5120n) == Some{B.Number64{0, 5120}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 5120n, 4864n, B.Number64{0, 4864}, B.Number64{0, 5120}, at_256(), at_4864(), {==}, {==})

def at_5376() -> {B.nat64(5376n) == Some{B.Number64{0, 5376}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 5376n, 5120n, B.Number64{0, 5120}, B.Number64{0, 5376}, at_256(), at_5120(), {==}, {==})

def at_5632() -> {B.nat64(5632n) == Some{B.Number64{0, 5632}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 5632n, 5376n, B.Number64{0, 5376}, B.Number64{0, 5632}, at_256(), at_5376(), {==}, {==})

def at_5888() -> {B.nat64(5888n) == Some{B.Number64{0, 5888}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 5888n, 5632n, B.Number64{0, 5632}, B.Number64{0, 5888}, at_256(), at_5632(), {==}, {==})

def at_6144() -> {B.nat64(6144n) == Some{B.Number64{0, 6144}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 6144n, 5888n, B.Number64{0, 5888}, B.Number64{0, 6144}, at_256(), at_5888(), {==}, {==})

def at_6400() -> {B.nat64(6400n) == Some{B.Number64{0, 6400}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 6400n, 6144n, B.Number64{0, 6144}, B.Number64{0, 6400}, at_256(), at_6144(), {==}, {==})

def at_6656() -> {B.nat64(6656n) == Some{B.Number64{0, 6656}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 6656n, 6400n, B.Number64{0, 6400}, B.Number64{0, 6656}, at_256(), at_6400(), {==}, {==})

def at_6912() -> {B.nat64(6912n) == Some{B.Number64{0, 6912}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 6912n, 6656n, B.Number64{0, 6656}, B.Number64{0, 6912}, at_256(), at_6656(), {==}, {==})

def at_7168() -> {B.nat64(7168n) == Some{B.Number64{0, 7168}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 7168n, 6912n, B.Number64{0, 6912}, B.Number64{0, 7168}, at_256(), at_6912(), {==}, {==})

def at_7424() -> {B.nat64(7424n) == Some{B.Number64{0, 7424}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 7424n, 7168n, B.Number64{0, 7168}, B.Number64{0, 7424}, at_256(), at_7168(), {==}, {==})

def at_7680() -> {B.nat64(7680n) == Some{B.Number64{0, 7680}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 7680n, 7424n, B.Number64{0, 7424}, B.Number64{0, 7680}, at_256(), at_7424(), {==}, {==})

def at_7936() -> {B.nat64(7936n) == Some{B.Number64{0, 7936}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 7936n, 7680n, B.Number64{0, 7680}, B.Number64{0, 7936}, at_256(), at_7680(), {==}, {==})

def at_8192() -> {B.nat64(8192n) == Some{B.Number64{0, 8192}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 8192n, 7936n, B.Number64{0, 7936}, B.Number64{0, 8192}, at_256(), at_7936(), {==}, {==})

def at_8448() -> {B.nat64(8448n) == Some{B.Number64{0, 8448}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 8448n, 8192n, B.Number64{0, 8192}, B.Number64{0, 8448}, at_256(), at_8192(), {==}, {==})

def at_8704() -> {B.nat64(8704n) == Some{B.Number64{0, 8704}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 8704n, 8448n, B.Number64{0, 8448}, B.Number64{0, 8704}, at_256(), at_8448(), {==}, {==})

def at_8960() -> {B.nat64(8960n) == Some{B.Number64{0, 8960}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 8960n, 8704n, B.Number64{0, 8704}, B.Number64{0, 8960}, at_256(), at_8704(), {==}, {==})

def at_9216() -> {B.nat64(9216n) == Some{B.Number64{0, 9216}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 9216n, 8960n, B.Number64{0, 8960}, B.Number64{0, 9216}, at_256(), at_8960(), {==}, {==})

def at_9472() -> {B.nat64(9472n) == Some{B.Number64{0, 9472}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 9472n, 9216n, B.Number64{0, 9216}, B.Number64{0, 9472}, at_256(), at_9216(), {==}, {==})

def at_9728() -> {B.nat64(9728n) == Some{B.Number64{0, 9728}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 9728n, 9472n, B.Number64{0, 9472}, B.Number64{0, 9728}, at_256(), at_9472(), {==}, {==})

def at_9984() -> {B.nat64(9984n) == Some{B.Number64{0, 9984}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 9984n, 9728n, B.Number64{0, 9728}, B.Number64{0, 9984}, at_256(), at_9728(), {==}, {==})

def at_10240() -> {B.nat64(10240n) == Some{B.Number64{0, 10240}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 10240n, 9984n, B.Number64{0, 9984}, B.Number64{0, 10240}, at_256(), at_9984(), {==}, {==})

def at_10496() -> {B.nat64(10496n) == Some{B.Number64{0, 10496}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 10496n, 10240n, B.Number64{0, 10240}, B.Number64{0, 10496}, at_256(), at_10240(), {==}, {==})

def at_10752() -> {B.nat64(10752n) == Some{B.Number64{0, 10752}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 10752n, 10496n, B.Number64{0, 10496}, B.Number64{0, 10752}, at_256(), at_10496(), {==}, {==})

def at_11008() -> {B.nat64(11008n) == Some{B.Number64{0, 11008}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 11008n, 10752n, B.Number64{0, 10752}, B.Number64{0, 11008}, at_256(), at_10752(), {==}, {==})

def at_11264() -> {B.nat64(11264n) == Some{B.Number64{0, 11264}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 11264n, 11008n, B.Number64{0, 11008}, B.Number64{0, 11264}, at_256(), at_11008(), {==}, {==})

def at_11520() -> {B.nat64(11520n) == Some{B.Number64{0, 11520}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 11520n, 11264n, B.Number64{0, 11264}, B.Number64{0, 11520}, at_256(), at_11264(), {==}, {==})

def at_11776() -> {B.nat64(11776n) == Some{B.Number64{0, 11776}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 11776n, 11520n, B.Number64{0, 11520}, B.Number64{0, 11776}, at_256(), at_11520(), {==}, {==})

def at_12032() -> {B.nat64(12032n) == Some{B.Number64{0, 12032}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 12032n, 11776n, B.Number64{0, 11776}, B.Number64{0, 12032}, at_256(), at_11776(), {==}, {==})

def at_12288() -> {B.nat64(12288n) == Some{B.Number64{0, 12288}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 12288n, 12032n, B.Number64{0, 12032}, B.Number64{0, 12288}, at_256(), at_12032(), {==}, {==})

def at_12544() -> {B.nat64(12544n) == Some{B.Number64{0, 12544}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 12544n, 12288n, B.Number64{0, 12288}, B.Number64{0, 12544}, at_256(), at_12288(), {==}, {==})

def at_12800() -> {B.nat64(12800n) == Some{B.Number64{0, 12800}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 12800n, 12544n, B.Number64{0, 12544}, B.Number64{0, 12800}, at_256(), at_12544(), {==}, {==})

def at_13056() -> {B.nat64(13056n) == Some{B.Number64{0, 13056}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 13056n, 12800n, B.Number64{0, 12800}, B.Number64{0, 13056}, at_256(), at_12800(), {==}, {==})

def at_13312() -> {B.nat64(13312n) == Some{B.Number64{0, 13312}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 13312n, 13056n, B.Number64{0, 13056}, B.Number64{0, 13312}, at_256(), at_13056(), {==}, {==})

def at_13568() -> {B.nat64(13568n) == Some{B.Number64{0, 13568}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 13568n, 13312n, B.Number64{0, 13312}, B.Number64{0, 13568}, at_256(), at_13312(), {==}, {==})

def at_13824() -> {B.nat64(13824n) == Some{B.Number64{0, 13824}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 13824n, 13568n, B.Number64{0, 13568}, B.Number64{0, 13824}, at_256(), at_13568(), {==}, {==})

def at_14080() -> {B.nat64(14080n) == Some{B.Number64{0, 14080}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 14080n, 13824n, B.Number64{0, 13824}, B.Number64{0, 14080}, at_256(), at_13824(), {==}, {==})

def at_14336() -> {B.nat64(14336n) == Some{B.Number64{0, 14336}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 14336n, 14080n, B.Number64{0, 14080}, B.Number64{0, 14336}, at_256(), at_14080(), {==}, {==})

def at_14592() -> {B.nat64(14592n) == Some{B.Number64{0, 14592}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 14592n, 14336n, B.Number64{0, 14336}, B.Number64{0, 14592}, at_256(), at_14336(), {==}, {==})

def at_14848() -> {B.nat64(14848n) == Some{B.Number64{0, 14848}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 14848n, 14592n, B.Number64{0, 14592}, B.Number64{0, 14848}, at_256(), at_14592(), {==}, {==})

def at_15104() -> {B.nat64(15104n) == Some{B.Number64{0, 15104}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 15104n, 14848n, B.Number64{0, 14848}, B.Number64{0, 15104}, at_256(), at_14848(), {==}, {==})

def at_15360() -> {B.nat64(15360n) == Some{B.Number64{0, 15360}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 15360n, 15104n, B.Number64{0, 15104}, B.Number64{0, 15360}, at_256(), at_15104(), {==}, {==})

def at_15616() -> {B.nat64(15616n) == Some{B.Number64{0, 15616}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 15616n, 15360n, B.Number64{0, 15360}, B.Number64{0, 15616}, at_256(), at_15360(), {==}, {==})

def at_15872() -> {B.nat64(15872n) == Some{B.Number64{0, 15872}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 15872n, 15616n, B.Number64{0, 15616}, B.Number64{0, 15872}, at_256(), at_15616(), {==}, {==})

def at_16128() -> {B.nat64(16128n) == Some{B.Number64{0, 16128}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 16128n, 15872n, B.Number64{0, 15872}, B.Number64{0, 16128}, at_256(), at_15872(), {==}, {==})

def at_16384() -> {B.nat64(16384n) == Some{B.Number64{0, 16384}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 16384n, 16128n, B.Number64{0, 16128}, B.Number64{0, 16384}, at_256(), at_16128(), {==}, {==})

def at_16640() -> {B.nat64(16640n) == Some{B.Number64{0, 16640}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 16640n, 16384n, B.Number64{0, 16384}, B.Number64{0, 16640}, at_256(), at_16384(), {==}, {==})

def at_16896() -> {B.nat64(16896n) == Some{B.Number64{0, 16896}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 16896n, 16640n, B.Number64{0, 16640}, B.Number64{0, 16896}, at_256(), at_16640(), {==}, {==})

def at_17152() -> {B.nat64(17152n) == Some{B.Number64{0, 17152}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 17152n, 16896n, B.Number64{0, 16896}, B.Number64{0, 17152}, at_256(), at_16896(), {==}, {==})

def at_17408() -> {B.nat64(17408n) == Some{B.Number64{0, 17408}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 17408n, 17152n, B.Number64{0, 17152}, B.Number64{0, 17408}, at_256(), at_17152(), {==}, {==})

def at_17664() -> {B.nat64(17664n) == Some{B.Number64{0, 17664}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 17664n, 17408n, B.Number64{0, 17408}, B.Number64{0, 17664}, at_256(), at_17408(), {==}, {==})

def at_17920() -> {B.nat64(17920n) == Some{B.Number64{0, 17920}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 17920n, 17664n, B.Number64{0, 17664}, B.Number64{0, 17920}, at_256(), at_17664(), {==}, {==})

def at_18176() -> {B.nat64(18176n) == Some{B.Number64{0, 18176}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 18176n, 17920n, B.Number64{0, 17920}, B.Number64{0, 18176}, at_256(), at_17920(), {==}, {==})

def at_18432() -> {B.nat64(18432n) == Some{B.Number64{0, 18432}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 18432n, 18176n, B.Number64{0, 18176}, B.Number64{0, 18432}, at_256(), at_18176(), {==}, {==})

def at_18688() -> {B.nat64(18688n) == Some{B.Number64{0, 18688}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 18688n, 18432n, B.Number64{0, 18432}, B.Number64{0, 18688}, at_256(), at_18432(), {==}, {==})

def at_18944() -> {B.nat64(18944n) == Some{B.Number64{0, 18944}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 18944n, 18688n, B.Number64{0, 18688}, B.Number64{0, 18944}, at_256(), at_18688(), {==}, {==})

def at_19200() -> {B.nat64(19200n) == Some{B.Number64{0, 19200}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 19200n, 18944n, B.Number64{0, 18944}, B.Number64{0, 19200}, at_256(), at_18944(), {==}, {==})

def at_19456() -> {B.nat64(19456n) == Some{B.Number64{0, 19456}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 19456n, 19200n, B.Number64{0, 19200}, B.Number64{0, 19456}, at_256(), at_19200(), {==}, {==})

def at_19712() -> {B.nat64(19712n) == Some{B.Number64{0, 19712}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 19712n, 19456n, B.Number64{0, 19456}, B.Number64{0, 19712}, at_256(), at_19456(), {==}, {==})

def at_19968() -> {B.nat64(19968n) == Some{B.Number64{0, 19968}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 19968n, 19712n, B.Number64{0, 19712}, B.Number64{0, 19968}, at_256(), at_19712(), {==}, {==})

def at_20224() -> {B.nat64(20224n) == Some{B.Number64{0, 20224}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 20224n, 19968n, B.Number64{0, 19968}, B.Number64{0, 20224}, at_256(), at_19968(), {==}, {==})

def at_20480() -> {B.nat64(20480n) == Some{B.Number64{0, 20480}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 20480n, 20224n, B.Number64{0, 20224}, B.Number64{0, 20480}, at_256(), at_20224(), {==}, {==})

def at_20736() -> {B.nat64(20736n) == Some{B.Number64{0, 20736}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 20736n, 20480n, B.Number64{0, 20480}, B.Number64{0, 20736}, at_256(), at_20480(), {==}, {==})

def at_20992() -> {B.nat64(20992n) == Some{B.Number64{0, 20992}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 20992n, 20736n, B.Number64{0, 20736}, B.Number64{0, 20992}, at_256(), at_20736(), {==}, {==})

def at_21248() -> {B.nat64(21248n) == Some{B.Number64{0, 21248}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 21248n, 20992n, B.Number64{0, 20992}, B.Number64{0, 21248}, at_256(), at_20992(), {==}, {==})

def at_21504() -> {B.nat64(21504n) == Some{B.Number64{0, 21504}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 21504n, 21248n, B.Number64{0, 21248}, B.Number64{0, 21504}, at_256(), at_21248(), {==}, {==})

def at_21760() -> {B.nat64(21760n) == Some{B.Number64{0, 21760}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 21760n, 21504n, B.Number64{0, 21504}, B.Number64{0, 21760}, at_256(), at_21504(), {==}, {==})

def at_22016() -> {B.nat64(22016n) == Some{B.Number64{0, 22016}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 22016n, 21760n, B.Number64{0, 21760}, B.Number64{0, 22016}, at_256(), at_21760(), {==}, {==})

def at_22272() -> {B.nat64(22272n) == Some{B.Number64{0, 22272}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 22272n, 22016n, B.Number64{0, 22016}, B.Number64{0, 22272}, at_256(), at_22016(), {==}, {==})

def at_22528() -> {B.nat64(22528n) == Some{B.Number64{0, 22528}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 22528n, 22272n, B.Number64{0, 22272}, B.Number64{0, 22528}, at_256(), at_22272(), {==}, {==})

def at_22784() -> {B.nat64(22784n) == Some{B.Number64{0, 22784}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 22784n, 22528n, B.Number64{0, 22528}, B.Number64{0, 22784}, at_256(), at_22528(), {==}, {==})

def at_23040() -> {B.nat64(23040n) == Some{B.Number64{0, 23040}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 23040n, 22784n, B.Number64{0, 22784}, B.Number64{0, 23040}, at_256(), at_22784(), {==}, {==})

def at_23296() -> {B.nat64(23296n) == Some{B.Number64{0, 23296}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 23296n, 23040n, B.Number64{0, 23040}, B.Number64{0, 23296}, at_256(), at_23040(), {==}, {==})

def at_23552() -> {B.nat64(23552n) == Some{B.Number64{0, 23552}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 23552n, 23296n, B.Number64{0, 23296}, B.Number64{0, 23552}, at_256(), at_23296(), {==}, {==})

def at_23808() -> {B.nat64(23808n) == Some{B.Number64{0, 23808}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 23808n, 23552n, B.Number64{0, 23552}, B.Number64{0, 23808}, at_256(), at_23552(), {==}, {==})

def at_24064() -> {B.nat64(24064n) == Some{B.Number64{0, 24064}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 24064n, 23808n, B.Number64{0, 23808}, B.Number64{0, 24064}, at_256(), at_23808(), {==}, {==})

def at_24320() -> {B.nat64(24320n) == Some{B.Number64{0, 24320}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 24320n, 24064n, B.Number64{0, 24064}, B.Number64{0, 24320}, at_256(), at_24064(), {==}, {==})

def at_24576() -> {B.nat64(24576n) == Some{B.Number64{0, 24576}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 24576n, 24320n, B.Number64{0, 24320}, B.Number64{0, 24576}, at_256(), at_24320(), {==}, {==})

def at_24832() -> {B.nat64(24832n) == Some{B.Number64{0, 24832}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 24832n, 24576n, B.Number64{0, 24576}, B.Number64{0, 24832}, at_256(), at_24576(), {==}, {==})

def at_25088() -> {B.nat64(25088n) == Some{B.Number64{0, 25088}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 25088n, 24832n, B.Number64{0, 24832}, B.Number64{0, 25088}, at_256(), at_24832(), {==}, {==})

def at_25344() -> {B.nat64(25344n) == Some{B.Number64{0, 25344}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 25344n, 25088n, B.Number64{0, 25088}, B.Number64{0, 25344}, at_256(), at_25088(), {==}, {==})

def at_25600() -> {B.nat64(25600n) == Some{B.Number64{0, 25600}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 25600n, 25344n, B.Number64{0, 25344}, B.Number64{0, 25600}, at_256(), at_25344(), {==}, {==})

def at_25856() -> {B.nat64(25856n) == Some{B.Number64{0, 25856}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 25856n, 25600n, B.Number64{0, 25600}, B.Number64{0, 25856}, at_256(), at_25600(), {==}, {==})

def at_26112() -> {B.nat64(26112n) == Some{B.Number64{0, 26112}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 26112n, 25856n, B.Number64{0, 25856}, B.Number64{0, 26112}, at_256(), at_25856(), {==}, {==})

def at_26368() -> {B.nat64(26368n) == Some{B.Number64{0, 26368}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 26368n, 26112n, B.Number64{0, 26112}, B.Number64{0, 26368}, at_256(), at_26112(), {==}, {==})

def at_26624() -> {B.nat64(26624n) == Some{B.Number64{0, 26624}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 26624n, 26368n, B.Number64{0, 26368}, B.Number64{0, 26624}, at_256(), at_26368(), {==}, {==})

def at_26880() -> {B.nat64(26880n) == Some{B.Number64{0, 26880}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 26880n, 26624n, B.Number64{0, 26624}, B.Number64{0, 26880}, at_256(), at_26624(), {==}, {==})

def at_27136() -> {B.nat64(27136n) == Some{B.Number64{0, 27136}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 27136n, 26880n, B.Number64{0, 26880}, B.Number64{0, 27136}, at_256(), at_26880(), {==}, {==})

def at_27392() -> {B.nat64(27392n) == Some{B.Number64{0, 27392}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 27392n, 27136n, B.Number64{0, 27136}, B.Number64{0, 27392}, at_256(), at_27136(), {==}, {==})

def at_27648() -> {B.nat64(27648n) == Some{B.Number64{0, 27648}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 27648n, 27392n, B.Number64{0, 27392}, B.Number64{0, 27648}, at_256(), at_27392(), {==}, {==})

def at_27904() -> {B.nat64(27904n) == Some{B.Number64{0, 27904}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 27904n, 27648n, B.Number64{0, 27648}, B.Number64{0, 27904}, at_256(), at_27648(), {==}, {==})

def at_28160() -> {B.nat64(28160n) == Some{B.Number64{0, 28160}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 28160n, 27904n, B.Number64{0, 27904}, B.Number64{0, 28160}, at_256(), at_27904(), {==}, {==})

def at_28416() -> {B.nat64(28416n) == Some{B.Number64{0, 28416}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 28416n, 28160n, B.Number64{0, 28160}, B.Number64{0, 28416}, at_256(), at_28160(), {==}, {==})

def at_28672() -> {B.nat64(28672n) == Some{B.Number64{0, 28672}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 28672n, 28416n, B.Number64{0, 28416}, B.Number64{0, 28672}, at_256(), at_28416(), {==}, {==})

def at_28928() -> {B.nat64(28928n) == Some{B.Number64{0, 28928}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 28928n, 28672n, B.Number64{0, 28672}, B.Number64{0, 28928}, at_256(), at_28672(), {==}, {==})

def at_29184() -> {B.nat64(29184n) == Some{B.Number64{0, 29184}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 29184n, 28928n, B.Number64{0, 28928}, B.Number64{0, 29184}, at_256(), at_28928(), {==}, {==})

def at_29440() -> {B.nat64(29440n) == Some{B.Number64{0, 29440}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 29440n, 29184n, B.Number64{0, 29184}, B.Number64{0, 29440}, at_256(), at_29184(), {==}, {==})

def at_29696() -> {B.nat64(29696n) == Some{B.Number64{0, 29696}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 29696n, 29440n, B.Number64{0, 29440}, B.Number64{0, 29696}, at_256(), at_29440(), {==}, {==})

def at_29952() -> {B.nat64(29952n) == Some{B.Number64{0, 29952}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 29952n, 29696n, B.Number64{0, 29696}, B.Number64{0, 29952}, at_256(), at_29696(), {==}, {==})

def at_30208() -> {B.nat64(30208n) == Some{B.Number64{0, 30208}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 30208n, 29952n, B.Number64{0, 29952}, B.Number64{0, 30208}, at_256(), at_29952(), {==}, {==})

def at_30464() -> {B.nat64(30464n) == Some{B.Number64{0, 30464}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 30464n, 30208n, B.Number64{0, 30208}, B.Number64{0, 30464}, at_256(), at_30208(), {==}, {==})

def at_30720() -> {B.nat64(30720n) == Some{B.Number64{0, 30720}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 30720n, 30464n, B.Number64{0, 30464}, B.Number64{0, 30720}, at_256(), at_30464(), {==}, {==})

def at_30976() -> {B.nat64(30976n) == Some{B.Number64{0, 30976}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 30976n, 30720n, B.Number64{0, 30720}, B.Number64{0, 30976}, at_256(), at_30720(), {==}, {==})

def at_31232() -> {B.nat64(31232n) == Some{B.Number64{0, 31232}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 31232n, 30976n, B.Number64{0, 30976}, B.Number64{0, 31232}, at_256(), at_30976(), {==}, {==})

def at_31488() -> {B.nat64(31488n) == Some{B.Number64{0, 31488}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 31488n, 31232n, B.Number64{0, 31232}, B.Number64{0, 31488}, at_256(), at_31232(), {==}, {==})

def at_31744() -> {B.nat64(31744n) == Some{B.Number64{0, 31744}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 31744n, 31488n, B.Number64{0, 31488}, B.Number64{0, 31744}, at_256(), at_31488(), {==}, {==})

def at_32000() -> {B.nat64(32000n) == Some{B.Number64{0, 32000}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 32000n, 31744n, B.Number64{0, 31744}, B.Number64{0, 32000}, at_256(), at_31744(), {==}, {==})

def at_32256() -> {B.nat64(32256n) == Some{B.Number64{0, 32256}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 32256n, 32000n, B.Number64{0, 32000}, B.Number64{0, 32256}, at_256(), at_32000(), {==}, {==})

def at_32512() -> {B.nat64(32512n) == Some{B.Number64{0, 32512}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 32512n, 32256n, B.Number64{0, 32256}, B.Number64{0, 32512}, at_256(), at_32256(), {==}, {==})

def at_32768() -> {B.nat64(32768n) == Some{B.Number64{0, 32768}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 32768n, 32512n, B.Number64{0, 32512}, B.Number64{0, 32768}, at_256(), at_32512(), {==}, {==})

def at_33024() -> {B.nat64(33024n) == Some{B.Number64{0, 33024}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 33024n, 32768n, B.Number64{0, 32768}, B.Number64{0, 33024}, at_256(), at_32768(), {==}, {==})

def at_33280() -> {B.nat64(33280n) == Some{B.Number64{0, 33280}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 33280n, 33024n, B.Number64{0, 33024}, B.Number64{0, 33280}, at_256(), at_33024(), {==}, {==})

def at_33536() -> {B.nat64(33536n) == Some{B.Number64{0, 33536}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 33536n, 33280n, B.Number64{0, 33280}, B.Number64{0, 33536}, at_256(), at_33280(), {==}, {==})

def at_33792() -> {B.nat64(33792n) == Some{B.Number64{0, 33792}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 33792n, 33536n, B.Number64{0, 33536}, B.Number64{0, 33792}, at_256(), at_33536(), {==}, {==})

def at_34048() -> {B.nat64(34048n) == Some{B.Number64{0, 34048}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 34048n, 33792n, B.Number64{0, 33792}, B.Number64{0, 34048}, at_256(), at_33792(), {==}, {==})

def at_34304() -> {B.nat64(34304n) == Some{B.Number64{0, 34304}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 34304n, 34048n, B.Number64{0, 34048}, B.Number64{0, 34304}, at_256(), at_34048(), {==}, {==})

def at_34560() -> {B.nat64(34560n) == Some{B.Number64{0, 34560}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 34560n, 34304n, B.Number64{0, 34304}, B.Number64{0, 34560}, at_256(), at_34304(), {==}, {==})

def at_34816() -> {B.nat64(34816n) == Some{B.Number64{0, 34816}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 34816n, 34560n, B.Number64{0, 34560}, B.Number64{0, 34816}, at_256(), at_34560(), {==}, {==})

def at_35072() -> {B.nat64(35072n) == Some{B.Number64{0, 35072}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 35072n, 34816n, B.Number64{0, 34816}, B.Number64{0, 35072}, at_256(), at_34816(), {==}, {==})

def at_35328() -> {B.nat64(35328n) == Some{B.Number64{0, 35328}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 35328n, 35072n, B.Number64{0, 35072}, B.Number64{0, 35328}, at_256(), at_35072(), {==}, {==})

def at_35584() -> {B.nat64(35584n) == Some{B.Number64{0, 35584}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 35584n, 35328n, B.Number64{0, 35328}, B.Number64{0, 35584}, at_256(), at_35328(), {==}, {==})

def at_35840() -> {B.nat64(35840n) == Some{B.Number64{0, 35840}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 35840n, 35584n, B.Number64{0, 35584}, B.Number64{0, 35840}, at_256(), at_35584(), {==}, {==})

def at_36096() -> {B.nat64(36096n) == Some{B.Number64{0, 36096}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 36096n, 35840n, B.Number64{0, 35840}, B.Number64{0, 36096}, at_256(), at_35840(), {==}, {==})

def at_36352() -> {B.nat64(36352n) == Some{B.Number64{0, 36352}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 36352n, 36096n, B.Number64{0, 36096}, B.Number64{0, 36352}, at_256(), at_36096(), {==}, {==})

def at_36608() -> {B.nat64(36608n) == Some{B.Number64{0, 36608}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 36608n, 36352n, B.Number64{0, 36352}, B.Number64{0, 36608}, at_256(), at_36352(), {==}, {==})

def at_36864() -> {B.nat64(36864n) == Some{B.Number64{0, 36864}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 36864n, 36608n, B.Number64{0, 36608}, B.Number64{0, 36864}, at_256(), at_36608(), {==}, {==})

def at_37120() -> {B.nat64(37120n) == Some{B.Number64{0, 37120}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 37120n, 36864n, B.Number64{0, 36864}, B.Number64{0, 37120}, at_256(), at_36864(), {==}, {==})

def at_37376() -> {B.nat64(37376n) == Some{B.Number64{0, 37376}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 37376n, 37120n, B.Number64{0, 37120}, B.Number64{0, 37376}, at_256(), at_37120(), {==}, {==})

def at_37632() -> {B.nat64(37632n) == Some{B.Number64{0, 37632}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 37632n, 37376n, B.Number64{0, 37376}, B.Number64{0, 37632}, at_256(), at_37376(), {==}, {==})

def at_37888() -> {B.nat64(37888n) == Some{B.Number64{0, 37888}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 37888n, 37632n, B.Number64{0, 37632}, B.Number64{0, 37888}, at_256(), at_37632(), {==}, {==})

def at_38144() -> {B.nat64(38144n) == Some{B.Number64{0, 38144}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 38144n, 37888n, B.Number64{0, 37888}, B.Number64{0, 38144}, at_256(), at_37888(), {==}, {==})

def at_38400() -> {B.nat64(38400n) == Some{B.Number64{0, 38400}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 38400n, 38144n, B.Number64{0, 38144}, B.Number64{0, 38400}, at_256(), at_38144(), {==}, {==})

def at_38656() -> {B.nat64(38656n) == Some{B.Number64{0, 38656}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 38656n, 38400n, B.Number64{0, 38400}, B.Number64{0, 38656}, at_256(), at_38400(), {==}, {==})

def at_38912() -> {B.nat64(38912n) == Some{B.Number64{0, 38912}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 38912n, 38656n, B.Number64{0, 38656}, B.Number64{0, 38912}, at_256(), at_38656(), {==}, {==})

def at_39168() -> {B.nat64(39168n) == Some{B.Number64{0, 39168}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 39168n, 38912n, B.Number64{0, 38912}, B.Number64{0, 39168}, at_256(), at_38912(), {==}, {==})

def at_39424() -> {B.nat64(39424n) == Some{B.Number64{0, 39424}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 39424n, 39168n, B.Number64{0, 39168}, B.Number64{0, 39424}, at_256(), at_39168(), {==}, {==})

def at_39680() -> {B.nat64(39680n) == Some{B.Number64{0, 39680}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 39680n, 39424n, B.Number64{0, 39424}, B.Number64{0, 39680}, at_256(), at_39424(), {==}, {==})

def at_39936() -> {B.nat64(39936n) == Some{B.Number64{0, 39936}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 39936n, 39680n, B.Number64{0, 39680}, B.Number64{0, 39936}, at_256(), at_39680(), {==}, {==})

def at_40192() -> {B.nat64(40192n) == Some{B.Number64{0, 40192}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 40192n, 39936n, B.Number64{0, 39936}, B.Number64{0, 40192}, at_256(), at_39936(), {==}, {==})

def at_40448() -> {B.nat64(40448n) == Some{B.Number64{0, 40448}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 40448n, 40192n, B.Number64{0, 40192}, B.Number64{0, 40448}, at_256(), at_40192(), {==}, {==})

def at_40704() -> {B.nat64(40704n) == Some{B.Number64{0, 40704}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 40704n, 40448n, B.Number64{0, 40448}, B.Number64{0, 40704}, at_256(), at_40448(), {==}, {==})

def at_40960() -> {B.nat64(40960n) == Some{B.Number64{0, 40960}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 40960n, 40704n, B.Number64{0, 40704}, B.Number64{0, 40960}, at_256(), at_40704(), {==}, {==})

def at_41216() -> {B.nat64(41216n) == Some{B.Number64{0, 41216}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 41216n, 40960n, B.Number64{0, 40960}, B.Number64{0, 41216}, at_256(), at_40960(), {==}, {==})

def at_41472() -> {B.nat64(41472n) == Some{B.Number64{0, 41472}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 41472n, 41216n, B.Number64{0, 41216}, B.Number64{0, 41472}, at_256(), at_41216(), {==}, {==})

def at_41728() -> {B.nat64(41728n) == Some{B.Number64{0, 41728}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 41728n, 41472n, B.Number64{0, 41472}, B.Number64{0, 41728}, at_256(), at_41472(), {==}, {==})

def at_41984() -> {B.nat64(41984n) == Some{B.Number64{0, 41984}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 41984n, 41728n, B.Number64{0, 41728}, B.Number64{0, 41984}, at_256(), at_41728(), {==}, {==})

def at_42240() -> {B.nat64(42240n) == Some{B.Number64{0, 42240}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 42240n, 41984n, B.Number64{0, 41984}, B.Number64{0, 42240}, at_256(), at_41984(), {==}, {==})

def at_42496() -> {B.nat64(42496n) == Some{B.Number64{0, 42496}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 42496n, 42240n, B.Number64{0, 42240}, B.Number64{0, 42496}, at_256(), at_42240(), {==}, {==})

def at_42752() -> {B.nat64(42752n) == Some{B.Number64{0, 42752}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 42752n, 42496n, B.Number64{0, 42496}, B.Number64{0, 42752}, at_256(), at_42496(), {==}, {==})

def at_43008() -> {B.nat64(43008n) == Some{B.Number64{0, 43008}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 43008n, 42752n, B.Number64{0, 42752}, B.Number64{0, 43008}, at_256(), at_42752(), {==}, {==})

def at_43264() -> {B.nat64(43264n) == Some{B.Number64{0, 43264}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 43264n, 43008n, B.Number64{0, 43008}, B.Number64{0, 43264}, at_256(), at_43008(), {==}, {==})

def at_43520() -> {B.nat64(43520n) == Some{B.Number64{0, 43520}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 43520n, 43264n, B.Number64{0, 43264}, B.Number64{0, 43520}, at_256(), at_43264(), {==}, {==})

def at_43776() -> {B.nat64(43776n) == Some{B.Number64{0, 43776}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 43776n, 43520n, B.Number64{0, 43520}, B.Number64{0, 43776}, at_256(), at_43520(), {==}, {==})

def at_44032() -> {B.nat64(44032n) == Some{B.Number64{0, 44032}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 44032n, 43776n, B.Number64{0, 43776}, B.Number64{0, 44032}, at_256(), at_43776(), {==}, {==})

def at_44288() -> {B.nat64(44288n) == Some{B.Number64{0, 44288}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 44288n, 44032n, B.Number64{0, 44032}, B.Number64{0, 44288}, at_256(), at_44032(), {==}, {==})

def at_44544() -> {B.nat64(44544n) == Some{B.Number64{0, 44544}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 44544n, 44288n, B.Number64{0, 44288}, B.Number64{0, 44544}, at_256(), at_44288(), {==}, {==})

def at_44800() -> {B.nat64(44800n) == Some{B.Number64{0, 44800}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 44800n, 44544n, B.Number64{0, 44544}, B.Number64{0, 44800}, at_256(), at_44544(), {==}, {==})

def at_45056() -> {B.nat64(45056n) == Some{B.Number64{0, 45056}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 45056n, 44800n, B.Number64{0, 44800}, B.Number64{0, 45056}, at_256(), at_44800(), {==}, {==})

def at_45312() -> {B.nat64(45312n) == Some{B.Number64{0, 45312}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 45312n, 45056n, B.Number64{0, 45056}, B.Number64{0, 45312}, at_256(), at_45056(), {==}, {==})

def at_45568() -> {B.nat64(45568n) == Some{B.Number64{0, 45568}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 45568n, 45312n, B.Number64{0, 45312}, B.Number64{0, 45568}, at_256(), at_45312(), {==}, {==})

def at_45824() -> {B.nat64(45824n) == Some{B.Number64{0, 45824}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 45824n, 45568n, B.Number64{0, 45568}, B.Number64{0, 45824}, at_256(), at_45568(), {==}, {==})

def at_46080() -> {B.nat64(46080n) == Some{B.Number64{0, 46080}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 46080n, 45824n, B.Number64{0, 45824}, B.Number64{0, 46080}, at_256(), at_45824(), {==}, {==})

def at_46336() -> {B.nat64(46336n) == Some{B.Number64{0, 46336}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 46336n, 46080n, B.Number64{0, 46080}, B.Number64{0, 46336}, at_256(), at_46080(), {==}, {==})

def at_46592() -> {B.nat64(46592n) == Some{B.Number64{0, 46592}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 46592n, 46336n, B.Number64{0, 46336}, B.Number64{0, 46592}, at_256(), at_46336(), {==}, {==})

def at_46848() -> {B.nat64(46848n) == Some{B.Number64{0, 46848}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 46848n, 46592n, B.Number64{0, 46592}, B.Number64{0, 46848}, at_256(), at_46592(), {==}, {==})

def at_47104() -> {B.nat64(47104n) == Some{B.Number64{0, 47104}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 47104n, 46848n, B.Number64{0, 46848}, B.Number64{0, 47104}, at_256(), at_46848(), {==}, {==})

def at_47360() -> {B.nat64(47360n) == Some{B.Number64{0, 47360}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 47360n, 47104n, B.Number64{0, 47104}, B.Number64{0, 47360}, at_256(), at_47104(), {==}, {==})

def at_47616() -> {B.nat64(47616n) == Some{B.Number64{0, 47616}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 47616n, 47360n, B.Number64{0, 47360}, B.Number64{0, 47616}, at_256(), at_47360(), {==}, {==})

def at_47872() -> {B.nat64(47872n) == Some{B.Number64{0, 47872}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 47872n, 47616n, B.Number64{0, 47616}, B.Number64{0, 47872}, at_256(), at_47616(), {==}, {==})

def at_48128() -> {B.nat64(48128n) == Some{B.Number64{0, 48128}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 48128n, 47872n, B.Number64{0, 47872}, B.Number64{0, 48128}, at_256(), at_47872(), {==}, {==})

def at_48384() -> {B.nat64(48384n) == Some{B.Number64{0, 48384}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 48384n, 48128n, B.Number64{0, 48128}, B.Number64{0, 48384}, at_256(), at_48128(), {==}, {==})

def at_48640() -> {B.nat64(48640n) == Some{B.Number64{0, 48640}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 48640n, 48384n, B.Number64{0, 48384}, B.Number64{0, 48640}, at_256(), at_48384(), {==}, {==})

def at_48896() -> {B.nat64(48896n) == Some{B.Number64{0, 48896}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 48896n, 48640n, B.Number64{0, 48640}, B.Number64{0, 48896}, at_256(), at_48640(), {==}, {==})

def at_49152() -> {B.nat64(49152n) == Some{B.Number64{0, 49152}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 49152n, 48896n, B.Number64{0, 48896}, B.Number64{0, 49152}, at_256(), at_48896(), {==}, {==})

def at_49408() -> {B.nat64(49408n) == Some{B.Number64{0, 49408}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 49408n, 49152n, B.Number64{0, 49152}, B.Number64{0, 49408}, at_256(), at_49152(), {==}, {==})

def at_49664() -> {B.nat64(49664n) == Some{B.Number64{0, 49664}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 49664n, 49408n, B.Number64{0, 49408}, B.Number64{0, 49664}, at_256(), at_49408(), {==}, {==})

def at_49920() -> {B.nat64(49920n) == Some{B.Number64{0, 49920}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 49920n, 49664n, B.Number64{0, 49664}, B.Number64{0, 49920}, at_256(), at_49664(), {==}, {==})

def at_50176() -> {B.nat64(50176n) == Some{B.Number64{0, 50176}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 50176n, 49920n, B.Number64{0, 49920}, B.Number64{0, 50176}, at_256(), at_49920(), {==}, {==})

def at_50432() -> {B.nat64(50432n) == Some{B.Number64{0, 50432}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 50432n, 50176n, B.Number64{0, 50176}, B.Number64{0, 50432}, at_256(), at_50176(), {==}, {==})

def at_50688() -> {B.nat64(50688n) == Some{B.Number64{0, 50688}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 50688n, 50432n, B.Number64{0, 50432}, B.Number64{0, 50688}, at_256(), at_50432(), {==}, {==})

def at_50944() -> {B.nat64(50944n) == Some{B.Number64{0, 50944}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 50944n, 50688n, B.Number64{0, 50688}, B.Number64{0, 50944}, at_256(), at_50688(), {==}, {==})

def at_51200() -> {B.nat64(51200n) == Some{B.Number64{0, 51200}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 51200n, 50944n, B.Number64{0, 50944}, B.Number64{0, 51200}, at_256(), at_50944(), {==}, {==})

def at_51456() -> {B.nat64(51456n) == Some{B.Number64{0, 51456}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 51456n, 51200n, B.Number64{0, 51200}, B.Number64{0, 51456}, at_256(), at_51200(), {==}, {==})

def at_51712() -> {B.nat64(51712n) == Some{B.Number64{0, 51712}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 51712n, 51456n, B.Number64{0, 51456}, B.Number64{0, 51712}, at_256(), at_51456(), {==}, {==})

def at_51968() -> {B.nat64(51968n) == Some{B.Number64{0, 51968}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 51968n, 51712n, B.Number64{0, 51712}, B.Number64{0, 51968}, at_256(), at_51712(), {==}, {==})

def at_52224() -> {B.nat64(52224n) == Some{B.Number64{0, 52224}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 52224n, 51968n, B.Number64{0, 51968}, B.Number64{0, 52224}, at_256(), at_51968(), {==}, {==})

def at_52480() -> {B.nat64(52480n) == Some{B.Number64{0, 52480}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 52480n, 52224n, B.Number64{0, 52224}, B.Number64{0, 52480}, at_256(), at_52224(), {==}, {==})

def at_52736() -> {B.nat64(52736n) == Some{B.Number64{0, 52736}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 52736n, 52480n, B.Number64{0, 52480}, B.Number64{0, 52736}, at_256(), at_52480(), {==}, {==})

def at_52992() -> {B.nat64(52992n) == Some{B.Number64{0, 52992}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 52992n, 52736n, B.Number64{0, 52736}, B.Number64{0, 52992}, at_256(), at_52736(), {==}, {==})

def at_53248() -> {B.nat64(53248n) == Some{B.Number64{0, 53248}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 53248n, 52992n, B.Number64{0, 52992}, B.Number64{0, 53248}, at_256(), at_52992(), {==}, {==})

def at_53504() -> {B.nat64(53504n) == Some{B.Number64{0, 53504}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 53504n, 53248n, B.Number64{0, 53248}, B.Number64{0, 53504}, at_256(), at_53248(), {==}, {==})

def at_53760() -> {B.nat64(53760n) == Some{B.Number64{0, 53760}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 53760n, 53504n, B.Number64{0, 53504}, B.Number64{0, 53760}, at_256(), at_53504(), {==}, {==})

def at_54016() -> {B.nat64(54016n) == Some{B.Number64{0, 54016}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 54016n, 53760n, B.Number64{0, 53760}, B.Number64{0, 54016}, at_256(), at_53760(), {==}, {==})

def at_54272() -> {B.nat64(54272n) == Some{B.Number64{0, 54272}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 54272n, 54016n, B.Number64{0, 54016}, B.Number64{0, 54272}, at_256(), at_54016(), {==}, {==})

def at_54528() -> {B.nat64(54528n) == Some{B.Number64{0, 54528}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 54528n, 54272n, B.Number64{0, 54272}, B.Number64{0, 54528}, at_256(), at_54272(), {==}, {==})

def at_54784() -> {B.nat64(54784n) == Some{B.Number64{0, 54784}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 54784n, 54528n, B.Number64{0, 54528}, B.Number64{0, 54784}, at_256(), at_54528(), {==}, {==})

def at_55040() -> {B.nat64(55040n) == Some{B.Number64{0, 55040}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 55040n, 54784n, B.Number64{0, 54784}, B.Number64{0, 55040}, at_256(), at_54784(), {==}, {==})

def at_55296() -> {B.nat64(55296n) == Some{B.Number64{0, 55296}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 55296n, 55040n, B.Number64{0, 55040}, B.Number64{0, 55296}, at_256(), at_55040(), {==}, {==})

def at_55552() -> {B.nat64(55552n) == Some{B.Number64{0, 55552}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 55552n, 55296n, B.Number64{0, 55296}, B.Number64{0, 55552}, at_256(), at_55296(), {==}, {==})

def at_55808() -> {B.nat64(55808n) == Some{B.Number64{0, 55808}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 55808n, 55552n, B.Number64{0, 55552}, B.Number64{0, 55808}, at_256(), at_55552(), {==}, {==})

def at_56064() -> {B.nat64(56064n) == Some{B.Number64{0, 56064}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 56064n, 55808n, B.Number64{0, 55808}, B.Number64{0, 56064}, at_256(), at_55808(), {==}, {==})

def at_56320() -> {B.nat64(56320n) == Some{B.Number64{0, 56320}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 56320n, 56064n, B.Number64{0, 56064}, B.Number64{0, 56320}, at_256(), at_56064(), {==}, {==})

def at_56576() -> {B.nat64(56576n) == Some{B.Number64{0, 56576}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 56576n, 56320n, B.Number64{0, 56320}, B.Number64{0, 56576}, at_256(), at_56320(), {==}, {==})

def at_56832() -> {B.nat64(56832n) == Some{B.Number64{0, 56832}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 56832n, 56576n, B.Number64{0, 56576}, B.Number64{0, 56832}, at_256(), at_56576(), {==}, {==})

def at_57088() -> {B.nat64(57088n) == Some{B.Number64{0, 57088}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 57088n, 56832n, B.Number64{0, 56832}, B.Number64{0, 57088}, at_256(), at_56832(), {==}, {==})

def at_57344() -> {B.nat64(57344n) == Some{B.Number64{0, 57344}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 57344n, 57088n, B.Number64{0, 57088}, B.Number64{0, 57344}, at_256(), at_57088(), {==}, {==})

def at_57600() -> {B.nat64(57600n) == Some{B.Number64{0, 57600}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 57600n, 57344n, B.Number64{0, 57344}, B.Number64{0, 57600}, at_256(), at_57344(), {==}, {==})

def at_57856() -> {B.nat64(57856n) == Some{B.Number64{0, 57856}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 57856n, 57600n, B.Number64{0, 57600}, B.Number64{0, 57856}, at_256(), at_57600(), {==}, {==})

def at_58112() -> {B.nat64(58112n) == Some{B.Number64{0, 58112}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 58112n, 57856n, B.Number64{0, 57856}, B.Number64{0, 58112}, at_256(), at_57856(), {==}, {==})

def at_58368() -> {B.nat64(58368n) == Some{B.Number64{0, 58368}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 58368n, 58112n, B.Number64{0, 58112}, B.Number64{0, 58368}, at_256(), at_58112(), {==}, {==})

def at_58624() -> {B.nat64(58624n) == Some{B.Number64{0, 58624}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 58624n, 58368n, B.Number64{0, 58368}, B.Number64{0, 58624}, at_256(), at_58368(), {==}, {==})

def at_58880() -> {B.nat64(58880n) == Some{B.Number64{0, 58880}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 58880n, 58624n, B.Number64{0, 58624}, B.Number64{0, 58880}, at_256(), at_58624(), {==}, {==})

def at_59136() -> {B.nat64(59136n) == Some{B.Number64{0, 59136}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 59136n, 58880n, B.Number64{0, 58880}, B.Number64{0, 59136}, at_256(), at_58880(), {==}, {==})

def at_59392() -> {B.nat64(59392n) == Some{B.Number64{0, 59392}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 59392n, 59136n, B.Number64{0, 59136}, B.Number64{0, 59392}, at_256(), at_59136(), {==}, {==})

def at_59648() -> {B.nat64(59648n) == Some{B.Number64{0, 59648}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 59648n, 59392n, B.Number64{0, 59392}, B.Number64{0, 59648}, at_256(), at_59392(), {==}, {==})

def at_59904() -> {B.nat64(59904n) == Some{B.Number64{0, 59904}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 59904n, 59648n, B.Number64{0, 59648}, B.Number64{0, 59904}, at_256(), at_59648(), {==}, {==})

def at_60160() -> {B.nat64(60160n) == Some{B.Number64{0, 60160}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 60160n, 59904n, B.Number64{0, 59904}, B.Number64{0, 60160}, at_256(), at_59904(), {==}, {==})

def at_60416() -> {B.nat64(60416n) == Some{B.Number64{0, 60416}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 60416n, 60160n, B.Number64{0, 60160}, B.Number64{0, 60416}, at_256(), at_60160(), {==}, {==})

def at_60672() -> {B.nat64(60672n) == Some{B.Number64{0, 60672}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 60672n, 60416n, B.Number64{0, 60416}, B.Number64{0, 60672}, at_256(), at_60416(), {==}, {==})

def at_60928() -> {B.nat64(60928n) == Some{B.Number64{0, 60928}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 60928n, 60672n, B.Number64{0, 60672}, B.Number64{0, 60928}, at_256(), at_60672(), {==}, {==})

def at_61184() -> {B.nat64(61184n) == Some{B.Number64{0, 61184}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 61184n, 60928n, B.Number64{0, 60928}, B.Number64{0, 61184}, at_256(), at_60928(), {==}, {==})

def at_61440() -> {B.nat64(61440n) == Some{B.Number64{0, 61440}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 61440n, 61184n, B.Number64{0, 61184}, B.Number64{0, 61440}, at_256(), at_61184(), {==}, {==})

def at_61696() -> {B.nat64(61696n) == Some{B.Number64{0, 61696}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 61696n, 61440n, B.Number64{0, 61440}, B.Number64{0, 61696}, at_256(), at_61440(), {==}, {==})

def at_61952() -> {B.nat64(61952n) == Some{B.Number64{0, 61952}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 61952n, 61696n, B.Number64{0, 61696}, B.Number64{0, 61952}, at_256(), at_61696(), {==}, {==})

def at_62208() -> {B.nat64(62208n) == Some{B.Number64{0, 62208}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 62208n, 61952n, B.Number64{0, 61952}, B.Number64{0, 62208}, at_256(), at_61952(), {==}, {==})

def at_62464() -> {B.nat64(62464n) == Some{B.Number64{0, 62464}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 62464n, 62208n, B.Number64{0, 62208}, B.Number64{0, 62464}, at_256(), at_62208(), {==}, {==})

def at_62720() -> {B.nat64(62720n) == Some{B.Number64{0, 62720}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 62720n, 62464n, B.Number64{0, 62464}, B.Number64{0, 62720}, at_256(), at_62464(), {==}, {==})

def at_62976() -> {B.nat64(62976n) == Some{B.Number64{0, 62976}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 62976n, 62720n, B.Number64{0, 62720}, B.Number64{0, 62976}, at_256(), at_62720(), {==}, {==})

def at_63232() -> {B.nat64(63232n) == Some{B.Number64{0, 63232}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 63232n, 62976n, B.Number64{0, 62976}, B.Number64{0, 63232}, at_256(), at_62976(), {==}, {==})

def at_63488() -> {B.nat64(63488n) == Some{B.Number64{0, 63488}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 63488n, 63232n, B.Number64{0, 63232}, B.Number64{0, 63488}, at_256(), at_63232(), {==}, {==})

def at_63744() -> {B.nat64(63744n) == Some{B.Number64{0, 63744}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 63744n, 63488n, B.Number64{0, 63488}, B.Number64{0, 63744}, at_256(), at_63488(), {==}, {==})

def at_64000() -> {B.nat64(64000n) == Some{B.Number64{0, 64000}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 64000n, 63744n, B.Number64{0, 63744}, B.Number64{0, 64000}, at_256(), at_63744(), {==}, {==})

def at_64256() -> {B.nat64(64256n) == Some{B.Number64{0, 64256}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 64256n, 64000n, B.Number64{0, 64000}, B.Number64{0, 64256}, at_256(), at_64000(), {==}, {==})

def at_64512() -> {B.nat64(64512n) == Some{B.Number64{0, 64512}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 64512n, 64256n, B.Number64{0, 64256}, B.Number64{0, 64512}, at_256(), at_64256(), {==}, {==})

def at_64768() -> {B.nat64(64768n) == Some{B.Number64{0, 64768}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 64768n, 64512n, B.Number64{0, 64512}, B.Number64{0, 64768}, at_256(), at_64512(), {==}, {==})

def at_65024() -> {B.nat64(65024n) == Some{B.Number64{0, 65024}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 65024n, 64768n, B.Number64{0, 64768}, B.Number64{0, 65024}, at_256(), at_64768(), {==}, {==})

def at_65280() -> {B.nat64(65280n) == Some{B.Number64{0, 65280}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 65280n, 65024n, B.Number64{0, 65024}, B.Number64{0, 65280}, at_256(), at_65024(), {==}, {==})

def at_65536() -> {B.nat64(65536n) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}:
  checked_block(256n, B.Number64{0, 256}, 65536n, 65280n, B.Number64{0, 65280}, B.Number64{0, 65536}, at_256(), at_65280(), {==}, {==})
