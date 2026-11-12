import Base
import ./Data.bend as D
import ./Semantics.bend as S

# Q0 integer random walk; every arithmetic operation below is U32 modulo 2^32.
# One path starts at 1,000,000. The threshold is also 1,000,000.
type Stats is Data:
  Stats{sum: U32, max: U32, above: U32, paths: U32}

def terminal(n: Nat, +rng: U32, value: U32, +drift: U32, +vol: U32) -> U32:
  match n:
    case 0n: value
    case 1n+p:
      +next = (rng * 1664525 + 1013904223 : U32)
      terminal(p, next, (value + drift + U32.mod(U32.div(next, 65536), (vol * 2 + 1 : U32)) - vol : U32), drift, vol)

def one(value: U32) -> Stats:
  +value = value
  Stats{value, value, Bool.pick(U32, U32.is_lt(1000000, value), 1, 0), 1}

def merge(a: Stats, b: Stats) -> Stats:
  Stats{asum, +amax, ac, an} = a
  Stats{bsum, +bmax, bc, bn} = b
  Stats{(asum + bsum : U32), Bool.pick(U32, U32.is_lt(amax, bmax), bmax, amax),
    (ac + bc : U32), (an + bn : U32)}

# A balanced fork tree, with one independent flat tail loop at each leaf.
def simulate(+depth: Nat, +steps: Nat, +index: U32, +seed: U32, +drift: U32, +vol: U32) -> Stats:
  match depth:
    case 0n: one(terminal(steps, (seed + index * 747796405 : U32), 1000000, drift, vol))
    case 1n+p:
      a b = simulate(p, steps, (index * 2 : U32), seed, drift, vol)
        simulate(p, steps, (index * 2 + 1 : U32), seed, drift, vol)
      merge(a, b)

def value(stats: Stats) -> D.Value:
  Stats{s, m, a, n} = stats
  D.VRecord{"above", D.VInt{0, a}, D.VRecord{"max", D.VInt{0, m},
    D.VRecord{"paths", D.VInt{0, n}, D.VRecord{"sum", D.VInt{0, s}, D.VRecordEmpty{}}}}}

def fields(+id: String, stats: Stats) -> List<&2, D.Field>:
  Stats{s, m, a, n} = stats
  [D.Field{"above", D.VInt{0, a}}, D.Field{"id", D.VText{id}}, D.Field{"max", D.VInt{0, m}},
    D.Field{"paths", D.VInt{0, n}}, D.Field{"sum", D.VInt{0, s}}]

def save(+id: String, +stats: Stats) -> S.Action:
  S.Access{D.DefineRow{D.Application{"results"}, id, fields(id, stats)}, r => S.Finish{value(stats)}}

# Malformed/missing cells map to zero; all possible observations are covered.
def number(r: S.Return) -> U32:
  match r:
    case S.Datum{D.Cell{D.VInt{0, n}}}: n
    case _: 0

def ready(id: String, depth: Nat, steps: Nat, seed: U32, drift: U32, r: S.Return) -> S.Action:
  save(id, simulate!(depth, steps, 0, seed, U32.mod(drift, 65536), U32.mod(number(r), 32768)))

def drifted(+id: String, depth: Nat, steps: Nat, seed: U32, r: S.Return) -> S.Action:
  S.Access{D.ReadCell{D.Application{"scenarios"}, id, "volatility"}, ready(id, depth, steps, seed, number(r))}

def seeded(+id: String, depth: Nat, steps: Nat, r: S.Return) -> S.Action:
  S.Access{D.ReadCell{D.Application{"scenarios"}, id, "drift"}, drifted(id, depth, steps, number(r))}

def bounded(ok: Bool, +id: String, depth: U32, steps: U32) -> S.Action:
  match ok:
    case True{}:
      S.Access{D.ReadCell{D.Application{"scenarios"}, id, "seed"}, seeded(id, U32.to_nat(depth), U32.to_nat(steps))}
    case False{}: S.Refuse{D.VText{"invalid size"}}

def arguments(id: String, args: D.Value) -> S.Action:
  match args:
    case D.VList{D.VInt{0, +d}, D.VList{D.VInt{0, +n}, D.VListEmpty{}}}:
      bounded(Bool.and(U32.is_lt(d, 19), U32.is_lt(n, 65537)), id, d, n)
    case _: S.Refuse{D.VText{"expected [depth, steps]"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  arguments(id, args)

def program() -> S.Program:
  S.Program{start}
