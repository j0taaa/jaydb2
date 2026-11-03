# Research API: queries of ONE fixed route; does not prove route validity.
import Base
import ../contract/Protocol.bend as P
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Interface.bend as I
import ../contract/Resources.bend as X
import ../contract/Logic.bend as L
import ./Foundations.bend as F

# Programs and configuration are not copied in frames.
type Frame is Data:
  Configured{}
  InitialAccepts{}
  Initialized{state: D.State}
  InitialRefused{status: S.Status}
  Encoded{value: D.Value, bytes: Maybe<&2, List<&2, U32>>}
  Decoded{bytes: List<&2, U32>, value: Maybe<&2, D.Value>}
  Stored{state: D.State, bytes: List<&2, U32>, abstraction: D.State}
  Checked{position: Nat, count: Nat}
  Constructed{position: Nat, count: Nat}
  Read{before: Nat, count: Nat, declared: Nat}
  Received{request: P.Request}
  Authenticated{request: P.Request, context: Maybe<&2, D.Context>}
  Accepts{request: P.Request, context: D.Context}
  Rejected{request: P.Request, context: D.Context}
  Started{request: P.Request, context: D.Context}
  Evaluated{request: P.Request, context: D.Context, execution_trace: S.Trace}
  Operated{schema: D.Schema, state: D.State, operation: D.Operation, result: D.ResultOp}
  Prepared{response: S.Response, bytes: List<&2, U32>}
  Published{state: D.State}
  Visible{state: D.State}
  Failed{stage: X.Stage, identifier: String, fatal: Bool}
  Completed{response: S.Response, state: D.State, closes: Bool}
  Delivered{bytes: List<&2, U32>}
  Interrupted{prefix: List<&2, U32>}
  Closed{}
  Next{previous: D.State, initial: D.State}
  Inspection{description: String}
  Effect{description: String}

# Canonical frame fact, indexed by public configuration and program.
def fact_of_frame(c: S.Configuration, p: S.Program, q: Frame) -> I.Fact:
  match q:
    case Configured{}: I.ConfigurationInUse{c}
    case InitialAccepts{}: I.ProofInitialAccepts{}
    case Initialized{s}: I.InstanceStarted{s}
    case InitialRefused{s}: I.InitializationRefused{s}
    case Encoded{v, bs}: I.Encoded{v, bs}
    case Decoded{bs, v}: I.Decoded{bs, v}
    case Stored{s, bs, abstr}: I.Stored{s, bs, abstr}
    case Checked{pos, n}: I.CheckedLength{pos, n}
    case Constructed{pos, n}: I.AllocatedField{pos, n}
    case Read{before, n, declared}: I.ReadBody{before, n, declared}
    case Received{r}: I.ReceivedRequest{r}
    case Authenticated{r, ctx}: I.Authenticated{r, ctx}
    case Accepts{r, ctx}: I.CertificateAccepted{r, ctx, p}
    case Rejected{r, ctx}: I.CertificateRejected{r, ctx}
    case Started{r, ctx}: I.ProgramStarted{r, ctx, p}
    case Evaluated{r, ctx, execution_trace}: I.Evaluated{r, ctx, p, execution_trace}
    case Operated{e, s, o, r}: I.Operated{e, s, o, r}
    case Prepared{r, bs}: I.Prepared{r, bs}
    case Published{s}: I.Published{s}
    case Visible{s}: I.StateVisible{s}
    case Failed{stage, id, fatal}: I.FailedEnvironment{stage, id, fatal}
    case Completed{r, s, closes}: I.Concluded{r, s, closes}
    case Delivered{bs}: I.DeliveredEverything{bs}
    case Interrupted{bs}: I.DeliveryInterrupted{bs}
    case Closed{}: I.ClosedChannel{}
    case Next{before, after}: I.NextCall{before, after}
    case Inspection{description}: I.InspectionNotModeled{description}
    case Effect{description}: I.EffectNotModeled{description}

def rel_fact(-c: S.Configuration, -p: S.Program, q: Frame, -f: I.Fact) -> Type:
  {f == fact_of_frame(c, p, q) : I.Fact}

def query(xs: List<&2, Frame>, n: Nat) -> Maybe<&2, Frame>:
  match xs n:
    case Nil{} _: None{}
    case Con{h, t} 0n: Some{h}
    case Con{h, t} 1n+k: query(t, k)

def selected(-c: S.Configuration, -p: S.Program, q: Maybe<&2, Frame>, -f: I.Fact) -> Type:
  match q:
    case None{}: Empty
    case Some{frame}: rel_fact(c, p, frame, f)

def observes(-c: S.Configuration, -p: S.Program, xs: List<&2, Frame>, t: Nat, -f: I.Fact) -> Type:
  selected(c, p, query(xs, t), f)

law head:
  for -h: Frame
  for -t: List<&2, Frame>
  {query(Con{h, t}, 0n) == Some{h} : Maybe<&2, Frame>}
def head(h, t):
  {==}

law tail:
  for -h: Frame
  for -t: List<&2, Frame>
  for -n: Nat
  {query(Con{h, t}, 1n+n) == query(t, n) : Maybe<&2, Frame>}
def tail(h, t, n):
  {==}

law query_unique:
  for -xs: List<&2, Frame>
  for -t: Nat
  for +a: Frame
  for -b: Frame
  for exists: {query(xs, t) == Some{a} : Maybe<&2, Frame>}
  for hb: {query(xs, t) == Some{b} : Maybe<&2, Frame>}
  {a == b : Frame}
def query_unique(xs, t, a, b, exists, hb):
  F.some_injective(Frame, a, b,
    Equal.trans(Maybe<&2, Frame>, Some{a}, query(xs, t), Some{b},
      Equal.sym(Maybe<&2, Frame>, query(xs, t), Some{a}, exists), hb))

# Concatenates subtraces; indices shift by the actual frame count.
def concatenate(xs: List<&2, Frame>, ys: List<&2, Frame>) -> List<&2, Frame>:
  match xs:
    case Nil{}: ys
    case Con{h, t}: Con{h, concatenate(t, ys)}

def size(xs: List<&2, Frame>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{h, t}: 1n+size(t)

law query_after_prefix:
  for xs: List<&2, Frame>
  for -ys: List<&2, Frame>
  for -n: Nat
  {query(concatenate(xs, ys), Nat.add(size(xs), n)) == query(ys, n) : Maybe<&2, Frame>}
def query_after_prefix(xs, ys, n):
  match xs:
    case Nil{}: {==}
    case Con{h, t}: query_after_prefix(t, ys, n)

law query_inside_prefix:
  for xs: List<&2, Frame>
  for -ys: List<&2, Frame>
  for n: Nat
  for inside: {Nat.is_lt(n, size(xs)) == True{} : Bool}
  {query(concatenate(xs, ys), n) == query(xs, n) : Maybe<&2, Frame>}
def query_inside_prefix(xs, ys, n, inside):
  match xs n:
    case Nil{} 0n:
      F.absurd_boolean({query(concatenate(Nil{}, ys), 0n) == query(Nil{}, 0n) : Maybe<&2, Frame>}, inside)
    case Nil{} 1n+k:
      F.absurd_boolean({query(concatenate(Nil{}, ys), 1n+k) == query(Nil{}, 1n+k) : Maybe<&2, Frame>}, inside)
    case Con{h, t} 0n: {==}
    case Con{h, t} 1n+k: query_inside_prefix(t, ys, k, inside)

# An existing query stays equal when frames are appended.
# Induction avoids computing a limit and duplicating query equality.
law query_prefix:
  for +xs: List<&2, Frame>
  for -ys: List<&2, Frame>
  for +t: Nat
  for -q: Frame
  for present: {query(xs, t) == Some{q} : Maybe<&2, Frame>}
  {query(concatenate(xs, ys), t) == Some{q} : Maybe<&2, Frame>}
def query_prefix(xs, ys, t, q, present):
  match xs t:
    case Nil{} _:
      L.ex_false({query(concatenate(Nil{}, ys), t) == Some{q} : Maybe<&2, Frame>},
        F.none_negative_some(Frame, q, present))
    case Con{h, tail} 0n: present
    case Con{h, tail} 1n+n: query_prefix(tail, ys, n, q, present)

law position_present_inside:
  for xs: List<&2, Frame>
  for n: Nat
  for -q: Frame
  for present: {query(xs, n) == Some{q} : Maybe<&2, Frame>}
  {Nat.is_lt(n, size(xs)) == True{} : Bool}
def position_present_inside(xs, n, q, present):
  match xs n:
    case Nil{} _:
      L.ex_false({Nat.is_lt(n, size(Nil{})) == True{} : Bool}, F.none_negative_some(Frame, q, present))
    case Con{h, t} 0n: {==}
    case Con{h, t} 1n+k: position_present_inside(t, k, q, present)

law query_establishes_observation:
  for -c: S.Configuration
  for -p: S.Program
  for -xs: List<&2, Frame>
  for -t: Nat
  for -q: Frame
  for -f: I.Fact
  for query_result: {query(xs, t) == Some{q} : Maybe<&2, Frame>}
  for fact: rel_fact(c, p, q, f)
  observes(c, p, xs, t, f)
def query_establishes_observation(c, p, xs, t, q, f, query_result, fact):
  %Equal.sym(Maybe<&2, Frame>, query(xs, t), Some{q}, query_result) : selected(c, p, _, f)
  fact

# Core subtrace: cannot introduce publication/conclusion.
type FrameExec is Data:
  Evaluation{execution_trace: S.Trace}
  Operation{schema: D.Schema, state: D.State, operation: D.Operation, result: D.ResultOp}

def expand_exec(+r: P.Request, +ctx: D.Context, xs: List<&2, FrameExec>) -> List<&2, Frame>:
  match xs:
    case Nil{}: Nil{}
    case Con{Evaluation{execution_trace}, t}: Con{Evaluated{r, ctx, execution_trace}, expand_exec(r, ctx, t)}
    case Con{Operation{e, s, o, result}, t}: Con{Operated{e, s, o, result}, expand_exec(r, ctx, t)}

# Persistent state before the tick; not an account chosen by the candidate.
def update_state(q: Frame, previous: Maybe<&2, D.State>) -> Maybe<&2, D.State>:
  match q:
    case Initialized{s}: Some{s}
    case Published{s}: Some{s}
    case _: previous

def state_in(xs: List<&2, Frame>, t: Nat, previous: Maybe<&2, D.State>) -> Maybe<&2, D.State>:
  match xs t:
    case Nil{} _: previous
    case Con{h, tail} 0n: previous
    case Con{h, tail} 1n+k: state_in(tail, k, update_state(h, previous))

def state_initial(x: I.Scenario) -> Maybe<&2, D.State>:
  match x:
    case I.Initialize{world, c, s, pi}: None{}
    case I.Serve{world, c, s, input}: Some{s}

def visible(q: Maybe<&2, D.State>, -s: D.State) -> Type:
  match q:
    case None{}: Empty
    case Some{current}: {s == current : D.State}

# The index is a protocol position, never a clock or budget.
# Fatal failure ends instance availability without undoing stores.
def failure_fatal(q: Frame) -> Bool:
  match q:
    case Failed{stage, id, fatal}: fatal
    case _: False{}

def instance_active(xs: List<&2, Frame>, t: Nat) -> Bool:
  match xs t:
    case Nil{} _: True{}
    case Con{h, r} 0n: True{}
    case Con{h, r} 1n+k: Bool.not(failure_fatal(h)) && instance_active(r, k)

def position_observable(+xs: List<&2, Frame>, +t: Nat) -> Bool:
  Nat.is_le(t, size(xs)) && instance_active(xs, t)

def observes_service(-c: S.Configuration, -p: S.Program, initial: Maybe<&2, D.State>,
  xs: List<&2, Frame>, t: Nat, f: I.Fact) -> Type:
  match f:
    case I.ConfigurationInUse{original}: L.E<{position_observable(xs, t) == True{} : Bool}, {original == c : S.Configuration}>
    case I.StateVisible{s}: L.E<{position_observable(xs, t) == True{} : Bool}, visible(state_in(xs, t, initial), s)>
    case _: observes(c, p, xs, t, f)

law state_before_of_first_step:
  for xs: List<&2, Frame>
  for -s: Maybe<&2, D.State>
  {state_in(xs, 0n, s) == s : Maybe<&2, D.State>}
def state_before_of_first_step(xs, s):
  match xs:
    case Nil{}: {==}
    case Con{h, t}: {==}

law publish_changes_only_o_state_next:
  for -xs: List<&2, Frame>
  for -s: Maybe<&2, D.State>
  for -w: D.State
  for -t: Nat
  {state_in(Con{Published{w}, xs}, 1n+t, s) == state_in(xs, t, Some{w}) : Maybe<&2, D.State>}
def publish_changes_only_o_state_next(xs, s, w, t):
  {==}


# Uniqueness of the selected event, without requiring the fact to be Data.
def rel_fact_unique(-c: S.Configuration, -p: S.Program, q: Frame,
  -f: I.Fact, -g: I.Fact, hf: rel_fact(c, p, q, f), hg: rel_fact(c, p, q, g)) ->
  {f == g : I.Fact}:
  Equal.trans(I.Fact, f, fact_of_frame(c, p, q), g, hf,
    Equal.sym(I.Fact, g, fact_of_frame(c, p, q), hg))

def selected_unique(-c: S.Configuration, -p: S.Program, q: Maybe<&2, Frame>,
  -f: I.Fact, -g: I.Fact, hf: selected(c, p, q, f), hg: selected(c, p, q, g)) ->
  {f == g : I.Fact}:
  match q:
    case None{}: L.ex_false({f == g : I.Fact}, hf)
    case Some{frame}: rel_fact_unique(c, p, frame, f, g, hf, hg)

law observation_unique:
  for -c: S.Configuration
  for -p: S.Program
  for xs: List<&2, Frame>
  for t: Nat
  for -f: I.Fact
  for -g: I.Fact
  for hf: observes(c, p, xs, t, f)
  for hg: observes(c, p, xs, t, g)
  {f == g : I.Fact}
def observation_unique(c, p, xs, t, f, g, hf, hg):
  selected_unique(c, p, query(xs, t), f, g, hf, hg)


# Projection forgets only Type indices (configuration/program).
def frame_of_fact(f: I.Fact) -> Frame:
  match f:
    case I.ConfigurationInUse{c}: Configured{}
    case I.ProofInitialAccepts{}: InitialAccepts{}
    case I.InstanceStarted{s}: Initialized{s}
    case I.InitializationRefused{s}: InitialRefused{s}
    case I.Encoded{v, bs}: Encoded{v, bs}
    case I.Decoded{bs, v}: Decoded{bs, v}
    case I.Stored{s, bs, abstr}: Stored{s, bs, abstr}
    case I.CheckedLength{pos, n}: Checked{pos, n}
    case I.AllocatedField{pos, n}: Constructed{pos, n}
    case I.ReadBody{before, n, declared}: Read{before, n, declared}
    case I.ReceivedRequest{r}: Received{r}
    case I.Authenticated{r, ctx}: Authenticated{r, ctx}
    case I.CertificateAccepted{r, ctx, p}: Accepts{r, ctx}
    case I.CertificateRejected{r, ctx}: Rejected{r, ctx}
    case I.ProgramStarted{r, ctx, p}: Started{r, ctx}
    case I.Evaluated{r, ctx, p, execution_trace}: Evaluated{r, ctx, execution_trace}
    case I.Operated{e, s, o, r}: Operated{e, s, o, r}
    case I.Prepared{r, bs}: Prepared{r, bs}
    case I.Published{s}: Published{s}
    case I.StateVisible{s}: Visible{s}
    case I.FailedEnvironment{stage, id, fatal}: Failed{stage, id, fatal}
    case I.Concluded{r, s, closes}: Completed{r, s, closes}
    case I.DeliveredEverything{bs}: Delivered{bs}
    case I.DeliveryInterrupted{bs}: Interrupted{bs}
    case I.ClosedChannel{}: Closed{}
    case I.NextCall{before, after}: Next{before, after}
    case I.InspectionNotModeled{description}: Inspection{description}
    case I.EffectNotModeled{description}: Effect{description}

# Projection forgets indices and recovers exactly the original frame.
def fact_reconstructs_frame(-c: S.Configuration, -p: S.Program, q: Frame) ->
  {frame_of_fact(fact_of_frame(c, p, q)) == q : Frame}:
  match q:
    case Configured{}: {==}
    case InitialAccepts{}: {==}
    case Initialized{s}: {==}
    case InitialRefused{s}: {==}
    case Encoded{v, bs}: {==}
    case Decoded{bs, v}: {==}
    case Stored{s, bs, abstr}: {==}
    case Checked{pos, n}: {==}
    case Constructed{pos, n}: {==}
    case Read{before, n, declared}: {==}
    case Received{r}: {==}
    case Authenticated{r, ctx}: {==}
    case Accepts{r, ctx}: {==}
    case Rejected{r, ctx}: {==}
    case Started{r, ctx}: {==}
    case Evaluated{r, ctx, execution_trace}: {==}
    case Operated{e, s, o, r}: {==}
    case Prepared{r, bs}: {==}
    case Published{s}: {==}
    case Visible{s}: {==}
    case Failed{stage, id, fatal}: {==}
    case Completed{r, s, closes}: {==}
    case Delivered{bs}: {==}
    case Interrupted{bs}: {==}
    case Closed{}: {==}
    case Next{before, after}: {==}
    case Inspection{description}: {==}
    case Effect{description}: {==}

def relation_frame(-c: S.Configuration, -p: S.Program, q: Frame,
  -f: I.Fact, hf: rel_fact(c, p, q, f)) -> {frame_of_fact(f) == q : Frame}:
  %Equal.sym(I.Fact, f, fact_of_frame(c, p, q), hf) : {frame_of_fact(_) == q : Frame}
  fact_reconstructs_frame(c, p, q)

def selected_frame(-c: S.Configuration, -p: S.Program, q: Maybe<&2, Frame>,
  -f: I.Fact, hf: selected(c, p, q, f)) -> {q == Some{frame_of_fact(f)} : Maybe<&2, Frame>}:
  match q:
    case None{}: L.ex_false({None{} == Some{frame_of_fact(f)} : Maybe<&2, Frame>}, hf)
    case Some{+frame}:
      Equal.cong(Frame, Maybe<&2, Frame>, q => Some{q}, frame, frame_of_fact(f),
        Equal.sym(Frame, frame_of_fact(f), frame, relation_frame(c, p, frame, f, hf)))

law observation_frame:
  for -c: S.Configuration
  for -p: S.Program
  for xs: List<&2, Frame>
  for t: Nat
  for -f: I.Fact
  for hf: observes(c, p, xs, t, f)
  {query(xs, t) == Some{frame_of_fact(f)} : Maybe<&2, Frame>}
def observation_frame(c, p, xs, t, f, hf):
  selected_frame(c, p, query(xs, t), f, hf)

# Generic query decomposition into two concatenated phases.
def Part(-xs: List<&2, Frame>, -ys: List<&2, Frame>, -t: Nat, -q: Frame) -> Type:
  L.Disjunction<&i: Nat -> L.E<{t == i : Nat}, {query(xs, i) == Some{q} : Maybe<&2, Frame>}>,
    &i: Nat -> L.E<{t == Nat.add(size(xs), i) : Nat}, {query(ys, i) == Some{q} : Maybe<&2, Frame>}>>

def raise_part(-h: Frame, -xs: List<&2, Frame>, -ys: List<&2, Frame>,
  -t: Nat, -q: Frame, part: Part(xs, ys, t, q)) -> Part(Con{h, xs}, ys, Succ{t}, q):
  match part:
    case L.Left{(i, L.Both{pos, query_result})}:
      L.Left{(Succ{i}, L.Both{Equal.cong(Nat, Nat, x => Succ{x}, t, i, pos), query_result})}
    case L.Right{(i, L.Both{pos, query_result})}:
      L.Right{(i, L.Both{Equal.cong(Nat, Nat, x => Succ{x}, t, Nat.add(size(xs), i), pos), query_result})}

law divide_query:
  for +xs: List<&2, Frame>
  for -ys: List<&2, Frame>
  for t: Nat
  for -q: Frame
  for query_result: {query(concatenate(xs, ys), t) == Some{q} : Maybe<&2, Frame>}
  Part(xs, ys, t, q)
def divide_query(xs, ys, t, q, query_result):
  match xs t:
    case Nil{} +u: L.Right{(u, L.Both{{==}, query_result})}
    case Con{h, r} 0n: L.Left{(0n, L.Both{{==}, query_result})}
    case Con{h, +r} 1n+u: raise_part(h, r, ys, u, q, divide_query(r, ys, u, q, query_result))

law order_shifted:
  for prefix: Nat
  for -a: Nat
  for -b: Nat
  for less: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(prefix, a), Nat.add(prefix, b)) == True{} : Bool}
def order_shifted(prefix, a, b, less):
  match prefix:
    case 0n: less
    case 1n+p: order_shifted(p, a, b, less)


law concatenate_assoc:
  for xs: List<&2, Frame>
  for -ys: List<&2, Frame>
  for -zs: List<&2, Frame>
  {concatenate(concatenate(xs, ys), zs) == concatenate(xs, concatenate(ys, zs)) : List<&2, Frame>}
def concatenate_assoc(xs, ys, zs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Frame>, List<&2, Frame>, r => Con{h, r},
        concatenate(concatenate(t, ys), zs), concatenate(t, concatenate(ys, zs)), concatenate_assoc(t, ys, zs))

# Each selected relation is fact equality. J reopens that
# equality twice; no live Program/Configuration is duplicated.
def equality_reopenable(-A: Type, -x: A, -y: A, equal: {x == y : A}) ->
  L.E<{x == y : A}, {x == y : A}>:
  %equal : L.E<{x == _ : A}, {x == _ : A}>
  L.Both{{==}, {==}}

def duplicate_rel_fact(-c: S.Configuration, -p: S.Program, q: Frame, -f: I.Fact,
  fact: rel_fact(c, p, q, f)) -> L.E<rel_fact(c, p, q, f), rel_fact(c, p, q, f)>:
  equality_reopenable(I.Fact, f, fact_of_frame(c, p, q), fact)

def duplicate_selected(-c: S.Configuration, -p: S.Program, q: Maybe<&2, Frame>, -f: I.Fact,
  fact: selected(c, p, q, f)) -> L.E<selected(c, p, q, f), selected(c, p, q, f)>:
  match q:
    case None{}: L.ex_false(L.E<Empty, Empty>, fact)
    case Some{q}: duplicate_rel_fact(c, p, q, f, fact)

law duplicate_observation:
  for -c: S.Configuration
  for -p: S.Program
  for xs: List<&2, Frame>
  for t: Nat
  for -f: I.Fact
  for fact: observes(c, p, xs, t, f)
  L.E<observes(c, p, xs, t, f), observes(c, p, xs, t, f)>
def duplicate_observation(c, p, xs, t, f, fact):
  duplicate_selected(c, p, query(xs, t), f, fact)

# Two consecutive milestones after a prefix, without empty-slot conventions.
law two_frames_after_prefix:
  for xs: List<&2, Frame>
  for -ys: List<&2, Frame>
  for -a: Frame
  for -b: Frame
  L.E<{query(concatenate(xs, Con{a, Con{b, ys}}), size(xs)) == Some{a} : Maybe<&2, Frame>},
    {query(concatenate(xs, Con{a, Con{b, ys}}), Succ{size(xs)}) == Some{b} : Maybe<&2, Frame>}>
def two_frames_after_prefix(xs, ys, a, b):
  match xs:
    case Nil{}: L.Both{{==}, {==}}
    case Con{h, t}: two_frames_after_prefix(t, ys, a, b)

# Order arithmetic used by prefixes and execution.
law less_transitive:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}
def less_transitive(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _: F.absurd_boolean({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 0n 1n+j 0n: F.absurd_boolean({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 1n+j 1n+k: {==}
    case 1n+i 0n _: F.absurd_boolean({Nat.is_lt(1n+i, c) == True{} : Bool}, ab)
    case 1n+i 1n+j 0n: F.absurd_boolean({Nat.is_lt(1n+i, 0n) == True{} : Bool}, bc)
    case 1n+i 1n+j 1n+k: less_transitive(i, j, k, ab, bc)


# Prefix of facts actually observed when a call is interrupted.
# It is not a deadline, fuel or execution limit.
def first(n: Nat, xs: List<&2, Frame>) -> List<&2, Frame>:
  match n xs:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k Con{h, t}: Con{h, first(k, t)}

law query_in_prefix_and_real:
  for n: Nat
  for +xs: List<&2, Frame>
  for t: Nat
  for -q: Frame
  for query_result: {query(first(n, xs), t) == Some{q} : Maybe<&2, Frame>}
  {query(xs, t) == Some{q} : Maybe<&2, Frame>}
def query_in_prefix_and_real(n, xs, t, q, query_result):
  match n xs t:
    case 0n _ _: L.ex_false({query(xs, t) == Some{q} : Maybe<&2, Frame>}, F.none_negative_some(Frame, q, query_result))
    case 1n+k Nil{} _: L.ex_false({query(Nil{}, t) == Some{q} : Maybe<&2, Frame>}, F.none_negative_some(Frame, q, query_result))
    case 1n+k Con{h, r} 0n: query_result
    case 1n+k Con{h, r} 1n+u: query_in_prefix_and_real(k, r, u, q, query_result)

law query_in_prefix_respects_cut:
  for n: Nat
  for xs: List<&2, Frame>
  for t: Nat
  for -q: Frame
  for query_result: {query(first(n, xs), t) == Some{q} : Maybe<&2, Frame>}
  {Nat.is_lt(t, n) == True{} : Bool}
def query_in_prefix_respects_cut(n, xs, t, q, query_result):
  match n xs t:
    case 0n _ _: L.ex_false({Nat.is_lt(t, 0n) == True{} : Bool}, F.none_negative_some(Frame, q, query_result))
    case 1n+k Nil{} _: L.ex_false({Nat.is_lt(t, 1n+k) == True{} : Bool}, F.none_negative_some(Frame, q, query_result))
    case 1n+k Con{h, r} 0n: {==}
    case 1n+k Con{h, r} 1n+u: query_in_prefix_respects_cut(k, r, u, q, query_result)

law query_before_of_cut_and_preserved:
  for n: Nat
  for xs: List<&2, Frame>
  for t: Nat
  for less: {Nat.is_lt(t, n) == True{} : Bool}
  {query(first(n, xs), t) == query(xs, t) : Maybe<&2, Frame>}
def query_before_of_cut_and_preserved(n, xs, t, less):
  match n xs t:
    case 0n _ 0n: F.absurd_boolean({query(first(0n, xs), 0n) == query(xs, 0n) : Maybe<&2, Frame>}, less)
    case 0n _ 1n+u: F.absurd_boolean({query(first(0n, xs), 1n+u) == query(xs, 1n+u) : Maybe<&2, Frame>}, less)
    case 1n+k Nil{} _: {==}
    case 1n+k Con{h, r} 0n: {==}
    case 1n+k Con{h, r} 1n+u: query_before_of_cut_and_preserved(k, r, u, less)
