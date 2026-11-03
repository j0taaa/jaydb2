# Bound on each confirmed read

`ReceptionLimits.bend` proves six general laws. `cap` can be any Nat, including
zero: it adds no message or program quota. A reader may divide a message into
any number of chunks.

`consumption_confirmed_respects_declared_and_limit` receives a prior total within
the declared size, its admission under the message ceiling, and an actual
quantity no greater than the request `min(cap, declared - before)`. It proves
that the new total exceeds neither the declaration nor the ceiling.
Comparisons are including. Transitivity, minimum bounds, and natural
subtraction are proved by induction without assuming those final inequalities.

`header_measured_establishes_declaration_original` connects `nat64(declared)` to
the header's high/low words and proves the original declaration-equality
predicate. `consumption_real_bounded_establishes_rule2_original` composes these
relations and yields exactly `LAWS.Rule2(ReadBody{before, received, declared})`
in a serving scenario without receiving Rule2 itself as a premise. The
positive test reapplies this API for every body, representable header,
configuration, and confirmed quantity. Two mutations reject consumption beyond
the remainder and replacement of the header size.

The confirmed quantity is an obligation of correspondence with the real
`read`. The theorem does not claim that writing a number into a receipt
satisfies that contract. The selected C retains the actual return before FFI,
bounds requests by the remainder, and never reuses a consumed receipt. The
bridge must still connect each call and receipt to its actual event, including
the prior total, frame identity, single consumption, and validity of the whole
reception. `ReceptionValid` does not follow from the inequality: bytes, actual
length, framing, and truncation have their own obligations.

A Python exception does not establish zero consumption. A retry requires the
reader to preserve confirmed consumption correctly. Driver progress and
correspondence of external facts are not results of this proof. The active
contract requires no physical measurement or budget. No `Environment` was
constructed, and no complete Law 2 or executable Contract is claimed.
