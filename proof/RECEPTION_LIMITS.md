# Bound on each confirmed read

`ReceptionLimits.bend` proves five pure laws. A confirmed read's previous
consumption is bounded by the declared length; its returned count is bounded
by `min(cap, declared - before)`; admission bounds the declaration by the
message limit. `consumption_confirmed_respects_declared_and_limit` derives
that the new total respects both declaration and message limit. Transitivity,
minimum and subtraction facts are proved by induction.

`header_measured_establishes_declaration_original` connects the actual uint64
header words to `nat64(declared)` and derives declaration equality. The
remaining negative controls reject consumption beyond the remainder and a
changed header length.

T3 must connect the supplied count to the actual read, prior total and frame.
`Resources.ReceptionValid` separately describes exact received octets, physical
length and truncation. Neither read progress nor OS behavior is inferred from
the arithmetic. See the [proof guide](README.md) for the trusted boundary.
