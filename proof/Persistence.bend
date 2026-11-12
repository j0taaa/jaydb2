# Complete-image recovery composition. No persisted proof chain is required:
# records describe the mathematical origin of published bytes. The OS bridge
# must establish that recovered bytes came from one such certified publication
# (or initialization), in the exact same configuration/environment.
# The host selects that complete payload from the v2 alternating slots.
# Sequence/payload checksums, slot parity, consecutive sequences and physical
# fdatasync/growth refinement are T3, not consequences of these byte lemmas.
# DurableCommit checks both slot overwrite and replacement crash transitions.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Codec.bend as C
import ../src/Input.bend as Input
import ../src/State.bend as State
import ./CodecComplete.bend as Codec
import ./Representation.bend as Representation
import ./History.bend as History

# Includes a commit followed by process loss before publication/acknowledgment:
# the candidate is the certified N.conclude state, independent of delivery.
law recovered_certified_publication_is_valid:
  for ~c: S.Configuration
  for +seed: D.State
  for records: List<&2, History.Record>
  for +recovered: D.State
  for initial: R.Valid(c, seed)
  for sources: History.Sources(c, records, seed)
  for exact: {History.state(records, seed) == recovered : D.State}
  R.Valid(c, recovered)
def recovered_certified_publication_is_valid(c, seed, records, recovered, initial, sources, exact):
  %exact : R.Valid(c, _)
  History.history_preserves_validity(c, records, seed, initial, sources)

# Refines the actual Input.state_decoded -> State.decode path. Exact storage
# equality is a protected-filesystem assumption, not a checksum theorem. The
# codec and state roundtrip are discharged with existing checked proofs.
law complete_image_restores_actual_private_input_state:
  for +schema: D.Schema
  for +state: D.State
  for +canonical: List<&2, U32>
  for +disk: List<&2, U32>
  for +body_size: B.Number64
  for +ceiling: B.Number64
  for -request: List<&2, U32>
  for -message_limit: Maybe<&2, B.Number64>
  for structure: {D.structure(schema, state) == True{} : Bool}
  for encoded: P.Encoding(D.state_value(state), canonical)
  for measured: {B.nat64(B.length(canonical)) == Some{body_size} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body_size, ceiling) == True{} : Bool}
  for protected_storage: {disk == canonical : List<&2, U32>}
  {Input.state_decoded(C.decode(disk, ceiling), schema, request, message_limit) ==
    Input.state_read(Some{state}, request, message_limit) : Input.PreAuthentication}
def complete_image_restores_actual_private_input_state(schema, state, canonical, disk,
  body_size, ceiling, request, message_limit, structure, encoded, measured, fits, protected_storage):
  %Equal.sym(List<&2, U32>, disk, canonical, protected_storage) :
    {Input.state_decoded(C.decode(_, ceiling), schema, request, message_limit) ==
      Input.state_read(Some{state}, request, message_limit) : Input.PreAuthentication}
  %Equal.sym(C.Outcome, C.decode(canonical, ceiling), C.Decoded{D.state_value(state)},
    Codec.all_encoding_canonical_representable_and_decoded(D.state_value(state), canonical,
      body_size, ceiling, encoded, measured, fits)) :
    {Input.state_decoded(_, schema, request, message_limit) ==
      Input.state_read(Some{state}, request, message_limit) : Input.PreAuthentication}
  Equal.cong(Maybe<&2, D.State>, Input.PreAuthentication,
    s => Input.state_read(s, request, message_limit),
    State.decode(D.state_value(state), schema), Some{state},
    Representation.transport_private_preserves_state(schema, state, structure))
