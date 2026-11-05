# The removed host gate returned framing errors, otherwise ran authentication
# on the SAME packet/snapshot. Compare exact private output bytes, including
# public errors, transport errors and generated source/proof/instance metadata.
# This is a pure route equivalence, not a proof of OS processes or artifact IO.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../src/Input.bend as E
import ../src/Messages.bend as M

def gated(input: E.PreAuthentication) -> List<&2, U32>:
  match input:
    case E.InputReady{s, r}:
      M.authentication(E.authenticate_pre(E.InputReady{s, r}))
    case E.ErrorMessage{status}:
      M.framing(E.ErrorMessage{status})
    case E.ErrorTransport{}:
      M.framing(E.ErrorTransport{})

law gate_preserves_exact_output:
  for +input: E.PreAuthentication
  {gated(input) == M.authentication(E.authenticate_pre(input)) : List<&2, U32>}
def gate_preserves_exact_output(input):
  match input:
    case E.InputReady{s, r}: {==}
    case E.ErrorMessage{status}: {==}
    case E.ErrorTransport{}: {==}

# No validity, successful decode, credential or final-state premise is needed.
law single_pass_preserves_exact_output:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  {gated(E.decode(bytes, schema, limits)) ==
    M.authentication(E.analyze(bytes, schema, limits)) : List<&2, U32>}
def single_pass_preserves_exact_output(bytes, schema, limits):
  gate_preserves_exact_output(E.decode(bytes, schema, limits))
