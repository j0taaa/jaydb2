# Source equivalence covers every actual byte string, schema and limits,
# including malformed input, invalid credentials and overflowed ceilings.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../src/Input.bend as E
import ../src/OptimizedInput.bend as O
import ../src/Transport.bend as T
import ../src/FastBytes.bend as F
import ../src/Messages.bend as M
import ./FastBytes.bend as P

law parts_exact:
  for parts: Maybe<&2, T.Parts>
  for +schema: D.Schema
  for +limits: S.Limits
  {O.parts(parts, schema, limits) == E.parts(parts, schema, limits) : E.PreAuthentication}
def parts_exact(parts, schema, limits):
  match parts:
    case None{}:
      {==}
    case Some{T.Parts{+state, +body}}:
      Equal.trans(E.PreAuthentication,
        E.read_state(F.nat64_checked(R.limit_state(limits)), schema, state, body,
          F.nat64_checked(R.limit_message(limits))),
        E.read_state(B.nat64(R.limit_state(limits)), schema, state, body,
          F.nat64_checked(R.limit_message(limits))),
        E.read_state(B.nat64(R.limit_state(limits)), schema, state, body,
          B.nat64(R.limit_message(limits))),
        Equal.cong(Maybe<&2, B.Number64>, E.PreAuthentication,
          n => E.read_state(n, schema, state, body, F.nat64_checked(R.limit_message(limits))),
          F.nat64_checked(R.limit_state(limits)), B.nat64(R.limit_state(limits)),
          P.nat64_checked_exact(R.limit_state(limits))),
        Equal.cong(Maybe<&2, B.Number64>, E.PreAuthentication,
          n => E.read_state(B.nat64(R.limit_state(limits)), schema, state, body, n),
          F.nat64_checked(R.limit_message(limits)), B.nat64(R.limit_message(limits)),
          P.nat64_checked_exact(R.limit_message(limits))))

law decode_exact:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  {O.decode(bytes, schema, limits) == E.decode(bytes, schema, limits) : E.PreAuthentication}
def decode_exact(bytes, schema, limits):
  parts_exact(T.separate(bytes), schema, limits)

law analyze_exact:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  {O.analyze(bytes, schema, limits) == E.analyze(bytes, schema, limits) : E.Analysis}
def analyze_exact(bytes, schema, limits):
  Equal.cong(E.PreAuthentication, E.Analysis, E.authenticate_pre,
    O.decode(bytes, schema, limits), E.decode(bytes, schema, limits),
    decode_exact(bytes, schema, limits))

law authentication_output_exact:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  {M.authentication(O.analyze(bytes, schema, limits)) ==
    M.authentication(E.analyze(bytes, schema, limits)) : List<&2, U32>}
def authentication_output_exact(bytes, schema, limits):
  Equal.cong(E.Analysis, List<&2, U32>, M.authentication,
    O.analyze(bytes, schema, limits), E.analyze(bytes, schema, limits),
    analyze_exact(bytes, schema, limits))
