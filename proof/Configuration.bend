# Links the initialization test to the original relation.
# Defines neither Environment, observes, Processable nor any host fact.
import Base
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../src/ConfigurationCheck.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O

law accepts_requires_structure_and_identity_exact:
  for c: S.Configuration
  for +identity: String
  for accepted: {C.is_valid(c, identity) == True{} : Bool}
  L.E<{R.configuration_is_valid(c) == True{} : Bool},
    {S.environment(c) == identity : String}>
def accepts_requires_structure_and_identity_exact(c, identity, accepted):
  match c:
    case S.Configuration{e, ls, lim, +amb}:
      F.combined_pair(
        L.E<{R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) == True{} : Bool}, {amb == identity : String}>,
        {R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) == True{} : Bool},
        {String.eq(amb, identity) == True{} : Bool},
        F.and_boolean_separate(R.configuration_is_valid(S.Configuration{e, ls, lim, amb}), String.eq(amb, identity), accepted),
        structure => equal => L.Both{structure, O.string_equal(amb, identity, equal)})

law accepts_satisfies_configuration_is_valid_original:
  for a: I.Environment
  for c: S.Configuration
  for accepted: {C.is_valid(c, I.identity(a)) == True{} : Bool}
  I.ConfigurationValid(a, c)
def accepts_satisfies_configuration_is_valid_original(a, c, accepted):
  accepts_requires_structure_and_identity_exact(c, I.identity(a), accepted)

law configuration_original_is_valid_and_accepts:
  for a: I.Environment
  for c: S.Configuration
  for is_valid: I.ConfigurationValid(a, c)
  {C.is_valid(c, I.identity(a)) == True{} : Bool}
def configuration_original_is_valid_and_accepts(a, c, is_valid):
  match c:
    case S.Configuration{+e, ls, +lim, +amb}:
      +id = I.identity(a)
      F.combined_pair({C.is_valid(S.Configuration{e, ls, lim, amb}, id) == True{} : Bool},
        {R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) == True{} : Bool}, {amb == id : String}, is_valid,
        structure => equal => F.and_boolean_intro(R.configuration_is_valid(S.Configuration{e, ls, lim, amb}), String.eq(amb, id),
          structure, (%Equal.sym(String, amb, id, equal) :
            {String.eq(_, id) == True{} : Bool}
            O.string_eq_refl(id))))
