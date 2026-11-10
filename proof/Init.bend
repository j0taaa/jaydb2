import Base
import ../contract/Theorems.bend as C
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ./Foundations.bend as F

def seed_cases(-c: S.Configuration, +seed: D.State, ok: Bool,
  v: C.SeedVerdict<c, seed>, exact: {R.configuration_is_valid(c) == ok : Bool}) -> C.Init(c, seed, v):
  match ok v:
    case False{} C.SeedReject{}:
      %Equal.sym(Bool, R.configuration_is_valid(c), False{}, exact) : C.InitAt(c, seed, C.SeedReject{}, _)
      L.Both{started => h => L.ex_false(L.E<{started == seed : D.State}, L.E<{False{} == True{} : Bool}, R.Valid(c, started)>>, F.none_negative_some(D.State, started, h)),
        L.Both{h => accepted => F.absurd_boolean({None{} == Some{seed} : Maybe<&2, D.State>}, h), {==}}}
    case False{} C.SeedAccept{valid}:
      %Equal.sym(Bool, R.configuration_is_valid(c), False{}, exact) : C.InitAt(c, seed, C.SeedAccept{valid}, _)
      L.Both{started => h => L.ex_false(L.E<{started == seed : D.State}, L.E<{False{} == True{} : Bool}, R.Valid(c, started)>>, F.none_negative_some(D.State, started, h)),
        L.Both{h => accepted => F.absurd_boolean({None{} == Some{seed} : Maybe<&2, D.State>}, h), {==}}}
    case True{} C.SeedReject{}:
      %Equal.sym(Bool, R.configuration_is_valid(c), True{}, exact) : C.InitAt(c, seed, C.SeedReject{}, _)
      L.Both{started => h => L.ex_false(L.E<{started == seed : D.State}, L.E<{True{} == True{} : Bool}, R.Valid(c, started)>>, F.none_negative_some(D.State, started, h)),
        L.Both{h => accepted => L.ex_false({None{} == Some{seed} : Maybe<&2, D.State>}, accepted), {==}}}
    case True{} C.SeedAccept{valid}:
      %Equal.sym(Bool, R.configuration_is_valid(c), True{}, exact) : C.InitAt(c, seed, C.SeedAccept{valid}, _)
      L.Both{started => h =>
        (%F.some_injective(D.State, seed, started, h) :
          L.E<{_ == seed : D.State}, L.E<{True{} == True{} : Bool}, R.Valid(c, _)>>
          L.Both{{==}, L.Both{{==}, valid}}),
        L.Both{h => accepted => {==}, {==}}}

def init_theorem() -> C.InitTheorem():
  c => seed => v => seed_cases(c, seed, R.configuration_is_valid(c), v, {==})
