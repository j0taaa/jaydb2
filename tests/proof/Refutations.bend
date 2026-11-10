# These are proved impossibility statements about concrete wrong executable
# results and the exact EntryCore/Publication clauses, not just failed proofs.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Logic.bend as L
import ../../proof/Foundations.bend as F
import ../../src/Gate.bend as K
import ../../contract/Theorems.bend as G
import ./Controls.bend as X
import ./WrongSteps.bend as Wrong

law spoofed_step_uninhabited:
  G.EntryCore(G.Admitted{}, Wrong.spoofed_begin(), X.configuration(), X.seed(), X.request(), X.reject) -> Empty

def spoofed_step_uninhabited(core):
  match core:
    case L.Both{identity, remaining}:
      F.absurd_boolean(Empty,
        Equal.cong(Maybe<&2, D.Context>, Bool, Wrong.is_spoof,
          D.authenticate(X.seed(), "token"), Some{X.spoof()}, identity))

law uncertified_step_uninhabited:
  G.EntryCore(G.Admitted{}, Wrong.uncertified_begin(), X.configuration(), X.seed(), X.request(), X.reject) -> Empty

def uncertified_step_uninhabited(core):
  match core:
    case L.Both{identity, (p, L.Both{admission, remaining})}:
      F.absurd_boolean(Empty,
        Equal.cong(K.Verdict, Bool, Wrong.is_accept,
          X.reject(X.configuration(), X.request(), X.context()), K.Accept{p}, admission))

law refusal_publication_uninhabited:
  G.Publication(S.Response{S.Refusal{}, D.VAbsent{}}, X.seed(), X.changed(), X.changed()) -> Empty

def refusal_publication_uninhabited(wrong):
  F.absurd_boolean(Empty,
    Equal.cong(D.State, Bool, Wrong.has_users, X.changed(), X.seed(), wrong))

law reject_all_controller_uninhabited:
  G.EntryCore(G.Admitted{}, K.Halted{S.response_error(S.Certificate{})},
    X.configuration(), X.seed(), X.request(), Wrong.accept) -> Empty

def reject_all_controller_uninhabited(core):
  match core:
    case L.Both{rejection, early}:
      F.absurd_boolean(Empty,
        Equal.cong(K.Entry, Bool, Wrong.is_halted,
          K.begin(X.configuration(), X.seed(), X.request(), Wrong.accept),
          K.Halted{S.response_error(S.Certificate{})}, rejection))
