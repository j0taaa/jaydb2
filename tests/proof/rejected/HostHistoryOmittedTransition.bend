# Causal negative: dropping the first operational edge makes completeness false.
import Base
import ../../../proof/SourceService.bend as Source
import ../../../contract/Semantics.bend as S
import ../../../proof/HostTransitions.bend as H
import ../../../proof/HostHistory.bend as T

law false_omitted_first_transition_would_still_be_complete:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for +instance: String
  for +index: Nat
  for +state: H.Published
  T.Occurs(T.Edge{0n, index, state, H.next(c, instance, state, H.call(c, binding, public, book, index))},
    T.history(c, binding, public, book, instance, Nil{}, 1n, H.next(c, instance, state, H.call(c, binding, public, book, index))))
def false_omitted_first_transition_would_still_be_complete(c, binding, public, book, instance, index, state):
  T.no_operational_transition_is_omitted_from_history(c, binding, public, book, instance, Con{index, Nil{}}, 0n, state, 0n,
    T.Edge{0n, index, state, H.next(c, instance, state, H.call(c, binding, public, book, index))}, {==})
