import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequenceGroupLookup.bend as Lookup
import ../../../library/SequenceGroupUniqueness.bend as U

law false_negative_duplicate_keys_satisfy_the_independent_uniqueness_spec:
  U.Unique([Sequence.Group{"a",[]},Sequence.Group{"a",[]}])
def false_negative_duplicate_keys_satisfy_the_independent_uniqueness_spec():
  U.Both{U.Both{{==},Unit{}},U.Both{Unit{},Unit{}}}
