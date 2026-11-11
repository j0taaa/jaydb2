import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequenceGroupLookup.bend as Lookup
import ../../../library/SequenceGroupUniqueness.bend as U

law false:
  U.Unique([Sequence.Group{"a",[]},Sequence.Group{"a",[]}])
def false():
  U.Both{U.Both{{==},Unit{}},U.Both{Unit{},Unit{}}}
