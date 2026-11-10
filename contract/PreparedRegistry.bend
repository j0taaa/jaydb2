# Scoped prepared entries used by executable request resolution.
import Base

type Entry is Data:
  Entry{instance: String, handle: String, code: String, proof: String,
    read_only: Bool, seal: String}

def code(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  c

def proof(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  p

def matches(i: String, h: String, e: Entry) -> Bool:
  Entry{ei, eh, c, p, r, s} = e
  String.eq(i, ei) && String.eq(h, eh)

def lookup(+i: String, +h: String, entries: List<&2, Entry>) -> Maybe<&2, Entry>:
  match entries:
    case Nil{}: None{}
    case Con{+entry, rest}:
      Bool.pick(Maybe<&2, Entry>, matches(i, h, entry), Some{entry}, lookup(i, h, rest))
