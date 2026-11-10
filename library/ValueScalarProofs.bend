# Complete scalar decoder domains. Int64/Bool decoding is purely a constructor
# check; text additionally rejects non-Unicode Char data. No name/record/list
# validity premise is silently added to these exact typed-value statements.
import Base
import ../contract/Data.bend as D
import ./Value.bend as V
import ../proof/Foundations.bend as F

type Both<-P: Data,-Q: Data> is Data:
  Both{left: P,right: Q}

def reject_encoded_candidate(~A: Data,~decode: D.Value -> Maybe<&2,A>,~encode: A -> D.Value,+input: D.Value,+candidate: A,actual: {decode(input) == None{} : Maybe<&2,A>},equal: {input == encode(candidate) : D.Value},roundtrip: {decode(encode(candidate)) == Some{candidate} : Maybe<&2,A>}) -> Empty:
  F.none_negative_some(A,candidate,Equal.trans(Maybe<&2,A>,None{},decode(input),Some{candidate},Equal.sym(Maybe<&2,A>,decode(input),None{},actual),Equal.trans(Maybe<&2,A>,decode(input),decode(encode(candidate)),Some{candidate},Equal.cong(D.Value,Maybe<&2,A>,decode,input,encode(candidate),equal),roundtrip)))

def IntegerSound(+input: D.Value,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{word}: {input == V.int_value(word) : D.Value}
    case None{}: Unit

law actual_integer_decoder_preserves_the_exact_word_and_value:
  for +input: D.Value
  IntegerSound(input,V.integer(input))
def actual_integer_decoder_preserves_the_exact_word_and_value(input):
  match input:
    case D.VInt{h,l}: {==}
    case D.VAbsent{}: Unit{}
    case D.VBool{b}: Unit{}
    case D.VText{s}: Unit{}
    case D.VListEmpty{}: Unit{}
    case D.VList{h,t}: Unit{}
    case D.VRecordEmpty{}: Unit{}
    case D.VRecord{n,v,t}: Unit{}

def IntegerMeaning(+input: D.Value,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{word}: {input == V.int_value(word) : D.Value}
    case None{}: @+word: V.Int64 -> {input == V.int_value(word) : D.Value} -> Empty

def integer_complete(+input: D.Value,result: Maybe<&2,V.Int64>,actual: {V.integer(input) == result : Maybe<&2,V.Int64>},sound: IntegerSound(input,result)) -> IntegerMeaning(input,result):
  match result:
    case Some{word}: sound
    case None{}: +word => exact => reject_encoded_candidate(~V.Int64,~V.integer,~V.int_value,input,word,actual,exact,V.integer_roundtrip(word))

law actual_integer_decoder_accepts_exactly_all_integer_values:
  for +input: D.Value
  IntegerMeaning(input,V.integer(input))
def actual_integer_decoder_accepts_exactly_all_integer_values(input):
  integer_complete(input,V.integer(input),{==},actual_integer_decoder_preserves_the_exact_word_and_value(input))


def bool_value(b: Bool) -> D.Value:
  D.VBool{b}

def BooleanSound(+input: D.Value,result: Maybe<&2,Bool>) -> Type:
  match result:
    case Some{b}: {input == D.VBool{b} : D.Value}
    case None{}: Unit

law actual_boolean_decoder_preserves_the_exact_value:
  for +input: D.Value
  BooleanSound(input,V.boolean(input))
def actual_boolean_decoder_preserves_the_exact_value(input):
  match input:
    case D.VBool{b}: {==}
    case D.VAbsent{}: Unit{}
    case D.VInt{h,l}: Unit{}
    case D.VText{s}: Unit{}
    case D.VListEmpty{}: Unit{}
    case D.VList{h,t}: Unit{}
    case D.VRecordEmpty{}: Unit{}
    case D.VRecord{n,v,t}: Unit{}

def BooleanMeaning(+input: D.Value,result: Maybe<&2,Bool>) -> Type:
  match result:
    case Some{b}: {input == D.VBool{b} : D.Value}
    case None{}: @+b: Bool -> {input == D.VBool{b} : D.Value} -> Empty

law boolean_value_roundtrip:
  for +b: Bool
  {V.boolean(D.VBool{b}) == Some{b} : Maybe<&2,Bool>}
def boolean_value_roundtrip(b): {==}

def boolean_complete(+input: D.Value,result: Maybe<&2,Bool>,actual: {V.boolean(input) == result : Maybe<&2,Bool>},sound: BooleanSound(input,result)) -> BooleanMeaning(input,result):
  match result:
    case Some{b}: sound
    case None{}: +b => exact => reject_encoded_candidate(~Bool,~V.boolean,~bool_value,input,b,actual,exact,boolean_value_roundtrip(b))

law actual_boolean_decoder_accepts_exactly_all_boolean_values:
  for +input: D.Value
  BooleanMeaning(input,V.boolean(input))
def actual_boolean_decoder_accepts_exactly_all_boolean_values(input):
  boolean_complete(input,V.boolean(input),{==},actual_boolean_decoder_preserves_the_exact_value(input))


def text_value(s: String) -> D.Value:
  D.VText{s}

def TextSound(+input: D.Value,result: Maybe<&2,String>) -> Type:
  match result:
    case Some{s}: Both<{input == D.VText{s} : D.Value},{D.unicode_valid(s) == True{} : Bool}>
    case None{}: Unit

def text_guard_case(valid: Bool,+s: String,actual: {D.unicode_valid(s) == valid : Bool}) -> TextSound(D.VText{s},Bool.pick(Maybe<&2,String>,valid,Some{s},None{})):
  match valid:
    case True{}: Both{{==},actual}
    case False{}: Unit{}

law actual_text_decoder_preserves_the_exact_unicode_string:
  for +input: D.Value
  TextSound(input,V.text(input))
def actual_text_decoder_preserves_the_exact_unicode_string(input):
  match input:
    case D.VText{+s}: text_guard_case(D.unicode_valid(s),s,{==})
    case D.VAbsent{}: Unit{}
    case D.VBool{b}: Unit{}
    case D.VInt{h,l}: Unit{}
    case D.VListEmpty{}: Unit{}
    case D.VList{h,t}: Unit{}
    case D.VRecordEmpty{}: Unit{}
    case D.VRecord{n,v,t}: Unit{}

law unicode_text_value_roundtrip:
  for +s: String
  for valid: {D.unicode_valid(s) == True{} : Bool}
  {V.text(D.VText{s}) == Some{s} : Maybe<&2,String>}
def unicode_text_value_roundtrip(s,valid):
  Equal.cong(Bool,Maybe<&2,String>,accepted => Bool.pick(Maybe<&2,String>,accepted,Some{s},None{}),D.unicode_valid(s),True{},valid)

def TextMeaning(+input: D.Value,result: Maybe<&2,String>) -> Type:
  match result:
    case Some{s}: Both<{input == D.VText{s} : D.Value},{D.unicode_valid(s) == True{} : Bool}>
    case None{}: @+s: String -> {D.unicode_valid(s) == True{} : Bool} -> {input == D.VText{s} : D.Value} -> Empty

def text_complete(+input: D.Value,result: Maybe<&2,String>,actual: {V.text(input) == result : Maybe<&2,String>},sound: TextSound(input,result)) -> TextMeaning(input,result):
  match result:
    case Some{s}: sound
    case None{}: +s => valid => exact => reject_encoded_candidate(~String,~V.text,~text_value,input,s,actual,exact,unicode_text_value_roundtrip(s,valid))

law actual_text_decoder_accepts_exactly_unicode_text_values:
  for +input: D.Value
  TextMeaning(input,V.text(input))
def actual_text_decoder_accepts_exactly_unicode_text_values(input):
  text_complete(input,V.text(input),{==},actual_text_decoder_preserves_the_exact_unicode_string(input))
