# Independent multiset and all-pairs order specifications for Sequence.sort.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Q
import ./Value.bend as V

type Both<-P:Data,-Q:Data> is Data:
  Both{left:P,right:Q}

# Counts any predicate, independently of comparison or sorting.
def tick(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}: Succ{n}
    case False{}: n

def count(~test: D.Value -> D.Value -> Bool, +env:D.Value, xs: List<&2, D.Value>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{x, rest}: tick(test(env,x), count(~test,env, rest))

law ticks_commute:
  for +a: Bool
  for +b: Bool
  for +n: Nat
  {tick(a, tick(b, n)) == tick(b, tick(a, n)) : Nat}
def ticks_commute(a,b,n):
  match a b:
    case True{} True{}: {==}
    case True{} False{}: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

def insert_count_choice(~less: D.Value -> D.Value -> Bool, ~test: D.Value -> D.Value -> Bool,
  +env:D.Value, b: Bool, +x: D.Value, +h: D.Value, +rest: List<&2, D.Value>,
  rec: {count(~test,env, Q.insert(~less,x,rest)) == tick(test(env,x),count(~test,env,rest)) : Nat}) ->
  {count(~test,env, Bool.pick(List<&2,D.Value>, b, Con{x,Con{h,rest}}, Con{h,Q.insert(~less,x,rest)})) == tick(test(env,x),tick(test(env,h),count(~test,env,rest))) : Nat}:
  match b:
    case True{}: {==}
    case False{}:
      Equal.trans(Nat, tick(test(env,h),count(~test,env,Q.insert(~less,x,rest))), tick(test(env,h),tick(test(env,x),count(~test,env,rest))), tick(test(env,x),tick(test(env,h),count(~test,env,rest))),
        Equal.cong(Nat,Nat,n => tick(test(env,h),n),count(~test,env,Q.insert(~less,x,rest)),tick(test(env,x),count(~test,env,rest)),rec),
        ticks_commute(test(env,h),test(env,x),count(~test,env,rest)))

law insert_content:
  for ~less: D.Value -> D.Value -> Bool
  for ~test: D.Value -> D.Value -> Bool
  for +env:D.Value
  for +x: D.Value
  for +xs: List<&2,D.Value>
  {count(~test,env,Q.insert(~less,x,xs)) == tick(test(env,x),count(~test,env,xs)) : Nat}
def insert_content(less,test,env,x,xs):
  match xs:
    case Nil{}: {==}
    case Con{+h,+rest}: insert_count_choice(~less,~test,env,Bool.not(less(h,x)),x,h,rest,insert_content(~less,~test,env,x,rest))

# Universal predicate counts characterize multiset content, including duplicates.
law sort_content:
  for ~less: D.Value -> D.Value -> Bool
  for ~test: D.Value -> D.Value -> Bool
  for +env:D.Value
  for +xs: List<&2,D.Value>
  {count(~test,env,Q.sort(~less,xs)) == count(~test,env,xs) : Nat}
def sort_content(less,test,env,xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+rest}:
      Equal.trans(Nat,count(~test,env,Q.insert(~less,x,Q.sort(~less,rest))),tick(test(env,x),count(~test,env,Q.sort(~less,rest))),tick(test(env,x),count(~test,env,rest)),
        insert_content(~less,~test,env,x,Q.sort(~less,rest)),
        Equal.cong(Nat,Nat,n => tick(test(env,x),n),count(~test,env,Q.sort(~less,rest)),count(~test,env,rest),sort_content(~less,~test,env,rest)))

def occurrences(+needle:D.Value,xs:List<&2,D.Value>) -> Nat:
  count(~V.equal,needle,xs)

law sort_occurrences:
  for ~less:D.Value -> D.Value -> Bool
  for +needle:D.Value
  for +xs:List<&2,D.Value>
  {occurrences(needle,Q.sort(~less,xs)) == occurrences(needle,xs) : Nat}
def sort_occurrences(less,needle,xs):
  sort_content(~less,~V.equal,needle,xs)

# Non-strict order induced by the caller's strict comparison. Sorted means
# EVERY earlier element is <= EVERY later element; it does not mention sort.
def Le(~less: D.Value -> D.Value -> Bool, a: D.Value, b: D.Value) -> Data:
  {Bool.not(less(b,a)) == True{} : Bool}

def After(~less: D.Value -> D.Value -> Bool, +x: D.Value, xs: List<&2,D.Value>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{h,rest}: Both<Le(~less,x,h),After(~less,x,rest)>

def Sorted(~less: D.Value -> D.Value -> Bool, xs: List<&2,D.Value>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{+h,+rest}: Both<After(~less,h,rest),Sorted(~less,rest)>

# Transitivity and totality are INPUT proof obligations, not axioms.
def after_trans(~less: D.Value -> D.Value -> Bool,
  ~trans: @a:D.Value -> @b:D.Value -> @c:D.Value -> Le(~less,a,b) -> Le(~less,b,c) -> Le(~less,a,c),
  +a:D.Value, +b:D.Value, xs:List<&2,D.Value>, +ab:Le(~less,a,b), h:After(~less,b,xs)) -> After(~less,a,xs):
  match xs h:
    case Nil{} Unit{}: Unit{}
    case Con{+c,rest} Both{bc,tail}: Both{trans(a,b,c,ab,bc),after_trans(~less,~trans,a,b,rest,ab,tail)}

def after_insert_choice(~less:D.Value -> D.Value -> Bool, b:Bool, +a:D.Value, +x:D.Value, +h:D.Value, +rest:List<&2,D.Value>,
  +ax:Le(~less,a,x), ah:Le(~less,a,h), tail:After(~less,a,rest), rec:After(~less,a,Q.insert(~less,x,rest))) ->
  After(~less,a,Bool.pick(List<&2,D.Value>,b,Con{x,Con{h,rest}},Con{h,Q.insert(~less,x,rest)})):
  match b:
    case True{}: Both{ax,Both{ah,tail}}
    case False{}: Both{ah,rec}

def after_insert(~less:D.Value -> D.Value -> Bool, +a:D.Value, +x:D.Value, +xs:List<&2,D.Value>,
  +ax:Le(~less,a,x), h:After(~less,a,xs)) -> After(~less,a,Q.insert(~less,x,xs)):
  match xs h:
    case Nil{} Unit{}: Both{ax,Unit{}}
    case Con{+head,+rest} Both{ah,+tail}:
      after_insert_choice(~less,Bool.not(less(head,x)),a,x,head,rest,ax,ah,tail,after_insert(~less,a,x,rest,ax,tail))

def insert_sorted_choice(~less:D.Value -> D.Value -> Bool,
  ~trans: @a:D.Value -> @b:D.Value -> @c:D.Value -> Le(~less,a,b) -> Le(~less,b,c) -> Le(~less,a,c),
  ~total: @a:D.Value -> @b:D.Value -> {Bool.not(less(b,a)) == False{} : Bool} -> Le(~less,b,a),
  b:Bool, +x:D.Value, +h:D.Value, +rest:List<&2,D.Value>,
  +eq:{Bool.not(less(h,x)) == b : Bool}, +after:After(~less,h,rest), sorted:Sorted(~less,rest), rec:Sorted(~less,Q.insert(~less,x,rest))) ->
  Sorted(~less,Bool.pick(List<&2,D.Value>,b,Con{x,Con{h,rest}},Con{h,Q.insert(~less,x,rest)})):
  match b:
    case True{}:
      Both{Both{eq,after_trans(~less,~trans,x,h,rest,eq,after)},Both{after,sorted}}
    case False{}:
      Both{after_insert(~less,h,x,rest,total(x,h,eq),after),rec}

law insert_sorted:
  for ~less:D.Value -> D.Value -> Bool
  for ~trans: @a:D.Value -> @b:D.Value -> @c:D.Value -> Le(~less,a,b) -> Le(~less,b,c) -> Le(~less,a,c)
  for ~total: @a:D.Value -> @b:D.Value -> {Bool.not(less(b,a)) == False{} : Bool} -> Le(~less,b,a)
  for +x:D.Value
  for +xs:List<&2,D.Value>
  for h:Sorted(~less,xs)
  Sorted(~less,Q.insert(~less,x,xs))
def insert_sorted(less,trans,total,x,xs,h):
  match xs h:
    case Nil{} Unit{}: Both{Unit{},Unit{}}
    case Con{+head,+rest} Both{+after,+sorted}:
      insert_sorted_choice(~less,~trans,~total,Bool.not(less(head,x)),x,head,rest,{==},after,sorted,insert_sorted(~less,~trans,~total,x,rest,sorted))

law sort_sorted:
  for ~less:D.Value -> D.Value -> Bool
  for ~trans: @a:D.Value -> @b:D.Value -> @c:D.Value -> Le(~less,a,b) -> Le(~less,b,c) -> Le(~less,a,c)
  for ~total: @a:D.Value -> @b:D.Value -> {Bool.not(less(b,a)) == False{} : Bool} -> Le(~less,b,a)
  for +xs:List<&2,D.Value>
  Sorted(~less,Q.sort(~less,xs))
def sort_sorted(less,trans,total,xs):
  match xs:
    case Nil{}: Unit{}
    case Con{x,+rest}: insert_sorted(~less,~trans,~total,x,Q.sort(~less,rest),sort_sorted(~less,~trans,~total,rest))

# A useful fully discharged order: incomplete tasks before completed tasks.
# Payloads are ignored by comparison, so equal-key stability is observable.
def completed(v:D.Value) -> Bool:
  match v:
    case D.VBool{b}: b
    case D.VRecord{"completed",D.VBool{b},rest}: b
    case _: False{}

def completed_less(a:D.Value,b:D.Value) -> Bool:
  Bool.not(completed(a)) && completed(b)

def false_true(-A:Type,h:{False{} == True{} : Bool}) -> A:
  L.ex_false(A,(%h : Bool.pick(Type,_,Empty,Unit) Unit{}))

def true_false(-A:Type,h:{True{} == False{} : Bool}) -> A:
  false_true(A,Equal.sym(Bool,True{},False{},h))

def rank_le(a:Bool,b:Bool) -> Data:
  {Bool.not(Bool.not(b) && a) == True{} : Bool}

def rank_trans(+a:Bool,+b:Bool,+c:Bool,ab:rank_le(a,b),bc:rank_le(b,c)) -> rank_le(a,c):
  match a b c:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: false_true(rank_le(True{},False{}),ab)
    case True{} False{} True{}: false_true(rank_le(True{},True{}),ab)
    case True{} True{} False{}: false_true(rank_le(True{},False{}),bc)
    case True{} True{} True{}: {==}

def rank_total(+a:Bool,+b:Bool,h:{Bool.not(Bool.not(b) && a) == False{} : Bool}) -> rank_le(b,a):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: true_false(rank_le(True{},False{}),h)
    case True{} False{}: {==}
    case True{} True{}: {==}

def completed_trans(a:D.Value,b:D.Value,c:D.Value,ab:Le(~completed_less,a,b),bc:Le(~completed_less,b,c)) -> Le(~completed_less,a,c):
  rank_trans(completed(a),completed(b),completed(c),ab,bc)

def completed_total(a:D.Value,b:D.Value,h:{Bool.not(completed_less(b,a)) == False{} : Bool}) -> Le(~completed_less,b,a):
  rank_total(completed(a),completed(b),h)

law completed_sorted:
  for +xs:List<&2,D.Value>
  Sorted(~completed_less,Q.sort(~completed_less,xs))
def completed_sorted(xs):
  sort_sorted(~completed_less,~completed_trans,~completed_total,xs)
