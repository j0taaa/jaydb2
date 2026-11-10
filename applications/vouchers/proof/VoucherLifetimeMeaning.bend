# Independent complete lifetime meaning at EVERY request, in BOTH directions.
# A live receipt and business row exist together, with the same original input,
# frozen operation/result/principal fields, and the successful (False) cancel tag.
# The specification is a relation over initial row lookups, not a second program.
import Base
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../library/ValueScalarProofs.bend as Pair

def At(+owner: String,+request: String,receipt: Maybe<&2,D.Row>,voucher: Maybe<&2,D.Row>) -> Type:
  match receipt voucher:
    case None{} None{}: Unit
    case Some{receipt} Some{voucher}: Sigma<&2,&2,String,input => Pair.Both<{receipt == P.receipt_row(owner,request,input,False{}) : D.Row},{voucher == P.voucher_row(owner,request,input) : D.Row}>>
    case Some{receipt} None{}: Empty
    case None{} Some{voucher}: Empty

def Request(+owner: String,+request: String,+rows: List<&2,D.Row>) -> Type:
  At(owner,request,D.find_row(rows,V.receipt(request)),D.find_row(rows,V.voucher(request)))
def Lifetime(+owner: String,+rows: List<&2,D.Row>) -> Type:
  @+request: String -> Request(owner,request,rows)

def same_views(+owner: String,+request: String,+old: List<&2,D.Row>,+new: List<&2,D.Row>,receipt: {D.find_row(new,V.receipt(request)) == D.find_row(old,V.receipt(request)) : Maybe<&2,D.Row>},voucher: {D.find_row(new,V.voucher(request)) == D.find_row(old,V.voucher(request)) : Maybe<&2,D.Row>},previous: Request(owner,request,old)) -> Request(owner,request,new):
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(new,V.receipt(request)),D.find_row(old,V.receipt(request)),receipt) : At(owner,request,_,D.find_row(new,V.voucher(request)))
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(new,V.voucher(request)),D.find_row(old,V.voucher(request)),voucher) : At(owner,request,D.find_row(old,V.receipt(request)),_)
  previous

def from_pair(+owner: String,+request: String,+input: String,+old: List<&2,D.Row>,pair: P.PairRows(owner,request,input,False{},P.rows(owner,request,input,False{},old))) -> Request(owner,request,P.rows(owner,request,input,False{},old)):
  match pair:
    case L.Both{voucher,receipt}:
      %Equal.sym(Maybe<&2,D.Row>,D.find_row(P.rows(owner,request,input,False{},old),V.receipt(request)),Some{P.receipt_row(owner,request,input,False{})},receipt) : At(owner,request,_,D.find_row(P.rows(owner,request,input,False{},old),V.voucher(request)))
      %Equal.sym(Maybe<&2,D.Row>,D.find_row(P.rows(owner,request,input,False{},old),V.voucher(request)),Some{P.voucher_row(owner,request,input)},voucher) : At(owner,request,Some{P.receipt_row(owner,request,input,False{})},_)
      (input,Pair.Both{{==},{==}})
