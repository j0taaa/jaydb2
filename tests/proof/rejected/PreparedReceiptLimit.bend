# An oversized control receipt cannot register a program.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedRegistry.bend as G

law false_oversized_receipt_registers:
  {H.registry(H.register_fits(False{}, D.State{Nil{}, Nil{}},
    G.Entry{"instance", "handle", "source", "proof", False{}, "seal"}, Nil{})) ==
    [G.Entry{"instance", "handle", "source", "proof", False{}, "seal"}] : List<&2, G.Entry>}
def false_oversized_receipt_registers():
  {==}
