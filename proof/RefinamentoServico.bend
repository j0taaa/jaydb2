# Reabertura das guardas do mesmo observador; nao concede leis do banco.
import Base
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L

# As guardas pertencem a observacao; nao se assume E<Refl,P> = P.
def observacao_guardada(-G: Type, -H: Type, -ob: Nat -> I.Fato -> Type,
  t: Nat, f: I.Fato) -> Type:
  L.E<G, L.E<H, ob(t, f)>>

def retirar_guardas(-G: Type, -H: Type, -P: Type, prova: L.E<G, L.E<H, P>>) -> P:
  match prova:
    case L.Ambos{g, L.Ambos{h, p}}: p

def com_guardas(-G: Type, -H: Type, -P: Type,
  guardas: L.E<G, H>, prova: P) -> L.E<G, L.E<H, P>>:
  match guardas:
    case L.Ambos{g, h}: L.Ambos{g, L.Ambos{h, prova}}
