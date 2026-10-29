import Base
import ../../../contrato/Logica.bend as L
import ../../../proof/RecepcaoLimites.bend as Q

# Confirmar 1 byte quando declarado=0 nao respeita o syscall limitado.
law falso:
  L.E<{Nat.is_le(1n,0n) == True{} : Bool}, {Nat.is_le(1n,1n) == True{} : Bool}>
def falso():
  Q.consumo_confirmado_respeita_declarado_e_limite(0n,0n,1n,1n,1n,{==},{==},{==})
