import Base
import ./Dados.bend as D
import ./Requisitos.bend as R
import ./Logica.bend as L
import ./Configuration.bend as C

def estado() -> D.Estado:
  D.Estado{Nil{}, [
    D.Linha{"alice", [D.Campo{"credencial", D.VTexto{"alice-token"}},
      D.Campo{"id", D.VTexto{"alice"}}, D.Campo{"tipo", D.VTexto{"usuario"}}]},
    D.Linha{"bob", [D.Campo{"credencial", D.VTexto{"bob-token"}},
      D.Campo{"id", D.VTexto{"bob"}}, D.Campo{"tipo", D.VTexto{"usuario"}}]}]}

law inicial_valido:
  R.Valido(C.config(), estado())
def inicial_valido():
  L.Ambos{{==}, L.Ambos{Unit{}, Unit{}}}
