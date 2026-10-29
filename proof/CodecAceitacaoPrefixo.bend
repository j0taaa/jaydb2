# Corte do primeiro filho: a segmentacao e extraida da execucao REAL.
# A maquina local conserva os guards e e ligada passo a passo a src/Codec.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAceitacaoPilha.bend as J

def avancar_local(q: R.Quadro, fora: C.Pilha, b: U32) -> R.Quadro:
  R.Quadro{corpo, teto, m} = q
  +resto = C.diminuir64(corpo)
  +livre = C.diminuir64(teto)
  R.Quadro{resto, livre, J.passo_local(m, fora, b, resto, livre)}

def executar_local(bs: List<&2, U32>, +fora: C.Pilha, q: R.Quadro) -> R.Quadro:
  match bs:
    case Nil{}:
      q
    case Con{b, t}:
      executar_local(t, fora, avancar_local(q, fora, b))

def e_pronto(m: C.Maquina) -> Bool:
  match m:
    case C.Pronto{v}:
      True{}
    case _:
      False{}

def nao_emitiu_nao_esta_pronto(+m: C.Maquina, +fora: C.Pilha, -v: D.Valor,
  continua: J.Continua(m), igual: {J.ligar(m, fora) == C.Pronto{v} : C.Maquina}) -> Empty:
  match m:
    case C.Pronto{w}:
      continua
    case C.Tag{p}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, x => e_pronto(x), J.ligar(m, fora), C.Pronto{v}, igual))
    case C.TagNome{p}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, x => e_pronto(x), J.ligar(m, fora), C.Pronto{v}, igual))
    case C.Palavra{f, n, a, b, p}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, x => e_pronto(x), J.ligar(m, fora), C.Pronto{v}, igual))
    case C.Conteudo{nome, u, q, cp, s, p}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, x => e_pronto(x), J.ligar(m, fora), C.Pronto{v}, igual))
    case C.Invalido{}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, x => e_pronto(x), C.Invalido{}, C.Pronto{v}, igual))
    case C.Acima{}:
      F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, x => e_pronto(x), C.Acima{}, C.Pronto{v}, igual))

type Corte<-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64,
  -m: C.Maquina, -fora: C.Pilha, -v: D.Valor> is Type:
  Corte{prefixo: List<&2, U32>, sufixo: List<&2, U32>, filho: D.Valor,
    corpo_final: B.Numero64, teto_final: B.Numero64,
    bytes: {bs == B.concatenar(prefixo, sufixo) : List<&2, U32>},
    local: {executar_local(prefixo, fora, R.Quadro{corpo, teto, m}) ==
      R.Quadro{corpo_final, teto_final, C.Pronto{filho}} : R.Quadro},
    real: {R.executar(prefixo, R.Quadro{corpo, teto, J.ligar(m, fora)}) ==
      R.Quadro{corpo_final, teto_final, C.emitir(fora, filho)} : R.Quadro},
    restante: {R.maquina(R.executar(sufixo, R.Quadro{corpo_final, teto_final, C.emitir(fora, filho)})) == C.Pronto{v} : C.Maquina}}

def avanco_ligado(+m: C.Maquina, +fora: C.Pilha, +b: U32, +corpo: B.Numero64, +teto: B.Numero64,
  interna: J.Interna(m), continua: J.Continua(m)) ->
  {R.avancar(R.Quadro{corpo, teto, J.ligar(m, fora)}, b) ==
    R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro}:
  Equal.cong(C.Maquina, R.Quadro, x => R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), x},
    C.passo(J.ligar(m, fora), b, C.diminuir64(corpo), C.diminuir64(teto)),
    J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora),
    Equal.sym(C.Maquina,
      J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora),
      C.passo(J.ligar(m, fora), b, C.diminuir64(corpo), C.diminuir64(teto)),
      J.passo_local_ligado_e_o_passo_real(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto), interna, continua)))

def avancar_aceitacao(+b: U32, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +m: C.Maquina, +fora: C.Pilha, -v: D.Valor,
  avanco: {R.avancar(R.Quadro{corpo, teto, J.ligar(m, fora)}, b) ==
    R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
  aceito: {R.maquina(R.executar(Con{b, bs}, R.Quadro{corpo, teto, J.ligar(m, fora)})) == C.Pronto{v} : C.Maquina}) ->
  {R.maquina(R.executar(bs, R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)})) == C.Pronto{v} : C.Maquina}:
  %avanco : {R.maquina(R.executar(bs, _)) == C.Pronto{v} : C.Maquina}
  aceito

def levantar_corte(+b: U32, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +m: C.Maquina, +fora: C.Pilha, -v: D.Valor,
  +avanco: {R.avancar(R.Quadro{corpo, teto, J.ligar(m, fora)}, b) ==
    R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
  corte: Corte<bs, C.diminuir64(corpo), C.diminuir64(teto), J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v>) ->
  Corte<Con{b, bs}, corpo, teto, m, fora, v>:
  match corte:
    case Corte{+pre, +suf, +filho, +cf, +tf, bytes, local, real, restante}:
      Corte{Con{b, pre}, suf, filho, cf, tf,
        Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{b, t}, bs, B.concatenar(pre, suf), bytes), local,
        (%Equal.sym(R.Quadro, R.avancar(R.Quadro{corpo, teto, J.ligar(m, fora)}, b),
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)}, avanco) :
          {R.executar(pre, _) == R.Quadro{cf, tf, C.emitir(fora, filho)} : R.Quadro}
          real), restante}

def corte_imediato(+bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +filho: D.Valor, +fora: C.Pilha, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.emitir(fora, filho)})) == C.Pronto{v} : C.Maquina}) ->
  Corte<bs, corpo, teto, C.Pronto{filho}, fora, v>:
  Corte{Nil{}, bs, filho, corpo, teto, {==}, {==}, {==}, aceito}

def corte_vazio(+corpo: B.Numero64, +teto: B.Numero64, +m: C.Maquina, +fora: C.Pilha, -v: D.Valor,
  continua: J.Continua(m), aceito: {J.ligar(m, fora) == C.Pronto{v} : C.Maquina}) -> Corte<Nil{}, corpo, teto, m, fora, v>:
  L.ex_falso(Corte<Nil{}, corpo, teto, m, fora, v>, nao_emitiu_nao_esta_pronto(m, fora, v, continua, aceito))

def provar_avanco(+m: C.Maquina, +fora: C.Pilha, +b: U32, +corpo: B.Numero64, +teto: B.Numero64,
  interna: J.Interna(m), continua: J.Continua(m)) ->
  L.E<J.Interna(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
    {R.avancar(R.Quadro{corpo, teto, J.ligar(m, fora)}, b) ==
      R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro}>:
  F.com_par(L.E<J.Interna(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
      {R.avancar(R.Quadro{corpo, teto, J.ligar(m, fora)}, b) ==
        R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro}>,
    J.Interna(m), J.Interna(m), J.duplicar_interna(m, interna),
    primeira => segunda => L.Ambos{
      J.passo_local_preserva_interior(m, fora, b, C.diminuir64(corpo), C.diminuir64(teto), primeira),
      avanco_ligado(m, fora, b, corpo, teto, segunda, continua)})

law execucao_real_aceita_extrai_a_primeira_emissao:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for +fora: C.Pilha
  for -v: D.Valor
  for interna: J.Interna(m)
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, J.ligar(m, fora)})) == C.Pronto{v} : C.Maquina}
  Corte<bs, corpo, teto, m, fora, v>
def execucao_real_aceita_extrai_a_primeira_emissao(bs, corpo, teto, m, fora, v, interna, aceito):
  match bs m:
    case _ C.Pronto{+filho}:
      corte_imediato(bs, corpo, teto, filho, fora, v, aceito)
    case Nil{} C.Tag{+p}:
      corte_vazio(corpo, teto, C.Tag{p}, fora, v, Unit{}, aceito)
    case Nil{} C.TagNome{+p}:
      corte_vazio(corpo, teto, C.TagNome{p}, fora, v, Unit{}, aceito)
    case Nil{} C.Palavra{+f, +n, +a, +b, +p}:
      corte_vazio(corpo, teto, C.Palavra{f, n, a, b, p}, fora, v, Unit{}, aceito)
    case Nil{} C.Conteudo{+nome, +u, +q, +cp, +s, +p}:
      corte_vazio(corpo, teto, C.Conteudo{nome, u, q, cp, s, p}, fora, v, Unit{}, aceito)
    case Nil{} C.Invalido{}:
      corte_vazio(corpo, teto, C.Invalido{}, fora, v, Unit{}, aceito)
    case Nil{} C.Acima{}:
      corte_vazio(corpo, teto, C.Acima{}, fora, v, Unit{}, aceito)
    case Con{+b, +t} C.Tag{+p}:
      +estado = {C.Tag{p} : C.Maquina}
      F.com_par(Corte<Con{b, t}, corpo, teto, estado, fora, v>,
        J.Interna(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
        {R.avancar(R.Quadro{corpo, teto, J.ligar(estado, fora)}, b) ==
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
        provar_avanco(estado, fora, b, corpo, teto, interna, Unit{}),
        proxima => fato =>
          (+avanco = fato
           levantar_corte(b, t, corpo, teto, estado, fora, v, avanco,
             execucao_real_aceita_extrai_a_primeira_emissao(t, C.diminuir64(corpo), C.diminuir64(teto),
               J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v, proxima,
               avancar_aceitacao(b, t, corpo, teto, estado, fora, v, avanco, aceito)))))
    case Con{+b, +t} C.TagNome{+p}:
      +estado = {C.TagNome{p} : C.Maquina}
      F.com_par(Corte<Con{b, t}, corpo, teto, estado, fora, v>,
        J.Interna(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
        {R.avancar(R.Quadro{corpo, teto, J.ligar(estado, fora)}, b) ==
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
        provar_avanco(estado, fora, b, corpo, teto, interna, Unit{}),
        proxima => fato =>
          (+avanco = fato
           levantar_corte(b, t, corpo, teto, estado, fora, v, avanco,
             execucao_real_aceita_extrai_a_primeira_emissao(t, C.diminuir64(corpo), C.diminuir64(teto),
               J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v, proxima,
               avancar_aceitacao(b, t, corpo, teto, estado, fora, v, avanco, aceito)))))
    case Con{+b, +t} C.Palavra{+f, +n, +a, +c, +p}:
      +estado = {C.Palavra{f, n, a, c, p} : C.Maquina}
      F.com_par(Corte<Con{b, t}, corpo, teto, estado, fora, v>,
        J.Interna(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
        {R.avancar(R.Quadro{corpo, teto, J.ligar(estado, fora)}, b) ==
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
        provar_avanco(estado, fora, b, corpo, teto, interna, Unit{}),
        proxima => fato =>
          (+avanco = fato
           levantar_corte(b, t, corpo, teto, estado, fora, v, avanco,
             execucao_real_aceita_extrai_a_primeira_emissao(t, C.diminuir64(corpo), C.diminuir64(teto),
               J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v, proxima,
               avancar_aceitacao(b, t, corpo, teto, estado, fora, v, avanco, aceito)))))
    case Con{+b, +t} C.Conteudo{+nome, +u, +q, +cp, +s, +p}:
      +estado = {C.Conteudo{nome, u, q, cp, s, p} : C.Maquina}
      F.com_par(Corte<Con{b, t}, corpo, teto, estado, fora, v>,
        J.Interna(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
        {R.avancar(R.Quadro{corpo, teto, J.ligar(estado, fora)}, b) ==
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
        provar_avanco(estado, fora, b, corpo, teto, interna, Unit{}),
        proxima => fato =>
          (+avanco = fato
           levantar_corte(b, t, corpo, teto, estado, fora, v, avanco,
             execucao_real_aceita_extrai_a_primeira_emissao(t, C.diminuir64(corpo), C.diminuir64(teto),
               J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v, proxima,
               avancar_aceitacao(b, t, corpo, teto, estado, fora, v, avanco, aceito)))))
    case Con{+b, +t} C.Invalido{}:
      +estado = {C.Invalido{} : C.Maquina}
      F.com_par(Corte<Con{b, t}, corpo, teto, estado, fora, v>,
        J.Interna(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
        {R.avancar(R.Quadro{corpo, teto, J.ligar(estado, fora)}, b) ==
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
        provar_avanco(estado, fora, b, corpo, teto, interna, Unit{}),
        proxima => fato =>
          (+avanco = fato
           levantar_corte(b, t, corpo, teto, estado, fora, v, avanco,
             execucao_real_aceita_extrai_a_primeira_emissao(t, C.diminuir64(corpo), C.diminuir64(teto),
               J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v, proxima,
               avancar_aceitacao(b, t, corpo, teto, estado, fora, v, avanco, aceito)))))
    case Con{+b, +t} C.Acima{}:
      +estado = {C.Acima{} : C.Maquina}
      F.com_par(Corte<Con{b, t}, corpo, teto, estado, fora, v>,
        J.Interna(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto))),
        {R.avancar(R.Quadro{corpo, teto, J.ligar(estado, fora)}, b) ==
          R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), J.ligar(J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora)} : R.Quadro},
        provar_avanco(estado, fora, b, corpo, teto, interna, Unit{}),
        proxima => fato =>
          (+avanco = fato
           levantar_corte(b, t, corpo, teto, estado, fora, v, avanco,
             execucao_real_aceita_extrai_a_primeira_emissao(t, C.diminuir64(corpo), C.diminuir64(teto),
               J.passo_local(estado, fora, b, C.diminuir64(corpo), C.diminuir64(teto)), fora, v, proxima,
               avancar_aceitacao(b, t, corpo, teto, estado, fora, v, avanco, aceito)))))
