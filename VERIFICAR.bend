# Componentes puros implementados e seus testes. A prova do contrato completo
# do servidor nativo e uma obrigacao separada desta entrada de desenvolvimento.
import Base
import ./contrato/VERIFICAR.bend as ContratoOriginal
import ./src/Nucleo.bend as Nucleo
import ./src/Entrada.bend as Entrada
import ./src/Execucao.bend as Execucao
import ./src/Gerar.bend as Gerar
import ./src/Reificacao.bend as Reificacao
import ./src/Configuracao.bend as Configuracao
import ./src/Mensagens.bend as Mensagens
import ./src/Livre.bend as Livre
import ./src/Terminacao.bend as Terminacao
import ./tests/Codec.bend as TestesCodec
import ./tests/Requisicao.bend as TestesRequisicao
import ./tests/Credenciais.bend as TestesCredenciais
