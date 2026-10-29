# Serviço com três limites lógicos

A entrada ativa é `jaydb2.py` → `controller.Database` →
`abi_simple.SimpleModule`. A configuração contém somente `mensagem`, `estado`
e `resposta`, medidos em bytes canônicos. Igualdade com o teto é permitida.
Não há orçamento físico, relógio por etapa ou prazo de execução.

## Caminho da chamada

1. O host lê o enquadramento e verifica o teto de mensagem.
2. Os módulos Bend compilados decodificam e autenticam pelo estado publicado.
3. A admissão verifica fonte, dependências e prova contra a configuração,
   contexto e argumentos reais; o emissor recebe o mesmo Book admitido.
4. O builder confere o hash do C. O host confere o hash do DSO e seu descritor,
   que identifica o C emitido e os insumos do build.
5. O programa executa sincronicamente na thread principal do mesmo processo.
   O estado de trabalho é privado; o Codec é o programa Bend compilado.
6. O host copia a saída completa, libera seu lease, fecha o módulo temporário,
   valida estado/resposta e remove o diretório de compilação.
7. O sucesso substitui uma referência por `Published(state, response)`
   imutável. Toda recusa ou falha anterior conserva a publicação anterior.
8. A entrega vem depois. Uma falha de entrega conserva o par publicado e
   encerra o canal, sem repetição automática nem deduplicação.

Os diretórios de compilação recebem fonte, prova e dados públicos da admissão;
não recebem o estado privado da instância. O seed só participa da inicialização,
é removido depois e não entra na identidade pública do ambiente.

## Ownership e falhas

Cada módulo possui seu DSO e a saída da chamada corrente. Context managers
concluem a limpeza antes de devolver uma proposta ao publicador. Não existem
shims C de loading/lifecycle, instalação adicional, recibos ou registries de
recuperação. `run` e `close` recusam uso reentrante. O DSO permanece carregado
enquanto uma chamada ou saída ainda o possui.

Os helpers confiáveis usam sessão própria, pipes e um dono Python curto.
`waitid(WNOWAIT)` conserva a identidade do líder até `killpg`, antes do reap.
A pausa de 50 ms do seletor observa o fim do líder quando um descendente
mantém um pipe aberto; ela não limita a duração da compilação.

O teto de saída é lógico e não pré-aloca memória. Status nativo 7 permite nova
chamada após exceder esse teto. Falhas nativas de alocação, representação,
efeito ou invariante tornam a instância inutilizável. Ownership incerto escapa
do mapper de respostas, impede publicação e exige encerrar a instância; uma
operação possivelmente consumida não é repetida.

O perfil é uma CLI Linux serial, com ferramentas e host confiáveis. Não promete
recuperar handlers Python arbitrários, cancelamento de threads, falhas fatais
ou morte do processo. Uma falha fatal pode encerrar o banco RAM sem resposta.

`prepare_entry()` exige Linux x86_64, páginas de 4096 bytes, thread principal,
SIGCHLD padrão e ausência de loaders externos. Permite o crescimento da stack
principal e desliga core dumps. Os helpers usam `/usr/bin/python3 -I -S -B`
com bootstrap fixo e root materializado dos bytes imutáveis do ambiente;
argumentos são elementos de argv, sem shell. O launcher de admissão faz exec
do Node. `build_simple.py` usa Clang 19 com `--no-default-config` e
`-fstack-clash-protection`, registrando hashes dos insumos e flags. A instalação
dessas ferramentas e bibliotecas faz parte do perfil confiável.

## Verificação

`make test-host` cobre publicação, rollback e enquadramento com fixtures de
fronteira. `make test-integration` admite, compila e executa Bend real.
`make test-native` cobre o runtime e a ABI com C emitido de poucos Books.
Esses controles não provam a correspondência geral do compilador/runtime nem
o contrato inteiro. Hashes identificam artefatos; não substituem essas provas.
