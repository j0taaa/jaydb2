# JayDB2

Banco em RAM que executa programas Bend acompanhados de provas contra as leis do administrador. Autentica a chamada pelo estado publicado, trabalha em uma proposta privada e publica estado e resposta completos numa única troca de referência. Atendimento serial por stdin/stdout, CPU no processo do banco.

O contrato tem **três limites de tamanho canônico: mensagem, estado e resposta**. Não há orçamento físico próprio, observador de memória ou prazo por etapa. Uma falha fatal pode encerrar a instância e perder seus dados em RAM.

## Instalação

Perfil atual: Linux x86_64, páginas de 4096 bytes, Python 3.12, Clang/Clang++ 19 e headers Node em `/usr/include/node`. A versão exata de Node está em `tools/admission/frontend.lock.json`. O processo principal usa stack Linux expansível; o hard limit deve permitir esse perfil.

```sh
python3 tools/bootstrap.py --source /caminho/bend-2.0.39 --kernel /caminho/bendtt
python3 tools/bend.py version
node tools/admission/build-frontend.mjs
node tools/verifier/build.mjs
python3 jaydb2.py --configuration examples/sem-observacoes/Configuration.bend \
  --seed examples/sem-observacoes/Seed.bend
```

É necessário fornecer o BendTT original de SHA-256 `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`. O derivado usa Lean 4.34.0 instalado pelo Elan em `~/.elan/toolchains/leanprover--lean4---v4.34.0/bin`. Fontes, ferramentas e artefatos executados são fixados por hash; os builds normais não atualizam os locks. `--write-lock` é uma alteração deliberada da identidade, acompanhada de revisão.

Não há shims de loading/lifecycle para instalar. Bibliotecas e subprocessos têm um dono síncrono por escopo. Uma operação de ownership incerto encerra o uso da instância, sem tentar recuperar uma publicação.

## Cliente

```sh
python3 tools/client.py --codigo examples/sem-observacoes/Client.bend \
  --prova examples/sem-observacoes/ClientProof.bend --credencial demo
```

O comando escreve uma mensagem canônica enquadrada. `python3 tools/client.py --decode` lê uma resposta e imprime JSON. Configuração e dependências são públicas e imutáveis; seed e estado corrente permanecem privados.

## Verificação

```sh
make verify-contract
make verify
make test
```

`make verify` verifica os agregados gerais nos dois modos oficiais e seis mutações causais. `make test` cobre as fronteiras que essas provas não verificam: admissão/emissão do mesmo Book, execução nativa, ownership normal, publicação/rollback e enquadramento. Os programas dos testes C são gerados de pequenos fixtures Bend; C compilado, logs e snapshots não são versionados como suítes paralelas.

As [provas gerais](proof/README.md) incluem a equivalência canônica do Codec. A [admissão](tools/admission/README.md) mantém os corpos físicos e seus vínculos de origem, mas ainda tem formas estruturais não implementadas; uma prova válida com Bool casado antes de recursão em Nat é uma pendência conhecida. A correspondência geral do executável completo com `Contrato(a,k)` ainda não foi demonstrada.

A [especificação](ESPECIFICACAO.md), o [contrato Bend](contrato/README.md), o [serviço](tools/service/SIMPLE_SERVICE.md) e o [runtime](native/SIMPLE_RUNTIME.md) descrevem o caminho atual. Os 18 originais permanecem em `history/contrato-v1/`; implementações e capturas retiradas da árvore corrente podem ser consultadas no histórico Git.
