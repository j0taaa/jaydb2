# JayDB2

Implementação experimental de um banco em RAM que executa programas Bend acompanhados de provas contra as leis do administrador. Autentica a chamada pelo estado publicado, trabalha em uma proposta privada e publica estado e resposta completos numa única troca de referência. Atendimento serial por stdin/stdout, com código emitido pelo compilador oficial.

Cada chamada executa num processo nativo auxiliar. O host conserva o estado publicado e só aceita o resultado completo do auxiliar antes de publicar a proposta. O C emitido pelo compilador oficial não é reescrito para criar um runtime próprio.

O contrato tem **três limites de tamanho canônico: mensagem, estado e resposta**. Não há orçamento físico próprio, observador de memória ou prazo por etapa. Uma falha fatal pode encerrar a instância e perder seus dados em RAM.

## Instalação

Perfil de execução: Linux x86_64, Node 24 e Clang 19. O controlador é um binário Rust; Python é usado somente em ferramentas de desenvolvimento e testes.

O processo auxiliar Node usa `--stack_size=65536` e stack soft ilimitada. O launcher exige que o limite hard de stack do Linux já seja ilimitado; não altera os fontes do Node ou do Bend.

```sh
python3 tools/bootstrap.py --source /caminho/bend-2.0.39 --kernel /caminho/bendtt
python3 tools/bend.py version
make build
./jaydb2 --configuration examples/sem-observacoes/Configuration.bend \
  --seed examples/sem-observacoes/Seed.bend
```

A distribuição usada é **Bend 2.0.39 oficial**. Os cinco fontes oficiais e os binários estão identificados em `tools/admission/toolchain.lock.json`. No perfil Linux x86_64, o executável Bend tem SHA-256 `2ec160fa4486d33aff51e9eedcc294d6b531dc10c279c00b0c00685dae2045cd`; o BendTT original tem SHA-256 `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`.

Não há frontend, tradutor, compilador ou kernel BendTT modificado pelo JayDB. O carregamento dos módulos TypeScript oficiais apenas remove a sintaxe TypeScript pelo transformador do Node. Não há build de verificador derivado, addon V8 ou cache de fontes adaptadas para instalar. As capacidades e limitações das ferramentas oficiais são mantidas.

`server/main.rs` mantém o estado publicado em RAM e atende os frames em série. O helper Node congela o ambiente público, verifica e compila os workers; o seed aparece somente na compilação da inicialização. Cada worker recebe bytes por pipe e termina antes de uma proposta completa substituir o estado publicado. A execução do servidor não carrega Python.

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

`make verify` verifica os agregados gerais nos dois modos oficiais e seis mutações causais. `make test` cobre as fronteiras que essas provas não verificam: admissão/emissão do mesmo Book, execução, publicação/rollback e enquadramento. Logs, C compilado e snapshots não são versionados como suítes paralelas. Resultados históricos obtidos com os adaptadores retirados não atestam o caminho oficial atual.

As [provas gerais](proof/README.md) incluem a equivalência canônica do Codec. A [admissão](tools/admission/README.md) usa o frontend, Safe e BendTT oficiais, sem reescrever provas para ampliar o fragmento aceito. A correspondência geral do executável completo com `Contrato(a,k)` ainda não foi demonstrada.

A [especificação](ESPECIFICACAO.md), o [contrato Bend](contrato/README.md), o [serviço](tools/service/SIMPLE_SERVICE.md) e o [runtime](native/SIMPLE_RUNTIME.md) descrevem o projeto. Os 18 originais permanecem em `history/contrato-v1/`; implementações e capturas retiradas da árvore corrente podem ser consultadas no histórico Git.
