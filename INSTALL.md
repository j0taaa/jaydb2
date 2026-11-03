# Instalação e primeira sessão

## Ambiente testado

A versão experimental 0.1.0 usa Linux x86_64 (Ubuntu 24.04), Node 24.19,
Clang 19, Rust/Cargo 1.98 e Python 3.12. O serviço é Rust + Node + executáveis
Bend; Python é usado na instalação e no cliente de demonstração.

Confira as ferramentas já instaladas:

```sh
node --version
/usr/bin/clang-19 --version
rustc --version
cargo --version
python3 --version
ulimit -Hs
```

O último comando deve informar `unlimited`. O launcher configura o limite soft
da stack; um limite hard finito exige uma sessão/perfil do Linux que permita
esse ajuste. Isso não modifica Bend ou Node. Git e GitHub CLI (`gh`) são usados
pelos comandos de download abaixo. Se o repositório exigir acesso, autentique
o `gh` e use uma conta autorizada.

## Obter a versão e as ferramentas Bend

```sh
gh repo clone j0taaa/jaydb2
cd jaydb2
git checkout v0.1.0
mkdir -p .tools/bootstrap
gh release download v0.1.0 --repo j0taaa/jaydb2 \
  --pattern bendtt-linux-x86_64.tar.gz --dir .tools/bootstrap
tar -xzf .tools/bootstrap/bendtt-linux-x86_64.tar.gz -C .tools/bootstrap
python3 tools/bootstrap.py \
  --kernel .tools/bootstrap/bendtt-linux-x86_64/bendtt
python3 tools/bend.py version
make build
```

O bootstrap baixa e confere os fontes oficiais Bend 2.0.39. `tools/bend.py`
baixa a distribuição oficial e deve imprimir `bend 2.0.39`. Nenhuma ferramenta
é instalada globalmente. O arquivo de BendTT da release é uma distribuição
pelo JayDB do artefato sem patches já fixado no projeto, acompanhado do fonte
e das licenças; não é apresentado como um binário publicado pelo upstream.

O instalador exige SHA-256
`e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`
para o BendTT. Os cinco fontes e o executável Bend também são conferidos contra
[toolchain.lock.json](tools/admission/toolchain.lock.json). Um binário diferente
é recusado; não há compilação de um verificador substituto durante a instalação.

Se já possui os fontes e o kernel exatos, pode usar:

```sh
python3 tools/bootstrap.py --source /caminho/bend-2.0.39 \
  --kernel /caminho/bendtt
```

## Usar a aplicação de exemplo

```sh
make demo
```

Esse comando inicia uma instância em RAM com Alice e Bob, envia cinco
requisições e encerra o servidor depois de receber todas as respostas:

```json
{"status": "sucesso", "valor": "alice-nova"}
{"status": "autenticacao", "valor": null}
{"status": "recusa", "valor": "cancelado"}
{"status": "sucesso", "valor": "alice-final"}
{"status": "sucesso", "valor": "bob-nova"}
```

A quarta chamada usa a mesma credencial da terceira: a escrita provisória
feita antes da recusa foi descartada. A quinta usa outra identidade.
[O exemplo](examples/acessos/README.md) explica os fontes e a prova universal.
As leis do administrador restringem cada leitura e escrita, inclusive antes
de uma recusa. Os testes existentes incluem a tentativa proibida de ler outra
conta e recusar depois.

Cada execução de `make demo` começa do seed. Encerrar o processo perde a
instância em RAM. O exemplo não grava um banco em disco nem inicia um listener
de rede.

Para sua própria aplicação, forneça configuração e seed com prova de validade,
e envie programas/provas pelo mesmo protocolo de stdin/stdout. O script
[demo.sh](examples/acessos/demo.sh) mostra a conexão completa; o cliente
`tools/client.py` gera frames e decodifica respostas. A função Bend do cliente
acessa os dados exclusivamente pelas operações do banco.

## Verificar a instalação

```sh
make verify-contract
make verify
make test
```

São comandos separados do build. `make verify` exige a composição das oito leis
nos dois checkers oficiais; `make test` exercita a integração real. Os limites
conhecidos do runtime oficial estão em [SIMPLE_RUNTIME.md](native/SIMPLE_RUNTIME.md).
O alcance das provas e os contratos da integração estão em
[CONTRATO_SERVICO.md](proof/CONTRATO_SERVICO.md).
