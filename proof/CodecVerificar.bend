# Agregado dos teoremas gerais do Codec, incluindo equivalencia canonica.
# Nao constroi Ambiente nem afirma Contrato do executavel/host.
import Base
import ./Codec.bend as Validade
import ./CodecInteiros.bend as Inteiros
import ./CodecTextos.bend as Textos
import ./CodecTextoAceito.bend as TextoAceito
import ./CodecAridades.bend as Aridades
import ./CodecMinimos.bend as Minimos
import ./CodecUTF8InversaTexto.bend as UTF8Inversa
import ./CodecUTF8InversaOctetos.bend as Octetos

import ./CodecMinimosPilha.bend as MinimosPilha
import ./CodecSomasMinimos.bend as SomasMinimos
import ./CodecLimitesParciais.bend as LimitesParciais
import ./CodecLimitesPilha.bend as LimitesPilha
import ./CodecLimitesCopia.bend as LimitesCopia
import ./CodecReservas.bend as Reservas
import ./CodecComposicao.bend as Composicao
import ./CodecSequencias.bend as Sequencias
import ./CodecLocais.bend as Locais
import ./CodecCampos.bend as Campos
import ./CodecRegistros.bend as Registros
import ./CodecNomesLocais.bend as NomesLocais
import ./CodecMontagemVerificar.bend as Montagem
import ./CodecOctetos.bend as OctetosOriginais
import ./CodecPublico.bend as Publico
import ./CodecCompleto.bend as Completo
import ./CodecPrimitivos.bend as Primitivos
import ./CodecRelaxar.bend as Relaxar
import ./CodecRecusas.bend as Recusas
import ./CodecAceitacao.bend as Aceitacao
import ./CodecLei2.bend as RelacaoOriginal
