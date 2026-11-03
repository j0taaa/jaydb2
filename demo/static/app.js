const $ = (selector) => document.querySelector(selector);
const $$ = (selector) => [...document.querySelectorAll(selector)];
let session;
let sources;
let eventStream;
let busy = false;
let selectedSequence;
let followLatest = true;
let resultTab = 'response';
let showJSON = false;
let previousState;
let renderedStateHash;
let renderedHistory = '';

async function api(path, body) {
  const response = await fetch(path, body === undefined ? {cache: 'no-store'} : {
    method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)
  });
  const data = await response.json();
  if (!response.ok) throw new Error(data.error || `HTTP ${response.status}`);
  return data;
}

function error(message) {
  $('#error').textContent = message;
  $('#error').hidden = false;
}

function download(name, text) {
  const url = URL.createObjectURL(new Blob([text], {type: 'text/plain;charset=utf-8'}));
  const link = document.createElement('a');
  link.href = url;
  link.download = name;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function controls() {
  const running = busy || session?.running;
  $('#run').disabled = running || !session?.alive;
  $('#run').classList.toggle('working', Boolean(running));
  $('#run').textContent = running ? 'Running…' : 'Run transaction ↵';
  $('#reset').disabled = Boolean(running);
  $('#request-note').textContent = running ? 'Waiting for JayDB2.' : 'Program and proof go to JayDB2 admission.';
  $('#database-status').textContent = session?.alive ? (session.running ? 'Executing request' : 'Ready') : 'Unavailable';
  $('#connection').textContent = session?.alive ? (session.running ? 'Running' : 'Connected') : 'Offline';
  $('#connection').className = `connection ${session?.alive ? 'online' : 'offline'}`;
  $('#process').textContent = session?.database_pid ? `PID ${session.database_pid}` : '';
}

function table(rows, collection) {
  const element = document.createElement('table');
  const keys = [...new Set(rows.flatMap((row) => Object.keys(row)))];
  const columns = keys.includes('id') ? ['id', ...keys.filter((key) => key !== 'id')] : keys;
  if (!columns.length) {
    const empty = document.createElement('p');
    empty.className = 'placeholder';
    empty.textContent = 'Empty collection.';
    return empty;
  }
  const head = document.createElement('thead');
  const header = document.createElement('tr');
  for (const column of columns) {
    const th = document.createElement('th');
    th.textContent = column;
    header.append(th);
  }
  head.append(header);
  element.append(head);
  const body = document.createElement('tbody');
  for (const row of rows) {
    const tr = document.createElement('tr');
    for (const column of columns) {
      const td = document.createElement('td');
      const value = row[column];
      td.textContent = typeof value === 'string' ? value : JSON.stringify(value) ?? '—';
      const before = previousState?.usuarios?.find((previous) => previous.id === row.id);
      if (collection === 'usuarios' && before && JSON.stringify(before[column]) !== JSON.stringify(value)) td.className = 'changed';
      if (collection === 'usuarios' && column === 'credencial') {
        const use = document.createElement('button');
        use.textContent = 'Use';
        use.title = `Use ${row.id}’s current credential`;
        use.addEventListener('click', () => {$('#credential').value = value;});
        td.append(use);
      }
      tr.append(td);
    }
    body.append(tr);
  }
  element.append(body);
  return element;
}

function renderData(force = false) {
  const inspection = session?.inspection;
  if (!inspection?.state) return;
  $('#live-status').textContent = !session.alive ? 'Offline' : inspection.error ? 'Inspector unavailable' : 'Live';
  $('#live-status').className = `live ${session.alive && !inspection.error ? 'connected' : ''}`;
  $('#state-size').textContent = `${inspection.canonical_bytes.toLocaleString()} bytes`;
  $('#snapshot-sequence').textContent = `Snapshot ${inspection.sequence}`;
  $('#state-time').textContent = new Date(inspection.observed_at * 1000).toLocaleTimeString();
  $('#state-hash').textContent = inspection.sha256;
  $('#state-json').textContent = inspection.state_json;
  if (!force && renderedStateHash === inspection.sha256) return;
  const state = inspection.state;
  const collections = [{name: 'usuarios', rows: state.usuarios}, ...(state.tabelas || []).map((item) => ({name: item.nome, rows: item.linhas}))];
  const current = $('#collection').value;
  $('#collection').replaceChildren();
  for (const item of collections) $('#collection').add(new Option(item.name, item.name));
  if (collections.some((item) => item.name === current)) $('#collection').value = current;
  const selected = collections.find((item) => item.name === $('#collection').value);
  $('#row-count').textContent = `${selected.rows.length} rows`;
  $('#data-table').replaceChildren(table(selected.rows, selected.name));
  renderedStateHash = inspection.sha256;
  previousState = state;
}

function receipt() {
  return session?.receipts?.find((item) => item.sequence === selectedSequence);
}

function resultContent() {
  const item = receipt();
  if (!item) return {text: 'No response.', filename: 'response.json'};
  switch (resultTab) {
    case 'diagnostics': return {text: item.diagnostic ? `${item.diagnostic.code}\n\n${item.diagnostic.message}` : 'No error diagnostic returned.', filename: 'diagnostics.txt'};
    case 'request': return {text: item.request_json, filename: 'request.json'};
    case 'code': return {text: item.request.codigo, filename: 'Client.bend'};
    case 'proof': return {text: item.request.prova, filename: 'ClientProof.bend'};
    case 'bindings': return {text: item.generated_sources?.['Bindings.bend'] || 'No bindings generated: authentication did not reach admission.', filename: 'Bindings.bend'};
    case 'context': return {text: item.generated_sources?.['Instance.bend'] || 'No context generated: authentication did not reach admission.', filename: 'Instance.bend'};
    case 'before': return {text: item.state_before_json, filename: 'state-before.json'};
    case 'after': return {text: item.state_after_json, filename: 'state-after.json'};
    default: return {text: item.response_json, filename: 'response.json'};
  }
}

function renderResult() {
  const item = receipt();
  $('#result-content').textContent = resultContent().text;
  $('#download-result').disabled = !item;
  $('#result-meta').textContent = item ? `#${item.sequence} · ${(item.duration_ms / 1000).toFixed(2)} s · ${item.request_bytes.toLocaleString()} B → ${item.response_bytes.toLocaleString()} B` : '';
  for (const button of $$('[data-result]')) {
    const active = button.dataset.result === resultTab;
    button.classList.toggle('active', active);
    button.setAttribute('aria-pressed', String(active));
    if (button.dataset.result === 'diagnostics') button.textContent = item?.diagnostic ? 'Diagnostics ●' : 'Diagnostics';
  }
  for (const button of $$('.history button')) button.classList.toggle('active', Number(button.dataset.sequence) === selectedSequence);
}

function renderHistory() {
  const receipts = session?.receipts || [];
  $('#request-count').textContent = receipts.at(-1)?.sequence || 0;
  if (followLatest || !receipts.some((item) => item.sequence === selectedSequence)) selectedSequence = receipts.at(-1)?.sequence;
  const key = receipts.map((item) => item.sequence).join(',');
  if (renderedHistory !== key) {
    $('#history').replaceChildren();
    if (!receipts.length) {
      const empty = document.createElement('p');
      empty.className = 'placeholder';
      empty.textContent = 'No requests.';
      $('#history').append(empty);
    }
    for (const item of [...receipts].reverse()) {
      const row = document.createElement('button');
      row.dataset.sequence = item.sequence;
      const number = document.createElement('span');
      number.className = 'history-number';
      number.textContent = `#${item.sequence}`;
      const content = document.createElement('span');
      content.textContent = new Date(item.timestamp * 1000).toLocaleTimeString();
      const detail = document.createElement('small');
      detail.textContent = `${(item.duration_ms / 1000).toFixed(2)} s · ${item.request_bytes.toLocaleString()} B`;
      content.append(detail);
      const status = document.createElement('span');
      status.className = `history-status ${item.response.status === 'sucesso' ? '' : item.response.status === 'recusa' ? 'refused' : 'rejected'}`;
      status.textContent = item.response.status;
      row.append(number, content, status);
      row.addEventListener('click', () => {
        selectedSequence = item.sequence;
        followLatest = selectedSequence === receipts.at(-1)?.sequence;
        renderResult();
      });
      $('#history').append(row);
    }
    renderedHistory = key;
  }
  renderResult();
}

function updateSession(data) {
  session = data;
  controls();
  if (!data.alive) {$('#live-status').textContent = 'Offline'; $('#live-status').className = 'live';}
  renderData();
  renderHistory();
  if (data.inspection?.error && data.alive) error(`Inspector: ${data.inspection.error}. Displayed state may be stale.`);
}

function subscribe() {
  eventStream?.close();
  const pid = session.database_pid;
  eventStream = new EventSource('/api/events');
  eventStream.onmessage = (event) => {
    const data = JSON.parse(event.data);
    if (session?.database_pid !== pid) return;
    updateSession(data);
    if (!data.alive) eventStream.close();
  };
  eventStream.onerror = async () => {
    $('#live-status').textContent = 'Reconnecting…';
    $('#live-status').className = 'live';
    try {
      const data = await api('/api/session');
      if (session?.database_pid !== pid) return;
      if (!data.alive) eventStream.close();
      updateSession(data);
    } catch {$('#live-status').textContent = 'Disconnected';}
  };
}

function definition(file, name) {
  const lines = sources.files[file]?.split('\n') || [];
  const start = lines.findIndex((line) => line.startsWith(`def ${name}(`));
  if (start < 0) return `Definition not found: ${file}:${name}`;
  const end = lines.findIndex((line, index) => index > start && /^(def |type |law )/.test(line));
  return lines.slice(start, end < 0 ? undefined : end).join('\n').trimEnd();
}

function showSource() {
  $('#source-code').textContent = sourceFiles()[$('#source-file').value] || '';
}

function sourceFiles() {
  return {...sources.files, 'Client.bend': sources.program, 'ClientProof.bend': sources.proof, 'Seed.bend': sources.seed};
}

function renderSources() {
  const schema = sources.schema;
  $('#schema-key').textContent = schema.usuarios?.primary_key || 'See source';
  $('#schema-columns').replaceChildren();
  for (const column of schema.usuarios?.columns || []) {
    const row = document.createElement('tr');
    for (const value of [column.name, column.type, column.optional ? 'yes' : 'no']) {
      const cell = document.createElement('td');
      cell.textContent = value;
      row.append(cell);
    }
    $('#schema-columns').append(row);
  }
  $('#application-schema').textContent = definition('Configuration.bend', 'esquema');
  $('#schema-source').textContent = definition('Dados.bend', 'esquema_usuarios');
  $('#limits').replaceChildren();
  for (const [name, value] of Object.entries(sources.limits || {})) {
    const pair = document.createElement('div');
    const term = document.createElement('dt');
    term.textContent = name;
    const content = document.createElement('dd');
    content.textContent = value.toLocaleString();
    pair.append(term, content);
    $('#limits').append(pair);
  }
  $('#law-source').textContent = sources.configuration;
  $('#structural-source').textContent = definition('Dados.bend', 'estrutura');
  $('#credential-law-source').textContent = definition('Dados.bend', 'credenciais_validas');
  $('#valid-source').textContent = definition('Requisitos.bend', 'Valido');
  $('#certificate-source').textContent = definition('Requisitos.bend', 'Certifica');
  $('#termination-source').textContent = definition('Interface.bend', 'ProgramaTermina');
  $('#source-file').replaceChildren();
  for (const name of Object.keys(sourceFiles()).sort()) $('#source-file').add(new Option(name, name));
  $('#source-file').value = 'Configuration.bend';
  showSource();
  $('#environment-identity').textContent = sources.environment.identity;
  $('#environment-files').textContent = JSON.stringify(sources.environment.publicFiles, null, 2);
}

function editorSize() {
  for (const name of ['code', 'proof']) $(`#${name}-size`).textContent = `${new TextEncoder().encode($(`#${name}`).value).length.toLocaleString()} B`;
}

function loadPreset() {
  if (!sources) return;
  const preset = $('#preset').value;
  $('#code').value = preset === 'forbidden' ? sources.forbidden_program : sources.program;
  $('#proof').value = sources.proof;
  $('#arguments').value = preset === 'rotate' ? '"alice-new"' : preset === 'verify' ? JSON.stringify($('#credential').value) : 'null';
  editorSize();
}

async function connect() {
  busy = true;
  controls();
  $('#connection').textContent = 'Starting database…';
  try {
    updateSession(await api('/api/session', {}));
    sources = await api('/api/sources');
    renderSources();
    loadPreset();
    const alice = session.inspection.state.usuarios.find((row) => row.id === 'alice');
    if (alice) $('#credential').value = alice.credencial;
    subscribe();
  } catch (failure) {
    error(failure.message);
    $('#connection').textContent = 'Unavailable';
  } finally {
    busy = false;
    controls();
  }
}

$('#request-form').addEventListener('submit', async (event) => {
  event.preventDefault();
  if (busy || session?.running || !session?.alive) return;
  const draft = {action: 'custom', credential: $('#credential').value, arguments_json: $('#arguments').value,
    code: $('#code').value, proof: $('#proof').value};
  busy = true;
  followLatest = true;
  $('#error').hidden = true;
  controls();
  try {
    const item = await api('/api/execute', draft);
    updateSession(await api('/api/session'));
    selectedSequence = item.sequence;
    resultTab = item.diagnostic ? 'diagnostics' : 'response';
    renderResult();
    const before = JSON.parse(item.state_before_json);
    const after = JSON.parse(item.state_after_json);
    const actor = before.usuarios.find((row) => row.credencial === draft.credential);
    const current = after.usuarios.find((row) => row.id === actor?.id);
    if (current && $('#credential').value === draft.credential) $('#credential').value = current.credencial;
  } catch (failure) {
    error(`${failure.message} No automatic retry.`);
    try {updateSession(await api('/api/session'));} catch {$('#connection').textContent = 'Disconnected';}
  } finally {
    busy = false;
    controls();
  }
});

for (const button of $$('[data-view]')) button.addEventListener('click', () => {
  for (const tab of $$('[data-view]')) {
    const active = tab === button;
    tab.classList.toggle('active', active);
    tab.setAttribute('aria-pressed', String(active));
    $(`#view-${tab.dataset.view}`).hidden = !active;
  }
});
for (const button of $$('[data-result]')) button.addEventListener('click', () => {resultTab = button.dataset.result; renderResult();});
$('#collection').addEventListener('change', () => renderData(true));
$('#toggle-json').addEventListener('click', () => {
  showJSON = !showJSON;
  $('#state-json').hidden = !showJSON;
  $('#data-table').hidden = showJSON;
  $('#toggle-json').textContent = showJSON ? 'Table' : 'JSON';
});
$('#load-preset').addEventListener('click', loadPreset);
$('#source-file').addEventListener('change', showSource);
$('#download-source').addEventListener('click', () => {if (sources) download($('#source-file').value, $('#source-code').textContent);});
$('#download-result').addEventListener('click', () => {const content = resultContent(); download(content.filename, content.text);});
$('#download-draft').addEventListener('click', () => download('jaydb2-request.json', JSON.stringify({action: 'custom',
  credential: $('#credential').value, arguments_json: $('#arguments').value, code: $('#code').value, proof: $('#proof').value}, null, 2)));
for (const name of ['code', 'proof']) {
  $(`#${name}`).addEventListener('input', editorSize);
  $(`#${name}`).addEventListener('keydown', (event) => {
    if (event.key === 'Tab' && !event.shiftKey) {
      event.preventDefault();
      event.target.setRangeText('  ', event.target.selectionStart, event.target.selectionEnd, 'end');
      editorSize();
    }
  });
  $(`[data-upload=${name}]`).addEventListener('click', () => $(`#upload-${name}`).click());
  $(`#upload-${name}`).addEventListener('change', async (event) => {
    const file = event.target.files[0];
    if (!file) return;
    if (file.size > 262144) return error('File exceeds the HTTP body limit.');
    $(`#${name}`).value = await file.text();
    editorSize();
  });
}
document.addEventListener('keydown', (event) => {
  if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') {
    event.preventDefault();
    if (!$('#run').disabled) $('#request-form').requestSubmit();
  }
});
$('#reset').addEventListener('click', () => $('#reset-dialog').showModal());
$('#cancel-reset').addEventListener('click', () => $('#reset-dialog').close());
$('#confirm-reset').addEventListener('click', async () => {
  $('#reset-dialog').close();
  eventStream?.close();
  busy = true;
  controls();
  try {
    await api('/api/reset', {});
    session = null;
    previousState = null;
    renderedStateHash = null;
    renderedHistory = null;
    selectedSequence = null;
    resultTab = 'response';
    followLatest = true;
    $('#error').hidden = true;
    await connect();
  } catch (failure) {error(failure.message); busy = false; controls();}
});
window.addEventListener('pagehide', () => eventStream?.close());
connect();
