import { spawn } from 'node:child_process';
import { constants } from 'node:buffer';
import type { Readable, Writable } from 'node:stream';
import { decode, frame, preparedFrame } from './codec.ts';
import type { Value } from './codec.ts';

export type Status = 'input' | 'authentication' | 'certificate' | 'data' | 'limit' | 'failure' | 'refusal' | 'success' | 'prepared' | 'invalidated';
export interface Response { status: Status; value: Value }
export interface Request { credential: string; code: string; proof: string; arguments: Value }
export interface Preparation { credential: string; code: string; proof: string }
export interface Execution { credential: string; handle: string; arguments: Value }
export interface Invalidation { credential: string; handle: string }

/** A client failure is not a database rollback receipt. Submitted work may commit. */
export class JaydbError extends Error {
  readonly outcome = 'unknown' as const;
}
export class TransportError extends JaydbError {
  constructor(message: string, options?: ErrorOptions) { super(message, options); this.name = 'TransportError'; }
}
export class ProtocolError extends JaydbError {
  constructor(message: string, options?: ErrorOptions) { super(message, options); this.name = 'ProtocolError'; }
}

export interface ClientOptions {
  input: Writable;
  output: Readable;
  /** Optional external process completion; reject if the process exits unsuccessfully. */
  completion?: Promise<void>;
  /** Local allocation cap, separate from the administrator's response limit. Default 16 MiB. */
  maxResponseBytes?: number;
  /** Local bound on outstanding requests. Default 64. */
  maxPendingRequests?: number;
}
export interface SpawnOptions {
  command: string;
  args?: readonly string[];
  cwd?: string;
  env?: NodeJS.ProcessEnv;
  stderr?: 'inherit' | 'ignore';
  maxResponseBytes?: number;
  maxPendingRequests?: number;
}

const statuses = new Set<Status>(['input', 'authentication', 'certificate', 'data', 'limit', 'failure', 'refusal', 'success', 'prepared', 'invalidated']);
type Pending = { resolve: (response: Response) => void; reject: (error: JaydbError) => void };

function limits(options: Pick<ClientOptions, 'maxResponseBytes' | 'maxPendingRequests'>): [number, number] {
  const response = options.maxResponseBytes ?? 16 * 1024 * 1024;
  const pending = options.maxPendingRequests ?? 64;
  if (!Number.isSafeInteger(response) || response < 1 || response > constants.MAX_LENGTH) throw new RangeError('Invalid maxResponseBytes');
  if (!Number.isSafeInteger(pending) || pending < 1) throw new RangeError('Invalid maxPendingRequests');
  return [response, pending];
}

/** FIFO client for one existing pipe session. No reconnect, retry or reprepare. */
export class Client {
  #input: Writable;
  #output: Readable;
  #maxResponse: number;
  #maxPending: number;
  #pending: Pending[] = [];
  #header = Buffer.alloc(8);
  #headerUsed = 0;
  #body: Buffer | undefined;
  #bodyUsed = 0;
  #error: JaydbError | undefined;
  #ended = false;
  #closing = false;
  #closePromise: Promise<void> | undefined;
  #endPromise: Promise<void>;
  #resolveEnd!: () => void;
  #rejectEnd!: (error: JaydbError) => void;
  #completion: Promise<void>;
  #terminate: (() => void) | undefined;

  constructor(options: ClientOptions) {
    [this.#maxResponse, this.#maxPending] = limits(options);
    this.#input = options.input; this.#output = options.output;
    this.#endPromise = new Promise<void>((resolve, reject) => { this.#resolveEnd = resolve; this.#rejectEnd = reject; });
    void this.#endPromise.catch(() => {});
    this.#completion = (options.completion ?? Promise.resolve()).catch(error => {
      throw new TransportError('Server process failed; submitted outcomes may be unknown', { cause: error });
    });
    void this.#completion.catch(error => this.#fail(error));
    this.#input.on('error', error => this.#fail(new TransportError('Request pipe failed; submitted outcomes may be unknown', { cause: error })));
    this.#input.once('close', () => {
      if (!this.#input.writableFinished && !this.#ended && !this.#error)
        this.#fail(new TransportError('Request pipe closed before completion; submitted outcomes may be unknown'));
    });
    this.#output.on('error', error => this.#fail(new TransportError('Response pipe failed; submitted outcomes may be unknown', { cause: error })));
    this.#output.on('data', chunk => this.#receive(chunk));
    this.#output.once('end', () => {
      if (this.#headerUsed || this.#body || this.#pending.length) {
        this.#fail(new TransportError('Server ended before all complete responses; submitted outcomes may be unknown'));
      } else { this.#ended = true; this.#resolveEnd(); }
    });
    this.#output.once('close', () => {
      if (!this.#ended && !this.#error) this.#fail(new TransportError('Response pipe closed before EOF; submitted outcomes may be unknown'));
    });
    // Existing streams may have emitted their terminal events before attachment.
    if (this.#output.readableEnded) { this.#ended = true; this.#resolveEnd(); }
    else if (this.#output.destroyed || this.#input.destroyed || this.#input.writableEnded)
      this.#fail(new TransportError('Cannot attach to closed pipes; request was not submitted'));
  }

  static spawn(options: SpawnOptions): Client {
    limits(options); // Reject bad options before starting a process.
    const child = spawn(options.command, [...options.args ?? []], {
      cwd: options.cwd, env: options.env, shell: false,
      // Own a group so a failed client can stop its compiler/native descendants.
      detached: process.platform !== 'win32', stdio: ['pipe', 'pipe', options.stderr ?? 'inherit'],
    });
    let childClosed = false;
    const completion = new Promise<void>((resolve, reject) => {
      child.once('error', reject);
      child.once('close', (code, signal) => {
        childClosed = true;
        if (code === 0) resolve(); else reject(new Error(`Server exited with code ${code}, signal ${signal}`));
      });
    });
    const client = new Client({ input: child.stdin!, output: child.stdout!, completion,
      maxResponseBytes: options.maxResponseBytes, maxPendingRequests: options.maxPendingRequests });
    client.#terminate = () => {
      // A reaped child's numeric PID/group may later belong to another process.
      if (childClosed || !child.pid) return;
      try { if (process.platform === 'win32') child.kill(); else process.kill(-child.pid, 'SIGTERM'); }
      catch (error) { if ((error as NodeJS.ErrnoException).code !== 'ESRCH') throw error; }
    };
    return client;
  }

  request(request: Request): Promise<Response> {
    this.#strings(request.credential, request.code, request.proof);
    return this.#send(frame({ arguments: request.arguments, code: request.code, credential: request.credential, proof: request.proof }));
  }

  prepare(request: Preparation): Promise<Response> {
    this.#strings(request.credential, request.code, request.proof);
    return this.#send(preparedFrame(0, request.code, request.credential, null, request.proof));
  }

  execute(request: Execution): Promise<Response> {
    this.#strings(request.credential, request.handle);
    return this.#send(preparedFrame(1, request.handle, request.credential, request.arguments));
  }

  invalidate(request: Invalidation): Promise<Response> {
    this.#strings(request.credential, request.handle);
    return this.#send(preparedFrame(2, request.handle, request.credential));
  }

  /** Close stdin, drain accepted responses, then await process exit. No deadline. */
  close(): Promise<void> {
    if (!this.#closePromise) {
      this.#closing = true;
      this.#input.end();
      this.#closePromise = (async () => {
        try { await this.#endPromise; } finally {
          try { await this.#completion; } catch (error) { throw this.#error ?? error; }
        }
        if (this.#error) throw this.#error;
      })();
    }
    return this.#closePromise;
  }

  /** Abort this session. Already submitted operations may have committed. */
  abort(): void { this.#fail(new TransportError('Client aborted; submitted outcomes may be unknown')); }

  #strings(...values: unknown[]): void {
    if (values.some(value => typeof value !== 'string')) throw new TypeError('Credentials, source, proofs and handles must be strings');
  }

  #send(bytes: Buffer): Promise<Response> {
    if (this.#error) return Promise.reject(this.#error);
    if (this.#ended || this.#closing) return Promise.reject(new TransportError('Session is closed; request was not submitted'));
    if (this.#pending.length >= this.#maxPending) throw new RangeError('Client pending-request limit reached; request was not submitted');
    return new Promise<Response>((resolve, reject) => {
      this.#pending.push({ resolve, reject });
      try {
        this.#input.write(bytes, error => { if (error) this.#fail(new TransportError('Request write failed; submitted outcomes may be unknown', { cause: error })); });
      } catch (error) { this.#fail(new TransportError('Request write failed; submitted outcomes may be unknown', { cause: error })); }
    });
  }

  #receive(chunk: Buffer): void {
    if (this.#error) return;
    try {
      if (!Buffer.isBuffer(chunk)) throw new TypeError('Response stream must deliver binary Buffer chunks; do not set an encoding');
      let offset = 0;
      while (offset < chunk.length) {
        if (!this.#body) {
          const count = Math.min(8 - this.#headerUsed, chunk.length - offset);
          chunk.copy(this.#header, this.#headerUsed, offset, offset + count);
          this.#headerUsed += count; offset += count;
          if (this.#headerUsed !== 8) continue;
          const length = this.#header.readBigUInt64BE();
          if (length === 0n || length > BigInt(this.#maxResponse)) throw new RangeError('Response exceeds local client allocation cap or is empty');
          this.#body = Buffer.allocUnsafe(Number(length)); this.#bodyUsed = 0;
        }
        const count = Math.min(this.#body.length - this.#bodyUsed, chunk.length - offset);
        chunk.copy(this.#body, this.#bodyUsed, offset, offset + count);
        this.#bodyUsed += count; offset += count;
        if (this.#bodyUsed !== this.#body.length) continue;
        const value = decode(this.#body);
        if (!value || typeof value !== 'object' || Array.isArray(value)) throw new TypeError('Response must be a record');
        const response = value as { [key: string]: Value };
        if (Object.keys(response).length !== 2 || !Object.hasOwn(response, 'status') || typeof response.status !== 'string' || !statuses.has(response.status as Status) || !Object.hasOwn(response, 'value')) throw new TypeError('Invalid response record');
        const pending = this.#pending.shift();
        if (!pending) throw new TypeError('Unsolicited response');
        this.#body = undefined; this.#headerUsed = 0;
        pending.resolve({ status: response.status as Status, value: response.value! });
      }
    } catch (error) { this.#fail(new ProtocolError('Malformed server response; submitted outcomes may be unknown', { cause: error })); }
  }

  #fail(error: JaydbError): void {
    if (this.#error) return;
    this.#error = error;
    for (const pending of this.#pending.splice(0)) pending.reject(error);
    this.#rejectEnd(error);
    this.#input.destroy(); this.#output.destroy();
    try { this.#terminate?.(); } catch { /* Failure reporting must not suppress pending rejections. */ }
  }
}
