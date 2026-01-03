import { createReadStream } from 'node:fs';
import { createInterface } from 'node:readline';

export async function* readString(text: string) {
  let lines = text.split(/\r?\n/)
  yield* lines
}

export async function* readFile(fileName: string) {
  const input = createReadStream(fileName);
  const rl = createInterface({ input, crlfDelay: Infinity });
  yield* rl;
}
