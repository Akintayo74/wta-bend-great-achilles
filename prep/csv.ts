// A small, strict CSV reader and writer for the files in data/.
//
// Fields may be quoted ("a, b"), with "" for a quote inside quotes. Anything
// else odd (a quote in the middle of a field, a ragged row, an unclosed
// quote) is an error, not a guess.

export type Row = Record<string, string>;

export class CsvError extends Error {}

// Split CSV text into rows of fields.
function fields(text: string): string[][] {
  const rows: string[][] = [];
  let row: string[] = [];
  let field = "";
  let i = 0;
  let quoted = false; // inside a quoted field
  let wasQuoted = false; // the current field was quoted (so it is complete)
  let line = 1;
  const endField = () => {
    row.push(field);
    field = "";
    wasQuoted = false;
  };
  while (i < text.length) {
    const c = text[i];
    if (quoted) {
      if (c === '"') {
        if (text[i + 1] === '"') {
          field += '"';
          i += 2;
          continue;
        }
        quoted = false;
        wasQuoted = true;
        i++;
        continue;
      }
      if (c === "\n") line++;
      field += c;
      i++;
      continue;
    }
    if (c === '"') {
      if (field !== "" || wasQuoted) throw new CsvError(`line ${line}: a quote in the middle of a field`);
      quoted = true;
      i++;
      continue;
    }
    if (c === ",") {
      endField();
      i++;
      continue;
    }
    if (c === "\r" && text[i + 1] === "\n") {
      i++;
      continue;
    }
    if (c === "\n") {
      endField();
      rows.push(row);
      row = [];
      line++;
      i++;
      continue;
    }
    if (wasQuoted) throw new CsvError(`line ${line}: text after a closing quote`);
    field += c;
    i++;
  }
  if (quoted) throw new CsvError(`line ${line}: unclosed quote`);
  if (field !== "" || wasQuoted || row.length > 0) {
    endField();
    rows.push(row);
  }
  return rows;
}

// Parse CSV text with a header row into one record per data row. Blank lines
// are skipped. Every row must have exactly as many fields as the header.
export function parseCsv(text: string): { header: string[]; rows: Row[] } {
  const all = fields(text).filter((r) => !(r.length === 1 && r[0] === ""));
  if (all.length === 0) throw new CsvError("empty file: no header row");
  const header = all[0];
  const seen = new Set<string>();
  for (const h of header) {
    if (h === "") throw new CsvError("header has an empty column name");
    if (seen.has(h)) throw new CsvError(`header repeats the column ${h}`);
    seen.add(h);
  }
  const rows = all.slice(1).map((r, k) => {
    if (r.length !== header.length) {
      throw new CsvError(`data row ${k + 1}: ${r.length} fields, header has ${header.length}`);
    }
    return Object.fromEntries(header.map((h, j) => [h, r[j]]));
  });
  return { header, rows };
}

function quote(v: string): string {
  return /[",\n\r]/.test(v) ? `"${v.replaceAll('"', '""')}"` : v;
}

// Write rows as CSV text, columns in the order given, ending in a newline.
export function formatCsv(header: string[], rows: Row[]): string {
  const lines = [header.map(quote).join(",")];
  for (const r of rows) lines.push(header.map((h) => quote(r[h] ?? "")).join(","));
  return lines.join("\n") + "\n";
}
