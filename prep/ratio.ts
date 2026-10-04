// Exact fractions (whole numbers over whole numbers, as BigInt), so that the
// one rounding step to "out of 10,000" is the only place a number changes.
// Ordinary decimals would add tiny errors (0.62 + 1 - 0.42 - 0.56 is
// 0.6400000000000001), and those can tip a value that sits exactly halfway
// between two whole numbers.

export type Ratio = { readonly n: bigint; readonly d: bigint }; // d > 0, in lowest terms

const gcd = (a: bigint, b: bigint): bigint => {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
};

export function ratio(n: bigint | number, d: bigint | number = 1n): Ratio {
  let nn = BigInt(n);
  let dd = BigInt(d);
  if (dd === 0n) throw new RangeError("division by zero");
  if (dd < 0n) {
    nn = -nn;
    dd = -dd;
  }
  const g = gcd(nn, dd) || 1n;
  return { n: nn / g, d: dd / g };
}

export const add = (a: Ratio, b: Ratio): Ratio => ratio(a.n * b.d + b.n * a.d, a.d * b.d);
export const sub = (a: Ratio, b: Ratio): Ratio => ratio(a.n * b.d - b.n * a.d, a.d * b.d);
export const half = (a: Ratio): Ratio => ratio(a.n, a.d * 2n);
export const cmp = (a: Ratio, b: Ratio): number => {
  const x = a.n * b.d - b.n * a.d;
  return x < 0n ? -1 : x > 0n ? 1 : 0;
};
export const ONE = ratio(1);
export const ZERO = ratio(0);

// Floor division that rounds toward minus infinity for negative numbers too.
const floorDiv = (a: bigint, b: bigint): bigint => {
  const q = a / b;
  return (a % b !== 0n && (a < 0n) !== (b < 0n)) ? q - 1n : q;
};

// The nearest whole number out of 10,000, with an exact half going up:
// 0.64005 -> 6401, 0.64004 -> 6400.
export function toTenThousandths(r: Ratio): bigint {
  return floorDiv(2n * r.n * 10000n + r.d, 2n * r.d);
}

// Read a plain decimal such as "65.1" or "-3" exactly. Returns null for
// anything else (blank, "65.1%", "1e3", "6,5").
export function parseDecimal(s: string): Ratio | null {
  const m = /^(-?)(\d+)(?:\.(\d+))?$/.exec(s.trim());
  if (!m) return null;
  const frac = m[3] ?? "";
  const n = BigInt(m[2] + frac) * (m[1] === "-" ? -1n : 1n);
  return ratio(n, 10n ** BigInt(frac.length));
}

// A ratio as a percentage with `places` decimals, for messages and reports
// (display only: never fed back into a calculation).
export function percent(r: Ratio, places = 2): string {
  const scale = 10n ** BigInt(places);
  const v = floorDiv(2n * r.n * 100n * scale + r.d, 2n * r.d);
  const neg = v < 0n;
  const a = neg ? -v : v;
  const whole = a / scale;
  const frac = (a % scale).toString().padStart(places, "0");
  return `${neg ? "-" : ""}${whole}${places > 0 ? "." + frac : ""}`;
}
