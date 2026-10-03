# Bend toolchain notes

Facts about Bend 2 as found in this project. Newest findings at the bottom of each section.

## Version

- **Bend 2.0.35** (released build `bend-2.0.35-linux-x64`), installed 2026-10-03.
- `bend version` prints the version. `bend --version` is **not** a valid flag.

## Install (Claude Code cloud, Ubuntu 24.04, x86_64)

```sh
curl -fsSL https://bend-lang.com/install.sh | sh
export PATH="$HOME/.bend/bin:$PATH"
export BEND_NO_TELEMETRY=1   # optional: stops the once-a-day version check
```

- The script downloads the release tarball from GitHub, checks its sha256, and
  installs to `~/.bend` (`bin/bend`, `bend2/` with Base and the C/JS effects,
  `guide/`). No sudo, no shell files edited.
- `tar` prints dozens of harmless `Ignoring unknown extended header keyword
  'LIBARCHIVE.xattr.com.apple.provenance'` warnings (the tarball was made on a Mac).
- **The cloud container is wiped between sessions**, and `~/.bend` is outside
  the repo. `.claude/hooks/session-start.sh` reinstalls Bend at every session
  start (~2 s). It does **not** use `install.sh`, which always fetches the
  latest version. It downloads the pinned 2.0.35 archive from GitHub and checks
  its sha256 itself. If it finds another version, it warns and replaces it.
  To upgrade on purpose, change `BEND_VERSION` and `BEND_SHA256` in the hook
  together. The checksums for each platform are listed in that version's
  `install.sh`.
- The hook also sets `BEND_NO_TELEMETRY=1`, so the installed bend does not
  check bend-lang.com for newer versions.
- Native builds need clang 14+ (19+ only for GPU `!` calls). The container has
  **clang 18.1.3**, which works for CPU builds. The install card's "install
  clang 19+" hint only matters for the GPU.

## Commands that work

| What | Command | Notes |
| --- | --- | --- |
| Read the language guide | `bend guide` | The whole language in ~700 lines. Read before writing Bend. |
| Browse the standard library | `bend base`, `bend base --types`, `bend base Nat` | |
| Check a file (types + proofs) | `bend file.bend --check-only` | Prints `ALL PROOFS CHECK` or `SOME PROOFS FAIL`; exit code 0 / 1. |
| Check, then run `main` | `bend file.bend` | Interpreted; fine for small things. |
| Build a native binary | `bend file.bend -o out` | ~1.7 s for hello-world. Binary is ~1 MB. |
| Run on N threads | `./out --threads N` | Defaults to all cores. |
| Check the laws | `bend PROOF.bend` | Convention: `LAWS.bend` states laws, `PROOF.bend` proves them. |
| Recheck with the proven kernel | `bend PROOF.bend --verdict` | Needs Lean 4 v4.34.0 (see below). Required before a milestone is done. |

Smoke test for a fresh session: `bend engine/hello.bend` should print `Hello, world!`.

## Measured in milestone 1

- Hello-world: interpreted run 0.23 s; native build 1.7 s; native run instant.
- Parallel scaling (the guide's `pow2(28n)` example, 2^28 leaf calls, native):

  | Threads | Wall time |
  | --- | --- |
  | 1 | 1.41 s |
  | 2 | 0.72 s |
  | 4 | 0.37 s |

  That is a 3.8× speed-up on 4 cores: Bend's parallel calls use every core here.

- Law checking works as advertised: a true law (`x + 0 = x`, by induction)
  printed `ALL PROOFS CHECK`; a false one (`double(2) = 5`) printed
  `SOME PROOFS FAIL` with expected `4n`, observed `5n`, and exit code 1.

## Lean and `--verdict`

`--verdict` re-checks proofs with BendTT, a small kernel whose soundness is
proven in Lean. Bend's everyday checker is faster but has no such proof, so
`--verdict` is the gate before a milestone is called done.

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0 --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
```

- Without Lean, `--verdict` fails with `lean: Executable not found in $PATH`.
- Measured cost in a fresh container: ~25 s to install elan plus the toolchain,
  **3 GB** of disk; the first `--verdict` then builds the kernel into
  `~/.bend/bendtt/` in ~27 s, and later runs are instant. That is too slow
  for every session start, so it is not in the hook: install it at
  milestone end.
- elan prints harmless `could not canonicalize path` and `could not check for
  elan self-update` warnings.

## Quirks and bugs

- Bend's convention puts `LAWS.bend` and `PROOF.bend` side by side, and `bend`
  refuses a `PROOF.bend` that sits beside a `LAWS.bend` without importing it.
- Things to remember from the guide (Bend 2 differs a lot from Bend 1):
  - No `if`: use `match` on `True{}` / `False{}`.
  - Variables are affine (usable once) unless marked `+` and of a `Data` type.
  - Termination is checked: a recursive call must shrink an argument obtained
    by pattern matching, and the shrinking argument should come first. No
    mutual recursion. A point-capped loop should count down a `Nat` fuel.
  - `match` only works on parameters or pattern-bound variables, not on
    computed values; pass a computed value to a helper.
  - Operators need a type annotation and spaces: `(a + b : U32)`.
  - Equality of values is `T.is_eq(a, b)`; `==` only appears in types.
  - A `Nat` literal above `4294967295n` is not supported.

## Found in milestone 2

- A constructor from an imported module needs the module's alias, like a def:
  with `import ./scoring.bend as S`, write `S.A{}` and `S.Game{a, b}`, not
  `A{}`. The error says `expected : a declared constructor (scoring.Side
  declares scoring.A, scoring.B)`. Type names (`S.Side`) need the alias too.
- `?TODO` works as the body of an ordinary def, not just a proof, so a file
  can declare an interface (types and signatures) before any code exists.
  `--check-only` then reports `N TODOs found` and exits 1, but still type-checks
  everything else first: a real type error is reported instead of the TODO
  count.
- An open law (one with no proof yet) counts as a TODO too.
- `bend file.bend` refuses to run `main` while any TODO remains in the file or
  its imports, even if `main` doesn't use the unfinished parts.
- `Nat` is unary (`Zero`/`Succ`), and `3n+n` is the term "3 plus n". As a law
  parameter, `for n: Nat` with `3n+n` means "every number from 3 up".
- **Use-once law parameters.** If a law says `for n: Nat` (not `for +n`), its
  proof may use `n` only once in running code, so it can't call three lemmas
  that each take `n`. Mentioning `n` in types and rewrites doesn't count. A
  proof can't relax this either (`def Laws.x(+n)` is a syntax error).
  Workaround used in PROOF.bend: one lemma proves all the facts by a single
  induction and returns them as a tuple (`deuce_comparisons`), and the other
  lemmas take the fact they need as an argument, with `n` erased (`-n`).
- A destructuring let, `(x, y) = f(n)`, counts as a `match`, so it can't
  unpack a computed value. Pass the value to a helper def and match on its
  parameter there.
- A def can return a `Type`, which gives a long proposition a short name:
  `def DeuceFacts(-n: Nat) -> Type: {..} & {..}`.
- **Rewriting.** `%e : P` with `e : {a == b : T}` treats `P` as the current
  goal with `_` where `b` appears, and leaves `P` with `a` there as the new
  goal. To replace a computed expression `X` by its value `V`, you need
  `e : {V == X}`, so wrap the lemma in `Equal.sym(T, X, V, lemma)`. One `P` can
  hold several `_`, and `P` may be written in partly evaluated form, because
  it is compared by computing.
- Bend matches tuples of constructors directly
  (`match p q r t: case True{} False{} ...`), which makes "check every
  combination of Bools" lemmas quick to write.
- `--verdict` takes 0 s once the kernel is built and Lean is installed.
- Checking `engine/LAWS.bend` on its own always reports its laws as TODOs,
  because it only states them. The gate is `bend engine/PROOF.bend`, which
  imports the laws and proves them.
