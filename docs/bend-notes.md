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
  the repo, so Bend must be reinstalled at the start of each new session
  (takes a few seconds). A SessionStart hook could automate this.
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
| Recheck with the proven kernel | `bend PROOF.bend --verdict` | **Needs Lean 4 (v4.34.0)** — not installed here, see quirks. |

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

## Quirks and bugs

- `--verdict` fails without Lean: `lean: Executable not found in $PATH`. It
  needs the elan toolchain `leanprover/lean4:v4.34.0` (or `$BENDTT` pointing to
  a built kernel). Plain `bend PROOF.bend` still checks every proof with Bend's
  own checker; `--verdict` is a second, independent check.
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
