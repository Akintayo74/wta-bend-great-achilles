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
- Checking `engine/LAWS.bend` (or `engine/proof_tables.bend`, which imports
  it) on its own always reports the laws as TODOs, because it only states them. The gate is `bend engine/PROOF.bend`, which
  imports the laws and proves them.

## Found in milestone 3

- A `+` (reusable) input must have a copyable (`Data`) type. `List<S.Side>`
  is short for `List<&1, S.Side>`, which is not copyable, so `for +pts:
  List<S.Side>` is refused ("+pts can be used many times, so its type must
  be Data"). Write `List<&2, S.Side>` instead. The same goes for a list
  stored inside a `Data` record: `done: List<&2, Score>`.
- A def must appear above every def that calls it. Calling one defined
  further down fails with the confusing message "expected : a filled
  definition (an unfilled law is a dead claim: live code cannot use it)".
- `Set` is taken: Base defines `Set.new`, `Set.add` and so on, so the tennis
  set type is called `TennisSet`.
- **Type-only inputs can't be branched on.** A proof can't `match` on an
  input marked `-` (erased): "a live scrutinee (a - scrutinee matches only in
  a dead region)". Several laws take the winner as `-w`. The fix is the
  standard one: the proof computes the winner itself as a live value,
  branches on that, and uses the assumption `m == Some{w}` to show it is `w`
  (`some_injective`, `none_is_not_some`).
- **Two functions with identical bodies are still different.** Bend compares
  stuck terms by name, so `f(w, a, b)` and `g(w, a, b)` aren't equal when `w`
  is unknown, even if f and g are written the same way. Each engine helper
  that mirrors a spec helper (`Match.same` vs `Rule.same`, and so on) needs a
  small lemma saying they agree. Functions that end in the same Base calls
  (`Nat.is_ge`, `Bool.and`) do compare equal.
- **Assumptions are use-once too.** A proof of `x == y` can be used only once.
  `dup_eq` turns one proof into a pair; a helper then unpacks the pair.
- A `match` can't come after a rewrite step (`%e : P`) in the same body.
  Branch first, then rewrite inside each branch.
- **Proof by computation.** With concrete numbers, Bend just computes, so
  `{==}` proves any true claim about them. `prep/gen-proof-tables.ts`
  generates lemmas that split on every small score (0-0 to 6-6, plus "7 or
  more") and finish each case with `{==}`. Writing the claim as
  `Imp(premise, conclusion) == True` keeps every case uniform: out-of-range
  cases make the premise false, so they compute to True as well.
- The whole proof set (about 3,900 lines across LAWS, PROOF, proof_tables and
  scoring) checks in 0.3 s, and `--verdict` in under 1 s.

## Found in milestone 4

- **Base has no 64-bit integers.** `U32` is the only fixed-size number type
  (`bend base U64` finds nothing). The random number generator therefore
  works in 32 bits.
- `U32` is a 32-bit word stored as bits (`Word(32n)`). The checker can
  compute with concrete `U32`s (`{==}` proves `U32.mod(4294967295, 10000) ==
  7295`), but Base has almost no lemmas about `U32` arithmetic (only
  `U32.add_comm`). So laws about all `U32` values (such as "x mod 10000 is
  below 10000 for every x") are out of practical reach, while laws that only
  pass `U32`s around are fine.
- A `Data` type can carry a proof as a field:
  `Chance{p: U32, ok: {U32.is_le(p, 10000) == True{} : Bool}}`. In a type,
  write constructors with braces (`True{}`); plain `True` fails with
  "expected : a defined name".
- A def named `Sim.step` in a file imported `as Sim` can't be reached:
  `Sim.step` from the importer means the file's own `step`, and the def is
  `Sim.Sim.step`. Name defs in a module by type or topic (`Point.simulate`,
  `Run.tally`), like `scoring.bend` does (`Game.point`, imported as
  `S.Game.point`).
- `match a b:` accepts `Nat` literal patterns with a fallback:
  `case 6n 0n:` ... `case _ _:`.
- **The checker computes whole equations on any mismatch.** When the two
  sides of an equation differ anywhere, even in a constant's name
  (`Sim.Match.cap()` vs `Laws.Rule.cap()`, both `1000n`), the checker
  evaluates both sides in full. For L27 that meant playing 1,000 points
  symbolically: the proof took 22 s instead of 0.6 s. A rewrite (`%e : P`)
  triggers it too. Fix: split the proof with `Equal.trans(T, a, b, c, ab,
  bc)` so the expensive side is only ever compared with an identical copy of
  itself, and the step that needs computing has nothing expensive in it.
  Syntactically identical sides are compared instantly.
- Tuple patterns work only as the sole pattern: `match hh: case (h1, h2):`
  is fine, `match n hh: case 1n+p (h1, h2):` is a syntax error. Nest the
  matches.
- After `match x y z:`, a further `match` on fields bound in that case
  (`xs ys zs`) is refused ("can't be matched in this position"). Write the
  nested patterns in one go instead:
  `case Sim.Tally{xa, xb, xu, Sim.SetCounts{x1, ...}} ...`.
- `match` can't scrutinize a computed value in IO code either
  (`match U32.read(s):`); pass it to a helper def.
- In a `do` block, binds can't be marked reusable (`+x : U32 <- ...` is a
  syntax error). Bind plainly, then hand the values to a pure def whose
  parameters are `+`.
- `++` joins Strings only; to build a `List<String>` use `<>` (cons).
- `List.append(&2, T, xs, ys)` needs the quantity and type spelled out in
  laws and proofs.
- `bend --check-only` on PROOF.bend takes ~0.6 s with all milestone 4
  proofs.

## Measured in milestone 4

- Simulator binary (`bend engine/simulate.bend -o build/simulate`) builds in
  a few seconds.
- 2^20 = 1,048,576 best-of-three matches (60% vs 56.5% servers): **5.0 s on
  4 cores, 21 s on 1 core** (4.2x), with byte-identical output.
- `U32` arithmetic compiles to native operations (the hash costs little);
  unary `Nat` scores and counters are cheap at tennis sizes, and adding up
  the `Nat` tallies of a million runs is not noticeable.

## Found in milestone 5

- **Proof-carrying literals are checked when the file is read.** A generated
  `Sim.Chance{6474, {==}}` makes the checker compute `U32.is_le(6474, 10000)`
  and confirm it is `True`. A value of 10500 fails `--check-only` with
  `SOME PROOFS FAIL`, `expected : False{}` / `observed : True{}`, pointing at
  that line. So generated data can carry its own range check (law L1)
  without any new law. Cost: params.bend with 30 players (1,800 chances,
  3,900 lines) checks in 0.8 s, and `--verdict` on matchup.bend, which
  imports it, takes 2.2 s. A test file with 50 players (5,000 chances)
  checked in 1.6 s and built in 6.5 s.
- A two-argument `match server receiver:` with 900 constructor pairs is
  fine. Bend doesn't complain about the size.
- **Importing a file that has its own `main` works.** matchup.bend imports
  simulate.bend `as Cli` to reuse `Cli.number`, `Cli.bits`, `Cli.show_tally`
  and `Cli.wta`, and the imported `main` is simply not used.
- `String.eq(a, b)` exists in Base, along with `String.order`, `String.is_lt`
  and the rest, so the command line can name players.
- No mutual recursion, so "search a list, stop at the first hit" is written as
  one recursive def that builds both outcomes and picks with a helper:
  `first(when(String.eq(s, id(p)), p), find(rest, s))`. That searches the
  whole list (30 players), which costs nothing here.
- An optional command-line argument is two `match args:` cases, one per
  length (`Con{.., Con{b_s, Nil{}}}` and `Con{.., Con{m_s, Nil{}}}`).
- `Con{+p, rest}` in a pattern makes the head reusable when the element type
  is `Data`.
- Constructors are per module: params.bend's test fixtures had players
  called `A{}` and `B{}`, and that does not clash with scoring.bend's `S.A{}`
  and `S.B{}`.

## Found in milestone 6

- Base already declares a type `Result` and a constructor `Done`, so a
  module can't reuse those names ("duplicate declaration"). The tournament
  types are `Finished` (one match result) and `Complete` (a finished
  tournament).
- `LAWS.bend` can declare its own `type` (`GroupRecord`), not only defs, so
  a rule can keep its working figures in a record of its own instead of
  borrowing an engine type.
- Worked examples catch slips in the examples themselves: one of my
  hand-worked three-way ties had a set count wrong, and `{==}` refused it
  with the rule's actual answer in "observed".
- Rewriting with `%e : P`, where `e : {a == b}`: P is the current goal
  with `_` where **b** appears, and the goal becomes P with **a** there. To
  replace the left side of a lemma, rewrite with `Equal.sym(...)` of it. I
  got this backwards often enough that it's worth writing down.
- `match` has to come before any `%` rewrite in a def, and a variable can't
  be matched after one bound later. To split a record and a field inside it
  at once, match with a nested pattern: `case Tour.Finished{S.A{}, +t}:`.
  When a rewrite has to come first, put it in a wrapper def that calls a
  helper which does the matching (L16, L17).
- Proofs are affine like any other value: a premise used four times has to
  be copied first (`dup_eq`, `dup3`, `dup4` in PROOF.bend), and a law param
  used twice needs `+`.
- A false Bool premise only becomes `False == True` if the evaluator gets to
  the false part. In `Bool.and(stuck, False)` it doesn't; take the right
  side out with `and_true_r` first.
- A Nat literal pattern with a `_` fallback (`case 1n: ... case _:`) left
  the fallback stuck in proofs (`7n+_17`). Writing the fallback as explicit
  `case 0n:` and `case 8n+p:` fixed it.
- Base has no arithmetic laws for Nat. PROOF.bend now proves the ones L17
  needed: commutativity and associativity of + and *, distributivity, and
  that multiplying both sides by a positive number keeps a comparison.
  Each is a few lines by induction.
- Engine helpers and rule helpers with the same body are still different
  names to the checker, so each needs a small "same" lemma. When the
  engine's record type differs from the rule's (`Tour.Record` vs
  `GroupRecord`), a `conv` function bridges them.
- Long case splits (64 ways a group's matches can fall; the three-way-tie
  lemma) were written by short throwaway scripts, then checked by Bend like
  everything else. PROOF.bend is now 7,700 lines and checks in 3.5 s.
- The finals CLI does 2^16 tournaments in 7.3 s and 2^18 in 29 s on 4 cores.
- In this session, `--verdict` couldn't run: elan now downloads Lean from
  `releases.lean-lang.org`, and the session's network policy blocked that
  host (403 from the proxy).

## Milestone 7 (2026-10-10)

- No new Bend code: the final run drives the existing `build/finals` and
  `build/matchup` binaries from `prep/final.ts`.
- At 2^20 on 4 cores: the Finals take 113 s and the 28 match-ups 169 s.
