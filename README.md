# WTA Finals simulator

A WTA match and tournament simulator. The tennis scoring rules are written in
[Bend 2](https://bend-lang.com), with their correctness proven by laws
(`engine/LAWS.bend`), and matches are simulated a million at a time. A small
TypeScript layer in `prep/` prepares the player data and checks the
simulator against an exact calculator. The first goal is title odds for the
2026 WTA Finals.

- `SPEC.md`: what is being built and why.
- `docs/progress.md`: progress, milestone by milestone.
- `docs/bend-notes.md`: notes on the Bend toolchain.

## Data

Player statistics come from [Tennis Abstract](https://www.tennisabstract.com)
by Jeff Sackmann, licensed
[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/). This is
a non-commercial project, and the data in `data/` is shared under the same
licence.
