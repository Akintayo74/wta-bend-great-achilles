# Progress log

A plain-language diary of the WTA Finals simulator, one entry per milestone.

## Milestone 1 — Bend runs in the cloud (2026-10-03)

**What works now:** Bend 2 (version 2.0.35) installs in a few seconds in the
Claude Code cloud machine, and a hello-world both runs and compiles to a native
program. The project folders are in place, waiting for code.

**Interesting finding:** Bend really does spread work across every core with no
extra effort. A toy program that makes 268 million tiny function calls took
1.41 seconds on one core and 0.37 seconds on all four — almost exactly 4× faster.

**Also:** I tried to "prove" that double(2) equals 5. Bend refused, saying it
expected 4. That refusal is the whole point of the project: tennis scoring rules
will be checked the same way.

**Machine:** 4 CPU cores (Intel Xeon, 2.1 GHz), 15 GB memory, no GPU.
