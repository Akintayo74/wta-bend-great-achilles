# WTA Match Simulator — Spec v0

Oct 3, 2026 · @Akintayo

## Overview

We are building a WTA match and tournament simulator whose first real job is to publish title odds for the 2026 WTA Finals before the event starts on November 8. The scoring rules are written in Bend so that their correctness is proven, not just tested, and simulations run in parallel.

The engine models each point as a weighted coin flip. Two numbers per player (serve points won, return points won) decide the weight. Everything else in the project either makes those two numbers better or reports what the coin flips produce.

**v0 is done when:**

1. Every law in the Laws section compiles as proven in Bend.
2. The simulator agrees with an exact calculation to within 0.2 percentage points for any pair of inputs.
3. Re-running with the same seed gives identical results.
4. A page showing each qualified player's chance of advancing, reaching the final and winning the title is published before November 8.

## Scope

v0 covers WTA singles, one surface (hard court), the two-number player model and the WTA Finals format. Everything else waits until v0 works end to end.

**In v0**

- Point, game, tiebreak, set and match scoring, with laws proven in Bend.
- Monte Carlo simulation of single matches and of the full WTA Finals (round robin, semifinals, final).
- An exact calculator for single matches, used only to check the simulator.
- Hand-collected hard-court stats for the eight qualified players.
- A results page in Astro.

**Out of v0 (planned upgrades, in rough order)**

- Opponent-strength adjustment of each player's stats.
- Shrinking small samples toward the tour average.
- Weighting recent matches more heavily.
- Big-point ("clutch") behaviour from Match Charting data.
- Fatigue across the round robin, withdrawals and alternates.
- Other events (Slams, replaying past draws, cross-era matchups).

**Milestones**

1. Repo set up in Claude Code cloud; Bend installed and a hello-world compiles.
2. Game layer in Bend with its laws.
3. Tiebreak, set and match layers with their laws.
4. Simulator (random numbers, many runs) plus the exact calculator; both agree.
5. Player inputs: hand-collected stats, prep script, generated parameters.
6. Tournament layer (groups, standings, knockouts) with its laws.
7. Results page; final run once the field and groups are known; publish before November 8. This is a fun project though, so maybe on twitter and on my blog or something. I plan to keep tweeting on my progress on this project.

## Inputs and data

Each player needs two hard-court numbers: the share of points she wins on her own serve, and the share she wins when returning. For eight players that is 16 numbers, few enough to collect by hand.

| Field | Meaning | Example |
| --- | --- | --- |
| `name` | Player name as displayed | Player A |
| `serve_won` | Hard-court serve points won, last 52 weeks | 62.0% |
| `return_won` | Hard-court return points won, last 52 weeks | 45.0% |
| `serve_points` | Serve points behind `serve_won` (sample size) | 3,200 |
| `return_points` | Return points behind `return_won` | 3,150 |
| `source` | Where the numbers came from, and the date read | Tennis Abstract, 2026-10-xx |

The sample-size columns are not used in v0. They are recorded now because the shrinkage upgrade needs them, and re-collecting later is wasted work.

**Sources**

| Source | Coverage | Problem |
| --- | --- | --- |
| Tennis Abstract player pages | Current, with surface splits | Manual reading; site layout can change |
| [Match Charting Project](https://github.com/JeffSackmann/tennis_MatchChartingProject) | Shot-by-shot, volunteer-charted | Only some matches are charted; thin for any one player on one surface |
| Archive mirror of the removed `tennis_wta` repo | Match-level stats, all tour matches | Snapshot ends June 2026, missing the summer hard-court season |
| WTA official stats | Current | Season totals, usually without surface splits |

All Sackmann-derived data is CC BY-NC-SA: credit it on the page and keep the project non-commercial.

## Point model

For each pairing we compute two numbers: the chance A wins a point on her own serve against B, and the same for B against A. Every point in the match is then an independent weighted coin flip using the server's number.

There are two ways to combine the players' stats, and the choice changes results far more than it looks like it should.

**Method 1: average (milestones 2–4).** Average the server's record with what the returner's record implies.

```latex
p_{A \text{ serving}} = \frac{\text{serve}_A + (1 - \text{return}_B)}{2}
```

**Method 2: additive (from milestone 5).** Start from the tour average and add both players' edges in full.

```latex
p_{A \text{ serving}} = \text{serve}_A + (1 - \text{return}_B) - \text{tour serve average}
```

With invented players (A: 62% serve, 45% return; B: 58% serve, 42% return; tour average 56%), I computed both exactly:

| Method | A's serve points won vs B | B's serve points won vs A | A wins the match |
| --- | --- | --- | --- |
| Average | 60.0% | 56.5% | 67.7% |
| Additive | 64.0% | 57.0% | 81.6% |

The average halves every player's edge, which pulls all matches toward 50/50. The additive method is the standard in tennis modelling and needs only one extra number, the tour average on hard courts. **Recommendation:** build with the average first because it is easy to reason about, then switch to additive and compare the two on the same inputs. Seeing that 14-point gap is part of the learning.

**Assumption accepted for v0:** points are independent. A player does not get better or worse at break point, after losing a set, or when tired. Research suggests these effects are small; testing that is a later upgrade.

## Scoring rules

The engine follows standard WTA tour singles rules, with every format detail stored as a setting so Slams and other events can be added later without touching the core.

| Layer | Rule | Setting (v0 default) |
| --- | --- | --- |
| Game | Server serves every point; first to 4 points with a 2-point lead | Ad scoring (no-ad off) |
| Tiebreak | Played at 6–6; first to 7 with a 2-point lead | Tiebreak target: 7 |
| Tiebreak serving | First server serves 1 point, then each player serves 2 in turn | Fixed |
| Set | First to 6 games with a 2-game lead, or 7–6 via tiebreak | Games to win: 6 |
| Serve between games | Alternates every game, including across sets | Fixed |
| After a tiebreak set | The player who did not serve first in the tiebreak serves first in the next set | Fixed |
| Match | Best of three sets | Sets to win: 2 |
| Deciding set | Ordinary set with a 7-point tiebreak at 6–6 | Final-set tiebreak target: 7 (Slams use 10) |
| First server | Coin toss | 50/50 |

The two serve-order rows are easy to get wrong and hard to notice when wrong: the results still look like tennis. They get their own laws.

**To confirm before milestone 6:** the official WTA Finals match format for 2026.

## Simulation

The simulator plays 2²⁰ = 1,048,576 tournaments ("one million" below) from a fixed, published seed, **20261108**, so anyone re-running it gets identical numbers. Runs come in a power of two because Bend splits work in halves, and that shape is what lets L14 be proven.

**Numbers are whole numbers out of 10,000.** A 60% chance is stored as 6000. Bend can prove things about whole numbers but not about decimals, so this keeps laws like "a probability is never above 100%" provable. Resolution is 0.01%, finer than the data deserves.

**Randomness is counter-based.** Each simulation gets its own random stream derived from the seed and the simulation's number, using a small hash function. No simulation shares state with another, which is what lets Bend split them across cores freely. A point is won by the server when the next random number, reduced to the range 0–9,999, falls below her point chance.

**Every match has a point cap.** A game can, in principle, stay at deuce forever, and Bend insists that every function finishes. Each match draws from a stream of at most 1,000 points. A match that hits the cap is counted as unfinished and reported. At realistic point chances this should never happen; if it does, it signals a bug.

**How many runs.** More runs shrink random noise; the margins below are at 95% confidence for a probability near 50%.

| Runs | Noise in each probability |
| --- | --- |
| 10,000 | ± 1.0 points |
| 100,000 | ± 0.3 points |
| 1,000,000 | ± 0.1 points |

**Why one million is enough.** The page shows whole percentages, so ±0.1 points is already finer than anything displayed; 100,000 runs would arguably do. A million tournaments is about 15 million matches and roughly 2.4 billion points.

The real uncertainty sits in the inputs, not the run count. A serve percentage built from about 3,000 points is itself uncertain by roughly ±1.8 points, and near 50/50 a 1-point change in point-win rate moves best-of-three match odds by about 10 points. More runs cannot fix that; better inputs can.

**Expected speed.** At about 20 nanoseconds per point in compiled C, a full run is under a minute on one core. Even if Bend is ten times slower, that is minutes. Measured at milestone 4.

**The exact calculator.** For a single match, the win probability can be calculated exactly by working backwards through every possible score. We build this separately (in the prep language, not Bend) and require the simulator to agree with it. I used this method to produce the figures in the Point model table; it also confirmed a quick simulation within 0.2 points.

## Tournament layer

The WTA Finals has eight players in two groups of four; each plays the other three in her group, the top two of each group reach the semifinals, and the semifinal winners meet in the final.

1. **Groups.** Three modes. Seeded random (default before the draw): the top two seeds go in different groups, and seeds 3–4, 5–6 and 7–8 are each split between the groups by lot, mirroring the real draw (confirm in the rulebook). Real groups: used once the draw happens. Custom groups: you choose who goes where, for what-ifs such as a group of death.
2. **Round robin.** Simulate all six matches in each group.
3. **Standings.** Rank by matches won; break ties with the official rules (below).
4. **Semifinals.** Group A winner vs Group B runner-up; Group B winner vs Group A runner-up.
5. **Final.** Semifinal winners meet.

**Standings tiebreaks must be copied from the official 2026 WTA rulebook, not from memory.** The usual pattern is head-to-head for a two-way tie and set and game percentages for a three-way tie, but the exact order and edge cases matter. A wrong rule here silently shifts who advances in thousands of simulations. These rules get their own laws.

**Simplifications in v0:** every match is completed (no retirements, withdrawals or alternates), and players do not tire across the week. Withdrawals are common at the Finals, so the page should say this plainly.

## Laws

These are the rules the code must never break, written in plain words; each becomes a law in `LAWS.bend` that Bend proves for every possible sequence of points. A law that is wrong or missing is a bug Bend cannot catch, so this list deserves the most careful review in the whole doc.

| # | Layer | Law |
| --- | --- | --- |
| L1 | Inputs | Every point chance is between 0 and 10,000. The engine checks each input once and rejects anything outside that range; it never clamps. |
| L2 | Game | A game ends only when one player has at least 4 points and leads by 2. |
| L3 | Game (deuce) | At any tie of 3–3 (40–40) or higher, the game is not over. |
| L4 | Game (advantage) | From a 1-point lead at 4–3 or higher, the next point either wins the game or returns it to deuce. |
| L5 | Game | Once a game is won, further points do not change it. |
| L6 | Tiebreak | A tiebreak ends only when one player has at least 7 points (or the set target) and leads by 2. |
| L7 | Tiebreak (level) | At any tie of 6–6 or higher, the tiebreak is not over; from a 1-point lead at 6–5 or higher (target minus 1 for longer tiebreaks), the next point either wins it or levels it. |
| L8 | Tiebreak | The serving player for each tiebreak point follows the 1-then-2s pattern. |
| L9 | Set | A finished set score is 6–0 to 6–4, 7–5 or 7–6 (either way round); nothing else. |
| L10 | Set | A 7–6 set always contains exactly one tiebreak; no other set contains one. |
| L11 | Serve order | The server alternates every game, with the tiebreak counting as a game, so after a tiebreak set the player who received first in the tiebreak serves first in the next set. In an ordinary game the same player serves every point. Stated about the function the simulator uses to pick whose serve chance applies. |
| L12 | Match | A finished match has a winner with exactly 2 sets; the loser has 0 or 1. |
| L13 | Match | Once a match is won, further points do not change it. |
| L14 | Simulation | The total over all runs counts every run exactly once, however the work is split across cores. |
| L15 | Draw | In seeded mode, the top two seeds are never in the same group, and each pair of lower seeds is split. |
| L16 | Standings | A player with more round-robin wins always ranks above one with fewer. |
| L17 | Standings | Exactly two players advance from each group. |
| L18 | Knockouts | The champion won both her semifinal and the final. |
| L19 | Knockouts | Semifinal pairings always cross groups. |
| L20 | Game | While a game is in progress, each point is added to the player who won it. |
| L21 | Tiebreak | While a tiebreak is in progress, each point is added to the player who won it; a finished tiebreak does not change. |
| L22 | Set | While a set is in progress, each finished game or tiebreak adds one game to its winner and changes nothing else; a finished set does not change. |
| L23 | Match | While a match is in progress, each finished set adds one set to its winner, and the next set starts at 0–0 with the correct server. |
| L24 | Set | Who has won a set follows the set rule at every score: first to 6 games with a 2-game lead, or 7–6 via the tiebreak. |
| L25 | Match | Who has won a match follows the match rule: the first player to win 2 sets (the sets-to-win setting). |
| L26 | Simulation | Each simulated point goes to the server exactly when the random number is below the server's point chance, and to the receiver otherwise. The server is the one L11 picks. |
| L27 | Simulation | A simulated match plays at most 1,000 points from its random stream. It is reported as won only by the player the scoring engine says has won; otherwise it is reported as unfinished. |

L3, L4 and L7 follow from L2 and L6, but they get their own laws anyway: deuce is where scoring bugs hide, and it is the reason every match needs a point cap.

L20 was added during milestone 2. L2–L5 only constrain who has won a game and that a won game stays won, so without L20 an engine that credited a point to the wrong player would still pass them. L21–L23 were added in milestone 3 to close the same gap for tiebreaks, sets and matches. L24 and L25 were added for the same reason: L9 and L12 only describe a finished set or match, so without them an engine that never ended a set or match would pass.

L14 was reworded in milestone 4. As first written ("the same seed and inputs always give the same result") it is automatically true in Bend: functions have no hidden state, clock or shared generator, so the proof would be "it is the same expression" and could never fail. The reworded law covers the way parallel tallying really goes wrong: a run dropped or counted twice. Identical output on reruns, and on 1 core versus all cores, is still checked by running it. L26 and L27 were added in milestone 4: without L26 a simulator could use the wrong player's point chance and every scoring law would still prove; without L27 it could stop early, use more than 1,000 points, or count an unfinished match as a win.

Two things Bend will not prove: that the point model reflects real tennis, and that the input numbers are right. Those are checked by validation, below.

## Architecture and repo

Data flows one way through five stages; Bend owns only the middle one, where proofs and parallelism pay off, and TypeScript handles everything that touches files, text or the web.

&#91;embedded content: data pipeline · 5 stages plus a check\]

The exact calculator reads the same point chances as the engine, so any disagreement between them points at the engine or the random numbers, not the data.

**Proposed repo layout**

```
wta-sim/
  SPEC.md              this document, exported
  data/
    players.csv        hand-collected inputs
    rules/             official format and tiebreak rules, copied in
  prep/                TypeScript: builds params, exact calculator, checks
  engine/              Bend
    LAWS.bend          the laws; approved by the owner, then locked
    PROOF.bend         proves each law in LAWS.bend (imports it)
    scoring.bend       point, game, tiebreak, set, match
    tournament.bend    groups, standings, knockouts
    sim.bend           random numbers and the run loop
    params.bend        generated by prep; never edited by hand
  results/             one CSV per run
  site/                Astro page
```

## Outputs and validation

The published page shows, for each of the eight players, her chance of getting out of the group, reaching the final and winning the title, plus win chances for every possible match-up.

**Engine output (CSV, one file per run):** per player, the counts of group exits, semifinals, finals and titles; per pair, match wins and set-score counts (the game score of each set, such as 6–4 or 7–6); plus the seed, inputs, run count and any unfinished matches.

**Validation, in order of how much it tells us:**

1. **Laws compile.** Proves the rules are followed.
2. **Simulator matches the exact calculator** within 0.2 points on a grid of inputs: each player's serve point chance takes the values 40%, 45%, … 75%, giving 8 × 8 = 64 match-ups, with 2²⁰ (1,048,576) runs each. Both the match-win chance and the share of each set score (6–4, 7–6 and so on) must agree. Any unfinished match fails the check. Catches errors in the simulation and random numbers. (A tolerance of 0.2 points needs about a million runs per match-up: at 100,000 runs the noise alone is ±0.3 points, so a correct simulator would fail some match-ups by chance.)
3. **Sanity cases.** Equal players give 50/50; a 100% server never loses a service game; swapping players swaps the result.
4. **Compare with outside forecasts** (bookmaker odds, Tennis Abstract forecasts) before the event. Large gaps need an explanation, not necessarily a fix.
5. **Score the predictions after the event.** Use the Brier score (average squared gap between predicted chance and what happened).

**A warning on step 5:** the Finals has only 15 matches. A good model can look bad, and a bad one lucky, over that few matches. A meaningful verdict needs backtesting on many past matches, which is a post-v0 task.

## Decision register

These are the choices that are easy to make without noticing, each with my recommendation; mark each one in the last column before implementation starts.

| # | Decision | Options | Recommendation | Why it matters | Your call |
| --- | --- | --- | --- | --- | --- |
| 1 | Data source | Hand-collect from Tennis Abstract; archive mirror; Match Charting; WTA official | Hand-collect from Tennis Abstract | The mirror stops in June 2026 and misses the summer hard-court season | Agreed |
| 2 | Time window | Last 52 weeks; this season; career | Last 52 weeks | Shorter is more current but noisier; can shift a player's numbers by several points | Agreed |
| 3 | Surface bucket | All hard courts; outdoor hard only | All hard courts | Indian Wells is outdoor, but outdoor-only shrinks samples a lot | Agreed |
| 4 | Which matches count | Tour-level main draw incl. Slams; add qualifying; drop retirements | Tour-level main draw incl. Slams, retirements and walkovers excluded | Retired matches record points played while injured | Agreed |
| 5 | Pooling | Total points across matches; average of each match's percentage | Total points | Averaging percentages gives a short blowout the same weight as a three-hour match | Agreed |
| 6 | Combination formula | Average; additive | Average first, additive from milestone 5 | Moved our example favourite from 68% to 82% | Agreed |
| 7 | Tour average (additive method) | All tour-level hard-court matches; top-50 players only | All tour-level hard-court matches, same 52 weeks | Shifts every additive match-up | Agreed |
| 8 | Probability units | Whole numbers out of 10,000; decimals | Out of 10,000 | Needed for Bend to prove anything about chances | Agreed |
| 9 | Point cap per match | 1,000 points; none | 1,000, with capped matches reported | Bend requires every function to finish | Agreed |
| 10 | Random numbers | Counter-based hash per simulation; one shared generator | Counter-based hash | Lets simulations run in parallel and stay reproducible | Agreed |
| 11 | Number of runs | 100,000; 1,000,000 | 1,000,000, run as 2²⁰ = 1,048,576 (milestone 4) | Noise of about 0.1 points versus 0.3 | Agreed |
| 12 | Deciding-set format | 7-point tiebreak at 6–6; 10-point | 7-point, confirmed against the 2026 rulebook | A wrong format slightly changes every three-set result | Agreed |
| 13 | First server | Coin toss; higher-ranked player | Coin toss | Serving first is a small edge; a fixed choice biases toward one player | Agreed |
| 14 | Groups before the draw | Seeded random; real groups; custom groups | Seeded random until drawn, then real groups; custom for what-ifs | Fully random groups would sometimes pair the top two seeds, which the real draw never does | Agreed&#32; |
| 15 | Withdrawals | Ignore; model a chance of withdrawal | Ignore, and say so on the page | Modelling it needs data we don't have | Agreed |
| 16 | Prep and checking language | TypeScript; Python | TypeScript | One language with the Astro site; the data work here is small | Agreed |
| 17 | Passing inputs to Bend | Prep script writes a generated `.bend` parameters file; Bend reads CSV | Generated `.bend` file | Bend has no JSON support and slow text handling | Agreed |
| 18 | Where to run | Claude Code cloud; local PC; both | Build in the cloud; run full simulations there if session limits allow, else locally from the same repo | Bend needs Linux or macOS, which the cloud provides with no setup; local runs have no session time limits. CPU only; GPUs are out of scope | Agreed |
| 19 | Display precision? | Whole percentages; two decimals | Whole percentages | Decimals suggest accuracy the model does not have | Agreed |
| 20 | Seed | Fixed and published; random each run | Fixed and published: 20261108 (milestone 4) | Anyone can reproduce the exact numbers | Agreed |

## Open questions and roadmap

The biggest unknown is the toolchain: Bend 2 is young, so milestone 1 should prove it installs and compiles in the Claude Code cloud environment before anything else is built.

- [ ] Does Bend 2 install and run in Claude Code cloud, and how much CPU and run time does a session allow?
- [ ] Official 2026 WTA Finals match format and round-robin tiebreak rules (rulebook text, safoved in the repo).
- [ ] When is the group draw, and when is the eight-player field final?
- [ ] Does Tennis Abstract show 52-week hard-court serve and return points won for each player, with point counts?
- [ ] Repo name, and public or private?

**After v0, in order:** switch to the additive formula (if not already), opponent-strength adjustment, shrinkage using the sample sizes, recency weighting, big-point behaviour from Match Charting data, then backtesting on past tournaments. Fun spin-offs once the engine is trusted: replaying a real Slam draw, cross-era matchups, and player what-ifs.
