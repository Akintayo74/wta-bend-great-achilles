# Snapshot 2026-10-04 (provisional)

Trimmed extracts of Tennis Abstract data, written by `prep/fetch.ts --date
2026-10-04`. `prep/collect.ts` turns them into `data/players.csv` and
`data/tour.csv`.

- `players.csv`: every hard-court match of the 30 players in
  `data/players.csv` (Race to the WTA Finals top 30, as of 28 Sep 2026), with
  tournament dates 2025-10-06 to 2026-10-04. These come from Tennis
  Abstract's per-player data files. One row per (player, match); the other
  filters are applied by `collect.ts`, so the rows it leaves out are still
  here. Rows with a blank score are matches not yet played.
- `tour.csv`: every hard-court row of Tennis Abstract's leaderboard file
  (every tour-level match involving a current top-50 player), 2025-09-23 to
  2026-09-21, the latest 52 weeks in that file.
- `manifest.csv`: each downloaded file's address, date read, size, SHA-256
  and latest match.

Columns: `pts` is the player's serve points, `fwon` and `swon` her first- and
second-serve points won, and `opts`, `ofwon`, `oswon` the same for her
opponent.

**Cross-check against official WTA match statistics** (api.wtatennis.com),
serve points played and won for both players:

| Match | Official | Tennis Abstract |
| --- | --- | --- |
| Cincinnati 2026 R64, Sabalenka v Gibson | 81/50, 66/34 | 81/50, 66/34 |
| Cincinnati 2026 R16, Sabalenka v Bejlek | 82/44, 69/40 | 82/44, 69/40 |
| Toronto 2026 R16, Sabalenka v Alexandrova | 113/63, 100/59 | 113/63, 100/59 |
| Beijing 2026 R64, Rybakina v Charaeva | 93/52, 78/47 | 93/52, 78/47 |

Source: Tennis Abstract (tennisabstract.com, Jeff Sackmann), licensed
CC BY-NC-SA 4.0. This extract is shared under the same licence.
