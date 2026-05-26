# bench-results/

Output directory for `bench-parallel.sh` runs. Each subdirectory here is a
single sweep. The `report.txt` inside each is a self-contained, human-readable
summary suitable for committing.

## Recommended structure

```
bench-results/
├── README.md                       (this file)
├── <sweep-name>/
│   ├── report.txt                  human-readable summary; commit this
│   ├── run.log                     full stdout of the script; commit this
│   ├── results.csv                 raw per-run data; commit this
│   ├── summary.txt                 leaderboard sorted by PAR-2; commit this
│   ├── per-instance.txt            config x instance matrix; commit this
│   ├── rows/                       intermediate per-run csv rows; *do not commit*
│   └── <config>/<inst>-<seed>.log  per-run palsat stdout; commit if small / useful
```

## Usage

From the repo root, on a large-core machine:

```sh
# typical 192-core invocation: 24 parallel palsat x 8 threads each
bash bench-parallel.sh \
  bench/configs-sweep4.tsv \
  bench/instances-veryhard.txt \
  "1,2,3,4,5" \
  big-sweep-2026-05-26
```

That writes everything to `bench-results/big-sweep-2026-05-26/`.

To resume after interruption, just re-invoke the same command — runs whose
`.row` file already exists are skipped.

## What to commit

Always:
- `report.txt`, `summary.txt`, `per-instance.txt`, `results.csv`, `run.log`

Optionally:
- The `<config>/<inst>-<seed>.log` per-run logs if disk-space permits and they
  contain interesting cache statistics worth preserving.

Never:
- `rows/` (intermediate scratch, harmless to delete)

## A `.gitignore` snippet to filter scratch:

```
bench-results/*/rows/
```
