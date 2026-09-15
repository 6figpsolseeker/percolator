#!/usr/bin/env python3
"""Kani harness census: the checked-in list, the source tree, and the required set.

Three independent views of "which harnesses exist" have to agree, or every count
this repo publishes is guesswork:

  A. the source tree      -- every `#[kani::proof]` in tests/*.rs, as (file, name)
  B. kani-list.json       -- the checked-in artefact `cargo kani list` produces
  C. .github/kani/*.tsv   -- the sets CI actually runs

They have disagreed before. At 2c38570a, kani-list.json declared 305 harnesses
across ten test files, none of which existed in the tree, while the workflow's own
comment said 240 and README.md said 471, against a measured 328. A stale list is
not cosmetic: it is how a harness gets renamed out of the required set with nobody
noticing, and `cargo kani --exact --harness <gone-name>` fails with the same
message as a cfg-gated-out harness.

Subcommands
-----------
  census                 print the tree census as TSV (file, name, line, covers)
  check                  A == B, and |A| == kani-list.json totals; exit 1 on drift
  check-required FILE    every name in FILE (col 1) exists in the tree, exactly as
                         many times as column 2 of the shard file says (default 1)
  shards N [COSTS] [HEAVY] [EXCLUDED]
                         print a bin-packed shard assignment for the FULL census:
                         TSV of (shard, name, expected_count, cost_s). Names in
                         HEAVY get a shard to themselves; names in EXCLUDED are
                         assigned shard 0, which no matrix leg selects, so they are
                         planned and counted but NOT RUN; the rest are LPT-packed
                         into the remaining shards using COSTS (default 120 s for
                         a name with no measured cost -- a new harness is included
                         automatically, which is the point of deriving this from
                         the census rather than from a checked-in list).

Everything here is a static grep. It is bookkeeping, never evidence that a
harness proves anything: that only comes from running it, and only then if its
cover properties are satisfied.
"""

import json
import pathlib
import re
import sys

PROOF_ATTR = re.compile(r"#\[kani::proof\]")
FN_NAME = re.compile(r"fn\s+([A-Za-z_0-9]+)\s*\(")
COVER = re.compile(r"kani::cover!")


def strip_line_comments(text):
    """Blank out `//`-comment lines.

    A `#[kani::proof]` written inside a doc comment is NOT a harness. The tree has
    had three of those (and five commented-out `kani::proof_for_contract`), which is
    exactly the difference between a raw grep of 331+ and the real census.
    """
    out = []
    for line in text.split("\n"):
        out.append("" if line.lstrip().startswith("//") else line)
    return "\n".join(out)


def census(root):
    rows = []
    for path in sorted((root / "tests").glob("*.rs")):
        text = strip_line_comments(path.read_text())
        starts = [m.start() for m in PROOF_ATTR.finditer(text)]
        for i, start in enumerate(starts):
            end = starts[i + 1] if i + 1 < len(starts) else len(text)
            body = text[start:end]
            m = FN_NAME.search(body)
            if not m:
                continue
            rows.append(
                {
                    "file": str(path.relative_to(root)),
                    "name": m.group(1),
                    "line": text[:start].count("\n") + 1,
                    "covers": len(COVER.findall(body)),
                }
            )
    return rows


def load_json_list(root):
    data = json.loads((root / "kani-list.json").read_text())
    pairs = []
    for f, names in data.get("standard-harnesses", {}).items():
        for n in names:
            pairs.append((f, n))
    return data, pairs


def cmd_census(root):
    for r in census(root):
        print(f"{r['file']}\t{r['name']}\t{r['line']}\t{r['covers']}")
    return 0


def cmd_check(root):
    rows = census(root)
    tree = sorted((r["file"], r["name"]) for r in rows)
    data, jpairs = load_json_list(root)
    js = sorted(jpairs)
    ok = True

    print(f"kani-list.json version : {data.get('kani-version')}")
    print(f"tree  #[kani::proof]   : {len(tree)} ({len(set(n for _, n in tree))} distinct names)")
    print(f"kani-list.json entries : {len(js)}")
    totals = data.get("totals", {})
    print(f"kani-list.json totals  : {totals}")

    only_tree = sorted(set(tree) - set(js))
    only_json = sorted(set(js) - set(tree))
    if only_tree:
        ok = False
        print(f"::error::{len(only_tree)} harness(es) in the tree are missing from kani-list.json")
        for f, n in only_tree:
            print(f"  tree-only: {f}\t{n}")
    if only_json:
        ok = False
        print(f"::error::{len(only_json)} entr(ies) in kani-list.json do not exist in the tree")
        for f, n in only_json:
            print(f"  json-only: {f}\t{n}")
    if totals.get("standard-harnesses") != len(js):
        ok = False
        print(
            "::error::kani-list.json totals.standard-harnesses="
            f"{totals.get('standard-harnesses')} but the file lists {len(js)} harnesses"
        )
    if len(tree) != len(js):
        ok = False
        print(f"::error::census mismatch: tree {len(tree)} vs kani-list.json {len(js)}")

    dupes = {}
    for f, n in tree:
        dupes.setdefault(n, []).append(f)
    multi = {n: fs for n, fs in dupes.items() if len(fs) > 1}
    if multi:
        # Not an error: it is a documented property of this tree, and the reason
        # every shard line carries an expected-match count.
        print(f"note: {len(multi)} harness name(s) are defined more than once "
              f"-- `--exact --harness` runs ALL of them:")
        for n, fs in sorted(multi.items()):
            print(f"  {n}: {', '.join(fs)}")

    zero = [r for r in rows if r["covers"] == 0]
    print(f"note: {len(zero)} harness(es) declare no kani::cover! "
          f"-- a SUCCESSFUL on any of these is evidence-free")

    if not ok:
        print("::error::Kani census check FAILED — regenerate kani-list.json "
              "(see the Kani section of README.md)")
        return 1
    print("Kani census check OK")
    return 0


def cmd_check_required(root, listfile):
    rows = census(root)
    counts = {}
    for r in rows:
        counts[r["name"]] = counts.get(r["name"], 0) + 1
    covers = {}
    for r in rows:
        covers[r["name"]] = covers.get(r["name"], 0) + r["covers"]

    ok = True
    n = 0
    for raw in pathlib.Path(listfile).read_text().split("\n"):
        line = raw.rstrip("\r")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        name = parts[0].strip()
        expect = int(parts[1]) if len(parts) > 1 and parts[1].strip() else 1
        n += 1
        have = counts.get(name, 0)
        if have != expect:
            ok = False
            print(f"::error::{name}: defined {have} time(s) in the tree, "
                  f"{listfile} expects {expect}")
        elif covers.get(name, 0) == 0:
            ok = False
            print(f"::error::{name}: declares no kani::cover! — it cannot supply "
                  f"non-vacuity evidence and must not sit in a required set")
    if n == 0:
        print(f"::error::{listfile} lists no harnesses")
        return 1
    print(f"checked {n} required harness name(s) against the tree census")
    if not ok:
        return 1
    print("required-set check OK")
    return 0


def _read_name_list(path):
    names = set()
    if path and pathlib.Path(path).exists():
        for raw in pathlib.Path(path).read_text().split("\n"):
            line = raw.strip()
            if line and not line.startswith("#"):
                names.add(line.split("\t")[0])
    return names


def cmd_shards(root, nshards, costs_file=None, heavy_file=None, excluded_file=None):
    rows = census(root)
    counts = {}
    for r in rows:
        counts[r["name"]] = counts.get(r["name"], 0) + 1

    costs = {}
    if costs_file and pathlib.Path(costs_file).exists():
        for raw in pathlib.Path(costs_file).read_text().split("\n"):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            p = line.split("\t")
            if len(p) >= 2:
                try:
                    costs[p[0]] = int(float(p[1]))
                except ValueError:
                    pass
    heavy = _read_name_list(heavy_file)
    excluded = _read_name_list(excluded_file)

    DEFAULT = 120
    names = sorted(counts)
    # Shard 0 is never selected by a matrix leg: these are planned, counted against
    # the census, and reported as NOT RUN — never as passes.
    assign_zero = [n for n in names if n in excluded]
    heavy_names = [n for n in names if n in heavy and n not in excluded]
    rest = [n for n in names if n not in heavy and n not in excluded]

    assign = {n: 0 for n in assign_zero}
    shard = 1
    for n in heavy_names:
        if shard > nshards:
            break
        assign[n] = shard
        shard += 1
    first_general = shard
    if first_general > nshards:
        # More heavy harnesses than shards: fall back to packing everything except
        # the excluded set (which must stay on shard 0 or it would kill a runner).
        assign = {n: 0 for n in assign_zero}
        first_general = 1
        rest = [n for n in names if n not in excluded]

    load = {s: 0 for s in range(first_general, nshards + 1)}
    if not load:
        load = {nshards: 0}
    rest.sort(key=lambda n: -costs.get(n, DEFAULT))
    for n in rest:
        s = min(load, key=lambda k: (load[k], k))
        assign[n] = s
        load[s] += costs.get(n, DEFAULT)

    for n in names:
        print(f"{assign[n]}\t{n}\t{counts[n]}\t{costs.get(n, DEFAULT)}")
    return 0


def main(argv):
    root = pathlib.Path(__file__).resolve().parent.parent
    if len(argv) < 2:
        print(__doc__)
        return 2
    cmd = argv[1]
    if cmd == "census":
        return cmd_census(root)
    if cmd == "check":
        return cmd_check(root)
    if cmd == "check-required":
        if len(argv) < 3:
            print("usage: kani_census.py check-required <file>", file=sys.stderr)
            return 2
        return cmd_check_required(root, argv[2])
    if cmd == "shards":
        if len(argv) < 3:
            print("usage: kani_census.py shards <n> [costs.tsv] [heavy.txt] [excluded.tsv]",
                  file=sys.stderr)
            return 2
        return cmd_shards(
            root,
            int(argv[2]),
            argv[3] if len(argv) > 3 else None,
            argv[4] if len(argv) > 4 else None,
            argv[5] if len(argv) > 5 else None,
        )
    print(f"unknown subcommand: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
