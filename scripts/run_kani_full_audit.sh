#!/usr/bin/env bash
# Full Kani audit: run all proofs one-by-one with 20-minute timeout each.
set -euo pipefail

# ---------------------------------------------------------------------------
# Kani version pin (2026-09-15).
#
# This script writes a results TSV that gets cited as evidence. A results table
# that does not name its verifier version cannot be reproduced, and the things
# that move between Kani releases are exactly the things the table reports:
# which unstable flags a harness needs to compile at all, the JSON schema of
# `kani-list.json` (checked in at the repo root, regenerated with 0.67.0), and
# therefore the harness count itself. Checking the version here, before anything
# runs, is cheaper than discovering the mismatch in a merged claim.
#
# `cargo kani --version` prints e.g. "cargo-kani 0.67.0".
# ---------------------------------------------------------------------------
KANI_VERSION_REQUIRED="0.67.0"
if ! command -v cargo-kani > /dev/null 2>&1 && ! cargo kani --version > /dev/null 2>&1; then
    echo "ERROR: Kani is not installed." >&2
    echo "       This repo is pinned to Kani ${KANI_VERSION_REQUIRED}. Install it with:" >&2
    echo "         cargo install --locked kani-verifier@${KANI_VERSION_REQUIRED} && cargo kani setup" >&2
    exit 1
fi
KANI_VERSION_ACTUAL="$(cargo kani --version 2>/dev/null | awk '{print $NF}')"
if [ "${KANI_VERSION_ACTUAL}" != "${KANI_VERSION_REQUIRED}" ]; then
    echo "ERROR: Kani version mismatch." >&2
    echo "       required: ${KANI_VERSION_REQUIRED}" >&2
    echo "       found:    ${KANI_VERSION_ACTUAL:-<could not parse \`cargo kani --version\`>}" >&2
    echo "" >&2
    echo "       The results TSV this script writes is cited as evidence, and harness" >&2
    echo "       counts, required unstable flags, and the kani-list.json schema all move" >&2
    echo "       between Kani releases. Re-pin deliberately, or install the pinned version:" >&2
    echo "         cargo install --locked kani-verifier@${KANI_VERSION_REQUIRED} && cargo kani setup" >&2
    echo "" >&2
    echo "       If you are intentionally re-pinning, update KANI_VERSION_REQUIRED here AND" >&2
    echo "       the Kani section of README.md, and regenerate kani-list.json." >&2
    exit 1
fi
echo "Kani ${KANI_VERSION_ACTUAL} (pinned)"

cd /home/anatoly/percolator

OUTFILE="/home/anatoly/percolator/kani_audit_full.tsv"
FINAL_OUTFILE="/home/anatoly/percolator/kani_audit_final.tsv"
AUDIT_DATE=$(date +%F)
echo -e "proof\ttime_s\tstatus" > "$OUTFILE"

# Collect all proof harness names from all proof files. Some harnesses have
# more than three attribute lines, so grep -A is not sufficient.
mapfile -t PROOFS < <(python3 - <<'PY'
import pathlib
import re

names = []
for path in sorted(pathlib.Path("tests").glob("proofs_*.rs")):
    text = path.read_text()
    starts = list(re.finditer(r"#\[kani::proof\]", text))
    for i, start in enumerate(starts):
        end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
        body = text[start.start():end]
        match = re.search(r"fn\s+([A-Za-z_0-9]+)\s*\(", body)
        if match:
            names.append(match.group(1))

for name in sorted(set(names)):
    print(name)
PY
)

TOTAL=${#PROOFS[@]}
COUNT=0
PASS=0
FAIL=0
TIMEOUTS=0

for proof in "${PROOFS[@]}"; do
    COUNT=$((COUNT + 1))
    echo "[$COUNT/$TOTAL] Running: $proof"
    START=$(date +%s)
    LOGFILE=$(mktemp)

    if timeout 1200 cargo kani --tests --exact --harness "$proof" --output-format terse > "$LOGFILE" 2>&1; then
        STATUS="PASS"
        PASS=$((PASS + 1))
    else
        EXIT_CODE=$?
        if [ $EXIT_CODE -eq 124 ]; then
            STATUS="TIMEOUT"
            TIMEOUTS=$((TIMEOUTS + 1))
        else
            STATUS="FAIL"
        fi
        FAIL=$((FAIL + 1))
    fi
    tail -3 "$LOGFILE" || true
    rm -f "$LOGFILE"

    END=$(date +%s)
    ELAPSED=$((END - START))
    echo -e "${proof}\t${ELAPSED}\t${STATUS}" >> "$OUTFILE"
    echo "  -> $STATUS (${ELAPSED}s)"
done

echo ""
awk -F'\t' -v note="overnight-${AUDIT_DATE}" '
    BEGIN { OFS = "\t" }
    NR == 1 { print $1, $2, $3, "note"; next }
    { print $1, $2, $3, note }
' "$OUTFILE" > "$FINAL_OUTFILE"

echo "========================================="
echo "SUMMARY: $PASS passed, $FAIL failed/timeout ($TIMEOUTS timeout) out of $TOTAL"
echo "Results saved to: $OUTFILE"
echo "Final timings saved to: $FINAL_OUTFILE"
echo "========================================="
