#!/usr/bin/env bash
# Run one shard of Kani harnesses, one harness per `cargo kani` invocation, and write a TSV.
#
# Used by BOTH .github/workflows/ci.yml (the PR tier) and
# .github/workflows/kani-full.yml (the scheduled full-census tier), and runnable
# locally with exactly the same command line, so a CI result and a local result
# are the same measurement.
#
# Usage:
#   scripts/kani_ci_shard.sh <shard-file> <out.tsv>
#
# <shard-file> is one harness per line; blank lines and lines starting with '#'
# are ignored. A line may carry a second, tab-separated field: the number of
# harnesses `--exact --harness <name>` is expected to match (default 1). That
# column exists because of a real trap: the repo has ONE duplicated harness name
# (proof_v16_adjust_u128_applies_exact_delta_or_fails_closed, defined in both
# tests/proofs_v16.rs and tests/proofs_v16_arithmetic.rs) and `--exact` runs BOTH.
# A count mismatch in either direction is a failure: it means a harness was
# renamed, deleted, cfg-gated out, or newly duplicated, and "SUCCESSFUL" would
# otherwise be reported for a name that no longer proves what the list claims.
#
# Environment:
#   KANI_REQUIRE_COVERS=1  (default)  a harness must print `N of N cover properties
#                                     satisfied` with N > 0, or it FAILS. Kani reports
#                                     SUCCESSFUL for a harness whose covers are
#                                     unreachable, and for a harness that declares no
#                                     kani::cover! at all it prints no cover line —
#                                     both are evidence-free passes.
#   KANI_REQUIRE_COVERS=0             covers are recorded and classified but do not
#                                     fail the shard; used by the scheduled tier, which
#                                     must run the 28 in-tree zero-cover harnesses and
#                                     reports them as EVIDENCE-FREE instead of as passes.
#   KANI_TIMEOUT_S                    optional per-harness timeout in seconds. Applied
#                                     only if a `timeout` binary exists (GNU coreutils,
#                                     or `gtimeout` from Homebrew). macOS has neither by
#                                     default, so this is best-effort by design rather
#                                     than a hard requirement — the workflow's
#                                     timeout-minutes is the real backstop.
#   CARGO_TARGET_DIR                  honoured as usual; set it per shard when running
#                                     several shards on one machine.
#
# Output TSV columns (a header row is written):
#   harness  status  wall_s  rc  verified  failures  total  covers_sat  covers_total  checks_failed  checks_total
# status is one of: OK  OK-NOCOVER  OK-PARTIAL-COVER  VACUOUS  FAILED  COUNT-MISMATCH  ERROR
#
# Exit status: 0 only if every harness in the shard ended OK (or, with
# KANI_REQUIRE_COVERS=0, OK / OK-NOCOVER / OK-PARTIAL-COVER).

set -uo pipefail

SHARD_FILE="${1:-}"
OUT_TSV="${2:-}"
if [ -z "$SHARD_FILE" ] || [ -z "$OUT_TSV" ]; then
  echo "usage: $0 <shard-file> <out.tsv>" >&2
  exit 2
fi
if [ ! -f "$SHARD_FILE" ]; then
  echo "ERROR: shard file not found: $SHARD_FILE" >&2
  exit 2
fi

REQUIRE_COVERS="${KANI_REQUIRE_COVERS:-1}"
TIMEOUT_S="${KANI_TIMEOUT_S:-}"

# Portable timeout: GNU coreutils `timeout`, Homebrew `gtimeout`, or nothing.
# (The in-tree scripts/run_kani_full_audit.sh hardcodes `timeout`, which does not
# exist on macOS; this one degrades instead of dying.)
TIMEOUT_BIN=""
if [ -n "$TIMEOUT_S" ]; then
  if command -v timeout > /dev/null 2>&1; then
    TIMEOUT_BIN="timeout"
  elif command -v gtimeout > /dev/null 2>&1; then
    TIMEOUT_BIN="gtimeout"
  else
    echo "note: no timeout/gtimeout on PATH — KANI_TIMEOUT_S=${TIMEOUT_S} not applied" >&2
  fi
fi

LOGDIR="$(dirname "$OUT_TSV")/logs"
mkdir -p "$LOGDIR"
printf 'harness\tstatus\twall_s\trc\tverified\tfailures\ttotal\tcovers_sat\tcovers_total\tchecks_failed\tchecks_total\n' > "$OUT_TSV"

FAILED=0
RAN=0

while IFS= read -r LINE || [ -n "$LINE" ]; do
  # strip CR (a shard file edited on Windows would otherwise produce a name no
  # harness matches, and `--exact` failing to match is the same message shape as
  # a cfg-gated-out harness)
  LINE="${LINE%$'\r'}"
  case "$LINE" in
    ''|'#'*) continue ;;
  esac
  H="${LINE%%$'\t'*}"
  EXPECT="${LINE#*$'\t'}"
  if [ "$EXPECT" = "$LINE" ] || [ -z "$EXPECT" ]; then EXPECT=1; fi

  RAN=$((RAN + 1))
  LOG="$LOGDIR/$H.log"
  echo "=== $H (expect $EXPECT harness match(es)) ==="

  START=$(date +%s)
  if [ -n "$TIMEOUT_BIN" ]; then
    "$TIMEOUT_BIN" "$TIMEOUT_S" \
      cargo kani --tests --features fuzz --jobs 1 --exact --harness "$H" --output-format terse \
      > "$LOG" 2>&1
  else
    cargo kani --tests --features fuzz --jobs 1 --exact --harness "$H" --output-format terse \
      > "$LOG" 2>&1
  fi
  RC=$?
  END=$(date +%s)
  WALL=$((END - START))

  # `Complete - N successfully verified harnesses, M failures, K total.`
  SUMMARY=$(grep -F 'Complete - ' "$LOG" | tail -1)
  VERIFIED=$(printf '%s' "$SUMMARY" | sed -n 's/.*Complete - \([0-9][0-9]*\) successfully verified.*/\1/p')
  FAILURES=$(printf '%s' "$SUMMARY" | sed -n 's/.*, \([0-9][0-9]*\) failures.*/\1/p')
  TOTAL=$(printf '%s' "$SUMMARY" | sed -n 's/.*, \([0-9][0-9]*\) total.*/\1/p')
  [ -z "$VERIFIED" ] && VERIFIED="-"
  [ -z "$FAILURES" ] && FAILURES="-"
  [ -z "$TOTAL" ] && TOTAL="-"

  # `** N of M cover properties satisfied` — summed over every harness the name matched.
  COV_SAT=0
  COV_TOT=0
  COV_LINES=0
  while IFS= read -r CL; do
    [ -z "$CL" ] && continue
    COV_LINES=$((COV_LINES + 1))
    S=$(printf '%s' "$CL" | sed -n 's/.*[^0-9]\([0-9][0-9]*\) of \([0-9][0-9]*\) cover properties satisfied.*/\1/p')
    T=$(printf '%s' "$CL" | sed -n 's/.*[^0-9]\([0-9][0-9]*\) of \([0-9][0-9]*\) cover properties satisfied.*/\2/p')
    COV_SAT=$((COV_SAT + ${S:-0}))
    COV_TOT=$((COV_TOT + ${T:-0}))
  done <<EOF
$(grep -E '[0-9]+ of [0-9]+ cover properties satisfied' "$LOG" || true)
EOF

  # `** N of M failed` check totals (the first field on each summary line)
  CHK_FAIL=0
  CHK_TOT=0
  while IFS= read -r KL; do
    [ -z "$KL" ] && continue
    S=$(printf '%s' "$KL" | sed -n 's/^[^0-9]*\([0-9][0-9]*\) of \([0-9][0-9]*\) failed.*/\1/p')
    T=$(printf '%s' "$KL" | sed -n 's/^[^0-9]*\([0-9][0-9]*\) of \([0-9][0-9]*\) failed.*/\2/p')
    CHK_FAIL=$((CHK_FAIL + ${S:-0}))
    CHK_TOT=$((CHK_TOT + ${T:-0}))
  done <<EOF
$(grep -E '^\s*\*\* [0-9]+ of [0-9]+ failed' "$LOG" || true)
EOF

  STATUS="OK"
  if [ "$RC" -ne 0 ]; then
    STATUS="ERROR"
  elif [ "$TOTAL" = "-" ] || [ "$VERIFIED" = "-" ] || [ "$FAILURES" = "-" ]; then
    # No `Complete -` line at all: kani did not get as far as a verdict.
    STATUS="ERROR"
  elif [ "$TOTAL" != "$EXPECT" ]; then
    # Either --exact matched more harnesses than the list declares (the duplicate-name
    # trap) or fewer (renamed / deleted / cfg-gated out).
    STATUS="COUNT-MISMATCH"
  elif [ "$FAILURES" != "0" ] || [ "$VERIFIED" != "$TOTAL" ]; then
    STATUS="FAILED"
  elif [ "$COV_LINES" -eq 0 ]; then
    STATUS="OK-NOCOVER"
  elif [ "$COV_SAT" -eq 0 ]; then
    STATUS="VACUOUS"
  elif [ "$COV_SAT" -ne "$COV_TOT" ]; then
    STATUS="OK-PARTIAL-COVER"
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$H" "$STATUS" "$WALL" "$RC" "$VERIFIED" "$FAILURES" "$TOTAL" \
    "$COV_SAT" "$COV_TOT" "$CHK_FAIL" "$CHK_TOT" >> "$OUT_TSV"

  case "$STATUS" in
    OK)
      echo "  -> OK ${WALL}s  covers ${COV_SAT}/${COV_TOT}  checks ${CHK_FAIL}/${CHK_TOT} failed"
      ;;
    OK-NOCOVER|OK-PARTIAL-COVER|VACUOUS)
      if [ "$REQUIRE_COVERS" = "1" ]; then
        echo "::error::$H: ${STATUS} — Kani reported SUCCESSFUL but covers are ${COV_SAT} of ${COV_TOT} (no non-vacuity evidence). A harness in the required PR tier must satisfy every cover property it declares, and must declare at least one."
        FAILED=$((FAILED + 1))
      else
        echo "  -> ${STATUS} ${WALL}s  covers ${COV_SAT}/${COV_TOT}  (EVIDENCE-FREE: recorded, not counted as proof)"
      fi
      ;;
    COUNT-MISMATCH)
      echo "::error::$H: --exact matched ${TOTAL} harness(es), the list declares ${EXPECT}. Renamed, deleted, cfg-gated out, or newly duplicated."
      tail -20 "$LOG" || true
      FAILED=$((FAILED + 1))
      ;;
    *)
      echo "::error::$H: ${STATUS} (rc=${RC}, verified=${VERIFIED}, failures=${FAILURES}, total=${TOTAL})"
      tail -40 "$LOG" || true
      FAILED=$((FAILED + 1))
      ;;
  esac
done < "$SHARD_FILE"

echo ""
echo "shard: ran ${RAN} harness name(s), ${FAILED} failing"

# A shard that ran nothing is not a pass. This is the same trap as a `cargo test`
# guard that reads only the exit code while the test file has zero tests
# (`running 0 tests` -> ok, exit 0), and as `--exact` on a name that matches
# nothing. Assert the count, never the exit code alone.
if [ "$RAN" -eq 0 ]; then
  echo "::error::shard file ${SHARD_FILE} produced 0 harnesses to run"
  exit 1
fi

[ "$FAILED" -eq 0 ] || exit 1
exit 0
