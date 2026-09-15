# Percolator

**EXPERIMENTAL RESEARCH PROJECT — NOT AUDITED. Do NOT use with real funds. This is experimental software provided for learning and research purposes only. Use at your own risk.**

Risk engine library for permissionless perpetual futures on Solana.

Current normative spec: [`spec.md`](spec.md), **v16.8.3**.

A predictable perpetual-futures risk engine built around backed exits, lazy
overhang clearing, and bounded cranks.

If you want the `xy = k` of perpetual futures risk engines -- something you can reason about, audit, and run without human intervention -- the cleanest move is simple: stop treating profit like money. Treat it like what it really is in a stressed exchange: a junior claim on a shared balance sheet.

> No user can ever withdraw more value than actually exists on the exchange balance sheet.

## Three Invariants

A stressed perp exchange has three jobs:

1. **Backed exits:** when the vault is stressed, nobody can extract more value than the balance sheet can pay.
2. **Fair overhang clearing:** when positions go bankrupt, the residual is absorbed pro rata instead of by a discretionary ADL queue.
3. **Bounded cranks:** when the oracle moves, the live book is repriced only inside the configured one-step risk budget.

Percolator composes three mechanisms:

- **H** (the haircut ratio) makes positive PnL a junior claim on residual value.
- **A/K/F** (lazy side indices) settles mark moves, funding, and ADL overhang without selecting individual losers.
- **The price/funding envelope** bounds every exposed accrual step before K/F/price/slot state can mutate.

---

## H: Backed Exits

Capital is senior. Profit is junior. A single global ratio determines how much
released positive PnL is actually backed.

```
Residual  = max(0, V - C_tot - I - E - F)

              min(Residual, PNL_matured_pos_tot)
    h     =  ----------------------------------
                    PNL_matured_pos_tot
```

`Residual` is what is left for junior claims after **every** senior claim, and
there are four of them, not two:

| term | what it is | why it is senior |
|---|---|---|
| `C_tot` | deposited capital | principal is never junior to profit |
| `I` | insurance | reserved against future losses |
| `E` | `backing_provider_earnings_total` | utilization fees already owed to LPs |
| `F` | `source_fresh_backing_total` | backing earmarked to a specific claim |

`E` and `F` are easy to overlook and both are load-bearing. Omitting either
over-states the junior pool and promises winners atoms that someone else can
already withdraw — see the Kani proofs
`proof_v16_residual_excludes_senior_backing_provider_earnings` and
`proof_v16_residual_excludes_recoverable_counterparty_backing_principal`.

### Two ways a junior claim gets paid

`h` above governs **unsecured** junior claims — those with no dedicated
backing. A claim that *is* source-backed is paid from its own backing instead,
and does not compete for `Residual`:

```
account has source claims   ->  paid from that claim's backing (backing-limited)
otherwise                   ->  paid from Residual, pro-rata via h
```

That is a seniority *structure*, not an exemption, and `F` is what keeps the two
consistent: atoms earmarked to a backed claim are removed from `Residual`, so the
same atom is never promised to both a backed and an unsecured claimant.

When a losing account's principal is consumed it becomes exactly this kind of
earmarked backing for its counterparty — capital and `c_tot` fall by precisely
the amount that appears as backing, and the vault does not move. Value is
reshaped, never created (`proof_v16_capital_backed_loss_reservation_is_value_neutral_and_capital_capped`).

If fully backed, `h = 1`. If stressed, `h < 1`. Every profitable account sees
the same fraction of its *released* positive PnL:

```
ReleasedPos_i   = max(PNL_i, 0) - R_i
effective_pnl_i = floor(ReleasedPos_i * h)
```

Fresh profit sits in a per-account reserve `R_i` and converts to released
(matured) profit through admission and warmup. Only admitted matured profit
enters the haircut denominator (`PNL_matured_pos_tot`) and per-account effective
PnL.

This is the core anti-oracle-manipulation defense. An attacker who spikes a
price sees live gain locked in reserve, excluded from both the ratio and their
withdrawable amount, until the instruction policy admits it. Public wrappers
using untrusted live oracle or execution-price PnL must use nonzero admission
warmup; stress-threshold gating is not a substitute.

No rankings, no queue priority, no first-come advantage. The floor rounding is conservative — the sum of all effective PnL never exceeds what exists in the vault.

When the system is stressed, `h` falls and less profit converts. When losses
settle or buffers recover, `h` rises. Self-healing.

Flat accounts are always protected — `h` only gates profit extraction, never touches deposited capital.

---

## A/K/F: Fair Overhang Clearing

When a leveraged account goes bankrupt, two things need to happen: remove the position quantity from open interest, and distribute any uncovered deficit across the opposing side.

Traditional ADL queues pick specific counterparties and force-close them.
Percolator replaces the queue with lazy side indices:

- **A** scales everyone's effective position equally.
- **K** accumulates mark and ADL overhang effects.
- **F** accumulates funding effects.

```
effective_pos(i) = floor(basis_i * A / a_basis_i)
pnl_delta(i)     =
    floor(|basis_i| * ((K - k_snap_i) * FUNDING_DEN + (F - f_snap_i))
          / (a_basis_i * POS_SCALE * FUNDING_DEN))
```

When a liquidation reduces OI, `A` decreases -- every account on that side
shrinks by the same ratio. When a deficit is socialized, `K` shifts -- every
account absorbs the same per-unit loss. Funding moves through `F` the same way:
accounts settle against their snapshots when touched.

No account is singled out. Settlement is O(1) per account and order-independent.

### Markets Return to Healthy

A/K/F guarantees forward progress through a deterministic cycle:

**DrainOnly** — when `A` drops below a precision threshold, no new OI can be added. Positions can only close.

**ResetPending** — when OI reaches zero, the engine snapshots `K`, increments the epoch, and resets `A` back to 1. Remaining accounts settle their residual PnL exactly once when next touched.

**Normal** — once all stale accounts have settled and OI is confirmed zero, the side reopens for trading with full precision.

No admin intervention. No governance vote. The state machine always makes progress.

---

## Price/Funding Envelope

The third invariant is a system bound: an exposed market cannot be cranked
through an arbitrary oracle or funding jump in one step.

For any crank that advances the engine price while open interest exists, the
allowed price move is capped by elapsed slots:

```
abs(P_new - P_last) * 10_000
    <= max_price_move_bps_per_slot * dt * P_last
```

Equivalently, the normalized move is bounded by
`max_price_move_bps_per_slot * dt / 10_000`.

At a high level, the maximum price movement between exposed cranks is bounded by
the system's risk budget. If the market is configured around `L` times leverage,
the safe one-step move is roughly on the order of `1 / L`, with room reserved
for funding, liquidation fees, integer rounding, and fee floors/caps.

This turns "crank often enough" into a hard solvency boundary rather than an
operator preference. A stale or fast-moving oracle target must be fed into the
engine as a capped staircase of effective prices. Same-slot exposed cranks use
the previous price; they cannot mark live OI through a zero-time jump.

Active price or funding accrual also has a maximum elapsed-slot window; beyond
that, ordinary live catch-up fails closed and the wrapper must use recovery or
resolution.

Initialization proves a per-risk-notional envelope for the worst allowed
price/funding step plus liquidation fees. At runtime, before any K/F/price/slot
mutation, the engine checks that the next effective step stays inside that
envelope. If it does not fit, the crank fails closed instead of moving the
market into an unbudgeted state.

---

## How They Compose

| | H | A/K/F | Price/funding envelope |
|---|---|---|---|
| **Solves** | Backed exits | Bankrupt overhang clearing | Bounded live repricing |
| **Math** | Pro-rata profit scaling | Pro-rata position, mark, funding, and deficit scaling | Exact per-risk-notional loss budget |
| **Triggered by** | Withdrawal, conversion, settlement | Mark, funding, liquidation, reset | Live accrual/crank |
| **Failure mode** | Less profit is released | Side drains and resets | Crank fails closed or wrapper stair-steps |

Together:
- No user can withdraw more than exists.
- No user is singled out for forced closure.
- Flat accounts keep their deposits.
- Risk-increasing trades cannot count their own favorable execution slippage as margin.
- Markets recover through deterministic side resets.
- Exposed cranks are bounded to the configured price/funding budget.
- Raw oracle targets are wrapper-owned; the engine only sees capped effective prices.

A/K/F fairness is exact for open-position economics. H fairness is exact for the
currently stored realized claim set, not for the economically "true" claim set
you would get after globally touching every account.

The engine is not the whole public protocol by itself. A compliant wrapper must
enforce authorization, source and clamp oracle/funding inputs, use nonzero live
PnL admission for untrusted public flows, sync recurring fees when enabled, and
reject extraction-sensitive actions while raw oracle target and effective engine
price diverge.

---

## Features

- **v12.17 two-bucket warmup** — unrealized profit sits in a scheduled then pending reserve before entering the matured haircut denominator, bounding oracle-manipulation exposure
- **Per-side funding** — long and short funding indices (F coefficients) are tracked independently, enabling asymmetric funding rates
- **ADL via A/K coefficients** — position overhang is cleared lazily without singling out counterparties; O(1) per account, order-independent
- **Three-phase side reset** — `DrainOnly` → `ResetPending` → `Normal` guarantees markets always recover without admin intervention
- **No external dependencies** — pure `no_std` compatible Rust library; no CPI, no token transfers, no signer checks

## Build and Test

```bash
# Default suite
cargo test                          # 312 tests, 0 failures

# With the fuzz/property targets (v16_fuzzing is `required-features = ["fuzz"]`)
cargo test --features fuzz          # 365 tests, 0 failures

# With the O(N) account-table invariant scans. This feature is the ONLY build in which
# validate_shape_full_audit_scan / validate_asset_shape_for_view compile in at all, so the
# default suite being green says nothing about them. CI runs these two as the `audit-scan` job.
cargo test --features audit-scan --test v16_spec_tests   # 179 tests, 0 failures
cargo test --features audit-scan --lib                   # 67 tests, 0 failures
```

`v16_spec_tests` runs 179 under `audit-scan` and 180 by default: exactly one test is
`#[cfg(not(feature = "audit-scan"))]`, because its fixture is deliberately off-model for the
Live matched-book invariant — see the comment above
`v16_auto_crank_does_not_liquidate_against_unmatched_effective_oi`.

The `audit-scan` job is deliberately scoped to those two targets. `cargo test --features
audit-scan` across ALL targets is **not** green today: `tests/grief_econ_final.rs` is 5/2, and
both failures (`:146`, `:208`) are the same hand-written-fixture shape the spec suite's seven
had — `Err(InvalidConfig)` from `validate_shape()` on state a helper assigned directly, never
produced by an engine instruction. That is untriaged, so it is not in the gate yet.

There is no `test` feature; the declared features are `stress`, `fuzz`, `audit-scan` and
`fork-facade` (`Cargo.toml`), with `default = []`.

## Kani

**Pinned to Kani 0.67.0.** `scripts/run_kani_full_audit.sh` refuses to run against any other
version: harness counts, the JSON schema of `kani-list.json`, and which unstable flags are
required all move between Kani releases, and a results table that does not name its verifier
version cannot be reproduced.

```bash
# One-time setup
cargo install --locked kani-verifier@0.67.0
cargo kani setup

# All harnesses. --features fuzz is REQUIRED, not optional: [workspace.metadata.kani] sets
# `flags = { tests = true }`, so cargo builds every test target, and the v16_fuzzing target
# is `required-features = ["fuzz"]`. Without it cargo aborts before any proof runs:
#   error: target `v16_fuzzing` in package `percolator` requires the features: `fuzz`
cargo kani --tests --features fuzz

# One harness (the fully-qualified name; --exact matches same-named harnesses across files)
cargo kani --tests --features fuzz --jobs 1 --harness HARNESS_NAME

# Long audits: one harness per process, with a 20-minute cap and a results TSV.
# Linux only: the per-harness cap is `timeout 1200` (scripts/run_kani_full_audit.sh:83),
# a coreutils binary that macOS does not ship (`brew install coreutils` provides it as
# `gtimeout`). The script is unchanged; run it on Linux, or expect it to abort there.
bash scripts/run_kani_full_audit.sh
```

### Harness census

Counted at this checkout, not carried forward from a previous one:

| Class | Count | Where |
| --- | ---: | --- |
| `#[kani::proof]` harnesses | **328** | `tests/proofs_v16.rs` 283, `tests/proofs_v17_fork.rs` 30, `tests/proofs_v16_arithmetic.rs` 13, `tests/proofs_v16_asymmetric_a_accrual.rs` 2 |
| `#[kani::proof_for_contract]` harnesses | **0** | this fork has no `contracts` feature and no `src/v16_proofs.rs` |

```bash
# Reproduce both numbers. Exclude comment lines: a `#[kani::proof]` written inside a doc
# comment is not a harness (there are 3 such lines, e.g. tests/proofs_v17_fork.rs:1078).
grep -rn '#\[kani::proof\]' --include='*.rs' . | grep -vE ':\s*//' | wc -l   # 328
grep -rn '#\[kani::proof_for_contract' --include='*.rs' . | grep -vE ':\s*//' | wc -l  # 0
```

`kani-list.json` is the machine-readable form of the same census and agrees: 328
standard harnesses, 0 contract harnesses, `"kani-version": "0.67.0"`. Regenerate it with

```bash
# `cargo kani list` (0.67.0) accepts no cargo flags, so the features have to reach it
# through the manifest for the duration of the run.
sed -i.bak 's/flags = { tests = true }/flags = { tests = true, features = ["fuzz"] }/' Cargo.toml
cargo kani list --format json -Z stubbing    # -Z stubbing: tests/proofs_v17_fork.rs:1191 uses #[kani::stub]
mv Cargo.toml.bak Cargo.toml
```

**On the contract layer.** Upstream (`aeyakovenko/percolator`) carries a `contracts` feature and
61 `#[kani::proof_for_contract]` harnesses in `src/v16_proofs.rs`, run there with
`cargo kani --tests --features fuzz,contracts -Z function-contracts`. **That invocation does not
apply to this fork**: `Cargo.toml` declares no `contracts` feature and this tree has no
`src/v16_proofs.rs`, so the command fails at cargo. Five upstream contract properties are carried
here as plain `#[kani::proof]` harnesses that assert the same postcondition over the same
unconstrained domain — `proof_v16_terminal_source_haircut_reserved_exactly_once`,
`proof_v16_kernel_advance_leg_b_snap_rank_witness`,
`proof_v16_kernel_initial_margin_gate_exact_decision`,
`proof_v16_kernel_accumulate_batch_trade_exact_fold` and
`proof_v16_kernel_settle_principal_exact_paid_and_conservation` (plus
`proof_v16_cert_is_current_matches_the_favorable_action_gate` for upstream's
`contract_check_kernel_cert_is_current`). They are inside the 328, not additional to it; each
names its upstream contract in a comment above the harness.

**A SUCCESSFUL harness is not by itself evidence.** Kani reports SUCCESSFUL for a harness whose
`kani::cover!` properties are unreachable. Judge every result on its cover line as well —
`0 of N cover properties satisfied` means the harness proved nothing. The CI smoke job gates on
exactly that.

## Security

See [THREAT_MODEL.md](THREAT_MODEL.md) for the full trust model, known deferred findings, and deployment checklist.

## Specification

The normative spec is in [spec.md](spec.md). It covers the H haircut ratio, A/K coefficient mechanics, two-bucket warmup math, funding computation, and all state machine transitions.

## Open Source

Fork it, test it, send bug reports. Percolator is open research under Apache-2.0.

## References

- Tarun Chitra, *Autodeleveraging: Impossibilities and Optimization*, arXiv:2512.01112, 2025. https://arxiv.org/abs/2512.01112
