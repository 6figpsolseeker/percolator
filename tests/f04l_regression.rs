//! F-04-L regression suite — the lifecycle-`DrainOnly` wind-down arm of
//! `leg_is_dead_for_forfeit`, and the three states it must still refuse.
//!
//! Register row F-04-L (decision memo `verify/items/F-04-L.md`, option (ii)). F-04
//! (`9de7eb9d`) gated the side-mode disjunct of `leg_is_dead_for_forfeit` on
//! `asset_lifecycle ∈ {Recovery, Retired}`, which closed X-01/X-02/AS-02 — and closed the
//! documented prediction-slot wind-down with it: a lifecycle-`DrainOnly` asset holding a dead
//! counterparty leg had NO owner-callable exit left (`retire_empty_asset_not_atomic` refuses
//! while the leg is stored, a second unilateral reduce refuses once the opposite side is
//! `ResetPending`, and only an admin `force_asset_recovery_not_atomic` could move it on).
//! That contradicts `av spec.md:1621-1623` ("Wrappers MUST also expose the owner-authorized
//! risk-reducing, cure-and-cancel, dead-leg forfeit/detach, resolved-claim, and
//! rebalance-on-touch routes required for user exits") and breaks Toly's own wrapper
//! regressions `aeyakovenko/percolator-prog` `b4ff060e` and `74c31b39`.
//!
//! THE FIX: a third arm, `asset_lifecycle == DrainOnly && oi_eff_long_q == 0 &&
//! oi_eff_short_q == 0`. It is safe by a WRITE-SITE argument, not by search: the forfeit's only
//! `oi_eff` writes are `kernel_clear_leg`'s (`72289b24:src/v16.rs:1472` long / `:1498` short)
//! and `kernel_retain_leg_as_pending_obligation`'s (`:1302` / `:1312`) `checked_sub` on the
//! FORFEITED side alone, so with the pair already at `0 == 0` every such write is either of zero
//! or underflows to `CounterUnderflow` and fails closed. The pair stays `0 == 0`, which is what
//! `av spec.md:946` + `:952` ("if Live: OI_eff_long == OI_eff_short", for every
//! Active/DrainOnly/Recovery asset side) require and what `validate_asset_shape_for_view`'s
//! matched-book conjunct checks — satisfied verbatim, not exempted.
//!
//! THIS FILE ASSERTS THE FIXED BEHAVIOUR:
//!   (a) `f04l_drainonly_zero_oi_owner_forfeit_clears_both_sides_and_the_slot_retires_and_reuses`
//!       — the prediction wind-down at engine level: forfeit `Ok`, both sides cleared, retire,
//!         reactivate, other assets' legs untouched.
//!   (b) `f04l_drainonly_with_live_oi_forfeit_is_still_refused`
//!       — the discriminating negative: same lifecycle, NON-zero pair -> `LockActive`.
//!   (c) `f04l_active_lifecycle_drainonly_side_mode_forfeit_is_still_refused`
//!       — the X-01 shape -> `LockActive` (F-04's guarantee, unchanged).
//!   (d) `f04l_c04_recovery_lifecycle_owner_exit_still_works`
//!       — C-04's owner exit on a Recovery-lifecycle asset, unchanged.
//!
//! Every test carries a non-vacuity guard asserting the state it claims to be in BEFORE the
//! call under test, so none of them can pass by testing an empty fixture.
//!
//! Run:
//!   cargo test --test f04l_regression
//!   cargo test --features audit-scan --test f04l_regression

use percolator::{
    v16_domain_count_for_market_slots, AssetLifecycleV16, AssetStateV16, EngineAssetSlotV16Account,
    Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, MarketModeV16,
    PortfolioAccountV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, RebalanceRequestV16, SideModeV16, SideV16, TradeRequestV16,
    V16Config, V16Error, V16PodU64,
};
use percolator::{ADL_ONE, MIN_A_SIDE, POS_SCALE};

const PRICE: u64 = 1_000_000;
const PRICE_1: u64 = 1_900_000; // <= +90% of PRICE   (max_price_move_bps_per_slot = 9_000)
const PRICE_2: u64 = 3_610_000; // <= +90% of PRICE_1
const HALF_Q: u128 = POS_SCALE / 2;

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn signed_q(q: u128) -> i128 {
    i128::try_from(q).unwrap()
}

/// `account_fixture` from `tests/v16_spec_tests.rs:118-130` (as `tests/f04_regression.rs:66`).
fn account_fixture(market_slots: u32, account_seed: u8) -> PortfolioAccountV16Account {
    let (market_id, _, owner) = ids();
    let header = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
        market_id,
        [account_seed; 32],
        owner,
    ));
    let _ = v16_domain_count_for_market_slots(market_slots).unwrap();
    let mut account = PortfolioAccountV16Account::default();
    account.init_empty_in_place(header).unwrap();
    account
}

/// `decode_market_mode` (`72289b24:src/v16.rs:23117-23124`), as `tests/f04_regression.rs:143`.
fn decode_mode(header: &MarketGroupV16HeaderAccount) -> MarketModeV16 {
    match header.mode {
        0 => MarketModeV16::Live,
        1 => MarketModeV16::Resolved,
        2 => MarketModeV16::Recovery,
        other => panic!("unknown market mode byte {other}"),
    }
}

// =================================================================================================
// PART A — the prediction-slot wind-down, driven at ENGINE level.
//
// This mirrors, instruction for instruction, the flow of Toly's wrapper regression
// `v16_wrapper_prediction_asset_can_drain_retire_and_reactivate_without_closing_other_legs`
// (`aeyakovenko/percolator-prog` `b4ff060e`, carried in our fork at
// `origin/fix/W-19:tests/v16_wrapper.rs`), whose upstream write-up states the invariant as
// "both sides can be cleared while other assets stay open"
// (`upstream/v16:scripts/security.md:502-506`, disposition `PASS_SAFE`).
// =================================================================================================

/// Two asset slots, one of which (index 1) is the "prediction" slot that gets drained, cleared,
/// retired and reused while asset 0 keeps a live matched book throughout.
fn prediction_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(2, 2, 0, 10);
    cfg.max_price_move_bps_per_slot = 9_000;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 2, 0).unwrap();
    let mut markets = (0..2)
        .map(|i| Market::new(i as u64, EngineAssetSlotV16Account::default()))
        .collect::<Vec<_>>();
    for (i, slot) in markets.iter_mut().enumerate() {
        header
            .activate_empty_asset_slot_not_atomic(i as u32, &mut slot.engine, PRICE, (i + 1) as u64)
            .unwrap();
    }
    {
        let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.validate_shape().unwrap();
    }
    (header, markets)
}

struct Pred {
    header: MarketGroupV16HeaderAccount,
    markets: Vec<Market<u64>>,
    /// long on the prediction asset (index 1), the side that closes out
    pl: PortfolioAccountV16Account,
    /// short on the prediction asset (index 1), the side left holding dead stored basis
    ps: PortfolioAccountV16Account,
    /// long on asset 0 — an unrelated leg that must survive the whole wind-down
    ol: PortfolioAccountV16Account,
    /// short on asset 0 — ditto
    os: PortfolioAccountV16Account,
}

impl Pred {
    fn asset(&self, i: usize) -> AssetStateV16 {
        self.markets[i].engine.asset.try_to_runtime().unwrap()
    }
    fn validate(&mut self, label: &str) {
        let view = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        assert_eq!(view.validate_shape(), Ok(()), "{label}: validate_shape");
    }
}

/// Deposits + a matched book on BOTH assets, then `mark_asset_drain_only_not_atomic(1)`, then the
/// long owner's unilateral full close of the prediction leg. Ends in exactly the state the
/// memo's probe recorded at the wrapper's `ForfeitRecoveryLeg` call
/// (`verify/poc/F-04-L/option_ii_state_probe_at_forfeit.txt`):
/// `lifecycle=DrainOnly | oi_eff_long=0 | oi_eff_short=0 | stored_short=1`.
fn drive_prediction_to_the_dead_leg() -> Pred {
    let (header, markets) = prediction_fixture();
    let mut w = Pred {
        header,
        markets,
        pl: account_fixture(2, 21),
        ps: account_fixture(2, 22),
        ol: account_fixture(2, 23),
        os: account_fixture(2, 24),
    };

    // 1. deposits
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        for acct in [&mut w.pl, &mut w.ps, &mut w.ol, &mut w.os] {
            let mut v = PortfolioV16ViewMut::new(acct);
            m.deposit_not_atomic(&mut v, 400_000_000u128).unwrap();
        }
    }
    w.validate("1. after the deposits");

    // 2a. asset 0: an unrelated matched book that must still be open at the end.
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.ol);
        let mut short = PortfolioV16ViewMut::new(&mut w.os);
        m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(2 * POS_SCALE),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    }
    w.validate("2a. after the unrelated asset-0 trade");

    // 2b. asset 1: the prediction book.
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.pl);
        let mut short = PortfolioV16ViewMut::new(&mut w.ps);
        m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 1,
                size_q: signed_q(2 * POS_SCALE),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    }
    w.validate("2b. after the prediction trade");
    assert_eq!(w.asset(1).oi_eff_long_q, 2 * POS_SCALE);
    assert_eq!(w.asset(1).oi_eff_short_q, 2 * POS_SCALE);

    // 3. the prediction resolves: marketauth marks the slot drain-only (wrapper
    //    `UpdateAssetLifecycle { ASSET_ACTION_DRAIN_ONLY }`, marketauth-only).
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.mark_asset_drain_only_not_atomic(1).unwrap();
    }
    assert_eq!(w.asset(1).lifecycle, AssetLifecycleV16::DrainOnly);
    w.validate("3. after mark_asset_drain_only");

    // 4. the long owner closes out unilaterally (wrapper `RebalanceReduce`, owner-signed). The
    //    paired reducer takes the SHORT side's effective OI down with it, leaving the short's
    //    stored basis behind with zero effective exposure.
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.pl);
        m.rebalance_reduce_position_not_atomic(
            &mut long,
            RebalanceRequestV16 {
                asset_index: 1,
                reduce_q: 2 * POS_SCALE,
            },
        )
        .unwrap();
    }
    w.validate("4. after the long owner's unilateral full close");
    w
}

/// (a) THE FIX, POSITIVE DIRECTION. A lifecycle-`DrainOnly` asset with a zero `oi_eff` pair and a
/// dead stored basis on the counterparty side: the OWNER's forfeit succeeds, both sides end
/// cleared, the slot retires and re-activates, and the unrelated asset-0 legs are untouched.
///
/// Before the third arm this call was `Err(LockActive)` — measured as the revert control in
/// `verify/fixes/F-04-L.md` §MEASURE(4) and, at wrapper level, as the 231/21 vs 233/19 pair on
/// `percolator-prog origin/fix/W-19`.
#[test]
fn f04l_drainonly_zero_oi_owner_forfeit_clears_both_sides_and_the_slot_retires_and_reuses() {
    let mut w = drive_prediction_to_the_dead_leg();

    // ---- non-vacuity guard: we are in the state the new arm keys on, and nowhere else ----
    let before = w.asset(1);
    assert_eq!(
        before.lifecycle,
        AssetLifecycleV16::DrainOnly,
        "vacuous unless the asset lifecycle is DrainOnly: the other arms would admit"
    );
    assert_eq!(
        decode_mode(&w.header),
        MarketModeV16::Live,
        "vacuous unless the MARKET is Live: disjunct 1 would admit"
    );
    assert_eq!(
        before.oi_eff_long_q, 0,
        "vacuous unless the effective-OI pair is 0 == 0"
    );
    assert_eq!(
        before.oi_eff_short_q, 0,
        "vacuous unless the effective-OI pair is 0 == 0"
    );
    assert!(
        matches!(
            before.mode_short,
            SideModeV16::DrainOnly | SideModeV16::ResetPending
        ),
        "vacuous unless the forfeited SIDE is dead: mode_short = {:?}",
        before.mode_short
    );
    assert_eq!(
        before.stored_pos_count_short, 1,
        "vacuous unless a dead stored leg actually remains on the short side"
    );
    assert_eq!(
        before.stored_pos_count_long, 0,
        "the long owner's unilateral full close must have cleared its own leg"
    );
    let dead_leg = w.ps.legs[0].try_to_runtime().unwrap();
    assert!(dead_leg.active, "the short's stored leg is still active");
    assert_ne!(
        dead_leg.basis_pos_q, 0,
        "vacuous unless the stored leg still carries basis (dead stored basis, zero effective OI)"
    );
    // the unrelated asset-0 book, recorded before the forfeit
    let other_before = w.asset(0);
    assert_ne!(other_before.oi_eff_long_q, 0, "asset 0 must be live");
    assert_eq!(other_before.oi_eff_long_q, other_before.oi_eff_short_q);
    assert_eq!(other_before.stored_pos_count_long, 1);
    assert_eq!(other_before.stored_pos_count_short, 1);

    // ---- the call under test: the dead-leg OWNER's forfeit (wrapper tag 43) ----
    let outcome = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut short = PortfolioV16ViewMut::new(&mut w.ps);
        m.forfeit_recovery_leg_not_atomic(&mut short, 1, u128::MAX)
    };
    assert!(
        outcome.is_ok(),
        "the owner dead-leg forfeit MUST be exposed on a zero-exposure DrainOnly wind-down \
         (av spec.md:1621-1623; Toly's b4ff060e / 74c31b39 regressions): {outcome:?}"
    );

    // ---- the invariant the arm rests on: the pair did not move ----
    let after = w.asset(1);
    assert_eq!(
        (after.oi_eff_long_q, after.oi_eff_short_q),
        (0, 0),
        "the forfeit's only oi_eff writes are same-side checked_subs; from 0 == 0 the pair cannot move"
    );
    w.validate("after the admitted DrainOnly forfeit");

    // ---- both sides cleared ----
    assert_eq!(
        after.stored_pos_count_short, 0,
        "the forfeited leg must be gone from the short side"
    );
    assert_eq!(after.stored_pos_count_long, 0);
    assert!(
        !w.ps.legs[0].try_to_runtime().unwrap().active,
        "the exit did real work: the leg detached"
    );

    // ---- the two permissionless side resets close out the drain (wrapper `FinalizeResetSide`) ----
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.finalize_side_reset_not_atomic(1, SideV16::Long).unwrap();
        m.finalize_side_reset_not_atomic(1, SideV16::Short).unwrap();
    }
    assert_eq!(w.asset(1).mode_long, SideModeV16::Normal);
    assert_eq!(
        w.asset(1).mode_short,
        SideModeV16::Normal,
        "the side reset only finalizes because the forfeit emptied the short side"
    );
    w.validate("after the two permissionless side resets");

    // ---- the slot retires ... ----
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.retire_empty_asset_not_atomic(1, 5).unwrap();
    }
    assert_eq!(w.asset(1).lifecycle, AssetLifecycleV16::Retired);
    w.validate("after retire");

    // ---- ... and the slot is reusable for the next prediction ----
    let old_market_id = w.markets[1].engine.asset.market_id.get();
    w.header
        .activate_empty_asset_slot_not_atomic(1, &mut w.markets[1].engine, PRICE, 99)
        .unwrap();
    assert_ne!(
        w.markets[1].engine.asset.market_id.get(),
        old_market_id,
        "reactivation must assign a fresh monotonic market_id"
    );
    assert_eq!(w.asset(1).lifecycle, AssetLifecycleV16::Active);
    w.validate("after reactivation");

    // ---- and the other asset's legs never moved ----
    let other_after = w.asset(0);
    assert_eq!(other_after.oi_eff_long_q, other_before.oi_eff_long_q);
    assert_eq!(other_after.oi_eff_short_q, other_before.oi_eff_short_q);
    assert_eq!(other_after.stored_pos_count_long, 1);
    assert_eq!(other_after.stored_pos_count_short, 1);
    assert_eq!(other_after.lifecycle, AssetLifecycleV16::Active);
}

// =================================================================================================
// PART B — the three states the gate must STILL refuse.
// The driver is `tests/f04_regression.rs::drive_to_the_barrier` (the X-01 sequence), copied here
// so that suite stays byte-identical.
// =================================================================================================

/// `x01_market_fixture` (`tests/f04_regression.rs:159`).
fn x01_market_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.max_abs_funding_e9_per_slot = 10_000;
    cfg.max_price_move_bps_per_slot = 9_000;
    cfg.max_bankrupt_close_lifetime_slots = 100;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, PRICE, 1)
        .unwrap();
    {
        let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.validate_shape().unwrap();
    }
    (header, markets)
}

struct World {
    header: MarketGroupV16HeaderAccount,
    markets: Vec<Market<u64>>,
    l: PortfolioAccountV16Account,
    s1: PortfolioAccountV16Account,
    s2: PortfolioAccountV16Account,
    s3: PortfolioAccountV16Account,
}

impl World {
    fn asset(&self) -> AssetStateV16 {
        self.markets[0].engine.asset.try_to_runtime().unwrap()
    }
    fn validate(&mut self, label: &str) {
        let view = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        assert_eq!(view.validate_shape(), Ok(()), "{label}: validate_shape");
    }
}

/// Steps 1-5 of the X-01 sequence (`tests/f04_regression.rs:234`), barrier-off variant only:
/// it ends with `mode_long == DrainOnly` on a lifecycle-`Active`, `Live` asset whose effective-OI
/// pair is `HALF_Q == HALF_Q` — NON-zero, which is what parts (b) and (c) need.
fn drive_to_the_dead_side_mode() -> World {
    let (header, markets) = x01_market_fixture();
    let mut w = World {
        header,
        markets,
        l: account_fixture(1, 10),
        s1: account_fixture(1, 11),
        s2: account_fixture(1, 12),
        s3: account_fixture(1, 13),
    };

    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        for (acct, amount) in [
            (&mut w.l, 400_000_000u128),
            (&mut w.s1, 200_000_000),
            (&mut w.s2, 8_000_000),
            (&mut w.s3, 200_000_000),
        ] {
            let mut v = PortfolioV16ViewMut::new(acct);
            m.deposit_not_atomic(&mut v, amount).unwrap();
        }
    }

    for seed in [11u8, 12, 13] {
        let half_units: u128 = if seed == 11 { 22 } else { 1 };
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        let short_acct = match seed {
            11 => &mut w.s1,
            12 => &mut w.s2,
            _ => &mut w.s3,
        };
        let mut short = PortfolioV16ViewMut::new(short_acct);
        m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(half_units * HALF_Q),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    }
    assert_eq!(w.asset().oi_eff_long_q, 12 * POS_SCALE);

    // S1's unilateral full close scales a_long below MIN_A_SIDE -> mode_long = DrainOnly
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut s1 = PortfolioV16ViewMut::new(&mut w.s1);
        m.rebalance_reduce_position_not_atomic(
            &mut s1,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: 11 * POS_SCALE,
            },
        )
        .unwrap();
    }
    assert_eq!(
        w.asset().mode_long,
        SideModeV16::DrainOnly,
        "reduce_matching_open_interest_for_unilateral_close (:17781) must have set DrainOnly"
    );
    assert!(w.asset().a_long < MIN_A_SIDE && w.asset().a_long != 0);
    assert!(w.asset().a_long < ADL_ONE);

    // the mark runs away from the shorts, then the small short closes its leg in a trade
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.accrue_asset_to_not_atomic(0, 2, PRICE_1, 0, true)
            .unwrap();
    }
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.accrue_asset_to_not_atomic(0, 3, PRICE_2, 0, true)
            .unwrap();
        m.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(PRICE_2);
    }
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        let mut s2 = PortfolioV16ViewMut::new(&mut w.s2);
        m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut s2,
            TradeRequestV16 {
                asset_index: 0,
                size_q: -signed_q(HALF_Q),
                exec_price: PRICE_2,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    }
    w.validate("5. after the small short's terminal trade");
    assert_eq!(w.asset().oi_eff_long_q, HALF_Q);
    assert_eq!(w.asset().oi_eff_short_q, HALF_Q);
    w
}

/// (b) THE DISCRIMINATING NEGATIVE. Same lifecycle as (a) — `DrainOnly` — same dead side mode,
/// but the effective-OI pair is NOT zero: there is still a live counterparty leg on the asset, so
/// the forfeit would end the instruction with `oi_eff_long != oi_eff_short` on a Live market.
/// It must still be refused with `LockActive`. This is the conjunct that makes the new arm safe,
/// and (a)+(b) differ ONLY in the value of the pair.
#[test]
fn f04l_drainonly_with_live_oi_forfeit_is_still_refused() {
    let mut w = drive_to_the_dead_side_mode();
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.mark_asset_drain_only_not_atomic(0).unwrap();
    }

    // ---- non-vacuity guard ----
    let before = w.asset();
    assert_eq!(
        before.lifecycle,
        AssetLifecycleV16::DrainOnly,
        "vacuous unless the lifecycle is the one the new arm keys on"
    );
    assert_eq!(before.mode_long, SideModeV16::DrainOnly, "the SIDE is dead");
    assert_eq!(
        decode_mode(&w.header),
        MarketModeV16::Live,
        "vacuous unless the market is Live"
    );
    assert_ne!(
        before.oi_eff_long_q, 0,
        "vacuous unless the pair is NON-zero — that is the only difference from case (a)"
    );
    assert_eq!(
        before.oi_eff_long_q, before.oi_eff_short_q,
        "the book is matched before the call"
    );

    let result = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
    };
    assert_eq!(
        result.err(),
        Some(V16Error::LockActive),
        "a DrainOnly asset that still carries effective OI must NOT admit the terminal exit"
    );

    // fail-closed: nothing was written
    let after = w.asset();
    assert_eq!(after.oi_eff_long_q, before.oi_eff_long_q);
    assert_eq!(after.oi_eff_short_q, before.oi_eff_short_q);
    assert_eq!(after.stored_pos_count_long, before.stored_pos_count_long);
    assert_eq!(after.stored_pos_count_short, before.stored_pos_count_short);
    assert!(w.l.legs[0].try_to_runtime().unwrap().active);
    w.validate("after the REFUSED DrainOnly-with-live-OI forfeit");
}

/// (c) THE X-01 SHAPE, unchanged by F-04-L: a `DrainOnly` SIDE MODE latched by one unilateral
/// close on a lifecycle-`Active` asset. The side mode is not the asset lifecycle, and the new arm
/// keys on the LIFECYCLE, so this stays refused — F-04's guarantee.
#[test]
fn f04l_active_lifecycle_drainonly_side_mode_forfeit_is_still_refused() {
    let mut w = drive_to_the_dead_side_mode();

    // ---- non-vacuity guard ----
    let before = w.asset();
    assert_eq!(
        before.lifecycle,
        AssetLifecycleV16::Active,
        "vacuous unless the asset lifecycle is still Active"
    );
    assert_eq!(
        before.mode_long,
        SideModeV16::DrainOnly,
        "vacuous unless the SIDE mode is dead — otherwise the third disjunct is never reached"
    );
    assert_eq!(decode_mode(&w.header), MarketModeV16::Live);
    assert_ne!(before.oi_eff_long_q, 0, "the asset still carries OI");

    let result = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
    };
    assert_eq!(
        result.err(),
        Some(V16Error::LockActive),
        "X-01: a DrainOnly SIDE mode on an ACTIVE asset must never open the terminal exit"
    );
    let after = w.asset();
    assert_eq!(after.oi_eff_long_q, before.oi_eff_long_q);
    assert_eq!(after.oi_eff_short_q, before.oi_eff_short_q);
    assert!(w.l.legs[0].try_to_runtime().unwrap().active);
    w.validate("after the REFUSED X-01-shaped forfeit");
}

/// (d) C-04, unchanged: the owner exit on a lifecycle-`Recovery` asset admits through disjunct 2,
/// which F-04-L does not touch. Mirrors `tests/f04_regression.rs::f04_c04_recovery_lifecycle_owner_exit_still_works`.
#[test]
fn f04l_c04_recovery_lifecycle_owner_exit_still_works() {
    let mut w = drive_to_the_dead_side_mode();

    // ---- non-vacuity guard: refused while Active ----
    assert_eq!(w.asset().lifecycle, AssetLifecycleV16::Active);
    assert_eq!(w.asset().mode_long, SideModeV16::DrainOnly);
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        assert_eq!(
            m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
                .err(),
            Some(V16Error::LockActive),
            "Active asset: refused"
        );
    }

    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.force_asset_recovery_not_atomic(0, 4).unwrap();
    }
    assert_eq!(w.asset().lifecycle, AssetLifecycleV16::Recovery);
    assert_eq!(
        decode_mode(&w.header),
        MarketModeV16::Live,
        "market still Live, so disjunct 1 is not what admits"
    );

    let outcome = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
    };
    assert!(
        outcome.is_ok(),
        "a Recovery-lifecycle asset's dead leg MUST still be forfeitable by its owner: {outcome:?}"
    );
    assert!(
        !w.l.legs[0].try_to_runtime().unwrap().active
            || w.asset().pending_obligation_count_long != 0,
        "the exit did real work: the leg detached or became a pending obligation"
    );
}
