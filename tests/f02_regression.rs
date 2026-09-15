//! F-02 REGRESSION — the fixed behaviour, asserted.
//!
//! This is `verify/poc/F-02/poc_F02.rs` with the defect assertions inverted. Every
//! fixture, scenario and measurement helper is byte-identical to the PoC, so the two
//! files measure the same thing and disagree only about what the answer must be.
//!
//! Two halves have to hold, and the PR's one-line `min` only delivers the first:
//!   1. BOOKING  — the loss-bearing side is charged the FRESH residual (R - D), never
//!                 the figure captured when the close opened.
//!   2. LEDGER   — a mid-close principal settlement is credited to the open close
//!                 ledger, so `residual_remaining` falls, the close FINALIZES, and the
//!                 `pending_domain_loss_barrier_*` it holds is released. Without this
//!                 half, route 1c ends `residual_remaining = 100, finalized = false`
//!                 with the barrier raised forever, and `begin_close_progress_ledger`
//!                 (`:16955`) refuses every future bankruptcy close in that domain.
//!
//! Routes 2 and 3 stay DEFEATED: the `close_slot_available()` gate at
//! `begin_close_progress_ledger` (`:16955`) must still refuse a liquidation / recovery
//! forfeit that meets a pending ledger. Those two tests are copied verbatim — the fix
//! must not open them.

use percolator::{
    active_bitmap_is_empty, v16_domain_count_for_market_slots, AutoCrankPlanV16, AutoCrankWorkV16,
    CloseProgressLedgerV16, CloseProgressLedgerV16Account, EngineAssetSlotV16Account,
    LiquidationRequestV16, Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut,
    PortfolioAccountV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, SideV16, TradeRequestV16, V16Config, V16Error, V16PodU128,
    V16PodU64, POS_SCALE, SOCIAL_LOSS_DEN,
};

// ---------------------------------------------------------------------------
// fixture helpers — verbatim from tests/v16_spec_tests.rs
// ---------------------------------------------------------------------------

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn market_fixture(
    market_slots: u32,
    init_price: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let max_portfolio_assets =
        market_slots.min(percolator::V16_MAX_PORTFOLIO_ASSETS_N as u32) as u16;
    let cfg =
        V16Config::public_user_fund_with_market_slots(max_portfolio_assets, market_slots, 0, 10);
    let mut header =
        MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, market_slots, 0).unwrap();
    let mut markets = (0..market_slots)
        .map(|i| Market::new(i as u64, EngineAssetSlotV16Account::default()))
        .collect::<Vec<_>>();
    for i in 0..market_slots as usize {
        header
            .activate_empty_asset_slot_not_atomic(
                i as u32,
                &mut markets[i].engine,
                init_price,
                (i + 1) as u64,
            )
            .unwrap();
    }
    {
        let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.validate_shape().unwrap();
    }
    (header, markets)
}

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

fn signed_q(q: u128) -> i128 {
    i128::try_from(q).unwrap()
}

// ---------------------------------------------------------------------------
// shared scenario: a Live market carrying an account with an ACTIVE, non-finalized
// close ledger and `residual_remaining = R`, produced by the delta's new
// `begin_terminal_trade_residual_if_needed` (:18304). Copied from
// `v16_spec_tests::v16_trade_final_leg_residual_routes_through_close_without_forcing_market_recovery`.
// ---------------------------------------------------------------------------

const SIZE_Q: u128 = 10 * POS_SCALE;
/// `R` — the residual stamped on the ledger when the close begins.
const R: u128 = 250;

struct Scenario {
    header: MarketGroupV16HeaderAccount,
    markets: Vec<Market<u64>>,
    long_header: PortfolioAccountV16Account,
    short_header: PortfolioAccountV16Account,
}

/// Drives a Live market to the state the defect needs: `short` is flat, `capital = 0`,
/// `pnl = -R`, and carries an active close ledger with `residual_remaining = R`.
fn live_pending_close_scenario() -> Scenario {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 61);
    let mut short_header = account_fixture(1, 62);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 250).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(SIZE_Q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        for (offset, price) in (105u64..=150).step_by(5).enumerate() {
            let slot = 2 + offset as u64;
            market
                .set_asset_raw_oracle_target_not_atomic(0, price)
                .unwrap();
            market
                .accrue_asset_to_not_atomic(0, slot, price, 0, true)
                .unwrap();
        }
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: -signed_q(SIZE_Q),
                    exec_price: 150,
                    fee_bps: 0,
                },
                true,
            )
            .expect("risk-reducing final trade must remain available");

        // Preconditions of the defect, pinned.
        let pending = short.header.close_progress.try_to_runtime().unwrap();
        assert!(active_bitmap_is_empty(
            short.header.active_bitmap.map(V16PodU64::get)
        ));
        assert_eq!(short.header.capital.get(), 0);
        assert_eq!(short.header.pnl.get(), -(R as i128));
        assert!(pending.active && !pending.finalized && !pending.canceled);
        assert_eq!(pending.residual_remaining, R);
        assert_eq!(pending.gross_loss_at_close_start, R);
        assert_eq!(pending.asset_index, 0);
        assert_eq!(pending.domain_side, SideV16::Long);
        // The five progress categories are all zero, and `drift_consumed` — which has
        // no writer anywhere in the file — is zero too.
        assert_eq!(pending.support_consumed, 0);
        assert_eq!(pending.junior_face_burned, 0);
        assert_eq!(pending.insurance_spent, 0);
        assert_eq!(pending.b_loss_booked, 0);
        assert_eq!(pending.explicit_loss_assigned, 0);
        assert_eq!(pending.drift_consumed, 0);
    }

    Scenario {
        header,
        markets,
        long_header,
        short_header,
    }
}

/// The atoms actually charged to the loss-bearing side, recovered exactly from the
/// social-loss index move: `numerator = engine_chunk * SOCIAL_LOSS_DEN + rem_before`,
/// `delta_b = numerator / weight_sum`, `rem_after = numerator % weight_sum`
/// (`apply_bankruptcy_residual_chunk_to_loss_side`, `:17249`).
fn atoms_charged_to_long_side(
    before: &percolator::AssetStateV16,
    after: &percolator::AssetStateV16,
) -> u128 {
    let delta_b = after.b_long_num - before.b_long_num;
    let weight_sum = after.loss_weight_sum_long;
    let numerator = delta_b * weight_sum + after.social_loss_remainder_long_num;
    let charged = numerator - before.social_loss_remainder_long_num;
    assert_eq!(
        charged % SOCIAL_LOSS_DEN,
        0,
        "the b-index move must decode to a whole number of atoms"
    );
    charged / SOCIAL_LOSS_DEN
}

// ===========================================================================
// ROUTE 1 (FIXED) — owner deposit mid-close in Live, then resolve, then
//                   CloseResolved (wrapper tag 3 -> tag 39 -> tag 30).
// ===========================================================================

#[test]
fn route1_fixed_the_loss_side_is_charged_the_fresh_residual_and_the_close_finalizes() {
    const D: u128 = 100; // the mid-close deposit; 0 < D < R

    let Scenario {
        mut header,
        mut markets,
        mut long_header,
        mut short_header,
    } = live_pending_close_scenario();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.deposit_not_atomic(&mut short, D).unwrap();
    assert_eq!(short.header.capital.get(), D);
    assert_eq!(
        short
            .header
            .close_progress
            .try_to_runtime()
            .unwrap()
            .residual_remaining,
        R,
        "the deposit alone still writes nothing to the ledger — the credit happens \
         when principal actually settles"
    );

    market.resolve_market_not_atomic(11).unwrap();

    let asset_before = market.markets[0].engine.asset.try_to_runtime().unwrap();
    let vault_before = market.header.vault.get();
    market
        .close_resolved_account_not_atomic(&mut short, 0)
        .expect("the bankrupt account must close in Resolved mode");
    let asset_after = market.markets[0].engine.asset.try_to_runtime().unwrap();

    let true_residual = R - D; // 150
    let charged = atoms_charged_to_long_side(&asset_before, &asset_after);

    // ---- HALF 1: the booking is the FRESH residual ----
    assert_eq!(
        charged, true_residual,
        "F-02: the loss-bearing (long) side must be charged the fresh residual, not the \
         stale ledger figure R"
    );
    assert_eq!(short.header.pnl.get(), 0, "the debtor is credited in full");
    assert_eq!(
        charged, true_residual,
        "no asymmetry left: the loss side pays exactly what the debtor is forgiven"
    );

    // ---- HALF 2: the ledger settles and the close finalizes ----
    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(
        ledger.residual_remaining, 0,
        "F-02 (ledger half): the principal settlement must lower residual_remaining"
    );
    assert!(
        ledger.finalized,
        "F-02 (ledger half): the close must finalize once nothing is owed"
    );
    assert_eq!(
        ledger.gross_loss_at_close_start,
        R - D,
        "the gross the close is still absorbing is reduced by exactly the principal paid"
    );
    assert_eq!(
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get(),
        0,
        "the (asset 0, Long) domain-loss barrier must be released"
    );

    assert_eq!(
        short.header.capital.get(),
        0,
        "capital consumed by settlement"
    );
    assert_eq!(market.header.vault.get(), vault_before);

    println!(
        "ROUTE 1 FIXED: R={R} D={D} true_residual={true_residual} charged_to_long_side={charged} \
         residual_remaining={} finalized={} barrier={}",
        ledger.residual_remaining,
        ledger.finalized,
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get()
    );

    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

/// Control: with NO interleaved deposit the charge is still the full residual, so the
/// fix changes the interleaved case and nothing else.
#[test]
fn route1_control_without_the_mid_close_deposit_the_charge_equals_the_residual() {
    let Scenario {
        mut header,
        mut markets,
        long_header: _long_header,
        mut short_header,
    } = live_pending_close_scenario();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.resolve_market_not_atomic(11).unwrap();
    let asset_before = market.markets[0].engine.asset.try_to_runtime().unwrap();
    market
        .close_resolved_account_not_atomic(&mut short, 0)
        .unwrap();
    let asset_after = market.markets[0].engine.asset.try_to_runtime().unwrap();

    let charged = atoms_charged_to_long_side(&asset_before, &asset_after);
    assert_eq!(
        charged, R,
        "no interleaving: charge == ledger == true residual"
    );
    assert_eq!(short.header.pnl.get(), 0);
    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(ledger.residual_remaining, 0);
    assert!(ledger.finalized);
    println!("ROUTE 1 CONTROL (no deposit): charged_to_long_side={charged} true_residual={R}");
}

// ===========================================================================
// ROUTE 1b (FIXED) — the same interleaving entirely inside LIVE mode, through
//                    `advance_pending_close_residual_not_atomic` (:17428).
// ===========================================================================

#[test]
fn route1b_fixed_the_live_advancer_books_the_fresh_residual_and_finalizes() {
    const D: u128 = 100;

    let Scenario {
        mut header,
        mut markets,
        long_header: _long_header,
        mut short_header,
    } = live_pending_close_scenario();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.deposit_not_atomic(&mut short, D).unwrap();
    assert_eq!(market.header.mode, 0, "still LIVE — no resolve needed");

    let asset_before = market.markets[0].engine.asset.try_to_runtime().unwrap();
    let work = AutoCrankWorkV16 {
        now_slot: 11,
        observations: &[],
        resolved_close_fee_rate_per_slot: 0,
    };
    let booked = market
        .permissionless_auto_crank_not_atomic(&mut short, work)
        .expect("the pending close must still have a permissionless continuation");
    assert_eq!(booked.selected, AutoCrankPlanV16::AdvanceClose);
    let asset_after = market.markets[0].engine.asset.try_to_runtime().unwrap();

    let true_residual = R - D;
    let charged = atoms_charged_to_long_side(&asset_before, &asset_after);
    assert_eq!(
        charged, true_residual,
        "F-02: the Live advancer must book the fresh residual too"
    );
    assert_eq!(short.header.pnl.get(), 0, "the debtor is credited in full");

    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(ledger.residual_remaining, 0);
    assert!(ledger.finalized, "the Live close must finalize");
    assert_eq!(
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get(),
        0
    );

    println!(
        "ROUTE 1b FIXED (LIVE, AdvanceClose :17428): R={R} D={D} true_residual={true_residual} \
         charged_to_long_side={charged} residual_remaining={} finalized={}",
        ledger.residual_remaining, ledger.finalized
    );

    market.validate_shape().unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

// ===========================================================================
// ROUTE 1c (FIXED) — the brick. A chunk cap between |pnl| and the stale
//                    `residual_remaining` used to leave the ledger unfinalizable
//                    with the domain barrier raised forever. It must now finalize
//                    and a FRESH bankruptcy close in the same domain must open.
// ===========================================================================

#[test]
fn route1c_fixed_a_capped_chunk_no_longer_bricks_the_close_or_holds_the_barrier() {
    const D: u128 = 100; // true residual after settlement = 150
    const CHUNK_CAP: u128 = 200; // |pnl| (150) < cap (200) < stale residual (250)

    let Scenario {
        mut header,
        mut markets,
        long_header: _long_header,
        mut short_header,
    } = live_pending_close_scenario();
    header.config.public_b_chunk_atoms = V16PodU128::new(CHUNK_CAP);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.deposit_not_atomic(&mut short, D).unwrap();
    market.resolve_market_not_atomic(11).unwrap();
    let outcome = market
        .close_resolved_account_not_atomic(&mut short, 0)
        .expect("the capped chunk still books");

    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    println!(
        "ROUTE 1c FIXED: outcome={outcome:?} pnl={} b_loss_booked={} residual_remaining={} \
         finalized={} barrier={}",
        short.header.pnl.get(),
        ledger.b_loss_booked,
        ledger.residual_remaining,
        ledger.finalized,
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get()
    );
    assert_eq!(short.header.pnl.get(), 0, "the debtor is credited in full");
    assert_eq!(
        ledger.b_loss_booked,
        R - D,
        "the loss side pays the fresh residual, which is under the cap"
    );
    assert_eq!(
        ledger.residual_remaining, 0,
        "F-02 (ledger half): the ledger must not be left claiming a residual nobody owes"
    );
    assert!(
        ledger.finalized,
        "F-02 (ledger half): the close must finalize"
    );
    assert_eq!(
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get(),
        0,
        "F-02 (ledger half): the (asset 0, Long) domain-loss barrier must be released"
    );

    // The liveness consequence, asserted directly: a fresh bankruptcy close in the
    // same (asset 0, Long) domain must be able to OPEN. Under the brick the ledger
    // stayed `active && !finalized`, so `close_slot_available()` (:5623) was false and
    // `begin_close_progress_ledger` (:16955) refused with LockActive forever.
    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    assert!(
        ledger.active && ledger.finalized && !ledger.canceled && ledger.residual_remaining == 0,
        "the ledger must be finalized-inert, which is exactly what close_slot_available() \
         (:5623) accepts, so begin_close_progress_ledger (:16955) can open the next close"
    );
}

/// active, non-finalized close ledger on `(asset 0, Long)` from an earlier transaction.
/// The stamped fixture is a legal state — `validate_shape` and `validate_with_market`
/// are asserted below — so the refusal proves something about the close path, not the
/// fixture.
fn bankrupt_with_live_leg(
    stamp_pending_ledger: bool,
) -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
    PortfolioAccountV16Account,
) {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 81);
    let mut short_header = account_fixture(1, 82);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 2_000).unwrap();
        market.deposit_not_atomic(&mut short, 250).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(SIZE_Q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        for (offset, price) in (105u64..=140).step_by(5).enumerate() {
            let slot = 2 + offset as u64;
            market
                .set_asset_raw_oracle_target_not_atomic(0, price)
                .unwrap();
            market
                .accrue_asset_to_not_atomic(0, slot, price, 0, true)
                .unwrap();
        }
    }
    if stamp_pending_ledger {
        let market_id = markets[0].engine.asset.market_id.get();
        short_header.close_progress =
            CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
                active: true,
                finalized: false,
                canceled: false,
                close_id: 1,
                asset_index: 0,
                market_id,
                domain_side: SideV16::Long,
                gross_loss_at_close_start: R,
                drift_reference_slot: 0,
                max_close_slot: u64::MAX,
                residual_remaining: R,
                ..CloseProgressLedgerV16::EMPTY
            });
        // The barrier the real `begin_close_progress_ledger` would have taken, and the
        // market-level blocker total that mirrors it (`slot_resolved_payout_blockers_v16`).
        markets[0].engine.pending_domain_loss_barrier_long = V16PodU64::new(1);
        header.resolved_payout_blocker_count =
            V16PodU64::new(header.resolved_payout_blocker_count.get() + 1);
    }
    (header, markets, long_header, short_header)
}

#[test]
fn route2_liquidation_meeting_a_pending_ledger_is_refused_at_begin_close_progress_ledger() {
    let (mut header, mut markets, _long_header, mut short_header) = bankrupt_with_live_leg(true);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    // The constructed state is legal.
    market.validate_shape().expect("market shape must be valid");
    short
        .validate_with_market(&market.as_view())
        .expect("account carrying a pending close ledger must be valid");

    // tag 3 — the interleaved deposit the route needs (deposit is Live-only, and Live
    // is exactly where we are; it has no `close_progress` gate).
    market
        .deposit_not_atomic(&mut short, 100)
        .expect("Live deposit into an account with an active close ledger is accepted");
    let before = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(before.residual_remaining, R);

    // tag 5 action 1 — the second liquidation.
    let err = market
        .liquidate_account_not_atomic(&mut short, LiquidationRequestV16 { asset_index: 0 })
        .expect_err("route 2 must not reach the stale booking");
    println!("ROUTE 2 (DEFEATED): liquidate_account_not_atomic -> {err:?}");
    assert_eq!(
        err,
        V16Error::LockActive,
        "refused by begin_close_progress_ledger (:16955) on !close_slot_available()"
    );

    // Nothing was booked: the stale figure never reached :17386.
    let after = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(after.residual_remaining, R);
    assert_eq!(after.b_loss_booked, 0);
    assert_eq!(after.explicit_loss_assigned, 0);
}

/// POSITIVE CONTROL for route 2: the identical liquidation, without the pending ledger,
/// succeeds and books — so the refusal above is caused by the pending ledger and not by
/// an unrelated defect in the fixture.
#[test]
fn route2_positive_control_the_same_liquidation_books_when_no_close_is_open() {
    let (mut header, mut markets, _long_header, mut short_header) = bankrupt_with_live_leg(false);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.deposit_not_atomic(&mut short, 100).unwrap();
    let outcome = market
        .liquidate_account_not_atomic(&mut short, LiquidationRequestV16 { asset_index: 0 })
        .expect("the same liquidation must succeed with no close open");
    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    println!(
        "ROUTE 2 POSITIVE CONTROL: residual_booked={} explicit_loss={} \
         gross_loss_at_close_start={} residual_remaining={}",
        outcome.residual_booked,
        outcome.explicit_loss,
        ledger.gross_loss_at_close_start,
        ledger.residual_remaining
    );
    assert!(
        outcome.residual_booked + outcome.explicit_loss > 0,
        "the control must actually reach the booking site"
    );
    // And what it booked is the FRESH residual it stamped in this same call — the
    // ledger cannot be stale when the caller opened it microseconds earlier.
    assert_eq!(
        ledger.b_loss_booked + ledger.explicit_loss_assigned,
        ledger.gross_loss_at_close_start - ledger.insurance_spent
    );
}

// ===========================================================================
// ROUTE 3 (BEHAVIOUR CHANGE, intended) — `forfeit_recovery_leg_not_atomic`
//           (:21554, wrapper tag 43, Recovery mode) meeting a pending ledger.
//
// At `2c38570a` this was DEFEATED: `begin_close_progress_ledger` (`:16955`)
// refused with LockActive because the stale ledger was still `active &&
// !finalized`, so the forfeit could never complete and the account was stuck.
//
// The ledger half of the F-02 fix changes that, and this is the intended
// consequence, not a widened attack surface: the forfeit settles 350 of
// principal FIRST, which fully extinguishes the ledger's 250 of outstanding
// residual. The ledger becomes finalized-inert, which is exactly the state
// `close_slot_available()` (`:5623`, `is_finalized_inert()`) exists to accept,
// so the next close may begin and the forfeit books the genuinely remaining 50.
//
// The `:16955` lock itself is UNCHANGED and still bites whenever the ledger is
// genuinely pending — route 2 above proves that with the identical fixture and a
// principal payment (100) smaller than the outstanding residual (250).
// ===========================================================================

#[test]
fn route3_recovery_forfeit_completes_once_principal_extinguishes_the_pending_ledger() {
    let (mut header, mut markets, _long_header, mut short_header) = bankrupt_with_live_leg(true);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.validate_shape().unwrap();
    short.validate_with_market(&market.as_view()).unwrap();

    // The interleaved settlement must happen while the market is still Live — deposit
    // is Live-only (`:20841`), which is itself part of why route 3 is narrow.
    market.deposit_not_atomic(&mut short, 100).unwrap();
    market
        .force_asset_recovery_not_atomic(0, market.header.current_slot.get())
        .unwrap();

    let outcome = market
        .forfeit_recovery_leg_not_atomic(&mut short, 0, u128::MAX)
        .expect("the forfeit must complete once principal has extinguished the old ledger");
    let after = short.header.close_progress.try_to_runtime().unwrap();
    println!(
        "ROUTE 3 FIXED: {outcome:?} | residual_remaining={} finalized={} barrier={}",
        after.residual_remaining,
        after.finalized,
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get()
    );

    // Conservation: every atom of the forfeited loss is accounted for.
    assert_eq!(
        outcome.loss_settled,
        outcome.principal_used
            + outcome.insurance_used
            + outcome.support_consumed
            + outcome.junior_face_burned
            + outcome.residual_booked
            + outcome.explicit_loss,
        "the forfeited loss must be exactly partitioned"
    );
    // The principal payment was >= the old ledger's outstanding residual, so it
    // retired that ledger; what the new close booked is the FRESH remainder, not the
    // stale R.
    assert!(
        outcome.principal_used >= R,
        "this fixture's principal ({}) must cover the stamped residual ({R}) — otherwise \
         the ledger stays pending and :16955 refuses, as route 2 shows",
        outcome.principal_used
    );
    assert!(
        outcome.residual_booked + outcome.explicit_loss < R,
        "the booking must be the fresh remainder, never the stale ledger figure R"
    );
    assert_eq!(
        after.residual_remaining, 0,
        "the new close finishes in the same call"
    );
    assert!(after.finalized);

    market.validate_shape().unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

/// POSITIVE CONTROL for route 3.
#[test]
fn route3_positive_control_the_same_forfeit_books_when_no_close_is_open() {
    let (mut header, mut markets, _long_header, mut short_header) = bankrupt_with_live_leg(false);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    market.deposit_not_atomic(&mut short, 100).unwrap();
    market
        .force_asset_recovery_not_atomic(0, market.header.current_slot.get())
        .unwrap();
    let outcome = market
        .forfeit_recovery_leg_not_atomic(&mut short, 0, u128::MAX)
        .expect("the same forfeit must succeed with no close open");
    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    println!(
        "ROUTE 3 POSITIVE CONTROL: residual_booked={} explicit_loss={} \
         gross_loss_at_close_start={} residual_remaining={}",
        outcome.residual_booked,
        outcome.explicit_loss,
        ledger.gross_loss_at_close_start,
        ledger.residual_remaining
    );
}
