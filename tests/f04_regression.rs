//! F-04 regression suite — `forfeit_recovery_leg_not_atomic` must not open the terminal
//! dead-leg exit on an asset that is still trading.
//!
//! Register rows X-01 + X-02 (verified ARM High, `verify/items/X-01.md`, `verify/items/X-02.md`).
//! Before the fix, `leg_is_dead_for_forfeit` admitted a leg on the SIDE MODE alone
//! (`2c38570a:src/v16.rs:21134-21145`, disjunct `:21140-21143` ≡ `av:19767-19778` / `av:19773-19776`).
//! `reduce_matching_open_interest_for_unilateral_close` (`:17565-17567` long / `:17572-17574` short)
//! latches `mode_<side> = DrainOnly` on a single unilateral close that drives the opposite side's
//! `A` factor under `MIN_A_SIDE`, and it touches no lifecycle — so one owner-signed reduce opened
//! the terminal exit on a Live/Active asset. Both exits of the forfeit then removed one side's
//! `oi_eff` with no paired opposite-side write:
//!
//!   * the RETENTION exit (`:21586-21587` → `retain_leg_as_pending_obligation` `:16599` →
//!     `kernel_retain_leg_as_pending_obligation` `:1210`), taken when a pending-domain-loss barrier
//!     is standing — this is X-01;
//!   * the CLEAN-DETACH exit (`:21440` / `:21589` `clear_leg`) — this is X-02 / AS-02.
//!
//! Either way the instruction ENDED with `mode == Live`, `lifecycle == Active` and
//! `oi_eff_long_q != oi_eff_short_q`, which `av:spec.md:952` forbids ("if Live:
//! OI_eff_long == OI_eff_short", stated for every Active/DrainOnly/Recovery asset side) and which
//! `spec.md:1239` (§8.1 step 9) requires to be asserted at instruction end. Every surviving
//! counterparty then read `unilateral_close_capacity = min(.., 0, ..) = 0` (`:919-925` → `:17490`)
//! and could neither reduce (`NonProgress`) nor be liquidated, and
//! `accrual_activity_for_asset_segment`'s `balanced_exposure` (`:2497`) switched funding off for
//! everyone on the asset.
//!
//! THE FIX (`leg_is_dead_for_forfeit`): the side-mode disjunct is gated on the ASSET LIFECYCLE, so
//! the dead-leg exit only opens on the terminal lifecycles the spec names — requirement 30
//! (`av spec.md:65`, "for terminal/recovery assets") and `av spec.md:1580`
//! ("terminal/recovery/dead assets").
//!
//! THIS FILE ASSERTS THE FIXED BEHAVIOUR. It is the PoC bodies of `verify/poc/X-01/poc_X01.rs`,
//! `verify/poc/X-02/poc_X-02.rs` and `verify/poc/AS-02/poc_AS-02.rs` re-asserted the other way
//! round: the forfeit is refused with `LockActive`, the book stays matched, `validate_shape()` is
//! `Ok(())` at every instruction end under BOTH feature sets, the surviving counterparty keeps
//! every exit, funding keeps running — and the legitimate Recovery-lifecycle owner exit that C-04
//! relies on still works.
//!
//! Run:
//!   cargo test --test f04_regression
//!   cargo test --features audit-scan --test f04_regression

use percolator::{
    v16_domain_count_for_market_slots, AssetLifecycleV16, AssetStateV16, AutoCrankWorkV16,
    EngineAssetSlotV16Account, LiquidationRequestV16, Market, MarketGroupV16HeaderAccount,
    MarketGroupV16ViewMut, MarketModeV16, PortfolioAccountV16Account, PortfolioV16ViewMut,
    ProvenanceHeaderV16, ProvenanceHeaderV16Account, RebalanceRequestV16, SideModeV16, SideV16,
    TradeRequestV16, V16Config, V16Error, V16PodU64,
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

/// `account_fixture` from `tests/v16_spec_tests.rs:118-130`.
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

/// `market_fixture` as used by the X-02 / AS-02 PoCs.
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
    for (i, slot) in markets.iter_mut().enumerate() {
        header
            .activate_empty_asset_slot_not_atomic(
                i as u32,
                &mut slot.engine,
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

/// Same, with funding switched on (X-02 T5's fixture).
fn market_fixture_with_funding(
    market_slots: u32,
    init_price: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let max_portfolio_assets =
        market_slots.min(percolator::V16_MAX_PORTFOLIO_ASSETS_N as u32) as u16;
    let mut cfg =
        V16Config::public_user_fund_with_market_slots(max_portfolio_assets, market_slots, 0, 10);
    cfg.max_abs_funding_e9_per_slot = 10_000;
    cfg.max_price_move_bps_per_slot = 1_000;
    let mut header =
        MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, market_slots, 0).unwrap();
    let mut markets = (0..market_slots)
        .map(|i| Market::new(i as u64, EngineAssetSlotV16Account::default()))
        .collect::<Vec<_>>();
    for (i, slot) in markets.iter_mut().enumerate() {
        header
            .activate_empty_asset_slot_not_atomic(
                i as u32,
                &mut slot.engine,
                init_price,
                (i + 1) as u64,
            )
            .unwrap();
    }
    (header, markets)
}

/// `decode_market_mode` (`2c38570a:src/v16.rs:22883-22890`) — NOTE the PoC helper this replaces
/// had `1 => Recovery, 2 => Resolved` transposed (X-01 verifier §9 defect 1).
fn decode_mode(header: &MarketGroupV16HeaderAccount) -> MarketModeV16 {
    match header.mode {
        0 => MarketModeV16::Live,
        1 => MarketModeV16::Resolved,
        2 => MarketModeV16::Recovery,
        other => panic!("unknown market mode byte {other}"),
    }
}

// =================================================================================================
// PART A — the X-01 route: the barrier retention exit.
// Fixture and step sequence copied from `verify/poc/X-01/poc_X01.rs`; only the verdict changes.
// =================================================================================================

/// `funding_market_fixture` (`tests/v16_spec_tests.rs:65-79`) + `max_bankrupt_close_lifetime_slots
/// = 100`, so the close ledger opened in step 5 has not expired by step 6.
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
    fn barrier_long(&self) -> u64 {
        self.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get()
    }
    fn barrier_short(&self) -> u64 {
        self.markets[0]
            .engine
            .pending_domain_loss_barrier_short
            .get()
    }

    /// THE PROBE, applied at the end of EVERY instruction — including, now, the forfeit itself.
    /// Under `--features audit-scan` the `validate_shape()` conjunct IS the audit scan
    /// (`:8501-8503`), so a green run under that feature set is the matched-book invariant
    /// certified at every instruction end.
    fn assert_matched_book_at_instruction_end(&mut self, label: &str) {
        let asset = self.asset();
        assert_eq!(
            asset.lifecycle,
            AssetLifecycleV16::Active,
            "{label}: the asset must still be Active or the probe is empty (:8502 exempts Recovery)"
        );
        assert_eq!(
            decode_mode(&self.header),
            MarketModeV16::Live,
            "{label}: the market must still be Live or the probe is empty (:8501)"
        );
        assert_eq!(
            asset.oi_eff_long_q, asset.oi_eff_short_q,
            "{label}: instruction ended with an unmatched book"
        );
        let view = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        assert_eq!(
            view.validate_shape(),
            Ok(()),
            "{label}: validate_shape rejected a state produced by public entries"
        );
    }
}

/// Steps 1-5 of the X-01 sequence, verbatim. `bankrupt_s2 == false` is the barrier-off variant,
/// which selects the CLEAN-DETACH exit of the forfeit instead of the retention.
fn drive_to_the_barrier(bankrupt_s2: bool) -> World {
    let (header, markets) = x01_market_fixture();
    let mut w = World {
        header,
        markets,
        l: account_fixture(1, 10),
        s1: account_fixture(1, 11),
        s2: account_fixture(1, 12),
        s3: account_fixture(1, 13),
    };

    let s2_deposit: u128 = if bankrupt_s2 { 520_000 } else { 8_000_000 };

    // 1. deposits
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        for (acct, amount) in [
            (&mut w.l, 400_000_000u128),
            (&mut w.s1, 200_000_000),
            (&mut w.s2, s2_deposit),
            (&mut w.s3, 200_000_000),
        ] {
            let mut v = PortfolioV16ViewMut::new(acct);
            m.deposit_not_atomic(&mut v, amount).unwrap();
        }
    }
    w.assert_matched_book_at_instruction_end("1. after the four deposits");

    // 2. open a matched book: L long 12, S1 short 11, S2 short 1/2, S3 short 1/2
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
        w.assert_matched_book_at_instruction_end("2. after an opening trade");
    }
    assert_ne!(w.asset().oi_eff_long_q, 0);
    assert_eq!(w.asset().oi_eff_long_q, 12 * POS_SCALE);
    assert_eq!(w.asset().mode_long, SideModeV16::Normal);

    // 3. S1's unilateral full close scales a_long below MIN_A_SIDE -> mode_long = DrainOnly
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
    w.assert_matched_book_at_instruction_end("3. after S1's unilateral full close");
    // THE CRACK the fix closes: a DrainOnly SIDE MODE on an ACTIVE asset lifecycle.
    assert_eq!(
        w.asset().mode_long,
        SideModeV16::DrainOnly,
        "reduce_matching_open_interest_for_unilateral_close (:17566) must have set DrainOnly"
    );
    assert!(w.asset().a_long < MIN_A_SIDE && w.asset().a_long != 0);
    assert!(w.asset().a_long < ADL_ONE);
    assert_eq!(
        w.asset().lifecycle,
        AssetLifecycleV16::Active,
        "the side mode is NOT the asset lifecycle — this is the state the gate must refuse"
    );

    // 4. the mark runs away from the shorts
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.accrue_asset_to_not_atomic(0, 2, PRICE_1, 0, true)
            .unwrap();
    }
    w.assert_matched_book_at_instruction_end("4a. after the first accrual");
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.accrue_asset_to_not_atomic(0, 3, PRICE_2, 0, true)
            .unwrap();
        m.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(PRICE_2);
    }
    w.assert_matched_book_at_instruction_end("4b. after the second accrual");

    // 5. the bankrupt short closes its only leg in a trade: the barrier goes up
    assert_eq!(w.barrier_long(), 0, "no barrier before step 5");
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
    w.assert_matched_book_at_instruction_end("5. after the bankrupt short's terminal trade");
    assert_eq!(
        w.barrier_long(),
        u64::from(bankrupt_s2),
        "begin_terminal_trade_residual_if_needed (:18329) raises the LONG barrier iff S2 is bankrupt"
    );
    assert_eq!(w.barrier_short(), 0);
    assert_eq!(w.asset().oi_eff_long_q, HALF_Q);
    assert_eq!(w.asset().oi_eff_short_q, HALF_Q);
    w
}

/// A1 — THE X-01 DEFECT ASSERTION, INVERTED. Before the fix this forfeit returned
/// `Ok(DeadLegForfeitOutcomeV16 { detached: false, .. })` and left `0 / 500_000` on an Active
/// asset in a Live market (`poc_X01.rs:313`, measured `verify/poc/X-01/01_cand_default_features.txt`).
/// It must now be refused, and refused BEFORE any state is written — `leg_is_dead_for_forfeit`
/// is read at the top of `forfeit_recovery_leg_not_atomic`, so this is a fail-closed refusal, not
/// a `not_atomic` partial mutation.
#[test]
fn f04_x01_barrier_retention_forfeit_on_an_active_asset_is_refused() {
    let mut w = drive_to_the_barrier(true);
    let before = w.asset();
    assert_ne!(
        before.oi_eff_long_q, 0,
        "vacuous unless the side carries OI"
    );
    assert_eq!(
        w.barrier_long(),
        1,
        "the retention exit is the one selected here"
    );

    let result = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
    };
    assert_eq!(
        result.err(),
        Some(V16Error::LockActive),
        "leg_is_dead_for_forfeit must not admit a DrainOnly SIDE on an Active ASSET"
    );

    // Nothing was written: the kernel at :1210 never ran.
    let after = w.asset();
    assert_eq!(after.oi_eff_long_q, before.oi_eff_long_q);
    assert_eq!(after.oi_eff_short_q, before.oi_eff_short_q);
    assert_eq!(
        after.pending_obligation_count_long, before.pending_obligation_count_long,
        ":1230 (the kernel's only writer of this counter) did not run"
    );
    assert_eq!(after.loss_weight_sum_long, before.loss_weight_sum_long);
    let leg = w.l.legs[0].try_to_runtime().unwrap();
    assert!(leg.active);
    assert_eq!(leg.side, SideV16::Long);
    assert_ne!(leg.basis_pos_q, 0, ":1245 did not zero the basis");

    // THE END STATE the defect produced is now unreachable by this route.
    w.assert_matched_book_at_instruction_end("6. after the REFUSED forfeit");
    assert_eq!(after.lifecycle, AssetLifecycleV16::Active);
    assert_eq!(decode_mode(&w.header), MarketModeV16::Live);
    assert_eq!(
        w.barrier_long(),
        1,
        "the barrier is untouched by the refusal"
    );
}

/// A2 — LIVENESS. The surviving short keeps its exits. Before the fix, `rebalance_reduce` and
/// `liquidate` both returned `NonProgress` for S3 forever, because
/// `unilateral_close_capacity = min(account_effective, oi_eff_long = 0, oi_eff_short)` was 0
/// (`poc_X01.rs:437`). Now the only refusal is the barrier's designed, TEMPORARY `LockActive`,
/// and it lifts: one PERMISSIONLESS crank settles the close ledger, and S3 reduces.
#[test]
fn f04_x01_the_surviving_short_keeps_every_exit() {
    // CONTROL HALF — while the barrier stands, the refusal S3 gets is the BARRIER'S own
    // `LockActive` (`:17831`), the designed temporary block, and not the permanent `NonProgress`
    // the zeroed book used to produce (`poc_X01.rs:437`, `verify/poc/X-01/01_cand_default_features.txt`).
    // Its own World, because `rebalance_reduce_position_not_atomic` is `_not_atomic`: a refused
    // call still leaves the caller's view partially mutated (`reduce_position :17604-17606`).
    {
        let mut w = drive_to_the_barrier(true);
        {
            let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut long = PortfolioV16ViewMut::new(&mut w.l);
            assert_eq!(
                m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
                    .err(),
                Some(V16Error::LockActive)
            );
        }
        assert_eq!(w.asset().oi_eff_long_q, HALF_Q);
        assert_eq!(w.asset().oi_eff_short_q, HALF_Q);
        let blocked = {
            let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut s3 = PortfolioV16ViewMut::new(&mut w.s3);
            m.rebalance_reduce_position_not_atomic(
                &mut s3,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: HALF_Q,
                },
            )
        };
        assert_eq!(
            blocked.err(),
            Some(V16Error::LockActive),
            "the barrier's designed TEMPORARY block, not a permanent NonProgress"
        );
    }

    // LIVENESS HALF — and the block lifts. One PERMISSIONLESS crank settles the close ledger and
    // drops the barrier, then the third party recertifies and closes its whole position.
    let mut w = drive_to_the_barrier(true);
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        assert_eq!(
            m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
                .err(),
            Some(V16Error::LockActive)
        );
    }
    let crank_out = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut s2 = PortfolioV16ViewMut::new(&mut w.s2);
        m.permissionless_auto_crank_not_atomic(
            &mut s2,
            AutoCrankWorkV16 {
                now_slot: 4,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
    };
    assert!(
        crank_out.is_ok(),
        "the close ledger is permissionlessly advanceable: {crank_out:?}"
    );
    assert_eq!(
        w.barrier_long(),
        0,
        "a permissionless crank released the barrier"
    );

    // S3 has not been touched since the two accruals, so it recertifies first — an ordinary
    // owner-signed step.
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut s3 = PortfolioV16ViewMut::new(&mut w.s3);
        let cert = m
            .full_account_refresh_not_atomic(&mut s3)
            .expect("the surviving short can recertify");
        assert_eq!(
            cert.certified_liq_deficit, 0,
            "S3 is healthy — it was only ever locked by the defect"
        );
    }

    let reduced = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut s3 = PortfolioV16ViewMut::new(&mut w.s3);
        m.rebalance_reduce_position_not_atomic(
            &mut s3,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: HALF_Q,
            },
        )
    };
    assert!(
        reduced.is_ok(),
        "the surviving short must still be able to reduce: {reduced:?}"
    );
    assert_eq!(
        reduced.unwrap().reduced_q,
        HALF_Q,
        "S3 closes its whole position — the permanent NonProgress lock is gone"
    );
    // The asset ends empty and MATCHED, which the defect made unreachable
    // (`begin_side_reset_if_effective_oi_exhausted` `:17504-17528` needs both a zero pending
    // obligation count and no barrier; the retention set the first while holding the second).
    assert_eq!(w.asset().oi_eff_long_q, 0);
    assert_eq!(w.asset().oi_eff_short_q, 0);
    let view = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
    assert_eq!(view.validate_shape(), Ok(()));
}

/// A3 — the CLEAN-DETACH exit (no barrier) is gated by the SAME predicate, so it is refused too.
/// Before the fix this returned `Ok(detached: true)` and still ended `0 / 500_000`
/// (`poc_X01.rs:520`; X-01 verifier §6: "the barrier retention is sufficient but not necessary").
#[test]
fn f04_x01_barrier_off_clean_detach_exit_is_refused_too() {
    let mut w = drive_to_the_barrier(false);
    assert_eq!(w.barrier_long(), 0);
    let before = w.asset();

    let result = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
    };
    assert_eq!(
        result.err(),
        Some(V16Error::LockActive),
        "both exits of forfeit_recovery_leg_not_atomic go through leg_is_dead_for_forfeit"
    );
    let after = w.asset();
    assert_eq!(after.oi_eff_long_q, before.oi_eff_long_q);
    assert_eq!(after.oi_eff_short_q, before.oi_eff_short_q);
    assert_ne!(after.loss_weight_sum_long, 0, "clear_leg did not run");
    assert!(w.l.legs[0].try_to_runtime().unwrap().active);
    w.assert_matched_book_at_instruction_end("after the REFUSED clean-detach forfeit");
}

/// A4 — fixture control, unchanged from the PoC: the state one instruction before the forfeit is
/// accepted under both feature sets, so nothing in the fixture is what the audit build objects to.
#[test]
fn f04_x01_state_before_the_forfeit_is_accepted_under_both_feature_sets() {
    let mut w = drive_to_the_barrier(true);
    assert_eq!(w.asset().oi_eff_long_q, w.asset().oi_eff_short_q);
    assert_eq!(w.asset().lifecycle, AssetLifecycleV16::Active);
    assert_eq!(w.asset().mode_long, SideModeV16::DrainOnly);
    assert_eq!(w.barrier_long(), 1, "the barrier alone is legal");
    let view = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
    assert_eq!(view.validate_shape(), Ok(()));
}

// =================================================================================================
// PART B — the X-02 route: an INNOCENT THIRD PARTY holds the surviving side.
// Sequence copied from `verify/poc/X-02/poc_X-02.rs` `build_asymmetry` / T1.
//   A = attacker portfolio #1 (long, then rebalance-reduces)
//   B = attacker portfolio #2 (short, then forfeits)
//   C = innocent third party, long, never acts adversarially
// =================================================================================================

/// B1 — the three-call sequence is refused at call 3, and C keeps a matched book.
/// Before the fix: `X02|3_forfeit|…|oil=20000|ois=0` with `validate_shape=Ok(())`,
/// `stored_l=1` (C's leg alone) and `stored_s=0` (`verify/poc/X-02/out_x02_cand.txt`).
#[test]
fn f04_x02_third_party_is_never_left_holding_a_one_sided_book() {
    let (mut header, mut markets) = market_fixture(1, PRICE);
    let (mut aa, mut bb, mut cc) = (
        account_fixture(1, 11),
        account_fixture(1, 12),
        account_fixture(1, 13),
    );
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut aa);
    let mut b = PortfolioV16ViewMut::new(&mut bb);
    let mut c = PortfolioV16ViewMut::new(&mut cc);

    market.deposit_not_atomic(&mut a, 500_000_000).unwrap();
    market.deposit_not_atomic(&mut b, 500_000_000).unwrap();
    market.deposit_not_atomic(&mut c, 500_000_000).unwrap();

    // (0) the innocent third party opens FIRST — C long vs B short.
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut c,
            &mut b,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(20_000),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    assert_eq!(market.validate_shape(), Ok(()));

    // (1) the attacker self-matches: A long vs B short.
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut a,
            &mut b,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(447_912),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    assert_eq!(market.validate_shape(), Ok(()));

    // (2) owner-signed unilateral reduce of A's OWN long leg (wrapper tag 44): a_short falls
    //     under MIN_A_SIDE and mode_short latches DrainOnly, with the LIFECYCLE still Active.
    market
        .rebalance_reduce_position_not_atomic(
            &mut a,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: 447_912,
            },
        )
        .unwrap();
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert!(
        asset.a_short < MIN_A_SIDE,
        "a_short must fall under MIN_A_SIDE"
    );
    assert_eq!(asset.mode_short, SideModeV16::DrainOnly);
    assert_eq!(asset.lifecycle, AssetLifecycleV16::Active);
    assert_eq!(asset.oi_eff_long_q, asset.oi_eff_short_q);
    assert_eq!(market.validate_shape(), Ok(()));

    // (3) owner-signed forfeit of B's OWN now-"dead" short leg (wrapper tag 43) — REFUSED.
    let forfeit = market.forfeit_recovery_leg_not_atomic(&mut b, 0, 1);
    assert_eq!(
        forfeit.err(),
        Some(V16Error::LockActive),
        "the side-mode disjunct no longer admits a forfeit on an Active asset"
    );

    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(market.header.mode, 0, "Live");
    assert_eq!(after.lifecycle, AssetLifecycleV16::Active);
    assert_eq!(
        after.oi_eff_long_q, after.oi_eff_short_q,
        "the third party is never left facing an empty opposite side"
    );
    assert_eq!(after.oi_eff_long_q, 20_000);
    assert_eq!(after.stored_pos_count_long, 1, "C's leg");
    assert_eq!(
        after.stored_pos_count_short, 1,
        "B's leg is still there to face it"
    );
    assert_eq!(market.validate_shape(), Ok(()));

    // …and C, who never acted, can still get out. Before the fix this was `Err(NonProgress)`
    // for every size, and `withdraw` was `Err(Stale)` behind the un-closable leg.
    let reduced = market.rebalance_reduce_position_not_atomic(
        &mut c,
        RebalanceRequestV16 {
            asset_index: 0,
            reduce_q: 20_000,
        },
    );
    assert!(
        reduced.is_ok(),
        "the third party must keep its exit: {reduced:?}"
    );
    assert_ne!(reduced.unwrap().reduced_q, 0);
}

/// B2 — funding keeps running for the whole asset. `accrual_activity_for_asset_segment` (`:2489`)
/// sets `balanced_exposure = oi_eff_long_q != 0 && oi_eff_short_q != 0` (`:2497`) and
/// `funding_active` depends on it, so the one-sided book silently cancelled the funding leg for
/// EVERY account on the asset (X-01 verifier §5, X-02 §3 reader #3). With the forfeit refused the
/// book stays two-sided and funding accrues.
#[test]
fn f04_x02_funding_keeps_running_for_the_whole_asset() {
    let (mut header, mut markets) = market_fixture_with_funding(1, PRICE);
    let (mut aa, mut bb, mut cc) = (
        account_fixture(1, 11),
        account_fixture(1, 12),
        account_fixture(1, 13),
    );
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut aa);
    let mut b = PortfolioV16ViewMut::new(&mut bb);
    let mut c = PortfolioV16ViewMut::new(&mut cc);

    market.deposit_not_atomic(&mut a, 500_000_000).unwrap();
    market.deposit_not_atomic(&mut b, 500_000_000).unwrap();
    market.deposit_not_atomic(&mut c, 500_000_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut c,
            &mut b,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(20_000),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    let f_long_0 = market.markets[0]
        .engine
        .asset
        .try_to_runtime()
        .unwrap()
        .f_long_num;
    let pre = market
        .accrue_asset_to_not_atomic(0, 2, PRICE, 10_000, true)
        .unwrap();
    assert!(pre.funding_active, "funding is active on a symmetric book");
    let f_long_1 = market.markets[0]
        .engine
        .asset
        .try_to_runtime()
        .unwrap()
        .f_long_num;
    assert_ne!(f_long_1, f_long_0);

    for acct in [&mut b, &mut c] {
        let _ = market.full_account_refresh_not_atomic(acct);
    }
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut a,
            &mut b,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(447_912),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    market
        .rebalance_reduce_position_not_atomic(
            &mut a,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: 447_912,
            },
        )
        .unwrap();
    assert_eq!(
        market.forfeit_recovery_leg_not_atomic(&mut b, 0, 1).err(),
        Some(V16Error::LockActive),
        "the forfeit that used to freeze funding is refused"
    );

    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.oi_eff_long_q, asset.oi_eff_short_q);
    assert_ne!(asset.oi_eff_long_q, 0);
    let f_long_2 = asset.f_long_num;
    let post = market
        .accrue_asset_to_not_atomic(0, 3, PRICE, 10_000, true)
        .unwrap();
    assert!(
        post.funding_active,
        "balanced_exposure (:2497) still holds, so funding is NOT switched off"
    );
    let f_long_3 = market.markets[0]
        .engine
        .asset
        .try_to_runtime()
        .unwrap()
        .f_long_num;
    assert_ne!(f_long_3, f_long_2, "the funding index keeps moving");
}

// =================================================================================================
// PART C — the AS-02 route: the minimal three-call sequence, and the bounded adversarial search.
// Copied from `verify/poc/AS-02/poc_AS-02.rs`; the search's verdict is inverted from
// "unequal_dispatchable > 0" to "== 0".
// =================================================================================================

#[derive(Clone, Copy, Debug)]
struct Shape {
    mode: u8,
    lifecycle: AssetLifecycleV16,
    oi_long: u128,
    oi_short: u128,
}

impl Shape {
    fn dispatchable(&self) -> bool {
        matches!(
            self.lifecycle,
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly
        )
    }
    fn equal(&self) -> bool {
        self.oi_long == self.oi_short
    }
}

fn shape(market: &MarketGroupV16ViewMut<'_, u64>, asset_index: usize) -> Shape {
    let asset = market.markets[asset_index]
        .engine
        .asset
        .try_to_runtime()
        .unwrap();
    Shape {
        mode: market.header.mode,
        lifecycle: asset.lifecycle,
        oi_long: asset.oi_eff_long_q,
        oi_short: asset.oi_eff_short_q,
    }
}

fn crank(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    account: &mut PortfolioV16ViewMut<'_>,
    now_slot: u64,
) -> bool {
    market
        .permissionless_auto_crank_not_atomic(
            account,
            AutoCrankWorkV16 {
                now_slot,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .is_ok()
}

/// C1 — the AS-02 minimal sequence (`poc_as02_minimal_active_asymmetry_no_admin_action`,
/// `poc_AS-02.rs:866`). Before the fix it committed `oil=37741 / ois=0` on a Live/Active asset
/// with `validate_shape=Ok(())`. Now call 3 is refused and the pair stays equal.
#[test]
fn f04_as02_minimal_active_asymmetry_is_unreachable() {
    let (mut header, mut markets) = market_fixture(1, PRICE);
    let mut a = account_fixture(1, 11);
    let mut b = account_fixture(1, 12);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut lg = PortfolioV16ViewMut::new(&mut a);
    let mut sh = PortfolioV16ViewMut::new(&mut b);
    market.deposit_not_atomic(&mut lg, 100_000_000).unwrap();
    market.deposit_not_atomic(&mut sh, 100_000_000).unwrap();

    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut lg,
            &mut sh,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(447_912),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    let s = shape(&market, 0);
    assert!(s.equal() && s.lifecycle == AssetLifecycleV16::Active);

    market
        .rebalance_reduce_position_not_atomic(
            &mut lg,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: 410_171,
            },
        )
        .unwrap();
    let s = shape(&market, 0);
    assert!(s.equal() && s.oi_long == 37_741);
    assert_eq!(
        market.markets[0]
            .engine
            .asset
            .try_to_runtime()
            .unwrap()
            .mode_short,
        SideModeV16::DrainOnly,
        "the side mode latched, which is what used to open the forfeit"
    );

    let forfeit = market.forfeit_recovery_leg_not_atomic(&mut sh, 0, 1);
    assert_eq!(forfeit.err(), Some(V16Error::LockActive));

    let s = shape(&market, 0);
    assert_eq!(s.mode, 0, "market mode Live");
    assert_eq!(s.lifecycle, AssetLifecycleV16::Active);
    assert!(s.dispatchable());
    assert!(s.equal(), "the dispatchable asymmetry is gone");
    assert_eq!(s.oi_long, 37_741);
    assert_eq!(s.oi_short, 37_741);
    assert_eq!(market.validate_shape(), Ok(()));

    // the short owner keeps its own exit
    let reduced = market.rebalance_reduce_position_not_atomic(
        &mut sh,
        RebalanceRequestV16 {
            asset_index: 0,
            reduce_q: 37_741,
        },
    );
    assert!(reduced.is_ok(), "{reduced:?}");
}

/// C2 — the bounded adversarial search over PUBLIC entry sequences
/// (`poc_as02_search_finds_reachable_dispatchable_asymmetry`, `poc_AS-02.rs:401`), verdict
/// inverted. The recorded baseline at `2c38570a` is
/// `seeds_reaching_dispatchable_asymmetry=27 | unequal_pairs_on_dispatchable_lifecycle=27`
/// out of 4 000 sequences (identical at `av`, `verify/poc/X-02/out_repro_AS02_*.txt`).
/// With the gate the same search must report ZERO.
#[test]
fn f04_as02_no_public_entry_sequence_reaches_a_dispatchable_asymmetry() {
    const SEQUENCES: u64 = 4_000;
    const STEPS: usize = 14;
    let mut checks = 0u64;
    let mut unequal_dispatchable = 0u64;
    let mut unequal_nondispatchable = 0u64;
    let mut oks = 0u64;
    let mut witnesses: Vec<String> = Vec::new();
    let mut seeds_hit = 0u64;
    for seed in 0..SEQUENCES {
        let mut rng = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(12345);
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        let (mut header, mut markets) = market_fixture(1, PRICE);
        let mut a = account_fixture(1, 11);
        let mut b = account_fixture(1, 12);
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut a);
        let mut short = PortfolioV16ViewMut::new(&mut b);
        let _ = market.deposit_not_atomic(&mut long, 100_000_000);
        let _ = market.deposit_not_atomic(&mut short, 100_000_000);
        let mut slot = 0u64;
        let mut trace: Vec<u8> = Vec::new();
        for _ in 0..STEPS {
            let r = next();
            let action = (r % 13) as u8;
            let q = 1 + (r >> 8) % (POS_SCALE as u64);
            let px = 100_000 + (r >> 20) % 1_900_000;
            trace.push(action);
            let ok = match action {
                0 => market
                    .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                        &mut long,
                        &mut short,
                        TradeRequestV16 {
                            asset_index: 0,
                            size_q: signed_q(q as u128),
                            exec_price: PRICE,
                            fee_bps: 0,
                        },
                        true,
                    )
                    .is_ok(),
                1 => market
                    .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                        &mut short,
                        &mut long,
                        TradeRequestV16 {
                            asset_index: 0,
                            size_q: signed_q(q as u128),
                            exec_price: PRICE,
                            fee_bps: 0,
                        },
                        true,
                    )
                    .is_ok(),
                2 => {
                    slot += 1;
                    let _ = market.set_asset_raw_oracle_target_not_atomic(0, px);
                    market
                        .accrue_asset_to_not_atomic(0, slot, px, 0, false)
                        .is_ok()
                }
                3 => market
                    .liquidate_account_not_atomic(
                        &mut long,
                        LiquidationRequestV16 { asset_index: 0 },
                    )
                    .is_ok(),
                4 => market
                    .liquidate_account_not_atomic(
                        &mut short,
                        LiquidationRequestV16 { asset_index: 0 },
                    )
                    .is_ok(),
                5 => market
                    .rebalance_reduce_position_not_atomic(
                        &mut long,
                        RebalanceRequestV16 {
                            asset_index: 0,
                            reduce_q: q as u128,
                        },
                    )
                    .is_ok(),
                6 => market
                    .rebalance_reduce_position_not_atomic(
                        &mut short,
                        RebalanceRequestV16 {
                            asset_index: 0,
                            reduce_q: q as u128,
                        },
                    )
                    .is_ok(),
                7 => crank(&mut market, &mut long, slot),
                8 => crank(&mut market, &mut short, slot),
                9 => market.mark_asset_drain_only_not_atomic(0).is_ok(),
                10 => market.force_asset_recovery_not_atomic(0, slot).is_ok(),
                11 => market
                    .forfeit_recovery_leg_not_atomic(&mut long, 0, 1)
                    .is_ok(),
                12 => market
                    .forfeit_recovery_leg_not_atomic(&mut short, 0, 1)
                    .is_ok(),
                _ => false,
            };
            if ok {
                oks += 1;
            }
            let s = shape(&market, 0);
            checks += 1;
            if !s.equal() {
                if s.dispatchable() {
                    unequal_dispatchable += 1;
                    if witnesses.len() < 10 {
                        witnesses.push(format!(
                            "seed={seed} trace={trace:?} mode={} lifecycle={:?} oi_eff_long={} oi_eff_short={}",
                            s.mode, s.lifecycle, s.oi_long, s.oi_short
                        ));
                    }
                    seeds_hit += 1;
                    break;
                } else {
                    unequal_nondispatchable += 1;
                }
            }
        }
    }
    eprintln!(
        "F04-SEARCH|sequences={SEQUENCES}|steps={STEPS}|state_checks={checks}|successful_actions={oks}|\
         seeds_reaching_dispatchable_asymmetry={seeds_hit}|\
         unequal_pairs_on_dispatchable_lifecycle={unequal_dispatchable}|\
         unequal_pairs_on_non_dispatchable_lifecycle={unequal_nondispatchable}"
    );
    for w in &witnesses {
        eprintln!("F04-WITNESS|{w}");
    }
    assert_eq!(
        unequal_dispatchable, 0,
        "a public-entry sequence still reaches a dispatchable-lifecycle asymmetry (baseline: 27/4000)"
    );
    assert_eq!(seeds_hit, 0);
    assert_ne!(
        unequal_nondispatchable, 0,
        "non-vacuity: the search must still reach one-sided NON-dispatchable (Recovery/Retired) \
         lifecycles, which are legal — otherwise the search stopped exercising the forfeit at all"
    );
}

// =================================================================================================
// PART D — LIVENESS: the gate must NOT break the legitimate owner exit C-04 relies on.
// `av spec.md:65` (requirement 30) / `av spec.md:1580`: the dead-leg exit exists precisely FOR
// terminal/recovery assets, and `av spec.md:892-898` forbids the permissionless crank from doing
// it instead, so a Recovery-lifecycle asset's dead leg MUST stay forfeitable by its owner.
// =================================================================================================

/// D1 — the SAME fixture the gate now refuses, with the asset moved to the Recovery lifecycle:
/// the owner exit succeeds, on the identical leg and side mode. This is the discriminating pair —
/// only the asset lifecycle differs between A3 (refused) and D1 (admitted).
#[test]
fn f04_c04_recovery_lifecycle_owner_exit_still_works() {
    let mut w = drive_to_the_barrier(false);
    assert_eq!(w.asset().mode_long, SideModeV16::DrainOnly);
    assert_eq!(w.asset().lifecycle, AssetLifecycleV16::Active);
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

    // asset lifecycle -> Recovery while the MARKET stays Live (`force_asset_recovery_not_atomic`).
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.force_asset_recovery_not_atomic(0, 4).unwrap();
    }
    assert_eq!(w.asset().lifecycle, AssetLifecycleV16::Recovery);
    assert_eq!(
        decode_mode(&w.header),
        MarketModeV16::Live,
        "market still Live"
    );

    let outcome = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut long = PortfolioV16ViewMut::new(&mut w.l);
        m.forfeit_recovery_leg_not_atomic(&mut long, 0, u128::MAX)
    };
    assert!(
        outcome.is_ok(),
        "a Recovery-lifecycle asset's dead leg MUST still be forfeitable by its owner \
         (av spec.md:65 requirement 30, av spec.md:1580): {outcome:?}"
    );
    assert!(
        !w.l.legs[0].try_to_runtime().unwrap().active
            || w.asset().pending_obligation_count_long != 0,
        "the exit did real work: the leg detached or became a pending obligation"
    );
}

// D2 (market-mode Recovery, the FIRST disjunct) is untouched by this change — the gate narrows
// only the third disjunct — and is exercised end-to-end by
// `verify/poc/C-04/poc_C04.rs::poc_c04_b2_c_owner_exit_commits_recovery_then_terminal_is_permissionless`,
// run against this branch in `verify/fixes/F-04.md` §C-04.
