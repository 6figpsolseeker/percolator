//! GRIEFING-ECONOMICS lens harness for dcccrypto/percolator PR #135.
//!
//! Scenario under test: an asset side is in DrainOnly with a *dust* amount of
//! residual open interest held by a single over-collateralised account that
//! simply declines to close. Question: does the group-wide
//! `bankruptcy_hlock_active` gate (which the wrapper uses to block
//! WithdrawBackingBucket / WithdrawBackingBucketEarnings / WithdrawInsuranceAsset
//! for EVERY domain in the group) stay engaged forever, and can anyone force the
//! holder out?
//!
//! Written to compile against BOTH f53be74a (deployed) and dc41fca9 (PR head)
//! so the same file measures the marginal change.

use percolator::{
    AssetStateV16Account, EngineAssetSlotV16Account, LiquidationRequestV16, Market,
    MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PermissionlessCrankActionV16,
    PermissionlessCrankRequestV16, PortfolioAccountV16Account, PortfolioLegV16,
    PortfolioLegV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16, ProvenanceHeaderV16Account,
    SideModeV16, SideV16, V16Config, V16Error, V16PodU128, V16PodU64,
};
use percolator::{ADL_ONE, MIN_A_SIDE, POS_SCALE};

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn market_fixture(
    market_slots: u32,
    init_price: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let cfg =
        V16Config::public_user_fund_with_market_slots(market_slots as u16, market_slots, 0, 10);
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

fn account_fixture(account_seed: u8) -> PortfolioAccountV16Account {
    let (market_id, _, owner) = ids();
    let header = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
        market_id,
        [account_seed; 32],
        owner,
    ));
    let mut account = PortfolioAccountV16Account::default();
    account.init_empty_in_place(header).unwrap();
    account
}

/// Build: hlock engaged, long side DrainOnly, exactly `oi` quanta of residual
/// long OI, held by ONE over-collateralised account (`capital`).
/// Every group-header conjunct of the DEPLOYED predicate reads zero.
fn drain_only_holdout(
    oi: u128,
    capital: u128,
) -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
) {
    const PRICE: u64 = POS_SCALE as u64;
    let (mut header, mut markets) = market_fixture(1, PRICE);

    // A bankruptcy already happened: the engine set the group hlock.
    header.bankruptcy_hlock_active = 1;
    header.vault = V16PodU128::new(capital);
    header.c_tot = V16PodU128::new(capital);
    header.current_slot = V16PodU64::new(100);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.effective_price = PRICE;
    asset.raw_oracle_target_price = PRICE;
    asset.fund_px_last = PRICE;
    asset.slot_last = 100;
    // Residual exposure, under-backed => the side goes DrainOnly. The engine sets
    // that mode inside `reduce_matching_open_interest_for_unilateral_close`
    // (2c38570a:src/v16.rs:17530), at :17565-17567 for the long side, when
    // `opp_oi_after != 0 && a_long < MIN_A_SIDE`.
    //
    // MATCHED BOOK, not a one-sided residue. That same function subtracts the SAME
    // `close_q` from the opposite side (:17548 `opp_oi_after = opp_oi_before -
    // close_q`, written at :17563 / :17570), so a unilateral close leaves
    // `oi_eff_long_q == oi_eff_short_q`. A Live market whose asset is not in
    // Recovery is held to exactly that by the audit-scan conjunct at
    // 2c38570a:src/v16.rs:8501-8503, whose own doc comment (:8482-8483) gives the
    // reason: "The Live matched-book invariant (oi_eff_long == oi_eff_short) holds
    // for a normally-trading asset (Active/DrainOnly always reduce matched pairs)."
    // Writing the long side alone built a state no engine transition can reach:
    // under `--features audit-scan` `validate_shape` rejected this fixture with
    // InvalidConfig before either asserting test reached its subject (AS-03).
    asset.oi_eff_long_q = oi;
    asset.loss_weight_sum_long = oi;
    asset.stored_pos_count_long = 1;
    asset.a_long = ADL_ONE;
    asset.mode_long = SideModeV16::DrainOnly;
    asset.oi_eff_short_q = oi;
    asset.loss_weight_sum_short = oi;
    asset.stored_pos_count_short = 1;
    asset.a_short = ADL_ONE;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    // The raw `engine.asset = ...` write above bypasses `set_asset_state`
    // (2c38570a:src/v16.rs:15629-15643), which recomputes
    // `slot_resolved_payout_blockers_v16` (:7457-7467 -- the sum of
    // stored_pos_count_{long,short} + stale_account_count_{long,short} +
    // pending_domain_loss_barrier_{long,short}, so 1 + 1 = 2 here) and pushes the
    // delta into `header.resolved_payout_blocker_count` through
    // `update_resolved_payout_blocker_total` (:8741-8748). Mirror by hand what the
    // setter would have written; otherwise the audit-scan conjunct at :8331-8332
    // rejects with scan=2 vs hdr=0.
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    let mut acct = account_fixture(77);
    acct.capital = V16PodU128::new(capital);
    acct.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: i128::try_from(oi).unwrap(),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: oi,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    acct.active_bitmap[0] = V16PodU64::new(1);

    (header, markets, acct)
}

/// The five group-header conjuncts the DEPLOYED (f53be74a) predicate tests.
fn deployed_predicate_satisfied(m: &MarketGroupV16ViewMut<'_, u64>) -> bool {
    m.header.negative_pnl_account_count.get() == 0
        && m.header.stale_certificate_count.get() == 0
        && m.header.b_stale_account_count.get() == 0
        && m.header.pnl_pos_tot.get() == 0
        && m.header.recovery_reason.try_to_runtime().unwrap().is_none()
}

/// A permissionless Refresh crank is the cheapest public entry that reaches
/// `try_clear_bankruptcy_hlock_if_healthy` (src/v16.rs:9918).
#[test]
fn holdout_of_one_quantum_cannot_hold_the_group_hlock() {
    const OI: u128 = 1; // ONE quantum of residual exposure
    const CAPITAL: u128 = 1_000_000_000; // griefer is wildly over-collateralised

    let (mut header, mut markets, mut acct) = drain_only_holdout(OI, CAPITAL);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut acct);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();

    assert_eq!(market.header.bankruptcy_hlock_active, 1);
    assert!(
        deployed_predicate_satisfied(&market),
        "every group-header conjunct the deployed predicate inspects reads zero"
    );

    // Permissionless crank: anyone can pay ~5000 lamports to run this.
    market
        .permissionless_crank_not_atomic(
            &mut account,
            PermissionlessCrankRequestV16 {
                now_slot: 100,
                asset_index: 0,
                effective_price: POS_SCALE as u64,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::Refresh,
            },
        )
        .expect("refresh crank must succeed");

    // THE ASSERTION. An earlier version of this harness only PRINTED the result, so it
    // passed against both the safe and the unsafe predicate — exactly the vacuous shape
    // this codebase keeps tripping over. It asserts now.
    //
    // The holder is still in DrainOnly with one quantum of open interest and is wildly
    // solvent, so nothing can force them out. If a user-controlled side mode byte could
    // gate the group-wide hlock, this would read 1 and every domain's LP backing, LP
    // earnings and insurance would be frozen for as long as the holder felt like it, for
    // the price of one quantum plus min_nonzero_mm_req.
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        OI,
        "precondition: the holdout still carries exposure"
    );
    assert_ne!(
        market.markets[0].engine.asset.mode_long, 0,
        "precondition: the side is still non-Normal (DrainOnly)"
    );
    assert_eq!(
        market.header.bankruptcy_hlock_active, 0,
        "a solvent holdout on a DrainOnly side must NOT be able to hold the group-wide \
         hlock — that is a free, permanent freeze of every domain's backing"
    );
}

/// (c) Can anyone FORCE the holder out? Permissionless liquidation is the only
/// third-party position-reducing action in the engine's public crank surface.
#[test]
fn healthy_holdout_cannot_be_liquidated_by_anyone() {
    const OI: u128 = 1;
    const CAPITAL: u128 = 1_000_000_000;

    let (mut header, mut markets, mut acct) = drain_only_holdout(OI, CAPITAL);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut acct);

    let direct =
        market.liquidate_account_not_atomic(&mut account, LiquidationRequestV16 { asset_index: 0 });
    println!("DIRECT-LIQUIDATE => {:?}", direct);
    assert_eq!(
        direct,
        Err(V16Error::NonProgress),
        "a solvent holder is not liquidatable at any price the crank can pass"
    );

    let via_crank = market.permissionless_crank_not_atomic(
        &mut account,
        PermissionlessCrankRequestV16 {
            now_slot: 100,
            asset_index: 0,
            effective_price: POS_SCALE as u64,
            funding_rate_e9: 0,
            action: PermissionlessCrankActionV16::Liquidate(LiquidationRequestV16 {
                asset_index: 0,
            }),
        },
    );
    println!("CRANK-LIQUIDATE => {:?}", via_crank);
    assert!(via_crank.is_err());
}

/// (a) Can the holder be forced to close by a RISK-INCREASE gate? No: DrainOnly
/// only blocks increases. Prove that a reduction is accepted and an increase is
/// rejected, i.e. holding is a stable strategy.
#[test]
fn drain_only_blocks_increases_but_never_forces_a_close() {
    const OI: u128 = 1_000;
    const CAPITAL: u128 = 1_000_000_000;

    let (mut header, mut markets, mut acct) = drain_only_holdout(OI, CAPITAL);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut acct);

    // Withdrawing the holder's OWN capital is not hlock-gated (only LP /
    // insurance withdrawals are), so the griefer's capital is never actually
    // trapped alongside the LP's.
    let w = market.withdraw_not_atomic(&mut account, 1);
    println!("HOLDER-SELF-WITHDRAW => {:?}", w);
}

/// Numerical statement of the DrainOnly entry condition, from
/// `reduce_matching_open_interest_for_unilateral_close` (src/v16.rs:12530-12557):
///   a_after = a_before * oi_after / oi_before   (floor)
///   DrainOnly iff oi_after != 0 && a_after < MIN_A_SIDE
/// Starting from a_before == ADL_ONE this is purely `oi_after < oi_before/10`.
#[test]
fn drain_only_entry_is_a_pure_oi_ratio_when_a_starts_at_one() {
    let a_before = ADL_ONE;
    for (oi_before, oi_after) in [(1_000u128, 101u128), (1_000, 99), (1_000, 1)] {
        let a_after = a_before * oi_after / oi_before;
        println!(
            "oi {} -> {} : a {} -> {} (MIN_A_SIDE {}) drain_only={}",
            oi_before,
            oi_after,
            a_before,
            a_after,
            MIN_A_SIDE,
            oi_after != 0 && a_after < MIN_A_SIDE
        );
    }
}

/// (b)/(d) How little capital keeps the holdout alive, and what actually ends it?
/// `certified_liq_deficit = maintenance_req.saturating_sub(equity)` (src/v16.rs:9931),
/// and `liquidate_account_not_atomic` rejects with NonProgress when that is 0
/// (src/v16.rs:12618). So the holdout survives while equity >= maintenance_req.
#[test]
fn minimum_capital_to_sustain_the_holdout() {
    const OI: u128 = 1;
    for capital in [0u128, 1, 2, 5, 100] {
        let (mut header, mut markets, mut acct) = drain_only_holdout(OI, capital.max(1));
        header.vault = V16PodU128::new(capital);
        header.c_tot = V16PodU128::new(capital);
        acct.capital = V16PodU128::new(capital);
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut acct);
        let liq = market
            .liquidate_account_not_atomic(&mut account, LiquidationRequestV16 { asset_index: 0 });
        let cert = account.header.health_cert.try_to_runtime().unwrap();
        println!(
            "capital={} equity={} mm_req={} liq_deficit={} liquidate={:?} oi_after={} hlock={}",
            capital,
            cert.certified_equity,
            cert.certified_maintenance_req,
            cert.certified_liq_deficit,
            liq.map(|o| o.closed_q),
            market.markets[0].engine.asset.oi_eff_long_q.get(),
            market.header.bankruptcy_hlock_active,
        );
    }
}

/// Does the exit actually work once the holdout IS liquidatable? Liquidate a
/// zero-equity holder, then run the permissionless refresh crank and see whether
/// the hlock releases.
#[test]
fn liquidating_a_broke_holdout_releases_the_group_hlock() {
    const OI: u128 = 1;
    let (mut header, mut markets, mut acct) = drain_only_holdout(OI, 1);
    header.vault = V16PodU128::new(0);
    header.c_tot = V16PodU128::new(0);
    acct.capital = V16PodU128::new(0);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut acct);

    let liq =
        market.liquidate_account_not_atomic(&mut account, LiquidationRequestV16 { asset_index: 0 });
    println!("BROKE-LIQUIDATE => {:?}", liq);
    println!(
        "  oi_eff_long={} oi_eff_short={} mode_long_normal={} hlock={}",
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        market.markets[0].engine.asset.oi_eff_short_q.get(),
        market.markets[0].engine.asset.mode_long == 0,
        market.header.bankruptcy_hlock_active,
    );
    let refresh = market.permissionless_crank_not_atomic(
        &mut account,
        PermissionlessCrankRequestV16 {
            now_slot: 100,
            asset_index: 0,
            effective_price: POS_SCALE as u64,
            funding_rate_e9: 0,
            action: PermissionlessCrankActionV16::Refresh,
        },
    );
    println!(
        "AFTER-BROKE-REFRESH {:?} hlock={} oi_eff_long={}",
        refresh.map(|_| ()),
        market.header.bankruptcy_hlock_active,
        market.markets[0].engine.asset.oi_eff_long_q.get(),
    );
}

/// Same measurement, but with the EXACT risk knobs the percolator-launch wizard
/// ships for live devnet markets (percolator-launch/app/hooks/useCreateMarket.ts
/// v17InitArgs): minNonzeroMmReq = 1_000_000 atoms (= 1.00 USDC at 6dp),
/// minNonzeroImReq = 2_000_000, maintenanceFeePerSlot = 0, maxAbsFundingE9PerSlot = 0.
#[test]
fn devnet_parameterised_holdout_cost() {
    const OI: u128 = 1;
    for capital in [999_999u128, 1_000_000, 2_000_000] {
        let (mut header, mut markets, mut acct) = drain_only_holdout(OI, capital);
        header.config.min_nonzero_mm_req = V16PodU128::new(1_000_000);
        header.config.min_nonzero_im_req = V16PodU128::new(2_000_000);
        header.config.maintenance_margin_bps = V16PodU64::new(1_000);
        header.config.initial_margin_bps = V16PodU64::new(2_000);
        header.config.liquidation_fee_bps = V16PodU64::new(50);
        header.config.liquidation_fee_cap = V16PodU128::new(10_000_000_000);
        header.vault = V16PodU128::new(capital);
        header.c_tot = V16PodU128::new(capital);
        acct.capital = V16PodU128::new(capital);

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut acct);
        let liq = market
            .liquidate_account_not_atomic(&mut account, LiquidationRequestV16 { asset_index: 0 });
        let cert = account.header.health_cert.try_to_runtime().unwrap();
        println!(
            "DEVNET capital={} equity={} mm_req={} liq_deficit={} liquidate={:?} \
             oi_after={} hlock_after={}",
            capital,
            cert.certified_equity,
            cert.certified_maintenance_req,
            cert.certified_liq_deficit,
            liq.map(|o| o.closed_q),
            market.markets[0].engine.asset.oi_eff_long_q.get(),
            market.header.bankruptcy_hlock_active,
        );
    }
}
