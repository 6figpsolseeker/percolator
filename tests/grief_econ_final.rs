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
//!
//! CITE REF. Every `src/v16.rs:N` below is a line number at the fork's `2c38570a` — the
//! loop base this file's fixture repair (AS-03) was measured at, and the ref whose `src/`
//! tree is byte-identical to this branch's base. Four cites in this file were still legacy
//! `f53be74a`/`dc41fca9` numbers and were re-pointed in AS-04:
//!   `:9918`        -> `:19282-19296`  (`try_clear_bankruptcy_hlock_if_healthy`)
//!   `:9931`        -> `:13934-13938`  (`certified_liq_deficit`)
//!   `:12618`       -> `:17637-17638`  (liquidation's zero-deficit NonProgress gate)
//!   `:12530-12557` -> `:17530-17582`  (`reduce_matching_open_interest_for_unilateral_close`)
//!
//! ASSERTIONS. Until AS-04, five of the seven tests here asserted nothing about the engine:
//! they only `println!`ed, so they passed under `--features audit-scan` while running on a
//! fixture the audit validator REJECTED, and three of them were printing a FALSE answer
//! (`liquidating_a_broke_holdout_releases_the_group_hlock` printed `Err(NonProgress)` purely
//! because the hand-written one-sided book made `unilateral_close_capacity` zero). AS-03
//! repaired the fixture; AS-04 gives each of those five a real assertion, every one derived
//! from a cited engine line rather than from what the test happens to print.

use percolator::{
    AssetStateV16Account, EngineAssetSlotV16Account, LiquidationRequestV16, Market,
    MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PermissionlessCrankActionV16,
    PermissionlessCrankRequestV16, PortfolioAccountV16Account, PortfolioLegV16,
    PortfolioLegV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16, ProvenanceHeaderV16Account,
    RebalanceOutcomeV16, RebalanceRequestV16, SideModeV16, SideV16, V16Config, V16Error,
    V16PodU128, V16PodU64,
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
/// `try_clear_bankruptcy_hlock_if_healthy` (2c38570a:src/v16.rs:19282-19296; the `:9918`
/// this comment used to carry was a legacy f53be74a/dc41fca9 line number).
///
/// POST-F-03 NOTE, and it governs every `bankruptcy_hlock_active == 0` assertion in this
/// file. Engine `main` 22440ebb carries F-03 (`9d3ceec5`), which deleted the two
/// `explicit_unallocated_loss_*` terms from `group_has_unabsorbed_bankruptcy_loss`
/// (`2c38570a:src/v16.rs:19261-19280`) — the predicate `try_clear_…` negates at `:19291`.
/// Post-F-03 that predicate tests two disjuncts where it tested four, so it returns `true`
/// on a strict SUBSET of the states it used to: every "the hlock clears" assertion here
/// holds a fortiori after the merge. `drain_only_holdout` writes neither
/// `explicit_unallocated_loss_*` nor `pending_domain_loss_barrier_*`, and no call these
/// tests make writes either (`kernel_normalize_social_loss_carry`'s write sites are leg
/// clears that cross a whole SOCIAL_LOSS_DEN atom with no side weight left; these fixtures
/// carry no B residual), so the predicate is false at BOTH refs. Re-measured green at
/// 22440ebb under both feature sets (AS-04).
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
    // Strengthened in AS-04 from a bare `is_err()` to the exact error (strictly stronger —
    // this implies `is_err()`). The crank's Liquidate arm calls the same
    // `liquidate_account_not_atomic` at :15494 and hands any error to
    // `kernel_commit_declared_liquidation_recovery` (:2179-2190), whose `_ => Err(error)` at
    // :2188 converts ONLY RecoveryRequired-in-Recovery-mode. So the refusal the crank
    // surfaces is the same solvency gate at :17637-17638 the direct call above hit.
    assert_eq!(
        via_crank.err(),
        Some(V16Error::NonProgress),
        "the permissionless crank propagates the liquidation verdict verbatim, so a solvent \
         holder is not liquidatable through it either"
    );
}

/// (a) Can the holder be forced to close by a RISK-INCREASE gate? No: DrainOnly
/// only blocks increases. Prove that a reduction is accepted and an increase is
/// rejected, i.e. holding is a stable strategy.
///
/// The INCREASE half is cite-only and stays cite-only, deliberately:
/// `require_asset_risk_change_allowed` (`2c38570a:src/v16.rs:15647-15660`) early-returns
/// `Ok(())` for every non-increasing change at `:15652-15653`, and otherwise calls
/// `asset_risk_increase_gate` (`:22205-22217`), which returns `Err(LockActive)` when
/// `mode_long != Normal`. That is the whole of "DrainOnly blocks increases". Outside the
/// verifier-only shims its one public reachability is the two-account trade path
/// (`:18361`), which this single-account fixture cannot drive, so this test pins the
/// REDUCTION half executably and leaves the increase half to the cite.
///
/// Until AS-04 this test asserted NOTHING — it printed `Err(Stale)` and passed.
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
    // `withdraw_not_atomic` (:20076-20146) refuses at :20088-20090 —
    // `!active_bitmap_is_empty(...) => Err(V16Error::Stale)`, the OPEN-POSITION gate, which
    // `drain_only_holdout` arms by setting `acct.active_bitmap[0] = 1`. That is the FIRST
    // gate the call meets, and the function body reads no bankruptcy-hlock field anywhere:
    // the hlock gates LP principal / LP earnings / insurance withdrawals, never a user's own
    // capital. The error value is therefore the proof of the sentence above it.
    assert_eq!(
        w,
        Err(V16Error::Stale),
        "the holder's own withdraw is refused by the open-position gate at :20088-20090, not \
         by the group hlock"
    );
    // ...and the refusal forces nothing: it returns before :20106's settle, so every byte is
    // where the fixture left it.
    assert_eq!(
        market.header.bankruptcy_hlock_active, 1,
        "a refused self-withdraw must not move the group hlock"
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        OI,
        "nothing forced the holdout's position down"
    );
    assert_ne!(
        market.markets[0].engine.asset.mode_long, 0,
        "the side is still non-Normal (DrainOnly)"
    );
    assert_eq!(
        account.header.capital.get(),
        CAPITAL,
        "the refused withdraw debited nothing"
    );

    // The exit is nonetheless OPEN whenever the holder chooses it — which is the other half
    // of "never forces a close": DrainOnly is not a trap in either direction.
    // `rebalance_reduce_position_not_atomic` (:17799-17850) is the owner's unilateral
    // reduction. Its body calls `require_asset_risk_change_allowed` nowhere (a reduction is
    // not a risk increase), and its one lifecycle gate, `require_asset_live_reducible`
    // (:15833-15839), admits `Active | DrainOnly`. The budget is `unilateral_close_capacity`
    // — kernel :919-925, `account_effective_abs.min(oi_eff_long_q).min(oi_eff_short_q)` —
    // which is OI on the matched book AS-03 restored (it was 0 on the old one-sided fixture,
    // and that is exactly the artefact AS-03 found this file printing).
    let reduced = market.rebalance_reduce_position_not_atomic(
        &mut account,
        RebalanceRequestV16 {
            asset_index: 0,
            reduce_q: OI,
        },
    );
    println!("HOLDER-SELF-REDUCE => {:?}", reduced);
    assert_eq!(
        reduced,
        Ok(RebalanceOutcomeV16 { reduced_q: OI }),
        "a full reduction on a DrainOnly side is accepted: :17799 takes no risk-increase gate \
         and :15833-15839 admits Active/DrainOnly"
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        0,
        "the whole residual left through the voluntary exit"
    );
}

/// Numerical statement of the DrainOnly entry condition, from
/// `reduce_matching_open_interest_for_unilateral_close`
/// (2c38570a:src/v16.rs:17530-17582; the `:12530-12557` this comment used to carry was a
/// legacy f53be74a/dc41fca9 line number — `:17530` is the ref `drain_only_holdout` above
/// already cites for the same function):
///   a_after = wide_mul_div_floor_u128(a_before, oi_after, oi_before)   (`:17552`, floor)
///   DrainOnly iff oi_after != 0 && a_after < MIN_A_SIDE                (`:17565-17567`
///                                                 long, `:17572-17574` short)
/// Starting from a_before == ADL_ONE this is purely `oi_after < oi_before/10`, because
/// MIN_A_SIDE is one tenth of ADL_ONE (`2c38570a:src/lib.rs:16-17`: ADL_ONE = 1e15,
/// MIN_A_SIDE = 1e14) — asserted below rather than restated.
///
/// The floor is written out here rather than called: `wide_math` is a private module
/// outside `--features fork-facade` (`2c38570a:src/lib.rs:43-49`). For a_before = ADL_ONE
/// and oi_before = 1_000 the product `ADL_ONE * oi_after` is at most 1.01e17, far inside
/// u128, so the plain expression below IS the value `:17552` computes.
///
/// Until AS-04 this test asserted NOTHING — it printed a three-row table and passed.
#[test]
fn drain_only_entry_is_a_pure_oi_ratio_when_a_starts_at_one() {
    assert_eq!(
        MIN_A_SIDE,
        ADL_ONE / 10,
        "the DrainOnly threshold is one tenth of unit A (2c38570a:src/lib.rs:16-17) — the \
         whole 'pure oi ratio' claim in this test's name rests on it"
    );

    let a_before = ADL_ONE;
    // (oi_before, oi_after, expected a_after, expected DrainOnly). The 100 row is the EXACT
    // boundary, added by AS-04: a_after == MIN_A_SIDE there, and `:17565` tests `<`, so the
    // mode does NOT latch. Without it the table never touches the comparison it is about.
    for (oi_before, oi_after, expect_a_after, expect_drain_only) in [
        (1_000u128, 101u128, 101_000_000_000_000u128, false),
        (1_000, 100, 100_000_000_000_000, false),
        (1_000, 99, 99_000_000_000_000, true),
        (1_000, 1, 1_000_000_000_000, true),
    ] {
        let a_after = a_before * oi_after / oi_before;
        let drain_only = oi_after != 0 && a_after < MIN_A_SIDE;
        println!(
            "oi {} -> {} : a {} -> {} (MIN_A_SIDE {}) drain_only={}",
            oi_before, oi_after, a_before, a_after, MIN_A_SIDE, drain_only
        );
        assert_eq!(
            a_after, expect_a_after,
            "`:17552`'s floor for oi {oi_before} -> {oi_after} at a_before == ADL_ONE"
        );
        assert_eq!(
            drain_only, expect_drain_only,
            "`:17565-17567`'s latch for oi {oi_before} -> {oi_after}"
        );
        assert_eq!(
            drain_only,
            oi_after * 10 < oi_before,
            "and it is exactly the closed form this test is named for: a tenth of the prior \
             OI, with the boundary itself NOT latching"
        );
    }
}

/// (b)/(d) How little capital keeps the holdout alive, and what actually ends it?
/// `certified_liq_deficit = maintenance_req.saturating_sub(equity)`
/// (2c38570a:src/v16.rs:13934-13938, inside `refresh_account_and_certify_not_atomic`
/// `:13735` — the `:9931` this comment used to carry was a legacy f53be74a/dc41fca9 line
/// number), and `liquidate_account_not_atomic` rejects with NonProgress when that is 0
/// (`:17637-17638`; the old cite was `:12618`). So the holdout survives while
/// equity >= maintenance_req.
///
/// The maintenance requirement here is the config FLOOR, not a bps figure. One quantum at
/// PRICE == POS_SCALE is one atom of notional, and `maintenance_margin_bps` is 10_000, so
/// the bps term is 1 atom; `V16Config::public_user_fund_with_market_slots` sets
/// `min_nonzero_mm_req: 1` (`:4048`). Either way the sustaining threshold is 1 atom of
/// equity, and it is read off the config below rather than hard-coded.
/// `devnet_parameterised_holdout_cost` re-measures the same threshold at the launch
/// wizard's 1_000_000.
///
/// READ THE PRINTED COLUMNS CAREFULLY: the certificate is fetched AFTER the call, so a row
/// that liquidated prints its POST-close `mm_req=0 liq_deficit=0` next to `liquidate=Ok(1)`,
/// which reads like a contradiction and is not one — the gate at `:17637` consumed the
/// PRE-call deficit. The assertions are therefore on the liquidation VERDICT and on the
/// position, never on the post-call deficit.
///
/// Until AS-04 this test asserted NOTHING — it printed five rows and passed. On the
/// pre-AS-03 fixture it was printing `Err(NonProgress)` for the `capital=0` row too, from
/// the zero-close-budget gate at `:17667-17668`, purely because the hand-written one-sided
/// book made `unilateral_close_capacity` (`:919-925`) zero.
#[test]
fn minimum_capital_to_sustain_the_holdout() {
    const OI: u128 = 1;
    for capital in [0u128, 1, 2, 5, 100] {
        let (mut header, mut markets, mut acct) = drain_only_holdout(OI, capital.max(1));
        // The threshold this test exists to find, taken from the config the fixture builds.
        let mm_req = header.config.min_nonzero_mm_req.get();
        assert_eq!(
            mm_req, 1,
            "public_user_fund_with_market_slots sets min_nonzero_mm_req = 1 (:4048)"
        );
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

        // THE ASSERTION. Equity here is the account's capital (no PnL, no fee credits), so
        // the pre-call deficit at `:13934-13938` is `mm_req.saturating_sub(capital)`: zero
        // for every row at or above the floor, non-zero below it.
        if capital < mm_req {
            assert_eq!(
                liq.map(|o| o.closed_q),
                Ok(OI),
                "below the maintenance floor the deficit at :13934-13938 is non-zero, :17637 \
                 passes, and the close budget is min(1,1,1)=1 (:919-925) — so the holdout IS \
                 removable"
            );
            assert_eq!(
                market.markets[0].engine.asset.oi_eff_long_q.get(),
                0,
                "and the exposure is actually gone"
            );
        } else {
            assert_eq!(
                liq.map(|o| o.closed_q),
                Err(V16Error::NonProgress),
                "at or above the maintenance floor the deficit is 0 and :17637-17638 refuses \
                 — capital = {capital} sustains the holdout"
            );
            assert_eq!(
                market.markets[0].engine.asset.oi_eff_long_q.get(),
                OI,
                "and the exposure is untouched — nothing forced the holder out"
            );
        }
        // Either way the holdout does NOT hold the group hostage: liquidation runs
        // `refresh_account_and_certify_not_atomic` (:17626) BEFORE the deficit gate at
        // :17637, and that refresh calls `try_clear_bankruptcy_hlock_if_healthy`
        // unconditionally at :13921. So even the REFUSED rows release the hlock. (See the
        // post-F-03 note on `holdout_of_one_quantum_cannot_hold_the_group_hlock`.)
        assert_eq!(
            market.header.bankruptcy_hlock_active, 0,
            "a solvent holdout must not keep every domain's LP backing and insurance frozen"
        );
    }
}

/// Does the exit actually work once the holdout IS liquidatable? Liquidate a
/// zero-equity holder, then run the permissionless refresh crank and see whether
/// the hlock releases.
///
/// Until AS-04 this test asserted NOTHING, and on the pre-AS-03 fixture it was printing the
/// WRONG answer to its own question: `BROKE-LIQUIDATE => Err(NonProgress)` with
/// `oi_eff_long=1`, i.e. "the exit does not work". That was an artefact of the hand-written
/// one-sided book — `kernel_unilateral_close_capacity` (`:919-925`) is
/// `account_effective_abs.min(oi_eff_long_q).min(oi_eff_short_q)`, so `oi_eff_short_q = 0`
/// made the close budget 0 and the call died at `:17667-17668`, a DIFFERENT gate from the
/// solvency one this test is about. AS-03 restored the matched book; AS-04 asserts the
/// answer so the file can never print a false one again unnoticed.
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

    // THE ASSERTIONS. Equity is 0 against a maintenance requirement of 1 atom
    // (`min_nonzero_mm_req`, :4048), so the pre-call deficit at :13934-13938 is 1, the gate
    // at :17637-17638 passes, and the close budget is min(1,1,1) = 1 (:919-925).
    assert_eq!(
        liq.map(|o| o.closed_q),
        Ok(OI),
        "the exit works once the holdout is broke — this is the question the test's own doc \
         comment asks, and the pre-AS-03 fixture was answering it 'no' by artefact"
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        0,
        "the residual long exposure is gone"
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_short_q.get(),
        0,
        "and its matched opposite side went with it: \
         `reduce_matching_open_interest_for_unilateral_close` (:17530-17582) subtracts the \
         same close_q from the opposite side (:17548 -> :17563/:17570)"
    );
    // The side mode byte is STILL non-Normal after the close — `:17605`'s
    // `begin_side_reset_if_effective_oi_exhausted` leaves the long side in ResetPending —
    // and the hlock clears anyway. That is the predicate's documented design:
    // `group_has_unabsorbed_bankruptcy_loss`'s own comment at `:19267-19269` says the side
    // mode byte was deliberately dropped as a term, because a single holder on a DrainOnly
    // side must not be able to freeze every domain (`:19235-19253`).
    assert_ne!(
        market.markets[0].engine.asset.mode_long, 0,
        "precondition: the side mode byte is still non-Normal"
    );
    assert_eq!(
        market.header.bankruptcy_hlock_active, 0,
        "the group hlock is RELEASED — which is what this test is named for. \
         `try_clear_bankruptcy_hlock_if_healthy` (:19282-19296) runs inside the liquidation's \
         own refresh (:13921, reached from :17626); every header conjunct it reads is zero and \
         `group_has_unabsorbed_bankruptcy_loss` (:19261-19280) finds no pending domain-loss \
         barrier"
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
    // And the permissionless crank that anyone can pay for is idempotent over the released
    // state: it succeeds and leaves the hlock down. `try_clear_…` (:19282-19296)
    // early-returns `Ok(())` at :19283-19285 when the flag is already 0, so a second caller
    // can neither re-latch it nor fail on it.
    assert_eq!(
        refresh.map(|_| ()),
        Ok(()),
        "the permissionless refresh crank still succeeds after the exit"
    );
    assert_eq!(
        market.header.bankruptcy_hlock_active, 0,
        "and the hlock stays released"
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        0,
        "with no exposure left to re-arm it"
    );
}

/// Same measurement, but with the EXACT risk knobs the percolator-launch wizard
/// ships for live devnet markets (percolator-launch/app/hooks/useCreateMarket.ts
/// v17InitArgs): minNonzeroMmReq = 1_000_000 atoms (= 1.00 USDC at 6dp),
/// minNonzeroImReq = 2_000_000, maintenanceFeePerSlot = 0, maxAbsFundingE9PerSlot = 0.
///
/// The headline this test exists to produce: with those knobs, holding one quantum of
/// residual exposure — and with it the DrainOnly side the wrapper's hlock hangs off — costs
/// exactly `min_nonzero_mm_req` of equity, i.e. 1.00 USDC. The bps term is 0 here (1 atom of
/// notional at maintenance_margin_bps = 1_000 floors to 0), so the config floor IS the
/// price. Asserted below as the boundary between the three rows.
///
/// Until AS-04 this test asserted NOTHING — it printed three rows and passed. On the
/// pre-AS-03 fixture it printed `liquidate=Err(NonProgress) oi_after=1` for ALL three,
/// including the 999_999 row that is below the floor, because `unilateral_close_capacity`
/// (`:919-925`) was 0 on the one-sided book — so the file's central number, the cost of the
/// grief, was being reported as "unbounded" when it is 1.00 USDC.
#[test]
fn devnet_parameterised_holdout_cost() {
    const OI: u128 = 1;
    // The wizard's `minNonzeroMmReq`, and (bps term being 0 at this size) the exact equity a
    // holdout must keep to stay unliquidatable.
    const DEVNET_MIN_NONZERO_MM_REQ: u128 = 1_000_000;
    for capital in [999_999u128, 1_000_000, 2_000_000] {
        let (mut header, mut markets, mut acct) = drain_only_holdout(OI, capital);
        header.config.min_nonzero_mm_req = V16PodU128::new(DEVNET_MIN_NONZERO_MM_REQ);
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

        // THE ASSERTION, and the file's headline number. Equity is the account's capital, so
        // the pre-call deficit at :13934-13938 is
        // `DEVNET_MIN_NONZERO_MM_REQ.saturating_sub(capital)` and the gate at :17637-17638
        // flips at exactly the floor: 999_999 is removable, 1_000_000 is not.
        if capital < DEVNET_MIN_NONZERO_MM_REQ {
            assert_eq!(
                liq.map(|o| o.closed_q),
                Ok(OI),
                "one atom below the devnet maintenance floor the holdout IS removable"
            );
            assert_eq!(
                market.markets[0].engine.asset.oi_eff_long_q.get(),
                0,
                "and the exposure is gone"
            );
        } else {
            assert_eq!(
                liq.map(|o| o.closed_q),
                Err(V16Error::NonProgress),
                "at or above 1.00 USDC of equity the deficit is 0 and :17637-17638 refuses — \
                 that, exactly, is the price of the grief on a wizard-configured devnet market"
            );
            assert_eq!(
                market.markets[0].engine.asset.oi_eff_long_q.get(),
                OI,
                "and the exposure survives"
            );
        }
        // As in `minimum_capital_to_sustain_the_holdout`: the refusal still releases the
        // group hlock, because :17626's refresh calls :13921 before the deficit gate. The
        // grief buys a position nobody can close, NOT a frozen group.
        assert_eq!(
            market.header.bankruptcy_hlock_active, 0,
            "the devnet-parameterised holdout does not hold the group hostage either"
        );
    }
}
