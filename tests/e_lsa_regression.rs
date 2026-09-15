//! Regression test for E-LSA — the market-header byte `loss_stale_active` must carry the touched
//! asset's CLOCK-LAG fact, never K/F settlement-cohort membership.
//!
//! `bf2fda46` ("Adopt upstream 92ed4a1a: track K/F settlement cohorts by generation (layout 18)")
//! routed the four market-header writers through `asset_is_loss_stale_at_slot`, whose first two
//! disjuncts are `stale_account_count_{long,short} != 0` — which `kernel_mark_kf_stale_cohorts`
//! reuses as the K/F cohort counter and sets to `stored_pos_count_side` on EVERY K/F move. The
//! group byte therefore stood for the whole interval between a price move and the LAST account's
//! crank, on a Live market with no stale and no lagging asset, and the wrapper's LP/insurance
//! custody gate `live_domain_withdraw_health_or_shutdown_view` refused `WithdrawBackingBucket`
//! with `Custom(21)` `EngineLockActive`.
//!
//! The fix splits the two facts: `asset_is_loss_stale_at_slot` (asset-local, cohort-aware) is
//! unchanged and still gates risk transfer; the header writers use
//! `asset_header_loss_stale_summary_at_slot` (clock lag only), which is what every market-wide
//! consumer — including the wrapper's own asset-local twin `asset_local_loss_stale_view` — is
//! written against.
//!
//! These tests assert the FIXED behaviour. Each one FAILS at `dc01e542` (the base) — see
//! `verify/poc/E-LSA/` for the PoC in its defect-asserting form.

use percolator::{v16_domain_count_for_market_slots, POS_SCALE};
use percolator::{
    AssetLifecycleV16, EngineAssetSlotV16Account, Market, MarketGroupV16HeaderAccount,
    MarketGroupV16ViewMut, PortfolioAccountV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, TradeRequestV16, V16Config, V16PodU64,
};

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

/// Verbatim from `tests/v16_spec_tests.rs::market_fixture`.
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
    // (the one deviation from the verbatim fixture: an iterator instead of `markets[i]`, so this
    // file adds no `clippy::needless_range_loop` finding of its own)
    for (i, market) in markets.iter_mut().enumerate() {
        header
            .activate_empty_asset_slot_not_atomic(
                i as u32,
                &mut market.engine,
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

/// Verbatim from `tests/v16_spec_tests.rs::account_fixture`.
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

/// Faithful host mirror of the wrapper's asset-local loss-stale test,
/// `percolator-prog d562e75d:src/v16_program.rs:6842-6857`
/// (byte-identical at upstream `aeyakovenko/percolator-prog 2b1d025c:6009-6022`):
///
/// ```text
/// matches!(asset.lifecycle, ACTIVE | DRAIN_ONLY)
///     && asset.slot_last.get() < group.header.current_slot.get()
///     && asset_local_has_position_or_loss_state_view(group, asset_index)
/// ```
///
/// The `has_position_or_loss_state` term is passed in by the caller below (the market in this PoC
/// always has live OI on both assets, so it is `true`); what matters here is the CONJOINED
/// clock-lag term, which is exactly the pre-`bf2fda46` engine predicate.
fn wrapper_asset_local_loss_stale_view(
    lifecycle: AssetLifecycleV16,
    asset_slot_last: u64,
    group_current_slot: u64,
    has_position_or_loss_state: bool,
) -> bool {
    matches!(
        lifecycle,
        AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly
    ) && asset_slot_last < group_current_slot
        && has_position_or_loss_state
}

/// Faithful host mirror of the group-level disjunct of the wrapper's LP/insurance custody gate,
/// `percolator-prog d562e75d:src/v16_program.rs:6823-6832`
/// (byte-identical at upstream `aeyakovenko/percolator-prog 2b1d025c:5981-5990`):
///
/// ```text
/// if group.header.bankruptcy_hlock_active != 0
///     || group.header.threshold_stress_active != 0
///     || group.header.loss_stale_active != 0
///     || group.header.recovery_reason...is_some()
/// { return Err(PercolatorError::EngineLockActive.into()); }   // Custom(21)
/// ```
///
/// Returns `Err("EngineLockActive")` with the name of the disjunct that fired.
fn wrapper_group_withdraw_gate(header: &MarketGroupV16HeaderAccount) -> Result<(), &'static str> {
    if header.bankruptcy_hlock_active != 0 {
        return Err("EngineLockActive(bankruptcy_hlock_active)");
    }
    if header.threshold_stress_active != 0 {
        return Err("EngineLockActive(threshold_stress_active)");
    }
    if header.loss_stale_active != 0 {
        return Err("EngineLockActive(loss_stale_active)");
    }
    if header
        .recovery_reason
        .try_to_runtime()
        .expect("recovery_reason decodes")
        .is_some()
    {
        return Err("EngineLockActive(recovery_reason)");
    }
    Ok(())
}

/// The E-LSA PoC scenario, asserting the FIXED behaviour: the LP's custody withdrawal goes through
/// on a Live market whose withdraw-target asset is Active, current and fully settled, while the
/// K/F cohort fact on the OTHER asset is preserved and still gates risk transfer.
#[test]
fn e_lsa_header_byte_is_clear_while_the_withdraw_asset_is_clean() {
    const ASSET_LP_WITHDRAWS_FROM: usize = 0;
    const ASSET_WITH_AN_UNCRANKED_ACCOUNT: usize = 1;

    let (mut header, mut markets) = market_fixture(2, 100);
    let mut a_header = account_fixture(2, 221); // long on both assets
    let mut b_header = account_fixture(2, 222); // short on asset 0
    let mut c_header = account_fixture(2, 223); // short on asset 1 — never cranked
    let mut d_header = account_fixture(2, 224); // entrant used for the risk-increase probe

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut a_header);
    let mut b = PortfolioV16ViewMut::new(&mut b_header);
    let mut c = PortfolioV16ViewMut::new(&mut c_header);
    let mut d = PortfolioV16ViewMut::new(&mut d_header);

    for account in [&mut a, &mut b, &mut c, &mut d] {
        market.deposit_not_atomic(account, 1_000_000).unwrap();
    }

    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut a,
            &mut b,
            TradeRequestV16 {
                asset_index: ASSET_LP_WITHDRAWS_FROM,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut a,
            &mut c,
            TradeRequestV16 {
                asset_index: ASSET_WITH_AN_UNCRANKED_ACCOUNT,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    market
        .accrue_asset_to_not_atomic(ASSET_LP_WITHDRAWS_FROM, 2, 101, 0, true)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(ASSET_WITH_AN_UNCRANKED_ACCOUNT, 3, 101, 0, true)
        .unwrap();
    market.markets[ASSET_WITH_AN_UNCRANKED_ACCOUNT]
        .engine
        .asset
        .raw_oracle_target_price = V16PodU64::new(101);
    market
        .accrue_asset_to_not_atomic(ASSET_LP_WITHDRAWS_FROM, 3, 102, 0, true)
        .unwrap();
    market.markets[ASSET_LP_WITHDRAWS_FROM]
        .engine
        .asset
        .raw_oracle_target_price = V16PodU64::new(102);

    market.full_account_refresh_not_atomic(&mut b).unwrap();
    market.full_account_refresh_not_atomic(&mut a).unwrap();

    let withdraw_asset = market.markets[ASSET_LP_WITHDRAWS_FROM]
        .engine
        .asset
        .try_to_runtime()
        .unwrap();
    let other_asset = market.markets[ASSET_WITH_AN_UNCRANKED_ACCOUNT]
        .engine
        .asset
        .try_to_runtime()
        .unwrap();
    let current_slot = market.header.current_slot.get();

    // preconditions the fix does not change
    assert_eq!(market.header.mode, 0, "market is Live");
    assert_eq!(withdraw_asset.lifecycle, AssetLifecycleV16::Active);
    assert_eq!(withdraw_asset.slot_last, current_slot, "no clock lag");
    assert_eq!(withdraw_asset.stale_account_count_long, 0);
    assert_eq!(withdraw_asset.stale_account_count_short, 0);
    assert!(!wrapper_asset_local_loss_stale_view(
        withdraw_asset.lifecycle,
        withdraw_asset.slot_last,
        current_slot,
        true
    ));

    // (1) the group byte is clear and the LP's custody withdrawal is admitted
    assert_eq!(
        market.header.loss_stale_active, 0,
        "the header byte must carry the clock fact, and no asset is clock-lagged"
    );
    assert_eq!(
        wrapper_group_withdraw_gate(market.header),
        Ok(()),
        "WithdrawBackingBucket must no longer be refused with Custom(21)"
    );

    // (2) the audit fact is NOT hidden: the cohort counter still holds the un-cranked account
    assert_eq!(
        other_asset.stale_account_count_short, 1,
        "the K/F cohort counter must still record the un-cranked account"
    );
    assert_eq!(other_asset.stale_account_count_long, 0);

    // (3) and it still gates risk transfer on the asset that owes settlement
    let rejected = market.execute_trade_with_fee_loss_stale_scoped_not_atomic(
        &mut d,
        &mut a,
        TradeRequestV16 {
            asset_index: ASSET_WITH_AN_UNCRANKED_ACCOUNT,
            size_q: signed_q(POS_SCALE),
            exec_price: 101,
            fee_bps: 0,
        },
        true,
    );
    assert_eq!(
        rejected,
        Err(percolator::V16Error::LockActive),
        "an open K/F cohort must still block risk increase on its own asset"
    );

    market.validate_shape().unwrap();
}

/// One price move on a single-asset market: the group byte must be clear as soon as the asset sits
/// on the market clock, even though both sides still owe the K/F cohort.
#[test]
fn e_lsa_one_price_move_does_not_freeze_custody() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 225);
    let mut short_header = account_fixture(1, 226);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    let outcome = market
        .accrue_asset_to_not_atomic(0, 2, 101, 0, true)
        .unwrap();
    market.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(101);
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();

    assert_eq!(asset.slot_last, market.header.current_slot.get());
    assert_eq!(
        (
            asset.stale_account_count_long,
            asset.stale_account_count_short
        ),
        (1, 1),
        "the cohort counter still opens on every K/F move — the audit fact is untouched"
    );
    assert_eq!(
        market.header.loss_stale_active, 0,
        "no clock lag, so the market-wide byte must be clear"
    );
    assert!(
        !outcome.loss_stale_after,
        "AccrueAssetOutcomeV16::loss_stale_after reports the same clock fact as the header byte \
         (and as the wrapper's own host mirror, which never left `asset.slot_last < now_slot`)"
    );
    assert_eq!(wrapper_group_withdraw_gate(market.header), Ok(()));

    market.validate_shape().unwrap();
}

/// The byte must still fire on the fact it is for: a genuinely clock-lagged asset.
#[test]
fn e_lsa_header_byte_still_fires_on_a_clock_lagged_asset() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 227);
    let mut short_header = account_fixture(1, 228);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    // `accrue_asset_to_not_atomic` commits ONE bounded segment, so asking for slot 3 from
    // `slot_last == 1` leaves the asset at slot 2 under a market clock of 3.
    let outcome = market
        .accrue_asset_to_not_atomic(0, 3, 101, 0, true)
        .unwrap();
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert!(
        asset.slot_last < market.header.current_slot.get(),
        "fixture precondition: the asset really is clock-lagged"
    );
    assert_eq!(
        market.header.loss_stale_active, 1,
        "a clock-lagged asset must still set the market-wide byte"
    );
    assert!(outcome.loss_stale_after);
    assert_eq!(
        wrapper_group_withdraw_gate(market.header),
        Err("EngineLockActive(loss_stale_active)"),
        "and the wrapper's custody gate must still refuse while an asset lags the clock"
    );

    market.validate_shape().unwrap();
}
