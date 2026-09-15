//! Regression tests for fix/Q (verify-loop items C-S-20, C-S-20b, C-S-10b).
//!
//! These assert the FIXED behaviour. The original PoCs
//! (`verify/poc/C-S-20/poc_CS20.rs`, `verify/poc/C-S-20b/poc_CS20b.rs`,
//! `verify/poc/C-S-10/poc_C_S_10.rs` part (c)) assert the DEFECT and therefore
//! fail against this tree — that flip is the measurement.
//!
//! The governing rule in all three is the same: a counterparty backing bucket
//! that is `Fresh` with `expiry_slot <= current_slot` is LAPSED, and
//! `spec.md:562` ("if a counterparty backing bucket expires ... the lien becomes
//! `Impaired`") plus the expiry rule at `spec.md:342-357` ("liened backing in an
//! expiring bucket MUST NOT cause `available_backing_num` underflow or
//! inflation ... on expiry the engine MUST [refresh | atomically expire | route
//! to recovery] before any credit-rate read") make its liened principal a
//! forfeit to the junior residual pool — never an un-pledge back to the
//! provider, and never withdrawable.
//!
//! Fixtures are the PoC fixtures, which are in turn copied from
//! `tests/v16_spec_tests.rs` (`ids` / `market_fixture` / `account_fixture` /
//! `signed_q` verbatim).

use percolator::{
    AssetStateV16Account, AutoCrankOutcomeV16, AutoCrankPlanV16, AutoCrankResultV16,
    AutoCrankWorkV16, BackingBucketStatusV16, EngineAssetSlotV16Account, Market,
    MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PermissionlessProgressOutcomeV16,
    PortfolioAccountV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, TradeRequestV16, V16Config, V16PodU64,
    v16_domain_count_for_market_slots,
};
use percolator::{BOUND_SCALE, POS_SCALE};

// ---------------------------------------------------------------------------
// fixture helpers, verbatim from tests/v16_spec_tests.rs
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

fn trade(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    long: &mut PortfolioV16ViewMut<'_>,
    short: &mut PortfolioV16ViewMut<'_>,
    request: TradeRequestV16,
) {
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(long, short, request, true)
        .unwrap();
}

// ---------------------------------------------------------------------------
// shared constants / observers
// ---------------------------------------------------------------------------

const ASSET: usize = 0;
/// asset-0 SHORT domain = `insurance_domain_index(0, opposite_side(Long))`.
const CP_DOMAIN: usize = 1;
const BACKING_PRINCIPAL: u128 = 100_000;
const OPEN_Q: u128 = 1_000 * POS_SCALE;
const INCREASE_Q: u128 = 50 * POS_SCALE;
/// social-loss target driving a loss larger than the whole positive face, so
/// the burn walks past `source_claim_unliened_num` into the LIENED face.
const B_TARGET: u128 = 6_000_000_000_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Bucket {
    status: BackingBucketStatusV16,
    expiry: u64,
    valid: u128,
    fresh: u128,
    impaired: u128,
}

fn bucket_of(market: &MarketGroupV16ViewMut<'_, u64>) -> Bucket {
    let b = market.markets[ASSET]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    Bucket {
        status: b.status,
        expiry: b.expiry_slot,
        valid: b.valid_liened_backing_num,
        fresh: b.fresh_unliened_backing_num,
        impaired: b.impaired_liened_backing_num,
    }
}

// ===========================================================================
// PART 1 — Q-Live: C-S-20, `burn_account_source_lien_face_not_atomic`
// ===========================================================================

struct LiveFixture {
    header: MarketGroupV16HeaderAccount,
    markets: Vec<Market<u64>>,
    long_header: PortfolioAccountV16Account,
    /// `source_lien_counterparty_backing_num` standing on the bucket just
    /// before the burn: the amount whose destination the fix decides.
    liened_backing_num: u128,
}

/// The C-S-20 fixture, parameterized on the bucket's `expiry_slot` and on how
/// far the clock is advanced, so the same construction yields both the LAPSED
/// state (`expiry_slot <= now`) and the still-valid state used as the liveness
/// control.
fn live_fixture(expiry_slot: u64, advance_to: u64) -> LiveFixture {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(5_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 10);
    let mut short_header = account_fixture(1, 11);

    let liened_backing_num;
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);

        market
            .deposit_fresh_counterparty_backing_not_atomic(
                CP_DOMAIN,
                BACKING_PRINCIPAL,
                expiry_slot,
            )
            .unwrap();
        market.deposit_not_atomic(&mut long, 52_501).unwrap();
        market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
        trade(
            &mut market,
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: ASSET,
                size_q: signed_q(OPEN_Q),
                exec_price: 100,
                fee_bps: 0,
            },
        );

        market
            .set_asset_raw_oracle_target_not_atomic(ASSET, 105)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(ASSET, 2, 105, 0, true)
            .unwrap();
        market.full_account_refresh_not_atomic(&mut short).unwrap();
        market.full_account_refresh_not_atomic(&mut long).unwrap();
        assert_eq!(long.header.pnl.get(), 5_000);

        // risk-increasing trade: IM is met out of the source claim, which LIENS
        // the bucket's principal while it is still fresh and unlapsed.
        trade(
            &mut market,
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: ASSET,
                size_q: signed_q(INCREASE_Q),
                exec_price: 105,
                fee_bps: 0,
            },
        );
        let lien = long.header.source_domains[0];
        assert_eq!(lien.domain.get() as usize, CP_DOMAIN);
        liened_backing_num = lien.source_lien_counterparty_backing_num.get();
        assert!(liened_backing_num > 0, "counterparty-backed lien expected");
        assert_eq!(
            lien.source_lien_insurance_backing_num.get(),
            0,
            "counterparty leg only: the insurance leg's mode gate must not be what runs"
        );

        for slot in 3..=advance_to {
            market
                .accrue_asset_to_not_atomic(ASSET, slot, 105, 0, true)
                .unwrap();
        }
        let b = bucket_of(&market);
        assert_eq!(b.status, BackingBucketStatusV16::Fresh);
        assert_eq!(b.valid, liened_backing_num);
        assert_eq!(b.impaired, 0);

        let mut asset = market.markets[ASSET].engine.asset.try_to_runtime().unwrap();
        asset.b_long_num = B_TARGET;
        market.markets[ASSET].engine.asset = AssetStateV16Account::from_runtime(&asset);
        long.header.health_cert.valid = 0;
    }

    LiveFixture {
        header,
        markets,
        long_header,
        liened_backing_num,
    }
}

/// LAPSED: `expiry_slot (4) <= current_slot (5)`, nobody ran tag 89.
fn lapsed_live_fixture() -> LiveFixture {
    live_fixture(4, 5)
}

/// STILL VALID: `expiry_slot (50) > current_slot (5)`. Liveness control.
fn unexpired_live_fixture() -> LiveFixture {
    live_fixture(50, 5)
}

fn drive_loss_via_auto_crank(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    long: &mut PortfolioV16ViewMut<'_>,
) -> AutoCrankResultV16 {
    let now = market.header.current_slot.get();
    market
        .permissionless_auto_crank_not_atomic(
            long,
            AutoCrankWorkV16 {
                now_slot: now,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the Live loss must still settle -- the fix must not deadlock the burn")
}

fn chunk_loss(result: &AutoCrankResultV16) -> u128 {
    assert_eq!(
        result.selected,
        AutoCrankPlanV16::SettleBChunk { asset_index: ASSET },
        "the public crank still selects the B chunk"
    );
    match result.outcome {
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountBChunk(chunk)) => {
            chunk.loss
        }
        ref other => panic!("expected an AccountBChunk outcome, got {other:?}"),
    }
}

/// C-S-20 FIXED: the Live burn of a lapsed `Fresh` bucket applies the canonical
/// expiry rule first, so the liened principal is FORFEITED to the junior pool
/// instead of landing in `fresh_unliened` where wrapper tag 50 could pay it out.
#[test]
fn q_live_burn_on_lapsed_bucket_forfeits_principal_instead_of_returning_it() {
    let mut fx = lapsed_live_fixture();
    let released = fx.liened_backing_num;
    let mut market = MarketGroupV16ViewMut::new(&mut fx.header, &mut fx.markets);
    let mut long = PortfolioV16ViewMut::new(&mut fx.long_header);

    let before = bucket_of(&market);
    let src_fresh_before = market.header.source_fresh_backing_total_num.get();
    assert!(
        before.expiry <= market.header.current_slot.get(),
        "fixture must be LAPSED: expiry {} vs now {}",
        before.expiry,
        market.header.current_slot.get()
    );

    // LIVENESS: the loss still settles.
    let result = drive_loss_via_auto_crank(&mut market, &mut long);
    let loss = chunk_loss(&result);
    assert!(loss > 0, "the burn must still recognize the loss");

    let after = bucket_of(&market);
    let src_fresh_after = market.header.source_fresh_backing_total_num.get();
    println!("[Q-live lapsed] chunk.loss                   = {loss}");
    println!("[Q-live lapsed] lien on the lapsed bucket    = {released}");
    println!("[Q-live lapsed] bucket.status                = {:?}", after.status);
    println!("[Q-live lapsed] valid_liened    {} -> {}", before.valid, after.valid);
    println!("[Q-live lapsed] fresh_unliened  {} -> {}", before.fresh, after.fresh);
    println!(
        "[Q-live lapsed] impaired_liened {} -> {}",
        before.impaired, after.impaired
    );
    println!(
        "[Q-live lapsed] source_fresh_backing_total_num {src_fresh_before} -> {src_fresh_after}"
    );

    assert_eq!(after.valid, 0, "the lien is gone either way");
    assert_eq!(
        after.fresh, 0,
        "FIXED: the lapsed bucket's principal is NOT returned to fresh_unliened; \
         the expiry rule forfeits the bucket wholesale"
    );
    assert!(
        after.fresh <= before.fresh,
        "FIXED: the burn must never INFLATE unliened backing on a lapsed bucket \
         (spec.md:342-357)"
    );
    assert_ne!(
        after.status,
        BackingBucketStatusV16::Fresh,
        "FIXED: a lapsed bucket does not stay Fresh across the burn, so the tag-50 \
         withdraw gate no longer sees a Fresh bucket"
    );
    assert_eq!(
        src_fresh_before - src_fresh_after,
        before.fresh + released,
        "FIXED: the senior term drops by unliened+liened, i.e. residual() (the junior \
         payout pool) GAINS exactly the forfeited principal"
    );

    // the money leg: wrapper tag 50 is refused on the forfeited principal.
    let w = market.withdraw_fresh_counterparty_backing_not_atomic(CP_DOMAIN, released / BOUND_SCALE);
    println!("[Q-live lapsed] tag50 withdraw(released) -> {w:?}");
    assert!(
        w.is_err(),
        "FIXED: the provider cannot withdraw the forfeited principal: {w:?}"
    );
    let w_all = market
        .withdraw_fresh_counterparty_backing_not_atomic(CP_DOMAIN, BACKING_PRINCIPAL);
    println!("[Q-live lapsed] tag50 withdraw(whole principal) -> {w_all:?}");
    assert!(w_all.is_err(), "nothing in the lapsed bucket is withdrawable");
}

/// The two crank orderings now CONVERGE: burn-first (the defect ordering) ends
/// in exactly the state expire-first (wrapper tag 89) produces.
#[test]
fn q_live_burn_first_and_expire_first_orderings_converge() {
    let burn_first = {
        let mut fx = lapsed_live_fixture();
        let mut market = MarketGroupV16ViewMut::new(&mut fx.header, &mut fx.markets);
        let mut long = PortfolioV16ViewMut::new(&mut fx.long_header);
        drive_loss_via_auto_crank(&mut market, &mut long);
        (
            bucket_of(&market),
            market.header.source_fresh_backing_total_num.get(),
            market.header.vault.get(),
        )
    };
    let expire_first = {
        let mut fx = lapsed_live_fixture();
        let mut market = MarketGroupV16ViewMut::new(&mut fx.header, &mut fx.markets);
        let mut long = PortfolioV16ViewMut::new(&mut fx.long_header);
        let now = market.header.current_slot.get();
        market
            .expire_source_backing_bucket_not_atomic(CP_DOMAIN, now)
            .expect("tag 89 is permissionless and legal here");
        // LIVENESS of the LIEN-1 impaired arm (:2877-2898): the burn must still
        // settle against an ALREADY-Impaired bucket.
        let after = market.permissionless_auto_crank_not_atomic(
            &mut long,
            AutoCrankWorkV16 {
                now_slot: now,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        );
        println!("[Q-live expire-first] crank after expiry -> {after:?}");
        after.expect("LIEN-1 impaired arm: the burn must settle on an Impaired bucket");
        (
            bucket_of(&market),
            market.header.source_fresh_backing_total_num.get(),
            market.header.vault.get(),
        )
    };
    println!("[Q-live converge] burn-first  = {burn_first:?}");
    println!("[Q-live converge] expire-first= {expire_first:?}");
    assert_eq!(
        burn_first, expire_first,
        "FIXED: the crank ordering no longer decides where the lapsed principal lands"
    );
}

/// LIVENESS control: on a bucket that is still within its expiry the burn's
/// terminal release is unchanged — the principal returns to the provider's
/// unliened pool exactly as `prepare_counterparty_lien_release_delta` and spec
/// property 39 require.
#[test]
fn q_live_burn_on_unexpired_bucket_still_returns_principal_to_provider() {
    let mut fx = unexpired_live_fixture();
    let released = fx.liened_backing_num;
    let mut market = MarketGroupV16ViewMut::new(&mut fx.header, &mut fx.markets);
    let mut long = PortfolioV16ViewMut::new(&mut fx.long_header);

    let before = bucket_of(&market);
    let src_fresh_before = market.header.source_fresh_backing_total_num.get();
    assert!(
        before.expiry > market.header.current_slot.get(),
        "control fixture must be UNEXPIRED: expiry {} vs now {}",
        before.expiry,
        market.header.current_slot.get()
    );

    let result = drive_loss_via_auto_crank(&mut market, &mut long);
    let loss = chunk_loss(&result);
    assert!(loss > 0);

    let after = bucket_of(&market);
    let src_fresh_after = market.header.source_fresh_backing_total_num.get();
    println!("[Q-live unexpired] chunk.loss = {loss}, lien = {released}");
    println!("[Q-live unexpired] status {:?} -> {:?}", before.status, after.status);
    println!("[Q-live unexpired] valid   {} -> {}", before.valid, after.valid);
    println!("[Q-live unexpired] fresh   {} -> {}", before.fresh, after.fresh);
    println!("[Q-live unexpired] impaired {} -> {}", before.impaired, after.impaired);

    assert_eq!(after.valid, 0);
    assert_eq!(
        after.fresh,
        before.fresh + released,
        "LIVENESS: an unexpired bucket still un-pledges valid_liened -> fresh_unliened"
    );
    assert_eq!(after.impaired, 0, "nothing is forfeited on an unexpired bucket");
    assert_eq!(after.status, BackingBucketStatusV16::Fresh);
    assert_eq!(
        src_fresh_after, src_fresh_before,
        "the senior term is value-neutral for an unexpired release"
    );
    let w = market.withdraw_fresh_counterparty_backing_not_atomic(CP_DOMAIN, released / BOUND_SCALE);
    println!("[Q-live unexpired] tag50 withdraw(released) -> {w:?}");
    w.expect("LIVENESS: an unexpired bucket's unliened principal is still withdrawable");
}

/// Same fix via wrapper tag 48 `SyncMaintenanceFee`
/// (`sync_account_fee_to_slot_not_atomic`), the second permissionless route
/// into the same burn.
#[test]
fn q_live_tag48_sync_maintenance_fee_also_forfeits() {
    let mut fx = lapsed_live_fixture();
    let released = fx.liened_backing_num;
    let mut market = MarketGroupV16ViewMut::new(&mut fx.header, &mut fx.markets);
    let mut long = PortfolioV16ViewMut::new(&mut fx.long_header);

    let before = bucket_of(&market);
    let now = market.header.current_slot.get();
    market
        .sync_account_fee_to_slot_not_atomic(&mut long, now, 0)
        .expect("tag 48 must still settle the B chunk on a lapsed bucket");
    let after = bucket_of(&market);
    println!(
        "[Q-live tag48] status={:?} valid={} fresh {}->{} impaired={}",
        after.status, after.valid, before.fresh, after.fresh, after.impaired
    );
    assert_eq!(after.valid, 0);
    assert_eq!(after.fresh, 0, "FIXED: nothing is returned to the provider");
    assert_ne!(after.status, BackingBucketStatusV16::Fresh);
    assert!(
        released > 0 && after.fresh < before.fresh + released,
        "FIXED: the released lien did not land in fresh_unliened"
    );
}
