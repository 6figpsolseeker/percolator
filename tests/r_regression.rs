//! Regression test for FIX item R (verify-loop row C-S-04 = composition C-X-1).
//!
//! Derived from `verify/poc/C-S-04/poc_CS04.rs`, re-asserted for the FIXED
//! behaviour. The PoC file itself now FAILS against this tree (3 failed) and its
//! `#[ignore]`d probe, which asserts the corrected behaviour, now PASSES — that
//! pair is the negative control recorded in `verify/fixes/R.md`.
//!
//! THE DEFECT (at `origin/main` = `2c38570a`, byte-identical at `av`)
//! -----------------------------------------------------------------
//! `account_source_realizable_support` credited the account-side mirror
//! `source_lien_effective_reserved` into `support` with no currency test at all;
//! the only validator in the function (`validate_source_domain_ledger_current`)
//! is reached on the UNLIENED branch, and even there rejects only a
//! `Fresh`-and-lapsed bucket, never an already-`Impaired` one. So after any third
//! party ran the permissionless market-side expiry (wrapper tag 89
//! `ExpireBackingBucket`), the holder kept certifying on principal the market had
//! already written off — and because that phantom equity zeroed
//! `certified_liq_deficit`, `liquidate_account_not_atomic` refused with
//! `NonProgress`. Impairment BLOCKED the liquidation `spec.md:562` ( = `av:657`)
//! names as a required resolution, for as long as the leg stayed open (the only
//! account-side normalizer skips a domain with open exposure).
//!
//! THE FIX
//! -------
//! `account_source_realizable_support` drops the COUNTERPARTY share of the
//! account-side lien term whenever the domain's backing bucket is not
//! `Fresh`-and-unexpired. The share is exact, not apportioned — it is the same
//! `source_lien_counterparty_backing_num / BOUND_SCALE` that the account-side
//! clearer `V16Core::prepare_account_counterparty_lien_impairment` subtracts —
//! so valuation now agrees IN ADVANCE with what the clearer will book. The gate
//! yields zero rather than `Err(Stale)`, because an uncertifiable account is an
//! un-liquidatable account.
//!
//! WHAT THIS FILE PINS
//! -------------------
//!  1. after a third-party expiry the certificate tells the truth (`0`, not the
//!     phantom) and the underwater account IS liquidatable (`Ok`);
//!  2. the same holds with no third party at all (holder-only, two cranks);
//!  3. the withdraw and convert refusals are UNCHANGED (no new extraction);
//!  4. the flat-account normalizer still clears the lien, and the certificate is
//!     now INVARIANT across it;
//!  5. LIVENESS: a `Fresh`, unexpired bucket still supports in full, and an
//!     insurance-backed lien still supports in full even when the domain's
//!     counterparty bucket is stone dead.

use percolator::{
    BackingBucketStatusV16, BackingBucketV16, BackingBucketV16Account, EngineAssetSlotV16Account,
    InsuranceCreditReservationV16, InsuranceCreditReservationV16Account, LiquidationRequestV16,
    Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PermissionlessCrankActionV16,
    PermissionlessCrankRequestV16, PermissionlessProgressOutcomeV16, PortfolioAccountV16Account,
    PortfolioV16ViewMut, ProvenanceHeaderV16, ProvenanceHeaderV16Account, SourceCreditStateV16,
    SourceCreditStateV16Account, TradeRequestV16, V16Config, V16Error, V16PodI128, V16PodU128,
    V16PodU32, V16PodU64,
};
use percolator::{BOUND_SCALE, CREDIT_RATE_SCALE, POS_SCALE};

/// Positive PnL of the source-backed winner, all of it attributed to domain 0.
const CLAIM: u128 = 100;
/// Risk-increasing position the winner opens against the source credit.
const POSITION_Q: u128 = 10 * POS_SCALE;
/// Backing bucket lifetime.
const EXPIRY_SLOT: u64 = 100;
/// Effective backing the IM path reserves for `POSITION_Q` at price 1 with
/// `initial_margin_bps = 10_000`. Before the fix this was the PHANTOM support.
const LIEN_EFFECTIVE: u128 = 10;
/// Maintenance requirement for `POSITION_Q` at price 1 with
/// `maintenance_margin_bps = 5_000`.
const MAINTENANCE_REQ: u128 = 5;

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn signed_q(q: u128) -> i128 {
    i128::try_from(q).unwrap()
}

fn account_fixture(seed: u8) -> PortfolioAccountV16Account {
    let (market_id, _, owner) = ids();
    let header = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
        market_id, [seed; 32], owner,
    ));
    let mut account = PortfolioAccountV16Account::default();
    account.init_empty_in_place(header).unwrap();
    account
}

/// Identical to the PoC fixture: IM stays at 10_000 bps so the IM path mints
/// exactly `LIEN_EFFECTIVE` atoms of effective backing; MM drops to 5_000 bps so
/// the TRUE maintenance shortfall after the forfeit (`MAINTENANCE_REQ`) is
/// strictly inside it — which is what makes assertion (1) a real deferral rather
/// than a tie. The finding (and this fix) also reproduce at the untouched
/// defaults; see `verify/items/C-S-04.md` §5.
fn r_market_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.maintenance_margin_bps = 5_000;
    cfg.max_price_move_bps_per_slot = 500;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 1, 1)
        .unwrap();
    {
        let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.validate_shape().unwrap();
    }
    (header, markets)
}

/// Market + winner + counterparty, winner holding an OPEN risk-increasing
/// position whose initial margin is entirely carried by an engine-minted source
/// credit lien on a still-`Fresh` backing bucket. `now_slot` is where the wall
/// clock is left: `EXPIRY_SLOT` puts the bucket at its expiry, anything smaller
/// leaves it live.
fn open_source_backed_position(
    long_seed: u8,
    short_seed: u8,
    now_slot: u64,
) -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
    PortfolioAccountV16Account,
) {
    let (mut header, mut markets) = r_market_fixture();
    let mut long_header = account_fixture(long_seed);
    let mut short_header = account_fixture(short_seed);
    let claim_num = CLAIM * BOUND_SCALE;

    long_header.pnl = V16PodI128::new(CLAIM as i128);
    long_header.source_domains[0].domain = V16PodU32::new(0);
    long_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    long_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(CLAIM);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(CLAIM);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
    header.vault = V16PodU128::new(CLAIM + header.vault.get());
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            positive_claim_bound_num: claim_num,
            exact_positive_claim_num: claim_num,
            fresh_reserved_backing_num: claim_num,
            credit_rate_num: CREDIT_RATE_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[0].engine.backing_long = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id: 1,
        fresh_unliened_backing_num: claim_num,
        expiry_slot: EXPIRY_SLOT,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POSITION_Q),
                    exec_price: 1,
                    fee_bps: 0,
                },
                true,
            )
            .expect("risk-increasing trade must mint the IM source-credit lien");
    }
    assert_eq!(long_header.capital.get(), 0);
    assert_eq!(
        long_header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        LIEN_EFFECTIVE
    );
    assert_eq!(
        long_header.source_domains[0]
            .source_lien_counterparty_backing_num
            .get(),
        LIEN_EFFECTIVE * BOUND_SCALE,
        "the lien is COUNTERPARTY-backed; that is the share the fix gates"
    );
    assert_eq!(
        long_header.source_domains[0]
            .source_lien_insurance_backing_num
            .get(),
        0
    );
    header.current_slot = V16PodU64::new(now_slot);
    (header, markets, long_header, short_header)
}

fn refresh_crank(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    account: &mut PortfolioV16ViewMut<'_>,
    now_slot: u64,
) -> Result<PermissionlessProgressOutcomeV16, V16Error> {
    market.permissionless_crank_not_atomic(
        account,
        PermissionlessCrankRequestV16 {
            now_slot,
            asset_index: 0,
            effective_price: 1,
            funding_rate_e9: 0,
            action: PermissionlessCrankActionV16::Refresh,
        },
    )
}

fn close_position(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    long: &mut PortfolioV16ViewMut<'_>,
    short: &mut PortfolioV16ViewMut<'_>,
) {
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            short,
            long,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POSITION_Q),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .expect("closing trade must flatten the position");
}

// ---------------------------------------------------------------------------
// (1) MAIN REGRESSION — third-party expiry: honest certificate, liquidatable.
//
// This is `poc_cs04_phantom_source_support_survives_third_party_expiry` with the
// three defect assertions inverted. Against the unfixed tree the very same
// sequence produced `certified_equity = 10`, `certified_liq_deficit = 0` and
// `liquidate_account_not_atomic => Err(NonProgress)`.
// ---------------------------------------------------------------------------

#[test]
fn r_regression_impaired_backing_yields_no_support_and_the_account_is_liquidatable() {
    let (mut header, mut markets, mut long_header, mut short_header) =
        open_source_backed_position(18, 19, EXPIRY_SLOT);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let _ = &mut short_header;

    // A THIRD PARTY runs the permissionless market-side expiry (wrapper tag 89,
    // no signer check). The holder's portfolio is not even passed to it.
    market
        .expire_source_backing_bucket_not_atomic(0, EXPIRY_SLOT)
        .expect("a lapsed bucket must expire through the production transition");

    let bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    let source = market.markets[0]
        .engine
        .source_credit_long
        .try_to_runtime()
        .unwrap();
    // MARKET SIDE: principal forfeited, exactly as before the fix.
    assert_eq!(bucket.status, BackingBucketStatusV16::Impaired);
    assert_eq!(bucket.fresh_unliened_backing_num, 0);
    assert_eq!(bucket.valid_liened_backing_num, 0);
    assert_eq!(
        bucket.impaired_liened_backing_num,
        LIEN_EFFECTIVE * BOUND_SCALE
    );
    assert_eq!(source.fresh_reserved_backing_num, 0);

    // ACCOUNT SIDE: still untouched. The fix changes VALUATION, not state — the
    // mirror is still there for the clearer to settle later.
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        LIEN_EFFECTIVE,
        "the fix must not silently mutate the account; the clearer still owes \
         this account its impaired-claim relabel"
    );
    assert_eq!(
        long.header.source_domains[0].source_claim_impaired_num.get(),
        0
    );

    // The holder re-certifies through the public permissionless crank.
    let outcome = refresh_crank(&mut market, &mut long, EXPIRY_SLOT).expect("refresh must certify");
    assert_eq!(
        outcome,
        PermissionlessProgressOutcomeV16::AccountCurrent,
        "refresh must still be LIVE: the fix drops a term, it does not fail the \
         certificate"
    );

    let cert = long.header.health_cert.try_to_runtime().unwrap();
    assert!(cert.valid, "the account must remain CERTIFIABLE");
    println!(
        "FIXED   bucket.status={:?} source_lien_effective_reserved={} \
         source_lien_counterparty_backing_num={}",
        bucket.status,
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        long.header.source_domains[0]
            .source_lien_counterparty_backing_num
            .get(),
    );
    println!(
        "CERT    certified_equity={} certified_maintenance_req={} certified_initial_req={} \
         certified_liq_deficit={}",
        cert.certified_equity,
        cert.certified_maintenance_req,
        cert.certified_initial_req,
        cert.certified_liq_deficit
    );

    // === (1a) the certificate now tells the truth =========================
    assert_eq!(long.header.capital.get(), 0);
    assert_eq!(long.header.fee_credits.get(), 0);
    assert_eq!(
        cert.certified_equity, 0,
        "capital(0) + support(0) - fee_debt(0): the forfeited counterparty share \
         no longer counts"
    );
    assert_eq!(cert.certified_maintenance_req, MAINTENANCE_REQ);
    assert_eq!(
        cert.certified_liq_deficit, MAINTENANCE_REQ,
        "the true shortfall is now visible to the liquidation gate"
    );

    // === (1b) the ORIGINAL C-S-04 defect assertions must no longer hold ====
    assert_ne!(
        cert.certified_equity, LIEN_EFFECTIVE as i128,
        "DEFECT ASSERTION (1) must fail: the PoC asserted certified_equity == 10"
    );
    assert_ne!(
        cert.certified_liq_deficit, 0,
        "DEFECT ASSERTION (2a) must fail: the PoC asserted certified_liq_deficit == 0"
    );

    // === (1c) withdrawal refusal is UNCHANGED (open leg, :20088) ===========
    assert_eq!(
        market.withdraw_not_atomic(&mut long, 1),
        Err(V16Error::Stale),
        "an account with an open leg still cannot withdraw at all"
    );

    // === (1d) THE POINT: the underwater account is LIQUIDATABLE ============
    let liq = market.liquidate_account_not_atomic(&mut long, LiquidationRequestV16 {
        asset_index: 0,
    });
    println!("LIQUIDATE liquidate_account_not_atomic => {liq:?}");
    let outcome = liq.expect("the underwater account must be liquidatable");
    assert!(
        outcome.closed_q > 0,
        "DEFECT ASSERTION (2b) must fail: the PoC asserted Err(NonProgress); \
         liquidation must make real progress, closed_q = {}",
        outcome.closed_q
    );

    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
}

// ---------------------------------------------------------------------------
// (2) The same, with NO third party: the holder alone, two cranks.
//
// This closes the dossier's open gap 3 (the self-serve route was never
// exercised). The first crank fires the one-shot lapsed-backing guard, which
// commits the MARKET-side expiry; the second certifies. Before the fix the
// second certificate carried the phantom; now it is honest and the account is
// liquidatable without anybody's cooperation.
// ---------------------------------------------------------------------------

#[test]
fn r_regression_holder_only_two_crank_route_also_certifies_honestly() {
    let (mut header, mut markets, mut long_header, mut short_header) =
        open_source_backed_position(26, 27, EXPIRY_SLOT);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let _ = &mut short_header;

    // No third party runs anything. The bucket is `Fresh` and lapsed.
    let bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(bucket.status, BackingBucketStatusV16::Fresh);
    assert!(bucket.expiry_slot <= market.header.current_slot.get());

    let first = refresh_crank(&mut market, &mut long, EXPIRY_SLOT).expect("first crank");
    println!("SELF-SERVE first crank => {first:?}");
    let second = refresh_crank(&mut market, &mut long, EXPIRY_SLOT).expect("second crank");
    println!("SELF-SERVE second crank => {second:?}");

    let bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(
        bucket.status,
        BackingBucketStatusV16::Impaired,
        "the holder's own crank committed the market-side expiry"
    );
    let cert = long.header.health_cert.try_to_runtime().unwrap();
    assert!(cert.valid);
    println!(
        "SELF-SERVE certified_equity={} certified_liq_deficit={}",
        cert.certified_equity, cert.certified_liq_deficit
    );
    assert_eq!(cert.certified_equity, 0);
    assert_eq!(cert.certified_liq_deficit, MAINTENANCE_REQ);
    let outcome = market
        .liquidate_account_not_atomic(&mut long, LiquidationRequestV16 { asset_index: 0 })
        .expect("liquidatable on the holder-only route too");
    assert!(outcome.closed_q > 0);
}

// ---------------------------------------------------------------------------
// (3) Withdraw / convert refusals are UNCHANGED — the fix opens no new
//     extraction path, and closes none that was open.
// ---------------------------------------------------------------------------

#[test]
fn r_regression_withdraw_and_convert_refusals_are_unchanged() {
    let (mut header, mut markets, mut long_header, mut short_header) =
        open_source_backed_position(20, 21, EXPIRY_SLOT);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .expire_source_backing_bucket_not_atomic(0, EXPIRY_SLOT)
            .unwrap();
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        close_position(&mut market, &mut long, &mut short);
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);

    // Flat, still carrying the (now unsupported) lien. The certificate the
    // closing trade left behind is already the honest one.
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        LIEN_EFFECTIVE
    );
    let cert = long.header.health_cert.try_to_runtime().unwrap();
    assert!(cert.valid);
    assert_eq!(
        cert.certified_equity, 0,
        "the trade-path recertification is gated too, not just the crank path"
    );
    assert_eq!(long.header.capital.get(), 0);
    assert_eq!(long.header.pnl.get(), CLAIM as i128);

    // Capital ceiling: unchanged.
    assert_eq!(
        market.withdraw_not_atomic(&mut long, 1),
        Err(V16Error::LockActive),
        "withdraw is still ceilinged by capital"
    );
    assert_eq!(
        market.withdraw_not_atomic(&mut long, LIEN_EFFECTIVE),
        Err(V16Error::LockActive)
    );
    // The support -> capital conduit: unchanged. `account_has_source_liens` is
    // still true (the fix does not zero the field), so the refusal still fires
    // before any support is computed.
    assert_eq!(
        market.convert_released_pnl_to_capital_not_atomic(&mut long),
        Err(V16Error::LockActive),
        "convert still refuses while the lien is held"
    );
    assert_eq!(market.header.vault.get(), 1_000 + CLAIM);
}

// ---------------------------------------------------------------------------
// (4) The flat-account normalizer still works, AND valuation is now invariant
//     across it: the certificate before the clearer equals the certificate
//     after. That equality is the statement that the gate subtracts exactly
//     what `prepare_account_counterparty_lien_impairment` subtracts.
//
//     Before the fix this delta was 10 (the whole forfeited principal).
// ---------------------------------------------------------------------------

#[test]
fn r_regression_flat_normalizer_still_clears_and_valuation_is_clearer_invariant() {
    let (mut header, mut markets, mut long_header, mut short_header) =
        open_source_backed_position(22, 23, EXPIRY_SLOT);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .expire_source_backing_bucket_not_atomic(0, EXPIRY_SLOT)
            .unwrap();
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        close_position(&mut market, &mut long, &mut short);
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    let before = long.header.health_cert.try_to_runtime().unwrap();
    assert!(before.valid);

    let released = market
        .release_account_source_credit_liens_if_unneeded_not_atomic(&mut long)
        .expect("a flat account must still reach the clearer");
    assert_eq!(
        released, LIEN_EFFECTIVE,
        "the normalizer still books the full effective through the \
         ImpairCounterparty arm"
    );
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        0
    );
    assert_eq!(
        long.header.source_domains[0].source_claim_impaired_num.get(),
        LIEN_EFFECTIVE * BOUND_SCALE,
        "the forfeited face still lands in the impaired lane"
    );

    let after = long.header.health_cert.try_to_runtime().unwrap();
    assert!(after.valid);
    println!(
        "INVARIANT certified_equity before clearer = {}, after clearer = {}, delta = {}",
        before.certified_equity,
        after.certified_equity,
        before.certified_equity - after.certified_equity
    );
    assert_eq!(after.certified_equity, 0);
    assert_eq!(
        before.certified_equity - after.certified_equity,
        0,
        "valuation is now invariant across the clearer: the gate removed exactly \
         what prepare_account_counterparty_lien_impairment removes"
    );

    // Re-opening the position the phantom used to support is still refused.
    let reopen = market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POSITION_Q),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .map(|_| ());
    assert_eq!(reopen, Err(V16Error::LockActive));
}

// ---------------------------------------------------------------------------
// (5) LIVENESS A — a live bucket still supports in full.
//
// The fix must not be "always zero". With the SAME fixture one slot before
// expiry, the account certifies at the full lien effective and is NOT
// liquidatable.
// ---------------------------------------------------------------------------

#[test]
fn r_regression_fresh_unexpired_backing_still_supports_in_full() {
    let live_slot = EXPIRY_SLOT - 1;
    let (mut header, mut markets, mut long_header, mut short_header) =
        open_source_backed_position(28, 29, live_slot);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let _ = &mut short_header;

    let bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(bucket.status, BackingBucketStatusV16::Fresh);
    assert!(bucket.expiry_slot > market.header.current_slot.get());

    let outcome = refresh_crank(&mut market, &mut long, live_slot).expect("refresh must certify");
    assert_eq!(outcome, PermissionlessProgressOutcomeV16::AccountCurrent);
    let cert = long.header.health_cert.try_to_runtime().unwrap();
    println!(
        "LIVENESS certified_equity={} certified_liq_deficit={}",
        cert.certified_equity, cert.certified_liq_deficit
    );
    // On a LIVE bucket both terms of `account_source_realizable_support` pay:
    //   * the gated lien term, in full            -> LIEN_EFFECTIVE            = 10
    //   * the unliened claim term, haircut by the
    //     domain's post-lien credit rate:
    //     claim_num = 100*BS - 10*BS = 90*BS, rate = (100-10)/100 of scale,
    //     credited = 90 * 0.9                     -> UNLIENED_CLAIM_SUPPORT    = 81
    // If the fix had gated a live bucket, this certificate would read 81.
    const UNLIENED_CLAIM_SUPPORT: u128 = 81;
    assert_eq!(
        cert.certified_equity as u128,
        UNLIENED_CLAIM_SUPPORT + LIEN_EFFECTIVE,
        "a Fresh, unexpired bucket must still support the lien term in full: the \
         certificate is the unliened claim credit PLUS the whole lien effective"
    );
    assert_ne!(
        cert.certified_equity as u128, UNLIENED_CLAIM_SUPPORT,
        "…and specifically must NOT be the unliened credit alone, which is what a \
         fix that gated live backing would produce"
    );
    assert_eq!(cert.certified_liq_deficit, 0);
    assert_eq!(
        market.liquidate_account_not_atomic(&mut long, LiquidationRequestV16 { asset_index: 0 }),
        Err(V16Error::NonProgress),
        "a properly backed account must NOT become liquidatable"
    );
}

// ---------------------------------------------------------------------------
// (6) LIVENESS B — an INSURANCE-backed lien is untouched by a dead counterparty
//     bucket.
//
// This is why the fix subtracts the counterparty share rather than zeroing the
// whole `source_lien_effective_reserved` term. The domain here has NO
// counterparty backing at all (bucket `Empty`, which is "not current"); the IM
// path mints the lien out of the domain's insurance reservation, and that
// support must survive.
// ---------------------------------------------------------------------------

#[test]
fn r_regression_insurance_backed_lien_survives_a_dead_counterparty_bucket() {
    let (market_id, _, _) = ids();
    let claim_num = CLAIM * BOUND_SCALE;
    // `available_backing = insurance_reserved`, so the domain's credit rate is
    // `insurance / positive_claim_bound` = 1/10 of scale; `LIEN_EFFECTIVE` atoms
    // of effective credit then need the full `claim_num` of face.
    let insurance_num = LIEN_EFFECTIVE * BOUND_SCALE;
    let insurance_atoms = LIEN_EFFECTIVE;

    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.maintenance_margin_bps = 5_000;
    cfg.max_price_move_bps_per_slot = 500;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 1, 1)
        .unwrap();

    let mut long_header = account_fixture(30);
    let mut short_header = account_fixture(31);
    long_header.pnl = V16PodI128::new(CLAIM as i128);
    long_header.source_domains[0].domain = V16PodU32::new(0);
    long_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    long_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(CLAIM);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(CLAIM);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_insurance_credit_reserved_total_atoms = V16PodU128::new(insurance_atoms);
    header.insurance = V16PodU128::new(insurance_atoms);
    header.vault = V16PodU128::new(CLAIM + insurance_atoms + header.vault.get());
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            positive_claim_bound_num: claim_num,
            exact_positive_claim_num: claim_num,
            insurance_credit_reserved_num: insurance_num,
            credit_rate_num: CREDIT_RATE_SCALE / 10,
            ..SourceCreditStateV16::EMPTY
        });
    // A stone-dead counterparty bucket: `Empty`, no principal, not "current".
    markets[0].engine.backing_long =
        BackingBucketV16Account::from_runtime(&BackingBucketV16::empty_for_market(1));
    markets[0].engine.insurance_reservation_long =
        InsuranceCreditReservationV16Account::from_runtime(&InsuranceCreditReservationV16 {
            insurance_credit_reserved_num: insurance_num,
            ..InsuranceCreditReservationV16::EMPTY
        });
    {
        let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.validate_shape()
            .expect("insurance-only source domain must be a valid market shape");
    }
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POSITION_Q),
                    exec_price: 1,
                    fee_bps: 0,
                },
                true,
            )
            .expect("the IM path must mint an INSURANCE-backed source lien");
    }
    assert_eq!(
        long_header.source_domains[0]
            .source_lien_insurance_backing_num
            .get(),
        LIEN_EFFECTIVE * BOUND_SCALE,
        "this lien is insurance-backed"
    );
    assert_eq!(
        long_header.source_domains[0]
            .source_lien_counterparty_backing_num
            .get(),
        0,
        "and carries no counterparty share at all"
    );

    header.current_slot = V16PodU64::new(EXPIRY_SLOT);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(
        bucket.status,
        BackingBucketStatusV16::Empty,
        "the counterparty bucket is not `Fresh`-and-unexpired, i.e. the gate fires"
    );

    let outcome = refresh_crank(&mut market, &mut long, EXPIRY_SLOT).expect("refresh must certify");
    assert_eq!(outcome, PermissionlessProgressOutcomeV16::AccountCurrent);
    let cert = long.header.health_cert.try_to_runtime().unwrap();
    println!(
        "INSURANCE certified_equity={} certified_liq_deficit={}",
        cert.certified_equity, cert.certified_liq_deficit
    );
    assert_eq!(
        cert.certified_equity, LIEN_EFFECTIVE as i128,
        "an insurance-backed lien keeps supporting: the gate removes only the \
         COUNTERPARTY share (here zero), never the insurance share"
    );
    assert_eq!(cert.certified_liq_deficit, 0);
    assert_eq!(
        market.liquidate_account_not_atomic(&mut long, LiquidationRequestV16 { asset_index: 0 }),
        Err(V16Error::NonProgress),
        "an insurance-backed account must NOT be dragged into liquidation"
    );
}
