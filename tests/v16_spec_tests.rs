use percolator::active_bitmap_count_ones;
use percolator::{
    active_bitmap_is_empty, auto_crank_plan_requires_caller_observation,
    v16_domain_count_for_market_slots, AssetLifecycleV16, AssetStateV16, AssetStateV16Account,
    AutoCrankObservationV16, AutoCrankOutcomeV16, AutoCrankPlanV16, AutoCrankResultV16,
    AutoCrankWorkV16, BackingBucketStatusV16, BackingBucketV16, BackingBucketV16Account,
    CloseProgressLedgerV16, CloseProgressLedgerV16Account, EngineAssetSlotV16Account,
    HealthCertV16, HealthCertV16Account, LiquidationRequestV16, Market,
    MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PermissionlessCrankActionV16,
    PermissionlessCrankRequestV16, PermissionlessProgressOutcomeV16,
    PermissionlessRecoveryReasonV16, PortfolioAccountV16Account, PortfolioLegV16,
    PortfolioLegV16Account, PortfolioSourceDomainV16Account, PortfolioV16View, PortfolioV16ViewMut,
    ProvenanceHeaderV16, ProvenanceHeaderV16Account, RebalanceRequestV16, ResolvedCloseOutcomeV16,
    ResolvedPayoutLedgerV16, ResolvedPayoutLedgerV16Account, ResolvedPayoutReceiptV16,
    ResolvedPayoutReceiptV16Account, SideModeV16, SideV16, SourceCreditStateV16,
    SourceCreditStateV16Account, TerminalSlabOutcomeV16, TradeRequestV16, V16Config, V16Error,
    V16OptionalRecoveryReasonAccount, V16PodI128, V16PodU128, V16PodU32, V16PodU64,
    V16_EMPTY_ACTIVE_BITMAP,
};
use percolator::{canonical_accrual_price_step_v16, AccrualStepV16};
use percolator::{ADL_ONE, BOUND_SCALE, CREDIT_RATE_SCALE, POS_SCALE, SOCIAL_LOSS_DEN};

const FUNDING_COUNTER_PRICE: u64 = 1_000_000;
const FUNDING_COUNTER_RATE_E9: i128 = 10_000;
const FUNDING_COUNTER_ATOMS_PER_SLOT: u128 = 10;

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn market_fixture(
    market_slots: u32,
    init_price: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    // upstream fixture: the portfolio-asset cap is bounded by the engine
    // constant, so fixtures with more market slots than that stay valid.
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

fn funding_market_fixture(init_price: u64) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.max_abs_funding_e9_per_slot = FUNDING_COUNTER_RATE_E9 as u64;
    cfg.max_price_move_bps_per_slot = 9_000;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, init_price, 1)
        .unwrap();
    {
        let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.validate_shape().unwrap();
    }
    (header, markets)
}

fn canonical_path_market_fixture(
    init_price: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.max_accrual_dt_slots = 10;
    cfg.min_funding_lifetime_slots = 10;
    cfg.max_abs_funding_e9_per_slot = 10_000;
    cfg.max_price_move_bps_per_slot = 100;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, init_price, 1)
        .unwrap();
    (header, markets)
}

fn canonical_up_path(mut price: u64, count: usize) -> (u64, Vec<AccrualStepV16>) {
    let target = price.checked_mul(2).unwrap();
    let cap_anchor = price;
    let mut remainder = 0;
    let steps = (0..count)
        .map(|index| {
            let remainder_before = remainder;
            (price, remainder) =
                canonical_accrual_price_step_v16(price, target, cap_anchor, 100, true, remainder)
                    .unwrap();
            AccrualStepV16 {
                effective_price: price,
                funding_rate_e9: if index % 2 == 0 { 10_000 } else { -7_500 },
                price_move_remainder_before_bps_num: remainder_before,
                price_move_remainder_after_bps_num: remainder,
            }
        })
        .collect();
    (target, steps)
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

// E6: a close ledger that finished paying out -- `finalized`, zero residual --
// but is still `active` because the ledger stays active to preserve close
// identity/history (close_id watermark, progress totals) for audit purposes.
// `support_consumed == junior_face_burned == gross` and
// `residual_remaining == 0` satisfy validate_close_progress_ledger_with_market's
// progress/residual bookkeeping invariant for a finalized ledger.
fn finalized_inert_close_progress(
    market_id: u64,
    close_id: u64,
    gross: u128,
) -> CloseProgressLedgerV16 {
    CloseProgressLedgerV16 {
        active: true,
        finalized: true,
        canceled: false,
        close_id,
        asset_index: 0,
        market_id,
        domain_side: SideV16::Long,
        gross_loss_at_close_start: gross,
        drift_reference_slot: 0,
        max_close_slot: 0,
        support_consumed: gross,
        junior_face_burned: gross,
        residual_remaining: 0,
        ..CloseProgressLedgerV16::EMPTY
    }
}

// Upstream 592d538c. Two source domains each back exactly half a quote atom, so
// neither can settle a whole atom on its own. Before this commit
// `account_unliened_source_realizable_support` summed the two halves into one
// phantom atom of support and then demanded the consumer deliver it; the
// consumer rounds per domain, delivered nothing, and the whole loss crank died
// on `LockActive` forever.
//
// Fork note: at 592d538c upstream asserted (0, 2) with pnl -1, because it still
// clamped `junior_face_burned = old_positive_face` whenever any loss was
// uncovered. This fork never took that clamp (#172 site 2 -- burning the whole
// face double-charged the account), so it has always retained the positive face
// and landed on pnl +1. Upstream deleted the clamp in 07208fb1 and converged on
// pnl +1 too, and in the same commit redefined the reported face burn as the
// face that actually vanished: (0, 1), not (0, 0). The one atom of source claim
// that the uncovered tail retires is now reported as burned instead of going
// unattributed. What 592d538c is about -- that the crank completes instead of
// returning LockActive -- is unchanged throughout.
#[cfg(feature = "fuzz")]
#[test]
fn v16_cross_domain_unbacked_loss_burns_only_matching_positive_face() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 250);
    let half_atom_num = BOUND_SCALE / 2;
    let asset_market_id = markets[0].engine.asset.market_id.get();
    let source = SourceCreditStateV16 {
        positive_claim_bound_num: BOUND_SCALE,
        exact_positive_claim_num: BOUND_SCALE,
        fresh_reserved_backing_num: half_atom_num,
        credit_rate_num: CREDIT_RATE_SCALE / 2,
        ..SourceCreditStateV16::EMPTY
    };
    let backing = BackingBucketV16 {
        market_id: asset_market_id,
        fresh_unliened_backing_num: half_atom_num,
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    };
    markets[0].engine.source_credit_long = SourceCreditStateV16Account::from_runtime(&source);
    markets[0].engine.source_credit_short = SourceCreditStateV16Account::from_runtime(&source);
    markets[0].engine.backing_long = BackingBucketV16Account::from_runtime(&backing);
    markets[0].engine.backing_short = BackingBucketV16Account::from_runtime(&backing);

    account_header.pnl = V16PodI128::new(2);
    for (slot, domain) in [0u32, 1u32].into_iter().enumerate() {
        account_header.source_domains[slot].domain = V16PodU32::new(domain);
        account_header.source_domains[slot].source_claim_market_id =
            V16PodU64::new(asset_market_id);
        account_header.source_domains[slot].source_claim_bound_num = V16PodU128::new(BOUND_SCALE);
    }
    header.vault = V16PodU128::new(1);
    header.pnl_pos_tot = V16PodU128::new(2);
    header.pnl_pos_bound_tot = V16PodU128::new(2);
    header.pnl_pos_bound_tot_num = V16PodU128::new(2 * BOUND_SCALE);
    header.source_claim_bound_total_num = V16PodU128::new(2 * BOUND_SCALE);
    header.source_fresh_backing_total_num = V16PodU128::new(BOUND_SCALE);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market
        .validate_shape()
        .expect("fractional source fixture must be a valid market state");
    account
        .validate_with_market(&market.as_view())
        .expect("fractional source fixture must be a valid portfolio state");
    let outcome = market
        .kani_apply_signed_kf_delta_to_pnl(&mut account, -1, None)
        .expect("an unbacked cross-domain loss must remain settleable");

    assert_eq!(outcome, (0, 1));
    assert_eq!(account.header.pnl.get(), 1);
    assert_eq!(market.header.pnl_pos_tot.get(), 1);
    // The uncovered atom of loss ate one atom of retained face, so exactly one
    // atom of source claim retires with it -- and that atom is exactly the
    // `junior_face_burned = 1` the call reports.
    assert_eq!(
        market.header.source_claim_bound_total_num.get(),
        BOUND_SCALE
    );
    assert_eq!(market.header.vault.get(), 1);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

fn signed_q(q: u128) -> i128 {
    i128::try_from(q).unwrap()
}

#[derive(Debug, PartialEq, Eq)]
struct KfSettlementOrderOutcome {
    vault: u128,
    c_tot: u128,
    long_capital: u128,
    long_pnl: i128,
    long_equity: i128,
    long_claims: Vec<(u32, u128)>,
    long_funding: (u128, u128, u128, u128),
    short_capital: u128,
    short_pnl: i128,
    short_equity: i128,
    short_claims: Vec<(u32, u128)>,
    short_funding: (u128, u128, u128, u128),
    source_stock: Vec<(u128, u128, u128)>,
}

fn multi_asset_funding_fixture(
    market_slots: u32,
    init_price: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg =
        V16Config::public_user_fund_with_market_slots(market_slots as u16, market_slots, 0, 10);
    cfg.max_abs_funding_e9_per_slot = FUNDING_COUNTER_RATE_E9 as u64;
    cfg.max_price_move_bps_per_slot = 9_000;
    let mut header =
        MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, market_slots, 0).unwrap();
    let mut markets = (0..market_slots)
        .map(|i| Market::new(i as u64, EngineAssetSlotV16Account::default()))
        .collect::<Vec<_>>();
    for (asset_index, market) in markets.iter_mut().enumerate() {
        header
            .activate_empty_asset_slot_not_atomic(
                asset_index as u32,
                &mut market.engine,
                init_price,
                (asset_index + 1) as u64,
            )
            .unwrap();
    }
    (header, markets)
}

fn account_claims(account: &PortfolioAccountV16Account) -> Vec<(u32, u128)> {
    account
        .source_domains
        .iter()
        .filter(|source| source.is_occupied())
        .map(|source| (source.domain.get(), source.source_claim_bound_num.get()))
        .collect()
}

fn kf_settlement_order_outcome(
    attach_order: [usize; 3],
    settle_short_first: bool,
    funding_only: bool,
) -> KfSettlementOrderOutcome {
    let initial_price = if funding_only {
        FUNDING_COUNTER_PRICE
    } else {
        100
    };
    let (mut header, mut markets) = if funding_only {
        multi_asset_funding_fixture(3, initial_price)
    } else {
        market_fixture(3, initial_price)
    };
    let mut long_header = account_fixture(3, 180);
    let mut short_header = account_fixture(3, 181);
    let quantities = [20u128, 10, 15];
    let marks = if funding_only {
        [initial_price; 3]
    } else {
        [110u64, 95, 98]
    };
    let funding_rates = [
        FUNDING_COUNTER_RATE_E9,
        -FUNDING_COUNTER_RATE_E9,
        FUNDING_COUNTER_RATE_E9,
    ];

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        let deposit = if funding_only { 100_000_000 } else { 10_000 };
        market.deposit_not_atomic(&mut long, deposit).unwrap();
        market.deposit_not_atomic(&mut short, deposit).unwrap();
        for asset_index in attach_order {
            market
                .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                    &mut long,
                    &mut short,
                    TradeRequestV16 {
                        asset_index,
                        size_q: signed_q(quantities[asset_index] * POS_SCALE),
                        exec_price: initial_price,
                        fee_bps: 0,
                    },
                    true,
                )
                .unwrap();
        }
        if funding_only {
            for asset_index in 0..3 {
                market
                    .accrue_asset_to_not_atomic(asset_index, 4, initial_price, 0, true)
                    .unwrap();
            }
        }
        for asset_index in 0..3 {
            if !funding_only {
                market
                    .set_asset_raw_oracle_target_not_atomic(asset_index, marks[asset_index])
                    .unwrap();
            }
            market
                .accrue_asset_to_not_atomic(
                    asset_index,
                    if funding_only { 5 } else { 4 },
                    marks[asset_index],
                    if funding_only {
                        funding_rates[asset_index]
                    } else {
                        0
                    },
                    true,
                )
                .unwrap_or_else(|err| panic!("asset {asset_index} accrual failed: {err:?}"));
        }
        if settle_short_first {
            market.full_account_refresh_not_atomic(&mut short).unwrap();
            market.full_account_refresh_not_atomic(&mut long).unwrap();
        } else {
            market.full_account_refresh_not_atomic(&mut long).unwrap();
            market.full_account_refresh_not_atomic(&mut short).unwrap();
        }
        let first_cert = if settle_short_first {
            short.header.health_cert.try_to_runtime().unwrap()
        } else {
            long.header.health_cert.try_to_runtime().unwrap()
        };
        assert_ne!(
            first_cert.cert_risk_epoch,
            market.header.risk_epoch.get(),
            "later source-backing settlement must invalidate the earlier health certificate",
        );
        market.full_account_refresh_not_atomic(&mut long).unwrap();
        market.full_account_refresh_not_atomic(&mut short).unwrap();
        market.validate_shape().unwrap();
        long.validate_with_market(&market.as_view()).unwrap();
        short.validate_with_market(&market.as_view()).unwrap();
    }

    let mut source_stock = Vec::new();
    for market in &markets {
        for (source, backing) in [
            (
                &market.engine.source_credit_long,
                &market.engine.backing_long,
            ),
            (
                &market.engine.source_credit_short,
                &market.engine.backing_short,
            ),
        ] {
            let source = source.try_to_runtime().unwrap();
            let backing = backing.try_to_runtime().unwrap();
            source_stock.push((
                source.positive_claim_bound_num,
                source.fresh_reserved_backing_num,
                backing.fresh_unliened_backing_num,
            ));
        }
    }
    KfSettlementOrderOutcome {
        vault: header.vault.get(),
        c_tot: header.c_tot.get(),
        long_capital: long_header.capital.get(),
        long_pnl: long_header.pnl.get(),
        long_equity: long_header
            .health_cert
            .try_to_runtime()
            .unwrap()
            .certified_equity,
        long_claims: account_claims(&long_header),
        long_funding: funding_counter_tuple(&long_header),
        short_capital: short_header.capital.get(),
        short_pnl: short_header.pnl.get(),
        short_equity: short_header
            .health_cert
            .try_to_runtime()
            .unwrap()
            .certified_equity,
        short_claims: account_claims(&short_header),
        short_funding: funding_counter_tuple(&short_header),
        source_stock,
    }
}

#[test]
fn v16_whole_account_kf_settlement_is_leg_and_account_order_independent() {
    let orders = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let expected = kf_settlement_order_outcome(orders[0], false, false);
    for order in orders {
        for settle_short_first in [false, true] {
            assert_eq!(
                kf_settlement_order_outcome(order, settle_short_first, false),
                expected,
                "K/F settlement changed under attach order {order:?}, short-first={settle_short_first}",
            );
        }
    }

    assert_eq!(expected.vault, 20_000);
    assert_eq!(expected.c_tot, 19_720);
    assert_eq!(
        (
            expected.long_capital,
            expected.long_pnl,
            expected.long_equity,
        ),
        (9_920, 200, 10_120),
    );
    assert_eq!(
        (
            expected.short_capital,
            expected.short_pnl,
            expected.short_equity,
        ),
        (9_800, 80, 9_880),
    );
    assert_eq!(expected.long_claims, vec![(1, 200 * BOUND_SCALE)]);
    assert_eq!(
        expected.short_claims,
        vec![(2, 50 * BOUND_SCALE), (4, 30 * BOUND_SCALE)],
    );
    assert_eq!(
        expected.source_stock,
        vec![
            (0, 0, 0),
            (200 * BOUND_SCALE, 200 * BOUND_SCALE, 200 * BOUND_SCALE),
            (50 * BOUND_SCALE, 50 * BOUND_SCALE, 50 * BOUND_SCALE),
            (0, 0, 0),
            (30 * BOUND_SCALE, 30 * BOUND_SCALE, 30 * BOUND_SCALE),
            (0, 0, 0),
        ],
    );

    let funding_expected = kf_settlement_order_outcome(orders[0], false, true);
    for order in orders {
        for settle_short_first in [false, true] {
            assert_eq!(
                kf_settlement_order_outcome(order, settle_short_first, true),
                funding_expected,
                "funding settlement changed under attach order {order:?}, short-first={settle_short_first}",
            );
        }
    }
    assert_eq!(funding_expected.c_tot, 199_999_550);
    assert_eq!(
        (
            funding_expected.long_capital,
            funding_expected.long_pnl,
            funding_expected.long_equity,
            funding_expected.long_funding,
        ),
        (99_999_650, 100, 99_999_750, (350, 100, 0, 0)),
    );
    assert_eq!(
        (
            funding_expected.short_capital,
            funding_expected.short_pnl,
            funding_expected.short_equity,
            funding_expected.short_funding,
        ),
        (99_999_900, 350, 100_000_250, (0, 0, 100, 350)),
    );
    assert_eq!(funding_expected.long_claims, vec![(3, 100 * BOUND_SCALE)],);
    assert_eq!(
        funding_expected.short_claims,
        vec![(0, 200 * BOUND_SCALE), (4, 150 * BOUND_SCALE)],
    );
    assert_eq!(
        funding_expected.source_stock,
        vec![
            (200 * BOUND_SCALE, 200 * BOUND_SCALE, 200 * BOUND_SCALE),
            (0, 0, 0),
            (0, 0, 0),
            (100 * BOUND_SCALE, 100 * BOUND_SCALE, 100 * BOUND_SCALE),
            (150 * BOUND_SCALE, 150 * BOUND_SCALE, 150 * BOUND_SCALE),
            (0, 0, 0),
        ],
    );
}

fn funding_counter_tuple(account: &PortfolioAccountV16Account) -> (u128, u128, u128, u128) {
    (
        account.funding_long_paid_atoms_total.get(),
        account.funding_long_received_atoms_total.get(),
        account.funding_short_paid_atoms_total.get(),
        account.funding_short_received_atoms_total.get(),
    )
}

fn open_one_lot_pair(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    long: &mut PortfolioV16ViewMut<'_>,
    short: &mut PortfolioV16ViewMut<'_>,
) {
    market.deposit_not_atomic(long, 10_000_000).unwrap();
    market.deposit_not_atomic(short, 10_000_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            long,
            short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: FUNDING_COUNTER_PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
}

/// Like `market_fixture`, but with a nonzero `max_trading_fee_bps` cap so
/// trade requests may carry a fee (the base `market_fixture` config has
/// `max_trading_fee_bps: 0`, which is why every pre-existing trade test in
/// this file uses `fee_bps: 0`).
fn market_fixture_with_trade_fee(
    market_slots: u32,
    init_price: u64,
    max_trading_fee_bps: u64,
) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg =
        V16Config::public_user_fund_with_market_slots(market_slots as u16, market_slots, 0, 10);
    cfg.max_trading_fee_bps = max_trading_fee_bps;
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

#[test]
fn v16_canonical_accrual_path_matches_every_complete_transaction_partition() {
    const INITIAL_PRICE: u64 = 1_000_000;
    let (target, steps) = canonical_up_path(INITIAL_PRICE, 10);
    assert_eq!(target, 2_000_000);
    assert_eq!(steps.last().unwrap().effective_price, 1_100_000);

    let run = |fragmented: bool| {
        let (mut header, mut markets) = canonical_path_market_fixture(INITIAL_PRICE);
        let mut long_account = account_fixture(1, 41);
        let mut short_account = account_fixture(1, 42);
        {
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut long = PortfolioV16ViewMut::new(&mut long_account);
            let mut short = PortfolioV16ViewMut::new(&mut short_account);
            open_one_lot_pair(&mut market, &mut long, &mut short);

            if fragmented {
                for (index, step) in steps.iter().enumerate() {
                    let now_slot = u64::try_from(index + 2).unwrap();
                    let outcome = market
                        .accrue_asset_path_to_not_atomic(
                            0,
                            now_slot,
                            target,
                            core::slice::from_ref(step),
                            true,
                        )
                        .unwrap();
                    assert_eq!(outcome.dt, 1);
                }
            } else {
                let outcome = market
                    .accrue_asset_path_to_not_atomic(0, 11, target, &steps, true)
                    .unwrap();
                assert_eq!(outcome.dt, 10);
            }
        }
        (header, markets.remove(0).engine.asset)
    };

    let (fragmented_header, fragmented_asset) = run(true);
    let (delayed_header, delayed_asset) = run(false);
    assert_eq!(delayed_asset, fragmented_asset);
    assert_eq!(delayed_asset.effective_price.get(), 1_100_000);
    assert_eq!(delayed_asset.fund_px_last.get(), INITIAL_PRICE);
    assert_eq!(delayed_header.current_slot, fragmented_header.current_slot);
    assert_eq!(delayed_header.slot_last, fragmented_header.slot_last);
    assert_eq!(delayed_header.oracle_epoch, fragmented_header.oracle_epoch);
    assert_eq!(
        delayed_header.funding_epoch,
        fragmented_header.funding_epoch
    );
    assert_eq!(
        delayed_header.loss_stale_active,
        fragmented_header.loss_stale_active
    );
}

#[test]
fn v16_canonical_accrual_path_requires_the_complete_bounded_prefix() {
    const INITIAL_PRICE: u64 = 1_000_000;
    let (target, steps) = canonical_up_path(INITIAL_PRICE, 10);
    let (mut header, mut markets) = canonical_path_market_fixture(INITIAL_PRICE);
    let mut long_account = account_fixture(1, 43);
    let mut short_account = account_fixture(1, 44);
    let before_header;
    let before_asset;
    let result;
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_account);
        let mut short = PortfolioV16ViewMut::new(&mut short_account);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        before_header = *market.header;
        before_asset = market.markets[0].engine.asset;
        result = market.accrue_asset_path_to_not_atomic(0, 11, target, &steps[..9], true);
    }

    assert_eq!(result, Err(V16Error::InvalidConfig));
    assert_eq!(header, before_header);
    assert_eq!(markets[0].engine.asset, before_asset);
}

#[test]
fn v16_canonical_accrual_path_bounds_long_gap_work_and_remains_actionable() {
    const INITIAL_PRICE: u64 = 1_000_000;
    let (target, steps) = canonical_up_path(INITIAL_PRICE, percolator::V16_MAX_ACCRUAL_PATH_STEPS);
    let (mut header, mut markets) = canonical_path_market_fixture(INITIAL_PRICE);
    header.config.max_accrual_dt_slots = V16PodU64::new(64);
    header.config.min_funding_lifetime_slots = V16PodU64::new(64);
    let mut long_account = account_fixture(1, 45);
    let mut short_account = account_fixture(1, 46);
    let outcome;
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_account);
        let mut short = PortfolioV16ViewMut::new(&mut short_account);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        outcome = market
            .accrue_asset_path_to_not_atomic(0, 65, target, &steps, true)
            .unwrap();
    }

    assert_eq!(outcome.dt as usize, percolator::V16_MAX_ACCRUAL_PATH_STEPS);
    assert!(outcome.loss_stale_after);
    assert_eq!(markets[0].engine.asset.slot_last.get(), 33);
    assert_eq!(header.current_slot.get(), 65);
    assert_eq!(header.loss_stale_active, 1);
}

#[test]
fn v16_canonical_accrual_path_carries_sub_atom_price_progress_across_calls() {
    let mut price = 100;
    let mut remainder = 0;
    let mut steps = Vec::new();
    for _ in 0..5 {
        let before = remainder;
        (price, remainder) =
            canonical_accrual_price_step_v16(price, 200, 100, 20, true, remainder).unwrap();
        steps.push(AccrualStepV16 {
            effective_price: price,
            funding_rate_e9: 0,
            price_move_remainder_before_bps_num: before,
            price_move_remainder_after_bps_num: remainder,
        });
    }
    assert_eq!(price, 101);
    assert_eq!(remainder, 0);

    let run = |fragmented: bool| {
        let (mut header, mut markets) = canonical_path_market_fixture(100);
        header.config.max_accrual_dt_slots = V16PodU64::new(5);
        header.config.min_funding_lifetime_slots = V16PodU64::new(5);
        header.config.max_price_move_bps_per_slot = V16PodU64::new(20);
        let mut long_account = account_fixture(1, 47);
        let mut short_account = account_fixture(1, 48);
        {
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut long = PortfolioV16ViewMut::new(&mut long_account);
            let mut short = PortfolioV16ViewMut::new(&mut short_account);
            open_one_lot_pair(&mut market, &mut long, &mut short);
            if fragmented {
                for (index, step) in steps.iter().enumerate() {
                    market
                        .accrue_asset_path_to_not_atomic(
                            0,
                            u64::try_from(index + 2).unwrap(),
                            200,
                            core::slice::from_ref(step),
                            true,
                        )
                        .unwrap();
                }
            } else {
                market
                    .accrue_asset_path_to_not_atomic(0, 6, 200, &steps, true)
                    .unwrap();
            }
        }
        (header, markets.remove(0).engine.asset)
    };

    assert_eq!(run(false), run(true));
}

/// 149cfe56 hunk without an upstream test: a funding-only accrual at an unchanged
/// effective price must leave `fund_px_last`, the canonical path's price-cap anchor,
/// where the active trajectory put it, so the next canonical step is computed from
/// the same anchor whether or not the funding accrual happened in between.
#[test]
fn v16_zero_move_funding_accrual_preserves_canonical_price_anchor() {
    const INITIAL_PRICE: u64 = 1_000_000;
    const STEP_ATOMS: u64 = INITIAL_PRICE / 100;
    let (target, steps) = canonical_up_path(INITIAL_PRICE, 1);
    let (mut header, mut markets) = canonical_path_market_fixture(INITIAL_PRICE);
    let mut long_account = account_fixture(1, 61);
    let mut short_account = account_fixture(1, 62);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_account);
        let mut short = PortfolioV16ViewMut::new(&mut short_account);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_path_to_not_atomic(0, 2, target, &steps, true)
            .unwrap();
    }
    let after_path = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after_path.effective_price, INITIAL_PRICE + STEP_ATOMS);
    assert_eq!(after_path.fund_px_last, INITIAL_PRICE);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let outcome = market
            .accrue_asset_to_not_atomic(0, 3, INITIAL_PRICE + STEP_ATOMS, 10_000, true)
            .unwrap();
        assert!(outcome.funding_active);
        assert!(!outcome.price_move_active);
    }
    let after_funding = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_ne!(after_funding.f_long_num, after_path.f_long_num);
    assert_eq!(after_funding.effective_price, INITIAL_PRICE + STEP_ATOMS);
    assert_eq!(after_funding.fund_px_last, INITIAL_PRICE);

    let (next_price, next_remainder) = canonical_accrual_price_step_v16(
        INITIAL_PRICE + STEP_ATOMS,
        target,
        INITIAL_PRICE,
        100,
        true,
        0,
    )
    .unwrap();
    assert_eq!(
        (next_price, next_remainder),
        (INITIAL_PRICE + 2 * STEP_ATOMS, 0)
    );
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .accrue_asset_path_to_not_atomic(
                0,
                4,
                target,
                &[AccrualStepV16 {
                    effective_price: next_price,
                    funding_rate_e9: 0,
                    price_move_remainder_before_bps_num: 0,
                    price_move_remainder_after_bps_num: next_remainder,
                }],
                true,
            )
            .unwrap();
    }
    let after_next = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after_next.effective_price, INITIAL_PRICE + 2 * STEP_ATOMS);
    assert_eq!(after_next.fund_px_last, INITIAL_PRICE);
}

#[test]
fn v16_canonical_accrual_path_rejects_discontinuous_remainder_before_mutation() {
    let (mut header, mut markets) = canonical_path_market_fixture(100);
    header.config.max_accrual_dt_slots = V16PodU64::new(2);
    header.config.min_funding_lifetime_slots = V16PodU64::new(2);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(20);
    let steps = [
        AccrualStepV16 {
            effective_price: 100,
            funding_rate_e9: 0,
            price_move_remainder_before_bps_num: 0,
            price_move_remainder_after_bps_num: 2_000,
        },
        AccrualStepV16 {
            effective_price: 100,
            funding_rate_e9: 0,
            price_move_remainder_before_bps_num: 1_999,
            price_move_remainder_after_bps_num: 4_000,
        },
    ];
    let before_header = header;
    let before_asset = markets[0].engine.asset;
    let result = MarketGroupV16ViewMut::new(&mut header, &mut markets)
        .accrue_asset_path_to_not_atomic(0, 3, 200, &steps, true);
    assert_eq!(result, Err(V16Error::InvalidConfig));
    assert_eq!(header, before_header);
    assert_eq!(markets[0].engine.asset, before_asset);
}

#[test]
fn v16_canonical_accrual_path_scales_indices_after_quantity_adl() {
    const INITIAL_PRICE: u64 = 1_000_000;
    let (target, steps) = canonical_up_path(INITIAL_PRICE, 1);
    let step = steps[0];
    let (mut header, mut markets) = canonical_path_market_fixture(INITIAL_PRICE);
    let mut long_header = account_fixture(1, 225);
    let mut short_header = account_fixture(1, 226);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 100_000_000).unwrap();
        market.deposit_not_atomic(&mut short, 100_000_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(4 * POS_SCALE),
                    exec_price: INITIAL_PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: POS_SCALE,
                },
            )
            .unwrap();
        market
            .accrue_asset_path_to_not_atomic(0, 2, target, &steps, true)
            .unwrap();
    }

    let asset = markets[0].engine.asset.try_to_runtime().unwrap();
    let a_short = ADL_ONE * 3 / 4;
    let price_delta = i128::from(step.effective_price - INITIAL_PRICE);
    let funding_index_delta = FUNDING_COUNTER_ATOMS_PER_SLOT as i128;
    assert_eq!(asset.a_short, a_short);
    assert_eq!(asset.k_long, price_delta * ADL_ONE as i128);
    assert_eq!(asset.k_short, -(price_delta * a_short as i128));
    assert_eq!(asset.f_long_num, -(funding_index_delta * ADL_ONE as i128));
    assert_eq!(asset.f_short_num, funding_index_delta * a_short as i128);
}

#[test]
fn v16_public_fund_validator_accepts_nontrivial_exact_solvency_profile() {
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 1, 10);
    cfg.maintenance_margin_bps = 10_000;
    cfg.initial_margin_bps = 10_000;
    cfg.max_price_move_bps_per_slot = 100;
    cfg.max_accrual_dt_slots = 1;
    cfg.min_funding_lifetime_slots = 1;
    cfg.max_abs_funding_e9_per_slot = 0;
    cfg.liquidation_fee_bps = 100;
    cfg.min_liquidation_abs = 1;
    cfg.liquidation_fee_cap = 1;
    cfg.min_nonzero_mm_req = 2;
    cfg.min_nonzero_im_req = 3;

    assert_eq!(cfg.validate_public_user_fund(), Ok(()));
}

#[test]
fn v16_view_deposit_and_withdraw_are_the_tested_paths() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 2);
    let mut market_view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account_view = PortfolioV16ViewMut::new(&mut account_header);

    market_view
        .deposit_not_atomic(&mut account_view, 11)
        .unwrap();
    market_view
        .withdraw_not_atomic(&mut account_view, 4)
        .unwrap();

    assert_eq!(account_view.header.capital.get(), 7);
    assert_eq!(market_view.header.c_tot.get(), 7);
    assert_eq!(market_view.header.vault.get(), 7);
    market_view.validate_shape().unwrap();
    account_view
        .validate_with_market(&market_view.as_view())
        .unwrap();
}

#[test]
fn v16_funding_counter_layout_canary_places_fields_before_fee_state() {
    let width = core::mem::size_of::<V16PodU128>();

    assert_eq!(
        core::mem::offset_of!(PortfolioAccountV16Account, funding_long_paid_atoms_total),
        core::mem::offset_of!(PortfolioAccountV16Account, residual_received_atoms_total) + width
    );
    assert_eq!(
        core::mem::offset_of!(
            PortfolioAccountV16Account,
            funding_long_received_atoms_total
        ),
        core::mem::offset_of!(PortfolioAccountV16Account, funding_long_paid_atoms_total) + width
    );
    assert_eq!(
        core::mem::offset_of!(PortfolioAccountV16Account, funding_short_paid_atoms_total),
        core::mem::offset_of!(
            PortfolioAccountV16Account,
            funding_long_received_atoms_total
        ) + width
    );
    assert_eq!(
        core::mem::offset_of!(
            PortfolioAccountV16Account,
            funding_short_received_atoms_total
        ),
        core::mem::offset_of!(PortfolioAccountV16Account, funding_short_paid_atoms_total) + width
    );
    assert_eq!(
        core::mem::offset_of!(PortfolioAccountV16Account, fee_credits),
        core::mem::offset_of!(
            PortfolioAccountV16Account,
            funding_short_received_atoms_total
        ) + width
    );
}

#[test]
fn v16_funding_counters_record_long_pays_short_once_on_refresh() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 120);
    let mut short_header = account_fixture(1, 121);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();

    assert_eq!(
        funding_counter_tuple(long.header),
        (FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0, 0)
    );
    assert_eq!(
        funding_counter_tuple(short.header),
        (0, 0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT)
    );
    assert_eq!(
        long.header.capital.get(),
        10_000_000 - FUNDING_COUNTER_ATOMS_PER_SLOT
    );
    assert_eq!(
        long.header.funding_long_paid_atoms_total.get(),
        short.header.funding_short_received_atoms_total.get(),
        "payer/receiver funding counters must conserve across both refreshed accounts"
    );

    market.full_account_refresh_not_atomic(&mut long).unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    assert_eq!(
        funding_counter_tuple(long.header),
        (FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0, 0),
        "advancing f_snap must prevent double counting on a later refresh"
    );
    assert_eq!(
        funding_counter_tuple(short.header),
        (0, 0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT)
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_funding_counters_record_short_pays_long_on_negative_funding() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 122);
    let mut short_header = account_fixture(1, 123);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, -FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();

    assert_eq!(
        funding_counter_tuple(long.header),
        (0, FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0)
    );
    assert_eq!(
        funding_counter_tuple(short.header),
        (0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT, 0)
    );
    assert_eq!(
        long.header.funding_long_received_atoms_total.get(),
        short.header.funding_short_paid_atoms_total.get(),
        "receiver/payer funding counters must conserve when shorts pay longs"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_funding_counters_settle_before_same_side_resize() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 124);
    let mut short_header = account_fixture(1, 125);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POS_SCALE),
                    exec_price: FUNDING_COUNTER_PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }

    let long_leg = long_header.legs[0].try_to_runtime().unwrap();
    let short_leg = short_header.legs[0].try_to_runtime().unwrap();
    assert_eq!(long_leg.basis_pos_q, signed_q(2 * POS_SCALE));
    assert_eq!(short_leg.basis_pos_q, -signed_q(2 * POS_SCALE));
    assert_eq!(
        funding_counter_tuple(&long_header),
        (FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0, 0)
    );
    assert_eq!(
        funding_counter_tuple(&short_header),
        (0, 0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT)
    );

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    assert_eq!(
        funding_counter_tuple(long.header),
        (FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0, 0)
    );
    assert_eq!(
        funding_counter_tuple(short.header),
        (0, 0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT)
    );
}

#[test]
fn v16_funding_counters_settle_before_trade_close_clears_leg() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 126);
    let mut short_header = account_fixture(1, 127);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: -signed_q(POS_SCALE),
                    exec_price: FUNDING_COUNTER_PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }

    assert_eq!(long_header.active_bitmap[0].get(), 0);
    assert_eq!(short_header.active_bitmap[0].get(), 0);
    assert_eq!(
        funding_counter_tuple(&long_header),
        (FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0, 0)
    );
    assert_eq!(
        funding_counter_tuple(&short_header),
        (0, 0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT)
    );
}

#[test]
fn v16_funding_counters_record_forfeited_dead_leg_settlement() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 128);
    let mut short_header = account_fixture(1, 129);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
        market.force_asset_recovery_not_atomic(0, 2).unwrap();
        market
            .forfeit_recovery_leg_not_atomic(&mut long, 0, 1)
            .unwrap();
        market
            .forfeit_recovery_leg_not_atomic(&mut short, 0, 1)
            .unwrap();
    }

    assert_eq!(
        funding_counter_tuple(&long_header),
        (FUNDING_COUNTER_ATOMS_PER_SLOT, 0, 0, 0)
    );
    assert_eq!(
        funding_counter_tuple(&short_header),
        (0, 0, 0, FUNDING_COUNTER_ATOMS_PER_SLOT)
    );
}

#[test]
fn v16_funding_counters_ignore_inactive_accounts_when_market_funding_moves() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 130);
    let mut short_header = account_fixture(1, 131);
    let mut idle_header = account_fixture(1, 132);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut idle = PortfolioV16ViewMut::new(&mut idle_header);
    market.full_account_refresh_not_atomic(&mut idle).unwrap();

    assert_eq!(funding_counter_tuple(idle.header), (0, 0, 0, 0));
    market.validate_shape().unwrap();
    idle.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_view_fee_sync_settles_flat_loss_before_fee() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 4);
    header.vault = V16PodU128::new(100);
    header.c_tot = V16PodU128::new(100);
    header.negative_pnl_account_count = V16PodU64::new(1);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);
    account_header.capital = V16PodU128::new(100);
    account_header.pnl = V16PodI128::new(-40);

    let mut market_view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account_view = PortfolioV16ViewMut::new(&mut account_header);
    let charged = market_view
        .sync_account_fee_to_slot_not_atomic(&mut account_view, 10, 10)
        .unwrap();

    assert_eq!(charged, 60);
    assert_eq!(account_view.header.pnl.get(), 0);
    assert_eq!(account_view.header.capital.get(), 0);
    assert_eq!(market_view.header.c_tot.get(), 0);
    assert_eq!(market_view.header.insurance.get(), 60);
    assert_eq!(market_view.header.vault.get(), 100);
    assert_eq!(market_view.header.negative_pnl_account_count.get(), 0);
}

#[test]
fn v16_fee_sync_on_nonflat_account_settles_hidden_k_loss_before_fee() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 14);
    let mut short_header = account_fixture(1, 15);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 100).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
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
        market
            .accrue_asset_to_not_atomic(0, 2, 50, 0, true)
            .unwrap();
    }
    assert_eq!(long_header.pnl.get(), 0);
    assert_eq!(long_header.capital.get(), 100);
    assert_eq!(header.insurance.get(), 0);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let charged = market
        .sync_account_fee_to_slot_not_atomic(&mut long, 2, 100)
        .unwrap();

    assert_eq!(
        charged, 50,
        "lazy K loss must consume principal before recurring fee collection"
    );
    assert_eq!(long.header.capital.get(), 0);
    assert_eq!(long.header.pnl.get(), 0);
    assert_eq!(market.header.insurance.get(), 50);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_finalize_side_reset_is_public_value_neutral_and_epoch_bumping() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();
    let risk_epoch_before = header.risk_epoch.get();
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.mode_long = SideModeV16::ResetPending;
    asset.k_epoch_start_long = -17;
    asset.f_epoch_start_long_num = 23;
    asset.b_epoch_start_long_num = 29;
    asset.k_epoch_start_short = 31;
    asset.f_epoch_start_short_num = -37;
    asset.b_epoch_start_short_num = 41;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .finalize_side_reset_not_atomic(0, SideV16::Long)
        .unwrap();

    let finalized = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(finalized.mode_long, SideModeV16::Normal);
    assert_eq!(finalized.k_epoch_start_long, 0);
    assert_eq!(finalized.f_epoch_start_long_num, 0);
    assert_eq!(finalized.b_epoch_start_long_num, 0);
    assert_eq!(finalized.k_epoch_start_short, 31);
    assert_eq!(finalized.f_epoch_start_short_num, -37);
    assert_eq!(finalized.b_epoch_start_short_num, 41);
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 1);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    market.validate_shape().unwrap();
}

#[test]
fn v16_finalize_side_reset_rejects_blocked_pending_side() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let risk_epoch_before = header.risk_epoch.get();
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.mode_short = SideModeV16::ResetPending;
    asset.pending_obligation_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(
        market.finalize_side_reset_not_atomic(0, SideV16::Short),
        Err(V16Error::Stale)
    );

    let blocked = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(blocked.mode_short, SideModeV16::ResetPending);
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_batch_trade_applies_multiple_fills_after_inline_refresh() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut long_header = account_fixture(2, 201);
    let mut short_header = account_fixture(2, 202);
    let requests = [
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 0,
        },
        TradeRequestV16 {
            asset_index: 1,
            size_q: signed_q(2 * POS_SCALE),
            exec_price: 100,
            fee_bps: 0,
        },
    ];

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000).unwrap();

    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(&mut long, &mut short, &requests, true)
        .unwrap();

    assert_eq!(outcome.fill_count, 2);
    assert_eq!(outcome.notional, 300);
    assert_eq!(outcome.fee_a, 0);
    assert_eq!(outcome.fee_b, 0);
    assert_ne!(long.header.active_bitmap[0].get(), 0);
    assert_ne!(short.header.active_bitmap[0].get(), 0);
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        POS_SCALE
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_short_q.get(),
        POS_SCALE
    );
    assert_eq!(
        market.markets[1].engine.asset.oi_eff_long_q.get(),
        2 * POS_SCALE
    );
    assert_eq!(
        market.markets[1].engine.asset.oi_eff_short_q.get(),
        2 * POS_SCALE
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_batch_trade_supports_mixed_signed_spread_legs() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut taker_header = account_fixture(2, 221);
    let mut lp_header = account_fixture(2, 222);
    let size_q = signed_q(5 * POS_SCALE);
    let requests = [
        TradeRequestV16 {
            asset_index: 0,
            size_q,
            exec_price: 100,
            fee_bps: 0,
        },
        TradeRequestV16 {
            asset_index: 1,
            size_q: -size_q,
            exec_price: 100,
            fee_bps: 0,
        },
    ];

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
    let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
    market.deposit_not_atomic(&mut taker, 1_000).unwrap();
    market.deposit_not_atomic(&mut lp, 1_000).unwrap();

    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(&mut taker, &mut lp, &requests, true)
        .unwrap();

    assert_eq!(outcome.fill_count, 2);
    assert_eq!(outcome.notional, 1_000);
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        5 * POS_SCALE
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_short_q.get(),
        5 * POS_SCALE
    );
    assert_eq!(
        market.markets[1].engine.asset.oi_eff_long_q.get(),
        5 * POS_SCALE
    );
    assert_eq!(
        market.markets[1].engine.asset.oi_eff_short_q.get(),
        5 * POS_SCALE
    );

    let taker_asset0 = taker.header.legs[0].try_to_runtime().unwrap();
    let taker_asset1 = taker.header.legs[1].try_to_runtime().unwrap();
    let lp_asset0 = lp.header.legs[0].try_to_runtime().unwrap();
    let lp_asset1 = lp.header.legs[1].try_to_runtime().unwrap();
    assert_eq!(taker_asset0.side, SideV16::Long);
    assert_eq!(taker_asset1.side, SideV16::Short);
    assert_eq!(lp_asset0.side, SideV16::Short);
    assert_eq!(lp_asset1.side, SideV16::Long);
    assert_eq!(taker_asset0.basis_pos_q, size_q);
    assert_eq!(taker_asset1.basis_pos_q, -size_q);
    assert_eq!(lp_asset0.basis_pos_q, -size_q);
    assert_eq!(lp_asset1.basis_pos_q, size_q);
    market.validate_shape().unwrap();
    taker.validate_with_market(&market.as_view()).unwrap();
    lp.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_single_trade_matches_batch_of_one_state() {
    let (mut single_header, mut single_markets) = market_fixture(1, 100);
    let mut single_long_header = account_fixture(1, 209);
    let mut single_short_header = account_fixture(1, 210);
    let mut batch_header = single_header;
    let mut batch_markets = single_markets.clone();
    let mut batch_long_header = single_long_header;
    let mut batch_short_header = single_short_header;
    let request = TradeRequestV16 {
        asset_index: 0,
        size_q: signed_q(2 * POS_SCALE),
        exec_price: 100,
        fee_bps: 0,
    };

    let single_outcome = {
        let mut market = MarketGroupV16ViewMut::new(&mut single_header, &mut single_markets);
        let mut long = PortfolioV16ViewMut::new(&mut single_long_header);
        let mut short = PortfolioV16ViewMut::new(&mut single_short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long, &mut short, request, true,
            )
            .unwrap()
    };
    let batch_outcome = {
        let mut market = MarketGroupV16ViewMut::new(&mut batch_header, &mut batch_markets);
        let mut long = PortfolioV16ViewMut::new(&mut batch_long_header);
        let mut short = PortfolioV16ViewMut::new(&mut batch_short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
        market
            .execute_batch_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                &[request],
                true,
            )
            .unwrap()
    };

    assert_eq!(batch_outcome.fill_count, 1);
    assert_eq!(single_outcome.fee_a, batch_outcome.fee_a);
    assert_eq!(single_outcome.fee_b, batch_outcome.fee_b);
    assert_eq!(single_outcome.notional, batch_outcome.notional);
    assert_eq!(single_header, batch_header);
    assert_eq!(single_markets, batch_markets);
    assert_eq!(single_long_header, batch_long_header);
    assert_eq!(single_short_header, batch_short_header);
}

#[test]
fn v16_batch_trade_checks_initial_margin_on_final_portfolio() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut taker_header = account_fixture(2, 211);
    let mut lp_header = account_fixture(2, 212);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
        let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
        market.deposit_not_atomic(&mut taker, 1_000).unwrap();
        market.deposit_not_atomic(&mut lp, 1_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut lp,
                &mut taker,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(10 * POS_SCALE),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
    let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(
            &mut taker,
            &mut lp,
            &[
                TradeRequestV16 {
                    asset_index: 1,
                    size_q: signed_q(10 * POS_SCALE),
                    exec_price: 100,
                    fee_bps: 0,
                },
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(10 * POS_SCALE),
                    exec_price: 100,
                    fee_bps: 0,
                },
            ],
            true,
        )
        .expect("batch must not reject a final-IM-valid basket due to interim IM");

    assert_eq!(outcome.fill_count, 2);
    assert_eq!(outcome.notional, 2_000);
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        0,
        "second fill closes the original asset-0 exposure"
    );
    assert_eq!(
        market.markets[1].engine.asset.oi_eff_long_q.get(),
        10 * POS_SCALE,
        "final portfolio keeps only the replacement asset-1 exposure"
    );
    assert_eq!(
        taker
            .header
            .health_cert
            .try_to_runtime()
            .unwrap()
            .certified_initial_req,
        1_000
    );
    assert_eq!(
        lp.header
            .health_cert
            .try_to_runtime()
            .unwrap()
            .certified_initial_req,
        1_000
    );
    market.validate_shape().unwrap();
    taker.validate_with_market(&market.as_view()).unwrap();
    lp.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_batch_trade_self_settles_stale_certificates_once_before_fills() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 203);
    let mut short_header = account_fixture(1, 204);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
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
        market
            .accrue_asset_to_not_atomic(0, 2, 101, 0, true)
            .unwrap();
        market.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(101);
    }
    assert_eq!(long_header.pnl.get(), 0);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            &[TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 101,
                fee_bps: 0,
            }],
            true,
        )
        .unwrap();

    assert_eq!(outcome.fill_count, 1);
    assert_eq!(outcome.notional, 101);
    assert!(long.header.pnl.get() > 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_batch_trade_rejects_loss_stale_risk_increase_after_inline_settlement() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 207);
    let mut short_header = account_fixture(1, 208);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
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
        market
            .accrue_asset_to_not_atomic(0, 3, 101, 0, true)
            .unwrap();
        market.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(101);
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let res = market.execute_batch_with_fee_loss_stale_scoped_not_atomic(
        &mut long,
        &mut short,
        &[TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 101,
            fee_bps: 0,
        }],
        true,
    );

    assert_eq!(res, Err(V16Error::LockActive));
}

#[test]
fn v16_fully_accrued_kf_cohort_blocks_fresh_risk_until_every_side_settles() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut winner_header = account_fixture(1, 211);
    let mut loser_header = account_fixture(1, 212);
    let mut entrant_header = account_fixture(1, 213);
    let request = TradeRequestV16 {
        asset_index: 0,
        size_q: signed_q(POS_SCALE),
        exec_price: 101,
        fee_bps: 0,
    };

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    let mut loser = PortfolioV16ViewMut::new(&mut loser_header);
    let mut entrant = PortfolioV16ViewMut::new(&mut entrant_header);
    for account in [&mut winner, &mut loser, &mut entrant] {
        market.deposit_not_atomic(account, 10_000).unwrap();
    }
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut winner,
            &mut loser,
            TradeRequestV16 {
                exec_price: 100,
                ..request
            },
            true,
        )
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 101, 0, true)
        .unwrap();
    market.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(101);
    let accrued = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(accrued.slot_last, market.header.current_slot.get());
    assert_eq!(accrued.stale_account_count_long, 1);
    assert_eq!(accrued.stale_account_count_short, 1);

    market.full_account_refresh_not_atomic(&mut winner).unwrap();
    let winner_current = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(winner_current.stale_account_count_long, 0);
    assert_eq!(winner_current.stale_account_count_short, 1);

    let rejected = market.execute_trade_with_fee_loss_stale_scoped_not_atomic(
        &mut entrant,
        &mut winner,
        request,
        true,
    );
    assert_eq!(rejected, Err(V16Error::LockActive));
    assert_eq!(entrant.header.active_bitmap[0].get(), 0);
    assert_ne!(winner.header.active_bitmap[0].get(), 0);

    market.full_account_refresh_not_atomic(&mut loser).unwrap();
    let current = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(current.stale_account_count_long, 0);
    assert_eq!(current.stale_account_count_short, 0);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut entrant,
            &mut winner,
            request,
            true,
        )
        .expect("settling the final stale cohort must reopen risk transfer");
    market.validate_shape().unwrap();
    winner.validate_with_market(&market.as_view()).unwrap();
    loser.validate_with_market(&market.as_view()).unwrap();
    entrant.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_kf_epoch_clears_exact_index_reversal_without_duplicate_discharge() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 214);
    let mut short_header = account_fixture(1, 215);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 10_000).unwrap();
    market.deposit_not_atomic(&mut short, 10_000).unwrap();
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

    market
        .accrue_asset_to_not_atomic(0, 2, 101, 0, true)
        .unwrap();
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    let first = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(first.kf_epoch_long, 2);
    assert_eq!(first.kf_epoch_short, 2);
    assert_eq!(first.stale_account_count_long, 0);
    assert_eq!(first.stale_account_count_short, 1);

    market
        .accrue_asset_to_not_atomic(0, 3, 100, 0, true)
        .unwrap();
    let reversed = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reversed.k_long, 0);
    assert_eq!(reversed.k_short, 0);
    assert_eq!(reversed.kf_epoch_long, 3);
    assert_eq!(reversed.kf_epoch_short, 3);
    assert_eq!(reversed.stale_account_count_long, 1);
    assert_eq!(reversed.stale_account_count_short, 1);

    // The short's arithmetic snapshots already equal the reversed targets, but
    // its older epoch still owns one cohort membership and must discharge it.
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    let short_current = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(short_current.stale_account_count_long, 1);
    assert_eq!(short_current.stale_account_count_short, 0);
    assert_eq!(short.header.pnl.get(), 0);
    assert_eq!(
        short.header.legs[0].try_to_runtime().unwrap().kf_epoch_snap,
        3
    );

    // Repeating the same account at the same epoch cannot discharge the long.
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    let repeated = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(repeated.stale_account_count_long, 1);
    assert_eq!(repeated.stale_account_count_short, 0);

    market.full_account_refresh_not_atomic(&mut long).unwrap();
    let current = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(current.stale_account_count_long, 0);
    assert_eq!(current.stale_account_count_short, 0);
    assert_eq!(long.header.pnl.get(), 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_stale_opposite_cohort_does_not_block_bounded_owner_reduction() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 216);
    let mut short_header = account_fixture(1, 217);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 10_000).unwrap();
    market.deposit_not_atomic(&mut short, 10_000).unwrap();
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
    market
        .accrue_asset_to_not_atomic(0, 2, 101, 0, true)
        .unwrap();
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    let stale = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(stale.stale_account_count_long, 0);
    assert_eq!(stale.stale_account_count_short, 1);

    let reduced = market
        .rebalance_reduce_position_not_atomic(
            &mut long,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: POS_SCALE,
            },
        )
        .expect("a stale counterparty cannot block the owner's bounded exit");
    assert_eq!(reduced.reduced_q, POS_SCALE);
    assert_eq!(long.header.active_bitmap[0].get(), 0);
    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.stored_pos_count_long, 0);
    assert_eq!(after.stale_account_count_long, 0);
    assert_eq!(after.stale_account_count_short, 1);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_resolved_close_migrates_legacy_normal_adl_residue_before_detach() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 26);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = 0;
    asset.oi_eff_short_q = 0;
    asset.a_long = ADL_ONE / 2;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(1);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();
    market.resolve_market_not_atomic(1).unwrap();
    let outcome = market
        .close_resolved_account_not_atomic(&mut account, 0)
        .expect("resolution must not strand an upgraded zero-effective-OI residue");
    assert_eq!(
        outcome,
        percolator::ResolvedCloseOutcomeV16::Closed { payout: 1_000 }
    );
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    assert_eq!(account.header.capital.get(), 0);
    assert_eq!(market.header.vault.get(), 0);
    let reset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reset.mode_long, SideModeV16::ResetPending);
    assert_eq!(reset.stored_pos_count_long, 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_resolved_close_caps_adl_reduced_basis_before_reset_detach() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 28);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = POS_SCALE;
    asset.oi_eff_short_q = POS_SCALE;
    asset.a_long = ADL_ONE / 2;
    asset.loss_weight_sum_long = 2 * POS_SCALE;
    asset.loss_weight_sum_short = POS_SCALE;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: (2 * POS_SCALE) as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: 2 * POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();
    market.resolve_market_not_atomic(1).unwrap();

    let first = market
        .close_resolved_account_not_atomic(&mut account, 0)
        .expect("resolved close must consume the remaining effective OI");
    assert_eq!(
        first,
        percolator::ResolvedCloseOutcomeV16::Closed { payout: 1_000 }
    );
    assert!(!account.header.legs[0].try_to_runtime().unwrap().active);
    let reset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reset.oi_eff_long_q, 0);
    assert_eq!(reset.oi_eff_short_q, POS_SCALE);
    assert_eq!(reset.mode_long, SideModeV16::ResetPending);
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    assert_eq!(account.header.capital.get(), 0);
    assert_eq!(market.header.vault.get(), 0);
    let terminal = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(terminal.oi_eff_long_q, 0);
    assert_eq!(terminal.oi_eff_short_q, POS_SCALE);
    assert_eq!(terminal.stored_pos_count_long, 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_resolved_close_detaches_one_solvent_leg_per_call() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut long_header = account_fixture(2, 203);
    let mut short_header = account_fixture(2, 204);
    let requests = [
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 0,
        },
        TradeRequestV16 {
            asset_index: 1,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 0,
        },
    ];

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000).unwrap();
    market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(&mut long, &mut short, &requests, true)
        .unwrap();
    let resolved_slot = market.header.current_slot.get();
    market.resolve_market_not_atomic(resolved_slot).unwrap();

    let first = market
        .close_resolved_account_not_atomic(&mut long, 0)
        .expect("the first resolved continuation must clear one leg");
    assert_eq!(first, ResolvedCloseOutcomeV16::ProgressOnly);
    assert_eq!(
        active_bitmap_count_ones(long.header.active_bitmap.map(V16PodU64::get)),
        1
    );
    assert_eq!(long.header.capital.get(), 1_000);

    let second = market
        .close_resolved_account_not_atomic(&mut long, 0)
        .expect("the final resolved continuation must clear and pay");
    assert_eq!(second, ResolvedCloseOutcomeV16::Closed { payout: 1_000 });
    assert!(active_bitmap_is_empty(
        long.header.active_bitmap.map(V16PodU64::get)
    ));
    assert_eq!(long.header.capital.get(), 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_resolved_auto_crank_closes_capital_only_account() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 205);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();
    let resolved_slot = market.header.current_slot.get();
    market.resolve_market_not_atomic(resolved_slot).unwrap();

    let summary = market
        .build_actionable_summary(&account.as_view())
        .expect("capital-only resolved account must classify");
    assert!(summary.resolved_winner);
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: resolved_slot,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("permissionless close must return capital");
    assert_eq!(result.selected, AutoCrankPlanV16::CloseResolved);
    assert_eq!(
        result.outcome,
        AutoCrankOutcomeV16::ResolvedClose(ResolvedCloseOutcomeV16::Closed { payout: 1_000 })
    );
    assert_eq!(account.header.capital.get(), 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_recovery_forfeit_migrates_legacy_normal_adl_residue_before_detach() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 27);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = 0;
    asset.oi_eff_short_q = 0;
    asset.a_long = ADL_ONE / 2;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(1);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();
    market.force_asset_recovery_not_atomic(0, 1).unwrap();
    let vault_before = market.header.vault.get();
    let c_tot_before = market.header.c_tot.get();
    let insurance_before = market.header.insurance.get();
    let capital_before = account.header.capital.get();
    let pnl_before = account.header.pnl.get();
    let outcome = market
        .forfeit_recovery_leg_not_atomic(&mut account, 0, POS_SCALE)
        .expect("Recovery forfeit must detach a zero-effective-OI ADL residue");
    assert!(outcome.detached);
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    let reset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reset.mode_long, SideModeV16::ResetPending);
    assert_eq!(reset.stored_pos_count_long, 0);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(account.header.capital.get(), capital_before);
    assert_eq!(account.header.pnl.get(), pnl_before);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_quantity_adl_blocks_fresh_basis_reissue_across_split_trades() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 220);
    let mut short_header = account_fixture(1, 221);
    let mut successor_header = account_fixture(1, 222);
    let open_q = 4 * POS_SCALE;

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        let mut successor = PortfolioV16ViewMut::new(&mut successor_header);
        market.deposit_not_atomic(&mut long, 10_000).unwrap();
        market.deposit_not_atomic(&mut short, 10_000).unwrap();
        market.deposit_not_atomic(&mut successor, 10_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(open_q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: POS_SCALE,
                },
            )
            .unwrap();
    }

    let asset = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.oi_eff_long_q, 3 * POS_SCALE);
    assert_eq!(asset.oi_eff_short_q, 3 * POS_SCALE);
    assert_eq!(asset.a_short, ADL_ONE * 3 / 4);
    assert_eq!(
        short_header.legs[0]
            .try_to_runtime()
            .unwrap()
            .basis_pos_q
            .unsigned_abs(),
        open_q
    );

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let mut successor = PortfolioV16ViewMut::new(&mut successor_header);
    let result = market.execute_trade_with_fee_loss_stale_scoped_not_atomic(
        &mut short,
        &mut successor,
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(open_q / 2),
            exec_price: 100,
            fee_bps: 0,
        },
        true,
    );

    assert_eq!(result, Err(V16Error::LockActive));
}

#[test]
fn v16_quantity_adl_price_and_funding_accrual_remain_zero_sum() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 223);
    let mut short_header = account_fixture(1, 224);
    let open_q = 12 * POS_SCALE;
    let reduction_q = 3 * POS_SCALE;

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 100_000_000).unwrap();
        market.deposit_not_atomic(&mut short, 100_000_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(open_q),
                    exec_price: FUNDING_COUNTER_PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: reduction_q,
                },
            )
            .unwrap();
        let long_cert = market.full_account_refresh_not_atomic(&mut long).unwrap();
        let short_cert = market.full_account_refresh_not_atomic(&mut short).unwrap();
        assert_eq!(
            (
                short_cert.certified_initial_req,
                short_cert.certified_maintenance_req,
                short_cert.certified_worst_case_loss,
            ),
            (
                long_cert.certified_initial_req,
                long_cert.certified_maintenance_req,
                long_cert.certified_worst_case_loss,
            ),
            "equal effective exposures must receive equal health requirements after quantity ADL"
        );
        market
            .accrue_asset_to_not_atomic(
                0,
                2,
                FUNDING_COUNTER_PRICE + 1,
                FUNDING_COUNTER_RATE_E9,
                true,
            )
            .unwrap();
        market.markets[0].engine.asset.raw_oracle_target_price =
            V16PodU64::new(FUNDING_COUNTER_PRICE + 1);
    }

    let asset = markets[0].engine.asset.try_to_runtime().unwrap();
    let scaled = (ADL_ONE * 3 / 4) as i128;
    assert_eq!(asset.k_long, ADL_ONE as i128);
    assert_eq!(asset.k_short, -scaled);
    assert_eq!(
        asset.f_long_num,
        -(FUNDING_COUNTER_ATOMS_PER_SLOT as i128 * ADL_ONE as i128)
    );
    assert_eq!(
        asset.f_short_num,
        FUNDING_COUNTER_ATOMS_PER_SLOT as i128 * scaled
    );

    let total_value = |long: &PortfolioAccountV16Account,
                       short: &PortfolioAccountV16Account|
     -> i128 {
        long.capital.get() as i128 + long.pnl.get() + short.capital.get() as i128 + short.pnl.get()
    };
    let value_before = total_value(&long_header, &short_header);
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
                    size_q: -signed_q(reduction_q),
                    exec_price: FUNDING_COUNTER_PRICE + 1,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }
    assert_eq!(total_value(&long_header, &short_header), value_before);

    let reduced_asset = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reduced_asset.oi_eff_long_q, 6 * POS_SCALE);
    assert_eq!(reduced_asset.oi_eff_short_q, 6 * POS_SCALE);
    assert_eq!(
        long_header.legs[0].try_to_runtime().unwrap().basis_pos_q,
        signed_q(6 * POS_SCALE)
    );
    assert_eq!(
        short_header.legs[0].try_to_runtime().unwrap().basis_pos_q,
        -signed_q(8 * POS_SCALE),
        "the ADL-scaled short must remove four raw lots for three effective lots"
    );

    let value_before_continuation = total_value(&long_header, &short_header);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .accrue_asset_to_not_atomic(
                0,
                3,
                FUNDING_COUNTER_PRICE + 2,
                FUNDING_COUNTER_RATE_E9,
                true,
            )
            .unwrap();
        market.markets[0].engine.asset.raw_oracle_target_price =
            V16PodU64::new(FUNDING_COUNTER_PRICE + 2);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.full_account_refresh_not_atomic(&mut long).unwrap();
        market.full_account_refresh_not_atomic(&mut short).unwrap();
    }
    assert_eq!(
        total_value(&long_header, &short_header),
        value_before_continuation,
        "future price/funding accrual must remain zero-sum after the partial ADL reduction"
    );
}

#[test]
fn v16_post_quantity_adl_bankrupt_effective_full_close_stays_live() {
    const PRICE: u64 = 1_000_000;
    const OPEN_Q: u128 = 12 * POS_SCALE;
    const REDUCTION_Q: u128 = 3 * POS_SCALE;

    let (mut header, mut markets) = funding_market_fixture(PRICE);
    let mut long_header = account_fixture(1, 227);
    let mut short_header = account_fixture(1, 228);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 100_000_000).unwrap();
        market.deposit_not_atomic(&mut short, 13_000_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(OPEN_Q),
                    exec_price: PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: REDUCTION_Q,
                },
            )
            .unwrap();
        market
            .accrue_asset_to_not_atomic(0, 2, PRICE + 900_000, 0, true)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(0, 3, PRICE + 1_800_000, 0, true)
            .unwrap();
        market.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(PRICE + 1_800_000);
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let outcome = market
        .liquidate_account_not_atomic(&mut short, LiquidationRequestV16 { asset_index: 0 })
        .expect("the full live exposure must remain liquidatable after quantity ADL");

    assert_eq!(outcome.closed_q, OPEN_Q - REDUCTION_Q);
    assert!(active_bitmap_is_empty(
        short.header.active_bitmap.map(V16PodU64::get)
    ));
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.oi_eff_long_q, 0);
    assert_eq!(asset.oi_eff_short_q, 0);
    market.validate_shape().unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_recovery_pair_close_clamps_stale_work_to_dual_adl_effective_oi() {
    const PRICE: u64 = 100;
    const OPEN_Q: u128 = 2 * POS_SCALE;
    const FIRST_REDUCE_Q: u128 = POS_SCALE / 100;
    const SECOND_REDUCE_Q: u128 = POS_SCALE / 100;

    let (mut header, mut markets) = market_fixture(1, PRICE);
    let mut long_header = account_fixture(1, 229);
    let mut short_header = account_fixture(1, 230);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 10_000).unwrap();
        market.deposit_not_atomic(&mut short, 10_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(OPEN_Q),
                    exec_price: PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: FIRST_REDUCE_Q,
                },
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut short,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: SECOND_REDUCE_Q,
                },
            )
            .unwrap();
    }

    let before = markets[0].engine.asset.try_to_runtime().unwrap();
    let long_raw_q = long_header.legs[0]
        .try_to_runtime()
        .unwrap()
        .basis_pos_q
        .unsigned_abs();
    let short_raw_q = short_header.legs[0]
        .try_to_runtime()
        .unwrap()
        .basis_pos_q
        .unsigned_abs();
    assert!(before.a_long < ADL_ONE && before.a_short < ADL_ONE);
    assert_eq!(before.oi_eff_long_q, before.oi_eff_short_q);
    assert!(long_raw_q > before.oi_eff_long_q);
    assert!(short_raw_q > before.oi_eff_short_q);
    let effective_q = before.oi_eff_long_q;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.force_asset_recovery_not_atomic(0, 1).unwrap();
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let landed_q = market
        .force_close_recovery_pair_not_atomic(
            &mut long,
            &mut short,
            0,
            effective_q.checked_add(1).unwrap(),
        )
        .expect("stale Recovery work must clamp to canonical effective OI");

    assert_eq!(landed_q, effective_q);
    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.oi_eff_long_q, 0);
    assert_eq!(after.oi_eff_short_q, 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

/// The clamp has two independent families of bound: the two *per-leg*
/// effective quantities and the two *side* effective OI totals. Upstream's own
/// fixture cannot tell them apart — with one leg per side all four numbers are
/// equal, so dropping either pair leaves the result unchanged.
///
/// This puts a second long leg on the asset, so `oi_eff_long_q` is strictly
/// larger than the closing leg's own effective quantity. The pair close must
/// then be bounded by the *pair*, not by the side total: a budget of
/// `u128::MAX` may land only account A's own effective size, leaving account
/// B's leg untouched. Without the per-leg bound the clamp would resolve to the
/// side OI, ask for more than A holds, and the engine would refuse the whole
/// close.
#[test]
fn v16_recovery_pair_close_clamps_to_the_pair_not_the_side_oi() {
    const PRICE: u64 = 100;
    let (mut header, mut markets) = market_fixture(1, PRICE);
    let mut a_header = account_fixture(1, 240);
    let mut b_header = account_fixture(1, 241);
    let mut c_header = account_fixture(1, 242);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut a = PortfolioV16ViewMut::new(&mut a_header);
        let mut b = PortfolioV16ViewMut::new(&mut b_header);
        let mut c = PortfolioV16ViewMut::new(&mut c_header);
        market.deposit_not_atomic(&mut a, 100_000).unwrap();
        market.deposit_not_atomic(&mut b, 100_000).unwrap();
        market.deposit_not_atomic(&mut c, 100_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut a,
                &mut c,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(2 * POS_SCALE),
                    exec_price: PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut b,
                &mut c,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POS_SCALE),
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
                    reduce_q: POS_SCALE / 100,
                },
            )
            .unwrap();
    }

    let before = markets[0].engine.asset.try_to_runtime().unwrap();
    let a_raw_q = a_header.legs[0]
        .try_to_runtime()
        .unwrap()
        .basis_pos_q
        .unsigned_abs();
    // The long side took no haircut, so A's effective size is its raw basis —
    // and it is strictly below the side total, which also carries B's leg.
    assert_eq!(before.a_long, ADL_ONE);
    assert!(a_raw_q < before.oi_eff_long_q);
    let b_remaining_q = before.oi_eff_long_q - a_raw_q;
    assert!(b_remaining_q > 0);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.force_asset_recovery_not_atomic(0, 1).unwrap();
    let mut a = PortfolioV16ViewMut::new(&mut a_header);
    let mut c = PortfolioV16ViewMut::new(&mut c_header);
    let landed_q = market
        .force_close_recovery_pair_not_atomic(&mut a, &mut c, 0, u128::MAX)
        .expect("an unbounded budget must clamp to the pair, not the side OI");

    assert_eq!(landed_q, a_raw_q);
    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.oi_eff_long_q, b_remaining_q);
    assert_eq!(after.oi_eff_short_q, b_remaining_q);
    market.validate_shape().unwrap();
    a.validate_with_market(&market.as_view()).unwrap();
    c.validate_with_market(&market.as_view()).unwrap();
}

/// Upstream `ce590d9b` ("Fix Recovery pair close work clamping") adds
/// `force_close_recovery_pair_not_atomic`: an entry point that treats the
/// caller quantity as a *work budget* and clamps it to the canonical
/// effective quantities — `min(effective_a, effective_b, oi_eff_long_q,
/// oi_eff_short_q)` — before landing a Recovery pair close, so that a caller
/// sizing its request from the retained raw basis cannot land more close work
/// than actually exists.
///
/// This test locks the reason that clamp has to be written against effective
/// quantities rather than raw bases. On the ordinary trade path the engine
/// does not clamp an oversized Recovery close — it *refuses* it, via two
/// independent gates: `require_asset_risk_change_allowed`'s ADL-haircut check
/// (`a_long != ADL_ONE || a_short != ADL_ONE`) and `asset_risk_increase_gate`'s
/// lifecycle check (`lifecycle != Active`), either of which alone rejects the
/// over-request. So a caller that sizes a Recovery pair close from the
/// retained raw basis does not merely overshoot — it gets `LockActive` and
/// lands nothing, forever, because the raw basis stays above the canonical
/// effective OI for as long as the ADL haircut stands.
///
/// That is not hypothetical: `handle_force_close_abandoned_asset` in
/// percolator-prog (`src/v16_program.rs:9010-9015` @ `origin/main` 480e23a0)
/// clamps to `leg.basis_pos_q.unsigned_abs()` on both legs, so instruction
/// `ForceCloseAbandonedAsset` (wire tag 64) cannot close an ADL-haircut
/// Recovery pair at all. `force_close_recovery_pair_not_atomic` above is the
/// primitive that fixes it; this test pins the refusal that makes the raw
/// clamp unusable, so the two cannot drift back apart.
///
/// Both halves are locked here: the over-request must be refused with the
/// market left untouched, and the exact effective quantity must still drive
/// the pair to zero with every validator green.
#[test]
fn v16_recovery_pair_close_refuses_stale_work_beyond_effective_oi() {
    const PRICE: u64 = 100;
    const OPEN_Q: u128 = 2 * POS_SCALE;
    const FIRST_REDUCE_Q: u128 = POS_SCALE / 100;
    const SECOND_REDUCE_Q: u128 = POS_SCALE / 100;

    let (mut header, mut markets) = market_fixture(1, PRICE);
    let mut long_header = account_fixture(1, 229);
    let mut short_header = account_fixture(1, 230);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 10_000).unwrap();
        market.deposit_not_atomic(&mut short, 10_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(OPEN_Q),
                    exec_price: PRICE,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: FIRST_REDUCE_Q,
                },
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut short,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: SECOND_REDUCE_Q,
                },
            )
            .unwrap();
    }

    // The fixture must actually reach the state the clamp is about: both sides
    // ADL-haircut, so each retained raw basis overstates the real exposure.
    let before = markets[0].engine.asset.try_to_runtime().unwrap();
    let long_raw_q = long_header.legs[0]
        .try_to_runtime()
        .unwrap()
        .basis_pos_q
        .unsigned_abs();
    let short_raw_q = short_header.legs[0]
        .try_to_runtime()
        .unwrap()
        .basis_pos_q
        .unsigned_abs();
    assert!(before.a_long < ADL_ONE && before.a_short < ADL_ONE);
    assert_eq!(before.oi_eff_long_q, before.oi_eff_short_q);
    assert!(long_raw_q > before.oi_eff_long_q);
    assert!(short_raw_q > before.oi_eff_short_q);
    let effective_q = before.oi_eff_long_q;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.force_asset_recovery_not_atomic(0, 1).unwrap();
    let recovered = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(recovered.lifecycle, AssetLifecycleV16::Recovery);
    let exec_price = recovered.effective_price;
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    // Stale work budget: one quantum past the canonical effective OI. Upstream
    // clamps this down; this fork refuses it outright. Either way the close
    // must not land, and the refusal must leave the market untouched.
    let refused = market.execute_trade_with_fee_loss_stale_scoped_not_atomic(
        &mut short,
        &mut long,
        TradeRequestV16 {
            asset_index: 0,
            size_q: i128::try_from(effective_q.checked_add(1).unwrap()).unwrap(),
            exec_price,
            fee_bps: 0,
        },
        true,
    );
    assert_eq!(
        refused.map(|outcome| outcome.notional),
        Err(V16Error::LockActive),
        "stale Recovery work past the canonical effective OI must not land"
    );
    let untouched = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(untouched.oi_eff_long_q, effective_q);
    assert_eq!(untouched.oi_eff_short_q, effective_q);

    // The canonical effective quantity still closes the pair completely, so the
    // refusal above costs liveness nothing: nobody is stranded in Recovery.
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut short,
            &mut long,
            TradeRequestV16 {
                asset_index: 0,
                size_q: i128::try_from(effective_q).unwrap(),
                exec_price,
                fee_bps: 0,
            },
            true,
        )
        .expect("the canonical effective quantity must close the Recovery pair");
    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.oi_eff_long_q, 0);
    assert_eq!(after.oi_eff_short_q, 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_sub_minimum_drain_only_adl_leg_refreshes_and_exits() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 231);
    let mut short_header = account_fixture(1, 232);
    let open_q = 100 * POS_SCALE;
    let surviving_q = POS_SCALE;

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 100_000_000).unwrap();
        market.deposit_not_atomic(&mut short, 100_000_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(open_q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: open_q - surviving_q,
                },
            )
            .unwrap();
    }

    let asset = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.oi_eff_short_q, surviving_q);
    assert!(asset.a_short < percolator::MIN_A_SIDE);
    assert_eq!(asset.mode_short, SideModeV16::DrainOnly);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market
        .full_account_refresh_not_atomic(&mut short)
        .expect("a surviving sub-minimum-A DrainOnly leg must remain refreshable");
    market
        .rebalance_reduce_position_not_atomic(
            &mut short,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: surviving_q,
            },
        )
        .expect("the owner must be able to close the final effective DrainOnly exposure");

    assert!(active_bitmap_is_empty(
        short.header.active_bitmap.map(V16PodU64::get)
    ));
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.oi_eff_long_q, 0);
    assert_eq!(asset.oi_eff_short_q, 0);
    market.validate_shape().unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_exact_oi_cross_starts_reset_for_adl_basis_residue() {
    const SURVIVOR_Q: u128 = 13 * POS_SCALE;
    const MATCHED_Q: u128 = 10 * POS_SCALE;

    let (mut header, mut markets) = market_fixture(1, 1);
    let mut survivor_header = account_fixture(1, 20);
    let mut liquidated_header = account_fixture(1, 21);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut survivor = PortfolioV16ViewMut::new(&mut survivor_header);
        let mut liquidated = PortfolioV16ViewMut::new(&mut liquidated_header);
        market.deposit_not_atomic(&mut survivor, 100).unwrap();
        market.deposit_not_atomic(&mut liquidated, 100).unwrap();
    }

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.a_long = ADL_ONE * MATCHED_Q / SURVIVOR_Q;
    asset.oi_eff_long_q = MATCHED_Q;
    asset.oi_eff_short_q = MATCHED_Q;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    asset.loss_weight_sum_long = SURVIVOR_Q;
    asset.loss_weight_sum_short = MATCHED_Q;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    survivor_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: signed_q(SURVIVOR_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: SURVIVOR_Q,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    survivor_header.active_bitmap[0] = V16PodU64::new(1);
    survivor_header.health_cert.valid = 0;
    liquidated_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Short,
        basis_pos_q: -signed_q(MATCHED_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_short,
        f_snap: asset.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_short,
        loss_weight: MATCHED_Q,
        b_snap: asset.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_short,
        b_stale: false,
        stale: false,
    });
    liquidated_header.active_bitmap[0] = V16PodU64::new(1);
    liquidated_header.health_cert.valid = 0;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut survivor = PortfolioV16ViewMut::new(&mut survivor_header);
    let mut liquidated = PortfolioV16ViewMut::new(&mut liquidated_header);
    market.validate_shape().unwrap();
    survivor.validate_with_market(&market.as_view()).unwrap();
    liquidated.validate_with_market(&market.as_view()).unwrap();

    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut liquidated,
            &mut survivor,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(MATCHED_Q),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.oi_eff_long_q, 0);
    assert_eq!(after.oi_eff_short_q, 0);
    assert!(!survivor.header.legs[0].try_to_runtime().unwrap().active);
    assert!(!liquidated.header.legs[0].try_to_runtime().unwrap().active);
    assert_eq!(after.mode_long, SideModeV16::ResetPending);
    assert_eq!(after.loss_weight_sum_long, 0);
    market.validate_shape().unwrap();
    survivor.validate_with_market(&market.as_view()).unwrap();
    liquidated.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_recovery_forfeit_retains_loss_weight_until_opposite_positions_settle() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut first_header = account_fixture(1, 29);
    let mut second_header = account_fixture(1, 30);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut first = PortfolioV16ViewMut::new(&mut first_header);
        let mut second = PortfolioV16ViewMut::new(&mut second_header);
        market.deposit_not_atomic(&mut first, 1_000).unwrap();
        market.deposit_not_atomic(&mut second, 1_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut first,
                &mut second,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: POS_SCALE as i128,
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market.force_asset_recovery_not_atomic(0, 2).unwrap();
    }

    let first_side = first_header.legs[0].try_to_runtime().unwrap().side;
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut first = PortfolioV16ViewMut::new(&mut first_header);
        let outcome = market
            .forfeit_recovery_leg_not_atomic(&mut first, 0, u128::MAX)
            .expect("first Recovery exit must retain future loss absorption");
        assert!(!outcome.detached);
        let obligation = first.header.legs[0].try_to_runtime().unwrap();
        assert!(obligation.active);
        assert_eq!(obligation.basis_pos_q, 0);
        assert_ne!(obligation.loss_weight, 0);
        let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
        match first_side {
            SideV16::Long => {
                assert_eq!(asset.oi_eff_long_q, 0);
                assert_eq!(asset.pending_obligation_count_long, 1);
                assert_ne!(asset.oi_eff_short_q, 0);
            }
            SideV16::Short => {
                assert_eq!(asset.oi_eff_short_q, 0);
                assert_eq!(asset.pending_obligation_count_short, 1);
                assert_ne!(asset.oi_eff_long_q, 0);
            }
        }
        market.validate_shape().unwrap();
        first.validate_with_market(&market.as_view()).unwrap();
    }

    {
        // #189 dropped upstream's NonProgress crank block here because the fork
        // had no self-classifying crank to drive. Stage D now carries one, so the
        // block is restored in 3b76b794's own post form: a Recovery-asset leg the
        // opposite side has NOT yet released is refreshable from committed state,
        // keeps its zero-basis loss weight, and reaches a NoAction fixed point.
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut first = PortfolioV16ViewMut::new(&mut first_header);
        let result = market
            .permissionless_auto_crank_not_atomic(
                &mut first,
                AutoCrankWorkV16 {
                    now_slot: 2,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .expect("Recovery obligation must permit one committed-state refresh");
        assert_eq!(
            result.selected,
            AutoCrankPlanV16::RefreshAccount {
                asset_index: Some(0)
            }
        );
        assert_eq!(
            result.outcome,
            AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
        );
        let obligation = first.header.legs[0].try_to_runtime().unwrap();
        assert!(obligation.active);
        assert_eq!(obligation.basis_pos_q, 0);
        assert_ne!(obligation.loss_weight, 0);
        let fixed_point = market.permissionless_auto_crank_not_atomic(
            &mut first,
            AutoCrankWorkV16 {
                now_slot: 2,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        );
        assert_eq!(
            fixed_point,
            Ok(AutoCrankResultV16 {
                selected: AutoCrankPlanV16::NoAction,
                outcome: AutoCrankOutcomeV16::NoAction,
            })
        );
        market.validate_shape().unwrap();
        first.validate_with_market(&market.as_view()).unwrap();
    }

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut second = PortfolioV16ViewMut::new(&mut second_header);
        let outcome = market
            .forfeit_recovery_leg_not_atomic(&mut second, 0, u128::MAX)
            .expect("last non-pending opposite position can detach");
        assert!(outcome.detached);
        assert!(active_bitmap_is_empty(
            second.header.active_bitmap.map(V16PodU64::get)
        ));
        market.validate_shape().unwrap();
        second.validate_with_market(&market.as_view()).unwrap();
    }

    {
        let market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.header.mode = 2;
        market.header.recovery_reason = V16OptionalRecoveryReasonAccount::from_runtime(Some(
            PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
        ));
        market.validate_shape().unwrap();
    }

    {
        // #189 adapted this block to a second Recovery forfeit, because the fork
        // had no self-classifying crank to reach the release path. Stage D now
        // carries one, so the adaptation is retired and upstream's own form runs:
        // a market in global Recovery clears the released obligation FIRST, and
        // only then finalizes into Resolved.
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut first = PortfolioV16ViewMut::new(&mut first_header);
        let result = market
            .permissionless_auto_crank_not_atomic(
                &mut first,
                AutoCrankWorkV16 {
                    now_slot: 2,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .expect("global Recovery must first clear a released zero-basis obligation");
        assert_eq!(
            result.selected,
            AutoCrankPlanV16::RefreshAccount {
                asset_index: Some(0)
            }
        );
        assert_eq!(
            result.outcome,
            AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
        );
        assert!(active_bitmap_is_empty(
            first.header.active_bitmap.map(V16PodU64::get)
        ));
        let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
        assert_eq!(asset.pending_obligation_count_long, 0);
        assert_eq!(asset.pending_obligation_count_short, 0);
        assert_eq!(asset.loss_weight_sum_long, 0);
        assert_eq!(asset.loss_weight_sum_short, 0);
        market.validate_shape().unwrap();
        first.validate_with_market(&market.as_view()).unwrap();

        let finalized = market
            .permissionless_auto_crank_not_atomic(
                &mut first,
                AutoCrankWorkV16 {
                    now_slot: 2,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .expect("the next public crank must finalize Recovery");
        assert_eq!(finalized.selected, AutoCrankPlanV16::FinalizeRecovery);
        assert_eq!(finalized.outcome, AutoCrankOutcomeV16::RecoveryResolved);
        market.validate_shape().unwrap();
        first.validate_with_market(&market.as_view()).unwrap();
    }
}

#[test]
fn v16_auto_crank_clears_released_recovery_obligation_with_finalized_close() {
    use percolator::{CloseProgressLedgerV16, CloseProgressLedgerV16Account};

    for (b_short_num, expected_capital) in [(0, 7), (100_000_000_000_000_000, 4)] {
        let (mut header, mut markets) = market_fixture(1, 100);
        let mut account_header = account_fixture(1, 31);
        header.current_slot = V16PodU64::new(44);
        header.slot_last = V16PodU64::new(41);
        header.resolved_payout_blocker_count = V16PodU64::new(1);
        header.vault = V16PodU128::new(7);
        header.c_tot = V16PodU128::new(7);

        let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
        asset.lifecycle = AssetLifecycleV16::Recovery;
        asset.raw_oracle_target_price = 300;
        asset.effective_price = 300;
        asset.fund_px_last = 300;
        asset.slot_last = 41;
        asset.k_long = 200_000_000_000_000_000;
        asset.k_short = -200_000_000_000_000_000;
        asset.b_long_num = 100_000_000_000_000_000;
        asset.b_short_num = b_short_num;
        asset.oi_eff_long_q = 0;
        asset.oi_eff_short_q = 0;
        asset.stored_pos_count_long = 0;
        asset.stored_pos_count_short = 1;
        asset.pending_obligation_count_long = 0;
        asset.pending_obligation_count_short = 1;
        asset.loss_weight_sum_long = 0;
        asset.loss_weight_sum_short = 30_000;
        markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);

        account_header.capital = V16PodU128::new(7);
        account_header.residual_crystallized_loss_atoms_total = V16PodU128::new(3);
        account_header.active_bitmap[0] = V16PodU64::new(1);
        account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
            active: true,
            asset_index: 0,
            market_id: asset.market_id,
            side: SideV16::Short,
            basis_pos_q: 0,
            a_basis: ADL_ONE,
            k_snap: asset.k_short,
            f_snap: asset.f_short_num,
            kf_epoch_snap: 0,
            epoch_snap: asset.epoch_short,
            loss_weight: 30_000,
            b_snap: 0,
            b_rem: 0,
            b_epoch_snap: asset.epoch_short,
            b_stale: false,
            stale: false,
        });
        account_header.close_progress =
            CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
                active: true,
                finalized: true,
                canceled: false,
                close_id: 1,
                asset_index: 0,
                market_id: asset.market_id,
                domain_side: SideV16::Long,
                gross_loss_at_close_start: 3,
                drift_reference_slot: 41,
                max_close_slot: 141,
                b_loss_booked: 3,
                ..CloseProgressLedgerV16::EMPTY
            });

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        account.validate_with_market(&market.as_view()).unwrap();
        let summary = market
            .build_actionable_summary_at_slot(&account.as_view(), 44)
            .unwrap();
        assert!(summary.stale);
        let mut result = market
            .permissionless_auto_crank_not_atomic(
                &mut account,
                AutoCrankWorkV16 {
                    now_slot: 44,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .expect("a released Recovery obligation must be a successful bounded continuation");
        if b_short_num != 0 {
            assert_eq!(
                result.selected,
                AutoCrankPlanV16::SettleBChunk { asset_index: 0 }
            );
            assert_eq!(account.header.capital.get(), 7);
            assert_eq!(account.header.pnl.get(), -3);
            assert!(!active_bitmap_is_empty(
                account.header.active_bitmap.map(V16PodU64::get)
            ));
            result = market
                .permissionless_auto_crank_not_atomic(
                    &mut account,
                    AutoCrankWorkV16 {
                        now_slot: 44,
                        observations: &[],
                        resolved_close_fee_rate_per_slot: 0,
                    },
                )
                .expect("settled Recovery obligation must detach on the next bounded step");
        }
        assert_eq!(
            result.selected,
            AutoCrankPlanV16::RefreshAccount {
                asset_index: Some(0)
            }
        );
        assert!(active_bitmap_is_empty(
            account.header.active_bitmap.map(V16PodU64::get)
        ));
        assert_eq!(account.header.capital.get(), expected_capital);
        let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
        assert_eq!(asset.stored_pos_count_short, 0);
        assert_eq!(asset.pending_obligation_count_short, 0);
        assert_eq!(asset.loss_weight_sum_short, 0);
    }
}

#[test]
fn v16_auto_crank_refreshes_recovery_kf_without_forfeiting_position() {
    let (mut header, mut markets) = funding_market_fixture(FUNDING_COUNTER_PRICE);
    let mut long_header = account_fixture(1, 211);
    let mut short_header = account_fixture(1, 212);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        open_one_lot_pair(&mut market, &mut long, &mut short);
        market
            .accrue_asset_to_not_atomic(0, 2, FUNDING_COUNTER_PRICE, FUNDING_COUNTER_RATE_E9, true)
            .unwrap();
        market.force_asset_recovery_not_atomic(0, 2).unwrap();
    }

    let stale = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(stale.lifecycle, AssetLifecycleV16::Recovery);
    assert_eq!(stale.stale_account_count_long, 1);
    assert_eq!(stale.stale_account_count_short, 1);

    for (account_header, expected_side) in [
        (&mut long_header, SideV16::Long),
        (&mut short_header, SideV16::Short),
    ] {
        let position_before = account_header.legs[0].basis_pos_q.get();
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(account_header);
        let result = market
            .permissionless_auto_crank_not_atomic(
                &mut account,
                AutoCrankWorkV16 {
                    now_slot: 2,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .expect("Recovery K/F work must be refreshable without an oracle observation");
        assert_eq!(
            result.selected,
            AutoCrankPlanV16::RefreshAccount {
                asset_index: Some(0)
            }
        );
        assert_eq!(
            result.outcome,
            AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
        );
        let leg = account.header.legs[0].try_to_runtime().unwrap();
        let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
        assert!(leg.active);
        assert_eq!(leg.side, expected_side);
        assert_eq!(leg.basis_pos_q, position_before);
        assert_eq!(
            leg.kf_epoch_snap,
            match expected_side {
                SideV16::Long => asset.kf_epoch_long,
                SideV16::Short => asset.kf_epoch_short,
            }
        );
        assert_eq!(asset.lifecycle, AssetLifecycleV16::Recovery);
        market.validate_shape().unwrap();
        account.validate_with_market(&market.as_view()).unwrap();
    }

    let settled = markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(settled.stale_account_count_long, 0);
    assert_eq!(settled.stale_account_count_short, 0);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: -signed_q(POS_SCALE),
                exec_price: FUNDING_COUNTER_PRICE,
                fee_bps: 0,
            },
            true,
        )
        .expect("settled Recovery positions must retain their matched owner exit");
    assert!(active_bitmap_is_empty(
        long.header.active_bitmap.map(V16PodU64::get)
    ));
    assert!(active_bitmap_is_empty(
        short.header.active_bitmap.map(V16PodU64::get)
    ));
}

// COVERAGE CONTROL for 8fc8e836's OTHER call site. Upstream's own fixture
// (v16_auto_crank_clears_released_recovery_obligation_with_finalized_close)
// drives a Live-mode market whose ASSET is in Recovery, so it exercises only the
// second of the two sites this commit rewrote. A mutation that replaced the
// forfeit call in the Recovery-MARKET-mode early return with a bare clear_leg
// left all 278 tests green, so that site -- which decides whether an obligation
// is settled before Recovery is finalized -- was uncovered.
//
// Recovery finalization is irreversible: resolving over a still-owing leg would
// strand it, its stored_pos_count, its pending_obligation_count and its
// loss_weight_sum on the far side of the transition. This pins that the crank
// settles FIRST and does not finalize on that step.
#[test]
fn v16_auto_crank_settles_released_recovery_obligation_before_finalizing_recovery() {
    for (b_short_num, expected_capital) in [(0, 7), (100_000_000_000_000_000, 4)] {
        let (mut header, mut markets) = market_fixture(1, 100);
        let mut account_header = account_fixture(1, 31);
        header.current_slot = V16PodU64::new(44);
        header.slot_last = V16PodU64::new(41);
        header.resolved_payout_blocker_count = V16PodU64::new(1);
        header.vault = V16PodU128::new(7);
        header.c_tot = V16PodU128::new(7);
        header.mode = 2;
        header.recovery_reason = V16OptionalRecoveryReasonAccount::from_runtime(Some(
            PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
        ));

        let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
        asset.lifecycle = AssetLifecycleV16::Recovery;
        asset.raw_oracle_target_price = 300;
        asset.effective_price = 300;
        asset.fund_px_last = 300;
        asset.slot_last = 41;
        asset.k_long = 200_000_000_000_000_000;
        asset.k_short = -200_000_000_000_000_000;
        asset.b_long_num = 100_000_000_000_000_000;
        asset.b_short_num = b_short_num;
        asset.oi_eff_long_q = 0;
        asset.oi_eff_short_q = 0;
        asset.stored_pos_count_long = 0;
        asset.stored_pos_count_short = 1;
        asset.pending_obligation_count_long = 0;
        asset.pending_obligation_count_short = 1;
        asset.loss_weight_sum_long = 0;
        asset.loss_weight_sum_short = 30_000;
        markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);

        account_header.capital = V16PodU128::new(7);
        account_header.residual_crystallized_loss_atoms_total = V16PodU128::new(3);
        account_header.active_bitmap[0] = V16PodU64::new(1);
        account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
            active: true,
            asset_index: 0,
            market_id: asset.market_id,
            side: SideV16::Short,
            basis_pos_q: 0,
            a_basis: ADL_ONE,
            k_snap: asset.k_short,
            f_snap: asset.f_short_num,
            kf_epoch_snap: 0,
            epoch_snap: asset.epoch_short,
            loss_weight: 30_000,
            b_snap: 0,
            b_rem: 0,
            b_epoch_snap: asset.epoch_short,
            b_stale: false,
            stale: false,
        });
        account_header.close_progress =
            CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
                active: true,
                finalized: true,
                canceled: false,
                close_id: 1,
                asset_index: 0,
                market_id: asset.market_id,
                domain_side: SideV16::Long,
                gross_loss_at_close_start: 3,
                drift_reference_slot: 41,
                max_close_slot: 141,
                b_loss_booked: 3,
                ..CloseProgressLedgerV16::EMPTY
            });

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        account.validate_with_market(&market.as_view()).unwrap();
        let result = market
            .permissionless_auto_crank_not_atomic(
                &mut account,
                AutoCrankWorkV16 {
                    now_slot: 44,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .expect("a released Recovery obligation must be a successful bounded continuation");
        assert_eq!(
            result.selected,
            AutoCrankPlanV16::RefreshAccount {
                asset_index: Some(0)
            },
            "the obligation step must be taken INSTEAD of finalizing recovery"
        );
        assert_eq!(
            market.header.mode, 2,
            "recovery must not be finalized over an obligation on this step"
        );
        assert!(active_bitmap_is_empty(
            account.header.active_bitmap.map(V16PodU64::get)
        ));
        assert_eq!(account.header.capital.get(), expected_capital);
        let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
        assert_eq!(asset.stored_pos_count_short, 0);
        assert_eq!(asset.pending_obligation_count_short, 0);
        assert_eq!(asset.loss_weight_sum_short, 0);
    }
}

#[test]
fn v16_exact_oi_unilateral_reduce_starts_reset_for_adl_basis_residue() {
    const SURVIVOR_Q: u128 = 13 * POS_SCALE;
    const MATCHED_Q: u128 = 10 * POS_SCALE;

    let (mut header, mut markets) = market_fixture(1, 1);
    let mut survivor_header = account_fixture(1, 22);
    let mut counterparty_header = account_fixture(1, 23);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut survivor = PortfolioV16ViewMut::new(&mut survivor_header);
        let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
        market.deposit_not_atomic(&mut survivor, 100).unwrap();
        market.deposit_not_atomic(&mut counterparty, 100).unwrap();
    }

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.a_long = ADL_ONE * MATCHED_Q / SURVIVOR_Q;
    asset.oi_eff_long_q = MATCHED_Q;
    asset.oi_eff_short_q = MATCHED_Q;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    asset.loss_weight_sum_long = SURVIVOR_Q;
    asset.loss_weight_sum_short = MATCHED_Q;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    survivor_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: signed_q(SURVIVOR_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: SURVIVOR_Q,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    survivor_header.active_bitmap[0] = V16PodU64::new(1);
    survivor_header.health_cert.valid = 0;
    counterparty_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Short,
        basis_pos_q: -signed_q(MATCHED_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_short,
        f_snap: asset.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_short,
        loss_weight: MATCHED_Q,
        b_snap: asset.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_short,
        b_stale: false,
        stale: false,
    });
    counterparty_header.active_bitmap[0] = V16PodU64::new(1);
    counterparty_header.health_cert.valid = 0;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut survivor = PortfolioV16ViewMut::new(&mut survivor_header);
    let counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
    market.validate_shape().unwrap();
    survivor.validate_with_market(&market.as_view()).unwrap();
    counterparty
        .validate_with_market(&market.as_view())
        .unwrap();

    // Upstream refreshes through the self-classifying auto-crank with one
    // observation; this fork's permissionless crank takes the same observation
    // as an explicit Refresh request.
    market
        .permissionless_crank_not_atomic(
            &mut survivor,
            PermissionlessCrankRequestV16 {
                now_slot: 1,
                asset_index: 0,
                effective_price: 1,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::Refresh,
            },
        )
        .unwrap();
    market
        .rebalance_reduce_position_not_atomic(
            &mut survivor,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: MATCHED_Q,
            },
        )
        .unwrap();

    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.oi_eff_long_q, 0);
    assert_eq!(after.oi_eff_short_q, 0);
    assert!(!survivor.header.legs[0].try_to_runtime().unwrap().active);
    assert_eq!(after.mode_long, SideModeV16::ResetPending);
    assert_eq!(after.mode_short, SideModeV16::ResetPending);
    market.validate_shape().unwrap();
    survivor.validate_with_market(&market.as_view()).unwrap();
    counterparty
        .validate_with_market(&market.as_view())
        .unwrap();
}
// Coverage for the SECOND call site upstream 65e7a7cd adds. That commit places
// begin_zero_oi_residue_resets on BOTH unilateral reduction routes -- rebalance
// and liquidation -- but ships only a rebalance test
// (v16_exact_oi_unilateral_reduce_starts_reset_for_adl_basis_residue). Measured
// at av 8eb7142a and at this fork: deleting the liquidation call leaves both
// suites fully green, so the keeper-driven route was reached but never asserted.
// This is the liquidation analogue of the rebalance test and closes that gap.
/// The **Flip** route of `apply_position_delta_with_lookup_inner` — the branch
/// taken when a position reverses sign in one fill, clearing the old leg and
/// attaching a new one on the opposite side.
///
/// It was reached by **zero tests and zero proofs**. Measured on `3980add64`,
/// three steps, because a silent probe alone proves nothing:
///   1. the enclosing function IS reached — a probe at the route classifier
///      fires with `route=Clear`;
///   2. the Flip line itself compiles and panics work there — a sibling
///      `Resize` poison at the identical line fires 3x, `cargo build` rc 0;
///   3. a `panic!` at the Flip branch fires **zero times across 288 plain and
///      337 fuzz tests**.
///
/// `panic!` rather than `Err`: an `Err` can be swallowed by a caller, which
/// makes a green suite ambiguous when the claim is "this branch is never taken".
///
/// This test drives a genuine reversal through the real matched-trade mutator:
/// A is long 1 lot against B short 1 lot, then a 2-lot trade in the opposite
/// direction takes A to -1 and B to +1. Both accounts flip on the same fill,
/// so one fixture covers the route from both sides.
#[test]
fn v16_matched_trade_reversing_a_position_takes_the_flip_route() {
    let (mut header, mut markets) = market_fixture(1, 1_000_000);
    let mut a_header = account_fixture(1, 41);
    let mut b_header = account_fixture(1, 42);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    {
        let mut a = PortfolioV16ViewMut::new(&mut a_header);
        let mut b = PortfolioV16ViewMut::new(&mut b_header);
        market.deposit_not_atomic(&mut a, 100_000_000).unwrap();
        market.deposit_not_atomic(&mut b, 100_000_000).unwrap();
        // A long 1 lot / B short 1 lot.
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut a,
                &mut b,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POS_SCALE),
                    exec_price: 1_000_000,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }
    {
        let a_leg = a_header.legs[0].try_to_runtime().unwrap();
        let b_leg = b_header.legs[0].try_to_runtime().unwrap();
        assert_eq!(a_leg.side, SideV16::Long, "A opens long");
        assert_eq!(b_leg.side, SideV16::Short, "B opens short");
        assert_eq!(a_leg.basis_pos_q, signed_q(POS_SCALE));
        assert_eq!(b_leg.basis_pos_q, -signed_q(POS_SCALE));
    }

    // The reversal: B takes the long side for 2 lots, so A goes +1 -> -1 and
    // B goes -1 -> +1. Both cross zero in a single fill, which is exactly the
    // Flip route's precondition (`current.signum() != new.signum()`, neither zero).
    {
        let mut a = PortfolioV16ViewMut::new(&mut a_header);
        let mut b = PortfolioV16ViewMut::new(&mut b_header);
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut b,
                &mut a,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(2 * POS_SCALE),
                    exec_price: 1_000_000,
                    fee_bps: 0,
                },
                true,
            )
            .expect("the reversing fill must be accepted");
    }

    let a_leg = a_header.legs[0].try_to_runtime().unwrap();
    let b_leg = b_header.legs[0].try_to_runtime().unwrap();
    assert_eq!(a_leg.side, SideV16::Short, "A flipped long -> short");
    assert_eq!(b_leg.side, SideV16::Long, "B flipped short -> long");
    assert_eq!(
        a_leg.basis_pos_q,
        -signed_q(POS_SCALE),
        "A holds exactly the reversed remainder"
    );
    assert_eq!(
        b_leg.basis_pos_q,
        signed_q(POS_SCALE),
        "B holds exactly the reversed remainder"
    );
    assert!(a_leg.active && b_leg.active, "both legs stay attached");
    assert_eq!(
        a_leg.asset_index, 0,
        "the flipped leg stays on the same asset"
    );
    market
        .validate_shape()
        .expect("aggregate conservation holds across the flip");
}

#[test]
fn v16_exact_oi_liquidation_close_starts_reset_for_adl_basis_residue() {
    const SURVIVOR_Q: u128 = 13 * POS_SCALE;
    const MATCHED_Q: u128 = 10 * POS_SCALE;

    let (mut header, mut markets) = market_fixture(1, 1);
    let mut survivor_header = account_fixture(1, 22);
    let mut counterparty_header = account_fixture(1, 23);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
        market.deposit_not_atomic(&mut counterparty, 100).unwrap();
    }

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.a_long = ADL_ONE * MATCHED_Q / SURVIVOR_Q;
    asset.oi_eff_long_q = MATCHED_Q;
    asset.oi_eff_short_q = MATCHED_Q;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    asset.loss_weight_sum_long = SURVIVOR_Q;
    asset.loss_weight_sum_short = MATCHED_Q;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    // Survivor holds a 13-lot basis whose effective size is 10 lots (a_long =
    // 10/13). It carries zero capital, so maintenance (100% of notional) is
    // unmet and the engine-selected close is the whole effective leg.
    survivor_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: signed_q(SURVIVOR_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: SURVIVOR_Q,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    survivor_header.active_bitmap[0] = V16PodU64::new(1);
    survivor_header.health_cert.valid = 0;
    counterparty_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Short,
        basis_pos_q: -signed_q(MATCHED_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_short,
        f_snap: asset.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_short,
        loss_weight: MATCHED_Q,
        b_snap: asset.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_short,
        b_stale: false,
        stale: false,
    });
    counterparty_header.active_bitmap[0] = V16PodU64::new(1);
    counterparty_header.health_cert.valid = 0;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut survivor = PortfolioV16ViewMut::new(&mut survivor_header);
    let counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
    market.validate_shape().unwrap();
    survivor.validate_with_market(&market.as_view()).unwrap();
    counterparty
        .validate_with_market(&market.as_view())
        .unwrap();

    market
        .permissionless_crank_not_atomic(
            &mut survivor,
            PermissionlessCrankRequestV16 {
                now_slot: 1,
                asset_index: 0,
                effective_price: 1,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::Refresh,
            },
        )
        .unwrap();
    let outcome = market
        .liquidate_account_not_atomic(&mut survivor, LiquidationRequestV16 { asset_index: 0 })
        .unwrap();

    // The close exhausts effective OI on both sides; the residue reset that
    // 65e7a7cd adds must then arm ResetPending so the auto-crank can retire the
    // stranded 3-lot ADL basis residue.
    assert_eq!(outcome.closed_q, MATCHED_Q);
    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.oi_eff_long_q, 0);
    assert_eq!(after.oi_eff_short_q, 0);
    assert_eq!(after.mode_long, SideModeV16::ResetPending);
    assert_eq!(after.mode_short, SideModeV16::ResetPending);
    market.validate_shape().unwrap();
    survivor.validate_with_market(&market.as_view()).unwrap();
    counterparty
        .validate_with_market(&market.as_view())
        .unwrap();
}

#[test]
fn v16_adl_reduced_basis_caps_exit_to_effective_oi_then_detaches_residue() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 24);

    // A partial ADL can leave a winner's stored basis larger than the side's
    // remaining effective OI. This is the exact state reached by the public
    // wrapper regression: basis=2 lots, matched effective OI=1 lot.
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = POS_SCALE;
    asset.oi_eff_short_q = POS_SCALE;
    asset.a_long = ADL_ONE / 2;
    asset.loss_weight_sum_long = 2 * POS_SCALE;
    asset.loss_weight_sum_short = POS_SCALE;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: (2 * POS_SCALE) as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: 2 * POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();

    let reduced = market
        .rebalance_reduce_position_not_atomic(
            &mut account,
            RebalanceRequestV16 {
                asset_index: 0,
                reduce_q: 2 * POS_SCALE,
            },
        )
        .expect("max-work exit must clamp to matched effective OI");
    assert_eq!(reduced.reduced_q, POS_SCALE);
    assert!(!account.header.legs[0].try_to_runtime().unwrap().active);
    let reset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reset.oi_eff_long_q, 0);
    assert_eq!(reset.oi_eff_short_q, 0);
    assert_eq!(reset.mode_long, SideModeV16::ResetPending);
    assert_eq!(reset.mode_short, SideModeV16::ResetPending);

    assert_eq!(account.header.active_bitmap[0].get(), 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_post_quantity_adl_recovery_forfeit_retires_only_effective_oi() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 229);
    let mut short_header = account_fixture(1, 230);
    let open_q = 12 * POS_SCALE;
    let reduction_q = 3 * POS_SCALE;
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 100_000_000).unwrap();
        market.deposit_not_atomic(&mut short, 100_000_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(open_q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        market
            .rebalance_reduce_position_not_atomic(
                &mut long,
                RebalanceRequestV16 {
                    asset_index: 0,
                    reduce_q: reduction_q,
                },
            )
            .unwrap();
        market.force_asset_recovery_not_atomic(0, 2).unwrap();
    }

    assert_eq!(
        short_header.legs[0]
            .try_to_runtime()
            .unwrap()
            .basis_pos_q
            .unsigned_abs(),
        open_q,
        "quantity ADL must retain raw K/F basis until settlement"
    );
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let outcome = market
        .forfeit_recovery_leg_not_atomic(&mut short, 0, u128::MAX)
        .expect("post-ADL recovery forfeit must consume live OI rather than stale raw basis");

    assert!(!outcome.detached);
    let obligation = short.header.legs[0].try_to_runtime().unwrap();
    assert_eq!(obligation.basis_pos_q, 0);
    assert_ne!(obligation.loss_weight, 0);
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.oi_eff_short_q, 0);
    assert_eq!(asset.oi_eff_long_q, open_q - reduction_q);
    assert_eq!(asset.pending_obligation_count_short, 1);
    market.validate_shape().unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_public_scoped_trade_preserves_unrelated_loss_stale_summary() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut long_header = account_fixture(2, 209);
    let mut short_header = account_fixture(2, 210);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(9);
    header.loss_stale_active = 1;
    let mut current_asset = markets[0].engine.asset.try_to_runtime().unwrap();
    current_asset.slot_last = 10;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&current_asset);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let outcome = market
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
        .expect("unrelated loss-stale summary must not block a locally current trade");

    assert_eq!(outcome.notional, 100);
    assert_eq!(market.header.loss_stale_active, 1);
    assert_eq!(market.markets[0].engine.asset.slot_last.get(), 10);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_batch_trade_is_bounded_by_configured_portfolio_asset_cap() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 205);
    let mut short_header = account_fixture(1, 206);
    let requests = [
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 0,
        },
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 0,
        },
    ];
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000).unwrap();

    let res = market.execute_batch_with_fee_loss_stale_scoped_not_atomic(
        &mut long, &mut short, &requests, true,
    );

    assert_eq!(res, Err(V16Error::InvalidConfig));
}

#[test]
fn v16_view_dynamic_market_slots_can_be_activated_without_runtime_vec_engine() {
    let (mut header, mut markets) = market_fixture(3, 100);
    let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    view.validate_shape().unwrap();

    assert_eq!(
        view.header
            .config
            .try_to_runtime()
            .unwrap()
            .max_market_slots,
        3
    );
    assert_eq!(view.markets.len(), 3);
    assert_eq!(view.markets[2].engine.asset.market_id.get(), 3);
    assert_eq!(view.markets[2].engine.asset.effective_price.get(), 100);
}

#[test]
fn v16_public_raw_oracle_target_update_is_value_neutral_and_lifecycle_gated() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();
    let oracle_epoch_before = header.oracle_epoch.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .set_asset_raw_oracle_target_not_atomic(0, 111)
        .unwrap();
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();

    assert_eq!(asset.raw_oracle_target_price, 111);
    assert_eq!(asset.effective_price, 100);
    assert_eq!(market.header.oracle_epoch.get(), oracle_epoch_before + 1);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    market
        .set_asset_raw_oracle_target_not_atomic(0, 111)
        .unwrap();
    assert_eq!(market.header.oracle_epoch.get(), oracle_epoch_before + 1);
    market.validate_shape().unwrap();
}

#[test]
fn v16_public_raw_oracle_target_batch_updates_distinct_assets_with_one_epoch() {
    let (mut header, mut markets) = market_fixture(3, 100);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();
    let oracle_epoch_before = header.oracle_epoch.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .set_asset_raw_oracle_targets_not_atomic(&[(0, 111), (1, 90), (2, 125)])
        .unwrap();

    assert_eq!(
        market.markets[0].engine.asset.raw_oracle_target_price.get(),
        111
    );
    assert_eq!(
        market.markets[1].engine.asset.raw_oracle_target_price.get(),
        90
    );
    assert_eq!(
        market.markets[2].engine.asset.raw_oracle_target_price.get(),
        125
    );
    assert_eq!(market.header.oracle_epoch.get(), oracle_epoch_before + 1);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);

    market
        .set_asset_raw_oracle_targets_not_atomic(&[(2, 125), (0, 111), (1, 90)])
        .unwrap();
    assert_eq!(market.header.oracle_epoch.get(), oracle_epoch_before + 1);
    assert_eq!(
        market.set_asset_raw_oracle_targets_not_atomic(&[(0, 112), (0, 113)]),
        Err(V16Error::InvalidConfig)
    );
    assert_eq!(
        market.markets[0].engine.asset.raw_oracle_target_price.get(),
        111
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_raw_oracle_target_only_change_invalidates_a_cached_health_cert() {
    // Regression for engine #107 / #93: a target-only push (no accrual, no
    // effective_price move) must invalidate any health cert taken while the
    // old target was in force, because target/effective lag -- and therefore
    // risk -- has grown even though the cert's own numbers are stale-blind
    // to it. We drive this through a real cert-gated not_atomic API
    // (charge_account_backing_fee_not_atomic) rather than reading the epoch
    // counter directly, so the test fails the way an exploit would: a stale
    // cert being admitted to authorize a financial action.
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 30);
    header.vault = V16PodU128::new(100);
    header.c_tot = V16PodU128::new(100);
    account_header.capital = V16PodU128::new(100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .deposit_fresh_counterparty_backing_not_atomic(0, 1, 10)
        .unwrap();

    // Cert taken while the target is still 100 (matches effective_price, no
    // lag) and current against every header epoch at the moment it's minted.
    account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        certified_equity: 100,
        certified_initial_req: 50,
        certified_maintenance_req: 40,
        cert_oracle_epoch: market.header.oracle_epoch.get(),
        cert_funding_epoch: market.header.funding_epoch.get(),
        cert_risk_epoch: market.header.risk_epoch.get(),
        cert_asset_set_epoch: market.header.asset_set_epoch.get(),
        active_bitmap_at_cert: V16_EMPTY_ACTIVE_BITMAP,
        valid: true,
        ..HealthCertV16::default()
    });
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    // Sanity: with the target unchanged, this exact cert is still admitted
    // (proves the setup is correct and the rejection below is caused
    // specifically by the target push, not some other staleness source).
    let vault_before = market.header.vault.get();
    let c_tot_before = market.header.c_tot.get();
    let insurance_before = market.header.insurance.get();
    let capital_before = account.header.capital.get();

    // Now push a target-only change: raw_oracle_target_price moves from 100
    // to 111 while effective_price (100) does not -- new target/effective
    // lag with zero accrual in between.
    market
        .set_asset_raw_oracle_target_not_atomic(0, 111)
        .unwrap();

    // The cert minted above is now stale: it was current for the pre-push
    // oracle_epoch and must be rejected, not silently admitted under grown
    // target/effective lag.
    let err = market.charge_account_backing_fee_not_atomic(&mut account, 0, 6, 1, 4);
    assert_eq!(
        err,
        Err(V16Error::Stale),
        "cached cert must be invalidated by a target-only oracle push"
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(account.header.capital.get(), capital_before);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_public_empty_asset_oracle_anchor_reset_rejects_any_group_position_state() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut other_asset = markets[1].engine.asset.try_to_runtime().unwrap();
    other_asset.oi_eff_long_q = POS_SCALE;
    other_asset.oi_eff_short_q = POS_SCALE;
    other_asset.stored_pos_count_long = 1;
    other_asset.stored_pos_count_short = 1;
    other_asset.loss_weight_sum_long = POS_SCALE;
    other_asset.loss_weight_sum_short = POS_SCALE;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&other_asset);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let res = market.reset_empty_asset_oracle_anchor_not_atomic(0, 123, 10);

    assert_eq!(res, Err(V16Error::LockActive));
    assert_eq!(market.markets[0].engine.asset.effective_price.get(), 100);
}

#[test]
fn v16_public_empty_asset_oracle_anchor_reset_is_value_neutral() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .reset_empty_asset_oracle_anchor_not_atomic(0, 123, 10)
        .unwrap();
    let asset = market.markets[0].engine.asset.try_to_runtime().unwrap();

    assert_eq!(asset.raw_oracle_target_price, 123);
    assert_eq!(asset.effective_price, 123);
    assert_eq!(asset.fund_px_last, 123);
    assert_eq!(asset.slot_last, 10);
    assert_eq!(market.header.current_slot.get(), 10);
    assert_eq!(market.header.slot_last.get(), 10);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    market.validate_shape().unwrap();
}

#[test]
fn v16_public_force_asset_recovery_freezes_mark_and_is_idempotent() {
    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .set_asset_raw_oracle_target_not_atomic(1, 150)
            .unwrap();
    }
    let asset_epoch_before = header.asset_set_epoch.get();
    let risk_epoch_before = header.risk_epoch.get();
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.force_asset_recovery_not_atomic(1, 2).unwrap();
    let asset = market.markets[1].engine.asset.try_to_runtime().unwrap();

    assert_eq!(asset.lifecycle, AssetLifecycleV16::Recovery);
    assert_eq!(asset.raw_oracle_target_price, asset.effective_price);
    assert_eq!(market.header.asset_set_epoch.get(), asset_epoch_before + 1);
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 1);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);

    market.force_asset_recovery_not_atomic(1, 2).unwrap();
    assert_eq!(market.header.asset_set_epoch.get(), asset_epoch_before + 1);
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 1);
    market.validate_shape().unwrap();
}

#[test]
fn v16_restart_empty_asset_preserves_domain_budget_for_nonzero_asset() {
    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.deposit_domain_insurance_not_atomic(2, 10).unwrap();
        market.force_asset_recovery_not_atomic(1, 2).unwrap();
    }
    let old_market_id = markets[1].engine.asset.market_id.get();
    let budget_before = markets[1].engine.insurance_domain_budget_long.get();
    let budget_total_before = header.insurance_domain_budget_remaining_total.get();
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .restart_empty_asset_preserving_insurance_budget_not_atomic(1, 222, 3)
        .unwrap();
    let asset = market.markets[1].engine.asset.try_to_runtime().unwrap();

    assert_eq!(asset.lifecycle, AssetLifecycleV16::Active);
    assert_ne!(asset.market_id, old_market_id);
    assert_eq!(asset.raw_oracle_target_price, 222);
    assert_eq!(
        market.markets[1].engine.insurance_domain_budget_long.get(),
        budget_before
    );
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        budget_total_before
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    market.validate_shape().unwrap();
}

#[test]
fn v16_restart_normalizes_only_inert_terminal_history() {
    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.deposit_domain_insurance_not_atomic(2, 10).unwrap();
        market.force_asset_recovery_not_atomic(1, 2).unwrap();
    }
    header.insurance = V16PodU128::new(0);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(0);
    markets[1].engine.insurance_domain_spent_long = V16PodU128::new(10);
    let mut historical_asset = markets[1].engine.asset.try_to_runtime().unwrap();
    historical_asset.k_long = -601 * ADL_ONE as i128;
    historical_asset.f_short_num = 17;
    historical_asset.k_epoch_start_long = -3;
    historical_asset.f_epoch_start_short_num = 5;
    historical_asset.social_loss_dust_long_num = 7;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&historical_asset);
    markets[1].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: 11,
            ..SourceCreditStateV16::EMPTY
        });
    let old_market_id = markets[1].engine.asset.market_id.get();
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();
    let remaining_before = header.insurance_domain_budget_remaining_total.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(market.validate_shape(), Ok(()));
    market
        .restart_empty_asset_preserving_insurance_budget_not_atomic(1, 222, 3)
        .unwrap();
    let asset = market.markets[1].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.lifecycle, AssetLifecycleV16::Active);
    assert_ne!(asset.market_id, old_market_id);
    assert_eq!(asset.effective_price, 222);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        remaining_before
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_budget_long.get(),
        0
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_spent_long.get(),
        0
    );
    assert_eq!(
        market.markets[1]
            .engine
            .source_credit_short
            .try_to_runtime()
            .unwrap(),
        SourceCreditStateV16::EMPTY
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_restart_rejects_remaining_insurance_budget_without_mutation() {
    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.deposit_domain_insurance_not_atomic(2, 10).unwrap();
        market.force_asset_recovery_not_atomic(1, 2).unwrap();
    }
    header.insurance = V16PodU128::new(6);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(6);
    markets[1].engine.insurance_domain_spent_long = V16PodU128::new(4);
    let vault_before = header.vault;
    let insurance_before = header.insurance;
    let remaining_before = header.insurance_domain_budget_remaining_total;
    let budget_before = markets[1].engine.insurance_domain_budget_long;
    let spent_before = markets[1].engine.insurance_domain_spent_long;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(
        market.restart_empty_asset_preserving_insurance_budget_not_atomic(1, 222, 3),
        Err(V16Error::LockActive)
    );
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.insurance, insurance_before);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total,
        remaining_before
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_budget_long,
        budget_before
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_spent_long,
        spent_before
    );
}

#[test]
fn v16_restart_rejects_active_asset() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(
        market.restart_empty_asset_preserving_insurance_budget_not_atomic(1, 222, 3),
        Err(V16Error::LockActive)
    );
}

/// 573c4e90 ships only a proof; this concrete twin pins the behaviour it adds:
/// one retirement clears a spent-only domain budget together with the rest of
/// the inert history, with no preparatory cleanup transition.
#[test]
fn v16_retire_clears_spent_only_domain_budget_in_one_transition() {
    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.deposit_domain_insurance_not_atomic(2, 10).unwrap();
        market.force_asset_recovery_not_atomic(1, 2).unwrap();
    }
    header.insurance = V16PodU128::new(0);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(0);
    markets[1].engine.insurance_domain_spent_long = V16PodU128::new(10);
    let mut historical_asset = markets[1].engine.asset.try_to_runtime().unwrap();
    historical_asset.k_short = 41;
    historical_asset.f_epoch_start_long_num = -9;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&historical_asset);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(market.validate_shape(), Ok(()));
    market.retire_empty_asset_not_atomic(1, 3).unwrap();
    let asset = market.markets[1].engine.asset.try_to_runtime().unwrap();
    assert_eq!(asset.lifecycle, AssetLifecycleV16::Retired);
    assert_eq!(asset.retired_slot, 3);
    assert_eq!(asset.k_short, 0);
    assert_eq!(asset.f_epoch_start_long_num, 0);
    assert_eq!(
        market.markets[1].engine.insurance_domain_budget_long.get(),
        0
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_spent_long.get(),
        0
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        0
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_retire_normalizes_only_inert_social_loss_audit_state() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.social_loss_remainder_long_num = SOCIAL_LOSS_DEN - 1;
    asset.social_loss_remainder_short_num = 1;
    asset.social_loss_dust_long_num = 1;
    asset.social_loss_dust_short_num = SOCIAL_LOSS_DEN - 1;
    asset.explicit_unallocated_loss_long = 7;
    asset.explicit_unallocated_loss_short = u128::MAX;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: 17 * BOUND_SCALE,
            credit_epoch: 9,
            ..SourceCreditStateV16::EMPTY
        });
    let vault_before = header.vault;
    let c_tot_before = header.c_tot;
    let insurance_before = header.insurance;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.retire_empty_asset_not_atomic(0, 1).unwrap();
    let retired = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(retired.lifecycle, AssetLifecycleV16::Retired);
    assert_eq!(retired.social_loss_remainder_long_num, 0);
    assert_eq!(retired.social_loss_remainder_short_num, 0);
    assert_eq!(retired.social_loss_dust_long_num, 0);
    assert_eq!(retired.social_loss_dust_short_num, 0);
    assert_eq!(retired.explicit_unallocated_loss_long, 0);
    assert_eq!(retired.explicit_unallocated_loss_short, 0);
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .try_to_runtime()
            .unwrap(),
        SourceCreditStateV16::EMPTY
    );
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.c_tot, c_tot_before);
    assert_eq!(market.header.insurance, insurance_before);
    market.validate_shape().unwrap();

    let (mut live_header, mut live_markets) = market_fixture(1, 100);
    let mut live_asset = live_markets[0].engine.asset.try_to_runtime().unwrap();
    live_asset.social_loss_dust_long_num = 1;
    live_asset.explicit_unallocated_loss_long = 1;
    live_asset.oi_eff_long_q = POS_SCALE;
    live_asset.oi_eff_short_q = POS_SCALE;
    live_asset.stored_pos_count_long = 1;
    live_asset.stored_pos_count_short = 1;
    live_asset.loss_weight_sum_long = POS_SCALE;
    live_asset.loss_weight_sum_short = POS_SCALE;
    live_markets[0].engine.asset = AssetStateV16Account::from_runtime(&live_asset);
    let slot_before = live_markets[0].engine;

    let mut live = MarketGroupV16ViewMut::new(&mut live_header, &mut live_markets);
    assert_eq!(
        live.retire_empty_asset_not_atomic(0, 1),
        Err(V16Error::LockActive)
    );
    assert_eq!(live.markets[0].engine, slot_before);
}

#[test]
fn v16_retire_rejects_live_provider_receivable_without_mutation() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let receivable_num = 19 * BOUND_SCALE;
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: receivable_num,
            provider_receivable_num: receivable_num,
            ..SourceCreditStateV16::EMPTY
        });
    markets[0].engine.backing_long = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id: 1,
        consumed_liened_backing_num: receivable_num,
        expiry_slot: 1,
        status: BackingBucketStatusV16::Expired,
        ..BackingBucketV16::EMPTY
    });
    let header_before = header;
    let slot_before = markets[0].engine;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(
        market.retire_empty_asset_not_atomic(0, 2),
        Err(V16Error::LockActive)
    );
    assert_eq!(*market.header, header_before);
    assert_eq!(market.markets[0].engine, slot_before);
}

#[test]
fn v16_canonicalize_retired_empty_asset_slot_clears_inert_domain_state() {
    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.retire_empty_asset_not_atomic(1, 3).unwrap();
    }
    let old_market_id = markets[1].engine.asset.market_id.get();
    let inert_empty_source = SourceCreditStateV16 {
        credit_epoch: 7,
        credit_rate_num: 0,
        ..SourceCreditStateV16::EMPTY
    };
    markets[1].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&inert_empty_source);
    markets[1].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&inert_empty_source);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .canonicalize_retired_empty_asset_slot_not_atomic(1)
        .unwrap();
    let asset = market.markets[1].engine.asset.try_to_runtime().unwrap();

    assert_eq!(asset.lifecycle, AssetLifecycleV16::Retired);
    assert_eq!(asset.market_id, old_market_id);
    assert_eq!(
        market.markets[1]
            .engine
            .source_credit_long
            .try_to_runtime()
            .unwrap(),
        SourceCreditStateV16::EMPTY
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    market.validate_shape().unwrap();
}

#[test]
fn v16_reused_market_slot_rejects_old_market_id_leg() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 16);
    let old_market_id = markets[0].engine.asset.market_id.get();
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.retire_empty_asset_not_atomic(0, 1).unwrap();
    }
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 200, 2)
        .unwrap();
    assert_ne!(markets[0].engine.asset.market_id.get(), old_market_id);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: old_market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: 0,
        f_snap: 0,
        kf_epoch_snap: 0,
        epoch_snap: 0,
        loss_weight: POS_SCALE,
        b_snap: 0,
        b_rem: 0,
        b_epoch_snap: 0,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    assert_eq!(
        market.full_account_refresh_not_atomic(&mut account),
        Err(V16Error::HiddenLeg),
        "stale legs from a retired market slot must not bind to the reactivated market"
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_retire_and_reactivate_empty_asset_after_source_credit_epoch_bump() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let old_market_id = markets[0].engine.asset.market_id.get();
    let recomputed_empty_source = SourceCreditStateV16 {
        credit_epoch: 2,
        ..SourceCreditStateV16::EMPTY
    };
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&recomputed_empty_source);
    markets[0].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&recomputed_empty_source);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.retire_empty_asset_not_atomic(0, 1).unwrap();
    assert_eq!(
        market.markets[0]
            .engine
            .asset
            .try_to_runtime()
            .unwrap()
            .lifecycle,
        AssetLifecycleV16::Retired
    );

    market
        .header
        .activate_empty_market_slot_not_atomic(0, &mut market.markets[0], 200, 2)
        .unwrap();
    assert_ne!(
        market.markets[0].engine.asset.market_id.get(),
        old_market_id
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .try_to_runtime()
            .unwrap(),
        SourceCreditStateV16::EMPTY
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_short
            .try_to_runtime()
            .unwrap(),
        SourceCreditStateV16::EMPTY
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_view_rejects_overwithdraw() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 6);
    let mut market_view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account_view = PortfolioV16ViewMut::new(&mut account_header);
    market_view
        .deposit_not_atomic(&mut account_view, 3)
        .unwrap();

    let err = market_view.withdraw_not_atomic(&mut account_view, 4);

    assert_eq!(err, Err(V16Error::LockActive));
}

// E6 (port of upstream engine c8aab338): a finalized zero-residual close
// ledger represents no outstanding obligation -- it must not permanently
// freeze a flat, solvent user's withdrawal just because the ledger is still
// `active` for history/identity. Companion to the already-carried Finding E
// (canceled-ledger) exemption proven by `v16_view_rejects_overwithdraw`'s
// sibling tests above.
#[test]
fn v16_finalized_zero_residual_close_does_not_block_withdraw() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 7);
    let market_id = markets[0].engine.asset.market_id.get();

    {
        let mut market_view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account_view = PortfolioV16ViewMut::new(&mut account_header);
        market_view
            .deposit_not_atomic(&mut account_view, 10)
            .unwrap();
    }

    account_header.close_progress = CloseProgressLedgerV16Account::from_runtime(
        &finalized_inert_close_progress(market_id, 3, 5),
    );

    let mut market_view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account_view = PortfolioV16ViewMut::new(&mut account_header);

    market_view
        .withdraw_not_atomic(&mut account_view, 4)
        .unwrap();

    assert_eq!(account_view.header.capital.get(), 6);
    assert_eq!(market_view.header.c_tot.get(), 6);
    assert_eq!(market_view.header.vault.get(), 6);
    // Withdraw does not itself mutate the finalized ledger -- it only stops
    // treating it as a blocker.
    let after_close = account_view.header.close_progress.try_to_runtime().unwrap();
    assert!(after_close.active && after_close.finalized && after_close.residual_remaining == 0);
}

// E6, second call site: a finalized zero-residual close ledger must also be
// treated as inert by the empty-account dematerialization gate
// (`is_empty_for_dematerialization`, reached via
// register/deregister_empty_materialized_portfolio_not_atomic), so an
// otherwise-empty account is not stranded from ordinary lifecycle bookkeeping
// (materialized-portfolio rent accounting) after an insurance-covered
// liquidation finishes paying out.
#[test]
fn v16_finalized_zero_residual_close_does_not_block_dematerialization() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 8);
    let market_id = markets[0].engine.asset.market_id.get();
    account_header.close_progress = CloseProgressLedgerV16Account::from_runtime(
        &finalized_inert_close_progress(market_id, 2, 5),
    );

    let mut market_view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let account_view = PortfolioV16ViewMut::new(&mut account_header);

    market_view
        .register_empty_materialized_portfolio_not_atomic(&account_view.as_view())
        .unwrap();
    assert_eq!(market_view.header.materialized_portfolio_count.get(), 1);

    market_view
        .deregister_empty_materialized_portfolio_not_atomic(&account_view.as_view())
        .unwrap();
    assert_eq!(market_view.header.materialized_portfolio_count.get(), 0);
}

#[cfg(feature = "fuzz")]
#[test]
fn v16_insurance_lien_consume_rejects_fractional_bound_amount() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    header.insurance = V16PodU128::new(10);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.deposit_domain_insurance_not_atomic(0, 10).unwrap();
    market
        .reserve_insurance_credit_not_atomic(0, BOUND_SCALE)
        .unwrap();
    market
        .create_source_credit_lien_from_insurance_not_atomic(0, BOUND_SCALE)
        .unwrap();

    let before_insurance = market.header.insurance;
    let before_spent = market.markets[0].engine.insurance_domain_spent_long;
    let before_reservation = market.markets[0].engine.insurance_reservation_long;
    let before_source = market.markets[0].engine.source_credit_long;

    let err = market.consume_source_credit_lien_from_insurance_not_atomic(0, 1);

    assert_eq!(err, Err(V16Error::InvalidConfig));
    assert_eq!(market.header.insurance, before_insurance);
    assert_eq!(
        market.markets[0].engine.insurance_domain_spent_long,
        before_spent
    );
    assert_eq!(
        market.markets[0].engine.insurance_reservation_long,
        before_reservation
    );
    assert_eq!(market.markets[0].engine.source_credit_long, before_source);
}

#[test]
fn v16_domain_insurance_deposit_and_withdraw_use_engine_budget_accounting() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market.deposit_domain_insurance_not_atomic(0, 10).unwrap();
    assert_eq!(market.header.vault.get(), 10);
    assert_eq!(market.header.insurance.get(), 10);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        10
    );
    assert_eq!(
        market.markets[0].engine.insurance_domain_budget_long.get(),
        10
    );

    market.withdraw_domain_insurance_not_atomic(0, 4).unwrap();
    assert_eq!(market.header.vault.get(), 6);
    assert_eq!(market.header.insurance.get(), 6);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        6
    );
    assert_eq!(
        market.markets[0].engine.insurance_domain_budget_long.get(),
        6
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_domain_insurance_bulk_credit_accumulates_duplicates_with_one_exact_delta() {
    let (mut header, mut markets) = market_fixture(2, 100);
    header.vault = V16PodU128::new(21);
    header.insurance = V16PodU128::new(21);
    let vault_before = header.vault.get();
    let insurance_before = header.insurance.get();
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market
        .credit_domain_insurance_budgets_not_atomic(&[(0, 3), (2, 5), (0, 7), (3, 6)])
        .unwrap();

    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        21
    );
    assert_eq!(
        market.markets[0].engine.insurance_domain_budget_long.get(),
        10
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_budget_long.get(),
        5
    );
    assert_eq!(
        market.markets[1].engine.insurance_domain_budget_short.get(),
        6
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_credit_account_from_insurance_uses_unbudgeted_surplus_only() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    header.insurance = V16PodU128::new(10);
    let mut account_header = account_fixture(1, 9);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    market
        .credit_account_from_insurance_not_atomic(&mut account, 3, 0)
        .unwrap();
    assert_eq!(market.header.vault.get(), 10);
    assert_eq!(market.header.insurance.get(), 7);
    assert_eq!(market.header.c_tot.get(), 3);
    assert_eq!(account.header.capital.get(), 3);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(account.validate_with_market(&market.as_view()), Ok(()));

    market
        .credit_domain_insurance_budget_not_atomic(0, 7)
        .unwrap();
    let err = market.credit_account_from_insurance_not_atomic(&mut account, 1, 0);
    assert_eq!(
        err,
        Err(V16Error::LockActive),
        "budgeted domain insurance must not be paid as a cranker reward"
    );
}

#[test]
fn v16_credit_account_from_insurance_respects_additional_reserved() {
    // Starvation-attack regression (protocol-fee RESERVE amendment,
    // ~/v17/DECISIONS-LEDGER.md): a crank-reward-style credit must never dip
    // `header.insurance` below the caller-declared `additional_reserved`
    // floor (e.g. the protocol's accrued-but-unwithdrawn fee claim), even
    // when the naive unbudgeted-surplus check (pre-amendment: `budget_remaining
    // > next_insurance`) would have allowed it.
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    header.insurance = V16PodU128::new(10);
    let mut account_header = account_fixture(1, 9);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    // No domain budget allocated (budget_remaining == 0), so the pre-amendment
    // check would allow draining the full 10 atoms of unbudgeted surplus as a
    // "cranker reward". With a 6-atom protocol reservation in place, only 4
    // atoms are actually free.
    let protocol_owed: u128 = 6;

    let err = market.credit_account_from_insurance_not_atomic(&mut account, 5, protocol_owed);
    assert_eq!(
        err,
        Err(V16Error::LockActive),
        "cranker reward must not be able to dip insurance below the protocol's reserved claim"
    );
    // Insurance/vault/capital must be untouched by the rejected attempt.
    assert_eq!(market.header.insurance.get(), 10);
    assert_eq!(account.header.capital.get(), 0);

    // Exactly the free amount (10 - 6 = 4) still succeeds.
    market
        .credit_account_from_insurance_not_atomic(&mut account, 4, protocol_owed)
        .unwrap();
    assert_eq!(market.header.insurance.get(), 6);
    assert_eq!(account.header.capital.get(), 4);
    assert_eq!(market.validate_shape(), Ok(()));

    // The reserved floor (6) is now exactly `header.insurance` -- any further
    // draw, however small, must fail.
    let err = market.credit_account_from_insurance_not_atomic(&mut account, 1, protocol_owed);
    assert_eq!(err, Err(V16Error::LockActive));
    assert_eq!(market.header.insurance.get(), 6, "reserve floor is exact");
}

#[test]
fn v16_public_domain_insurance_spent_setter_preserves_budget_total() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market.deposit_domain_insurance_not_atomic(0, 10).unwrap();
    market.set_domain_insurance_spent(0, 4).unwrap();
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        6
    );
    assert_eq!(
        market.markets[0].engine.insurance_domain_spent_long.get(),
        4
    );
    market.set_domain_insurance_spent(0, 0).unwrap();
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        10
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_public_domain_insurance_spent_setter_rejects_unbacked_clear() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(5);
    header.insurance = V16PodU128::new(5);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(5);
    markets[0].engine.insurance_domain_budget_long = V16PodU128::new(10);
    markets[0].engine.insurance_domain_spent_long = V16PodU128::new(5);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(market.validate_shape(), Ok(()));

    let err = market.set_domain_insurance_spent(0, 0);

    assert_eq!(err, Err(V16Error::LockActive));
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        5
    );
    assert_eq!(
        market.markets[0].engine.insurance_domain_spent_long.get(),
        5
    );
}

#[test]
fn v16_backing_provider_earnings_credit_and_withdraw_are_engine_accounted() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    let market_id = markets[0].engine.asset.market_id.get();
    markets[0].engine.backing_long = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id,
        fresh_unliened_backing_num: 1,
        expiry_slot: 10,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            fresh_reserved_backing_num: 1,
            credit_rate_num: CREDIT_RATE_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market
        .credit_backing_provider_earnings_not_atomic(0, 4)
        .unwrap();
    assert_eq!(market.header.vault.get(), 10);
    assert_eq!(market.header.backing_provider_earnings_total.get(), 4);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .utilization_fee_earnings
            .get(),
        4
    );
    market
        .withdraw_backing_provider_earnings_not_atomic(0, 3)
        .unwrap();
    assert_eq!(market.header.vault.get(), 7);
    assert_eq!(market.header.backing_provider_earnings_total.get(), 1);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .utilization_fee_earnings
            .get(),
        1
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_backing_provider_earnings_credit_rejects_without_vault_slack() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    header.c_tot = V16PodU128::new(10);
    let market_id = markets[0].engine.asset.market_id.get();
    markets[0].engine.backing_long = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id,
        fresh_unliened_backing_num: 1,
        expiry_slot: 10,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            fresh_reserved_backing_num: 1,
            credit_rate_num: CREDIT_RATE_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    assert_eq!(market.validate_shape(), Ok(()));

    let err = market.credit_backing_provider_earnings_not_atomic(0, 1);

    assert_eq!(err, Err(V16Error::LockActive));
    assert_eq!(market.header.backing_provider_earnings_total.get(), 0);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .utilization_fee_earnings
            .get(),
        0
    );
}

#[test]
fn v16_public_backing_principal_deposit_and_withdraw_move_vault_and_source_state() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market
        .deposit_fresh_counterparty_backing_not_atomic(0, 5, 10)
        .unwrap();
    assert_eq!(market.header.vault.get(), 5);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .fresh_unliened_backing_num
            .get(),
        5 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .fresh_reserved_backing_num
            .get(),
        5 * BOUND_SCALE
    );

    market
        .withdraw_fresh_counterparty_backing_not_atomic(0, 2)
        .unwrap();
    assert_eq!(market.header.vault.get(), 3);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .fresh_unliened_backing_num
            .get(),
        3 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .fresh_reserved_backing_num
            .get(),
        3 * BOUND_SCALE
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[cfg(feature = "fuzz")]
#[test]
fn v16_public_backing_principal_withdraw_rejects_if_claims_would_be_underbacked() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .deposit_fresh_counterparty_backing_not_atomic(0, 5, 10)
        .unwrap();
    market.header.pnl_pos_bound_tot_num = V16PodU128::new(5 * BOUND_SCALE);
    market.header.pnl_pos_bound_tot = V16PodU128::new(5);
    market
        .add_source_positive_claim_bound_not_atomic(0, 5 * BOUND_SCALE, 5 * BOUND_SCALE)
        .unwrap();

    let err = market.withdraw_fresh_counterparty_backing_not_atomic(0, 1);

    assert_eq!(err, Err(V16Error::LockActive));
    assert_eq!(market.header.vault.get(), 5);
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .credit_rate_num
            .get(),
        CREDIT_RATE_SCALE
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_public_account_backing_fee_routes_provider_and_insurance_splits_atomically() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 23);
    header.vault = V16PodU128::new(100);
    header.c_tot = V16PodU128::new(100);
    account_header.capital = V16PodU128::new(100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .deposit_fresh_counterparty_backing_not_atomic(0, 1, 10)
        .unwrap();
    account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        certified_equity: 100,
        certified_initial_req: 50,
        certified_maintenance_req: 40,
        cert_oracle_epoch: market.header.oracle_epoch.get(),
        cert_funding_epoch: market.header.funding_epoch.get(),
        cert_risk_epoch: market.header.risk_epoch.get(),
        cert_asset_set_epoch: market.header.asset_set_epoch.get(),
        active_bitmap_at_cert: V16_EMPTY_ACTIVE_BITMAP,
        valid: true,
        ..HealthCertV16::default()
    });
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    let charged = market
        .charge_account_backing_fee_not_atomic(&mut account, 0, 6, 1, 4)
        .unwrap();

    assert_eq!(charged, 10);
    assert_eq!(market.header.vault.get(), 101);
    assert_eq!(market.header.c_tot.get(), 90);
    assert_eq!(account.header.capital.get(), 90);
    assert_eq!(market.header.insurance.get(), 4);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        4
    );
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .utilization_fee_earnings
            .get(),
        6
    );
    assert_eq!(account.header.health_cert.certified_equity.get(), 90);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(account.validate_with_market(&market.as_view()), Ok(()));
}

#[test]
fn v16_public_account_backing_fee_rejects_if_post_fee_im_would_fail() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 24);
    header.vault = V16PodU128::new(100);
    header.c_tot = V16PodU128::new(100);
    account_header.capital = V16PodU128::new(100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .deposit_fresh_counterparty_backing_not_atomic(0, 1, 10)
        .unwrap();
    account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        certified_equity: 100,
        certified_initial_req: 95,
        certified_maintenance_req: 80,
        cert_oracle_epoch: market.header.oracle_epoch.get(),
        cert_funding_epoch: market.header.funding_epoch.get(),
        cert_risk_epoch: market.header.risk_epoch.get(),
        cert_asset_set_epoch: market.header.asset_set_epoch.get(),
        active_bitmap_at_cert: V16_EMPTY_ACTIVE_BITMAP,
        valid: true,
        ..HealthCertV16::default()
    });
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    let err = market.charge_account_backing_fee_not_atomic(&mut account, 0, 6, 1, 4);

    assert_eq!(err, Err(V16Error::LockActive));
    assert_eq!(market.header.c_tot.get(), 100);
    assert_eq!(account.header.capital.get(), 100);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_public_liquidation_on_unfunded_domain_cannot_drain_shared_insurance() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 10);
    header.vault = V16PodU128::new(50);
    header.insurance = V16PodU128::new(50);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = 2 * POS_SCALE;
    asset.oi_eff_short_q = 2 * POS_SCALE;
    asset.loss_weight_sum_long = 2 * POS_SCALE;
    asset.loss_weight_sum_short = 2 * POS_SCALE;
    asset.stored_pos_count_long = 2;
    asset.stored_pos_count_short = 2;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(4);

    account_header.pnl = V16PodI128::new(-5);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let insurance_before = market.header.insurance.get();
    let vault_before = market.header.vault.get();

    let out = market
        .liquidate_account_not_atomic(&mut account, LiquidationRequestV16 { asset_index: 0 })
        .expect("liquidation should progress by booking residual, not draining other domains");

    assert_eq!(out.insurance_used, 0);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(
        market.markets[0].engine.insurance_domain_spent_short.get(),
        0
    );
    assert!(out.residual_booked > 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// FIX E3 (upstream #92 / b97e1746): liquidation size + fee are now fully
// engine-selected. This test proves the engine picks the MINIMAL healthy
// partial close (981, not the full 10_000 position) and charges the
// correspondingly smaller fee (79, not 800) -- the exact opposite of the
// pre-fix "caller picks close_q" behavior this fix closes.
#[test]
fn v16_liquidation_engine_selects_healthy_partial_before_margin_floor() {
    const PRICE: u64 = POS_SCALE as u64;
    const POSITION_Q: u128 = 10_000;
    const ACCOUNT_CAPITAL: u128 = 980;
    const EXPECTED_CLOSE_Q: u128 = 1_000;
    const EXPECTED_FEE: u128 = 80;

    let (mut header, mut markets) = market_fixture(1, PRICE);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.min_nonzero_mm_req = V16PodU128::new(800);
    header.config.min_nonzero_im_req = V16PodU128::new(801);
    header.config.liquidation_fee_bps = V16PodU64::new(800);
    header.config.min_liquidation_abs = V16PodU128::new(0);
    header.config.liquidation_fee_cap = V16PodU128::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(1);
    header
        .config
        .try_to_runtime_shape()
        .unwrap()
        .validate_public_user_fund()
        .unwrap();
    header.vault = V16PodU128::new(ACCOUNT_CAPITAL * 2);
    header.c_tot = V16PodU128::new(ACCOUNT_CAPITAL * 2);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.effective_price = PRICE;
    asset.raw_oracle_target_price = PRICE;
    asset.oi_eff_long_q = POSITION_Q * 2;
    asset.oi_eff_short_q = POSITION_Q * 2;
    asset.loss_weight_sum_long = POSITION_Q * 2;
    asset.loss_weight_sum_short = POSITION_Q * 2;
    asset.stored_pos_count_long = 2;
    asset.stored_pos_count_short = 2;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(4);

    let mut account_header = account_fixture(1, 14);
    account_header.capital = V16PodU128::new(ACCOUNT_CAPITAL);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: i128::try_from(POSITION_Q).unwrap(),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POSITION_Q,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let out = market
        .liquidate_account_not_atomic(&mut account, LiquidationRequestV16 { asset_index: 0 })
        .unwrap();

    assert_eq!(out.closed_q, EXPECTED_CLOSE_Q); // 981, NOT 10_000 (full close)
    assert_eq!(out.fee_charged, EXPECTED_FEE); // 79, NOT 800 (8% of full notional)
    assert_eq!(account.header.capital.get(), ACCOUNT_CAPITAL - EXPECTED_FEE);
    assert_eq!(account.header.active_bitmap[0].get(), 1); // leg stays open (partial)
    let leg = account.header.legs[0].try_to_runtime().unwrap();
    assert_eq!(
        leg.basis_pos_q,
        i128::try_from(POSITION_Q - EXPECTED_CLOSE_Q).unwrap()
    );
    let cert = account.header.health_cert.try_to_runtime().unwrap();
    assert_eq!(cert.certified_liq_deficit, 0);
    assert_eq!(cert.certified_equity, 900);
    assert_eq!(cert.certified_maintenance_req, 900);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_permissionless_liquidation_progresses_when_unrelated_asset_is_loss_stale() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 11);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(9);
    header.loss_stale_active = 1;
    header.vault = V16PodU128::new(50);
    header.insurance = V16PodU128::new(50);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
    asset0.slot_last = 10;
    asset0.oi_eff_long_q = 2 * POS_SCALE;
    asset0.oi_eff_short_q = 2 * POS_SCALE;
    asset0.loss_weight_sum_long = 2 * POS_SCALE;
    asset0.loss_weight_sum_short = 2 * POS_SCALE;
    asset0.stored_pos_count_long = 2;
    asset0.stored_pos_count_short = 2;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);
    let mut asset1 = markets[1].engine.asset.try_to_runtime().unwrap();
    asset1.slot_last = 9;
    asset1.oi_eff_long_q = POS_SCALE;
    asset1.oi_eff_short_q = POS_SCALE;
    asset1.loss_weight_sum_long = POS_SCALE;
    asset1.loss_weight_sum_short = POS_SCALE;
    asset1.stored_pos_count_long = 1;
    asset1.stored_pos_count_short = 1;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&asset1);
    header.resolved_payout_blocker_count = V16PodU64::new(6);

    account_header.pnl = V16PodI128::new(-5);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset0.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset0.k_long,
        f_snap: asset0.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset0.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset0.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset0.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let outcome = market
        .permissionless_crank_not_atomic(
            &mut account,
            percolator::PermissionlessCrankRequestV16 {
                now_slot: 10,
                asset_index: 0,
                effective_price: 100,
                funding_rate_e9: 0,
                action: percolator::PermissionlessCrankActionV16::Liquidate(
                    LiquidationRequestV16 { asset_index: 0 },
                ),
            },
        )
        .expect(
            "locally current liquidation must progress despite unrelated global loss-staleness",
        );

    assert_eq!(
        outcome,
        percolator::PermissionlessProgressOutcomeV16::AccountCurrent
    );
    assert_eq!(market.header.loss_stale_active, 0);
    assert_eq!(market.header.slot_last.get(), 10);
    let unrelated_asset = market.markets[1].engine.asset.try_to_runtime().unwrap();
    assert_eq!(unrelated_asset.slot_last, 9);
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_permissionless_recovery_crank_is_value_neutral_and_idempotent() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 12);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 7).unwrap();
    }
    header.insurance = V16PodU128::new(3);
    header.vault = V16PodU128::new(10);
    let vault_before = header.vault;
    let c_tot_before = header.c_tot;
    let insurance_before = header.insurance;
    let capital_before = account_header.capital;
    let pnl_before = account_header.pnl;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let first = market
        .permissionless_crank_not_atomic(
            &mut account,
            PermissionlessCrankRequestV16 {
                now_slot: 1,
                asset_index: 0,
                effective_price: 100,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::Recover(
                    PermissionlessRecoveryReasonV16::ExplicitLossOrDustAuditOverflow,
                ),
            },
        )
        .unwrap();
    let second = market
        .permissionless_crank_not_atomic(
            &mut account,
            PermissionlessCrankRequestV16 {
                now_slot: 1,
                asset_index: 0,
                effective_price: 100,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::Recover(
                    PermissionlessRecoveryReasonV16::BIndexHeadroomExhausted,
                ),
            },
        )
        .unwrap();
    let refresh_after_recovery = market.permissionless_crank_not_atomic(
        &mut account,
        PermissionlessCrankRequestV16 {
            now_slot: 1,
            asset_index: 0,
            effective_price: 100,
            funding_rate_e9: 0,
            action: PermissionlessCrankActionV16::Refresh,
        },
    );

    assert_eq!(
        first,
        PermissionlessProgressOutcomeV16::RecoveryDeclared(
            PermissionlessRecoveryReasonV16::ExplicitLossOrDustAuditOverflow
        )
    );
    assert_eq!(second, first);
    assert_eq!(refresh_after_recovery, Err(V16Error::LockActive));
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.c_tot, c_tot_before);
    assert_eq!(market.header.insurance, insurance_before);
    assert_eq!(account.header.capital, capital_before);
    assert_eq!(account.header.pnl, pnl_before);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_resolved_payout_topup_finishes_receipt_without_overpaying() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 13);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.resolve_market_not_atomic(1).unwrap();
    }
    let terminal_claim = 10u128;
    header.vault = V16PodU128::new(4);
    header.payout_snapshot_captured = 1;
    header.resolved_payout_ledger =
        ResolvedPayoutLedgerV16Account::from_runtime(&ResolvedPayoutLedgerV16 {
            snapshot_residual: terminal_claim,
            terminal_claim_exact_receipts_num: terminal_claim * BOUND_SCALE,
            terminal_claim_bound_unreceipted_num: 0,
            current_payout_rate_num: 1,
            current_payout_rate_den: 1,
            snapshot_slot: 1,
            payout_halted: false,
            finalized: false,
        });
    account_header.resolved_payout_receipt =
        ResolvedPayoutReceiptV16Account::from_runtime(&ResolvedPayoutReceiptV16 {
            present: true,
            prior_bound_contribution_num: terminal_claim * BOUND_SCALE,
            live_released_face_at_receipt: 0,
            terminal_positive_claim_face: terminal_claim,
            paid_effective: 2,
            finalized: false,
        });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let first = market
        .claim_resolved_payout_topup_not_atomic(&mut account)
        .unwrap();
    let after_first = account
        .header
        .resolved_payout_receipt
        .try_to_runtime()
        .unwrap();
    market.header.vault = V16PodU128::new(4);
    let second = market
        .claim_resolved_payout_topup_not_atomic(&mut account)
        .unwrap();
    let after_second = account
        .header
        .resolved_payout_receipt
        .try_to_runtime()
        .unwrap();
    let third = market
        .claim_resolved_payout_topup_not_atomic(&mut account)
        .unwrap();

    assert_eq!(first, 4);
    assert_eq!(after_first.paid_effective, 6);
    assert!(!after_first.finalized);
    assert_eq!(second, 4);
    assert_eq!(after_second.paid_effective, terminal_claim);
    assert!(after_second.finalized);
    assert_eq!(third, 0);
    assert_eq!(market.header.vault.get(), 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_risk_increasing_trade_creates_source_credit_lien_for_im() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut long_header = account_fixture(1, 8);
    let mut short_header = account_fixture(1, 9);
    let claim = 100u128;
    let claim_num = claim * BOUND_SCALE;
    long_header.pnl = V16PodI128::new(claim as i128);
    long_header.source_domains[0].domain = V16PodU32::new(0);
    long_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    long_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
    // Backing principal is vault-funded and senior-side: vault must cover it.
    header.vault = V16PodU128::new(claim + header.vault.get());
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
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(10 * POS_SCALE),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .expect("risk-increasing trade should atomically lien backed source credit for IM");

    assert_eq!(long.header.capital.get(), 0);
    assert_eq!(
        long.header.source_domains[0].source_claim_liened_num.get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        10
    );
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_counterparty_backing_num
            .get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .valid_liened_backing_num
            .get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .valid_liened_backing_num
            .get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .fresh_unliened_backing_num
            .get(),
        90 * BOUND_SCALE
    );
    assert_eq!(
        market.convert_released_pnl_to_capital_not_atomic(&mut long),
        Err(V16Error::LockActive),
        "source-backed positive PnL must not be realized while the source-claim exposure remains open"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

// upstream 6e0dc19c "test: reproduce impaired source terminal lock", tip form
// (92ed4a1a later moved the second price step and the resolve slot). Once a
// Resolved source bucket is Impaired, a prospective terminal loss must still
// close instead of failing LockActive. Fork adaptation: the taker-only fee's
// fourth trade argument (both trades are zero-fee).
#[test]
fn v16_resolved_impaired_source_accepts_prospective_terminal_loss() {
    const Q: u128 = 1_000 * POS_SCALE;
    const INCREASE_Q: u128 = POS_SCALE;
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.maintenance_margin_bps = 1_000;
    cfg.initial_margin_bps = 5_000;
    cfg.max_price_move_bps_per_slot = 500;
    cfg.max_accrual_dt_slots = 1;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
        .unwrap();

    let mut liened_winner_header = account_fixture(1, 40);
    let mut liened_peer_header = account_fixture(1, 41);
    let mut expiry_trigger_header = account_fixture(1, 42);
    let mut prospective_loser_header = account_fixture(1, 43);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut liened_winner = PortfolioV16ViewMut::new(&mut liened_winner_header);
    let mut liened_peer = PortfolioV16ViewMut::new(&mut liened_peer_header);
    let mut expiry_trigger = PortfolioV16ViewMut::new(&mut expiry_trigger_header);
    let mut prospective_loser = PortfolioV16ViewMut::new(&mut prospective_loser_header);

    market
        .deposit_fresh_counterparty_backing_not_atomic(1, 100_000, 3)
        .unwrap();
    market
        .deposit_not_atomic(&mut liened_winner, 52_501)
        .unwrap();
    market
        .deposit_not_atomic(&mut liened_peer, 1_000_000)
        .unwrap();
    market
        .deposit_not_atomic(&mut expiry_trigger, 1_000_000)
        .unwrap();
    market
        .deposit_not_atomic(&mut prospective_loser, 1_000_000)
        .unwrap();
    for (long, short) in [
        (&mut liened_winner, &mut liened_peer),
        (&mut expiry_trigger, &mut prospective_loser),
    ] {
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                long,
                short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(Q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }

    market
        .set_asset_raw_oracle_target_not_atomic(0, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 105, 0, true)
        .unwrap();
    for account in [
        &mut liened_peer,
        &mut liened_winner,
        &mut expiry_trigger,
        &mut prospective_loser,
    ] {
        market.full_account_refresh_not_atomic(account).unwrap();
    }
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut liened_winner,
            &mut liened_peer,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(INCREASE_Q),
                exec_price: 105,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    market
        .set_asset_raw_oracle_target_not_atomic(0, 110)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 3, 110, 0, true)
        .unwrap();

    market.resolve_market_not_atomic(4).unwrap();
    assert_eq!(
        market
            .close_resolved_account_not_atomic(&mut expiry_trigger, 0)
            .unwrap(),
        percolator::ResolvedCloseOutcomeV16::ProgressOnly,
    );
    assert_eq!(
        market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Impaired,
    );

    market
        .close_resolved_account_not_atomic(&mut prospective_loser, 0)
        .expect("an impaired source bucket must accept a prospective terminal loss");
    assert_eq!(prospective_loser.header.pnl.get(), 0);
    market.validate_shape().unwrap();
    prospective_loser
        .validate_with_market(&market.as_view())
        .unwrap();
}

fn run_live_mark_reversal_unwinds_source_lien_before_claim_burn(insurance_backed: bool) {
    const OPEN_Q: u128 = 1_000 * POS_SCALE;
    const INCREASE_Q: u128 = 50 * POS_SCALE;
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(5_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 10);
    let mut short_header = account_fixture(1, 11);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    if insurance_backed {
        #[cfg(feature = "fuzz")]
        {
            market
                .deposit_domain_insurance_not_atomic(1, 100_000)
                .unwrap();
            market
                .reserve_insurance_credit_not_atomic(1, 100_000 * BOUND_SCALE)
                .unwrap();
        }
        #[cfg(not(feature = "fuzz"))]
        unreachable!("the insurance-backed variant requires the fuzz test API");
    } else {
        market
            .deposit_fresh_counterparty_backing_not_atomic(1, 100_000, 100)
            .unwrap();
    }
    market.deposit_not_atomic(&mut long, 52_501).unwrap();
    market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(OPEN_Q),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    market
        .set_asset_raw_oracle_target_not_atomic(0, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 105, 0, true)
        .unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    if insurance_backed {
        let fresh_backing_atoms = market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .fresh_unliened_backing_num
            / BOUND_SCALE;
        assert!(fresh_backing_atoms > 0);
        market
            .withdraw_fresh_counterparty_backing_not_atomic(1, fresh_backing_atoms)
            .expect("reserved insurance must fully replace withdrawn counterparty backing");
    }
    assert_eq!(long.header.pnl.get(), 5_000);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(INCREASE_Q),
                exec_price: 105,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    let lien_before = long.header.source_domains[0];
    assert_eq!(long.header.pnl.get(), 5_000);
    assert!(lien_before.source_claim_liened_num.get() > 0);
    if insurance_backed {
        assert!(
            lien_before.source_lien_insurance_backing_num.get() > 0,
            "expected insurance-backed lien: {lien_before:?}"
        );
        assert_eq!(lien_before.source_lien_counterparty_backing_num.get(), 0);
    } else {
        assert!(lien_before.source_lien_counterparty_backing_num.get() > 0);
        assert_eq!(lien_before.source_lien_insurance_backing_num.get(), 0);
    }
    let capital_before_reversal = long.header.capital.get();
    let lien_effective = lien_before.source_lien_effective_reserved.get();
    let backing_before_reversal = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    let reservation_before_reversal = market.markets[0]
        .engine
        .insurance_reservation_short
        .try_to_runtime()
        .unwrap();
    let insurance_before_reversal = market.header.insurance.get();
    let risk_epoch_before_reversal = market.header.risk_epoch.get();
    let source_credit_epoch_before_reversal = market.markets[0]
        .engine
        .source_credit_short
        .try_to_runtime()
        .unwrap()
        .credit_epoch;

    market
        .set_asset_raw_oracle_target_not_atomic(0, 100)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 3, 100, 0, true)
        .unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    let cert = market
        .full_account_refresh_not_atomic(&mut long)
        .expect("a mark reversal must settle even when the prior positive claim backed IM");

    let backing_after_reversal = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    let unliened_support_consumed = 5_000 - lien_effective;
    // Upstream's a0335e57 form wrote `5_250 - unliened_support_consumed` here and
    // corrected it to `5_250 - 5_000` in 07208fb1 ("Fix source loss face
    // overburn"): the prior positive face absorbs the reversal one-for-one
    // before principal is touched. This fork already produces the corrected
    // number, because its #172 site-1 proportional burn (row 120) reaches the
    // same split, so the assertion is taken in its 07208fb1 form.
    let principal_loss = 5_250 - 5_000;
    assert_eq!(long.header.pnl.get(), 0);
    assert_eq!(
        long.header.capital.get(),
        capital_before_reversal - principal_loss,
        "the prior positive face absorbs the reversal one-for-one before principal"
    );
    assert_eq!(long.header.source_domains[0], Default::default());
    if insurance_backed {
        let reservation_after_reversal = market.markets[0]
            .engine
            .insurance_reservation_short
            .try_to_runtime()
            .unwrap();
        let source_after_reversal = market.markets[0]
            .engine
            .source_credit_short
            .try_to_runtime()
            .unwrap();
        assert_eq!(reservation_after_reversal.valid_liened_insurance_num, 0);
        assert_eq!(source_after_reversal.valid_liened_insurance_num, 0);
        assert_eq!(
            reservation_after_reversal.consumed_insurance_num,
            reservation_before_reversal.consumed_insurance_num
                + unliened_support_consumed * BOUND_SCALE,
            "only realizable unliened support consumes insurance"
        );
        assert_eq!(
            market.header.insurance.get() + unliened_support_consumed,
            insurance_before_reversal,
            "the fused burn spends each insurance-backed support atom exactly once"
        );
        assert_eq!(backing_after_reversal, backing_before_reversal);
    } else {
        assert_eq!(
            backing_after_reversal.fresh_unliened_backing_num,
            backing_before_reversal
                .fresh_unliened_backing_num
                .checked_sub(unliened_support_consumed * BOUND_SCALE)
                .unwrap()
                .checked_add(lien_before.source_lien_counterparty_backing_num.get())
                .unwrap(),
            "the still-liened backing is unpledged rather than consumed"
        );
        assert_eq!(backing_after_reversal.valid_liened_backing_num, 0);
        assert_eq!(
            backing_after_reversal.consumed_liened_backing_num,
            backing_before_reversal.consumed_liened_backing_num
                + unliened_support_consumed * BOUND_SCALE,
            "only realizable unliened support offsets the reversal loss"
        );
        assert_eq!(market.header.insurance.get(), insurance_before_reversal);
    }
    // 4c4dfb20's fused burn advances the credit epoch by
    // `1 + (source_claim_burn_num != 0)` so the two-in-one delta lands on the
    // same epoch the legacy two-pass form reached. Nothing else in the engine
    // binds the epoch's absolute value -- ReservationEncumbranceProofV16 carries
    // source_credit_rate_num but no epoch field, and the only production
    // inequality (the A-6 stress envelope) uses a strict `>` that +1 and +2
    // satisfy identically -- so without these assertions the fused step is
    // unobservable: de-fusing both call sites to a hardcoded `epoch_steps = 1`
    // left the entire suite green (301/0 plain, 353/0 fuzz) while silently
    // landing the reversal an epoch short (5/3 instead of 6/4).
    assert_eq!(
        market.header.risk_epoch.get() - risk_epoch_before_reversal,
        6,
        "the fused source-claim burn must contribute its own risk-epoch step"
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_short
            .try_to_runtime()
            .unwrap()
            .credit_epoch
            - source_credit_epoch_before_reversal,
        4,
        "the fused source-claim burn must contribute its own credit-epoch step"
    );
    assert!(cert.valid);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

/// A PARTIAL mark reversal: the loss is smaller than the accumulated positive
/// face, so 4c4dfb20's close-loss path burns only part of the account's source
/// claim and the position is NOT fully unwound. The full-reversal fixtures above
/// drive the same call with the whole face, so they cannot distinguish a
/// proportional burn from a total one; this shape pins the arithmetic, and it
/// reaches the fused burn inside
/// `apply_haircut_bounded_close_loss_to_pnl` ->
/// `consume_validated_account_source_credit_not_atomic` with a measured
/// `preburned_source_claim_num` of exactly 2_100 * BOUND_SCALE.
///
/// It does NOT discriminate that call's `burn_account_claims = true` argument:
/// flipping it to false leaves this test (and the whole suite) green, because
/// `set_account_pnl_inner` (src/v16.rs:12813, writing at :12856 and :12864)
/// independently reconciles BOTH the account's `source_claim_bound_num` and the
/// domain's `positive_claim_bound_num` down to the new pnl. With a preburned
/// count of 0 it simply performs the whole burn itself and lands on the same
/// final state. The fused burn's only externally visible trace is therefore the
/// credit/risk epoch it advances -- which is what the two epoch assertions in
/// `run_live_mark_reversal_unwinds_source_lien_before_claim_burn` pin down.
fn run_partial_mark_reversal_burns_only_matched_source_claim(insurance_backed: bool) {
    const OPEN_Q: u128 = 1_000 * POS_SCALE;
    const INCREASE_Q: u128 = 50 * POS_SCALE;
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(5_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 10);
    let mut short_header = account_fixture(1, 11);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    if insurance_backed {
        #[cfg(feature = "fuzz")]
        {
            market
                .deposit_domain_insurance_not_atomic(1, 100_000)
                .unwrap();
            market
                .reserve_insurance_credit_not_atomic(1, 100_000 * BOUND_SCALE)
                .unwrap();
        }
        #[cfg(not(feature = "fuzz"))]
        unreachable!("the insurance-backed variant requires the fuzz test API");
    } else {
        market
            .deposit_fresh_counterparty_backing_not_atomic(1, 100_000, 100)
            .unwrap();
    }
    market.deposit_not_atomic(&mut long, 52_501).unwrap();
    market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(OPEN_Q),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    market
        .set_asset_raw_oracle_target_not_atomic(0, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 105, 0, true)
        .unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    market.full_account_refresh_not_atomic(&mut long).unwrap();
    if insurance_backed {
        let fresh_backing_atoms = market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .fresh_unliened_backing_num
            / BOUND_SCALE;
        assert!(fresh_backing_atoms > 0);
        market
            .withdraw_fresh_counterparty_backing_not_atomic(1, fresh_backing_atoms)
            .expect("reserved insurance must fully replace withdrawn counterparty backing");
    }
    assert_eq!(long.header.pnl.get(), 5_000);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(INCREASE_Q),
                exec_price: 105,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    let lien_before = long.header.source_domains[0];
    assert_eq!(long.header.pnl.get(), 5_000);
    assert!(lien_before.source_claim_liened_num.get() > 0);
    let claim_bound_before = lien_before.source_claim_bound_num.get();
    assert!(claim_bound_before > 0);
    let domain_claim_before = market.markets[0]
        .engine
        .source_credit_short
        .try_to_runtime()
        .unwrap()
        .positive_claim_bound_num;

    // PARTIAL reversal: 105 -> 103 leaves part of the +5_000 face standing.
    market
        .set_asset_raw_oracle_target_not_atomic(0, 103)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 3, 103, 0, true)
        .unwrap();
    market.full_account_refresh_not_atomic(&mut short).unwrap();
    market
        .full_account_refresh_not_atomic(&mut long)
        .expect("a partial mark reversal must settle");

    let claim_bound_after = long.header.source_domains[0].source_claim_bound_num.get();
    let domain_claim_after = market.markets[0]
        .engine
        .source_credit_short
        .try_to_runtime()
        .unwrap()
        .positive_claim_bound_num;
    // The reversal costs 2_100 of the standing 5_000 face, so 2_900 survives.
    assert_eq!(long.header.pnl.get(), 2_900);
    assert!(
        claim_bound_after > 0,
        "this fixture must leave a RESIDUAL source claim -- a full reversal zeroes \
         the claim and cannot tell a proportional burn from a total one"
    );
    assert_eq!(
        claim_bound_before - claim_bound_after,
        2_100 * BOUND_SCALE,
        "the account's source claim must retire exactly the face the loss consumed"
    );
    assert_eq!(
        domain_claim_before - domain_claim_after,
        2_100 * BOUND_SCALE,
        "the domain's positive claim must retire the same face as the account's, \
         not survive the loss it already paid for"
    );
    assert_eq!(
        claim_bound_after,
        long.header.pnl.get().unsigned_abs() * BOUND_SCALE,
        "the surviving claim must track the surviving positive face"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_partial_mark_reversal_burns_only_matched_source_claim() {
    run_partial_mark_reversal_burns_only_matched_source_claim(false);
}

#[cfg(feature = "fuzz")]
#[test]
fn v16_partial_mark_reversal_burns_only_matched_source_claim_insurance_backed() {
    run_partial_mark_reversal_burns_only_matched_source_claim(true);
}

#[test]
fn v16_live_mark_reversal_unwinds_counterparty_lien_before_claim_burn() {
    run_live_mark_reversal_unwinds_source_lien_before_claim_burn(false);
}

#[cfg(feature = "fuzz")]
#[test]
fn v16_live_mark_reversal_unwinds_insurance_lien_before_claim_burn() {
    run_live_mark_reversal_unwinds_source_lien_before_claim_burn(true);
}

#[test]
fn v16_residual_reward_credit_uses_real_principal_not_notional() {
    let (mut header, mut markets) = market_fixture(1, 1_000);
    header.config.initial_margin_bps = V16PodU64::new(500);
    header.config.maintenance_margin_bps = V16PodU64::new(500);
    header.config.min_nonzero_im_req = V16PodU128::new(2);
    header.config.min_nonzero_mm_req = V16PodU128::new(1);
    let mut taker_header = account_fixture(1, 23);
    let mut lp_header = account_fixture(1, 24);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
        let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
        market.deposit_not_atomic(&mut taker, 10_000).unwrap();
        market.deposit_not_atomic(&mut lp, 10_000).unwrap();
    }

    taker_header.residual_crystallized_loss_atoms_total = V16PodU128::new(10_000);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
    let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut taker,
            &mut lp,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 1_000,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    assert_eq!(
        taker.header.residual_spent_principal_atoms_total.get(),
        50,
        "1 lot at price 1000 with 500 bps IM spends only 50 atoms of residual budget"
    );
    assert_eq!(lp.header.residual_received_atoms_total.get(), 50);
    assert_ne!(
        lp.header.residual_received_atoms_total.get(),
        1_000,
        "counter must not credit leveraged notional"
    );
    taker.validate_with_market(&market.as_view()).unwrap();
    lp.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

fn flat_source_credit_lien_fixture() -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
) {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut winner_header = account_fixture(1, 10);
    let mut counterparty_header = account_fixture(1, 11);
    let claim = 100;
    let claim_num = claim * BOUND_SCALE;
    winner_header.pnl = V16PodI128::new(claim as i128);
    winner_header.source_domains[0].domain = V16PodU32::new(0);
    winner_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    winner_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.vault = V16PodU128::new(claim);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
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
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
        market.deposit_not_atomic(&mut counterparty, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
    let open = TradeRequestV16 {
        asset_index: 0,
        size_q: signed_q(10 * POS_SCALE),
        exec_price: 1,
        fee_bps: 0,
    };
    // This fork charges the fee to the taker only, so the trade entrypoint carries
    // `taker_is_long_account`. fee_bps is 0 here, so the flag is economically inert
    // and only satisfies the fork signature.
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut winner,
            &mut counterparty,
            open,
            true,
        )
        .unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut winner,
            &mut counterparty,
            TradeRequestV16 {
                size_q: -open.size_q,
                ..open
            },
            true,
        )
        .unwrap();
    drop(market);
    drop(winner);
    drop(counterparty);
    (header, markets, winner_header)
}

#[test]
fn v16_auto_crank_releases_flat_source_credit_lien_for_conversion() {
    const CLAIM: u128 = 100;
    let (mut header, mut markets, mut winner_header) = flat_source_credit_lien_fixture();
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);

    assert!(active_bitmap_is_empty(
        winner.header.active_bitmap.map(V16PodU64::get)
    ));
    assert_ne!(
        winner.header.source_domains[0]
            .source_claim_liened_num
            .get(),
        0,
        "the public trades must reach the flat retained-lien state"
    );
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut winner,
            AutoCrankWorkV16 {
                now_slot: market.header.current_slot.get(),
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("a flat funded source claim must have a bounded crank continuation");
    assert_eq!(result.selected, AutoCrankPlanV16::ReleaseSourceLiens);
    assert_eq!(
        winner.header.source_domains[0]
            .source_claim_liened_num
            .get(),
        0,
        "the crank must release the obsolete source-credit encumbrance"
    );
    assert_eq!(
        market
            .convert_released_pnl_to_capital_not_atomic(&mut winner)
            .expect("released source-backed PnL must become convertible"),
        CLAIM
    );
    winner.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

/// Two-asset analogue of `flat_source_credit_lien_fixture`: the same flat,
/// funded, retained-lien account, but holding a source lien on BOTH assets'
/// long domains, so the two Live source-lien continuations can be ordered
/// against each other. (Upstream carries this as `flat_source_credit_lien_fixture(2)`.)
#[allow(clippy::type_complexity)]
fn flat_source_credit_lien_fixture_two_domains() -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
    [usize; 2],
) {
    const ASSETS: usize = 2;
    let (mut header, mut markets) = market_fixture(ASSETS as u32, 1);
    let mut winner_header = account_fixture(ASSETS as u32, 10);
    let mut counterparty_header = account_fixture(ASSETS as u32, 11);
    let claim = 100u128;
    let claim_num = claim * BOUND_SCALE;
    winner_header.pnl = V16PodI128::new((claim * ASSETS as u128) as i128);
    for (a, market) in markets.iter_mut().enumerate().take(ASSETS) {
        winner_header.source_domains[a].domain = V16PodU32::new((a * 2) as u32);
        // market_fixture assigns asset i the market_id (i + 1); a source claim whose
        // market_id does not match its domain's asset is rejected as HiddenLeg.
        winner_header.source_domains[a].source_claim_market_id = V16PodU64::new((a + 1) as u64);
        winner_header.source_domains[a].source_claim_bound_num = V16PodU128::new(claim_num);
        market.engine.source_credit_long =
            SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
                positive_claim_bound_num: claim_num,
                exact_positive_claim_num: claim_num,
                fresh_reserved_backing_num: claim_num,
                credit_rate_num: CREDIT_RATE_SCALE,
                ..SourceCreditStateV16::EMPTY
            });
        market.engine.backing_long = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
            market_id: (a + 1) as u64,
            fresh_unliened_backing_num: claim_num,
            expiry_slot: 100,
            status: BackingBucketStatusV16::Fresh,
            ..BackingBucketV16::EMPTY
        });
    }
    header.pnl_pos_tot = V16PodU128::new(claim * ASSETS as u128);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num * ASSETS as u128);
    header.pnl_pos_bound_tot = V16PodU128::new(claim * ASSETS as u128);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num * ASSETS as u128);
    header.vault = V16PodU128::new(claim * ASSETS as u128);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num * ASSETS as u128);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
        market
            .deposit_not_atomic(&mut counterparty, 10_000)
            .unwrap();
    }
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
    // The winner is deliberately UNFUNDED: the IM lien only forms when a
    // risk-increasing trade must lean on source-backed PnL rather than the
    // account's own capital, so depositing to the winner would silently produce
    // a fixture with no lien at all. Only asset 0 is traded -- the second source
    // domain needs to be OCCUPIED, not liened, because
    // `first_lapsed_source_backing_for_account_at_slot` scans every occupied
    // source domain regardless of whether it carries a lien.
    // Taker-only fee (fork): fee_bps is 0, so `taker_is_long_account` is inert.
    let open = TradeRequestV16 {
        asset_index: 0,
        size_q: signed_q(10 * POS_SCALE),
        exec_price: 1,
        fee_bps: 0,
    };
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut winner,
            &mut counterparty,
            open,
            true,
        )
        .unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut winner,
            &mut counterparty,
            TradeRequestV16 {
                size_q: -open.size_q,
                ..open
            },
            true,
        )
        .unwrap();
    drop(market);
    drop(winner);
    drop(counterparty);
    (header, markets, winner_header, [0, 2])
}

/// 6c8d94bc adds `!lapsed_source_backing` to the flat-lien class, ORDERING two
/// continuations that were previously mutually blind. Clock-driven backing
/// expiry is market-wide state every co-tenant depends on, so it must be
/// canonicalized before this account's own lien normalization runs. Two liened
/// source domains: one already globally `Impaired` (normalizable now) and one
/// still `Fresh` but lapsed at the authenticated slot. The crank must reach the
/// lapsed bucket FIRST.
#[test]
fn v16_auto_crank_expires_lapsed_source_backing_before_normalizing_an_impaired_lien() {
    const NOW: u64 = 100;
    let (mut header, mut markets, mut winner_header, domains) =
        flat_source_credit_lien_fixture_two_domains();
    let (impaired_domain, lapsed_domain) = (domains[0], domains[1]);
    {
        // Only the FIRST domain's bucket goes through the canonical expiry
        // transition, as a co-tenant of that market-wide bucket would drive it.
        // The second stays `Fresh` with expiry_slot <= NOW: lapsed, not yet
        // canonicalized, and therefore visible ONLY to the lapsed-bucket class.
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .expire_source_backing_bucket_not_atomic(impaired_domain, NOW)
            .unwrap();
    }
    assert_eq!(
        markets[0]
            .engine
            .backing_long
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Impaired,
        "fixture must reach the globally impaired bucket"
    );
    let sibling = markets[1].engine.backing_long.try_to_runtime().unwrap();
    assert_eq!(sibling.status, BackingBucketStatusV16::Fresh);
    assert!(
        sibling.expiry_slot <= NOW,
        "the sibling bucket must be Fresh but lapsed, or the ordering is untested"
    );

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    let observations = [
        AutoCrankObservationV16 {
            asset_index: 0,
            effective_price: market.markets[0].engine.asset.effective_price.get(),
            funding_rate_e9: 0,
        },
        AutoCrankObservationV16 {
            asset_index: 1,
            effective_price: market.markets[1].engine.asset.effective_price.get(),
            funding_rate_e9: 0,
        },
    ];
    let work = AutoCrankWorkV16 {
        now_slot: NOW,
        observations: &observations,
        resolved_close_fee_rate_per_slot: 0,
    };

    let mut first_release_step: Option<usize> = None;
    let mut lapsed_expiry_step: Option<usize> = None;
    for step in 0..12usize {
        let summary = market
            .build_actionable_summary_at_slot(&winner.as_view(), NOW)
            .unwrap();
        if !summary.is_actionable() {
            break;
        }
        let result = market
            .permissionless_auto_crank_not_atomic(&mut winner, work)
            .expect("every selected continuation must succeed");
        if result.outcome
            == AutoCrankOutcomeV16::Progressed(
                PermissionlessProgressOutcomeV16::SourceBackingExpired {
                    domain: lapsed_domain,
                },
            )
        {
            lapsed_expiry_step.get_or_insert(step);
        }
        if result.selected == AutoCrankPlanV16::ReleaseSourceLiens {
            first_release_step.get_or_insert(step);
        }
    }
    let release =
        first_release_step.expect("the impaired lien must be normalized in finite cranks");
    let expiry = lapsed_expiry_step
        .expect("the lapsed sibling bucket must be canonicalized in finite cranks");
    assert!(
        expiry < release,
        "lapsed backing must PRE-EMPT flat-lien normalization: expiry at step {expiry}, first \
         release at step {release}"
    );

    winner.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

/// 6c8d94bc ("Restore live progress for impaired source liens"). A flat, funded,
/// margin-safe Live account whose counterparty backing bucket has already gone
/// through the canonical expiry transition -- typically because a CO-TENANT of
/// the same (asset, side) domain drove it, since the bucket is market-wide --
/// was invisible to every permissionless crank class at once:
///
///   * `first_lapsed_source_backing_for_account_at_slot` only selects `Fresh`
///     buckets, so an already-`Impaired` one never sets `lapsed_source_backing`;
///   * the pre-6c8d94bc `account_source_credit_liens_are_fresh_and_releasable`
///     returned `Ok(false)` for any lien whose bucket was not `Fresh`, so
///     `source_liens_releasable` was false too.
///
/// The account therefore reached an all-false `ActionableSummaryV16` with the
/// lien still held and its `source_lien_effective_reserved` still encumbered --
/// a permanent stall, with no keeper, user or admin route out in Live mode.
#[test]
fn v16_auto_crank_normalizes_impaired_flat_source_lien_into_the_impaired_claim_lane() {
    const EXPIRY_SLOT: u64 = 100;
    let (mut header, mut markets, mut winner_header) = flat_source_credit_lien_fixture();
    {
        // Drive the market-wide bucket through the canonical expiry transition,
        // exactly as a co-tenant's own crank continuation would.
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .expire_source_backing_bucket_not_atomic(0, EXPIRY_SLOT)
            .unwrap();
    }
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Impaired,
        "fixture must reach the globally impaired bucket, or this proves nothing"
    );
    let lien_num = winner.header.source_domains[0]
        .source_claim_liened_num
        .get();
    let bound_num = winner.header.source_domains[0].source_claim_bound_num.get();
    assert_ne!(
        lien_num, 0,
        "the co-tenant's expiry cannot mutate this account's lien"
    );
    assert_eq!(
        winner.header.source_domains[0]
            .source_claim_counterparty_liened_num
            .get(),
        lien_num
    );

    let observations = [AutoCrankObservationV16 {
        asset_index: 0,
        effective_price: market.markets[0].engine.asset.effective_price.get(),
        funding_rate_e9: 0,
    }];
    let work = AutoCrankWorkV16 {
        now_slot: EXPIRY_SLOT,
        observations: &observations,
        resolved_close_fee_rate_per_slot: 0,
    };

    let mut normalization_steps = 0usize;
    let mut steps = 0usize;
    for _ in 0..8 {
        let summary = market
            .build_actionable_summary_at_slot(&winner.as_view(), EXPIRY_SLOT)
            .unwrap();
        if !summary.is_actionable() {
            break;
        }
        let result = market
            .permissionless_auto_crank_not_atomic(&mut winner, work)
            .expect("every selected continuation must succeed");
        normalization_steps += usize::from(result.selected == AutoCrankPlanV16::ReleaseSourceLiens);
        steps += 1;
    }
    assert!(
        steps < 8,
        "the crank must reach a fixed point in finite steps"
    );
    assert_eq!(
        normalization_steps, 1,
        "the impaired lien must be selected for exactly one bounded normalization"
    );

    // The lien is gone from the live lane and LOCKED in the impaired lane --
    // not silently dropped, which would have grown the account's spendable
    // `source_claim_unliened_num` by the forfeited face.
    let source = winner.header.source_domains[0];
    assert_eq!(source.source_claim_liened_num.get(), 0);
    assert_eq!(source.source_claim_counterparty_liened_num.get(), 0);
    assert_eq!(source.source_claim_impaired_num.get(), lien_num);
    assert_eq!(source.source_lien_effective_reserved.get(), 0);
    assert_eq!(source.source_lien_counterparty_backing_num.get(), 0);
    assert_eq!(
        source.source_claim_bound_num.get()
            - source.source_claim_liened_num.get()
            - source.source_claim_impaired_num.get(),
        bound_num - lien_num,
        "forfeited face must not return to the unliened (spendable) claim"
    );

    // Market side: the impaired counters are retired and expiry-forfeited
    // principal is never resurrected as fresh backing.
    let bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(bucket.impaired_liened_backing_num, 0);
    assert_eq!(bucket.valid_liened_backing_num, 0);
    assert_eq!(bucket.fresh_unliened_backing_num, 0);

    winner.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

// The A6 classifier must REJECT as well as accept. fdf11670 ships only the
// positive fixture, so every rejection arm of
// account_source_credit_liens_are_fresh_and_releasable was uncovered: gutting the
// whole freshness/sufficiency block left the suite green. These two arms are the
// reachable ones for this fixture (it funds no insurance leg).
#[test]
fn v16_auto_crank_does_not_release_source_liens_against_stale_backing() {
    // (a) backing that has gone through the CANONICAL expiry transition.
    let (mut header, mut markets, mut winner_header) = flat_source_credit_lien_fixture();
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let winner = PortfolioV16ViewMut::new(&mut winner_header);
        let now = market.header.current_slot.get();
        assert!(
            market
                .build_actionable_summary_at_slot(&winner.as_view(), now)
                .unwrap()
                .source_liens_releasable,
            "fixture must start releasable, or the rejection below proves nothing"
        );
        drop(winner);
        market
            .expire_source_backing_bucket_not_atomic(0, 100)
            .unwrap();
    }
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    let now = market.header.current_slot.get();
    assert!(
        !market
            .build_actionable_summary_at_slot(&winner.as_view(), now)
            .unwrap()
            .source_liens_releasable,
        "expired backing must not classify as releasable"
    );
    assert_ne!(
        market
            .permissionless_auto_crank_not_atomic(
                &mut winner,
                AutoCrankWorkV16 {
                    now_slot: now,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .map(|r| r.selected),
        Ok(AutoCrankPlanV16::ReleaseSourceLiens),
        "the crank must not dispatch a release against expired backing"
    );
    drop(market);
    drop(winner);

    // (b) a bucket that no longer carries enough VALID LIENED backing to cover the
    // lien it is supposed to be releasing.
    let (mut header2, mut markets2, mut winner_header2) = flat_source_credit_lien_fixture();
    let mut bucket = markets2[0].engine.backing_long.try_to_runtime().unwrap();
    bucket.valid_liened_backing_num = 0;
    markets2[0].engine.backing_long = BackingBucketV16Account::from_runtime(&bucket);
    let market2 = MarketGroupV16ViewMut::new(&mut header2, &mut markets2);
    let winner2 = PortfolioV16ViewMut::new(&mut winner_header2);
    let now2 = market2.header.current_slot.get();
    assert!(
        !market2
            .build_actionable_summary_at_slot(&winner2.as_view(), now2)
            .unwrap()
            .source_liens_releasable,
        "a lien exceeding the bucket's valid liened backing must not classify as \
         releasable"
    );
}

#[test]
fn v16_released_pnl_conversion_consumes_the_backed_source_claim_exactly_once() {
    const CLAIM: u128 = 100;
    const BACKING: u128 = 2 * CLAIM;
    let claim_num = CLAIM * BOUND_SCALE;
    let backing_num = BACKING * BOUND_SCALE;
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut winner_header = account_fixture(1, 12);

    winner_header.pnl = V16PodI128::new((2 * CLAIM) as i128);
    for domain in 0..2 {
        winner_header.source_domains[domain].domain = V16PodU32::new(domain as u32);
        winner_header.source_domains[domain].source_claim_market_id = V16PodU64::new(1);
        winner_header.source_domains[domain].source_claim_bound_num = V16PodU128::new(claim_num);
    }
    header.pnl_pos_tot = V16PodU128::new(2 * CLAIM);
    header.pnl_pos_bound_tot_num = V16PodU128::new(2 * claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(2 * CLAIM);
    header.source_claim_bound_total_num = V16PodU128::new(2 * claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(backing_num);
    header.vault = V16PodU128::new(BACKING);

    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            positive_claim_bound_num: claim_num,
            exact_positive_claim_num: claim_num,
            credit_rate_num: 0,
            ..SourceCreditStateV16::EMPTY
        });
    markets[0].engine.backing_long = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id: 1,
        ..BackingBucketV16::EMPTY
    });
    markets[0].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            positive_claim_bound_num: claim_num,
            exact_positive_claim_num: claim_num,
            fresh_reserved_backing_num: backing_num,
            credit_rate_num: CREDIT_RATE_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[0].engine.backing_short = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id: 1,
        fresh_unliened_backing_num: backing_num,
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut winner_header);
    market
        .validate_shape()
        .expect("cross-domain fixture must be a valid market state");
    winner
        .validate_with_market(&market.as_view())
        .expect("cross-domain fixture must be a valid portfolio state");
    market.full_account_refresh_not_atomic(&mut winner).unwrap();

    assert_eq!(
        market
            .convert_released_pnl_to_capital_not_atomic(&mut winner)
            .expect("the funded source claim must convert"),
        CLAIM
    );
    assert_eq!(winner.header.capital.get(), CLAIM);
    assert_eq!(winner.header.pnl.get(), CLAIM as i128);
    assert_eq!(winner.header.source_domains[0].domain.get(), 0);
    assert_eq!(
        winner.header.source_domains[0].source_claim_bound_num.get(),
        claim_num,
        "the unfunded source claim must not be burned for another domain's backing"
    );
    assert_eq!(winner.header.source_domains[1], Default::default());

    market.full_account_refresh_not_atomic(&mut winner).unwrap();
    assert_eq!(
        market.convert_released_pnl_to_capital_not_atomic(&mut winner),
        Err(V16Error::LockActive),
        "the same funded source backing must not convert a second source claim"
    );
    assert_eq!(winner.header.capital.get(), CLAIM);
    winner.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

#[test]
fn v16_residual_reward_credit_is_capped_by_available_crystallized_loss() {
    let (mut header, mut markets) = market_fixture(1, 1_000);
    header.config.initial_margin_bps = V16PodU64::new(500);
    header.config.maintenance_margin_bps = V16PodU64::new(500);
    let mut taker_header = account_fixture(1, 25);
    let mut lp_header = account_fixture(1, 26);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
        let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
        market.deposit_not_atomic(&mut taker, 10_000).unwrap();
        market.deposit_not_atomic(&mut lp, 10_000).unwrap();
    }

    taker_header.residual_crystallized_loss_atoms_total = V16PodU128::new(30);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
    let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut taker,
            &mut lp,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 1_000,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    assert_eq!(taker.header.residual_spent_principal_atoms_total.get(), 30);
    assert_eq!(lp.header.residual_received_atoms_total.get(), 30);
    taker.validate_with_market(&market.as_view()).unwrap();
    lp.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_principal_loss_crystallizes_residual_budget_monotonically() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 27);
    header.vault = V16PodU128::new(100);
    header.c_tot = V16PodU128::new(100);
    header.negative_pnl_account_count = V16PodU64::new(1);
    account_header.capital = V16PodU128::new(100);
    account_header.pnl = V16PodI128::new(-40);
    account_header.residual_crystallized_loss_atoms_total = V16PodU128::new(7);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market
        .sync_account_fee_to_slot_not_atomic(&mut account, 1, 0)
        .unwrap();

    assert_eq!(account.header.capital.get(), 60);
    assert_eq!(account.header.pnl.get(), 0);
    assert_eq!(
        account.header.residual_crystallized_loss_atoms_total.get(),
        47,
        "historical crystallized-loss budget only increases by real capital consumed"
    );
    account.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

#[test]
fn v16_source_backed_conversion_ignores_unrelated_historical_bankruptcy() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut account_header = account_fixture(1, 18);
    let claim = 20u128;
    let claim_num = claim * BOUND_SCALE;
    // Keep an unrelated live residual and historical opposite-domain insurance
    // spend present. Only the claim-free terminal sweep may recredit an overlap.
    // (upstream 76a86f48)
    header.vault = V16PodU128::new(claim + 10);
    header.insurance = V16PodU128::new(5);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(5);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
    account_header.pnl = V16PodI128::new(claim as i128);
    account_header.source_domains[0].domain = V16PodU32::new(0);
    account_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    account_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
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
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    markets[0].engine.insurance_domain_budget_short = V16PodU128::new(10);
    markets[0].engine.insurance_domain_spent_short = V16PodU128::new(5);

    header.bankruptcy_hlock_active = 1;
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market
        .full_account_refresh_not_atomic(&mut account)
        .unwrap();
    let converted = market
        .convert_released_pnl_to_capital_not_atomic(&mut account)
        .expect("flat source-backed PnL should be convertible when backing is available");

    assert_eq!(converted, claim);
    assert_eq!(account.header.pnl.get(), 0);
    assert_eq!(account.header.capital.get(), claim);
    assert_eq!(
        market.header.insurance.get(),
        5,
        "live conversion must not recredit historical insurance spend"
    );
    assert_eq!(
        market.markets[0].engine.insurance_domain_spent_short.get(),
        5
    );
    assert_eq!(
        account.header.source_domains[0],
        PortfolioSourceDomainV16Account::default()
    );
    account.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

/// 3c01f42b drops the preflight's own `validate_with_market` because
/// `ensure_favorable_action_allowed`, two statements below, already performs it.
/// Nothing in the suite pinned that surviving validation, so this test does: a
/// provenance-mismatched account must still be rejected with ProvenanceMismatch,
/// not with whatever later gate happens to trip first.
#[test]
fn v16_released_pnl_conversion_still_rejects_a_foreign_account() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 81);
    account_header.provenance_header.market_group_id = [9u8; 32];

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    assert_eq!(
        market.convert_released_pnl_to_capital_not_atomic(&mut account),
        Err(V16Error::ProvenanceMismatch)
    );
}

#[test]
fn v16_sparse_source_domains_reject_unoccupied_tagged_slot() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut account_header = account_fixture(1, 19);
    account_header.source_domains[1].domain = V16PodU32::new(1);
    account_header.source_domains[1].source_claim_market_id = V16PodU64::new(1);

    let market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let account = PortfolioV16View::new(&account_header);
    assert_eq!(
        account.validate_with_market(&market.as_view()),
        Err(V16Error::HiddenLeg),
        "unoccupied tagged source-domain slots must not survive validation"
    );
}

#[test]
fn v16_mutable_view_compacts_persisted_domain_indexed_source_claim_before_deposit() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut account_header = account_fixture(1, 20);
    let claim = 7u128;
    let claim_num = claim * BOUND_SCALE;
    header.vault = V16PodU128::new(claim);
    header.c_tot = V16PodU128::new(0);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    account_header.pnl = V16PodI128::new(claim as i128);
    account_header.source_domains[1].domain = V16PodU32::new(1);
    account_header.source_domains[1].source_claim_market_id = V16PodU64::new(1);
    account_header.source_domains[1].source_claim_bound_num = V16PodU128::new(claim_num);
    markets[0].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            positive_claim_bound_num: claim_num,
            exact_positive_claim_num: claim_num,
            fresh_reserved_backing_num: claim_num,
            credit_rate_num: CREDIT_RATE_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[0].engine.backing_short = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id: 1,
        fresh_unliened_backing_num: claim_num,
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    PortfolioV16View::new(&account_header)
        .validate_with_market(&market.as_view())
        .expect("read-only validation must accept coherent domain-indexed parked PnL");
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market
        .deposit_not_atomic(&mut account, 3)
        .expect("later deposit must accept a persisted parked source claim");

    assert_eq!(account.header.capital.get(), 3);
    assert_eq!(account.header.source_domains[0].domain.get(), 1);
    assert_eq!(
        account.header.source_domains[0]
            .source_claim_bound_num
            .get(),
        claim_num
    );
    assert_eq!(
        account.header.source_domains[1],
        PortfolioSourceDomainV16Account::default()
    );
    account.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

#[test]
fn v16_trade_created_parked_source_claim_survives_later_deposit() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 21);
    let mut short_header = account_fixture(1, 22);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
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
        market
            .accrue_asset_to_not_atomic(0, 2, 101, 0, true)
            .unwrap();
        market.full_account_refresh_not_atomic(&mut long).unwrap();
    }

    assert!(long_header.pnl.get() > 0);
    assert!(
        long_header
            .source_domains
            .iter()
            .any(|source| source.domain.get() == 1
                && source.source_claim_market_id.get() == 1
                && source.source_claim_bound_num.get() != 0),
        "winner refresh must persist the source-domain claim created by K/F settlement"
    );

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    PortfolioV16View::new(&long_header)
        .validate_with_market(&market.as_view())
        .expect("read-only validation must accept the trade-created parked claim");
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    market
        .deposit_not_atomic(&mut long, 3)
        .expect("later deposit must accept the persisted trade-created parked claim");

    assert_eq!(long.header.capital.get(), 1_003);
    long.validate_with_market(&market.as_view()).unwrap();
    market.validate_shape().unwrap();
}

// Converged from toly v16.8.11 (ce073dc): certifies the new first-class engine
// API add_account_source_positive_pnl_not_atomic — value-neutral notional
// attribution with account -> domain -> group claim aggregates in lockstep, and
// the non-Live rejection.
#[test]
fn v16_grant_source_positive_pnl_attributes_claims_and_aggregates_in_lockstep() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut account_header = account_fixture(1, 31);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    market
        .add_account_source_positive_pnl_not_atomic(&mut account, 0, 25)
        .expect("granting source-attributed positive pnl must succeed in Live");

    assert_eq!(account.header.pnl.get(), 25);
    assert_eq!(
        account.header.source_domains[0]
            .source_claim_bound_num
            .get(),
        25 * BOUND_SCALE
    );
    assert_eq!(market.header.pnl_pos_tot.get(), 25);
    assert_eq!(market.header.pnl_pos_bound_tot_num.get(), 25 * BOUND_SCALE);
    assert_eq!(
        market.header.source_claim_bound_total_num.get(),
        25 * BOUND_SCALE
    );
    // The grant is notional attribution: no quote value moves.
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.header.c_tot.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(account.validate_with_market(&market.as_view()), Ok(()));

    // Granting in a non-Live market is rejected before any mutation.
    market.header.mode = 1; // Resolved
    market.header.resolved_slot = V16PodU64::new(1);
    let err = market.add_account_source_positive_pnl_not_atomic(&mut account, 0, 1);
    assert_eq!(err, Err(V16Error::LockActive));
    assert_eq!(account.header.pnl.get(), 25);
}

/// A B-settlement loss must retire the claim of the leg's own opposite-side
/// source domain before any unrelated domain's claim (upstream 3ed6e11b, made
/// domain-first with an explicit fallback in ce01590b). The unrelated domain must
/// occupy the earlier portfolio slot, which is exactly the slot the pre-port
/// generic burn walked first. Since c0dec8ce every mutable view keeps occupied
/// source domains in ascending domain order, so allocation order alone no longer
/// decides the slot: the unrelated domain (asset 0 short, domain 1) is chosen to
/// sort before the leg's own domain (asset 1 short, domain 3).
#[test]
fn v16_b_settlement_loss_retires_the_legs_own_source_domain_first() {
    const LOT_Q: u128 = 1_000 * POS_SCALE;
    // loss = loss_weight * delta_b / SOCIAL_LOSS_DEN = 1e9 * 1e13 / 1e21 = 10 atoms.
    const B_TARGET: u128 = 10_000_000_000_000;
    const LOSS_ATOMS: u128 = 10;
    const GRANT_ATOMS: u128 = 40;
    const LEG_ASSET: usize = 1;
    const LEG_DOMAIN: usize = 3;
    const UNRELATED_DOMAIN: usize = 1;

    let (mut header, mut markets) = market_fixture(2, 100);
    let mut long_header = account_fixture(2, 71);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut long, UNRELATED_DOMAIN, GRANT_ATOMS)
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut long, LEG_DOMAIN, GRANT_ATOMS)
            .unwrap();
    }
    assert_eq!(
        long_header.source_domains[0].domain.get() as usize,
        UNRELATED_DOMAIN,
        "the unrelated domain must occupy the earlier slot for this to be a real test"
    );
    assert_eq!(
        long_header.source_domains[1].domain.get() as usize,
        LEG_DOMAIN
    );

    let mut asset = markets[LEG_ASSET].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = LOT_Q;
    asset.oi_eff_short_q = LOT_Q;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    asset.loss_weight_sum_long = LOT_Q;
    asset.loss_weight_sum_short = LOT_Q;
    asset.b_long_num = B_TARGET;
    markets[LEG_ASSET].engine.asset = AssetStateV16Account::from_runtime(&asset);

    long_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: LEG_ASSET as u32,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: signed_q(LOT_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: LOT_Q,
        b_snap: 0,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    long_header.active_bitmap[0] = V16PodU64::new(1);
    long_header.health_cert.valid = 0;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();

    let outcome = market
        .permissionless_crank_not_atomic(
            &mut long,
            PermissionlessCrankRequestV16 {
                now_slot: 1,
                asset_index: LEG_ASSET,
                effective_price: 100,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::SettleB {
                    asset_index: LEG_ASSET,
                },
            },
        )
        .unwrap();
    let PermissionlessProgressOutcomeV16::AccountBChunk(chunk) = outcome else {
        panic!("SettleB must return a B chunk, got {outcome:?}");
    };
    assert_eq!(chunk.delta_b, B_TARGET);
    assert_eq!(chunk.loss, LOSS_ATOMS);
    assert_eq!(chunk.remaining_after, 0);

    assert_eq!(
        long.header.pnl.get() as u128,
        2 * GRANT_ATOMS - LOSS_ATOMS,
        "the loss reduces the account's positive PnL"
    );
    let claim_for = |domain: usize| -> u128 {
        long.header
            .source_domains
            .iter()
            .filter(|source| source.domain.get() as usize == domain)
            .map(|source| source.source_claim_bound_num.get())
            .sum()
    };
    assert_eq!(
        claim_for(LEG_DOMAIN),
        (GRANT_ATOMS - LOSS_ATOMS) * BOUND_SCALE,
        "the leg's own opposite-side domain absorbs the whole B loss"
    );
    assert_eq!(
        claim_for(UNRELATED_DOMAIN),
        GRANT_ATOMS * BOUND_SCALE,
        "an unrelated domain's claim is untouched by another asset's B loss"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
}

/// The fallback half of the same rule, which ce01590b makes an explicit
/// partition: a loss larger than the leg's own domain claim exhausts that domain
/// and only the strict remainder reaches any other domain. As above, the unrelated
/// domain is chosen to sort before the leg's own domain under c0dec8ce's canonical
/// source-domain order, so a generic slot walk would burn it first.
#[test]
fn v16_b_settlement_loss_spills_past_an_exhausted_own_source_domain() {
    const LOT_Q: u128 = 1_000 * POS_SCALE;
    // loss = loss_weight * delta_b / SOCIAL_LOSS_DEN = 1e9 * 1e13 / 1e21 = 10 atoms.
    const B_TARGET: u128 = 10_000_000_000_000;
    const LOSS_ATOMS: u128 = 10;
    const UNRELATED_GRANT_ATOMS: u128 = 40;
    const LEG_GRANT_ATOMS: u128 = 4;
    const LEG_ASSET: usize = 1;
    const LEG_DOMAIN: usize = 3;
    const UNRELATED_DOMAIN: usize = 1;

    let (mut header, mut markets) = market_fixture(2, 100);
    let mut long_header = account_fixture(2, 71);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(
                &mut long,
                UNRELATED_DOMAIN,
                UNRELATED_GRANT_ATOMS,
            )
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut long, LEG_DOMAIN, LEG_GRANT_ATOMS)
            .unwrap();
    }
    assert_eq!(
        long_header.source_domains[0].domain.get() as usize,
        UNRELATED_DOMAIN,
        "the unrelated domain must occupy the earlier slot for this to be a real test"
    );
    assert_eq!(
        long_header.source_domains[1].domain.get() as usize,
        LEG_DOMAIN
    );

    let mut asset = markets[LEG_ASSET].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = LOT_Q;
    asset.oi_eff_short_q = LOT_Q;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    asset.loss_weight_sum_long = LOT_Q;
    asset.loss_weight_sum_short = LOT_Q;
    asset.b_long_num = B_TARGET;
    markets[LEG_ASSET].engine.asset = AssetStateV16Account::from_runtime(&asset);

    long_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: LEG_ASSET as u32,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: signed_q(LOT_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: LOT_Q,
        b_snap: 0,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    long_header.active_bitmap[0] = V16PodU64::new(1);
    long_header.health_cert.valid = 0;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();

    let outcome = market
        .permissionless_crank_not_atomic(
            &mut long,
            PermissionlessCrankRequestV16 {
                now_slot: 1,
                asset_index: LEG_ASSET,
                effective_price: 100,
                funding_rate_e9: 0,
                action: PermissionlessCrankActionV16::SettleB {
                    asset_index: LEG_ASSET,
                },
            },
        )
        .unwrap();
    let PermissionlessProgressOutcomeV16::AccountBChunk(chunk) = outcome else {
        panic!("SettleB must return a B chunk, got {outcome:?}");
    };
    assert_eq!(chunk.delta_b, B_TARGET);
    assert_eq!(chunk.loss, LOSS_ATOMS);
    assert_eq!(chunk.remaining_after, 0);

    assert_eq!(
        long.header.pnl.get() as u128,
        UNRELATED_GRANT_ATOMS + LEG_GRANT_ATOMS - LOSS_ATOMS,
        "the loss reduces the account's positive PnL"
    );
    let claim_for = |domain: usize| -> u128 {
        long.header
            .source_domains
            .iter()
            .filter(|source| source.domain.get() as usize == domain)
            .map(|source| source.source_claim_bound_num.get())
            .sum()
    };
    assert_eq!(
        claim_for(LEG_DOMAIN),
        0,
        "the leg's own opposite-side domain is exhausted first"
    );
    assert_eq!(
        claim_for(UNRELATED_DOMAIN),
        (UNRELATED_GRANT_ATOMS - (LOSS_ATOMS - LEG_GRANT_ATOMS)) * BOUND_SCALE,
        "only the strict remainder past the exhausted own domain reaches another domain"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
}

// ---------------------------------------------------------------------------
// Protocol-fee design §1A: taker-only trade fee charging.
// ---------------------------------------------------------------------------

#[test]
fn v16_taker_only_charges_long_side_when_taker_is_long_account() {
    let (mut header, mut markets) = market_fixture_with_trade_fee(1, 100, 1_000);
    let mut long_header = account_fixture(1, 41);
    let mut short_header = account_fixture(1, 42);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let short_capital_before = short.header.capital.get();

    let outcome = market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 1_000, // notional 100 -> fee 10
            },
            true, // long_account is the taker
        )
        .unwrap();

    assert_eq!(outcome.fee_a, 10, "taker (long) pays the full fee");
    assert_eq!(outcome.fee_b, 0, "maker (short) pays nothing");
    assert_eq!(long.header.capital.get(), 1_000 - 10);
    assert_eq!(
        short.header.capital.get(),
        short_capital_before,
        "maker's capital is byte-identical before/after the fee-bearing fill"
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_taker_only_charges_short_side_when_taker_is_short_account() {
    let (mut header, mut markets) = market_fixture_with_trade_fee(1, 100, 1_000);
    let mut long_header = account_fixture(1, 43);
    let mut short_header = account_fixture(1, 44);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let long_capital_before = long.header.capital.get();

    let outcome = market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 1_000,
            },
            false, // short_account is the taker
        )
        .unwrap();

    assert_eq!(outcome.fee_a, 0, "maker (long) pays nothing");
    assert_eq!(outcome.fee_b, 10, "taker (short) pays the full fee");
    assert_eq!(
        long.header.capital.get(),
        long_capital_before,
        "maker's capital is byte-identical before/after the fee-bearing fill"
    );
    assert_eq!(short.header.capital.get(), 1_000 - 10);
    market.validate_shape().unwrap();
}

// E4 (upstream 8f25aa5d): a sub-atom fill (size_q * exec_price / POS_SCALE < 1,
// i.e. floor-notional == 0) must still charge a nonzero fee via ceil-notional,
// because it opens nonzero OI (free risk) despite the floored notional reading
// zero. Adapted from upstream's `v16_subatom_trade_charges_fee_on_ceil_fee_notional`
// for this fork's taker-only single-payer fee model (upstream charges both legs
// independently; here exactly one side -- the taker -- pays the fee).
#[test]
fn v16_subatom_trade_charges_fee_on_ceil_fee_notional() {
    let (mut header, mut markets) = market_fixture_with_trade_fee(1, 100, 1);
    let mut long_header = account_fixture(1, 213);
    let mut short_header = account_fixture(1, 214);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    // sub_atom_size * exec_price / POS_SCALE floors to 0 (999_900 / 1_000_000),
    // but ceils to 1 -- this is the exact boundary upstream's fix targets.
    let sub_atom_size = POS_SCALE / 100 - 1;
    let outcome = market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(sub_atom_size),
                exec_price: 100,
                fee_bps: 1,
            },
            true, // long_account is the taker
        )
        .unwrap();

    assert_eq!(
        outcome.notional, 0,
        "floor-notional (margin/PnL basis) is unaffected by the fee fix"
    );
    assert_eq!(
        outcome.fee_a, 1,
        "ceil-notional fee: sub-atom fill must not charge a fee of 0"
    );
    assert_eq!(
        outcome.fee_b, 0,
        "maker (short) pays nothing under taker-only"
    );
    assert_eq!(long.header.capital.get(), 1_000 - 1);
    assert_eq!(short.header.capital.get(), 1_000);
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_long_q.get(),
        sub_atom_size,
        "nonzero risk was opened despite the floored notional reading zero"
    );
    assert_eq!(
        market.markets[0].engine.asset.oi_eff_short_q.get(),
        sub_atom_size
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_taker_only_batch_mixed_spread_charges_taker_on_every_leg() {
    let (mut header, mut markets) = market_fixture_with_trade_fee(2, 100, 1_000);
    let mut taker_header = account_fixture(2, 45);
    let mut lp_header = account_fixture(2, 46);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
        let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
        market.deposit_not_atomic(&mut taker, 1_000).unwrap();
        market.deposit_not_atomic(&mut lp, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
    let mut lp = PortfolioV16ViewMut::new(&mut lp_header);
    let lp_capital_before = lp.header.capital.get();

    // A mixed long/short spread against one LP: taker (account_a, the
    // engine's fixed first positional account for batches per design §1A.3)
    // goes long asset 0 and short asset 1.
    let requests = [
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 1_000,
        },
        TradeRequestV16 {
            asset_index: 1,
            size_q: -signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 1_000,
        },
    ];

    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(
            &mut taker, &mut lp, &requests,
            true, // taker == account_a is always the engine's first (long_account) slot for batches
        )
        .unwrap();

    assert_eq!(outcome.fill_count, 2);
    assert_eq!(
        outcome.fee_a, 20,
        "taker pays fee on both legs of the spread (10 + 10)"
    );
    assert_eq!(outcome.fee_b, 0, "LP pays nothing on either leg");
    assert_eq!(taker.header.capital.get(), 1_000 - 20);
    assert_eq!(
        lp.header.capital.get(),
        lp_capital_before,
        "LP's capital is unchanged across every leg of the batch"
    );
    market.validate_shape().unwrap();
}

#[test]
fn v16_taker_only_n1_maker_fallback_when_taker_pnl_negative() {
    let (mut header, mut markets) = market_fixture_with_trade_fee(1, 100, 1_000);
    let mut long_header = account_fixture(1, 47);
    let mut short_header = account_fixture(1, 48);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
        // Certify both accounts once while flat/pnl==0 so `stale_state` is
        // false and `health_cert.valid` is true against the *current*
        // epochs/bitmap. `settle_account_for_position_action_and_refresh_not_atomic`
        // (called at the top of the trade pipeline) then takes its early-out
        // branch instead of re-settling the account, which is what lets the
        // negative pnl injected below survive into the fee-charge site
        // un-settled — exactly the "current path deliberately skips loss
        // settlement" property the N1 guard is written against.
        market.full_account_refresh_not_atomic(&mut long).unwrap();
        market.full_account_refresh_not_atomic(&mut short).unwrap();
    }
    // N1: the taker (long) already carries a negative PnL, which fires the
    // pre-existing `charge_account_fee_current_not_atomic` waiver
    // (`account.header.pnl.get() < 0`). Under pure taker-only charging this
    // would let an underwater taker trade fee-free; the maker-fallback must
    // instead charge the solvent maker `fee.min(maker.capital)`.
    long_header.pnl = V16PodI128::new(-5);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let long_capital_before = long.header.capital.get();

    let outcome = market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 1_000,
            },
            true, // long_account (the underwater taker) initiated the trade
        )
        .unwrap();

    assert_eq!(
        outcome.fee_a, 0,
        "taker's own charge is waived by the pnl<0 guard, not stripped"
    );
    assert_eq!(
        outcome.fee_b, 10,
        "N1 fallback: the solvent maker is charged instead of nobody"
    );
    assert_eq!(
        long.header.capital.get(),
        long_capital_before,
        "the pnl<0 guard still protects the taker's own capital"
    );
    assert_eq!(
        long.header.pnl.get(),
        -5,
        "taker pnl untouched by the fee path"
    );
    assert_eq!(short.header.capital.get(), 1_000 - 10);
    market.validate_shape().unwrap();
}

#[test]
fn v16_taker_only_n1_no_fallback_when_fee_is_genuinely_zero() {
    // Distinguishes "fee == 0" (no fallback — nothing to collect from anyone)
    // from "pnl < 0 waived a nonzero fee" (fallback fires). Both taker and
    // maker have negative PnL here, but fee_bps is 0, so neither should ever
    // be charged and outcome.fee_a/fee_b must both be 0.
    let (mut header, mut markets) = market_fixture_with_trade_fee(1, 100, 1_000);
    let mut long_header = account_fixture(1, 49);
    let mut short_header = account_fixture(1, 50);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 1_000).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
        market.full_account_refresh_not_atomic(&mut long).unwrap();
        market.full_account_refresh_not_atomic(&mut short).unwrap();
    }
    long_header.pnl = V16PodI128::new(-5);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    let long_capital_before = long.header.capital.get();
    let short_capital_before = short.header.capital.get();

    let outcome = market
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

    assert_eq!(outcome.fee_a, 0);
    assert_eq!(outcome.fee_b, 0);
    assert_eq!(long.header.capital.get(), long_capital_before);
    assert_eq!(short.header.capital.get(), short_capital_before);
}

#[test]
fn v16_taker_only_n1_maker_fallback_when_taker_capital_zero_pnl_nonnegative() {
    // Fee-evasion regression (security review 2026-07-15, MEDIUM). Before the
    // fix, the maker-fallback trigger was
    // `taker_fee == 0 && fee != 0 && taker.pnl < 0`. A taker whose capital is
    // drawn to exactly 0 WITHOUT being underwater (pnl >= 0) also makes
    // `charge_account_fee_current_not_atomic` return 0 -- via
    // `fee.min(capital) == 0`, a structurally different reason than the
    // pnl<0 waiver -- but the old pnl<0 qualifier didn't fire for this case,
    // so the fallback never charged the maker either: the fee vanished
    // entirely (protocol/LP/creator/insurance all got 0).
    //
    // This reproduces the exact scenario the security review flagged: a
    // multi-leg batch where an EARLY leg drains the taker's capital to
    // exactly 0 (paying its own fee in full, so it is NOT underwater -- pnl
    // stays 0), and a LATER leg in the SAME batch then owes a nonzero fee
    // with nothing left to pay it. Leg 2 closes the position leg 1 opened
    // (net batch position == 0) so the batch-final initial-margin check
    // (`finish_trade_checks_not_atomic` certifies once, after all legs, for
    // multi-leg batches) sees a flat book and a trivial (zero) margin
    // requirement regardless of the taker's zero capital.
    let (mut header, mut markets) = market_fixture_with_trade_fee(2, 100, 1_000);
    let mut long_header = account_fixture(2, 51);
    let mut short_header = account_fixture(2, 52);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        // Taker (long) is funded with exactly one leg's fee (10) -- enough to
        // pay leg 1 in full and land at capital == 0, pnl == 0 (NOT
        // negative) before leg 2 is even evaluated.
        market.deposit_not_atomic(&mut long, 10).unwrap();
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    let requests = [
        // Leg 1: taker opens long POS_SCALE @ 100, fee 10 -- fully solvent,
        // pays in full, capital drops 10 -> 0.
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 1_000,
        },
        // Leg 2: taker closes the same position back to flat, notional 100,
        // fee 10 -- taker capital is now 0, so the taker's own charge
        // attempt collects 0 even though pnl is still 0 (not negative).
        TradeRequestV16 {
            asset_index: 0,
            size_q: -signed_q(POS_SCALE),
            exec_price: 100,
            fee_bps: 1_000,
        },
    ];

    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(
            &mut long, &mut short, &requests, true, // long_account is the taker on every leg
        )
        .unwrap();

    assert_eq!(outcome.fill_count, 2);
    assert_eq!(
        outcome.fee_a, 10,
        "taker pays leg 1 in full (solvent), then owes 0 on leg 2 (capital \
         exhausted) -- total taker-side charge is just leg 1's fee"
    );
    assert_eq!(
        outcome.fee_b, 10,
        "fix: leg 2's fee is NOT lost -- the maker-fallback fires because \
         the taker's own charge returned 0, even though the taker's pnl is \
         NOT negative (capital exhaustion, not the pnl<0 waiver)"
    );
    assert_eq!(long.header.capital.get(), 0, "taker fully drained by leg 1");
    assert_eq!(long.header.pnl.get(), 0, "taker was never underwater");
    assert_eq!(
        short.header.capital.get(),
        1_000 - 10,
        "maker pays leg 2's fee via the fallback"
    );
    market.validate_shape().unwrap();
}

// ---------------------------------------------------------------------------
// New engine primitive: withdraw_insurance_surplus_not_atomic (design §1.5).
// ---------------------------------------------------------------------------

#[test]
fn v16_withdraw_insurance_surplus_zero_amount_is_a_noop() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(500);
    header.insurance = V16PodU128::new(200);
    let vault_before = header.vault;
    let insurance_before = header.insurance;

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.withdraw_insurance_surplus_not_atomic(0).unwrap();

    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.insurance, insurance_before);
}

#[test]
fn v16_withdraw_insurance_surplus_rejects_amount_exceeding_surplus() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(500);
    header.insurance = V16PodU128::new(200);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(150);
    // Unbudgeted surplus = insurance(200) - source_reserved(0) - budget_remaining(150) = 50.
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    let err = market.withdraw_insurance_surplus_not_atomic(51);
    assert_eq!(err, Err(V16Error::LockActive));
}

#[test]
fn v16_withdraw_insurance_surplus_rejects_amount_exceeding_vault() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(40);
    header.insurance = V16PodU128::new(200);
    // Unbudgeted surplus = 200 (no reservations/budget set), but vault only
    // has 40 physical atoms — the vault bound must still gate the transfer.
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    let err = market.withdraw_insurance_surplus_not_atomic(41);
    assert_eq!(err, Err(V16Error::LockActive));
}

#[test]
fn v16_withdraw_insurance_surplus_exact_boundary_succeeds() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(500);
    header.insurance = V16PodU128::new(200);
    header.insurance_domain_budget_remaining_total = V16PodU128::new(150);
    // Exact boundary: surplus == 50, withdraw exactly 50.
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market.withdraw_insurance_surplus_not_atomic(50).unwrap();

    assert_eq!(market.header.vault.get(), 450);
    assert_eq!(market.header.insurance.get(), 150);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        150,
        "domain budgets are untouched by the surplus withdrawal"
    );
    market.validate_shape().unwrap();
}

// --- E2 (upstream engine #108, fixes #97): fresh risk must be blocked while
// either side of an asset is mid side-recovery (ResetPending/DrainOnly), not
// just while the asset's overall lifecycle is non-Active. Risk-REDUCING
// trades must remain admitted throughout recovery.

#[test]
fn v16_trade_rejects_fresh_risk_when_either_side_is_recovering() {
    let cases = [
        (SideModeV16::ResetPending, SideModeV16::Normal),
        (SideModeV16::Normal, SideModeV16::ResetPending),
        (SideModeV16::DrainOnly, SideModeV16::Normal),
        (SideModeV16::Normal, SideModeV16::DrainOnly),
    ];
    for (mode_long, mode_short) in cases {
        let (mut header, mut markets) = market_fixture(1, 100);
        let mut long_header = account_fixture(1, 60);
        let mut short_header = account_fixture(1, 61);
        {
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut long = PortfolioV16ViewMut::new(&mut long_header);
            let mut short = PortfolioV16ViewMut::new(&mut short_header);
            market.deposit_not_atomic(&mut long, 1_000).unwrap();
            market.deposit_not_atomic(&mut short, 1_000).unwrap();
        }
        let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
        asset.mode_long = mode_long;
        asset.mode_short = mode_short;
        markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);

        let vault_before = header.vault.get();
        let c_tot_before = header.c_tot.get();
        let insurance_before = header.insurance.get();

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        let long_capital_before = long.header.capital.get();
        let short_capital_before = short.header.capital.get();

        let res = market.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        );

        assert_eq!(
            res,
            Err(V16Error::LockActive),
            "fresh risk admitted with mode_long={mode_long:?} mode_short={mode_short:?}"
        );
        // Rollback-clean rejection: no partial state mutation, no fee leakage.
        assert_eq!(market.header.vault.get(), vault_before);
        assert_eq!(market.header.c_tot.get(), c_tot_before);
        assert_eq!(market.header.insurance.get(), insurance_before);
        assert_eq!(long.header.capital.get(), long_capital_before);
        assert_eq!(short.header.capital.get(), short_capital_before);
        market.validate_shape().unwrap();
    }
}

#[test]
fn v16_trade_keeps_two_sided_risk_reduction_open_during_side_recovery() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut long_header = account_fixture(1, 62);
    let mut short_header = account_fixture(1, 63);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut long = PortfolioV16ViewMut::new(&mut long_header);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut long, 10_000).unwrap();
        market.deposit_not_atomic(&mut short, 10_000).unwrap();
        // Open long +2*POS_SCALE / short -2*POS_SCALE while both side modes
        // are still Normal.
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut long,
                &mut short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(2 * POS_SCALE),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }

    // Now put the asset mid side-recovery on BOTH sides simultaneously (the
    // gate is not side-specific by design).
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.mode_long = SideModeV16::ResetPending;
    asset.mode_short = SideModeV16::DrainOnly;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);

    // A matched reduction (-POS_SCALE) shrinks both legs' magnitude
    // (long: +2 -> +1, short: -2 -> -1) and must still be admitted.
    let outcome = market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: -signed_q(POS_SCALE),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .expect("risk-reducing trade must stay open during side recovery");

    assert_eq!(outcome.notional, 100);
    let long_leg = long.header.legs[0].try_to_runtime().unwrap();
    let short_leg = short.header.legs[0].try_to_runtime().unwrap();
    assert_eq!(long_leg.basis_pos_q, signed_q(POS_SCALE));
    assert_eq!(short_leg.basis_pos_q, -signed_q(POS_SCALE));
    market.validate_shape().unwrap();
}

// E5 (upstream engine #109 / 143e68c4, "Prevent same-trade OI masking"): a
// single trade may reduce only OI that existed BEFORE that trade -- otherwise
// one leg's same-call addition can be spent as if it were preexisting
// reduction capacity on the other leg, making aggregate accounting depend on
// mutation order within one apply_trade_after_refresh_not_atomic call.
//
// Scenario: `liquidated` flips short(-10) -> long(+1) in the same call that
// `survivor` reduces long(+13) -> long(+2). In isolation, survivor's leg
// alone appears to free up 11 units of long-side reduction capacity, but the
// asset's PRE-TRADE ledger only records oi_eff_long_q = oi_eff_short_q =
// MATCHED_Q = 10 units (the pre-fix bug: the ledger is authoritative, not
// whatever a single leg's raw basis happens to show, and one leg cannot
// "loan" the other leg's same-call delta as spendable reduction capacity).
// The gate must reject with LockActive and mutate NOTHING -- not the asset
// ledger, not vault/c_tot/insurance, not either leg -- proving this is a
// preflight rejection, not a partial-apply rollback.
#[test]
fn v16_crossed_trade_cannot_spend_same_call_addition_as_preexisting_oi() {
    const MATCHED_Q: u128 = 10 * POS_SCALE;
    const LIQUIDATED_SHORT_Q: u128 = 10 * POS_SCALE;
    const SURVIVOR_LONG_Q: u128 = 13 * POS_SCALE;
    const FLIP_SIZE_Q: u128 = 11 * POS_SCALE; // liquidated: -10 -> +1; survivor: +13 -> +2

    let (mut header, mut markets) = market_fixture(1, 100);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = MATCHED_Q;
    asset.oi_eff_short_q = MATCHED_Q;
    asset.loss_weight_sum_long = MATCHED_Q;
    asset.loss_weight_sum_short = MATCHED_Q;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    // resolved_payout_blocker_count must reconcile with the asset's own
    // stored_pos_count_long(1) + stored_pos_count_short(1) totals, or
    // set_asset_state's delta-reconciliation throws CounterUnderflow before
    // the trade path (and therefore the OI gate) is ever reached.
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    let mut liquidated_header = account_fixture(1, 217);
    liquidated_header.capital = V16PodU128::new(1_000_000);
    liquidated_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Short,
        basis_pos_q: -signed_q(LIQUIDATED_SHORT_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_short,
        f_snap: asset.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_short,
        loss_weight: LIQUIDATED_SHORT_Q,
        b_snap: asset.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_short,
        b_stale: false,
        stale: false,
    });
    liquidated_header.active_bitmap[0] = V16PodU64::new(1);

    let mut survivor_header = account_fixture(1, 218);
    survivor_header.capital = V16PodU128::new(1_000_000);
    survivor_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: signed_q(SURVIVOR_LONG_Q),
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: SURVIVOR_LONG_Q,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    survivor_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut liquidated = PortfolioV16ViewMut::new(&mut liquidated_header);
    let mut survivor = PortfolioV16ViewMut::new(&mut survivor_header);

    let asset_before = market.markets[0].engine.asset;
    let vault_before = market.header.vault.get();
    let c_tot_before = market.header.c_tot.get();
    let insurance_before = market.header.insurance.get();
    let liquidated_capital_before = liquidated.header.capital.get();
    let survivor_capital_before = survivor.header.capital.get();

    // `liquidated` is the long_account param (receives +FLIP_SIZE_Q, flipping
    // short(-10) -> long(+1)); `survivor` is the short_account param
    // (receives -FLIP_SIZE_Q, reducing long(+13) -> long(+2)).
    let result = market.execute_trade_with_fee_loss_stale_scoped_not_atomic(
        &mut liquidated,
        &mut survivor,
        TradeRequestV16 {
            asset_index: 0,
            size_q: signed_q(FLIP_SIZE_Q),
            exec_price: 100,
            fee_bps: 0,
        },
        true,
    );

    assert_eq!(result, Err(V16Error::LockActive));
    assert_eq!(
        market.markets[0].engine.asset, asset_before,
        "rejected trade must not mutate the asset ledger at all"
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(liquidated.header.capital.get(), liquidated_capital_before);
    assert_eq!(survivor.header.capital.get(), survivor_capital_before);
    let liquidated_leg = liquidated.header.legs[0].try_to_runtime().unwrap();
    let survivor_leg = survivor.header.legs[0].try_to_runtime().unwrap();
    assert_eq!(liquidated_leg.basis_pos_q, -signed_q(LIQUIDATED_SHORT_Q));
    assert_eq!(survivor_leg.basis_pos_q, signed_q(SURVIVOR_LONG_Q));
    market.validate_shape().unwrap();
}

// Builds a resolved market in which `taker` holds exactly one active leg (so
// `resolved_bankruptcy_attribution` resolves via the leg scan) and carries an
// unabsorbed loss larger than its capital. Returns the asset's `market_id` so the
// caller can stamp a prior close ledger onto the account if it wants one.
fn resolved_market_with_bankrupt_taker_funded(
    fund_insurance: bool,
) -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
    u64,
) {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut taker_header = account_fixture(1, 91);
    let mut maker_header = account_fixture(1, 92);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
        let mut maker = PortfolioV16ViewMut::new(&mut maker_header);
        market.deposit_not_atomic(&mut taker, 1_000).unwrap();
        market.deposit_not_atomic(&mut maker, 1_000).unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut taker,
                &mut maker,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POS_SCALE),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
        // With insurance funded the bankruptcy path consumes it and reaches
        // `advance_close_progress_ledger`'s ledger-state guard. Without it, the
        // advance short-circuits on an all-zero progress delta and the failure is
        // silent instead -- both variants are exercised below.
        if fund_insurance {
            market.deposit_domain_insurance_not_atomic(0, 500).unwrap();
            market.deposit_domain_insurance_not_atomic(1, 500).unwrap();
        }
        market.resolve_market_not_atomic(1).unwrap();
    }

    // Loss exceeds capital, so principal settlement cannot clear it and the
    // resolved close must route through the bankruptcy path.
    taker_header.pnl = V16PodI128::new(-5_000);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let market_id = markets[0].engine.asset.market_id.get();
    (header, markets, taker_header, market_id)
}

// E6 exempted finalized-inert ledgers inside `begin_close_progress_ledger`, but
// `settle_resolved_bankruptcy_negative_pnl` decides whether to CALL it by testing
// the raw `close_progress.active` flag. A finalized-inert ledger is still
// `active`, so the fresh close is skipped and the stale finalized ledger is kept;
// the following `advance_close_progress_ledger` then rejects it outright, and the
// whole resolved close reverts. An account that survived one fully-covered
// bankruptcy and meets a second at resolution can no longer be closed.
#[test]
fn e6_second_bankruptcy_reopens_finalized_inert_close_ledger() {
    let (mut header, mut markets, mut taker_header, market_id) =
        resolved_market_with_bankrupt_taker_funded(true);

    // An earlier bankruptcy on this account finished paying out in full: the
    // ledger is finalized with zero residual, but stays `active` to preserve
    // close identity for audit. `domain_side` is the side that BACKS the loss,
    // i.e. the opposite of the account's own leg (validated at the
    // `ledger.domain_side != opposite_side(leg.side)` check), so a long taker
    // carries a Short-domain ledger.
    taker_header.close_progress =
        CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
            active: true,
            finalized: true,
            canceled: false,
            close_id: 3,
            asset_index: 0,
            market_id,
            domain_side: SideV16::Short,
            gross_loss_at_close_start: 5,
            drift_reference_slot: 0,
            max_close_slot: 0,
            support_consumed: 5,
            junior_face_burned: 5,
            residual_remaining: 0,
            ..CloseProgressLedgerV16::EMPTY
        });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);

    // The constructed state must itself be valid, otherwise the revert below
    // would prove nothing about the close path.
    assert_eq!(
        market.validate_shape(),
        Ok(()),
        "market shape must be valid"
    );
    assert_eq!(
        taker.validate_with_market(&market.as_view()),
        Ok(()),
        "account (including the finalized-inert ledger) must be valid"
    );

    let outcome = market
        .close_resolved_account_not_atomic(&mut taker, 0)
        .expect("a second bankruptcy must reopen the inert close, not revert");
    assert!(matches!(outcome, ResolvedCloseOutcomeV16::Closed { .. }));

    // The replacement close is a well-formed first-class close, not a patched-up
    // remnant: the loss is absorbed, the close-id watermark advances rather than
    // colliding, the domain barrier it took is released again, and both validators
    // still accept the resulting state.
    assert_eq!(taker.header.pnl.get(), 0, "the loss is fully absorbed");
    let ledger = taker.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(ledger.close_id, 4, "close-id watermark advances from 3");
    assert!(ledger.finalized && ledger.residual_remaining == 0);
    assert_eq!(
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get(),
        0
    );
    assert_eq!(
        market.markets[0]
            .engine
            .pending_domain_loss_barrier_short
            .get(),
        0,
        "the barrier taken by the reopened close is released again"
    );
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(taker.validate_with_market(&market.as_view()), Ok(()));
}

// Control: identical account and market, but with no prior close on record. The
// same resolved close must not hit LockActive, which pins the finalized-inert
// ledger -- not the bankruptcy itself -- as the cause above.
#[test]
fn e6_resolved_close_on_bankruptcy_without_prior_close_is_not_blocked() {
    let (mut header, mut markets, mut taker_header, _market_id) =
        resolved_market_with_bankrupt_taker_funded(true);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);

    let result = market.close_resolved_account_not_atomic(&mut taker, 0);
    assert_ne!(
        result.err(),
        Some(V16Error::LockActive),
        "a first bankruptcy at resolution must not be blocked"
    );
}

// The same defect with no insurance on the loss-backing domain, where it is
// SILENT rather than an error and has market-wide reach.
//
// `consume_domain_insurance_for_negative_pnl` returns 0, so the `advance` that
// raises LockActive above is skipped. `book_bankruptcy_residual_chunk_*` is then
// reached with the stale finalized ledger, whose `residual_remaining` is 0, so
// both the booking and the advance short-circuit on their zero guards and the
// call returns Ok having booked nothing. The close makes no progress and can be
// re-cranked forever.
//
// The account's own capital is stranded, but the wider consequence is that
// `negative_pnl_account_count` never falls to zero, and
// `resolved_positive_payout_ready` gates every positive resolved payout on that
// counter -- so no winner in the market can be paid either.
#[test]
fn e6_second_bankruptcy_completes_without_insurance() {
    let (mut header, mut markets, mut taker_header, market_id) =
        resolved_market_with_bankrupt_taker_funded(false);

    taker_header.close_progress =
        CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
            active: true,
            finalized: true,
            canceled: false,
            close_id: 3,
            asset_index: 0,
            market_id,
            domain_side: SideV16::Short,
            gross_loss_at_close_start: 5,
            drift_reference_slot: 0,
            max_close_slot: 0,
            support_consumed: 5,
            junior_face_burned: 5,
            residual_remaining: 0,
            ..CloseProgressLedgerV16::EMPTY
        });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut taker = PortfolioV16ViewMut::new(&mut taker_header);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(taker.validate_with_market(&market.as_view()), Ok(()));

    // The reopened close books the residual as explicit loss and completes, with
    // no insurance available and without new capital being added.
    let outcome = market
        .close_resolved_account_not_atomic(&mut taker, 0)
        .expect("the close must progress rather than stall");
    assert!(
        matches!(outcome, ResolvedCloseOutcomeV16::Closed { .. }),
        "close completes instead of returning ProgressOnly forever"
    );

    assert_eq!(
        taker.header.pnl.get(),
        0,
        "the loss is absorbed, not parked"
    );
    // Before the fix this counter never returned to zero, and
    // `resolved_positive_payout_ready` gates every positive resolved payout on it
    // -- so a single stalled account withheld every winner's payout market-wide.
    assert_eq!(
        market.header.negative_pnl_account_count.get(),
        0,
        "the market's positive-payout gate is released"
    );
    let ledger = taker.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(ledger.close_id, 4, "close-id watermark advances from 3");
    assert!(ledger.finalized && ledger.residual_remaining == 0);
    assert_eq!(market.validate_shape(), Ok(()));
    assert_eq!(taker.validate_with_market(&market.as_view()), Ok(()));
}

/// #137 — the initial-margin source-credit lien must be released when the exposure
/// that required it is closed, so the account can convert its own positive PnL while
/// the market is still Live.
#[test]
fn im_lien_is_released_when_the_position_closes_in_live() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut long_header = account_fixture(1, 8);
    let mut short_header = account_fixture(1, 9);
    let claim = 100u128;
    let claim_num = claim * BOUND_SCALE;
    long_header.pnl = V16PodI128::new(claim as i128);
    long_header.source_domains[0].domain = V16PodU32::new(0);
    long_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    long_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
    // Backing principal is vault-funded and senior-side: vault must cover it.
    header.vault = V16PodU128::new(claim + header.vault.get());
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
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut short = PortfolioV16ViewMut::new(&mut short_header);
        market.deposit_not_atomic(&mut short, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(10 * POS_SCALE),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .expect("risk-increasing trade should atomically lien backed source credit for IM");

    assert_eq!(long.header.capital.get(), 0);
    assert_eq!(
        long.header.source_domains[0].source_claim_liened_num.get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        10
    );
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_counterparty_backing_num
            .get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .source_credit_long
            .valid_liened_backing_num
            .get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .valid_liened_backing_num
            .get(),
        10 * BOUND_SCALE
    );
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .fresh_unliened_backing_num
            .get(),
        90 * BOUND_SCALE
    );
    assert_eq!(
        market.convert_released_pnl_to_capital_not_atomic(&mut long),
        Err(V16Error::LockActive),
        "source-backed positive PnL must not be realized while the source-claim exposure remains open"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();

    let lien_open = long.header.source_domains[0].source_claim_liened_num.get();
    assert_ne!(lien_open, 0, "fixture must actually create an IM lien");

    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut short,
            &mut long,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(10 * POS_SCALE),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .expect("closing trade");

    // Refresh so certificate staleness (an unrelated gate) does not mask the result.
    let _ = market.full_account_refresh_not_atomic(&mut long);

    let converted = market.convert_released_pnl_to_capital_not_atomic(&mut long);
    let lien_closed = long.header.source_domains[0].source_claim_liened_num.get();
    println!("FIX137 lien_open={lien_open} lien_closed={lien_closed} convert={converted:?}");

    // The defect: the lien survived the close and pinned the conversion.
    assert_eq!(
        lien_closed, 0,
        "IM lien must be released once the exposure that required it is closed"
    );
    assert_ne!(
        converted,
        Err(V16Error::LockActive),
        "conversion must no longer be held by a stale source-credit lien in Live"
    );
    // NOT asserted: `converted.is_ok()`. This minimal fixture never accrues, so the
    // market's own freshness gate returns `Stale` — a legitimate and unrelated
    // guard. Asserting it here would test the fixture, not the fix. The two
    // assertions above are exactly what #137 changes, and both fail without it
    // (the lien stays at its opening value and the error is LockActive).
}

/// #146 — expiry moves liened counterparty backing to the impaired counters. A
/// subsequent Live release for a flat account must clear that lien without either
/// reporting an arithmetic underflow or restoring the forfeited backing.
#[test]
fn expired_im_lien_release_is_live_and_does_not_restore_backing() {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut long_header = account_fixture(1, 18);
    let mut short_header = account_fixture(1, 19);
    let claim = 100u128;
    let claim_num = claim * BOUND_SCALE;
    long_header.pnl = V16PodI128::new(claim as i128);
    long_header.source_domains[0].domain = V16PodU32::new(0);
    long_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    long_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
    header.vault = V16PodU128::new(claim);
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
        expiry_slot: 100,
        status: BackingBucketStatusV16::Fresh,
        ..BackingBucketV16::EMPTY
    });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut short, 1_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(10 * POS_SCALE),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .expect("risk-increasing trade must create the IM lien");
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut short,
            &mut long,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(10 * POS_SCALE),
                exec_price: 1,
                fee_bps: 0,
            },
            true,
        )
        .expect("closing trade must flatten the lien's exposure");

    let lien_num = long.header.source_domains[0]
        .source_lien_counterparty_backing_num
        .get();
    assert_ne!(lien_num, 0, "fixture must retain a stale IM lien");
    market
        .expire_source_backing_bucket_not_atomic(0, 100)
        .expect("the backing bucket must expire through the production transition");
    let impaired = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(impaired.status, BackingBucketStatusV16::Impaired);
    assert_eq!(impaired.impaired_liened_backing_num, lien_num);
    assert_eq!(impaired.fresh_unliened_backing_num, 0);

    let vault_before = market.header.vault.get();
    let capital_before = market.header.c_tot.get();
    let released = market.release_account_source_credit_liens_if_unneeded_not_atomic(&mut long);

    assert_eq!(released, Ok(10));
    assert_eq!(
        long.header.source_domains[0].source_claim_liened_num.get(),
        0
    );
    // 6c8d94bc reroutes this scenario from the terminal-release arm to the
    // ImpairCounterparty arm. Both drain the market-side impaired counters to
    // zero without resurrecting principal; they differ only in the label left on
    // an economically bare bucket. `prepare_counterparty_lien_terminal_release_delta`
    // inlines its own Empty fix-up, while `prepare_counterparty_impaired_lien_retirement_delta`
    // leaves `Expired` for `kernel_retirement_backing_normalization` (the shared
    // 379fbfea canonicalizer, reachable from the per-asset retirement sweep) to
    // collapse. Upstream's own 6c8d94bc fixture asserts `Expired` here too.
    let released_bucket = market.markets[0]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(
        released_bucket.status,
        BackingBucketStatusV16::Expired,
        "a fully drained impaired bucket keeps no residue"
    );
    // ...and it is economically bare on every field the shared 379fbfea
    // canonicalizer keys on, so the retirement sweep collapses it to Empty.
    assert_eq!(released_bucket.consumed_liened_backing_num, 0);
    assert_eq!(released_bucket.utilization_fee_earnings, 0);
    assert_eq!(released_bucket.impaired_liened_backing_num, 0);
    // 6c8d94bc: the forfeited face must stay LOCKED in the account's impaired
    // lane. Before this row the release arm zeroed `source_claim_liened_num`
    // without crediting `source_claim_impaired_num`, which handed the account
    // back `lien_num` of spendable UNLIENED source claim against principal that
    // expiry had already forfeited.
    assert_eq!(
        long.header.source_domains[0]
            .source_claim_impaired_num
            .get(),
        lien_num,
        "impaired claim attribution was not retained"
    );
    assert_eq!(
        long.header.source_domains[0]
            .source_lien_effective_reserved
            .get(),
        0
    );
    assert_eq!(
        released_bucket.fresh_unliened_backing_num, 0,
        "expired principal must never be resurrected as fresh backing"
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), capital_before);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}
/// Shared fixture for the Live source-credit-lien regressions below: an account
/// that opened a risk-increasing trade (minting the IM lien) and then closed it,
/// leaving a stale lien and realizable positive PnL.
#[allow(clippy::type_complexity)]
fn live_stale_im_lien_fixture() -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
) {
    let (mut header, mut markets) = market_fixture(1, 1);
    let mut long_header = account_fixture(1, 8);
    let mut short_header = account_fixture(1, 9);
    let claim = 100u128;
    let claim_num = claim * BOUND_SCALE;
    long_header.pnl = V16PodI128::new(claim as i128);
    long_header.source_domains[0].domain = V16PodU32::new(0);
    long_header.source_domains[0].source_claim_market_id = V16PodU64::new(1);
    long_header.source_domains[0].source_claim_bound_num = V16PodU128::new(claim_num);
    header.pnl_pos_tot = V16PodU128::new(claim);
    header.pnl_pos_bound_tot_num = V16PodU128::new(claim_num);
    header.pnl_pos_bound_tot = V16PodU128::new(claim);
    header.source_claim_bound_total_num = V16PodU128::new(claim_num);
    header.source_fresh_backing_total_num = V16PodU128::new(claim_num);
    header.vault = V16PodU128::new(claim + header.vault.get());
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
        expiry_slot: 100,
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
                    size_q: signed_q(10 * POS_SCALE),
                    exec_price: 1,
                    fee_bps: 0,
                },
                true,
            )
            .expect("opening trade mints the IM lien");
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut short,
                &mut long,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(10 * POS_SCALE),
                    exec_price: 1,
                    fee_bps: 0,
                },
                true,
            )
            .expect("closing trade");
    }
    (header, markets, long_header)
}

/// The Live lien release must leave the account with a CURRENT certificate.
///
/// `release_account_source_credit_liens_if_unneeded_not_atomic` advances the market
/// `risk_epoch` (it recomputes the source-credit domain), which retires every
/// outstanding certificate including the one the release derived for itself. It
/// previously also cleared `health_cert.valid` on exit. Either alone is enough to
/// make `ensure_favorable_action_current_certificate` reject the account, so the
/// conversion that `convert_released_pnl_to_capital_not_atomic` performs
/// immediately after the release returned `Stale` — and because the instruction
/// returned an error, the runtime discarded the release along with it, so the lien
/// could never clear in `Live` at all.
///
/// Regression for the durable freeze reported in #148 (a recurrence of #137).
#[test]
fn live_lien_release_leaves_a_current_certificate_so_conversion_succeeds() {
    let (mut header, mut markets, mut acct) = live_stale_im_lien_fixture();

    let lien = acct.source_domains[0].source_lien_effective_reserved.get();
    assert_ne!(
        lien, 0,
        "fixture must carry the stale IM lien the release targets"
    );

    // Model the runtime: an instruction that returns Err commits nothing, so a
    // failing conversion must not be credited with the release it performed.
    let mut outcomes = Vec::new();
    for _ in 0..4 {
        {
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut a = PortfolioV16ViewMut::new(&mut acct);
            let _ = market.full_account_refresh_not_atomic(&mut a);
        }
        let (h, m, s) = (header, markets.clone(), acct);
        let res = {
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut a = PortfolioV16ViewMut::new(&mut acct);
            market.convert_released_pnl_to_capital_not_atomic(&mut a)
        };
        if res.is_err() {
            header = h;
            markets = m;
            acct = s;
        }
        outcomes.push(res);
    }

    assert_eq!(
        outcomes[0],
        Ok(100),
        "the first conversion must succeed; it previously returned Err(Stale) because \
         the release retired the certificate the preflight then demanded"
    );
    assert!(
        outcomes[1..].iter().all(|r| *r == Ok(0)),
        "later conversions are no-ops once the claim is realized; got {outcomes:?}"
    );
    assert_eq!(
        acct.source_domains[0].source_lien_effective_reserved.get(),
        0,
        "the released lien must be committed, not rolled back with an error"
    );
}

/// The release is `pub` and reachable on its own, so it must leave a usable
/// certificate regardless of how it is reached — not only when it happens to be
/// called from inside `convert_released_pnl_to_capital_not_atomic`.
///
/// This distinguishes certifying inside the release from certifying at that one
/// call site: the call site is guarded by `valid_source_lien_effective_reserved_sum
/// != 0`, which is already false after a direct release, so a call-site-only fix
/// leaves this path returning `Stale`.
#[test]
fn direct_live_lien_release_leaves_a_certificate_the_conversion_can_use() {
    let (mut header, mut markets, mut acct) = live_stale_im_lien_fixture();

    let released = {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut a = PortfolioV16ViewMut::new(&mut acct);
        market.release_account_source_credit_liens_if_unneeded_not_atomic(&mut a)
    };
    assert_eq!(released, Ok(10), "the release itself succeeds");
    assert!(
        acct.health_cert.try_to_runtime().unwrap().valid,
        "the release must leave a valid certificate, as every other self-contained \
         mutating operation in this engine does"
    );

    let converted = {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut a = PortfolioV16ViewMut::new(&mut acct);
        market.convert_released_pnl_to_capital_not_atomic(&mut a)
    };
    assert_eq!(
        converted,
        Ok(100),
        "converting straight after a direct release must not be blocked by the \
         certificate that release retired"
    );
}

/// Nothing in the suite pinned the risk-epoch term of the certificate-currency
/// gate: dropping it from the kernel left every test green. This pins it at the
/// production entry point, where a certificate that is current in every other
/// respect but was taken under an older risk epoch must be refused as Stale.
#[test]
fn v16_favorable_action_rejects_a_certificate_stale_on_the_risk_epoch_alone() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 91);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 1_000).unwrap();
        market
            .full_account_refresh_not_atomic(&mut account)
            .unwrap();
    }
    let mut cert = account_header.health_cert.try_to_runtime().unwrap();
    assert!(
        cert.valid,
        "the fixture must start from a valid certificate"
    );
    assert_eq!(cert.cert_risk_epoch, header.risk_epoch.get());
    cert.cert_risk_epoch = cert.cert_risk_epoch.wrapping_add(1);
    account_header.health_cert = HealthCertV16Account::from_runtime(&cert);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    assert_eq!(
        market.convert_released_pnl_to_capital_not_atomic(&mut account),
        Err(V16Error::Stale)
    );
}

#[test]
fn v16_auto_crank_classifies_fresh_account_stale_then_refreshes_to_clean() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 21);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 1_000).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    // A fresh (uncertified) account in a Live market is classified stale ONLY.
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(summary.stale, "fresh uncertified account must be stale");
    assert!(
        !summary.b_stale
            && !summary.pending_close
            && !summary.expired_close
            && !summary.liquidatable
            && !summary.source_liens_releasable
            && !summary.recovery_eligible
            && !summary.resolved_winner,
        "no other actionable class on a fresh empty account"
    );

    let obs = [AutoCrankObservationV16 {
        asset_index: 0,
        effective_price: 100,
        funding_rate_e9: 0,
    }];
    let work = AutoCrankWorkV16 {
        now_slot: 5,
        observations: &obs,
        resolved_close_fee_rate_per_slot: 0,
    };

    // The engine selects RefreshAccount (engine-chosen asset) and dispatches it;
    // the account becomes current (real liveness progress, no caller-chosen action).
    let r = market
        .permissionless_auto_crank_not_atomic(&mut account, work)
        .unwrap();
    assert!(matches!(
        r.selected,
        AutoCrankPlanV16::RefreshAccount { .. }
    ));
    assert_eq!(
        r.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
    );

    // Now certified & clean -> not actionable -> NoAction (terminates).
    let summary2 = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        !summary2.is_actionable(),
        "a refreshed, clean account is not actionable"
    );
    let r2 = market
        .permissionless_auto_crank_not_atomic(&mut account, work)
        .unwrap();
    assert_eq!(r2.selected, AutoCrankPlanV16::NoAction);
    assert_eq!(r2.outcome, AutoCrankOutcomeV16::NoAction);

    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_releases_current_flat_pending_obligations_on_both_sides() {
    for side in [SideV16::Long, SideV16::Short] {
        let (mut header, mut markets) = market_fixture(1, 100);
        let mut account_header = account_fixture(1, 22);
        let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
        match side {
            SideV16::Long => {
                asset.stored_pos_count_long = 1;
                asset.pending_obligation_count_long = 1;
                asset.loss_weight_sum_long = POS_SCALE;
            }
            SideV16::Short => {
                asset.stored_pos_count_short = 1;
                asset.pending_obligation_count_short = 1;
                asset.loss_weight_sum_short = POS_SCALE;
            }
        }
        markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
        header.resolved_payout_blocker_count = V16PodU64::new(1);
        header.materialized_portfolio_count = V16PodU64::new(1);

        account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
            active: true,
            asset_index: 0,
            market_id: asset.market_id,
            side,
            basis_pos_q: 0,
            a_basis: ADL_ONE,
            k_snap: match side {
                SideV16::Long => asset.k_long,
                SideV16::Short => asset.k_short,
            },
            f_snap: match side {
                SideV16::Long => asset.f_long_num,
                SideV16::Short => asset.f_short_num,
            },
            kf_epoch_snap: 0,
            epoch_snap: match side {
                SideV16::Long => asset.epoch_long,
                SideV16::Short => asset.epoch_short,
            },
            loss_weight: POS_SCALE,
            b_snap: match side {
                SideV16::Long => asset.b_long_num,
                SideV16::Short => asset.b_short_num,
            },
            b_rem: 0,
            b_epoch_snap: match side {
                SideV16::Long => asset.epoch_long,
                SideV16::Short => asset.epoch_short,
            },
            b_stale: false,
            stale: false,
        });
        account_header.active_bitmap[0] = V16PodU64::new(1);
        account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
            cert_oracle_epoch: header.oracle_epoch.get(),
            cert_funding_epoch: header.funding_epoch.get(),
            cert_risk_epoch: header.risk_epoch.get(),
            cert_asset_set_epoch: header.asset_set_epoch.get(),
            active_bitmap_at_cert: account_header.active_bitmap.map(V16PodU64::get),
            valid: true,
            ..HealthCertV16::default()
        });

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.validate_shape().unwrap();
        account.validate_with_market(&market.as_view()).unwrap();
        assert!(
            market
                .build_actionable_summary(&account.as_view())
                .unwrap()
                .stale
        );
        let current_slot = market.header.current_slot.get();

        let result = market
            .permissionless_auto_crank_not_atomic(
                &mut account,
                AutoCrankWorkV16 {
                    now_slot: current_slot,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .unwrap();
        assert_eq!(
            result.selected,
            AutoCrankPlanV16::RefreshAccount {
                asset_index: Some(0)
            }
        );
        assert_eq!(
            result.outcome,
            AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
        );
        assert_eq!(account.header.active_bitmap[0].get(), 0);
        let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
        assert_eq!(after.stored_pos_count_long, 0);
        assert_eq!(after.stored_pos_count_short, 0);
        assert_eq!(after.pending_obligation_count_long, 0);
        assert_eq!(after.pending_obligation_count_short, 0);
        assert_eq!(after.loss_weight_sum_long, 0);
        assert_eq!(after.loss_weight_sum_short, 0);
        assert_eq!(market.header.resolved_payout_blocker_count.get(), 0);
        market.validate_shape().unwrap();
        account.validate_with_market(&market.as_view()).unwrap();
        market
            .deregister_empty_materialized_portfolio_not_atomic(&account.as_view())
            .unwrap();
        assert_eq!(market.header.materialized_portfolio_count.get(), 0);
    }
}

// A Recovery obligation may only be released once the OPPOSITE side holds no
// real (non-obligation) positions -- otherwise the loss weight it carries is
// still needed to absorb that side's settlement. 6d70fdbe established this rule;
// this pins the auto-crank selector against it, which is the one place the rule
// was missing when the released-obligation signal was introduced.
#[test]
fn v16_auto_crank_retains_released_obligation_while_the_opposite_side_is_live() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 26);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.lifecycle = AssetLifecycleV16::Recovery;
    // The obligation is on the short side; the LONG side still holds one real
    // position (stored 1, pending 0), so release must wait.
    asset.stored_pos_count_short = 1;
    asset.pending_obligation_count_short = 1;
    asset.loss_weight_sum_short = POS_SCALE;
    asset.stored_pos_count_long = 1;
    asset.pending_obligation_count_long = 0;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.oi_eff_long_q = POS_SCALE;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(1);
    header.materialized_portfolio_count = V16PodU64::new(1);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Short,
        basis_pos_q: 0,
        a_basis: ADL_ONE,
        k_snap: asset.k_short,
        f_snap: asset.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_short,
        loss_weight: POS_SCALE,
        b_snap: asset.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_short,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);
    account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        cert_oracle_epoch: header.oracle_epoch.get(),
        cert_funding_epoch: header.funding_epoch.get(),
        cert_risk_epoch: header.risk_epoch.get(),
        cert_asset_set_epoch: header.asset_set_epoch.get(),
        active_bitmap_at_cert: account_header.active_bitmap.map(V16PodU64::get),
        valid: true,
        ..HealthCertV16::default()
    });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();

    // The selector must NOT offer this obligation, so the account is not stale on
    // its account: nothing here is releasable yet.
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        !summary.stale,
        "an obligation whose opposite side is still live is not releasable: {summary:?}"
    );

    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: market.header.current_slot.get(),
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .unwrap();
    assert_eq!(result.selected, AutoCrankPlanV16::NoAction);
    // The leg, its loss weight and every counter it holds open must survive.
    assert_eq!(account.header.active_bitmap[0].get(), 1);
    let after = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(after.pending_obligation_count_short, 1);
    assert_eq!(after.loss_weight_sum_short, POS_SCALE);
    assert_eq!(market.header.resolved_payout_blocker_count.get(), 1);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// upstream e1deaf88: a legacy zero-effective-OI residue must stay crankable.
#[test]
fn v16_auto_crank_migrates_legacy_normal_adl_residue_into_reset_cleanup() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 25);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = 0;
    asset.oi_eff_short_q = 0;
    asset.a_long = ADL_ONE / 2;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(1);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 1,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("a legacy zero-effective-OI residue must remain crankable after upgrade");
    assert_eq!(
        result.selected,
        AutoCrankPlanV16::RefreshAccount {
            asset_index: Some(0)
        }
    );
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    assert!(!account.header.legs[0].try_to_runtime().unwrap().active);
    let reset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reset.mode_long, SideModeV16::ResetPending);
    assert_eq!(reset.stored_pos_count_long, 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// FORK CONTROL for 9ffc4749's selector hunk. upstream e1deaf88's test above runs on
// an account with no valid health certificate, so the classifier selects a refresh
// regardless and the refresh path migrates the residue: deleting the
// `|| leg_has_exhausted_effective_oi` term leaves it green. The term only matters
// when the certificate is CURRENT -- then nothing else marks the account stale, and
// without the term a legacy zero-effective-OI residue classifies as NoAction and is
// never migrated. Same fixture as e1deaf88, plus a current certificate.
#[test]
fn v16_auto_crank_migrates_exhausted_residue_behind_a_current_certificate() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 26);
    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = 0;
    asset.oi_eff_short_q = 0;
    asset.a_long = ADL_ONE / 2;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(1);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.deposit_not_atomic(&mut account, 1_000).unwrap();
    account.header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        cert_oracle_epoch: market.header.oracle_epoch.get(),
        cert_funding_epoch: market.header.funding_epoch.get(),
        cert_risk_epoch: market.header.risk_epoch.get(),
        cert_asset_set_epoch: market.header.asset_set_epoch.get(),
        active_bitmap_at_cert: account.header.active_bitmap.map(V16PodU64::get),
        valid: true,
        ..HealthCertV16::default()
    });
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.stale,
        "an exhausted legacy residue must be actionable even behind a current certificate: {summary:?}"
    );
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: market.header.current_slot.get(),
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the residue must be crankable behind a current certificate");
    assert_eq!(
        result.selected,
        AutoCrankPlanV16::RefreshAccount {
            asset_index: Some(0)
        }
    );
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    let reset = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(reset.mode_long, SideModeV16::ResetPending);
    assert_eq!(reset.stored_pos_count_long, 0);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// Fork control for upstream 9ffc4749's selector hunk: liquidation eligibility
// reads MATCHED effective OI. This account's short leg sits on a side that still
// holds effective OI, but the long side is an exhausted residue (zero effective
// OI while a stored position remains), so a close has nothing to match against.
// A side-local reading dispatches a liquidation that cannot progress; the matched
// reading classifies no liquidation work, so the crank is a clean NoAction.
#[test]
fn v16_auto_crank_does_not_liquidate_against_unmatched_effective_oi() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 23);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.slot_last = 10;
    asset.oi_eff_long_q = 0;
    asset.oi_eff_short_q = POS_SCALE;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.loss_weight_sum_short = POS_SCALE;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Short,
        basis_pos_q: -(POS_SCALE as i128),
        a_basis: ADL_ONE,
        k_snap: asset.k_short,
        f_snap: asset.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_short,
        loss_weight: POS_SCALE,
        b_snap: asset.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_short,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);
    account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        certified_equity: 0,
        certified_initial_req: 2,
        certified_maintenance_req: 2,
        certified_liq_deficit: 2,
        certified_worst_case_loss: 200,
        cert_oracle_epoch: header.oracle_epoch.get(),
        cert_funding_epoch: header.funding_epoch.get(),
        cert_risk_epoch: header.risk_epoch.get(),
        cert_asset_set_epoch: header.asset_set_epoch.get(),
        active_bitmap_at_cert: [1],
        valid: true,
    });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        !summary.liquidatable,
        "a leg with no opposite effective OI has nothing to liquidate against: {summary:?}"
    );
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the crank must not dispatch a liquidation that cannot progress");
    assert_eq!(result.selected, AutoCrankPlanV16::NoAction);
    assert!(account.header.legs[0].try_to_runtime().unwrap().active);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_drives_stale_underwater_account_to_derisked_fixed_point() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 13);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(9);
    header.loss_stale_active = 1;
    header.vault = V16PodU128::new(50);
    header.insurance = V16PodU128::new(50);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
    asset0.slot_last = 10;
    asset0.oi_eff_long_q = 2 * POS_SCALE;
    asset0.oi_eff_short_q = 2 * POS_SCALE;
    asset0.loss_weight_sum_long = 2 * POS_SCALE;
    asset0.loss_weight_sum_short = 2 * POS_SCALE;
    asset0.stored_pos_count_long = 2;
    asset0.stored_pos_count_short = 2;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);
    let mut asset1 = markets[1].engine.asset.try_to_runtime().unwrap();
    asset1.slot_last = 9;
    asset1.oi_eff_long_q = POS_SCALE;
    asset1.oi_eff_short_q = POS_SCALE;
    asset1.loss_weight_sum_long = POS_SCALE;
    asset1.loss_weight_sum_short = POS_SCALE;
    asset1.stored_pos_count_long = 1;
    asset1.stored_pos_count_short = 1;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&asset1);
    header.resolved_payout_blocker_count = V16PodU64::new(6);

    account_header.pnl = V16PodI128::new(-5);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset0.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset0.k_long,
        f_snap: asset0.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset0.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset0.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset0.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    let obs = [AutoCrankObservationV16 {
        asset_index: 0,
        effective_price: 100,
        funding_rate_e9: 0,
    }];
    let work = AutoCrankWorkV16 {
        now_slot: 10,
        observations: &obs,
        resolved_close_fee_rate_per_slot: 0,
    };

    // Drive the engine auto-crank to a fixed point. It MUST converge (no-DoS)
    // within a bounded number of steps, self-selecting the asset each step.
    let mut plans = Vec::new();
    let mut saw_refresh = false;
    let mut saw_liquidate = false;
    let mut steps = 0;
    loop {
        let summary = market.build_actionable_summary(&account.as_view()).unwrap();
        let r = match market.permissionless_auto_crank_not_atomic(&mut account, work) {
            Ok(r) => r,
            Err(e) => panic!(
                "step {steps} dispatch err {e:?}; summary={summary:?}; plans={plans:?}; bitmap={}",
                account.header.active_bitmap[0].get()
            ),
        };
        match r.selected {
            AutoCrankPlanV16::NoAction => break,
            AutoCrankPlanV16::RefreshAccount { .. } => saw_refresh = true,
            AutoCrankPlanV16::Liquidate { .. } => saw_liquidate = true,
            _ => {}
        }
        plans.push(r.selected);
        steps += 1;
        assert!(
            steps < 12,
            "engine auto-crank must converge (no-DoS); selected so far: {:?}",
            plans
        );
    }

    // The engine escalated: it refreshed the stale account, then liquidated
    // the underwater position — and reached a non-actionable fixed point.
    assert!(
        saw_refresh,
        "must refresh the uncertified account: {:?}",
        plans
    );
    assert!(
        saw_liquidate,
        "must liquidate the underwater position: {:?}",
        plans
    );
    assert_eq!(
        account.header.active_bitmap[0].get(),
        0,
        "position must be liquidated at the fixed point"
    );

    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_trade_final_leg_residual_routes_through_close_without_forcing_market_recovery() {
    const SIZE_Q: u128 = 10 * POS_SCALE;
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 61);
    let mut short_header = account_fixture(1, 62);

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

    let pending = short.header.close_progress.try_to_runtime().unwrap();
    assert!(active_bitmap_is_empty(
        short.header.active_bitmap.map(V16PodU64::get)
    ));
    assert_eq!(short.header.capital.get(), 0);
    assert_eq!(short.header.pnl.get(), -250);
    assert!(pending.active && !pending.finalized && pending.residual_remaining != 0);
    assert_eq!(pending.asset_index, 0);
    assert_eq!(pending.domain_side, SideV16::Long);
    assert_eq!(pending.residual_remaining, 250);
    assert!(
        market
            .build_actionable_summary(&short.as_view())
            .unwrap()
            .pending_close
    );

    let work = AutoCrankWorkV16 {
        now_slot: 11,
        observations: &[],
        resolved_close_fee_rate_per_slot: 0,
    };
    let booked = market
        .permissionless_auto_crank_not_atomic(&mut short, work)
        .expect("pending close must have a committed-state continuation");
    assert_eq!(booked.selected, AutoCrankPlanV16::AdvanceClose);
    assert!(matches!(
        booked.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::ResidualBooked(_))
    ));
    assert_eq!(short.header.pnl.get(), 0);
    assert_eq!(market.header.negative_pnl_account_count.get(), 0);
    let finalized = short.header.close_progress.try_to_runtime().unwrap();
    assert!(finalized.active && finalized.finalized && finalized.residual_remaining == 0);

    let observations = [AutoCrankObservationV16 {
        asset_index: 0,
        effective_price: 150,
        funding_rate_e9: 0,
    }];
    let normalized = market
        .permissionless_auto_crank_not_atomic(
            &mut short,
            AutoCrankWorkV16 {
                now_slot: work.now_slot,
                observations: &observations,
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the completed close account must normalize its stale certificate");
    assert_eq!(
        normalized.selected,
        AutoCrankPlanV16::RefreshAccount { asset_index: None }
    );

    let no_forced_recovery = market
        .permissionless_auto_crank_not_atomic(&mut short, work)
        .expect("a completed account close is not market-wide recovery authority");
    assert_eq!(
        no_forced_recovery.selected,
        AutoCrankPlanV16::NoAction,
        "completed residual work must not terminate unrelated market activity"
    );
    assert_eq!(market.header.mode, 0);

    market
        .resolve_market_not_atomic(work.now_slot)
        .expect("an explicit market-level transition can start terminal settlement");
    assert_eq!(market.header.mode, 1);

    let loser_close = market
        .close_resolved_account_not_atomic(&mut short, 0)
        .expect("the flat bankrupt account must close in Resolved mode");
    assert!(matches!(
        loser_close,
        percolator::ResolvedCloseOutcomeV16::Closed { payout: 0 }
    ));
    let mut winner_closed = false;
    let mut last_winner_close = None;
    for _ in 0..8 {
        let close = market
            .close_resolved_account_not_atomic(&mut long, 0)
            .expect("the loss-side obligation must make bounded resolved progress");
        last_winner_close = Some(close);
        if matches!(close, percolator::ResolvedCloseOutcomeV16::Closed { .. }) {
            winner_closed = true;
            break;
        }
    }
    assert!(
        winner_closed,
        "the winner must reach terminal payout finitely: last={last_winner_close:?}, \
         blockers={}, b_stale={}, stale={}, pnl={}, capital={}, bitmap={:?}, asset={:?}",
        market.header.resolved_payout_blocker_count.get(),
        long.header.b_stale_state,
        long.header.stale_state,
        long.header.pnl.get(),
        long.header.capital.get(),
        long.header.active_bitmap,
        market.markets[0].engine.asset.try_to_runtime().unwrap(),
    );
    assert!(active_bitmap_is_empty(
        long.header.active_bitmap.map(V16PodU64::get)
    ));
    assert_eq!(long.header.capital.get(), 0);
    assert_eq!(long.header.pnl.get(), 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_batch_trade_starts_terminal_residual_only_at_final_fill() {
    const HALF_Q: u128 = 5 * POS_SCALE;
    let (mut header, mut markets) = market_fixture(2, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(2, 63);
    let mut short_header = account_fixture(2, 64);

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
                size_q: signed_q(2 * HALF_Q),
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

    let outcome = market
        .execute_batch_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            &[
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: -signed_q(HALF_Q),
                    exec_price: 150,
                    fee_bps: 0,
                },
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: -signed_q(HALF_Q),
                    exec_price: 150,
                    fee_bps: 0,
                },
            ],
            true,
        )
        .expect("an intermediate partial close must not lock the final fill");

    assert_eq!(outcome.fill_count, 2);
    let pending = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(pending.close_id, 1);
    assert_eq!(pending.gross_loss_at_close_start, 250);
    assert_eq!(pending.residual_remaining, 250);
    assert!(active_bitmap_is_empty(
        short.header.active_bitmap.map(V16PodU64::get)
    ));
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_liquidates_current_account_without_observation() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 14);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);
    header.vault = V16PodU128::new(50);
    header.insurance = V16PodU128::new(50);
    header.negative_pnl_account_count = V16PodU64::new(1);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.slot_last = 10;
    asset.oi_eff_long_q = 2 * POS_SCALE;
    asset.oi_eff_short_q = 2 * POS_SCALE;
    asset.loss_weight_sum_long = 2 * POS_SCALE;
    asset.loss_weight_sum_short = 2 * POS_SCALE;
    asset.stored_pos_count_long = 2;
    asset.stored_pos_count_short = 2;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(4);

    account_header.pnl = V16PodI128::new(-5);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market
        .full_account_refresh_not_atomic(&mut account)
        .expect("setup must produce a current liquidation cert");
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.liquidatable && !summary.stale && !summary.b_stale,
        "setup must be current and liquidatable: {summary:?}"
    );

    let work = AutoCrankWorkV16 {
        now_slot: 10,
        observations: &[],
        resolved_close_fee_rate_per_slot: 0,
    };
    let result = market
        .permissionless_auto_crank_not_atomic(&mut account, work)
        .expect("current liquidation must not require a fresh observation");

    assert_eq!(
        result.selected,
        AutoCrankPlanV16::Liquidate { asset_index: 0 }
    );
    assert!(matches!(
        result.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
    ));
    assert_eq!(
        account.header.active_bitmap[0].get(),
        0,
        "liquidation must close the selected position"
    );
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// A cross-margin bankruptcy whose uncovered loss cannot be booked in one bounded
// step has exactly one terminal: Recovery. The liquidation discovers that itself,
// declares Recovery and returns RecoveryRequired -- and if the public crank
// propagates that error, SVM rolls the declaration back and the account never
// moves. The crank must report the COMMITTED declaration as progress, and the
// next call must then finalize Recovery into Resolved so terminal close is
// reachable. Value must not move at either step.
#[test]
fn v16_auto_crank_commits_recovery_for_uncovered_cross_margin_liquidation() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 15);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);
    header.vault = V16PodU128::new(50);
    header.insurance = V16PodU128::new(50);
    header.negative_pnl_account_count = V16PodU64::new(1);

    for (asset_index, market_slot) in markets.iter_mut().enumerate() {
        let mut asset = market_slot.engine.asset.try_to_runtime().unwrap();
        asset.slot_last = 10;
        asset.oi_eff_long_q = 2 * POS_SCALE;
        asset.oi_eff_short_q = 2 * POS_SCALE;
        asset.loss_weight_sum_long = 2 * POS_SCALE;
        asset.loss_weight_sum_short = 2 * POS_SCALE;
        asset.stored_pos_count_long = 2;
        asset.stored_pos_count_short = 2;
        market_slot.engine.asset = AssetStateV16Account::from_runtime(&asset);
        account_header.legs[asset_index] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
            active: true,
            asset_index: asset_index as u32,
            market_id: asset.market_id,
            side: SideV16::Long,
            basis_pos_q: POS_SCALE as i128,
            a_basis: ADL_ONE,
            k_snap: asset.k_long,
            f_snap: asset.f_long_num,
            kf_epoch_snap: 0,
            epoch_snap: asset.epoch_long,
            loss_weight: POS_SCALE,
            b_snap: asset.b_long_num,
            b_rem: 0,
            b_epoch_snap: asset.epoch_long,
            b_stale: false,
            stale: false,
        });
    }
    header.resolved_payout_blocker_count = V16PodU64::new(8);
    account_header.active_bitmap[0] = V16PodU64::new(0b11);
    account_header.pnl = V16PodI128::new(-5);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market
        .full_account_refresh_not_atomic(&mut account)
        .expect("setup must produce a current cross-margin liquidation cert");
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    // The classifier does NOT pre-scan for this: the liquidation itself is what
    // discovers the terminal, which is the whole point of doing it this way.
    assert!(summary.liquidatable && !summary.recovery_eligible);

    let bitmap_before = account.header.active_bitmap;
    let pnl_before = account.header.pnl;
    let capital_before = account.header.capital;
    let vault_before = market.header.vault;
    let c_tot_before = market.header.c_tot;
    let insurance_before = market.header.insurance;
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("recovery-required liquidation must be successful crank progress");

    assert_eq!(
        result.selected,
        AutoCrankPlanV16::Liquidate { asset_index: 0 }
    );
    assert_eq!(
        result.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::RecoveryDeclared(
            PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
        ))
    );
    assert_eq!(market.header.mode, 2, "market must commit Recovery mode");
    assert_eq!(account.header.active_bitmap, bitmap_before);
    assert_eq!(account.header.pnl, pnl_before);
    assert_eq!(account.header.capital, capital_before);
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.c_tot, c_tot_before);
    assert_eq!(market.header.insurance, insurance_before);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();

    let recovery_reason_before = market.header.recovery_reason;
    let finalized = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the next public crank must finalize Recovery into Resolved");
    assert_eq!(finalized.selected, AutoCrankPlanV16::FinalizeRecovery);
    assert_eq!(finalized.outcome, AutoCrankOutcomeV16::RecoveryResolved);
    assert_eq!(
        market.header.mode, 1,
        "terminal close must become reachable"
    );
    assert_eq!(market.header.recovery_reason, recovery_reason_before);
    assert_eq!(account.header.active_bitmap, bitmap_before);
    assert_eq!(account.header.pnl, pnl_before);
    assert_eq!(account.header.capital, capital_before);
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.c_tot, c_tot_before);
    assert_eq!(market.header.insurance, insurance_before);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// A market in Recovery is a DEAD END for the single public crank unless the
// engine offers the Recovery-to-Resolved step itself: permissionless_crank_not_atomic
// rejects every non-Recover action outside Live, so terminal account close stays
// unreachable and the account is stuck. The transition must be value-neutral and
// must preserve the declared recovery reason so the record of WHY the market
// recovered survives resolution.
#[test]
fn v16_auto_crank_finalizes_recovery_into_resolved_without_moving_value() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 205);
    header.current_slot = V16PodU64::new(10);
    header.mode = 2;
    header.recovery_reason = V16OptionalRecoveryReasonAccount::from_runtime(Some(
        PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
    ));

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let vault_before = market.header.vault;
    let c_tot_before = market.header.c_tot;
    let insurance_before = market.header.insurance;
    let recovery_reason_before = market.header.recovery_reason;
    let pnl_before = account.header.pnl;
    let capital_before = account.header.capital;

    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("a recovered market must still have a bounded public step");

    assert_eq!(result.selected, AutoCrankPlanV16::FinalizeRecovery);
    assert_eq!(result.outcome, AutoCrankOutcomeV16::RecoveryResolved);
    assert_eq!(
        market.header.mode, 1,
        "terminal close must become reachable"
    );
    assert_eq!(market.header.recovery_reason, recovery_reason_before);
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.c_tot, c_tot_before);
    assert_eq!(market.header.insurance, insurance_before);
    assert_eq!(account.header.pnl, pnl_before);
    assert_eq!(account.header.capital, capital_before);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// Clock-driven work must be classifiable at the AUTHENTICATED execution slot,
// not only at the committed market slot. Advancing the committed slot needs an
// oracle observation; if expiry were read from it, a close that has genuinely
// lapsed would stay invisible to the crank until somebody happened to supply a
// price -- and a keeper holding no observation is exactly the caller this crank
// exists for. The reverse direction must fail closed: a caller cannot backdate
// now_slot to classify against a clock the market has already moved past.
//
// SECOND CONTROL: upstream also pins this with
// v16_auto_crank_classifies_lapsed_source_backing_with_current_certificate, which
// drives the property through first_lapsed_source_backing_for_account_at_slot.
// That test landed with 0e773c77 and was sharpened by 867fbdc9 into its
// !stale-at-committed / stale-at-authenticated form; both are on this branch. This
// one keeps the property pinned through the independent clock-driven signal,
// expired_close, and additionally covers the backdated-slot refusal that the other
// one does not.
#[test]
fn v16_auto_crank_classifies_close_expiry_at_the_authenticated_slot() {
    use percolator::{CloseProgressLedgerV16, CloseProgressLedgerV16Account};

    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 42);
    header.current_slot = V16PodU64::new(2);

    let market_id = markets[0].engine.asset.try_to_runtime().unwrap().market_id;
    account_header.close_progress =
        CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
            active: true,
            finalized: false,
            canceled: false,
            close_id: 1,
            asset_index: 0,
            market_id,
            domain_side: SideV16::Short,
            gross_loss_at_close_start: 10,
            drift_reference_slot: 1,
            // Not expired at the COMMITTED slot 2, expired at slot 10.
            max_close_slot: 2,
            support_consumed: 0,
            junior_face_burned: 0,
            insurance_spent: 0,
            b_loss_booked: 0,
            explicit_loss_assigned: 0,
            quantity_adl_applied_q: 0,
            drift_consumed: 0,
            residual_remaining: 10,
        });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    // At the committed slot the close has not lapsed.
    assert!(
        !market
            .build_actionable_summary(&account.as_view())
            .unwrap()
            .expired_close
    );
    // At an authenticated later slot it has, with no observation supplied and no
    // change to the committed market clock.
    assert!(
        market
            .build_actionable_summary_at_slot(&account.as_view(), 10)
            .unwrap()
            .expired_close
    );
    assert_eq!(
        market.header.current_slot.get(),
        2,
        "classification is pure"
    );

    // A backdated slot is refused rather than silently classified.
    assert_eq!(
        market.build_actionable_summary_at_slot(&account.as_view(), 1),
        Err(V16Error::InvalidConfig)
    );

    // And the public crank dispatches on the authenticated slot.
    let r = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("an expired close must be actionable without an oracle hint");
    assert_eq!(
        r.selected,
        AutoCrankPlanV16::DeclareRecovery {
            reason: PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress
        }
    );
    assert_eq!(market.header.mode, 2);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_declares_recovery_for_expired_live_close() {
    use percolator::{CloseProgressLedgerV16, CloseProgressLedgerV16Account};

    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 41);
    header.current_slot = V16PodU64::new(10);

    // An active, outstanding (residual>0), EXPIRED close ledger on asset 0.
    let market_id = markets[0].engine.asset.try_to_runtime().unwrap().market_id;
    account_header.close_progress =
        CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
            active: true,
            finalized: false,
            canceled: false,
            close_id: 1,
            asset_index: 0,
            market_id,
            domain_side: SideV16::Short,
            gross_loss_at_close_start: 10,
            drift_reference_slot: 1,
            max_close_slot: 2, // < current_slot 10 => expired
            support_consumed: 0,
            junior_face_burned: 0,
            insurance_spent: 0,
            b_loss_booked: 0,
            explicit_loss_assigned: 0,
            quantity_adl_applied_q: 0,
            drift_consumed: 0,
            residual_remaining: 10,
        });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.expired_close,
        "outstanding expired close ledger must classify expired_close: {summary:?}"
    );
    assert!(!summary.recovery_eligible && !summary.resolved_winner);

    // DeclareRecovery needs no observation (empty work).
    let work = AutoCrankWorkV16 {
        now_slot: 10,
        observations: &[],
        resolved_close_fee_rate_per_slot: 0,
    };
    let vault_before = market.header.vault;
    let r = market
        .permissionless_auto_crank_not_atomic(&mut account, work)
        .unwrap();
    assert_eq!(
        r.selected,
        AutoCrankPlanV16::DeclareRecovery {
            reason: PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress
        }
    );
    assert_eq!(
        r.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::RecoveryDeclared(
            PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress
        ))
    );
    // recovery declaration moves no value.
    assert_eq!(market.header.vault, vault_before);
    market.validate_shape().unwrap();
}

#[test]
fn v16_auto_crank_classifies_payout_ready_resolved_winner_without_snapshot() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 42);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.resolve_market_not_atomic(1).unwrap();
    }
    header.vault = V16PodU128::new(50);
    // Positive PnL, all blocking counts clear (resolved_positive_payout_ready);
    // payout_snapshot_captured stays 0 — the property under test.
    account_header.pnl = V16PodI128::new(5);

    let market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let account = PortfolioV16ViewMut::new(&mut account_header);
    assert_eq!(
        market.header.payout_snapshot_captured, 0,
        "snapshot intentionally NOT captured"
    );

    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.resolved_winner,
        "a payout-ready resolved winner must be resolved_winner even before the \
         snapshot is captured (no snapshot gate -> no first-winner deadlock): {summary:?}"
    );
    assert!(!summary.recovery_eligible && !summary.stale && !summary.liquidatable);
}

#[test]
fn v16_auto_crank_normalizes_empty_resolved_account_fee_anchor() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 43);
    account_header.last_fee_slot = V16PodU64::new(0);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.resolve_market_not_atomic(1).unwrap();
    }

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    assert!(active_bitmap_is_empty(
        account.header.active_bitmap.map(V16PodU64::get)
    ));
    assert_eq!(account.header.capital.get(), 0);
    assert_eq!(account.header.pnl.get(), 0);
    assert_eq!(account.header.reserved_pnl.get(), 0);
    assert_eq!(account.header.fee_credits.get(), 0);
    assert_eq!(account.header.cancel_deposit_escrow.get(), 0);
    assert_eq!(account.header.last_fee_slot.get(), 0);
    assert_eq!(market.header.resolved_slot.get(), 1);

    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.resolved_winner,
        "an empty account with a stale resolved fee anchor still has one bounded normalization step"
    );
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 1,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .unwrap();
    assert_eq!(result.selected, AutoCrankPlanV16::CloseResolved);
    assert_eq!(
        result.outcome,
        AutoCrankOutcomeV16::ResolvedClose(ResolvedCloseOutcomeV16::Closed { payout: 0 })
    );
    assert_eq!(account.header.last_fee_slot.get(), 1);
    assert!(
        !market
            .build_actionable_summary(&account.as_view())
            .unwrap()
            .is_actionable(),
        "the one-step fee-anchor normalization must reach a fixed point"
    );
}

#[test]
fn v16_auto_crank_settles_b_stale_leg() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 51);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);
    let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
    asset0.slot_last = 10;
    asset0.oi_eff_long_q = POS_SCALE;
    asset0.oi_eff_short_q = POS_SCALE;
    asset0.loss_weight_sum_long = POS_SCALE;
    asset0.loss_weight_sum_short = POS_SCALE;
    asset0.stored_pos_count_long = 1;
    asset0.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);

    // Active leg flagged b-stale, with b_snap already at the current target so the
    // settle resolves to a clean delta_b=0 clear (progress: clears the b-stale flag).
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset0.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset0.k_long,
        f_snap: asset0.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset0.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset0.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset0.epoch_long,
        b_stale: true,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.b_stale,
        "b-stale leg must classify b_stale: {summary:?}"
    );

    let work = AutoCrankWorkV16 {
        now_slot: 10,
        observations: &[],
        resolved_close_fee_rate_per_slot: 0,
    };
    let r = market
        .permissionless_auto_crank_not_atomic(&mut account, work)
        .unwrap();
    // b_stale has priority over the stale-cert refresh, so SettleBChunk is selected
    // with the engine-chosen asset (the b-stale leg's asset) and dispatched to the
    // real B-chunk settle entrypoint (AccountBChunk outcome). The rank-decreasing
    // B-advance for a genuinely drifted leg (delta_b>0) is proven at the A2 kernel.
    assert_eq!(
        r.selected,
        AutoCrankPlanV16::SettleBChunk { asset_index: 0 }
    );
    assert!(matches!(
        r.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountBChunk(_))
    ));
    market.validate_shape().unwrap();
}

#[test]
fn v16_auto_crank_settles_latent_b_delta_on_recovery_leg() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 52);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 1_000).unwrap();
    }
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.lifecycle = AssetLifecycleV16::Recovery;
    asset.slot_last = 10;
    asset.b_long_num = SOCIAL_LOSS_DEN / POS_SCALE;
    asset.oi_eff_long_q = POS_SCALE;
    asset.oi_eff_short_q = POS_SCALE;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.loss_weight_sum_short = POS_SCALE;
    asset.stored_pos_count_long = 1;
    asset.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(2);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: 0,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    account.validate_with_market(&market.as_view()).unwrap();
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(
        summary.b_stale,
        "a current B target above the leg snapshot is actionable even when the cached stale bit is false: {summary:?}"
    );

    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("latent Recovery B must have a permissionless bounded continuation");
    assert_eq!(
        result.selected,
        AutoCrankPlanV16::SettleBChunk { asset_index: 0 }
    );
    assert!(matches!(
        result.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountBChunk(_))
    ));
    let settled_leg = account.header.legs[0].try_to_runtime().unwrap();
    assert_eq!(settled_leg.b_snap, asset.b_long_num);
    assert_eq!(account.header.pnl.get(), -1);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_missing_observation_is_clean_nonprogress_no_mutation() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 71);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 1_000).unwrap();
    }
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);

    // fresh account -> selector wants RefreshAccount, which needs an observation;
    // supply NONE -> clean NonProgress, no mutation.
    let summary = market.build_actionable_summary(&account.as_view()).unwrap();
    assert!(summary.stale);
    let cert_before = account.header.health_cert;
    let work = AutoCrankWorkV16 {
        now_slot: 5,
        observations: &[],
        resolved_close_fee_rate_per_slot: 0,
    };
    let r = market.permissionless_auto_crank_not_atomic(&mut account, work);
    assert_eq!(r, Err(percolator::V16Error::NonProgress));
    // no mutation (SVM would roll back anyway, but the engine did not commit).
    assert_eq!(account.header.health_cert, cert_before);
    market.validate_shape().unwrap();
}

// REALIZABILITY MATRIX — closes the no-DoS dispatch seam that hid the b-stale /
// committed-state-liquidation stall. The faithful invariant is OBSERVATION-
// INDEPENDENCE: for a plan that `auto_crank_plan_requires_caller_observation`
// reports as NOT requiring one, the single public crank must return the SAME
// outcome whether or not an observation is supplied (the observation is redundant
// — the plan is realizable from committed state). For the one form that DOES
// require one (RefreshAccount with no active asset), the empty-observation call
// cleanly stalls (NonProgress) while supplying the observation progresses. This
// both guards liveness AND ties the pure predicate to the REAL dispatch per class,
// so the predicate cannot drift from behaviour. Note: a committed-state plan may
// still return a genuine economic terminal (e.g. RecoveryRequired) — that is fine,
// because it returns the SAME terminal with or without the observation; the bug
// was an outcome that DIFFERED on the observation.
fn assert_observation_independent(
    label: &str,
    build: impl Fn() -> (
        MarketGroupV16HeaderAccount,
        Vec<Market<u64>>,
        PortfolioAccountV16Account,
    ),
    obs_asset_index: usize,
    now_slot: u64,
    expected_plan: AutoCrankPlanV16,
    expected_requires_obs: bool,
    // For a REDUNDANT-observation class: whether dispatching the plan from purely
    // committed state is expected to SUCCEED. Every class but resolved_winner does;
    // resolved_winner's committed-state dispatch reaches a legitimate economic
    // terminal (RecoveryRequired). Declaring this per class is what stops the
    // outcome-equality check below from passing vacuously when BOTH calls error:
    // upstream's form guards the selected plan behind `if let Ok(..)`, so a change
    // that turns a committed-state plan into an unconditional error slips through.
    expect_committed_dispatch_ok: bool,
) {
    // The predicate's claim must equal this class's documented observation need.
    assert_eq!(
        auto_crank_plan_requires_caller_observation(&expected_plan),
        expected_requires_obs,
        "{label}: predicate disagrees with documented observation-requirement"
    );

    let run = |observations: &[AutoCrankObservationV16]| {
        let (mut header, mut markets, mut account_header) = build();
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot,
                observations,
                resolved_close_fee_rate_per_slot: 0,
            },
        )
    };

    let r_empty = run(&[]);

    // The observation a keeper would otherwise supply: the asset's *committed*
    // price (the value the cert was already certified against) and zero funding.
    let committed_price = {
        let (_h, m, _a) = build();
        m[obs_asset_index]
            .engine
            .asset
            .try_to_runtime()
            .unwrap()
            .effective_price
    };
    let obs = [AutoCrankObservationV16 {
        asset_index: obs_asset_index,
        effective_price: committed_price,
        funding_rate_e9: 0,
    }];
    let r_obs = run(&obs);

    if expected_requires_obs {
        assert_eq!(
            r_empty,
            Err(percolator::V16Error::NonProgress),
            "{label}: a plan requiring an observation must cleanly stall without one"
        );
        assert!(
            r_obs.is_ok(),
            "{label}: must progress once the observation is supplied, got {r_obs:?}"
        );
    } else {
        // The whole bug class: outcome differing on a redundant observation.
        assert_eq!(
            r_empty, r_obs,
            "{label}: observation must not change the outcome (plan is realizable \
             from committed state)"
        );
        if expect_committed_dispatch_ok {
            assert!(
                r_empty.is_ok(),
                "{label}: a plan realizable from committed state must dispatch \
                 without an observation, got {r_empty:?}"
            );
        }
        if let Ok(res) = r_empty {
            assert_eq!(
                res.selected, expected_plan,
                "{label}: unexpected selected plan"
            );
        }
    }
}

#[test]
fn v16_auto_crank_progress_realizable_without_observation_for_every_class() {
    // --- A1 stale with no active asset: fallback refresh has no committed asset
    // to use, so it still needs a caller observation.
    assert_observation_independent(
        "stale_empty_account",
        || {
            let (mut header, mut markets) = market_fixture(1, 100);
            let mut account_header = account_fixture(1, 200);
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut account = PortfolioV16ViewMut::new(&mut account_header);
            market.deposit_not_atomic(&mut account, 1_000).unwrap();
            drop(market);
            drop(account);
            (header, markets, account_header)
        },
        0,
        5,
        AutoCrankPlanV16::RefreshAccount { asset_index: None },
        true,
        true,
    );

    // --- A1 stale with an active asset: refresh is realizable from committed
    // state. This is the no-DoS case for stale multi-asset accounts whose first
    // active asset does not have a fresh oracle observation available.
    assert_observation_independent(
        "stale_active_asset",
        || {
            let (mut header, mut markets) = market_fixture(1, 100);
            let mut account_header = account_fixture(1, 209);
            let mut counterparty_header = account_fixture(1, 210);
            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            let mut account = PortfolioV16ViewMut::new(&mut account_header);
            let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
            market.deposit_not_atomic(&mut account, 1_000).unwrap();
            market.deposit_not_atomic(&mut counterparty, 1_000).unwrap();
            open_one_lot_pair(&mut market, &mut account, &mut counterparty);
            account.header.health_cert.valid = 0;
            drop(market);
            drop(account);
            drop(counterparty);
            (header, markets, account_header)
        },
        0,
        5,
        AutoCrankPlanV16::RefreshAccount {
            asset_index: Some(0),
        },
        false,
        true,
    );

    // --- A2 b_stale: SettleBChunk ignores price -> observation REDUNDANT.
    assert_observation_independent(
        "b_stale",
        || {
            let (mut header, mut markets) = market_fixture(1, 100);
            let mut account_header = account_fixture(1, 201);
            header.current_slot = V16PodU64::new(10);
            header.slot_last = V16PodU64::new(10);
            let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
            asset0.slot_last = 10;
            asset0.oi_eff_long_q = POS_SCALE;
            asset0.oi_eff_short_q = POS_SCALE;
            asset0.loss_weight_sum_long = POS_SCALE;
            asset0.loss_weight_sum_short = POS_SCALE;
            asset0.stored_pos_count_long = 1;
            asset0.stored_pos_count_short = 1;
            markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);
            account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
                active: true,
                asset_index: 0,
                market_id: asset0.market_id,
                side: SideV16::Long,
                basis_pos_q: POS_SCALE as i128,
                a_basis: ADL_ONE,
                k_snap: asset0.k_long,
                f_snap: asset0.f_long_num,
                kf_epoch_snap: 0,
                epoch_snap: asset0.epoch_long,
                loss_weight: POS_SCALE,
                b_snap: asset0.b_long_num,
                b_rem: 0,
                b_epoch_snap: asset0.epoch_long,
                b_stale: true,
                stale: false,
            });
            account_header.active_bitmap[0] = V16PodU64::new(1);
            (header, markets, account_header)
        },
        0,
        10,
        AutoCrankPlanV16::SettleBChunk { asset_index: 0 },
        false,
        true,
    );

    // --- A3 pending_close: the immutable close ledger carries all dispatch
    // inputs, so AdvanceClose must not depend on a caller observation.
    assert_observation_independent(
        "pending_close",
        || {
            const SIZE_Q: u128 = 10 * POS_SCALE;
            let (mut header, mut markets) = market_fixture(1, 100);
            header.config.maintenance_margin_bps = V16PodU64::new(1_000);
            header.config.initial_margin_bps = V16PodU64::new(1_000);
            header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
            header.config.max_accrual_dt_slots = V16PodU64::new(1);
            header.config.min_funding_lifetime_slots = V16PodU64::new(1);
            header.config.public_b_chunk_atoms = V16PodU128::new(100);
            let mut long_header = account_fixture(1, 211);
            let mut short_header = account_fixture(1, 212);
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
                    .unwrap();
            }
            (header, markets, short_header)
        },
        0,
        11,
        AutoCrankPlanV16::AdvanceClose,
        false,
        true,
    );

    // --- A5 liquidatable: Liquidate reads the current cert -> observation REDUNDANT.
    assert_observation_independent(
        "liquidatable",
        || {
            let (mut header, mut markets) = market_fixture(1, 100);
            let mut account_header = account_fixture(1, 202);
            header.current_slot = V16PodU64::new(10);
            header.slot_last = V16PodU64::new(10);
            header.vault = V16PodU128::new(50);
            header.insurance = V16PodU128::new(50);
            header.negative_pnl_account_count = V16PodU64::new(1);
            let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
            asset.slot_last = 10;
            asset.oi_eff_long_q = 2 * POS_SCALE;
            asset.oi_eff_short_q = 2 * POS_SCALE;
            asset.loss_weight_sum_long = 2 * POS_SCALE;
            asset.loss_weight_sum_short = 2 * POS_SCALE;
            asset.stored_pos_count_long = 2;
            asset.stored_pos_count_short = 2;
            markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
            header.resolved_payout_blocker_count = V16PodU64::new(4);
            account_header.pnl = V16PodI128::new(-5);
            account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
                active: true,
                asset_index: 0,
                market_id: asset.market_id,
                side: SideV16::Long,
                basis_pos_q: POS_SCALE as i128,
                a_basis: ADL_ONE,
                k_snap: asset.k_long,
                f_snap: asset.f_long_num,
                kf_epoch_snap: 0,
                epoch_snap: asset.epoch_long,
                loss_weight: POS_SCALE,
                b_snap: asset.b_long_num,
                b_rem: 0,
                b_epoch_snap: asset.epoch_long,
                b_stale: false,
                stale: false,
            });
            account_header.active_bitmap[0] = V16PodU64::new(1);
            {
                let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
                let mut account = PortfolioV16ViewMut::new(&mut account_header);
                market
                    .full_account_refresh_not_atomic(&mut account)
                    .expect("setup must produce a current liquidation cert");
            }
            (header, markets, account_header)
        },
        0,
        10,
        AutoCrankPlanV16::Liquidate { asset_index: 0 },
        false,
        true,
    );

    // --- A6 flat source lien: release uses only the current certificate and
    // committed source ledgers, so no oracle observation may gate the exit.
    // now_slot is the fixture's OWN current_slot (1, advanced by the two trades),
    // not 0: the classifier rejects a slot regression with InvalidConfig, so
    // upstream's `0` makes both dispatches Err and its `if let Ok(..)` form passes
    // this case VACUOUSLY. This fork's expect_committed_dispatch_ok=true refuses
    // that, so the case is pinned at the slot where the release really dispatches.
    assert_observation_independent(
        "flat_source_lien",
        flat_source_credit_lien_fixture,
        0,
        1,
        AutoCrankPlanV16::ReleaseSourceLiens,
        false,
        true,
    );

    // --- A4 expired_close: DeclareRecovery needs no price -> observation REDUNDANT.
    assert_observation_independent(
        "expired_close",
        || {
            use percolator::{CloseProgressLedgerV16, CloseProgressLedgerV16Account};
            let (mut header, mut markets) = market_fixture(1, 100);
            let mut account_header = account_fixture(1, 203);
            header.current_slot = V16PodU64::new(10);
            let market_id = markets[0].engine.asset.try_to_runtime().unwrap().market_id;
            account_header.close_progress =
                CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
                    active: true,
                    finalized: false,
                    canceled: false,
                    close_id: 1,
                    asset_index: 0,
                    market_id,
                    domain_side: SideV16::Short,
                    gross_loss_at_close_start: 10,
                    drift_reference_slot: 1,
                    max_close_slot: 2,
                    support_consumed: 0,
                    junior_face_burned: 0,
                    insurance_spent: 0,
                    b_loss_booked: 0,
                    explicit_loss_assigned: 0,
                    quantity_adl_applied_q: 0,
                    drift_consumed: 0,
                    residual_remaining: 10,
                });
            (header, markets, account_header)
        },
        0,
        10,
        AutoCrankPlanV16::DeclareRecovery {
            reason: PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
        },
        false,
        true,
    );

    // --- A7 terminal Recovery: the next step is a value-neutral transition to
    // Resolved and needs no oracle observation.
    assert_observation_independent(
        "finalize_recovery",
        || {
            let (mut header, markets) = market_fixture(1, 100);
            let account_header = account_fixture(1, 205);
            header.mode = 2;
            header.recovery_reason = V16OptionalRecoveryReasonAccount::from_runtime(Some(
                PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
            ));
            (header, markets, account_header)
        },
        0,
        10,
        AutoCrankPlanV16::FinalizeRecovery,
        false,
        true,
    );

    // --- A8 resolved_winner: CloseResolved needs no price -> observation REDUNDANT.
    // (Previously only its CLASSIFICATION was tested; the empty-observation DISPATCH
    // — including a legitimate RecoveryRequired terminal — was uncovered.)
    assert_observation_independent(
        "resolved_winner",
        || {
            let (mut header, mut markets) = market_fixture(1, 100);
            let mut account_header = account_fixture(1, 204);
            {
                let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
                market.resolve_market_not_atomic(1).unwrap();
            }
            header.vault = V16PodU128::new(50);
            account_header.pnl = V16PodI128::new(5);
            (header, markets, account_header)
        },
        0,
        10,
        AutoCrankPlanV16::CloseResolved,
        false,
        false,
    );
}

#[test]
fn v16_auto_crank_skips_recovery_first_leg_for_live_refresh() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 22);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 1_000).unwrap();
    }

    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);
    let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
    asset0.lifecycle = AssetLifecycleV16::Recovery;
    asset0.slot_last = 10;
    asset0.oi_eff_long_q = POS_SCALE;
    asset0.oi_eff_short_q = POS_SCALE;
    asset0.loss_weight_sum_long = POS_SCALE;
    asset0.loss_weight_sum_short = POS_SCALE;
    asset0.stored_pos_count_long = 1;
    asset0.stored_pos_count_short = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);

    let mut asset1 = markets[1].engine.asset.try_to_runtime().unwrap();
    asset1.slot_last = 10;
    asset1.oi_eff_long_q = POS_SCALE;
    asset1.oi_eff_short_q = POS_SCALE;
    asset1.loss_weight_sum_long = POS_SCALE;
    asset1.loss_weight_sum_short = POS_SCALE;
    asset1.stored_pos_count_long = 1;
    asset1.stored_pos_count_short = 1;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&asset1);
    header.resolved_payout_blocker_count = V16PodU64::new(4);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset0.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset0.k_long,
        f_snap: asset0.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset0.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset0.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset0.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.legs[1] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 1,
        market_id: asset1.market_id,
        side: SideV16::Short,
        basis_pos_q: -(POS_SCALE as i128),
        a_basis: ADL_ONE,
        k_snap: asset1.k_short,
        f_snap: asset1.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset1.epoch_short,
        loss_weight: POS_SCALE,
        b_snap: asset1.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset1.epoch_short,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(3);

    let obs = [AutoCrankObservationV16 {
        asset_index: 1,
        effective_price: 100,
        funding_rate_e9: 0,
    }];
    let work = AutoCrankWorkV16 {
        now_slot: 10,
        observations: &obs,
        resolved_close_fee_rate_per_slot: 0,
    };
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    assert!(
        market
            .build_actionable_summary(&account.as_view())
            .unwrap()
            .stale
    );

    let result = market
        .permissionless_auto_crank_not_atomic(&mut account, work)
        .expect("a Recovery first leg must not block the live asset refresh");
    assert_eq!(
        result.selected,
        AutoCrankPlanV16::RefreshAccount {
            asset_index: Some(1),
        },
    );
    assert_eq!(
        result.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent),
    );
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_detaches_prior_reset_obligation_after_asset_recovery() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 23);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.lifecycle = AssetLifecycleV16::Recovery;
    asset.slot_last = 10;
    asset.epoch_long = 1;
    asset.mode_long = SideModeV16::ResetPending;
    asset.oi_eff_long_q = 0;
    asset.oi_eff_short_q = 0;
    asset.loss_weight_sum_long = 0;
    asset.loss_weight_sum_short = 0;
    asset.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.resolved_payout_blocker_count = V16PodU64::new(1);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_epoch_start_long,
        f_snap: asset.f_epoch_start_long_num,
        kf_epoch_snap: 0,
        epoch_snap: 0,
        loss_weight: POS_SCALE,
        b_snap: asset.b_epoch_start_long_num,
        b_rem: 0,
        b_epoch_snap: 0,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let cleanup = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("Recovery must retain permissionless prior-reset cleanup");

    assert_eq!(
        cleanup.selected,
        AutoCrankPlanV16::RefreshAccount {
            asset_index: Some(0)
        }
    );
    assert_eq!(
        cleanup.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
    );
    assert_eq!(account.header.active_bitmap[0].get(), 0);
    assert!(!account.header.legs[0].try_to_runtime().unwrap().active);
    let cleaned = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(cleaned.lifecycle, AssetLifecycleV16::Recovery);
    assert_eq!(cleaned.mode_long, SideModeV16::ResetPending);
    assert_eq!(cleaned.stored_pos_count_long, 0);
    market
        .finalize_side_reset_not_atomic(0, SideV16::Long)
        .expect("the cleaned Recovery side must finalize");
    let finalized = market.markets[0].engine.asset.try_to_runtime().unwrap();
    assert_eq!(finalized.lifecycle, AssetLifecycleV16::Recovery);
    assert_eq!(finalized.mode_long, SideModeV16::Normal);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_auto_crank_skips_prior_reset_obligation_for_live_liquidation() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 23);
    header.current_slot = V16PodU64::new(10);
    header.slot_last = V16PodU64::new(10);

    let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
    asset0.slot_last = 10;
    asset0.epoch_long = 1;
    asset0.mode_long = SideModeV16::ResetPending;
    asset0.oi_eff_long_q = 0;
    asset0.oi_eff_short_q = 0;
    asset0.loss_weight_sum_long = 0;
    asset0.loss_weight_sum_short = 0;
    asset0.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);

    let mut asset1 = markets[1].engine.asset.try_to_runtime().unwrap();
    asset1.slot_last = 10;
    asset1.oi_eff_long_q = 2 * POS_SCALE;
    asset1.oi_eff_short_q = 2 * POS_SCALE;
    asset1.loss_weight_sum_long = 2 * POS_SCALE;
    asset1.loss_weight_sum_short = 2 * POS_SCALE;
    asset1.stored_pos_count_long = 2;
    asset1.stored_pos_count_short = 2;
    markets[1].engine.asset = AssetStateV16Account::from_runtime(&asset1);
    header.resolved_payout_blocker_count = V16PodU64::new(5);

    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset0.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset0.k_epoch_start_long,
        f_snap: asset0.f_epoch_start_long_num,
        kf_epoch_snap: 0,
        epoch_snap: 0,
        loss_weight: POS_SCALE,
        b_snap: asset0.b_epoch_start_long_num,
        b_rem: 0,
        b_epoch_snap: 0,
        b_stale: false,
        stale: false,
    });
    account_header.legs[1] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 1,
        market_id: asset1.market_id,
        side: SideV16::Short,
        basis_pos_q: -(POS_SCALE as i128),
        a_basis: ADL_ONE,
        k_snap: asset1.k_short,
        f_snap: asset1.f_short_num,
        kf_epoch_snap: 0,
        epoch_snap: asset1.epoch_short,
        loss_weight: POS_SCALE,
        b_snap: asset1.b_short_num,
        b_rem: 0,
        b_epoch_snap: asset1.epoch_short,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(3);
    account_header.health_cert = HealthCertV16Account::from_runtime(&HealthCertV16 {
        certified_equity: 0,
        certified_initial_req: 2,
        certified_maintenance_req: 2,
        certified_liq_deficit: 2,
        certified_worst_case_loss: 200,
        cert_oracle_epoch: header.oracle_epoch.get(),
        cert_funding_epoch: header.funding_epoch.get(),
        cert_risk_epoch: header.risk_epoch.get(),
        cert_asset_set_epoch: header.asset_set_epoch.get(),
        active_bitmap_at_cert: [3],
        valid: true,
    });

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let refresh = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the prior-reset first leg must be detached permissionlessly");

    assert_eq!(
        refresh.selected,
        AutoCrankPlanV16::RefreshAccount {
            asset_index: Some(0)
        }
    );
    assert!(!account.header.legs[0].try_to_runtime().unwrap().active);
    assert!(account.header.legs[1].try_to_runtime().unwrap().active);

    let liquidation = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the next step must liquidate the remaining live asset");
    assert_eq!(
        liquidation.selected,
        AutoCrankPlanV16::Liquidate { asset_index: 1 }
    );
    assert!(!account.header.legs[1].try_to_runtime().unwrap().active);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

#[test]
#[cfg(feature = "fuzz")]
fn v16_fractional_social_loss_carry_normalizes_on_reset_and_clear() {
    for side in [SideV16::Long, SideV16::Short] {
        let mut reset_asset = AssetStateV16::default();
        reset_asset.lifecycle = AssetLifecycleV16::Active;
        let remainder = SOCIAL_LOSS_DEN / 2 + 1;
        let dust = SOCIAL_LOSS_DEN / 2;
        match side {
            SideV16::Long => {
                reset_asset.oi_eff_long_q = 0;
                reset_asset.stored_pos_count_long = 1;
                reset_asset.social_loss_remainder_long_num = remainder;
                reset_asset.social_loss_dust_long_num = dust;
                reset_asset.explicit_unallocated_loss_long = 7;
            }
            SideV16::Short => {
                reset_asset.oi_eff_short_q = 0;
                reset_asset.stored_pos_count_short = 1;
                reset_asset.social_loss_remainder_short_num = remainder;
                reset_asset.social_loss_dust_short_num = dust;
                reset_asset.explicit_unallocated_loss_short = 7;
            }
        }

        let reset =
            MarketGroupV16ViewMut::<u64>::kani_kernel_begin_full_drain_reset(reset_asset, side)
                .expect("a valid fractional carry must not block reset");
        match side {
            SideV16::Long => {
                assert_eq!(reset.social_loss_remainder_long_num, 0);
                assert_eq!(reset.social_loss_dust_long_num, 1);
                assert_eq!(reset.explicit_unallocated_loss_long, 8);
            }
            SideV16::Short => {
                assert_eq!(reset.social_loss_remainder_short_num, 0);
                assert_eq!(reset.social_loss_dust_short_num, 1);
                assert_eq!(reset.explicit_unallocated_loss_short, 8);
            }
        }

        let mut clear_asset = AssetStateV16::default();
        clear_asset.lifecycle = AssetLifecycleV16::Active;
        let basis_q = POS_SCALE;
        match side {
            SideV16::Long => {
                clear_asset.oi_eff_long_q = basis_q;
                clear_asset.loss_weight_sum_long = basis_q;
                clear_asset.stored_pos_count_long = 1;
                clear_asset.social_loss_dust_long_num = SOCIAL_LOSS_DEN / 2;
                clear_asset.explicit_unallocated_loss_long = 11;
            }
            SideV16::Short => {
                clear_asset.oi_eff_short_q = basis_q;
                clear_asset.loss_weight_sum_short = basis_q;
                clear_asset.stored_pos_count_short = 1;
                clear_asset.social_loss_dust_short_num = SOCIAL_LOSS_DEN / 2;
                clear_asset.explicit_unallocated_loss_short = 11;
            }
        }
        let basis_pos_q = match side {
            SideV16::Long => basis_q as i128,
            SideV16::Short => -(basis_q as i128),
        };
        let leg = PortfolioLegV16 {
            active: true,
            side,
            basis_pos_q,
            loss_weight: basis_q,
            b_rem: SOCIAL_LOSS_DEN / 2,
            ..PortfolioLegV16::EMPTY
        };
        let cleared =
            MarketGroupV16ViewMut::<u64>::kani_kernel_clear_leg(leg, clear_asset, basis_q)
                .expect("a valid fractional carry must not block leg clear");
        match side {
            SideV16::Long => {
                assert_eq!(cleared.social_loss_dust_long_num, 0);
                assert_eq!(cleared.explicit_unallocated_loss_long, 12);
            }
            SideV16::Short => {
                assert_eq!(cleared.social_loss_dust_short_num, 0);
                assert_eq!(cleared.explicit_unallocated_loss_short, 12);
            }
        }
    }

    assert_eq!(
        MarketGroupV16ViewMut::<u64>::kani_kernel_normalize_social_loss_carry(
            SOCIAL_LOSS_DEN - 1,
            1,
            u128::MAX,
        )
        .unwrap(),
        (0, u128::MAX),
        "audit-counter saturation must remain a successful value-neutral normalization"
    );
}

/// Upstream dfd7eed4 ("test: reproduce foreign-expired source lien lock"), the
/// reproducing test for the 1e0d952e fix in this commit's parent. A second
/// account's activity expires the shared backing bucket while this account still
/// holds a counterparty lien against it; resolved close must reconcile that lien
/// instead of locking. Ported in its dfd7eed4 form, which is the form that
/// discriminates the fix; 0a23b5f5 extends it next.
#[test]
fn v16_resolved_foreign_expiry_impairs_account_lien_before_release() {
    const Q: u128 = 1_000 * POS_SCALE;
    const INCREASE_Q: u128 = POS_SCALE;
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.maintenance_margin_bps = 1_000;
    cfg.initial_margin_bps = 5_000;
    cfg.max_price_move_bps_per_slot = 500;
    cfg.max_accrual_dt_slots = 1;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
        .unwrap();

    let mut target_header = account_fixture(1, 44);
    let mut target_peer_header = account_fixture(1, 45);
    let mut expiry_trigger_header = account_fixture(1, 46);
    let mut trigger_peer_header = account_fixture(1, 47);
    let mut sibling_target_header = account_fixture(1, 48);
    let mut sibling_peer_header = account_fixture(1, 49);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut target = PortfolioV16ViewMut::new(&mut target_header);
    let mut target_peer = PortfolioV16ViewMut::new(&mut target_peer_header);
    let mut expiry_trigger = PortfolioV16ViewMut::new(&mut expiry_trigger_header);
    let mut trigger_peer = PortfolioV16ViewMut::new(&mut trigger_peer_header);
    let mut sibling_target = PortfolioV16ViewMut::new(&mut sibling_target_header);
    let mut sibling_peer = PortfolioV16ViewMut::new(&mut sibling_peer_header);

    market
        .deposit_fresh_counterparty_backing_not_atomic(1, 100_000, 3)
        .unwrap();
    market.deposit_not_atomic(&mut target, 52_501).unwrap();
    market
        .deposit_not_atomic(&mut target_peer, 1_000_000)
        .unwrap();
    market
        .deposit_not_atomic(&mut expiry_trigger, 1_000_000)
        .unwrap();
    market
        .deposit_not_atomic(&mut trigger_peer, 1_000_000)
        .unwrap();
    market
        .deposit_not_atomic(&mut sibling_target, 52_501)
        .unwrap();
    market
        .deposit_not_atomic(&mut sibling_peer, 1_000_000)
        .unwrap();
    for (long, short) in [
        (&mut target, &mut target_peer),
        (&mut expiry_trigger, &mut trigger_peer),
        (&mut sibling_target, &mut sibling_peer),
    ] {
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                long,
                short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(Q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }

    market
        .set_asset_raw_oracle_target_not_atomic(0, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 105, 0, true)
        .unwrap();
    for account in [
        &mut target_peer,
        &mut trigger_peer,
        &mut sibling_peer,
        &mut target,
        &mut expiry_trigger,
        &mut sibling_target,
    ] {
        market.full_account_refresh_not_atomic(account).unwrap();
    }
    for (long, short) in [
        (&mut target, &mut target_peer),
        (&mut sibling_target, &mut sibling_peer),
    ] {
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                long,
                short,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(INCREASE_Q),
                    exec_price: 105,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }
    let lien_before = target.header.source_domains[0];
    let sibling_lien_before = sibling_target.header.source_domains[0];
    assert!(lien_before.source_claim_counterparty_liened_num.get() > 0);
    assert!(lien_before.source_lien_counterparty_backing_num.get() > 0);
    assert!(
        sibling_lien_before
            .source_lien_counterparty_backing_num
            .get()
            > 0
    );
    assert_eq!(lien_before.source_claim_impaired_num.get(), 0);
    assert!(
        expiry_trigger.header.source_domains[0]
            .source_claim_bound_num
            .get()
            > 0
    );
    assert_eq!(
        expiry_trigger.header.source_domains[0]
            .source_claim_liened_num
            .get(),
        0
    );

    market.resolve_market_not_atomic(3).unwrap();
    assert_eq!(
        market
            .close_resolved_account_not_atomic(&mut expiry_trigger, 0)
            .unwrap(),
        percolator::ResolvedCloseOutcomeV16::ProgressOnly,
    );
    let bucket_before = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    assert_eq!(bucket_before.status, BackingBucketStatusV16::Impaired);

    let mut relabeled = false;
    for _ in 0..4 {
        assert_eq!(
            market
                .close_resolved_account_not_atomic(&mut target, 0)
                .expect("foreign bucket expiry must leave bounded lien-impairment continuations",),
            percolator::ResolvedCloseOutcomeV16::ProgressOnly,
        );
        if target.header.source_domains[0]
            .source_claim_counterparty_liened_num
            .get()
            == 0
        {
            relabeled = true;
            break;
        }
    }
    assert!(relabeled, "the account-local lien never became impaired");
    let impaired = target.header.source_domains[0];
    assert_eq!(impaired.source_claim_liened_num.get(), 0);
    assert_eq!(impaired.source_claim_counterparty_liened_num.get(), 0);
    assert_eq!(impaired.source_lien_counterparty_backing_num.get(), 0);
    assert_eq!(
        impaired.source_claim_impaired_num.get(),
        lien_before.source_claim_counterparty_liened_num.get()
    );
    assert_eq!(
        impaired.source_lien_impaired_effective_reserved.get(),
        0,
        "expired provider principal must not be reclassified as impaired insurance"
    );
    let bucket_after_target_relabel = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    assert_eq!(
        bucket_after_target_relabel.impaired_liened_backing_num,
        bucket_before.impaired_liened_backing_num
            - lien_before.source_lien_counterparty_backing_num.get(),
        "the target must retire exactly its own expired provider-lien label"
    );
    assert!(
        bucket_after_target_relabel.impaired_liened_backing_num
            >= sibling_lien_before
                .source_lien_counterparty_backing_num
                .get(),
        "the first relabel must preserve its sibling's provider-lien label"
    );

    let mut all_closed = false;
    let mut last_outcomes = Vec::new();
    for _ in 0..16 {
        last_outcomes.clear();
        for account in [
            &mut target_peer,
            &mut trigger_peer,
            &mut sibling_peer,
            &mut expiry_trigger,
            &mut target,
            &mut sibling_target,
        ] {
            last_outcomes.push(
                market
                    .close_resolved_account_not_atomic(account, 0)
                    .expect("foreign-expired source claims must retain a terminal continuation"),
            );
        }
        all_closed = [
            &target_peer,
            &trigger_peer,
            &sibling_peer,
            &expiry_trigger,
            &target,
            &sibling_target,
        ]
        .iter()
        .all(|account| {
            account.header.capital.get() == 0
                && account.header.pnl.get() == 0
                && active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get))
        });
        if all_closed {
            break;
        }
    }
    assert!(
        all_closed,
        "foreign-expired source claims did not terminate: last={last_outcomes:?}"
    );
    let bucket_after = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    let source_after = market.markets[0]
        .engine
        .source_credit_short
        .try_to_runtime()
        .unwrap();
    assert_eq!(bucket_after.status, BackingBucketStatusV16::Expired);
    assert_eq!(bucket_after.impaired_liened_backing_num, 0);
    assert_eq!(source_after.impaired_liened_backing_num, 0);
    market.validate_shape().unwrap();
    target.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_resolved_close_normalizes_prospective_lapsed_source_before_settlement() {
    const Q: u128 = 1_000 * POS_SCALE;
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.max_price_move_bps_per_slot = 500;
    cfg.max_accrual_dt_slots = 1;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
        .unwrap();

    let mut long_header = account_fixture(1, 50);
    let mut short_header = account_fixture(1, 51);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
    market
        .deposit_fresh_counterparty_backing_not_atomic(1, 100_000, 3)
        .unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(Q),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    market
        .set_asset_raw_oracle_target_not_atomic(0, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 105, 0, true)
        .unwrap();
    market.resolve_market_not_atomic(4).unwrap();

    assert_eq!(long.header.pnl.get(), 0);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh,
    );
    assert_eq!(
        market.close_resolved_account_not_atomic(&mut long, 0),
        Ok(percolator::ResolvedCloseOutcomeV16::ProgressOnly),
    );
    assert_eq!(long.header.pnl.get(), 0);
    assert!(long.header.legs[0].try_to_runtime().unwrap().active);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Expired,
    );

    assert_eq!(
        market.close_resolved_account_not_atomic(&mut long, 0),
        Ok(percolator::ResolvedCloseOutcomeV16::ProgressOnly),
    );
    assert!(long.header.pnl.get() > 0);
    assert!(!long.header.legs[0].try_to_runtime().unwrap().active);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
}

// Fork regression, adjacent to upstream 50ae7b62's own spec test above.
//
// `expire_one_lapsed_source_backing_for_resolved_active_leg_not_atomic` scans
// BOTH insurance domains of every leg slot, but only for slots whose leg is
// ACTIVE. That `leg.active` guard is load-bearing and was untested: an empty
// leg slot is `PortfolioLegV16::EMPTY`, whose `asset_index` is 0, so dropping
// the guard silently aims the scan at asset 0's domains for all 16 static
// slots. A resolved close would then expire a Fresh source-backing bucket in a
// domain the closing account holds no leg in -- foreign backing normalized as
// a side effect of an unrelated account's close.
//
// Here the only active leg is on asset 1 and the lapsed Fresh bucket sits on
// asset 0 / Short (domain 1), so the guard is the only thing keeping the scan
// off it. Removing `leg.active` flips the final assertion to `Expired`.
#[test]
fn v16_resolved_close_prospective_expiry_scan_skips_inactive_leg_slots() {
    const Q: u128 = 1_000 * POS_SCALE;
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(2, 2, 0, 10);
    cfg.max_price_move_bps_per_slot = 500;
    cfg.max_accrual_dt_slots = 1;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 2, 0).unwrap();
    let mut markets = vec![
        Market::new(0, EngineAssetSlotV16Account::default()),
        Market::new(1, EngineAssetSlotV16Account::default()),
    ];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
        .unwrap();
    header
        .activate_empty_asset_slot_not_atomic(1, &mut markets[1].engine, 100, 2)
        .unwrap();

    let mut long_header = account_fixture(2, 50);
    let mut short_header = account_fixture(2, 51);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000_000).unwrap();
    // Lapsing Fresh backing on ASSET 0 / Short (domain 1). Neither account
    // under test ever holds a leg on asset 0.
    market
        .deposit_fresh_counterparty_backing_not_atomic(1, 100_000, 3)
        .unwrap();
    // The only traded asset is ASSET 1.
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 1,
                size_q: signed_q(Q),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    market
        .set_asset_raw_oracle_target_not_atomic(1, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(1, 3, 105, 0, true)
        .unwrap();
    market.resolve_market_not_atomic(4).unwrap();

    // Slot 0 carries the asset-1 leg; every other static slot is EMPTY and
    // therefore reports asset_index 0 -- the shape the guard has to survive.
    let leg0 = long.header.legs[0].try_to_runtime().unwrap();
    assert!(leg0.active);
    assert_eq!(leg0.asset_index, 1);
    for slot in 1..percolator::V16_MAX_PORTFOLIO_ASSETS_N {
        let leg = long.header.legs[slot].try_to_runtime().unwrap();
        assert!(!leg.active, "slot {} unexpectedly active", slot);
        assert_eq!(leg.asset_index, 0, "empty slot {} asset_index", slot);
    }
    assert_eq!(
        market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh,
    );

    // Crank the loss side first so the winner's positive payout can settle.
    for account in [&mut short, &mut long] {
        let mut steps = 0usize;
        loop {
            match market.close_resolved_account_not_atomic(account, 0) {
                Ok(ResolvedCloseOutcomeV16::ProgressOnly) => {
                    steps += 1;
                    assert!(steps < 64, "resolved close did not terminate");
                }
                Ok(ResolvedCloseOutcomeV16::Closed { .. }) => break,
                Err(e) => panic!("resolved close halted with {:?}", e),
            }
        }
    }

    assert_eq!(
        market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh,
        "an INACTIVE leg slot must not reach a foreign domain's source backing",
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

// upstream b4b975f3 "fix: allow lagging committed checkpoint accrual" (2026-08-31):
// `now_slot` is the endpoint of one asset-local committed segment. Another asset can
// already have advanced the market's authenticated clock past it, so a lagging asset
// must still be able to settle its earlier checkpoint while the global clock stays
// monotonic (max), and an asset-local checkpoint still cannot move behind that
// asset's own clock.
#[test]
fn v16_asset_local_committed_accrual_can_trail_global_clock() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    market
        .accrue_asset_to_not_atomic(0, 10, 100, 0, true)
        .expect("the first asset must advance the authenticated market clock");
    let global_slot = market.header.current_slot.get();
    let lagging_before = market.markets[1].engine.asset.slot_last.get();
    let committed_slot = lagging_before + 1;
    assert!(committed_slot < global_slot);

    let outcome = market
        .accrue_asset_to_not_atomic(1, committed_slot, 100, 0, true)
        .expect("a lagging asset must settle an earlier committed checkpoint");

    assert_eq!(outcome.dt, 1);
    assert_eq!(
        market.markets[1].engine.asset.slot_last.get(),
        committed_slot
    );
    assert_eq!(market.header.current_slot.get(), global_slot);
    assert_eq!(
        market.accrue_asset_to_not_atomic(1, committed_slot - 1, 100, 0, true),
        Err(V16Error::InvalidConfig),
        "an asset-local checkpoint still cannot move behind that asset's own clock"
    );
    market.validate_shape().unwrap();
}

// upstream 44847fd5 "Authenticate resolved settlement time" (2026-08-20): resolved
// routes do not accrue markets, but expiry-sensitive backing still needs a
// monotonic clock. The wrapper authenticates the slot (Clock sysvar) and the
// engine admits it only in Resolved mode and only forward.
#[test]
fn v16_resolved_clock_advance_is_monotonic_and_value_neutral() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let vault_before = header.vault;
    let c_tot_before = header.c_tot;
    let insurance_before = header.insurance;
    let markets_before = markets.clone();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(5).unwrap();
    market.advance_resolved_slot_not_atomic(9).unwrap();
    assert_eq!(market.header.current_slot.get(), 9);
    assert_eq!(market.header.resolved_slot.get(), 5);
    assert_eq!(market.header.vault, vault_before);
    assert_eq!(market.header.c_tot, c_tot_before);
    assert_eq!(market.header.insurance, insurance_before);
    assert_eq!(market.markets, &markets_before[..]);

    assert_eq!(
        market.advance_resolved_slot_not_atomic(8),
        Err(V16Error::Stale)
    );
    assert_eq!(market.header.current_slot.get(), 9);

    let (mut live_header, mut live_markets) = market_fixture(1, 100);
    let live_slot = live_header.current_slot;
    let mut live = MarketGroupV16ViewMut::new(&mut live_header, &mut live_markets);
    assert_eq!(
        live.advance_resolved_slot_not_atomic(9),
        Err(V16Error::LockActive)
    );
    assert_eq!(live.header.current_slot, live_slot);
}

// upstream c0dec8ce "Canonicalize source-domain allocation order" (2026-08-29):
// the mutable view compacts AND orders occupied source domains by domain index,
// so bounded one-domain-per-call continuations see one canonical layout
// regardless of allocation history.
#[test]
fn v16_mutable_view_canonicalizes_persisted_source_domain_order() {
    let mut account_header = account_fixture(2, 120);
    account_header.source_domains[0].domain = V16PodU32::new(3);
    account_header.source_domains[0].source_claim_market_id = V16PodU64::new(2);
    account_header.source_domains[0].source_claim_bound_num = V16PodU128::new(3 * BOUND_SCALE);
    account_header.source_domains[2].domain = V16PodU32::new(1);
    account_header.source_domains[2].source_claim_market_id = V16PodU64::new(1);
    account_header.source_domains[2].source_claim_bound_num = V16PodU128::new(BOUND_SCALE);

    let account = PortfolioV16ViewMut::new(&mut account_header);

    assert_eq!(account.header.source_domains[0].domain.get(), 1);
    assert_eq!(
        account.header.source_domains[0]
            .source_claim_bound_num
            .get(),
        BOUND_SCALE
    );
    assert_eq!(account.header.source_domains[1].domain.get(), 3);
    assert_eq!(
        account.header.source_domains[1]
            .source_claim_bound_num
            .get(),
        3 * BOUND_SCALE
    );
    assert!(account.header.source_domains[2..]
        .iter()
        .all(|source| *source == PortfolioSourceDomainV16Account::default()));
}

// upstream c09d4575 "Fix live source-backing expiry progress" (2026-08-06): a
// source-backed winner can remain Live past its backing bucket's expiry; the
// permissionless refresh commits exactly one canonical expiry transition per
// call (SourceBackingExpired { domain }) before valuation, so repeated cranks
// drain the bounded domain set. Fork adaptation: upstream drives this through
// permissionless_auto_crank_not_atomic (not ported); ours uses the Refresh action
// of permissionless_crank_not_atomic, which reaches the same refresh path with
// allow_b_chunk = true.
#[test]
fn v16_permissionless_refresh_expires_one_lapsed_live_source_domain_per_step() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 22);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 100).unwrap();
        market
            .deposit_fresh_counterparty_backing_not_atomic(1, 40, 5)
            .unwrap();
        market
            .deposit_fresh_counterparty_backing_not_atomic(3, 40, 5)
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut account, 1, 40)
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut account, 3, 40)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(0, 10, 100, 0, true)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(1, 10, 100, 0, true)
            .unwrap();
    }

    let before = markets[0].engine.backing_short.try_to_runtime().unwrap();
    assert_eq!(before.status, BackingBucketStatusV16::Fresh);
    assert_eq!(before.expiry_slot, 5);
    assert_eq!(
        markets[1]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh
    );
    assert!(header.current_slot.get() > before.expiry_slot);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();
    let earnings_before = header.backing_provider_earnings_total.get();
    let source_backing_before = header.source_fresh_backing_total_num.get();
    let risk_epoch_before = header.risk_epoch.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let refresh_request = PermissionlessCrankRequestV16 {
        now_slot: 10,
        asset_index: 0,
        effective_price: 100,
        funding_rate_e9: 0,
        action: PermissionlessCrankActionV16::Refresh,
    };
    let expiry = market
        .permissionless_crank_not_atomic(&mut account, refresh_request)
        .expect("a Live refresh must expire lapsed backing instead of returning Stale");
    assert_eq!(
        expiry,
        PermissionlessProgressOutcomeV16::SourceBackingExpired { domain: 1 }
    );
    let after = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    assert_eq!(after.status, BackingBucketStatusV16::Expired);
    assert_eq!(after.fresh_unliened_backing_num, 0);
    assert_eq!(
        market.markets[1]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh,
        "one refresh expires exactly one source domain"
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.backing_provider_earnings_total.get(),
        earnings_before
    );
    assert_eq!(
        market.header.source_fresh_backing_total_num.get(),
        source_backing_before - 40 * BOUND_SCALE
    );
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 1);
    assert_eq!(account.header.capital.get(), 100);
    assert_eq!(account.header.pnl.get(), 80);
    assert!(!account.header.health_cert.try_to_runtime().unwrap().valid);

    let second_expiry = market
        .permissionless_crank_not_atomic(&mut account, refresh_request)
        .expect("the next bounded refresh must expire the next domain");
    assert_eq!(
        second_expiry,
        PermissionlessProgressOutcomeV16::SourceBackingExpired { domain: 3 }
    );
    assert_eq!(
        market.markets[1]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Expired
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.backing_provider_earnings_total.get(),
        earnings_before
    );
    assert_eq!(market.header.source_fresh_backing_total_num.get(), 0);
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 2);

    let refresh = market
        .permissionless_crank_not_atomic(&mut account, refresh_request)
        .expect("the final bounded refresh must finish account refresh");
    assert_eq!(refresh, PermissionlessProgressOutcomeV16::AccountCurrent);
    assert!(account.header.health_cert.try_to_runtime().unwrap().valid);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// upstream 650e3fdf "Commit recovery for unbookable terminal forfeits" (2026-08-22):
// when a Recovery-mode owner forfeit leaves a residual that the absorbing side
// cannot book (capacity 0), the forfeit COMMITS Recovery as a successful
// transition instead of returning RecoveryRequired. On Solana an Err discards the
// whole instruction, so the declared mode never persisted and the only path to
// resolved settlement was unreachable (the dead escalation valve). Fork
// adaptation: upstream's tail finalizes through permissionless_auto_crank
// (row 241, not ported); the committed state is asserted directly.
#[test]
fn v16_recovery_forfeit_commits_terminal_recovery_when_absorbing_side_is_empty() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 28);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market.force_asset_recovery_not_atomic(0, 2).unwrap();
    }

    let mut asset = markets[0].engine.asset.try_to_runtime().unwrap();
    asset.oi_eff_long_q = POS_SCALE;
    asset.loss_weight_sum_long = POS_SCALE;
    asset.stored_pos_count_long = 1;
    markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset);
    header.negative_pnl_account_count = V16PodU64::new(1);
    header.resolved_payout_blocker_count = V16PodU64::new(1);
    account_header.pnl = V16PodI128::new(-5);
    account_header.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
        active: true,
        asset_index: 0,
        market_id: asset.market_id,
        side: SideV16::Long,
        basis_pos_q: POS_SCALE as i128,
        a_basis: ADL_ONE,
        k_snap: asset.k_long,
        f_snap: asset.f_long_num,
        kf_epoch_snap: 0,
        epoch_snap: asset.epoch_long,
        loss_weight: POS_SCALE,
        b_snap: asset.b_long_num,
        b_rem: 0,
        b_epoch_snap: asset.epoch_long,
        b_stale: false,
        stale: false,
    });
    account_header.active_bitmap[0] = V16PodU64::new(1);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();

    let outcome = market
        .forfeit_recovery_leg_not_atomic(&mut account, 0, u128::MAX)
        .expect("forfeit must commit Recovery instead of returning a rollback-only error");
    assert!(!outcome.detached);
    assert_eq!(outcome.residual_booked, 0);
    assert_eq!(outcome.explicit_loss, 0);
    assert_eq!(market.header.mode, 2);
    assert_eq!(
        market.header.recovery_reason.try_to_runtime().unwrap(),
        Some(PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress)
    );
    assert_eq!(account.header.pnl.get(), -5);
    assert_eq!(
        account
            .header
            .close_progress
            .try_to_runtime()
            .unwrap()
            .residual_remaining,
        5
    );
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

// upstream f06a04a7 "Keep strict trade reductions open below initial margin"
// (2026-08-06): an account whose fill is a STRICT reduction of its position on
// the asset skips the final initial-margin gate (and the IM source-lien /
// locked-lane no-positive-credit gates), so an under-margin owner can hand risk
// to a margin-healthy counterparty. Fork adaptation: the taker flag is passed
// explicitly (taker-only fee model, KL-ENGINE-TAKER-ONLY-FEE).
#[test]
fn v16_under_margin_owner_can_transfer_risk_to_margin_healthy_counterparty() {
    const OPEN_Q: u128 = 100 * POS_SCALE;
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(5_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(1_000);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    let mut owner_header = account_fixture(1, 12);
    let mut original_short_header = account_fixture(1, 13);
    let mut new_holder_header = account_fixture(1, 14);

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut owner = PortfolioV16ViewMut::new(&mut owner_header);
    let mut original_short = PortfolioV16ViewMut::new(&mut original_short_header);
    let mut new_holder = PortfolioV16ViewMut::new(&mut new_holder_header);
    market.deposit_not_atomic(&mut owner, 5_001).unwrap();
    market
        .deposit_not_atomic(&mut original_short, 100_000)
        .unwrap();
    market.deposit_not_atomic(&mut new_holder, 10_000).unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut owner,
            &mut original_short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(OPEN_Q),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();

    market
        .set_asset_raw_oracle_target_not_atomic(0, 90)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 90, 0, true)
        .unwrap();
    market
        .full_account_refresh_not_atomic(&mut original_short)
        .unwrap();
    let owner_cert = market.full_account_refresh_not_atomic(&mut owner).unwrap();
    market
        .full_account_refresh_not_atomic(&mut new_holder)
        .unwrap();
    assert!(
        owner_cert.certified_equity >= 0
            && (owner_cert.certified_equity as u128) < owner_cert.certified_initial_req,
        "owner must be below IM before the transfer"
    );

    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut owner,
            &mut new_holder,
            TradeRequestV16 {
                asset_index: 0,
                size_q: -signed_q(POS_SCALE),
                exec_price: 90,
                fee_bps: 0,
            },
            true,
        )
        .expect("strict reducer may exit while the new risk holder passes IM");

    assert_eq!(
        owner.header.legs[0].try_to_runtime().unwrap().basis_pos_q,
        signed_q(99 * POS_SCALE)
    );
    assert_eq!(
        new_holder.header.legs[0]
            .try_to_runtime()
            .unwrap()
            .basis_pos_q,
        signed_q(POS_SCALE)
    );
    let new_holder_cert = new_holder.header.health_cert.try_to_runtime().unwrap();
    assert!(
        new_holder_cert.valid
            && new_holder_cert.certified_equity >= 0
            && (new_holder_cert.certified_equity as u128) >= new_holder_cert.certified_initial_req,
        "new risk holder remains fully margined"
    );
    market.validate_shape().unwrap();
    owner.validate_with_market(&market.as_view()).unwrap();
    original_short
        .validate_with_market(&market.as_view())
        .unwrap();
    new_holder.validate_with_market(&market.as_view()).unwrap();
}

// upstream 379fbfea "Normalize lapsed backing during asset retirement" (2026-08-20):
// retirement is the terminal consumer for one asset, so it normalizes both of the
// asset's source domains (expire a lapsed Fresh bucket, canonicalize an
// economically empty Expired one) before testing whether the slot is empty. This
// also covers a lapsed bucket that no portfolio references.
#[test]
fn v16_retire_normalizes_unreferenced_lapsed_backing() {
    const BACKING: u128 = 7;
    const EXPIRY_SLOT: u64 = 5;
    const DOMAIN: usize = 2;

    let (mut header, mut markets) = market_fixture(2, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .deposit_fresh_counterparty_backing_not_atomic(DOMAIN, BACKING, EXPIRY_SLOT)
            .unwrap();
    }
    let vault_before = header.vault.get();
    let bucket_before = markets[1].engine.backing_long.try_to_runtime().unwrap();
    assert_eq!(bucket_before.status, BackingBucketStatusV16::Fresh);
    assert_eq!(
        bucket_before.fresh_unliened_backing_num,
        BACKING * BOUND_SCALE
    );

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        assert_eq!(
            market.retire_empty_asset_not_atomic(1, EXPIRY_SLOT - 1),
            Err(V16Error::LockActive),
            "fresh principal remains a retirement blocker"
        );
    }
    assert_eq!(header.vault.get(), vault_before);
    assert_eq!(
        markets[1].engine.asset.try_to_runtime().unwrap().lifecycle,
        AssetLifecycleV16::Active
    );

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .retire_empty_asset_not_atomic(1, EXPIRY_SLOT)
        .unwrap();
    let bucket = market.markets[1]
        .engine
        .backing_long
        .try_to_runtime()
        .unwrap();
    let source = market.markets[1]
        .engine
        .source_credit_long
        .try_to_runtime()
        .unwrap();
    assert_eq!(bucket.status, BackingBucketStatusV16::Empty);
    assert_eq!(bucket.expiry_slot, 0);
    assert_eq!(bucket.fresh_unliened_backing_num, 0);
    assert_eq!(source.fresh_reserved_backing_num, 0);
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(
        market.markets[1]
            .engine
            .asset
            .try_to_runtime()
            .unwrap()
            .lifecycle,
        AssetLifecycleV16::Retired
    );
    market.validate_shape().unwrap();
}

// upstream a7577b0b "Credit backing released after payout snapshot" (2026-07-20):
// once the terminal payout snapshot is captured, principal released by a backing
// expiry must reach the resolved payout ledger (snapshot_residual and the legacy
// payout_snapshot) and raise the common payout rate, otherwise the released
// residual is stranded forever behind a frozen snapshot. Fork test (upstream ships
// the kernel proof only).
#[test]
fn v16_post_snapshot_backing_expiry_credits_resolved_payout_ledger() {
    const BACKING: u128 = 7;
    const EXPIRY_SLOT: u64 = 5;
    const CLAIM_ATOMS: u128 = 20;

    let (mut header, mut markets) = market_fixture(1, 100);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        market
            .deposit_fresh_counterparty_backing_not_atomic(0, BACKING, EXPIRY_SLOT)
            .unwrap();
        market.resolve_market_not_atomic(EXPIRY_SLOT + 1).unwrap();
    }
    // Terminal snapshot captured before the lapsed bucket expired: the junior
    // pool the snapshot saw excludes the still-reserved backing principal.
    let residual_before = header.vault.get()
        - header.c_tot.get()
        - header.insurance.get()
        - header.backing_provider_earnings_total.get()
        - BACKING;
    header.payout_snapshot_captured = 1;
    header.payout_snapshot = V16PodU128::new(residual_before);
    header.payout_snapshot_pnl_pos_tot = V16PodU128::new(CLAIM_ATOMS);
    let claim_num = CLAIM_ATOMS * BOUND_SCALE;
    header.resolved_payout_ledger =
        ResolvedPayoutLedgerV16Account::from_runtime(&ResolvedPayoutLedgerV16 {
            snapshot_residual: residual_before,
            terminal_claim_exact_receipts_num: 0,
            terminal_claim_bound_unreceipted_num: claim_num,
            current_payout_rate_num: (residual_before * BOUND_SCALE).min(claim_num),
            current_payout_rate_den: claim_num,
            snapshot_slot: EXPIRY_SLOT + 1,
            payout_halted: false,
            finalized: false,
        });
    let vault_before = header.vault.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .expire_source_backing_bucket_not_atomic(0, EXPIRY_SLOT + 1)
        .unwrap();

    let ledger = market
        .header
        .resolved_payout_ledger
        .try_to_runtime()
        .unwrap();
    assert_eq!(
        ledger.snapshot_residual,
        residual_before + BACKING,
        "released principal must be credited to the snapshot residual"
    );
    assert_eq!(
        market.header.payout_snapshot.get(),
        residual_before + BACKING
    );
    assert_eq!(
        ledger.current_payout_rate_num,
        ((residual_before + BACKING) * BOUND_SCALE).min(claim_num)
    );
    assert_eq!(ledger.current_payout_rate_den, claim_num);
    assert_eq!(ledger.terminal_claim_bound_unreceipted_num, claim_num);
    assert_eq!(market.header.vault.get(), vault_before);
}

// ---------------------------------------------------------------------------
// upstream 6d8e0a48 "Fix unattributed cross-margin insurance drain" (2026-08-26)
// + 9b737fdc "Prove unattributed loss lock lifecycle".
//
// Account PnL is one cross-margin scalar. Once a negative PnL has spanned more
// than one active asset, no single asset's insurance / B domain can be charged
// for it. The engine marks the account (`liquidation_lock`) at the detach that
// leaves an uncovered loss with open risk, keeps the mark while the deficit is
// negative, and liquidates such an account REDUCE-ONLY: no insurance, no
// bankruptcy residual booked against the surviving asset.
//
// ---------------------------------------------------------------------------

fn unattributed_deficit_fixture() -> (
    MarketGroupV16HeaderAccount,
    Vec<Market<u64>>,
    PortfolioAccountV16Account,
    PortfolioAccountV16Account,
) {
    let (mut header, markets) = market_fixture(2, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let long_header = account_fixture(2, 65);
    let short_header = account_fixture(2, 66);
    (header, markets, long_header, short_header)
}

/// Opens 10 units long/short on both assets (long 2_000 capital, short 250),
/// ramps asset 0 from 105 to 150 (short loses 500 on asset 0), then closes the
/// asset-0 leg by a risk-reducing trade. Returns with the short at pnl -250,
/// capital 0, one open leg on asset 1, and `liquidation_lock == 1`.
fn open_unattributed_deficit(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    long: &mut PortfolioV16ViewMut<'_>,
    short: &mut PortfolioV16ViewMut<'_>,
) {
    const SIZE_Q: u128 = 10 * POS_SCALE;
    market.deposit_not_atomic(long, 2_000).unwrap();
    market.deposit_not_atomic(short, 250).unwrap();
    for asset_index in 0..2 {
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                long,
                short,
                TradeRequestV16 {
                    asset_index,
                    size_q: signed_q(SIZE_Q),
                    exec_price: 100,
                    fee_bps: 0,
                },
                true,
            )
            .unwrap();
    }
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
            long,
            short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: -signed_q(SIZE_Q),
                exec_price: 150,
                fee_bps: 0,
            },
            true,
        )
        .expect("the first risk-reducing close must remain available");
    assert_eq!(short.header.pnl.get(), -250);
    assert_eq!(short.header.capital.get(), 0);
    assert_eq!(
        short
            .header
            .close_progress
            .try_to_runtime()
            .unwrap()
            .residual_remaining,
        0
    );
}

#[test]
fn v16_trade_does_not_charge_prior_multi_asset_deficit_or_force_market_recovery() {
    const SIZE_Q: u128 = 10 * POS_SCALE;
    let (mut header, mut markets, mut long_header, mut short_header) =
        unattributed_deficit_fixture();
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    open_unattributed_deficit(&mut market, &mut long, &mut short);
    assert_eq!(
        short.header.liquidation_lock, 1,
        "detaching one leg from an uncovered multi-asset deficit must retain its unattributed-loss marker"
    );

    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 1,
                size_q: -signed_q(SIZE_Q),
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .expect("the final risk-reducing close must remain available");
    assert!(active_bitmap_is_empty(
        short.header.active_bitmap.map(V16PodU64::get)
    ));
    // sticky: the last leg detaching does not clear an unattributed deficit
    assert_eq!(short.header.liquidation_lock, 1);
    let ledger = short.header.close_progress.try_to_runtime().unwrap();
    assert_eq!(ledger.residual_remaining, 0);
    assert!(
        !market
            .build_actionable_summary(&short.as_view())
            .unwrap()
            .recovery_eligible,
        "an unattributed account must not gain authority to recover the whole market"
    );
    // no asset domain was charged and no market-wide recovery was declared
    assert_eq!(market.header.mode, 0);
    assert_eq!(market.header.insurance.get(), 0);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();

    // upstream 228d9b3f: explicit market resolution winds the unattributed debt
    // down inside the resolved close itself (no domain guessing, no recovery).
    market
        .resolve_market_not_atomic(market.header.current_slot.get())
        .expect("explicit market resolution handles unattributed terminal debt");
    let loser_close = market
        .close_resolved_account_not_atomic(&mut short, 0)
        .expect("resolved settlement clears unattributed negative PnL without domain guessing");
    assert!(matches!(
        loser_close,
        percolator::ResolvedCloseOutcomeV16::Closed { payout: 0 }
    ));
    assert_eq!(short.header.pnl.get(), 0);
    assert_eq!(short.header.liquidation_lock, 0);
    assert_eq!(market.header.bankruptcy_hlock_active, 1);
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

#[test]
fn v16_liquidation_of_unattributed_deficit_reduces_risk_without_charging_the_surviving_domain() {
    let (mut header, mut markets, mut long_header, mut short_header) =
        unattributed_deficit_fixture();
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    open_unattributed_deficit(&mut market, &mut long, &mut short);

    let insurance_before = market.header.insurance.get();
    let asset1_before = markets_snapshot(&market, 1);
    let outcome = market
        .liquidate_account_not_atomic(&mut short, LiquidationRequestV16 { asset_index: 1 })
        .expect("a locked account still liquidates, reduce-only");
    // NEGATIVE CONTROL for 6d8e0a48: without the lock this liquidation charges the
    // asset-0 loss to asset 1 (residual booked / fee charged against the surviving
    // domain). With it, only risk is removed.
    assert!(outcome.closed_q > 0);
    assert_eq!(outcome.insurance_used, 0);
    assert_eq!(outcome.residual_booked, 0);
    assert_eq!(outcome.explicit_loss, 0);
    assert_eq!(outcome.fee_charged, 0);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(market.header.mode, 0, "no market recovery declared");
    assert_eq!(short.header.liquidation_lock, 1);
    assert_eq!(short.header.pnl.get(), -250);
    let asset1_after = markets_snapshot(&market, 1);
    assert_eq!(
        asset1_after.close_ledger_side_1_touched, false,
        "no close ledger was begun against the surviving asset"
    );
    assert!(
        asset1_after.oi_eff_short_q < asset1_before.oi_eff_short_q,
        "risk on the surviving asset was reduced"
    );
    market.validate_shape().unwrap();
    long.validate_with_market(&market.as_view()).unwrap();
    short.validate_with_market(&market.as_view()).unwrap();
}

struct AssetSnapshot {
    oi_eff_short_q: u128,
    close_ledger_side_1_touched: bool,
}

fn markets_snapshot(market: &MarketGroupV16ViewMut<'_, u64>, asset_index: usize) -> AssetSnapshot {
    let asset = market.markets[asset_index]
        .engine
        .asset
        .try_to_runtime()
        .unwrap();
    AssetSnapshot {
        oi_eff_short_q: asset.oi_eff_short_q,
        close_ledger_side_1_touched: asset.social_loss_dust_long_num != 0
            || asset.social_loss_dust_short_num != 0
            || asset.b_long_num != 0
            || asset.b_short_num != 0,
    }
}

// upstream 76a86f48 [BLOCKER LoF] "Recredit claim-free terminal overlap", a87c9a5b "Retire
// terminal unbudgeted insurance safely", 545e0224 "Fix terminal backing expiry cleanup",
// af7b4d2a "Bound terminal cleanup discovery cost", 6f3c5c12 "Prove terminal scan cursor
// progress": the bounded terminal close-slab entries and their claim-free recredit.
#[test]
fn v16_terminal_unbudgeted_insurance_retirement_is_claim_free_and_exact() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    header.insurance = V16PodU128::new(10);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Err(V16Error::LockActive),
        "live insurance cannot be retired"
    );
    market.resolve_market_not_atomic(1).unwrap();
    market
        .credit_domain_insurance_budget_not_atomic(0, 1)
        .unwrap();
    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Err(V16Error::LockActive),
        "a remaining domain claim protects the whole terminal pool"
    );
    market.withdraw_domain_insurance_not_atomic(0, 1).unwrap();

    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Ok(9)
    );
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_terminal_retirement_includes_claim_free_protocol_surplus() {
    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(10);
    header.insurance = V16PodU128::new(3);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(1).unwrap();

    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Ok(10)
    );
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_terminal_slab_progress_expires_one_domain_before_retiring_residual() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .deposit_fresh_counterparty_backing_not_atomic(0, 10, 5)
        .unwrap();
    market.resolve_market_not_atomic(1).unwrap();

    assert_eq!(
        market.advance_terminal_slab_not_atomic(5, 0, 0),
        Ok(TerminalSlabOutcomeV16::BackingExpired { domain: 0 })
    );
    assert_eq!(market.header.current_slot.get(), 5);
    assert_eq!(market.header.vault.get(), 10);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.header.source_fresh_backing_total_num.get(), 0);
    assert_eq!(
        market.markets[0]
            .engine
            .backing_long
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Expired
    );

    assert_eq!(
        market.advance_terminal_slab_not_atomic(5, 0, 0),
        Ok(TerminalSlabOutcomeV16::ReadyToClose { retired: 10 })
    );
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_terminal_slab_progress_restores_insurance_before_retiring_surplus() {
    const RESIDUAL: u128 = 750;
    const SPENT: u128 = 123;
    const RECEIVABLE: u128 = 776;
    const ASSET: usize = 2;

    let (mut header, mut markets) = market_fixture(3, 100);
    let market_id = markets[ASSET].engine.asset.market_id.get();
    header.vault = V16PodU128::new(RESIDUAL);
    markets[ASSET].engine.insurance_domain_budget_long = V16PodU128::new(SPENT);
    markets[ASSET].engine.insurance_domain_spent_long = V16PodU128::new(SPENT);
    markets[ASSET].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: RECEIVABLE * BOUND_SCALE,
            provider_receivable_num: RECEIVABLE * BOUND_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[ASSET].engine.backing_short =
        BackingBucketV16Account::from_runtime(&BackingBucketV16 {
            market_id,
            consumed_liened_backing_num: RECEIVABLE * BOUND_SCALE,
            status: BackingBucketStatusV16::Expired,
            ..BackingBucketV16::EMPTY
        });
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(3).unwrap();

    assert_eq!(
        market.advance_terminal_slab_not_atomic(3, 0, 0),
        Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
            asset_index: ASSET,
            amount: SPENT,
        })
    );
    assert_eq!(market.header.vault.get(), RESIDUAL);
    assert_eq!(market.header.insurance.get(), SPENT);
    assert_eq!(
        market.header.insurance_domain_budget_remaining_total.get(),
        SPENT
    );
    assert_eq!(
        market.markets[ASSET]
            .engine
            .insurance_domain_spent_long
            .get(),
        0
    );
    assert_eq!(
        market.advance_terminal_slab_not_atomic(3, 0, 0),
        Err(V16Error::LockActive),
        "restored domain insurance must be withdrawn before final retirement"
    );

    market
        .withdraw_domain_insurance_not_atomic(ASSET * 2, SPENT)
        .unwrap();
    assert_eq!(market.header.vault.get(), RESIDUAL - SPENT);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(
        market.advance_terminal_slab_not_atomic(3, 0, 0),
        Ok(TerminalSlabOutcomeV16::ReadyToClose {
            retired: RESIDUAL - SPENT,
        })
    );
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_terminal_retirement_refuses_to_burn_a_pending_insurance_recredit() {
    // Coverage for the `first_terminal_claim_free_recredit_asset` gate that
    // upstream 545e0224 added to `retire_terminal_unbudgeted_insurance_not_atomic`.
    // Upstream shipped this gate with no direct-entry test: every upstream case
    // reaches the equivalent state through `advance_terminal_slab_not_atomic`,
    // which RECREDITS instead of erroring, so the gate never fires under the
    // upstream suite. Without it the direct entry burns the whole vault,
    // including the `SPENT` atoms still owed back to the paired insurance
    // domain (and from there to the counterparty backing provider).
    const RESIDUAL: u128 = 750;
    const SPENT: u128 = 123;
    const RECEIVABLE: u128 = 776;
    const ASSET: usize = 2;

    let (mut header, mut markets) = market_fixture(3, 100);
    let market_id = markets[ASSET].engine.asset.market_id.get();
    header.vault = V16PodU128::new(RESIDUAL);
    markets[ASSET].engine.insurance_domain_budget_long = V16PodU128::new(SPENT);
    markets[ASSET].engine.insurance_domain_spent_long = V16PodU128::new(SPENT);
    markets[ASSET].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: RECEIVABLE * BOUND_SCALE,
            provider_receivable_num: RECEIVABLE * BOUND_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[ASSET].engine.backing_short =
        BackingBucketV16Account::from_runtime(&BackingBucketV16 {
            market_id,
            consumed_liened_backing_num: RECEIVABLE * BOUND_SCALE,
            status: BackingBucketStatusV16::Expired,
            ..BackingBucketV16::EMPTY
        });
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(3).unwrap();

    // The two earlier gates do not dominate: no fresh backing and no provider
    // earnings remain, so only the recredit gate can refuse this state.
    assert_eq!(market.header.source_fresh_backing_total_num.get(), 0);
    assert_eq!(market.header.backing_provider_earnings_total.get(), 0);

    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Err(V16Error::LockActive),
        "a pending claim-free recredit must block direct terminal retirement"
    );
    assert_eq!(market.header.vault.get(), RESIDUAL);
    assert_eq!(market.header.insurance.get(), 0);

    // The bounded crank is the only way forward, and it recredits rather than burns.
    assert_eq!(
        market.advance_terminal_slab_not_atomic(3, 0, 0),
        Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
            asset_index: ASSET,
            amount: SPENT,
        })
    );
    assert_eq!(market.header.insurance.get(), SPENT);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_terminal_slab_chunk_cursor_finds_last_asset_recredit_before_retirement() {
    const ASSETS: u32 = percolator::TERMINAL_SLAB_SCAN_ASSETS_PER_CALL as u32 + 1;
    const ASSET: usize = ASSETS as usize - 1;
    const RESIDUAL: u128 = 10;
    const SPENT: u128 = 3;
    const RECEIVABLE: u128 = 7;
    const SLOT: u64 = ASSETS as u64 + 1;

    let (mut header, mut markets) = market_fixture(ASSETS, 100);
    let market_id = markets[ASSET].engine.asset.market_id.get();
    header.vault = V16PodU128::new(RESIDUAL);
    markets[ASSET].engine.insurance_domain_budget_long = V16PodU128::new(SPENT);
    markets[ASSET].engine.insurance_domain_spent_long = V16PodU128::new(SPENT);
    markets[ASSET].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: RECEIVABLE * BOUND_SCALE,
            provider_receivable_num: RECEIVABLE * BOUND_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[ASSET].engine.backing_short =
        BackingBucketV16Account::from_runtime(&BackingBucketV16 {
            market_id,
            consumed_liened_backing_num: RECEIVABLE * BOUND_SCALE,
            status: BackingBucketStatusV16::Expired,
            ..BackingBucketV16::EMPTY
        });
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(SLOT).unwrap();

    assert_eq!(
        market.advance_terminal_slab_not_atomic(SLOT, 0, 0),
        Ok(TerminalSlabOutcomeV16::ScanProgress {
            next_asset_index: percolator::TERMINAL_SLAB_SCAN_ASSETS_PER_CALL,
        })
    );
    assert_eq!(
        (market.header.vault.get(), market.header.insurance.get()),
        (RESIDUAL, 0),
        "a scan-only step cannot reclassify terminal value"
    );
    assert_eq!(
        market.advance_terminal_slab_not_atomic(
            SLOT + 1,
            percolator::TERMINAL_SLAB_SCAN_ASSETS_PER_CALL,
            0,
        ),
        Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
            asset_index: ASSET,
            amount: SPENT,
        }),
        "the persisted continuation cannot skip a candidate in the last chunk"
    );
    assert_eq!(
        (market.header.vault.get(), market.header.insurance.get()),
        (RESIDUAL, SPENT)
    );
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_terminal_slab_cursor_stops_at_unexpired_backing_across_slots() {
    const ASSETS: u32 = percolator::TERMINAL_SLAB_SCAN_ASSETS_PER_CALL as u32 + 1;
    const BLOCKING_ASSET: usize = 100;
    const SLOT: u64 = ASSETS as u64 + 1;
    const EXPIRY: u64 = SLOT + 2;

    let (mut header, mut markets) = market_fixture(ASSETS, 100);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market
        .deposit_fresh_counterparty_backing_not_atomic(BLOCKING_ASSET * 2, 7, EXPIRY)
        .unwrap();
    market.resolve_market_not_atomic(SLOT).unwrap();

    assert_eq!(
        market.advance_terminal_slab_not_atomic(SLOT, 0, 0),
        Ok(TerminalSlabOutcomeV16::ScanProgress {
            next_asset_index: BLOCKING_ASSET,
        }),
        "the scan may advance up to, but never past, a still-live bucket"
    );
    assert_eq!(
        market.advance_terminal_slab_not_atomic(SLOT + 1, BLOCKING_ASSET, 0),
        Err(V16Error::LockActive),
        "a parked cursor cannot report a successful no-op before expiry"
    );
    assert_eq!(
        market.advance_terminal_slab_not_atomic(EXPIRY, BLOCKING_ASSET, 0),
        Ok(TerminalSlabOutcomeV16::BackingExpired {
            domain: BLOCKING_ASSET * 2,
        }),
        "authenticated time makes the parked bucket actionable without restarting the prefix"
    );
    assert_eq!(market.header.source_fresh_backing_total_num.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

// Fork protocol-fee RESERVE amendment: unwithdrawn protocol fees sit inside
// header.insurance and the wrapper passes the protocol's claim as
// additional_reserved. Terminal retirement must refuse to burn it and leave the
// market untouched; once the fee leaves through the surplus-withdraw path the
// same market retires to empty with a zero reserve.
#[test]
fn v16_terminal_retirement_refuses_unwithdrawn_protocol_fee_reserve() {
    const INSURANCE: u128 = 10;
    const PROTOCOL_FEE: u128 = 4;

    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(INSURANCE);
    header.insurance = V16PodU128::new(INSURANCE);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(1).unwrap();
    let header_before = *market.header;
    let markets_before = market.markets.to_vec();

    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(PROTOCOL_FEE),
        Err(V16Error::LockActive),
        "terminal retirement must not burn an unwithdrawn protocol fee"
    );
    assert_eq!(
        *market.header, header_before,
        "a refused retirement must leave the header untouched"
    );
    assert_eq!(market.markets, &markets_before[..]);
    assert_eq!(
        (market.header.vault.get(), market.header.insurance.get()),
        (INSURANCE, INSURANCE)
    );

    market
        .withdraw_insurance_surplus_not_atomic(PROTOCOL_FEE)
        .unwrap();
    assert_eq!(market.header.vault.get(), INSURANCE - PROTOCOL_FEE);
    assert_eq!(market.header.insurance.get(), INSURANCE - PROTOCOL_FEE);

    assert_eq!(
        market.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Ok(INSURANCE - PROTOCOL_FEE)
    );
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

// The bounded close slab reaches the same retirement through ReadyToClose and
// must refuse it identically while the protocol fee is still reserved.
#[test]
fn v16_terminal_slab_close_refuses_unwithdrawn_protocol_fee_reserve() {
    const INSURANCE: u128 = 10;
    const PROTOCOL_FEE: u128 = 4;

    let (mut header, mut markets) = market_fixture(1, 100);
    header.vault = V16PodU128::new(INSURANCE);
    header.insurance = V16PodU128::new(INSURANCE);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    market.resolve_market_not_atomic(1).unwrap();
    let slot = market.header.current_slot.get();
    let header_before = *market.header;
    let markets_before = market.markets.to_vec();

    assert_eq!(
        market.advance_terminal_slab_not_atomic(slot, 0, PROTOCOL_FEE),
        Err(V16Error::LockActive),
        "the close slab must not reach ReadyToClose over an unwithdrawn protocol fee"
    );
    assert_eq!(
        *market.header, header_before,
        "a refused close step must leave the header untouched"
    );
    assert_eq!(market.markets, &markets_before[..]);

    market
        .withdraw_insurance_surplus_not_atomic(PROTOCOL_FEE)
        .unwrap();
    assert_eq!(
        market.advance_terminal_slab_not_atomic(slot, 0, 0),
        Ok(TerminalSlabOutcomeV16::ReadyToClose {
            retired: INSURANCE - PROTOCOL_FEE,
        })
    );
    assert_eq!(market.header.vault.get(), 0);
    assert_eq!(market.header.insurance.get(), 0);
    assert_eq!(market.validate_shape(), Ok(()));
}

#[test]
fn v16_auto_crank_expires_one_lapsed_live_source_domain_per_step() {
    let (mut header, mut markets) = market_fixture(2, 100);
    let mut account_header = account_fixture(2, 22);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        market.deposit_not_atomic(&mut account, 100).unwrap();
        market
            .deposit_fresh_counterparty_backing_not_atomic(1, 40, 5)
            .unwrap();
        market
            .deposit_fresh_counterparty_backing_not_atomic(3, 40, 5)
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut account, 1, 40)
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut account, 3, 40)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(0, 10, 100, 0, true)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(1, 10, 100, 0, true)
            .unwrap();
    }

    let before = markets[0].engine.backing_short.try_to_runtime().unwrap();
    assert_eq!(before.status, BackingBucketStatusV16::Fresh);
    assert_eq!(before.expiry_slot, 5);
    assert_eq!(
        markets[1]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh
    );
    assert!(header.current_slot.get() > before.expiry_slot);
    let vault_before = header.vault.get();
    let c_tot_before = header.c_tot.get();
    let insurance_before = header.insurance.get();
    let earnings_before = header.backing_provider_earnings_total.get();
    let source_backing_before = header.source_fresh_backing_total_num.get();
    let risk_epoch_before = header.risk_epoch.get();

    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut account = PortfolioV16ViewMut::new(&mut account_header);
    let observations = [AutoCrankObservationV16 {
        asset_index: 0,
        effective_price: 100,
        funding_rate_e9: 0,
    }];
    let expiry = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &observations,
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("Live auto-crank must expire lapsed backing instead of returning Stale");

    assert!(matches!(
        expiry.selected,
        AutoCrankPlanV16::RefreshAccount { .. }
    ));
    assert_eq!(
        expiry.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::SourceBackingExpired {
            domain: 1
        })
    );
    let after = market.markets[0]
        .engine
        .backing_short
        .try_to_runtime()
        .unwrap();
    assert_eq!(after.status, BackingBucketStatusV16::Expired);
    assert_eq!(after.fresh_unliened_backing_num, 0);
    assert_eq!(
        market.markets[1]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Fresh,
        "one auto-crank expires exactly one source domain"
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.backing_provider_earnings_total.get(),
        earnings_before
    );
    assert_eq!(
        market.header.source_fresh_backing_total_num.get(),
        source_backing_before - 40 * BOUND_SCALE
    );
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 1);
    assert_eq!(account.header.capital.get(), 100);
    assert_eq!(account.header.pnl.get(), 80);
    assert!(!account.header.health_cert.try_to_runtime().unwrap().valid);

    let second_expiry = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &observations,
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the next bounded auto-crank must expire the next domain");
    assert_eq!(
        second_expiry.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::SourceBackingExpired {
            domain: 3
        })
    );
    assert_eq!(
        market.markets[1]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap()
            .status,
        BackingBucketStatusV16::Expired
    );
    assert_eq!(market.header.vault.get(), vault_before);
    assert_eq!(market.header.c_tot.get(), c_tot_before);
    assert_eq!(market.header.insurance.get(), insurance_before);
    assert_eq!(
        market.header.backing_provider_earnings_total.get(),
        earnings_before
    );
    assert_eq!(market.header.source_fresh_backing_total_num.get(), 0);
    assert_eq!(market.header.risk_epoch.get(), risk_epoch_before + 2);

    let refresh = market
        .permissionless_auto_crank_not_atomic(
            &mut account,
            AutoCrankWorkV16 {
                now_slot: 10,
                observations: &observations,
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("the final bounded auto-crank must finish account refresh");
    assert_eq!(
        refresh.outcome,
        AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
    );
    assert!(account.header.health_cert.try_to_runtime().unwrap().valid);
    market.validate_shape().unwrap();
    account.validate_with_market(&market.as_view()).unwrap();
}

/// upstream 0e773c77 + 867fbdc9: the sibling test above never certifies the
/// account, so its cert is stale and `stale` is already set by `!cert_current`.
/// Here the account IS certified and no epoch moves, which is exactly the case
/// the classifier used to miss: clock-driven backing expiry must be its own
/// classifier input.
///
/// 867fbdc9 sharpened this from "expiry is a classifier input" to "expiry is
/// classified at the AUTHENTICATED slot": the committed market slot stays BEFORE
/// the bucket's expiry, so `build_actionable_summary` (committed clock) must
/// report `!stale` while `build_actionable_summary_at_slot(.., 10)` reports
/// `stale` — with no observation supplied and no mutation of the market clock.
/// The pre-867fbdc9 form advanced the committed slot past expiry with an
/// `accrue_asset_to_not_atomic` hint, so it passed identically whether the
/// classifier read `now_slot` or `self.header.current_slot`; the open leg added
/// here is what forces the first crank to be a clock catch-up (Refresh accrues
/// the leg's asset to `now_slot`) and the second to be the actual expiry.
#[test]
fn v16_auto_crank_classifies_lapsed_source_backing_with_current_certificate() {
    let (mut header, mut markets) = market_fixture(1, 100);
    let mut account_header = account_fixture(1, 23);
    let mut counterparty_header = account_fixture(1, 24);
    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        let mut counterparty = PortfolioV16ViewMut::new(&mut counterparty_header);
        market.deposit_not_atomic(&mut account, 10_000).unwrap();
        market
            .deposit_not_atomic(&mut counterparty, 10_000)
            .unwrap();
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut account,
                &mut counterparty,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: signed_q(POS_SCALE),
                    exec_price: 100,
                    fee_bps: 0,
                },
                // fork: taker-only fee needs the taker side; fee_bps is 0 here so
                // no fee is charged either way.
                true,
            )
            .unwrap();
        market
            .deposit_fresh_counterparty_backing_not_atomic(1, 40, 5)
            .unwrap();
        market
            .add_account_source_positive_pnl_not_atomic(&mut account, 1, 40)
            .unwrap();
        market
            .full_account_refresh_not_atomic(&mut account)
            .unwrap();
        assert!(account.header.health_cert.try_to_runtime().unwrap().valid);

        // The committed market slot remains before expiry and every certificate
        // epoch is current. Authenticated execution time must nevertheless make
        // the lapsed bucket actionable without an oracle hint.
        let cert = account.header.health_cert.try_to_runtime().unwrap();
        assert_eq!(cert.cert_oracle_epoch, market.header.oracle_epoch.get());
        assert_eq!(cert.cert_funding_epoch, market.header.funding_epoch.get());
        assert_eq!(cert.cert_risk_epoch, market.header.risk_epoch.get());
        assert_eq!(
            cert.cert_asset_set_epoch,
            market.header.asset_set_epoch.get()
        );
        let committed_before = market.header.current_slot.get();
        assert!(
            committed_before < 5,
            "fixture: the committed slot must sit BEFORE the bucket expiry, got {committed_before}"
        );

        assert!(
            !market
                .build_actionable_summary(&account.as_view())
                .unwrap()
                .stale
        );
        assert!(
            market
                .build_actionable_summary_at_slot(&account.as_view(), 10)
                .unwrap()
                .stale
        );
        assert_eq!(
            market.header.current_slot.get(),
            committed_before,
            "classification is pure: the committed clock must not move"
        );

        let catchup = market
            .permissionless_auto_crank_not_atomic(
                &mut account,
                AutoCrankWorkV16 {
                    now_slot: 10,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .unwrap();
        assert_eq!(
            catchup.outcome,
            AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
        );
        assert_eq!(market.header.current_slot.get(), 10);
        assert_eq!(
            market.markets[0]
                .engine
                .backing_short
                .try_to_runtime()
                .unwrap()
                .status,
            BackingBucketStatusV16::Fresh
        );

        let result = market
            .permissionless_auto_crank_not_atomic(
                &mut account,
                AutoCrankWorkV16 {
                    now_slot: 10,
                    observations: &[],
                    resolved_close_fee_rate_per_slot: 0,
                },
            )
            .unwrap();
        assert_eq!(
            result.outcome,
            AutoCrankOutcomeV16::Progressed(
                PermissionlessProgressOutcomeV16::SourceBackingExpired { domain: 1 }
            )
        );
        let bucket = market.markets[0]
            .engine
            .backing_short
            .try_to_runtime()
            .unwrap();
        assert_eq!(bucket.status, BackingBucketStatusV16::Expired);
        assert_eq!(bucket.fresh_unliened_backing_num, 0);
        assert_eq!(market.header.source_fresh_backing_total_num.get(), 0);
        assert_eq!(market.header.vault.get(), 20_040);
        assert_eq!(account.header.capital.get(), 10_000);
        assert_eq!(account.header.pnl.get(), 40);
        market.validate_shape().unwrap();
        account.validate_with_market(&market.as_view()).unwrap();
    }
}

/// Negative control for joining #172 (upstream 44847fd5) with #203's public crank:
/// upstream's only engine caller of `advance_resolved_slot_not_atomic` is the
/// CloseResolved arm of `permissionless_auto_crank_not_atomic`. Removing that call left
/// every resolved and auto-crank test green, so pin it: a CloseResolved step carries the
/// wrapper-authenticated slot into the resolved-settlement clock before closing, and
/// leaves the resolved slot itself untouched.
#[test]
fn v16_auto_crank_close_resolved_advances_the_resolved_settlement_clock() {
    const SIZE_Q: u128 = 10 * POS_SCALE;
    let (mut header, mut markets) = market_fixture(1, 100);
    header.config.maintenance_margin_bps = V16PodU64::new(1_000);
    header.config.initial_margin_bps = V16PodU64::new(1_000);
    header.config.max_price_move_bps_per_slot = V16PodU64::new(500);
    header.config.max_accrual_dt_slots = V16PodU64::new(1);
    header.config.min_funding_lifetime_slots = V16PodU64::new(1);
    let mut long_header = account_fixture(1, 45);
    let mut short_header = account_fixture(1, 46);
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut long = PortfolioV16ViewMut::new(&mut long_header);
    let mut short = PortfolioV16ViewMut::new(&mut short_header);
    market.deposit_not_atomic(&mut long, 1_000).unwrap();
    market.deposit_not_atomic(&mut short, 1_000).unwrap();
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
    market
        .set_asset_raw_oracle_target_not_atomic(0, 105)
        .unwrap();
    market
        .accrue_asset_to_not_atomic(0, 2, 105, 0, true)
        .unwrap();
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: -signed_q(SIZE_Q),
                exec_price: 105,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    assert!(
        long.header.pnl.get() > 0,
        "fixture: the long must hold realized profit"
    );
    let resolved_slot = market.header.current_slot.get();
    market.resolve_market_not_atomic(resolved_slot).unwrap();
    let mut short_closed = false;
    for _ in 0..4 {
        if let ResolvedCloseOutcomeV16::Closed { .. } = market
            .close_resolved_account_not_atomic(&mut short, 0)
            .unwrap()
        {
            short_closed = true;
            break;
        }
    }
    assert!(short_closed, "fixture: the losing account must close first");

    let authenticated_slot = resolved_slot + 7;
    let result = market
        .permissionless_auto_crank_not_atomic(
            &mut long,
            AutoCrankWorkV16 {
                now_slot: authenticated_slot,
                observations: &[],
                resolved_close_fee_rate_per_slot: 0,
            },
        )
        .expect("a payout-ready resolved winner must close through the public crank");
    assert_eq!(result.selected, AutoCrankPlanV16::CloseResolved);
    assert!(matches!(
        result.outcome,
        AutoCrankOutcomeV16::ResolvedClose(ResolvedCloseOutcomeV16::Closed { .. })
    ));
    assert_eq!(
        market.header.current_slot.get(),
        authenticated_slot,
        "CloseResolved must advance the resolved-settlement clock to the authenticated slot"
    );
    assert_eq!(market.header.resolved_slot.get(), resolved_slot);
    market.validate_shape().unwrap();
}
