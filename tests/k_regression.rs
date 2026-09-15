// Regression tests for FIX-LOOP item K — the unchecked subtraction inside
// `PortfolioV16View::validate_with_market` (src/v16.rs:5077):
//
//     let source_attributed_pnl =
//         if decode_market_mode(market.header.mode)? == MarketModeV16::Resolved {
//             pnl.max(0) as u128 - self.header.reserved_pnl.get()
//         } else { ... };
//
// guarded thirteen lines earlier at src/v16.rs:5093 by
//     if self.header.reserved_pnl.get() > pnl.max(0) as u128 { return Err(InvalidLeg); }
// with `validate_fee_credits`, the `liquidation_lock` check, the
// `residual_spent_principal_atoms_total` check,
// `validate_source_credit_shape_with_market` and `source_claim_bound_sum_num()`
// in between.
//
// Wrapping that subtraction does not make the downstream check wrong, it makes
// it DISAPPEAR: `validate_positive_pnl_source_attribution` (src/v16.rs) opens
// with `if pnl <= 0 { return Ok(()); }`, so `u128::MAX as i128 == -1` returns
// `Ok(())` before `bound_num_from_amount` is ever computed, and the
// source-domain realizability cap stops being enforced for that input.
//
// Ported from the VERIFY-LOOP PoC `verify/poc/U-K/poc_U-K.rs`; fixture helpers
// from `tests/v16_spec_tests.rs`.

use percolator::{v16_domain_count_for_market_slots, BOUND_SCALE};
use percolator::{
    EngineAssetSlotV16Account, Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut,
    PortfolioAccountV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, SourceCreditStateV16, SourceCreditStateV16Account, V16Config,
    V16Error, V16PodI128, V16PodU128, V16PodU32, V16PodU64,
};

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

/// One asset, market in `Resolved` mode, an account carrying `pnl` quote atoms
/// of positive PnL, `reserved_pnl` reserved atoms, and one source domain whose
/// `source_claim_bound_num` is `claim_bound_atoms * BOUND_SCALE`.
///
/// `validate_positive_pnl_source_attribution` requires
/// `source_claim_bound_sum_num >= bound_num_from_amount(attributed_pnl)` —
/// i.e. `claim_bound_atoms >= attributed_pnl`.
fn run(pnl: i128, reserved_pnl: u128, claim_bound_atoms: u128) -> Result<(), V16Error> {
    let (mut header, mut markets) = market_fixture(1, 100);
    let asset_market_id = markets[0].engine.asset.market_id.get();
    markets[0].engine.source_credit_long =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            positive_claim_bound_num: claim_bound_atoms * BOUND_SCALE,
            exact_positive_claim_num: claim_bound_atoms * BOUND_SCALE,
            // fully backed, so `credit_rate_num` stays at CREDIT_RATE_SCALE and
            // `validate_source_credit_state_static` accepts the slot.
            fresh_reserved_backing_num: claim_bound_atoms * BOUND_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    header.mode = 1; // MarketModeV16::Resolved

    let mut account_header = account_fixture(1, 250);
    account_header.pnl = V16PodI128::new(pnl);
    account_header.reserved_pnl = V16PodU128::new(reserved_pnl);
    account_header.source_domains[0].domain = V16PodU32::new(0);
    account_header.source_domains[0].source_claim_market_id = V16PodU64::new(asset_market_id);
    account_header.source_domains[0].source_claim_bound_num =
        V16PodU128::new(claim_bound_atoms * BOUND_SCALE);

    let market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let account = PortfolioV16ViewMut::new(&mut account_header);
    account.validate_with_market(&market.as_view())
}

/// TRIANGULATION A — with `reserved_pnl = 0` the attribution check is live and
/// REFUSES: 2 atoms of positive PnL need 2 atoms of source-claim bound, only 1
/// is declared. Proves the check is discriminating, not vacuous.
#[test]
fn k_attribution_check_refuses_an_under_backed_positive_pnl() {
    assert_eq!(run(2, 0, 1), Err(V16Error::InvalidLeg));
}

/// TRIANGULATION B — the same shape with enough declared bound is accepted.
#[test]
fn k_attribution_check_accepts_a_fully_backed_positive_pnl() {
    assert_eq!(run(2, 0, 2), Ok(()));
}

/// THE ITEM, asserted as fail-closed rather than as a particular error.
/// `reserved_pnl = 3 > pnl.max(0) = 2` with only half the required source-claim
/// bound declared.
///
/// * today the dominating guard at src/v16.rs:5093 refuses -> `InvalidLeg`;
/// * if that guard and its use ever drift apart, `checked_sub(..)`
///   `.ok_or(CounterUnderflow)?` refuses -> `CounterUnderflow`;
/// * `Ok(())` would mean the subtraction wrapped and
///   `validate_positive_pnl_source_attribution` was handed a negative value, so
///   the source-domain realizability cap was silently not enforced. That is the
///   outcome this fix makes unreachable independently of the `overflow-checks`
///   profile setting.
#[test]
fn k_reserved_pnl_above_positive_pnl_fails_closed() {
    let result = run(2, 3, 1);
    assert_ne!(
        result,
        Ok(()),
        "the source-domain realizability cap must never be silently skipped"
    );
    assert!(
        matches!(
            result,
            Err(V16Error::InvalidLeg) | Err(V16Error::CounterUnderflow)
        ),
        "expected a conservative failure, got {result:?}"
    );
}

/// On the unmutated tree it is the guard at src/v16.rs:5093 that refuses, so the
/// `checked_sub` changes nothing on any reachable input. Pinning this keeps the
/// test above honest about which layer is doing the work today.
#[test]
fn k_the_dominating_guard_is_what_refuses_today() {
    assert_eq!(run(2, 3, 1), Err(V16Error::InvalidLeg));
}
