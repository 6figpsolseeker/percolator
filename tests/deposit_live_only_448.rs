//! GH#448 — `deposit_not_atomic` must be LIVE-ONLY, per spec.md §1204.
//!
//! > `deposit(i, amount, now_slot)` is live-only, no-accrual, and may materialize
//! > missing `i` only if `amount > 0`.
//!
//! The function had no mode check at all — only `validate_with_market`, which
//! accepts an account carrying an active close ledger and negative pnl. #448 shows
//! what that permits: during a multi-chunk RESOLVED-mode bankruptcy close, a
//! mid-close deposit drives `pnl` back to >= 0 through principal settlement WITHOUT
//! advancing the close ledger, so the ledger stays active and non-finalized with
//! `residual_remaining > 0` and the domain-loss barrier is held forever. The domain
//! is then permanently bricked and `cure_and_cancel_close` refuses to help, because
//! a chunk has already been booked.
//!
//! PRODUCTION WAS NEVER EXPOSED, and the tests below pin the two facts that make
//! that true, so the claim does not rest on a reading of the wrapper today:
//! the engine's own close path requires Resolved, and deposit now requires Live.
//! A market is one or the other, so the windows cannot overlap. (The wrapper's
//! `handle_deposit` also rejects any non-Live market — belt and braces, and the
//! reason the deployed program was safe before this gate existed.)

use percolator::{
    v16_domain_count_for_market_slots, EngineAssetSlotV16Account, Market,
    MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PortfolioAccountV16Account,
    PortfolioV16View, PortfolioV16ViewMut, ProvenanceHeaderV16, ProvenanceHeaderV16Account,
    V16Config, V16Error,
};

const LIVE: u8 = 0;
const RESOLVED: u8 = 1;

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

/// Same shape as `tests/v16_spec_tests.rs::market_fixture`, with the mode byte
/// exposed — reused rather than reinvented so this suite cannot drift from the
/// fixture the spec tests use.
fn market_fixture(mode: u8) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0u64, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
        .unwrap();
    header.mode = mode;
    (header, markets)
}

fn account_fixture() -> PortfolioAccountV16Account {
    let (market_id, _, owner) = ids();
    let header = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
        market_id, [4; 32], owner,
    ));
    let _ = v16_domain_count_for_market_slots(1).unwrap();
    let mut account = PortfolioAccountV16Account::default();
    account.init_empty_in_place(header).unwrap();
    account
}

#[test]
fn deposit_is_accepted_while_live() {
    // POSITIVE CONTROL. Without it, the rejection below would pass against a
    // deposit that was broken for any reason at all.
    let (mut header, mut markets) = market_fixture(LIVE);
    let mut acct = account_fixture();

    let mut m = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut acct);
    m.deposit_not_atomic(&mut a, 1_000)
        .expect("a Live market must still accept deposits");

    assert_eq!(a.header.capital.get(), 1_000, "capital must have moved");
    assert_eq!(m.header.vault.get(), 1_000, "vault must have moved");
}

#[test]
fn deposit_is_refused_once_the_market_is_resolved() {
    // The #448 mechanism in one line: this is the call that used to succeed
    // mid-close and strand the ledger.
    let (mut header, mut markets) = market_fixture(RESOLVED);
    let mut acct = account_fixture();

    let mut m = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut acct);
    let err = m
        .deposit_not_atomic(&mut a, 1_000)
        .expect_err("spec.md §1204: deposit is live-only");
    assert_eq!(err, V16Error::LockActive);

    // And it must be a true no-op — a rejected deposit that had already moved
    // value would be worse than the bug.
    assert_eq!(a.header.capital.get(), 0, "capital must be untouched");
    assert_eq!(m.header.vault.get(), 0, "vault must be untouched");
}

#[test]
fn a_zero_amount_deposit_is_still_refused_when_not_live() {
    // The early `amount == 0` return sits AFTER the mode gate, deliberately. If it
    // came first, a caller could probe a non-Live market for a silent Ok — a small
    // thing, but it would make the mode invariant conditional on the amount.
    let (mut header, mut markets) = market_fixture(RESOLVED);
    let mut acct = account_fixture();

    let mut m = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut acct);
    assert_eq!(
        m.deposit_not_atomic(&mut a, 0).expect_err("still not Live"),
        V16Error::LockActive
    );
}

#[test]
fn the_close_path_requires_resolved_so_the_windows_cannot_overlap() {
    // This is the fact that makes "production was never exposed" true rather than
    // asserted. `close_resolved_account_not_atomic` refuses a Live market; deposit
    // now refuses a Resolved one. There is no mode in which both are reachable.
    let (mut header, mut markets) = market_fixture(LIVE);
    let mut acct = account_fixture();

    let mut m = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut a = PortfolioV16ViewMut::new(&mut acct);
    let err = m
        .close_resolved_account_not_atomic(&mut a, 0)
        .expect_err("the resolved-close path must refuse a Live market");
    assert_eq!(err, V16Error::LockActive);
}
