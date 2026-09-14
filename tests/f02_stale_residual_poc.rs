//! F-02 regression: a multi-chunk bankruptcy close must book the FRESH residual on
//! each chunk, not the figure captured when the close began.
//!
//! `book_bankruptcy_residual_chunk_for_account_core` opens a close ledger on its first
//! chunk, capturing `residual_remaining`. On a later chunk it previously booked that
//! captured `ledger.residual_remaining` again. Nothing lowers the ledger figure when
//! principal settles part of the debt between chunks (an owner deposit before a resolved
//! close, or a liquidation between Live chunks), so the loss-bearing side and insurance
//! were charged the pre-settlement residual while the account's own credit was clamped at
//! the true loss — the group is over-socialised.
//!
//! This drives that exact sequence via a fuzz/kani-gated shim: open the ledger with a
//! large residual (chunk 1), settle almost all of the debt, then book a second chunk
//! whose fresh residual is tiny. The fix books `residual_remaining.min(ledger.residual_remaining)`,
//! so the second chunk socialises at most the fresh residual. The pre-fix code booked a
//! full stale chunk, which this test rejects.
//!
//! Built with `--features fuzz` (the shim is gated to the proof/fuzz builds).
#![cfg(feature = "fuzz")]

use percolator::{
    EngineAssetSlotV16Account, Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut,
    PortfolioAccountV16Account, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, SideV16, TradeRequestV16, V16Config, V16PodI128, V16PodU128,
    POS_SCALE,
};

fn market_id() -> [u8; 32] {
    [7u8; 32]
}

fn new_account(seed: u8) -> PortfolioAccountV16Account {
    let header = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
        market_id(),
        [seed; 32],
        [seed; 32],
    ));
    let mut account = PortfolioAccountV16Account::default();
    account.init_empty_in_place(header).unwrap();
    account
}

fn activated_market() -> (MarketGroupV16HeaderAccount, [Market<u64>; 1]) {
    let cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id(), cfg, 1, 0).unwrap();
    let mut markets = [Market::new(0u64, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
        .unwrap();
    (header, markets)
}

#[test]
fn f02_second_chunk_books_fresh_residual_not_stale_ledger() {
    const CHUNK_CAP: u128 = 1_000_000;
    const OPENING_RESIDUAL: u128 = 3_000_000; // > CHUNK_CAP, so the ledger stays open
    const FRESH_RESIDUAL: u128 = 1_000; // the debt left after a mid-close settlement

    let (mut header, mut markets) = activated_market();
    let mut taker = new_account(91);
    let mut maker = new_account(92);

    // Matched positions so the winner (maker) side carries loss weight for the bankruptcy
    // booking to socialise against. Taker goes long, maker short.
    {
        let mut m = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut t = PortfolioV16ViewMut::new(&mut taker);
        let mut k = PortfolioV16ViewMut::new(&mut maker);
        m.deposit_not_atomic(&mut t, 1_000).unwrap();
        m.deposit_not_atomic(&mut k, 1_000).unwrap();
        m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut t,
            &mut k,
            TradeRequestV16 {
                asset_index: 0,
                size_q: POS_SCALE as i128,
                exec_price: 100,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    }

    // Cap a single chunk far below the opening residual so the close spans >1 chunk.
    header.config.public_b_chunk_atoms = V16PodU128::new(CHUNK_CAP);

    // Taker (long) is the bankrupt side; the loss-bearing side is short (the maker).
    let bankrupt_side = SideV16::Long;

    let mut m = MarketGroupV16ViewMut::new(&mut header, &mut markets);

    // CHUNK 1 — opens the close ledger capturing residual = OPENING_RESIDUAL and books one
    // capped chunk, leaving the ledger open with a large residual_remaining.
    {
        let mut t = PortfolioV16ViewMut::new(&mut taker);
        let (booked1, explicit1) = m
            .kani_book_bankruptcy_residual_chunk_for_account_core(
                &mut t,
                0,
                bankrupt_side,
                OPENING_RESIDUAL,
            )
            .expect("chunk 1 opens the ledger and books a chunk");
        assert!(
            booked1 + explicit1 > 0 && booked1 + explicit1 <= OPENING_RESIDUAL,
            "chunk 1 should book a bounded, non-zero amount (got {})",
            booked1 + explicit1
        );
    }

    // PRINCIPAL SETTLEMENT between chunks: an owner deposit (Live) or a liquidation cleared
    // almost all of the debt. Only FRESH_RESIDUAL of loss remains. The close ledger's
    // captured residual_remaining is NOT lowered by this.
    taker.pnl = V16PodI128::new(-(FRESH_RESIDUAL as i128));

    // CHUNK 2 — the caller recomputes the fresh residual from the account's current pnl.
    let (booked2, explicit2) = {
        let mut t = PortfolioV16ViewMut::new(&mut taker);
        m.kani_book_bankruptcy_residual_chunk_for_account_core(
            &mut t,
            0,
            bankrupt_side,
            FRESH_RESIDUAL,
        )
        .expect("chunk 2 books the remaining fresh residual")
    };

    // The fix books min(FRESH_RESIDUAL, ledger.residual_remaining) = FRESH_RESIDUAL, so the
    // second chunk socialises at most the fresh residual. The pre-fix code booked the stale
    // ledger figure (a full ~CHUNK_CAP chunk), over-socialising the loss onto the winner.
    let socialised = booked2 + explicit2;
    assert!(
        socialised <= FRESH_RESIDUAL,
        "F-02 regression: chunk 2 socialised {} but only {} of loss remained after settlement \
         — the stale ledger residual was booked instead of the fresh one",
        socialised,
        FRESH_RESIDUAL
    );
}
