// Regression tests for FIX-LOOP item I2 — `advance_terminal_slab_not_atomic`'s
// fall-through to `retire_terminal_unbudgeted_insurance_core_not_atomic` had no
// claim-free recredit gate, while the bounded scan only covers
// `[scan_start_asset_index, scan_start + TERMINAL_SLAB_SCAN_ASSETS_PER_CALL)`.
// With the continuation cursor above an asset that still owes a provider
// recredit, `ReadyToClose` emptied the vault while `insurance_domain_spent_*`
// and `provider_receivable_num` stayed nonzero — and `validate_shape()` stayed
// silent.
//
// Fixture and defect measurements ported from the VERIFY-LOOP PoCs
// `verify/poc/U-I/UI_VERIFIER_scan_start_skip.rs` (arbitrary cursor),
// `verify/poc/U-I2/UI2_VERIFIER_sanctioned_cursor_skip.rs` (the wrapper's OWN
// persisted `BackingExpired -> domain / 2` cursor) and `verify/poc/U-I/poc_U-I.rs`
// (the reaching `vault > insurance` fixture that first exposed the gate).
// Every assertion below asserts the FIXED behaviour: the crank rewinds the
// cursor via `ScanProgress` to the skipped asset and recredits it instead of
// burning the atoms owed to the paired insurance domain.
//
// The fixture helpers `ids` / `market_fixture` are copied from
// `tests/v16_spec_tests.rs`.

use percolator::BOUND_SCALE;
use percolator::{
    BackingBucketStatusV16, BackingBucketV16, BackingBucketV16Account, EngineAssetSlotV16Account,
    Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, SourceCreditStateV16,
    SourceCreditStateV16Account, TerminalSlabOutcomeV16, V16Config, V16Error, V16PodU128,
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

// ---------------------------------------------------------------------------
// (A) arbitrary cursor — `verify/poc/U-I/UI_VERIFIER_scan_start_skip.rs`
// ---------------------------------------------------------------------------

const RESIDUAL: u128 = 750;
const SPENT: u128 = 123;
const RECEIVABLE: u128 = 776;

/// `vault > insurance` (so `residual() != 0` and the recredit scan does not
/// short-circuit), a pending claim-free recredit of `SPENT` atoms on `asset`,
/// and BOTH dominating gates (`backing_provider_earnings_total`,
/// `source_fresh_backing_total_num`) equal to zero.
fn reaching_fixture(asset: usize) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (mut header, mut markets) = market_fixture(3, 100);
    let market_id = markets[asset].engine.asset.market_id.get();
    header.vault = V16PodU128::new(RESIDUAL);
    markets[asset].engine.insurance_domain_budget_long = V16PodU128::new(SPENT);
    markets[asset].engine.insurance_domain_spent_long = V16PodU128::new(SPENT);
    markets[asset].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: RECEIVABLE * BOUND_SCALE,
            provider_receivable_num: RECEIVABLE * BOUND_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[asset].engine.backing_short =
        BackingBucketV16Account::from_runtime(&BackingBucketV16 {
            market_id,
            consumed_liened_backing_num: RECEIVABLE * BOUND_SCALE,
            status: BackingBucketStatusV16::Expired,
            ..BackingBucketV16::EMPTY
        });
    (header, markets)
}

/// THE I2 DEFECT, re-asserted for the fixed behaviour. Before the fix
/// `advance_terminal_slab_not_atomic(3, 1, 0)` returned
/// `ReadyToClose { retired: 750 }` — asset 0 sits below the cursor, is never
/// inspected, and its owed `SPENT` atoms are burned with the vault. The fix
/// rewinds the cursor to the skipped asset instead.
#[test]
fn i2_cursor_above_a_pending_recredit_rewinds_instead_of_burning() {
    let (mut h, mut m) = reaching_fixture(0);
    let mut c = MarketGroupV16ViewMut::new(&mut h, &mut m);
    c.resolve_market_not_atomic(3).unwrap();
    assert_eq!(c.header.vault.get(), RESIDUAL);

    let skipped = c.advance_terminal_slab_not_atomic(3, 1, 0);
    assert_eq!(
        skipped,
        Ok(TerminalSlabOutcomeV16::ScanProgress {
            next_asset_index: 0
        }),
        "a cursor above a pending claim-free recredit must rewind, not retire"
    );
    // The pre-fix outcome, spelled out so the regression cannot be read as vacuous.
    assert_ne!(
        skipped,
        Ok(TerminalSlabOutcomeV16::ReadyToClose { retired: RESIDUAL }),
        "pre-fix this call retired the whole vault"
    );

    // Nothing was burned.
    assert_eq!(c.header.vault.get(), RESIDUAL);
    assert_eq!(c.header.insurance.get(), 0);
    assert_eq!(c.markets[0].engine.insurance_domain_spent_long.get(), SPENT);
    assert_eq!(c.validate_shape(), Ok(()));

    // And the rewound cursor makes progress: the next call recredits the atoms.
    assert_eq!(
        c.advance_terminal_slab_not_atomic(3, 0, 0),
        Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
            asset_index: 0,
            amount: SPENT,
        }),
    );
    assert_eq!(c.header.insurance.get(), SPENT);
    assert_eq!(c.markets[0].engine.insurance_domain_spent_long.get(), 0);
    assert_eq!(c.validate_shape(), Ok(()));
}

/// Every accepted cursor above the pending recredit rewinds; the bounds check on
/// `scan_start_asset_index` is unchanged.
#[test]
fn i2_every_cursor_above_the_pending_recredit_rewinds() {
    for cursor in 1..3usize {
        let (mut h, mut m) = reaching_fixture(0);
        let mut c = MarketGroupV16ViewMut::new(&mut h, &mut m);
        c.resolve_market_not_atomic(3).unwrap();
        assert_eq!(
            c.advance_terminal_slab_not_atomic(3, cursor, 0),
            Ok(TerminalSlabOutcomeV16::ScanProgress {
                next_asset_index: 0
            }),
            "cursor {cursor} must rewind"
        );
        assert_eq!(c.header.vault.get(), RESIDUAL, "cursor {cursor} burned");
    }
    let (mut h, mut m) = reaching_fixture(0);
    let mut c = MarketGroupV16ViewMut::new(&mut h, &mut m);
    c.resolve_market_not_atomic(3).unwrap();
    assert_eq!(
        c.advance_terminal_slab_not_atomic(3, 3, 0),
        Err(V16Error::InvalidConfig),
        "the configured-assets bound is unchanged"
    );
}

/// U-I's own reaching fixture (the recreditable asset at index 2): the direct
/// entry's gate still refuses, and the crank from cursor 0 still recredits. This
/// is the control that the fix did not disturb the path that already worked.
#[test]
fn i2_reaching_fixture_direct_entry_still_refuses_and_crank_recredits() {
    let (mut h, mut m) = reaching_fixture(2);
    let mut c = MarketGroupV16ViewMut::new(&mut h, &mut m);
    c.resolve_market_not_atomic(3).unwrap();

    // Neither dominating gate can be doing the work.
    assert_eq!(c.header.source_fresh_backing_total_num.get(), 0);
    assert_eq!(c.header.backing_provider_earnings_total.get(), 0);
    assert!(c.header.vault.get() > c.header.insurance.get());

    assert_eq!(
        c.retire_terminal_unbudgeted_insurance_not_atomic(0),
        Err(V16Error::LockActive),
        "a pending claim-free recredit must block direct terminal retirement"
    );
    assert_eq!(c.header.vault.get(), RESIDUAL);

    assert_eq!(
        c.advance_terminal_slab_not_atomic(3, 0, 0),
        Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
            asset_index: 2,
            amount: SPENT,
        }),
    );
    assert_eq!(c.header.insurance.get(), SPENT);
    assert_eq!(c.validate_shape(), Ok(()));
}

// ---------------------------------------------------------------------------
// (B) the wrapper's OWN persisted cursor —
//     `verify/poc/U-I2/UI2_VERIFIER_sanctioned_cursor_skip.rs`
// ---------------------------------------------------------------------------

const SPENT2: u128 = 3;
const RECEIVABLE2: u128 = 7;
const BACKING: u128 = 10;
const EXPIRY: u64 = 5;

/// Asset 0 carries a pending claim-free recredit; asset 1 (domain 2) holds a
/// Fresh backing bucket worth the whole vault, so `residual() == 0` and asset 0
/// is NOT yet recreditable on the first pass. Expiring that bucket makes
/// `residual` jump from 0 to positive — retroactively making the LOWER asset
/// recreditable — while the wrapper has just persisted the cursor at the higher
/// one (`BackingExpired { domain } -> domain / 2`).
fn sanctioned_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (mut header, mut markets) = market_fixture(3, 100);
    let market_id = markets[0].engine.asset.market_id.get();
    markets[0].engine.insurance_domain_budget_long = V16PodU128::new(SPENT2);
    markets[0].engine.insurance_domain_spent_long = V16PodU128::new(SPENT2);
    markets[0].engine.source_credit_short =
        SourceCreditStateV16Account::from_runtime(&SourceCreditStateV16 {
            spent_backing_num: RECEIVABLE2 * BOUND_SCALE,
            provider_receivable_num: RECEIVABLE2 * BOUND_SCALE,
            ..SourceCreditStateV16::EMPTY
        });
    markets[0].engine.backing_short = BackingBucketV16Account::from_runtime(&BackingBucketV16 {
        market_id,
        consumed_liened_backing_num: RECEIVABLE2 * BOUND_SCALE,
        status: BackingBucketStatusV16::Expired,
        ..BackingBucketV16::EMPTY
    });
    {
        let mut view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        view.deposit_fresh_counterparty_backing_not_atomic(2, BACKING, EXPIRY)
            .unwrap();
        view.resolve_market_not_atomic(3).unwrap();
    }
    (header, markets)
}

/// The sequence an honest wrapper runs, with no arbitrary input: the cursor it
/// persists after `BackingExpired { domain: 2 }` is `domain / 2 == 1`, which sits
/// above the asset the expiry just made recreditable. Pre-fix the next call
/// returned `ReadyToClose { retired: 10 }` and destroyed the owed atoms; now it
/// rewinds and the atoms are recredited before the market can close.
#[test]
fn i2_sanctioned_persisted_cursor_no_longer_burns_the_owed_recredit() {
    let (mut h, mut m) = sanctioned_fixture();
    let mut c = MarketGroupV16ViewMut::new(&mut h, &mut m);
    assert_eq!(c.header.vault.get(), BACKING);
    assert_eq!(
        c.markets[0].engine.insurance_domain_spent_long.get(),
        SPENT2
    );

    // CALL 1 from the wrapper's initial cursor 0.
    let r1 = c.advance_terminal_slab_not_atomic(EXPIRY, 0, 0);
    let cursor = match r1 {
        Ok(TerminalSlabOutcomeV16::BackingExpired { domain }) => domain / 2,
        other => panic!("expected BackingExpired, got {other:?}"),
    };
    assert_eq!(cursor, 1, "the wrapper persists the expired asset index");
    assert_eq!(c.header.source_fresh_backing_total_num.get(), 0);

    // CALL 2 with that SANCTIONED persisted cursor.
    let r2 = c.advance_terminal_slab_not_atomic(EXPIRY, cursor, 0);
    assert_eq!(
        r2,
        Ok(TerminalSlabOutcomeV16::ScanProgress {
            next_asset_index: 0
        }),
        "the sanctioned cursor must rewind to the asset the expiry made recreditable"
    );
    assert_ne!(
        r2,
        Ok(TerminalSlabOutcomeV16::ReadyToClose { retired: BACKING }),
        "pre-fix this call retired the vault and destroyed the owed atoms"
    );
    assert_eq!(c.header.vault.get(), BACKING, "nothing burned");
    assert_eq!(
        c.markets[0].engine.insurance_domain_spent_long.get(),
        SPENT2
    );

    // CALL 3 from the rewound cursor recredits, exactly as restarting from 0 did.
    assert_eq!(
        c.advance_terminal_slab_not_atomic(EXPIRY, 0, 0),
        Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
            asset_index: 0,
            amount: SPENT2,
        }),
    );
    assert_eq!(c.header.insurance.get(), SPENT2);
    assert_eq!(c.markets[0].engine.insurance_domain_spent_long.get(), 0);
    assert_eq!(c.validate_shape(), Ok(()));
}

/// Drives the wrapper's persisted-cursor protocol
/// (`upstream/main:src/v16_program.rs:11073-11096`) to a fixed point and reports
/// `(total recredited, final outcome, vault, insurance, asset0 paired spend)`.
fn drive(
    market: &mut MarketGroupV16ViewMut<'_, u64>,
    slot: u64,
    mut cursor: usize,
) -> (
    u128,
    Result<TerminalSlabOutcomeV16, V16Error>,
    u128,
    u128,
    u128,
) {
    let mut recredited = 0u128;
    for _ in 0..16 {
        let step = market.advance_terminal_slab_not_atomic(slot, cursor, 0);
        match step {
            Ok(TerminalSlabOutcomeV16::ScanProgress { next_asset_index }) => {
                cursor = next_asset_index
            }
            Ok(TerminalSlabOutcomeV16::BackingExpired { domain }) => cursor = domain / 2,
            Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
                asset_index,
                amount,
            }) => {
                recredited += amount;
                cursor = asset_index;
            }
            other => {
                return (
                    recredited,
                    other,
                    market.header.vault.get(),
                    market.header.insurance.get(),
                    market.markets[0].engine.insurance_domain_spent_long.get(),
                );
            }
        }
    }
    panic!("close sequence did not reach a fixed point in 16 steps");
}

/// Liveness: the rewind keeps the close sequence live. Driven from the
/// sanctioned cursor the protocol converges to EXACTLY the state it reaches when
/// restarted from 0 — same recredited total, same terminal outcome, same vault,
/// insurance and paired spend. A repeated `Err(LockActive)` gate would instead
/// pin `terminal_slab_scan_progress` at the higher asset and dead-end `CloseSlab`
/// with the atoms never recredited.
#[test]
fn i2_rewind_converges_to_the_restart_from_zero_state() {
    let (mut h1, mut m1) = sanctioned_fixture();
    let mut rewound = MarketGroupV16ViewMut::new(&mut h1, &mut m1);
    // first step from 0 expires the Fresh bucket, which is what persists cursor 1
    let first = rewound.advance_terminal_slab_not_atomic(EXPIRY, 0, 0);
    assert_eq!(
        first,
        Ok(TerminalSlabOutcomeV16::BackingExpired { domain: 2 })
    );
    let from_cursor = drive(&mut rewound, EXPIRY, 2 / 2);

    let (mut h2, mut m2) = sanctioned_fixture();
    let mut control = MarketGroupV16ViewMut::new(&mut h2, &mut m2);
    let from_zero = drive(&mut control, EXPIRY, 0);

    assert_eq!(
        from_cursor, from_zero,
        "the rewound cursor must converge to the restart-from-zero state"
    );
    assert_eq!(from_cursor.0, SPENT2, "the owed atoms are recredited");
    assert_eq!(from_cursor.4, 0, "the paired insurance spend is settled");
    assert_eq!(rewound.validate_shape(), Ok(()));
}

/// Same convergence claim on the arbitrary-cursor fixture: driving from cursor 1
/// recredits the skipped asset and lands on the same state as cursor 0.
#[test]
fn i2_rewind_converges_on_the_reaching_fixture_too() {
    let (mut h1, mut m1) = reaching_fixture(0);
    let mut rewound = MarketGroupV16ViewMut::new(&mut h1, &mut m1);
    rewound.resolve_market_not_atomic(3).unwrap();
    let from_cursor = drive(&mut rewound, 3, 1);

    let (mut h2, mut m2) = reaching_fixture(0);
    let mut control = MarketGroupV16ViewMut::new(&mut h2, &mut m2);
    control.resolve_market_not_atomic(3).unwrap();
    let from_zero = drive(&mut control, 3, 0);

    assert_eq!(from_cursor, from_zero);
    assert_eq!(from_cursor.0, SPENT, "the skipped asset is recredited");
    assert_eq!(
        from_cursor.2, RESIDUAL,
        "nothing was retired out of the vault"
    );
    assert_eq!(from_cursor.3, SPENT, "the atoms landed back in insurance");
    assert_eq!(from_cursor.4, 0);
}
