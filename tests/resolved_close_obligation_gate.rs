//! REGRESSION — a Recovery pending-obligation must not be released by resolved close
//! while the opposite side still holds real (non-obligation) positions.
//!
//! `detach_solvent_active_legs_for_resolved_close` (`e8715152:src/v16.rs:21059`) guards its
//! per-leg detach on `has_pending_domain_loss_barrier` alone (`:21087-21089`). A leg with
//! `basis_pos_q == 0` and `loss_weight != 0` — a pending loss obligation parked by
//! `kernel_retain_leg_as_pending_obligation` (`:1287`) — has
//! `effective_abs_quantity_for_leg` (`:1695`) == 0, so it takes the `close_q == 0` branch at
//! `:21126` and is detached through `clear_leg_at_slot_inner(.., Some(0))` (`:21130`, fn at
//! `:16891`). `kernel_clear_leg` (`:1412`) then runs its `basis_pos_q == 0 && loss_weight != 0`
//! arm (`:1461` long / `:1487` short) and decrements `pending_obligation_count_<side>`, and —
//! because the leg is not prior-reset — subtracts `leg.loss_weight` from
//! `loss_weight_sum_<side>` (`:1476` / `:1502`). The obligor escapes its share of the next
//! socialized loss; the surviving same-side obligors absorb it.
//!
//! The fork already gates this exact release in the two sibling paths — auto-crank plan selection
//! (`:15325-15334`) and `retain_recovery_loss_weight_before_detach` (`:16855-16865`) — both
//! through `recovery_pending_obligation_release_allowed` (`:16802`, kernel `:1329-1339`).
//! Resolved close was the one site that did not. Upstream closes it in hunk (d) of
//! `aeyakovenko/percolator` `94979ede`.
//!
//! REACHABILITY: `resolve_market_not_atomic` (`:20529-20542`) flips the group to `Resolved` and
//! never touches per-asset lifecycle, so an asset left in `Recovery` by
//! `force_asset_recovery_not_atomic` (`:14682`) stays `Recovery` inside a `Resolved` market.
//! Every step below is a public engine entry; wrapper tags are named where they exist.
//!
//! THIS FILE ASSERTS THE FIXED BEHAVIOUR:
//!   (a) `resolved_close_must_not_release_a_gated_recovery_obligation`
//!       — THE DISCRIMINATOR. Fails on the unfixed tree: the obligation is released
//!         (`pending_obligation_count_long` 1 -> 0, `loss_weight_sum_long` 4_000_000 -> 2_000_000)
//!         and the obligor is paid out in full.
//!   (b) `gated_obligation_releases_once_the_opposite_side_has_cleared`
//!       — THE LIVENESS HALF. The refusal is not a brick: the same public entry releases the
//!         obligation on the very next call once the opposite side's real positions are gone.
//!         Passes before AND after the fix, by construction.
//!   (c) `an_ordinary_leg_on_the_same_recovery_asset_still_detaches`
//!       — THE NARROWNESS CONTROL. The new conjunct keys on `basis_pos_q == 0 &&
//!         loss_weight != 0`; an ordinary leg on the same asset, in the same market, with the
//!         same opposite-side state, still closes in one call. Passes before AND after the fix.
//!
//! Every test carries a non-vacuity block asserting the state it claims to be in BEFORE the call
//! under test — in particular that NO `pending_domain_loss_barrier_*` is standing, so the
//! pre-existing guard at `:21087` cannot be what produces the result.
//!
//! Run:
//!   cargo test --test resolved_close_obligation_gate
//!   cargo test --features audit-scan --test resolved_close_obligation_gate

use percolator::POS_SCALE;
use percolator::{
    v16_domain_count_for_market_slots, AssetLifecycleV16, AssetStateV16, EngineAssetSlotV16Account,
    Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, MarketModeV16,
    PortfolioAccountV16Account, PortfolioLegV16, PortfolioV16ViewMut, ProvenanceHeaderV16,
    ProvenanceHeaderV16Account, ResolvedCloseOutcomeV16, TradeRequestV16, V16Config, V16Error,
};

const PRICE: u64 = 1_000_000;
const LOT: u128 = 2 * POS_SCALE;
const DEPOSIT: u128 = 400_000_000;
/// `add_open_interest_for_new_position` (`:732-769`) books `loss_weight == abs_q` for an opening
/// leg at `a == ADL_ONE`, so each leg here weighs `LOT` and the long side starts at `2 * LOT`.
const LEG_WEIGHT: u128 = LOT;

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn signed_q(q: u128) -> i128 {
    i128::try_from(q).unwrap()
}

/// `account_fixture`, copied from `tests/v16_spec_tests.rs` (as in `tests/f04_regression.rs`).
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

/// `decode_market_mode` (`e8715152:src/v16.rs:23320-23327`), as in `tests/f04_regression.rs`.
fn decode_mode(header: &MarketGroupV16HeaderAccount) -> MarketModeV16 {
    match header.mode {
        0 => MarketModeV16::Live,
        1 => MarketModeV16::Resolved,
        2 => MarketModeV16::Recovery,
        other => panic!("unknown market mode byte {other}"),
    }
}

#[derive(Clone, Copy)]
enum Who {
    /// the obligor: its leg is retained as a zero-basis pending obligation
    L1,
    /// an ordinary long on the same asset — the remaining same-side loss bearer
    L2,
    /// the real position on the OPPOSITE side, whose presence must hold the release
    S,
}

struct World {
    header: MarketGroupV16HeaderAccount,
    markets: Vec<Market<u64>>,
    l1: PortfolioAccountV16Account,
    l2: PortfolioAccountV16Account,
    s: PortfolioAccountV16Account,
}

impl World {
    fn asset(&self) -> AssetStateV16 {
        self.markets[0].engine.asset.try_to_runtime().unwrap()
    }
    fn barrier_long(&self) -> u64 {
        self.markets[0]
            .engine
            .pending_domain_loss_barrier_long
            .get()
    }
    fn barrier_short(&self) -> u64 {
        self.markets[0]
            .engine
            .pending_domain_loss_barrier_short
            .get()
    }
    fn leg(&self, who: Who) -> PortfolioLegV16 {
        let acct = match who {
            Who::L1 => &self.l1,
            Who::L2 => &self.l2,
            Who::S => &self.s,
        };
        acct.legs[0].try_to_runtime().unwrap()
    }
    fn validate(&mut self, label: &str) {
        let view = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        assert_eq!(view.validate_shape(), Ok(()), "{label}: validate_shape");
    }

    /// wrapper tag 30 `CloseResolved` -> `handle_close_resolved`
    /// (`percolator-prog:src/v16_program.rs:16745`), which stops requiring the owner's signature
    /// once `force_close_delay_slots` has elapsed since `resolved_slot` (`:16779-16785`).
    fn close_resolved(&mut self, who: Who) -> Result<ResolvedCloseOutcomeV16, V16Error> {
        let mut m = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        let acct = match who {
            Who::L1 => &mut self.l1,
            Who::L2 => &mut self.l2,
            Who::S => &mut self.s,
        };
        let mut v = PortfolioV16ViewMut::new(acct);
        m.close_resolved_account_not_atomic(&mut v, 0)
    }
}

/// Public entries only:
///   1. three deposits (`deposit_not_atomic`, wrapper tag 1),
///   2. two opening trades L1/S and L2/S (`execute_trade_with_fee_loss_stale_scoped_not_atomic`,
///      wrapper tag 3),
///   3. `force_asset_recovery_not_atomic(0, 1)` — marketauth-gated `UpdateAssetLifecycle`,
///   4. L1's owner-signed dead-leg forfeit (`forfeit_recovery_leg_not_atomic`, wrapper tag 43).
///      On a `Recovery` asset whose opposite side still holds a real position,
///      `retain_recovery_loss_weight_before_detach` (`:16855`) is TRUE, so the forfeit parks the
///      leg as a pending obligation instead of detaching it,
///   5. `resolve_market_not_atomic(2)` — the group goes `Resolved`; the asset stays `Recovery`.
fn drive_to_the_parked_obligation() -> World {
    let (market_id, _, _) = ids();
    let cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    let mut header = MarketGroupV16HeaderAccount::new_dynamic(market_id, cfg, 1, 0).unwrap();
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header
        .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, PRICE, 1)
        .unwrap();
    let mut w = World {
        header,
        markets,
        l1: account_fixture(1, 10),
        l2: account_fixture(1, 11),
        s: account_fixture(1, 12),
    };
    w.validate("0. after activation");

    // 1. deposits
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        for acct in [&mut w.l1, &mut w.l2, &mut w.s] {
            let mut v = PortfolioV16ViewMut::new(acct);
            m.deposit_not_atomic(&mut v, DEPOSIT).unwrap();
        }
    }
    w.validate("1. after the three deposits");

    // 2. a matched book: L1 long LOT and L2 long LOT, both against S.
    for first in [true, false] {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let long_acct = if first { &mut w.l1 } else { &mut w.l2 };
        let mut long = PortfolioV16ViewMut::new(long_acct);
        let mut short = PortfolioV16ViewMut::new(&mut w.s);
        m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut long,
            &mut short,
            TradeRequestV16 {
                asset_index: 0,
                size_q: signed_q(LOT),
                exec_price: PRICE,
                fee_bps: 0,
            },
            true,
        )
        .unwrap();
    }
    w.validate("2. after the two opening trades");
    assert_eq!(w.asset().oi_eff_long_q, 2 * LOT);
    assert_eq!(w.asset().oi_eff_short_q, 2 * LOT);
    assert_eq!(w.asset().loss_weight_sum_long, 2 * LEG_WEIGHT);
    assert_eq!(w.asset().stored_pos_count_long, 2);
    assert_eq!(w.asset().stored_pos_count_short, 1);

    // 3. the asset goes into Recovery.
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.force_asset_recovery_not_atomic(0, 1).unwrap();
    }
    assert_eq!(w.asset().lifecycle, AssetLifecycleV16::Recovery);
    w.validate("3. after force_asset_recovery");

    // 4. L1's owner forfeit parks the leg as a pending obligation (detached == false).
    let outcome = {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut v = PortfolioV16ViewMut::new(&mut w.l1);
        m.forfeit_recovery_leg_not_atomic(&mut v, 0, u128::MAX)
    }
    .expect("the Recovery dead-leg forfeit is the owner exit C-04 relies on");
    assert!(
        !outcome.detached,
        "the forfeit must RETAIN, not detach: retain_recovery_loss_weight_before_detach \
         (:16855) is true while the short side holds a real position — got {outcome:?}"
    );
    assert_eq!(w.asset().pending_obligation_count_long, 1);
    assert_eq!(
        w.asset().loss_weight_sum_long,
        2 * LEG_WEIGHT,
        "retention keeps the obligor's loss weight on the side"
    );
    w.validate("4. after the retention forfeit");

    // 5. the group resolves. The asset lifecycle is NOT reset (:20529-20542).
    {
        let mut m = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        m.resolve_market_not_atomic(2).unwrap();
    }
    assert_eq!(decode_mode(&w.header), MarketModeV16::Resolved);
    assert_eq!(
        w.asset().lifecycle,
        AssetLifecycleV16::Recovery,
        "resolve_market_not_atomic never resets per-asset lifecycle — this is the reachability"
    );
    w
}

/// Asserts the exact state the new conjunct keys on, and that nothing ELSE could explain a
/// refusal. Returns the obligor's leg.
fn non_vacuity(w: &World) -> PortfolioLegV16 {
    assert_eq!(decode_mode(&w.header), MarketModeV16::Resolved);
    assert_eq!(
        w.asset().lifecycle,
        AssetLifecycleV16::Recovery,
        "vacuous unless the asset lifecycle is Recovery: \
         kernel_recovery_pending_obligation_release_allowed (:1329) admits unconditionally otherwise"
    );
    assert_eq!(
        w.barrier_long(),
        0,
        "vacuous unless NO long barrier stands: the pre-existing guard at :21087 would refuse on \
         its own and the test would prove nothing"
    );
    assert_eq!(w.barrier_short(), 0, "and none on the short side either");
    let leg = w.leg(Who::L1);
    assert!(leg.active, "vacuous unless the obligor still holds its leg");
    assert_eq!(
        leg.basis_pos_q, 0,
        "vacuous unless the leg is zero-basis — the first conjunct of the gate"
    );
    assert_eq!(
        leg.loss_weight, LEG_WEIGHT,
        "vacuous unless the leg still carries loss weight — the second conjunct"
    );
    assert!(!leg.b_stale && !leg.stale, "the leg is settled and fresh");
    assert_eq!(
        w.l1.pnl.get(),
        0,
        "the obligor is solvent, so detach_solvent_active_legs_for_resolved_close (:21064) does \
         not bail before reaching the per-leg walk"
    );
    leg
}

// =================================================================================================
// (a) THE DISCRIMINATOR — RED before the fix, GREEN after.
// =================================================================================================

/// Before hunk (d) this resolved close returned `Ok(Closed { payout: 400000000 })`:
/// `pending_obligation_count_long` went 1 -> 0 and `loss_weight_sum_long` 4_000_000 -> 2_000_000,
/// leaving L2 carrying 100% of the long side's loss weight instead of 50% while the short side's
/// real position was still open. It must now be refused — as `ProgressOnly`, with no state
/// written — because the opposite side still holds a real (non-obligation) position.
#[test]
fn resolved_close_must_not_release_a_gated_recovery_obligation() {
    let mut w = drive_to_the_parked_obligation();
    let leg = non_vacuity(&w);
    let before = w.asset();
    let vault_before = w.header.vault.get();

    // The gate's own predicate, spelled out: the opposite (short) side holds a stored position
    // that is NOT itself a pending obligation, so the obligation may not be released yet.
    assert_eq!(before.stored_pos_count_short, 1);
    assert_eq!(before.pending_obligation_count_short, 0);
    assert_ne!(
        before.stored_pos_count_short, before.pending_obligation_count_short,
        "vacuous unless the opposite side carries REAL positions: \
         kernel_recovery_pending_obligation_release_allowed (:1337-1338) would otherwise admit"
    );
    assert_eq!(before.pending_obligation_count_long, 1);
    assert_eq!(before.loss_weight_sum_long, 2 * LEG_WEIGHT);
    assert_eq!(before.stored_pos_count_long, 2);
    assert_eq!(w.l1.capital.get(), DEPOSIT);

    // ---- the call under test (wrapper tag 30 `CloseResolved`) ----
    let outcome = w.close_resolved(Who::L1);

    // ---- THE OBSERVABLE (asserted before the outcome enum, so a regression names the field) --
    let after = w.asset();
    assert_eq!(
        after.pending_obligation_count_long, 1,
        "kernel_clear_leg (:1461) decremented pending_obligation_count_long for a \
         zero-basis obligation whose side had not earned release"
    );
    assert_eq!(
        after.loss_weight_sum_long,
        2 * LEG_WEIGHT,
        "kernel_clear_leg (:1476) subtracted the obligor's loss_weight from \
         loss_weight_sum_long, shifting its share of the next socialized loss onto L2"
    );
    assert_eq!(after.stored_pos_count_long, 2);
    assert_eq!(
        after.oi_eff_short_q, before.oi_eff_short_q,
        "the opposite side is untouched"
    );

    // ---- and it was a clean refusal, not a partial mutation ----
    let leg_after = w.leg(Who::L1);
    assert!(leg_after.active, "the obligation leg is still stored");
    assert_eq!(leg_after.basis_pos_q, leg.basis_pos_q);
    assert_eq!(leg_after.loss_weight, leg.loss_weight);
    assert_eq!(
        w.l1.capital.get(),
        DEPOSIT,
        "the obligor was not paid out ahead of the loss it still owes"
    );
    assert_eq!(
        w.header.vault.get(),
        vault_before,
        "and the vault owes no transfer for the refused close"
    );
    assert_eq!(
        outcome,
        Ok(ResolvedCloseOutcomeV16::ProgressOnly),
        "the obligor's resolved close must not COMPLETE while its obligation is unreleasable"
    );
    w.validate("after the refused obligor close");

    // ---- idempotent: repeating the permissionless crank neither progresses nor corrupts ----
    for round in 0..3 {
        assert_eq!(
            w.close_resolved(Who::L1),
            Ok(ResolvedCloseOutcomeV16::ProgressOnly),
            "round {round}"
        );
        assert_eq!(w.asset().pending_obligation_count_long, 1);
        assert_eq!(w.asset().loss_weight_sum_long, 2 * LEG_WEIGHT);
        w.validate("after a repeated refused obligor close");
    }
}

// =================================================================================================
// (b) THE LIVENESS HALF — the refusal has a production exit.
// =================================================================================================

/// The gate is a wait, not a brick. `recovery_pending_obligation_release_allowed` becomes true as
/// soon as the OPPOSITE side's real positions are gone, and those positions have their own
/// unconditional exit through the very same public entry (their legs carry `basis_pos_q != 0`, so
/// the new conjunct never applies to them). This test drives that to completion.
///
/// It passes both before and after the fix — its job is to prove the fix is not a brick.
#[test]
fn gated_obligation_releases_once_the_opposite_side_has_cleared() {
    let mut w = drive_to_the_parked_obligation();
    non_vacuity(&w);

    // L2 and S close out through tag 30. Neither is gated: both legs carry non-zero basis.
    assert_eq!(
        w.close_resolved(Who::L2),
        Ok(ResolvedCloseOutcomeV16::Closed { payout: DEPOSIT })
    );
    w.validate("after L2's close");
    assert_eq!(
        w.close_resolved(Who::S),
        Ok(ResolvedCloseOutcomeV16::Closed { payout: DEPOSIT })
    );
    w.validate("after S's close");

    // The release condition is now met on the long side's opposite (short) side.
    let mid = w.asset();
    assert_eq!(
        (
            mid.stored_pos_count_short,
            mid.pending_obligation_count_short
        ),
        (0, 0),
        "the opposite side is empty, so the obligation has earned its release"
    );
    assert_eq!(mid.pending_obligation_count_long, 1, "still parked");
    assert_eq!(
        mid.loss_weight_sum_long, LEG_WEIGHT,
        "only the obligor's own weight is left on the side"
    );
    assert_eq!(
        mid.lifecycle,
        AssetLifecycleV16::Recovery,
        "and it was reached with NO lifecycle change — the liveness needs no admin action"
    );

    // ---- and the SAME call that was refused in (a) now completes, on the very next attempt ----
    assert_eq!(
        w.close_resolved(Who::L1),
        Ok(ResolvedCloseOutcomeV16::Closed { payout: DEPOSIT }),
        "LIVENESS: the gate must release the obligation once the opposite side is clear"
    );
    let after = w.asset();
    assert_eq!(after.pending_obligation_count_long, 0);
    assert_eq!(after.loss_weight_sum_long, 0);
    assert_eq!(after.stored_pos_count_long, 0);
    assert!(!w.leg(Who::L1).active);
    w.validate("after the released obligor close");
}

// =================================================================================================
// (c) THE NARROWNESS CONTROL — the gate does not refuse ordinary legs.
// =================================================================================================

/// The new conjunct is `basis_pos_q == 0 && loss_weight != 0 && !release_allowed`. L2 sits on the
/// SAME Recovery asset, in the SAME Resolved market, with the SAME opposite-side state that
/// refuses L1 in (a) — but its leg carries real basis, so its resolved close must still complete
/// in one call. Without this control, (a) would be satisfied by a blanket refusal.
///
/// It passes both before and after the fix.
#[test]
fn an_ordinary_leg_on_the_same_recovery_asset_still_detaches() {
    let mut w = drive_to_the_parked_obligation();
    non_vacuity(&w);

    let l2_leg = w.leg(Who::L2);
    assert!(l2_leg.active);
    assert_ne!(
        l2_leg.basis_pos_q, 0,
        "vacuous unless L2's leg carries real basis — that is the only difference from (a)"
    );
    let before = w.asset();
    assert_ne!(
        before.stored_pos_count_short, before.pending_obligation_count_short,
        "the opposite-side state is the one that refuses L1 in (a)"
    );

    assert_eq!(
        w.close_resolved(Who::L2),
        Ok(ResolvedCloseOutcomeV16::Closed { payout: DEPOSIT }),
        "an ordinary leg must not be caught by the obligation gate"
    );
    let after = w.asset();
    assert!(!w.leg(Who::L2).active);
    assert_eq!(after.stored_pos_count_long, 1);
    assert_eq!(
        after.loss_weight_sum_long, LEG_WEIGHT,
        "L2's own weight left the side; the obligor's did not"
    );
    assert_eq!(
        after.pending_obligation_count_long, 1,
        "and the parked obligation is untouched by L2's close"
    );
    w.validate("after the ordinary leg's close");
}
