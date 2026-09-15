//! F-03 REGRESSION — the fixed behaviour, asserted.
//!
//! This is `verify/poc/F-03/poc_F03.rs` with the defect assertion inverted. Every
//! fixture and every step is byte-identical to the PoC, so the two files measure the
//! same thing and disagree only about what the answer must be.
//!
//! What must hold after the fix:
//!   * the AUDIT FACT survives — an ordinary leg clear whose sub-atom social-loss dust
//!     crosses one `SOCIAL_LOSS_DEN` still saturating-adds +1 to
//!     `explicit_unallocated_loss_<side>` (tests (a), (b) and (d) are unchanged, and
//!     (d) still shows no public entry ever LOWERS it);
//!   * the LATCH is gone — with every header counter at its healthy value and no
//!     `pending_domain_loss_barrier_*`, a permissionless crank must now CLEAR
//!     `bankruptcy_hlock_active`, even though the write-off counter is still set.
//!
//! The wrapper half is measured separately (percolator-prog `tests/v16_wrapper.rs`,
//! `f03_regression_wrapper_tags_reopen_after_a_permissionless_clear`): after this
//! clear, tags 50 / 52 return Ok. See `verify/fixes/F-03.md`.

use percolator::{
    v16_domain_count_for_market_slots, EngineAssetSlotV16Account, LiquidationRequestV16, Market,
    MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PermissionlessCrankActionV16,
    PermissionlessCrankRequestV16, PortfolioAccountV16Account, PortfolioV16ViewMut,
    ProvenanceHeaderV16, ProvenanceHeaderV16Account, RebalanceRequestV16, TradeRequestV16,
    V16Config, V16Error, V16PodU64,
};
use percolator::{ADL_ONE, POS_SCALE, SOCIAL_LOSS_DEN};

// ---------------------------------------------------------------- fixtures --
// copied from tests/v16_spec_tests.rs @ 2c38570a

fn ids() -> ([u8; 32], [u8; 32], [u8; 32]) {
    ([1; 32], [2; 32], [3; 32])
}

fn funding_market_fixture(init_price: u64) -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
    let (market_id, _, _) = ids();
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.max_abs_funding_e9_per_slot = 10_000;
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

// ------------------------------------------------------------------ world ---

const PRICE: u64 = 1_000_000;
const MARK: u64 = PRICE + 1_800_000;
const LOT: u128 = 3 * POS_SCALE;

struct World {
    header: MarketGroupV16HeaderAccount,
    markets: Vec<Market<u64>>,
    longs: Vec<PortfolioAccountV16Account>,
    short_big: PortfolioAccountV16Account,
    #[allow(dead_code)]
    short_thin: PortfolioAccountV16Account,
}

impl World {
    fn asset(&self) -> percolator::AssetStateV16 {
        self.markets[0].engine.asset.try_to_runtime().unwrap()
    }
    fn explicit_long(&self) -> u128 {
        self.asset().explicit_unallocated_loss_long
    }
    fn hlock(&self) -> u8 {
        self.header.bankruptcy_hlock_active
    }

    /// wrapper tag 5 `PermissionlessCrank`, action 0 -> `PermissionlessCrankActionV16::Refresh`
    /// (`percolator-prog` `handle_permissionless_crank_zero_copy`; the target
    /// portfolio's owner never signs).
    fn crank_refresh(&mut self, account: &mut PortfolioAccountV16Account, now_slot: u64) {
        let mut market = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        let mut v = PortfolioV16ViewMut::new(account);
        market
            .permissionless_crank_not_atomic(
                &mut v,
                PermissionlessCrankRequestV16 {
                    now_slot,
                    asset_index: 0,
                    effective_price: MARK,
                    funding_rate_e9: 0,
                    action: PermissionlessCrankActionV16::Refresh,
                },
            )
            .expect("permissionless Refresh crank must succeed");
    }

    /// wrapper tag 3 `Trade` -> `execute_trade_with_fee_loss_stale_scoped_not_atomic`.
    /// Closes `longs[i]` to flat against the fat short; the engine routes this
    /// through `PositionRouteV16::Clear` -> `clear_leg_at_slot_inner` ->
    /// `V16Core::kernel_clear_leg`.
    fn close_long_to_flat(&mut self, i: usize) -> Result<(), V16Error> {
        let asset = self.asset();
        let leg = self.longs[i].legs[0].try_to_runtime().unwrap();
        let effective = leg.basis_pos_q * (asset.a_long as i128) / (ADL_ONE as i128);
        let mut market = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        let mut lv = PortfolioV16ViewMut::new(&mut self.longs[i]);
        let mut sv = PortfolioV16ViewMut::new(&mut self.short_big);
        market
            .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                &mut lv,
                &mut sv,
                TradeRequestV16 {
                    asset_index: 0,
                    size_q: -effective,
                    exec_price: MARK,
                    fee_bps: 0,
                },
                true,
            )
            .map(|_| ())
    }
}

/// Builds the chain state every step starts from, using only public entries:
///   * five long accounts each carrying `LOT`,
///   * one fat short taking the other side of `longs[0..4]`,
///   * one thin short taking the other side of `longs[4]`,
///   * a price move that puts the thin short under water past its capital,
///   * a PUBLIC permissionless liquidation of the thin short (wrapper tag 5,
///     action `Liquidate`) whose residual is socialized onto the long side.
fn bankrupt_world() -> World {
    let (mut header, mut markets) = funding_market_fixture(PRICE);
    let mut longs: Vec<PortfolioAccountV16Account> =
        (0..5).map(|i| account_fixture(1, 100 + i as u8)).collect();
    let mut short_big = account_fixture(1, 200);
    let mut short_thin = account_fixture(1, 201);

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        {
            let mut v = PortfolioV16ViewMut::new(&mut short_big);
            market.deposit_not_atomic(&mut v, 400_000_000).unwrap();
        }
        {
            let mut v = PortfolioV16ViewMut::new(&mut short_thin);
            market.deposit_not_atomic(&mut v, 3_250_000).unwrap();
        }
        for l in longs.iter_mut() {
            let mut v = PortfolioV16ViewMut::new(l);
            market.deposit_not_atomic(&mut v, 100_000_000).unwrap();
        }
        for l in longs.iter_mut().take(4) {
            let mut lv = PortfolioV16ViewMut::new(l);
            let mut sv = PortfolioV16ViewMut::new(&mut short_big);
            market
                .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                    &mut lv,
                    &mut sv,
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
        {
            let mut lv = PortfolioV16ViewMut::new(&mut longs[4]);
            let mut sv = PortfolioV16ViewMut::new(&mut short_thin);
            market
                .execute_trade_with_fee_loss_stale_scoped_not_atomic(
                    &mut lv,
                    &mut sv,
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
        market
            .accrue_asset_to_not_atomic(0, 2, PRICE + 900_000, 0, true)
            .unwrap();
        market
            .accrue_asset_to_not_atomic(0, 3, MARK, 0, true)
            .unwrap();
        market.markets[0].engine.asset.raw_oracle_target_price = V16PodU64::new(MARK);
    }

    {
        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut sv = PortfolioV16ViewMut::new(&mut short_thin);
        market
            .liquidate_account_not_atomic(&mut sv, LiquidationRequestV16 { asset_index: 0 })
            .expect("permissionless liquidation (wrapper tag 5, action Liquidate)");
    }

    World {
        header,
        markets,
        longs,
        short_big,
        short_thin,
    }
}

/// `bankrupt_world()` + a permissionless Refresh crank on every surviving
/// account (so each long carries its settled sub-atom `b_rem`).
fn settled_world() -> World {
    let mut w = bankrupt_world();
    for i in 0..5 {
        let mut a = core::mem::take(&mut w.longs[i]);
        // The public Refresh crank settles B in bounded chunks; repeat until the
        // leg is no longer b-stale (the wrapper keeper does exactly this).
        for _ in 0..64 {
            w.crank_refresh(&mut a, 3);
            if !a.legs[0].try_to_runtime().unwrap().b_stale {
                break;
            }
        }
        assert!(
            !a.legs[0].try_to_runtime().unwrap().b_stale,
            "long[{i}] must settle its B index within the chunk budget"
        );
        w.longs[i] = a;
    }
    let mut s = core::mem::take(&mut w.short_big);
    for _ in 0..64 {
        w.crank_refresh(&mut s, 3);
        if !s.legs[0].try_to_runtime().unwrap().b_stale {
            break;
        }
    }
    w.short_big = s;
    w
}

// ------------------------------------------------------------------- (a) ----

#[test]
fn f03_a_public_liquidation_sets_bankruptcy_hlock_and_socializes_loss() {
    let w = bankrupt_world();
    assert_eq!(
        w.hlock(),
        1,
        "consume_domain_insurance_for_negative_pnl (v16.rs:11622) must latch the group byte"
    );
    let asset = w.asset();
    assert_ne!(
        asset.b_long_num, 0,
        "the bankruptcy residual must be socialized onto the surviving long side"
    );
    assert_eq!(asset.explicit_unallocated_loss_long, 0);
    assert_eq!(asset.social_loss_dust_long_num, 0);
    println!(
        "(a) hlock={} b_long_num={} loss_weight_sum_long={}",
        w.hlock(),
        asset.b_long_num,
        asset.loss_weight_sum_long
    );
}

// ------------------------------------------------------------------- (b) ----

#[test]
fn f03_b_ordinary_close_crossing_one_atom_writes_explicit_unallocated_loss() {
    let mut w = settled_world();

    let b_rem = w.longs[0].legs[0].try_to_runtime().unwrap().b_rem;
    assert_ne!(b_rem, 0, "a settled leg still carries sub-atom social dust");
    assert!(b_rem < SOCIAL_LOSS_DEN);
    println!("(b) per-leg b_rem = {b_rem}  (SOCIAL_LOSS_DEN = {SOCIAL_LOSS_DEN})");

    // First ordinary close: dust rises but does not cross an atom.
    w.close_long_to_flat(0)
        .expect("ordinary close must succeed");
    let a1 = w.asset();
    assert_eq!(a1.social_loss_dust_long_num, b_rem);
    assert_eq!(
        a1.explicit_unallocated_loss_long, 0,
        "no atom crossed yet -> no write"
    );
    println!(
        "(b) after close #1: dust={} explicit={}",
        a1.social_loss_dust_long_num, a1.explicit_unallocated_loss_long
    );

    // Second ordinary close: the dust crosses one atom.
    w.close_long_to_flat(1)
        .expect("ordinary close must succeed");
    let a2 = w.asset();
    assert_eq!(
        a2.explicit_unallocated_loss_long, 1,
        "kernel_normalize_social_loss_carry (v16.rs:1439-1465) wrote \
         explicit_unallocated_loss_long = field.saturating_add(1) at v16.rs:1393"
    );
    assert_eq!(
        a2.social_loss_dust_long_num,
        b_rem + b_rem - SOCIAL_LOSS_DEN,
        "the crossing keeps only the fractional remainder as dust"
    );
    println!(
        "(b) after close #2: dust={} explicit={}  <-- ATOM CROSSED",
        a2.social_loss_dust_long_num, a2.explicit_unallocated_loss_long
    );
}

// ------------------------------------------------------------------- (c) ----

#[test]
fn f03_c_a_realized_write_off_atom_no_longer_latches_the_hlock() {
    let mut w = settled_world();
    w.close_long_to_flat(0).unwrap();
    w.close_long_to_flat(1).unwrap();
    assert_eq!(w.explicit_long(), 1);

    // Drive the market back to a fully healthy, flat state through public
    // entries only: close every remaining long, which also takes the fat short
    // to flat.
    for i in 2..5 {
        w.close_long_to_flat(i).unwrap();
    }
    for i in 0..5 {
        let mut a = core::mem::take(&mut w.longs[i]);
        {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            let r1 = market.full_account_refresh_not_atomic(&mut v).map(|_| ());
            let r2 = market.convert_released_pnl_to_capital_not_atomic(&mut v);
            println!(
                "(c) long[{i}] refresh={r1:?} convert={r2:?} pnl={}",
                v.header.pnl.get()
            );
        }
        w.longs[i] = a;
    }
    {
        let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        let mut v = PortfolioV16ViewMut::new(&mut w.short_big);
        let r1 = market.full_account_refresh_not_atomic(&mut v).map(|_| ());
        let r2 = market.convert_released_pnl_to_capital_not_atomic(&mut v);
        println!(
            "(c) short_big refresh={r1:?} convert={r2:?} pnl={}",
            v.header.pnl.get()
        );
    }

    println!(
        "(c) neg_pnl={} stale_cert={} b_stale={} pnl_pos_tot={} recovery={:?} barrier={}/{}",
        w.header.negative_pnl_account_count.get(),
        w.header.stale_certificate_count.get(),
        w.header.b_stale_account_count.get(),
        w.header.pnl_pos_tot.get(),
        w.header.recovery_reason.try_to_runtime().unwrap(),
        w.markets[0].engine.pending_domain_loss_barrier_long.get(),
        w.markets[0].engine.pending_domain_loss_barrier_short.get()
    );
    println!(
        "(c) explicit_long={} explicit_short={} hlock={}",
        w.asset().explicit_unallocated_loss_long,
        w.asset().explicit_unallocated_loss_short,
        w.hlock()
    );

    // Every header condition `try_clear_bankruptcy_hlock_if_healthy`
    // (v16.rs:19282-19296) checks is now at its healthy value...
    assert_eq!(w.header.negative_pnl_account_count.get(), 0);
    assert_eq!(w.header.stale_certificate_count.get(), 0);
    assert_eq!(w.header.b_stale_account_count.get(), 0);
    assert_eq!(w.header.pnl_pos_tot.get(), 0);
    assert!(w.header.recovery_reason.try_to_runtime().unwrap().is_none());
    assert_eq!(
        w.markets[0].engine.pending_domain_loss_barrier_long.get(),
        0
    );
    assert_eq!(
        w.markets[0].engine.pending_domain_loss_barrier_short.get(),
        0
    );

    // ...and the permissionless clear path must now SUCCEED.
    // `group_has_unabsorbed_bankruptcy_loss` no longer counts
    // `explicit_unallocated_loss_*`: a realized write-off is not loss awaiting
    // absorption, so it must not hold the group-wide byte.
    let counter_before = w.explicit_long();
    assert!(
        counter_before >= 1,
        "the write-off counter must actually be set, or this proves nothing"
    );
    let mut a = core::mem::take(&mut w.longs[0]);
    w.crank_refresh(&mut a, 4);
    w.longs[0] = a;
    assert_eq!(
        w.hlock(),
        0,
        "F-03: a realized write-off atom must not keep bankruptcy_hlock_active latched \
         after a healthy permissionless crank"
    );

    // The audit fact is NOT destroyed by the fix: the counter is still exactly what it
    // was. The write-off stays durable until asset retirement.
    assert_eq!(
        w.explicit_long(),
        counter_before,
        "F-03: the fix must clear the latch without erasing the audit counter"
    );

    // And the gate is not neutered: a genuine `pending_domain_loss_barrier_*` still
    // holds the hlock. Raise one by hand (a state edit, not a source edit), re-latch,
    // and the identical crank must refuse to clear.
    w.header.bankruptcy_hlock_active = 1;
    w.markets[0].engine.pending_domain_loss_barrier_long = V16PodU64::new(1);
    let mut a = core::mem::take(&mut w.longs[1]);
    w.crank_refresh(&mut a, 5);
    w.longs[1] = a;
    assert_eq!(
        w.hlock(),
        1,
        "a genuine pending domain-loss barrier must still hold the hlock"
    );
    w.markets[0].engine.pending_domain_loss_barrier_long = V16PodU64::new(0);
}

// ------------------------------------------------------------------- (d) ----

#[test]
fn f03_d_no_public_entry_lowers_the_counter() {
    let mut w = settled_world();
    w.close_long_to_flat(0).unwrap();
    w.close_long_to_flat(1).unwrap();
    assert_eq!(w.explicit_long(), 1);
    let baseline = w.explicit_long();
    let mut prev = baseline;
    let mut tried: Vec<(&str, String)> = Vec::new();

    macro_rules! probe {
        ($name:expr, $body:expr) => {{
            let r: String = $body;
            let now = w.explicit_long();
            assert!(
                now >= prev,
                "{} LOWERED explicit_unallocated_loss_long: {} -> {}",
                $name,
                prev,
                now
            );
            tried.push(($name, format!("{r} | explicit_long = {now}")));
            prev = now;
        }};
    }

    probe!("PermissionlessCrank(Refresh)", {
        let mut a = core::mem::take(&mut w.longs[2]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!(
                "{:?}",
                market.permissionless_crank_not_atomic(
                    &mut v,
                    PermissionlessCrankRequestV16 {
                        now_slot: 4,
                        asset_index: 0,
                        effective_price: MARK,
                        funding_rate_e9: 0,
                        action: PermissionlessCrankActionV16::Refresh,
                    },
                )
            )
        };
        w.longs[2] = a;
        r
    });

    probe!("PermissionlessCrank(SettleB)", {
        let mut a = core::mem::take(&mut w.longs[2]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!(
                "{:?}",
                market.permissionless_crank_not_atomic(
                    &mut v,
                    PermissionlessCrankRequestV16 {
                        now_slot: 4,
                        asset_index: 0,
                        effective_price: MARK,
                        funding_rate_e9: 0,
                        action: PermissionlessCrankActionV16::SettleB { asset_index: 0 },
                    },
                )
            )
        };
        w.longs[2] = a;
        r
    });

    probe!("PermissionlessCrank(Liquidate)", {
        let mut a = core::mem::take(&mut w.longs[2]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!(
                "{:?}",
                market.permissionless_crank_not_atomic(
                    &mut v,
                    PermissionlessCrankRequestV16 {
                        now_slot: 4,
                        asset_index: 0,
                        effective_price: MARK,
                        funding_rate_e9: 0,
                        action: PermissionlessCrankActionV16::Liquidate(LiquidationRequestV16 {
                            asset_index: 0,
                        }),
                    },
                )
            )
        };
        w.longs[2] = a;
        r
    });

    probe!("permissionless_auto_crank_not_atomic", {
        let mut a = core::mem::take(&mut w.longs[2]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!(
                "{:?}",
                market.permissionless_auto_crank_not_atomic(
                    &mut v,
                    percolator::AutoCrankWorkV16 {
                        now_slot: 4,
                        observations: &[percolator::AutoCrankObservationV16 {
                            asset_index: 0,
                            effective_price: MARK,
                            funding_rate_e9: 0,
                        }],
                        resolved_close_fee_rate_per_slot: 0,
                    },
                )
            )
        };
        w.longs[2] = a;
        r
    });

    probe!(
        "Trade close-to-flat",
        format!("{:?}", w.close_long_to_flat(2))
    );

    probe!("full_account_refresh_not_atomic", {
        let mut a = core::mem::take(&mut w.longs[3]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!("{:?}", market.full_account_refresh_not_atomic(&mut v))
        };
        w.longs[3] = a;
        r
    });

    probe!("rebalance_reduce_position_not_atomic", {
        let mut a = core::mem::take(&mut w.longs[3]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!(
                "{:?}",
                market.rebalance_reduce_position_not_atomic(
                    &mut v,
                    RebalanceRequestV16 {
                        asset_index: 0,
                        reduce_q: POS_SCALE,
                    },
                )
            )
        };
        w.longs[3] = a;
        r
    });

    probe!("deposit_not_atomic", {
        let mut a = core::mem::take(&mut w.longs[3]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!("{:?}", market.deposit_not_atomic(&mut v, 1_000))
        };
        w.longs[3] = a;
        r
    });
    probe!("withdraw_not_atomic", {
        let mut a = core::mem::take(&mut w.longs[3]);
        let r = {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            let mut v = PortfolioV16ViewMut::new(&mut a);
            format!("{:?}", market.withdraw_not_atomic(&mut v, 1_000))
        };
        w.longs[3] = a;
        r
    });

    probe!("accrue_asset_to_not_atomic", {
        let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        format!(
            "{:?}",
            market.accrue_asset_to_not_atomic(0, 5, MARK, 0, true)
        )
    });

    probe!("finalize_side_reset_not_atomic", {
        let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        format!(
            "{:?}",
            market.finalize_side_reset_not_atomic(0, percolator::SideV16::Long)
        )
    });
    probe!("mark_asset_drain_only_not_atomic", {
        let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        format!("{:?}", market.mark_asset_drain_only_not_atomic(0))
    });

    // The ONLY engine code that writes 0 to this field is
    // `clear_terminal_social_loss_audit` (v16.rs:20932), reached only from
    // `normalize_terminal_empty_asset_history_not_atomic` (v16.rs:21072), whose
    // only callers are `retire_empty_asset_not_atomic` (v16.rs:20912/20925) and
    // `restart_empty_asset_preserving_insurance_budget_not_atomic`
    // (v16.rs:21019) — both marketauth-gated in the wrapper, and both refuse
    // while the asset still carries live state.
    probe!("retire_empty_asset_not_atomic(asset 0)", {
        let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
        format!("{:?}", market.retire_empty_asset_not_atomic(0, 6))
    });
    probe!(
        "restart_empty_asset_preserving_insurance_budget(asset 0)",
        {
            let mut market = MarketGroupV16ViewMut::new(&mut w.header, &mut w.markets);
            format!(
                "{:?}",
                market.restart_empty_asset_preserving_insurance_budget_not_atomic(0, MARK, 6)
            )
        }
    );

    for (name, out) in &tried {
        println!("(d) {name:<56} -> {out}");
    }
    assert!(
        w.explicit_long() >= baseline,
        "no public entry lowered explicit_unallocated_loss_long ({} -> {})",
        baseline,
        w.explicit_long()
    );
    println!(
        "(d) explicit_unallocated_loss_long: {baseline} -> {} (monotone non-decreasing across {} public entries)",
        w.explicit_long(),
        tried.len()
    );
    assert_eq!(w.hlock(), 1, "and the group byte is still latched");
}
