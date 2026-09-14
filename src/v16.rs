//! v16 account-local risk engine.
//!
//! This module implements the v16 slab-free engine surface: authenticated
//! portfolio accounts, bounded per-account refresh, lazy A/K/F/B settlement,
//! source-domain realizable credit, loss-senior fee handling, account-local
//! cranks, residual B booking, dynamic trade fees, liquidation progress checks,
//! and resolved account close.

use crate::wide_math::{
    checked_mul_div_ceil_u256, floor_div_signed_conservative_i128, mul_div_floor_u256_with_rem,
    wide_mul_div_floor_u128, wide_signed_mul_div_floor_from_k_pair, U256,
};
use crate::{
    ADL_ONE, BOUND_SCALE, CREDIT_RATE_SCALE, FUNDING_DEN, MAX_ACCOUNT_NOTIONAL, MAX_MARGIN_BPS,
    MAX_ORACLE_PRICE, MAX_POSITION_ABS_Q, MAX_PROTOCOL_FEE_ABS,
    MAX_RECOVERY_FALLBACK_DEVIATION_BPS, MAX_TRADE_SIZE_Q, MAX_VAULT_TVL, MIN_A_SIDE, POS_SCALE,
    SOCIAL_LOSS_DEN, SOCIAL_WEIGHT_SCALE,
};

pub const V16_MAX_PORTFOLIO_ASSETS_N: usize = 16;
#[cfg(kani)]
pub const PORTFOLIO_SOURCE_DOMAIN_CAP: usize = 4;
#[cfg(not(kani))]
pub const PORTFOLIO_SOURCE_DOMAIN_CAP: usize = 2 * V16_MAX_PORTFOLIO_ASSETS_N;
pub const V16_ACTIVE_BITMAP_WORDS: usize = (V16_MAX_PORTFOLIO_ASSETS_N + 63) / 64;
pub type V16ActiveBitmap = [u64; V16_ACTIVE_BITMAP_WORDS];
pub const V16_EMPTY_ACTIVE_BITMAP: V16ActiveBitmap = [0; V16_ACTIVE_BITMAP_WORDS];
pub const V16_BACKING_BUCKETS_PER_DOMAIN: usize = 1;
// Bump whenever the on-chain account/header Pod layout changes (see the
// PortfolioAccountV16Account size assertion). 18: added per-side K/F settlement
// epochs and a per-leg epoch snapshot.
pub const V16_LAYOUT_DISCRIMINATOR: u16 = 18;
pub const V16_ACCOUNT_VERSION: u16 = 1;
pub const BACKING_FEE_RATE_DEN_E9: u128 = 1_000_000_000;
pub const MAX_BACKING_FEE_RATE_E9_PER_SLOT: u64 = 1_000_000_000;
pub const MAX_BACKING_FEE_UTIL_BPS: u64 = 10_000;

/// fork feature A-6 stress envelope: trigger threshold (bps x 1e9) for the
/// `stress_consumption_bps_e9_since_envelope` accumulator. When the accumulator crosses this value,
/// `threshold_stress_active` is set true and the next `h_lock_lane` lookup lifts the lane HMin->HMax.
/// Calibration: a single max-budget accrual at MAX_MARGIN_BPS=10_000 contributes at most ~1e13 bps_e9,
/// so the trigger at 1e20 requires ~1e7 sustained max-budget accruals before flipping.
pub const STRESS_ENVELOPE_TRIGGER_BPS_E9: u128 = 100_000_000_000_000_000_000;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BackingDomainFeeSplitV16 {
    pub lien_delta_atoms: u128,
    pub total_fee: u128,
    pub provider_fee: u128,
    pub insurance_fee: u128,
}

pub fn backing_domain_fee_split_for_lien_delta_num(
    lien_delta_num: u128,
    fee_bps: u16,
    insurance_share_bps: u16,
) -> V16Result<BackingDomainFeeSplitV16> {
    if fee_bps as u64 > MAX_MARGIN_BPS || insurance_share_bps as u64 > MAX_MARGIN_BPS {
        return Err(V16Error::InvalidConfig);
    }
    if lien_delta_num % BOUND_SCALE != 0 {
        return Err(V16Error::InvalidConfig);
    }
    let lien_delta_atoms = lien_delta_num / BOUND_SCALE;
    let total_fee = checked_fee_bps(lien_delta_atoms, fee_bps as u64)?;
    let insurance_fee = wide_mul_div_floor_u128(
        total_fee,
        insurance_share_bps as u128,
        MAX_MARGIN_BPS as u128,
    );
    let provider_fee = total_fee
        .checked_sub(insurance_fee)
        .ok_or(V16Error::CounterUnderflow)?;
    Ok(BackingDomainFeeSplitV16 {
        lien_delta_atoms,
        total_fee,
        provider_fee,
        insurance_fee,
    })
}

fn apply_backing_utilization_fee_charge(
    account_capital: u128,
    group_c_tot: u128,
    bucket_earnings: u128,
    account_pnl: i128,
    requested_fee: u128,
) -> V16Result<(u128, u128, u128, u128)> {
    if requested_fee == 0 || account_pnl < 0 {
        return Ok((0, account_capital, group_c_tot, bucket_earnings));
    }
    let charged = requested_fee.min(account_capital);
    if charged == 0 {
        return Ok((0, account_capital, group_c_tot, bucket_earnings));
    }
    let next_account_capital = account_capital
        .checked_sub(charged)
        .ok_or(V16Error::CounterUnderflow)?;
    let next_group_c_tot = group_c_tot
        .checked_sub(charged)
        .ok_or(V16Error::CounterUnderflow)?;
    let next_bucket_earnings = bucket_earnings
        .checked_add(charged)
        .ok_or(V16Error::CounterOverflow)?;
    Ok((
        charged,
        next_account_capital,
        next_group_c_tot,
        next_bucket_earnings,
    ))
}

fn apply_backing_provider_earnings_withdraw(
    vault: u128,
    bucket_earnings: u128,
    amount: u128,
) -> V16Result<(u128, u128)> {
    if amount == 0 {
        return Ok((vault, bucket_earnings));
    }
    if bucket_earnings < amount {
        return Err(V16Error::CounterUnderflow);
    }
    let next_vault = vault
        .checked_sub(amount)
        .ok_or(V16Error::CounterUnderflow)?;
    Ok((next_vault, bucket_earnings - amount))
}

fn health_cert_after_capital_debit(cert: HealthCertV16, amount: u128) -> V16Result<HealthCertV16> {
    let amount_i128 = i128::try_from(amount).map_err(|_| V16Error::ArithmeticOverflow)?;
    let next_equity = cert
        .certified_equity
        .checked_sub(amount_i128)
        .ok_or(V16Error::ArithmeticOverflow)?;
    if next_equity < 0 || (next_equity as u128) < cert.certified_initial_req {
        return Err(V16Error::LockActive);
    }
    Ok(HealthCertV16 {
        certified_equity: next_equity,
        certified_liq_deficit: if next_equity < 0 {
            next_equity.unsigned_abs()
        } else {
            cert.certified_maintenance_req
                .saturating_sub(next_equity as u128)
        },
        ..cert
    })
}

#[cfg(kani)]
pub fn kani_apply_backing_utilization_fee_charge(
    account_capital: u128,
    group_c_tot: u128,
    bucket_earnings: u128,
    account_pnl: i128,
    requested_fee: u128,
) -> V16Result<(u128, u128, u128, u128)> {
    apply_backing_utilization_fee_charge(
        account_capital,
        group_c_tot,
        bucket_earnings,
        account_pnl,
        requested_fee,
    )
}

#[cfg(kani)]
pub fn kani_apply_backing_provider_earnings_withdraw(
    vault: u128,
    bucket_earnings: u128,
    amount: u128,
) -> V16Result<(u128, u128)> {
    apply_backing_provider_earnings_withdraw(vault, bucket_earnings, amount)
}

#[cfg(kani)]
pub fn kani_health_cert_after_capital_debit(
    cert: HealthCertV16,
    amount: u128,
) -> V16Result<HealthCertV16> {
    health_cert_after_capital_debit(cert, amount)
}

#[inline]
pub fn v16_domain_count_for_market_slots(max_market_slots: u32) -> V16Result<usize> {
    (max_market_slots as usize)
        .checked_mul(2)
        .ok_or(V16Error::ArithmeticOverflow)
}

#[inline]
pub fn v16_domain_pair_for_asset_index(asset_index: usize) -> V16Result<(usize, usize)> {
    let long_domain = asset_index
        .checked_mul(2)
        .ok_or(V16Error::ArithmeticOverflow)?;
    let short_domain = long_domain
        .checked_add(1)
        .ok_or(V16Error::ArithmeticOverflow)?;
    Ok((long_domain, short_domain))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V16Error {
    InvalidConfig,
    ArithmeticOverflow,
    ProvenanceMismatch,
    HiddenLeg,
    InvalidLeg,
    Stale,
    BStale,
    LockActive,
    NonProgress,
    RecoveryRequired,
    CounterOverflow,
    CounterUnderflow,
    /// Equity is below the initial-margin requirement for this action.
    /// Distinct from `InvalidConfig` (configuration error) so callers can
    /// surface a user-readable "insufficient margin" message rather than a
    /// generic config-error bucket.  The wrapper maps this to
    /// `PercolatorError::EngineInsufficientInitialMargin` (Custom 49).
    InsufficientInitialMargin,
    /// An LP-vault deposit is too small to receive even one share after
    /// conservative round-down pricing. Rejecting this in the engine prevents
    /// callers from accepting collateral while silently minting zero shares.
    LpVaultZeroSharesMinted,
}

pub type V16Result<T> = core::result::Result<T, V16Error>;

#[inline]
pub const fn active_bitmap_empty() -> V16ActiveBitmap {
    V16_EMPTY_ACTIVE_BITMAP
}

#[inline]
pub fn active_bitmap_is_empty(bitmap: V16ActiveBitmap) -> bool {
    let mut i = 0;
    while i < V16_ACTIVE_BITMAP_WORDS {
        if bitmap[i] != 0 {
            return false;
        }
        i += 1;
    }
    true
}

#[inline]
pub fn active_bitmap_get(bitmap: V16ActiveBitmap, leg_slot_index: usize) -> bool {
    if leg_slot_index >= V16_MAX_PORTFOLIO_ASSETS_N {
        return false;
    }
    let word = leg_slot_index / 64;
    let bit = leg_slot_index % 64;
    ((bitmap[word] >> bit) & 1) != 0
}

#[inline]
fn active_bitmap_set(bitmap: &mut V16ActiveBitmap, leg_slot_index: usize) -> V16Result<()> {
    if leg_slot_index >= V16_MAX_PORTFOLIO_ASSETS_N {
        return Err(V16Error::InvalidConfig);
    }
    let word = leg_slot_index / 64;
    let bit = leg_slot_index % 64;
    bitmap[word] |= 1u64 << bit;
    Ok(())
}

#[cfg(any(kani, test, feature = "fork-facade"))]
pub fn kani_active_bitmap_set(
    bitmap: &mut V16ActiveBitmap,
    leg_slot_index: usize,
) -> V16Result<()> {
    active_bitmap_set(bitmap, leg_slot_index)
}

#[inline]
fn active_bitmap_clear(bitmap: &mut V16ActiveBitmap, leg_slot_index: usize) -> V16Result<()> {
    if leg_slot_index >= V16_MAX_PORTFOLIO_ASSETS_N {
        return Err(V16Error::InvalidConfig);
    }
    let word = leg_slot_index / 64;
    let bit = leg_slot_index % 64;
    bitmap[word] &= !(1u64 << bit);
    Ok(())
}

#[inline]
fn active_bitmap_with_cleared(
    mut bitmap: V16ActiveBitmap,
    leg_slot_index: usize,
) -> V16Result<V16ActiveBitmap> {
    active_bitmap_clear(&mut bitmap, leg_slot_index)?;
    Ok(bitmap)
}

#[inline]
fn liquidation_remaining_active_bitmap_after_close(
    active_bitmap: V16ActiveBitmap,
    leg_slot_index: usize,
    close_q: u128,
    leg_abs_q: u128,
) -> V16Result<V16ActiveBitmap> {
    if close_q == leg_abs_q {
        active_bitmap_with_cleared(active_bitmap, leg_slot_index)
    } else {
        Ok(active_bitmap)
    }
}

#[inline]
fn liquidation_uncovered_loss_after_principal(pnl: i128, capital: u128) -> u128 {
    if pnl < 0 {
        pnl.unsigned_abs().saturating_sub(capital)
    } else {
        0
    }
}

#[inline]
fn uncovered_loss_remains_with_open_risk(
    pnl: i128,
    capital: u128,
    remaining_active_bitmap: V16ActiveBitmap,
) -> bool {
    let uncovered_loss_after_principal = liquidation_uncovered_loss_after_principal(pnl, capital);
    uncovered_loss_after_principal != 0 && !active_bitmap_is_empty(remaining_active_bitmap)
}

#[inline]
fn unattributed_loss_lock_after_pnl(
    was_locked: bool,
    active_bitmap: V16ActiveBitmap,
    new_pnl: i128,
) -> bool {
    new_pnl < 0 && (was_locked || active_bitmap_count_ones(active_bitmap) > 1)
}

#[cfg(kani)]
pub fn kani_liquidation_close_would_leave_uncovered_loss_with_open_risk(
    pnl: i128,
    capital: u128,
    active_bitmap: V16ActiveBitmap,
    leg_slot_index: usize,
    close_q: u128,
    leg_abs_q: u128,
) -> V16Result<bool> {
    let remaining_active_bitmap = liquidation_remaining_active_bitmap_after_close(
        active_bitmap,
        leg_slot_index,
        close_q,
        leg_abs_q,
    )?;
    Ok(uncovered_loss_remains_with_open_risk(
        pnl,
        capital,
        remaining_active_bitmap,
    ))
}

#[cfg(kani)]
pub fn kani_unattributed_loss_lock_after_pnl(
    was_locked: bool,
    active_bitmap: V16ActiveBitmap,
    new_pnl: i128,
) -> bool {
    unattributed_loss_lock_after_pnl(was_locked, active_bitmap, new_pnl)
}

// FIX E3 (upstream #92 / b97e1746): liquidation size + fee are now fully
// engine-selected. The caller (wrapper/keeper) supplies only `asset_index`;
// the engine binary-searches the minimal partial close that restores
// maintenance health (or closes the leg fully when no such partial exists),
// and always derives the fee rate from CONFIG, never from the caller.
fn liquidation_risk_notional_ceil(abs_pos_q: u128, price: u64) -> V16Result<u128> {
    if abs_pos_q == 0 {
        return Ok(0);
    }
    if abs_pos_q > MAX_POSITION_ABS_Q || price > MAX_ORACLE_PRICE {
        return Err(V16Error::InvalidConfig);
    }
    let product = abs_pos_q * price as u128;
    let q = product / POS_SCALE;
    let r = product % POS_SCALE;
    q.checked_add(u128::from(r != 0))
        .ok_or(V16Error::ArithmeticOverflow)
}

fn liquidation_leg_maintenance_requirement(
    config: V16Config,
    abs_q: u128,
    side: SideV16,
    effective_price: u64,
    raw_target_price: u64,
) -> V16Result<u128> {
    if abs_q == 0 {
        return Ok(0);
    }
    if config.maintenance_margin_bps > MAX_MARGIN_BPS {
        return Err(V16Error::InvalidConfig);
    }
    let risk_notional = liquidation_risk_notional_ceil(abs_q, effective_price)?;
    let adverse_delta =
        V16Core::target_effective_lag_adverse_delta(side, effective_price, raw_target_price);
    let target_lag_penalty = liquidation_risk_notional_ceil(abs_q, adverse_delta)?;
    let base = margin_requirement(
        risk_notional,
        config.maintenance_margin_bps,
        config.min_nonzero_mm_req,
    )?;
    base.checked_add(target_lag_penalty)
        .ok_or(V16Error::ArithmeticOverflow)
}

fn liquidation_projected_health_deficit_from_parts(
    certified_equity: i128,
    certified_maintenance_req: u128,
    old_leg_maintenance: u128,
    new_leg_maintenance: u128,
    charged_fee: u128,
) -> V16Result<u128> {
    let post_maintenance = certified_maintenance_req
        .checked_sub(old_leg_maintenance)
        .and_then(|v| v.checked_add(new_leg_maintenance))
        .ok_or(V16Error::ArithmeticOverflow)?;
    let charged_fee_i128 = i128::try_from(charged_fee).map_err(|_| V16Error::ArithmeticOverflow)?;
    let post_equity = certified_equity
        .checked_sub(charged_fee_i128)
        .ok_or(V16Error::ArithmeticOverflow)?;
    if post_equity < 0 {
        return post_maintenance
            .checked_add(post_equity.unsigned_abs())
            .ok_or(V16Error::ArithmeticOverflow);
    }
    Ok(post_maintenance.saturating_sub(post_equity as u128))
}

#[allow(clippy::too_many_arguments)]
fn liquidation_projected_healthy_after_close(
    config: V16Config,
    cert: HealthCertV16,
    capital: u128,
    pnl: i128,
    side: SideV16,
    old_abs_q: u128,
    effective_price: u64,
    raw_target_price: u64,
    fee_bps: u64,
    close_q: u128,
) -> V16Result<bool> {
    if close_q == 0 || close_q > old_abs_q {
        return Ok(false);
    }
    let old_maintenance = liquidation_leg_maintenance_requirement(
        config,
        old_abs_q,
        side,
        effective_price,
        raw_target_price,
    )?;
    let new_abs_q = old_abs_q - close_q;
    let new_maintenance = liquidation_leg_maintenance_requirement(
        config,
        new_abs_q,
        side,
        effective_price,
        raw_target_price,
    )?;
    let fee_notional = liquidation_risk_notional_ceil(close_q, effective_price)?;
    let fee = liquidation_fee_for_close(
        fee_notional,
        fee_bps,
        config.min_liquidation_abs,
        config.liquidation_fee_cap,
        close_q == old_abs_q,
    )?;
    let charged_fee = if pnl >= 0 { fee.min(capital) } else { 0 };
    Ok(liquidation_projected_health_deficit_from_parts(
        cert.certified_equity,
        cert.certified_maintenance_req,
        old_maintenance,
        new_maintenance,
        charged_fee,
    )? == 0)
}

#[allow(clippy::too_many_arguments)]
fn liquidation_partial_close_is_healthy(
    config: V16Config,
    cert: HealthCertV16,
    capital: u128,
    pnl: i128,
    side: SideV16,
    old_abs_q: u128,
    effective_price: u64,
    raw_target_price: u64,
    fee_bps: u64,
    close_q: u128,
) -> V16Result<bool> {
    match liquidation_projected_healthy_after_close(
        config,
        cert,
        capital,
        pnl,
        side,
        old_abs_q,
        effective_price,
        raw_target_price,
        fee_bps,
        close_q,
    ) {
        // A partial close below the configured absolute fee floor is not an
        // admissible liquidation chunk. Every other error remains fail-closed.
        Err(V16Error::NonProgress) => Ok(false),
        result => result,
    }
}

fn min_abs_q_for_risk_notional_at_least(
    risk_notional: u128,
    effective_price: u64,
) -> V16Result<u128> {
    if risk_notional == 0 {
        return Ok(0);
    }
    if effective_price == 0 {
        return Err(V16Error::InvalidConfig);
    }
    let numerator = risk_notional - 1;
    if let Some(product) = numerator.checked_mul(POS_SCALE) {
        return (product / effective_price as u128)
            .checked_add(1)
            .ok_or(V16Error::ArithmeticOverflow);
    }
    U256::from_u128(numerator)
        .checked_mul(U256::from_u128(POS_SCALE))
        .and_then(|v| v.checked_div(U256::from_u128(effective_price as u128)))
        .and_then(|v| v.try_into_u128())
        .and_then(|v| v.checked_add(1))
        .ok_or(V16Error::ArithmeticOverflow)
}

fn liquidation_partial_search_hi(
    config: V16Config,
    old_abs_q: u128,
    effective_price: u64,
) -> V16Result<u128> {
    if config.maintenance_margin_bps == 0 {
        return Ok(0);
    }
    let floor_exit_notional = V16Config::checked_mul_div_ceil_to_u128(
        config.min_nonzero_mm_req,
        MAX_MARGIN_BPS as u128,
        config.maintenance_margin_bps as u128,
    )?;
    let floor_exit_q = min_abs_q_for_risk_notional_at_least(floor_exit_notional, effective_price)?;
    Ok(old_abs_q.saturating_sub(floor_exit_q))
}

#[allow(clippy::too_many_arguments)]
fn liquidation_engine_close_request_q(
    config: V16Config,
    cert: HealthCertV16,
    capital: u128,
    pnl: i128,
    side: SideV16,
    old_abs_q: u128,
    effective_price: u64,
    raw_target_price: u64,
    fee_bps: u64,
) -> V16Result<u128> {
    if old_abs_q == 0 {
        return Err(V16Error::InvalidLeg);
    }
    if cert.certified_equity < 0 || pnl < 0 {
        return Ok(old_abs_q);
    }
    if !liquidation_projected_healthy_after_close(
        config,
        cert,
        capital,
        pnl,
        side,
        old_abs_q,
        effective_price,
        raw_target_price,
        fee_bps,
        old_abs_q,
    )? {
        return Ok(old_abs_q);
    }
    // The absolute maintenance floor makes projected health non-monotone: a
    // partial close can become healthy, unhealthy again as its fee grows while
    // maintenance is flat, then healthy on the full-close discontinuity. Search
    // only the proportional-margin prefix. Crossing into the floor region is a
    // deterministic dust/full-close policy.
    let partial_hi = liquidation_partial_search_hi(config, old_abs_q, effective_price)?;
    if partial_hi == 0
        || !liquidation_partial_close_is_healthy(
            config,
            cert,
            capital,
            pnl,
            side,
            old_abs_q,
            effective_price,
            raw_target_price,
            fee_bps,
            partial_hi,
        )?
    {
        return Ok(old_abs_q);
    }
    let mut lo = 1u128;
    let mut hi = partial_hi;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let healthy = liquidation_partial_close_is_healthy(
            config,
            cert,
            capital,
            pnl,
            side,
            old_abs_q,
            effective_price,
            raw_target_price,
            fee_bps,
            mid,
        )?;
        if healthy {
            hi = mid;
        } else {
            lo = mid.checked_add(1).ok_or(V16Error::ArithmeticOverflow)?;
        }
    }
    if liquidation_partial_close_is_healthy(
        config,
        cert,
        capital,
        pnl,
        side,
        old_abs_q,
        effective_price,
        raw_target_price,
        fee_bps,
        lo,
    )? {
        Ok(lo)
    } else {
        Ok(old_abs_q)
    }
}

#[cfg(kani)]
pub fn kani_liquidation_projected_health_deficit_from_parts(
    certified_equity: i128,
    certified_maintenance_req: u128,
    old_leg_maintenance: u128,
    new_leg_maintenance: u128,
    charged_fee: u128,
) -> V16Result<u128> {
    liquidation_projected_health_deficit_from_parts(
        certified_equity,
        certified_maintenance_req,
        old_leg_maintenance,
        new_leg_maintenance,
        charged_fee,
    )
}

#[cfg(kani)]
pub fn kani_liquidation_projected_healthy_after_close(
    config: V16Config,
    cert: HealthCertV16,
    capital: u128,
    pnl: i128,
    side: SideV16,
    old_abs_q: u128,
    effective_price: u64,
    raw_target_price: u64,
    fee_bps: u64,
    close_q: u128,
) -> V16Result<bool> {
    liquidation_projected_healthy_after_close(
        config,
        cert,
        capital,
        pnl,
        side,
        old_abs_q,
        effective_price,
        raw_target_price,
        fee_bps,
        close_q,
    )
}

#[cfg(kani)]
pub fn kani_liquidation_engine_close_request_q(
    config: V16Config,
    cert: HealthCertV16,
    capital: u128,
    pnl: i128,
    side: SideV16,
    old_abs_q: u128,
    effective_price: u64,
    raw_target_price: u64,
    fee_bps: u64,
) -> V16Result<u128> {
    liquidation_engine_close_request_q(
        config,
        cert,
        capital,
        pnl,
        side,
        old_abs_q,
        effective_price,
        raw_target_price,
        fee_bps,
    )
}

#[cfg(kani)]
pub fn kani_liquidation_partial_search_hi(
    config: V16Config,
    old_abs_q: u128,
    effective_price: u64,
) -> V16Result<u128> {
    liquidation_partial_search_hi(config, old_abs_q, effective_price)
}

fn add_open_interest_for_new_position(
    asset: &mut AssetStateV16,
    side: SideV16,
    abs_q: u128,
    loss_weight: u128,
) -> V16Result<()> {
    match side {
        SideV16::Long => {
            asset.stored_pos_count_long = asset
                .stored_pos_count_long
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?;
            asset.oi_eff_long_q = asset
                .oi_eff_long_q
                .checked_add(abs_q)
                .ok_or(V16Error::ArithmeticOverflow)?;
            asset.loss_weight_sum_long = asset
                .loss_weight_sum_long
                .checked_add(loss_weight)
                .ok_or(V16Error::ArithmeticOverflow)?;
        }
        SideV16::Short => {
            asset.stored_pos_count_short = asset
                .stored_pos_count_short
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?;
            asset.oi_eff_short_q = asset
                .oi_eff_short_q
                .checked_add(abs_q)
                .ok_or(V16Error::ArithmeticOverflow)?;
            asset.loss_weight_sum_short = asset
                .loss_weight_sum_short
                .checked_add(loss_weight)
                .ok_or(V16Error::ArithmeticOverflow)?;
        }
    }
    Ok(())
}

#[cfg(kani)]
pub fn kani_add_open_interest_for_new_position(
    asset: &mut AssetStateV16,
    side: SideV16,
    abs_q: u128,
    loss_weight: u128,
) -> V16Result<()> {
    add_open_interest_for_new_position(asset, side, abs_q, loss_weight)
}

#[inline]
pub fn active_bitmap_count_ones(bitmap: V16ActiveBitmap) -> u32 {
    let mut total = 0u32;
    let mut i = 0;
    while i < V16_ACTIVE_BITMAP_WORDS {
        total = total.saturating_add(bitmap[i].count_ones());
        i += 1;
    }
    total
}

struct V16Core;

impl V16Core {
    /// ceil(a * b / denominator) with a u128 fast path and a U256 fallback
    /// (upstream 4c4dfb20 / ba7a84b7; zero denominator is InvalidConfig).
    #[inline(always)]
    fn mul_div_ceil_u128_or_wide(a: u128, b: u128, denominator: u128) -> V16Result<u128> {
        if denominator == 0 {
            return Err(V16Error::InvalidConfig);
        }
        if let Some(product) = a.checked_mul(b) {
            let quotient = product / denominator;
            return quotient
                .checked_add(u128::from(product % denominator != 0))
                .ok_or(V16Error::ArithmeticOverflow);
        }
        checked_mul_div_ceil_u256(
            U256::from_u128(a),
            U256::from_u128(b),
            U256::from_u128(denominator),
        )
        .and_then(|value| value.try_into_u128())
        .ok_or(V16Error::ArithmeticOverflow)
    }

    /// Claim-free terminal overlap recredit: the paired-domain insurance spend
    /// that is also backed by an outstanding provider receivable and by
    /// claim-free residual. (upstream 76a86f48)
    fn terminal_claim_free_overlap_recredit(
        provider_receivable_atoms: u128,
        paired_domain_insurance_spent: u128,
        claim_free_residual_remaining: u128,
    ) -> u128 {
        provider_receivable_atoms
            .min(paired_domain_insurance_spent)
            .min(claim_free_residual_remaining)
    }

    /// One asset step of the bounded terminal slab scan, priority ordered:
    /// expire a lapsed long, then short, bucket; recredit; wait on live
    /// backing; else continue. (upstream 6f3c5c12 / 545e0224)
    fn kernel_terminal_slab_asset_step(
        long_status: BackingBucketStatusV16,
        long_expiry_slot: u64,
        short_status: BackingBucketStatusV16,
        short_expiry_slot: u64,
        authenticated_slot: u64,
        recreditable: bool,
    ) -> TerminalSlabAssetStepV16 {
        let long_fresh = long_status == BackingBucketStatusV16::Fresh;
        let short_fresh = short_status == BackingBucketStatusV16::Fresh;
        if long_fresh && long_expiry_slot <= authenticated_slot {
            TerminalSlabAssetStepV16::Expire(0)
        } else if short_fresh && short_expiry_slot <= authenticated_slot {
            TerminalSlabAssetStepV16::Expire(1)
        } else if recreditable {
            TerminalSlabAssetStepV16::Recredit
        } else if (long_fresh && long_expiry_slot > authenticated_slot)
            || (short_fresh && short_expiry_slot > authenticated_slot)
        {
            TerminalSlabAssetStepV16::Wait
        } else {
            TerminalSlabAssetStepV16::Continue
        }
    }

    /// A parked cursor may only report strict progress. (upstream 6f3c5c12)
    fn kernel_terminal_slab_wait_continuation(
        scan_start_asset_index: usize,
        asset_index: usize,
    ) -> V16Result<usize> {
        if asset_index <= scan_start_asset_index {
            Err(V16Error::LockActive)
        } else {
            Ok(asset_index)
        }
    }

    /// Starts a new settlement cohort whenever a side's K/F target moves.
    /// The epoch makes repeated accrual and exact index reversal unambiguous.
    pub(crate) fn kernel_mark_kf_stale_cohorts(
        mut asset: AssetStateV16,
        long_changed: bool,
        short_changed: bool,
        cohort_epoch: u64,
    ) -> V16Result<AssetStateV16> {
        if long_changed {
            if cohort_epoch <= asset.kf_epoch_long {
                return Err(V16Error::InvalidConfig);
            }
            asset.kf_epoch_long = cohort_epoch;
            asset.stale_account_count_long = asset.stored_pos_count_long;
        }
        if short_changed {
            if cohort_epoch <= asset.kf_epoch_short {
                return Err(V16Error::InvalidConfig);
            }
            asset.kf_epoch_short = cohort_epoch;
            asset.stale_account_count_short = asset.stored_pos_count_short;
        }
        Ok(asset)
    }

    /// Discharges this leg from the current side cohort exactly once and returns
    /// the epoch the leg must persist with its refreshed K/F snapshots.
    pub(crate) fn kernel_settle_kf_stale_cohort(
        mut asset: AssetStateV16,
        side: SideV16,
        leg_kf_epoch_snap: u64,
    ) -> V16Result<(AssetStateV16, u64)> {
        let (epoch, count) = match side {
            SideV16::Long => (asset.kf_epoch_long, &mut asset.stale_account_count_long),
            SideV16::Short => (asset.kf_epoch_short, &mut asset.stale_account_count_short),
        };
        if leg_kf_epoch_snap > epoch {
            return Err(V16Error::InvalidLeg);
        }
        if leg_kf_epoch_snap < epoch {
            *count = count.checked_sub(1).ok_or(V16Error::CounterUnderflow)?;
        }
        Ok((asset, epoch))
    }

    /// PRODUCTION KERNEL: cap unilateral close work by the account's effective
    /// quantity and by matched effective OI. Liquidation and owner rebalance
    /// share this bound so neither can subtract more OI than any participant
    /// or side contains.
    fn kernel_unilateral_close_capacity(
        account_effective_abs: u128,
        oi_eff_long_q: u128,
        oi_eff_short_q: u128,
    ) -> u128 {
        account_effective_abs.min(oi_eff_long_q).min(oi_eff_short_q)
    }

    /// PRODUCTION KERNEL (roadmap 3A.2 risk-reduction / S-L3, A5.dec rank): the
    /// position-reduction core of liquidation/rebalance. Clamps the requested
    /// close to the leg and produces the toward-zero signed delta.
    pub(crate) fn kernel_reduce_position_delta(
        pre_basis_signed: i128,
        side: SideV16,
        requested: u128,
    ) -> V16Result<(u128, i128)> {
        let pre_abs = pre_basis_signed.unsigned_abs();
        let reduce_q = requested.min(pre_abs);
        let reduce_i128 = i128::try_from(reduce_q).map_err(|_| V16Error::ArithmeticOverflow)?;
        let delta = match side {
            SideV16::Long => reduce_i128
                .checked_neg()
                .ok_or(V16Error::ArithmeticOverflow)?,
            SideV16::Short => reduce_i128,
        };
        Ok((reduce_q, delta))
    }

    /// PRODUCTION KERNEL (kernel-proofs restructure): the same-side leg
    /// resize state transform. Pure on small Copy structs so the contract
    /// layer can verify it over its full input domain; the position-delta
    /// glue in MarketGroupV16ViewMut calls exactly this.
    pub(crate) fn kernel_resize_leg_same_side(
        leg: PortfolioLegV16,
        asset: AssetStateV16,
        new_signed: i128,
        new_weight: u128,
        preserve_pending_obligation_weight: bool,
        old_effective_abs: u128,
        new_effective_abs: u128,
    ) -> V16Result<(PortfolioLegV16, AssetStateV16)> {
        let mut leg = leg;
        let mut asset = asset;
        match leg.side {
            SideV16::Long => {
                asset.oi_eff_long_q =
                    adjust_u128(asset.oi_eff_long_q, old_effective_abs, new_effective_abs)?;
                if !preserve_pending_obligation_weight {
                    asset.loss_weight_sum_long =
                        adjust_u128(asset.loss_weight_sum_long, leg.loss_weight, new_weight)?;
                }
            }
            SideV16::Short => {
                asset.oi_eff_short_q =
                    adjust_u128(asset.oi_eff_short_q, old_effective_abs, new_effective_abs)?;
                if !preserve_pending_obligation_weight {
                    asset.loss_weight_sum_short =
                        adjust_u128(asset.loss_weight_sum_short, leg.loss_weight, new_weight)?;
                }
            }
        }
        leg.basis_pos_q = new_signed;
        if !preserve_pending_obligation_weight {
            leg.loss_weight = new_weight;
        }
        Ok((leg, asset))
    }

    /// PRODUCTION KERNEL (spec #37 gate): the trade-finalization initial-
    /// margin decision - an EXACT total decision contract: the gate admits
    /// precisely the states with a VALID certificate whose certified equity
    /// is nonnegative and covers the certified initial requirement, and
    /// rejects everything else (Ok <=> condition, both directions). This is
    /// the verified-certificate gate the maker-exemption rule rides on.
    /// Upstream states that as a `kani::ensures` contract behind its
    /// `contracts` feature, which this fork does not have; the identical
    /// both-directions postcondition is asserted over the same unconstrained
    /// domain by `proof_v16_kernel_initial_margin_gate_exact_decision`.
    ///
    /// FORK FEATURE - DO NOT NORMALIZE AWAY ON A RE-SYNC: the insufficient-
    /// margin rejection returns this fork's `V16Error::InsufficientInitialMargin`,
    /// NOT upstream's generic `V16Error::InvalidConfig`, so the wrapper can
    /// surface a user-readable "insufficient margin"
    /// (`PercolatorError::EngineInsufficientInitialMargin`, Custom 49) rather
    /// than a config-error bucket. That variant does not exist upstream.
    pub(crate) fn kernel_initial_margin_gate(cert: HealthCertV16) -> V16Result<()> {
        if !cert.valid {
            return Err(V16Error::Stale);
        }
        let equity = cert.certified_equity;
        if equity < 0 || (equity as u128) < cert.certified_initial_req {
            return Err(V16Error::InsufficientInitialMargin);
        }
        Ok(())
    }

    /// PRODUCTION KERNEL (spec #37 locked lane): the no-positive-credit
    /// margin decision - exact total decision over the locked-lane equity
    /// (capital + min(pnl,0) - |fee debt|) against the certified initial
    /// requirement: positive PnL credit can NEVER satisfy IM under h-lock.
    /// Upstream states the precondition (`pnl > i128::MIN && fee_credits >
    /// i128::MIN && capital < 1 << 100`) as `kani::requires` and the
    /// postcondition as `kani::ensures`, both behind its `contracts` feature,
    /// which this fork does not have; both are carried over the identical
    /// domain by `proof_v16_kernel_locked_margin_gate_no_positive_credit`.
    pub(crate) fn kernel_locked_margin_gate(
        capital: u128,
        pnl: i128,
        fee_credits: i128,
        certified_initial_req: u128,
    ) -> V16Result<()> {
        let capital_i = i128::try_from(capital).map_err(|_| V16Error::ArithmeticOverflow)?;
        let fee_debt =
            i128::try_from(fee_credits.unsigned_abs()).map_err(|_| V16Error::ArithmeticOverflow)?;
        let equity = capital_i
            .checked_add(pnl.min(0))
            .ok_or(V16Error::ArithmeticOverflow)?
            .checked_sub(fee_debt)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if equity < 0 || (equity as u128) < certified_initial_req {
            return Err(V16Error::LockActive);
        }
        Ok(())
    }

    /// PRODUCTION KERNEL (#37 batch projection): accumulate one fill's
    /// outcome into the running batch outcome. EXACT sum: fill_count += 1,
    /// fees and notional add by exactly the fill's amounts, the three flags
    /// are monotone-OR. Proving this is the batch-projection invariant — a
    /// batch outcome is exactly the fold of its per-fill outcomes, so a batch
    /// is equivalent to its sequence of single fills (no hidden extra work).
    /// Upstream states that as a `kani::ensures` contract behind its
    /// `contracts` feature, which this fork does not have; the identical
    /// postcondition is asserted over the same unconstrained domain by
    /// `proof_v16_kernel_accumulate_batch_trade_exact_fold`.
    pub(crate) fn kernel_accumulate_batch_trade(
        mut outcome: BatchTradeOutcomeV16,
        risk_increasing: bool,
        long_has_source_claims: bool,
        short_has_source_claims: bool,
        applied: TradeApplyOutcomeV16,
    ) -> V16Result<(BatchTradeOutcomeV16, bool, bool, bool)> {
        outcome.fill_count = outcome
            .fill_count
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        outcome.fee_a = outcome
            .fee_a
            .checked_add(applied.fee_a)
            .ok_or(V16Error::ArithmeticOverflow)?;
        outcome.fee_b = outcome
            .fee_b
            .checked_add(applied.fee_b)
            .ok_or(V16Error::ArithmeticOverflow)?;
        outcome.notional = outcome
            .notional
            .checked_add(applied.notional)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok((
            outcome,
            risk_increasing | applied.risk_increasing,
            long_has_source_claims | applied.long_has_source_claims,
            short_has_source_claims | applied.short_has_source_claims,
        ))
    }

    /// PRODUCTION KERNEL (liveness rank): the close-progress ledger advance.
    /// Each partition category grows by exactly its delta; residual_remaining
    /// is recomputed to the exact partition identity and STRICTLY DECREASES by
    /// the booked total — the well-founded rank for close progress (a close
    /// terminates in at most gross_loss booked value); finalization is exactly
    /// residual == 0; over-booking fails closed; every immutable identity
    /// field is frozen.
    pub(crate) fn kernel_advance_close_ledger(
        mut ledger: CloseProgressLedgerV16,
        support_consumed: u128,
        junior_face_burned: u128,
        insurance_spent: u128,
        b_loss_booked: u128,
        explicit_loss_assigned: u128,
    ) -> V16Result<CloseProgressLedgerV16> {
        ledger.support_consumed = ledger
            .support_consumed
            .checked_add(support_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        ledger.junior_face_burned = ledger
            .junior_face_burned
            .checked_add(junior_face_burned)
            .ok_or(V16Error::ArithmeticOverflow)?;
        ledger.insurance_spent = ledger
            .insurance_spent
            .checked_add(insurance_spent)
            .ok_or(V16Error::ArithmeticOverflow)?;
        ledger.b_loss_booked = ledger
            .b_loss_booked
            .checked_add(b_loss_booked)
            .ok_or(V16Error::ArithmeticOverflow)?;
        ledger.explicit_loss_assigned = ledger
            .explicit_loss_assigned
            .checked_add(explicit_loss_assigned)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let total_loss = ledger
            .gross_loss_at_close_start
            .checked_add(ledger.drift_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let progress = ledger
            .support_consumed
            .checked_add(ledger.insurance_spent)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let progress = progress
            .checked_add(ledger.b_loss_booked)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let progress = progress
            .checked_add(ledger.explicit_loss_assigned)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if progress > total_loss {
            return Err(V16Error::ArithmeticOverflow);
        }
        ledger.residual_remaining = total_loss - progress;
        if ledger.residual_remaining == 0 {
            ledger.finalized = true;
        }
        Ok(ledger)
    }

    /// PRODUCTION KERNEL: the attach-leg core — snapshot the side's basis
    /// anchors, gate the a-basis range, add open interest, and construct the
    /// new leg. Pure on (AssetStateV16, scalars); the attach glue calls
    /// exactly this. loss_weight is caller-supplied (division-bearing).
    pub(crate) fn kernel_attach_leg(
        mut asset: AssetStateV16,
        side: SideV16,
        basis_pos_q: i128,
        loss_weight: u128,
        asset_index_u32: u32,
    ) -> V16Result<(AssetStateV16, PortfolioLegV16)> {
        let (a_basis, k_snap, f_snap, kf_epoch_snap, b_snap, epoch_snap) = match side {
            SideV16::Long => (
                asset.a_long,
                asset.k_long,
                asset.f_long_num,
                asset.kf_epoch_long,
                asset.b_long_num,
                asset.epoch_long,
            ),
            SideV16::Short => (
                asset.a_short,
                asset.k_short,
                asset.f_short_num,
                asset.kf_epoch_short,
                asset.b_short_num,
                asset.epoch_short,
            ),
        };
        if !(MIN_A_SIDE..=ADL_ONE).contains(&a_basis) {
            return Err(V16Error::InvalidLeg);
        }
        if loss_weight == 0 {
            return Err(V16Error::InvalidLeg);
        }
        add_open_interest_for_new_position(
            &mut asset,
            side,
            basis_pos_q.unsigned_abs(),
            loss_weight,
        )?;
        let leg = PortfolioLegV16 {
            active: true,
            asset_index: asset_index_u32,
            market_id: asset.market_id,
            side,
            basis_pos_q,
            a_basis,
            k_snap,
            f_snap,
            kf_epoch_snap,
            epoch_snap,
            loss_weight,
            b_snap,
            b_rem: 0,
            b_epoch_snap: epoch_snap,
            b_stale: false,
            stale: false,
        };
        Ok((asset, leg))
    }

    /// PRODUCTION KERNEL: retain a position's loss weight after its basis is
    /// removed. Recovery exits use this while an opposite non-pending position
    /// can still crystallize a socialized loss. The zero-basis leg remains a
    /// bounded, account-local obligation until that cohort has settled.
    pub(crate) fn kernel_retain_leg_as_pending_obligation(
        mut leg: PortfolioLegV16,
        mut asset: AssetStateV16,
        retained_effective_oi_q: u128,
    ) -> V16Result<(PortfolioLegV16, AssetStateV16)> {
        if !leg.active
            || leg.basis_pos_q == 0
            || leg.loss_weight == 0
            || retained_effective_oi_q == 0
            || retained_effective_oi_q > leg.basis_pos_q.unsigned_abs()
        {
            return Err(V16Error::InvalidLeg);
        }
        match leg.side {
            SideV16::Long => {
                asset.oi_eff_long_q = asset
                    .oi_eff_long_q
                    .checked_sub(retained_effective_oi_q)
                    .ok_or(V16Error::CounterUnderflow)?;
                asset.pending_obligation_count_long = asset
                    .pending_obligation_count_long
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?;
            }
            SideV16::Short => {
                asset.oi_eff_short_q = asset
                    .oi_eff_short_q
                    .checked_sub(retained_effective_oi_q)
                    .ok_or(V16Error::CounterUnderflow)?;
                asset.pending_obligation_count_short = asset
                    .pending_obligation_count_short
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?;
            }
        }
        leg.basis_pos_q = 0;
        Ok((leg, asset))
    }

    /// A Recovery obligation may detach only after the opposite side contains
    /// no real (non-obligation) positions. Checking `stored - pending` avoids
    /// both early release and a two-sided zero-basis wait cycle.
    pub(crate) fn kernel_recovery_pending_obligation_release_allowed(
        lifecycle: AssetLifecycleV16,
        opposite_stored_count: u64,
        opposite_pending_count: u64,
    ) -> V16Result<bool> {
        if opposite_pending_count > opposite_stored_count {
            return Err(V16Error::InvalidConfig);
        }
        Ok(lifecycle != AssetLifecycleV16::Recovery
            || opposite_stored_count == opposite_pending_count)
    }

    fn kernel_is_prior_reset_obligation(
        side_mode: SideModeV16,
        asset_epoch: u64,
        leg_epoch_snap: u64,
    ) -> bool {
        side_mode == SideModeV16::ResetPending && leg_epoch_snap.checked_add(1) == Some(asset_epoch)
    }

    /// PRODUCTION KERNEL (value safety, roadmap S-A1/S-L2 foundation): the
    /// principal-settlement core of negative-PnL liquidation/close. Given an
    /// account's capital, the group junior total c_tot, and a (negative) pnl,
    /// pay the loss from principal FIRST: `paid = min(capital, |pnl|)`, and drop
    /// BOTH capital and c_tot by exactly `paid` (conservation — the principal
    /// debit leaves the junior pool by exactly what the account loses, nothing
    /// created or stranded). Pure scalar; the settle/close glue calls exactly
    /// this for the arithmetic.
    ///
    /// Upstream states `paid == min(capital, |pnl|)`, the two exact debits and
    /// `new_pnl == pnl + paid` as a `kani::requires`/`kani::ensures` contract
    /// behind its `contracts` feature, which this fork does not have; the
    /// identical precondition and postcondition are carried over the same
    /// unconstrained domain by
    /// `proof_v16_kernel_settle_principal_exact_paid_and_conservation`.
    pub(crate) fn kernel_settle_principal(
        capital: u128,
        c_tot: u128,
        pnl: i128,
    ) -> V16Result<(u128, u128, u128, i128)> {
        let loss = pnl.unsigned_abs();
        let paid = capital.min(loss);
        let new_capital = capital
            .checked_sub(paid)
            .ok_or(V16Error::CounterUnderflow)?;
        let new_c_tot = c_tot.checked_sub(paid).ok_or(V16Error::CounterUnderflow)?;
        let paid_i128 = i128::try_from(paid).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = pnl
            .checked_add(paid_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok((paid, new_capital, new_c_tot, new_pnl))
    }

    /// PRODUCTION KERNEL (liveness rank): the B-settlement leg advance.
    /// b_snap moves FORWARD by exactly delta_b — the well-founded rank
    /// component for the B-settlement progress theorem: each successful
    /// chunk strictly decreases the leg's distance to its B target.
    /// b_rem is set to new_remainder and b_stale to `remaining_after != 0`
    /// exactly, and every other leg field is frozen. Upstream states that as a
    /// `kani::ensures` contract behind its `contracts` feature, which this fork
    /// does not have; the identical postcondition is asserted over the same
    /// unconstrained domain by
    /// `proof_v16_kernel_advance_leg_b_snap_rank_witness`.
    pub(crate) fn kernel_advance_leg_b_snap(
        mut leg: PortfolioLegV16,
        delta_b: u128,
        new_remainder: u128,
        remaining_after: u128,
    ) -> V16Result<PortfolioLegV16> {
        leg.b_snap = leg
            .b_snap
            .checked_add(delta_b)
            .ok_or(V16Error::ArithmeticOverflow)?;
        leg.b_rem = new_remainder;
        leg.b_stale = remaining_after != 0;
        Ok(leg)
    }

    /// PRODUCTION KERNEL: the clear-leg asset transform — decrement the
    /// side's stored-position count (and pending-obligation count for a
    /// zero-basis obligation leg), and unless the leg predates a side reset,
    /// fold its social-loss dust and remove its OI and loss weight. Pure on
    /// (PortfolioLegV16, AssetStateV16); the clear-leg glue calls exactly this.
    pub(crate) fn kernel_clear_leg(
        leg: PortfolioLegV16,
        mut asset: AssetStateV16,
        clear_effective_oi_q: u128,
    ) -> V16Result<AssetStateV16> {
        let prior_reset_epoch = match leg.side {
            SideV16::Long => {
                asset.mode_long == SideModeV16::ResetPending
                    && leg.epoch_snap.checked_add(1) == Some(asset.epoch_long)
            }
            SideV16::Short => {
                asset.mode_short == SideModeV16::ResetPending
                    && leg.epoch_snap.checked_add(1) == Some(asset.epoch_short)
            }
        };
        let raw_abs_q = leg.basis_pos_q.unsigned_abs();
        let valid_effective_clear = if prior_reset_epoch || raw_abs_q == 0 {
            clear_effective_oi_q == 0
        } else {
            (1..=raw_abs_q).contains(&clear_effective_oi_q)
        };
        if !leg.active || !valid_effective_clear {
            return Err(V16Error::InvalidLeg);
        }
        let normalized_carry = if !prior_reset_epoch && leg.b_rem != 0 {
            let (dust, explicit_loss) = match leg.side {
                SideV16::Long => (
                    asset.social_loss_dust_long_num,
                    asset.explicit_unallocated_loss_long,
                ),
                SideV16::Short => (
                    asset.social_loss_dust_short_num,
                    asset.explicit_unallocated_loss_short,
                ),
            };
            Some(V16Core::kernel_normalize_social_loss_carry(
                leg.b_rem,
                dust,
                explicit_loss,
            )?)
        } else {
            None
        };
        match leg.side {
            SideV16::Long => {
                asset.stored_pos_count_long = asset
                    .stored_pos_count_long
                    .checked_sub(1)
                    .ok_or(V16Error::CounterUnderflow)?;
                if leg.basis_pos_q == 0 && leg.loss_weight != 0 {
                    asset.pending_obligation_count_long = asset
                        .pending_obligation_count_long
                        .checked_sub(1)
                        .ok_or(V16Error::CounterUnderflow)?;
                }
                if !prior_reset_epoch {
                    if let Some((new_dust, explicit_loss)) = normalized_carry {
                        asset.social_loss_dust_long_num = new_dust;
                        asset.explicit_unallocated_loss_long = explicit_loss;
                    }
                    asset.oi_eff_long_q = asset
                        .oi_eff_long_q
                        .checked_sub(clear_effective_oi_q)
                        .ok_or(V16Error::CounterUnderflow)?;
                    asset.loss_weight_sum_long = asset
                        .loss_weight_sum_long
                        .checked_sub(leg.loss_weight)
                        .ok_or(V16Error::CounterUnderflow)?;
                }
            }
            SideV16::Short => {
                asset.stored_pos_count_short = asset
                    .stored_pos_count_short
                    .checked_sub(1)
                    .ok_or(V16Error::CounterUnderflow)?;
                if leg.basis_pos_q == 0 && leg.loss_weight != 0 {
                    asset.pending_obligation_count_short = asset
                        .pending_obligation_count_short
                        .checked_sub(1)
                        .ok_or(V16Error::CounterUnderflow)?;
                }
                if !prior_reset_epoch {
                    if let Some((new_dust, explicit_loss)) = normalized_carry {
                        asset.social_loss_dust_short_num = new_dust;
                        asset.explicit_unallocated_loss_short = explicit_loss;
                    }
                    asset.oi_eff_short_q = asset
                        .oi_eff_short_q
                        .checked_sub(clear_effective_oi_q)
                        .ok_or(V16Error::CounterUnderflow)?;
                    asset.loss_weight_sum_short = asset
                        .loss_weight_sum_short
                        .checked_sub(leg.loss_weight)
                        .ok_or(V16Error::CounterUnderflow)?;
                }
            }
        }
        Ok(asset)
    }

    /// Normalize two sub-atom social-loss carries without making a valid exit
    /// fallible. Crossing one atom records a side-local explicit loss and keeps
    /// only the fractional remainder as dust. The explicit counter is audit
    /// state, so saturation preserves liveness without creating payout value.
    pub(crate) fn kernel_normalize_social_loss_carry(
        remainder: u128,
        dust: u128,
        explicit_loss: u128,
    ) -> V16Result<(u128, u128)> {
        if remainder >= SOCIAL_LOSS_DEN || dust >= SOCIAL_LOSS_DEN {
            return Err(V16Error::InvalidConfig);
        }
        let total = remainder
            .checked_add(dust)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let crossed_atom = total >= SOCIAL_LOSS_DEN;
        let next_dust = if crossed_atom {
            total - SOCIAL_LOSS_DEN
        } else {
            total
        };
        Ok((
            next_dust,
            explicit_loss.saturating_add(u128::from(crossed_atom)),
        ))
    }

    /// PRODUCTION KERNEL: move an exhausted side behind a reset epoch without
    /// touching the opposite side. Prior-epoch legs can then detach without
    /// subtracting their stored basis from already-zero effective OI.
    fn kernel_begin_full_drain_reset(
        mut asset: AssetStateV16,
        side: SideV16,
    ) -> V16Result<AssetStateV16> {
        match side {
            SideV16::Long => {
                if asset.mode_long == SideModeV16::ResetPending
                    || asset.oi_eff_long_q != 0
                    || asset.pending_obligation_count_long != 0
                {
                    return Err(V16Error::LockActive);
                }
                let (dust, explicit_loss) = V16Core::kernel_normalize_social_loss_carry(
                    asset.social_loss_remainder_long_num,
                    asset.social_loss_dust_long_num,
                    asset.explicit_unallocated_loss_long,
                )?;
                asset.social_loss_remainder_long_num = 0;
                asset.social_loss_dust_long_num = dust;
                asset.explicit_unallocated_loss_long = explicit_loss;
                asset.k_epoch_start_long = asset.k_long;
                asset.f_epoch_start_long_num = asset.f_long_num;
                asset.b_epoch_start_long_num = asset.b_long_num;
                asset.k_long = 0;
                asset.f_long_num = 0;
                asset.b_long_num = 0;
                asset.loss_weight_sum_long = 0;
                asset.a_long = ADL_ONE;
                asset.epoch_long = asset
                    .epoch_long
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?;
                asset.mode_long = SideModeV16::ResetPending;
            }
            SideV16::Short => {
                if asset.mode_short == SideModeV16::ResetPending
                    || asset.oi_eff_short_q != 0
                    || asset.pending_obligation_count_short != 0
                {
                    return Err(V16Error::LockActive);
                }
                let (dust, explicit_loss) = V16Core::kernel_normalize_social_loss_carry(
                    asset.social_loss_remainder_short_num,
                    asset.social_loss_dust_short_num,
                    asset.explicit_unallocated_loss_short,
                )?;
                asset.social_loss_remainder_short_num = 0;
                asset.social_loss_dust_short_num = dust;
                asset.explicit_unallocated_loss_short = explicit_loss;
                asset.k_epoch_start_short = asset.k_short;
                asset.f_epoch_start_short_num = asset.f_short_num;
                asset.b_epoch_start_short_num = asset.b_short_num;
                asset.k_short = 0;
                asset.f_short_num = 0;
                asset.b_short_num = 0;
                asset.loss_weight_sum_short = 0;
                asset.a_short = ADL_ONE;
                asset.epoch_short = asset
                    .epoch_short
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?;
                asset.mode_short = SideModeV16::ResetPending;
            }
        }
        Ok(asset)
    }

    /// PRODUCTION KERNEL (roadmap 3A.1 trade spine): classify a position change
    /// from (current signed, new signed) into its leg route — the EXACT total
    /// decision the position-delta body dispatches on. `delta != 0` is enforced
    /// upstream, so `current == 0 => new != 0`. Pure scalar.
    pub(crate) fn kernel_classify_position_delta(current: i128, new: i128) -> PositionRouteV16 {
        if current == 0 {
            PositionRouteV16::Attach
        } else if new == 0 {
            PositionRouteV16::Clear
        } else if current.signum() != new.signum() {
            PositionRouteV16::Flip
        } else {
            PositionRouteV16::Resize
        }
    }

    #[inline]
    pub(crate) fn kernel_adl_scaled_accrual_index_deltas(
        price_delta: i128,
        funding_index_delta: i128,
        a_long: u128,
        a_short: u128,
    ) -> V16Result<(i128, i128, i128, i128)> {
        let a_long = i128::try_from(a_long).map_err(|_| V16Error::ArithmeticOverflow)?;
        let a_short = i128::try_from(a_short).map_err(|_| V16Error::ArithmeticOverflow)?;
        let k_long = checked_i128_mul(price_delta, a_long)?;
        let k_short = checked_i128_mul(price_delta, a_short)?
            .checked_neg()
            .ok_or(V16Error::ArithmeticOverflow)?;
        let f_long = checked_i128_mul(funding_index_delta, a_long)?
            .checked_neg()
            .ok_or(V16Error::ArithmeticOverflow)?;
        let f_short = checked_i128_mul(funding_index_delta, a_short)?;
        Ok((k_long, k_short, f_long, f_short))
    }

    #[inline]
    pub(crate) fn kernel_position_route_requires_unit_adl(
        route: PositionRouteV16,
        current: i128,
        new: i128,
    ) -> bool {
        match route {
            PositionRouteV16::Attach | PositionRouteV16::Flip => true,
            PositionRouteV16::Clear => false,
            PositionRouteV16::Resize => new.unsigned_abs() > current.unsigned_abs(),
        }
    }

    #[inline(always)]
    fn mul_div_floor_u128_or_wide(a: u128, b: u128, denominator: u128) -> V16Result<u128> {
        if denominator == 0 {
            return Err(V16Error::InvalidConfig);
        }
        if let Some(product) = a.checked_mul(b) {
            return Ok(product / denominator);
        }
        U256::from_u128(a)
            .checked_mul(U256::from_u128(b))
            .and_then(|value| value.checked_div(U256::from_u128(denominator)))
            .and_then(|value| value.try_into_u128())
            .ok_or(V16Error::ArithmeticOverflow)
    }

    /// Convert a leg's retained raw basis into the conservative effective
    /// quantity represented by the current side A index. Quantity ADL lowers
    /// `current_a` without rewriting every portfolio, so public position work
    /// must use this quantity rather than treating stale raw basis as live OI.
    pub(crate) fn kernel_adl_effective_quantity_ceil(
        raw_abs_q: u128,
        a_basis: u128,
        current_a: u128,
    ) -> V16Result<u128> {
        if raw_abs_q > MAX_POSITION_ABS_Q
            || !(MIN_A_SIDE..=ADL_ONE).contains(&a_basis)
            || !(1..=a_basis).contains(&current_a)
        {
            return Err(V16Error::InvalidLeg);
        }
        V16Core::mul_div_ceil_u128_or_wide(raw_abs_q, current_a, a_basis)
    }

    /// Return the economically live quantity represented by a retained leg.
    /// Current-epoch legs scale with the side A index. A prior-reset obligation
    /// owns no effective OI even though its raw basis can remain attached until
    /// the bounded cleanup continuation removes it.
    pub(crate) fn effective_abs_quantity_for_leg(
        asset: AssetStateV16,
        leg: PortfolioLegV16,
    ) -> V16Result<u128> {
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let (current_a, asset_epoch, side_mode) = match leg.side {
            SideV16::Long => (asset.a_long, asset.epoch_long, asset.mode_long),
            SideV16::Short => (asset.a_short, asset.epoch_short, asset.mode_short),
        };
        if leg.epoch_snap == asset_epoch {
            return Self::kernel_adl_effective_quantity_ceil(
                leg.basis_pos_q.unsigned_abs(),
                leg.a_basis,
                current_a,
            );
        }
        if Self::kernel_is_prior_reset_obligation(side_mode, asset_epoch, leg.epoch_snap) {
            return Ok(0);
        }
        Err(V16Error::InvalidLeg)
    }

    /// Choose the largest retained raw basis whose conservative effective
    /// quantity is `effective_abs_q`. This is the inverse used after a partial
    /// reduction: `ceil(raw * current_a / a_basis) == effective` while the
    /// account remains on the same side.
    pub(crate) fn kernel_raw_basis_for_adl_effective_quantity(
        effective_abs_q: u128,
        a_basis: u128,
        current_a: u128,
    ) -> V16Result<u128> {
        if effective_abs_q > MAX_POSITION_ABS_Q
            || !(MIN_A_SIDE..=ADL_ONE).contains(&a_basis)
            || !(1..=a_basis).contains(&current_a)
        {
            return Err(V16Error::InvalidLeg);
        }
        let raw_abs_q = V16Core::mul_div_floor_u128_or_wide(effective_abs_q, a_basis, current_a)?;
        if raw_abs_q > MAX_POSITION_ABS_Q {
            return Err(V16Error::InvalidLeg);
        }
        Ok(raw_abs_q)
    }

    /// Applies the uncovered tail of a loss after source support has already
    /// burned `support_face_burned`. Uncovered loss consumes the retained
    /// positive face one-for-one before creating negative PnL.
    pub(crate) fn kernel_settle_positive_face_after_support(
        old_positive_face: u128,
        support_face_burned: u128,
        remaining_loss: u128,
    ) -> V16Result<(i128, u128)> {
        if old_positive_face > i128::MAX as u128
            || support_face_burned > old_positive_face
            || remaining_loss > i128::MAX as u128
        {
            return Err(V16Error::ArithmeticOverflow);
        }
        let retained_face = old_positive_face - support_face_burned;
        let new_pnl = (retained_face as i128)
            .checked_sub(remaining_loss as i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let total_face_burned = old_positive_face - new_pnl.max(0) as u128;
        Ok((new_pnl, total_face_burned))
    }

    /// Separates elective live source-credit conversion from mandatory terminal
    /// settlement. At terminal, only value actually converted to capital leaves
    /// the junior claim face; the source haircut remainder stays in the receipt
    /// pool instead of becoming ownerless vault residue.
    /// (upstream ca4cb3c9; upstream states the same partition as a
    /// `kani::ensures` contract, which this fork carries as the proof
    /// `proof_v16_terminal_source_haircut_retains_junior_face` instead — there
    /// is no `contracts` feature and no `cfg_attr` in this tree.)
    pub(crate) fn kernel_released_pnl_conversion_partition(
        positive_face: u128,
        converted: u128,
        source_face_burn: u128,
        retain_haircut_face: bool,
    ) -> V16Result<(u128, u128)> {
        if converted > source_face_burn || source_face_burn > positive_face {
            return Err(V16Error::InvalidConfig);
        }
        if retain_haircut_face {
            Ok((converted, source_face_burn - converted))
        } else {
            Ok((source_face_burn, 0))
        }
    }

    /// Carries terminal source-credit haircut face between bounded close calls.
    /// The newly reserved face is no longer eligible for realization by another
    /// source, while the still-released face remains exactly the unprocessed
    /// source-attributed portion.
    /// (upstream a4919ffa; upstream states this as a `kani::ensures` contract,
    /// which this fork carries as the proof
    /// `proof_v16_terminal_source_haircut_reserved_exactly_once` instead —
    /// there is no `contracts` feature and no `cfg_attr` in this tree.)
    pub(crate) fn kernel_retain_terminal_source_haircut(
        positive_pnl: u128,
        reserved_pnl: u128,
        source_attributed_face: u128,
        converted: u128,
    ) -> V16Result<u128> {
        if reserved_pnl > positive_pnl
            || source_attributed_face > positive_pnl - reserved_pnl
            || converted > source_attributed_face
        {
            return Err(V16Error::InvalidLeg);
        }
        reserved_pnl
            .checked_add(source_attributed_face - converted)
            .ok_or(V16Error::CounterOverflow)
    }

    /// Recompute the resolved payout rate from the ledger's current residual
    /// and outstanding claim bound. This deliberately contains no wide
    /// division: receipts apply the resulting fraction when they are paid.
    /// (upstream a7577b0b)
    pub(crate) fn kernel_recompute_resolved_payout_rate(
        mut ledger: ResolvedPayoutLedgerV16,
    ) -> V16Result<ResolvedPayoutLedgerV16> {
        let total_bound_num = ledger
            .terminal_claim_exact_receipts_num
            .checked_add(ledger.terminal_claim_bound_unreceipted_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if total_bound_num == 0 {
            ledger.current_payout_rate_num = 1;
            ledger.current_payout_rate_den = 1;
        } else {
            ledger.current_payout_rate_num = ledger
                .snapshot_residual
                .checked_mul(BOUND_SCALE)
                .ok_or(V16Error::ArithmeticOverflow)?
                .min(total_bound_num);
            ledger.current_payout_rate_den = total_bound_num;
        }
        Ok(ledger)
    }

    /// Credit residual released after terminal snapshot capture into both
    /// persisted snapshots and immediately raise the common payout rate.
    /// (upstream a7577b0b)
    pub(crate) fn kernel_credit_post_snapshot_residual(
        mut ledger: ResolvedPayoutLedgerV16,
        legacy_snapshot: u128,
        released: u128,
    ) -> V16Result<(ResolvedPayoutLedgerV16, u128)> {
        ledger.snapshot_residual = ledger
            .snapshot_residual
            .checked_add(released)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let legacy_snapshot = legacy_snapshot
            .checked_add(released)
            .ok_or(V16Error::ArithmeticOverflow)?;
        ledger = Self::kernel_recompute_resolved_payout_rate(ledger)?;
        Ok((ledger, legacy_snapshot))
    }

    /// A close snapshot becomes stale only when the originating asset has
    /// advanced past the immutable close anchor while that asset's leg remains
    /// attached. Unrelated assets may advance the market-wide slot without
    /// changing this close's economics and therefore cannot trigger recovery.
    /// (upstream 377de75c)
    pub(crate) fn kernel_open_close_snapshot_is_stale(
        originating_leg_active: bool,
        originating_asset_slot: u64,
        drift_reference_slot: u64,
    ) -> bool {
        originating_leg_active && originating_asset_slot > drift_reference_slot
    }

    /// PRODUCTION KERNEL: canonicalize only an economically empty expired
    /// bucket. Retirement must not erase consumed principal, impaired backing,
    /// or provider earnings merely because the freshness period ended.
    /// (upstream 379fbfea)
    fn kernel_retirement_backing_normalization(bucket: BackingBucketV16) -> BackingBucketV16 {
        if bucket.status == BackingBucketStatusV16::Expired
            && bucket.fresh_unliened_backing_num == 0
            && bucket.valid_liened_backing_num == 0
            && bucket.consumed_liened_backing_num == 0
            && bucket.impaired_liened_backing_num == 0
            && bucket.utilization_fee_earnings == 0
        {
            BackingBucketV16::empty_for_market(bucket.market_id)
        } else {
            bucket
        }
    }

    /// PRODUCTION KERNEL: expire one lapsed Fresh counterparty-backing bucket.
    /// Unliened and valid-liened principal leave the source fresh reserve; the
    /// liened part becomes impaired on both the source and the bucket.
    /// (upstream c09d4575, extracted from expire_source_backing_bucket_not_atomic)
    fn prepare_counterparty_backing_expiry_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        now_slot: u64,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if bucket.status != BackingBucketStatusV16::Fresh || now_slot < bucket.expiry_slot {
            return Err(V16Error::Stale);
        }
        let expired_unliened = bucket.fresh_unliened_backing_num;
        let expired_liened = bucket.valid_liened_backing_num;
        let expired_total = expired_unliened
            .checked_add(expired_liened)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if source.fresh_reserved_backing_num < expired_total
            || source.valid_liened_backing_num < expired_liened
        {
            return Err(V16Error::CounterUnderflow);
        }
        source.fresh_reserved_backing_num -= expired_total;
        source.valid_liened_backing_num -= expired_liened;
        source.impaired_liened_backing_num = source
            .impaired_liened_backing_num
            .checked_add(expired_liened)
            .ok_or(V16Error::CounterOverflow)?;
        bucket.fresh_unliened_backing_num = 0;
        bucket.valid_liened_backing_num = 0;
        bucket.impaired_liened_backing_num = bucket
            .impaired_liened_backing_num
            .checked_add(expired_liened)
            .ok_or(V16Error::CounterOverflow)?;
        bucket.status = if expired_liened == 0 && bucket.impaired_liened_backing_num == 0 {
            BackingBucketStatusV16::Expired
        } else {
            BackingBucketStatusV16::Impaired
        };
        Ok((bucket, source))
    }

    /// PRODUCTION KERNEL: admit an authenticated clock observation into terminal
    /// settlement. Resolved routes do not accrue markets, but expiry-sensitive
    /// backing still requires a monotonic current slot. (upstream 44847fd5)
    fn kernel_advance_resolved_slot(
        mode: MarketModeV16,
        current_slot: u64,
        authenticated_slot: u64,
    ) -> V16Result<u64> {
        if mode != MarketModeV16::Resolved {
            return Err(V16Error::LockActive);
        }
        if authenticated_slot < current_slot {
            return Err(V16Error::Stale);
        }
        Ok(authenticated_slot)
    }

    /// PRODUCTION KERNEL: one step of the compact source-domain expiry scan.
    /// The first sparse-tail entry terminates the scan; otherwise the first
    /// occupied lapsed Fresh bucket is selected and terminates the scan.
    /// (upstream c09d4575)
    fn kernel_lapsed_source_backing_scan_step(
        selected: Option<usize>,
        sparse_tail: bool,
        occupied: bool,
        domain: usize,
        bucket_status: BackingBucketStatusV16,
        expiry_slot: u64,
        current_slot: u64,
    ) -> (Option<usize>, bool) {
        if selected.is_some() || sparse_tail {
            return (selected, true);
        }
        if occupied && bucket_status == BackingBucketStatusV16::Fresh && expiry_slot <= current_slot
        {
            return (Some(domain), true);
        }
        (None, false)
    }

    /// Select one bounded flat-account source-lien transition. Impaired
    /// counterparty backing is crystallized before any other component in that
    /// domain; otherwise every live component must be current and releasable so
    /// the per-domain release remains atomic. (upstream 6c8d94bc)
    fn kernel_flat_source_lien_normalization(
        source_claim_liened_num: u128,
        counterparty_backing_num: u128,
        insurance_backing_num: u128,
        bucket_status: BackingBucketStatusV16,
        bucket_expiry_slot: u64,
        now_slot: u64,
        bucket_valid_liened_num: u128,
        bucket_impaired_liened_num: u128,
        source_valid_liened_backing_num: u128,
        source_impaired_liened_backing_num: u128,
        reservation_valid_liened_insurance_num: u128,
        source_valid_liened_insurance_num: u128,
    ) -> FlatSourceLienNormalizationV16 {
        if source_claim_liened_num == 0
            || (counterparty_backing_num == 0 && insurance_backing_num == 0)
        {
            return FlatSourceLienNormalizationV16::None;
        }
        if counterparty_backing_num != 0
            && bucket_status == BackingBucketStatusV16::Impaired
            && bucket_impaired_liened_num >= counterparty_backing_num
            && source_impaired_liened_backing_num >= counterparty_backing_num
        {
            return FlatSourceLienNormalizationV16::ImpairCounterparty;
        }
        let counterparty_releasable = counterparty_backing_num == 0
            || (bucket_status == BackingBucketStatusV16::Fresh
                && bucket_expiry_slot > now_slot
                && bucket_valid_liened_num >= counterparty_backing_num
                && source_valid_liened_backing_num >= counterparty_backing_num);
        let insurance_releasable = insurance_backing_num == 0
            || (insurance_backing_num % BOUND_SCALE == 0
                && reservation_valid_liened_insurance_num >= insurance_backing_num
                && source_valid_liened_insurance_num >= insurance_backing_num);
        if counterparty_releasable && insurance_releasable {
            FlatSourceLienNormalizationV16::Release
        } else {
            FlatSourceLienNormalizationV16::None
        }
    }

    /// PRODUCTION KERNEL: every Live account-local obligation serviced by the
    /// refresh continuation must make that continuation actionable. In
    /// particular, clock-driven backing expiry is independent of certificate
    /// epochs, so a still-current certificate cannot suppress expiry progress.
    /// (upstream 0e773c77)
    fn kernel_live_account_refresh_required(
        live: bool,
        cert_current: bool,
        reset_obligation: bool,
        released_obligation: bool,
        lapsed_source_backing: bool,
    ) -> bool {
        live && (!cert_current || reset_obligation || released_obligation || lapsed_source_backing)
    }

    /// PRODUCTION KERNEL: a flat, current, margin-safe Live account with a
    /// normalizable source lien is actionable -- but clock-driven backing expiry
    /// outranks it, so a lapsed bucket must be canonicalized first.
    /// (upstream 6c8d94bc)
    fn kernel_live_flat_source_lien_normalization_required(
        live: bool,
        cert_current: bool,
        lapsed_source_backing: bool,
        flat: bool,
        margin_safe: bool,
        normalizable_lien: bool,
    ) -> bool {
        live && cert_current && !lapsed_source_backing && flat && margin_safe && normalizable_lien
    }

    /// Select the terminal owner-forfeit residual route. An unbookable positive
    /// residual commits Recovery as a successful transition so SVM rollback
    /// cannot erase the only path to resolved settlement. (upstream 650e3fdf)
    pub(crate) fn kernel_forfeit_residual_step(
        residual_remaining: u128,
        booking_capacity: u128,
    ) -> ForfeitResidualStepV16 {
        if residual_remaining == 0 {
            ForfeitResidualStepV16::NoResidual
        } else if booking_capacity == 0 {
            ForfeitResidualStepV16::CommitRecovery
        } else {
            ForfeitResidualStepV16::Book
        }
    }

    fn loss_stale_trade_scope_allowed(
        market_loss_stale_active: bool,
        trade_asset_loss_stale: bool,
        long_account_loss_stale_exposed: bool,
        short_account_loss_stale_exposed: bool,
    ) -> bool {
        market_loss_stale_active
            && !trade_asset_loss_stale
            && !long_account_loss_stale_exposed
            && !short_account_loss_stale_exposed
    }

    fn prepare_asset_recovery_transition(
        mut asset: AssetStateV16,
        asset_set_epoch: u64,
        risk_epoch: u64,
    ) -> V16Result<(AssetStateV16, u64, u64)> {
        match asset.lifecycle {
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly => {
                if asset.effective_price == 0 || asset.effective_price > MAX_ORACLE_PRICE {
                    return Err(V16Error::InvalidConfig);
                }
                let next_asset_set_epoch = asset_set_epoch
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?;
                let next_risk_epoch = risk_epoch.checked_add(1).ok_or(V16Error::CounterOverflow)?;
                asset.lifecycle = AssetLifecycleV16::Recovery;
                asset.raw_oracle_target_price = asset.effective_price;
                Ok((asset, next_asset_set_epoch, next_risk_epoch))
            }
            AssetLifecycleV16::Recovery => Ok((asset, asset_set_epoch, risk_epoch)),
            _ => Err(V16Error::LockActive),
        }
    }

    #[inline]
    fn amount_from_bound_num(bound_num: u128) -> V16Result<u128> {
        let whole = bound_num / BOUND_SCALE;
        let rem = bound_num % BOUND_SCALE;
        if rem == 0 {
            Ok(whole)
        } else {
            whole.checked_add(1).ok_or(V16Error::ArithmeticOverflow)
        }
    }

    #[inline]
    fn bound_num_from_amount(amount: u128) -> V16Result<u128> {
        amount
            .checked_mul(BOUND_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)
    }

    #[inline(always)]
    fn source_credit_lien_amounts_for_effective(
        effective_credit: u128,
        credit_rate_num: u128,
    ) -> V16Result<(u128, u128)> {
        if credit_rate_num == 0 {
            return Err(V16Error::LockActive);
        }
        if credit_rate_num > CREDIT_RATE_SCALE {
            return Err(V16Error::InvalidConfig);
        }
        let required_backing_num = Self::bound_num_from_amount(effective_credit)?;
        if credit_rate_num == CREDIT_RATE_SCALE {
            return Ok((required_backing_num, required_backing_num));
        }
        let required_face_num = Self::mul_div_ceil_u128_or_wide(
            required_backing_num,
            CREDIT_RATE_SCALE,
            credit_rate_num,
        )?;
        Ok((required_face_num, required_backing_num))
    }

    pub(crate) fn first_actionable_slot(
        flags: [bool; V16_MAX_PORTFOLIO_ASSETS_N],
    ) -> Option<usize> {
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            if flags[slot] {
                return Some(slot);
            }
            slot += 1;
        }
        None
    }

    /// PRODUCTION KERNEL: ordinary refresh accrual and liquidation can target
    /// only a live or draining asset. Recovery uses a separate committed-state
    /// refresh fallback and can never be selected for accrual or liquidation.
    fn kernel_auto_crank_lifecycle_dispatchable(lifecycle: AssetLifecycleV16) -> bool {
        matches!(
            lifecycle,
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly
        )
    }

    /// A portfolio-local cache may lag a market-level B update. The canonical
    /// work predicate therefore includes the derived target delta and rejects an
    /// impossible snapshot reversal instead of hiding it as `NoAction`.
    fn kernel_b_settlement_pending(
        cached_stale: bool,
        target_b: u128,
        b_snap: u128,
    ) -> V16Result<bool> {
        if target_b < b_snap {
            return Err(V16Error::RecoveryRequired);
        }
        Ok(cached_stale || target_b > b_snap)
    }

    /// PRODUCTION KERNEL: classify one account leg for the bounded auto-crank
    /// scans. A prior-reset obligation remains refreshable but can never be
    /// dispatched as liquidation work because its effective OI was removed by
    /// the reset.
    #[allow(clippy::too_many_arguments)]
    fn kernel_auto_crank_leg_flags(
        active: bool,
        lifecycle: AssetLifecycleV16,
        basis_pos_q: i128,
        side_oi_q: u128,
        side_mode: SideModeV16,
        asset_epoch: u64,
        leg_epoch_snap: u64,
        b_settlement_pending: bool,
    ) -> (bool, bool, bool, bool) {
        let lifecycle_dispatchable = Self::kernel_auto_crank_lifecycle_dispatchable(lifecycle);
        let prior_reset_obligation =
            Self::kernel_is_prior_reset_obligation(side_mode, asset_epoch, leg_epoch_snap);
        let refresh = active && lifecycle_dispatchable;
        let liquidatable = refresh && basis_pos_q != 0 && side_oi_q != 0 && !prior_reset_obligation;
        (
            active && b_settlement_pending,
            refresh,
            liquidatable,
            active && prior_reset_obligation,
        )
    }

    /// PRODUCTION KERNEL: a refresh detaches at most one settled prior-reset
    /// obligation. A pending close residual owns the account and blocks this
    /// cleanup until its own continuation advances.
    fn kernel_should_clear_prior_reset_obligation(
        already_cleared: bool,
        prior_reset_obligation: bool,
        pending_close_residual: bool,
    ) -> bool {
        !already_cleared && prior_reset_obligation && !pending_close_residual
    }

    fn kernel_auto_crank_refresh_asset(
        refresh_asset: Option<usize>,
        reset_obligation_asset: Option<usize>,
    ) -> Option<usize> {
        refresh_asset.or(reset_obligation_asset)
    }

    fn kernel_refresh_detached_selected_leg(
        selected_leg_before: bool,
        selected_leg_after: bool,
    ) -> bool {
        selected_leg_before && !selected_leg_after
    }

    /// PRODUCTION KERNEL (resolved-bankruptcy settlement): reduce an account's
    /// NEGATIVE PnL by the loss the residual booking just absorbed.
    /// `cleared = min(booked_loss + explicit_loss, |pnl|)` — capped at the
    /// outstanding loss so it can never exceed it — and `new_pnl = pnl + cleared`.
    /// PROVES the loss only SHRINKS toward zero (pnl <= new_pnl <= 0; never
    /// over-cleared into a spurious positive credit) and its magnitude drops by
    /// EXACTLY cleared (|new_pnl| == |pnl| - cleared). Pure scalar; the
    /// resolved-bankruptcy settle glue calls exactly this for the PnL update after
    /// book_bankruptcy_residual_chunk_for_account_core.
    pub(crate) fn kernel_settle_resolved_pnl_after_booking(
        pnl: i128,
        booked_loss: u128,
        explicit_loss: u128,
    ) -> V16Result<i128> {
        let loss = pnl.unsigned_abs();
        let cleared = booked_loss
            .checked_add(explicit_loss)
            .ok_or(V16Error::ArithmeticOverflow)?
            .min(loss);
        let cleared_i128 = i128::try_from(cleared).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = pnl
            .checked_add(cleared_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok(new_pnl)
    }

    /// PRODUCTION KERNEL: a liquidation error is successful public progress only
    /// when the same call committed the matching Recovery state. Every other
    /// error, including an incomplete Recovery marker, remains unchanged.
    fn kernel_commit_declared_liquidation_recovery(
        error: V16Error,
        mode: MarketModeV16,
        reason: Option<PermissionlessRecoveryReasonV16>,
    ) -> V16Result<PermissionlessProgressOutcomeV16> {
        match (error, mode, reason) {
            (V16Error::RecoveryRequired, MarketModeV16::Recovery, Some(reason)) => {
                Ok(PermissionlessProgressOutcomeV16::RecoveryDeclared(reason))
            }
            _ => Err(error),
        }
    }

    pub(crate) fn select_auto_crank_plan(
        summary: ActionableSummaryV16,
        b_stale_slot: usize,
        liq_slot: usize,
        refresh_asset: Option<usize>,
        recovery_reason: PermissionlessRecoveryReasonV16,
    ) -> AutoCrankPlanV16 {
        if summary.expired_close || summary.recovery_eligible {
            AutoCrankPlanV16::DeclareRecovery {
                reason: recovery_reason,
            }
        } else if summary.resolved_winner {
            AutoCrankPlanV16::CloseResolved
        } else if summary.pending_close {
            AutoCrankPlanV16::AdvanceClose
        } else if summary.b_stale {
            AutoCrankPlanV16::SettleBChunk {
                asset_index: b_stale_slot,
            }
        } else if summary.liquidatable {
            AutoCrankPlanV16::Liquidate {
                asset_index: liq_slot,
            }
        } else if summary.source_liens_releasable {
            AutoCrankPlanV16::ReleaseSourceLiens
        } else if summary.stale {
            AutoCrankPlanV16::RefreshAccount {
                asset_index: refresh_asset,
            }
        } else {
            AutoCrankPlanV16::NoAction
        }
    }

    pub(crate) fn actionable_summary_from_signals(
        stale: bool,
        b_stale: bool,
        pending_close: bool,
        expired_close: bool,
        liquidatable: bool,
        source_liens_releasable: bool,
        recovery_eligible: bool,
        resolved_winner: bool,
    ) -> ActionableSummaryV16 {
        ActionableSummaryV16 {
            stale,
            b_stale,
            pending_close,
            expired_close,
            liquidatable,
            source_liens_releasable,
            recovery_eligible,
            resolved_winner,
        }
    }

    /// PRODUCTION KERNEL: the certificate-currentness predicate. A certificate
    /// is current when it is valid, every epoch it was taken under still matches
    /// the market, and the account's active-leg bitmap has not changed since.
    pub(crate) fn kernel_cert_is_current(
        cert: HealthCertV16,
        oracle_epoch: u64,
        funding_epoch: u64,
        risk_epoch: u64,
        asset_set_epoch: u64,
        account_bitmap: V16ActiveBitmap,
    ) -> bool {
        cert.valid
            && cert.cert_oracle_epoch == oracle_epoch
            && cert.cert_funding_epoch == funding_epoch
            && cert.cert_risk_epoch == risk_epoch
            && cert.cert_asset_set_epoch == asset_set_epoch
            && cert.active_bitmap_at_cert == account_bitmap
    }

    fn crystallize_source_lien_fee_for_effective(
        source: &mut PortfolioSourceDomainV16Account,
        impaired_effective: u128,
    ) -> V16Result<u128> {
        let live_effective = source.source_lien_effective_reserved.get();
        if impaired_effective > live_effective {
            return Err(V16Error::CounterUnderflow);
        }
        let live_fee = source.source_lien_capital_at_risk_fee_revenue.get();
        let impaired_fee = if impaired_effective == live_effective {
            live_fee
        } else if impaired_effective == 0 || live_fee == 0 {
            0
        } else {
            wide_mul_div_floor_u128(live_fee, impaired_effective, live_effective)
        };
        source.source_lien_capital_at_risk_fee_revenue = V16PodU128::new(
            live_fee
                .checked_sub(impaired_fee)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_lien_impaired_capital_at_risk_fee_revenue = V16PodU128::new(
            source
                .source_lien_impaired_capital_at_risk_fee_revenue
                .get()
                .checked_add(impaired_fee)
                .ok_or(V16Error::CounterOverflow)?,
        );
        Ok(impaired_fee)
    }

    fn prepare_account_counterparty_lien_impairment(
        mut source: PortfolioSourceDomainV16Account,
    ) -> V16Result<(PortfolioSourceDomainV16Account, u128)> {
        let face = source.source_claim_counterparty_liened_num.get();
        let backing_num = source.source_lien_counterparty_backing_num.get();
        if face == 0 && backing_num == 0 {
            return Ok((source, 0));
        }
        if face == 0 || backing_num == 0 || backing_num % BOUND_SCALE != 0 {
            return Err(V16Error::InvalidLeg);
        }
        let effective = backing_num / BOUND_SCALE;
        if effective == 0 {
            return Err(V16Error::InvalidLeg);
        }

        Self::crystallize_source_lien_fee_for_effective(&mut source, effective)?;
        source.source_claim_counterparty_liened_num = V16PodU128::new(0);
        source.source_claim_liened_num = V16PodU128::new(
            source
                .source_claim_liened_num
                .get()
                .checked_sub(face)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_claim_impaired_num = V16PodU128::new(
            source
                .source_claim_impaired_num
                .get()
                .checked_add(face)
                .ok_or(V16Error::CounterOverflow)?,
        );
        source.source_lien_counterparty_backing_num = V16PodU128::new(0);
        source.source_lien_effective_reserved = V16PodU128::new(
            source
                .source_lien_effective_reserved
                .get()
                .checked_sub(effective)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        // Expired counterparty principal already left the recoverable backing
        // stock. Do not add it to the generic impaired-effective field: that
        // field is backed by impaired insurance and its burn path releases the
        // corresponding insurance reservation. Provider audit labels are
        // retired separately while this account still carries exact provenance.
        source.source_lien_fee_last_slot = V16PodU64::new(0);
        Ok((source, effective))
    }

    #[inline]
    fn source_lien_backing_release_for_face_burn(
        face_locked_num: u128,
        backing_reserved_num: u128,
        face_burn_num: u128,
    ) -> V16Result<u128> {
        if face_burn_num > face_locked_num || backing_reserved_num % BOUND_SCALE != 0 {
            return Err(V16Error::InvalidLeg);
        }
        let effective_reserved = backing_reserved_num / BOUND_SCALE;
        if effective_reserved > Self::amount_from_bound_num(face_locked_num)? {
            return Err(V16Error::InvalidLeg);
        }
        let remaining_face_num = face_locked_num
            .checked_sub(face_burn_num)
            .ok_or(V16Error::CounterUnderflow)?;
        let max_remaining_effective = Self::amount_from_bound_num(remaining_face_num)?;
        let effective_release = effective_reserved.saturating_sub(max_remaining_effective);
        Self::bound_num_from_amount(effective_release)
    }

    #[inline]
    fn source_claim_domain_first_burn_partition(
        source_claim_num: u128,
        burn_num: u128,
    ) -> (u128, u128) {
        let source_burn_num = source_claim_num.min(burn_num);
        (source_burn_num, burn_num - source_burn_num)
    }

    /// PRODUCTION KERNEL: partition a liened-face burn across counterparty then
    /// insurance support without overlap or omission.
    fn source_lien_face_burn_partition(
        counterparty_face_num: u128,
        insurance_face_num: u128,
        face_burn_num: u128,
    ) -> V16Result<(u128, u128)> {
        let total_face_num = counterparty_face_num
            .checked_add(insurance_face_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if face_burn_num > total_face_num {
            return Err(V16Error::CounterUnderflow);
        }
        let counterparty_face_burn = face_burn_num.min(counterparty_face_num);
        let insurance_face_burn = face_burn_num
            .checked_sub(counterparty_face_burn)
            .ok_or(V16Error::CounterUnderflow)?;
        Ok((counterparty_face_burn, insurance_face_burn))
    }

    /// Compose the face partition with the minimum source-local backing release
    /// needed to keep each remaining lien bounded by its remaining face.
    fn source_lien_face_burn_plan(
        counterparty_face_num: u128,
        insurance_face_num: u128,
        counterparty_backing_num: u128,
        insurance_backing_num: u128,
        face_burn_num: u128,
    ) -> V16Result<(u128, u128, u128, u128, u128)> {
        let (counterparty_face_burn, insurance_face_burn) = Self::source_lien_face_burn_partition(
            counterparty_face_num,
            insurance_face_num,
            face_burn_num,
        )?;
        let counterparty_backing_release = Self::source_lien_backing_release_for_face_burn(
            counterparty_face_num,
            counterparty_backing_num,
            counterparty_face_burn,
        )?;
        let insurance_backing_release = Self::source_lien_backing_release_for_face_burn(
            insurance_face_num,
            insurance_backing_num,
            insurance_face_burn,
        )?;
        let backing_release_num = counterparty_backing_release
            .checked_add(insurance_backing_release)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok((
            counterparty_face_burn,
            insurance_face_burn,
            counterparty_backing_release,
            insurance_backing_release,
            backing_release_num,
        ))
    }

    /// PRODUCTION KERNEL: the fee revenue a source lien keeps after part of its
    /// counterparty backing is released. Revenue scales with the backing that
    /// remains, floored so the lien can never keep more than it earned. Releasing
    /// all backing keeps nothing; releasing none keeps everything, without a
    /// round-trip through mul_div. Backing that GREW is a caller error, not a
    /// negative release. (upstream 6276d568)
    fn source_lien_fee_after_backing_release(
        fee_revenue: u128,
        backing_before: u128,
        backing_after: u128,
    ) -> V16Result<u128> {
        if backing_after > backing_before {
            return Err(V16Error::InvalidLeg);
        }
        if backing_after == 0 || fee_revenue == 0 {
            return Ok(0);
        }
        if backing_after == backing_before {
            return Ok(fee_revenue);
        }
        if backing_before == 0 {
            return Err(V16Error::InvalidLeg);
        }
        Ok(wide_mul_div_floor_u128(
            fee_revenue,
            backing_after,
            backing_before,
        ))
    }

    #[inline]
    fn validate_bound_num_atom_aligned(bound_num: u128) -> V16Result<()> {
        if bound_num == 0 {
            return Ok(());
        }
        if bound_num % BOUND_SCALE != 0 {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    #[inline]
    fn validate_positive_pnl_source_attribution(
        pnl: i128,
        source_claim_sum_num: u128,
    ) -> V16Result<()> {
        if pnl <= 0 {
            return Ok(());
        }
        let required = Self::bound_num_from_amount(pnl as u128)?;
        if source_claim_sum_num < required {
            return Err(V16Error::InvalidLeg);
        }
        Ok(())
    }

    #[inline]
    fn accrual_activity_for_asset_segment(
        old: AssetStateV16,
        segment_dt: u64,
        effective_price: u64,
        funding_rate_e9: i128,
    ) -> AccrueAssetOutcomeV16 {
        let exposed = old.oi_eff_long_q != 0 || old.oi_eff_short_q != 0;
        let balanced_exposure = old.oi_eff_long_q != 0 && old.oi_eff_short_q != 0;
        let price_move_active = effective_price != old.effective_price && exposed;
        let funding_active =
            segment_dt > 0 && funding_rate_e9 != 0 && balanced_exposure && old.fund_px_last > 0;
        AccrueAssetOutcomeV16 {
            dt: segment_dt,
            price_move_active,
            funding_active,
            equity_active: price_move_active || funding_active,
            loss_stale_after: false,
        }
    }

    #[inline]
    fn liquidation_progress_from_scores(before: RiskScoreV16, after: RiskScoreV16) -> bool {
        after.strictly_reduces_from(before)
            || after.certified_liq_deficit < before.certified_liq_deficit
    }

    fn available_backing_num_for_source_credit_state(
        state: SourceCreditStateV16,
    ) -> V16Result<u128> {
        if state.fresh_reserved_backing_num < state.valid_liened_backing_num {
            return Err(V16Error::InvalidConfig);
        }
        let insurance_encumbered = state
            .valid_liened_insurance_num
            .checked_add(state.impaired_liened_insurance_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if state.insurance_credit_reserved_num < insurance_encumbered {
            return Err(V16Error::InvalidConfig);
        }
        (state.fresh_reserved_backing_num - state.valid_liened_backing_num)
            .checked_add(state.insurance_credit_reserved_num - insurance_encumbered)
            .ok_or(V16Error::ArithmeticOverflow)
    }

    fn expected_source_credit_rate_num_for_state(state: SourceCreditStateV16) -> V16Result<u128> {
        Self::validate_source_credit_state_shape_static(state)?;
        if state.positive_claim_bound_num == 0 {
            return Ok(CREDIT_RATE_SCALE);
        }
        let available = Self::available_backing_num_for_source_credit_state(state)?;
        if available == 0 {
            return Ok(0);
        }
        let rate = U256::from_u128(available)
            .checked_mul(U256::from_u128(CREDIT_RATE_SCALE))
            .and_then(|v| v.checked_div(U256::from_u128(state.positive_claim_bound_num)))
            .and_then(|v| v.try_into_u128())
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok(core::cmp::min(rate, CREDIT_RATE_SCALE))
    }

    fn validate_source_credit_state_shape_static(state: SourceCreditStateV16) -> V16Result<()> {
        if state == SourceCreditStateV16::EMPTY {
            return Ok(());
        }
        Self::validate_bound_num_atom_aligned(state.insurance_credit_reserved_num)?;
        Self::validate_bound_num_atom_aligned(state.valid_liened_insurance_num)?;
        Self::validate_bound_num_atom_aligned(state.impaired_liened_insurance_num)?;
        if state.exact_positive_claim_num > state.positive_claim_bound_num
            || state.credit_rate_num > CREDIT_RATE_SCALE
            || state.spent_backing_num < state.provider_receivable_num
        {
            return Err(V16Error::InvalidConfig);
        }
        Self::available_backing_num_for_source_credit_state(state).map(|_| ())
    }

    fn validate_source_credit_state_static(state: SourceCreditStateV16) -> V16Result<()> {
        Self::validate_source_credit_state_shape_static(state)?;
        if state.credit_rate_num != Self::expected_source_credit_rate_num_for_state(state)? {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    fn validate_backing_bucket_static(bucket: BackingBucketV16) -> V16Result<()> {
        match bucket.status {
            BackingBucketStatusV16::Empty => {
                if !bucket.is_empty_amount_shape() {
                    return Err(V16Error::InvalidConfig);
                }
            }
            BackingBucketStatusV16::Fresh => {
                if bucket.market_id == 0
                    || bucket.expiry_slot == 0
                    || bucket
                        .fresh_unliened_backing_num
                        .checked_add(bucket.valid_liened_backing_num)
                        .ok_or(V16Error::ArithmeticOverflow)?
                        == 0
                {
                    return Err(V16Error::InvalidConfig);
                }
            }
            BackingBucketStatusV16::Expired => {
                if bucket.market_id == 0
                    || bucket.fresh_unliened_backing_num != 0
                    || bucket.valid_liened_backing_num != 0
                    || bucket.impaired_liened_backing_num != 0
                {
                    return Err(V16Error::InvalidConfig);
                }
            }
            BackingBucketStatusV16::Impaired => {
                if bucket.market_id == 0
                    || bucket.fresh_unliened_backing_num != 0
                    || bucket.valid_liened_backing_num != 0
                    || bucket.impaired_liened_backing_num == 0
                {
                    return Err(V16Error::InvalidConfig);
                }
            }
        }
        Ok(())
    }

    fn validate_insurance_reservation_static(
        reservation: InsuranceCreditReservationV16,
    ) -> V16Result<()> {
        if reservation == InsuranceCreditReservationV16::EMPTY {
            return Ok(());
        }
        Self::validate_bound_num_atom_aligned(reservation.insurance_credit_reserved_num)?;
        Self::validate_bound_num_atom_aligned(reservation.valid_liened_insurance_num)?;
        Self::validate_bound_num_atom_aligned(reservation.impaired_liened_insurance_num)?;
        let encumbered = reservation
            .valid_liened_insurance_num
            .checked_add(reservation.impaired_liened_insurance_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if reservation.insurance_credit_reserved_num < encumbered {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    fn validate_source_domain_ledger_parts(
        expected_market_id: u64,
        source: SourceCreditStateV16,
        bucket: BackingBucketV16,
        reservation: InsuranceCreditReservationV16,
    ) -> V16Result<()> {
        Self::validate_source_credit_state_static(source)?;
        Self::validate_backing_bucket_static(bucket)?;
        Self::validate_insurance_reservation_static(reservation)?;
        if expected_market_id == 0 {
            if source == SourceCreditStateV16::EMPTY
                && bucket == BackingBucketV16::EMPTY
                && reservation == InsuranceCreditReservationV16::EMPTY
            {
                return Ok(());
            }
            return Err(V16Error::InvalidConfig);
        }
        if bucket.market_id != expected_market_id {
            return Err(V16Error::InvalidConfig);
        }
        let fresh_reserved = bucket
            .fresh_unliened_backing_num
            .checked_add(bucket.valid_liened_backing_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if source.fresh_reserved_backing_num != fresh_reserved
            || source.provider_receivable_num != bucket.consumed_liened_backing_num
            || source.valid_liened_backing_num != bucket.valid_liened_backing_num
            || source.impaired_liened_backing_num != bucket.impaired_liened_backing_num
            || source.insurance_credit_reserved_num != reservation.insurance_credit_reserved_num
            || source.valid_liened_insurance_num != reservation.valid_liened_insurance_num
            || source.impaired_liened_insurance_num != reservation.impaired_liened_insurance_num
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    fn prepare_source_credit_domain_recompute_for_epoch(
        source: SourceCreditStateV16,
        risk_epoch: u64,
    ) -> V16Result<(SourceCreditStateV16, u64)> {
        Self::prepare_source_credit_domain_recompute_for_epoch_steps(source, risk_epoch, 1)
    }

    fn prepare_source_credit_domain_recompute_for_epoch_steps(
        mut source: SourceCreditStateV16,
        risk_epoch: u64,
        epoch_steps: u64,
    ) -> V16Result<(SourceCreditStateV16, u64)> {
        if epoch_steps == 0 {
            return Err(V16Error::InvalidConfig);
        }
        source.credit_rate_num = Self::expected_source_credit_rate_num_for_state(source)?;
        source.credit_epoch = source
            .credit_epoch
            .checked_add(epoch_steps)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((
            source,
            risk_epoch
                .checked_add(epoch_steps)
                .ok_or(V16Error::CounterOverflow)?,
        ))
    }

    /// Burns a source-attributed positive claim without touching backing,
    /// insurance, or epoch state. The caller composes this delta with the
    /// backing-consumption delta and performs one credit-rate recomputation.
    #[inline(always)]
    fn prepare_source_positive_claim_burn_delta(
        mut source: SourceCreditStateV16,
        face_burn_num: u128,
    ) -> V16Result<SourceCreditStateV16> {
        source.positive_claim_bound_num = source
            .positive_claim_bound_num
            .checked_sub(face_burn_num)
            .ok_or(V16Error::CounterUnderflow)?;
        source.exact_positive_claim_num = source
            .exact_positive_claim_num
            .checked_sub(face_burn_num.min(source.exact_positive_claim_num))
            .ok_or(V16Error::CounterUnderflow)?;
        Ok(source)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn prepare_source_positive_claim_bound_delta(
        mut source: SourceCreditStateV16,
        claim_bound_num: u128,
        exact_claim_num: u128,
    ) -> V16Result<SourceCreditStateV16> {
        if exact_claim_num > claim_bound_num {
            return Err(V16Error::InvalidConfig);
        }
        source.positive_claim_bound_num = source
            .positive_claim_bound_num
            .checked_add(claim_bound_num)
            .ok_or(V16Error::CounterOverflow)?;
        source.exact_positive_claim_num = source
            .exact_positive_claim_num
            .checked_add(exact_claim_num)
            .ok_or(V16Error::CounterOverflow)?;
        Ok(source)
    }

    fn prepare_counterparty_lien_create_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        current_slot: u64,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        if bucket.status != BackingBucketStatusV16::Fresh
            || bucket.expiry_slot <= current_slot
            || bucket.fresh_unliened_backing_num < amount
        {
            return Err(V16Error::LockActive);
        }
        bucket.fresh_unliened_backing_num -= amount;
        bucket.valid_liened_backing_num = bucket
            .valid_liened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.valid_liened_backing_num = source
            .valid_liened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((bucket, source))
    }

    fn prepare_counterparty_backing_add_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        amount: u128,
        current_slot: u64,
        expiry_slot: u64,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 || expiry_slot <= current_slot {
            return Err(V16Error::InvalidConfig);
        }
        if source.provider_receivable_num != bucket.consumed_liened_backing_num
            || source.spent_backing_num < source.provider_receivable_num
        {
            return Err(V16Error::InvalidConfig);
        }
        match bucket.status {
            BackingBucketStatusV16::Empty | BackingBucketStatusV16::Expired => {
                bucket.status = BackingBucketStatusV16::Fresh;
                bucket.expiry_slot = expiry_slot;
            }
            BackingBucketStatusV16::Fresh if bucket.expiry_slot == expiry_slot => {}
            _ => return Err(V16Error::LockActive),
        }
        let refill = amount.min(source.provider_receivable_num);
        if refill > bucket.consumed_liened_backing_num {
            return Err(V16Error::CounterUnderflow);
        }
        bucket.consumed_liened_backing_num -= refill;
        source.provider_receivable_num -= refill;
        bucket.fresh_unliened_backing_num = bucket
            .fresh_unliened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.fresh_reserved_backing_num = source
            .fresh_reserved_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((bucket, source))
    }

    fn prepare_counterparty_backing_withdraw_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        if bucket.status != BackingBucketStatusV16::Fresh
            || bucket.fresh_unliened_backing_num < amount
            || source.fresh_reserved_backing_num < amount
        {
            return Err(V16Error::LockActive);
        }
        bucket.fresh_unliened_backing_num -= amount;
        source.fresh_reserved_backing_num -= amount;
        if bucket.fresh_unliened_backing_num == 0 && bucket.valid_liened_backing_num == 0 {
            if bucket.impaired_liened_backing_num != 0 {
                bucket.status = BackingBucketStatusV16::Impaired;
            } else if bucket.consumed_liened_backing_num != 0 {
                bucket.status = BackingBucketStatusV16::Expired;
            } else {
                bucket.status = BackingBucketStatusV16::Empty;
                bucket.expiry_slot = 0;
            }
        }
        Ok((bucket, source))
    }

    // #137: NOT cfg-gated. The Live release path must exist in the deployed
    // binary; gating it to kani/fuzz is what left the IM lien permanent.
    fn prepare_counterparty_lien_release_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        current_slot: u64,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        if bucket.status != BackingBucketStatusV16::Fresh
            || bucket.expiry_slot <= current_slot
            || bucket.valid_liened_backing_num < amount
            || source.valid_liened_backing_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        bucket.valid_liened_backing_num -= amount;
        bucket.fresh_unliened_backing_num = bucket
            .fresh_unliened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.valid_liened_backing_num -= amount;
        Ok((bucket, source))
    }

    // Expiry-agnostic counterparty lien release for terminal (Resolved) wind-down.
    // Identical to prepare_counterparty_lien_release_delta but WITHOUT the lending-time
    // freshness guard (Fresh status / expiry_slot > current_slot): unwinding returns
    // liened backing to the provider's unliened pool, it is not re-lending, so a
    // time-expired bucket must not block it. Without this, a market that resolves past a
    // backing bucket's expiry re-introduces the Finding-A close deadlock.
    fn prepare_counterparty_lien_terminal_release_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        // LIEN-1 fix (issue #116): split into a still-VALID portion (returned to the provider's
        // unliened pool) and an already-IMPAIRED portion. The per-(asset,side) backing bucket +
        // source-credit are SHARED across accounts; a bucket expiry (the shared bucket's expiry_slot
        // lapsing while a co-tenant winner's resolved close runs) forfeits the WHOLE remaining
        // valid_liened — including THIS account's live share — to impaired via
        // expire_source_backing_bucket_not_atomic. Without the impaired arm below, this account's
        // terminal release underflows the emptied valid counter and can never close. Mirrors the
        // insurance twin prepare_insurance_lien_terminal_release_delta. The impaired drain ONLY
        // clears the impaired counters — it must NOT re-credit fresh_unliened/fresh_reserved (expiry
        // already removed that backing once; re-crediting would double-count the senior backing).
        let valid_release = amount.min(bucket.valid_liened_backing_num);
        if source.valid_liened_backing_num < valid_release {
            return Err(V16Error::CounterUnderflow);
        }
        let impaired_release = amount
            .checked_sub(valid_release)
            .ok_or(V16Error::CounterUnderflow)?;
        if bucket.impaired_liened_backing_num < impaired_release
            || source.impaired_liened_backing_num < impaired_release
        {
            return Err(V16Error::CounterUnderflow);
        }
        bucket.valid_liened_backing_num -= valid_release;
        bucket.fresh_unliened_backing_num = bucket
            .fresh_unliened_backing_num
            .checked_add(valid_release)
            .ok_or(V16Error::CounterOverflow)?;
        source.valid_liened_backing_num -= valid_release;
        bucket.impaired_liened_backing_num -= impaired_release;
        source.impaired_liened_backing_num -= impaired_release;
        // Status fix-up: validate_backing_bucket_static requires an Impaired bucket to keep
        // impaired_liened > 0. If the impaired drain empties the bucket entirely, route it to Expired
        // (residue remains in consumed/util) or Empty (fully bare, expiry_slot cleared), matching the
        // empties-bucket transition in prepare_counterparty_lien_consume_delta.
        if impaired_release != 0
            && bucket.fresh_unliened_backing_num == 0
            && bucket.valid_liened_backing_num == 0
            && bucket.impaired_liened_backing_num == 0
        {
            if bucket.consumed_liened_backing_num != 0 || bucket.utilization_fee_earnings != 0 {
                bucket.status = BackingBucketStatusV16::Expired;
            } else {
                bucket.status = BackingBucketStatusV16::Empty;
                bucket.expiry_slot = 0;
            }
        }
        Ok((bucket, source))
    }

    fn prepare_counterparty_lien_consume_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        if bucket.valid_liened_backing_num < amount
            || source.valid_liened_backing_num < amount
            || source.fresh_reserved_backing_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        bucket.valid_liened_backing_num -= amount;
        bucket.consumed_liened_backing_num = bucket
            .consumed_liened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        if bucket.fresh_unliened_backing_num == 0
            && bucket.valid_liened_backing_num == 0
            && bucket.impaired_liened_backing_num == 0
        {
            bucket.status = BackingBucketStatusV16::Expired;
        }
        source.valid_liened_backing_num -= amount;
        source.fresh_reserved_backing_num -= amount;
        source.spent_backing_num = source
            .spent_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.provider_receivable_num = source
            .provider_receivable_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((bucket, source))
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn prepare_counterparty_lien_impair_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        if bucket.valid_liened_backing_num < amount
            || source.valid_liened_backing_num < amount
            || source.fresh_reserved_backing_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        bucket.valid_liened_backing_num -= amount;
        bucket.impaired_liened_backing_num = bucket
            .impaired_liened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        if bucket.valid_liened_backing_num == 0 && bucket.fresh_unliened_backing_num == 0 {
            bucket.status = BackingBucketStatusV16::Impaired;
        }
        source.valid_liened_backing_num -= amount;
        source.fresh_reserved_backing_num -= amount;
        source.impaired_liened_backing_num = source
            .impaired_liened_backing_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((bucket, source))
    }

    /// Retire provider-backed lien labels after expiry has already forfeited
    /// their principal into the junior residual pool. The account still carries
    /// the exact counterparty amount at this point, so this transition preserves
    /// provenance and remains order-independent across accounts in one domain.
    fn prepare_counterparty_impaired_lien_retirement_delta(
        mut bucket: BackingBucketV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((bucket, source));
        }
        Self::validate_bound_num_atom_aligned(amount)?;
        if bucket.status != BackingBucketStatusV16::Impaired
            || bucket.fresh_unliened_backing_num != 0
            || bucket.valid_liened_backing_num != 0
            || bucket.impaired_liened_backing_num < amount
            || source.impaired_liened_backing_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        bucket.impaired_liened_backing_num -= amount;
        source.impaired_liened_backing_num -= amount;
        if bucket.impaired_liened_backing_num == 0 {
            bucket.status = BackingBucketStatusV16::Expired;
        }
        Ok((bucket, source))
    }

    fn prepare_insurance_lien_consume_delta(
        mut reservation: InsuranceCreditReservationV16,
        mut source: SourceCreditStateV16,
        domain_spent: u128,
        insurance: u128,
        amount: u128,
    ) -> V16Result<(
        InsuranceCreditReservationV16,
        SourceCreditStateV16,
        u128,
        u128,
    )> {
        if amount == 0 {
            return Ok((reservation, source, domain_spent, insurance));
        }
        Self::validate_bound_num_atom_aligned(amount)?;
        let spend_atoms = Self::amount_from_bound_num(amount)?;
        if reservation.valid_liened_insurance_num < amount
            || reservation.insurance_credit_reserved_num < amount
            || source.valid_liened_insurance_num < amount
            || source.insurance_credit_reserved_num < amount
            || insurance < spend_atoms
        {
            return Err(V16Error::CounterUnderflow);
        }
        reservation.valid_liened_insurance_num -= amount;
        reservation.insurance_credit_reserved_num -= amount;
        reservation.consumed_insurance_num = reservation
            .consumed_insurance_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.valid_liened_insurance_num -= amount;
        source.insurance_credit_reserved_num -= amount;
        Ok((
            reservation,
            source,
            domain_spent
                .checked_add(spend_atoms)
                .ok_or(V16Error::CounterOverflow)?,
            insurance - spend_atoms,
        ))
    }

    fn prepare_insurance_lien_create_delta(
        mut reservation: InsuranceCreditReservationV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(InsuranceCreditReservationV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((reservation, source));
        }
        Self::validate_bound_num_atom_aligned(amount)?;
        let encumbered = reservation
            .valid_liened_insurance_num
            .checked_add(reservation.impaired_liened_insurance_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if reservation
            .insurance_credit_reserved_num
            .checked_sub(encumbered)
            .ok_or(V16Error::CounterUnderflow)?
            < amount
        {
            return Err(V16Error::LockActive);
        }
        reservation.valid_liened_insurance_num = reservation
            .valid_liened_insurance_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.valid_liened_insurance_num = source
            .valid_liened_insurance_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((reservation, source))
    }

    // #137: NOT cfg-gated. The Live release path must exist in the deployed
    // binary; gating it to kani/fuzz is what left the IM lien permanent.
    fn prepare_insurance_lien_release_delta(
        mut reservation: InsuranceCreditReservationV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(InsuranceCreditReservationV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((reservation, source));
        }
        Self::validate_bound_num_atom_aligned(amount)?;
        if reservation.valid_liened_insurance_num < amount
            || source.valid_liened_insurance_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        reservation.valid_liened_insurance_num -= amount;
        source.valid_liened_insurance_num -= amount;
        Ok((reservation, source))
    }

    fn prepare_insurance_lien_terminal_release_delta(
        mut reservation: InsuranceCreditReservationV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(InsuranceCreditReservationV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((reservation, source));
        }
        Self::validate_bound_num_atom_aligned(amount)?;
        if reservation.insurance_credit_reserved_num < amount
            || source.insurance_credit_reserved_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        let valid_release = amount.min(reservation.valid_liened_insurance_num);
        if source.valid_liened_insurance_num < valid_release {
            return Err(V16Error::CounterUnderflow);
        }
        let impaired_release = amount
            .checked_sub(valid_release)
            .ok_or(V16Error::CounterUnderflow)?;
        if reservation.impaired_liened_insurance_num < impaired_release
            || source.impaired_liened_insurance_num < impaired_release
        {
            return Err(V16Error::CounterUnderflow);
        }
        reservation.valid_liened_insurance_num -= valid_release;
        source.valid_liened_insurance_num -= valid_release;
        reservation.impaired_liened_insurance_num -= impaired_release;
        source.impaired_liened_insurance_num -= impaired_release;
        reservation.insurance_credit_reserved_num -= amount;
        source.insurance_credit_reserved_num -= amount;
        Ok((reservation, source))
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn prepare_insurance_lien_impair_delta(
        mut reservation: InsuranceCreditReservationV16,
        mut source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(InsuranceCreditReservationV16, SourceCreditStateV16)> {
        if amount == 0 {
            return Ok((reservation, source));
        }
        Self::validate_bound_num_atom_aligned(amount)?;
        if reservation.valid_liened_insurance_num < amount
            || source.valid_liened_insurance_num < amount
        {
            return Err(V16Error::CounterUnderflow);
        }
        reservation.valid_liened_insurance_num -= amount;
        reservation.impaired_liened_insurance_num = reservation
            .impaired_liened_insurance_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        source.valid_liened_insurance_num -= amount;
        source.impaired_liened_insurance_num = source
            .impaired_liened_insurance_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((reservation, source))
    }

    // Source domains settle whole quote atoms independently. Round before a
    // caller aggregates domains so fractional backing cannot become phantom support.
    fn source_credit_state_realizable_support_for_claim_num(
        state: SourceCreditStateV16,
        claim_num: u128,
    ) -> V16Result<u128> {
        if claim_num == 0 || state.positive_claim_bound_num == 0 {
            return Ok(0);
        }
        let credited_num =
            Self::mul_div_floor_u128_or_wide(claim_num, state.credit_rate_num, CREDIT_RATE_SCALE)?;
        Ok((credited_num / BOUND_SCALE)
            .min(Self::available_backing_num_for_source_credit_state(state)? / BOUND_SCALE))
    }

    fn source_credit_state_realizable_support_for_face(
        state: SourceCreditStateV16,
        face_claim: u128,
    ) -> V16Result<u128> {
        Self::source_credit_state_realizable_support_for_claim_num(
            state,
            Self::bound_num_from_amount(face_claim)?,
        )
    }

    fn target_effective_lag_loss_penalty(
        abs_pos_q: u128,
        side: SideV16,
        effective_price: u64,
        raw_target_price: u64,
    ) -> V16Result<u128> {
        let adverse_delta =
            Self::target_effective_lag_adverse_delta(side, effective_price, raw_target_price);
        risk_notional_ceil(abs_pos_q, adverse_delta)
    }

    fn target_effective_lag_adverse_delta(
        side: SideV16,
        effective_price: u64,
        raw_target_price: u64,
    ) -> u64 {
        match side {
            SideV16::Long if raw_target_price < effective_price => {
                effective_price - raw_target_price
            }
            SideV16::Short if raw_target_price > effective_price => {
                raw_target_price - effective_price
            }
            _ => 0,
        }
    }

    fn health_requirements_from_notional_and_target_lag(
        config: V16Config,
        risk_notional: u128,
        target_lag_penalty: u128,
    ) -> V16Result<(u128, u128, u128)> {
        let base_initial = margin_requirement(
            risk_notional,
            config.initial_margin_bps,
            config.min_nonzero_im_req,
        )?;
        let base_maintenance = margin_requirement(
            risk_notional,
            config.maintenance_margin_bps,
            config.min_nonzero_mm_req,
        )?;
        Self::health_requirements_from_base_and_target_lag(
            base_initial,
            base_maintenance,
            risk_notional,
            target_lag_penalty,
        )
    }

    fn health_requirements_from_base_and_target_lag(
        base_initial: u128,
        base_maintenance: u128,
        risk_notional: u128,
        target_lag_penalty: u128,
    ) -> V16Result<(u128, u128, u128)> {
        Ok((
            base_initial
                .checked_add(target_lag_penalty)
                .ok_or(V16Error::ArithmeticOverflow)?,
            base_maintenance
                .checked_add(target_lag_penalty)
                .ok_or(V16Error::ArithmeticOverflow)?,
            risk_notional
                .checked_add(target_lag_penalty)
                .ok_or(V16Error::ArithmeticOverflow)?,
        ))
    }

    fn backing_utilization_rate_e9_for_source_state(
        config: V16Config,
        source: SourceCreditStateV16,
    ) -> V16Result<u64> {
        config.validate_public_user_fund_shape()?;
        if source.valid_liened_backing_num == 0 {
            return Ok(0);
        }
        if source.fresh_reserved_backing_num == 0
            || source.valid_liened_backing_num > source.fresh_reserved_backing_num
        {
            return Err(V16Error::InvalidConfig);
        }
        let util_bps = U256::from_u128(source.valid_liened_backing_num)
            .checked_mul(U256::from_u64(MAX_BACKING_FEE_UTIL_BPS))
            .and_then(|v| v.checked_div(U256::from_u128(source.fresh_reserved_backing_num)))
            .and_then(|v| v.try_into_u128())
            .ok_or(V16Error::ArithmeticOverflow)? as u64;
        let kink = config.backing_fee_kink_util_bps;
        let rate = if util_bps <= kink {
            let slope = U256::from_u64(config.backing_fee_slope_at_kink_e9_per_slot)
                .checked_mul(U256::from_u64(util_bps))
                .and_then(|v| v.checked_div(U256::from_u64(kink)))
                .and_then(|v| v.try_into_u128())
                .ok_or(V16Error::ArithmeticOverflow)? as u64;
            config
                .backing_fee_base_rate_e9_per_slot
                .checked_add(slope)
                .ok_or(V16Error::ArithmeticOverflow)?
        } else {
            let above_den = MAX_BACKING_FEE_UTIL_BPS
                .checked_sub(kink)
                .ok_or(V16Error::InvalidConfig)?;
            let above_num = util_bps.checked_sub(kink).ok_or(V16Error::InvalidConfig)?;
            let above_slope = U256::from_u64(config.backing_fee_slope_above_kink_e9_per_slot)
                .checked_mul(U256::from_u64(above_num))
                .and_then(|v| v.checked_div(U256::from_u64(above_den)))
                .and_then(|v| v.try_into_u128())
                .ok_or(V16Error::ArithmeticOverflow)? as u64;
            config
                .backing_fee_base_rate_e9_per_slot
                .checked_add(config.backing_fee_slope_at_kink_e9_per_slot)
                .and_then(|v| v.checked_add(above_slope))
                .ok_or(V16Error::ArithmeticOverflow)?
        };
        if rate > MAX_BACKING_FEE_RATE_E9_PER_SLOT {
            return Err(V16Error::InvalidConfig);
        }
        Ok(rate)
    }

    fn backing_utilization_fee_quote_atoms_for_lien(
        config: V16Config,
        source: SourceCreditStateV16,
        lien_backing_num: u128,
        from_slot: u64,
        to_slot: u64,
    ) -> V16Result<u128> {
        if lien_backing_num == 0 || to_slot <= from_slot {
            return Ok(0);
        }
        let rate = Self::backing_utilization_rate_e9_for_source_state(config, source)?;
        if rate == 0 {
            return Ok(0);
        }
        let den = BACKING_FEE_RATE_DEN_E9
            .checked_mul(BOUND_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        U256::from_u128(lien_backing_num)
            .checked_mul(U256::from_u64(rate))
            .and_then(|v| v.checked_mul(U256::from_u64(to_slot - from_slot)))
            .and_then(|v| v.checked_div(U256::from_u128(den)))
            .and_then(|v| v.try_into_u128())
            .ok_or(V16Error::ArithmeticOverflow)
    }
}

#[cfg(kani)]
pub fn kani_validate_positive_pnl_source_attribution(
    pnl: i128,
    source_claim_sum_num: u128,
) -> V16Result<()> {
    V16Core::validate_positive_pnl_source_attribution(pnl, source_claim_sum_num)
}

#[cfg(kani)]
pub fn kani_expected_source_credit_rate_num_for_state(
    state: SourceCreditStateV16,
) -> V16Result<u128> {
    V16Core::expected_source_credit_rate_num_for_state(state)
}

#[cfg(kani)]
pub fn kani_available_backing_num_for_source_credit_state(
    state: SourceCreditStateV16,
) -> V16Result<u128> {
    V16Core::available_backing_num_for_source_credit_state(state)
}

/// REALIZABILITY — the no-DoS auto-crank dispatch-seam invariant.
///
/// `RefreshAccount { asset_index: None }` is the UNIQUE [`AutoCrankPlanV16`] whose
/// dispatch hard-requires a caller-supplied oracle observation: there is no active
/// account leg from which to choose a committed asset, so it must accrue a NEW
/// price. `RefreshAccount { asset_index: Some(_) }` and EVERY other plan are
/// dispatchable from committed on-chain state alone — `SettleBChunk` ignores
/// price, `Liquidate` reads the current health cert, and `AdvanceClose` /
/// `DeclareRecovery` / `FinalizeRecovery` / `CloseResolved` / `NoAction` take no
/// price — so a keeper
/// holding no fresh observation can still drive the account forward (no liveness
/// stall). A wrapper
/// may call this to decide whether it must source an oracle observation before
/// cranking.
///
/// The exhaustive match forces a conscious classification if a plan variant is
/// added. `proof_v16_auto_crank_refresh_is_unique_observation_requiring_plan` pins
/// this truth table, and the spec matrix
/// `v16_auto_crank_progress_realizable_without_observation_for_every_class` ties
/// it to the REAL dispatch for every reachable ActionableState class — so the
/// predicate cannot silently drift from behaviour. This is the seam that hid the
/// b-stale / committed-state-liquidation stall before the observation fallback.
pub fn auto_crank_plan_requires_caller_observation(plan: &AutoCrankPlanV16) -> bool {
    match plan {
        AutoCrankPlanV16::RefreshAccount { asset_index } => asset_index.is_none(),
        AutoCrankPlanV16::AdvanceClose
        | AutoCrankPlanV16::SettleBChunk { .. }
        | AutoCrankPlanV16::Liquidate { .. }
        | AutoCrankPlanV16::ReleaseSourceLiens
        | AutoCrankPlanV16::DeclareRecovery { .. }
        | AutoCrankPlanV16::FinalizeRecovery
        | AutoCrankPlanV16::CloseResolved
        | AutoCrankPlanV16::NoAction => false,
    }
}

#[cfg(kani)]
pub fn kani_b_settlement_pending(
    cached_stale: bool,
    target_b: u128,
    b_snap: u128,
) -> V16Result<bool> {
    V16Core::kernel_b_settlement_pending(cached_stale, target_b, b_snap)
}

#[cfg(kani)]
#[allow(clippy::too_many_arguments)]
pub fn kani_auto_crank_leg_flags(
    active: bool,
    lifecycle: AssetLifecycleV16,
    basis_pos_q: i128,
    side_oi_q: u128,
    side_mode: SideModeV16,
    asset_epoch: u64,
    leg_epoch_snap: u64,
    b_settlement_pending: bool,
) -> (bool, bool, bool, bool) {
    V16Core::kernel_auto_crank_leg_flags(
        active,
        lifecycle,
        basis_pos_q,
        side_oi_q,
        side_mode,
        asset_epoch,
        leg_epoch_snap,
        b_settlement_pending,
    )
}

#[cfg(kani)]
pub fn kani_should_clear_prior_reset_obligation(
    already_cleared: bool,
    prior_reset_obligation: bool,
    pending_close_residual: bool,
) -> bool {
    V16Core::kernel_should_clear_prior_reset_obligation(
        already_cleared,
        prior_reset_obligation,
        pending_close_residual,
    )
}

#[cfg(kani)]
pub fn kani_auto_crank_refresh_asset(
    refresh_asset: Option<usize>,
    reset_obligation_asset: Option<usize>,
) -> Option<usize> {
    V16Core::kernel_auto_crank_refresh_asset(refresh_asset, reset_obligation_asset)
}

#[cfg(kani)]
pub fn kani_refresh_detached_selected_leg(
    selected_leg_before: bool,
    selected_leg_after: bool,
) -> bool {
    V16Core::kernel_refresh_detached_selected_leg(selected_leg_before, selected_leg_after)
}

#[cfg(kani)]
pub fn kani_settle_resolved_pnl_after_booking(
    pnl: i128,
    booked_loss: u128,
    explicit_loss: u128,
) -> V16Result<i128> {
    V16Core::kernel_settle_resolved_pnl_after_booking(pnl, booked_loss, explicit_loss)
}

#[cfg(kani)]
pub fn kani_commit_declared_liquidation_recovery(
    error: V16Error,
    mode: MarketModeV16,
    reason: Option<PermissionlessRecoveryReasonV16>,
) -> V16Result<PermissionlessProgressOutcomeV16> {
    V16Core::kernel_commit_declared_liquidation_recovery(error, mode, reason)
}

#[cfg(kani)]
pub fn kani_auto_crank_lifecycle_dispatchable(lifecycle: AssetLifecycleV16) -> bool {
    V16Core::kernel_auto_crank_lifecycle_dispatchable(lifecycle)
}

#[cfg(kani)]
pub fn kani_first_actionable_slot(flags: [bool; V16_MAX_PORTFOLIO_ASSETS_N]) -> Option<usize> {
    V16Core::first_actionable_slot(flags)
}

#[cfg(kani)]
pub fn kani_select_auto_crank_plan(
    summary: ActionableSummaryV16,
    b_stale_asset_index: usize,
    liquidate_asset_index: usize,
    refresh_asset_index: Option<usize>,
    recovery_reason: PermissionlessRecoveryReasonV16,
) -> AutoCrankPlanV16 {
    V16Core::select_auto_crank_plan(
        summary,
        b_stale_asset_index,
        liquidate_asset_index,
        refresh_asset_index,
        recovery_reason,
    )
}

#[cfg(kani)]
pub fn kani_cert_is_current(
    cert: HealthCertV16,
    oracle_epoch: u64,
    funding_epoch: u64,
    risk_epoch: u64,
    asset_set_epoch: u64,
    account_bitmap: V16ActiveBitmap,
) -> bool {
    V16Core::kernel_cert_is_current(
        cert,
        oracle_epoch,
        funding_epoch,
        risk_epoch,
        asset_set_epoch,
        account_bitmap,
    )
}

#[cfg(kani)]
pub fn kani_kernel_advance_close_ledger(
    ledger: CloseProgressLedgerV16,
    support_consumed: u128,
    junior_face_burned: u128,
    insurance_spent: u128,
    b_loss_booked: u128,
    explicit_loss_assigned: u128,
) -> V16Result<CloseProgressLedgerV16> {
    V16Core::kernel_advance_close_ledger(
        ledger,
        support_consumed,
        junior_face_burned,
        insurance_spent,
        b_loss_booked,
        explicit_loss_assigned,
    )
}

#[cfg(kani)]
pub fn kani_kernel_advance_leg_b_snap(
    leg: PortfolioLegV16,
    delta_b: u128,
    new_remainder: u128,
    remaining_after: u128,
) -> V16Result<PortfolioLegV16> {
    V16Core::kernel_advance_leg_b_snap(leg, delta_b, new_remainder, remaining_after)
}

#[cfg(kani)]
pub fn kani_kernel_settle_principal(
    capital: u128,
    c_tot: u128,
    pnl: i128,
) -> V16Result<(u128, u128, u128, i128)> {
    V16Core::kernel_settle_principal(capital, c_tot, pnl)
}

#[cfg(kani)]
pub fn kani_kernel_initial_margin_gate(cert: HealthCertV16) -> V16Result<()> {
    V16Core::kernel_initial_margin_gate(cert)
}

#[cfg(kani)]
pub fn kani_kernel_locked_margin_gate(
    capital: u128,
    pnl: i128,
    fee_credits: i128,
    certified_initial_req: u128,
) -> V16Result<()> {
    V16Core::kernel_locked_margin_gate(capital, pnl, fee_credits, certified_initial_req)
}

#[cfg(kani)]
#[allow(clippy::too_many_arguments)]
pub fn kani_kernel_accumulate_batch_trade(
    outcome: BatchTradeOutcomeV16,
    risk_increasing: bool,
    long_has_source_claims: bool,
    short_has_source_claims: bool,
    applied_fee_a: u128,
    applied_fee_b: u128,
    applied_notional: u128,
    applied_risk_increasing: bool,
    applied_long_requires_initial_margin: bool,
    applied_short_requires_initial_margin: bool,
    applied_long_has_source_claims: bool,
    applied_short_has_source_claims: bool,
) -> V16Result<(BatchTradeOutcomeV16, bool, bool, bool)> {
    V16Core::kernel_accumulate_batch_trade(
        outcome,
        risk_increasing,
        long_has_source_claims,
        short_has_source_claims,
        TradeApplyOutcomeV16 {
            fee_a: applied_fee_a,
            fee_b: applied_fee_b,
            notional: applied_notional,
            risk_increasing: applied_risk_increasing,
            long_requires_initial_margin: applied_long_requires_initial_margin,
            short_requires_initial_margin: applied_short_requires_initial_margin,
            long_has_source_claims: applied_long_has_source_claims,
            short_has_source_claims: applied_short_has_source_claims,
        },
    )
}

#[cfg(kani)]
pub fn kani_source_claim_domain_first_burn_partition(
    source_claim_num: u128,
    burn_num: u128,
) -> (u128, u128) {
    V16Core::source_claim_domain_first_burn_partition(source_claim_num, burn_num)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_mul_div_floor_u128_or_wide(a: u128, b: u128, denominator: u128) -> V16Result<u128> {
    V16Core::mul_div_floor_u128_or_wide(a, b, denominator)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_mul_div_ceil_u128_or_wide(a: u128, b: u128, denominator: u128) -> V16Result<u128> {
    V16Core::mul_div_ceil_u128_or_wide(a, b, denominator)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_mul_div_floor_u128_wide_reference(
    a: u128,
    b: u128,
    denominator: u128,
) -> V16Result<u128> {
    if denominator == 0 {
        return Err(V16Error::InvalidConfig);
    }
    U256::from_u128(a)
        .checked_mul(U256::from_u128(b))
        .and_then(|value| value.checked_div(U256::from_u128(denominator)))
        .and_then(|value| value.try_into_u128())
        .ok_or(V16Error::ArithmeticOverflow)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_mul_div_ceil_u128_wide_reference(
    a: u128,
    b: u128,
    denominator: u128,
) -> V16Result<u128> {
    if denominator == 0 {
        return Err(V16Error::InvalidConfig);
    }
    checked_mul_div_ceil_u256(
        U256::from_u128(a),
        U256::from_u128(b),
        U256::from_u128(denominator),
    )
    .and_then(|value| value.try_into_u128())
    .ok_or(V16Error::ArithmeticOverflow)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_prepare_source_positive_claim_burn_delta(
    source: SourceCreditStateV16,
    face_burn_num: u128,
) -> V16Result<SourceCreditStateV16> {
    V16Core::prepare_source_positive_claim_burn_delta(source, face_burn_num)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_prepare_source_credit_domain_recompute_for_epoch(
    source: SourceCreditStateV16,
    risk_epoch: u64,
) -> V16Result<(SourceCreditStateV16, u64)> {
    V16Core::prepare_source_credit_domain_recompute_for_epoch(source, risk_epoch)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_prepare_source_credit_domain_recompute_for_epoch_steps(
    source: SourceCreditStateV16,
    risk_epoch: u64,
    epoch_steps: u64,
) -> V16Result<(SourceCreditStateV16, u64)> {
    V16Core::prepare_source_credit_domain_recompute_for_epoch_steps(source, risk_epoch, epoch_steps)
}

#[cfg(kani)]
pub fn kani_loss_stale_trade_scope_allowed(
    market_loss_stale_active: bool,
    trade_asset_loss_stale: bool,
    long_account_loss_stale_exposed: bool,
    short_account_loss_stale_exposed: bool,
) -> bool {
    V16Core::loss_stale_trade_scope_allowed(
        market_loss_stale_active,
        trade_asset_loss_stale,
        long_account_loss_stale_exposed,
        short_account_loss_stale_exposed,
    )
}

#[cfg(kani)]
pub fn kani_prepare_asset_recovery_transition(
    asset: AssetStateV16,
    asset_set_epoch: u64,
    risk_epoch: u64,
) -> V16Result<(AssetStateV16, u64, u64)> {
    V16Core::prepare_asset_recovery_transition(asset, asset_set_epoch, risk_epoch)
}

#[cfg(kani)]
pub fn kani_mark_kf_stale_cohorts(
    asset: AssetStateV16,
    long_changed: bool,
    short_changed: bool,
    cohort_epoch: u64,
) -> V16Result<AssetStateV16> {
    V16Core::kernel_mark_kf_stale_cohorts(asset, long_changed, short_changed, cohort_epoch)
}

#[cfg(kani)]
pub fn kani_settle_kf_stale_cohort(
    asset: AssetStateV16,
    side: SideV16,
    leg_kf_epoch_snap: u64,
) -> V16Result<(AssetStateV16, u64)> {
    V16Core::kernel_settle_kf_stale_cohort(asset, side, leg_kf_epoch_snap)
}

#[cfg(kani)]
pub fn kani_source_credit_state_realizable_support_for_face(
    state: SourceCreditStateV16,
    face_claim: u128,
) -> V16Result<u128> {
    V16Core::source_credit_state_realizable_support_for_face(state, face_claim)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_source_credit_state_realizable_support_for_claim_num(
    state: SourceCreditStateV16,
    claim_num: u128,
) -> V16Result<u128> {
    V16Core::source_credit_state_realizable_support_for_claim_num(state, claim_num)
}

#[cfg(kani)]
pub fn kani_backing_utilization_rate_e9_for_source_state(
    config: V16Config,
    source: SourceCreditStateV16,
) -> V16Result<u64> {
    V16Core::backing_utilization_rate_e9_for_source_state(config, source)
}

#[cfg(kani)]
pub fn kani_backing_utilization_fee_quote_atoms_for_lien(
    config: V16Config,
    source: SourceCreditStateV16,
    lien_backing_num: u128,
    from_slot: u64,
    to_slot: u64,
) -> V16Result<u128> {
    V16Core::backing_utilization_fee_quote_atoms_for_lien(
        config,
        source,
        lien_backing_num,
        from_slot,
        to_slot,
    )
}

#[cfg(kani)]
pub fn kani_target_effective_lag_adverse_delta(
    side: SideV16,
    effective_price: u64,
    raw_target_price: u64,
) -> u64 {
    V16Core::target_effective_lag_adverse_delta(side, effective_price, raw_target_price)
}

#[cfg(kani)]
pub fn kani_health_requirements_from_base_and_target_lag(
    base_initial: u128,
    base_maintenance: u128,
    risk_notional: u128,
    target_lag_penalty: u128,
) -> V16Result<(u128, u128, u128)> {
    V16Core::health_requirements_from_base_and_target_lag(
        base_initial,
        base_maintenance,
        risk_notional,
        target_lag_penalty,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HLockLaneV16 {
    HMin,
    HMax,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SideV16 {
    Long,
    Short,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SideModeV16 {
    Normal,
    DrainOnly,
    ResetPending,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssetLifecycleV16 {
    Disabled,
    PendingActivation,
    Active,
    DrainOnly,
    Retired,
    Recovery,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MarketModeV16 {
    Live,
    Resolved,
    Recovery,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackingBucketStatusV16 {
    Empty,
    Fresh,
    Expired,
    Impaired,
}

/// Compact ActionableState summary (roadmap Phase 4 / 3A.4): which of the eight
/// ActionableState classes are live for an account/market. The liveness
/// selector reads only this — never per-class witnesses that another active
/// class could invalidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ActionableSummaryV16 {
    pub stale: bool,                   // A1
    pub b_stale: bool,                 // A2
    pub pending_close: bool,           // A3
    pub expired_close: bool,           // A4
    pub liquidatable: bool,            // A5
    pub source_liens_releasable: bool, // A6
    pub recovery_eligible: bool,       // A7
    pub resolved_winner: bool,         // A8
}

impl ActionableSummaryV16 {
    pub fn is_actionable(self) -> bool {
        self.stale
            || self.b_stale
            || self.pending_close
            || self.expired_close
            || self.liquidatable
            || self.source_liens_releasable
            || self.recovery_eligible
            || self.resolved_winner
    }
}

/// One oracle observation a keeper submits to the auto-crank (engine.md). The
/// caller supplies a bounded set of these for the assets it has fresh data for;
/// the ENGINE selects which (if any) the highest-priority step needs. The caller
/// never chooses the action TYPE or the asset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AutoCrankObservationV16 {
    pub asset_index: usize,
    pub effective_price: u64,
    pub funding_rate_e9: i128,
}

/// Bounded work a keeper submits to the order-insensitive auto-crank (engine.md):
/// observations that may land in any order, a liquidation work budget, and the
/// resolved-close fee rate. NO caller-chosen action, asset, or liquidation fee —
/// the engine selects the step and the asset and derives the fee from config.
#[derive(Clone, Copy, Debug)]
pub struct AutoCrankWorkV16<'a> {
    pub now_slot: u64,
    pub observations: &'a [AutoCrankObservationV16],
    pub resolved_close_fee_rate_per_slot: u128,
}

/// The bounded progress step the engine SELECTED from current state (engine.md).
/// The asset/leg is chosen by the engine, not the caller. One auto-crank call
/// dispatches exactly one of these.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AutoCrankPlanV16 {
    NoAction,
    RefreshAccount {
        asset_index: Option<usize>,
    },
    SettleBChunk {
        asset_index: usize,
    },
    Liquidate {
        asset_index: usize,
    },
    ReleaseSourceLiens,
    AdvanceClose,
    DeclareRecovery {
        reason: PermissionlessRecoveryReasonV16,
    },
    FinalizeRecovery,
    CloseResolved,
}

/// The outcome of one self-classifying crank step: nothing actionable, a
/// permissionless-progress outcome (refresh / settle-B / liquidate / recovery),
/// a Recovery-to-Resolved transition, or a resolved-close outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AutoCrankOutcomeV16 {
    NoAction,
    Progressed(PermissionlessProgressOutcomeV16),
    RecoveryResolved,
    ResolvedClose(ResolvedCloseOutcomeV16),
}

/// Result of `permissionless_auto_crank_not_atomic`: the engine-selected plan
/// (including the engine-chosen asset) and the dispatched outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AutoCrankResultV16 {
    pub selected: AutoCrankPlanV16,
    pub outcome: AutoCrankOutcomeV16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PermissionlessRecoveryReasonV16 {
    BelowProgressFloor,
    BlockedSegmentHeadroomOrRepresentability,
    AccountBSettlementCannotProgress,
    BIndexHeadroomExhausted,
    ActiveBankruptCloseCannotProgress,
    ExplicitLossOrDustAuditOverflow,
    OracleOrTargetUnavailableByAuthenticatedPolicy,
    CounterOrEpochOverflowDeclaredRecovery,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProvenanceHeaderV16 {
    pub market_group_id: [u8; 32],
    pub portfolio_account_id: [u8; 32],
    pub owner: [u8; 32],
    pub version: u16,
    pub layout_discriminator: u16,
}

impl ProvenanceHeaderV16 {
    pub const fn new(
        market_group_id: [u8; 32],
        portfolio_account_id: [u8; 32],
        owner: [u8; 32],
    ) -> Self {
        Self {
            market_group_id,
            portfolio_account_id,
            owner,
            version: V16_ACCOUNT_VERSION,
            layout_discriminator: V16_LAYOUT_DISCRIMINATOR,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V16Config {
    pub max_portfolio_assets: u16,
    pub max_market_slots: u32,
    pub min_nonzero_mm_req: u128,
    pub min_nonzero_im_req: u128,
    pub h_min: u64,
    pub h_max: u64,
    pub maintenance_margin_bps: u64,
    pub initial_margin_bps: u64,
    pub max_trading_fee_bps: u64,
    pub liquidation_fee_bps: u64,
    pub liquidation_fee_cap: u128,
    pub min_liquidation_abs: u128,
    pub max_accrual_dt_slots: u64,
    pub max_abs_funding_e9_per_slot: u64,
    pub min_funding_lifetime_slots: u64,
    pub max_price_move_bps_per_slot: u64,
    pub max_account_b_settlement_chunks: u64,
    pub max_bankrupt_close_chunks: u64,
    pub max_bankrupt_close_lifetime_slots: u64,
    pub asset_activation_cooldown_slots: u64,
    pub public_b_chunk_atoms: u128,
    pub max_recovery_fallback_deviation_bps: u64,
    pub backing_fee_base_rate_e9_per_slot: u64,
    pub backing_fee_kink_util_bps: u64,
    pub backing_fee_slope_at_kink_e9_per_slot: u64,
    pub backing_fee_slope_above_kink_e9_per_slot: u64,
    pub backing_freshness_buckets: u8,
    pub margin_mode_realizable_full_shared_cross_margin: bool,
    pub source_credit_lien_required: bool,
    pub insurance_credit_reservation_required: bool,
    pub permissionless_recovery_enabled: bool,
    pub recovery_fallback_price_enabled: bool,
    pub recovery_fallback_envelope_enabled: bool,
    pub credit_lien_revalidation_required: bool,
    pub stale_certificate_penalty_enabled: bool,
    pub full_refresh_required_for_favorable_actions: bool,
    pub public_liveness_profile_crank_forward: bool,
}

impl V16Config {
    pub const fn public_user_fund(max_portfolio_assets: u16, h_min: u64, h_max: u64) -> Self {
        Self::public_user_fund_with_market_slots(
            max_portfolio_assets,
            max_portfolio_assets as u32,
            h_min,
            h_max,
        )
    }

    pub const fn public_user_fund_with_market_slots(
        max_portfolio_assets: u16,
        max_market_slots: u32,
        h_min: u64,
        h_max: u64,
    ) -> Self {
        Self {
            max_portfolio_assets,
            max_market_slots,
            min_nonzero_mm_req: 1,
            min_nonzero_im_req: 2,
            h_min,
            h_max,
            maintenance_margin_bps: 10_000,
            initial_margin_bps: 10_000,
            max_trading_fee_bps: 0,
            liquidation_fee_bps: 0,
            liquidation_fee_cap: 0,
            min_liquidation_abs: 0,
            max_accrual_dt_slots: 1,
            max_abs_funding_e9_per_slot: 0,
            min_funding_lifetime_slots: 1,
            max_price_move_bps_per_slot: 10_000,
            max_account_b_settlement_chunks: 1,
            max_bankrupt_close_chunks: 1,
            max_bankrupt_close_lifetime_slots: 1,
            asset_activation_cooldown_slots: 1,
            public_b_chunk_atoms: MAX_VAULT_TVL,
            max_recovery_fallback_deviation_bps: MAX_RECOVERY_FALLBACK_DEVIATION_BPS,
            backing_fee_base_rate_e9_per_slot: 0,
            backing_fee_kink_util_bps: 8_000,
            backing_fee_slope_at_kink_e9_per_slot: 0,
            backing_fee_slope_above_kink_e9_per_slot: 0,
            backing_freshness_buckets: V16_BACKING_BUCKETS_PER_DOMAIN as u8,
            margin_mode_realizable_full_shared_cross_margin: true,
            source_credit_lien_required: true,
            insurance_credit_reservation_required: true,
            permissionless_recovery_enabled: true,
            recovery_fallback_price_enabled: true,
            recovery_fallback_envelope_enabled: true,
            credit_lien_revalidation_required: true,
            stale_certificate_penalty_enabled: true,
            full_refresh_required_for_favorable_actions: true,
            public_liveness_profile_crank_forward: true,
        }
    }

    fn ceil_div_u256_to_u128(n: U256, d: U256) -> V16Result<u128> {
        if d.is_zero() {
            return Err(V16Error::InvalidConfig);
        }
        if let (Some(n), Some(d)) = (n.try_into_u128(), d.try_into_u128()) {
            if d == 0 {
                return Err(V16Error::InvalidConfig);
            }
            let q = n / d;
            let r = n % d;
            return q
                .checked_add(u128::from(r != 0))
                .ok_or(V16Error::InvalidConfig);
        }
        let q = n.checked_div(d).ok_or(V16Error::InvalidConfig)?;
        let r = n.checked_rem(d).ok_or(V16Error::InvalidConfig)?;
        let q = if r.is_zero() {
            q
        } else {
            q.checked_add(U256::ONE).ok_or(V16Error::InvalidConfig)?
        };
        q.try_into_u128().ok_or(V16Error::InvalidConfig)
    }

    fn checked_mul_div_ceil_to_u128(a: u128, b: u128, d: u128) -> V16Result<u128> {
        if d == 0 {
            return Err(V16Error::InvalidConfig);
        }
        if let Some(product) = a.checked_mul(b) {
            let q = product / d;
            let r = product % d;
            return q
                .checked_add(u128::from(r != 0))
                .ok_or(V16Error::InvalidConfig);
        }
        checked_mul_div_ceil_u256(U256::from_u128(a), U256::from_u128(b), U256::from_u128(d))
            .and_then(|v| v.try_into_u128())
            .ok_or(V16Error::InvalidConfig)
    }

    fn solvency_envelope_total_for_notional(
        &self,
        n: u128,
        loss_budget_num: u128,
        loss_budget_den: u128,
        price_budget_bps: u128,
    ) -> V16Result<u128> {
        let loss = Self::checked_mul_div_ceil_to_u128(n, loss_budget_num, loss_budget_den)?;

        let worst_liq_multiplier = 10_000u128
            .checked_add(price_budget_bps)
            .ok_or(V16Error::InvalidConfig)?;
        let worst_liq_notional =
            Self::checked_mul_div_ceil_to_u128(n, worst_liq_multiplier, 10_000)?;
        let liq_fee_raw = Self::checked_mul_div_ceil_to_u128(
            worst_liq_notional,
            self.liquidation_fee_bps as u128,
            10_000,
        )?;
        let liq_fee = core::cmp::min(
            core::cmp::max(liq_fee_raw, self.min_liquidation_abs),
            self.liquidation_fee_cap,
        );

        loss.checked_add(liq_fee).ok_or(V16Error::InvalidConfig)
    }

    fn maintenance_requirement_for_notional(&self, n: u128) -> V16Result<u128> {
        let mm_prop =
            Self::checked_mul_div_ceil_to_u128(n, self.maintenance_margin_bps as u128, 10_000)?;
        Ok(core::cmp::max(mm_prop, self.min_nonzero_mm_req))
    }

    fn solvency_envelope_holds_for_notional(
        &self,
        n: u128,
        loss_budget_num: u128,
        loss_budget_den: u128,
        price_budget_bps: u128,
    ) -> V16Result<bool> {
        let total = self.solvency_envelope_total_for_notional(
            n,
            loss_budget_num,
            loss_budget_den,
            price_budget_bps,
        )?;
        let mm_req = self.maintenance_requirement_for_notional(n)?;
        Ok(total <= mm_req)
    }

    fn solvency_envelope_interval_certifies(
        &self,
        lo: u128,
        hi: u128,
        loss_budget_num: u128,
        loss_budget_den: u128,
        price_budget_bps: u128,
    ) -> V16Result<bool> {
        let total_hi = self.solvency_envelope_total_for_notional(
            hi,
            loss_budget_num,
            loss_budget_den,
            price_budget_bps,
        )?;
        let mm_lo = self.maintenance_requirement_for_notional(lo)?;
        Ok(total_hi <= mm_lo)
    }

    fn validate_solvency_envelope_range(
        &self,
        lo: u128,
        hi: u128,
        loss_budget_num: u128,
        loss_budget_den: u128,
        price_budget_bps: u128,
    ) -> V16Result<()> {
        if lo > hi {
            return Ok(());
        }

        const MAX_SOLVENCY_INTERVALS: usize = 96;
        const MAX_SOLVENCY_STEPS: usize = 4096;
        const EXACT_CHUNK: u128 = 64;

        let mut stack = [(0u128, 0u128); MAX_SOLVENCY_INTERVALS];
        let mut len = 1usize;
        let mut steps = 0usize;
        stack[0] = (lo, hi);

        while len != 0 {
            steps = steps.checked_add(1).ok_or(V16Error::InvalidConfig)?;
            if steps > MAX_SOLVENCY_STEPS {
                return Err(V16Error::InvalidConfig);
            }

            len -= 1;
            let (range_lo, range_hi) = stack[len];

            if self.solvency_envelope_interval_certifies(
                range_lo,
                range_hi,
                loss_budget_num,
                loss_budget_den,
                price_budget_bps,
            )? {
                continue;
            }

            if range_hi == range_lo || range_hi - range_lo <= EXACT_CHUNK {
                let mut n = range_lo;
                loop {
                    if !self.solvency_envelope_holds_for_notional(
                        n,
                        loss_budget_num,
                        loss_budget_den,
                        price_budget_bps,
                    )? {
                        return Err(V16Error::InvalidConfig);
                    }
                    if n == range_hi {
                        break;
                    }
                    n = n.checked_add(1).ok_or(V16Error::InvalidConfig)?;
                }
                continue;
            }

            let mid = range_lo + (range_hi - range_lo) / 2;
            if len + 2 > MAX_SOLVENCY_INTERVALS {
                return Err(V16Error::InvalidConfig);
            }
            stack[len] = (mid.checked_add(1).ok_or(V16Error::InvalidConfig)?, range_hi);
            stack[len + 1] = (range_lo, mid);
            len += 2;
        }

        Ok(())
    }

    fn validate_funding_headroom(&self, slots: u64) -> V16Result<()> {
        let max_signed = U256::from_u128(i128::MAX as u128);
        let headroom = U256::from_u128(ADL_ONE)
            .checked_mul(U256::from_u128(MAX_ORACLE_PRICE as u128))
            .and_then(|v| v.checked_mul(U256::from_u128(self.max_abs_funding_e9_per_slot as u128)))
            .and_then(|v| v.checked_mul(U256::from_u128(slots as u128)))
            .ok_or(V16Error::InvalidConfig)?;
        if headroom <= max_signed {
            Ok(())
        } else {
            Err(V16Error::InvalidConfig)
        }
    }

    fn validate_exact_solvency_envelope(&self) -> V16Result<()> {
        let price_budget_fast = (self.max_price_move_bps_per_slot as u128)
            .checked_mul(self.max_accrual_dt_slots as u128)
            .ok_or(V16Error::InvalidConfig)?;
        if self.maintenance_margin_bps == 10_000
            && price_budget_fast <= 10_000
            && self.max_abs_funding_e9_per_slot == 0
            && self.liquidation_fee_bps == 0
            && self.min_liquidation_abs == 0
        {
            return Ok(());
        }

        self.validate_funding_headroom(self.max_accrual_dt_slots)?;
        self.validate_funding_headroom(self.min_funding_lifetime_slots)?;

        let move_cap = U256::from_u128(self.max_price_move_bps_per_slot as u128);
        let dt = U256::from_u128(self.max_accrual_dt_slots as u128);
        let rate = U256::from_u128(self.max_abs_funding_e9_per_slot as u128);
        let ten_thousand = U256::from_u128(10_000);
        let funding_den = U256::from_u128(FUNDING_DEN);

        let price_budget_bps = move_cap
            .checked_mul(dt)
            .and_then(|v| v.try_into_u128())
            .ok_or(V16Error::InvalidConfig)?;
        let funding_budget_num = rate
            .checked_mul(dt)
            .and_then(|v| v.checked_mul(ten_thousand))
            .ok_or(V16Error::InvalidConfig)?;
        let loss_budget_num_wide = U256::from_u128(price_budget_bps)
            .checked_mul(funding_den)
            .and_then(|v| v.checked_add(funding_budget_num))
            .ok_or(V16Error::InvalidConfig)?;
        let loss_budget_den_wide = ten_thousand
            .checked_mul(funding_den)
            .ok_or(V16Error::InvalidConfig)?;

        let funding_budget_bps_ceil = Self::ceil_div_u256_to_u128(funding_budget_num, funding_den)?;
        let loss_budget_bps_ceil = price_budget_bps
            .checked_add(funding_budget_bps_ceil)
            .ok_or(V16Error::InvalidConfig)?;
        let worst_liq_budget_bps_ceil = Self::ceil_div_u256_to_u128(
            U256::from_u128(
                10_000u128
                    .checked_add(price_budget_bps)
                    .ok_or(V16Error::InvalidConfig)?,
            )
            .checked_mul(U256::from_u128(self.liquidation_fee_bps as u128))
            .ok_or(V16Error::InvalidConfig)?,
            ten_thousand,
        )?;
        let linear_budget_bps = loss_budget_bps_ceil
            .checked_add(worst_liq_budget_bps_ceil)
            .ok_or(V16Error::InvalidConfig)?;

        if self.maintenance_margin_bps == 10_000
            && loss_budget_bps_ceil == 10_000
            && worst_liq_budget_bps_ceil == 0
            && self.min_liquidation_abs == 0
        {
            return Ok(());
        }

        let loss_budget_num = loss_budget_num_wide
            .try_into_u128()
            .ok_or(V16Error::InvalidConfig)?;
        let loss_budget_den = loss_budget_den_wide
            .try_into_u128()
            .ok_or(V16Error::InvalidConfig)?;
        let domain_max = MAX_ACCOUNT_NOTIONAL;

        if self.maintenance_margin_bps == 0 {
            if self.solvency_envelope_holds_for_notional(
                domain_max,
                loss_budget_num,
                loss_budget_den,
                price_budget_bps,
            )? {
                return Ok(());
            }
            return Err(V16Error::InvalidConfig);
        }

        let floor_region_max = U256::from_u128(self.min_nonzero_mm_req)
            .checked_mul(ten_thousand)
            .and_then(|v| v.checked_div(U256::from_u128(self.maintenance_margin_bps as u128)))
            .and_then(|v| v.try_into_u128())
            .ok_or(V16Error::InvalidConfig)?;
        let floor_region_end = core::cmp::min(floor_region_max, domain_max);
        if floor_region_end != 0
            && !self.solvency_envelope_holds_for_notional(
                floor_region_end,
                loss_budget_num,
                loss_budget_den,
                price_budget_bps,
            )?
        {
            return Err(V16Error::InvalidConfig);
        }
        if floor_region_max >= domain_max {
            return Ok(());
        }

        let exact_start = floor_region_end
            .checked_add(1)
            .ok_or(V16Error::InvalidConfig)?;

        if linear_budget_bps < self.maintenance_margin_bps as u128 {
            let slope_gap = (self.maintenance_margin_bps as u128) - linear_budget_bps;
            let tail_for_linear = Self::ceil_div_u256_to_u128(
                U256::from_u128(3 * 10_000),
                U256::from_u128(slope_gap),
            )?;

            let loss_gap = (self.maintenance_margin_bps as u128)
                .checked_sub(loss_budget_bps_ceil)
                .ok_or(V16Error::InvalidConfig)?;
            let floor_fee_slack = self
                .min_liquidation_abs
                .checked_add(2)
                .ok_or(V16Error::InvalidConfig)?;
            let tail_for_fee_floor = Self::ceil_div_u256_to_u128(
                U256::from_u128(floor_fee_slack)
                    .checked_mul(ten_thousand)
                    .ok_or(V16Error::InvalidConfig)?,
                U256::from_u128(loss_gap),
            )?;

            let exact_tail = core::cmp::max(tail_for_linear, tail_for_fee_floor);
            if exact_tail <= exact_start {
                return Ok(());
            }
            let exact_end = core::cmp::min(exact_tail.saturating_sub(1), domain_max);
            return self.validate_solvency_envelope_range(
                exact_start,
                exact_end,
                loss_budget_num,
                loss_budget_den,
                price_budget_bps,
            );
        }

        if loss_budget_bps_ceil >= self.maintenance_margin_bps as u128 {
            return self.validate_solvency_envelope_range(
                exact_start,
                domain_max,
                loss_budget_num,
                loss_budget_den,
                price_budget_bps,
            );
        }

        let slope_gap = (self.maintenance_margin_bps as u128) - loss_budget_bps_ceil;
        let capped_fee_slack = self
            .liquidation_fee_cap
            .checked_add(3)
            .ok_or(V16Error::InvalidConfig)?;
        let exact_tail = Self::ceil_div_u256_to_u128(
            U256::from_u128(capped_fee_slack)
                .checked_mul(ten_thousand)
                .ok_or(V16Error::InvalidConfig)?,
            U256::from_u128(slope_gap),
        )?;

        if exact_tail <= exact_start {
            return Ok(());
        }

        let exact_end = core::cmp::min(exact_tail.saturating_sub(1), domain_max);
        self.validate_solvency_envelope_range(
            exact_start,
            exact_end,
            loss_budget_num,
            loss_budget_den,
            price_budget_bps,
        )
    }

    fn validate_public_user_fund_shape(&self) -> V16Result<()> {
        if self.max_portfolio_assets == 0
            || self.max_portfolio_assets as usize > V16_MAX_PORTFOLIO_ASSETS_N
            || self.max_market_slots == 0
            || self.max_portfolio_assets as u32 > self.max_market_slots
        {
            return Err(V16Error::InvalidConfig);
        }
        if self.h_max == 0 || self.h_min > self.h_max {
            return Err(V16Error::InvalidConfig);
        }
        if self.min_nonzero_mm_req == 0 || self.min_nonzero_mm_req >= self.min_nonzero_im_req {
            return Err(V16Error::InvalidConfig);
        }
        if self.maintenance_margin_bps > self.initial_margin_bps
            || self.initial_margin_bps > MAX_MARGIN_BPS
            || self.max_trading_fee_bps > MAX_MARGIN_BPS
            || self.liquidation_fee_bps > MAX_MARGIN_BPS
            || self.min_liquidation_abs > self.liquidation_fee_cap
            || self.liquidation_fee_cap > MAX_PROTOCOL_FEE_ABS
            || self.max_accrual_dt_slots == 0
            || self.min_funding_lifetime_slots < self.max_accrual_dt_slots
            || self.max_abs_funding_e9_per_slot > 10_000
            || self.max_price_move_bps_per_slot == 0
            // fork feature A-10: upper-bound the per-slot price-move cap (toly bounds only the
            // lower edge == 0). A config with max_price_move_bps_per_slot > MAX_MARGIN_BPS would
            // admit a price-move budget exceeding full margin, weakening the move guard; reject it.
            || self.max_price_move_bps_per_slot > MAX_MARGIN_BPS
            || self.max_account_b_settlement_chunks == 0
            || self.max_bankrupt_close_chunks == 0
            || self.max_bankrupt_close_lifetime_slots == 0
            || self.asset_activation_cooldown_slots == 0
            || self.public_b_chunk_atoms == 0
            || self.max_recovery_fallback_deviation_bps > MAX_RECOVERY_FALLBACK_DEVIATION_BPS
            || self.backing_fee_kink_util_bps == 0
            || self.backing_fee_kink_util_bps >= MAX_BACKING_FEE_UTIL_BPS
            || self.backing_freshness_buckets == 0
            || self.backing_freshness_buckets as usize > V16_BACKING_BUCKETS_PER_DOMAIN
        {
            return Err(V16Error::InvalidConfig);
        }
        if self
            .backing_fee_base_rate_e9_per_slot
            .checked_add(self.backing_fee_slope_at_kink_e9_per_slot)
            .and_then(|v| v.checked_add(self.backing_fee_slope_above_kink_e9_per_slot))
            .ok_or(V16Error::InvalidConfig)?
            > MAX_BACKING_FEE_RATE_E9_PER_SLOT
        {
            return Err(V16Error::InvalidConfig);
        }
        if !self.margin_mode_realizable_full_shared_cross_margin
            || !self.source_credit_lien_required
            || !self.insurance_credit_reservation_required
            || !self.permissionless_recovery_enabled
            || !self.recovery_fallback_price_enabled
            || !self.recovery_fallback_envelope_enabled
            || !self.credit_lien_revalidation_required
            || !self.stale_certificate_penalty_enabled
            || !self.full_refresh_required_for_favorable_actions
            || !self.public_liveness_profile_crank_forward
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    pub fn validate_public_user_fund(&self) -> V16Result<()> {
        self.validate_public_user_fund_shape()?;
        self.validate_exact_solvency_envelope()
    }

    /// fork-facade (A-10): kani-only accessor for the SHAPE check in isolation, so the A-10
    /// `max_price_move_bps_per_slot > MAX_MARGIN_BPS` clause can be proven operative without the
    /// solvency-envelope path (which would mask the clause via an unrelated overflow rejection).
    /// Mirrors frozen's own `kani_*` shim convention; absent from the production surface.
    #[cfg(kani)]
    pub fn kani_validate_public_user_fund_shape(&self) -> V16Result<()> {
        self.validate_public_user_fund_shape()
    }

    #[cfg(kani)]
    pub fn kani_solvency_envelope_holds_for_notional(&self, n: u128) -> V16Result<bool> {
        self.validate_funding_headroom(self.max_accrual_dt_slots)?;
        self.validate_funding_headroom(self.min_funding_lifetime_slots)?;
        let price_budget_bps = (self.max_price_move_bps_per_slot as u128)
            .checked_mul(self.max_accrual_dt_slots as u128)
            .ok_or(V16Error::InvalidConfig)?;
        let funding_budget_num = (self.max_abs_funding_e9_per_slot as u128)
            .checked_mul(self.max_accrual_dt_slots as u128)
            .and_then(|v| v.checked_mul(10_000))
            .ok_or(V16Error::InvalidConfig)?;
        let loss_budget_num = price_budget_bps
            .checked_mul(FUNDING_DEN)
            .and_then(|v| v.checked_add(funding_budget_num))
            .ok_or(V16Error::InvalidConfig)?;
        let loss_budget_den = 10_000u128
            .checked_mul(FUNDING_DEN)
            .ok_or(V16Error::InvalidConfig)?;
        self.solvency_envelope_holds_for_notional(
            n,
            loss_budget_num,
            loss_budget_den,
            price_budget_bps,
        )
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssetStateV16 {
    pub market_id: u64,
    pub retired_slot: u64,
    pub lifecycle: AssetLifecycleV16,
    pub raw_oracle_target_price: u64,
    pub effective_price: u64,
    pub fund_px_last: u64,
    pub slot_last: u64,
    pub a_long: u128,
    pub a_short: u128,
    pub k_long: i128,
    pub k_short: i128,
    pub f_long_num: i128,
    pub f_short_num: i128,
    pub kf_epoch_long: u64,
    pub kf_epoch_short: u64,
    pub k_epoch_start_long: i128,
    pub k_epoch_start_short: i128,
    pub f_epoch_start_long_num: i128,
    pub f_epoch_start_short_num: i128,
    pub b_long_num: u128,
    pub b_short_num: u128,
    pub b_epoch_start_long_num: u128,
    pub b_epoch_start_short_num: u128,
    pub oi_eff_long_q: u128,
    pub oi_eff_short_q: u128,
    pub stored_pos_count_long: u64,
    pub stored_pos_count_short: u64,
    pub stale_account_count_long: u64,
    pub stale_account_count_short: u64,
    pub pending_obligation_count_long: u64,
    pub pending_obligation_count_short: u64,
    pub loss_weight_sum_long: u128,
    pub loss_weight_sum_short: u128,
    pub social_loss_remainder_long_num: u128,
    pub social_loss_remainder_short_num: u128,
    pub social_loss_dust_long_num: u128,
    pub social_loss_dust_short_num: u128,
    pub explicit_unallocated_loss_long: u128,
    pub explicit_unallocated_loss_short: u128,
    pub epoch_long: u64,
    pub epoch_short: u64,
    pub mode_long: SideModeV16,
    pub mode_short: SideModeV16,
}

impl Default for AssetStateV16 {
    fn default() -> Self {
        Self {
            market_id: 0,
            retired_slot: 0,
            lifecycle: AssetLifecycleV16::Active,
            raw_oracle_target_price: 1,
            effective_price: 1,
            fund_px_last: 1,
            slot_last: 0,
            a_long: ADL_ONE,
            a_short: ADL_ONE,
            k_long: 0,
            k_short: 0,
            f_long_num: 0,
            f_short_num: 0,
            kf_epoch_long: 0,
            kf_epoch_short: 0,
            k_epoch_start_long: 0,
            k_epoch_start_short: 0,
            f_epoch_start_long_num: 0,
            f_epoch_start_short_num: 0,
            b_long_num: 0,
            b_short_num: 0,
            b_epoch_start_long_num: 0,
            b_epoch_start_short_num: 0,
            oi_eff_long_q: 0,
            oi_eff_short_q: 0,
            stored_pos_count_long: 0,
            stored_pos_count_short: 0,
            stale_account_count_long: 0,
            stale_account_count_short: 0,
            pending_obligation_count_long: 0,
            pending_obligation_count_short: 0,
            loss_weight_sum_long: 0,
            loss_weight_sum_short: 0,
            social_loss_remainder_long_num: 0,
            social_loss_remainder_short_num: 0,
            social_loss_dust_long_num: 0,
            social_loss_dust_short_num: 0,
            explicit_unallocated_loss_long: 0,
            explicit_unallocated_loss_short: 0,
            epoch_long: 0,
            epoch_short: 0,
            mode_long: SideModeV16::Normal,
            mode_short: SideModeV16::Normal,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceCreditStateV16 {
    pub positive_claim_bound_num: u128,
    pub exact_positive_claim_num: u128,
    pub fresh_reserved_backing_num: u128,
    pub spent_backing_num: u128,
    pub provider_receivable_num: u128,
    pub valid_liened_backing_num: u128,
    pub impaired_liened_backing_num: u128,
    pub insurance_credit_reserved_num: u128,
    pub valid_liened_insurance_num: u128,
    pub impaired_liened_insurance_num: u128,
    pub credit_rate_num: u128,
    pub credit_epoch: u64,
}

impl SourceCreditStateV16 {
    pub const EMPTY: Self = Self {
        positive_claim_bound_num: 0,
        exact_positive_claim_num: 0,
        fresh_reserved_backing_num: 0,
        spent_backing_num: 0,
        provider_receivable_num: 0,
        valid_liened_backing_num: 0,
        impaired_liened_backing_num: 0,
        insurance_credit_reserved_num: 0,
        valid_liened_insurance_num: 0,
        impaired_liened_insurance_num: 0,
        credit_rate_num: CREDIT_RATE_SCALE,
        credit_epoch: 0,
    };

    const fn is_empty_amount_shape(self) -> bool {
        self.positive_claim_bound_num == 0
            && self.exact_positive_claim_num == 0
            && self.fresh_reserved_backing_num == 0
            && self.spent_backing_num == 0
            && self.provider_receivable_num == 0
            && self.valid_liened_backing_num == 0
            && self.impaired_liened_backing_num == 0
            && self.insurance_credit_reserved_num == 0
            && self.valid_liened_insurance_num == 0
            && self.impaired_liened_insurance_num == 0
            && (self.credit_rate_num == 0 || self.credit_rate_num == CREDIT_RATE_SCALE)
    }

    const fn is_terminal_spent_audit_only_shape(self) -> bool {
        self.positive_claim_bound_num == 0
            && self.exact_positive_claim_num == 0
            && self.fresh_reserved_backing_num == 0
            && self.provider_receivable_num == 0
            && self.valid_liened_backing_num == 0
            && self.impaired_liened_backing_num == 0
            && self.insurance_credit_reserved_num == 0
            && self.valid_liened_insurance_num == 0
            && self.impaired_liened_insurance_num == 0
            && (self.credit_rate_num == 0 || self.credit_rate_num == CREDIT_RATE_SCALE)
    }
}

impl Default for SourceCreditStateV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BackingBucketV16 {
    pub market_id: u64,
    pub fresh_unliened_backing_num: u128,
    pub valid_liened_backing_num: u128,
    pub consumed_liened_backing_num: u128,
    pub impaired_liened_backing_num: u128,
    pub utilization_fee_earnings: u128,
    pub expiry_slot: u64,
    pub status: BackingBucketStatusV16,
}

impl BackingBucketV16 {
    pub const EMPTY: Self = Self {
        market_id: 0,
        fresh_unliened_backing_num: 0,
        valid_liened_backing_num: 0,
        consumed_liened_backing_num: 0,
        impaired_liened_backing_num: 0,
        utilization_fee_earnings: 0,
        expiry_slot: 0,
        status: BackingBucketStatusV16::Empty,
    };

    pub const fn empty_for_market(market_id: u64) -> Self {
        Self {
            market_id,
            fresh_unliened_backing_num: 0,
            valid_liened_backing_num: 0,
            consumed_liened_backing_num: 0,
            impaired_liened_backing_num: 0,
            utilization_fee_earnings: 0,
            expiry_slot: 0,
            status: BackingBucketStatusV16::Empty,
        }
    }

    fn is_empty_amount_shape(self) -> bool {
        self.fresh_unliened_backing_num == 0
            && self.valid_liened_backing_num == 0
            && self.consumed_liened_backing_num == 0
            && self.impaired_liened_backing_num == 0
            && self.utilization_fee_earnings == 0
            && self.expiry_slot == 0
            && self.status == BackingBucketStatusV16::Empty
    }
}

impl Default for BackingBucketV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InsuranceCreditReservationV16 {
    pub insurance_credit_reserved_num: u128,
    pub valid_liened_insurance_num: u128,
    pub impaired_liened_insurance_num: u128,
    pub consumed_insurance_num: u128,
    pub source_credit_epoch: u64,
}

impl InsuranceCreditReservationV16 {
    pub const EMPTY: Self = Self {
        insurance_credit_reserved_num: 0,
        valid_liened_insurance_num: 0,
        impaired_liened_insurance_num: 0,
        consumed_insurance_num: 0,
        source_credit_epoch: 0,
    };
}

impl Default for InsuranceCreditReservationV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

/// Wrapper-owned bytes embedded beside the engine market slot.
///
/// # Safety
///
/// Implementors must be valid `bytemuck::Pod` / `Zeroable` values, and
/// `Market<Self>` must not contain inter-field or trailing padding. A wrapper
/// can satisfy this by using an alignment-1 byte wrapper, or by proving its
/// alignment divides `size_of::<EngineAssetSlotV16Account>()`.
#[allow(unsafe_code)]
pub unsafe trait MarketWrapperPod: bytemuck::Pod + bytemuck::Zeroable {}

#[allow(unsafe_code)]
unsafe impl MarketWrapperPod for () {}
#[allow(unsafe_code)]
unsafe impl MarketWrapperPod for u8 {}

macro_rules! impl_market_wrapper_pod_for_byte_arrays {
    ($($n:expr),* $(,)?) => {
        $(
            #[allow(unsafe_code)]
            unsafe impl MarketWrapperPod for [u8; $n] {}
        )*
    };
}

impl_market_wrapper_pod_for_byte_arrays!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 64, 128, 256, 512, 1024,
);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Market<T> {
    pub wrapper: T,
    pub engine: EngineAssetSlotV16Account,
}

#[allow(unsafe_code)]
unsafe impl<T: MarketWrapperPod> bytemuck::Zeroable for Market<T> {}
#[allow(unsafe_code)]
unsafe impl<T: MarketWrapperPod> bytemuck::Pod for Market<T> {}

impl<T> Market<T> {
    pub const fn new(wrapper: T, engine: EngineAssetSlotV16Account) -> Self {
        Self { wrapper, engine }
    }
}

impl<T> MarketSlotV16View for Market<T> {
    fn engine_slot(&self) -> &EngineAssetSlotV16Account {
        &self.engine
    }
}

impl<T> MarketSlotV16ViewMut for Market<T> {
    fn engine_slot_mut(&mut self) -> &mut EngineAssetSlotV16Account {
        &mut self.engine
    }
}

pub struct MarketGroupV16View<'a, T> {
    pub header: &'a MarketGroupV16HeaderAccount,
    pub markets: &'a [Market<T>],
}

pub struct MarketGroupV16ViewMut<'a, T> {
    pub header: &'a mut MarketGroupV16HeaderAccount,
    pub markets: &'a mut [Market<T>],
}

impl<'a, T> MarketGroupV16View<'a, T> {
    pub fn new(header: &'a MarketGroupV16HeaderAccount, markets: &'a [Market<T>]) -> Self {
        Self { header, markets }
    }
}

impl<'a, T> MarketGroupV16ViewMut<'a, T> {
    pub fn new(header: &'a mut MarketGroupV16HeaderAccount, markets: &'a mut [Market<T>]) -> Self {
        Self { header, markets }
    }

    pub fn as_view(&self) -> MarketGroupV16View<'_, T> {
        MarketGroupV16View {
            header: self.header,
            markets: self.markets,
        }
    }
}

pub struct PortfolioV16View<'a> {
    pub header: &'a PortfolioAccountV16Account,
}

pub struct PortfolioV16ViewMut<'a> {
    pub header: &'a mut PortfolioAccountV16Account,
}

impl<'a> PortfolioV16View<'a> {
    pub fn new(header: &'a PortfolioAccountV16Account) -> Self {
        Self { header }
    }

    #[inline]
    fn source_domains(&self) -> &[PortfolioSourceDomainV16Account; PORTFOLIO_SOURCE_DOMAIN_CAP] {
        &self.header.source_domains
    }

    fn source_domain_slot(&self, domain: usize) -> V16Result<Option<usize>> {
        let domain_u32 = u32::try_from(domain).map_err(|_| V16Error::ArithmeticOverflow)?;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = self.header.source_domains[slot];
            if source.domain.get() == domain_u32 && source.is_occupied() {
                return Ok(Some(slot));
            }
            slot += 1;
        }
        Ok(None)
    }

    fn source_domain(&self, domain: usize) -> V16Result<PortfolioSourceDomainV16Account> {
        Ok(match self.source_domain_slot(domain)? {
            Some(slot) => self.header.source_domains[slot],
            None => PortfolioSourceDomainV16Account::default(),
        })
    }

    #[cfg(kani)]
    pub fn kani_source_domain_slot(&self, domain: usize) -> V16Result<Option<usize>> {
        self.source_domain_slot(domain)
    }

    #[cfg(kani)]
    pub fn kani_source_domain(&self, domain: usize) -> V16Result<PortfolioSourceDomainV16Account> {
        self.source_domain(domain)
    }
}

impl<'a> PortfolioV16ViewMut<'a> {
    pub fn new(header: &'a mut PortfolioAccountV16Account) -> Self {
        let mut view = Self { header };
        view.compact_source_domains();
        view
    }

    pub fn as_view(&self) -> PortfolioV16View<'_> {
        PortfolioV16View {
            header: self.header,
        }
    }

    fn source_domain_slot(&self, domain: usize) -> V16Result<Option<usize>> {
        let domain_u32 = u32::try_from(domain).map_err(|_| V16Error::ArithmeticOverflow)?;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = self.header.source_domains[slot];
            let source_domain = source.domain.get();
            if source_domain == domain_u32 {
                if source.is_occupied() {
                    return Ok(Some(slot));
                }
                if source.has_default_sparse_tag() {
                    return Ok(None);
                }
            } else if source.has_default_sparse_tag() && !source.is_occupied() {
                return Ok(None);
            }
            slot += 1;
        }
        Ok(None)
    }

    fn source_domain_slot_or_insert(&mut self, domain: usize) -> V16Result<usize> {
        let domain_u32 = u32::try_from(domain).map_err(|_| V16Error::ArithmeticOverflow)?;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = self.header.source_domains[slot];
            let source_domain = source.domain.get();
            if source_domain == domain_u32 {
                if source.is_occupied() || !source.has_default_sparse_tag() {
                    return Ok(slot);
                }
                if source.has_default_sparse_tag() {
                    self.header.source_domains[slot].domain = V16PodU32::new(domain_u32);
                    return Ok(slot);
                }
            } else if source.has_default_sparse_tag() && !source.is_occupied() {
                self.header.source_domains[slot].domain = V16PodU32::new(domain_u32);
                return Ok(slot);
            }
            slot += 1;
        }
        Err(V16Error::LockActive)
    }

    fn source_domain_mut_or_insert(
        &mut self,
        domain: usize,
    ) -> V16Result<&mut PortfolioSourceDomainV16Account> {
        let slot = self.source_domain_slot_or_insert(domain)?;
        Ok(&mut self.header.source_domains[slot])
    }

    #[cfg(kani)]
    pub fn kani_source_domain_slot_or_insert(&mut self, domain: usize) -> V16Result<usize> {
        self.source_domain_slot_or_insert(domain)
    }

    fn reset_source_domain_slot_if_empty(&mut self, slot: usize) -> bool {
        if slot < PORTFOLIO_SOURCE_DOMAIN_CAP
            && !self.header.source_domains[slot].is_occupied()
            && !self.header.source_domains[slot].has_default_sparse_tag()
        {
            self.header.source_domains[slot] = PortfolioSourceDomainV16Account::default();
            return true;
        }
        false
    }

    fn compact_source_domains(&mut self) {
        let mut write = 0usize;
        let mut read = 0usize;
        let mut ordered = true;
        let mut previous_domain = None;
        while read < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = self.header.source_domains[read];
            if source.is_occupied() {
                let domain = source.domain.get();
                if previous_domain.is_some_and(|previous| previous > domain) {
                    ordered = false;
                }
                previous_domain = Some(domain);
                if write != read {
                    self.header.source_domains[write] = source;
                    self.header.source_domains[read] = PortfolioSourceDomainV16Account::default();
                }
                write += 1;
            }
            read += 1;
        }
        let occupied = write;
        while write < PORTFOLIO_SOURCE_DOMAIN_CAP {
            self.header.source_domains[write] = PortfolioSourceDomainV16Account::default();
            write += 1;
        }
        // upstream c0dec8ce: canonical allocation order (ascending domain index) so
        // bounded one-domain-per-call continuations see one layout.
        if !ordered {
            let mut index = 1usize;
            while index < occupied {
                let source = self.header.source_domains[index];
                let mut insert = index;
                while insert != 0
                    && self.header.source_domains[insert - 1].domain.get() > source.domain.get()
                {
                    self.header.source_domains[insert] = self.header.source_domains[insert - 1];
                    insert -= 1;
                }
                self.header.source_domains[insert] = source;
                index += 1;
            }
        }
    }
}

impl<'a> PortfolioV16View<'a> {
    pub fn validate_with_market<T>(&self, market: &MarketGroupV16View<'_, T>) -> V16Result<()> {
        let config = market.header.config.try_to_runtime_shape()?;
        if self.header.provenance_header.market_group_id != market.header.market_group_id
            || self.header.owner != self.header.provenance_header.owner
            || self.header.provenance_header.version.get() != V16_ACCOUNT_VERSION
            || self.header.provenance_header.layout_discriminator.get() != V16_LAYOUT_DISCRIMINATOR
        {
            return Err(V16Error::ProvenanceMismatch);
        }
        let pnl = self.header.pnl.get();
        validate_non_min_i128(pnl)?;
        validate_fee_credits(self.header.fee_credits.get())?;
        let liquidation_lock = decode_bool(self.header.liquidation_lock)?;
        if liquidation_lock && pnl >= 0 {
            return Err(V16Error::InvalidLeg);
        }
        if self.header.reserved_pnl.get() > pnl.max(0) as u128 {
            return Err(V16Error::InvalidLeg);
        }
        if self.header.residual_spent_principal_atoms_total.get()
            > self.header.residual_crystallized_loss_atoms_total.get()
        {
            return Err(V16Error::InvalidLeg);
        }
        self.validate_source_credit_shape_with_market(market)?;
        let source_claim_sum_num = self.source_claim_bound_sum_num()?;
        if source_claim_sum_num != 0 {
            let source_attributed_pnl =
                if decode_market_mode(market.header.mode)? == MarketModeV16::Resolved {
                    pnl.max(0) as u128 - self.header.reserved_pnl.get()
                } else {
                    pnl.max(0) as u128
                };
            V16Core::validate_positive_pnl_source_attribution(
                source_attributed_pnl as i128,
                source_claim_sum_num,
            )?;
        }
        Self::validate_resolved_payout_receipt_static(
            self.header.resolved_payout_receipt.try_to_runtime()?,
        )?;
        self.validate_close_progress_ledger_with_market(market)?;

        let active_leg_cap = config.max_portfolio_assets as usize;
        let configured_assets = config.max_market_slots as usize;
        let bitmap = self.header.active_bitmap.map(V16PodU64::get);
        let mut seen_assets = [u32::MAX; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut seen_asset_count = 0usize;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let bit = active_bitmap_get(bitmap, slot);
            let leg = self.header.legs[slot].try_to_runtime()?;
            if slot >= active_leg_cap {
                if bit || !leg.is_empty() {
                    return Err(V16Error::HiddenLeg);
                }
                slot += 1;
                continue;
            }
            if bit != leg.active {
                return Err(V16Error::HiddenLeg);
            }
            if !leg.active {
                if !leg.is_empty() {
                    return Err(V16Error::HiddenLeg);
                }
                slot += 1;
                continue;
            }
            validate_active_leg(leg)?;
            let asset_index = leg.asset_index as usize;
            if asset_index >= configured_assets || asset_index >= market.markets.len() {
                return Err(V16Error::HiddenLeg);
            }
            let asset = market.markets[asset_index].engine.asset.try_to_runtime()?;
            if leg.market_id != asset.market_id
                || !matches!(
                    asset.lifecycle,
                    AssetLifecycleV16::Active
                        | AssetLifecycleV16::DrainOnly
                        | AssetLifecycleV16::Recovery
                )
                || !leg_snapshots_bound_to_asset_side(asset, leg)
            {
                return Err(V16Error::HiddenLeg);
            }
            let mut seen = 0usize;
            while seen < seen_asset_count {
                if seen_assets[seen] == leg.asset_index {
                    return Err(V16Error::HiddenLeg);
                }
                seen += 1;
            }
            seen_assets[seen_asset_count] = leg.asset_index;
            seen_asset_count += 1;
            slot += 1;
        }

        if self.header.close_progress.quantity_adl_applied_q.get() != 0 {
            let i = self.header.close_progress.asset_index.get() as usize;
            if i >= configured_assets || self.active_leg_slot_for_asset(i)?.is_some() {
                return Err(V16Error::InvalidLeg);
            }
        }
        Ok(())
    }

    fn validate_source_credit_shape_with_market<T>(
        &self,
        market: &MarketGroupV16View<'_, T>,
    ) -> V16Result<()> {
        let configured_domains =
            v16_domain_count_for_market_slots(market.header.config.max_market_slots.get())?;
        let mut seen = [u32::MAX; PORTFOLIO_SOURCE_DOMAIN_CAP];
        let mut seen_count = 0usize;
        let mut slot_index = 0usize;
        while slot_index < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = self.source_domains()[slot_index];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                slot_index += 1;
                continue;
            }
            if !source.is_occupied() {
                return Err(V16Error::HiddenLeg);
            }
            let d_u32 = source.domain.get();
            let d = d_u32 as usize;
            if d >= configured_domains {
                return Err(V16Error::HiddenLeg);
            }
            let mut seen_i = 0usize;
            while seen_i < seen_count {
                if seen[seen_i] == d_u32 {
                    return Err(V16Error::HiddenLeg);
                }
                seen_i += 1;
            }
            seen[seen_count] = d_u32;
            seen_count += 1;
            let asset_index = d / 2;
            let asset = market.markets[asset_index].engine.asset.try_to_runtime()?;
            if source.source_claim_market_id.get() != asset.market_id {
                return Err(V16Error::HiddenLeg);
            }
            let slot = market.markets[asset_index].engine_slot();
            let domain_credit = if d % 2 == 0 {
                slot.source_credit_long.try_to_runtime()?
            } else {
                slot.source_credit_short.try_to_runtime()?
            };
            if source.source_claim_bound_num.get() > domain_credit.positive_claim_bound_num {
                return Err(V16Error::InvalidLeg);
            }
            let proof = SourceCreditLienAggregateProofV16 {
                domain: u16::try_from(d).map_err(|_| V16Error::ArithmeticOverflow)?,
                source_claim_bound_num: source.source_claim_bound_num.get(),
                face_claim_locked_num: source.source_claim_liened_num.get(),
                counterparty_face_claim_locked_num: source
                    .source_claim_counterparty_liened_num
                    .get(),
                insurance_face_claim_locked_num: source.source_claim_insurance_liened_num.get(),
                effective_credit_reserved: source.source_lien_effective_reserved.get(),
                counterparty_backing_reserved_num: source
                    .source_lien_counterparty_backing_num
                    .get(),
                insurance_backing_reserved_num: source.source_lien_insurance_backing_num.get(),
                impaired_face_claim_num: source.source_claim_impaired_num.get(),
                impaired_effective_credit_reserved: source
                    .source_lien_impaired_effective_reserved
                    .get(),
            };
            proof.validate()?;
            let locked = proof
                .face_claim_locked_num
                .checked_add(proof.impaired_face_claim_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            if locked > proof.source_claim_bound_num {
                return Err(V16Error::InvalidLeg);
            }
            let backing_source_claim = proof
                .counterparty_face_claim_locked_num
                .checked_add(proof.insurance_face_claim_locked_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            if backing_source_claim != proof.face_claim_locked_num {
                return Err(V16Error::InvalidLeg);
            }
            if proof.effective_credit_reserved
                > V16Core::amount_from_bound_num(proof.face_claim_locked_num)?
            {
                return Err(V16Error::InvalidLeg);
            }
            let lien_backing_num = proof
                .counterparty_backing_reserved_num
                .checked_add(proof.insurance_backing_reserved_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            if proof.counterparty_backing_reserved_num % BOUND_SCALE != 0
                || proof.insurance_backing_reserved_num % BOUND_SCALE != 0
                || lien_backing_num
                    != proof
                        .effective_credit_reserved
                        .checked_mul(BOUND_SCALE)
                        .ok_or(V16Error::ArithmeticOverflow)?
            {
                return Err(V16Error::InvalidLeg);
            }
            if proof.impaired_effective_credit_reserved != 0 && proof.impaired_face_claim_num == 0 {
                return Err(V16Error::InvalidLeg);
            }
            if (source.source_lien_counterparty_backing_num.get() == 0
                && source.source_lien_fee_last_slot.get() != 0)
                || source.source_lien_fee_last_slot.get() > market.header.current_slot.get()
            {
                return Err(V16Error::InvalidLeg);
            }
            slot_index += 1;
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_validate_source_credit_shape_with_market<T>(
        &self,
        market: &MarketGroupV16View<'_, T>,
    ) -> V16Result<()> {
        self.validate_source_credit_shape_with_market(market)
    }

    fn source_claim_bound_sum_num(&self) -> V16Result<u128> {
        let mut sum = 0u128;
        let mut d = 0usize;
        while d < PORTFOLIO_SOURCE_DOMAIN_CAP {
            sum = sum
                .checked_add(self.source_domains()[d].source_claim_bound_num.get())
                .ok_or(V16Error::ArithmeticOverflow)?;
            d += 1;
        }
        Ok(sum)
    }

    fn validate_resolved_payout_receipt_static(receipt: ResolvedPayoutReceiptV16) -> V16Result<()> {
        validate_resolved_payout_receipt_value(receipt)
    }

    fn validate_close_progress_ledger_with_market<T>(
        &self,
        market: &MarketGroupV16View<'_, T>,
    ) -> V16Result<()> {
        let ledger = self.header.close_progress.try_to_runtime()?;
        let configured_assets = market.header.config.max_market_slots.get() as usize;
        if ledger.canceled {
            if ledger.active
                || ledger.finalized
                || ledger.close_id == 0
                || ledger.asset_index as usize >= configured_assets
                || ledger.drift_reference_slot > ledger.max_close_slot
                || ledger.has_irreversible_progress()
                || ledger.residual_remaining != ledger.gross_loss_at_close_start
            {
                return Err(V16Error::InvalidLeg);
            }
            return Ok(());
        }
        if !ledger.active {
            if !ledger.is_empty() {
                return Err(V16Error::InvalidLeg);
            }
            return Ok(());
        }
        let asset_index = ledger.asset_index as usize;
        if ledger.close_id == 0
            || asset_index >= configured_assets
            || asset_index >= market.markets.len()
            || ledger.market_id != market.markets[asset_index].engine.asset.market_id.get()
            || ledger.drift_reference_slot > ledger.max_close_slot
            || ledger.max_close_slot < ledger.drift_reference_slot
            || ledger.support_consumed > ledger.junior_face_burned
            || ledger.canceled
        {
            return Err(V16Error::InvalidLeg);
        }
        let progress = ledger
            .support_consumed
            .checked_add(ledger.insurance_spent)
            .and_then(|v| v.checked_add(ledger.b_loss_booked))
            .and_then(|v| v.checked_add(ledger.explicit_loss_assigned))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let total_loss = ledger
            .gross_loss_at_close_start
            .checked_add(ledger.drift_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if progress > total_loss || ledger.residual_remaining != total_loss - progress {
            return Err(V16Error::InvalidLeg);
        }
        if ledger.finalized && ledger.residual_remaining != 0 {
            return Err(V16Error::InvalidLeg);
        }
        if ledger.quantity_adl_applied_q != 0
            && (!ledger.finalized || ledger.residual_remaining != 0)
        {
            return Err(V16Error::InvalidLeg);
        }
        if ledger.active {
            if let Some(slot) = self.active_leg_slot_for_asset(asset_index)? {
                let leg = self.header.legs[slot].try_to_runtime()?;
                if leg.active && ledger.domain_side != opposite_side(leg.side) {
                    return Err(V16Error::InvalidLeg);
                }
            }
        }
        Ok(())
    }

    fn active_leg_slot_for_asset(&self, asset_index: usize) -> V16Result<Option<usize>> {
        let mut found = None;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = self.header.legs[slot].try_to_runtime()?;
            if leg.active && leg.asset_index as usize == asset_index {
                if found.is_some() {
                    return Err(V16Error::HiddenLeg);
                }
                found = Some(slot);
            }
            slot += 1;
        }
        Ok(found)
    }

    #[cfg(kani)]
    pub fn kani_active_leg_slot_for_asset(&self, asset_index: usize) -> V16Result<Option<usize>> {
        self.active_leg_slot_for_asset(asset_index)
    }

    fn is_empty_for_dematerialization(&self) -> V16Result<bool> {
        if !active_bitmap_is_empty(self.header.active_bitmap.map(V16PodU64::get))
            || self.header.capital.get() != 0
            || self.header.pnl.get() != 0
            || self.header.reserved_pnl.get() != 0
            || self.header.fee_credits.get() != 0
            || self.header.cancel_deposit_escrow.get() != 0
            || decode_bool(self.header.stale_state)?
            || decode_bool(self.header.b_stale_state)?
            || decode_bool(self.header.rebalance_lock)?
            || decode_bool(self.header.liquidation_lock)?
        {
            return Ok(false);
        }

        let close_progress = self.header.close_progress.try_to_runtime()?;
        let inert_canceled_close = close_progress.canceled
            && !close_progress.active
            && !close_progress.finalized
            && close_progress.close_id != 0
            && !close_progress.has_irreversible_progress()
            && close_progress.residual_remaining == close_progress.gross_loss_at_close_start;
        if !close_progress.is_empty()
            && !inert_canceled_close
            && !close_progress.is_finalized_inert()
        {
            return Ok(false);
        }

        let receipt = self.header.resolved_payout_receipt.try_to_runtime()?;
        if receipt.present && !receipt.finalized {
            return Ok(false);
        }

        let mut d = 0usize;
        while d < PORTFOLIO_SOURCE_DOMAIN_CAP {
            if self.header.source_domains[d].is_occupied() {
                return Ok(false);
            }
            d += 1;
        }
        Ok(true)
    }
}

impl<'a> PortfolioV16ViewMut<'a> {
    pub fn validate_with_market<T>(&self, market: &MarketGroupV16View<'_, T>) -> V16Result<()> {
        self.as_view().validate_with_market(market)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PortfolioLegV16 {
    pub active: bool,
    pub asset_index: u32,
    pub market_id: u64,
    pub side: SideV16,
    pub basis_pos_q: i128,
    pub a_basis: u128,
    pub k_snap: i128,
    pub f_snap: i128,
    pub kf_epoch_snap: u64,
    pub epoch_snap: u64,
    pub loss_weight: u128,
    pub b_snap: u128,
    pub b_rem: u128,
    pub b_epoch_snap: u64,
    pub b_stale: bool,
    pub stale: bool,
}

impl PortfolioLegV16 {
    pub const EMPTY: Self = Self {
        active: false,
        asset_index: 0,
        market_id: 0,
        side: SideV16::Long,
        basis_pos_q: 0,
        a_basis: ADL_ONE,
        k_snap: 0,
        f_snap: 0,
        kf_epoch_snap: 0,
        epoch_snap: 0,
        loss_weight: 0,
        b_snap: 0,
        b_rem: 0,
        b_epoch_snap: 0,
        b_stale: false,
        stale: false,
    };

    pub fn is_empty(self) -> bool {
        !self.active
            && self.asset_index == 0
            && self.market_id == 0
            && matches!(self.side, SideV16::Long)
            && self.basis_pos_q == 0
            && self.a_basis == ADL_ONE
            && self.k_snap == 0
            && self.f_snap == 0
            && self.kf_epoch_snap == 0
            && self.epoch_snap == 0
            && self.loss_weight == 0
            && self.b_snap == 0
            && self.b_rem == 0
            && self.b_epoch_snap == 0
            && !self.b_stale
            && !self.stale
    }
}

impl Default for PortfolioLegV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct HealthCertV16 {
    pub certified_equity: i128,
    pub certified_initial_req: u128,
    pub certified_maintenance_req: u128,
    pub certified_liq_deficit: u128,
    pub certified_worst_case_loss: u128,
    pub cert_oracle_epoch: u64,
    pub cert_funding_epoch: u64,
    pub cert_risk_epoch: u64,
    pub cert_asset_set_epoch: u64,
    pub active_bitmap_at_cert: V16ActiveBitmap,
    pub valid: bool,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CloseProgressLedgerV16 {
    pub active: bool,
    pub finalized: bool,
    pub canceled: bool,
    pub close_id: u64,
    pub asset_index: u32,
    pub market_id: u64,
    pub domain_side: SideV16,
    pub gross_loss_at_close_start: u128,
    pub drift_reference_slot: u64,
    pub max_close_slot: u64,
    pub support_consumed: u128,
    pub junior_face_burned: u128,
    pub insurance_spent: u128,
    pub b_loss_booked: u128,
    pub explicit_loss_assigned: u128,
    pub quantity_adl_applied_q: u128,
    pub drift_consumed: u128,
    pub residual_remaining: u128,
}

impl CloseProgressLedgerV16 {
    pub const EMPTY: Self = Self {
        active: false,
        finalized: false,
        canceled: false,
        close_id: 0,
        asset_index: 0,
        market_id: 0,
        domain_side: SideV16::Long,
        gross_loss_at_close_start: 0,
        drift_reference_slot: 0,
        max_close_slot: 0,
        support_consumed: 0,
        junior_face_burned: 0,
        insurance_spent: 0,
        b_loss_booked: 0,
        explicit_loss_assigned: 0,
        quantity_adl_applied_q: 0,
        drift_consumed: 0,
        residual_remaining: 0,
    };

    fn has_pending_residual(self) -> bool {
        self.active && !self.finalized && !self.canceled && self.residual_remaining != 0
    }

    fn has_irreversible_progress(self) -> bool {
        self.support_consumed != 0
            || self.junior_face_burned != 0
            || self.insurance_spent != 0
            || self.b_loss_booked != 0
            || self.explicit_loss_assigned != 0
            || self.quantity_adl_applied_q != 0
            || self.drift_consumed != 0
    }

    /// A close that finished paying out (finalized, no residual left) but is
    /// still `active` -- the ledger stays active to preserve close identity /
    /// history (close_id watermark, progress totals) for audit purposes.
    /// Economically it is terminal: no obligation remains. Exempt from the
    /// active-close gates below so it does not strand funds/rent (E6, port
    /// of upstream engine c8aab338; companion to the canceled-ledger
    /// exemption above / Finding E).
    fn is_finalized_inert(self) -> bool {
        self.active && self.finalized && !self.canceled && self.residual_remaining == 0
    }

    /// True when a fresh close may be opened over this ledger: either nothing is
    /// recorded, or the previous close is finalized-inert (paid out in full, kept
    /// `active` only to carry the close-id watermark).
    ///
    /// `begin_close_progress_ledger` enforces exactly this, so every caller that
    /// decides whether to *call* it must ask the same question. Testing the raw
    /// `active` flag instead skips the fresh close for a finalized-inert ledger and
    /// leaves the stale one in place, which `advance_close_progress_ledger` then
    /// refuses -- stranding the account on its next bankruptcy.
    fn close_slot_available(self) -> bool {
        !self.active || self.is_finalized_inert()
    }

    pub fn is_empty(self) -> bool {
        !self.active
            && !self.finalized
            && !self.canceled
            && self.close_id == 0
            && self.asset_index == 0
            && self.market_id == 0
            && matches!(self.domain_side, SideV16::Long)
            && self.gross_loss_at_close_start == 0
            && self.drift_reference_slot == 0
            && self.max_close_slot == 0
            && self.support_consumed == 0
            && self.junior_face_burned == 0
            && self.insurance_spent == 0
            && self.b_loss_booked == 0
            && self.explicit_loss_assigned == 0
            && self.quantity_adl_applied_q == 0
            && self.drift_consumed == 0
            && self.residual_remaining == 0
    }
}

impl Default for CloseProgressLedgerV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedPayoutLedgerV16 {
    pub snapshot_residual: u128,
    pub terminal_claim_exact_receipts_num: u128,
    pub terminal_claim_bound_unreceipted_num: u128,
    pub current_payout_rate_num: u128,
    pub current_payout_rate_den: u128,
    pub snapshot_slot: u64,
    pub payout_halted: bool,
    pub finalized: bool,
}

impl ResolvedPayoutLedgerV16 {
    pub const EMPTY: Self = Self {
        snapshot_residual: 0,
        terminal_claim_exact_receipts_num: 0,
        terminal_claim_bound_unreceipted_num: 0,
        current_payout_rate_num: 0,
        current_payout_rate_den: 0,
        snapshot_slot: 0,
        payout_halted: false,
        finalized: false,
    };
}

impl Default for ResolvedPayoutLedgerV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedPayoutReceiptV16 {
    pub present: bool,
    pub prior_bound_contribution_num: u128,
    pub live_released_face_at_receipt: u128,
    pub terminal_positive_claim_face: u128,
    pub paid_effective: u128,
    pub finalized: bool,
}

impl ResolvedPayoutReceiptV16 {
    pub const EMPTY: Self = Self {
        present: false,
        prior_bound_contribution_num: 0,
        live_released_face_at_receipt: 0,
        terminal_positive_claim_face: 0,
        paid_effective: 0,
        finalized: false,
    };

    pub fn is_empty(self) -> bool {
        !self.present
            && self.prior_bound_contribution_num == 0
            && self.live_released_face_at_receipt == 0
            && self.terminal_positive_claim_face == 0
            && self.paid_effective == 0
            && !self.finalized
    }
}

impl Default for ResolvedPayoutReceiptV16 {
    fn default() -> Self {
        Self::EMPTY
    }
}

fn validate_resolved_payout_receipt_value(receipt: ResolvedPayoutReceiptV16) -> V16Result<()> {
    if !receipt.present {
        if !receipt.is_empty() {
            return Err(V16Error::InvalidLeg);
        }
        return Ok(());
    }
    let exact_num = receipt
        .terminal_positive_claim_face
        .checked_mul(BOUND_SCALE)
        .ok_or(V16Error::ArithmeticOverflow)?;
    if exact_num > receipt.prior_bound_contribution_num
        || receipt.paid_effective > receipt.terminal_positive_claim_face
        || receipt.finalized != (receipt.paid_effective == receipt.terminal_positive_claim_face)
    {
        return Err(V16Error::InvalidLeg);
    }
    Ok(())
}

fn apply_resolved_payout_receipt_payment(
    mut receipt: ResolvedPayoutReceiptV16,
    actual_resolved_paid: u128,
) -> V16Result<ResolvedPayoutReceiptV16> {
    validate_resolved_payout_receipt_value(receipt)?;
    if actual_resolved_paid == 0 {
        return Ok(receipt);
    }
    if !receipt.present {
        return Err(V16Error::InvalidLeg);
    }
    let remaining = receipt
        .terminal_positive_claim_face
        .checked_sub(receipt.paid_effective)
        .ok_or(V16Error::InvalidLeg)?;
    if actual_resolved_paid > remaining {
        return Err(V16Error::InvalidLeg);
    }
    receipt.paid_effective = receipt
        .paid_effective
        .checked_add(actual_resolved_paid)
        .ok_or(V16Error::ArithmeticOverflow)?;
    receipt.finalized = receipt.paid_effective == receipt.terminal_positive_claim_face;
    validate_resolved_payout_receipt_value(receipt)?;
    Ok(receipt)
}

#[cfg(kani)]
pub fn kani_apply_resolved_payout_receipt_payment(
    receipt: ResolvedPayoutReceiptV16,
    actual_resolved_paid: u128,
) -> V16Result<ResolvedPayoutReceiptV16> {
    apply_resolved_payout_receipt_payment(receipt, actual_resolved_paid)
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccrueAssetOutcomeV16 {
    pub dt: u64,
    pub price_move_active: bool,
    pub funding_active: bool,
    pub equity_active: bool,
    pub loss_stale_after: bool,
}

/// Maximum canonical one-slot accrual steps that one public wrapper call may commit.
/// Longer gaps remain actionable across additional bounded calls.
pub const V16_MAX_ACCRUAL_PATH_STEPS: usize = 32;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccrualStepV16 {
    pub effective_price: u64,
    pub funding_rate_e9: i128,
    pub price_move_remainder_before_bps_num: u16,
    pub price_move_remainder_after_bps_num: u16,
}

/// Computes one canonical price-cap step while carrying sub-atom movement forward.
///
/// `cap_anchor` is fixed for the lifetime of one raw-oracle target. Using that stable anchor makes
/// the cumulative movement exactly the configured linear `max_change_bps * dt` envelope instead
/// of compounding the cap at caller-selected transaction boundaries. The remainder is the
/// numerator left after division by `MAX_MARGIN_BPS`; carrying it across calls prevents permanent
/// low-price target pinning.
pub fn canonical_accrual_price_step_v16(
    current: u64,
    target: u64,
    cap_anchor: u64,
    max_change_bps: u64,
    exposed: bool,
    remainder_before_bps_num: u16,
) -> V16Result<(u64, u16)> {
    if current == 0
        || target == 0
        || cap_anchor == 0
        || current > MAX_ORACLE_PRICE
        || target > MAX_ORACLE_PRICE
        || cap_anchor > MAX_ORACLE_PRICE
        || remainder_before_bps_num as u64 >= MAX_MARGIN_BPS
    {
        return Err(V16Error::InvalidConfig);
    }
    if !exposed {
        return Ok((target, 0));
    }
    if current == target || max_change_bps == 0 {
        return Ok((current, 0));
    }
    let numerator = (cap_anchor as u128)
        .checked_mul(max_change_bps as u128)
        .and_then(|value| value.checked_add(remainder_before_bps_num as u128))
        .ok_or(V16Error::ArithmeticOverflow)?;
    let max_delta = numerator / MAX_MARGIN_BPS as u128;
    let remainder_after = u16::try_from(numerator % MAX_MARGIN_BPS as u128)
        .map_err(|_| V16Error::ArithmeticOverflow)?;
    let distance = current.abs_diff(target) as u128;
    if max_delta >= distance {
        return Ok((target, 0));
    }
    let delta = u64::try_from(max_delta).map_err(|_| V16Error::ArithmeticOverflow)?;
    let next = if target > current {
        current
            .checked_add(delta)
            .ok_or(V16Error::ArithmeticOverflow)?
    } else {
        current
            .checked_sub(delta)
            .ok_or(V16Error::ArithmeticOverflow)?
    };
    Ok((next, remainder_after))
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TradeRequestV16 {
    pub asset_index: usize,
    /// Signed base quantity. Positive makes the first account long; negative
    /// makes the first account short.
    pub size_q: i128,
    pub exec_price: u64,
    pub fee_bps: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TradeOutcomeV16 {
    pub fee_a: u128,
    pub fee_b: u128,
    pub notional: u128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BatchTradeOutcomeV16 {
    pub fill_count: u32,
    pub fee_a: u128,
    pub fee_b: u128,
    pub notional: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TradeApplyOutcomeV16 {
    fee_a: u128,
    fee_b: u128,
    notional: u128,
    risk_increasing: bool,
    long_requires_initial_margin: bool,
    short_requires_initial_margin: bool,
    long_has_source_claims: bool,
    short_has_source_claims: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TradePositionPreflightV16 {
    risk_increasing: bool,
    long_requires_initial_margin: bool,
    short_requires_initial_margin: bool,
    long_lookup: PositionDeltaLookupV16,
    short_lookup: PositionDeltaLookupV16,
    long_old_abs_q: u128,
    short_old_abs_q: u128,
    long_new_abs_q: u128,
    short_new_abs_q: u128,
    long_has_source_claims: bool,
    short_has_source_claims: bool,
}

/// The leg route a position change dispatches to (roadmap 3A.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PositionRouteV16 {
    Attach,
    Clear,
    Flip,
    Resize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PositionDeltaLookupV16 {
    existing_slot: Option<usize>,
    empty_slot: Option<usize>,
    /// Retained per-leg basis before and after the transition.
    current_q: i128,
    next_q: i128,
    /// Economically live quantity before and after the transition. These are
    /// identical to raw basis at unit ADL and differ after quantity ADL.
    current_effective_q: i128,
    next_effective_q: i128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PositionSlotMapV16 {
    assets: [u32; V16_MAX_PORTFOLIO_ASSETS_N],
    positions: [i128; V16_MAX_PORTFOLIO_ASSETS_N],
    a_basis: [u128; V16_MAX_PORTFOLIO_ASSETS_N],
}

impl PositionSlotMapV16 {
    fn from_account(account: &PortfolioV16View<'_>) -> V16Result<Self> {
        let mut out = Self {
            assets: [u32::MAX; V16_MAX_PORTFOLIO_ASSETS_N],
            positions: [0; V16_MAX_PORTFOLIO_ASSETS_N],
            a_basis: [0; V16_MAX_PORTFOLIO_ASSETS_N],
        };
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let in_bitmap = active_bitmap_get(bitmap, slot);
            let leg = account.header.legs[slot].try_to_runtime()?;
            if in_bitmap {
                if !leg.active || out.assets[..slot].contains(&leg.asset_index) {
                    return Err(V16Error::HiddenLeg);
                }
                out.assets[slot] = leg.asset_index;
                out.positions[slot] = signed_position(leg);
                out.a_basis[slot] = leg.a_basis;
            } else if leg.active || !leg.is_empty() {
                return Err(V16Error::HiddenLeg);
            }
            slot += 1;
        }
        Ok(out)
    }

    fn plan_delta(
        &mut self,
        asset_index: usize,
        delta_q: i128,
        asset: AssetStateV16,
    ) -> V16Result<PositionDeltaLookupV16> {
        let asset_index = u32::try_from(asset_index).map_err(|_| V16Error::InvalidLeg)?;
        let existing_slot = self.assets.iter().position(|asset| *asset == asset_index);
        let current_q = existing_slot.map_or(0, |slot| self.positions[slot]);
        let current_effective_q = if let Some(slot) = existing_slot {
            let current_a = match current_q.signum() {
                1 => asset.a_long,
                -1 => asset.a_short,
                _ => return Err(V16Error::HiddenLeg),
            };
            let effective_abs = V16Core::kernel_adl_effective_quantity_ceil(
                current_q.unsigned_abs(),
                self.a_basis[slot],
                current_a,
            )?;
            if current_q > 0 {
                i128::try_from(effective_abs).map_err(|_| V16Error::ArithmeticOverflow)?
            } else {
                i128::try_from(effective_abs)
                    .map_err(|_| V16Error::ArithmeticOverflow)?
                    .checked_neg()
                    .ok_or(V16Error::ArithmeticOverflow)?
            }
        } else {
            0
        };
        let next_effective_q = current_effective_q
            .checked_add(delta_q)
            .ok_or(V16Error::ArithmeticOverflow)?;
        validate_basis_or_zero(next_effective_q)?;
        let next_q =
            match V16Core::kernel_classify_position_delta(current_effective_q, next_effective_q) {
                PositionRouteV16::Attach | PositionRouteV16::Flip => next_effective_q,
                PositionRouteV16::Clear => 0,
                PositionRouteV16::Resize => {
                    let slot = existing_slot.ok_or(V16Error::InvalidLeg)?;
                    let current_a = if next_effective_q > 0 {
                        asset.a_long
                    } else {
                        asset.a_short
                    };
                    let mut next_abs = V16Core::kernel_raw_basis_for_adl_effective_quantity(
                        next_effective_q.unsigned_abs(),
                        self.a_basis[slot],
                        current_a,
                    )?;
                    if next_effective_q.unsigned_abs() <= current_effective_q.unsigned_abs() {
                        next_abs = next_abs.min(current_q.unsigned_abs());
                    }
                    let next_abs =
                        i128::try_from(next_abs).map_err(|_| V16Error::ArithmeticOverflow)?;
                    if next_effective_q > 0 {
                        next_abs
                    } else {
                        next_abs.checked_neg().ok_or(V16Error::ArithmeticOverflow)?
                    }
                }
            };
        validate_basis_or_zero(next_q)?;
        let mut empty_slot = None;
        match V16Core::kernel_classify_position_delta(current_effective_q, next_effective_q) {
            PositionRouteV16::Attach => {
                let slot = self
                    .assets
                    .iter()
                    .position(|asset| *asset == u32::MAX)
                    .ok_or(V16Error::InvalidLeg)?;
                empty_slot = Some(slot);
                self.assets[slot] = asset_index;
                self.positions[slot] = next_q;
                self.a_basis[slot] = if next_q > 0 {
                    asset.a_long
                } else {
                    asset.a_short
                };
            }
            PositionRouteV16::Clear => {
                let slot = existing_slot.ok_or(V16Error::InvalidLeg)?;
                self.assets[slot] = u32::MAX;
                self.positions[slot] = 0;
                self.a_basis[slot] = 0;
            }
            PositionRouteV16::Flip => {
                let slot = existing_slot.ok_or(V16Error::InvalidLeg)?;
                self.assets[slot] = u32::MAX;
                self.positions[slot] = 0;
                self.a_basis[slot] = 0;
                let slot = self
                    .assets
                    .iter()
                    .position(|asset| *asset == u32::MAX)
                    .ok_or(V16Error::InvalidLeg)?;
                empty_slot = Some(slot);
                self.assets[slot] = asset_index;
                self.positions[slot] = next_q;
                self.a_basis[slot] = if next_q > 0 {
                    asset.a_long
                } else {
                    asset.a_short
                };
            }
            PositionRouteV16::Resize => {
                let slot = existing_slot.ok_or(V16Error::InvalidLeg)?;
                self.positions[slot] = next_q;
            }
        }
        Ok(PositionDeltaLookupV16 {
            existing_slot,
            empty_slot,
            current_q,
            next_q,
            current_effective_q,
            next_effective_q,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AccountRefreshCertOutcomeV16 {
    Certified(HealthCertV16),
    BChunk(AccountBSettlementChunkV16),
    SourceBackingExpired(usize),
}

#[cfg(kani)]
pub const V16_TOKEN_VALUE_CLASS_COUNT: usize = 17;
#[cfg(not(kani))]
const V16_TOKEN_VALUE_CLASS_COUNT: usize = 17;

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(kani)]
pub enum TokenValueClassV16 {
    TokenVault = 0,
    SeniorCapital = 1,
    InsuranceCapital = 2,
    AccountCapital = 3,
    CloseSupportConsumed = 4,
    CloseInsuranceSpent = 5,
    CloseCounterpartyCreditConsumed = 6,
    BResidualBooked = 7,
    PendingObligationEscrow = 8,
    PendingObligationCredit = 9,
    ExplicitBackedLoss = 10,
    SettlementRoundingResidue = 11,
    CancelDepositEscrow = 12,
    ResolvedPayoutPaid = 13,
    ProtocolFeePaid = 14,
    ExternalQuote = 15,
    UnallocatedProtocolSurplus = 16,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(not(kani))]
#[allow(dead_code)]
enum TokenValueClassV16 {
    TokenVault = 0,
    SeniorCapital = 1,
    InsuranceCapital = 2,
    AccountCapital = 3,
    CloseSupportConsumed = 4,
    CloseInsuranceSpent = 5,
    CloseCounterpartyCreditConsumed = 6,
    BResidualBooked = 7,
    PendingObligationEscrow = 8,
    PendingObligationCredit = 9,
    ExplicitBackedLoss = 10,
    SettlementRoundingResidue = 11,
    CancelDepositEscrow = 12,
    ResolvedPayoutPaid = 13,
    ProtocolFeePaid = 14,
    ExternalQuote = 15,
    UnallocatedProtocolSurplus = 16,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(kani)]
pub struct TokenValueFlowProofV16 {
    pub debits: [u128; V16_TOKEN_VALUE_CLASS_COUNT],
    pub credits: [u128; V16_TOKEN_VALUE_CLASS_COUNT],
    pub external_quote_in: u128,
    pub external_quote_out: u128,
    pub vault_before: u128,
    pub vault_after: u128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(not(kani))]
struct TokenValueFlowProofV16 {
    debits: [u128; V16_TOKEN_VALUE_CLASS_COUNT],
    credits: [u128; V16_TOKEN_VALUE_CLASS_COUNT],
    external_quote_in: u128,
    external_quote_out: u128,
    vault_before: u128,
    vault_after: u128,
}

impl TokenValueFlowProofV16 {
    pub const fn empty(vault_before: u128, vault_after: u128) -> Self {
        Self {
            debits: [0; V16_TOKEN_VALUE_CLASS_COUNT],
            credits: [0; V16_TOKEN_VALUE_CLASS_COUNT],
            external_quote_in: 0,
            external_quote_out: 0,
            vault_before,
            vault_after,
        }
    }

    pub fn external_in_to_account_capital(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.external_quote_in = amount;
        proof.credit(TokenValueClassV16::ExternalQuote, amount)?;
        proof.debit(TokenValueClassV16::AccountCapital, amount)?;
        Ok(proof)
    }

    pub fn account_capital_to_external_out(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.external_quote_out = amount;
        proof.debit(TokenValueClassV16::AccountCapital, amount)?;
        proof.credit(TokenValueClassV16::ExternalQuote, amount)?;
        Ok(proof)
    }

    pub fn close_cure_to_account_capital(
        optional_external_deposit: u128,
        cancel_deposit_escrow: u128,
        capital_credit: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let expected_credit = optional_external_deposit
            .checked_add(cancel_deposit_escrow)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if expected_credit != capital_credit {
            return Err(V16Error::InvalidConfig);
        }
        let mut proof = Self::empty(vault_before, vault_after);
        proof.external_quote_in = optional_external_deposit;
        proof.credit(TokenValueClassV16::ExternalQuote, optional_external_deposit)?;
        proof.credit(
            TokenValueClassV16::CancelDepositEscrow,
            cancel_deposit_escrow,
        )?;
        proof.debit(TokenValueClassV16::AccountCapital, capital_credit)?;
        Ok(proof)
    }

    pub fn account_capital_to_insurance(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.debit(TokenValueClassV16::AccountCapital, amount)?;
        proof.credit(TokenValueClassV16::InsuranceCapital, amount)?;
        Ok(proof)
    }

    fn external_in_to_insurance_capital(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.external_quote_in = amount;
        proof.credit(TokenValueClassV16::ExternalQuote, amount)?;
        proof.debit(TokenValueClassV16::InsuranceCapital, amount)?;
        Ok(proof)
    }

    fn insurance_capital_to_external_out(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.external_quote_out = amount;
        proof.debit(TokenValueClassV16::InsuranceCapital, amount)?;
        proof.credit(TokenValueClassV16::ExternalQuote, amount)?;
        Ok(proof)
    }

    fn insurance_capital_to_account_capital(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.debit(TokenValueClassV16::InsuranceCapital, amount)?;
        proof.credit(TokenValueClassV16::AccountCapital, amount)?;
        Ok(proof)
    }

    fn unallocated_protocol_surplus_to_insurance(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.debit(TokenValueClassV16::UnallocatedProtocolSurplus, amount)?;
        proof.credit(TokenValueClassV16::InsuranceCapital, amount)?;
        Ok(proof)
    }

    pub fn account_capital_to_realized_loss(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.debit(TokenValueClassV16::AccountCapital, amount)?;
        proof.credit(TokenValueClassV16::ExplicitBackedLoss, amount)?;
        Ok(proof)
    }

    pub fn insurance_to_close_insurance_spent(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let mut proof = Self::empty(vault_before, vault_after);
        proof.debit(TokenValueClassV16::InsuranceCapital, amount)?;
        proof.credit(TokenValueClassV16::CloseInsuranceSpent, amount)?;
        Ok(proof)
    }

    pub fn validate_insurance_to_close_insurance_spent(
        amount: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<()> {
        Self::insurance_to_close_insurance_spent(amount, vault_before, vault_after)?.validate()
    }

    pub fn support_to_account_capital(
        account_capital_credit: u128,
        counterparty_credit_consumed: u128,
        insurance_credit_consumed: u128,
        protocol_surplus_consumed: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let source_total = counterparty_credit_consumed
            .checked_add(insurance_credit_consumed)
            .and_then(|v| v.checked_add(protocol_surplus_consumed))
            .ok_or(V16Error::ArithmeticOverflow)?;
        if source_total != account_capital_credit {
            return Err(V16Error::InvalidConfig);
        }
        let mut proof = Self::empty(vault_before, vault_after);
        proof.credit(
            TokenValueClassV16::CloseCounterpartyCreditConsumed,
            counterparty_credit_consumed,
        )?;
        proof.credit(
            TokenValueClassV16::CloseInsuranceSpent,
            insurance_credit_consumed,
        )?;
        proof.credit(
            TokenValueClassV16::UnallocatedProtocolSurplus,
            protocol_surplus_consumed,
        )?;
        proof.debit(TokenValueClassV16::AccountCapital, account_capital_credit)?;
        Ok(proof)
    }

    pub fn capital_and_resolved_payout_to_external_out(
        capital_paid: u128,
        resolved_payout_paid: u128,
        total_external_out: u128,
        vault_before: u128,
        vault_after: u128,
    ) -> V16Result<Self> {
        let total_source = capital_paid
            .checked_add(resolved_payout_paid)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if total_source != total_external_out {
            return Err(V16Error::InvalidConfig);
        }
        let mut proof = Self::empty(vault_before, vault_after);
        proof.external_quote_out = total_external_out;
        proof.debit(TokenValueClassV16::AccountCapital, capital_paid)?;
        proof.debit(TokenValueClassV16::ResolvedPayoutPaid, resolved_payout_paid)?;
        proof.credit(TokenValueClassV16::ExternalQuote, total_external_out)?;
        Ok(proof)
    }

    pub fn debit(&mut self, class: TokenValueClassV16, amount: u128) -> V16Result<()> {
        let idx = class as usize;
        self.debits[idx] = self.debits[idx]
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok(())
    }

    pub fn credit(&mut self, class: TokenValueClassV16, amount: u128) -> V16Result<()> {
        let idx = class as usize;
        self.credits[idx] = self.credits[idx]
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok(())
    }

    pub fn validate(&self) -> V16Result<()> {
        let mut total_debits = 0u128;
        let mut total_credits = 0u128;
        let mut i = 0;
        while i < V16_TOKEN_VALUE_CLASS_COUNT {
            total_debits = total_debits
                .checked_add(self.debits[i])
                .ok_or(V16Error::ArithmeticOverflow)?;
            total_credits = total_credits
                .checked_add(self.credits[i])
                .ok_or(V16Error::ArithmeticOverflow)?;
            i += 1;
        }
        if total_debits != total_credits {
            return Err(V16Error::InvalidConfig);
        }

        if self.vault_after >= self.vault_before {
            let vault_delta = self.vault_after - self.vault_before;
            if self.external_quote_in < self.external_quote_out
                || self.external_quote_in - self.external_quote_out != vault_delta
            {
                return Err(V16Error::InvalidConfig);
            }
        } else {
            let vault_delta = self.vault_before - self.vault_after;
            if self.external_quote_out < self.external_quote_in
                || self.external_quote_out - self.external_quote_in != vault_delta
            {
                return Err(V16Error::InvalidConfig);
            }
        }
        Ok(())
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ReservationEncumbranceProofV16 {
    domain: u16,
    exact_positive_claim_num: u128,
    positive_claim_bound_num: u128,
    source_fresh_reserved_backing_num: u128,
    source_spent_backing_num: u128,
    source_provider_receivable_num: u128,
    bucket_fresh_unliened_backing_num: u128,
    bucket_valid_liened_backing_num: u128,
    bucket_consumed_liened_backing_num: u128,
    source_valid_liened_backing_num: u128,
    source_impaired_liened_backing_num: u128,
    bucket_impaired_liened_backing_num: u128,
    source_insurance_credit_reserved_num: u128,
    reservation_insurance_credit_reserved_num: u128,
    source_valid_liened_insurance_num: u128,
    reservation_valid_liened_insurance_num: u128,
    source_impaired_liened_insurance_num: u128,
    reservation_impaired_liened_insurance_num: u128,
    source_credit_rate_num: u128,
}

impl ReservationEncumbranceProofV16 {
    fn validate(&self) -> V16Result<()> {
        let fresh_reserved = self
            .bucket_fresh_unliened_backing_num
            .checked_add(self.bucket_valid_liened_backing_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if self.source_fresh_reserved_backing_num != fresh_reserved
            || self.source_provider_receivable_num != self.bucket_consumed_liened_backing_num
            || self.source_spent_backing_num < self.source_provider_receivable_num
            || self.source_valid_liened_backing_num != self.bucket_valid_liened_backing_num
            || self.source_impaired_liened_backing_num != self.bucket_impaired_liened_backing_num
            || self.source_insurance_credit_reserved_num
                != self.reservation_insurance_credit_reserved_num
            || self.source_valid_liened_insurance_num != self.reservation_valid_liened_insurance_num
            || self.source_impaired_liened_insurance_num
                != self.reservation_impaired_liened_insurance_num
        {
            return Err(V16Error::InvalidConfig);
        }
        let insurance_encumbered = self
            .reservation_valid_liened_insurance_num
            .checked_add(self.reservation_impaired_liened_insurance_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if self.reservation_insurance_credit_reserved_num < insurance_encumbered {
            return Err(V16Error::InvalidConfig);
        }
        let source = SourceCreditStateV16 {
            exact_positive_claim_num: self.exact_positive_claim_num,
            positive_claim_bound_num: self.positive_claim_bound_num,
            fresh_reserved_backing_num: self.source_fresh_reserved_backing_num,
            valid_liened_backing_num: self.source_valid_liened_backing_num,
            impaired_liened_backing_num: self.source_impaired_liened_backing_num,
            spent_backing_num: self.source_spent_backing_num,
            provider_receivable_num: self.source_provider_receivable_num,
            insurance_credit_reserved_num: self.source_insurance_credit_reserved_num,
            valid_liened_insurance_num: self.source_valid_liened_insurance_num,
            impaired_liened_insurance_num: self.source_impaired_liened_insurance_num,
            credit_rate_num: self.source_credit_rate_num,
            credit_epoch: 0,
        };
        V16Core::validate_source_credit_state_static(source)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(kani)]
pub struct StockReconciliationProofV16 {
    pub token_vault: u128,
    pub senior_capital_total: u128,
    pub insurance_capital: u128,
    pub backing_provider_earnings: u128,
    pub counterparty_backing_principal: u128,
    pub settlement_rounding_residue_total: u128,
    pub unallocated_protocol_surplus: u128,
}

#[cfg(kani)]
impl StockReconciliationProofV16 {
    pub fn validate(&self) -> V16Result<()> {
        let accounted = self
            .senior_capital_total
            .checked_add(self.insurance_capital)
            .and_then(|v| v.checked_add(self.backing_provider_earnings))
            .and_then(|v| v.checked_add(self.counterparty_backing_principal))
            .and_then(|v| v.checked_add(self.settlement_rounding_residue_total))
            .and_then(|v| v.checked_add(self.unallocated_protocol_surplus))
            .ok_or(V16Error::ArithmeticOverflow)?;
        if accounted != self.token_vault {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SourceCreditLienAggregateProofV16 {
    domain: u16,
    source_claim_bound_num: u128,
    face_claim_locked_num: u128,
    counterparty_face_claim_locked_num: u128,
    insurance_face_claim_locked_num: u128,
    effective_credit_reserved: u128,
    counterparty_backing_reserved_num: u128,
    insurance_backing_reserved_num: u128,
    impaired_face_claim_num: u128,
    impaired_effective_credit_reserved: u128,
}

impl SourceCreditLienAggregateProofV16 {
    fn validate(&self) -> V16Result<()> {
        let backing_face = self
            .counterparty_face_claim_locked_num
            .checked_add(self.insurance_face_claim_locked_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if backing_face != self.face_claim_locked_num {
            return Err(V16Error::InvalidLeg);
        }
        let locked_or_impaired = self
            .face_claim_locked_num
            .checked_add(self.impaired_face_claim_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if locked_or_impaired > self.source_claim_bound_num {
            return Err(V16Error::InvalidLeg);
        }
        if self.effective_credit_reserved
            > V16Core::amount_from_bound_num(self.face_claim_locked_num)?
        {
            return Err(V16Error::InvalidLeg);
        }
        if self.counterparty_backing_reserved_num % BOUND_SCALE != 0
            || self.insurance_backing_reserved_num % BOUND_SCALE != 0
        {
            return Err(V16Error::InvalidLeg);
        }
        let backing_num = self
            .counterparty_backing_reserved_num
            .checked_add(self.insurance_backing_reserved_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let expected_backing_num = self
            .effective_credit_reserved
            .checked_mul(BOUND_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if backing_num != expected_backing_num {
            return Err(V16Error::InvalidLeg);
        }
        if self.impaired_effective_credit_reserved != 0 && self.impaired_face_claim_num == 0 {
            return Err(V16Error::InvalidLeg);
        }
        Ok(())
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiquidationRequestV16 {
    pub asset_index: usize,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiquidationOutcomeV16 {
    pub closed_q: u128,
    pub insurance_used: u128,
    pub residual_booked: u128,
    pub explicit_loss: u128,
    pub fee_charged: u128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeadLegForfeitOutcomeV16 {
    pub detached: bool,
    pub positive_pnl_forfeited: u128,
    pub loss_settled: u128,
    pub support_consumed: u128,
    pub junior_face_burned: u128,
    pub principal_used: u128,
    pub insurance_used: u128,
    pub residual_booked: u128,
    pub explicit_loss: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SupportLossApplicationV16 {
    support_consumed: u128,
    junior_face_burned: u128,
}

const ACCOUNT_KF_SETTLEMENT_DOMAIN_MAX: u64 = u32::MAX as u64 * 2 + 1;
const ACCOUNT_KF_SETTLEMENT_PHASE_SHIFT: u32 = 37;
const ACCOUNT_KF_SETTLEMENT_KEY_MAX: u64 = (1u64 << 38) - 1;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct AccountKfSettlementPreparedV16 {
    k_now: i128,
    f_now: i128,
    f_delta: i128,
    net: i128,
}

fn account_kf_settlement_plan_key(
    phase: u8,
    source_domain: usize,
    leg_slot: usize,
) -> V16Result<u64> {
    let domain = u64::try_from(source_domain).map_err(|_| V16Error::InvalidLeg)?;
    if phase > 1
        || domain > ACCOUNT_KF_SETTLEMENT_DOMAIN_MAX
        || leg_slot >= V16_MAX_PORTFOLIO_ASSETS_N
    {
        return Err(V16Error::InvalidLeg);
    }
    Ok((u64::from(phase) << ACCOUNT_KF_SETTLEMENT_PHASE_SHIFT) | (domain << 4) | leg_slot as u64)
}

fn decode_account_kf_settlement_plan_key(key: u64) -> V16Result<(u8, usize, usize)> {
    if key > ACCOUNT_KF_SETTLEMENT_KEY_MAX {
        return Err(V16Error::InvalidLeg);
    }
    let phase = (key >> ACCOUNT_KF_SETTLEMENT_PHASE_SHIFT) as u8;
    let source_domain = usize::try_from((key >> 4) & ACCOUNT_KF_SETTLEMENT_DOMAIN_MAX)
        .map_err(|_| V16Error::InvalidLeg)?;
    let leg_slot = (key & 0xf) as usize;
    if account_kf_settlement_plan_key(phase, source_domain, leg_slot)? != key {
        return Err(V16Error::InvalidLeg);
    }
    Ok((phase, source_domain, leg_slot))
}

fn insert_account_kf_settlement_plan_entry(
    plan: &mut [Option<u64>; V16_MAX_PORTFOLIO_ASSETS_N],
    plan_len: usize,
    entry: u64,
) -> V16Result<usize> {
    if plan_len >= V16_MAX_PORTFOLIO_ASSETS_N || plan[plan_len].is_some() {
        return Err(V16Error::InvalidLeg);
    }
    let mut insert_at = plan_len;
    while insert_at > 0 {
        let incumbent = plan[insert_at - 1].ok_or(V16Error::InvalidLeg)?;
        if entry >= incumbent {
            break;
        }
        plan[insert_at] = Some(incumbent);
        insert_at -= 1;
    }
    plan[insert_at] = Some(entry);
    plan_len.checked_add(1).ok_or(V16Error::CounterOverflow)
}

#[cfg(kani)]
pub const KANI_ACCOUNT_KF_SETTLEMENT_DOMAIN_MAX: u64 = ACCOUNT_KF_SETTLEMENT_DOMAIN_MAX;
#[cfg(kani)]
pub const KANI_ACCOUNT_KF_SETTLEMENT_KEY_MAX: u64 = ACCOUNT_KF_SETTLEMENT_KEY_MAX;

#[cfg(kani)]
pub fn kani_account_kf_settlement_plan_key(
    phase: u8,
    source_domain: usize,
    leg_slot: usize,
) -> V16Result<u64> {
    account_kf_settlement_plan_key(phase, source_domain, leg_slot)
}

#[cfg(kani)]
pub fn kani_decode_account_kf_settlement_plan_key(key: u64) -> V16Result<(u8, usize, usize)> {
    decode_account_kf_settlement_plan_key(key)
}

#[cfg(kani)]
pub fn kani_insert_account_kf_settlement_plan_entry(
    plan: &mut [Option<u64>; V16_MAX_PORTFOLIO_ASSETS_N],
    plan_len: usize,
    entry: u64,
) -> V16Result<usize> {
    insert_account_kf_settlement_plan_entry(plan, plan_len, entry)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SourceCreditConsumptionV16 {
    face_burn: u128,
    counterparty_credit_consumed: u128,
    insurance_credit_consumed: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReleasedPnlConversionDispositionV16 {
    ConsumeHaircutFace,
    RetainHaircutFaceForTerminalDomain {
        source_domain: usize,
        source_claim_num: u128,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResolvedSourcePreparationV16 {
    BackingNormalized,
    LienReleased,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SourceCreditBackingSourceV16 {
    Counterparty,
    Insurance,
}

/// The single bounded transition a flat account's source-lien domain may take
/// this call. (upstream 6c8d94bc)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlatSourceLienNormalizationV16 {
    None,
    ImpairCounterparty,
    Release,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RebalanceRequestV16 {
    pub asset_index: usize,
    pub reduce_q: u128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RebalanceOutcomeV16 {
    pub reduced_q: u128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BResidualBookingOutcomeV16 {
    pub booked_loss: u128,
    pub explicit_loss: u128,
    pub delta_b: u128,
    pub remaining_after: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ForfeitResidualStepV16 {
    NoResidual,
    Book,
    CommitRecovery,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PermissionlessCrankActionV16 {
    Refresh,
    SettleB { asset_index: usize },
    Liquidate(LiquidationRequestV16),
    Recover(PermissionlessRecoveryReasonV16),
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PermissionlessCrankRequestV16 {
    pub now_slot: u64,
    pub asset_index: usize,
    pub effective_price: u64,
    pub funding_rate_e9: i128,
    pub action: PermissionlessCrankActionV16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolvedCloseOutcomeV16 {
    ProgressOnly,
    Closed { payout: u128 },
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16PodU16 {
    pub bytes: [u8; 2],
}

impl V16PodU16 {
    pub fn new(value: u16) -> Self {
        Self {
            bytes: value.to_le_bytes(),
        }
    }

    pub fn get(self) -> u16 {
        u16::from_le_bytes(self.bytes)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16PodU32 {
    pub bytes: [u8; 4],
}

impl V16PodU32 {
    pub fn new(value: u32) -> Self {
        Self {
            bytes: value.to_le_bytes(),
        }
    }

    pub fn get(self) -> u32 {
        u32::from_le_bytes(self.bytes)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16PodU64 {
    pub bytes: [u8; 8],
}

impl V16PodU64 {
    pub fn new(value: u64) -> Self {
        Self {
            bytes: value.to_le_bytes(),
        }
    }

    pub fn get(self) -> u64 {
        u64::from_le_bytes(self.bytes)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16PodU128 {
    pub bytes: [u8; 16],
}

impl V16PodU128 {
    pub fn new(value: u128) -> Self {
        Self {
            bytes: value.to_le_bytes(),
        }
    }

    pub fn get(self) -> u128 {
        u128::from_le_bytes(self.bytes)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16PodI128 {
    pub bytes: [u8; 16],
}

impl V16PodI128 {
    pub fn new(value: i128) -> Self {
        Self {
            bytes: value.to_le_bytes(),
        }
    }

    pub fn get(self) -> i128 {
        i128::from_le_bytes(self.bytes)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16OptionalRecoveryReasonAccount {
    pub present: u8,
    pub value: u8,
}

impl V16OptionalRecoveryReasonAccount {
    pub fn from_runtime(value: Option<PermissionlessRecoveryReasonV16>) -> Self {
        match value {
            Some(reason) => Self {
                present: 1,
                value: encode_recovery_reason(reason),
            },
            None => Self {
                present: 0,
                value: 0,
            },
        }
    }

    pub fn try_to_runtime(self) -> V16Result<Option<PermissionlessRecoveryReasonV16>> {
        match self.present {
            0 if self.value == 0 => Ok(None),
            1 => Ok(Some(decode_recovery_reason(self.value)?)),
            _ => Err(V16Error::InvalidConfig),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct ProvenanceHeaderV16Account {
    pub market_group_id: [u8; 32],
    pub portfolio_account_id: [u8; 32],
    pub owner: [u8; 32],
    pub version: V16PodU16,
    pub layout_discriminator: V16PodU16,
}

impl ProvenanceHeaderV16Account {
    pub fn from_runtime(value: &ProvenanceHeaderV16) -> Self {
        Self {
            market_group_id: value.market_group_id,
            portfolio_account_id: value.portfolio_account_id,
            owner: value.owner,
            version: V16PodU16::new(value.version),
            layout_discriminator: V16PodU16::new(value.layout_discriminator),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<ProvenanceHeaderV16> {
        let out = ProvenanceHeaderV16 {
            market_group_id: self.market_group_id,
            portfolio_account_id: self.portfolio_account_id,
            owner: self.owner,
            version: self.version.get(),
            layout_discriminator: self.layout_discriminator.get(),
        };
        if out.version != V16_ACCOUNT_VERSION
            || out.layout_discriminator != V16_LAYOUT_DISCRIMINATOR
        {
            return Err(V16Error::ProvenanceMismatch);
        }
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct V16ConfigAccount {
    pub max_portfolio_assets: V16PodU16,
    pub max_market_slots: V16PodU32,
    pub min_nonzero_mm_req: V16PodU128,
    pub min_nonzero_im_req: V16PodU128,
    pub h_min: V16PodU64,
    pub h_max: V16PodU64,
    pub maintenance_margin_bps: V16PodU64,
    pub initial_margin_bps: V16PodU64,
    pub max_trading_fee_bps: V16PodU64,
    pub liquidation_fee_bps: V16PodU64,
    pub liquidation_fee_cap: V16PodU128,
    pub min_liquidation_abs: V16PodU128,
    pub max_accrual_dt_slots: V16PodU64,
    pub max_abs_funding_e9_per_slot: V16PodU64,
    pub min_funding_lifetime_slots: V16PodU64,
    pub max_price_move_bps_per_slot: V16PodU64,
    pub max_account_b_settlement_chunks: V16PodU64,
    pub max_bankrupt_close_chunks: V16PodU64,
    pub max_bankrupt_close_lifetime_slots: V16PodU64,
    pub asset_activation_cooldown_slots: V16PodU64,
    pub public_b_chunk_atoms: V16PodU128,
    pub max_recovery_fallback_deviation_bps: V16PodU64,
    pub backing_fee_base_rate_e9_per_slot: V16PodU64,
    pub backing_fee_kink_util_bps: V16PodU64,
    pub backing_fee_slope_at_kink_e9_per_slot: V16PodU64,
    pub backing_fee_slope_above_kink_e9_per_slot: V16PodU64,
    pub backing_freshness_buckets: u8,
    pub margin_mode_realizable_full_shared_cross_margin: u8,
    pub source_credit_lien_required: u8,
    pub insurance_credit_reservation_required: u8,
    pub permissionless_recovery_enabled: u8,
    pub recovery_fallback_price_enabled: u8,
    pub recovery_fallback_envelope_enabled: u8,
    pub credit_lien_revalidation_required: u8,
    pub stale_certificate_penalty_enabled: u8,
    pub full_refresh_required_for_favorable_actions: u8,
    pub public_liveness_profile_crank_forward: u8,
}

impl V16ConfigAccount {
    pub fn from_runtime(value: &V16Config) -> Self {
        Self {
            max_portfolio_assets: V16PodU16::new(value.max_portfolio_assets),
            max_market_slots: V16PodU32::new(value.max_market_slots),
            min_nonzero_mm_req: V16PodU128::new(value.min_nonzero_mm_req),
            min_nonzero_im_req: V16PodU128::new(value.min_nonzero_im_req),
            h_min: V16PodU64::new(value.h_min),
            h_max: V16PodU64::new(value.h_max),
            maintenance_margin_bps: V16PodU64::new(value.maintenance_margin_bps),
            initial_margin_bps: V16PodU64::new(value.initial_margin_bps),
            max_trading_fee_bps: V16PodU64::new(value.max_trading_fee_bps),
            liquidation_fee_bps: V16PodU64::new(value.liquidation_fee_bps),
            liquidation_fee_cap: V16PodU128::new(value.liquidation_fee_cap),
            min_liquidation_abs: V16PodU128::new(value.min_liquidation_abs),
            max_accrual_dt_slots: V16PodU64::new(value.max_accrual_dt_slots),
            max_abs_funding_e9_per_slot: V16PodU64::new(value.max_abs_funding_e9_per_slot),
            min_funding_lifetime_slots: V16PodU64::new(value.min_funding_lifetime_slots),
            max_price_move_bps_per_slot: V16PodU64::new(value.max_price_move_bps_per_slot),
            max_account_b_settlement_chunks: V16PodU64::new(value.max_account_b_settlement_chunks),
            max_bankrupt_close_chunks: V16PodU64::new(value.max_bankrupt_close_chunks),
            max_bankrupt_close_lifetime_slots: V16PodU64::new(
                value.max_bankrupt_close_lifetime_slots,
            ),
            asset_activation_cooldown_slots: V16PodU64::new(value.asset_activation_cooldown_slots),
            public_b_chunk_atoms: V16PodU128::new(value.public_b_chunk_atoms),
            max_recovery_fallback_deviation_bps: V16PodU64::new(
                value.max_recovery_fallback_deviation_bps,
            ),
            backing_fee_base_rate_e9_per_slot: V16PodU64::new(
                value.backing_fee_base_rate_e9_per_slot,
            ),
            backing_fee_kink_util_bps: V16PodU64::new(value.backing_fee_kink_util_bps),
            backing_fee_slope_at_kink_e9_per_slot: V16PodU64::new(
                value.backing_fee_slope_at_kink_e9_per_slot,
            ),
            backing_fee_slope_above_kink_e9_per_slot: V16PodU64::new(
                value.backing_fee_slope_above_kink_e9_per_slot,
            ),
            backing_freshness_buckets: value.backing_freshness_buckets,
            margin_mode_realizable_full_shared_cross_margin: encode_bool(
                value.margin_mode_realizable_full_shared_cross_margin,
            ),
            source_credit_lien_required: encode_bool(value.source_credit_lien_required),
            insurance_credit_reservation_required: encode_bool(
                value.insurance_credit_reservation_required,
            ),
            permissionless_recovery_enabled: encode_bool(value.permissionless_recovery_enabled),
            recovery_fallback_price_enabled: encode_bool(value.recovery_fallback_price_enabled),
            recovery_fallback_envelope_enabled: encode_bool(
                value.recovery_fallback_envelope_enabled,
            ),
            credit_lien_revalidation_required: encode_bool(value.credit_lien_revalidation_required),
            stale_certificate_penalty_enabled: encode_bool(value.stale_certificate_penalty_enabled),
            full_refresh_required_for_favorable_actions: encode_bool(
                value.full_refresh_required_for_favorable_actions,
            ),
            public_liveness_profile_crank_forward: encode_bool(
                value.public_liveness_profile_crank_forward,
            ),
        }
    }

    fn decode_runtime(&self) -> V16Result<V16Config> {
        let out = V16Config {
            max_portfolio_assets: self.max_portfolio_assets.get(),
            max_market_slots: self.max_market_slots.get(),
            min_nonzero_mm_req: self.min_nonzero_mm_req.get(),
            min_nonzero_im_req: self.min_nonzero_im_req.get(),
            h_min: self.h_min.get(),
            h_max: self.h_max.get(),
            maintenance_margin_bps: self.maintenance_margin_bps.get(),
            initial_margin_bps: self.initial_margin_bps.get(),
            max_trading_fee_bps: self.max_trading_fee_bps.get(),
            liquidation_fee_bps: self.liquidation_fee_bps.get(),
            liquidation_fee_cap: self.liquidation_fee_cap.get(),
            min_liquidation_abs: self.min_liquidation_abs.get(),
            max_accrual_dt_slots: self.max_accrual_dt_slots.get(),
            max_abs_funding_e9_per_slot: self.max_abs_funding_e9_per_slot.get(),
            min_funding_lifetime_slots: self.min_funding_lifetime_slots.get(),
            max_price_move_bps_per_slot: self.max_price_move_bps_per_slot.get(),
            max_account_b_settlement_chunks: self.max_account_b_settlement_chunks.get(),
            max_bankrupt_close_chunks: self.max_bankrupt_close_chunks.get(),
            max_bankrupt_close_lifetime_slots: self.max_bankrupt_close_lifetime_slots.get(),
            asset_activation_cooldown_slots: self.asset_activation_cooldown_slots.get(),
            public_b_chunk_atoms: self.public_b_chunk_atoms.get(),
            max_recovery_fallback_deviation_bps: self.max_recovery_fallback_deviation_bps.get(),
            backing_fee_base_rate_e9_per_slot: self.backing_fee_base_rate_e9_per_slot.get(),
            backing_fee_kink_util_bps: self.backing_fee_kink_util_bps.get(),
            backing_fee_slope_at_kink_e9_per_slot: self.backing_fee_slope_at_kink_e9_per_slot.get(),
            backing_fee_slope_above_kink_e9_per_slot: self
                .backing_fee_slope_above_kink_e9_per_slot
                .get(),
            backing_freshness_buckets: self.backing_freshness_buckets,
            margin_mode_realizable_full_shared_cross_margin: decode_bool(
                self.margin_mode_realizable_full_shared_cross_margin,
            )?,
            source_credit_lien_required: decode_bool(self.source_credit_lien_required)?,
            insurance_credit_reservation_required: decode_bool(
                self.insurance_credit_reservation_required,
            )?,
            permissionless_recovery_enabled: decode_bool(self.permissionless_recovery_enabled)?,
            recovery_fallback_price_enabled: decode_bool(self.recovery_fallback_price_enabled)?,
            recovery_fallback_envelope_enabled: decode_bool(
                self.recovery_fallback_envelope_enabled,
            )?,
            credit_lien_revalidation_required: decode_bool(self.credit_lien_revalidation_required)?,
            stale_certificate_penalty_enabled: decode_bool(self.stale_certificate_penalty_enabled)?,
            full_refresh_required_for_favorable_actions: decode_bool(
                self.full_refresh_required_for_favorable_actions,
            )?,
            public_liveness_profile_crank_forward: decode_bool(
                self.public_liveness_profile_crank_forward,
            )?,
        };
        Ok(out)
    }

    pub fn try_to_runtime_shape(&self) -> V16Result<V16Config> {
        let out = self.decode_runtime()?;
        out.validate_public_user_fund_shape()?;
        Ok(out)
    }

    pub fn try_to_runtime(&self) -> V16Result<V16Config> {
        let out = self.decode_runtime()?;
        out.validate_public_user_fund()?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct SourceCreditStateV16Account {
    pub positive_claim_bound_num: V16PodU128,
    pub exact_positive_claim_num: V16PodU128,
    pub fresh_reserved_backing_num: V16PodU128,
    pub spent_backing_num: V16PodU128,
    pub provider_receivable_num: V16PodU128,
    pub valid_liened_backing_num: V16PodU128,
    pub impaired_liened_backing_num: V16PodU128,
    pub insurance_credit_reserved_num: V16PodU128,
    pub valid_liened_insurance_num: V16PodU128,
    pub impaired_liened_insurance_num: V16PodU128,
    pub credit_rate_num: V16PodU128,
    pub credit_epoch: V16PodU64,
}

impl SourceCreditStateV16Account {
    pub fn from_runtime(value: &SourceCreditStateV16) -> Self {
        Self {
            positive_claim_bound_num: V16PodU128::new(value.positive_claim_bound_num),
            exact_positive_claim_num: V16PodU128::new(value.exact_positive_claim_num),
            fresh_reserved_backing_num: V16PodU128::new(value.fresh_reserved_backing_num),
            spent_backing_num: V16PodU128::new(value.spent_backing_num),
            provider_receivable_num: V16PodU128::new(value.provider_receivable_num),
            valid_liened_backing_num: V16PodU128::new(value.valid_liened_backing_num),
            impaired_liened_backing_num: V16PodU128::new(value.impaired_liened_backing_num),
            insurance_credit_reserved_num: V16PodU128::new(value.insurance_credit_reserved_num),
            valid_liened_insurance_num: V16PodU128::new(value.valid_liened_insurance_num),
            impaired_liened_insurance_num: V16PodU128::new(value.impaired_liened_insurance_num),
            credit_rate_num: V16PodU128::new(value.credit_rate_num),
            credit_epoch: V16PodU64::new(value.credit_epoch),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<SourceCreditStateV16> {
        let out = SourceCreditStateV16 {
            positive_claim_bound_num: self.positive_claim_bound_num.get(),
            exact_positive_claim_num: self.exact_positive_claim_num.get(),
            fresh_reserved_backing_num: self.fresh_reserved_backing_num.get(),
            spent_backing_num: self.spent_backing_num.get(),
            provider_receivable_num: self.provider_receivable_num.get(),
            valid_liened_backing_num: self.valid_liened_backing_num.get(),
            impaired_liened_backing_num: self.impaired_liened_backing_num.get(),
            insurance_credit_reserved_num: self.insurance_credit_reserved_num.get(),
            valid_liened_insurance_num: self.valid_liened_insurance_num.get(),
            impaired_liened_insurance_num: self.impaired_liened_insurance_num.get(),
            credit_rate_num: self.credit_rate_num.get(),
            credit_epoch: self.credit_epoch.get(),
        };
        V16Core::validate_source_credit_state_static(out)?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct BackingBucketV16Account {
    pub market_id: V16PodU64,
    pub fresh_unliened_backing_num: V16PodU128,
    pub valid_liened_backing_num: V16PodU128,
    pub consumed_liened_backing_num: V16PodU128,
    pub impaired_liened_backing_num: V16PodU128,
    pub utilization_fee_earnings: V16PodU128,
    pub expiry_slot: V16PodU64,
    pub status: u8,
}

impl BackingBucketV16Account {
    pub fn from_runtime(value: &BackingBucketV16) -> Self {
        Self {
            market_id: V16PodU64::new(value.market_id),
            fresh_unliened_backing_num: V16PodU128::new(value.fresh_unliened_backing_num),
            valid_liened_backing_num: V16PodU128::new(value.valid_liened_backing_num),
            consumed_liened_backing_num: V16PodU128::new(value.consumed_liened_backing_num),
            impaired_liened_backing_num: V16PodU128::new(value.impaired_liened_backing_num),
            utilization_fee_earnings: V16PodU128::new(value.utilization_fee_earnings),
            expiry_slot: V16PodU64::new(value.expiry_slot),
            status: encode_backing_bucket_status(value.status),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<BackingBucketV16> {
        let out = BackingBucketV16 {
            market_id: self.market_id.get(),
            fresh_unliened_backing_num: self.fresh_unliened_backing_num.get(),
            valid_liened_backing_num: self.valid_liened_backing_num.get(),
            consumed_liened_backing_num: self.consumed_liened_backing_num.get(),
            impaired_liened_backing_num: self.impaired_liened_backing_num.get(),
            utilization_fee_earnings: self.utilization_fee_earnings.get(),
            expiry_slot: self.expiry_slot.get(),
            status: decode_backing_bucket_status(self.status)?,
        };
        V16Core::validate_backing_bucket_static(out)?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct InsuranceCreditReservationV16Account {
    pub insurance_credit_reserved_num: V16PodU128,
    pub valid_liened_insurance_num: V16PodU128,
    pub impaired_liened_insurance_num: V16PodU128,
    pub consumed_insurance_num: V16PodU128,
    pub source_credit_epoch: V16PodU64,
}

impl InsuranceCreditReservationV16Account {
    pub fn from_runtime(value: &InsuranceCreditReservationV16) -> Self {
        Self {
            insurance_credit_reserved_num: V16PodU128::new(value.insurance_credit_reserved_num),
            valid_liened_insurance_num: V16PodU128::new(value.valid_liened_insurance_num),
            impaired_liened_insurance_num: V16PodU128::new(value.impaired_liened_insurance_num),
            consumed_insurance_num: V16PodU128::new(value.consumed_insurance_num),
            source_credit_epoch: V16PodU64::new(value.source_credit_epoch),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<InsuranceCreditReservationV16> {
        let out = InsuranceCreditReservationV16 {
            insurance_credit_reserved_num: self.insurance_credit_reserved_num.get(),
            valid_liened_insurance_num: self.valid_liened_insurance_num.get(),
            impaired_liened_insurance_num: self.impaired_liened_insurance_num.get(),
            consumed_insurance_num: self.consumed_insurance_num.get(),
            source_credit_epoch: self.source_credit_epoch.get(),
        };
        V16Core::validate_insurance_reservation_static(out)?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct AssetStateV16Account {
    pub market_id: V16PodU64,
    pub retired_slot: V16PodU64,
    pub lifecycle: u8,
    pub raw_oracle_target_price: V16PodU64,
    pub effective_price: V16PodU64,
    pub fund_px_last: V16PodU64,
    pub slot_last: V16PodU64,
    pub a_long: V16PodU128,
    pub a_short: V16PodU128,
    pub k_long: V16PodI128,
    pub k_short: V16PodI128,
    pub f_long_num: V16PodI128,
    pub f_short_num: V16PodI128,
    pub kf_epoch_long: V16PodU64,
    pub kf_epoch_short: V16PodU64,
    pub k_epoch_start_long: V16PodI128,
    pub k_epoch_start_short: V16PodI128,
    pub f_epoch_start_long_num: V16PodI128,
    pub f_epoch_start_short_num: V16PodI128,
    pub b_long_num: V16PodU128,
    pub b_short_num: V16PodU128,
    pub b_epoch_start_long_num: V16PodU128,
    pub b_epoch_start_short_num: V16PodU128,
    pub oi_eff_long_q: V16PodU128,
    pub oi_eff_short_q: V16PodU128,
    pub stored_pos_count_long: V16PodU64,
    pub stored_pos_count_short: V16PodU64,
    pub stale_account_count_long: V16PodU64,
    pub stale_account_count_short: V16PodU64,
    pub pending_obligation_count_long: V16PodU64,
    pub pending_obligation_count_short: V16PodU64,
    pub loss_weight_sum_long: V16PodU128,
    pub loss_weight_sum_short: V16PodU128,
    pub social_loss_remainder_long_num: V16PodU128,
    pub social_loss_remainder_short_num: V16PodU128,
    pub social_loss_dust_long_num: V16PodU128,
    pub social_loss_dust_short_num: V16PodU128,
    pub explicit_unallocated_loss_long: V16PodU128,
    pub explicit_unallocated_loss_short: V16PodU128,
    pub epoch_long: V16PodU64,
    pub epoch_short: V16PodU64,
    pub mode_long: u8,
    pub mode_short: u8,
}

impl AssetStateV16Account {
    pub fn from_runtime(value: &AssetStateV16) -> Self {
        Self {
            market_id: V16PodU64::new(value.market_id),
            retired_slot: V16PodU64::new(value.retired_slot),
            lifecycle: encode_asset_lifecycle(value.lifecycle),
            raw_oracle_target_price: V16PodU64::new(value.raw_oracle_target_price),
            effective_price: V16PodU64::new(value.effective_price),
            fund_px_last: V16PodU64::new(value.fund_px_last),
            slot_last: V16PodU64::new(value.slot_last),
            a_long: V16PodU128::new(value.a_long),
            a_short: V16PodU128::new(value.a_short),
            k_long: V16PodI128::new(value.k_long),
            k_short: V16PodI128::new(value.k_short),
            f_long_num: V16PodI128::new(value.f_long_num),
            f_short_num: V16PodI128::new(value.f_short_num),
            kf_epoch_long: V16PodU64::new(value.kf_epoch_long),
            kf_epoch_short: V16PodU64::new(value.kf_epoch_short),
            k_epoch_start_long: V16PodI128::new(value.k_epoch_start_long),
            k_epoch_start_short: V16PodI128::new(value.k_epoch_start_short),
            f_epoch_start_long_num: V16PodI128::new(value.f_epoch_start_long_num),
            f_epoch_start_short_num: V16PodI128::new(value.f_epoch_start_short_num),
            b_long_num: V16PodU128::new(value.b_long_num),
            b_short_num: V16PodU128::new(value.b_short_num),
            b_epoch_start_long_num: V16PodU128::new(value.b_epoch_start_long_num),
            b_epoch_start_short_num: V16PodU128::new(value.b_epoch_start_short_num),
            oi_eff_long_q: V16PodU128::new(value.oi_eff_long_q),
            oi_eff_short_q: V16PodU128::new(value.oi_eff_short_q),
            stored_pos_count_long: V16PodU64::new(value.stored_pos_count_long),
            stored_pos_count_short: V16PodU64::new(value.stored_pos_count_short),
            stale_account_count_long: V16PodU64::new(value.stale_account_count_long),
            stale_account_count_short: V16PodU64::new(value.stale_account_count_short),
            pending_obligation_count_long: V16PodU64::new(value.pending_obligation_count_long),
            pending_obligation_count_short: V16PodU64::new(value.pending_obligation_count_short),
            loss_weight_sum_long: V16PodU128::new(value.loss_weight_sum_long),
            loss_weight_sum_short: V16PodU128::new(value.loss_weight_sum_short),
            social_loss_remainder_long_num: V16PodU128::new(value.social_loss_remainder_long_num),
            social_loss_remainder_short_num: V16PodU128::new(value.social_loss_remainder_short_num),
            social_loss_dust_long_num: V16PodU128::new(value.social_loss_dust_long_num),
            social_loss_dust_short_num: V16PodU128::new(value.social_loss_dust_short_num),
            explicit_unallocated_loss_long: V16PodU128::new(value.explicit_unallocated_loss_long),
            explicit_unallocated_loss_short: V16PodU128::new(value.explicit_unallocated_loss_short),
            epoch_long: V16PodU64::new(value.epoch_long),
            epoch_short: V16PodU64::new(value.epoch_short),
            mode_long: encode_side_mode(value.mode_long),
            mode_short: encode_side_mode(value.mode_short),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<AssetStateV16> {
        let out = AssetStateV16 {
            market_id: self.market_id.get(),
            retired_slot: self.retired_slot.get(),
            lifecycle: decode_asset_lifecycle(self.lifecycle)?,
            raw_oracle_target_price: self.raw_oracle_target_price.get(),
            effective_price: self.effective_price.get(),
            fund_px_last: self.fund_px_last.get(),
            slot_last: self.slot_last.get(),
            a_long: self.a_long.get(),
            a_short: self.a_short.get(),
            k_long: self.k_long.get(),
            k_short: self.k_short.get(),
            f_long_num: self.f_long_num.get(),
            f_short_num: self.f_short_num.get(),
            kf_epoch_long: self.kf_epoch_long.get(),
            kf_epoch_short: self.kf_epoch_short.get(),
            k_epoch_start_long: self.k_epoch_start_long.get(),
            k_epoch_start_short: self.k_epoch_start_short.get(),
            f_epoch_start_long_num: self.f_epoch_start_long_num.get(),
            f_epoch_start_short_num: self.f_epoch_start_short_num.get(),
            b_long_num: self.b_long_num.get(),
            b_short_num: self.b_short_num.get(),
            b_epoch_start_long_num: self.b_epoch_start_long_num.get(),
            b_epoch_start_short_num: self.b_epoch_start_short_num.get(),
            oi_eff_long_q: self.oi_eff_long_q.get(),
            oi_eff_short_q: self.oi_eff_short_q.get(),
            stored_pos_count_long: self.stored_pos_count_long.get(),
            stored_pos_count_short: self.stored_pos_count_short.get(),
            stale_account_count_long: self.stale_account_count_long.get(),
            stale_account_count_short: self.stale_account_count_short.get(),
            pending_obligation_count_long: self.pending_obligation_count_long.get(),
            pending_obligation_count_short: self.pending_obligation_count_short.get(),
            loss_weight_sum_long: self.loss_weight_sum_long.get(),
            loss_weight_sum_short: self.loss_weight_sum_short.get(),
            social_loss_remainder_long_num: self.social_loss_remainder_long_num.get(),
            social_loss_remainder_short_num: self.social_loss_remainder_short_num.get(),
            social_loss_dust_long_num: self.social_loss_dust_long_num.get(),
            social_loss_dust_short_num: self.social_loss_dust_short_num.get(),
            explicit_unallocated_loss_long: self.explicit_unallocated_loss_long.get(),
            explicit_unallocated_loss_short: self.explicit_unallocated_loss_short.get(),
            epoch_long: self.epoch_long.get(),
            epoch_short: self.epoch_short.get(),
            mode_long: decode_side_mode(self.mode_long)?,
            mode_short: decode_side_mode(self.mode_short)?,
        };
        validate_non_min_i128(out.k_long)?;
        validate_non_min_i128(out.k_short)?;
        validate_non_min_i128(out.f_long_num)?;
        validate_non_min_i128(out.f_short_num)?;
        validate_non_min_i128(out.k_epoch_start_long)?;
        validate_non_min_i128(out.k_epoch_start_short)?;
        validate_non_min_i128(out.f_epoch_start_long_num)?;
        validate_non_min_i128(out.f_epoch_start_short_num)?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct EngineAssetSlotV16Account {
    pub asset: AssetStateV16Account,
    pub insurance_domain_budget_long: V16PodU128,
    pub insurance_domain_budget_short: V16PodU128,
    pub insurance_domain_spent_long: V16PodU128,
    pub insurance_domain_spent_short: V16PodU128,
    pub pending_domain_loss_barrier_long: V16PodU64,
    pub pending_domain_loss_barrier_short: V16PodU64,
    pub source_credit_long: SourceCreditStateV16Account,
    pub source_credit_short: SourceCreditStateV16Account,
    pub backing_long: BackingBucketV16Account,
    pub backing_short: BackingBucketV16Account,
    pub insurance_reservation_long: InsuranceCreditReservationV16Account,
    pub insurance_reservation_short: InsuranceCreditReservationV16Account,
}

fn asset_contributes_to_loss_stale_summary(asset: AssetStateV16) -> bool {
    matches!(
        asset.lifecycle,
        AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly
    ) && (asset.oi_eff_long_q != 0
        || asset.oi_eff_short_q != 0
        || asset.stored_pos_count_long != 0
        || asset.stored_pos_count_short != 0
        || asset.stale_account_count_long != 0
        || asset.stale_account_count_short != 0
        || asset.pending_obligation_count_long != 0
        || asset.pending_obligation_count_short != 0
        || asset.loss_weight_sum_long != 0
        || asset.loss_weight_sum_short != 0)
}

fn asset_is_loss_stale_at_slot(asset: AssetStateV16, current_slot: u64) -> bool {
    asset.stale_account_count_long != 0
        || asset.stale_account_count_short != 0
        || (asset_contributes_to_loss_stale_summary(asset) && asset.slot_last < current_slot)
}

fn slot_resolved_payout_blockers_v16(slot: &EngineAssetSlotV16Account) -> V16Result<u64> {
    let asset = slot.asset.try_to_runtime()?;
    asset
        .stored_pos_count_long
        .checked_add(asset.stored_pos_count_short)
        .and_then(|v| v.checked_add(asset.stale_account_count_long))
        .and_then(|v| v.checked_add(asset.stale_account_count_short))
        .and_then(|v| v.checked_add(slot.pending_domain_loss_barrier_long.get()))
        .and_then(|v| v.checked_add(slot.pending_domain_loss_barrier_short.get()))
        .ok_or(V16Error::CounterOverflow)
}

pub trait MarketSlotV16View {
    fn engine_slot(&self) -> &EngineAssetSlotV16Account;
}

pub trait MarketSlotV16ViewMut: MarketSlotV16View {
    fn engine_slot_mut(&mut self) -> &mut EngineAssetSlotV16Account;
}

impl MarketSlotV16View for EngineAssetSlotV16Account {
    fn engine_slot(&self) -> &EngineAssetSlotV16Account {
        self
    }
}

impl MarketSlotV16ViewMut for EngineAssetSlotV16Account {
    fn engine_slot_mut(&mut self) -> &mut EngineAssetSlotV16Account {
        self
    }
}

impl EngineAssetSlotV16Account {
    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn is_zero_fill_or_canonical_disabled_slot(&self) -> V16Result<bool> {
        if !Self::asset_account_is_empty_for_activation(self.asset) {
            return Ok(false);
        }
        Ok((self.insurance_domain_budget_long.get() == 0
            || self.insurance_domain_budget_long.get() == MAX_VAULT_TVL)
            && (self.insurance_domain_budget_short.get() == 0
                || self.insurance_domain_budget_short.get() == MAX_VAULT_TVL)
            && self.insurance_domain_spent_long.get() == 0
            && self.insurance_domain_spent_short.get() == 0
            && self.pending_domain_loss_barrier_long.get() == 0
            && self.pending_domain_loss_barrier_short.get() == 0
            && Self::source_credit_account_is_empty_for_activation(self.source_credit_long)
            && Self::source_credit_account_is_empty_for_activation(self.source_credit_short)
            && Self::backing_bucket_account_is_empty_for_activation(self.backing_long)
            && Self::backing_bucket_account_is_empty_for_activation(self.backing_short)
            && Self::insurance_reservation_account_is_empty_for_activation(
                self.insurance_reservation_long,
            )
            && Self::insurance_reservation_account_is_empty_for_activation(
                self.insurance_reservation_short,
            ))
    }

    fn validate_market_id_binding(&self) -> V16Result<()> {
        let asset = self.asset.try_to_runtime()?;
        let long_bucket = self.backing_long.try_to_runtime()?;
        let short_bucket = self.backing_short.try_to_runtime()?;
        if long_bucket.market_id != asset.market_id || short_bucket.market_id != asset.market_id {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    pub fn empty_for_market(market_id: u64) -> Self {
        let backing = BackingBucketV16::empty_for_market(market_id);
        Self {
            asset: AssetStateV16Account::default(),
            insurance_domain_budget_long: V16PodU128::default(),
            insurance_domain_budget_short: V16PodU128::default(),
            insurance_domain_spent_long: V16PodU128::default(),
            insurance_domain_spent_short: V16PodU128::default(),
            pending_domain_loss_barrier_long: V16PodU64::default(),
            pending_domain_loss_barrier_short: V16PodU64::default(),
            source_credit_long: SourceCreditStateV16Account::from_runtime(
                &SourceCreditStateV16::EMPTY,
            ),
            source_credit_short: SourceCreditStateV16Account::from_runtime(
                &SourceCreditStateV16::EMPTY,
            ),
            backing_long: BackingBucketV16Account::from_runtime(&backing),
            backing_short: BackingBucketV16Account::from_runtime(&backing),
            insurance_reservation_long: InsuranceCreditReservationV16Account::from_runtime(
                &InsuranceCreditReservationV16::EMPTY,
            ),
            insurance_reservation_short: InsuranceCreditReservationV16Account::from_runtime(
                &InsuranceCreditReservationV16::EMPTY,
            ),
        }
    }

    fn source_credit_account_is_empty_for_activation(state: SourceCreditStateV16Account) -> bool {
        let all_non_rate_fields_empty = state.positive_claim_bound_num.get() == 0
            && state.exact_positive_claim_num.get() == 0
            && state.fresh_reserved_backing_num.get() == 0
            && state.spent_backing_num.get() == 0
            && state.provider_receivable_num.get() == 0
            && state.valid_liened_backing_num.get() == 0
            && state.impaired_liened_backing_num.get() == 0
            && state.insurance_credit_reserved_num.get() == 0
            && state.valid_liened_insurance_num.get() == 0
            && state.impaired_liened_insurance_num.get() == 0;
        all_non_rate_fields_empty
            && (state.credit_rate_num.get() == 0
                || state.credit_rate_num.get() == CREDIT_RATE_SCALE)
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn backing_bucket_account_is_empty_for_activation(state: BackingBucketV16Account) -> bool {
        state.market_id.get() == 0
            && state.fresh_unliened_backing_num.get() == 0
            && state.valid_liened_backing_num.get() == 0
            && state.consumed_liened_backing_num.get() == 0
            && state.impaired_liened_backing_num.get() == 0
            && state.expiry_slot.get() == 0
            && state.status == 0
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn insurance_reservation_account_is_empty_for_activation(
        state: InsuranceCreditReservationV16Account,
    ) -> bool {
        state.insurance_credit_reserved_num.get() == 0
            && state.valid_liened_insurance_num.get() == 0
            && state.impaired_liened_insurance_num.get() == 0
            && state.consumed_insurance_num.get() == 0
            && state.source_credit_epoch.get() == 0
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn asset_account_is_empty_for_activation(asset: AssetStateV16Account) -> bool {
        let a_shape = (asset.a_long.get() == 0 && asset.a_short.get() == 0)
            || (asset.a_long.get() == ADL_ONE && asset.a_short.get() == ADL_ONE);
        asset.lifecycle == 0
            && asset.market_id.get() == 0
            && a_shape
            && asset.k_long.get() == 0
            && asset.k_short.get() == 0
            && asset.f_long_num.get() == 0
            && asset.f_short_num.get() == 0
            && asset.kf_epoch_long.get() == 0
            && asset.kf_epoch_short.get() == 0
            && asset.k_epoch_start_long.get() == 0
            && asset.k_epoch_start_short.get() == 0
            && asset.f_epoch_start_long_num.get() == 0
            && asset.f_epoch_start_short_num.get() == 0
            && asset.b_long_num.get() == 0
            && asset.b_short_num.get() == 0
            && asset.b_epoch_start_long_num.get() == 0
            && asset.b_epoch_start_short_num.get() == 0
            && asset.oi_eff_long_q.get() == 0
            && asset.oi_eff_short_q.get() == 0
            && asset.stored_pos_count_long.get() == 0
            && asset.stored_pos_count_short.get() == 0
            && asset.stale_account_count_long.get() == 0
            && asset.stale_account_count_short.get() == 0
            && asset.pending_obligation_count_long.get() == 0
            && asset.pending_obligation_count_short.get() == 0
            && asset.loss_weight_sum_long.get() == 0
            && asset.loss_weight_sum_short.get() == 0
            && asset.social_loss_remainder_long_num.get() == 0
            && asset.social_loss_remainder_short_num.get() == 0
            && asset.social_loss_dust_long_num.get() == 0
            && asset.social_loss_dust_short_num.get() == 0
            && asset.explicit_unallocated_loss_long.get() == 0
            && asset.explicit_unallocated_loss_short.get() == 0
            && asset.retired_slot.get() == 0
            && asset.raw_oracle_target_price.get() == 0
            && asset.effective_price.get() == 0
            && asset.fund_px_last.get() == 0
            && asset.slot_last.get() == 0
            && asset.epoch_long.get() == 0
            && asset.epoch_short.get() == 0
            && asset.mode_long == 0
            && asset.mode_short == 0
    }

    fn asset_state_is_empty_for_activation(asset: AssetStateV16) -> bool {
        let a_shape = (asset.a_long == 0 && asset.a_short == 0)
            || (asset.a_long == ADL_ONE && asset.a_short == ADL_ONE);
        a_shape
            && asset.k_long == 0
            && asset.k_short == 0
            && asset.f_long_num == 0
            && asset.f_short_num == 0
            && asset.kf_epoch_long == 0
            && asset.kf_epoch_short == 0
            && asset.k_epoch_start_long == 0
            && asset.k_epoch_start_short == 0
            && asset.f_epoch_start_long_num == 0
            && asset.f_epoch_start_short_num == 0
            && asset.b_long_num == 0
            && asset.b_short_num == 0
            && asset.b_epoch_start_long_num == 0
            && asset.b_epoch_start_short_num == 0
            && asset.oi_eff_long_q == 0
            && asset.oi_eff_short_q == 0
            && asset.stored_pos_count_long == 0
            && asset.stored_pos_count_short == 0
            && asset.stale_account_count_long == 0
            && asset.stale_account_count_short == 0
            && asset.pending_obligation_count_long == 0
            && asset.pending_obligation_count_short == 0
            && asset.loss_weight_sum_long == 0
            && asset.loss_weight_sum_short == 0
            && asset.social_loss_remainder_long_num == 0
            && asset.social_loss_remainder_short_num == 0
            && asset.social_loss_dust_long_num == 0
            && asset.social_loss_dust_short_num == 0
            && asset.explicit_unallocated_loss_long == 0
            && asset.explicit_unallocated_loss_short == 0
            && asset.mode_long == SideModeV16::Normal
            && asset.mode_short == SideModeV16::Normal
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct MarketGroupV16HeaderAccount {
    pub market_group_id: [u8; 32],
    pub config: V16ConfigAccount,
    pub asset_slot_capacity: V16PodU32,
    pub vault: V16PodU128,
    pub insurance: V16PodU128,
    pub c_tot: V16PodU128,
    pub pnl_pos_tot: V16PodU128,
    pub pnl_pos_bound_tot_num: V16PodU128,
    pub pnl_pos_bound_tot: V16PodU128,
    pub pnl_matured_pos_tot: V16PodU128,
    pub backing_provider_earnings_total: V16PodU128,
    pub source_claim_bound_total_num: V16PodU128,
    pub source_fresh_backing_total_num: V16PodU128,
    pub source_insurance_credit_reserved_total_atoms: V16PodU128,
    pub insurance_domain_budget_remaining_total: V16PodU128,
    pub resolved_payout_blocker_count: V16PodU64,
    // fork feature A-6 stress envelope: POD accumulator + slot/epoch sentinels, appended AFTER the 5
    // O(1) aggregates (collision-matrix row 10) to keep the aggregate block contiguous. Makes toly's
    // dormant `threshold_stress_active` flag live. EXCLUDED from the rescan-equality set (scalar header
    // state, not slot-recomputable). +48B shifts dynamic asset-slot offsets (fresh-start cutover ABI).
    pub stress_consumption_bps_e9_since_envelope: V16PodU128,
    pub stress_envelope_start_slot: V16PodU64,
    pub stress_envelope_start_credit_epoch: V16PodU64,
    pub materialized_portfolio_count: V16PodU64,
    pub stale_certificate_count: V16PodU64,
    pub b_stale_account_count: V16PodU64,
    pub negative_pnl_account_count: V16PodU64,
    pub risk_epoch: V16PodU64,
    pub asset_set_epoch: V16PodU64,
    pub asset_activation_count: V16PodU64,
    pub last_asset_activation_slot: V16PodU64,
    pub next_market_id: V16PodU64,
    pub oracle_epoch: V16PodU64,
    pub funding_epoch: V16PodU64,
    pub slot_last: V16PodU64,
    pub current_slot: V16PodU64,
    pub bankruptcy_hlock_active: u8,
    pub threshold_stress_active: u8,
    pub loss_stale_active: u8,
    pub recovery_reason: V16OptionalRecoveryReasonAccount,
    pub mode: u8,
    pub resolved_slot: V16PodU64,
    pub payout_snapshot: V16PodU128,
    pub payout_snapshot_pnl_pos_tot: V16PodU128,
    pub payout_snapshot_captured: u8,
    pub resolved_payout_ledger: ResolvedPayoutLedgerV16Account,
}

impl Default for MarketGroupV16HeaderAccount {
    fn default() -> Self {
        bytemuck::Zeroable::zeroed()
    }
}

/// fork feature A-9 (dynamic-trade-fee): engine-level fee-policy update payload. The wrapper-side
/// admin auth / signer / replay-nonce checks land in Phase 3; the engine surface stays admin-agnostic.
/// v16 already validates per-call `fee_bps` against `config.max_trading_fee_bps` in trade validation;
/// this payload carries the four fee-policy fields an authorized admin may rewrite atomically on a live
/// market group. Field order/types (u64,u64,u128,u128) are the engine read-side of the Phase-3 wire.
#[cfg(feature = "fork-facade")]
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FeePolicyUpdateV16 {
    pub max_trading_fee_bps: u64,
    pub liquidation_fee_bps: u64,
    pub liquidation_fee_cap: u128,
    pub min_liquidation_abs: u128,
}

impl MarketGroupV16HeaderAccount {
    fn dynamic_asset_slot_stride<T: MarketWrapperPod>() -> usize {
        core::mem::size_of::<Market<T>>()
    }

    #[cfg(kani)]
    pub fn kani_dynamic_asset_slot_stride<T: MarketWrapperPod>() -> usize {
        Self::dynamic_asset_slot_stride::<T>()
    }

    pub fn dynamic_market_group_account_len<T: MarketWrapperPod>(
        asset_slot_capacity: usize,
    ) -> V16Result<usize> {
        let slot_len = Self::dynamic_asset_slot_stride::<T>();
        core::mem::size_of::<Self>()
            .checked_add(
                asset_slot_capacity
                    .checked_mul(slot_len)
                    .ok_or(V16Error::ArithmeticOverflow)?,
            )
            .ok_or(V16Error::ArithmeticOverflow)
    }

    pub fn dynamic_asset_slot_offset<T: MarketWrapperPod>(asset_index: usize) -> V16Result<usize> {
        let slot_len = Self::dynamic_asset_slot_stride::<T>();
        core::mem::size_of::<Self>()
            .checked_add(
                asset_index
                    .checked_mul(slot_len)
                    .ok_or(V16Error::ArithmeticOverflow)?,
            )
            .ok_or(V16Error::ArithmeticOverflow)
    }

    pub fn dynamic_asset_slot_capacity_from_account_len<T: MarketWrapperPod>(
        account_len: usize,
    ) -> V16Result<usize> {
        let header_len = core::mem::size_of::<Self>();
        if account_len < header_len {
            return Err(V16Error::InvalidConfig);
        }
        let slot_len = Self::dynamic_asset_slot_stride::<T>();
        let trailing_len = account_len - header_len;
        if slot_len == 0 || trailing_len % slot_len != 0 {
            return Err(V16Error::InvalidConfig);
        }
        Ok(trailing_len / slot_len)
    }

    pub fn validate_dynamic_market_group_account_len<T: MarketWrapperPod>(
        account_len: usize,
        asset_slot_capacity: usize,
    ) -> V16Result<()> {
        let expected_len = Self::dynamic_market_group_account_len::<T>(asset_slot_capacity)?;
        if account_len != expected_len {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    pub fn new_dynamic(
        market_group_id: [u8; 32],
        config: V16Config,
        asset_slot_capacity: u32,
        init_slot: u64,
    ) -> V16Result<Self> {
        if asset_slot_capacity < config.max_market_slots {
            return Err(V16Error::InvalidConfig);
        }
        config.validate_public_user_fund()?;
        Ok(Self {
            market_group_id,
            config: V16ConfigAccount::from_runtime(&config),
            asset_slot_capacity: V16PodU32::new(asset_slot_capacity),
            vault: V16PodU128::default(),
            insurance: V16PodU128::default(),
            c_tot: V16PodU128::default(),
            pnl_pos_tot: V16PodU128::default(),
            pnl_pos_bound_tot_num: V16PodU128::default(),
            pnl_pos_bound_tot: V16PodU128::default(),
            pnl_matured_pos_tot: V16PodU128::default(),
            backing_provider_earnings_total: V16PodU128::default(),
            source_claim_bound_total_num: V16PodU128::default(),
            source_fresh_backing_total_num: V16PodU128::default(),
            source_insurance_credit_reserved_total_atoms: V16PodU128::default(),
            insurance_domain_budget_remaining_total: V16PodU128::default(),
            resolved_payout_blocker_count: V16PodU64::default(),
            // A-6: envelope idle by default — accumulator zero, slot/epoch sentinels u64::MAX so the
            // writer's not-same-slot / epoch-advance guards read "no envelope open". Sentinels (NOT 0)
            // are required so the validate_shape pairing invariant holds for a fresh account.
            stress_consumption_bps_e9_since_envelope: V16PodU128::default(),
            stress_envelope_start_slot: V16PodU64::new(u64::MAX),
            stress_envelope_start_credit_epoch: V16PodU64::new(u64::MAX),
            materialized_portfolio_count: V16PodU64::default(),
            stale_certificate_count: V16PodU64::default(),
            b_stale_account_count: V16PodU64::default(),
            negative_pnl_account_count: V16PodU64::default(),
            risk_epoch: V16PodU64::default(),
            asset_set_epoch: V16PodU64::default(),
            asset_activation_count: V16PodU64::default(),
            last_asset_activation_slot: V16PodU64::default(),
            next_market_id: V16PodU64::new(1),
            oracle_epoch: V16PodU64::default(),
            funding_epoch: V16PodU64::default(),
            slot_last: V16PodU64::new(init_slot),
            current_slot: V16PodU64::new(init_slot),
            bankruptcy_hlock_active: 0,
            threshold_stress_active: 0,
            loss_stale_active: 0,
            recovery_reason: V16OptionalRecoveryReasonAccount::default(),
            mode: encode_market_mode(MarketModeV16::Live),
            resolved_slot: V16PodU64::default(),
            payout_snapshot: V16PodU128::default(),
            payout_snapshot_pnl_pos_tot: V16PodU128::default(),
            payout_snapshot_captured: 0,
            resolved_payout_ledger: ResolvedPayoutLedgerV16Account::from_runtime(
                &ResolvedPayoutLedgerV16::EMPTY,
            ),
        })
    }

    pub fn grow_asset_slot_capacity_not_atomic(
        &mut self,
        new_asset_slot_capacity: u32,
        new_max_market_slots: u32,
    ) -> V16Result<()> {
        let mut config = self.config.try_to_runtime_shape()?;
        let old_capacity = self.asset_slot_capacity.get();
        if decode_market_mode(self.mode)? != MarketModeV16::Live
            || new_asset_slot_capacity < old_capacity
            || new_max_market_slots < config.max_market_slots
            || new_max_market_slots > new_asset_slot_capacity
        {
            return Err(V16Error::InvalidConfig);
        }
        config.max_market_slots = new_max_market_slots;
        config.validate_public_user_fund_shape()?;
        let next_asset_set_epoch = self
            .asset_set_epoch
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        let next_risk_epoch = self
            .risk_epoch
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        self.asset_slot_capacity = V16PodU32::new(new_asset_slot_capacity);
        self.config = V16ConfigAccount::from_runtime(&config);
        self.asset_set_epoch = V16PodU64::new(next_asset_set_epoch);
        self.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    /// fork feature A-9 (zero-copy header form): atomically rewrite the four fee-policy config fields
    /// on a LIVE market group via decode→mutate-candidate→revalidate→re-encode (same template as
    /// grow_asset_slot_capacity_not_atomic above). Validation runs against a candidate V16Config BEFORE
    /// the on-account config is touched, so a rejected update leaves engine state byte-unchanged.
    /// Admin-agnostic; the wrapper verb (Phase 3) owns signer + replay nonce. Does NOT call any
    /// assert_public_invariants (the runtime-form mirror that did is dropped with runtime-vec; the
    /// candidate validate_public_user_fund is the sole guarantee, identical to grow_* and the fork).
    #[cfg(feature = "fork-facade")]
    pub fn apply_fee_policy_update_not_atomic(
        &mut self,
        update: FeePolicyUpdateV16,
    ) -> V16Result<()> {
        if decode_market_mode(self.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let mut candidate = self.config.try_to_runtime_shape()?;
        candidate.max_trading_fee_bps = update.max_trading_fee_bps;
        candidate.liquidation_fee_bps = update.liquidation_fee_bps;
        candidate.liquidation_fee_cap = update.liquidation_fee_cap;
        candidate.min_liquidation_abs = update.min_liquidation_abs;
        candidate.validate_public_user_fund()?;
        self.config = V16ConfigAccount::from_runtime(&candidate);
        Ok(())
    }

    /// fork-facade (A-9): kani-only shape-only shim — proves fee-field bounds + persistence without
    /// the solvency envelope's encode/decode byte-array symbolic explosion (which OOMs even solo on
    /// 64GB: 7.7 GB RSS after 4min and growing — empirically confirmed 2026-06-09). The
    /// `max_trading_fee_bps > MAX_MARGIN_BPS` bound is checked by `validate_public_user_fund_shape`
    /// at the same line as the full validator (v16.rs:1950). Solvency envelope correctness is
    /// separately covered by:
    ///   (a) the frozen `proofs_v16.rs` solvency-envelope harnesses (byte-identical toly content), AND
    ///   (b) the isolated `proof_v17_a9_validate_public_user_fund_direct` harness which calls the REAL
    ///       `validate_public_user_fund` directly on a V16Config struct with symbolic fee fields, without
    ///       the POD encode/decode step that causes CBMC to track symbolic bytes through all config fields.
    /// The three A-9 harnesses (bounds, persists, no-other-mutation) do NOT exercise the solvency envelope
    /// for their properties; they are sound over the shape-check boundary.
    #[cfg(all(kani, feature = "fork-facade"))]
    pub fn kani_apply_fee_policy_update_not_atomic(
        &mut self,
        update: FeePolicyUpdateV16,
    ) -> V16Result<()> {
        // Shape-only validation path: decode → mutate → validate shape (no solvency envelope).
        // This is operationally equivalent for the A-9 invariants (fee bounds + field isolation):
        //   - fee-bounds rejection: validated by validate_public_user_fund_shape line 1950
        //   - field persistence: config encode/decode roundtrip is the same path
        //   - non-mutation: same struct mutation, same from_runtime encode
        if decode_market_mode(self.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let mut candidate = self.config.try_to_runtime_shape()?;
        candidate.max_trading_fee_bps = update.max_trading_fee_bps;
        candidate.liquidation_fee_bps = update.liquidation_fee_bps;
        candidate.liquidation_fee_cap = update.liquidation_fee_cap;
        candidate.min_liquidation_abs = update.min_liquidation_abs;
        candidate.validate_public_user_fund_shape()?;
        self.config = V16ConfigAccount::from_runtime(&candidate);
        Ok(())
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn validate_dynamic_market_slots_shape<S: MarketSlotV16View>(
        &self,
        slots: &[S],
    ) -> V16Result<()> {
        let configured_market_slots = self.config.max_market_slots.get() as usize;
        let capacity = self.asset_slot_capacity.get() as usize;
        Self::validate_dynamic_market_slots_len_static(
            slots.len(),
            capacity,
            configured_market_slots,
        )?;
        if capacity == configured_market_slots {
            return Ok(());
        }
        let mut slot_index = configured_market_slots;
        while slot_index < capacity {
            self.validate_dynamic_market_slot_shape_at(slot_index, &slots[slot_index])?;
            slot_index += 1;
        }
        Ok(())
    }

    fn validate_dynamic_market_slots_len_static(
        supplied_len: usize,
        capacity: usize,
        configured_market_slots: usize,
    ) -> V16Result<()> {
        if supplied_len != capacity || capacity < configured_market_slots {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_validate_dynamic_market_slots_len(
        supplied_len: usize,
        capacity: usize,
        configured_market_slots: usize,
    ) -> V16Result<()> {
        Self::validate_dynamic_market_slots_len_static(
            supplied_len,
            capacity,
            configured_market_slots,
        )
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn validate_dynamic_market_slot_shape_at<S: MarketSlotV16View>(
        &self,
        slot_index: usize,
        slot: &S,
    ) -> V16Result<()> {
        let configured_market_slots = self.config.max_market_slots.get() as usize;
        let capacity = self.asset_slot_capacity.get() as usize;
        if slot_index >= capacity || capacity < configured_market_slots {
            return Err(V16Error::InvalidConfig);
        }
        if slot_index >= configured_market_slots
            && !slot
                .engine_slot()
                .is_zero_fill_or_canonical_disabled_slot()?
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_validate_dynamic_market_slot_shape_at<S: MarketSlotV16View>(
        &self,
        slot_index: usize,
        slot: &S,
    ) -> V16Result<()> {
        self.validate_dynamic_market_slot_shape_at(slot_index, slot)
    }

    pub fn activate_empty_market_slot_not_atomic<S: MarketSlotV16ViewMut>(
        &mut self,
        asset_index: u32,
        slot: &mut S,
        authenticated_price: u64,
        now_slot: u64,
    ) -> V16Result<()> {
        let config = self.config.try_to_runtime_shape()?;
        let capacity = self.asset_slot_capacity.get();
        if asset_index >= capacity || asset_index as usize >= config.max_market_slots as usize {
            return Err(V16Error::InvalidLeg);
        }
        if decode_market_mode(self.mode)? != MarketModeV16::Live
            || authenticated_price == 0
            || authenticated_price > MAX_ORACLE_PRICE
            || now_slot < self.current_slot.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        config.validate_public_user_fund_shape()?;
        if self.asset_activation_count.get() != 0 {
            let elapsed = now_slot
                .checked_sub(self.last_asset_activation_slot.get())
                .ok_or(V16Error::Stale)?;
            if elapsed < config.asset_activation_cooldown_slots {
                return Err(V16Error::LockActive);
            }
        }
        let slot = slot.engine_slot_mut();
        let previous_asset = slot.asset.try_to_runtime()?;
        if !EngineAssetSlotV16Account::asset_state_is_empty_for_activation(previous_asset) {
            return Err(V16Error::LockActive);
        }
        match previous_asset.lifecycle {
            AssetLifecycleV16::Disabled => {
                if previous_asset.market_id != 0 {
                    return Err(V16Error::LockActive);
                }
            }
            AssetLifecycleV16::Retired => {
                if previous_asset.market_id == 0 || previous_asset.retired_slot == 0 {
                    return Err(V16Error::LockActive);
                }
                let elapsed = now_slot
                    .checked_sub(previous_asset.retired_slot)
                    .ok_or(V16Error::Stale)?;
                if elapsed < config.asset_activation_cooldown_slots {
                    return Err(V16Error::LockActive);
                }
                slot.validate_market_id_binding()?;
            }
            _ => return Err(V16Error::LockActive),
        }
        if slot.insurance_domain_spent_long.get() != 0
            || slot.insurance_domain_spent_short.get() != 0
            || slot.pending_domain_loss_barrier_long.get() != 0
            || slot.pending_domain_loss_barrier_short.get() != 0
            || !EngineAssetSlotV16Account::source_credit_account_is_empty_for_activation(
                slot.source_credit_long,
            )
            || !EngineAssetSlotV16Account::source_credit_account_is_empty_for_activation(
                slot.source_credit_short,
            )
            || !slot.backing_long.try_to_runtime()?.is_empty_amount_shape()
            || !slot.backing_short.try_to_runtime()?.is_empty_amount_shape()
            || slot.insurance_reservation_long.try_to_runtime()?
                != InsuranceCreditReservationV16::EMPTY
            || slot.insurance_reservation_short.try_to_runtime()?
                != InsuranceCreditReservationV16::EMPTY
        {
            return Err(V16Error::LockActive);
        }

        let market_id = self.next_market_id.get();
        if market_id == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let next_market_id = market_id.checked_add(1).ok_or(V16Error::CounterOverflow)?;
        let next_activation_count = self
            .asset_activation_count
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        let next_asset_set_epoch = self
            .asset_set_epoch
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        let next_risk_epoch = self
            .risk_epoch
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        let mut asset = AssetStateV16::default();
        asset.market_id = market_id;
        asset.lifecycle = AssetLifecycleV16::Active;
        asset.raw_oracle_target_price = authenticated_price;
        asset.effective_price = authenticated_price;
        asset.fund_px_last = authenticated_price;
        asset.slot_last = now_slot;
        *slot = EngineAssetSlotV16Account {
            asset: AssetStateV16Account::from_runtime(&asset),
            insurance_domain_budget_long: V16PodU128::default(),
            insurance_domain_budget_short: V16PodU128::default(),
            insurance_domain_spent_long: V16PodU128::default(),
            insurance_domain_spent_short: V16PodU128::default(),
            pending_domain_loss_barrier_long: V16PodU64::default(),
            pending_domain_loss_barrier_short: V16PodU64::default(),
            source_credit_long: SourceCreditStateV16Account::from_runtime(
                &SourceCreditStateV16::EMPTY,
            ),
            source_credit_short: SourceCreditStateV16Account::from_runtime(
                &SourceCreditStateV16::EMPTY,
            ),
            backing_long: BackingBucketV16Account::from_runtime(
                &BackingBucketV16::empty_for_market(market_id),
            ),
            backing_short: BackingBucketV16Account::from_runtime(
                &BackingBucketV16::empty_for_market(market_id),
            ),
            insurance_reservation_long: InsuranceCreditReservationV16Account::from_runtime(
                &InsuranceCreditReservationV16::EMPTY,
            ),
            insurance_reservation_short: InsuranceCreditReservationV16Account::from_runtime(
                &InsuranceCreditReservationV16::EMPTY,
            ),
        };
        self.next_market_id = V16PodU64::new(next_market_id);
        self.current_slot = V16PodU64::new(now_slot);
        self.asset_activation_count = V16PodU64::new(next_activation_count);
        self.last_asset_activation_slot = V16PodU64::new(now_slot);
        self.asset_set_epoch = V16PodU64::new(next_asset_set_epoch);
        self.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    pub fn activate_empty_asset_slot_not_atomic(
        &mut self,
        asset_index: u32,
        slot: &mut EngineAssetSlotV16Account,
        authenticated_price: u64,
        now_slot: u64,
    ) -> V16Result<()> {
        self.activate_empty_market_slot_not_atomic(asset_index, slot, authenticated_price, now_slot)
    }
}

#[cfg(any(test, kani, feature = "audit-scan"))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct MarketAggregateTotalsV16 {
    backing_provider_earnings: u128,
    source_claim_bound_num: u128,
    source_fresh_backing_num: u128,
    source_insurance_credit_reserved_atoms: u128,
    insurance_domain_budget_remaining_atoms: u128,
    resolved_payout_blocker_count: u64,
}

impl<'a, T> MarketGroupV16View<'a, T> {
    pub fn validate_shape(&self) -> V16Result<()> {
        MarketGroupV16HeaderAccount::validate_dynamic_market_slots_len_static(
            self.markets.len(),
            self.header.asset_slot_capacity.get() as usize,
            self.header.config.max_market_slots.get() as usize,
        )?;
        self.header.config.try_to_runtime_shape()?;
        decode_bool(self.header.bankruptcy_hlock_active)?;
        decode_bool(self.header.threshold_stress_active)?;
        // A-6: envelope sentinel-pairing invariant. When the flag is false AND the accumulator is
        // zero (no envelope open), both slot/epoch sentinels must be u64::MAX. Any other byte pattern
        // is a legal u128/u64, so this is the only structural check; a violation implies a torn write.
        if !decode_bool(self.header.threshold_stress_active)?
            && self.header.stress_consumption_bps_e9_since_envelope.get() == 0
            && (self.header.stress_envelope_start_slot.get() != u64::MAX
                || self.header.stress_envelope_start_credit_epoch.get() != u64::MAX)
        {
            return Err(V16Error::InvalidConfig);
        }
        decode_bool(self.header.loss_stale_active)?;
        decode_bool(self.header.payout_snapshot_captured)?;
        self.header.recovery_reason.try_to_runtime()?;
        let resolved_ledger = self.header.resolved_payout_ledger.try_to_runtime()?;
        if self.header.vault.get() > MAX_VAULT_TVL {
            return Err(V16Error::InvalidConfig);
        }
        if self.header.c_tot.get() > self.header.vault.get()
            || self.header.insurance.get() > self.header.vault.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        if self.header.pnl_matured_pos_tot.get() > self.header.pnl_pos_tot.get()
            || self.header.pnl_pos_bound_tot.get() < self.header.pnl_pos_tot.get()
            || self.header.slot_last.get() > self.header.current_slot.get()
            || self.header.next_market_id.get() == 0
        {
            return Err(V16Error::InvalidConfig);
        }
        let derived_bound =
            V16Core::amount_from_bound_num(self.header.pnl_pos_bound_tot_num.get())?;
        if self.header.pnl_pos_bound_tot.get() != derived_bound {
            return Err(V16Error::InvalidConfig);
        }
        let exact_bound_num = V16Core::bound_num_from_amount(self.header.pnl_pos_tot.get())?;
        if self.header.pnl_pos_bound_tot_num.get() < exact_bound_num {
            return Err(V16Error::InvalidConfig);
        }
        if !decode_bool(self.header.payout_snapshot_captured)?
            && resolved_ledger != ResolvedPayoutLedgerV16::EMPTY
        {
            return Err(V16Error::InvalidConfig);
        }
        if self.header.asset_activation_count.get() == 0 {
            if self.header.last_asset_activation_slot.get() != 0 {
                return Err(V16Error::InvalidConfig);
            }
        } else if self.header.last_asset_activation_slot.get() > self.header.current_slot.get() {
            return Err(V16Error::InvalidConfig);
        }

        self.validate_header_aggregate_totals()?;
        #[cfg(any(test, kani, feature = "audit-scan"))]
        {
            self.validate_shape_full_audit_scan()?;
        }
        Ok(())
    }

    fn validate_header_aggregate_totals(&self) -> V16Result<()> {
        let senior = self
            .header
            .c_tot
            .get()
            .checked_add(self.header.insurance.get())
            .and_then(|v| v.checked_add(self.header.backing_provider_earnings_total.get()))
            .ok_or(V16Error::ArithmeticOverflow)?;
        if senior > self.header.vault.get() {
            return Err(V16Error::InvalidConfig);
        }
        // Recoverable counterparty backing principal is also a vault claim:
        // every deposit moves vault and backing in lockstep, every consume that
        // re-credits c_tot debits backing first, so the strengthened stack must
        // always be covered. A state violating it is double-promising atoms.
        let senior_with_backing = senior
            .checked_add(self.header.source_fresh_backing_total_num.get() / BOUND_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if senior_with_backing > self.header.vault.get() {
            return Err(V16Error::InvalidConfig);
        }
        if self
            .header
            .source_insurance_credit_reserved_total_atoms
            .get()
            > self.header.insurance.get()
            || self.header.insurance_domain_budget_remaining_total.get()
                > self.header.insurance.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        // The group junior-claim bound is the denominator for the non-source
        // haircut and the resolved-payout snapshot, so it must never understate
        // the aggregate per-domain source claims it haircuts against; an
        // understated bound shrinks that denominator and over-credits support.
        // The credit/burn paths maintain this in lockstep; enforce it here so a
        // deserialized or future-corrupted state cannot slip through.
        if self.header.pnl_pos_bound_tot_num.get() < self.header.source_claim_bound_total_num.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    /// Kani/test shim: exposes the private `validate_header_aggregate_totals`
    /// for use in formal harnesses. Called from `proofs_v17_fork.rs` LP-NON-DRIFT.
    #[cfg(kani)]
    pub fn kani_validate_header_aggregate_totals(&self) -> V16Result<()> {
        self.validate_header_aggregate_totals()
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn validate_shape_full_audit_scan(&self) -> V16Result<()> {
        let totals = self.compute_aggregate_totals_and_validate_slots()?;
        if totals.backing_provider_earnings != self.header.backing_provider_earnings_total.get()
            || totals.source_claim_bound_num != self.header.source_claim_bound_total_num.get()
            || totals.source_fresh_backing_num != self.header.source_fresh_backing_total_num.get()
            || totals.source_insurance_credit_reserved_atoms
                != self
                    .header
                    .source_insurance_credit_reserved_total_atoms
                    .get()
            || totals.insurance_domain_budget_remaining_atoms
                != self.header.insurance_domain_budget_remaining_total.get()
            || totals.resolved_payout_blocker_count
                != self.header.resolved_payout_blocker_count.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn compute_aggregate_totals_and_validate_slots(&self) -> V16Result<MarketAggregateTotalsV16> {
        let mode = decode_market_mode(self.header.mode)?;
        let configured_assets = self.header.config.max_market_slots.get() as usize;
        let mut totals = MarketAggregateTotalsV16::default();
        let mut i = 0usize;
        while i < self.markets.len() {
            let slot = self.markets[i].engine_slot();
            totals.resolved_payout_blocker_count = totals
                .resolved_payout_blocker_count
                .checked_add(slot_resolved_payout_blockers_v16(slot)?)
                .ok_or(V16Error::CounterOverflow)?;
            totals.backing_provider_earnings = totals
                .backing_provider_earnings
                .checked_add(slot.backing_long.utilization_fee_earnings.get())
                .and_then(|v| v.checked_add(slot.backing_short.utilization_fee_earnings.get()))
                .ok_or(V16Error::ArithmeticOverflow)?;
            let asset = slot.asset.try_to_runtime()?;
            if i >= configured_assets {
                if asset.lifecycle != AssetLifecycleV16::Disabled
                    || asset.market_id != 0
                    || !EngineAssetSlotV16Account::asset_state_is_empty_for_activation(asset)
                    || !slot.is_zero_fill_or_canonical_disabled_slot()?
                {
                    return Err(V16Error::InvalidConfig);
                }
                i += 1;
                continue;
            }
            if asset.lifecycle == AssetLifecycleV16::Disabled
                && asset.market_id == 0
                && slot.is_zero_fill_or_canonical_disabled_slot()?
            {
                i += 1;
                continue;
            }
            Self::validate_asset_shape_for_view(
                asset,
                mode,
                self.header.current_slot.get(),
                self.header.next_market_id.get(),
            )?;
            let source_credit_long = slot.source_credit_long.try_to_runtime()?;
            totals.source_claim_bound_num = totals
                .source_claim_bound_num
                .checked_add(source_credit_long.positive_claim_bound_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            totals.source_fresh_backing_num = totals
                .source_fresh_backing_num
                .checked_add(source_credit_long.fresh_reserved_backing_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            Self::validate_domain_shape_for_view(
                asset.market_id,
                source_credit_long,
                slot.backing_long.try_to_runtime()?,
                slot.insurance_reservation_long.try_to_runtime()?,
                slot.insurance_domain_budget_long.get(),
                slot.insurance_domain_spent_long.get(),
                slot.pending_domain_loss_barrier_long.get(),
                self.header.current_slot.get(),
                &mut totals.source_insurance_credit_reserved_atoms,
            )?;
            totals.insurance_domain_budget_remaining_atoms = totals
                .insurance_domain_budget_remaining_atoms
                .checked_add(
                    slot.insurance_domain_budget_long
                        .get()
                        .checked_sub(slot.insurance_domain_spent_long.get())
                        .ok_or(V16Error::InvalidConfig)?,
                )
                .ok_or(V16Error::ArithmeticOverflow)?;
            let source_credit_short = slot.source_credit_short.try_to_runtime()?;
            totals.source_claim_bound_num = totals
                .source_claim_bound_num
                .checked_add(source_credit_short.positive_claim_bound_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            totals.source_fresh_backing_num = totals
                .source_fresh_backing_num
                .checked_add(source_credit_short.fresh_reserved_backing_num)
                .ok_or(V16Error::ArithmeticOverflow)?;
            Self::validate_domain_shape_for_view(
                asset.market_id,
                source_credit_short,
                slot.backing_short.try_to_runtime()?,
                slot.insurance_reservation_short.try_to_runtime()?,
                slot.insurance_domain_budget_short.get(),
                slot.insurance_domain_spent_short.get(),
                slot.pending_domain_loss_barrier_short.get(),
                self.header.current_slot.get(),
                &mut totals.source_insurance_credit_reserved_atoms,
            )?;
            totals.insurance_domain_budget_remaining_atoms = totals
                .insurance_domain_budget_remaining_atoms
                .checked_add(
                    slot.insurance_domain_budget_short
                        .get()
                        .checked_sub(slot.insurance_domain_spent_short.get())
                        .ok_or(V16Error::InvalidConfig)?,
                )
                .ok_or(V16Error::ArithmeticOverflow)?;
            i += 1;
        }
        Ok(totals)
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn validate_asset_shape_for_view(
        asset: AssetStateV16,
        mode: MarketModeV16,
        current_slot: u64,
        next_market_id: u64,
    ) -> V16Result<()> {
        if matches!(asset.lifecycle, AssetLifecycleV16::Disabled) {
            if asset.market_id != 0 {
                return Err(V16Error::InvalidConfig);
            }
        } else if asset.market_id == 0 || asset.market_id >= next_market_id {
            return Err(V16Error::InvalidConfig);
        }
        let requires_price = matches!(
            asset.lifecycle,
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly | AssetLifecycleV16::Recovery
        );
        if (requires_price
            && (asset.effective_price == 0
                || asset.effective_price > MAX_ORACLE_PRICE
                || asset.raw_oracle_target_price == 0
                || asset.raw_oracle_target_price > MAX_ORACLE_PRICE
                || asset.fund_px_last == 0
                || asset.fund_px_last > MAX_ORACLE_PRICE))
            || asset.slot_last > current_slot
            || asset.k_long == i128::MIN
            || asset.k_short == i128::MIN
            || asset.f_long_num == i128::MIN
            || asset.f_short_num == i128::MIN
            || asset.k_epoch_start_long == i128::MIN
            || asset.k_epoch_start_short == i128::MIN
            || asset.f_epoch_start_long_num == i128::MIN
            || asset.f_epoch_start_short_num == i128::MIN
            || asset.kf_epoch_long > asset.slot_last
            || asset.kf_epoch_short > asset.slot_last
            || asset.oi_eff_long_q > crate::MAX_OI_SIDE_Q
            || asset.oi_eff_short_q > crate::MAX_OI_SIDE_Q
            // The Live matched-book invariant (oi_eff_long == oi_eff_short) holds for
            // a normally-trading asset (Active/DrainOnly always reduce matched pairs).
            // A single asset can be in `Recovery` lifecycle inside a still-`Live`
            // market: `force_asset_recovery` flips the asset to Recovery while the
            // market mode stays Live, and the recovery teardown legitimately retires
            // one side's `oi_eff` to 0 before the opposite side settles (the imbalance
            // is bookkept by `pending_obligation_count`). Gate the symmetry conjunct on
            // asset lifecycle, not market mode, so this intended transient asymmetry is
            // not flagged. Empty lifecycles are symmetric at 0, so only Recovery needs
            // the exemption; Active/DrainOnly enforcement is unchanged.
            //
            // Do NOT narrow this to `pending_obligation_count != 0`. That was tried
            // (2026-09-14) and re-creates a false positive: a Recovery asset whose
            // OPPOSITE side has already completed terminal wind-down holds a real
            // position on one side and nothing on the other, with both obligation
            // counts at 0 -- the very state `forfeit_recovery_leg_not_atomic`'s
            // CommitRecovery arm exists for. Pinned by
            // `v16_recovery_forfeit_commits_terminal_recovery_when_absorbing_side_is_empty`,
            // whose fixture the narrower gate rejects before forfeit even runs.
            || (mode == MarketModeV16::Live
                && asset.lifecycle != AssetLifecycleV16::Recovery
                && asset.oi_eff_long_q != asset.oi_eff_short_q)
            || asset.stale_account_count_long > asset.stored_pos_count_long
            || asset.stale_account_count_short > asset.stored_pos_count_short
            || asset.loss_weight_sum_long > SOCIAL_LOSS_DEN
            || asset.loss_weight_sum_short > SOCIAL_LOSS_DEN
            || (asset.oi_eff_long_q != 0 && asset.loss_weight_sum_long == 0)
            || (asset.oi_eff_short_q != 0 && asset.loss_weight_sum_short == 0)
            || (asset.loss_weight_sum_long != 0 && asset.stored_pos_count_long == 0)
            || (asset.loss_weight_sum_short != 0 && asset.stored_pos_count_short == 0)
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    #[cfg(any(test, kani, feature = "audit-scan"))]
    fn validate_domain_shape_for_view(
        market_id: u64,
        source: SourceCreditStateV16,
        bucket: BackingBucketV16,
        reservation: InsuranceCreditReservationV16,
        budget: u128,
        spent: u128,
        pending_barrier: u64,
        _current_slot: u64,
        live_source_credit_insurance_atoms: &mut u128,
    ) -> V16Result<()> {
        if spent > budget || pending_barrier > 1 {
            return Err(V16Error::InvalidConfig);
        }
        V16Core::validate_source_domain_ledger_parts(market_id, source, bucket, reservation)?;
        let reserved_atoms = V16Core::amount_from_bound_num(source.insurance_credit_reserved_num)?;
        *live_source_credit_insurance_atoms = live_source_credit_insurance_atoms
            .checked_add(reserved_atoms)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if spent
            .checked_add(reserved_atoms)
            .ok_or(V16Error::ArithmeticOverflow)?
            > budget
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }
}

impl<'a, T> MarketGroupV16ViewMut<'a, T> {
    pub fn validate_shape(&self) -> V16Result<()> {
        self.as_view().validate_shape()
    }

    pub fn register_empty_materialized_portfolio_not_atomic(
        &mut self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        if !account.is_empty_for_dematerialization()? {
            return Err(V16Error::LockActive);
        }
        self.header.materialized_portfolio_count = V16PodU64::new(
            self.header
                .materialized_portfolio_count
                .get()
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
        );
        self.validate_shape_audit_scan()
    }

    pub fn deregister_empty_materialized_portfolio_not_atomic(
        &mut self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        if !account.is_empty_for_dematerialization()? {
            return Err(V16Error::LockActive);
        }
        self.header.materialized_portfolio_count = V16PodU64::new(
            self.header
                .materialized_portfolio_count
                .get()
                .checked_sub(1)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        self.validate_shape_audit_scan()
    }

    #[cfg(kani)]
    pub fn refresh_header_aggregate_totals_for_test(&mut self) -> V16Result<()> {
        let totals = self
            .as_view()
            .compute_aggregate_totals_and_validate_slots()?;
        self.header.backing_provider_earnings_total =
            V16PodU128::new(totals.backing_provider_earnings);
        self.header.source_claim_bound_total_num = V16PodU128::new(totals.source_claim_bound_num);
        self.header.source_fresh_backing_total_num =
            V16PodU128::new(totals.source_fresh_backing_num);
        self.header.source_insurance_credit_reserved_total_atoms =
            V16PodU128::new(totals.source_insurance_credit_reserved_atoms);
        self.header.insurance_domain_budget_remaining_total =
            V16PodU128::new(totals.insurance_domain_budget_remaining_atoms);
        self.header.resolved_payout_blocker_count =
            V16PodU64::new(totals.resolved_payout_blocker_count);
        Ok(())
    }

    #[inline]
    fn validate_shape_audit_scan(&self) -> V16Result<()> {
        #[cfg(feature = "audit-scan")]
        {
            self.validate_shape()
        }
        #[cfg(not(feature = "audit-scan"))]
        {
            Ok(())
        }
    }

    #[inline]
    fn validate_account_audit_scan(&self, _account: &PortfolioV16View<'_>) -> V16Result<()> {
        #[cfg(feature = "audit-scan")]
        {
            _account.validate_with_market(&self.as_view())
        }
        #[cfg(not(feature = "audit-scan"))]
        {
            Ok(())
        }
    }

    fn validate_account_scalar_preflight(&self, account: &PortfolioV16View<'_>) -> V16Result<()> {
        if account.header.provenance_header.market_group_id != self.header.market_group_id
            || account.header.owner != account.header.provenance_header.owner
            || account.header.provenance_header.version.get() != V16_ACCOUNT_VERSION
            || account.header.provenance_header.layout_discriminator.get()
                != V16_LAYOUT_DISCRIMINATOR
        {
            return Err(V16Error::ProvenanceMismatch);
        }
        let pnl = account.header.pnl.get();
        validate_non_min_i128(pnl)?;
        validate_fee_credits(account.header.fee_credits.get())?;
        let liquidation_lock = decode_bool(account.header.liquidation_lock)?;
        if liquidation_lock && pnl >= 0 {
            return Err(V16Error::InvalidLeg);
        }
        if account.header.reserved_pnl.get() > pnl.max(0) as u128 {
            return Err(V16Error::InvalidLeg);
        }
        if account.header.residual_spent_principal_atoms_total.get()
            > account.header.residual_crystallized_loss_atoms_total.get()
        {
            return Err(V16Error::InvalidLeg);
        }
        PortfolioV16View::validate_resolved_payout_receipt_static(
            account.header.resolved_payout_receipt.try_to_runtime()?,
        )?;
        if account.header.close_progress.try_to_runtime()? != CloseProgressLedgerV16::EMPTY {
            account.validate_close_progress_ledger_with_market(&self.as_view())?;
        }
        Ok(())
    }

    fn configured_domain_count(&self) -> V16Result<usize> {
        v16_domain_count_for_market_slots(self.header.config.max_market_slots.get())
    }

    fn apply_total_delta(total: u128, old: u128, new: u128) -> V16Result<u128> {
        if new >= old {
            total
                .checked_add(new - old)
                .ok_or(V16Error::CounterOverflow)
        } else {
            total
                .checked_sub(old - new)
                .ok_or(V16Error::CounterUnderflow)
        }
    }

    fn apply_total_delta_u64(total: u64, old: u64, new: u64) -> V16Result<u64> {
        if new >= old {
            total
                .checked_add(new - old)
                .ok_or(V16Error::CounterOverflow)
        } else {
            total
                .checked_sub(old - new)
                .ok_or(V16Error::CounterUnderflow)
        }
    }

    fn domain_budget_remaining_parts(budget: u128, spent: u128) -> V16Result<u128> {
        budget.checked_sub(spent).ok_or(V16Error::InvalidConfig)
    }

    fn update_source_credit_aggregate_totals(
        &mut self,
        old: SourceCreditStateV16,
        new: SourceCreditStateV16,
    ) -> V16Result<()> {
        let old_insurance_atoms =
            V16Core::amount_from_bound_num(old.insurance_credit_reserved_num)?;
        let new_insurance_atoms =
            V16Core::amount_from_bound_num(new.insurance_credit_reserved_num)?;
        self.header.source_claim_bound_total_num = V16PodU128::new(Self::apply_total_delta(
            self.header.source_claim_bound_total_num.get(),
            old.positive_claim_bound_num,
            new.positive_claim_bound_num,
        )?);
        self.header.source_fresh_backing_total_num = V16PodU128::new(Self::apply_total_delta(
            self.header.source_fresh_backing_total_num.get(),
            old.fresh_reserved_backing_num,
            new.fresh_reserved_backing_num,
        )?);
        self.header.source_insurance_credit_reserved_total_atoms =
            V16PodU128::new(Self::apply_total_delta(
                self.header
                    .source_insurance_credit_reserved_total_atoms
                    .get(),
                old_insurance_atoms,
                new_insurance_atoms,
            )?);
        Ok(())
    }

    fn update_backing_aggregate_totals(
        &mut self,
        old: BackingBucketV16,
        new: BackingBucketV16,
    ) -> V16Result<()> {
        self.header.backing_provider_earnings_total = V16PodU128::new(Self::apply_total_delta(
            self.header.backing_provider_earnings_total.get(),
            old.utilization_fee_earnings,
            new.utilization_fee_earnings,
        )?);
        Ok(())
    }

    fn update_resolved_payout_blocker_total(&mut self, old: u64, new: u64) -> V16Result<()> {
        self.header.resolved_payout_blocker_count = V16PodU64::new(Self::apply_total_delta_u64(
            self.header.resolved_payout_blocker_count.get(),
            old,
            new,
        )?);
        Ok(())
    }

    // Senior backing-provider earnings (LP utilization fees) summed across every
    // domain — the same quantity validate_shape's senior stack includes.
    fn backing_provider_earnings_total(&self) -> u128 {
        self.header.backing_provider_earnings_total.get()
    }

    // Recoverable counterparty backing principal (Fresh-bucket unliened+liened
    // atoms across every domain): provider-withdrawable whenever the domain is
    // fully backed, with no mode or payout-snapshot gate, so it is a senior-side
    // claim on the vault — never junior surplus.
    fn source_fresh_backing_total_atoms(&self) -> u128 {
        self.header.source_fresh_backing_total_num.get() / BOUND_SCALE
    }

    // Junior (positive-PnL) payout pool = vault minus ALL senior claims: capital
    // (c_tot), insurance, backing-provider earnings, AND recoverable counterparty
    // backing principal. Omitting a senior claim here over-states the pool and
    // promises the same vault atoms to two parties: a haircut resolved-close
    // over-pays winners out of value its owner can still withdraw (or, when the
    // final validate_shape catches it, deadlocks the close permanently).
    fn residual(&self) -> u128 {
        self.header.vault.get().saturating_sub(
            self.header
                .c_tot
                .get()
                .saturating_add(self.header.insurance.get())
                .saturating_add(self.backing_provider_earnings_total())
                .saturating_add(self.source_fresh_backing_total_atoms()),
        )
    }

    #[cfg(kani)]
    pub fn kani_residual(&self) -> u128 {
        self.residual()
    }

    fn junior_claim_bound(&self) -> u128 {
        self.header.pnl_pos_bound_tot.get()
    }

    fn domain_asset_side(&self, domain: usize) -> V16Result<(usize, SideV16)> {
        let configured_domains = self.configured_domain_count()?;
        if domain >= configured_domains {
            return Err(V16Error::InvalidLeg);
        }
        let asset_index = domain / 2;
        let side = if domain % 2 == 0 {
            SideV16::Long
        } else {
            SideV16::Short
        };
        if asset_index >= self.markets.len() {
            return Err(V16Error::InvalidLeg);
        }
        Ok((asset_index, side))
    }

    #[cfg(kani)]
    pub fn kani_domain_asset_side(&self, domain: usize) -> V16Result<(usize, SideV16)> {
        self.domain_asset_side(domain)
    }

    fn insurance_domain_index(&self, asset_index: usize, side: SideV16) -> V16Result<usize> {
        if asset_index >= self.header.config.max_market_slots.get() as usize {
            return Err(V16Error::InvalidLeg);
        }
        let domain = asset_index
            .checked_mul(2)
            .and_then(|v| v.checked_add(encode_side(side) as usize))
            .ok_or(V16Error::ArithmeticOverflow)?;
        self.domain_asset_side(domain)?;
        Ok(domain)
    }

    #[cfg(kani)]
    pub fn kani_insurance_domain_index(
        &self,
        asset_index: usize,
        side: SideV16,
    ) -> V16Result<usize> {
        self.insurance_domain_index(asset_index, side)
    }

    fn source_credit_for_domain(&self, domain: usize) -> V16Result<SourceCreditStateV16> {
        let source = self.source_credit_for_domain_shape(domain)?;
        V16Core::validate_source_credit_state_static(source)?;
        Ok(source)
    }

    fn source_credit_for_domain_shape(&self, domain: usize) -> V16Result<SourceCreditStateV16> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot();
        let source = match side {
            SideV16::Long => slot.source_credit_long,
            SideV16::Short => slot.source_credit_short,
        };
        let out = SourceCreditStateV16 {
            positive_claim_bound_num: source.positive_claim_bound_num.get(),
            exact_positive_claim_num: source.exact_positive_claim_num.get(),
            fresh_reserved_backing_num: source.fresh_reserved_backing_num.get(),
            spent_backing_num: source.spent_backing_num.get(),
            provider_receivable_num: source.provider_receivable_num.get(),
            valid_liened_backing_num: source.valid_liened_backing_num.get(),
            impaired_liened_backing_num: source.impaired_liened_backing_num.get(),
            insurance_credit_reserved_num: source.insurance_credit_reserved_num.get(),
            valid_liened_insurance_num: source.valid_liened_insurance_num.get(),
            impaired_liened_insurance_num: source.impaired_liened_insurance_num.get(),
            credit_rate_num: source.credit_rate_num.get(),
            credit_epoch: source.credit_epoch.get(),
        };
        V16Core::validate_source_credit_state_shape_static(out)?;
        Ok(out)
    }

    fn set_source_credit_for_domain(
        &mut self,
        domain: usize,
        source: SourceCreditStateV16,
    ) -> V16Result<()> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let old_source = self.source_credit_for_domain_shape(domain)?;
        self.update_source_credit_aggregate_totals(old_source, source)?;
        let slot = self.markets[asset_index].engine_slot_mut();
        match side {
            SideV16::Long => {
                slot.source_credit_long = SourceCreditStateV16Account::from_runtime(&source)
            }
            SideV16::Short => {
                slot.source_credit_short = SourceCreditStateV16Account::from_runtime(&source)
            }
        }
        Ok(())
    }

    fn backing_bucket_for_domain(&self, domain: usize) -> V16Result<BackingBucketV16> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot();
        match side {
            SideV16::Long => slot.backing_long.try_to_runtime(),
            SideV16::Short => slot.backing_short.try_to_runtime(),
        }
    }

    #[cfg(kani)]
    pub fn kani_backing_bucket_for_domain(&self, domain: usize) -> V16Result<BackingBucketV16> {
        self.backing_bucket_for_domain(domain)
    }

    fn set_backing_bucket_for_domain(
        &mut self,
        domain: usize,
        bucket: BackingBucketV16,
    ) -> V16Result<()> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let old_bucket = self.backing_bucket_for_domain(domain)?;
        self.update_backing_aggregate_totals(old_bucket, bucket)?;
        let slot = self.markets[asset_index].engine_slot_mut();
        match side {
            SideV16::Long => slot.backing_long = BackingBucketV16Account::from_runtime(&bucket),
            SideV16::Short => slot.backing_short = BackingBucketV16Account::from_runtime(&bucket),
        }
        Ok(())
    }

    fn insurance_reservation_for_domain(
        &self,
        domain: usize,
    ) -> V16Result<InsuranceCreditReservationV16> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot();
        match side {
            SideV16::Long => slot.insurance_reservation_long.try_to_runtime(),
            SideV16::Short => slot.insurance_reservation_short.try_to_runtime(),
        }
    }

    fn validate_source_domain_ledger(&self, domain: usize) -> V16Result<()> {
        let source = self.source_credit_for_domain_shape(domain)?;
        let bucket = self.backing_bucket_for_domain(domain)?;
        let reservation = self.insurance_reservation_for_domain(domain)?;
        let (asset_index, _) = self.domain_asset_side(domain)?;
        let market_id = self.markets[asset_index].engine.asset.market_id.get();
        V16Core::validate_source_domain_ledger_parts(market_id, source, bucket, reservation)
    }

    fn validate_source_domain_ledger_current(&self, domain: usize) -> V16Result<()> {
        self.validate_source_domain_ledger(domain)?;
        let bucket = self.backing_bucket_for_domain(domain)?;
        if bucket.status == BackingBucketStatusV16::Fresh
            && bucket.expiry_slot <= self.header.current_slot.get()
        {
            return Err(V16Error::Stale);
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_validate_source_domain_ledger_current(&self, domain: usize) -> V16Result<()> {
        self.validate_source_domain_ledger_current(domain)
    }

    fn recompute_source_credit_domain_after_mutation(&mut self, domain: usize) -> V16Result<()> {
        let source = self.source_credit_for_domain_shape(domain)?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    fn refresh_source_credit_domain_after_mutation(&mut self, domain: usize) -> V16Result<()> {
        self.recompute_source_credit_domain_after_mutation(domain)?;
        self.reservation_encumbrance_proof_for_domain(domain)?
            .validate()?;
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn add_source_positive_claim_bound_not_atomic(
        &mut self,
        domain: usize,
        claim_bound_num: u128,
        exact_claim_num: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if exact_claim_num > claim_bound_num {
            return Err(V16Error::InvalidConfig);
        }
        let source = V16Core::prepare_source_positive_claim_bound_delta(
            self.source_credit_for_domain(domain)?,
            claim_bound_num,
            exact_claim_num,
        )?;
        self.set_source_credit_for_domain(domain, source)?;
        self.refresh_source_credit_domain_after_mutation(domain)
    }

    fn reservation_encumbrance_proof_for_domain(
        &self,
        domain: usize,
    ) -> V16Result<ReservationEncumbranceProofV16> {
        let source = self.source_credit_for_domain(domain)?;
        let bucket = self.backing_bucket_for_domain(domain)?;
        let reservation = self.insurance_reservation_for_domain(domain)?;
        Ok(ReservationEncumbranceProofV16 {
            domain: u16::try_from(domain).map_err(|_| V16Error::ArithmeticOverflow)?,
            exact_positive_claim_num: source.exact_positive_claim_num,
            positive_claim_bound_num: source.positive_claim_bound_num,
            source_fresh_reserved_backing_num: source.fresh_reserved_backing_num,
            source_spent_backing_num: source.spent_backing_num,
            source_provider_receivable_num: source.provider_receivable_num,
            bucket_fresh_unliened_backing_num: bucket.fresh_unliened_backing_num,
            bucket_valid_liened_backing_num: bucket.valid_liened_backing_num,
            bucket_consumed_liened_backing_num: bucket.consumed_liened_backing_num,
            source_valid_liened_backing_num: source.valid_liened_backing_num,
            source_impaired_liened_backing_num: source.impaired_liened_backing_num,
            bucket_impaired_liened_backing_num: bucket.impaired_liened_backing_num,
            source_insurance_credit_reserved_num: source.insurance_credit_reserved_num,
            reservation_insurance_credit_reserved_num: reservation.insurance_credit_reserved_num,
            source_valid_liened_insurance_num: source.valid_liened_insurance_num,
            reservation_valid_liened_insurance_num: reservation.valid_liened_insurance_num,
            source_impaired_liened_insurance_num: source.impaired_liened_insurance_num,
            reservation_impaired_liened_insurance_num: reservation.impaired_liened_insurance_num,
            source_credit_rate_num: source.credit_rate_num,
        })
    }

    fn reservation_encumbrance_proof_for_domain_parts(
        &self,
        domain: usize,
        source: SourceCreditStateV16,
        bucket: BackingBucketV16,
        reservation: InsuranceCreditReservationV16,
    ) -> V16Result<ReservationEncumbranceProofV16> {
        self.domain_asset_side(domain)?;
        Ok(ReservationEncumbranceProofV16 {
            domain: u16::try_from(domain).map_err(|_| V16Error::ArithmeticOverflow)?,
            exact_positive_claim_num: source.exact_positive_claim_num,
            positive_claim_bound_num: source.positive_claim_bound_num,
            source_fresh_reserved_backing_num: source.fresh_reserved_backing_num,
            source_spent_backing_num: source.spent_backing_num,
            source_provider_receivable_num: source.provider_receivable_num,
            bucket_fresh_unliened_backing_num: bucket.fresh_unliened_backing_num,
            bucket_valid_liened_backing_num: bucket.valid_liened_backing_num,
            bucket_consumed_liened_backing_num: bucket.consumed_liened_backing_num,
            source_valid_liened_backing_num: source.valid_liened_backing_num,
            source_impaired_liened_backing_num: source.impaired_liened_backing_num,
            bucket_impaired_liened_backing_num: bucket.impaired_liened_backing_num,
            source_insurance_credit_reserved_num: source.insurance_credit_reserved_num,
            reservation_insurance_credit_reserved_num: reservation.insurance_credit_reserved_num,
            source_valid_liened_insurance_num: source.valid_liened_insurance_num,
            reservation_valid_liened_insurance_num: reservation.valid_liened_insurance_num,
            source_impaired_liened_insurance_num: source.impaired_liened_insurance_num,
            reservation_impaired_liened_insurance_num: reservation.impaired_liened_insurance_num,
            source_credit_rate_num: source.credit_rate_num,
        })
    }

    fn fresh_counterparty_backing_expiry_slot(&self, domain: usize) -> V16Result<u64> {
        self.domain_asset_side(domain)?;
        let bucket = self.backing_bucket_for_domain(domain)?;
        if bucket.status == BackingBucketStatusV16::Fresh
            && bucket.expiry_slot > self.header.current_slot.get()
        {
            return Ok(bucket.expiry_slot);
        }
        let config = self.header.config.try_to_runtime_shape()?;
        let freshness_horizon = config
            .max_accrual_dt_slots
            .max(config.h_max)
            .max(config.max_bankrupt_close_lifetime_slots)
            .max(1);
        self.header
            .current_slot
            .get()
            .checked_add(freshness_horizon)
            .ok_or(V16Error::CounterOverflow)
    }

    fn add_fresh_counterparty_backing_unchecked(
        &mut self,
        domain: usize,
        amount: u128,
        expiry_slot: u64,
    ) -> V16Result<()> {
        let bucket = self.backing_bucket_for_domain(domain)?;
        let source = self.source_credit_for_domain(domain)?;
        let (bucket, source) = V16Core::prepare_counterparty_backing_add_delta(
            bucket,
            source,
            amount,
            self.header.current_slot.get(),
            expiry_slot,
        )?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.recompute_source_credit_domain_after_mutation(domain)?;
        self.reservation_encumbrance_proof_for_domain(domain)?
            .validate()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn add_fresh_counterparty_backing_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
        expiry_slot: u64,
    ) -> V16Result<()> {
        self.add_fresh_counterparty_backing_unchecked(domain, amount, expiry_slot)?;
        self.validate_shape()
    }

    /// Deposits external quote into a source domain's fresh counterparty backing.
    ///
    /// `amount` is quote atoms. The backing ledger stores BOUND_SCALE-scaled
    /// amounts, while vault stores quote atoms, so both sides move in one engine
    /// transition.
    pub fn deposit_fresh_counterparty_backing_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
        expiry_slot: u64,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let backing_num = V16Core::bound_num_from_amount(amount)?;
        self.add_fresh_counterparty_backing_unchecked(domain, backing_num, expiry_slot)?;
        self.header.vault = V16PodU128::new(
            self.header
                .vault
                .get()
                .checked_add(amount)
                .ok_or(V16Error::ArithmeticOverflow)?,
        );
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    /// Withdraws unliened fresh counterparty-backing principal.
    ///
    /// The withdrawal is allowed only if the source domain remains fully backed
    /// (`credit_rate_num == CREDIT_RATE_SCALE`) after the principal leaves. This
    /// prevents a backing provider from withdrawing principal that currently
    /// supports outstanding source-credit claims.
    pub fn withdraw_fresh_counterparty_backing_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let backing_num = V16Core::bound_num_from_amount(amount)?;
        let (bucket, source) = V16Core::prepare_counterparty_backing_withdraw_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            backing_num,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        if source.credit_rate_num != CREDIT_RATE_SCALE {
            return Err(V16Error::LockActive);
        }
        let next_vault = self
            .header
            .vault
            .get()
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.header.vault = V16PodU128::new(next_vault);
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    // Contract layer: terminal retirement removes only value that has no
    // remaining domain or source-credit claimant. Any vault value above
    // insurance is claim-free protocol surplus at this boundary; the wrapper
    // pairs the complete accounting transition with an SPL-token burn.
    // (upstream a87c9a5b / 545e0224)
    /// `additional_reserved` (protocol-fee RESERVE amendment,
    /// ~/v17/DECISIONS-LEDGER.md) is a caller-supplied claim that still sits
    /// inside `insurance`. In this fork unwithdrawn protocol fees are an
    /// unbudgeted slice of `header.insurance`; the engine has no concept of
    /// who owns it (that ledger lives in the wrapper's `WrapperConfigV16`,
    /// `protocol_fee_accrued_atoms - protocol_fee_withdrawn_atoms`). Upstream
    /// has no such claim and retires the entire vault, which would burn an
    /// unwithdrawn protocol fee. A retirement whose postcondition is an empty
    /// vault cannot leave a floor behind, so any nonzero `additional_reserved`
    /// fails closed with `LockActive`: the caller withdraws the fee first
    /// (`withdraw_insurance_surplus_not_atomic`) and then retires with `0`.
    /// Pass `0` to recover upstream behavior exactly; the `(vault, 0, 0)`
    /// postcondition is unchanged.
    fn retire_terminal_unbudgeted_insurance_delta(
        vault: u128,
        insurance: u128,
        budget_remaining: u128,
        source_reserved_atoms: u128,
        additional_reserved: u128,
    ) -> V16Result<(u128, u128, u128)> {
        if insurance > vault
            || budget_remaining != 0
            || source_reserved_atoms != 0
            || additional_reserved != 0
        {
            return Err(V16Error::LockActive);
        }
        Ok((vault, 0, 0))
    }

    fn retire_terminal_unbudgeted_insurance_core_not_atomic(
        &mut self,
        additional_reserved: u128,
    ) -> V16Result<u128> {
        let vault_before = self.header.vault.get();
        let insurance_before = self.header.insurance.get();
        let (retired, next_vault, next_insurance) =
            Self::retire_terminal_unbudgeted_insurance_delta(
                vault_before,
                insurance_before,
                self.header.insurance_domain_budget_remaining_total.get(),
                self.header
                    .source_insurance_credit_reserved_total_atoms
                    .get(),
                additional_reserved,
            )?;
        self.header.vault = V16PodU128::new(next_vault);
        self.header.insurance = V16PodU128::new(next_insurance);
        let protocol_surplus = vault_before
            .checked_sub(insurance_before)
            .ok_or(V16Error::CounterUnderflow)?;
        TokenValueFlowProofV16::unallocated_protocol_surplus_to_insurance(
            protocol_surplus,
            vault_before,
            vault_before,
        )?
        .validate()?;
        TokenValueFlowProofV16::insurance_capital_to_external_out(
            retired,
            vault_before,
            next_vault,
        )?
        .validate()?;
        Ok(retired)
    }

    /// Retires the final unbudgeted insurance and claim-free protocol surplus
    /// from an otherwise empty resolved market. No recoverable insurance
    /// overlap, domain budget, source reservation, portfolio, PnL, backing
    /// claim, or payout receipt may remain. (upstream a87c9a5b / 545e0224)
    ///
    /// `additional_reserved` -- see `retire_terminal_unbudgeted_insurance_delta`
    /// doc -- lets the caller (wrapper) declare the protocol's
    /// accrued-but-unwithdrawn fee claim that still sits inside `insurance`.
    /// Any nonzero value fails closed with `LockActive` before any mutation;
    /// withdraw the fee, then retire with `0`. Pass `0` for upstream behavior.
    pub fn retire_terminal_unbudgeted_insurance_not_atomic(
        &mut self,
        additional_reserved: u128,
    ) -> V16Result<u128> {
        self.validate_shape()?;
        self.require_terminal_claim_free_state()?;
        if self.header.backing_provider_earnings_total.get() != 0
            || self.header.source_fresh_backing_total_num.get() != 0
        {
            return Err(V16Error::LockActive);
        }
        if self.first_terminal_claim_free_recredit_asset()?.is_some() {
            return Err(V16Error::LockActive);
        }
        let retired =
            self.retire_terminal_unbudgeted_insurance_core_not_atomic(additional_reserved)?;
        self.validate_shape()?;
        Ok(retired)
    }

    fn recredit_terminal_claim_free_overlap_for_source_domain_not_atomic(
        &mut self,
        source_domain: usize,
        claim_free_residual_remaining: &mut u128,
    ) -> V16Result<u128> {
        let (asset_index, source_side) = self.domain_asset_side(source_domain)?;
        let insurance_domain =
            self.insurance_domain_index(asset_index, opposite_side(source_side))?;
        let (_, insurance_spent) = self.domain_insurance_budget_spent(insurance_domain)?;
        let provider_receivable_atoms = self
            .source_credit_for_domain(source_domain)?
            .provider_receivable_num
            / BOUND_SCALE;
        let recredit = V16Core::terminal_claim_free_overlap_recredit(
            provider_receivable_atoms,
            insurance_spent,
            *claim_free_residual_remaining,
        );
        if recredit == 0 {
            return Ok(0);
        }

        let vault_before = self.header.vault.get();
        self.header.insurance = V16PodU128::new(
            self.header
                .insurance
                .get()
                .checked_add(recredit)
                .ok_or(V16Error::ArithmeticOverflow)?,
        );
        self.set_domain_insurance_spent_core(
            insurance_domain,
            insurance_spent
                .checked_sub(recredit)
                .ok_or(V16Error::CounterUnderflow)?,
        )?;
        *claim_free_residual_remaining = claim_free_residual_remaining
            .checked_sub(recredit)
            .ok_or(V16Error::CounterUnderflow)?;
        TokenValueFlowProofV16::unallocated_protocol_surplus_to_insurance(
            recredit,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        Ok(recredit)
    }

    /// Shared gate of the three terminal public entries: Resolved and no
    /// trader claim of any kind remains. (upstream 76a86f48 / 545e0224)
    fn require_terminal_claim_free_state(&self) -> V16Result<()> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Resolved
            || self.header.materialized_portfolio_count.get() != 0
            || self.header.c_tot.get() != 0
            || self.header.pnl_pos_tot.get() != 0
            || self.header.pnl_matured_pos_tot.get() != 0
            || self.header.pnl_pos_bound_tot.get() != 0
            || self.header.pnl_pos_bound_tot_num.get() != 0
            || self.header.source_claim_bound_total_num.get() != 0
            || self.header.resolved_payout_blocker_count.get() != 0
            || self.header.stale_certificate_count.get() != 0
            || self.header.b_stale_account_count.get() != 0
            || self.header.negative_pnl_account_count.get() != 0
        {
            return Err(V16Error::LockActive);
        }
        Ok(())
    }

    /// Read-only recredit amount for one persisted asset slot, so the bounded
    /// scan does no view resolution. (upstream af7b4d2a)
    fn terminal_claim_free_recredit_for_slot(
        slot: &EngineAssetSlotV16Account,
        claim_free_residual: u128,
    ) -> V16Result<u128> {
        let long_source_recredit = V16Core::terminal_claim_free_overlap_recredit(
            slot.source_credit_long.provider_receivable_num.get() / BOUND_SCALE,
            slot.insurance_domain_spent_short.get(),
            claim_free_residual,
        );
        let residual_after_long = claim_free_residual
            .checked_sub(long_source_recredit)
            .ok_or(V16Error::CounterUnderflow)?;
        let short_source_recredit = V16Core::terminal_claim_free_overlap_recredit(
            slot.source_credit_short.provider_receivable_num.get() / BOUND_SCALE,
            slot.insurance_domain_spent_long.get(),
            residual_after_long,
        );
        long_source_recredit
            .checked_add(short_source_recredit)
            .ok_or(V16Error::ArithmeticOverflow)
    }

    fn first_terminal_claim_free_recredit_asset(&self) -> V16Result<Option<usize>> {
        let residual = self.residual();
        if residual == 0 {
            return Ok(None);
        }
        let configured_assets = self.header.config.max_market_slots.get() as usize;
        for asset_index in 0..configured_assets {
            if Self::terminal_claim_free_recredit_for_slot(
                self.markets[asset_index].engine_slot(),
                residual,
            )? != 0
            {
                return Ok(Some(asset_index));
            }
        }
        Ok(None)
    }

    /// Restores one asset's claim-free terminal residual that is also backed by
    /// both an outstanding counterparty-provider receivable and historical
    /// insurance spend on the paired side. The final materialized-portfolio gate
    /// makes the residual unowned by traders before any reclassification occurs.
    ///
    /// This operation is intentionally asset-local: wrapper callers can make
    /// bounded progress even when the market account contains thousands of
    /// configured slots. (upstream 76a86f48 [BLOCKER LoF])
    fn recredit_terminal_claim_free_residual_for_asset_core_not_atomic(
        &mut self,
        asset_index: usize,
    ) -> V16Result<u128> {
        let mut claim_free_residual_remaining = self.residual();
        let mut recredited_total = 0u128;
        for side in [SideV16::Long, SideV16::Short] {
            if claim_free_residual_remaining == 0 {
                break;
            }
            let source_domain = self.insurance_domain_index(asset_index, side)?;
            let recredited = self
                .recredit_terminal_claim_free_overlap_for_source_domain_not_atomic(
                    source_domain,
                    &mut claim_free_residual_remaining,
                )?;
            recredited_total = recredited_total
                .checked_add(recredited)
                .ok_or(V16Error::ArithmeticOverflow)?;
        }
        Ok(recredited_total)
    }

    pub fn recredit_terminal_claim_free_residual_for_asset_not_atomic(
        &mut self,
        asset_index: usize,
    ) -> V16Result<u128> {
        self.validate_shape()?;
        self.require_terminal_claim_free_state()?;
        let recredited =
            self.recredit_terminal_claim_free_residual_for_asset_core_not_atomic(asset_index)?;
        self.validate_shape()?;
        Ok(recredited)
    }

    /// Advances one bounded terminal cleanup step. A nonzero scan start must be the exact
    /// `ScanProgress` continuation persisted by the wrapper. The scan never advances past a Fresh
    /// backing bucket: it expires an elapsed bucket, advances up to a still-live bucket, or returns
    /// `LockActive` when already parked on one. This makes the prefix stable across authenticated
    /// slot changes without requiring every continuation to land in one slot. The wrapper owns the
    /// continuation state and closes external custody only for `ReadyToClose`.
    /// (upstream 545e0224 / a8f81352 / af7b4d2a / 91481480 / 0b63e1c5 / bb877cde /
    /// 6f3c5c12; d87da490's modulo continuation gate was superseded by bb877cde
    /// upstream and is deliberately absent here too)
    ///
    /// `additional_reserved` -- see `retire_terminal_unbudgeted_insurance_delta`
    /// doc -- is consulted only by the final `ReadyToClose` retirement. Expiry
    /// and recredit steps never lower `insurance` or `vault`, so a nonzero
    /// reserve still lets the scan progress and fails closed with `LockActive`
    /// exactly where retirement would burn the protocol's fee. Pass `0` for
    /// upstream behavior.
    pub fn advance_terminal_slab_not_atomic(
        &mut self,
        authenticated_slot: u64,
        scan_start_asset_index: usize,
        additional_reserved: u128,
    ) -> V16Result<TerminalSlabOutcomeV16> {
        self.validate_shape()?;
        self.require_terminal_claim_free_state()?;
        self.advance_resolved_slot_not_atomic(authenticated_slot)?;

        let configured_assets = self.header.config.max_market_slots.get() as usize;
        if scan_start_asset_index != 0 && scan_start_asset_index >= configured_assets {
            return Err(V16Error::InvalidConfig);
        }
        let inspect_backing = self.header.source_fresh_backing_total_num.get() != 0;
        let residual = self.residual();
        let inspect_recredit = residual != 0;
        if inspect_backing || inspect_recredit {
            let scan_end = scan_start_asset_index
                .checked_add(TERMINAL_SLAB_SCAN_ASSETS_PER_CALL)
                .ok_or(V16Error::ArithmeticOverflow)?
                .min(configured_assets);
            for asset_index in scan_start_asset_index..scan_end {
                let step = {
                    let slot = self.markets[asset_index].engine_slot();
                    let long_status = decode_backing_bucket_status(slot.backing_long.status)?;
                    let short_status = decode_backing_bucket_status(slot.backing_short.status)?;
                    let recreditable = inspect_recredit
                        && Self::terminal_claim_free_recredit_for_slot(slot, residual)? != 0;
                    V16Core::kernel_terminal_slab_asset_step(
                        if inspect_backing {
                            long_status
                        } else {
                            BackingBucketStatusV16::Empty
                        },
                        slot.backing_long.expiry_slot.get(),
                        if inspect_backing {
                            short_status
                        } else {
                            BackingBucketStatusV16::Empty
                        },
                        slot.backing_short.expiry_slot.get(),
                        authenticated_slot,
                        recreditable,
                    )
                };
                match step {
                    TerminalSlabAssetStepV16::Expire(side_offset) => {
                        let domain = asset_index
                            .checked_mul(2)
                            .and_then(|value| value.checked_add(side_offset))
                            .ok_or(V16Error::ArithmeticOverflow)?;
                        self.expire_source_backing_bucket_not_atomic(domain, authenticated_slot)?;
                        self.validate_shape()?;
                        return Ok(TerminalSlabOutcomeV16::BackingExpired { domain });
                    }
                    TerminalSlabAssetStepV16::Recredit => {
                        let amount = self
                            .recredit_terminal_claim_free_residual_for_asset_core_not_atomic(
                                asset_index,
                            )?;
                        if amount == 0 {
                            return Err(V16Error::InvalidConfig);
                        }
                        self.validate_shape()?;
                        return Ok(TerminalSlabOutcomeV16::InsuranceRecredited {
                            asset_index,
                            amount,
                        });
                    }
                    TerminalSlabAssetStepV16::Wait => {
                        let next_asset_index = V16Core::kernel_terminal_slab_wait_continuation(
                            scan_start_asset_index,
                            asset_index,
                        )?;
                        return Ok(TerminalSlabOutcomeV16::ScanProgress { next_asset_index });
                    }
                    TerminalSlabAssetStepV16::Continue => {}
                }
            }
            if scan_end != configured_assets {
                return Ok(TerminalSlabOutcomeV16::ScanProgress {
                    next_asset_index: scan_end,
                });
            }
        }

        if self.header.backing_provider_earnings_total.get() != 0
            || self.header.source_fresh_backing_total_num.get() != 0
        {
            return Err(V16Error::LockActive);
        }
        let retired =
            self.retire_terminal_unbudgeted_insurance_core_not_atomic(additional_reserved)?;
        self.validate_shape()?;
        Ok(TerminalSlabOutcomeV16::ReadyToClose { retired })
    }

    pub fn expire_source_backing_bucket_not_atomic(
        &mut self,
        domain: usize,
        now_slot: u64,
    ) -> V16Result<()> {
        let snapshot_captured = decode_bool(self.header.payout_snapshot_captured)?;
        let residual_before = if snapshot_captured {
            self.residual()
        } else {
            0
        };
        let (bucket, source) = V16Core::prepare_counterparty_backing_expiry_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            now_slot,
        )?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.refresh_source_credit_domain_after_mutation(domain)?;
        if snapshot_captured {
            // upstream a7577b0b: principal released after the terminal snapshot
            // was captured must reach the payout ledger, not strand behind it.
            let released = self
                .residual()
                .checked_sub(residual_before)
                .ok_or(V16Error::CounterUnderflow)?;
            self.credit_post_snapshot_residual_not_atomic(released)?;
        }
        Ok(())
    }

    fn credit_post_snapshot_residual_not_atomic(&mut self, released: u128) -> V16Result<()> {
        if released == 0 || !decode_bool(self.header.payout_snapshot_captured)? {
            return Ok(());
        }
        let (ledger, legacy_snapshot) = V16Core::kernel_credit_post_snapshot_residual(
            self.header.resolved_payout_ledger.try_to_runtime()?,
            self.header.payout_snapshot.get(),
            released,
        )?;
        self.header.payout_snapshot = V16PodU128::new(legacy_snapshot);
        self.header.resolved_payout_ledger = ResolvedPayoutLedgerV16Account::from_runtime(&ledger);
        Ok(())
    }

    /// First occupied source domain of the account whose backing bucket is
    /// Fresh and lapsed at `now_slot`; the sparse tail ends the scan.
    /// (upstream c09d4575 / 867fbdc9)
    fn first_lapsed_source_backing_for_account_at_slot(
        &self,
        account: &PortfolioV16View<'_>,
        now_slot: u64,
    ) -> V16Result<Option<usize>> {
        let mut selected = None;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.header.source_domains[slot];
            let occupied = source.is_occupied();
            let sparse_tail = source.has_default_sparse_tag() && !occupied;
            let (domain, bucket_status, expiry_slot) = if occupied {
                let domain = source.domain.get() as usize;
                let bucket = self.backing_bucket_for_domain(domain)?;
                (domain, bucket.status, bucket.expiry_slot)
            } else {
                (0, BackingBucketStatusV16::Empty, 0)
            };
            let (next_selected, stop) = V16Core::kernel_lapsed_source_backing_scan_step(
                selected,
                sparse_tail,
                occupied,
                domain,
                bucket_status,
                expiry_slot,
                now_slot,
            );
            selected = next_selected;
            if stop {
                break;
            }
            slot += 1;
        }
        Ok(selected)
    }

    /// Expire exactly one lapsed backing bucket used by the account (the first in
    /// scan order) at the market clock; None when nothing has lapsed.
    /// (upstream c09d4575)
    fn expire_first_lapsed_source_backing_for_account_not_atomic(
        &mut self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<Option<usize>> {
        let current_slot = self.header.current_slot.get();
        let Some(domain) =
            self.first_lapsed_source_backing_for_account_at_slot(account, current_slot)?
        else {
            return Ok(None);
        };
        self.expire_source_backing_bucket_not_atomic(domain, current_slot)?;
        Ok(Some(domain))
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn create_source_credit_lien_from_counterparty_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.create_source_credit_lien_from_counterparty_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    fn create_source_credit_lien_from_counterparty_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (bucket, source) = V16Core::prepare_counterparty_lien_create_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            self.header.current_slot.get(),
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    // #137: reachable from the Live release path — must be compiled in.
    pub fn release_source_credit_lien_from_counterparty_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.release_source_credit_lien_from_counterparty_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    fn release_source_credit_lien_from_counterparty_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (bucket, source) = V16Core::prepare_counterparty_lien_release_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            self.header.current_slot.get(),
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    // Expiry-agnostic counterparty lien release for terminal (Resolved) wind-down; see
    // prepare_counterparty_lien_terminal_release_delta. Mirrors
    // release_source_credit_lien_from_counterparty_not_atomic but does not gate on
    // bucket freshness/expiry, so a market that resolves past a bucket's expiry can
    // still release the lien and wind the winner down.
    fn release_source_credit_lien_from_counterparty_terminal_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (bucket, source) = V16Core::prepare_counterparty_lien_terminal_release_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.validate_shape()
    }

    fn retire_source_credit_lien_from_counterparty_impaired_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (bucket, source) = V16Core::prepare_counterparty_impaired_lien_retirement_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn consume_source_credit_lien_from_counterparty_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (bucket, source) = V16Core::prepare_counterparty_lien_consume_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn consume_source_credit_lien_from_counterparty_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.consume_source_credit_lien_from_counterparty_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn impair_source_credit_lien_from_counterparty_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (bucket, source) = V16Core::prepare_counterparty_lien_impair_delta(
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            bucket,
            self.insurance_reservation_for_domain(domain)?,
        )?
        .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn impair_source_credit_lien_from_counterparty_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.impair_source_credit_lien_from_counterparty_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn reserve_insurance_credit_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        V16Core::validate_bound_num_atom_aligned(amount)?;
        let current_reservation = self.insurance_reservation_for_domain(domain)?;
        let new_reserved = current_reservation
            .insurance_credit_reserved_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        let current_reserved_atoms =
            V16Core::amount_from_bound_num(current_reservation.insurance_credit_reserved_num)?;
        let new_reserved_atoms = V16Core::amount_from_bound_num(new_reserved)?;
        let live_source_credit_insurance_atoms = Self::apply_total_delta(
            self.header
                .source_insurance_credit_reserved_total_atoms
                .get(),
            current_reserved_atoms,
            new_reserved_atoms,
        )?;
        let domain_reserved_atoms = V16Core::amount_from_bound_num(new_reserved)?;
        let (budget, spent) = self.domain_insurance_budget_spent(domain)?;
        if live_source_credit_insurance_atoms > self.header.insurance.get()
            || spent
                .checked_add(domain_reserved_atoms)
                .ok_or(V16Error::ArithmeticOverflow)?
                > budget
        {
            return Err(V16Error::LockActive);
        }
        let mut reservation = current_reservation;
        let mut source = self.source_credit_for_domain(domain)?;
        reservation.insurance_credit_reserved_num = new_reserved;
        reservation.source_credit_epoch = source.credit_epoch;
        source.insurance_credit_reserved_num = source
            .insurance_credit_reserved_num
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            self.backing_bucket_for_domain(domain)?,
            reservation,
        )?
        .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn create_source_credit_lien_from_insurance_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.create_source_credit_lien_from_insurance_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    fn create_source_credit_lien_from_insurance_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (reservation, source) = V16Core::prepare_insurance_lien_create_delta(
            self.insurance_reservation_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            self.backing_bucket_for_domain(domain)?,
            reservation,
        )?
        .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    // #137: reachable from the Live release path — must be compiled in.
    fn release_source_credit_lien_from_insurance_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (reservation, source) = V16Core::prepare_insurance_lien_release_delta(
            self.insurance_reservation_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            self.backing_bucket_for_domain(domain)?,
            reservation,
        )?
        .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    pub fn release_source_credit_lien_from_insurance_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.release_source_credit_lien_from_insurance_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    fn release_source_credit_lien_from_insurance_terminal_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (reservation, source) = V16Core::prepare_insurance_lien_terminal_release_delta(
            self.insurance_reservation_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            self.backing_bucket_for_domain(domain)?,
            reservation,
        )?
        .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn consume_source_credit_lien_from_insurance_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (reservation, source, next_domain_spent, next_insurance) =
            V16Core::prepare_insurance_lien_consume_delta(
                self.insurance_reservation_for_domain(domain)?,
                self.source_credit_for_domain(domain)?,
                self.domain_insurance_budget_spent(domain)?.1,
                self.header.insurance.get(),
                amount,
            )?;
        let spend_atoms = self
            .header
            .insurance
            .get()
            .checked_sub(next_insurance)
            .ok_or(V16Error::CounterUnderflow)?;
        let vault_before = self.header.vault.get();
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        TokenValueFlowProofV16::validate_insurance_to_close_insurance_spent(
            spend_atoms,
            vault_before,
            self.header.vault.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            self.backing_bucket_for_domain(domain)?,
            reservation,
        )?
        .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.insurance = V16PodU128::new(next_insurance);
        self.set_domain_insurance_spent_core(domain, next_domain_spent)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.validate_shape()
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn impair_source_credit_lien_from_insurance_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let (reservation, source) = V16Core::prepare_insurance_lien_impair_delta(
            self.insurance_reservation_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
        )?;
        let (source, next_risk_epoch) = V16Core::prepare_source_credit_domain_recompute_for_epoch(
            source,
            self.header.risk_epoch.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(
            domain,
            source,
            self.backing_bucket_for_domain(domain)?,
            reservation,
        )?
        .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn impair_source_credit_lien_from_insurance_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.impair_source_credit_lien_from_insurance_core_not_atomic(domain, amount)?;
        self.validate_shape()
    }

    pub fn withdraw_backing_provider_earnings_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let mut bucket = self.backing_bucket_for_domain(domain)?;
        let (next_vault, next_earnings) = apply_backing_provider_earnings_withdraw(
            self.header.vault.get(),
            bucket.utilization_fee_earnings,
            amount,
        )?;
        bucket.utilization_fee_earnings = next_earnings;
        self.header.vault = V16PodU128::new(next_vault);
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    /// Credits already-collected backing utilization fees to the provider bucket.
    ///
    /// This does not debit an account or increase the vault; callers must have already
    /// moved value into vault slack. The method rejects if the resulting senior
    /// backing-provider claim would exceed vault coverage.
    fn credit_backing_provider_earnings_delta(
        vault: u128,
        c_tot: u128,
        insurance: u128,
        earnings_total: u128,
        bucket_earnings: u128,
        amount: u128,
    ) -> V16Result<(u128, u128)> {
        let next_earnings_total = earnings_total
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        let senior = c_tot
            .checked_add(insurance)
            .and_then(|v| v.checked_add(next_earnings_total))
            .ok_or(V16Error::ArithmeticOverflow)?;
        if senior > vault {
            return Err(V16Error::LockActive);
        }
        let next_bucket_earnings = bucket_earnings
            .checked_add(amount)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((next_earnings_total, next_bucket_earnings))
    }

    #[cfg(kani)]
    pub fn kani_credit_backing_provider_earnings_delta(
        vault: u128,
        c_tot: u128,
        insurance: u128,
        earnings_total: u128,
        bucket_earnings: u128,
        amount: u128,
    ) -> V16Result<(u128, u128)> {
        Self::credit_backing_provider_earnings_delta(
            vault,
            c_tot,
            insurance,
            earnings_total,
            bucket_earnings,
            amount,
        )
    }

    pub fn credit_backing_provider_earnings_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        let mut bucket = self.backing_bucket_for_domain(domain)?;
        if bucket.status != BackingBucketStatusV16::Fresh
            || bucket.expiry_slot <= self.header.current_slot.get()
        {
            return Err(V16Error::LockActive);
        }
        let (_, next_bucket_earnings) = Self::credit_backing_provider_earnings_delta(
            self.header.vault.get(),
            self.header.c_tot.get(),
            self.header.insurance.get(),
            self.header.backing_provider_earnings_total.get(),
            bucket.utilization_fee_earnings,
            amount,
        )?;
        bucket.utilization_fee_earnings = next_bucket_earnings;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    /// Charges an account-level backing fee and routes it to backing-provider
    /// earnings and/or domain insurance.
    ///
    /// The wrapper owns fee-policy calculation. The engine owns the value
    /// transition: account capital and `c_tot` decrease by
    /// `provider_fee + insurance_fee`; provider earnings and domain insurance
    /// budget increase by their exact routed amounts; vault is unchanged.
    pub fn charge_account_backing_fee_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        provider_domain: usize,
        provider_fee: u128,
        insurance_domain: usize,
        insurance_fee: u128,
    ) -> V16Result<u128> {
        self.domain_asset_side(provider_domain)?;
        self.domain_asset_side(insurance_domain)?;
        let total_fee = provider_fee
            .checked_add(insurance_fee)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if total_fee == 0 {
            return Ok(0);
        }
        account.validate_with_market(&self.as_view())?;
        self.ensure_favorable_action_current_certificate(&account.as_view())?;
        if account.header.pnl.get() < 0 || account.header.capital.get() < total_fee {
            return Err(V16Error::LockActive);
        }
        let cert = health_cert_after_capital_debit(
            account.header.health_cert.try_to_runtime()?,
            total_fee,
        )?;
        account.header.capital = V16PodU128::new(
            account
                .header
                .capital
                .get()
                .checked_sub(total_fee)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        self.header.c_tot = V16PodU128::new(
            self.header
                .c_tot
                .get()
                .checked_sub(total_fee)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        account.header.health_cert = HealthCertV16Account::from_runtime(&cert);

        if provider_fee != 0 {
            let mut bucket = self.backing_bucket_for_domain(provider_domain)?;
            if bucket.status != BackingBucketStatusV16::Fresh
                || bucket.expiry_slot <= self.header.current_slot.get()
            {
                return Err(V16Error::LockActive);
            }
            bucket.utilization_fee_earnings = bucket
                .utilization_fee_earnings
                .checked_add(provider_fee)
                .ok_or(V16Error::CounterOverflow)?;
            self.set_backing_bucket_for_domain(provider_domain, bucket)?;
            self.validate_source_domain_ledger(provider_domain)?;
        }

        if insurance_fee != 0 {
            let next_insurance = self
                .header
                .insurance
                .get()
                .checked_add(insurance_fee)
                .ok_or(V16Error::CounterOverflow)?;
            let (budget, _) = self.domain_insurance_budget_spent(insurance_domain)?;
            let next_budget = budget
                .checked_add(insurance_fee)
                .ok_or(V16Error::CounterOverflow)?;
            self.header.insurance = V16PodU128::new(next_insurance);
            self.set_domain_insurance_budget_core(insurance_domain, next_budget, next_insurance)?;
            self.validate_source_domain_ledger(insurance_domain)?;
        }

        TokenValueFlowProofV16::account_capital_to_insurance(
            insurance_fee,
            self.header.vault.get(),
            self.header.vault.get(),
        )?
        .validate()?;
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()?;
        Ok(total_fee)
    }

    fn account_source_claim_bound_sum_num(account: &PortfolioV16View<'_>) -> V16Result<u128> {
        let mut sum = 0u128;
        let mut d = 0usize;
        while d < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.source_domains()[d];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            sum = sum
                .checked_add(source.source_claim_bound_num.get())
                .ok_or(V16Error::ArithmeticOverflow)?;
            d += 1;
        }
        Ok(sum)
    }

    fn account_has_source_claims(account: &PortfolioV16View<'_>) -> V16Result<bool> {
        Ok(Self::account_source_claim_bound_sum_num(account)? != 0)
    }

    // Carried in from upstream alongside fdf11670: absent from this fork, and a
    // dependency of the ReleaseSourceLiens crank-entry guard below.
    fn account_has_source_liens(account: &PortfolioV16View<'_>) -> bool {
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.source_domains()[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if source.source_claim_liened_num.get() != 0 {
                return true;
            }
            slot += 1;
        }
        false
    }

    /// 6c8d94bc renamed and inverted this from the all-domains "every lien is
    /// fresh AND releasable" predicate into an any-domain "some lien has a
    /// bounded transition" predicate. The old form returned false for a domain
    /// whose bucket had already gone Impaired, and the lapsed-bucket selector
    /// only sees `Fresh` buckets -- so a flat account holding an impaired lien
    /// was invisible to every crank class at once.
    fn account_has_normalizable_source_credit_lien(
        &self,
        account: &PortfolioV16View<'_>,
        now_slot: u64,
    ) -> V16Result<bool> {
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.source_domains()[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if source.is_occupied() && source.source_claim_liened_num.get() != 0 {
                let domain = source.domain.get() as usize;
                self.domain_asset_side(domain)?;
                let counterparty_backing = source.source_lien_counterparty_backing_num.get();
                let insurance_backing = source.source_lien_insurance_backing_num.get();
                let source_credit = self.source_credit_for_domain(domain)?;
                let bucket = self.backing_bucket_for_domain(domain)?;
                let reservation = self.insurance_reservation_for_domain(domain)?;
                if V16Core::kernel_flat_source_lien_normalization(
                    source.source_claim_liened_num.get(),
                    counterparty_backing,
                    insurance_backing,
                    bucket.status,
                    bucket.expiry_slot,
                    now_slot,
                    bucket.valid_liened_backing_num,
                    bucket.impaired_liened_backing_num,
                    source_credit.valid_liened_backing_num,
                    source_credit.impaired_liened_backing_num,
                    reservation.valid_liened_insurance_num,
                    source_credit.valid_liened_insurance_num,
                ) != FlatSourceLienNormalizationV16::None
                {
                    return Ok(true);
                }
            }
            slot += 1;
        }
        Ok(false)
    }

    fn source_claim_unliened_num(account: &PortfolioV16View<'_>, domain: usize) -> V16Result<u128> {
        let source = account.source_domain(domain)?;
        let locked = source
            .source_claim_liened_num
            .get()
            .checked_add(source.source_claim_impaired_num.get())
            .ok_or(V16Error::ArithmeticOverflow)?;
        source
            .source_claim_bound_num
            .get()
            .checked_sub(locked)
            .ok_or(V16Error::CounterUnderflow)
    }

    fn impair_account_source_credit_counterparty_lien_fields(
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
    ) -> V16Result<u128> {
        let slot = account
            .source_domain_slot(domain)?
            .ok_or(V16Error::InvalidLeg)?;
        let (source, effective) = V16Core::prepare_account_counterparty_lien_impairment(
            account.header.source_domains[slot],
        )?;
        account.header.source_domains[slot] = source;
        account.header.health_cert.valid = 0;
        Ok(effective)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    fn impair_account_source_credit_insurance_lien_fields(
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
        face: u128,
        effective: u128,
    ) -> V16Result<u128> {
        let source = account.source_domain_mut_or_insert(domain)?;
        source.source_claim_insurance_liened_num = V16PodU128::new(0);
        source.source_claim_liened_num = V16PodU128::new(
            source
                .source_claim_liened_num
                .get()
                .checked_sub(face)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_claim_impaired_num = V16PodU128::new(
            source
                .source_claim_impaired_num
                .get()
                .checked_add(face)
                .ok_or(V16Error::CounterOverflow)?,
        );
        source.source_lien_insurance_backing_num = V16PodU128::new(0);
        // Genesis counter: move the pro-rata live capital-at-risk fee revenue to the impaired counter,
        // matched to the backing capital that actually crystallized. Compute BEFORE shrinking the live
        // effective reserve (the denominator). Floor rounding keeps dust with the still-live counter
        // (conservative for residual farming; never over-credits).
        let live_effective_before = source.source_lien_effective_reserved.get();
        let live_fee = source.source_lien_capital_at_risk_fee_revenue.get();
        let fee_to_crystallize = if live_effective_before == 0 || live_fee == 0 {
            0
        } else {
            U256::from_u128(live_fee)
                .checked_mul(U256::from_u128(effective))
                .ok_or(V16Error::ArithmeticOverflow)?
                .checked_div(U256::from_u128(live_effective_before))
                .ok_or(V16Error::ArithmeticOverflow)?
                .try_into_u128()
                .ok_or(V16Error::ArithmeticOverflow)?
        };
        source.source_lien_capital_at_risk_fee_revenue = V16PodU128::new(
            live_fee
                .checked_sub(fee_to_crystallize)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_lien_impaired_capital_at_risk_fee_revenue = V16PodU128::new(
            source
                .source_lien_impaired_capital_at_risk_fee_revenue
                .get()
                .checked_add(fee_to_crystallize)
                .ok_or(V16Error::CounterOverflow)?,
        );
        source.source_lien_effective_reserved = V16PodU128::new(
            source
                .source_lien_effective_reserved
                .get()
                .checked_sub(effective)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_lien_impaired_effective_reserved = V16PodU128::new(
            source
                .source_lien_impaired_effective_reserved
                .get()
                .checked_add(effective)
                .ok_or(V16Error::CounterOverflow)?,
        );
        account.header.health_cert.valid = 0;
        Ok(effective)
    }

    // Release one domain's counterparty/insurance source-credit lien and clear the
    // account's per-domain lien fields. The terminal primitives are deliberately
    // impairment-aware: valid backing returns to the provider, while backing already
    // forfeited by expiry is only removed from the impaired counters and is never
    // re-credited. Live release preserves the domain's insurance reservation; Resolved
    // wind-down releases that terminal reservation as well.
    fn release_account_source_credit_lien_for_domain_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        d: usize,
        terminal: bool,
    ) -> V16Result<()> {
        let slot = account.source_domain_slot(d)?.ok_or(V16Error::InvalidLeg)?;
        let counterparty_backing = account.header.source_domains[slot]
            .source_lien_counterparty_backing_num
            .get();
        let insurance_backing = account.header.source_domains[slot]
            .source_lien_insurance_backing_num
            .get();
        if counterparty_backing != 0 {
            // Expiry/impaired-aware: an unwind must not be blocked by time, but must
            // not resurrect principal which expiry already removed either.
            self.release_source_credit_lien_from_counterparty_terminal_not_atomic(
                d,
                counterparty_backing,
            )?;
        }
        if insurance_backing != 0 {
            if terminal {
                self.release_source_credit_lien_from_insurance_terminal_not_atomic(
                    d,
                    insurance_backing,
                )?;
            } else {
                self.release_source_credit_lien_from_insurance_not_atomic(d, insurance_backing)?;
            }
        }
        let source = &mut account.header.source_domains[slot];
        source.source_claim_liened_num = V16PodU128::new(0);
        source.source_claim_counterparty_liened_num = V16PodU128::new(0);
        source.source_claim_insurance_liened_num = V16PodU128::new(0);
        source.source_lien_effective_reserved = V16PodU128::new(0);
        source.source_lien_counterparty_backing_num = V16PodU128::new(0);
        source.source_lien_insurance_backing_num = V16PodU128::new(0);
        source.source_lien_fee_last_slot = V16PodU64::new(0);
        source.source_lien_capital_at_risk_fee_revenue = V16PodU128::new(0);
        account.reset_source_domain_slot_if_empty(slot);
        Ok(())
    }

    fn burn_impaired_account_source_claim_fields(
        account: &mut PortfolioV16ViewMut<'_>,
        slot: usize,
        burn_num: u128,
    ) -> V16Result<(u128, u128)> {
        if burn_num == 0 {
            return Ok((0, 0));
        }
        if slot >= PORTFOLIO_SOURCE_DOMAIN_CAP {
            return Err(V16Error::InvalidLeg);
        }
        let source = account.header.source_domains[slot];
        let impaired_burn = source.source_claim_impaired_num.get().min(burn_num);
        if impaired_burn == 0 {
            return Ok((0, 0));
        }
        let next_impaired = source
            .source_claim_impaired_num
            .get()
            .checked_sub(impaired_burn)
            .ok_or(V16Error::CounterUnderflow)?;
        let source = &mut account.header.source_domains[slot];
        source.source_claim_bound_num = V16PodU128::new(
            source
                .source_claim_bound_num
                .get()
                .checked_sub(impaired_burn)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_claim_impaired_num = V16PodU128::new(next_impaired);
        let impaired_effective_burn = if next_impaired == 0 {
            source.source_lien_impaired_effective_reserved.get()
        } else {
            V16Core::amount_from_bound_num(impaired_burn)?
                .min(source.source_lien_impaired_effective_reserved.get())
        };
        source.source_lien_impaired_effective_reserved = V16PodU128::new(
            source
                .source_lien_impaired_effective_reserved
                .get()
                .checked_sub(impaired_effective_burn)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        if next_impaired == 0 {
            source.source_lien_impaired_capital_at_risk_fee_revenue = V16PodU128::new(0);
        }
        Ok((impaired_burn, impaired_effective_burn))
    }

    #[cfg(kani)]
    pub fn kani_burn_impaired_account_source_claim_fields(
        account: &mut PortfolioV16ViewMut<'_>,
        slot: usize,
        burn_num: u128,
    ) -> V16Result<(u128, u128)> {
        Self::burn_impaired_account_source_claim_fields(account, slot, burn_num)
    }

    fn decrement_account_source_claim_for_domain_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        slot: usize,
        domain: usize,
        burn_num: u128,
    ) -> V16Result<()> {
        if burn_num == 0 {
            return Ok(());
        }
        if slot >= PORTFOLIO_SOURCE_DOMAIN_CAP {
            return Err(V16Error::InvalidLeg);
        }
        let source = &mut account.header.source_domains[slot];
        source.source_claim_bound_num = V16PodU128::new(
            source
                .source_claim_bound_num
                .get()
                .checked_sub(burn_num)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        let mut source_credit = self.source_credit_for_domain(domain)?;
        source_credit.positive_claim_bound_num = source_credit
            .positive_claim_bound_num
            .checked_sub(burn_num)
            .ok_or(V16Error::CounterUnderflow)?;
        source_credit.exact_positive_claim_num = source_credit
            .exact_positive_claim_num
            .checked_sub(burn_num.min(source_credit.exact_positive_claim_num))
            .ok_or(V16Error::CounterUnderflow)?;
        self.set_source_credit_for_domain(domain, source_credit)?;
        account.reset_source_domain_slot_if_empty(slot);
        self.recompute_source_credit_domain_after_mutation(domain)
    }

    fn burn_account_source_lien_face_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        slot: usize,
        domain: usize,
        face_burn_num: u128,
    ) -> V16Result<()> {
        if face_burn_num == 0 {
            return Ok(());
        }
        if slot >= PORTFOLIO_SOURCE_DOMAIN_CAP {
            return Err(V16Error::InvalidLeg);
        }
        let source_before = account.header.source_domains[slot];
        if face_burn_num > source_before.source_claim_liened_num.get() {
            return Err(V16Error::CounterUnderflow);
        }
        let (
            counterparty_face_burn,
            insurance_face_burn,
            counterparty_backing_release,
            insurance_backing_release,
            backing_release_num,
        ) = V16Core::source_lien_face_burn_plan(
            source_before.source_claim_counterparty_liened_num.get(),
            source_before.source_claim_insurance_liened_num.get(),
            source_before.source_lien_counterparty_backing_num.get(),
            source_before.source_lien_insurance_backing_num.get(),
            face_burn_num,
        )?;

        if counterparty_backing_release != 0 {
            // Unwinding returns already-liened principal; it does not extend new
            // credit, so expiry must not block a loss from being recognized.
            self.release_source_credit_lien_from_counterparty_terminal_not_atomic(
                domain,
                counterparty_backing_release,
            )?;
        }
        if insurance_backing_release != 0 {
            if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
                self.release_source_credit_lien_from_insurance_terminal_not_atomic(
                    domain,
                    insurance_backing_release,
                )?;
            } else {
                self.release_source_credit_lien_from_insurance_core_not_atomic(
                    domain,
                    insurance_backing_release,
                )?;
            }
        }

        let effective_release = backing_release_num / BOUND_SCALE;
        let counterparty_backing_after = source_before
            .source_lien_counterparty_backing_num
            .get()
            .checked_sub(counterparty_backing_release)
            .ok_or(V16Error::CounterUnderflow)?;
        let fee_revenue_after = V16Core::source_lien_fee_after_backing_release(
            source_before.source_lien_capital_at_risk_fee_revenue.get(),
            source_before.source_lien_counterparty_backing_num.get(),
            counterparty_backing_after,
        )?;

        let source = &mut account.header.source_domains[slot];
        source.source_claim_liened_num = V16PodU128::new(
            source
                .source_claim_liened_num
                .get()
                .checked_sub(face_burn_num)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_claim_counterparty_liened_num = V16PodU128::new(
            source
                .source_claim_counterparty_liened_num
                .get()
                .checked_sub(counterparty_face_burn)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_claim_insurance_liened_num = V16PodU128::new(
            source
                .source_claim_insurance_liened_num
                .get()
                .checked_sub(insurance_face_burn)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_lien_effective_reserved = V16PodU128::new(
            source
                .source_lien_effective_reserved
                .get()
                .checked_sub(effective_release)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_lien_counterparty_backing_num = V16PodU128::new(counterparty_backing_after);
        source.source_lien_insurance_backing_num = V16PodU128::new(
            source
                .source_lien_insurance_backing_num
                .get()
                .checked_sub(insurance_backing_release)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        source.source_lien_capital_at_risk_fee_revenue = V16PodU128::new(fee_revenue_after);
        if counterparty_backing_after == 0 {
            source.source_lien_fee_last_slot = V16PodU64::new(0);
        }
        account.header.health_cert.valid = 0;
        self.decrement_account_source_claim_for_domain_not_atomic(
            account,
            slot,
            domain,
            face_burn_num,
        )
    }

    fn burn_account_source_claim_bound_num(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        mut burn_num: u128,
    ) -> V16Result<()> {
        if burn_num == 0 {
            return Ok(());
        }
        let account_claim_sum = Self::account_source_claim_bound_sum_num(&account.as_view())?;
        if account_claim_sum == 0 {
            return Ok(());
        }
        if account_claim_sum < burn_num {
            return Err(V16Error::CounterUnderflow);
        }
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP && burn_num != 0 {
            let source_snapshot = account.header.source_domains[slot];
            if source_snapshot.has_default_sparse_tag() && !source_snapshot.is_occupied() {
                break;
            }
            if !source_snapshot.is_occupied() {
                slot += 1;
                continue;
            }
            let d = source_snapshot.domain.get() as usize;
            self.domain_asset_side(d)?;
            let burned =
                self.burn_account_source_claim_at_slot_up_to(account, slot, d, burn_num)?;
            burn_num = burn_num
                .checked_sub(burned)
                .ok_or(V16Error::CounterUnderflow)?;
            slot += 1;
        }
        if burn_num != 0 {
            return Err(V16Error::LockActive);
        }
        account.compact_source_domains();
        Ok(())
    }

    fn burn_account_source_claim_at_slot_up_to(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        slot: usize,
        domain: usize,
        burn_num: u128,
    ) -> V16Result<u128> {
        if burn_num == 0 {
            return Ok(0);
        }
        if slot >= PORTFOLIO_SOURCE_DOMAIN_CAP {
            return Err(V16Error::CounterUnderflow);
        }
        // Read the slot IN PLACE. Resolving the slot by scanning for `domain`
        // breaks once an earlier burn has emptied a slot and made the table
        // sparse: the lookup no longer agrees with the caller's index and a
        // still-funded later domain is refused. (upstream efa7e6f4)
        let source = account.header.source_domains[slot];
        if !source.is_occupied() || source.domain.get() as usize != domain {
            return Err(V16Error::CounterUnderflow);
        }
        let target = burn_num.min(
            account.header.source_domains[slot]
                .source_claim_bound_num
                .get(),
        );
        let mut remaining = target;

        let burn = Self::source_claim_unliened_num(&account.as_view(), domain)?.min(remaining);
        if burn != 0 {
            self.decrement_account_source_claim_for_domain_not_atomic(account, slot, domain, burn)?;
            remaining -= burn;
        }
        if remaining != 0 {
            let liened_burn = account.header.source_domains[slot]
                .source_claim_liened_num
                .get()
                .min(remaining);
            if liened_burn != 0 {
                self.burn_account_source_lien_face_not_atomic(account, slot, domain, liened_burn)?;
                remaining -= liened_burn;
            }
        }
        if remaining != 0 {
            let (impaired_burn, impaired_effective_burn) =
                Self::burn_impaired_account_source_claim_fields(account, slot, remaining)?;
            if impaired_burn != 0 {
                if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved
                    && impaired_effective_burn != 0
                {
                    let impaired_insurance_backing =
                        V16Core::bound_num_from_amount(impaired_effective_burn)?;
                    self.release_source_credit_lien_from_insurance_terminal_not_atomic(
                        domain,
                        impaired_insurance_backing,
                    )?;
                }
                let mut source_credit = self.source_credit_for_domain(domain)?;
                source_credit.positive_claim_bound_num = source_credit
                    .positive_claim_bound_num
                    .checked_sub(impaired_burn)
                    .ok_or(V16Error::CounterUnderflow)?;
                source_credit.exact_positive_claim_num = source_credit
                    .exact_positive_claim_num
                    .checked_sub(impaired_burn.min(source_credit.exact_positive_claim_num))
                    .ok_or(V16Error::CounterUnderflow)?;
                self.set_source_credit_for_domain(domain, source_credit)?;
                account.reset_source_domain_slot_if_empty(slot);
                self.recompute_source_credit_domain_after_mutation(domain)?;
                remaining -= impaired_burn;
            }
        }
        if remaining != 0 {
            return Err(V16Error::LockActive);
        }
        Ok(target)
    }

    fn burn_account_source_claim_bound_num_domain_first(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
        burn_num: u128,
    ) -> V16Result<()> {
        if burn_num == 0 {
            return Ok(());
        }
        self.domain_asset_side(domain)?;
        let slot = account.source_domain_slot(domain)?;
        let source_claim_num = match slot {
            Some(slot) => account.header.source_domains[slot]
                .source_claim_bound_num
                .get(),
            None => 0,
        };
        let (source_burn_num, fallback_burn_num) =
            V16Core::source_claim_domain_first_burn_partition(source_claim_num, burn_num);
        if let Some(slot) = slot {
            self.burn_account_source_claim_at_slot_up_to(account, slot, domain, source_burn_num)?;
            account.compact_source_domains();
        }
        self.burn_account_source_claim_bound_num(account, fallback_burn_num)
    }

    fn source_domain_realizable_support_for_face(
        &self,
        domain: usize,
        face_claim: u128,
    ) -> V16Result<u128> {
        if face_claim == 0 {
            return Ok(0);
        }
        self.validate_source_domain_ledger_current(domain)?;
        V16Core::source_credit_state_realizable_support_for_face(
            self.source_credit_for_domain(domain)?,
            face_claim,
        )
    }

    fn account_source_realizable_support(
        &self,
        account: &PortfolioV16View<'_>,
        face_claim: u128,
    ) -> V16Result<u128> {
        if face_claim == 0 {
            return Ok(0);
        }
        let mut remaining_num = V16Core::bound_num_from_amount(face_claim)?;
        let mut support = 0u128;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP && remaining_num != 0 {
            let source = account.source_domains()[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if !source.is_occupied() {
                slot += 1;
                continue;
            }
            let d = source.domain.get() as usize;
            let locked = source
                .source_claim_liened_num
                .get()
                .checked_add(source.source_claim_impaired_num.get())
                .ok_or(V16Error::ArithmeticOverflow)?;
            if locked > source.source_claim_bound_num.get() {
                return Err(V16Error::InvalidLeg);
            }
            let valid_lien_effective = source
                .source_lien_effective_reserved
                .get()
                .min(remaining_num / BOUND_SCALE);
            if valid_lien_effective != 0 {
                support = support
                    .checked_add(valid_lien_effective)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                remaining_num = remaining_num
                    .checked_sub(
                        valid_lien_effective
                            .checked_mul(BOUND_SCALE)
                            .ok_or(V16Error::ArithmeticOverflow)?,
                    )
                    .ok_or(V16Error::CounterUnderflow)?;
            }
            let claim_num = source
                .source_claim_bound_num
                .get()
                .checked_sub(locked)
                .ok_or(V16Error::CounterUnderflow)?
                .min(remaining_num);
            if claim_num != 0 {
                self.validate_source_domain_ledger_current(d)?;
                let source_credit = self.source_credit_for_domain(d)?;
                let credited = V16Core::source_credit_state_realizable_support_for_claim_num(
                    source_credit,
                    claim_num,
                )?;
                support = support
                    .checked_add(credited)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                remaining_num -= claim_num;
            }
            slot += 1;
        }
        Ok(support)
    }

    // Fork: after 592d538c the only caller left is the kani shim below, so this
    // is gated like every other proof-only helper here. Upstream gates it
    // `any(kani, feature = "fuzz")` because its fuzz targets reach it; no fuzz
    // target in this fork does.
    #[cfg(kani)]
    fn account_unliened_source_realizable_support(
        &self,
        account: &PortfolioV16View<'_>,
        face_claim: u128,
    ) -> V16Result<u128> {
        if face_claim == 0 {
            return Ok(0);
        }
        let mut remaining_num = V16Core::bound_num_from_amount(face_claim)?;
        let mut support = 0u128;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP && remaining_num != 0 {
            let source = account.source_domains()[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if !source.is_occupied() {
                slot += 1;
                continue;
            }
            let domain = source.domain.get() as usize;
            let claim_num = Self::source_claim_unliened_num(account, domain)?.min(remaining_num);
            if claim_num != 0 {
                self.validate_source_domain_ledger_current(domain)?;
                let credited = V16Core::source_credit_state_realizable_support_for_claim_num(
                    self.source_credit_for_domain(domain)?,
                    claim_num,
                )?;
                support = support
                    .checked_add(credited)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                remaining_num -= claim_num;
            }
            slot += 1;
        }
        Ok(support)
    }

    fn source_credit_available_backing_num(&self, domain: usize) -> V16Result<u128> {
        V16Core::available_backing_num_for_source_credit_state(
            self.source_credit_for_domain(domain)?,
        )
    }

    fn valid_source_lien_effective_reserved_sum(account: &PortfolioV16View<'_>) -> V16Result<u128> {
        let mut sum = 0u128;
        let mut d = 0usize;
        while d < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.source_domains()[d];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            sum = sum
                .checked_add(source.source_lien_effective_reserved.get())
                .ok_or(V16Error::ArithmeticOverflow)?;
            d += 1;
        }
        Ok(sum)
    }

    fn incremental_initial_margin_source_credit_needed(
        account: &PortfolioV16View<'_>,
        no_positive_equity: i128,
    ) -> V16Result<u128> {
        let cert = account.header.health_cert.try_to_runtime()?;
        if !cert.valid {
            return Err(V16Error::Stale);
        }
        let existing_lien = Self::valid_source_lien_effective_reserved_sum(account)?;
        if no_positive_equity >= 0 {
            let covered = (no_positive_equity as u128)
                .checked_add(existing_lien)
                .ok_or(V16Error::ArithmeticOverflow)?;
            return Ok(cert.certified_initial_req.saturating_sub(covered));
        }
        let need_before_lien = cert
            .certified_initial_req
            .checked_add(no_positive_equity.unsigned_abs())
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok(need_before_lien.saturating_sub(existing_lien))
    }

    fn set_insurance_reservation_for_domain(
        &mut self,
        domain: usize,
        reservation: InsuranceCreditReservationV16,
    ) -> V16Result<()> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot_mut();
        match side {
            SideV16::Long => {
                slot.insurance_reservation_long =
                    InsuranceCreditReservationV16Account::from_runtime(&reservation)
            }
            SideV16::Short => {
                slot.insurance_reservation_short =
                    InsuranceCreditReservationV16Account::from_runtime(&reservation)
            }
        }
        Ok(())
    }

    fn domain_insurance_budget_spent(&self, domain: usize) -> V16Result<(u128, u128)> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot();
        Ok(match side {
            SideV16::Long => (
                slot.insurance_domain_budget_long.get(),
                slot.insurance_domain_spent_long.get(),
            ),
            SideV16::Short => (
                slot.insurance_domain_budget_short.get(),
                slot.insurance_domain_spent_short.get(),
            ),
        })
    }

    fn set_domain_insurance_spent_delta(
        total_remaining: u128,
        insurance: u128,
        budget: u128,
        old_spent: u128,
        new_spent: u128,
    ) -> V16Result<u128> {
        let old_remaining = Self::domain_budget_remaining_parts(budget, old_spent)?;
        let new_remaining = Self::domain_budget_remaining_parts(budget, new_spent)?;
        let next_total = Self::apply_total_delta(total_remaining, old_remaining, new_remaining)?;
        if next_total > insurance {
            return Err(V16Error::LockActive);
        }
        Ok(next_total)
    }

    #[cfg(kani)]
    pub fn kani_set_domain_insurance_spent_delta(
        total_remaining: u128,
        insurance: u128,
        budget: u128,
        old_spent: u128,
        new_spent: u128,
    ) -> V16Result<u128> {
        Self::set_domain_insurance_spent_delta(
            total_remaining,
            insurance,
            budget,
            old_spent,
            new_spent,
        )
    }

    fn set_domain_insurance_spent_core(&mut self, domain: usize, spent: u128) -> V16Result<()> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let (old_budget, old_spent) = self.domain_insurance_budget_spent(domain)?;
        let next_total = Self::set_domain_insurance_spent_delta(
            self.header.insurance_domain_budget_remaining_total.get(),
            self.header.insurance.get(),
            old_budget,
            old_spent,
            spent,
        )?;
        self.header.insurance_domain_budget_remaining_total = V16PodU128::new(next_total);
        let slot = self.markets[asset_index].engine_slot_mut();
        match side {
            SideV16::Long => slot.insurance_domain_spent_long = V16PodU128::new(spent),
            SideV16::Short => slot.insurance_domain_spent_short = V16PodU128::new(spent),
        }
        Ok(())
    }

    /// Sets the spent amount for a domain insurance budget while preserving the
    /// aggregate remaining-budget invariant.
    pub fn set_domain_insurance_spent(&mut self, domain: usize, spent: u128) -> V16Result<()> {
        self.set_domain_insurance_spent_core(domain, spent)?;
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    fn clear_terminal_spent_domain_budget_pair(
        budget: V16PodU128,
        spent: V16PodU128,
    ) -> V16Result<(V16PodU128, V16PodU128)> {
        let budget = budget.get();
        let spent = spent.get();
        if spent == 0 {
            return Ok((V16PodU128::new(budget), V16PodU128::default()));
        }
        if budget != spent {
            return Err(V16Error::LockActive);
        }
        Ok((V16PodU128::default(), V16PodU128::default()))
    }

    fn set_domain_insurance_budget_core(
        &mut self,
        domain: usize,
        budget: u128,
        insurance_limit: u128,
    ) -> V16Result<()> {
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let (old_budget, spent) = self.domain_insurance_budget_spent(domain)?;
        let next_total = Self::set_domain_insurance_budget_delta(
            self.header.insurance_domain_budget_remaining_total.get(),
            insurance_limit,
            old_budget,
            spent,
            budget,
        )?;
        self.header.insurance_domain_budget_remaining_total = V16PodU128::new(next_total);
        let slot = self.markets[asset_index].engine_slot_mut();
        match side {
            SideV16::Long => slot.insurance_domain_budget_long = V16PodU128::new(budget),
            SideV16::Short => slot.insurance_domain_budget_short = V16PodU128::new(budget),
        }
        Ok(())
    }

    fn set_domain_insurance_budget_delta(
        total_remaining: u128,
        insurance_limit: u128,
        old_budget: u128,
        spent: u128,
        new_budget: u128,
    ) -> V16Result<u128> {
        let old_remaining = Self::domain_budget_remaining_parts(old_budget, spent)?;
        let new_remaining = Self::domain_budget_remaining_parts(new_budget, spent)?;
        let next_total = Self::apply_total_delta(total_remaining, old_remaining, new_remaining)?;
        if next_total > insurance_limit {
            return Err(V16Error::LockActive);
        }
        Ok(next_total)
    }

    #[cfg(kani)]
    pub fn kani_set_domain_insurance_budget_delta(
        total_remaining: u128,
        insurance_limit: u128,
        old_budget: u128,
        spent: u128,
        new_budget: u128,
    ) -> V16Result<u128> {
        Self::set_domain_insurance_budget_delta(
            total_remaining,
            insurance_limit,
            old_budget,
            spent,
            new_budget,
        )
    }

    /// Credits already-collected insurance to a domain budget without changing vault
    /// or total insurance.
    pub fn credit_domain_insurance_budget_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.credit_domain_insurance_budgets_not_atomic(&[(domain, amount)])
    }

    /// Credits multiple already-collected fee amounts and validates the resulting market once.
    /// Duplicate domains are permitted and accumulate in input order.
    pub fn credit_domain_insurance_budgets_not_atomic(
        &mut self,
        credits: &[(usize, u128)],
    ) -> V16Result<()> {
        if credits.is_empty() {
            return Err(V16Error::InvalidConfig);
        }
        for &(domain, amount) in credits {
            let (budget, _) = self.domain_insurance_budget_spent(domain)?;
            let next_budget = budget
                .checked_add(amount)
                .ok_or(V16Error::ArithmeticOverflow)?;
            self.set_domain_insurance_budget_core(
                domain,
                next_budget,
                self.header.insurance.get(),
            )?;
        }
        for &(domain, _) in credits {
            self.validate_source_domain_ledger(domain)?;
        }
        self.validate_shape()
    }

    /// Deposits external quote into insurance and credits the same domain budget.
    pub fn deposit_domain_insurance_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        let vault_before = self.header.vault.get();
        let next_vault = vault_before
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let next_insurance = self
            .header
            .insurance
            .get()
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let (budget, _) = self.domain_insurance_budget_spent(domain)?;
        let next_budget = budget
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;

        self.set_domain_insurance_budget_core(domain, next_budget, next_insurance)?;
        self.header.vault = V16PodU128::new(next_vault);
        self.header.insurance = V16PodU128::new(next_insurance);
        TokenValueFlowProofV16::external_in_to_insurance_capital(amount, vault_before, next_vault)?
            .validate()?;
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    fn withdraw_domain_insurance_delta(
        vault: u128,
        insurance: u128,
        source_reserved_atoms: u128,
        budget: u128,
        spent: u128,
        domain_reserved_atoms: u128,
        amount: u128,
    ) -> V16Result<(u128, u128, u128)> {
        let global_available = insurance.saturating_sub(source_reserved_atoms);
        let budget_remaining = budget
            .saturating_sub(spent)
            .saturating_sub(domain_reserved_atoms);
        if amount > global_available.min(budget_remaining) || amount > vault {
            return Err(V16Error::LockActive);
        }
        let next_vault = vault
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        let next_insurance = insurance
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        let next_budget = budget
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        Ok((next_vault, next_insurance, next_budget))
    }

    #[cfg(kani)]
    pub fn kani_withdraw_domain_insurance_delta(
        vault: u128,
        insurance: u128,
        source_reserved_atoms: u128,
        budget: u128,
        spent: u128,
        domain_reserved_atoms: u128,
        amount: u128,
    ) -> V16Result<(u128, u128, u128)> {
        Self::withdraw_domain_insurance_delta(
            vault,
            insurance,
            source_reserved_atoms,
            budget,
            spent,
            domain_reserved_atoms,
            amount,
        )
    }

    /// Withdraws available insurance from a single domain budget.
    pub fn withdraw_domain_insurance_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        let (budget, spent) = self.domain_insurance_budget_spent(domain)?;
        let domain_reserved_atoms = V16Core::amount_from_bound_num(
            self.insurance_reservation_for_domain(domain)?
                .insurance_credit_reserved_num,
        )?;
        let vault_before = self.header.vault.get();
        let (next_vault, next_insurance, next_budget) = Self::withdraw_domain_insurance_delta(
            vault_before,
            self.header.insurance.get(),
            self.header
                .source_insurance_credit_reserved_total_atoms
                .get(),
            budget,
            spent,
            domain_reserved_atoms,
            amount,
        )?;
        let next_insurance = V16PodU128::new(next_insurance);
        let next_vault = V16PodU128::new(next_vault);
        self.set_domain_insurance_budget_core(domain, next_budget, next_insurance.get())?;
        self.header.vault = next_vault;
        self.header.insurance = next_insurance;
        TokenValueFlowProofV16::insurance_capital_to_external_out(
            amount,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        self.validate_source_domain_ledger(domain)?;
        self.validate_shape()
    }

    fn withdraw_insurance_surplus_delta(
        vault: u128,
        insurance: u128,
        source_reserved_atoms: u128,
        budget_remaining_total: u128,
        amount: u128,
    ) -> V16Result<(u128, u128)> {
        let available_surplus = insurance
            .saturating_sub(source_reserved_atoms)
            .saturating_sub(budget_remaining_total);
        if amount > available_surplus || amount > vault {
            return Err(V16Error::LockActive);
        }
        let next_vault = vault
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        let next_insurance = insurance
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        Ok((next_vault, next_insurance))
    }

    #[cfg(kani)]
    pub fn kani_withdraw_insurance_surplus_delta(
        vault: u128,
        insurance: u128,
        source_reserved_atoms: u128,
        budget_remaining_total: u128,
        amount: u128,
    ) -> V16Result<(u128, u128)> {
        Self::withdraw_insurance_surplus_delta(
            vault,
            insurance,
            source_reserved_atoms,
            budget_remaining_total,
            amount,
        )
    }

    /// Withdraws external quote out of the market's *unbudgeted* insurance
    /// surplus — value that was charged into `header.insurance` but never
    /// credited to any domain's `insurance_domain_budget_*`. Domain budgets
    /// and source-credit reservations are untouched and cannot be reduced by
    /// this call. Protocol-agnostic at the engine level: the caller (wrapper)
    /// is responsible for tracking *who* is entitled to how much of the
    /// surplus (e.g. an accrued/withdrawn ledger) — this primitive only
    /// enforces "you cannot withdraw more than the surplus that isn't
    /// backing any domain or reservation," mirroring
    /// `withdraw_domain_insurance_not_atomic`'s bound style.
    pub fn withdraw_insurance_surplus_not_atomic(&mut self, amount: u128) -> V16Result<()> {
        let vault_before = self.header.vault.get();
        let (next_vault, next_insurance) = Self::withdraw_insurance_surplus_delta(
            vault_before,
            self.header.insurance.get(),
            self.header
                .source_insurance_credit_reserved_total_atoms
                .get(),
            self.header.insurance_domain_budget_remaining_total.get(),
            amount,
        )?;
        self.header.vault = V16PodU128::new(next_vault);
        self.header.insurance = V16PodU128::new(next_insurance);
        TokenValueFlowProofV16::insurance_capital_to_external_out(
            amount,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        self.validate_shape()
    }

    /// Pays an account from unbudgeted insurance surplus, e.g. a crank reward.
    ///
    /// Budgeted domain insurance remains isolated and cannot be consumed by this path.
    ///
    /// `additional_reserved` (protocol-fee RESERVE amendment,
    /// ~/v17/DECISIONS-LEDGER.md) is a caller-supplied floor -- on top of
    /// `budget_remaining` -- that this credit must never dip `next_insurance`
    /// below. The engine has no concept of "who" the reservation belongs to
    /// (that ledger lives in the wrapper's `WrapperConfigV16`, e.g.
    /// `protocol_fee_accrued_atoms - protocol_fee_withdrawn_atoms`); it only
    /// enforces that whatever the caller declares reserved cannot be consumed
    /// by this crank-reward-style credit. Pass `0` to recover the prior
    /// (pre-reserve) behavior exactly.
    fn credit_account_from_insurance_delta(
        insurance: u128,
        budget_remaining: u128,
        additional_reserved: u128,
        c_tot: u128,
        capital: u128,
        amount: u128,
    ) -> V16Result<(u128, u128, u128)> {
        let next_insurance = insurance
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        let reserved_floor = budget_remaining.saturating_add(additional_reserved);
        if reserved_floor > next_insurance {
            return Err(V16Error::LockActive);
        }
        let next_c_tot = c_tot
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let next_capital = capital
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok((next_insurance, next_c_tot, next_capital))
    }

    #[cfg(kani)]
    pub fn kani_credit_account_from_insurance_delta(
        insurance: u128,
        budget_remaining: u128,
        additional_reserved: u128,
        c_tot: u128,
        capital: u128,
        amount: u128,
    ) -> V16Result<(u128, u128, u128)> {
        Self::credit_account_from_insurance_delta(
            insurance,
            budget_remaining,
            additional_reserved,
            c_tot,
            capital,
            amount,
        )
    }

    /// `additional_reserved` -- see `credit_account_from_insurance_delta` doc
    /// -- lets the caller (wrapper) carve out atoms (e.g. the protocol's
    /// accrued-but-unwithdrawn fee claim) that this crank-reward-style credit
    /// must never touch, on top of the pre-existing domain-budget isolation.
    /// Pass `0` for pre-reserve-amendment behavior.
    pub fn credit_account_from_insurance_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        amount: u128,
        additional_reserved: u128,
    ) -> V16Result<()> {
        if amount == 0 {
            return Ok(());
        }
        account.validate_with_market(&self.as_view())?;
        let (next_insurance, next_c_tot, next_capital) = Self::credit_account_from_insurance_delta(
            self.header.insurance.get(),
            self.header.insurance_domain_budget_remaining_total.get(),
            additional_reserved,
            self.header.c_tot.get(),
            account.header.capital.get(),
            amount,
        )?;
        let vault = self.header.vault.get();

        self.header.insurance = V16PodU128::new(next_insurance);
        self.header.c_tot = V16PodU128::new(next_c_tot);
        account.header.capital = V16PodU128::new(next_capital);
        account.header.health_cert.valid = 0;
        TokenValueFlowProofV16::insurance_capital_to_account_capital(amount, vault, vault)?
            .validate()?;
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()
    }

    fn available_domain_insurance(&self, domain: usize) -> V16Result<u128> {
        let (budget, spent) = self.domain_insurance_budget_spent(domain)?;
        let domain_reserved_atoms = V16Core::amount_from_bound_num(
            self.insurance_reservation_for_domain(domain)?
                .insurance_credit_reserved_num,
        )?;
        let global_available = self.header.insurance.get().saturating_sub(
            self.header
                .source_insurance_credit_reserved_total_atoms
                .get(),
        );
        let budget_remaining = budget
            .saturating_sub(spent)
            .saturating_sub(domain_reserved_atoms);
        Ok(global_available.min(budget_remaining))
    }

    pub fn domain_insurance_budget_remaining(&self, domain: usize) -> V16Result<u128> {
        let (budget, spent) = self.domain_insurance_budget_spent(domain)?;
        Self::domain_budget_remaining_parts(budget, spent)
    }

    pub fn domain_insurance_withdraw_capacity(&self, domain: usize) -> V16Result<u128> {
        self.domain_asset_side(domain)?;
        Ok(self
            .available_domain_insurance(domain)?
            .min(self.header.vault.get()))
    }

    fn consume_domain_insurance_for_negative_pnl(
        &mut self,
        asset_index: usize,
        bankrupt_side: SideV16,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        let domain = self.insurance_domain_index(asset_index, opposite_side(bankrupt_side))?;
        if account.header.pnl.get() >= 0 {
            return Ok(0);
        }
        self.header.bankruptcy_hlock_active = 1;
        let residual = account.header.pnl.get().unsigned_abs();
        let domain_available = self.available_domain_insurance(domain)?;
        let used = residual.min(domain_available);
        if used == 0 {
            return Ok(0);
        }
        let vault_before = self.header.vault.get();
        self.header.insurance = V16PodU128::new(
            self.header
                .insurance
                .get()
                .checked_sub(used)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        let (_, spent_before) = self.domain_insurance_budget_spent(domain)?;
        self.set_domain_insurance_spent_core(
            domain,
            spent_before
                .checked_add(used)
                .ok_or(V16Error::ArithmeticOverflow)?,
        )?;
        let used_i128 = i128::try_from(used).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = account
            .header
            .pnl
            .get()
            .checked_add(used_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        self.set_account_pnl(account, new_pnl)?;
        TokenValueFlowProofV16::validate_insurance_to_close_insurance_spent(
            used,
            vault_before,
            self.header.vault.get(),
        )?;
        account.header.health_cert.valid = 0;
        Ok(used)
    }

    #[cfg(kani)]
    pub fn kani_consume_domain_insurance_for_negative_pnl(
        &mut self,
        asset_index: usize,
        bankrupt_side: SideV16,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        self.consume_domain_insurance_for_negative_pnl(asset_index, bankrupt_side, account)
    }

    fn liquidation_residual_after_principal_and_insurance(
        &self,
        asset_index: usize,
        bankrupt_side: SideV16,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<u128> {
        let domain = self.insurance_domain_index(asset_index, opposite_side(bankrupt_side))?;
        Ok(if account.header.pnl.get() < 0 {
            account
                .header
                .pnl
                .get()
                .unsigned_abs()
                .saturating_sub(account.header.capital.get())
                .saturating_sub(self.available_domain_insurance(domain)?)
        } else {
            0
        })
    }

    fn liquidation_residual_exceeds_single_step_capacity(
        &self,
        asset_index: usize,
        bankrupt_side: SideV16,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<bool> {
        let residual_after_principal_and_insurance = self
            .liquidation_residual_after_principal_and_insurance(
                asset_index,
                bankrupt_side,
                account,
            )?;
        if residual_after_principal_and_insurance == 0 {
            return Ok(false);
        }
        if self.header.config.public_b_chunk_atoms.get() < residual_after_principal_and_insurance {
            return Ok(true);
        }
        let capacity = self.bankruptcy_residual_single_step_capacity(
            asset_index,
            bankrupt_side,
            residual_after_principal_and_insurance,
        )?;
        Ok(capacity < residual_after_principal_and_insurance)
    }

    fn preflight_liquidation_residual_durability(
        &mut self,
        asset_index: usize,
        bankrupt_side: SideV16,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        if self.liquidation_residual_exceeds_single_step_capacity(
            asset_index,
            bankrupt_side,
            account,
        )? {
            self.declare_permissionless_recovery(
                PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
            )?;
            return Err(V16Error::RecoveryRequired);
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_clear_leg(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
    ) -> V16Result<()> {
        self.clear_leg(account, asset_index)
    }

    #[cfg(kani)]
    pub fn kani_preflight_liquidation_residual_durability(
        &mut self,
        asset_index: usize,
        bankrupt_side: SideV16,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        self.preflight_liquidation_residual_durability(asset_index, bankrupt_side, account)
    }

    fn create_and_consume_source_credit_from_counterparty_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        self.create_and_consume_source_credit_from_counterparty_parts_not_atomic(
            domain,
            self.backing_bucket_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            self.insurance_reservation_for_domain(domain)?,
            amount,
            0,
        )
    }

    fn create_and_consume_source_credit_from_counterparty_parts_not_atomic(
        &mut self,
        domain: usize,
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        reservation: InsuranceCreditReservationV16,
        amount: u128,
        source_claim_burn_num: u128,
    ) -> V16Result<()> {
        let (bucket, source) = V16Core::prepare_counterparty_lien_create_delta(
            bucket,
            source,
            self.header.current_slot.get(),
            amount,
        )?;
        let (bucket, source) =
            V16Core::prepare_counterparty_lien_consume_delta(bucket, source, amount)?;
        let source =
            V16Core::prepare_source_positive_claim_burn_delta(source, source_claim_burn_num)?;
        let epoch_steps = 1 + u64::from(source_claim_burn_num != 0);
        let (source, next_risk_epoch) =
            V16Core::prepare_source_credit_domain_recompute_for_epoch_steps(
                source,
                self.header.risk_epoch.get(),
                epoch_steps,
            )?;
        self.reservation_encumbrance_proof_for_domain_parts(domain, source, bucket, reservation)?
            .validate()?;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    fn create_and_consume_source_credit_from_insurance_core_not_atomic(
        &mut self,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if amount == 0 {
            return Ok(());
        }
        self.create_and_consume_source_credit_from_insurance_parts_not_atomic(
            domain,
            self.backing_bucket_for_domain(domain)?,
            self.insurance_reservation_for_domain(domain)?,
            self.source_credit_for_domain(domain)?,
            amount,
            0,
        )
    }

    fn create_and_consume_source_credit_from_insurance_parts_not_atomic(
        &mut self,
        domain: usize,
        bucket: BackingBucketV16,
        reservation: InsuranceCreditReservationV16,
        source: SourceCreditStateV16,
        amount: u128,
        source_claim_burn_num: u128,
    ) -> V16Result<()> {
        let (reservation, source) =
            V16Core::prepare_insurance_lien_create_delta(reservation, source, amount)?;
        let (_, spent_before) = self.domain_insurance_budget_spent(domain)?;
        let insurance_before = self.header.insurance.get();
        let (reservation, source, next_domain_spent, next_insurance) =
            V16Core::prepare_insurance_lien_consume_delta(
                reservation,
                source,
                spent_before,
                insurance_before,
                amount,
            )?;
        let source =
            V16Core::prepare_source_positive_claim_burn_delta(source, source_claim_burn_num)?;
        let spend_atoms = insurance_before
            .checked_sub(next_insurance)
            .ok_or(V16Error::CounterUnderflow)?;
        let epoch_steps = 1 + u64::from(source_claim_burn_num != 0);
        let (source, next_risk_epoch) =
            V16Core::prepare_source_credit_domain_recompute_for_epoch_steps(
                source,
                self.header.risk_epoch.get(),
                epoch_steps,
            )?;
        TokenValueFlowProofV16::validate_insurance_to_close_insurance_spent(
            spend_atoms,
            self.header.vault.get(),
            self.header.vault.get(),
        )?;
        self.reservation_encumbrance_proof_for_domain_parts(domain, source, bucket, reservation)?
            .validate()?;
        self.set_insurance_reservation_for_domain(domain, reservation)?;
        self.set_source_credit_for_domain(domain, source)?;
        self.header.insurance = V16PodU128::new(next_insurance);
        self.set_domain_insurance_spent_core(domain, next_domain_spent)?;
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        Ok(())
    }

    fn consume_source_domain_credit_for_effective_not_atomic(
        &mut self,
        domain: usize,
        effective_credit: u128,
    ) -> V16Result<SourceCreditConsumptionV16> {
        self.domain_asset_side(domain)?;
        if effective_credit == 0 {
            return Ok(SourceCreditConsumptionV16 {
                face_burn: 0,
                counterparty_credit_consumed: 0,
                insurance_credit_consumed: 0,
            });
        }
        self.validate_source_domain_ledger_current(domain)?;
        let rate = self.source_credit_for_domain(domain)?.credit_rate_num;
        let (required_face_num, backing_num) =
            V16Core::source_credit_lien_amounts_for_effective(effective_credit, rate)?;
        if self.source_credit_available_backing_num(domain)? < backing_num {
            return Err(V16Error::LockActive);
        }
        let bucket = self.backing_bucket_for_domain(domain)?;
        let mut counterparty_credit_consumed = 0;
        let mut insurance_credit_consumed = 0;
        if bucket.status == BackingBucketStatusV16::Fresh
            && bucket.expiry_slot > self.header.current_slot.get()
            && bucket.fresh_unliened_backing_num >= backing_num
        {
            self.create_and_consume_source_credit_from_counterparty_core_not_atomic(
                domain,
                backing_num,
            )?;
            counterparty_credit_consumed = effective_credit;
        } else {
            self.create_and_consume_source_credit_from_insurance_core_not_atomic(
                domain,
                backing_num,
            )?;
            insurance_credit_consumed = effective_credit;
        }
        Ok(SourceCreditConsumptionV16 {
            face_burn: V16Core::amount_from_bound_num(required_face_num)?,
            counterparty_credit_consumed,
            insurance_credit_consumed,
        })
    }

    // Loss settlement may consume whatever whole-atom support exists; routes
    // promising an exact conversion set require_full and retain fail-closed behavior.
    fn consume_validated_account_source_credit_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        effective_credit: u128,
        burn_account_claims: bool,
        require_full: bool,
    ) -> V16Result<(SourceCreditConsumptionV16, u128, u128)> {
        if effective_credit == 0 {
            return Ok((
                SourceCreditConsumptionV16 {
                    face_burn: 0,
                    counterparty_credit_consumed: 0,
                    insurance_credit_consumed: 0,
                },
                0,
                0,
            ));
        }
        let mut remaining = effective_credit;
        let mut face_burn_num = 0u128;
        let mut counterparty_credit_consumed = 0u128;
        let mut insurance_credit_consumed = 0u128;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP && remaining != 0 {
            let source = account.header.source_domains[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if !source.is_occupied() {
                slot += 1;
                continue;
            }
            let d = source.domain.get() as usize;
            let source_credit = self.source_credit_for_domain_shape(d)?;
            let bucket = self.backing_bucket_for_domain(d)?;
            let reservation = self.insurance_reservation_for_domain(d)?;
            let (asset_index, _) = self.domain_asset_side(d)?;
            let market_id = self.markets[asset_index].engine.asset.market_id.get();
            V16Core::validate_source_domain_ledger_parts(
                market_id,
                source_credit,
                bucket,
                reservation,
            )?;
            if bucket.status == BackingBucketStatusV16::Fresh
                && bucket.expiry_slot <= self.header.current_slot.get()
            {
                return Err(V16Error::Stale);
            }
            let rate = source_credit.credit_rate_num;
            let locked = source
                .source_claim_liened_num
                .get()
                .checked_add(source.source_claim_impaired_num.get())
                .ok_or(V16Error::ArithmeticOverflow)?;
            let unliened = source
                .source_claim_bound_num
                .get()
                .checked_sub(locked)
                .ok_or(V16Error::CounterUnderflow)?;
            if rate != 0 && unliened != 0 {
                let consumable = V16Core::source_credit_state_realizable_support_for_claim_num(
                    source_credit,
                    unliened,
                )?;
                let take = remaining.min(consumable);
                if take != 0 {
                    let (face_num, backing_num) =
                        V16Core::source_credit_lien_amounts_for_effective(take, rate)?;
                    if face_num > unliened {
                        return Err(V16Error::CounterUnderflow);
                    }
                    let next_account_claim = if burn_account_claims {
                        source
                            .source_claim_bound_num
                            .get()
                            .checked_sub(face_num)
                            .ok_or(V16Error::CounterUnderflow)?
                    } else {
                        source.source_claim_bound_num.get()
                    };
                    let source_claim_burn_num = if burn_account_claims { face_num } else { 0 };
                    if bucket.status == BackingBucketStatusV16::Fresh
                        && bucket.expiry_slot > self.header.current_slot.get()
                        && bucket.fresh_unliened_backing_num >= backing_num
                    {
                        self.create_and_consume_source_credit_from_counterparty_parts_not_atomic(
                            d,
                            bucket,
                            source_credit,
                            reservation,
                            backing_num,
                            source_claim_burn_num,
                        )?;
                        counterparty_credit_consumed = counterparty_credit_consumed
                            .checked_add(take)
                            .ok_or(V16Error::ArithmeticOverflow)?;
                    } else {
                        self.create_and_consume_source_credit_from_insurance_parts_not_atomic(
                            d,
                            bucket,
                            reservation,
                            source_credit,
                            backing_num,
                            source_claim_burn_num,
                        )?;
                        insurance_credit_consumed = insurance_credit_consumed
                            .checked_add(take)
                            .ok_or(V16Error::ArithmeticOverflow)?;
                    }
                    if burn_account_claims {
                        account.header.source_domains[slot].source_claim_bound_num =
                            V16PodU128::new(next_account_claim);
                    }
                    face_burn_num = face_burn_num
                        .checked_add(face_num)
                        .ok_or(V16Error::ArithmeticOverflow)?;
                    remaining = remaining
                        .checked_sub(take)
                        .ok_or(V16Error::CounterUnderflow)?;
                }
            }
            slot += 1;
        }
        let consumed = counterparty_credit_consumed
            .checked_add(insurance_credit_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if consumed
            != effective_credit
                .checked_sub(remaining)
                .ok_or(V16Error::CounterUnderflow)?
        {
            return Err(V16Error::InvalidConfig);
        }
        if require_full && consumed != effective_credit {
            return Err(V16Error::LockActive);
        }
        if burn_account_claims {
            account.compact_source_domains();
        }
        Ok((
            SourceCreditConsumptionV16 {
                face_burn: V16Core::amount_from_bound_num(face_burn_num)?,
                counterparty_credit_consumed,
                insurance_credit_consumed,
            },
            if burn_account_claims {
                face_burn_num
            } else {
                0
            },
            consumed,
        ))
    }

    fn create_source_credit_lien_backing_not_atomic(
        &mut self,
        domain: usize,
        backing_num: u128,
    ) -> V16Result<SourceCreditBackingSourceV16> {
        self.domain_asset_side(domain)?;
        if backing_num == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let bucket = self.backing_bucket_for_domain(domain)?;
        if bucket.status == BackingBucketStatusV16::Fresh
            && bucket.expiry_slot > self.header.current_slot.get()
            && bucket.fresh_unliened_backing_num >= backing_num
        {
            self.create_source_credit_lien_from_counterparty_core_not_atomic(domain, backing_num)?;
            return Ok(SourceCreditBackingSourceV16::Counterparty);
        }
        let reservation = self.insurance_reservation_for_domain(domain)?;
        let encumbered = reservation
            .valid_liened_insurance_num
            .checked_add(reservation.impaired_liened_insurance_num)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if reservation
            .insurance_credit_reserved_num
            .checked_sub(encumbered)
            .ok_or(V16Error::CounterUnderflow)?
            >= backing_num
        {
            self.create_source_credit_lien_from_insurance_core_not_atomic(domain, backing_num)?;
            return Ok(SourceCreditBackingSourceV16::Insurance);
        }
        Err(V16Error::LockActive)
    }

    fn apply_account_source_credit_lien_delta(
        source: &mut PortfolioSourceDomainV16Account,
        backing_source: SourceCreditBackingSourceV16,
        required_face_num: u128,
        required_backing_num: u128,
        effective_credit: u128,
        current_slot: u64,
    ) -> V16Result<()> {
        let prior_counterparty_backing = source.source_lien_counterparty_backing_num.get();
        source.source_claim_liened_num = V16PodU128::new(
            source
                .source_claim_liened_num
                .get()
                .checked_add(required_face_num)
                .ok_or(V16Error::ArithmeticOverflow)?,
        );
        source.source_lien_effective_reserved = V16PodU128::new(
            source
                .source_lien_effective_reserved
                .get()
                .checked_add(effective_credit)
                .ok_or(V16Error::ArithmeticOverflow)?,
        );
        match backing_source {
            SourceCreditBackingSourceV16::Counterparty => {
                source.source_claim_counterparty_liened_num = V16PodU128::new(
                    source
                        .source_claim_counterparty_liened_num
                        .get()
                        .checked_add(required_face_num)
                        .ok_or(V16Error::ArithmeticOverflow)?,
                );
                source.source_lien_counterparty_backing_num = V16PodU128::new(
                    source
                        .source_lien_counterparty_backing_num
                        .get()
                        .checked_add(required_backing_num)
                        .ok_or(V16Error::ArithmeticOverflow)?,
                );
                if prior_counterparty_backing == 0 {
                    source.source_lien_fee_last_slot = V16PodU64::new(current_slot);
                }
            }
            SourceCreditBackingSourceV16::Insurance => {
                source.source_claim_insurance_liened_num = V16PodU128::new(
                    source
                        .source_claim_insurance_liened_num
                        .get()
                        .checked_add(required_face_num)
                        .ok_or(V16Error::ArithmeticOverflow)?,
                );
                source.source_lien_insurance_backing_num = V16PodU128::new(
                    source
                        .source_lien_insurance_backing_num
                        .get()
                        .checked_add(required_backing_num)
                        .ok_or(V16Error::ArithmeticOverflow)?,
                );
            }
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_apply_counterparty_source_credit_lien_delta(
        source: &mut PortfolioSourceDomainV16Account,
        required_face_num: u128,
        required_backing_num: u128,
        effective_credit: u128,
        current_slot: u64,
    ) -> V16Result<()> {
        Self::apply_account_source_credit_lien_delta(
            source,
            SourceCreditBackingSourceV16::Counterparty,
            required_face_num,
            required_backing_num,
            effective_credit,
            current_slot,
        )
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_lien_create_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        current_slot: u64,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_lien_create_delta(bucket, source, current_slot, amount)
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_lien_consume_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_lien_consume_delta(bucket, source, amount)
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_lien_terminal_release_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_lien_terminal_release_delta(bucket, source, amount)
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_backing_add_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        amount: u128,
        current_slot: u64,
        expiry_slot: u64,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_backing_add_delta(
            bucket,
            source,
            amount,
            current_slot,
            expiry_slot,
        )
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_backing_withdraw_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_backing_withdraw_delta(bucket, source, amount)
    }

    #[cfg(kani)]
    pub fn kani_live_account_refresh_required(
        live: bool,
        cert_current: bool,
        reset_obligation: bool,
        released_obligation: bool,
        lapsed_source_backing: bool,
    ) -> bool {
        V16Core::kernel_live_account_refresh_required(
            live,
            cert_current,
            reset_obligation,
            released_obligation,
            lapsed_source_backing,
        )
    }

    #[cfg(kani)]
    pub fn kani_live_flat_source_lien_normalization_required(
        live: bool,
        cert_current: bool,
        lapsed_source_backing: bool,
        flat: bool,
        margin_safe: bool,
        normalizable_lien: bool,
    ) -> bool {
        V16Core::kernel_live_flat_source_lien_normalization_required(
            live,
            cert_current,
            lapsed_source_backing,
            flat,
            margin_safe,
            normalizable_lien,
        )
    }

    #[cfg(kani)]
    pub fn kani_flat_source_lien_normalization(
        source_claim_liened_num: u128,
        counterparty_backing_num: u128,
        insurance_backing_num: u128,
        bucket_status: BackingBucketStatusV16,
        bucket_expiry_slot: u64,
        now_slot: u64,
        bucket_valid_liened_num: u128,
        bucket_impaired_liened_num: u128,
        source_valid_liened_backing_num: u128,
        source_impaired_liened_backing_num: u128,
        reservation_valid_liened_insurance_num: u128,
        source_valid_liened_insurance_num: u128,
    ) -> u8 {
        match V16Core::kernel_flat_source_lien_normalization(
            source_claim_liened_num,
            counterparty_backing_num,
            insurance_backing_num,
            bucket_status,
            bucket_expiry_slot,
            now_slot,
            bucket_valid_liened_num,
            bucket_impaired_liened_num,
            source_valid_liened_backing_num,
            source_impaired_liened_backing_num,
            reservation_valid_liened_insurance_num,
            source_valid_liened_insurance_num,
        ) {
            FlatSourceLienNormalizationV16::None => 0,
            FlatSourceLienNormalizationV16::ImpairCounterparty => 1,
            FlatSourceLienNormalizationV16::Release => 2,
        }
    }

    #[cfg(kani)]
    pub fn kani_source_credit_lien_amounts_for_effective(
        effective_credit: u128,
        credit_rate_num: u128,
    ) -> V16Result<(u128, u128)> {
        V16Core::source_credit_lien_amounts_for_effective(effective_credit, credit_rate_num)
    }

    #[cfg(kani)]
    pub fn kani_counterparty_cure_atoms_from_scaled_backing(amount: u128) -> V16Result<u128> {
        V16Core::validate_bound_num_atom_aligned(amount)?;
        Ok(amount / BOUND_SCALE)
    }

    #[cfg(kani)]
    pub fn kani_prepare_insurance_lien_consume_delta(
        reservation: InsuranceCreditReservationV16,
        source: SourceCreditStateV16,
        domain_spent: u128,
        insurance: u128,
        amount: u128,
    ) -> V16Result<(
        InsuranceCreditReservationV16,
        SourceCreditStateV16,
        u128,
        u128,
    )> {
        V16Core::prepare_insurance_lien_consume_delta(
            reservation,
            source,
            domain_spent,
            insurance,
            amount,
        )
    }

    #[cfg(kani)]
    pub fn kani_prepare_insurance_lien_terminal_release_delta(
        reservation: InsuranceCreditReservationV16,
        source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(InsuranceCreditReservationV16, SourceCreditStateV16)> {
        V16Core::prepare_insurance_lien_terminal_release_delta(reservation, source, amount)
    }

    fn create_account_source_credit_lien_for_effective_unchecked(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
        effective_credit: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        if effective_credit == 0 {
            return Ok(());
        }
        self.validate_source_domain_ledger_current(domain)?;
        let rate = self.source_credit_for_domain(domain)?.credit_rate_num;
        let (required_face_num, required_backing_num) =
            V16Core::source_credit_lien_amounts_for_effective(effective_credit, rate)?;
        if Self::source_claim_unliened_num(&account.as_view(), domain)? < required_face_num {
            return Err(V16Error::LockActive);
        }
        self.collect_account_backing_utilization_fee_for_domain_not_atomic(account, domain)?;
        let backing_source =
            self.create_source_credit_lien_backing_not_atomic(domain, required_backing_num)?;
        let source = account.source_domain_mut_or_insert(domain)?;
        Self::apply_account_source_credit_lien_delta(
            source,
            backing_source,
            required_face_num,
            required_backing_num,
            effective_credit,
            self.header.current_slot.get(),
        )?;
        account.header.health_cert.valid = 0;
        Ok(())
    }

    fn create_account_source_credit_lien_for_effective_any_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        effective_credit: u128,
    ) -> V16Result<()> {
        // Each domain mutation preserves the same local ledger equations. Validate
        // the account once around the bounded batch instead of rescanning all source
        // slots before and after every individual domain.
        account.validate_with_market(&self.as_view())?;
        let mut remaining = effective_credit;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP && remaining != 0 {
            let source = account.header.source_domains[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if !source.is_occupied() {
                slot += 1;
                continue;
            }
            let d = source.domain.get() as usize;
            let rate = self.source_credit_for_domain(d)?.credit_rate_num;
            let unliened = Self::source_claim_unliened_num(&account.as_view(), d)?;
            if rate != 0 && unliened != 0 {
                self.validate_source_domain_ledger_current(d)?;
                let soft_num = U256::from_u128(unliened)
                    .checked_mul(U256::from_u128(rate))
                    .and_then(|v| v.checked_div(U256::from_u128(CREDIT_RATE_SCALE)))
                    .and_then(|v| v.try_into_u128())
                    .ok_or(V16Error::ArithmeticOverflow)?;
                let by_claim = soft_num / BOUND_SCALE;
                let by_backing = self.source_credit_available_backing_num(d)? / BOUND_SCALE;
                let take = remaining.min(by_claim).min(by_backing);
                if take != 0 {
                    self.create_account_source_credit_lien_for_effective_unchecked(
                        account, d, take,
                    )?;
                    remaining -= take;
                }
            }
            slot += 1;
        }
        if remaining != 0 {
            return Err(V16Error::LockActive);
        }
        account.validate_with_market(&self.as_view())
    }

    fn create_initial_margin_source_lien_if_needed(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        let mut attempts = 0u8;
        while attempts < 2 {
            if !decode_bool(account.header.health_cert.valid)? {
                return Err(V16Error::Stale);
            }
            let no_positive = Self::account_no_positive_credit_equity(&account.as_view())?;
            let required_credit = Self::incremental_initial_margin_source_credit_needed(
                &account.as_view(),
                no_positive,
            )?;
            if required_credit == 0 {
                return Ok(());
            }
            self.create_account_source_credit_lien_for_effective_any_not_atomic(
                account,
                required_credit,
            )?;
            self.recertify_account_after_source_lien_change(account)?;
            attempts += 1;
        }
        Err(V16Error::LockActive)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_create_initial_margin_source_lien_if_needed(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        self.create_initial_margin_source_lien_if_needed(account)
    }

    fn haircut_effective_support(
        &self,
        face_claim: u128,
        residual: u128,
        junior_bound: u128,
    ) -> V16Result<u128> {
        if face_claim == 0 || residual == 0 || junior_bound == 0 {
            return Ok(0);
        }
        if residual >= junior_bound {
            return Ok(face_claim);
        }
        Ok(wide_mul_div_floor_u128(face_claim, residual, junior_bound))
    }

    fn account_haircut_equity(&self, account: &PortfolioV16View<'_>) -> V16Result<i128> {
        validate_non_min_i128(account.header.pnl.get())?;
        validate_fee_credits(account.header.fee_credits.get())?;
        let capital = i128::try_from(account.header.capital.get())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        let fee_debt = i128::try_from(account.header.fee_credits.get().unsigned_abs())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        if account.header.pnl.get() <= 0 {
            return capital
                .checked_add(account.header.pnl.get())
                .and_then(|v| v.checked_sub(fee_debt))
                .ok_or(V16Error::ArithmeticOverflow);
        }
        let positive_support = if Self::account_has_source_claims(account)? {
            self.account_source_realizable_support(account, account.header.pnl.get() as u128)?
        } else {
            0
        };
        let positive_support_i128 =
            i128::try_from(positive_support).map_err(|_| V16Error::ArithmeticOverflow)?;
        capital
            .checked_add(positive_support_i128)
            .and_then(|v| v.checked_sub(fee_debt))
            .ok_or(V16Error::ArithmeticOverflow)
    }

    fn ensure_account_source_claim_market_id(
        &self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
    ) -> V16Result<()> {
        let (asset_index, _) = self.domain_asset_side(domain)?;
        let market_id = self.markets[asset_index].engine.asset.market_id.get();
        if market_id == 0 {
            return Err(V16Error::InvalidLeg);
        }
        let source = account.source_domain_mut_or_insert(domain)?;
        source.domain =
            V16PodU32::new(u32::try_from(domain).map_err(|_| V16Error::ArithmeticOverflow)?);
        if source.source_claim_market_id.get() == 0 {
            source.source_claim_market_id = V16PodU64::new(market_id);
            return Ok(());
        }
        if source.source_claim_market_id.get() != market_id {
            return Err(V16Error::HiddenLeg);
        }
        Ok(())
    }

    fn record_account_residual_crystallized_loss(
        account: &mut PortfolioV16ViewMut<'_>,
        atoms: u128,
    ) -> V16Result<()> {
        if atoms == 0 {
            return Ok(());
        }
        account.header.residual_crystallized_loss_atoms_total = V16PodU128::new(
            account
                .header
                .residual_crystallized_loss_atoms_total
                .get()
                .checked_add(atoms)
                .ok_or(V16Error::CounterOverflow)?,
        );
        Ok(())
    }

    fn add_account_u128_counter(counter: &mut V16PodU128, atoms: u128) -> V16Result<()> {
        if atoms == 0 {
            return Ok(());
        }
        *counter = V16PodU128::new(
            counter
                .get()
                .checked_add(atoms)
                .ok_or(V16Error::CounterOverflow)?,
        );
        Ok(())
    }

    fn record_account_funding_flow(
        account: &mut PortfolioV16ViewMut<'_>,
        side: SideV16,
        f_delta: i128,
    ) -> V16Result<()> {
        if f_delta < 0 {
            let atoms = f_delta.unsigned_abs();
            match side {
                SideV16::Long => {
                    Self::add_account_u128_counter(
                        &mut account.header.funding_long_paid_atoms_total,
                        atoms,
                    )?;
                }
                SideV16::Short => {
                    Self::add_account_u128_counter(
                        &mut account.header.funding_short_paid_atoms_total,
                        atoms,
                    )?;
                }
            }
        } else if f_delta > 0 {
            let atoms = f_delta as u128;
            match side {
                SideV16::Long => {
                    Self::add_account_u128_counter(
                        &mut account.header.funding_long_received_atoms_total,
                        atoms,
                    )?;
                }
                SideV16::Short => {
                    Self::add_account_u128_counter(
                        &mut account.header.funding_short_received_atoms_total,
                        atoms,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn transfer_account_residual_reward_credit(
        trader: &mut PortfolioV16ViewMut<'_>,
        lp: &mut PortfolioV16ViewMut<'_>,
        principal_atoms: u128,
    ) -> V16Result<u128> {
        if principal_atoms == 0 {
            return Ok(0);
        }
        let crystallized = trader.header.residual_crystallized_loss_atoms_total.get();
        let spent = trader.header.residual_spent_principal_atoms_total.get();
        let available = crystallized
            .checked_sub(spent)
            .ok_or(V16Error::CounterUnderflow)?;
        let credit = available.min(principal_atoms);
        if credit == 0 {
            return Ok(0);
        }
        trader.header.residual_spent_principal_atoms_total =
            V16PodU128::new(spent.checked_add(credit).ok_or(V16Error::CounterOverflow)?);
        lp.header.residual_received_atoms_total = V16PodU128::new(
            lp.header
                .residual_received_atoms_total
                .get()
                .checked_add(credit)
                .ok_or(V16Error::CounterOverflow)?,
        );
        Ok(credit)
    }

    fn initial_margin_requirement_for_abs_q(
        config: V16Config,
        abs_q: u128,
        price: u64,
    ) -> V16Result<u128> {
        let notional = risk_notional_ceil(abs_q, price)?;
        margin_requirement(
            notional,
            config.initial_margin_bps,
            config.min_nonzero_im_req,
        )
    }

    fn increased_initial_margin_principal(
        config: V16Config,
        old_abs_q: u128,
        new_abs_q: u128,
        price: u64,
    ) -> V16Result<u128> {
        if new_abs_q <= old_abs_q {
            return Ok(0);
        }
        let old_req = Self::initial_margin_requirement_for_abs_q(config, old_abs_q, price)?;
        let new_req = Self::initial_margin_requirement_for_abs_q(config, new_abs_q, price)?;
        Ok(new_req.saturating_sub(old_req))
    }

    fn transfer_trade_residual_reward_credit(
        &self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        trade_preflight: &TradePositionPreflightV16,
        asset_index: usize,
    ) -> V16Result<()> {
        let config = self.header.config.try_to_runtime_shape()?;
        let price = self.asset_state(asset_index)?.effective_price;
        let long_principal = Self::increased_initial_margin_principal(
            config,
            trade_preflight.long_old_abs_q,
            trade_preflight.long_new_abs_q,
            price,
        )?;
        let short_principal = Self::increased_initial_margin_principal(
            config,
            trade_preflight.short_old_abs_q,
            trade_preflight.short_new_abs_q,
            price,
        )?;
        if trade_preflight.long_new_abs_q > trade_preflight.long_old_abs_q {
            Self::transfer_account_residual_reward_credit(
                long_account,
                short_account,
                short_principal,
            )?;
        }
        if trade_preflight.short_new_abs_q > trade_preflight.short_old_abs_q {
            Self::transfer_account_residual_reward_credit(
                short_account,
                long_account,
                long_principal,
            )?;
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_transfer_account_residual_reward_credit(
        trader: &mut PortfolioV16ViewMut<'_>,
        lp: &mut PortfolioV16ViewMut<'_>,
        principal_atoms: u128,
    ) -> V16Result<u128> {
        Self::transfer_account_residual_reward_credit(trader, lp, principal_atoms)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_settle_account_b_chunk(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        endpoint_delta_budget: u128,
    ) -> V16Result<AccountBSettlementChunkV16> {
        self.settle_account_b_chunk(account, asset_index, endpoint_delta_budget)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_set_account_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
    ) -> V16Result<()> {
        self.set_account_pnl(account, new_pnl)
    }

    fn set_account_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
    ) -> V16Result<()> {
        self.set_account_pnl_inner(account, new_pnl, None, 0)
    }

    fn set_account_pnl_with_source(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
        source_domain: usize,
    ) -> V16Result<()> {
        self.domain_asset_side(source_domain)?;
        self.set_account_pnl_inner(account, new_pnl, Some(source_domain), 0)
    }

    fn set_account_pnl_after_source_claim_burn(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
        source_face_burn_num: u128,
    ) -> V16Result<()> {
        self.set_account_pnl_inner(account, new_pnl, None, source_face_burn_num)
    }

    fn set_account_pnl_after_domain_first_source_claim_burn(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
        source_domain: usize,
    ) -> V16Result<()> {
        let old_pos = account.header.pnl.get().max(0) as u128;
        let new_pos = new_pnl.max(0) as u128;
        let decrease = old_pos
            .checked_sub(new_pos)
            .ok_or(V16Error::InvalidConfig)?;
        let decrease_num = V16Core::bound_num_from_amount(decrease)?;
        self.burn_account_source_claim_bound_num_domain_first(
            account,
            source_domain,
            decrease_num,
        )?;
        self.set_account_pnl_after_source_claim_burn(account, new_pnl, decrease_num)
    }

    /// Grants source-attributed positive PnL to an account — the first-class
    /// API for crediting a source-backed claim (e.g. an external settlement
    /// feed). Live-mode only. The grant is pure notional attribution: no quote
    /// value moves; the account claim bound, the domain claim bound/exact, and
    /// the group junior aggregates move in lockstep through the same canonical
    /// setter every internal attribution uses, and the final shape validation
    /// re-checks the global junior-bound >= sum(domain claims) invariant.
    ///
    /// Converged from toly v16.8.11 (ce073dc): promotes the wrapper's host-side
    /// shadow to a proven engine surface (closes the "no engine API / no proof"
    /// bypass on the source-backed-claim creation path).
    pub fn add_account_source_positive_pnl_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
        amount: u128,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        if amount == 0 {
            return Ok(());
        }
        let delta = i128::try_from(amount).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = account
            .header
            .pnl
            .get()
            .checked_add(delta)
            .ok_or(V16Error::ArithmeticOverflow)?;
        self.set_account_pnl_with_source(account, new_pnl, domain)?;
        account.header.health_cert.valid = 0;
        self.validate_shape()?;
        account.validate_with_market(&self.as_view())
    }

    fn sync_unattributed_loss_lock(
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
    ) -> V16Result<()> {
        let was_locked = decode_bool(account.header.liquidation_lock)?;
        account.header.liquidation_lock = encode_bool(unattributed_loss_lock_after_pnl(
            was_locked,
            account.header.active_bitmap.map(V16PodU64::get),
            new_pnl,
        ));
        Ok(())
    }

    fn set_account_pnl_inner(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
        source_domain: Option<usize>,
        preburned_source_claim_num: u128,
    ) -> V16Result<()> {
        validate_non_min_i128(new_pnl)?;
        let old_pos = account.header.pnl.get().max(0) as u128;
        let new_pos = new_pnl.max(0) as u128;
        if new_pos >= old_pos {
            if preburned_source_claim_num != 0 {
                return Err(V16Error::InvalidConfig);
            }
            let increase = new_pos - old_pos;
            let increase_num = V16Core::bound_num_from_amount(increase)?;
            let increase_domain = if increase_num != 0 {
                if source_domain.is_none()
                    && decode_market_mode(self.header.mode)? == MarketModeV16::Live
                {
                    return Err(V16Error::InvalidLeg);
                }
                source_domain
            } else {
                None
            };
            self.header.pnl_pos_tot = V16PodU128::new(
                self.header
                    .pnl_pos_tot
                    .get()
                    .checked_add(increase)
                    .ok_or(V16Error::ArithmeticOverflow)?,
            );
            self.header.pnl_pos_bound_tot_num = V16PodU128::new(
                self.header
                    .pnl_pos_bound_tot_num
                    .get()
                    .checked_add(increase_num)
                    .ok_or(V16Error::ArithmeticOverflow)?,
            );
            if let Some(domain) = increase_domain {
                self.ensure_account_source_claim_market_id(account, domain)?;
                let source = account.source_domain_mut_or_insert(domain)?;
                source.source_claim_bound_num = V16PodU128::new(
                    source
                        .source_claim_bound_num
                        .get()
                        .checked_add(increase_num)
                        .ok_or(V16Error::ArithmeticOverflow)?,
                );
                let mut source_credit = self.source_credit_for_domain(domain)?;
                source_credit.positive_claim_bound_num = source_credit
                    .positive_claim_bound_num
                    .checked_add(increase_num)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                source_credit.exact_positive_claim_num = source_credit
                    .exact_positive_claim_num
                    .checked_add(increase_num)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                let (source_credit, next_risk_epoch) =
                    V16Core::prepare_source_credit_domain_recompute_for_epoch(
                        source_credit,
                        self.header.risk_epoch.get(),
                    )?;
                self.set_source_credit_for_domain(domain, source_credit)?;
                self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
            }
        } else {
            let decrease = old_pos - new_pos;
            let decrease_num = V16Core::bound_num_from_amount(decrease)?;
            let remaining_source_claim_burn = decrease_num
                .checked_sub(preburned_source_claim_num)
                .ok_or(V16Error::CounterUnderflow)?;
            self.burn_account_source_claim_bound_num(account, remaining_source_claim_burn)?;
            self.header.pnl_pos_tot = V16PodU128::new(
                self.header
                    .pnl_pos_tot
                    .get()
                    .checked_sub(decrease)
                    .ok_or(V16Error::CounterUnderflow)?,
            );
            let next_bound_num = self
                .header
                .pnl_pos_bound_tot_num
                .get()
                .saturating_sub(decrease_num);
            let exact_min_num = V16Core::bound_num_from_amount(self.header.pnl_pos_tot.get())?;
            self.header.pnl_pos_bound_tot_num = V16PodU128::new(next_bound_num.max(exact_min_num));
            self.header.pnl_matured_pos_tot = V16PodU128::new(
                self.header
                    .pnl_matured_pos_tot
                    .get()
                    .min(self.header.pnl_pos_tot.get()),
            );
        }
        self.header.pnl_pos_bound_tot = V16PodU128::new(V16Core::amount_from_bound_num(
            self.header.pnl_pos_bound_tot_num.get(),
        )?);

        let old_negative = account.header.pnl.get() < 0;
        let new_negative = new_pnl < 0;
        match (old_negative, new_negative) {
            (false, true) => {
                self.header.negative_pnl_account_count = V16PodU64::new(
                    self.header
                        .negative_pnl_account_count
                        .get()
                        .checked_add(1)
                        .ok_or(V16Error::CounterOverflow)?,
                );
            }
            (true, false) => {
                self.header.negative_pnl_account_count = V16PodU64::new(
                    self.header
                        .negative_pnl_account_count
                        .get()
                        .checked_sub(1)
                        .ok_or(V16Error::CounterUnderflow)?,
                );
            }
            _ => {}
        }
        Self::sync_unattributed_loss_lock(account, new_pnl)?;
        account.header.pnl = V16PodI128::new(new_pnl);
        account.header.health_cert.valid = 0;
        Ok(())
    }

    fn face_claim_to_burn_for_support(
        &self,
        effective_support: u128,
        residual: u128,
        junior_bound: u128,
    ) -> V16Result<u128> {
        if effective_support == 0 {
            return Ok(0);
        }
        if residual == 0 || junior_bound == 0 {
            return Err(V16Error::LockActive);
        }
        if residual >= junior_bound {
            return Ok(effective_support);
        }
        checked_mul_div_ceil_u256(
            U256::from_u128(effective_support),
            U256::from_u128(junior_bound),
            U256::from_u128(residual),
        )
        .and_then(|v| v.try_into_u128())
        .ok_or(V16Error::ArithmeticOverflow)
    }

    fn apply_haircut_bounded_close_loss_to_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        loss_abs: u128,
    ) -> V16Result<SupportLossApplicationV16> {
        if loss_abs == 0 {
            return Ok(SupportLossApplicationV16 {
                support_consumed: 0,
                junior_face_burned: 0,
            });
        }
        let old_positive_face = account.header.pnl.get().max(0) as u128;
        if old_positive_face == 0 {
            let loss_i128 = i128::try_from(loss_abs).map_err(|_| V16Error::ArithmeticOverflow)?;
            let new_pnl = account
                .header
                .pnl
                .get()
                .checked_sub(loss_i128)
                .ok_or(V16Error::ArithmeticOverflow)?;
            self.set_account_pnl(account, new_pnl)?;
            return Ok(SupportLossApplicationV16 {
                support_consumed: 0,
                junior_face_burned: 0,
            });
        }
        let has_source_claims = Self::account_has_source_claims(&account.as_view())?;
        let (support_consumed, support_face_burned, preburned_source_claim_num) =
            if has_source_claims {
                let source_support_limit = loss_abs.min(old_positive_face);
                let (consumption, preburned_source_claim_num, support_consumed) = self
                    .consume_validated_account_source_credit_not_atomic(
                        account,
                        source_support_limit,
                        true,
                        false,
                    )?;
                (
                    support_consumed,
                    consumption.face_burn.min(old_positive_face),
                    preburned_source_claim_num,
                )
            } else {
                let effective_available =
                    if decode_market_mode(self.header.mode)? == MarketModeV16::Live {
                        0
                    } else {
                        self.haircut_effective_support(
                            old_positive_face,
                            self.residual(),
                            self.junior_claim_bound(),
                        )?
                    };
                let support_consumed = effective_available.min(loss_abs);
                let junior_face_burned = if support_consumed == 0 {
                    0
                } else {
                    self.face_claim_to_burn_for_support(
                        support_consumed,
                        self.residual(),
                        self.junior_claim_bound(),
                    )?
                };
                (support_consumed, junior_face_burned, 0)
            };
        let remaining_loss = loss_abs
            .checked_sub(support_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        // PROPORTIONAL: burn only the support-matched face, not the whole positive
        // face, on an under-supported loss. Burning it all double-charged the account
        // (accumulated gain destroyed AND the loss still taken from capital).
        // Upstream had `if remaining_loss != 0 { junior_face_burned =
        // old_positive_face; }` here at 592d538c; this fork omitted it from the start
        // (#172 site 2) and upstream deleted it in 07208fb1, which also moved the
        // arithmetic into the kernel below and redefined the reported face burn as
        // the face that actually vanished (support-matched burn PLUS the retained
        // face the uncovered tail ate), not just the support-matched part.
        let (new_pnl, junior_face_burned) = V16Core::kernel_settle_positive_face_after_support(
            old_positive_face,
            support_face_burned,
            remaining_loss,
        )?;
        account.header.reserved_pnl = V16PodU128::new(
            account
                .header
                .reserved_pnl
                .get()
                .min(new_pnl.max(0) as u128),
        );
        self.set_account_pnl_after_source_claim_burn(account, new_pnl, preburned_source_claim_num)?;
        Ok(SupportLossApplicationV16 {
            support_consumed,
            junior_face_burned,
        })
    }

    fn apply_signed_kf_delta_to_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        delta: i128,
        source_domain: Option<usize>,
    ) -> V16Result<SupportLossApplicationV16> {
        validate_non_min_i128(delta)?;
        if delta == 0 {
            return Ok(SupportLossApplicationV16 {
                support_consumed: 0,
                junior_face_burned: 0,
            });
        }
        if delta < 0 {
            return self.apply_haircut_bounded_close_loss_to_pnl(account, delta.unsigned_abs());
        }
        if account.header.pnl.get() >= 0 {
            if source_domain.is_none()
                && decode_market_mode(self.header.mode)? == MarketModeV16::Live
            {
                return Err(V16Error::InvalidLeg);
            }
            let new_pnl = account
                .header
                .pnl
                .get()
                .checked_add(delta)
                .ok_or(V16Error::ArithmeticOverflow)?;
            if let Some(domain) = source_domain {
                self.set_account_pnl_with_source(account, new_pnl, domain)?;
            } else {
                self.set_account_pnl(account, new_pnl)?;
            }
            return Ok(SupportLossApplicationV16 {
                support_consumed: 0,
                junior_face_burned: 0,
            });
        }

        let old_loss = account.header.pnl.get().unsigned_abs();
        let new_face_support = delta as u128;
        let (effective_available, source_support_domain) = if let Some(domain) = source_domain {
            (
                self.source_domain_realizable_support_for_face(domain, new_face_support)?,
                Some(domain),
            )
        } else if decode_market_mode(self.header.mode)? == MarketModeV16::Live {
            (0, None)
        } else {
            let residual = self.residual();
            let junior_bound = self
                .junior_claim_bound()
                .checked_add(new_face_support)
                .ok_or(V16Error::ArithmeticOverflow)?;
            (
                self.haircut_effective_support(new_face_support, residual, junior_bound)?,
                None,
            )
        };
        let support_consumed = effective_available.min(old_loss);
        let remaining_loss = old_loss
            .checked_sub(support_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let mut junior_face_burned = if let Some(domain) = source_support_domain {
            self.consume_source_domain_credit_for_effective_not_atomic(domain, support_consumed)?
                .face_burn
                .min(new_face_support)
        } else if support_consumed == 0 {
            0
        } else {
            let residual = self.residual();
            let junior_bound = self
                .junior_claim_bound()
                .checked_add(new_face_support)
                .ok_or(V16Error::ArithmeticOverflow)?;
            self.face_claim_to_burn_for_support(support_consumed, residual, junior_bound)?
        };
        if (source_support_domain.is_none()
            && decode_market_mode(self.header.mode)? == MarketModeV16::Live)
            || remaining_loss != 0
        {
            // Burn only the part of the gain EXCEEDING the outstanding loss. The part
            // that merely NETS against the loss is the counterparty's loss being
            // realized against a debt already owed, so it needs no source backing.
            // Burning it made an underwater account permanently unrecoverable.
            junior_face_burned = new_face_support.saturating_sub(old_loss);
        }
        if junior_face_burned > new_face_support {
            return Err(V16Error::ArithmeticOverflow);
        }
        let retained_face = new_face_support
            .checked_sub(junior_face_burned)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let retained_i128 =
            i128::try_from(retained_face).map_err(|_| V16Error::ArithmeticOverflow)?;
        let remaining_i128 =
            i128::try_from(remaining_loss).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = retained_i128
            .checked_sub(remaining_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if new_pnl > 0 {
            if let Some(domain) = source_domain {
                self.set_account_pnl_with_source(account, new_pnl, domain)?;
            } else {
                self.set_account_pnl(account, new_pnl)?;
            }
        } else {
            self.set_account_pnl(account, new_pnl)?;
        }
        Ok(SupportLossApplicationV16 {
            support_consumed,
            junior_face_burned,
        })
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_apply_signed_kf_delta_to_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        delta: i128,
        source_domain: Option<usize>,
    ) -> V16Result<(u128, u128)> {
        let out = self.apply_signed_kf_delta_to_pnl(account, delta, source_domain)?;
        Ok((out.support_consumed, out.junior_face_burned))
    }

    #[cfg(kani)]
    pub fn kani_account_unliened_source_realizable_support(
        &self,
        account: &PortfolioV16View<'_>,
        face_claim: u128,
    ) -> V16Result<u128> {
        self.account_unliened_source_realizable_support(account, face_claim)
    }

    fn reserve_new_capital_backed_loss_for_source_domain_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
        negative_before: u128,
        negative_after: u128,
    ) -> V16Result<()> {
        self.domain_asset_side(domain)?;
        let new_negative_loss = negative_after.saturating_sub(negative_before);
        if new_negative_loss == 0 {
            return Ok(());
        }
        let capital_not_already_encumbered =
            account.header.capital.get().saturating_sub(negative_before);
        let backing = new_negative_loss.min(capital_not_already_encumbered);
        if backing == 0 {
            return Ok(());
        }
        let backing_num = backing
            .checked_mul(BOUND_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let vault_before = self.header.vault.get();
        account.header.capital = V16PodU128::new(
            account
                .header
                .capital
                .get()
                .checked_sub(backing)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        self.header.c_tot = V16PodU128::new(
            self.header
                .c_tot
                .get()
                .checked_sub(backing)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        let backing_i128 = i128::try_from(backing).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = account
            .header
            .pnl
            .get()
            .checked_add(backing_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        self.set_account_pnl(account, new_pnl)?;
        TokenValueFlowProofV16::account_capital_to_realized_loss(
            backing,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        let terminal_impaired = decode_market_mode(self.header.mode)? == MarketModeV16::Resolved
            && self.backing_bucket_for_domain(domain)?.status == BackingBucketStatusV16::Impaired;
        if terminal_impaired {
            // Once the provider bucket has defaulted, newly crystallized loss is
            // terminal junior support, not recoverable provider principal.
            self.credit_post_snapshot_residual_not_atomic(backing)?;
        } else {
            let expiry_slot = self.fresh_counterparty_backing_expiry_slot(domain)?;
            self.add_fresh_counterparty_backing_unchecked(domain, backing_num, expiry_slot)?;
        }
        Self::record_account_residual_crystallized_loss(account, backing)?;
        account.header.health_cert.valid = 0;
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_reserve_new_capital_backed_loss_for_source_domain_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
        negative_before: u128,
        negative_after: u128,
    ) -> V16Result<()> {
        self.reserve_new_capital_backed_loss_for_source_domain_not_atomic(
            account,
            domain,
            negative_before,
            negative_after,
        )
    }

    fn kf_target_for_leg(
        &self,
        asset_index: usize,
        leg: PortfolioLegV16,
    ) -> V16Result<(i128, i128)> {
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
        {
            return Err(V16Error::InvalidLeg);
        }
        let asset = self.markets[asset_index].engine.asset.try_to_runtime()?;
        Self::kf_target_for_leg_from_asset(asset, leg)
    }

    fn kf_target_for_leg_from_asset(
        asset: AssetStateV16,
        leg: PortfolioLegV16,
    ) -> V16Result<(i128, i128)> {
        let (current_k, current_f, epoch_start_k, epoch_start_f, side_epoch, mode) = match leg.side
        {
            SideV16::Long => (
                asset.k_long,
                asset.f_long_num,
                asset.k_epoch_start_long,
                asset.f_epoch_start_long_num,
                asset.epoch_long,
                asset.mode_long,
            ),
            SideV16::Short => (
                asset.k_short,
                asset.f_short_num,
                asset.k_epoch_start_short,
                asset.f_epoch_start_short_num,
                asset.epoch_short,
                asset.mode_short,
            ),
        };
        if leg.epoch_snap == side_epoch {
            Ok((current_k, current_f))
        } else if mode == SideModeV16::ResetPending
            && leg.epoch_snap.checked_add(1) == Some(side_epoch)
        {
            Ok((epoch_start_k, epoch_start_f))
        } else {
            Err(V16Error::InvalidLeg)
        }
    }

    #[inline]
    fn kf_epoch_for_leg_from_asset(asset: AssetStateV16, leg: PortfolioLegV16) -> u64 {
        match leg.side {
            SideV16::Long => asset.kf_epoch_long,
            SideV16::Short => asset.kf_epoch_short,
        }
    }

    #[inline]
    fn leg_kf_epoch_is_current(asset: AssetStateV16, leg: PortfolioLegV16) -> bool {
        leg.kf_epoch_snap == Self::kf_epoch_for_leg_from_asset(asset, leg)
    }

    fn b_target_for_leg(&self, asset_index: usize, leg: PortfolioLegV16) -> V16Result<u128> {
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
        {
            return Err(V16Error::InvalidLeg);
        }
        let asset = self.markets[asset_index].engine.asset.try_to_runtime()?;
        Self::b_target_for_leg_from_asset(asset, leg)
    }

    fn b_target_for_leg_from_asset(asset: AssetStateV16, leg: PortfolioLegV16) -> V16Result<u128> {
        let (current_b, epoch_start_b, side_epoch, mode) = match leg.side {
            SideV16::Long => (
                asset.b_long_num,
                asset.b_epoch_start_long_num,
                asset.epoch_long,
                asset.mode_long,
            ),
            SideV16::Short => (
                asset.b_short_num,
                asset.b_epoch_start_short_num,
                asset.epoch_short,
                asset.mode_short,
            ),
        };
        if leg.b_epoch_snap == side_epoch {
            Ok(current_b)
        } else if mode == SideModeV16::ResetPending
            && leg.b_epoch_snap.checked_add(1) == Some(side_epoch)
        {
            Ok(epoch_start_b)
        } else {
            Err(V16Error::InvalidLeg)
        }
    }

    #[inline(always)]
    fn leg_kf_delta_components_for_settlement_from_asset(
        asset: AssetStateV16,
        leg: PortfolioLegV16,
    ) -> V16Result<(i128, i128, i128, i128, i128)> {
        let (k_now, f_now) = Self::kf_target_for_leg_from_asset(asset, leg)?;
        let den = leg
            .a_basis
            .checked_mul(POS_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let k_delta = scaled_adl_delta_fast(
            leg.basis_pos_q.unsigned_abs(),
            leg.a_basis,
            leg.k_snap,
            k_now,
        )
        .unwrap_or_else(|| {
            wide_signed_mul_div_floor_from_k_pair(
                leg.basis_pos_q.unsigned_abs(),
                leg.k_snap,
                k_now,
                den,
            )
        });
        let f_delta = scaled_adl_delta_fast(
            leg.basis_pos_q.unsigned_abs(),
            leg.a_basis,
            leg.f_snap,
            f_now,
        )
        .unwrap_or_else(|| {
            wide_signed_mul_div_floor_from_k_pair(
                leg.basis_pos_q.unsigned_abs(),
                leg.f_snap,
                f_now,
                den,
            )
        });
        let net = k_delta
            .checked_add(f_delta)
            .ok_or(V16Error::ArithmeticOverflow)?;
        validate_non_min_i128(net)?;
        Ok((k_now, f_now, k_delta, f_delta, net))
    }

    #[cfg(kani)]
    #[inline(always)]
    fn leg_kf_delta_for_settlement_from_asset(
        asset: AssetStateV16,
        leg: PortfolioLegV16,
    ) -> V16Result<(i128, i128, i128)> {
        let (k_now, f_now, _k_delta, _f_delta, net) =
            Self::leg_kf_delta_components_for_settlement_from_asset(asset, leg)?;
        Ok((k_now, f_now, net))
    }

    #[cfg(kani)]
    #[inline(always)]
    fn leg_kf_delta_for_settlement(&self, leg: PortfolioLegV16) -> V16Result<(i128, i128, i128)> {
        let asset = self.asset_state(leg.asset_index as usize)?;
        Self::leg_kf_delta_for_settlement_from_asset(asset, leg)
    }

    #[cfg(kani)]
    pub fn kani_leg_kf_delta_for_settlement(
        &self,
        leg: PortfolioLegV16,
    ) -> V16Result<(i128, i128, i128)> {
        self.leg_kf_delta_for_settlement(leg)
    }

    fn prepare_account_kf_settlement_entry(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        leg_slot: usize,
        normalize_exhausted_sides: bool,
    ) -> V16Result<(u64, AccountKfSettlementPreparedV16)> {
        if leg_slot >= V16_MAX_PORTFOLIO_ASSETS_N {
            return Err(V16Error::InvalidLeg);
        }
        let leg = account.header.legs[leg_slot].try_to_runtime()?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let asset_index = leg.asset_index as usize;
        let mut asset = self.asset_state(asset_index)?;
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
            || asset.market_id == 0
        {
            return Err(V16Error::InvalidLeg);
        }
        if normalize_exhausted_sides
            && Self::leg_has_exhausted_effective_oi(asset, leg)
            && !account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual()
            && !self.has_pending_domain_loss_barrier(asset_index, leg.side)?
        {
            self.begin_full_drain_reset_inner(asset_index, leg.side)?;
            asset = self.asset_state(asset_index)?;
        }
        let (k_now, f_now, _k_delta, f_delta, net) =
            Self::leg_kf_delta_components_for_settlement_from_asset(asset, leg)?;
        let source_side = if net > 0 {
            opposite_side(leg.side)
        } else {
            leg.side
        };
        let source_domain = self.insurance_domain_index(asset_index, source_side)?;
        let entry = account_kf_settlement_plan_key(u8::from(net >= 0), source_domain, leg_slot)?;
        Ok((
            entry,
            AccountKfSettlementPreparedV16 {
                k_now,
                f_now,
                f_delta,
                net,
            },
        ))
    }

    fn apply_account_kf_settlement_entry(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        entry: u64,
        prepared: AccountKfSettlementPreparedV16,
    ) -> V16Result<()> {
        let (phase, source_domain, leg_slot) = decode_account_kf_settlement_plan_key(entry)?;
        let mut leg = account.header.legs[leg_slot].try_to_runtime()?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let asset_index = leg.asset_index as usize;
        let mut asset = self.asset_state(asset_index)?;
        let (live_k_now, live_f_now) = Self::kf_target_for_leg_from_asset(asset, leg)?;
        let actual_source_side = if prepared.net > 0 {
            opposite_side(leg.side)
        } else {
            leg.side
        };
        if live_k_now != prepared.k_now
            || live_f_now != prepared.f_now
            || phase != u8::from(prepared.net >= 0)
            || source_domain != self.insurance_domain_index(asset_index, actual_source_side)?
        {
            return Err(V16Error::InvalidLeg);
        }
        if prepared.net != 0 {
            if prepared.net > 0 {
                self.apply_signed_kf_delta_to_pnl(account, prepared.net, Some(source_domain))?;
            } else {
                let negative_before = account.header.pnl.get().min(0).unsigned_abs();
                self.apply_signed_kf_delta_to_pnl(account, prepared.net, None)?;
                let negative_after = account.header.pnl.get().min(0).unsigned_abs();
                self.reserve_new_capital_backed_loss_for_source_domain_not_atomic(
                    account,
                    source_domain,
                    negative_before,
                    negative_after,
                )?;
            }
        }
        Self::record_account_funding_flow(account, leg.side, prepared.f_delta)?;
        let (settled_asset, kf_epoch_snap) =
            V16Core::kernel_settle_kf_stale_cohort(asset, leg.side, leg.kf_epoch_snap)?;
        asset = settled_asset;
        leg.k_snap = prepared.k_now;
        leg.f_snap = prepared.f_now;
        leg.kf_epoch_snap = kf_epoch_snap;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&leg);
        account.header.health_cert.valid = 0;
        self.set_asset_state(asset_index, asset)?;
        self.header.loss_stale_active = encode_bool(asset_is_loss_stale_at_slot(
            asset,
            self.header.current_slot.get(),
        ));
        Ok(())
    }

    fn settle_account_kf_effects_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        normalize_exhausted_sides: bool,
    ) -> V16Result<()> {
        // The composing refresh/crank paths validate bitmap-to-leg consistency. Flat
        // accounts have no K/F work, and skipping a second full leg scan preserves
        // headroom for their bounded source-domain admission checks.
        let active_bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let active_leg_count = active_bitmap_count_ones(active_bitmap);
        if active_leg_count == 0 {
            return Ok(());
        }
        if active_leg_count == 1 {
            let mut slot = 0usize;
            while slot < V16_MAX_PORTFOLIO_ASSETS_N && !active_bitmap_get(active_bitmap, slot) {
                slot += 1;
            }
            if slot == V16_MAX_PORTFOLIO_ASSETS_N {
                return Err(V16Error::InvalidLeg);
            }
            let (entry, prepared) =
                self.prepare_account_kf_settlement_entry(account, slot, normalize_exhausted_sides)?;
            return self.apply_account_kf_settlement_entry(account, entry, prepared);
        }
        let mut plan = [None; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut prepared_by_slot =
            [AccountKfSettlementPreparedV16::default(); V16_MAX_PORTFOLIO_ASSETS_N];
        let mut plan_len = 0usize;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if !leg.active {
                slot += 1;
                continue;
            }
            let (entry, prepared) =
                self.prepare_account_kf_settlement_entry(account, slot, normalize_exhausted_sides)?;
            prepared_by_slot[slot] = prepared;
            plan_len = insert_account_kf_settlement_plan_entry(&mut plan, plan_len, entry)?;
            slot += 1;
        }

        let mut index = 0usize;
        while index < plan_len {
            let entry = plan[index].ok_or(V16Error::InvalidLeg)?;
            let leg_slot = (entry & 0xf) as usize;
            if leg_slot >= V16_MAX_PORTFOLIO_ASSETS_N {
                return Err(V16Error::InvalidLeg);
            }
            self.apply_account_kf_settlement_entry(account, entry, prepared_by_slot[leg_slot])?;
            index += 1;
        }
        Ok(())
    }

    fn clear_account_stale(&mut self, account: &mut PortfolioV16ViewMut<'_>) -> V16Result<()> {
        if decode_bool(account.header.stale_state)? {
            account.header.stale_state = 0;
            self.header.stale_certificate_count = V16PodU64::new(
                self.header
                    .stale_certificate_count
                    .get()
                    .checked_sub(1)
                    .ok_or(V16Error::CounterUnderflow)?,
            );
        }
        Ok(())
    }

    fn compute_account_health_cert_with_price_override(
        &self,
        account: &PortfolioV16View<'_>,
        require_b_current: bool,
        price_override: Option<(usize, u64)>,
    ) -> V16Result<HealthCertV16> {
        let config = self.header.config.try_to_runtime_shape()?;
        let mut initial_req = 0u128;
        let mut maintenance_req = 0u128;
        let mut worst_case_loss = 0u128;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if !leg.active {
                slot += 1;
                continue;
            }
            let asset_index = leg.asset_index as usize;
            if require_b_current && self.b_target_for_leg(asset_index, leg)? > leg.b_snap {
                return Err(V16Error::BStale);
            }
            let asset = self.asset_state(asset_index)?;
            let effective_abs_q = V16Core::effective_abs_quantity_for_leg(asset, leg)?;
            let price = if let Some((override_asset, override_price)) = price_override {
                if override_asset == asset_index {
                    override_price
                } else {
                    asset.effective_price
                }
            } else {
                asset.effective_price
            };
            let risk_notional = risk_notional_ceil(effective_abs_q, price)?;
            let target_lag_penalty = V16Core::target_effective_lag_loss_penalty(
                effective_abs_q,
                leg.side,
                price,
                asset.raw_oracle_target_price,
            )?;
            let (leg_initial, leg_maintenance, leg_worst_case_loss) =
                V16Core::health_requirements_from_notional_and_target_lag(
                    config,
                    risk_notional,
                    target_lag_penalty,
                )?;
            initial_req = initial_req
                .checked_add(leg_initial)
                .ok_or(V16Error::ArithmeticOverflow)?;
            maintenance_req = maintenance_req
                .checked_add(leg_maintenance)
                .ok_or(V16Error::ArithmeticOverflow)?;
            worst_case_loss = worst_case_loss
                .checked_add(leg_worst_case_loss)
                .ok_or(V16Error::ArithmeticOverflow)?;
            slot += 1;
        }
        let equity = self.account_haircut_equity(account)?;
        Ok(HealthCertV16 {
            certified_equity: equity,
            certified_initial_req: initial_req,
            certified_maintenance_req: maintenance_req,
            certified_liq_deficit: if equity < 0 {
                equity.unsigned_abs()
            } else {
                maintenance_req.saturating_sub(equity as u128)
            },
            certified_worst_case_loss: worst_case_loss,
            cert_oracle_epoch: self.header.oracle_epoch.get(),
            cert_funding_epoch: self.header.funding_epoch.get(),
            cert_risk_epoch: self.header.risk_epoch.get(),
            cert_asset_set_epoch: self.header.asset_set_epoch.get(),
            active_bitmap_at_cert: account.header.active_bitmap.map(V16PodU64::get),
            valid: true,
        })
    }

    pub fn full_account_refresh_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<HealthCertV16> {
        match self.refresh_account_and_certify_not_atomic(account, None, 0, false)? {
            AccountRefreshCertOutcomeV16::Certified(cert) => Ok(cert),
            AccountRefreshCertOutcomeV16::BChunk(_) => Err(V16Error::BStale),
            AccountRefreshCertOutcomeV16::SourceBackingExpired(_) => Err(V16Error::Stale),
        }
    }

    fn refresh_account_and_certify_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        price_override: Option<(usize, u64)>,
        b_loss_atom_budget: u128,
        allow_b_chunk: bool,
    ) -> V16Result<AccountRefreshCertOutcomeV16> {
        self.validate_account_scalar_preflight(&account.as_view())?;
        let source_claim_sum_num = if account.header.source_domains[0].is_sparse_tail_default() {
            0
        } else {
            account
                .as_view()
                .validate_source_credit_shape_with_market(&self.as_view())?;
            Self::account_source_claim_bound_sum_num(&account.as_view())?
        };
        if source_claim_sum_num != 0 {
            V16Core::validate_positive_pnl_source_attribution(
                account.header.pnl.get(),
                source_claim_sum_num,
            )?;
        }
        // A source-backed winner can remain Live past the backing bucket's expiry.
        // The permissionless path commits exactly one canonical expiry transition
        // per call, then returns before valuation. Repeated cranks drain the
        // bounded domain set without an O(source-domains) CU cliff.
        // (upstream c09d4575)
        if allow_b_chunk {
            if let Some(domain) =
                self.expire_first_lapsed_source_backing_for_account_not_atomic(&account.as_view())?
            {
                return Ok(AccountRefreshCertOutcomeV16::SourceBackingExpired(domain));
            }
        }
        if decode_bool(account.header.b_stale_state)? && !allow_b_chunk {
            return Err(V16Error::BStale);
        }
        self.settle_account_kf_effects_not_atomic(account, true)?;
        let config = self.header.config.try_to_runtime_shape()?;
        let mut initial_req = 0u128;
        let mut maintenance_req = 0u128;
        let mut worst_case_loss = 0u128;
        let active_leg_cap = config.max_portfolio_assets as usize;
        let configured_assets = config.max_market_slots as usize;
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let mut seen_assets = [u32::MAX; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut seen_asset_count = 0usize;
        let mut reset_obligation_cleared = false;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            let bit = active_bitmap_get(bitmap, slot);
            if slot >= active_leg_cap {
                if bit || !leg.is_empty() {
                    return Err(V16Error::HiddenLeg);
                }
                slot += 1;
                continue;
            }
            if bit != leg.active {
                return Err(V16Error::HiddenLeg);
            }
            if !leg.active {
                if !leg.is_empty() {
                    return Err(V16Error::HiddenLeg);
                }
                slot += 1;
                continue;
            }
            validate_active_leg(leg)?;
            let asset_index = leg.asset_index as usize;
            if asset_index >= configured_assets || asset_index >= self.markets.len() {
                return Err(V16Error::HiddenLeg);
            }
            let asset = self.markets[asset_index].engine.asset.try_to_runtime()?;
            if leg.market_id != asset.market_id
                || !matches!(
                    asset.lifecycle,
                    AssetLifecycleV16::Active
                        | AssetLifecycleV16::DrainOnly
                        | AssetLifecycleV16::Recovery
                )
                || !leg_snapshots_bound_to_asset_side(asset, leg)
            {
                return Err(V16Error::HiddenLeg);
            }
            let mut seen = 0usize;
            while seen < seen_asset_count {
                if seen_assets[seen] == leg.asset_index {
                    return Err(V16Error::HiddenLeg);
                }
                seen += 1;
            }
            seen_assets[seen_asset_count] = leg.asset_index;
            seen_asset_count += 1;
            let mut refreshed = account.header.legs[slot].try_to_runtime()?;
            let target = Self::b_target_for_leg_from_asset(asset, refreshed)?;
            if target > refreshed.b_snap {
                self.mark_leg_b_stale(account, asset_index)?;
                if allow_b_chunk {
                    let chunk =
                        self.settle_account_b_chunk(account, asset_index, b_loss_atom_budget)?;
                    if chunk.remaining_after != 0 {
                        return Ok(AccountRefreshCertOutcomeV16::BChunk(chunk));
                    }
                    refreshed = account.header.legs[slot].try_to_runtime()?;
                } else {
                    return Err(V16Error::BStale);
                }
            }
            if refreshed.b_stale {
                if allow_b_chunk {
                    return Ok(AccountRefreshCertOutcomeV16::BChunk(
                        AccountBSettlementChunkV16 {
                            delta_b: 0,
                            loss: 0,
                            new_remainder: refreshed.b_rem,
                            remaining_after: target.saturating_sub(refreshed.b_snap),
                        },
                    ));
                }
                return Err(V16Error::BStale);
            }
            // A prior-reset leg no longer owns effective OI. This includes a
            // legacy exhausted residue migrated into a reset above.
            let should_clear_reset = if reset_obligation_cleared
                || !Self::leg_is_prior_reset_obligation(asset, refreshed)
            {
                false
            } else {
                V16Core::kernel_should_clear_prior_reset_obligation(
                    false,
                    true,
                    account
                        .header
                        .close_progress
                        .try_to_runtime()?
                        .has_pending_residual(),
                )
            };
            if should_clear_reset {
                self.clear_leg(account, asset_index)?;
                reset_obligation_cleared = true;
                slot += 1;
                continue;
            }
            let price = if let Some((override_asset, override_price)) = price_override {
                if override_asset == asset_index {
                    override_price
                } else {
                    self.markets[asset_index].engine.asset.effective_price.get()
                }
            } else {
                self.markets[asset_index].engine.asset.effective_price.get()
            };
            let effective_abs_q = V16Core::effective_abs_quantity_for_leg(asset, refreshed)?;
            let risk_notional = risk_notional_ceil(effective_abs_q, price)?;
            let target_lag_penalty = V16Core::target_effective_lag_loss_penalty(
                effective_abs_q,
                refreshed.side,
                price,
                asset.raw_oracle_target_price,
            )?;
            let (leg_initial, leg_maintenance, leg_worst_case_loss) =
                V16Core::health_requirements_from_notional_and_target_lag(
                    config,
                    risk_notional,
                    target_lag_penalty,
                )?;
            initial_req = initial_req
                .checked_add(leg_initial)
                .ok_or(V16Error::ArithmeticOverflow)?;
            maintenance_req = maintenance_req
                .checked_add(leg_maintenance)
                .ok_or(V16Error::ArithmeticOverflow)?;
            worst_case_loss = worst_case_loss
                .checked_add(leg_worst_case_loss)
                .ok_or(V16Error::ArithmeticOverflow)?;
            slot += 1;
        }
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        // FIX-1b: the reserve path (reserve_new_capital_backed_loss_for_source_domain_not_atomic)
        // can zero the PnL before settle_negative_pnl_from_principal_core_not_atomic sees it,
        // causing the settle to return early and bypass the try_clear at line 13248.  Call
        // try_clear here unconditionally so a FeeSweep/Refresh also clears the hlock when all
        // five health conditions are satisfied.
        self.try_clear_bankruptcy_hlock_if_healthy()?;
        self.collect_account_backing_utilization_fees_not_atomic(account)?;
        if decode_bool(account.header.b_stale_state)? {
            return Err(V16Error::BStale);
        }
        if decode_bool(account.header.stale_state)? {
            self.clear_account_stale(account)?;
        }
        let equity = self.account_haircut_equity(&account.as_view())?;
        let cert = HealthCertV16 {
            certified_equity: equity,
            certified_initial_req: initial_req,
            certified_maintenance_req: maintenance_req,
            certified_liq_deficit: if equity < 0 {
                equity.unsigned_abs()
            } else {
                maintenance_req.saturating_sub(equity as u128)
            },
            certified_worst_case_loss: worst_case_loss,
            cert_oracle_epoch: self.header.oracle_epoch.get(),
            cert_funding_epoch: self.header.funding_epoch.get(),
            cert_risk_epoch: self.header.risk_epoch.get(),
            cert_asset_set_epoch: self.header.asset_set_epoch.get(),
            active_bitmap_at_cert: account.header.active_bitmap.map(V16PodU64::get),
            valid: true,
        };
        account.header.health_cert = HealthCertV16Account::from_runtime(&cert);
        self.validate_account_audit_scan(&account.as_view())?;
        self.validate_shape_audit_scan()?;
        Ok(AccountRefreshCertOutcomeV16::Certified(cert))
    }

    fn has_b_stale_leg(account: &PortfolioV16View<'_>) -> V16Result<bool> {
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active && leg.b_stale {
                return Ok(true);
            }
            slot += 1;
        }
        Ok(false)
    }

    fn mark_account_b_stale(&mut self, account: &mut PortfolioV16ViewMut<'_>) -> V16Result<()> {
        if !decode_bool(account.header.b_stale_state)? {
            account.header.b_stale_state = 1;
            account.header.health_cert.valid = 0;
            self.header.b_stale_account_count = V16PodU64::new(
                self.header
                    .b_stale_account_count
                    .get()
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?,
            );
        }
        Ok(())
    }

    fn clear_account_b_stale(&mut self, account: &mut PortfolioV16ViewMut<'_>) -> V16Result<()> {
        if Self::has_b_stale_leg(&account.as_view())? {
            return Err(V16Error::BStale);
        }
        if decode_bool(account.header.b_stale_state)? {
            account.header.b_stale_state = 0;
            self.header.b_stale_account_count = V16PodU64::new(
                self.header
                    .b_stale_account_count
                    .get()
                    .checked_sub(1)
                    .ok_or(V16Error::CounterUnderflow)?,
            );
        }
        Ok(())
    }

    fn collect_account_backing_utilization_fees_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        let mut total_charged = 0u128;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.header.source_domains[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if !source.is_occupied() {
                slot += 1;
                continue;
            }
            let d = source.domain.get() as usize;
            total_charged = total_charged
                .checked_add(
                    self.collect_account_backing_utilization_fee_for_domain_not_atomic(account, d)?,
                )
                .ok_or(V16Error::ArithmeticOverflow)?;
            slot += 1;
        }
        account.compact_source_domains();
        self.validate_account_audit_scan(&account.as_view())?;
        self.validate_shape_audit_scan()?;
        Ok(total_charged)
    }

    fn collect_account_backing_utilization_fee_for_domain_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
    ) -> V16Result<u128> {
        self.domain_asset_side(domain)?;
        let slot = match account.source_domain_slot(domain)? {
            Some(slot) => slot,
            None => return Ok(0),
        };
        let lien_backing_num = account.header.source_domains[slot]
            .source_lien_counterparty_backing_num
            .get();
        if lien_backing_num == 0 {
            account.header.source_domains[slot].source_lien_fee_last_slot = V16PodU64::new(0);
            account.reset_source_domain_slot_if_empty(slot);
            return Ok(0);
        }
        let last_slot = account.header.source_domains[slot]
            .source_lien_fee_last_slot
            .get();
        if last_slot == 0 {
            account.header.source_domains[slot].source_lien_fee_last_slot =
                V16PodU64::new(self.header.current_slot.get());
            return Ok(0);
        }
        let mut bucket = self.backing_bucket_for_domain(domain)?;
        // Rent stops at the bucket's own expiry: a foreign-expired lien must not
        // keep accruing utilization fee for the period after the backing lapsed.
        let fee_through_slot = if bucket.expiry_slot == 0 {
            self.header.current_slot.get()
        } else {
            self.header.current_slot.get().min(bucket.expiry_slot)
        };
        let fee = V16Core::backing_utilization_fee_quote_atoms_for_lien(
            self.header.config.try_to_runtime_shape()?,
            self.source_credit_for_domain(domain)?,
            lien_backing_num,
            last_slot,
            fee_through_slot,
        )?;
        // Carry the floored-away fractional accrual forward: when the rent quote
        // floors to zero this interval, do NOT advance the fee cursor, so a later
        // collection over a longer interval crosses >= 1 atom (no free lien). The
        // lien_backing_num == 0 and last_slot == 0 cases were handled above, so a
        // stuck cursor here only ever means real, still-accruing rent.
        // (upstream f7ad3ee9)
        if fee == 0 {
            return Ok(0);
        }
        account.header.source_domains[slot].source_lien_fee_last_slot =
            V16PodU64::new(fee_through_slot);
        let (charged, next_capital, next_c_tot, next_earnings) =
            apply_backing_utilization_fee_charge(
                account.header.capital.get(),
                self.header.c_tot.get(),
                bucket.utilization_fee_earnings,
                account.header.pnl.get(),
                fee,
            )?;
        if charged == 0 {
            return Ok(0);
        }
        account.header.capital = V16PodU128::new(next_capital);
        self.header.c_tot = V16PodU128::new(next_c_tot);
        bucket.utilization_fee_earnings = next_earnings;
        self.set_backing_bucket_for_domain(domain, bucket)?;
        // Genesis counter: this fee was charged while the domain's backing lien was live and at risk
        // (lien_backing_num > 0 above), so it is capital-at-risk fee revenue for this source domain.
        account.header.source_domains[slot].source_lien_capital_at_risk_fee_revenue =
            V16PodU128::new(
                account.header.source_domains[slot]
                    .source_lien_capital_at_risk_fee_revenue
                    .get()
                    .checked_add(charged)
                    .ok_or(V16Error::CounterOverflow)?,
            );
        account.header.health_cert.valid = 0;
        Ok(charged)
    }

    #[cfg(kani)]
    pub fn kani_collect_account_backing_utilization_fee_for_domain_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
    ) -> V16Result<u128> {
        self.collect_account_backing_utilization_fee_for_domain_not_atomic(account, domain)
    }

    fn mark_leg_b_stale(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
    ) -> V16Result<()> {
        let leg_slot = Self::require_active_leg_slot_for_asset(&account.as_view(), asset_index)?;
        let mut leg = account.header.legs[leg_slot].try_to_runtime()?;
        leg.b_stale = true;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&leg);
        self.mark_account_b_stale(account)
    }

    fn account_b_settlement_chunk_from_leg(
        &self,
        leg: PortfolioLegV16,
        target: u128,
        endpoint_loss_atom_budget: u128,
    ) -> V16Result<AccountBSettlementChunkV16> {
        if target < leg.b_snap {
            return Err(V16Error::RecoveryRequired);
        }
        let b_remaining = target - leg.b_snap;
        if b_remaining == 0 {
            return Ok(AccountBSettlementChunkV16 {
                delta_b: 0,
                loss: 0,
                new_remainder: leg.b_rem,
                remaining_after: 0,
            });
        }
        if leg.loss_weight == 0 || endpoint_loss_atom_budget == 0 {
            return Err(V16Error::RecoveryRequired);
        }
        // Both limits are collateral atoms. Convert that atom budget to the
        // corresponding B-index delta exactly once through loss_weight below.
        let limit = self
            .header
            .config
            .public_b_chunk_atoms
            .get()
            .min(endpoint_loss_atom_budget);
        let max_num = limit
            .checked_add(1)
            .and_then(|v| v.checked_mul(SOCIAL_LOSS_DEN))
            .and_then(|v| v.checked_sub(1))
            .ok_or(V16Error::ArithmeticOverflow)?;
        if leg.b_rem > max_num {
            return Err(V16Error::RecoveryRequired);
        }
        let max_delta_by_loss = (max_num - leg.b_rem) / leg.loss_weight;
        let delta_b = b_remaining.min(max_delta_by_loss);
        if delta_b == 0 {
            return Err(V16Error::RecoveryRequired);
        }
        let num = leg
            .loss_weight
            .checked_mul(delta_b)
            .and_then(|v| v.checked_add(leg.b_rem))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let loss = num / SOCIAL_LOSS_DEN;
        let new_remainder = num % SOCIAL_LOSS_DEN;
        Ok(AccountBSettlementChunkV16 {
            delta_b,
            loss,
            new_remainder,
            remaining_after: b_remaining - delta_b,
        })
    }

    fn account_b_settlement_chunk(
        &self,
        account: &PortfolioV16View<'_>,
        asset_index: usize,
        endpoint_loss_atom_budget: u128,
    ) -> V16Result<AccountBSettlementChunkV16> {
        account.validate_with_market(&self.as_view())?;
        let leg = Self::active_leg_for_asset(account, asset_index)?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let target = self.b_target_for_leg(asset_index, leg)?;
        if target < leg.b_snap {
            return Err(V16Error::RecoveryRequired);
        }
        self.account_b_settlement_chunk_from_leg(leg, target, endpoint_loss_atom_budget)
    }

    fn settle_account_b_chunk(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        endpoint_loss_atom_budget: u128,
    ) -> V16Result<AccountBSettlementChunkV16> {
        let chunk = self.account_b_settlement_chunk(
            &account.as_view(),
            asset_index,
            endpoint_loss_atom_budget,
        )?;
        if chunk.delta_b == 0 {
            if !Self::has_b_stale_leg(&account.as_view())? {
                self.clear_account_b_stale(account)?;
            }
            return Ok(chunk);
        }
        let old_pnl = account.header.pnl.get();
        let loss_i128 = i128::try_from(chunk.loss).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = old_pnl
            .checked_sub(loss_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let leg_slot = Self::require_active_leg_slot_for_asset(&account.as_view(), asset_index)?;
        let leg = account.header.legs[leg_slot].try_to_runtime()?;
        let leg = V16Core::kernel_advance_leg_b_snap(
            leg,
            chunk.delta_b,
            chunk.new_remainder,
            chunk.remaining_after,
        )?;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&leg);
        let source_domain = self.insurance_domain_index(asset_index, opposite_side(leg.side))?;
        self.set_account_pnl_after_domain_first_source_claim_burn(account, new_pnl, source_domain)?;
        if chunk.remaining_after != 0 {
            self.mark_account_b_stale(account)?;
        } else if !Self::has_b_stale_leg(&account.as_view())? {
            self.clear_account_b_stale(account)?;
        }
        account.header.health_cert.valid = 0;
        self.validate_account_audit_scan(&account.as_view())?;
        Ok(chunk)
    }

    fn settle_account_side_effects_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        b_loss_atom_budget: u128,
    ) -> V16Result<PermissionlessProgressOutcomeV16> {
        account.validate_with_market(&self.as_view())?;
        self.settle_account_kf_effects_not_atomic(account, false)?;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active {
                let asset_index = leg.asset_index as usize;
                let refreshed = account.header.legs[slot].try_to_runtime()?;
                let target = self.b_target_for_leg(asset_index, refreshed)?;
                if target > refreshed.b_snap {
                    self.mark_leg_b_stale(account, asset_index)?;
                    let chunk =
                        self.settle_account_b_chunk(account, asset_index, b_loss_atom_budget)?;
                    if chunk.remaining_after != 0 {
                        return Ok(PermissionlessProgressOutcomeV16::AccountBChunk(chunk));
                    }
                }
            }
            slot += 1;
        }
        // This composition validated the account before applying only canonical K/F and B
        // transitions. Avoid repeating the same full source-domain and leg scan here.
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        account.header.health_cert.valid = 0;
        Ok(PermissionlessProgressOutcomeV16::AccountCurrent)
    }

    fn certify_account_after_local_settlement_with_price_override(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        price_override: Option<(usize, u64)>,
    ) -> V16Result<HealthCertV16> {
        self.collect_account_backing_utilization_fees_not_atomic(account)?;
        if decode_bool(account.header.b_stale_state)? || Self::has_b_stale_leg(&account.as_view())?
        {
            return Err(V16Error::BStale);
        }
        if decode_bool(account.header.stale_state)? {
            self.clear_account_stale(account)?;
        }
        let cert = self.compute_account_health_cert_with_price_override(
            &account.as_view(),
            true,
            price_override,
        )?;
        account.header.health_cert = HealthCertV16Account::from_runtime(&cert);
        Ok(cert)
    }

    fn require_asset_accruable(&self, asset_index: usize) -> V16Result<()> {
        match self.asset_state(asset_index)?.lifecycle {
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly => Ok(()),
            _ => Err(V16Error::LockActive),
        }
    }

    fn require_asset_mark_pushable(&self, asset_index: usize) -> V16Result<()> {
        match self.asset_state(asset_index)?.lifecycle {
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly => Ok(()),
            _ => Err(V16Error::LockActive),
        }
    }

    fn asset_local_has_position_or_loss_state(&self, asset_index: usize) -> V16Result<bool> {
        self.validate_configured_asset_index(asset_index)?;
        let asset = self.asset_state(asset_index)?;
        let slot = self.markets[asset_index].engine_slot();
        Ok(asset.oi_eff_long_q != 0
            || asset.oi_eff_short_q != 0
            || asset.stored_pos_count_long != 0
            || asset.stored_pos_count_short != 0
            || asset.stale_account_count_long != 0
            || asset.stale_account_count_short != 0
            || asset.b_long_num != 0
            || asset.b_short_num != 0
            || asset.b_epoch_start_long_num != 0
            || asset.b_epoch_start_short_num != 0
            || asset.loss_weight_sum_long != 0
            || asset.loss_weight_sum_short != 0
            || asset.social_loss_remainder_long_num != 0
            || asset.social_loss_remainder_short_num != 0
            || asset.social_loss_dust_long_num != 0
            || asset.social_loss_dust_short_num != 0
            || asset.explicit_unallocated_loss_long != 0
            || asset.explicit_unallocated_loss_short != 0
            || asset.mode_long != SideModeV16::Normal
            || asset.mode_short != SideModeV16::Normal
            || slot.pending_domain_loss_barrier_long.get() != 0
            || slot.pending_domain_loss_barrier_short.get() != 0)
    }

    fn group_has_position_or_loss_state_for_oracle_reset(&self) -> V16Result<bool> {
        if self.header.pnl_pos_tot.get() != 0
            || self.header.stale_certificate_count.get() != 0
            || self.header.b_stale_account_count.get() != 0
            || self.header.negative_pnl_account_count.get() != 0
            || decode_bool(self.header.bankruptcy_hlock_active)?
            || decode_bool(self.header.threshold_stress_active)?
            || decode_bool(self.header.loss_stale_active)?
            || self.header.recovery_reason.try_to_runtime()?.is_some()
        {
            return Ok(true);
        }
        let configured_assets = self.header.config.max_market_slots.get() as usize;
        let mut i = 0usize;
        while i < configured_assets {
            if self.asset_local_has_position_or_loss_state(i)? {
                return Ok(true);
            }
            i += 1;
        }
        Ok(false)
    }

    pub fn set_asset_raw_oracle_target_not_atomic(
        &mut self,
        asset_index: usize,
        raw_oracle_target_price: u64,
    ) -> V16Result<()> {
        self.set_asset_raw_oracle_targets_not_atomic(&[(asset_index, raw_oracle_target_price)])
    }

    /// Stages distinct per-asset oracle targets and validates the resulting market once. A batch
    /// is one committed observation event, so any number of changed targets advances the global
    /// oracle epoch exactly once.
    pub fn set_asset_raw_oracle_targets_not_atomic(
        &mut self,
        targets: &[(usize, u64)],
    ) -> V16Result<()> {
        if targets.is_empty() || decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::InvalidConfig);
        }

        let mut changed = false;
        let mut i = 0usize;
        while i < targets.len() {
            let (asset_index, target) = targets[i];
            self.validate_configured_asset_index(asset_index)?;
            if target == 0 || target > MAX_ORACLE_PRICE {
                return Err(V16Error::InvalidConfig);
            }
            self.require_asset_mark_pushable(asset_index)?;
            let mut prior = 0usize;
            while prior < i {
                if targets[prior].0 == asset_index {
                    return Err(V16Error::InvalidConfig);
                }
                prior += 1;
            }
            changed |= self.asset_state(asset_index)?.raw_oracle_target_price != target;
            i += 1;
        }

        let next_oracle_epoch = if changed {
            Some(
                self.header
                    .oracle_epoch
                    .get()
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?,
            )
        } else {
            None
        };
        for &(asset_index, target) in targets {
            let mut asset = self.asset_state(asset_index)?;
            asset.raw_oracle_target_price = target;
            self.set_asset_state(asset_index, asset)?;
        }
        if let Some(next) = next_oracle_epoch {
            self.header.oracle_epoch = V16PodU64::new(next);
        }
        self.validate_shape()
    }

    pub fn reset_empty_asset_oracle_anchor_not_atomic(
        &mut self,
        asset_index: usize,
        authenticated_price: u64,
        now_slot: u64,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live
            || authenticated_price == 0
            || authenticated_price > MAX_ORACLE_PRICE
            || now_slot < self.header.current_slot.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        let mut asset = self.asset_state(asset_index)?;
        if asset.lifecycle != AssetLifecycleV16::Active
            || self.group_has_position_or_loss_state_for_oracle_reset()?
        {
            return Err(V16Error::LockActive);
        }
        asset.raw_oracle_target_price = authenticated_price;
        asset.effective_price = authenticated_price;
        asset.fund_px_last = authenticated_price;
        asset.slot_last = now_slot;
        self.set_asset_state(asset_index, asset)?;
        self.header.current_slot = V16PodU64::new(now_slot);
        self.header.slot_last = V16PodU64::new(now_slot);
        self.validate_shape()
    }

    pub fn force_asset_recovery_not_atomic(
        &mut self,
        asset_index: usize,
        now_slot: u64,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live
            || now_slot < self.header.current_slot.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        let asset = self.asset_state(asset_index)?;
        match asset.lifecycle {
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly => {
                let (asset, next_asset_set_epoch, next_risk_epoch) =
                    V16Core::prepare_asset_recovery_transition(
                        asset,
                        self.header.asset_set_epoch.get(),
                        self.header.risk_epoch.get(),
                    )?;
                self.set_asset_state(asset_index, asset)?;
                self.commit_asset_set_epoch_bump(next_asset_set_epoch, next_risk_epoch);
                self.validate_shape()
            }
            AssetLifecycleV16::Recovery => self.validate_shape(),
            _ => Err(V16Error::LockActive),
        }
    }

    pub fn accrue_asset_to_not_atomic(
        &mut self,
        asset_index: usize,
        now_slot: u64,
        effective_price: u64,
        funding_rate_e9: i128,
        protective_progress_committed: bool,
    ) -> V16Result<AccrueAssetOutcomeV16> {
        let config = self.header.config.try_to_runtime_shape()?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        if asset_index >= config.max_market_slots as usize
            || asset_index >= self.markets.len()
            || effective_price == 0
            || effective_price > MAX_ORACLE_PRICE
            || funding_rate_e9.unsigned_abs() > config.max_abs_funding_e9_per_slot as u128
        {
            return Err(V16Error::InvalidConfig);
        }
        self.require_asset_accruable(asset_index)?;
        let old = self.asset_state(asset_index)?;
        if now_slot < old.slot_last {
            return Err(V16Error::InvalidConfig);
        }
        let dt_total = now_slot - old.slot_last;
        let segment_dt = if dt_total > config.max_accrual_dt_slots {
            config.max_accrual_dt_slots
        } else {
            dt_total
        };
        let activity = V16Core::accrual_activity_for_asset_segment(
            old,
            segment_dt,
            effective_price,
            funding_rate_e9,
        );
        if activity.equity_active {
            if segment_dt == 0 {
                return Err(V16Error::NonProgress);
            }
            let price_diff = effective_price.abs_diff(old.effective_price) as u128;
            let lhs = price_diff
                .checked_mul(MAX_MARGIN_BPS as u128)
                .ok_or(V16Error::ArithmeticOverflow)?;
            let rhs = (config.max_price_move_bps_per_slot as u128)
                .checked_mul(segment_dt as u128)
                .and_then(|v| v.checked_mul(old.effective_price as u128))
                .ok_or(V16Error::ArithmeticOverflow)?;
            if lhs > rhs {
                return Err(V16Error::RecoveryRequired);
            }
            if !protective_progress_committed {
                return Err(V16Error::NonProgress);
            }
        }

        let price_delta = effective_price as i128 - old.effective_price as i128;
        // FZS-1 fix (spec 5.3, spec.md:1070-1079): accrue K/F PER SIDE scaled by that
        // side's live A (a_long/a_short), NOT a flat ADL_ONE to both legs. Settlement
        // realizes each leg as basis*(K_now-K_snap)/(a_basis*POS_SCALE), so the per-side
        // A factor cancels the leg's frozen a_basis divisor and matched legs realize
        // equal-and-opposite magnitudes for ANY a in [MIN_A_SIDE, ADL_ONE]. On a balanced
        // book (a_long == a_short == ADL_ONE) this is byte-identical to the old flat code.
        // The old flat path minted value on an asymmetric-a book because the low-A side
        // over-realized by ADL_ONE/a_side (see issue #114).
        let funding_index_delta = if activity.funding_active {
            let n = funding_rate_e9
                .checked_mul(segment_dt as i128)
                .and_then(|v| v.checked_mul(effective_price as i128))
                .ok_or(V16Error::ArithmeticOverflow)?;
            floor_div_signed_conservative_i128(n, FUNDING_DEN)
        } else {
            0
        };
        let (k_delta_long, k_delta_short, funding_delta_long, funding_delta_short) =
            V16Core::kernel_adl_scaled_accrual_index_deltas(
                price_delta,
                funding_index_delta,
                old.a_long,
                old.a_short,
            )?;

        let long_kf_changed = k_delta_long != 0 || funding_delta_long != 0;
        let short_kf_changed = k_delta_short != 0 || funding_delta_short != 0;

        let mut asset = old;
        asset.k_long = add_non_min_i128(asset.k_long, k_delta_long)?;
        asset.k_short = add_non_min_i128(asset.k_short, k_delta_short)?;
        asset.f_long_num = add_non_min_i128(asset.f_long_num, funding_delta_long)?;
        asset.f_short_num = add_non_min_i128(asset.f_short_num, funding_delta_short)?;
        asset.effective_price = effective_price;
        // Canonical path accrual uses this persisted nonzero field as its stable price-cap anchor.
        // A direct price move starts a new trajectory; zero-move funding must preserve an active
        // trajectory anchor so transaction partitioning cannot change later price movement.
        if effective_price != old.effective_price || effective_price == old.raw_oracle_target_price
        {
            asset.fund_px_last = effective_price;
        }
        asset.slot_last = asset
            .slot_last
            .checked_add(segment_dt)
            .ok_or(V16Error::ArithmeticOverflow)?;
        asset = V16Core::kernel_mark_kf_stale_cohorts(
            asset,
            long_kf_changed,
            short_kf_changed,
            asset.slot_last,
        )?;
        self.set_asset_state(asset_index, asset)?;
        // `now_slot` is the endpoint of this asset-local committed segment. Another asset can
        // already have advanced the market's authenticated clock beyond that endpoint, so keep
        // the global clock monotonic while allowing this lagging asset to catch up.
        // (upstream b4b975f3)
        self.header.current_slot = V16PodU64::new(self.header.current_slot.get().max(now_slot));
        // Hot paths are asset-local: scanning all markets here makes every
        // crank/trade depend on total dynamic asset count. `slot_last` and
        // `loss_stale_active` summarize only the touched asset; safety gates
        // use account/asset-local stale checks.
        self.header.slot_last = V16PodU64::new(asset.slot_last);
        let loss_stale_after = asset_is_loss_stale_at_slot(asset, now_slot);
        self.header.loss_stale_active = encode_bool(loss_stale_after);
        if activity.price_move_active {
            self.header.oracle_epoch = V16PodU64::new(
                self.header
                    .oracle_epoch
                    .get()
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?,
            );
        }
        if activity.funding_active {
            self.header.funding_epoch = V16PodU64::new(
                self.header
                    .funding_epoch
                    .get()
                    .checked_add(1)
                    .ok_or(V16Error::CounterOverflow)?,
            );
        }
        self.validate_shape_audit_scan()?;
        Ok(AccrueAssetOutcomeV16 {
            dt: segment_dt,
            price_move_active: activity.price_move_active,
            funding_active: activity.funding_active,
            equity_active: activity.equity_active,
            loss_stale_after,
        })
    }

    /// Applies the unique canonical one-slot accrual prefix for this asset.
    ///
    /// Requiring the complete bounded prefix prevents a caller from choosing transaction
    /// boundaries that change price compounding or funding sampling. The wrapper may construct up
    /// to `V16_MAX_ACCRUAL_PATH_STEPS` deterministic steps; a longer stale interval remains
    /// actionable through another call with the same authenticated `now_slot`.
    pub fn accrue_asset_path_to_not_atomic(
        &mut self,
        asset_index: usize,
        now_slot: u64,
        raw_oracle_target_price: u64,
        steps: &[AccrualStepV16],
        protective_progress_committed: bool,
    ) -> V16Result<AccrueAssetOutcomeV16> {
        let config = self.header.config.try_to_runtime_shape()?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live
            || asset_index >= config.max_market_slots as usize
            || asset_index >= self.markets.len()
            || raw_oracle_target_price == 0
            || raw_oracle_target_price > MAX_ORACLE_PRICE
            || now_slot < self.header.current_slot.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        self.require_asset_accruable(asset_index)?;
        let mut asset = self.asset_state(asset_index)?;
        let k_long_before = asset.k_long;
        let k_short_before = asset.k_short;
        let f_long_before = asset.f_long_num;
        let f_short_before = asset.f_short_num;
        if now_slot < asset.slot_last {
            return Err(V16Error::InvalidConfig);
        }
        let expected_steps_u64 = (now_slot - asset.slot_last)
            .min(config.max_accrual_dt_slots)
            .min(V16_MAX_ACCRUAL_PATH_STEPS as u64);
        let expected_steps =
            usize::try_from(expected_steps_u64).map_err(|_| V16Error::ArithmeticOverflow)?;
        if steps.len() != expected_steps {
            return Err(V16Error::InvalidConfig);
        }
        let target_changed = asset.raw_oracle_target_price != raw_oracle_target_price;
        let price_cap_anchor = if target_changed {
            asset.effective_price
        } else {
            asset.fund_px_last
        };
        if price_cap_anchor == 0 || price_cap_anchor > MAX_ORACLE_PRICE {
            return Err(V16Error::InvalidConfig);
        }
        if target_changed {
            asset.fund_px_last = asset.effective_price;
        }

        let mut price_move_count = 0u64;
        let mut funding_count = 0u64;
        let mut expected_remainder = steps
            .first()
            .map(|step| step.price_move_remainder_before_bps_num)
            .unwrap_or(0);
        for (index, step) in steps.iter().enumerate() {
            if step.effective_price == 0
                || step.effective_price > MAX_ORACLE_PRICE
                || step.funding_rate_e9.unsigned_abs() > config.max_abs_funding_e9_per_slot as u128
                || (index == 0 && target_changed && step.price_move_remainder_before_bps_num != 0)
                || step.price_move_remainder_before_bps_num != expected_remainder
            {
                return Err(V16Error::InvalidConfig);
            }
            let exposed = asset.oi_eff_long_q != 0 || asset.oi_eff_short_q != 0;
            let (expected_price, remainder_after) = canonical_accrual_price_step_v16(
                asset.effective_price,
                raw_oracle_target_price,
                price_cap_anchor,
                config.max_price_move_bps_per_slot,
                exposed,
                step.price_move_remainder_before_bps_num,
            )?;
            if step.effective_price != expected_price
                || step.price_move_remainder_after_bps_num != remainder_after
            {
                return Err(V16Error::InvalidConfig);
            }
            expected_remainder = remainder_after;
            let activity = V16Core::accrual_activity_for_asset_segment(
                asset,
                1,
                step.effective_price,
                step.funding_rate_e9,
            );
            if activity.equity_active && !protective_progress_committed {
                return Err(V16Error::NonProgress);
            }

            let price_delta = step.effective_price as i128 - asset.effective_price as i128;
            let funding_index_delta = if activity.funding_active {
                let n = step
                    .funding_rate_e9
                    .checked_mul(step.effective_price as i128)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                floor_div_signed_conservative_i128(n, FUNDING_DEN)
            } else {
                0
            };
            let (k_delta_long, k_delta_short, funding_delta_long, funding_delta_short) =
                V16Core::kernel_adl_scaled_accrual_index_deltas(
                    price_delta,
                    funding_index_delta,
                    asset.a_long,
                    asset.a_short,
                )?;

            asset.k_long = add_non_min_i128(asset.k_long, k_delta_long)?;
            asset.k_short = add_non_min_i128(asset.k_short, k_delta_short)?;
            asset.f_long_num = add_non_min_i128(asset.f_long_num, funding_delta_long)?;
            asset.f_short_num = add_non_min_i128(asset.f_short_num, funding_delta_short)?;
            asset.effective_price = step.effective_price;
            asset.slot_last = asset
                .slot_last
                .checked_add(1)
                .ok_or(V16Error::ArithmeticOverflow)?;
            price_move_count = price_move_count
                .checked_add(u64::from(activity.price_move_active))
                .ok_or(V16Error::CounterOverflow)?;
            funding_count = funding_count
                .checked_add(u64::from(activity.funding_active))
                .ok_or(V16Error::CounterOverflow)?;
        }

        if asset.effective_price == raw_oracle_target_price {
            asset.fund_px_last = asset.effective_price;
        }

        let long_kf_changed = asset.k_long != k_long_before || asset.f_long_num != f_long_before;
        let short_kf_changed =
            asset.k_short != k_short_before || asset.f_short_num != f_short_before;
        asset = V16Core::kernel_mark_kf_stale_cohorts(
            asset,
            long_kf_changed,
            short_kf_changed,
            asset.slot_last,
        )?;
        asset.raw_oracle_target_price = raw_oracle_target_price;
        self.set_asset_state(asset_index, asset)?;
        self.header.current_slot = V16PodU64::new(now_slot);
        self.header.slot_last = V16PodU64::new(asset.slot_last);
        let loss_stale_after = asset_is_loss_stale_at_slot(asset, now_slot);
        self.header.loss_stale_active = encode_bool(loss_stale_after);
        self.header.oracle_epoch = V16PodU64::new(
            self.header
                .oracle_epoch
                .get()
                .checked_add(price_move_count)
                .and_then(|value| value.checked_add(u64::from(target_changed)))
                .ok_or(V16Error::CounterOverflow)?,
        );
        self.header.funding_epoch = V16PodU64::new(
            self.header
                .funding_epoch
                .get()
                .checked_add(funding_count)
                .ok_or(V16Error::CounterOverflow)?,
        );
        self.validate_shape_audit_scan()?;
        Ok(AccrueAssetOutcomeV16 {
            dt: expected_steps_u64,
            price_move_active: price_move_count != 0,
            funding_active: funding_count != 0,
            equity_active: price_move_count != 0 || funding_count != 0,
            loss_stale_after,
        })
    }

    fn declare_permissionless_recovery(
        &mut self,
        reason: PermissionlessRecoveryReasonV16,
    ) -> V16Result<PermissionlessProgressOutcomeV16> {
        if !decode_bool(self.header.config.permissionless_recovery_enabled)? {
            return Err(V16Error::InvalidConfig);
        }
        if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
            return Err(V16Error::LockActive);
        }
        if let Some(existing_reason) = self.header.recovery_reason.try_to_runtime()? {
            return Ok(PermissionlessProgressOutcomeV16::RecoveryDeclared(
                existing_reason,
            ));
        }
        self.header.mode = encode_market_mode(MarketModeV16::Recovery);
        self.header.recovery_reason = V16OptionalRecoveryReasonAccount::from_runtime(Some(reason));
        self.validate_shape()?;
        Ok(PermissionlessProgressOutcomeV16::RecoveryDeclared(reason))
    }

    /// PRODUCTION CLASSIFIER (roadmap 3C step 4): map the real account/market
    /// state to the ActionableState summary the self-classifying crank dispatches
    /// from. Each flag is exactly its production eligibility predicate, MODE-
    /// GATED so every flag that can be set has a currently-valid dispatch target:
    ///   stale            — Live, health cert not current, a settled prior-reset
    ///                      obligation needs permissionless detachment, or source
    ///                      backing used by the account has reached expiry
    ///   b_stale          — Live, some active leg has a cached or derived pending B settlement
    ///   pending_close    — Live, a close-progress ledger is active
    ///   expired_close    — Live, that ledger is past its max-close slot
    ///   liquidatable     — Live, current cert with nonzero certified liq deficit
    ///   source_liens_releasable — Live, flat, independently initial-margin safe,
    ///                      current account whose obsolete source liens can be
    ///                      returned without an oracle observation
    ///   recovery_eligible— reserved for selector-level proactive Recovery
    ///   resolved_winner  — Resolved, positive PnL, resolved payout ready
    /// Assembled via the proven actionable_summary_from_signals kernel. Live-only
    /// flags need cert currentness only where their entrypoint does (liquidate),
    /// so refresh is selected first for a stale account and the deficit is read
    /// from a fresh cert on the next step.
    pub fn build_actionable_summary(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<ActionableSummaryV16> {
        self.build_actionable_summary_at_slot(account, self.header.current_slot.get())
    }

    /// Classifies clock-driven work against an authenticated execution slot even
    /// when no oracle observation was supplied to advance the committed market
    /// slot. The caller must authenticate `now_slot`; execution remains bounded
    /// to one selected continuation.
    pub fn build_actionable_summary_at_slot(
        &self,
        account: &PortfolioV16View<'_>,
        now_slot: u64,
    ) -> V16Result<ActionableSummaryV16> {
        Ok(self
            .build_actionable_summary_and_selected_assets(account, now_slot)?
            .0)
    }

    fn build_actionable_summary_and_selected_assets(
        &self,
        account: &PortfolioV16View<'_>,
        now_slot: u64,
    ) -> V16Result<(
        ActionableSummaryV16,
        (
            Option<usize>,
            Option<usize>,
            Option<usize>,
            Option<usize>,
            Option<usize>,
        ),
    )> {
        if now_slot < self.header.current_slot.get() {
            return Err(V16Error::InvalidConfig);
        }
        let mode = decode_market_mode(self.header.mode)?;
        let live = mode == MarketModeV16::Live;
        let resolved = mode == MarketModeV16::Resolved;

        let cert = account.header.health_cert.try_to_runtime()?;
        let cert_current = V16Core::kernel_cert_is_current(
            cert,
            self.header.oracle_epoch.get(),
            self.header.funding_epoch.get(),
            self.header.risk_epoch.get(),
            self.header.asset_set_epoch.get(),
            account.header.active_bitmap.map(V16PodU64::get),
        );
        let ledger = account.header.close_progress.try_to_runtime()?;

        let selected_assets = self.auto_crank_selected_assets(account)?;
        let liquidatable_asset = selected_assets.2;
        let reset_obligation_asset = selected_assets.3;
        let released_obligation_asset = selected_assets.4;
        // Clock-driven, so it is classified at the AUTHENTICATED execution slot
        // rather than the committed market slot (fork: _at_slot classification).
        let lapsed_source_backing = self
            .first_lapsed_source_backing_for_account_at_slot(account, now_slot)?
            .is_some();
        let has_open_risk = liquidatable_asset.is_some();
        // A close ledger with residual_remaining==0 is already fully booked/covered
        // (e.g. insurance absorbed the loss); only OUTSTANDING residual is real,
        // actionable close work. The `active` flag can linger past that.
        let close_outstanding = ledger.has_pending_residual();
        let stale = V16Core::kernel_live_account_refresh_required(
            live,
            cert_current,
            reset_obligation_asset.is_some(),
            released_obligation_asset.is_some(),
            lapsed_source_backing,
        );
        let b_stale = live && selected_assets.0.is_some();
        // A durable close ledger is independently actionable even after the trade
        // that created it cleared the bankrupt leg. AdvanceClose infers the asset
        // and bankrupt side from this immutable ledger, so no caller hint can
        // redirect the residual.
        let pending_close = live && close_outstanding;
        // Expired outstanding close -> terminal recovery (Recover needs no leg).
        let expired_close = live && close_outstanding && now_slot > ledger.max_close_slot;
        // liquidatable requires a current certified deficit AND actual open risk.
        // Prior-reset obligations are settled/detached first through Refresh so
        // they cannot block side finalization or poison liquidation dispatch:
        // a stale cert can still report a deficit after the position was already
        // closed, but with no active leg there is nothing to liquidate (the real
        // liquidate entrypoint requires an active leg), so the flag must be false.
        let liquidatable = live
            && cert_current
            && cert.certified_liq_deficit != 0
            && has_open_risk
            && reset_obligation_asset.is_none();
        let no_positive_equity = Self::account_no_positive_credit_equity(account)?;
        let flat = active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get));
        let source_lien_margin_safe =
            no_positive_equity >= 0 && (no_positive_equity as u128) >= cert.certified_initial_req;
        let normalizable_source_lien =
            if live && cert_current && !lapsed_source_backing && flat && source_lien_margin_safe {
                self.account_has_normalizable_source_credit_lien(account, now_slot)?
            } else {
                false
            };
        let source_liens_releasable = V16Core::kernel_live_flat_source_lien_normalization_required(
            live,
            cert_current,
            lapsed_source_backing,
            flat,
            source_lien_margin_safe,
            normalizable_source_lien,
        );
        // A completed account-local bankruptcy must not let that account force a
        // market-wide Recovery. In particular, a permissionless asset can be
        // attacker-controlled while unrelated assets remain healthy. Outstanding
        // close expiry remains the proactive Recovery route above; completed or
        // unattributed deficits wait for an explicit market-level resolution
        // policy instead of inventing an asset domain or terminating the market.
        let recovery_eligible = false;
        // resolved_winner routes to close_resolved, which LAZILY captures the
        // payout snapshot itself (initialize_resolved_payout_ledger_if_needed is
        // reached only via close_resolved -> create_resolved_payout_receipt) — so
        // we must NOT gate on payout_snapshot_captured: doing so would deadlock the
        // FIRST winner (snapshot never captured -> never classified -> never
        // captured). resolved_positive_payout_ready (all blocking counts zero) is
        // exactly close_resolved's own precondition for proceeding with payout.
        //
        // Resolved close is also the bounded cleanup route for capital-only
        // accounts, zero-PnL source attribution, active legs, receipts, and the
        // final resolved-slot fee-anchor sync. The fee anchor is deliberately not
        // part of economic emptiness, but close_resolved still has to advance it
        // before the account is fully normalized. Gating solely on economic
        // emptiness would hide that bounded step from the only permissionless
        // crank. A flat positive-PnL account still waits until the payout blocker
        // census is clear, because close_resolved would otherwise return a
        // successful no-op; pre-payout cleanup work remains actionable.
        let resolved_fee_sync_pending =
            resolved && account.header.last_fee_slot.get() < self.header.resolved_slot.get();
        let resolved_pending =
            resolved && (!account.is_empty_for_dematerialization()? || resolved_fee_sync_pending);
        let resolved_pre_payout_progress =
            !active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get))
                || decode_bool(account.header.b_stale_state)?
                || decode_bool(account.header.stale_state)?
                || account.header.pnl.get() <= 0
                || Self::account_has_source_liens(account)
                || lapsed_source_backing
                || ledger.has_pending_residual()
                || resolved_fee_sync_pending;
        let resolved_winner = resolved_pending
            && (resolved_pre_payout_progress || self.resolved_positive_payout_ready()?);

        Ok((
            V16Core::actionable_summary_from_signals(
                stale,
                b_stale,
                pending_close,
                expired_close,
                liquidatable,
                source_liens_releasable,
                recovery_eligible,
                resolved_winner,
            ),
            selected_assets,
        ))
    }

    /// PRODUCTION SELF-CLASSIFYING CRANK (roadmap 3C step 4): the keeper no longer
    /// chooses the action. build_actionable_summary classifies the account and
    /// the proven select_progress_witness picks the unique, overlap-safe,
    /// highest-priority continuation, which this dispatches to the matching proven
    /// entrypoint. The caller supplies only the unavoidable oracle observation +
    /// action parameters via the hint. Returns the selected continuation (None
    /// when not actionable) and the dispatched outcome. Each continuation's
    /// dispatch target is valid in the mode that the classifier gated its flag to.
    /// ENGINE asset self-selection (engine.md): scan the account's bounded legs and
    /// return, for each asset-scoped continuation, the engine-chosen asset_index —
    /// the FIRST active leg with pending B settlement (either a cached stale bit or
    /// a current B target above its snapshot), the FIRST accrual-dispatchable
    /// active leg (falling back to the FIRST Recovery leg for committed-state
    /// refresh), and the FIRST live-reducible leg (liquidation). A prior-epoch
    /// ResetPending leg is still refreshable, but
    /// its effective OI was already removed by ADL; selecting it for liquidation
    /// would fail before a later current-epoch leg could make progress. Recovery
    /// legs use committed-state refresh only and are never selected for accrual
    /// or liquidation. The
    /// selection is proven in-range / actionable / first-match / complete by the
    /// first_actionable_slot contract; the slot->asset_index and lifecycle filter
    /// are bound to production state here.
    // Five engine-selected asset slots. Upstream carries the same bare tuple and
    // trips this lint too; naming a type here would diverge for no benefit.
    #[allow(clippy::type_complexity)]
    fn auto_crank_selected_assets(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<(
        Option<usize>,
        Option<usize>,
        Option<usize>,
        Option<usize>,
        Option<usize>,
    )> {
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let release_allowed = !account
            .header
            .close_progress
            .try_to_runtime()?
            .has_pending_residual();
        let mut refresh_flags = [false; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut liquidation_flags = [false; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut reset_obligation_flags = [false; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut b_stale_flags = [false; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut recovery_refresh_flags = [false; V16_MAX_PORTFOLIO_ASSETS_N];
        let mut released_obligation_asset = None;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            let active = active_bitmap_get(bitmap, slot) && leg.active;
            if active {
                let asset = self.asset_state(leg.asset_index as usize)?;
                let (side_mode, asset_epoch) = match leg.side {
                    SideV16::Long => (asset.mode_long, asset.epoch_long),
                    SideV16::Short => (asset.mode_short, asset.epoch_short),
                };
                // A leg can only be liquidated against OI both sides still hold;
                // a side-local OI reading would offer a liquidation that has
                // nothing left to match. (upstream 9ffc4749)
                let matched_oi = asset.oi_eff_long_q.min(asset.oi_eff_short_q);
                let b_target = Self::b_target_for_leg_from_asset(asset, leg)?;
                let b_settlement_pending =
                    V16Core::kernel_b_settlement_pending(leg.b_stale, b_target, leg.b_snap)?;
                let (b_stale, refresh, liquidatable, reset_obligation) =
                    V16Core::kernel_auto_crank_leg_flags(
                        true,
                        asset.lifecycle,
                        leg.basis_pos_q,
                        matched_oi,
                        side_mode,
                        asset_epoch,
                        leg.epoch_snap,
                        b_settlement_pending,
                    );
                b_stale_flags[slot] = b_stale;
                refresh_flags[slot] = refresh;
                recovery_refresh_flags[slot] = asset.lifecycle == AssetLifecycleV16::Recovery;
                liquidation_flags[slot] = liquidatable;
                // A legacy Normal-mode leg whose effective OI is already exhausted
                // is a reset obligation too, or it stays uncrankable after upgrade.
                // (upstream 9ffc4749)
                reset_obligation_flags[slot] =
                    reset_obligation || Self::leg_has_exhausted_effective_oi(asset, leg);
                let released_obligation = release_allowed
                    && !leg.stale
                    && !leg.b_stale
                    && leg.basis_pos_q == 0
                    && leg.loss_weight != 0
                    && !self.has_pending_domain_loss_barrier(leg.asset_index as usize, leg.side)?
                    && self.recovery_pending_obligation_release_allowed(
                        leg.asset_index as usize,
                        leg.side,
                    )?;
                if released_obligation_asset.is_none() && released_obligation {
                    released_obligation_asset = Some(leg.asset_index as usize);
                }
            }
            slot += 1;
        }
        let asset_of = |s: Option<usize>| -> V16Result<Option<usize>> {
            match s {
                Some(i) => Ok(Some(
                    account.header.legs[i].try_to_runtime()?.asset_index as usize,
                )),
                None => Ok(None),
            }
        };
        let b_stale_asset = asset_of(V16Core::first_actionable_slot(b_stale_flags))?;
        let ordinary_refresh_asset = asset_of(V16Core::first_actionable_slot(refresh_flags))?;
        let recovery_refresh_asset =
            asset_of(V16Core::first_actionable_slot(recovery_refresh_flags))?;
        let refresh_asset = V16Core::kernel_auto_crank_refresh_asset(
            ordinary_refresh_asset,
            recovery_refresh_asset,
        );
        let liquidatable_asset = asset_of(V16Core::first_actionable_slot(liquidation_flags))?;
        let reset_obligation_asset =
            asset_of(V16Core::first_actionable_slot(reset_obligation_flags))?;
        Ok((
            b_stale_asset,
            refresh_asset,
            liquidatable_asset,
            reset_obligation_asset,
            released_obligation_asset,
        ))
    }

    /// THE SINGLE PUBLIC PERMISSIONLESS CRANK (engine.md): the only crank the
    /// wrapper should call — order-insensitive and engine-selected, built for a
    /// swarm of opportunistic keepers whose transactions land out of order. The
    /// per-action primitives (refresh / settle-B / liquidate / recover /
    /// close-resolved) are internal dispatch targets, not wrapper entrypoints.
    ///
    /// Calling convention (wrapper side):
    /// 1. Decode a public auto-crank instruction carrying a bounded set of oracle
    ///    OBSERVATIONS (asset, authenticated price, funding) — one per asset the
    ///    keeper has fresh data for — plus the `resolved_close_fee_rate_per_slot`.
    /// 2. Authenticate clock/slot + each observation against the oracle.
    /// 3. Build `AutoCrankWorkV16 { now_slot, observations,
    ///    resolved_close_fee_rate_per_slot }` and call this ONCE (one ix = one step;
    ///    never loop to a fixed point — CU).
    /// 4. The engine classifies the account, selects the highest-priority step AND
    ///    its asset (self-selected — the caller never chooses action or asset),
    ///    matches the observation that step needs, derives the liquidation fee from
    ///    CONFIG (never the caller), and dispatches one bounded primitive.
    /// 5. On `Ok(result)`, mirror any wrapper-owned token/custody movement keyed off
    ///    `result.selected` (the `AutoCrankPlanV16`): refresh / settle-B /
    ///    source-lien release move no custody; liquidate / close-resolved may.
    ///    `NoAction` => nothing was needed.
    ///    In Recovery, the next call selects `FinalizeRecovery` and performs the
    ///    value-neutral transition to Resolved so terminal account close remains
    ///    publicly reachable. `Err(NonProgress)` => the selected step needed an
    ///    observation the caller did not supply (currently the no-active-asset
    ///    refresh fallback, or a stale/late tx whose task changed) — no mutation,
    ///    so SVM rollback is a clean no-op and arbitrary landing order is safe.
    pub fn permissionless_auto_crank_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        work: AutoCrankWorkV16<'_>,
    ) -> V16Result<AutoCrankResultV16> {
        // A market already in Recovery has exactly one bounded public step left:
        // the value-neutral transition to Resolved, which puts terminal account
        // close back within reach. Without it Recovery is a dead end for the single
        // public crank, because permissionless_crank_not_atomic rejects every
        // non-Recover action outside Live.
        if decode_market_mode(self.header.mode)? == MarketModeV16::Recovery {
            account.validate_with_market(&self.as_view())?;
            // Finalizing Recovery is irreversible, so any obligation this account
            // still holds must be SETTLED and released first. Resolving over it
            // would strand the leg on the far side of the transition.
            let released_obligation_asset = self.auto_crank_selected_assets(&account.as_view())?.4;
            if let Some(asset_index) = released_obligation_asset {
                self.validate_unconfigured_market_tail()?;
                self.forfeit_recovery_leg_not_atomic(
                    account,
                    asset_index,
                    self.header.config.public_b_chunk_atoms.get(),
                )?;
                self.validate_shape_audit_scan()?;
                account.validate_with_market(&self.as_view())?;
                return Ok(AutoCrankResultV16 {
                    selected: AutoCrankPlanV16::RefreshAccount {
                        asset_index: Some(asset_index),
                    },
                    outcome: AutoCrankOutcomeV16::Progressed(
                        PermissionlessProgressOutcomeV16::AccountCurrent,
                    ),
                });
            }
            self.resolve_market_not_atomic(work.now_slot)?;
            account.validate_with_market(&self.as_view())?;
            return Ok(AutoCrankResultV16 {
                selected: AutoCrankPlanV16::FinalizeRecovery,
                outcome: AutoCrankOutcomeV16::RecoveryResolved,
            });
        }
        let (
            summary,
            (
                b_stale_asset,
                refresh_asset,
                liquidatable_asset,
                reset_obligation_asset,
                released_obligation_asset,
            ),
        ) = self.build_actionable_summary_and_selected_assets(&account.as_view(), work.now_slot)?;
        let recovery_reason = if summary.expired_close || summary.recovery_eligible {
            PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress
        } else {
            PermissionlessRecoveryReasonV16::ExplicitLossOrDustAuditOverflow
        };
        // PRODUCTION KERNEL: the proven plan selector (priority + totality +
        // engine-selected asset). refresh accrues the first active leg's asset.
        let plan = V16Core::select_auto_crank_plan(
            summary,
            b_stale_asset.unwrap_or(0),
            liquidatable_asset.unwrap_or(0),
            V16Core::kernel_auto_crank_refresh_asset(refresh_asset, reset_obligation_asset),
            recovery_reason,
        );

        // Once the originating domain barrier is gone, a zero-basis leg carries
        // only a released loss obligation. Route it through the canonical
        // Recovery-forfeit transition so any K/F/B delta is settled before the
        // leg and its aggregate counters are detached.
        if matches!(plan, AutoCrankPlanV16::RefreshAccount { .. }) {
            if let Some(asset_index) = released_obligation_asset {
                self.validate_unconfigured_market_tail()?;
                let advanced =
                    if self.asset_state(asset_index)?.lifecycle == AssetLifecycleV16::Recovery {
                        self.forfeit_recovery_leg_not_atomic(
                            account,
                            asset_index,
                            self.header.config.public_b_chunk_atoms.get(),
                        )?;
                        true
                    } else {
                        match self.clear_leg(account, asset_index) {
                            Ok(()) => true,
                            // Active/DrainOnly obligations can still accrue K/F/B.
                            // The ordinary refresh dispatch below settles them.
                            Err(V16Error::Stale) => false,
                            Err(err) => return Err(err),
                        }
                    };
                if advanced {
                    self.validate_shape_audit_scan()?;
                    account.validate_with_market(&self.as_view())?;
                    return Ok(AutoCrankResultV16 {
                        selected: AutoCrankPlanV16::RefreshAccount {
                            asset_index: Some(asset_index),
                        },
                        outcome: AutoCrankOutcomeV16::Progressed(
                            PermissionlessProgressOutcomeV16::AccountCurrent,
                        ),
                    });
                }
            }
        }

        let obs_or_current_asset = |me: &Self, i: usize| -> V16Result<AutoCrankObservationV16> {
            match work
                .observations
                .iter()
                .copied()
                .find(|o| o.asset_index == i)
            {
                Some(obs) => Ok(obs),
                None => {
                    let asset = me.asset_state(i)?;
                    Ok(AutoCrankObservationV16 {
                        asset_index: i,
                        effective_price: asset.effective_price,
                        funding_rate_e9: 0,
                    })
                }
            }
        };
        let crank_with = |me: &mut Self,
                          account: &mut PortfolioV16ViewMut<'_>,
                          asset_index: usize,
                          obs: AutoCrankObservationV16,
                          action: PermissionlessCrankActionV16|
         -> V16Result<PermissionlessProgressOutcomeV16> {
            me.permissionless_crank_not_atomic(
                account,
                PermissionlessCrankRequestV16 {
                    now_slot: work.now_slot,
                    asset_index,
                    effective_price: obs.effective_price,
                    funding_rate_e9: obs.funding_rate_e9,
                    action,
                },
            )
        };

        let outcome = match plan {
            AutoCrankPlanV16::NoAction => AutoCrankOutcomeV16::NoAction,
            AutoCrankPlanV16::ReleaseSourceLiens => {
                // fdf11670 guards this inside the core fn. Here the core is shared
                // with the #137 conversion path, which legitimately runs on a
                // NON-flat account to release a lien whose own domain has closed,
                // so the flatness precondition lives on the crank entry instead.
                if !active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get))
                    || !Self::account_has_source_liens(&account.as_view())
                    || self.account_has_active_source_claim_exposure(&account.as_view())?
                {
                    return Err(V16Error::NonProgress);
                }
                self.release_account_source_credit_liens_if_unneeded_core_not_atomic(account)?;
                AutoCrankOutcomeV16::Progressed(PermissionlessProgressOutcomeV16::AccountCurrent)
            }
            AutoCrankPlanV16::RefreshAccount { asset_index } => {
                // Accrue the engine-selected active asset from either a fresh
                // observation or committed state; if no active asset exists, use
                // the first supplied observation to give the refresh a price.
                let (ai, obs) = match asset_index {
                    Some(i) => {
                        if self.asset_state(i)?.lifecycle == AssetLifecycleV16::Recovery {
                            return Ok(AutoCrankResultV16 {
                                selected: plan,
                                outcome: AutoCrankOutcomeV16::Progressed(
                                    self.refresh_recovery_account_from_committed_state_not_atomic(
                                        account,
                                        i,
                                        work.now_slot,
                                    )?,
                                ),
                            });
                        }
                        (i, obs_or_current_asset(self, i)?)
                    }
                    None => {
                        let o = work
                            .observations
                            .first()
                            .copied()
                            .ok_or(V16Error::NonProgress)?;
                        (o.asset_index, o)
                    }
                };
                AutoCrankOutcomeV16::Progressed(crank_with(
                    self,
                    account,
                    ai,
                    obs,
                    PermissionlessCrankActionV16::Refresh,
                )?)
            }
            AutoCrankPlanV16::SettleBChunk { asset_index } => {
                let obs = obs_or_current_asset(self, asset_index)?;
                AutoCrankOutcomeV16::Progressed(crank_with(
                    self,
                    account,
                    asset_index,
                    obs,
                    PermissionlessCrankActionV16::SettleB { asset_index },
                )?)
            }
            AutoCrankPlanV16::Liquidate { asset_index } => {
                let obs = obs_or_current_asset(self, asset_index)?;
                // Fee policy and close sizing both come from CONFIG and the
                // engine's own liquidation selector, never from a caller hint.
                // Upstream's f5d291eb form passed close_q and fee_bps in the
                // request and carried a liquidation_max_close_q budget in the
                // work; b97e1746 removed all three, and this fork already carries
                // the reduced shape, so the request is built in its tip form.
                AutoCrankOutcomeV16::Progressed(crank_with(
                    self,
                    account,
                    asset_index,
                    obs,
                    PermissionlessCrankActionV16::Liquidate(LiquidationRequestV16 { asset_index }),
                )?)
            }
            AutoCrankPlanV16::AdvanceClose => {
                let progressed = match self.advance_pending_close_residual_not_atomic(account) {
                    Ok(outcome) => outcome,
                    Err(error) => {
                        let mode = decode_market_mode(self.header.mode)?;
                        let reason = self.header.recovery_reason.try_to_runtime()?;
                        V16Core::kernel_commit_declared_liquidation_recovery(error, mode, reason)?
                    }
                };
                AutoCrankOutcomeV16::Progressed(progressed)
            }
            AutoCrankPlanV16::DeclareRecovery { reason } => {
                // recovery declaration needs no observation.
                AutoCrankOutcomeV16::Progressed(self.permissionless_crank_not_atomic(
                    account,
                    PermissionlessCrankRequestV16 {
                        now_slot: work.now_slot,
                        asset_index: 0,
                        effective_price: 0,
                        funding_rate_e9: 0,
                        action: PermissionlessCrankActionV16::Recover(reason),
                    },
                )?)
            }
            AutoCrankPlanV16::FinalizeRecovery => return Err(V16Error::InvalidConfig),
            AutoCrankPlanV16::CloseResolved => {
                self.advance_resolved_slot_not_atomic(work.now_slot)?;
                AutoCrankOutcomeV16::ResolvedClose(self.close_resolved_account_not_atomic(
                    account,
                    work.resolved_close_fee_rate_per_slot,
                )?)
            }
        };
        Ok(AutoCrankResultV16 {
            selected: plan,
            outcome,
        })
    }

    pub fn permissionless_crank_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        request: PermissionlessCrankRequestV16,
    ) -> V16Result<PermissionlessProgressOutcomeV16> {
        self.validate_unconfigured_market_tail()?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live
            && !matches!(request.action, PermissionlessCrankActionV16::Recover(_))
        {
            return Err(V16Error::LockActive);
        }
        let protective_progress = match request.action {
            PermissionlessCrankActionV16::Refresh => {
                let selected_leg_before = request.asset_index
                    < self.header.config.max_market_slots.get() as usize
                    && Self::active_leg_slot_for_asset(&account.as_view(), request.asset_index)?
                        .is_some();
                match self.refresh_account_and_certify_not_atomic(
                    account,
                    Some((request.asset_index, request.effective_price)),
                    self.header.config.public_b_chunk_atoms.get(),
                    true,
                )? {
                    AccountRefreshCertOutcomeV16::Certified(_) => {}
                    AccountRefreshCertOutcomeV16::BChunk(out) => {
                        self.validate_shape_audit_scan()?;
                        return Ok(PermissionlessProgressOutcomeV16::AccountBChunk(out));
                    }
                    AccountRefreshCertOutcomeV16::SourceBackingExpired(domain) => {
                        self.validate_shape_audit_scan()?;
                        return Ok(PermissionlessProgressOutcomeV16::SourceBackingExpired {
                            domain,
                        });
                    }
                }
                let selected_leg_after = request.asset_index
                    < self.header.config.max_market_slots.get() as usize
                    && Self::active_leg_slot_for_asset(&account.as_view(), request.asset_index)?
                        .is_some();
                if V16Core::kernel_refresh_detached_selected_leg(
                    selected_leg_before,
                    selected_leg_after,
                ) {
                    self.validate_shape_audit_scan()?;
                    return Ok(PermissionlessProgressOutcomeV16::AccountCurrent);
                }
                selected_leg_before
            }
            PermissionlessCrankActionV16::SettleB { asset_index } => {
                let out = self.settle_account_b_chunk(
                    account,
                    asset_index,
                    self.header.config.public_b_chunk_atoms.get(),
                )?;
                return Ok(PermissionlessProgressOutcomeV16::AccountBChunk(out));
            }
            PermissionlessCrankActionV16::Liquidate(_) => {
                if let PermissionlessCrankActionV16::Liquidate(liq) = request.action {
                    let liquidated_asset_index = liq.asset_index;
                    // A liquidation whose only bounded terminal is Recovery declares
                    // it and then returns RecoveryRequired. Propagating that error
                    // would roll the declaration back on SVM, so the account never
                    // moves. Convert it to progress -- but ONLY when this same call
                    // left a complete Recovery marker behind.
                    if let Err(error) = self.liquidate_account_not_atomic(account, liq) {
                        let mode = decode_market_mode(self.header.mode)?;
                        let reason = self.header.recovery_reason.try_to_runtime()?;
                        return V16Core::kernel_commit_declared_liquidation_recovery(
                            error, mode, reason,
                        );
                    }
                    liquidated_asset_index == request.asset_index
                } else {
                    unreachable!()
                }
            }
            PermissionlessCrankActionV16::Recover(reason) => {
                return self.declare_permissionless_recovery(reason);
            }
        };
        self.accrue_asset_to_not_atomic(
            request.asset_index,
            request.now_slot,
            request.effective_price,
            request.funding_rate_e9,
            protective_progress,
        )?;
        Ok(PermissionlessProgressOutcomeV16::AccountCurrent)
    }

    /// Refresh a Recovery leg from committed engine state without attempting
    /// oracle accrual. Recovery freezes the asset's mark/funding trajectory, but
    /// accounts must still crystallize already-committed K/F/B and source-expiry
    /// work before their owners can submit matched risk-reducing trades.
    fn refresh_recovery_account_from_committed_state_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        now_slot: u64,
    ) -> V16Result<PermissionlessProgressOutcomeV16> {
        self.validate_unconfigured_market_tail()?;
        if now_slot < self.header.current_slot.get()
            || self.asset_state(asset_index)?.lifecycle != AssetLifecycleV16::Recovery
            || Self::active_leg_slot_for_asset(&account.as_view(), asset_index)?.is_none()
        {
            return Err(V16Error::NonProgress);
        }

        // Classification uses the authenticated execution slot. Normalize the
        // same first expired source before the legacy refresh helper, which
        // otherwise consults only the committed market slot.
        if let Some(domain) =
            self.first_lapsed_source_backing_for_account_at_slot(&account.as_view(), now_slot)?
        {
            self.expire_source_backing_bucket_not_atomic(domain, now_slot)?;
            self.validate_shape_audit_scan()?;
            account.validate_with_market(&self.as_view())?;
            return Ok(PermissionlessProgressOutcomeV16::SourceBackingExpired { domain });
        }

        let outcome = match self.refresh_account_and_certify_not_atomic(
            account,
            None,
            self.header.config.public_b_chunk_atoms.get(),
            true,
        )? {
            AccountRefreshCertOutcomeV16::Certified(_) => {
                PermissionlessProgressOutcomeV16::AccountCurrent
            }
            AccountRefreshCertOutcomeV16::BChunk(chunk) => {
                PermissionlessProgressOutcomeV16::AccountBChunk(chunk)
            }
            AccountRefreshCertOutcomeV16::SourceBackingExpired(domain) => {
                PermissionlessProgressOutcomeV16::SourceBackingExpired { domain }
            }
        };
        self.validate_shape_audit_scan()?;
        account.validate_with_market(&self.as_view())?;
        Ok(outcome)
    }

    fn active_leg_slot_for_asset(
        account: &PortfolioV16View<'_>,
        asset_index: usize,
    ) -> V16Result<Option<usize>> {
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let mut found = None;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            if active_bitmap_get(bitmap, slot) {
                let leg = account.header.legs[slot].try_to_runtime()?;
                if !leg.active {
                    return Err(V16Error::HiddenLeg);
                }
                if leg.asset_index as usize == asset_index {
                    if found.is_some() {
                        return Err(V16Error::HiddenLeg);
                    }
                    found = Some(slot);
                }
            }
            slot += 1;
        }
        Ok(found)
    }

    fn require_active_leg_slot_for_asset(
        account: &PortfolioV16View<'_>,
        asset_index: usize,
    ) -> V16Result<usize> {
        Self::active_leg_slot_for_asset(account, asset_index)?.ok_or(V16Error::InvalidLeg)
    }

    fn active_leg_for_asset(
        account: &PortfolioV16View<'_>,
        asset_index: usize,
    ) -> V16Result<PortfolioLegV16> {
        if let Some(slot) = Self::active_leg_slot_for_asset(account, asset_index)? {
            account.header.legs[slot].try_to_runtime()
        } else {
            Ok(PortfolioLegV16::EMPTY)
        }
    }

    fn asset_state(&self, asset_index: usize) -> V16Result<AssetStateV16> {
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
        {
            return Err(V16Error::InvalidLeg);
        }
        self.markets[asset_index].engine.asset.try_to_runtime()
    }

    fn set_asset_state(&mut self, asset_index: usize, asset: AssetStateV16) -> V16Result<()> {
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
        {
            return Err(V16Error::InvalidLeg);
        }
        let old_blockers =
            slot_resolved_payout_blockers_v16(self.markets[asset_index].engine_slot())?;
        let new_blockers = {
            let slot = self.markets[asset_index].engine_slot_mut();
            let old_asset = slot.asset;
            slot.asset = AssetStateV16Account::from_runtime(&asset);
            match slot_resolved_payout_blockers_v16(slot) {
                Ok(value) => value,
                Err(err) => {
                    slot.asset = old_asset;
                    return Err(err);
                }
            }
        };
        self.update_resolved_payout_blocker_total(old_blockers, new_blockers)?;
        Ok(())
    }

    fn require_asset_risk_change_allowed(
        &self,
        asset_index: usize,
        risk_increasing: bool,
    ) -> V16Result<()> {
        if !risk_increasing {
            return Ok(());
        }
        let asset = self.asset_state(asset_index)?;
        if asset.a_long != ADL_ONE || asset.a_short != ADL_ONE {
            return Err(V16Error::LockActive);
        }
        asset_risk_increase_gate(asset.lifecycle, asset.mode_long, asset.mode_short)
    }

    fn require_position_route_adl_safe(
        &self,
        asset_index: usize,
        route: PositionRouteV16,
        current: i128,
        new: i128,
    ) -> V16Result<()> {
        if V16Core::kernel_position_route_requires_unit_adl(route, current, new) {
            self.require_asset_risk_change_allowed(asset_index, true)?;
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_require_position_change_adl_safe(
        &self,
        asset_index: usize,
        current: i128,
        new: i128,
    ) -> V16Result<()> {
        let route = V16Core::kernel_classify_position_delta(current, new);
        self.require_position_route_adl_safe(asset_index, route, current, new)
    }

    #[cfg(kani)]
    pub fn kani_require_asset_risk_change_allowed(
        &self,
        asset_index: usize,
        risk_increasing: bool,
    ) -> V16Result<()> {
        self.require_asset_risk_change_allowed(asset_index, risk_increasing)
    }

    fn validate_configured_asset_index(&self, asset_index: usize) -> V16Result<()> {
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
        {
            return Err(V16Error::InvalidLeg);
        }
        Ok(())
    }

    #[inline]
    fn validate_unconfigured_market_tail(&self) -> V16Result<()> {
        MarketGroupV16HeaderAccount::validate_dynamic_market_slots_len_static(
            self.markets.len(),
            self.header.asset_slot_capacity.get() as usize,
            self.header.config.max_market_slots.get() as usize,
        )?;
        #[cfg(any(test, kani, feature = "audit-scan"))]
        {
            self.header
                .validate_dynamic_market_slots_shape(self.markets)?;
        }
        Ok(())
    }

    fn checked_asset_set_epoch_bump(&self) -> V16Result<(u64, u64)> {
        let next_asset_set_epoch = self
            .header
            .asset_set_epoch
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        let next_risk_epoch = self
            .header
            .risk_epoch
            .get()
            .checked_add(1)
            .ok_or(V16Error::CounterOverflow)?;
        Ok((next_asset_set_epoch, next_risk_epoch))
    }

    fn commit_asset_set_epoch_bump(&mut self, next_asset_set_epoch: u64, next_risk_epoch: u64) {
        self.header.asset_set_epoch = V16PodU64::new(next_asset_set_epoch);
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
    }

    fn asset_restart_next_counters(
        next_market_id_before: u64,
        activation_count_before: u64,
        asset_set_epoch_before: u64,
        risk_epoch_before: u64,
    ) -> V16Result<(u64, u64, u64, u64)> {
        Ok((
            next_market_id_before
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
            activation_count_before
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
            asset_set_epoch_before
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
            risk_epoch_before
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
        ))
    }

    fn restarted_asset_slot_preserving_insurance_budget(
        old_slot: &EngineAssetSlotV16Account,
        market_id: u64,
        authenticated_price: u64,
        now_slot: u64,
    ) -> EngineAssetSlotV16Account {
        let mut asset = AssetStateV16::default();
        asset.market_id = market_id;
        asset.lifecycle = AssetLifecycleV16::Active;
        asset.raw_oracle_target_price = authenticated_price;
        asset.effective_price = authenticated_price;
        asset.fund_px_last = authenticated_price;
        asset.slot_last = now_slot;
        let mut restarted = EngineAssetSlotV16Account::empty_for_market(market_id);
        restarted.asset = AssetStateV16Account::from_runtime(&asset);
        restarted.insurance_domain_budget_long = old_slot.insurance_domain_budget_long;
        restarted.insurance_domain_budget_short = old_slot.insurance_domain_budget_short;
        restarted
    }

    fn canonical_retired_asset_slot(old_asset: AssetStateV16) -> EngineAssetSlotV16Account {
        let mut canonical_asset = AssetStateV16::default();
        canonical_asset.market_id = old_asset.market_id;
        canonical_asset.retired_slot = old_asset.retired_slot;
        canonical_asset.lifecycle = AssetLifecycleV16::Retired;
        canonical_asset.raw_oracle_target_price = old_asset.raw_oracle_target_price;
        canonical_asset.effective_price = old_asset.effective_price;
        canonical_asset.fund_px_last = old_asset.fund_px_last;
        canonical_asset.slot_last = old_asset.slot_last;
        let mut canonical_slot = EngineAssetSlotV16Account::empty_for_market(old_asset.market_id);
        canonical_slot.asset = AssetStateV16Account::from_runtime(&canonical_asset);
        canonical_slot
    }

    #[cfg(kani)]
    pub fn kani_asset_restart_next_counters(
        next_market_id_before: u64,
        activation_count_before: u64,
        asset_set_epoch_before: u64,
        risk_epoch_before: u64,
    ) -> V16Result<(u64, u64, u64, u64)> {
        Self::asset_restart_next_counters(
            next_market_id_before,
            activation_count_before,
            asset_set_epoch_before,
            risk_epoch_before,
        )
    }

    #[cfg(kani)]
    pub fn kani_restarted_asset_slot_preserving_insurance_budget(
        old_slot: &EngineAssetSlotV16Account,
        market_id: u64,
        authenticated_price: u64,
        now_slot: u64,
    ) -> EngineAssetSlotV16Account {
        Self::restarted_asset_slot_preserving_insurance_budget(
            old_slot,
            market_id,
            authenticated_price,
            now_slot,
        )
    }

    #[cfg(kani)]
    pub fn kani_canonical_retired_asset_slot(
        old_asset: AssetStateV16,
    ) -> EngineAssetSlotV16Account {
        Self::canonical_retired_asset_slot(old_asset)
    }

    fn require_asset_live_reducible(&self, asset_index: usize) -> V16Result<()> {
        let asset = self.asset_state(asset_index)?;
        match asset.lifecycle {
            AssetLifecycleV16::Active | AssetLifecycleV16::DrainOnly => Ok(()),
            _ => Err(V16Error::LockActive),
        }
    }

    fn require_empty_asset_lifecycle_state(&self, asset_index: usize) -> V16Result<()> {
        self.require_empty_asset_lifecycle_state_with_policy(
            asset_index,
            false,
            false,
            false,
            false,
        )
    }

    fn require_empty_asset_lifecycle_state_with_policy(
        &self,
        asset_index: usize,
        allow_terminal_spent_budget: bool,
        allow_terminal_social_loss_audit: bool,
        allow_terminal_source_spent_audit: bool,
        allow_terminal_price_funding_history: bool,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        let asset = self.asset_state(asset_index)?;
        let long_domain = self.insurance_domain_index(asset_index, SideV16::Long)?;
        let short_domain = self.insurance_domain_index(asset_index, SideV16::Short)?;
        let long_bucket = self.backing_bucket_for_domain(long_domain)?;
        let short_bucket = self.backing_bucket_for_domain(short_domain)?;
        let long_source = self.source_credit_for_domain_shape(long_domain)?;
        let short_source = self.source_credit_for_domain_shape(short_domain)?;
        let long_reservation = self.insurance_reservation_for_domain(long_domain)?;
        let short_reservation = self.insurance_reservation_for_domain(short_domain)?;
        let slot = self.markets[asset_index].engine_slot();
        let long_budget = slot.insurance_domain_budget_long.get();
        let long_spent = slot.insurance_domain_spent_long.get();
        let short_budget = slot.insurance_domain_budget_short.get();
        let short_spent = slot.insurance_domain_spent_short.get();
        let spent_blocks_empty = if allow_terminal_spent_budget {
            (long_spent != 0 && long_budget != long_spent)
                || (short_spent != 0 && short_budget != short_spent)
        } else {
            long_spent != 0 || short_spent != 0
        };

        if slot.pending_domain_loss_barrier_long.get() != 0
            || slot.pending_domain_loss_barrier_short.get() != 0
            || asset.mode_long != SideModeV16::Normal
            || asset.mode_short != SideModeV16::Normal
            || !((asset.a_long == ADL_ONE && asset.a_short == ADL_ONE)
                || (asset.a_long == 0 && asset.a_short == 0))
            || (!allow_terminal_price_funding_history
                && (asset.k_long != 0
                    || asset.k_short != 0
                    || asset.f_long_num != 0
                    || asset.f_short_num != 0
                    || asset.k_epoch_start_long != 0
                    || asset.k_epoch_start_short != 0
                    || asset.f_epoch_start_long_num != 0
                    || asset.f_epoch_start_short_num != 0))
            || asset.b_long_num != 0
            || asset.b_short_num != 0
            || asset.b_epoch_start_long_num != 0
            || asset.b_epoch_start_short_num != 0
            || asset.oi_eff_long_q != 0
            || asset.oi_eff_short_q != 0
            || asset.stored_pos_count_long != 0
            || asset.stored_pos_count_short != 0
            || asset.stale_account_count_long != 0
            || asset.stale_account_count_short != 0
            || asset.pending_obligation_count_long != 0
            || asset.pending_obligation_count_short != 0
            || asset.loss_weight_sum_long != 0
            || asset.loss_weight_sum_short != 0
            || (!allow_terminal_social_loss_audit
                && (asset.social_loss_remainder_long_num != 0
                    || asset.social_loss_remainder_short_num != 0
                    || asset.social_loss_dust_long_num != 0
                    || asset.social_loss_dust_short_num != 0
                    || asset.explicit_unallocated_loss_long != 0
                    || asset.explicit_unallocated_loss_short != 0))
            || spent_blocks_empty
            || !(if allow_terminal_source_spent_audit {
                long_source.is_terminal_spent_audit_only_shape()
            } else {
                long_source.is_empty_amount_shape()
            })
            || !(if allow_terminal_source_spent_audit {
                short_source.is_terminal_spent_audit_only_shape()
            } else {
                short_source.is_empty_amount_shape()
            })
            || !long_bucket.is_empty_amount_shape()
            || !short_bucket.is_empty_amount_shape()
            || long_bucket.market_id != asset.market_id
            || short_bucket.market_id != asset.market_id
            || long_reservation != InsuranceCreditReservationV16::EMPTY
            || short_reservation != InsuranceCreditReservationV16::EMPTY
        {
            return Err(V16Error::LockActive);
        }
        Ok(())
    }

    fn side_mode_for(&self, asset_index: usize, side: SideV16) -> V16Result<SideModeV16> {
        let asset = self.asset_state(asset_index)?;
        Ok(match side {
            SideV16::Long => asset.mode_long,
            SideV16::Short => asset.mode_short,
        })
    }

    pub fn finalize_side_reset_not_atomic(
        &mut self,
        asset_index: usize,
        side: SideV16,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        let pending_barrier = self.pending_domain_loss_barrier_count(asset_index, side)?;
        let mut asset = self.asset_state(asset_index)?;
        match side {
            SideV16::Long => match asset.mode_long {
                SideModeV16::Normal => return Ok(()),
                SideModeV16::DrainOnly => return Err(V16Error::LockActive),
                SideModeV16::ResetPending => {
                    if asset.stored_pos_count_long != 0
                        || asset.stale_account_count_long != 0
                        || asset.pending_obligation_count_long != 0
                        || pending_barrier != 0
                    {
                        return Err(V16Error::Stale);
                    }
                    asset.k_epoch_start_long = 0;
                    asset.f_epoch_start_long_num = 0;
                    asset.b_epoch_start_long_num = 0;
                    asset.mode_long = SideModeV16::Normal;
                }
            },
            SideV16::Short => match asset.mode_short {
                SideModeV16::Normal => return Ok(()),
                SideModeV16::DrainOnly => return Err(V16Error::LockActive),
                SideModeV16::ResetPending => {
                    if asset.stored_pos_count_short != 0
                        || asset.stale_account_count_short != 0
                        || asset.pending_obligation_count_short != 0
                        || pending_barrier != 0
                    {
                        return Err(V16Error::Stale);
                    }
                    asset.k_epoch_start_short = 0;
                    asset.f_epoch_start_short_num = 0;
                    asset.b_epoch_start_short_num = 0;
                    asset.mode_short = SideModeV16::Normal;
                }
            },
        }
        self.set_asset_state(asset_index, asset)?;
        self.header.risk_epoch = V16PodU64::new(
            self.header
                .risk_epoch
                .get()
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
        );
        self.as_view().validate_header_aggregate_totals()?;
        self.validate_shape_audit_scan()
    }

    fn account_b_loss_bound(account: &PortfolioV16View<'_>) -> V16Result<u128> {
        let mut bound = 0u128;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active && leg.b_stale {
                bound = bound
                    .checked_add(leg.loss_weight)
                    .ok_or(V16Error::ArithmeticOverflow)?;
            }
            slot += 1;
        }
        Ok(bound)
    }

    fn risk_score_unchecked(&self, account: &PortfolioV16View<'_>) -> V16Result<RiskScoreV16> {
        let cert = account.header.health_cert.try_to_runtime()?;
        if !cert.valid {
            return Err(V16Error::Stale);
        }
        Ok(RiskScoreV16 {
            certified_liq_deficit: cert.certified_liq_deficit,
            unsettled_b_loss_bound: Self::account_b_loss_bound(account)?,
            stale_loss_bound: if decode_bool(account.header.stale_state)? {
                1
            } else {
                0
            },
            gross_risk_notional: cert.certified_worst_case_loss,
            active_leg_count: active_bitmap_count_ones(
                account.header.active_bitmap.map(V16PodU64::get),
            ),
        })
    }

    #[inline(never)]
    fn validate_liquidation_progress_from_score(
        &self,
        before_score: RiskScoreV16,
        after: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        let after_score = self.risk_score_unchecked(after)?;
        if V16Core::liquidation_progress_from_scores(before_score, after_score) {
            Ok(())
        } else {
            Err(V16Error::NonProgress)
        }
    }

    fn ensure_favorable_action_current_certificate(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        let cert = account.header.health_cert.try_to_runtime()?;
        if !V16Core::kernel_cert_is_current(
            cert,
            self.header.oracle_epoch.get(),
            self.header.funding_epoch.get(),
            self.header.risk_epoch.get(),
            self.header.asset_set_epoch.get(),
            account.header.active_bitmap.map(V16PodU64::get),
        ) {
            return Err(V16Error::Stale);
        }
        Ok(())
    }

    fn account_has_target_effective_lag(&self, account: &PortfolioV16View<'_>) -> V16Result<bool> {
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active && self.asset_has_target_effective_lag(leg.asset_index as usize)? {
                return Ok(true);
            }
            slot += 1;
        }
        Ok(false)
    }

    fn ensure_favorable_action_allowed(&self, account: &PortfolioV16View<'_>) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        if self.h_lock_lane(
            Some(account),
            false,
            #[cfg(feature = "fork-facade")]
            None, // A-1: non-trade caller; threshold not applicable
        )? == HLockLaneV16::HMax
        {
            return Err(V16Error::LockActive);
        }
        self.ensure_favorable_action_current_certificate(account)?;
        if self.account_has_target_effective_lag(account)? {
            return Err(V16Error::LockActive);
        }
        Ok(())
    }

    fn account_has_active_exposure_for_source_domain(
        &self,
        account: &PortfolioV16View<'_>,
        domain: usize,
    ) -> V16Result<bool> {
        let (asset_index, source_side) = self.domain_asset_side(domain)?;
        let leg = Self::active_leg_for_asset(account, asset_index)?;
        Ok(leg.active && opposite_side(leg.side) == source_side)
    }

    fn account_has_active_source_claim_exposure(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<bool> {
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.source_domains()[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if source.is_occupied() && source.source_claim_bound_num.get() != 0 {
                let d = source.domain.get() as usize;
                if self.domain_asset_side(d).is_ok()
                    && self.account_has_active_exposure_for_source_domain(account, d)?
                {
                    return Ok(true);
                }
            }
            slot += 1;
        }
        Ok(false)
    }

    #[cfg(kani)]
    pub fn kani_convert_source_claim_exposure_guard(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<bool> {
        Ok(Self::account_has_source_claims(account)?
            && self.account_has_active_source_claim_exposure(account)?)
    }

    fn pending_domain_loss_barrier_count(
        &self,
        asset_index: usize,
        side: SideV16,
    ) -> V16Result<u64> {
        let domain = self.insurance_domain_index(asset_index, side)?;
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot();
        Ok(match side {
            SideV16::Long => slot.pending_domain_loss_barrier_long.get(),
            SideV16::Short => slot.pending_domain_loss_barrier_short.get(),
        })
    }

    fn has_pending_domain_loss_barrier(
        &self,
        asset_index: usize,
        side: SideV16,
    ) -> V16Result<bool> {
        Ok(self.pending_domain_loss_barrier_count(asset_index, side)? != 0)
    }

    fn account_touches_pending_domain_loss_barrier(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<bool> {
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active
                && self.has_pending_domain_loss_barrier(leg.asset_index as usize, leg.side)?
            {
                return Ok(true);
            }
            slot += 1;
        }
        Ok(false)
    }

    fn position_change_touches_pending_domain_loss_barrier(
        &self,
        asset_index: usize,
        current: i128,
        next: i128,
    ) -> V16Result<bool> {
        if current != 0 {
            let current_side = if current > 0 {
                SideV16::Long
            } else {
                SideV16::Short
            };
            if self.has_pending_domain_loss_barrier(asset_index, current_side)? {
                return Ok(true);
            }
        }
        if next != 0 {
            let next_side = if next > 0 {
                SideV16::Long
            } else {
                SideV16::Short
            };
            if self.has_pending_domain_loss_barrier(asset_index, next_side)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    #[cfg(kani)]
    pub fn kani_position_change_touches_pending_domain_loss_barrier(
        &self,
        asset_index: usize,
        current: i128,
        next: i128,
    ) -> V16Result<bool> {
        self.position_change_touches_pending_domain_loss_barrier(asset_index, current, next)
    }

    fn position_delta_touches_pending_domain_loss_barrier(
        &self,
        account: &PortfolioV16View<'_>,
        asset_index: usize,
        delta_q: i128,
    ) -> V16Result<bool> {
        if delta_q == 0 {
            return Ok(false);
        }
        let current = signed_position(Self::active_leg_for_asset(account, asset_index)?);
        let next = current
            .checked_add(delta_q)
            .ok_or(V16Error::ArithmeticOverflow)?;
        validate_basis_or_zero(next)?;
        self.position_change_touches_pending_domain_loss_barrier(asset_index, current, next)
    }

    fn position_delta_blocked_by_pending_domain_loss_barrier(
        &self,
        account: &PortfolioV16View<'_>,
        asset_index: usize,
        delta_q: i128,
    ) -> V16Result<bool> {
        let current = signed_position(Self::active_leg_for_asset(account, asset_index)?);
        let next = current
            .checked_add(delta_q)
            .ok_or(V16Error::ArithmeticOverflow)?;
        validate_basis_or_zero(next)?;
        Ok(pending_domain_loss_barrier_blocks_position_change(
            self.position_change_touches_pending_domain_loss_barrier(asset_index, current, next)?,
            current,
            next,
        ))
    }

    fn h_lock_lane(
        &self,
        account: Option<&PortfolioV16View<'_>>,
        instruction_bankruptcy_candidate: bool,
        // fork feature A-1: per-trade admit-threshold (None = toly baseline).
        // Gated under fork-facade; the production path (None) is zero-overhead.
        #[cfg(feature = "fork-facade")] instruction_threshold_bps_opt: Option<u128>,
    ) -> V16Result<HLockLaneV16> {
        let account_scoped = account.is_some();
        let bankruptcy_hlock_active = decode_bool(self.header.bankruptcy_hlock_active)?;
        if let Some(account) = account {
            if decode_bool(account.header.liquidation_lock)?
                || decode_bool(account.header.stale_state)?
                || decode_bool(account.header.b_stale_state)?
                || self.account_has_loss_stale_live_leg(account)?
            {
                return Ok(HLockLaneV16::HMax);
            }
            if account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual()
            {
                return Ok(HLockLaneV16::HMax);
            }
            if self.account_touches_pending_domain_loss_barrier(account)? {
                return Ok(HLockLaneV16::HMax);
            }
        }
        if decode_bool(self.header.threshold_stress_active)?
            || (!account_scoped && bankruptcy_hlock_active)
            || decode_market_mode(self.header.mode)? == MarketModeV16::Recovery
            || instruction_bankruptcy_candidate
        {
            return Ok(HLockLaneV16::HMax);
        }
        // fork feature A-1: lift lane to HMax when the per-trade caller has
        // opted into a stress-consumption threshold and the persisted A-6
        // accumulator has reached it. `None` preserves toly baseline.
        #[cfg(feature = "fork-facade")]
        if let Some(threshold) = instruction_threshold_bps_opt {
            if self.header.stress_consumption_bps_e9_since_envelope.get() >= threshold {
                return Ok(HLockLaneV16::HMax);
            }
        }
        Ok(HLockLaneV16::HMin)
    }

    #[cfg(kani)]
    pub fn kani_h_lock_lane(
        &self,
        account: Option<&PortfolioV16View<'_>>,
        instruction_bankruptcy_candidate: bool,
    ) -> V16Result<HLockLaneV16> {
        self.h_lock_lane(
            account,
            instruction_bankruptcy_candidate,
            #[cfg(feature = "fork-facade")]
            None,
        )
    }

    /// fork-facade (A-1): kani/test shim that exposes the threshold parameter.
    #[cfg(all(kani, feature = "fork-facade"))]
    pub fn kani_h_lock_lane_with_threshold(
        &self,
        account: Option<&PortfolioV16View<'_>>,
        instruction_bankruptcy_candidate: bool,
        threshold_bps_opt: Option<u128>,
    ) -> V16Result<HLockLaneV16> {
        self.h_lock_lane(account, instruction_bankruptcy_candidate, threshold_bps_opt)
    }

    fn asset_has_target_effective_lag(&self, asset_index: usize) -> V16Result<bool> {
        let asset = self.asset_state(asset_index)?;
        Ok(asset.raw_oracle_target_price != asset.effective_price)
    }

    fn asset_is_loss_stale(&self, asset_index: usize) -> V16Result<bool> {
        let asset = self.asset_state(asset_index)?;
        Ok(asset_is_loss_stale_at_slot(
            asset,
            self.header.current_slot.get(),
        ))
    }

    fn account_has_loss_stale_live_leg(&self, account: &PortfolioV16View<'_>) -> V16Result<bool> {
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            if active_bitmap_get(bitmap, slot) {
                let leg = account.header.legs[slot].try_to_runtime()?;
                if !leg.active {
                    return Err(V16Error::HiddenLeg);
                }
                if self.asset_is_loss_stale(leg.asset_index as usize)? {
                    return Ok(true);
                }
            }
            slot += 1;
        }
        Ok(false)
    }

    fn can_ignore_unrelated_loss_stale_for_trade(
        &self,
        long_account: &PortfolioV16View<'_>,
        short_account: &PortfolioV16View<'_>,
        asset_index: usize,
    ) -> V16Result<bool> {
        if !decode_bool(self.header.loss_stale_active)? {
            return Ok(false);
        }
        Ok(V16Core::loss_stale_trade_scope_allowed(
            true,
            self.asset_is_loss_stale(asset_index)?,
            self.account_has_loss_stale_live_leg(long_account)?,
            self.account_has_loss_stale_live_leg(short_account)?,
        ))
    }

    #[cfg(kani)]
    pub fn kani_can_ignore_unrelated_loss_stale_for_trade(
        &self,
        long_account: &PortfolioV16View<'_>,
        short_account: &PortfolioV16View<'_>,
        asset_index: usize,
    ) -> V16Result<bool> {
        self.can_ignore_unrelated_loss_stale_for_trade(long_account, short_account, asset_index)
    }

    fn account_fee_anchor_for_loss_currentness(
        &self,
        account: &PortfolioV16View<'_>,
        now_slot: u64,
    ) -> V16Result<u64> {
        let mut anchor = now_slot;
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            if active_bitmap_get(bitmap, slot) {
                let leg = account.header.legs[slot].try_to_runtime()?;
                if !leg.active {
                    return Err(V16Error::HiddenLeg);
                }
                let asset = self.asset_state(leg.asset_index as usize)?;
                if asset_contributes_to_loss_stale_summary(asset) {
                    anchor = anchor.min(asset.slot_last);
                }
            }
            slot += 1;
        }
        Ok(anchor)
    }

    fn validate_trade_request(&self, request: TradeRequestV16) -> V16Result<()> {
        let config = self.header.config.try_to_runtime_shape()?;
        let size_q = Self::trade_request_abs_size_q(request)?;
        if request.asset_index >= config.max_market_slots as usize
            || size_q > MAX_TRADE_SIZE_Q
            || request.exec_price == 0
            || request.exec_price > MAX_ORACLE_PRICE
            || request.fee_bps > config.max_trading_fee_bps
        {
            return Err(V16Error::InvalidConfig);
        }
        Ok(())
    }

    fn trade_request_abs_size_q(request: TradeRequestV16) -> V16Result<u128> {
        let (size_q, _, _) = Self::trade_signed_size_deltas(request.size_q)?;
        Ok(size_q)
    }

    fn trade_signed_size_deltas(size_q: i128) -> V16Result<(u128, i128, i128)> {
        if size_q == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let abs_size_q = size_q.unsigned_abs();
        if abs_size_q > MAX_TRADE_SIZE_Q {
            return Err(V16Error::InvalidConfig);
        }
        let opposite_delta = size_q.checked_neg().ok_or(V16Error::ArithmeticOverflow)?;
        Ok((abs_size_q, size_q, opposite_delta))
    }

    #[cfg(kani)]
    pub fn kani_trade_signed_size_deltas(size_q: i128) -> V16Result<(u128, i128, i128)> {
        Self::trade_signed_size_deltas(size_q)
    }

    fn validate_trade_position_preflight(
        &self,
        long_account: &PortfolioV16View<'_>,
        short_account: &PortfolioV16View<'_>,
        request: TradeRequestV16,
        long_lookup: PositionDeltaLookupV16,
        short_lookup: PositionDeltaLookupV16,
    ) -> V16Result<TradePositionPreflightV16> {
        Self::trade_signed_size_deltas(request.size_q)?;
        let long_risk_increasing = long_lookup.next_effective_q.unsigned_abs()
            > long_lookup.current_effective_q.unsigned_abs();
        let short_risk_increasing = short_lookup.next_effective_q.unsigned_abs()
            > short_lookup.current_effective_q.unsigned_abs();
        let risk_increasing = long_risk_increasing || short_risk_increasing;
        let preflight_asset = self.asset_state(request.asset_index)?;
        kernel_trade_preexisting_oi_reduction_gate(
            preflight_asset.oi_eff_long_q,
            preflight_asset.oi_eff_short_q,
            long_lookup.current_effective_q,
            long_lookup.next_effective_q,
            short_lookup.current_effective_q,
            short_lookup.next_effective_q,
        )?;
        let target_effective_lag = self.asset_has_target_effective_lag(request.asset_index)?;
        let blocked_by_pending_domain_barrier = pending_domain_loss_barrier_blocks_position_change(
            self.position_change_touches_pending_domain_loss_barrier(
                request.asset_index,
                long_lookup.current_effective_q,
                long_lookup.next_effective_q,
            )?,
            long_lookup.current_effective_q,
            long_lookup.next_effective_q,
        )
            || pending_domain_loss_barrier_blocks_position_change(
                self.position_change_touches_pending_domain_loss_barrier(
                    request.asset_index,
                    short_lookup.current_effective_q,
                    short_lookup.next_effective_q,
                )?,
                short_lookup.current_effective_q,
                short_lookup.next_effective_q,
            );
        trade_preflight_risk_gate(
            risk_increasing,
            self.asset_is_loss_stale(request.asset_index)?,
            target_effective_lag,
            blocked_by_pending_domain_barrier,
        )?;
        Ok(TradePositionPreflightV16 {
            risk_increasing,
            long_requires_initial_margin: trade_account_requires_initial_margin(
                long_lookup.current_effective_q,
                long_lookup.next_effective_q,
            ),
            short_requires_initial_margin: trade_account_requires_initial_margin(
                short_lookup.current_effective_q,
                short_lookup.next_effective_q,
            ),
            long_lookup,
            short_lookup,
            long_old_abs_q: long_lookup.current_effective_q.unsigned_abs(),
            short_old_abs_q: short_lookup.current_effective_q.unsigned_abs(),
            long_new_abs_q: long_lookup.next_effective_q.unsigned_abs(),
            short_new_abs_q: short_lookup.next_effective_q.unsigned_abs(),
            long_has_source_claims: Self::account_has_source_claims(long_account)?,
            short_has_source_claims: Self::account_has_source_claims(short_account)?,
        })
    }

    fn position_delta_lookup_for_asset(
        &self,
        account: &PortfolioV16View<'_>,
        asset_index: usize,
        delta_q: i128,
    ) -> V16Result<PositionDeltaLookupV16> {
        PositionSlotMapV16::from_account(account)?.plan_delta(
            asset_index,
            delta_q,
            self.asset_state(asset_index)?,
        )
    }

    fn attach_leg_at_slot(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        side: SideV16,
        basis_pos_q: i128,
        leg_slot: usize,
    ) -> V16Result<()> {
        if leg_slot >= V16_MAX_PORTFOLIO_ASSETS_N {
            return Err(V16Error::InvalidLeg);
        }
        let bitmap = account.header.active_bitmap.map(V16PodU64::get);
        let existing = account.header.legs[leg_slot].try_to_runtime()?;
        if active_bitmap_get(bitmap, leg_slot) || existing.active || !existing.is_empty() {
            return Err(V16Error::HiddenLeg);
        }
        if self.has_pending_domain_loss_barrier(asset_index, side)? {
            return Err(V16Error::LockActive);
        }
        validate_basis(basis_pos_q)?;
        let asset = self.asset_state(asset_index)?;
        self.require_asset_risk_change_allowed(asset_index, true)?;
        let a_basis = match side {
            SideV16::Long => asset.a_long,
            SideV16::Short => asset.a_short,
        };
        let loss_weight = loss_weight_for_basis(basis_pos_q.unsigned_abs(), a_basis)?;
        let (asset, new_leg) =
            V16Core::kernel_attach_leg(asset, side, basis_pos_q, loss_weight, asset_index as u32)?;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&new_leg);
        let mut bitmap = account.header.active_bitmap.map(V16PodU64::get);
        active_bitmap_set(&mut bitmap, leg_slot)?;
        account.header.active_bitmap = bitmap.map(V16PodU64::new);
        account.header.health_cert.valid = 0;
        self.set_asset_state(asset_index, asset)?;
        Ok(())
    }

    fn leg_is_prior_reset_obligation(asset: AssetStateV16, leg: PortfolioLegV16) -> bool {
        let (side_mode, asset_epoch) = match leg.side {
            SideV16::Long => (asset.mode_long, asset.epoch_long),
            SideV16::Short => (asset.mode_short, asset.epoch_short),
        };
        V16Core::kernel_is_prior_reset_obligation(side_mode, asset_epoch, leg.epoch_snap)
    }

    fn recovery_pending_obligation_release_allowed(
        &self,
        asset_index: usize,
        side: SideV16,
    ) -> V16Result<bool> {
        let asset = self.asset_state(asset_index)?;
        let (opposite_stored_count, opposite_pending_count) = match opposite_side(side) {
            SideV16::Long => (
                asset.stored_pos_count_long,
                asset.pending_obligation_count_long,
            ),
            SideV16::Short => (
                asset.stored_pos_count_short,
                asset.pending_obligation_count_short,
            ),
        };
        V16Core::kernel_recovery_pending_obligation_release_allowed(
            asset.lifecycle,
            opposite_stored_count,
            opposite_pending_count,
        )
    }

    fn retain_leg_as_pending_obligation(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
    ) -> V16Result<()> {
        let leg_slot = Self::require_active_leg_slot_for_asset(&account.as_view(), asset_index)?;
        let leg = account.header.legs[leg_slot].try_to_runtime()?;
        let asset = self.asset_state(asset_index)?;
        if Self::leg_is_prior_reset_obligation(asset, leg) {
            return Err(V16Error::InvalidLeg);
        }
        if leg.b_stale || leg.stale {
            return Err(V16Error::Stale);
        }
        let (k_target, f_target) = self.kf_target_for_leg(asset_index, leg)?;
        if !Self::leg_kf_epoch_is_current(asset, leg)
            || k_target != leg.k_snap
            || f_target != leg.f_snap
            || self.b_target_for_leg(asset_index, leg)? != leg.b_snap
        {
            return Err(V16Error::Stale);
        }
        let effective_abs_q = V16Core::effective_abs_quantity_for_leg(asset, leg)?;
        let (leg, asset) =
            V16Core::kernel_retain_leg_as_pending_obligation(leg, asset, effective_abs_q)?;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&leg);
        account.header.health_cert.valid = 0;
        self.set_asset_state(asset_index, asset)
    }

    fn retain_recovery_loss_weight_before_detach(
        &self,
        asset_index: usize,
        leg: PortfolioLegV16,
    ) -> V16Result<bool> {
        if Self::leg_is_prior_reset_obligation(self.asset_state(asset_index)?, leg) {
            return Ok(false);
        }
        Ok(self.has_pending_domain_loss_barrier(asset_index, leg.side)?
            || !self.recovery_pending_obligation_release_allowed(asset_index, leg.side)?)
    }

    fn clear_leg(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
    ) -> V16Result<()> {
        self.clear_leg_inner(account, asset_index, false)
    }

    fn clear_leg_inner(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        allow_attributed_terminal_trade: bool,
    ) -> V16Result<()> {
        let leg_slot = Self::require_active_leg_slot_for_asset(&account.as_view(), asset_index)?;
        self.clear_leg_at_slot_inner(
            account,
            asset_index,
            leg_slot,
            allow_attributed_terminal_trade,
            None,
        )
    }

    fn clear_leg_at_slot_inner(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        leg_slot: usize,
        allow_attributed_terminal_trade: bool,
        clear_effective_oi_q: Option<u128>,
    ) -> V16Result<()> {
        if leg_slot >= V16_MAX_PORTFOLIO_ASSETS_N {
            return Err(V16Error::InvalidLeg);
        }
        let leg = account.header.legs[leg_slot].try_to_runtime()?;
        if !active_bitmap_get(account.header.active_bitmap.map(V16PodU64::get), leg_slot)
            || !leg.active
            || leg.asset_index as usize != asset_index
            || leg.b_stale
            || leg.stale
        {
            return Err(V16Error::InvalidLeg);
        }
        let remaining_active_bitmap =
            active_bitmap_with_cleared(account.header.active_bitmap.map(V16PodU64::get), leg_slot)?;
        // Account PnL is cross-margin and does not retain negative-loss provenance.
        // Preserve that fact across the detach so later liquidation can reduce
        // risk without charging the selected surviving asset domain.
        if uncovered_loss_remains_with_open_risk(
            account.header.pnl.get(),
            account.header.capital.get(),
            remaining_active_bitmap,
        ) {
            account.header.liquidation_lock = encode_bool(true);
            account.header.health_cert.valid = 0;
        }
        let close_progress = account.header.close_progress.try_to_runtime()?;
        if close_progress.has_pending_residual() {
            let attributed_terminal_trade = allow_attributed_terminal_trade
                && close_progress.asset_index as usize == asset_index
                && close_progress.domain_side == opposite_side(leg.side);
            if !attributed_terminal_trade {
                return Err(V16Error::LockActive);
            }
        }
        if self.has_pending_domain_loss_barrier(asset_index, leg.side)? {
            return Err(V16Error::LockActive);
        }
        let asset = self.asset_state(asset_index)?;
        let (k_target, f_target) = Self::kf_target_for_leg_from_asset(asset, leg)?;
        if !Self::leg_kf_epoch_is_current(asset, leg)
            || k_target != leg.k_snap
            || f_target != leg.f_snap
        {
            return Err(V16Error::Stale);
        }
        if self.b_target_for_leg(asset_index, leg)? != leg.b_snap {
            return Err(V16Error::Stale);
        }
        let clear_effective_oi_q = match clear_effective_oi_q {
            Some(value) => value,
            None => V16Core::effective_abs_quantity_for_leg(asset, leg)?,
        };
        let asset = V16Core::kernel_clear_leg(leg, asset, clear_effective_oi_q)?;
        account.header.legs[leg_slot] =
            PortfolioLegV16Account::from_runtime(&PortfolioLegV16::EMPTY);
        let mut bitmap = account.header.active_bitmap.map(V16PodU64::get);
        active_bitmap_clear(&mut bitmap, leg_slot)?;
        account.header.active_bitmap = bitmap.map(V16PodU64::new);
        account.header.health_cert.valid = 0;
        self.set_asset_state(asset_index, asset)?;
        Ok(())
    }

    fn apply_position_delta(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        delta_q: i128,
    ) -> V16Result<()> {
        if delta_q == 0 {
            return Ok(());
        }
        let lookup =
            self.position_delta_lookup_for_asset(&account.as_view(), asset_index, delta_q)?;
        let raw_delta_q = lookup
            .next_q
            .checked_sub(lookup.current_q)
            .ok_or(V16Error::ArithmeticOverflow)?;
        self.apply_position_delta_with_lookup(account, asset_index, raw_delta_q, lookup)
    }

    fn apply_position_delta_with_lookup(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        delta_q: i128,
        lookup: PositionDeltaLookupV16,
    ) -> V16Result<()> {
        self.apply_position_delta_with_lookup_inner(account, asset_index, delta_q, lookup, false)
    }

    fn apply_current_position_delta_with_lookup(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        delta_q: i128,
        lookup: PositionDeltaLookupV16,
    ) -> V16Result<()> {
        self.apply_position_delta_with_lookup_inner(account, asset_index, delta_q, lookup, true)
    }

    fn apply_position_delta_with_lookup_inner(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        delta_q: i128,
        lookup: PositionDeltaLookupV16,
        allow_attributed_terminal_trade: bool,
    ) -> V16Result<()> {
        if delta_q == 0 {
            return Ok(());
        }
        let expected_next = lookup
            .current_q
            .checked_add(delta_q)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if expected_next != lookup.next_q {
            return Err(V16Error::InvalidLeg);
        }
        validate_basis_or_zero(lookup.next_q)?;
        let existing_slot = lookup.existing_slot;
        let current_leg = if let Some(existing_slot) = existing_slot {
            let leg = account.header.legs[existing_slot].try_to_runtime()?;
            if !leg.active || leg.asset_index as usize != asset_index {
                return Err(V16Error::HiddenLeg);
            }
            let asset = self.asset_state(asset_index)?;
            let (k_target, f_target) = Self::kf_target_for_leg_from_asset(asset, leg)?;
            if !Self::leg_kf_epoch_is_current(asset, leg)
                || k_target != leg.k_snap
                || f_target != leg.f_snap
            {
                return Err(V16Error::Stale);
            }
            leg
        } else {
            PortfolioLegV16::EMPTY
        };
        let current = signed_position(current_leg);
        if current != lookup.current_q {
            return Err(V16Error::HiddenLeg);
        }
        let new = lookup.next_q;
        let current_effective = lookup.current_effective_q;
        let new_effective = lookup.next_effective_q;
        if pending_domain_loss_barrier_blocks_position_change(
            self.position_change_touches_pending_domain_loss_barrier(
                asset_index,
                current_effective,
                new_effective,
            )?,
            current_effective,
            new_effective,
        ) {
            return Err(V16Error::LockActive);
        }
        // PRODUCTION KERNEL: classify the route (Attach/Clear/Flip/Resize) — the
        // exact decision this body dispatches on, factored out and contracted.
        let route = V16Core::kernel_classify_position_delta(current_effective, new_effective);
        self.require_position_route_adl_safe(asset_index, route, current_effective, new_effective)?;
        if route == PositionRouteV16::Attach {
            let side = if new > 0 {
                SideV16::Long
            } else {
                SideV16::Short
            };
            let leg_slot = lookup.empty_slot.ok_or(V16Error::InvalidLeg)?;
            return self.attach_leg_at_slot(account, asset_index, side, new, leg_slot);
        }
        let leg_slot = existing_slot.ok_or(V16Error::InvalidLeg)?;
        if route == PositionRouteV16::Clear {
            let leg = current_leg;
            if leg.active && self.has_pending_domain_loss_barrier(asset_index, leg.side)? {
                let asset = self.asset_state(asset_index)?;
                let effective_abs_q = V16Core::effective_abs_quantity_for_leg(asset, leg)?;
                let (obligation, asset) =
                    V16Core::kernel_retain_leg_as_pending_obligation(leg, asset, effective_abs_q)?;
                account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&obligation);
                account.header.health_cert.valid = 0;
                self.set_asset_state(asset_index, asset)?;
                return Ok(());
            }
            return self.clear_leg_at_slot_inner(
                account,
                asset_index,
                leg_slot,
                allow_attributed_terminal_trade,
                Some(lookup.current_effective_q.unsigned_abs()),
            );
        }
        if route == PositionRouteV16::Flip {
            self.clear_leg_at_slot_inner(account, asset_index, leg_slot, false, None)?;
            let side = if new > 0 {
                SideV16::Long
            } else {
                SideV16::Short
            };
            let empty_slot = lookup.empty_slot.ok_or(V16Error::InvalidLeg)?;
            return self.attach_leg_at_slot(account, asset_index, side, new, empty_slot);
        }
        let preserve_pending_obligation_weight =
            same_side_risk_reduction_or_flat_obligation(current_effective, new_effective)
                && self.has_pending_domain_loss_barrier(asset_index, current_leg.side)?;
        self.resize_leg_same_side_at_slot(
            account,
            asset_index,
            leg_slot,
            new,
            preserve_pending_obligation_weight,
            current_effective.unsigned_abs(),
            new_effective.unsigned_abs(),
        )
    }

    #[inline(never)]
    fn resize_leg_same_side_at_slot(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        leg_slot: usize,
        new: i128,
        preserve_pending_obligation_weight: bool,
        old_effective_abs: u128,
        new_effective_abs: u128,
    ) -> V16Result<()> {
        let old_leg = account.header.legs[leg_slot].try_to_runtime()?;
        let new_weight = loss_weight_for_basis(new.unsigned_abs(), old_leg.a_basis)?;
        let asset = self.asset_state(asset_index)?;
        let (new_leg, new_asset) = V16Core::kernel_resize_leg_same_side(
            old_leg,
            asset,
            new,
            new_weight,
            preserve_pending_obligation_weight,
            old_effective_abs,
            new_effective_abs,
        )?;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&new_leg);
        account.header.health_cert.valid = 0;
        self.set_asset_state(asset_index, new_asset)?;
        Ok(())
    }

    fn set_pending_domain_loss_barrier_count(
        &mut self,
        asset_index: usize,
        side: SideV16,
        value: u64,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        let slot = self.markets[asset_index].engine_slot();
        let old_blockers = slot_resolved_payout_blockers_v16(slot)?;
        let old_value = match side {
            SideV16::Long => slot.pending_domain_loss_barrier_long.get(),
            SideV16::Short => slot.pending_domain_loss_barrier_short.get(),
        };
        let new_blockers = old_blockers
            .checked_sub(old_value)
            .and_then(|v| v.checked_add(value))
            .ok_or(V16Error::CounterOverflow)?;
        self.update_resolved_payout_blocker_total(old_blockers, new_blockers)?;

        let slot = self.markets[asset_index].engine_slot_mut();
        match side {
            SideV16::Long => slot.pending_domain_loss_barrier_long = V16PodU64::new(value),
            SideV16::Short => slot.pending_domain_loss_barrier_short = V16PodU64::new(value),
        }
        Ok(())
    }

    fn begin_close_progress_ledger(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        domain_side: SideV16,
        gross_loss: u128,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        if gross_loss == 0 {
            return Ok(());
        }
        let current = account.header.close_progress.try_to_runtime()?;
        if !current.close_slot_available() {
            return Err(V16Error::LockActive);
        }
        let domain = self.insurance_domain_index(asset_index, domain_side)?;
        if self.pending_domain_loss_barrier_count(asset_index, domain_side)? != 0 {
            return Err(V16Error::LockActive);
        }
        let close_id = current.close_id.saturating_add(1).max(1);
        let asset = self.asset_state(asset_index)?;
        let ledger = CloseProgressLedgerV16 {
            active: true,
            finalized: false,
            close_id,
            asset_index: u32::try_from(asset_index).map_err(|_| V16Error::InvalidLeg)?,
            market_id: asset.market_id,
            domain_side,
            gross_loss_at_close_start: gross_loss,
            drift_reference_slot: self.header.current_slot.get(),
            max_close_slot: self
                .header
                .current_slot
                .get()
                .checked_add(self.header.config.max_bankrupt_close_lifetime_slots.get())
                .ok_or(V16Error::ArithmeticOverflow)?,
            residual_remaining: gross_loss,
            ..CloseProgressLedgerV16::EMPTY
        };
        account.header.close_progress = CloseProgressLedgerV16Account::from_runtime(&ledger);
        let count = self.pending_domain_loss_barrier_count(asset_index, domain_side)?;
        self.set_pending_domain_loss_barrier_count(
            asset_index,
            domain_side,
            count.checked_add(1).ok_or(V16Error::CounterOverflow)?,
        )?;
        self.domain_asset_side(domain)?;
        self.validate_account_audit_scan(&account.as_view())
    }

    fn ensure_close_progress_not_expired(
        &mut self,
        ledger: CloseProgressLedgerV16,
    ) -> V16Result<()> {
        if ledger.active && self.header.current_slot.get() > ledger.max_close_slot {
            if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
                return Ok(());
            }
            self.declare_permissionless_recovery(
                PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
            )?;
            return Err(V16Error::RecoveryRequired);
        }
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_ensure_close_progress_not_expired(
        &mut self,
        ledger: CloseProgressLedgerV16,
    ) -> V16Result<()> {
        self.ensure_close_progress_not_expired(ledger)
    }

    fn ensure_open_close_snapshot_current_or_recovery(
        &mut self,
        account: &PortfolioV16View<'_>,
        ledger: CloseProgressLedgerV16,
    ) -> V16Result<()> {
        if !ledger.active {
            return Ok(());
        }
        let asset_index = ledger.asset_index as usize;
        if asset_index < self.header.config.max_market_slots.get() as usize
            && V16Core::kernel_open_close_snapshot_is_stale(
                Self::active_leg_slot_for_asset(account, asset_index)?.is_some(),
                self.asset_state(asset_index)?.slot_last,
                ledger.drift_reference_slot,
            )
        {
            if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
                return Ok(());
            }
            self.declare_permissionless_recovery(
                PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
            )?;
            return Err(V16Error::RecoveryRequired);
        }
        Ok(())
    }

    fn advance_close_progress_ledger(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        support_consumed: u128,
        junior_face_burned: u128,
        insurance_spent: u128,
        b_loss_booked: u128,
        explicit_loss_assigned: u128,
    ) -> V16Result<()> {
        if support_consumed == 0
            && junior_face_burned == 0
            && insurance_spent == 0
            && b_loss_booked == 0
            && explicit_loss_assigned == 0
        {
            return Ok(());
        }
        let mut ledger = account.header.close_progress.try_to_runtime()?;
        self.ensure_close_progress_not_expired(ledger)?;
        let was_pending = ledger.has_pending_residual();
        let domain_side = ledger.domain_side;
        let asset_index = ledger.asset_index as usize;
        if !ledger.active || ledger.finalized {
            return Err(V16Error::LockActive);
        }
        let ledger_advanced = V16Core::kernel_advance_close_ledger(
            ledger,
            support_consumed,
            junior_face_burned,
            insurance_spent,
            b_loss_booked,
            explicit_loss_assigned,
        )?;
        let mut ledger = ledger_advanced;
        let _ = &mut ledger;
        if was_pending && !ledger.has_pending_residual() {
            let count = self.pending_domain_loss_barrier_count(asset_index, domain_side)?;
            self.set_pending_domain_loss_barrier_count(
                asset_index,
                domain_side,
                count.checked_sub(1).ok_or(V16Error::CounterUnderflow)?,
            )?;
        }
        account.header.close_progress = CloseProgressLedgerV16Account::from_runtime(&ledger);
        account.header.health_cert.valid = 0;
        account.validate_with_market(&self.as_view())
    }

    fn bankruptcy_residual_single_step_capacity(
        &self,
        asset_index: usize,
        bankrupt_side: SideV16,
        residual_remaining: u128,
    ) -> V16Result<u128> {
        self.validate_configured_asset_index(asset_index)?;
        if residual_remaining == 0 {
            return Ok(0);
        }
        let opp = opposite_side(bankrupt_side);
        let asset = self.asset_state(asset_index)?;
        let (b_now, weight_sum, rem) = match opp {
            SideV16::Long => (
                asset.b_long_num,
                asset.loss_weight_sum_long,
                asset.social_loss_remainder_long_num,
            ),
            SideV16::Short => (
                asset.b_short_num,
                asset.loss_weight_sum_short,
                asset.social_loss_remainder_short_num,
            ),
        };
        if weight_sum == 0 {
            return Ok(0);
        }
        let candidate = residual_remaining.min(self.header.config.public_b_chunk_atoms.get());
        if candidate != 0 {
            if let Some(delta_b) = candidate
                .checked_mul(SOCIAL_LOSS_DEN)
                .and_then(|v| v.checked_add(rem))
                .map(|v| v / weight_sum)
            {
                if delta_b != 0 && b_now.checked_add(delta_b).is_some() {
                    return Ok(candidate);
                }
            }
        }
        let headroom_plus_one = U256::from_u128(u128::MAX - b_now)
            .checked_add(U256::ONE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let max_scaled = headroom_plus_one
            .checked_mul(U256::from_u128(weight_sum))
            .and_then(|v| v.checked_sub(U256::ONE))
            .ok_or(V16Error::ArithmeticOverflow)?;
        if U256::from_u128(rem) > max_scaled {
            return Ok(0);
        }
        let max_chunk_by_b_wide = max_scaled
            .checked_sub(U256::from_u128(rem))
            .and_then(|v| v.checked_div(U256::from_u128(SOCIAL_LOSS_DEN)))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let max_chunk_by_b = max_chunk_by_b_wide
            .try_into_u128()
            .unwrap_or(residual_remaining);
        Ok(residual_remaining
            .min(max_chunk_by_b)
            .min(self.header.config.public_b_chunk_atoms.get()))
    }

    #[cfg(kani)]
    pub fn kani_bankruptcy_residual_single_step_capacity(
        &self,
        asset_index: usize,
        bankrupt_side: SideV16,
        residual_remaining: u128,
    ) -> V16Result<u128> {
        self.bankruptcy_residual_single_step_capacity(
            asset_index,
            bankrupt_side,
            residual_remaining,
        )
    }

    fn book_bankruptcy_residual_chunk_internal(
        &mut self,
        asset_index: usize,
        bankrupt_side: SideV16,
        residual_remaining: u128,
    ) -> V16Result<BResidualBookingOutcomeV16> {
        self.validate_configured_asset_index(asset_index)?;
        if residual_remaining == 0 {
            return Ok(BResidualBookingOutcomeV16 {
                booked_loss: 0,
                explicit_loss: 0,
                delta_b: 0,
                remaining_after: 0,
            });
        }
        let opp = opposite_side(bankrupt_side);
        let asset = self.asset_state(asset_index)?;
        let weight_sum = match opp {
            SideV16::Long => asset.loss_weight_sum_long,
            SideV16::Short => asset.loss_weight_sum_short,
        };
        if weight_sum == 0 {
            if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
                self.header.bankruptcy_hlock_active = 1;
                return Ok(BResidualBookingOutcomeV16 {
                    booked_loss: 0,
                    explicit_loss: residual_remaining,
                    delta_b: 0,
                    remaining_after: 0,
                });
            }
            self.declare_permissionless_recovery(
                PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
            )?;
            return Err(V16Error::RecoveryRequired);
        }
        let engine_chunk = self.bankruptcy_residual_single_step_capacity(
            asset_index,
            bankrupt_side,
            residual_remaining,
        )?;
        if engine_chunk == 0 {
            if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
                self.header.bankruptcy_hlock_active = 1;
                return Ok(BResidualBookingOutcomeV16 {
                    booked_loss: 0,
                    explicit_loss: residual_remaining,
                    delta_b: 0,
                    remaining_after: 0,
                });
            }
            self.declare_permissionless_recovery(
                PermissionlessRecoveryReasonV16::BIndexHeadroomExhausted,
            )?;
            return Err(V16Error::RecoveryRequired);
        }
        let mut asset = asset;
        if let Some(outcome) = Self::apply_bankruptcy_residual_chunk_to_loss_side(
            &mut asset,
            opp,
            engine_chunk,
            residual_remaining,
        )? {
            self.set_asset_state(asset_index, asset)?;
            self.header.bankruptcy_hlock_active = 1;
            return Ok(outcome);
        }
        if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
            self.header.bankruptcy_hlock_active = 1;
            return Ok(BResidualBookingOutcomeV16 {
                booked_loss: 0,
                explicit_loss: residual_remaining,
                delta_b: 0,
                remaining_after: 0,
            });
        }
        self.declare_permissionless_recovery(
            PermissionlessRecoveryReasonV16::BIndexHeadroomExhausted,
        )?;
        Err(V16Error::RecoveryRequired)
    }

    fn apply_bankruptcy_residual_chunk_to_loss_side(
        asset: &mut AssetStateV16,
        opp: SideV16,
        engine_chunk: u128,
        residual_remaining: u128,
    ) -> V16Result<Option<BResidualBookingOutcomeV16>> {
        if engine_chunk == 0 || engine_chunk > residual_remaining {
            return Ok(None);
        }
        let (b_now, weight_sum, rem) = match opp {
            SideV16::Long => (
                asset.b_long_num,
                asset.loss_weight_sum_long,
                asset.social_loss_remainder_long_num,
            ),
            SideV16::Short => (
                asset.b_short_num,
                asset.loss_weight_sum_short,
                asset.social_loss_remainder_short_num,
            ),
        };
        if weight_sum == 0 {
            return Ok(None);
        }
        let numerator = engine_chunk
            .checked_mul(SOCIAL_LOSS_DEN)
            .and_then(|v| v.checked_add(rem))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let delta_b = numerator / weight_sum;
        let new_rem = numerator % weight_sum;
        if delta_b == 0 || b_now.checked_add(delta_b).is_none() {
            return Ok(None);
        }
        match opp {
            SideV16::Long => {
                asset.b_long_num = asset
                    .b_long_num
                    .checked_add(delta_b)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                asset.social_loss_remainder_long_num = new_rem;
            }
            SideV16::Short => {
                asset.b_short_num = asset
                    .b_short_num
                    .checked_add(delta_b)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                asset.social_loss_remainder_short_num = new_rem;
            }
        }
        Ok(Some(BResidualBookingOutcomeV16 {
            booked_loss: engine_chunk,
            explicit_loss: 0,
            delta_b,
            remaining_after: residual_remaining - engine_chunk,
        }))
    }

    #[cfg(kani)]
    pub fn kani_book_bankruptcy_residual_chunk_internal(
        &mut self,
        asset_index: usize,
        bankrupt_side: SideV16,
        residual_remaining: u128,
    ) -> V16Result<BResidualBookingOutcomeV16> {
        self.book_bankruptcy_residual_chunk_internal(asset_index, bankrupt_side, residual_remaining)
    }

    #[cfg(kani)]
    pub fn kani_apply_bankruptcy_residual_chunk_to_loss_side(
        asset: &mut AssetStateV16,
        opp: SideV16,
        engine_chunk: u128,
        residual_remaining: u128,
    ) -> V16Result<Option<BResidualBookingOutcomeV16>> {
        Self::apply_bankruptcy_residual_chunk_to_loss_side(
            asset,
            opp,
            engine_chunk,
            residual_remaining,
        )
    }

    fn book_bankruptcy_residual_chunk_for_account_core(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        bankrupt_side: SideV16,
        residual_remaining: u128,
    ) -> V16Result<BResidualBookingOutcomeV16> {
        if residual_remaining == 0 {
            return Ok(BResidualBookingOutcomeV16 {
                booked_loss: 0,
                explicit_loss: 0,
                delta_b: 0,
                remaining_after: 0,
            });
        }
        let domain_side = opposite_side(bankrupt_side);
        // Defence in depth: every caller of this function already opens a close
        // when the gross loss is non-zero, so a finalized-inert ledger is not
        // reachable here today. Asking the same question as the sibling site keeps
        // the two consistent if that ever changes. The capacity pre-flight stays on
        // this branch so a residual with no bookable capacity still routes to
        // recovery rather than erroring.
        if account
            .header
            .close_progress
            .try_to_runtime()?
            .close_slot_available()
        {
            if self.bankruptcy_residual_single_step_capacity(
                asset_index,
                bankrupt_side,
                residual_remaining,
            )? == 0
            {
                self.declare_permissionless_recovery(
                    PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
                )?;
                return Err(V16Error::RecoveryRequired);
            }
            self.begin_close_progress_ledger(
                account,
                asset_index,
                domain_side,
                residual_remaining,
            )?;
        }
        let ledger = account.header.close_progress.try_to_runtime()?;
        self.ensure_close_progress_not_expired(ledger)?;
        if ledger.asset_index as usize != asset_index || ledger.domain_side != domain_side {
            return Err(V16Error::LockActive);
        }
        self.ensure_open_close_snapshot_current_or_recovery(&account.as_view(), ledger)?;
        let outcome = self.book_bankruptcy_residual_chunk_internal(
            asset_index,
            bankrupt_side,
            ledger.residual_remaining,
        )?;
        self.advance_close_progress_ledger(
            account,
            0,
            0,
            0,
            outcome.booked_loss,
            outcome.explicit_loss,
        )?;
        Ok(outcome)
    }

    fn advance_pending_close_residual_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<PermissionlessProgressOutcomeV16> {
        account.validate_with_market(&self.as_view())?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let ledger_before = account.header.close_progress.try_to_runtime()?;
        if !ledger_before.has_pending_residual() {
            return Err(V16Error::NonProgress);
        }
        self.ensure_close_progress_not_expired(ledger_before)?;
        let asset_index = ledger_before.asset_index as usize;
        let bankrupt_side = opposite_side(ledger_before.domain_side);

        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        let insurance_used =
            self.consume_domain_insurance_for_negative_pnl(asset_index, bankrupt_side, account)?;
        if insurance_used != 0 {
            self.advance_close_progress_ledger(account, 0, 0, insurance_used, 0, 0)?;
        }

        let residual = if account.header.pnl.get() < 0 {
            account.header.pnl.get().unsigned_abs()
        } else {
            0
        };
        let outcome = if residual != 0 {
            let outcome = self.book_bankruptcy_residual_chunk_for_account_core(
                account,
                asset_index,
                bankrupt_side,
                residual,
            )?;
            let new_pnl = V16Core::kernel_settle_resolved_pnl_after_booking(
                account.header.pnl.get(),
                outcome.booked_loss,
                outcome.explicit_loss,
            )?;
            self.set_account_pnl(account, new_pnl)?;
            PermissionlessProgressOutcomeV16::ResidualBooked(outcome)
        } else {
            PermissionlessProgressOutcomeV16::AccountCurrent
        };

        let ledger_after = account.header.close_progress.try_to_runtime()?;
        if ledger_after.residual_remaining >= ledger_before.residual_remaining {
            return Err(V16Error::NonProgress);
        }
        self.validate_account_audit_scan(&account.as_view())?;
        self.validate_shape_audit_scan()?;
        Ok(outcome)
    }

    fn begin_full_drain_reset_inner(&mut self, asset_index: usize, side: SideV16) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        if self.has_pending_domain_loss_barrier(asset_index, side)? {
            return Err(V16Error::LockActive);
        }
        let asset = V16Core::kernel_begin_full_drain_reset(self.asset_state(asset_index)?, side)?;
        self.set_asset_state(asset_index, asset)?;
        self.header.risk_epoch = V16PodU64::new(
            self.header
                .risk_epoch
                .get()
                .checked_add(1)
                .ok_or(V16Error::CounterOverflow)?,
        );
        Ok(())
    }

    fn begin_zero_oi_residue_resets(&mut self, asset_index: usize) -> V16Result<()> {
        let asset = self.asset_state(asset_index)?;
        let reset_long = asset.oi_eff_long_q == 0
            && asset.pending_obligation_count_long == 0
            && asset.mode_long != SideModeV16::ResetPending
            && (asset.stored_pos_count_long != 0 || asset.a_long != ADL_ONE);
        let reset_short = asset.oi_eff_short_q == 0
            && asset.pending_obligation_count_short == 0
            && asset.mode_short != SideModeV16::ResetPending
            && (asset.stored_pos_count_short != 0 || asset.a_short != ADL_ONE);
        if reset_long {
            self.begin_full_drain_reset_inner(asset_index, SideV16::Long)?;
        }
        if reset_short {
            self.begin_full_drain_reset_inner(asset_index, SideV16::Short)?;
        }
        Ok(())
    }

    fn unilateral_close_capacity(
        &self,
        asset_index: usize,
        leg: PortfolioLegV16,
    ) -> V16Result<u128> {
        let asset = self.asset_state(asset_index)?;
        let account_effective_q = V16Core::effective_abs_quantity_for_leg(asset, leg)?;
        Ok(V16Core::kernel_unilateral_close_capacity(
            account_effective_q,
            asset.oi_eff_long_q,
            asset.oi_eff_short_q,
        ))
    }

    fn begin_side_reset_if_effective_oi_exhausted(
        &mut self,
        asset_index: usize,
        side: SideV16,
    ) -> V16Result<()> {
        let asset = self.asset_state(asset_index)?;
        let exhausted = match side {
            SideV16::Long => {
                asset.oi_eff_long_q == 0
                    && asset.stored_pos_count_long != 0
                    && asset.pending_obligation_count_long == 0
                    && asset.mode_long != SideModeV16::ResetPending
            }
            SideV16::Short => {
                asset.oi_eff_short_q == 0
                    && asset.stored_pos_count_short != 0
                    && asset.pending_obligation_count_short == 0
                    && asset.mode_short != SideModeV16::ResetPending
            }
        };
        if exhausted && !self.has_pending_domain_loss_barrier(asset_index, side)? {
            self.begin_full_drain_reset_inner(asset_index, side)?;
        }
        Ok(())
    }

    fn reduce_matching_open_interest_for_unilateral_close(
        &mut self,
        asset_index: usize,
        closed_side: SideV16,
        close_q: u128,
    ) -> V16Result<()> {
        if close_q == 0 {
            return Ok(());
        }
        let opp = opposite_side(closed_side);
        let mut asset = self.asset_state(asset_index)?;
        let (opp_oi_before, opp_a_before) = match opp {
            SideV16::Long => (asset.oi_eff_long_q, asset.a_long),
            SideV16::Short => (asset.oi_eff_short_q, asset.a_short),
        };
        if close_q > opp_oi_before {
            return Err(V16Error::InvalidLeg);
        }
        let opp_oi_after = opp_oi_before - close_q;
        let opp_a_after = if opp_oi_after == 0 {
            ADL_ONE
        } else {
            let candidate = wide_mul_div_floor_u128(opp_a_before, opp_oi_after, opp_oi_before);
            if candidate == 0 {
                self.declare_permissionless_recovery(
                    PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
                )?;
                return Err(V16Error::RecoveryRequired);
            }
            candidate
        };
        match opp {
            SideV16::Long => {
                asset.oi_eff_long_q = opp_oi_after;
                asset.a_long = opp_a_after;
                if opp_oi_after != 0 && asset.a_long < MIN_A_SIDE {
                    asset.mode_long = SideModeV16::DrainOnly;
                }
            }
            SideV16::Short => {
                asset.oi_eff_short_q = opp_oi_after;
                asset.a_short = opp_a_after;
                if opp_oi_after != 0 && asset.a_short < MIN_A_SIDE {
                    asset.mode_short = SideModeV16::DrainOnly;
                }
            }
        }
        self.set_asset_state(asset_index, asset)?;
        if opp_oi_after == 0 {
            self.begin_full_drain_reset_inner(asset_index, opp)?;
        }
        Ok(())
    }

    fn reduce_position(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        close_q: u128,
    ) -> V16Result<()> {
        if close_q == 0 {
            return Ok(());
        }
        let leg = Self::active_leg_for_asset(&account.as_view(), asset_index)?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let close_i128 = i128::try_from(close_q).map_err(|_| V16Error::ArithmeticOverflow)?;
        let delta = match leg.side {
            SideV16::Long => close_i128
                .checked_neg()
                .ok_or(V16Error::ArithmeticOverflow)?,
            SideV16::Short => close_i128,
        };
        self.apply_position_delta(account, asset_index, delta)?;
        self.begin_side_reset_if_effective_oi_exhausted(asset_index, leg.side)?;
        self.reduce_matching_open_interest_for_unilateral_close(asset_index, leg.side, close_q)
    }

    pub fn liquidate_account_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        request: LiquidationRequestV16,
    ) -> V16Result<LiquidationOutcomeV16> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let config = self.header.config.try_to_runtime_shape()?;
        if request.asset_index >= config.max_market_slots as usize {
            return Err(V16Error::InvalidConfig);
        }
        // FIX E3 (upstream #92): fee rate is CONFIG-only, never a caller hint.
        let fee_bps = config.liquidation_fee_bps;
        self.require_asset_live_reducible(request.asset_index)?;
        self.validate_account_scalar_preflight(&account.as_view())?;
        Self::require_active_leg_slot_for_asset(&account.as_view(), request.asset_index)?;
        match self.refresh_account_and_certify_not_atomic(
            account,
            None,
            self.header.config.public_b_chunk_atoms.get(),
            false,
        )? {
            AccountRefreshCertOutcomeV16::Certified(_) => {}
            AccountRefreshCertOutcomeV16::BChunk(_) => return Err(V16Error::BStale),
            AccountRefreshCertOutcomeV16::SourceBackingExpired(_) => return Err(V16Error::Stale),
        }
        let cert = account.header.health_cert.try_to_runtime()?;
        if cert.certified_liq_deficit == 0 {
            return Err(V16Error::NonProgress);
        }
        let before_score = self.risk_score_unchecked(&account.as_view())?;
        let leg_slot =
            Self::require_active_leg_slot_for_asset(&account.as_view(), request.asset_index)?;
        let leg = account.header.legs[leg_slot].try_to_runtime()?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let asset = self.asset_state(request.asset_index)?;
        let account_effective_q = V16Core::effective_abs_quantity_for_leg(asset, leg)?;
        // FIX E3 (upstream #92): liquidation size is engine-selected -- close
        // just enough to restore maintenance health when a healthy partial
        // close exists, otherwise close the leg fully. `.min` below is
        // defense in depth: `liquidation_engine_close_request_q` already
        // returns a value in `[1, account_effective_q]`.
        let close_request_q = liquidation_engine_close_request_q(
            config,
            cert,
            account.header.capital.get(),
            account.header.pnl.get(),
            leg.side,
            account_effective_q,
            asset.effective_price,
            asset.raw_oracle_target_price,
            fee_bps,
        )?;
        let close_budget =
            close_request_q.min(self.unilateral_close_capacity(request.asset_index, leg)?);
        if close_budget == 0 {
            return Err(V16Error::NonProgress);
        }
        let (close_q, close_delta) =
            V16Core::kernel_reduce_position_delta(leg.basis_pos_q, leg.side, close_budget)?;
        if self.position_delta_touches_pending_domain_loss_barrier(
            &account.as_view(),
            request.asset_index,
            close_delta,
        )? {
            return Err(V16Error::LockActive);
        }
        // A multi-asset deficit has no safe per-domain attribution in the
        // account-global PnL scalar. Permissionless liquidation can still remove
        // bounded risk, but it must not consume insurance or book B against the
        // selected surviving asset.
        if decode_bool(account.header.liquidation_lock)? {
            self.reduce_position(account, request.asset_index, close_q)?;
            self.certify_account_after_local_settlement_with_price_override(account, None)?;
            self.begin_zero_oi_residue_resets(request.asset_index)?;
            self.validate_liquidation_progress_from_score(before_score, &account.as_view())?;
            self.validate_shape_audit_scan()?;
            self.validate_account_audit_scan(&account.as_view())?;
            return Ok(LiquidationOutcomeV16 {
                closed_q: close_q,
                insurance_used: 0,
                residual_booked: 0,
                explicit_loss: 0,
                fee_charged: 0,
            });
        }
        let remaining_active_bitmap = liquidation_remaining_active_bitmap_after_close(
            account.header.active_bitmap.map(V16PodU64::get),
            leg_slot,
            close_q,
            account_effective_q,
        )?;
        if uncovered_loss_remains_with_open_risk(
            account.header.pnl.get(),
            account.header.capital.get(),
            remaining_active_bitmap,
        ) {
            self.declare_permissionless_recovery(
                PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
            )?;
            return Err(V16Error::RecoveryRequired);
        }
        self.preflight_liquidation_residual_durability(
            request.asset_index,
            leg.side,
            &account.as_view(),
        )?;
        let fee_notional = liquidation_risk_notional_ceil(close_q, asset.effective_price)?;
        let fee = liquidation_fee_for_close(
            fee_notional,
            fee_bps,
            config.min_liquidation_abs,
            config.liquidation_fee_cap,
            close_q == account_effective_q,
        )?;
        let charged_fee = self.charge_account_fee_not_atomic(account, fee)?;
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        let gross_bankruptcy_residual = if account.header.pnl.get() < 0 {
            account.header.pnl.get().unsigned_abs()
        } else {
            0
        };
        if gross_bankruptcy_residual != 0 {
            self.begin_close_progress_ledger(
                account,
                request.asset_index,
                opposite_side(leg.side),
                gross_bankruptcy_residual,
            )?;
        }
        let insurance_used =
            self.consume_domain_insurance_for_negative_pnl(request.asset_index, leg.side, account)?;
        if insurance_used != 0 {
            self.advance_close_progress_ledger(account, 0, 0, insurance_used, 0, 0)?;
        }
        // FIX-1: consume_domain_insurance_for_negative_pnl sets hlock=1 at entry (line 7758)
        // and then zeroes the account's negative PnL via set_account_pnl, which decrements
        // negative_pnl_account_count.  When insurance covers the full loss, all five
        // try_clear conditions are met at this point but the hlock was never cleared.
        // Call try_clear here so a full-insurance liquidation unblocks LP/insurance
        // withdrawals without requiring a separate FeeSweep transaction.
        self.try_clear_bankruptcy_hlock_if_healthy()?;
        let residual = if account.header.pnl.get() < 0 {
            account.header.pnl.get().unsigned_abs()
        } else {
            0
        };
        let mut booked = 0u128;
        let mut explicit = 0u128;
        if residual != 0 {
            let outcome = self.book_bankruptcy_residual_chunk_for_account_core(
                account,
                request.asset_index,
                leg.side,
                residual,
            )?;
            booked = outcome.booked_loss;
            explicit = outcome.explicit_loss;
            let cleared = booked
                .checked_add(explicit)
                .ok_or(V16Error::ArithmeticOverflow)?
                .min(residual);
            let cleared_i128 = i128::try_from(cleared).map_err(|_| V16Error::ArithmeticOverflow)?;
            let new_pnl = account
                .header
                .pnl
                .get()
                .checked_add(cleared_i128)
                .ok_or(V16Error::ArithmeticOverflow)?;
            self.set_account_pnl(account, new_pnl)?;
            self.header.bankruptcy_hlock_active = 1;
        }
        self.reduce_position(account, request.asset_index, close_q)?;
        self.certify_account_after_local_settlement_with_price_override(account, None)?;
        self.begin_zero_oi_residue_resets(request.asset_index)?;
        self.validate_liquidation_progress_from_score(before_score, &account.as_view())?;
        self.validate_shape_audit_scan()?;
        self.validate_account_audit_scan(&account.as_view())?;
        Ok(LiquidationOutcomeV16 {
            closed_q: close_q,
            insurance_used,
            residual_booked: booked,
            explicit_loss: explicit,
            fee_charged: charged_fee,
        })
    }

    pub fn rebalance_reduce_position_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        request: RebalanceRequestV16,
    ) -> V16Result<RebalanceOutcomeV16> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        if request.asset_index >= self.header.config.max_market_slots.get() as usize
            || request.reduce_q == 0
        {
            return Err(V16Error::InvalidConfig);
        }
        self.require_asset_live_reducible(request.asset_index)?;
        self.settle_account_side_effects_not_atomic(
            account,
            self.header.config.public_b_chunk_atoms.get(),
        )?;
        self.certify_account_after_local_settlement_with_price_override(account, None)?;
        let before_score = self.risk_score_unchecked(&account.as_view())?;
        let leg = Self::active_leg_for_asset(&account.as_view(), request.asset_index)?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        let reduce_budget = request
            .reduce_q
            .min(self.unilateral_close_capacity(request.asset_index, leg)?);
        let (reduce_q, reduce_delta) =
            V16Core::kernel_reduce_position_delta(leg.basis_pos_q, leg.side, reduce_budget)?;
        if reduce_q == 0 {
            return Err(V16Error::NonProgress);
        }
        if self.position_delta_blocked_by_pending_domain_loss_barrier(
            &account.as_view(),
            request.asset_index,
            reduce_delta,
        )? {
            return Err(V16Error::LockActive);
        }
        self.reduce_position(account, request.asset_index, reduce_q)?;
        // The entry validation and canonical reduction establish the core preconditions. The
        // following certification and audit-feature scans validate the resulting state.
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        self.certify_account_after_local_settlement_with_price_override(account, None)?;
        self.begin_zero_oi_residue_resets(request.asset_index)?;
        self.validate_liquidation_progress_from_score(before_score, &account.as_view())?;
        self.validate_shape_audit_scan()?;
        self.validate_account_audit_scan(&account.as_view())?;
        Ok(RebalanceOutcomeV16 {
            reduced_q: reduce_q,
        })
    }

    fn settle_account_for_position_action_and_refresh_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<HealthCertV16> {
        self.validate_account_scalar_preflight(&account.as_view())?;
        if !decode_bool(account.header.stale_state)?
            && !decode_bool(account.header.b_stale_state)?
            && self
                .ensure_favorable_action_current_certificate(&account.as_view())
                .is_ok()
            && !Self::has_b_stale_leg(&account.as_view())?
        {
            return account.header.health_cert.try_to_runtime();
        }
        match self.refresh_account_and_certify_not_atomic(account, None, 0, false)? {
            AccountRefreshCertOutcomeV16::Certified(cert) => Ok(cert),
            AccountRefreshCertOutcomeV16::BChunk(_) => Err(V16Error::BStale),
            AccountRefreshCertOutcomeV16::SourceBackingExpired(_) => Err(V16Error::Stale),
        }
    }

    fn ensure_initial_margin(account: &PortfolioV16View<'_>) -> V16Result<()> {
        let cert = account.header.health_cert.try_to_runtime()?;
        V16Core::kernel_initial_margin_gate(cert)
    }

    #[cfg(kani)]
    pub fn kani_ensure_initial_margin(account: &PortfolioV16View<'_>) -> V16Result<()> {
        Self::ensure_initial_margin(account)
    }

    #[cfg(kani)]
    pub fn kani_kernel_settle_positive_face_after_support(
        old_positive_face: u128,
        support_face_burned: u128,
        remaining_loss: u128,
    ) -> V16Result<(i128, u128)> {
        V16Core::kernel_settle_positive_face_after_support(
            old_positive_face,
            support_face_burned,
            remaining_loss,
        )
    }

    #[cfg(kani)]
    pub fn kani_kernel_released_pnl_conversion_partition(
        positive_face: u128,
        converted: u128,
        source_face_burn: u128,
        retain_haircut_face: bool,
    ) -> V16Result<(u128, u128)> {
        V16Core::kernel_released_pnl_conversion_partition(
            positive_face,
            converted,
            source_face_burn,
            retain_haircut_face,
        )
    }

    #[cfg(kani)]
    pub fn kani_kernel_retain_terminal_source_haircut(
        positive_pnl: u128,
        reserved_pnl: u128,
        source_attributed_face: u128,
        converted: u128,
    ) -> V16Result<u128> {
        V16Core::kernel_retain_terminal_source_haircut(
            positive_pnl,
            reserved_pnl,
            source_attributed_face,
            converted,
        )
    }

    #[cfg(kani)]
    pub fn kani_kernel_credit_post_snapshot_residual(
        ledger: ResolvedPayoutLedgerV16,
        legacy_snapshot: u128,
        released: u128,
    ) -> V16Result<(ResolvedPayoutLedgerV16, u128)> {
        V16Core::kernel_credit_post_snapshot_residual(ledger, legacy_snapshot, released)
    }

    #[cfg(kani)]
    pub fn kani_retirement_backing_normalization(bucket: BackingBucketV16) -> BackingBucketV16 {
        V16Core::kernel_retirement_backing_normalization(bucket)
    }

    #[cfg(kani)]
    pub fn kani_recredit_terminal_claim_free_overlap_for_source_domain_not_atomic(
        &mut self,
        source_domain: usize,
        claim_free_residual_remaining: &mut u128,
    ) -> V16Result<u128> {
        self.recredit_terminal_claim_free_overlap_for_source_domain_not_atomic(
            source_domain,
            claim_free_residual_remaining,
        )
    }

    #[cfg(kani)]
    pub fn kani_retire_terminal_unbudgeted_insurance_delta(
        vault: u128,
        insurance: u128,
        budget_remaining: u128,
        source_reserved_atoms: u128,
        additional_reserved: u128,
    ) -> V16Result<(u128, u128, u128)> {
        Self::retire_terminal_unbudgeted_insurance_delta(
            vault,
            insurance,
            budget_remaining,
            source_reserved_atoms,
            additional_reserved,
        )
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_backing_expiry_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        now_slot: u64,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_backing_expiry_delta(bucket, source, now_slot)
    }

    #[cfg(kani)]
    pub fn kani_advance_resolved_slot(
        mode: MarketModeV16,
        current_slot: u64,
        authenticated_slot: u64,
    ) -> V16Result<u64> {
        V16Core::kernel_advance_resolved_slot(mode, current_slot, authenticated_slot)
    }

    #[cfg(kani)]
    pub fn kani_lapsed_source_backing_scan_step(
        selected: Option<usize>,
        sparse_tail: bool,
        occupied: bool,
        domain: usize,
        bucket_status: BackingBucketStatusV16,
        expiry_slot: u64,
        current_slot: u64,
    ) -> (Option<usize>, bool) {
        V16Core::kernel_lapsed_source_backing_scan_step(
            selected,
            sparse_tail,
            occupied,
            domain,
            bucket_status,
            expiry_slot,
            current_slot,
        )
    }

    #[cfg(kani)]
    pub fn kani_create_resolved_payout_receipt_if_needed(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        self.create_resolved_payout_receipt_if_needed(account)
    }

    fn account_no_positive_credit_equity(account: &PortfolioV16View<'_>) -> V16Result<i128> {
        validate_non_min_i128(account.header.pnl.get())?;
        validate_fee_credits(account.header.fee_credits.get())?;
        let capital = i128::try_from(account.header.capital.get())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        let fee_debt = i128::try_from(account.header.fee_credits.get().unsigned_abs())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        capital
            .checked_add(account.header.pnl.get().min(0))
            .and_then(|v| v.checked_sub(fee_debt))
            .ok_or(V16Error::ArithmeticOverflow)
    }

    fn ensure_no_positive_credit_initial_margin(account: &PortfolioV16View<'_>) -> V16Result<()> {
        validate_non_min_i128(account.header.pnl.get())?;
        validate_fee_credits(account.header.fee_credits.get())?;
        let cert = account.header.health_cert.try_to_runtime()?;
        V16Core::kernel_locked_margin_gate(
            account.header.capital.get(),
            account.header.pnl.get(),
            account.header.fee_credits.get(),
            cert.certified_initial_req,
        )
    }

    #[cfg(kani)]
    pub fn kani_ensure_no_positive_credit_initial_margin(
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        Self::ensure_no_positive_credit_initial_margin(account)
    }

    #[cfg(kani)]
    pub fn kani_trade_account_requires_initial_margin(current: i128, next: i128) -> bool {
        trade_account_requires_initial_margin(current, next)
    }

    fn recertify_account_after_source_lien_change(
        &self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<HealthCertV16> {
        let existing = account.header.health_cert.try_to_runtime()?;
        if existing.active_bitmap_at_cert != account.header.active_bitmap.map(V16PodU64::get) {
            return Err(V16Error::Stale);
        }
        let equity = self.account_haircut_equity(&account.as_view())?;
        let certified_liq_deficit = if equity < 0 {
            equity.unsigned_abs()
        } else {
            existing
                .certified_maintenance_req
                .saturating_sub(equity as u128)
        };
        let cert = HealthCertV16 {
            certified_equity: equity,
            certified_initial_req: existing.certified_initial_req,
            certified_maintenance_req: existing.certified_maintenance_req,
            certified_liq_deficit,
            certified_worst_case_loss: existing.certified_worst_case_loss,
            cert_oracle_epoch: self.header.oracle_epoch.get(),
            cert_funding_epoch: self.header.funding_epoch.get(),
            cert_risk_epoch: self.header.risk_epoch.get(),
            cert_asset_set_epoch: self.header.asset_set_epoch.get(),
            active_bitmap_at_cert: account.header.active_bitmap.map(V16PodU64::get),
            valid: true,
        };
        account.header.health_cert = HealthCertV16Account::from_runtime(&cert);
        Ok(cert)
    }

    fn recertify_account_after_trade_delta(
        &self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        old_abs_q: u128,
        new_abs_q: u128,
        price: u64,
    ) -> V16Result<HealthCertV16> {
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || price == 0
            || price > MAX_ORACLE_PRICE
        {
            return Err(V16Error::InvalidConfig);
        }
        let asset = self.asset_state(asset_index)?;
        if asset.raw_oracle_target_price != asset.effective_price {
            let cert = self.compute_account_health_cert_with_price_override(
                &account.as_view(),
                false,
                None,
            )?;
            account.header.health_cert = HealthCertV16Account::from_runtime(&cert);
            return Ok(cert);
        }
        let existing = account.header.health_cert.try_to_runtime()?;
        let old_notional = risk_notional_ceil(old_abs_q, price)?;
        let new_notional = risk_notional_ceil(new_abs_q, price)?;
        let config = self.header.config.try_to_runtime_shape()?;
        let old_initial = margin_requirement(
            old_notional,
            config.initial_margin_bps,
            config.min_nonzero_im_req,
        )?;
        let old_maintenance = margin_requirement(
            old_notional,
            config.maintenance_margin_bps,
            config.min_nonzero_mm_req,
        )?;
        let new_initial = margin_requirement(
            new_notional,
            config.initial_margin_bps,
            config.min_nonzero_im_req,
        )?;
        let new_maintenance = margin_requirement(
            new_notional,
            config.maintenance_margin_bps,
            config.min_nonzero_mm_req,
        )?;
        let initial_req = existing
            .certified_initial_req
            .checked_sub(old_initial)
            .and_then(|v| v.checked_add(new_initial))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let maintenance_req = existing
            .certified_maintenance_req
            .checked_sub(old_maintenance)
            .and_then(|v| v.checked_add(new_maintenance))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let worst_case_loss = existing
            .certified_worst_case_loss
            .checked_sub(old_notional)
            .and_then(|v| v.checked_add(new_notional))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let equity = self.account_haircut_equity(&account.as_view())?;
        let certified_liq_deficit = if equity < 0 {
            equity.unsigned_abs()
        } else {
            maintenance_req.saturating_sub(equity as u128)
        };
        let cert = HealthCertV16 {
            certified_equity: equity,
            certified_initial_req: initial_req,
            certified_maintenance_req: maintenance_req,
            certified_liq_deficit,
            certified_worst_case_loss: worst_case_loss,
            cert_oracle_epoch: self.header.oracle_epoch.get(),
            cert_funding_epoch: self.header.funding_epoch.get(),
            cert_risk_epoch: self.header.risk_epoch.get(),
            cert_asset_set_epoch: self.header.asset_set_epoch.get(),
            active_bitmap_at_cert: account.header.active_bitmap.map(V16PodU64::get),
            valid: true,
        };
        account.header.health_cert = HealthCertV16Account::from_runtime(&cert);
        Ok(cert)
    }

    /// Taker-only trade fee charge (design §1A), with the N1 maker-fallback
    /// folded in. Only the side that initiated the trade
    /// (`taker_is_long_account` selects `long_account` vs `short_account`)
    /// pays `fee`; the passive maker/LP side pays nothing — *unless* the
    /// taker's own charge attempt returns `0` while `fee != 0` (i.e. the fee
    /// was genuinely owed but the taker paid nothing), in which case the
    /// solvent maker is charged `fee.min(maker.capital)` instead.
    /// `charge_account_fee_current_not_atomic` returns `0` for **two**
    /// structurally distinct reasons and the fallback fires on *either*:
    /// the taker's negative-PnL waiver (`pnl < 0`), or the taker's capital
    /// being exhausted (`fee.min(capital) == 0` while `pnl >= 0`, e.g. an
    /// earlier leg of a multi-leg batch already drew capital to zero). A
    /// version of this fallback gated on the pnl<0 waiver alone left the
    /// capital-exhausted-but-not-underwater case fee-free — closed
    /// 2026-07-15 (security review, MEDIUM: fee evasion). This does NOT
    /// strip the pnl<0 guard on the taker's own charge attempt — the guard
    /// still fires first, exactly as before; only the *consequence* of it
    /// (or of capital exhaustion) firing changes: fallback to maker instead
    /// of collecting nothing.
    ///
    /// Returns `(fee_a, fee_b)` in the caller's original long/short axis
    /// (`fee_a` = amount charged to `long_account`, `fee_b` = amount charged
    /// to `short_account`) — independent of which side was the taker.
    fn charge_trade_fee_taker_only_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        fee: u128,
        taker_is_long_account: bool,
    ) -> V16Result<(u128, u128)> {
        // Maker-fallback (N1): when the taker's fee resolves to 0 on a
        // fee-bearing fill, charge the maker instead of losing the fee. The
        // trigger is `taker_fee == 0 && fee != 0` WITHOUT a `pnl < 0` qualifier
        // on purpose: charge_account_fee_current_not_atomic returns 0 for TWO
        // structurally distinct reasons — the pnl<0 waiver AND capital == 0
        // (fee.min(capital) == 0). Gating the fallback on pnl<0 alone let a
        // capital-depleted-but-not-underwater taker (e.g. an early batch leg
        // sized to exhaust capital, so every later leg pays nothing) evade the
        // fee entirely — protocol/LP/creator/insurance all get 0. Widening to
        // "taker paid nothing for any reason" closes that revenue leak
        // (security review 2026-07-15, MEDIUM).
        // GH#133: the trigger is a SHORTFALL, not a zero.
        //
        // `charge_account_fee_current_not_atomic` charges `fee.min(capital)` and
        // returns what it actually took. Testing that against zero meant a taker
        // who paid a single atom short of the fee was treated identically to one
        // who paid in full: the fallback did not fire, the maker was never asked,
        // and the remainder was collected from nobody. Protocol, LP, creator and
        // insurance all silently received less than the fill earned.
        //
        // Two things follow from charging on shortfall instead.
        //
        // First, the maker is asked for the REMAINDER (`fee - taker_fee`), not for
        // the full `fee`. Asking for the full amount after the taker already paid
        // part of it would over-collect on exactly the partial-payment case this
        // fixes.
        //
        // Second, BOTH return values can now be non-zero — previously exactly one
        // was. That is safe here: the caller accumulates `fee_a` and `fee_b`
        // additively into the trade outcome rather than treating them as mutually
        // exclusive alternatives.
        //
        // The taker_fee == 0 case is unchanged: shortfall == fee, the maker is
        // asked for the whole thing, and the pair is (0, fee) exactly as before.
        // So this strictly widens when the fallback fires and changes nothing that
        // already worked — including the deliberate absence of a `pnl < 0`
        // qualifier described above.
        if taker_is_long_account {
            let taker_fee = self.charge_account_fee_current_not_atomic(long_account, fee)?;
            let shortfall = fee.saturating_sub(taker_fee);
            if shortfall != 0 {
                Ok((
                    taker_fee,
                    self.charge_account_fee_current_not_atomic(short_account, shortfall)?,
                ))
            } else {
                Ok((taker_fee, 0u128))
            }
        } else {
            let taker_fee = self.charge_account_fee_current_not_atomic(short_account, fee)?;
            let shortfall = fee.saturating_sub(taker_fee);
            if shortfall != 0 {
                Ok((
                    self.charge_account_fee_current_not_atomic(long_account, shortfall)?,
                    taker_fee,
                ))
            } else {
                Ok((0u128, taker_fee))
            }
        }
    }

    #[cfg(kani)]
    pub fn kani_charge_trade_fee_taker_only_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        fee: u128,
        taker_is_long_account: bool,
    ) -> V16Result<(u128, u128)> {
        self.charge_trade_fee_taker_only_not_atomic(
            long_account,
            short_account,
            fee,
            taker_is_long_account,
        )
    }

    fn terminal_trade_residual_asset_before_refresh(
        account: &PortfolioV16View<'_>,
    ) -> V16Result<Option<usize>> {
        if account.header.pnl.get() < 0
            || account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual()
            || active_bitmap_count_ones(account.header.active_bitmap.map(V16PodU64::get)) != 1
        {
            return Ok(None);
        }
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active {
                return Ok(Some(leg.asset_index as usize));
            }
            slot += 1;
        }
        Err(V16Error::HiddenLeg)
    }

    fn begin_terminal_trade_residual_if_needed(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        lookup: PositionDeltaLookupV16,
        is_final_batch_fill: bool,
        attributable_asset_before_refresh: Option<usize>,
    ) -> V16Result<()> {
        if !is_final_batch_fill
            || attributable_asset_before_refresh != Some(asset_index)
            || lookup.current_q == 0
            || lookup.next_q != 0
            || account.header.pnl.get() >= 0
            || active_bitmap_count_ones(account.header.active_bitmap.map(V16PodU64::get)) != 1
        {
            return Ok(());
        }
        let leg_slot = lookup.existing_slot.ok_or(V16Error::InvalidLeg)?;
        let leg = account.header.legs[leg_slot].try_to_runtime()?;
        if !leg.active
            || leg.asset_index as usize != asset_index
            || signed_position(leg) != lookup.current_q
        {
            return Err(V16Error::InvalidLeg);
        }
        self.begin_close_progress_ledger(
            account,
            asset_index,
            opposite_side(leg.side),
            account.header.pnl.get().unsigned_abs(),
        )
    }

    // Nine arguments: the fork's own position_lookups and taker_is_long_account on
    // top of upstream's seven. Upstream trips this lint here too.
    #[allow(clippy::too_many_arguments)]
    fn apply_trade_after_refresh_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        request: TradeRequestV16,
        position_lookups: (PositionDeltaLookupV16, PositionDeltaLookupV16),
        recertify_after_fill: bool,
        taker_is_long_account: bool,
        is_final_batch_fill: bool,
        long_attributable_asset_before_refresh: Option<usize>,
        short_attributable_asset_before_refresh: Option<usize>,
    ) -> V16Result<TradeApplyOutcomeV16> {
        let (abs_size_q, _, _) = Self::trade_signed_size_deltas(request.size_q)?;
        let trade_preflight = self.validate_trade_position_preflight(
            &long_account.as_view(),
            &short_account.as_view(),
            request,
            position_lookups.0,
            position_lookups.1,
        )?;
        let risk_increasing = trade_preflight.risk_increasing;
        self.require_asset_risk_change_allowed(request.asset_index, risk_increasing)?;
        let notional = trade_notional_floor(abs_size_q, request.exec_price)?;
        let fee_notional = trade_fee_notional_ceil(abs_size_q, request.exec_price)?;
        let fee = checked_fee_bps(fee_notional, request.fee_bps)?;
        let (fee_a, fee_b) = self.charge_trade_fee_taker_only_not_atomic(
            long_account,
            short_account,
            fee,
            taker_is_long_account,
        )?;
        self.begin_terminal_trade_residual_if_needed(
            long_account,
            request.asset_index,
            trade_preflight.long_lookup,
            is_final_batch_fill,
            long_attributable_asset_before_refresh,
        )?;
        self.begin_terminal_trade_residual_if_needed(
            short_account,
            request.asset_index,
            trade_preflight.short_lookup,
            is_final_batch_fill,
            short_attributable_asset_before_refresh,
        )?;
        self.apply_current_position_delta_with_lookup(
            long_account,
            request.asset_index,
            trade_preflight
                .long_lookup
                .next_q
                .checked_sub(trade_preflight.long_lookup.current_q)
                .ok_or(V16Error::ArithmeticOverflow)?,
            trade_preflight.long_lookup,
        )?;
        self.apply_current_position_delta_with_lookup(
            short_account,
            request.asset_index,
            trade_preflight
                .short_lookup
                .next_q
                .checked_sub(trade_preflight.short_lookup.current_q)
                .ok_or(V16Error::ArithmeticOverflow)?,
            trade_preflight.short_lookup,
        )?;
        self.transfer_trade_residual_reward_credit(
            long_account,
            short_account,
            &trade_preflight,
            request.asset_index,
        )?;
        if recertify_after_fill {
            let price = self.asset_state(request.asset_index)?.effective_price;
            self.recertify_account_after_trade_delta(
                long_account,
                request.asset_index,
                trade_preflight.long_old_abs_q,
                trade_preflight.long_new_abs_q,
                price,
            )?;
            self.recertify_account_after_trade_delta(
                short_account,
                request.asset_index,
                trade_preflight.short_old_abs_q,
                trade_preflight.short_new_abs_q,
                price,
            )?;
        }
        Ok(TradeApplyOutcomeV16 {
            fee_a,
            fee_b,
            notional,
            risk_increasing,
            long_requires_initial_margin: trade_preflight.long_requires_initial_margin,
            short_requires_initial_margin: trade_preflight.short_requires_initial_margin,
            long_has_source_claims: trade_preflight.long_has_source_claims,
            short_has_source_claims: trade_preflight.short_has_source_claims,
        })
    }

    fn accumulate_batch_trade_apply(
        outcome: &mut BatchTradeOutcomeV16,
        risk_increasing: &mut bool,
        long_has_source_claims: &mut bool,
        short_has_source_claims: &mut bool,
        applied: TradeApplyOutcomeV16,
    ) -> V16Result<()> {
        let (o, ri, lhsc, shsc) = V16Core::kernel_accumulate_batch_trade(
            *outcome,
            *risk_increasing,
            *long_has_source_claims,
            *short_has_source_claims,
            applied,
        )?;
        *outcome = o;
        *risk_increasing = ri;
        *long_has_source_claims = lhsc;
        *short_has_source_claims = shsc;
        Ok(())
    }

    #[cfg(kani)]
    pub fn kani_accumulate_batch_trade_apply(
        outcome: &mut BatchTradeOutcomeV16,
        risk_increasing: &mut bool,
        long_has_source_claims: &mut bool,
        short_has_source_claims: &mut bool,
        fee_a: u128,
        fee_b: u128,
        notional: u128,
        applied_risk_increasing: bool,
        applied_long_has_source_claims: bool,
        applied_short_has_source_claims: bool,
    ) -> V16Result<()> {
        Self::accumulate_batch_trade_apply(
            outcome,
            risk_increasing,
            long_has_source_claims,
            short_has_source_claims,
            TradeApplyOutcomeV16 {
                fee_a,
                fee_b,
                notional,
                risk_increasing: applied_risk_increasing,
                long_requires_initial_margin: true,
                short_requires_initial_margin: true,
                long_has_source_claims: applied_long_has_source_claims,
                short_has_source_claims: applied_short_has_source_claims,
            },
        )
    }

    fn finish_trade_checks_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        locked: bool,
        risk_increasing: bool,
        long_requires_initial_margin: bool,
        short_requires_initial_margin: bool,
        long_has_source_claims: bool,
        short_has_source_claims: bool,
    ) -> V16Result<()> {
        if risk_increasing && !locked {
            if long_requires_initial_margin && long_has_source_claims {
                self.create_initial_margin_source_lien_if_needed(long_account)?;
            }
            if short_requires_initial_margin && short_has_source_claims {
                self.create_initial_margin_source_lien_if_needed(short_account)?;
            }
        }
        if long_requires_initial_margin {
            Self::ensure_initial_margin(&long_account.as_view())?;
        }
        if short_requires_initial_margin {
            Self::ensure_initial_margin(&short_account.as_view())?;
        }
        if locked {
            if long_requires_initial_margin {
                Self::ensure_no_positive_credit_initial_margin(&long_account.as_view())?;
            }
            if short_requires_initial_margin {
                Self::ensure_no_positive_credit_initial_margin(&short_account.as_view())?;
            }
        }
        self.validate_shape_audit_scan()?;
        self.validate_account_audit_scan(&long_account.as_view())?;
        self.validate_account_audit_scan(&short_account.as_view())?;
        Ok(())
    }

    /// Closes one opposite-side pair in Recovery while treating caller quantity as a work budget.
    /// The canonical effective quantities, rather than retained raw bases, bound the landed close.
    ///
    /// Fork note (upstream `ce590d9b`): this fork's trade primitive carries the
    /// taker-only fee selector `taker_is_long_account`, which upstream's
    /// signature does not have. This path always trades at `fee_bps: 0`, so the
    /// selector is a documented no-op here — `charge_trade_fee_taker_only_not_atomic`
    /// resolves to `(0, 0)` on a zero requested fee whichever side is nominally
    /// the taker (design §1A) — and `true` is passed in both orientations, which
    /// is the same choice `handle_force_close_abandoned_asset` makes in the
    /// wrapper.
    pub fn force_close_recovery_pair_not_atomic(
        &mut self,
        account_a: &mut PortfolioV16ViewMut<'_>,
        account_b: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        close_request_q: u128,
    ) -> V16Result<u128> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        if close_request_q == 0 {
            return Err(V16Error::InvalidConfig);
        }
        self.validate_configured_asset_index(asset_index)?;
        let asset = self.asset_state(asset_index)?;
        if asset.lifecycle != AssetLifecycleV16::Recovery {
            return Err(V16Error::LockActive);
        }
        let leg_a = Self::active_leg_for_asset(&account_a.as_view(), asset_index)?;
        let leg_b = Self::active_leg_for_asset(&account_b.as_view(), asset_index)?;
        if !leg_a.active || !leg_b.active || leg_a.side == leg_b.side {
            return Err(V16Error::InvalidLeg);
        }
        let effective_a = V16Core::effective_abs_quantity_for_leg(asset, leg_a)?;
        let effective_b = V16Core::effective_abs_quantity_for_leg(asset, leg_b)?;
        let close_q = close_request_q
            .min(effective_a)
            .min(effective_b)
            .min(asset.oi_eff_long_q)
            .min(asset.oi_eff_short_q);
        if close_q == 0 {
            return Err(V16Error::NonProgress);
        }
        let size_q = i128::try_from(close_q).map_err(|_| V16Error::ArithmeticOverflow)?;
        let request = TradeRequestV16 {
            asset_index,
            size_q,
            exec_price: asset.effective_price,
            fee_bps: 0,
        };
        // Positive `size_q` is applied to the first account and its negation to the second.
        // Put the short first so both signed deltas move the existing legs toward zero.
        if leg_a.side == SideV16::Short {
            self.execute_trade_with_fee_loss_stale_scoped_not_atomic(
                account_a, account_b, request, true,
            )?;
        } else {
            self.execute_trade_with_fee_loss_stale_scoped_not_atomic(
                account_b, account_a, request, true,
            )?;
        }
        Ok(close_q)
    }

    pub fn execute_trade_with_fee_loss_stale_scoped_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        request: TradeRequestV16,
        taker_is_long_account: bool,
    ) -> V16Result<TradeOutcomeV16> {
        let outcome = self.execute_batch_with_fee_loss_stale_scoped_not_atomic(
            long_account,
            short_account,
            core::slice::from_ref(&request),
            taker_is_long_account,
        )?;
        Ok(TradeOutcomeV16 {
            fee_a: outcome.fee_a,
            fee_b: outcome.fee_b,
            notional: outcome.notional,
        })
    }

    pub fn execute_batch_with_fee_loss_stale_scoped_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        requests: &[TradeRequestV16],
        taker_is_long_account: bool,
    ) -> V16Result<BatchTradeOutcomeV16> {
        self.validate_unconfigured_market_tail()?;
        let mut ignore_unrelated_loss_stale =
            decode_bool(self.header.loss_stale_active)? && !requests.is_empty();
        if ignore_unrelated_loss_stale {
            let mut i = 0usize;
            while i < requests.len() {
                if !self.can_ignore_unrelated_loss_stale_for_trade(
                    &long_account.as_view(),
                    &short_account.as_view(),
                    requests[i].asset_index,
                )? {
                    ignore_unrelated_loss_stale = false;
                    break;
                }
                i += 1;
            }
        }
        let restore_loss_stale_active = self.header.loss_stale_active;
        if ignore_unrelated_loss_stale {
            self.header.loss_stale_active = 0;
        }
        let result = self.execute_batch_with_fee_after_tail_validation_not_atomic(
            long_account,
            short_account,
            requests,
            taker_is_long_account,
        );
        if ignore_unrelated_loss_stale {
            self.header.loss_stale_active = restore_loss_stale_active;
        }
        let outcome = result?;
        self.validate_shape()?;
        long_account.validate_with_market(&self.as_view())?;
        short_account.validate_with_market(&self.as_view())?;
        Ok(outcome)
    }

    /// fork feature A-1 (fork-facade only): single trade with an explicit
    /// admit-threshold. When `threshold_bps_opt` is `Some(t)` and the
    /// persisted A-6 stress-consumption accumulator has reached `t`, the lane
    /// is lifted to `HMax` even if `threshold_stress_active` has not yet
    /// flipped. The wrapper instruction context carries the threshold; the
    /// toly-baseline `execute_trade_with_fee_loss_stale_scoped_not_atomic`
    /// (no threshold) is preserved for ordinary trades.
    ///
    /// Implementation: re-enters the batch execution path with the threshold
    /// injected at the `h_lock_lane` call by routing through the internal
    /// `fork_execute_batch_with_admit_threshold_not_atomic` helper.
    #[cfg(feature = "fork-facade")]
    pub fn fork_execute_trade_with_admit_threshold_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        request: TradeRequestV16,
        threshold_bps_opt: Option<u128>,
        taker_is_long_account: bool,
    ) -> V16Result<TradeOutcomeV16> {
        let outcome = self.fork_execute_batch_with_admit_threshold_not_atomic(
            long_account,
            short_account,
            core::slice::from_ref(&request),
            threshold_bps_opt,
            taker_is_long_account,
        )?;
        Ok(TradeOutcomeV16 {
            fee_a: outcome.fee_a,
            fee_b: outcome.fee_b,
            notional: outcome.notional,
        })
    }

    /// Internal batch helper for A-1: identical to the toly baseline batch but
    /// passes `threshold_bps_opt` to `h_lock_lane` for the A-1 gate.
    #[cfg(feature = "fork-facade")]
    fn fork_execute_batch_with_admit_threshold_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        requests: &[TradeRequestV16],
        threshold_bps_opt: Option<u128>,
        taker_is_long_account: bool,
    ) -> V16Result<BatchTradeOutcomeV16> {
        self.validate_unconfigured_market_tail()?;
        let mut ignore_unrelated_loss_stale =
            decode_bool(self.header.loss_stale_active)? && !requests.is_empty();
        if ignore_unrelated_loss_stale {
            let mut i = 0usize;
            while i < requests.len() {
                if !self.can_ignore_unrelated_loss_stale_for_trade(
                    &long_account.as_view(),
                    &short_account.as_view(),
                    requests[i].asset_index,
                )? {
                    ignore_unrelated_loss_stale = false;
                    break;
                }
                i += 1;
            }
        }
        let restore_loss_stale_active = self.header.loss_stale_active;
        if ignore_unrelated_loss_stale {
            self.header.loss_stale_active = 0;
        }
        let result = self.fork_execute_batch_after_tail_validation_with_threshold_not_atomic(
            long_account,
            short_account,
            requests,
            threshold_bps_opt,
            taker_is_long_account,
        );
        if ignore_unrelated_loss_stale {
            self.header.loss_stale_active = restore_loss_stale_active;
        }
        let outcome = result?;
        self.validate_shape()?;
        long_account.validate_with_market(&self.as_view())?;
        short_account.validate_with_market(&self.as_view())?;
        Ok(outcome)
    }

    /// Core A-1 inner loop: the frozen inner loop but with threshold forwarded to h_lock_lane.
    #[cfg(feature = "fork-facade")]
    fn fork_execute_batch_after_tail_validation_with_threshold_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        requests: &[TradeRequestV16],
        threshold_bps_opt: Option<u128>,
        taker_is_long_account: bool,
    ) -> V16Result<BatchTradeOutcomeV16> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let config = self.header.config.try_to_runtime_shape()?;
        if requests.is_empty() {
            return Err(V16Error::NonProgress);
        }
        if requests.len() > config.max_portfolio_assets as usize {
            return Err(V16Error::InvalidConfig);
        }
        let mut i = 0usize;
        while i < requests.len() {
            self.validate_trade_request(requests[i])?;
            i += 1;
        }
        // Residual attribution is sound only when the account entered this
        // public batch nonnegative with exactly one live asset. A pre-existing
        // deficit or multi-asset account has lost per-domain provenance in the
        // account-global PnL scalar; if it later becomes flat, it waits for the
        // explicit market-level resolution policy instead of charging the last
        // touched asset or letting one account force market-wide Recovery.
        let long_attributable_asset_before_refresh =
            Self::terminal_trade_residual_asset_before_refresh(&long_account.as_view())?;
        let short_attributable_asset_before_refresh =
            Self::terminal_trade_residual_asset_before_refresh(&short_account.as_view())?;
        self.settle_account_for_position_action_and_refresh_not_atomic(long_account)?;
        self.settle_account_for_position_action_and_refresh_not_atomic(short_account)?;
        // A-1: threshold injected here (key difference from the toly baseline loop)
        let locked = self.h_lock_lane(Some(&long_account.as_view()), false, threshold_bps_opt)?
            == HLockLaneV16::HMax
            || self.h_lock_lane(Some(&short_account.as_view()), false, threshold_bps_opt)?
                == HLockLaneV16::HMax;
        let mut outcome = BatchTradeOutcomeV16 {
            fill_count: 0,
            fee_a: 0,
            fee_b: 0,
            notional: 0,
        };
        let mut risk_increasing = false;
        let mut long_requires_initial_margin = false;
        let mut short_requires_initial_margin = false;
        let mut long_has_source_claims = false;
        let mut short_has_source_claims = false;
        let recertify_after_fill = requests.len() == 1;
        let mut long_position_map = PositionSlotMapV16::from_account(&long_account.as_view())?;
        let mut short_position_map = PositionSlotMapV16::from_account(&short_account.as_view())?;
        let mut i = 0usize;
        while i < requests.len() {
            let (_, long_delta, short_delta) = Self::trade_signed_size_deltas(requests[i].size_q)?;
            let position_asset = self.asset_state(requests[i].asset_index)?;
            let request_position_lookups = (
                long_position_map.plan_delta(
                    requests[i].asset_index,
                    long_delta,
                    position_asset,
                )?,
                short_position_map.plan_delta(
                    requests[i].asset_index,
                    short_delta,
                    position_asset,
                )?,
            );
            let applied = self.apply_trade_after_refresh_not_atomic(
                long_account,
                short_account,
                requests[i],
                request_position_lookups,
                recertify_after_fill,
                taker_is_long_account,
                i + 1 == requests.len(),
                long_attributable_asset_before_refresh,
                short_attributable_asset_before_refresh,
            )?;
            long_requires_initial_margin |= applied.long_requires_initial_margin;
            short_requires_initial_margin |= applied.short_requires_initial_margin;
            Self::accumulate_batch_trade_apply(
                &mut outcome,
                &mut risk_increasing,
                &mut long_has_source_claims,
                &mut short_has_source_claims,
                applied,
            )?;
            i += 1;
        }
        if !recertify_after_fill {
            self.certify_account_after_local_settlement_with_price_override(long_account, None)?;
            self.certify_account_after_local_settlement_with_price_override(short_account, None)?;
        }
        self.finish_trade_checks_not_atomic(
            long_account,
            short_account,
            locked,
            risk_increasing,
            long_requires_initial_margin,
            short_requires_initial_margin,
            long_has_source_claims,
            short_has_source_claims,
        )?;
        // ADL can leave stored basis larger than effective OI. Start resets only after final margin
        // checks so the reset's risk-epoch advance leaves each affected account certificate stale;
        // the public auto-crank then selects Refresh and clears the economically exhausted residue.
        let mut i = 0usize;
        while i < requests.len() {
            self.begin_zero_oi_residue_resets(requests[i].asset_index)?;
            i += 1;
        }
        Ok(outcome)
    }

    fn execute_batch_with_fee_after_tail_validation_not_atomic(
        &mut self,
        long_account: &mut PortfolioV16ViewMut<'_>,
        short_account: &mut PortfolioV16ViewMut<'_>,
        requests: &[TradeRequestV16],
        taker_is_long_account: bool,
    ) -> V16Result<BatchTradeOutcomeV16> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let config = self.header.config.try_to_runtime_shape()?;
        if requests.is_empty() {
            return Err(V16Error::NonProgress);
        }
        if requests.len() > config.max_portfolio_assets as usize {
            return Err(V16Error::InvalidConfig);
        }
        let mut i = 0usize;
        while i < requests.len() {
            self.validate_trade_request(requests[i])?;
            i += 1;
        }
        // Residual attribution is sound only when the account entered this
        // public batch nonnegative with exactly one live asset. A pre-existing
        // deficit or multi-asset account has lost per-domain provenance in the
        // account-global PnL scalar; if it later becomes flat, it waits for the
        // explicit market-level resolution policy instead of charging the last
        // touched asset or letting one account force market-wide Recovery.
        let long_attributable_asset_before_refresh =
            Self::terminal_trade_residual_asset_before_refresh(&long_account.as_view())?;
        let short_attributable_asset_before_refresh =
            Self::terminal_trade_residual_asset_before_refresh(&short_account.as_view())?;
        self.settle_account_for_position_action_and_refresh_not_atomic(long_account)?;
        self.settle_account_for_position_action_and_refresh_not_atomic(short_account)?;

        let locked = self.h_lock_lane(
            Some(&long_account.as_view()),
            false,
            #[cfg(feature = "fork-facade")]
            None, // A-1: toly baseline; use fork_execute_trade_with_admit_threshold for A-1 gating
        )? == HLockLaneV16::HMax
            || self.h_lock_lane(
                Some(&short_account.as_view()),
                false,
                #[cfg(feature = "fork-facade")]
                None,
            )? == HLockLaneV16::HMax;
        let mut outcome = BatchTradeOutcomeV16 {
            fill_count: 0,
            fee_a: 0,
            fee_b: 0,
            notional: 0,
        };
        let mut risk_increasing = false;
        let mut long_requires_initial_margin = false;
        let mut short_requires_initial_margin = false;
        let mut long_has_source_claims = false;
        let mut short_has_source_claims = false;
        let recertify_after_fill = requests.len() == 1;
        let mut long_position_map = PositionSlotMapV16::from_account(&long_account.as_view())?;
        let mut short_position_map = PositionSlotMapV16::from_account(&short_account.as_view())?;
        let mut i = 0usize;
        while i < requests.len() {
            let (_, long_delta, short_delta) = Self::trade_signed_size_deltas(requests[i].size_q)?;
            let position_asset = self.asset_state(requests[i].asset_index)?;
            let request_position_lookups = (
                long_position_map.plan_delta(
                    requests[i].asset_index,
                    long_delta,
                    position_asset,
                )?,
                short_position_map.plan_delta(
                    requests[i].asset_index,
                    short_delta,
                    position_asset,
                )?,
            );
            let applied = self.apply_trade_after_refresh_not_atomic(
                long_account,
                short_account,
                requests[i],
                request_position_lookups,
                recertify_after_fill,
                taker_is_long_account,
                i + 1 == requests.len(),
                long_attributable_asset_before_refresh,
                short_attributable_asset_before_refresh,
            )?;
            long_requires_initial_margin |= applied.long_requires_initial_margin;
            short_requires_initial_margin |= applied.short_requires_initial_margin;
            Self::accumulate_batch_trade_apply(
                &mut outcome,
                &mut risk_increasing,
                &mut long_has_source_claims,
                &mut short_has_source_claims,
                applied,
            )?;
            i += 1;
        }
        if !recertify_after_fill {
            self.certify_account_after_local_settlement_with_price_override(long_account, None)?;
            self.certify_account_after_local_settlement_with_price_override(short_account, None)?;
        }
        self.finish_trade_checks_not_atomic(
            long_account,
            short_account,
            locked,
            risk_increasing,
            long_requires_initial_margin,
            short_requires_initial_margin,
            long_has_source_claims,
            short_has_source_claims,
        )?;
        // ADL can leave stored basis larger than effective OI. Start resets only after final margin
        // checks so the reset's risk-epoch advance leaves each affected account certificate stale;
        // the public auto-crank then selects Refresh and clears the economically exhausted residue.
        let mut i = 0usize;
        while i < requests.len() {
            self.begin_zero_oi_residue_resets(requests[i].asset_index)?;
            i += 1;
        }
        Ok(outcome)
    }

    fn set_account_pnl_after_principal_settlement(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        new_pnl: i128,
    ) -> V16Result<()> {
        validate_non_min_i128(new_pnl)?;
        let old_pnl = account.header.pnl.get();
        if old_pnl >= 0 || new_pnl > 0 || new_pnl < old_pnl {
            return Err(V16Error::InvalidConfig);
        }
        if old_pnl < 0 && new_pnl == 0 {
            self.header.negative_pnl_account_count = V16PodU64::new(
                self.header
                    .negative_pnl_account_count
                    .get()
                    .checked_sub(1)
                    .ok_or(V16Error::CounterUnderflow)?,
            );
        }
        Self::sync_unattributed_loss_lock(account, new_pnl)?;
        account.header.pnl = V16PodI128::new(new_pnl);
        Ok(())
    }

    fn resolved_bankruptcy_attribution(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<Option<(usize, SideV16)>> {
        let ledger = account.header.close_progress.try_to_runtime()?;
        if ledger.active && !ledger.canceled && !ledger.finalized && ledger.residual_remaining != 0
        {
            let asset_index = ledger.asset_index as usize;
            self.validate_configured_asset_index(asset_index)?;
            return Ok(Some((asset_index, opposite_side(ledger.domain_side))));
        }

        let mut out = None;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active && !leg.stale && !leg.b_stale {
                let candidate = (leg.asset_index as usize, leg.side);
                self.validate_configured_asset_index(candidate.0)?;
                if out.replace(candidate).is_some() {
                    return Ok(None);
                }
            }
            slot += 1;
        }
        Ok(out)
    }

    fn clear_resolved_unattributed_negative_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        if account.header.pnl.get() >= 0 {
            return Ok(());
        }
        // upstream 228d9b3f: resolved bad-debt wind-down is handled by the
        // resolved close itself (hlock set, PnL zeroed) rather than a terminal
        // RecoveryRequired state with no permissionless crank.
        self.header.bankruptcy_hlock_active = 1;
        self.set_account_pnl(account, 0)?;
        account.header.health_cert.valid = 0;
        Ok(())
    }

    fn settle_resolved_bankruptcy_negative_pnl(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        if account.header.pnl.get() >= 0 {
            return Ok(());
        }
        if decode_market_mode(self.header.mode)? != MarketModeV16::Resolved {
            return Err(V16Error::LockActive);
        }
        let Some((asset_index, bankrupt_side)) =
            self.resolved_bankruptcy_attribution(&account.as_view())?
        else {
            return self.clear_resolved_unattributed_negative_pnl(account);
        };

        self.header.bankruptcy_hlock_active = 1;
        let gross_residual = account.header.pnl.get().unsigned_abs();
        // A close left over from an earlier bankruptcy that paid out in full is
        // finalized but still `active`, so testing `active` alone would skip the
        // fresh close and leave the stale ledger in place -- which
        // `advance_close_progress_ledger` then refuses, stranding the account.
        if account
            .header
            .close_progress
            .try_to_runtime()?
            .close_slot_available()
        {
            self.begin_close_progress_ledger(
                account,
                asset_index,
                opposite_side(bankrupt_side),
                gross_residual,
            )?;
        }

        let insurance_used =
            self.consume_domain_insurance_for_negative_pnl(asset_index, bankrupt_side, account)?;
        if insurance_used != 0 {
            self.advance_close_progress_ledger(account, 0, 0, insurance_used, 0, 0)?;
        }

        let residual = if account.header.pnl.get() < 0 {
            account.header.pnl.get().unsigned_abs()
        } else {
            0
        };
        if residual == 0 {
            account.header.health_cert.valid = 0;
            // Insurance fully covered the loss: negative_pnl_account_count may have
            // reached zero — attempt to auto-clear the hlock.
            self.try_clear_bankruptcy_hlock_if_healthy()?;
            return Ok(());
        }

        let outcome = self.book_bankruptcy_residual_chunk_for_account_core(
            account,
            asset_index,
            bankrupt_side,
            residual,
        )?;
        let new_pnl = V16Core::kernel_settle_resolved_pnl_after_booking(
            account.header.pnl.get(),
            outcome.booked_loss,
            outcome.explicit_loss,
        )?;
        self.set_account_pnl(account, new_pnl)?;
        account.header.health_cert.valid = 0;
        // Residual was booked into explicit/social loss: if this settled the last
        // negative-PnL account, auto-clear the hlock now.
        self.try_clear_bankruptcy_hlock_if_healthy()?;
        Ok(())
    }

    fn settle_negative_pnl_from_principal_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        account.validate_with_market(&self.as_view())?;
        let paid = self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        self.validate_account_audit_scan(&account.as_view())?;
        self.validate_shape_audit_scan()?;
        Ok(paid)
    }

    fn settle_negative_pnl_from_principal_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        let pnl = account.header.pnl.get();
        if pnl >= 0 {
            return Ok(0);
        }
        // PRODUCTION KERNEL: principal-settlement core (exact paid + conservation).
        let (paid, capital, c_tot, new_pnl) = V16Core::kernel_settle_principal(
            account.header.capital.get(),
            self.header.c_tot.get(),
            pnl,
        )?;
        if paid == 0 {
            self.header.bankruptcy_hlock_active = 1;
            return Ok(0);
        }

        let vault_before = self.header.vault.get();
        account.header.capital = V16PodU128::new(capital);
        self.header.c_tot = V16PodU128::new(c_tot);
        self.set_account_pnl_after_principal_settlement(account, new_pnl)?;
        Self::record_account_residual_crystallized_loss(account, paid)?;
        if new_pnl < 0 {
            self.header.bankruptcy_hlock_active = 1;
        }
        // If settling this account's PnL brought the last negative-PnL account to
        // zero (and all other health counters are already zero), auto-clear the hlock
        // so LP/insurance withdrawals are unblocked.  The helper is O(1) and
        // short-circuits immediately when the hlock is already clear.
        self.try_clear_bankruptcy_hlock_if_healthy()?;
        TokenValueFlowProofV16::account_capital_to_realized_loss(
            paid,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        account.header.health_cert.valid = 0;
        Ok(paid)
    }

    // FIX-1 background: `bankruptcy_hlock_active` is SET on any deep-liquidation /
    // insurance-consumption path (see every `self.header.bankruptcy_hlock_active = 1`
    // site). It was originally never cleared, permanently trapping LP/insurance backing
    // withdrawals and oracle reconfig even after the bankruptcy was settled. The auto-
    // clear below re-enables those once the loss is provably absorbed.
    //
    // Per-asset "unabsorbed bankruptcy loss still in flight" predicate for the hlock
    // auto-clear. Deliberately NOT `asset_local_has_position_or_loss_state`: that is an
    // "asset empty / market at rest" predicate (used by the oracle re-anchor path, which
    // must block on ANY open position) and it trips on benign activity (`oi_eff_*`,
    // `stored_pos_count_*`, `loss_weight_sum_*`) and on the monotone social-loss index
    // (`b_*`, `b_epoch_start_*`) that never returns to zero after the first socialized
    // bankruptcy. Requiring those here would leave the hlock — and with it LP/insurance
    // withdrawals and the HMax haircut lane — engaged forever in any market that has ever
    // carried a position, which is the pre-FIX-1 defect.
    //
    // Only fields that represent loss NOT YET ABSORBED BY ANYONE qualify:
    //
    //   pending_domain_loss_barrier_*  an open bankruptcy-close ledger with residual,
    //                                  raised at begin_close_progress_ledger and cleared
    //                                  when the residual hits 0 or on cure-cancel. This is
    //                                  the term that actually fixes the reported hole: a
    //                                  real ledger, with its own clearing sites, that no
    //                                  single user controls, and whose over-lock window is
    //                                  bounded by max_bankrupt_close_lifetime_slots.
    //
    //   explicit_unallocated_loss_*    NOT a term (removed, F-03). The realized
    //                                  unallocatable-loss sink: whole atoms of social loss
    //                                  that `kernel_normalize_social_loss_carry` could not
    //                                  assign to any side's weight, saturating-added on a
    //                                  leg clear (`kernel_clear_leg`) and cleared only at
    //                                  retirement. (An earlier revision of this note said
    //                                  the field had ZERO write sites; that is no longer
    //                                  true.) It was a term here on the theory that it
    //                                  flags unabsorbed loss — but it is a REALIZED
    //                                  write-off, not pending loss (no crank or settlement
    //                                  ever consumes it), so gating the group hlock on it
    //                                  recreated the exact HOSTAGE this predicate was
    //                                  narrowed to avoid: an ordinary close leaves a dust
    //                                  atom that freezes LP/insurance withdrawals and
    //                                  oracle reconfiguration group-wide, and for asset 0
    //                                  (which RETIRE rejects) permanently. Its written
    //                                  siblings social_loss_dust/remainder are, correctly,
    //                                  already excluded for the same reason. The bankruptcy
    //                                  path additionally books unallocatable loss into the
    //                                  per-ACCOUNT `close_progress.explicit_loss_assigned`
    //                                  where it counts as PROGRESS. The write-off still
    //                                  blocks slot reactivation/retire via
    //                                  `asset_state_is_empty_for_activation`, so it is
    //                                  recorded, not lost — only demoted from a group-freeze
    //                                  signal to the residual-state signal it is.
    //
    // b_*/b_epoch_start_* (absorbed-loss bookkeeping, monotone) and social_loss_dust/
    // remainder (sub-atom quarantine sink that never drains) are intentionally excluded.
    //
    // WHY THE SIDE MODE BYTE IS NOT A TERM HERE.
    // An earlier revision also counted `mode_* != Normal` (later narrowed to
    // `mode_* != Normal AND oi_eff_* != 0`). Both forms were wrong, in opposite ways, and
    // the term is gone:
    //   * Bare `mode_* != Normal` LATCHED PERMANENTLY. Nothing moves a drained side out of
    //     DrainOnly: begin_full_drain_reset_inner is the only writer of ResetPending
    //     (:12474/:12499), has one call site (:12562) reachable only via reduce_position
    //     <- liquidate_account_not_atomic / rebalance_reduce_position_not_atomic, both of
    //     which need an ACTIVE LEG, while ordinary closes decrement oi_eff at
    //     :11924/:11931 and never route there.
    //   * Adding `AND oi_eff_* != 0` removed the latch but created a HOSTAGE. Because
    //     bankruptcy_hlock_active is a single group-wide byte consumed by the wrapper's
    //     WithdrawBackingBucket / WithdrawBackingBucketEarnings / WithdrawInsuranceAsset,
    //     one holder on a DrainOnly side who simply declines to close freezes LP backing,
    //     LP earnings and insurance for EVERY domain in the group — at a cost of one
    //     position quantum plus min_nonzero_mm_req of equity, indefinitely. Holding is
    //     legal (asset_risk_increase_gate blocks only risk INCREASES), liquidation is
    //     deficit-gated so a solvent holder never qualifies, and no permissionless path can
    //     force the close. With funding and maintenance fees configured to zero the
    //     holder's equity never decays, so the freeze is permanent and free.
    //   * `mode == ResetPending AND oi_eff != 0` is additionally UNREACHABLE — ResetPending
    //     can only be entered with oi_eff already 0 — so that half was dead code.
    // Upstream reached the same conclusion independently: aeyakovenko/percolator #120
    // rejects inferring the affected asset "from mutable state such as DrainOnly, B state,
    // insurance spend, and barriers" as "unsound in both directions", and prefers a durable
    // per-asset lock bit (an ABI break we cannot take on the deployed layout).
    //
    // Raw POD reads only: this adds no new error return to the settlement/liquidation
    // paths that call try_clear with `?`, so a single corrupt slot byte cannot revert a
    // liquidation on an unrelated asset. The scan is O(configured assets) but runs only
    // when the hlock is set (post-bankruptcy); the common path early-returns before it.
    fn group_has_unabsorbed_bankruptcy_loss(&self) -> bool {
        let configured =
            (self.header.config.max_market_slots.get() as usize).min(self.markets.len());
        let mut i = 0usize;
        while i < configured {
            let slot = self.markets[i].engine_slot();
            // ONLY genuine unabsorbed-loss ledgers gate the hlock. Deliberately NOT the
            // side mode byte — see the note above the function for why that term was
            // dropped.
            // F-03: `explicit_unallocated_loss_*` is a REALIZED write-off — whole atoms of
            // social loss that `kernel_normalize_social_loss_carry` could not assign to any
            // side's weight, saturating-added on a leg clear and cleared only at asset
            // retirement. It is not pending, absorbable loss: no crank or settlement will
            // ever consume it. Gating the group-wide hlock on it recreated exactly the
            // HOSTAGE this predicate was narrowed to avoid (see the note above) — an ordinary
            // close leaves a dust atom that latches LP/insurance withdrawals and oracle
            // reconfiguration for EVERY domain in the group, and for asset 0 (which RETIRE
            // rejects) the latch is permanent. Its written siblings `social_loss_dust_*` /
            // `social_loss_remainder_*` were already, correctly, not gated here for the same
            // reason. `pending_domain_loss_barrier_*` remains: it IS genuine loss awaiting
            // domain absorption. The write-off still blocks slot reactivation/retire through
            // `asset_state_is_empty_for_activation`, so it is not lost — only demoted from a
            // group-freeze signal to the residual-state signal it actually is.
            if slot.pending_domain_loss_barrier_long.get() != 0
                || slot.pending_domain_loss_barrier_short.get() != 0
            {
                return true;
            }
            i += 1;
        }
        false
    }

    fn try_clear_bankruptcy_hlock_if_healthy(&mut self) -> V16Result<()> {
        if !decode_bool(self.header.bankruptcy_hlock_active)? {
            return Ok(());
        }
        if self.header.negative_pnl_account_count.get() == 0
            && self.header.stale_certificate_count.get() == 0
            && self.header.b_stale_account_count.get() == 0
            && self.header.pnl_pos_tot.get() == 0
            && self.header.recovery_reason.try_to_runtime()?.is_none()
            && !self.group_has_unabsorbed_bankruptcy_loss()
        {
            self.header.bankruptcy_hlock_active = 0;
        }
        Ok(())
    }

    fn charge_account_fee_current_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        requested_fee: u128,
    ) -> V16Result<u128> {
        if requested_fee == 0 || account.header.pnl.get() < 0 {
            return Ok(0);
        }
        let charged = requested_fee.min(account.header.capital.get());
        if charged == 0 {
            return Ok(0);
        }
        let vault_before = self.header.vault.get();
        let capital = account
            .header
            .capital
            .get()
            .checked_sub(charged)
            .ok_or(V16Error::CounterUnderflow)?;
        let c_tot = self
            .header
            .c_tot
            .get()
            .checked_sub(charged)
            .ok_or(V16Error::CounterUnderflow)?;
        let insurance = self
            .header
            .insurance
            .get()
            .checked_add(charged)
            .ok_or(V16Error::ArithmeticOverflow)?;
        account.header.capital = V16PodU128::new(capital);
        self.header.c_tot = V16PodU128::new(c_tot);
        self.header.insurance = V16PodU128::new(insurance);
        TokenValueFlowProofV16::account_capital_to_insurance(
            charged,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        account.header.health_cert.valid = 0;
        Ok(charged)
    }

    #[cfg(kani)]
    pub fn kani_charge_account_fee_current_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        requested_fee: u128,
    ) -> V16Result<u128> {
        self.charge_account_fee_current_not_atomic(account, requested_fee)
    }

    // Kani-only entry to the bare negative-PnL principal-settlement transition,
    // bypassing the O(N) loop-based shape validation so an inductive proof can
    // assume a decomposed loop-free invariant and apply just this transition.
    #[cfg(kani)]
    pub fn kani_settle_negative_pnl_from_principal_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        self.settle_negative_pnl_from_principal_core_not_atomic(account)
    }

    fn charge_account_fee_after_loss_settlement(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        requested_fee: u128,
    ) -> V16Result<u128> {
        self.settle_account_side_effects_not_atomic(
            account,
            self.header.config.public_b_chunk_atoms.get(),
        )?;
        if decode_bool(account.header.b_stale_state)? || Self::has_b_stale_leg(&account.as_view())?
        {
            return Err(V16Error::BStale);
        }
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        let charged = self.charge_account_fee_current_not_atomic(account, requested_fee)?;
        self.validate_shape_audit_scan()?;
        Ok(charged)
    }

    fn charge_account_fee_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        requested_fee: u128,
    ) -> V16Result<u128> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        self.charge_account_fee_after_loss_settlement(account, requested_fee)
    }

    fn resolved_positive_payout_ready(&self) -> V16Result<bool> {
        if self.header.b_stale_account_count.get() != 0
            || self.header.stale_certificate_count.get() != 0
            || self.header.negative_pnl_account_count.get() != 0
            || self.header.resolved_payout_blocker_count.get() != 0
        {
            return Ok(false);
        }
        Ok(true)
    }

    fn recompute_resolved_payout_rate(&mut self) -> V16Result<()> {
        let ledger = V16Core::kernel_recompute_resolved_payout_rate(
            self.header.resolved_payout_ledger.try_to_runtime()?,
        )?;
        self.header.resolved_payout_ledger = ResolvedPayoutLedgerV16Account::from_runtime(&ledger);
        Ok(())
    }

    fn initialize_resolved_payout_ledger_if_needed(&mut self) -> V16Result<()> {
        if decode_bool(self.header.payout_snapshot_captured)? {
            return Ok(());
        }
        let snapshot_residual = self.residual();
        self.header.payout_snapshot = V16PodU128::new(snapshot_residual);
        self.header.payout_snapshot_pnl_pos_tot = V16PodU128::new(self.junior_claim_bound());
        self.header.payout_snapshot_captured = 1;
        self.header.resolved_payout_ledger =
            ResolvedPayoutLedgerV16Account::from_runtime(&ResolvedPayoutLedgerV16 {
                snapshot_residual,
                terminal_claim_exact_receipts_num: 0,
                terminal_claim_bound_unreceipted_num: self.header.pnl_pos_bound_tot_num.get(),
                current_payout_rate_num: 0,
                current_payout_rate_den: 0,
                snapshot_slot: self
                    .header
                    .resolved_slot
                    .get()
                    .max(self.header.current_slot.get()),
                payout_halted: false,
                finalized: false,
            });
        self.recompute_resolved_payout_rate()
    }

    fn create_resolved_payout_receipt_if_needed(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        if decode_bool(account.header.resolved_payout_receipt.present)? {
            return Ok(());
        }
        self.initialize_resolved_payout_ledger_if_needed()?;
        let terminal_positive_claim_face = account.header.pnl.get().max(0) as u128;
        let prior_bound_contribution_num =
            V16Core::bound_num_from_amount(terminal_positive_claim_face)?;
        let mut ledger = self.header.resolved_payout_ledger.try_to_runtime()?;
        if V16Core::bound_num_from_amount(terminal_positive_claim_face)?
            > prior_bound_contribution_num
            || prior_bound_contribution_num > ledger.terminal_claim_bound_unreceipted_num
        {
            ledger.payout_halted = true;
            self.header.resolved_payout_ledger =
                ResolvedPayoutLedgerV16Account::from_runtime(&ledger);
            return Err(V16Error::RecoveryRequired);
        }
        ledger.terminal_claim_bound_unreceipted_num = ledger
            .terminal_claim_bound_unreceipted_num
            .checked_sub(prior_bound_contribution_num)
            .ok_or(V16Error::CounterUnderflow)?;
        ledger.terminal_claim_exact_receipts_num = ledger
            .terminal_claim_exact_receipts_num
            .checked_add(V16Core::bound_num_from_amount(
                terminal_positive_claim_face,
            )?)
            .ok_or(V16Error::ArithmeticOverflow)?;
        self.header.resolved_payout_ledger = ResolvedPayoutLedgerV16Account::from_runtime(&ledger);
        account.header.resolved_payout_receipt =
            ResolvedPayoutReceiptV16Account::from_runtime(&ResolvedPayoutReceiptV16 {
                present: true,
                prior_bound_contribution_num,
                live_released_face_at_receipt: 0,
                terminal_positive_claim_face,
                paid_effective: 0,
                finalized: false,
            });
        self.recompute_resolved_payout_rate()
    }

    fn resolved_receipt_claimable_now(&self, receipt: ResolvedPayoutReceiptV16) -> V16Result<u128> {
        let ledger = self.header.resolved_payout_ledger.try_to_runtime()?;
        Self::resolved_receipt_claimable_against_ledger(receipt, ledger)
    }

    fn resolved_receipt_claimable_against_ledger(
        receipt: ResolvedPayoutReceiptV16,
        ledger: ResolvedPayoutLedgerV16,
    ) -> V16Result<u128> {
        PortfolioV16View::validate_resolved_payout_receipt_static(receipt)?;
        if !receipt.present {
            return Ok(0);
        }
        if ledger.payout_halted {
            return Err(V16Error::RecoveryRequired);
        }
        let gross = wide_mul_div_floor_u128(
            receipt.terminal_positive_claim_face,
            ledger.current_payout_rate_num,
            ledger.current_payout_rate_den,
        );
        gross
            .checked_sub(receipt.paid_effective)
            .ok_or(V16Error::InvalidLeg)
    }

    #[cfg(kani)]
    pub fn kani_resolved_receipt_claimable_against_ledger(
        receipt: ResolvedPayoutReceiptV16,
        ledger: ResolvedPayoutLedgerV16,
    ) -> V16Result<u128> {
        Self::resolved_receipt_claimable_against_ledger(receipt, ledger)
    }

    fn preflight_convert_released_pnl_to_capital(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        // The account is validated once, two statements below, by
        // ensure_favorable_action_allowed; a second full scan here only costs
        // compute on the max-source shape.
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live
            || decode_bool(self.header.payout_snapshot_captured)?
        {
            return Err(V16Error::LockActive);
        }
        self.ensure_favorable_action_allowed(account)
    }

    fn convert_released_pnl_to_capital_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        disposition: ReleasedPnlConversionDispositionV16,
    ) -> V16Result<u128> {
        let pos = account.header.pnl.get().max(0) as u128;
        let released = pos.saturating_sub(account.header.reserved_pnl.get());
        if released == 0 {
            return Ok(0);
        }
        let has_source_claims = Self::account_has_source_claims(&account.as_view())?;
        if has_source_claims
            && (Self::account_has_source_liens(&account.as_view())
                || self.account_has_active_source_claim_exposure(&account.as_view())?)
        {
            return Err(V16Error::LockActive);
        }
        let converted = if has_source_claims {
            self.account_source_realizable_support(&account.as_view(), released)?
        } else if decode_market_mode(self.header.mode)? == MarketModeV16::Live {
            0
        } else {
            self.haircut_effective_support(released, self.residual(), self.junior_claim_bound())?
        };
        if converted == 0 {
            return Err(V16Error::LockActive);
        }
        self.apply_released_pnl_conversion_core_not_atomic(
            account,
            pos,
            converted,
            has_source_claims,
            disposition,
        )
    }

    fn apply_released_pnl_conversion_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        pos: u128,
        converted: u128,
        has_source_claims: bool,
        disposition: ReleasedPnlConversionDispositionV16,
    ) -> V16Result<u128> {
        let (consumption, preburned_source_claim_num) = if has_source_claims {
            let (consumption, preburned_source_claim_num, _) = self
                .consume_validated_account_source_credit_not_atomic(
                    account, converted, true, true,
                )?;
            (consumption, preburned_source_claim_num)
        } else {
            let residual = self.residual();
            let junior_bound = self.junior_claim_bound();
            (
                SourceCreditConsumptionV16 {
                    face_burn: self.face_claim_to_burn_for_support(
                        converted,
                        residual,
                        junior_bound,
                    )?,
                    counterparty_credit_consumed: 0,
                    insurance_credit_consumed: 0,
                },
                0,
            )
        };
        self.apply_released_pnl_conversion_with_consumption_core_not_atomic(
            account,
            pos,
            converted,
            consumption,
            preburned_source_claim_num,
            disposition,
        )
    }

    fn apply_released_pnl_conversion_with_consumption_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        pos: u128,
        converted: u128,
        consumption: SourceCreditConsumptionV16,
        preburned_source_claim_num: u128,
        disposition: ReleasedPnlConversionDispositionV16,
    ) -> V16Result<u128> {
        if converted == 0 || converted > pos.saturating_sub(account.header.reserved_pnl.get()) {
            return Err(V16Error::InvalidConfig);
        }
        let vault_before = self.header.vault.get();
        let retain_haircut_face = matches!(
            disposition,
            ReleasedPnlConversionDispositionV16::RetainHaircutFaceForTerminalDomain { .. }
        );
        let (pnl_debit, _retained_haircut_face) =
            V16Core::kernel_released_pnl_conversion_partition(
                pos,
                converted,
                consumption.face_burn,
                retain_haircut_face,
            )?;
        let face_i128 = i128::try_from(pnl_debit).map_err(|_| V16Error::ArithmeticOverflow)?;
        let new_pnl = account
            .header
            .pnl
            .get()
            .checked_sub(face_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        match disposition {
            ReleasedPnlConversionDispositionV16::ConsumeHaircutFace => {
                self.set_account_pnl_after_source_claim_burn(
                    account,
                    new_pnl,
                    preburned_source_claim_num,
                )?;
            }
            ReleasedPnlConversionDispositionV16::RetainHaircutFaceForTerminalDomain {
                source_domain,
                source_claim_num,
            } => {
                // The terminal caller consumes the domain's backing directly, so it
                // never pre-burns account claims; the domain-first burn below is the
                // only account-claim retirement on this arm.
                if preburned_source_claim_num != 0 {
                    return Err(V16Error::InvalidConfig);
                }
                self.burn_account_source_claim_bound_num_domain_first(
                    account,
                    source_domain,
                    source_claim_num,
                )?;
                self.set_account_pnl_after_source_claim_burn(
                    account,
                    new_pnl,
                    V16Core::bound_num_from_amount(pnl_debit)?,
                )?;
            }
        }
        account.header.capital = V16PodU128::new(
            account
                .header
                .capital
                .get()
                .checked_add(converted)
                .ok_or(V16Error::ArithmeticOverflow)?,
        );
        self.header.c_tot = V16PodU128::new(
            self.header
                .c_tot
                .get()
                .checked_add(converted)
                .ok_or(V16Error::ArithmeticOverflow)?,
        );
        self.header.pnl_matured_pos_tot = V16PodU128::new(
            self.header
                .pnl_matured_pos_tot
                .get()
                .saturating_sub(pnl_debit),
        );
        let protocol_surplus_consumed = converted
            .checked_sub(consumption.counterparty_credit_consumed)
            .and_then(|v| v.checked_sub(consumption.insurance_credit_consumed))
            .ok_or(V16Error::CounterUnderflow)?;
        TokenValueFlowProofV16::support_to_account_capital(
            converted,
            consumption.counterparty_credit_consumed,
            consumption.insurance_credit_consumed,
            protocol_surplus_consumed,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        account.header.health_cert.valid = 0;
        Ok(converted)
    }

    pub fn convert_released_pnl_to_capital_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        // #137: release any source-credit lien whose exposure has already closed
        // BEFORE the preflight, so a stale lien cannot hold the conversion in Live.
        // Mirrors upstream av/codex/blocker-dos-flat-source-lien-convert-20260728
        // ("Release flat source liens before PnL conversion", 4d4f9ed8), minus the
        // contracts layer this fork does not carry.
        if Self::valid_source_lien_effective_reserved_sum(&account.as_view())? != 0 {
            self.release_account_source_credit_liens_if_unneeded_not_atomic(account)?;
        }
        self.preflight_convert_released_pnl_to_capital(&account.as_view())?;
        let converted = self.convert_released_pnl_to_capital_core_not_atomic(
            account,
            ReleasedPnlConversionDispositionV16::ConsumeHaircutFace,
        )?;
        if converted != 0 {
            self.validate_shape()?;
            account.validate_with_market(&self.as_view())?;
        }
        Ok(converted)
    }

    // #137: NOT cfg-gated. The Live release path must exist in the deployed
    // binary; gating it to kani/fuzz is what left the IM lien permanent.
    pub fn release_account_source_credit_liens_if_unneeded_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        self.release_account_source_credit_liens_if_unneeded_core_not_atomic(account)
    }

    // fdf11670: the crank dispatch calls this core directly. The fork body is kept
    // whole -- per-domain targeting, the canonical backing-expiry transition, and
    // the terminal re-certification are fork behaviour upstream does not carry.
    fn release_account_source_credit_liens_if_unneeded_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        self.settle_account_side_effects_not_atomic(
            account,
            self.header.config.public_b_chunk_atoms.get(),
        )?;
        self.certify_account_after_local_settlement_with_price_override(account, None)?;
        let no_positive = Self::account_no_positive_credit_equity(&account.as_view())?;
        let cert = account.header.health_cert.try_to_runtime()?;
        if no_positive < 0 || (no_positive as u128) < cert.certified_initial_req {
            return Err(V16Error::LockActive);
        }

        let mut released_effective = 0u128;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source_snapshot = account.header.source_domains[slot];
            if source_snapshot.has_default_sparse_tag() && !source_snapshot.is_occupied() {
                break;
            }
            if !source_snapshot.is_occupied() {
                slot += 1;
                continue;
            }
            let d = source_snapshot.domain.get() as usize;
            self.domain_asset_side(d)?;
            // Preserve upstream's targeted semantics: a healthy account may carry
            // liens for several source domains, but only a domain whose own exposure
            // has closed is eligible for release.
            if self.account_has_active_exposure_for_source_domain(&account.as_view(), d)? {
                slot += 1;
                continue;
            }
            let effective = source_snapshot.source_lien_effective_reserved.get();
            let counterparty_backing = source_snapshot.source_lien_counterparty_backing_num.get();
            let insurance_backing = source_snapshot.source_lien_insurance_backing_num.get();
            if counterparty_backing != 0 {
                let bucket = self.backing_bucket_for_domain(d)?;
                if bucket.status == BackingBucketStatusV16::Fresh
                    && bucket.expiry_slot <= self.header.current_slot.get()
                {
                    // Apply the canonical expiry transition before unwinding. It
                    // moves valid liened backing to impaired counters; the release
                    // below then clears those counters without minting fresh backing.
                    self.expire_source_backing_bucket_not_atomic(
                        d,
                        self.header.current_slot.get(),
                    )?;
                }
            }
            // 6c8d94bc: a GLOBALLY impaired counterparty lien must first move into
            // this account's impaired-claim lane. The release arm below zeroes
            // `source_claim_liened_num` WITHOUT crediting `source_claim_impaired_num`,
            // which is correct only for backing that is still valid: on an impaired
            // bucket it would hand the account back `face` of UNLIENED source claim
            // (`bound - liened - impaired` grows) against principal expiry already
            // forfeited. Crystallize the utilization fee, retire the market-side
            // impaired counters and relabel the account's claim instead, exactly as
            // the Resolved wind-down already does in
            // prepare_one_source_domain_for_resolved_close_not_atomic.
            let bucket = self.backing_bucket_for_domain(d)?;
            let source_credit = self.source_credit_for_domain(d)?;
            let reservation = self.insurance_reservation_for_domain(d)?;
            if V16Core::kernel_flat_source_lien_normalization(
                source_snapshot.source_claim_liened_num.get(),
                counterparty_backing,
                insurance_backing,
                bucket.status,
                bucket.expiry_slot,
                self.header.current_slot.get(),
                bucket.valid_liened_backing_num,
                bucket.impaired_liened_backing_num,
                source_credit.valid_liened_backing_num,
                source_credit.impaired_liened_backing_num,
                reservation.valid_liened_insurance_num,
                source_credit.valid_liened_insurance_num,
            ) == FlatSourceLienNormalizationV16::ImpairCounterparty
            {
                self.collect_account_backing_utilization_fee_for_domain_not_atomic(account, d)?;
                self.retire_source_credit_lien_from_counterparty_impaired_not_atomic(
                    d,
                    counterparty_backing,
                )?;
                let impaired_effective =
                    Self::impair_account_source_credit_counterparty_lien_fields(account, d)?;
                released_effective = released_effective
                    .checked_add(impaired_effective)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                slot += 1;
                continue;
            }
            if effective != 0 {
                released_effective = released_effective
                    .checked_add(effective)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                self.release_account_source_credit_lien_for_domain_not_atomic(account, d, false)?;
            }
            slot += 1;
        }
        account.compact_source_domains();
        // The releases above advanced the market `risk_epoch` and therefore retired
        // the certificate this function derived for itself at the top. Leave a
        // current one instead of clearing the flag, so a caller can act on the
        // post-release state in the same instruction. This matches how every other
        // self-contained mutating operation here ends (reduce/liquidate, batch
        // trade); `health_cert.valid = 0` is the leaf-mutator idiom, and this
        // function is not a leaf -- it mode-gates, settles, certifies and runs its
        // own margin gate. Certifying before the validations below also means the
        // new certificate is itself covered by them.
        self.certify_account_after_local_settlement_with_price_override(account, None)?;
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()?;
        Ok(released_effective)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn impair_account_source_credit_lien_from_insurance_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        domain: usize,
    ) -> V16Result<u128> {
        self.domain_asset_side(domain)?;
        account.validate_with_market(&self.as_view())?;
        let source = account.as_view().source_domain(domain)?;
        let insurance_backing = source.source_lien_insurance_backing_num.get();
        if insurance_backing == 0 {
            return Ok(0);
        }
        let effective = insurance_backing / BOUND_SCALE;
        let face = source.source_claim_insurance_liened_num.get();
        if effective == 0 || face == 0 {
            return Err(V16Error::InvalidLeg);
        }

        self.impair_source_credit_lien_from_insurance_core_not_atomic(domain, insurance_backing)?;
        let effective = Self::impair_account_source_credit_insurance_lien_fields(
            account, domain, face, effective,
        )?;
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()?;
        Ok(effective)
    }

    fn preflight_cure_and_cancel_close(
        &self,
        account: &PortfolioV16View<'_>,
        optional_deposit: u128,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        let ledger = account.header.close_progress.try_to_runtime()?;
        if !ledger.active
            || ledger.finalized
            || ledger.canceled
            || ledger.has_irreversible_progress()
            || ledger.residual_remaining != ledger.gross_loss_at_close_start
        {
            return Err(V16Error::LockActive);
        }
        let domain =
            self.insurance_domain_index(ledger.asset_index as usize, ledger.domain_side)?;
        let (asset_index, side) = self.domain_asset_side(domain)?;
        let slot = self.markets[asset_index].engine_slot();
        let barrier_count = match side {
            SideV16::Long => slot.pending_domain_loss_barrier_long.get(),
            SideV16::Short => slot.pending_domain_loss_barrier_short.get(),
        };
        if barrier_count == 0 {
            return Err(V16Error::LockActive);
        }
        let escrow_total = account
            .header
            .cancel_deposit_escrow
            .get()
            .checked_add(optional_deposit)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let new_vault = self
            .header
            .vault
            .get()
            .checked_add(optional_deposit)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if new_vault > MAX_VAULT_TVL {
            return Err(V16Error::InvalidConfig);
        }
        let _new_capital = account
            .header
            .capital
            .get()
            .checked_add(escrow_total)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let _new_c_tot = self
            .header
            .c_tot
            .get()
            .checked_add(escrow_total)
            .ok_or(V16Error::ArithmeticOverflow)?;
        Ok(())
    }

    fn cure_and_cancel_close_with_cert_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        optional_deposit: u128,
        cert: HealthCertV16,
    ) -> V16Result<()> {
        self.preflight_cure_and_cancel_close(&account.as_view(), optional_deposit)?;
        let ledger = account.header.close_progress.try_to_runtime()?;
        let vault_before = self.header.vault.get();
        let escrow_before = account.header.cancel_deposit_escrow.get();
        let escrow_total = escrow_before
            .checked_add(optional_deposit)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let new_vault = self
            .header
            .vault
            .get()
            .checked_add(optional_deposit)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let new_capital = account
            .header
            .capital
            .get()
            .checked_add(escrow_total)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let new_c_tot = self
            .header
            .c_tot
            .get()
            .checked_add(escrow_total)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let escrow_i128 = i128::try_from(escrow_total).map_err(|_| V16Error::ArithmeticOverflow)?;
        let cured_equity = cert
            .certified_equity
            .checked_add(escrow_i128)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if cured_equity < 0 || (cured_equity as u128) < cert.certified_initial_req {
            return Err(V16Error::InvalidConfig);
        }

        self.header.vault = V16PodU128::new(new_vault);
        self.header.c_tot = V16PodU128::new(new_c_tot);
        account.header.capital = V16PodU128::new(new_capital);
        account.header.cancel_deposit_escrow = V16PodU128::new(0);
        let domain =
            self.insurance_domain_index(ledger.asset_index as usize, ledger.domain_side)?;
        let count = self
            .pending_domain_loss_barrier_count(ledger.asset_index as usize, ledger.domain_side)?;
        if count == 0 {
            return Err(V16Error::CounterUnderflow);
        }
        let (asset_index, side) = self.domain_asset_side(domain)?;
        self.set_pending_domain_loss_barrier_count(asset_index, side, count - 1)?;
        account.header.close_progress =
            CloseProgressLedgerV16Account::from_runtime(&CloseProgressLedgerV16 {
                active: false,
                finalized: false,
                canceled: true,
                ..ledger
            });
        TokenValueFlowProofV16::close_cure_to_account_capital(
            optional_deposit,
            escrow_before,
            escrow_total,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        account.header.health_cert.valid = 0;
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()
    }

    pub fn cure_and_cancel_close_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        optional_deposit: u128,
    ) -> V16Result<()> {
        self.preflight_cure_and_cancel_close(&account.as_view(), optional_deposit)?;
        let cert = self.full_account_refresh_not_atomic(account)?;
        self.cure_and_cancel_close_with_cert_not_atomic(account, optional_deposit, cert)
    }

    pub fn sync_account_fee_to_slot_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        now_slot: u64,
        fee_rate_per_slot: u128,
    ) -> V16Result<u128> {
        account.validate_with_market(&self.as_view())?;
        if decode_market_mode(self.header.mode)? == MarketModeV16::Recovery {
            return Err(V16Error::LockActive);
        }
        if now_slot < account.header.last_fee_slot.get() {
            return Err(V16Error::Stale);
        }
        let nonflat = !active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get));
        let fee_anchor = if decode_market_mode(self.header.mode)? == MarketModeV16::Live && nonflat
        {
            self.account_fee_anchor_for_loss_currentness(&account.as_view(), now_slot)?
        } else if decode_market_mode(self.header.mode)? == MarketModeV16::Resolved {
            self.header.resolved_slot.get()
        } else {
            now_slot
        };
        if fee_anchor <= account.header.last_fee_slot.get() {
            return Ok(0);
        }
        let dt = fee_anchor - account.header.last_fee_slot.get();
        let raw_fee = U256::from_u128(fee_rate_per_slot)
            .checked_mul(U256::from_u64(dt))
            .ok_or(V16Error::ArithmeticOverflow)?;
        let requested_fee = raw_fee.try_into_u128().unwrap_or(u128::MAX);
        if decode_market_mode(self.header.mode)? == MarketModeV16::Live && nonflat {
            if let PermissionlessProgressOutcomeV16::AccountBChunk(_) = self
                .settle_account_side_effects_not_atomic(
                    account,
                    self.header.config.public_b_chunk_atoms.get(),
                )?
            {
                return Err(V16Error::BStale);
            }
        }
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        let charged = self.charge_account_fee_current_not_atomic(account, requested_fee)?;
        account.header.last_fee_slot = V16PodU64::new(fee_anchor);
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()?;
        Ok(charged)
    }

    pub fn withdraw_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        amount: u128,
    ) -> V16Result<()> {
        if amount == 0 {
            return Ok(());
        }
        account.validate_with_market(&self.as_view())?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        if !active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get)) {
            return Err(V16Error::Stale);
        }
        // A `canceled` close ledger (left behind by cure_and_cancel_close) is inert:
        // validate_close_progress_ledger_with_market guarantees it carries no
        // irreversible progress and residual_remaining == gross_loss_at_close_start,
        // so it represents no obligation. Blocking withdraw on it permanently freezes a
        // flat, solvent user who cured a forced close. Only an active/in-progress close
        // ledger must block withdrawal. A finalized zero-residual close (E6) is likewise
        // inert -- it paid out in full and only stays `active` to preserve close
        // identity/history.
        let close_progress = account.header.close_progress.try_to_runtime()?;
        if close_progress != CloseProgressLedgerV16::EMPTY
            && !close_progress.canceled
            && !close_progress.is_finalized_inert()
        {
            return Err(V16Error::LockActive);
        }
        self.settle_negative_pnl_from_principal_core_not_atomic(account)?;
        if account.header.pnl.get() < 0 || amount > account.header.capital.get() {
            return Err(V16Error::LockActive);
        }
        let post_capital = account
            .header
            .capital
            .get()
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        let equity_after = account_equity_from_parts(
            post_capital,
            account.header.pnl.get(),
            account.header.fee_credits.get(),
        )?;
        if equity_after < 0 {
            return Err(V16Error::InvalidConfig);
        }

        let vault_before = self.header.vault.get();
        let c_tot = self
            .header
            .c_tot
            .get()
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        let vault = self
            .header
            .vault
            .get()
            .checked_sub(amount)
            .ok_or(V16Error::CounterUnderflow)?;
        account.header.capital = V16PodU128::new(post_capital);
        self.header.c_tot = V16PodU128::new(c_tot);
        self.header.vault = V16PodU128::new(vault);
        TokenValueFlowProofV16::account_capital_to_external_out(amount, vault_before, vault)?
            .validate()?;
        account.header.health_cert.valid = 0;
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()
    }

    /// fork feature A-6 (zero-copy view form): advance the stress-envelope accumulator. Ported
    /// verbatim from the fork ViewMut writer; the runtime-mirror twin is DROPPED (no runtime
    /// MarketGroupV16 at frozen). Operates directly on the POD header. Resets a stale envelope
    /// (epoch advanced, different slot, not in active-close) before accruing; flips
    /// `threshold_stress_active` true when the accumulator crosses STRESS_ENVELOPE_TRIGGER_BPS_E9.
    pub fn apply_stress_envelope_progress(
        &mut self,
        consumption_bps_e9: u128,
        now_slot: u64,
    ) -> V16Result<()> {
        if consumption_bps_e9 == 0 {
            return Ok(());
        }
        let bool_on = decode_bool(self.header.threshold_stress_active)?;
        let active_close = decode_market_mode(self.header.mode)? == MarketModeV16::Recovery
            || decode_bool(self.header.loss_stale_active)?;
        let start_epoch = self.header.stress_envelope_start_credit_epoch.get();
        let start_slot = self.header.stress_envelope_start_slot.get();
        if bool_on
            && start_epoch != u64::MAX
            && self.header.risk_epoch.get() > start_epoch
            && start_slot != now_slot
            && !active_close
        {
            self.clear_stress_envelope_v16();
        }

        let next_acc = self
            .header
            .stress_consumption_bps_e9_since_envelope
            .get()
            .saturating_add(consumption_bps_e9);
        self.header.stress_consumption_bps_e9_since_envelope = V16PodU128::new(next_acc);

        if next_acc >= STRESS_ENVELOPE_TRIGGER_BPS_E9
            && !decode_bool(self.header.threshold_stress_active)?
        {
            self.header.threshold_stress_active = encode_bool(true);
            self.header.stress_envelope_start_slot = V16PodU64::new(now_slot);
            self.header.stress_envelope_start_credit_epoch = self.header.risk_epoch;
        }
        Ok(())
    }

    /// fork feature A-6 (zero-copy view form): clear the envelope — zero the accumulator, restore
    /// the slot/epoch sentinels to u64::MAX, and clear the active flag.
    pub fn clear_stress_envelope_v16(&mut self) {
        self.header.stress_consumption_bps_e9_since_envelope = V16PodU128::default();
        self.header.stress_envelope_start_slot = V16PodU64::new(u64::MAX);
        self.header.stress_envelope_start_credit_epoch = V16PodU64::new(u64::MAX);
        self.header.threshold_stress_active = encode_bool(false);
    }

    pub fn resolve_market_not_atomic(&mut self, resolved_slot: u64) -> V16Result<()> {
        decode_market_mode(self.header.mode)?;
        if resolved_slot < self.header.current_slot.get() {
            return Err(V16Error::Stale);
        }
        self.header.mode = encode_market_mode(MarketModeV16::Resolved);
        self.header.resolved_slot = V16PodU64::new(resolved_slot);
        self.header.current_slot = V16PodU64::new(resolved_slot);
        self.header.loss_stale_active = 0;
        // A-6: clear the stress envelope on resolution (fork 9cee487) — restore accumulator +
        // sentinels to the no-envelope-open state BEFORE validate_shape so the pairing invariant holds.
        self.clear_stress_envelope_v16();
        self.validate_shape()
    }

    /// Advances only the clock used by resolved settlement. The wrapper must
    /// authenticate `authenticated_slot` (for Solana, from the Clock sysvar).
    /// No price, funding, value, claim, or lifecycle field is changed.
    /// (upstream 44847fd5)
    pub fn advance_resolved_slot_not_atomic(&mut self, authenticated_slot: u64) -> V16Result<()> {
        let next = V16Core::kernel_advance_resolved_slot(
            decode_market_mode(self.header.mode)?,
            self.header.current_slot.get(),
            authenticated_slot,
        )?;
        self.header.current_slot = V16PodU64::new(next);
        Ok(())
    }

    // A resolved-payout receipt that has been paid its full entitlement at the TERMINAL
    // payout rate (no unreceipted bound remains, so the rate can no longer rise) holds
    // only unrecoverable insolvency bad debt: the haircut shortfall (face - paid) is not
    // an open obligation. The only finalize site requires paid_effective == FULL face,
    // which is unreachable under a haircut, so the receipt would otherwise stay
    // `present && !finalized` forever and permanently block the portfolio from
    // dematerializing (stranding insurance + backing earnings + residual vault + rent).
    // Clear such a fully-diluted receipt so the account can close.
    fn clear_fully_diluted_resolved_receipt_if_terminal(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        let receipt = account.header.resolved_payout_receipt.try_to_runtime()?;
        if !receipt.present || receipt.finalized {
            return Ok(());
        }
        let ledger = self.header.resolved_payout_ledger.try_to_runtime()?;
        // Rate is terminal only once all junior bound has been receipted/refined.
        if ledger.terminal_claim_bound_unreceipted_num != 0 {
            return Ok(());
        }
        if self.resolved_receipt_claimable_now(receipt)? != 0 {
            return Ok(());
        }
        account.header.resolved_payout_receipt =
            ResolvedPayoutReceiptV16Account::from_runtime(&ResolvedPayoutReceiptV16::EMPTY);
        Ok(())
    }

    fn preflight_claim_resolved_payout_topup(
        &self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Resolved
            || !decode_bool(self.header.payout_snapshot_captured)?
        {
            return Err(V16Error::LockActive);
        }
        Ok(())
    }

    /// Realize one canonical source domain before its claim face enters the
    /// junior receipt pool. Each call consumes only that domain's whole-atom
    /// backing entitlement, demotes its unconverted haircut face to ordinary
    /// junior PnL, and removes exactly that source attribution. This keeps the
    /// terminal continuation bounded without changing the final value partition.
    fn realize_one_source_domain_for_resolved_close_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<bool> {
        if decode_bool(account.header.resolved_payout_receipt.present)? {
            // The face is already frozen into the receipt pool.
            return Ok(false);
        }
        account.compact_source_domains();
        let mut claim_source = None;
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.header.source_domains[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if source.is_occupied() && source.source_claim_bound_num.get() != 0 {
                claim_source = Some(source);
                break;
            }
            slot += 1;
        }
        let Some(source) = claim_source else {
            return Ok(false);
        };
        let pos = account.header.pnl.get().max(0) as u128;
        let released = pos.saturating_sub(account.header.reserved_pnl.get());
        let source_domain = source.domain.get() as usize;
        let source_claim_num = source.source_claim_bound_num.get();
        let claim_num = Self::source_claim_unliened_num(&account.as_view(), source_domain)?
            .min(V16Core::bound_num_from_amount(released)?);
        let mut converted = 0u128;
        if claim_num != 0 {
            self.validate_source_domain_ledger_current(source_domain)?;
            let rate = self
                .source_credit_for_domain(source_domain)?
                .credit_rate_num;
            let credited_num = U256::from_u128(claim_num)
                .checked_mul(U256::from_u128(rate))
                .and_then(|v| v.checked_div(U256::from_u128(CREDIT_RATE_SCALE)))
                .and_then(|v| v.try_into_u128())
                .ok_or(V16Error::ArithmeticOverflow)?;
            converted = (credited_num / BOUND_SCALE)
                .min(self.source_credit_available_backing_num(source_domain)? / BOUND_SCALE);
            if converted != 0 {
                let consumption = self.consume_source_domain_credit_for_effective_not_atomic(
                    source_domain,
                    converted,
                )?;
                if V16Core::bound_num_from_amount(consumption.face_burn)? > claim_num {
                    return Err(V16Error::InvalidConfig);
                }
                self.apply_released_pnl_conversion_with_consumption_core_not_atomic(
                    account,
                    pos,
                    converted,
                    consumption,
                    0,
                    ReleasedPnlConversionDispositionV16::RetainHaircutFaceForTerminalDomain {
                        source_domain,
                        source_claim_num,
                    },
                )?;
            }
        }
        if converted == 0 {
            // Zero-rate, sub-atom, or impaired source face remains a junior claim;
            // only its source-specific backing attribution is terminally removed.
            self.burn_account_source_claim_bound_num_domain_first(
                account,
                source_domain,
                source_claim_num,
            )?;
            account.header.health_cert.valid = 0;
        }

        // The source claim is removed in full, but only backed value was converted
        // into senior capital. Preserve the remainder as terminal-only junior PnL so
        // another source cannot realize the same face on a later bounded call.
        let source_attributed_face =
            V16Core::amount_from_bound_num(source_claim_num)?.min(released);
        let reserved_pnl = V16Core::kernel_retain_terminal_source_haircut(
            pos,
            account.header.reserved_pnl.get(),
            source_attributed_face,
            converted,
        )?;
        account.header.reserved_pnl = V16PodU128::new(reserved_pnl);

        // If the payout snapshot was captured before this account realized (another
        // winner closed first), the realized face is still counted in the ledger's
        // unreceipted bound. Refine it out, or the stale bound dilutes the payout
        // rate forever and blocks every remaining receipt from reaching the
        // terminal rate (never finalized, never clearable).
        if decode_bool(self.header.payout_snapshot_captured)? {
            let pos_after = account.header.pnl.get().max(0) as u128;
            let face_burned = pos
                .checked_sub(pos_after)
                .ok_or(V16Error::CounterUnderflow)?;
            let ledger = self.header.resolved_payout_ledger.try_to_runtime()?;
            let decrease_num = V16Core::bound_num_from_amount(face_burned)?
                .min(ledger.terminal_claim_bound_unreceipted_num);
            if decrease_num != 0 {
                self.refine_resolved_unreceipted_bound_not_atomic(decrease_num)?;
            }
        }
        account.compact_source_domains();
        Ok(true)
    }

    #[cfg(kani)]
    pub fn kani_realize_one_source_domain_for_resolved_close_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<bool> {
        self.realize_one_source_domain_for_resolved_close_not_atomic(account)
    }

    /// Commit at most one source-domain preparation mutation for resolved
    /// settlement. K/F settlement can reduce positive PnL and burn its source
    /// claim, so expired or impaired backing and persisted liens must be handled
    /// before those side effects or terminal realization runs.
    fn prepare_one_source_domain_for_resolved_close_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<Option<ResolvedSourcePreparationV16>> {
        if !Self::account_has_source_claims(&account.as_view())? {
            return Ok(None);
        }

        account.compact_source_domains();
        let current_slot = self.header.current_slot.get();
        let mut slot = 0usize;
        while slot < PORTFOLIO_SOURCE_DOMAIN_CAP {
            let source = account.header.source_domains[slot];
            if source.has_default_sparse_tag() && !source.is_occupied() {
                break;
            }
            if !source.is_occupied() {
                slot += 1;
                continue;
            }

            let domain = source.domain.get() as usize;
            self.domain_asset_side(domain)?;
            let bucket = self.backing_bucket_for_domain(domain)?;
            let account_counterparty_backing = source.source_lien_counterparty_backing_num.get();
            if account_counterparty_backing != 0
                && bucket.status == BackingBucketStatusV16::Impaired
            {
                if bucket.impaired_liened_backing_num < account_counterparty_backing {
                    return Err(V16Error::CounterUnderflow);
                }
                self.collect_account_backing_utilization_fee_for_domain_not_atomic(
                    account, domain,
                )?;
                self.retire_source_credit_lien_from_counterparty_impaired_not_atomic(
                    domain,
                    account_counterparty_backing,
                )?;
                Self::impair_account_source_credit_counterparty_lien_fields(account, domain)?;
                self.validate_shape()?;
                account.validate_with_market(&self.as_view())?;
                return Ok(Some(ResolvedSourcePreparationV16::BackingNormalized));
            }
            if bucket.status == BackingBucketStatusV16::Fresh && bucket.expiry_slot <= current_slot
            {
                if source.source_claim_liened_num.get() != 0 {
                    // This fork's release takes the #146 terminal flag; the
                    // Resolved wind-down is exactly upstream's unflagged body.
                    self.release_account_source_credit_lien_for_domain_not_atomic(
                        account, domain, true,
                    )?;
                } else {
                    self.expire_source_backing_bucket_not_atomic(domain, current_slot)?;
                }
                account.compact_source_domains();
                account.header.health_cert.valid = 0;
                self.validate_shape()?;
                account.validate_with_market(&self.as_view())?;
                return Ok(Some(ResolvedSourcePreparationV16::BackingNormalized));
            }
            if source.source_claim_liened_num.get() != 0 {
                // This fork's release takes the #146 terminal flag; the Resolved
                // wind-down is exactly upstream's unflagged body.
                self.release_account_source_credit_lien_for_domain_not_atomic(
                    account, domain, true,
                )?;
                account.compact_source_domains();
                account.header.health_cert.valid = 0;
                self.validate_shape()?;
                account.validate_with_market(&self.as_view())?;
                return Ok(Some(ResolvedSourcePreparationV16::LienReleased));
            }
            slot += 1;
        }
        Ok(None)
    }

    /// Normalize at most one lapsed source bucket that an active resolved leg
    /// may touch while settling its pending K/F delta. The account has no claim
    /// for a prospective positive delta yet, so account-local source discovery
    /// cannot find this prerequisite. Scanning both domains of each bounded
    /// active leg avoids duplicating the settlement arithmetic and is safely
    /// conservative: an elapsed Fresh bucket must be normalized regardless of
    /// which side's pending delta is nonzero.
    fn expire_one_lapsed_source_backing_for_resolved_active_leg_not_atomic(
        &mut self,
        account: &PortfolioV16View<'_>,
    ) -> V16Result<Option<usize>> {
        let current_slot = self.header.current_slot.get();
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active {
                let asset_index = leg.asset_index as usize;
                for side in [SideV16::Long, SideV16::Short] {
                    let domain = self.insurance_domain_index(asset_index, side)?;
                    let bucket = self.backing_bucket_for_domain(domain)?;
                    if bucket.status == BackingBucketStatusV16::Fresh
                        && bucket.expiry_slot <= current_slot
                    {
                        self.expire_source_backing_bucket_not_atomic(domain, current_slot)?;
                        return Ok(Some(domain));
                    }
                }
            }
            slot += 1;
        }
        Ok(None)
    }

    fn claim_resolved_payout_topup_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        let mut receipt = account.header.resolved_payout_receipt.try_to_runtime()?;
        let claimable = self.resolved_receipt_claimable_now(receipt)?;
        if claimable == 0 {
            // Fully paid at the current rate; if that rate is terminal the receipt is
            // fully diluted -- clear it so the portfolio can dematerialize.
            self.clear_fully_diluted_resolved_receipt_if_terminal(account)?;
            return Ok(0);
        }
        let payout = claimable.min(self.header.vault.get());
        receipt = apply_resolved_payout_receipt_payment(receipt, payout)?;
        let vault_before = self.header.vault.get();
        self.header.vault = V16PodU128::new(
            self.header
                .vault
                .get()
                .checked_sub(payout)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        account.header.resolved_payout_receipt =
            ResolvedPayoutReceiptV16Account::from_runtime(&receipt);
        TokenValueFlowProofV16::capital_and_resolved_payout_to_external_out(
            0,
            payout,
            payout,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        Ok(payout)
    }

    #[cfg(kani)]
    pub fn kani_claim_resolved_payout_topup_core_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        self.claim_resolved_payout_topup_core_not_atomic(account)
    }

    pub fn claim_resolved_payout_topup_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<u128> {
        self.preflight_claim_resolved_payout_topup(&account.as_view())?;
        let payout = self.claim_resolved_payout_topup_core_not_atomic(account)?;
        self.validate_shape()?;
        account.validate_with_market(&self.as_view())?;
        Ok(payout)
    }

    // upstream 2cbca3eb (av#89 for av#88): internal only. The only legitimate
    // decrement is derived from actual source-backed claim realization; a public
    // caller could inflate the resolved payout rate and strand later claimants.
    fn refine_resolved_unreceipted_bound_not_atomic(
        &mut self,
        decrease_num: u128,
    ) -> V16Result<()> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Resolved
            || !decode_bool(self.header.payout_snapshot_captured)?
        {
            return Err(V16Error::LockActive);
        }
        let mut ledger = self.header.resolved_payout_ledger.try_to_runtime()?;
        let old_num = ledger.current_payout_rate_num;
        let old_den = ledger.current_payout_rate_den;
        ledger.terminal_claim_bound_unreceipted_num = ledger
            .terminal_claim_bound_unreceipted_num
            .checked_sub(decrease_num)
            .ok_or(V16Error::CounterUnderflow)?;
        self.header.resolved_payout_ledger = ResolvedPayoutLedgerV16Account::from_runtime(&ledger);
        self.recompute_resolved_payout_rate()?;
        let next = self.header.resolved_payout_ledger.try_to_runtime()?;
        if !fraction_ge(
            next.current_payout_rate_num,
            next.current_payout_rate_den,
            old_num,
            old_den,
        )? {
            return Err(V16Error::InvalidConfig);
        }
        self.as_view().validate_header_aggregate_totals()?;
        self.validate_shape_audit_scan()
    }

    pub fn close_resolved_account_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        fee_rate_per_slot: u128,
    ) -> V16Result<ResolvedCloseOutcomeV16> {
        if decode_market_mode(self.header.mode)? != MarketModeV16::Resolved {
            return Err(V16Error::LockActive);
        }
        if let Some(preparation) =
            self.prepare_one_source_domain_for_resolved_close_not_atomic(account)?
        {
            if preparation == ResolvedSourcePreparationV16::BackingNormalized
                || Self::account_has_source_liens(&account.as_view())
            {
                return Ok(ResolvedCloseOutcomeV16::ProgressOnly);
            }
        }
        if self
            .expire_one_lapsed_source_backing_for_resolved_active_leg_not_atomic(
                &account.as_view(),
            )?
            .is_some()
        {
            self.validate_shape()?;
            account.validate_with_market(&self.as_view())?;
            return Ok(ResolvedCloseOutcomeV16::ProgressOnly);
        }
        if let PermissionlessProgressOutcomeV16::AccountBChunk(_) = self
            .settle_account_side_effects_not_atomic(
                account,
                self.header.config.public_b_chunk_atoms.get(),
            )?
        {
            self.validate_shape()?;
            return Ok(ResolvedCloseOutcomeV16::ProgressOnly);
        }
        self.sync_account_fee_to_slot_not_atomic(
            account,
            self.header.resolved_slot.get(),
            fee_rate_per_slot,
        )?;
        self.settle_negative_pnl_from_principal_not_atomic(account)?;
        if account.header.pnl.get() < 0 {
            self.settle_resolved_bankruptcy_negative_pnl(account)?;
        }
        self.detach_solvent_active_legs_for_resolved_close(account)?;
        if !active_bitmap_is_empty(account.header.active_bitmap.map(V16PodU64::get))
            || account.header.pnl.get() < 0
            || decode_bool(account.header.b_stale_state)?
            || decode_bool(account.header.stale_state)?
        {
            return Ok(ResolvedCloseOutcomeV16::ProgressOnly);
        }
        if account.header.pnl.get() > 0 && !self.resolved_positive_payout_ready()? {
            return Ok(ResolvedCloseOutcomeV16::ProgressOnly);
        }
        if self.realize_one_source_domain_for_resolved_close_not_atomic(account)?
            && Self::account_has_source_claims(&account.as_view())?
        {
            self.validate_shape()?;
            account.validate_with_market(&self.as_view())?;
            return Ok(ResolvedCloseOutcomeV16::ProgressOnly);
        }
        let mut payout_receipt = None;
        let pnl_payout = if account.header.pnl.get() > 0
            || decode_bool(account.header.resolved_payout_receipt.present)?
        {
            self.create_resolved_payout_receipt_if_needed(account)?;
            let receipt = account.header.resolved_payout_receipt.try_to_runtime()?;
            let claimable = self.resolved_receipt_claimable_now(receipt)?;
            payout_receipt = Some(receipt);
            claimable
        } else {
            0
        };
        let account_capital = account.header.capital.get();
        let payout = account_capital
            .checked_add(pnl_payout)
            .ok_or(V16Error::ArithmeticOverflow)?
            .min(self.header.vault.get());
        let capital_paid = account_capital.min(payout);
        let resolved_paid = payout
            .checked_sub(capital_paid)
            .ok_or(V16Error::CounterUnderflow)?;
        if let Some(mut receipt) = payout_receipt {
            receipt = apply_resolved_payout_receipt_payment(receipt, resolved_paid)?;
            account.header.resolved_payout_receipt =
                ResolvedPayoutReceiptV16Account::from_runtime(&receipt);
        }
        // If the receipt is now fully paid at the terminal payout rate, dematerialize it
        // (insolvency bad-debt shortfall is not an open obligation) so this close fully
        // settles instead of leaving the portfolio stuck present-but-unfinalized.
        self.clear_fully_diluted_resolved_receipt_if_terminal(account)?;
        let vault_before = self.header.vault.get();
        self.header.vault = V16PodU128::new(
            self.header
                .vault
                .get()
                .checked_sub(payout)
                .ok_or(V16Error::CounterUnderflow)?,
        );
        self.header.c_tot = V16PodU128::new(
            self.header
                .c_tot
                .get()
                .saturating_sub(account_capital.min(self.header.c_tot.get())),
        );
        self.set_account_pnl(account, 0)?;
        account.header.capital = V16PodU128::new(0);
        account.header.reserved_pnl = V16PodU128::new(0);
        account.header.fee_credits = V16PodI128::new(0);
        account.header.health_cert.valid = 0;
        TokenValueFlowProofV16::capital_and_resolved_payout_to_external_out(
            capital_paid,
            resolved_paid,
            payout,
            vault_before,
            self.header.vault.get(),
        )?
        .validate()?;
        self.validate_shape()?;
        account.validate_with_market(&self.as_view())?;
        Ok(ResolvedCloseOutcomeV16::Closed { payout })
    }

    fn detach_solvent_active_legs_for_resolved_close(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
    ) -> V16Result<()> {
        if account.header.pnl.get() < 0
            || decode_bool(account.header.b_stale_state)?
            || decode_bool(account.header.stale_state)?
            || account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual()
        {
            return Ok(());
        }

        let configured_max = self.header.config.max_market_slots.get() as usize;
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active {
                if leg.b_stale || leg.stale {
                    return Ok(());
                }
                let asset_index = leg.asset_index as usize;
                if asset_index >= configured_max {
                    return Err(V16Error::InvalidLeg);
                }
                if self.has_pending_domain_loss_barrier(asset_index, leg.side)? {
                    return Ok(());
                }
                let asset = self.asset_state(asset_index)?;
                if Self::leg_has_exhausted_effective_oi(asset, leg) {
                    self.begin_full_drain_reset_inner(asset_index, leg.side)?;
                }
                let asset = self.asset_state(asset_index)?;
                let (k_target, f_target) = Self::kf_target_for_leg_from_asset(asset, leg)?;
                if !Self::leg_kf_epoch_is_current(asset, leg)
                    || k_target != leg.k_snap
                    || f_target != leg.f_snap
                {
                    return Ok(());
                }
                if self.b_target_for_leg(asset_index, leg)? != leg.b_snap {
                    return Ok(());
                }
            }
            slot += 1;
        }

        // Keep the terminal continuation bounded: a multi-leg account advances
        // one canonical slot per call and the caller observes ProgressOnly until
        // the bitmap is empty. The close is capped by whichever effective
        // quantity is smaller, so a post-ADL leg cannot subtract more open
        // interest than its side still carries.
        let mut slot = 0usize;
        while slot < V16_MAX_PORTFOLIO_ASSETS_N {
            let leg = account.header.legs[slot].try_to_runtime()?;
            if leg.active {
                let asset_index = leg.asset_index as usize;
                let asset = self.asset_state(asset_index)?;
                let side_effective_oi_q = match leg.side {
                    SideV16::Long => asset.oi_eff_long_q,
                    SideV16::Short => asset.oi_eff_short_q,
                };
                let account_effective_q = V16Core::effective_abs_quantity_for_leg(asset, leg)?;
                let close_q = side_effective_oi_q.min(account_effective_q);
                if close_q == 0 {
                    // Zero-effective legs are either prior-reset residue or a
                    // released pending-loss obligation. They own no live OI,
                    // but still have to detach so resolved close can finish.
                    self.clear_leg_at_slot_inner(account, asset_index, slot, false, Some(0))?;
                    self.begin_zero_oi_residue_resets(asset_index)?;
                    return Ok(());
                }
                let close_q = i128::try_from(close_q).map_err(|_| V16Error::ArithmeticOverflow)?;
                let delta_q = match leg.side {
                    SideV16::Long => close_q.checked_neg().ok_or(V16Error::ArithmeticOverflow)?,
                    SideV16::Short => close_q,
                };
                self.apply_position_delta(account, asset_index, delta_q)?;
                self.begin_zero_oi_residue_resets(asset_index)?;
                return Ok(());
            }
            slot += 1;
        }
        Ok(())
    }

    pub fn deposit_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        amount: u128,
    ) -> V16Result<()> {
        account.validate_with_market(&self.as_view())?;
        // ── GH#448 / spec.md §1204: deposit is LIVE-ONLY ────────────────────────
        //
        // "`deposit(i, amount, now_slot)` is live-only, no-accrual, and may
        // materialize missing `i` only if `amount > 0`."
        //
        // This function had NO mode check — only `validate_with_market`, which
        // accepts an account with an active close ledger and negative pnl. #448
        // showed what that permits: during a multi-chunk RESOLVED-mode bankruptcy
        // close, a mid-close deposit lets principal settlement drive `pnl` back to
        // >= 0 WITHOUT advancing the close ledger. The ledger stays active and
        // non-finalized with `residual_remaining > 0`, the domain-loss barrier is
        // held forever, and `cure_and_cancel_close` refuses to help because a chunk
        // was already booked. That bricks the (asset, side) domain permanently.
        //
        // PRODUCTION WAS NEVER EXPOSED, and it is worth being exact about why
        // rather than implying a live fund bug: the wrapper's `handle_deposit`
        // already rejects any market whose mode is not Live, and
        // `close_resolved_account_not_atomic` requires Resolved. A market is one or
        // the other, so the two windows cannot overlap through the deployed
        // program. #448's PoC reaches it by calling this function directly.
        //
        // The gate belongs here anyway. Relying on the wrapper makes a spec
        // invariant depend on one caller remembering it, and the engine is the
        // layer the spec constrains — a second wrapper path calling this without a
        // mode check would silently reopen the whole thing.
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        if amount == 0 {
            return Ok(());
        }
        let vault_before = self.header.vault.get();
        let capital = account
            .header
            .capital
            .get()
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let c_tot = self
            .header
            .c_tot
            .get()
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let vault = self
            .header
            .vault
            .get()
            .checked_add(amount)
            .ok_or(V16Error::ArithmeticOverflow)?;
        TokenValueFlowProofV16::external_in_to_account_capital(amount, vault_before, vault)?
            .validate()?;
        account.header.capital = V16PodU128::new(capital);
        account.header.health_cert.valid = 0;
        self.header.c_tot = V16PodU128::new(c_tot);
        self.header.vault = V16PodU128::new(vault);
        account.validate_with_market(&self.as_view())?;
        self.validate_shape()
    }

    pub fn mark_asset_drain_only_not_atomic(&mut self, asset_index: usize) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live {
            return Err(V16Error::LockActive);
        }
        let mut asset = self.asset_state(asset_index)?;
        match asset.lifecycle {
            AssetLifecycleV16::Active => {
                let (next_asset_set_epoch, next_risk_epoch) =
                    self.checked_asset_set_epoch_bump()?;
                asset.lifecycle = AssetLifecycleV16::DrainOnly;
                self.set_asset_state(asset_index, asset)?;
                self.commit_asset_set_epoch_bump(next_asset_set_epoch, next_risk_epoch);
                self.validate_shape()
            }
            AssetLifecycleV16::DrainOnly => Ok(()),
            _ => Err(V16Error::LockActive),
        }
    }

    pub fn retire_empty_asset_not_atomic(
        &mut self,
        asset_index: usize,
        now_slot: u64,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        if now_slot < self.header.current_slot.get() {
            return Err(V16Error::Stale);
        }
        let mut asset = self.asset_state(asset_index)?;
        match asset.lifecycle {
            AssetLifecycleV16::Active
            | AssetLifecycleV16::DrainOnly
            | AssetLifecycleV16::Recovery => {
                self.expire_lapsed_source_backing_for_asset_not_atomic(asset_index, now_slot)?;
                self.normalize_terminal_empty_asset_history_not_atomic(asset_index)?;
                let (next_asset_set_epoch, next_risk_epoch) =
                    self.checked_asset_set_epoch_bump()?;
                asset = self.asset_state(asset_index)?;
                asset.lifecycle = AssetLifecycleV16::Retired;
                asset.retired_slot = now_slot;
                self.set_asset_state(asset_index, asset)?;
                self.header.current_slot = V16PodU64::new(now_slot);
                self.commit_asset_set_epoch_bump(next_asset_set_epoch, next_risk_epoch);
                self.validate_shape()
            }
            AssetLifecycleV16::Retired => {
                self.expire_lapsed_source_backing_for_asset_not_atomic(asset_index, now_slot)?;
                self.normalize_terminal_empty_asset_history_not_atomic(asset_index)?;
                self.validate_shape()
            }
            _ => Err(V16Error::LockActive),
        }
    }

    fn clear_terminal_social_loss_audit(asset: &mut AssetStateV16) {
        asset.social_loss_remainder_long_num = 0;
        asset.social_loss_remainder_short_num = 0;
        asset.social_loss_dust_long_num = 0;
        asset.social_loss_dust_short_num = 0;
        asset.explicit_unallocated_loss_long = 0;
        asset.explicit_unallocated_loss_short = 0;
    }

    fn clear_terminal_price_funding_history(asset: &mut AssetStateV16) {
        asset.k_long = 0;
        asset.k_short = 0;
        asset.f_long_num = 0;
        asset.f_short_num = 0;
        asset.kf_epoch_long = 0;
        asset.kf_epoch_short = 0;
        asset.k_epoch_start_long = 0;
        asset.k_epoch_start_short = 0;
        asset.f_epoch_start_long_num = 0;
        asset.f_epoch_start_short_num = 0;
    }

    fn clear_terminal_source_spent_audit(&mut self, asset_index: usize) -> V16Result<()> {
        for side in [SideV16::Long, SideV16::Short] {
            let domain = self.insurance_domain_index(asset_index, side)?;
            let source = self.source_credit_for_domain_shape(domain)?;
            if !source.is_terminal_spent_audit_only_shape() {
                return Err(V16Error::LockActive);
            }
            self.set_source_credit_for_domain(domain, SourceCreditStateV16::EMPTY)?;
        }
        Ok(())
    }

    /// Retirement is the terminal consumer for one asset, so it must normalize
    /// both of that asset's source domains before testing whether the slot is
    /// empty. This is constant work and also covers a lapsed bucket that no
    /// portfolio references, which account-local crank discovery cannot
    /// otherwise select. (upstream 379fbfea)
    fn expire_lapsed_source_backing_for_asset_not_atomic(
        &mut self,
        asset_index: usize,
        now_slot: u64,
    ) -> V16Result<()> {
        for side in [SideV16::Long, SideV16::Short] {
            let domain = self.insurance_domain_index(asset_index, side)?;
            let bucket = self.backing_bucket_for_domain(domain)?;
            if bucket.status == BackingBucketStatusV16::Fresh && bucket.expiry_slot <= now_slot {
                self.expire_source_backing_bucket_not_atomic(domain, now_slot)?;
            }
            let bucket = self.backing_bucket_for_domain(domain)?;
            let normalized = V16Core::kernel_retirement_backing_normalization(bucket);
            if normalized != bucket {
                self.set_backing_bucket_for_domain(domain, normalized)?;
            }
        }
        Ok(())
    }

    /// Restarts an empty Recovery/Retired asset with a fresh market_id.
    ///
    /// Remaining domain insurance budgets are preserved exactly. Audit-only spent budgets,
    /// source/social-loss history, and K/F indices are normalized inside this transition after
    /// proving all positions, claims, backing, receivables, liens, reservations, and barriers are
    /// empty, so stale legs from the old market_id fail closed after restart.
    pub fn restart_empty_asset_preserving_insurance_budget_not_atomic(
        &mut self,
        asset_index: usize,
        authenticated_price: u64,
        now_slot: u64,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        if decode_market_mode(self.header.mode)? != MarketModeV16::Live
            || authenticated_price == 0
            || authenticated_price > MAX_ORACLE_PRICE
            || now_slot < self.header.current_slot.get()
        {
            return Err(V16Error::InvalidConfig);
        }
        let old_asset = self.asset_state(asset_index)?;
        if !matches!(
            old_asset.lifecycle,
            AssetLifecycleV16::Recovery | AssetLifecycleV16::Retired
        ) || old_asset.market_id == 0
        {
            return Err(V16Error::LockActive);
        }
        self.normalize_terminal_empty_asset_history_not_atomic(asset_index)?;

        let market_id = self.header.next_market_id.get();
        if market_id == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let (next_market_id, next_activation_count, next_asset_set_epoch, next_risk_epoch) =
            Self::asset_restart_next_counters(
                market_id,
                self.header.asset_activation_count.get(),
                self.header.asset_set_epoch.get(),
                self.header.risk_epoch.get(),
            )?;

        let slot = self.markets[asset_index].engine_slot_mut();
        *slot = Self::restarted_asset_slot_preserving_insurance_budget(
            slot,
            market_id,
            authenticated_price,
            now_slot,
        );

        self.header.next_market_id = V16PodU64::new(next_market_id);
        self.header.current_slot = V16PodU64::new(now_slot);
        self.header.asset_activation_count = V16PodU64::new(next_activation_count);
        self.header.last_asset_activation_slot = V16PodU64::new(now_slot);
        self.header.asset_set_epoch = V16PodU64::new(next_asset_set_epoch);
        self.header.risk_epoch = V16PodU64::new(next_risk_epoch);
        self.validate_shape()
    }

    /// Canonicalizes audit-only history on an otherwise empty terminal asset.
    ///
    /// This is value-neutral: spent insurance may clear only when its remaining budget is zero
    /// (`budget == spent`), and source, social-loss, price, and funding history may clear only
    /// after every position, claim, backing amount, receivable, lien, reservation, and barrier is
    /// gone. Any live obligation rejects before mutation.
    fn normalize_terminal_empty_asset_history_not_atomic(
        &mut self,
        asset_index: usize,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        self.require_empty_asset_lifecycle_state_with_policy(asset_index, true, true, true, true)?;
        let slot = self.markets[asset_index].engine_slot();
        let (budget_long, spent_long) = Self::clear_terminal_spent_domain_budget_pair(
            slot.insurance_domain_budget_long,
            slot.insurance_domain_spent_long,
        )?;
        let (budget_short, spent_short) = Self::clear_terminal_spent_domain_budget_pair(
            slot.insurance_domain_budget_short,
            slot.insurance_domain_spent_short,
        )?;
        let mut asset = self.asset_state(asset_index)?;
        Self::clear_terminal_social_loss_audit(&mut asset);
        Self::clear_terminal_price_funding_history(&mut asset);
        self.clear_terminal_source_spent_audit(asset_index)?;
        self.set_asset_state(asset_index, asset)?;
        let slot = self.markets[asset_index].engine_slot_mut();
        slot.insurance_domain_budget_long = budget_long;
        slot.insurance_domain_spent_long = spent_long;
        slot.insurance_domain_budget_short = budget_short;
        slot.insurance_domain_spent_short = spent_short;
        self.validate_shape()
    }

    /// Rewrites an empty retired slot into the canonical retired representation.
    ///
    /// This is value-neutral and only succeeds after all domain budgets, spent
    /// amounts, source-credit, backing, reservations, and barriers are zero.
    pub fn canonicalize_retired_empty_asset_slot_not_atomic(
        &mut self,
        asset_index: usize,
    ) -> V16Result<()> {
        self.validate_configured_asset_index(asset_index)?;
        let old_asset = self.asset_state(asset_index)?;
        if old_asset.lifecycle != AssetLifecycleV16::Retired
            || old_asset.market_id == 0
            || old_asset.retired_slot == 0
        {
            return Err(V16Error::LockActive);
        }
        let slot = self.markets[asset_index].engine_slot();
        if slot.insurance_domain_budget_long.get() != 0
            || slot.insurance_domain_budget_short.get() != 0
            || slot.insurance_domain_spent_long.get() != 0
            || slot.insurance_domain_spent_short.get() != 0
        {
            return Err(V16Error::LockActive);
        }
        self.require_empty_asset_lifecycle_state(asset_index)?;

        *self.markets[asset_index].engine_slot_mut() =
            Self::canonical_retired_asset_slot(old_asset);
        self.validate_shape()
    }

    #[cfg(any(test, kani, feature = "fuzz"))]
    pub fn activate_empty_market_not_atomic(
        &mut self,
        asset_index: u32,
        authenticated_price: u64,
        now_slot: u64,
    ) -> V16Result<()> {
        let slot = self
            .markets
            .get_mut(asset_index as usize)
            .ok_or(V16Error::InvalidLeg)?;
        self.header.activate_empty_market_slot_not_atomic(
            asset_index,
            slot,
            authenticated_price,
            now_slot,
        )
    }

    fn leg_is_dead_for_forfeit(&self, asset_index: usize, side: SideV16) -> V16Result<bool> {
        let side_mode = self.side_mode_for(asset_index, side)?;
        let asset_lifecycle = self.asset_state(asset_index)?.lifecycle;
        Ok(
            decode_market_mode(self.header.mode)? == MarketModeV16::Recovery
                || asset_lifecycle == AssetLifecycleV16::Recovery
                || matches!(
                    side_mode,
                    SideModeV16::DrainOnly | SideModeV16::ResetPending
                ),
        )
    }

    fn settle_forfeited_leg_kf_effects(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
    ) -> V16Result<(u128, u128, u128, u128)> {
        let Some(leg_slot) = Self::active_leg_slot_for_asset(&account.as_view(), asset_index)?
        else {
            return Ok((0, 0, 0, 0));
        };
        let mut leg = account.header.legs[leg_slot].try_to_runtime()?;
        let (k_now, f_now) = self.kf_target_for_leg(asset_index, leg)?;
        let den = leg
            .a_basis
            .checked_mul(POS_SCALE)
            .ok_or(V16Error::ArithmeticOverflow)?;
        let k_delta = scaled_adl_delta_fast(
            leg.basis_pos_q.unsigned_abs(),
            leg.a_basis,
            leg.k_snap,
            k_now,
        )
        .unwrap_or_else(|| {
            wide_signed_mul_div_floor_from_k_pair(
                leg.basis_pos_q.unsigned_abs(),
                leg.k_snap,
                k_now,
                den,
            )
        });
        let f_delta = scaled_adl_delta_fast(
            leg.basis_pos_q.unsigned_abs(),
            leg.a_basis,
            leg.f_snap,
            f_now,
        )
        .unwrap_or_else(|| {
            wide_signed_mul_div_floor_from_k_pair(
                leg.basis_pos_q.unsigned_abs(),
                leg.f_snap,
                f_now,
                den,
            )
        });
        let net = k_delta
            .checked_add(f_delta)
            .ok_or(V16Error::ArithmeticOverflow)?;
        validate_non_min_i128(net)?;

        let mut loss_settled = 0u128;
        let mut support_consumed = 0u128;
        let mut junior_face_burned = 0u128;
        let mut positive_pnl_forfeited = 0u128;
        if net < 0 {
            loss_settled = net.unsigned_abs();
            let support = self.apply_haircut_bounded_close_loss_to_pnl(account, loss_settled)?;
            support_consumed = support.support_consumed;
            junior_face_burned = support.junior_face_burned;
        } else {
            positive_pnl_forfeited = net as u128;
        }

        Self::record_account_funding_flow(account, leg.side, f_delta)?;
        let asset = self.asset_state(asset_index)?;
        let (asset, kf_epoch_snap) =
            V16Core::kernel_settle_kf_stale_cohort(asset, leg.side, leg.kf_epoch_snap)?;
        leg.k_snap = k_now;
        leg.f_snap = f_now;
        leg.kf_epoch_snap = kf_epoch_snap;
        account.header.legs[leg_slot] = PortfolioLegV16Account::from_runtime(&leg);
        account.header.health_cert.valid = 0;
        self.set_asset_state(asset_index, asset)?;
        self.header.loss_stale_active = encode_bool(asset_is_loss_stale_at_slot(
            asset,
            self.header.current_slot.get(),
        ));
        Ok((
            loss_settled,
            positive_pnl_forfeited,
            support_consumed,
            junior_face_burned,
        ))
    }

    fn leg_has_exhausted_effective_oi(asset: AssetStateV16, leg: PortfolioLegV16) -> bool {
        let (effective_oi, stored_count, pending_count, mode) = match leg.side {
            SideV16::Long => (
                asset.oi_eff_long_q,
                asset.stored_pos_count_long,
                asset.pending_obligation_count_long,
                asset.mode_long,
            ),
            SideV16::Short => (
                asset.oi_eff_short_q,
                asset.stored_pos_count_short,
                asset.pending_obligation_count_short,
                asset.mode_short,
            ),
        };
        leg.active
            && leg.basis_pos_q != 0
            && effective_oi == 0
            && stored_count != 0
            && pending_count == 0
            && mode != SideModeV16::ResetPending
    }

    #[cfg(kani)]
    pub fn kani_kernel_unilateral_close_capacity(
        account_effective_abs: u128,
        oi_eff_long_q: u128,
        oi_eff_short_q: u128,
    ) -> u128 {
        V16Core::kernel_unilateral_close_capacity(
            account_effective_abs,
            oi_eff_long_q,
            oi_eff_short_q,
        )
    }

    #[cfg(kani)]
    pub fn kani_kernel_reduce_position_delta(
        pre_basis_signed: i128,
        side: SideV16,
        requested: u128,
    ) -> V16Result<(u128, i128)> {
        V16Core::kernel_reduce_position_delta(pre_basis_signed, side, requested)
    }

    #[cfg(kani)]
    pub fn kani_leg_has_exhausted_effective_oi(asset: AssetStateV16, leg: PortfolioLegV16) -> bool {
        Self::leg_has_exhausted_effective_oi(asset, leg)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_kernel_begin_full_drain_reset(
        asset: AssetStateV16,
        side: SideV16,
    ) -> V16Result<AssetStateV16> {
        V16Core::kernel_begin_full_drain_reset(asset, side)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_kernel_normalize_social_loss_carry(
        remainder: u128,
        dust: u128,
        explicit_loss: u128,
    ) -> V16Result<(u128, u128)> {
        V16Core::kernel_normalize_social_loss_carry(remainder, dust, explicit_loss)
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_account_b_settlement_chunk_from_leg(
        &self,
        leg: PortfolioLegV16,
        target: u128,
        endpoint_loss_atom_budget: u128,
    ) -> V16Result<AccountBSettlementChunkV16> {
        self.account_b_settlement_chunk_from_leg(leg, target, endpoint_loss_atom_budget)
    }

    #[cfg(kani)]
    pub fn kani_prepare_counterparty_impaired_lien_retirement_delta(
        bucket: BackingBucketV16,
        source: SourceCreditStateV16,
        amount: u128,
    ) -> V16Result<(BackingBucketV16, SourceCreditStateV16)> {
        V16Core::prepare_counterparty_impaired_lien_retirement_delta(bucket, source, amount)
    }

    #[cfg(kani)]
    pub fn kani_prepare_account_counterparty_lien_impairment(
        source: PortfolioSourceDomainV16Account,
    ) -> V16Result<(PortfolioSourceDomainV16Account, u128)> {
        V16Core::prepare_account_counterparty_lien_impairment(source)
    }

    #[cfg(kani)]
    pub fn kani_source_lien_face_burn_plan(
        counterparty_face_num: u128,
        insurance_face_num: u128,
        counterparty_backing_num: u128,
        insurance_backing_num: u128,
        face_burn_num: u128,
    ) -> V16Result<(u128, u128, u128, u128, u128)> {
        V16Core::source_lien_face_burn_plan(
            counterparty_face_num,
            insurance_face_num,
            counterparty_backing_num,
            insurance_backing_num,
            face_burn_num,
        )
    }

    #[cfg(kani)]
    pub fn kani_source_lien_face_burn_partition(
        counterparty_face_num: u128,
        insurance_face_num: u128,
        face_burn_num: u128,
    ) -> V16Result<(u128, u128)> {
        V16Core::source_lien_face_burn_partition(
            counterparty_face_num,
            insurance_face_num,
            face_burn_num,
        )
    }

    #[cfg(kani)]
    pub fn kani_source_lien_backing_release_for_face_burn(
        face_locked_num: u128,
        backing_reserved_num: u128,
        face_burn_num: u128,
    ) -> V16Result<u128> {
        V16Core::source_lien_backing_release_for_face_burn(
            face_locked_num,
            backing_reserved_num,
            face_burn_num,
        )
    }

    #[cfg(any(kani, feature = "fuzz"))]
    pub fn kani_kernel_clear_leg(
        leg: PortfolioLegV16,
        asset: AssetStateV16,
        clear_effective_oi_q: u128,
    ) -> V16Result<AssetStateV16> {
        V16Core::kernel_clear_leg(leg, asset, clear_effective_oi_q)
    }

    #[cfg(kani)]
    pub fn kani_clear_terminal_spent_domain_budget_pair(
        budget: u128,
        spent: u128,
    ) -> V16Result<(u128, u128)> {
        let (budget, spent) = Self::clear_terminal_spent_domain_budget_pair(
            V16PodU128::new(budget),
            V16PodU128::new(spent),
        )?;
        Ok((budget.get(), spent.get()))
    }

    pub fn forfeit_recovery_leg_not_atomic(
        &mut self,
        account: &mut PortfolioV16ViewMut<'_>,
        asset_index: usize,
        b_loss_atom_budget: u128,
    ) -> V16Result<DeadLegForfeitOutcomeV16> {
        account.validate_with_market(&self.as_view())?;
        if asset_index >= self.header.config.max_market_slots.get() as usize
            || asset_index >= self.markets.len()
            || b_loss_atom_budget == 0
        {
            return Err(V16Error::InvalidLeg);
        }
        let mut leg = Self::active_leg_for_asset(&account.as_view(), asset_index)?;
        if !leg.active {
            return Err(V16Error::InvalidLeg);
        }
        if !self.leg_is_dead_for_forfeit(asset_index, leg.side)? {
            return Err(V16Error::LockActive);
        }
        if Self::leg_has_exhausted_effective_oi(self.asset_state(asset_index)?, leg)
            && !account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual()
            && !self.has_pending_domain_loss_barrier(asset_index, leg.side)?
        {
            // A matched Recovery close can consume the final effective OI while
            // leaving an ADL-reduced account's larger stored basis behind. Move
            // that terminal residue into the reset epoch before forfeit clears it.
            self.begin_full_drain_reset_inner(asset_index, leg.side)?;
            leg = Self::active_leg_for_asset(&account.as_view(), asset_index)?;
        }

        let asset = self.asset_state(asset_index)?;
        let (k_target, f_target) = Self::kf_target_for_leg_from_asset(asset, leg)?;
        let b_target = self.b_target_for_leg(asset_index, leg)?;
        if account.header.pnl.get() == 0
            && Self::leg_kf_epoch_is_current(asset, leg)
            && k_target == leg.k_snap
            && f_target == leg.f_snap
            && b_target <= leg.b_snap
            && !account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual()
        {
            let retain = self.retain_recovery_loss_weight_before_detach(asset_index, leg)?;
            if retain {
                self.retain_leg_as_pending_obligation(account, asset_index)?;
            } else {
                self.clear_leg(account, asset_index)?;
            }
            return Ok(DeadLegForfeitOutcomeV16 {
                detached: !retain,
                positive_pnl_forfeited: 0,
                loss_settled: 0,
                support_consumed: 0,
                junior_face_burned: 0,
                principal_used: 0,
                insurance_used: 0,
                residual_booked: 0,
                explicit_loss: 0,
            });
        }

        let (loss_settled, positive_pnl_forfeited, support_consumed, junior_face_burned) =
            self.settle_forfeited_leg_kf_effects(account, asset_index)?;

        let mut total_loss_settled = loss_settled;
        let refreshed = Self::active_leg_for_asset(&account.as_view(), asset_index)?;
        if self.b_target_for_leg(asset_index, refreshed)? > refreshed.b_snap {
            self.mark_leg_b_stale(account, asset_index)?;
            let chunk = self.settle_account_b_chunk(account, asset_index, b_loss_atom_budget)?;
            total_loss_settled = total_loss_settled
                .checked_add(chunk.loss)
                .ok_or(V16Error::ArithmeticOverflow)?;
            if chunk.remaining_after != 0 {
                self.validate_shape()?;
                account.validate_with_market(&self.as_view())?;
                return Ok(DeadLegForfeitOutcomeV16 {
                    detached: false,
                    positive_pnl_forfeited,
                    loss_settled: total_loss_settled,
                    support_consumed,
                    junior_face_burned,
                    principal_used: 0,
                    insurance_used: 0,
                    residual_booked: 0,
                    explicit_loss: 0,
                });
            }
        }

        let principal_used = self.settle_negative_pnl_from_principal_not_atomic(account)?;
        let bankruptcy_residual_after_principal = if account.header.pnl.get() < 0 {
            account.header.pnl.get().unsigned_abs()
        } else {
            0
        };
        let gross_close_loss = bankruptcy_residual_after_principal
            .checked_add(support_consumed)
            .ok_or(V16Error::ArithmeticOverflow)?;
        if gross_close_loss != 0 {
            self.begin_close_progress_ledger(
                account,
                asset_index,
                opposite_side(leg.side),
                gross_close_loss,
            )?;
            if support_consumed != 0 {
                self.advance_close_progress_ledger(
                    account,
                    support_consumed,
                    junior_face_burned,
                    0,
                    0,
                    0,
                )?;
            }
        }

        let insurance_used =
            self.consume_domain_insurance_for_negative_pnl(asset_index, leg.side, account)?;
        if insurance_used != 0 {
            self.advance_close_progress_ledger(account, 0, 0, insurance_used, 0, 0)?;
        }

        let residual = if account.header.pnl.get() < 0 {
            account.header.pnl.get().unsigned_abs()
        } else {
            0
        };
        let mut residual_booked = 0u128;
        let mut explicit_loss = 0u128;
        let booking_capacity = if residual == 0 {
            0
        } else {
            self.bankruptcy_residual_single_step_capacity(asset_index, leg.side, residual)?
        };
        match V16Core::kernel_forfeit_residual_step(residual, booking_capacity) {
            ForfeitResidualStepV16::NoResidual => {}
            ForfeitResidualStepV16::CommitRecovery => {
                // The opposing side may already have completed terminal wind-down.
                // Returning RecoveryRequired would make SVM rollback the only
                // terminal transition. The close ledger retains the exact debt.
                // (upstream 650e3fdf)
                self.declare_permissionless_recovery(
                    PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress,
                )?;
                self.validate_shape()?;
                account.validate_with_market(&self.as_view())?;
                return Ok(DeadLegForfeitOutcomeV16 {
                    detached: false,
                    positive_pnl_forfeited,
                    loss_settled: total_loss_settled,
                    support_consumed,
                    junior_face_burned,
                    principal_used,
                    insurance_used,
                    residual_booked: 0,
                    explicit_loss: 0,
                });
            }
            ForfeitResidualStepV16::Book => {
                let outcome = self.book_bankruptcy_residual_chunk_for_account_core(
                    account,
                    asset_index,
                    leg.side,
                    residual,
                )?;
                residual_booked = outcome.booked_loss;
                explicit_loss = outcome.explicit_loss;
                let cleared = residual_booked
                    .checked_add(explicit_loss)
                    .ok_or(V16Error::ArithmeticOverflow)?
                    .min(residual);
                let cleared_i128 =
                    i128::try_from(cleared).map_err(|_| V16Error::ArithmeticOverflow)?;
                let new_pnl = account
                    .header
                    .pnl
                    .get()
                    .checked_add(cleared_i128)
                    .ok_or(V16Error::ArithmeticOverflow)?;
                self.set_account_pnl(account, new_pnl)?;
            }
        }

        let mut detached = account.header.pnl.get() >= 0
            && !account
                .header
                .close_progress
                .try_to_runtime()?
                .has_pending_residual();
        if detached {
            let refreshed = Self::active_leg_for_asset(&account.as_view(), asset_index)?;
            if self.retain_recovery_loss_weight_before_detach(asset_index, refreshed)? {
                self.retain_leg_as_pending_obligation(account, asset_index)?;
                detached = false;
            } else {
                self.clear_leg(account, asset_index)?;
            }
        }
        self.validate_shape()?;
        account.validate_with_market(&self.as_view())?;

        Ok(DeadLegForfeitOutcomeV16 {
            detached,
            positive_pnl_forfeited,
            loss_settled: total_loss_settled,
            support_consumed,
            junior_face_burned,
            principal_used,
            insurance_used,
            residual_booked,
            explicit_loss,
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct PortfolioLegV16Account {
    pub active: u8,
    pub asset_index: V16PodU32,
    pub market_id: V16PodU64,
    pub side: u8,
    pub basis_pos_q: V16PodI128,
    pub a_basis: V16PodU128,
    pub k_snap: V16PodI128,
    pub f_snap: V16PodI128,
    pub kf_epoch_snap: V16PodU64,
    pub epoch_snap: V16PodU64,
    pub loss_weight: V16PodU128,
    pub b_snap: V16PodU128,
    pub b_rem: V16PodU128,
    pub b_epoch_snap: V16PodU64,
    pub b_stale: u8,
    pub stale: u8,
}

impl PortfolioLegV16Account {
    pub fn from_runtime(value: &PortfolioLegV16) -> Self {
        Self {
            active: encode_bool(value.active),
            asset_index: V16PodU32::new(value.asset_index),
            market_id: V16PodU64::new(value.market_id),
            side: encode_side(value.side),
            basis_pos_q: V16PodI128::new(value.basis_pos_q),
            a_basis: V16PodU128::new(value.a_basis),
            k_snap: V16PodI128::new(value.k_snap),
            f_snap: V16PodI128::new(value.f_snap),
            kf_epoch_snap: V16PodU64::new(value.kf_epoch_snap),
            epoch_snap: V16PodU64::new(value.epoch_snap),
            loss_weight: V16PodU128::new(value.loss_weight),
            b_snap: V16PodU128::new(value.b_snap),
            b_rem: V16PodU128::new(value.b_rem),
            b_epoch_snap: V16PodU64::new(value.b_epoch_snap),
            b_stale: encode_bool(value.b_stale),
            stale: encode_bool(value.stale),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<PortfolioLegV16> {
        let out = PortfolioLegV16 {
            active: decode_bool(self.active)?,
            asset_index: self.asset_index.get(),
            market_id: self.market_id.get(),
            side: decode_side(self.side)?,
            basis_pos_q: self.basis_pos_q.get(),
            a_basis: self.a_basis.get(),
            k_snap: self.k_snap.get(),
            f_snap: self.f_snap.get(),
            kf_epoch_snap: self.kf_epoch_snap.get(),
            epoch_snap: self.epoch_snap.get(),
            loss_weight: self.loss_weight.get(),
            b_snap: self.b_snap.get(),
            b_rem: self.b_rem.get(),
            b_epoch_snap: self.b_epoch_snap.get(),
            b_stale: decode_bool(self.b_stale)?,
            stale: decode_bool(self.stale)?,
        };
        if out.active {
            validate_active_leg(out)?;
        } else if !out.is_empty() {
            return Err(V16Error::HiddenLeg);
        }
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct HealthCertV16Account {
    pub certified_equity: V16PodI128,
    pub certified_initial_req: V16PodU128,
    pub certified_maintenance_req: V16PodU128,
    pub certified_liq_deficit: V16PodU128,
    pub certified_worst_case_loss: V16PodU128,
    pub cert_oracle_epoch: V16PodU64,
    pub cert_funding_epoch: V16PodU64,
    pub cert_risk_epoch: V16PodU64,
    pub cert_asset_set_epoch: V16PodU64,
    pub active_bitmap_at_cert: [V16PodU64; V16_ACTIVE_BITMAP_WORDS],
    pub valid: u8,
}

impl HealthCertV16Account {
    pub fn from_runtime(value: &HealthCertV16) -> Self {
        Self {
            certified_equity: V16PodI128::new(value.certified_equity),
            certified_initial_req: V16PodU128::new(value.certified_initial_req),
            certified_maintenance_req: V16PodU128::new(value.certified_maintenance_req),
            certified_liq_deficit: V16PodU128::new(value.certified_liq_deficit),
            certified_worst_case_loss: V16PodU128::new(value.certified_worst_case_loss),
            cert_oracle_epoch: V16PodU64::new(value.cert_oracle_epoch),
            cert_funding_epoch: V16PodU64::new(value.cert_funding_epoch),
            cert_risk_epoch: V16PodU64::new(value.cert_risk_epoch),
            cert_asset_set_epoch: V16PodU64::new(value.cert_asset_set_epoch),
            active_bitmap_at_cert: value.active_bitmap_at_cert.map(V16PodU64::new),
            valid: encode_bool(value.valid),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<HealthCertV16> {
        let out = HealthCertV16 {
            certified_equity: self.certified_equity.get(),
            certified_initial_req: self.certified_initial_req.get(),
            certified_maintenance_req: self.certified_maintenance_req.get(),
            certified_liq_deficit: self.certified_liq_deficit.get(),
            certified_worst_case_loss: self.certified_worst_case_loss.get(),
            cert_oracle_epoch: self.cert_oracle_epoch.get(),
            cert_funding_epoch: self.cert_funding_epoch.get(),
            cert_risk_epoch: self.cert_risk_epoch.get(),
            cert_asset_set_epoch: self.cert_asset_set_epoch.get(),
            active_bitmap_at_cert: self.active_bitmap_at_cert.map(|v| v.get()),
            valid: decode_bool(self.valid)?,
        };
        validate_non_min_i128(out.certified_equity)?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct CloseProgressLedgerV16Account {
    pub active: u8,
    pub finalized: u8,
    pub canceled: u8,
    pub close_id: V16PodU64,
    pub asset_index: V16PodU32,
    pub market_id: V16PodU64,
    pub domain_side: u8,
    pub gross_loss_at_close_start: V16PodU128,
    pub drift_reference_slot: V16PodU64,
    pub max_close_slot: V16PodU64,
    pub support_consumed: V16PodU128,
    pub junior_face_burned: V16PodU128,
    pub insurance_spent: V16PodU128,
    pub b_loss_booked: V16PodU128,
    pub explicit_loss_assigned: V16PodU128,
    pub quantity_adl_applied_q: V16PodU128,
    pub drift_consumed: V16PodU128,
    pub residual_remaining: V16PodU128,
}

impl CloseProgressLedgerV16Account {
    pub fn from_runtime(value: &CloseProgressLedgerV16) -> Self {
        Self {
            active: encode_bool(value.active),
            finalized: encode_bool(value.finalized),
            canceled: encode_bool(value.canceled),
            close_id: V16PodU64::new(value.close_id),
            asset_index: V16PodU32::new(value.asset_index),
            market_id: V16PodU64::new(value.market_id),
            domain_side: encode_side(value.domain_side),
            gross_loss_at_close_start: V16PodU128::new(value.gross_loss_at_close_start),
            drift_reference_slot: V16PodU64::new(value.drift_reference_slot),
            max_close_slot: V16PodU64::new(value.max_close_slot),
            support_consumed: V16PodU128::new(value.support_consumed),
            junior_face_burned: V16PodU128::new(value.junior_face_burned),
            insurance_spent: V16PodU128::new(value.insurance_spent),
            b_loss_booked: V16PodU128::new(value.b_loss_booked),
            explicit_loss_assigned: V16PodU128::new(value.explicit_loss_assigned),
            quantity_adl_applied_q: V16PodU128::new(value.quantity_adl_applied_q),
            drift_consumed: V16PodU128::new(value.drift_consumed),
            residual_remaining: V16PodU128::new(value.residual_remaining),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<CloseProgressLedgerV16> {
        Ok(CloseProgressLedgerV16 {
            active: decode_bool(self.active)?,
            finalized: decode_bool(self.finalized)?,
            canceled: decode_bool(self.canceled)?,
            close_id: self.close_id.get(),
            asset_index: self.asset_index.get(),
            market_id: self.market_id.get(),
            domain_side: decode_side(self.domain_side)?,
            gross_loss_at_close_start: self.gross_loss_at_close_start.get(),
            drift_reference_slot: self.drift_reference_slot.get(),
            max_close_slot: self.max_close_slot.get(),
            support_consumed: self.support_consumed.get(),
            junior_face_burned: self.junior_face_burned.get(),
            insurance_spent: self.insurance_spent.get(),
            b_loss_booked: self.b_loss_booked.get(),
            explicit_loss_assigned: self.explicit_loss_assigned.get(),
            quantity_adl_applied_q: self.quantity_adl_applied_q.get(),
            drift_consumed: self.drift_consumed.get(),
            residual_remaining: self.residual_remaining.get(),
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct ResolvedPayoutLedgerV16Account {
    pub snapshot_residual: V16PodU128,
    pub terminal_claim_exact_receipts_num: V16PodU128,
    pub terminal_claim_bound_unreceipted_num: V16PodU128,
    pub current_payout_rate_num: V16PodU128,
    pub current_payout_rate_den: V16PodU128,
    pub snapshot_slot: V16PodU64,
    pub payout_halted: u8,
    pub finalized: u8,
}

impl ResolvedPayoutLedgerV16Account {
    pub fn from_runtime(value: &ResolvedPayoutLedgerV16) -> Self {
        Self {
            snapshot_residual: V16PodU128::new(value.snapshot_residual),
            terminal_claim_exact_receipts_num: V16PodU128::new(
                value.terminal_claim_exact_receipts_num,
            ),
            terminal_claim_bound_unreceipted_num: V16PodU128::new(
                value.terminal_claim_bound_unreceipted_num,
            ),
            current_payout_rate_num: V16PodU128::new(value.current_payout_rate_num),
            current_payout_rate_den: V16PodU128::new(value.current_payout_rate_den),
            snapshot_slot: V16PodU64::new(value.snapshot_slot),
            payout_halted: encode_bool(value.payout_halted),
            finalized: encode_bool(value.finalized),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<ResolvedPayoutLedgerV16> {
        Ok(ResolvedPayoutLedgerV16 {
            snapshot_residual: self.snapshot_residual.get(),
            terminal_claim_exact_receipts_num: self.terminal_claim_exact_receipts_num.get(),
            terminal_claim_bound_unreceipted_num: self.terminal_claim_bound_unreceipted_num.get(),
            current_payout_rate_num: self.current_payout_rate_num.get(),
            current_payout_rate_den: self.current_payout_rate_den.get(),
            snapshot_slot: self.snapshot_slot.get(),
            payout_halted: decode_bool(self.payout_halted)?,
            finalized: decode_bool(self.finalized)?,
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct ResolvedPayoutReceiptV16Account {
    pub prior_bound_contribution_num: V16PodU128,
    pub live_released_face_at_receipt: V16PodU128,
    pub terminal_positive_claim_face: V16PodU128,
    pub paid_effective: V16PodU128,
    pub present: u8,
    pub finalized: u8,
}

impl ResolvedPayoutReceiptV16Account {
    pub fn from_runtime(value: &ResolvedPayoutReceiptV16) -> Self {
        Self {
            prior_bound_contribution_num: V16PodU128::new(value.prior_bound_contribution_num),
            live_released_face_at_receipt: V16PodU128::new(value.live_released_face_at_receipt),
            terminal_positive_claim_face: V16PodU128::new(value.terminal_positive_claim_face),
            paid_effective: V16PodU128::new(value.paid_effective),
            present: encode_bool(value.present),
            finalized: encode_bool(value.finalized),
        }
    }

    pub fn try_to_runtime(&self) -> V16Result<ResolvedPayoutReceiptV16> {
        Ok(ResolvedPayoutReceiptV16 {
            present: decode_bool(self.present)?,
            prior_bound_contribution_num: self.prior_bound_contribution_num.get(),
            live_released_face_at_receipt: self.live_released_face_at_receipt.get(),
            terminal_positive_claim_face: self.terminal_positive_claim_face.get(),
            paid_effective: self.paid_effective.get(),
            finalized: decode_bool(self.finalized)?,
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct PortfolioSourceDomainV16Account {
    pub domain: V16PodU32,
    pub source_claim_market_id: V16PodU64,
    pub source_claim_bound_num: V16PodU128,
    pub source_claim_liened_num: V16PodU128,
    pub source_claim_counterparty_liened_num: V16PodU128,
    pub source_claim_insurance_liened_num: V16PodU128,
    pub source_lien_effective_reserved: V16PodU128,
    pub source_lien_counterparty_backing_num: V16PodU128,
    pub source_lien_insurance_backing_num: V16PodU128,
    pub source_lien_fee_last_slot: V16PodU64,
    pub source_claim_impaired_num: V16PodU128,
    pub source_lien_impaired_effective_reserved: V16PodU128,
    // Genesis residual-farming counter (anti-wash). Collateral-atom non-rebatable fee revenue
    // generated WHILE this domain's backing lien was live and at risk. On residual crystallization
    // the pro-rata share moves from the live counter to the impaired counter; the genesis farm reads
    // the impaired counter to cap residual reward weight. Event-local, never a cumulative total.
    pub source_lien_capital_at_risk_fee_revenue: V16PodU128,
    pub source_lien_impaired_capital_at_risk_fee_revenue: V16PodU128,
}

impl PortfolioSourceDomainV16Account {
    #[inline]
    pub fn is_occupied(self) -> bool {
        self.source_claim_bound_num.get() != 0
            || self.source_claim_liened_num.get() != 0
            || self.source_claim_counterparty_liened_num.get() != 0
            || self.source_claim_insurance_liened_num.get() != 0
            || self.source_lien_effective_reserved.get() != 0
            || self.source_lien_counterparty_backing_num.get() != 0
            || self.source_lien_insurance_backing_num.get() != 0
            || self.source_lien_fee_last_slot.get() != 0
            || self.source_claim_impaired_num.get() != 0
            || self.source_lien_impaired_effective_reserved.get() != 0
            || self.source_lien_capital_at_risk_fee_revenue.get() != 0
            || self.source_lien_impaired_capital_at_risk_fee_revenue.get() != 0
    }

    #[inline]
    fn has_default_sparse_tag(self) -> bool {
        self.domain.get() == 0 && self.source_claim_market_id.get() == 0
    }

    #[inline]
    fn is_sparse_tail_default(self) -> bool {
        self.has_default_sparse_tag() && !self.is_occupied()
    }

    #[cfg(kani)]
    pub fn kani_is_sparse_tail_default(self) -> bool {
        self.is_sparse_tail_default()
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
pub struct PortfolioAccountV16Account {
    pub provenance_header: ProvenanceHeaderV16Account,
    pub owner: [u8; 32],
    pub capital: V16PodU128,
    pub pnl: V16PodI128,
    pub reserved_pnl: V16PodU128,
    // Monotonic reward-accounting counters. These do not affect margin or solvency:
    // crystallized_loss increments only when real account capital is consumed by
    // loss settlement; spent_principal caps how much of that budget has rewarded
    // counterparties; received is the LP-side total earned for matching that budget.
    pub residual_crystallized_loss_atoms_total: V16PodU128,
    pub residual_spent_principal_atoms_total: V16PodU128,
    pub residual_received_atoms_total: V16PodU128,
    pub funding_long_paid_atoms_total: V16PodU128,
    pub funding_long_received_atoms_total: V16PodU128,
    pub funding_short_paid_atoms_total: V16PodU128,
    pub funding_short_received_atoms_total: V16PodU128,
    pub fee_credits: V16PodI128,
    pub cancel_deposit_escrow: V16PodU128,
    pub last_fee_slot: V16PodU64,
    pub active_bitmap: [V16PodU64; V16_ACTIVE_BITMAP_WORDS],
    pub legs: [PortfolioLegV16Account; V16_MAX_PORTFOLIO_ASSETS_N],
    pub source_domains: [PortfolioSourceDomainV16Account; PORTFOLIO_SOURCE_DOMAIN_CAP],
    pub health_cert: HealthCertV16Account,
    pub stale_state: u8,
    pub b_stale_state: u8,
    pub rebalance_lock: u8,
    // Set while negative PnL has crossed more than one active asset and therefore
    // cannot be safely charged to any one asset's insurance/B domain.
    pub liquidation_lock: u8,
    pub close_progress: CloseProgressLedgerV16Account,
    pub resolved_payout_receipt: ResolvedPayoutReceiptV16Account,
}

// Compile-time layout guard: any change to the PortfolioAccountV16Account Pod
// layout fails the build here. When it does, bump V16_LAYOUT_DISCRIMINATOR and
// update this expected size deliberately (no deployed markets => no migration).
// Gated to non-kani: under `cfg(kani)` PORTFOLIO_SOURCE_DOMAIN_CAP is reduced for
// proof tractability, so the production on-chain layout is the non-kani one.
#[cfg(not(kani))]
const _: () = assert!(core::mem::size_of::<PortfolioAccountV16Account>() == 9419);

impl Default for PortfolioAccountV16Account {
    fn default() -> Self {
        bytemuck::Zeroable::zeroed()
    }
}

impl PortfolioAccountV16Account {
    pub fn init_empty_in_place(&mut self, header: ProvenanceHeaderV16Account) -> V16Result<()> {
        let owner = header.try_to_runtime()?.owner;
        self.provenance_header = header;
        self.owner = owner;
        self.capital = V16PodU128::new(0);
        self.pnl = V16PodI128::new(0);
        self.reserved_pnl = V16PodU128::new(0);
        self.residual_crystallized_loss_atoms_total = V16PodU128::new(0);
        self.residual_spent_principal_atoms_total = V16PodU128::new(0);
        self.residual_received_atoms_total = V16PodU128::new(0);
        self.funding_long_paid_atoms_total = V16PodU128::new(0);
        self.funding_long_received_atoms_total = V16PodU128::new(0);
        self.funding_short_paid_atoms_total = V16PodU128::new(0);
        self.funding_short_received_atoms_total = V16PodU128::new(0);
        self.fee_credits = V16PodI128::new(0);
        self.cancel_deposit_escrow = V16PodU128::new(0);
        self.last_fee_slot = V16PodU64::new(0);
        self.active_bitmap = [V16PodU64::new(0); V16_ACTIVE_BITMAP_WORDS];

        let empty_leg = PortfolioLegV16Account::from_runtime(&PortfolioLegV16::EMPTY);
        let mut i = 0usize;
        while i < V16_MAX_PORTFOLIO_ASSETS_N {
            self.legs[i] = empty_leg;
            i += 1;
        }
        let mut i = 0usize;
        while i < PORTFOLIO_SOURCE_DOMAIN_CAP {
            self.source_domains[i] = PortfolioSourceDomainV16Account::default();
            i += 1;
        }

        self.health_cert = HealthCertV16Account::default();
        self.stale_state = encode_bool(false);
        self.b_stale_state = encode_bool(false);
        self.rebalance_lock = encode_bool(false);
        self.liquidation_lock = encode_bool(false);
        self.close_progress = CloseProgressLedgerV16Account::default();
        self.resolved_payout_receipt = ResolvedPayoutReceiptV16Account::default();
        Ok(())
    }

    #[cfg(kani)]
    pub fn try_empty(header: ProvenanceHeaderV16Account) -> V16Result<Self> {
        let mut out = Self::default();
        out.init_empty_in_place(header)?;
        Ok(out)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccountBSettlementChunkV16 {
    pub delta_b: u128,
    pub loss: u128,
    pub new_remainder: u128,
    pub remaining_after: u128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct RiskScoreV16 {
    certified_liq_deficit: u128,
    unsettled_b_loss_bound: u128,
    stale_loss_bound: u128,
    gross_risk_notional: u128,
    active_leg_count: u32,
}

impl RiskScoreV16 {
    fn strictly_reduces_from(self, before: Self) -> bool {
        self < before
    }
}

/// Outcome of one bounded terminal cleanup step (upstream 545e0224; the
/// `ScanProgress` variant from 91481480 / bb877cde). The wrapper owns the
/// `ScanProgress` continuation and closes external custody only for
/// `ReadyToClose`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TerminalSlabOutcomeV16 {
    ScanProgress { next_asset_index: usize },
    BackingExpired { domain: usize },
    InsuranceRecredited { asset_index: usize, amount: u128 },
    ReadyToClose { retired: u128 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TerminalSlabAssetStepV16 {
    Expire(usize),
    Recredit,
    Wait,
    Continue,
}

/// Assets inspected by one `advance_terminal_slab_not_atomic` call.
pub const TERMINAL_SLAB_SCAN_ASSETS_PER_CALL: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PermissionlessProgressOutcomeV16 {
    AccountCurrent,
    AccountBChunk(AccountBSettlementChunkV16),
    SourceBackingExpired { domain: usize },
    ResidualBooked(BResidualBookingOutcomeV16),
    RecoveryDeclared(PermissionlessRecoveryReasonV16),
}

fn risk_notional_ceil(abs_pos_q: u128, price: u64) -> V16Result<u128> {
    if abs_pos_q == 0 {
        return Ok(0);
    }
    if let Some(product) = abs_pos_q.checked_mul(price as u128) {
        let q = product / POS_SCALE;
        let r = product % POS_SCALE;
        return q
            .checked_add(u128::from(r != 0))
            .ok_or(V16Error::ArithmeticOverflow);
    }
    checked_mul_div_ceil_u256(
        U256::from_u128(abs_pos_q),
        U256::from_u128(price as u128),
        U256::from_u128(POS_SCALE),
    )
    .and_then(|v| v.try_into_u128())
    .ok_or(V16Error::ArithmeticOverflow)
}

#[cfg(kani)]
pub fn kani_risk_notional_ceil(abs_pos_q: u128, price: u64) -> V16Result<u128> {
    risk_notional_ceil(abs_pos_q, price)
}

fn account_equity_from_parts(capital: u128, pnl: i128, fee_credits: i128) -> V16Result<i128> {
    validate_non_min_i128(pnl)?;
    validate_fee_credits(fee_credits)?;
    let capital = i128::try_from(capital).map_err(|_| V16Error::ArithmeticOverflow)?;
    let fee_debt =
        i128::try_from(fee_credits.unsigned_abs()).map_err(|_| V16Error::ArithmeticOverflow)?;
    capital
        .checked_add(pnl)
        .and_then(|v| v.checked_sub(fee_debt))
        .ok_or(V16Error::ArithmeticOverflow)
}

#[cfg(kani)]
fn position_delta_increases_risk(current: i128, delta_q: i128) -> V16Result<bool> {
    let next = current
        .checked_add(delta_q)
        .ok_or(V16Error::ArithmeticOverflow)?;
    validate_basis_or_zero(next)?;
    Ok(next.unsigned_abs() > current.unsigned_abs())
}

// upstream f06a04a7 "Keep strict trade reductions open below initial margin":
// only a STRICT reduction of the account's position on the asset is exempt from
// the final initial-margin gate; equal-size flips and increases keep it.
fn trade_account_requires_initial_margin(current: i128, next: i128) -> bool {
    next.unsigned_abs() >= current.unsigned_abs()
}

fn trade_preflight_risk_gate(
    risk_increasing: bool,
    asset_loss_stale: bool,
    target_effective_lag: bool,
    touches_pending_domain_barrier: bool,
) -> V16Result<()> {
    if touches_pending_domain_barrier
        || (risk_increasing && (asset_loss_stale || target_effective_lag))
    {
        return Err(V16Error::LockActive);
    }
    Ok(())
}

/// A trade may reduce only OI that existed before that trade. This makes
/// aggregate accounting independent of which counterparty mutates first.
/// (engine upstream #109 / 143e68c4 "Prevent same-trade OI masking";
/// ported as a free fn to match this fork's `position_delta_increases_risk`
/// / `trade_preflight_risk_gate` sibling-function convention.)
fn kernel_trade_preexisting_oi_reduction_gate(
    oi_long_q: u128,
    oi_short_q: u128,
    account_a_current_q: i128,
    account_a_next_q: i128,
    account_b_current_q: i128,
    account_b_next_q: i128,
) -> V16Result<(u128, u128)> {
    let side_reduction = |current_q: i128, next_q: i128, side: SideV16| {
        let on_side = |position_q: i128| match side {
            SideV16::Long if position_q > 0 => position_q as u128,
            SideV16::Short if position_q < 0 => position_q.unsigned_abs(),
            _ => 0,
        };
        on_side(current_q).saturating_sub(on_side(next_q))
    };
    let long_reduction_q = side_reduction(account_a_current_q, account_a_next_q, SideV16::Long)
        .checked_add(side_reduction(
            account_b_current_q,
            account_b_next_q,
            SideV16::Long,
        ))
        .ok_or(V16Error::ArithmeticOverflow)?;
    let short_reduction_q = side_reduction(account_a_current_q, account_a_next_q, SideV16::Short)
        .checked_add(side_reduction(
            account_b_current_q,
            account_b_next_q,
            SideV16::Short,
        ))
        .ok_or(V16Error::ArithmeticOverflow)?;
    if long_reduction_q > oi_long_q || short_reduction_q > oi_short_q {
        return Err(V16Error::LockActive);
    }
    Ok((long_reduction_q, short_reduction_q))
}

fn asset_risk_increase_gate(
    lifecycle: AssetLifecycleV16,
    mode_long: SideModeV16,
    mode_short: SideModeV16,
) -> V16Result<()> {
    if lifecycle != AssetLifecycleV16::Active
        || mode_long != SideModeV16::Normal
        || mode_short != SideModeV16::Normal
    {
        return Err(V16Error::LockActive);
    }
    Ok(())
}

#[cfg(kani)]
pub fn kani_position_delta_increases_risk(current: i128, delta_q: i128) -> V16Result<bool> {
    position_delta_increases_risk(current, delta_q)
}

#[cfg(kani)]
pub fn kani_position_change_requires_unit_adl(current: i128, new: i128) -> bool {
    let route = V16Core::kernel_classify_position_delta(current, new);
    V16Core::kernel_position_route_requires_unit_adl(route, current, new)
}

#[cfg(kani)]
pub fn kani_source_lien_fee_after_backing_release(
    fee_revenue: u128,
    backing_before: u128,
    backing_after: u128,
) -> V16Result<u128> {
    V16Core::source_lien_fee_after_backing_release(fee_revenue, backing_before, backing_after)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_adl_effective_quantity_ceil(
    raw_abs_q: u128,
    a_basis: u128,
    current_a: u128,
) -> V16Result<u128> {
    V16Core::kernel_adl_effective_quantity_ceil(raw_abs_q, a_basis, current_a)
}

#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_raw_basis_for_adl_effective_quantity(
    effective_abs_q: u128,
    a_basis: u128,
    current_a: u128,
) -> V16Result<u128> {
    V16Core::kernel_raw_basis_for_adl_effective_quantity(effective_abs_q, a_basis, current_a)
}

#[cfg(kani)]
pub fn kani_adl_scaled_accrual_index_deltas(
    price_delta: i128,
    funding_index_delta: i128,
    a_long: u128,
    a_short: u128,
) -> V16Result<(i128, i128, i128, i128)> {
    V16Core::kernel_adl_scaled_accrual_index_deltas(
        price_delta,
        funding_index_delta,
        a_long,
        a_short,
    )
}

#[cfg(kani)]
pub fn kani_trade_preflight_risk_gate(
    risk_increasing: bool,
    asset_loss_stale: bool,
    target_effective_lag: bool,
    touches_pending_domain_barrier: bool,
) -> V16Result<()> {
    trade_preflight_risk_gate(
        risk_increasing,
        asset_loss_stale,
        target_effective_lag,
        touches_pending_domain_barrier,
    )
}

#[cfg(kani)]
pub fn kani_terminal_claim_free_overlap_recredit(
    provider_receivable_atoms: u128,
    paired_domain_insurance_spent: u128,
    claim_free_residual_remaining: u128,
) -> u128 {
    V16Core::terminal_claim_free_overlap_recredit(
        provider_receivable_atoms,
        paired_domain_insurance_spent,
        claim_free_residual_remaining,
    )
}

#[cfg(kani)]
pub fn kani_terminal_slab_asset_step(
    long_status: BackingBucketStatusV16,
    long_expiry_slot: u64,
    short_status: BackingBucketStatusV16,
    short_expiry_slot: u64,
    authenticated_slot: u64,
    recreditable: bool,
) -> u8 {
    match V16Core::kernel_terminal_slab_asset_step(
        long_status,
        long_expiry_slot,
        short_status,
        short_expiry_slot,
        authenticated_slot,
        recreditable,
    ) {
        TerminalSlabAssetStepV16::Expire(0) => 0,
        TerminalSlabAssetStepV16::Expire(_) => 1,
        TerminalSlabAssetStepV16::Recredit => 2,
        TerminalSlabAssetStepV16::Wait => 3,
        TerminalSlabAssetStepV16::Continue => 4,
    }
}

#[cfg(kani)]
pub fn kani_terminal_slab_wait_continuation(
    scan_start_asset_index: usize,
    asset_index: usize,
) -> V16Result<usize> {
    V16Core::kernel_terminal_slab_wait_continuation(scan_start_asset_index, asset_index)
}

// upstream a2760ddb ("Prove terminal insurance retirement isolation") frames the
// public retirement route with these field-wise equalities (upstream keeps them in
// src/v16_kani_api.rs). Fork adaptation: the header also compares the fork A-6
// stress-envelope fields.
#[cfg(kani)]
pub fn kani_eq_v16_config_account(a: &V16ConfigAccount, b: &V16ConfigAccount) -> bool {
    a.max_portfolio_assets.get() == b.max_portfolio_assets.get()
        && a.max_market_slots.get() == b.max_market_slots.get()
        && a.min_nonzero_mm_req.get() == b.min_nonzero_mm_req.get()
        && a.min_nonzero_im_req.get() == b.min_nonzero_im_req.get()
        && a.h_min.get() == b.h_min.get()
        && a.h_max.get() == b.h_max.get()
        && a.maintenance_margin_bps.get() == b.maintenance_margin_bps.get()
        && a.initial_margin_bps.get() == b.initial_margin_bps.get()
        && a.max_trading_fee_bps.get() == b.max_trading_fee_bps.get()
        && a.liquidation_fee_bps.get() == b.liquidation_fee_bps.get()
        && a.liquidation_fee_cap.get() == b.liquidation_fee_cap.get()
        && a.min_liquidation_abs.get() == b.min_liquidation_abs.get()
        && a.max_accrual_dt_slots.get() == b.max_accrual_dt_slots.get()
        && a.max_abs_funding_e9_per_slot.get() == b.max_abs_funding_e9_per_slot.get()
        && a.min_funding_lifetime_slots.get() == b.min_funding_lifetime_slots.get()
        && a.max_price_move_bps_per_slot.get() == b.max_price_move_bps_per_slot.get()
        && a.max_account_b_settlement_chunks.get() == b.max_account_b_settlement_chunks.get()
        && a.max_bankrupt_close_chunks.get() == b.max_bankrupt_close_chunks.get()
        && a.max_bankrupt_close_lifetime_slots.get() == b.max_bankrupt_close_lifetime_slots.get()
        && a.asset_activation_cooldown_slots.get() == b.asset_activation_cooldown_slots.get()
        && a.public_b_chunk_atoms.get() == b.public_b_chunk_atoms.get()
        && a.max_recovery_fallback_deviation_bps.get()
            == b.max_recovery_fallback_deviation_bps.get()
        && a.backing_fee_base_rate_e9_per_slot.get() == b.backing_fee_base_rate_e9_per_slot.get()
        && a.backing_fee_kink_util_bps.get() == b.backing_fee_kink_util_bps.get()
        && a.backing_fee_slope_at_kink_e9_per_slot.get()
            == b.backing_fee_slope_at_kink_e9_per_slot.get()
        && a.backing_fee_slope_above_kink_e9_per_slot.get()
            == b.backing_fee_slope_above_kink_e9_per_slot.get()
        && a.backing_freshness_buckets == b.backing_freshness_buckets
        && a.margin_mode_realizable_full_shared_cross_margin
            == b.margin_mode_realizable_full_shared_cross_margin
        && a.source_credit_lien_required == b.source_credit_lien_required
        && a.insurance_credit_reservation_required == b.insurance_credit_reservation_required
        && a.permissionless_recovery_enabled == b.permissionless_recovery_enabled
        && a.recovery_fallback_price_enabled == b.recovery_fallback_price_enabled
        && a.recovery_fallback_envelope_enabled == b.recovery_fallback_envelope_enabled
        && a.credit_lien_revalidation_required == b.credit_lien_revalidation_required
        && a.stale_certificate_penalty_enabled == b.stale_certificate_penalty_enabled
        && a.full_refresh_required_for_favorable_actions
            == b.full_refresh_required_for_favorable_actions
        && a.public_liveness_profile_crank_forward == b.public_liveness_profile_crank_forward
}

#[cfg(kani)]
pub fn kani_eq_v16_optional_recovery_reason_account(
    a: &V16OptionalRecoveryReasonAccount,
    b: &V16OptionalRecoveryReasonAccount,
) -> bool {
    a.present == b.present && a.value == b.value
}

#[cfg(kani)]
pub fn kani_eq_resolved_payout_ledger_v16_account(
    a: &ResolvedPayoutLedgerV16Account,
    b: &ResolvedPayoutLedgerV16Account,
) -> bool {
    a.snapshot_residual.get() == b.snapshot_residual.get()
        && a.terminal_claim_exact_receipts_num.get() == b.terminal_claim_exact_receipts_num.get()
        && a.terminal_claim_bound_unreceipted_num.get()
            == b.terminal_claim_bound_unreceipted_num.get()
        && a.current_payout_rate_num.get() == b.current_payout_rate_num.get()
        && a.current_payout_rate_den.get() == b.current_payout_rate_den.get()
        && a.snapshot_slot.get() == b.snapshot_slot.get()
        && a.payout_halted == b.payout_halted
        && a.finalized == b.finalized
}

#[cfg(kani)]
pub fn kani_eq_market_group_v16_header_account(
    a: &MarketGroupV16HeaderAccount,
    b: &MarketGroupV16HeaderAccount,
) -> bool {
    ({
        let mut i = 0;
        let mut ok = true;
        while i < 32 {
            ok = ok && a.market_group_id[i] == b.market_group_id[i];
            i += 1;
        }
        ok
    }) && kani_eq_v16_config_account(&a.config, &b.config)
        && a.asset_slot_capacity.get() == b.asset_slot_capacity.get()
        && a.vault.get() == b.vault.get()
        && a.insurance.get() == b.insurance.get()
        && a.c_tot.get() == b.c_tot.get()
        && a.pnl_pos_tot.get() == b.pnl_pos_tot.get()
        && a.pnl_pos_bound_tot_num.get() == b.pnl_pos_bound_tot_num.get()
        && a.pnl_pos_bound_tot.get() == b.pnl_pos_bound_tot.get()
        && a.pnl_matured_pos_tot.get() == b.pnl_matured_pos_tot.get()
        && a.backing_provider_earnings_total.get() == b.backing_provider_earnings_total.get()
        && a.source_claim_bound_total_num.get() == b.source_claim_bound_total_num.get()
        && a.source_fresh_backing_total_num.get() == b.source_fresh_backing_total_num.get()
        && a.source_insurance_credit_reserved_total_atoms.get()
            == b.source_insurance_credit_reserved_total_atoms.get()
        && a.insurance_domain_budget_remaining_total.get()
            == b.insurance_domain_budget_remaining_total.get()
        && a.resolved_payout_blocker_count.get() == b.resolved_payout_blocker_count.get()
        && a.stress_consumption_bps_e9_since_envelope.get()
            == b.stress_consumption_bps_e9_since_envelope.get()
        && a.stress_envelope_start_slot.get() == b.stress_envelope_start_slot.get()
        && a.stress_envelope_start_credit_epoch.get() == b.stress_envelope_start_credit_epoch.get()
        && a.materialized_portfolio_count.get() == b.materialized_portfolio_count.get()
        && a.stale_certificate_count.get() == b.stale_certificate_count.get()
        && a.b_stale_account_count.get() == b.b_stale_account_count.get()
        && a.negative_pnl_account_count.get() == b.negative_pnl_account_count.get()
        && a.risk_epoch.get() == b.risk_epoch.get()
        && a.asset_set_epoch.get() == b.asset_set_epoch.get()
        && a.asset_activation_count.get() == b.asset_activation_count.get()
        && a.last_asset_activation_slot.get() == b.last_asset_activation_slot.get()
        && a.next_market_id.get() == b.next_market_id.get()
        && a.oracle_epoch.get() == b.oracle_epoch.get()
        && a.funding_epoch.get() == b.funding_epoch.get()
        && a.slot_last.get() == b.slot_last.get()
        && a.current_slot.get() == b.current_slot.get()
        && a.bankruptcy_hlock_active == b.bankruptcy_hlock_active
        && a.threshold_stress_active == b.threshold_stress_active
        && a.loss_stale_active == b.loss_stale_active
        && kani_eq_v16_optional_recovery_reason_account(&a.recovery_reason, &b.recovery_reason)
        && a.mode == b.mode
        && a.resolved_slot.get() == b.resolved_slot.get()
        && a.payout_snapshot.get() == b.payout_snapshot.get()
        && a.payout_snapshot_pnl_pos_tot.get() == b.payout_snapshot_pnl_pos_tot.get()
        && a.payout_snapshot_captured == b.payout_snapshot_captured
        && kani_eq_resolved_payout_ledger_v16_account(
            &a.resolved_payout_ledger,
            &b.resolved_payout_ledger,
        )
}

#[cfg(kani)]
pub fn kani_eq_asset_state_v16_account(a: &AssetStateV16Account, b: &AssetStateV16Account) -> bool {
    a.market_id.get() == b.market_id.get()
        && a.retired_slot.get() == b.retired_slot.get()
        && a.lifecycle == b.lifecycle
        && a.raw_oracle_target_price.get() == b.raw_oracle_target_price.get()
        && a.effective_price.get() == b.effective_price.get()
        && a.fund_px_last.get() == b.fund_px_last.get()
        && a.slot_last.get() == b.slot_last.get()
        && a.a_long.get() == b.a_long.get()
        && a.a_short.get() == b.a_short.get()
        && a.k_long.get() == b.k_long.get()
        && a.k_short.get() == b.k_short.get()
        && a.f_long_num.get() == b.f_long_num.get()
        && a.f_short_num.get() == b.f_short_num.get()
        && a.kf_epoch_long.get() == b.kf_epoch_long.get()
        && a.kf_epoch_short.get() == b.kf_epoch_short.get()
        && a.k_epoch_start_long.get() == b.k_epoch_start_long.get()
        && a.k_epoch_start_short.get() == b.k_epoch_start_short.get()
        && a.f_epoch_start_long_num.get() == b.f_epoch_start_long_num.get()
        && a.f_epoch_start_short_num.get() == b.f_epoch_start_short_num.get()
        && a.b_long_num.get() == b.b_long_num.get()
        && a.b_short_num.get() == b.b_short_num.get()
        && a.b_epoch_start_long_num.get() == b.b_epoch_start_long_num.get()
        && a.b_epoch_start_short_num.get() == b.b_epoch_start_short_num.get()
        && a.oi_eff_long_q.get() == b.oi_eff_long_q.get()
        && a.oi_eff_short_q.get() == b.oi_eff_short_q.get()
        && a.stored_pos_count_long.get() == b.stored_pos_count_long.get()
        && a.stored_pos_count_short.get() == b.stored_pos_count_short.get()
        && a.stale_account_count_long.get() == b.stale_account_count_long.get()
        && a.stale_account_count_short.get() == b.stale_account_count_short.get()
        && a.pending_obligation_count_long.get() == b.pending_obligation_count_long.get()
        && a.pending_obligation_count_short.get() == b.pending_obligation_count_short.get()
        && a.loss_weight_sum_long.get() == b.loss_weight_sum_long.get()
        && a.loss_weight_sum_short.get() == b.loss_weight_sum_short.get()
        && a.social_loss_remainder_long_num.get() == b.social_loss_remainder_long_num.get()
        && a.social_loss_remainder_short_num.get() == b.social_loss_remainder_short_num.get()
        && a.social_loss_dust_long_num.get() == b.social_loss_dust_long_num.get()
        && a.social_loss_dust_short_num.get() == b.social_loss_dust_short_num.get()
        && a.explicit_unallocated_loss_long.get() == b.explicit_unallocated_loss_long.get()
        && a.explicit_unallocated_loss_short.get() == b.explicit_unallocated_loss_short.get()
        && a.epoch_long.get() == b.epoch_long.get()
        && a.epoch_short.get() == b.epoch_short.get()
        && a.mode_long == b.mode_long
        && a.mode_short == b.mode_short
}

#[cfg(kani)]
pub fn kani_eq_source_credit_state_v16_account(
    a: &SourceCreditStateV16Account,
    b: &SourceCreditStateV16Account,
) -> bool {
    a.positive_claim_bound_num.get() == b.positive_claim_bound_num.get()
        && a.exact_positive_claim_num.get() == b.exact_positive_claim_num.get()
        && a.fresh_reserved_backing_num.get() == b.fresh_reserved_backing_num.get()
        && a.spent_backing_num.get() == b.spent_backing_num.get()
        && a.provider_receivable_num.get() == b.provider_receivable_num.get()
        && a.valid_liened_backing_num.get() == b.valid_liened_backing_num.get()
        && a.impaired_liened_backing_num.get() == b.impaired_liened_backing_num.get()
        && a.insurance_credit_reserved_num.get() == b.insurance_credit_reserved_num.get()
        && a.valid_liened_insurance_num.get() == b.valid_liened_insurance_num.get()
        && a.impaired_liened_insurance_num.get() == b.impaired_liened_insurance_num.get()
        && a.credit_rate_num.get() == b.credit_rate_num.get()
        && a.credit_epoch.get() == b.credit_epoch.get()
}

#[cfg(kani)]
pub fn kani_eq_backing_bucket_v16_account(
    a: &BackingBucketV16Account,
    b: &BackingBucketV16Account,
) -> bool {
    a.market_id.get() == b.market_id.get()
        && a.fresh_unliened_backing_num.get() == b.fresh_unliened_backing_num.get()
        && a.valid_liened_backing_num.get() == b.valid_liened_backing_num.get()
        && a.consumed_liened_backing_num.get() == b.consumed_liened_backing_num.get()
        && a.impaired_liened_backing_num.get() == b.impaired_liened_backing_num.get()
        && a.utilization_fee_earnings.get() == b.utilization_fee_earnings.get()
        && a.expiry_slot.get() == b.expiry_slot.get()
        && a.status == b.status
}

#[cfg(kani)]
pub fn kani_eq_insurance_credit_reservation_v16_account(
    a: &InsuranceCreditReservationV16Account,
    b: &InsuranceCreditReservationV16Account,
) -> bool {
    a.insurance_credit_reserved_num.get() == b.insurance_credit_reserved_num.get()
        && a.valid_liened_insurance_num.get() == b.valid_liened_insurance_num.get()
        && a.impaired_liened_insurance_num.get() == b.impaired_liened_insurance_num.get()
        && a.consumed_insurance_num.get() == b.consumed_insurance_num.get()
        && a.source_credit_epoch.get() == b.source_credit_epoch.get()
}

#[cfg(kani)]
pub fn kani_eq_engine_asset_slot_v16_account(
    a: &EngineAssetSlotV16Account,
    b: &EngineAssetSlotV16Account,
) -> bool {
    kani_eq_asset_state_v16_account(&a.asset, &b.asset)
        && a.insurance_domain_budget_long.get() == b.insurance_domain_budget_long.get()
        && a.insurance_domain_budget_short.get() == b.insurance_domain_budget_short.get()
        && a.insurance_domain_spent_long.get() == b.insurance_domain_spent_long.get()
        && a.insurance_domain_spent_short.get() == b.insurance_domain_spent_short.get()
        && a.pending_domain_loss_barrier_long.get() == b.pending_domain_loss_barrier_long.get()
        && a.pending_domain_loss_barrier_short.get() == b.pending_domain_loss_barrier_short.get()
        && kani_eq_source_credit_state_v16_account(&a.source_credit_long, &b.source_credit_long)
        && kani_eq_source_credit_state_v16_account(&a.source_credit_short, &b.source_credit_short)
        && kani_eq_backing_bucket_v16_account(&a.backing_long, &b.backing_long)
        && kani_eq_backing_bucket_v16_account(&a.backing_short, &b.backing_short)
        && kani_eq_insurance_credit_reservation_v16_account(
            &a.insurance_reservation_long,
            &b.insurance_reservation_long,
        )
        && kani_eq_insurance_credit_reservation_v16_account(
            &a.insurance_reservation_short,
            &b.insurance_reservation_short,
        )
}

#[cfg(kani)]
pub fn kani_trade_preexisting_oi_reduction_gate(
    oi_long_q: u128,
    oi_short_q: u128,
    account_a_current_q: i128,
    account_a_next_q: i128,
    account_b_current_q: i128,
    account_b_next_q: i128,
) -> V16Result<(u128, u128)> {
    kernel_trade_preexisting_oi_reduction_gate(
        oi_long_q,
        oi_short_q,
        account_a_current_q,
        account_a_next_q,
        account_b_current_q,
        account_b_next_q,
    )
}

fn margin_requirement(notional: u128, bps: u64, floor: u128) -> V16Result<u128> {
    if notional == 0 {
        return Ok(0);
    }
    let raw = V16Core::mul_div_ceil_u128_or_wide(notional, bps as u128, MAX_MARGIN_BPS as u128)?;
    Ok(raw.max(floor))
}

fn trade_notional_floor(size_q: u128, exec_price: u64) -> V16Result<u128> {
    if size_q == 0 {
        return Ok(0);
    }
    if let Some(product) = size_q.checked_mul(exec_price as u128) {
        return Ok(product / POS_SCALE);
    }
    let (q, _) = mul_div_floor_u256_with_rem(
        U256::from_u128(size_q),
        U256::from_u128(exec_price as u128),
        U256::from_u128(POS_SCALE),
    );
    q.try_into_u128().ok_or(V16Error::ArithmeticOverflow)
}

#[cfg(kani)]
pub fn kani_trade_notional_floor(size_q: u128, exec_price: u64) -> V16Result<u128> {
    trade_notional_floor(size_q, exec_price)
}

// E4 (upstream 8f25aa5d, "Charge sub-atom trade fees on ceil notional"): the fee
// charged on a fill must be computed on the CEIL notional, not the floor notional
// used for margin/PnL bookkeeping (`trade_notional_floor` above). A sub-atom fill
// (size_q * exec_price / POS_SCALE < 1) floors to notional=0 and therefore fee=0
// via `checked_fee_bps`'s notional==0 short-circuit, even though the fill opens
// nonzero OI (free, fee-less risk). Reuses `risk_notional_ceil` (already used by
// the liquidation-fee path at this same ceil-notional pattern) so a trade sized
// to leave ANY nonzero remainder after the POS_SCALE division rounds up to at
// least 1 atom of notional, and therefore charges at least 1 atom of fee whenever
// fee_bps != 0. Deliberately kept as a SEPARATE value from `notional` above --
// `notional` (floor) still drives `TradeApplyOutcomeV16.notional` / batch
// aggregation / PnL-neutral accounting; only the fee calc uses the ceil.
fn trade_fee_notional_ceil(size_q: u128, exec_price: u64) -> V16Result<u128> {
    if size_q == 0 || exec_price == 0 {
        return Ok(0);
    }
    risk_notional_ceil(size_q, exec_price)
}

#[cfg(kani)]
pub fn kani_trade_fee_notional_ceil(size_q: u128, exec_price: u64) -> V16Result<u128> {
    trade_fee_notional_ceil(size_q, exec_price)
}

fn checked_fee_bps(notional: u128, fee_bps: u64) -> V16Result<u128> {
    if notional == 0 || fee_bps == 0 {
        return Ok(0);
    }
    if let Some(product) = notional.checked_mul(fee_bps as u128) {
        let den = MAX_MARGIN_BPS as u128;
        let q = product / den;
        let r = product % den;
        return q
            .checked_add(u128::from(r != 0))
            .ok_or(V16Error::ArithmeticOverflow);
    }
    checked_mul_div_ceil_u256(
        U256::from_u128(notional),
        U256::from_u128(fee_bps as u128),
        U256::from_u128(MAX_MARGIN_BPS as u128),
    )
    .and_then(|v| v.try_into_u128())
    .ok_or(V16Error::ArithmeticOverflow)
}

#[cfg(kani)]
pub fn kani_checked_fee_bps(notional: u128, fee_bps: u64) -> V16Result<u128> {
    checked_fee_bps(notional, fee_bps)
}

// FIX E3 (upstream #92 / b97e1746): liquidation fee is CONFIG-derived only
// (never caller-supplied `fee_bps`), and a partial liquidation chunk whose
// proportional fee falls below `min_liquidation_abs` is rejected as
// NonProgress rather than silently inflated to the floor -- that inflation
// is exactly the "min-fee chunking" exploit this fix closes. A full-position
// close is exempt from the floor rejection (dust closes must still be able
// to progress) and is instead clamped up to the floor as before.
fn liquidation_fee_for_close(
    fee_notional: u128,
    fee_bps: u64,
    min_liquidation_abs: u128,
    liquidation_fee_cap: u128,
    closes_full_position: bool,
) -> V16Result<u128> {
    if fee_notional > MAX_ACCOUNT_NOTIONAL || fee_bps > MAX_MARGIN_BPS {
        return Err(V16Error::InvalidConfig);
    }
    let product = fee_notional * fee_bps as u128;
    let q = product / MAX_MARGIN_BPS as u128;
    let r = product % MAX_MARGIN_BPS as u128;
    let raw_fee = q
        .checked_add(u128::from(r != 0))
        .ok_or(V16Error::ArithmeticOverflow)?;
    liquidation_fee_from_raw_fee(
        raw_fee,
        min_liquidation_abs,
        liquidation_fee_cap,
        closes_full_position,
    )
}

fn liquidation_fee_from_raw_fee(
    raw_fee: u128,
    min_liquidation_abs: u128,
    liquidation_fee_cap: u128,
    closes_full_position: bool,
) -> V16Result<u128> {
    if !closes_full_position && min_liquidation_abs != 0 && raw_fee < min_liquidation_abs {
        return Err(V16Error::NonProgress);
    }
    Ok(raw_fee.max(min_liquidation_abs).min(liquidation_fee_cap))
}

#[cfg(kani)]
pub fn kani_liquidation_fee_for_close(
    fee_notional: u128,
    fee_bps: u64,
    min_liquidation_abs: u128,
    liquidation_fee_cap: u128,
    closes_full_position: bool,
) -> V16Result<u128> {
    liquidation_fee_for_close(
        fee_notional,
        fee_bps,
        min_liquidation_abs,
        liquidation_fee_cap,
        closes_full_position,
    )
}

#[cfg(kani)]
pub fn kani_liquidation_fee_from_raw_fee(
    raw_fee: u128,
    min_liquidation_abs: u128,
    liquidation_fee_cap: u128,
    closes_full_position: bool,
) -> V16Result<u128> {
    liquidation_fee_from_raw_fee(
        raw_fee,
        min_liquidation_abs,
        liquidation_fee_cap,
        closes_full_position,
    )
}

/// Per-side trade fee atoms, mirroring the production derivation in
/// `execute_trade_*` exactly (ceil fee notional -> ceil bps). Proof shim for the
/// no-free-OI lower bound: a nonzero fill at nonzero price with nonzero fee must
/// charge >= 1 atom. See `proof_v16_nonzero_trade_charges_positive_fee_per_side`.
/// (upstream 63891280)
#[cfg(any(kani, feature = "fuzz"))]
pub fn kani_trade_fee_atoms_per_side(
    size_q: u128,
    exec_price: u64,
    fee_bps: u64,
) -> V16Result<u128> {
    let fee_notional = trade_fee_notional_ceil(size_q, exec_price)?;
    checked_fee_bps(fee_notional, fee_bps)
}

fn checked_i128_mul(a: i128, b: i128) -> V16Result<i128> {
    let out = a.checked_mul(b).ok_or(V16Error::ArithmeticOverflow)?;
    validate_non_min_i128(out)?;
    Ok(out)
}

fn add_non_min_i128(a: i128, b: i128) -> V16Result<i128> {
    let out = a.checked_add(b).ok_or(V16Error::ArithmeticOverflow)?;
    validate_non_min_i128(out)?;
    Ok(out)
}

fn adjust_u128(current: u128, old: u128, new: u128) -> V16Result<u128> {
    if new >= old {
        current
            .checked_add(new - old)
            .ok_or(V16Error::ArithmeticOverflow)
    } else {
        current
            .checked_sub(old - new)
            .ok_or(V16Error::CounterUnderflow)
    }
}

#[cfg(kani)]
pub fn kani_adjust_u128(current: u128, old: u128, new: u128) -> V16Result<u128> {
    adjust_u128(current, old, new)
}

fn encode_bool(value: bool) -> u8 {
    if value {
        1
    } else {
        0
    }
}

fn decode_bool(value: u8) -> V16Result<bool> {
    match value {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn encode_side(value: SideV16) -> u8 {
    match value {
        SideV16::Long => 0,
        SideV16::Short => 1,
    }
}

fn decode_side(value: u8) -> V16Result<SideV16> {
    match value {
        0 => Ok(SideV16::Long),
        1 => Ok(SideV16::Short),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn encode_side_mode(value: SideModeV16) -> u8 {
    match value {
        SideModeV16::Normal => 0,
        SideModeV16::DrainOnly => 1,
        SideModeV16::ResetPending => 2,
    }
}

fn decode_side_mode(value: u8) -> V16Result<SideModeV16> {
    match value {
        0 => Ok(SideModeV16::Normal),
        1 => Ok(SideModeV16::DrainOnly),
        2 => Ok(SideModeV16::ResetPending),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn encode_asset_lifecycle(value: AssetLifecycleV16) -> u8 {
    match value {
        AssetLifecycleV16::Disabled => 0,
        AssetLifecycleV16::PendingActivation => 1,
        AssetLifecycleV16::Active => 2,
        AssetLifecycleV16::DrainOnly => 3,
        AssetLifecycleV16::Retired => 4,
        AssetLifecycleV16::Recovery => 5,
    }
}

fn decode_asset_lifecycle(value: u8) -> V16Result<AssetLifecycleV16> {
    match value {
        0 => Ok(AssetLifecycleV16::Disabled),
        1 => Ok(AssetLifecycleV16::PendingActivation),
        2 => Ok(AssetLifecycleV16::Active),
        3 => Ok(AssetLifecycleV16::DrainOnly),
        4 => Ok(AssetLifecycleV16::Retired),
        5 => Ok(AssetLifecycleV16::Recovery),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn encode_market_mode(value: MarketModeV16) -> u8 {
    match value {
        MarketModeV16::Live => 0,
        MarketModeV16::Resolved => 1,
        MarketModeV16::Recovery => 2,
    }
}

fn decode_market_mode(value: u8) -> V16Result<MarketModeV16> {
    match value {
        0 => Ok(MarketModeV16::Live),
        1 => Ok(MarketModeV16::Resolved),
        2 => Ok(MarketModeV16::Recovery),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn encode_backing_bucket_status(value: BackingBucketStatusV16) -> u8 {
    match value {
        BackingBucketStatusV16::Empty => 0,
        BackingBucketStatusV16::Fresh => 1,
        BackingBucketStatusV16::Expired => 2,
        BackingBucketStatusV16::Impaired => 3,
    }
}

fn decode_backing_bucket_status(value: u8) -> V16Result<BackingBucketStatusV16> {
    match value {
        0 => Ok(BackingBucketStatusV16::Empty),
        1 => Ok(BackingBucketStatusV16::Fresh),
        2 => Ok(BackingBucketStatusV16::Expired),
        3 => Ok(BackingBucketStatusV16::Impaired),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn encode_recovery_reason(value: PermissionlessRecoveryReasonV16) -> u8 {
    match value {
        PermissionlessRecoveryReasonV16::BelowProgressFloor => 0,
        PermissionlessRecoveryReasonV16::BlockedSegmentHeadroomOrRepresentability => 1,
        PermissionlessRecoveryReasonV16::AccountBSettlementCannotProgress => 2,
        PermissionlessRecoveryReasonV16::BIndexHeadroomExhausted => 3,
        PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress => 4,
        PermissionlessRecoveryReasonV16::ExplicitLossOrDustAuditOverflow => 5,
        PermissionlessRecoveryReasonV16::OracleOrTargetUnavailableByAuthenticatedPolicy => 6,
        PermissionlessRecoveryReasonV16::CounterOrEpochOverflowDeclaredRecovery => 7,
    }
}

fn decode_recovery_reason(value: u8) -> V16Result<PermissionlessRecoveryReasonV16> {
    match value {
        0 => Ok(PermissionlessRecoveryReasonV16::BelowProgressFloor),
        1 => Ok(PermissionlessRecoveryReasonV16::BlockedSegmentHeadroomOrRepresentability),
        2 => Ok(PermissionlessRecoveryReasonV16::AccountBSettlementCannotProgress),
        3 => Ok(PermissionlessRecoveryReasonV16::BIndexHeadroomExhausted),
        4 => Ok(PermissionlessRecoveryReasonV16::ActiveBankruptCloseCannotProgress),
        5 => Ok(PermissionlessRecoveryReasonV16::ExplicitLossOrDustAuditOverflow),
        6 => Ok(PermissionlessRecoveryReasonV16::OracleOrTargetUnavailableByAuthenticatedPolicy),
        7 => Ok(PermissionlessRecoveryReasonV16::CounterOrEpochOverflowDeclaredRecovery),
        _ => Err(V16Error::InvalidConfig),
    }
}

fn validate_basis_or_zero(basis_pos_q: i128) -> V16Result<()> {
    if basis_pos_q == 0 {
        Ok(())
    } else {
        validate_basis(basis_pos_q)
    }
}

fn signed_position(leg: PortfolioLegV16) -> i128 {
    if !leg.active {
        0
    } else {
        match leg.side {
            SideV16::Long => leg.basis_pos_q.unsigned_abs() as i128,
            SideV16::Short => -(leg.basis_pos_q.unsigned_abs() as i128),
        }
    }
}

fn opposite_side(side: SideV16) -> SideV16 {
    match side {
        SideV16::Long => SideV16::Short,
        SideV16::Short => SideV16::Long,
    }
}

fn fraction_ge(lhs_num: u128, lhs_den: u128, rhs_num: u128, rhs_den: u128) -> V16Result<bool> {
    if lhs_den == 0 || rhs_den == 0 {
        return Err(V16Error::InvalidConfig);
    }
    let lhs = U256::from_u128(lhs_num)
        .checked_mul(U256::from_u128(rhs_den))
        .ok_or(V16Error::ArithmeticOverflow)?;
    let rhs = U256::from_u128(rhs_num)
        .checked_mul(U256::from_u128(lhs_den))
        .ok_or(V16Error::ArithmeticOverflow)?;
    Ok(lhs >= rhs)
}

fn validate_non_min_i128(v: i128) -> V16Result<()> {
    if v == i128::MIN {
        return Err(V16Error::ArithmeticOverflow);
    }
    Ok(())
}

fn validate_fee_credits(v: i128) -> V16Result<()> {
    validate_non_min_i128(v)?;
    if v > 0 {
        return Err(V16Error::InvalidLeg);
    }
    Ok(())
}

fn validate_basis(basis_pos_q: i128) -> V16Result<()> {
    if basis_pos_q == 0
        || basis_pos_q == i128::MIN
        || basis_pos_q.unsigned_abs() > MAX_POSITION_ABS_Q
    {
        return Err(V16Error::InvalidLeg);
    }
    Ok(())
}

fn validate_active_leg(leg: PortfolioLegV16) -> V16Result<()> {
    validate_non_min_i128(leg.k_snap)?;
    validate_non_min_i128(leg.f_snap)?;
    let current_loss_weight = if leg.basis_pos_q == 0 {
        0
    } else {
        validate_basis(leg.basis_pos_q)?;
        loss_weight_for_basis(leg.basis_pos_q.unsigned_abs(), leg.a_basis)?
    };
    if !(MIN_A_SIDE..=ADL_ONE).contains(&leg.a_basis)
        || leg.loss_weight == 0
        || leg.loss_weight < current_loss_weight
        || leg.loss_weight > SOCIAL_LOSS_DEN
        || leg.b_rem >= SOCIAL_LOSS_DEN
        || leg.b_epoch_snap != leg.epoch_snap
    {
        return Err(V16Error::InvalidLeg);
    }
    Ok(())
}

fn snapshot_epoch_bound_to_side(epoch_snap: u64, side_epoch: u64, mode: SideModeV16) -> bool {
    epoch_snap == side_epoch
        || (mode == SideModeV16::ResetPending && epoch_snap.checked_add(1) == Some(side_epoch))
}

fn leg_snapshots_bound_to_asset_side(asset: AssetStateV16, leg: PortfolioLegV16) -> bool {
    let (side_epoch, kf_epoch, mode) = match leg.side {
        SideV16::Long => (asset.epoch_long, asset.kf_epoch_long, asset.mode_long),
        SideV16::Short => (asset.epoch_short, asset.kf_epoch_short, asset.mode_short),
    };
    leg.kf_epoch_snap <= kf_epoch
        && snapshot_epoch_bound_to_side(leg.epoch_snap, side_epoch, mode)
        && snapshot_epoch_bound_to_side(leg.b_epoch_snap, side_epoch, mode)
}

fn same_side_risk_reduction_or_flat_obligation(current: i128, next: i128) -> bool {
    current != 0
        && (next == 0 || current.signum() == next.signum())
        && next.unsigned_abs() < current.unsigned_abs()
}

fn pending_domain_loss_barrier_blocks_position_change(
    touches_barrier: bool,
    current: i128,
    next: i128,
) -> bool {
    touches_barrier && !same_side_risk_reduction_or_flat_obligation(current, next)
}

#[cfg(kani)]
pub fn kani_pending_domain_loss_barrier_blocks_position_change(
    touches_barrier: bool,
    current: i128,
    next: i128,
) -> bool {
    pending_domain_loss_barrier_blocks_position_change(touches_barrier, current, next)
}

fn loss_weight_for_basis(abs_basis_q: u128, a_basis: u128) -> V16Result<u128> {
    if a_basis == 0 {
        return Err(V16Error::InvalidLeg);
    }
    checked_mul_div_ceil_u256(
        U256::from_u128(abs_basis_q),
        U256::from_u128(SOCIAL_WEIGHT_SCALE),
        U256::from_u128(a_basis),
    )
    .and_then(|v| v.try_into_u128())
    .ok_or(V16Error::ArithmeticOverflow)
}

fn scaled_adl_delta_fast(abs_basis_q: u128, a_basis: u128, then: i128, now: i128) -> Option<i128> {
    if abs_basis_q == 0 {
        return Some(0);
    }
    if a_basis != ADL_ONE {
        return None;
    }
    let adl_one_i = i128::try_from(ADL_ONE).ok()?;
    let delta = now.checked_sub(then)?;
    if delta % adl_one_i != 0 {
        return None;
    }
    let scaled_delta = delta / adl_one_i;
    let basis_i = i128::try_from(abs_basis_q).ok()?;
    let numerator = scaled_delta.checked_mul(basis_i)?;
    Some(floor_div_signed_conservative_i128(numerator, POS_SCALE))
}

#[cfg(kani)]
pub fn kani_scaled_adl_delta_fast(
    abs_basis_q: u128,
    a_basis: u128,
    then: i128,
    now: i128,
) -> Option<i128> {
    scaled_adl_delta_fast(abs_basis_q, a_basis, then, now)
}

// ============================================================================
// fork feature: LP Vault share-math module (re-grafted onto the zero-copy core,
// byte-identical to the fork baseline). Pure primitive NAV/share math — no engine or
// runtime types — so it survives the runtime-vec drop clean (collision matrix row 13).
// Gated behind fork-facade; the wrapper enables that feature on its engine dep.
// ============================================================================
#[cfg(feature = "fork-facade")]
pub mod lp_vault {
    use super::{V16Error, V16Result};
    use crate::wide_math::wide_mul_div_floor_u128;
    use crate::MAX_MARGIN_BPS;

    /// Net asset value of the LP Vault, in collateral atoms, derived
    /// strictly from backing-domain ledger counters (Note 2 security
    /// invariant). All inputs come from `BackingDomainLedgerAccountV16`:
    ///
    /// - `total_principal_atoms`           current principal (deposits - withdraws)
    /// - `total_earnings_atoms`            cumulative utilization-fee earnings
    /// - `total_earnings_withdrawn_atoms`  cumulative earnings withdrawn
    /// - `cumulative_loss_atoms`           cumulative impaired/consumed principal
    /// - `cumulative_recovery_atoms`       cumulative recovered principal
    /// - `fee_share_bps`                   LP share of earnings (0..=10_000)
    ///
    /// `NAV = available_principal + lp_earnings`, where
    ///   `available_principal = total_principal_atoms - (loss - recovery)`
    ///   `lp_earnings = floor((earnings - earnings_withdrawn) * fee_share_bps / 10_000)`
    ///
    /// `loss - recovery` equals the current unavailable principal and is
    /// always `>= 0` by the ledger's construction (both counters track the
    /// same `unavailable_principal` going up = loss, down = recovery — see
    /// `sync_backing_domain_ledger` in `percolator-prog`). We nonetheless
    /// fail closed on any underflow as an accounting anomaly.
    ///
    /// NOTE: the insurance-side fraction of earnings
    /// `(1 - fee_share_bps/10_000)` is intentionally NOT counted in NAV —
    /// it accrues in the bucket as a protocol reserve (sign-off Note 3, v1
    /// stub). A future insurance-claim instruction can route it.
    pub fn lp_vault_nav_atoms(
        total_principal_atoms: u128,
        total_earnings_atoms: u128,
        total_earnings_withdrawn_atoms: u128,
        cumulative_loss_atoms: u128,
        cumulative_recovery_atoms: u128,
        fee_share_bps: u16,
    ) -> V16Result<u128> {
        if fee_share_bps as u64 > MAX_MARGIN_BPS {
            return Err(V16Error::InvalidConfig);
        }
        // net impairment = loss - recovery == current unavailable principal (>= 0)
        let net_impairment = cumulative_loss_atoms
            .checked_sub(cumulative_recovery_atoms)
            .ok_or(V16Error::CounterUnderflow)?;
        // available principal cannot go negative; anomaly => fail closed
        let available_principal = total_principal_atoms
            .checked_sub(net_impairment)
            .ok_or(V16Error::CounterUnderflow)?;
        // net earnings = earnings - withdrawn (>= 0 by monotonicity)
        let net_earnings = total_earnings_atoms
            .checked_sub(total_earnings_withdrawn_atoms)
            .ok_or(V16Error::CounterUnderflow)?;
        // LP share of earnings (round DOWN). Remainder is the insurance-side
        // stub (Note 3) — accrues in the bucket, not counted in LP NAV.
        let lp_earnings =
            wide_mul_div_floor_u128(net_earnings, fee_share_bps as u128, MAX_MARGIN_BPS as u128);
        available_principal
            .checked_add(lp_earnings)
            .ok_or(V16Error::ArithmeticOverflow)
    }

    /// BUG-2 / N7 anti-inflation design note: percolator-stake's N7 hardening
    /// (`percolator-stake/src/math.rs`, `percolator-stake/src/state.rs`) pairs
    /// TWO defenses: a `VIRTUAL_SHARES`/`VIRTUAL_ASSETS` offset in the pure
    /// pro-rata math AND a `MINIMUM_LIQUIDITY` dead-share lock applied by the
    /// caller at genesis. This module intentionally carries ONLY the second
    /// one (`percolator-prog::v16_program::handle_deposit_to_lp_vault`
    /// applies `LP_VAULT_MINIMUM_LIQUIDITY` against the genesis deposit) —
    /// stake's own doc calls that the PRIMARY defense, with the virtual-offset
    /// merely defense-in-depth. A virtual-offset variant of
    /// `lp_shares_for_deposit`/`lp_atoms_for_redemption` was prototyped and
    /// REJECTED here: `handle_execute_redemption` (v16_program.rs) computes
    /// `principal_portion` as a SEPARATE, un-offset
    /// `wide_mul_div_floor_u128(shares, available_principal, total_shares)`
    /// call (not routed through `lp_atoms_for_redemption`) so it can split
    /// `atoms` into principal-vs-earnings; offsetting `lp_atoms_for_redemption`
    /// alone desynchronizes the two computations and can make
    /// `principal_portion > atoms_out`, underflowing `earnings_portion =
    /// atoms_out - principal_portion` (a redemption-DoS regression, confirmed
    /// with concrete inputs: shares=500, total_shares=1_000_000, nav=
    /// available_principal=2_000_000 -> atoms_out=999 vs principal_portion=
    /// 1_000). Fixing that would require re-deriving the principal/earnings
    /// split under the offset too, which is out of scope for this fix and
    /// not required — the dead-share lock alone makes genesis-donation
    /// inflation unprofitable. Do not add a virtual-offset here without also
    /// re-deriving `handle_execute_redemption`'s split.
    ///
    /// LP shares to mint for a deposit of `amount` atoms against a vault
    /// with `total_shares` outstanding and `nav_atoms` net asset value
    /// (computed BEFORE this deposit). Round DOWN — the vault keeps any
    /// dust, never over-issues.
    ///
    /// - `total_shares == 0`: fresh vault or drain-epoch reset -> 1:1
    ///   (returns `amount`). Caller guarantees `amount > 0`.
    /// - `total_shares > 0 && nav_atoms == 0`: vault wiped to zero NAV
    ///   while shares still outstanding -> cannot price a deposit; reject.
    /// - otherwise: `floor(amount * total_shares / nav_atoms)`, rejected with
    ///   `LpVaultZeroSharesMinted` if conservative rounding produces zero.
    ///
    /// The zero-share check deliberately lives in this primitive rather than
    /// relying on every wrapper to repeat it: no successful quote may absorb a
    /// deposit without issuing ownership. Callers may retain the same check as
    /// defense in depth.
    pub fn lp_shares_for_deposit(
        amount: u128,
        total_shares: u128,
        nav_atoms: u128,
    ) -> V16Result<u128> {
        if total_shares == 0 {
            return Ok(amount);
        }
        if nav_atoms == 0 {
            return Err(V16Error::InvalidConfig);
        }
        let shares = wide_mul_div_floor_u128(amount, total_shares, nav_atoms);
        if shares == 0 {
            return Err(V16Error::LpVaultZeroSharesMinted);
        }
        Ok(shares)
    }

    /// Collateral atoms to release for redeeming `shares` against a vault
    /// with `total_shares` outstanding and `nav_atoms` NAV. Round DOWN —
    /// the vault keeps any dust so it stays solvent against remaining
    /// shares.
    ///
    /// `floor(shares * nav_atoms / total_shares)`.
    pub fn lp_atoms_for_redemption(
        shares: u128,
        total_shares: u128,
        nav_atoms: u128,
    ) -> V16Result<u128> {
        if total_shares == 0 {
            return Err(V16Error::InvalidConfig);
        }
        if shares > total_shares {
            return Err(V16Error::CounterUnderflow);
        }
        Ok(wide_mul_div_floor_u128(shares, nav_atoms, total_shares))
    }

    /// Split a fee/earnings delta into the LP-side accrual and the
    /// insurance-side remainder. LP side = `floor(delta * fee_share_bps /
    /// 10_000)`; insurance side = `delta - lp_side`.
    ///
    /// In v1 the LP side accrues automatically via NAV (the earnings
    /// counter feeds `lp_vault_nav_atoms`); this helper exists for the
    /// crank's snapshot bookkeeping and for the future insurance-side
    /// routing hook (sign-off Note 3 — insurance routing is a v1 stub).
    pub fn lp_fee_split(delta_atoms: u128, fee_share_bps: u16) -> V16Result<(u128, u128)> {
        if fee_share_bps as u64 > MAX_MARGIN_BPS {
            return Err(V16Error::InvalidConfig);
        }
        let lp_side =
            wide_mul_div_floor_u128(delta_atoms, fee_share_bps as u128, MAX_MARGIN_BPS as u128);
        let insurance_side = delta_atoms
            .checked_sub(lp_side)
            .ok_or(V16Error::CounterUnderflow)?;
        Ok((lp_side, insurance_side))
    }

    /// True iff a queued redemption's cooldown has elapsed:
    /// `current_slot >= request_slot + cooldown_slots` (saturating add).
    /// `cooldown_slots == 0` => always elapsed (immediate redemption).
    pub fn lp_redemption_cooldown_elapsed(
        request_slot: u64,
        current_slot: u64,
        cooldown_slots: u64,
    ) -> bool {
        current_slot >= request_slot.saturating_add(cooldown_slots)
    }
}

// ============================================================================
// fork-port A-4: wrapper-facade aliases for the account-equity / IM family.
// ============================================================================
//
// In the v17 zero-copy/sparse engine, the underlying computations are private
// methods in the ViewMut impl (account_no_positive_credit_equity,
// ensure_initial_margin) or standalone primitives (account_equity_from_parts).
// This module re-lifts them as public aliases under the fork-facade feature so
// the wrapper (Phase 3) can consume them without the old runtime heap types.
//
// All functions take `&PortfolioV16View<'_>` (zero-copy read view) — the v17
// equivalent of the fork's `&PortfolioAccountV16` (deleted heap struct).
//
// Alias naming preserves the v12 public-API surface so downstream wrapper
// callsites can migrate name-by-name in Phase 3 without semantic changes.
#[cfg(feature = "fork-facade")]
pub mod fork_facade {
    use super::{
        account_equity_from_parts, validate_fee_credits, validate_non_min_i128, PortfolioV16View,
        V16Error, V16Result,
    };

    // -----------------------------------------------------------------------
    // Maintenance-margin equity family (full equity: capital + pnl - fee_debt)
    // -----------------------------------------------------------------------

    /// alias for v12 `account_equity_maint_raw`.
    /// Returns `capital + pnl - fee_debt` (clamp-free).
    pub fn account_equity_maint_raw(account: &PortfolioV16View<'_>) -> V16Result<i128> {
        account_equity_from_parts(
            account.header.capital.get(),
            account.header.pnl.get(),
            account.header.fee_credits.get(),
        )
    }

    /// alias for v12 `account_equity_net`.
    /// `max(0, account_equity_maint_raw)` — the clamped MM lane.
    pub fn account_equity_net(account: &PortfolioV16View<'_>) -> V16Result<i128> {
        Ok(account_equity_maint_raw(account)?.max(0))
    }

    // -----------------------------------------------------------------------
    // Initial-margin equity family (IM lane: capital + min(pnl,0) - fee_debt)
    // -----------------------------------------------------------------------

    /// alias for v12 `account_equity_init_raw`.
    /// `capital + min(pnl, 0) - fee_debt` — IM-lane base equity.
    pub fn account_equity_init_raw(account: &PortfolioV16View<'_>) -> V16Result<i128> {
        validate_non_min_i128(account.header.pnl.get())?;
        validate_fee_credits(account.header.fee_credits.get())?;
        let capital = i128::try_from(account.header.capital.get())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        let fee_debt = i128::try_from(account.header.fee_credits.get().unsigned_abs())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        capital
            .checked_add(account.header.pnl.get().min(0))
            .and_then(|v| v.checked_sub(fee_debt))
            .ok_or(V16Error::ArithmeticOverflow)
    }

    /// alias for v12 `account_equity_init_net`.
    /// `max(0, account_equity_init_raw)`.
    pub fn account_equity_init_net(account: &PortfolioV16View<'_>) -> V16Result<i128> {
        Ok(account_equity_init_raw(account)?.max(0))
    }

    /// alias for v12 `account_equity_withdraw_raw`.
    /// Identical to `account_equity_init_raw`; preserved for withdraw-preflight callsites.
    pub fn account_equity_withdraw_raw(account: &PortfolioV16View<'_>) -> V16Result<i128> {
        account_equity_init_raw(account)
    }

    // -----------------------------------------------------------------------
    // Counterfactual trade open equity (IM lane under a pnl override)
    // -----------------------------------------------------------------------

    /// alias for v12 `account_equity_trade_open_raw`.
    /// Counterfactual IM-lane equity recomputed with `pnl_override` in place of
    /// the account's current PnL. Callers pass `account.pnl + candidate_delta`
    /// or any other override. The IM-lane uses `min(pnl_override, 0)`.
    pub fn account_equity_trade_open_raw(
        account: &PortfolioV16View<'_>,
        pnl_override: i128,
    ) -> V16Result<i128> {
        validate_non_min_i128(pnl_override)?;
        validate_fee_credits(account.header.fee_credits.get())?;
        let capital = i128::try_from(account.header.capital.get())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        let fee_debt = i128::try_from(account.header.fee_credits.get().unsigned_abs())
            .map_err(|_| V16Error::ArithmeticOverflow)?;
        capital
            .checked_add(pnl_override.min(0))
            .and_then(|v| v.checked_sub(fee_debt))
            .ok_or(V16Error::ArithmeticOverflow)
    }

    // -----------------------------------------------------------------------
    // IM predicate
    // -----------------------------------------------------------------------

    /// alias for v12 `is_above_initial_margin`.
    /// `true` iff the account's current health certificate is valid AND equity
    /// (certified_equity) covers certified_initial_req.
    pub fn is_above_initial_margin(account: &PortfolioV16View<'_>) -> bool {
        // Inline the frozen ensure_initial_margin body (cert valid + equity >= IM req).
        let Ok(cert) = account.header.health_cert.try_to_runtime() else {
            return false;
        };
        if !cert.valid {
            return false;
        }
        let equity = cert.certified_equity;
        equity >= 0 && (equity as u128) >= cert.certified_initial_req
    }
}

// ============================================================================
// E6 unit tests (finalized-inert close ledger; port of upstream engine c8aab338)
// ============================================================================
//
// `begin_close_progress_ledger` is crate-private, so its non-vacuity coverage
// lives here (in-crate, with access to private items) rather than in the
// `tests/` integration suite, which only sees the public API. The other two
// E6 call sites (the withdraw gate and the empty-account dematerialization
// gate) are both public API and are covered in
// `tests/v16_spec_tests.rs::v16_finalized_zero_residual_close_does_not_block_withdraw`
// and `..._does_not_block_dematerialization`.
#[cfg(test)]
mod e6_finalized_close_inert_tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    fn one_asset_market_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
        let market_group_id = [21u8; 32];
        let cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
        let mut header =
            MarketGroupV16HeaderAccount::new_dynamic(market_group_id, cfg, 1, 0).unwrap();
        let mut markets = vec![Market::new(0u64, EngineAssetSlotV16Account::default())];
        header
            .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 0)
            .unwrap();
        {
            let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            view.validate_shape().unwrap();
        }
        (header, markets)
    }

    fn empty_account_fixture(market_group_id: [u8; 32]) -> PortfolioAccountV16Account {
        let provenance = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
            market_group_id,
            [30u8; 32],
            [31u8; 32],
        ));
        let mut account = PortfolioAccountV16Account::default();
        account.init_empty_in_place(provenance).unwrap();
        account
    }

    // Mirrors `finalized_inert_close_progress` in tests/v16_spec_tests.rs: a close
    // that finished paying out (finalized, zero residual) but is still `active`
    // because the ledger stays active to preserve close identity/history.
    fn finalized_inert_ledger(
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

    // E6, third call site: `begin_close_progress_ledger` (the close-progress-active
    // gate hit while reserving a fresh bankruptcy-close on backing loss) must treat
    // a finalized zero-residual close as inert and allow the *next* close to begin,
    // strictly advancing close_id. Before the fix this unconditionally errored
    // LockActive on any `active` ledger, permanently blocking a second bankruptcy
    // event on an account whose prior close had already finished paying out in
    // full -- stranding the account (and its rent) forever.
    #[test]
    fn finalized_inert_close_allows_next_close_to_begin() {
        let (mut header, mut markets) = one_asset_market_fixture();
        let market_group_id = header.market_group_id;
        let mut account_header = empty_account_fixture(market_group_id);
        let market_id = markets[0].engine.asset.market_id.get();

        account_header.close_progress =
            CloseProgressLedgerV16Account::from_runtime(&finalized_inert_ledger(market_id, 3, 5));

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        account.validate_with_market(&market.as_view()).unwrap();

        market
            .begin_close_progress_ledger(&mut account, 0, SideV16::Long, 7)
            .unwrap();

        let next = account.header.close_progress.try_to_runtime().unwrap();
        assert!(next.active && !next.finalized && !next.canceled);
        assert_eq!(next.close_id, 4);
        assert_eq!(next.gross_loss_at_close_start, 7);
        assert_eq!(next.residual_remaining, 7);
        assert_eq!(
            market.markets[0]
                .engine
                .pending_domain_loss_barrier_long
                .get(),
            1
        );
    }
}

#[cfg(test)]
mod bankruptcy_hlock_clear_predicate_tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    fn one_asset_market_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
        let market_group_id = [22u8; 32];
        let cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
        let mut header =
            MarketGroupV16HeaderAccount::new_dynamic(market_group_id, cfg, 1, 0).unwrap();
        let mut markets = vec![Market::new(0u64, EngineAssetSlotV16Account::default())];
        header
            .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 0)
            .unwrap();
        {
            let view = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            view.validate_shape().unwrap();
        }
        (header, markets)
    }

    fn empty_account_fixture(market_group_id: [u8; 32]) -> PortfolioAccountV16Account {
        let provenance = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
            market_group_id,
            [30u8; 32],
            [31u8; 32],
        ));
        let mut account = PortfolioAccountV16Account::default();
        account.init_empty_in_place(provenance).unwrap();
        account
    }

    // Regression: an open bankruptcy-close ledger with residual (raised via
    // `begin_close_progress_ledger`, the operation `settle_resolved_bankruptcy_negative_pnl`
    // performs immediately before it calls the clear helper) MUST hold the hlock.
    // `pending_domain_loss_barrier_*` is per-asset state the pre-fix predicate did not
    // inspect, so it released the hlock while the residual was still in flight.
    #[test]
    fn hlock_held_while_asset_close_ledger_has_residual() {
        let (mut header, mut markets) = one_asset_market_fixture();
        let market_group_id = header.market_group_id;
        let mut account_header = empty_account_fixture(market_group_id);

        // A bankruptcy / insurance-consumption event engaged the hlock.
        header.bankruptcy_hlock_active = 1;

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let mut account = PortfolioV16ViewMut::new(&mut account_header);
        account.validate_with_market(&market.as_view()).unwrap();

        // Move the bankruptcy residual off the account and onto the asset.
        market
            .begin_close_progress_ledger(&mut account, 0, SideV16::Long, 7)
            .unwrap();

        // Asset-level loss is outstanding (barrier raised), while every group-header
        // counter the pre-fix predicate inspected reads zero.
        assert_eq!(
            market.markets[0]
                .engine
                .pending_domain_loss_barrier_long
                .get(),
            1
        );
        assert_eq!(market.header.negative_pnl_account_count.get(), 0);
        assert_eq!(market.header.stale_certificate_count.get(), 0);
        assert_eq!(market.header.b_stale_account_count.get(), 0);
        assert_eq!(market.header.pnl_pos_tot.get(), 0);
        assert!(market
            .header
            .recovery_reason
            .try_to_runtime()
            .unwrap()
            .is_none());

        assert!(market.group_has_unabsorbed_bankruptcy_loss());
        market.try_clear_bankruptcy_hlock_if_healthy().unwrap();

        assert_eq!(
            market.header.bankruptcy_hlock_active, 1,
            "hlock must stay engaged while a close ledger still has residual"
        );
    }

    // F-03 regression: a REALIZED unallocatable write-off atom must NOT gate the group
    // hlock. In production `kernel_clear_leg` -> `kernel_normalize_social_loss_carry`
    // saturating-adds a whole SOCIAL_LOSS_DEN atom into `explicit_unallocated_loss_*` when a
    // leg clear's `b_rem` crosses an atom with no side weight left to absorb it. That atom
    // is cleared only at asset retirement, and RETIRE rejects asset 0 -- so gating the
    // group-wide hlock on it froze LP/insurance withdrawals and oracle reconfiguration for
    // EVERY domain, permanently. Here the only residual is that write-off (no domain-loss
    // barrier, every header counter zero), so the hlock must clear.
    #[test]
    fn an_unallocatable_write_off_atom_does_not_latch_the_hlock() {
        let (mut header, mut markets) = one_asset_market_fixture();
        // The whole-atom dust a leg clear leaves behind (kernel_normalize_social_loss_carry).
        markets[0].engine.asset.explicit_unallocated_loss_long = V16PodU128::new(1);
        header.bankruptcy_hlock_active = 1;

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

        // No genuine pending loss: no domain-loss barrier on either side.
        assert_eq!(
            market.markets[0].engine.pending_domain_loss_barrier_long.get(),
            0
        );
        assert_eq!(
            market.markets[0].engine.pending_domain_loss_barrier_short.get(),
            0
        );

        assert!(
            !market.group_has_unabsorbed_bankruptcy_loss(),
            "a realized unallocatable write-off must not count as unabsorbed bankruptcy loss (F-03)"
        );
        market.try_clear_bankruptcy_hlock_if_healthy().unwrap();
        assert_eq!(
            market.header.bankruptcy_hlock_active, 0,
            "hlock must clear once the only residual is an unallocatable write-off atom (F-03)"
        );

        // The write-off is still recorded as residual state: the slot is not reusable.
        assert!(
            market.asset_local_has_position_or_loss_state(0).unwrap(),
            "the write-off stays recorded (still blocks slot reactivation), only demoted from a group freeze"
        );
    }

    // Regression: an asset side left in a non-Normal mode (DrainOnly / ResetPending)
    // represents structural impairment mid-resolution, and also covers the social-loss
    // quarantine window (the same `begin_full_drain_reset_inner` that quarantines dust
    // sets mode = ResetPending). It MUST hold the hlock.
    /// A side in DrainOnly must NOT hold the hlock, no matter how much open interest it
    /// still carries.
    ///
    /// This is the anti-hostage property. `bankruptcy_hlock_active` is ONE group-wide byte
    /// which the wrapper consumes to gate WithdrawBackingBucket,
    /// WithdrawBackingBucketEarnings and WithdrawInsuranceAsset. If a side's mode byte
    /// could hold it, a single holder who simply declines to close would freeze LP backing,
    /// LP earnings and insurance for EVERY domain in the group — indefinitely, and for the
    /// price of one position quantum plus min_nonzero_mm_req of equity. Holding is legal
    /// (asset_risk_increase_gate blocks only risk INCREASES), liquidation is deficit-gated
    /// so a solvent holder never qualifies, and no permissionless path can force the close.
    ///
    /// Two earlier revisions of this predicate had that defect: the bare mode term latched
    /// permanently, and the `AND oi_eff != 0` narrowing turned the latch into a hostage.
    /// Neither is present now, and this test is what keeps them out.
    #[test]
    fn a_drain_only_side_never_holds_the_hlock() {
        for oi in [0u128, 1, 5_000] {
            let (mut header, mut markets) = one_asset_market_fixture();
            header.bankruptcy_hlock_active = 1;
            markets[0].engine.asset.mode_long = encode_side_mode(SideModeV16::DrainOnly);
            markets[0].engine.asset.oi_eff_long_q = V16PodU128::new(oi);

            let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
            assert!(
                !market.group_has_unabsorbed_bankruptcy_loss(),
                "a DrainOnly side (oi_eff={oi}) must not gate the hlock — the side mode byte \
                 is user-controlled and this byte is group-wide"
            );
            market.try_clear_bankruptcy_hlock_if_healthy().unwrap();
            assert_eq!(
                market.header.bankruptcy_hlock_active, 0,
                "hlock must release with oi_eff={oi}; anything else is a free, permanent \
                 freeze of every domain's backing"
            );
        }
    }

    /// Same for ResetPending, for completeness — no side mode gates the hlock.
    #[test]
    fn a_reset_pending_side_never_holds_the_hlock() {
        let (mut header, mut markets) = one_asset_market_fixture();
        header.bankruptcy_hlock_active = 1;
        markets[0].engine.asset.mode_long = encode_side_mode(SideModeV16::ResetPending);

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        assert!(!market.group_has_unabsorbed_bankruptcy_loss());
        market.try_clear_bankruptcy_hlock_if_healthy().unwrap();
        assert_eq!(market.header.bankruptcy_hlock_active, 0);
    }

    // Liveness guard (the assertion the over-strict candidate fix failed): after a
    // bankruptcy the hlock MUST still be able to clear on a market that merely has an
    // ordinary open position. `oi_eff_*` / `stored_pos_count_*` / `loss_weight_sum_*`
    // are benign activity, not unabsorbed loss; blocking on them would permanently trap
    // LP/insurance withdrawals (the pre-FIX-1 defect). This test fails under a fix that
    // reuses `asset_local_has_position_or_loss_state`.
    #[test]
    fn hlock_clears_with_open_position_and_no_unabsorbed_loss() {
        let (mut header, mut markets) = one_asset_market_fixture();

        header.bankruptcy_hlock_active = 1;
        // An open position: set the position-presence fields in the shape the engine's
        // own invariant requires them to co-move (oi_eff > 0 => loss_weight_sum > 0 =>
        // stored_pos_count > 0; see validate_shape). No loss fields set.
        markets[0].engine.asset.oi_eff_long_q = V16PodU128::new(1_000);
        markets[0].engine.asset.loss_weight_sum_long = V16PodU128::new(1_000);
        markets[0].engine.asset.stored_pos_count_long = V16PodU64::new(1);

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);

        // The strict "market at rest" predicate correctly reports activity...
        assert!(market.asset_local_has_position_or_loss_state(0).unwrap());
        // ...but there is no UNABSORBED LOSS, so the hlock predicate must not block.
        assert!(!market.group_has_unabsorbed_bankruptcy_loss());

        market.try_clear_bankruptcy_hlock_if_healthy().unwrap();

        assert_eq!(
            market.header.bankruptcy_hlock_active, 0,
            "hlock must clear on a market that only has an ordinary open position"
        );
    }
}

// ============================================================================
// Close-drift scope unit tests (upstream 377de75c "Scope close drift to
// originating asset"). `ensure_open_close_snapshot_current_or_recovery` is
// crate-private, so its negative control lives here with access to it.
// ============================================================================
#[cfg(test)]
mod close_drift_scope_tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    fn two_asset_market_fixture() -> (MarketGroupV16HeaderAccount, Vec<Market<u64>>) {
        let market_group_id = [23u8; 32];
        let cfg = V16Config::public_user_fund_with_market_slots(2, 2, 0, 10);
        let mut header =
            MarketGroupV16HeaderAccount::new_dynamic(market_group_id, cfg, 2, 0).unwrap();
        let mut markets = vec![
            Market::new(0u64, EngineAssetSlotV16Account::default()),
            Market::new(1u64, EngineAssetSlotV16Account::default()),
        ];
        header
            .activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, 100, 1)
            .unwrap();
        header
            .activate_empty_asset_slot_not_atomic(1, &mut markets[1].engine, 100, 2)
            .unwrap();
        (header, markets)
    }

    fn account_with_leg_on_asset_zero(
        market_group_id: [u8; 32],
        asset: AssetStateV16,
    ) -> PortfolioAccountV16Account {
        let provenance = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new(
            market_group_id,
            [32u8; 32],
            [33u8; 32],
        ));
        let mut account = PortfolioAccountV16Account::default();
        account.init_empty_in_place(provenance).unwrap();
        account.legs[0] = PortfolioLegV16Account::from_runtime(&PortfolioLegV16 {
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
        account.active_bitmap[0] = V16PodU64::new(1);
        account
    }

    fn open_ledger_on_asset_zero(
        market_id: u64,
        drift_reference_slot: u64,
    ) -> CloseProgressLedgerV16 {
        CloseProgressLedgerV16 {
            active: true,
            finalized: false,
            canceled: false,
            close_id: 7,
            asset_index: 0,
            market_id,
            domain_side: SideV16::Short,
            gross_loss_at_close_start: 5,
            drift_reference_slot,
            max_close_slot: 0,
            residual_remaining: 5,
            ..CloseProgressLedgerV16::EMPTY
        }
    }

    /// Only the ORIGINATING asset advancing past the close anchor (with the leg
    /// still attached) makes the snapshot stale. An unrelated asset moving the
    /// market-wide clock must not trigger recovery.
    #[test]
    fn unrelated_asset_accrual_does_not_stale_an_open_close() {
        let (mut header, mut markets) = two_asset_market_fixture();
        let asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
        assert_eq!(
            asset0.slot_last, 1,
            "asset 0 anchored at its activation slot"
        );
        // Asset 1 advanced the market-wide clock well past the close anchor.
        header.current_slot = V16PodU64::new(9);
        header.slot_last = V16PodU64::new(9);
        let market_group_id = header.market_group_id;
        let mut account_header = account_with_leg_on_asset_zero(market_group_id, asset0);
        let ledger = open_ledger_on_asset_zero(asset0.market_id, 1);

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let account = PortfolioV16ViewMut::new(&mut account_header);
        let result =
            market.ensure_open_close_snapshot_current_or_recovery(&account.as_view(), ledger);
        assert_eq!(
            result,
            Ok(()),
            "an unrelated asset advancing the global clock must not declare recovery"
        );
        assert_eq!(market.header.mode, 0, "market stays Live");
    }

    /// The originating asset advancing past the anchor while the leg is attached
    /// is stale on both sides of the port.
    #[test]
    fn originating_asset_accrual_stales_an_open_close() {
        let (mut header, mut markets) = two_asset_market_fixture();
        let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
        asset0.slot_last = 9;
        markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);
        header.current_slot = V16PodU64::new(9);
        header.slot_last = V16PodU64::new(9);
        let market_group_id = header.market_group_id;
        let mut account_header = account_with_leg_on_asset_zero(market_group_id, asset0);
        let ledger = open_ledger_on_asset_zero(asset0.market_id, 1);

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let account = PortfolioV16ViewMut::new(&mut account_header);
        let result =
            market.ensure_open_close_snapshot_current_or_recovery(&account.as_view(), ledger);
        assert_eq!(result, Err(V16Error::RecoveryRequired));
        assert_eq!(market.header.mode, 2, "recovery declared");
    }

    /// A detached originating leg never stales the close, whatever the clocks say.
    #[test]
    fn detached_originating_leg_never_stales_an_open_close() {
        let (mut header, mut markets) = two_asset_market_fixture();
        let mut asset0 = markets[0].engine.asset.try_to_runtime().unwrap();
        asset0.slot_last = 9;
        markets[0].engine.asset = AssetStateV16Account::from_runtime(&asset0);
        header.current_slot = V16PodU64::new(9);
        header.slot_last = V16PodU64::new(9);
        let market_group_id = header.market_group_id;
        let mut account_header = account_with_leg_on_asset_zero(market_group_id, asset0);
        account_header.legs[0] = PortfolioLegV16Account::default();
        account_header.active_bitmap[0] = V16PodU64::new(0);
        let ledger = open_ledger_on_asset_zero(asset0.market_id, 1);

        let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
        let account = PortfolioV16ViewMut::new(&mut account_header);
        assert_eq!(
            market.ensure_open_close_snapshot_current_or_recovery(&account.as_view(), ledger),
            Ok(())
        );
        assert_eq!(market.header.mode, 0);
    }
}

#[cfg(test)]
mod margin_rounding_tests {
    // upstream ba7a84b7 "Round margin requirements conservatively" (2026-08-23):
    // mm_req = max(ceil(X * bps / 10_000), min). Under the former floor, splitting
    // one notional across two portfolios lowered the aggregate requirement
    // (2 x 1_311 = 2_622 < 2_623), i.e. fractional-atom collateral credit.
    use super::margin_requirement;
    use proptest::prelude::*;

    #[test]
    fn margin_requirement_partition_regression() {
        let aggregate = margin_requirement(52_470, 500, 1).unwrap();
        let partitioned = margin_requirement(26_235, 500, 1)
            .unwrap()
            .checked_mul(2)
            .unwrap();
        assert_eq!(aggregate, 2_624);
        assert_eq!(partitioned, aggregate);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]

        #[test]
        fn margin_requirement_is_exact_ceiled_with_min(
            notional in 0u128..=u128::MAX / 20_000,
            bps in 0u64..=10_000u64,
            min_req in 0u128..=1_000_000u128,
        ) {
            let req = margin_requirement(notional, bps, min_req).unwrap();
            if notional == 0 {
                prop_assert_eq!(req, 0);
            } else {
                let product = notional * bps as u128;
                let expected = (product / 10_000 + u128::from(product % 10_000 != 0)).max(min_req);
                prop_assert_eq!(req, expected);
            }
        }

        #[test]
        fn margin_requirement_is_conservative_under_partition(
            first in 0u128..=u128::MAX / 40_000,
            second in 0u128..=u128::MAX / 40_000,
            bps in 0u64..=10_000u64,
            min_req in 0u128..=1_000_000u128,
        ) {
            let aggregate = margin_requirement(first + second, bps, min_req).unwrap();
            let partitioned = margin_requirement(first, bps, min_req)
                .unwrap()
                .checked_add(margin_requirement(second, bps, min_req).unwrap())
                .unwrap();
            prop_assert!(
                partitioned >= aggregate,
                "partitioned requirement {} fell below aggregate {}", partitioned, aggregate
            );
        }
    }
}

/// GH#164 tripwire: the ATTACH writer's `oi_eff` contribution must not depend
/// on the attaching side's own `a` scale.
///
/// `validate_asset_shape_for_view` enforces `oi_eff_long_q == oi_eff_short_q`
/// in Live mode, but that check reaches production only through
/// `validate_shape_full_audit_scan`, which is gated
/// `#[cfg(any(test, kani, feature = "audit-scan"))]`. A writer that breaks the
/// equality therefore builds a state the default build commits and the audit
/// build rejects with `InvalidConfig` -- a split invisible to anyone not
/// running the audit feature.
///
/// Existing coverage cannot catch that class of change.
/// `proof_v16_view_trade_position_delta_preserves_oi_symmetry` builds its asset
/// from `AssetStateV16::default()`, so both sides sit at equal `a`, and scaling
/// by equal scales is equality-preserving either way. The divergence needs
/// `a_long != a_short`, which needs a prior one-sided ADL, and nothing else in
/// the suite constructs that state -- which is why the reverted #162 passed CI.
///
/// The fixture below is a genuinely reachable state, not merely a shape-valid
/// one: `fixture_is_reachable_and_audit_clean` asserts the telescoping relation
/// `oi_eff_side == floor(a_side * sum_w_side / SCALE)` holds exactly on both
/// sides, which the shape validator itself never checks.
///
/// These tests pass trivially against the nominal writer. That is the point --
/// they are a tripwire for the next attempt at the `#457` fix, not a claim of a
/// defect in current `main`.
#[cfg(test)]
mod attach_writer_cross_side_oi_tripwire_tests {
    use super::*;

    const CURRENT_SLOT: u64 = 1_000;
    const NEXT_MARKET_ID: u64 = 2;
    const PRICE: u64 = 1_000_000;

    /// A long side scaled down by a prior one-sided ADL. This exact value is
    /// load-bearing: `the_fixture_is_one_where_an_a_scaled_writer_would_diverge`
    /// pins that it is a scale at which an A-scaled contribution rounds apart
    /// from the untouched short side. Most scales do not, so do not reduce this
    /// to a round number without re-checking that test.
    const A_LONG: u128 = 656_160_904_301_049;
    const BALANCED_OI: u128 = 62_275_870;
    const ATTACH_Q: u128 = 8_513_359;

    /// An Active, Live-shaped asset whose sides sit at DIFFERENT `a` scales
    /// with balanced open interest: what a prior one-sided ADL leaves behind.
    /// Each side's weight is derived with the production helper, so the
    /// telescoping relation holds by construction rather than by hand-tuning.
    fn asset_with_asymmetric_a() -> AssetStateV16 {
        let mut asset = AssetStateV16::default();
        asset.market_id = 1;
        asset.lifecycle = AssetLifecycleV16::Active;
        asset.raw_oracle_target_price = PRICE;
        asset.effective_price = PRICE;
        asset.fund_px_last = PRICE;
        asset.slot_last = CURRENT_SLOT;
        asset.a_long = A_LONG;
        asset.a_short = ADL_ONE;
        asset.oi_eff_long_q = BALANCED_OI;
        asset.oi_eff_short_q = BALANCED_OI;
        asset.loss_weight_sum_long = loss_weight_for_basis(BALANCED_OI, A_LONG).unwrap();
        asset.loss_weight_sum_short = loss_weight_for_basis(BALANCED_OI, ADL_ONE).unwrap();
        asset.stored_pos_count_long = 1;
        asset.stored_pos_count_short = 1;
        asset
    }

    fn audit_scan(asset: AssetStateV16) -> V16Result<()> {
        MarketGroupV16View::<u64>::validate_asset_shape_for_view(
            asset,
            MarketModeV16::Live,
            CURRENT_SLOT,
            NEXT_MARKET_ID,
        )
    }

    /// `floor(a * sum_w / SCALE)` -- the aggregate `oi_eff` a side's lazy
    /// indices reconstruct to.
    fn telescoped_oi(a: u128, weight_sum: u128) -> u128 {
        wide_mul_div_floor_u128(a, weight_sum, SOCIAL_WEIGHT_SCALE)
    }

    /// Attach both legs of one fill, weighting each leg the way production
    /// does: normalized against the side's own `a`.
    fn attach_one_fill(asset: &mut AssetStateV16) {
        let (a_long, a_short) = (asset.a_long, asset.a_short);
        let w_long = loss_weight_for_basis(ATTACH_Q, a_long).unwrap();
        let w_short = loss_weight_for_basis(ATTACH_Q, a_short).unwrap();
        add_open_interest_for_new_position(asset, SideV16::Long, ATTACH_Q, w_long).unwrap();
        add_open_interest_for_new_position(asset, SideV16::Short, ATTACH_Q, w_short).unwrap();
    }

    /// The fixture must be a state the engine could actually be in, or every
    /// test below proves nothing. Shape-validity alone is not enough: the
    /// validator never checks the telescoping relation, so a fixture can pass
    /// it while being unreachable.
    #[test]
    fn fixture_is_reachable_and_audit_clean() {
        let asset = asset_with_asymmetric_a();

        assert_ne!(
            asset.a_long, asset.a_short,
            "fixture must be asymmetric or it cannot exercise the divergence"
        );
        assert_eq!(
            telescoped_oi(asset.a_long, asset.loss_weight_sum_long),
            asset.oi_eff_long_q,
            "long side must satisfy oi_eff == floor(a * sum_w / SCALE)"
        );
        assert_eq!(
            telescoped_oi(asset.a_short, asset.loss_weight_sum_short),
            asset.oi_eff_short_q,
            "short side must satisfy oi_eff == floor(a * sum_w / SCALE)"
        );
        audit_scan(asset).expect("asymmetric `a` with balanced OI is a legal Live state");
    }

    /// Why these particular constants. An A-scaled writer computes each side's
    /// contribution as the difference of that side's aggregates; on this
    /// fixture those differ by one atom across the two sides. Most scales round
    /// identically and would make the tripwire vacuous, so this pins that the
    /// chosen fixture genuinely trips.
    ///
    /// This asserts on the formula directly, NOT on the writer, so it holds
    /// whichever writer is in tree.
    #[test]
    fn the_fixture_is_one_where_an_a_scaled_writer_would_diverge() {
        let asset = asset_with_asymmetric_a();
        let contribution = |a: u128, w_before: u128, added: u128| {
            telescoped_oi(a, w_before + added) - telescoped_oi(a, w_before)
        };

        let long = contribution(
            asset.a_long,
            asset.loss_weight_sum_long,
            loss_weight_for_basis(ATTACH_Q, asset.a_long).unwrap(),
        );
        let short = contribution(
            asset.a_short,
            asset.loss_weight_sum_short,
            loss_weight_for_basis(ATTACH_Q, asset.a_short).unwrap(),
        );

        assert_eq!(
            long,
            ATTACH_Q + 1,
            "long side A-scaled contribution rounds up"
        );
        assert_eq!(short, ATTACH_Q, "short side A-scaled contribution is exact");
        assert_ne!(
            long, short,
            "fixture must be one where an A-scaled writer diverges, or this module cannot catch a re-land of #162"
        );
    }

    /// Each side's `oi_eff` grows by exactly the nominal size, with no
    /// dependence on that side's `a`. This is the property the reverted #162
    /// gave up, and what makes the equality below structural not incidental.
    #[test]
    fn attach_contribution_is_independent_of_the_side_a_scale() {
        let before = asset_with_asymmetric_a();
        let mut asset = before;
        attach_one_fill(&mut asset);

        assert_eq!(
            asset.oi_eff_long_q,
            before.oi_eff_long_q + ATTACH_Q,
            "long side oi_eff must grow by the nominal size, not an a-scaled one"
        );
        assert_eq!(
            asset.oi_eff_short_q,
            before.oi_eff_short_q + ATTACH_Q,
            "short side oi_eff must grow by the nominal size, not an a-scaled one"
        );
    }

    /// The Live-mode invariant the audit scanner enforces, asserted at the
    /// writer, on a state where it is not automatic.
    #[test]
    fn attach_onto_asymmetric_a_preserves_cross_side_oi_equality() {
        let mut asset = asset_with_asymmetric_a();
        attach_one_fill(&mut asset);

        assert_eq!(
            asset.oi_eff_long_q, asset.oi_eff_short_q,
            "a fill attaches the same size to both sides, so Live-mode cross-side equality must survive it at any `a` scales"
        );
        audit_scan(asset)
            .expect("the production writer must not build a state the audit scan rejects");
    }

    /// Negative control. Without it, the assertions above would still pass if
    /// the scanner had stopped enforcing the equality. This pins that a
    /// one-atom divergence really is rejected, which is exactly the size of
    /// divergence an A-scaled writer produces here.
    #[test]
    fn audit_scanner_rejects_a_one_atom_cross_side_divergence() {
        let mut asset = asset_with_asymmetric_a();
        attach_one_fill(&mut asset);
        asset.oi_eff_long_q += 1;

        assert!(
            matches!(audit_scan(asset), Err(V16Error::InvalidConfig)),
            "a one-atom cross-side divergence must be rejected in Live mode"
        );
    }

    /// The matched-book symmetry conjunct is gated on asset lifecycle, not market
    /// mode. A single asset in `Recovery` lifecycle inside a still-`Live` market is
    /// transiently asymmetric by design during teardown (`force_asset_recovery`
    /// flips the asset to Recovery while the market stays Live, and forfeit retires
    /// one side's `oi_eff` before the opposite settles). This pins that exemption —
    /// AND that it is scoped to Recovery only, so the Active-asset enforcement the
    /// negative control above relies on is untouched.
    #[test]
    fn recovery_lifecycle_exempts_the_cross_side_oi_symmetry_requirement() {
        // Same one-atom divergence the negative control rejects for an Active asset.
        let mut asset = asset_with_asymmetric_a();
        attach_one_fill(&mut asset);
        asset.oi_eff_long_q += 1;

        // Active: still rejected (the #457 defense the negative control guards).
        assert_eq!(asset.lifecycle, AssetLifecycleV16::Active);
        assert!(
            matches!(audit_scan(asset), Err(V16Error::InvalidConfig)),
            "an Active asset must still be held to the matched-book invariant"
        );

        // Recovery: the identical asymmetry is accepted (intended teardown state).
        asset.lifecycle = AssetLifecycleV16::Recovery;
        audit_scan(asset).expect(
            "a Recovery-lifecycle asset is transiently asymmetric during teardown \
             and must not be flagged by the Live matched-book conjunct",
        );
    }
}
