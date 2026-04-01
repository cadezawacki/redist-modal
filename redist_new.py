"""
Bond Charge Optimization (Delta Space)
=======================================
Decision variables:
    X[side, qt]           - 4 scalars (bucket-level risk-curve delta scaling)
    Y[trader, side, qt]   - M scalars (trader-level shift, inverse-priority weighted)

Per unlocked bond i:
    delta_charge_i  =  X[s,q] * blended_i  −  Y[t,s,q] * inv_priority_i
    final_charge_i  =  starting_charge_i  +  delta_charge_i

    With X=0, Y=0: every bond keeps its starting charge.
    The optimizer only makes incremental adjustments.

    X scales by blended (BSR/illiquid gets LARGER positive deltas)
    Y scales by 1/blended^α (BSI/liquid ABSORBS MORE of reductions)

    kappa_i         = DV01 (SPD) or notional/10_000 (PX)
    sign_i          = +1 (SELL+PX, BUY+SPD), −1 (SELL+SPD, BUY+PX)
    proceeds_i      = sign_i * final_charge_i * kappa_i

liq_alpha controls priority protection strength:
    0.0 → Y is a flat shift (all bonds absorb equally)
    1.0 → Y hits BSI ~50% harder than BSR at liq 10
    2.0 → Y hits BSI ~2.25x harder than BSR at liq 10

Objective:  MAXIMIZE Σ delta_proceeds_i  (equivalent to maximizing total proceeds)
Constraints:
    1. Side band       (total proceeds within ±pct of starting)
    2. Trader band     (trader proceeds near risk-weighted target ± buffer)

"""

from __future__ import annotations
from dataclasses import dataclass, field, asdict
from typing import Any, Dict

import cvxpy as cp
import numpy as np
import polars as pl
from polars import DataFrame, LazyFrame

from app.logs.logging import log

COLUMN_MAP: dict[str, str] = {
    "bond_id": "tnum",
    "trader": "desigName",
    "side": "side",
    "quote_type": "quoteType",
    "ref_mid_px": "_refMidPx",
    "ref_mid_spd": "_refMidSpd",
    "quote_px": "_my_quotePx",
    "quote_spd": "_my_quoteSpd",
    "size": "grossSize",
    "dv01": "grossDv01",
    "liq_score": "avgLiqScore",
    "bsr_notional": "firmBsrSize",
    "bsi_notional": "firmBsinSize",
    "locked": "isLocked",
}


def _c(k: str) -> str:
    return COLUMN_MAP.get(k, None)


_DEFAULT_CHARGE_STRENGTH = {
    ("BSR", "PX"): 0.10,
    ("BSI", "PX"): 0.10,
    ("BSR", "SPD"): 0.20,
    ("BSI", "SPD"): 0.20,
}
_DEFAULT_STRENGTH = 0.20


def add_adjusted_bsr_bsi(df: pl.DataFrame | pl.LazyFrame, clamp_liq=True,
                          charge_strength: dict | None = None,
                          default_strength: float | None = None):

    cs = charge_strength or _DEFAULT_CHARGE_STRENGTH
    ds = default_strength if default_strength is not None else _DEFAULT_STRENGTH

    liq_expr = pl.col(_c('liq_score')).cast(pl.Float64)

    if clamp_liq:
        liq_expr = liq_expr.clip(1.0, 10.0)

    bsr_expr = (
        pl.when(pl.col(_c('quote_type'))==pl.lit("PX")).then(pl.lit(cs.get(('BSR', 'PX'), ds)))
        .when(pl.col(_c('quote_type'))==pl.lit("SPD")).then(pl.lit(cs.get(('BSR', 'SPD'), ds)))
        .otherwise(pl.lit(ds))
        .cast(pl.Float64).alias('_bsr_mult')
    )

    bsi_expr = (
        pl.when(pl.col(_c('quote_type'))==pl.lit("PX")).then(pl.lit(cs.get(('BSI', 'PX'), ds)))
        .when(pl.col(_c('quote_type'))==pl.lit("SPD")).then(pl.lit(cs.get(('BSI', 'SPD'), ds)))
        .otherwise(pl.lit(ds))
        .cast(pl.Float64).alias('_bsi_mult')
    )

    factor_bsr_expr = (pl.lit(1.0) + bsr_expr).pow(pl.lit(11.0) - liq_expr)
    factor_bsi_expr = (pl.lit(1.0) - bsi_expr).pow(pl.lit(11.0) - liq_expr)

    return df.with_columns([
        factor_bsr_expr.alias('rawBsrCharge'),
        factor_bsi_expr.alias('rawBsiCharge'),
        (pl.col(_c('bsr_notional')) / pl.col(_c('size'))).alias('bsrPct'),
        (pl.col(_c('bsi_notional')) / pl.col(_c('size'))).alias('bsiPct')
    ]).with_columns([
        ((pl.col('rawBsrCharge') * pl.col('bsrPct')) + (pl.col('rawBsiCharge') * pl.col('bsiPct'))).alias('blendedCharge')
    ])

SIGN_MAP = {
    ("SELL", "PX"): +1.0, ("SELL", "SPD"): -1.0,
    ("BUY", "PX"): -1.0, ("BUY", "SPD"): +1.0,
}

_SOLVER_KW: dict[str, dict] = {
    "SCS": {"max_iters": 100_000}, "ECOS": {}, "OSQP": {"max_iter": 100_000}, "CLARABEL": {},
}


@dataclass
class OptimizerConfig:
    # ── Side-level constraints ──────────────────────────────────────────
    side_floor_pct: float = 0.95
    """Symmetric band for total proceeds per side. Total must stay within
    [floor × starting, starting / floor].
    Min: 0.50 | Max: 1.00 | Default: 0.95"""

    # ── Trader-band constraints ─────────────────────────────────────────
    buffer_mode: str = 'fixed'
    """How the trader-band buffer is computed. 'fixed' uses buffer_fixed;
    'pct' uses max(|target| × buffer_pct, buffer_min_flat).
    Options: 'fixed', 'pct' | Default: 'fixed'"""

    buffer_fixed: float = 100.0
    """Flat dollar buffer around each trader's target (when buffer_mode='fixed').
    Min: 0 | Max: unbounded | Default: 100.0"""

    buffer_pct: float = 0.05
    """Percentage of |target| used as buffer (when buffer_mode='pct').
    Min: 0.0 | Max: 1.0 | Default: 0.05"""

    buffer_min_flat: float = 100.0
    """Minimum dollar buffer floor when buffer_mode='pct'.
    Min: 0 | Max: unbounded | Default: 100.0"""

    # ── Risk allocation weights ─────────────────────────────────────────
    risk_weights: Dict[str, float] = field(default_factory=dict)
    """Weights for blending risk metrics into each trader's target share.
    Keys: 'NET', 'GROSS', 'NET_BSI', 'GROSS_BSI'. Auto-normalized to sum=1.
    Default: {NET_BSI: 0.50, GROSS_BSI: 0.25, NET: 0.15, GROSS: 0.10}"""

    bsr_risk_share_weight: float = 0.70
    """Weight on the trader's actual BSR risk share when computing the
    BSR-component of the target allocation. Paired with bsr_preference_weight.
    Must satisfy: bsr_risk_share_weight + bsr_preference_weight = 1.0.
    Min: 0.0 | Max: 1.0 | Default: 0.70"""

    bsr_preference_weight: float = 0.30
    """Weight on the BSR preference boost (trader's own BSR%) when computing
    the BSR-component of the target allocation. Higher values give more
    target share to traders with higher BSR percentages, independent of
    their absolute DV01 size.
    Min: 0.0 | Max: 1.0 | Default: 0.30"""

    target_blend: float = 0.50
    """Anchoring blend between risk-weighted target and starting allocation.
    0.0 = keep starting (no redistribution). 1.0 = full risk-weighted target.
    0.5 = halfway. Controls how aggressively the optimizer redistributes
    proceeds across traders.
    Min: 0.0 | Max: 1.0 | Default: 0.50"""

    # ── Objective & penalty ─────────────────────────────────────────────
    linear: bool = False
    """If True, use a linear objective (no penalty term). Faster but allows
    the optimizer to make large per-bond changes with no smoothing cost.
    Default: False"""

    lambda_param: float = 0.25
    """Penalty strength for per-bond charge deviations from starting.
    Higher values keep individual bond charges closer to starting; lower
    values allow more redistribution. Clamped to >= 0.
    Min: 0.0 | Max: unbounded (practical: 0.01–1.0) | Default: 0.25"""

    liq_alpha: float = 1.0
    """Controls how strongly the inverse-priority Y weight protects BSR
    bonds during reductions. Y_reduce weight = blended^(-liq_alpha).
    0.0 = uniform (all bonds absorb equally). 1.0 = BSI absorbs ~50% more.
    2.0 = BSI absorbs ~2.25x more.
    Min: 0.0 | Max: unbounded (practical: 0.0–3.0) | Default: 1.0"""

    skew_stiffness: float = 0.05
    """Extra penalty weight for bonds with large starting charges. Prevents
    the optimizer from collapsing wide skews. Multiplier = 1 + stiffness × |starting_charge|.
    Min: 0.0 | Max: unbounded (practical: 0.0–0.5) | Default: 0.05"""

    skew_asymmetry: float = 0.0
    """Additional penalty that discourages reducing a bond's absolute charge
    below its starting level (penalizes normalization toward zero). Only
    active when > 0.
    Min: 0.0 | Max: unbounded (practical: 0.0–1.0) | Default: 0.0"""

    # ── Charge curve calibration ────────────────────────────────────────
    charge_strength: Dict[tuple, float] = field(default_factory=dict)
    """Per-(BSR/BSI, PX/SPD) exponential base rates for the blended charge
    curve. Controls how steeply the charge increases with illiquidity.
    Default: {(BSR,PX): 0.10, (BSI,PX): 0.10, (BSR,SPD): 0.20, (BSI,SPD): 0.20}"""

    default_strength: float | None = None
    """Fallback charge strength if a (BSR/BSI, qt) key is missing from
    charge_strength. None uses _DEFAULT_STRENGTH (0.20).
    Min: 0.0 | Max: 1.0 | Default: None (→ 0.20)"""

    # ── Skew delta caps ─────────────────────────────────────────────────
    max_spread_skew_delta: float | None = None
    """Maximum allowed weighted-average skew change per bucket for SPD bonds.
    None = disabled. Units: spread bps × total kappa.
    Min: 0.0 | Max: unbounded | Default: None (disabled)"""

    max_px_skew_delta: float | None = None
    """Maximum allowed weighted-average skew change per bucket for PX bonds.
    None = disabled. Units: price points × total kappa.
    Min: 0.0 | Max: unbounded | Default: None (disabled)"""

    max_individual_spread_skew_delta: float | None = None
    """Maximum per-bond skew change for SPD bonds. None = disabled.
    Units: spread bps.
    Min: 0.0 | Max: unbounded | Default: None (disabled)"""

    max_individual_px_skew_delta: float | None = None
    """Maximum per-bond skew change for PX bonds. None = disabled.
    Units: price points (converted to bps internally via ×100).
    Min: 0.0 | Max: unbounded | Default: None (disabled)"""

    # ── Behavioral flags ────────────────────────────────────────────────
    allow_through_mid: bool = True
    """If False, constrains each bond's final charge to stay on the same
    side of mid as its starting charge (no sign flip). If True, the
    optimizer may push charges through mid for better PnL.
    Default: True"""

    isolate_traders: bool = False
    """If True, solves each trader independently (no cross-trader
    redistribution). Useful for debugging individual trader behavior.
    Default: False"""

    auto_relax: bool = True
    """If True, automatically widens trader-band buffers (2x, 4x) on
    infeasibility before giving up. Prevents hard failures on tight configs.
    Default: True"""

    debug: bool = True
    """Enables debug logging (solver status, skew changes, risk_pct
    validation, auto-relax warnings).
    Default: True"""

    # ── Grouping ────────────────────────────────────────────────────────
    group_columns: list[str] | None = None
    """Alternative grouping columns to use instead of the default trader
    column ('desigName'). When set, a composite key is built from these
    columns. None = group by trader.
    Default: None"""

    # ── Solver ──────────────────────────────────────────────────────────
    solver: str = "SCS"
    """Primary CVXPY solver. Falls back through [SCS, ECOS, CLARABEL].
    Options: 'SCS', 'ECOS', 'OSQP', 'CLARABEL' | Default: 'SCS'"""

    solver_verbose: bool = False
    """Pass verbose=True to the solver for iteration-level output.
    Default: False"""

    normalize_objective_by_bucket: bool|int = True
    """If True, normalizes each bucket's contribution to the objective by
    its starting proceeds magnitude, preventing large buckets from
    dominating. Uses an adaptive floor (10th percentile).
    Default: True"""

    objective_norm_floor: float = 1.0
    """Minimum denominator for bucket normalization. Prevents division by
    near-zero starting proceeds.
    Min: 0.01 | Max: unbounded | Default: 1.0"""

    def __post_init__(self):
        if not self.risk_weights:
            self.risk_weights = {
                "NET_BSI": 0.5,
                "GROSS_BSI": 0.25,
                "NET": 0.15,
                "GROSS": 0.1
            }
        tlt = sum(self.risk_weights.values())
        if tlt and (tlt != 1):
            for k, v in self.risk_weights.items():
                self.risk_weights[k] = v / tlt
        self.lambda_param = max(0.0, self.lambda_param)
        if not self.charge_strength:
            self.charge_strength = dict(_DEFAULT_CHARGE_STRENGTH)

        # Normalize BSR blend weights to sum to 1.0
        bsr_total = self.bsr_risk_share_weight + self.bsr_preference_weight
        if bsr_total > 0 and abs(bsr_total - 1.0) > 1e-6:
            self.bsr_risk_share_weight /= bsr_total
            self.bsr_preference_weight /= bsr_total


def _parse_num(s) -> float:
    return float(s.replace(",", "").strip()) if isinstance(s, str) else float(s)

def _derive_skew(qt, ref_mid_px, ref_mid_spd, quote_px, quote_spd):
    N = len(qt)
    skews = np.zeros(N)
    for i in range(N):
        if qt[i]=="SPD":
            skews[i] = quote_spd[i] - ref_mid_spd[i]
        else:
            skews[i] = quote_px[i] - ref_mid_px[i]
    return skews


def _derive_dv01(qt, size, ref_mid_px, ref_mid_spd, quote_px, quote_spd):
    N = len(qt)
    dv01 = np.zeros(N)
    for i in range(N):
        d_spd = quote_spd[i] - ref_mid_spd[i]
        d_px = quote_px[i] - ref_mid_px[i]
        if abs(d_spd) < 1e-8:
            dv01[i] = 0.08 * size[i] / 100.0
        else:
            dv01[i] = abs(d_px / d_spd) * size[i] / 100.0
    return dv01


def _compute_kappa(qt, size, dv01):
    """k = DV01 for SPD, size/100/100 for PX."""
    return np.array([dv01[i] if qt[i]=="SPD" else size[i] / 10_000.0 for i in range(len(qt))])


def _compute_trader_risk(side, dv01, liq, mid_spd):
    return np.array([
        (1.0 if side[i]=="BUY" else -1.0) * dv01[i] * (np.sqrt(11) - np.sqrt(liq[i])) * mid_spd[i] / 100.0
        for i in range(len(side))
    ])


def _sort_dict(d):
    return {key: d[key] for key in sorted(d)}


@dataclass
class OptimizationResult:
    status: str
    optimal: bool
    objective_value: float
    X_values: dict[tuple[str, str], float]
    Y_values: dict[tuple[str, str, str], float]
    final_charges: np.ndarray
    final_proceeds: np.ndarray
    starting_proceeds_by_side: dict[str, float]
    final_proceeds_by_side: dict[str, float]
    risk_pct: dict[tuple[str, str, str], float]


PX_SOURCES = ['_refMidPx', 'bvalMidPx', 'macpMidPx', 'amMidPx', 'traceMidPx', 'cbbtMidPx']
SPD_SOURCES = ['_refMidSpd', 'bvalMidSpd', 'macpMidSpd', 'amMidSpd', 'traceMidSpd', 'cbbtMidSpd']
MY_PX_SOURCE_BID = ['newLevelPx', '_refBidPx','bvalBidPx', 'macpBidPx', 'amBidPx', 'traceBidPx', 'cbbtBidPx']
MY_PX_SOURCE_ASK = ['newLevelPx', '_refAskPx','bvalAskPx', 'macpAskPx', 'amAskPx', 'traceAskPx', 'cbbtAskPx']
MY_SPD_SOURCE_BID = ['newLevelSpd', '_refBidSpd','bvalBidSpd', 'macpBidSpd', 'amBidSpd', 'traceBidSpd', 'cbbtBidSpd']
MY_SPD_SOURCE_ASK = ['newLevelSpd', '_refAskSpd','bvalAskSpd', 'macpAskSpd', 'amAskSpd', 'traceAskSpd', 'cbbtAskSpd']

IS_SPREAD = pl.col(_c('quote_type'))=='SPD'
IS_PX = pl.col(_c('quote_type'))=='PX'
IS_BUY = pl.col(_c('side'))=='BUY'
IS_SELL = pl.col(_c('side'))=='SELL'

_GROUP_KEY_COL = '_group_key'
_GROUP_SEP = '|||'

def _resolve_inner_col(cfg: OptimizerConfig) -> tuple[str, list[str] | None]:
    """Return (inner_column_name, original_group_columns_or_None).
    When group_columns is set, the inner column is '_group_key' (a composite).
    Otherwise falls back to the standard 'desigName' trader column."""
    gc = getattr(cfg, 'group_columns', None)
    if gc and isinstance(gc, list) and len(gc) > 0:
        return _GROUP_KEY_COL, gc
    return _c('trader'), None


def _add_group_key_column(df, group_cols: list[str]):
    """Add a composite _group_key column by concatenating group_cols with a separator."""
    if len(group_cols) == 1:
        return df.with_columns(pl.col(group_cols[0]).cast(pl.Utf8).fill_null('MISSING').alias(_GROUP_KEY_COL))
    parts = [pl.col(c).cast(pl.Utf8).fill_null('MISSING') for c in group_cols]
    expr = parts[0]
    for p in parts[1:]:
        expr = expr + pl.lit(_GROUP_SEP) + p
    return df.with_columns(expr.alias(_GROUP_KEY_COL))


def _parse_group_key(key: str, group_cols: list[str]) -> dict[str, str]:
    """Parse a composite key back into individual column values."""
    parts = key.split(_GROUP_SEP)
    result = {}
    for i, col in enumerate(group_cols):
        result[col] = parts[i] if i < len(parts) else 'MISSING'
    return result

def solve(df: pl.DataFrame, cfg: OptimizerConfig | None = None, name=None):
    df = df.lazy() if isinstance(df, pl.DataFrame) else df
    cfg = cfg or OptimizerConfig()

    print(asdict(cfg))

    inner_col, orig_group_cols = _resolve_inner_col(cfg)

    if cfg.isolate_traders:
        return _solve_isolated(df, cfg)

    removed_ids = {}

    for _id in df.filter(pl.col('isReal')==0).hyper.ul(_c('bond_id')):
        removed_ids[_id] = 'Bond removed from portfolio'
    df = df.filter(pl.col('isReal')==1)

    for _id in df.filter(~pl.col(_c("quote_type")).is_in(['PX', 'SPD'])).hyper.ul(_c('bond_id')):
        removed_ids[_id] = 'Quote Type not supported'
    df = df.filter(pl.col(_c("quote_type")).is_in(['PX', 'SPD']))

    s = df.hyper.schema()
    px_sources = [col for col in PX_SOURCES if col in s]
    spd_sources = [col for col in SPD_SOURCES if col in s]

    my_px_source_bid = [col for col in MY_PX_SOURCE_BID if col in s]
    my_px_source_ask = [col for col in MY_PX_SOURCE_ASK if col in s]
    my_spd_source_bid = [col for col in MY_SPD_SOURCE_BID if col in s]
    my_spd_source_ask = [col for col in MY_SPD_SOURCE_ASK if col in s]

    df = df.with_columns(
        [
            pl.when(IS_BUY).then(pl.coalesce(my_px_source_bid))
            .otherwise(pl.coalesce(my_px_source_ask)).alias('_my_quotePx'),
            pl.when(IS_BUY).then(pl.coalesce(my_spd_source_bid))
            .otherwise(pl.coalesce(my_spd_source_ask)).alias('_my_quoteSpd')
        ]
    )

    df = df.with_columns(
        [
            (pl.col('_my_quoteSpd') - pl.col('_refMidSpd')).alias('skewSpd'),
            (pl.col('_my_quotePx') - pl.col('_refMidPx')).alias('skewPx'),
        ]
    ).with_columns(
        [
            pl.when(IS_SPREAD).then(pl.col('skewSpd')).otherwise(pl.col('skewPx')).alias('skew')
        ]
    )

    df = add_adjusted_bsr_bsi(df, clamp_liq=True,
                              charge_strength=cfg.charge_strength,
                              default_strength=cfg.default_strength)

    df = df.with_columns(
        [
            pl.when(IS_SPREAD).then(pl.col(_c('dv01'))).otherwise(pl.col(_c('size')) / 10_000).alias('kappa'),
            pl.when(IS_PX & IS_SELL).then(pl.lit(1))
            .when(IS_SPREAD & IS_SELL).then(pl.lit(-1))
            .when(IS_PX & IS_BUY).then(pl.lit(-1))
            .when(IS_SPREAD & IS_BUY).then(pl.lit(1)).alias('quoteSign'),

            pl.when(IS_BUY).then(pl.lit(1)).otherwise(pl.lit(-1)).alias('sideSign'),

            pl.when(IS_SPREAD & IS_SELL).then((pl.col('_refMidSpd') - pl.col('_my_quoteSpd')) * pl.col(_c('dv01')))
            .when(IS_SPREAD & IS_BUY).then((pl.col('_my_quoteSpd') - pl.col('_refMidSpd')) * pl.col(_c('dv01')))
            .when(IS_PX & IS_SELL).then((pl.col('_my_quotePx') - pl.col('_refMidPx')) * pl.col(_c('size')) / 100)
            .when(IS_PX & IS_BUY).then((pl.col('_refMidPx') - pl.col('_my_quotePx')) * pl.col(_c('size')) / 100)
            .alias('skewProceeds'),

            (
                    pl.when(pl.col(_c('side'))=='BUY')
                    .then(pl.lit(1))
                    .otherwise(pl.lit(-1)) *
                    pl.col(_c('dv01')) *
                    (pl.lit(11).sqrt() - pl.col(_c('liq_score')).sqrt()) *
                    pl.col(_c('ref_mid_spd')) / 100
            ).alias('trader_risk')

        ]
    )

    for _id in df.filter(pl.col('trader_risk').is_null()).hyper.ul(_c('bond_id')):
        removed_ids[_id] = "Insuffient data"
    df = df.filter(pl.col('trader_risk').is_not_null())

    if orig_group_cols is not None:
        df = _add_group_key_column(df, orig_group_cols)

    df = df.with_columns(
        [
            (pl.col('trader_risk')).alias('trader_net'),
            (pl.col('trader_risk').abs()).alias('trader_gross'),
            (pl.col('trader_risk') * pl.col('bsrPct')).abs().alias('trader_bsr_gross'),
            (pl.col('trader_risk') * pl.col('bsrPct')).alias('trader_bsr'),
            (pl.col('trader_risk') * pl.col('bsiPct')).abs().alias('trader_bsi_gross'),
            (pl.col('trader_risk') * pl.col('bsiPct')).alias('trader_bsi'),
        ]
    )

    N = df.hyper.height()
    if N==0:
        return pl.DataFrame(), {"status": 'FAILED'}, pl.DataFrame(), pl.DataFrame(), removed_ids

    agg_dimenstion = ["quoteType", "side"]
    trader_agg = df.group_by([inner_col] + agg_dimenstion).agg(
        [
            pl.col("trader_net").abs().sum().alias('trader_net_sum'),
            pl.col("trader_gross").abs().sum().alias('trader_gross_sum'),
            pl.col("trader_bsr_gross").abs().sum().alias('trader_bsr_gross_sum'),
            pl.col("trader_bsr").sum().alias('trader_bsr_sum'),
            pl.col("trader_bsi_gross").abs().sum().alias('trader_bsi_gross_sum'),
            pl.col("trader_bsi").sum().alias('trader_bsi_sum'),
            pl.col('skewProceeds').sum().alias('skewProceeds_sum'),
            (pl.col('skewProceeds') * (pl.col('isLocked'))).sum().alias('currentLocked_sum'),
            (pl.col('isLocked').sum() / pl.col('isLocked').count()).alias('pctLocked')
        ]
    ).with_columns(
        [
            pl.col("trader_net_sum").abs().sum().over(agg_dimenstion).alias('net_over_trader_qt'),
            pl.col("trader_gross_sum").abs().sum().over(agg_dimenstion).alias('gross_over_trader_qt'),
            pl.col("trader_bsr_sum").abs().sum().over(agg_dimenstion).alias('net_bsr_over_trader_qt'),
            pl.col("trader_bsr_gross_sum").abs().sum().over(agg_dimenstion).alias('gross_bsr_over_trader_qt'),
            pl.col("trader_bsi_sum").abs().sum().over(agg_dimenstion).alias('net_bsi_over_trader_qt'),
            pl.col("trader_bsi_gross_sum").abs().sum().over(agg_dimenstion).alias('gross_bsi_over_trader_qt'),
        ]
    ).with_columns(
        [
            pl.when(pl.col('net_over_trader_qt').fill_null(0) > 0).then(
                pl.lit(cfg.risk_weights.get('NET', 0), pl.Float64)
                ).otherwise(pl.lit(0, pl.Float64)).alias('net_weight'),
            pl.when(pl.col('gross_over_trader_qt').fill_null(0) > 0).then(
                pl.lit(cfg.risk_weights.get('GROSS', 0), pl.Float64)
                ).otherwise(pl.lit(0, pl.Float64)).alias('gross_weight'),
            pl.when(pl.col('net_bsi_over_trader_qt').fill_null(0) > 0).then(
                pl.lit(cfg.risk_weights.get('NET_BSI', 0), pl.Float64)
                ).otherwise(pl.lit(0, pl.Float64)).alias('net_bsi_weight'),
            pl.when(pl.col('gross_bsi_over_trader_qt').fill_null(0) > 0).then(
                pl.lit(cfg.risk_weights.get('GROSS_BSI', 0), pl.Float64)
                ).otherwise(pl.lit(0, pl.Float64)).alias('gross_bsi_weight')
        ]
    ).with_columns(
        [
            (pl.col('net_weight') + pl.col('gross_weight') + pl.col('net_bsi_weight') + pl.col('gross_bsi_weight')).alias('_total_weight')
        ]
    ).with_columns(
        [
            (pl.col('net_weight') / pl.col('_total_weight')).alias('net_weight'),
            (pl.col('gross_weight') / pl.col('_total_weight')).alias('gross_weight'),
            (pl.col('net_bsi_weight') / pl.col('_total_weight')).alias('net_bsi_weight'),
            (pl.col('gross_bsi_weight') / pl.col('_total_weight')).alias('gross_bsi_weight'),
        ]
    ).with_columns(
        [
            ((pl.col("trader_net_sum").abs()) / (pl.col('net_over_trader_qt'))).fill_nan(0).alias('net_size_pct'),
            ((pl.col("trader_gross_sum").abs()) / (pl.col('gross_over_trader_qt'))).fill_nan(0).alias('gross_size_pct'),
            ((pl.col("trader_bsr_sum").abs()) / (pl.col('net_bsr_over_trader_qt'))).fill_nan(0).alias('bsr_size_pct'),
            ((pl.col("trader_bsr_gross_sum").abs()) / (pl.col('gross_bsr_over_trader_qt'))).fill_nan(0).alias(
                'bsr_gross_size_pct'
                ),
            ((pl.col("trader_bsi_sum").abs()) / (pl.col('net_bsi_over_trader_qt'))).fill_nan(0).alias('bsi_size_pct'),
            ((pl.col("trader_bsi_gross_sum").abs()) / (pl.col('gross_bsi_over_trader_qt'))).fill_nan(0).alias(
                'bsi_gross_size_pct'
                ),
            (pl.col("skewProceeds_sum").sum().over(agg_dimenstion)).fill_nan(0).alias('skewProceeds_sum_sum'),
            (pl.col("currentLocked_sum").sum().over(agg_dimenstion)).fill_nan(0).alias('currentLocked_sum_sum'),
            pl.when(pl.col('pctLocked')==1).then(pl.lit(1, pl.Int8)).otherwise(pl.lit(0, pl.Int8)).alias(
                'isFullyLocked'
                )
        ]
    ).with_columns(
        [
            # FIX: Use the trader's OWN BSR percentage as preference, not (1 - bsi_share_of_total).
            # Old formula: (1 - bsi_size_pct) confused "small trader" with "high BSR trader".
            # A trader with 0% BSR but tiny DV01 would get MAX preference — completely wrong.
            # New: preference = trader's BSR% of their own book, from the aggregation.
            (pl.col('trader_bsr_gross_sum') / (pl.col('trader_bsr_gross_sum') + pl.col('trader_bsi_gross_sum')))
                .fill_null(0).fill_nan(0).clip(0.0, 1.0).alias('_own_bsr_pct'),
        ]
    ).with_columns(
        [
            # Normalize own BSR% to a share across traders within each (side, qt) bucket
            (pl.col('_own_bsr_pct') / pl.col('_own_bsr_pct').sum().over(agg_dimenstion)).fill_nan(0).alias('bsr_pref_size_pct'),
            (pl.col('_own_bsr_pct') / pl.col('_own_bsr_pct').sum().over(agg_dimenstion)).fill_nan(0).alias('bsr_pref_gross_size_pct'),
        ]
    ).with_columns(
        [
            (pl.lit(cfg.bsr_risk_share_weight) * pl.col('bsr_size_pct') + pl.lit(cfg.bsr_preference_weight) * pl.col('bsr_pref_size_pct')).alias('bsr_target_size_pct'),
            (pl.lit(cfg.bsr_risk_share_weight) * pl.col('bsr_gross_size_pct') + pl.lit(cfg.bsr_preference_weight) * pl.col('bsr_pref_gross_size_pct')).alias('bsr_target_gross_size_pct'),
        ]
    ).with_columns(
        [
            (pl.col('net_size_pct') * pl.col('net_weight') + pl.col('gross_size_pct') * pl.col('gross_weight') + pl.col('bsr_target_size_pct') * pl.col('net_bsi_weight') + pl.col('bsr_target_gross_size_pct') * pl.col('gross_bsi_weight')).alias('wavg_pct_by_side_qt')
        ]
    ).with_columns(
        [
            # Blend between risk-weighted target and starting allocation.
            # target_blend=0: keep starting. target_blend=1: full risk reallocation.
            (
                pl.lit(cfg.target_blend) * (pl.col('wavg_pct_by_side_qt') * pl.col('skewProceeds_sum_sum'))
                + pl.lit(1.0 - cfg.target_blend) * pl.col('skewProceeds_sum')
            ).alias('expected_proceeds')
        ]
    )

    # Extract per-trader risk_pct for output columns
    _risk_pct_map_raw = trader_agg.select(
        pl.concat_arr([pl.col(inner_col), pl.col(_c('side')), pl.col(_c('quote_type'))]).alias('_key'),
        pl.col('wavg_pct_by_side_qt')
    ).collect().hyper.to_map('_key', 'wavg_pct_by_side_qt')
    _risk_pct_for_bonds = {
        tuple(k) if isinstance(k, (list, np.ndarray)) else k: v
        for k, v in (_risk_pct_map_raw or {}).items()
    }

    sides = df.hyper.to_list(_c('side'))
    qts = df.hyper.to_list(_c('quote_type'))
    inner_vals = df.hyper.to_list(inner_col)
    locked = df.select(pl.col('isLocked').cast(pl.Boolean, strict=False)).collect().to_series().to_numpy()
    skew = df.select(pl.col('skew').cast(pl.Float64, strict=False)).collect().to_series().to_numpy()
    kappa = df.select(pl.col('kappa').cast(pl.Float64, strict=False)).collect().to_series().to_numpy()
    signs = df.select(pl.col('quoteSign').cast(pl.Int8, strict=False)).collect().to_series().to_numpy()
    dv01_arr = df.select(pl.col(_c('dv01')).cast(pl.Float64, strict=False)).collect().to_series().to_numpy()

    bucket_keys_s: set[tuple[str, str]] = set()
    tbk_keys_s: set[tuple[str, str, str]] = set()
    bond_bk: list[tuple[str, str]] = []
    bond_tbk: list[tuple[str, str, str]] = []
    for i in range(N):
        bk = (sides[i], qts[i])
        tbk = (inner_vals[i] or 'MISSING', sides[i], qts[i])
        bucket_keys_s.add(bk)
        tbk_keys_s.add(tbk)
        bond_bk.append(bk)
        bond_tbk.append(tbk)

    bucket_keys = sorted(bucket_keys_s)
    tbk_keys = sorted(tbk_keys_s)
    bk_idx = {bk: j for j, bk in enumerate(bucket_keys)}
    tbk_idx = {tbk: j for j, tbk in enumerate(tbk_keys)}
    n_bk, n_tbk = len(bucket_keys), len(tbk_keys)

    # Per-bond risk_pct: distribute each trader's bucket share across their
    # individual bonds proportionally by |trader_risk|.
    # Result sums to 1.0 per (side, qt) bucket.
    try:
        trader_risk_abs = df.select(pl.col('trader_risk').abs().cast(pl.Float64)).collect().to_series().to_numpy()
        tbk_risk_totals: dict[tuple, float] = {}
        for i in range(N):
            tbk = bond_tbk[i]
            tbk_risk_totals[tbk] = tbk_risk_totals.get(tbk, 0.0) + trader_risk_abs[i]
        bond_risk_pct = np.array([
            _risk_pct_for_bonds.get(bond_tbk[i], 0.0)
            * (trader_risk_abs[i] / tbk_risk_totals[bond_tbk[i]] if tbk_risk_totals.get(bond_tbk[i], 0) > 1e-12 else 0.0)
            for i in range(N)
        ])
    except Exception:
        bond_risk_pct = np.zeros(N)

    unlocked = ~locked
    ul_idx = np.where(unlocked)[0]
    lk_idx = np.where(locked)[0]
    n_ul = len(ul_idx)
    u_sides = df.hyper.ul(_c('side'))

    proceeds = df.select('skewProceeds').collect().to_series().to_numpy()
    is_px = np.array([q=="PX" for q in qts])
    starting_charge_bps = np.where(is_px, skew * 100.0, skew)

    start_by_side: dict[str, float] = {}
    for s in u_sides:
        m = np.array([sides[i]==s for i in range(N)])
        start_by_side[s] = float(np.sum(proceeds[m]))

    start_charge_by_bk: dict[tuple[str, str], float] = {}
    for bk in bucket_keys:
        m = np.array([bond_bk[i]==bk for i in range(N)])
        start_charge_by_bk[bk] = float(np.sum(signs[m] * starting_charge_bps[m] * kappa[m]))

    X = cp.Variable(n_bk, name="X")
    # Split Y into two non-negative variables with direction-appropriate weights:
    #   Y_add >= 0: when adding PnL to a trader, scales by BLENDED (BSR gets MORE additions)
    #   Y_reduce >= 0: when reducing PnL, scales by INV_BLENDED (BSI absorbs MORE reductions)
    # The optimizer naturally uses one or the other per trader (using both would cancel out).
    Y_add = cp.Variable(n_tbk, name="Y_add", nonneg=True)
    Y_reduce = cp.Variable(n_tbk, name="Y_reduce", nonneg=True)

    blended_raw = df.select('blendedCharge').cast(pl.Float64, strict=False).collect().to_series().to_numpy()

    # X and Y_add scale by blended (priority-proportional)
    # Y_reduce scales by inverse-blended (inverse-priority)
    safe_blended = np.clip(blended_raw, 0.01, None)
    inv_weight = safe_blended ** (-cfg.liq_alpha)

    A_X = np.zeros((n_ul, n_bk))
    A_Ya = np.zeros((n_ul, n_tbk))   # Y_add: positive contribution, blended weight
    A_Yr = np.zeros((n_ul, n_tbk))   # Y_reduce: negative contribution, inv weight

    for j, i in enumerate(ul_idx):
        A_X[j, bk_idx[bond_bk[i]]] = signs[i] * kappa[i] * blended_raw[i]
        A_Ya[j, tbk_idx[bond_tbk[i]]] = signs[i] * kappa[i] * blended_raw[i]     # same shape as X
        A_Yr[j, tbk_idx[bond_tbk[i]]] = -signs[i] * kappa[i] * inv_weight[i]     # inverse priority

    # DELTA SPACE: A_X @ X + A_Ya @ Y_add + A_Yr @ Y_reduce = delta proceeds.
    # Total proceeds = starting_proceeds + delta_proceeds.
    # With X=0, Y_add=0, Y_reduce=0: every bond keeps its starting charge.
    ul_delta_proceeds = A_X @ X + A_Ya @ Y_add + A_Yr @ Y_reduce
    ul_starting_total = float(np.sum(proceeds[ul_idx]))
    locked_total = float(np.sum(proceeds[lk_idx])) if len(lk_idx) else 0.0

    # Objective: maximize total = starting + delta (starting is constant, so maximize delta)
    normalized_pnl_expr = cp.sum(ul_delta_proceeds)  # only delta matters for objective
    if getattr(cfg, "normalize_objective_by_bucket", True):
        norm_terms = []
        cfg_norm_floor = float(getattr(cfg, "objective_norm_floor", 1.0))
        # FIX #9: Adaptive floor — use 10th percentile of bucket sizes so tiny buckets
        # don't dominate the objective with disproportionate weight.
        all_abs_bk = [abs(start_charge_by_bk.get(bk, 0.0)) for bk in bucket_keys]
        nonzero_abs = [v for v in all_abs_bk if v > 0]
        norm_floor = max(cfg_norm_floor, float(np.percentile(nonzero_abs, 10)) if nonzero_abs else cfg_norm_floor)
        for bk in bucket_keys:
            ul_mask = np.array([bond_bk[ul_idx[j]]==bk for j in range(n_ul)])
            lk_bk = [i for i in lk_idx if bond_bk[i]==bk]
            lk_chg = float(np.sum(proceeds[lk_bk])) if lk_bk else 0.0
            ul_start_bk = float(np.sum(proceeds[ul_idx[ul_mask]])) if ul_mask.any() else 0.0
            # Total bucket proceeds = starting(unlocked) + delta(unlocked) + locked
            bk_delta_expr = (
                (A_X[ul_mask].sum(0) if ul_mask.any() else np.zeros(n_bk)) @ X
                + (A_Ya[ul_mask].sum(0) if ul_mask.any() else np.zeros(n_tbk)) @ Y_add
                + (A_Yr[ul_mask].sum(0) if ul_mask.any() else np.zeros(n_tbk)) @ Y_reduce
            )
            bk_total_expr = ul_start_bk + bk_delta_expr + lk_chg
            denom = max(abs(start_charge_by_bk.get(bk, 0.0)), norm_floor)
            norm_terms.append(bk_total_expr / denom)
        if norm_terms:
            normalized_pnl_expr = cp.sum(cp.hstack(norm_terms))

    # In delta space, X=0 means no change. Mild regularization for stability.
    x_regularization = 0.001 * cp.sum_squares(X)

    if cfg.linear:
        objective = cp.Maximize(normalized_pnl_expr - x_regularization)
    else:
        deviation = []
        for j, i in enumerate(ul_idx):
            # In delta space, fc IS the change from starting. Penalize large changes.
            fc = X[bk_idx[bond_bk[i]]] * blended_raw[i] + Y_add[tbk_idx[bond_tbk[i]]] * blended_raw[i] - Y_reduce[tbk_idx[bond_tbk[i]]] * inv_weight[i]
            deviation.append(cp.abs(fc))
        dev = cp.hstack(deviation)
        l = cfg.lambda_param
        if l is None: l = 0

        stiffness_weights = np.ones(n_ul)
        if cfg.skew_stiffness > 0:
            stiffness_weights = 1.0 + cfg.skew_stiffness * np.abs(starting_charge_bps[ul_idx])

        base_penalty = l * cp.sum(cp.multiply(kappa[ul_idx] * stiffness_weights, cp.square(dev)))

        asym_penalty = 0.0
        if cfg.skew_asymmetry > 0:
            abs_start = np.abs(starting_charge_bps[ul_idx])
            fc_terms = []
            for j, i in enumerate(ul_idx):
                fc = X[bk_idx[bond_bk[i]]] * blended_raw[i] + Y_add[tbk_idx[bond_tbk[i]]] * blended_raw[i] - Y_reduce[tbk_idx[bond_tbk[i]]] * inv_weight[i]
                fc_terms.append(fc)
            fc_vec = cp.hstack(fc_terms)
            # In delta space, penalize when final charge (starting + delta) is closer to zero than starting
            normalization = cp.pos(abs_start - cp.abs(starting_charge_bps[ul_idx] + fc_vec))
            asym_penalty = cfg.skew_asymmetry * l * cp.sum(
                cp.multiply(kappa[ul_idx] * stiffness_weights, cp.square(normalization))
            )

        penalty = base_penalty + asym_penalty
        objective = cp.Maximize(normalized_pnl_expr - penalty - x_regularization)

    tiers = [
        {"desc": "Strict", "buffer_mult": 1.0},
        {"desc": "Expand Buffers (2x)", "buffer_mult": 2.0},
        {"desc": "Expand Buffers (4x)", "buffer_mult": 4.0},
    ] if getattr(cfg, 'auto_relax', False) else [{"desc": "Strict", "buffer_mult": 1.0}]

    is_ok_final = False
    prob = None
    risk_pct = None

    for attempt, tier in enumerate(tiers):
        log.notify(f'Running solver for tier {attempt}: {tier.get("desc")}')
        constraints: list[cp.Constraint] = []

        for s in u_sides:
            start_val = start_by_side.get(s, 0)
            if start_val==0:
                continue

            sm = np.array([sides[ul_idx[j]]==s for j in range(n_ul)])
            lk_s = float(np.sum(proceeds[lk_idx[np.array([sides[i]==s for i in lk_idx])]])) if len(lk_idx) else 0.0
            ul_start_s = float(np.sum(proceeds[ul_idx[sm]])) if sm.any() else 0.0
            # DELTA SPACE: total_side = starting_unlocked + delta + locked
            delta_side_expr = (
                    (A_X[sm].sum(0) if sm.any() else np.zeros(n_bk)) @ X
                    + (A_Ya[sm].sum(0) if sm.any() else np.zeros(n_tbk)) @ Y_add
                    + (A_Yr[sm].sum(0) if sm.any() else np.zeros(n_tbk)) @ Y_reduce
            )
            side_expr = ul_start_s + delta_side_expr + lk_s

            if start_val >= 0:
                floor_val = cfg.side_floor_pct * start_val
                ceil_val = start_val / cfg.side_floor_pct   # FIX #3: symmetric ceiling
            else:
                floor_val = start_val / cfg.side_floor_pct
                ceil_val = cfg.side_floor_pct * start_val    # FIX #3: symmetric ceiling

            constraints.append(side_expr >= floor_val)
            constraints.append(side_expr <= ceil_val)  # FIX #3: prevent unbounded margin drift

        risk_pct_raw = trader_agg.select(
            [
                pl.concat_arr(
                    [
                        pl.col(inner_col),
                        pl.col(_c('side')),
                        pl.col(_c('quote_type'))
                    ]
                ).alias('_key'),
                pl.col('wavg_pct_by_side_qt')
            ]
        ).collect().hyper.to_map('_key', 'wavg_pct_by_side_qt')

        # FIX #11: Normalize dict keys to tuples so .get(tuple) lookups succeed.
        # hyper.to_map may return list keys from concat_arr; list != tuple in dict lookup.
        risk_pct = {
            tuple(k) if isinstance(k, (list, np.ndarray)) else k: v
            for k, v in risk_pct_raw.items()
        }

        if cfg.debug:
            matched = sum(1 for tbk in tbk_keys if risk_pct.get(tbk, None) is not None)
            if matched == 0 and len(tbk_keys) > 0:
                sample_raw = next(iter(risk_pct_raw.keys()), None)
                log.error(
                    f"risk_pct key mismatch: 0/{len(tbk_keys)} matched. "
                    f"Raw key type={type(sample_raw)}, tbk type={type(tbk_keys[0])}"
                )

        # Extract blended expected_proceeds per trader as constraint targets
        expected_proceeds_raw = trader_agg.select(
            [
                pl.concat_arr(
                    [
                        pl.col(inner_col),
                        pl.col(_c('side')),
                        pl.col(_c('quote_type'))
                    ]
                ).alias('_key'),
                pl.col('expected_proceeds')
            ]
        ).collect().hyper.to_map('_key', 'expected_proceeds')
        expected_proceeds_map = {
            tuple(k) if isinstance(k, (list, np.ndarray)) else k: v
            for k, v in expected_proceeds_raw.items()
        }

        sum_of_targets = {k: 0 for k in bucket_keys}
        for tbk in tbk_keys:
            t, s, q = tbk
            bk = (s, q)
            rp = risk_pct.get(tbk, 0.0)
            # Use blended target (anchored to starting) instead of pure risk_pct × total
            target = expected_proceeds_map.get(tbk, rp * start_charge_by_bk.get(bk, 0.0))
            sum_of_targets[bk] += target

            tm = np.array([bond_tbk[ul_idx[j]]==tbk for j in range(n_ul)])

            if not tm.any(): continue

            if cfg.buffer_mode == 'pct':
                base_buffer = max(abs(target) * cfg.buffer_pct, cfg.buffer_min_flat)
            else:
                base_buffer = getattr(cfg, 'buffer_fixed', 100)
            active_buffer = base_buffer * tier["buffer_mult"]

            lk_tbk = [i for i in lk_idx if bond_tbk[i]==tbk]
            lk_chg = float(np.sum(proceeds[lk_tbk])) if lk_tbk else 0.0
            ul_start_tbk = float(np.sum(proceeds[ul_idx[tm]])) if tm.any() else 0.0
            # DELTA SPACE: total_trader = starting_unlocked + delta + locked
            delta_tbk_expr = (
                    (A_X[tm].sum(0) if tm.any() else np.zeros(n_bk)) @ X
                    + (A_Ya[tm].sum(0) if tm.any() else np.zeros(n_tbk)) @ Y_add
                    + (A_Yr[tm].sum(0) if tm.any() else np.zeros(n_tbk)) @ Y_reduce
            )
            tbk_expr = ul_start_tbk + delta_tbk_expr + lk_chg

            constraints.append(tbk_expr <= target + active_buffer)
            constraints.append(tbk_expr >= target - active_buffer)

        # FIX #4: Validate that trader target allocations sum to bucket totals
        if cfg.debug:
            for bk in bucket_keys:
                expected = start_charge_by_bk.get(bk, 0.0)
                actual_sum = sum_of_targets.get(bk, 0.0)
                if abs(expected) > 1e-6 and abs(expected - actual_sum) > max(1.0, abs(expected) * 0.01):
                    log.warning(
                        f"Target allocation mismatch for {bk}: "
                        f"bucket_total={expected:.2f}, sum_of_trader_targets={actual_sum:.2f}, "
                        f"gap={expected - actual_sum:.2f}"
                    )

        def _add_bond_constraints(constraints_list):
            for j, i in enumerate(ul_idx):
                # In delta space: final_charge = starting + delta. Prevent going through mid.
                delta = X[bk_idx[bond_bk[i]]] * blended_raw[i] + Y_add[tbk_idx[bond_tbk[i]]] * blended_raw[i] - Y_reduce[tbk_idx[bond_tbk[i]]] * inv_weight[i]
                final_charge = starting_charge_bps[i] + delta
                if bond_bk[i] in (("SELL", "PX"), ("BUY", "SPD")):
                    constraints_list.append(final_charge >= 0)
                else:
                    constraints_list.append(final_charge <= 0)

        if not getattr(cfg, 'allow_through_mid', False):
            _add_bond_constraints(constraints)

        for bk in bucket_keys:
            s, q = bk
            cap = (cfg.max_spread_skew_delta if q=="SPD" else cfg.max_px_skew_delta if q=="PX" else None)
            if cap is None: continue

            bps_to_skew = 1.0 if q=="SPD" else 1.0 / 100.0
            ul_js = [j for j, ii in enumerate(ul_idx) if bond_bk[ii]==bk]
            bk_mask = np.array([bond_bk[i]==bk for i in range(N)])
            total_kappa_bk = float(np.sum(kappa[bk_mask]))

            if not ul_js or total_kappa_bk < 1e-12:
                continue

            x_coeff = 0.0
            ya_coeff = np.zeros(n_tbk)  # Y_add coefficient (blended weight)
            yr_coeff = np.zeros(n_tbk)  # Y_reduce coefficient (inv weight)
            const_part = 0.0  # no starting subtraction needed — fc IS the delta
            for j in ul_js:
                i = ul_idx[j]
                k = kappa[i]
                si = signs[i]
                x_coeff += si * k * blended_raw[i]
                ya_coeff[tbk_idx[bond_tbk[i]]] += si * k * blended_raw[i]      # same sign as X
                yr_coeff[tbk_idx[bond_tbk[i]]] -= si * k * inv_weight[i]       # negative sign

            skew_delta_expr = bps_to_skew * (
                    x_coeff * X[bk_idx[bk]] + ya_coeff @ Y_add + yr_coeff @ Y_reduce + const_part
            )
            rhs = cap * total_kappa_bk

            constraints.append(skew_delta_expr <= rhs)
            constraints.append(skew_delta_expr >= -rhs)

        for j, i in enumerate(ul_idx):
            # In delta space, fc IS the change from starting
            fc = X[bk_idx[bond_bk[i]]] * blended_raw[i] + Y_add[tbk_idx[bond_tbk[i]]] * blended_raw[i] - Y_reduce[tbk_idx[bond_tbk[i]]] * inv_weight[i]
            q = qts[i]

            if q=="SPD" and cfg.max_individual_spread_skew_delta is not None:
                cap = cfg.max_individual_spread_skew_delta
                constraints.append(fc <= cap)
                constraints.append(fc >= -cap)
            elif q=="PX" and cfg.max_individual_px_skew_delta is not None:
                cap_bps = cfg.max_individual_px_skew_delta * 100.0
                constraints.append(fc <= cap_bps)
                constraints.append(fc >= -cap_bps)

        prob = cp.Problem(objective, constraints)
        for slv in [cfg.solver, "SCS", "ECOS", "CLARABEL"]:
            kw = _SOLVER_KW.get(slv, {})
            try:
                prob.solve(solver=slv, verbose=cfg.solver_verbose, **kw)
                if prob.status in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
                    is_ok_final = True
                    break
            except Exception as e:
                pass

        if is_ok_final:
            if getattr(cfg, 'debug', False) and attempt > 0:
                log.warning(f"Optimization solved via auto-relax ({tier['desc']}) after {attempt} failures.")
            break

    if not is_ok_final:
        if name is None:
            log.error(f"Optimization failed even after full relaxation: {prob.status if prob else 'Unknown'}")
        else:
            log.error(
                f"Optimization failed for {name} even after full relaxation: {prob.status if prob else 'Unknown'}"
                )

    X_val = X.value if X.value is not None else np.zeros(n_bk)
    Y_add_val = Y_add.value if Y_add.value is not None else np.zeros(n_tbk)
    Y_reduce_val = Y_reduce.value if Y_reduce.value is not None else np.zeros(n_tbk)

    if not is_ok_final:
        final_charge_bps = np.copy(starting_charge_bps)
        final_proceeds_arr = proceeds.copy()
        if cfg.debug:
            if name is None:
                log.warning("Using starting values as fallback (no solution found).")
            else:
                log.warning(f"Using starting values as fallback for {name} (no solution found).")
    else:
        final_charge_bps = np.copy(starting_charge_bps)
        final_proceeds_arr = proceeds.copy()
        for j, i in enumerate(ul_idx):
            # DELTA SPACE: final = starting + delta
            delta = (X_val[bk_idx[bond_bk[i]]] * blended_raw[i]
                     + Y_add_val[tbk_idx[bond_tbk[i]]] * blended_raw[i]
                     - Y_reduce_val[tbk_idx[bond_tbk[i]]] * inv_weight[i])
            final_charge_bps[i] = starting_charge_bps[i] + delta
            final_proceeds_arr[i] = signs[i] * final_charge_bps[i] * kappa[i]

    # Decomposition:
    #   rebase_effect: informational — what the blended risk curve implies vs starting
    #                  (positive = blended curve says bond should have MORE charge than it started with)
    #   bucket_effect: optimizer's bucket-level delta (X × blended)
    #   group_effect:  optimizer's trader-level delta (Y_add × blended − Y_reduce × inv_priority)
    #   skew_delta = bucket_effect + group_effect  (rebase is informational only, not additive)
    bps_to_skew = np.where(is_px, 1.0 / 100.0, 1.0)

    rebase_effect = np.zeros(N)
    bucket_effect = np.zeros(N)
    trader_effect = np.zeros(N)
    for i in range(N):
        if locked[i]:
            rebase_effect[i] = 0.0
            bucket_effect[i] = 0.0
            trader_effect[i] = 0.0
        else:
            # Informational: blended curve baseline vs starting skew
            rebase_effect[i] = blended_raw[i] * bps_to_skew[i] - skew[i]
            # Optimization deltas
            bucket_effect[i] = X_val[bk_idx[bond_bk[i]]] * blended_raw[i] * bps_to_skew[i]
            trader_effect[i] = (Y_add_val[tbk_idx[bond_tbk[i]]] * blended_raw[i]
                               - Y_reduce_val[tbk_idx[bond_tbk[i]]] * inv_weight[i]) * bps_to_skew[i]

    sizes = df.select(_c('size')).collect().to_series().to_numpy()
    ref_mid_spd = df.select(_c('ref_mid_spd')).collect().to_series().to_numpy()
    ref_mid_px = df.select(_c('ref_mid_px')).collect().to_series().to_numpy()
    dv01 = df.select(_c('dv01')).collect().to_series().to_numpy()

    side_signs = np.array([1.0 if s == "BUY" else -1.0 for s in sides])
    implied_px = ref_mid_px - side_signs * (final_proceeds_arr * 100.0 / sizes)
    implied_spd = np.where(~is_px, ref_mid_spd + final_charge_bps, np.nan)
    # final_skew = final_charge in skew units. bucket + group = skew_delta.
    # rebase is informational only — NOT included in the sum.
    implied_skew = final_charge_bps * bps_to_skew
    charge_delta_display = implied_skew - skew  # = bucket_effect + group_effect

    X_dict = {bk: float(X_val[bk_idx[bk]]) for bk in bucket_keys}
    Y_dict = {tbk: float(Y_add_val[tbk_idx[tbk]] - Y_reduce_val[tbk_idx[tbk]]) for tbk in tbk_keys}
    final_by_side: dict[str, float] = {}
    for s in u_sides:
        m = np.array([sides[i]==s for i in range(N)])
        final_by_side[s] = float(np.sum(final_proceeds_arr[m]))

    status = prob.status if prob else 'FAILED'
    if (status=='optimal') and (len(removed_ids) > 0):
        status = "partial"

    result = OptimizationResult(
        status=status,
        optimal=is_ok_final,
        objective_value=prob.value if prob and prob.value is not None else float("nan"),
        X_values=X_dict, Y_values=Y_dict,
        final_charges=final_charge_bps, final_proceeds=final_proceeds_arr,
        starting_proceeds_by_side=start_by_side, final_proceeds_by_side=final_by_side,
        risk_pct=risk_pct
    )

    quote_spd = df.select(_c('quote_spd')).collect().to_series().to_numpy()
    _result_select = [
        pl.col(_c('bond_id')),
        pl.col(_c('side')),
        pl.col(_c('quote_type')),
        pl.col(_c('size')),
        pl.col(_c('dv01')),
        pl.col(_c('quote_spd')),
        pl.col(_c('quote_px')),
        pl.col(_c('ref_mid_spd')),
        pl.col(_c('ref_mid_px')),
        pl.col(_c('trader')),
        pl.col(_c('liq_score')),
        pl.col(_c('bsr_notional')),
        pl.col(_c('bsi_notional')),
        (pl.col(_c('bsr_notional')) / pl.col(_c('size'))).alias('bsr_pct'),
        pl.col('skew'),
        pl.Series("starting_proceeds", np.round(proceeds, 0)),
        pl.Series("blended_charge", np.round(blended_raw, 4)),
        pl.Series("kappa", np.round(kappa, 2)),
        pl.Series("final_charge_bps", np.round(final_charge_bps, 4)),
        pl.Series("final_skew", np.round(implied_skew, 4)),          # FINAL skew level (starting + delta)
        pl.Series("skew_delta", np.round(charge_delta_display, 4)),  # CHANGE from starting skew = bucket + group
        pl.Series("rebase_effect", np.round(rebase_effect, 4)),      # INFORMATIONAL: blended curve vs starting
        pl.Series("bucket_effect", np.round(bucket_effect, 4)),      # optimizer X scaling effect
        pl.Series("group_effect", np.round(trader_effect, 4)),       # optimizer Y group adjustment
        pl.Series("risk_pct", np.round(bond_risk_pct, 6)),           # normalized trader share per bucket (sums to 1.0)
        pl.Series("final_proceeds", np.round(final_proceeds_arr, 0)),
        pl.Series("proceeds_delta", np.round(final_proceeds_arr - proceeds, 0)),
        pl.Series("implied_px", np.round(implied_px, 6)),
        pl.Series("implied_spd", np.round(np.nan_to_num(implied_spd, nan=0), 4)),
        pl.Series("spd_delta", np.round(np.where(~is_px, implied_spd - quote_spd, 0), 4)),
    ]
    if orig_group_cols is not None:
        for gc in orig_group_cols:
            _result_select.append(pl.col(gc))

    df_result = df.select(*_result_select)

    summary_overall = df_result.group_by([_c('side'), _c('quote_type')]).agg(
        [
            pl.col('skew_delta').abs().max().alias('max_skew_delta'),

            pl.col('skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_start_skew_dv01'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_final_skew_dv01'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_abs_skew_delta_dv01'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_skew_delta_dv01'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_rebase_effect_dv01'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_bucket_effect_dv01'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_trader_effect_dv01'),

            pl.col('skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_start_skew_size'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_final_skew_size'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('size'))).alias('_wavg_abs_skew_delta_size'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('size'))).alias('_wavg_skew_delta_size'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_rebase_effect_size'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_bucket_effect_size'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_trader_effect_size'),
            pl.col('proceeds_delta').sum().alias('proceeds_delta')
        ]
    ).with_columns(
        [
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_start_skew_dv01')).otherwise(
                pl.col('_wavg_start_skew_size')
                ).alias('wavg_start_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_final_skew_dv01')).otherwise(
                pl.col('_wavg_final_skew_size')
                ).alias('wavg_final_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_abs_skew_delta_dv01')).otherwise(
                pl.col('_wavg_abs_skew_delta_size')
                ).alias('wavg_abs_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_skew_delta_dv01')).otherwise(
                pl.col('_wavg_skew_delta_size')
                ).alias('wavg_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_rebase_effect_dv01')).otherwise(
                pl.col('_wavg_rebase_effect_size')
            ).alias('wavg_rebase_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_bucket_effect_dv01')).otherwise(
                pl.col('_wavg_bucket_effect_size')
            ).alias('wavg_bucket_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_trader_effect_dv01')).otherwise(
                pl.col('_wavg_trader_effect_size')
            ).alias('wavg_trader_effect'),
        ]
    ).drop(
        [
            '_wavg_start_skew_dv01', '_wavg_final_skew_dv01', '_wavg_abs_skew_delta_dv01', '_wavg_skew_delta_dv01',
            '_wavg_start_skew_size', '_wavg_final_skew_size', '_wavg_abs_skew_delta_size', '_wavg_skew_delta_size',
            '_wavg_rebase_effect_dv01', '_wavg_rebase_effect_size',
            '_wavg_bucket_effect_dv01', '_wavg_trader_effect_dv01','_wavg_bucket_effect_size', '_wavg_trader_effect_size',
        ], strict=False
    )

    _inner_group_by = orig_group_cols if orig_group_cols is not None else [_c('trader')]
    summary_trader = df_result.group_by([_c('side'), _c('quote_type')] + _inner_group_by).agg(
        [
            pl.col('skew_delta').abs().max().alias('max_skew_delta'),
            (pl.col(_c('bsr_notional')).sum() / pl.col(_c('size')).sum()).alias('pct_bsr'),
            (pl.col(_c('bsi_notional')).sum() / pl.col(_c('size')).sum()).alias('pct_bsi'),
            pl.col(_c('quote_type')).count().alias('count'),
            pl.col(_c('size')).sum().alias('size'),
            pl.col(_c('dv01')).sum().alias('dv01'),
            pl.col('risk_pct').sum().alias('risk_pct'),  # bond-level pcts sum to trader's bucket share

            pl.col(_c('liq_score')).hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_liq_score_dv01'),
            pl.col('skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_start_skew_dv01'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_final_skew_dv01'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_abs_skew_delta_dv01'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_skew_delta_dv01'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_rebase_effect_dv01'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_bucket_effect_dv01'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_trader_effect_dv01'),

            pl.col(_c('liq_score')).hyper.wavg(pl.col(_c('size'))).alias('_wavg_liq_score_size'),
            pl.col('skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_start_skew_size'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_final_skew_size'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('size'))).alias('_wavg_abs_skew_delta_size'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('size'))).alias('_wavg_skew_delta_size'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_rebase_effect_size'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_bucket_effect_size'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_trader_effect_size'),
            pl.col('proceeds_delta').sum().alias('proceeds_delta')

        ]
    ).with_columns(
        [
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_liq_score_dv01')).otherwise(
                pl.col('_wavg_liq_score_size')
                ).alias('wavg_liq_score'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_start_skew_dv01')).otherwise(
                pl.col('_wavg_start_skew_size')
                ).alias('wavg_start_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_final_skew_dv01')).otherwise(
                pl.col('_wavg_final_skew_size')
                ).alias('wavg_final_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_abs_skew_delta_dv01')).otherwise(
                pl.col('_wavg_abs_skew_delta_size')
                ).alias('wavg_abs_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_skew_delta_dv01')).otherwise(
                pl.col('_wavg_skew_delta_size')
                ).alias('wavg_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_rebase_effect_dv01')).otherwise(
                pl.col('_wavg_rebase_effect_size')
            ).alias('wavg_rebase_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_bucket_effect_dv01')).otherwise(
                pl.col('_wavg_bucket_effect_size')
            ).alias('wavg_bucket_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_trader_effect_dv01')).otherwise(
                pl.col('_wavg_trader_effect_size')
            ).alias('wavg_trader_effect'),
        ]
    ).drop(
        [
            '_wavg_liq_score_dv01', '_wavg_start_skew_dv01', '_wavg_final_skew_dv01', '_wavg_skew_delta_dv01',
            '_wavg_liq_score_size', '_wavg_start_skew_size', '_wavg_final_skew_size', '_wavg_skew_delta_size',
            '_wavg_rebase_effect_dv01', '_wavg_rebase_effect_size',
            '_wavg_bucket_effect_dv01', '_wavg_trader_effect_dv01', '_wavg_bucket_effect_size',
            '_wavg_trader_effect_size',
        ], strict=False
    )

    if cfg.debug:
        if is_ok_final:
            chgs = summary_overall.select(
                [
                    pl.concat_arr([pl.col(_c('side')), pl.col(_c('quote_type'))]).alias('k'),
                    pl.col('wavg_start_skew'), pl.col('wavg_final_skew'), pl.col('max_skew_delta')
                ]
            ).hyper.to_map('k', ['wavg_start_skew', 'wavg_final_skew', 'max_skew_delta'])
            res = {}
            for k, v in chgs.items():
                res["-".join(k)] = (
                    f'{round(v.get("wavg_start_skew"), 2)} -> {round(v.get("wavg_final_skew"), 2)}, ↑ {round(v.get("max_skew_delta"), 2)}')

            if name is None:
                log.success("Redistributed Success", **_sort_dict(res))
            else:
                log.success(f"Redistributed Success for {name}", **_sort_dict(res))
        else:
            if name is None:
                log.error("Redistribute FAILED", status=result.status)
            else:
                log.error(f"Redistribute FAILED for {name}", status=result.status)

    return df_result, result, summary_overall, summary_trader, removed_ids


def _build_fallback_result(sub_df: pl.LazyFrame, cfg: OptimizerConfig) -> pl.DataFrame:
    """Build a result DataFrame with starting values (zero optimization effects)
    for a trader whose solve() failed. Matches the output schema of solve()."""
    sub_df = sub_df.lazy() if isinstance(sub_df, pl.DataFrame) else sub_df

    # Match solve()'s preprocessing filters
    sub_df = sub_df.filter(pl.col('isReal') == 1)
    sub_df = sub_df.filter(pl.col(_c("quote_type")).is_in(['PX', 'SPD']))

    s = dict(sub_df.collect_schema())
    my_px_bid = [c for c in MY_PX_SOURCE_BID if c in s]
    my_px_ask = [c for c in MY_PX_SOURCE_ASK if c in s]
    my_spd_bid = [c for c in MY_SPD_SOURCE_BID if c in s]
    my_spd_ask = [c for c in MY_SPD_SOURCE_ASK if c in s]

    sub_df = sub_df.with_columns([
        pl.when(IS_BUY).then(pl.coalesce(my_px_bid)).otherwise(pl.coalesce(my_px_ask)).alias('_my_quotePx'),
        pl.when(IS_BUY).then(pl.coalesce(my_spd_bid)).otherwise(pl.coalesce(my_spd_ask)).alias('_my_quoteSpd'),
    ]).with_columns([
        pl.when(IS_SPREAD).then(pl.col('_my_quoteSpd') - pl.col('_refMidSpd'))
        .otherwise(pl.col('_my_quotePx') - pl.col('_refMidPx')).alias('skew'),
    ])

    sub_df = add_adjusted_bsr_bsi(sub_df, clamp_liq=True,
                                   charge_strength=cfg.charge_strength,
                                   default_strength=cfg.default_strength)

    sub_df = sub_df.with_columns([
        pl.when(IS_SPREAD).then(pl.col(_c('dv01'))).otherwise(pl.col(_c('size')) / 10_000).alias('kappa'),
        pl.when(IS_SPREAD & IS_SELL).then((pl.col('_refMidSpd') - pl.col('_my_quoteSpd')) * pl.col(_c('dv01')))
        .when(IS_SPREAD & IS_BUY).then((pl.col('_my_quoteSpd') - pl.col('_refMidSpd')) * pl.col(_c('dv01')))
        .when(IS_PX & IS_SELL).then((pl.col('_my_quotePx') - pl.col('_refMidPx')) * pl.col(_c('size')) / 100)
        .when(IS_PX & IS_BUY).then((pl.col('_refMidPx') - pl.col('_my_quotePx')) * pl.col(_c('size')) / 100)
        .alias('skewProceeds'),
    ])

    collected = sub_df.collect()
    N = len(collected)

    skew = collected['skew'].to_numpy().astype(float)
    kappa = collected['kappa'].to_numpy().astype(float)
    blended = collected['blendedCharge'].to_numpy().astype(float)
    proceeds = collected['skewProceeds'].to_numpy().astype(float)
    qts = collected[_c('quote_type')].to_list()
    is_px = np.array([q == "PX" for q in qts])
    bps_to_skew = np.where(is_px, 1.0 / 100.0, 1.0)
    starting_charge = np.where(is_px, skew * 100.0, skew)
    rebase = blended * bps_to_skew - skew

    sides = collected[_c('side')].to_list()
    side_signs = np.array([1.0 if si == "BUY" else -1.0 for si in sides])
    sizes = collected[_c('size')].to_numpy().astype(float)
    ref_mid_px = collected[_c('ref_mid_px')].to_numpy().astype(float)
    ref_mid_spd = collected[_c('ref_mid_spd')].to_numpy().astype(float)
    implied_px = ref_mid_px - side_signs * (proceeds * 100.0 / sizes)
    implied_spd = np.where(~is_px, ref_mid_spd + starting_charge, np.nan)
    quote_spd = collected[_c('quote_spd')].to_numpy().astype(float)

    return collected.select([
        pl.col(_c('bond_id')), pl.col(_c('side')), pl.col(_c('quote_type')),
        pl.col(_c('size')), pl.col(_c('dv01')),
        pl.col(_c('quote_spd')), pl.col(_c('quote_px')),
        pl.col(_c('ref_mid_spd')), pl.col(_c('ref_mid_px')),
        pl.col(_c('trader')), pl.col(_c('liq_score')),
        pl.col(_c('bsr_notional')), pl.col(_c('bsi_notional')),
        (pl.col(_c('bsr_notional')) / pl.col(_c('size'))).alias('bsr_pct'),
        pl.col('skew'),
        pl.Series("starting_proceeds", np.round(proceeds, 0)),
        pl.Series("blended_charge", np.round(blended, 4)),
        pl.Series("kappa", np.round(kappa, 2)),
        pl.Series("final_charge_bps", np.round(starting_charge, 4)),
        pl.Series("final_skew", np.round(skew, 4)),
        pl.Series("skew_delta", np.zeros(N)),
        pl.Series("rebase_effect", np.round(rebase, 4)),
        pl.Series("bucket_effect", np.zeros(N)),
        pl.Series("group_effect", np.zeros(N)),
        pl.Series("risk_pct", np.zeros(N)),
        pl.Series("final_proceeds", np.round(proceeds, 0)),
        pl.Series("proceeds_delta", np.zeros(N)),
        pl.Series("implied_px", np.round(implied_px, 6)),
        pl.Series("implied_spd", np.round(np.nan_to_num(implied_spd, nan=0), 4)),
        pl.Series("spd_delta", np.zeros(N)),
    ] + [pl.col(gc) for gc in (getattr(cfg, 'group_columns', None) or []) if gc in collected.columns])


def _solve_isolated(df: pl.DataFrame | pl.LazyFrame, cfg: OptimizerConfig):
    df = df.lazy() if isinstance(df, pl.DataFrame) else df
    sub_cfg = OptimizerConfig(**{f.name: getattr(cfg, f.name) for f in cfg.__dataclass_fields__.values()})
    sub_cfg.isolate_traders = False

    inner_col, orig_group_cols = _resolve_inner_col(cfg)

    traders_unique = df.select(pl.col(_c('trader')).unique()).collect().to_series().to_list()

    dfs_out: list[pl.LazyFrame] = []
    all_optimal = True
    combined_X, combined_Y, combined_risk_pct = {}, {}, {}
    combined_start_by_side, combined_final_by_side = {}, {}
    total_obj = 0.0
    success = 0

    for t in traders_unique:
        sub_df = df.filter(pl.col(_c('trader'))==t)
        try:
            df_r, res_r, _, _, _ = solve(sub_df, sub_cfg, name=t)
            if not isinstance(res_r, OptimizationResult):
                raise ValueError(f"solve returned non-OptimizationResult: {type(res_r)}")
            success += 1
        except Exception as e:
            if cfg.debug: log.warning(f"Isolated solve for trader {t} failed: {e} -- using starting values")
            # Build fallback: all bonds keep starting values, zero optimization effects
            try:
                df_r = _build_fallback_result(sub_df, sub_cfg)
                # Compute side proceeds for the fallback trader
                _fb_starts: dict[str, float] = {}
                for row in df_r.select([_c('side'), 'starting_proceeds']).iter_rows():
                    _fb_starts[row[0]] = _fb_starts.get(row[0], 0.0) + float(row[1])
                res_r = OptimizationResult(
                    status="infeasible", optimal=False, objective_value=0.0,
                    X_values={}, Y_values={},
                    final_charges=np.array([]), final_proceeds=np.array([]),
                    starting_proceeds_by_side=_fb_starts,
                    final_proceeds_by_side=dict(_fb_starts),  # final = starting for fallback
                    risk_pct={}
                )
            except Exception as e2:
                if cfg.debug: log.warning(f"Fallback for trader {t} also failed: {e2} -- skipping entirely")
            continue

        dfs_out.append(df_r.lazy() if isinstance(df_r, pl.DataFrame) else df_r)
        all_optimal = all_optimal and res_r.optimal
        combined_X.update(res_r.X_values)
        combined_Y.update(res_r.Y_values)
        if res_r.risk_pct:
            combined_risk_pct.update(res_r.risk_pct)
        total_obj += res_r.objective_value if not np.isnan(res_r.objective_value) else 0.0
        for s, v in res_r.starting_proceeds_by_side.items():
            combined_start_by_side[s] = combined_start_by_side.get(s, 0.0) + v
        for s, v in res_r.final_proceeds_by_side.items():
            combined_final_by_side[s] = combined_final_by_side.get(s, 0.0) + v

    if not dfs_out: raise RuntimeError("All isolated trader solves failed -- cannot produce a result.")

    df_result = pl.concat(dfs_out)

    # Recompute bond-level risk_pct from the FULL cross-trader dataset.
    # Each sub-solve had only 1 trader → its risk_pct was always 1.0.
    # We need the correct cross-trader allocation.
    try:
        _iso_result = df_result.collect() if hasattr(df_result, 'collect') else df_result
        _iso_sides = _iso_result[_c('side')].to_list()
        _iso_qts = _iso_result[_c('quote_type')].to_list()
        _iso_inner = _iso_result[_c('trader')].to_list()
        _iso_trader_risk = _iso_result['starting_proceeds'].to_numpy()  # use starting proceeds as risk proxy
        _iso_N = len(_iso_result)

        # Build (trader, side, qt) keys and bucket (side, qt) keys
        _iso_tbk = [((_iso_inner[i] or 'MISSING'), _iso_sides[i], _iso_qts[i]) for i in range(_iso_N)]
        _iso_bk = [(_iso_sides[i], _iso_qts[i]) for i in range(_iso_N)]

        # Sum |starting_proceeds| per (trader, side, qt) and per (side, qt) bucket
        _tbk_sums: dict[tuple, float] = {}
        _bk_sums: dict[tuple, float] = {}
        for i in range(_iso_N):
            v = abs(float(_iso_trader_risk[i]))
            _tbk_sums[_iso_tbk[i]] = _tbk_sums.get(_iso_tbk[i], 0.0) + v
            _bk_sums[_iso_bk[i]] = _bk_sums.get(_iso_bk[i], 0.0) + v

        # bond_risk_pct = |bond_risk| / bucket_total
        _iso_bond_risk_pct = np.array([
            abs(float(_iso_trader_risk[i])) / _bk_sums[_iso_bk[i]]
            if _bk_sums.get(_iso_bk[i], 0) > 1e-12 else 0.0
            for i in range(_iso_N)
        ])

        # Replace the per-sub-solve risk_pct with the correct cross-trader values
        if isinstance(df_result, pl.LazyFrame):
            df_result = _iso_result
        df_result = df_result.with_columns(
            pl.Series("risk_pct", np.round(_iso_bond_risk_pct, 6))
        )
        if not isinstance(df_result, pl.LazyFrame):
            df_result = df_result.lazy()
    except Exception as e:
        if cfg.debug: log.warning(f"Isolated risk_pct recompute failed: {e}")

    summary_overall = df_result.group_by([_c('side'), _c('quote_type')]).agg(
        [
            pl.col('skew_delta').abs().max().alias('max_skew_delta'),

            pl.col('skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_start_skew_dv01'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_final_skew_dv01'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_abs_skew_delta_dv01'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_skew_delta_dv01'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_rebase_effect_dv01'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_bucket_effect_dv01'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_trader_effect_dv01'),

            pl.col('skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_start_skew_size'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_final_skew_size'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('size'))).alias('_wavg_abs_skew_delta_size'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('size'))).alias('_wavg_skew_delta_size'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_rebase_effect_size'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_bucket_effect_size'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_trader_effect_size'),
        ]
    ).with_columns(
        [
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_start_skew_dv01')).otherwise(
                pl.col('_wavg_start_skew_size')).alias('wavg_start_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_final_skew_dv01')).otherwise(
                pl.col('_wavg_final_skew_size')).alias('wavg_final_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_abs_skew_delta_dv01')).otherwise(
                pl.col('_wavg_abs_skew_delta_size')).alias('wavg_abs_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_skew_delta_dv01')).otherwise(
                pl.col('_wavg_skew_delta_size')).alias('wavg_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_rebase_effect_dv01')).otherwise(
                pl.col('_wavg_rebase_effect_size')).alias('wavg_rebase_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_bucket_effect_dv01')).otherwise(
                pl.col('_wavg_bucket_effect_size')).alias('wavg_bucket_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_trader_effect_dv01')).otherwise(
                pl.col('_wavg_trader_effect_size')).alias('wavg_trader_effect'),
        ]
    ).drop(
        [
            '_wavg_start_skew_dv01', '_wavg_final_skew_dv01', '_wavg_abs_skew_delta_dv01', '_wavg_skew_delta_dv01',
            '_wavg_rebase_effect_dv01', '_wavg_rebase_effect_size',
            '_wavg_bucket_effect_dv01', '_wavg_trader_effect_dv01',
            '_wavg_start_skew_size', '_wavg_final_skew_size', '_wavg_abs_skew_delta_size', '_wavg_skew_delta_size',
            '_wavg_bucket_effect_size', '_wavg_trader_effect_size',
        ], strict=False
    )

    _iso_inner_col, _iso_group_cols = _resolve_inner_col(cfg)
    _iso_group_by = _iso_group_cols if _iso_group_cols is not None else [_c('trader')]
    summary_trader = df_result.group_by([_c('side'), _c('quote_type')] + _iso_group_by).agg(
        [
            pl.col('skew_delta').abs().max().alias('max_skew_delta'),
            pl.col('risk_pct').sum().alias('risk_pct'),

            (pl.col(_c('bsr_notional')).sum() / pl.col(_c('size')).sum()).alias('pct_bsr'),
            (pl.col(_c('bsi_notional')).sum() / pl.col(_c('size')).sum()).alias('pct_bsi'),
            pl.col(_c('quote_type')).count().alias('count'),
            pl.col(_c('size')).sum().alias('size'),
            pl.col(_c('dv01')).sum().alias('dv01'),

            pl.col('skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_start_skew_dv01'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_final_skew_dv01'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_abs_skew_delta_dv01'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_skew_delta_dv01'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_rebase_effect_dv01'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_bucket_effect_dv01'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_trader_effect_dv01'),

            pl.col(_c('liq_score')).hyper.wavg(pl.col(_c('dv01'))).alias('_wavg_liq_score_dv01'),
            pl.col(_c('liq_score')).hyper.wavg(pl.col(_c('size'))).alias('_wavg_liq_score_size'),

            pl.col('skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_start_skew_size'),
            pl.col('final_skew').hyper.wavg(pl.col(_c('size'))).alias('_wavg_final_skew_size'),
            pl.col('skew_delta').abs().hyper.wavg(pl.col(_c('size'))).alias('_wavg_abs_skew_delta_size'),
            pl.col('skew_delta').hyper.wavg(pl.col(_c('size'))).alias('_wavg_skew_delta_size'),
            pl.col('rebase_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_rebase_effect_size'),
            pl.col('bucket_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_bucket_effect_size'),
            pl.col('group_effect').hyper.wavg(pl.col(_c('size'))).alias('_wavg_trader_effect_size'),
        ]
    ).with_columns(
        [
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_liq_score_dv01')).otherwise(
                pl.col('_wavg_liq_score_size')).alias('wavg_liq_score'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_start_skew_dv01')).otherwise(
                pl.col('_wavg_start_skew_size')).alias('wavg_start_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_final_skew_dv01')).otherwise(
                pl.col('_wavg_final_skew_size')).alias('wavg_final_skew'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_abs_skew_delta_dv01')).otherwise(
                pl.col('_wavg_abs_skew_delta_size')).alias('wavg_abs_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_skew_delta_dv01')).otherwise(
                pl.col('_wavg_skew_delta_size')).alias('wavg_skew_delta'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_rebase_effect_dv01')).otherwise(
                pl.col('_wavg_rebase_effect_size')).alias('wavg_rebase_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_bucket_effect_dv01')).otherwise(
                pl.col('_wavg_bucket_effect_size')).alias('wavg_bucket_effect'),
            pl.when(pl.col(_c('quote_type'))=="SPD").then(pl.col('_wavg_trader_effect_dv01')).otherwise(
                pl.col('_wavg_trader_effect_size')).alias('wavg_trader_effect'),
        ]
    ).drop(
        [
            '_wavg_liq_score_dv01', '_wavg_liq_score_size',
            '_wavg_start_skew_dv01', '_wavg_final_skew_dv01', '_wavg_abs_skew_delta_dv01', '_wavg_skew_delta_dv01',
            '_wavg_rebase_effect_dv01', '_wavg_rebase_effect_size',
            '_wavg_bucket_effect_dv01', '_wavg_trader_effect_dv01',
            '_wavg_start_skew_size', '_wavg_final_skew_size', '_wavg_abs_skew_delta_size', '_wavg_skew_delta_size',
            '_wavg_bucket_effect_size', '_wavg_trader_effect_size',
        ], strict=False
    )

    result = OptimizationResult(
        status="optimal" if all_optimal else "partial",
        optimal=all_optimal, objective_value=total_obj,
        X_values=combined_X, Y_values=combined_Y,
        final_charges=np.array([]), final_proceeds=np.array([]),
        starting_proceeds_by_side=combined_start_by_side,
        final_proceeds_by_side=combined_final_by_side, risk_pct=combined_risk_pct,
    )

    if cfg.debug:
        if all_optimal: log.success(
            "Isolated-trader redistribute complete", traders=len(traders_unique), objective=round(total_obj, 2)
            )
        else: log.warning(f"Isolated-trader redistribute -- some traders infeasible, {success} / {len(traders_unique)}")

    return df_result, result, summary_overall, summary_trader, {}
