import Interval.Interval.Division
import Interval.Interval.Monotone
import Interval.Interval.Pi
import Interval.Interval.Series
import Interval.Misc.ArctanBounds

/-!
## Interval `arctan`

We implement `arctan` for intervals using Taylor series for small arguments
and argument reduction for large arguments.
-/

open Set
open scoped Real

/-!
### `arctan x / x` for small `x` via series

The arctan series is `arctan(x) = Σ_{n=0}^∞ (-1)^n * x^(2n+1) / (2n+1)`.
We factor out `x` to get `arctan(x) = x * Σ_{n=0}^∞ (-1)^n * x^(2n) / (2n+1)`,
which we evaluate as a power series in `x²`.
-/

/-- Our series will be accurate on `|x| ≤ r` for `r` slightly less than 1. -/
def arctan_series_radius : ℚ := 0.95

/-- A power series approximation for `arctan(x) / x` = `Σ (-1)^n * x^(2n) / (2n+1)`.
    This is a series in `u = x²`, evaluated at `u`. -/
@[irreducible] def arctan_over_x_series (n : ℕ) : Series where
  radius := .ofRat (arctan_series_radius ^ 2) false  -- radius for u = x²
  coeffs := (Array.range n).map (fun k ↦
    (((-1 : ℤ)^k / ((2 * k + 1 : ℕ) : ℚ) : ℚ) : Interval))
  error := bif n == 0 then nan
           else .ofRat (arctan_series_radius ^ (2 * n) / (1 - arctan_series_radius ^ 2)) true

/-- Helper: arctan(x)/x for the series approximation, extended by continuity at 0 -/
noncomputable def arctan_over_x (x : ℝ) : ℝ := if x = 0 then 1 else Real.arctan x / x

/-- arctan = x * (arctan/x) -/
lemma arctan_eq_mul_arctan_over_x (x : ℝ) : Real.arctan x = x * arctan_over_x x := by
  by_cases h : x = 0
  · simp only [h, Real.arctan_zero, zero_mul]
  · simp only [arctan_over_x, h, ↓reduceIte, mul_div_cancel₀ _ h]

/-- arctan_over_x is even -/
lemma arctan_over_x_neg (x : ℝ) : arctan_over_x (-x) = arctan_over_x x := by
  by_cases h : x = 0
  · simp only [h, neg_zero]
  · simp only [arctan_over_x, neg_eq_zero, h, ↓reduceIte, Real.arctan_neg, neg_div_neg_eq]

/-- arctan_over_x at |x| equals arctan_over_x at x -/
lemma arctan_over_x_abs (x : ℝ) : arctan_over_x |x| = arctan_over_x x := by
  cases' abs_cases x with h h <;> simp only [h, arctan_over_x_neg]

/-- Bound for arctan_over_x Taylor series -/
lemma arctan_over_x_taylor_bound {x : ℝ} (n : ℕ) (n0 : n ≠ 0) (xr : |x| ≤ arctan_series_radius) :
    |arctan_over_x x - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * k + 1) * x ^ (2 * k)| ≤
      (arctan_series_radius : ℝ) ^ (2 * n) / (1 - arctan_series_radius ^ 2) := by
  by_cases h : x = 0
  · -- x = 0 case: arctan_over_x 0 = 1, and sum starts with 1
    simp only [h, arctan_over_x, ↓reduceIte]
    have hsum : ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * k + 1) * 0 ^ (2 * k) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, Nat.cast_zero, mul_zero, zero_add, div_one, mul_one]
      · intro k _ hk
        have h2k : 2 * k ≠ 0 := by omega
        rw [zero_pow h2k, mul_zero]
      · intro hn; exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero n0)) hn
    simp only [hsum, sub_self, abs_zero]
    apply div_nonneg (pow_nonneg _ _)
    · simp only [arctan_series_radius]; norm_num
    · simp only [arctan_series_radius]; norm_num
  · -- x ≠ 0 case: prove bound directly using geometric series
    have r1 : arctan_series_radius < 1 := by simp only [arctan_series_radius]; norm_num
    have r_pos : 0 < (arctan_series_radius : ℝ) := by simp only [arctan_series_radius]; norm_num
    have r_nonneg : 0 ≤ (arctan_series_radius : ℝ) := le_of_lt r_pos
    have hr2 : (arctan_series_radius : ℝ) ^ 2 < 1 := by
      simp only [arctan_series_radius]; norm_num
    have hx1 : ‖x‖ < 1 := by
      calc ‖x‖ = |x| := Real.norm_eq_abs x
        _ ≤ arctan_series_radius := xr
        _ < 1 := by exact_mod_cast r1
    -- HasSum for arctan(x)/x series
    have hs_arctan := Real.hasSum_arctan hx1
    have hs : HasSum (fun (k : ℕ) ↦ (-1 : ℝ) ^ k * x ^ (2 * k) / (↑(2 * k + 1) : ℝ)) (Real.arctan x / x) := by
      have hdiv := hs_arctan.div_const x
      simp only [mul_div_assoc] at hdiv
      convert hdiv using 1
      funext k
      have hpow : x ^ (2 * k + 1) / x = x ^ (2 * k) := by
        rw [pow_succ, mul_div_assoc, div_self h, mul_one]
      -- LHS: (-1) ^ k * x ^ (2 * k) / ↑(2 * k + 1)
      -- RHS: (-1) ^ k * (x ^ (2 * k + 1) / ↑(2 * k + 1) / x)
      rw [div_div, mul_comm (↑(2 * k + 1) : ℝ) x, ← div_div, hpow, mul_div_assoc]
    -- Each term is bounded by 1 * (r²)^k
    have hf_bound : ∀ k : ℕ, ‖(-1 : ℝ) ^ k * x ^ (2 * k) / ↑(2 * k + 1)‖ ≤ 1 * ((arctan_series_radius : ℝ) ^ 2) ^ k := by
      intro k
      have h_denom_pos : (0 : ℝ) < ↑(2 * k + 1) := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos h_denom_pos, abs_pow]
      have h1 : |x| ^ (2 * k) / ↑(2 * k + 1) ≤ |x| ^ (2 * k) := by
        apply div_le_self (pow_nonneg (abs_nonneg x) _)
        have : 1 ≤ (2 * k + 1 : ℕ) := by omega
        exact_mod_cast this
      rw [one_mul]
      calc |x| ^ (2 * k) / ↑(2 * k + 1)
          ≤ |x| ^ (2 * k) := h1
        _ ≤ (arctan_series_radius : ℝ) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg x) xr _
        _ = ((arctan_series_radius : ℝ) ^ 2) ^ k := by ring
    -- Apply geometric series bound
    have hbound := norm_sub_le_of_geometric_bound_of_hasSum hr2 hf_bound hs n
    simp only [arctan_over_x, h, ↓reduceIte]
    -- Convert norm to abs and massage the sum
    have sum_eq : ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * k + 1) * x ^ (2 * k) =
                  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k) / ↑(2 * k + 1) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    calc |Real.arctan x / x - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * k + 1) * x ^ (2 * k)|
        = ‖Real.arctan x / x - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * k + 1) * x ^ (2 * k)‖ := (Real.norm_eq_abs _).symm
      _ = ‖Real.arctan x / x - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k) / ↑(2 * k + 1)‖ := by rw [sum_eq]
      _ = ‖(∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k) / ↑(2 * k + 1)) - Real.arctan x / x‖ := norm_sub_rev _ _
      _ ≤ 1 * ((arctan_series_radius : ℝ) ^ 2) ^ n / (1 - (arctan_series_radius : ℝ) ^ 2) := hbound
      _ = (arctan_series_radius : ℝ) ^ (2 * n) / (1 - arctan_series_radius ^ 2) := by ring

/-- arctan series approximation lemma - uses geometric series bounds -/
lemma mem_approx_arctan_over_x_series (n : ℕ) (n0 : n ≠ 0) (x : ℝ) (y : Interval)
    (xy : approx y x) :
    approx (y * (arctan_over_x_series n).eval y.sqr) (Real.arctan x) := by
  -- arctan(x) = x * arctan_over_x(x), and arctan_over_x(x) = arctan_over_x(|x|) = arctan_over_x(sqrt(x²))
  rw [arctan_eq_mul_arctan_over_x]
  apply approx_mul xy
  -- Show that series.eval(y.sqr) approximates arctan_over_x(x)
  -- The series is evaluated at u = x², so the function is f(u) = arctan_over_x(sqrt(u))
  -- Since sqrt(x²) = |x| and arctan_over_x is even, arctan_over_x(sqrt(x²)) = arctan_over_x(x)
  have hconv : arctan_over_x (Real.sqrt (x ^ 2)) = arctan_over_x x := by
    rw [Real.sqrt_sq_eq_abs, arctan_over_x_abs]
  rw [← hconv]
  have nn : (arctan_over_x_series n).coeffs.size = n := by
    rw [arctan_over_x_series, Array.size_map, Array.size_range]
  apply (arctan_over_x_series n).approx_of_taylor'
      (f := fun u ↦ arctan_over_x (Real.sqrt u))
      (a := fun k ↦ (-1 : ℝ) ^ k / (2 * k + 1))
      (b := (arctan_series_radius : ℝ) ^ (2 * n) / (1 - arctan_series_radius ^ 2))
      (xy := Interval.approx_sqr xy)
  · -- Bound: |f(u) - Σ a_k u^k| ≤ b for |u| ≤ radius
    intro rn ur
    rw [arctan_over_x_series] at rn ur
    simp only [arctan_series_radius] at rn ur ⊢
    -- u = x², and |u| = |x²| = x² (since x² ≥ 0)
    -- ur says |x^2| ≤ radius.val, so x² ≤ r²
    have ur' : x ^ 2 ≤ (0.95 : ℝ) ^ 2 := by
      have h1 : |x ^ 2| = x ^ 2 := abs_of_nonneg (sq_nonneg x)
      have h_cast : (((0.95 : ℚ) ^ 2 : ℚ) : ℝ) = (0.95 : ℝ) ^ 2 := by
        simp only [Rat.cast_pow]; rfl
      calc x ^ 2 = |x ^ 2| := h1.symm
        _ ≤ (Floating.ofRat (0.95 ^ 2) false).val := ur
        _ ≤ (((0.95 : ℚ) ^ 2 : ℚ) : ℝ) := Floating.ofRat_le rn
        _ = (0.95 : ℝ) ^ 2 := h_cast
    have xr : |x| ≤ (0.95 : ℝ) := by
      have h_abs_sq : |x| ^ 2 ≤ 0.95 ^ 2 := by rw [sq_abs]; exact ur'
      rwa [sq_le_sq, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 0.95)] at h_abs_sq
    -- sqrt(x²) = |x|, and arctan_over_x(|x|) = arctan_over_x(x)
    rw [Real.sqrt_sq_eq_abs, arctan_over_x_abs, nn]
    -- Now apply the Taylor bound
    have hb := arctan_over_x_taylor_bound n n0 xr
    -- Match the sum format - the sums are equal term by term
    simp only [arctan_series_radius] at hb ⊢
    -- The sums differ only in the order of multiplication; show they're equal
    have sum_eq : ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * ↑k + 1) * (x ^ 2) ^ k =
                  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / (2 * k + 1) * x ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← pow_mul]
    rw [sum_eq]
    exact hb
  · -- Coefficients: interval coeffs approximate real coeffs
    intro k
    -- The coefficient is (-1)^k / (2k+1) as a rational, and we need to show
    -- it approximates (-1)^k / (2*k+1) as a real
    simp only [arctan_over_x_series, Array.getElem_map, Array.getElem_range]
    -- k : Fin coeffs.size, and a k = (-1)^(k:ℕ) / (2*(k:ℕ)+1)
    -- coeffs[k] = ((-1:ℤ)^(k:ℕ) / (2*(k:ℕ)+1) : ℚ) : Interval
    -- Need to show: approx (coeff) (a (k : ℕ))
    -- The two sides are both (-1)^k / (2k+1), just with different type annotations
    have e : (-1 : ℝ) ^ (k : ℕ) / (2 * (k : ℕ) + 1) = (((-1 : ℤ) ^ (k : ℕ) / (2 * (k : ℕ) + 1 : ℕ) : ℚ) : ℝ) := by
      push_cast
      ring
    rw [e]
    approx
  · -- Error: b ≤ error.val
    intro en
    simp only [arctan_over_x_series, bif_eq_if, beq_iff_eq, n0, ↓reduceIte] at en ⊢
    -- Both b and error are r^(2n) / (1-r²), so this is exactly Floating.le_ofRat
    -- Need to convert from ℝ expression to ℚ cast form
    have h_eq : (arctan_series_radius : ℝ) ^ (2 * n) / (1 - (arctan_series_radius : ℝ) ^ 2) =
                ((arctan_series_radius ^ (2 * n) / (1 - arctan_series_radius ^ 2) : ℚ) : ℝ) := by
      simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]
    rw [h_eq]
    exact Floating.le_ofRat en

/-- 12 terms should give about 64 bits of precision for |x| ≤ 0.95 -/
@[irreducible] def arctan_over_x_series_12 := arctan_over_x_series 12

/-- Arctan for small arguments using series. -/
@[irreducible] def Interval.arctan_small (x : Interval) : Interval :=
  x * arctan_over_x_series_12.eval x.sqr

@[approx] lemma Interval.mem_approx_arctan_small {a : ℝ} {x : Interval} (ax : approx x a) :
    approx x.arctan_small (Real.arctan a) := by
  rw [arctan_small, arctan_over_x_series_12]
  exact mem_approx_arctan_over_x_series 12 (by norm_num) a x ax

/-!
### Full `arctan` with argument reduction

For |x| > 1, we use the identities:
- `arctan(x) = π/2 - arctan(1/x)` for x > 0
- `arctan(x) = -π/2 - arctan(1/x)` for x < 0
-/

/-- Arctan for a `Floating` point value -/
@[irreducible] def Floating.arctan (x : Floating) : Interval :=
  bif x == nan then nan
  else bif x.abs ≤ .ofRat arctan_series_radius false then
    -- Small argument: use series directly
    Interval.arctan_small x
  else
    -- Large argument: use arctan(x) = ±π/2 - arctan(1/x)
    let inv := (1 : Interval) / x
    let small := Interval.arctan_small inv
    bif 0 ≤ x then
      Interval.pi.div2 - small
    else
      -Interval.pi.div2 - small

/-- `Floating.arctan` is conservative -/
@[approx] lemma Floating.approx_arctan {a : ℝ} {x : Floating}
    (ax : approx x a) : approx x.arctan (Real.arctan a) := by
  rw [Floating.arctan]
  simp only [bif_eq_if, beq_iff_eq, decide_eq_true_eq]
  by_cases xn : x = nan
  · simp only [xn, ↓reduceIte, approx_nan]
  simp only [xn, ↓reduceIte]
  by_cases small : x.abs ≤ .ofRat arctan_series_radius false
  · simp only [small, ↓reduceIte]
    apply Interval.mem_approx_arctan_small
    exact Interval.approx_coe.mpr ax
  · simp only [small, ↓reduceIte]
    -- Argument reduction: arctan(x) = ±π/2 - arctan(1/x)
    have xnn : x ≠ nan := xn
    have a_eq : a = x.val := by
      simp only [Floating.approx_eq_singleton xnn] at ax
      exact ax.symm
    -- |x| > some threshold > 0, so x ≠ 0
    simp only [not_le, Floating.val_lt_val] at small
    -- The threshold is positive, so |x.val| > 0
    have threshold_pos : 0 < (Floating.ofRat arctan_series_radius false).val := by
      have h : (0 : Floating) < Floating.ofRat arctan_series_radius false := by decide +kernel
      simpa [Floating.val_zero] using Floating.val_lt_val.mp h
    have x_abs_pos : 0 < x.abs.val := lt_trans threshold_pos small
    rw [Floating.val_abs xnn] at x_abs_pos
    split_ifs with x_pos
    · -- Case: x ≥ 0, so a > 0 (since |x| > 0)
      have x_pos_val : (0 : ℝ) ≤ x.val := by
        have h := Floating.val_le_val.mp x_pos
        simp only [Floating.val_zero] at h
        exact h
      have a_pos : 0 < a := by
        rw [a_eq]  -- goal: 0 < x.val
        have heq : |x.val| = x.val := by rw [abs_eq_self]; exact x_pos_val
        rw [heq] at x_abs_pos
        exact x_abs_pos
      -- arctan(a) = π/2 - arctan(1/a) by arctan_inv_of_pos
      rw [show Real.arctan a = π / 2 - Real.arctan a⁻¹ by
        rw [Real.arctan_inv_of_pos a_pos]; ring]
      rw [inv_eq_one_div]
      -- Connect 1/a to 1/x.val
      have h1a : 1 / a = 1 / x.val := by rw [a_eq]
      rw [h1a]
      approx
    · -- Case: x < 0, so a < 0
      simp only [not_le, Floating.val_lt_val, Floating.val_zero] at x_pos
      have a_neg : a < 0 := by rw [a_eq]; exact x_pos
      -- arctan(a) = -π/2 - arctan(1/a) by arctan_inv_of_neg
      rw [show Real.arctan a = -(π / 2) - Real.arctan a⁻¹ by
        rw [Real.arctan_inv_of_neg a_neg]; ring]
      rw [inv_eq_one_div]
      -- Need to relate 1/a to 1/x.val
      have ha : 1 / a = 1 / x.val := by rw [a_eq]
      rw [ha]
      approx

/-- Arctan for an `Interval` -/
@[irreducible] def Interval.arctan (x : Interval) : Interval :=
  x.lo.arctan ∪ x.hi.arctan

/-- `Interval.arctan` is conservative -/
@[approx] lemma Interval.approx_arctan {a : ℝ} {x : Interval}
    (ax : approx x a) : approx x.arctan (Real.arctan a) := by
  rw [Interval.arctan]
  by_cases xn : x = nan
  · simp only [xn, lo_nan, Floating.arctan, bif_eq_if, beq_self_eq_true, ↓reduceIte, hi_nan,
      union_self, approx_nan]
  apply approx_of_mem_Icc (a := Real.arctan x.lo.val) (c := Real.arctan x.hi.val)
  · apply Interval.approx_union_left; approx
  · apply Interval.approx_union_right; approx
  · simp only [approx, lo_eq_nan, xn, false_or] at ax
    exact ⟨Real.arctan_mono ax.1, Real.arctan_mono ax.2⟩

/-- `Interval.arctan` propagates `nan` -/
@[simp] lemma Interval.nan_arctan : (nan : Interval).arctan = nan := by
  rw [Interval.arctan]
  simp only [lo_nan, Floating.arctan, bif_eq_if, beq_self_eq_true, ↓reduceIte, hi_nan, union_self]
