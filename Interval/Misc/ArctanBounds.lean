/-
Copyright (c) 2025 Interval contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Field

/-!
## Bounds for `arctan` Taylor series

We prove error bounds for the Taylor series of `arctan`, analogous to the bounds
in `Interval/Misc/TrigBounds.lean` for `sin` and `cos`.
-/

open Set Finset
open scoped Real

/-!
### Taylor series with remainder for `arctan`

The Taylor series for `arctan` is an alternating series:
  `arctan(x) = Σ_{n=0}^∞ (-1)^n * x^(2n+1) / (2n+1)`

We provide a bound using the geometric series.
-/

/-- A computational error bound for arctan's Taylor series.
    For `|x| ≤ r < 1`, we have a bound in terms of r.
    This uses a geometric series bound which is looser than the optimal
    alternating series bound, but easier to prove and sufficient for interval arithmetic. -/
lemma Real.arctan_series_bound {x : ℝ} (r : ℚ) (xr : |x| ≤ r) (r1 : r < 1) (n : ℕ) :
    |Real.arctan x - ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ↑(2 * k + 1)| ≤
      (r : ℝ) ^ (2 * n + 1) / (1 - r ^ 2) := by
  -- The key insight: we use norm_sub_le_of_geometric_bound_of_hasSum with ratio r²
  -- Each term |(-1)^k * x^(2k+1) / (2k+1)| ≤ |x|^(2k+1) ≤ r^(2k+1) = r * (r²)^k
  have hr2 : (r : ℝ) ^ 2 < 1 := by
    have h : (r : ℝ) < 1 := by exact_mod_cast r1
    have hr_nonneg : 0 ≤ (r : ℝ) := by
      calc (0 : ℝ) ≤ |x| := abs_nonneg x
        _ ≤ r := xr
    nlinarith [sq_nonneg r, sq_nonneg (1 - r)]
  have hx1 : ‖x‖ < 1 := by
    calc ‖x‖ = |x| := Real.norm_eq_abs x
      _ ≤ r := xr
      _ < 1 := by exact_mod_cast r1
  -- Apply the series hasSum result
  have hs := Real.hasSum_arctan hx1
  -- Each term |(-1)^k * x^(2k+1) / (2k+1)| ≤ r * (r²)^k
  have hf_bound : ∀ k : ℕ, ‖(-1 : ℝ) ^ k * x ^ (2 * k + 1) / (↑(2 * k + 1) : ℝ)‖ ≤ (r : ℝ) * ((r : ℝ) ^ 2) ^ k := by
    intro k
    simp only [Real.norm_eq_abs]
    have h1 : |(-1 : ℝ) ^ k * x ^ (2 * k + 1) / (↑(2 * k + 1) : ℝ)| =
        |x| ^ (2 * k + 1) / (↑(2 * k + 1) : ℝ) := by
      rw [abs_div, abs_mul]
      simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    rw [h1]
    have h2 : |x| ^ (2 * k + 1) / (↑(2 * k + 1) : ℝ) ≤ |x| ^ (2 * k + 1) := by
      apply div_le_self (pow_nonneg (abs_nonneg x) _)
      have : 1 ≤ (2 * k + 1 : ℕ) := Nat.one_le_iff_ne_zero.mpr (by omega)
      exact_mod_cast this
    calc |x| ^ (2 * k + 1) / (↑(2 * k + 1) : ℝ) ≤ |x| ^ (2 * k + 1) := h2
      _ ≤ (r : ℝ) ^ (2 * k + 1) := by
        apply pow_le_pow_left₀ (abs_nonneg x) xr
      _ = (r : ℝ) * ((r : ℝ) ^ 2) ^ k := by ring
  -- Apply the geometric series bound
  have hbound := norm_sub_le_of_geometric_bound_of_hasSum hr2 hf_bound hs n
  -- Convert the bound to the desired form
  calc |Real.arctan x - ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ↑(2 * k + 1)|
      = ‖Real.arctan x - ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ↑(2 * k + 1)‖ := (Real.norm_eq_abs _).symm
    _ = ‖(∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ↑(2 * k + 1)) - Real.arctan x‖ := norm_sub_rev _ _
    _ ≤ (r : ℝ) * ((r : ℝ) ^ 2) ^ n / (1 - (r : ℝ) ^ 2) := hbound
    _ = (r : ℝ) ^ (2 * n + 1) / (1 - (r : ℝ) ^ 2) := by ring
