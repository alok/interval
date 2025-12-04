import Interval.Interval.Arctan
import Interval.Interval.Sqrt

/-!
## Interval `arcsin` and `arccos`

We implement `arcsin` and `arccos` for intervals using the identity:
  `arcsin(x) = arctan(x / √(1-x²))` for |x| < 1
and handling the boundary cases ±1 separately.
-/

open Set
open scoped Real

/-!
### Arcsin implementation

For |x| < 1, we use `arcsin(x) = arctan(x / √(1-x²))`.
At the boundaries, `arcsin(±1) = ±π/2`.
-/

/-- Arcsin for a `Floating` point value -/
@[irreducible] def Floating.arcsin (x : Floating) : Interval :=
  bif x == nan then nan
  else bif x < -1 || 1 < x then nan  -- out of domain
  else bif x == 1 then Interval.pi.div2
  else bif x == -1 then -Interval.pi.div2
  else
    -- Use arcsin(x) = arctan(x / √(1-x²))
    let x_int : Interval := x
    let one_minus_x2 := 1 - x_int.sqr
    let sqrt_term := one_minus_x2.sqrt
    let ratio := x_int / sqrt_term
    ratio.arctan

/-- `Floating.arcsin` is conservative -/
@[approx] lemma Floating.approx_arcsin {a : ℝ} {x : Floating}
    (ax : approx x a) : approx x.arcsin (Real.arcsin a) := by
  rw [Floating.arcsin]
  simp only [bif_eq_if, beq_iff_eq]
  split_ifs with xn out x1 xn1 <;> try simp only [approx_nan]
  · -- x = 1
    have a1 : a = 1 := by
      simp only [x1, Floating.approx_eq_singleton Floating.one_ne_nan] at ax
      simp only [Floating.val_one] at ax
      exact ax.symm
    rw [a1, Real.arcsin_one]
    exact Interval.mem_approx_div2 Interval.approx_pi
  · -- x = -1
    have neg1_ne_nan : (-1 : Floating) ≠ nan := by decide +kernel
    have val_neg1 : (-1 : Floating).val = -1 := by
      simp only [Floating.val_neg Floating.one_ne_nan, Floating.val_one]
    have an1 : a = -1 := by
      rw [xn1] at ax
      simp only [Floating.approx_eq_singleton neg1_ne_nan, val_neg1] at ax
      linarith
    rw [an1, Real.arcsin_neg_one]
    have h := Interval.mem_approx_div2 Interval.approx_pi
    rw [Interval.approx_neg]
    simp only [neg_neg]
    exact h
  · -- Main case: -1 < x < 1
    have xnn : x ≠ nan := xn
    have val_neg1 : (-1 : Floating).val = -1 := by
      simp only [Floating.val_neg Floating.one_ne_nan, Floating.val_one]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt,
               Floating.val_lt_val, Floating.val_one] at out
    have hx_bounds : -1 ≤ x.val ∧ x.val ≤ 1 := ⟨by rw [← val_neg1]; exact out.1, out.2⟩
    have a_eq : a = x.val := by
      simp only [Floating.approx_eq_singleton xnn] at ax
      exact ax.symm
    -- Since val_inj tells us val is injective, x ≠ 1 implies x.val ≠ 1
    have hx_ne1 : x.val ≠ 1 := by
      intro h
      apply x1
      rw [← Floating.val_inj, h, Floating.val_one]
    have hx_nen1 : x.val ≠ -1 := by
      intro h
      apply xn1
      rw [← Floating.val_inj, h, val_neg1]
    have ha_bounds : a ∈ Set.Ioo (-1) 1 := by
      rw [a_eq]
      exact ⟨lt_of_le_of_ne hx_bounds.1 (Ne.symm hx_nen1),
             lt_of_le_of_ne hx_bounds.2 hx_ne1⟩
    rw [Real.arcsin_eq_arctan ha_bounds, a_eq]
    approx

/-- Arcsin for an `Interval` -/
@[irreducible] def Interval.arcsin (x : Interval) : Interval :=
  -- arcsin is monotone, so use endpoint union
  x.lo.arcsin ∪ x.hi.arcsin

/-- `Interval.arcsin` is conservative -/
@[approx] lemma Interval.approx_arcsin {a : ℝ} {x : Interval}
    (ax : approx x a) : approx x.arcsin (Real.arcsin a) := by
  rw [Interval.arcsin]
  by_cases xn : x = nan
  · simp only [xn, lo_nan, Floating.arcsin, bif_eq_if, beq_self_eq_true, ↓reduceIte, hi_nan,
      union_self, approx_nan]
  apply approx_of_mem_Icc (a := Real.arcsin x.lo.val) (c := Real.arcsin x.hi.val)
  · apply Interval.approx_union_left; approx
  · apply Interval.approx_union_right; approx
  · simp only [approx, lo_eq_nan, xn, false_or] at ax
    exact ⟨Real.monotone_arcsin ax.1, Real.monotone_arcsin ax.2⟩

/-- `Interval.arcsin` propagates `nan` -/
@[simp] lemma Interval.nan_arcsin : (nan : Interval).arcsin = nan := by
  rw [Interval.arcsin]
  simp only [lo_nan, Floating.arcsin, bif_eq_if, beq_self_eq_true, ↓reduceIte, hi_nan, union_self]

/-!
### Arccos implementation

We use the identity `arccos(x) = π/2 - arcsin(x)`.
-/

/-- Arccos for a `Floating` point value -/
@[irreducible] def Floating.arccos (x : Floating) : Interval :=
  Interval.pi.div2 - x.arcsin

/-- `Floating.arccos` is conservative -/
@[approx] lemma Floating.approx_arccos {a : ℝ} {x : Floating}
    (ax : approx x a) : approx x.arccos (Real.arccos a) := by
  rw [Floating.arccos, Real.arccos_eq_pi_div_two_sub_arcsin]
  approx

/-- Arccos for an `Interval` -/
@[irreducible] def Interval.arccos (x : Interval) : Interval :=
  -- arccos is antitone, so we swap endpoints
  x.hi.arccos ∪ x.lo.arccos

/-- `Interval.arccos` is conservative -/
@[approx] lemma Interval.approx_arccos {a : ℝ} {x : Interval}
    (ax : approx x a) : approx x.arccos (Real.arccos a) := by
  rw [Interval.arccos]
  by_cases xn : x = nan
  · simp only [xn, hi_nan, Floating.arccos, Floating.arcsin, bif_eq_if, beq_self_eq_true,
      ↓reduceIte, lo_nan, Interval.sub_nan, union_nan, approx_nan]
  apply approx_of_mem_Icc (a := Real.arccos x.hi.val) (c := Real.arccos x.lo.val)
  · apply Interval.approx_union_left; approx
  · apply Interval.approx_union_right; approx
  · simp only [approx, lo_eq_nan, xn, false_or] at ax
    exact ⟨Real.antitone_arccos ax.2, Real.antitone_arccos ax.1⟩

/-- `Interval.arccos` propagates `nan` -/
@[simp] lemma Interval.nan_arccos : (nan : Interval).arccos = nan := by
  rw [Interval.arccos]
  simp only [hi_nan, Floating.arccos, Floating.arcsin, bif_eq_if, beq_self_eq_true, ↓reduceIte,
    lo_nan, Interval.sub_nan, union_nan]
