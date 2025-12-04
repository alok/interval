import Interval.Interval.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
## Interval `atan2`

We implement `atan2(y, x)` for intervals using `Complex.arg`.

`atan2(y, x)` returns the angle θ ∈ (-π, π] such that `x = r cos θ` and `y = r sin θ`.
This is `Complex.arg ⟨x, y⟩` in mathlib.

The function has a branch cut along the negative real axis (x < 0, y = 0), where
the value jumps from π (y → 0⁺) to -π (y → 0⁻).
-/

open Set
open scoped Real

/-!
### `atan2` definition
-/

/-- `atan2 y x` is the angle θ ∈ (-π, π] such that x = r cos θ, y = r sin θ.
    This is `Complex.arg ⟨x, y⟩`. -/
noncomputable def Real.atan2 (y x : ℝ) : ℝ := Complex.arg ⟨x, y⟩

@[simp] lemma Real.atan2_zero_zero : Real.atan2 0 0 = 0 := Complex.arg_zero

lemma Real.atan2_mem_Ioc (y x : ℝ) : Real.atan2 y x ∈ Ioc (-π) π :=
  Complex.arg_mem_Ioc _

/-!
### Helper lemmas connecting `Complex.arg` to `arctan`

These lemmas express `Complex.arg` in terms of `Real.arctan` for the different
quadrants, which is more useful for interval arithmetic.
-/

/-- When x > 0, atan2(y, x) = arctan(y/x) -/
lemma Real.atan2_of_pos {y x : ℝ} (hx : 0 < x) :
    Real.atan2 y x = Real.arctan (y / x) := by
  unfold Real.atan2
  -- Complex.arg uses arcsin internally, but tan(arg z) = z.im / z.re
  -- For x > 0, arg is in (-π/2, π/2) where arctan is the inverse of tan
  have h_re_pos : (0 : ℝ) < (⟨x, y⟩ : ℂ).re := by simp [hx]
  have h_lt : Complex.arg ⟨x, y⟩ < π / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl h_re_pos)
  have h_gt : -(π / 2) < Complex.arg ⟨x, y⟩ :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl h_re_pos)
  have h_tan : Real.tan (Complex.arg ⟨x, y⟩) = y / x := by
    rw [Complex.tan_arg]
  rw [← h_tan, Real.arctan_tan h_gt h_lt]

/-- When x < 0 and y ≥ 0, atan2(y, x) = arctan(y/x) + π -/
lemma Real.atan2_of_neg_of_nonneg {y x : ℝ} (hx : x < 0) (hy : 0 ≤ y) :
    Real.atan2 y x = Real.arctan (y / x) + π := by
  unfold Real.atan2
  have h_re : (⟨x, y⟩ : ℂ).re < 0 := by simp [hx]
  have h_im : 0 ≤ (⟨x, y⟩ : ℂ).im := by simp [hy]
  rw [Complex.arg_of_re_neg_of_im_nonneg h_re h_im]
  congr 1
  -- Need: arcsin((-⟨x,y⟩).im / ‖⟨x,y⟩‖) = arctan(y/x)
  simp only [Complex.neg_im]
  rw [Real.arctan_eq_arcsin]
  congr 1
  -- Need: -y / ‖⟨x,y⟩‖ = (y/x) / √(1 + (y/x)²)
  have norm_eq : ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; ring
  rw [norm_eq]
  have hx_ne : x ≠ 0 := ne_of_lt hx
  have sqrt_one_plus : Real.sqrt (1 + (y / x) ^ 2) = Real.sqrt (x ^ 2 + y ^ 2) / (-x) := by
    have h1 : 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 := by field_simp
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_neg hx]
  rw [sqrt_one_plus]
  field_simp

/-- When x < 0 and y < 0, atan2(y, x) = arctan(y/x) - π -/
lemma Real.atan2_of_neg_of_neg {y x : ℝ} (hx : x < 0) (hy : y < 0) :
    Real.atan2 y x = Real.arctan (y / x) - π := by
  unfold Real.atan2
  have h_re : (⟨x, y⟩ : ℂ).re < 0 := by simp [hx]
  have h_im : (⟨x, y⟩ : ℂ).im < 0 := by simp [hy]
  rw [Complex.arg_of_re_neg_of_im_neg h_re h_im]
  congr 1
  -- Need: arcsin((-⟨x,y⟩).im / ‖⟨x,y⟩‖) = arctan(y/x)
  simp only [Complex.neg_im]
  rw [Real.arctan_eq_arcsin]
  congr 1
  -- Need: -y / ‖⟨x,y⟩‖ = (y/x) / √(1 + (y/x)²)
  have norm_eq : ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; ring
  rw [norm_eq]
  have hx_ne : x ≠ 0 := ne_of_lt hx
  have sqrt_one_plus : Real.sqrt (1 + (y / x) ^ 2) = Real.sqrt (x ^ 2 + y ^ 2) / (-x) := by
    have h1 : 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 := by field_simp
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_neg hx]
  rw [sqrt_one_plus]
  field_simp

/-- When x = 0 and y > 0, atan2(y, 0) = π/2 -/
lemma Real.atan2_of_zero_of_pos {y : ℝ} (hy : 0 < y) :
    Real.atan2 y 0 = π / 2 := by
  unfold Real.atan2
  have h : (⟨0, y⟩ : ℂ) = ↑y * Complex.I := by
    apply Complex.ext <;> simp
  rw [h, Complex.arg_real_mul _ hy, Complex.arg_I]

/-- When x = 0 and y < 0, atan2(y, 0) = -π/2 -/
lemma Real.atan2_of_zero_of_neg {y : ℝ} (hy : y < 0) :
    Real.atan2 y 0 = -π / 2 := by
  unfold Real.atan2
  have h : (⟨0, y⟩ : ℂ) = ↑(-y) * (-Complex.I) := by
    apply Complex.ext <;> simp [neg_neg]
  rw [h, Complex.arg_real_mul _ (by linarith : 0 < -y), Complex.arg_neg_I]
  ring

/-- When y = 0 and x < 0, atan2(0, x) = π -/
@[simp] lemma Real.atan2_zero_neg {x : ℝ} (hx : x < 0) :
    Real.atan2 0 x = π := by
  unfold Real.atan2
  have h : (⟨x, 0⟩ : ℂ) = ↑(-x) * (-1 : ℂ) := by
    apply Complex.ext <;> simp [neg_neg]
  rw [h, Complex.arg_real_mul _ (by linarith : 0 < -x), Complex.arg_neg_one]

/-!
### Monotonicity of atan2

We prove that atan2 has specific monotonicity properties in different regions.
-/

/-- For x > 0, atan2 is monotone in y -/
lemma Real.atan2_mono_left_of_pos {a b x : ℝ} (hx : 0 < x) (hab : a ≤ b) :
    Real.atan2 a x ≤ Real.atan2 b x := by
  unfold Real.atan2
  have ha_re_pos : (0 : ℝ) < (⟨x, a⟩ : ℂ).re := by simp [hx]
  have hb_re_pos : (0 : ℝ) < (⟨x, b⟩ : ℂ).re := by simp [hx]
  have ha_arg : Complex.arg ⟨x, a⟩ = Real.arctan (a / x) := by
    have h_lt : Complex.arg ⟨x, a⟩ < π / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl ha_re_pos)
    have h_gt : -(π / 2) < Complex.arg ⟨x, a⟩ := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl ha_re_pos)
    have h_tan : Real.tan (Complex.arg ⟨x, a⟩) = a / x := by rw [Complex.tan_arg]
    rw [← h_tan, Real.arctan_tan h_gt h_lt]
  have hb_arg : Complex.arg ⟨x, b⟩ = Real.arctan (b / x) := by
    have h_lt : Complex.arg ⟨x, b⟩ < π / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hb_re_pos)
    have h_gt : -(π / 2) < Complex.arg ⟨x, b⟩ := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hb_re_pos)
    have h_tan : Real.tan (Complex.arg ⟨x, b⟩) = b / x := by rw [Complex.tan_arg]
    rw [← h_tan, Real.arctan_tan h_gt h_lt]
  rw [ha_arg, hb_arg]
  apply Real.arctan_mono
  exact div_le_div_of_nonneg_right hab hx.le

/-- On x > 0, atan2 is monotone as a function of y -/
lemma Real.atan2_monotone_left_of_pos {x : ℝ} (hx : 0 < x) :
    Monotone (fun y => Real.atan2 y x) :=
  fun _ _ hab => Real.atan2_mono_left_of_pos hx hab

/-- For y ≥ 0 and x > 0, atan2 is antitone in x -/
lemma Real.atan2_anti_right_of_nonneg_of_pos {y a b : ℝ} (hy : 0 ≤ y) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) : Real.atan2 y b ≤ Real.atan2 y a := by
  rw [Real.atan2_of_pos ha, Real.atan2_of_pos hb]
  apply Real.arctan_mono
  exact div_le_div_of_nonneg_left hy ha hab

/-- For y ≤ 0 and x > 0, atan2 is monotone in x -/
lemma Real.atan2_mono_right_of_nonpos_of_pos {y a b : ℝ} (hy : y ≤ 0) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) : Real.atan2 y a ≤ Real.atan2 y b := by
  rw [Real.atan2_of_pos ha, Real.atan2_of_pos hb]
  apply Real.arctan_mono
  have hy' : 0 ≤ -y := by linarith
  have h1 : y / a = -(-y / a) := by ring
  have h2 : y / b = -(-y / b) := by ring
  rw [h1, h2]
  apply neg_le_neg
  exact div_le_div_of_nonneg_left hy' ha hab

/-- For x < 0 and y ≥ 0, atan2 is antitone in y -/
lemma Real.atan2_anti_left_of_neg_of_nonneg {a b x : ℝ} (hx : x < 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≤ b) : Real.atan2 b x ≤ Real.atan2 a x := by
  by_cases hb0 : b = 0
  · -- b = 0 implies a = 0 since 0 ≤ a ≤ b = 0
    have ha0 : a = 0 := le_antisymm (hb0 ▸ hab) ha
    simp only [hb0, ha0, le_refl]
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases ha0 : a = 0
  · simp only [ha0]
    rw [Real.atan2_of_neg_of_nonneg hx hb]
    -- Real.atan2 0 x = Complex.arg ⟨x, 0⟩ = Complex.arg ↑x = π when x < 0
    have arg_eq : Real.atan2 0 x = π := by
      unfold Real.atan2
      have : (⟨x, 0⟩ : ℂ) = ↑x := rfl
      rw [this, Complex.arg_ofReal_of_neg hx]
    rw [arg_eq]
    have arctan_neg : Real.arctan (b / x) < 0 := by
      rw [Real.arctan_lt_zero]
      exact div_neg_of_pos_of_neg hb_pos hx
    linarith
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  rw [Real.atan2_of_neg_of_nonneg hx ha_pos.le, Real.atan2_of_neg_of_nonneg hx hb]
  apply add_le_add_right
  apply Real.arctan_mono
  -- b/x ≤ a/x when x < 0 and a ≤ b
  rw [div_le_div_right_of_neg hx]
  exact hab

/-- For x < 0 and both y values strictly negative, atan2 is antitone in y -/
lemma Real.atan2_anti_left_of_neg_of_neg {a b x : ℝ} (hx : x < 0) (ha : a < 0) (hb : b < 0)
    (hab : a ≤ b) : Real.atan2 b x ≤ Real.atan2 a x := by
  rw [Real.atan2_of_neg_of_neg hx ha, Real.atan2_of_neg_of_neg hx hb]
  apply sub_le_sub_right
  apply Real.arctan_mono
  rw [div_le_div_right_of_neg hx]
  exact hab

/-- For x < 0 and y ≥ 0, atan2 is anti-monotone in x (larger x = smaller atan2) -/
lemma Real.atan2_anti_right_of_nonneg_of_neg {y a b : ℝ} (hy : 0 ≤ y) (ha : a < 0) (hb : b < 0)
    (hab : a ≤ b) : Real.atan2 y b ≤ Real.atan2 y a := by
  rw [Real.atan2_of_neg_of_nonneg ha hy, Real.atan2_of_neg_of_nonneg hb hy]
  apply add_le_add_right
  apply Real.arctan_mono
  -- Need: y/b ≤ y/a when a ≤ b < 0 and y ≥ 0
  -- y/a and y/b are both ≤ 0 (y ≥ 0, a,b < 0)
  -- a ≤ b < 0 means |a| ≥ |b|
  -- y/b = -y/|b|, y/a = -y/|a|
  -- Since |a| ≥ |b|, we have y/|b| ≥ y/|a|, so -y/|b| ≤ -y/|a|, i.e., y/b ≤ y/a ✓
  by_cases hy0 : y = 0
  · simp [hy0]
  · -- Need y/b ≤ y/a when y > 0 and a ≤ b < 0
    -- Since a ≤ b < 0, we have 1/b ≤ 1/a (both negative)
    -- Since y > 0, y/b = y * (1/b) ≤ y * (1/a) = y/a ✓
    have hy_pos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have h1 : (1 : ℝ) / b ≤ 1 / a := (one_div_le_one_div_of_neg hb ha).mpr hab
    calc y / b = y * (1 / b) := by rw [mul_one_div]
      _ ≤ y * (1 / a) := by apply mul_le_mul_of_nonneg_left h1 hy_pos.le
      _ = y / a := by rw [mul_one_div]

/-- For x < 0 and y < 0, atan2 is monotone in x (larger x = larger atan2) -/
lemma Real.atan2_mono_right_of_neg_of_neg {y a b : ℝ} (hy : y < 0) (ha : a < 0) (hb : b < 0)
    (hab : a ≤ b) : Real.atan2 y a ≤ Real.atan2 y b := by
  rw [Real.atan2_of_neg_of_neg ha hy, Real.atan2_of_neg_of_neg hb hy]
  apply sub_le_sub_right
  apply Real.arctan_mono
  -- Need: y/a ≤ y/b when a ≤ b < 0 and y < 0
  -- y/a and y/b are both > 0 (y < 0, a,b < 0)
  -- a ≤ b < 0 means |a| ≥ |b|
  -- Since a ≤ b < 0, we have 1/a ≥ 1/b (both negative)
  -- Since y < 0, y * (1/a) ≤ y * (1/b), i.e., y/a ≤ y/b ✓
  have h1 : (1 : ℝ) / a ≥ 1 / b := (one_div_le_one_div_of_neg hb ha).mpr hab
  calc y / a = y * (1 / a) := by rw [mul_one_div]
    _ ≤ y * (1 / b) := by apply mul_le_mul_of_nonpos_left h1 hy.le
    _ = y / b := by rw [mul_one_div]

/-!
### Sign and bound lemmas for atan2
-/

/-- For y ≥ 0 and x < 0 (second quadrant), atan2 is in [π/2, π] -/
lemma Real.pi_div_two_le_atan2_of_neg_of_nonneg {y x : ℝ} (hx : x < 0) (hy : 0 ≤ y) :
    π / 2 ≤ Real.atan2 y x := by
  by_cases hy0 : y = 0
  · -- atan2(0, x) = π when x < 0
    subst hy0
    unfold Real.atan2
    have : (⟨x, 0⟩ : ℂ) = ↑x := rfl
    rw [this, Complex.arg_ofReal_of_neg hx]
    linarith [Real.pi_pos]
  · have hy_pos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [Real.atan2_of_neg_of_nonneg hx hy_pos.le]
    have arctan_bound : -(π / 2) < Real.arctan (y / x) := Real.neg_pi_div_two_lt_arctan _
    linarith

/-- For y ≥ 0 and x < 0 (second quadrant), atan2 is nonnegative -/
lemma Real.atan2_nonneg_of_nonneg_of_neg {y x : ℝ} (hy : 0 ≤ y) (hx : x < 0) :
    0 ≤ Real.atan2 y x := by
  have h := Real.pi_div_two_le_atan2_of_neg_of_nonneg hx hy
  linarith [Real.pi_pos]

/-- For y < 0 and x > 0 (fourth quadrant), atan2 is negative -/
lemma Real.atan2_neg_of_neg_of_pos {y x : ℝ} (hy : y < 0) (hx : 0 < x) :
    Real.atan2 y x < 0 := by
  rw [Real.atan2_of_pos hx]
  rw [Real.arctan_lt_zero]
  exact div_neg_of_neg_of_pos hy hx

/-- For y ≤ 0 and x > 0 (fourth quadrant or positive x-axis), atan2 ≤ 0 -/
lemma Real.atan2_nonpos_of_nonpos_of_pos {y x : ℝ} (hy : y ≤ 0) (hx : 0 < x) :
    Real.atan2 y x ≤ 0 := by
  by_cases hy0 : y = 0
  · simp [hy0, Real.atan2_of_pos hx]
  · exact le_of_lt (Real.atan2_neg_of_neg_of_pos (lt_of_le_of_ne hy hy0) hx)

/-- For y ≥ 0 and x > 0 (first quadrant or positive x-axis), atan2 ≥ 0 -/
lemma Real.atan2_nonneg_of_nonneg_of_pos {y x : ℝ} (hy : 0 ≤ y) (hx : 0 < x) :
    0 ≤ Real.atan2 y x := by
  rw [Real.atan2_of_pos hx]
  exact Real.arctan_nonneg.mpr (div_nonneg hy hx.le)

/-- For y ≥ 0 and x > 0 (first quadrant), atan2 ≤ π/2 -/
lemma Real.atan2_le_pi_div_two_of_pos {y x : ℝ} (hx : 0 < x) :
    Real.atan2 y x ≤ π / 2 := by
  rw [Real.atan2_of_pos hx]
  exact le_of_lt (Real.arctan_lt_pi_div_two _)

/-- For x > 0, atan2 y x > -π/2 -/
lemma Real.neg_pi_div_two_lt_atan2_of_pos {y x : ℝ} (hx : 0 < x) :
    -π / 2 < Real.atan2 y x := by
  rw [Real.atan2_of_pos hx]
  have h := Real.neg_pi_div_two_lt_arctan (y / x)
  linarith

/-- For y < 0 and x < 0 (third quadrant), atan2 y x < -π/2 -/
lemma Real.atan2_lt_neg_pi_div_two_of_neg_of_neg {y x : ℝ} (hy : y < 0) (hx : x < 0) :
    Real.atan2 y x < -π / 2 := by
  rw [Real.atan2_of_neg_of_neg hx hy]
  -- arctan(y/x) - π where y/x > 0, so arctan(y/x) ∈ (0, π/2)
  have hyx_pos : 0 < y / x := div_pos_of_neg_of_neg hy hx
  have arctan_pos : 0 < Real.arctan (y / x) := Real.arctan_pos.mpr hyx_pos
  have arctan_bound : Real.arctan (y / x) < π / 2 := Real.arctan_lt_pi_div_two _
  linarith

/-- For a rectangle in the right half-plane (x > 0), atan2 is bounded below by a corner -/
lemma Real.atan2_rect_lower_bound_pos {ay ax y_lo y_hi x_lo x_hi : ℝ}
    (hy_lo : y_lo ≤ ay) (hy_hi : ay ≤ y_hi) (hx_lo : x_lo ≤ ax) (hx_hi : ax ≤ x_hi)
    (hx_pos : 0 < x_lo) :
    min (min (Real.atan2 y_lo x_lo) (Real.atan2 y_lo x_hi))
        (min (Real.atan2 y_hi x_lo) (Real.atan2 y_hi x_hi)) ≤ Real.atan2 ay ax := by
  -- In right half-plane, atan2(y, x) = arctan(y/x)
  -- atan2 is increasing in y, and either increasing or decreasing in x depending on y's sign
  simp only [min_le_iff, le_min_iff]
  have hx_lo_pos : 0 < x_lo := hx_pos
  have hx_hi_pos : 0 < x_hi := lt_of_lt_of_le hx_pos (le_trans hx_lo hx_hi)
  have hax_pos : 0 < ax := lt_of_lt_of_le hx_pos hx_lo
  by_cases hay_nonneg : 0 ≤ ay
  · -- ay ≥ 0: atan2 is increasing in y, decreasing in x
    -- min is at (y_lo, x_hi)
    left; right
    calc Real.atan2 y_lo x_hi
        ≤ Real.atan2 ay x_hi := Real.atan2_mono_left_of_pos hx_hi_pos hy_lo
      _ ≤ Real.atan2 ay ax := Real.atan2_anti_right_of_nonneg_of_pos hay_nonneg hax_pos hx_hi_pos hx_hi
  · -- ay < 0: atan2 is increasing in y, increasing in x
    -- min is at (y_lo, x_lo)
    push_neg at hay_nonneg
    left; left
    calc Real.atan2 y_lo x_lo
        ≤ Real.atan2 ay x_lo := Real.atan2_mono_left_of_pos hx_lo_pos hy_lo
      _ ≤ Real.atan2 ay ax := Real.atan2_mono_right_of_nonpos_of_pos hay_nonneg.le hx_lo_pos hax_pos hx_lo

/-- For a rectangle in the right half-plane (x > 0), atan2 is bounded above by a corner -/
lemma Real.atan2_rect_upper_bound_pos {ay ax y_lo y_hi x_lo x_hi : ℝ}
    (hy_lo : y_lo ≤ ay) (hy_hi : ay ≤ y_hi) (hx_lo : x_lo ≤ ax) (hx_hi : ax ≤ x_hi)
    (hx_pos : 0 < x_lo) :
    Real.atan2 ay ax ≤ max (max (Real.atan2 y_lo x_lo) (Real.atan2 y_lo x_hi))
        (max (Real.atan2 y_hi x_lo) (Real.atan2 y_hi x_hi)) := by
  simp only [le_max_iff, max_le_iff]
  have hx_lo_pos : 0 < x_lo := hx_pos
  have hx_hi_pos : 0 < x_hi := lt_of_lt_of_le hx_pos (le_trans hx_lo hx_hi)
  have hax_pos : 0 < ax := lt_of_lt_of_le hx_pos hx_lo
  by_cases hay_nonpos : ay ≤ 0
  · -- ay ≤ 0: atan2 is increasing in y, increasing in x
    -- max is at (y_hi, x_hi)
    right; right
    calc Real.atan2 ay ax
        ≤ Real.atan2 ay x_hi := Real.atan2_mono_right_of_nonpos_of_pos hay_nonpos hax_pos hx_hi_pos hx_hi
      _ ≤ Real.atan2 y_hi x_hi := Real.atan2_mono_left_of_pos hx_hi_pos hy_hi
  · -- ay > 0: atan2 is increasing in y, decreasing in x
    -- max is at (y_hi, x_lo)
    push_neg at hay_nonpos
    right; left
    calc Real.atan2 ay ax
        ≤ Real.atan2 ay x_lo := Real.atan2_anti_right_of_nonneg_of_pos hay_nonpos.le hx_lo_pos hax_pos hx_lo
      _ ≤ Real.atan2 y_hi x_lo := Real.atan2_mono_left_of_pos hx_lo_pos hy_hi

/-!
### Interval `atan2`
-/

/-- `atan2` for `Floating` point values -/
@[irreducible] def Floating.atan2 (y x : Floating) : Interval :=
  bif y == nan || x == nan then nan
  else bif 0 < x then
    -- x > 0: atan2(y, x) = arctan(y/x)
    ((y : Interval) / x).arctan
  else bif x < 0 then
    -- x < 0: atan2(y, x) = arctan(y/x) ± π
    let base := ((y : Interval) / x).arctan
    bif 0 ≤ y then base + Interval.pi
    else base - Interval.pi
  else
    -- x = 0
    bif 0 < y then Interval.pi.div2
    else bif y < 0 then -Interval.pi.div2
    else nan  -- atan2(0, 0) is undefined

-- Note: The lemma `Floating.atan2_ne_nan_of_pos` was originally conjectured here, but
-- Aristotle proved it is FALSE. The interval division can produce nan for extreme
-- floating-point values (very large or denormalized numbers) even when both inputs
-- are non-nan. The proofs below handle the nan case separately.

/-- `Floating.atan2` is conservative -/
@[approx] lemma Floating.approx_atan2 {ay ax : ℝ} {y x : Floating}
    (hy : approx y ay) (hx : approx x ax) :
    approx (Floating.atan2 y x) (Real.atan2 ay ax) := by
  rw [Floating.atan2]
  simp only [bif_eq_if, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
  by_cases hnan : y = nan ∨ x = nan
  · simp only [hnan, ite_true, approx_nan]
  simp only [hnan, ite_false]
  push_neg at hnan
  have xnn : x ≠ nan := hnan.2
  have ynn : y ≠ nan := hnan.1
  simp only [Floating.approx_eq_singleton xnn] at hx
  simp only [Floating.approx_eq_singleton ynn] at hy
  by_cases hxpos : 0 < x
  · -- x > 0: atan2(y, x) = arctan(y/x)
    simp only [hxpos, ite_true]
    have ax_pos : 0 < ax := by
      have h := Floating.val_lt_val.mp hxpos
      simp only [Floating.val_zero] at h
      rw [← hx]; exact h
    rw [Real.atan2_of_pos ax_pos]
    approx
  simp only [hxpos, ite_false]
  by_cases hxneg : x < 0
  · -- x < 0
    simp only [hxneg, ite_true]
    have ax_neg : ax < 0 := by
      have h := Floating.val_lt_val.mp hxneg
      simp only [Floating.val_zero] at h
      rw [← hx]; exact h
    by_cases hypos : 0 ≤ y
    · -- y ≥ 0
      simp only [hypos, ite_true]
      have ay_nonneg : 0 ≤ ay := by
        have h := Floating.val_le_val.mp hypos
        simp only [Floating.val_zero] at h
        rw [← hy]; exact h
      rw [Real.atan2_of_neg_of_nonneg ax_neg ay_nonneg]
      approx
    · -- y < 0
      simp only [hypos, ite_false]
      push_neg at hypos
      have ay_neg : ay < 0 := by
        have h := Floating.val_lt_val.mp hypos
        simp only [Floating.val_zero] at h
        rw [← hy]; exact h
      rw [Real.atan2_of_neg_of_neg ax_neg ay_neg]
      approx
  simp only [hxneg, ite_false]
  -- x = 0
  have hx_nonneg : 0 ≤ x := le_of_not_gt hxneg
  have hx_nonpos : x ≤ 0 := le_of_not_gt hxpos
  have ax_zero : ax = 0 := by
    have h1 := Floating.val_le_val.mp hx_nonneg
    have h2 := Floating.val_le_val.mp hx_nonpos
    simp only [Floating.val_zero] at h1 h2
    rw [← hx]
    linarith
  by_cases hypos : 0 < y
  · -- y > 0
    simp only [hypos, ite_true]
    have ay_pos : 0 < ay := by
      have h := Floating.val_lt_val.mp hypos
      simp only [Floating.val_zero] at h
      rw [← hy]; exact h
    rw [ax_zero, Real.atan2_of_zero_of_pos ay_pos]
    exact Interval.mem_approx_div2 Interval.approx_pi
  simp only [hypos, ite_false]
  by_cases hyneg : y < 0
  · -- y < 0
    simp only [hyneg, ite_true]
    have ay_neg : ay < 0 := by
      have h := Floating.val_lt_val.mp hyneg
      simp only [Floating.val_zero] at h
      rw [← hy]; exact h
    rw [ax_zero, Real.atan2_of_zero_of_neg ay_neg, neg_div, Interval.approx_neg, neg_neg]
    exact Interval.mem_approx_div2 Interval.approx_pi
  · -- y = 0
    simp only [hyneg, ite_false]
    -- ay = 0 and ax = 0, so atan2(0, 0) = 0
    have ay_zero : ay = 0 := by
      have hy_nonneg : 0 ≤ y := le_of_not_gt hyneg
      have hy_nonpos : y ≤ 0 := le_of_not_gt hypos
      have h1 := Floating.val_le_val.mp hy_nonneg
      have h2 := Floating.val_le_val.mp hy_nonpos
      simp only [Floating.val_zero] at h1 h2
      rw [← hy]
      linarith
    simp only [ax_zero, ay_zero, Real.atan2_zero_zero, approx_nan]

/-- `atan2` for `Interval` values.
    We compute atan2 at the four corners and take their hull.
    For the branch cut case (x < 0 and y crosses 0), we return nan to be conservative. -/
@[irreducible] def Interval.atan2 (y x : Interval) : Interval :=
  -- Handle the branch cut: atan2 is discontinuous at (x < 0, y = 0).
  -- If x reaches negative values and y crosses zero (or the rectangle spans
  -- both third quadrant and another region), the 4-corner approach is unsound.
  -- Return nan in these cases to be conservative.
  -- Condition: x.lo < 0 (x reaches left half-plane) AND y.lo < 0 (y reaches negative)
  -- AND y.hi >= 0 (y reaches non-negative, so y crosses or touches 0)
  bif x.lo < 0 && y.lo < 0 && 0 ≤ y.hi then nan
  else
    (Floating.atan2 y.lo x.lo ∪ Floating.atan2 y.lo x.hi) ∪
    (Floating.atan2 y.hi x.lo ∪ Floating.atan2 y.hi x.hi)

/-- `Interval.atan2` is conservative -/
@[approx] lemma Interval.approx_atan2 {ay ax : ℝ} {y x : Interval}
    (hy : approx y ay) (hx : approx x ax) :
    approx (Interval.atan2 y x) (Real.atan2 ay ax) := by
  rw [Interval.atan2]
  -- First handle the branch cut case: if x.hi < 0 && y.lo < 0 && 0 < y.hi, return nan
  simp only [bif_eq_if, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs with hbc
  · -- Branch cut case: return nan
    simp only [approx, lo_nan, hi_nan, true_or]
  -- Non-branch cut case: continue with 4-corner proof
  by_cases hyn : y = nan
  · simp only [hyn, lo_nan, hi_nan, Floating.atan2, bif_eq_if, beq_self_eq_true,
      Bool.true_or, ite_true, union_self, approx_nan]
  by_cases hxn : x = nan
  · simp only [hxn, lo_nan, hi_nan]
    simp only [Floating.atan2, bif_eq_if, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
    have hlo : y.lo ≠ nan := lo_ne_nan hyn
    have hhi : y.hi ≠ nan := hi_ne_nan hyn
    simp only [hlo, hhi, false_or, ite_true, union_self, approx_nan]
  -- The four corners bound the result via continuity of atan2.
  -- Mathematical claim: For (ay, ax) in rectangle [y.lo.val, y.hi.val] × [x.lo.val, x.hi.val],
  -- Real.atan2 ay ax ∈ [min(corner atan2 values), max(corner atan2 values)].
  -- This holds because:
  -- 1. atan2 is continuous except at the branch cut (x < 0, y = 0)
  -- 2. On any compact rectangle, continuous functions achieve extrema on the boundary
  -- 3. On edges, atan2 is monotonic in the free variable, so extrema are at corners
  -- 4. At the branch cut, values are ±π, which are achieved at corners when y straddles 0
  -- The implementation uses the union of 4 corner intervals, which is conservative.
  simp only [approx, lo_eq_nan, hyn, hxn, lo_union, hi_union, false_or] at hy hx ⊢
  have hlo_y := lo_ne_nan hyn
  have hhi_y := hi_ne_nan hyn
  have hlo_x := lo_ne_nan hxn
  have hhi_x := hi_ne_nan hxn
  -- Get the corner interval approximations
  have c1 : approx (y.lo.atan2 x.lo) (Real.atan2 y.lo.val x.lo.val) :=
    Floating.approx_atan2 Floating.approx_val Floating.approx_val
  have c2 : approx (y.lo.atan2 x.hi) (Real.atan2 y.lo.val x.hi.val) :=
    Floating.approx_atan2 Floating.approx_val Floating.approx_val
  have c3 : approx (y.hi.atan2 x.lo) (Real.atan2 y.hi.val x.lo.val) :=
    Floating.approx_atan2 Floating.approx_val Floating.approx_val
  have c4 : approx (y.hi.atan2 x.hi) (Real.atan2 y.hi.val x.hi.val) :=
    Floating.approx_atan2 Floating.approx_val Floating.approx_val
  -- Define the 4-way union
  let u := (y.lo.atan2 x.lo ∪ y.lo.atan2 x.hi) ∪ (y.hi.atan2 x.lo ∪ y.hi.atan2 x.hi)
  -- Show the union contains all 4 corner values
  have u1 : approx u (Real.atan2 y.lo.val x.lo.val) :=
    approx_union_left (approx_union_left c1)
  have u2 : approx u (Real.atan2 y.lo.val x.hi.val) :=
    approx_union_left (approx_union_right c2)
  have u3 : approx u (Real.atan2 y.hi.val x.lo.val) :=
    approx_union_right (approx_union_left c3)
  have u4 : approx u (Real.atan2 y.hi.val x.hi.val) :=
    approx_union_right (approx_union_right c4)
  -- Strategy: Use approx_of_mem_Icc with corner bounds
  -- The union of 4 corners contains all corner atan2 values
  -- By rect bounds lemmas, Real.atan2 ay ax is in [min corner, max corner]
  -- Case analysis on the position of ax
  by_cases hx_pos : 0 < x.lo.val
  · -- x.lo.val > 0: entire rectangle in right half-plane
    -- Use the rect bounds lemmas
    have lb := Real.atan2_rect_lower_bound_pos hy.1 hy.2 hx.1 hx.2 hx_pos
    have ub := Real.atan2_rect_upper_bound_pos hy.1 hy.2 hx.1 hx.2 hx_pos
    -- Find which corners give min and max
    have min_corner : min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) ∈
        ({Real.atan2 y.lo.val x.lo.val, Real.atan2 y.lo.val x.hi.val,
          Real.atan2 y.hi.val x.lo.val, Real.atan2 y.hi.val x.hi.val} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, min_def]
      split_ifs <;> simp
    have max_corner : max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) ∈
        ({Real.atan2 y.lo.val x.lo.val, Real.atan2 y.lo.val x.hi.val,
          Real.atan2 y.hi.val x.lo.val, Real.atan2 y.hi.val x.hi.val} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, max_def]
      split_ifs <;> simp
    -- The union contains min and max corners
    have u_min : approx u (min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                               (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at min_corner
      rcases min_corner with h | h | h | h <;> simp only [h, u1, u2, u3, u4]
    have u_max : approx u (max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                               (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at max_corner
      rcases max_corner with h | h | h | h <;> simp only [h, u1, u2, u3, u4]
    -- Real.atan2 ay ax is in [min corner, max corner]
    have in_range : Real.atan2 ay ax ∈ Set.Icc
        (min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
             (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)))
        (max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
             (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))) :=
      ⟨lb, ub⟩
    -- By ApproxConnected, the union contains atan2 ay ax
    have u_result : approx u (Real.atan2 ay ax) := approx_of_mem_Icc u_min u_max in_range
    -- The goal is `(min = nan) ∨ bounds`, which is exactly what u_result gives us after simp
    simp only [approx, lo_eq_nan, lo_union, hi_union, u] at u_result
    exact u_result
  · -- x.lo.val ≤ 0: may cross y-axis or be in left half-plane
    -- This case involves the branch cut and requires more careful analysis
    -- For rectangles crossing the y-axis or in the left half-plane,
    -- the 4-corner approach is still conservative but proving it requires
    -- additional monotonicity lemmas for each region
    -- For now, we use the same approx_of_mem_Icc structure
    -- TODO: Add full proof for left half-plane and y-axis crossing cases
    have min_corner : min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) ∈
        ({Real.atan2 y.lo.val x.lo.val, Real.atan2 y.lo.val x.hi.val,
          Real.atan2 y.hi.val x.lo.val, Real.atan2 y.hi.val x.hi.val} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, min_def]
      split_ifs <;> simp
    have max_corner : max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) ∈
        ({Real.atan2 y.lo.val x.lo.val, Real.atan2 y.lo.val x.hi.val,
          Real.atan2 y.hi.val x.lo.val, Real.atan2 y.hi.val x.hi.val} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, max_def]
      split_ifs <;> simp
    have u_min : approx u (min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                               (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at min_corner
      rcases min_corner with h | h | h | h <;> simp only [h, u1, u2, u3, u4]
    have u_max : approx u (max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                               (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at max_corner
      rcases max_corner with h | h | h | h <;> simp only [h, u1, u2, u3, u4]
    -- The key claim: atan2 ay ax is bounded by corner values
    -- This requires proving that atan2 on a rectangle is bounded by corners
    -- even when crossing the y-axis or branch cut
    have lb : min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                  (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) ≤
              Real.atan2 ay ax := by
      -- Case split: is ax > 0 (right half-plane) or ax ≤ 0 (left half or y-axis)?
      by_cases hax_pos : 0 < ax
      · -- ax > 0: right half-plane, can use monotonicity
        have hx_hi_pos : 0 < x.hi.val := lt_of_lt_of_le hax_pos hx.2
        have corner_bound : ∃ c ∈ ({Real.atan2 y.lo.val x.lo.val, Real.atan2 y.lo.val x.hi.val,
              Real.atan2 y.hi.val x.lo.val, Real.atan2 y.hi.val x.hi.val} : Set ℝ),
              c ≤ Real.atan2 ay ax := by
          by_cases hay_sign : 0 ≤ ay
          · -- ay ≥ 0: corner (y.lo, x.hi) gives lower bound
            refine ⟨Real.atan2 y.lo.val x.hi.val, ?_, ?_⟩
            · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
            · calc Real.atan2 y.lo.val x.hi.val
                  ≤ Real.atan2 ay x.hi.val := Real.atan2_mono_left_of_pos hx_hi_pos hy.1
                _ ≤ Real.atan2 ay ax := Real.atan2_anti_right_of_nonneg_of_pos hay_sign hax_pos hx_hi_pos hx.2
          · -- ay < 0
            simp only [not_le] at hay_sign
            by_cases hx_lo_pos : 0 < x.lo.val
            · refine ⟨Real.atan2 y.lo.val x.lo.val, ?_, ?_⟩
              · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
              · calc Real.atan2 y.lo.val x.lo.val
                    ≤ Real.atan2 ay x.lo.val := Real.atan2_mono_left_of_pos hx_lo_pos hy.1
                  _ ≤ Real.atan2 ay ax := Real.atan2_mono_right_of_nonpos_of_pos hay_sign.le
                      hx_lo_pos hax_pos hx.1
            · -- x.lo ≤ 0 < ax: the rectangle crosses the y-axis
              -- For ay < 0, ax > 0, the third quadrant corner (y.lo, x.lo) gives minimum
              -- since atan2 in third quadrant ∈ (-π, -π/2) < atan2 in fourth ∈ (-π/2, 0)
              simp only [not_lt] at hx_lo_pos
              -- Use (y.lo, x.lo) corner - it's either in third quadrant or on negative y-axis
              refine ⟨Real.atan2 y.lo.val x.lo.val, ?_, ?_⟩
              · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
              · -- Third quadrant or y-axis corner ≤ fourth quadrant value
                -- Key insight: atan2 in third quadrant or at x=0 is ≤ -π/2,
                -- while atan2 in fourth quadrant is > -π/2
                have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_sign
                have h_corner_bound : Real.atan2 y.lo.val x.lo.val ≤ -(π / 2) := by
                  by_cases hx_lo_neg : x.lo.val < 0
                  · -- Third quadrant: atan2 < -π/2
                    rw [Real.atan2_of_neg_of_neg hx_lo_neg hy_lo_neg]
                    have h := Real.arctan_lt_pi_div_two (y.lo.val / x.lo.val)
                    linarith
                  · -- x.lo = 0: atan2(y.lo, 0) = -π/2
                    have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_lo_pos (le_of_not_gt hx_lo_neg)
                    simp only [hx_lo_zero, Real.atan2_of_zero_of_neg hy_lo_neg]
                    linarith
                have h_actual_bound : -(π / 2) < Real.atan2 ay ax := by
                  rw [Real.atan2_of_pos hax_pos]
                  exact Real.neg_pi_div_two_lt_arctan _
                linarith
        rcases corner_bound with ⟨c, hc_mem, hc_le⟩
        calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
              (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
            ≤ c := by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc_mem
              rcases hc_mem with rfl | rfl | rfl | rfl
              · exact min_le_of_left_le (min_le_left _ _)
              · exact min_le_of_left_le (min_le_right _ _)
              · exact min_le_of_right_le (min_le_left _ _)
              · exact min_le_of_right_le (min_le_right _ _)
          _ ≤ Real.atan2 ay ax := hc_le
      · -- ax ≤ 0: left half-plane or on y-axis
        simp only [not_lt] at hax_pos
        by_cases hax_neg : ax < 0
        · -- ax < 0: strictly in left half-plane
          have hx_lo_neg : x.lo.val < 0 := hx.1.trans_lt hax_neg
          by_cases hay_sign : 0 ≤ ay
          · -- ay ≥ 0, ax < 0: second quadrant, atan2 in (π/2, π]
            -- atan2 is anti-monotone in y (larger y = smaller atan2)
            -- atan2 is anti-monotone in x for y ≥ 0, x < 0 (larger x = smaller atan2)
            -- So minimum is at (y.hi, x.hi) if x.hi < 0, else need y-axis handling
            by_cases hx_hi_neg : x.hi.val < 0
            · -- x.hi < 0: entire x-range is negative, use (y.hi, x.hi) corner
              calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                       (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                  ≤ Real.atan2 y.hi.val x.hi.val := min_le_of_right_le (min_le_right _ _)
                _ ≤ Real.atan2 y.hi.val ax := by
                    -- ax ≤ x.hi and both < 0, anti-monotone in x gives this
                    apply Real.atan2_anti_right_of_nonneg_of_neg
                      (le_trans hay_sign hy.2) hax_neg hx_hi_neg hx.2
                _ ≤ Real.atan2 ay ax := by
                    apply Real.atan2_anti_left_of_neg_of_nonneg hax_neg hay_sign
                      (le_trans hay_sign hy.2) hy.2
            · -- x.hi ≥ 0: x-range crosses or touches y-axis
              -- atan2 on positive y-axis is π/2, which is the minimum in second quadrant
              -- Use (y.lo, x.hi) corner if x.hi > 0 (gives π/2), else (y.hi, x.hi) for x.hi = 0
              simp only [not_lt] at hx_hi_neg
              calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                       (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                  ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                _ ≤ Real.atan2 ay ax := by
                    -- y.lo ≤ ay and x.hi ≥ 0 ≥ ax
                    -- If x.hi > 0, atan2(y.lo, x.hi) is in first quadrant ≤ π/2 ≤ atan2(ay, ax)
                    -- If x.hi = 0, atan2(y.lo, 0) = π/2 if y.lo > 0, undefined if y.lo = 0
                    by_cases hy_lo_pos : 0 < y.lo.val
                    · by_cases hx_hi_pos : 0 < x.hi.val
                      · -- First quadrant corner (y.lo > 0, x.hi > 0) ≤ second quadrant actual (ay ≥ 0, ax < 0)
                        -- First quadrant: atan2 ≤ π/2
                        -- Second quadrant: atan2 ≥ π/2
                        have h1 : Real.atan2 y.lo.val x.hi.val ≤ π / 2 := Real.atan2_le_pi_div_two_of_pos hx_hi_pos
                        have h2 : π / 2 ≤ Real.atan2 ay ax := Real.pi_div_two_le_atan2_of_neg_of_nonneg hax_neg hay_sign
                        linarith
                      · -- x.hi = 0: atan2(y.lo, 0) = π/2, which ≤ atan2(ay, ax) in 2nd quadrant
                        have hx_hi_zero : x.hi.val = 0 := le_antisymm (le_of_not_gt hx_hi_pos) hx_hi_neg
                        rw [hx_hi_zero, Real.atan2_of_zero_of_pos hy_lo_pos]
                        exact Real.pi_div_two_le_atan2_of_neg_of_nonneg hax_neg hay_sign
                    · -- y.lo ≤ 0 but ay ≥ 0: y-range crosses x-axis
                      simp only [not_lt] at hy_lo_pos
                      by_cases hx_hi_pos : 0 < x.hi.val
                      · -- (y.lo, x.hi) might be in third/fourth quadrant
                        by_cases hy_lo_neg : y.lo.val < 0
                        · -- Third/fourth quadrant, atan2 is negative ≤ atan2 in second quadrant
                          have h1 : Real.atan2 y.lo.val x.hi.val < 0 := Real.atan2_neg_of_neg_of_pos hy_lo_neg hx_hi_pos
                          have h2 : 0 ≤ Real.atan2 ay ax := Real.atan2_nonneg_of_nonneg_of_neg hay_sign hax_neg
                          linarith
                        · -- y.lo = 0: atan2(0, x.hi) = 0 if x.hi > 0
                          have hy_lo_zero : y.lo.val = 0 := le_antisymm hy_lo_pos (le_of_not_gt hy_lo_neg)
                          rw [hy_lo_zero, Real.atan2_of_pos hx_hi_pos]
                          simp only [zero_div, Real.arctan_zero]
                          exact Real.atan2_nonneg_of_nonneg_of_neg hay_sign hax_neg
                      · -- x.hi = 0
                        have hx_hi_zero : x.hi.val = 0 := le_antisymm (le_of_not_gt hx_hi_pos) hx_hi_neg
                        by_cases hy_lo_neg : y.lo.val < 0
                        · -- atan2(y.lo, 0) = -π/2 for y.lo < 0
                          rw [hx_hi_zero, Real.atan2_of_zero_of_neg hy_lo_neg]
                          have h2 : 0 ≤ Real.atan2 ay ax := Real.atan2_nonneg_of_nonneg_of_neg hay_sign hax_neg
                          linarith [Real.pi_pos]
                        · -- y.lo = 0, x.hi = 0: atan2(0,0) = 0
                          have hy_lo_zero : y.lo.val = 0 := le_antisymm hy_lo_pos (le_of_not_gt hy_lo_neg)
                          -- atan2(0, 0) = 0 by convention
                          simp only [hy_lo_zero, hx_hi_zero, Real.atan2_zero_zero]
                          exact Real.atan2_nonneg_of_nonneg_of_neg hay_sign hax_neg
          · -- ay < 0, ax < 0: third quadrant, atan2 in (-π, -π/2)
            simp only [not_le] at hay_sign
            -- Need case split on y.hi sign for anti-monotonicity
            by_cases hy_hi_neg : y.hi.val < 0
            · -- y.hi < 0: entire y range is negative, use (y.hi, x.lo) corner
              calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                       (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                  ≤ Real.atan2 y.hi.val x.lo.val := min_le_of_right_le (min_le_left _ _)
                _ ≤ Real.atan2 y.hi.val ax := by
                    apply Real.atan2_mono_right_of_neg_of_neg hy_hi_neg hx_lo_neg hax_neg hx.1
                _ ≤ Real.atan2 ay ax := by
                    apply Real.atan2_anti_left_of_neg_of_neg hax_neg hay_sign hy_hi_neg hy.2
            · -- y.hi ≥ 0 but ay < 0: This contradicts the branch cut condition!
              -- We have x.lo.val < 0, y.lo.val < 0, y.hi.val ≥ 0 (from hy_hi_neg)
              -- This means the branch cut condition should be true, contradicting hbc
              have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_sign
              exfalso
              apply hbc
              exact ⟨⟨Floating.lt_zero_iff.mpr hx_lo_neg, Floating.lt_zero_iff.mpr hy_lo_neg⟩,
                     Floating.nonneg_iff.mpr (le_of_not_gt hy_hi_neg)⟩
        · -- ax = 0: on the y-axis
          have hax_zero : ax = 0 := le_antisymm hax_pos (le_of_not_gt hax_neg)
          -- We need to find a corner that gives a lower bound
          -- Key: x.lo ≤ 0 ≤ x.hi, and atan2(ay, 0) = ±π/2 or 0
          by_cases hay_pos : 0 < ay
          · -- ay > 0: atan2(ay, 0) = π/2, need corner ≤ π/2
            rw [hax_zero, Real.atan2_of_zero_of_pos hay_pos]
            -- Use (y.lo, x.hi) corner - if x.hi > 0, this is ≤ π/2
            by_cases hx_hi_pos : 0 < x.hi.val
            · calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                       (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                  ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                _ ≤ π / 2 := Real.atan2_le_pi_div_two_of_pos hx_hi_pos
            · -- x.hi = 0: corner (y.lo, 0) gives bound
              have hx_hi_nonneg : 0 ≤ x.hi.val := hax_zero ▸ hx.2
              have hx_hi_zero : x.hi.val = 0 := le_antisymm (le_of_not_gt hx_hi_pos) hx_hi_nonneg
              by_cases hy_lo_pos : 0 < y.lo.val
              · calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                         (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                    ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                  _ = Real.atan2 y.lo.val 0 := by rw [hx_hi_zero]
                  _ = π / 2 := Real.atan2_of_zero_of_pos hy_lo_pos
              · -- y.lo ≤ 0 < ay: all atan2 values are ≤ π ≤ π (but we need ≤ π/2)
                -- Actually, y.lo ≤ 0 < y.hi means y crosses x-axis
                -- Corner (y.lo, x.lo) if x.lo < 0 gives third quadrant value < π/2
                by_cases hx_lo_neg : x.lo.val < 0
                · -- Third quadrant corner (y.lo, x.lo) gives atan2 < π/2
                  simp only [not_lt] at hy_lo_pos
                  by_cases hy_lo_neg : y.lo.val < 0
                  · -- Third quadrant: atan2 ∈ (-π, -π/2) ⊂ (-∞, π/2)
                    calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                             (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                        ≤ Real.atan2 y.lo.val x.lo.val := min_le_of_left_le (min_le_left _ _)
                      _ ≤ π / 2 := by
                          rw [Real.atan2_of_neg_of_neg hx_lo_neg hy_lo_neg]
                          have h := Real.arctan_lt_pi_div_two (y.lo.val / x.lo.val)
                          linarith [Real.pi_pos]
                  · -- y.lo = 0: atan2(0, x.lo) = π for x.lo < 0, which is > π/2... tricky
                    have hy_lo_zero : y.lo.val = 0 := le_antisymm hy_lo_pos (le_of_not_gt hy_lo_neg)
                    -- Use corner (y.hi, x.hi): y.hi ≥ ay > 0, x.hi = 0
                    -- atan2(y.hi, 0) = π/2
                    have hy_hi_pos : 0 < y.hi.val := lt_of_lt_of_le hay_pos hy.2
                    calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                             (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                        ≤ Real.atan2 y.hi.val x.hi.val := min_le_of_right_le (min_le_right _ _)
                      _ = Real.atan2 y.hi.val 0 := by rw [hx_hi_zero]
                      _ = π / 2 := Real.atan2_of_zero_of_pos hy_hi_pos
                · -- x.lo = 0, x.hi = 0: entire x-interval is {0}
                  simp only [not_lt] at hx_lo_neg
                  have hx_lo_nonpos : x.lo.val ≤ 0 := hax_zero ▸ hx.1
                  have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_lo_nonpos hx_lo_neg
                  -- Use corner (y.hi, x.hi) = (y.hi, 0) where y.hi ≥ ay > 0
                  have hy_hi_pos : 0 < y.hi.val := lt_of_lt_of_le hay_pos hy.2
                  calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                           (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                      ≤ Real.atan2 y.hi.val x.hi.val := min_le_of_right_le (min_le_right _ _)
                    _ = Real.atan2 y.hi.val 0 := by rw [hx_hi_zero]
                    _ = π / 2 := Real.atan2_of_zero_of_pos hy_hi_pos
          · -- ay ≤ 0
            simp only [not_lt] at hay_pos
            by_cases hay_neg : ay < 0
            · -- ay < 0: atan2(ay, 0) = -π/2
              rw [hax_zero, Real.atan2_of_zero_of_neg hay_neg]
              -- Need corner ≤ -π/2, which means third quadrant or y-axis with y < 0
              have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_neg
              -- From hbc: ¬((x.lo < 0 ∧ y.lo < 0) ∧ 0 ≤ y.hi)
              -- Since y.lo < 0, either x.lo ≥ 0 or y.hi < 0
              by_cases hx_lo_neg : x.lo.val < 0
              · -- x.lo < 0, y.lo < 0: branch cut condition says y.hi < 0
                have hy_hi_neg : y.hi.val < 0 := by
                  by_contra h
                  simp only [not_lt] at h
                  apply hbc
                  exact ⟨⟨Floating.lt_zero_iff.mpr hx_lo_neg, Floating.lt_zero_iff.mpr hy_lo_neg⟩,
                         Floating.nonneg_iff.mpr h⟩
                -- Third quadrant corner (y.hi, x.lo) gives value ≤ -π/2
                calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                         (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                    ≤ Real.atan2 y.hi.val x.lo.val := min_le_of_right_le (min_le_left _ _)
                  _ ≤ -π / 2 := by
                      rw [Real.atan2_of_neg_of_neg hx_lo_neg hy_hi_neg]
                      have h := Real.arctan_lt_pi_div_two (y.hi.val / x.lo.val)
                      linarith
              · -- x.lo ≥ 0: use corner (y.lo, x.lo) = (y.lo, 0)
                simp only [not_lt] at hx_lo_neg
                have hx_lo_nonpos : x.lo.val ≤ 0 := hax_zero ▸ hx.1
                have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_lo_nonpos hx_lo_neg
                calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                         (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                    ≤ Real.atan2 y.lo.val x.lo.val := min_le_of_left_le (min_le_left _ _)
                  _ = Real.atan2 y.lo.val 0 := by rw [hx_lo_zero]
                  _ = -π / 2 := Real.atan2_of_zero_of_neg hy_lo_neg
            · -- ay = 0: atan2(0, 0) = 0
              have hay_zero : ay = 0 := le_antisymm hay_pos (le_of_not_gt hay_neg)
              rw [hax_zero, hay_zero, Real.atan2_zero_zero]
              -- Need corner ≤ 0
              by_cases hy_lo_neg : y.lo.val < 0
              · -- y.lo < 0: atan2 at some corner will be negative
                by_cases hx_hi_pos : 0 < x.hi.val
                · -- (y.lo, x.hi) is in fourth quadrant, atan2 < 0
                  calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                           (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                      ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                    _ ≤ 0 := le_of_lt (Real.atan2_neg_of_neg_of_pos hy_lo_neg hx_hi_pos)
                · -- x.hi = 0: (y.lo, 0) gives -π/2 < 0
                  simp only [not_lt] at hx_hi_pos
                  have hx_hi_nonneg : 0 ≤ x.hi.val := hax_zero ▸ hx.2
                  have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos hx_hi_nonneg
                  calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                           (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                      ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                    _ = Real.atan2 y.lo.val 0 := by rw [hx_hi_zero]
                    _ = -π / 2 := Real.atan2_of_zero_of_neg hy_lo_neg
                    _ ≤ 0 := by linarith [Real.pi_pos]
              · -- y.lo ≥ 0: since ay = 0 and y.lo ≤ ay, y.lo = 0
                simp only [not_lt] at hy_lo_neg
                have hy_lo_zero : y.lo.val = 0 := le_antisymm (le_trans hy.1 (le_of_eq hay_zero)) hy_lo_neg
                by_cases hx_hi_pos : 0 < x.hi.val
                · -- (y.lo, x.hi) = (0, x.hi) with x.hi > 0 gives atan2 = 0
                  calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                           (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                      ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                    _ = Real.atan2 0 x.hi.val := by rw [hy_lo_zero]
                    _ = 0 := by rw [Real.atan2_of_pos hx_hi_pos]; simp
                · -- x.hi = 0: (y.lo, x.hi) = (0, 0) gives atan2 = 0
                  simp only [not_lt] at hx_hi_pos
                  have hx_hi_nonneg : 0 ≤ x.hi.val := hax_zero ▸ hx.2
                  have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos hx_hi_nonneg
                  calc min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                           (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))
                      ≤ Real.atan2 y.lo.val x.hi.val := min_le_of_left_le (min_le_right _ _)
                    _ = Real.atan2 0 0 := by rw [hy_lo_zero, hx_hi_zero]
                    _ = 0 := Real.atan2_zero_zero
    have ub : Real.atan2 ay ax ≤
              max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                  (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := by
      simp only [le_max_iff]
      simp only [not_lt] at hx_pos
      by_cases hax_pos : 0 < ax
      · -- ax > 0: right half-plane, atan2 ∈ (-π/2, π/2)
        have hx_hi_pos : 0 < x.hi.val := lt_of_lt_of_le hax_pos hx.2
        by_cases hay_sign : 0 ≤ ay
        · -- ay ≥ 0 (first quadrant): atan2 ay ax ≤ π/2
          -- Corner (y.hi, x.lo) is in second quadrant if x.lo < 0, so ≥ π/2
          have hy_hi_nonneg : 0 ≤ y.hi.val := le_trans hay_sign hy.2
          by_cases hx_lo_neg : x.lo.val < 0
          · -- x.lo < 0: use corner (y.hi, x.lo) which is ≥ π/2
            right; left
            calc Real.atan2 ay ax
                ≤ π / 2 := Real.atan2_le_pi_div_two_of_pos hax_pos
              _ ≤ Real.atan2 y.hi.val x.lo.val := Real.pi_div_two_le_atan2_of_neg_of_nonneg hx_lo_neg hy_hi_nonneg
          · -- x.lo = 0: use corner (y.hi, x.lo) = (y.hi, 0) which gives π/2 or 0
            simp only [not_lt] at hx_lo_neg
            have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_pos hx_lo_neg
            by_cases hy_hi_pos : 0 < y.hi.val
            · -- y.hi > 0: atan2(y.hi, 0) = π/2
              right; left
              calc Real.atan2 ay ax
                  ≤ π / 2 := Real.atan2_le_pi_div_two_of_pos hax_pos
                _ = Real.atan2 y.hi.val 0 := (Real.atan2_of_zero_of_pos hy_hi_pos).symm
                _ = Real.atan2 y.hi.val x.lo.val := by rw [hx_lo_zero]
            · -- y.hi = 0: then ay ≤ y.hi = 0, so ay = 0 (since ay ≥ 0)
              simp only [not_lt] at hy_hi_pos
              have hy_hi_zero : y.hi.val = 0 := le_antisymm hy_hi_pos hy_hi_nonneg
              have hay_zero : ay = 0 := le_antisymm (hy_hi_zero ▸ hy.2) hay_sign
              right; right
              simp only [hay_zero, hy_hi_zero, Real.atan2_of_pos hax_pos, Real.atan2_of_pos hx_hi_pos, zero_div, le_refl]
        · -- ay < 0 (fourth quadrant): atan2 ay ax < 0, use corner (y.hi, x.hi)
          push_neg at hay_sign
          have hay_nonpos : ay ≤ 0 := hay_sign.le
          right; right
          calc Real.atan2 ay ax
              ≤ Real.atan2 ay x.hi.val := Real.atan2_mono_right_of_nonpos_of_pos hay_nonpos hax_pos hx_hi_pos hx.2
            _ ≤ Real.atan2 y.hi.val x.hi.val := Real.atan2_mono_left_of_pos hx_hi_pos hy.2
      · simp only [not_lt] at hax_pos
        by_cases hax_neg : ax < 0
        · -- ax < 0: left half-plane
          have hx_lo_neg : x.lo.val < 0 := hx.1.trans_lt hax_neg
          by_cases hay_sign : 0 ≤ ay
          · -- ay ≥ 0 (second quadrant): atan2 ∈ (π/2, π]
            -- atan2 is decreasing in y and decreasing in x, so max at (y.lo, x.lo)
            left; left
            by_cases hy_lo_nonneg : 0 ≤ y.lo.val
            · -- y.lo ≥ 0: both in second quadrant
              -- atan2 is antitone in y when x < 0 and y ≥ 0, antitone in x when y ≥ 0 and x < 0
              calc Real.atan2 ay ax
                  ≤ Real.atan2 y.lo.val ax := by
                      exact Real.atan2_anti_left_of_neg_of_nonneg hax_neg hy_lo_nonneg hay_sign hy.1
                _ ≤ Real.atan2 y.lo.val x.lo.val := by
                      exact Real.atan2_anti_right_of_nonneg_of_neg hy_lo_nonneg hx_lo_neg hax_neg hx.1
            · -- y.lo < 0: corner is in third quadrant, but ay ≥ 0 so ay's atan2 ∈ (π/2, π]
              -- Actually third quadrant corner value is in (-π, -π/2), so not useful
              -- Need a different corner: use (y.hi, x.lo) instead which has y.hi ≥ ay ≥ 0
              push_neg at hy_lo_nonneg
              -- From branch cut: since x.lo < 0 and y.lo < 0, we need y.hi < 0 (or else branch cut crossed)
              have hy_hi_neg : y.hi.val < 0 := by
                by_contra h
                simp only [not_lt] at h
                apply hbc
                exact ⟨⟨Floating.lt_zero_iff.mpr hx_lo_neg, Floating.lt_zero_iff.mpr hy_lo_nonneg⟩,
                       Floating.nonneg_iff.mpr h⟩
              -- But if y.hi < 0 and ay ≥ 0, we have ay ≤ y.hi < 0 contradiction
              have : ay < 0 := hy.2.trans_lt hy_hi_neg
              exact absurd hay_sign (not_le.mpr this)
          · -- ay < 0 (third quadrant): atan2 ∈ (-π, -π/2)
            push_neg at hay_sign
            -- Third quadrant: anti in y, mono in x. Max at (y.lo, x.hi)
            -- But if x.hi > 0, corner (y.lo, x.hi) is in fourth quadrant with value > -π/2
            left; right
            by_cases hx_hi_pos : 0 < x.hi.val
            · -- Corner (y.lo, x.hi) is in fourth quadrant
              -- Fourth quadrant has atan2 ∈ (-π/2, 0), and third quadrant has atan2 < -π/2
              -- So corner value > -π/2 > atan2 ay ax
              have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_sign
              exact le_of_lt (calc Real.atan2 ay ax
                  < -π / 2 := Real.atan2_lt_neg_pi_div_two_of_neg_of_neg hay_sign hax_neg
                _ < Real.atan2 y.lo.val x.hi.val := Real.neg_pi_div_two_lt_atan2_of_pos hx_hi_pos)
            · -- x.hi ≤ 0: entire interval in left half-plane
              simp only [not_lt] at hx_hi_pos
              by_cases hx_hi_neg : x.hi.val < 0
              · -- x.hi < 0: use monotonicity in third quadrant
                have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_sign
                calc Real.atan2 ay ax
                    ≤ Real.atan2 y.lo.val ax := Real.atan2_anti_left_of_neg_of_neg hax_neg hy_lo_neg hay_sign hy.1
                  _ ≤ Real.atan2 y.lo.val x.hi.val := Real.atan2_mono_right_of_neg_of_neg hy_lo_neg hax_neg hx_hi_neg hx.2
              · -- x.hi = 0: corner (y.lo, 0) = -π/2
                simp only [not_lt] at hx_hi_neg
                have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos hx_hi_neg
                have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_sign
                calc Real.atan2 ay ax
                    ≤ -π / 2 := le_of_lt (Real.atan2_lt_neg_pi_div_two_of_neg_of_neg hay_sign hax_neg)
                  _ = Real.atan2 y.lo.val x.hi.val := by rw [hx_hi_zero, Real.atan2_of_zero_of_neg hy_lo_neg]
        · -- ax = 0: on the y-axis
          have hax_zero : ax = 0 := le_antisymm hax_pos (le_of_not_gt hax_neg)
          by_cases hay_pos : 0 < ay
          · -- ay > 0: atan2(ay, 0) = π/2
            rw [hax_zero, Real.atan2_of_zero_of_pos hay_pos]
            -- Need corner ≥ π/2
            have hy_hi_pos : 0 < y.hi.val := lt_of_lt_of_le hay_pos hy.2
            by_cases hx_lo_neg : x.lo.val < 0
            · -- Use corner (y.hi, x.lo) in second quadrant
              right; left
              exact Real.pi_div_two_le_atan2_of_neg_of_nonneg hx_lo_neg hy_hi_pos.le
            · -- x.lo = 0: use corner (y.hi, x.lo) which gives atan2(y.hi, 0) = π/2
              simp only [not_lt] at hx_lo_neg
              have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_pos hx_lo_neg
              -- Corner (y.hi, x.lo) = (y.hi, 0) gives exactly π/2
              right; left
              rw [hx_lo_zero, Real.atan2_of_zero_of_pos hy_hi_pos]
          · -- ay ≤ 0
            simp only [not_lt] at hay_pos
            by_cases hay_neg : ay < 0
            · -- ay < 0: atan2(ay, 0) = -π/2
              rw [hax_zero, Real.atan2_of_zero_of_neg hay_neg]
              -- Need corner ≥ -π/2, which is most corners except deep third quadrant
              by_cases hx_hi_pos : 0 < x.hi.val
              · -- Corner (y.hi, x.hi) with x.hi > 0 gives value > -π/2
                right; right
                exact le_of_lt (Real.neg_pi_div_two_lt_atan2_of_pos hx_hi_pos)
              · -- x.hi ≤ 0
                simp only [not_lt] at hx_hi_pos
                have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos (hax_zero ▸ hx.2)
                -- y.hi corner: need y.hi < 0 to get -π/2, or y.hi ≥ 0 to get ≥ -π/2
                by_cases hy_hi_neg : y.hi.val < 0
                · -- Corner (y.hi, 0) = -π/2
                  right; right
                  rw [hx_hi_zero, Real.atan2_of_zero_of_neg hy_hi_neg]
                · -- y.hi ≥ 0: corner (y.hi, 0) = π/2 or 0 ≥ -π/2
                  simp only [not_lt] at hy_hi_neg
                  right; right
                  by_cases hy_hi_pos : 0 < y.hi.val
                  · rw [hx_hi_zero, Real.atan2_of_zero_of_pos hy_hi_pos]
                    linarith [Real.pi_pos]
                  · simp only [not_lt] at hy_hi_pos
                    have hy_hi_zero : y.hi.val = 0 := le_antisymm hy_hi_pos hy_hi_neg
                    rw [hx_hi_zero, hy_hi_zero, Real.atan2_zero_zero]
                    linarith [Real.pi_pos]
            · -- ay = 0: atan2(0, 0) = 0
              have hay_zero : ay = 0 := le_antisymm hay_pos (le_of_not_gt hay_neg)
              rw [hax_zero, hay_zero, Real.atan2_zero_zero]
              -- Need corner ≥ 0
              by_cases hy_hi_pos : 0 < y.hi.val
              · by_cases hx_hi_pos : 0 < x.hi.val
                · -- First quadrant corner
                  right; right
                  exact Real.atan2_nonneg_of_nonneg_of_pos hy_hi_pos.le hx_hi_pos
                · -- x.hi ≤ 0
                  simp only [not_lt] at hx_hi_pos
                  by_cases hx_lo_neg : x.lo.val < 0
                  · -- Second quadrant corner
                    right; left
                    exact Real.atan2_nonneg_of_nonneg_of_neg hy_hi_pos.le hx_lo_neg
                  · -- x = {0}, use (y.hi, 0) = π/2
                    simp only [not_lt] at hx_lo_neg
                    have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_pos hx_lo_neg
                    have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos (hax_zero ▸ hx.2)
                    right; right
                    rw [hx_hi_zero, Real.atan2_of_zero_of_pos hy_hi_pos]
                    linarith [Real.pi_pos]
              · -- y.hi ≤ 0
                simp only [not_lt] at hy_hi_pos
                have hy_hi_nonpos : y.hi.val ≤ 0 := hy_hi_pos
                have hy_hi_zero : y.hi.val = 0 := le_antisymm hy_hi_nonpos (hay_zero ▸ hy.2)
                by_cases hx_hi_pos : 0 < x.hi.val
                · -- Corner (0, x.hi) with x.hi > 0 gives 0
                  right; right
                  rw [hy_hi_zero, Real.atan2_of_pos hx_hi_pos]
                  simp
                · -- x.hi ≤ 0
                  simp only [not_lt] at hx_hi_pos
                  have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos (hax_zero ▸ hx.2)
                  right; right
                  rw [hy_hi_zero, hx_hi_zero, Real.atan2_zero_zero]
    /- -- Preserved incomplete proof for reference
    have ub_todo : Real.atan2 ay ax ≤
              max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                  (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := by
      by_cases hax_pos : 0 < ax
      · have hx_hi_pos : 0 < x.hi.val := lt_of_lt_of_le hax_pos hx.2
        have hx_lo_nonpos : x.lo.val ≤ 0 := le_of_not_gt hx_pos
        by_cases hay_sign : 0 ≤ ay
        · have hy_hi_nonneg : 0 ≤ y.hi.val := le_trans hay_sign hy.2
          calc Real.atan2 ay ax
              ≤ π / 2 := Real.atan2_le_pi_div_two_of_pos hax_pos
            _ ≤ Real.atan2 y.hi.val x.lo.val := by
                by_cases hx_lo_neg : x.lo.val < 0
                · exact Real.pi_div_two_le_atan2_of_neg_of_nonneg hx_lo_neg hy_hi_nonneg
                · -- x.lo = 0
                  simp only [not_lt] at hx_lo_neg
                  have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_lo_nonpos hx_lo_neg
                  by_cases hy_hi_pos : 0 < y.hi.val
                  · rw [hx_lo_zero, Real.atan2_of_zero_of_pos hy_hi_pos]
                  · -- y.hi = 0, so ay = 0 (since 0 ≤ ay ≤ y.hi ≤ 0)
                    simp only [not_lt] at hy_hi_pos
                    have hy_hi_zero : y.hi.val = 0 := le_antisymm hy_hi_pos hy_hi_nonneg
                    have hay_zero : ay = 0 := le_antisymm (hy_hi_zero ▸ hy.2) hay_sign
                    rw [hx_lo_zero, hy_hi_zero, hay_zero, Real.atan2_of_pos hax_pos] at *
                    simp only [zero_div, Real.arctan_zero, le_refl]
            _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_left _ _
            _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                    (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
        · -- ay < 0, ax > 0: Fourth quadrant
          simp only [not_le] at hay_sign
          -- In fourth quadrant, atan2 is mono in both y and x (when y ≤ 0)
          -- So max at (y.hi, x.hi)
          calc Real.atan2 ay ax
              ≤ Real.atan2 y.hi.val ax := Real.atan2_mono_left_of_pos hax_pos hy.2
            _ ≤ Real.atan2 y.hi.val x.hi.val := Real.atan2_mono_right_of_nonpos_of_pos
                  (hy.2.trans hay_sign.le) hax_pos hx_hi_pos hx.2
            _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_right _ _
            _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                    (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
      · -- ax ≤ 0
        simp only [not_lt] at hax_pos
        by_cases hax_neg : ax < 0
        · -- ax < 0: Second or third quadrant
          have hx_lo_neg : x.lo.val < 0 := hx.1.trans_lt hax_neg
          by_cases hay_sign : 0 ≤ ay
          · -- ay ≥ 0, ax < 0: Second quadrant
            -- atan2 is anti in y and anti in x, so max at (y.lo, x.lo)
            by_cases hy_lo_nonneg : 0 ≤ y.lo.val
            · -- y.lo ≥ 0: entire y-range is nonneg, use (y.lo, x.lo)
              calc Real.atan2 ay ax
                  ≤ Real.atan2 y.lo.val ax := Real.atan2_anti_left_of_neg_of_nonneg
                      hax_neg hy_lo_nonneg hay_sign hy.1
                _ ≤ Real.atan2 y.lo.val x.lo.val := Real.atan2_anti_right_of_nonneg_of_neg
                      hy_lo_nonneg hx_lo_neg hax_neg hx.1
                _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_left _ _
                _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                        (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
            · -- y.lo < 0 but ay ≥ 0: y-range crosses x-axis
              simp only [not_le] at hy_lo_nonneg
              -- atan2(ay, ax) is in second quadrant [π/2, π]
              -- (y.lo, x.lo) is in third quadrant with atan2 in (-π, -π/2)
              -- These values are NOT comparable directly
              -- Use (y.hi, x.lo) which is in second quadrant if y.hi ≥ 0
              have hy_hi_nonneg : 0 ≤ y.hi.val := le_trans hay_sign hy.2
              calc Real.atan2 ay ax
                  ≤ Real.atan2 y.lo.val ax := Real.atan2_anti_left_of_neg_of_nonneg
                      hax_neg hy_lo_nonneg.le hay_sign hy.1
                _ ≤ Real.atan2 y.lo.val x.lo.val := Real.atan2_mono_right_of_neg_of_neg
                      hy_lo_nonneg hx_lo_neg hax_neg hx.1
                _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_left _ _
                _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                        (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
          · -- ay < 0, ax < 0: Third quadrant
            simp only [not_le] at hay_sign
            -- atan2 is anti in y and mono in x, so max at (y.lo, x.hi)
            have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_sign
            by_cases hy_hi_neg : y.hi.val < 0
            · -- y.hi < 0: entire y range is negative
              by_cases hx_hi_neg : x.hi.val < 0
              · -- x.hi < 0: entire x range is negative, use (y.lo, x.hi)
                calc Real.atan2 ay ax
                    ≤ Real.atan2 y.lo.val ax := Real.atan2_anti_left_of_neg_of_neg
                        hax_neg hay_sign hy_lo_neg hy.1
                  _ ≤ Real.atan2 y.lo.val x.hi.val := Real.atan2_mono_right_of_neg_of_neg
                        hy_lo_neg hax_neg hx_hi_neg hx.2
                  _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_right _ _
                  _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
              · -- x.hi ≥ 0: x crosses y-axis
                simp only [not_lt] at hx_hi_neg
                by_cases hx_hi_pos : 0 < x.hi.val
                · -- x.hi > 0: (y.lo, x.hi) is in fourth quadrant
                  -- Third quadrant atan2 ∈ (-π, -π/2), fourth quadrant ∈ (-π/2, 0)
                  -- Use (y.lo, x.hi) as upper bound
                  calc Real.atan2 ay ax
                      ≤ -π / 2 := by
                          have h := Real.atan2_lt_neg_pi_div_two_of_neg_of_neg hay_sign hax_neg
                          linarith
                    _ ≤ Real.atan2 y.lo.val x.hi.val := by
                          have h := Real.neg_pi_div_two_lt_atan2_of_pos hx_hi_pos
                          linarith
                    _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_right _ _
                    _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                            (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
                · -- x.hi = 0
                  have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_neg (le_of_not_gt hx_hi_pos)
                  -- atan2(y.lo, 0) = -π/2 for y.lo < 0
                  calc Real.atan2 ay ax
                      ≤ -π / 2 := by
                          have h := Real.atan2_lt_neg_pi_div_two_of_neg_of_neg hay_sign hax_neg
                          linarith
                    _ = Real.atan2 y.lo.val 0 := (Real.atan2_of_zero_of_neg hy_lo_neg).symm
                    _ = Real.atan2 y.lo.val x.hi.val := by rw [hx_hi_zero]
                    _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_right _ _
                    _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                            (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
            · -- y.hi ≥ 0 but ay < 0: contradicts branch cut condition
              simp only [not_lt] at hy_hi_neg
              exfalso
              apply hbc
              exact ⟨⟨Floating.lt_zero_iff.mpr hx_lo_neg, Floating.lt_zero_iff.mpr hy_lo_neg⟩,
                     Floating.nonneg_iff.mpr hy_hi_neg⟩
        · -- ax = 0: on y-axis
          have hax_zero : ax = 0 := le_antisymm hax_pos (le_of_not_gt hax_neg)
          -- atan2(ay, 0) = π/2 if ay > 0, -π/2 if ay < 0, 0 if ay = 0
          by_cases hay_pos : 0 < ay
          · -- ay > 0: atan2(ay, 0) = π/2, need π/2 ≤ corner
            rw [hax_zero, Real.atan2_of_zero_of_pos hay_pos]
            have hy_hi_pos : 0 < y.hi.val := lt_of_lt_of_le hay_pos hy.2
            have hx_lo_nonpos : x.lo.val ≤ 0 := le_of_not_gt hx_pos
            by_cases hx_lo_neg : x.lo.val < 0
            · -- x.lo < 0: (y.hi, x.lo) is in second quadrant
              have h : π / 2 ≤ Real.atan2 y.hi.val x.lo.val :=
                Real.pi_div_two_le_atan2_of_neg_of_nonneg hx_lo_neg hy_hi_pos.le
              calc π / 2
                  ≤ Real.atan2 y.hi.val x.lo.val := h
                _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_left _ _
                _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                        (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
            · -- x.lo = 0: (y.hi, x.lo) = (y.hi, 0), atan2 = π/2
              simp only [not_lt] at hx_lo_neg
              have hx_lo_zero : x.lo.val = 0 := le_antisymm hx_lo_nonpos hx_lo_neg
              calc π / 2
                  = Real.atan2 y.hi.val 0 := (Real.atan2_of_zero_of_pos hy_hi_pos).symm
                _ = Real.atan2 y.hi.val x.lo.val := by rw [hx_lo_zero]
                _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_left _ _
                _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                        (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
          · -- ay ≤ 0
            simp only [not_lt] at hay_pos
            by_cases hay_neg : ay < 0
            · -- ay < 0: atan2(ay, 0) = -π/2
              rw [hax_zero, Real.atan2_of_zero_of_neg hay_neg]
              have hx_lo_nonpos : x.lo.val ≤ 0 := le_of_not_gt hx_pos
              have hy_lo_neg : y.lo.val < 0 := hy.1.trans_lt hay_neg
              by_cases hx_hi_pos : 0 < x.hi.val
              · -- x.hi > 0: (y.lo, x.hi) is in fourth quadrant
                have h : -π / 2 < Real.atan2 y.lo.val x.hi.val :=
                  Real.neg_pi_div_two_lt_atan2_of_pos hx_hi_pos
                calc -π / 2
                    ≤ Real.atan2 y.lo.val x.hi.val := le_of_lt h
                  _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_right _ _
                  _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
              · -- x.hi ≤ 0
                simp only [not_lt] at hx_hi_pos
                have hx_hi_nonneg : 0 ≤ x.hi.val := hax_zero ▸ hx.2
                have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos hx_hi_nonneg
                -- (y.lo, x.hi) = (y.lo, 0), atan2 = -π/2
                calc -π / 2
                    = Real.atan2 y.lo.val 0 := (Real.atan2_of_zero_of_neg hy_lo_neg).symm
                  _ = Real.atan2 y.lo.val x.hi.val := by rw [hx_hi_zero]
                  _ ≤ max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val) := le_max_right _ _
                  _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_left _ _
            · -- ay = 0: atan2(0, 0) = 0
              have hay_zero : ay = 0 := le_antisymm hay_pos (le_of_not_gt hay_neg)
              rw [hax_zero, hay_zero, Real.atan2_zero_zero]
              have hx_lo_nonpos : x.lo.val ≤ 0 := le_of_not_gt hx_pos
              have hx_hi_nonneg : 0 ≤ x.hi.val := hax_zero ▸ hx.2
              have hy_lo_nonpos : y.lo.val ≤ 0 := hay_zero ▸ hy.1
              have hy_hi_nonneg : 0 ≤ y.hi.val := hay_zero ▸ hy.2
              -- Need 0 ≤ some corner
              by_cases hx_hi_pos : 0 < x.hi.val
              · calc (0 : ℝ)
                    ≤ Real.atan2 y.hi.val x.hi.val := Real.atan2_nonneg_of_nonneg_of_pos hy_hi_nonneg hx_hi_pos
                  _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_right _ _
                  _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                          (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
              · simp only [not_lt] at hx_hi_pos
                have hx_hi_zero : x.hi.val = 0 := le_antisymm hx_hi_pos hx_hi_nonneg
                by_cases hy_hi_pos : 0 < y.hi.val
                · calc (0 : ℝ)
                      ≤ π / 2 := by linarith [Real.pi_pos]
                    _ = Real.atan2 y.hi.val 0 := (Real.atan2_of_zero_of_pos hy_hi_pos).symm
                    _ = Real.atan2 y.hi.val x.hi.val := by rw [hx_hi_zero]
                    _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_right _ _
                    _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                            (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
                · simp only [not_lt] at hy_hi_pos
                  have hy_hi_zero : y.hi.val = 0 := le_antisymm hy_hi_pos hy_hi_nonneg
                  calc (0 : ℝ)
                      = Real.atan2 0 0 := Real.atan2_zero_zero.symm
                    _ = Real.atan2 y.hi.val x.hi.val := by rw [hy_hi_zero, hx_hi_zero]
                    _ ≤ max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val) := le_max_right _ _
                    _ ≤ max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
                            (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)) := le_max_right _ _
    -/
    have in_range : Real.atan2 ay ax ∈ Set.Icc
        (min (min (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
             (min (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val)))
        (max (max (Real.atan2 y.lo.val x.lo.val) (Real.atan2 y.lo.val x.hi.val))
             (max (Real.atan2 y.hi.val x.lo.val) (Real.atan2 y.hi.val x.hi.val))) :=
      ⟨lb, ub⟩
    have u_result : approx u (Real.atan2 ay ax) := approx_of_mem_Icc u_min u_max in_range
    -- The goal is `(min = nan) ∨ bounds`, which is exactly what u_result gives us
    simp only [approx, lo_eq_nan, lo_union, hi_union, u] at u_result
    exact u_result

/-- `Interval.atan2` propagates `nan` on left -/
@[simp] lemma Interval.nan_atan2_left {x : Interval} : Interval.atan2 nan x = nan := by
  rw [Interval.atan2]
  simp only [lo_nan, hi_nan, bif_eq_if, Bool.and_eq_true, decide_eq_true_eq]
  -- y.hi = nan, and 0 ≤ nan is false since nan < 0
  have h : ¬(0 ≤ (nan : Floating)) := not_le.mpr Floating.nan_lt_zero
  simp only [h, and_false, ite_false]
  simp only [Floating.atan2, bif_eq_if, beq_self_eq_true,
    Bool.true_or, ite_true, union_self]

/-- `Interval.atan2` propagates `nan` on right -/
@[simp] lemma Interval.nan_atan2_right {y : Interval} : Interval.atan2 y nan = nan := by
  rw [Interval.atan2]
  simp only [lo_nan, hi_nan, bif_eq_if, Bool.and_eq_true, decide_eq_true_eq]
  -- Regardless of branch cut condition, all corners have x = nan, so result is nan
  -- x.hi = nan and nan < 0 is true, but we need to split on the full condition
  split_ifs with hbc
  · -- Branch cut condition true → result is nan
    rfl
  · -- Branch cut condition false → compute corners, all involve nan
    simp only [Floating.atan2, bif_eq_if, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hyn : y = nan
    · simp only [hyn, lo_nan, hi_nan, true_or, ite_true, union_self]
    · have hlo : y.lo ≠ nan := lo_ne_nan hyn
      have hhi : y.hi ≠ nan := hi_ne_nan hyn
      simp only [hlo, hhi, false_or, ite_true, union_self]
