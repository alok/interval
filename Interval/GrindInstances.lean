/-
Copyright (c) 2025 Interval contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Algebra.Field.Basic
import Interval.Int64

/-!
# Grind instances for the Interval library

This file provides `Lean.Grind` instances for types in the interval library,
enabling the `grind` tactic to solve ring/field goals.

## Main instances

* `Lean.Grind.CommRing Int64` - via mathlib's `CommRing.toGrindCommRing`
* `Lean.Grind.IsCharP Int64 (2^64)` - Int64 has characteristic 2^64 (wrapping arithmetic)

## Notes

Types like `Floating`, `Interval`, `Fixed`, and `Box` are NOT rings because they use
conservative/saturating arithmetic. The `grind` tactic can still be used in proofs
*about* these types by working with the underlying `ℝ` and `ℂ` values.
-/

open Lean

namespace Int64

/-- `OfNat.ofNat x` equals the natCast for Int64. -/
theorem ofNat_eq_natCast (x : ℕ) : (OfNat.ofNat x : Int64) = (x : Int64) := by
  induction x with
  | zero => rfl
  | succ n ih => rw [Lean.Grind.Semiring.ofNat_succ, ih, Nat.cast_succ]

/-- An Int64 from a natural is zero iff the natural is divisible by 2^64. -/
theorem ofNat_eq_zero_iff (x : ℕ) : (OfNat.ofNat x : Int64) = 0 ↔ x % 2^64 = 0 := by
  rw [ofNat_eq_natCast]
  simp only [Int64.ext_iff, Int64.toUInt64_natCast, Int64.n_zero,
    UInt64.eq_iff_toNat_eq, UInt64.toNat_ofNat', UInt64.toNat_zero]

end Int64

namespace Interval.Grind

/-!
### Int64 characteristic

`Int64` has characteristic `2^64` because arithmetic wraps modulo `2^64`.
This allows `grind` to use modular arithmetic reasoning.
-/

instance : Lean.Grind.IsCharP Int64 (2^64) :=
  Lean.Grind.IsCharP.mk' (2^64) Int64 Int64.ofNat_eq_zero_iff

end Interval.Grind
