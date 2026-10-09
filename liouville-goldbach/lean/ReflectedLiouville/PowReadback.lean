import ReflectedLiouville.ZeroBox
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option pp.all true in
#check @Real.rpow_sub
set_option pp.all true in
#check @Real.rpow_mul
set_option pp.all true in
#check @Real.rpow

example (x y : ℝ) : x ^ y = Real.rpow x y := by rfl

example (t b : ℝ) (ht : 0 < t) :
    Real.rpow t (1 - b) = t / Real.rpow t b := by
  simpa only [Real.rpow_eq_pow, Real.rpow_one] using Real.rpow_sub ht 1 b
