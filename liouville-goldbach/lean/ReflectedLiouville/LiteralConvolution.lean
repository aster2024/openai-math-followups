import ReflectedLiouville.QuotientLatticeSum

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace ReflectedLiouville

/-- The literal reflected correlation with weighted rough shifts is exactly
    the circle convolution. The fixed total N is never averaged. -/
theorem literal_reflected_convolution_identity (N : ℕ) (hN : 0 < N) (Y : ℝ) (hY : 0 ≤ Y)
    (M : ℕ) (Z : Finset ℕ) (c : ℕ → ℂ) (hZ : ∀ v ∈ Z, v ≤ M) :
    (∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ v ∈ Z, (c v / (v : ℂ)) * liouville m * liouville (N * v - m)) =
      ∑ r : Fin N, ∫ θ,
        quotientSourcePolynomial N (r.val + 1) Y θ * quotientTargetPolynomial N (r.val + 1) M θ *
          meanPrimeMultiplier Z c θ ∂AddCircle.haarAddCircle := by
  symm
  calc
    _ = ∑ r : Fin N, ∑ k ∈ quotientPrefixIndices N (r.val + 1) Y, ∑ v ∈ Z,
        (c v / (v : ℂ)) * liouville (N * k + (r.val + 1)) *
          liouville (N * v - (N * k + (r.val + 1))) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact quotient_reflected_convolution_identity N (r.val + 1) M Y Z c hZ
    _ = _ := quotient_lattice_prefix_sum N hN Y hY
      (fun m => ∑ v ∈ Z, (c v / (v : ℂ)) * liouville m * liouville (N * v - m))

#print axioms literal_reflected_convolution_identity

end ReflectedLiouville
