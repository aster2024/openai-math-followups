import ReflectedLiouville.CirclePolynomialEnergy
import ReflectedLiouville.Casts

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def quotientPrefixIndices (N r : ℕ) (Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Y / N⌋₊ + 1)).filter (fun k => ((N * k + r : ℕ) : ℝ) ≤ Y)

noncomputable def quotientSourcePolynomial (N r : ℕ) (Y : ℝ) : AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial (quotientPrefixIndices N r Y) (fun k => (k : ℤ)) (fun k => liouville (N * k + r))

noncomputable def quotientTargetPolynomial (N r M : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial (Finset.Icc 1 M) (fun t => (t : ℤ)) (fun t => liouville (N * t - r))

noncomputable def meanPrimeMultiplier (Z : Finset ℕ) (c : ℕ → ℂ) : AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial Z (fun v => -(v : ℤ)) (fun v => c v / (v : ℂ))

lemma reflected_nat_difference (N k v r : ℕ) :
    N * (v - k) - r = N * v - (N * k + r) := by
  rw [Nat.mul_sub_left_distrib, Nat.sub_sub]

/-- The exact reflected convolution on each residue, including the totalized
    lambda(0)=0 boundary when a natural reflected argument is nonpositive. -/
theorem quotient_reflected_convolution_identity (N r M : ℕ) (Y : ℝ)
    (Z : Finset ℕ) (c : ℕ → ℂ) (hZ : ∀ v ∈ Z, v ≤ M) :
    (∫ θ, quotientSourcePolynomial N r Y θ * quotientTargetPolynomial N r M θ * meanPrimeMultiplier Z c θ
      ∂AddCircle.haarAddCircle) =
      ∑ k ∈ quotientPrefixIndices N r Y, ∑ v ∈ Z,
        (c v / (v : ℂ)) * liouville (N * k + r) * liouville (N * v - (N * k + r)) := by
  unfold quotientSourcePolynomial quotientTargetPolynomial meanPrimeMultiplier
  rw [integral_fourier_triple]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hfreq (t : ℕ) : ((k : ℤ) + (t : ℤ) + -(v : ℤ) = 0) ↔ k + t = v := by omega
  simp only [hfreq]
  by_cases hkv : k < v
  · have ht0 : v - k ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨by omega, (Nat.sub_le v k).trans (hZ v hv)⟩
    have heq (t : ℕ) : (k + t = v) ↔ t = v - k := by omega
    simp only [heq, Finset.sum_ite_eq, Finset.sum_ite_eq', ht0, ite_true]
    rw [reflected_nat_difference]
    ring
  · have hvk : v ≤ k := le_of_not_gt hkv
    have hnone : ∀ t ∈ Finset.Icc 1 M, ¬k + t = v := by
      intro t ht
      have := (Finset.mem_Icc.mp ht).1
      omega
    have hzero : N * v - (N * k + r) = 0 := Nat.sub_eq_zero_of_le
      ((Nat.mul_le_mul_left N hvk).trans (Nat.le_add_right _ _))
    simp only [hzero]
    have hsum : (∑ t ∈ Finset.Icc 1 M,
        if k + t = v then liouville (N * k + r) * liouville (N * t - r) * (c v / (v : ℂ)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp only [ite_eq_right (hnone t ht)]
    rw [hsum]
    simp [liouville, OAI.TwoPointCorrelations.liouville]

lemma meanPrimeMultiplier_eq_conj (Z : Finset ℕ) (c : ℕ → ℂ) :
    meanPrimeMultiplier Z c = fun θ => conj (weightedRoughFourier Z (fun v => conj (c v)) 1 θ) := by
  funext θ
  unfold meanPrimeMultiplier weightedRoughFourier
  rw [fourierPolynomial_conj]
  simp only [Nat.cast_one, one_mul, map_div₀, map_natCast, Complex.conj_conj]

#print axioms quotient_reflected_convolution_identity

end ReflectedLiouville
