import ReflectedLiouville.ConvolutionThreshold
import OAI.NumberTheory.TwoPoint.Bounds.RoughFourier

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Exact finite three-polynomial convolution, before any analytic estimate. -/
theorem integral_fourier_triple {ι κ ρ : Type*} (S : Finset ι) (T : Finset κ) (Z : Finset ρ)
    (f : ι → ℤ) (g : κ → ℤ) (h : ρ → ℤ) (a : ι → ℂ) (b : κ → ℂ) (c : ρ → ℂ) :
    (∫ θ, fourierPolynomial S f a θ * fourierPolynomial T g b θ * fourierPolynomial Z h c θ
      ∂AddCircle.haarAddCircle) =
      ∑ i ∈ (S ×ˢ T) ×ˢ Z,
        if f i.1.1 + g i.1.2 + h i.2 = 0 then a i.1.1 * b i.1.2 * c i.2 else 0 := by
  simp_rw [fourierPolynomial_mul S T f g a b]
  exact integral_fourier_product _ _ _ _ _ _

theorem finite_fourier_parseval_injective {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ)
    (hf : ∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ (2 : ℕ) ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S, ‖a i‖ ^ (2 : ℕ) := by
  rw [integral_norm_fourierPolynomial_sq, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  have hpoint (j : ι) (hj : j ∈ S) :
      (if f i = f j then (a i * conj (a j)).re else 0) =
      (if i = j then ‖a i‖ ^ (2 : ℕ) else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have hc := congrArg Complex.re (Complex.mul_conj' (a i))
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hc
    · have hnot : f i ≠ f j := fun h => hij (hf i hi j hj h)
      simp only [ite_eq_right hij, ite_eq_right hnot]
  calc
    _ = ∑ j ∈ S, if i = j then ‖a i‖ ^ (2 : ℕ) else 0 := Finset.sum_congr rfl hpoint
    _ = _ := by simp only [Finset.sum_ite_eq, hi, ite_true]

theorem finite_fourier_l2_card_bound {ι : Type*} (S : Finset ι) (f : ι → ℤ) (a : ι → ℂ)
    (hf : ∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ (2 : ℕ) ∂AddCircle.haarAddCircle) ≤ (S.card : ℝ) := by
  rw [finite_fourier_parseval_injective S f a hf]
  calc
    _ ≤ ∑ _i ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (ha i hi) 2
    _ = _ := by simp

#print axioms integral_fourier_triple
#print axioms finite_fourier_parseval_injective

end ReflectedLiouville
