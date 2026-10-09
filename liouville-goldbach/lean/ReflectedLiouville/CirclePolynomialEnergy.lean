import ReflectedLiouville.FiniteFourierConvolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma continuous_circle_real_integrable (F : AddCircle (1 : ℝ) → ℝ) (hF : Continuous F) :
    Integrable F AddCircle.haarAddCircle :=
  hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

lemma continuous_circle_complex_integrable (F : AddCircle (1 : ℝ) → ℂ) (hF : Continuous F) :
    Integrable F AddCircle.haarAddCircle :=
  hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

/-- Parseval and a pointwise Young inequality control the norm-product energy
    of the actual finite polynomials, with their integrability proved. -/
theorem finite_fourier_norm_product_energy {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ)
    (hf : ∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j)
    (hg : ∀ i ∈ T, ∀ j ∈ T, g i = g j → i = j)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) (hb : ∀ i ∈ T, ‖b i‖ ≤ 1) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ * ‖fourierPolynomial T g b θ‖ ∂AddCircle.haarAddCircle) ≤
      ((S.card : ℝ) + T.card) / 2 := by
  let F := fourierPolynomial S f a
  let G := fourierPolynomial T g b
  have hF : Continuous F := continuous_fourierPolynomial _ _ _
  have hG : Continuous G := continuous_fourierPolynomial _ _ _
  have hFsq := continuous_circle_real_integrable (fun θ => ‖F θ‖ ^ (2 : ℕ)) (hF.norm.pow 2)
  have hGsq := continuous_circle_real_integrable (fun θ => ‖G θ‖ ^ (2 : ℕ)) (hG.norm.pow 2)
  have hProd := continuous_circle_real_integrable (fun θ => ‖F θ‖ * ‖G θ‖) (hF.norm.mul hG.norm)
  have hRight : Integrable (fun θ => (‖F θ‖ ^ (2 : ℕ) + ‖G θ‖ ^ (2 : ℕ)) / 2)
      AddCircle.haarAddCircle := (hFsq.add hGsq).div_const 2
  have hmono := integral_mono hProd hRight (fun θ => by
    nlinarith only [sq_nonneg (‖F θ‖ - ‖G θ‖)])
  simp only [div_eq_mul_inv] at hmono
  rw [integral_mul_const, integral_add hFsq hGsq] at hmono
  have hFE := finite_fourier_l2_card_bound S f a hf ha
  have hGE := finite_fourier_l2_card_bound T g b hg hb
  change (∫ θ, ‖F θ‖ ^ (2 : ℕ) ∂AddCircle.haarAddCircle) ≤ (S.card : ℝ) at hFE
  change (∫ θ, ‖G θ‖ ^ (2 : ℕ) ∂AddCircle.haarAddCircle) ≤ (T.card : ℝ) at hGE
  exact hmono.trans (by linarith only [hFE, hGE])

#print axioms finite_fourier_norm_product_energy

end ReflectedLiouville
