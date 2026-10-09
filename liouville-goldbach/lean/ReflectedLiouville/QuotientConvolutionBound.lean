import ReflectedLiouville.LiteralConvolution
import ReflectedLiouville.CircleConvolutionEstimate

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma quotient_prefix_card_bound (N r D : ℕ) (Y : ℝ) (hN : 0 < N) (hD : 1 ≤ D)
    (hY : 0 ≤ Y) (hYD : Y / N ≤ (D : ℝ)) : (quotientPrefixIndices N r Y).card ≤ 2 * D := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloorR : (⌊Y / N⌋₊ : ℝ) ≤ (D : ℝ) := (Nat.floor_le (div_nonneg hY hNr.le)).trans hYD
  have hfloor : ⌊Y / N⌋₊ ≤ D := by exact_mod_cast hfloorR
  have hc : (quotientPrefixIndices N r Y).card ≤ ⌊Y / N⌋₊ + 1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  omega

lemma quotient_polynomial_norm_product_energy (N D : ℕ) (Y : ℝ) (hN : 0 < N) (hD : 1 ≤ D)
    (hY : 0 ≤ Y) (hYD : Y / N ≤ (D : ℝ)) :
    (∫ θ, circleNormProductSum
      (fun r : Fin N => quotientSourcePolynomial N (r.val + 1) Y)
      (fun r : Fin N => quotientTargetPolynomial N (r.val + 1) (2 * D)) θ ∂AddCircle.haarAddCircle) ≤
        3 * (N : ℝ) * D := by
  have hFE (r : Fin N) := finite_fourier_norm_product_energy (quotientPrefixIndices N (r.val + 1) Y)
    (Finset.Icc 1 (2 * D)) (fun k => (k : ℤ)) (fun t => (t : ℤ))
    (fun k => liouville (N * k + (r.val + 1))) (fun t => liouville (N * t - (r.val + 1)))
    (fun i hi j hj he => by exact_mod_cast he) (fun i hi j hj he => by exact_mod_cast he)
    (fun k hk => norm_liouville_le _) (fun t ht => norm_liouville_le _)
  have hInt (r : Fin N) : Integrable (fun θ => ‖quotientSourcePolynomial N (r.val + 1) Y θ‖ *
      ‖quotientTargetPolynomial N (r.val + 1) (2 * D) θ‖) AddCircle.haarAddCircle :=
    continuous_circle_real_integrable _
      ((continuous_fourierPolynomial _ _ _).norm.mul (continuous_fourierPolynomial _ _ _).norm)
  unfold circleNormProductSum
  rw [integral_finsetSum _ (fun r _ => hInt r)]
  have hpoint (r : Fin N) : (∫ θ, ‖quotientSourcePolynomial N (r.val + 1) Y θ‖ *
      ‖quotientTargetPolynomial N (r.val + 1) (2 * D) θ‖ ∂AddCircle.haarAddCircle) ≤ 2 * (D : ℝ) := by
    have hc := quotient_prefix_card_bound N (r.val + 1) D Y hN hD hY hYD
    have hcr : ((quotientPrefixIndices N (r.val + 1) Y).card : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast hc
    have htcard : ((Finset.Icc 1 (2 * D)).card : ℝ) = 2 * (D : ℝ) := by simp
    have he := hFE r
    rw [htcard] at he
    exact he.trans (by linarith only [hcr])
  calc
    _ ≤ ∑ _r : Fin N, 2 * (D : ℝ) := Finset.sum_le_sum (fun r _ => hpoint r)
    _ ≤ _ := by simp; nlinarith

/-- The actual reflected convolution saving, with only explicit derived
    Fourier-mean and rough-multiplier bounds awaiting scale instantiation. -/
theorem quotient_convolution_saving_from_bounds
    (N D : ℕ) (Y L C U V γ β s : ℝ) (Z : Finset ℕ) (c : ℕ → ℂ)
    (hN : 0 < N) (hD : 1 ≤ D) (hL : 1 ≤ L) (hYlow : (N : ℝ) * D / 2 ≤ Y)
    (hYhigh : Y / N ≤ (D : ℝ)) (hZ : ∀ v ∈ Z, v ≤ 2 * D)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) (hmargin : 5 + 5 * s ≤ 5 * γ + β)
    (hSource : ∀ θ : AddCircle (1 : ℝ), (∑ r : Fin N, ‖quotientSourcePolynomial N (r.val + 1) Y θ‖) ≤
      C * (N : ℝ) * D * L ^ (-β))
    (hSup : ∀ θ, ‖meanPrimeMultiplier Z c θ‖ ≤ U * L ^ (-γ))
    (hFourth : (∫ θ, ‖meanPrimeMultiplier Z c θ‖ ^ (4 : ℕ) ∂AddCircle.haarAddCircle) ≤
      V / D * L ^ (-4 * γ)) :
    ‖∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ v ∈ Z, (c v / (v : ℂ)) * liouville m * liouville (N * v - m)‖ / Y ≤
      (6 + 6 * C * U * V) * L ^ (-1 - s) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hY : 0 ≤ Y := (by positivity : (0 : ℝ) ≤ (N : ℝ) * D / 2).trans hYlow
  let F := fun r : Fin N => quotientSourcePolynomial N (r.val + 1) Y
  let G := fun r : Fin N => quotientTargetPolynomial N (r.val + 1) (2 * D)
  let B := meanPrimeMultiplier Z c
  have hGmax (r : Fin N) (θ : AddCircle (1 : ℝ)) : ‖G r θ‖ ≤ 2 * (D : ℝ) := by
    have hn := norm_fourierPolynomial_le (Finset.Icc 1 (2 * D)) (fun t => (t : ℤ))
      (fun t => liouville (N * t - (r.val + 1))) θ
    apply hn.trans
    calc
      _ ≤ ∑ _t ∈ Finset.Icc 1 (2 * D), (1 : ℝ) := Finset.sum_le_sum (fun t _ => norm_liouville_le _)
      _ = _ := by simp
  have hPoint (θ : AddCircle (1 : ℝ)) : circleNormProductSum F G θ ≤
      3 * C * (N : ℝ) * (D : ℝ) ^ (2 : ℕ) * L ^ (-β) := by
    have hs := mul_le_mul_of_nonneg_left (hSource θ) (by positivity : 0 ≤ 2 * (D : ℝ))
    have hsum : circleNormProductSum F G θ ≤ 2 * (D : ℝ) * (∑ r : Fin N, ‖F r θ‖) := by
      unfold circleNormProductSum
      calc
        _ ≤ ∑ r : Fin N, ‖F r θ‖ * (2 * (D : ℝ)) :=
          Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hGmax r θ) (norm_nonneg _))
        _ = _ := by rw [← Finset.sum_mul]; ring
    have hnonneg : 0 ≤ C * (N : ℝ) * (D : ℝ) ^ (2 : ℕ) * L ^ (-β) := by positivity
    nlinarith only [hsum, hs, hnonneg]
  have hBound := circle_convolution_moment_bound F G B
    (fun r => continuous_fourierPolynomial _ _ _) (fun r => continuous_fourierPolynomial _ _ _)
    (continuous_fourierPolynomial _ _ _) L (N : ℝ) (D : ℝ) Y C U V γ β s
    hL hNr hDr hYlow hC hU hV hmargin hPoint hSup
    (quotient_polynomial_norm_product_energy N D Y hN hD hY hYhigh) hFourth
  rw [literal_reflected_convolution_identity N hN Y hY (2 * D) Z c hZ]
  exact hBound

#print axioms quotient_convolution_saving_from_bounds

end ReflectedLiouville
