import ReflectedLiouville.BinnedSaving
import ReflectedLiouville.LinearSaving
import ReflectedLiouville.OrderedPairs

set_option autoImplicit false
open Filter
open scoped Classical

namespace ReflectedLiouville

/-- Existential logarithmic saving for the literal one-total reflected
    Liouville correlation, conditional only on the two published inputs. -/
theorem reflected_liouville_log_saving
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) : ReflectedLogSaving := by
  obtain ⟨A,hA,hb⟩ := binned_reflected_saving h_KMT h_MRT
  exact log_saving_of_binned_estimate A (by omega) ((10 : ℝ)^(180 : ℕ)) (1/100000)
    (by positivity) (by norm_num) hb

/-- Four ordered sign patterns, with the literal ordered-pair count. -/
theorem reflected_liouville_sign_patterns
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ e₁ e₂ : ℤ, IsSign e₁ → IsSign e₂ →
        |(orderedPairCount N e₁ e₂ : ℝ)-(N : ℝ)/4| ≤ C*(N : ℝ)/(Real.log (N : ℝ))^c := by
  obtain ⟨c,hc,C,hC,N₀,hN₀,hb⟩ := sign_patterns_of_reflected_saving h_MRT
    (reflected_liouville_log_saving h_KMT h_MRT)
  refine ⟨c,hc,C,hC,N₀,hN₀,?_⟩
  intro N hN e₁ e₂ he₁ he₂
  rw [← signPatternCount_eq_orderedPairCount]
  exact hb N hN e₁ e₂ he₁ he₂

/-- The correlation and all four ordered counts share one positive exponent,
    constant and threshold. No derived analytic target remains a parameter. -/
theorem reflected_liouville_main_and_sign_patterns
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        |reflectedSum N| ≤ C*(N : ℝ)/(Real.log (N : ℝ))^c ∧
        ∀ e₁ e₂ : ℤ, IsSign e₁ → IsSign e₂ →
          |(orderedPairCount N e₁ e₂ : ℝ)-(N : ℝ)/4| ≤ C*(N : ℝ)/(Real.log (N : ℝ))^c := by
  obtain ⟨c,hc,Cr,hCr,Nr,hNr,hr⟩ := reflected_liouville_log_saving h_KMT h_MRT
  obtain ⟨d,hd,Cs,hCs,Ns,hNs,hs⟩ := reflected_liouville_sign_patterns h_KMT h_MRT
  obtain ⟨Nl,hNl⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  let e := min c d
  refine ⟨e,lt_min hc hd,Cr+Cs,by positivity,max (max Nr Ns) Nl,?_,?_⟩
  · exact hNr.trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro N hN
    have h0 : Nr ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    have h1 : Ns ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have h2 : Nl ≤ N := (le_max_right _ _).trans hN
    have hlog := hNl N h2
    have hrate : 0 ≤ (N : ℝ)/(Real.log (N : ℝ))^e := by positivity
    have hCrSum : Cr ≤ Cr+Cs := by linarith
    have hCsSum : Cs ≤ Cr+Cs := by linarith
    constructor
    · have he := (hr N h0).trans (log_saving_error_antitone N hlog e c Cr hCr.le (min_le_left _ _))
      have hm := mul_le_mul_of_nonneg_right hCrSum hrate
      apply he.trans
      simpa only [mul_div_assoc,Real.rpow_eq_pow] using hm
    · intro e₁ e₂ he₁ he₂
      have he := (hs N h1 e₁ e₂ he₁ he₂).trans
        (log_saving_error_antitone N hlog e d Cs hCs.le (min_le_right _ _))
      have hm := mul_le_mul_of_nonneg_right hCsSum hrate
      apply he.trans
      simpa only [mul_div_assoc,Real.rpow_eq_pow] using hm

#print axioms reflected_liouville_log_saving
#print axioms reflected_liouville_sign_patterns
#print axioms reflected_liouville_main_and_sign_patterns
end ReflectedLiouville
