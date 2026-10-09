import ReflectedLiouville.ExplicitExponent
import ReflectedLiouville.OrderedPairs

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Classical
namespace ReflectedLiouville

/-- Expose the fixed 1/40 exponent already proved for the linear mean. -/
theorem explicit_liouville_linear_saving (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      |linearSum N| ≤ C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/40) := by
  obtain ⟨C,X₀,hC,hX₀,hmean⟩ := liouville_mean_saving h_MRT
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (log_saving_error_eventually_ge_one (1/40))
  refine ⟨C+1,by positivity,max 3 (max ⌈X₀⌉₊ N₁),le_max_left _ _,?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hceil : ⌈X₀⌉₊ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNX : X₀ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hb : ‖∑ n ∈ Finset.Icc 1 N, liouville n‖ ≤
      C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/40) := by
    simpa only [Nat.floor_natCast] using hmean (N : ℝ) hNX
  have he := hN₁ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  apply (linearSum_le_mean_and_one N (by omega)).trans
  calc
    _ ≤ C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/40) +
        (N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/40) := by linarith only [hb,he]
    _ = _ := by ring

/-- Literal paper Theorem 1.1: fixed exponent 1/10^200, correlation and
    all four ordered counts, with one positive constant and one threshold. -/
theorem paper_theorem_1_1_explicit
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) : PaperMainStatement := by
  obtain ⟨Cr,hCr,Nr,hNr,hr⟩ := explicit_liouville_correlation h_KMT h_MRT
  obtain ⟨D,hD,Nl,hNl,hl⟩ := explicit_liouville_linear_saving h_MRT
  let e := (1 : ℝ)/(10 : ℝ)^(200 : ℕ)
  obtain ⟨Ne,hNe⟩ := eventually_atTop.mp (log_saving_error_eventually_ge_one e)
  obtain ⟨Ng,hNg⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  let Cs := (1+2*D+Cr)/4
  let C := Cr+Cs
  have hCs : 0 < Cs := by dsimp only [Cs]; positivity
  have hC : 0 < C := add_pos hCr hCs
  refine ⟨C,hC,max (max Nr Nl) (max Ne Ng),?_,?_⟩
  · exact hNr.trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro N hN
    have h0 : Nr ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    have h1 : Nl ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have h2 : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have h3 : Ng ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hlog := hNg N h3
    let rate := (N : ℝ)/Real.rpow (Real.log (N : ℝ)) e
    have hRate : 1 ≤ rate := hNe N h2
    have hRate0 : 0 ≤ rate := zero_le_one.trans hRate
    have hc : |reflectedSum N| ≤ Cr*rate := by
      simpa only [rate,mul_div_assoc] using hr N h0
    have hlinear : |linearSum N| ≤ D*rate := by
      have hb := (hl N h1).trans (log_saving_error_antitone N hlog e (1/40) D hD.le paper_exponent_le_linear)
      simpa only [rate,mul_div_assoc] using hb
    have hCrC : Cr ≤ C := by dsimp only [C]; linarith only [hCs]
    have hCsC : Cs ≤ C := by dsimp only [C]; linarith only [hCr]
    constructor
    · apply hc.trans
      have hh := mul_le_mul_of_nonneg_right hCrC hRate0
      simpa only [rate,mul_div_assoc] using hh
    · intro e₁ e₂ he₁ he₂
      rw [← signPatternCount_eq_orderedPairCount]
      apply (sign_pattern_error_bound N (by omega) e₁ e₂ he₁ he₂).trans
      have hFirst : (1+2*|linearSum N|+|reflectedSum N|)/4 ≤ Cs*rate := by
        dsimp only [Cs]
        nlinarith only [hRate,hlinear,hc]
      apply hFirst.trans
      have hh := mul_le_mul_of_nonneg_right hCsC hRate0
      simpa only [rate,mul_div_assoc] using hh

#print axioms paper_theorem_1_1_explicit
end ReflectedLiouville
