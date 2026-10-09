import ReflectedLiouville.VarianceScaleGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
open scoped BigOperators

namespace ReflectedLiouville

lemma divisor_totient_quotient_sum (q : ℕ) :
    (∑ u : ↥q.divisors, (q / u.val).totient) = q := by
  change (∑ u ∈ q.divisors.attach, (q / u.val).totient) = q
  calc
    _ = ∑ u ∈ q.divisors, (q / u).totient := Finset.sum_attach _ _
    _ = _ := by rw [Nat.sum_div_divisors, Nat.sum_totient]

/-- Full manuscript short-progression variance, including every nonunit class.
    The realmean target has been discharged; the only analytic premises are the
    reviewed published KMT and MRT statements. -/
theorem liouville_short_progression_variance
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) : ShortProgressionVarianceBound := by
  intro ν hν hν₁
  obtain ⟨C, X₁, hC, hX₁, hunit⟩ := liouville_unit_progression_variance h_KMT h_MRT ν hν hν₁
  have hRlim := Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop hν).comp Real.tendsto_log_atTop)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (hRlim.eventually (eventually_ge_atTop X₁))
  refine ⟨C, max X₁ X₂, hC, hX₁.trans (le_max_left _ _), ?_⟩
  intro q inst X H hX hHX hHq hRlower
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hH : 0 < H := by nlinarith
  have hR10 : 10 ≤ H / q := (le_div_iff₀ hq).mpr hHq
  have hR : 1 ≤ H / q := by linarith
  have hRX₁ : X₁ ≤ H / q := (hX₂ X hXX₂).trans hRlower
  let ε := (Real.log (H / q)) ^ (-1 / 1000 : ℝ)
  have hstratum : ∀ u : ↥q.divisors,
      letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
      (u.val : ℝ) * unitResidueVariance (q / u.val) (X / u.val) (H / u.val) ≤
        C * ε * ((q / u.val).totient : ℝ) * X * (H / q) ^ (2 : ℕ) := by
    intro u
    letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
    have hup : (0 : ℝ) < u.val := by exact_mod_cast divisor_positive q u
    obtain ⟨hlo, hhi, hlength⟩ := divisor_scale_bounds q u X H hXp.le hH.le hHX
    have hXscaled : X₁ ≤ X / u.val := hRX₁.trans hlo
    have hHscaled := divisor_scaled_length q u H hHq
    have hExpscaled := divisor_scaled_exp_requirement q u X H ν hν.le hXp.le hH.le hHX hR hRlower
    have hb := hunit (q / u.val) (X / u.val) (H / u.val) hXscaled hlength hHscaled hExpscaled
    rw [divisor_scaled_ratio] at hb
    have hm := mul_le_mul_of_nonneg_left hb hup.le
    convert hm using 1 <;> dsimp only [ε] <;> simp only [div_eq_mul_inv] <;> field_simp <;> ring
  rw [allResidueVariance_gcd q X H hXp.le hH.le]
  have hsumNat : (∑ u : ↥q.divisors, (q / u.val).totient : ℕ) = q := divisor_totient_quotient_sum q
  have hsum : (∑ u : ↥q.divisors, ((q / u.val).totient : ℝ)) = q := by exact_mod_cast hsumNat
  calc
    _ ≤ ∑ u : ↥q.divisors, C * ε * ((q / u.val).totient : ℝ) * X * (H / q) ^ (2 : ℕ) :=
      Finset.sum_le_sum (fun u _ => hstratum u)
    _ = C * ε * X * (H / q) ^ (2 : ℕ) * (q : ℝ) := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hsum]
      ring
    _ = _ := by
      dsimp only [ε]
      simp only [Real.rpow_eq_pow]
      rw [show (-1 / 1000 : ℝ) = -(1 / 1000 : ℝ) by ring,
        Real.rpow_neg (Real.log_nonneg hR)]
      field_simp <;> ring

#print axioms liouville_short_progression_variance

end ReflectedLiouville
