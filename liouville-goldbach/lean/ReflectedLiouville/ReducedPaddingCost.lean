import ReflectedLiouville.BooleanPaddingRestriction
import ReflectedLiouville.VarianceAbsorption

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma retained_divisors_mono {Q R : Finset ℕ} (hQR : Q ⊆ R) :
    retainedPrimeDivisors Q ⊆ retainedPrimeDivisors R := by
  intro q hq
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
  apply Finset.mem_image.mpr
  refine ⟨S, Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS).trans hQR), rfl⟩

lemma eventually_log_power_times_power (k : ℕ) (a b C : ℝ) (hba : b < a) :
    ∀ᶠ L : ℝ in atTop, C * (Real.log L) ^ k * L ^ (-a) ≤ L ^ (-b) := by
  have h := Real.tendsto_exp_atTop.eventually (eventually_loglog_power_error k a b C hba)
  filter_upwards [h] with L hL
  simpa only [Real.log_exp] using hL

/-- Normalized rejected padding cost, uniform over arbitrary changing reduced
    pools whose removed primes divide N. This is the arithmetic content of the
    paper's conditioning repair. -/
theorem eventually_reduced_boolean_padding_cost (a : ℝ) (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.exp 2 ≤ (N : ℝ) → Real.log (N : ℝ) ≤ L ^ a →
        ∀ (Q : Finset ℕ) (hQ : Q ⊆ paddingPrimeSupply ∅ L),
          paddingPrimeSupply ∅ L \ Q ⊆ N.primeFactors →
          ∀ (D : Finset ℕ) (bins : Finset ℤ) (η c K : ℝ),
            D ⊆ retainedPrimeDivisors Q → 0 < η → η ≤ 1 → 0 < K →
            (paddingOriginalLaw Q (fun p hp =>
              (paddingPrimeSupply_prime (hQ hp)).two_le)).average
                (fun b => activePaddingRejected D bins η c L K (paddingAvailablePrimes Q b)) /
                  paddingTiltNormalizer Q ≤ C * (Real.log L) ^ (10 : ℕ) / K + L ^ (-90 : ℝ) := by
  obtain ⟨A, hA, hfull⟩ := eventually_full_boolean_padding_cost
  obtain ⟨B, hB, hholes⟩ := padding_hole_product_uniform
  let C := A * B * a ^ (10 : ℕ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfull, eventually_log_power_times_power 10 100 90 (B * a ^ (10 : ℕ)) (by norm_num),
    eventually_ge_atTop (2 : ℝ)] with L hfullL hsmall hL
  intro N inst hN hNlog Q hQ hremoved D bins η c K hD hη hη₁ hK
  let R := paddingPrimeSupply ∅ L
  have hRp : ∀ p ∈ R, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  have hR2 : ∀ p ∈ R, 2 ≤ p := fun p hp => (hRp p hp).two_le
  have hlogN : 2 ≤ Real.log (N : ℝ) := by
    have ht := Real.log_le_log (Real.exp_pos 2) hN
    rwa [Real.log_exp] at ht
  have hLpos : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hllN : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith)
  have hll : Real.log (Real.log (N : ℝ)) ≤ a * Real.log L := by
    have ht := Real.log_le_log (by linarith : 0 < Real.log (N : ℝ)) hNlog
    rwa [Real.log_rpow hLpos] at ht
  have hholeBound : (∏ p ∈ R \ Q, ((p : ℝ) + 4) / ((p : ℝ) - 1)) ≤
      B * a ^ (10 : ℕ) * (Real.log L) ^ (10 : ℕ) := by
    have ht := (hholes N hN (R \ Q) hremoved).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hllN hll 10) hB.le)
    convert ht using 1 <;> ring
  have hholeNonneg : 0 ≤ ∏ p ∈ R \ Q, ((p : ℝ) + 4) / ((p : ℝ) - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hRp p (Finset.mem_sdiff.mp hp).1).two_le
    exact div_nonneg (by linarith) (by linarith)
  have hshrink := boolean_padding_cost_shrinking Q R D hQ hR2 bins η c L K
  have hfullD := hfullL D bins η c K (hD.trans (retained_divisors_mono hQ)) hη hη₁ hK
  have hfullNonneg : 0 ≤ A / K + L ^ (-100 : ℝ) := by positivity
  have hbound := hshrink.trans ((mul_le_mul_of_nonneg_right hfullD hholeNonneg).trans
    (mul_le_mul_of_nonneg_left hholeBound hfullNonneg))
  have herror : B * a ^ (10 : ℕ) * (Real.log L) ^ (10 : ℕ) * L ^ (-100 : ℝ) ≤ L ^ (-90 : ℝ) := hsmall
  have heq : (A / K + L ^ (-100 : ℝ)) * (B * a ^ (10 : ℕ) * (Real.log L) ^ (10 : ℕ)) =
      C * (Real.log L) ^ (10 : ℕ) / K +
        B * a ^ (10 : ℕ) * (Real.log L) ^ (10 : ℕ) * L ^ (-100 : ℝ) := by dsimp [C]; ring
  rw [heq] at hbound
  exact hbound.trans (by linarith only [herror])

#print axioms eventually_reduced_boolean_padding_cost

end ReflectedLiouville
