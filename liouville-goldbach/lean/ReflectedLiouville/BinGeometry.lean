import ReflectedLiouville.ReflectionPoolBounds
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reflection_bin_card_polynomial (W δ L : ℝ) (hW : 1 ≤ W)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hL : 101 ≤ L) :
    ((paddingBinIndices L (Real.exp (-(reflectionBandCount W δ L : ℝ)))).card : ℝ) ≤
      Real.exp (3 * Real.log L) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hJ := (reflection_degree_budget W δ L hW hδ hδ₁ hLone).2.2
  have hJlog : (reflectionBandCount W δ L : ℝ) ≤ Real.log L := by
    have hnonneg : (0 : ℝ) ≤ reflectionBandCount W δ L := by positivity
    nlinarith only [hJ, hW, hnonneg]
  have he : Real.exp (reflectionBandCount W δ L) ≤ L := by
    simpa only [Real.exp_log hLp] using Real.exp_le_exp.mpr hJlog
  have hη : Real.exp (-(reflectionBandCount W δ L : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hb := paddingBinIndices_card_linear L (Real.exp (-(reflectionBandCount W δ L : ℝ)))
    hLone (Real.exp_pos _) hη
  calc
    _ ≤ 101 * L / Real.exp (-(reflectionBandCount W δ L : ℝ)) := hb
    _ = 101 * L * Real.exp (reflectionBandCount W δ L) := by rw [Real.exp_neg]; field_simp
    _ ≤ 101 * L * L := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ L ^ (3 : ℕ) := by
      have hx := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
      nlinarith only [hx]
    _ = _ := by
      rw [show 3 * Real.log L = (3 : ℕ) * Real.log L by norm_num,
        Real.exp_nat_mul, Real.exp_log hLp]

lemma logarithmic_bin_cutoff_bounds (N a : ℕ) (ha : 0 < a) (j : ℤ) (η : ℝ)
    (hbin : (j : ℝ) * η ≤ Real.log (a : ℝ) ∧ Real.log (a : ℝ) < ((j : ℝ) + 1) * η) :
    (1 - η) * (a : ℝ) * N ≤ (N : ℝ) * Real.exp ((j : ℝ) * η) ∧
      (N : ℝ) * Real.exp ((j : ℝ) * η) ≤ (a : ℝ) * N := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hupper : Real.exp ((j : ℝ) * η) ≤ (a : ℝ) := by
    simpa only [Real.exp_log har] using Real.exp_le_exp.mpr hbin.1
  have hloglower : Real.log (a : ℝ) - η ≤ (j : ℝ) * η := by linarith [hbin.2]
  have hlower := Real.exp_le_exp.mpr hloglower
  rw [Real.exp_sub, Real.exp_log har] at hlower
  have hexp : 1 - η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
  have hid : (a : ℝ) / Real.exp η = (a : ℝ) * Real.exp (-η) := by rw [Real.exp_neg]; ring
  rw [hid] at hlower
  have hlow := (mul_le_mul_of_nonneg_left hexp har.le).trans hlower
  constructor
  · have ht := mul_le_mul_of_nonneg_right hlow (Nat.cast_nonneg N)
    convert ht using 1 <;> ring
  · have ht := mul_le_mul_of_nonneg_right hupper (Nat.cast_nonneg N)
    convert ht using 1 <;> ring

lemma actual_pair_bin_cutoff_bounds (N a : ℕ) (ha : 0 < a) (η : ℝ) (hη : 0 < η) :
    let j := paddingBin η 0 (Real.log (a : ℝ))
    (1 - η) * (a : ℝ) * N ≤ (N : ℝ) * Real.exp ((j : ℝ) * η) ∧
      (N : ℝ) * Real.exp ((j : ℝ) * η) ≤ (a : ℝ) * N := by
  dsimp only
  apply logarithmic_bin_cutoff_bounds N a ha _ η
  simpa only [add_zero] using (paddingBin_eq_iff η 0 (Real.log (a : ℝ)) _ hη).mp rfl

#print axioms actual_pair_bin_cutoff_bounds

end ReflectedLiouville
