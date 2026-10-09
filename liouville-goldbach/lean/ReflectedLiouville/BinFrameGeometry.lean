import ReflectedLiouville.KeptFullPairing
import ReflectedLiouville.ReflectionFiniteGeometry
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reflected_bin_frame_geometry (N : ℕ) (hN : 0 < N) (L η : ℝ)
    (hL : 2 ≤ L) (hη : 0 < η) (hηsmall : η ≤ 1 / 2)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    let T := reflectionBinCutoff N η j
    let U := Real.exp η * T
    let B := ⌈Real.exp (100 * L + 1)⌉₊ + 2
    (N : ℝ) ≤ T ∧ (N : ℝ) ≤ U ∧ U ≤ 3 * T ∧
      T / N ≤ (B : ℝ) ∧ U / N + 1 ≤ (B : ℝ) ∧
      2 * (B + 1) ≤ ⌈Real.exp (103 * L)⌉₊ := by
  dsimp only
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hj0,hjL⟩ := (mem_paddingBinIndices_iff L η j hη).mp hj
  have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj0
  have hExp : 1 ≤ Real.exp ((j : ℝ) * η) := Real.one_le_exp (by positivity)
  have hEta : 1 ≤ Real.exp η := Real.one_le_exp hη.le
  have hEta3 : Real.exp η ≤ 3 := (Real.exp_le_exp.mpr (by linarith : η ≤ 1)).trans Real.exp_one_lt_three.le
  have hT : (N : ℝ) ≤ reflectionBinCutoff N η j := by
    unfold reflectionBinCutoff
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp hNr.le
  have hTpos : 0 < reflectionBinCutoff N η j := hNr.trans_le hT
  have hratio : reflectionBinCutoff N η j / N = Real.exp ((j : ℝ) * η) := by
    unfold reflectionBinCutoff
    field_simp
  have hUr : Real.exp η * reflectionBinCutoff N η j / N = Real.exp (η + (j : ℝ) * η) := by
    rw [mul_div_assoc, hratio, ← Real.exp_add]
  have hUbound : Real.exp η * reflectionBinCutoff N η j / N ≤ Real.exp (100 * L + 1) := by
    rw [hUr]
    exact Real.exp_le_exp.mpr (by linarith only [hjL,hηsmall])
  have hTbound : reflectionBinCutoff N η j / N ≤ Real.exp (100 * L + 1) := by
    rw [hratio]
    exact Real.exp_le_exp.mpr (by linarith only [hjL])
  have hceil := Nat.le_ceil (Real.exp (100 * L + 1))
  refine ⟨hT, ?_, ?_, ?_, ?_, reflection_frame_size L hL⟩
  · have he := mul_le_mul_of_nonneg_right hEta hTpos.le
    exact hT.trans (by simpa only [one_mul] using he)
  · exact mul_le_mul_of_nonneg_right hEta3 hTpos.le
  · push_cast
    linarith only [hTbound,hceil]
  · push_cast
    linarith only [hUbound,hceil]

lemma bin_pair_physical_step_upper {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (η : ℝ) (hη : 0 < η) (j : ℤ) (dq : ℕ × ℕ)
    (hdq : dq ∈ data.pairs) (hbin : reflectionPairBin η dq = j) :
    (((N * dq.1 * dq.2 : ℕ) : ℤ) : ℝ) ≤ Real.exp η * reflectionBinCutoff N η j := by
  have ha : 0 < dq.1 * dq.2 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (data.tuple_squarefree _ hdq).ne_zero)
      (Nat.pos_of_ne_zero (data.padding_squarefree _ hdq).ne_zero)
  have hbounds := (paddingBin_eq_iff η 0 (Real.log ((dq.1 * dq.2 : ℕ) : ℝ)) j hη).mp hbin
  have haR : (0 : ℝ) < (dq.1 * dq.2 : ℕ) := by exact_mod_cast ha
  have he : ((dq.1 * dq.2 : ℕ) : ℝ) ≤ Real.exp (((j : ℝ)+1)*η) := by
    simpa only [add_zero, Real.exp_log haR] using (Real.exp_lt_exp.mpr hbounds.2).le
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hExp : Real.exp (((j : ℝ)+1)*η) = Real.exp η * Real.exp ((j : ℝ)*η) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold reflectionBinCutoff
  push_cast
  rw [hExp] at hmul
  push_cast at hmul
  nlinarith only [hmul]

#print axioms reflected_bin_frame_geometry
#print axioms bin_pair_physical_step_upper
end ReflectedLiouville
