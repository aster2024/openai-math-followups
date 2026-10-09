import ReflectedLiouville.ActualRawDilation

set_option autoImplicit false
open scoped BigOperators Classical

namespace ReflectedLiouville

lemma reflected_dilation_recovery (r c S₀ M ε B : ℝ) (hM : 0 < M)
    (hMass : M / 2 ≤ S₀) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hRaw : |r| ≤ B * M) (hDilation : |r - S₀ * c| ≤ ε * M) : |c| ≤ 2 * (ε + B) := by
  have hS : 0 < S₀ := (by positivity : 0 < M / 2).trans_le hMass
  have htriangle := abs_add_le (S₀ * c - r) r
  have hid : S₀ * c - r + r = S₀ * c := by ring
  rw [hid, abs_mul, abs_of_pos hS, abs_sub_comm (S₀ * c) r] at htriangle
  have hupper : S₀ * |c| ≤ (ε + B) * M := by linarith only [htriangle, hRaw, hDilation]
  have hlower := mul_le_mul_of_nonneg_right hMass (abs_nonneg c)
  have hscaled : |c| ≤ ((ε + B) * M) / (M / 2) :=
    (le_div_iff₀ (by positivity : 0 < M / 2)).mpr (by nlinarith only [hlower, hupper])
  convert hscaled using 1 <;> field_simp [hM.ne'] <;> ring

/-- A derived project target for the last stage of the paper, never a
    published input or axiom. It must be discharged by kept/deleted/centering. -/
def BinnedReflectedSaving (A : ℕ) (W δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    |reflectedSum N| / (N : ℝ) ≤ C * Real.exp (-(reflectionBandCount W δ
      ((Real.log (N : ℝ)) ^ (1 / (A : ℝ))) : ℝ))

/-- Exact conversion of the positive floor-band exponent to the literal
    logarithmic saving statement. The hypothesis is an explicit derived
    target, not an extra analytic input to the final theorem. -/
theorem log_saving_of_binned_estimate (A : ℕ) (hA : 0 < A) (W δ : ℝ)
    (hW : 0 < W) (hδ : 0 < δ) (hbin : BinnedReflectedSaving A W δ) : ReflectedLogSaving := by
  obtain ⟨C, hC, N₀, hN₀, hb⟩ := hbin
  let c := δ / (6 * W * (A : ℝ))
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, C * Real.exp 1, by positivity, N₀, hN₀, ?_⟩
  intro N hN
  have hn : 3 ≤ N := hN₀.trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let L := (Real.log (N : ℝ)) ^ (1 / (A : ℝ))
  let J := reflectionBandCount W δ L
  have hL : 0 < L := Real.rpow_pos_of_pos hlog _
  have hfloor := Nat.lt_floor_add_one (δ * Real.log L / (6 * W))
  have hexp : Real.exp (-(J : ℝ)) ≤ Real.exp (1 - δ * Real.log L / (6 * W)) := by
    apply Real.exp_le_exp.mpr
    change δ * Real.log L / (6 * W) < (J : ℝ) + 1 at hfloor
    linarith only [hfloor]
  have hlogId : δ * Real.log L / (6 * W) = c * Real.log (Real.log (N : ℝ)) := by
    dsimp only [L, c]
    rw [Real.log_rpow hlog]
    field_simp [hW.ne', hAr.ne']
    <;> ring
  have hpower : Real.exp (1 - c * Real.log (Real.log (N : ℝ))) =
      Real.exp 1 * (Real.log (N : ℝ)) ^ (-c) := by
    rw [Real.exp_sub, Real.rpow_def_of_pos hlog]
    rw [show Real.log (Real.log (N : ℝ)) * (-c) = -(c * Real.log (Real.log (N : ℝ))) by ring,
      Real.exp_neg]
    ring
  rw [hlogId, hpower] at hexp
  have hbound := (hb N hN).trans (mul_le_mul_of_nonneg_left hexp hC.le)
  have hsum := (div_le_iff₀ hNr).mp hbound
  apply hsum.trans_eq
  simp only [Real.rpow_eq_pow, Real.rpow_neg hlog.le, div_eq_mul_inv]
  ring

#print axioms log_saving_of_binned_estimate

end ReflectedLiouville
