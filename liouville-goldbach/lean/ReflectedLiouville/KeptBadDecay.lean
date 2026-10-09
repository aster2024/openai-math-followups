import ReflectedLiouville.ActualKeptBound

set_option autoImplicit false
open Filter
open scoped BigOperators

namespace ReflectedLiouville

lemma eventually_kept_bad_decay (W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) :
    ∀ᶠ L : ℝ in atTop,
      let J := reflectionBandCount W δ L
      404 * Real.exp (5*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) *
        Real.exp (-(2*⌊L⌋₊ : ℕ)) ≤ Real.exp (-(J : ℝ)) := by
  let p := 6 + Real.log (8*W) + 400*Real.log 5
  have hlim := (power_exp_power_tendsto_zero p 1 (by norm_num)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/404))
  filter_upwards [hlim,eventually_ge_atTop (2 : ℝ)] with L hsmall hL
  dsimp only
  let J := reflectionBandCount W δ L
  have hLone : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hJnonneg : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hJbudget := (reflection_degree_budget W δ L hW hδ hδone hLone).2.2
  have hJlog : (J : ℝ) ≤ Real.log L := by
    have hprod := mul_le_mul_of_nonneg_left hW hJnonneg
    nlinarith only [hJbudget,hprod]
  have h8 : 0 < 8*W := by linarith
  have hLog8 : 0 ≤ Real.log (8*W) := Real.log_nonneg (by linarith)
  have hPow : (8*W)^J = Real.exp ((J : ℝ)*Real.log (8*W)) := by
    rw [Real.exp_nat_mul,Real.exp_log h8]
  have hPoly : Real.exp (6*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) ≤ L ^ p := by
    rw [hPow,Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5),
      ← Real.exp_add,← Real.exp_add,Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hJlog hLog8
    dsimp only [p]
    nlinarith only [hJlog,hm]
  have hFloor : L ≤ (2*⌊L⌋₊ : ℕ) := by
    have hf := Nat.lt_floor_add_one L
    push_cast
    linarith only [hf,hL]
  have hTail : Real.exp (-(2*⌊L⌋₊ : ℕ)) ≤ Real.exp (-L) :=
    Real.exp_le_exp.mpr (by linarith only [hFloor])
  have hAll : 404 * Real.exp (6*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) *
      Real.exp (-(2*⌊L⌋₊ : ℕ)) ≤ 1 := by
    have hp := mul_le_mul hPoly hTail (Real.exp_pos _).le (Real.rpow_nonneg hLp.le p)
    have hs : 404*(L ^ p / Real.exp L) ≤ 1 := by
      simp only [Real.rpow_one] at hsmall
      linarith only [hsmall]
    calc
      _ = 404 * (Real.exp (6*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) *
          Real.exp (-(2*⌊L⌋₊ : ℕ))) := by ring
      _ ≤ 404 * (L^p * Real.exp (-L)) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 404*(L^p/Real.exp L) := by rw [Real.exp_neg]; ring
      _ ≤ _ := hs
  have hFinal := mul_le_mul_of_nonneg_right hAll (Real.exp_pos (-(J : ℝ))).le
  have hExp : Real.exp (6*J) * Real.exp (-(J : ℝ)) = Real.exp (5*J) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hId : 404 * Real.exp (6*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) *
      Real.exp (-(2*⌊L⌋₊ : ℕ)) * Real.exp (-(J : ℝ)) =
      404 * Real.exp (5*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) * Real.exp (-(2*⌊L⌋₊ : ℕ)) := by
    calc
      _ = 404 * (Real.exp (6*J) * Real.exp (-(J : ℝ))) * (8*W)^J *
        (5 : ℝ)^(400*Real.log L) * Real.exp (-(2*⌊L⌋₊ : ℕ)) := by ring
      _ = _ := by rw [hExp]
  rw [hId,one_mul] at hFinal
  exact hFinal

#print axioms eventually_kept_bad_decay
end ReflectedLiouville
