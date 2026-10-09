import MRTRepulsion.Algebra
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
namespace MRTRepulsion

lemma floor_ge_hundred {X : ℝ} (hX : 100 ≤ X) : 100 ≤ ⌊X⌋₊ := by
  exact (Nat.le_floor_iff (by linarith : 0 ≤ X)).mpr (by simpa using hX)

lemma floor_scale {X : ℝ} (hX : 100 ≤ X) : X ≤ 2*(⌊X⌋₊ : ℝ) := by
  have hn : (100 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast floor_ge_hundred hX
  have hf := Nat.lt_floor_add_one X
  linarith only [hn,hf]

lemma floor_exp_one {X : ℝ} (hX : 100 ≤ X) : Real.exp 1 ≤ (⌊X⌋₊ : ℝ) := by
  have hn : (100 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast floor_ge_hundred hX
  linarith [Real.exp_one_lt_three]

/-- The real cutoff changes log log by at most one in the target range. -/
lemma loglog_floor {X : ℝ} (hX : 100 ≤ X) :
    Real.log (Real.log X) ≤ Real.log (Real.log (⌊X⌋₊ : ℝ)) + 1 := by
  let N : ℝ := ⌊X⌋₊
  have hN : (100 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast floor_ge_hundred hX
  have hN0 : 0 < N := by linarith
  have hN2 : 2 ≤ N := by linarith
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hX0 : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hscale : X ≤ 2*N := floor_scale hX
  have hl := Real.log_le_log hX0 hscale
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hl
  have hl2 : Real.log X ≤ 2*Real.log N := by linarith only [hl,hlog2]
  have hll := Real.log_le_log hlX hl2
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlN.ne'] at hll
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact hll.trans (by linarith only [htwo])

lemma large_sqrt_margin (L D B : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (h : L/16-B ≤ D) :
    (1/4 : ℝ)*Real.sqrt L - Real.sqrt B ≤ Real.sqrt D := by
  have hs : (Real.sqrt L/4)^2 ≤ (Real.sqrt D+Real.sqrt B)^2 := by
    nlinarith only [h,Real.sq_sqrt hL,Real.sq_sqrt hD,Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg B)]
  have hr := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt L/4)
    (by positivity : 0 ≤ Real.sqrt D+Real.sqrt B)).mp hs
  linarith only [hr]

lemma small_sqrt_margin (D₀ D B : ℝ) (hD₀ : 0 ≤ D₀) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (h : D₀ ≤ 5*D+B) :
    (1/3 : ℝ)*Real.sqrt D₀ - Real.sqrt B ≤ Real.sqrt D := by
  have hs : (Real.sqrt D₀)^2 ≤ (3*Real.sqrt D+Real.sqrt B)^2 := by
    nlinarith only [h,hD,Real.sq_sqrt hD₀,Real.sq_sqrt hD,Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg B)]
  have hr := (sq_le_sq₀ (Real.sqrt_nonneg D₀)
    (by positivity : 0 ≤ 3*Real.sqrt D+Real.sqrt B)).mp hs
  have hBroot := Real.sqrt_nonneg B
  linarith only [hr,hBroot]

#print axioms loglog_floor
#print axioms large_sqrt_margin
#print axioms small_sqrt_margin
end MRTRepulsion
