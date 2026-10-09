import ReflectedLiouville.CenterBandHoles
import ReflectedLiouville.KMTTypicalCutoff

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

noncomputable abbrev convolutionRoughExponent : ℝ := 99998 / 100000
noncomputable abbrev convolutionSavingExponent : ℝ := 99997 / 100000
noncomputable abbrev convolutionSizeExponent : ℝ := 99999 / 100000
noncomputable abbrev convolutionFourierExponent : ℝ := 1 / 4000
noncomputable abbrev convolutionFinalExponent : ℝ := 1 / 100000

/-- All analytic-scale prerequisites are consequences of the paper's actual
    L scale and rough shift size; none is retained as a published hypothesis. -/
theorem eventually_rough_convolution_scales (A : ℕ) (hA : 1000 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, 3 ≤ N → Real.log (N : ℝ) = L ^ A →
      ∀ (D : ℕ) (Y : ℝ),
        (1 / 2 : ℝ) * Real.exp (L ^ convolutionSizeExponent) ≤ (D : ℝ) →
        (D : ℝ) ≤ 2 * Real.exp (2 * L) → (N : ℝ) * D / 2 ≤ Y → Y / N ≤ (D : ℝ) →
        Real.exp ((Real.log (N : ℝ)) ^ (convolutionRoughExponent / A)) ≤ Y / N ∧
          Y / N ≤ N ∧
          L ^ convolutionFourierExponent ≤ (Real.log (Y / N)) ^ (1 / 3000 : ℝ) ∧
          1 ≤ (D : ℝ) * L ^ (-convolutionFourierExponent) := by
  let κ := convolutionSizeExponent
  let γ := convolutionRoughExponent
  let β := convolutionFourierExponent
  have hκ : 0 < κ := by norm_num [κ, convolutionSizeExponent]
  have hgap : 0 < κ - γ := by norm_num [κ, γ, convolutionSizeExponent, convolutionRoughExponent]
  have hgapβ : 0 < κ / 3000 - β := by norm_num [κ, β, convolutionSizeExponent, convolutionFourierExponent]
  filter_upwards [(tendsto_rpow_atTop hgap).eventually (eventually_ge_atTop (2 : ℝ)),
    (tendsto_rpow_atTop hgapβ).eventually (eventually_ge_atTop (2 : ℝ)),
    (tendsto_rpow_atTop hκ).eventually (eventually_ge_atTop (2 * Real.log 4)),
    (power_exp_power_tendsto_zero β κ hκ).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (2 : ℝ)] with L hgain hgainβ hlarge hpower hL2
  intro N hN hlog D Y hDlow hDhigh hYlow hYhigh
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hAr : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hDpos : (0 : ℝ) < D := (by positivity : 0 < (1 / 2 : ℝ) * Real.exp (L ^ κ)).trans_le hDlow
  have hYp : 0 < Y := (by positivity : 0 < (N : ℝ) * D / 2).trans_le hYlow
  have hRatio : (D : ℝ) / 2 ≤ Y / N := (le_div_iff₀ hNr).mpr (by nlinarith only [hYlow])
  have hlow : Real.exp (L ^ κ) / 4 ≤ Y / N := by linarith only [hDlow, hRatio]
  have hratioPos : 0 < Y / N := div_pos hYp hNr
  have hlogRatio : L ^ κ - Real.log 4 ≤ Real.log (Y / N) := by
    have ht := Real.log_le_log (by positivity : 0 < Real.exp (L ^ κ) / 4) hlow
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at ht
  have hhalfLog : L ^ κ / 2 ≤ Real.log (Y / N) := by linarith only [hlogRatio, hlarge]
  have hgamma := halve_power_ge L κ γ hLp hgain
  have hNpower : (Real.log (N : ℝ)) ^ (γ / A) = L ^ γ := by
    rw [hlog, ← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    congr 1
    field_simp [hAr.ne']
  have hFourier : Real.exp ((Real.log (N : ℝ)) ^ (γ / A)) ≤ Y / N := by
    rw [hNpower]
    have ht := Real.exp_le_exp.mpr (hgamma.trans hhalfLog)
    rwa [Real.exp_log hratioPos] at ht
  have hlogNexp : Real.exp (L ^ A) = (N : ℝ) := by rw [← hlog, Real.exp_log hNr]
  have hPow3 : 3 * L ≤ L ^ A := by
    have hLsq : 3 ≤ L ^ (2 : ℕ) := by nlinarith only [hL2]
    have ht := mul_nonneg (sub_nonneg.mpr hLsq) hLp.le
    have hcube : 3 * L ≤ L ^ (3 : ℕ) := by nlinarith only [ht]
    exact hcube.trans (pow_le_pow_right₀ hL (by omega : 3 ≤ A))
  have hupperN : 2 * Real.exp (2 * L) ≤ (N : ℝ) := by
    have hExpL : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc
      _ ≤ Real.exp L * Real.exp (2 * L) := mul_le_mul_of_nonneg_right hExpL (Real.exp_pos _).le
      _ = Real.exp (3 * L) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (L ^ A) := Real.exp_le_exp.mpr hPow3
      _ = _ := hlogNexp
  have hUpper := hYhigh.trans (hDhigh.trans hupperN)
  have hHalf : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 3000 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (by norm_num : (1 / 3000 : ℝ) ≤ 1)
  have hid : (L ^ κ / 2) ^ (1 / 3000 : ℝ) =
      (1 / 2 : ℝ) ^ (1 / 3000 : ℝ) * L ^ (κ / 3000) := by
    rw [show L ^ κ / 2 = (1 / 2 : ℝ) * L ^ κ by ring,
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hLp.le _), ← Real.rpow_mul hLp.le]
    congr 1
    ring
  have hRate : L ^ β ≤ (Real.log (Y / N)) ^ (1 / 3000 : ℝ) := by
    calc
      _ ≤ L ^ (κ / 3000) / 2 := halve_power_ge L _ _ hLp hgainβ
      _ ≤ (L ^ κ / 2) ^ (1 / 3000 : ℝ) := by
        rw [hid]
        have ht := mul_le_mul_of_nonneg_right hHalf (Real.rpow_nonneg hLp.le (κ / 3000))
        convert ht using 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hhalfLog (by norm_num)
  have hDβ : L ^ β ≤ (D : ℝ) := by
    have ht := (div_le_iff₀ (Real.exp_pos (L ^ κ))).mp hpower
    linarith only [ht, hDlow]
  have hDgain : 1 ≤ (D : ℝ) * L ^ (-β) := by
    have ht := mul_le_mul_of_nonneg_right hDβ (Real.rpow_nonneg hLp.le (-β))
    have hid : L ^ β * L ^ (-β) = 1 := by rw [← Real.rpow_add hLp]; norm_num
    rwa [hid] at ht
  exact ⟨hFourier, hUpper, hRate, hDgain⟩

#print axioms eventually_rough_convolution_scales

end ReflectedLiouville
