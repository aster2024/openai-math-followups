import ReflectedLiouville.RoughMultiplier
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
open MeasureTheory

namespace ReflectedLiouville

/-- An algebraic threshold estimate; it avoids any convention about integrals
    of nonintegrable functions by carrying the needed integrability explicitly. -/
lemma convolution_threshold_pointwise (H M S t b : ℝ)
    (hH : 0 ≤ H) (hHM : H ≤ M) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (ht : 0 < t) (hb : 0 ≤ b) (hbS : b ≤ S) :
    H * b ≤ t * H + (M * S / t ^ (4 : ℕ)) * b ^ (4 : ℕ) := by
  have ht4 : 0 < t ^ (4 : ℕ) := by positivity
  have hcoef : 0 ≤ M * S / t ^ (4 : ℕ) := by positivity
  by_cases hsmall : b ≤ t
  · have hmain := mul_le_mul_of_nonneg_left hsmall hH
    have herr : 0 ≤ (M * S / t ^ (4 : ℕ)) * b ^ (4 : ℕ) := by positivity
    nlinarith only [hmain, herr]
  · have htB : t ≤ b := (lt_of_not_ge hsmall).le
    have hpow := pow_le_pow_left₀ ht.le htB 4
    have hratio : 1 ≤ b ^ (4 : ℕ) / t ^ (4 : ℕ) := (one_le_div ht4).mpr hpow
    have hupper := mul_le_mul hHM hbS hb hM
    have hprod := mul_le_mul_of_nonneg_left hratio (mul_nonneg hM hS)
    have hid : M * S * (b ^ (4 : ℕ) / t ^ (4 : ℕ)) = (M * S / t ^ (4 : ℕ)) * b ^ (4 : ℕ) := by ring
    rw [mul_one, hid] at hprod
    have hfirst : 0 ≤ t * H := mul_nonneg ht.le hH
    nlinarith only [hupper, hprod, hfirst]

theorem convolution_threshold_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Ω → ℝ) (B : Ω → ℂ) (M S t : ℝ)
    (hH : ∀ x, 0 ≤ H x) (hHM : ∀ x, H x ≤ M) (hM : 0 ≤ M) (hS : 0 ≤ S) (ht : 0 < t)
    (hB : ∀ x, ‖B x‖ ≤ S)
    (hIntH : Integrable H μ)
    (hIntFourth : Integrable (fun x => ‖B x‖ ^ (4 : ℕ)) μ)
    (hIntProduct : Integrable (fun x => H x * ‖B x‖) μ) :
    (∫ x, H x * ‖B x‖ ∂μ) ≤ t * (∫ x, H x ∂μ) +
      (M * S / t ^ (4 : ℕ)) * (∫ x, ‖B x‖ ^ (4 : ℕ) ∂μ) := by
  have hRight : Integrable (fun x => t * H x + (M * S / t ^ (4 : ℕ)) * ‖B x‖ ^ (4 : ℕ)) μ :=
    (hIntH.const_mul t).add (hIntFourth.const_mul _)
  have hmono := integral_mono hIntProduct hRight (fun x =>
    convolution_threshold_pointwise (H x) M S t (‖B x‖) (hH x) (hHM x) hM hS ht (norm_nonneg _) (hB x))
  rw [integral_add (hIntH.const_mul t) (hIntFourth.const_mul _), integral_const_mul, integral_const_mul] at hmono
  exact hmono

/-- A normalized form ready for the finite quotient-convolution polynomials. -/
theorem convolution_threshold_of_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Ω → ℝ) (B : Ω → ℂ) (M S t E V Y : ℝ)
    (hH : ∀ x, 0 ≤ H x) (hHM : ∀ x, H x ≤ M) (hM : 0 ≤ M) (hS : 0 ≤ S) (ht : 0 < t) (hY : 0 < Y)
    (hB : ∀ x, ‖B x‖ ≤ S)
    (hIntH : Integrable H μ) (hIntFourth : Integrable (fun x => ‖B x‖ ^ (4 : ℕ)) μ)
    (hIntProduct : Integrable (fun x => H x * ‖B x‖) μ)
    (hEnergy : (∫ x, H x ∂μ) ≤ E) (hFourth : (∫ x, ‖B x‖ ^ (4 : ℕ) ∂μ) ≤ V) :
    (∫ x, H x * ‖B x‖ ∂μ) / Y ≤ (t * E + (M * S / t ^ (4 : ℕ)) * V) / Y := by
  have h := convolution_threshold_integral μ H B M S t hH hHM hM hS ht hB hIntH hIntFourth hIntProduct
  have he := mul_le_mul_of_nonneg_left hEnergy ht.le
  have hf := mul_le_mul_of_nonneg_left hFourth (by positivity : 0 ≤ M * S / t ^ (4 : ℕ))
  apply div_le_div_of_nonneg_right (h.trans (add_le_add he hf)) hY.le

#print axioms convolution_threshold_of_moments

end ReflectedLiouville
