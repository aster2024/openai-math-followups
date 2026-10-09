import ReflectedLiouville.ReflectedDeletionBin

set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter
open scoped BigOperators

namespace ReflectedLiouville

lemma eventually_deletion_scale_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ C : ℝ, 0 ≤ C →
      let J := reflectionBandCount W (1/100000) L
      let η := Real.exp (-(J : ℝ))
      (2 : ℝ)^J*(C*(Real.log L)^(10 : ℕ)/Real.exp (4*J) + L ^ (-90 : ℝ) + Real.exp (-2*W*J)) +
        2*Real.exp (-L ^ (9/10 : ℝ)) ≤ (C+4)*η := by
  let c := (1/100000 : ℝ)/(6*W)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10 (2*c) (by positivity)).comp Real.tendsto_log_atTop
  have hevent := hlim.eventually (eventually_le_nhds (Real.exp_pos (-2)))
  have hrare := (power_exp_power_tendsto_zero 1 (9/10) (by norm_num)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hevent,hrare,eventually_ge_atTop (2 : ℝ)] with L hsmall hrare hL
  intro C hC
  dsimp only
  let J := reflectionBandCount W (1/100000) L
  let η := Real.exp (-(J : ℝ))
  have hLone : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hη : 0 < η := Real.exp_pos _
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hLone
  have h2 : (2 : ℝ)^J ≤ Real.exp (J : ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le J
    simpa only [← Real.exp_nat_mul,mul_one] using hp
  have hJbudget := reflectionBandCount_mul_bound W (1/100000) L (by linarith) (by norm_num) hLone
  have hJlog : (J : ℝ) ≤ Real.log L := by
    have hw := mul_le_mul_of_nonneg_left hW hJ0
    nlinarith only [hJbudget,hw,hlog]
  have hExpJ : Real.exp (J : ℝ) ≤ L := by
    simpa only [Real.exp_log hLp] using Real.exp_le_exp.mpr hJlog
  have hFloor : c*Real.log L - 1 ≤ (J : ℝ) := by
    have hh := Nat.lt_floor_add_one ((1/100000 : ℝ)*Real.log L/(6*W))
    have he : c*Real.log L = (1/100000 : ℝ)*Real.log L/(6*W) := by dsimp only [c]; ring
    rw [he]
    dsimp only [J,reflectionBandCount]
    linarith only [hh]
  have hTail : Real.exp (-2*(J : ℝ)) ≤ Real.exp 2 * Real.exp (-(2*c)*Real.log L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hFloor]
  have hSmall : Real.exp (-2*(J : ℝ)) * (Real.log L)^(10 : ℕ) ≤ 1 := by
    have hs : (Real.log L)^(10 : ℕ)*Real.exp (-(2*c)*Real.log L) ≤ Real.exp (-2) := by
      have he : (Real.log L)^(10 : ℝ) = (Real.log L)^(10 : ℕ) := by
        convert Real.rpow_natCast (Real.log L) 10 using 1
      simpa only [Function.comp_apply,he] using hsmall
    have ht := mul_le_mul_of_nonneg_right hTail (by positivity : 0 ≤ (Real.log L)^(10 : ℕ))
    have hu := mul_le_mul_of_nonneg_left hs (Real.exp_pos 2).le
    have he : Real.exp 2*Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    rw [he] at hu
    nlinarith only [ht,hu]
  have hPad : (2 : ℝ)^J * ((Real.log L)^(10 : ℕ)/Real.exp (4*J)) ≤ η := by
    have hs := mul_le_mul_of_nonneg_left hSmall (Real.exp_pos (-(J : ℝ))).le
    have hpoly := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ (Real.log L)^(10 : ℕ)/Real.exp (4*J))
    apply hpoly.trans
    dsimp only [η] at hs ⊢
    have he : Real.exp (J : ℝ)/Real.exp (4*J) = Real.exp (-(J : ℝ))*Real.exp (-2*(J : ℝ)) := by
      rw [← Real.exp_sub,← Real.exp_add]
      congr 1
      ring
    rw [show Real.exp (J : ℝ)*((Real.log L)^(10 : ℕ)/Real.exp (4*J)) =
      (Real.exp (J : ℝ)/Real.exp (4*J))*(Real.log L)^(10 : ℕ) by ring,he]
    convert hs using 1 <;> ring
  have hLow : (2 : ℝ)^J * L ^ (-90 : ℝ) ≤ η := by
    have hgain : (2 : ℝ)^J*Real.exp (J : ℝ) ≤ L^2 := by
      have hp := mul_le_mul h2 hExpJ (Real.exp_pos _).le (Real.exp_pos _).le
      have he := mul_le_mul_of_nonneg_left hExpJ hLp.le
      nlinarith only [hp,he]
    have hpow : L ^ (2 : ℕ)*L ^ (-90 : ℝ) ≤ 1 := by
      rw [← Real.rpow_natCast,← Real.rpow_add hLp]
      rw [show ((2 : ℕ) : ℝ) + (-90 : ℝ) = -88 by norm_num]
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hLone (by norm_num : (-88 : ℝ) ≤ 0)
    have hh := mul_le_mul_of_nonneg_right hgain (Real.rpow_nonneg hLp.le (-90))
    have hb := hh.trans hpow
    have ht := mul_le_mul_of_nonneg_right hb hη.le
    have he : Real.exp (J : ℝ)*η = 1 := by dsimp only [η]; rw [Real.exp_neg,mul_inv_cancel₀ (Real.exp_pos _).ne']
    have hid : ((2 : ℝ)^J*Real.exp (J : ℝ)*L ^ (-90 : ℝ))*η = (2 : ℝ)^J*L ^ (-90 : ℝ) := by
      calc
        _ = ((2 : ℝ)^J*L ^ (-90 : ℝ))*(Real.exp (J : ℝ)*η) := by ring
        _ = _ := by rw [he,mul_one]
    rw [hid,one_mul] at ht
    exact ht
  have hDeg : (2 : ℝ)^J * Real.exp (-2*W*J) ≤ η := by
    apply (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le).trans
    dsimp only [η]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hw := mul_le_mul_of_nonneg_right hW hJ0
    nlinarith only [hw]
  have hRare : Real.exp (-L ^ (9/10 : ℝ)) ≤ η := by
    have hh : L/Real.exp (L ^ (9/10 : ℝ)) ≤ 1 := by simpa only [Real.rpow_one] using hrare
    have hx := (div_le_div_of_nonneg_right hExpJ (Real.exp_pos _).le).trans hh
    have ht := mul_le_mul_of_nonneg_left hx hη.le
    have he : η*Real.exp (J : ℝ) = 1 := by dsimp only [η]; rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_pos _).ne']
    have hid : η*(Real.exp (J : ℝ)/Real.exp (L ^ (9/10 : ℝ))) = Real.exp (-L ^ (9/10 : ℝ)) := by
      rw [← mul_div_assoc,he,Real.exp_neg]
      ring
    rw [hid,mul_one] at ht
    exact ht
  have hPadC := mul_le_mul_of_nonneg_left hPad hC
  have hPadC' : (2 : ℝ)^J*(C*(Real.log L)^(10 : ℕ)/Real.exp (4*J)) ≤ C*η := by
    convert hPadC using 1 <;> ring
  have hsum := add_le_add (add_le_add hPadC' hLow) hDeg
  have hrare2 := mul_le_mul_of_nonneg_left hRare (by norm_num : (0 : ℝ) ≤ 2)
  have ht := add_le_add hsum hrare2
  convert ht using 1 <;> ring

#print axioms eventually_deletion_scale_saving
end ReflectedLiouville
