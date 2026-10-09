import ReflectedLiouville.FourierScaleAdmissibility
import ReflectedLiouville.FourierWindowReduction
import ReflectedLiouville.DirichletApproximation

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped BigOperators

namespace ReflectedLiouville

/-- Paper Lemma fourier, obtained from the reviewed KMT and MRT statements. The
    frequency remains fixed outside every residue/window average. -/
theorem quotient_liouville_fourier
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) : QuotientFourierBound := by
  intro ν₀ hν₀ hν₀₁
  let ν := ν₀ / 2
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hν₁ : ν ≤ 1 := by dsimp [ν]; linarith
  obtain ⟨B, X₀, hB, hX₀, hrational⟩ := rational_window_uniform_mean h_KMT h_MRT ν hν hν₁
  simp only [Real.rpow_eq_pow, neg_div] at hrational
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp eventually_fourier_power_margins
  have hDlim := Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop hν₀).comp Real.tendsto_log_atTop)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      X₀ ≤ (N : ℝ) ∧ 3 ≤ N ∧
        max D₀ (Real.exp 1) ≤ Real.exp ((Real.log (N : ℝ)) ^ ν₀) ∧
        ∀ D : ℝ, Real.exp ((Real.log (N : ℝ)) ^ ν₀) ≤ D → D ≤ N → 1 < D →
          Real.log D / 8 ≤ Real.log (⌊D ^ (1 / 4 : ℝ)⌋₊ : ℝ) →
          Real.exp ((Real.log ((N : ℝ) * (⌊D⌋₊ : ℝ))) ^ ν) ≤ (⌊D ^ (1 / 4 : ℝ)⌋₊ : ℝ) := by
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop X₀), eventually_ge_atTop (3 : ℕ),
      (hDlim.comp hcast).eventually (eventually_ge_atTop (max D₀ (Real.exp 1))),
      hcast.eventually (eventually_fourier_scale_admissible ν₀ hν₀)] with N hN hN3 hMin hScale
    exact ⟨hN, hN3, hMin, hScale⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hlarge
  refine ⟨9 * B + 9, by positivity, max 3 N₀, le_max_left _ _, ?_⟩
  intro N hN D hDlow hDN θ
  obtain ⟨hNX₀, hN3, hMin, hScale⟩ := hN₀ N ((le_max_right _ _).trans hN)
  let K := ⌊D⌋₊
  let Q := ⌊D ^ (1 / 3 : ℝ)⌋₊
  let M := ⌊D ^ (1 / 4 : ℝ)⌋₊
  have hDD₀ : D₀ ≤ D := ((le_max_left _ _).trans hMin).trans hDlow
  obtain ⟨hD, hM10, hMQ, hQQK, hlogM, hQKsave, hMsave, hMQsave, hQQsave⟩ := hD₀ D hDD₀
  change 10 ≤ M at hM10
  change M ≤ Q at hMQ
  change Q * Q ≤ K at hQQK
  have hNp : 0 < N := by omega
  have hQp : 0 < Q := by omega
  have hMp : 0 < M := by omega
  have hKp : 0 < K := lt_of_lt_of_le (Nat.mul_pos hQp hQp) hQQK
  letI : NeZero N := ⟨hNp.ne'⟩
  letI : NeZero K := ⟨hKp.ne'⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hDexp : Real.exp 1 ≤ D := ((le_max_right _ _).trans hMin).trans hDlow
  have hL1 : 1 ≤ Real.log D := by
    have ht := Real.log_le_log (Real.exp_pos 1) hDexp
    rwa [Real.log_exp] at ht
  have hL : 0 < Real.log D := by linarith
  have hMlarge : Real.exp ((Real.log ((N : ℝ) * K)) ^ ν) ≤ (M : ℝ) :=
    hScale D hDlow hDN hD hlogM
  obtain ⟨a, q, β, hq, hqQ, hθ, hβ⟩ := exists_rational_frequency θ Q hQp
  letI : NeZero q := ⟨hq.ne'⟩
  let h := q * Q
  let m := q * M
  have hh : 0 < h := Nat.mul_pos hq hQp
  have hmh : m ≤ h := Nat.mul_le_mul_left q hMQ
  have hhQ : h ≤ Q * Q := Nat.mul_le_mul_right Q hqQ
  have hhK : h ≤ K := hhQ.trans hQQK
  have hm10 : 10 * q ≤ m := by dsimp [m]; nlinarith
  have hmpos : 0 < m := Nat.mul_pos hq hMp
  have hX : X₀ ≤ ((N * m : ℕ) : ℝ) := hNX₀.trans (by
    exact_mod_cast (show N ≤ N * m by nlinarith))
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQp
  have hratio : (m : ℝ) / q = (M : ℝ) := by dsimp [m]; push_cast; field_simp
  have hR : Real.exp ((Real.log ((N * K : ℕ) : ℝ)) ^ ν) ≤ (m : ℝ) / q := by
    rw [hratio, Nat.cast_mul]
    exact hMlarge
  have hlog : Real.log D / 8 ≤ Real.log ((m : ℝ) / q) := by rw [hratio]; exact hlogM
  have hhsmall : (h : ℝ) / K ≤ (Real.log D) ^ (-(1 / 1000) : ℝ) := by
    have hhr : (h : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hhQ
    exact (div_le_div_of_nonneg_right hhr (by positivity)).trans hQKsave
  have hqsmall : (q : ℝ) ^ (2 : ℕ) ≤ (m : ℝ) ^ (2 : ℕ) * (Real.log D) ^ (-(1 / 1000) : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hMsave (sq_nonneg (q : ℝ))
    convert ht using 1 <;> try simp only [m, M, Nat.cast_mul]
    all_goals ring
  have hbound := hrational N q K h m (Real.log D) hL hmh hhK hm10 hX hR hlog hhsmall hqsmall a
  have hphase : (2 * Real.pi * |β|) * h ≤ 8 := by
    have hb : |β| * (h : ℝ) ≤ 1 := by
      have hb := (le_div_iff₀ (mul_pos hqr hQr)).mp hβ
      simpa only [h, Nat.cast_mul] using hb
    have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)
    have hpi := Real.pi_lt_four
    nlinarith
  have hsmall : (m : ℝ) ^ (2 : ℕ) ≤ (h : ℝ) ^ (2 : ℕ) * (Real.log D) ^ (-(1 / 2000) : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hMQsave (sq_nonneg (q : ℝ))
    convert ht using 1 <;> try simp only [m, h, M, Q, Nat.cast_mul]
    all_goals ring
  have hmean := quotientWindowMean_abel_bound N K h m ((a : ℝ) / q) β B
    ((Real.log D) ^ (-(1 / 2000) : ℝ)) hB.le (Real.rpow_nonneg hL.le _) hmh hbound hphase hsmall
  rw [← hθ] at hmean
  have hpref := quotient_fourier_of_window N K h θ ((9 * B + 8) * (Real.log D) ^ (-(1 / 2000) : ℝ)) hh
    (by convert hmean using 1 <;> ring)
  have hKhi : (K : ℝ) ≤ D := Nat.floor_le (by linarith)
  have hsave : 0 ≤ (Real.log D) ^ (-(1 / 2000) : ℝ) := Real.rpow_nonneg hL.le _
  have hKscaled := mul_le_mul_of_nonneg_left hKhi (by positivity :
    0 ≤ (9 * B + 8) * (Real.log D) ^ (-(1 / 2000) : ℝ))
  have herror : (h : ℝ) + 1 ≤ D * (Real.log D) ^ (-(1 / 2000) : ℝ) := by
    have he : (h : ℝ) + 1 ≤ ((Q * Q : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hhQ 1
    exact he.trans hQQsave
  have hnorm : (∑ r : Fin N, ‖quotientExponentialSum N D (r.val + 1) θ‖) / (N : ℝ) ≤
      (9 * B + 9) * D * (Real.log D) ^ (-(1 / 2000) : ℝ) := by
    change (∑ r : Fin N, ‖∑ k ∈ Finset.range K, liouville (N * k + (r.val + 1)) *
      OAI.TwoPointCorrelations.additiveCharacter θ k‖) / (N : ℝ) ≤ _
    nlinarith only [hpref, hKscaled, herror]
  have hsave' : (Real.log D) ^ (-(1 / 2000) : ℝ) ≤ (Real.log D) ^ (-(1 / 3000) : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_left hsave' (by positivity : 0 ≤ (9 * B + 9) * D))
  rw [sum_fin_shift_eq_Icc N (fun r => ‖quotientExponentialSum N D r θ‖)] at hnorm'
  simpa only [Real.rpow_eq_pow, neg_div, Real.rpow_neg hL.le, div_eq_mul_inv] using hnorm'

#print axioms quotient_liouville_fourier

end ReflectedLiouville
