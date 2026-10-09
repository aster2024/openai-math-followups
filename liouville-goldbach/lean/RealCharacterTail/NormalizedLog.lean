import RealCharacterTail.EulerLog

set_option autoImplicit false
open scoped Topology
open Set Filter

namespace RealCharacterTail

/-- Continuous exponential lifts agreeing at a point agree locally. -/
theorem eventuallyEq_of_exp_eq {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) (hg : ContinuousAt g z) (hz : f z = g z)
    (he : (fun w => Complex.exp (f w)) =ᶠ[𝓝 z] fun w => Complex.exp (g w)) :
    f =ᶠ[𝓝 z] g := by
  have hc : ContinuousAt (fun w => (f w - g w).im) z :=
    Complex.continuous_im.continuousAt.comp (hf.sub hg)
  have hl : Tendsto (fun w => (f w - g w).im) (𝓝 z) (𝓝 0) := by
    simpa only [ContinuousAt, hz, sub_self, Complex.zero_im] using hc
  filter_upwards [he, hl.eventually (Ioo_mem_nhds
    (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)] with w hw hs
  have hsub : Complex.exp (f w - g w) = 1 := by
    rw [Complex.exp_sub, hw]
    exact div_self (Complex.exp_ne_zero _)
  have hzero : f w - g w = 0 := by
    rw [← Complex.log_exp hs.1 hs.2.le, hsub, Complex.log_one]
  exact sub_eq_zero.mp hzero

/-- The half-plane logarithm normalized by the absolutely convergent Euler series. -/
theorem exists_normalized_log {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re} ∧
      (∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s) ∧
      (∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s) := by
  obtain ⟨H, hHd, hHe⟩ := exists_holomorphic_log χ hχ
  let G := LSeries (logCoeff χ)
  let K : ℂ → ℂ := fun s => H s - H 3 + G 3
  let U : Set ℂ := {s | (7 / 8 : ℝ) < s.re}
  let V : Set ℂ := {s | (1 : ℝ) < s.re}
  have hUo : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hVo : IsOpen V := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hVsub : V ⊆ U := by
    intro s hs
    change (1 : ℝ) < s.re at hs
    change (7 / 8 : ℝ) < s.re
    linarith
  have hKd : DifferentiableOn ℂ K U := (hHd.sub_const (H 3)).add_const (G 3)
  have hKe : ∀ s ∈ U, Complex.exp (K s) = χ.LFunction s := by
    intro s hs
    have h3 : (7 / 8 : ℝ) < (3 : ℂ).re := by norm_num
    have hg3 : Complex.exp (G 3) = χ.LFunction 3 := exp_logEuler χ (by norm_num)
    change Complex.exp (H s - H 3 + G 3) = χ.LFunction s
    rw [Complex.exp_add, Complex.exp_sub, hHe s hs, hHe 3 h3, hg3]
    exact div_mul_cancel₀ _ (nonprincipal_nonzero χ hχ h3)
  have hGd : DifferentiableOn ℂ G V := fun s hs =>
    (logEuler_differentiableAt χ hs).differentiableWithinAt
  have h3V : (3 : ℂ) ∈ V := by norm_num [V]
  have hK3 : K 3 = G 3 := by simp [K]
  have hExp : (fun s => Complex.exp (K s)) =ᶠ[𝓝 (3 : ℂ)]
      fun s => Complex.exp (G s) := by
    filter_upwards [hVo.mem_nhds h3V] with s hs
    rw [hKe s (hVsub hs)]
    exact (exp_logEuler χ hs).symm
  have heqlocal := eventuallyEq_of_exp_eq
    (hKd.continuousOn.continuousAt (hUo.mem_nhds (hVsub h3V)))
    (hGd.continuousOn.continuousAt (hVo.mem_nhds h3V)) hK3 hExp
  have hconn : IsPreconnected V :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have heq : EqOn K G V := (hKd.mono hVsub).analyticOnNhd hVo
    |>.eqOn_of_preconnected_of_eventuallyEq (hGd.analyticOnNhd hVo) hconn h3V heqlocal
  exact ⟨K, hKd, hKe, heq⟩

#print axioms eventuallyEq_of_exp_eq
#print axioms exists_normalized_log

end RealCharacterTail
