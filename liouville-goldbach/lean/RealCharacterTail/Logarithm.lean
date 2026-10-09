import RealCharacterTail.Growth
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false
open scoped Topology
open Set Filter

namespace RealCharacterTail

/-- A continuous logarithm of a holomorphic function is holomorphic. -/
theorem differentiableAt_of_continuous_log {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : ContinuousAt g z)
    (heq : f =ᶠ[𝓝 z] fun w => Complex.exp (g w)) :
    DifferentiableAt ℂ g z := by
  have hsmall : ∀ᶠ w in 𝓝 z,
      -Real.pi < (g w - g z).im ∧ (g w - g z).im ≤ Real.pi := by
    have hc : ContinuousAt (fun w => (g w - g z).im) z :=
      Complex.continuous_im.continuousAt.comp (hg.sub continuousAt_const)
    have hlim : Tendsto (fun w => (g w - g z).im) (𝓝 z) (𝓝 0) := by
      simpa only [ContinuousAt, sub_self, Complex.zero_im] using hc
    filter_upwards [hlim.eventually (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)] with w hw
    exact ⟨hw.1, hw.2.le⟩
  have hfz : f z = Complex.exp (g z) := heq.eq_of_nhds
  have hne : f z ≠ 0 := hfz ▸ Complex.exp_ne_zero (g z)
  have hlocal : g =ᶠ[𝓝 z] fun w => Complex.log (f w / f z) + g z := by
    filter_upwards [heq, hsmall] with w hw hwi
    rw [hw, hfz, ← Complex.exp_sub, Complex.log_exp hwi.1 hwi.2]
    ring
  have hnorm : f z / f z ∈ Complex.slitPlane := by simp [hne]
  exact (((hf.div_const (f z)).clog hnorm).add_const (g z)).congr_of_eventuallyEq hlocal

/-- A nonprincipal Dirichlet L-function has a holomorphic logarithm throughout
    the proved zero-free half-plane. No estimate is assumed here. -/
theorem exists_holomorphic_log {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re} ∧
      ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s := by
  let U : Set ℂ := {s | (7 / 8 : ℝ) < s.re}
  have ho : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hv : Convex ℝ U := (convex_Ioi (7 / 8 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hn : U.Nonempty := ⟨2, by norm_num [U]⟩
  have hc : IsSimplyConnected U := by
    letI := hv.contractibleSpace hn
    change SimplyConnectedSpace U
    infer_instance
  have hfn : 0 ∉ χ.LFunction '' U := by
    rintro ⟨s, hs, hz⟩
    exact nonprincipal_nonzero χ hχ hs hz
  obtain ⟨H, hH, hExp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hc ho
    (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousOn hfn
  refine ⟨H, ?_, fun s hs => hExp hs⟩
  intro s hs
  have hcont : ContinuousAt H s := hH.continuousAt (ho.mem_nhds hs)
  have heq : χ.LFunction =ᶠ[𝓝 s] fun w => Complex.exp (H w) := by
    filter_upwards [ho.mem_nhds hs] with w hw
    exact (hExp hw).symm
  exact (differentiableAt_of_continuous_log
    (DirichletCharacter.differentiable_LFunction hχ s) hcont heq).differentiableWithinAt

#print axioms differentiableAt_of_continuous_log
#print axioms exists_holomorphic_log

end RealCharacterTail
