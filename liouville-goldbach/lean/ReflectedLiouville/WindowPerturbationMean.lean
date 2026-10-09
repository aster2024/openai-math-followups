import ReflectedLiouville.QuotientWindowMean

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

noncomputable def quotientWindowMean (N K h : ℕ) (θ : ℝ) : ℝ :=
  (∑ v ∈ Finset.range K, ∑ r : Fin N,
    ‖quotientWindowFrequency N (r.val + 1) v h θ‖) / ((N : ℝ) * K)

lemma quotientWindowMean_nonneg (N K h : ℕ) (θ : ℝ) :
    0 ≤ quotientWindowMean N K h θ := by
  unfold quotientWindowMean
  positivity

lemma quotientWindowMean_trivial (N K h : ℕ) [NeZero N] [NeZero K] (θ : ℝ) :
    quotientWindowMean N K h θ ≤ (h : ℝ) := by
  have hden : (0 : ℝ) < (N : ℝ) * K := by
    exact mul_pos (by exact_mod_cast NeZero.pos N) (by exact_mod_cast NeZero.pos K)
  unfold quotientWindowMean
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ ∑ _v ∈ Finset.range K, ∑ _r : Fin N, (h : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum (fun r _ => quotient_window_norm_trivial N (r.val + 1) v h θ)
    _ = _ := by simp; ring

lemma quotientWindowMean_perturbation (N K h : ℕ) [NeZero N] [NeZero K] (α β : ℝ) :
    quotientWindowMean N K h (α + β) ≤ quotientWindowMean N K h α +
      2 * Real.pi * |β| * (∑ j ∈ Finset.range (h - 1), quotientWindowMean N K (j + 1) α) := by
  have hd : 0 ≤ (N : ℝ) * K := by positivity
  have h := div_le_div_of_nonneg_right (quotient_frequency_perturbation_sum N K h α β) hd
  simpa only [quotientWindowMean, add_div, mul_div_assoc, Finset.sum_div] using h

/-- Long prefixes use their averaged analytic bound; short prefixes contribute
    at most m². No frequency or residue is chosen after taking an average. -/
lemma quotientWindowMean_prefix_sum (N K h m : ℕ) [NeZero N] [NeZero K]
    (α B s : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hbound : ∀ t : ℕ, m ≤ t → t ≤ h → quotientWindowMean N K t α ≤ B * t * s) :
    (∑ j ∈ Finset.range (h - 1), quotientWindowMean N K (j + 1) α) ≤
      (m : ℝ) ^ (2 : ℕ) + B * (h : ℝ) ^ (2 : ℕ) * s := by
  have hp : ∀ j ∈ Finset.range (h - 1), quotientWindowMean N K (j + 1) α ≤
      (if j < m then (m : ℝ) else 0) + B * h * s := by
    intro j hj
    have hjh : j + 1 ≤ h := by have := Finset.mem_range.mp hj; omega
    by_cases hjm : j < m
    · rw [if_pos hjm]
      have htr := quotientWindowMean_trivial N K (j + 1) α
      have hjmr : ((j + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast (show j + 1 ≤ m by omega)
      have hpos : 0 ≤ B * (h : ℝ) * s := by positivity
      linarith
    · rw [if_neg hjm, zero_add]
      have hmj : m ≤ j + 1 := by omega
      exact (hbound (j + 1) hmj hjh).trans (by
        have hcast : ((j + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hjh
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hB) hs)
  have hi : (∑ j ∈ Finset.range (h - 1), if j < m then (m : ℝ) else 0) ≤ (m : ℝ) ^ (2 : ℕ) := by
    have heq : (∑ j ∈ Finset.range (h - 1), if j < m then (m : ℝ) else 0) =
        ∑ j ∈ (Finset.range (h - 1)).filter (fun j => j < m), (m : ℝ) := by
      rw [Finset.sum_filter]
    rw [heq]
    have hsub : (Finset.range (h - 1)).filter (fun j => j < m) ⊆ Finset.range m := by
      intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    calc
      _ ≤ ∑ _j ∈ Finset.range m, (m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ j ∈ Finset.range (h - 1), ((if j < m then (m : ℝ) else 0) + B * h * s) :=
      Finset.sum_le_sum hp
    _ = (∑ j ∈ Finset.range (h - 1), if j < m then (m : ℝ) else 0) +
        ((h - 1 : ℕ) : ℝ) * (B * h * s) := by simp [Finset.sum_add_distrib]
    _ ≤ (m : ℝ) ^ (2 : ℕ) + (h : ℝ) * (B * h * s) := by
      apply add_le_add hi
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.sub_le h 1
      · positivity
    _ = _ := by ring

/-- A finite quantitative Abel step, ready for concrete Dirichlet parameters. -/
theorem quotientWindowMean_abel_bound (N K h m : ℕ) [NeZero N] [NeZero K]
    (α β B s : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s) (hmh : m ≤ h)
    (hbound : ∀ t : ℕ, m ≤ t → t ≤ h → quotientWindowMean N K t α ≤ B * t * s)
    (hphase : (2 * Real.pi * |β|) * h ≤ 8)
    (hsmall : (m : ℝ) ^ (2 : ℕ) ≤ (h : ℝ) ^ (2 : ℕ) * s) :
    quotientWindowMean N K h (α + β) ≤ (9 * B + 8) * h * s := by
  have hL : 0 ≤ 2 * Real.pi * |β| := by positivity
  have hp := quotientWindowMean_perturbation N K h α β
  have hsum := quotientWindowMean_prefix_sum N K h m α B s hB hs hbound
  have hsum' := mul_le_mul_of_nonneg_left hsum hL
  have hh := hbound h hmh le_rfl
  have hsm := mul_le_mul_of_nonneg_left hsmall hL
  have hph₁ := mul_le_mul_of_nonneg_right hphase (by positivity : 0 ≤ (h : ℝ) * s)
  have hph₂ := mul_le_mul_of_nonneg_right hphase (by positivity : 0 ≤ B * (h : ℝ) * s)
  nlinarith

#print axioms quotientWindowMean_abel_bound

end ReflectedLiouville
