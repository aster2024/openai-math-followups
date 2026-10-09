import ReflectedLiouville.PublishedInputs
import Mathlib.Topology.Order.Compact
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic

set_option autoImplicit false
open OAI.TwoPointCorrelations
open scoped ComplexConjugate

namespace ReflectedLiouville

lemma squaredDistanceMod_twist_continuous {q : ℕ} (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (X : ℝ) :
    Continuous (fun t : ℝ => squaredDistanceMod q f (characterTwist χ t) X) := by
  unfold squaredDistanceMod characterTwist
  fun_prop

/-- The minimizing pair required by the published KMT theorem actually exists.
    Its existence is a compactness/finite-choice proof, not another hypothesis. -/
theorem exists_minimizing_character (q : ℕ) [NeZero q] (f : ℕ → ℂ) (X : ℝ)
    (hX : 0 ≤ X) : ∃ (χ : DirichletCharacter ℂ q) (t : ℝ), MinimizingCharacter f X χ t := by
  classical
  have hnonempty : (Set.Icc (-X) X).Nonempty := ⟨0, by constructor <;> linarith⟩
  have hmin : ∀ χ : DirichletCharacter ℂ q, ∃ t ∈ Set.Icc (-X) X,
      ∀ u ∈ Set.Icc (-X) X,
        squaredDistanceMod q f (characterTwist χ t) X ≤
          squaredDistanceMod q f (characterTwist χ u) X := by
    intro χ
    exact isCompact_Icc.exists_isMinOn hnonempty
      (squaredDistanceMod_twist_continuous f χ X).continuousOn
  choose t ht hminimal using hmin
  obtain ⟨χ, hχ, hbest⟩ := Finset.exists_min_image (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ => squaredDistanceMod q f (characterTwist χ (t χ)) X) Finset.univ_nonempty
  refine ⟨χ, t χ, abs_le.mpr (ht χ), ?_⟩
  intro ψ u hu
  exact (hbest ψ (Finset.mem_univ _)).trans (hminimal ψ u (abs_le.mp hu))

#print axioms exists_minimizing_character

end ReflectedLiouville
