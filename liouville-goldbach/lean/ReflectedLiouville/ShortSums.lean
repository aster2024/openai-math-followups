import ReflectedLiouville.PublishedInputs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

noncomputable def progressionPrefix (f : ℕ → ℂ) (q : ℕ) (a : ZMod q) (N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => (n : ZMod q) = a), f n

lemma progressionPrefix_difference (f : ℕ → ℂ) (q : ℕ) (a : ZMod q)
    (A B : ℕ) (hAB : A ≤ B) :
    progressionPrefix f q a B - progressionPrefix f q a A =
      ∑ n ∈ (Finset.Icc (A + 1) B).filter (fun n : ℕ => (n : ZMod q) = a), f n := by
  classical
  have hsub : (Finset.Icc 1 A).filter (fun n : ℕ => (n : ZMod q) = a) ⊆
      (Finset.Icc 1 B).filter (fun n : ℕ => (n : ZMod q) = a) := by
    intro n hn
    obtain ⟨hn, ha⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hAB⟩, ha⟩
  have hsets : ((Finset.Icc 1 B).filter (fun n : ℕ => (n : ZMod q) = a)) \
      ((Finset.Icc 1 A).filter (fun n : ℕ => (n : ZMod q) = a)) =
      (Finset.Icc (A + 1) B).filter (fun n : ℕ => (n : ZMod q) = a) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn, ha⟩, hnot⟩
      refine ⟨⟨?_, hn.2⟩, ha⟩
      have hnA : ¬ n ≤ A := fun hnA => hnot ⟨⟨hn.1, hnA⟩, ha⟩
      omega
    · rintro ⟨⟨hn, hnB⟩, ha⟩
      refine ⟨⟨⟨by omega, hnB⟩, ha⟩, ?_⟩
      rintro ⟨hnA, heq⟩
      omega
  unfold progressionPrefix
  rw [← hsets]
  have h := Finset.sum_sdiff (f := f) hsub
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

lemma shortProgressionSum_eq_prefix_difference (f : ℕ → ℂ) (q : ℕ) (a : ZMod q)
    (H : ℝ) (hH : 0 ≤ H) (x : ℝ) :
    shortProgressionSum f q a x H =
      progressionPrefix f q a ⌊x + H⌋₊ - progressionPrefix f q a ⌊x⌋₊ := by
  exact (progressionPrefix_difference f q a _ _ (Nat.floor_mono (by linarith))).symm

/-- Measurability is proved independently of the analytic KMT input. -/
lemma shortProgressionSum_measurable (f : ℕ → ℂ) (q : ℕ) (a : ZMod q)
    (H : ℝ) (hH : 0 ≤ H) : Measurable (fun x : ℝ => shortProgressionSum f q a x H) := by
  have hp : Measurable (progressionPrefix f q a) := measurable_of_countable _
  have hupper := hp.comp ((measurable_id.add_const H).nat_floor)
  have hlower := hp.comp (Nat.measurable_floor (R := ℝ))
  have hsub := hupper.sub hlower
  change Measurable (fun x : ℝ => progressionPrefix f q a ⌊x + H⌋₊ -
    progressionPrefix f q a ⌊x⌋₊) at hsub
  have heq : (fun x : ℝ => shortProgressionSum f q a x H) =
      (fun x : ℝ => progressionPrefix f q a ⌊x + H⌋₊ - progressionPrefix f q a ⌊x⌋₊) := by
    funext x
    exact shortProgressionSum_eq_prefix_difference f q a H hH x
  rw [heq]
  exact hsub

#print axioms shortProgressionSum_measurable

end ReflectedLiouville
