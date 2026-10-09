import ReflectedLiouville.GenericSpectralTail
import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineCompression

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionCompressedGraph {J M : ℕ} (data : ProhibitedPrimeFamily 1 J M)
    (P : Fin J → Finset ℕ) (L W : ℝ) (eligible : ℕ → ℕ → Prop)
    (gate : ℕ → ℤ → ℤ → Prop) (c : ℤ) :=
  primeBlockCompression P ⌈Real.exp (103 * L)⌉₊ (boundedPaddingDivisors data.Q M)
    actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J)) W
    (fun _ => actualPaddingDegreeCut data.Q L) 1 gate
    (fun z => ¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z) c

lemma reflection_compression_of_radius {J M : ℕ} (data : ProhibitedPrimeFamily 1 J M)
    (P : Fin J → Finset ℕ) (L W α : ℝ) (hrange : ReflectionTraceRange data P L W α)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (eligible : ℕ → ℕ → Prop)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n) (c : ℤ)
    (hradius : realMatrixSpectralRadius (reflectionShiftMatrix data P L eligible
      (fun d n m => gate (∏ j, (d j).val) n m) c) ≤ reflectionSpectralScale J W) :
    ‖reflectionCompressedGraph data P L W eligible gate c‖ ≤ 3 * reflectionSpectralScale J W := by
  have hb := actual_spectral_scale_bounds J (Real.exp (4 * J)) W (Real.exp_pos _).le hW
  change 0 ≤ reflectionSpectralScale J W ∧ 2 * Real.exp (4 * J) ≤ reflectionSpectralScale J W ∧
    4 * (Real.exp (4 * J)) ^ 2 * (8 * W) ^ J ≤ (reflectionSpectralScale J W) ^ 2 at hb
  have hc := prime_physical_compression P hrange.pool.bandPrimes hrange.pool.bandDisjoint
    (fun i : Fin ⌈Real.exp (103 * L)⌉₊ => (i.val : ℤ))
    (fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)) (boundedPaddingDivisors data.Q M)
    actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J)) W
    (fun _ => actualPaddingDegreeCut data.Q L) 1 gate hgate
    (fun z => ¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z) c
    (by linarith) (Real.exp_pos _).le (fun q _ => actualPaddingCoefficient_nonneg q)
    (actualPaddingVertex_pos data.Q) hrange.pool.bandsUpper (reflectionSpectralScale J W) hb.1 hb.2.1 hb.2.2 hradius
  exact hc

/-- Compression outside an exponentially small set of progression origins.
    No canonical fixed-exclusion wrapper theorem is used. -/
theorem reflection_affine_compression (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (eligible : ℕ → ℕ → Prop), (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
          ∀ (gate : ℕ → ℤ → ℤ → Prop), (∀ d n m, gate d n m ↔ gate d m n) →
            ∀ a l U : ℕ, (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (U : ℝ) →
              uniformAverage (fun x : Fin U => if 3 * reflectionSpectralScale J W <
                ‖reflectionCompressedGraph data P L W eligible gate ((a + l * x.val : ℕ) : ℤ)‖
                then (1 : ℝ) else 0) ≤ Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, ht⟩ := reflection_affine_spectral_tail W hW
  refine ⟨A, hA, ?_⟩
  filter_upwards [ht] with L htail
  intro J M data P α hrange hL hB eligible hallowed gate hgate a l U hl hU
  have ht' := htail J M data P α hrange hL hB eligible hallowed
    (fun d n m => gate (∏ j, (d j).val) n m) a l U hl hU
  apply le_trans _ ht'
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro x hx
  by_cases hr : reflectionSpectralScale J W < realMatrixSpectralRadius
      (reflectionShiftMatrix data P L eligible (fun d n m => gate (∏ j, (d j).val) n m)
        ((a + l * x.val : ℕ) : ℤ))
  · rw [ite_eq_left hr]
    split_ifs <;> norm_num
  · have hc := reflection_compression_of_radius data P L W α hrange hL hW eligible gate hgate
      ((a + l * x.val : ℕ) : ℤ) (le_of_not_gt hr)
    rw [ite_eq_right hr, ite_eq_right (not_lt_of_ge hc)]

#print axioms reflection_affine_compression

end ReflectedLiouville
