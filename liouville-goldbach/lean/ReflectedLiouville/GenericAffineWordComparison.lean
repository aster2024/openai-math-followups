import ReflectedLiouville.ModelMatrixTrace
import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineWordComparison

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- The comparison threshold is independent of all changing prime families,
    CRT progression steps and initial origins. -/
theorem reflection_affine_word_comparison (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊,
          ∀ (w : ColumnPrimeAssignment J (2 * ⌊L⌋₊) P)
            (forward : Fin (2 * ⌊L⌋₊) → Bool)
            (padding : Fin (2 * ⌊L⌋₊) → boundedPaddingDivisors data.Q M),
            wordDisplacement 1 (columnTupleWord w forward (fun i => (padding i).val)) = 0 →
            ∀ (eligible : ℕ → ℕ → Prop) (a l U : ℕ),
              (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (U : ℝ) →
              |uniformAverage (fun x : Fin U => scalarWalkProduct 1 (reflectionMaskedWeight data L eligible)
                  ((a + l * x.val : ℕ) : ℤ) (columnTupleWord w forward (fun i => (padding i).val))) -
                (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r => scalarWalkProduct 1
                  (reflectionMaskedWeight data L eligible) (data.residueOrigin r)
                    (columnTupleWord w forward (fun i => (padding i).val)))| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hcomp⟩ := bravermanDepth22Input.eventually_actual_affine_word_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcomp, eventually_trace_slot_budgets 101 (by norm_num),
    eventually_ge_atTop (4800 : ℝ)] with L hcompare hslots hlarge
  intro J M data P α hrange hL hB w forward padding hclosed eligible a l U hl hU
  let k := ⌊L⌋₊
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  let Q := boundedPaddingDivisors data.Q M
  have hkhi : (k : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hkpos : 0 < k := by
    have hk1 : 1 ≤ k := Nat.le_floor (by simpa only [Nat.cast_one] using hL)
    omega
  have hR : 0 < 2 * k := by omega
  have hRplus : (((2 * k + 1 : ℕ) : ℝ)) ≤ 4 * L := by push_cast; nlinarith only [hkhi, hL]
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith : 0 < L)).trans (by linarith)
  have hJM : ((J + M : ℕ) : ℝ) ≤ L ^ (2 : ℕ) :=
    hrange.pool.slots.trans (by nlinarith only [hlarge, hlogL])
  have hs : (s : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 10 : ℝ) ≤ 1)
  have hslot := hslots k J M hkhi hrange.pool.slots
  have hRJ : (((2 * k * J : ℕ) : ℝ)) ≤ L ^ (2 : ℕ) := by
    have hnat : 2 * k * J ≤ 2 * k * (J + M) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hcast : ((2 * k * J : ℕ) : ℝ) ≤ ((2 * k * (J + M) : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith only [hcast, hslot.2.1]
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono Finset.subset_union_left))
    have hm := hrange.pool.centerLower
    rw [hempty] at hm
    norm_num [primeHarmonicMass] at hm
  have hQ : Q ⊆ retainedPrimeDivisors data.Q := Finset.filter_subset _ _
  have hdeg (i : Fin (2 * k)) : ((padding i).val.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    (show ((padding i).val.primeFactors.card : ℝ) ≤ (M : ℝ) by
      exact_mod_cast (Finset.mem_filter.mp (padding i).property).2).trans hrange.pool.paddingDegree
  let label : Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q) := fun ij =>
    ⟨(w ij.2 ij.1).val, Finset.mem_union_left _ (hrange.pool.bandSubset ij.2 (w ij.2 ij.1).property)⟩
  have hc := hcompare 1 J M (2 * k) s ⌊Real.exp L⌋₊ data hB hpool
    (Nat.floor_le (Real.exp_pos _).le) hs hJM hrange.pairsCard hR hRplus hRJ Q hQ
    P w forward (fun i => (padding i).val) hrange.pool.bandPrimes hrange.pool.bandDisjoint hdeg
    label (fun _ _ => rfl) hclosed eligible (Real.exp (4 * J)) a l U hl hU
  simpa only [reflectionMaskedWeight, Int.natCast_add, Int.natCast_mul] using hc

#print axioms reflection_affine_word_comparison

end ReflectedLiouville
