import ReflectedLiouville.GenericAffineWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineIntervalMatrix

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionShiftMatrix {J M : ℕ} (data : ProhibitedPrimeFamily 1 J M)
    (P : Fin J → Finset ℕ) (L : ℝ) (eligible : ℕ → ℕ → Prop)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop) (c : ℤ) :=
  shiftMatrix (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
    (integerShiftNext (boundedPaddingDivisors data.Q M) (fun d => ∏ j, (d j).val) 1)
    (physicalShiftWeight (boundedPaddingDivisors data.Q M) (fun d => ∏ j, (d j).val) 1 gate
      (fun t n => reflectionMaskedWeight data L eligible t (n + c)))

/-- Average matrix moment over an arbitrary CRT-compatible progression, with
    all varying supplies and progressions following a uniform threshold. -/
theorem reflection_affine_matrix_moment (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (eligible : ℕ → ℕ → Prop), (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
          ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop) (a l U : ℕ),
            (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (U : ℝ) →
            uniformAverage (fun x : Fin U => matrixFrobeniusSq
              (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ) ^ ⌊L⌋₊)) ≤
              (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) + 1 := by
  obtain ⟨A, hA, hword⟩ := reflection_affine_word_comparison W hW
  refine ⟨A, hA, ?_⟩
  filter_upwards [hword, reflection_model_matrix_trace W hW, eventually_ge_atTop (4800 : ℝ)]
    with L hwordL htrace hlarge
  intro J M data P α hrange hL hB eligible hallowed gate a l U hl hU
  let Q := boundedPaddingDivisors data.Q M
  let weight := reflectionMaskedWeight data L eligible
  let D := (j : Fin J) → P j
  let MB := ⌈Real.exp (103 * L)⌉₊
  let V := D × Fin MB
  let embed : V → D × ℤ := primeBlockEmbedding MB
  let tuple : D → ℕ := fun d => ∏ j, (d j).val
  have hsq (q : ℕ) (hq : q ∈ Q) : Squarefree q :=
    retainedPrimeDivisor_squarefree data.Q data.primeQ (Finset.mem_filter.mp hq).1
  have hpool (q : ℕ) (hq : q ∈ Q) : q.primeFactors ⊆ data.Q :=
    retainedPrimeDivisor_factors data.Q data.primeQ (Finset.mem_filter.mp hq).1
  have hUpos : 0 < U := by
    have : (0 : ℝ) < U := (Real.exp_pos _).trans_le hU
    exact_mod_cast this
  letI : Nonempty (Fin U) := ⟨⟨0, hUpos⟩⟩
  have hcompare := physicalMatrix_moment_comparison embed (primeBlockEmbedding_injective MB) Q tuple 1 gate weight
    (maskedSignedIntegerWeight_flip Q actualPaddingCoefficient eligible _ _ _ _ _ 1 _)
    (FiniteLaw.uniform (Fin U)) (data.residueLaw ⌊Real.exp L⌋₊ hB)
    (fun x => ((a + l * x.val : ℕ) : ℤ)) data.residueOrigin ⌊L⌋₊ (Real.exp (-(L ^ 9))) (Real.exp_pos _).le ?_
  · rw [FiniteLaw.uniform_average] at hcompare
    have herr := trace_interval_error_le_one L ⌊L⌋₊ (Fintype.card V)
      (Fintype.card (D × (Q × Bool))) hlarge (Nat.floor_le (by linarith))
      (Nat.cast_nonneg _) hrange.blockDimension hrange.alphabetSize
    have hupper := htrace J M data P α hrange hL hB eligible hallowed V embed
      (primeBlockEmbedding_injective MB) hrange.blockDimension gate
    have hdiff := (le_abs_self _).trans (hcompare.trans herr)
    change uniformAverage (fun x : Fin U => matrixFrobeniusSq
        (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ) ^ ⌊L⌋₊)) -
      (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r => matrixFrobeniusSq
        (reflectionShiftMatrix data P L eligible gate (data.residueOrigin r) ^ ⌊L⌋₊)) ≤ 1 at hdiff
    change (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r => matrixFrobeniusSq
        (reflectionShiftMatrix data P L eligible gate (data.residueOrigin r) ^ ⌊L⌋₊)) ≤ _ at hupper
    linarith only [hdiff, hupper]
  · intro i b c hend
    let enc := closedTraceEncoding Q (b, c)
    have hclosed : wordDisplacement 1 (columnTupleWord enc.2.1 enc.1 (fun j => (enc.2.2 j).val)) = 0 := by
      rw [closedTraceEncoding_word]
      exact integer_closed_word_displacement Q tuple 1 (embed i) b c hend
    have hw := hwordL J M data P α hrange hL hB enc.2.1 enc.1 enc.2.2 hclosed eligible
      (a + i.2.val) l U hl hU
    rw [closedTraceEncoding_word] at hw
    have ht := data.residue_average_translate hB
      (fun n => scalarWalkProduct 1 weight n (integerClosedWordCode Q tuple (b, c)))
      (fun n m hnm => scalarWalkProduct_residue_congr (data.P ∪ data.Q) 1 weight _
        (fun t ht z z' hz => primeClosedPair_residue_congr data hB hrange.pool.bandSubset
          hrange.pool.bandPrimes hrange.pool.bandDisjoint ⌊L ^ (1 / 10 : ℝ)⌋₊ Q actualPaddingCoefficient
          eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J))
          (fun _ => actualPaddingDegreeCut data.Q L) hsq hpool
          (actualPaddingVertex_residue_congr data.Q)
          (fun _ n m hnm => actualPaddingDegreeCut_residue_congr data.Q L n m hnm)
          b c t ht z z' (fun p => hz p.val p.property)) n m (fun p hp => hnm ⟨p, hp⟩))
      (embed i).2
    have havg : (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r =>
        scalarWalkProduct 1 weight ((embed i).2 + data.residueOrigin r) (integerClosedWordCode Q tuple (b, c))) =
        (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r =>
          scalarWalkProduct 1 weight (data.residueOrigin r) (integerClosedWordCode Q tuple (b, c))) := by
      simpa only [add_comm (embed i).2] using ht
    rw [FiniteLaw.uniform_average, havg]
    simpa only [embed, primeBlockEmbedding, Nat.cast_add, Nat.cast_mul,
      add_assoc, add_left_comm (a : ℤ)] using hw

#print axioms reflection_affine_matrix_moment

end ReflectedLiouville
