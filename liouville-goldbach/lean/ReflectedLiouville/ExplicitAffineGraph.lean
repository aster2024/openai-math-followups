import ReflectedLiouville.ExplicitActualWordComparison
import ReflectedLiouville.ReflectedCompression

set_option autoImplicit false
set_option maxHeartbeats 1800000
open OAI.TwoPointCorrelations Filter
open scoped BigOperators Classical
namespace ReflectedLiouville

theorem explicit_reflection_affine_word_comparison (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊,
          ∀ (w : ColumnPrimeAssignment J (2 * ⌊L⌋₊) P)
            (forward : Fin (2 * ⌊L⌋₊) → Bool)
            (padding : Fin (2 * ⌊L⌋₊) → boundedPaddingDivisors data.Q M),
            wordDisplacement 1 (columnTupleWord w forward (fun i => (padding i).val)) = 0 →
            ∀ (eligible : ℕ → ℕ → Prop) (a l U : ℕ),
              (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ (144789 : ℕ) / 2) ≤ (U : ℝ) →
              |uniformAverage (fun x : Fin U => scalarWalkProduct 1 (reflectionMaskedWeight data L eligible)
                  ((a + l * x.val : ℕ) : ℤ) (columnTupleWord w forward (fun i => (padding i).val))) -
                (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r => scalarWalkProduct 1
                  (reflectionMaskedWeight data L eligible) (data.residueOrigin r)
                    (columnTupleWord w forward (fun i => (padding i).val)))| ≤ Real.exp (-(L ^ 9)) := by
  have hcomp := explicit_actual_affine_word_comparison
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

theorem explicit_reflection_affine_matrix_moment (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (eligible : ℕ → ℕ → Prop), (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
          ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop) (a l U : ℕ),
            (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ (144789 : ℕ) / 2) ≤ (U : ℝ) →
            uniformAverage (fun x : Fin U => matrixFrobeniusSq
              (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ) ^ ⌊L⌋₊)) ≤
              (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) + 1 := by
  have hword := explicit_reflection_affine_word_comparison W hW
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

theorem explicit_reflection_affine_spectral_tail (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (eligible : ℕ → ℕ → Prop), (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
          ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop) (a l U : ℕ),
            (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ (144789 : ℕ) / 2) ≤ (U : ℝ) →
            uniformAverage (fun x : Fin U => if reflectionSpectralScale J W <
              realMatrixSpectralRadius (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ))
              then (1 : ℝ) else 0) ≤ Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  have hm := explicit_reflection_affine_matrix_moment W hW
  filter_upwards [hm] with L hmoment
  intro J M data P α hrange hL hB eligible hallowed gate a l U hl hU
  have hUpos : 0 < U := by
    have : (0 : ℝ) < U := (Real.exp_pos _).trans_le hU
    exact_mod_cast this
  letI : Nonempty (Fin U) := ⟨⟨0, hUpos⟩⟩
  have hk : 0 < ⌊L⌋₊ := by
    have hk1 : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hL)
    omega
  have hb := hmoment J M data P α hrange hL hB eligible hallowed gate a l U hl hU
  change uniformAverage (fun x : Fin U => matrixFrobeniusSq
    (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ) ^ ⌊L⌋₊)) ≤
      (reflectionTraceBase J W) ^ (2 * ⌊L⌋₊) + 1 at hb
  rw [← FiniteLaw.uniform_average] at hb
  have ht := (FiniteLaw.uniform (Fin U)).matrix_spectral_tail_add_one
    (fun x => reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ))
    ⌊L⌋₊ hk (reflectionTraceBase J W) (reflectionTraceBase_one_le J W hW) hb
  simp only [FiniteLaw.probability, FiniteLaw.uniform_average] at ht
  convert ht using 1
  congr 1

theorem explicit_reflection_affine_compression (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (eligible : ℕ → ℕ → Prop), (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
          ∀ (gate : ℕ → ℤ → ℤ → Prop), (∀ d n m, gate d n m ↔ gate d m n) →
            ∀ a l U : ℕ, (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ (144789 : ℕ) / 2) ≤ (U : ℝ) →
              uniformAverage (fun x : Fin U => if 3 * reflectionSpectralScale J W <
                ‖reflectionCompressedGraph data P L W eligible gate ((a + l * x.val : ℕ) : ℤ)‖
                then (1 : ℝ) else 0) ≤ Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  have ht := explicit_reflection_affine_spectral_tail W hW
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

theorem explicit_reflected_compression_bound (W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) :
    ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
        ∀ hL : 1 ≤ L,
          let J := reflectionBandCount W δ L
          let η := Real.exp (-(J : ℝ))
          let physical := reflectionPrimeFamily N W δ L η hL (by linarith)
          let data := quotientPrimeFamily physical
          let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
          let MB := ⌈Real.exp (103 * L)⌉₊
          ∃ ell : ℕ, MB < ell ∧
            (∀ p : ↥(data.P ∪ data.Q), (N : ZMod p.val) * (ell : ZMod p.val) = 1) ∧
            ∀ j : ℤ, uniformAverage (fun r : Fin N => if
              Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J <
                ‖reflectionCompressedGraph data P L W (binPairEligible data.pairs η j) (fun _ _ _ => True)
                  (((ell - MB / 2 + ell * r.val : ℕ) : ℤ))‖ then (1 : ℝ) else 0) ≤
                    Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  have hc := explicit_reflection_affine_compression W hW
  intro a
  filter_upwards [hc, eventually_reflection_trace_range a W δ hW hδ hδsmall] with L hcompress htrace
  intro N inst hNlog hNlength hL
  dsimp only
  let J := reflectionBandCount W δ L
  let η := Real.exp (-(J : ℝ))
  let physical := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let data := quotientPrimeFamily physical
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  let MB := ⌈Real.exp (103 * L)⌉₊
  have hη : 0 < η := Real.exp_pos _
  have hη₁ : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  have hrange := htrace N hNlog hL η hη hη₁
  obtain ⟨ell, hlarge, hinv⟩ := reflection_CRT_inverse N W δ L η hL (by linarith) MB
  have hl : ∀ p ∈ data.P ∪ data.Q, ell.Coprime p := by
    intro p hp
    exact coprime_of_pool_inverse N ell p (hinv ⟨p, hp⟩)
  refine ⟨ell, hlarge, hinv, ?_⟩
  intro j
  have hb := hcompress J ⌊100 * Real.log L⌋₊ data P (1 - δ) hrange hL hrange.pool.residueBound
    (binPairEligible data.pairs η j) (fun d q h => h.1) (fun _ _ _ => True) (by simp)
    (ell - MB / 2) ell N hl hNlength
  have hscale := compression_scale_le_paper J W hrange.pool.oneJ
  apply le_trans _ hb
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro r hr
  by_cases hp : Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J <
      ‖reflectionCompressedGraph data P L W (binPairEligible data.pairs η j) (fun _ _ _ => True)
        (((ell - MB / 2 + ell * r.val : ℕ) : ℤ))‖
  · have hlow := lt_of_le_of_lt hscale hp
    rw [ite_eq_left hp, ite_eq_left hlow]
  · rw [ite_eq_right hp]
    split_ifs <;> norm_num

#print axioms explicit_reflected_compression_bound
end ReflectedLiouville
