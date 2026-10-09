import ReflectedLiouville.PrimeFamilyRebase
import OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reflection_tuple_card_bound (E : Finset ℕ) (W δ L : ℝ)
    (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    let P := centeredPrimeBands E (L ^ (1 - δ)) W (reflectionBandCount W δ L)
    Fintype.card ((j : Fin (reflectionBandCount W δ L)) → P j) ≤ ⌊Real.exp (2 * L)⌋₊ := by
  dsimp only
  let J := reflectionBandCount W δ L
  let A := L ^ (1 - δ)
  let P := centeredPrimeBands E A W J
  have hAp : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  have hend := reflection_prime_endpoint W δ L (by linarith) hδ hL
  apply primeTuple_card_le P (centeredPrimeBands_prime E A W J)
    (centeredPrimeBands_disjoint E A W J hAp.le (by linarith))
  intro d
  exact centeredPrimeTuple_upper E A W L J hAp hW hend (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)

lemma reflection_block_dimension (E : Finset ℕ) (W δ L : ℝ)
    (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    let P := centeredPrimeBands E (L ^ (1 - δ)) W (reflectionBandCount W δ L)
    (Fintype.card (((j : Fin (reflectionBandCount W δ L)) → P j) × Fin ⌈Real.exp (103 * L)⌉₊) : ℝ) ≤
      Real.exp (106 * L) := by
  dsimp only
  let P := centeredPrimeBands E (L ^ (1 - δ)) W (reflectionBandCount W δ L)
  have hd := reflection_tuple_card_bound E W δ L hW hδ hL
  have hd' : (Fintype.card ((j : Fin (reflectionBandCount W δ L)) → P j) : ℝ) ≤ Real.exp (2 * L) :=
    (show (Fintype.card ((j : Fin (reflectionBandCount W δ L)) → P j) : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by
      exact_mod_cast hd).trans (Nat.floor_le (Real.exp_pos _).le)
  have hm : (⌈Real.exp (103 * L)⌉₊ : ℝ) ≤ 2 * Real.exp (103 * L) := by
    have he := Real.one_le_exp (by linarith : 0 ≤ 103 * L)
    have hc := (Nat.ceil_lt_add_one (Real.exp_pos (103 * L)).le).le
    linarith
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  calc
    _ ≤ Real.exp (2 * L) * (2 * Real.exp (103 * L)) :=
      mul_le_mul hd' hm (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = 2 * Real.exp (105 * L) := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp L * Real.exp (105 * L) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp L]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma reflection_alphabet_size (E : Finset ℕ) (W δ L : ℝ)
    (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hL : 4800 ≤ L) :
    let P := centeredPrimeBands E (L ^ (1 - δ)) W (reflectionBandCount W δ L)
    let Q := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
    (Fintype.card (((j : Fin (reflectionBandCount W δ L)) → P j) × (Q × Bool)) : ℝ) ≤ Real.exp (L ^ 4) := by
  dsimp only
  let P := centeredPrimeBands E (L ^ (1 - δ)) W (reflectionBandCount W δ L)
  have hd := reflection_tuple_card_bound E W δ L hW hδ (by linarith)
  have hd' : (Fintype.card ((j : Fin (reflectionBandCount W δ L)) → P j) : ℝ) ≤ Real.exp (2 * L) :=
    (show (Fintype.card ((j : Fin (reflectionBandCount W δ L)) → P j) : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by
      exact_mod_cast hd).trans (Nat.floor_le (Real.exp_pos _).le)
  have hq := boundedPaddingDivisors_card E L (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (2 * L) * (Real.exp (100 * L ^ 2) * Real.exp L) := by gcongr
    _ = Real.exp (100 * L ^ 2 + 3 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hL2 : 103 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 103 by linarith) (sq_nonneg L)]

/-- Every field is numerical support or a size bound, not a trace estimate. -/
structure ReflectionTraceRange {J M : ℕ} (data : ProhibitedPrimeFamily 1 J M)
    (P : Fin J → Finset ℕ) (L W α : ℝ) : Prop where
  pool : ReflectionPoolRange data P L W α
  alphaLower : (199 / 200 : ℝ) ≤ α
  pairsCard : (data.pairs.card : ℝ) ≤ Real.exp (101 * L)
  paddingMax : ∀ dq ∈ data.pairs, dq.2 ≤ ⌊Real.exp (100 * L + 1)⌋₊
  tupleMax : ∀ d : (j : Fin J) → P j, (∏ j, (d j).val) ≤ ⌊Real.exp (2 * L)⌋₊
  tuplePartialMax : ∀ d : (j : Fin J) → P j, ∀ j, (∏ l ∈ Finset.univ.erase j, (d l).val) ≤ ⌊Real.exp (2 * L)⌋₊
  blockDimension : (Fintype.card (((j : Fin J) → P j) × Fin ⌈Real.exp (103 * L)⌉₊) : ℝ) ≤ Real.exp (106 * L)
  alphabetSize : (Fintype.card (((j : Fin J) → P j) × (boundedPaddingDivisors data.Q M × Bool)) : ℝ) ≤ Real.exp (L ^ 4)

theorem eventually_reflection_trace_range (a W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
        let data := quotientPrimeFamily (reflectionPrimeFamily N W δ L η hL (by linarith))
        let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W (reflectionBandCount W δ L)
        ReflectionTraceRange data P L W (1 - δ) := by
  filter_upwards [eventually_reflection_pool_range a W δ hW hδ (by linarith),
    eventually_ge_atTop (4800 : ℝ)] with L hpool hlarge
  intro N inst hN hL η hη hη₁
  dsimp only
  let J := reflectionBandCount W δ L
  let physical := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let data := quotientPrimeFamily physical
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  have hrange := (hpool N hN hL η).quotient physical P L W (1 - δ)
  have hs := reflection_family_support N W δ L η hL hW hδ.le hη hη₁
  have hAp : 0 < L ^ (1 - δ) := Real.rpow_pos_of_pos (by linarith) _
  have hend := reflection_prime_endpoint W δ L (by linarith) hδ.le hL
  refine ⟨hrange, by linarith, hs.2, (fun dq hdq => (hs.1 dq hdq).1), ?_, ?_,
    reflection_block_dimension N.primeFactors W δ L hW hδ.le hL,
    reflection_alphabet_size N.primeFactors W δ L hW hδ.le hlarge⟩
  · intro d
    exact centeredPrimeTuple_upper N.primeFactors (L ^ (1 - δ)) W L J hAp hW hend
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)
  · intro d j
    exact centeredPrimeTuple_complement_upper N.primeFactors (L ^ (1 - δ)) W L J hAp hW hend d j

#print axioms eventually_reflection_trace_range

end ReflectedLiouville
