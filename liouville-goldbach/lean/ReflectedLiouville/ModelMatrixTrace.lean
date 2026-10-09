import ReflectedLiouville.ReflectionTraceGeometry
import OAI.NumberTheory.TwoPoint.Bounds.ActualMatrixTrace

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionMaskedWeight {J M : ℕ} (data : ProhibitedPrimeFamily 1 J M)
    (L : ℝ) (eligible : ℕ → ℕ → Prop) : SignedStep → ℤ → ℝ :=
  maskedSignedIntegerWeight (boundedPaddingDivisors data.Q M) actualPaddingCoefficient eligible
    (actualPaddingVertex data.Q) (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
    (fun _ => actualPaddingDegreeCut data.Q L) 1
    (fun z => ¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)

/-- Generic model matrix moment specialized only at fixed h=1 and C=101.
    Every prime family and gate remains after the threshold. -/
theorem reflection_model_matrix_trace (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
      (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
      1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
        (eligible : ℕ → ℕ → Prop),
        (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (embed : V → ((j : Fin J) → P j) × ℤ), Function.Injective embed →
          (Fintype.card V : ℝ) ≤ Real.exp (106 * L) →
          ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
            (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r => matrixFrobeniusSq
              (shiftMatrix embed (integerShiftNext (boundedPaddingDivisors data.Q M)
                (fun d => ∏ j, (d j).val) 1)
                (physicalShiftWeight (boundedPaddingDivisors data.Q M) (fun d => ∏ j, (d j).val) 1 gate
                  (fun t n => reflectionMaskedWeight data L eligible t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
                (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_actual_matrix_trace 1 101 W (by decide) (by norm_num) hW] with L htrace
  intro J M data P α hrange hL hB eligible hallowed V instV instEq embed hinj hdim gate
  let Q := boundedPaddingDivisors data.Q M
  have hq (q : ℕ) (hq : q ∈ Q) : q ∈ retainedPrimeDivisors data.Q := (Finset.mem_filter.mp hq).1
  have hH : Real.exp (L ^ (199 / 200 : ℝ)) ≤ (⌈Real.exp (L ^ α)⌉₊ : ℝ) :=
    (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL hrange.alphaLower)).trans (Nat.le_ceil _)
  have hep := prime_trace_endpoints L hL
  apply htrace J M ⌊Real.exp L⌋₊ ⌈Real.exp (L ^ α)⌉₊ ⌊Real.exp L⌋₊
    ⌊Real.exp (100 * L + 1)⌋₊ ⌊Real.exp (2 * L)⌋₊ data hB P Q hrange.pool.bandSubset
    hrange.pool.oneJ hrange.pool.slots
    (fun j => hW.trans (hrange.pool.bandsLower j)) hrange.pool.bandsUpper hrange.pool.bandsPolynomial
    hrange.pool.centerLower hrange.pool.centerUpper hrange.pool.paddingUpper hrange.pool.paddingDegree
    hrange.pool.bandPrimes hrange.pool.bandDisjoint hrange.pool.centerPrimeLower hrange.pool.centerPrimeUpper
    hep.1 hep.2.1 hH hep.2.2.2.1 hep.2.2.2.2 hrange.paddingMax hrange.tuplePartialMax
    (fun q hqQ => retainedPrimeDivisor_squarefree data.Q data.primeQ (hq q hqQ))
    (fun q hqQ => retainedPrimeDivisor_factors data.Q data.primeQ (hq q hqQ))
    actualPaddingCoefficient (actualPaddingVertex data.Q) (Real.exp (4 * J)) eligible
    (fun _ => actualPaddingDegreeCut data.Q L) actualPaddingCoefficient_nonneg (fun _ => le_rfl)
    (fun n => by rw [actualPaddingVertex_sq]; exact actualPaddingWeight_one_le data.Q n)
    (Real.one_le_exp (by positivity)) (actualPaddingVertex_residue_congr data.Q)
    (fun _ n m hnm => actualPaddingDegreeCut_residue_congr data.Q L n m hnm)
    V embed hinj hdim gate hallowed

#print axioms reflection_model_matrix_trace

end ReflectedLiouville
