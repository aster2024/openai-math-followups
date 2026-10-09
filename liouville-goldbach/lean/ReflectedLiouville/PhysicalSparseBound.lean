import ReflectedLiouville.TestVectorInterfaces
import ReflectedLiouville.SourceSupportCard

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- The deterministic reflected test bound counts source points at spacing N,
    with no factor from the ambient graph block or the CRT progression step. -/
theorem physical_reflected_sparse_bound {N J M : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily N J M) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site) (hN : 0 < N)
    (r : ℤ) (hr : 1 ≤ r ∧ r ≤ (N : ℤ)) (L W T U : ℝ)
    (hL : 0 < L) (hW : 0 ≤ W) (hT : 0 ≤ T)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W) (eligible : ℕ → ℕ → Prop) :
    ‖inner ℂ (sourceTestVector data.Q T L (fun i => (N : ℤ) * site i + r))
      (physicalReflectionCompression data P site r L W eligible
        (targetTestVector data.Q U L (fun i => (N : ℤ) * site i + r)))‖ ≤
          (T / N + 1) * (2 * Real.exp (4 * J) * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L) := by
  let physical := fun i : V => (N : ℤ) * site i + r
  let S := (Finset.univ : Finset V).filter (fun i => 0 < physical i ∧ (physical i : ℝ) ≤ T)
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hphys : Function.Injective physical := by
    intro i j he
    apply hinj
    exact mul_left_cancel₀ hN0 (add_right_cancel he)
  have hzero : ∀ i, i ∉ S → unweightedSourceTest T (physical i) = 0 := by
    intro i hi
    have hnot : ¬(0 < physical i ∧ (physical i : ℝ) ≤ T) := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    simp only [unweightedSourceTest, ite_eq_right hnot]
  have hb := projected_padding_sparse_bilinear P hprime hdisjoint physical hphys
    (boundedPaddingDivisors data.Q M) data.Q actualPaddingCoefficient eligible L (Real.exp (4 * J)) W
    (fun _ => actualPaddingDegreeCut data.Q L) N
    (fun _ i j =>
      (¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (physical i)) ∧
      (¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (physical j)))
    hL (Real.exp_pos _).le hW (fun q _ => actualPaddingCoefficient_nonneg q) hV
    (unweightedSourceTest T) (unweightedTargetTest U) (unweightedSourceTest_one_bounded T)
    (unweightedTargetTest_one_bounded U) S hzero
  rw [← sourceTestVector_eq_padding, ← targetTestVector_eq_padding] at hb
  change ‖inner ℂ (sourceTestVector data.Q T L physical)
    (physicalReflectionCompression data P site r L W eligible (targetTestVector data.Q U L physical))‖ ≤ _ at hb
  have hcard := source_support_card_le N hN site hinj r hr T hT
  change (S.card : ℝ) ≤ T / N + 1 at hcard
  have hscale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 2 * Real.exp (4 * J) * (8 * W) ^ J))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (400 * Real.log L))
  exact hb.trans hscale

#print axioms physical_reflected_sparse_bound

end ReflectedLiouville
