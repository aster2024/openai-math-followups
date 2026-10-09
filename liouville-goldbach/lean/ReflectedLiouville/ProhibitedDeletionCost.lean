import ReflectedLiouville.UniformRareRow

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Positive prohibited-site cost for the concrete changing prime families,
    allowing an independent shift for every numerical pair. The factor A can
    absorb any prescribed polynomial number of bins. -/
theorem prohibited_deletion_cost (a W δ C : ℝ) (hW : 10 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      ∀ (hL : 1 ≤ L) (η : ℝ),
        let data := reflectionPrimeFamily N W δ L η hL (by linarith)
        let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W (reflectionBandCount W δ L)
        ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (T : Finset ℕ) (padding : ℕ → Finset ℕ) (site : ℕ → ℕ → ℤ) (A : ℝ),
          T ⊆ primeTupleDivisors P →
          (∀ d ∈ T, padding d ⊆ retainedPrimeDivisors data.Q) →
          0 ≤ A → A ≤ Real.exp (C * Real.log L) →
          A * (∑ d ∈ T, ∑ q ∈ padding d,
            (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun x =>
              actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x + site d q) *
                if (q : ℤ) ∣ data.residueOrigin x + site d q ∧
                  ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs)
                    (data.residueOrigin x + site d q)
                then 1 else 0)) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_reflection_pool_range a W δ (by linarith) hδ (by linarith),
    reflection_prohibited_density a W δ (by linarith) hδ hδsmall,
    uniform_rare_row_bound C hC] with L hpool hdensity hrare
  intro N inst hN hL η
  dsimp only
  intro hB T padding site A hT hpadding hA hAcap
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W (reflectionBandCount W δ L)
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  have hrange := hpool N hN hL η
  have hprob : (data.residueLaw ⌊Real.exp L⌋₊ hB).probability (data.deletedEvent s ⌊Real.exp L⌋₊) ≤
      Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
    have hp := hdensity N hN hL η hB 0
    rwa [prohibited_site_probability_translate data hB s 0] at hp
  have hrow := prohibited_atom_sum_le_row data hB P hrange.bandPrimes hrange.bandDisjoint
    hrange.bandSubset T hT padding hpadding s site
  have hscaled := mul_le_mul_of_nonneg_left hrow hA
  have hsmall := hrare N (reflectionBandCount W δ L) ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊
    data hB P W (1 - δ) hrange hW hL 0 (data.deletedEvent s ⌊Real.exp L⌋₊) hprob A hA hAcap
  apply hscaled.trans
  simpa only [add_zero] using hsmall

#print axioms prohibited_deletion_cost

end ReflectedLiouville
