import ReflectedLiouville.ReflectedPartialSaving

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- The complete analytic centering estimate at one bin, with exact
    harmonic masses for its outer padding and center supplies. -/
theorem reflected_centering_bin_saving (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (A : ℕ) (hA : 1000 ≤ A) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ, N₀ ≤ N → Real.log (N : ℝ) = L ^ A →
        ∀ (J : ℕ) (P : Fin J → Finset ℕ),
          (∀ j, ∀ p ∈ P j, p.Prime) →
          (∀ j k, k ≠ j → Disjoint (P j) (P k)) →
          (∀ j, 1 ≤ primeHarmonicMass (P j)) →
          (∀ j, ∀ p ∈ P j, Real.exp (L ^ convolutionSizeExponent) ≤ (p : ℝ)) →
          (∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ Real.exp (2 * L)) →
          ∀ (Q : Finset ℕ) (weight : ℕ → ℝ),
          (∀ q ∈ Q, 0 < q) → (∀ q ∈ Q, 0 ≤ weight q) →
          (∀ q ∈ Q, ∀ j, ∀ p ∈ P j, q.Coprime p) →
          ∀ (S : Finset (ℕ × ℕ)) (η : ℝ), 0 < η → η ≤ 1 / 2 → ∀ j : ℤ,
            let T := reflectionBinCutoff N η j
            ‖∑ q ∈ Q, (weight q : ℂ) *
              ((positivePrefix (reflectedTupleCenteredProfile P q N (binPairEligible S η j)) ⌊T⌋₊ -
                positivePrefix (reflectedTuplePartialProfile P ∅ q N (binPairEligible S η j)) ⌊T⌋₊) / (T : ℂ))‖ ≤
              C * L ^ (-1 - convolutionFinalExponent) * (2 : ℝ) ^ J *
                (∑ q ∈ Q, weight q / (q : ℝ)) * ∏ k, primeHarmonicMass (P k) := by
  obtain ⟨C,L₀,hC,hL₀,N₀,hN₀,hb⟩ := reflected_partial_profile_saving h_KMT h_MRT A hA
  refine ⟨C,L₀,hC,hL₀,N₀,hN₀,?_⟩
  intro L hL N hN hlog J P hprime hdisjoint hmass hlarge hfull Q weight hq hw hcop S η hη hηsmall j
  dsimp only
  have hne (k : Fin J) : (P k).Nonempty := by
    by_contra hn
    have he : P k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := hmass k
    rw [he] at hh
    norm_num [primeHarmonicMass] at hh
  have hLpos : 0 < L := by linarith
  apply reflected_partial_centering_sum_bound P hprime hdisjoint hmass Q weight hw hcop
    (binPairEligible S η j) N (reflectionBinCutoff N η j)
    (C * L ^ (-1 - convolutionFinalExponent)) (by positivity)
  intro q hqmem I hI
  exact hb L hL N hN hlog J P hprime hdisjoint hne hlarge hfull I
    (Finset.mem_filter.mp hI).2 q (hq q hqmem) S η hη hηsmall j

#print axioms reflected_centering_bin_saving
end ReflectedLiouville
