import ReflectedLiouville.ReflectedSliceSaving
import ReflectedLiouville.ReflectedCenteringSum
import OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialBounds

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma rescaled_real_norm_bound (z : ℂ) (T m E : ℝ) (hT : 0 < T) (hm : 0 < m)
    (hb : ‖z‖ / (T / m) ≤ E) : ‖z‖ / T ≤ E * (1 / m) := by
  have hy : 0 < T / m := div_pos hT hm
  have he := (div_le_iff₀ hy).mp hb
  calc
    _ ≤ (E * (T / m)) / T := div_le_div_of_nonneg_right he hT.le
    _ = _ := by field_simp

/-- Real-cutoff reciprocal mass normalization for all complementary tuples. -/
lemma reflected_partial_prefix_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j))
    (I : Finset (Fin J)) (q N : ℕ) (hq : 0 < q)
    (eligible : ℕ → ℕ → Prop) (T E : ℝ) (hT : 0 < T)
    (hb : ∀ y : (j : {j // j ∉ I}) → P j,
      let Z := (primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)
      let Y := T / ((q * ∏ j, (y j).val : ℕ) : ℝ)
      ‖∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
        liouville m * liouville (N * z - m)‖ / Y ≤ E) :
    ‖positivePrefix (reflectedTuplePartialProfile P I q N eligible) ⌊T⌋₊ / (T : ℂ)‖ ≤
      E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
  rw [reflected_tuple_partial_prefix_reindex P hprime hdisjoint I q N hq T eligible,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  have hsum :
      (∑ y : (j : {j // j ∉ I}) → P j, E * (1 / ((q * ∏ j, (y j).val : ℕ) : ℝ))) =
        E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
    rw [← Finset.mul_sum]
    congr 1
    simpa only [Nat.cast_mul, Nat.cast_prod] using retained_tuple_reciprocal_sum P I q
  calc
    _ ≤ (∑ y : (j : {j // j ∉ I}) → P j,
        ‖∑ z ∈ (primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q),
          (z : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 ⌊T / ((q * ∏ j, (y j).val : ℕ) : ℝ)⌋₊,
            liouville m * liouville (N * z - m)‖) / T :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hT.le
    _ = ∑ y : (j : {j // j ∉ I}) → P j,
        ‖∑ z ∈ (primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q),
          (z : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 ⌊T / ((q * ∏ j, (y j).val : ℕ) : ℝ)⌋₊,
            liouville m * liouville (N * z - m)‖ / T := Finset.sum_div _ _ _
    _ ≤ ∑ y : (j : {j // j ∉ I}) → P j, E * (1 / ((q * ∏ j, (y j).val : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      apply rescaled_real_norm_bound _ T _ E hT _ (hb y)
      exact_mod_cast Nat.mul_pos hq (Finset.prod_pos (fun j : {j // j ∉ I} => by intro hj; exact (hprime j _ (y j).property).pos))
    _ = _ := hsum

theorem reflected_partial_profile_saving (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (A : ℕ) (hA : 1000 ≤ A) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ, N₀ ≤ N → Real.log (N : ℝ) = L ^ A →
        ∀ (J : ℕ) (P : Fin J → Finset ℕ),
          (∀ j, ∀ p ∈ P j, p.Prime) →
          (∀ j k, k ≠ j → Disjoint (P j) (P k)) →
          (∀ j, (P j).Nonempty) →
          (∀ j, ∀ p ∈ P j, Real.exp (L ^ convolutionSizeExponent) ≤ (p : ℝ)) →
          (∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ Real.exp (2 * L)) →
          ∀ (I : Finset (Fin J)), I.Nonempty → ∀ (q : ℕ), 0 < q →
          ∀ (S : Finset (ℕ × ℕ)) (η : ℝ), 0 < η → η ≤ 1 / 2 → ∀ j : ℤ,
            ‖positivePrefix (reflectedTuplePartialProfile P I q N (binPairEligible S η j))
              ⌊reflectionBinCutoff N η j⌋₊ / (reflectionBinCutoff N η j : ℂ)‖ ≤
                C * L ^ (-1 - convolutionFinalExponent) *
                  ((1 / (q : ℝ)) * ∏ k : {k // k ∉ I}, primeHarmonicMass (P k)) := by
  obtain ⟨C,L₀,hC,hL₀,N₀,hN₀,hb⟩ := reflected_slice_saving h_KMT h_MRT A hA
  refine ⟨C,L₀,hC,hL₀,N₀,hN₀,?_⟩
  intro L hL N hN hlog J P hprime hdisjoint hne hlarge hfull I hI q hq S η hη hηsmall j
  have hn : 0 < N := by omega
  have hT : 0 < reflectionBinCutoff N η j := by unfold reflectionBinCutoff; positivity
  exact reflected_partial_prefix_bound P hprime hdisjoint I q N hq _ _ _ hT
    (hb L hL N hN hlog J P hprime hdisjoint hne hlarge hfull I hI q hq S η hη hηsmall j)

#print axioms reflected_partial_profile_saving
end ReflectedLiouville
