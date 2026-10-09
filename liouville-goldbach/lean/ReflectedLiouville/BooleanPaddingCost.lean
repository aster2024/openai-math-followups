import ReflectedLiouville.ActivePaddingCost

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- The literal integer deletion cost pushes forward to independent
    Bernoulli(1/p) activations, with the same restricted divisor and bin sets. -/
theorem residue_padding_cost_eq_original {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors data.Q) (bins : Finset ℤ)
    (η c L K : ℝ) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) =
      (paddingOriginalLaw data.Q (fun p hp => (data.primeQ p hp).two_le)).average
        (fun b => activePaddingRejected D bins η c L K (paddingAvailablePrimes data.Q b)) := by
  rw [data.residue_average_padding_shift hB site
    (paddingRejectedMass data.Q D bins η c L K)
    (paddingRejectedMass_residue_congr data.Q data.primeQ D hD bins η c L K)]
  let F := fun b : data.Q → Bool => activePaddingRejected D bins η c L K (paddingAvailablePrimes data.Q b)
  have hpoint (z : data.Q → Fin B) : paddingRejectedMass data.Q D bins η c L K
      (data.paddingResidueOrigin z + site) = F (paddingResidueAvailable data.Q B site z) := by
    rw [paddingRejectedMass_eq_active data.Q D data.primeQ hD]
    have hlift := actualPaddingAvailability_lift data.Q B site z
      (data.paddingResidueOrigin z + site) (by
        intro p
        rw [Int.cast_add, data.paddingResidueOrigin_spec])
    rw [hlift]
  have hfun : (fun z : data.Q → Fin B => paddingRejectedMass data.Q D bins η c L K
      (data.paddingResidueOrigin z + site)) = (fun z => F (paddingResidueAvailable data.Q B site z)) :=
    funext hpoint
  rw [hfun]
  exact padding_residue_average data.Q B (fun p hp => (data.primeQ p hp).two_le)
    (fun p hp => hB p (Finset.mem_union_right _ hp)) site F

/-- An auxiliary empty-center family lets the library full-pool theorem be
    used without introducing any new analytic input. -/
noncomputable def paddingOnlyFamily (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ProhibitedPrimeFamily 1 0 0 where
  P := ∅
  Q := Q
  pairs := ∅
  primeP := by simp
  primeQ := hQ
  disjoint := by simp
  excluded := by simp
  tuple_squarefree := by simp
  padding_squarefree := by simp
  tuple_card := by simp
  padding_card := by simp
  tuple_pool := by simp
  padding_pool := by simp

/-- The full-pool bound as an exact independent-activation inequality.
    No exclusions are fixed here other than the empty set in the proved input. -/
theorem eventually_full_boolean_padding_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let Q := paddingPrimeSupply ∅ L
      ∀ (D : Finset ℕ) (bins : Finset ℤ) (η c K : ℝ),
        D ⊆ retainedPrimeDivisors Q → 0 < η → η ≤ 1 → 0 < K →
        (paddingOriginalLaw Q (fun p hp => (paddingPrimeSupply_prime hp).two_le)).average
          (fun b => activePaddingRejected D bins η c L K (paddingAvailablePrimes Q b)) /
            paddingTiltNormalizer Q ≤ C / K + L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := modFiveThetaInput.eventually_positive_padding_cut_cost ∅
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hcost
  dsimp only
  intro D bins η c K hD hη hη₁ hK
  let Q := paddingPrimeSupply ∅ L
  let data := paddingOnlyFamily Q (fun p hp => paddingPrimeSupply_prime hp)
  let B := Q.sup id + 1
  have hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B := by
    intro p hp
    have hpQ : p ∈ Q := by simpa only [data, paddingOnlyFamily, Finset.empty_union] using hp
    exact (Finset.le_sup (f := id) hpQ).trans (Nat.le_succ _)
  have hc := hcost η c K 1 0 0 B data rfl hB 0 bins hη hη₁ hK D hD ∅ (by simp [data, paddingOnlyFamily])
  have hpoint : (fun x : ↥(data.P ∪ data.Q) → Fin B => positivePrimeWeight ∅ (data.residueOrigin x + 0) *
      paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + 0)) =
      (fun x => paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + 0)) := by
    funext x
    simp [positivePrimeWeight]
  rw [hpoint] at hc
  simp only [positivePrimeNormalizer, Finset.prod_empty, one_mul] at hc
  rw [residue_padding_cost_eq_original data hB D hD bins η c L K 0] at hc
  exact hc

#print axioms eventually_full_boolean_padding_cost

end ReflectedLiouville
