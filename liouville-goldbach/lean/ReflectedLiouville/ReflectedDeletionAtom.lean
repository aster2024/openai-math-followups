import ReflectedLiouville.ReflectedSourceInteger
import ReflectedLiouville.EdgeWeightCancellation

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations
namespace ReflectedLiouville

lemma reflected_eligible_actual_bin (I : Finset (ℕ × ℕ)) (d q : ℕ)
    (hd : 0 < d) (hq : 0 < q) (η : ℝ) (hη : 0 < η) (j : ℤ)
    (he : binPairEligible I η j d q) : actualPaddingBin η (Real.log (d : ℝ)) j q := by
  have hb := (paddingBin_eq_iff η 0 (Real.log ((d*q : ℕ) : ℝ)) j hη).mp he.2
  unfold actualPaddingBin
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  simpa only [Nat.cast_mul,Real.log_mul hdR.ne' hqR.ne',add_zero,zero_add,add_comm] using hb

lemma padding_keep_eligible_mono (D : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hu : ∀ q ∈ D, 0 ≤ u q) (he : ∀ q ∈ D, e q → f q) (n : ℤ) :
    integerEdgeKeep D u f g L K extra n → integerEdgeKeep D u e g L K extra n := by
  intro hk
  have hden : paddingDensity D u e g n ≤ paddingDensity D u f g n := by
    unfold paddingDensity
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro q hq
    by_cases ha : e q ∧ (q : ℤ) ∣ n
    · have hf : f q ∧ (q : ℤ) ∣ n := ⟨he q hq ha.1,ha.2⟩
      simp only [ha,hf,ite_true,le_refl]
    · simp only [ha,ite_false]
      split_ifs <;> first | exact hu q hq | exact le_rfl
  exact ⟨hden.trans hk.1,hk.2⟩

lemma positiveDeletionAtom_nonneg (P Q R : Finset ℕ) (η : ℝ) (c : ℕ → ℝ)
    (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) : 0 ≤ positiveDeletionAtom P Q R η c L K W eligible bad j d q n := by
  have hu := actualPaddingCoefficient_nonneg q
  have hw := positivePrimeWeight_nonneg d.primeFactors n
  unfold positiveDeletionAtom
  split_ifs <;> positivity

/-- Literal reflected deletion is bounded by the two original signed-site
    positive costs; eligibility monotonicity only enlarges the padding event. -/
theorem reflected_deletion_atom_bound {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W η : ℝ) (hη : 0 < η) (j : ℤ) (d q : ℕ) (n : ℤ)
    (he : binPairEligible data.pairs η j d q) :
    let R := boundedPaddingDivisors data.Q M
    let eligible := fun j => binPairEligible data.pairs η j
    let bad := fun (_ : ℤ) x => ProhibitedSite N ⌊L ^ (1/10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) x
    |centeredReflectionAtom N (d,q) n - keptReflectionAtom data L W (eligible j) (d,q) n| ≤
      positiveDeletionAtom data.P data.Q R η (fun d => Real.log (d : ℝ)) L (Real.exp (4*J)) W
        eligible bad j d q n +
      positiveDeletionAtom data.P data.Q R η (fun d => Real.log (d : ℝ)) L (Real.exp (4*J)) W
        eligible bad j d q (n - ((N*d*q : ℕ) : ℤ)) := by
  dsimp only
  let R := boundedPaddingDivisors data.Q M
  let eligible := fun j => binPairEligible data.pairs η j
  let bad := fun (_ : ℤ) x => ProhibitedSite N ⌊L ^ (1/10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) x
  let cost := positiveDeletionAtom data.P data.Q R η (fun d => Real.log (d : ℝ)) L (Real.exp (4*J)) W eligible bad j d q
  let y := n - ((N*d*q : ℕ) : ℤ)
  change |centeredReflectionAtom N (d,q) n - keptReflectionAtom data L W (eligible j) (d,q) n| ≤ cost n + cost y
  have hd : 0 < d := Nat.pos_of_ne_zero (data.tuple_squarefree _ he.1).ne_zero
  have hq : 0 < q := Nat.pos_of_ne_zero (data.padding_squarefree _ he.1).ne_zero
  have hcard := data.tuple_card _ he.1
  have hmono (x : ℤ) := padding_keep_eligible_mono R actualPaddingCoefficient (eligible j d)
    (actualPaddingBin η (Real.log (d : ℝ)) j) (actualPaddingVertex data.Q) L (Real.exp (4*J))
    (actualPaddingDegreeCut data.Q L) (fun q _ => actualPaddingCoefficient_nonneg q)
    (fun q hq heq => reflected_eligible_actual_bin data.pairs d q hd
      (bounded_padding_positive data q hq) η hη j heq) x
  have hcost (x : ℤ) (hdv : (q : ℤ) ∣ x) (hb : ¬reflectionVertexKeep data L W (eligible j) d x) :
      cost x = actualPaddingCoefficient q * positivePrimeWeight d.primeFactors x := by
    have hfail : ¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (Real.log (d : ℝ)) j)
        (actualPaddingVertex data.Q) L (Real.exp (4*J)) (actualPaddingDegreeCut data.Q L) x ∨
        6*W*d.primeFactors.card < (actualPaddingDegree data.P x : ℝ) ∨ bad j x := by
      by_contra hn
      push_neg at hn
      apply hb
      exact ⟨hmono x hn.1,by simpa only [hcard] using hn.2.1,hn.2.2⟩
    simp only [cost,positiveDeletionAtom,eligible,he,ite_true,hfail,hdv,true_and,and_true,mul_one]
  have hnonneg (x : ℤ) : 0 ≤ cost x := positiveDeletionAtom_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hweight : positivePrimeWeight d.primeFactors y = positivePrimeWeight d.primeFactors n := by
    have hs : ((N*d*q : ℕ) : ℤ) = ((N*q*d : ℕ) : ℤ) := by push_cast; ring
    dsimp only [y]
    rw [hs]
    exact positive_weight_at_reflected_endpoint N q d n
  have hb := centeredReflectionAtom_positive_bound N (d,q) n
  have hKept : keptReflectionAtom data L W (eligible j) (d,q) n =
      if reflectionVertexKeep data L W (eligible j) d n ∧ reflectionVertexKeep data L W (eligible j) d y then
        centeredReflectionAtom N (d,q) n else 0 := rfl
  rw [hKept]
  by_cases hdv : (q : ℤ) ∣ n
  · have hstep : (q : ℤ) ∣ ((N*d*q : ℕ) : ℤ) := by exact_mod_cast dvd_mul_left q (N*d)
    have hydv : (q : ℤ) ∣ y := (dvd_sub_left hstep).mpr hdv
    by_cases hs : reflectionVertexKeep data L W (eligible j) d n <;>
      by_cases ht : reflectionVertexKeep data L W (eligible j) d y
    · simp only [hs,ht,and_self,ite_true,sub_self,abs_zero]
      exact add_nonneg (hnonneg n) (hnonneg y)
    · have hc := hcost y hydv ht
      rw [hweight] at hc
      simp only [hs,ht,and_false,ite_false,sub_zero]
      change |centeredReflectionAtom N (d,q) n| ≤ cost n + cost y
      linarith only [hb,hc,hnonneg n]
    · have hc := hcost n hdv hs
      simp only [hs,false_and,ite_false,sub_zero]
      change |centeredReflectionAtom N (d,q) n| ≤ cost n + cost y
      linarith only [hb,hc,hnonneg y]
    · have hc := hcost n hdv hs
      simp only [hs,false_and,ite_false,sub_zero]
      change |centeredReflectionAtom N (d,q) n| ≤ cost n + cost y
      linarith only [hb,hc,hnonneg y]
  · have hz : centeredReflectionAtom N (d,q) n = 0 := by simp only [centeredReflectionAtom,hdv,ite_false]
    simp only [hz,ite_self,sub_self,abs_zero]
    exact add_nonneg (hnonneg n) (hnonneg y)

#print axioms reflected_deletion_atom_bound
end ReflectedLiouville
