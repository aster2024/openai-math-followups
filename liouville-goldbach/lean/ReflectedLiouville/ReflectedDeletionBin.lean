import ReflectedLiouville.ReflectedDeletionAtom
import ReflectedLiouville.BinFrameGeometry

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset
namespace ReflectedLiouville

lemma positive_real_prefix_le_uniform (T : ℝ) (hT : 0 < T) (hB : 0 < ⌊T⌋₊)
    (F : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ n ∈ Icc 1 ⌊T⌋₊, F (n : ℤ)) / T ≤
      uniformAverage (fun x : Fin ⌊T⌋₊ => F ((x.val+1 : ℕ) : ℤ)) := by
  rw [uniformAverage,Fintype.card_fin]
  have heq := sum_fin_shift_eq_Icc ⌊T⌋₊ (fun n => F (n : ℤ))
  rw [heq]
  have hBr : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hB
  exact div_le_div_of_nonneg_left (sum_nonneg (fun n _ => hF n)) hBr (Nat.floor_le hT.le)

theorem reflected_deletion_bin_bound {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (D : Finset ℕ) (hsub : data.pairs ⊆ D ×ˢ boundedPaddingDivisors data.Q M)
    (L W η : ℝ) (hη : 0 < η) (j : ℤ)
    (hT : 0 < reflectionBinCutoff N η j) (hB : 0 < ⌊reflectionBinCutoff N η j⌋₊) :
    let R := boundedPaddingDivisors data.Q M
    let eligible := fun j => binPairEligible data.pairs η j
    let bad := fun (_ : ℤ) n => ProhibitedSite N ⌊L ^ (1/10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) n
    let cost := fun d q => positiveDeletionAtom data.P data.Q R η (fun d => Real.log (d : ℝ)) L
      (Real.exp (4*J)) W eligible bad j d q
    |centeredBinForm data.pairs N η j - keptCenteredBinForm data L W η j| ≤
      (∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin ⌊reflectionBinCutoff N η j⌋₊ =>
        cost d q ((x.val+1 : ℕ) : ℤ))) +
      (∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin ⌊reflectionBinCutoff N η j⌋₊ =>
        cost d q (((x.val+1 : ℕ) : ℤ) - ((N*d*q : ℕ) : ℤ)))) := by
  dsimp only
  let T := reflectionBinCutoff N η j
  let R := boundedPaddingDivisors data.Q M
  let eligible := fun j => binPairEligible data.pairs η j
  let bad := fun (_ : ℤ) n => ProhibitedSite N ⌊L ^ (1/10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) n
  let cost := fun d q => positiveDeletionAtom data.P data.Q R η (fun d => Real.log (d : ℝ)) L
    (Real.exp (4*J)) W eligible bad j d q
  let Ib := data.pairs.filter (fun dq => reflectionPairBin η dq = j)
  have hIb : Ib ⊆ D ×ˢ R := fun dq hdq => hsub (mem_filter.mp hdq).1
  have hnonneg (d q : ℕ) (n : ℤ) : 0 ≤ cost d q n := positiveDeletionAtom_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hdiff : centeredBinForm data.pairs N η j - keptCenteredBinForm data L W η j =
      (∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊T⌋₊,
        (centeredReflectionAtom N dq (n : ℤ) - keptReflectionAtom data L W (eligible j) dq (n : ℤ))) / T := by
    simp only [centeredBinForm,keptCenteredBinForm,sub_div,sum_sub_distrib]
    rfl
  rw [hdiff,abs_div,abs_of_pos hT]
  have hsum : |∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊T⌋₊,
      (centeredReflectionAtom N dq (n : ℤ) - keptReflectionAtom data L W (eligible j) dq (n : ℤ))| ≤
      ∑ d ∈ D, ∑ q ∈ R, ∑ n ∈ Icc 1 ⌊T⌋₊,
        (cost d q (n : ℤ) + cost d q ((n : ℤ) - ((N*d*q : ℕ) : ℤ))) := by
    calc
      _ ≤ ∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊T⌋₊,
          |centeredReflectionAtom N dq (n : ℤ) - keptReflectionAtom data L W (eligible j) dq (n : ℤ)| := by
        apply (abs_sum_le_sum_abs _ _).trans
        exact sum_le_sum (fun dq _ => abs_sum_le_sum_abs _ _)
      _ ≤ ∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊T⌋₊,
          (cost dq.1 dq.2 (n : ℤ) + cost dq.1 dq.2 ((n : ℤ) - ((N*dq.1*dq.2 : ℕ) : ℤ))) := by
        apply sum_le_sum
        intro dq hdq
        apply sum_le_sum
        intro n hn
        have he : binPairEligible data.pairs η j dq.1 dq.2 := by
          exact ⟨(mem_filter.mp hdq).1,(mem_filter.mp hdq).2⟩
        exact reflected_deletion_atom_bound data L W η hη j dq.1 dq.2 n he
      _ ≤ ∑ dq ∈ D ×ˢ R, ∑ n ∈ Icc 1 ⌊T⌋₊,
          (cost dq.1 dq.2 (n : ℤ) + cost dq.1 dq.2 ((n : ℤ) - ((N*dq.1*dq.2 : ℕ) : ℤ))) :=
        sum_le_sum_of_subset_of_nonneg hIb (fun dq _ _ => sum_nonneg (fun n _ =>
          add_nonneg (hnonneg _ _ _) (hnonneg _ _ _)))
      _ = _ := sum_product _ _ _
  apply (div_le_div_of_nonneg_right hsum hT.le).trans
  simp only [sum_div,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro q hq
  have hb := positive_real_prefix_le_uniform T hT hB
    (fun n => cost d q n + cost d q (n - ((N*d*q : ℕ) : ℤ)))
    (fun n => add_nonneg (hnonneg _ _ _) (hnonneg _ _ _))
  have hadd : uniformAverage (fun x : Fin ⌊T⌋₊ => cost d q ((x.val+1 : ℕ) : ℤ) +
      cost d q (((x.val+1 : ℕ) : ℤ) - ((N*d*q : ℕ) : ℤ))) =
      uniformAverage (fun x : Fin ⌊T⌋₊ => cost d q ((x.val+1 : ℕ) : ℤ)) +
      uniformAverage (fun x : Fin ⌊T⌋₊ => cost d q (((x.val+1 : ℕ) : ℤ) - ((N*d*q : ℕ) : ℤ))) := by
    simp only [uniformAverage,sum_add_distrib,add_div]
  rw [hadd] at hb
  rw [← sum_div]
  simpa only [T,cost,R,eligible,bad] using hb

#print axioms reflected_deletion_bin_bound
end ReflectedLiouville
