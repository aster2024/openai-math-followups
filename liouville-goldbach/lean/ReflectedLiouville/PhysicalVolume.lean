import ReflectedLiouville.CrossSupportPairing
import ReflectedLiouville.PhysicalCompressionBlock

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma physical_residue_sites_injective {V : Type*} (N : ℕ) (hN : 0 < N)
    (site : V → ℤ) (hinj : Function.Injective site) :
    Function.Injective (fun ri : Fin N × V => (N : ℤ) * site ri.2 + ((ri.1.val + 1 : ℕ) : ℤ)) := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  intro a b he
  have hc := congrArg (fun z : ℤ => (z : ZMod N)) he
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
    Nat.cast_add, Nat.cast_one, add_right_cancel_iff] at hc
  have hv := congrArg (fun z : ZMod N => z.val) hc
  have hval : a.1.val = b.1.val := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt a.1.isLt, Nat.mod_eq_of_lt b.1.isLt] using hv
  have hr : a.1 = b.1 := Fin.ext hval
  apply Prod.ext hr
  apply hinj
  change (N : ℤ) * site a.2 + ((a.1.val + 1 : ℕ) : ℤ) =
    (N : ℤ) * site b.2 + ((b.1.val + 1 : ℕ) : ℤ) at he
  rw [hr] at he
  exact mul_left_cancel₀ hN0 (add_right_cancel he)

/-- A finite injective family of positive physical sites can be bounded by
    the literal initial integer interval; no origin average is substituted. -/
lemma bounded_integer_sum_le {ι : Type*} (I : Finset ι) (x : ι → ℤ)
    (hinj : Function.Injective x) (T : ℝ) (F : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ i ∈ I, if 0 < x i ∧ (x i : ℝ) ≤ T then F (x i) else 0) ≤
      ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, F (n : ℤ) := by
  let S := I.filter (fun i => 0 < x i ∧ (x i : ℝ) ≤ T)
  have hcast (i : ι) (hi : i ∈ S) : ((x i).toNat : ℤ) = x i :=
    Int.toNat_of_nonneg (Finset.mem_filter.mp hi).2.1.le
  have himage : S.image (fun i => (x i).toNat) ⊆ Finset.Icc 1 ⌊T⌋₊ := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hiI, hpos, hT⟩ := Finset.mem_filter.mp hi
    have hc := hcast i hi
    have hcr : ((x i).toNat : ℝ) = (x i : ℝ) := by exact_mod_cast hc
    apply Finset.mem_Icc.mpr
    constructor
    · have hnpos : 0 < (x i).toNat := by rw [← hc] at hpos; exact_mod_cast hpos
      omega
    · exact Nat.le_floor (hcr.trans_le hT)
  have hsum : (∑ n ∈ S.image (fun i => (x i).toNat), F (n : ℤ)) = ∑ i ∈ S, F (x i) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hcast i hi]
    · intro i hi j hj he
      apply hinj
      have hc := congrArg (fun n : ℕ => (n : ℤ)) he
      rwa [hcast i hi, hcast j hj] at hc
  calc
    _ = ∑ i ∈ S, F (x i) := by rw [Finset.sum_filter]
    _ = ∑ n ∈ S.image (fun i => (x i).toNat), F (n : ℤ) := hsum.symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himage (fun n _ _ => hF n)

lemma actualPaddingDegree_neg (Q : Finset ℕ) (n : ℤ) : actualPaddingDegree Q (-n) = actualPaddingDegree Q n := by
  unfold actualPaddingDegree
  congr 1
  ext p
  simp only [Finset.mem_filter, dvd_neg]

lemma actualPaddingVertex_neg (Q : Finset ℕ) (n : ℤ) : actualPaddingVertex Q (-n) = actualPaddingVertex Q n := by
  unfold actualPaddingVertex actualPaddingWeight
  rw [actualPaddingDegree_neg]

lemma actualPaddingDegreeCut_neg (Q : Finset ℕ) (L : ℝ) (n : ℤ) :
    actualPaddingDegreeCut Q L (-n) ↔ actualPaddingDegreeCut Q L n := by
  unfold actualPaddingDegreeCut
  rw [actualPaddingDegree_neg]

#print axioms bounded_integer_sum_le
#print axioms physical_residue_sites_injective

end ReflectedLiouville
