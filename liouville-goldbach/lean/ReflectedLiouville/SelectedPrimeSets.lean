import ReflectedLiouville.ActivePaddingCost
import OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def keptPrimeCoordinates (Q R : Finset ℕ) : Finset R :=
  Finset.univ.filter (fun p => p.val ∈ Q)

lemma mem_keptPrimeCoordinates (Q R : Finset ℕ) (p : R) :
    p ∈ keptPrimeCoordinates Q R ↔ p.val ∈ Q := by simp [keptPrimeCoordinates]

noncomputable def keptPrimeEquiv (Q R : Finset ℕ) (hQR : Q ⊆ R) : Q ≃ keptPrimeCoordinates Q R where
  toFun p := ⟨⟨p.val, hQR p.property⟩, (mem_keptPrimeCoordinates Q R _).mpr p.property⟩
  invFun p := ⟨p.val.val, (mem_keptPrimeCoordinates Q R p.val).mp p.property⟩
  left_inv p := rfl
  right_inv p := rfl

noncomputable def coordinateActivePrimes {R : Finset ℕ} (S : Finset R) (b : S → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun p : S => b p = true)).image (fun p => p.val.val)

lemma coordinateActivePrimes_reindex (Q R : Finset ℕ) (hQR : Q ⊆ R) (b : Q → Bool) :
    coordinateActivePrimes (keptPrimeCoordinates Q R)
      (fun p => b ((keptPrimeEquiv Q R hQR).symm p)) = paddingAvailablePrimes Q b := by
  ext n
  simp only [coordinateActivePrimes, paddingAvailablePrimes, selectedCoordinates,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hn⟩
    exact ⟨(keptPrimeEquiv Q R hQR).symm p, hp, hn⟩
  · rintro ⟨p, hp, hn⟩
    refine ⟨keptPrimeEquiv Q R hQR p, ?_, hn⟩
    simpa only [Equiv.symm_apply_apply] using hp

lemma paddingAvailablePrimes_join_false (R : Finset ℕ) (S : Finset R) (b : S → Bool) :
    paddingAvailablePrimes R (joinCoordinates S b (fun _ => false)) = coordinateActivePrimes S b := by
  ext n
  simp only [coordinateActivePrimes, paddingAvailablePrimes, selectedCoordinates,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hn⟩
    have hpS : p ∈ S := by
      by_contra hnot
      simp only [joinCoordinates, dif_neg hnot, Bool.false_eq_true] at hp
    refine ⟨⟨p, hpS⟩, ?_, hn⟩
    simpa only [joinCoordinates, dif_pos hpS] using hp
  · rintro ⟨p, hp, hn⟩
    refine ⟨p.val, ?_, hn⟩
    simpa only [joinCoordinates, dif_pos p.property] using hp

lemma kept_prime_normalizer (Q R : Finset ℕ) (hQR : Q ⊆ R) :
    (∏ p : keptPrimeCoordinates Q R, (1 + 4 / (p.val.val : ℝ))) = paddingTiltNormalizer Q := by
  unfold paddingTiltNormalizer
  have he := (keptPrimeEquiv Q R hQR).prod_comp (fun p : keptPrimeCoordinates Q R =>
    1 + 4 / (p.val.val : ℝ))
  exact he.symm

noncomputable def removedPrimeEquiv (Q R : Finset ℕ) :
    {p : R // p ∉ keptPrimeCoordinates Q R} ≃ ↥(R \ Q) where
  toFun p := ⟨p.val.val, Finset.mem_sdiff.mpr ⟨p.val.property, by
    intro hp
    exact p.property ((mem_keptPrimeCoordinates Q R p.val).mpr hp)⟩⟩
  invFun p := ⟨⟨p.val, (Finset.mem_sdiff.mp p.property).1⟩, by
    intro hp
    exact (Finset.mem_sdiff.mp p.property).2 ((mem_keptPrimeCoordinates Q R _).mp hp)⟩
  left_inv p := rfl
  right_inv p := rfl

lemma removed_prime_product (Q R : Finset ℕ) (f : ℕ → ℝ) :
    (∏ p : {p : R // p ∉ keptPrimeCoordinates Q R}, f p.val.val) = ∏ p ∈ R \ Q, f p := by
  have he := (removedPrimeEquiv Q R).prod_comp (fun p : ↥(R \ Q) => f p.val)
  rw [← Finset.prod_coe_sort (R \ Q) f]
  exact he

#print axioms paddingAvailablePrimes_join_false

end ReflectedLiouville
