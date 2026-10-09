import ReflectedLiouville.ReflectionPrimeFamily

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- An arbitrarily large positive inverse exists simultaneously at every
    pool prime. The product modulus need not be small. -/
theorem exists_large_pool_inverse (N : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, Nat.Coprime p N) (B : ℕ) :
    ∃ ell : ℕ, B < ell ∧ ∀ p ∈ P, (N : ZMod p) * (ell : ZMod p) = 1 := by
  let M := ∏ p ∈ P, p
  have hM : 0 < M := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  letI : NeZero M := ⟨hM.ne'⟩
  have hNM : Nat.Coprime N M := Nat.coprime_prod_right_iff.mpr (fun p hp => (hcop p hp).symm)
  let e := ((N : ZMod M)⁻¹).val
  let ell := e + M * (B + 1)
  have hlarge : B < ell := by
    have hM1 : 1 ≤ M := hM
    dsimp only [ell]
    nlinarith
  have hbase : (N : ZMod M) * (e : ZMod M) = 1 := by
    dsimp only [e]
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one N hNM
  have hall : (N : ZMod M) * (ell : ZMod M) = 1 := by
    dsimp only [ell]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    exact hbase
  refine ⟨ell, hlarge, ?_⟩
  intro p hp
  have hpM : p ∣ M := Finset.dvd_prod_of_mem (fun p => p) hp
  have hm : N * ell ≡ 1 [MOD M] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_one] using hall
  have hmp := hm.of_dvd hpM
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmp
  simpa only [Nat.cast_mul, Nat.cast_one] using hz

/-- The concrete reflection supplies meet the inverse theorem's premises. -/
theorem reflection_CRT_inverse (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (B : ℕ) :
    ∃ ell : ℕ, B < ell ∧ ∀ p : ↥((reflectionPrimeFamily N W δ L η hL hW).P ∪
      (reflectionPrimeFamily N W δ L η hL hW).Q),
        (N : ZMod p.val) * (ell : ZMod p.val) = 1 := by
  let data := reflectionPrimeFamily N W δ L η hL hW
  obtain ⟨ell, hlarge, hinv⟩ := exists_large_pool_inverse N (data.P ∪ data.Q)
    (fun p hp => data.prime ⟨p, hp⟩)
    (fun p hp => reflection_pool_coprime_total N W δ L η hL hW p hp) B
  exact ⟨ell, hlarge, fun p => hinv p.val p.property⟩

#print axioms reflection_CRT_inverse

end ReflectedLiouville
