import OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialGrowth

set_option autoImplicit false

open OAI.TwoPointCorrelations

namespace ReflectedLiouville

private def Poly (f : ℕ → ℕ) (C : ℕ) : Prop :=
  ∃ K : ℕ, ∀ j, f j ≤ K * (j + 1) ^ C

private lemma poly_const (a : ℕ) : Poly (fun _ => a) 0 :=
  ⟨a, fun _ => by simp⟩

private lemma poly_id : Poly (fun j => j) 1 :=
  ⟨1, fun _ => by simp⟩

private lemma poly_add {f g : ℕ → ℕ} {C D : ℕ}
    (hf : Poly f C) (hg : Poly g D) : Poly (fun j => f j + g j) (C + D) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hg
  refine ⟨K + L, fun j => ?_⟩
  calc
    _ ≤ K * (j + 1) ^ C + L * (j + 1) ^ D := Nat.add_le_add (hK j) (hL j)
    _ ≤ K * (j + 1) ^ (C + D) + L * (j + 1) ^ (C + D) := by
      gcongr <;> omega
    _ = _ := by ring

private lemma poly_mul {f g : ℕ → ℕ} {C D : ℕ}
    (hf : Poly f C) (hg : Poly g D) : Poly (fun j => f j * g j) (C + D) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hg
  refine ⟨K * L, fun j => ?_⟩
  calc
    _ ≤ (K * (j + 1) ^ C) * (L * (j + 1) ^ D) := Nat.mul_le_mul (hK j) (hL j)
    _ = _ := by rw [pow_add]; ring

private lemma poly_pow {f : ℕ → ℕ} {C : ℕ}
    (hf : Poly f C) (r : ℕ) : Poly (fun j => f j ^ r) (C * r) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K ^ r, fun j => ?_⟩
  calc
    _ ≤ (K * (j + 1) ^ C) ^ r := Nat.pow_le_pow_left (hK j) r
    _ = _ := by rw [mul_pow, pow_mul]

/-- The literal exponent extracted from the source growth-proof constructors. -/
theorem braverman_degree_explicit_exponent :
    ∃ K : ℕ, ∀ j, bravermanDegree j ≤ K * (j + 1) ^ 8457 := by
  have hid := poly_id
  have hb := poly_mul (poly_mul (poly_const 40) (poly_add hid (poly_const 1)))
    (poly_add hid (poly_const 3))
  have hbase : Poly bravermanBase 2 := by
    change Poly (fun j => 40 * (j + 1) * (j + 3)) 2
    simpa only [Nat.zero_add, Nat.add_zero] using hb
  have hn := poly_mul (poly_add (poly_mul (poly_const 2) hid) (poly_const 3))
    (poly_pow (poly_add (poly_mul (poly_const 2) hbase) (poly_const 2)) 22)
  have hnorm : Poly bravermanNormExponent 45 := by
    change Poly (fun j => (2 * j + 3) * (2 * bravermanBase j + 2) ^ 22) 45
    simpa only [Nat.zero_add, Nat.add_zero] using hn
  have he := poly_mul (poly_const 20) (poly_add hid (poly_const 3))
  have herror : Poly bravermanErrorExponent 1 := by
    change Poly (fun j => 20 * (j + 3)) 1
    simpa only [Nat.zero_add, Nat.add_zero] using he
  have hrt := poly_add (poly_add (poly_add (poly_mul (poly_const 2) hnorm) herror) hid)
    (poly_const 10)
  have hr : Poly bravermanSwitches 47 := by
    change Poly (fun j => 2 * bravermanNormExponent j + bravermanErrorExponent j + j + 10) 47
    simpa only [Nat.zero_add, Nat.add_zero] using hrt
  have hdent := poly_mul (poly_const 24)
    (poly_pow (poly_add (poly_mul (poly_const 2) hr) (poly_const 3)) 2)
  have hden : Poly (fun j => switchingDenominator (bravermanSwitches j)) 94 := by
    simpa only [switchingDenominator] using hdent
  have hDt := poly_mul (poly_mul (poly_const 8) (poly_add hr (poly_const 1)))
    (poly_pow hden 89)
  have hD : Poly (fun j => switchingDegree 89 (bravermanSwitches j)) 8413 := by
    simpa only [switchingDegree] using hDt
  have hout := poly_mul (poly_const 2) (poly_add (poly_pow hbase 22) hD)
  exact hout

theorem braverman_degree_positive_explicit_exponent :
    ∃ K : ℕ, 0 < K ∧ ∀ j, bravermanDegree j ≤ K * (j + 1) ^ 8458 := by
  obtain ⟨K, hK⟩ := braverman_degree_explicit_exponent
  refine ⟨K + 1, by omega, fun j => (hK j).trans ?_⟩
  exact Nat.mul_le_mul (Nat.le_succ K)
    (Nat.pow_le_pow_right (by omega) (by omega))

#print axioms ReflectedLiouville.braverman_degree_explicit_exponent
#print axioms ReflectedLiouville.braverman_degree_positive_explicit_exponent

end ReflectedLiouville
