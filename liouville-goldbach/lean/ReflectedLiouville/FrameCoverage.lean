import ReflectedLiouville.SourceSupportCard

set_option autoImplicit false
open scoped Classical

namespace ReflectedLiouville

lemma centered_integer_frame_covers (M B : ℕ) (hM : 2 * (B + 1) ≤ M)
    (k : ℤ) (hk : -(B : ℤ) ≤ k ∧ k ≤ (B : ℤ)) :
    ∃ i : Fin M, (i.val : ℤ) - (M / 2 : ℕ) = k := by
  have hb : B + 1 ≤ M / 2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by omega)
  have hm : M / 2 + B < M := by omega
  have hlo : 0 ≤ k + (M / 2 : ℕ) := by omega
  have hhi : k + (M / 2 : ℕ) < (M : ℤ) := by omega
  have hcast := Int.toNat_of_nonneg hlo
  have hNat : (k + (M / 2 : ℕ)).toNat < M := by omega
  refine ⟨⟨(k + (M / 2 : ℕ)).toNat, hNat⟩, ?_⟩
  change ((k + (M / 2 : ℕ)).toNat : ℤ) - (M / 2 : ℕ) = k
  rw [hcast]
  ring

lemma reflection_frame_size (L : ℝ) (hL : 2 ≤ L) :
    2 * (⌈Real.exp (100 * L + 1)⌉₊ + 2 + 1) ≤ ⌈Real.exp (103 * L)⌉₊ := by
  let R := Real.exp (100 * L + 1)
  have hR : 4 ≤ R := by dsimp [R]; linarith [Real.add_one_le_exp (100 * L + 1)]
  have hc : (⌈R⌉₊ : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have hExp : 4 ≤ Real.exp (3 * L - 1) := by linarith [Real.add_one_le_exp (3 * L - 1)]
  have heq : Real.exp (103 * L) = R * Real.exp (3 * L - 1) := by
    dsimp only [R]
    rw [← Real.exp_add]
    congr 1
    ring
  have hfull := Nat.le_ceil (Real.exp (103 * L))
  have hprod := mul_le_mul_of_nonneg_left hExp (by linarith : 0 ≤ R)
  rw [← heq] at hprod
  have hbound : (2 : ℝ) * ((⌈R⌉₊ : ℝ) + 2 + 1) ≤ (⌈Real.exp (103 * L)⌉₊ : ℝ) := by
    linarith only [hc, hR, hprod, hfull]
  exact_mod_cast hbound

lemma reflected_target_site_bounds (N : ℕ) (hN : 0 < N) (r k : ℤ) (U : ℝ)
    (hr : 1 ≤ r ∧ r ≤ (N : ℤ)) (hpos : 0 < -((N : ℤ) * k + r))
    (hupper : ((-((N : ℤ) * k + r) : ℤ) : ℝ) ≤ U) :
    k < 0 ∧ -(k : ℝ) ≤ U / N + 1 := by
  have hn : (0 : ℤ) ≤ N := Int.natCast_nonneg _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · by_contra hnot
    have hk : 0 ≤ k := by omega
    have hprod := mul_nonneg hn hk
    linarith only [hprod, hr.1, hpos]
  · have hu : -((N : ℝ) * (k : ℝ) + (r : ℝ)) ≤ U := by
      simpa only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hupper
    have hrN : (r : ℝ) ≤ N := by exact_mod_cast hr.2
    have hmain : -(k : ℝ) * N ≤ U + N := by nlinarith only [hu, hrN]
    have hd := (le_div_iff₀ hNr).mpr hmain
    simpa only [add_div, div_self hNr.ne'] using hd

#print axioms centered_integer_frame_covers
#print axioms reflection_frame_size

end ReflectedLiouville
