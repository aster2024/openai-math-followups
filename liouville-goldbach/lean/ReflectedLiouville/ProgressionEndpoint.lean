import ReflectedLiouville.ShortSums
import ReflectedLiouville.Casts
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma progression_interval_unique (q : ℕ) (a : ZMod q) (x H : ℝ) (hHq : H ≤ q)
    (n m : ℕ) (hnlo : x < (n : ℝ)) (hnhi : (n : ℝ) ≤ x + H)
    (hmlo : x < (m : ℝ)) (hmhi : (m : ℝ) ≤ x + H)
    (hnclass : (n : ZMod q) = a) (hmclass : (m : ZMod q) = a) : n = m := by
  have hmod := (ZMod.natCast_eq_natCast_iff n m q).mp (hnclass.trans hmclass.symm)
  rcases le_total n m with hnm | hmn
  · have hd : q ∣ m - n := hmod.dvd'
    have hlt : m - n < q := by
      have h : (m : ℝ) - (n : ℝ) < q := by linarith
      rw [← Nat.cast_sub hnm] at h
      exact_mod_cast h
    have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · have hd : q ∣ n - m := hmod.symm.dvd'
    have hlt : n - m < q := by
      have h : (n : ℝ) - (m : ℝ) < q := by linarith
      rw [← Nat.cast_sub hmn] at h
      exact_mod_cast h
    have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega

lemma short_progression_card_le_one (q : ℕ) (a : ZMod q) (x H : ℝ)
    (hx : 0 ≤ x) (hH : 0 ≤ H) (hHq : H ≤ q) :
    ((Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro n hn m hm
  obtain ⟨hn, hnclass⟩ := Finset.mem_filter.mp hn
  obtain ⟨hm, hmclass⟩ := Finset.mem_filter.mp hm
  have hnI := Finset.mem_Icc.mp hn
  have hmI := Finset.mem_Icc.mp hm
  have hnlo : x < (n : ℝ) := (Nat.floor_lt hx).mp (by omega)
  have hmlo : x < (m : ℝ) := (Nat.floor_lt hx).mp (by omega)
  have hnhi := (Nat.le_floor_iff (add_nonneg hx hH)).mp hnI.2
  have hmhi := (Nat.le_floor_iff (add_nonneg hx hH)).mp hmI.2
  exact progression_interval_unique q a x H hHq n m hnlo hnhi hmlo hmhi hnclass hmclass

/-- Moving one endpoint by at most one modulus changes a progression prefix
    by at most one term. -/
lemma short_progression_norm_le_one (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) (hHq : H ≤ q) :
    ‖shortProgressionSum f q a x H‖ ≤ 1 := by
  classical
  unfold shortProgressionSum
  calc
    _ ≤ ∑ n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), ‖f n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => hf n)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast short_progression_card_le_one q a x H hx hH hHq

#print axioms short_progression_norm_le_one

end ReflectedLiouville
