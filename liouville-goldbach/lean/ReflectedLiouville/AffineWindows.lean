import ReflectedLiouville.ProgressionScaling
import ReflectedLiouville.ProgressionShift

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma affine_residue_congruence (N q r b m : ℕ) (hN : 0 < N) :
    (((N * m + r : ℕ) : ZMod (N * q)) = ((N * b + r : ℕ) : ZMod (N * q))) ↔
      ((m : ZMod q) = (b : ZMod q)) := by
  simp only [Nat.cast_add, add_right_cancel_iff]
  exact scaled_residue_congruence N q m b hN

/-- Integer quotient windows map exactly to physical windows without endpoint
    error; the r-offset remains in the physical Liouville arguments. -/
lemma affine_progression_window (f : ℕ → ℂ) (N q r b A B : ℕ)
    (hN : 0 < N) (hAB : A ≤ B) :
    (∑ m ∈ (Finset.Icc (A + 1) B).filter (fun m : ℕ => (m : ZMod q) = (b : ZMod q)), f (N * m + r)) =
      ∑ n ∈ (Finset.Icc (N * A + r + 1) (N * B + r)).filter
        (fun n : ℕ => (n : ZMod (N * q)) = ((N * b + r : ℕ) : ZMod (N * q))), f n := by
  classical
  apply Finset.sum_bij (fun m _ => N * m + r)
  · intro m hm
    obtain ⟨hm, hclass⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, (affine_residue_congruence N q r b m hN).mpr hclass⟩
    · have h := Nat.mul_lt_mul_of_pos_left (by omega : A < m) hN
      omega
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left N hmhi) r
  · intro m hm n hn heq
    exact Nat.eq_of_mul_eq_mul_left hN (Nat.add_right_cancel heq)
  · intro n hn
    obtain ⟨hn, hclass⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hnr : r ≤ n := by omega
    have hmod := (ZMod.natCast_eq_natCast_iff n (N * b + r) (N * q)).mp hclass
    have hmodN := Nat.ModEq.of_dvd (dvd_mul_right N q) hmod
    have hmodr : n ≡ r [MOD N] := by
      apply hmodN.trans
      simp [Nat.ModEq, Nat.add_mod]
    have hdiv : N ∣ n - r := hmodr.symm.dvd'
    obtain ⟨m, hm⟩ := hdiv
    have hnm : n = N * m + r := by omega
    refine ⟨m, ?_, hnm.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have hmul : N * A < N * m := by omega
      have hml : A < m := Nat.lt_of_mul_lt_mul_left hmul
      omega
    · apply Nat.le_of_mul_le_mul_left (by omega : N * m ≤ N * B) hN
    · rw [hnm] at hclass
      exact (affine_residue_congruence N q r b m hN).mp hclass
  · intro m hm
    rfl

#print axioms affine_progression_window

lemma quotient_class_window_physical (f : ℕ → ℂ) (N q r b v h : ℕ) (hN : 0 < N) :
    (∑ m ∈ (Finset.Icc (v + 1) (v + h)).filter (fun m : ℕ => (m : ZMod q) = (b : ZMod q)),
      f (N * m + r)) =
      shortProgressionSum f (N * q) ((N * b + r : ℕ) : ZMod (N * q))
        ((N * v + r : ℕ) : ℝ) ((N * h : ℕ) : ℝ) := by
  rw [affine_progression_window f N q r b v (v + h) hN (Nat.le_add_right _ _)]
  unfold shortProgressionSum
  have hfloor : ⌊((N * v + r : ℕ) : ℝ) + ((N * h : ℕ) : ℝ)⌋₊ = N * v + r + N * h := by
    rw [← Nat.cast_add, Nat.floor_natCast]
  rw [Nat.floor_natCast, hfloor]
  have hid : N * (v + h) + r = N * v + r + N * h := by ring
  rw [hid]

#print axioms quotient_class_window_physical

end ReflectedLiouville
