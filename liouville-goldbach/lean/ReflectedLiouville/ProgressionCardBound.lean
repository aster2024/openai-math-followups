import ReflectedLiouville.ProgressionEndpoint
import ReflectedLiouville.RealCutoff

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma progression_card_quotient_bound (q : ℕ) [NeZero q] (a : ZMod q) (x H : ℝ)
    (hx : 0 ≤ x) (hH : 0 ≤ H) :
    (((Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a)).card : ℝ) ≤
      H / q + 2 := by
  classical
  let S := (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a)
  let T := Finset.Icc (⌊x⌋₊ / q) (⌊x + H⌋₊ / q)
  have hmap : Set.MapsTo (fun n : ℕ => n / q) S T := by
    intro n hn
    obtain ⟨hn, hclass⟩ := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (by omega), Nat.div_le_div_right hnI.2⟩
  have hinj : Set.InjOn (fun n : ℕ => n / q) S := by
    intro n hn m hm hnm
    have hnclass := (Finset.mem_filter.mp hn).2
    have hmclass := (Finset.mem_filter.mp hm).2
    have hmod := (ZMod.natCast_eq_natCast_iff' n m q).mp (hnclass.trans hmclass.symm)
    nlinarith [Nat.div_add_mod n q, Nat.div_add_mod m q]
  have hcard := Finset.card_le_card_of_injOn (fun n : ℕ => n / q) hmap hinj
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hfloorle : ⌊x⌋₊ / q ≤ ⌊x + H⌋₊ / q :=
    Nat.div_le_div_right (Nat.floor_mono (by linarith))
  have hTcard : T.card = ⌊x + H⌋₊ / q + 1 - ⌊x⌋₊ / q := by simp [T]
  have hcast : (T.card : ℝ) = (⌊(x + H) / (q : ℝ)⌋₊ : ℝ) + 1 - ⌊x / (q : ℝ)⌋₊ := by
    rw [hTcard, Nat.cast_sub (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, floor_div_natCast _ q (NeZero.ne q)]
  have hupper := Nat.floor_le (div_nonneg (add_nonneg hx hH) hq.le)
  have hlower := Nat.lt_floor_add_one (x / (q : ℝ))
  have hdiff : (T.card : ℝ) ≤ H / q + 2 := by
    rw [hcast]
    have hid : (x + H) / (q : ℝ) = x / q + H / q := by ring
    rw [hid] at hupper
    rw [hid]
    linarith
  exact (show (S.card : ℝ) ≤ T.card by exact_mod_cast hcard).trans hdiff

theorem short_progression_norm_card_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) [NeZero q] (a : ZMod q) (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ‖shortProgressionSum f q a x H‖ ≤ H / q + 2 := by
  unfold shortProgressionSum
  calc
    _ ≤ ∑ n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => hf n)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact progression_card_quotient_bound q a x H hx hH

#print axioms short_progression_norm_card_bound

end ReflectedLiouville
