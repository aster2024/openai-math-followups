import ReflectedLiouville.Typicality
import OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass
import Mathlib.Tactic

set_option autoImplicit false
open Filter ArithmeticFunction
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def thetaPrefix (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range N).filter Nat.Prime, Real.log (p : ℝ)

lemma thetaPrefix_eq_cumsum (N : ℕ) :
    thetaPrefix N = cumsum
      (fun n => if Nat.Prime n then vonMangoldt.residueClass (1 : ZMod 1) n else 0) N := by
  unfold thetaPrefix cumsum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hprime : Nat.Prime n
  · have hcast : (n : ZMod 1) = 1 := Subsingleton.elim _ _
    simp [hprime, vonMangoldt.residueClass, hcast, vonMangoldt_apply_prime hprime]
  · simp [hprime]

lemma thetaPrefix_ratio_tendsto_one :
    Tendsto (fun N : ℕ => thetaPrefix N / N) atTop (nhds 1) := by
  have h := OAI.SevenEighths.PNT.prime_residueClass_ratio_tendsto (q := 1) (1 : ZMod 1) isUnit_one
  simpa only [← thetaPrefix_eq_cumsum, Nat.totient_one, Nat.cast_one, inv_one] using h

lemma thetaPrefix_le_count_log (N : ℕ) (Y : ℝ) (hNY : (N : ℝ) ≤ Y) (hY : 1 ≤ Y) :
    thetaPrefix N ≤ ((primesUpTo N).card : ℝ) * Real.log Y := by
  have hsub : (Finset.range N).filter Nat.Prime ⊆ primesUpTo N := by
    intro p hp
    obtain ⟨hp, hprime⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hp; omega), hprime⟩
  unfold thetaPrefix
  calc
    _ ≤ ∑ _p ∈ (Finset.range N).filter Nat.Prime, Real.log Y := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp, hprime⟩ := Finset.mem_filter.mp hp
      have hpN : (p : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hp).le
      exact Real.log_le_log (by exact_mod_cast hprime.pos) (hpN.trans hNY)
    _ = (((Finset.range N).filter Nat.Prime).card : ℝ) * Real.log Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (Real.log_nonneg hY)

/-- A weak prime-counting lower bound from the already built PNT declaration. -/
theorem eventually_prime_count_lower :
    ∀ᶠ Y : ℝ in atTop, Y / (4 * Real.log Y) ≤ ((primesUpTo ⌊Y⌋₊).card : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (thetaPrefix_ratio_tendsto_one.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  filter_upwards [eventually_ge_atTop (max 2 ((N₀ : ℝ) + 1))] with Y hY
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hYN : (N₀ : ℝ) ≤ Y := by have := (le_max_right _ _).trans hY; linarith
  have hfloor : N₀ ≤ ⌊Y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hYN
  have hNpos : (0 : ℝ) < ⌊Y⌋₊ := by
    have hfloor1 : (1 : ℕ) ≤ ⌊Y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by norm_num; linarith)
    exact_mod_cast hfloor1
  have htheta := (le_div_iff₀ hNpos).mp (hN₀ ⌊Y⌋₊ hfloor)
  have hhalf : Y / 2 ≤ (⌊Y⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one Y
    linarith
  have hcount := thetaPrefix_le_count_log ⌊Y⌋₊ Y (Nat.floor_le (by linarith)) (by linarith)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (Real.log_pos (by linarith)))).mpr
  nlinarith

#print axioms eventually_prime_count_lower

end ReflectedLiouville
