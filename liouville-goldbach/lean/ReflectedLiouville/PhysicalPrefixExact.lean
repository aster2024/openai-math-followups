import ReflectedLiouville.ReflectedTestVectors
import ReflectedLiouville.FrameCoverage

set_option autoImplicit false
open scoped BigOperators Classical

namespace ReflectedLiouville

/-- A complete residue sample covers every positive physical integer once.
    The finite graph frame is required only to contain the used quotient sites. -/
theorem physical_positive_prefix_sum {V α : Type*} [Fintype V] [AddCommMonoid α]
    (N : ℕ) (hN : 0 < N) (site : V → ℤ) (hinj : Function.Injective site)
    (T : ℝ) (hT : 0 ≤ T) (F : ℤ → α)
    (hcover : ∀ k : ℕ, k ≤ ⌊T / N⌋₊ → ∃ i, site i = (k : ℤ)) :
    (∑ r : Fin N, ∑ i : V,
      if 0 < (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ) ∧
          (((N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)) : ℝ) ≤ T then
        F ((N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)) else 0) =
      ∑ m ∈ Finset.Icc 1 ⌊T⌋₊, F (m : ℤ) := by
  let physical := fun ri : Fin N × V => (N : ℤ) * site ri.2 + ((ri.1.val + 1 : ℕ) : ℤ)
  let S := (Finset.univ : Finset (Fin N × V)).filter (fun ri => 0 < physical ri ∧ (physical ri : ℝ) ≤ T)
  have hleft : (∑ r : Fin N, ∑ i : V,
      if 0 < physical (r,i) ∧ (physical (r,i) : ℝ) ≤ T then F (physical (r,i)) else 0) =
      ∑ ri ∈ S, F (physical ri) := by
    simp only [S, Finset.sum_filter, Fintype.sum_prod_type]
  have hstart : (∑ r : Fin N, ∑ i : V,
      if 0 < (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ) ∧
          (((N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)) : ℝ) ≤ T then
        F ((N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)) else 0) =
      ∑ ri ∈ S, F (physical ri) := by
    convert hleft using 1
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [physical]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [hstart]
  apply Finset.sum_bij (fun ri _ => (physical ri).toNat)
  · intro ri hri
    obtain ⟨_, hp, hu⟩ := Finset.mem_filter.mp hri
    have hc := Int.toNat_of_nonneg hp.le
    have hn : 1 ≤ (physical ri).toNat := by omega
    have hr : ((physical ri).toNat : ℝ) ≤ T := by
      have hcast : ((physical ri).toNat : ℝ) = (physical ri : ℝ) := by exact_mod_cast hc
      rw [hcast]
      exact hu
    exact Finset.mem_Icc.mpr ⟨hn, Nat.le_floor hr⟩
  · intro a ha b hb he
    have hpa := (Finset.mem_filter.mp ha).2.1
    have hpb := (Finset.mem_filter.mp hb).2.1
    have hca := Int.toNat_of_nonneg hpa.le
    have hcb := Int.toNat_of_nonneg hpb.le
    apply physical_residue_sites_injective N hN site hinj
    change physical a = physical b
    omega
  · intro m hm
    obtain ⟨hm1, hmT⟩ := Finset.mem_Icc.mp hm
    let k := (m - 1) / N
    let r : Fin N := ⟨(m - 1) % N, Nat.mod_lt _ hN⟩
    have he : N * k + (r.val + 1) = m := by
      have hp := Nat.mod_add_div (m - 1) N
      dsimp only [k, r]
      omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hmReal : (m : ℝ) ≤ T := (by exact_mod_cast hmT : (m : ℝ) ≤ (⌊T⌋₊ : ℝ)).trans (Nat.floor_le hT)
    have hk : k ≤ ⌊T / N⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ hNr).mpr
      have hn : N * k ≤ m := by omega
      have hr : (N : ℝ) * k ≤ (m : ℝ) := by exact_mod_cast hn
      nlinarith only [hr, hmReal]
    obtain ⟨i, hi⟩ := hcover k hk
    have hp : physical (r,i) = (m : ℤ) := by
      dsimp only [physical]
      rw [hi]
      exact_mod_cast he
    refine ⟨(r,i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [hp]
      exact ⟨by exact_mod_cast hm1, by simpa only [Int.cast_natCast] using hmReal⟩
    · rw [hp, Int.toNat_natCast]
  · intro ri hri
    obtain ⟨_, hp, _⟩ := Finset.mem_filter.mp hri
    rw [Int.toNat_of_nonneg hp.le]

#print axioms physical_positive_prefix_sum
end ReflectedLiouville
