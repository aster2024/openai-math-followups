import ReflectedLiouville.CircleQuotientPrefix
import ReflectedLiouville.PhysicalVolume

set_option autoImplicit false
open scoped BigOperators Classical

namespace ReflectedLiouville

noncomputable def prefixLatticePairs (N : ℕ) (Y : ℝ) : Finset (ℕ × Fin N) :=
  ((Finset.range (⌊Y / N⌋₊ + 1)) ×ˢ Finset.univ).filter
    (fun kr => (((N * kr.1 + (kr.2.val + 1) : ℕ) : ℝ)) ≤ Y)

/-- Exact one-total lattice reindexing of every positive integer in the real
    prefix. The residue sum runs over 1..N through Fin N representatives. -/
theorem quotient_lattice_prefix_sum {α : Type*} [AddCommMonoid α]
    (N : ℕ) (hN : 0 < N) (Y : ℝ) (hY : 0 ≤ Y) (F : ℕ → α) :
    (∑ r : Fin N, ∑ k ∈ quotientPrefixIndices N (r.val + 1) Y, F (N * k + (r.val + 1))) =
      ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, F m := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft : (∑ r : Fin N, ∑ k ∈ quotientPrefixIndices N (r.val + 1) Y, F (N * k + (r.val + 1))) =
      ∑ kr ∈ prefixLatticePairs N Y, F (N * kr.1 + (kr.2.val + 1)) := by
    unfold quotientPrefixIndices prefixLatticePairs
    simp only [Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
  rw [hleft]
  apply Finset.sum_bij (fun kr _ => N * kr.1 + (kr.2.val + 1))
  · intro kr hkr
    obtain ⟨hmem, hu⟩ := Finset.mem_filter.mp hkr
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, Nat.le_floor hu⟩
  · intro a ha b hb he
    have hf := physical_residue_sites_injective N hN (fun k : ℕ => (k : ℤ)) Int.ofNat_injective
    have hc : (N : ℤ) * (a.1 : ℤ) + ((a.2.val + 1 : ℕ) : ℤ) =
        (N : ℤ) * (b.1 : ℤ) + ((b.2.val + 1 : ℕ) : ℤ) := by exact_mod_cast he
    have hp : (a.2, a.1) = (b.2, b.1) := hf hc
    exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)
  · intro m hm
    obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp hm
    let k := (m - 1) / N
    let r : Fin N := ⟨(m - 1) % N, Nat.mod_lt _ hN⟩
    have he : N * k + (r.val + 1) = m := by
      have hp := Nat.mod_add_div (m - 1) N
      dsimp only [k, r]
      omega
    have hmReal : (m : ℝ) ≤ Y := (show (m : ℝ) ≤ (⌊Y⌋₊ : ℝ) by exact_mod_cast hmY).trans (Nat.floor_le hY)
    have hkprod : (k : ℝ) * N ≤ Y := by
      have hnat : N * k ≤ m := by omega
      have hr : ((N * k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnat
      push_cast at hr
      nlinarith only [hr, hmReal]
    have hkfloor : k ≤ ⌊Y / N⌋₊ := Nat.le_floor ((le_div_iff₀ hNreal).mpr hkprod)
    refine ⟨(k, r), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_univ _⟩, ?_⟩, he⟩
    rw [he]
    exact hmReal
  · intro kr hkr
    rfl

#print axioms quotient_lattice_prefix_sum

end ReflectedLiouville
