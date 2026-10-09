import ReflectedLiouville.TotientUniform

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma padding_hole_factor_le_totient_power (p : ℕ) (hp : p.Prime) :
    ((p : ℝ) + 4) / ((p : ℝ) - 1) ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ (5 : ℕ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hinv : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 / ((p : ℝ) - 1)) 5
  have hleft : ((p : ℝ) + 4) / ((p : ℝ) - 1) = 1 + 5 * (1 / ((p : ℝ) - 1)) := by
    field_simp; ring
  have hright : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by field_simp; ring
  rw [hleft, hright]
  simpa only [Nat.cast_ofNat] using hb

lemma padding_hole_product_le_ratio (N : ℕ) [NeZero N] (E : Finset ℕ)
    (hE : E ⊆ N.primeFactors) :
    (∏ p ∈ E, ((p : ℝ) + 4) / ((p : ℝ) - 1)) ≤
      ((N : ℝ) / N.totient) ^ (5 : ℕ) := by
  classical
  have hp (p : ℕ) (h : p ∈ N.primeFactors) : p.Prime := (Nat.mem_primeFactors.mp h).1
  have hfac (p : ℕ) (h : p ∈ N.primeFactors) : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    apply (one_le_div (by linarith : 0 < (p : ℝ) - 1)).mpr
    linarith
  calc
    _ ≤ ∏ p ∈ E, ((p : ℝ) / ((p : ℝ) - 1)) ^ (5 : ℕ) := by
      apply Finset.prod_le_prod₀
      · intro p h
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p (hE h)).two_le
        exact div_nonneg (by linarith) (by linarith)
      · intro p h
        exact padding_hole_factor_le_totient_power p (hp p (hE h))
    _ = (∏ p ∈ E, (p : ℝ) / ((p : ℝ) - 1)) ^ (5 : ℕ) := by rw [Finset.prod_pow]
    _ ≤ (∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) ^ (5 : ℕ) := by
      apply pow_le_pow_left₀
      · exact Finset.prod_nonneg (fun p h => (hfac p (hE h)).trans' (by norm_num))
      · have hfilter : N.primeFactors.filter (fun p => p ∈ E) = E := by
          ext p
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hE h, h⟩⟩
        calc
          _ = ∏ p ∈ N.primeFactors, (if p ∈ E then (p : ℝ) / ((p : ℝ) - 1) else 1) := by
            rw [← Finset.prod_filter, hfilter]
          _ ≤ _ := by
            apply Finset.prod_le_prod₀
            · intro p h
              split_ifs with he
              · exact (hfac p h).trans' (by norm_num)
              · norm_num
            · intro p h
              split_ifs with he
              · exact le_rfl
              · exact hfac p h
    _ = _ := by rw [← totient_ratio_product]

/-- The precise polynomial logarithmic loss needed in Lemma paddingholes,
    uniform over every subset of the changing prime factors of N. -/
theorem padding_hole_product_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N], Real.exp 2 ≤ (N : ℝ) →
      ∀ E : Finset ℕ, E ⊆ N.primeFactors →
        (∏ p ∈ E, ((p : ℝ) + 4) / ((p : ℝ) - 1)) ≤
          C * (Real.log (Real.log (N : ℝ))) ^ (10 : ℕ) := by
  obtain ⟨A, hA, hr⟩ := totient_ratio_uniform
  refine ⟨A ^ (5 : ℕ), by positivity, ?_⟩
  intro N inst hN E hE
  have hratio : 0 ≤ (N : ℝ) / N.totient := by positivity
  have h := (padding_hole_product_le_ratio N E hE).trans
    (pow_le_pow_left₀ hratio (hr (N : ℝ) hN N le_rfl) 5)
  convert h using 1 <;> ring

#print axioms padding_hole_product_uniform

end ReflectedLiouville
