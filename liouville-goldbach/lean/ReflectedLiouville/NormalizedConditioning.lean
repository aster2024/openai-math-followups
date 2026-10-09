import ReflectedLiouville.IndependentConditioning
import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw

set_option autoImplicit false
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma product_split_finset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (z : ι → ℝ) :
    (∏ i : S, z i) * (∏ i : {i : ι // i ∉ S}, z i) = ∏ i, z i := by
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S) z
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) := Subsingleton.elim _ _
  rw [hinst] at h
  exact h

/-- Conditioning with literal product normalizers. This retains both the
    probability denominator and the full/reduced normalizer ratio. -/
theorem normalized_conditioning_cost
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι) (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (E : {i : ι // i ∉ S} → A → Prop)
    (hE : ∀ i : {i : ι // i ∉ S}, 0 < (μ i).probability (E i))
    (F : (ι → A) → ℝ) (f : (S → A) → ℝ)
    (hF : ∀ x, 0 ≤ F x)
    (hagree : ∀ (x : S → A) (y : {i : ι // i ∉ S} → A),
      (∀ i, E i (y i)) → F (joinCoordinates S x y) = f x) :
    (FiniteLaw.independent (fun i : S => μ i)).average f / (∏ i : S, z i) ≤
      ((FiniteLaw.independent μ).average F / (∏ i, z i)) *
        ∏ i : {i : ι // i ∉ S}, z i / (μ i).probability (E i) := by
  have hc := independent_conditioning_cost_product μ S E F f hF hagree
  let P := ∏ i : {i : ι // i ∉ S}, (μ i).probability (E i)
  let Z := ∏ i : S, z i
  let R := ∏ i : {i : ι // i ∉ S}, z i
  have hP : 0 < P := Finset.prod_pos (fun i _ => hE i)
  have hZ : 0 < Z := Finset.prod_pos (fun i _ => hz i)
  have hR : 0 < R := Finset.prod_pos (fun i _ => hz i)
  have htotal : (∏ i, z i) = Z * R := (product_split_finset S z).symm
  have hprod : (∏ i : {i : ι // i ∉ S}, z i / (μ i).probability (E i)) = R / P := by
    dsimp only [R, P]
    rw [Finset.prod_div_distrib]
  have hsmall : (FiniteLaw.independent (fun i : S => μ i)).average f ≤
      (FiniteLaw.independent μ).average F / P := by
    apply (le_div_iff₀ hP).mpr
    simpa only [P, mul_comm] using hc
  calc
    _ ≤ ((FiniteLaw.independent μ).average F / P) / Z := div_le_div_of_nonneg_right hsmall hZ.le
    _ = _ := by rw [htotal, hprod]; field_simp <;> ring

lemma padding_original_false_probability (p : ℕ) (hp : 2 ≤ p) :
    (paddingOriginalPrimeLaw p hp).probability (fun b => b = false) = 1 - 1 / (p : ℝ) := by
  simp [paddingOriginalPrimeLaw, booleanLaw, FiniteLaw.probability, FiniteLaw.average, one_div]

lemma padding_conditioning_single_factor (p : ℕ) (hp : 2 ≤ p) :
    (1 + 4 / (p : ℝ)) / (paddingOriginalPrimeLaw p hp).probability (fun b => b = false) =
      ((p : ℝ) + 4) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [padding_original_false_probability]
  field_simp
  <;> ring

/-- The manuscript's exact product of (p+4)/(p−1), already at normalized
    original Bernoulli expectations and with arbitrary retained observables. -/
theorem normalized_padding_conditioning
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 2 ≤ p i) (S : Finset ι)
    (F : (ι → Bool) → ℝ) (f : (S → Bool) → ℝ)
    (hF : ∀ x, 0 ≤ F x)
    (hagree : ∀ x : S → Bool, F (joinCoordinates S x (fun _ => false)) = f x) :
    (FiniteLaw.independent (fun i : S => paddingOriginalPrimeLaw (p i) (hp i))).average f /
        (∏ i : S, (1 + 4 / (p i : ℝ))) ≤
      ((FiniteLaw.independent (fun i => paddingOriginalPrimeLaw (p i) (hp i))).average F /
          (∏ i, (1 + 4 / (p i : ℝ)))) *
        ∏ i : {i : ι // i ∉ S}, ((p i : ℝ) + 4) / ((p i : ℝ) - 1) := by
  have hz : ∀ i, 0 < 1 + 4 / (p i : ℝ) := fun i => by positivity
  have hprob : ∀ i : {i : ι // i ∉ S}, 0 <
      (paddingOriginalPrimeLaw (p i) (hp i)).probability (fun b => b = false) := by
    intro i
    rw [padding_original_false_probability]
    have hpr : (2 : ℝ) ≤ p i := by exact_mod_cast hp i
    have hq : 1 / (p i : ℝ) ≤ 1 / 2 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hpr
    linarith
  have hc := normalized_conditioning_cost
    (fun i => paddingOriginalPrimeLaw (p i) (hp i)) S (fun i => 1 + 4 / (p i : ℝ)) hz
    (fun _ b => b = false) hprob F f hF (by
      intro x y hy
      have heq : y = fun _ => false := funext hy
      rw [heq]
      exact hagree x)
  simpa only [padding_conditioning_single_factor] using hc

#print axioms normalized_padding_conditioning

end ReflectedLiouville
