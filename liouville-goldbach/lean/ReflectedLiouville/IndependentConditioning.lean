import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

set_option autoImplicit false
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Conditioning outside retained coordinates leaves their law unchanged. -/
theorem independent_conditioning_cost
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι)
    (E : {i : ι // i ∉ S} → A → Prop)
    (F : (ι → A) → ℝ) (f : (S → A) → ℝ)
    (hF : ∀ z, 0 ≤ F z)
    (hagree : ∀ (x : S → A) (y : {i : ι // i ∉ S} → A),
      (∀ i, E i (y i)) → F (joinCoordinates S x y) = f x) :
    ((FiniteLaw.independent (fun i : {i : ι // i ∉ S} => μ i)).probability
      (fun y => ∀ i, E i (y i))) *
      (FiniteLaw.independent (fun i : S => μ i)).average f ≤
        (FiniteLaw.independent μ).average F := by
  classical
  rw [FiniteLaw.independent_average_split μ S F]
  let ν := FiniteLaw.independent (fun i : {i : ι // i ∉ S} => μ i)
  let σ := FiniteLaw.independent (fun i : S => μ i)
  have hpoint : ∀ y : {i : ι // i ∉ S} → A,
      (if ∀ i, E i (y i) then σ.average f else 0) ≤
        σ.average (fun x => F (joinCoordinates S x y)) := by
    intro y
    by_cases hy : ∀ i, E i (y i)
    · simp only [ite_eq_left hy]
      have hf : (fun x => F (joinCoordinates S x y)) = f := funext (fun x => hagree x y hy)
      rw [hf]
    · simp only [ite_eq_right hy]
      exact σ.average_nonneg (fun x => hF _)
  have h := ν.average_mono hpoint
  change ν.probability (fun y => ∀ i, E i (y i)) * σ.average f ≤ _
  have heq : ν.average (fun y => if ∀ i, E i (y i) then σ.average f else 0) =
      ν.probability (fun y => ∀ i, E i (y i)) * σ.average f := by
    unfold FiniteLaw.probability
    rw [← ν.average_mul_const]
    apply congrArg ν.average
    funext y
    split_ifs <;> simp
  rwa [heq] at h

/-- Exact product cost of single-site conditioning. -/
theorem independent_conditioning_cost_product
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι)
    (E : {i : ι // i ∉ S} → A → Prop)
    (F : (ι → A) → ℝ) (f : (S → A) → ℝ)
    (hF : ∀ z, 0 ≤ F z)
    (hagree : ∀ (x : S → A) (y : {i : ι // i ∉ S} → A),
      (∀ i, E i (y i)) → F (joinCoordinates S x y) = f x) :
    (∏ i : {i : ι // i ∉ S}, (μ i).probability (E i)) *
      (FiniteLaw.independent (fun i : S => μ i)).average f ≤
        (FiniteLaw.independent μ).average F := by
  have h := independent_conditioning_cost μ S E F f hF hagree
  rwa [FiniteLaw.independent_probability_all] at h

#print axioms independent_conditioning_cost_product

end ReflectedLiouville
