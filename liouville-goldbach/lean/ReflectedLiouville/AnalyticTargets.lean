import ReflectedLiouville.PublishedInputs
import OAI.NumberTheory.TwoPoint.PublishedInputs

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

/-- The exact missing intermediate analytic tail estimate from Lemma realmean.
    This is a project target, not a faithful published input and not an axiom. -/
def RealCharacterPrimeTailBound : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
      ∀ χ : DirichletCharacter ℂ q, RealCharacter χ → χ ≠ 1 →
        |∑ p ∈ (OAI.TwoPointCorrelations.primesUpTo ⌊X⌋₊).filter
          (fun p : ℕ => (Real.log X) ^ (64 : ℕ) < (p : ℝ)), (χ (p : ZMod q)).re / p| ≤ C

/-- Paper Lemma realmean. This is an unproved project target, not an external input. -/
def RealCharacterMeanBound : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
      ∀ χ : DirichletCharacter ℂ q, RealCharacter χ →
        ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville n * χ (n : ZMod q)‖ ≤
          C * X / Real.rpow (Real.log X) (1 / 40)

/-- All residue classes, including zero and nonunits. -/
noncomputable def allResidueVariance (q : ℕ) [NeZero q] (X H : ℝ) : ℝ :=
  ∫ x in X..2 * X, ∑ a : ZMod q, ‖shortProgressionSum liouville q a x H‖ ^ 2

/-- Paper Lemma variance. ν is fixed before the constants, and q remains free. -/
def ShortProgressionVarianceBound : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧
    ∀ (q : ℕ) [NeZero q] (X H : ℝ), X₀ ≤ X → H ≤ X → 10 * (q : ℝ) ≤ H →
      Real.exp (Real.rpow (Real.log X) ν) ≤ H / q →
      allResidueVariance q X H ≤ C * X * H ^ 2 / q /
        Real.rpow (Real.log (H / q)) (1 / 1000)

noncomputable def quotientExponentialSum (N : ℕ) (D : ℝ) (r : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range ⌊D⌋₊,
    liouville (N * k + r) * OAI.TwoPointCorrelations.additiveCharacter θ k

/-- Paper Lemma fourier. A single frequency is outside the residue average. -/
def QuotientFourierBound : Prop :=
  ∀ ν₀ : ℝ, 0 < ν₀ → ν₀ ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ D : ℝ,
      Real.exp (Real.rpow (Real.log (N : ℝ)) ν₀) ≤ D → D ≤ N →
      ∀ θ : ℝ,
        ((∑ r ∈ Finset.Icc 1 N, ‖quotientExponentialSum N D r θ‖) / (N : ℝ)) ≤
          C * D / Real.rpow (Real.log D) (1 / 3000)

end ReflectedLiouville
