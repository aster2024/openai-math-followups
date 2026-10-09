import ReflectedLiouville.Definitions

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- A real-valued, one-bounded multiplicative function in the published results. -/
def RealMultiplicative (f : ℕ → ℂ) : Prop :=
  Multiplicative f ∧ OneBounded f ∧ ∀ n : ℕ, (f n).im = 0

/-- KMT's distance excludes primes dividing the modulus. -/
noncomputable def squaredDistanceMod (q : ℕ) (f g : ℕ → ℂ) (X : ℝ) : ℝ :=
  ∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p => ¬ p ∣ q),
    (1 - (f p * conj (g p)).re) / (p : ℝ)

/-- The minimizing character and twist, allowing any choice in a tie. -/
def MinimizingCharacter {q : ℕ} (f : ℕ → ℂ) (X : ℝ)
    (χ₁ : DirichletCharacter ℂ q) (t₁ : ℝ) : Prop :=
  |t₁| ≤ X ∧ ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ X →
    squaredDistanceMod q f (characterTwist χ₁ t₁) X ≤
      squaredDistanceMod q f (characterTwist χ t) X

def RealCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a : ZMod q, (χ a).im = 0

/-- Definition 1.1 of KMT v5, using its literal 1/100 prime-counting test. -/
def KMTTypical (q : ℕ) (y : ℝ) : Prop :=
  ∀ z : ℝ, y ≤ z →
    (((primesUpTo ⌊z⌋₊).filter (fun p => p ∣ q)).card : ℝ) ≤
      ((primesUpTo ⌊z⌋₊).card : ℝ) / 100

/-- The explicit zero-box good set of KMT Lemma 8.1, equation (32).
    Its conductor cutoff excludes the principal pole in the intended range. -/
def KMTGoodModulus (X u M : ℝ) (q : ℕ) [NeZero q] : Prop :=
  0 < q ∧ (q : ℝ) ≤ X ∧
  ∀ χ : DirichletCharacter ℂ q,
    Real.rpow X (Real.rpow u 20) < (χ.conductor : ℝ) →
    ∀ s : ℂ, 1 - M * Real.log (Real.log X) / Real.log X ≤ s.re →
      |s.im| ≤ 3 * X → DirichletCharacter.LFunction χ s ≠ 0

/-- Exactly the integers x < n ≤ x+H in one progression. -/
noncomputable def shortProgressionSum (f : ℕ → ℂ) (q : ℕ)
    (a : ZMod q) (x H : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter
    (fun n : ℕ => (n : ZMod q) = a), f n

/-- Character mean in KMT Corollary 1.6, without a twist. -/
noncomputable def characterMean {q : ℕ} (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, f n * conj (χ (n : ZMod q))

/-- Corollary 1.6 allows deletion of the main term for a nonreal character. -/
noncomputable def kmtRealMainTerm {q : ℕ} (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (X H : ℝ) (a : ZMod q) : ℂ := by
  classical
  exact if RealCharacter χ then
    χ a / (Nat.totient q : ℂ) * ((H / (3 * X) : ℝ) : ℂ) * characterMean f χ X
    else 0

/-- Unit classes only, as indicated by the starred residue sum in KMT. -/
noncomputable def kmtRealVariance {q : ℕ} [NeZero q] (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (X H : ℝ) : ℝ :=
  ∫ x in X..2 * X,
    ∑ a : (ZMod q)ˣ, ‖shortProgressionSum f q (a : ZMod q) x H -
      kmtRealMainTerm f χ X H (a : ZMod q)‖ ^ 2

/-- Restricted KMT v5 Corollary 1.6. Its statements assert only existence of a
    good set; the explicit zero box comes from Proposition 9.4, the ε^(11/10)
    substitution in §9.2, and the proof of Corollary 1.6 via Lemma 8.2(ii).
    The -1/50 threshold is required by Corollary 8.4 and Lemma 8.2; the log cap
    validates the terminal interval in (52); the q-dependent buffer validates
    the first mean-value estimate in §9.3, Case X_1. -/
def KMTRealProgressionVarianceInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 10 ≤ X₀ ∧
    ∀ X H Q ε : ℝ, X₀ ≤ X → H ≤ X → 10 ≤ H → 1 ≤ Q → Q ≤ H / 10 →
      0 < ε → ε < 1 →
      Real.rpow (Real.log (H / Q)) (-1 / 200) ≤ Real.rpow ε (11 / 10) →
      Real.rpow (Real.log X) (-1 / 50) < Real.rpow ε (33 / 5) →
      1 / Real.log (Real.log X) ≤ Real.rpow ε (-88) →
      Real.rpow ε (-88) ≤
        Real.rpow (Real.rpow ε (33 / 5)) 20 * Real.log X /
          (20 * Real.log (Real.log X)) →
      Real.log (H / Q) ≤ Real.rpow (Real.log X) (2 / 5) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q →
        (q : ℝ) * Real.rpow (H / Q) (Real.rpow ε (11 / 10) / 100) ≤ Q →
        KMTGoodModulus X (Real.rpow ε (33 / 5)) (Real.rpow ε (-88)) q →
        KMTTypical q (Real.rpow (H / Q) (ε ^ 2)) →
        ∀ f : ℕ → ℂ, RealMultiplicative f →
          ∀ (χ₁ : DirichletCharacter ℂ q) (t₁ : ℝ),
            MinimizingCharacter f X χ₁ t₁ →
            kmtRealVariance f χ₁ X H ≤ C * ε * (Nat.totient q : ℝ) * X * (H / q) ^ 2

/-- Modulus-one twist, reusing the library's definition. -/
noncomputable def modulusOneTwist (t : ℝ) : ℕ → ℂ :=
  characterTwist (1 : DirichletCharacter ℂ 1) t

noncomputable def halaszMinimum (f : ℕ → ℂ) (X T : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, |t| ≤ T ∧ v = squaredDistance f (modulusOneTwist t) ⌊X⌋₊}

/-- The sole remaining published KMT input. Halasz is supplied by the proved library. -/
structure KMTInput : Prop where
  realProgressionVariance : KMTRealProgressionVarianceInput

/-- MRT corrected arXiv:1503.05121v3, Lemma C.1, specialized to its fixed
    modulus-one character. The real multiplicative function still varies.
    Both additive constants are absolute after fixing that character. -/
def MRTRealTwistRepulsionInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℂ, RealMultiplicative f →
    ∀ X : ℝ, 100 ≤ X → ∀ t : ℝ,
      (1 ≤ |t| → |t| ≤ X →
        (1 / 4 : ℝ) * Real.sqrt (Real.log (Real.log X)) - C ≤
          Real.sqrt (squaredDistance f (modulusOneTwist t) ⌊X⌋₊)) ∧
      (|t| ≤ 1 →
        (1 / 3 : ℝ) * Real.sqrt (squaredDistance f (modulusOneTwist 0) ⌊X⌋₊) - C ≤
          Real.sqrt (squaredDistance f (modulusOneTwist t) ⌊X⌋₊))

end ReflectedLiouville
