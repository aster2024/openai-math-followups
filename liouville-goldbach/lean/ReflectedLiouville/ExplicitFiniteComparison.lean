import ReflectedLiouville.ExplicitCircuitBudget
import OAI.NumberTheory.TwoPoint.Bounds.FiniteLawParameters

set_option autoImplicit false
set_option maxHeartbeats 1000000
open OAI.TwoPointCorrelations Finset
namespace ReflectedLiouville

/-- Fixed-exponent adaptations of CircuitComparison, FourierMass,
EncodedCoefficients and FiniteResidueComparison, preserving the literal
finite-law errors and avoiding the source's existential exponent field. -/
theorem explicit_fourier_comparison :
    ∃ K : ℕ, 0 < K ∧ ∀ (n : ℕ) (c : AC0Circuit n), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ (8458 : ℕ) ≤ (t : ℝ) →
        ∀ (f : BooleanCube n → ℝ) (a : ℝ),
          (∀ x, 0 ≤ f x) → cubeAverage f = 1 → 0 ≤ a → lowWalshMass f t ≤ a →
          |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
            3 * a / 2 + ε := by
  obtain ⟨K,hK,hbound⟩ := braverman_depth22_8458
  refine ⟨K,hK,?_⟩
  intro n c hdepth ε hε hεmax t ht f a hf hmean ha hmass
  let g := correctedCubeDensity f t a
  have hcorr := fourierCorrection f t a hf hmean ha hmass
  have hBrav := hbound n c hdepth ε hε hεmax t ht g hcorr.1 hcorr.2.1 hcorr.2.2.1
  have hTV := circuit_event_le_totalVariation c f g (hmean.trans hcorr.2.1.symm)
  have hTVbound : cubeAverage (fun x => |f x - g x|) / 2 ≤ 3 * a / 2 := by
    simpa only [abs_sub_comm] using hcorr.2.2.2
  calc
    |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
        |cubeAverage (fun x => f x * c.indicator x) -
          cubeAverage (fun x => g x * c.indicator x)| +
        |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| :=
      abs_sub_le _ _ _
    _ ≤ 3 * a / 2 + ε := add_le_add (hTV.trans hTVbound) hBrav

theorem explicit_coefficient_comparison :
    ∃ K : ℕ, 0 < K ∧ ∀ (n : ℕ), 0 < n →
      ∀ (c : AC0Circuit n), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ (8458 : ℕ) ≤ (t : ℝ) →
        ∀ (f : BooleanCube n → ℝ) (δ a : ℝ),
          (∀ x, 0 ≤ f x) → cubeAverage f = 1 → 0 ≤ δ →
          (∀ S ∈ lowWalshSets n t, |walshCoefficient f S| ≤ δ) →
          δ * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t ≤ a →
          |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
            3 * a / 2 + ε := by
  obtain ⟨K,hK,hbound⟩ := explicit_fourier_comparison
  refine ⟨K,hK,?_⟩
  intro n hn c hc ε hε hεmax t ht f δ a hf hmean hδ hcoeff ha
  have hmass := lowWalshMass_le_of_coefficients hn f t δ hδ hcoeff
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  exact hbound n c hc ε hε hεmax t ht f a hf hmean ha0 (hmass.trans ha)

theorem explicit_encoded_interval_comparison :
    ∃ K : ℕ, 0 < K ∧ ∀ (m B : ℕ), 0 < m * B →
      ∀ (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      Pairwise (fun i j => (s i).Coprime (s j)) →
      ∀ (c : AC0Circuit (m * B)), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ (8458 : ℕ) ≤ (t : ℝ) →
        ∀ (a N : ℕ), 0 < N → ∀ M A : ℝ, 1 ≤ M → (∀ i, (s i : ℝ) ≤ M) →
          (M ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * ((m * B : ℕ) : ℝ) ^ t ≤ A →
          |uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
              c.indicator (integerBitSample s B a x)) - cubeAverage c.indicator| ≤
            3 * A / 2 + ε := by
  obtain ⟨K,hK,hbound⟩ := explicit_coefficient_comparison
  refine ⟨K,hK,?_⟩
  intro m B hn s _hpos hcop c hc ε hε hεmax t ht a N hN M A hM hs hA
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  have h := hbound (m * B) hn c hc ε hε hεmax t ht (integerBitDensity s B a N)
    (M ^ t / (N : ℝ)) A (integerBitDensity_nonneg s B a N)
    (integerBitDensity_mean s B a N hN) (by positivity)
    (integerBitDensity_low_coefficients s hcop a N hN M hM hs t) hA
  simpa only [integerBitDensity, sampleDensity_expectation] using h

theorem explicit_finite_residue_comparison :
    ∃ K : ℕ, 0 < K ∧ ∀ (m B : ℕ), 0 < m * B →
      ∀ (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      Pairwise (fun i j => (s i).Coprime (s j)) →
      ∀ (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n), c.depth ≤ 20 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log
          (((encodeResidueCircuit s B coord test c).size : ℝ) / ε)) ^ (8458 : ℕ) ≤ (t : ℝ) →
        ∀ (a N : ℕ), 0 < N → ∀ M A : ℝ, 1 ≤ M → (∀ i, (s i : ℝ) ≤ M) →
          (M ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * ((m * B : ℕ) : ℝ) ^ t ≤ A →
          |uniformAverage (fun x : Fin N =>
              eventIndicator (residueCircuitEvent s coord test c)
                (fun i => (a + x.val : ZMod (s i)))) -
            uniformAverage (eventIndicator (residueCircuitEvent s coord test c))| ≤
              2 * (∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ)) + 3 * A / 2 + ε := by
  obtain ⟨K,hK,hcompare⟩ := explicit_encoded_interval_comparison
  refine ⟨K,hK,?_⟩
  intro m B hn s _hpos hcop n coord test c hc ε hε hεmax t ht a N hN M A hM hs hA
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hdepth : (encodeResidueCircuit s B coord test c).depth ≤ 22 :=
    (encodeResidueCircuit_depth (B := B) s coord test c).trans (by omega)
  have hmiddle := hcompare m B hn s hcop (encodeResidueCircuit s B coord test c)
    hdepth ε hε hεmax t ht a N hN M A hM hs hA
  rw [encodeResidueCircuit_interval_average, encodeResidueCircuit_uniform_average] at hmiddle
  have hleft := decoder_event_error_averaged (B := B) s (residueCircuitEvent s coord test c)
    (fun x : Fin N => fun i => (a + x.val : ZMod (s i)))
  have hright := decoder_event_error_averaged (B := B) s (residueCircuitEvent s coord test c)
    (fun r : ∀ i, ZMod (s i) => r)
  let I := uniformAverage (fun x : Fin N =>
    eventIndicator (residueCircuitEvent s coord test c) (fun i => (a + x.val : ZMod (s i))))
  let J := uniformAverage (fun x : Fin N => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
    eventIndicator (residueCircuitEvent s coord test c)
      (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j))))
  let U := uniformAverage (fun r : ∀ i, ZMod (s i) =>
    uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator (residueCircuitEvent s coord test c)
        (decodedResidues s B (crtJitterBits s B r j))))
  let V := uniformAverage (eventIndicator (residueCircuitEvent s coord test c))
  change |I - J| ≤ _ at hleft
  change |J - U| ≤ _ at hmiddle
  change |V - U| ≤ _ at hright
  change |I - V| ≤ _
  have htriangle : |I - V| ≤ |I - J| + |J - U| + |U - V| := by
    calc
      _ = |(I - J) + (J - U) + (U - V)| := by congr 1 <;> ring
      _ ≤ _ := OAI.TwoPointCorrelations.abs_add_three (I - J) (J - U) (U - V)
  rw [abs_sub_comm] at hright
  linarith

#print axioms explicit_finite_residue_comparison
end ReflectedLiouville
