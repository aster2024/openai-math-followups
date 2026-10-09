import ReflectedLiouville.PhysicalSparseBound
import ReflectedLiouville.GoodBadBilinear

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Good/bad-origin combination for the concrete physical kept operator.
    The subsequent exact raw-form pairing remains a separate finite identity. -/
theorem kept_operator_bilinear_bound (W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) :
    ∃ Af : ℕ, 1000 ≤ Af ∧ ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ Af / 2) ≤ (N : ℝ) →
        ∀ (hL : 1 ≤ L) (T U : ℝ), (N : ℝ) ≤ T → (N : ℝ) ≤ U → U ≤ 3 * T →
          let J := reflectionBandCount W δ L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W δ L η hL (by linarith)
          let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
          let MB := ⌈Real.exp (103 * L)⌉₊
          let site := fun i : Fin MB => (i.val : ℤ) - (MB / 2 : ℕ)
          let B := Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J
          ∀ j : ℤ,
            (∑ r : Fin N, ‖inner ℂ
              (sourceTestVector data.Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)))
              (physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W (binPairEligible data.pairs η j)
                (targetTestVector data.Q U L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))))‖) ≤
              4 * paddingTiltNormalizer data.Q * T * B +
                (T / N + 1) * (2 * Real.exp (4 * J) * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L) *
                  Real.exp (-(2 * ⌊L⌋₊ : ℕ)) * N := by
  obtain ⟨Ac, hAc, hcomp⟩ := reflected_compression_bound W δ hW hδ hδsmall
  obtain ⟨Av, hAv, henergy⟩ := reflected_test_energy_bound
  refine ⟨Ac + Av, by omega, ?_⟩
  intro a
  filter_upwards [hcomp a, henergy, eventually_reflection_pool_range a W δ hW hδ (by linarith)]
    with L hcompress hnorm hpool
  intro N inst hNlog hlength hL T U hNT hNU hUT
  dsimp only
  let J := reflectionBandCount W δ L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  let MB := ⌈Real.exp (103 * L)⌉₊
  let site := fun i : Fin MB => (i.val : ℤ) - (MB / 2 : ℕ)
  let B := Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J
  let D := (T / N + 1) * (2 * Real.exp (4 * J) * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)
  have hn : 0 < N := NeZero.pos N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hT : 0 < T := hNr.trans_le hNT
  have hNc : Real.exp (L ^ Ac / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (pow_le_pow_right₀ hL (Nat.le_add_right Ac Av)) (by norm_num))).trans hlength
  have hNv : Real.exp (L ^ Av / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (pow_le_pow_right₀ hL (Nat.le_add_left Av Ac)) (by norm_num))).trans hlength
  have hrange := hpool N hNlog hL η
  obtain ⟨ell, hlarge, hinv, htail⟩ := hcompress N hNlog hNc hL
  have hsite : Function.Injective site := by
    intro i j he
    apply Fin.ext
    dsimp only [site] at he
    omega
  have hQupper : ∀ p ∈ data.Q, (p : ℝ) ≤ Real.exp L := by
    intro p hp
    have hpb : p ≤ ⌊Real.exp L⌋₊ := hrange.residueBound p (Finset.mem_union_right _ hp)
    exact (show (p : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) by exact_mod_cast hpb).trans (Nat.floor_le (Real.exp_pos _).le)
  have hE := hnorm data.Q data.primeQ hQupper N T U hn hNT hNU hUT hNv (Fin MB) site hsite
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro j
  let A := fun r : Fin N => physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W
    (binPairEligible data.pairs η j)
  let f := fun r : Fin N => sourceTestVector data.Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))
  let g := fun r : Fin N => targetTestVector data.Q U L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))
  have hEllOff : MB / 2 ≤ ell := by have := Nat.div_le_self MB 2; omega
  have hOp (r : Fin N) : A r =
      reflectionCompressedGraph (quotientPrimeFamily data) P L W (binPairEligible data.pairs η j) (fun _ _ _ => True)
        (((ell - MB / 2 + ell * r.val : ℕ) : ℤ)) := by
    have ho := physical_compression_eq_block data hrange.residueBound hn P hrange.bandPrimes
      hrange.bandDisjoint hrange.bandSubset
      (fun d q hdq => reflection_pair_coprime_total N W δ L η hL (by linarith) d q hdq)
      ell (MB / 2) hinv ((r.val + 1 : ℕ) : ℤ) L W (binPairEligible data.pairs η j)
    have hc : ((ell - MB / 2 + ell * r.val : ℕ) : ℤ) =
        (ell : ℤ) * ((r.val + 1 : ℕ) : ℤ) - (MB / 2 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hEllOff]
      push_cast
      ring
    rw [← hc] at ho
    exact ho
  have hbadMean : uniformAverage (fun r : Fin N => if B < ‖A r‖ then (1 : ℝ) else 0) ≤
      Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
    have ht := htail j
    change uniformAverage (fun r : Fin N => if B < ‖A r‖ then (1 : ℝ) else 0) ≤ _
    simp only [hOp]
    convert ht using 1
    congr 1
  have hcount : (∑ r : Fin N, if B < ‖A r‖ then (1 : ℝ) else 0) ≤
      Real.exp (-(2 * ⌊L⌋₊ : ℕ)) * N := by
    simp only [uniformAverage, Fintype.card_fin] at hbadMean
    exact (div_le_iff₀ hNr).mp hbadMean
  have hbad : ∀ r : Fin N, B < ‖A r‖ → ‖inner ℂ (f r) (A r (g r))‖ ≤ D := by
    intro r hbad
    have hr : 1 ≤ ((r.val + 1 : ℕ) : ℤ) ∧ ((r.val + 1 : ℕ) : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (show 1 ≤ r.val + 1 ∧ r.val + 1 ≤ N by have := r.isLt; omega)
    exact physical_reflected_sparse_bound data P hrange.bandPrimes hrange.bandDisjoint site hsite hn _ hr
      L W T U (by linarith) (by linarith) hT.le hrange.bandsUpper (binPairEligible data.pairs η j)
  have hb := finite_good_bad_bilinear A f g B D (8 * paddingTiltNormalizer data.Q * T)
    (Real.exp (-(2 * ⌊L⌋₊ : ℕ))) hB hD hE (by simpa only [Fintype.card_fin] using hcount) hbad
  change (∑ r : Fin N, ‖inner ℂ (f r) (A r (g r))‖) ≤
    4 * paddingTiltNormalizer data.Q * T * B + D * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) * N
  simp only [Fintype.card_fin] at hb
  convert hb using 1 <;> ring

#print axioms kept_operator_bilinear_bound

end ReflectedLiouville
