import ReflectedLiouville.CompressionConstant
import ReflectedLiouville.BinnedDilation
import ReflectedLiouville.CRTInverse

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def binPairEligible (I : Finset (ℕ × ℕ)) (η : ℝ) (j : ℤ) (d q : ℕ) : Prop :=
  (d, q) ∈ I ∧ reflectionPairBin η (d, q) = j

lemma coprime_of_pool_inverse (N ell p : ℕ) (hinv : (N : ZMod p) * (ell : ZMod p) = 1) :
    Nat.Coprime ell p := by
  have hu : IsUnit (ell : ZMod p) := by
    refine ⟨⟨(ell : ZMod p), (N : ZMod p), ?_, hinv⟩, rfl⟩
    simpa only [mul_comm] using hinv
  exact (ZMod.isUnit_iff_coprime ell p).mp hu

/-- Concrete reflection supplies admit one large CRT inverse for every bin,
    and each bin has at most exp(-2 floor L) exceptional residue origins. This
    is the ordinary integer-site compression that cross-support pairing uses. -/
theorem reflected_compression_bound (W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) :
    ∃ Af : ℕ, 1000 ≤ Af ∧ ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ Af / 2) ≤ (N : ℝ) →
        ∀ hL : 1 ≤ L,
          let J := reflectionBandCount W δ L
          let η := Real.exp (-(J : ℝ))
          let physical := reflectionPrimeFamily N W δ L η hL (by linarith)
          let data := quotientPrimeFamily physical
          let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
          let MB := ⌈Real.exp (103 * L)⌉₊
          ∃ ell : ℕ, MB < ell ∧
            (∀ p : ↥(data.P ∪ data.Q), (N : ZMod p.val) * (ell : ZMod p.val) = 1) ∧
            ∀ j : ℤ, uniformAverage (fun r : Fin N => if
              Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J <
                ‖reflectionCompressedGraph data P L W (binPairEligible data.pairs η j) (fun _ _ _ => True)
                  (((ell - MB / 2 + ell * r.val : ℕ) : ℤ))‖ then (1 : ℝ) else 0) ≤
                    Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨Af, hAf, hc⟩ := reflection_affine_compression W hW
  refine ⟨Af, hAf, ?_⟩
  intro a
  filter_upwards [hc, eventually_reflection_trace_range a W δ hW hδ hδsmall] with L hcompress htrace
  intro N inst hNlog hNlength hL
  dsimp only
  let J := reflectionBandCount W δ L
  let η := Real.exp (-(J : ℝ))
  let physical := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let data := quotientPrimeFamily physical
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  let MB := ⌈Real.exp (103 * L)⌉₊
  have hη : 0 < η := Real.exp_pos _
  have hη₁ : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  have hrange := htrace N hNlog hL η hη hη₁
  obtain ⟨ell, hlarge, hinv⟩ := reflection_CRT_inverse N W δ L η hL (by linarith) MB
  have hl : ∀ p ∈ data.P ∪ data.Q, ell.Coprime p := by
    intro p hp
    exact coprime_of_pool_inverse N ell p (hinv ⟨p, hp⟩)
  refine ⟨ell, hlarge, hinv, ?_⟩
  intro j
  have hb := hcompress J ⌊100 * Real.log L⌋₊ data P (1 - δ) hrange hL hrange.pool.residueBound
    (binPairEligible data.pairs η j) (fun d q h => h.1) (fun _ _ _ => True) (by simp)
    (ell - MB / 2) ell N hl hNlength
  have hscale := compression_scale_le_paper J W hrange.pool.oneJ
  apply le_trans _ hb
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro r hr
  by_cases hp : Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J <
      ‖reflectionCompressedGraph data P L W (binPairEligible data.pairs η j) (fun _ _ _ => True)
        (((ell - MB / 2 + ell * r.val : ℕ) : ℤ))‖
  · have hlow := lt_of_le_of_lt hscale hp
    rw [ite_eq_left hp, ite_eq_left hlow]
  · rw [ite_eq_right hp]
    split_ifs <;> norm_num

#print axioms reflected_compression_bound

end ReflectedLiouville
