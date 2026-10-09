import ReflectedLiouville.ReflectionPoolBounds
import OAI.NumberTheory.TwoPoint.Bounds.UniformResidueTranslation

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma prohibited_site_probability_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (site : ℤ) :
    (data.residueLaw B hB).probability (fun x =>
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)) =
      (data.residueLaw B hB).probability (data.deletedEvent s B) := by
  unfold FiniteLaw.probability
  have he := data.residue_average_translate hB
    (fun n => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then (1 : ℝ) else 0)
    (by
      intro n m hnm
      simp only [data.prohibitedSite_congr hB s n m hnm]) site
  rw [he]
  apply congrArg (data.residueLaw B hB).average
  funext x
  have hi := data.deletedEvent_iff s B x (data.residueOrigin x) (data.residueOrigin_spec x)
  simp only [hi]

/-- The prohibited density is proved uniformly in N; the multiplier is among
    the objects quantified after the library's threshold. -/
theorem reflection_prohibited_density (a W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      ∀ (hL : 1 ≤ L) (η : ℝ),
        let data := reflectionPrimeFamily N W δ L η hL (by linarith)
        ∀ hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊,
          ∀ site : ℤ, (data.residueLaw ⌊Real.exp L⌋₊ hB).probability (fun x =>
            ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs)
              (data.residueOrigin x + site)) ≤
                Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  have hs := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_reflection_pool_range a W δ hW hδ (by linarith),
    eventually_prohibited_density 101 (by norm_num), hs] with L hpool hdensity hsL
  intro N inst hN hL η
  dsimp only
  intro hB site
  let J := reflectionBandCount W δ L
  let M := ⌊100 * Real.log L⌋₊
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let H := ⌈Real.exp (L ^ (1 - δ))⌉₊
  let B := ⌊Real.exp L⌋₊
  have hrange := hpool N hN hL η
  have hspos : 1 ≤ s := Nat.le_floor (by simpa only [Nat.cast_one] using hsL)
  have hsupper : (s : ℝ) ≤ L ^ (1 / 10 : ℝ) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have hslots : ((s * (J + M) : ℕ) : ℝ) ≤ 101 * s * Real.log L := by
    have hb := mul_le_mul_of_nonneg_left hrange.slots (show (0 : ℝ) ≤ s by positivity)
    push_cast at hb ⊢
    nlinarith only [hb]
  have hH : Real.exp (L ^ (199 / 200 : ℝ)) ≤ (H : ℝ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL (by linarith : (199 / 200 : ℝ) ≤ 1 - δ)
    exact (Real.exp_le_exp.mpr hp).trans (Nat.le_ceil _)
  have hprob := hdensity N s J M B H data hB hspos hsupper hslots
    hrange.centerLower hrange.centerUpper hrange.paddingUpper hH
    (prime_trace_endpoints L hL).1 (prime_trace_endpoints L hL).2.1 hrange.centerPrimeLower
  rw [prohibited_site_probability_translate data hB s site]
  exact hprob

#print axioms reflection_prohibited_density

end ReflectedLiouville
