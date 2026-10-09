import ReflectedLiouville.CenterBandHoles
import ReflectedLiouville.UniformPaddingMass
import OAI.NumberTheory.TwoPoint.Bounds.PrimePairCatalog

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionBandCount (W δ L : ℝ) : ℕ :=
  ⌊δ * Real.log L / (6 * W)⌋₊

lemma reflectionBandCount_mul_bound (W δ L : ℝ) (hW : 0 < W) (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    (reflectionBandCount W δ L : ℝ) * (6 * W) ≤ δ * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (reflectionBandCount W δ L : ℝ) ≤ δ * Real.log L / (6 * W) :=
    Nat.floor_le (by positivity)
  exact (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj

lemma reflection_prime_endpoint (W δ L : ℝ) (hW : 0 < W) (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    primeSupplyEndpoint (L ^ (1 - δ)) W (reflectionBandCount W δ L) ≤ L := by
  have hLp : 0 < L := by linarith
  have hj := reflectionBandCount_mul_bound W δ L hW hδ hL
  have he := Real.exp_le_exp.mpr hj
  have hexp : Real.exp (δ * Real.log L) = L ^ δ := by
    rw [Real.rpow_def_of_pos hLp]
    congr 1
    ring
  rw [hexp] at he
  unfold primeSupplyEndpoint
  calc
    _ ≤ L ^ (1 - δ) * L ^ δ := mul_le_mul_of_nonneg_left (by simpa only [mul_comm, mul_left_comm, mul_assoc] using he) (by positivity)
    _ = L := by rw [← Real.rpow_add hLp]; norm_num

lemma eventually_reflectionBandCount_positive (W δ : ℝ) (hW : 0 < W) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ reflectionBandCount W δ L := by
  have hc : 0 < δ / (6 * W) := by positivity
  have hlim : Tendsto (fun L : ℝ => (δ / (6 * W)) * Real.log L) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hc
  filter_upwards [hlim.eventually (eventually_ge_atTop (1 : ℝ))] with L hL
  apply Nat.le_floor
  simpa only [Nat.cast_one, div_mul_eq_mul_div] using hL

lemma paddingPrimeSupply_subset_empty (E : Finset ℕ) (L : ℝ) :
    paddingPrimeSupply E L ⊆ paddingPrimeSupply ∅ L := by
  intro p hp
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp).1, by simp⟩

lemma centered_tuple_coprime_total (N : ℕ) [NeZero N] (A W : ℝ) (J : ℕ)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (centeredPrimeBands N.primeFactors A W J)) :
    Nat.Coprime d N := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
  apply Nat.coprime_prod_left_iff.mpr
  intro j hj
  have hp := centeredPrimeSupply_mem (x j).property
  apply hp.1.coprime_iff_not_dvd.mpr
  intro hdiv
  exact hp.2.2.1 (Nat.mem_primeFactors.mpr ⟨hp.1, hdiv, NeZero.ne N⟩)

/-- All support geometry is proved for the actual changing exclusion set. -/
theorem reflection_tuple_geometry (N : ℕ) [NeZero N] (W δ L : ℝ)
    (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    let J := reflectionBandCount W δ L
    let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
    (∀ d ∈ primeTupleDivisors P,
      0 < d ∧ Real.log (d : ℝ) ≤ 2 * L ∧ Nat.Coprime d N ∧
        Squarefree d ∧ d.primeFactors.card = J) ∧
      (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) = ∏ j, primeHarmonicMass (P j) := by
  dsimp only
  let J := reflectionBandCount W δ L
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  have hA : 0 < L ^ (1 - δ) := Real.rpow_pos_of_pos (by linarith) _
  have hWp : 0 < W := by linarith
  have hend := reflection_prime_endpoint W δ L hWp hδ hL
  have hp := centeredPrimeBands_prime N.primeFactors (L ^ (1 - δ)) W J
  have hd := centeredPrimeBands_disjoint N.primeFactors (L ^ (1 - δ)) W J hA.le hWp.le
  constructor
  · intro d hmem
    obtain ⟨hpos, hlog⟩ := centeredPrimeTuple_log_bound hA hW hend hmem
    obtain ⟨hsq, hcard, hpool⟩ := primeTupleDivisors_arithmetic P hp hd hmem
    exact ⟨hpos, hlog, centered_tuple_coprime_total N _ _ J hmem, hsq, hcard⟩
  · have hm := primeTupleDivisors_mass P hp hd
    simpa only [primeHarmonicMass_eq_sum] using hm

/-- Lemma mass for the constructed tuple and reduced padding pools. -/
theorem retained_padding_mass (W δ a : ℝ) (hW : 1 ≤ W) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      let J := reflectionBandCount W δ L
      let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
      let Q := paddingPrimeSupply N.primeFactors L
      ∀ η : ℝ, 0 < η →
        W ^ J ≤ (∏ j, primeHarmonicMass (P j)) ∧
          (1 / 2 : ℝ) * paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) ≤
            totalPaddingBinMass (primeTupleDivisors P) Q L η := by
  filter_upwards [eventually_center_band_masses a (1 - δ) W (by linarith) (by linarith),
    uniform_retained_padding_mass, eventually_ge_atTop (1 : ℝ)] with L hmass hretain hL
  intro N inst hN
  dsimp only
  intro η hη
  let J := reflectionBandCount W δ L
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  let Q := paddingPrimeSupply N.primeFactors L
  have hgeom := reflection_tuple_geometry N W δ L hW hδ.le hL
  change (∀ d ∈ primeTupleDivisors P, _) ∧ _ at hgeom
  constructor
  · calc
      W ^ J = ∏ _j : Fin J, W := by simp
      _ ≤ ∏ j, primeHarmonicMass (P j) := Finset.prod_le_prod₀
        (fun _ _ => by linarith) (fun j _ => (hmass N hN j.val).1)
  · have hr := hretain (primeTupleDivisors P) Q η (paddingPrimeSupply_subset_empty _ _) hη
      (fun d hd => ⟨(hgeom.1 d hd).1, (hgeom.1 d hd).2.1⟩)
    rwa [hgeom.2] at hr

#print axioms retained_padding_mass

end ReflectedLiouville
