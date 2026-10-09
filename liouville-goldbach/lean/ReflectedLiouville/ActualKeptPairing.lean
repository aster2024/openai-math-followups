import ReflectedLiouville.BinFrameGeometry

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

theorem actual_kept_pairing (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 2 ≤ L) (hW : 0 ≤ W) (hη : 0 < η) (hηsmall : η ≤ 1/2)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    let J := reflectionBandCount W δ L
    let data := reflectionPrimeFamily N W δ L η (by linarith) hW
    let P := centeredPrimeBands N.primeFactors (L ^ (1-δ)) W J
    let T := reflectionBinCutoff N η j
    let U := Real.exp η * T
    let MB := ⌈Real.exp (103*L)⌉₊
    let site := fun i : Fin MB => (i.val : ℤ) - (MB/2 : ℕ)
    (∑ r : Fin N, inner ℂ
      (sourceTestVector data.Q T L (fun i => (N : ℤ)*site i + ((r.val+1 : ℕ) : ℤ)))
      (physicalReflectionCompression data P site ((r.val+1 : ℕ) : ℤ) L W
        (binPairEligible data.pairs η j)
        (targetTestVector data.Q U L (fun i => (N : ℤ)*site i + ((r.val+1 : ℕ) : ℤ))))) =
      ((L*T*keptCenteredBinForm data L W η j : ℝ) : ℂ) := by
  dsimp only
  have hLone : 1 ≤ L := by linarith
  let data := reflectionPrimeFamily N W δ L η hLone hW
  have hA : 0 ≤ L ^ (1-δ) := Real.rpow_nonneg (by linarith) _
  have hf := reflected_bin_frame_geometry N (NeZero.pos N) L η hL hη hηsmall j hj
  dsimp only at hf
  exact kept_full_pairing data _
    (centeredPrimeBands_prime N.primeFactors (L ^ (1-δ)) W _)
    (centeredPrimeBands_disjoint N.primeFactors (L ^ (1-δ)) W _ hA hW)
    (reflection_band_union N W δ L η hLone hW)
    (reflection_pair_supply_subset N W δ L η hLone hW)
    L W η j _ (NeZero.pos N) hf.2.2.2.2.2 hf.2.2.2.1 hf.2.2.2.2.1
    (fun dq hdq hbin => bin_pair_physical_step_upper data η hη j dq hdq hbin)

#print axioms actual_kept_pairing
end ReflectedLiouville
