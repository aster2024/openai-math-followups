import ReflectedLiouville.ShortSums
import ReflectedLiouville.RealCutoff
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma scaled_residue_congruence (u d m b : ℕ) (hu : 0 < u) :
    (((u * m : ℕ) : ZMod (u * d)) = ((u * b : ℕ) : ZMod (u * d))) ↔
      ((m : ZMod d) = (b : ZMod d)) := by
  rw [ZMod.natCast_eq_natCast_iff', ZMod.natCast_eq_natCast_iff',
    Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  constructor
  · exact Nat.eq_of_mul_eq_mul_left hu
  · intro h
    rw [h]

lemma residue_class_implies_common_divisor (u d n b : ℕ)
    (hclass : (n : ZMod (u * d)) = ((u * b : ℕ) : ZMod (u * d))) : u ∣ n := by
  have hmod := (ZMod.natCast_eq_natCast_iff n (u * b) (u * d)).mp hclass
  have hmodu := Nat.ModEq.of_dvd (dvd_mul_right u d) hmod
  change n % u = (u * b) % u at hmodu
  exact Nat.dvd_of_mod_eq_zero (by simpa using hmodu)

/-- The exact prefix scaling for one gcd stratum, before integration.
    Every positive common factor u contributes its true Liouville sign. -/
lemma progressionPrefix_scaling (u d b B : ℕ) (hu : 0 < u) :
    progressionPrefix liouville (u * d) ((u * b : ℕ) : ZMod (u * d)) B =
      liouville u * progressionPrefix liouville d (b : ZMod d) (B / u) := by
  classical
  unfold progressionPrefix
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun m _ => u * m)
  · intro m hm
    obtain ⟨hm, hclass⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmB⟩ := Finset.mem_Icc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, (scaled_residue_congruence u d m b hu).mpr hclass⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos hu (by omega))
    · have h := (Nat.le_div_iff_mul_le hu).mp hmB
      simpa only [Nat.mul_comm] using h
  · intro m hm n hn hmn
    exact Nat.eq_of_mul_eq_mul_left hu hmn
  · intro n hn
    obtain ⟨hn, hclass⟩ := Finset.mem_filter.mp hn
    obtain ⟨m, hm⟩ := residue_class_implies_common_divisor u d n b hclass
    have hnI := Finset.mem_Icc.mp hn
    rw [hm] at hnI hclass
    refine ⟨m, ?_, hm.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, (scaled_residue_congruence u d m b hu).mp hclass⟩
    apply (Nat.le_div_iff_mul_le hu).mpr
    simpa only [Nat.mul_comm] using hnI.2
  · intro m hm
    exact (OAI.TwoPointCorrelations.liouville_mul u m).symm

lemma shortProgressionSum_scaling (u d b : ℕ) (hu : 0 < u) (x H : ℝ) (hH : 0 ≤ H) :
    shortProgressionSum liouville (u * d) ((u * b : ℕ) : ZMod (u * d)) x H =
      liouville u * shortProgressionSum liouville d (b : ZMod d) (x / u) (H / u) := by
  have hupos : (0 : ℝ) < u := by exact_mod_cast hu
  rw [shortProgressionSum_eq_prefix_difference _ _ _ H hH,
    shortProgressionSum_eq_prefix_difference _ _ _ (H / u) (div_nonneg hH hupos.le),
    progressionPrefix_scaling u d b _ hu, progressionPrefix_scaling u d b _ hu]
  rw [floor_div_natCast (x + H) u hu.ne', floor_div_natCast x u hu.ne', ← add_div]
  ring

#print axioms progressionPrefix_scaling
#print axioms shortProgressionSum_scaling

end ReflectedLiouville
