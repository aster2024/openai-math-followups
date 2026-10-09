import MRTRepulsion.LargePhase
import MRTRepulsion.Elementary
import ReflectedLiouville.ExplicitMain

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations ReflectedLiouville Filter

namespace MRTRepulsion

lemma loglog_nonneg {X : ℝ} (hX : 100 ≤ X) : 0 ≤ Real.log (Real.log X) := by
  have he : Real.exp 1 ≤ X := by linarith [Real.exp_one_lt_three]
  have hl := Real.log_le_log (Real.exp_pos 1) he
  simp only [Real.log_exp] at hl
  exact Real.log_nonneg hl

/-- Both parts of the original imported proposition, with one absolute
    positive constant. No definition is copied or changed. -/
theorem repulsion_input : ReflectedLiouville.MRTRealTwistRepulsionInput := by
  obtain ⟨B,hB,hphase⟩ := large_phase_lower
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hphase
  obtain ⟨S,hS,hsmall⟩ := small_phase_difference
  let A : ℝ := (max 100 N₀ : ℕ)+1
  let C : ℝ := Real.sqrt (B+1)+Real.sqrt S+Real.sqrt (Real.log (Real.log A))+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 100 ≤ A := by
    have hn : (100 : ℝ) ≤ (max 100 N₀ : ℕ) := by exact_mod_cast le_max_left 100 N₀
    dsimp [A]
    linarith only [hn]
  refine ⟨C,hC,?_⟩
  intro f hf X hX t
  have hD := squaredDistance_twist_nonneg f hf.2.1 t ⌊X⌋₊
  have hD₀ := squaredDistance_twist_nonneg f hf.2.1 0 ⌊X⌋₊
  have hCbig : Real.sqrt (B+1) ≤ C := by
    dsimp [C]
    linarith [Real.sqrt_nonneg S,Real.sqrt_nonneg (Real.log (Real.log A))]
  have hCsmall : Real.sqrt S ≤ C := by
    dsimp [C]
    linarith [Real.sqrt_nonneg (B+1),Real.sqrt_nonneg (Real.log (Real.log A))]
  constructor
  · intro htlow hthi
    by_cases hXA : A ≤ X
    · have hn : N₀ ≤ ⌊X⌋₊ := by
        apply (Nat.le_floor_iff (by linarith : 0 ≤ X)).mpr
        have hh : (N₀ : ℝ) ≤ (max 100 N₀ : ℕ) := by exact_mod_cast le_max_right 100 N₀
        dsimp [A] at hXA
        linarith only [hh,hXA]
      have h2low : 1 ≤ |2*t| := by rw [abs_mul]; norm_num; linarith
      have h2hi : |2*t| ≤ 6*(⌊X⌋₊ : ℝ) := by
        rw [abs_mul]
        norm_num
        have hscale := floor_scale hX
        nlinarith only [hthi,hscale,Nat.cast_nonneg (α := ℝ) ⌊X⌋₊]
      have hp := hN₀ ⌊X⌋₊ hn (2*t) h2low h2hi
      have hd := phaseSum_double_le f hf t ⌊X⌋₊
      have hfloor := loglog_floor hX
      have hb : Real.log (Real.log X)/16-(B+1) ≤
          squaredDistance f (modulusOneTwist t) ⌊X⌋₊ := by
        linarith only [hp,hd,hfloor,hB]
      have hh := large_sqrt_margin _ _ (B+1) (loglog_nonneg hX) hD (by linarith) hb
      linarith only [hh,hCbig]
    · have hXle : X ≤ A := le_of_not_ge hXA
      have hlog : Real.log X ≤ Real.log A := Real.log_le_log (by linarith) hXle
      have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
      have hroot := Real.sqrt_le_sqrt (Real.log_le_log hlogX hlog)
      have hCroot : Real.sqrt (Real.log (Real.log A)) ≤ C := by
        dsimp [C]
        linarith [Real.sqrt_nonneg (B+1),Real.sqrt_nonneg S]
      linarith [Real.sqrt_nonneg (Real.log (Real.log X)),Real.sqrt_nonneg
        (squaredDistance f (modulusOneTwist t) ⌊X⌋₊)]
  · intro ht
    have hp := hsmall ⌊X⌋₊ (floor_exp_one hX) t ht
    have ha := untwisted_distance_le f hf t ⌊X⌋₊
    have hb : squaredDistance f (modulusOneTwist 0) ⌊X⌋₊ ≤
        5*squaredDistance f (modulusOneTwist t) ⌊X⌋₊+S := by linarith only [hp,ha]
    have hh := small_sqrt_margin _ _ S hD₀ hD hS hb
    linarith only [hh,hCsmall]

end MRTRepulsion

theorem mrt_real_twist_repulsion : ReflectedLiouville.MRTRealTwistRepulsionInput :=
  MRTRepulsion.repulsion_input

theorem paper_theorem_1_1_one_hypothesis
    (h_KMT : ReflectedLiouville.KMTInput) : ReflectedLiouville.PaperMainStatement :=
  ReflectedLiouville.paper_theorem_1_1_explicit h_KMT mrt_real_twist_repulsion

#print axioms mrt_real_twist_repulsion
#print axioms paper_theorem_1_1_one_hypothesis
