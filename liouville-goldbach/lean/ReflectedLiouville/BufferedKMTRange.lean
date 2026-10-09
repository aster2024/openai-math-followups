import ReflectedLiouville.KMTRangeGeometry
import ReflectedLiouville.KMTTypicalCutoff
import ReflectedLiouville.TypicalityUniform
import ReflectedLiouville.UnitVarianceDelivered

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

/-- Every reviewed KMT range condition is derived from the actual manuscript
    buffer, including cap, q-buffer, typicality, and the 003 zero box. -/
theorem eventually_buffered_kmt_range (ν : ℝ) (hν : 0 < ν) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (H : ℝ),
      10 * (q : ℝ) ≤ H → H ≤ X → Real.exp ((Real.log X) ^ ν) ≤ H / q →
      let ε := (Real.log (H / q)) ^ (-1 / 1000 : ℝ)
      let ρ := ε ^ (11 / 10 : ℝ)
      KMTRange X H (kmtBufferedQ X H ρ q) ε q := by
  let θ := min (ν / 2) (1 / 5 : ℝ)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  filter_upwards [eventually_kmt_log_gains ν hν, eventually_kmt_inner_parameters,
    eventually_kmt_typical_log_cutoff ν hν, all_moduli_eventually_typical θ hθ,
    eventually_kmt_zero_box_width, eventually_ge_atTop (Real.exp 2)]
    with X hgains hinner htypcut htypical hwidth hX
  intro q inst H hH10 hHX hRlower
  dsimp only
  let S := Real.log (H / q)
  let T := Real.log X
  let ε := S ^ (-1 / 1000 : ℝ)
  let ρ := ε ^ (11 / 10 : ℝ)
  let Q : ℝ := kmtBufferedQ X H ρ q
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hH : 0 < H := by nlinarith
  have hR10 : 10 ≤ H / q := (le_div_iff₀ hq).mpr hH10
  have hR : 1 < H / q := by linarith
  have hRX : H / q ≤ X := by
    apply le_trans _ hHX
    exact (div_le_iff₀ hq).mpr (le_mul_of_one_le_right hH.le hq₁)
  have hqX : (q : ℝ) ≤ X := by nlinarith
  have hT2 : 2 ≤ T := by
    have h := Real.log_le_log (Real.exp_pos 2) hX
    simpa only [T, Real.log_exp] using h
  have hX₁ : 1 ≤ X := by
    have he : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    exact he.trans hX
  have hST : S ≤ T := Real.log_le_log (by positivity) hRX
  have hSν : T ^ ν ≤ S := by
    have h := Real.log_le_log (Real.exp_pos _) hRlower
    simpa only [Real.log_exp, S, T] using h
  obtain ⟨hS1, hmin30, hgainS, hgainT⟩ := hgains S hSν
  have hSpos : 0 < S := by linarith
  have hεp : 0 < ε := Real.rpow_pos_of_pos hSpos _
  have hε₁ : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg hS1 (by norm_num)
  have hρ : 0 ≤ ρ := Real.rpow_nonneg hεp.le _
  have hρ₁ : ρ ≤ 1 := Real.rpow_le_one hεp.le hε₁.le (by norm_num)
  have hqQ : (q : ℝ) ≤ Q := kmtBufferedQ_ge_modulus X H ρ q hR.le hρ
  have hQ : 0 < Q := hq.trans_le hqQ
  have hQ₁ : 1 ≤ Q := hq₁.trans hqQ
  have hQH : Q ≤ H / 10 := kmtBufferedQ_le_length_tenth X H ρ q hX₁ hH hR.le hρ hρ₁ hmin30
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hminLog : 3 * Real.log 2 ≤ min S (T ^ (2 / 5 : ℝ)) := by linarith
  have hlogHalf : min S (T ^ (2 / 5 : ℝ)) / 2 ≤ Real.log (H / Q) :=
    kmtBufferedQ_log_half X H ρ q hX₁ hH hR.le hρ hρ₁ hminLog
  have haccuracy := kmt_accuracy_of_log_lower S T (Real.log (H / Q)) hSpos
    (by linarith) hST hlogHalf hgainS hgainT
  obtain ⟨hinnerAccuracy, hMlower, hMupper⟩ := hinner S hS1 hST
  have hreviewed := kmtBufferedQ_reviewed_premises X H ρ q hH hR.le hρ
  have htypicalQ : KMTTypical q ((H / Q) ^ (ε ^ (2 : ℕ))) := by
    apply (htypical q hqX).mono_cutoff
    have hlogCut := htypcut S (Real.log (H / Q)) hSpos hST hSν hlogHalf
    rw [Real.rpow_def_of_pos (div_pos hH hQ)]
    apply Real.exp_le_exp.mpr
    simpa only [θ, ε, mul_comm] using hlogCut
  have hboxwidth : ε ^ (-88 : ℝ) * Real.log (Real.log X) / Real.log X < 1 / 8 := by
    simpa only [Real.rpow_eq_pow, ε, S] using hwidth (H / q) hR hRX
  have hgood : KMTGoodModulus X (ε ^ (33 / 5 : ℝ)) (ε ^ (-88 : ℝ)) q := by
    apply kmt_good_modulus_of_zero_box X _ _ q hqX
    · have hu : 0 ≤ ε ^ (33 / 5 : ℝ) := Real.rpow_nonneg hεp.le _
      have hexponent : 0 ≤ (ε ^ (33 / 5 : ℝ)) ^ (20 : ℝ) := Real.rpow_nonneg hu _
      exact Real.one_le_rpow hX₁ hexponent
    · exact kmt_box_left_of_width X (ε ^ (-88 : ℝ)) hboxwidth
  refine ⟨hHX, by nlinarith, hQ₁, hQH, hεp, hε₁, haccuracy,
    hinnerAccuracy, hMlower, hMupper, hreviewed.2, hqQ, hreviewed.1, hgood, htypicalQ⟩

#print axioms eventually_buffered_kmt_range

end ReflectedLiouville
