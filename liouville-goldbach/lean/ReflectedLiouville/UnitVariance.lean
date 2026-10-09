import ReflectedLiouville.VarianceTransfer
import ReflectedLiouville.ShortSumIntegrability
import ReflectedLiouville.CharacterMinimizer

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

/-- The reviewed admissibility premises, to be derived from the manuscript's
    buffered Q_* parameters. This structure is not a new analytic hypothesis. -/
structure KMTRange (X H Q ε : ℝ) (q : ℕ) [NeZero q] : Prop where
  length_le : H ≤ X
  length_ge : 10 ≤ H
  Q_ge : 1 ≤ Q
  Q_le : Q ≤ H / 10
  ε_pos : 0 < ε
  ε_lt : ε < 1
  accuracy : Real.rpow (Real.log (H / Q)) (-1 / 200) ≤ Real.rpow ε (11 / 10)
  inner_accuracy : Real.rpow (Real.log X) (-1 / 50) < Real.rpow ε (33 / 5)
  M_lower : 1 / Real.log (Real.log X) ≤ Real.rpow ε (-88)
  M_upper : Real.rpow ε (-88) ≤ Real.rpow (Real.rpow ε (33 / 5)) 20 * Real.log X /
    (20 * Real.log (Real.log X))
  log_cap : Real.log (H / Q) ≤ Real.rpow (Real.log X) (2 / 5)
  q_le : (q : ℝ) ≤ Q
  q_buffer : (q : ℝ) * Real.rpow (H / Q) (Real.rpow ε (11 / 10) / 100) ≤ Q
  good : KMTGoodModulus X (Real.rpow ε (33 / 5)) (Real.rpow ε (-88)) q
  typical : KMTTypical q (Real.rpow (H / Q) (ε ^ 2))

noncomputable def unitResidueVariance (q : ℕ) [NeZero q] (X H : ℝ) : ℝ :=
  ∫ x in X..2 * X, ∑ a : (ZMod q)ˣ, ‖shortProgressionSum liouville q (a : ZMod q) x H‖ ^ 2

lemma unit_short_squares_intervalIntegrable (q : ℕ) [NeZero q] (X H : ℝ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) (w : (ZMod q)ˣ → ℂ) :
    IntervalIntegrable (fun x : ℝ => ∑ a : (ZMod q)ˣ,
      ‖shortProgressionSum liouville q (a : ZMod q) x H - w a‖ ^ 2) volume X (2 * X) := by
  have heq : (∑ a : (ZMod q)ˣ, fun x : ℝ =>
      ‖shortProgressionSum liouville q (a : ZMod q) x H - w a‖ ^ 2) =
      (fun x : ℝ => ∑ a : (ZMod q)ˣ,
        ‖shortProgressionSum liouville q (a : ZMod q) x H - w a‖ ^ 2) := by
    funext x
    simp only [Finset.sum_apply]
  rw [← heq]
  apply IntervalIntegrable.sum Finset.univ
  intro a ha
  exact liouville_short_square_intervalIntegrable q (a : ZMod q) X H hX hH (w a)

lemma kmtRealVariance_intervalIntegrable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    IntervalIntegrable (fun x : ℝ => ∑ a : (ZMod q)ˣ,
      ‖shortProgressionSum liouville q (a : ZMod q) x H -
        kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ^ 2) volume X (2 * X) :=
  unit_short_squares_intervalIntegrable q X H hX hH _

/-- KMT unit variance plus the explicitly bounded character main-term energy.
    h_tail is the derived target supplied by the realmean module, not a published
    input. All reviewed KMT premises remain visible in KMTRange. -/
theorem kmt_unit_variance_uncentered
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (h_tail : RealCharacterPrimeTailBound) :
    ∃ C D X₀ : ℝ, 0 < C ∧ 0 < D ∧ 10 ≤ X₀ ∧ ∀ X H Q ε : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) [NeZero q], KMTRange X H Q ε q →
        unitResidueVariance q X H ≤
          2 * C * ε * (q.totient : ℝ) * X * (H / q) ^ 2 +
          2 * D ^ 2 * X * H ^ 2 / ((q.totient : ℝ) * Real.rpow (Real.log X) (1 / 20)) := by
  obtain ⟨C, hC, X₁, hX₁, hvariance⟩ := h_KMT.realProgressionVariance
  obtain ⟨D, X₂, hD, hX₂, hmain⟩ := kmt_main_term_square_sum h_MRT h_tail
  refine ⟨C, D, max X₁ X₂, hC, hD, hX₁.trans (le_max_left _ _), ?_⟩
  intro X H Q ε hX q inst hrange
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := by linarith
  have hH : 0 ≤ H := by linarith [hrange.length_ge]
  have hqX : (q : ℝ) ≤ X := hrange.good.2.1
  obtain ⟨χ, t, hmin⟩ := exists_minimizing_character q liouville X hXp.le
  have hv := hvariance X H Q ε hXX₁ hrange.length_le hrange.length_ge hrange.Q_ge hrange.Q_le
    hrange.ε_pos hrange.ε_lt hrange.accuracy hrange.inner_accuracy hrange.M_lower hrange.M_upper
    hrange.log_cap q hrange.q_le hrange.q_buffer hrange.good hrange.typical liouville
    liouville_realMultiplicative χ t hmin
  have hzero : IntervalIntegrable (fun x : ℝ => ∑ a : (ZMod q)ˣ,
      ‖shortProgressionSum liouville q (a : ZMod q) x H‖ ^ 2) volume X (2 * X) := by
    simpa only [sub_zero] using unit_short_squares_intervalIntegrable q X H hXp.le hH (fun _ => 0)
  have hcenter := kmtRealVariance_intervalIntegrable q χ X H hXp.le hH
  have huncenter := integrated_square_sum_uncenter
    (fun (x : ℝ) (a : (ZMod q)ˣ) => shortProgressionSum liouville q (a : ZMod q) x H)
    (fun a : (ZMod q)ˣ => kmtRealMainTerm liouville χ X H (a : ZMod q)) X hXp.le hzero hcenter
  have hm := hmain X H hXX₂ hH q hqX χ
  have hmainEnergy := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * X)
  change unitResidueVariance q X H ≤ 2 * kmtRealVariance liouville χ X H +
    2 * X * (∑ a : (ZMod q)ˣ, ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ^ 2) at huncenter
  have hmainEnergy' :
      2 * X * (∑ a : (ZMod q)ˣ, ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ^ 2) ≤
      2 * D ^ 2 * X * H ^ 2 / ((q.totient : ℝ) * Real.rpow (Real.log X) (1 / 20)) := by
    convert hmainEnergy using 1 <;> ring
  have hvariance' := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)
  have hvariance'' : 2 * kmtRealVariance liouville χ X H ≤
      2 * C * ε * (q.totient : ℝ) * X * (H / q) ^ 2 := by
    convert hvariance' using 1 <;> ring
  exact huncenter.trans (add_le_add hvariance'' hmainEnergy')

#print axioms kmt_unit_variance_uncentered

end ReflectedLiouville
