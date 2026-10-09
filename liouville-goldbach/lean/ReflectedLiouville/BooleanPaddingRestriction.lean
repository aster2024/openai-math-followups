import ReflectedLiouville.SelectedPrimeSets
import ReflectedLiouville.BooleanPaddingCost

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma selected_padding_average_reindex (Q R : Finset ℕ) (hQR : Q ⊆ R)
    (hR : ∀ p ∈ R, 2 ≤ p) (F : Finset ℕ → ℝ) :
    (FiniteLaw.independent (fun p : keptPrimeCoordinates Q R =>
      paddingOriginalPrimeLaw p.val.val (hR _ p.val.property))).average
        (fun b => F (coordinateActivePrimes (keptPrimeCoordinates Q R) b)) =
      (paddingOriginalLaw Q (fun p hp => hR p (hQR hp))).average
        (fun b => F (paddingAvailablePrimes Q b)) := by
  rw [FiniteLaw.independent_average_reindex (keptPrimeEquiv Q R hQR)]
  have hf : (fun b : Q → Bool => F (coordinateActivePrimes (keptPrimeCoordinates Q R)
      (fun p => b ((keptPrimeEquiv Q R hQR).symm p)))) =
      (fun b => F (paddingAvailablePrimes Q b)) := by
    funext b
    rw [coordinateActivePrimes_reindex]
  rw [hf]
  rfl

/-- Exact normalized shrinking-pool inequality for the actual bin rejection
    observable. The same D is retained on both sides. -/
theorem boolean_padding_cost_shrinking (Q R D : Finset ℕ) (hQR : Q ⊆ R)
    (hR : ∀ p ∈ R, 2 ≤ p) (bins : Finset ℤ) (η c L K : ℝ) :
    (paddingOriginalLaw Q (fun p hp => hR p (hQR hp))).average
      (fun b => activePaddingRejected D bins η c L K (paddingAvailablePrimes Q b)) /
        paddingTiltNormalizer Q ≤
      ((paddingOriginalLaw R hR).average
        (fun b => activePaddingRejected D bins η c L K (paddingAvailablePrimes R b)) /
          paddingTiltNormalizer R) *
        (∏ p ∈ R \ Q, ((p : ℝ) + 4) / ((p : ℝ) - 1)) := by
  let S := keptPrimeCoordinates Q R
  have hc := normalized_padding_conditioning (fun p : R => p.val) (fun p => hR p p.property) S
    (fun b => activePaddingRejected D bins η c L K (paddingAvailablePrimes R b))
    (fun b => activePaddingRejected D bins η c L K (coordinateActivePrimes S b))
    (fun b => activePaddingRejected_nonneg _ _ _ _ _ _ _)
    (by intro b; rw [paddingAvailablePrimes_join_false])
  change
    (FiniteLaw.independent (fun p : S => paddingOriginalPrimeLaw p.val.val (hR _ p.val.property))).average
      (fun b => activePaddingRejected D bins η c L K (coordinateActivePrimes S b)) /
      (∏ p : S, (1 + 4 / (p.val.val : ℝ))) ≤ _ at hc
  rw [selected_padding_average_reindex Q R hQR hR,
    kept_prime_normalizer Q R hQR] at hc
  have hprod := removed_prime_product Q R (fun p => ((p : ℝ) + 4) / ((p : ℝ) - 1))
  rw [hprod] at hc
  exact hc

#print axioms boolean_padding_cost_shrinking

end ReflectedLiouville
