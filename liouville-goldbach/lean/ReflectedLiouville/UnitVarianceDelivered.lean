import ReflectedLiouville.VarianceAbsorption
import ReflectedLiouville.RealMeanDelivered

set_option autoImplicit false

namespace ReflectedLiouville

/-- The independently delivered realmean theorem discharges h_tail. Only the
    reviewed published KMT and MRT propositions remain as analytic inputs. -/
theorem unit_variance_of_reviewed_range
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧ ∀ X H Q : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) [NeZero q], 1 < H / q → H / q ≤ X →
        KMTRange X H Q ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) q →
        unitResidueVariance q X H ≤ C * ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) *
          (q.totient : ℝ) * X * (H / q) ^ 2 :=
  kmt_unit_variance_saved h_KMT h_MRT real_character_prime_tail_derived

#print axioms unit_variance_of_reviewed_range

end ReflectedLiouville
