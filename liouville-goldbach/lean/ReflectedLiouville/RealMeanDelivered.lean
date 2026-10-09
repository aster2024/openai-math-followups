import ReflectedLiouville.PrimeTailTransfer
import RealCharacterTail.Main

set_option autoImplicit false

namespace ReflectedLiouville

/-- Discharge of the exact derived target by the independently delivered,
    hypothesis-free realmean module. No published premise is added. -/
theorem real_character_prime_tail_derived : RealCharacterPrimeTailBound := by
  exact RealCharacterTail.real_character_prime_tail

theorem real_character_mean_bound (h_MRT : MRTRealTwistRepulsionInput) : RealCharacterMeanBound :=
  real_character_mean_of_prime_tail h_MRT real_character_prime_tail_derived

#print axioms real_character_prime_tail_derived
#print axioms real_character_mean_bound

end ReflectedLiouville
