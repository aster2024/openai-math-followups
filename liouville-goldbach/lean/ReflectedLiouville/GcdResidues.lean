import ReflectedLiouville.ProgressionScaling
import Mathlib.Data.Nat.Totient

set_option autoImplicit false

namespace ReflectedLiouville

abbrev ReducedResidues (d : ℕ) := {b : Fin d // b.val.Coprime d}
abbrev GcdResidueIndex (q : ℕ) := (u : ↥q.divisors) × ReducedResidues (q / u.val)

lemma divisor_positive (q : ℕ) (u : ↥q.divisors) : 0 < u.val :=
  Nat.pos_of_mem_divisors u.property

lemma divisor_mul_quotient (q : ℕ) (u : ↥q.divisors) : u.val * (q / u.val) = q :=
  Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors u.property)

lemma scaled_coprime_gcd (q : ℕ) (u : ↥q.divisors) (b : ReducedResidues (q / u.val)) :
    (u.val * b.val.val).gcd q = u.val := by
  conv_lhs => arg 2; rw [← divisor_mul_quotient q u]
  rw [Nat.gcd_mul_left, b.property.gcd_eq_one, Nat.mul_one]

def gcdResidueValue (q : ℕ) (i : GcdResidueIndex q) : Fin q :=
  ⟨i.1.val * i.2.val.val, by
    have h := Nat.mul_lt_mul_of_pos_left i.2.val.isLt (divisor_positive q i.1)
    rwa [divisor_mul_quotient] at h⟩

lemma gcdResidueValue_injective (q : ℕ) : Function.Injective (gcdResidueValue q) := by
  intro i j heq
  rcases i with ⟨u, b⟩
  rcases j with ⟨v, c⟩
  have hvalues : u.val * b.val.val = v.val * c.val.val := congrArg Fin.val heq
  have huEq : u = v := by
    apply Subtype.ext
    have h := congrArg (fun n => n.gcd q) hvalues
    simpa only [scaled_coprime_gcd] using h
  subst v
  have hb : b = c := by
    apply Subtype.ext
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (divisor_positive q u) hvalues
  subst c
  rfl

lemma gcd_normalized_coprime (a q : ℕ) [NeZero q] : (a / a.gcd q).Coprime (q / a.gcd q) := by
  have hu : 0 < a.gcd q := Nat.gcd_pos_of_pos_right a (NeZero.pos q)
  have ha := Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)
  have hq := Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)
  have heq : a.gcd q * (a / a.gcd q).gcd (q / a.gcd q) = a.gcd q := by
    rw [← Nat.gcd_mul_left, ha, hq]
  change (a / a.gcd q).gcd (q / a.gcd q) = 1
  exact Nat.eq_of_mul_eq_mul_left hu (by simpa only [Nat.mul_one] using heq)

lemma gcdResidueValue_surjective (q : ℕ) [NeZero q] : Function.Surjective (gcdResidueValue q) := by
  intro a
  let u : ↥q.divisors := ⟨a.val.gcd q, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right a.val q, NeZero.ne q⟩⟩
  have hu : 0 < u.val := divisor_positive q u
  have huq : u.val * (q / u.val) = q := divisor_mul_quotient q u
  have hab : a.val / u.val < q / u.val := by
    apply (Nat.div_lt_iff_lt_mul hu).mpr
    simpa only [Nat.mul_comm, huq] using a.isLt
  let b : ReducedResidues (q / u.val) := ⟨⟨a.val / u.val, hab⟩, gcd_normalized_coprime a.val q⟩
  refine ⟨⟨u, b⟩, ?_⟩
  apply Fin.ext
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a.val q)

noncomputable def gcdResidueEquiv (q : ℕ) [NeZero q] : GcdResidueIndex q ≃ Fin q :=
  Equiv.ofBijective (gcdResidueValue q) ⟨gcdResidueValue_injective q, gcdResidueValue_surjective q⟩

#print axioms gcdResidueEquiv

end ReflectedLiouville
