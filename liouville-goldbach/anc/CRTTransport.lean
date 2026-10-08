import OAI.NumberTheory.TwoPointCorrelations.FinalMain
import Mathlib.Data.Int.GCD

set_option autoImplicit false

open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma step_scale (N : ℕ) (a : SignedStep) :
    a.displacement N = (N : ℤ) * a.displacement 1 := by
  unfold SignedStep.displacement
  simp only [Nat.cast_one, mul_one]
  ring

lemma word_scale (N : ℕ) (w : List SignedStep) :
    wordDisplacement N w = (N : ℤ) * wordDisplacement 1 w := by
  induction w with
  | nil => simp
  | cons a w ih => rw [wordDisplacement_cons, wordDisplacement_cons, step_scale, ih]; ring

lemma nat_scaled_dvd (d N : ℕ) (h : Nat.Coprime d N) (z : ℤ) :
    (d : ℤ) ∣ (N : ℤ) * z ↔ (d : ℤ) ∣ z := by
  constructor
  · intro hz
    apply Int.dvd_of_dvd_mul_right_of_gcd_one hz
    simpa using h.gcd_eq_one
  · intro hz
    exact hz.mul_left (N : ℤ)

lemma divisor_scaled_dvd (N : ℕ) (a : SignedStep)
    (h : Nat.Coprime (a.padding * a.tuple) N) (z : ℤ) :
    a.divisor ∣ (N : ℤ) * z ↔ a.divisor ∣ z := by
  simpa [SignedStep.divisor] using nat_scaled_dvd (a.padding * a.tuple) N h z

lemma positive_scale (N : ℕ) (w : List SignedStep) (x : ℤ) :
    (∀ a ∈ w, Nat.Coprime (a.padding * a.tuple) N) →
    (PositiveWord N ((N : ℤ) * x) w ↔ PositiveWord 1 x w) := by
  induction w generalizing x with
  | nil => intro h; simp [PositiveWord]
  | cons a w ih =>
    intro h
    have ha := h a (by simp)
    have ht : ∀ b ∈ w, Nat.Coprime (b.padding * b.tuple) N :=
      fun b hb => h b (by simp [hb])
    have he : (N : ℤ) * x + a.displacement N =
        (N : ℤ) * (x + a.displacement 1) := by rw [step_scale]; ring
    rw [positiveWord_cons, positiveWord_cons, he, divisor_scaled_dvd N a ha,
      ih (x + a.displacement 1) ht]

lemma forward_scale (N s : ℕ) (supply : ℕ → ℕ → Prop)
    (hc : ∀ d q, supply d q → Nat.Coprime d N) (w : List SignedStep) :
    ForwardProhibited N s supply w ↔ ForwardProhibited 1 s supply w := by
  have hstart (hs : ∀ a ∈ w, supply a.tuple a.padding) (p : ℕ)
      (hp : TuplePrimeAt w p 0) : Nat.Coprime p N := by
    obtain ⟨_, a, ha, hpa⟩ := hp
    have ham : a ∈ w := List.mem_of_getElem? ha
    exact (hc a.tuple a.padding (hs a ham)).of_dvd_left hpa
  constructor
  · rintro ⟨hlo, hhi, hs, hchain, hinterval, p, hp, hpnot, a, ha, haend, hdiv⟩
    refine ⟨hlo, hhi, hs, hchain, hinterval, p, hp, hpnot, a, ha, haend, ?_⟩
    rw [word_scale] at hdiv
    exact (nat_scaled_dvd p N (hstart hs p hp) _).mp hdiv
  · rintro ⟨hlo, hhi, hs, hchain, hinterval, p, hp, hpnot, a, ha, haend, hdiv⟩
    refine ⟨hlo, hhi, hs, hchain, hinterval, p, hp, hpnot, a, ha, haend, ?_⟩
    rw [word_scale]
    exact (nat_scaled_dvd p N (hstart hs p hp) _).mpr hdiv

lemma minimal_scale (N s : ℕ) (supply : ℕ → ℕ → Prop)
    (hc : ∀ d q, supply d q → Nat.Coprime d N) (w : List SignedStep) :
    MinimalWord (ForwardProhibited N s supply) w ↔
      MinimalWord (ForwardProhibited 1 s supply) w := by
  unfold MinimalWord
  simp_rw [forward_scale N s supply hc]

lemma prohibited_scale (N s : ℕ) (supply : ℕ → ℕ → Prop)
    (hc : ∀ d q, supply d q → Nat.Coprime d N)
    (hwhole : ∀ d q, supply d q → Nat.Coprime (q * d) N) (x : ℤ) :
    ProhibitedSite N s supply ((N : ℤ) * x) ↔ ProhibitedSite 1 s supply x := by
  constructor
  · rintro ⟨w, hp, hm⟩
    have hs := hm.1.2.2.1
    refine ⟨w, ?_, (minimal_scale N s supply hc w).mp hm⟩
    exact (positive_scale N w x (fun a ha => hwhole a.tuple a.padding (hs a ha))).mp hp
  · rintro ⟨w, hp, hm⟩
    have hs := hm.1.2.2.1
    refine ⟨w, ?_, (minimal_scale N s supply hc w).mpr hm⟩
    exact (positive_scale N w x (fun a ha => hwhole a.tuple a.padding (hs a ha))).mpr hp

lemma prohibited_CRT {N J M B : ℕ}
    (data : ProhibitedPrimeFamily N J M)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hc : ∀ d q, (d, q) ∈ data.pairs → Nat.Coprime (q * d) N)
    (s ell : ℕ)
    (hinv : ∀ p : ↥(data.P ∪ data.Q),
      (N : ZMod p.val) * (ell : ZMod p.val) = 1)
    (k r : ℤ) :
    ProhibitedSite N s (fun d q => (d, q) ∈ data.pairs) ((N : ℤ) * k + r) ↔
      ProhibitedSite 1 s (fun d q => (d, q) ∈ data.pairs) (k + (ell : ℤ) * r) := by
  have hm : ∀ p : ↥(data.P ∪ data.Q),
      (((N : ℤ) * k + r : ℤ) : ZMod p.val) =
        (((N : ℤ) * (k + (ell : ℤ) * r) : ℤ) : ZMod p.val) := by
    intro p
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_add,
      ← mul_assoc, hinv p, one_mul]
  refine (data.prohibitedSite_congr hB s _ _ hm).trans ?_
  exact prohibited_scale N s (fun d q => (d, q) ∈ data.pairs)
    (fun d q hd => (hc d q hd).of_dvd_left (dvd_mul_left d q)) hc _

#print axioms ReflectedLiouville.prohibited_scale
#print axioms ReflectedLiouville.prohibited_CRT

end ReflectedLiouville
