import ReflectedLiouville.ExplicitStateWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingIntegerBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
open OAI.TwoPointCorrelations Finset Filter
open scoped Classical
namespace ReflectedLiouville

theorem explicit_prime_state_weight :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => primeStateTruncatedWeight s
        ⌊400 * Real.log L⌋₊ site (fun i => (a + x.val : ZMod (s i)))) ≤
          (∏ i, (1 + 4 / (s i : ℝ))) + Real.exp (-(L ^ 9)) := by
  have hcompare := explicit_active_state_comparison
  filter_upwards [hcompare, eventually_ge_atTop (4800 : ℝ)] with L hcompare hL
  intro m s _ hm hmL hcop hs site a N hN
  let M : ℕ := ⌊400 * Real.log L⌋₊
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hM : (M : ℝ) ≤ 400 * Real.log L := Nat.floor_le hlog
  let f : (Fin 1 → Finset (Fin m)) → ℝ := fun S => (5 : ℝ) ^ (S 0).card
  have hf : ∀ b : Fin 1 → boundedActiveStates m M,
      |f (fun r => (b r).val)| ≤ Real.exp (L ^ 4) := by
    intro b
    dsimp [f]
    rw [abs_of_nonneg (pow_nonneg (by norm_num) _)]
    apply padding_state_coefficient_bound L _ hL
    exact (Nat.cast_le.mpr (mem_boundedActiveStates.mp (b 0).property)).trans hM
  have hc := hcompare m s hm (by linarith) hcop hs 1 m m M hmL hM
    (by norm_num; linarith)
    (fun i => i) (fun i z => decide (z + (site : ZMod (s i)) = 0))
    (fun _ i => i) f hf a N hN
  have he (z : ∀ i, ZMod (s i)) :
      (if ∀ r : Fin 1,
        (activeState (fun i => residueCircuitInputs s (fun i => i)
          (fun i z => decide (z + (site : ZMod (s i)) = 0)) z i)).card ≤ M
        then f (fun _ => activeState (fun i => residueCircuitInputs s (fun i => i)
          (fun i z => decide (z + (site : ZMod (s i)) = 0)) z i)) else 0) =
      primeStateTruncatedWeight s M site z := by
    simp only [residueCircuitInputs, f, primeStateTruncatedWeight, forall_const]
  dsimp only at hc
  simp only [he] at hc
  have hb := primeStateTruncatedWeight_average_le s M site
  linarith [(le_abs_self
    (uniformAverage (fun x : Fin N => primeStateTruncatedWeight s M site
      (fun i => (a + x.val : ZMod (s i)))) -
        uniformAverage (primeStateTruncatedWeight s M site))).trans hc]

theorem explicit_actual_padding_weight :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let T := uniformAverage (fun x : Fin N =>
        (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
          if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site) then 1 else 0)
      T ≤ paddingTiltNormalizer Q + Real.exp (-(L ^ 9)) ∧
        T ≤ 2 * paddingTiltNormalizer Q := by
  have hb := explicit_prime_state_weight
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro Q hQ hupper site a N hN
  have hL0 : 0 ≤ L := by linarith
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hmain : uniformAverage (fun x : Fin N =>
      (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
        if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site) then 1 else 0) ≤
      paddingTiltNormalizer Q + Real.exp (-(L ^ 9)) := by
    by_cases hne : Q.Nonempty
    · let m := Fintype.card Q
      let e : Fin m ≃ Q := (Fintype.equivFin Q).symm
      let s := fun i : Fin m => (e i).val
      let (i : Fin m) : NeZero (s i) := ⟨(hQ _ (e i).property).ne_zero⟩
      have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨hne.choose, hne.choose_spec⟩⟩
      have hmL : (m : ℝ) ≤ Real.exp L := by
        simpa only [m, Fintype.card_coe] using primeSet_card_le_exp Q hQ L hupper
      have hcop : Pairwise (fun i j => (s i).Coprime (s j)) := by
        intro i j hij
        apply (Nat.coprime_primes (hQ _ (e i).property) (hQ _ (e j).property)).mpr
        intro he
        exact hij (e.injective (Subtype.ext he))
      have hs (i : Fin m) : (s i : ℝ) ≤ Real.exp L := hupper _ (e i).property
      have hh := hb m s hm hmL hcop hs site a N hN
      have heval (x : Fin N) : primeStateTruncatedWeight s ⌊400 * Real.log L⌋₊ site
          (fun i => (a + x.val : ZMod (s i))) =
          (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
            if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site) then 1 else 0 := by
        have hx := primeStateTruncatedWeight_actual Q e ⌊400 * Real.log L⌋₊ site
          ((a + x.val : ℕ) : ℤ)
        simp only [Nat.cast_add, Int.cast_add, Int.cast_natCast] at hx
        rw [hx]
        simp only [Nat.le_floor_iff hlog, actualPaddingVertex_sq,
          actualPaddingDegreeCut, Nat.cast_add]
        split_ifs <;> simp
      have hnorm : (∏ i, (1 + 4 / (s i : ℝ))) = paddingTiltNormalizer Q :=
        e.prod_comp (fun p : Q => 1 + 4 / (p.val : ℝ))
      simpa only [heval, hnorm] using hh
    · have hQempty : Q = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst Q
      have hNpos : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
      let : NeZero N := ⟨by omega⟩
      have hf (x : Fin N) :
          (actualPaddingVertex ∅ (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
            (if actualPaddingDegreeCut ∅ L (((a + x.val : ℕ) : ℤ) + site)
              then (1 : ℝ) else 0) = 1 := by
        simp only [actualPaddingVertex_sq, actualPaddingWeight, actualPaddingDegree,
          filter_empty, card_empty, pow_zero, actualPaddingDegreeCut, Nat.cast_zero,
          hlog, ite_true, mul_one]
      simp only [hf, uniformAverage_const]
      have hnorm : paddingTiltNormalizer ∅ = 1 := by simp [paddingTiltNormalizer]
      rw [hnorm]
      linarith [Real.exp_pos (-(L ^ 9))]
  dsimp only
  refine ⟨hmain, ?_⟩
  have he : Real.exp (-(L ^ 9)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg hL0 _))
  have hS := paddingTiltNormalizer_one_le Q
  linarith

#print axioms explicit_actual_padding_weight
end ReflectedLiouville
