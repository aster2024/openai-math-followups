import ReflectedLiouville.ExplicitResidueComparison
import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateComparison
import OAI.NumberTheory.TwoPoint.Walks.WeightedWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.AffineWeightedWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.PositiveWeightComparison

set_option autoImplicit false
set_option maxHeartbeats 1200000
open OAI.TwoPointCorrelations Finset Filter
open scoped Classical
namespace ReflectedLiouville

theorem explicit_active_state_comparison :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (index : Fin R → Fin n → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → ℝ),
      (∀ b : Fin R → boundedActiveStates n M,
        |f (fun r => (b r).val)| ≤ Real.exp (L ^ 4)) →
      ∀ a N : ℕ, Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if ∀ r, (activeState (fun i => bits (index r i))).card ≤ M
        then f (fun r => activeState (fun i => bits (index r i))) else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  have hscalar := explicit_scalar_residue_comparison 1 (by norm_num)
  filter_upwards [hscalar, eventually_ge_atTop (4800 : ℝ)] with L hscalar hL
  intro m s _ hm hmexp hcop hs R n Ninput M hn hM hR coord test index f hf a N hN
  let c := fun b : Fin R → boundedActiveStates n M =>
    activeStateVectorCircuit index (fun r => (b r).val)
  let coeff := fun b : Fin R → boundedActiveStates n M => f (fun r => (b r).val)
  have hb := hscalar m s hm hmexp hcop hs _ Ninput coord test c coeff
    (fun b => (activeStateVectorCircuit_depth index _).trans (by norm_num))
    (fun b => activeStateVector_size_budget L index _ (by linarith) hn hR)
    (by simpa only [one_mul] using activeStateVector_coefficient_budget L f hL hn hM hR hf)
    a N hN
  have hexpand (z : ∀ j, ZMod (s j)) :
      (if ∀ r, (activeState (fun i => residueCircuitInputs s coord test z (index r i))).card ≤ M
        then f (fun r => activeState (fun i => residueCircuitInputs s coord test z (index r i))) else 0) =
        ∑ b : Fin R → boundedActiveStates n M, coeff b *
          eventIndicator (residueCircuitEvent s coord test (c b)) z :=
    activeStateVector_scalar_expansion M index f (residueCircuitInputs s coord test z)
  dsimp only
  simpa only [← hexpand] using hb

theorem explicit_weighted_word_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n t Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L → (t : ℝ) ≤ L ^ 2 →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (qindex : Fin R → Fin n → Fin Ninput) (pindex : Fin t → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (c : AC0Circuit Ninput),
      (∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
        |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) →
      c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a N : ℕ, Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  have hscalar := explicit_scalar_residue_comparison 1 (by norm_num)
  filter_upwards [hscalar, eventually_ge_atTop (4800 : ℝ)] with L hscalar hL
  intro m s _ hm hmexp hcop hs R n t Ninput M hn hM hR ht coord test qindex pindex f c hf hc hsize a N hN
  let circuits := fun b : (Fin R → boundedActiveStates n M) × BooleanCube t =>
    weightedStateCircuit qindex pindex (fun r => (b.1 r).val) b.2 c
  let coeff := fun b : (Fin R → boundedActiveStates n M) × BooleanCube t =>
    f (fun r => (b.1 r).val) b.2
  have hb := hscalar m s hm hmexp hcop hs _ Ninput coord test circuits coeff
    (fun b => weightedStateCircuit_depth qindex pindex _ _ c hc)
    (fun b => weightedStateCircuit_size_budget L qindex pindex _ _ c (by linarith) hn hR ht hsize)
    (by simpa only [one_mul] using weightedWord_coefficient_budget L f hL hn hM hR ht hf)
    a N hN
  have hexpand (z : ∀ j, ZMod (s j)) :
      (if (∀ r, (activeState (fun i => residueCircuitInputs s coord test z (qindex r i))).card ≤ M) ∧
          c.eval (residueCircuitInputs s coord test z) = true
        then f (fun r => activeState (fun i => residueCircuitInputs s coord test z (qindex r i)))
          (fun i => residueCircuitInputs s coord test z (pindex i)) else 0) =
      ∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t, coeff b *
        eventIndicator (residueCircuitEvent s coord test (circuits b)) z :=
    weightedWord_scalar_expansion M qindex pindex f c (residueCircuitInputs s coord test z)
  dsimp only
  simpa only [← hexpand] using hb

theorem explicit_affine_weighted_word_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n t Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L → (t : ℝ) ≤ L ^ 2 →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (qindex : Fin R → Fin n → Fin Ninput) (pindex : Fin t → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (c : AC0Circuit Ninput),
      (∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
        |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) →
      c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a l N : ℕ, (∀ i, l.Coprime (s i)) → Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + l * x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  have hbase := explicit_weighted_word_comparison
  filter_upwards [hbase] with L hbase
  intro m s _ hm hmexp hcop hs R n t Ninput M hn hM hR ht coord test qindex pindex f c hf hc hsize a l N hl hN
  let affineTest := fun i (z : ZMod (s (coord i))) =>
    test i ((a : ZMod (s (coord i))) + (l : ZMod (s (coord i))) * z)
  let F := fun z : ∀ j, ZMod (s j) =>
    let bits := residueCircuitInputs s coord test z
    if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
    then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
    else 0
  let G := fun z : ∀ j, ZMod (s j) =>
    let bits := residueCircuitInputs s coord affineTest z
    if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
    then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
    else 0
  have hbits (z : ∀ j, ZMod (s j)) : residueCircuitInputs s coord affineTest z =
      residueCircuitInputs s coord test (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := rfl
  have hG (z : ∀ j, ZMod (s j)) : G z =
      F (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := by
    dsimp only [G, F]
    rw [hbits]
  have hb := hbase m s hm hmexp hcop hs R n t Ninput M hn hM hR ht
    coord affineTest qindex pindex f c hf hc hsize 0 N hN
  change |uniformAverage (fun x : Fin N => G (fun j => ((0 : ℕ) : ZMod (s j)) + x.val)) -
    uniformAverage G| ≤ Real.exp (-(L ^ 9)) at hb
  have hGfun : G = fun z => F (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := funext hG
  rw [hGfun] at hb
  rw [uniformAverage_residue_affine s a l hl F] at hb
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_zero, zero_add] using hb

theorem explicit_positive_weight_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (t r Ninput : ℕ) (p : Fin t → ℕ),
      (∀ i, 1 ≤ p i) → (t : ℝ) ≤ L ^ 2 → (r : ℝ) ≤ 100 * Real.log L →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (pindex : Fin t → Fin Ninput)
        (c : AC0Circuit Ninput), c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a N : ℕ, Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        positivePrimeTable p r (fun i => bits (pindex i)) * c.indicator bits
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  have hb := explicit_weighted_word_comparison
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro m s _ hm hmexp hcop hs t r Ninput p hp ht hr coord test pindex c hc hsize a N hN
  let qindex : Fin 0 → Fin 0 → Fin Ninput := fun i => Fin.elim0 i
  let f : (Fin 0 → Finset (Fin 0)) → BooleanCube t → ℝ :=
    fun _ bits => positivePrimeTable p r bits
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hh := hb m s hm hmexp hcop hs 0 0 t Ninput 0
    (by simpa only [Nat.cast_zero] using (Real.exp_pos L).le)
    (by simpa only [Nat.cast_zero] using hlog)
    (by simp only [Nat.cast_zero]; linarith) ht coord test qindex pindex f c
    (fun b => positivePrimeTable_budget p hp r L hL ht hr b.2) hc hsize a N hN
  have he (z : ∀ j, ZMod (s j)) :
      (if (∀ i : Fin 0, (activeState (fun j => residueCircuitInputs s coord test z
          (qindex i j))).card ≤ 0) ∧ c.eval (residueCircuitInputs s coord test z) = true
        then f (fun i => activeState (fun j => residueCircuitInputs s coord test z (qindex i j)))
          (fun i => residueCircuitInputs s coord test z (pindex i)) else 0) =
      positivePrimeTable p r (fun i => residueCircuitInputs s coord test z (pindex i)) *
        c.indicator (residueCircuitInputs s coord test z) := by
    simp only [Fin.forall_fin_zero, true_and, f, AC0Circuit.indicator]
    split_ifs <;> simp
  dsimp only at hh ⊢
  simpa only [he] using hh

#print axioms explicit_active_state_comparison
#print axioms explicit_affine_weighted_word_comparison
#print axioms explicit_positive_weight_comparison
end ReflectedLiouville
