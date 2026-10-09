import ReflectedLiouville.ExplicitStateWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.DegreeCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.StateCostComparison
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedCostComparison

set_option autoImplicit false
set_option maxHeartbeats 1500000
open OAI.TwoPointCorrelations Finset Filter
open scoped Classical
namespace ReflectedLiouville

theorem explicit_positive_prime_cost_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (r ninput : ℕ), (r : ℝ) ≤ 100 * Real.log L →
      ∀ (literal : Fin ninput → ↥(data.P ∪ data.Q) × ℤ)
        (index : Fin (Fintype.card S) → Fin ninput) (site : ℤ),
      (∀ i, (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site) →
      ∀ (c : AC0Circuit ninput), c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ (bad : ℤ → Prop),
      (∀ n, c.eval (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔
        bad n) →
      ∀ a N : ℕ, Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => (4 : ℝ) ^ r * positivePrimeWeight S (n + site) *
        if bad n then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  have hb := explicit_positive_weight_comparison
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hS hSL r ninput hr literal index site hindex
    c hc hsize bad hbad a N hN
  let primes := data.P ∪ data.Q
  let modulus := primeResidueModuli primes
  let (i : Fin (Fintype.card primes)) : NeZero (modulus i) :=
    ⟨(primeResidueModuli_prime primes (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let p : Fin (Fintype.card S) → ℕ := fun i => (e i).val
  let F := fun z : ∀ i, ZMod (modulus i) =>
    let bits := residueCircuitInputs modulus (primeLiteralCoordinate primes literal)
      (primeLiteralTest primes literal) z
    positivePrimeTable p r (fun i => bits (index i)) * c.indicator bits
  let cost := fun n : ℤ => (4 : ℝ) ^ r * positivePrimeWeight S (n + site) *
    if bad n then 1 else 0
  have hp (i : Fin (Fintype.card S)) : 1 ≤ p i :=
    (data.prime ⟨p i, hS (e i).property⟩).one_lt.le
  have hcard : (Fintype.card primes : ℝ) ≤ Real.exp L := by
    have hh := primePool_card_bound primes (fun p hp => data.prime ⟨p, hp⟩) B hB
    have hh' : (primes.card : ℝ) ≤ B := by exact_mod_cast hh
    simpa only [Fintype.card_coe] using hh'.trans hBL
  have hm : 0 < Fintype.card primes := by
    simpa only [Fintype.card_coe] using card_pos.mpr hpool
  have hmod (i : Fin (Fintype.card primes)) : (modulus i : ℝ) ≤ Real.exp L :=
    primeResidueModuli_bound primes (Real.exp L)
      (fun p hp => (show (p : ℝ) ≤ B by exact_mod_cast hB p hp).trans hBL) i
  have hh := hb (Fintype.card primes) modulus hm (by linarith)
    (primeResidueModuli_coprime primes (fun p hp => data.prime ⟨p, hp⟩)) hmod
    (Fintype.card S) r ninput p hp (by simpa only [Fintype.card_coe] using hSL) hr
    (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal) index c
    hc hsize a N hN
  change |uniformAverage (fun x : Fin N => F (fun i => (a + x.val : ZMod (modulus i)))) -
    uniformAverage F| ≤ Real.exp (-(L ^ 9)) at hh
  have hF (n : ℤ) : F (fun i => (n : ZMod (modulus i))) = cost n := by
    let bits := residueCircuitInputs modulus (primeLiteralCoordinate primes literal)
      (primeLiteralTest primes literal) (fun i => (n : ZMod (modulus i)))
    have hall : bits = fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2) := by
      funext i
      exact primeLiteral_integer_input primes literal n i
    have hbits (i : Fin (Fintype.card S)) : bits (index i) =
        decide ((p i : ℤ) ∣ n + site) := by
      rw [hall]
      simp only [(hindex i).1, (hindex i).2, p, e]
    have hgate : c.indicator bits = if bad n then 1 else 0 := by
      have heval : c.eval bits = true ↔ bad n := by
        simpa only [hall] using hbad n
      simp only [AC0Circuit.indicator, heval]
    change positivePrimeTable p r (fun i => bits (index i)) * c.indicator bits = cost n
    simp only [hbits, hgate]
    rw [positivePrimeTable_actual S e r (n + site)]
  have hmodel : (data.residueLaw B hB).average (fun x => cost (data.residueOrigin x)) =
      uniformAverage F := by
    rw [← data.residue_average_canonical hB F]
    apply congrArg (data.residueLaw B hB).average
    funext x
    rw [← hF, data.canonical_origin]
  dsimp only
  rw [hmodel]
  have hsample : (fun x : Fin N => cost (a + x.val)) =
      (fun x : Fin N => F (fun i => (a + x.val : ZMod (modulus i)))) := by
    funext x
    simpa only [Int.cast_add, Int.cast_natCast, Nat.cast_add] using (hF (a + x.val)).symm
  rw [hsample]
  exact hh

theorem explicit_degree_cost_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S V : Finset ℕ), S ⊆ data.P ∪ data.Q → V ⊆ data.P ∪ data.Q →
      (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (T : ℝ), 0 ≤ T → T ≤ 400 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ T < (actualPaddingDegree V (n + site) : ℝ) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  have hb := explicit_positive_prime_cost_comparison
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S V hS hV hSL q hq hqdegree T hT hTL site a N hN
  let U := data.P ∪ data.Q
  let hQU : data.Q ⊆ U := subset_union_right
  let literal : Fin (Fintype.card U) → U × ℤ :=
    fun i => ((Fintype.equivFin U).symm i, site)
  let index := primeSubsetIndex U S hS
  let pindex := primeSubsetIndex U V hV
  let qindex := primeSubsetIndex U q.primeFactors
    ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans hQU)
  let c := degreeDivisorCircuit pindex qindex (⌊T⌋₊ + 1)
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧
    T < (actualPaddingDegree V (n + site) : ℝ)
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site :=
    ⟨primeSubsetIndex_value U S hS i, rfl⟩
  have hVcard : (Fintype.card V : ℝ) ≤ Real.exp L := by
    have hbound : V.card ≤ B := (card_le_card hV).trans
      (primePool_card_bound U (fun p hp => data.prime ⟨p, hp⟩) B hB)
    have hbound' : (V.card : ℝ) ≤ B := by exact_mod_cast hbound
    simpa only [Fintype.card_coe] using hbound'.trans hBL
  have hqcard : (Fintype.card q.primeFactors : ℝ) ≤ 100 * Real.log L := by
    simpa only [Fintype.card_coe] using hqdegree
  have hfloor : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 400 * Real.log L + 1 := by
    push_cast
    linarith [Nat.floor_le hT]
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) :=
    degreeDivisorCircuit_size_exp pindex qindex (⌊T⌋₊ + 1) L hL hVcard hqcard hfloor
  have hc : c.depth ≤ 19 := (degreeDivisorCircuit_depth pindex qindex _).trans (by norm_num)
  have hbad (n : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔ bad n :=
    degreeDivisorCircuit_integer U V data.Q hV hQU data.primeQ q hq T hT (n + site)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card U) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

theorem explicit_state_cost_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (D : ℕ), (D : ℝ) ≤ 400 * Real.log L →
      ∀ (E : Finset (Fin (Fintype.card data.Q)) → Prop) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ actualPaddingDegree data.Q (n + site) ≤ D ∧
          E (paddingActiveState data.Q (Fintype.equivFin data.Q).symm (n + site))
          then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  have hb := explicit_positive_prime_cost_comparison
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD E site a N hN
  let U := data.P ∪ data.Q
  let hQU : data.Q ⊆ U := subset_union_right
  let literal : Fin (Fintype.card U) → U × ℤ :=
    fun i => ((Fintype.equivFin U).symm i, site)
  let index := primeSubsetIndex U S hS
  let qindex := primeSubsetIndex U data.Q hQU
  let dindex := primeSubsetIndex U q.primeFactors
    ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans hQU)
  let c := stateDivisorCircuit qindex dindex D E
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧ actualPaddingDegree data.Q (n + site) ≤ D ∧
    E (paddingActiveState data.Q (Fintype.equivFin data.Q).symm (n + site))
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site :=
    ⟨primeSubsetIndex_value U S hS i, rfl⟩
  have hQcard : (Fintype.card data.Q : ℝ) ≤ Real.exp L := by
    have hbound : data.Q.card ≤ B := (card_le_card hQU).trans
      (primePool_card_bound U (fun p hp => data.prime ⟨p, hp⟩) B hB)
    have hbound' : (data.Q.card : ℝ) ≤ B := by exact_mod_cast hbound
    simpa only [Fintype.card_coe] using hbound'.trans hBL
  have hqcard : (Fintype.card q.primeFactors : ℝ) ≤ 100 * Real.log L := by
    simpa only [Fintype.card_coe] using hqdegree
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) :=
    stateDivisorCircuit_size_exp qindex dindex D E L hL hQcard hqcard hD
  have hc : c.depth ≤ 19 := (stateDivisorCircuit_depth qindex dindex D E).trans (by norm_num)
  have hbad (n : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔ bad n :=
    stateDivisorCircuit_integer U data.Q hQU data.primeQ q hq D E (n + site)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card U) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

theorem explicit_density_cost_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (eligible : ℕ → Prop) (K : ℝ) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ actualPaddingDegreeCut data.Q L (n + site) ∧
          K / L < paddingDensity D actualPaddingCoefficient eligible
            (actualPaddingVertex data.Q) (n + site) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  have hb := explicit_state_cost_comparison
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD eligible K site a N hN
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg hL)
  let E := fun T : Finset (Fin (Fintype.card data.Q)) =>
    K / L < paddingStateDensity data.Q D (Fintype.equivFin data.Q).symm eligible T
  have hh := hb h J M B data hB hpool hBL S hS hSL q hq hqdegree
    ⌊400 * Real.log L⌋₊ (Nat.floor_le hlog) E site a N hN
  have he (n : ℤ) : (actualPaddingDegree data.Q n ≤ ⌊400 * Real.log L⌋₊ ∧
      E (paddingActiveState data.Q (Fintype.equivFin data.Q).symm n)) ↔
      (actualPaddingDegreeCut data.Q L n ∧
        K / L < paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex data.Q) n) := by
    rw [Nat.le_floor_iff hlog, paddingDensity_eq_state data.Q D data.primeQ hD
      (Fintype.equivFin data.Q).symm eligible n]
    rfl
  simpa only [he] using hh

theorem explicit_prohibited_cost_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B s cap : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  have hb := explicit_positive_prime_cost_comparison
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree S hS hSL q hq hqdegree site a N hN
  let U := data.P ∪ data.Q
  let n := Fintype.card (ProhibitedInputs data.pairs h s)
  let I := Fin n ⊕ Fin (Fintype.card U)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let cindex : Fin n → Fin (Fintype.card I) := fun i => e (Sum.inl i)
  let uindex : Fin (Fintype.card U) → Fin (Fintype.card I) := fun i => e (Sum.inr i)
  let literal : Fin (Fintype.card I) → U × ℤ := fun i =>
    Sum.elim (fun j => ((data.prohibitedLiteral s j).1, site + (data.prohibitedLiteral s j).2))
      (fun j => ((Fintype.equivFin U).symm j, site)) (e.symm i)
  let index : Fin (Fintype.card S) → Fin (Fintype.card I) :=
    fun i => uindex (primeSubsetIndex U S hS i)
  let qindex : Fin (Fintype.card q.primeFactors) → Fin (Fintype.card I) :=
    fun i => uindex (primeSubsetIndex U q.primeFactors
      ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans subset_union_right) i)
  let c := prohibitedCostCircuit (prohibitedCircuit data.pairs h s) cindex qindex
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site)
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site := by
    simp only [literal, index, uindex, Equiv.symm_apply_apply, Sum.elim_inr]
    exact ⟨primeSubsetIndex_value U S hS i, trivial⟩
  have hbad (n0 : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n0 + (literal i).2)) = true ↔ bad n0 := by
    rw [prohibitedCostCircuit_eval]
    have hqbits : (∀ i, decide (((literal (qindex i)).1.val : ℤ) ∣
        n0 + (literal (qindex i)).2) = true) ↔ (q : ℤ) ∣ n0 + site := by
      simpa only [literal, qindex, uindex, Equiv.symm_apply_apply, Sum.elim_inr,
        primeSiteBits] using
        prime_divisor_all_bits U data.Q subset_union_right data.primeQ q hq (n0 + site)
    have hcbits : (fun i => decide (((literal (cindex i)).1.val : ℤ) ∣
        n0 + (literal (cindex i)).2)) = prohibitedInputAt data.pairs h s (n0 + site) := by
      funext i
      have hi := data.prohibitedLiteral_integer_input s (n0 + site) i
      rw [primeLiteral_integer_input] at hi
      simpa only [literal, cindex, Equiv.symm_apply_apply, Sum.elim_inl, add_assoc] using hi
    rw [hqbits, hcbits, prohibitedCircuit_correct data.pairs h s (n0 + site) data.whole_squarefree]
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) := by
    apply prohibitedCostCircuit_size_exp _ _ _ L hL
    · simpa only [Fintype.card_coe] using hqdegree
    · exact prohibitedCircuit_size_quadratic data.pairs h s cap L (by linarith)
        hs hcap hpair hdegree
  have hc : c.depth ≤ 19 :=
    (prohibitedCostCircuit_depth _ _ _ (prohibitedCircuit_depth data.pairs h s)).trans (by omega)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card I) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

#print axioms explicit_degree_cost_comparison
#print axioms explicit_density_cost_comparison
#print axioms explicit_prohibited_cost_comparison
end ReflectedLiouville
