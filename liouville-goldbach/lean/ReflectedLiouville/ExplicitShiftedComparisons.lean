import ReflectedLiouville.ExplicitPaddingAtom
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedPaddingComparison
import OAI.NumberTheory.TwoPoint.Bounds.DegreeCostResidue
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedDegreeDeletion
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedRareComparison

set_option autoImplicit false
set_option maxHeartbeats 1500000
open OAI.TwoPointCorrelations Finset Filter
open scoped Classical
namespace ReflectedLiouville

theorem explicit_shifted_padding_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (D : Finset ℕ),
      (∀ d ∈ D, d.primeFactors ⊆ data.P ∪ data.Q) →
      (∀ d ∈ D, (d.primeFactors.card : ℝ) ≤ L ^ 2) →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ) (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ (289578 : ℕ) / 2) ≤ (N j : ℝ)) →
      |(∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
          paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
            ((a j + x.val : ℤ) + site j d q))) -
        (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
          positivePrimeWeight d.primeFactors (data.residueOrigin x) *
            paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x))| ≤
        2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
  have hb := explicit_padding_atom_comparison
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL D hD hcard Q hQ hqdegree bins η K c site a N hN
  let I := bins ×ˢ (D ×ˢ Q)
  let f := fun (i : ℤ × (ℕ × ℕ)) (n : ℤ) =>
    paddingRejectionAtom data.Q i.2.1.primeFactors Q (actualPaddingBin η (c i.2.1) i.1)
      L K i.2.2 (n + site i.1 i.2.1 i.2.2)
  let g := fun (i : ℤ × (ℕ × ℕ)) (x : ↥(data.P ∪ data.Q) → Fin B) =>
    paddingRejectionAtom data.Q i.2.1.primeFactors Q (actualPaddingBin η (c i.2.1) i.1)
      L K i.2.2 (data.residueOrigin x)
  have hs := finite_interval_family_error I (data.residueLaw B hB)
    (fun i => a i.1) (fun i => N i.1) f g (fun _ => 2 * Real.exp (-(L ^ 9))) (by
      intro i hi
      obtain ⟨hj, hdq⟩ := mem_product.mp hi
      obtain ⟨hd, hq⟩ := mem_product.mp hdq
      have hx := hb h J M B data hB hpool hBL i.2.1.primeFactors (hD _ hd) (hcard _ hd)
        i.2.2 (hQ hq) (hqdegree _ hq) Q hQ (actualPaddingBin η (c i.2.1) i.1)
        K (site i.1 i.2.1 i.2.2) (a i.1) (N i.1) (hN _ hj)
      rw [data.padding_rejection_average_translate hB i.2.1.primeFactors Q (hD _ hd)
        hQ (actualPaddingBin η (c i.2.1) i.1) L K i.2.2 (hQ hq)
          (site i.1 i.2.1 i.2.2)] at hx
      exact hx)
  have he : (∑ _i ∈ I, 2 * Real.exp (-(L ^ 9))) =
      2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
    simp only [sum_const, nsmul_eq_mul, I, card_product, Nat.cast_mul]
    ring
  rw [he] at hs
  simp only [I, sum_product, f, g] at hs
  have hmodel (x : ↥(data.P ∪ data.Q) → Fin B) :
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q,
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          (data.residueOrigin x)) =
      ∑ d ∈ D, positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    exact (padding_rejection_bin_identity data.Q d.primeFactors Q bins η (c d) L K _).symm
  simpa only [hmodel] using hs

theorem explicit_integer_degree_cost
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (W : ℝ), 10 ≤ W → 6 * W * S.card ≤ 400 * Real.log L →
      (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N =>
        actualPaddingCoefficient q * positivePrimeWeight S ((a + x.val : ℤ) + site) *
          if (q : ℤ) ∣ (a + x.val : ℤ) + site ∧
            6 * W * S.card < (actualPaddingDegree data.P ((a + x.val : ℤ) + site) : ℝ)
            then 1 else 0) ≤
        actualPaddingCoefficient q / q * positivePrimeNormalizer S *
          Real.exp (-2 * W * S.card) + Real.exp (-(L ^ 9)) := by
  have hb := explicit_degree_cost_comparison
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hSP hSL W hW hTL hmass q hq hqdegree site a N hN
  have hc := hb h J M B data hB hpool hBL S data.P
    (hSP.trans subset_union_left) subset_union_left hSL q hq hqdegree
    (6 * W * S.card) (by positivity) hTL site a N hN
  have hm := data.positive_divisor_degree_cost hB S hSP q hq W hW hmass site
  dsimp only at hc
  have hu := le_trans (le_abs_self _) hc
  linarith

theorem explicit_shifted_tuple_degree_deletion
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      ∀ W : ℝ, 10 ≤ W → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (J : ℝ) ≤ L ^ 2 → 6 * W * J ≤ 400 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η : ℝ) (c : ℕ → ℝ), 0 < η →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * paddingTiltNormalizer data.Q *
        Real.exp (-2 * W * J) +
          bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
  have hb := explicit_integer_degree_cost
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL P hP hprime hdisjoint W hW hV hJ hTL D hD Q hQ
    hqdegree bins η c hη site a N hN
  have hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J := by
    rw [← primeHarmonicMass_eq_sum, ← hP, primeTuplePool_mass P hdisjoint]
    calc
      _ ≤ ∑ _j : Fin J, 2 * W := sum_le_sum (fun j _ => hV j)
      _ = _ := by simp; ring
  have ht (d : ℕ) (hd : d ∈ D) :
      (∑ j ∈ bins, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) ≤
      positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) * paddingTiltNormalizer data.Q +
        bins.card * Q.card * Real.exp (-(L ^ 9)) := by
    have ha := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
    have heach (j : ℤ) (hj : j ∈ bins) :
        (∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
          uniformAverage (fun x : Fin (N j) =>
            positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) ≤
        positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
            Q.card * Real.exp (-(L ^ 9)) := by
      have hpoint (q : ℕ) (hq : q ∈ Q.filter (actualPaddingBin η (c d) j)) :
          uniformAverage (fun x : Fin (N j) =>
            positiveDegreeCost data.P d.primeFactors W q
              ((a j + x.val : ℤ) + site j d q)) ≤
            actualPaddingCoefficient q / q * positivePrimeNormalizer d.primeFactors *
              Real.exp (-2 * W * J) + Real.exp (-(L ^ 9)) := by
        have hx := hb h J M B data hB hpool hBL d.primeFactors (ha.2.2.trans_eq hP)
          (by simpa only [ha.2.1] using hJ) W hW (by simpa only [ha.2.1] using hTL)
          (by simpa only [ha.2.1] using hmass) q (hQ (mem_filter.mp hq).1)
          (hqdegree q (mem_filter.mp hq).1) (site j d q) (a j) (N j) (hN j hj)
        simpa only [positiveDegreeCost, ha.2.1] using hx
      have hcard : ((Q.filter (actualPaddingBin η (c d) j)).card : ℝ) ≤ Q.card := by
        exact_mod_cast card_filter_le Q (actualPaddingBin η (c d) j)
      calc
        _ ≤ ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
            (actualPaddingCoefficient q / q * positivePrimeNormalizer d.primeFactors *
              Real.exp (-2 * W * J) + Real.exp (-(L ^ 9))) := sum_le_sum hpoint
        _ = positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
              (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              (Q.filter (actualPaddingBin η (c d) j)).card * Real.exp (-(L ^ 9)) := by
          simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
          ring
        _ ≤ _ := by
          have he := mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-(L ^ 9))).le
          linarith
    calc
      _ ≤ ∑ j ∈ bins, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
            (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              Q.card * Real.exp (-(L ^ 9))) := sum_le_sum heach
      _ = positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
            (∑ j ∈ bins, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              bins.card * Q.card * Real.exp (-(L ^ 9)) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left
          (padding_bin_reciprocal_sum_le data.Q Q data.primeQ hQ bins η (c d) hη)
          (show 0 ≤ positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) by
            unfold positivePrimeNormalizer; positivity)
        linarith
  rw [sum_comm]
  calc
    _ ≤ ∑ d ∈ D, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          paddingTiltNormalizer data.Q + bins.card * Q.card * Real.exp (-(L ^ 9))) := sum_le_sum ht
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * Real.exp (-2 * W * J) *
          paddingTiltNormalizer data.Q + bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
      simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD)
          (Real.exp_pos (-2 * W * J)).le) (paddingTiltNormalizer_pos data.Q).le
      nlinarith

theorem explicit_shifted_prohibited_row_comparison
    :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B s cap : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      ∀ (D : Finset ℕ),
      (∀ d ∈ D, d.primeFactors ⊆ data.P ∪ data.Q) →
      (∀ d ∈ D, (d.primeFactors.card : ℝ) ≤ L ^ 2) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) →
      |(∑ d ∈ D, ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors ((a + x.val : ℤ) + site d q) *
            if (q : ℤ) ∣ (a + x.val : ℤ) + site d q ∧
              ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) ((a + x.val : ℤ) + site d q)
              then 1 else 0)) -
        (data.residueLaw B hB).average (fun x =>
          prohibitedPositiveRow data s D padding (data.residueOrigin x))| ≤
            (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
  have hb := explicit_prohibited_cost_comparison
  filter_upwards [hb] with L hb
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree D hD hcard
    padding hpadding hqdegree site a N hN
  let μ := data.residueLaw B hB
  let atom := fun d q n => actualPaddingCoefficient q * positivePrimeWeight (Nat.primeFactors d) n *
    if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0
  have hpoint (d : ℕ) (hd : d ∈ D) (q : ℕ) (hq : q ∈ padding d) :
      |uniformAverage (fun x : Fin N => atom d q ((a + x.val : ℤ) + site d q)) -
        μ.average (fun x => atom d q (data.residueOrigin x))| ≤ Real.exp (-(L ^ 9)) := by
    have hx := hb h J M B s cap data hB hpool hBL hs hcap hpair hdegree
      d.primeFactors (hD d hd) (hcard d hd) q (hpadding d hd hq) (hqdegree d hd q hq)
      (site d q) a N hN
    dsimp only at hx
    rw [data.prohibited_cost_average_translate hB d.primeFactors (hD d hd) s q
      (hpadding d hd hq) (site d q)] at hx
    exact hx
  have hinner (d : ℕ) (hd : d ∈ D) :
      |(∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
          atom d q ((a + x.val : ℤ) + site d q))) -
        μ.average (fun x => ∑ q ∈ padding d, atom d q (data.residueOrigin x))| ≤
          (padding d).card * Real.exp (-(L ^ 9)) := by
    rw [μ.average_finset_sum]
    simpa only [sum_const, nsmul_eq_mul] using finset_sum_error (padding d)
      (fun q => uniformAverage (fun x : Fin N => atom d q ((a + x.val : ℤ) + site d q)))
      (fun q => μ.average (fun x => atom d q (data.residueOrigin x)))
      (fun _ => Real.exp (-(L ^ 9))) (hpoint d hd)
  have hout := finset_sum_error D
    (fun d => ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
      atom d q ((a + x.val : ℤ) + site d q)))
    (fun d => μ.average (fun x => ∑ q ∈ padding d, atom d q (data.residueOrigin x)))
    (fun d => (padding d).card * Real.exp (-(L ^ 9))) hinner
  rw [← μ.average_finset_sum, ← sum_mul, ← Nat.cast_sum] at hout
  exact hout

#print axioms explicit_shifted_padding_comparison
#print axioms explicit_shifted_tuple_degree_deletion
#print axioms explicit_shifted_prohibited_row_comparison
end ReflectedLiouville
