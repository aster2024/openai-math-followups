import ReflectedLiouville.CRTDirectedEdges

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def physicalReflectionCompression {N J M : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily N J M) (P : Fin J → Finset ℕ) (site : V → ℤ)
    (r : ℤ) (L W : ℝ) (eligible : ℕ → ℕ → Prop) :=
  let Q := boundedPaddingDivisors data.Q M
  let physical := fun i => (N : ℤ) * site i + r
  let keep := fun n => ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) n
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0) physical Q
    actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J))
    (fun _ => actualPaddingDegreeCut data.Q L) N (fun _ i j => keep (physical i) ∧ keep (physical j))
  let proj := coordinateProjection (fun i : V =>
    (actualPaddingDegree (Finset.univ.biUnion P) (physical i) : ℝ) ≤ 6 * W * J)
  proj * (∑ d, B d) * proj

noncomputable def quotientReflectionCompression {N J M : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily N J M) (P : Fin J → Finset ℕ) (site : V → ℤ)
    (ell : ℕ) (r : ℤ) (L W : ℝ) (eligible : ℕ → ℕ → Prop) :=
  let Q := boundedPaddingDivisors data.Q M
  let quotient := fun i => site i + (ell : ℤ) * r
  let keep := fun n => ¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) n
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0) quotient Q
    actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J))
    (fun _ => actualPaddingDegreeCut data.Q L) 1 (fun _ i j => keep (quotient i) ∧ keep (quotient j))
  let proj := coordinateProjection (fun i : V =>
    (actualPaddingDegree (Finset.univ.biUnion P) (quotient i) : ℝ) ≤ 6 * W * J)
  proj * (∑ d, B d) * proj

/-- The full operator and center-degree projection transport, preserving the
    physical Liouville tests separately. Divisibility and all vertex deletions
    continue to be evaluated at their original signed physical sites. -/
theorem reflected_compression_CRT {N J M B : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily N J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hN : 0 < N) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (hsub : ∀ j, P j ⊆ data.P)
    (hc : ∀ d q, (d, q) ∈ data.pairs → Nat.Coprime (q * d) N)
    (site : V → ℤ) (ell : ℕ)
    (hinv : ∀ p : ↥(data.P ∪ data.Q), (N : ZMod p.val) * (ell : ZMod p.val) = 1)
    (r : ℤ) (L W : ℝ) (eligible : ℕ → ℕ → Prop) :
    physicalReflectionCompression data P site r L W eligible =
      quotientReflectionCompression data P site ell r L W eligible := by
  let Q := boundedPaddingDivisors data.Q M
  let physical := fun i : V => (N : ℤ) * site i + r
  let quotient := fun i : V => site i + (ell : ℤ) * r
  have hpoolInv : ∀ p ∈ data.P ∪ data.Q, (N : ZMod p) * (ell : ZMod p) = 1 :=
    fun p hp => hinv ⟨p, hp⟩
  have hcenterPool : ∀ d : (j : Fin J) → P j, (∏ j, (d j).val).primeFactors ⊆ data.P ∪ data.Q := by
    intro d p hp
    have ht := primeTupleDivisors_arithmetic P hprime hdisjoint
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)
    obtain ⟨j, hj⟩ := mem_primeTuplePool.mp (ht.2.2 hp)
    exact Finset.mem_union_left _ (hsub j hj)
  have hQpool : ∀ q ∈ Q, Squarefree q ∧ q.primeFactors ⊆ data.Q := by
    intro q hq
    have hr := (Finset.mem_filter.mp hq).1
    exact ⟨retainedPrimeDivisor_squarefree data.Q data.primeQ hr,
      retainedPrimeDivisor_factors data.Q data.primeQ hr⟩
  have hkeep (i : V) :
      (¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (physical i)) ↔
      (¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (quotient i)) :=
    not_congr (prohibited_CRT data hB hc ⌊L ^ (1 / 10 : ℝ)⌋₊ ell hinv (site i) r)
  have hOp (d : (j : Fin J) → P j) :
      primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0) physical Q
        actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut data.Q L) N (fun _ i j =>
          (¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (physical i)) ∧
          (¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (physical j))) d =
      primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0) quotient Q
        actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut data.Q L) 1 (fun _ i j =>
          (¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (quotient i)) ∧
          (¬ProhibitedSite 1 ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) (quotient j))) d := by
    rw [primeFamilyGraphOperator_eq_realMatrix P hprime hdisjoint,
      primeFamilyGraphOperator_eq_realMatrix P hprime hdisjoint]
    congr 1
    funext i j
    unfold primeRealEdgeMatrix
    have hgate := and_congr (hkeep i) (hkeep j)
    have hmat := crt_integer_edge_matrix N ell (∏ j, (d j).val) hN site r
      (data.P ∪ data.Q) data.Q Q Finset.subset_union_right (hcenterPool d) hpoolInv hQpool
      actualPaddingCoefficient (eligible (∏ j, (d j).val)) L (Real.exp (4 * J))
    have hij := congrFun (congrFun hmat i) j
    simp only [hgate]
    dsimp only [physical, quotient]
    rw [hij]
  have hUnion : (Finset.univ.biUnion P) ⊆ data.P := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hsub j hpj
  have hproj : coordinateProjection (fun i : V =>
      (actualPaddingDegree (Finset.univ.biUnion P) (physical i) : ℝ) ≤ 6 * W * J) =
      coordinateProjection (fun i : V =>
        (actualPaddingDegree (Finset.univ.biUnion P) (quotient i) : ℝ) ≤ 6 * W * J) := by
    congr 1
    funext i
    have hcdeg := crt_padding_degree N ell (Finset.univ.biUnion P)
      (fun p hp => hinv ⟨p, Finset.mem_union_left _ (hUnion hp)⟩) (site i) r
    exact congrArg (fun n : ℕ => ((n : ℝ) ≤ 6 * W * J)) hcdeg
  unfold physicalReflectionCompression quotientReflectionCompression
  dsimp only
  rw [hproj]
  congr 1
  congr 1
  exact Finset.sum_congr rfl (fun d _ => hOp d)

#print axioms reflected_compression_CRT

end ReflectedLiouville
