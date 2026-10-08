import OAI.NumberTheory.TwoPointCorrelations.FinalMain
import OAI.NumberTheory.DirichletL.Nonvanishing

set_option autoImplicit false

-- Exact source names and kernel axiom readback for the manuscript inputs.
#check OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
#print axioms OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
#check OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
#print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re

example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

open OAI.TwoPointCorrelations

#check maskedClosedWord_residue_average
#print axioms OAI.TwoPointCorrelations.maskedClosedWord_residue_average
#check eventually_actual_matrix_trace
#print axioms OAI.TwoPointCorrelations.eventually_actual_matrix_trace
#check BravermanDepth22Input.eventually_residue_comparison
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_residue_comparison
#check AC0Circuit.dyadic_comparison
#print axioms OAI.TwoPointCorrelations.AC0Circuit.dyadic_comparison
#check bravermanDegree_polynomial
#print axioms OAI.TwoPointCorrelations.bravermanDegree_polynomial
#check bravermanDegree_polynomial_positive
#print axioms OAI.TwoPointCorrelations.bravermanDegree_polynomial_positive
