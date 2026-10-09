import OAI.NumberTheory.TwoPointCorrelations.FinalMain
import OAI.NumberTheory.DirichletL.Nonvanishing

set_option autoImplicit false

open OAI.TwoPointCorrelations

-- Independent readback of theorem types and axioms; no new reflected theorem is asserted.
#check eventually_prohibited_column_trace_total
#print axioms OAI.TwoPointCorrelations.eventually_prohibited_column_trace_total
#check eventually_actual_column_trace
#print axioms OAI.TwoPointCorrelations.eventually_actual_column_trace
#check uniform_designated_trace_bound
#print axioms OAI.TwoPointCorrelations.uniform_designated_trace_bound
#check BravermanDepth22Input.finite_residue_comparison
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.finite_residue_comparison
#check BravermanDepth22Input.eventually_actual_affine_word_comparison
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_affine_word_comparison
#check BravermanDepth22Input.eventually_affine_weighted_word_comparison
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_affine_weighted_word_comparison
#check bravermanDepth22Input
#print axioms OAI.TwoPointCorrelations.bravermanDepth22Input
#check eventually_prohibited_density
#print axioms OAI.TwoPointCorrelations.eventually_prohibited_density
#check BravermanDepth22Input.eventually_prohibited_row_comparison
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_prohibited_row_comparison
#check BravermanDepth22Input.eventually_variable_padding_comparison
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_variable_padding_comparison
#check BravermanDepth22Input.eventually_variable_tuple_degree_deletion
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_variable_tuple_degree_deletion
#check ModFiveThetaInput.eventually_positive_padding_cut_cost
#print axioms OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_positive_padding_cut_cost
#check BravermanDepth22Input.eventually_actual_padding_weight
#print axioms OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_padding_weight
#check primeFamilyGraphOperator_norm_le
#print axioms OAI.TwoPointCorrelations.primeFamilyGraphOperator_norm_le
#check primeFamilyGraphOperator_square_sum
#print axioms OAI.TwoPointCorrelations.primeFamilyGraphOperator_square_sum
#check noncommuting_spectral_transfer
#print axioms OAI.TwoPointCorrelations.noncommuting_spectral_transfer
#check noncommuting_spectral_transfer_max
#print axioms OAI.TwoPointCorrelations.noncommuting_spectral_transfer_max
#check weightedRoughFourier_bounds_of_sieve
#print axioms OAI.TwoPointCorrelations.weightedRoughFourier_bounds_of_sieve
#check PrimeReciprocalInput.rough_fourier
#print axioms OAI.TwoPointCorrelations.PrimeReciprocalInput.rough_fourier
#check rough_additiveQuadruples_card_le
#print axioms OAI.TwoPointCorrelations.rough_additiveQuadruples_card_le
#check modFiveThetaInput
#print axioms OAI.TwoPointCorrelations.modFiveThetaInput
#check primeReciprocalInput
#print axioms OAI.TwoPointCorrelations.primeReciprocalInput

example : BravermanDepth22Input := by exact bravermanDepth22Input
example : ModFiveThetaInput := by exact modFiveThetaInput
example : PrimeReciprocalInput := by exact primeReciprocalInput



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
