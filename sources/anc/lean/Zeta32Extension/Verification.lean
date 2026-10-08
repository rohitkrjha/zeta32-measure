module
public import Zeta32Extension.ExponentCorollary
import Lean.Util.CollectAxioms

open Lean Elab Command

/- The explicit list also audits public theorem aliases rather than counting
only constants with the thmInfo tag. Every source theorem in this extension
is listed; its type must be a proposition and its full axiom closure is checked. -/
run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names : Array Name := #[
    `Zeta32Extension.D_eval_neg_choose,
    `Zeta32Extension.Fn_eq_product,
    `Zeta32Extension.Rfun_lower,
    `Zeta32Extension.Sn_log_lower,
    `Zeta32Extension.abs_scaled_residue_le,
    `Zeta32Extension.abs_scaled_rs_le,
    `Zeta32Extension.abs_scaled_slope_le,
    `Zeta32Extension.affine_composition_cancel,
    `Zeta32Extension.affine_interval_integral,
    `Zeta32Extension.affine_power_coeff_norm_le,
    `Zeta32Extension.approximationExponents_bounded,
    `Zeta32Extension.baseGram_det,
    `Zeta32Extension.bilinear_le_of_entry_bound,
    `Zeta32Extension.chebyshev_T_three_abs_le,
    `Zeta32Extension.complexInverseFactorials_det,
    `Zeta32Extension.complex_polynomial_coeff_le_interval_bound,
    `Zeta32Extension.complex_polynomial_coeff_le_interval_bound_nonneg,
    `Zeta32Extension.complex_polynomial_lipschitz_on_unit_interval,
    `Zeta32Extension.conditioning_base_le_exp,
    `Zeta32Extension.continuous_basisCombination,
    `Zeta32Extension.continuous_gramWeight,
    `Zeta32Extension.continuous_heinePhi,
    `Zeta32Extension.cosh_le_exp_nonneg,
    `Zeta32Extension.denominator_bound,
    `Zeta32Extension.denominator_bound_of_local_decay,
    `Zeta32Extension.denominator_bound_of_uniformMinors,
    `Zeta32Extension.det_add_le_of_all_minors,
    `Zeta32Extension.det_le_of_bilinear_gram,
    `Zeta32Extension.det_le_of_bilinear_l2,
    `Zeta32Extension.eventually_conditioning_cost,
    `Zeta32Extension.eventually_exists_prime_not_dvd_in_log_window,
    `Zeta32Extension.eventually_primeLogInterval_gt_quarter,
    `Zeta32Extension.exists_gram_whitening,
    `Zeta32Extension.exists_prime_not_dvd_of_log_lt_interval,
    `Zeta32Extension.exp_neg_two_le_inv_cosh_sq,
    `Zeta32Extension.factorialPolynomial_coeff,
    `Zeta32Extension.factorialPolynomial_natDegree,
    `Zeta32Extension.factorialPolynomial_norm_recover,
    `Zeta32Extension.factorial_coefficient_square_le_integral,
    `Zeta32Extension.factorial_mul_taylor_coeff,
    `Zeta32Extension.factorial_polynomial_l2_lower,
    `Zeta32Extension.factorial_ratio_le,
    `Zeta32Extension.fin_selected_remove_card,
    `Zeta32Extension.finite_goodRationalApproximations,
    `Zeta32Extension.finite_rat_den_le_abs_sub_lt_one,
    `Zeta32Extension.gramKernel_sum,
    `Zeta32Extension.gramWeight_nonneg,
    `Zeta32Extension.gramWeight_scaled_lower,
    `Zeta32Extension.hilbert_det_norm_le_pow,
    `Zeta32Extension.integrable_baseGram_entry,
    `Zeta32Extension.integrable_gramKernel,
    `Zeta32Extension.integrable_gram_moment,
    `Zeta32Extension.integrable_signedKernel,
    `Zeta32Extension.integrable_weightedQuadratic,
    `Zeta32Extension.integrable_weighted_basis_square,
    `Zeta32Extension.inverseFactorials_det,
    `Zeta32Extension.inverse_line_constant_norm,
    `Zeta32Extension.irrationalityExponent_bounds,
    `Zeta32Extension.linePolynomial_eval,
    `Zeta32Extension.linePolynomial_natDegree,
    `Zeta32Extension.linePolynomial_recover,
    `Zeta32Extension.local_decay,
    `Zeta32Extension.local_decay_of_uniformMinors,
    `Zeta32Extension.mixed_minor_le,
    `Zeta32Extension.nearby_Qtilde_eventually,
    `Zeta32Extension.nearby_Qtilde_le,
    `Zeta32Extension.norm_star_dotProduct_self,
    `Zeta32Extension.normalizedPencil_apply,
    `Zeta32Extension.normalizedPencil_bilinear,
    `Zeta32Extension.normalizedPencil_bilinear_le,
    `Zeta32Extension.normalizedPencil_det,
    `Zeta32Extension.normalizedPencil_integral,
    `Zeta32Extension.normalizedPencil_sub,
    `Zeta32Extension.normalizedPencil_sub_le,
    `Zeta32Extension.normalizedSlope_crude,
    `Zeta32Extension.normalizedSlope_le_exp,
    `Zeta32Extension.normalized_Rfun_lower,
    `Zeta32Extension.peak_square_integral_lower,
    `Zeta32Extension.pencil_stability_eventually,
    `Zeta32Extension.pencil_stability_of_uniformMinors,
    `Zeta32Extension.perturbation_factor_le,
    `Zeta32Extension.perturbed_pencil_bilinear_le,
    `Zeta32Extension.polynomial_affine_coeff_le,
    `Zeta32Extension.polynomial_affine_coeff_sq_le_integral,
    `Zeta32Extension.polynomial_peak_square_le_integral,
    `Zeta32Extension.positiveGram_apply,
    `Zeta32Extension.positiveGram_det,
    `Zeta32Extension.positiveGram_eventually_lower,
    `Zeta32Extension.positiveGram_eventually_posDef,
    `Zeta32Extension.positiveGram_isHermitian,
    `Zeta32Extension.positiveGram_posSemidef,
    `Zeta32Extension.positiveGram_quadratic,
    `Zeta32Extension.positiveHeine_eventually_le,
    `Zeta32Extension.positiveHeine_nonneg,
    `Zeta32Extension.positive_andreief_integrand,
    `Zeta32Extension.positive_energy_bound_exp,
    `Zeta32Extension.positive_heine_scaled,
    `Zeta32Extension.primeLogInterval_eq_theta_sub,
    `Zeta32Extension.rawPencil_det,
    `Zeta32Extension.realLinearPolynomial_coeff,
    `Zeta32Extension.realLinearPolynomial_eval,
    `Zeta32Extension.realLinearPolynomial_natDegree_le,
    `Zeta32Extension.real_polynomial_coeff_le_interval_bound,
    `Zeta32Extension.real_polynomial_coeff_le_of_unit_interval,
    `Zeta32Extension.real_pow_sub_le_on_unit_interval,
    `Zeta32Extension.scaled_rs_eq,
    `Zeta32Extension.signedKernel_sum,
    `Zeta32Extension.sum_norm_le_sqrt_card_vectorL2,
    `Zeta32Extension.tanh_ge_half,
    `Zeta32Extension.taylor_one_coeff_abs_le_chebyshev,
    `Zeta32Extension.two_mem_approximationExponents,
    `Zeta32Extension.vectorL2_eq_norm,
    `Zeta32Extension.vectorL2_le_of_weighted_lower,
    `Zeta32Extension.vectorL2_star,
    `Zeta32Extension.vertical_root_lower,
    `Zeta32Extension.vertical_root_upper,
    `Zeta32Extension.weightedQuadratic_eventually_lower,
    `Zeta32Extension.weightedQuadratic_interval_lower,
    `Zeta32Extension.weightedQuadratic_nonneg,
    `Zeta32Extension.weighted_cauchy_schwarz,
    `Zeta32Extension.weighted_norm_memLp,
    `Zeta32Extension.wfun_lower,
    `Zeta32Extension.whitening_quadratic]
  for name in names do
    let info ← getConstInfo name
    let isProposition ← liftTermElabM <| Meta.isProp info.type
    unless isProposition do
      throwError "Expected a proposition-valued declaration {name}"
    for axName in (← collectAxioms name) do
      unless permitted.contains axName do
        throwError "Unexpected axiom {axName} in {name}"
  logInfo m!"PASS: {names.size} explicitly listed extension theorems; only standard axioms."
  logInfo "UNCONDITIONAL ENDPOINT: denominator exponent 10,000 for every fixed rational r."
  logInfo "UNCONDITIONAL COROLLARY: 2 <= irrationalityExponent (Cr r) <= 10,000."
  logInfo "UniformMinors is bypassed by the checked direct Gram-determinant comparison."

#check Zeta32Extension.denominator_bound
#print axioms Zeta32Extension.denominator_bound
#check Zeta32Extension.irrationalityExponent_bounds
#print axioms Zeta32Extension.irrationalityExponent_bounds
#check Zeta32Extension.positiveGram_eventually_lower
#check Zeta32Extension.positiveGram_det
