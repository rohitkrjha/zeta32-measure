module
public import Zeta32Extension.PolynomialIntegralLower
public import Zeta32Extension.WeightLower

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Polynomial Set MeasureTheory
open scoped BigOperators

def factorialPolynomial (n : ℕ) (v : Fin (3*n) → ℂ) : ℂ[X] :=
  ∑ i, monomial i.val (v i * (n : ℂ)^i.val / (i.val.factorial : ℂ))

def lineAffine (n : ℕ) : ℂ[X] :=
  C ((1 : ℂ)/(2*n) + 3*Complex.I/2) + C (Complex.I/2)*X

def linePolynomial (n : ℕ) (v : Fin (3*n) → ℂ) : ℂ[X] :=
  (factorialPolynomial n v).comp (lineAffine n)

theorem factorialPolynomial_coeff (n : ℕ) (v : Fin (3*n) → ℂ) (i : Fin (3*n)) :
    (factorialPolynomial n v).coeff i.val = v i * (n : ℂ)^i.val / (i.val.factorial : ℂ) := by
  classical
  simp only [factorialPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [show j.val ≠ i.val from fun he => hji (Fin.ext he)]
  · simp

theorem factorialPolynomial_natDegree (n : ℕ) (hn : 1 ≤ n) (v : Fin (3*n) → ℂ) :
    (factorialPolynomial n v).natDegree < 3*n := by
  have hh : 0 < 3*n := by omega
  apply lt_of_le_of_lt (b := 3*n-1) _ (by omega)
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (by have hi := i.isLt; omega)

theorem linePolynomial_natDegree (n : ℕ) (hn : 1 ≤ n) (v : Fin (3*n) → ℂ) :
    (linePolynomial n v).natDegree < 3*n := by
  have hA : (lineAffine n).natDegree ≤ 1 := by
    unfold lineAffine
    exact natDegree_add_le_of_degree_le
      (by rw [natDegree_C]; omega)
      (by exact (natDegree_C_mul_le _ _).trans (by simp))
  apply lt_of_le_of_lt natDegree_comp_le
  calc
    (factorialPolynomial n v).natDegree * (lineAffine n).natDegree ≤
      (factorialPolynomial n v).natDegree * 1 := Nat.mul_le_mul_left _ hA
    _ < 3*n := by simpa using factorialPolynomial_natDegree n hn v

theorem affine_composition_cancel (d e a b : ℂ)
    (hzero : d+e*a=0) (hone : e*b=1) :
    (C d+C e*X).comp (C a+C b*X) = X := by
  simp only [add_comp, C_comp, mul_comp, X_comp]
  calc
    C d+C e*(C a+C b*X) = C (d+e*a) + C (e*b)*X := by
      simp only [map_add, map_mul]
      ring
    _ = _ := by rw [hzero, hone]; simp

theorem linePolynomial_recover (n : ℕ) (hn : 1 ≤ n) (v : Fin (3*n) → ℂ) :
    (linePolynomial n v).comp
      (C (-3+Complex.I/(n : ℂ)) + C (-2*Complex.I)*X) = factorialPolynomial n v := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold linePolynomial lineAffine
  rw [comp_assoc]
  have hzero : (1 : ℂ)/(2*n)+3*Complex.I/2 +
      (Complex.I/2)*(-3+Complex.I/(n : ℂ)) = 0 := by
    field_simp
    linear_combination Complex.I_mul_I
  have hone : (Complex.I/2)*(-2*Complex.I) = (1 : ℂ) := by
    linear_combination -Complex.I_mul_I
  rw [affine_composition_cancel _ _ _ _ hzero hone, comp_X]

theorem inverse_line_constant_norm (n : ℕ) (hn : 1 ≤ n) :
    ‖-3+Complex.I/(n : ℂ)‖ ≤ 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := norm_add_le (-3 : ℂ) (Complex.I/(n : ℂ))
  norm_num only [norm_neg, Complex.norm_ofNat, norm_div, Complex.norm_I,
    Complex.norm_natCast] at hh
  have hi : (1 : ℝ)/(n : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hnR
  linarith

theorem factorial_ratio_le (n : ℕ) (hn : 1 ≤ n) (i : Fin (3*n)) :
    (i.val.factorial : ℝ)/(n : ℝ)^i.val ≤ (3 : ℝ)^(3*n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hi : (i.val : ℝ) ≤ 3*n := by exact_mod_cast i.isLt.le
  calc
    (i.val.factorial : ℝ)/(n : ℝ)^i.val ≤ (i.val : ℝ)^i.val/(n : ℝ)^i.val :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow i.val) (by positivity)
    _ ≤ (3*(n : ℝ))^i.val/(n : ℝ)^i.val := by gcongr
    _ = (3 : ℝ)^i.val := by rw [mul_pow]; field_simp
    _ ≤ (3 : ℝ)^(3*n) := pow_le_pow_right₀ (by norm_num) i.isLt.le

theorem factorialPolynomial_norm_recover (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (3*n) → ℂ) (i : Fin (3*n)) :
    ‖v i‖ = ((i.val.factorial : ℝ)/(n : ℝ)^i.val) *
      ‖(factorialPolynomial n v).coeff i.val‖ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf0 : (i.val.factorial : ℝ) ≠ 0 := by positivity
  rw [factorialPolynomial_coeff, norm_div, norm_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_natCast]
  field_simp

theorem factorial_coefficient_square_le_integral (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (3*n) → ℂ) (i : Fin (3*n)) :
    ‖v i‖^2 ≤ 64*((3*n : ℕ) : ℝ)^4*(111132 : ℝ)^(3*n) *
      ∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2 := by
  have hb := polynomial_affine_coeff_sq_le_integral
    (linePolynomial_natDegree n hn v) (inverse_line_constant_norm n hn)
    (show ‖(-2 : ℂ)*Complex.I‖ ≤ 2 by norm_num [norm_mul]) i.val
  rw [linePolynomial_recover n hn v] at hb
  have hr := factorial_ratio_le n hn i
  have hrec : ‖v i‖ ≤ (3 : ℝ)^(3*n) * ‖(factorialPolynomial n v).coeff i.val‖ := by
    rw [factorialPolynomial_norm_recover n hn v i]
    exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hrec 2
  calc
    ‖v i‖^2 ≤ ((3 : ℝ)^(3*n))^2 * ‖(factorialPolynomial n v).coeff i.val‖^2 := by
      simpa only [mul_pow] using hsq
    _ ≤ ((3 : ℝ)^(3*n))^2 *
      (64*((3*n : ℕ) : ℝ)^4*(12348 : ℝ)^(3*n) *
        ∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      have he : ((3 : ℝ)^2)^(3*n) = ((3 : ℝ)^(3*n))^2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [show (111132 : ℝ) = 3^2*12348 by norm_num,
        mul_pow (3^2 : ℝ) 12348 (3*n), he]
      ring

/-- The quantitative polynomial-conditioning estimate for the actual
factorial-normalized basis. No Gram or minor hypothesis occurs here. -/
theorem factorial_polynomial_l2_lower (n : ℕ) (hn : 1 ≤ n) (v : Fin (3*n) → ℂ) :
    (∑ i, ‖v i‖^2) ≤ 64*((3*n : ℕ) : ℝ)^5*(111132 : ℝ)^(3*n) *
      ∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2 := by
  calc
    (∑ i, ‖v i‖^2) ≤ ∑ _i : Fin (3*n),
      64*((3*n : ℕ) : ℝ)^4*(111132 : ℝ)^(3*n) *
        ∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2 :=
      Finset.sum_le_sum fun i _ => factorial_coefficient_square_le_integral n hn v i
    _ = _ := by simp; ring

theorem linePolynomial_eval (n : ℕ) (hn : 1 ≤ n) (v : Fin (3*n) → ℂ) (s : ℝ) :
    (linePolynomial n v).eval (s : ℂ) =
      ∑ i, v i * (Zeta32.Analytic.Contour.tpt ((n : ℝ)*(3+s)/2))^i.val /
        (i.val.factorial : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (n : ℂ) * ((1 : ℂ)/(2*n)+3*Complex.I/2 + (Complex.I/2)*(s : ℂ)) =
      Zeta32.Analytic.Contour.tpt ((n : ℝ)*(3+s)/2) := by
    unfold Zeta32.Analytic.Contour.tpt
    push_cast
    field_simp
    ring
  simp only [linePolynomial, eval_comp, lineAffine, eval_add, eval_C, eval_mul, eval_X,
    factorialPolynomial, eval_finsetSum, eval_monomial]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = v i * ((n : ℂ) * ((1 : ℂ)/(2*n)+3*Complex.I/2 +
      (Complex.I/2)*(s : ℂ)))^i.val / (i.val.factorial : ℂ) := by rw [mul_pow]; ring
    _ = _ := by rw [he]

end
end Zeta32Extension
end
