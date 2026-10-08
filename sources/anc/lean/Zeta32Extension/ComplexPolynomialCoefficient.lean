module
public import Zeta32Extension.RealPolynomialCoefficient
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Polynomial Set
open scoped BigOperators

/-- Apply a real-linear functional to every complex coefficient. -/
def realLinearPolynomial (f : ℂ →ₗ[ℝ] ℝ) (p : ℂ[X]) : ℝ[X] :=
  .ofFinsupp (.ofCoeff (p.toFinsupp.coeff.mapRange f (map_zero f)))

@[simp] theorem realLinearPolynomial_coeff (f : ℂ →ₗ[ℝ] ℝ) (p : ℂ[X]) (i : ℕ) :
    (realLinearPolynomial f p).coeff i = f (p.coeff i) := by rfl

theorem realLinearPolynomial_natDegree_le (f : ℂ →ₗ[ℝ] ℝ) (p : ℂ[X]) :
    (realLinearPolynomial f p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [coeff_eq_zero_of_natDegree_lt hi]

theorem realLinearPolynomial_eval (f : ℂ →ₗ[ℝ] ℝ) (p : ℂ[X]) (x : ℝ) :
    (realLinearPolynomial f p).eval x = f (p.eval (x : ℂ)) := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le (realLinearPolynomial_natDegree_le f p)) x,
    eval_eq_sum_range' (Nat.lt_succ_self p.natDegree) (x : ℂ), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [realLinearPolynomial_coeff]
  have he : p.coeff i * (x : ℂ)^i = (x^i : ℝ) • p.coeff i := by
    simp [Algebra.smul_def, mul_comm]
  rw [he, map_smul]
  simp [mul_comm]

theorem complex_polynomial_coeff_le_interval_bound {p : ℂ[X]} {h : ℕ} {M : ℝ}
    (hM : 0 < M) (hdeg : p.natDegree ≤ h)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M) (i : ℕ) :
    ‖p.coeff i‖ ≤ 2 * (7 : ℝ)^h * M := by
  have hre : |(p.coeff i).re| ≤ (7 : ℝ)^h * M := by
    apply real_polynomial_coeff_le_interval_bound (p := realLinearPolynomial Complex.reLm p) hM
      (degree_le_of_natDegree_le ((realLinearPolynomial_natDegree_le _ p).trans hdeg))
    intro x hx
    rw [realLinearPolynomial_eval]
    exact (Complex.abs_re_le_norm _).trans (hbound x hx)
  have him : |(p.coeff i).im| ≤ (7 : ℝ)^h * M := by
    apply real_polynomial_coeff_le_interval_bound (p := realLinearPolynomial Complex.imLm p) hM
      (degree_le_of_natDegree_le ((realLinearPolynomial_natDegree_le _ p).trans hdeg))
    intro x hx
    rw [realLinearPolynomial_eval]
    exact (Complex.abs_im_le_norm _).trans (hbound x hx)
  have ht := Complex.norm_le_abs_re_add_abs_im (p.coeff i)
  linarith

theorem complex_polynomial_coeff_le_interval_bound_nonneg {p : ℂ[X]} {h : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hdeg : p.natDegree ≤ h)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M) (i : ℕ) :
    ‖p.coeff i‖ ≤ 2 * (7 : ℝ)^h * M := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpow : 0 < 2*(7 : ℝ)^h := by positivity
  have hMp : 0 < M + ε/(2*(7 : ℝ)^h) := by positivity
  have hb := complex_polynomial_coeff_le_interval_bound hMp hdeg
    (fun x hx => (hbound x hx).trans (le_add_of_nonneg_right (by positivity))) i
  convert hb using 1
  field_simp

theorem real_pow_sub_le_on_unit_interval (j : ℕ) {s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |s^j - t^j| ≤ (j : ℝ) * |s-t| := by
  have hmax : max |s| |t| ≤ (1 : ℝ) :=
    max_le (abs_le.mpr hs) (abs_le.mpr ht)
  calc
    |s^j-t^j| ≤ |s-t| * j * max |s| |t|^(j-1) := abs_pow_sub_pow_le ..
    _ ≤ |s-t| * j * (1 : ℝ)^(j-1) := by gcongr
    _ = _ := by simp [mul_comm]

theorem complex_polynomial_lipschitz_on_unit_interval {p : ℂ[X]} {h : ℕ} {M : ℝ}
    (hM : 0 < M) (hdeg : p.natDegree < h)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M)
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖p.eval (s : ℂ) - p.eval (t : ℂ)‖ ≤ 2*(h : ℝ)^2*(7 : ℝ)^h*M*|s-t| := by
  have hc := complex_polynomial_coeff_le_interval_bound hM hdeg.le hbound
  rw [eval_eq_sum_range' hdeg (s : ℂ), eval_eq_sum_range' hdeg (t : ℂ),
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ Finset.range h, (p.coeff i * (s : ℂ)^i - p.coeff i * (t : ℂ)^i)‖
      ≤ ∑ i ∈ Finset.range h, ‖p.coeff i * (s : ℂ)^i - p.coeff i * (t : ℂ)^i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range h, 2*(7 : ℝ)^h*M * h * |s-t| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, norm_mul]
      have he : ‖(s : ℂ)^i - (t : ℂ)^i‖ = |s^i-t^i| := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      rw [he]
      calc
        _ ≤ (2*(7 : ℝ)^h*M) * ((i : ℝ)*|s-t|) :=
          mul_le_mul (hc i) (real_pow_sub_le_on_unit_interval i hs ht)
            (abs_nonneg _) (by positivity)
        _ ≤ _ := by
          have hiR : (i : ℝ) ≤ h := by exact_mod_cast (Finset.mem_range.mp hi).le
          nlinarith [mul_le_mul_of_nonneg_right hiR
            (show 0 ≤ 2*(7 : ℝ)^h*M*|s-t| by positivity)]
    _ = _ := by simp; ring

/-- The coefficient cost of an affine substitution is exponential, not
factorial. In the application A=4 and B=2. -/
theorem affine_power_coeff_norm_le (a b : ℂ) (A B : ℝ)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (j i : ℕ) :
    ‖((C a + C b * X)^j).coeff i‖ ≤ (A+B)^j := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  induction j generalizing i with
  | zero =>
    simp only [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ j ih =>
    rw [pow_succ, mul_add, coeff_add, coeff_mul_C]
    have hm : ∀ k, ‖((C a + C b * X)^j).coeff k * a‖ ≤ (A+B)^j * A := by
      intro k
      rw [norm_mul]
      exact mul_le_mul (ih k) ha (norm_nonneg _) (by positivity)
    cases i with
    | zero =>
      simp only [← mul_assoc, coeff_mul_X_zero, add_zero]
      calc
        _ ≤ (A+B)^j*A := hm 0
        _ ≤ (A+B)^(j+1) := by rw [pow_succ]; gcongr; linarith
    | succ i =>
      rw [← mul_assoc, coeff_mul_X, coeff_mul_C]
      calc
        _ ≤ ‖((C a + C b * X)^j).coeff (i+1)*a‖ +
          ‖((C a + C b * X)^j).coeff i*b‖ := norm_add_le _ _
        _ ≤ (A+B)^j*A + (A+B)^j*B := by
          apply add_le_add (hm (i+1))
          rw [norm_mul]
          exact mul_le_mul (ih i) hb (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem polynomial_affine_coeff_le {p : ℂ[X]} {h : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hdeg : p.natDegree < h)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M)
    {a b : ℂ} (ha : ‖a‖ ≤ 4) (hb : ‖b‖ ≤ 2) (i : ℕ) :
    ‖(p.comp (C a + C b*X)).coeff i‖ ≤ 2*(h : ℝ)*(42 : ℝ)^h*M := by
  classical
  have hc := complex_polynomial_coeff_le_interval_bound_nonneg hM hdeg.le hbound
  have hp : p = ∑ j ∈ Finset.range h, C (p.coeff j)*X^j :=
    p.as_sum_range_C_mul_X_pow' hdeg
  rw [hp, sum_comp, finsetSum_coeff]
  simp only [mul_comp, C_comp, pow_comp, X_comp, coeff_C_mul]
  calc
    ‖∑ j ∈ Finset.range h, p.coeff j * ((C a+C b*X)^j).coeff i‖ ≤
      ∑ j ∈ Finset.range h, ‖p.coeff j * ((C a+C b*X)^j).coeff i‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range h, (2*(7 : ℝ)^h*M)*(6 : ℝ)^h := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      have hpow : ‖((C a+C b*X)^j).coeff i‖ ≤ (6 : ℝ)^h := by
        apply le_trans (affine_power_coeff_norm_le a b 4 2 ha hb j i)
        norm_num only [show (4 : ℝ)+2=6 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hj).le
      exact mul_le_mul (hc j) hpow (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [show (42 : ℝ) = 7*6 by norm_num, mul_pow]
      ring

end
end Zeta32Extension
end
