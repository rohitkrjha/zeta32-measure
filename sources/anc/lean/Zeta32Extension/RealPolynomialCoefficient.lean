module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Coefficients controlled by a real-interval supremum

This estimate permits coefficient extraction from a Vandermonde completion
using only real added nodes. Its exponential cost, unlike a crude Markov
bound of size `n^(2n)`, fits a loss proportional to the number of missing
rows times the ambient dimension.
-/

@[expose] public section

namespace Zeta32Extension

open Polynomial Set
open scoped BigOperators

theorem factorial_mul_taylor_coeff (p : ℝ[X]) (a : ℝ) (j : ℕ) :
    (j.factorial : ℝ) * (taylor a p).coeff j = (derivative^[j] p).eval a := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv]
  change (j.factorial : ℝ) * _ = ((j.factorial : ℕ) • (hasseDeriv j p)).eval a
  rw [eval_smul]
  simp only [nsmul_eq_mul]

theorem taylor_one_coeff_abs_le_chebyshev {p : ℝ[X]} {n : ℕ}
    (hdeg : p.degree ≤ n) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) (j : ℕ) :
    |(taylor 1 p).coeff j| ≤ (taylor 1 (Chebyshev.T ℝ n)).coeff j := by
  have hplus := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := j) (le_rfl : (1 : ℝ) ≤ 1) hdeg hbound
  have hminus := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := j) (le_rfl : (1 : ℝ) ≤ 1)
    (P := -p) (by simpa using hdeg) (by simpa using hbound)
  have hneg : (derivative^[j] (-p)).eval (1 : ℝ) = -(derivative^[j] p).eval 1 := by
    simp only [iterate_derivative_neg, eval_neg]
  rw [hneg] at hminus
  rw [← factorial_mul_taylor_coeff p 1 j,
    ← factorial_mul_taylor_coeff (Chebyshev.T ℝ n) 1 j] at hplus hminus
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  apply abs_le.mpr
  constructor
  · nlinarith
  · exact (mul_le_mul_iff_right₀ hf).mp hplus

theorem chebyshev_T_three_abs_le (n : ℕ) : |(Chebyshev.T ℝ n).eval 3| ≤ (7 : ℝ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num
  | more n hn hn1 =>
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    have htri := abs_sub_le
      ((2 : ℝ) * 3 * (Chebyshev.T ℝ ((n : ℤ) + 1)).eval 3) 0
      ((Chebyshev.T ℝ (n : ℤ)).eval 3)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 * 3)] at htri
    have hnext : |(Chebyshev.T ℝ ((n : ℤ) + 1)).eval 3| ≤ (7 : ℝ) ^ (n + 1) := by
      simpa using hn1
    norm_num only [pow_succ] at *
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 7) n]

theorem real_polynomial_coeff_le_of_unit_interval {p : ℝ[X]} {n : ℕ}
    (hdeg : p.degree ≤ n) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) (i : ℕ) :
    |p.coeff i| ≤ (7 : ℝ) ^ n := by
  classical
  let q := taylor (1 : ℝ) p
  let T := taylor (1 : ℝ) (Chebyshev.T ℝ n)
  have hT (j : ℕ) : 0 ≤ T.coeff j :=
    (abs_nonneg _).trans (taylor_one_coeff_abs_le_chebyshev hdeg hbound j)
  have hqdeg : q.natDegree ≤ n := by
    rw [natDegree_taylor]
    exact natDegree_le_of_degree_le hdeg
  have hcoeff : p.coeff i = ∑ j ∈ q.support,
      q.coeff j * ((X - C (1 : ℝ)) ^ j).coeff i := by
    conv_lhs => rw [← sum_taylor_eq p 1]
    simp only [Polynomial.sum_def, finsetSum_coeff, coeff_C_mul]
    rfl
  have hbin (j : ℕ) : |((X - C (1 : ℝ)) ^ j).coeff i| ≤ (2 : ℝ) ^ j := by
    rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
    simp only [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg (j.choose i) :
      (0 : ℝ) ≤ (j.choose i : ℝ))]
    exact_mod_cast Nat.choose_le_two_pow j i
  have hTdeg : T.natDegree < n + 1 := by
    simp [T, natDegree_taylor]
  calc
    |p.coeff i| ≤ ∑ j ∈ q.support, |q.coeff j * ((X - C (1 : ℝ)) ^ j).coeff i| := by
      rw [hcoeff]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ q.support, T.coeff j * (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (taylor_one_coeff_abs_le_chebyshev hdeg hbound j) (hbin j)
        (abs_nonneg _) (hT j)
    _ ≤ ∑ j ∈ Finset.range (n + 1), T.coeff j * (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp j hj).trans hqdeg))
      · intro j _ _; exact mul_nonneg (hT j) (by positivity)
    _ = T.eval 2 := (eval_eq_sum_range' hTdeg 2).symm
    _ = (Chebyshev.T ℝ n).eval 3 := by rw [taylor_eval]; norm_num
    _ ≤ |(Chebyshev.T ℝ n).eval 3| := le_abs_self _
    _ ≤ _ := chebyshev_T_three_abs_le n

theorem real_polynomial_coeff_le_interval_bound {p : ℝ[X]} {n : ℕ} {K : ℝ}
    (hK : 0 < K) (hdeg : p.degree ≤ n)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ K) (i : ℕ) :
    |p.coeff i| ≤ (7 : ℝ) ^ n * K := by
  let q : ℝ[X] := C K⁻¹ * p
  have hqdeg : q.degree ≤ n := by
    rw [show q = C K⁻¹ * p from rfl, degree_C_mul (inv_ne_zero hK.ne')]
    exact hdeg
  have hqb : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    simp only [q, eval_mul, eval_C, abs_mul, abs_inv, abs_of_pos hK]
    calc
      _ ≤ K⁻¹ * K := mul_le_mul_of_nonneg_left (hbound x hx) (by positivity)
      _ = _ := inv_mul_cancel₀ hK.ne'
  have hb := real_polynomial_coeff_le_of_unit_interval hqdeg hqb i
  simp only [q, coeff_C_mul, abs_mul, abs_inv, abs_of_pos hK] at hb
  have hm := mul_le_mul_of_nonneg_left hb hK.le
  calc
    _ = K * (K⁻¹ * |p.coeff i|) := by rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    _ ≤ K * (7 : ℝ) ^ n := hm
    _ = _ := mul_comm _ _

end Zeta32Extension
end
