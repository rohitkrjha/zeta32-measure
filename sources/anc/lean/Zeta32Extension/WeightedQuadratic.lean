module
public import Zeta32Extension.ConditioningCost
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Zeta32 Zeta32.Analytic Zeta32.Analytic.Contour
open Polynomial Set MeasureTheory Filter
open scoped BigOperators Topology

def basisCombination (n : ℕ) (v : Fin (3*n) → ℂ) (y : ℝ) : ℂ :=
  ∑ i, v i * (tpt y)^i.val / (i.val.factorial : ℂ)

def weightedQuadratic (r : ℚ) (n : ℕ) (v : Fin (3*n) → ℂ) : ℝ :=
  ∫ y, ‖basisCombination n v y‖^2 * gramWeight r n y

theorem continuous_heinePhi (r : ℚ) (n : ℕ) : Continuous (heinePhi r n) := by
  have hprod (m : ℕ) : Continuous (fun y : ℝ => ∏ j ∈ Finset.Icc 1 m, (tpt y+(j : ℂ))) :=
    continuous_finsetProd _ fun j _ => continuous_tpt.add continuous_const
  have hR : Continuous (fun y : ℝ => Rfun n (tpt y)) := by
    unfold Rfun
    apply (hprod n).pow 4 |>.div (hprod (5*n))
    intro y
    exact prod_add_nat_ne_zero (5*n) (by rw [tpt_re]; norm_num)
  have hw : Continuous (wfun r) := by
    have hr : Continuous (fun y => (rho y : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_rho
    have hd : Continuous (fun y => (rhoDeriv y : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_rhoDeriv
    change Continuous (fun y => wfun r y)
    simp_rw [wfun_eq]
    fun_prop
  exact (continuous_tpt.mul hR).mul hw

theorem continuous_gramWeight (r : ℚ) (n : ℕ) : Continuous (gramWeight r n) :=
  continuous_const.mul (continuous_heinePhi r n).norm

theorem continuous_basisCombination (n : ℕ) (v : Fin (3*n) → ℂ) :
    Continuous (basisCombination n v) := by
  unfold basisCombination
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_tpt.pow i.val)).div_const _

theorem integrable_gram_moment (r : ℚ) (n e : ℕ) :
    Integrable (fun y => ‖tpt y‖^e * gramWeight r n y) := by
  have he : (fun y => ‖tpt y‖^e * gramWeight r n y) =
      (fun y => (Sn n : ℝ) * ‖tpt y * (tpt y^e * Rfun n (tpt y)) * wfun r y‖) := by
    funext y
    simp only [gramWeight, heinePhi, norm_mul, norm_pow]
    ring
  rw [he]
  exact (logistic_integrable_entry r n e).norm.const_mul _

theorem integrable_weighted_basis_square (r : ℚ) (n : ℕ)
    (v : Fin (3*n) → ℂ) (i : Fin (3*n)) :
    Integrable (fun y => ‖v i * (tpt y)^i.val / (i.val.factorial : ℂ)‖^2 *
      gramWeight r n y) := by
  have he : (fun y => ‖v i * (tpt y)^i.val / (i.val.factorial : ℂ)‖^2 *
      gramWeight r n y) = (fun y => (‖v i‖^2/(i.val.factorial : ℝ)^2) *
        (‖tpt y‖^(2*i.val) * gramWeight r n y)) := by
    funext y
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow, mul_pow,
      ← pow_mul, Nat.mul_comm i.val 2]
    ring
  rw [he]
  exact (integrable_gram_moment r n (2*i.val)).const_mul _

theorem integrable_weightedQuadratic (r : ℚ) (n : ℕ) (v : Fin (3*n) → ℂ) :
    Integrable (fun y => ‖basisCombination n v y‖^2 * gramWeight r n y) := by
  have hi : Integrable (fun y => ((3*n : ℕ) : ℝ) *
      ∑ i, ‖v i * (tpt y)^i.val / (i.val.factorial : ℂ)‖^2 * gramWeight r n y) :=
    (integrable_finsetSum _ fun i _ => integrable_weighted_basis_square r n v i).const_mul _
  apply hi.mono' (((continuous_basisCombination n v).norm.pow 2).mul
    (continuous_gramWeight r n)).aestronglyMeasurable
  apply Eventually.of_forall
  intro y
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gramWeight_nonneg r n y))]
  have hn := pow_le_pow_left₀ (norm_nonneg (basisCombination n v y))
    (norm_sum_le (s := Finset.univ) (fun i => v i * (tpt y)^i.val / (i.val.factorial : ℂ))) 2
  have hs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (3*n))))
    (f := fun i => ‖v i * (tpt y)^i.val / (i.val.factorial : ℂ)‖)
  have hb : ‖basisCombination n v y‖^2 ≤ ((3*n : ℕ) : ℝ) *
      ∑ i, ‖v i * (tpt y)^i.val / (i.val.factorial : ℂ)‖^2 := by
    exact hn.trans (by simpa using hs)
  convert mul_le_mul_of_nonneg_right hb (gramWeight_nonneg r n y) using 1
  simp only [← Finset.sum_mul, mul_assoc]

theorem weightedQuadratic_nonneg (r : ℚ) (n : ℕ) (v : Fin (3*n) → ℂ) :
    0 ≤ weightedQuadratic r n v :=
  integral_nonneg fun y => mul_nonneg (sq_nonneg _) (gramWeight_nonneg r n y)

theorem affine_interval_integral (f : ℝ → ℝ) (N : ℝ) (hN : 0 ≤ N) :
    (N/2) * (∫ s in Icc (-1 : ℝ) 1, f (N*(3+s)/2)) =
      ∫ y in Icc N (2*N), f y := by
  have he (s : ℝ) : N*(3+s)/2 = (N/2)*s+3*N/2 := by ring
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hh := intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    f (N/2) (3*N/2)
  rw [show (N/2)*(-1)+3*N/2 = N by ring,
    show (N/2)*1+3*N/2 = 2*N by ring] at hh
  rw [intervalIntegral.integral_of_le (by linarith : N ≤ 2*N),
    ← integral_Icc_eq_integral_Ioc] at hh
  exact hh

theorem weightedQuadratic_interval_lower (r : ℚ) (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (3*n) → ℂ) :
    (Real.exp (-22*n)/2) *
      (∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2) ≤
        weightedQuadratic r n v := by
  let f : ℝ → ℝ := fun y => ‖basisCombination n v y‖^2 * gramWeight r n y
  have hf : Continuous f :=
    ((continuous_basisCombination n v).norm.pow 2).mul (continuous_gramWeight r n)
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hline (x : ℝ) : (linePolynomial n v).eval (x : ℂ) =
      basisCombination n v ((n : ℝ)*(3+x)/2) := linePolynomial_eval n hn v x
  have hfirst : (Real.exp (-22*n)/2) *
      (∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2) ≤
        (n : ℝ)/2 * ∫ x in Icc (-1 : ℝ) 1, f ((n : ℝ)*(3+x)/2) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_mono_on
      (continuous_const.mul (((linePolynomial n v).continuous.comp
        Complex.continuous_ofReal).norm.pow 2)).integrableOn_Icc
      (continuous_const.mul (hf.comp (by fun_prop))).integrableOn_Icc measurableSet_Icc
    intro x hx
    have hw := gramWeight_scaled_lower r n hn ((3+x)/2) (by linarith [hx.1])
      (by linarith [hx.2])
    rw [show (n : ℝ)*((3+x)/2) = (n : ℝ)*(3+x)/2 by ring] at hw
    dsimp only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
    rw [hline]
    dsimp [f]
    have hh := mul_le_mul_of_nonneg_right hw
      (sq_nonneg ‖basisCombination n v ((n : ℝ)*(3+x)/2)‖)
    nlinarith only [hh]
  have hsecond : (n : ℝ)/2 * ∫ x in Icc (-1 : ℝ) 1, f ((n : ℝ)*(3+x)/2) ≤
      weightedQuadratic r n v := by
    rw [affine_interval_integral f (n : ℝ) hnR]
    exact setIntegral_le_integral (integrable_weightedQuadratic r n v)
      (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (gramWeight_nonneg r n y))
  exact hfirst.trans hsecond

/-- Actual positive integral conditioning, uniform in the rational parameter.
This theorem still does not identify any matrix determinant or minor. -/
theorem weightedQuadratic_eventually_lower :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℚ, ∀ v : Fin (3*n) → ℂ,
      Real.exp (-60*n) * (∑ i, ‖v i‖^2) ≤ weightedQuadratic r n v := by
  filter_upwards [eventually_conditioning_cost, eventually_ge_atTop 1] with n hcost hn
  intro r v
  have hp := factorial_polynomial_l2_lower n hn v
  have hw := weightedQuadratic_interval_lower r n hn v
  have hI : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2 :=
    integral_nonneg fun x => sq_nonneg _
  have hcoeff : Real.exp (-60*n) * (64*((3*n : ℕ) : ℝ)^5*(111132 : ℝ)^(3*n)) ≤
      Real.exp (-22*n)/2 := by
    have hh := mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg (-60*n))
    have he : Real.exp (-60*n)*Real.exp (38*n) = Real.exp (-22*n) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he] at hh
    nlinarith only [hh]
  calc
    _ ≤ Real.exp (-60*n) *
      (64*((3*n : ℕ) : ℝ)^5*(111132 : ℝ)^(3*n) *
        ∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2) :=
          mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ ≤ (Real.exp (-22*n)/2) *
      (∫ x in Icc (-1 : ℝ) 1, ‖(linePolynomial n v).eval (x : ℂ)‖^2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoeff hI
    _ ≤ _ := hw

end
end Zeta32Extension
end
