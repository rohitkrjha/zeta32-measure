module
public import Zeta32Extension.PolynomialConditioning
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Filter
open scoped Topology

theorem conditioning_base_le_exp : (111132 : ℝ) ≤ Real.exp 12 := by
  have he : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    (111132 : ℝ) ≤ (27/10 : ℝ)^12 := by norm_num
    _ ≤ (Real.exp 1)^12 := pow_le_pow_left₀ (by norm_num) he 12
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

theorem eventually_conditioning_cost :
    ∀ᶠ n : ℕ in atTop,
      128*((3*n : ℕ) : ℝ)^5*(111132 : ℝ)^(3*n) ≤ Real.exp (38*n) := by
  have ht : Tendsto (fun n : ℕ => (128*(3 : ℝ)^5) *
      ((n : ℝ)^5*Real.exp (-(n : ℝ)))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp
      tendsto_natCast_atTop_atTop).const_mul (128*(3 : ℝ)^5)
  have hsmall := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall] with n hn
  have hpoly : 128*((3*n : ℕ) : ℝ)^5 ≤ Real.exp (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn.le (Real.exp_nonneg (n : ℝ))
    have he : (128*(3 : ℝ)^5) * ((n : ℝ)^5*Real.exp (-(n : ℝ))) *
        Real.exp (n : ℝ) = 128*((3*n : ℕ) : ℝ)^5 := by
      rw [show (128*(3 : ℝ)^5) * ((n : ℝ)^5*Real.exp (-(n : ℝ))) *
        Real.exp (n : ℝ) = (128*(3 : ℝ)^5)*(n : ℝ)^5 *
          (Real.exp (-(n : ℝ))*Real.exp (n : ℝ)) by ring,
        ← Real.exp_add]
      simp
      ring
    simpa only [he, one_mul] using hh
  have hbase : (111132 : ℝ)^(3*n) ≤ Real.exp (36*n) := by
    calc
      _ ≤ (Real.exp 12)^(3*n) := pow_le_pow_left₀ (by norm_num) conditioning_base_le_exp _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc
    _ ≤ Real.exp (n : ℝ)*Real.exp (36*n) :=
      mul_le_mul hpoly hbase (by positivity) (by positivity)
    _ = Real.exp (37*n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh : (0 : ℝ) ≤ n := by positivity
      linarith)

end
end Zeta32Extension
end
