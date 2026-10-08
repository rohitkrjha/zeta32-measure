module
public import Zeta32Extension.GramQuadratic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Zeta32 Zeta32.Analytic Zeta32.Analytic.Contour
open MeasureTheory Matrix Filter
open scoped BigOperators ComplexConjugate

def signedKernel (r : ℚ) (n : ℕ) (i j : Fin (3*n)) (y : ℝ) : ℂ :=
  (Sn n : ℂ) * (heineF n i y * heineG r n j y) /
    ((i.val.factorial : ℂ) * (j.val.factorial : ℂ))

theorem integrable_signedKernel (r : ℚ) (n : ℕ) (i j : Fin (3*n)) :
    Integrable (signedKernel r n i j) := by
  unfold signedKernel
  simp_rw [heineF_mul_heineG]
  exact ((logistic_integrable_entry r n _).const_mul _).div_const _

theorem normalizedPencil_integral (r : ℚ) (n : ℕ) (i j : Fin (3*n)) :
    (normalizedPencil r n (Cr r) i j : ℂ) = ∫ y, signedKernel r n i j y := by
  rw [normalizedPencil_apply]
  simp only [signedKernel, heineF_mul_heineG, integral_div, integral_const_mul,
    logistic_representation]
  push_cast
  rfl

theorem signedKernel_sum (r : ℚ) (n : ℕ) (u v : Fin (3*n) → ℂ) (y : ℝ) :
    (∑ i, ∑ j, u i * signedKernel r n i j y * v j) =
      basisCombination n u y * basisCombination n v y *
        ((Sn n : ℂ) * heinePhi r n y) := by
  simp only [basisCombination, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [signedKernel, heineF, heineG]
  ring

theorem normalizedPencil_bilinear (r : ℚ) (n : ℕ) (u v : Fin (3*n) → ℂ) :
    u ⬝ᵥ ((normalizedPencil r n (Cr r)).map Complex.ofReal *ᵥ v) =
      ∫ y, basisCombination n u y * basisCombination n v y *
        ((Sn n : ℂ) * heinePhi r n y) := by
  have hi (i j : Fin (3*n)) :
      Integrable (fun y => u i * signedKernel r n i j y * v j) :=
    ((integrable_signedKernel r n i j).const_mul _).mul_const _
  calc
    _ = ∑ i, ∑ j, ∫ y, u i * signedKernel r n i j y * v j := by
      simp only [dotProduct, mulVec, Matrix.map_apply, normalizedPencil_integral,
        integral_mul_const, integral_const_mul, Finset.mul_sum, mul_assoc]
    _ = ∫ y, ∑ i, ∑ j, u i * signedKernel r n i j y * v j := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hi i j)).symm
    _ = _ := by simp_rw [signedKernel_sum]

theorem weighted_norm_memLp (r : ℚ) (n : ℕ) (v : Fin (3*n) → ℂ) :
    MemLp (fun y => ‖basisCombination n v y‖ * Real.sqrt (gramWeight r n y)) 2 := by
  apply (memLp_two_iff_integrable_sq
    ((continuous_basisCombination n v).norm.mul
      (continuous_gramWeight r n).sqrt).aestronglyMeasurable).mpr
  convert integrable_weightedQuadratic r n v using 1
  funext y
  exact mul_pow _ _ 2 |>.trans (congrArg (‖basisCombination n v y‖^2 * ·)
    (Real.sq_sqrt (gramWeight_nonneg r n y)))

theorem weighted_cauchy_schwarz (r : ℚ) (n : ℕ) (u v : Fin (3*n) → ℂ) :
    (∫ y, ‖basisCombination n u y‖ * ‖basisCombination n v y‖ * gramWeight r n y) ≤
      Real.sqrt (weightedQuadratic r n u) * Real.sqrt (weightedQuadratic r n v) := by
  have h2 : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hu : MemLp (fun y => ‖basisCombination n u y‖ * Real.sqrt (gramWeight r n y))
      (ENNReal.ofReal (2 : ℝ)) := by simpa using weighted_norm_memLp r n u
  have hv : MemLp (fun y => ‖basisCombination n v y‖ * Real.sqrt (gramWeight r n y))
      (ENNReal.ofReal (2 : ℝ)) := by simpa using weighted_norm_memLp r n v
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg h2
    (Eventually.of_forall fun y => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (Eventually.of_forall fun y => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hu hv
  have hp (y : ℝ) :
      (‖basisCombination n u y‖ * Real.sqrt (gramWeight r n y)) *
        (‖basisCombination n v y‖ * Real.sqrt (gramWeight r n y)) =
      ‖basisCombination n u y‖ * ‖basisCombination n v y‖ * gramWeight r n y := by
    calc
      _ = (‖basisCombination n u y‖ * ‖basisCombination n v y‖) *
        (Real.sqrt (gramWeight r n y))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (gramWeight_nonneg r n y)]
  simpa only [hp, Real.rpow_two, mul_pow, Real.sq_sqrt (gramWeight_nonneg r n _),
    ← Real.sqrt_eq_rpow, weightedQuadratic] using hh

theorem normalizedPencil_bilinear_le (r : ℚ) (n : ℕ) (u v : Fin (3*n) → ℂ) :
    ‖u ⬝ᵥ ((normalizedPencil r n (Cr r)).map Complex.ofReal *ᵥ v)‖ ≤
      Real.sqrt (weightedQuadratic r n u) * Real.sqrt (weightedQuadratic r n v) := by
  rw [normalizedPencil_bilinear]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hs : 0 ≤ (Sn n : ℝ) := by exact_mod_cast (Sn_pos n).le
  simp only [norm_mul, Complex.norm_ratCast, abs_of_nonneg hs]
  exact weighted_cauchy_schwarz r n u v

end
end Zeta32Extension
end
