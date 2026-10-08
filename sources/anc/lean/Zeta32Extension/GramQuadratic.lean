module
public import Zeta32Extension.GramDeterminant
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Zeta32 Zeta32.Analytic Zeta32.Analytic.Contour
open Set MeasureTheory Matrix Filter RCLike
open scoped BigOperators ComplexConjugate ComplexOrder

def gramKernel (r : ℚ) (n : ℕ) (i j : Fin (3*n)) (y : ℝ) : ℂ :=
  (Sn n : ℂ) * (conj (heineF n i y) * heineF n j y * (‖heinePhi r n y‖ : ℂ)) /
    ((i.val.factorial : ℂ) * (j.val.factorial : ℂ))

theorem integrable_gramKernel (r : ℚ) (n : ℕ) (i j : Fin (3*n)) :
    Integrable (gramKernel r n i j) :=
  ((integrable_baseGram_entry r n i j).const_mul _).div_const _

theorem positiveGram_apply (r : ℚ) (n : ℕ) (i j : Fin (3*n)) :
    positiveGram r n i j = ∫ y, gramKernel r n i j y := by
  simp only [positiveGram, complexInverseFactorials, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, gramKernel,
    integral_div, integral_const_mul, baseGram]
  ring

theorem gramKernel_sum (r : ℚ) (n : ℕ) (v : Fin (3*n) → ℂ) (y : ℝ) :
    (∑ i, ∑ j, conj (v i) * gramKernel r n i j y * v j) =
      (‖basisCombination n v y‖^2 * gramWeight r n y : ℝ) := by
  push_cast
  rw [← Complex.conj_mul']
  simp only [basisCombination, map_sum, map_div₀, _root_.map_mul, Complex.conj_natCast,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [gramKernel, heineF, gramWeight]
  push_cast
  ring

theorem positiveGram_quadratic (r : ℚ) (n : ℕ) (v : Fin (3*n) → ℂ) :
    star v ⬝ᵥ (positiveGram r n *ᵥ v) = (weightedQuadratic r n v : ℂ) := by
  have hi (i j : Fin (3*n)) : Integrable (fun y => conj (v i) * gramKernel r n i j y * v j) :=
    ((integrable_gramKernel r n i j).const_mul _).mul_const _
  calc
    star v ⬝ᵥ (positiveGram r n *ᵥ v) =
      ∑ i, ∑ j, ∫ y, conj (v i) * gramKernel r n i j y * v j := by
        simp only [dotProduct, mulVec, Pi.star_apply, star_def, positiveGram_apply,
          integral_mul_const, integral_const_mul, Finset.mul_sum, mul_assoc]
    _ = ∫ y, ∑ i, ∑ j, conj (v i) * gramKernel r n i j y * v j := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hi i j)).symm
    _ = _ := by
      simp_rw [gramKernel_sum]
      exact integral_complex_ofReal

theorem positiveGram_isHermitian (r : ℚ) (n : ℕ) : (positiveGram r n).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, positiveGram_apply, star_def, ← integral_conj]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  simp only [gramKernel, map_div₀, _root_.map_mul, map_ratCast, Complex.conj_natCast,
    Complex.conj_ofReal, starRingEnd_self_apply]
  ring

theorem positiveGram_posSemidef (r : ℚ) (n : ℕ) : (positiveGram r n).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (positiveGram_isHermitian r n)
  intro v
  rw [positiveGram_quadratic]
  exact_mod_cast weightedQuadratic_nonneg r n v

theorem positiveGram_eventually_lower :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℚ, ∀ v : Fin (3*n) → ℂ,
      Real.exp (-60*n) * (∑ i, ‖v i‖^2) ≤
        (star v ⬝ᵥ (positiveGram r n *ᵥ v)).re := by
  filter_upwards [weightedQuadratic_eventually_lower] with n hn
  intro r v
  rw [positiveGram_quadratic, Complex.ofReal_re]
  exact hn r v

theorem positiveGram_eventually_posDef :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℚ, (positiveGram r n).PosDef := by
  filter_upwards [weightedQuadratic_eventually_lower] with n hn
  intro r
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (positiveGram_isHermitian r n)
  intro v hv
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  have hs : 0 < ∑ j, ‖v j‖^2 := by
    apply Finset.sum_pos' (fun j _ => sq_nonneg _)
    exact ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hw : 0 < weightedQuadratic r n v :=
    (mul_pos (Real.exp_pos _) hs).trans_le (hn r v)
  rw [positiveGram_quadratic]
  exact_mod_cast hw

end
end Zeta32Extension
end
