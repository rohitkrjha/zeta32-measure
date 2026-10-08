module
public import Zeta32Extension.PositiveEnergy
public import Zeta32Extension.SlopeGrowth
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section
open Zeta32 Polynomial Matrix
open scoped BigOperators

namespace Zeta32Extension
noncomputable section

def rawPencil (r : ℚ) (n : ℕ) (x : ℝ) : Matrix (Fin (3*n)) (Fin (3*n)) ℝ :=
  fun i j => x * (slope n (i.val+j.val) : ℝ) + (intercept r n (i.val+j.val) : ℝ)

def inverseFactorials (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℝ :=
  diagonal fun i => ((i.val.factorial : ℝ))⁻¹

def normalizedPencil (r : ℚ) (n : ℕ) (x : ℝ) : Matrix (Fin (3*n)) (Fin (3*n)) ℝ :=
  (Sn n : ℝ) • (inverseFactorials n * rawPencil r n x * inverseFactorials n)

theorem normalizedPencil_apply (r : ℚ) (n : ℕ) (x : ℝ) (i j : Fin (3*n)) :
    normalizedPencil r n x i j =
      (Sn n : ℝ) * (x * (slope n (i.val+j.val) : ℝ) +
        (intercept r n (i.val+j.val) : ℝ)) /
        ((i.val.factorial : ℝ) * (j.val.factorial : ℝ)) := by
  simp [normalizedPencil, inverseFactorials, rawPencil, Matrix.mul_diagonal,
    Matrix.diagonal_mul, div_eq_mul_inv]
  ring

theorem rawPencil_det (r : ℚ) (n : ℕ) (x : ℝ) :
    (rawPencil r n x).det = aeval x (Q r n) := by
  rw [Q, AlgHom.map_det]
  congr 1
  ext i j
  simp [rawPencil, AlgHom.mapMatrix_apply, A, B]
  ring

theorem Fn_eq_product (n : ℕ) :
    (Fn n : ℝ) = (∏ i : Fin (3*n), (i.val.factorial : ℝ))^2 := by
  simp only [Fn, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast]
  rw [Finset.prod_pow]
  congr 1
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => (i.factorial : ℝ)) (3*n)).symm

theorem inverseFactorials_det (n : ℕ) :
    (inverseFactorials n).det = (∏ i : Fin (3*n), (i.val.factorial : ℝ))⁻¹ := by
  simp [inverseFactorials, det_diagonal, Finset.prod_inv_distrib]

theorem normalizedPencil_det (r : ℚ) (n : ℕ) (x : ℝ) :
    (normalizedPencil r n x).det = aeval x (Qtilde r n) := by
  rw [normalizedPencil, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    inverseFactorials_det, rawPencil_det, Qtilde, map_mul, aeval_C]
  simp only [Fintype.card_fin, eq_ratCast, scale, Rat.cast_div, Rat.cast_pow]
  rw [Fn_eq_product]
  ring

theorem normalizedPencil_sub (r : ℚ) (n : ℕ) (x y : ℝ) (i j : Fin (3*n)) :
    (normalizedPencil r n x - normalizedPencil r n y) i j =
      (x-y) * normalizedSlope n i.val j.val := by
  simp only [Matrix.sub_apply, normalizedPencil_apply, normalizedSlope]
  ring

theorem normalizedPencil_sub_le (r : ℚ) (n : ℕ) (hn : 1 ≤ n)
    (x y : ℝ) (i j : Fin (3*n)) :
    |(normalizedPencil r n x - normalizedPencil r n y) i j| ≤
      |x-y| * Real.exp (50*n) := by
  rw [normalizedPencil_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (normalizedSlope_le_exp n i.val j.val hn) (abs_nonneg _)

/-- The outstanding analytic bridge. This is a definition of a required
estimate, not an assertion that the estimate has already been proved. -/
def UniformMinors (r : ℚ) (n : ℕ) : Prop :=
  ∀ m, m ≤ 3*n → ∀ rows cols : Fin m ↪ Fin (3*n),
    |((normalizedPencil r n (Cr r)).submatrix rows cols).det| ≤
      positiveHeine r n * (Real.exp (60*n))^(3*n-m)

end
end Zeta32Extension
end
