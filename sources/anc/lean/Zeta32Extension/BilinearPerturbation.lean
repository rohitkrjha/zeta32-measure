module
public import Zeta32Extension.GramComparison
public import Zeta32Extension.SignedBilinear

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Zeta32 Matrix Filter
open scoped BigOperators ComplexConjugate ComplexOrder

theorem sum_norm_le_sqrt_card_vectorL2 {h : ℕ} (v : Fin h → ℂ) :
    (∑ i, ‖v i‖) ≤ Real.sqrt h * vectorL2 v := by
  have hs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin h)))
    (f := fun i => ‖v i‖)
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [Finset.card_univ, Fintype.card_fin, vectorL2, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg h),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖v i‖)] using hs

theorem bilinear_le_of_entry_bound {h : ℕ} (Z : Matrix (Fin h) (Fin h) ℂ)
    {K : ℝ} (hK : 0 ≤ K) (hZ : ∀ i j, ‖Z i j‖ ≤ K) (u v : Fin h → ℂ) :
    ‖u ⬝ᵥ (Z *ᵥ v)‖ ≤ (h : ℝ) * K * vectorL2 u * vectorL2 v := by
  have hn : ‖u ⬝ᵥ (Z *ᵥ v)‖ ≤ K * (∑ i, ‖u i‖) * (∑ j, ‖v j‖) := by
    calc
      _ = ‖∑ i, ∑ j, u i * Z i j * v j‖ := by
        simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      _ ≤ ∑ i, ∑ j, ‖u i‖ * K * ‖v j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hZ i j) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hs := mul_le_mul (sum_norm_le_sqrt_card_vectorL2 u)
    (sum_norm_le_sqrt_card_vectorL2 v)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ ≤ K * ((∑ i, ‖u i‖) * (∑ j, ‖v j‖)) := by nlinarith only [hn]
    _ ≤ K * ((Real.sqrt h * vectorL2 u) * (Real.sqrt h * vectorL2 v)) :=
      mul_le_mul_of_nonneg_left hs hK
    _ = (h : ℝ) * K * vectorL2 u * vectorL2 v := by
      calc
        _ = (Real.sqrt h)^2 * K * vectorL2 u * vectorL2 v := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg h)]

theorem vectorL2_le_of_weighted_lower (r : ℚ) (n : ℕ)
    (hlower : ∀ v : Fin (3*n) → ℂ,
      Real.exp (-60*n) * (∑ i, ‖v i‖^2) ≤ weightedQuadratic r n v)
    (v : Fin (3*n) → ℂ) :
    vectorL2 v ≤ Real.exp (30*n) * Real.sqrt (weightedQuadratic r n v) := by
  have he : Real.exp (60*(n : ℝ)) * Real.exp (-60*n) = 1 := by
    rw [← Real.exp_add]; simp
  have he2 : Real.exp (30*(n : ℝ))^2 = Real.exp (60*n) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_left (hlower v) (Real.exp_nonneg (60*n))
  rw [← mul_assoc, he, one_mul] at hh
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [vectorL2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖v i‖),
    mul_pow, he2, Real.sq_sqrt (weightedQuadratic_nonneg r n v)] using hh

theorem perturbed_pencil_bilinear_le (r : ℚ) (n : ℕ) (hn : 1 ≤ n)
    (hlower : ∀ v : Fin (3*n) → ℂ,
      Real.exp (-60*n) * (∑ i, ‖v i‖^2) ≤ weightedQuadratic r n v)
    (x : ℝ) (u v : Fin (3*n) → ℂ) :
    ‖u ⬝ᵥ ((normalizedPencil r n x).map Complex.ofReal *ᵥ v)‖ ≤
      (1 + (3*n : ℝ) * (|x-Cr r| * Real.exp (50*n)) * Real.exp (60*n)) *
        Real.sqrt (weightedQuadratic r n u) * Real.sqrt (weightedQuadratic r n v) := by
  let A := (normalizedPencil r n (Cr r)).map Complex.ofReal
  let Z := (normalizedPencil r n x - normalizedPencil r n (Cr r)).map Complex.ofReal
  let K := |x-Cr r| * Real.exp (50*n)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hZ (i j : Fin (3*n)) : ‖Z i j‖ ≤ K := by
    simpa only [Z, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, K] using
      normalizedPencil_sub_le r n hn x (Cr r) i j
  have hz := bilinear_le_of_entry_bound Z hK hZ u v
  have hu := vectorL2_le_of_weighted_lower r n hlower u
  have hv := vectorL2_le_of_weighted_lower r n hlower v
  have huv := mul_le_mul hu hv (Real.sqrt_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _))
  have hpert : ‖u ⬝ᵥ (Z *ᵥ v)‖ ≤
      (3*n : ℝ) * K * Real.exp (60*n) *
        Real.sqrt (weightedQuadratic r n u) * Real.sqrt (weightedQuadratic r n v) := by
    have hh := mul_le_mul_of_nonneg_left huv (show 0 ≤ (3*n : ℝ) * K by positivity)
    have he : Real.exp (30*(n : ℝ)) * Real.exp (30*n) = Real.exp (60*n) := by
      rw [← Real.exp_add]; congr 1; ring
    have heq : (Real.exp (30*(n : ℝ)) * Real.sqrt (weightedQuadratic r n u)) *
        (Real.exp (30*n) * Real.sqrt (weightedQuadratic r n v)) =
      Real.exp (60*n) * Real.sqrt (weightedQuadratic r n u) *
        Real.sqrt (weightedQuadratic r n v) := by
      calc
        _ = (Real.exp (30*(n : ℝ)) * Real.exp (30*n)) *
            Real.sqrt (weightedQuadratic r n u) * Real.sqrt (weightedQuadratic r n v) := by ring
        _ = _ := by rw [he]
    rw [heq] at hh
    push_cast at hz
    nlinarith only [hz, hh]
  have heq : (normalizedPencil r n x).map Complex.ofReal = A+Z := by
    ext i j
    simp only [A, Z, Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Complex.ofReal_sub]
    ring
  rw [heq, add_mulVec, dotProduct_add]
  have hh := (norm_add_le (u ⬝ᵥ (A *ᵥ v)) (u ⬝ᵥ (Z *ᵥ v))).trans
    (add_le_add (normalizedPencil_bilinear_le r n u v) hpert)
  dsimp [K] at hh
  nlinarith only [hh]

end
end Zeta32Extension
end
