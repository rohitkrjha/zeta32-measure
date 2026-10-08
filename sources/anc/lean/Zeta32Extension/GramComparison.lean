/-
The Hilbert-space determinant lemma below follows the Gram--Schmidt proof
in OpenAI's Apache-2.0 FirstSheetHilbertDeterminant.lean (September 2026).
The bilinear-to-Gram comparison and its application are separate extensions.
-/
module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Matrix RCLike
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

def vectorL2 {h : ℕ} (v : Fin h → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖^2)

theorem vectorL2_eq_norm {h : ℕ} (v : Fin h → ℂ) :
    vectorL2 v = ‖WithLp.toLp 2 v‖ := by
  rw [vectorL2, ← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem norm_star_dotProduct_self {h : ℕ} (v : Fin h → ℂ) :
    ‖star v ⬝ᵥ v‖ = (vectorL2 v)^2 := by
  have hs : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [dotProduct, Pi.star_apply, star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs, vectorL2, Real.sq_sqrt hs]

theorem vectorL2_star {h : ℕ} (v : Fin h → ℂ) : vectorL2 (star v) = vectorL2 v := by
  simp [vectorL2]

theorem hilbert_det_norm_le_pow {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (L : V →ₗ[ℂ] V) {C : ℝ} (hL : ∀ v, ‖L v‖ ≤ C * ‖v‖) :
    ‖LinearMap.det L‖ ≤ C ^ Module.finrank ℂ V := by
  classical
  let b := stdOrthonormalBasis ℂ V
  let f : Fin (Module.finrank ℂ V) → V := fun i => L (b i)
  have hd : Module.finrank ℂ V = Fintype.card (Fin (Module.finrank ℂ V)) := by simp
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  have hdet : ‖c.toBasis.det f‖ = ‖LinearMap.det L‖ := by
    change ‖c.toBasis.det (L ∘ b)‖ = _
    rw [Module.Basis.det_comp, norm_mul,
      OrthonormalBasis.det_to_matrix_orthonormalBasis, mul_one]
  have hprod : ‖c.toBasis.det f‖ = ∏ i, ‖inner ℂ (c i) (f i)‖ := by
    simpa only [norm_prod] using congrArg (fun z : ℂ => ‖z‖)
      (InnerProductSpace.gramSchmidtOrthonormalBasis_det hd f)
  calc
    ‖LinearMap.det L‖ = ∏ i, ‖inner ℂ (c i) (f i)‖ := hdet.symm.trans hprod
    _ ≤ ∏ _i : Fin (Module.finrank ℂ V), C := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      calc
        ‖inner ℂ (c i) (f i)‖ ≤ ‖c i‖ * ‖f i‖ := norm_inner_le_norm _ _
        _ = ‖L (b i)‖ := by simp only [c.norm_eq_one, one_mul, f]
        _ ≤ C := by simpa only [b.norm_eq_one, mul_one] using hL (b i)
    _ = C ^ Module.finrank ℂ V := by simp

theorem det_le_of_bilinear_l2 {h : ℕ} (B : Matrix (Fin h) (Fin h) ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u v, ‖u ⬝ᵥ (B *ᵥ v)‖ ≤ C * vectorL2 u * vectorL2 v) :
    ‖B.det‖ ≤ C^h := by
  have hop (v : EuclideanSpace ℂ (Fin h)) :
      ‖B.toEuclideanLin v‖ ≤ C * ‖v‖ := by
    have hh := hB (star (B *ᵥ ⇑v)) ⇑v
    rw [norm_star_dotProduct_self, vectorL2_star] at hh
    have h0 : 0 ≤ vectorL2 (B *ᵥ ⇑v) := Real.sqrt_nonneg _
    have h1 : 0 ≤ vectorL2 ⇑v := Real.sqrt_nonneg _
    have hb : vectorL2 (B *ᵥ ⇑v) ≤ C * vectorL2 ⇑v := by
      by_cases hz : vectorL2 (B *ᵥ ⇑v) = 0
      · rw [hz]; exact mul_nonneg hC h1
      · have ha : 0 < vectorL2 (B *ᵥ ⇑v) := lt_of_le_of_ne h0 (Ne.symm hz)
        apply le_of_mul_le_mul_left (b := vectorL2 (B *ᵥ ⇑v)) _ ha
        nlinarith only [hh]
    simpa only [vectorL2_eq_norm, Matrix.toLpLin_apply, WithLp.toLp_ofLp] using hb
  have hh := hilbert_det_norm_le_pow B.toEuclideanLin hop
  simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    finrank_euclideanSpace, Fintype.card_fin] using hh

theorem exists_gram_whitening {h : ℕ} (M : Matrix (Fin h) (Fin h) ℂ)
    (hM : M.PosDef) : ∃ T : Matrix (Fin h) (Fin h) ℂ, Tᴴ * M * T = 1 := by
  obtain ⟨S, hS, hSM⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hM.isStrictlyPositive
  have hd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  refine ⟨S⁻¹, ?_⟩
  calc
    _ = (S * S⁻¹)ᴴ * (S * S⁻¹) := by
      rw [hSM]
      simp only [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [S.mul_nonsing_inv hd]; simp

theorem whitening_quadratic {h : ℕ} (M T : Matrix (Fin h) (Fin h) ℂ)
    (hT : Tᴴ * M * T = 1) (v : Fin h → ℂ) :
    (star (T *ᵥ v) ⬝ᵥ (M *ᵥ (T *ᵥ v))).re = ∑ i, ‖v i‖^2 := by
  have he : star (T *ᵥ v) ⬝ᵥ (M *ᵥ (T *ᵥ v)) = star v ⬝ᵥ v := by
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    rw [hT, vecMul_one]
  rw [he]
  simp only [dotProduct, Pi.star_apply, star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem det_le_of_bilinear_gram {h : ℕ} (M B : Matrix (Fin h) (Fin h) ℂ)
    (hM : M.PosDef) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u v, ‖u ⬝ᵥ (B *ᵥ v)‖ ≤ C *
      Real.sqrt (star u ⬝ᵥ (M *ᵥ u)).re * Real.sqrt (star v ⬝ᵥ (M *ᵥ v)).re) :
    ‖B.det‖ ≤ ‖M.det‖ * C^h := by
  obtain ⟨T, hT⟩ := exists_gram_whitening M hM
  have hb : ∀ u v, ‖u ⬝ᵥ ((Tᵀ * B * T) *ᵥ v)‖ ≤
      C * vectorL2 u * vectorL2 v := by
    intro u v
    have hh := hB (T *ᵥ u) (T *ᵥ v)
    rw [whitening_quadratic M T hT, whitening_quadratic M T hT] at hh
    change ‖u ⬝ᵥ ((Tᵀ * B * T) *ᵥ v)‖ ≤
      C * Real.sqrt (∑ i, ‖u i‖^2) * Real.sqrt (∑ i, ‖v i‖^2)
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    exact hh
  have hdet := det_le_of_bilinear_l2 (Tᵀ * B * T) hC hb
  have hid := congrArg (fun A : Matrix (Fin h) (Fin h) ℂ => ‖A.det‖) hT
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star, det_one, norm_one] at hid
  simp only [det_mul, det_transpose, norm_mul] at hdet
  have hh := mul_le_mul_of_nonneg_left hdet (norm_nonneg M.det)
  calc
    ‖B.det‖ = ‖M.det‖ * (‖T.det‖ * ‖B.det‖ * ‖T.det‖) := by
      calc
        _ = (‖T.det‖ * ‖M.det‖ * ‖T.det‖) * ‖B.det‖ := by rw [hid, one_mul]
        _ = _ := by ring
    _ ≤ _ := hh

end
end Zeta32Extension
end
