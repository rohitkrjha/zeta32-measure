module
public import Zeta32Extension.WeightedQuadratic
public import Zeta32Extension.Pencil

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Zeta32 Zeta32.Analytic Zeta32.Analytic.Contour
open Polynomial Set MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

/-- Unnormalized positive moment matrix. The conjugation is on the first
factor, in agreement with the complex inner-product convention. -/
def baseGram (r : ℚ) (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℂ :=
  fun i j => ∫ y, conj (heineF n i y) * heineF n j y * (‖heinePhi r n y‖ : ℂ)

def complexInverseFactorials (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℂ :=
  diagonal fun i => ((i.val.factorial : ℂ))⁻¹

def positiveGram (r : ℚ) (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℂ :=
  (Sn n : ℂ) • (complexInverseFactorials n * baseGram r n * complexInverseFactorials n)

theorem integrable_baseGram_entry (r : ℚ) (n : ℕ) (i j : Fin (3*n)) :
    Integrable (fun y => conj (heineF n i y) * heineF n j y * (‖heinePhi r n y‖ : ℂ)) := by
  have hc : Continuous (fun y => conj (heineF n i y) * heineF n j y * (‖heinePhi r n y‖ : ℂ)) := by
    unfold heineF
    exact ((continuous_tpt.pow i.val).star.mul (continuous_tpt.pow j.val)).mul
      (Complex.continuous_ofReal.comp (continuous_heinePhi r n).norm)
  apply (logistic_integrable_entry r n (i.val+j.val)).norm.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  apply le_of_eq
  simp only [heineF, heinePhi, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_norm, pow_add]
  ring

theorem positive_andreief_integrand (r : ℚ) (n : ℕ) (x : Fin (3*n) → ℝ) :
    (Matrix.of fun i j => conj (heineF n i (x j))).det *
      (Matrix.of fun i j => heineF n i (x j) * (‖heinePhi r n (x j)‖ : ℂ)).det =
        (heineIntegrand r n x : ℂ) := by
  have hconj : (Matrix.of fun i j => conj (heineF n i (x j))).det =
      conj ((Matrix.of fun i j => heineF n i (x j)).det) := by
    exact (RingHom.map_det (starRingEnd ℂ) _).symm
  have hG : (Matrix.of fun i j => heineF n i (x j) * (‖heinePhi r n (x j)‖ : ℂ)).det =
      (∏ j, (‖heinePhi r n (x j)‖ : ℂ)) * (Matrix.of fun i j => heineF n i (x j)).det := by
    rw [← det_mul_row]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    ring
  have hs := heine_norm_integrand r n x
  rw [heine_det_G, norm_mul, norm_mul, norm_prod] at hs
  rw [hconj, hG, ← hs]
  have he := Complex.conj_mul' ((Matrix.of fun i j => heineF n i (x j)).det)
  push_cast
  calc
    _ = (∏ j, (‖heinePhi r n (x j)‖ : ℂ)) *
      (conj ((Matrix.of fun i j => heineF n i (x j)).det) *
        (Matrix.of fun i j => heineF n i (x j)).det) := by ring
    _ = _ := by rw [he]; ring

theorem baseGram_det (r : ℚ) (n : ℕ) :
    (baseGram r n).det =
      ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y : ℝ) := by
  have he : baseGram r n = Matrix.of (fun i j =>
      ∫ y, conj (heineF n i y) * (heineF n j y * (‖heinePhi r n y‖ : ℂ))) := by
    ext i j
    simp only [baseGram, Matrix.of_apply, mul_assoc]
  rw [he, Contour.Andreief.andreief (μ := volume) _ _ (fun i j => by
    simpa only [mul_assoc] using integrable_baseGram_entry r n i j)]
  simp_rw [positive_andreief_integrand]
  change (1 / ((3*n).factorial : ℂ)) * (∫ x : Fin (3*n) → ℝ,
    (heineIntegrand r n x : ℂ)) = _
  rw [integral_complex_ofReal]
  push_cast
  rfl

theorem complexInverseFactorials_det (n : ℕ) :
    (complexInverseFactorials n).det = (∏ i : Fin (3*n), (i.val.factorial : ℂ))⁻¹ := by
  simp [complexInverseFactorials, det_diagonal, Finset.prod_inv_distrib]

/-- The positive integral retained from the upstream energy proof is
exactly the determinant of this positive moment matrix. -/
theorem positiveGram_det (r : ℚ) (n : ℕ) :
    (positiveGram r n).det = (positiveHeine r n : ℂ) := by
  have hFn : (Fn n : ℂ) = (∏ i : Fin (3*n), (i.val.factorial : ℂ))^2 := by
    exact_mod_cast Fn_eq_product n
  rw [positiveGram, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    complexInverseFactorials_det, baseGram_det]
  simp only [Fintype.card_fin, positiveHeine, scale, Rat.cast_div, Rat.cast_pow]
  push_cast
  rw [hFn]
  ring

end
end Zeta32Extension
end
