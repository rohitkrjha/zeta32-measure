module
public import Zeta32Extension.ComplexPolynomialCoefficient
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Polynomial Set MeasureTheory
open scoped BigOperators

/-- A maximum cannot be isolated when the function has a quantitative
Lipschitz bound. The proof takes a one-sided interval inside [-1,1]. -/
theorem peak_square_integral_lower {f : ℝ → ℝ} (hf : Continuous f)
    {M C a : ℝ} (hM : 0 < M) (hC : 1 ≤ C)
    (ha : a ∈ Icc (-1 : ℝ) 1) (hfa : f a = M)
    (hLip : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      |f s - f t| ≤ C*M*|s-t|) :
    M^2 ≤ 8*C * ∫ x in Icc (-1 : ℝ) 1, (f x)^2 := by
  let δ : ℝ := 1 / (2*C)
  have hC0 : 0 < C := by linarith
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hCδ : C*δ = 1/2 := by dsimp [δ]; field_simp
  obtain ⟨u, hsub, hdist⟩ : ∃ u : ℝ,
      Icc u (u+δ) ⊆ Icc (-1 : ℝ) 1 ∧
      ∀ x ∈ Icc u (u+δ), |x-a| ≤ δ := by
    rcases le_total a 0 with ha0 | ha0
    · refine ⟨a, ?_, ?_⟩
      · intro x hx; constructor <;> linarith [ha.1, ha.2, hx.1, hx.2]
      · intro x hx; apply abs_le.mpr; constructor <;> linarith [hx.1, hx.2]
    · refine ⟨a-δ, ?_, ?_⟩
      · intro x hx; constructor <;> linarith [ha.1, ha.2, hx.1, hx.2]
      · intro x hx; apply abs_le.mpr; constructor <;> linarith [hx.1, hx.2]
  have hnear (x : ℝ) (hx : x ∈ Icc u (u+δ)) : M/2 ≤ f x := by
    have hh := hLip x (hsub hx) a ha
    rw [hfa] at hh
    have hb := mul_le_mul_of_nonneg_left (hdist x hx) (show 0 ≤ C*M by positivity)
    have he : C*M*δ = M/2 := by nlinarith [hCδ]
    rw [he] at hb
    have hh' := (abs_le.mp (hh.trans hb)).1
    linarith
  have hfi : IntegrableOn (fun x => (f x)^2) (Icc (-1 : ℝ) 1) :=
    (hf.pow 2).integrableOn_Icc
  have hlo : δ*(M/2)^2 ≤ ∫ x in Icc u (u+δ), (f x)^2 := by
    calc
      δ*(M/2)^2 = ∫ _x in Icc u (u+δ), (M/2)^2 := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on continuous_const.integrableOn_Icc
        (hfi.mono_set hsub) measurableSet_Icc
        (fun x hx => by have hh := hnear x hx; nlinarith)
  have hmono : (∫ x in Icc u (u+δ), (f x)^2) ≤
      ∫ x in Icc (-1 : ℝ) 1, (f x)^2 :=
    setIntegral_mono_set hfi (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall hsub)
  have hh := mul_le_mul_of_nonneg_left (hlo.trans hmono) (show 0 ≤ 8*C by positivity)
  have he : (8*C)*(δ*(M/2)^2) = M^2 := by
    calc
      _ = 2*(C*δ)*M^2 := by ring
      _ = _ := by rw [hCδ]; ring
  rwa [he] at hh

theorem polynomial_peak_square_le_integral {p : ℂ[X]} {h : ℕ}
    (hdeg : p.natDegree < h) {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1)
    (hpeak : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ ‖p.eval (a : ℂ)‖) :
    ‖p.eval (a : ℂ)‖^2 ≤ 16*(h : ℝ)^2*(7 : ℝ)^h *
      ∫ x in Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖^2 := by
  let M := ‖p.eval (a : ℂ)‖
  have hM0 : 0 ≤ M := norm_nonneg _
  by_cases hM : M = 0
  · have hI : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖^2 :=
      integral_nonneg (fun x => sq_nonneg _)
    change M^2 ≤ _
    rw [hM, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
  have hh : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hpow : (1 : ℝ) ≤ (7 : ℝ)^h := one_le_pow₀ (by norm_num)
  have hC : (1 : ℝ) ≤ 2*(h : ℝ)^2*(7 : ℝ)^h := by nlinarith
  have hLip : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      |‖p.eval (s : ℂ)‖-‖p.eval (t : ℂ)‖| ≤
        (2*(h : ℝ)^2*(7 : ℝ)^h)*M*|s-t| := by
    intro s hs t ht
    exact (abs_norm_sub_norm_le _ _).trans
      (complex_polynomial_lipschitz_on_unit_interval hMpos hdeg hpeak hs ht)
  have hb := peak_square_integral_lower
    ((p.continuous.comp Complex.continuous_ofReal).norm) hMpos hC ha rfl hLip
  simpa only [M, Function.comp_apply, show 8*(2*(h : ℝ)^2*(7 : ℝ)^h) =
    16*(h : ℝ)^2*(7 : ℝ)^h by ring] using hb

/-- Quantitative L² control after the affine substitution used to recover
the factorial-normalized coefficients. -/
theorem polynomial_affine_coeff_sq_le_integral {p : ℂ[X]} {h : ℕ}
    (hdeg : p.natDegree < h) {a b : ℂ} (ha : ‖a‖ ≤ 4) (hb : ‖b‖ ≤ 2) (i : ℕ) :
    ‖(p.comp (C a + C b*X)).coeff i‖^2 ≤ 64*(h : ℝ)^4*(12348 : ℝ)^h *
      ∫ x in Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖^2 := by
  have hcont : Continuous (fun x : ℝ => ‖p.eval (x : ℂ)‖) :=
    (p.continuous.comp Complex.continuous_ofReal).norm
  obtain ⟨x₀, hx₀, hpeak⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hcont.continuousOn
  have hc := polynomial_affine_coeff_le (norm_nonneg _) hdeg hpeak ha hb i
  have hI := polynomial_peak_square_le_integral hdeg hx₀ hpeak
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hc 2
  calc
    ‖(p.comp (C a+C b*X)).coeff i‖^2 ≤
      (2*(h : ℝ)*(42 : ℝ)^h)^2 * ‖p.eval (x₀ : ℂ)‖^2 := by
        simpa only [mul_pow] using hsq
    _ ≤ (2*(h : ℝ)*(42 : ℝ)^h)^2 *
      (16*(h : ℝ)^2*(7 : ℝ)^h * ∫ x in Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖^2) :=
        mul_le_mul_of_nonneg_left hI (sq_nonneg _)
    _ = _ := by
      have he : ((42 : ℝ)^2)^h = ((42 : ℝ)^h)^2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [show (12348 : ℝ) = 42^2*7 by norm_num, mul_pow (42^2 : ℝ) 7 h, he]
      ring

end
end Zeta32Extension
end
