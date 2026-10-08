/-
Adapted from Qian Tang's Apache-2.0 Zeta32 development, revision
669c92bf7a3728e0de9ad80c373bc29fb5ca3d58:
Zeta32/Analytic/Energy/Scaling.lean and Assembly.lean.
Those files additionally acknowledge dtq1997/li2-half-irrationality.
Modification: retain the positive Heine integral, without a determinant hypothesis.
This file does not establish the proposed irrationality-exponent endpoint.
-/
module
public import Zeta32.Analytic.Energy.Assembly

@[expose] public section
open Real MeasureTheory Polynomial Filter Topology
open Zeta32 Zeta32.Analytic.EnergyI

namespace Zeta32Extension
noncomputable section

/-- Normalized nonnegative Heine integral; the candidate Gram determinant. -/
def positiveHeine (r : ℚ) (n : ℕ) : ℝ :=
  (scale n : ℝ) * ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y)

theorem positive_heine_scaled (r : ℚ) : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∀ D : (Fin (3*n) → ℝ) → ℝ, Integrable D →
      (∀ x : Fin (3*n) → ℝ, (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 ≤ D x) →
      positiveHeine r n ≤
        Real.exp (9 * (3/2 - Real.log 3) * (n:ℝ)^2 + C * (n:ℝ) * Real.log ((n:ℝ) + 1)) *
          ∫ x, D x := by
  refine ⟨6 * |cPt r| + 51, fun n hn D hD hGD => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hS : 0 < (Sn n : ℝ) := by exact_mod_cast Sn_pos n
  have hF : 0 < (Fn n : ℝ) := by exact_mod_cast Fn_pos n
  set E := Real.exp (cPt r + 7 * Real.log ((n : ℝ) + 1)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hG0 : ∀ x : Fin (3 * n) → ℝ, 0 ≤ (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) * vdm x :=
    fun x => mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (vdm_nonneg x)
  have hD0 : 0 ≤ ∫ x, D x := integral_nonneg fun x => (hG0 x).trans (hGD x)
  -- the value
  have hval : positiveHeine r n = (scale n : ℝ) * ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y) := by
    rfl
  -- the scaling of the integral
  have hscale : ∫ y, heineIntegrand r n y = (n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x) := by
    rw [Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul]
    rw [abs_of_pos (by positivity), ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  -- pointwise
  have hpt : ∀ x : Fin (3 * n) → ℝ, (Sn n : ℝ) ^ (3 * n) * heineIntegrand r n ((n : ℝ) • x) ≤
      E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * D x := by
    intro x
    rw [heineIntegrand_eq, vdm_smul]
    have hprod : (Sn n : ℝ) ^ (3 * n) * ∏ l, psiH r n (((n : ℝ) • x) l) =
        ∏ l, ((Sn n : ℝ) * psiH r n ((n : ℝ) * x l)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl
    have hle : ∏ l, ((Sn n : ℝ) * psiH r n ((n : ℝ) * x l)) ≤
        ∏ l, (E * ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) :=
      Finset.prod_le_prod₀ (fun l _ => mul_nonneg hS.le (psiH_nonneg r n _))
        (fun l _ => pointwise_bound r n hn (x l))
    have hR : ∏ l, (E * ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) =
        E ^ (3 * n) * ∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    replace hle := hle.trans hR.le
    have hG := hGD x
    change (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) * vdm x ≤ D x at hG
    calc (Sn n : ℝ) ^ (3 * n) * ((∏ l, psiH r n (((n : ℝ) • x) l)) * ((n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * vdm x))
        = (∏ l, ((Sn n : ℝ) * psiH r n ((n : ℝ) * x l))) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * vdm x := by
          rw [← hprod]; ring
      _ ≤ (E ^ (3 * n) * ∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) *
          (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * vdm x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (by positivity)) (vdm_nonneg x)
      _ = E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) *
          ((∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) * vdm x) := by ring
      _ ≤ E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * D x :=
          mul_le_mul_of_nonneg_left hG (by positivity)
  have hint : ∫ x, (Sn n : ℝ) ^ (3 * n) * heineIntegrand r n ((n : ℝ) • x) ≤
      E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * ∫ x, D x := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hD.const_mul _)
      (Filter.Eventually.of_forall hpt)
    change 0 ≤ (Sn n : ℝ) ^ (3 * n) * heineIntegrand r n ((n : ℝ) • x)
    rw [heineIntegrand_eq]
    exact mul_nonneg (pow_nonneg hS.le _) (mul_nonneg (Finset.prod_nonneg fun _ _ => psiH_nonneg _ _ _)
      (vdm_nonneg _))
  -- the coefficient
  have hfact : (1 : ℝ) ≤ ((3 * n).factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  have hscl : (scale n : ℝ) = (Sn n : ℝ) ^ (3 * n) / (Fn n : ℝ) := by
    simp only [scale, Rat.cast_div, Rat.cast_pow]
  have hmain : positiveHeine r n ≤
      ((n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) / (Fn n : ℝ)) * ∫ x, D x := by
    rw [hval]
    have h1 : ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y) ≤
        ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y) := le_rfl
    rw [hscale] at h1
    have h2 : ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y) ≤ (n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x) := by
      rw [hscale]
      refine h1.trans ?_
      have hI0 : 0 ≤ ∫ x, heineIntegrand r n ((n : ℝ) • x) :=
        integral_nonneg fun x => by
          rw [heineIntegrand_eq]
          exact mul_nonneg (Finset.prod_nonneg fun _ _ => psiH_nonneg _ _ _) (vdm_nonneg _)
      have : 1 / ((3 * n).factorial : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hfact
      have hp : 0 ≤ (n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x) := by positivity
      calc 1 / ((3 * n).factorial : ℝ) * ((n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x))
          ≤ 1 * ((n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x)) :=
            mul_le_mul_of_nonneg_right this hp
        _ = _ := one_mul _
    have h3 : (Sn n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x) ≤
        E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * ∫ x, D x := by
      rw [← integral_const_mul]; exact hint
    rw [hscl]
    calc (Sn n : ℝ) ^ (3 * n) / (Fn n : ℝ) * ((1 / ((3*n).factorial : ℝ)) * ∫ y, heineIntegrand r n y)
        ≤ (Sn n : ℝ) ^ (3 * n) / (Fn n : ℝ) * ((n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (n : ℝ) ^ (3 * n) / (Fn n : ℝ) * ((Sn n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x)) := by
          ring
      _ ≤ (n : ℝ) ^ (3 * n) / (Fn n : ℝ) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * ∫ x, D x) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hD0)
  -- logarithmic bound on the coefficient
  have hpos : 0 < (n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) / (Fn n : ℝ) := by positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have hhR : (((3 * n : ℕ)) : ℝ) = 3 * (n : ℝ) := by push_cast; ring
  have hexp_n : (n : ℝ) ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) = (n : ℝ) ^ ((3 * n) * (3 * n)) := by
    rw [← pow_add]
    congr 1
    rcases Nat.eq_zero_or_pos (3 * n) with h0 | h0
    · rw [h0]
    · have : 3 * n ≤ 3 * n * (3 * n) := Nat.le_mul_of_pos_right _ h0
      rw [Nat.mul_sub_one]; omega
  have hlog : Real.log ((n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) / (Fn n : ℝ)) =
      (((3 * n) * (3 * n) : ℕ) : ℝ) * Real.log n + ((3 * n) : ℝ) * (cPt r + 7 * Real.log ((n : ℝ) + 1)) -
        Real.log (Fn n : ℝ) := by
    rw [show (n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) = (n : ℝ) ^ ((3 * n) * (3 * n)) * E ^ (3 * n) by
      rw [← hexp_n]; ring]
    rw [Real.log_div (by positivity) hF.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow, hE, Real.log_exp]
    push_cast; ring
  rw [hlog]
  have hFl := Fn_log_lower n hn
  have hlog3n : Real.log (((3 * n : ℕ)) : ℝ) = Real.log 3 + Real.log n := by
    rw [hhR, Real.log_mul (by norm_num) hn0.ne']
  rw [hlog3n, hhR] at hFl
  have hlogn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) (show (2:ℝ) ≤ (n : ℝ) + 1 by linarith)
    norm_num at h2
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcast : (((3 * n) * (3 * n) : ℕ) : ℝ) = 9 * (n : ℝ) ^ 2 := by push_cast; ring
  rw [hcast]
  have hc := le_abs_self (cPt r)
  have hca := abs_nonneg (cPt r)
  have hL := Real.log_nonneg (show (1:ℝ) ≤ (n : ℝ) + 1 by linarith)
  -- `n ≤ 2 n log(n+1)`, `n log n ≤ n log(n+1)`
  have k1 : (n : ℝ) ≤ 2 * ((n : ℝ) * Real.log ((n : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_left hlog2 hn0.le
    linarith
  have k2 : (n : ℝ) * Real.log n ≤ (n : ℝ) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlogn hn0.le
  have k3 : 3 * (n : ℝ) * cPt r ≤ 3 * |cPt r| * (2 * ((n : ℝ) * Real.log ((n : ℝ) + 1))) := by
    have a1 := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 3 * n by positivity)
    have a2 := mul_le_mul_of_nonneg_left k1 (show (0:ℝ) ≤ 3 * |cPt r| by positivity)
    linarith
  have k4 : (n : ℝ) * Real.log 3 ≤ 2 * (2 * ((n : ℝ) * Real.log ((n : ℝ) + 1))) := by
    have := mul_le_mul_of_nonneg_left hlog3 hn0.le
    linarith
  linarith


theorem positive_energy_bound_exp (r : ℚ) (hF : FstarInput) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, positiveHeine r n ≤ Real.exp ((-6 + ε) * (n:ℝ)^2) := by
  obtain ⟨a, ha, hm⟩ := exists_massA_eq_one
  have hFa := hF a ha hm
  have hI := IA_eq ha hm
  have hconst : 9 * (3/2 - Real.log 3) + 9 * (ellA a - IA a) ≤ -6 := by linarith
  obtain ⟨C1, hC1⟩ := positive_heine_scaled r
  obtain ⟨B, C2, hC2⟩ := config_bound ha hm
  set K := max 1 (∫ y, tailFun B 1 y) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  filter_upwards [eventually_lin_log_le (|C1| + |C2| + 3 * Real.log K) hε,
    eventually_ge_atTop 1] with n hlin hn
  have hn0 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 0 ≤ Real.log ((n:ℝ) + 1) := Real.log_nonneg (by linarith)
  set E := 9 * (n:ℝ)^2 * (ellA a - IA a) + C2 * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) with hE
  have hm3 : (1:ℝ) ≤ 3 * (n:ℝ) := by linarith
  -- pointwise domination of the scaled Heine integrand
  have hdom : ∀ x : Fin (3*n) → ℝ,
      (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 ≤
        Real.exp E * ∏ l, tailFun B (3 * (n:ℝ)) (x l) := by
    intro x
    have h := hC2 n hn x
    rw [Finset.prod_mul_distrib, mul_assoc]
    unfold tailFun
    rw [Finset.prod_mul_distrib]
    calc (∏ l, (1 + |x l|)^7) * ((∏ l, Real.exp (-(3 * (n:ℝ)) * Wt |x l|)) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2)
        ≤ (∏ l, (1 + |x l|)^7) * (Real.exp E *
          ∏ l, Real.exp (-(3 * (n:ℝ)) * max 0 (|x l| - B))) :=
          mul_le_mul_of_nonneg_left h (Finset.prod_nonneg fun _ _ => by positivity)
      _ = _ := by ring
  have hint : Integrable (fun x : Fin (3*n) → ℝ => Real.exp E * ∏ l, tailFun B (3 * (n:ℝ)) (x l)) :=
    (Integrable.fintype_prod (f := fun _ => tailFun B (3 * (n:ℝ)))
      (fun _ => integrable_tailFun B hm3)).const_mul _
  have hInt : ∫ x : Fin (3*n) → ℝ, Real.exp E * ∏ l, tailFun B (3 * (n:ℝ)) (x l) ≤
      Real.exp E * K ^ (3*n) := by
    rw [integral_const_mul, integral_fintype_prod_volume_eq_pow, Fintype.card_fin]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply pow_le_pow_left₀ (integral_nonneg fun y => by unfold tailFun; positivity)
    exact (integral_tailFun_le B hm3).trans (le_max_right _ _)
  have hKpow : K ^ (3*n) = Real.exp (3 * (n:ℝ) * Real.log K) := by
    rw [← Real.exp_log (by linarith : (0:ℝ) < K), ← Real.exp_nat_mul, Real.exp_log (by linarith)]
    push_cast; ring_nf
  refine (hC1 n hn _ hint hdom).trans ?_
  refine (mul_le_mul_of_nonneg_left hInt (Real.exp_pos _).le).trans ?_
  rw [hKpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hA1 : C1 * (n:ℝ) * Real.log ((n:ℝ) + 1) ≤ |C1| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C1)
      (mul_nonneg (by positivity : (0:ℝ) ≤ n) hlog1), abs_nonneg C1]
  have hA2 : C2 * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) ≤
      |C2| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity))
      (by positivity)
  have hA3 : 3 * (n:ℝ) * Real.log K ≤ 3 * Real.log K * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) := by
    nlinarith [mul_nonneg (mul_nonneg hlogK (by positivity : (0:ℝ) ≤ n)) hlog1]
  have hsplit : (|C1| + |C2| + 3 * Real.log K) * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) =
      |C1| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) + |C2| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) +
        3 * Real.log K * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) := by ring
  have hc2 := mul_le_mul_of_nonneg_right hconst (sq_nonneg (n:ℝ))
  nlinarith


end
end Zeta32Extension
end
