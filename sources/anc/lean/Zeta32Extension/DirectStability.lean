module
public import Zeta32Extension.BilinearPerturbation
public import Zeta32Extension.Stability

@[expose] public section
namespace Zeta32Extension
noncomputable section
open Zeta32 Matrix Polynomial Filter Topology
open scoped BigOperators ComplexOrder

/-- Direct determinant stability for the actual pencil. No uniform-minor
hypothesis is used: all analytic inputs are discharged. -/
theorem pencil_stability_eventually (r : ℚ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ,
      |aeval x (Qtilde r n)| ≤ positiveHeine r n *
        (1 + (3*n : ℝ) * (|x-Cr r| * Real.exp (50*n)) * Real.exp (60*n))^(3*n) := by
  filter_upwards [weightedQuadratic_eventually_lower, positiveGram_eventually_posDef,
    eventually_ge_atTop (1 : ℕ)] with n hlower hpos hn
  intro x
  have hh := det_le_of_bilinear_gram (positiveGram r n)
    ((normalizedPencil r n x).map Complex.ofReal) (hpos r)
    (show 0 ≤ 1 + (3*n : ℝ) * (|x-Cr r| * Real.exp (50*n)) * Real.exp (60*n)
      by positivity) (fun u v => by
        rw [positiveGram_quadratic, positiveGram_quadratic, Complex.ofReal_re, Complex.ofReal_re]
        exact perturbed_pencil_bilinear_le r n hn (hlower r) x u v)
  have he : ((normalizedPencil r n x).map Complex.ofReal).det =
      ((aeval x (Qtilde r n) : ℝ) : ℂ) := by
    rw [← normalizedPencil_det]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  simpa only [he, positiveGram_det, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (positiveHeine_nonneg r n)] using hh

theorem nearby_Qtilde_eventually (r : ℚ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x-Cr r| ≤ Real.exp (-120*n) →
      |aeval x (Qtilde r n)| ≤ positiveHeine r n * Real.exp (3*n) := by
  filter_upwards [pencil_stability_eventually r] with n hn
  intro x hx
  have hb := perturbation_factor_le n hx
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh
    exact hh
  have hpow : (2 : ℝ)^(3*n) ≤ Real.exp (3*n) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (3*n)
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using hh
  refine (hn x).trans ?_
  apply mul_le_mul_of_nonneg_left _ (positiveHeine_nonneg r n)
  exact (pow_le_pow_left₀ (by positivity) hb (3*n)).trans hpow

/-- Unconditional local smallness. Nonvanishing of `Q` is supplied at the
good prime indices in the arithmetic endpoint argument. -/
theorem local_decay (r : ℚ) :
    ∀ᶠ n : ℕ in atTop, Q r n ≠ 0 → ∀ x : ℝ,
      |x-Cr r| ≤ Real.exp (-120*n) →
        |aeval x (P r n)| ≤ Real.exp (-(3/10 : ℝ)*(n : ℝ)^2) := by
  have hA := arith_node r (1/100) (by norm_num)
  have hF := positiveHeine_eventually_le r (1/100) (by norm_num)
  filter_upwards [hA, hF, nearby_Qtilde_eventually r, eventually_ge_atTop (300 : ℕ)]
    with n hAn hFn hnear hn
  intro hQ x hx
  have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hd : (dtilde r n : ℝ) ≤ Real.exp ((283/50+1/100 : ℝ)*(n : ℝ)^2) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast dtilde_pos r n)).mp (hAn hQ)
  have hq' : |aeval x (Qtilde r n)| ≤
      Real.exp ((-6+1/100 : ℝ)*(n : ℝ)^2) * Real.exp (3*n) :=
    (hnear x hx).trans (mul_le_mul_of_nonneg_right hFn (Real.exp_nonneg _))
  rw [abs_P_aeval_eq_dtilde_Qtilde]
  refine (mul_le_mul hd hq' (abs_nonneg _) (Real.exp_nonneg _)).trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hn0 (show (0 : ℝ) ≤ n-300 by linarith)]

end
end Zeta32Extension
end
