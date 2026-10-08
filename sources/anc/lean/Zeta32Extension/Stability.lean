module
public import Zeta32Extension.Pencil
public import Zeta32Extension.PositiveEndpoint
public import Zeta32Extension.MinorPerturbation

@[expose] public section
open Zeta32 Polynomial Filter Topology

namespace Zeta32Extension

theorem positiveHeine_nonneg (r : ℚ) (n : ℕ) : 0 ≤ positiveHeine r n := by
  unfold positiveHeine
  have hs : (0 : ℝ) ≤ scale n := by exact_mod_cast (scale_pos n).le
  apply mul_nonneg hs
  apply mul_nonneg (by positivity)
  apply MeasureTheory.integral_nonneg
  intro y
  unfold heineIntegrand
  positivity

/-- Conditional stability for the actual pencil. `UniformMinors` is the
remaining analytic obligation; it is not hidden as an axiom. -/
theorem pencil_stability_of_uniformMinors (r : ℚ) (n : ℕ) (hn : 1 ≤ n)
    (hM : UniformMinors r n) (x : ℝ) :
    |aeval x (Qtilde r n)| ≤ positiveHeine r n *
      (1 + (3*n : ℝ) * (|x-Cr r| * Real.exp (50*n)) * Real.exp (60*n))^(3*n) := by
  have h := det_add_le_of_all_minors
    (normalizedPencil r n (Cr r))
    (normalizedPencil r n x - normalizedPencil r n (Cr r))
    (positiveHeine_nonneg r n) (Real.exp_nonneg (60*n))
    (show 0 ≤ |x-Cr r| * Real.exp (50*n) by positivity)
    hM (normalizedPencil_sub_le r n hn x (Cr r))
  simpa only [add_sub_cancel, normalizedPencil_det, Nat.cast_mul, Nat.cast_ofNat] using h

theorem perturbation_factor_le (n : ℕ) {d : ℝ} (hd : d ≤ Real.exp (-120*n)) :
    (1 + (3*n : ℝ) * (d * Real.exp (50*n)) * Real.exp (60*n)) ≤ 2 := by
  have he : Real.exp (-120*(n : ℝ)) * Real.exp (50*n) * Real.exp (60*n) =
      Real.exp (-10*n) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod : d * Real.exp (50*n) * Real.exp (60*n) ≤ Real.exp (-10*n) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hlinear : (3*n : ℝ) ≤ Real.exp (10*n) := by
    have hh := Real.add_one_le_exp (10*(n : ℝ))
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hscaled : (3*n : ℝ) * Real.exp (-10*n) ≤ 1 := by
    calc
      _ ≤ Real.exp (10*n) * Real.exp (-10*n) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 3*n by positivity)
  nlinarith

theorem nearby_Qtilde_le (r : ℚ) (n : ℕ) (hn : 1 ≤ n)
    (hM : UniformMinors r n) (x : ℝ)
    (hx : |x-Cr r| ≤ Real.exp (-120*n)) :
    |aeval x (Qtilde r n)| ≤ positiveHeine r n * Real.exp (3*n) := by
  have hb := perturbation_factor_le n hx
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh
    exact hh
  have hpow : (2 : ℝ)^(3*n) ≤ Real.exp (3*n) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (3*n)
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using hh
  refine (pencil_stability_of_uniformMinors r n hn hM x).trans ?_
  apply mul_le_mul_of_nonneg_left _ (positiveHeine_nonneg r n)
  exact (pow_le_pow_left₀ (by positivity) hb (3*n)).trans hpow

/-- The required local decay estimate, still explicitly conditional on the
unproved uniform-minor bridge. The arithmetic and energy inputs are discharged. -/
theorem local_decay_of_uniformMinors (r : ℚ) :
    ∀ᶠ n : ℕ in atTop, UniformMinors r n → Q r n ≠ 0 → ∀ x : ℝ,
      |x-Cr r| ≤ Real.exp (-120*n) →
        |aeval x (P r n)| ≤ Real.exp (-(3/10 : ℝ)*(n : ℝ)^2) := by
  have hA := arith_node r (1/100) (by norm_num)
  have hF := positiveHeine_eventually_le r (1/100) (by norm_num)
  filter_upwards [hA, hF, eventually_ge_atTop (300 : ℕ)] with n hAn hFn hn
  intro hM hQ x hx
  have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hd : (dtilde r n : ℝ) ≤ Real.exp ((283/50+1/100 : ℝ)*(n : ℝ)^2) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast dtilde_pos r n)).mp (hAn hQ)
  have hq := nearby_Qtilde_le r n (by omega) hM x hx
  have hq' : |aeval x (Qtilde r n)| ≤
      Real.exp ((-6+1/100 : ℝ)*(n : ℝ)^2) * Real.exp (3*n) :=
    hq.trans (mul_le_mul_of_nonneg_right hFn (Real.exp_nonneg _))
  rw [abs_P_aeval_eq_dtilde_Qtilde]
  refine (mul_le_mul hd hq' (abs_nonneg _) (Real.exp_nonneg _)).trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hn0 (show (0 : ℝ) ≤ n-300 by linarith)]

#print axioms local_decay_of_uniformMinors

end Zeta32Extension
end
