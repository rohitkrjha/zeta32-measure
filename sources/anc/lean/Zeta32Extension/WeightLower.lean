module
public import Zeta32.Analytic.Heine
public import Zeta32.Analytic.Energy.Pointwise
public import Zeta32.Analytic.Energy.Stirling
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
open Zeta32 Zeta32.Analytic Zeta32.Analytic.Contour Zeta32.Analytic.EnergyI
open scoped BigOperators

namespace Zeta32Extension
noncomputable section

/-- The actual density used for the positive Gram matrix. -/
def gramWeight (r : ℚ) (n : ℕ) (y : ℝ) : ℝ :=
  (Sn n : ℝ) * ‖heinePhi r n y‖

theorem gramWeight_nonneg (r : ℚ) (n : ℕ) (y : ℝ) : 0 ≤ gramWeight r n y := by
  have hs : (0 : ℝ) ≤ Sn n := by exact_mod_cast (Sn_pos n).le
  exact mul_nonneg hs (norm_nonneg _)

theorem vertical_root_lower (n j : ℕ) (y : ℝ) (hy : (n : ℝ) ≤ y) :
    (n : ℝ) ≤ ‖tpt y + (j : ℂ)‖ := by
  have h := Complex.im_le_norm (tpt y + (j : ℂ))
  have he : (tpt y + (j : ℂ)).im = y := by simp [tpt]
  rw [he] at h
  exact hy.trans h

theorem vertical_root_upper (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ 5*n)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 2*n) :
    ‖tpt y + (j : ℂ)‖ ≤ (8*n : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (tpt y + (j : ℂ))
  have hre : (tpt y + (j : ℂ)).re = 1/2 + (j : ℝ) := by simp [tpt]
  have him : (tpt y + (j : ℂ)).im = y := by simp [tpt]
  rw [hre, him, abs_of_nonneg (by positivity), abs_of_nonneg hy0] at h
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 5*n := by exact_mod_cast hj
  linarith

theorem Rfun_lower (n : ℕ) (hn : 1 ≤ n) (y : ℝ)
    (hylo : (n : ℝ) ≤ y) (hyhi : y ≤ 2*n) :
    (n : ℝ)^(4*n) / (8*n : ℝ)^(5*n) ≤ ‖Rfun n (tpt y)‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnum : (n : ℝ)^n ≤ ∏ j ∈ Finset.Icc 1 n, ‖tpt y + (j : ℂ)‖ := by
    have hh := Finset.prod_le_prod₀ (s := (Finset.Icc 1 n : Finset ℕ))
      (f := fun (_ : ℕ) => (n : ℝ)) (g := fun (j : ℕ) => ‖tpt y + (j : ℂ)‖)
      (fun _ _ => hn0.le) (fun j _ => vertical_root_lower n j y hylo)
    simpa [Nat.card_Icc] using hh
  have hden : (∏ j ∈ Finset.Icc 1 (5*n), ‖tpt y + (j : ℂ)‖) ≤ (8*n : ℝ)^(5*n) := by
    have hh := Finset.prod_le_prod₀ (s := (Finset.Icc 1 (5*n) : Finset ℕ))
      (f := fun (j : ℕ) => ‖tpt y + (j : ℂ)‖) (g := fun (_ : ℕ) => (8*n : ℝ))
      (fun _ _ => norm_nonneg _) (fun j hj => vertical_root_upper n j hn
        (Finset.mem_Icc.mp hj).2 y (by linarith) hyhi)
    simpa [Nat.card_Icc] using hh
  have hdenpos : 0 < ∏ j ∈ Finset.Icc 1 (5*n), ‖tpt y + (j : ℂ)‖ :=
    Finset.prod_pos fun j _ => hn0.trans_le (vertical_root_lower n j y hylo)
  unfold Rfun
  rw [norm_div, norm_pow, norm_prod, norm_prod]
  have hnum4 := pow_le_pow_left₀ (by positivity) hnum 4
  rw [← pow_mul, mul_comm n 4] at hnum4
  exact (div_le_div_of_nonneg_left (by positivity) hdenpos hden).trans
    (div_le_div_of_nonneg_right hnum4 hdenpos.le)

theorem Sn_log_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n + (5 * Real.log 5 - 5) * n ≤ Real.log (Sn n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 := (factorial_log_error_bounds (5*n) (by omega)).1
  have hlog5 : 0 ≤ Real.log ((5*n : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
  have hnf : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial)
      (show (n.factorial : ℝ) ≤ (n : ℝ)^n by exact_mod_cast Nat.factorial_le_pow n)
    simpa [Real.log_pow] using hh
  have he : Real.log ((5*n : ℕ) : ℝ) = Real.log 5 + Real.log n := by
    push_cast
    rw [Real.log_mul (by norm_num) hn0.ne']
  rw [he] at h5 hlog5
  simp only [Sn, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast at h5 ⊢
  nlinarith

theorem normalized_Rfun_lower (n : ℕ) (hn : 1 ≤ n) (y : ℝ)
    (hylo : (n : ℝ) ≤ y) (hyhi : y ≤ 2*n) :
    Real.exp (-8*n) ≤ (Sn n : ℝ) * ‖Rfun n (tpt y)‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : (0 : ℝ) < Sn n := by exact_mod_cast Sn_pos n
  let L : ℝ := (Sn n : ℝ) * ((n : ℝ)^(4*n) / (8*n : ℝ)^(5*n))
  have hL : 0 < L := by dsimp [L]; positivity
  have hlogL : -8*(n : ℝ) ≤ Real.log L := by
    have hsn := Sn_log_lower n hn
    have hratio := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8/5)
    rw [Real.log_div (by norm_num) (by norm_num)] at hratio
    norm_num at hratio
    dsimp [L]
    rw [Real.log_mul hs.ne' (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hn0.ne']
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hratio hn0.le]
  calc
    Real.exp (-8*n) ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr hlogL
    _ = L := Real.exp_log hL
    _ ≤ _ := mul_le_mul_of_nonneg_left (Rfun_lower n hn y hylo hyhi) hs.le

theorem tanh_ge_half {u : ℝ} (hu : 2 ≤ u) : (1/2 : ℝ) ≤ Real.tanh u := by
  have hpos : 0 < Real.exp u + Real.exp (-u) := by positivity
  have hneg : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hlin := Real.add_one_le_exp u
  rw [Real.tanh_eq, le_div_iff₀ hpos]
  linarith

theorem cosh_le_exp_nonneg {u : ℝ} (hu : 0 ≤ u) : Real.cosh u ≤ Real.exp u := by
  have hh : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
  rw [Real.cosh_eq]
  linarith

theorem exp_neg_two_le_inv_cosh_sq {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-2*u) ≤ 1 / (Real.cosh u)^2 := by
  have hp : 0 < (Real.cosh u)^2 := pow_pos (Real.cosh_pos u) 2
  have hh : (Real.cosh u)^2 ≤ Real.exp (2*u) := by
    calc
      _ ≤ (Real.exp u)^2 := pow_le_pow_left₀ (Real.cosh_pos u).le (cosh_le_exp_nonneg hu) 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hi := one_div_le_one_div_of_le hp hh
  convert hi using 1
  rw [show -2*u = -(2*u) by ring, Real.exp_neg]
  simp only [one_div]

theorem wfun_lower (r : ℚ) (y : ℝ) (hy : 1 ≤ y) :
    Real.exp (-2*Real.pi*y) ≤ ‖wfun r y‖ := by
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  have hu : 2 ≤ Real.pi*y := by nlinarith
  have ht := tanh_ge_half hu
  have hphase : Real.pi ≤ ‖2*(r : ℂ) - 2*Real.pi*Complex.I*(Real.tanh (Real.pi*y) : ℂ)‖ := by
    have hh := Complex.abs_im_le_norm
      (2*(r : ℂ) - 2*Real.pi*Complex.I*(Real.tanh (Real.pi*y) : ℂ))
    have he : (2*(r : ℂ) - 2*Real.pi*Complex.I*(Real.tanh (Real.pi*y) : ℂ)).im =
        -(2*Real.pi*Real.tanh (Real.pi*y)) := by
      generalize Real.tanh (Real.pi*y) = a
      simp
    rw [he, abs_neg, abs_of_nonneg (by positivity)] at hh
    nlinarith
  have hsmall := exp_neg_two_le_inv_cosh_sq (by linarith : 0 ≤ Real.pi*y)
  have hc : 0 < (Real.cosh (Real.pi*y))^2 := pow_pos (Real.cosh_pos _) 2
  unfold wfun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    Real.exp (-2*Real.pi*y) = Real.exp (-2*(Real.pi*y)) := by congr 1; ring
    _ ≤ 1 / (Real.cosh (Real.pi*y))^2 := hsmall
    _ ≤ (Real.pi/2/(Real.cosh (Real.pi*y))^2) * Real.pi := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hc.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hphase (by positivity)

/-- Uniform in r: the imaginary part of the kernel provides the lower bound. -/
theorem gramWeight_scaled_lower (r : ℚ) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hxlo : 1 ≤ x) (hxhi : x ≤ 2) :
    Real.exp (-22*n) ≤ (n : ℝ) * gramWeight r n ((n : ℝ)*x) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hylo : (n : ℝ) ≤ (n : ℝ)*x := by nlinarith
  have hyhi : (n : ℝ)*x ≤ 2*n := by nlinarith
  have ht : (n : ℝ) ≤ ‖tpt ((n : ℝ)*x)‖ := by
    simpa using vertical_root_lower n 0 ((n : ℝ)*x) hylo
  have hR := normalized_Rfun_lower n hn ((n : ℝ)*x) hylo hyhi
  have hw := wfun_lower r ((n : ℝ)*x) (by linarith)
  have hw' : Real.exp (-4*Real.pi*n) ≤ ‖wfun r ((n : ℝ)*x)‖ := by
    apply le_trans _ hw
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hs : (0 : ℝ) ≤ Sn n := by exact_mod_cast (Sn_pos n).le
  have hp := mul_le_mul (mul_le_mul hR ht (by positivity) (by positivity)) hw'
    (Real.exp_nonneg _) (by positivity)
  have hnp := mul_le_mul_of_nonneg_left hp hn0
  unfold gramWeight heinePhi
  rw [norm_mul, norm_mul]
  have hprod : (n : ℝ) * (Real.exp (-8*n) * n * Real.exp (-4*Real.pi*n)) =
      (n : ℝ)^2 * Real.exp ((-8-4*Real.pi)*n) := by
    rw [show (n : ℝ) * (Real.exp (-8*n) * n * Real.exp (-4*Real.pi*n)) =
      (n : ℝ)^2 * (Real.exp (-8*n) * Real.exp (-4*Real.pi*n)) by ring,
      ← Real.exp_add]
    congr 2
    ring
  calc
    Real.exp (-22*n) ≤ Real.exp ((-8-4*Real.pi)*n) := by
      apply Real.exp_le_exp.mpr
      have hb := Real.pi_lt_d2
      nlinarith
    _ ≤ (n : ℝ)^2 * Real.exp ((-8-4*Real.pi)*n) := by
      have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
      nlinarith [Real.exp_pos ((-8-4*Real.pi)*n)]
    _ ≤ _ := by rw [← hprod]; nlinarith only [hnp]

end
end Zeta32Extension
end
