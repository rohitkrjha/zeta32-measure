/- Reused from this workspace's completed CatalanExtension development.
This standalone copy has no dependency on the Catalan/OAI project.
The prime window is changed from [500 log q,1500 log q] to [20 log q,60 log q].
-/
module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-! Prime scales logarithmic in the rational denominator. -/

namespace Zeta32Extension

open Filter Finset
open scoped Topology

noncomputable def primeLogInterval (x y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log (p : ℝ)

theorem primeLogInterval_eq_theta_sub {x y : ℝ} (hxy : x ≤ y) :
    primeLogInterval x y = Chebyshev.theta y - Chebyshev.theta x := by
  unfold primeLogInterval Chebyshev.theta
  simp only [Finset.sum_filter]
  have h := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0)
    (Nat.zero_le ⌊x⌋₊) (Nat.floor_le_floor hxy)
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

theorem exists_prime_not_dvd_of_log_lt_interval {q : ℕ} (hq : 0 < q)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hsum : Real.log (q : ℝ) < primeLogInterval x y) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y ∧ ¬ p ∣ q := by
  classical
  by_contra h
  push Not at h
  let s := (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime
  have hs : s ⊆ q.primeFactors := by
    intro p hp
    obtain ⟨hpi, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hpi
    exact hprime.mem_primeFactors
      (h p hprime ((Nat.floor_lt hx).mp hlo)
        ((Nat.le_floor_iff (hx.trans hxy)).mp hhi)) hq.ne'
  have hprod : (∏ p ∈ s, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset s q.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd q)
  have hprodpos : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp =>
    (Finset.mem_filter.mp hp).2.pos
  have hlog : primeLogInterval x y = Real.log ((∏ p ∈ s, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    · rfl
    · intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  rw [hlog] at hsum
  exact (not_lt_of_ge (Real.log_le_log (by exact_mod_cast hprodpos)
    (by exact_mod_cast Nat.le_of_dvd hq hprod))) hsum

/-- A coarse interval lower bound, using only elementary Chebyshev estimates,
not the prime number theorem. -/
theorem eventually_primeLogInterval_gt_quarter :
    ∀ᶠ x : ℝ in atTop, x / 4 < primeLogInterval x (3 * x) := by
  have hsmall : ∀ᶠ y : ℝ in atTop,
      ‖Real.log y‖ ≤ (1 / 100 : ℝ) * ‖y ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound (by norm_num)
  have hlinear : ∀ᶠ y : ℝ in atTop,
      ‖Real.log y‖ ≤ (1 / 100 : ℝ) * ‖y ^ (1 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound (by norm_num)
  have h3 : Tendsto (fun x : ℝ => 3 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have h32 : Tendsto (fun x : ℝ => 3 * x + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) h3
  filter_upwards [eventually_ge_atTop (10 : ℝ), h3.eventually hsmall,
    h32.eventually hlinear] with x hx hlog hlog2
  have hx0 : 0 ≤ x := by linarith
  have h3x : 0 ≤ 3 * x := by positivity
  have h32x : 0 ≤ 3 * x + 2 := by positivity
  have hlog' : Real.log (3 * x) ≤ (1 / 100 : ℝ) * Real.sqrt (3 * x) := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h3x _),
      ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] using hlog
  have hlog2' : Real.log (3 * x + 2) ≤ (1 / 100 : ℝ) * (3 * x + 2) := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg h32x] using hlog2
  have hroot := mul_le_mul_of_nonneg_left hlog' (Real.sqrt_nonneg (3 * x))
  have hsq := Real.sq_sqrt h3x
  have hlo := Chebyshev.theta_ge' (x := 3 * x) (by linarith)
  have hhi := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [hlog4] at hhi
  rw [primeLogInterval_eq_theta_sub (by linarith : x ≤ 3 * x)]
  nlinarith [mul_le_mul_of_nonneg_right hlog2lo hx0]

/-- A prime avoiding the denominator exists at a logarithmic scale. The
constant cutoff may be arbitrary but must be independent of `q`. -/
theorem eventually_exists_prime_not_dvd_in_log_window (cutoff : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ cutoff < p ∧
      20 * Real.log (q : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ 60 * Real.log (q : ℝ) ∧ ¬ p ∣ q := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun q : ℕ => 20 * Real.log (q : ℝ)) atTop atTop :=
    hlog.const_mul_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hscale.eventually eventually_primeLogInterval_gt_quarter,
    hscale.eventually_ge_atTop (cutoff : ℝ)] with q hq hsum hcut
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hsum' : Real.log (q : ℝ) <
      primeLogInterval (20 * Real.log (q : ℝ)) (3 * (20 * Real.log (q : ℝ))) :=
    (by linarith : Real.log (q : ℝ) < 20 * Real.log (q : ℝ) / 4).trans hsum
  obtain ⟨p, hp, hlo, hhi, hndvd⟩ := exists_prime_not_dvd_of_log_lt_interval
    (by omega : 0 < q) (by positivity) (by nlinarith) hsum'
  refine ⟨p, hp, ?_, hlo, ?_, hndvd⟩
  · exact_mod_cast hcut.trans_lt hlo
  · nlinarith [hhi]

end Zeta32Extension
end
