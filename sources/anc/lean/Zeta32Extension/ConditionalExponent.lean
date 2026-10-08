module
public import Zeta32Extension.Stability
public import Zeta32Extension.PrimeWindow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
open Zeta32 Polynomial Filter Topology

namespace Zeta32Extension

/-- The prime-window arithmetic reduction, separated from the choice of
analytic proof of local decay. -/
theorem denominator_bound_of_local_decay (r : ℚ)
    (hLocal : ∀ᶠ n : ℕ in atTop, Q r n ≠ 0 → ∀ x : ℝ,
      |x-Cr r| ≤ Real.exp (-120*n) →
        |aeval x (P r n)| ≤ Real.exp (-(3/10 : ℝ)*(n : ℝ)^2)) :
    ∀ᶠ b : ℕ in atTop, ∀ z : ℚ, z.den = b →
      (b : ℝ)^(-10000 : ℝ) < |Cr r - (z : ℝ)| := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hLocal
  let cutoff := max (max (max 7 (r.den+1)) (PrimeEdge.exceptional.sup id+1)) (N+2)
  have hlog : Tendsto (fun b : ℕ => Real.log (b : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_prime_not_dvd_in_log_window cutoff,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop (2 : ℕ)] with b hb hlogb hb2
  intro z hz
  obtain ⟨p, hp, hpcut, hplo, hphi, hpndvd⟩ := hb
  have hp7 : 7 ≤ p := by
    have : 7 ≤ cutoff := by dsimp [cutoff]; omega
    omega
  have hpr : ¬ p ∣ r.den := by
    have : r.den+1 ≤ cutoff := by dsimp [cutoff]; omega
    intro hd
    have hh := Nat.le_of_dvd r.den_pos hd
    omega
  have hpE : p ∉ PrimeEdge.exceptional := by
    have : PrimeEdge.exceptional.sup id+1 ≤ cutoff := by dsimp [cutoff]; omega
    intro hm
    have hh : p ≤ PrimeEdge.exceptional.sup id := Finset.le_sup (f := id) hm
    omega
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc, hred⟩ := prime_edge_node r p hp7 hpE hpr
  have hzb : (z.den : ZMod p) ≠ 0 := by
    rw [hz]
    exact fun he => hpndvd ((ZMod.natCast_eq_zero_iff b p).mp he)
  have hne := rational_nonzero_of_constant_reduction (P r (p-1)) p c hc hred z hzb
  have hQ : Q r (p-1) ≠ 0 := by
    intro he
    have hP := P_eq_zero_of_Q_eq_zero r (p-1) he
    simp [hP] at hne
  have hnN : N ≤ p-1 := by
    have : N+2 ≤ cutoff := by dsimp [cutoff]; omega
    omega
  have hncast : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hnlo : 19 * Real.log (b : ℝ) < ((p-1 : ℕ) : ℝ) := by
    rw [hncast]
    linarith
  have hnhi : ((p-1 : ℕ) : ℝ) ≤ 60 * Real.log (b : ℝ) := by
    rw [hncast]
    linarith
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  by_contra hbad
  have herr : |Cr r - (z : ℝ)| ≤ (b : ℝ)^(-10000 : ℝ) := le_of_not_gt hbad
  have hnear : |(z : ℝ)-Cr r| ≤ Real.exp (-120*((p-1 : ℕ) : ℝ)) := by
    rw [abs_sub_comm]
    refine herr.trans ?_
    rw [Real.rpow_def_of_pos hbpos]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsmall := hN (p-1) hnN hQ (z : ℝ) hnear
  have hlarge := one_le_den_pow_mul_abs (P r (p-1)) z (3*(p-1))
    (P_natDegree_le r (p-1)) hne
  rw [hz] at hlarge
  have hupper : (b : ℝ)^(3*(p-1)) * |aeval (z : ℝ) (P r (p-1))| < 1 := by
    calc
      _ ≤ (b : ℝ)^(3*(p-1)) * Real.exp (-(3/10 : ℝ)*((p-1 : ℕ) : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = Real.exp (3*((p-1 : ℕ) : ℝ)*Real.log b -
          (3/10 : ℝ)*((p-1 : ℕ) : ℝ)^2) := by
        rw [← Real.exp_log (pow_pos hbpos _), Real.log_pow, ← Real.exp_add]
        push_cast
        congr 1
        ring
      _ < 1 := by
        rw [Real.exp_lt_one_iff]
        have hnpos : (0 : ℝ) < ((p-1 : ℕ) : ℝ) := by linarith
        nlinarith [mul_pos hnpos (show (0 : ℝ) < ((p-1 : ℕ) : ℝ) -
          10 * Real.log (b : ℝ) by linarith)]
  linarith

/-- Original conditional route, retained with its hypothesis visible.
`DirectStability.local_decay` supplies a different, unconditional route. -/
theorem denominator_bound_of_uniformMinors (r : ℚ)
    (hM : ∀ᶠ n : ℕ in atTop, UniformMinors r n) :
    ∀ᶠ b : ℕ in atTop, ∀ z : ℚ, z.den = b →
      (b : ℝ)^(-10000 : ℝ) < |Cr r - (z : ℝ)| := by
  apply denominator_bound_of_local_decay r
  filter_upwards [local_decay_of_uniformMinors r, hM] with n h hn
  exact h hn

#print axioms denominator_bound_of_uniformMinors

end Zeta32Extension
end
