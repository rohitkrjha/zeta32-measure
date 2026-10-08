/-
The approximation-set definitions and the two elementary finite-denominator /
Dirichlet lemmas are adapted from OpenAI's Apache-2.0 PiExponent/Statement.lean
and PiExponent/Approximation/Exponent.lean, September 2026. The quantitative
bound here uses the independent Zeta32Extension denominator theorem.
-/
module
public import Zeta32Extension.UnconditionalExponent
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

@[expose] public section
namespace Zeta32Extension
open Zeta32 Filter

def GoodRationalApproximations (x ν : ℝ) : Set ℚ :=
  {z | 2 ≤ z.den ∧ 0 < |x - (z : ℝ)| ∧ |x - (z : ℝ)| < (z.den : ℝ)^(-ν)}

def ApproximationExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧ (GoodRationalApproximations x ν).Infinite}

/-- The real supremum is used only after proving the approximation-exponent
set nonempty and bounded above. No assertion about unbounded sets is made. -/
noncomputable def irrationalityExponent (x : ℝ) : ℝ := sSup (ApproximationExponents x)

theorem finite_rat_den_le_abs_sub_lt_one (x : ℝ) (N : ℕ) :
    {z : ℚ | z.den ≤ N ∧ |x - (z : ℝ)| < 1}.Finite := by
  classical
  let f : ℚ → ℤ × ℕ := fun z => (z.num, z.den)
  have hinj : Function.Injective f := by
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hp.1, hp.2]
  let t : Set (ℤ × ℕ) := ⋃ (q : ℕ) (_ : q ∈ Set.Icc 1 N),
    Set.Icc ⌈(x - 1) * q⌉ ⌊(x + 1) * q⌋ ×ˢ {q}
  have ht : t.Finite :=
    Set.Finite.biUnion (Set.finite_Icc _ _) fun q _ =>
      Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_singleton _)
  have hsub : f '' {z : ℚ | z.den ≤ N ∧ |x - (z : ℝ)| < 1} ⊆ t := by
    rintro _ ⟨z, ⟨hzN, hz⟩, rfl⟩
    have hzden : (0 : ℝ) < z.den := Nat.cast_pos.mpr z.pos
    have hzlow : x - 1 < (z : ℝ) := by linarith [(abs_lt.mp hz).2]
    have hzhigh : (z : ℝ) < x + 1 := by linarith [(abs_lt.mp hz).1]
    have hnlow : (x - 1) * z.den ≤ (z.num : ℝ) := by
      rw [Rat.cast_def] at hzlow
      exact ((lt_div_iff₀ hzden).mp hzlow).le
    have hnhigh : (z.num : ℝ) ≤ (x + 1) * z.den := by
      rw [Rat.cast_def] at hzhigh
      exact ((div_lt_iff₀ hzden).mp hzhigh).le
    simp only [t, Set.mem_iUnion]
    refine ⟨z.den, ⟨z.pos, hzN⟩, ?_⟩
    exact ⟨⟨Int.ceil_le.mpr hnlow, Int.le_floor.mpr hnhigh⟩, rfl⟩
  exact (ht.subset hsub).of_finite_image hinj.injOn

theorem two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by
  refine ⟨by norm_num, ?_⟩
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hf := finite_rat_den_le_abs_sub_lt_one x 1
  apply (hi.sdiff hf).mono
  intro z hz
  have hzden : 1 ≤ (z.den : ℝ) := by exact_mod_cast z.pos
  have hzone : |x - (z : ℝ)| < 1 :=
    hz.1.trans_le (by
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by nlinarith : (1 : ℝ) ≤ (z.den : ℝ)^2))
  have hz2 : 2 ≤ z.den := by
    by_contra h
    exact hz.2 ⟨by omega, hzone⟩
  refine ⟨hz2, abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat z)), ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.rpow_neg (Nat.cast_nonneg z.den),
    Real.rpow_two, one_div] using hz.1

theorem finite_goodRationalApproximations (r : ℚ) {ν : ℝ} (hν : 10000 ≤ ν) :
    (GoodRationalApproximations (Cr r) ν).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (denominator_bound r)
  apply (finite_rat_den_le_abs_sub_lt_one (Cr r) N).subset
  intro z hz
  have hlt : z.den < N := by
    by_contra hn
    have hh := hN z.den (by omega) z rfl
    have hp : (z.den : ℝ)^(-ν) ≤ (z.den : ℝ)^(-10000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast z.pos) (by linarith)
    exact (not_lt_of_ge ((hz.2.2.trans_le hp).le)) hh
  refine ⟨hlt.le, hz.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast z.pos) (by linarith)

theorem approximationExponents_bounded (r : ℚ) :
    ∀ ν ∈ ApproximationExponents (Cr r), ν ≤ 10000 := by
  intro ν hν
  by_contra hn
  exact (finite_goodRationalApproximations r (by linarith)).not_infinite hν.2

/-- Fully discharged irrationality-exponent bounds for every fixed rational r. -/
theorem irrationalityExponent_bounds (r : ℚ) :
    2 ≤ irrationalityExponent (Cr r) ∧ irrationalityExponent (Cr r) ≤ 10000 := by
  have hi : Irrational (Cr r) := zeta3_sub_rat_mul_zeta2_irrational r
  have htwo := two_mem_approximationExponents hi
  have hb := approximationExponents_bounded r
  exact ⟨le_csSup ⟨10000, hb⟩ htwo, csSup_le ⟨2, htwo⟩ hb⟩

#print axioms irrationalityExponent_bounds

end Zeta32Extension
end
