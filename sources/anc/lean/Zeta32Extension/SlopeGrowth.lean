module
public import Zeta32.Arith.Outer.Entries
public import Zeta32.Arith.Small.Binom
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic

@[expose] public section
open Zeta32 Polynomial
open scoped BigOperators

namespace Zeta32Extension
noncomputable section

theorem D_eval_neg_choose (n j : ℕ) (hj : 1 ≤ j) :
    (D n).eval (-(j : ℚ)) =
      (-1 : ℚ)^n * (n.factorial : ℚ) * ((j-1).choose n : ℚ) := by
  by_cases hnj : n < j
  · rw [Zeta32.Outer.D_eval_neg_of_lt n j hnj]
    have hc : ((j-1).choose n : ℚ) * (n.factorial : ℚ) *
        ((j-1-n).factorial : ℚ) = ((j-1).factorial : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (n := j-1) (k := n) (by omega)
    have hf : ((j-1-n).factorial : ℚ) ≠ 0 := by positivity
    rw [← hc]
    field_simp
  · rw [Zeta32.Outer.D_eval_neg_of_le hj (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Exact normalized residue; the bound can be obtained without complex
Cauchy estimates or asymptotic factorial estimates. -/
theorem scaled_rs_eq (n j : ℕ) (hj : 1 ≤ j) (hj5 : j ≤ 5*n) :
    Sn n * Zeta32.Outer.rs n j =
      (-1 : ℚ)^(j-1) * (5*n : ℕ) * ((5*n-1).choose (j-1) : ℚ) *
        ((j-1).choose n : ℚ)^4 := by
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  have he : Zeta32.Outer.eraseProd (5*n) j ≠ 0 :=
    Zeta32.Outer.eraseProd_ne_zero hj hj5
  have hs : ((-1 : ℚ)^n)^4 = 1 := by
    rw [← pow_mul, mul_comm n 4, pow_mul]
    norm_num
  calc
    Sn n * Zeta32.Outer.rs n j =
        ((5*n).factorial : ℚ) / Zeta32.Arith.Small.eraseProd (5*n) j *
          ((j-1).choose n : ℚ)^4 := by
      unfold Sn Zeta32.Outer.rs
      rw [D_eval_neg_choose n j hj, mul_pow, mul_pow, hs, one_mul]
      change _ = ((5*n).factorial : ℚ) / Zeta32.Outer.eraseProd (5*n) j * _
      field_simp
    _ = _ := by rw [Zeta32.Arith.Small.residueScale_eq hj hj5]

theorem abs_scaled_rs_le (n j : ℕ) (hj : 1 ≤ j) (hj5 : j ≤ 5*n) :
    |((Sn n * Zeta32.Outer.rs n j : ℚ) : ℝ)| ≤
      (5*n : ℝ) * (2 : ℝ)^(25*n) := by
  rw [scaled_rs_eq n j hj hj5]
  push_cast
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ ((5*n-1).choose (j-1) : ℕ) from Nat.cast_nonneg _),
    abs_of_nonneg (show (0 : ℝ) ≤ ((j-1).choose n : ℕ) from Nat.cast_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * n)]
  have hc1 : (((5*n-1).choose (j-1) : ℕ) : ℝ) ≤ (2 : ℝ)^(5*n) := by
    have hb : (((5*n-1).choose (j-1) : ℕ) : ℝ) ≤ (2 : ℝ)^(5*n-1) := by
      exact_mod_cast Nat.choose_le_two_pow (5*n-1) (j-1)
    exact hb.trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hc2 : (((j-1).choose n : ℕ) : ℝ) ≤ (2 : ℝ)^(5*n) := by
    have hb : (((j-1).choose n : ℕ) : ℝ) ≤ (2 : ℝ)^(j-1) := by
      exact_mod_cast Nat.choose_le_two_pow (j-1) n
    exact hb.trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  calc
    _ ≤ (5*n : ℝ) * (2 : ℝ)^(5*n) * ((2 : ℝ)^(5*n))^4 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hc1 (by positivity)
      · exact pow_le_pow_left₀ (by positivity) hc2 4
      · positivity
      · positivity
    _ = _ := by
      rw [mul_assoc, ← pow_mul, ← pow_add]
      congr 2
      omega

theorem abs_scaled_residue_le (n k j : ℕ) (hj : 1 ≤ j) (hj5 : j ≤ 5*n) :
    |((Sn n * residue n k j : ℚ) : ℝ)| ≤
      (5*n : ℝ) * (2 : ℝ)^(25*n) * (5*n : ℝ)^k := by
  rw [Zeta32.Outer.residue_eq]
  have he : Sn n * ((-(j : ℚ))^k * Zeta32.Outer.rs n j) =
      (Sn n * Zeta32.Outer.rs n j) * (-(j : ℚ))^k := by ring
  rw [he, Rat.cast_mul, abs_mul]
  have hp : |(((-(j : ℚ))^k : ℚ) : ℝ)| ≤ (5*n : ℝ)^k := by
    push_cast
    simp only [abs_pow, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ j from Nat.cast_nonneg _)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hj5) k
  exact mul_le_mul (abs_scaled_rs_le n j hj hj5) hp (abs_nonneg _) (by positivity)

theorem abs_scaled_slope_le (n k : ℕ) :
    |((Sn n * slope n k : ℚ) : ℝ)| ≤
      250 * (n : ℝ)^3 * (2 : ℝ)^(25*n) * (5*n : ℝ)^k := by
  have he : Sn n * slope n k =
      ∑ j ∈ Finset.Icc 1 (5*n), (Sn n * residue n k j) * (2*j) := by
    simp only [slope, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, Rat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 (5*n), |(((Sn n * residue n k j) * (2*j) : ℚ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 (5*n),
        ((5*n : ℝ) * (2 : ℝ)^(25*n) * (5*n : ℝ)^k) * (10*n) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj, hj5⟩ := Finset.mem_Icc.mp hj
      rw [Rat.cast_mul, abs_mul]
      apply mul_le_mul (abs_scaled_residue_le n k j hj hj5)
      · push_cast
        rw [abs_of_nonneg (by positivity)]
        have : (j : ℝ) ≤ 5*n := by exact_mod_cast hj5
        linarith
      · exact abs_nonneg _
      · positivity
    _ = _ := by simp [Nat.card_Icc]; ring

/-- The normalized X-coefficient of the rational pencil. -/
def normalizedSlope (n j k : ℕ) : ℝ :=
  (Sn n : ℝ) * (slope n (j+k) : ℝ) / ((j.factorial : ℝ) * (k.factorial : ℝ))

theorem normalizedSlope_crude (n j k : ℕ) :
    |normalizedSlope n j k| ≤
      250 * (n : ℝ)^3 * (2 : ℝ)^(25*n) * Real.exp (10*n) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) * (k.factorial : ℝ) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (5*n) (by positivity : (0 : ℝ) ≤ 5*n) j
  have h2 := Real.pow_div_factorial_le_exp (5*n) (by positivity : (0 : ℝ) ≤ 5*n) k
  unfold normalizedSlope
  rw [abs_div, abs_of_pos hf, ← Rat.cast_mul]
  calc
    _ ≤ (250 * (n : ℝ)^3 * (2 : ℝ)^(25*n) * (5*n : ℝ)^(j+k)) /
        ((j.factorial : ℝ) * (k.factorial : ℝ)) :=
      div_le_div_of_nonneg_right (abs_scaled_slope_le n (j+k)) hf.le
    _ = (250 * (n : ℝ)^3 * (2 : ℝ)^(25*n)) *
        (((5*n : ℝ)^j / (j.factorial : ℝ)) * ((5*n : ℝ)^k / (k.factorial : ℝ))) := by
      rw [pow_add]; field_simp
    _ ≤ (250 * (n : ℝ)^3 * (2 : ℝ)^(25*n)) *
        (Real.exp (5*n) * Real.exp (5*n)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul h1 h2 (by positivity) (Real.exp_nonneg _)
      · positivity
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- A uniform exponential entry bound for the actual normalized slope.
The indices need not be restricted to the pencil size. -/
theorem normalizedSlope_le_exp (n j k : ℕ) (hn : 1 ≤ n) :
    |normalizedSlope n j k| ≤ Real.exp (50*n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh
    exact hh
  have hpow : (2 : ℝ)^(25*n) ≤ Real.exp (25*n) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (25*n)
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using hh
  have h250 : (250 : ℝ) ≤ Real.exp (8*n) := by
    calc
      _ ≤ (2 : ℝ)^8 := by norm_num
      _ ≤ (Real.exp 1)^8 := pow_le_pow_left₀ (by norm_num) htwo 8
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (8*n) := Real.exp_le_exp.mpr (by linarith)
  have hnexp : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hcube : (n : ℝ)^3 ≤ Real.exp (3*n) := by
    have hh := pow_le_pow_left₀ hn0 hnexp 3
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hh
  calc
    _ ≤ 250 * (n : ℝ)^3 * (2 : ℝ)^(25*n) * Real.exp (10*n) :=
      normalizedSlope_crude n j k
    _ ≤ (Real.exp (8*n) * Real.exp (3*n)) * Real.exp (25*n) * Real.exp (10*n) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul (mul_le_mul h250 hcube (by positivity) (Real.exp_nonneg _)) hpow
        (by positivity) (by positivity)
    _ = Real.exp (46*n) := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (50*n) := Real.exp_le_exp.mpr (by linarith)

#print axioms normalizedSlope_le_exp

end
end Zeta32Extension
end
