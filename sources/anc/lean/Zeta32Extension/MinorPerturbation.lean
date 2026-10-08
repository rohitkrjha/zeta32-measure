/- Reused from this workspace's completed CatalanExtension development.
This standalone copy has no dependency on the Catalan/OAI project.
-/
module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Perturbing a matrix with uniform complementary-minor bounds

This is finite-dimensional determinant algebra, not an assertion that the
required Catalan minor bounds hold. It preserves the small full-determinant
scale instead of replacing every entry by a common coarse bound.
-/

namespace Zeta32Extension

open scoped BigOperators

theorem fin_selected_remove_card {m : ℕ} (s : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) (hi : i ∈ s) :
    (Finset.univ.filter (fun r : Fin m => i.succAbove r ∈ s)).card + 1 = s.card := by
  have h := Fin.sum_univ_succAbove (fun r => if r ∈ s then (1 : ℕ) else 0) i
  simpa [hi, Nat.add_comm] using h.symm

theorem mixed_minor_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    {R S K : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hA : ∀ m, m ≤ n → ∀ rows cols : Fin m ↪ Fin n,
      |(A.submatrix rows cols).det| ≤ R * S ^ (n - m))
    (hB : ∀ i j, |B i j| ≤ K) :
    ∀ m, m ≤ n → ∀ rows cols : Fin m ↪ Fin n, ∀ s : Finset (Fin m),
      |Matrix.det (s.piecewise (B.submatrix rows cols) (A.submatrix rows cols))| ≤
        R * S ^ (n - m) * ((n : ℝ) * K * S) ^ s.card := by
  classical
  intro m
  induction m with
  | zero =>
    intro hm rows cols s
    have hs : s = ∅ := Subsingleton.elim _ _
    subst s
    have heq : (∅ : Finset (Fin 0)).piecewise (B.submatrix rows cols)
        (A.submatrix rows cols) = A.submatrix rows cols := by
      funext i
      exact Fin.elim0 i
    rw [heq]
    simpa using hA 0 hm rows cols
  | succ m ih =>
    intro hm rows cols s
    by_cases hs : s = ∅
    · subst s
      have heq : (∅ : Finset (Fin (m + 1))).piecewise (B.submatrix rows cols)
          (A.submatrix rows cols) = A.submatrix rows cols := by
        ext i j
        simp [Finset.piecewise]
      rw [heq]
      simpa using hA (m + 1) hm rows cols
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    let t : Finset (Fin m) := Finset.univ.filter (fun r => i.succAbove r ∈ s)
    have hcard : t.card + 1 = s.card := fin_selected_remove_card s i hi
    let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
      s.piecewise (B.submatrix rows cols) (A.submatrix rows cols)
    have hminor (j : Fin (m + 1)) :
        |(M.submatrix i.succAbove j.succAbove).det| ≤
          R * S ^ (n - m) * ((n : ℝ) * K * S) ^ t.card := by
      have hh := ih (by omega) (i.succAboveEmb.trans rows) (j.succAboveEmb.trans cols) t
      have heq : M.submatrix i.succAbove j.succAbove =
          t.piecewise (B.submatrix (i.succAboveEmb.trans rows) (j.succAboveEmb.trans cols))
            (A.submatrix (i.succAboveEmb.trans rows) (j.succAboveEmb.trans cols)) := by
        ext r k
        by_cases hr : i.succAbove r ∈ s <;>
          simp [M, t, Matrix.submatrix, Finset.piecewise, hr]
      simpa only [heq] using hh
    have hterm (j : Fin (m + 1)) :
        |(-1 : ℝ) ^ (i.val + j.val) * M i j *
          (M.submatrix i.succAbove j.succAbove).det| ≤
        K * (R * S ^ (n - m) * ((n : ℝ) * K * S) ^ t.card) := by
      have hentry : |M i j| ≤ K := by simpa [M, hi, Finset.piecewise] using hB (rows i) (cols j)
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul hentry (hminor j) (abs_nonneg _) hK
    change |M.det| ≤ _
    calc
      _ ≤ ∑ j : Fin (m + 1),
          |(-1 : ℝ) ^ (i.val + j.val) * M i j *
            (M.submatrix i.succAbove j.succAbove).det| := by
        rw [Matrix.det_succ_row M i]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (m + 1 : ℕ) *
          (K * (R * S ^ (n - m) * ((n : ℝ) * K * S) ^ t.card)) := by
        simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
      _ ≤ (n : ℝ) *
          (K * (R * S ^ (n - m) * ((n : ℝ) * K * S) ^ t.card)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
      _ = _ := by
        rw [← hcard, show n - m = n - (m + 1) + 1 by omega, pow_succ, pow_succ]
        ring

/-- A uniform all-minors bound is stable under an entrywise perturbation.
The multiplicative loss is explicit and tends to one when `n K S` is small. -/
theorem det_add_le_of_all_minors {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    {R S K : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hA : ∀ m, m ≤ n → ∀ rows cols : Fin m ↪ Fin n,
      |(A.submatrix rows cols).det| ≤ R * S ^ (n - m))
    (hB : ∀ i j, |B i j| ≤ K) :
    |(A + B).det| ≤ R * (1 + (n : ℝ) * K * S) ^ n := by
  classical
  have hexpand : (A + B).det =
      ∑ s : Finset (Fin n), Matrix.det (s.piecewise B A) := by
    change Matrix.detRowAlternating (A + B) = _
    rw [add_comm A B]
    exact Matrix.detRowAlternating.map_add_univ B A
  have hterm (s : Finset (Fin n)) :
      |Matrix.det (s.piecewise B A)| ≤ R * ((n : ℝ) * K * S) ^ s.card := by
    have h := mixed_minor_le A B hR hS hK hA hB n le_rfl
      (Function.Embedding.refl _) (Function.Embedding.refl _) s
    change |Matrix.det (s.piecewise B A)| ≤ R * S ^ (n - n) *
      ((n : ℝ) * K * S) ^ s.card at h
    simpa using h
  calc
    _ ≤ ∑ s : Finset (Fin n), |Matrix.det (s.piecewise B A)| := by
      rw [hexpand]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Finset (Fin n), R * ((n : ℝ) * K * S) ^ s.card :=
      Finset.sum_le_sum (fun s _ => hterm s)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [one_pow, mul_one, Fintype.card_fin, add_comm] using
        Fintype.sum_pow_mul_eq_add_pow (Fin n) ((n : ℝ) * K * S) (1 : ℝ)

end Zeta32Extension
end
