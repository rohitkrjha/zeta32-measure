module
public import Zeta32.Final
public import Zeta32Extension.PositiveEnergy

@[expose] public section
open Filter Topology

namespace Zeta32Extension

/-- Unconditional decay of the positive Heine majorant, not merely the signed
determinant. This is an analytic input, not a finite irrationality exponent. -/
theorem positiveHeine_eventually_le (r : ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      positiveHeine r n ≤ Real.exp ((-6 + ε) * (n : ℝ)^2) :=
  positive_energy_bound_exp r
    (Zeta32.Fstar.fstarInput_of_points Zeta32.fstarPoints) ε hε

#print axioms positiveHeine_eventually_le
#print axioms Zeta32.zeta3_sub_rat_mul_zeta2_irrational

end Zeta32Extension
end
