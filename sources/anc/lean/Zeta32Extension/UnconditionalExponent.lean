module
public import Zeta32Extension.DirectStability
public import Zeta32Extension.ConditionalExponent

@[expose] public section
namespace Zeta32Extension
open Zeta32 Filter

/-- Unconditional denominator exponent for every fixed rational parameter.
All analytic, arithmetic, and nonvanishing inputs are discharged. -/
theorem denominator_bound (r : ℚ) :
    ∀ᶠ b : ℕ in atTop, ∀ z : ℚ, z.den = b →
      (b : ℝ)^(-10000 : ℝ) < |Cr r - (z : ℝ)| :=
  denominator_bound_of_local_decay r (local_decay r)

#print axioms denominator_bound

end Zeta32Extension
end
