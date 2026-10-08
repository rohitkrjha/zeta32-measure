import Lean
import Lean.Replay

/- Replay the actual proved components and unconditional quantitative
endpoint in a fresh Lean kernel environment. The original conditional
minor-based route is retained, but is not needed by the final theorem.

Run in the pinned upstream checkout after the extension build has finished:
  lake env lean --run /absolute/path/new-constants/VerifyZeta32Components.lean
Do not rebuild imported modules during replay.
-/

open Lean

def checkedRoots : Array Name := #[
  `Zeta32.zeta3_sub_rat_mul_zeta2_irrational,
  `Zeta32.arith_node,
  `Zeta32.prime_edge_node,
  `Zeta32Extension.positiveHeine_eventually_le,
  `Zeta32Extension.normalizedSlope_le_exp,
  `Zeta32Extension.normalizedPencil_det,
  `Zeta32Extension.det_add_le_of_all_minors,
  `Zeta32Extension.eventually_exists_prime_not_dvd_in_log_window,
  `Zeta32Extension.weightedQuadratic_eventually_lower,
  `Zeta32Extension.positiveGram_det,
  `Zeta32Extension.positiveGram_posSemidef,
  `Zeta32Extension.positiveGram_eventually_lower,
  `Zeta32Extension.positiveGram_eventually_posDef,
  `Zeta32Extension.local_decay_of_uniformMinors,
  `Zeta32Extension.denominator_bound_of_uniformMinors,
  `Zeta32Extension.normalizedPencil_bilinear_le,
  `Zeta32Extension.det_le_of_bilinear_gram,
  `Zeta32Extension.perturbed_pencil_bilinear_le,
  `Zeta32Extension.local_decay,
  `Zeta32Extension.denominator_bound,
  `Zeta32Extension.irrationalityExponent_bounds]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let sourceEnv ← importModules #[{ module := `Zeta32Extension.ExponentCorollary }] {}
  let mut pending := checkedRoots
  let mut selected : Std.HashMap Name ConstantInfo := {}
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if selected.contains name then
      continue
    let some info := sourceEnv.find? name |
      throw <| IO.userError s!"Missing dependency {name}"
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"Unsafe or partial dependency {name}"
    if info matches .axiomInfo _ then
      unless permitted.contains name do
        throw <| IO.userError s!"Nonstandard axiom {name}"
    selected := selected.insert name info
    for dependency in info.getUsedConstantsAsSet do
      pending := pending.push dependency
    match info with
    | .defnInfo value => pending := pending ++ value.all.toArray
    | .thmInfo value => pending := pending ++ value.all.toArray
    | .inductInfo value => pending := pending ++ value.all.toArray ++ value.ctors.toArray
    | .ctorInfo value => pending := pending.push value.induct
    | .recInfo value => pending := pending ++ value.all.toArray
    | .quotInfo _ => pending := pending.push `Eq
    | _ => pure ()
  IO.println s!"Replaying {selected.size} dependencies in a fresh Lean kernel environment."
  (← IO.getStdout).flush
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay selected
  for name in checkedRoots do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Missing checked root: {name}"
  IO.println s!"PASS: {checkedRoots.size} component/reduction roots and their dependency closure."
  IO.println "PASS: only propext, Classical.choice and Quot.sound allowed."
  IO.println "SCOPE: unconditional denominator exponent 10,000 for every fixed rational r."
  IO.println "COROLLARY: 2 <= irrationalityExponent (Cr r) <= 10,000."
  IO.println "The direct Gram comparison bypasses the UniformMinors hypothesis."
