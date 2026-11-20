module

import Weierstrass
import Lean.Util.CollectAxioms
import Lean.Compiler.Old
import Lean.Elab.Command

/-! Inspect the transitive dependencies of every exported project declaration.
The target is deliberately printed as a proposition rather than accepted as
a new axiom. Changes in the status of the target should be reported explicitly. -/

open Lean Elab Command in
set_option maxHeartbeats 5000000 in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut observed : Array Name := #[]
  for (name, info) in env.constants.toList do
    if !(`Weierstrass).isPrefixOf name then continue
    if info.isUnsafe then
      -- The code generator emits a runtime companion for structural recursion.
      -- The safe, kernel-checked parent is included in this same dependency audit.
      match Compiler.isUnsafeRecName? name with
      | some parent =>
        if let some checked := env.find? parent then
          unless checked.isUnsafe do continue
      | none => pure ()
      throwError "unsafe project declaration: {name}"
    -- An opaque theorem can be exposed as an axiom-shaped public interface.
    -- collectAxioms consults the dependency record exported from its checked proof.
    count := count + 1
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError "unexpected axiom {ax} in {name}"
      unless observed.contains ax do observed := observed.push ax
  if count == 0 then throwError "no project declarations loaded"
  logInfo m!"Checked {count} public declarations; transitive axioms: {observed}."
  match env.find? `Weierstrass.MainStatement with
  | some (.defnInfo _) => logInfo "MainStatement is declared as a proof target."
  | _ => throwError "expected MainStatement to be the specification"

#check Weierstrass.MainStatement
#print axioms Weierstrass.graph_dim_le_formula
#print axioms Weierstrass.mainStatement_iff_exactDimensionOnBoundedIntervals
#print axioms Weierstrass.fullBallFromRetainedCollisions
#print axioms Weierstrass.anchoredEstimate_transcendental
#print axioms Weierstrass.anchored_physical_entropy
#print axioms Weierstrass.CriticalRay.critical_linearization
#print axioms Weierstrass.GraphInformation.exists_vertical_origin
#print axioms Weierstrass.graph_of_anchored_estimate
#print axioms Weierstrass.graph_and_measure_transcendental
#print axioms Weierstrass.CriticalRay.critical_drift_anticoncentration
#print axioms Weierstrass.RaySeed.uniform_transverse_derivative
#print axioms Weierstrass.StripProof.strip_estimate
#print axioms Weierstrass.graph_and_measure_critical_real
#print axioms Weierstrass.Predecessor.haar_sharp_initial_collisions
#print axioms Weierstrass.Predecessor.haar_sharp_initial_lower_dimension
#print axioms Weierstrass.RaySeed.rayInformation_half

#print axioms Weierstrass.graph_and_measure_critical_conjugate
#print axioms Weierstrass.Angular.rayInformation_half_family
#print axioms Weierstrass.Descent.derivative_cell_oscillation

#print axioms Weierstrass.graph_and_measure_reciprocal_conjugate
#print axioms Weierstrass.Descent.bad_label_probability
#print axioms Weierstrass.StripProof.equal_rate_angular_conjugate
#print axioms Weierstrass.graph_and_measure_contracting_conjugate
#print axioms Weierstrass.Predecessor.slopeInformation_all
#print axioms Weierstrass.cusp_local_dimension
#print axioms Weierstrass.main_theorem
#print axioms Weierstrass.Predecessor.conditional_slope_exact_dimension
#print axioms Weierstrass.Branch.conditional_slopes_graph
#print axioms Weierstrass.graph_and_measure_circle_phases
