module

public import Weierstrass.DescentTheorem
public import Weierstrass.BranchAnchor
public import Weierstrass.AlgebraicSplit

/-! Theorem 1.1 for arbitrary real bases and prescribed phases. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology
namespace Weierstrass

/-- Theorem 1.1. The natural measure is the image of normalized Lebesgue
measure on the specified bounded interval. -/
theorem main_theorem : MainStatement :=
  main_of_analytic_inputs Descent.all_differentiation_rules Branch.branching_anchored

/-- The two conclusions with the exponent written as in the introduction. -/
theorem graph_and_measure_real_base {b lam : ℝ} (hb : 1<b) (hl : b⁻¹<lam) (hl1 : lam<1)
    (φ : ℕ → ℝ) (I : Set ℝ) (hI : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b lam φ I) = ENNReal.ofReal (2+Real.log lam/Real.log b) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b lam φ I) (2+Real.log lam/Real.log b)) := by
  rw [←dimension_formula];exact main_theorem b lam hb hl hl1 φ I hI hi

end Weierstrass
