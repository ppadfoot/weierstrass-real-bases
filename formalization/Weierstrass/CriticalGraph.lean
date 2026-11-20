module

public import Weierstrass.RayInformationTransport
public import Weierstrass.GraphComparison
public import Weierstrass.AngularWeights

/-! Both conclusions for a real contracting conjugate at the critical amplitude. -/
public noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators
namespace Weierstrass

/-- The main theorem at critical amplitude with any contracting conjugate,
including a nonreal image. The unit direction is chosen after the multiplier.
There are no small-ball or auxiliary nondegeneracy hypotheses. -/
theorem graph_and_measure_critical_conjugate {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K)
    {b l : ℝ} (hσ : σ a = (b:ℂ)) (hb : 1 < b) (hr : 0 < ‖τ a‖) (hr1 : ‖τ a‖ < 1)
    (hl : b⁻¹ < l) (hl1 : l < 1) (critical : l*b*‖τ a‖=1) (phase : ℕ → ℝ) (I : Set ℝ)
    (hc : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b l phase I) = ENNReal.ofReal (2-alpha b l) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b l phase I) (2-alpha b l)) := by
  have hb0 := zero_lt_one.trans hb
  have normb : ‖(b:ℂ)‖ = b := by simp [abs_of_pos hb0]
  have hD := norm_pos_iff.mp hr
  let ζ := Angular.rotation (τ a) hD
  obtain ⟨v,base⟩ := Angular.exists_admissibleBase ζ
  let e := rayProjection (τ a) (v:ℂ)
  have ew : Angular.Weight ζ v 1 e := Angular.Weight.rayProjection hD v v (Angular.permitted_base _ _)
  have orbit (x : ℝ) : CriticalRay.transverseOrbit ‖τ a‖ e x ∈ complexPhaseGroup (b:ℂ) := by
    rw [←hσ]
    exact CriticalRay.transverseOrbit_mem σ τ a (norm_pos_iff.mp hr) _ _
  have ray := Angular.rayInformation_critical_family (B:=(b:ℂ)) (by rw [normb];exact hb)
    ((inv_pos.mpr hb0).trans hl) hl1 hr hr1 (by rw [normb];exact critical) base ew orbit 0
  exact graph_of_anchored_estimate hb hl hl1 (anchoredEstimate_of_rayInformation (P:=Angular.rayFamily ζ v 0) hb0.le
    ⟨Angular.weight_one _ _ _,Angular.weight_one _ _ _⟩ ray) phase I hc hi

/-- Complete graph and natural measure conclusions whenever the same field
element has real images b and r with 0 < |r| < 1 and λ b |r| = 1. Both
signs of the contracting image and all deterministic phases are allowed. -/
theorem graph_and_measure_critical_real {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K)
    {b r l : ℝ} (hσ : σ a = (b:ℂ)) (hτ : τ a = (r:ℂ))
    (hb : 1 < b) (hr : 0 < |r|) (hr1 : |r| < 1) (hl : b⁻¹ < l) (hl1 : l < 1)
    (critical : l*b*|r|=1) (phase : ℕ → ℝ) (I : Set ℝ)
    (hc : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b l phase I) = ENNReal.ofReal (2-alpha b l) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b l phase I) (2-alpha b l)) := by
  have nr : ‖τ a‖=|r| := by simp [hτ]
  exact graph_and_measure_critical_conjugate σ τ a hσ hb (by rwa [nr]) (by rwa [nr]) hl hl1
    (by simpa only [nr] using critical) phase I hc hi

end Weierstrass
