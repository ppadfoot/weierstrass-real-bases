module

public import Weierstrass.MainTheorem

/-! The statement of Theorem 1.1 with phases in ℝ/ℤ, the explicit circle
character, the physical graph map, and its normalized pushforward. -/
open Set Filter MeasureTheory Weierstrass Weierstrass.CriticalRay
open scoped Topology ENNReal
@[expose] public noncomputable section
namespace Weierstrass

/-- The graph point with the phase supplied directly on the additive circle. -/
def circlePhaseGraphMap (b lam : ℝ) (Φ : ℕ → UnitAddCircle) (x : ℝ) : ℂ :=
  ⟨x,∑' j : ℕ, lam^j * angleCos ((↑(b^j*x) : UnitAddCircle) + Φ j)⟩

/-- Both conclusions of Theorem 1.1 with no choice of real-valued phase
representatives in the statement. `angleCos θ` is the real part of the
standard circle character, hence the physical cosine on each representative. -/
theorem graph_and_measure_circle_phases (b lam : ℝ) (hb : 1<b) (hlam₀ : 1/b<lam) (hlam₁ : lam<1)
    (Φ : ℕ → UnitAddCircle) (I : Set ℝ) (interval : I.OrdConnected) (length : (interior I).Nonempty) :
    dimH (circlePhaseGraphMap b lam Φ '' I) = ENNReal.ofReal (2+Real.log lam/Real.log b) ∧
    ∀ _ : Bornology.IsBounded I, let μ := ((volume I)⁻¹ • volume.restrict I).map (circlePhaseGraphMap b lam Φ)
    ∀ᵐ z ∂μ, Tendsto (fun r : ℝ => Real.log (μ (Metric.ball z r)).toReal/Real.log r)
      (𝓝[>] 0) (𝓝 (2+Real.log lam/Real.log b)) := by
  let φ (j : ℕ) : ℝ := AddCircle.equivIco (1:ℝ) 0 (Φ j)
  have rep (j : ℕ) : (↑(φ j) : UnitAddCircle) = Φ j := AddCircle.coe_equivIco
  have eq : circlePhaseGraphMap b lam Φ = graphMap b lam φ := by
    funext x
    apply Complex.ext
    · rfl
    change (∑' j,_) = ∑' j, term b lam φ j x
    apply tsum_congr;intro j
    rw [←rep j,←AddCircle.coe_add,angleCos_coe];rfl
  rw [eq]
  exact graph_and_measure_real_base hb (by simpa only [one_div] using hlam₀) hlam₁ φ I interval length

end Weierstrass
