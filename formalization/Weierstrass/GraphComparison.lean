module

public import Weierstrass.GraphEndpoint
public import Weierstrass.TranscendentalEstimate

/-! The conclusion of Theorem 1.1 from the anchored estimate, and its
unconditional verification for every transcendental real base. -/
public noncomputable section
open Set MeasureTheory
namespace Weierstrass

/-- The endpoint s=1 of the physical graph comparison of Appendix A. -/
theorem graph_of_anchored_estimate {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (anchor : AnchoredEstimate b l 1) (phase : ℕ → ℝ)
    (I : Set ℝ) (hc : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b l phase I) = ENNReal.ofReal (2-alpha b l) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b l phase I) (2-alpha b l)) := by
  apply fixedParameters_of_exact_unit hb hl hl' _ phase I hc hi
  intro ψ
  let φ (j : ℤ) := ψ j.toNat
  obtain ⟨T,C,G⟩ := GraphInformation.square_mass_window_bound hb hl hl' φ
  simpa only [φ,Int.toNat_natCast] using exactDimension_of_window hb hl hl' anchor φ T C G

/-- The entire graph and graph-measure theorem at transcendental real bases,
including every prescribed phase sequence and intervals with arbitrary endpoints. -/
theorem graph_and_measure_transcendental {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l)
    (hl' : l < 1) (ht : Transcendental ℤ b) (phase : ℕ → ℝ)
    (I : Set ℝ) (hc : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b l phase I) = ENNReal.ofReal (2-alpha b l) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b l phase I) (2-alpha b l)) :=
  graph_of_anchored_estimate hb hl hl' (anchoredEstimate_transcendental hb hl hl' ht) phase I hc hi

end Weierstrass
