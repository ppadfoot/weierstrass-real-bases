module

public import Weierstrass.CriticalOccupation

/-! # Uniform centered occupation on weighted phase-ray families -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Weierstrass

/-- A weight sequence and its physical ray projection sequence, in that order. -/
abbrev RayParameters := (ℤ → ℝ) × (ℤ → ℝ)

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- Normalized Haar law on the full physical group, independently of the ray. -/
def complexPhaseHaar (B : ℂ) : @Measure (complexPhaseGroup B) (borel _) :=
  Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts (complexPhaseGroup B))

instance complexPhaseHaar_probability (B : ℂ) : IsProbabilityMeasure (complexPhaseHaar B) where
  measure_univ := by simpa [complexPhaseHaar] using
    Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (complexPhaseGroup B)))

instance complexPhaseHaar_invariant (B : ℂ) : Measure.IsAddLeftInvariant (complexPhaseHaar B) := by
  unfold complexPhaseHaar; infer_instance

/-- Lebesgue occupation of the actual weighted bilateral increment in a centered target. -/
def rayOccupation (b g : ℝ) (p : RayParameters) (z : PhaseTorus) (T A r : ℝ) : ℝ≥0∞ :=
  volume {u : ℝ | u ∈ Icc (-T) T ∧ |CriticalRay.circleRay b g p.1 p.2 z u| ≤ A*r}

theorem measurable_rayOccupation (b g : ℝ) (p : RayParameters) (T A r : ℝ) :
    Measurable (fun z => rayOccupation b g p z T A r) := by
  let S : Set (PhaseTorus × ℝ) := {v | v.2 ∈ Icc (-T) T ∧
    |CriticalRay.circleRay b g p.1 p.2 v.1 v.2| ≤ A*r}
  have mS : MeasurableSet S := (measurableSet_Icc.preimage measurable_snd).inter
    (measurableSet_le (continuous_abs.measurable.comp (CriticalRay.measurable_circleRay _ _ _ _)) measurable_const)
  exact measurable_measure_prodMk_left mS

/-- Assertion S_s from §2 for any specified family of weights and physical rays.
Each radius threshold is uniform over the entire family and over all translated cosets. -/
def RayInformation (B : ℂ) (g s : ℝ) (P : Set RayParameters) : Prop :=
  ∀ h : ℝ, 0 < h → h < s → ∀ T A : ℝ, 0 < T → 0 < A →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ω : PhaseTorus, ∀ p ∈ P,
      (complexPhaseHaar B).real {z : complexPhaseGroup B | ENNReal.ofReal (r^h) <
        rayOccupation ‖B‖ g p (ω+z.val) T A r} ≤ ε

/-- The critical-rate result RC2 gives information one simultaneously for every
member having an admissible transverse ray with the same RC1 block constants. -/
theorem rayInformation_critical {B : ℂ} (hb : 1 < ‖B‖) {g ρ η : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hcrit : g*‖B‖*ρ=1)
    (hη : 0 < η) (m₀ : ℕ) {P : Set RayParameters}
    (H : ∀ p ∈ P, (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧ ∃ e : ℤ → ℝ,
      (∀ j, |e j| ≤ 1) ∧ (∀ x, CriticalRay.transverseOrbit ρ e x ∈ complexPhaseGroup B) ∧
      CriticalRay.DriftWeightBounds η m₀ (fun j => p.1 j*p.2 j*e j)) :
    RayInformation B g 1 P := by
  intro h hh hh1 T A hT hA ε hε
  filter_upwards [CriticalRay.critical_occupation hb (complexPhaseHaar B) hg hg1 hρ hρ1 hcrit hη
    m₀ hT hA hh hh1 hε] with r hr
  intro ω p hp
  obtain ⟨hc,hd,e,he,hm,hw⟩ := H p hp
  exact ENNReal.toReal_le_of_le_ofReal hε.le (hr ω p.1 p.2 e hc hd he hm hw)

end Weierstrass
