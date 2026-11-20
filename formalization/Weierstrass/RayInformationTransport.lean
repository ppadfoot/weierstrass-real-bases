module

public import Weierstrass.RayInformation

/-! Haar transport under integral reindexing of the bilateral angles. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Weierstrass

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩
local instance (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _
local instance (b : ℝ) : BorelSpace (phaseGroup b) := ⟨rfl⟩

/-- The shift of a two-sided forcing sequence, with the new origin at n. -/
def shiftPhase (n : ℤ) : PhaseTorus →+ PhaseTorus where
  toFun z j := z (j+n)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem shiftPhase_continuous (n : ℤ) : Continuous (shiftPhase n) :=
  continuous_pi (fun j ↦ continuous_apply (j+n))

theorem shiftPhase_group {B : ℂ} (hB : B ≠ 0) (n : ℤ) :
    (complexPhaseGroup B).map (shiftPhase n) = complexPhaseGroup B := by
  have incl (k : ℤ) : complexPhaseGroup B ≤ (complexPhaseGroup B).comap (shiftPhase k) := by
    refine AddSubgroup.topologicalClosure_minimal _ ?_
      ((complexPhaseOrbit B).range.isClosed_topologicalClosure.preimage (shiftPhase_continuous k))
    rintro _ ⟨x,rfl⟩
    apply (complexPhaseOrbit B).range.le_topologicalClosure
    refine ⟨B^k*x,?_⟩
    funext j
    change (↑((B^j*(B^k*x)).re) : AddCircle (1:ℝ)) = ↑((B^(j+k)*x).re)
    rw [zpow_add₀ hB, mul_assoc]
  apply le_antisymm ((AddSubgroup.map_le_iff_le_comap).mpr (incl n))
  intro z hz
  refine ⟨shiftPhase (-n) z,incl (-n) hz,?_⟩
  funext j; simp [shiftPhase]

/-- Restrict a torus homomorphism to two physical phase groups when its image is known. -/
def inducedPhaseMap (B C : ℂ) (f : PhaseTorus →+ PhaseTorus)
    (e : (complexPhaseGroup B).map f = complexPhaseGroup C) :
    complexPhaseGroup B →+ complexPhaseGroup C where
  toFun z := ⟨f z.val,e ▸ AddSubgroup.mem_map_of_mem f z.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' x y := Subtype.ext (f.map_add x.val y.val)

theorem inducedPhaseMap_preserving (B C : ℂ) (f : PhaseTorus →+ PhaseTorus) (hf : Continuous f)
    (e : (complexPhaseGroup B).map f = complexPhaseGroup C) :
    MeasurePreserving (inducedPhaseMap B C f e) (complexPhaseHaar B) (complexPhaseHaar C) := by
  have onto : Function.Surjective (inducedPhaseMap B C f e) := by
    intro z
    obtain ⟨x,hx,eq⟩ := (show z.val ∈ (complexPhaseGroup B).map f from e.symm ▸ z.property)
    exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  let (D : ℂ) : Measure.IsAddHaarMeasure (complexPhaseHaar D) := by unfold complexPhaseHaar; infer_instance
  exact AddMonoidHom.measurePreserving (f := inducedPhaseMap B C f e)
    ((hf.comp continuous_subtype_val).subtype_mk _) onto (by simp)

theorem shiftPhase_preserving {B : ℂ} (hb : B ≠ 0) (n : ℤ) :
    MeasurePreserving (inducedPhaseMap B B (shiftPhase n) (shiftPhase_group hb n))
      (complexPhaseHaar B) (complexPhaseHaar B) :=
  inducedPhaseMap_preserving _ _ _ (shiftPhase_continuous n) _

theorem reversePhase_conjugate_preserving {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K) :
    MeasurePreserving (inducedPhaseMap (σ a) (τ a)⁻¹ reversePhase (reversePhase_group_conjugate σ τ a))
      (complexPhaseHaar (σ a)) (complexPhaseHaar (τ a)⁻¹) :=
  inducedPhaseMap_preserving _ _ _ (continuous_pi (fun i : ℤ ↦ continuous_apply (-i))) _

private def normalizedPhaseEvent (G : AddSubgroup PhaseTorus) [CompactSpace G] (S : Set PhaseTorus) : ℝ≥0∞ := by
  letI : MeasurableSpace G := borel _
  letI : BorelSpace G := ⟨rfl⟩
  exact (Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) {z : G | z.val ∈ S}

private theorem real_complex_transport (b : ℝ) (S : Set PhaseTorus) :
    phaseHaar b {z : phaseGroup b | z.val ∈ S} =
      complexPhaseHaar (b:ℂ) {z : complexPhaseGroup (b:ℂ) | z.val ∈ S} := by
  have move {G H : AddSubgroup PhaseTorus} [CompactSpace G] [CompactSpace H] (eq : G=H) :
      normalizedPhaseEvent G S = normalizedPhaseEvent H S := by subst H; rfl
  exact move (complexPhaseGroup_ofReal b).symm

/-- The unweighted real conclusion used by the physical graph comparison. -/
theorem anchoredEstimate_of_rayInformation {b g s : ℝ} (hb : 0 ≤ b) {P : Set RayParameters}
    (hp : ((fun _ ↦ 1),fun _ ↦ 1) ∈ P) (h : RayInformation (b:ℂ) g s P) : AnchoredEstimate b g s := by
  intro k hk hks T A hT hA
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  obtain ⟨u,hu,huδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  have hup : 0 < (u:ℝ) := by exact_mod_cast (show (0:ℝ≥0) < u by exact_mod_cast hu)
  filter_upwards [h k hk hks T A hT hA u hup] with r hr
  apply iSup_le
  intro ω
  let S := {z : PhaseTorus | ENNReal.ofReal (r^k) <
      volume {t : ℝ | t ∈ Icc (-T) T ∧ |circleIncrement b g (ω+z) t| ≤ A*r}}
  change phaseHaar b {z : phaseGroup b | z.val ∈ S} ≤ δ
  rw [real_complex_transport]
  refine le_trans ?_ huδ.le
  have hu' := hr ω _ hp
  simp only [rayOccupation, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb, CriticalRay.circleRay_ones] at hu'
  simpa only [S,Set.mem_ofPred_eq,ENNReal.ofReal_coe_nnreal] using (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) u.coe_nonneg).mpr hu'

end Weierstrass
