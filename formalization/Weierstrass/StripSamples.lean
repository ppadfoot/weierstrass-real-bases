module

public import Weierstrass.StripHaarTests
public import Weierstrass.StripGeometry

/-! # Simultaneous measurable retention in the joint environment and input law -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Weierstrass.StripProof
open CriticalRay

local instance samplePhaseMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance samplePhaseBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def physicalFailure {B : ℂ} (g : ℝ) (ω : PhaseTorus) (p : RayParameters) (n : ℕ) (T A r s : ℝ) :
    Set (complexPhaseGroup B × ℝ) := {v | ENNReal.ofReal (r^s) < rayOccupation ‖B‖ g
    (shiftedParameters p n) (physicalEnvironment ‖B‖ p.2 (ω+v.1.val) n v.2) T A r}

theorem measurable_physicalFailure {B : ℂ} (g : ℝ) (ω : PhaseTorus) (p : RayParameters) (n : ℕ) (T A r s : ℝ) :
    MeasurableSet (physicalFailure (B:=B) g ω p n T A r s) :=
  measurableSet_lt measurable_const ((measurable_rayOccupation _ _ _ _ _ _).comp
    ((measurable_physicalEnvironment _ _ _).comp ((measurable_const.add (continuous_subtype_val.measurable.comp
      measurable_fst)).prodMk measurable_snd)))

def stableFailure {B : ℂ} (g ρ : ℝ) (ω : PhaseTorus) (p : RayParameters) (e : ℤ → ℝ) (m : ℕ)
    (T A r t : ℝ) : Set (complexPhaseGroup B × ℝ) :=
  {v | ENNReal.ofReal (r^t) < rayOccupation ρ⁻¹ g (reversedParameters p.1 p.2 e m)
    (reversedEnvironment ((ω+v.1.val)+transverseOrbit ρ e (ρ^m*v.2)) m) T A r}

theorem measurable_stableFailure {B : ℂ} (g ρ : ℝ) (ω : PhaseTorus) (p : RayParameters) (e : ℤ → ℝ)
    (m : ℕ) (T A r t : ℝ) : MeasurableSet (stableFailure (B:=B) g ρ ω p e m T A r t) :=
  measurableSet_lt measurable_const ((measurable_rayOccupation _ _ _ _ _ _).comp
    ((measurable_reversedEnvironment m).comp ((measurable_const.add (continuous_subtype_val.measurable.comp measurable_fst)).add
      ((measurable_transverseOrbit _ _).comp (measurable_const.mul measurable_snd)))))

def retainedSamples {X ι : Type*} (S : Set ℝ) (I : Finset ι) (F : ι → Set (X × ℝ)) : Set (X × ℝ) :=
  (univ ×ˢ S) ∩ retain I F

theorem retainedSamples_meas {X ι : Type*} [MeasurableSpace X] {S : Set ℝ} (mS : MeasurableSet S)
    (I : Finset ι) {F : ι → Set (X × ℝ)} (mF : ∀ j ∈ I, MeasurableSet (F j)) :
    MeasurableSet (retainedSamples S I F) := (MeasurableSet.univ.prod mS).inter (measurable_retain I mF)

theorem retainedSamples_good {X ι : Type*} {S : Set ℝ} {I : Finset ι} {F : ι → Set (X × ℝ)}
    {z : X × ℝ} (hz : z ∈ retainedSamples S I F) : z.2 ∈ S ∧ ∀ j ∈ I, z ∉ F j :=
  ⟨hz.1.2,fun j hj h => hz.2 (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,h⟩⟩)⟩

theorem deletedSamples_mass {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Measure ℝ) [IsProbabilityMeasure κ] {S : Set ℝ} (_mS : MeasurableSet S) (supp : ∀ᵐ x ∂κ, x ∈ S)
    (I : Finset ι) {F : ι → Set (X × ℝ)} {ε : ℝ}
    (bound : ∀ j ∈ I, (μ.prod κ).real (F j) ≤ ε) :
    (μ.prod κ).real (retainedSamples S I F)ᶜ ≤ I.card*ε := by
  let ν := μ.prod κ
  have eq : (retainedSamples S I F)ᶜ =ᵐ[ν] ⋃ j ∈ I, F j := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ)).ae supp] with v hv
    apply propext
    change (¬((v.1 ∈ (univ:Set X) ∧ v.2 ∈ S) ∧ v ∉ ⋃ j ∈ I, F j)) ↔ v ∈ ⋃ j ∈ I, F j
    simp [hv]
  have m := measure_congr eq
  change (ν (retainedSamples S I F)ᶜ).toReal ≤ _
  apply (congrArg ENNReal.toReal m).le.trans
  apply (measureReal_biUnion_finset_le (μ := ν) I F).trans
  simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum bound

end Weierstrass.StripProof
