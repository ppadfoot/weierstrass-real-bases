module

public import Weierstrass.StripCenters
public import Weierstrass.RayInformationTransport
public import Weierstrass.StripRetention

/-! # Haar bounds for the actual shifted physical and reversed stable input tests -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Weierstrass.StripProof
open CriticalRay

local instance haarTestPhaseMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance haarTestPhaseBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- Fubini with a measure-preserving phase map and an arbitrary offset depending on the
sampled input. The uniformity over translated cosets controls the whole discarded mass. -/
theorem joint_occupation_test {B C : ℂ} (κ : Measure ℝ) [IsProbabilityMeasure κ]
    {f : complexPhaseGroup B → complexPhaseGroup C}
    (mf : MeasurePreserving f (complexPhaseHaar B) (complexPhaseHaar C))
    {w : ℝ → PhaseTorus} (mw : Measurable w)
    (g : ℝ) (p : RayParameters) (T A r h : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (bound : ∀ ξ : PhaseTorus, (complexPhaseHaar C).real
      {z : complexPhaseGroup C | ENNReal.ofReal (r^h) < rayOccupation ‖C‖ g p (ξ+z.val) T A r} ≤ ε) :
    ((complexPhaseHaar B).prod κ).real
      {v : complexPhaseGroup B × ℝ | ENNReal.ofReal (r^h) <
        rayOccupation ‖C‖ g p (w v.2+(f v.1).val) T A r} ≤ ε := by
  let E := {v : complexPhaseGroup B × ℝ | ENNReal.ofReal (r^h) <
    rayOccupation ‖C‖ g p (w v.2+(f v.1).val) T A r}
  have mE : MeasurableSet E := measurableSet_lt measurable_const ((measurable_rayOccupation _ _ _ _ _ _).comp
    ((mw.comp measurable_snd).add (continuous_subtype_val.measurable.comp (mf.measurable.comp measurable_fst))))
  apply ENNReal.toReal_le_of_le_ofReal hε
  change ((complexPhaseHaar B).prod κ) E ≤ _
  rw [Measure.prod_apply_symm mE]
  apply (lintegral_mono (g := fun _ => ENNReal.ofReal ε) _).trans_eq (by simp)
  intro x
  let S := {z : complexPhaseGroup C | ENNReal.ofReal (r^h) < rayOccupation ‖C‖ g p (w x+z.val) T A r}
  have mS : MeasurableSet S := measurableSet_lt measurable_const ((measurable_rayOccupation _ _ _ _ _ _).comp
    (measurable_const.add continuous_subtype_val.measurable))
  change (complexPhaseHaar B) (f ⁻¹' S) ≤ _
  rw [mf.measure_preimage mS.nullMeasurableSet,← ofReal_measureReal (measure_ne_top _ S)]
  exact ENNReal.ofReal_le_ofReal (bound (w x))

theorem measurable_physicalEnvironment (b : ℝ) (d : ℤ → ℝ) (n : ℤ) :
    Measurable (fun v : PhaseTorus × ℝ => physicalEnvironment b d v.1 n v.2) := by
  apply measurable_pi_lambda
  intro j
  apply Continuous.measurable
  exact ((continuous_apply (j+n)).comp continuous_fst).add
    (continuous_quotient_mk'.comp (continuous_const.mul continuous_snd))

theorem measurable_reversedEnvironment (m : ℕ) : Measurable (fun z => reversedEnvironment z m) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply (-(j+m))).add measurable_const

/-- Physical information controls the joint Haar/input mass of the test defining B4. -/
theorem physical_haar_test {B : ℂ} (hB : B ≠ 0) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    {g s h : ℝ} {P : Set RayParameters} (H : RayInformation B g s P) (hh : 0 < h) (hs : h < s)
    {T A ε : ℝ} (hT : 0 < T) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (ω : PhaseTorus) (p : RayParameters) (n : ℤ),
      shiftedParameters p n ∈ P → ((complexPhaseHaar B).prod κ).real
      {v : complexPhaseGroup B × ℝ | ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g
        (shiftedParameters p n) (physicalEnvironment ‖B‖ p.2 (ω+v.1.val) n v.2) T A r} ≤ ε := by
  filter_upwards [H h hh hs T A hT hA ε hε] with r hr
  intro ω p n hp
  let w := physicalEnvironment ‖B‖ p.2 ω n
  have mw : Measurable w := (measurable_physicalEnvironment _ _ _).comp (measurable_const.prodMk measurable_id)
  have eq (v : complexPhaseGroup B × ℝ) :
      physicalEnvironment ‖B‖ p.2 (ω+v.1.val) n v.2 =
      w v.2+(inducedPhaseMap B B (shiftPhase n) (shiftPhase_group hB n) v.1).val := by
    funext j
    change (ω (j+n)+v.1.val (j+n))+_ = (ω (j+n)+_)+v.1.val (j+n)
    abel
  simp_rw [eq]
  exact joint_occupation_test κ (shiftPhase_preserving hB n) mw g _ T A r h hε.le (fun ξ => hr ξ _ hp)

/-- The reversed information controls the stable B3 test in its actual translated and
reindexed phase. The same assertion holds for every original coset, stable scale and ray. -/
theorem stable_haar_test {K : Type*} [Field K] (σ τ' : K →+* ℂ) (a : K) (ha : τ' a ≠ 0)
    {g s h : ℝ} {P : Set RayParameters} (H : RayInformation (τ' a)⁻¹ g s P) (hh : 0 < h) (hs : h < s)
    {T A ε : ℝ} (hT : 0 < T) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (ω : PhaseTorus) (c d e : ℤ → ℝ) (m : ℕ),
      reversedParameters c d e m ∈ P → ((complexPhaseHaar (σ a)).prod stableLaw).real
      {v : complexPhaseGroup (σ a) × ℝ | ENNReal.ofReal (r^h) < rayOccupation ‖(τ' a)⁻¹‖ g
        (reversedParameters c d e m) (reversedEnvironment
          ((ω+v.1.val)+transverseOrbit ‖τ' a‖ e (‖τ' a‖^m*v.2)) m) T A r} ≤ ε := by
  filter_upwards [H h hh hs T A hT hA ε hε] with r hr
  intro ω c d e m hp
  let C := (τ' a)⁻¹
  have hC : C ≠ 0 := inv_ne_zero ha
  let rev := inducedPhaseMap (σ a) C reversePhase (reversePhase_group_conjugate σ τ' a)
  let sh := inducedPhaseMap C C (shiftPhase m) (shiftPhase_group hC m)
  have mf : MeasurePreserving (sh ∘ rev) (complexPhaseHaar (σ a)) (complexPhaseHaar C) :=
    (shiftPhase_preserving hC m).comp (reversePhase_conjugate_preserving σ τ' a)
  let w := fun u => reversedEnvironment (ω+transverseOrbit ‖τ' a‖ e (‖τ' a‖^m*u)) m
  have mw : Measurable w := (measurable_reversedEnvironment m).comp (measurable_const.add
    ((measurable_transverseOrbit _ _).comp (measurable_const.mul measurable_id)))
  have eq (v : complexPhaseGroup (σ a) × ℝ) :
      reversedEnvironment ((ω+v.1.val)+transverseOrbit ‖τ' a‖ e (‖τ' a‖^m*v.2)) m =
      w v.2 + ((sh ∘ rev) v.1).val := by
    funext j
    change ((ω (-(j+m))+v.1.val (-(j+m)))+_)+_ = ((ω (-(j+m))+_)+_)+v.1.val (-(j+m))
    abel
  simp_rw [eq]
  exact joint_occupation_test stableLaw mf mw g _ T A r h hε.le (fun ξ => hr ξ _ hp)

end Weierstrass.StripProof
