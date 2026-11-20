module

public import Weierstrass.HalfFamily
public import Weierstrass.StripDual

/-! The Haar and angular inputs to the reciprocal occupation tests. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace Weierstrass.Reciprocal
open CriticalRay StripProof Angular

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def phaseReindex (m : ℕ) : PhaseTorus →+ PhaseTorus := (shiftPhase m).comp reversePhase

private theorem reindex_group {B D : ℂ} (hD : D ≠ 0)
    (rev : (complexPhaseGroup B).map reversePhase = complexPhaseGroup D) (m : ℕ) :
    (complexPhaseGroup B).map (phaseReindex m) = complexPhaseGroup D := by
  rw [phaseReindex,← AddSubgroup.map_map,rev,shiftPhase_group hD]

theorem reversedEnvironment_add (ω z : PhaseTorus) (m : ℕ) :
    reversedEnvironment (ω+z) m = reversedEnvironment ω m + phaseReindex m z := by
  funext j
  change (ω (-(j+m))+z (-(j+m)))+↑(1/4:ℝ) = (ω (-(j+m))+↑(1/4:ℝ))+z (-(j+m))
  abel

theorem reversed_event_mass {B D : ℂ} (hD : D ≠ 0)
    (rev : (complexPhaseGroup B).map reversePhase = complexPhaseGroup D)
    (ω : PhaseTorus) (m : ℕ) {E : Set PhaseTorus} (mE : MeasurableSet E) :
    complexPhaseHaar B {z : complexPhaseGroup B | reversedEnvironment (ω+z.val) m ∈ E} =
      complexPhaseHaar D {z : complexPhaseGroup D | reversedEnvironment ω m + z.val ∈ E} := by
  let f := inducedPhaseMap B D (phaseReindex m) (reindex_group hD rev m)
  have pf : MeasurePreserving f (complexPhaseHaar B) (complexPhaseHaar D) :=
    inducedPhaseMap_preserving B D (phaseReindex m) (continuous_pi (fun j : ℤ ↦ continuous_apply (-(j+m):ℤ))) _
  let S := {z : complexPhaseGroup D | reversedEnvironment ω m + z.val ∈ E}
  have mS : MeasurableSet S := (continuous_const.add continuous_subtype_val).measurable mE
  rw [show {z : complexPhaseGroup B | reversedEnvironment (ω+z.val) m ∈ E} = f ⁻¹' S from
    Set.ext (fun z ↦ by change _ ∈ E ↔ _ ∈ E; rw [reversedEnvironment_add]; rfl)]
  exact pf.measure_preimage mS.nullMeasurableSet

/-- Reversal and scale m carry an admissible transverse orbit to a physically
admissible ray of the dual system, including signed angular weights. -/
theorem reversedParameters_mem {B D : ℂ} (hD : D ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (normD : ‖D‖=ρ⁻¹)
    (rev : (complexPhaseGroup B).map reversePhase = complexPhaseGroup D)
    {ζ v₀ : Circle} {k : ℕ} {p : RayParameters} (hp : p ∈ physicalFamily B ζ v₀ k)
    {e : ℤ → ℝ} (he : Weight ζ v₀ 1 e) (hmem : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) (m : ℕ) :
    reversedParameters p.1 p.2 e m ∈ physicalFamily D ζ v₀ (k+1) := by
  obtain ⟨⟨hc,hd⟩,_⟩ := hp
  refine ⟨⟨((hc.mul hd).reverse.shift (m:ℤ)),he.reverse.shift (m:ℤ)⟩,?_⟩
  intro t
  have eq : transverseOrbit ‖D‖ (reversedParameters p.1 p.2 e m).2 t =
      phaseReindex m (transverseOrbit ρ e (ρ^m*t)) := by
    funext j
    change (↑(‖D‖^j*e (-(j+m))*t) : UnitAddCircle) = ↑(ρ^(-(j+m))*e (-(j+m))*(ρ^m*t))
    rw [normD,inv_zpow,zpow_neg,zpow_add₀ hρ.ne',zpow_natCast]
    congr 1; field_simp
  rw [eq,← reindex_group hD rev m]
  exact AddSubgroup.mem_map_of_mem _ (hmem _)

set_option maxHeartbeats 750000 in
/-- Uniformly discard all failing tests at a fixed finite list of reciprocal
stages. The retained set is chosen before either the physical or stable secant. -/
theorem retained_dual_tests {B D : ℂ} (hD : D ≠ 0) (rev : (complexPhaseGroup B).map reversePhase = complexPhaseGroup D)
    {g s σ K ε : ℝ} (hg : 0 < g) (hg1 : g < 1) (hσ : 0 < σ) (hσs : σ < s) (hK : 0 < K) (hε : 0 < ε)
    {P : Set RayParameters} (info : RayInformation D g s P) (I : Type*) [Fintype I] :
    ∃ N : ℕ, ∀ (ω : PhaseTorus) (p : I → RayParameters) (m d : I → ℕ), (∀ i, p i ∈ P) → (∀ i, N ≤ d i) →
      ∃ G : Set (complexPhaseGroup B), MeasurableSet G ∧ complexPhaseHaar B Gᶜ ≤ ENNReal.ofReal ε ∧
      ∀ z ∈ G, ∀ i, rayOccupation ‖D‖ g (p i) (reversedEnvironment (ω+z.val) (m i)) 2 K (g^(d i)) ≤
        ENNReal.ofReal ((g^(d i))^σ) := by
  let η := ε/(Fintype.card I+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have conv : Tendsto (fun k : ℕ ↦ g^k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hg1)
      (Eventually.of_forall fun n ↦ pow_pos hg n)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (conv.eventually (info σ hσ hσs 2 K (by norm_num) hK η hη))
  refine ⟨N,?_⟩
  intro ω p m d hp hd
  let E (i : I) := {z : PhaseTorus | ENNReal.ofReal ((g^(d i))^σ) < rayOccupation ‖D‖ g (p i) z 2 K (g^(d i))}
  have mE (i : I) : MeasurableSet (E i) := measurableSet_lt measurable_const (measurable_rayOccupation _ _ _ _ _ _)
  let X (i : I) := {z : complexPhaseGroup B | reversedEnvironment (ω+z.val) (m i) ∈ E i}
  have mx (i : I) : MeasurableSet (X i) := by
    apply (mE i).preimage
    apply Continuous.measurable
    apply continuous_pi
    intro j
    exact (((continuous_apply (-(j+m i):ℤ)).comp (continuous_const.add continuous_subtype_val)).add continuous_const)
  have small (i : I) : complexPhaseHaar B (X i) ≤ ENNReal.ofReal η := by
    have h := hN (d i) (hd i) (reversedEnvironment ω (m i)) (p i) (hp i)
    rw [show X i = {z : complexPhaseGroup B | reversedEnvironment (ω+z.val) (m i) ∈ E i} from rfl,
      reversed_event_mass hD rev ω (m i) (mE i)]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hη.le).mpr h
  refine ⟨(⋃ i, X i)ᶜ,(MeasurableSet.iUnion mx).compl,?_,?_⟩
  · rw [compl_compl]
    refine (measure_iUnion_fintype_le _ _).trans ((Finset.sum_le_sum (fun i _ ↦ small i)).trans ?_)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast (Fintype.card I),← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [η]; rw [← mul_div_assoc,div_le_iff₀ (by positivity)]; nlinarith
  · intro z hz i
    exact le_of_not_gt (fun h ↦ hz (mem_iUnion.mpr ⟨i,h⟩))

end Weierstrass.Reciprocal
