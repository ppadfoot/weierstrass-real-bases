module

public import Weierstrass.HeavyPairs
public import Weierstrass.RayModulus
public import Weierstrass.StripDual

/-! Recovering anchored occupation from the sampled graph, on every fixed
input interval and with unnormalized Lebesgue time. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex Weierstrass.CriticalRay
open scoped BigOperators Topology ENNReal
namespace Weierstrass.RaySeed

/-- A family of events of common mass cannot have all its pair intersections
small if that common mass stays positive as the family grows. -/
theorem packing_events {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (E : ι → Set X) (hm : ∀ i, MeasurableSet (E i)) {p v : ℝ} (hv : 0 ≤ v)
    (equal : ∀ i, μ.real (E i) = p)
    (pairs : ∀ i j, i ≠ j → μ.real (E i ∩ E j) ≤ v) (s : Finset ι) :
    (s.card:ℝ)*p ≤ 1+(s.card:ℝ)^2*v := by
  classical
  let U (s : Finset ι) := ⋃ i ∈ s, E i
  have fin (s : Finset ι) : (s.card:ℝ)*p ≤ μ.real (U s)+(s.card:ℝ)^2*v := by
    induction s using Finset.induction_on with
    | empty => simp [U]
    | @insert i s ni ih =>
      have eq : U (insert i s) = E i ∪ U s := by simp [U]
      have inc : E i ∩ U s ⊆ ⋃ j ∈ s, E i ∩ E j := by
        rintro x ⟨hi,hj⟩
        obtain ⟨j,hj⟩ := mem_iUnion.mp hj
        obtain ⟨inS,hj⟩ := mem_iUnion.mp hj
        exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨inS,hi,hj⟩⟩
      have cost : μ.real (E i ∩ U s) ≤ s.card*v := by
        apply (measureReal_mono inc (measure_ne_top μ _)).trans
        apply (measureReal_biUnion_finset_le s _).trans
        simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum
          (fun j (hj : j ∈ s) ↦ pairs i j (fun h ↦ ni (h ▸ hj)))
      have combo := measureReal_union_add_inter' (μ:=μ) (t:=U s) (hm i) (measure_ne_top μ _) (measure_ne_top μ _)
      rw [equal i] at combo
      rw [Finset.card_insert_of_notMem ni,Nat.cast_succ,eq]
      nlinarith only [ih,cost,combo,mul_nonneg (Nat.cast_nonneg s.card) hv,hv]
  exact (fin s).trans (add_le_add (by simp : μ.real (U s) ≤ 1) le_rfl)

def sampleInterval (T : ℝ) : Set ℝ := Icc (-T) (1+T)
def sampledLaw (F : ℝ → ℝ) (T : ℝ) : Measure ℝ := (volume.restrict (sampleInterval T)).map F

instance sample_finite (F : ℝ → ℝ) (T : ℝ) : IsFiniteMeasure (sampledLaw F T) := by
  unfold sampledLaw sampleInterval
  infer_instance

theorem sampled_mass (F : ℝ → ℝ) (mF : Measurable F) {T : ℝ} (hT : 0 < T) :
    (sampledLaw F T).real univ = 1+2*T := by
  simp only [sampledLaw,measureReal_def,Measure.map_apply mF MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ,sampleInterval,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ 1+T- -T)]
  ring

set_option maxHeartbeats 1500000 in
/-- Translate the anchored time section by the actual sampled input x. -/
theorem reanchor_dominates {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (z : PhaseTorus) (T A r x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    rayOccupation b g (c,d) (z+transverseOrbit b d x) T A r ≤
      (sampledLaw (circleRay b g c d z) T) (Icc (circleRay b g c d z x-A*r) (circleRay b g c d z x+A*r)) := by
  let F := circleRay b g c d z
  let V := Icc (F x-A*r) (F x+A*r)
  have mF : Measurable F := (measurable_circleRay b g c d).comp
    ((measurable_const (a:=z)).prodMk measurable_id)
  have recenter (u : ℝ) : F (x+u)-F x = circleRay b g c d (z+transverseOrbit b d x) u := by
    change F (x+u)-F x = circleRay b g c d (fun j ↦ z j+↑(b^j*d j*x)) u
    simpa only [neg_zero,zpow_zero,one_mul,Int.add_zero,F] using
      StripProof.circleRay_recenter_scale hb hg hg1 hbg hc hd z 0 x u
  change _ ≤ (sampledLaw F T) V
  rw [sampledLaw,Measure.map_apply mF measurableSet_Icc,Measure.restrict_apply (mF measurableSet_Icc)]
  change volume _ ≤ volume (F ⁻¹' V ∩ sampleInterval T)
  rw [←measure_preimage_add volume x (F ⁻¹' V ∩ sampleInterval T)]
  apply measure_mono
  intro u hu
  change u ∈ Icc (-T) T ∧ |circleRay b g c d (z+transverseOrbit b d x) u| ≤ A*r at hu
  have atRange := abs_le.mp ((recenter u).symm ▸ hu.2 : |F (x+u)-F x| ≤ A*r)
  exact ⟨⟨by linarith only [atRange.1],by linarith only [atRange.2]⟩,
    ⟨by linarith only [hu.1.1,hx.1],by linarith only [hu.1.2,hx.2]⟩⟩

end Weierstrass.RaySeed
