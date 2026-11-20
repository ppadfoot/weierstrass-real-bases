module

public import Weierstrass.DescentDifferentiation

/-! The uniform off-diagonal estimate from §6 on the physical Haar group. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped Topology ENNReal
namespace Weierstrass.Descent

local instance sublevelGroupMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance sublevelGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem derivative_measurable (b g ρ : ℝ) (c d e : ℤ → ℝ) :
    Measurable (fun v : PhaseTorus × ℝ ↦ derivRay b g ρ c d e v.1 v.2) := by
  have mq : Continuous quarter := continuous_pi (fun j ↦ (continuous_apply j).add continuous_const)
  exact ((measurable_circleRay _ _ _ _).comp ((mq.measurable.comp measurable_fst).prodMk measurable_snd)).const_mul _

set_option maxHeartbeats 1600000 in
/-- For each fixed pair of physical inputs, the Haar probability of ordinates
within r and separated derivatives is O(r). All translations, projections,
weights and input pairs share the same constant. -/
theorem haar_distant_pair {B : ℂ} (hb : 0 < ‖B‖) {g ρ T κ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hbgρ : 1 < ‖B‖*(g*ρ)) (hT : 0 ≤ T) (hk : 0 < κ)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) → (∀ j, |d j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → (∀ v, transverseOrbit ρ e v ∈ complexPhaseGroup B) →
      ∀ (ω : PhaseTorus) {x y r : ℝ}, |x| ≤ T → |y| ≤ T → 0 ≤ r →
        μ {z | |circleRay ‖B‖ g c d (ω+z.val) x-circleRay ‖B‖ g c d (ω+z.val) y| ≤ r ∧
          κ < |derivRay ‖B‖ g ρ c d e (ω+z.val) x-derivRay ‖B‖ g ρ c d e (ω+z.val) y|} ≤
          ENNReal.ofReal (C*r) := by
  obtain ⟨δ,hδ,osc⟩ := derivative_uniform_modulus hb hg hg1 hρ hρ1 hbgρ hT
    (show 0 < κ/4 by positivity)
  obtain ⟨N,hn⟩ := exists_nat_ge (1/δ)
  have cover := (div_le_iff₀ hδ).mp hn
  refine ⟨4*N/κ,by positivity,?_⟩
  intro c d e hc hd he hm ω x y r hx hy hr
  let f (z : PhaseTorus) := circleRay ‖B‖ g c d z x-circleRay ‖B‖ g c d z y
  let p (z : PhaseTorus) := derivRay ‖B‖ g ρ c d e z x-derivRay ‖B‖ g ρ c d e z y
  have mR (t : ℝ) : Measurable (fun z : PhaseTorus ↦ circleRay ‖B‖ g c d z t) := by
    change Measurable ((fun v : PhaseTorus × ℝ ↦ circleRay ‖B‖ g c d v.1 v.2) ∘ (fun z : PhaseTorus ↦ (z,t)))
    exact (measurable_circleRay ‖B‖ g c d).comp (measurable_id.prodMk (measurable_const (a:=t)))
  have mD (t : ℝ) : Measurable (fun z : PhaseTorus ↦ derivRay ‖B‖ g ρ c d e z t) := by
    change Measurable ((fun v : PhaseTorus × ℝ ↦ derivRay ‖B‖ g ρ c d e v.1 v.2) ∘ (fun z : PhaseTorus ↦ (z,t)))
    exact (derivative_measurable ‖B‖ g ρ c d e).comp (measurable_id.prodMk (measurable_const (a:=t)))
  have mf : Measurable f := (mR x).sub (mR y)
  have mp : Measurable p := (mD x).sub (mD y)
  have mshift : Measurable (fun z : complexPhaseGroup B ↦ ω+z.val) := measurable_const.add continuous_subtype_val.measurable
  have E : MeasurableSet {z : complexPhaseGroup B | |f (ω+z.val)| ≤ r ∧ κ < |p (ω+z.val)|} :=
    (measurableSet_le (mf.abs.comp mshift) measurable_const).inter (measurableSet_lt measurable_const (mp.abs.comp mshift))
  refine haar_le_of_transverse_slices μ hm _ E (ENNReal.ofReal ((4*N/κ)*r)) ?_
  intro z
  let Z (u : ℝ) := (ω+z.val)+transverseOrbit ρ e u
  have diff t : HasDerivAt (fun u ↦ f (Z u)) (p (Z t)) t :=
    (deriv_circleRay hb hg hg1 hρ hρ1 hbgρ hc hd he _ x t).sub
    (deriv_circleRay hb hg hg1 hρ hρ1 hbgρ hc hd he _ y t)
  have mod t u (htu : |t-u| ≤ δ) : |p (Z t)-p (Z u)| ≤ κ/2 := by
    have xx := osc c d e hc hd he (ω+z.val) x t u hx htu
    have yy := osc c d e hc hd he (ω+z.val) y t u hy htu
    have bound := abs_sub ((derivRay ‖B‖ g ρ c d e (Z t) x)-(derivRay ‖B‖ g ρ c d e (Z u) x))
        ((derivRay ‖B‖ g ρ c d e (Z t) y)-(derivRay ‖B‖ g ρ c d e (Z u) y))
    unfold p;rw [sub_sub_sub_comm]
    linarith only [xx,yy,bound]
  have H := Predecessor.sublevel_on_pieces diff hk mod N 0 0 r hr
  have sub : {u : ℝ | u ∈ Icc 0 1 ∧ z+⟨transverseOrbit ρ e u,hm u⟩ ∈
      {z : complexPhaseGroup B | |f (ω+z.val)| ≤ r ∧ κ < |p (ω+z.val)|}} ⊆
      Predecessor.transverseBand (fun u ↦ f (Z u)) (fun u ↦ p (Z u)) 0 (0+N*δ) 0 r κ := by
    rintro u ⟨hu,hf,hp⟩
    have rearr : ω+(z+⟨transverseOrbit ρ e u,hm u⟩:complexPhaseGroup B).val = Z u := by
      change ω+(z.val+transverseOrbit ρ e u) = (ω+z.val)+transverseOrbit ρ e u
      abel
    rw [rearr] at hf hp
    exact ⟨⟨hu.1,hu.2.trans (by linarith only [cover])⟩,by simpa only [sub_zero] using hf,hp⟩
  apply (measure_mono sub).trans (H.trans_eq _)
  rw [← ENNReal.ofReal_natCast (n:=N),←ENNReal.ofReal_mul (by positivity)]
  congr 1;ring

end Weierstrass.Descent
