module

public import Weierstrass.DescentPartition
public import Weierstrass.StripAngular

/-! Transfer the untrimmed sampled law on the fixed physical interval [0,3]
to centered Lebesgue occupations on every bounded time interval. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal Topology
namespace Weierstrass.Descent
open Angular
open Predecessor (unitLaw)
local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- Sampled small-ball estimate on the fixed interval of physical length three. -/
def SampledInformation (B : ℂ) (g s : ℝ) (P : Set RayParameters) : Prop :=
  ∀ h : ℝ, 0 < h → h < s → ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ω : PhaseTorus, ∀ p ∈ P,
      ((complexPhaseHaar B).prod unitLaw).real {v : complexPhaseGroup B × ℝ |
        ENNReal.ofReal (r^h) < fullLaw ‖B‖ g 3 p (ω+v.1.val)
          (Metric.closedBall (ordinate ‖B‖ g 3 p (ω+v.1.val) v.2) (A*r))} ≤ ε

private theorem compare_sampled {b g T A r : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (n : ℕ) (fit : 2*T ≤ b^n)
    {p : RayParameters} (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1)
    (z : PhaseTorus) {x : ℝ} (hx : x ∈ Icc (1/3:ℝ) (2/3)) :
    rayOccupation b g (shiftedParameters p n) (physicalEnvironment b p.2 z n (3*x)) T A r ≤
      ENNReal.ofReal (3*b^n) * fullLaw b g 3 p z
        (Metric.closedBall (ordinate b g 3 p z x) ((g^n*A)*r)) := by
  have bp := pow_pos hb n
  let K := 3*b^n
  have kp : 0 < K := by dsimp [K]; positivity
  let S := (ordinate b g 3 p z ⁻¹' Metric.closedBall (ordinate b g 3 p z x) ((g^n*A)*r)) ∩ Ico 0 1
  have changeVar : volume ((fun u : ℝ => x+K⁻¹*u) ⁻¹' S) = ENNReal.ofReal K * volume S := by
    change volume (((K⁻¹*·) ⁻¹' ((x+·) ⁻¹' S))) = _
    rw [Real.volume_preimage_mul_left (inv_ne_zero kp.ne'),inv_inv,abs_of_pos kp,measure_preimage_add]
  rw [fullLaw,Measure.map_apply (ordinate_measurable _ _ _ _ _) Metric.isClosed_closedBall.measurableSet,
    unitLaw,Measure.restrict_apply' measurableSet_Ico]
  change _ ≤ ENNReal.ofReal K * volume S
  rw [←changeVar]
  apply measure_mono
  rintro u ⟨hu,hy⟩
  have clow : -(1/2:ℝ) ≤ (b^n)⁻¹*u := by
    rw [←div_eq_inv_mul,le_div_iff₀ bp]; linarith [hu.1]
  have cup : (b^n)⁻¹*u ≤ (1/2:ℝ) := by
    rw [←div_eq_inv_mul,div_le_iff₀ bp]; linarith [hu.2]
  have scale : 3*(x+K⁻¹*u)=3*x+(b^n)⁻¹*u := by dsimp [K];field_simp
  have recenter :=  circleRay_recenter_scale hb hg hg1 hbg hc hd z (n:ℤ) (3*x) u
  rw [zpow_neg,zpow_natCast,zpow_natCast,←scale] at recenter
  change ordinate b g 3 p z (x+K⁻¹*u)-ordinate b g 3 p z x =
    g^n*circleRay b g (shiftedParameters p n).1 (shiftedParameters p n).2
      (physicalEnvironment b p.2 z n (3*x)) u at recenter
  constructor
  · change |ordinate b g 3 p z (x+K⁻¹*u)-ordinate b g 3 p z x| ≤ _
    rw [recenter,abs_mul,abs_of_pos (pow_pos hg n),mul_assoc]
    exact mul_le_mul_of_nonneg_left hy (pow_pos hg n).le
  · change 0 ≤ x+K⁻¹*u ∧ x+K⁻¹*u < 1
    constructor <;> linarith only [hx.1,hx.2,clow,cup,scale]

private theorem window_haar {B : ℂ} (hB : B ≠ 0) (ω : PhaseTorus) (n : ℕ)
    (d : ℤ → ℝ) (hm : ∀ x, transverseOrbit ‖B‖ d x ∈ complexPhaseGroup B)
    {S : Set PhaseTorus} (mS : MeasurableSet S) :
    ((complexPhaseHaar B).prod unitLaw) {v : complexPhaseGroup B × ℝ |
      v.2 ∈ Icc (1/3:ℝ) (2/3) ∧ physicalEnvironment ‖B‖ d
        ((shiftPhase (-(n:ℤ)) ω)+v.1.val) n (3*v.2) ∈ S} =
      ENNReal.ofReal (1/3:ℝ) * (complexPhaseHaar B) {z : complexPhaseGroup B | ω+z.val ∈ S} := by
  let J := Icc (1/3:ℝ) (2/3)
  let E := {z : complexPhaseGroup B | ω+z.val ∈ S}
  let V := fun (v : complexPhaseGroup B × ℝ) => physicalEnvironment ‖B‖ d
    ((shiftPhase (-(n:ℤ)) ω)+v.1.val) n (3*v.2)
  have mV : Measurable V := (measurable_physicalEnvironment _ _ _).comp
    ((measurable_const.add (continuous_subtype_val.measurable.comp measurable_fst)).prodMk
      (measurable_const.mul measurable_snd))
  have mE : MeasurableSet E := mS.preimage (measurable_const.add continuous_subtype_val.measurable)
  have slice (x : ℝ) : (complexPhaseHaar B) {z : complexPhaseGroup B | V (z,x) ∈ S} =
      (complexPhaseHaar B) E := by
    let sh := inducedPhaseMap B B (shiftPhase (n:ℤ)) (shiftPhase_group hB n)
    let off : complexPhaseGroup B := sh ⟨transverseOrbit ‖B‖ d (3*x),hm _⟩
    have eq : {z : complexPhaseGroup B | V (z,x) ∈ S} = sh ⁻¹' ((off+·) ⁻¹' E) := by
      ext z
      change V (z,x) ∈ S ↔ ω+(off+sh z).val ∈ S
      apply Iff.of_eq
      apply congrArg (fun q : PhaseTorus => q ∈ S)
      funext j
      change (ω (j+(n:ℤ)+ -(n:ℤ))+z.val (j+n))+_ = ω j+(_+z.val (j+n))
      rw [add_neg_cancel_right];abel
    rw [eq]
    have preM : MeasurableSet ((off+·) ⁻¹' E) := mE.preimage ((continuous_const.add continuous_id).measurable)
    exact ((shiftPhase_preserving hB (n:ℤ)).measure_preimage preM.nullMeasurableSet).trans
      (measure_preimage_add (complexPhaseHaar B) off E)
  change ((complexPhaseHaar B).prod unitLaw) {v | v.2 ∈ J ∧ V v ∈ S} = _
  have eventM : MeasurableSet {v : complexPhaseGroup B × ℝ | v.2 ∈ J ∧ V v ∈ S} :=
    (measurableSet_Icc.preimage measurable_snd).inter (mS.preimage mV)
  rw [Measure.prod_apply_symm eventM]
  have sect (x : ℝ) : (complexPhaseHaar B)
      ((fun z : complexPhaseGroup B => (z,x)) ⁻¹' {v | v.2 ∈ J ∧ V v ∈ S}) =
      J.indicator (fun _ => (complexPhaseHaar B) E) x := by
    by_cases hx : x ∈ J
    · simpa [hx] using slice x
    · simp [hx]
  simp_rw [sect]
  rw [lintegral_indicator measurableSet_Icc,lintegral_const,Measure.restrict_apply_univ,
    unitLaw,Measure.restrict_apply' measurableSet_Ico,inter_eq_left.mpr
      (show J ⊆ Ico 0 1 from fun y hy => ⟨by linarith only [hy.1],by linarith only [hy.2]⟩),
    Real.volume_Icc,mul_comm]
  norm_num
  rfl

/-- Centered occupation at arbitrary physical length. Both the change of time
and the shifted physical phase group act on the actual weighted ray. -/
theorem rayInformation_of_sampled {B : ℂ} (hb : 1 < ‖B‖) {g s : ℝ} (hg : 0 < g)
    (hg1 : g < 1) (hbg : 1 < ‖B‖*g) {ζ v : Circle} {k : ℕ}
    (H : SampledInformation B g s (physicalFamily B ζ v k)) :
    RayInformation B g s (physicalFamily B ζ v k) := by
  intro h hh hs T A _ hA ε hε
  obtain ⟨w,hw,hws⟩ := exists_between hs
  obtain ⟨n,fit⟩ := pow_unbounded_of_one_lt (2*T) hb
  have bp := zero_lt_one.trans hb
  have nz : B ≠ 0 := norm_ne_zero_iff.mp bp.ne'
  let K := 3*‖B‖^n
  have kp : 0 < K := mul_pos (by norm_num) (pow_pos bp n)
  have ep := sub_pos.mpr hw
  have lim := ((Real.continuousAt_rpow_const 0 (w-h) (.inr ep.le)).tendsto.mono_left
    (nhdsWithin_le_nhds (s:=Ioi 0))).const_mul K
  rw [Real.zero_rpow ep.ne',mul_zero] at lim
  filter_upwards [self_mem_nhdsWithin,lim.eventually_lt_const zero_lt_one,
    H w (hh.trans hw) hws (g^n*A) (ε/3) (mul_pos (pow_pos hg n) hA) (by positivity)] with r (rp : 0 < r) small law
  intro ω p hp
  let P := shiftedParameters p (-(n:ℤ))
  have hP : P ∈ physicalFamily B ζ v k := shiftedParameters_mem nz hp _
  have eqP : shiftedParameters P n = p := by
    ext j <;> simp [P,shiftedParameters]
  let S := {y : PhaseTorus | ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g p y T A r}
  have mS : MeasurableSet S := measurableSet_lt measurable_const (measurable_rayOccupation _ _ _ _ _ _)
  let J := Icc (1/3:ℝ) (2/3)
  let Ω := shiftPhase (-(n:ℤ)) ω
  let E := {z : complexPhaseGroup B | ω+z.val ∈ S}
  let V := {v : complexPhaseGroup B × ℝ | v.2 ∈ J ∧
    physicalEnvironment ‖B‖ P.2 (Ω+v.1.val) n (3*v.2) ∈ S}
  have mass := window_haar nz ω n P.2 hP.2 mS
  change ((complexPhaseHaar B).prod unitLaw) V = ENNReal.ofReal (1/3:ℝ)*(complexPhaseHaar B) E at mass
  have threshold : K*r^w ≤ r^h := by
    rw [Real.rpow_sub rp] at small
    calc K*r^w = (K*(r^w/r^h))*r^h := by field_simp [(Real.rpow_pos_of_pos rp h).ne']
         _ ≤ 1*r^h := mul_le_mul_of_nonneg_right small.le (Real.rpow_pos_of_pos rp h).le
         _ = _ := one_mul _
  have cost := law Ω P hP
  have inclusion : V ⊆ {v : complexPhaseGroup B × ℝ | ENNReal.ofReal (r^w) <
      fullLaw ‖B‖ g 3 P (Ω+v.1.val) (Metric.closedBall (ordinate ‖B‖ g 3 P (Ω+v.1.val) v.2) ((g^n*A)*r))} := by
    rintro ⟨z,x⟩ ⟨hx,hocc⟩
    have comp := compare_sampled (A:=A) (r:=r) bp hg hg1 hbg n fit.le hP.1.1.bounded hP.1.2.bounded (Ω+z.val) hx
    rw [eqP] at comp
    change ENNReal.ofReal (r^h) < _ at hocc
    change ENNReal.ofReal (r^w) < _
    by_contra! bad
    have upper := comp.trans (mul_le_mul_right bad (ENNReal.ofReal K))
    rw [←ENNReal.ofReal_mul kp.le] at upper
    exact (not_lt_of_ge (upper.trans (ENNReal.ofReal_le_ofReal threshold))) hocc
  have le := (measureReal_mono (μ:=(complexPhaseHaar B).prod unitLaw) inclusion).trans cost
  rw [measureReal_def,mass,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)] at le
  change (complexPhaseHaar B E).toReal ≤ ε
  linarith

end Weierstrass.Descent
