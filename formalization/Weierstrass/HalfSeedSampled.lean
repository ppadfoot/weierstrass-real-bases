module

public import Weierstrass.HalfSeed
public import Weierstrass.DescentPartition
public import Weierstrass.StripHaarTests

/-! The normalized sampled statement (H3) of the initial-exponent lemma,
uniform in the interval length. The input is T times a uniform unit seed. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.CriticalRay Weierstrass.Descent Weierstrass.StripProof
open scoped ENNReal Topology
namespace Weierstrass.RaySeed
local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem sampled_window_le_occupation {b g T R : ℝ} (hb : 0<b) (hg : 0<g) (hg1 : g<1) (hbg : 1<b*g)
    {p : RayParameters} (hc : ∀ j, |p.1 j|≤1) (hd : ∀ j, |p.2 j|≤1) (hT : 1≤T) (h3 : T≤3)
    (z : PhaseTorus) {x : ℝ} (hx : x∈Ico 0 1) :
    fullLaw b g T p z (Metric.closedBall (ordinate b g T p z x) R) ≤
      rayOccupation b g p (z+transverseOrbit b p.2 (T*x)) 3 1 R := by
  have tp := zero_lt_one.trans_le hT
  let S := {v : ℝ | v∈Icc (-3:ℝ) 3 ∧ |circleRay b g p.1 p.2 (z+transverseOrbit b p.2 (T*x)) v|≤1*R}
  have rescale : volume ((fun y : ℝ ↦ T*y+ -(T*x)) ⁻¹' S) ≤ volume S := by
    change volume ((T*·) ⁻¹' ((· + -(T*x)) ⁻¹' S)) ≤ volume S
    rw [Real.volume_preimage_mul_left tp.ne',measure_preimage_add_right,abs_of_pos (inv_pos.mpr tp)]
    exact mul_le_of_le_one_left' (by simpa using inv_le_one_of_one_le₀ hT)
  rw [fullLaw,Measure.map_apply (ordinate_measurable ..) Metric.isClosed_closedBall.measurableSet,
    Predecessor.unitLaw,Measure.restrict_apply' measurableSet_Ico]
  apply (measure_mono _).trans rescale
  rintro y ⟨hv,hy⟩
  change |circleRay b g p.1 p.2 z (T*y)-circleRay b g p.1 p.2 z (T*x)|≤R at hv
  have eq := circleRay_recenter_scale hb hg hg1 hbg hc hd z (0:ℤ) (T*x) (T*y-T*x)
  simp only [neg_zero,zpow_zero,one_mul,Int.add_zero,show T*x+(T*y-T*x)=T*y by ring] at eq
  change T*y+ -(T*x) ∈ Icc (-3:ℝ) 3 ∧ _
  rw [←sub_eq_add_neg]
  refine ⟨⟨?_,?_⟩,?_⟩
  · linarith only [mul_nonneg tp.le hy.1,mul_le_of_le_one_right tp.le hx.2.le,h3]
  · linarith only [mul_nonneg tp.le hx.1,mul_le_of_le_one_right tp.le hy.2.le,h3]
  · change |circleRay b g p.1 p.2 (z+transverseOrbit b p.2 (T*x)) (T*y+ -(T*x))|≤1*R
    rw [←sub_eq_add_neg,one_mul]
    change circleRay b g p.1 p.2 z (T*y)-circleRay b g p.1 p.2 z (T*x)= circleRay b g p.1 p.2 (z+transverseOrbit b p.2 (T*x)) (T*y-T*x) at eq
    rwa [←eq]

/-- Recentring transfers the full family of centered tests to sampled
closed-ball thresholds on every normalized interval of length in [1,3]. -/
theorem sampled_intervals_of_rayInformation {B : ℂ} {g s : ℝ} (hb : 1<‖B‖) (hg : 0<g)
    (hg1 : g<1) (hbg : 1<‖B‖*g) {P : Set RayParameters} (H : RayInformation B g s P)
    (bounded : ∀ p∈P, (∀ j, |p.1 j|≤1) ∧ (∀ j, |p.2 j|≤1)) {h K ε : ℝ}
    (hp : 0<h) (hs : h<s) (hK : 0<K) (hε : 0<ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (ω : PhaseTorus) (p : RayParameters), p∈P → ∀ (T : ℝ), 1≤T → T≤3 →
      ((complexPhaseHaar B).prod Predecessor.unitLaw).real {z | ENNReal.ofReal (r^h) <
        fullLaw ‖B‖ g T p (ω+z.1.val) (Metric.closedBall (ordinate ‖B‖ g T p (ω+z.1.val) z.2) (K*r))} ≤ ε := by
  filter_upwards [H h hp hs 3 K (by norm_num) hK ε hε] with r hr
  intro ω p mem T hT h3
  let w := fun x : ℝ ↦ ω+transverseOrbit ‖B‖ p.2 (T*x)
  have mw : Measurable w := measurable_const.add ((measurable_transverseOrbit _ _).comp (measurable_const.mul measurable_id))
  have bd := joint_occupation_test (B:=B) Predecessor.unitLaw (MeasurePreserving.id _) mw g p 3 K r h hε.le (fun φ ↦ hr φ p mem)
  apply le_trans _ bd
  apply ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _) |>.mpr
  apply measure_mono_ae
  have seed : ∀ᵐ z ∂(complexPhaseHaar B).prod Predecessor.unitLaw, z.2 ∈ Ico (0:ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ:=complexPhaseHaar B) (ν:=Predecessor.unitLaw)).ae (ae_restrict_mem measurableSet_Ico)
  filter_upwards [seed] with z hz bad
  have comp := sampled_window_le_occupation (R:=K*r) (zero_lt_one.trans hb) hg hg1 hbg (bounded p mem).1
    (bounded p mem).2 hT h3 (ω+z.1.val) hz
  have eq : w z.2+z.1.val = (ω+z.1.val)+transverseOrbit ‖B‖ p.2 (T*z.2) := by dsimp only [w];abel
  change ENNReal.ofReal (r^h)<rayOccupation ‖B‖ g p (w z.2+z.1.val) 3 K r
  rw [eq]
  exact bad.trans_le (by simpa only [rayOccupation,one_mul] using comp)

/-- (H3), with uniform thresholds over the weight/ray family, the translated
Haar environment and all interval lengths in [1,3]. -/
theorem half_seed_H3 {B : ℂ} (hb : 1<‖B‖) {g ρ δ : ℝ}
    (hg : 0<g) (hg1 : g<1) (hq : 1<‖B‖*g) (hρ : 0<ρ) (hρ' : ρ<1)
    (hQ : (‖B‖*g)*ρ<1) (hbQ : 1<((‖B‖*g)*ρ)*‖B‖) (hδ : 0<δ) (D : ℕ) {P : Set RayParameters}
    (weights : ∀ p∈P, (∀ t, transverseOrbit ‖B‖ p.2 t ∈ complexPhaseGroup B) ∧
      ∃ e, GoodWeight D δ p.1 p.2 e ∧ ∀ t, transverseOrbit ρ e t ∈ complexPhaseGroup B)
    {h K ε : ℝ} (hp : 0<h) (hs : h<1/2) (hK : 0<K) (hε : 0<ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (ω : PhaseTorus) (p : RayParameters), p∈P → ∀ (T : ℝ), 1≤T → T≤3 →
      ((complexPhaseHaar B).prod Predecessor.unitLaw).real {z | ENNReal.ofReal (r^h) <
        fullLaw ‖B‖ g T p (ω+z.1.val) (Metric.closedBall (ordinate ‖B‖ g T p (ω+z.1.val) z.2) (K*r))} ≤ ε := by
  apply sampled_intervals_of_rayInformation hb hg hg1 hq
    (rayInformation_half hb hg hg1 hq hρ hρ' hQ hbQ hδ D weights) _ hp hs hK hε
  intro p mem
  obtain ⟨e,good,_⟩ := (weights p mem).2
  exact ⟨good.1,good.2.1⟩

end Weierstrass.RaySeed
