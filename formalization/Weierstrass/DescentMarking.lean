module

public import Weierstrass.DescentCells
public import Weierstrass.StripHaarTests

/-! The actual derivative neighbor test of §6. Its exceptional probability is
uniform in the length, phase coset, and every permitted derivative weight. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators Topology
namespace Weierstrass.Descent
local instance markingGroupMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance markingGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- Sampling on the normalized parent costs at most the centered unnormalized
occupation. This includes the translation and Jacobian for arbitrary T≥1. -/
theorem sampled_derivative_ball {b g ρ T A r : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < b*(g*ρ)) (hT : 1 ≤ T) (hT' : T ≤ 3)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) {x : ℝ} (hx : x ∈ Ico 0 1) :
    (volume.restrict (Ico (0:ℝ) 1)) {y | |derivRay b g ρ c d e z (T*y)-derivRay b g ρ c d e z (T*x)| ≤ A*r} ≤
      rayOccupation b (g*ρ) (fun j ↦ c j*e j,d) (quarter z+transverseOrbit b d (T*x)) 3 (A/τ) r := by
  have Tpos : 0 < T := zero_lt_one.trans_le hT
  let phase := quarter z+transverseOrbit b d (T*x)
  let S : Set ℝ := {v | v ∈ Icc (-3:ℝ) 3 ∧ |circleRay b (g*ρ) (fun j ↦ c j*e j) d phase v| ≤ A/τ*r}
  have hh1 : g*ρ < 1 := (mul_lt_of_lt_one_right hg hr1).trans hg1
  have hce j : |c j*e j| ≤ 1 := by rw [abs_mul];exact (mul_le_of_le_one_right (abs_nonneg _) (he _)).trans (hc _)
  have tau : 0 < τ := by dsimp [τ];positivity
  have pre : volume ((fun y : ℝ ↦ T*y+ -(T*x)) ⁻¹' S) ≤ volume S := by
    change volume ((T*·) ⁻¹' ((· + -(T*x)) ⁻¹' S)) ≤ volume S
    rw [Real.volume_preimage_mul_left Tpos.ne',measure_preimage_add_right,abs_of_pos (inv_pos.mpr Tpos)]
    exact mul_le_of_le_one_left' (by simpa using inv_le_one_of_one_le₀ hT)
  rw [Measure.restrict_apply' measurableSet_Ico]
  apply (measure_mono _).trans pre
  rintro y ⟨hval,hy⟩
  have eq := circleRay_recenter_scale hb (mul_pos hg hr) hh1 hh hce hd (quarter z) (0:ℤ) (T*x) (T*y-T*x)
  simp only [neg_zero,zpow_zero,one_mul,Int.add_zero,show T*x+(T*y-T*x)=T*y by ring] at eq
  change circleRay b (g*ρ) _ d (quarter z) (T*y)-_ = circleRay b (g*ρ) _ d phase (T*y-T*x) at eq
  change |τ*circleRay b (g*ρ) _ d (quarter z) (T*y)-τ*circleRay b (g*ρ) _ d (quarter z) (T*x)| ≤ A*r at hval
  rw [←mul_sub,eq,abs_mul,abs_of_pos tau] at hval
  change T*y+ -(T*x) ∈ Icc (-3:ℝ) 3 ∧ _
  rw [←sub_eq_add_neg];refine ⟨⟨?_,?_⟩,?_⟩
  · linarith only [mul_nonneg Tpos.le hy.1,mul_le_of_le_one_right Tpos.le hx.2.le,hT']
  · linarith only [mul_nonneg Tpos.le hx.1,mul_le_of_le_one_right Tpos.le hy.2.le,hT']
  · change |circleRay b (g*ρ) _ d phase (T*y-T*x)| ≤ A/τ*r
    rw [div_mul_eq_mul_div,le_div_iff₀ tau,mul_comm _ τ];exact hval

def markConstant (b h : ℝ) := τ*rayBound b h 2

def marked {N : ℕ} (T : ℝ) (G : ℝ → ℝ) (w d₀ : ℝ) (x : ℝ) : Prop :=
  ∃ i : Fin N, x ∈ cell N i ∧ d₀ < ((neighbors T G w i).card:ℝ)/N

/-- For every sufficiently large fixed block size the sampled probability
of a bad derivative label is small for all mesh lengths [1,3]. The
threshold is g^(nt), whenever (gρ)^s' ≤ g^t. -/
theorem bad_label_probability {B : ℂ} (hb : 0 < ‖B‖) {g ρ s v : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (hv : 0 < v) (hv' : v < s)
    {P : Set RayParameters} (H : RayInformation B (g*ρ) s P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (ω : PhaseTorus) (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) →
      (∀ j, |d j| ≤ 1) → (∀ j, |e j| ≤ 1) → (fun j ↦ c j*e j,d) ∈ P →
      ∀ (T : ℝ), 1 ≤ T → T ≤ 3 → ∀ (N : ℕ), 0 < N → childLength ‖B‖ T n N ≤ 2 →
      ∀ (d₀ : ℝ), ((g*ρ)^n)^v ≤ d₀ →
      ((complexPhaseHaar B).prod Predecessor.unitLaw).real {z : complexPhaseGroup B × ℝ |
        marked (N:=N) T (derivRay ‖B‖ g ρ c d e (ω+z.1.val))
          ((2*markConstant ‖B‖ (g*ρ)+1)*(g*ρ)^n) d₀ z.2} ≤ ε := by
  let h := g*ρ
  let D := markConstant ‖B‖ h
  have hpos := mul_pos hg hr
  have hlt : h < 1 := (mul_lt_of_lt_one_right hg hr1).trans hg1
  have tau : 0 < τ := by dsimp [τ];positivity
  have Dpos : 0 ≤ D := by
    unfold D markConstant;apply mul_nonneg tau.le
    exact (abs_nonneg _).trans (circleRay_uniform_bound hb hpos hlt hh (c:=fun _ ↦ 0) (d:=fun _ ↦ 0)
      (by simp) (by simp) (0:PhaseTorus) (x:=0) (by norm_num : |(0:ℝ)| ≤ 2))
  have Apos : 0 < (4*D+1)/τ := div_pos (by linarith) tau
  have lim : Tendsto (fun n : ℕ ↦ h^n) atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt,Eventually.of_forall (fun n ↦ pow_pos hpos n)⟩
  filter_upwards [lim.eventually (H v hv hv' 3 ((4*D+1)/τ) (by norm_num) Apos ε hε)] with n test
  intro ω c d e hc hd he mem T hT hT' N hN len d₀ thresh
  let w (x : ℝ) := quarter ω+transverseOrbit ‖B‖ d (T*x)
  have mw : Measurable w := measurable_const.add ((measurable_transverseOrbit _ _).comp (measurable_const.mul measurable_id))
  have H' := joint_occupation_test (B:=B) Predecessor.unitLaw (MeasurePreserving.id _) mw h (fun j ↦ c j*e j,d) 3
    ((4*D+1)/τ) (h^n) v hε.le (fun ξ ↦ test ξ _ mem)
  apply (measureReal_mono (μ:=(complexPhaseHaar B).prod Predecessor.unitLaw) _).trans H'
  rintro ⟨z,x⟩ ⟨i,hi,heavy⟩
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  let G := derivRay ‖B‖ g ρ c d e (ω+z.val)
  have osc := derivative_cell_oscillation hb hg hg1 hr hr1 hh (zero_le_one.trans hT) hN len hc hd he (ω+z.val)
  have hn := neighbor_mass hN (G:=G) (D:=D*h^n) (r:=h^n) osc hi
  have hs := sampled_derivative_ball (A:=4*D+1) (r:=h^n) hb hg hg1 hr hr1 hh hT hT' hc hd he (ω+z.val) (cell_subset hN i hi)
  have eq : w x+z.val = quarter (ω+z.val)+transverseOrbit ‖B‖ d (T*x) := by
    funext j;change (ω j+_+_)+z.val j = ((ω j+z.val j)+_)+_;abel
  change ENNReal.ofReal ((h^n)^v) < rayOccupation _ _ _ (w x + z.val) _ _ _
  rw [eq]
  apply lt_of_lt_of_le _ hs
  rw [show (4*D+1)*h^n = 4*(D*h^n)+h^n by ring]
  apply lt_of_lt_of_le _ hn
  change d₀ < ((neighbors T G ((2*D+1)*h^n) i).card : ℝ)/N at heavy
  rw [show 2*(D*h^n)+h^n = (2*D+1)*h^n by ring,←ENNReal.ofReal_natCast,
    ←ENNReal.ofReal_mul (Nat.cast_nonneg _),←div_eq_mul_inv]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.rpow_nonneg (pow_nonneg hpos.le _) _)).mpr (thresh.trans_lt heavy)

end Weierstrass.Descent
