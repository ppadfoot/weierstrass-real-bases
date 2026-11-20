module

public import Weierstrass.StripGaussian

/-! # Gaussian localization at a single physical mesh

Averaging over neighboring square centers proves the bound directly from the mass of
squares at the one prescribed mesh. No estimates on intermediate scales are required. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Weierstrass.StripProof

def box (c : Plane) (r : ℝ) : Set Plane :=
  Icc (c.1-r) (c.1+r) ×ˢ Icc (c.2-r) (c.2+r)

def bell (a : ℝ) (c p : Plane) : ℝ :=
  Real.exp (-a*(p.1-c.1)^2) * Real.exp (-a*(p.2-c.2)^2)

theorem bell_pos (a : ℝ) (c p : Plane) : 0 < bell a c p := mul_pos (Real.exp_pos _) (Real.exp_pos _)

theorem measurable_box (c : Plane) (r : ℝ) : MeasurableSet (box c r) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem real_volume_box (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (box c r) = (2*r)^2 := by
  change (volume.prod volume).real _ = _
  rw [box,measureReal_prod_prod]
  simp only [measureReal_def,Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

theorem mem_box_comm (z p : Plane) (r : ℝ) : z ∈ box p r ↔ p ∈ box z r := by
  simp only [box, mem_prod,mem_Icc]; constructor <;> rintro ⟨⟨a,b⟩,c,d⟩ <;>
    exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

theorem integrable_bell {a : ℝ} (ha : 0 < a) (c : Plane) : Integrable (bell a c) := by
  exact ((integrable_exp_neg_mul_sq ha).comp_sub_right c.1).mul_prod
    ((integrable_exp_neg_mul_sq ha).comp_sub_right c.2)

theorem integral_bell {a : ℝ} (ha : 0 < a) (c : Plane) :
    ∫ p, bell a c p = Real.pi/a := by
  unfold bell
  rw [show (volume : Measure Plane) = volume.prod volume from rfl,
    integral_prod_mul (fun u => Real.exp (-a*(u-c.1)^2)) (fun u => Real.exp (-a*(u-c.2)^2))]
  simp_rw [integral_sub_right_eq_self (fun u : ℝ => Real.exp (-a*u^2)),integral_gaussian]
  rw [← sq,Real.sq_sqrt (by positivity)]

private theorem bell_shift {a r : ℝ} (ha : 0 ≤ a) (c p z : Plane) (hz : z ∈ box p r) :
    bell a c p ≤ Real.exp (2*a*r^2)*bell (a/2) c z := by
  obtain ⟨⟨x1,x2⟩,y1,y2⟩ := hz
  have bound (x y t : ℝ) (h₁ : x-r ≤ y) (h₂ : y ≤ x+r) :
      (y-t)^2 ≤ 2*(x-t)^2 + 2*r^2 := by
    nlinarith [sq_nonneg ((y-x)-(x-t)),mul_nonneg (by linarith : 0 ≤ r-(y-x))
      (by linarith : 0 ≤ r+(y-x))]
  have h₁ := mul_le_mul_of_nonneg_left (bound p.1 z.1 c.1 x1 x2) ha
  have h₂ := mul_le_mul_of_nonneg_left (bound p.2 z.2 c.2 y1 y2) ha
  simp only [bell,← Real.exp_add,Real.exp_le_exp]
  linarith

/-- A uniform one-mesh square mass bounds every translate of a Gaussian integral.
The explicit form works both on the physical and on the frequency side. -/
theorem gaussian_of_box_bound (μ : Measure Plane) [IsFiniteMeasure μ] {r a B : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hbox : ∀ z, μ.real (box z r) ≤ B) (c : Plane) :
    (2*r)^2 * (∫ p, bell a c p ∂μ) ≤ Real.exp (2*a*r^2) * B * (Real.pi/(a/2)) := by
  classical
  let E := Real.exp (2*a*r^2)
  let k := bell (a/2) c
  let H (p z : Plane) := (box p r).indicator (fun z => E*k z) z
  have hk : Integrable k := integrable_bell (by positivity) _
  have hm : MeasurableSet {v : Plane × Plane | v.2 ∈ box v.1 r} := by
    change MeasurableSet (({v : Plane × Plane | v.1.1-r ≤ v.2.1} ∩
      {v : Plane × Plane | v.2.1 ≤ v.1.1+r}) ∩ ({v : Plane × Plane | v.1.2-r ≤ v.2.2} ∩
      {v : Plane × Plane | v.2.2 ≤ v.1.2+r}))
    measurability
  have HI : Integrable (Function.uncurry H) (μ.prod volume) := by
    have he := ((integrable_const (1:ℝ) (μ := μ)).mul_prod (hk.const_mul E)).indicator hm
    apply he.congr (ae_of_all _ fun v => ?_)
    rcases v with ⟨p,z⟩
    by_cases h : z ∈ box p r <;> simp [H, Function.uncurry_apply_pair, h]
  have msmall : Integrable (fun p => bell a c p) μ := by
    have cm : Continuous (bell a c) := by unfold bell; fun_prop
    refine (integrable_const (1:ℝ)).mono' cm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs,abs_of_pos (bell_pos _ _ _)]
    apply mul_le_one₀ (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (p.1-c.1)]))
      (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (p.2-c.2)]))
  calc
    _ = ∫ p, (2*r)^2 * bell a c p ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ p, ∫ z, H p z ∂volume ∂μ := by
      apply integral_mono (msmall.const_mul _) HI.integral_prod_left
      intro p
      change (2*r)^2 * bell a c p ≤ ∫ z, H p z
      rw [← real_volume_box p hr.le,← smul_eq_mul,← integral_indicator_const _ (measurable_box p r)]
      apply integral_mono ((integrableOn_const ((isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne)).integrable_indicator (measurable_box p r))
        ((hk.const_mul E).indicator (measurable_box p r))
      intro z
      change (box p r).indicator (fun _ => bell a c p) z ≤ (box p r).indicator (fun z => E*k z) z
      by_cases h : z ∈ box p r
      · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]; exact bell_shift ha.le c p z h
      · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h]
    _ = ∫ z, ∫ p, H p z ∂μ ∂volume := integral_integral_swap HI
    _ ≤ ∫ z, E*B*k z ∂volume := by
      apply integral_mono HI.integral_prod_right (hk.const_mul _)
      intro z
      change (∫ p, H p z ∂μ) ≤ E*B*k z
      have funid : (fun p => H p z) = (box z r).indicator (fun _ => E*k z) := by
        funext p
        by_cases hp : z ∈ box p r
        · simp [H,hp,(mem_box_comm z p r).mp hp]
        · have hn : p ∉ box z r := fun hh => hp ((mem_box_comm z p r).mpr hh)
          simp [H,hp,hn]
      rw [funid,integral_indicator_const _ (measurable_box z r),smul_eq_mul]
      have pos : 0 ≤ E*k z := mul_nonneg (Real.exp_pos _).le (bell_pos _ _ _).le
      nlinarith [mul_le_mul_of_nonneg_right (hbox z) pos]
    _ = _ := by rw [integral_const_mul,integral_bell (by positivity)]

end Weierstrass.StripProof
