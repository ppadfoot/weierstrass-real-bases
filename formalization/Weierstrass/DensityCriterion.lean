module

public import Weierstrass.PrefixEnergy
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! The absolute continuity and square-integrable density criteria at the end
of Appendix B. The estimates are stated for arbitrary laws on the line. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
namespace Weierstrass.Branch

/-- Absolute continuity gives the subcritical small-ball estimates at points
sampled from the law itself. -/
theorem ac_sampled_dimension (μ : Measure ℝ) [IsFiniteMeasure μ] (ac : μ ≪ volume)
    {σ : ℝ} (hs : σ<1) :
    ∀ᵐ y ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0, μ (Icc (y-r) (y+r)) ≤ ENNReal.ofReal (r^σ) := by
  filter_upwards [ac.ae_le (Besicovitch.ae_tendsto_rnDeriv μ volume),
    ac.ae_le (Measure.rnDeriv_lt_top μ volume)] with y H finite
  let K := (μ.rnDeriv volume y).toReal+1
  have kp : 0<K := by dsimp [K];positivity
  have kbig : μ.rnDeriv volume y < ENNReal.ofReal K := by
    rw [←ENNReal.ofReal_toReal finite.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff kp).mpr (lt_add_one _)
  have ep := sub_pos.mpr hs
  have lim := (Real.continuousAt_rpow_const 0 (1-σ) (.inr ep.le)).tendsto.mono_left
    (nhdsWithin_le_nhds (s:=Ioi 0))
  rw [Real.zero_rpow ep.ne'] at lim
  filter_upwards [self_mem_nhdsWithin,H.eventually_lt_const kbig,
    lim.eventually_lt_const (inv_pos.mpr (mul_pos (by norm_num : (0:ℝ)<2) kp))] with r (rp : 0<r) rat tiny
  have bound := (ENNReal.div_le_iff_le_mul (.inr ENNReal.ofReal_ne_top)
    (.inr (ENNReal.ofReal_pos.mpr kp).ne')).mp rat.le
  rw [Real.volume_closedBall,Real.closedBall_eq_Icc,←ENNReal.ofReal_mul kp.le] at bound
  apply bound.trans (ENNReal.ofReal_le_ofReal _)
  have factor : r^(1-σ)*r^σ=r := by rw [←Real.rpow_add rp,sub_add_cancel,Real.rpow_one]
  have t : 2*K*r^(1-σ)≤1 := by
    simpa only [mul_inv_cancel₀ (mul_pos (by norm_num : (0:ℝ)<2) kp).ne'] using
      mul_le_mul_of_nonneg_left tiny.le (mul_pos (by norm_num : (0:ℝ)<2) kp).le
  nlinarith only [mul_le_mul_of_nonneg_right t (Real.rpow_pos_of_pos rp σ).le,
    congrArg (fun x : ℝ => 2*K*x) factor]

/-- Exactly the factor 2R for sampled balls under a density with finite
square integral. The extended-real inequality also allows an infinite RHS. -/
theorem density_collision (f : ℝ → ℝ≥0) (mf : Measurable f) (R : ℝ) :
    let ν := volume.withDensity (fun x => (f x:ℝ≥0∞))
    (ν.prod ν) (PrefixEnergy.band R) ≤ ENNReal.ofReal (2*R)*(∫⁻ x, (f x:ℝ≥0∞)^2) := by
  intro ν
  let P : Measure (ℝ×ℝ) := volume.prod volume
  let B := PrefixEnergy.band R
  let M := ENNReal.ofReal (2*R)*(∫⁻ x, (f x:ℝ≥0∞)^2)
  have mb := PrefixEnergy.band_measurable R
  have m' : Measurable (fun x => (f x:ℝ≥0∞)) := mf.coe_nnreal_ennreal
  have slab (x : ℝ) : volume ((Prod.mk x) ⁻¹' B) = ENNReal.ofReal (2*R) := by
    have eq : (Prod.mk x) ⁻¹' B = closedBall x R := by
      ext y;change |x-y|≤R ↔ |y-x|≤R;rw [abs_sub_comm]
    rw [eq,Real.volume_closedBall]
  have line : (∫⁻ v in B, (f v.1:ℝ≥0∞)^2 ∂P) = M := by
    rw [←lintegral_indicator mb]
    have meas : Measurable (B.indicator fun v : ℝ × ℝ => (f v.1:ℝ≥0∞)^2) :=
      ((m'.comp measurable_fst).pow_const 2).indicator mb
    rw [lintegral_prod _ meas.aemeasurable]
    calc
      _ = ∫⁻ x : ℝ, (f x:ℝ≥0∞)^2*ENNReal.ofReal (2*R) := by
        apply lintegral_congr;intro x
        change (∫⁻ y, ((Prod.mk x) ⁻¹' B).indicator (fun _ : ℝ => (f x:ℝ≥0∞)^2) y) = _
        rw [lintegral_indicator_const (mb.preimage measurable_prodMk_left),slab]
      _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,mul_comm]
  have line' : (∫⁻ v in B, (f v.2:ℝ≥0∞)^2 ∂P) = M := by
    rw [←lintegral_indicator mb]
    have sym (v : ℝ × ℝ) : B.indicator (fun w : ℝ×ℝ => (f w.2:ℝ≥0∞)^2) v =
        B.indicator (fun w : ℝ×ℝ => (f w.1:ℝ≥0∞)^2) v.swap := by
      have ball : v.swap ∈ B ↔ v ∈ B := by change |v.2-v.1|≤R ↔ |v.1-v.2|≤R;rw [abs_sub_comm]
      by_cases bv : v∈B <;> simp [bv,ball]
    calc
      _ = ∫⁻ v, B.indicator (fun w : ℝ×ℝ => (f w.1:ℝ≥0∞)^2) v.swap ∂P := lintegral_congr sym
      _ = _ := by
        erw [lintegral_prod_swap]
        rwa [lintegral_indicator mb]
  have point (v : ℝ×ℝ) : (f v.1:ℝ≥0∞)*(f v.2:ℝ≥0∞) ≤
      ((f v.1:ℝ≥0∞)^2+(f v.2:ℝ≥0∞)^2)/2 := by
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
    exact_mod_cast (show f v.1*f v.2*2 ≤ (f v.1)^2+(f v.2)^2 by
      exact_mod_cast (show (f v.1:ℝ)*(f v.2:ℝ)*2 ≤ (f v.1:ℝ)^2+(f v.2:ℝ)^2 by nlinarith only [sq_nonneg ((f v.1:ℝ)-(f v.2:ℝ))]))
  rw [show ν=volume.withDensity (fun x => (f x:ℝ≥0∞)) from rfl,prod_withDensity m' m',withDensity_apply _ mb]
  apply (lintegral_mono (μ:=P.restrict B) point).trans_eq
  simp only [div_eq_mul_inv]
  have mleft : Measurable (fun v : ℝ×ℝ => (f v.1:ℝ≥0∞)^2) := (m'.comp measurable_fst).pow_const 2
  rw [lintegral_mul_const' _ _ (by norm_num),lintegral_add_left mleft, line, line']
  change (M+M)*2⁻¹ = M
  rw [←two_mul,mul_comm,←mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]

/-- A finite-prefix approximation of a sampled variable may be used as the
ball center. On a probability space the error C*r enlarges D*r to (D+C)*r.
For r=γ^k this gives the quantitative γ^{(1-σ)k} discarded-prefix bound. -/
theorem density_bad_prefix {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {F : X → ℝ} (mF : Measurable F) (approx : X → ℝ) (f : ℝ → ℝ≥0) (mf : Measurable f)
    (law : μ.map F = volume.withDensity (fun y => (f y:ℝ≥0∞))) {C D r : ℝ} (rp : 0<r)
    (err : ∀ x, |approx x-F x|≤C*r) (σ : ℝ) :
    μ {x | ENNReal.ofReal (r^σ) < μ.map F (Icc (approx x-D*r) (approx x+D*r))} ≤
      ENNReal.ofReal (2*(D+C)*r^(1-σ))*(∫⁻ y, (f y:ℝ≥0∞)^2) := by
  let ν := μ.map F
  let H := (D+C)*r
  let E := {y : ℝ | ENNReal.ofReal (r^σ) ≤ ν ((Prod.mk y) ⁻¹' PrefixEnergy.band H)}
  have mE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_measure_prodMk_left (PrefixEnergy.band_measurable H))
  have inclusion : {x | ENNReal.ofReal (r^σ) < μ.map F (Icc (approx x-D*r) (approx x+D*r))} ⊆ F ⁻¹' E := by
    intro x hx
    apply hx.le.trans (measure_mono _)
    intro y hy
    change |F x-y| ≤ H
    obtain ⟨l,u⟩ := abs_le.mp (err x)
    dsimp only [H];rw [abs_le];constructor <;> linarith only [l,u,hy.1,hy.2]
  have power := Real.rpow_pos_of_pos rp σ
  have control : ν E ≤ (ν.prod ν) (PrefixEnergy.band H) / ENNReal.ofReal (r^σ) := by
    let _ := Measure.isProbabilityMeasure_map (μ:=μ) mF.aemeasurable
    rw [Measure.prod_apply (PrefixEnergy.band_measurable H)]
    exact meas_ge_le_lintegral_div (measurable_measure_prodMk_left (PrefixEnergy.band_measurable H)).aemeasurable
      (ENNReal.ofReal_pos.mpr power).ne' ENNReal.ofReal_ne_top
  have cap := density_collision f mf H
  change (volume.withDensity (fun y => (f y:ℝ≥0∞))).prod (volume.withDensity (fun y => (f y:ℝ≥0∞))) _ ≤ _ at cap
  rw [←law] at cap
  refine (measure_mono inclusion).trans ((Measure.map_apply mF mE).symm.le.trans (control.trans
    ((ENNReal.div_le_div_right cap _).trans_eq ?_)))
  rw [div_eq_mul_inv,mul_right_comm,←div_eq_mul_inv,←ENNReal.ofReal_div_of_pos power]
  congr 2
  rw [Real.rpow_sub rp,Real.rpow_one];dsimp [H];ring

/-- Integrating the prefix bound over the central coordinates gives the single
square-integral constant of Appendix B, even when the individual conditional
densities are unbounded. -/
theorem averaged_density_bad_prefix {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    (κ : Measure W) (μ : Measure X) [IsProbabilityMeasure μ]
    (F approx : W → X → ℝ) (f : W → ℝ → ℝ≥0) {C D r σ : ℝ} (rp : 0<r)
    (mF : ∀ w, Measurable (F w)) (mf : ∀ w, Measurable (f w))
    (law : ∀ᵐ w ∂κ, μ.map (F w) = volume.withDensity (fun y => (f w y:ℝ≥0∞)))
    (err : ∀ w x, |approx w x-F w x|≤C*r)
    (mE : MeasurableSet {v : W×X | ENNReal.ofReal (r^σ) <
      μ.map (F v.1) (Icc (approx v.1 v.2-D*r) (approx v.1 v.2+D*r))}) :
    (κ.prod μ) {v : W×X | ENNReal.ofReal (r^σ) <
      μ.map (F v.1) (Icc (approx v.1 v.2-D*r) (approx v.1 v.2+D*r))} ≤
      ENNReal.ofReal (2*(D+C)*r^(1-σ))*(∫⁻ w, (∫⁻ y, (f w y:ℝ≥0∞)^2) ∂κ) := by
  rw [Measure.prod_apply mE,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [law] with w hw
  exact density_bad_prefix μ (mF w) (approx w) (f w) (mf w) hw rp (err w) σ

end Weierstrass.Branch
