module

public import Weierstrass.SlopeInformation
public import Weierstrass.FullBall

/-! Conditional full-law tests from the actual retained slope laws of Appendix B. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Weierstrass.Predecessor

theorem sampled_full_ball {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω) [IsProbabilityMeasure m]
    (f : Ω → ℝ → ℝ) (hf : Measurable (Function.uncurry f)) (ξ : Ω → Measure ℝ) (hξ : Measurable ξ)
    (dom : ∀ w, ξ w ≤ unitLaw.map (f w)) {R τ K : ℝ} (hR : 0 < R) (hτ : 0 < τ) (hK : 1 < K) :
    (m.prod unitLaw) {z | ENNReal.ofReal τ < (unitLaw.map (f z.1)) (Icc (f z.1 z.2-R) (f z.1 z.2+R))} ≤
      (∫⁻ w, 1-ξ w univ ∂m) + ENNReal.ofReal (3/K) + ENNReal.ofReal (K/τ)*(∫⁻ w, ENNReal.ofReal (collision (ξ w) (ξ w) R) ∂m) := by
  let ν (w : Ω) := unitLaw.map (f w)
  have mf (w : Ω) : Measurable (f w) := hf.of_uncurry_left
  have prob (w : Ω) : IsProbabilityMeasure (ν w) := Measure.isProbabilityMeasure_map (mf w).aemeasurable
  have hbd (w : Ω) : ξ w univ ≤ 1 := (dom w univ).trans_eq (measure_univ (μ:=ν w))
  have fin (w : Ω) : IsFiniteMeasure (ξ w) := ⟨(hbd w).trans_lt ENNReal.one_lt_top⟩
  let E := {z : Ω × ℝ | ENNReal.ofReal τ < (ν z.1) (Icc (f z.1 z.2-R) (f z.1 z.2+R))}
  let D := {v : (Ω × ℝ) × ℝ | f v.1.1 v.1.2-R ≤ f v.1.1 v.2 ∧ f v.1.1 v.2 ≤ f v.1.1 v.1.2+R}
  have mD : MeasurableSet D := by
    have a : Measurable (fun v : (Ω × ℝ) × ℝ ↦ f v.1.1 v.1.2) := hf.comp measurable_fst
    have b : Measurable (fun v : (Ω × ℝ) × ℝ ↦ f v.1.1 v.2) := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (measurableSet_le (a.sub measurable_const) b).inter (measurableSet_le b (a.add measurable_const))
  have mass (z : Ω × ℝ) : (ν z.1) (Icc (f z.1 z.2-R) (f z.1 z.2+R)) = unitLaw (Prod.mk z ⁻¹' D) :=
    Measure.map_apply (mf _) measurableSet_Icc
  have mE : MeasurableSet E := by
    change MeasurableSet {z : Ω × ℝ | ENNReal.ofReal τ < (ν z.1) (Icc (f z.1 z.2-R) (f z.1 z.2+R))}
    simp_rw [mass];exact measurableSet_lt measurable_const (measurable_measure_prodMk_left mD)
  let B (w : Ω) := {y : ℝ | τ < (ν w).real (Icc (y-R) (y+R))}
  have mB (w : Ω) : MeasurableSet (B w) := by
    let S := {q : ℝ × ℝ | q.1-R ≤ q.2 ∧ q.2 ≤ q.1+R}
    have mS : MeasurableSet S := (measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add measurable_const))
    apply measurableSet_lt measurable_const
    exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left (ν:=ν w) mS)
  have slice (w : Ω) : unitLaw (Prod.mk w ⁻¹' E) = ν w (B w) := by
    rw [show ν w=unitLaw.map (f w) from rfl,Measure.map_apply (mf w) (mB w)];congr 1;ext x
    change ENNReal.ofReal τ < ν w _ ↔ τ < (ν w _).toReal
    exact (ENNReal.ofReal_lt_iff_lt_toReal hτ.le (measure_ne_top _ _))
  have bound (w : Ω) : unitLaw (Prod.mk w ⁻¹' E) ≤ (1-ξ w univ)+ENNReal.ofReal (3/K)+ENNReal.ofReal (K/τ)*ENNReal.ofReal (collision (ξ w) (ξ w) R) := by
    have wbd := fullBallFromRetainedCollisions (ν w) (ξ w) (dom w) hR hτ hK
    have h1 : (ξ w).real univ ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hbd w)
    rw [slice,←ofReal_measureReal (measure_ne_top _ _)]
    apply (ENNReal.ofReal_le_ofReal wbd).trans_eq
    rw [ENNReal.ofReal_add (by linarith [div_nonneg (by norm_num : (0:ℝ)≤3) (zero_lt_one.trans hK).le]) (mul_nonneg (div_nonneg (zero_lt_one.trans hK).le hτ.le) measureReal_nonneg),
      ENNReal.ofReal_add (sub_nonneg.mpr h1) (div_nonneg (by norm_num) (zero_lt_one.trans hK).le),ENNReal.ofReal_mul (div_nonneg (zero_lt_one.trans hK).le hτ.le),ENNReal.ofReal_sub _ measureReal_nonneg,
      ofReal_measureReal (measure_ne_top _ _),ENNReal.ofReal_one]
    rfl
  change (m.prod unitLaw) E ≤ _
  rw [Measure.prod_apply mE]
  apply (lintegral_mono bound).trans_eq
  have m1 := (measurable_diagonal_collision ξ hξ hbd R)
  have m2 : Measurable (fun w => ENNReal.ofReal (K/τ)*ENNReal.ofReal (collision (ξ w) (ξ w) R)) := measurable_const.mul m1
  rw [lintegral_add_right _ m2,lintegral_add_right _ (measurable_const (a:=ENNReal.ofReal (3/K))),
    lintegral_const,measure_univ,mul_one,lintegral_const_mul _ m1]

end Weierstrass.Predecessor
