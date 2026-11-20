module

public import Weierstrass.RayProof
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Harmonic isolation on the physical phase group in the half-exponent
initialization. Small translations in Haar measure localize the Fourier test
on the entire zero set, even when it has no interior. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate symmDiff
namespace Weierstrass.RaySeed

section Group
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] [μ.InnerRegularCompactLTTop]

private def switchSet (E : Set G) (v : G) : Set G := ((fun z ↦ v+z) ⁻¹' E) ∆ E

omit [CompactSpace G] in
private theorem switch_meas {E : Set G} (hm : MeasurableSet E) (v : G) :
    MeasurableSet (switchSet E v) := (hm.preimage (measurable_const_add v)).symmDiff hm

theorem translated_set_continuity {E : Set G} (hm : MeasurableSet E) {v : ℕ → G}
    (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n ↦ μ.real (((fun z ↦ v n+z) ⁻¹' E) ∆ E)) atTop (𝓝 0) := by
  let T (s : G) : C(G,G) := ⟨fun z ↦ s+z,continuous_const.add continuous_id⟩
  have cont : Continuous T := ContinuousMap.continuous_of_continuous_uncurry _ continuous_add
  have lim := tendsto_measure_symmDiff_preimage_nhds_zero (μ:=μ) (ν:=μ)
    (cont.continuousAt.tendsto.comp hv)
    (Eventually.of_forall fun n ↦ (show MeasurePreserving (T (v n)) μ μ from measurePreserving_add_left μ _))
    (show MeasurePreserving (T 0) μ μ from measurePreserving_add_left μ _)
    hm.nullMeasurableSet (measure_ne_top _ _)
  have val := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp lim
  simpa only [T,Function.comp_apply,ContinuousMap.coe_mk,zero_add,preimage_id_eq,
    ENNReal.toReal_zero,measureReal_def,Function.comp_def,show (fun z : G ↦ z) ⁻¹' E = E from rfl] using val

/-- Riemann--Lebesgue cancellation on any measurable portion of Haar space
for bounded test functions inverted by a translation tending to the identity. -/
theorem cancel_on_set {E : Set G} (hm : MeasurableSet E) (χ : ℕ → G → ℂ) (v : ℕ → G)
    (hv : Tendsto v atTop (𝓝 0)) (cm : ∀ n, Measurable (χ n))
    (bound : ∀ n x, ‖χ n x‖ ≤ 1) (flip : ∀ n x, χ n (v n+x) = -χ n x) :
    Tendsto (fun n ↦ ∫ x in E, χ n x ∂μ) atTop (𝓝 0) := by
  classical
  have decay := translated_set_continuity μ hm hv
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ decay
  intro n
  let f := E.indicator (χ n)
  let g (x : G) := f (v n+x)
  let A := switchSet E (v n)
  have mf : Measurable f := (cm n).indicator hm
  have bf (x : G) : ‖f x‖ ≤ 1 := by
    by_cases hx : x ∈ E <;> simp [f,hx,bound]
  have intf : Integrable f μ := Integrable.of_bound mf.aestronglyMeasurable 1 (.of_forall bf)
  have intg : Integrable g μ := Integrable.of_bound
    (mf.comp (measurable_const_add _)).aestronglyMeasurable 1 (.of_forall fun x ↦ bf _)
  have hg : ∫ x, g x ∂μ = ∫ x, f x ∂μ := integral_add_left_eq_self f _
  have point (x : G) : ‖f x+g x‖ ≤ A.indicator (fun _ ↦ (1:ℝ)) x := by
    by_cases p : x ∈ E <;> by_cases q : v n+x ∈ E <;>
      simp [g,f,A,switchSet,Set.mem_symmDiff,p,q,flip,bound]
  have total := norm_integral_le_of_norm_le ((integrable_const (μ:=μ) (1:ℝ)).indicator (switch_meas hm _))
    (.of_forall point)
  rw [integral_add intf intg,hg,←two_mul,norm_mul,integral_indicator_const (1:ℝ) (switch_meas hm _),smul_eq_mul,mul_one] at total
  have norm2 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [norm2] at total
  have val : (∫ x, f x ∂μ) = ∫ x in E, χ n x ∂μ := integral_indicator hm
  rw [val] at total
  change _ ≤ μ.real A
  linarith only [total,norm_nonneg (∫ x in E, χ n x ∂μ)]

/-- A bounded normalized increment, which vanishes whenever both the original
and the translated point lie in E, tends to zero in integral on E. -/
theorem localized_increment_vanishes {E : Set G} (hm : MeasurableSet E)
    (v : ℕ → G) (hv : Tendsto v atTop (𝓝 0)) (f : ℕ → G → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (bd : ∀ n x, ‖f n x‖ ≤ M)
    (zero : ∀ n x, x ∈ E → v n+x ∈ E → f n x = 0) :
    Tendsto (fun n ↦ ∫ x in E, f n x ∂μ) atTop (𝓝 0) := by
  classical
  have cv := (translated_set_continuity μ hm hv).const_mul M
  rw [mul_zero] at cv
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ cv
  intro n
  let A := switchSet E (v n)
  have mA := switch_meas hm (v n)
  rw [←integral_indicator hm]
  have h := norm_integral_le_of_norm_le ((integrable_const (μ:=μ) M).indicator mA) (f:=E.indicator (f n))
  have point (x : G) : ‖E.indicator (f n) x‖ ≤ A.indicator (fun _ ↦ M) x := by
    by_cases p : x ∈ E <;> by_cases q : v n+x ∈ E <;>
      simp [A,switchSet,Set.mem_symmDiff,p,q,zero,bd,hM]
  have H := h (.of_forall point)
  rw [integral_indicator_const M mA,smul_eq_mul,mul_comm] at H
  exact H

end Group

local instance borelGroup (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def orbitPoint (B v : ℂ) : complexPhaseGroup B :=
  ⟨complexPhaseOrbit B v,(complexPhaseOrbit B).range.le_topologicalClosure ⟨v,rfl⟩⟩

private theorem continuous_orbitPoint (B : ℂ) : Continuous (orbitPoint B) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous (fun x : ℂ ↦ (↑((B^j*x).re) : AddCircle (1:ℝ)))
  exact continuous_quotient_mk'.comp (Complex.continuous_re.comp (continuous_const.mul continuous_id))

def halfOrbit (B A : ℂ) (n : ℕ) : complexPhaseGroup B :=
  orbitPoint B ((B⁻¹)^n*((1/2)/A))

theorem halfOrbit_tendsto {B : ℂ} (hb : 1 < ‖B‖) (A : ℂ) :
    Tendsto (halfOrbit B A) atTop (𝓝 0) := by
  have hi : ‖B⁻¹‖ < 1 := by simpa only [norm_inv] using inv_lt_one_of_one_lt₀ hb
  have cv := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hi).mul_const ((1/2)/A)
  have p := (continuous_orbitPoint B).continuousAt.tendsto.comp cv
  have atzero : orbitPoint B (0*((1/2)/A)) = 0 := by
    apply Subtype.ext
    change complexPhaseOrbit B (0*((1/2)/A)) = _
    rw [zero_mul,map_zero]; rfl
  change Tendsto (fun n : ℕ ↦ orbitPoint B ((B⁻¹)^n*((1/2)/A))) atTop (𝓝 0)
  simpa only [Function.comp_def,atzero] using p

def turn (z : UnitAddCircle) : ℂ := AddCircle.toCircle z

theorem turn_half : turn (↑(1/2:ℝ)) = -1 := by
  have e := fourier_coe_apply (T:=(1:ℝ)) (n:=1) (x:=1/2)
  simp only [fourier_apply,one_zsmul] at e
  change (AddCircle.toCircle (↑(1/2:ℝ)) : ℂ) = _
  rw [e]
  convert Complex.exp_pi_mul_I using 2
  push_cast
  ring

def relativeAngle {B : ℂ} (s j : ℤ) (n : ℕ) (z : complexPhaseGroup B) : UnitAddCircle :=
  s • z.val ((n:ℤ)+j) - z.val (n:ℤ)

private lemma relative_add {B : ℂ} (s j : ℤ) (n : ℕ) (v z : complexPhaseGroup B) :
    relativeAngle s j n (v+z) = relativeAngle s j n v+relativeAngle s j n z := by
  simp [relativeAngle,smul_add,sub_eq_add_neg,add_comm,add_left_comm,add_assoc]

private lemma relative_half {B : ℂ} (hB : B ≠ 0) (s j : ℤ) (n : ℕ)
    (ne : (s:ℂ)*B^j-1 ≠ 0) :
    relativeAngle s j n (halfOrbit B ((s:ℂ)*B^j-1) n) = ↑(1/2:ℝ) := by
  let A := (s:ℂ)*B^j-1
  let x := (B⁻¹)^n*((1/2)/A)
  change s • (↑((B^((n:ℤ)+j)*x).re) : UnitAddCircle) - ↑((B^(n:ℤ)*x).re) = _
  rw [← AddCircle.coe_zsmul,← AddCircle.coe_sub]
  congr 1
  have eq : (s:ℂ)*(B^((n:ℤ)+j)*x)-(B^(n:ℤ)*x) = 1/2 := by
    rw [zpow_add₀ hB,zpow_natCast]
    have bn : B^n ≠ 0 := pow_ne_zero _ hB
    dsimp [x,A]
    rw [inv_pow]
    field_simp
  simpa [zsmul_eq_mul] using congrArg Complex.re eq

/-- All nonresonant components of a modulated bilateral harmonic vanish when
tested on an arbitrary measurable portion of one Haar coset. -/
theorem relative_coefficient_vanishes {B : ℂ} (hb : 1 < ‖B‖)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    [μ.InnerRegularCompactLTTop] {E : Set (complexPhaseGroup B)} (hm : MeasurableSet E)
    (s j : ℤ) (jne : (s:ℂ)*B^j-1 ≠ 0) :
    Tendsto (fun n ↦ ∫ z in E, turn (relativeAngle s j n z) ∂μ) atTop (𝓝 0) := by
  let v := halfOrbit B ((s:ℂ)*B^j-1)
  apply cancel_on_set μ hm _ v (halfOrbit_tendsto hb _)
  · intro n
    apply Continuous.measurable
    unfold turn relativeAngle
    apply continuous_subtype_val.comp
    apply AddCircle.continuous_toCircle.comp
    exact (((continuous_zsmul s).comp ((continuous_apply _).comp continuous_subtype_val)).sub
      ((continuous_apply _).comp continuous_subtype_val))
  · intro n x
    exact (Circle.norm_coe _).le
  · intro n x
    rw [relative_add,show relativeAngle s j n (v n) = ↑(1/2:ℝ) from
      relative_half (norm_pos_iff.mp (zero_lt_one.trans hb)) s j n jne]
    change (↑(AddCircle.toCircle _) : ℂ) = -_
    rw [AddCircle.toCircle_add]
    change turn (↑(1/2:ℝ))*turn (relativeAngle s j n x) = _
    rw [turn_half,neg_one_mul]

end Weierstrass.RaySeed
