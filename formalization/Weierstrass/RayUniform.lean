module

public import Weierstrass.RayIsolation

/-! Uniform small-band bounds for compact sets of nondegenerate harmonic profiles. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem coord_cont (j : ℤ) : Continuous (fun z : PhaseTorus ↦ coord z j) :=
  continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp (continuous_apply j))

theorem symmetricSeries_continuous {X : Type*} [TopologicalSpace X]
    (a : X → ℤ → ℂ) (ac : ∀ j, Continuous (fun x ↦ a x j))
    {W : ℤ → ℝ} (sw : Summable W) (bd : ∀ x j, ‖a x j‖ ≤ W j) :
    Continuous (fun u : X × PhaseTorus ↦ symmetricSeries (a u.1) u.2) := by
  change Continuous (fun u : X × PhaseTorus ↦ ∑' j, _)
  refine continuous_tsum (u:=fun j ↦ 2*W j) ?_ (sw.mul_left 2) ?_
  · intro j
    have p := ((ac j).comp continuous_fst).mul ((coord_cont j).comp continuous_snd)
    exact p.add (Complex.continuous_conj.comp p)
  · intro j x
    apply (norm_add_le _ _).trans
    simp only [norm_conj,norm_mul,norm_coord,mul_one,two_mul]
    exact add_le_add (bd _ _) (bd _ _)

/-- Nondecay at infinitely many positive indices excludes every atom. -/
theorem null_level_of_frequent {B : ℂ} {Q M δ : ℝ} (hb : 1 < ‖B‖)
    (hQ : 0 < Q) (hQ' : Q < 1) (hQb : 1 < Q*‖B‖) (hδ : 0 < δ)
    (a : ℤ → ℂ) (ha : Summable fun j ↦ ‖a j‖) (bd : ∀ j, ‖a j‖ ≤ M*Q^j)
    (good : ∃ᶠ n : ℕ in atTop, δ*Q^n ≤ ‖a n‖)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    [μ.InnerRegularCompactLTTop] (v : ℂ) :
    μ {z | symmetricSeries a z.val = v} = 0 := by
  classical
  let E := {z : complexPhaseGroup B | symmetricSeries a z.val = v}
  have cont : Continuous (fun z : complexPhaseGroup B ↦ symmetricSeries a z.val) :=
    (symmetricSeries_continuous (X:=Unit) (fun _ ↦ a) (fun _ ↦ continuous_const)
        ha (fun _ _ ↦ le_rfl)).comp ((continuous_const (y:=())).prodMk continuous_subtype_val)
  have hm : MeasurableSet E := (isClosed_eq cont continuous_const).measurableSet
  by_contra nonzero
  have pos : 0 < μ.real E :=
    (measureReal_nonneg).lt_of_ne' ((measureReal_ne_zero_iff (measure_ne_top μ E)).mpr nonzero)
  have decay := coefficient_decay_on_level hb hQ hQ' hQb a ha bd μ hm pos (fun _ h ↦ h)
  have small := (tendsto_zero_iff_norm_tendsto_zero.mp decay).eventually_lt_const hδ
  obtain ⟨n,large,small⟩ := (good.and_eventually small).exists
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ] at small
  exact (not_lt_of_ge large) ((div_lt_iff₀ (pow_pos hQ n)).mp small)

/-- Passage to uniformity, allowing all compact parameters to move with the
radius. Only a null level for each limiting member is required. -/
theorem uniform_shrinking_level {X Z : Type*} [TopologicalSpace X] [SeqCompactSpace X]
    [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (F : X → Z → ℂ) (meas : ∀ x, Measurable (F x))
    (cont : ∀ z, Continuous (fun x ↦ F x z)) (nul : ∀ x, μ {z | F x z = 0} = 0)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x, μ.real {z | ‖F x z‖ ≤ r n} < ε := by
  classical
  by_contra! bad
  obtain ⟨g,inc,hg⟩ := extraction_of_frequently_atTop bad
  choose x hx using hg
  obtain ⟨a,k,hk,hak⟩ := SeqCompactSpace.tendsto_subseq x
  let A (i : ℕ) := {z | ‖F (x (k i)) z‖ ≤ r (g (k i))}
  have mA (i : ℕ) : MeasurableSet (A i) := measurableSet_le (meas _).norm measurable_const
  let f (i : ℕ) := (A i).indicator (fun _ : Z ↦ (1:ℝ))
  have full : ∀ᵐ z ∂μ, F a z ≠ 0 := by
    apply ae_iff.mpr
    simpa using nul a
  have cv : ∀ᵐ z ∂μ, Tendsto (fun i ↦ f i z) atTop (𝓝 0) := by
    filter_upwards [full] with z h
    have hf := (cont z).continuousAt.tendsto.comp hak
    have small := (hr.comp (inc.tendsto_atTop.comp hk.tendsto_atTop)).eventually_lt
        hf.norm (norm_pos_iff.mpr h)
    apply tendsto_const_nhds.congr'
    filter_upwards [small] with i hi
    have hz : z ∉ A i := not_le.mpr hi
    simp [f,hz]
  have le (i : ℕ) (z : Z) : ‖f i z‖ ≤ 1 := by by_cases h : z ∈ A i <;> simp [f,h]
  have limit := tendsto_integral_filter_of_norm_le_const (μ:=μ) (F:=f)
    (.of_forall fun i ↦ (measurable_const.indicator (mA i)).aestronglyMeasurable)
    ⟨1,.of_forall fun i ↦ .of_forall (le i)⟩ cv
  simp only [integral_zero,f,integral_indicator_const _ (mA _),smul_eq_mul,mul_one] at limit
  obtain ⟨i,hi⟩ := (limit.eventually_lt_const he).exists
  exact (not_lt_of_ge (hx (k i))) hi

end Weierstrass.RaySeed
