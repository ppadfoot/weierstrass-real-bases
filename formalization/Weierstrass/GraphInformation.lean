module

public import Weierstrass.Anchored
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Conditional likelihoods on nested countable labels in Appendix A -/

@[expose] public noncomputable section
open Filter MeasureTheory Set Function
open scoped ENNReal BigOperators Topology

namespace Weierstrass.GraphInformation

variable {Ω H Z : Type*} [MeasurableSpace Ω] [Countable H] [Countable Z]

private theorem lintegral_labels (μ : Measure Ω) (label : Ω → H)
    (hm : ∀ h, MeasurableSet {x | label x = h}) (v : H → ℝ≥0∞) :
    ∫⁻ x, v (label x) ∂μ = ∑' h, v h * μ {x | label x = h} := by
  let A (h : H) := {x | label x = h}
  have cover : (⋃ h, A h) = univ := iUnion_eq_univ_iff.mpr (fun x ↦ ⟨label x, rfl⟩)
  have disj : Pairwise (Disjoint on A) := by
    intro h j hj
    exact disjoint_left.mpr (fun _ he hf ↦ hj (he.symm.trans hf))
  have split := lintegral_iUnion (μ := μ) hm disj (fun x ↦ v (label x))
  rw [cover, Measure.restrict_univ] at split
  rw [split]
  apply tsum_congr
  intro h
  rw [setLIntegral_congr_fun (hm h) (g := fun _ ↦ v h) (fun x hx ↦ congrArg v hx)]
  simp

/-- On an atom with past label h and next label z this is p(z|h)/r(z|h),
where r is the true conditional law. Values on null atoms make no contribution. -/
def likelihoodRatio (μ : Measure Ω) (past : Ω → H) (next : Ω → Z)
    (p : H → Z → ℝ≥0∞) (h : H) (z : Z) : ℝ≥0∞ :=
  p h z * μ {x | past x = h} / μ {x | past x = h ∧ next x = z}

/-- Integrating the ratio against any nonnegative weight determined by the
past contracts the integral, including in the presence of zero-mass labels. -/
theorem likelihood_step (μ : Measure Ω) [IsFiniteMeasure μ]
    (past : Ω → H) (next : Ω → Z) (p : H → Z → ℝ≥0∞)
    (hpast : ∀ h, MeasurableSet {x | past x = h})
    (hnext : ∀ z, MeasurableSet {x | next x = z}) (hp : ∀ h, ∑' z, p h z ≤ 1)
    (w : H → ℝ≥0∞) :
    ∫⁻ x, w (past x) * likelihoodRatio μ past next p (past x) (next x) ∂μ ≤
      ∫⁻ x, w (past x) ∂μ := by
  let A (h : H) := {x | past x = h}
  let C (h : H) (z : Z) := {x | past x = h ∧ next x = z}
  let pair (x : Ω) := (past x, next x)
  have fibre (hj : H × Z) : {x | pair x = hj} = C hj.1 hj.2 := by
    ext x
    exact Prod.ext_iff
  have mPair (hj : H × Z) : MeasurableSet {x | pair x = hj} :=
    fibre hj ▸ (hpast hj.1).inter (hnext hj.2)
  rw [lintegral_labels μ past hpast w]
  change (∫⁻ x, (fun hj : H × Z ↦ w hj.1 * likelihoodRatio μ past next p hj.1 hj.2) (pair x) ∂μ) ≤ _
  rw [lintegral_labels μ pair mPair (fun hj : H × Z ↦ w hj.1 * likelihoodRatio μ past next p hj.1 hj.2)]
  simp only [fibre]
  rw [ENNReal.tsum_prod (f := fun h z ↦ w h * likelihoodRatio μ past next p h z * μ (C h z))]
  apply ENNReal.tsum_le_tsum
  intro h
  calc
    _ ≤ ∑' z, (w h * μ (A h)) * p h z := by
      apply ENNReal.tsum_le_tsum
      intro z
      change w h * (p h z * μ (A h) / μ (C h z)) * μ (C h z) ≤ _
      by_cases hz : μ (C h z) = 0
      · simp [hz]
      rw [mul_assoc, ENNReal.div_mul_cancel hz (measure_ne_top _ _)]
      exact le_of_eq (by ac_rfl)
    _ = (w h * μ (A h)) * ∑' z, p h z := ENNReal.tsum_mul_left
    _ ≤ w h * μ (A h) := mul_le_of_le_one_right zero_le (hp h)

/-- Each new past label determines the preceding past label and its realized
successor. This is exactly the refinement used for the moving partitions.
The product of all realized likelihood ratios has expectation at most one. -/
theorem likelihood_product (μ : Measure Ω) [IsProbabilityMeasure μ]
    (past : ℕ → Ω → H) (next : ℕ → Ω → Z) (p : ℕ → H → Z → ℝ≥0∞)
    (hpast : ∀ i h, MeasurableSet {x | past i x = h})
    (hnext : ∀ i z, MeasurableSet {x | next i x = z}) (hp : ∀ i h, ∑' z, p i h z ≤ 1)
    (refines : ∀ i, ∃ back : H → H × Z, ∀ x, back (past (i+1) x) = (past i x, next i x))
    (m : ℕ) :
    ∫⁻ x, ∏ i ∈ Finset.range m, likelihoodRatio μ (past i) (next i) (p i) (past i x) (next i x) ∂μ
      ≤ 1 := by
  let L i := likelihoodRatio μ (past i) (next i) (p i)
  let W (i : ℕ) (x : Ω) := ∏ j ∈ Finset.range i, L j (past j x) (next j x)
  have factors (i : ℕ) : ∃ w : H → ℝ≥0∞, ∀ x, W i x = w (past i x) := by
    induction i with
    | zero => exact ⟨fun _ ↦ 1, fun x ↦ by simp [W]⟩
    | succ i ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨back, hb⟩ := refines i
      refine ⟨fun h ↦ w (back h).1 * L i (back h).1 (back h).2, fun x ↦ ?_⟩
      dsimp only
      rw [hb]
      change W (i+1) x = w (past i x) * L i (past i x) (next i x)
      rw [← hw]
      exact Finset.prod_range_succ _ _
  change (∫⁻ x, W m x ∂μ) ≤ 1
  induction m with
  | zero => simp [W]
  | succ i ih =>
    obtain ⟨w, hw⟩ := factors i
    have step := likelihood_step μ (past i) (next i) (p i) (hpast i) (hnext i) (hp i) w
    calc
      _ = ∫⁻ x, w (past i x) * L i (past i x) (next i x) ∂μ := by
        apply lintegral_congr
        intro x
        rw [← hw]
        exact Finset.prod_range_succ _ _
      _ ≤ _ := step
      _ = ∫⁻ x, W i x ∂μ := lintegral_congr (fun x ↦ (hw x).symm)
      _ ≤ 1 := ih

/-- Markov and Borel--Cantelli on a triangular array. Taking the geometric
threshold exp(ε) gives the o(K) comparison of information sums. -/
theorem ae_likelihood_subexponential (μ : Measure Ω) (total : ℕ → Ω → ℝ≥0∞)
    (hm : ∀ k, AEMeasurable (total k) μ) (bound : ∀ k, ∫⁻ x, total k x ∂μ ≤ 1)
    {t : ℝ≥0∞} (ht : 1 < t) (htop : t ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, total k x < t^k := by
  let E (k : ℕ) := {x | t^k ≤ total k x}
  have h0 := (zero_lt_one.trans ht).ne'
  have tail (k : ℕ) : μ (E k) ≤ t⁻¹^k := by
    calc
      _ ≤ (∫⁻ x, total k x ∂μ) / t^k :=
        meas_ge_le_lintegral_div (hm k) (pow_ne_zero _ h0) (ENNReal.pow_ne_top htop)
      _ ≤ 1 / t^k := by gcongr; exact bound k
      _ = _ := by rw [one_div, ENNReal.inv_pow]
  have summable : (∑' k : ℕ, t⁻¹^k) ≠ ∞ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr ht)).ne'
  exact (ae_eventually_notMem (ne_top_of_le_ne_top summable (ENNReal.tsum_le_tsum tail))).mono
    (fun _ hx ↦ hx.mono (fun _ hy ↦ lt_of_not_ge hy))

/-- Conditional probability of the next label on a countable partition.
This definition also sets every coordinate of a null row to zero. -/
def conditionalLabelLaw (μ : Measure Ω) (past : Ω → H) (next : Ω → Z) (h : H) (z : Z) : ℝ≥0∞ :=
  μ {x | past x = h ∧ next x = z} / μ {x | past x = h}

omit [Countable H] in
theorem conditionalLabelLaw_sum_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (past : Ω → H) (next : Ω → Z) (hpast : ∀ h, MeasurableSet {x | past x = h})
    (hnext : ∀ z, MeasurableSet {x | next x = z}) (h : H) :
    ∑' z, conditionalLabelLaw μ past next h z ≤ 1 := by
  let E z := {x | past x = h ∧ next x = z}
  let A := {x | past x = h}
  have split : (⋃ z, E z) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨z,hz⟩ := mem_iUnion.mp hx
      exact hz.1
    · intro hx
      exact mem_iUnion.mpr ⟨next x, hx, rfl⟩
  have disj : Pairwise (Disjoint on E) := by
    intro z j hj
    exact disjoint_left.mpr (fun _ hx hy ↦ hj (hx.2.symm.trans hy.2))
  have sum : (∑' z, μ (E z)) = μ A := by
    rw [← measure_iUnion disj (fun z ↦ (hpast h).inter (hnext z)), split]
  change (∑' z, μ (E z) * (μ A)⁻¹) ≤ 1
  rw [ENNReal.tsum_mul_right, sum]
  by_cases ha : μ A = 0
  · simp [ha]
  rw [ENNReal.mul_inv_cancel ha (measure_ne_top μ _)]

/-- A vertical or horizontal dyadic label, with a fixed real origin. -/
def dyadicLabel (k : ℕ) (o x : ℝ) : ℤ := ⌊(2:ℝ)^k * (x-o)⌋

theorem dyadicLabel_parent {k l : ℕ} (hkl : k ≤ l) (o x : ℝ) :
    dyadicLabel l o x / (2:ℤ)^(l-k) = dyadicLabel k o x := by
  have decomp : 2^(l-k) * ((2:ℝ)^k*(x-o)) = 2^l * (x-o) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hkl]
  have eq := Int.cast_mul_floor_div_cancel_of_pos (R := ℝ) (n := (2:ℤ)^(l-k))
    (by positivity) ((2:ℝ)^k*(x-o))
  simpa only [dyadicLabel, Int.cast_pow, Int.cast_ofNat, decomp] using eq

private theorem measurable_dyadic_fiber {f : Ω → ℝ} (hf : Measurable f)
    (k : ℕ) (o : ℝ) (j : ℤ) : MeasurableSet {x | dyadicLabel k o (f x) = j} := by
  have h : Measurable (fun x ↦ (2:ℝ)^k * (f x-o)) := measurable_const.mul (hf.sub measurable_const)
  have equal : {x | dyadicLabel k o (f x) = j} =
      (fun x ↦ (2:ℝ)^k * (f x-o)) ⁻¹' Ico (j:ℝ) (j+1) := by
    ext x
    exact Int.floor_eq_iff
  exact equal ▸ h measurableSet_Ico

/-- The likelihood estimate specialized to the two moving graph labels.
The predictor uses the fixed target horizontal depth K and the current
vertical label. The denominator uses the finer, current horizontal depth. -/
private theorem moving_dyadic_likelihood_aux (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (u T : ℝ) (K : ℕ) (k j : ℕ → ℕ)
    (hk : ∀ i, k i ≤ k (i+1)) (hj : ∀ i, j i ≤ j (i+1)) (m : ℕ) :
    let past i := fun x ↦ (dyadicLabel (k i) u (X x), dyadicLabel (j i) T (Y x))
    let target i := fun x ↦ (dyadicLabel K u (X x), dyadicLabel (j i) T (Y x))
    let next i := fun x ↦ dyadicLabel (j (i+1)) T (Y x)
    let predict i := fun h : ℤ × ℤ ↦ conditionalLabelLaw μ (target i) (next i)
      (h.1 / (2:ℤ)^(k i-K), h.2)
    (∫⁻ x, ∏ i ∈ Finset.range m,
      likelihoodRatio μ (past i) (next i) (predict i) (past i x) (next i x) ∂μ) ≤ 1 := by
  dsimp only
  let pair (s t : ℕ) (x : Ω) := (dyadicLabel s u (X x), dyadicLabel t T (Y x))
  have mpair (s t : ℕ) (h : ℤ × ℤ) : MeasurableSet {x | pair s t x = h} := by
    have eq : {x | pair s t x = h} =
        {x | dyadicLabel s u (X x) = h.1} ∩ {x | dyadicLabel t T (Y x) = h.2} := by
      ext x
      exact Prod.ext_iff
    rw [eq]
    exact (measurable_dyadic_fiber hX _ _ _).inter (measurable_dyadic_fiber hY _ _ _)
  apply likelihood_product
  · exact fun i ↦ mpair (k i) (j i)
  · exact fun i ↦ measurable_dyadic_fiber hY (j (i+1)) T
  · intro i h
    apply conditionalLabelLaw_sum_le
    · exact mpair K (j i)
    · exact measurable_dyadic_fiber hY (j (i+1)) T
  · intro i
    refine ⟨fun h ↦ ((h.1 / (2:ℤ)^(k (i+1)-k i), h.2 / (2:ℤ)^(j (i+1)-j i)), h.2), ?_⟩
    intro x
    simp only [dyadicLabel_parent (hk i), dyadicLabel_parent (hj i)]

private theorem ae_realized_atom_nonzero (μ : Measure Ω) (F : Ω → H) :
    ∀ᵐ x ∂μ, μ {y | F y = F x} ≠ 0 := by
  have one (h : H) : ∀ᵐ x ∂μ, μ {y | F y = h} = 0 → F x ≠ h := by
    by_cases hn : μ {y | F y = h} = 0
    · have he : ∀ᵐ x ∂μ, F x ≠ h := ae_iff.mpr (by simpa using hn)
      exact he.mono fun _ hx _ ↦ hx
    · exact .of_forall (fun _ hx ↦ (hn hx).elim)
  filter_upwards [ae_all_iff.mpr one] with x hx
  exact fun hn ↦ hx (F x) hn rfl

/-- The product of the actual coarse-to-fine conditional probabilities has
mean at most one, with the current horizontal depths at or above the fixed
target depth. Both coordinate variables may have atoms. -/
theorem moving_dyadic_likelihood (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (u T : ℝ) (K : ℕ) (k j : ℕ → ℕ)
    (hK : ∀ i, K ≤ k i) (hk : ∀ i, k i ≤ k (i+1)) (hj : ∀ i, j i ≤ j (i+1)) (m : ℕ) :
    let past i := fun x ↦ (dyadicLabel (k i) u (X x), dyadicLabel (j i) T (Y x))
    let target i := fun x ↦ (dyadicLabel K u (X x), dyadicLabel (j i) T (Y x))
    let next i := fun x ↦ dyadicLabel (j (i+1)) T (Y x)
    (∫⁻ x, ∏ i ∈ Finset.range m,
      conditionalLabelLaw μ (target i) (next i) (target i x) (next i x) /
      conditionalLabelLaw μ (past i) (next i) (past i x) (next i x) ∂μ) ≤ 1 := by
  dsimp only
  let past i (x : Ω) := (dyadicLabel (k i) u (X x), dyadicLabel (j i) T (Y x))
  let target i (x : Ω) := (dyadicLabel K u (X x), dyadicLabel (j i) T (Y x))
  let next i (x : Ω) := dyadicLabel (j (i+1)) T (Y x)
  let predict i (h : ℤ × ℤ) := conditionalLabelLaw μ (target i) (next i)
    (h.1 / (2:ℤ)^(k i-K), h.2)
  have aux := moving_dyadic_likelihood_aux μ X Y hX hY u T K k j hk hj m
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) aux
  filter_upwards [ae_all_iff.mpr (fun i ↦ ae_realized_atom_nonzero μ (past i))] with x hx
  apply Finset.prod_congr rfl
  intro i _
  have hp : predict i (past i x) =
      conditionalLabelLaw μ (target i) (next i) (target i x) := by
    dsimp [predict, past, target]
    rw [dyadicLabel_parent (hK i)]
  change _ = likelihoodRatio μ (past i) (next i) (predict i) (past i x) (next i x)
  rw [likelihoodRatio, hp]
  change _ / (_ / μ {y | past i y = past i x}) = _
  rw [div_eq_mul_inv, ENNReal.inv_div (.inl (measure_ne_top μ _)) (.inl (hx i))]
  simp only [div_eq_mul_inv, mul_assoc]
  rfl

/-- Conditional fine-label mass on a horizontal cell, in the physical graph
coordinates. This is the hard-cutoff version of (G2), before taking minus log.
The estimate is uniform in the position of both cells, in x and in the phases. -/
theorem fine_cell_occupation {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (phase : ℤ → ℝ) (x a R v S : ℝ),
      (b^n)⁻¹ / 2 ≤ R → R ≤ (b^n)⁻¹ → S ≤ 2 * lam^(n+q) →
      x ∈ Icc a (a+R) → series b lam (fun j : ℕ ↦ phase j) x ∈ Icc v (v+S) →
      volume {y : ℝ | y ∈ Icc a (a+R) ∧ series b lam (fun j : ℕ ↦ phase j) y ∈ Icc v (v+S)} /
        ENNReal.ofReal R ≤ 2 * volume {u : ℝ | u ∈ Icc (-1) 1 ∧
          |circleIncrement b lam (fun i ↦ ↑(environment b phase n x i)) u| ≤ 3 * lam^q} := by
  have hb₀ := zero_lt_one.trans hb
  have hl₀ := (inv_pos.mpr hb₀).trans hl
  let g := (b*lam)⁻¹
  have hg : 0 < g := inv_pos.mpr (mul_pos hb₀ hl₀)
  have hg₁ : g < 1 := inv_lt_one_of_one_lt₀ ((inv_lt_iff_one_lt_mul₀' hb₀).mp hl)
  have small : Tendsto (fun n : ℕ ↦ 2*Real.pi * g^(n+1) * (1-g)⁻¹) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hg₁
    simpa only [pow_succ, mul_zero, zero_mul] using ((h.mul_const g).const_mul (2*Real.pi)).mul_const (1-g)⁻¹
  filter_upwards [small.eventually (eventually_lt_nhds (pow_pos hl₀ q))] with n hn
  intro phase x a R v S low high Sbound hx hxv
  let W := series b lam (fun j : ℕ ↦ phase j)
  let E := {u : ℝ | u ∈ Icc (-1) 1 ∧ |circleIncrement b lam
    (fun i ↦ ↑(environment b phase n x i)) u| ≤ 3 * lam^q}
  have bn := pow_pos hb₀ n
  have ln := pow_pos hl₀ n
  have Rpos : 0 < R := (half_pos (inv_pos.mpr bn)).trans_le low
  apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr Rpos).ne' ENNReal.ofReal_ne_top).mpr
  have sub : {y : ℝ | y ∈ Icc a (a+R) ∧ W y ∈ Icc v (v+S)} ⊆
      (fun y : ℝ ↦ (-x)+y) ⁻¹' ((fun t : ℝ ↦ b^n*t) ⁻¹' E) := by
    intro y hy
    let u := b^n*((-x)+y)
    obtain ⟨hyh, hyv⟩ := hy
    have diff : |(-x)+y| ≤ R := abs_le.mpr ⟨by linarith [hx.2, hyh.1], by linarith [hyh.2,hx.1]⟩
    have hu : |u| ≤ 1 := by
      dsimp [u]
      rw [abs_mul, abs_of_pos bn]
      exact (mul_le_mul_of_nonneg_left (diff.trans high) bn.le).trans_eq (mul_inv_cancel₀ bn.ne')
    have hy' : x+(b^n)⁻¹*u = y := by dsimp [u]; field_simp; ring
    have vertical : |W y-W x| ≤ S := abs_le.mpr
      ⟨by linarith [hxv.2, hyv.1], by linarith [hxv.1, hyv.2]⟩
    have ordin : |(lam^n)⁻¹ * (W y-W x)| ≤ 2*lam^q := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr ln)]
      apply (mul_le_mul_of_nonneg_left (vertical.trans Sbound) (inv_pos.mpr ln).le).trans_eq
      rw [pow_add]; field_simp
    have anchor := circle_increment_comparison hb hl h1 phase n x u hu
    rw [hy'] at anchor
    change |circleIncrement b lam _ u - (lam^n)⁻¹ * (W y-W x)| ≤ _ at anchor
    refine ⟨abs_le.mp hu, ?_⟩
    have tri := abs_sub_le (circleIncrement b lam (fun i ↦ ↑(environment b phase n x i)) u)
      ((lam^n)⁻¹ * (W y-W x)) 0
    simp only [sub_zero] at tri
    change 2*Real.pi*g^(n+1)*(1-g)⁻¹ < lam^q at hn
    linarith only [tri, anchor, hn, ordin]
  calc
    _ ≤ _ := measure_mono sub
    _ = ENNReal.ofReal (b^n)⁻¹ * volume E := by
      rw [measure_preimage_add, Real.volume_preimage_mul_left bn.ne', abs_of_pos (inv_pos.mpr bn)]
    _ ≤ ENNReal.ofReal (2*R) * volume E := by gcongr; linarith
    _ = _  := by
      change ENNReal.ofReal (2*R) * volume E = 2 * volume E * ENNReal.ofReal R
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
      exact mul_right_comm _ _ _

/-- The conditional chain rule on a nested path, including extinct paths.
A target square inside the final path atom therefore has mass at most the
horizontal mass times the product of the vertical conditional probabilities. -/
theorem square_mass_chain (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) (B : ℕ → Set Ω)
    (inside : B 0 ⊆ A) (nested : ∀ i, B (i+1) ⊆ B i) (m : ℕ)
    {Q : Set Ω} (hQ : Q ⊆ B m) :
    μ Q ≤ μ A * ∏ i ∈ Finset.range m, μ (B (i+1)) / μ (B i) := by
  have telescopes (k : ℕ) : μ (B 0) * ∏ i ∈ Finset.range k, μ (B (i+1)) / μ (B i) = μ (B k) := by
    induction k with
    | zero => simp
    | succ i ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, mul_comm]
      exact ENNReal.div_mul_cancel' (fun h ↦ measure_mono_null (nested i) h)
        (fun h ↦ (measure_ne_top μ _ h).elim)
  exact (measure_mono hQ).trans ((telescopes m).symm.le.trans (by gcongr))

/-- Physical form of (G3). Any radius whose Hölder oscillation is at most
the distance of the realized ordinate to both vertical boundaries contributes
an interval of at least that length inside the horizontal cell. -/
theorem coarse_cell_mass {f : ℝ → ℝ} {a v x R S C α δ : ℝ}
    (hold : ∀ y z, |y-z| ≤ 1 → |f y-f z| ≤ C * |y-z|^α)
    (hC : 0 < C) (hα : 0 < α) (hδ : 0 < δ) (hδR : δ ≤ R) (hδ1 : δ ≤ 1)
    (hx : x ∈ Icc a (a+R)) (hbot : C*δ^α ≤ f x-v) (htop : C*δ^α ≤ v+S-f x) :
    ENNReal.ofReal δ ≤ volume {y : ℝ | y ∈ Ico a (a+R) ∧ f y ∈ Ico v (v+S)} := by
  let l := max a (x-δ)
  let u := min (a+R) (x+δ)
  have len : δ ≤ u-l := by
    dsimp [l,u]
    rw [le_sub_iff_add_le, le_min_iff, ← max_add_add_left]
    constructor <;> apply max_le <;> linarith [hx.1,hx.2]
  have sub : Ioo l u ⊆ {y : ℝ | y ∈ Ico a (a+R) ∧ f y ∈ Ico v (v+S)} := by
    intro y hy
    obtain ⟨ya, ylo⟩ := max_lt_iff.mp hy.1
    obtain ⟨yr, yhi⟩ := lt_min_iff.mp hy.2
    have hd : |y-x| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hc := (hold y x (hd.le.trans hδ1)).trans_lt
      (mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (abs_nonneg _) hd hα) hC)
    obtain ⟨hm,hp⟩ := abs_lt.mp hc
    exact ⟨⟨ya.le,yr⟩, ⟨by linarith,by linarith⟩⟩
  exact ((ENNReal.ofReal_le_ofReal len).trans_eq (Real.volume_Ioo.symm)).trans (measure_mono sub)

/-- The coarse conditional mass from (G3), with the precise vertical
position encoded as distance to the nearest integer. A dyadic label of width
S has lower endpoint T+S*floor((f(x)-T)/S). -/
theorem coarse_dyadic_conditional_mass {f : ℝ → ℝ} {C α x a R T S : ℝ}
    (hold : ∀ y z, |y-z| ≤ 1 → |f y-f z| ≤ C * |y-z|^α)
    (hC : 1 ≤ C) (hα : 0 < α) (hR : 0 < R) (hR1 : R ≤ 1) (hscale : R^α ≤ S)
    (hx : x ∈ Icc a (a+R)) (hn : (↑((f x-T)/S) : UnitAddCircle) ≠ 0) :
    let m := ⌊(f x-T)/S⌋
    ENNReal.ofReal ((‖(↑((f x-T)/S) : UnitAddCircle)‖/C)^α⁻¹) ≤
      volume {y | y ∈ Ico a (a+R) ∧ ⌊(f y-T)/S⌋ = m} / ENNReal.ofReal R := by
  let w := (f x-T)/S
  let b := ‖(↑w : UnitAddCircle)‖
  let A := (b/C)^α⁻¹
  let v := T + S*⌊w⌋
  have hC₀ := zero_lt_one.trans_le hC
  have hS := (Real.rpow_pos_of_pos hR α).trans_le hscale
  have bpos : 0 < b := norm_pos_iff.mpr hn
  have b1 : b ≤ 1 := (AddCircle.norm_le_half_period 1 one_ne_zero).trans (by norm_num)
  have Apos : 0 < A := Real.rpow_pos_of_pos (div_pos bpos hC₀) _
  have A1 : A ≤ 1 := Real.rpow_le_one (div_pos bpos hC₀).le
    ((div_le_one hC₀).mpr (b1.trans hC)) (inv_pos.mpr hα).le
  have upper : R*A ≤ R := mul_le_of_le_one_right hR.le A1
  have osc : C * (R*A)^α ≤ S*b := by
    rw [Real.mul_rpow hR.le Apos.le, show A^α = b/C from Real.rpow_inv_rpow (div_pos bpos hC₀).le hα.ne']
    have eq : C*(R^α*(b/C)) = R^α*b := by field_simp
    rw [eq]
    exact mul_le_mul_of_nonneg_right hscale bpos.le
  have near : b ≤ Int.fract w ∧ b ≤ 1-Int.fract w := by
    rw [← le_min_iff, ← abs_sub_round_eq_min, ← UnitAddCircle.norm_eq]
  have wval : S*w = f x-T := by dsimp [w]; field_simp
  have bot : S*b ≤ f x-v := by
    have lower := mul_le_mul_of_nonneg_left near.1 hS.le
    change S*b ≤ S*(w-⌊w⌋) at lower
    dsimp [v]
    linarith only [lower,wval]
  have top : S*b ≤ v+S-f x := by
    have higher := mul_le_mul_of_nonneg_left near.2 hS.le
    change S*b ≤ S*(1-(w-⌊w⌋)) at higher
    dsimp [v]
    linarith only [higher,wval]
  have lower := coarse_cell_mass hold hC₀ hα (mul_pos hR Apos) upper (upper.trans hR1) hx
    (osc.trans bot) (osc.trans top)
  have label : {y | y ∈ Ico a (a+R) ∧ f y ∈ Ico v (v+S)} ⊆
      {y | y ∈ Ico a (a+R) ∧ ⌊(f y-T)/S⌋ = ⌊w⌋} := by
    rintro y ⟨hy, hv⟩
    refine ⟨hy, Int.floor_eq_iff.mpr ⟨(le_div_iff₀ hS).mpr ?_, (div_lt_iff₀ hS).mpr ?_⟩⟩
    · dsimp [v] at hv; linarith [hv.1]
    · dsimp [v] at hv; linarith [hv.2]
  apply (ENNReal.le_div_iff_mul_le (.inl (ENNReal.ofReal_pos.mpr hR).ne')
    (.inl ENNReal.ofReal_ne_top)).mpr
  change ENNReal.ofReal A * ENNReal.ofReal R ≤ _
  rw [← ENNReal.ofReal_mul Apos.le,mul_comm A R]
  exact lower.trans (measure_mono label)

/-- The two coordinate labels of the half-open square containing a point. -/
def squareLabel (k : ℕ) (o z : ℂ) : ℤ × ℤ :=
  (dyadicLabel k o.re z.re, dyadicLabel k o.im z.im)

theorem measurable_squareLabel (k : ℕ) (o : ℂ) : Measurable (squareLabel k o) :=
  (measurable_to_countable' (measurable_dyadic_fiber Complex.continuous_re.measurable k o.re)).prodMk
    (measurable_to_countable' (measurable_dyadic_fiber Complex.continuous_im.measurable k o.im))

private theorem nearby_label {x y : ℝ} (o : ℝ) (k : ℕ) (hxy : |y-x| < ((2:ℝ)^k)⁻¹) :
    ∃ e : Fin 3, dyadicLabel k o y = dyadicLabel k o x + ((e:ℕ):ℤ) - 1 := by
  let L := (2:ℝ)^k
  have hL : 0 < L := pow_pos (by norm_num) _
  have scaled : L*|y-x| < 1 := (mul_lt_mul_of_pos_left hxy hL).trans_eq (mul_inv_cancel₀ hL.ne')
  rw [← abs_of_pos hL, ← abs_mul] at scaled
  obtain ⟨hlo, hhi⟩ := abs_lt.mp scaled
  have hy := Int.floor_mono (show L*(y-o) ≤ L*(x-o)+1 by linarith)
  have hx := Int.floor_mono (show L*(x-o) ≤ L*(y-o)+1 by linarith)
  rw [Int.floor_add_one] at hy hx
  change ∃ e : Fin 3, ⌊L*(y-o)⌋ = ⌊L*(x-o)⌋ + ((e:ℕ):ℤ)-1
  let z := ⌊L*(y-o)⌋-⌊L*(x-o)⌋+1
  exact ⟨⟨z.toNat, by dsimp [z]; omega⟩, by dsimp [z]; omega⟩

/-- Reindexing the labels shows that a cell with an exponentially heavier
specified neighbor has exponentially small total probability. -/
private theorem neighbor_ratio (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℤ × ℤ)
    (hF : Measurable F) (e : ℤ × ℤ ≃ ℤ × ℤ) :
    ∫⁻ x, μ {y | F y = e (F x)} / μ {y | F y = F x} ∂μ ≤ 1 := by
  let m (i : ℤ × ℤ) := μ {y | F y = i}
  have hm (i : ℤ × ℤ) := hF (measurableSet_singleton i)
  have sum : (∑' i, m i) = 1 := by
    have hh := lintegral_labels μ F hm (fun _ ↦ 1)
    simpa [m] using hh.symm
  rw [lintegral_labels μ F hm (fun i ↦ m (e i) / m i)]
  apply (ENNReal.tsum_le_tsum (g := fun i ↦ m (e i)) ?_).trans_eq ((e.tsum_eq m).trans sum)
  intro i
  by_cases hz : m i = 0
  · change m (e i) / m i * m i ≤ m (e i)
    simp [hz]
  exact (ENNReal.div_mul_cancel hz (measure_ne_top μ _)).le

/-- At almost every center the ball of dyadic radius is bounded by nine
times the realized square mass times any prescribed exponential loss. -/
theorem ae_ball_le_square (μ : Measure ℂ) [IsProbabilityMeasure μ] (o : ℂ)
    {t : ℝ≥0∞} (ht : 1 < t) (htop : t ≠ ∞) :
    ∀ᵐ z ∂μ, ∀ᶠ k : ℕ in atTop, μ (Metric.ball z ((2:ℝ)^k)⁻¹) ≤
      9 * t^k * μ {y | squareLabel k o y = squareLabel k o z} := by
  let Offset := Fin 3 × Fin 3
  let delta (e : Offset) : ℤ × ℤ := (((e.1:ℕ):ℤ)-1, ((e.2:ℕ):ℤ)-1)
  let F k := squareLabel k o
  let m k (i : ℤ × ℤ) := μ {y | F k y = i}
  have ratios (e : Offset) : ∀ᵐ z ∂μ, ∀ᶠ k : ℕ in atTop,
      m k (F k z + delta e) / m k (F k z) < t^k := by
    apply ae_likelihood_subexponential μ _ _ _ ht htop
    · intro k
      exact ((measurable_of_countable (fun i ↦ m k (i+delta e) / m k i)).comp
        (measurable_squareLabel k o)).aemeasurable
    · intro k
      exact neighbor_ratio μ (F k) (measurable_squareLabel k o) (Equiv.addRight (delta e))
  filter_upwards [ae_all_iff.mpr ratios, ae_all_iff.mpr (fun k ↦ ae_realized_atom_nonzero μ (F k))]
    with z hz hpos
  filter_upwards [Filter.eventually_all.mpr hz] with k hk
  let A (e : Offset) := {y | F k y = F k z + delta e}
  have cover : Metric.ball z ((2:ℝ)^k)⁻¹ ⊆ ⋃ e, A e := by
    intro y hy
    change dist y z < _ at hy
    rw [dist_eq_norm] at hy
    obtain ⟨a,ha⟩ := nearby_label o.re k ((Complex.abs_re_le_norm (y-z)).trans_lt hy)
    obtain ⟨b,hb⟩ := nearby_label o.im k ((Complex.abs_im_le_norm (y-z)).trans_lt hy)
    apply mem_iUnion.mpr
    refine ⟨(a,b), Prod.ext ?_ ?_⟩
    · change dyadicLabel k o.re y.re = dyadicLabel k o.re z.re + (((a:ℕ):ℤ)-1)
      simpa only [add_sub_assoc] using ha
    · change dyadicLabel k o.im y.im = dyadicLabel k o.im z.im + (((b:ℕ):ℤ)-1)
      simpa only [add_sub_assoc] using hb
  calc
    _ ≤ μ (⋃ e, A e) := measure_mono cover
    _ ≤ ∑ e, μ (A e) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Offset, t^k * m k (F k z) := Finset.sum_le_sum fun e _ ↦
      (ENNReal.div_le_iff (hpos k) (measure_ne_top μ _)).mp (hk e).le
    _ = _ := by simp [Offset, m, F, nsmul_eq_mul, mul_assoc]

/-- A dyadic square mass bound at exponent s gives the Euclidean lower
local-dimension bound at each strict exponent d, on all real radii. -/
theorem lower_local_of_dyadic_square_mass (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (o : ℂ) {s d : ℝ} (hd : 0 < d) (hs : d < s)
    (cells : ∀ᵐ z ∂μ, ∀ᶠ k : ℕ in atTop, μ {y | squareLabel k o y = squareLabel k o z} ≤
      ENNReal.ofReal (((1/2:ℝ)^s)^k)) :
    ∀ᵐ z ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      d ≤ Real.log (μ (Metric.ball z r)).toReal / Real.log r := by
  let q : ℝ := 1/2
  have hq : 0 < q := by norm_num [q]
  have hq₁ : q < 1 := by norm_num [q]
  obtain ⟨v, hdv, hvs⟩ := exists_between hs
  have vs : q^s < q^v := Real.rpow_lt_rpow_of_exponent_gt hq hq₁ hvs
  have vd : q^v < q^d := Real.rpow_lt_rpow_of_exponent_gt hq hq₁ hdv
  let t := q^v / q^s
  have ht : 1 < t := (one_lt_div₀ (Real.rpow_pos_of_pos hq _)).mpr vs
  have ht₀ := zero_lt_one.trans ht
  have htE : 1 < ENNReal.ofReal t := by exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr ht
  have compared := ae_ball_le_square μ o htE ENNReal.ofReal_ne_top
  have rho0 : 0 < q^v / q^d := div_pos (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hq _)
  have rho1 : q^v / q^d < 1 := (div_lt_one (Real.rpow_pos_of_pos hq _)).mpr vd
  have decay := tendsto_pow_atTop_nhds_zero_of_lt_one rho0.le rho1
  have absorb : ∀ᶠ n : ℕ in atTop, 9*(q^v)^n ≤ (q^(n+1))^d := by
    filter_upwards [decay.eventually (eventually_lt_nhds (show 0 < q^d/9 by positivity))] with n hn
    rw [div_pow] at hn
    have h := (div_lt_iff₀ (pow_pos (Real.rpow_pos_of_pos hq _) n)).mp hn
    rw [pow_succ, Real.mul_rpow (pow_nonneg hq.le _) hq.le, ← Real.rpow_pow_comm hq.le]
    linarith
  filter_upwards [cells, compared, (show ∀ᵐ z ∂μ, z ∈ μ.support from μ.support_mem_ae)] with z hcell hcompare hz
  have ballmass : ∀ᶠ n : ℕ in atTop, (μ (Metric.ball z (q^n))).toReal ≤ (q^(n+1))^d := by
    filter_upwards [hcell,hcompare,absorb] with n hc hb habs
    have sq : q^n = ((2:ℝ)^n)⁻¹ := by simp [q,one_div]
    rw [← sq] at hb
    apply le_trans _ habs
    have first := ENNReal.toReal_mono (by finiteness) (hb.trans (mul_le_mul_of_nonneg_left hc (zero_le (α := ℝ≥0∞))))
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal ht₀.le, ENNReal.toReal_ofReal (show 0 ≤ (((1/2:ℝ)^s)^n) by positivity)] at first
    apply first.trans_eq
    change 9*t^n*(q^s)^n = 9*(q^v)^n
    dsimp [t]
    rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hq _).ne']
  obtain ⟨N,hN⟩ := eventually_atTop.mp ballmass
  filter_upwards [Ioo_mem_nhdsGT (pow_pos hq N), Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ)<1)] with r hr hr₁
  obtain ⟨n, hnlow, hnhi⟩ := exists_nat_pow_near_of_lt_one hr.1 hr₁.2.le hq hq₁
  have nbig : N ≤ n := by
    by_contra! contra
    have := pow_le_pow_of_le_one hq.le hq₁.le (show n+1 ≤ N by omega)
    linarith [hr.2]
  have massle : (μ (Metric.ball z r)).toReal ≤ r^d := calc
    _ ≤ (μ (Metric.ball z (q^n))).toReal := ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Metric.ball_subset_ball hnhi))
    _ ≤ _ := hN n nbig
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hq.le _) hnlow.le hd.le
  apply (le_div_iff_of_neg (Real.log_neg hr.1 hr₁.2)).mpr
  have masspos := (Measure.mem_support_iff_forall z).mp hz _ (Metric.ball_mem_nhds _ hr.1)
  have h := Real.log_le_log (ENNReal.toReal_pos masspos.ne' (measure_ne_top _ _)) massle
  simpa [Real.log_rpow hr.1,mul_comm] using h

private def maxPrefix (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, x => max (f x + maxPrefix T f n (T x)) 0

omit [MeasurableSpace Ω] in
private theorem maxPrefix_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ maxPrefix T f n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_right _ _

omit [MeasurableSpace Ω] in
private theorem maxPrefix_mono (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    maxPrefix T f n x ≤ maxPrefix T f (n+1) x := by
  induction n generalizing x with
  | zero => exact maxPrefix_nonneg T f 1 x
  | succ n ih => exact max_le_max (add_le_add_right (ih (T x)) _) le_rfl

omit [MeasurableSpace Ω] in
private theorem maxPrefix_dominates (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    (∑ j ∈ Finset.range n, f (T^[j] x)) ≤ maxPrefix T f n x := by
  induction n generalizing x with
  | zero => simp [maxPrefix]
  | succ n ih =>
    have e : (∑ j ∈ Finset.range (n+1), f (T^[j] x)) =
        f x + ∑ j ∈ Finset.range n, f (T^[j] (T x)) :=
      (Finset.sum_range_succ' _ _).trans (add_comm _ _)
    rw [e]
    exact ((add_le_add_right (ih (T x)) _)).trans (le_max_left _ _)

/-- An elementary maximal ergodic estimate sufficient for the boundary
loss in (G3). No ergodicity is required. The constant is common to every
sample size and hence to every later choice of block length. -/
theorem ae_prefix_sum_bounded (μ : Measure Ω) [IsFiniteMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (g : Ω → ℝ) (gm : Measurable g) (gi : Integrable g μ)
    (g0 : ∀ x, 0 ≤ g x) :
    ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ n : ℕ, (∑ j ∈ Finset.range n, g (T^[j] x)) ≤ C*n := by
  let Bad (M : ℝ) := {x | ∃ n : ℕ, M*n < ∑ j ∈ Finset.range n, g (T^[j] x)}
  have weak (M : ℝ) (hM : 0 < M) : μ (Bad M) ≤ ENNReal.ofReal ((∫ x, g x ∂μ)/M) := by
    let f (x : Ω) := g x-M
    let U := maxPrefix T f
    let E (n : ℕ) := {x | 0 < U n x}
    have fi : Integrable f μ := gi.sub (integrable_const M)
    have um (n : ℕ) : Measurable (U n) := by
      induction n with
      | zero => exact measurable_const
      | succ n ih => exact ((gm.sub measurable_const).add (ih.comp hT.measurable)).max measurable_const
    have ui (n : ℕ) : Integrable (U n) μ := by
      induction n with
      | zero => exact integrable_const _
      | succ n ih => exact (fi.add (hT.integrable_comp_of_integrable ih)).pos_part
    have isE n : MeasurableSet (E n) := measurableSet_lt measurable_const (um n)
    have bound (n : ℕ) : μ (E n) ≤ ENNReal.ofReal ((∫ x, g x ∂μ)/M) := by
      have hopf (x : Ω) : U n x - U n (T x) ≤ (E n).indicator f x := by
        by_cases hx : x ∈ E n
        · rw [indicator_of_mem hx]
          cases n with
          | zero => exact (lt_irrefl (0:ℝ) (show 0 < 0 from hx)).elim
          | succ n =>
            change 0 < max (f x + U n (T x)) 0 at hx
            change max (f x + U n (T x)) 0 - U (n+1) (T x) ≤ f x
            rw [max_eq_left ((lt_max_iff.mp hx).resolve_right (lt_irrefl _)).le]
            linarith [show U n (T x) ≤ U (n+1) (T x) from maxPrefix_mono _ _ _ _]
        · rw [indicator_of_notMem hx]
          have hz : U n x ≤ 0 := le_of_not_gt hx
          linarith [show 0 ≤ U n (T x) from maxPrefix_nonneg _ _ _ _]
      have preserve : (∫ x, (U n ∘ T) x ∂μ) = ∫ x, U n x ∂μ := by
        have h := integral_map (μ := μ) hT.measurable.aemeasurable (um n).stronglyMeasurable.aestronglyMeasurable
        simpa only [hT.map_eq, Function.comp_apply] using h.symm
      have pos := integral_mono ((ui n).sub (hT.integrable_comp_of_integrable (ui n)))
        (fi.indicator (isE n)) hopf
      change (∫ x, U n x - (U n ∘ T) x ∂μ) ≤ _ at pos
      rw [integral_sub (ui n) (hT.integrable_comp_of_integrable (ui n)), preserve, sub_self,
        integral_indicator (isE n)] at pos
      change 0 ≤ ∫ x in E n, g x-M ∂μ at pos
      rw [integral_sub gi.integrableOn (integrable_const _), setIntegral_const] at pos
      have gin := setIntegral_le_integral (s := E n) gi (.of_forall g0)
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E n))]
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ hM).mpr
      simp only [smul_eq_mul, measureReal_def] at pos
      linarith
    have inc : Monotone E := monotone_nat_of_le_succ (fun n x hx ↦ hx.trans_le (maxPrefix_mono T f n x))
    apply (measure_mono (t := ⋃ n, E n) ?_).trans
    · rw [inc.measure_iUnion]
      exact iSup_le bound
    · rintro x ⟨n,hn⟩
      refine mem_iUnion.mpr ⟨n, lt_of_lt_of_le ?_ (maxPrefix_dominates T f n x)⟩
      simp only [f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith
  apply ae_iff.mpr
  apply nonpos_iff_eq_zero.mp
  have small : Tendsto (fun k : ℕ ↦ ENNReal.ofReal ((∫ x, g x ∂μ)/(k+1:ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (∫ x, g x ∂μ)
    simpa only [mul_one_div, mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h
  apply ge_of_tendsto small
  apply Filter.Eventually.of_forall
  intro k
  apply (measure_mono (t := Bad (k+1)) ?_).trans (weak _ (by positivity))
  intro x hx
  by_contra h
  exact hx ⟨k+1, fun n ↦ le_of_not_gt (fun hn ↦ h ⟨n,hn⟩)⟩

/-- The squared boundary loss for one random vertical origin is integrable
under the uniform circle law. The value assigned at the single boundary is zero. -/
theorem integrable_log_sq_circle : Integrable (fun z : UnitAddCircle ↦ (Real.log ‖z‖)^2) volume := by
  let r : ℝ := -(1/2)
  have gm : Measurable (fun z : UnitAddCircle ↦ ‖z‖^r) := by fun_prop
  have gi : Integrable (fun z : UnitAddCircle ↦ ‖z‖^r) volume := by
    apply (AddCircle.measurePreserving_mk 1 (-(1/2))).integrable_comp gm.aestronglyMeasurable |>.mp
    have base := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1/2)
      (show -1 < r by norm_num [r])
    have pos : IntervalIntegrable (fun x : ℝ ↦ |x|^r) volume 0 (1/2) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
      exact base.1.congr_fun (fun x hx ↦ by simp [abs_of_pos hx.1]) measurableSet_Ioc
    have neg : IntervalIntegrable (fun x : ℝ ↦ |x|^r) volume (-(1/2)) 0 := by
      rw [IntervalIntegrable.iff_comp_neg]
      simpa only [neg_neg, neg_zero,abs_neg] using pos.symm
    have both := (neg.trans pos).1
    change IntegrableOn _ (Ioc (-(1/2)) (-(1/2)+1)) volume
    rw [show -(1/2:ℝ)+1 = 1/2 by norm_num]
    apply both.congr_fun _ measurableSet_Ioc
    intro x hx
    have hnorm := (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr
      (show |x| ≤ |(1:ℝ)|/2 by rw [abs_one]; exact abs_le.mpr ⟨hx.1.le,hx.2⟩)
    simp only [comp_apply,hnorm]
  apply (gi.const_mul 16).mono' ((Real.measurable_log.comp measurable_norm).pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hb : ‖z‖ ≤ 1 := (AddCircle.norm_le_half_period 1 one_ne_zero).trans (by norm_num)
  have hlog : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hb
  have bound := Real.log_le_rpow_div (inv_nonneg.mpr (norm_nonneg z))
    (show 0 < (1/4:ℝ) by norm_num)
  rw [Real.log_inv, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)] at bound
  have hsq := sq_le_sq' (show -(‖z‖^(-(1/4:ℝ))/(1/4)) ≤ -Real.log ‖z‖ by
    have := Real.rpow_nonneg (norm_nonneg z) (-(1/4:ℝ)); linarith) bound
  have power : (‖z‖^(-(1/4:ℝ)))^2 = ‖z‖^r := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num [r]
  change ‖(Real.log ‖z‖)^2‖ ≤ 16 * ‖z‖^r
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← power]
  nlinarith

private theorem doubling_preserves : MeasurePreserving
    (fun z : UnitAddCircle ↦ (2:ℤ) • z) volume volume := by
  let ν : Measure UnitAddCircle := volume
  let p : UnitAddCircle →+ UnitAddCircle := zsmulAddGroupHom 2
  have pm : Measurable p := by
    change Measurable (fun z : UnitAddCircle ↦ (2:ℤ) • z)
    simp only [two_zsmul]
    exact measurable_id.add measurable_id
  let _ : IsProbabilityMeasure ν := ⟨UnitAddCircle.measure_univ⟩
  let _ : IsProbabilityMeasure (ν.map p) := Measure.isProbabilityMeasure_map pm.aemeasurable
  let _ : Measure.IsAddLeftInvariant (ν.map p) := isAddLeftInvariant_map p.toAddHom pm
    (fun z ↦ ⟨DivisibleBy.div z (2:ℤ), DivisibleBy.div_cancel _ (by norm_num : (2:ℤ) ≠ 0)⟩)
  have normHaar (η : Measure UnitAddCircle) [IsProbabilityMeasure η] [Measure.IsAddLeftInvariant η] :
      Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts UnitAddCircle) = η :=
    (Measure.addHaarMeasure_eq_iff _ _).mpr (by simp)
  change MeasurePreserving p ν ν
  exact ⟨pm,(normHaar (ν.map p)).symm.trans (normHaar ν)⟩

/-- On the unit circle a single conull set bounds every prefix of the
squared logarithmic distances of the doubling orbit to the vertical boundary. -/
theorem ae_doubling_boundary :
    ∀ᵐ z : UnitAddCircle ∂volume, ∃ C : ℝ, ∀ n : ℕ,
      (∑ j ∈ Finset.range n, (Real.log ‖(2:ℤ)^j • z‖)^2) ≤ C*n := by
  have h := ae_prefix_sum_bounded (volume : Measure UnitAddCircle) ((2:ℤ) • ·)
    doubling_preserves _
    ((Real.measurable_log.comp measurable_norm).pow_const 2) integrable_log_sq_circle (fun _ ↦ sq_nonneg _)
  simpa only [smul_iterate_apply, Function.comp_apply] using h

set_option maxHeartbeats 450000 in
/-- Fix one vertical origin simultaneously for almost all inputs, for every
measurable ordinate and finite input measure. Circle norm is the distance
to the vertical boundary in units of the cell width. -/
theorem exists_vertical_origin (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ) (hm : Measurable Y) :
    ∃ T : ℝ, ∀ᵐ x ∂μ,
      (∀ j : ℕ, ((↑((2:ℝ)^j*(Y x-T)) : UnitAddCircle)) ≠ 0) ∧
      ∃ C : ℝ, ∀ n : ℕ,
        (∑ j ∈ Finset.range n, (Real.log ‖(↑((2:ℝ)^j*(Y x-T)) : UnitAddCircle)‖)^2) ≤ C*n := by
  let P (z : UnitAddCircle) := (∀ j : ℕ, (2:ℤ)^j • z ≠ 0) ∧ ∃ C : ℝ, ∀ n : ℕ,
    (∑ j ∈ Finset.range n, (Real.log ‖(2:ℤ)^j • z‖)^2) ≤ C*n
  have avoid0 : ∀ᵐ w : UnitAddCircle ∂volume, w ≠ 0 := by
    apply ae_iff.mpr
    change volume {w : UnitAddCircle | ¬w ≠ 0} = 0
    simp only [not_not, Set.ofPred_eq_eq_singleton]
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    norm_num
  have avoids (j : ℕ) : ∀ᵐ z : UnitAddCircle ∂volume, (2:ℤ)^j • z ≠ 0 := by
    have h := (doubling_preserves.iterate j).quasiMeasurePreserving.ae
      avoid0
    simpa only [smul_iterate_apply] using h
  have good : ∀ᵐ z ∂(volume : Measure UnitAddCircle), P z :=
    (ae_all_iff.mpr avoids).and ae_doubling_boundary
  obtain ⟨N, hN, Nm, Nnull⟩ := exists_measurable_superset_of_null (ae_iff.mp good)
  let c (x : Ω) := (↑(Y x) : UnitAddCircle)
  have cm : Measurable c := AddCircle.measurable_mk'.comp hm
  have a : ∀ᵐ x ∂μ, ∀ᵐ z : UnitAddCircle ∂volume, c x+z ∉ N := by
    apply Filter.Eventually.of_forall
    intro x
    apply ae_iff.mpr
    simp only [not_not]
    exact (measure_preimage_add (volume : Measure UnitAddCircle) (c x) N).trans Nnull
  have flip := (Measure.ae_ae_comm (p := fun x z ↦ c x+z ∉ N)
    (((cm.comp measurable_fst).add measurable_snd) Nm.compl)).mp a
  obtain ⟨z,hz⟩ := flip.exists
  obtain ⟨v,hv⟩ := QuotientAddGroup.mk_surjective z
  refine ⟨-v, hz.mono ?_⟩
  intro x hx
  have pz : P (c x+z) := by exact of_not_not (fun hn ↦ hx (hN hn))
  have convert (j : ℕ) : (↑((2:ℝ)^j*(Y x- -v)) : UnitAddCircle) = (2:ℤ)^j • (c x+z) := by
    rw [← hv, sub_neg_eq_add]
    change (↑((2:ℝ)^j*(Y x+v)) : UnitAddCircle) = (2:ℤ)^j • (↑(Y x)+↑v)
    rw [← AddCircle.coe_add, ← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul,mul_add]
  simpa only [convert] using pz

/-- Probability of the realized vertical label under the realized horizontal cell. -/
def verticalMass (μ : Measure Ω) (X Y : Ω → ℝ) (u T : ℝ) (k j : ℕ) (x : Ω) : ℝ≥0∞ :=
  conditionalLabelLaw μ (fun y ↦ dyadicLabel k u (X y))
    (fun y ↦ dyadicLabel j T (Y y)) (dyadicLabel k u (X x)) (dyadicLabel j T (Y x))

private def horizontal (X : Ω → ℝ) (u : ℝ) (k : ℕ) (x : Ω) := dyadicLabel k u (X x)
private def joint (X Y : Ω → ℝ) (u T : ℝ) (k j : ℕ) (x : Ω) :=
  (dyadicLabel k u (X x), dyadicLabel j T (Y x))
private def atom {D : Type*} (F : Ω → D) (x : Ω) := {y | F y = F x}

omit [MeasurableSpace Ω] in
private theorem pair_child {X Y : Ω → ℝ} {u T : ℝ} {k j j' : ℕ} (hj : j ≤ j') (x : Ω) :
    {y | joint X Y u T k j y = joint X Y u T k j x ∧
      dyadicLabel j' T (Y y) = dyadicLabel j' T (Y x)} = atom (joint X Y u T k j') x := by
  ext y
  simp only [atom, joint, mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨h.1,h'⟩
  · intro h
    have v := h.2
    change dyadicLabel j' T (Y y) = dyadicLabel j' T (Y x) at v
    have v' := congrArg (fun z : ℤ ↦ z / (2:ℤ)^(j'-j)) v
    simp only [dyadicLabel_parent hj] at v'
    exact ⟨⟨h.1,v'⟩,v⟩

private theorem joint_cond_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℝ) (u T : ℝ) {k j j' : ℕ} (hj : j ≤ j') (x : Ω) :
    conditionalLabelLaw μ (joint X Y u T k j) (fun y ↦ dyadicLabel j' T (Y y))
      (joint X Y u T k j x) (dyadicLabel j' T (Y x)) =
        μ (atom (joint X Y u T k j') x) / μ (atom (joint X Y u T k j) x) := by
  rw [conditionalLabelLaw, pair_child hj x]
  rfl

private theorem vert_eq_joint (μ : Measure Ω) (X Y : Ω → ℝ) (u T : ℝ)
    (k j : ℕ) (x : Ω) :
    verticalMass μ X Y u T k j x =
      μ (atom (joint X Y u T k j) x) / μ (atom (horizontal X u k) x) := by
  unfold verticalMass conditionalLabelLaw
  congr 2
  ext y
  simp only [atom, joint, mem_ofPred_eq, Prod.mk.injEq]

/-- The chain rule and the moving dyadic likelihood comparison combined.
The window can depend on K. The right-hand product only involves vertical
masses conditional on a horizontal cell, as estimated by (G2) and (G3). -/
theorem ae_moving_square_product (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (u T : ℝ)
    (k j : ℕ → ℕ → ℕ) (m : ℕ → ℕ) (hK : ∀ K i, K ≤ k K i)
    (hk : ∀ K i, k K i ≤ k K (i+1)) (hj : ∀ K i, j K i ≤ j K (i+1))
    (last : ∀ᶠ K in atTop, j K (m K) ≤ K) {t : ℝ≥0∞} (ht : 1 < t) (htop : t ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ K : ℕ in atTop,
      μ {y | (dyadicLabel K u (X y), dyadicLabel K T (Y y)) =
             (dyadicLabel K u (X x), dyadicLabel K T (Y x))} ≤
        μ {y | dyadicLabel K u (X y) = dyadicLabel K u (X x)} * t^K *
          ∏ i ∈ Finset.range (m K), verticalMass μ X Y u T (k K i) (j K (i+1)) x /
            verticalMass μ X Y u T (k K i) (j K i) x := by
  let F := joint X Y u T
  let H := horizontal X u
  let V (l : ℕ) (x : Ω) := dyadicLabel l T (Y x)
  let p K i x := conditionalLabelLaw μ (F K (j K i)) (V (j K (i+1)))
    (F K (j K i) x) (V (j K (i+1)) x)
  let r K i x := conditionalLabelLaw μ (F (k K i) (j K i)) (V (j K (i+1)))
    (F (k K i) (j K i) x) (V (j K (i+1)) x)
  let Q K x := ∏ i ∈ Finset.range (m K), p K i x / r K i x
  have mV l : Measurable (V l) := measurable_to_countable' (measurable_dyadic_fiber hY l T)
  have mF a b : Measurable (F a b) :=
    (measurable_to_countable' (measurable_dyadic_fiber hX a u)).prodMk (mV b)
  have mL (a b c : ℕ) : Measurable (fun x ↦ conditionalLabelLaw μ (F a b) (V c) (F a b x) (V c x)) :=
    (measurable_of_countable (fun e : (ℤ × ℤ) × ℤ ↦ conditionalLabelLaw μ (F a b) (V c) e.1 e.2)).comp
      ((mF a b).prodMk (mV c))
  have mQ K : Measurable (Q K) := Finset.measurable_prod _ fun i _ ↦ (mL _ _ _).div (mL _ _ _)
  have loss := ae_likelihood_subexponential μ Q (fun K ↦ (mQ K).aemeasurable)
    (fun K ↦ moving_dyadic_likelihood μ X Y hX hY u T K (k K) (j K) (hK K) (hk K) (hj K) (m K)) ht htop
  have positive := ae_all_iff.mpr (fun a : ℕ ↦ ae_all_iff.mpr
    (fun b : ℕ ↦ ae_realized_atom_nonzero μ (F a b)))
  filter_upwards [loss, positive, ae_all_iff.mpr (fun a : ℕ ↦ ae_realized_atom_nonzero μ (H a))]
    with x hx hpairs hhs
  filter_upwards [hx,last] with K hQ he
  let B (i : ℕ) := atom (F K (j K i)) x
  have nested {a b : ℕ} (hab : a ≤ b) : atom (F K b) x ⊆ atom (F K a) x := by
    intro y hy
    have hh := pair_child (X := X) (Y := Y) (u := u) (T := T) (k := K) hab x
    exact ((Set.ext_iff.mp hh y).mpr hy).1
  have chain := square_mass_chain μ (atom (H K) x) B (fun y hy ↦ congrArg Prod.fst hy)
    (fun i ↦ nested (hj K i)) (m K) (nested he)
  have pval i : p K i x = μ (B (i+1)) / μ (B i) :=
    joint_cond_eq μ X Y u T (hj K i) x
  have rval i : r K i x = μ (atom (F (k K i) (j K (i+1))) x) / μ (atom (F (k K i) (j K i)) x) :=
    joint_cond_eq μ X Y u T (hj K i) x
  have rpos i : r K i x ≠ 0 := by
    rw [rval]
    exact (ENNReal.div_pos (hpairs _ _) (measure_ne_top μ _)).ne'
  have rfin i : r K i x ≠ ∞ := by
    rw [rval]
    exact ENNReal.div_ne_top (measure_ne_top μ _) (hpairs _ _)
  have normalize i : r K i x = verticalMass μ X Y u T (k K i) (j K (i+1)) x /
      verticalMass μ X Y u T (k K i) (j K i) x := by
    rw [rval, vert_eq_joint, vert_eq_joint]
    simp only [div_eq_mul_inv (μ (atom _ x)) (μ (atom (horizontal X u (k K i)) x))]
    exact (ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.mpr (measure_ne_top μ _))
      (ENNReal.inv_ne_top.mpr (hhs _))).symm
  have factor : (∏ i ∈ Finset.range (m K), p K i x) =
      Q K x * ∏ i ∈ Finset.range (m K), r K i x := by
    dsimp only [Q]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    exact fun i _ ↦ (ENNReal.div_mul_cancel (rpos i) (rfin i)).symm
  change μ (atom (F K K) x) ≤ _
  calc
    _ ≤ μ (atom (H K) x) * ∏ i ∈ Finset.range (m K), p K i x := by simpa only [pval] using chain
    _ ≤ μ (atom (H K) x) * (t^K * ∏ i ∈ Finset.range (m K), r K i x) := by rw [factor]; gcongr
    _ = _ := by simp only [← mul_assoc, normalize]; rfl

end Weierstrass.GraphInformation
