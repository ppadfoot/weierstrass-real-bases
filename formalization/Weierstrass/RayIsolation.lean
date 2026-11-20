module

public import Weierstrass.RaySpectrum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Isolation of a moving positive harmonic on a measurable level set. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

private def rel {B : ℂ} (s j : ℤ) (n : ℕ) (z : complexPhaseGroup B) :=
  turn (relativeAngle s j n z)

private theorem cont_rel {B : ℂ} (s j : ℤ) (n : ℕ) :
    Continuous (rel (B:=B) s j n) := by
  apply continuous_subtype_val.comp
  apply AddCircle.continuous_toCircle.comp
  exact (((continuous_zsmul s).comp ((continuous_apply _).comp continuous_subtype_val)).sub
    ((continuous_apply _).comp continuous_subtype_val))

private theorem norm_rel {B : ℂ} (s j : ℤ) (n : ℕ) (z : complexPhaseGroup B) :
    ‖rel s j n z‖ = 1 := Circle.norm_coe _

private theorem rel_center {B : ℂ} (n : ℕ) (z : complexPhaseGroup B) :
    rel 1 0 n z = 1 := by simp [rel,relativeAngle,turn]

private theorem nonresonant {B : ℂ} (h : 1 < ‖B‖) (s j : ℤ) (hs : s = 1 ∨ s = -1)
    (no : s = 1 → j ≠ 0) : (s:ℂ)*B^j-1 ≠ 0 := by
  intro e
  have v := congrArg norm (sub_eq_zero.mp e)
  have nz : ‖(s:ℂ)‖ = 1 := by rcases hs with rfl|rfl <;> norm_num
  rw [norm_mul,nz,one_mul,norm_zpow,norm_one] at v
  have zj := (zpow_eq_one_iff_right₀ (norm_nonneg _) h.ne').mp v
  subst j
  rcases hs with rfl|rfl
  · exact no rfl rfl
  · norm_num at e

private theorem integrated_sum {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] (p : ℤ → X → ℂ) (w : ℤ → ℝ) (sw : Summable w)
    (mp : ∀ j, Measurable (p j)) (bp : ∀ j x, ‖p j x‖ ≤ w j) :
    (∫ x, ∑' j, p j x ∂ν) = ∑' j, ∫ x, p j x ∂ν := by
  apply (integral_tsum_of_summable_integral_norm _ _).symm
  · intro j
    exact Integrable.of_bound (mp j).aestronglyMeasurable _ (.of_forall (bp j))
  · apply (sw.mul_right (ν.real univ)).of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    intro j
    exact (integral_mono_of_nonneg (ae_of_all _ (fun _ ↦ norm_nonneg _)) (integrable_const (w j))
      (.of_forall (bp j))).trans_eq (by rw [integral_const,smul_eq_mul,mul_comm])

private theorem weighted_limit (d c : ℕ → ℂ) {w : ℝ} (hd : ∀ n, ‖d n‖ ≤ w)
    (hc : Tendsto c atTop (𝓝 0)) : Tendsto (fun n ↦ d n*c n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (tendsto_zero_iff_norm_tendsto_zero.mp hc).const_mul w
  rw [mul_zero] at h
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ h
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd n) (norm_nonneg _)

/-- If a bilateral real Fourier series is constant on a Haar set of positive
measure, its positive-frequency coefficients are little-o of their envelope.
The bound on the relative phase lengths is exactly 1 < Q |B|. -/
theorem coefficient_decay_on_level {B : ℂ} {Q M : ℝ} (hb : 1 < ‖B‖) (hQ : 0 < Q)
    (hQ' : Q < 1) (hQb : 1 < Q*‖B‖)
    (a : ℤ → ℂ) (ha : Summable fun j ↦ ‖a j‖) (bd : ∀ j, ‖a j‖ ≤ M*Q^j)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    [μ.InnerRegularCompactLTTop] {E : Set (complexPhaseGroup B)} (hm : MeasurableSet E)
    (he : 0 < μ.real E) {v : ℂ} (eq : ∀ z ∈ E, symmetricSeries a z.val = v) :
    Tendsto (fun n : ℕ ↦ a n/(Q:ℂ)^n) atTop (𝓝 0) := by
  classical
  let d := coefficient B Q a
  let w := envelope ‖B‖ Q M
  have sw : Summable w := envelope_summable hQ hQ' hQb _
  have dw : ∀ n j, ‖d n j‖ ≤ w j := coefficient_bound hQ a bd
  let t (n : ℕ) (j : ℤ) (x : complexPhaseGroup B) :=
    d n j*rel 1 j n x + conj (d n j)*rel (-1) j n x
  let off (n : ℕ) (j : ℤ) (x : complexPhaseGroup B) :=
    (if j = 0 then 0 else d n j*rel 1 j n x) + conj (d n j)*rel (-1) j n x
  have tr n j x : ‖t n j x‖ ≤ 2*w j := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_rel,mul_one,norm_conj]
    linarith only [dw n j]
  have ofr n j x : ‖off n j x‖ ≤ 2*w j := by
    unfold off
    apply (norm_add_le _ _).trans
    split <;> simp only [norm_mul,norm_rel,mul_one,norm_conj,norm_zero,zero_add] <;>
      linarith only [dw n j,norm_nonneg (d n j)]
  have ofm n j : Measurable (off n j) := by
    unfold off
    split <;> exact ((by first | exact measurable_const | exact (cont_rel _ _ _).measurable.const_mul _ :
      Measurable _).add ((cont_rel _ _ _).measurable.const_mul _))
  let ν := μ.restrict E
  let H (s j : ℤ) (n : ℕ) := ∫ z, rel s j n z ∂ν
  have ih (s j : ℤ) (n : ℕ) : Integrable (rel (B:=B) s j n) ν :=
    Integrable.of_bound (cont_rel _ _ _).measurable.aestronglyMeasurable 1 (.of_forall fun x ↦ (norm_rel _ _ _ x).le)
  have ihlim (s j : ℤ) (hs : s = 1 ∨ s = -1) (no : s = 1 → j ≠ 0) :
      Tendsto (H s j) atTop (𝓝 0) :=
    relative_coefficient_vanishes hb μ hm s j (nonresonant hb _ _ hs no)
  have olim j : Tendsto (fun n ↦ ∫ z, off n j z ∂ν) atTop (𝓝 0) := by
    have neg := weighted_limit (fun n ↦ conj (d n j)) (H (-1) j)
      (fun n ↦ (norm_conj _).trans_le (dw n j))
      (ihlim _ _ (.inr rfl) (by norm_num))
    by_cases zero : j = 0
    · simpa [off,zero,integral_const_mul,H] using neg
    · have pos := weighted_limit (fun n ↦ d n j) (H 1 j) (fun n ↦ dw n j)
          (ihlim _ _ (.inl rfl) (fun _ ↦ zero))
      simpa only [off,if_neg zero,integral_add ((ih 1 j _).const_mul _) ((ih (-1) j _).const_mul _),
        integral_const_mul,H,add_zero] using pos.add neg
  have totalOff : Tendsto (fun n ↦ ∫ z, ∑' j, off n j z ∂ν) atTop (𝓝 0) := by
    simp_rw [integrated_sum ν (off _) _ (sw.mul_left 2) (ofm _) (ofr _)]
    have T := tendsto_tsum_of_dominated_convergence (g:=fun _ : ℤ ↦ (0:ℂ))
      ((sw.mul_left 2).mul_right (ν.real univ)) olim (.of_forall fun n j ↦
        norm_integral_le_of_norm_le_const (.of_forall (ofr n j)))
    simpa using T
  have modEq n x : ∑' j, t n j x =
      ((symmetricSeries a ((halfOrbit B 1 n+x).val)-symmetricSeries a x.val)/(Q:ℂ)^n) *
        conj (coord x.val n) := (modulated_increment (norm_pos_iff.mp (zero_lt_one.trans hb)) hQ ha n x).symm
  have total : Tendsto (fun n ↦ ∫ z, ∑' j, t n j z ∂ν) atTop (𝓝 0) := by
    apply localized_increment_vanishes μ hm _ (halfOrbit_tendsto hb 1) _
      (M:=∑' j, 2*w j)
    · exact tsum_nonneg fun j ↦ (norm_nonneg _).trans (tr 0 j 0)
    · intro n x
      exact tsum_of_norm_bounded (sw.mul_left 2).hasSum (fun j ↦ tr n j x)
    · intro n x hx hx'
      rw [modEq,eq x hx,eq _ hx',sub_self,zero_div,zero_mul]
  have splitEq n (x : complexPhaseGroup B) :
      ∑' j, t n j x = (∑' j, off n j x) + d n 0 := by
    have summ := (sw.mul_left 2).of_norm_bounded (fun j ↦ ofr n j x)
    let atom (j : ℤ) : ℂ := if j=0 then d n 0 else 0
    have single : HasSum atom (d n 0) := hasSum_ite_eq 0 _
    rw [←single.tsum_eq,←summ.tsum_add single.summable]
    apply tsum_congr
    intro j
    by_cases hj : j = 0
    · simp [t,off,atom,hj,rel_center,add_comm]
    · simp [t,off,atom,hj]
  have intOff n : Integrable (fun x ↦ ∑' j, off n j x) ν :=
    Integrable.of_bound (Measurable.tsum (ofm n)).aestronglyMeasurable _ (.of_forall fun x ↦
      tsum_of_norm_bounded (sw.mul_left 2).hasSum (fun j ↦ ofr n j x))
  have central : Tendsto (fun n ↦ (μ.real E : ℂ)*d n 0) atTop (𝓝 0) := by
    have diff := total.sub totalOff
    simp_rw [splitEq,integral_add (intOff _) (integrable_const _),integral_const,
      add_sub_cancel_left] at diff
    simpa [ν,measureReal_def,Complex.real_smul] using diff
  have k : (μ.real E : ℂ)*(-2) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr he.ne') (by norm_num)
  have hc := central.const_mul (((μ.real E:ℂ)*(-2))⁻¹)
  rw [mul_zero] at hc
  convert hc using 1
  funext n
  dsimp only [d,coefficient]
  rw [Int.add_zero,jump_zero,show (μ.real E:ℂ)*(a (↑n)/(Q:ℂ)^n*(-2)) =
      ((μ.real E:ℂ)*(-2))*(a (↑n)/(Q:ℂ)^n) by ring,←mul_assoc,inv_mul_cancel₀ k,one_mul]


end Weierstrass.RaySeed
