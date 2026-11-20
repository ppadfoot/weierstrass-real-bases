module

public import Weierstrass.PrefixEnergy
public import Weierstrass.Partition
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The directional sublevel estimate in Appendix B is applied on one-dimensional
slices with a uniform upper bound on the Lipschitz constant of the derivative.
The constant below is independent of the two codes, the slice origin, the target,
and the tested radius. -/

public noncomputable section

open Set MeasureTheory
open scoped ENNReal
namespace Weierstrass.Predecessor

/-- Points in a slice with values near `y` and derivative of modulus above `e`. -/
@[expose] def transverseBand (f f' : ℝ → ℝ) (a b y r e : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ |f x - y| ≤ r ∧ e < |f' x|}

private theorem band_on_short_interval {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {a b y r e : ℝ} (he : 0 < e) (hr : 0 ≤ r)
    (osc : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, |f' x - f' z| ≤ e/2) :
    volume (transverseBand f f' a b y r e) ≤ ENNReal.ofReal (4*r/e) := by
  let B := transverseBand f f' a b y r e
  have close {x x' : ℝ} (hx : x ∈ B) (hx' : x' ∈ B) (h : x < x') : x' - x ≤ 4*r/e := by
    obtain ⟨z, hz, hsec⟩ := exists_hasDerivAt_eq_slope f f' h
      (continuousOn_of_forall_continuousAt fun x _ => (hf x).continuousAt) (fun z _ => hf z)
    have hz' : z ∈ Icc a b := ⟨hx.1.1.trans hz.1.le, hz.2.le.trans hx'.1.2⟩
    have htri := abs_sub_le (f' x) (f' z) 0
    simp only [sub_zero] at htri
    have hlarge : e/2 ≤ |f' z| := by linarith [osc x hx.1 z hz', hx.2.2]
    have hval := abs_sub_le (f x') y (f x)
    rw [abs_sub_comm y (f x)] at hval
    have hval' : |f x' - f x| ≤ 2*r := by linarith [hx.2.1, hx'.2.1]
    rw [hsec, abs_div, abs_of_pos (sub_pos.mpr h)] at hlarge
    have hslope := (le_div_iff₀ (sub_pos.mpr h)).mp hlarge
    apply (le_div_iff₀ he).mpr
    linarith
  apply (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le ?_)
  intro x hx x' hx'
  rw [Real.dist_eq]
  rcases lt_trichotomy x x' with h | rfl | h
  · rw [abs_of_neg (sub_neg.mpr h)]
    linarith [close hx hx' h]
  · simp only [sub_self, abs_zero]; positivity
  · rw [abs_of_pos (sub_pos.mpr h)]
    exact close hx' hx h

/-- A uniform derivative modulus on distances up to `δ` suffices on every
interval of length `N * δ`, with a factor `N` for the number of pieces. -/
theorem sublevel_on_pieces {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {e δ : ℝ} (he : 0 < e)
    (osc : ∀ x z, |x-z| ≤ δ → |f' x - f' z| ≤ e/2)
    (N : ℕ) (a y r : ℝ) (hr : 0 ≤ r) :
    volume (transverseBand f f' a (a+N*δ) y r e) ≤ N * ENNReal.ofReal (4*r/e) := by
  induction N with
  | zero =>
    have hs : transverseBand f f' a (a+(0:ℕ)*δ) y r e ⊆ {a} := by
      intro x hx
      have hb := hx.1
      simpa using hb
    simpa using measure_mono (μ := volume) hs
  | succ N ih =>
    let b := a+N*δ
    have hsplit : transverseBand f f' a (a+(N+1:ℕ)*δ) y r e ⊆
        transverseBand f f' a b y r e ∪ transverseBand f f' b (b+δ) y r e := by
      rintro x ⟨⟨hx, hx'⟩, hxy, hxe⟩
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc] at hx'
      rcases le_total x b with h | h
      · exact Or.inl ⟨⟨hx,h⟩, hxy, hxe⟩
      · exact Or.inr ⟨⟨h,hx'⟩, hxy, hxe⟩
    have hshort : volume (transverseBand f f' b (b+δ) y r e) ≤ ENNReal.ofReal (4*r/e) := by
      apply band_on_short_interval hf he hr
      rintro x ⟨hx, hx'⟩ z ⟨hz, hz'⟩
      exact osc x z (abs_le.mpr ⟨by linarith, by linarith⟩)
    calc
      _ ≤ _ := (measure_mono hsplit).trans (measure_union_le _ _)
      _ ≤ _ := add_le_add ih hshort
      _ = _ := by rw [Nat.cast_succ, add_mul, one_mul]

/-- The uniform `C r` transverse sublevel estimate on any translated unit
interval, under a common Lipschitz bound `M` for all first derivatives. -/
theorem uniform_transverse_sublevel {M e : ℝ} (hM : 0 ≤ M) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f f' : ℝ → ℝ), (∀ x, HasDerivAt f (f' x) x) →
      (∀ x z, |f' x-f' z| ≤ M * |x-z|) → ∀ a y r, 0 ≤ r →
      volume (transverseBand f f' a (a+1) y r e) ≤ ENNReal.ofReal (C*r) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2*M/e))
  have hN₁ : 1 < (N:ℝ) := (le_max_left _ _).trans_lt hN
  have hNp : 0 < (N:ℝ) := zero_lt_one.trans hN₁
  have hNM := (div_lt_iff₀ he).mp ((le_max_right _ _).trans_lt hN)
  refine ⟨(N:ℝ)*4/e, by positivity, ?_⟩
  intro f f' hf hLip a y r hr
  have hosc (x z : ℝ) (hxz : |x-z| ≤ (N:ℝ)⁻¹) : |f' x-f' z| ≤ e/2 := by
    apply (hLip x z).trans ((mul_le_mul_of_nonneg_left hxz hM).trans ?_)
    rw [← div_eq_mul_inv, div_le_iff₀ hNp]
    linarith
  have h := sublevel_on_pieces hf he hosc N a y r hr
  rw [mul_inv_cancel₀ hNp.ne'] at h
  apply h.trans_eq
  rw [show (N:ℝ≥0∞) = ENNReal.ofReal (N:ℝ) by simp, ← ENNReal.ofReal_mul hNp.le]
  congr 1
  ring

/-- Restriction of a coded slope series to a line. In the predecessor tree
`ω n = 2π c^(n+1)` and `φ n` contains the inherited phase at depth `n+1`. -/
def sineRay (g : ℝ) (ω φ : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, g^n * Real.sin (φ n + ω n * x)

/-- The termwise directional derivative with the frequency of each term. -/
def slopeRay (g : ℝ) (ω φ : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, (g^n * ω n) * Real.cos (φ n + ω n * x)

private theorem slope_term_bound {g L : ℝ} (hg : 0 ≤ g) {ω : ℕ → ℝ}
    (hω : ∀ n, |ω n| ≤ L) (φ : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ‖(g^n*ω n)*Real.cos (φ n + ω n*x)‖ ≤ g^n*L := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hg _)]
  exact (mul_le_of_le_one_right (mul_nonneg (pow_nonneg hg _) (abs_nonneg _))
    (Real.abs_cos_le_one _)).trans (mul_le_mul_of_nonneg_left (hω n) (pow_nonneg hg _))

theorem hasDerivAt_sineRay {g L : ℝ} (hg : 0 ≤ g) (hg' : g < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, |ω n| ≤ L) (φ : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (sineRay g ω φ) (slopeRay g ω φ x) x := by
  have hs := summable_geometric_of_lt_one hg hg'
  apply hasDerivAt_tsum (hs.mul_right L) _ (slope_term_bound hg hω φ) (y₀ := (0:ℝ)) _ x
  · intro n t
    have h := (((hasDerivAt_id t).const_mul (ω n)).const_add (φ n)).sin.const_mul (g^n)
    convert! h using 1
    simp [mul_assoc, mul_comm, mul_left_comm]
  · apply Summable.of_norm_bounded hs
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hg _)]
    exact mul_le_of_le_one_right (pow_nonneg hg _) (Real.abs_sin_le_one _)

/-- A curvature bound independent of the code and deterministic phase offsets. -/
theorem slopeRay_lipschitz {g L : ℝ} (hg : 0 ≤ g) (hg' : g < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, |ω n| ≤ L) (φ : ℕ → ℝ) (x z : ℝ) :
    |slopeRay g ω φ x - slopeRay g ω φ z| ≤ ((1-g)⁻¹ * L^2) * |x-z| := by
  have hs := hasSum_geometric_of_lt_one hg hg'
  have hL : 0 ≤ L := (abs_nonneg _).trans (hω 0)
  have summ (t : ℝ) := Summable.of_norm_bounded (hs.summable.mul_right L)
    (fun n => slope_term_bound hg hω φ n t)
  unfold slopeRay
  rw [← (summ x).tsum_sub (summ z)]
  rw [mul_assoc, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded (hs.mul_right (L^2 * |x-z|))
  intro n
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hg _)]
  have hcos := Real.abs_cos_sub_cos_le (φ n + ω n*x) (φ n + ω n*z)
  rw [show (φ n + ω n*x) - (φ n + ω n*z) = ω n*(x-z) by ring, abs_mul] at hcos
  calc
    _ ≤ (g^n*L) * (L*|x-z|) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hω n) (pow_nonneg hg _))
      (hcos.trans (mul_le_mul_of_nonneg_right (hω n) (abs_nonneg _)))
      (abs_nonneg _) (mul_nonneg (pow_nonneg hg _) hL)
    _ = _ := by ring

/-- The sublevel inequality for differences of two infinite predecessor slope
series. It is uniform in both codes, their deterministic phase offsets, and
all frequencies `|ω n| ≤ L`, and it applies at every positive derivative cutoff. -/
theorem predecessor_pair_sublevel {g L e : ℝ} (hg : 0 ≤ g) (hg' : g < 1) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω φ ψ : ℕ → ℝ), (∀ n, |ω n| ≤ L) → ∀ a y r, 0 ≤ r →
      volume (transverseBand (fun x => sineRay g ω φ x - sineRay g ω ψ x)
        (fun x => slopeRay g ω φ x - slopeRay g ω ψ x) a (a+1) y r e) ≤
        ENNReal.ofReal (C*r) := by
  let M := (1-g)⁻¹ * L^2
  have hM : 0 ≤ M := mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hg'.le)) (sq_nonneg _)
  obtain ⟨C, hC, bound⟩ := uniform_transverse_sublevel (add_nonneg hM hM) he
  refine ⟨C, hC, ?_⟩
  intro ω φ ψ hω
  apply bound _ _ (fun x => (hasDerivAt_sineRay hg hg' hω φ x).sub
    (hasDerivAt_sineRay hg hg' hω ψ x))
  intro x z
  rw [show (slopeRay g ω φ x - slopeRay g ω ψ x) - (slopeRay g ω φ z - slopeRay g ω ψ z) =
    (slopeRay g ω φ x - slopeRay g ω φ z) - (slopeRay g ω ψ x - slopeRay g ω ψ z) by ring]
  apply (abs_sub _ _).trans
  simpa only [add_mul, M] using add_le_add (slopeRay_lipschitz hg hg' hω φ x z)
    (slopeRay_lipschitz hg hg' hω ψ x z)

private theorem tail_after_first {g A : ℝ} (hg : 0 ≤ g) (hg' : g < 1)
    (f : ℕ → ℝ) (hb : ∀ n, |f n| ≤ g^n*A) :
    |(∑' n, f n) - f 0| ≤ (1-g)⁻¹*(g*A) := by
  have hs := hasSum_geometric_of_lt_one hg hg'
  have hf : Summable f := Summable.of_norm_bounded (hs.summable.mul_right A) (fun n => by
    simpa only [Real.norm_eq_abs] using hb n)
  rw [hf.tsum_eq_zero_add, add_sub_cancel_left, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded (hs.mul_right (g*A))
  intro n
  simpa only [Real.norm_eq_abs, pow_succ, mul_assoc] using hb (n+1)

private theorem head_difference_error {u v a b h : ℝ} (hu : |u-a| ≤ h) (hv : |v-b| ≤ h) :
    |a-b| ≤ |u-v|+2*h := by
  have h₁ := abs_sub_le a u b
  have h₂ := abs_sub_le u v b
  rw [abs_sub_comm a u] at h₁
  linarith

private theorem first_harmonic_gap (u v : ℝ) :
    2 * |Real.sin ((u-v)/2)| ≤ |Real.sin u - Real.sin v| + |Real.cos u - Real.cos v| := by
  let t := (u+v)/2
  have hsum : 1 ≤ |Real.sin t| + |Real.cos t| := by
    have sq_le_abs {z : ℝ} (hz : |z| ≤ 1) : z^2 ≤ |z| := by
      rw [← sq_abs, sq]
      exact mul_le_of_le_one_right (abs_nonneg _) hz
    linarith [Real.sin_sq_add_cos_sq t, sq_le_abs (Real.abs_sin_le_one t),
      sq_le_abs (Real.abs_cos_le_one t)]
  have h := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (abs_nonneg (Real.sin ((u-v)/2))))
  rw [Real.sin_sub_sin, Real.cos_sub_cos]
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  dsimp [t] at h
  linarith

/-- A full sublevel estimate, with no derivative restriction, for two codes
whose first phases have a prescribed angular separation. The tail condition
is satisfied once the derivative index makes the geometric ratio small enough.
The leading frequency `L` can have either sign. -/
theorem first_disagreement_sublevel {g L d : ℝ} (hg : 0 ≤ g) (hg' : g < 1)
    (hL : 0 < L)
    (hgap : 2*((1-g)⁻¹*g)+2*((1-g)⁻¹*(g*L)) < min 1 L * (2*d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω φ ψ : ℕ → ℝ), |ω 0| = L → (∀ n, |ω n| ≤ L) →
      d ≤ |Real.sin ((φ 0 - ψ 0)/2)| → ∀ a r, 0 ≤ r →
      volume {x ∈ Icc a (a+1) | |sineRay g ω φ x - sineRay g ω ψ x| ≤ r} ≤
        ENNReal.ofReal (C*r) := by
  let Q := min 1 L * (2*d) - (2*((1-g)⁻¹*g)+2*((1-g)⁻¹*(g*L)))
  have hQ : 0 < Q := sub_pos.mpr hgap
  obtain ⟨C, hC, hsub⟩ := predecessor_pair_sublevel (L := L) hg hg' (show 0 < Q/3 by positivity)
  refine ⟨max C (3/Q), hC.trans_le (le_max_left _ _), ?_⟩
  intro ω φ ψ hω₀ hω hsep a r hr
  by_cases hsmall : r ≤ Q/3
  · have subset : {x ∈ Icc a (a+1) | |sineRay g ω φ x - sineRay g ω ψ x| ≤ r} ⊆
        transverseBand (fun x => sineRay g ω φ x - sineRay g ω ψ x)
          (fun x => slopeRay g ω φ x - slopeRay g ω ψ x) a (a+1) 0 r (Q/3) := by
      rintro x ⟨hx, hv⟩
      refine ⟨hx, by simpa using hv, ?_⟩
      let θ (η : ℕ → ℝ) := η 0 + ω 0*x
      have sineTail (η : ℕ → ℝ) : |sineRay g ω η x - Real.sin (θ η)| ≤ (1-g)⁻¹*g := by
        simpa [sineRay, θ] using tail_after_first (A := 1) hg hg'
          (fun n => g^n * Real.sin (η n + ω n*x)) (fun n => by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hg n), mul_one]
            exact mul_le_of_le_one_right (pow_nonneg hg n) (Real.abs_sin_le_one _))
      have slopeTail (η : ℕ → ℝ) :
          |slopeRay g ω η x - ω 0 * Real.cos (θ η)| ≤ (1-g)⁻¹*(g*L) := by
        simpa [slopeRay, θ] using tail_after_first hg hg'
          (fun n => (g^n*ω n) * Real.cos (η n + ω n*x)) (fun n => by
            simpa only [Real.norm_eq_abs] using slope_term_bound hg hω η n x)
      have sinGap := head_difference_error (sineTail φ) (sineTail ψ)
      have cosGap := head_difference_error (slopeTail φ) (slopeTail ψ)
      rw [← mul_sub, abs_mul, hω₀] at cosGap
      have hdiff : θ φ - θ ψ = φ 0 - ψ 0 := by dsimp [θ]; ring
      have hlead := first_harmonic_gap (θ φ) (θ ψ)
      rw [hdiff] at hlead
      have hk : 0 ≤ min 1 L := le_min zero_le_one hL.le
      have hsep' := mul_le_mul_of_nonneg_left
        (show 2*d ≤ |Real.sin (θ φ) - Real.sin (θ ψ)| + |Real.cos (θ φ) - Real.cos (θ ψ)|
          by linarith) hk
      have hs := mul_le_mul_of_nonneg_right (min_le_left 1 L)
        (abs_nonneg (Real.sin (θ φ) - Real.sin (θ ψ)))
      have hc := mul_le_mul_of_nonneg_right (min_le_right 1 L)
        (abs_nonneg (Real.cos (θ φ) - Real.cos (θ ψ)))
      rw [mul_add] at hsep'
      dsimp [Q] at hQ hsmall ⊢
      linarith
    exact (measure_mono subset).trans ((hsub ω φ ψ hω a 0 r hr).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)))
  · apply (measure_mono (show {x ∈ Icc a (a+1) | |sineRay g ω φ x - sineRay g ω ψ x| ≤ r} ⊆
      Icc a (a+1) from fun _ hx => hx.1)).trans
    rw [Real.volume_Icc, add_sub_cancel_left]
    apply ENNReal.ofReal_le_ofReal
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right _ _) hr)
    have h := (div_lt_iff₀ (by norm_num : (0:ℝ)<3)).mp (lt_of_not_ge hsmall)
    rw [div_mul_eq_mul_div, le_div_iff₀ hQ]
    linarith

private theorem discrete_sine_gap {m p : ℕ} (hm : 0 < m) (hmp : m < p) :
    2/(p:ℝ) ≤ |Real.sin (Real.pi*(m:ℝ)/p)| := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast hm.trans hmp
  have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm₂ : (m:ℝ)+1 ≤ p := by exact_mod_cast hmp
  let t := (m:ℝ)/p
  have ht₁ : 1/(p:ℝ) ≤ t := (div_le_div_iff_of_pos_right hp).mpr hm₁
  have ht₂ : 1/(p:ℝ) ≤ 1-t := by
    dsimp [t]
    field_simp
    linarith
  have chord {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/2) : 2*u ≤ Real.sin (Real.pi*u) := by
    simpa only [show Real.pi/2*(2*u) = Real.pi*u by ring] using
      Real.le_sin_mul (show 0 ≤ 2*u by positivity) (by linarith : 2*u ≤ 1)
  rw [show Real.pi*(m:ℝ)/p = Real.pi*t by dsimp [t]; ring]
  apply le_trans _ (le_abs_self _)
  rw [show 2/(p:ℝ) = 2*(1/p) by ring]
  by_cases hhalf : t ≤ 1/2
  · linarith [chord ((by positivity : 0 ≤ 1/(p:ℝ)).trans ht₁) hhalf]
  · have h := chord ((by positivity : 0 ≤ 1/(p:ℝ)).trans ht₂) (show 1-t ≤ 1/2 by linarith)
    rw [show Real.pi*(1-t) = Real.pi - Real.pi*t by ring, Real.sin_pi_sub] at h
    linarith

open Filter
open scoped Topology

/-- The first-disagreement estimate of Appendix B on a slice, at every
sufficiently high derivative index. All constants are uniform over the
predecessor digits and the remaining phase sequences. The condition on
`φ 0 - ψ 0` is precisely the difference of two distinct first digits for
one fixed inherited lift of the central coordinates. -/
theorem high_derivative_digit_sublevel {c γ : ℝ} (hc : 0 < c) (hc' : c < 1)
    (hγ : 0 ≤ γ) {p : ℕ} (hp : 2 ≤ p) :
    ∀ᶠ j : ℕ in atTop, ∃ C : ℝ, 0 < C ∧ ∀ (φ ψ : ℕ → ℝ) (m : ℕ),
      0 < m → m < p → |φ 0 - ψ 0| = 2*Real.pi*(m:ℝ)/p → ∀ a r, 0 ≤ r →
      volume {x ∈ Icc a (a+1) |
        |sineRay (γ*c^j) (fun n => 2*Real.pi*c^(n+1)) φ x -
          sineRay (γ*c^j) (fun n => 2*Real.pi*c^(n+1)) ψ x| ≤ r} ≤ ENNReal.ofReal (C*r) := by
  let L := 2*Real.pi*c
  let g (j : ℕ) := γ*c^j
  have hL : 0 < L := by dsimp [L]; positivity
  have hp' : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa [g] using (tendsto_const_nhds (x := γ)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc')
  have ht₁ : Tendsto (fun j => (1-g j)⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hg).inv₀ (by norm_num)
  have ht : Tendsto (fun j => 2*((1-g j)⁻¹*g j) + 2*((1-g j)⁻¹*(g j*L))) atTop (𝓝 0) := by
    simpa using ((ht₁.mul hg).const_mul 2).add ((ht₁.mul (hg.mul_const L)).const_mul 2)
  have hpos : 0 < min 1 L * (2*(2/p)) := mul_pos (lt_min zero_lt_one hL) (by positivity)
  filter_upwards [ht.eventually_lt_const hpos, hg.eventually_lt_const zero_lt_one] with j hgap hsmall
  have hgj : 0 ≤ g j := mul_nonneg hγ (pow_nonneg hc.le _)
  obtain ⟨C, hC, hbound⟩ := first_disagreement_sublevel hgj hsmall hL hgap
  refine ⟨C, hC, ?_⟩
  intro φ ψ m hm hmp hphase
  apply hbound _ φ ψ (by simp [L, abs_of_pos hc, abs_of_pos Real.pi_pos])
  · intro n
    rw [abs_of_pos (by positivity), pow_succ]
    dsimp [L]
    have hpow : c^n ≤ 1 := pow_le_one₀ hc.le hc'.le
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi) hc.le)]
  · have hh : |(φ 0 - ψ 0)/2| = Real.pi*(m:ℝ)/p := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), hphase]
      ring
    rcases le_total 0 ((φ 0 - ψ 0)/2) with h | h
    · rw [abs_of_nonneg h] at hh
      rw [hh]
      exact discrete_sine_gap hm hmp
    · rw [abs_of_nonpos h] at hh
      rw [← neg_neg ((φ 0 - ψ 0)/2), hh, Real.sin_neg, abs_neg]
      exact discrete_sine_gap hm hmp

/-- One step of the inherited real-lift construction. Only the first `d`
coordinates of `w` are read. `a k` means the coefficient of degree `k+1`. -/
@[expose] def predecessor (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w : ℕ → ℝ) (i : ℕ) : ℕ → ℝ
  | 0 => ((i:ℝ) - ∑ k ∈ Finset.range d, a k*w k)/a₀
  | k+1 => w k

/-- Central state after the prescribed sequence of predecessor choices. -/
@[expose] def pathState {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w : ℕ → ℝ)
    (I : ℕ → Fin p) : ℕ → ℕ → ℝ
  | 0 => w
  | n+1 => predecessor d a a₀ (pathState d a a₀ w I n) (I n)

private theorem predecessor_shift {d : ℕ} {a : ℕ → ℝ} {a₀ b c : ℝ}
    (ha₀ : a₀ ≠ 0) (hbc : b*c = 1) (heigen : a₀*c + ∑ k ∈ Finset.range d, a k*b^k = 0)
    (w : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    predecessor d a a₀ (fun k => w k+t*b^k) i =
      fun k => predecessor d a a₀ w i k + (t*c)*b^k := by
  funext k
  cases k with
  | zero =>
    have hsum : (∑ k ∈ Finset.range d, a k*(w k+t*b^k)) =
        (∑ k ∈ Finset.range d, a k*w k) + t * ∑ k ∈ Finset.range d, a k*b^k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    simp only [predecessor, hsum, pow_zero, mul_one]
    apply (div_eq_iff ha₀).mpr
    rw [add_mul, div_mul_cancel₀ _ ha₀]
    linear_combination -t*heigen
  | succ k =>
    simp only [predecessor, pow_succ]
    linear_combination -(t*b^k)*hbc

/-- Polynomial evaluation at `b` gives the exact directional factor `c^n`
after `n` inherited steps, for every real lift and every fixed code. -/
theorem pathState_shift {p d : ℕ} {a : ℕ → ℝ} {a₀ b c : ℝ} (ha₀ : a₀ ≠ 0)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0)
    (w : ℕ → ℝ) (I : ℕ → Fin p) (t : ℝ) (n : ℕ) :
    pathState d a a₀ (fun k => w k+t*b^k) I n =
      fun k => pathState d a a₀ w I n k + (t*c^n)*b^k := by
  have heigen : a₀*c + ∑ k ∈ Finset.range d, a k*b^k = 0 := by
    linear_combination c*hpoly - (∑ k ∈ Finset.range d, a k*b^k)*hbc
  induction n with
  | zero => simp [pathState]
  | succ n ih =>
    simp only [pathState, ih]
    rw [predecessor_shift ha₀ hbc heigen]
    simp only [pow_succ, mul_assoc]

/-- The original sine series evaluated on an inherited real lift. `η` includes
both the deterministic phase and the derivative-index rotation. -/
@[expose] def codedSlope {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g : ℝ) (w : ℕ → ℝ)
    (η : ℕ → ℝ) (I : ℕ → Fin p) : ℝ :=
  ∑' n, g^n * Real.sin (2*Real.pi * pathState d a a₀ w I (n+1) 0 + η n)

private theorem codedSlope_eq_sineRay {p d : ℕ} {a : ℕ → ℝ} {a₀ b c : ℝ}
    (ha₀ : a₀ ≠ 0) (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0)
    (w η : ℕ → ℝ) (I : ℕ → Fin p) (t g : ℝ) :
    codedSlope d a a₀ g (fun k => w k+t*b^k) η I = sineRay g (fun n => 2*Real.pi*c^(n+1))
      (fun n => 2*Real.pi*pathState d a a₀ w I (n+1) 0 + η n) t := by
  unfold codedSlope sineRay
  apply tsum_congr
  intro n
  simp only [pathState_shift ha₀ hbc hpoly, pow_zero, mul_one]
  congr 2
  ring

private theorem distance_of_digits {p : ℕ} {i j : Fin p} (h : i ≠ j) :
    ∃ m : ℕ, 0 < m ∧ m < p ∧ |(i.val:ℝ)-j.val| = m := by
  have h' : i.val ≠ j.val := fun heq => h (Fin.ext heq)
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne h' with h₁ | h₁
  · refine ⟨j.val-i.val, by omega, by omega, ?_⟩
    rw [Nat.cast_sub h₁.le, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h₁.le))]
    ring
  · refine ⟨i.val-j.val, by omega, by omega, ?_⟩
    rw [Nat.cast_sub h₁.le, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h₁.le))]

/-- Uniform first-disagreement sublevel bound for the concrete polynomial
predecessor tree, restricted to the manuscript's physical direction. -/
theorem coded_predecessor_initialization {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 ≤ γ)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ C : ℝ, 0 < C ∧ ∀ (w η : ℕ → ℝ) (I J : ℕ → Fin p), I 0 ≠ J 0 →
      ∀ s r, 0 ≤ r → volume {t ∈ Icc s (s+1) |
        |codedSlope d a a₀ (γ*c^j) (fun k => w k+t*b^k) η I -
          codedSlope d a a₀ (γ*c^j) (fun k => w k+t*b^k) η J| ≤ r} ≤ ENNReal.ofReal (C*r) := by
  have hp' : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have ha₀' : a₀ ≠ 0 := abs_pos.mp (ha₀.symm ▸ hp')
  filter_upwards [high_derivative_digit_sublevel hc hc' hγ hp] with j hj
  obtain ⟨C, hC, hbound⟩ := hj
  refine ⟨C, hC, ?_⟩
  intro w η I J hIJ s r hr
  simp only [codedSlope_eq_sineRay ha₀' hbc hpoly]
  obtain ⟨m, hm, hmp, hval⟩ := distance_of_digits hIJ
  refine hbound _ _ m hm hmp ?_ s r hr
  simp only [pathState, predecessor, add_sub_add_right_eq_sub]
  rw [← mul_sub, ← sub_div, sub_sub_sub_cancel_right, abs_mul, abs_div,
    abs_of_pos (by positivity : 0 < 2*Real.pi), ha₀, hval, mul_div_assoc]

/-- Cutting a path at depth `k` restarts exactly from its inherited lift. -/
theorem pathState_append {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w : ℕ → ℝ)
    (I : ℕ → Fin p) (k n : ℕ) :
    pathState d a a₀ w I (k+n) =
      pathState d a a₀ (pathState d a a₀ w I k) (fun i => I (k+i)) n := by
  induction n with
  | zero => simp [pathState]
  | succ n ih => exact congrArg (fun W => predecessor d a a₀ W (I (k+n))) ih

theorem pathState_prefix {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w : ℕ → ℝ)
    {I J : ℕ → Fin p} (k : ℕ) (hIJ : ∀ n < k, I n = J n) :
    pathState d a a₀ w I k = pathState d a a₀ w J k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pathState, pathState, ih (fun n hn => hIJ n (Nat.lt_succ_of_lt hn)),
      hIJ k (Nat.lt_succ_self k)]

private theorem coded_summable {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w η : ℕ → ℝ)
    (I : ℕ → Fin p) {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) :
    Summable (fun n => g^n * Real.sin (2*Real.pi * pathState d a a₀ w I (n+1) 0 + η n)) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one hg hg')
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hg _)]
  exact mul_le_of_le_one_right (pow_nonneg hg n) (Real.abs_sin_le_one _)

/-- Exact affine decomposition of the actual infinite polynomial-coded slope
at any block boundary, including the shifted deterministic phase sequence. -/
theorem codedSlope_prefix_cut {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w η : ℕ → ℝ) (k : ℕ)
    {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) (U : ℕ → Fin p) :
    codedSlope d a a₀ g w η U =
      (∑ n ∈ Finset.range k, g^n*Real.sin (2*Real.pi*pathState d a a₀ w U (n+1) 0+η n)) +
      g^k * codedSlope d a a₀ g (pathState d a a₀ w U k) (fun n => η (k+n)) (fun n => U (k+n)) := by
  let f (n : ℕ) := g^n*Real.sin (2*Real.pi*pathState d a a₀ w U (n+1) 0+η n)
  have hf : Summable f := coded_summable d a a₀ w η U hg hg'
  change (∑' n, f n) = _
  rw [← hf.sum_add_tsum_nat_add k]
  congr 1
  unfold codedSlope
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [f]
  rw [Nat.add_comm n k, Nat.add_assoc, pathState_append, pow_add, mul_assoc]

/-- Two paths with a shared prefix have exactly the scaled difference of their
suffixes at the common state, also with nonstationary prescribed phases. -/
theorem codedSlope_difference_after_prefix {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ)
    (w η : ℕ → ℝ) {I J : ℕ → Fin p} (k : ℕ) (hIJ : ∀ n < k, I n = J n)
    {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) :
    codedSlope d a a₀ g w η I - codedSlope d a a₀ g w η J = g^k *
      (codedSlope d a a₀ g (pathState d a a₀ w I k) (fun n => η (k+n)) (fun n => I (k+n)) -
       codedSlope d a a₀ g (pathState d a a₀ w I k) (fun n => η (k+n)) (fun n => J (k+n))) := by
  let f (U : ℕ → Fin p) (n : ℕ) := g^n*Real.sin (2*Real.pi*pathState d a a₀ w U (n+1) 0+η n)
  have hcut := codedSlope_prefix_cut (p := p) d a a₀ w η k hg hg'
  have heq : (∑ n ∈ Finset.range k, f I n) = ∑ n ∈ Finset.range k, f J n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    dsimp [f]
    rw [pathState_prefix d a a₀ w (I := I) (J := J) (n+1) (fun u hu => hIJ u (by omega))]
  rw [hcut I, hcut J, heq, ← pathState_prefix d a a₀ w k hIJ]
  ring

/-- Common-prefix collision bound on one fixed physical slice. It includes the
Jacobian `c⁻ᵏ` of the inherited slice. This bound needs no stationarity. -/
theorem coded_prefix_slice_estimate {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ C : ℝ, 1 ≤ C ∧ ∀ (w η : ℕ → ℝ) (I J : ℕ → Fin p) (k : ℕ),
      (∀ n < k, I n = J n) → I k ≠ J k → ∀ r : ℝ, 0 ≤ r →
      volume {t ∈ Icc 0 1 |
        |codedSlope d a a₀ (γ*c^j) (fun l => w l+t*b^l) η I -
          codedSlope d a a₀ (γ*c^j) (fun l => w l+t*b^l) η J| ≤ r} ≤
        ENNReal.ofReal (C * min 1 (r * ((γ*c^j)*c)⁻¹^k)) := by
  have hgj : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := γ)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc')
  have ha₀' : a₀ ≠ 0 := abs_pos.mp (ha₀.symm ▸ (by exact_mod_cast (show 0 < p by omega)))
  filter_upwards [coded_predecessor_initialization hp ha₀ hc hc' hγ.le hbc hpoly,
    hgj.eventually_lt_const zero_lt_one] with j hj hg'
  obtain ⟨C, hC, hbound⟩ := hj
  let g := γ*c^j
  have hg : 0 < g := mul_pos hγ (pow_pos hc _)
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro w η I J k hprefix hdiff r hr
  let D := {t ∈ Icc (0:ℝ) 1 |
    |codedSlope d a a₀ g (fun l => w l+t*b^l) η I -
      codedSlope d a a₀ g (fun l => w l+t*b^l) η J| ≤ r}
  let D' := {t ∈ Icc (0:ℝ) 1 |
    |codedSlope d a a₀ g (fun l => pathState d a a₀ w I k l+t*b^l) (fun n => η (k+n)) (fun n => I (k+n)) -
      codedSlope d a a₀ g (fun l => pathState d a a₀ w I k l+t*b^l) (fun n => η (k+n)) (fun n => J (k+n))| ≤ r/g^k}
  have hcov : D ⊆ (fun t => t*c^k) ⁻¹' D' := by
    rintro t ⟨ht, hδ⟩
    refine ⟨⟨mul_nonneg ht.1 (pow_nonneg hc.le _),
      mul_le_one₀ ht.2 (pow_nonneg hc.le _) (pow_le_one₀ hc.le hc'.le)⟩, ?_⟩
    rw [codedSlope_difference_after_prefix d a a₀ _ η k hprefix hg.le hg',
      pathState_shift ha₀' hbc hpoly, abs_mul, abs_of_pos (pow_pos hg _)] at hδ
    apply (le_div_iff₀ (pow_pos hg _)).mpr
    simpa only [mul_comm] using hδ
  have hck := (pow_pos hc k).ne'
  have hD' : volume D' ≤ ENNReal.ofReal (C*(r/g^k)) := by
    simpa [D', g] using hbound (pathState d a a₀ w I k) (fun n => η (k+n))
      (fun n => I (k+n)) (fun n => J (k+n)) (by simpa using hdiff) 0 (r/g^k) (by positivity)
  have hD : volume D ≤ ENNReal.ofReal (C*(r*(g*c)⁻¹^k)) := by
    calc
      _ ≤ _ := (measure_mono hcov).trans_eq (Real.volume_preimage_mul_right hck D')
      _ ≤ _ := mul_le_mul_right hD' _
      _ = _ := by
        rw [abs_of_pos (inv_pos.mpr (pow_pos hc _)), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [g, div_eq_mul_inv, mul_inv, mul_pow, ← inv_pow]
        ring
  change volume D ≤ ENNReal.ofReal (max C 1 * min 1 (r*(g*c)⁻¹^k))
  rcases le_total (r*(g*c)⁻¹^k) 1 with h | h
  · rw [min_eq_right h]
    exact hD.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · rw [min_eq_left h, mul_one]
    have hdom : D ⊆ Icc (0:ℝ) 1 := fun _ hx => hx.1
    apply (measure_mono hdom).trans
    rw [Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- Lebesgue probability on a unit interval; an input drawn from this law
supplies an equiprobable infinite stream of base-`p` digits. -/
@[expose] def unitLaw : Measure ℝ := volume.restrict (Ico 0 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw where
  measure_univ := by simp [unitLaw, Real.volume_Ico]

@[expose] def address (p : ℕ) (x : ℝ) (n : ℕ) := ⌊(p:ℝ)^n*x⌋₊

@[expose] def uniformCode (p : ℕ) (hp : 0 < p) (x : ℝ) (n : ℕ) : Fin p :=
  ⟨address p x (n+1) % p, Nat.mod_lt _ hp⟩

theorem measurable_uniformCode (p : ℕ) (hp : 0 < p) (n : ℕ) :
    Measurable (fun x => uniformCode p hp x n) := by
  let f (i : ℕ) : Fin p := ⟨i%p, Nat.mod_lt _ hp⟩
  apply (measurable_of_countable f).comp
  exact Nat.measurable_floor.comp (measurable_const.mul measurable_id)

private theorem address_succ_div {p : ℕ} (hp : 0 < p) (x : ℝ) (n : ℕ) :
    address p x (n+1) / p = address p x n := by
  unfold address
  rw [← Nat.floor_div_natCast]
  congr 1
  rw [pow_succ, mul_right_comm, mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne')]

private theorem address_of_common_prefix {p : ℕ} (hp : 0 < p) {x y : ℝ}
    (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) (k : ℕ)
    (h : ∀ n < k, uniformCode p hp x n = uniformCode p hp y n) :
    address p x k = address p y k := by
  induction k with
  | zero => simp [address, Nat.floor_eq_zero.mpr hx.2, Nat.floor_eq_zero.mpr hy.2]
  | succ k ih =>
    have hmod := congrArg Fin.val (h k (Nat.lt_succ_self k))
    change address p x (k+1) % p = address p y (k+1) % p at hmod
    have hdiv : address p x (k+1) / p = address p y (k+1) / p := by
      rw [address_succ_div hp, address_succ_div hp]
      exact ih (fun n hn => h n (Nat.lt_succ_of_lt hn))
    have h₁ := Nat.mod_add_div (address p x (k+1)) p
    have h₂ := Nat.mod_add_div (address p y (k+1)) p
    rw [hmod,hdiv] at h₁
    exact h₁.symm.trans h₂

private theorem distance_of_common_prefix {p : ℕ} (hp : 0 < p) {x y : ℝ}
    (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) (k : ℕ)
    (h : ∀ n < k, uniformCode p hp x n = uniformCode p hp y n) : |x-y| ≤ (p:ℝ)⁻¹^k := by
  have he := address_of_common_prefix hp hx hy k h
  have hpos : 0 < (p:ℝ)^k := pow_pos (by exact_mod_cast hp) _
  have h₁ : (address p x k : ℝ) ≤ (p:ℝ)^k*x := Nat.floor_le (mul_nonneg hpos.le hx.1)
  have h₂ : (p:ℝ)^k*x < (address p x k : ℝ)+1 := Nat.lt_floor_add_one _
  have h₃ : (address p y k : ℝ) ≤ (p:ℝ)^k*y := Nat.floor_le (mul_nonneg hpos.le hy.1)
  have h₄ : (p:ℝ)^k*y < (address p y k : ℝ)+1 := Nat.lt_floor_add_one _
  rw [he] at h₁ h₂
  rw [inv_pow, ← one_div, le_div_iff₀ hpos, ← abs_of_pos hpos, ← abs_mul, abs_le]
  constructor <;> nlinarith

@[expose] def prefixAddress {p : ℕ} (I : ℕ → Fin p) : ℕ → ℕ
  | 0 => 0
  | n+1 => (I n).val + prefixAddress I n * p

private theorem prefixAddress_lt {p : ℕ} (I : ℕ → Fin p) (k : ℕ) :
    prefixAddress I k < p^k := by
  induction k with
  | zero => simp [prefixAddress]
  | succ k ih =>
    have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt ih)
    simp only [Nat.succ_mul, prefixAddress, pow_succ] at h ⊢
    omega

private theorem prefixAddress_div_mod {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ) :
    prefixAddress I (k+1) / p = prefixAddress I k ∧ prefixAddress I (k+1) % p = (I k).val := by
  simp [prefixAddress, Nat.add_mul_div_right, hp, Nat.div_eq_of_lt (I k).isLt,
    Nat.mod_eq_of_lt (I k).isLt]

private theorem prefix_iff_address {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ)
    {x : ℝ} (hx : x ∈ Ico 0 1) :
    (∀ n < k, uniformCode p hp x n = I n) ↔ address p x k = prefixAddress I k := by
  induction k with
  | zero => simp [address, prefixAddress, Nat.floor_eq_zero.mpr hx.2]
  | succ k ih =>
    obtain ⟨hd,hm⟩ := prefixAddress_div_mod hp I k
    constructor
    · intro h
      have he := ih.mp (fun n hn => h n (Nat.lt_succ_of_lt hn))
      have ha := Nat.mod_add_div (address p x (k+1)) p
      have hb := Nat.mod_add_div (prefixAddress I (k+1)) p
      have he' := congrArg Fin.val (h k (Nat.lt_succ_self k))
      change address p x (k+1) % p = (I k).val at he'
      rw [he',address_succ_div hp,he] at ha
      rw [hd,hm] at hb
      exact ha.symm.trans hb
    · intro h n hn
      have hc := congrArg (fun z : ℕ => z/p) h
      change address p x (k+1) / p = prefixAddress I (k+1) / p at hc
      rw [hd,address_succ_div hp] at hc
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hlt | rfl
      · exact ih.mpr hc n hlt
      · apply Fin.ext
        change address p x (n+1) % p = (I n).val
        rw [h,hm]

private theorem prefix_interval {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ) :
    {x | ∀ n < k, uniformCode p hp x n = I n} ∩ Ico 0 1 =
      Ico ((prefixAddress I k:ℝ)/(p:ℝ)^k) (((prefixAddress I k:ℝ)+1)/(p:ℝ)^k) := by
  let N : ℝ := prefixAddress I k
  let P : ℝ := (p:ℝ)^k
  have hP : 0 < P := pow_pos (by exact_mod_cast hp) _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hNP : N+1 ≤ P := by
    dsimp [N,P]
    exact_mod_cast (show prefixAddress I k + 1 ≤ p^k from Nat.succ_le_of_lt (prefixAddress_lt I k))
  have hset : {x | ∀ n < k, uniformCode p hp x n = I n} ∩ Ico 0 1 = Ico (N/P) ((N+1)/P) := by
    ext x
    constructor
    · rintro ⟨hw,hx⟩
      have hf := (prefix_iff_address hp I k hx).mp hw
      change ⌊P*x⌋₊ = prefixAddress I k at hf
      obtain ⟨hl,hr⟩ := (Nat.floor_eq_iff (mul_nonneg hP.le hx.1)).mp hf
      exact ⟨(div_le_iff₀ hP).mpr (by simpa [N,mul_comm] using hl),
        (lt_div_iff₀ hP).mpr (by simpa [N,mul_comm] using hr)⟩
    · rintro ⟨hl,hr⟩
      have hx : x ∈ Ico (0:ℝ) 1 := ⟨(div_nonneg hN hP.le).trans hl,
        hr.trans_le ((div_le_one hP).mpr hNP)⟩
      refine ⟨(prefix_iff_address hp I k hx).mpr ?_,hx⟩
      apply (Nat.floor_eq_iff (mul_nonneg hP.le hx.1)).mpr
      exact ⟨by simpa [mul_comm] using (div_le_iff₀ hP).mp hl,
        by simpa [mul_comm] using (lt_div_iff₀ hP).mp hr⟩
  exact hset

/-- Every prescribed `k`-digit cylinder has exactly mass `p⁻ᵏ`. This
identifies the law used below with independent equiprobable branch choices. -/
theorem uniformCode_cylinder_mass {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ) :
    unitLaw {x | ∀ n < k, uniformCode p hp x n = I n} = ENNReal.ofReal ((p:ℝ)⁻¹^k) := by
  have hset := prefix_interval hp I k
  rw [unitLaw, Measure.restrict_apply' measurableSet_Ico, hset, Real.volume_Ico]
  congr 1
  rw [← sub_div, add_sub_cancel_left, one_div, inv_pow]

private def firstDifference (p : ℕ) (hp : 0 < p) (k : ℕ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Ico 0 1 ∧ z.2 ∈ Ico 0 1 ∧
    (∀ n < k, uniformCode p hp z.1 n = uniformCode p hp z.2 n) ∧
    uniformCode p hp z.1 k ≠ uniformCode p hp z.2 k}

private theorem measurable_firstDifference (p : ℕ) (hp : 0 < p) (k : ℕ) :
    MeasurableSet (firstDifference p hp k) := by
  have hm (n : ℕ) : MeasurableSet {z : ℝ × ℝ | uniformCode p hp z.1 n = uniformCode p hp z.2 n} :=
    measurableSet_eq_fun ((measurable_uniformCode p hp n).comp measurable_fst)
      ((measurable_uniformCode p hp n).comp measurable_snd)
  convert! (measurable_fst (measurableSet_Ico (a := (0:ℝ)) (b := 1))).inter
      ((measurable_snd (measurableSet_Ico (a := (0:ℝ)) (b := 1))).inter
      ((MeasurableSet.biInter (Set.to_countable (Iio k)) fun n _ => hm n).inter (hm k).compl)) using 1
  ext z
  simp [firstDifference]

private theorem firstDifference_mass (p : ℕ) (hp : 0 < p) (k : ℕ) :
    (unitLaw.prod unitLaw) (firstDifference p hp k) ≤ ENNReal.ofReal (2*(p:ℝ)⁻¹^k) := by
  rw [Measure.prod_apply (measurable_firstDifference p hp k)]
  have hb (x : ℝ) : unitLaw (Prod.mk x ⁻¹' firstDifference p hp k) ≤ ENNReal.ofReal (2*(p:ℝ)⁻¹^k) := by
    let q := (p:ℝ)⁻¹^k
    have hsub : Prod.mk x ⁻¹' firstDifference p hp k ⊆ Icc (x-q) (x+q) := by
      intro y hy
      obtain ⟨h₁,h₂⟩ := abs_le.mp (distance_of_common_prefix hp hy.1 hy.2.1 k hy.2.2.1)
      exact ⟨by dsimp [q]; linarith, by dsimp [q]; linarith⟩
    have hvol := (measure_mono hsub (μ := unitLaw)).trans (Measure.restrict_le_self _)
    simpa [Real.volume_Icc, show x+q-(x-q) = 2*(p:ℝ)⁻¹^k by dsimp [q]; ring] using hvol
  simpa using lintegral_mono (μ := unitLaw) hb

private theorem ae_firstDifference (p : ℕ) (hp : 1 < p) :
    ∀ᵐ z ∂unitLaw.prod unitLaw, ∃ k, z ∈ firstDifference p (by omega) k := by
  have hU : ∀ᵐ x ∂unitLaw, x ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  have hdiag : ∀ᵐ z ∂unitLaw.prod unitLaw, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).mpr
    apply Filter.Eventually.of_forall
    intro x
    have : NullSingletonClass unitLaw := by unfold unitLaw; infer_instance
    exact (unitLaw.ae_ne x).mono (fun _ h => h.symm)
  have hx := (Measure.quasiMeasurePreserving_fst (μ := unitLaw) (ν := unitLaw)).ae hU
  have hy := (Measure.quasiMeasurePreserving_snd (μ := unitLaw) (ν := unitLaw)).ae hU
  filter_upwards [hx,hy,hdiag] with z hz₁ hz₂ hz₃
  have hne : ∃ k, uniformCode p (by omega) z.1 k ≠ uniformCode p (by omega) z.2 k := by
    by_contra! he
    have hpr : 1 < (p:ℝ) := by exact_mod_cast hp
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (zero_lt_one.trans hpr).le)
      ((inv_lt_one₀ (zero_lt_one.trans hpr)).mpr hpr)
    have hl : |z.1-z.2| ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun k => distance_of_common_prefix (by omega : 0 < p) hz₁ hz₂ k (fun i _ => he i))
    exact hz₃ (sub_eq_zero.mp (abs_nonpos_iff.mp hl))
  classical
  exact ⟨Nat.find hne,hz₁,hz₂,fun i hi => not_ne_iff.mp (Nat.find_min hne hi),Nat.find_spec hne⟩

theorem measurable_pathState {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w : Ω → ℕ → ℝ) (I : Ω → ℕ → Fin p)
    (hw : ∀ k, Measurable (fun x => w x k)) (hI : ∀ k, Measurable (fun x => I x k))
    (n k : ℕ) : Measurable (fun x => pathState d a a₀ (w x) (I x) n k) := by
  induction n generalizing k with
  | zero => exact hw k
  | succ n ih =>
    cases k with
    | zero =>
      apply Measurable.div_const
      apply Measurable.sub ((measurable_of_countable (fun i : Fin p => (i.val:ℝ))).comp (hI n))
      apply Finset.measurable_fun_sum
      intro k _
      exact measurable_const.mul (ih k)
    | succ k => exact ih k

/-- The displacement `t` selects a central block on the physical line and
`x` selects a path from its base-`p` digits. -/
def sampledSlope {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ b g : ℝ) (w η : ℕ → ℝ)
    (t x : ℝ) := codedSlope d a a₀ g (fun k => w k+t*b^k) η (uniformCode p hp x)

theorem measurable_sampledSlope {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ b g : ℝ)
    (w η : ℕ → ℝ) : Measurable (fun z : ℝ × ℝ => sampledSlope hp d a a₀ b g w η z.1 z.2) := by
  unfold sampledSlope codedSlope
  apply Measurable.tsum
  intro n
  apply measurable_const.mul
  apply Real.continuous_sin.measurable.comp
  apply Measurable.add_const
  apply measurable_const.mul
  exact measurable_pathState d a a₀ _ _ (fun _ => measurable_const.add
    (measurable_fst.mul_const _)) (fun k => (measurable_uniformCode p hp k).comp measurable_snd) _ _

/-- Conditional sampled law on the actual inherited path tree, at one fixed
central block on a physical line. -/
def sampledLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ b g : ℝ) (w η : ℕ → ℝ) (t : ℝ) :=
  unitLaw.map (sampledSlope hp d a a₀ b g w η t)

instance {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ b g : ℝ) (w η : ℕ → ℝ) (t : ℝ) :
    IsFiniteMeasure (sampledLaw hp d a a₀ b g w η t) := by unfold sampledLaw; infer_instance

private theorem law_band_sections {f : ℝ → ℝ → ℝ} (hf : Measurable (fun z : ℝ × ℝ => f z.1 z.2))
    (r : ℝ) :
    Measurable (fun t => ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band r)) ∧
    (∫⁻ t, ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band r) ∂unitLaw) =
      ∫⁻ z : ℝ × ℝ, unitLaw {t | |f t z.1-f t z.2| ≤ r} ∂unitLaw.prod unitLaw := by
  let B : Set (ℝ × (ℝ × ℝ)) := {z | |f z.1 z.2.1 - f z.1 z.2.2| ≤ r}
  have hm : MeasurableSet B := by
    apply measurableSet_le _ measurable_const
    exact continuous_abs.measurable.comp ((hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).sub
      (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
  have e (t : ℝ) : ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band r) =
      (unitLaw.prod unitLaw) (Prod.mk t ⁻¹' B) := by
    have ht : Measurable (f t) := hf.comp measurable_prodMk_left
    rw [Measure.map_prod_map _ _ ht ht, Measure.map_apply (ht.prodMap ht) (PrefixEnergy.band_measurable _)]
    rfl
  simp_rw [e]
  exact ⟨measurable_measure_prodMk_left hm, (Measure.prod_apply hm).symm.trans (Measure.prod_apply_symm hm)⟩

/-- Integrating all first-disagreement classes against two independent paths
gives an actual collision estimate, uniformly in every deterministic phase
sequence and the initial central state of the slice. -/
theorem integrated_predecessor_collisions {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ K : ℝ, 0 < K ∧ ∀ (w η : ℕ → ℝ) (r : ℝ), 0 < r → r ≤ 1 →
      (∫⁻ t, let ν := sampledLaw (by omega : 0 < p) d a a₀ b (γ*c^j) w η t
             (ν.prod ν) (PrefixEnergy.band r) ∂unitLaw) ≤
        ENNReal.ofReal K * ENNReal.ofReal (PrefixEnergy.prefixSeries p ((γ*c^j)*c) r) := by
  have hp₀ : 0 < p := by omega
  have hpr : 1 < (p:ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hg : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := γ)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc')
  filter_upwards [coded_prefix_slice_estimate hp ha₀ hc hc' hγ hbc hpoly,
    hg.eventually_lt_const zero_lt_one] with j hj hgj
  obtain ⟨C,hC,hbound⟩ := hj
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  refine ⟨2*C, by positivity, ?_⟩
  intro w η r hr hr'
  let q := (γ*c^j)*c
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : q < 1 := (mul_lt_mul_of_pos_right hgj hc).trans_le (by simpa using hc'.le)
  let f := sampledSlope hp₀ d a a₀ b (γ*c^j) w η
  let B (z : ℝ × ℝ) := {t | |f t z.1-f t z.2| ≤ r}
  let weight (k : ℕ) := ENNReal.ofReal (C*min 1 (r*q⁻¹^k))
  let E := firstDifference p hp₀
  let A (k : ℕ) := (E k).indicator (fun _ => weight k)
  have hA (k : ℕ) : Measurable (A k) := measurable_const.indicator (measurable_firstDifference _ _ _)
  have hslice (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ E k) : unitLaw (B z) ≤ weight k := by
    have hb := hbound w η (uniformCode p hp₀ z.1) (uniformCode p hp₀ z.2) k hz.2.2.1 hz.2.2.2 r hr.le
    apply le_trans _ hb
    rw [unitLaw, Measure.restrict_apply' measurableSet_Ico]
    apply measure_mono
    exact fun t h => ⟨Ico_subset_Icc_self h.2,h.1⟩
  have hmajor : ∀ᵐ z ∂unitLaw.prod unitLaw, unitLaw (B z) ≤ ∑' k, A k z := by
    filter_upwards [ae_firstDifference p (by omega)] with z hz
    obtain ⟨k,hk⟩ := hz
    exact (hslice k z hk).trans ((by rw [show A k z = weight k from indicator_of_mem hk _] :
      weight k ≤ A k z).trans (ENNReal.le_tsum k))
  let σ := min 1 (Real.log p / Real.log (1/q))
  have hσ : (0:ℝ) < σ := lt_min zero_lt_one (div_pos (Real.log_pos hpr)
    (Real.log_pos ((one_lt_div hq).mpr hq')))
  obtain ⟨_, _, hsum⟩ := PrefixEnergy.prefixSeries_subcritical hpr hq hq' hσ
  have hn (k : ℕ) : 0 ≤ PrefixEnergy.prefixTerm p q r k := by
    unfold PrefixEnergy.prefixTerm
    exact mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
  have hprod (k : ℕ) : (∫⁻ z, A k z ∂unitLaw.prod unitLaw) ≤
      ENNReal.ofReal (2*C) * ENNReal.ofReal (PrefixEnergy.prefixTerm p q r k) := by
    rw [show (∫⁻ z, A k z ∂unitLaw.prod unitLaw) = weight k * (unitLaw.prod unitLaw) (E k) from
      lintegral_indicator_const (measurable_firstDifference _ _ _) _]
    apply (mul_le_mul_right (firstDifference_mass p hp₀ k) _).trans_eq
    unfold weight PrefixEnergy.prefixTerm
    rw [← ENNReal.ofReal_mul (mul_nonneg hC₀.le (le_min zero_le_one (by positivity))),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  change (∫⁻ t, ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band r) ∂unitLaw) ≤ _
  rw [(law_band_sections (measurable_sampledSlope hp₀ d a a₀ b _ w η) r).2]
  calc
    _ ≤ _ := lintegral_mono_ae hmajor
    _ = _ := lintegral_tsum fun k => (hA k).aemeasurable
    _ ≤ _ := ENNReal.tsum_le_tsum hprod
    _ = _ := by rw [ENNReal.tsum_mul_left, PrefixEnergy.prefixSeries,
      ENNReal.ofReal_tsum_of_nonneg hn (hsum r hr hr').1]

/-- An unconditional high-index lower local dimension estimate for the
conditional sampled slope measure. It holds almost everywhere on *every*
physical slice and for each prescribed sequence of phases. The denominator
uses `gⱼ c`, because averaging a fixed slice loses its Jacobian at a shared
prefix. Averaging Haar states before conditioning removes this loss in the
stronger estimate in the manuscript. -/
theorem ae_predecessor_slope_lower_dimension {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∀ w η : ℕ → ℝ, ∀ᵐ t ∂unitLaw,
      ∀ᵐ y ∂sampledLaw (by omega : 0 < p) d a a₀ b (γ*c^j) w η t,
        ∀ u : ℝ, u < min 1 (Real.log p / Real.log (1 / ((γ*c^j)*c))) →
          ∀ᶠ r : ℝ in 𝓝[>] 0, u ≤ Real.log ((sampledLaw (by omega : 0 < p) d a a₀ b (γ*c^j) w η t).real
            (Icc (y-r) (y+r))) / Real.log r := by
  have hg : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := γ)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc')
  filter_upwards [integrated_predecessor_collisions hp ha₀ hc hc' hγ hbc hpoly,
    hg.eventually_lt_const zero_lt_one] with j hj hsmall
  obtain ⟨K, _, hbound⟩ := hj
  have hq : 0 < (γ*c^j)*c := by positivity
  have hq' : (γ*c^j)*c < 1 := (mul_lt_mul_of_pos_right hsmall hc).trans_le (by simpa using hc'.le)
  intro w η
  apply PrefixEnergy.ae_lower_local_dimension_from_prefix_bound unitLaw
    (sampledLaw (by omega : 0 < p) d a a₀ b (γ*c^j) w η)
    (p := (p:ℝ)) (q := (1/2:ℝ)) (by exact_mod_cast (show 1 < p by omega)) hq hq'
    (by norm_num) (by norm_num) (ENNReal.ofReal_ne_top (r := K))
  · intro n
    exact (law_band_sections (measurable_sampledSlope _ _ _ _ _ _ _ _) _).1.aemeasurable
  · intro n
    exact hbound w η _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

private theorem heavy_ball_markov {X : Type*} [MeasurableSpace X] (m : Measure X) [SFinite m]
    {f : X → ℝ → ℝ} (hf : Measurable (fun z : X × ℝ => f z.1 z.2))
    (R τ : ℝ) (hτ : 0 < τ) :
    (m.prod unitLaw) {z | ENNReal.ofReal τ < (unitLaw.map (f z.1)) (Icc (f z.1 z.2-R) (f z.1 z.2+R))} ≤
      (∫⁻ t, ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band R) ∂m) /
        ENNReal.ofReal τ := by
  let D : Set ((X × ℝ) × ℝ) := {q | |f q.1.1 q.1.2 - f q.1.1 q.2| ≤ R}
  let B (z : X × ℝ) := unitLaw (Prod.mk z ⁻¹' D)
  have hD : MeasurableSet D := by
    apply measurableSet_le _ measurable_const
    apply continuous_abs.measurable.comp
    exact (hf.comp measurable_fst).sub (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hB : Measurable B := measurable_measure_prodMk_left hD
  have hz (z : X × ℝ) : (unitLaw.map (f z.1)) (Icc (f z.1 z.2-R) (f z.1 z.2+R)) = B z := by
    have ht : Measurable (f z.1) := hf.comp measurable_prodMk_left
    rw [Measure.map_apply ht measurableSet_Icc]
    congr 1
    ext x
    change (_ ≤ f z.1 x ∧ f z.1 x ≤ _) ↔ |_ - _| ≤ R
    rw [abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have he (t : X) : (∫⁻ x, B (t,x) ∂unitLaw) =
      ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band R) := by
    have ht : Measurable (f t) := hf.comp measurable_prodMk_left
    rw [Measure.map_prod_map _ _ ht ht, Measure.map_apply (ht.prodMap ht) (PrefixEnergy.band_measurable _),
      Measure.prod_apply ((ht.prodMap ht) (PrefixEnergy.band_measurable _))]
    rfl
  have hE : (∫⁻ z, B z ∂m.prod unitLaw) = ∫⁻ t,
      ((unitLaw.map (f t)).prod (unitLaw.map (f t))) (PrefixEnergy.band R) ∂m := by
    rw [lintegral_prod _ hB.aemeasurable]
    exact lintegral_congr_ae (.of_forall he)
  simp_rw [hz]
  calc
    _ ≤ (m.prod unitLaw) {z | ENNReal.ofReal τ ≤ B z} := measure_mono
      (fun z (h : ENNReal.ofReal τ < B z) => (h.le : ENNReal.ofReal τ ≤ B z))
    _ ≤ _ := meas_ge_le_lintegral_div hB.aemeasurable (ENNReal.ofReal_pos.mpr hτ).ne' ENNReal.ofReal_ne_top
    _ = _ := by rw [hE]

/-- Quantitative, phase-uniform information for the full conditional law at
high derivative indices. The probability of a sampled heavy ball decays at
the explicit rate `r^(v-u)` for every strictly subcritical `v`. -/
theorem uniform_predecessor_slope_information {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∀ u v : ℝ, u < v → v < min 1 (Real.log p / Real.log (1 / ((γ*c^j)*c))) →
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ (w η : ℕ → ℝ) (r : ℝ), 0 < r → A*r ≤ 1 →
      (unitLaw.prod unitLaw) {z | let y := sampledSlope (by omega : 0 < p) d a a₀ b (γ*c^j) w η z.1 z.2
        ENNReal.ofReal (r^u) < (sampledLaw (by omega : 0 < p) d a a₀ b (γ*c^j) w η z.1)
          (Icc (y-A*r) (y+A*r))} ≤ ENNReal.ofReal (C*r^(v-u)) := by
  have hg : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := γ)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc')
  filter_upwards [integrated_predecessor_collisions hp ha₀ hc hc' hγ hbc hpoly,
    hg.eventually_lt_const zero_lt_one] with j hj hsmall
  obtain ⟨K,hK,hbound⟩ := hj
  let q := (γ*c^j)*c
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : q < 1 := (mul_lt_mul_of_pos_right hsmall hc).trans_le (by simpa using hc'.le)
  intro u v _ hv A hA
  have hpr : 1 < (p:ℝ) := by exact_mod_cast (show 1 < p by omega)
  obtain ⟨D,hD,hseries⟩ := PrefixEnergy.prefixSeries_subcritical hpr hq hq' hv
  refine ⟨K*D*A^v, by positivity, ?_⟩
  intro w η r hr hAr
  let f := sampledSlope (by omega : 0 < p) d a a₀ b (γ*c^j) w η
  have hr' := Real.rpow_pos_of_pos hr u
  have hmark := heavy_ball_markov unitLaw (measurable_sampledSlope (by omega : 0 < p) d a a₀ b (γ*c^j) w η) (A*r) (r^u) hr'
  apply hmark.trans
  have ht := (hbound w η (A*r) (mul_pos hA hr) hAr).trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (hseries (A*r) (mul_pos hA hr) hAr).2) _)
  apply (ENNReal.div_le_div_right ht _).trans_eq
  rw [← ENNReal.ofReal_mul hK.le, ← ENNReal.ofReal_div_of_pos hr', Real.mul_rpow hA.le hr.le, Real.rpow_sub hr]
  congr 1
  ring

/-- The next-index conditional slope is exactly the physical derivative, on
every inherited code and for every deterministic phase string. -/
theorem codedSlope_hasDerivAt_next {p d : ℕ} {a : ℕ → ℝ} {a₀ b c g : ℝ} (ha₀ : a₀ ≠ 0)
    (hg : 0 ≤ g) (hg' : g < 1) (hc : 0 < c) (hc' : c ≤ 1)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0)
    (w η : ℕ → ℝ) (I : ℕ → Fin p) (x : ℝ) :
    HasDerivAt (fun t => codedSlope d a a₀ g (fun l => w l+t*b^l) η I)
      ((2*Real.pi*c) * codedSlope d a a₀ (g*c) (fun l => w l+x*b^l)
        (fun n => η n+Real.pi/2) I) x := by
  let ω (n : ℕ) := 2*Real.pi*c^(n+1)
  let φ (n : ℕ) := 2*Real.pi*pathState d a a₀ w I (n+1) 0+η n
  have hω (n : ℕ) : |ω n| ≤ 2*Real.pi := by
    dsimp [ω]
    rw [abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hc.le hc')
  have h := hasDerivAt_sineRay hg hg' hω φ x
  simp only [codedSlope_eq_sineRay ha₀ hbc hpoly]
  apply h.congr_deriv
  unfold slopeRay sineRay
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [φ,ω]
  rw [show 2*Real.pi*pathState d a a₀ w I (n+1) 0+(η n+Real.pi/2)+2*Real.pi*c^(n+1)*x =
    (2*Real.pi*pathState d a a₀ w I (n+1) 0+η n+2*Real.pi*c^(n+1)*x)+Real.pi/2 by ring,
    Real.sin_add_pi_div_two, mul_pow, pow_succ]
  ring

/-- The finite slope used to mark a block. -/
@[expose] def truncatedSlope {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, g^k*Real.sin (2*Real.pi*pathState d a a₀ w I (k+1) 0+η k)

theorem truncatedSlope_tail {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (w η : ℕ → ℝ)
    (I : ℕ → Fin p) {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) (n : ℕ) :
    |codedSlope d a a₀ g w η I - truncatedSlope d a a₀ g w η I n| ≤ (1-g)⁻¹ * g^n := by
  have hs := coded_summable d a a₀ w η I hg hg'
  unfold codedSlope truncatedSlope
  rw [← hs.sum_add_tsum_nat_add n, add_sub_cancel_left, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hg hg').mul_right (g^n))
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hg _), ← pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hg _) (Real.abs_sin_le_one _)

private theorem truncatedSlope_congr {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g : ℝ) (w η : ℕ → ℝ)
    (I J : ℕ → Fin p) (n : ℕ) (hIJ : ∀ k < n, I k = J k) :
    truncatedSlope d a a₀ g w η I n = truncatedSlope d a a₀ g w η J n := by
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [pathState_prefix d a a₀ w (I := I) (J := J) (k+1) (fun i hi => hIJ i (by omega))]

@[expose] def extendWord {p n : ℕ} (hp : 0 < p) (v : Fin n → Fin p) (k : ℕ) : Fin p :=
  if h : k < n then v ⟨k,h⟩ else ⟨0,hp⟩

/-- The good/bad neighbor test on actual length-`n` prefixes. -/
noncomputable def slopeNeighbors {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ g : ℝ)
    (w η : ℕ → ℝ) (I : ℕ → Fin p) (n : ℕ) (D : ℝ) : Finset (Fin n → Fin p) :=
  Finset.univ.filter fun v => |truncatedSlope d a a₀ g w η I n -
    truncatedSlope d a a₀ g w η (extendWord hp v) n| ≤ D*g^n

private theorem measurable_prefix_event {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (n : ℕ) :
    MeasurableSet {x | ∀ k < n, uniformCode p hp x k = I k} := by
  convert! (MeasurableSet.biInter (Set.to_countable (Iio n)) (fun k _ =>
    measurableSet_eq_fun (measurable_uniformCode p hp k) (measurable_const (a := I k)))) using 1
  ext x
  simp

set_option maxHeartbeats 750000 in
/-- The count of neighboring prefixes, weighted by their actual probabilities,
is bounded by the full conditional measure of the sampled slope ball. -/
theorem slopeNeighbor_mass_le {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ b : ℝ)
    {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) (w η : ℕ → ℝ) (t x : ℝ) (n : ℕ) (D : ℝ) :
    let W := fun k => w k+t*b^k
    let N := slopeNeighbors hp d a a₀ g W η (uniformCode p hp x) n D
    let y := sampledSlope hp d a a₀ b g w η t x
    let R := (D+2*(1-g)⁻¹)*g^n
    (N.card : ℝ≥0∞)*ENNReal.ofReal ((p:ℝ)⁻¹^n) ≤ (sampledLaw hp d a a₀ b g w η t) (Icc (y-R) (y+R)) := by
  classical
  dsimp only
  let W := fun k => w k+t*b^k
  let N := slopeNeighbors hp d a a₀ g W η (uniformCode p hp x) n D
  let E (v : Fin n → Fin p) := {z : ℝ | ∀ k < n, uniformCode p hp z k = extendWord hp v k}
  have hm (v : Fin n → Fin p) : MeasurableSet (E v) := measurable_prefix_event hp _ _
  have hdisj : (N:Set (Fin n → Fin p)).PairwiseDisjoint E := by
    intro v _ u _ hne
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    apply hne
    funext k
    simpa [extendWord, k.isLt] using (hz₁ k k.isLt).symm.trans (hz₂ k k.isLt)
  have hcount : unitLaw (⋃ v ∈ N, E v) = (N.card:ℝ≥0∞)*ENNReal.ofReal ((p:ℝ)⁻¹^n) := by
    rw [measure_biUnion_finset hdisj (fun v _ => hm v)]
    simp only [E, uniformCode_cylinder_mass, Finset.sum_const, nsmul_eq_mul]
  change (N.card : ℝ≥0∞)*ENNReal.ofReal ((p:ℝ)⁻¹^n) ≤ _
  refine LE.le.trans (le_of_eq hcount.symm) ?_
  let Y : ℝ → ℝ := sampledSlope hp d a a₀ b g w η t
  let R : ℝ := (D+2*(1-g)⁻¹)*g^n
  have hYm : Measurable Y := by
    change Measurable ((fun z : ℝ × ℝ => sampledSlope hp d a a₀ b g w η z.1 z.2) ∘ (fun x : ℝ => (t,x)))
    exact (measurable_sampledSlope hp d a a₀ b g w η).comp (measurable_const.prodMk measurable_id)
  change unitLaw _ ≤ (unitLaw.map Y) (Icc (Y x - R) (Y x + R))
  refine LE.le.trans ?_ (le_of_eq (Measure.map_apply hYm (measurableSet_Icc (a := Y x-R) (b := Y x+R))).symm)
  apply measure_mono
  intro z hz
  obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
  have hnear : |truncatedSlope d a a₀ g W η (uniformCode p hp x) n - truncatedSlope d a a₀ g W η (extendWord hp v) n| ≤ D*g^n := (Finset.mem_filter.mp hv).2
  have heq := truncatedSlope_congr d a a₀ g W η (uniformCode p hp z) (extendWord hp v) n hzv
  rw [← heq] at hnear
  have h₁ := truncatedSlope_tail d a a₀ W η (uniformCode p hp x) hg hg' n
  have h₂ := truncatedSlope_tail d a a₀ W η (uniformCode p hp z) hg hg' n
  rw [abs_le] at h₁ h₂ hnear
  change codedSlope d a a₀ g W η (uniformCode p hp x) - (D+2*(1-g)⁻¹)*g^n ≤
      codedSlope d a a₀ g W η (uniformCode p hp z) ∧
    codedSlope d a a₀ g W η (uniformCode p hp z) ≤
      codedSlope d a a₀ g W η (uniformCode p hp x) + (D+2*(1-g)⁻¹)*g^n
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hnear.1,hnear.2]

/-- High-index bad-block probabilities for the concrete finite-prefix graph.
Here the comparison is with the degree divided by `pⁿ`. The constants and the
first admissible length apply to all prescribed phases and initial slices. -/
theorem uniform_crowded_prefix_bound {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∀ u v : ℝ, u < v → v < min 1 (Real.log p / Real.log (1 / ((γ*c^j)*c))) →
      ∀ D : ℝ, 0 ≤ D → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (w η : ℕ → ℝ),
      (unitLaw.prod unitLaw) {z | let g := γ*c^j
        let N := slopeNeighbors (by omega : 0 < p) d a a₀ g (fun k => w k+z.1*b^k) η
          (uniformCode p (by omega) z.2) n D
        ENNReal.ofReal ((g^n)^u) < N.card*ENNReal.ofReal ((p:ℝ)⁻¹^n)} ≤
          ENNReal.ofReal (C*((γ*c^j)^n)^(v-u)) := by
  have hg : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := γ)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc')
  filter_upwards [uniform_predecessor_slope_information hp ha₀ hc hc' hγ hbc hpoly,
    hg.eventually_lt_const zero_lt_one] with j hj hsmall
  intro u v huv hv D hD
  let g := γ*c^j
  have hgj : 0 < g := mul_pos hγ (pow_pos hc _)
  let A := D+2*(1-g)⁻¹
  have hA : 0 < A := add_pos_of_nonneg_of_pos hD (mul_pos (by norm_num) (inv_pos.mpr (sub_pos.mpr hsmall)))
  obtain ⟨C,hC,hbound⟩ := hj u v huv hv A hA
  refine ⟨C,hC,?_⟩
  have hlim : Tendsto (fun n : ℕ => A*g^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hgj.le hsmall).const_mul A
  filter_upwards [hlim.eventually_lt_const zero_lt_one] with n hn
  intro w η
  apply le_trans _ (hbound w η (g^n) (pow_pos hgj n) hn.le)
  apply measure_mono
  intro z hz
  exact lt_of_lt_of_le hz (slopeNeighbor_mass_le (by omega : 0 < p) d a a₀ b hgj.le hsmall w η z.1 z.2 n D)

/-- The diagonal energy bound in the neighbor recursion. A symmetric
nonnegative matrix with row sums at most `D` costs at most `D` copies of the
diagonal energy. Zero entries may encode both status and neighbor tests. -/
theorem symmetric_neighbor_energy {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hsym : ∀ i j, M i j = M j i)
    (v : ι → ℝ) (D : ℝ) (hD : ∀ i, ∑ j, M i j ≤ D) :
    ∑ i, ∑ j, M i j * (v i * v j) ≤ D * ∑ i, (v i)^2 := by
  classical
  let A := ∑ i, ∑ j, M i j*(v i)^2
  have hright : (∑ i, ∑ j, M i j*(v j)^2) = A := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun i _ => by rw [hsym i j])
  have hA : A ≤ D*∑ i, (v i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)
  have hquad : (∑ i, ∑ j, M i j * (v i*v j)) + (∑ i, ∑ j, M i j * (v i*v j)) ≤ A+A := by
    nth_rw 2 [← hright]
    dsimp only [A]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have q : v i*v j+v i*v j ≤ (v i)^2+(v j)^2 := by nlinarith [sq_nonneg (v i-v j)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left q (hM i j)
  linarith

/-- Keeping track of the derivative cutoff gives a uniform `O(r/e²)` bound
for `0 < e ≤ 1`. The resulting constant depends only on the curvature bound. -/
theorem quantitative_transverse_sublevel {M e : ℝ} (hM : 0 ≤ M) (he : 0 < e) (he' : e ≤ 1)
    (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hLip : ∀ x z, |f' x-f' z| ≤ M*|x-z|) (a y r : ℝ) (hr : 0 ≤ r) :
    volume (transverseBand f f' a (a+1) y r e) ≤ ENNReal.ofReal ((4*(2*M+1)/e^2)*r) := by
  let N := ⌊2*M/e⌋₊ + 1
  have hNp : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hNM : 2*M < (N:ℝ)*e := by
    apply (div_lt_iff₀ he).mp
    simpa [N] using Nat.lt_floor_add_one (2*M/e)
  have hNM' : (N:ℝ)*e ≤ 2*M+1 := by
    have hfloor := Nat.floor_le (show 0 ≤ 2*M/e by positivity)
    have hh : (N:ℝ) ≤ 2*M/e+1 := by simpa [N] using add_le_add_right hfloor 1
    have hb := mul_le_mul_of_nonneg_right hh he.le
    rw [add_mul,div_mul_cancel₀ _ he.ne',one_mul] at hb
    linarith
  have hosc (x z : ℝ) (h : |x-z| ≤ (N:ℝ)⁻¹) : |f' x-f' z| ≤ e/2 := by
    apply (hLip x z).trans ((mul_le_mul_of_nonneg_left h hM).trans ?_)
    rw [← div_eq_mul_inv, div_le_iff₀ hNp]
    linarith
  have h := sublevel_on_pieces hf he hosc N a y r hr
  rw [mul_inv_cancel₀ hNp.ne', show (N:ℝ≥0∞) = ENNReal.ofReal (N:ℝ) by simp,
    ← ENNReal.ofReal_mul hNp.le] at h
  apply h.trans (ENNReal.ofReal_le_ofReal _)
  have hrate : (N:ℝ)*4/e ≤ 4*(2*M+1)/e^2 := by
    field_simp
    linarith
  exact (show (N:ℝ)*(4*r/e) = (N*4/e)*r by ring).le.trans (mul_le_mul_of_nonneg_right hrate hr)

/-- The off-diagonal coefficient for a prefix of length `n`. -/
@[expose] def slopeSliceBound (g c : ℝ) (n : ℕ) : ℝ :=
  let M := (1-g)⁻¹*(2*Real.pi)^2
  4*(2*(M+M)+1)/((min 1 (2*Real.pi*c))*(g*c)^n)^2

theorem slopeSliceBound_pos {g c : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (n : ℕ) :
    0 < slopeSliceBound g c n := by
  have e : 0<min 1 (2*Real.pi*c) := lt_min zero_lt_one (by positivity)
  unfold slopeSliceBound
  positivity

/-- The off-diagonal sublevel bound in the energy recursion, on the *actual*
polynomial code tree. The prefix test alone forces non-neighbor continuations
to have separated full directional derivatives on the tested set. This holds
at every derivative index, for every fixed block length. -/
theorem offDiagonal_prefix_collision_rate {p d : ℕ} {a : ℕ → ℝ} {a₀ b c g : ℝ} (ha₀ : a₀ ≠ 0)
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C = slopeSliceBound g c n ∧ ∀ (w η : ℕ → ℝ) (I J : ℕ → Fin p) (s r : ℝ), 0 ≤ r →
      volume {t ∈ Icc s (s+1) | let W := fun k => w k+t*b^k
        let θ := fun k => η k+Real.pi/2
        (2*(1-g*c)⁻¹+1)*(g*c)^n <
          |truncatedSlope d a a₀ (g*c) W θ I n - truncatedSlope d a a₀ (g*c) W θ J n| ∧
          |codedSlope d a a₀ g W η I - codedSlope d a a₀ g W η J| ≤ r} ≤ ENNReal.ofReal (C*r) := by
  let L := 2*Real.pi*c
  let h := g*c
  let ω (k : ℕ) := 2*Real.pi*c^(k+1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hh : 0 < h := mul_pos hg hc
  have hh' : h < 1 := (mul_lt_mul_of_pos_right hg' hc).trans_le (by simpa using hc'.le)
  have hω (k : ℕ) : |ω k| ≤ 2*Real.pi := by
    dsimp [ω]
    rw [abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hc.le hc'.le)
  let e := min 1 L * h^n
  let M := (1-g)⁻¹*(2*Real.pi)^2
  have hM : 0≤M := by dsimp [M];positivity
  have he : 0<e := mul_pos (lt_min zero_lt_one hL) (pow_pos hh n)
  have he' : e ≤ 1 := mul_le_one₀ (min_le_left ..) (pow_nonneg hh.le _) (pow_le_one₀ hh.le hh'.le)
  have hsub (ω φ ψ : ℕ → ℝ) (hf : ∀ n, |ω n| ≤ 2*Real.pi) (s y r : ℝ) (hr : 0≤r) :
      volume (transverseBand (fun x => sineRay g ω φ x-sineRay g ω ψ x)
        (fun x => slopeRay g ω φ x-slopeRay g ω ψ x) s (s+1) y r e) ≤ ENNReal.ofReal (slopeSliceBound g c n*r) := by
    apply quantitative_transverse_sublevel (add_nonneg hM hM) he he' _ _ (fun x ↦
      (hasDerivAt_sineRay hg.le hg' hf φ x).sub (hasDerivAt_sineRay hg.le hg' hf ψ x)) _ s y r hr
    intro x z
    rw [show (slopeRay g ω φ x-slopeRay g ω ψ x)-(slopeRay g ω φ z-slopeRay g ω ψ z)=
      (slopeRay g ω φ x-slopeRay g ω φ z)-(slopeRay g ω ψ x-slopeRay g ω ψ z) by ring]
    apply (abs_sub _ _).trans
    simpa only [add_mul,M] using add_le_add (slopeRay_lipschitz hg.le hg' hf φ x z) (slopeRay_lipschitz hg.le hg' hf ψ x z)
  refine ⟨_,slopeSliceBound_pos hg hg' hc n,rfl,?_⟩
  intro w η I J s r hr
  let W (t : ℝ) (k : ℕ) := w k+t*b^k
  let φ (U : ℕ → Fin p) (k : ℕ) := 2*Real.pi*pathState d a a₀ w U (k+1) 0 + η k
  let θ (k : ℕ) := η k+Real.pi/2
  have hray (U : ℕ → Fin p) (t : ℝ) : slopeRay g ω (φ U) t = L*codedSlope d a a₀ h (W t) θ U := by
    have h₁ := hasDerivAt_sineRay hg.le hg' hω (φ U) t
    have h₂ := codedSlope_hasDerivAt_next ha₀ hg.le hg' hc hc'.le hbc hpoly w η U t
    simp only [codedSlope_eq_sineRay ha₀ hbc hpoly] at h₂
    apply h₁.unique
    simpa only [W, θ, codedSlope_eq_sineRay ha₀ hbc hpoly] using h₂
  apply le_trans _ (hsub ω (φ I) (φ J) hω s 0 r hr)
  apply measure_mono
  rintro t ⟨ht,hd,hval⟩
  refine ⟨ht,?_,?_⟩
  · simp only [codedSlope_eq_sineRay ha₀ hbc hpoly] at hval
    simpa only [sub_zero] using hval
  · have herr := head_difference_error (truncatedSlope_tail d a a₀ (W t) θ I hh.le hh' n)
      (truncatedSlope_tail d a a₀ (W t) θ J hh.le hh' n)
    change (2*(1-h)⁻¹+1)*h^n < |truncatedSlope d a a₀ h (W t) θ I n -
        truncatedSlope d a a₀ h (W t) θ J n| at hd
    have hsep : h^n < |codedSlope d a a₀ h (W t) θ I - codedSlope d a a₀ h (W t) θ J| := by
      linarith only [hd,herr]
    apply (mul_le_mul_of_nonneg_right (min_le_right 1 L) (pow_nonneg hh.le n)).trans_lt
    change L*h^n < |slopeRay g ω (φ I) t - slopeRay g ω (φ J) t|
    rw [hray,hray,← mul_sub, abs_mul, abs_of_pos hL]
    exact mul_lt_mul_of_pos_left hsep hL

theorem offDiagonal_prefix_collision {p d : ℕ} {a : ℕ → ℝ} {a₀ b c g : ℝ} (ha₀ : a₀ ≠ 0)
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w η : ℕ → ℝ) (I J : ℕ → Fin p) (s r : ℝ), 0 ≤ r →
      volume {t ∈ Icc s (s+1) | let W := fun k => w k+t*b^k
        let θ := fun k => η k+Real.pi/2
        (2*(1-g*c)⁻¹+1)*(g*c)^n <
          |truncatedSlope d a a₀ (g*c) W θ I n - truncatedSlope d a a₀ (g*c) W θ J n| ∧
          |codedSlope d a a₀ g W η I - codedSlope d a a₀ g W η J| ≤ r} ≤ ENNReal.ofReal (C*r) := by
  obtain ⟨C,hC,_,H⟩ := offDiagonal_prefix_collision_rate (p:=p) ha₀ hg hg' hc hc' hbc hpoly n
  exact ⟨C,hC,H⟩

/-- Iteration of the one-block energy inequality along a prescribed status
word. At the geometric test radii the suffix energy is the one associated
with the shorter word. -/
theorem prescribed_status_energy (E : List Bool → ℝ) (A : Bool → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ s, 1 ≤ A s) (hbase : E [] ≤ C)
    (hstep : ∀ s v, E (s::v) ≤ C + A s * E v) (v : List Bool) :
    E v ≤ C*(v.length+1 : ℝ)*(v.map A).prod := by
  have hprod (v : List Bool) : 1 ≤ (v.map A).prod := by
    induction v with
    | nil => simp
    | cons s v ih => simpa using one_le_mul_of_one_le_of_one_le (hA s) ih
  induction v with
  | nil => simpa using hbase
  | cons s v ih =>
    have hneg := (hstep s v).trans (add_le_add_right (mul_le_mul_of_nonneg_left ih
      (zero_le_one.trans (hA s))) C)
    apply hneg.trans
    have hgain := mul_le_mul_of_nonneg_left (hprod (s::v)) hC
    simp only [List.map_cons,List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at hgain ⊢
    linarith only [hgain]

/-- A full pair estimate for first-disagreeing codes on all translated unit
slices. The constants are uniform over the whole family of deterministic phase
strings, all initial real lifts, and both completions. -/
def HasPairExponent {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ b g s : ℝ) :=
  ∃ K : ℝ, 0 < K ∧ ∀ (w η : ℕ → ℝ) (I J : ℕ → Fin p), I 0 ≠ J 0 →
    ∀ u r : ℝ, 0 < r → r ≤ 1 → volume {t ∈ Icc u (u+1) |
      |codedSlope d a a₀ g (fun k => w k+t*b^k) η I -
        codedSlope d a a₀ g (fun k => w k+t*b^k) η J| ≤ r} ≤ ENNReal.ofReal (K*r^s)

/-- Splitting the pair according to its first derivative gives a positive
sublevel exponent at the preceding derivative index. This weaker descent
uses a single physical slice and works with no stationary averaging. -/
theorem pair_exponent_descent {p d : ℕ} {a : ℕ → ℝ} {a₀ b c g s : ℝ} (ha₀ : a₀ ≠ 0)
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c ≤ 1)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0)
    (hnext : HasPairExponent (p := p) d a a₀ b (g*c) s) :
    HasPairExponent (p := p) d a a₀ b g (min (1/2) (s/4)) := by
  let L := 2*Real.pi*c
  let l := min 1 L
  let h := g*c
  let M := (1-g)⁻¹*(2*Real.pi)^2
  let C := 4*(2*(M+M)+1)
  have hM : 0 ≤ M := mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hg'.le)) (sq_nonneg _)
  have hL : 0 < L := by dsimp [L]; positivity
  have hl : 0 < l := lt_min zero_lt_one hL
  have hC : 0 < C := by dsimp [C]; linarith
  obtain ⟨K,hK,hbound⟩ := hnext
  refine ⟨K+C/l^2, add_pos hK (div_pos hC (sq_pos_of_pos hl)), ?_⟩
  intro w η I J hIJ u r hr hr'
  let δ := r ^ (1/4:ℝ)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hr _
  have hδ' : δ ≤ 1 := Real.rpow_le_one hr.le hr' (by norm_num)
  let W (t : ℝ) (k : ℕ) := w k + t*b^k
  let θ (k : ℕ) := η k + Real.pi/2
  let f (t : ℝ) := codedSlope d a a₀ g (W t) η I - codedSlope d a a₀ g (W t) η J
  let F (t : ℝ) := codedSlope d a a₀ h (W t) θ I - codedSlope d a a₀ h (W t) θ J
  let df (t : ℝ) := L * F t
  let ω (k : ℕ) := 2*Real.pi*c^(k+1)
  let φ (U : ℕ → Fin p) (k : ℕ) := 2*Real.pi*pathState d a a₀ w U (k+1) 0 + η k
  have hder (t : ℝ) : HasDerivAt f (df t) t := by
    dsimp only [df,F]
    rw [mul_sub]
    exact (codedSlope_hasDerivAt_next ha₀ hg.le hg' hc hc' hbc hpoly w η I t).fun_sub
      (codedSlope_hasDerivAt_next ha₀ hg.le hg' hc hc' hbc hpoly w η J t)
  have hω (k : ℕ) : |ω k| ≤ 2*Real.pi := by
    dsimp [ω]
    rw [abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hc.le hc')
  have heq (t : ℝ) : df t = slopeRay g ω (φ I) t - slopeRay g ω (φ J) t := by
    apply (hder t).unique
    dsimp only [f,W]
    simp only [codedSlope_eq_sineRay ha₀ hbc hpoly]
    exact (hasDerivAt_sineRay hg.le hg' hω (φ I) t).sub (hasDerivAt_sineRay hg.le hg' hω (φ J) t)
  have hLip (x z : ℝ) : |df x-df z| ≤ (M+M)*|x-z| := by
    rw [heq,heq, show (slopeRay g ω (φ I) x - slopeRay g ω (φ J) x) -
      (slopeRay g ω (φ I) z - slopeRay g ω (φ J) z) =
      (slopeRay g ω (φ I) x - slopeRay g ω (φ I) z) - (slopeRay g ω (φ J) x - slopeRay g ω (φ J) z) by ring]
    apply (abs_sub _ _).trans
    simpa only [M,add_mul] using add_le_add (slopeRay_lipschitz hg.le hg' hω (φ I) x z)
      (slopeRay_lipschitz hg.le hg' hω (φ J) x z)
  have hcov : {t ∈ Icc u (u+1) | |f t| ≤ r} ⊆ {t ∈ Icc u (u+1) | |F t| ≤ δ} ∪
      transverseBand f df u (u+1) 0 r (l*δ) := by
    rintro t ⟨ht, hv⟩
    by_cases h₀ : |F t| ≤ δ
    · exact Or.inl ⟨ht,h₀⟩
    · refine Or.inr ⟨ht, by simpa using hv, ?_⟩
      change l*δ < |L*F t|
      rw [abs_mul,abs_of_pos hL]
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hδ.le).trans_lt
        (mul_lt_mul_of_pos_left (lt_of_not_ge h₀) hL)
  have hb := hbound w θ I J hIJ u δ hδ hδ'
  have ht := quantitative_transverse_sublevel (add_nonneg hM hM) (mul_pos hl hδ)
    (mul_le_one₀ (min_le_left _ _) hδ.le hδ') f df hder hLip u 0 r hr.le
  apply (measure_mono hcov).trans ((measure_union_le _ _).trans ((add_le_add hb ht).trans ?_))
  have hδs : δ^s = r^(s/4) := by dsimp [δ]; rw [← Real.rpow_mul hr.le]; congr 1; ring
  have hδr : r/δ^2 = r^(1/2:ℝ) := by
    dsimp [δ]
    have hsq : (r^(1/4:ℝ))^2 = r^(1/2:ℝ) := by
      rw [← Real.rpow_natCast (r^(1/4:ℝ)) 2, ← Real.rpow_mul hr.le]
      norm_num
    rw [hsq]
    calc
      _ = r^(1:ℝ)/r^(1/2:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hr]; norm_num
  change ENNReal.ofReal (K*δ^s) + ENNReal.ofReal ((C/(l*δ)^2)*r) ≤ _
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), hδs,
    show (C/(l*δ)^2)*r = (C/l^2)*(r/δ^2) by ring, hδr]
  apply ENNReal.ofReal_le_ofReal
  rw [add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr'
    (min_le_right _ _)) hK.le) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr'
      (min_le_left _ _)) (div_nonneg hC.le (sq_nonneg _)))

/-- For every admissible original slope contraction `γ`, the actual polynomial
predecessor tree has some positive pair exponent, uniformly in all phases. -/
theorem positive_pair_exponent {p d : ℕ} {a : ℕ → ℝ} {a₀ b c γ : ℝ}
    (hp : 2 ≤ p) (ha₀ : |a₀| = p) (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ) (hγ' : γ < 1)
    (hbc : b*c = 1) (hpoly : a₀ + b * ∑ k ∈ Finset.range d, a k*b^k = 0) :
    ∃ s : ℝ, 0 < s ∧ HasPairExponent (p := p) d a a₀ b γ s := by
  have ha₀' : a₀ ≠ 0 := abs_pos.mp (ha₀.symm ▸ (by exact_mod_cast (show 0 < p by omega)))
  obtain ⟨N,K,hK,hbound⟩ := (coded_predecessor_initialization hp ha₀ hc hc' hγ.le hbc hpoly).exists
  have hinit : ∃ s : ℝ, 0 < s ∧ HasPairExponent (p := p) d a a₀ b (γ*c^N) s := by
    refine ⟨1,zero_lt_one,K,hK,?_⟩
    intro w η I J hIJ u r hr _
    simpa using hbound w η I J hIJ u r hr.le
  suffices H : ∀ n, (∃ s : ℝ, 0 < s ∧ HasPairExponent (p := p) d a a₀ b (γ*c^n) s) →
      ∃ s : ℝ, 0 < s ∧ HasPairExponent (p := p) d a a₀ b γ s from H N hinit
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rintro ⟨s,hs,h⟩
    apply ih
    have hg' : γ*c^n < 1 := (mul_le_of_le_one_right hγ.le (pow_le_one₀ hc.le hc'.le)).trans_lt hγ'
    rw [pow_succ, ← mul_assoc] at h
    exact ⟨min (1/2) (s/4),lt_min (by norm_num) (by positivity),
      pair_exponent_descent ha₀' (mul_pos hγ (pow_pos hc n)) hg' hc hc'.le hbc hpoly h⟩

/-- The normalized sum over the `p` real lifts of a predecessor coordinate. -/
def branchAverage (p : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (p:ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (((i:ℝ)+y)/p)

private theorem periodic_branchAverage {p : ℕ} (hp : 0 < p) {f : ℝ → ℝ}
    (hf : Function.Periodic f 1) : Function.Periodic (branchAverage p f) 1 := by
  intro y
  let A (i : ℕ) := f (((i:ℝ)+y)/p)
  have hpr : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A p = A 0 := by
    dsimp [A]
    rw [Nat.cast_zero,zero_add,add_div,div_self hpr,add_comm,hf]
  have h := (Finset.sum_range_succ' A p).symm.trans (Finset.sum_range_succ A p)
  rw [hA] at h
  unfold branchAverage
  congr 1
  have he (i : ℕ) : f (((i:ℝ)+(y+1))/p) = A (i+1) := by
    dsimp [A]
    rw [Nat.cast_succ]
    congr 2
    ring
  simp_rw [he]
  exact add_right_cancel h

private theorem bounded_intervalIntegrable {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (s t : ℝ) : IntervalIntegrable f volume s t := by
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const (a := s) (b := t) (μ := volume) (c := M)).def'.mono' hf.aestronglyMeasurable
  exact .of_forall (fun x => by simpa only [Real.norm_eq_abs] using hM x)

/-- The fresh coordinate is Haar modulo one after averaging the actual `p`
predecessor choices and the last central coordinate. `u` is the offset from
the other, fixed central coordinates and `q` is the signed, nonzero leading
coefficient. The test can be any bounded measurable periodic real function. -/
theorem predecessor_coordinate_stationary {p : ℕ} (hp : 0 < p) {q : ℤ} (hq : q ≠ 0)
    (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (hper : Function.Periodic f 1)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    (∫ x in (0:ℝ)..1, branchAverage p f (u+(q:ℝ)*x)) = ∫ x in (0:ℝ)..1, f x := by
  have hp₀ : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq₀ : (q:ℝ) ≠ 0 := by exact_mod_cast hq
  have hterm (i : ℕ) (s t : ℝ) : IntervalIntegrable (fun x : ℝ => f (((i:ℝ)+x)/p)) volume s t :=
    bounded_intervalIntegrable (hf.comp ((measurable_const.add measurable_id).div_const _)) (fun _ => hM _) _ _
  have havg (s t : ℝ) : IntervalIntegrable (branchAverage p f) volume s t := by
    apply IntervalIntegrable.const_mul
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum (Finset.range p) (fun i _ => hterm i s t)
  have hw := (periodic_branchAverage hp hper).intervalIntegral_add_zsmul_eq q u havg
  have hi := (periodic_branchAverage hp hper).intervalIntegral_add_eq u 0
  have hperiod : (∫ x in u..u+(q:ℝ), branchAverage p f x) =
      (q:ℝ)*(∫ x in (0:ℝ)..1, branchAverage p f x) := by
    simp only [zsmul_eq_mul, mul_one, zero_add] at hw hi
    rw [hw,hi]
  rw [intervalIntegral.integral_comp_add_mul _ hq₀, mul_zero, add_zero, mul_one, hperiod,
    smul_eq_mul,inv_mul_cancel_left₀ hq₀]
  unfold branchAverage
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun i _ => hterm i 0 1)]
  have hchange (i : ℕ) : (∫ x in (0:ℝ)..1, f (((i:ℝ)+x)/p)) = (p:ℝ)*
      ∫ x in (i:ℝ)/p..((i+1:ℕ):ℝ)/p, f x := by
    simp only [add_div,Nat.cast_succ,intervalIntegral.integral_comp_add_div f hp₀,zero_div,add_zero,
      smul_eq_mul]
  simp_rw [hchange]
  rw [← Finset.mul_sum, inv_mul_cancel_left₀ hp₀,
    intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k:ℝ)/p)
      (fun _ _ => bounded_intervalIntegrable hf hM _ _)]
  simp [hp₀]

private theorem unitLaw_integral (f : ℝ → ℝ) : (∫ x, f x ∂unitLaw) = ∫ x in (0:ℝ)..1, f x := by
  rw [unitLaw,intervalIntegral.integral_of_le zero_le_one,integral_Ico_eq_integral_Ioc]

private theorem unitLaw_first_digit {p : ℕ} (hp : 0 < p) (i : Fin p) :
    unitLaw {x | uniformCode p hp x 0 = i} = ENNReal.ofReal (p:ℝ)⁻¹ := by
  simpa using uniformCode_cylinder_mass hp (fun _ => i) 1

private theorem first_digit_expectation {p : ℕ} (hp : 0 < p) (v : Fin p → ℝ) :
    (∫ x, v (uniformCode p hp x 0) ∂unitLaw) = (p:ℝ)⁻¹*∑ i, v i := by
  classical
  let E (i : Fin p) := {x | uniformCode p hp x 0 = i}
  have hm (i : Fin p) : MeasurableSet (E i) := measurableSet_eq_fun (measurable_uniformCode p hp 0) measurable_const
  have heq (x : ℝ) : v (uniformCode p hp x 0) = ∑ i : Fin p, (E i).indicator (fun _ => v i) x := by
    simp [E,Set.indicator_apply, eq_comm]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => (integrable_const (v i)).indicator (hm i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const _ (hm i),measureReal_def,unitLaw_first_digit hp,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- The fresh phase of the actual encoded predecessor step, reduced modulo one.
The real offset collects the retained central coordinates. -/
def freshPhase (p : ℕ) (hp : 0 < p) (q : ℤ) (u : ℝ) (z : ℝ × ℝ) : UnitAddCircle :=
  ↑((((uniformCode p hp z.2 0).val:ℝ) + (u+(q:ℝ)*z.1))/p)

private theorem measurable_freshPhase (p : ℕ) (hp : 0 < p) (q : ℤ) (u : ℝ) :
    Measurable (freshPhase p hp q u) := by
  apply AddCircle.measurable_mk'.comp
  apply Measurable.div_const
  exact ((measurable_of_countable (fun i : Fin p => (i.val:ℝ))).comp
    ((measurable_uniformCode p hp 0).comp measurable_snd)).add
    (measurable_const.add (measurable_const.mul measurable_fst))

/-- The law of the explicit predecessor phase is circle Haar for any offset
and any nonzero signed leading coefficient, as an equality of Borel measures. -/
theorem freshPhase_haar {p : ℕ} (hp : 0 < p) {q : ℤ} (hq : q ≠ 0) (u : ℝ) :
    (unitLaw.prod unitLaw).map (freshPhase p hp q u) = (volume : Measure UnitAddCircle) := by
  classical
  let ν := unitLaw.prod unitLaw
  let Y := freshPhase p hp q u
  have hY := measurable_freshPhase p hp q u
  ext S hS
  have hfin : (ν.map Y) S ≠ ⊤ := measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top _ _)).mp
  let H : UnitAddCircle → ℝ := S.indicator (fun _ => 1)
  let f (x : ℝ) := H (x : UnitAddCircle)
  have hH : Measurable H := measurable_const.indicator hS
  have hf : Measurable f := hH.comp AddCircle.measurable_mk'
  have hnorm (y : UnitAddCircle) : |H y| ≤ 1 := by by_cases h : y ∈ S <;> simp [H,h]
  have hper : Function.Periodic f 1 := by
    intro x
    dsimp only [f]
    congr 1
    simp
  have hleft : ((ν.map Y) S).toReal = ∫ z, H (Y z) ∂ν := by
    rw [Measure.map_apply hY hS]
    have hi := integral_indicator_one (μ := ν) (hY hS)
    change _ = ∫ z, H (Y z) ∂ν
    simpa [H, Y, measureReal_def, Set.indicator_apply] using hi.symm
  have hright : (volume S).toReal = ∫ x in (0:ℝ)..1, f x := by
    have hi := integral_indicator_one (μ := (volume:Measure UnitAddCircle)) hS
    have hc := UnitAddCircle.intervalIntegral_preimage 0 H
    simpa only [zero_add, f, measureReal_def] using hi.symm.trans hc.symm
  change ((ν.map Y) S).toReal = (volume S).toReal
  rw [hleft, hright]
  have hInt : Integrable (fun z => H (Y z)) ν :=
    (integrable_const (μ := ν) (1:ℝ)).mono' (hH.comp hY).aestronglyMeasurable
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hnorm (Y z))
  rw [integral_prod _ hInt]
  have he (t : ℝ) : (∫ x, H (Y (t,x)) ∂unitLaw) = branchAverage p f (u+(q:ℝ)*t) := by
    have hh := first_digit_expectation hp (fun i : Fin p => f (((i.val:ℝ)+(u+(q:ℝ)*t))/p))
    unfold branchAverage
    rw [← Fin.sum_univ_eq_sum_range]
    exact hh
  simp_rw [he]
  rw [unitLaw_integral]
  exact predecessor_coordinate_stationary hp hq u hf hper fun x => hnorm _

/-- Keeping all other central coordinates, the fresh coordinate remains Haar
and independent of the retained block. The shift `u x` can be any measurable
function of those coordinates, hence can include all intermediate polynomial
coefficients. The dropped coordinate and digit seed are independent uniforms. -/
theorem predecessor_block_stationary {X : Type*} [MeasurableSpace X] (m : Measure X)
    {p : ℕ} (hp : 0 < p) {q : ℤ} (hq : q ≠ 0) (u : X → ℝ) (hu : Measurable u) :
    (m.prod (unitLaw.prod unitLaw)).map (fun z => (z.1, freshPhase p hp q (u z.1) z.2)) =
      m.prod (volume : Measure UnitAddCircle) := by
  let F (z : X × (ℝ × ℝ)) := (z.1, freshPhase p hp q (u z.1) z.2)
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply AddCircle.measurable_mk'.comp
    apply Measurable.div_const
    exact ((measurable_of_countable (fun i : Fin p => (i.val:ℝ))).comp
      ((measurable_uniformCode p hp 0).comp (measurable_snd.comp measurable_snd))).add
      ((hu.comp measurable_fst).add (measurable_const.mul (measurable_fst.comp measurable_snd)))
  ext S hS
  change ((m.prod (unitLaw.prod unitLaw)).map F) S = _
  rw [Measure.map_apply hF hS, Measure.prod_apply (hF hS), Measure.prod_apply hS]
  apply lintegral_congr_ae (.of_forall _)
  intro x
  have hm := measurable_freshPhase p hp q (u x)
  have he := congrArg (fun μ : Measure UnitAddCircle => μ (Prod.mk x ⁻¹' S)) (freshPhase_haar hp hq (u x))
  rw [Measure.map_apply hm (measurable_prodMk_left hS)] at he
  exact he

private def pushLift (y : ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => y
  | n+1 => w n

private def offset (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) : ℝ :=
  -∑ k ∈ Finset.range d, (a k:ℝ)*w k

/-- A finite path read in the torus, continuing from inherited real lifts. The
integer polynomial is normalized to have constant coefficient `p > 0`. -/
def phaseHistory {p : ℕ} (d : ℕ) (a : ℕ → ℤ) :
    (n : ℕ) → (ℕ → ℝ) → (Fin n → Fin p) → (Fin n → UnitAddCircle)
  | 0, _, _ => Fin.elim0
  | n+1, w, v =>
    let y := (((v 0).val:ℝ) + offset d a w)/p
    Fin.cons (y:UnitAddCircle) (phaseHistory d a n (pushLift y w) (Fin.tail v))

/-- Expectation of an arbitrary test on the first `n` predecessor phases. -/
def phaseHistoryMean (p d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : ℕ → ℝ) (F : (Fin n → UnitAddCircle) → ℝ) :=
  (p:ℝ)⁻¹^n * ∑ v : Fin n → Fin p, F (phaseHistory d a n w v)

private theorem phaseHistoryMean_succ (p d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : ℕ → ℝ)
    (F : (Fin (n+1) → UnitAddCircle) → ℝ) :
    phaseHistoryMean p d a (n+1) w F = branchAverage p (fun y => phaseHistoryMean p d a n
      (pushLift y w) (fun xs => F (Fin.cons (y:UnitAddCircle) xs))) (offset d a w) := by
  let G (v : Fin (n+1) → Fin p) := F (phaseHistory d a (n+1) w v)
  let E := Fin.consEquiv (fun _ : Fin (n+1) => Fin p)
  have h := E.sum_comp G
  unfold phaseHistoryMean branchAverage
  rw [← Fin.sum_univ_eq_sum_range, ← Finset.mul_sum, ← mul_assoc, ← pow_succ',
    show (∑ v, F (phaseHistory d a (n+1) w v)) = ∑ z, G (E z) from h.symm, Fintype.sum_prod_type]
  congr 1

/-- Changing any inherited real lift by integers preserves *every* finite path
law, not only its last central block. The result holds for arbitrary tests
on the whole ordered torus path, including tests depending jointly on steps. -/
theorem phaseHistoryMean_integer_shift {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ)
    (w : ℕ → ℝ) (k : ℕ → ℤ) (F : (Fin n → UnitAddCircle) → ℝ) :
    phaseHistoryMean p d a n (fun l => w l+(k l:ℝ)) F = phaseHistoryMean p d a n w F := by
  induction n generalizing w k with
  | zero => rfl
  | succ n ih =>
    rw [phaseHistoryMean_succ,phaseHistoryMean_succ]
    let G (y : ℝ) := phaseHistoryMean p d a n (pushLift y w) (fun xs => F (Fin.cons (y:UnitAddCircle) xs))
    let j (l : ℕ) : ℤ := match l with | 0 => 0 | l+1 => k l
    have hshift (y : ℝ) : pushLift y (fun l => w l+(k l:ℝ)) = fun l => pushLift y w l+(j l:ℝ) := by
      funext l
      cases l <;> simp [pushLift,j]
    have heq : (fun y => phaseHistoryMean p d a n (pushLift y (fun l => w l+(k l:ℝ)))
        (fun xs => F (Fin.cons (y:UnitAddCircle) xs))) = G := by
      funext y
      rw [hshift]
      exact ih _ _ _
    have hper : Function.Periodic G 1 := by
      intro y
      let J : ℕ → ℤ := fun l => if l = 0 then 1 else 0
      have hstate : pushLift (y+1) w = fun l => pushLift y w l + (J l:ℝ) := by
        funext l
        cases l <;> simp [J,pushLift]
      change phaseHistoryMean p d a n (pushLift (y+1) w) (fun xs => F (Fin.cons ((y+1:ℝ):UnitAddCircle) xs)) = _
      rw [hstate, AddCircle.coe_add_period 1 y, ih]
    let K : ℤ := -∑ l ∈ Finset.range d, a l*k l
    have hK : offset d a (fun l => w l+(k l:ℝ)) = offset d a w+(K:ℝ) := by
      dsimp [offset,K]
      push_cast
      simp only [mul_add,Finset.sum_add_distrib]
      ring
    rw [heq,hK]
    simpa using (periodic_branchAverage hp hper).int_mul K (offset d a w)

private theorem prefix_expectation {p : ℕ} (hp : 0 < p) (n : ℕ) (G : (Fin n → Fin p) → ℝ) :
    (∫ x, G (fun i : Fin n => uniformCode p hp x i) ∂unitLaw) = (p:ℝ)⁻¹^n * ∑ v, G v := by
  classical
  let E (v : Fin n → Fin p) := {x : ℝ | ∀ i < n, uniformCode p hp x i = extendWord hp v i}
  have hm (v : Fin n → Fin p) : MeasurableSet (E v) := measurable_prefix_event hp _ n
  have hv (x : ℝ) (v : Fin n → Fin p) : x ∈ E v ↔ (fun i : Fin n => uniformCode p hp x i) = v := by
    constructor
    · intro hx
      funext i
      simpa [extendWord, i.isLt] using hx i i.isLt
    · intro h i hi
      simpa [extendWord,hi] using congrFun h ⟨i,hi⟩
  have he (x : ℝ) : G (fun i : Fin n => uniformCode p hp x i) =
      ∑ v, (E v).indicator (fun _ => G v) x := by simp [Set.indicator_apply, hv,eq_comm]
  simp_rw [he]
  rw [integral_finsetSum _ (fun v _ => (integrable_const (G v)).indicator (hm v)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [integral_indicator_const _ (hm v),measureReal_def,
    show unitLaw (E v) = ENNReal.ofReal ((p:ℝ)⁻¹^n) from uniformCode_cylinder_mass hp _ n,
    ENNReal.toReal_ofReal (by positivity),smul_eq_mul]

private theorem predecessor_eq_push {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (i : Fin p) :
    predecessor d (fun k => (a k:ℝ)) p w i = pushLift (((i.val:ℝ)+offset d a w)/p) w := by
  funext k
  cases k with
  | zero => simp [predecessor,pushLift,offset,sub_eq_add_neg]
  | succ k => rfl

private theorem phaseHistory_eval {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : ℕ → ℝ)
    (I : ℕ → Fin p) (k : Fin n) : phaseHistory d a n w (fun i => I i) k =
      (↑(pathState d (fun i => (a i:ℝ)) p w I (k.val+1) 0) : UnitAddCircle) := by
  induction n generalizing w I with
  | zero => exact k.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [phaseHistory,Fin.cons_zero,Fin.val_zero,pathState,predecessor_eq_push,pushLift]
    · let w' := pushLift ((((I 0).val:ℝ)+offset d a w)/p) w
      have hx := ih w' (fun i => I (i+1)) j
      have hpath := congrFun (pathState_append d (fun i => (a i:ℝ)) (p:ℝ) w I 1 (j.val+1)) 0
      change pathState _ _ _ w I (1+(j.val+1)) 0 = _ at hpath
      rw [show 1+(j.val+1) = j.succ.val+1 by simp [Nat.add_comm 1]] at hpath
      rw [hpath]
      simpa only [phaseHistory, Fin.cons_succ, Fin.tail_def, Fin.val_succ,Fin.val_zero, pathState, predecessor_eq_push,
        Nat.add_comm 1, w'] using hx

/-- The entire circle-valued conditional past driven by the actual, uniform
base-`p` code. -/
@[expose] def observedPast {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (x : ℝ) (i : ℕ) : UnitAddCircle :=
  ↑(pathState d (fun k => (a k:ℝ)) p w (uniformCode p hp x) (i+1) 0)

theorem measurable_observedPast {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) :
    Measurable (observedPast hp d a w) := by
  apply measurable_pi_lambda
  intro i
  apply AddCircle.measurable_mk'.comp
  exact measurable_pathState d (fun k => (a k:ℝ)) (p:ℝ) (fun _ => w) (uniformCode p hp)
    (fun _ => measurable_const) (measurable_uniformCode p hp) (i+1) 0

private theorem observed_prefix_expectation {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ)
    (n : ℕ) (F : (Fin n → UnitAddCircle) → ℝ) :
    (∫ x, F (fun i : Fin n => observedPast hp d a w x i) ∂unitLaw) = phaseHistoryMean p d a n w F := by
  have e (x : ℝ) : (fun i : Fin n => observedPast hp d a w x i) =
      phaseHistory d a n w (fun i : Fin n => uniformCode p hp x i) := by
    funext k
    exact (phaseHistory_eval d a n w _ k).symm
  simp_rw [e]
  exact prefix_expectation hp n (fun v => F (phaseHistory d a n w v))

/-- Equality of the Borel probability laws of the entire infinite past under
any integer change of the central lift. This applies to all measurable suffix
restrictions used in the multiblock recursion. -/
theorem observedPast_integer_shift {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (k : ℕ → ℤ) :
    unitLaw.map (observedPast hp d a (fun l => w l+(k l:ℝ))) = unitLaw.map (observedPast hp d a w) := by
  let P (u : ℕ → ℝ) := observedPast hp d a u
  have hP (u : ℕ → ℝ) : Measurable (P u) := measurable_observedPast hp d a u
  let w' (l : ℕ) := w l+(k l:ℝ)
  change unitLaw.map (P w') = unitLaw.map (P w)
  apply ext_of_generate_finite (measurableCylinders (fun _ : ℕ => UnitAddCircle))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro B hB
    obtain ⟨S,T,hT,rfl⟩ := (mem_measurableCylinders _).mp hB
    let n := S.sup id+1
    let ι (i : S) : Fin n := ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
    let F (v : Fin n → UnitAddCircle) := T.indicator (fun _ => (1:ℝ)) (fun i : S => v (ι i))
    have htest (u : ℕ → ℝ) : ((unitLaw.map (P u)) (cylinder S T)).toReal = phaseHistoryMean p d a n u F := by
      rw [Measure.map_apply (hP u) hT.cylinder,← observed_prefix_expectation hp]
      have hi := integral_indicator_one (μ := unitLaw) ((hP u) hT.cylinder)
      change _ = ∫ x, F (fun i : Fin n => observedPast hp d a u x i) ∂unitLaw
      rw [← measureReal_def,← hi]
      apply integral_congr_ae (.of_forall _)
      intro x
      classical
      change (if (P u x) ∈ cylinder S T then (1:ℝ) else 0) =
        (if (fun i : S => observedPast hp d a u x (ι i).val) ∈ T then 1 else 0)
      rfl
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [htest,htest]
    exact phaseHistoryMean_integer_shift hp d a n w k F
  · rw [Measure.map_apply (hP w') MeasurableSet.univ,Measure.map_apply (hP w) MeasurableSet.univ]
    simp

/-- Closed-radius collision mass of a pair of finite real-line measures. -/
@[expose] def collision (μ ν : Measure ℝ) (R : ℝ) : ℝ := (μ.prod ν).real {v : ℝ × ℝ | |v.1-v.2| ≤ R}

open Weierstrass.Partition in
set_option maxHeartbeats 1200000 in
/-- Cross collisions cost at most three times the average of the two diagonal
collision probabilities, at exactly the same radius. Applied to the neighbors
of a block, the constant costs only a factor three per block. -/
theorem collision_cross_le (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R) : collision μ ν R ≤ (3/2)*(collision μ μ R+collision ν ν R) := by
  let a (i : ℤ) := μ.real (cell R i)
  let b (i : ℤ) := ν.real (cell R i)
  let qa (i : ℤ) := a i*a i
  let qb (i : ℤ) := b i*b i
  let tri (i : ℤ) := (cell R (i-1) ∪ cell R i) ∪ cell R (i+1)
  let A (i : ℤ) := cell R i ×ˢ tri i
  have hm (i : ℤ) : MeasurableSet (A i) :=
    (cell_measurable R i).prod (((cell_measurable R _).union (cell_measurable R _)).union (cell_measurable R _))
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp (cell_disjoint hR hij) hz.1 hz'.1
  have hcover : {v : ℝ × ℝ | |v.1-v.2| ≤ R} ⊆ ⋃ i, A i := by
    rintro ⟨x,y⟩ hxy
    have hx : x ∈ cell R ⌊x/R⌋ := (mem_cell_iff hR).mpr rfl
    refine Set.mem_iUnion.mpr ⟨⌊x/R⌋, hx, ball_subset_triple hx ?_⟩
    change |x-y| ≤ R at hxy
    obtain ⟨hl,hr⟩ := abs_le.mp hxy
    exact ⟨by linarith, by linarith⟩
  have hA := hasSum_disjoint (μ.prod ν) A hm hd
  have ha : Summable qa := summable_squares μ hR
  have hb : Summable qb := summable_squares ν hR
  have hshift (k : ℤ) : HasSum (fun i : ℤ => qb (i+k)) (∑' i, qb i) :=
    ((Equiv.addRight k).hasSum_iff).mpr hb.hasSum
  have hthree := (((ha.hasSum.mul_left 3).add (hshift (-1))).add hb.hasSum).add (hshift 1)
  have hcost (i : ℤ) : (μ.prod ν).real (A i) ≤
      (1/2)*(3*qa i+qb (i + -1)+qb i+qb (i+1)) := by
    have h₁ := measureReal_union_le (μ := ν) (cell R (i-1) ∪ cell R i) (cell R (i+1))
    have h₂ := measureReal_union_le (μ := ν) (cell R (i-1)) (cell R i)
    have ht : ν.real (tri i) ≤ b (i-1)+b i+b (i+1) := by dsimp [b,tri]; linarith
    change (μ.prod ν).real (cell R i ×ˢ tri i) ≤ _
    rw [measureReal_prod_prod]
    change a i*ν.real (tri i) ≤ _
    apply (mul_le_mul_of_nonneg_left ht measureReal_nonneg).trans
    dsimp only [qa,qb]
    rw [← sub_eq_add_neg]
    nlinarith [sq_nonneg (a i-b (i-1)),sq_nonneg (a i-b i),sq_nonneg (a i-b (i+1))]
  have hsum := hasSum_le hcost hA (hthree.mul_left (1/2))
  have hμ : (∑' i, qa i) ≤ collision μ μ R := square_tsum_le μ hR
  have hν : (∑' i, qb i) ≤ collision ν ν R := square_tsum_le ν hR
  have hμν : collision μ ν R ≤ (μ.prod ν).real (⋃ i, A i) := measureReal_mono hcover
  linarith

/-- Symmetric prefix-neighbor relations with row sums bounded by `D` count at
most `3*D` diagonal collision energies. Prefix measures may already be
restricted to any prescribed future status word. -/
theorem neighbor_collision_bound {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] {R : ℝ} (hR : 0 < R) (M : ι → ι → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hsym : ∀ i j, M i j = M j i)
    (D : ℝ) (hD : ∀ i, ∑ j, M i j ≤ D) :
    ∑ i, ∑ j, M i j * collision (μ i) (μ j) R ≤
      3*D*∑ i, collision (μ i) (μ i) R := by
  let C (i : ι) := collision (μ i) (μ i) R
  have hs : (∑ i, ∑ j, M i j*C j) = ∑ i, ∑ j, M i j*C i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by rw [hsym i j]))
  have hdiag : (∑ i, ∑ j, M i j*C i) ≤ D*∑ i, C i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hD i) measureReal_nonneg
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => mul_le_mul_of_nonneg_left (collision_cross_le (μ i) (μ j) hR) (hM i j)))
  have he (i j : ι) : M i j*((3/2)*(collision (μ i) (μ i) R+collision (μ j) (μ j) R)) =
      (3/2)*(M i j*C i+M i j*C j) := by dsimp [C]; ring
  simp_rw [he,← Finset.mul_sum,Finset.sum_add_distrib] at h
  rw [hs] at h
  change _ ≤ 3*D*∑ i, C i
  linarith

/-- The seed with prescribed initial digits and a variable suffix seed. -/
@[expose] def prefixSeed {p : ℕ} (I : ℕ → Fin p) (k : ℕ) (x : ℝ) :=
  ((prefixAddress I k:ℝ)+x)/(p:ℝ)^k

theorem measurable_prefixSeed {p : ℕ} (I : ℕ → Fin p) (k : ℕ) : Measurable (prefixSeed I k) :=
  (measurable_const.add measurable_id).div_const _

/-- Exact conditional change of variables on an arbitrary finite code cylinder.
This equality of measures applies to suffix events involving infinitely many
digits and to restrictions by a later block status. -/
theorem restrict_code_prefix {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ) :
    unitLaw.restrict {x | ∀ n < k, uniformCode p hp x n = I n} =
      ENNReal.ofReal ((p:ℝ)⁻¹^k) • unitLaw.map (prefixSeed I k) := by
  let P := (p:ℝ)^k
  let N := (prefixAddress I k:ℝ)
  let H := Ico (N/P) ((N+1)/P)
  have hP : 0 < P := pow_pos (by exact_mod_cast hp) _
  have hE : prefixSeed I k ⁻¹' H = Ico 0 1 := by
    ext x
    simp only [prefixSeed, H, P, N, Set.mem_preimage, Set.mem_Ico, div_le_div_iff_of_pos_right hP,
      div_lt_div_iff_of_pos_right hP]
    constructor <;> rintro ⟨hl,hr⟩ <;> constructor <;> linarith
  have hmap (B : Set ℝ) : volume (prefixSeed I k ⁻¹' B) = ENNReal.ofReal P * volume B := by
    change volume ((N+·) ⁻¹' ((· * P⁻¹) ⁻¹' B)) = _ 
    rw [measure_preimage_add, Real.volume_preimage_mul_right (inv_ne_zero hP.ne'), inv_inv, abs_of_pos hP]
  ext B hB
  rw [unitLaw,Measure.restrict_restrict (measurable_prefix_event hp I k),prefix_interval,
    Measure.restrict_apply hB,Measure.smul_apply, Measure.map_apply (measurable_prefixSeed I k) hB,
    Measure.restrict_apply ((measurable_prefixSeed I k) hB),← hE, ← preimage_inter, hmap]
  change volume (B ∩ H) = ENNReal.ofReal ((p:ℝ)⁻¹^k) * (ENNReal.ofReal P * volume (B ∩ H))
  rw [inv_pow,← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hP.le),inv_mul_cancel₀ hP.ne',
    ENNReal.ofReal_one,one_mul]

theorem prefixSeed_codes {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ)
    {x : ℝ} (hx : x ∈ Ico 0 1) :
    (∀ i < k, uniformCode p hp (prefixSeed I k x) i = I i) ∧
    (∀ i, uniformCode p hp (prefixSeed I k x) (k+i) = uniformCode p hp x i) := by
  have hP : 0 < (p:ℝ)^k := pow_pos (by exact_mod_cast hp) _
  have hmem : prefixSeed I k x ∈ Ico ((prefixAddress I k:ℝ)/(p:ℝ)^k)
      (((prefixAddress I k:ℝ)+1)/(p:ℝ)^k) := by
    exact ⟨(div_le_div_iff_of_pos_right hP).mpr (le_add_of_nonneg_right hx.1),
      (div_lt_div_iff_of_pos_right hP).mpr (add_lt_add_right hx.2 _)⟩
  rw [← prefix_interval hp I k] at hmem
  refine ⟨hmem.1,?_⟩
  intro i
  apply Fin.ext
  have hpow : (p:ℝ)^(k+i+1)*prefixSeed I k x =
      (p:ℝ)^(i+1)*x+((p^(i+1)*prefixAddress I k : ℕ):ℝ) := by
    unfold prefixSeed
    push_cast
    rw [Nat.add_assoc, pow_add]
    field_simp
    ring
  change ⌊(p:ℝ)^(k+i+1)*prefixSeed I k x⌋₊ % p = ⌊(p:ℝ)^(i+1)*x⌋₊ % p
  rw [hpow,Nat.floor_add_natCast (mul_nonneg (by positivity) hx.1),pow_succ p,
    Nat.mul_right_comm (p^i) p (prefixAddress I k), Nat.add_mul_mod_self_right]

/-- The affine inverse on a fixed seed cylinder. -/
def suffixSeed {p : ℕ} (I : ℕ → Fin p) (k : ℕ) (x : ℝ) := (p:ℝ)^k*x-prefixAddress I k

private theorem measurable_suffixSeed {p : ℕ} (I : ℕ → Fin p) (k : ℕ) : Measurable (suffixSeed I k) :=
  (measurable_const.mul measurable_id).sub_const _

theorem restrict_code_prefix_suffix {p : ℕ} (hp : 0 < p) (I : ℕ → Fin p) (k : ℕ)
    {T : Set ℝ} (hT : MeasurableSet T) :
    (unitLaw.restrict {x | ∀ n < k, uniformCode p hp x n = I n}).restrict (suffixSeed I k ⁻¹' T) =
      ENNReal.ofReal ((p:ℝ)⁻¹^k) • (unitLaw.restrict T).map (prefixSeed I k) := by
  have hP : 0 < (p:ℝ)^k := pow_pos (by exact_mod_cast hp) _
  have hpre : prefixSeed I k ⁻¹' (suffixSeed I k ⁻¹' T) = T := by
    ext x
    change (p:ℝ)^k*(((prefixAddress I k:ℝ)+x)/(p:ℝ)^k)-prefixAddress I k ∈ T ↔ x ∈ T
    rw [mul_comm,div_mul_cancel₀ _ hP.ne',add_sub_cancel_left]
  rw [restrict_code_prefix hp,Measure.restrict_smul,Measure.restrict_map
    (measurable_prefixSeed I k) ((measurable_suffixSeed I k) hT),hpre]

/-- For one fixed prefix, give the conditional suffix any measurable
restriction. Its full slope law is exactly the translated, contracted slope
law of that suffix at the inherited state, with the cylinder mass factor. -/
theorem restricted_slope_prefix_law {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ)
    (w η : ℕ → ℝ) (I : ℕ → Fin p) (k : ℕ) {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1)
    {T : Set ℝ} (hT : MeasurableSet T) :
    ((unitLaw.restrict {x | ∀ n < k, uniformCode p hp x n = I n}).restrict
      (suffixSeed I k ⁻¹' T)).map (fun x => codedSlope d a a₀ g w η (uniformCode p hp x)) =
    ENNReal.ofReal ((p:ℝ)⁻¹^k) • ((unitLaw.restrict T).map (fun x =>
      codedSlope d a a₀ g (pathState d a a₀ w I k) (fun n => η (k+n)) (uniformCode p hp x))).map
        (fun y => truncatedSlope d a a₀ g w η I k + g^k*y) := by
  have hm (u θ : ℕ → ℝ) : Measurable (fun x => codedSlope d a a₀ g u θ (uniformCode p hp x)) := by
    have h := (measurable_sampledSlope hp d a a₀ 1 g u θ).comp (measurable_prodMk_left (x := (0:ℝ)))
    simpa only [sampledSlope,zero_mul,add_zero,Function.comp_def] using h
  have ha : Measurable (fun y : ℝ => truncatedSlope d a a₀ g w η I k + g^k*y) :=
    measurable_const.add (measurable_const.mul measurable_id)
  rw [restrict_code_prefix_suffix hp I k hT,Measure.map_smul,Measure.map_map (hm _ _) (measurable_prefixSeed I k),
    Measure.map_map ha (hm _ _)]
  congr 1
  apply Measure.map_congr
  have hunit : ∀ᵐ x ∂unitLaw.restrict T, x ∈ Ico (0:ℝ) 1 :=
    ae_mono Measure.restrict_le_self (ae_restrict_mem measurableSet_Ico)
  filter_upwards [hunit] with x hx
  obtain ⟨hi,hs⟩ := prefixSeed_codes hp I k hx
  let J := uniformCode p hp (prefixSeed I k x)
  change codedSlope d a a₀ g w η J = _
  have ht := truncatedSlope_congr d a a₀ g w η J I k hi
  have hJ := codedSlope_prefix_cut d a a₀ w η k hg hg' J
  change _ = truncatedSlope d a a₀ g w η J k + _ at hJ
  rw [ht,pathState_prefix d a a₀ w k hi,show (fun n => J (k+n)) = uniformCode p hp x from funext hs] at hJ
  exact hJ

/-- Translation and dilation preserve diagonal collisions at the corresponding
rescaled radius, including for subprobabilities restricted by future statuses. -/
theorem affine_collision (μ : Measure ℝ) [IsFiniteMeasure μ] (z R : ℝ) {g : ℝ} (hg : 0 < g) :
    collision (μ.map (fun x => z+g*x)) (μ.map (fun x => z+g*x)) R = collision μ μ (R/g) := by
  let f := fun x : ℝ => z+g*x
  have hm : Measurable f := measurable_const.add (measurable_const.mul measurable_id)
  have hb (r : ℝ) : MeasurableSet {v : ℝ × ℝ | |v.1-v.2| ≤ r} :=
    measurableSet_le (continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)) measurable_const
  unfold collision Measure.real
  rw [Measure.map_prod_map _ _ hm hm,Measure.map_apply (hm.prodMap hm) (hb _)]
  congr 2
  ext v
  change |z+g*v.1-(z+g*v.2)| ≤ R ↔ |v.1-v.2| ≤ R/g
  rw [show z+g*v.1-(z+g*v.2) = (v.1-v.2)*g by ring,abs_mul,abs_of_pos hg,le_div_iff₀ hg]

private theorem collision_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Measure ℝ) (ν : κ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ j, IsFiniteMeasure (ν j)] (R : ℝ) :
    collision (∑ i, μ i) (∑ j, ν j) R = ∑ i, ∑ j, collision (μ i) (ν j) R := by
  classical
  have left (s : Finset ι) (η : Measure ℝ) [IsFiniteMeasure η] :
      collision (∑ i ∈ s, μ i) η R = ∑ i ∈ s, collision (μ i) η R := by
    induction s using Finset.induction_on with
    | empty => simp [collision]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      unfold collision at ih ⊢
      rw [Measure.add_prod,measureReal_add_apply, ih]
  have right (s : Finset κ) (η : Measure ℝ) [IsFiniteMeasure η] :
      collision η (∑ j ∈ s, ν j) R = ∑ j ∈ s, collision η (ν j) R := by
    induction s using Finset.induction_on with
    | empty => simp [collision]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      unfold collision at ih ⊢
      rw [Measure.prod_add,measureReal_add_apply, ih]
  rw [left]
  exact Finset.sum_congr rfl (fun _ _ => right _ _)

private theorem collision_smul (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : ℝ} (hs : 0 ≤ s) (R : ℝ) :
    collision (ENNReal.ofReal s • μ) (ENNReal.ofReal s • ν) R = s^2*collision μ ν R := by
  simp only [collision,Measure.real,Measure.prod_smul_left,Measure.prod_smul_right,Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul,ENNReal.toReal_ofReal hs,pow_two,mul_assoc]

/-- One block of the collision recursion. Every child is a translated and
scaled subprobability with a common prefix weight. The first term consists
only of non-neighbor pairs when `M` is the symmetric neighbor indicator. -/
theorem block_collision_recursion {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] (z : ι → ℝ) {r h s : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hs : 0 ≤ s) (M : ι → ι → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hSym : ∀ i j, M i j = M j i) (D : ℝ) (hD : ∀ i, ∑ j, M i j ≤ D) :
    let μ := fun i => (ν i).map (fun x => z i+h*x)
    let parent := ∑ i, ENNReal.ofReal s • μ i
    collision parent parent r ≤ s^2 * (∑ i, ∑ j, (1-M i j)*collision (μ i) (μ j) r) +
      s^2 * (3*D*∑ i, collision (ν i) (ν i) (r/h)) := by
  intro μ parent
  let C (i j : ι) := collision (μ i) (μ j) r
  have hsfin (i : ι) : IsFiniteMeasure (ENNReal.ofReal s • μ i) :=
    ⟨by rw [Measure.smul_apply,smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have he (i j : ι) : C i j = (1-M i j)*C i j + M i j*C i j := by ring
  have hexpand : collision parent parent r = s^2*((∑ i, ∑ j, (1-M i j)*C i j) +
      ∑ i, ∑ j, M i j*C i j) := by
    dsimp only [parent]
    rw [collision_sum, mul_add, Finset.mul_sum,Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [collision_smul _ _ hs]
    rw [← mul_add]
    exact congrArg (s^2*·) (he i j)
  have hdiag := neighbor_collision_bound μ hr M hM hSym D hD
  have heq (i : ι) : collision (μ i) (μ i) r = collision (ν i) (ν i) (r/h) :=
    affine_collision _ _ _ hh
  simp_rw [heq] at hdiag
  rw [hexpand,mul_add]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hdiag (sq_nonneg s)) _

/-- For each first prefix, retain the original paths whose suffix seed lies
in its prescribed event. Empty events also encode a forbidden first status. -/
def selectedBlock {p : ℕ} (hp : 0 < p) (k : ℕ) (T : (Fin k → Fin p) → Set ℝ) : Set ℝ :=
  ⋃ v : Fin k → Fin p, (suffixSeed (extendWord hp v) k ⁻¹' T v) ∩
    {x | ∀ n < k, uniformCode p hp x n = extendWord hp v n}

/-- The actual restricted path measure decomposes as the common prefix weight
times all affine images of the prescribed child measures. -/
theorem selectedBlock_slope_law {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ)
    (w η : ℕ → ℝ) (k : ℕ) {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1)
    (T : (Fin k → Fin p) → Set ℝ) (hT : ∀ v, MeasurableSet (T v)) :
    (unitLaw.restrict (selectedBlock hp k T)).map
      (fun x => codedSlope d a a₀ g w η (uniformCode p hp x)) =
    ∑ v, ENNReal.ofReal ((p:ℝ)⁻¹^k) • ((unitLaw.restrict (T v)).map (fun x =>
      codedSlope d a a₀ g (pathState d a a₀ w (extendWord hp v) k) (fun n => η (k+n))
        (uniformCode p hp x))).map (fun y => truncatedSlope d a a₀ g w η (extendWord hp v) k + g^k*y) := by
  let I (v : Fin k → Fin p) := extendWord hp v
  let E (v : Fin k → Fin p) := suffixSeed (I v) k ⁻¹' T v
  let B (v : Fin k → Fin p) := {x | ∀ n < k, uniformCode p hp x n = I v n}
  have hE (v : Fin k → Fin p) : MeasurableSet (E v) := measurable_suffixSeed _ _ (hT v)
  have hB (v : Fin k → Fin p) : MeasurableSet (B v) := measurable_prefix_event _ _ _
  have hdis : Pairwise (Function.onFun Disjoint (fun v => E v ∩ B v)) := by
    intro v u hne
    apply Set.disjoint_left.mpr
    rintro x ⟨_,hx⟩ ⟨_,hy⟩
    apply hne
    funext i
    simpa [I,extendWord,i.isLt] using (hx i i.isLt).symm.trans (hy i i.isLt)
  have hm : Measurable (fun x => codedSlope d a a₀ g w η (uniformCode p hp x)) := by
    have h := (measurable_sampledSlope hp d a a₀ 1 g w η).comp (measurable_prodMk_left (x := (0:ℝ)))
    simpa only [sampledSlope,zero_mul,add_zero,Function.comp_def] using h
  change (unitLaw.restrict (⋃ v, E v ∩ B v)).map _ = _
  rw [Measure.restrict_iUnion hdis (fun v => (hE v).inter (hB v)),Measure.map_sum hm.aemeasurable,
    Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Measure.restrict_restrict (hE v)]
  exact restricted_slope_prefix_law hp d a a₀ w η (I v) k hg hg' (hT v)

/-- The one-block neighbor estimate for the polynomial-coded slope on an
actual event in path space. Only the non-neighbor term still needs integration
over the base; each diagonal term is evaluated at its true inherited state. -/
theorem selectedBlock_collision_recursion {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ)
    (w η : ℕ → ℝ) (k : ℕ) {g r : ℝ} (hg : 0 < g) (hg' : g < 1) (hr : 0 < r)
    (T : (Fin k → Fin p) → Set ℝ) (hT : ∀ v, MeasurableSet (T v))
    (M : (Fin k → Fin p) → (Fin k → Fin p) → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hSym : ∀ i j, M i j = M j i) (D : ℝ) (hD : ∀ i, ∑ j, M i j ≤ D) :
    let μ := (unitLaw.restrict (selectedBlock hp k T)).map
      (fun x => codedSlope d a a₀ g w η (uniformCode p hp x))
    let ν := fun v : Fin k → Fin p => (unitLaw.restrict (T v)).map (fun x =>
      codedSlope d a a₀ g (pathState d a a₀ w (extendWord hp v) k) (fun n => η (k+n))
        (uniformCode p hp x))
    let L := fun v : Fin k → Fin p => (ν v).map (fun y => truncatedSlope d a a₀ g w η (extendWord hp v) k + g^k*y)
    let s := (p:ℝ)⁻¹^k
    collision μ μ r ≤ s^2*(∑ i, ∑ j, (1-M i j)*collision (L i) (L j) r) +
      s^2*(3*D*∑ i, collision (ν i) (ν i) (r/g^k)) := by
  intro μ ν L s
  have he : μ = ∑ v, ENNReal.ofReal s • L v := selectedBlock_slope_law hp d a a₀ w η k hg.le hg' T hT
  rw [he]
  exact block_collision_recursion ν (fun v => truncatedSlope d a a₀ g w η (extendWord hp v) k)
    hr (pow_pos hg k) (by dsimp [s]; positivity) M hM hSym D hD

private theorem shifted_sine_periodic (θ : ℝ) :
    Function.Periodic (fun x : ℝ => Real.sin (2*Real.pi*x+θ)) 1 := by
  intro x
  change Real.sin (2*Real.pi*(x+1)+θ) = Real.sin (2*Real.pi*x+θ)
  rw [show 2*Real.pi*(x+1)+θ = (2*Real.pi*x+θ)+2*Real.pi by ring,Real.sin_add_two_pi]

private def phaseSine (θ : ℝ) : UnitAddCircle → ℝ := (shifted_sine_periodic θ).lift

private theorem continuous_phaseSine (θ : ℝ) : Continuous (phaseSine θ) :=
  continuous_coinduced_dom.mpr (Real.continuous_sin.comp ((continuous_const.mul continuous_id).add_const θ))

/-- The slope and its prefix observations are Borel tests of the circle-valued
past, so their conditional laws descend to torus central states. -/
def phaseSlope (g : ℝ) (η : ℕ → ℝ) (v : ℕ → UnitAddCircle) : ℝ :=
  ∑' i, g^i * phaseSine (η i) (v i)

theorem measurable_phaseSlope (g : ℝ) (η : ℕ → ℝ) : Measurable (phaseSlope g η) := by
  apply Measurable.tsum
  intro i
  exact measurable_const.mul ((continuous_phaseSine _).measurable.comp (measurable_pi_apply i))

theorem phaseSlope_observed {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ)
    (g x : ℝ) : phaseSlope g η (observedPast hp d a w x) =
      codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp x) := by
  unfold phaseSlope codedSlope
  apply tsum_congr
  intro i
  unfold phaseSine observedPast
  rw [Function.Periodic.lift_coe]

/-- The pushforward of the actual infinite slope is invariant under all
integer changes of the inherited base lifts, for arbitrary additive phases. -/
theorem slope_law_integer_shift {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ)
    (k : ℕ → ℤ) (g : ℝ) :
    unitLaw.map (fun x => codedSlope d (fun i => (a i:ℝ)) p g (fun i => w i+(k i:ℝ)) η (uniformCode p hp x)) =
    unitLaw.map (fun x => codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp x)) := by
  have h := congrArg (fun μ : Measure (ℕ → UnitAddCircle) => μ.map (phaseSlope g η))
    (observedPast_integer_shift hp d a w k)
  simpa only [Measure.map_map (measurable_phaseSlope g η) (measurable_observedPast hp d a _),
    Function.comp_def,phaseSlope_observed] using h

private theorem first_phase_injective {p : ℕ} (hp : 0 < p) (u : ℝ) :
    Function.Injective (fun i : Fin p => ((((i.val:ℝ)+u)/p:ℝ):UnitAddCircle)) := by
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp
  have hI (i : Fin p) : ((i.val:ℝ)+u)/p ∈ Ico (u/p) (u/p+1) := by
    constructor
    · exact (div_le_div_iff_of_pos_right hp').mpr (by have := Nat.cast_nonneg (α := ℝ) i.val; linarith)
    · rw [div_lt_iff₀ hp',add_mul,div_mul_cancel₀ _ hp'.ne',one_mul]
      have hv : (i.val:ℝ) < p := by exact_mod_cast i.isLt
      linarith
  intro i j h
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hI i) (hI j)).mp h
  apply Fin.ext
  have hc := (div_left_inj' hp'.ne').mp he
  exact_mod_cast add_right_cancel hc

theorem first_observed_phase_eq_iff {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (w : ℕ → ℝ) (x y : ℝ) :
    observedPast hp d a w x 0 = observedPast hp d a w y 0 ↔
      uniformCode p hp x 0 = uniformCode p hp y 0 := by
  simp only [observedPast,pathState,predecessor_eq_push,pushLift]
  exact (first_phase_injective hp _).eq_iff

/-- The conditional two-code law restricted to unlike first digits is a Borel
function of the torus state. This preserves first disagreement through each
fresh-state change of lift in the high-derivative initialization. -/
theorem first_disagreement_law_integer_shift {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (w η : ℕ → ℝ) (k : ℕ → ℤ) (g r : ℝ) :
    let B := fun u : ℕ → ℝ => {z : ℝ × ℝ | uniformCode p hp z.1 0 ≠ uniformCode p hp z.2 0 ∧
      |codedSlope d (fun i => (a i:ℝ)) p g u η (uniformCode p hp z.1) -
       codedSlope d (fun i => (a i:ℝ)) p g u η (uniformCode p hp z.2)| ≤ r}
    (unitLaw.prod unitLaw) (B (fun i => w i+(k i:ℝ))) = (unitLaw.prod unitLaw) (B w) := by
  intro B
  let P (u : ℕ → ℝ) := observedPast hp d a u
  let E := {z : (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle) | z.1 0 ≠ z.2 0 ∧
      |phaseSlope g η z.1-phaseSlope g η z.2| ≤ r}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_snd)).compl.inter
      (measurableSet_le (continuous_abs.measurable.comp (((measurable_phaseSlope g η).comp measurable_fst).sub
        ((measurable_phaseSlope g η).comp measurable_snd))) measurable_const)
  have he (u : ℕ → ℝ) : (unitLaw.prod unitLaw) (B u) =
      ((unitLaw.map (P u)).prod (unitLaw.map (P u))) E := by
    have hm := measurable_observedPast hp d a u
    rw [Measure.map_prod_map _ _ hm hm,Measure.map_apply (hm.prodMap hm) hE]
    congr 1
    ext z
    change _ ↔ ((observedPast hp d a u z.1 0 ≠ observedPast hp d a u z.2 0) ∧ _)
    simp only [ne_eq, first_observed_phase_eq_iff,Prod.map_fst,Prod.map_snd,phaseSlope_observed]
    rfl
  rw [he,he]
  exact congrArg (fun μ : Measure (ℕ → UnitAddCircle) => (μ.prod μ) E)
    (observedPast_integer_shift hp d a w k)

/-- Collision mass restricted to pairs with distinct first predecessor digits. -/
def firstCollision {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ) (g r : ℝ) : ℝ≥0∞ :=
  (unitLaw.prod unitLaw) {z : ℝ × ℝ | uniformCode p hp z.1 0 ≠ uniformCode p hp z.2 0 ∧
    |codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp z.1) -
     codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp z.2)| ≤ r}

theorem measurable_coded_sample {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (W : Ω → ℕ → ℝ) (hW : ∀ i, Measurable (fun y => W y i))
    (x : Ω → ℝ) (hx : Measurable x) (η : ℕ → ℝ) (g : ℝ) :
    Measurable (fun y => codedSlope d (fun i => (a i:ℝ)) p g (W y) η (uniformCode p hp (x y))) := by
  apply Measurable.tsum
  intro n
  apply measurable_const.mul
  apply Real.continuous_sin.measurable.comp
  apply Measurable.add_const
  apply measurable_const.mul
  exact measurable_pathState d _ _ W (fun y => uniformCode p hp (x y)) hW
    (fun j => (measurable_uniformCode p hp j).comp hx) _ _

private theorem measurable_firstCollision_event {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (W : Ω → ℕ → ℝ) (hW : ∀ i, Measurable (fun y => W y i))
    (η : ℕ → ℝ) (g r : ℝ) : MeasurableSet {y : Ω × (ℝ × ℝ) |
      uniformCode p hp y.2.1 0 ≠ uniformCode p hp y.2.2 0 ∧
      |codedSlope d (fun i => (a i:ℝ)) p g (W y.1) η (uniformCode p hp y.2.1) -
       codedSlope d (fun i => (a i:ℝ)) p g (W y.1) η (uniformCode p hp y.2.2)| ≤ r} := by
  have h (x : Ω × (ℝ × ℝ) → ℝ) (hx : Measurable x) :=
    measurable_coded_sample hp d a (fun y : Ω × (ℝ × ℝ) => W y.1)
      (fun i => (hW i).comp measurable_fst) x hx η g
  exact (measurableSet_eq_fun ((measurable_uniformCode p hp 0).comp (measurable_fst.comp measurable_snd))
    ((measurable_uniformCode p hp 0).comp (measurable_snd.comp measurable_snd))).compl.inter
    (measurableSet_le (continuous_abs.measurable.comp
      ((h _ (measurable_fst.comp measurable_snd)).sub (h _ (measurable_snd.comp measurable_snd)))) measurable_const)

theorem measurable_firstCollision {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (W : Ω → ℕ → ℝ) (hW : ∀ i, Measurable (fun y => W y i))
    (η : ℕ → ℝ) (g r : ℝ) : Measurable (fun y => firstCollision hp d a (W y) η g r) :=
  measurable_measure_prodMk_left (measurable_firstCollision_event hp d a W hW η g r)

private theorem firstCollision_slice {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) {b c γ : ℝ}
    (hc : 0 < c) (hc' : c < 1) (hγ : 0 ≤ γ) (hbc : b*c = 1)
    (hpoly : (p:ℝ) + b * ∑ k ∈ Finset.range d, (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ C : ℝ, 0 < C ∧ ∀ (w η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ t, firstCollision (by omega : 0 < p) d a (fun k => w k+t*b^k) η (γ*c^j) r ∂unitLaw) ≤
        ENNReal.ofReal (C*r) := by
  have hp' : 0 < p := by omega
  filter_upwards [coded_predecessor_initialization hp (abs_of_nonneg (Nat.cast_nonneg p)) hc hc' hγ hbc hpoly] with j hj
  obtain ⟨C,hC,hbound⟩ := hj
  refine ⟨C,hC,?_⟩
  intro w η r hr
  let W (t : ℝ) (k : ℕ) := w k+t*b^k
  let B := {y : ℝ × (ℝ × ℝ) | uniformCode p hp' y.2.1 0 ≠ uniformCode p hp' y.2.2 0 ∧
      |codedSlope d (fun i => (a i:ℝ)) p (γ*c^j) (W y.1) η (uniformCode p hp' y.2.1) -
       codedSlope d (fun i => (a i:ℝ)) p (γ*c^j) (W y.1) η (uniformCode p hp' y.2.2)| ≤ r}
  have hm : MeasurableSet B := measurable_firstCollision_event hp' d a W
    (fun k => measurable_const.add (measurable_id.mul_const _)) η _ r
  change (∫⁻ t, (unitLaw.prod unitLaw) (Prod.mk t ⁻¹' B) ∂unitLaw) ≤ _
  rw [← Measure.prod_apply hm,Measure.prod_apply_symm hm]
  have hsec (z : ℝ × ℝ) : unitLaw ((fun t => (t,z)) ⁻¹' B) ≤ ENNReal.ofReal (C*r) := by
    by_cases hx : uniformCode p hp' z.1 0 = uniformCode p hp' z.2 0
    · simp [B,hx]
    · rw [unitLaw,Measure.restrict_apply' measurableSet_Ico]
      apply (measure_mono _).trans (hbound w η (uniformCode p hp' z.1) (uniformCode p hp' z.2) hx 0 r hr)
      intro t ht
      exact ⟨⟨ht.2.1,by simpa using ht.2.2.le⟩,ht.1.2⟩
  simpa using lintegral_mono (μ := unitLaw.prod unitLaw) hsec

private theorem past_coordinate_block_congr {p : ℕ} (d : ℕ) (a : ℕ → ℤ) {w u : ℕ → ℝ}
    (hu : ∀ i < d, w i = u i) (I : ℕ → Fin p) (n : ℕ) :
    pathState d (fun j => (a j:ℝ)) p w I (n+1) 0 = pathState d (fun j => (a j:ℝ)) p u I (n+1) 0 := by
  have hpath (I : ℕ → Fin p) (n : ℕ) : ∀ i < d,
      pathState d (fun j => (a j:ℝ)) p w I n i = pathState d (fun j => (a j:ℝ)) p u I n i := by
    induction n with
    | zero => exact hu
    | succ n ih =>
      intro i hi
      cases i with
      | zero =>
        simp only [pathState,predecessor]
        congr 2
        apply Finset.sum_congr rfl
        intro l hl
        rw [ih l (Finset.mem_range.mp hl)]
      | succ i => exact ih i (by omega)
  have he (I : ℕ → Fin p) (n : ℕ) :
      pathState d (fun j => (a j:ℝ)) p w I (n+1) 0 = pathState d (fun j => (a j:ℝ)) p u I (n+1) 0 := by
    by_cases hd : 0 < d
    · exact hpath I _ 0 hd
    · have : d = 0 := by omega
      simp [this,pathState,predecessor]
  exact he I n

private theorem codedSlope_block_congr {p : ℕ} (d : ℕ) (a : ℕ → ℤ) {w u : ℕ → ℝ}
    (hu : ∀ i < d, w i = u i) (η : ℕ → ℝ) (g : ℝ) (I : ℕ → Fin p) :
    codedSlope d (fun i => (a i:ℝ)) p g w η I = codedSlope d (fun i => (a i:ℝ)) p g u η I := by
  unfold codedSlope
  simp_rw [past_coordinate_block_congr d a hu]

private theorem firstCollision_block_congr {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    {w u : ℕ → ℝ} (hu : ∀ i < d, w i = u i) (η : ℕ → ℝ) (g r : ℝ) :
    firstCollision hp d a w η g r = firstCollision hp d a u η g r := by
  simp only [firstCollision,codedSlope_block_congr d a hu η g]

/-- Canonical representative of a torus-valued central block. -/
@[expose] def centralLift {d : ℕ} (u : Fin d → UnitAddCircle) (k : ℕ) : ℝ :=
  if h : k < d then (AddCircle.equivIco (1:ℝ) 0 (u ⟨k,h⟩)).val else 0

theorem measurable_centralLift (d k : ℕ) : Measurable (fun u : Fin d → UnitAddCircle => centralLift u k) := by
  by_cases h : k < d
  · have he : Measurable (AddCircle.equivIco (1:ℝ) 0) := measurable_of_measurable_on_compl_singleton _
      (continuousOn_iff_continuous_domRestrict.mp (continuousOn_of_forall_continuousAt fun _ hx =>
        AddCircle.continuousAt_equivIco _ _ hx)).measurable
    simpa only [centralLift,dif_pos h,Function.comp_def] using measurable_subtype_coe.comp
      (he.comp (measurable_pi_apply (⟨k,h⟩ : Fin d)))
  · simp only [centralLift,dif_neg h,measurable_const]

private theorem integer_offset_of_phase_eq {x y : ℝ} (h : (x:UnitAddCircle) = (y:UnitAddCircle)) :
    ∃ k : ℤ, x = y+(k:ℝ) := by
  have hz : ((x-y:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,h,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hz
  rw [zsmul_eq_mul,mul_one] at hk
  exact ⟨k,by linarith⟩

private theorem firstCollision_physical_translation {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (u : Fin d → UnitAddCircle) (η : ℕ → ℝ) (g r b t : ℝ) :
    firstCollision hp d a (centralLift (fun i => u i + ((t*b^(i.val):ℝ):UnitAddCircle))) η g r =
    firstCollision hp d a (fun k => centralLift u k+t*b^k) η g r := by
  let V := fun i : Fin d => u i + ((t*b^(i.val):ℝ):UnitAddCircle)
  let W := fun k => centralLift u k+t*b^k
  have he (i : Fin d) : ∃ l : ℤ, centralLift V i = W i+(l:ℝ) := by
    apply integer_offset_of_phase_eq
    simp only [W,centralLift,dif_pos i.isLt,AddCircle.coe_equivIco,AddCircle.coe_add,V]
  choose K hK using he
  let k (i : ℕ) : ℤ := if h : i < d then K ⟨i,h⟩ else 0
  have hh (i : ℕ) (hi : i < d) : centralLift V i = W i+(k i:ℝ) := by simpa [k,hi] using hK ⟨i,hi⟩
  exact (firstCollision_block_congr hp d a hh η g r).trans (first_disagreement_law_integer_shift hp d a W η k g r)

/-- The averaged first-disagreement collision on the actual finite-dimensional
Haar torus is linear in the tested radius for all sufficiently high indices.
The constant is uniform in the deterministic phase sequence. The change of lift
along physical translations retains the first-disagreement restriction. -/
theorem haar_firstCollision_initialization {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) {b c γ : ℝ}
    (hc : 0 < c) (hc' : c < 1) (hγ : 0 ≤ γ) (hbc : b*c = 1)
    (hpoly : (p:ℝ) + b * ∑ k ∈ Finset.range d, (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ C : ℝ, 0 < C ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ u : Fin d → UnitAddCircle,
        firstCollision (by omega : 0 < p) d a (centralLift u) η (γ*c^j) r) ≤ ENNReal.ofReal (C*r) := by
  let Ω := Fin d → UnitAddCircle
  have hp' : 0 < p := by omega
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  filter_upwards [firstCollision_slice hp a hc hc' hγ hbc hpoly] with j hj
  obtain ⟨C,hC,hbound⟩ := hj
  refine ⟨C,hC,?_⟩
  intro η r hr
  let Q (u : Ω) := firstCollision hp' d a (centralLift u) η (γ*c^j) r
  let V (t : ℝ) (i : Fin d) : UnitAddCircle := ((t*b^(i.val):ℝ):UnitAddCircle)
  have hQ : Measurable Q := measurable_firstCollision hp' d a centralLift (measurable_centralLift d) η _ r
  have hV : Measurable V := measurable_pi_lambda _ (fun i => AddCircle.measurable_mk'.comp (measurable_id.mul_const _))
  have hm : Measurable (fun z : Ω × ℝ => Q (z.1+V z.2)) :=
    hQ.comp (measurable_fst.add (hV.comp measurable_snd))
  have hs (t : ℝ) : (∫⁻ u : Ω, Q (u+V t)) = ∫⁻ u : Ω, Q u := lintegral_add_right_eq_self Q (V t)
  have hslice (u : Ω) : (∫⁻ t, Q (u+V t) ∂unitLaw) ≤ ENNReal.ofReal (C*r) := by
    have he (t : ℝ) : Q (u+V t) =
        firstCollision hp' d a (fun k => centralLift u k+t*b^k) η (γ*c^j) r :=
      firstCollision_physical_translation hp' d a u η (γ*c^j) r b t
    simp_rw [he]
    exact hbound (centralLift u) η r hr
  calc
    _ = ∫⁻ t, ∫⁻ u : Ω, Q (u+V t) ∂volume ∂unitLaw := by simp_rw [hs]; simp [Q,Ω]
    _ = ∫⁻ u : Ω, ∫⁻ t, Q (u+V t) ∂unitLaw ∂volume :=
      (lintegral_lintegral_swap (μ := (volume : Measure Ω)) (ν := unitLaw) (f := fun u t => Q (u+V t)) hm.aemeasurable).symm
    _ ≤ _ := by simpa using lintegral_mono (μ := (volume : Measure Ω)) hslice

private def circleRep (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val

private theorem measurable_circleRep : Measurable circleRep := by
  have he : Measurable (AddCircle.equivIco (1:ℝ) 0) := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_of_forall_continuousAt fun _ hx =>
      AddCircle.continuousAt_equivIco _ _ hx)).measurable
  exact measurable_subtype_coe.comp he

private theorem circleRep_preserving : MeasurePreserving circleRep volume unitLaw := by
  have hq : MeasurePreserving ((↑) : ℝ → UnitAddCircle) unitLaw volume := by
    simpa only [unitLaw, Measure.restrict_congr_set (μ := (volume : Measure ℝ)) (Ico_ae_eq_Ioc (a:=0) (b:=1)),
      zero_add] using UnitAddCircle.measurePreserving_mk 0
  refine ⟨measurable_circleRep,?_⟩
  rw [← hq.map_eq,Measure.map_map measurable_circleRep hq.measurable]
  have h : circleRep ∘ ((↑) : ℝ → UnitAddCircle) =ᵐ[unitLaw] id := by
    have hm : ∀ᵐ x ∂unitLaw, x ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
    filter_upwards [hm] with x hx
    exact AddCircle.equivIco_coe_of_mem (by simpa using hx : x ∈ Ico (0:ℝ) (0+1))
  rw [Measure.map_congr h,Measure.map_id]

private theorem finite_block_init_last (d : ℕ) : MeasurePreserving
    (fun u : Fin (d+1) → UnitAddCircle => (fun i : Fin d => u i.castSucc, circleRep (u (Fin.last d))))
    volume ((volume : Measure (Fin d → UnitAddCircle)).prod unitLaw) := by
  let m : Measure (Fin d → UnitAddCircle) := volume
  have hi := volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) (Fin.last d)
  have hrep := circleRep_preserving.prod (MeasurePreserving.id m)
  have h := (Measure.measurePreserving_swap (μ := unitLaw) (ν := m)).comp (hrep.comp hi)
  have he : (fun u : Fin (d+1) → UnitAddCircle => (fun i : Fin d => u i.castSucc, circleRep (u (Fin.last d)))) =
      Prod.swap ∘ Prod.map circleRep id ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) (Fin.last d)) := by
    funext u
    apply Prod.ext
    · funext i
      change u i.castSucc = u ((Fin.last d).succAbove i)
      rw [Fin.succAbove_last]
    · rfl
  rw [he]
  exact h

private theorem finite_block_cons (d : ℕ) : MeasurePreserving
    (fun z : (Fin d → UnitAddCircle) × UnitAddCircle => Fin.cons (α := fun _ : Fin (d+1) => UnitAddCircle) z.2 z.1)
    ((volume : Measure (Fin d → UnitAddCircle)).prod volume) volume := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) 0
  have hi := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) 0).symm e
  have h := hi.comp (Measure.measurePreserving_swap (μ := (volume : Measure (Fin d → UnitAddCircle)))
    (ν := (volume : Measure UnitAddCircle)))
  have he : (fun z : (Fin d → UnitAddCircle) × UnitAddCircle => Fin.cons (α := fun _ : Fin (d+1) => UnitAddCircle) z.2 z.1) =
      e.symm ∘ Prod.swap := by
    funext z
    change Fin.cons z.2 z.1 = e.symm (z.2,z.1)
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_zero']
  rw [he]
  exact h

/-- The complete next central block, with an independent uniform digit. The
dimension of the torus is `d+1`. The signed last coefficient is `a d`. -/
def torusPredecessor {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (z : (Fin (d+1) → UnitAddCircle) × ℝ) : Fin (d+1) → UnitAddCircle :=
  let v := fun i : Fin d => z.1 i.castSucc
  let u := - ∑ i : Fin d, (a i:ℝ)*circleRep (v i)
  Fin.cons (freshPhase p hp (-(a d)) u (circleRep (z.1 (Fin.last d)),z.2)) v

/-- Haar stationarity as an endomorphism of the same finite central torus.
The new first coordinate solves the integer predecessor equation, all the
remaining coordinates are the shifted old ones. -/
theorem torusPredecessor_stationary {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (ha : a d ≠ 0) :
    MeasurePreserving (torusPredecessor hp d a)
      ((volume : Measure (Fin (d+1) → UnitAddCircle)).prod unitLaw) volume := by
  let m : Measure (Fin d → UnitAddCircle) := volume
  let u (w : Fin d → UnitAddCircle) := - ∑ i : Fin d, (a i:ℝ)*circleRep (w i)
  have hu : Measurable u := by
    apply Measurable.neg
    apply Finset.measurable_fun_sum
    intro i _
    exact measurable_const.mul (measurable_circleRep.comp (measurable_pi_apply i))
  let f (z : (Fin d → UnitAddCircle) × (ℝ × ℝ)) := (z.1,freshPhase p hp (-(a d)) (u z.1) z.2)
  have hf : Measurable f := by
    apply measurable_fst.prodMk
    apply AddCircle.measurable_mk'.comp
    apply Measurable.div_const
    exact ((measurable_of_countable (fun i : Fin p => (i.val:ℝ))).comp
      ((measurable_uniformCode p hp 0).comp (measurable_snd.comp measurable_snd))).add
      ((hu.comp measurable_fst).add (measurable_const.mul (measurable_fst.comp measurable_snd)))
  have hF : MeasurePreserving f (m.prod (unitLaw.prod unitLaw)) (m.prod volume) :=
    ⟨hf,predecessor_block_stationary m hp (neg_ne_zero.mpr ha) u hu⟩
  have h := (finite_block_cons d).comp (hF.comp ((measurePreserving_prodAssoc m unitLaw unitLaw).comp
    ((finite_block_init_last d).prod (MeasurePreserving.id unitLaw))))
  exact h

def nextBlock {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (u : Fin (d+1) → UnitAddCircle)
    (i : Fin p) (j : Fin (d+1)) : UnitAddCircle :=
  ↑(predecessor (d+1) (fun n => (a n:ℝ)) p (centralLift u) i j)

theorem torusPredecessor_digit {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (u : Fin (d+1) → UnitAddCircle) (x : ℝ) :
    torusPredecessor hp d a (u,x) = nextBlock d a u (uniformCode p hp x 0) := by
  have hl (i : Fin (d+1)) : centralLift u i = circleRep (u i) := by simp [centralLift,circleRep,i.isLt]
  have hs : (∑ i ∈ Finset.range d, (a i:ℝ)*centralLift u i) =
      ∑ i : Fin d, (a i:ℝ)*circleRep (u i.castSucc) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => congrArg ((a i:ℝ)*·) (hl i.castSucc))
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [torusPredecessor,Fin.cons_zero,freshPhase,nextBlock,Fin.val_zero,predecessor,Finset.sum_range_succ,
      hs,Int.cast_neg,show centralLift u d = circleRep (u (Fin.last d)) from hl (Fin.last d)]
    congr 2
    ring
  · simp only [torusPredecessor,Fin.cons_succ,nextBlock,Fin.val_succ,predecessor]
    rw [show centralLift u i = circleRep (u i.castSucc) from hl i.castSucc]
    exact (AddCircle.coe_equivIco (p := (1:ℝ)) (a := 0)).symm

/-- The slope law before a physical displacement, with the initial central
state in its inherited lift. -/
@[expose] def baseSlopeLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ) (g : ℝ) :=
  unitLaw.map (fun x => codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp x))

instance {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ) (g : ℝ) :
    IsFiniteMeasure (baseSlopeLaw hp d a w η g) := by unfold baseSlopeLaw; infer_instance

def baseCollision {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ) (g r : ℝ) : ℝ≥0∞ :=
  let ν := baseSlopeLaw hp d a w η g
  (ν.prod ν) (PrefixEnergy.band r)

private theorem baseCollision_code {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (w η : ℕ → ℝ) (g r : ℝ) :
    baseCollision hp d a w η g r = (unitLaw.prod unitLaw) {z : ℝ × ℝ |
      |codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp z.1) -
       codedSlope d (fun i => (a i:ℝ)) p g w η (uniformCode p hp z.2)| ≤ r} := by
  have hm := measurable_coded_sample hp d a (fun _ : ℝ => w) (fun _ => measurable_const) id measurable_id η g
  dsimp only [baseCollision,baseSlopeLaw]
  simp only [id_eq] at hm
  rw [Measure.map_prod_map _ _ hm hm,Measure.map_apply (hm.prodMap hm) (PrefixEnergy.band_measurable _)]
  rfl

theorem measurable_baseCollision {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (W : Ω → ℕ → ℝ) (hW : ∀ i, Measurable (fun y => W y i))
    (η : ℕ → ℝ) (g r : ℝ) : Measurable (fun y => baseCollision hp d a (W y) η g r) := by
  have h (x : Ω × (ℝ × ℝ) → ℝ) (hx : Measurable x) :=
    measurable_coded_sample hp d a (fun y : Ω × (ℝ × ℝ) => W y.1)
      (fun i => (hW i).comp measurable_fst) x hx η g
  simp_rw [baseCollision_code]
  exact measurable_measure_prodMk_left (measurableSet_le (continuous_abs.measurable.comp
    ((h _ (measurable_fst.comp measurable_snd)).sub (h _ (measurable_snd.comp measurable_snd)))) measurable_const)

private theorem baseCollision_integer_shift {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (w η : ℕ → ℝ) (k : ℕ → ℤ) (g r : ℝ) :
    baseCollision hp d a (fun i => w i+(k i:ℝ)) η g r = baseCollision hp d a w η g r :=
  congrArg (fun μ : Measure ℝ => (μ.prod μ) (PrefixEnergy.band r)) (slope_law_integer_shift hp d a w η k g)

private theorem restrict_seed_digit {p : ℕ} (hp : 0 < p) (i : Fin p) :
    unitLaw.restrict {x | uniformCode p hp x 0 = i} =
      ENNReal.ofReal ((p:ℝ)⁻¹) • unitLaw.map (prefixSeed (fun _ => i) 1) := by
  simpa using restrict_code_prefix hp (fun _ => i) 1

private theorem diagonal_digit_collision {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (w η : ℕ → ℝ) {g : ℝ} (hg : 0 < g) (hg' : g < 1) (r : ℝ) (i : Fin p) :
    let μ := unitLaw.restrict {x | uniformCode p hp x 0 = i}
    let F := fun x => codedSlope d (fun j => (a j:ℝ)) p g w η (uniformCode p hp x)
    (μ.prod μ) {z : ℝ × ℝ | |F z.1-F z.2| ≤ r} = (ENNReal.ofReal ((p:ℝ)⁻¹))^2 *
      baseCollision hp d a (predecessor d (fun j => (a j:ℝ)) p w i) (fun n => η (1+n)) g (r/g) := by
  intro μ F
  let b := truncatedSlope d (fun j => (a j:ℝ)) p g w η (fun _ : ℕ => i) 1
  let ν := baseSlopeLaw hp d a (predecessor d (fun j => (a j:ℝ)) p w i) (fun n => η (1+n)) g
  let G (x : ℝ) := b+g*x
  let s := ENNReal.ofReal ((p:ℝ)⁻¹)
  have hm : Measurable F := measurable_coded_sample hp d a (fun _ : ℝ => w) (fun _ => measurable_const) id measurable_id η g
  have hG : Measurable G := measurable_const.add (measurable_const.mul measurable_id)
  have hsplit : μ.map F = s • ν.map G := by
    dsimp only [ν,μ,F,G,s,b,baseSlopeLaw]
    simpa only [Set.preimage_univ, Measure.restrict_univ, Nat.lt_one_iff, forall_eq, pow_one, pathState] using restricted_slope_prefix_law hp d (fun j => (a j:ℝ)) p w η
        (fun _ : ℕ => i) 1 hg.le hg' MeasurableSet.univ
  have hmap : (μ.prod μ) {z : ℝ × ℝ | |F z.1-F z.2| ≤ r} =
      ((μ.map F).prod (μ.map F)) (PrefixEnergy.band r) := by
    rw [Measure.map_prod_map _ _ hm hm,Measure.map_apply (hm.prodMap hm) (PrefixEnergy.band_measurable _)]
    rfl
  rw [hmap,hsplit,Measure.prod_smul_left,Measure.prod_smul_right,Measure.smul_apply,Measure.smul_apply,smul_eq_mul,
    smul_eq_mul,show ENNReal.ofReal ((p:ℝ)⁻¹) = s from rfl,pow_two,mul_assoc]
  congr 2
  rw [Measure.map_prod_map _ _ hG hG,Measure.map_apply (hG.prodMap hG) (PrefixEnergy.band_measurable _)]
  change (ν.prod ν) _ = (ν.prod ν) _
  congr 1
  ext z
  change |b+g*z.1-(b+g*z.2)| ≤ r ↔ |z.1-z.2| ≤ r/g
  rw [show b+g*z.1-(b+g*z.2) = (z.1-z.2)*g by ring,abs_mul,abs_of_pos hg,le_div_iff₀ hg]

/-- Exact separation of all two-code collisions into different first digits
and the diagonals of individual first-digit cylinders. -/
theorem baseCollision_one_step {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (w η : ℕ → ℝ) {g : ℝ} (hg : 0 < g) (hg' : g < 1) (r : ℝ) :
    baseCollision hp d a w η g r = firstCollision hp d a w η g r +
      ∑ i : Fin p, (ENNReal.ofReal ((p:ℝ)⁻¹))^2 *
        baseCollision hp d a (predecessor d (fun j => (a j:ℝ)) p w i) (fun n => η (1+n)) g (r/g) := by
  classical
  let μ := unitLaw.prod unitLaw
  let F (x : ℝ) := codedSlope d (fun j => (a j:ℝ)) p g w η (uniformCode p hp x)
  let B := {z : ℝ × ℝ | |F z.1-F z.2| ≤ r}
  let E (i : Fin p) := {x : ℝ | uniformCode p hp x 0 = i}
  let D := {z : ℝ × ℝ | uniformCode p hp z.1 0 ≠ uniformCode p hp z.2 0}
  let A (i : Fin p) := B ∩ (E i ×ˢ E i)
  have hmF : Measurable F := measurable_coded_sample hp d a (fun _ : ℝ => w) (fun _ => measurable_const) id measurable_id η g
  have hmB : MeasurableSet B := measurableSet_le
    (continuous_abs.measurable.comp ((hmF.comp measurable_fst).sub (hmF.comp measurable_snd))) measurable_const
  have hmE (i : Fin p) : MeasurableSet (E i) := measurableSet_eq_fun (measurable_uniformCode p hp 0) measurable_const
  have hmD : MeasurableSet D := (measurableSet_eq_fun ((measurable_uniformCode p hp 0).comp measurable_fst)
    ((measurable_uniformCode p hp 0).comp measurable_snd)).compl
  have hD : B ∩ D = {z : ℝ × ℝ | uniformCode p hp z.1 0 ≠ uniformCode p hp z.2 0 ∧ |F z.1-F z.2| ≤ r} := by
    ext z
    exact and_comm
  have hc : B \ D = ⋃ i, A i := by
    ext z
    simp only [B,D,A,E,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_prod,not_ne_iff]
    constructor
    · rintro ⟨hz,he⟩
      exact ⟨_,hz,rfl,he.symm⟩
    · rintro ⟨i,hz,hx,hy⟩
      exact ⟨hz,hx.trans hy.symm⟩
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hij (hz.2.1.symm.trans hz'.2.1)
  rw [baseCollision_code]
  change μ B = _ + _
  rw [← measure_inter_add_sdiff (μ := μ) B hmD,hD,hc,measure_iUnion hd (fun i => hmB.inter ((hmE i).prod (hmE i))),
    tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h := diagonal_digit_collision hp d a w η hg hg' r i
  change ((unitLaw.restrict (E i)).prod (unitLaw.restrict (E i))) B = _ at h
  rw [Measure.prod_restrict,Measure.restrict_apply hmB] at h
  exact h

private theorem baseCollision_nextBlock {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (u : Fin (d+1) → UnitAddCircle) (i : Fin p) (η : ℕ → ℝ) (g r : ℝ) :
    baseCollision hp (d+1) a (centralLift (nextBlock d a u i)) η g r =
    baseCollision hp (d+1) a (predecessor (d+1) (fun j => (a j:ℝ)) p (centralLift u) i) η g r := by
  let W := predecessor (d+1) (fun j => (a j:ℝ)) p (centralLift u) i
  let V := nextBlock d a u i
  have he (j : Fin (d+1)) : ∃ l : ℤ, centralLift V j = W j+(l:ℝ) := by
    apply integer_offset_of_phase_eq
    simp only [centralLift,dif_pos j.isLt,AddCircle.coe_equivIco]
    rfl
  choose K hK using he
  let k (j : ℕ) : ℤ := if h : j < d+1 then K ⟨j,h⟩ else 0
  have hh (j : ℕ) (hj : j < d+1) : centralLift V j = W j+(k j:ℝ) := by simpa only [k,dif_pos hj] using hK ⟨j,hj⟩
  calc
    _ = baseCollision hp (d+1) a (fun j => W j+(k j:ℝ)) η g r := by
      change baseCollision hp (d+1) a (centralLift V) η g r = _
      simp only [baseCollision,baseSlopeLaw,codedSlope_block_congr (p := p) (d+1) a hh η g]
    _ = _ := baseCollision_integer_shift hp (d+1) a W η k g r

private theorem lintegral_first_digit {p : ℕ} (hp : 0 < p) (f : Fin p → ℝ≥0∞) :
    (∫⁻ x, f (uniformCode p hp x 0) ∂unitLaw) = ENNReal.ofReal ((p:ℝ)⁻¹)*∑ i, f i := by
  classical
  let E (i : Fin p) := {x | uniformCode p hp x 0 = i}
  have hm (i : Fin p) : MeasurableSet (E i) := measurableSet_eq_fun (measurable_uniformCode p hp 0) measurable_const
  have he (x : ℝ) : f (uniformCode p hp x 0) = ∑ i, (E i).indicator (fun _ => f i) x := by
    simp [E,Set.indicator_apply,eq_comm]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hm i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator_const (hm i),show unitLaw (E i) = _ from unitLaw_first_digit hp i,mul_comm]

private theorem weighted_children_haar {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (ha : a d ≠ 0)
    (Q : (Fin (d+1) → UnitAddCircle) → ℝ≥0∞) (hQ : Measurable Q) :
    (∫⁻ u : Fin (d+1) → UnitAddCircle, ∑ i : Fin p, (ENNReal.ofReal ((p:ℝ)⁻¹))^2 * Q (nextBlock d a u i)) =
      ENNReal.ofReal ((p:ℝ)⁻¹)*(∫⁻ u, Q u) := by
  let s := ENNReal.ofReal ((p:ℝ)⁻¹)
  have h := torusPredecessor_stationary hp d a ha
  have he (u : Fin (d+1) → UnitAddCircle) : (∑ i : Fin p, s^2 * Q (nextBlock d a u i)) =
      s*(∫⁻ x, Q (torusPredecessor hp d a (u,x)) ∂unitLaw) := by
    simp_rw [torusPredecessor_digit]
    rw [lintegral_first_digit hp (fun i => Q (nextBlock d a u i)), ← Finset.mul_sum,pow_two,mul_assoc]
  change ∫⁻ u, ∑ i, s^2*Q (nextBlock d a u i) = _
  simp_rw [he]
  rw [lintegral_const_mul' s _ ENNReal.ofReal_ne_top]
  apply congrArg (s*·)
  exact (lintegral_prod (fun z => Q (torusPredecessor hp d a z)) (hQ.comp h.measurable).aemeasurable).symm.trans (h.lintegral_comp hQ)

/-- The high-index initialization on the true Haar block, including *all*
common prefixes. A first-digit coincidence costs exactly `1/p`; Haar
stationarity restores the base at the next scale without a slice Jacobian. -/
theorem haar_collision_one_step {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ C : ℝ, 0 < C ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ u : Fin (d+1) → UnitAddCircle, baseCollision (by omega : 0 < p) (d+1) a (centralLift u) η (γ*c^j) r) ≤
        ENNReal.ofReal (C*r) + ENNReal.ofReal ((p:ℝ)⁻¹) *
          (∫⁻ u : Fin (d+1) → UnitAddCircle, baseCollision (by omega : 0 < p) (d+1) a (centralLift u)
            (fun n => η (1+n)) (γ*c^j) (r/(γ*c^j))) := by
  have hp' : 0 < p := by omega
  have hlim : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc').const_mul γ
  filter_upwards [haar_firstCollision_initialization hp a hc hc' hγ.le hbc hpoly,
    hlim.eventually_lt_const zero_lt_one] with j hj hg'
  obtain ⟨C,hC,hbound⟩ := hj
  refine ⟨C,hC,?_⟩
  intro η r hr
  let g := γ*c^j
  let Q (u : Fin (d+1) → UnitAddCircle) := baseCollision hp' (d+1) a (centralLift u) (fun n => η (1+n)) g (r/g)
  have hQ : Measurable Q := measurable_baseCollision _ _ _ _ (measurable_centralLift _) _ _ _
  have he (u : Fin (d+1) → UnitAddCircle) : baseCollision hp' (d+1) a (centralLift u) η g r =
      firstCollision hp' (d+1) a (centralLift u) η g r +
      ∑ i : Fin p, (ENNReal.ofReal ((p:ℝ)⁻¹))^2 * Q (nextBlock d a u i) := by
    rw [baseCollision_one_step hp' _ _ _ η (show 0 < g by dsimp [g]; positivity) hg']
    congr 1
    exact Finset.sum_congr rfl (fun i _ => congrArg (((ENNReal.ofReal ((p:ℝ)⁻¹))^2)*·)
      (baseCollision_nextBlock hp' d a u i _ _ _).symm)
  change (∫⁻ u, baseCollision hp' (d+1) a (centralLift u) η g r) ≤ _
  simp_rw [he]
  rw [lintegral_add_left (measurable_firstCollision _ _ _ _ (measurable_centralLift _) _ _ _),weighted_children_haar hp' d a ha Q hQ]
  exact add_le_add_left (hbound η r hr) _

private theorem geometric_forcing_bound {X : Type*} (shift : X → X) (F : X → ℕ → ℝ) {g q C : ℝ}
    (hg : 0 < g) (hgq : g < q) (hC : 0 ≤ C) (hbase : ∀ x, F x 0 ≤ 1)
    (hstep : ∀ x n, F x (n+1) ≤ C*g^(n+1)+q*F (shift x) n) :
    ∃ K : ℝ, 0 < K ∧ ∀ x n, F x n ≤ K*q^n := by
  let A := C*g/(q-g)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hC hg.le) (sub_pos.mpr hgq).le
  have hcancel : (q-g)*A = C*g := by rw [mul_comm,div_mul_cancel₀ _ (sub_ne_zero.mpr hgq.ne')]
  have h (n : ℕ) (x : X) : F x n + A*g^n ≤ (1+A)*q^n := by
    induction n generalizing x with
    | zero => simpa only [pow_zero,mul_one] using add_le_add_left (hbase x) A
    | succ n ih =>
      have hi := mul_le_mul_of_nonneg_left (ih (shift x)) (hg.trans hgq).le
      have hc := congrArg (·*g^n) hcancel
      have hs := hstep x n
      simp only [pow_succ] at hs ⊢
      nlinarith only [hi,hc,hs]
  exact ⟨1+A,by linarith,fun x n => (le_add_of_nonneg_right (mul_nonneg hA (pow_nonneg hg.le n))).trans (h n x)⟩

private theorem ennreal_geometric_forcing {X : Type*} (S : X → X) (F : X → ℕ → ℝ≥0∞) {g q C : ℝ}
    (hg : 0 < g) (hgq : g < q) (hC : 0 ≤ C) (hle : ∀ x n, F x n ≤ 1)
    (hstep : ∀ x n, F x (n+1) ≤ ENNReal.ofReal (C*g^(n+1))+ENNReal.ofReal q * F (S x) n) :
    ∃ K : ℝ, 0 < K ∧ ∀ x n, F x n ≤ ENNReal.ofReal (K*q^n) := by
  have hfin (x : X) (n : ℕ) : F x n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hle x n)
  have hb (x : X) : (F x 0).toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hle x 0)
  have hs (x : X) (n : ℕ) : (F x (n+1)).toReal ≤ C*g^(n+1)+q*(F (S x) n).toReal := by
    have hm := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := q)) (hfin (S x) n)
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hm⟩) (hstep x n)
    simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top hm,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hC (pow_nonneg hg.le _)),ENNReal.toReal_ofReal (hg.trans hgq).le] using h
  obtain ⟨K,hK,hbound⟩ := geometric_forcing_bound S (fun x n => (F x n).toReal) hg hgq hC hb hs
  refine ⟨K,hK,?_⟩
  intro x n
  rw [← ENNReal.ofReal_toReal (hfin x n)]
  exact ENNReal.ofReal_le_ofReal (hbound x n)

/-- Uniform sharp geometric collision bound for the actual slope law:
at radius `g^n`, Haar-averaged collision probability is at most `K p⁻ⁿ`.
Both the high-index threshold and the bound are phase-uniform. -/
theorem haar_sharp_initial_collisions {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∃ K : ℝ, 0 < K ∧ ∀ (η : ℕ → ℝ) (n : ℕ),
      (∫⁻ u : Fin (d+1) → UnitAddCircle, baseCollision (by omega : 0 < p) (d+1) a (centralLift u)
        η (γ*c^j) ((γ*c^j)^n)) ≤ ENNReal.ofReal (K*((p:ℝ)⁻¹)^n) := by
  have hp' : 0 < p := by omega
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp'
  have hlim : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc').const_mul γ
  filter_upwards [haar_collision_one_step hp a ha hc hc' hγ hbc hpoly,
    hlim.eventually_lt_const (inv_pos.mpr hpR)] with j hj hsmall
  obtain ⟨C,hC,hstep⟩ := hj
  let g := γ*c^j
  have hg : 0 < g := mul_pos hγ (pow_pos hc j)
  let F (η : ℕ → ℝ) (n : ℕ) := ∫⁻ u : Fin (d+1) → UnitAddCircle,
    baseCollision hp' (d+1) a (centralLift u) η g (g^n)
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  have hle (η : ℕ → ℝ) (n : ℕ) : F η n ≤ 1 := by
    have h (u : Fin (d+1) → UnitAddCircle) : baseCollision hp' (d+1) a (centralLift u) η g (g^n) ≤ 1 := by
      rw [baseCollision_code]
      exact prob_le_one
    simpa using lintegral_mono (μ := (volume : Measure (Fin (d+1) → UnitAddCircle))) h
  apply ennreal_geometric_forcing (X := ℕ → ℝ) (g := g) (q := (p:ℝ)⁻¹) (C := C)
    (fun (η : ℕ → ℝ) (n : ℕ) => η (1+n)) F hg hsmall hC.le hle
  intro η n
  have he := hstep η (g^(n+1)) (pow_nonneg hg.le _)
  change F η (n+1) ≤ ENNReal.ofReal (C*g^(n+1)) + ENNReal.ofReal ((p:ℝ)⁻¹)*
    (∫⁻ u : Fin (d+1) → UnitAddCircle, baseCollision hp' (d+1) a (centralLift u) (fun i => η (1+i)) g (g^(n+1)/g)) at he
  simpa only [pow_succ g n,mul_div_cancel_right₀ _ hg.ne',F] using he

private theorem diagonal_prefixSeries {p g : ℝ} (hp : 1 < p) (hg : 0 < g) (n : ℕ) :
    p⁻¹^n ≤ PrefixEnergy.prefixSeries p g (g^n) := by
  have hq := (inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp
  have hs := (PrefixEnergy.prefixSeries_bound (zero_lt_one.trans hp) hg (pow_pos hg n)
    (le_refl (0:ℝ)) zero_le_one (by simpa using hq)).1
  have h := hs.sum_le_tsum ({n} : Finset ℕ) (fun k _ => show 0 ≤ PrefixEnergy.prefixTerm p g (g^n) k by
    unfold PrefixEnergy.prefixTerm; positivity)
  simpa [PrefixEnergy.prefixTerm,PrefixEnergy.prefixSeries,inv_pow,mul_inv_cancel₀ (pow_ne_zero n hg.ne')] using h

/-- Sharp lower local dimension for all sufficiently high derivative indices,
almost everywhere on the true central Haar torus and in the conditional slope
law. The exponent is precisely the manuscript's `min(1,log p/log(1/g))`. -/
theorem haar_sharp_initial_lower_dimension {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∀ η : ℕ → ℝ, ∀ᵐ u : Fin (d+1) → UnitAddCircle,
      ∀ᵐ y ∂baseSlopeLaw (by omega : 0 < p) (d+1) a (centralLift u) η (γ*c^j),
      ∀ t : ℝ, t < min 1 (Real.log p/Real.log (1/(γ*c^j))) →
        ∀ᶠ r : ℝ in 𝓝[>] 0, t ≤ Real.log ((baseSlopeLaw (by omega : 0 < p) (d+1) a (centralLift u)
          η (γ*c^j)).real (Icc (y-r) (y+r))) / Real.log r := by
  have hlim : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc').const_mul γ
  filter_upwards [haar_sharp_initial_collisions hp a ha hc hc' hγ hbc hpoly,
    hlim.eventually_lt_const zero_lt_one] with j hj hsmall
  obtain ⟨K,hK,hbound⟩ := hj
  intro η
  have hpR : 1 < (p:ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hg : 0 < γ*c^j := mul_pos hγ (pow_pos hc j)
  apply PrefixEnergy.ae_lower_local_dimension_from_prefix_bound volume
    (fun u : Fin (d+1) → UnitAddCircle => baseSlopeLaw (by omega : 0 < p) (d+1) a (centralLift u) η (γ*c^j))
    (q := γ*c^j) hpR hg hsmall hg hsmall (C := ENNReal.ofReal K) ENNReal.ofReal_ne_top
    (fun n => (measurable_baseCollision (by omega : 0 < p) (d+1) a centralLift (measurable_centralLift _) η _ _).aemeasurable)
  intro n
  rw [← ENNReal.ofReal_mul hK.le]
  exact (hbound η n).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (diagonal_prefixSeries hpR hg n) hK.le))

/-- Sharp, phase-uniform upper bound for heavy balls in the actual sampled
Haar slope law. The dilation is arbitrary and the threshold `τ` may depend
on the depth. -/
theorem haar_sharp_initial_information {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (η : ℕ → ℝ) (τ : ℝ), 0 < τ →
      ((volume : Measure (Fin (d+1) → UnitAddCircle)).prod unitLaw) {z | let g := γ*c^j
        let y := codedSlope (d+1) (fun i => (a i:ℝ)) p g (centralLift z.1) η (uniformCode p (by omega) z.2)
        ENNReal.ofReal τ < baseSlopeLaw (by omega : 0 < p) (d+1) a (centralLift z.1) η g (Icc (y-A*g^n) (y+A*g^n))} ≤
        ENNReal.ofReal (K*(p:ℝ)⁻¹^n/τ) := by
  have hp' : 0 < p := by omega
  have hlim : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc').const_mul γ
  filter_upwards [haar_sharp_initial_collisions hp a ha hc hc' hγ hbc hpoly,
    hlim.eventually_lt_const zero_lt_one] with j hj hsmall
  obtain ⟨K,hK,hbound⟩ := hj
  intro A hA
  let g := γ*c^j
  let q := (p:ℝ)⁻¹
  have hg : 0 < g := mul_pos hγ (pow_pos hc j)
  have hq : 0 < q := inv_pos.mpr (by exact_mod_cast hp')
  have hdec : Tendsto (fun n : ℕ => A*g^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hsmall).const_mul A
  obtain ⟨m,hm⟩ := (hdec.eventually_lt_const zero_lt_one).exists
  refine ⟨K/q^m,div_pos hK (pow_pos hq m),?_⟩
  filter_upwards [eventually_ge_atTop m] with n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  intro η τ hτ
  let F (u : Fin (d+1) → UnitAddCircle) (x : ℝ) := codedSlope (d+1) (fun i => (a i:ℝ)) p g
    (centralLift u) η (uniformCode p hp' x)
  have hF : Measurable (fun z : (Fin (d+1) → UnitAddCircle) × ℝ => F z.1 z.2) :=
    measurable_coded_sample hp' (d+1) a (fun z : (Fin (d+1) → UnitAddCircle) × ℝ => centralLift z.1)
      (fun i => (measurable_centralLift _ _).comp measurable_fst) Prod.snd measurable_snd η g
  have hR : A*g^(m+k) ≤ g^k := by
    rw [pow_add,← mul_assoc]
    exact mul_le_of_le_one_left (pow_nonneg hg.le k) hm.le
  have hmark := heavy_ball_markov volume hF (A*g^(m+k)) τ hτ
  have hsmallBall (u : Fin (d+1) → UnitAddCircle) : baseCollision hp' (d+1) a (centralLift u) η g (A*g^(m+k))
      ≤ baseCollision hp' (d+1) a (centralLift u) η g (g^k) :=
    measure_mono (fun _ h => h.trans hR)
  have htotal := (lintegral_mono hsmallBall).trans (hbound η k)
  change _ ≤ ENNReal.ofReal (K/q^m*q^(m+k)/τ)
  rw [pow_add,← mul_assoc,div_mul_cancel₀ _ (pow_ne_zero m hq.ne'),ENNReal.ofReal_div_of_pos hτ]
  apply hmark.trans
  rw [div_eq_mul_inv,div_eq_mul_inv]
  exact mul_le_mul_left htotal _

/-- A fixed code's observed torus past along the real polynomial predecessor. -/
def codePast {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (I : ℕ → Fin p) (n : ℕ) : UnitAddCircle :=
  ↑(pathState d (fun k => (a k:ℝ)) p w I (n+1) 0)

private theorem measurable_codePast {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (W : Ω → ℕ → ℝ) (hW : ∀ i, Measurable (fun y => W y i))
    (x : Ω → ℝ) (hx : Measurable x) :
    Measurable (fun y => codePast d a (W y) (uniformCode p hp (x y))) := by
  apply measurable_pi_lambda
  intro i
  apply AddCircle.measurable_mk'.comp
  exact measurable_pathState d _ _ W (fun y => uniformCode p hp (x y)) hW
    (fun j => (measurable_uniformCode p hp j).comp hx) _ _

private def pairPastMass {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ)
    (E : Set ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))) : ℝ≥0∞ :=
  (unitLaw.prod unitLaw) {z : ℝ × ℝ | (codePast d a w (uniformCode p hp z.1),codePast d a w (uniformCode p hp z.2)) ∈ E}

private theorem pairPastMass_shift {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (k : ℕ → ℤ)
    {E : Set ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))} (hE : MeasurableSet E) :
    pairPastMass hp d a (fun l => w l+(k l:ℝ)) E = pairPastMass hp d a w E := by
  let P (u : ℕ → ℝ) := observedPast hp d a u
  have he (u : ℕ → ℝ) : pairPastMass hp d a u E = ((unitLaw.map (P u)).prod (unitLaw.map (P u))) E := by
    have hm := measurable_observedPast hp d a u
    rw [Measure.map_prod_map _ _ hm hm,Measure.map_apply (hm.prodMap hm) hE]
    rfl
  rw [he,he]
  exact congrArg (fun μ : Measure (ℕ → UnitAddCircle) => (μ.prod μ) E) (observedPast_integer_shift hp d a w k)

private theorem measurable_pairPast_event {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (W : Ω → ℕ → ℝ) (hW : ∀ i, Measurable (fun y => W y i))
    {E : Set ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))} (hE : MeasurableSet E) :
    MeasurableSet {z : Ω × (ℝ × ℝ) | (codePast d a (W z.1) (uniformCode p hp z.2.1),
      codePast d a (W z.1) (uniformCode p hp z.2.2)) ∈ E} := by
  have h (x : Ω × (ℝ × ℝ) → ℝ) (hx : Measurable x) :=
    measurable_codePast hp d a (fun y : Ω × (ℝ × ℝ) => W y.1) (fun i => (hW i).comp measurable_fst) x hx
  exact ((h _ (measurable_fst.comp measurable_snd)).prodMk (h _ (measurable_snd.comp measurable_snd))) hE

private theorem haar_pairPast_bound {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (b : ℝ)
    {E : Set ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))} (hE : MeasurableSet E) {C : ℝ≥0∞}
    (hsub : ∀ (w : ℕ → ℝ) (I J : ℕ → Fin p), volume {t ∈ Icc (0:ℝ) 1 |
      (codePast d a (fun k => w k+t*b^k) I,codePast d a (fun k => w k+t*b^k) J) ∈ E} ≤ C) :
    (∫⁻ u : Fin d → UnitAddCircle, pairPastMass hp d a (centralLift u) E) ≤ C := by
  let Ω := Fin d → UnitAddCircle
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  let Q (u : Ω) := pairPastMass hp d a (centralLift u) E
  let V (t : ℝ) (i : Fin d) : UnitAddCircle := ((t*b^(i.val):ℝ):UnitAddCircle)
  have hQ : Measurable Q := measurable_measure_prodMk_left (measurable_pairPast_event hp d a centralLift (measurable_centralLift d) hE)
  have hV : Measurable V := measurable_pi_lambda _ (fun i => AddCircle.measurable_mk'.comp (measurable_id.mul_const _))
  have hm : Measurable (fun z : Ω × ℝ => Q (z.1+V z.2)) := hQ.comp (measurable_fst.add (hV.comp measurable_snd))
  have hs (t : ℝ) : (∫⁻ u : Ω, Q (u+V t)) = ∫⁻ u : Ω, Q u := lintegral_add_right_eq_self Q (V t)
  have hslice (u : Ω) : (∫⁻ t, Q (u+V t) ∂unitLaw) ≤ C := by
    let W (t : ℝ) (k : ℕ) := centralLift u k+t*b^k
    have he (t : ℝ) : Q (u+V t) = pairPastMass hp d a (W t) E := by
      have hi (i : Fin d) : ∃ l : ℤ, centralLift (u+V t) i = W t i+(l:ℝ) := by
        apply integer_offset_of_phase_eq
        simp only [W,V,centralLift,dif_pos i.isLt,AddCircle.coe_equivIco,AddCircle.coe_add]
        rfl
      choose K hK using hi
      let k (i : ℕ) : ℤ := if h : i < d then K ⟨i,h⟩ else 0
      have hh (i : ℕ) (hi : i < d) : centralLift (u+V t) i = W t i+(k i:ℝ) := by
        simpa only [k,dif_pos hi] using hK ⟨i,hi⟩
      change pairPastMass hp d a (centralLift (u+V t)) E = _
      rw [← pairPastMass_shift hp d a (W t) k hE]
      have hP (I : ℕ → Fin p) : codePast d a (centralLift (u+V t)) I =
          codePast d a (fun i => W t i+(k i:ℝ)) I := by
        funext i
        exact congrArg ((↑) : ℝ → UnitAddCircle) (past_coordinate_block_congr d a hh I i)
      simp only [pairPastMass,hP]
    simp_rw [he]
    let B := {z : ℝ × (ℝ × ℝ) | (codePast d a (W z.1) (uniformCode p hp z.2.1),
      codePast d a (W z.1) (uniformCode p hp z.2.2)) ∈ E}
    have hB : MeasurableSet B := measurable_pairPast_event hp d a W
      (fun k => measurable_const.add (measurable_id.mul_const _)) hE
    change (∫⁻ t, (unitLaw.prod unitLaw) (Prod.mk t ⁻¹' B) ∂unitLaw) ≤ C
    rw [← Measure.prod_apply hB,Measure.prod_apply_symm hB]
    have hbnd (z : ℝ × ℝ) : unitLaw ((fun t => (t,z)) ⁻¹' B) ≤ C := by
      rw [unitLaw,Measure.restrict_apply' measurableSet_Ico]
      apply (measure_mono _).trans (hsub (centralLift u) (uniformCode p hp z.1) (uniformCode p hp z.2))
      intro t ht
      exact ⟨⟨ht.2.1,ht.2.2.le⟩,ht.1⟩
    simpa using lintegral_mono (μ := unitLaw.prod unitLaw) hbnd
  calc
    _ = ∫⁻ t, ∫⁻ u : Ω, Q (u+V t) ∂volume ∂unitLaw := by simp_rw [hs]; simp [Q,Ω]
    _ = ∫⁻ u : Ω, ∫⁻ t, Q (u+V t) ∂unitLaw ∂volume :=
      (lintegral_lintegral_swap (μ := (volume : Measure Ω)) (ν := unitLaw) (f := fun u t => Q (u+V t)) hm.aemeasurable).symm
    _ ≤ _ := by simpa using lintegral_mono (μ := (volume : Measure Ω)) hslice

private def phasePrefix (g : ℝ) (η : ℕ → ℝ) (n : ℕ) (v : ℕ → UnitAddCircle) : ℝ :=
  ∑ i ∈ Finset.range n, g^i * phaseSine (η i) (v i)

private theorem measurable_phasePrefix (g : ℝ) (η : ℕ → ℝ) (n : ℕ) : Measurable (phasePrefix g η n) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact measurable_const.mul ((continuous_phaseSine _).measurable.comp (measurable_pi_apply i))

private theorem phase_observations {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (g : ℝ) (n : ℕ) :
    phasePrefix g η n (codePast d a w I) = truncatedSlope d (fun i => (a i:ℝ)) p g w η I n ∧
    phaseSlope g η (codePast d a w I) = codedSlope d (fun i => (a i:ℝ)) p g w η I := by
  constructor
  · unfold phasePrefix truncatedSlope codePast phaseSine
    simp only [Function.Periodic.lift_coe]
  · unfold phaseSlope codedSlope codePast phaseSine
    simp only [Function.Periodic.lift_coe]

/-- The non-neighbor contribution in the descent is `O_n(r)` on the actual
central Haar torus, uniformly over all phases. Both paths are sampled from the
true predecessor tree and prefix degrees use their concrete derivative sums. -/
theorem haar_offDiagonal_collision_rate {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) {b c g : ℝ}
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range d, (a k:ℝ)*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C = slopeSliceBound g c n ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ u : Fin d → UnitAddCircle, (unitLaw.prod unitLaw) {z : ℝ × ℝ | let W := centralLift u
        let I := uniformCode p hp z.1
        let J := uniformCode p hp z.2
        let θ := fun k => η k+Real.pi/2
        (2*(1-g*c)⁻¹+1)*(g*c)^n <
          |truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W θ I n - truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W θ J n| ∧
          |codedSlope d (fun i => (a i:ℝ)) p g W η I - codedSlope d (fun i => (a i:ℝ)) p g W η J| ≤ r}) ≤
        ENNReal.ofReal (C*r) := by
  have hp' : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  obtain ⟨C,hC,hEq,hbound⟩ := offDiagonal_prefix_collision_rate (p := p) hp' hg hg' hc hc' hbc hpoly n
  refine ⟨C,hC,hEq,?_⟩
  intro η r hr
  let h := g*c
  let θ := fun k => η k+Real.pi/2
  let E := {z : (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle) |
    (2*(1-h)⁻¹+1)*h^n < |phasePrefix h θ n z.1-phasePrefix h θ n z.2| ∧ |phaseSlope g η z.1-phaseSlope g η z.2| ≤ r}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp (((measurable_phasePrefix _ _ _).comp measurable_fst).sub
      ((measurable_phasePrefix _ _ _).comp measurable_snd)))).inter
      (measurableSet_le (continuous_abs.measurable.comp (((measurable_phaseSlope _ _).comp measurable_fst).sub
        ((measurable_phaseSlope _ _).comp measurable_snd))) measurable_const)
  have he (w : ℕ → ℝ) (I J : ℕ → Fin p) : (codePast d a w I,codePast d a w J) ∈ E ↔
      (2*(1-h)⁻¹+1)*h^n < |truncatedSlope d (fun i => (a i:ℝ)) p h w θ I n - truncatedSlope d (fun i => (a i:ℝ)) p h w θ J n| ∧
      |codedSlope d (fun i => (a i:ℝ)) p g w η I - codedSlope d (fun i => (a i:ℝ)) p g w η J| ≤ r := by
    simp only [E,Set.mem_ofPred_eq,(phase_observations d a w θ I h n).1,(phase_observations d a w θ J h n).1,
      (phase_observations d a w η I g n).2,(phase_observations d a w η J g n).2]
  have hs := haar_pairPast_bound hp d a b hE (C := ENNReal.ofReal (C*r)) (fun w I J => by
    simp only [he]; simpa only [zero_add,h,θ] using hbound w η I J 0 r hr)
  simpa only [pairPastMass,he,h,θ] using hs

theorem haar_offDiagonal_collision {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) {b c g : ℝ}
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range d, (a k:ℝ)*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ u : Fin d → UnitAddCircle, (unitLaw.prod unitLaw) {z : ℝ × ℝ | let W := centralLift u
        let I := uniformCode p hp z.1
        let J := uniformCode p hp z.2
        let θ := fun k => η k+Real.pi/2
        (2*(1-g*c)⁻¹+1)*(g*c)^n <
          |truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W θ I n - truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W θ J n| ∧
          |codedSlope d (fun i => (a i:ℝ)) p g W η I - codedSlope d (fun i => (a i:ℝ)) p g W η J| ≤ r}) ≤
        ENNReal.ofReal (C*r) := by
  obtain ⟨C,hC,_,H⟩ := haar_offDiagonal_collision_rate hp a hg hg' hc hc' hbc hpoly n
  exact ⟨C,hC,H⟩

private def shiftRegister (w z : ℕ → UnitAddCircle) : ℕ → ℕ → UnitAddCircle
  | 0, k => w k
  | n+1, 0 => z n
  | n+1, k+1 => shiftRegister w z n k

private theorem shiftRegister_reads_past {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ)
    (I : ℕ → Fin p) (n k : ℕ) : shiftRegister (fun i => (w i:UnitAddCircle)) (codePast d a w I) n k =
      (↑(pathState d (fun i => (a i:ℝ)) p w I n k):UnitAddCircle) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => cases k with
    | zero => rfl
    | succ k => exact ih k

private theorem measurable_shiftRegister (w : ℕ → UnitAddCircle) (n k : ℕ) :
    Measurable (fun z => shiftRegister w z n k) := by
  induction n generalizing k with
  | zero => exact measurable_const
  | succ n ih => cases k with
    | zero => exact measurable_pi_apply n
    | succ k => exact ih k

/-- Test of the entire finite central state at the end of a block, driven
through the original polynomial by the complete uniform digit stream. -/
def blockEndMean {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : ℕ → ℝ)
    (Q : (Fin d → UnitAddCircle) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, Q (fun i : Fin d => ↑(pathState d (fun j => (a j:ℝ)) p w (uniformCode p hp x) n i)) ∂unitLaw

private theorem measurable_end_state {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : Ω → ℕ → ℝ) (x : Ω → ℝ)
    (hw : ∀ i, Measurable (fun z => w z i)) (hx : Measurable x) :
    Measurable (fun z => fun i : Fin d => (↑(pathState d (fun j => (a j:ℝ)) p (w z) (uniformCode p hp (x z)) n i):UnitAddCircle)) := by
  apply measurable_pi_lambda
  intro i
  apply AddCircle.measurable_mk'.comp
  exact measurable_pathState d _ _ w _ hw (fun j => (measurable_uniformCode p hp j).comp hx) _ _

private theorem measurable_end_mean {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : Ω → ℕ → ℝ) (hw : ∀ i, Measurable (fun z => w z i))
    {Q : (Fin d → UnitAddCircle) → ℝ≥0∞} (hQ : Measurable Q) : Measurable (fun z => blockEndMean hp d a n (w z) Q) :=
  (hQ.comp (measurable_end_state hp d a n (fun z : Ω × ℝ => w z.1) Prod.snd
    (fun i => (hw i).comp measurable_fst) measurable_snd)).lintegral_prod_right'

private theorem end_mean_coherent {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ)
    {w u : ℕ → ℝ} (hw : ∀ i < d, (w i:UnitAddCircle) = (u i:UnitAddCircle))
    {Q : (Fin d → UnitAddCircle) → ℝ≥0∞} (hQ : Measurable Q) :
    blockEndMean hp d a n w Q = blockEndMean hp d a n u Q := by
  have hc {s t : ℕ → ℝ} (hst : ∀ i < d, s i = t i) (I : ℕ → Fin p) (j : ℕ) :
      ∀ i < d, pathState d (fun k => (a k:ℝ)) p s I j i = pathState d (fun k => (a k:ℝ)) p t I j i := by
    induction j with
    | zero => exact hst
    | succ j ih =>
      intro i hi
      cases i with
      | zero =>
        simp only [pathState,predecessor]
        congr 2
        exact Finset.sum_congr rfl (fun l hl => congrArg ((a l:ℝ)*·) (ih l (Finset.mem_range.mp hl)))
      | succ i => exact ih i (by omega)
  classical
  let k (i : ℕ) : ℤ := if h : i < d then (integer_offset_of_phase_eq (hw i h)).choose else 0
  have hk (i : ℕ) (hi : i < d) : w i = u i+(k i:ℝ) := by
    simpa only [k,dif_pos hi] using (integer_offset_of_phase_eq (hw i hi)).choose_spec
  let s (i : ℕ) := u i+(k i:ℝ)
  have hs : blockEndMean hp d a n w Q = blockEndMean hp d a n s Q := by
    apply lintegral_congr_ae (.of_forall _)
    intro x
    apply congrArg Q
    funext i
    exact congrArg ((↑) : ℝ → UnitAddCircle) (hc hk (uniformCode p hp x) n i i.isLt)
  let H (v : ℕ → UnitAddCircle) := Q (fun i : Fin d => shiftRegister (fun j => (u j:UnitAddCircle)) v n i)
  have hH : Measurable H := hQ.comp (measurable_pi_lambda _ (fun i => measurable_shiftRegister _ _ _))
  have hsu : (fun i => (s i:UnitAddCircle)) = (fun i => (u i:UnitAddCircle)) := by
    funext i
    simp [s]
  have hz (t : ℕ → ℝ) (ht : (fun i => (t i:UnitAddCircle)) = (fun i => (u i:UnitAddCircle))) :
      blockEndMean hp d a n t Q = ∫⁻ z, H z ∂unitLaw.map (observedPast hp d a t) := by
    rw [lintegral_map hH (measurable_observedPast hp d a t)]
    apply lintegral_congr_ae (.of_forall _)
    intro x
    apply congrArg Q
    funext i
    change _ = shiftRegister _ (codePast d a t (uniformCode p hp x)) n i
    rw [← ht,shiftRegister_reads_past]
  rw [hs,hz s hsu,hz u rfl]
  exact congrArg (fun μ : Measure (ℕ → UnitAddCircle) => ∫⁻ z, H z ∂μ) (observedPast_integer_shift hp d a u k)

private theorem blockEndMean_succ {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (w : ℕ → ℝ)
    {Q : (Fin d → UnitAddCircle) → ℝ≥0∞} (hQ : Measurable Q) :
    blockEndMean hp d a (n+1) w Q = ENNReal.ofReal ((p:ℝ)⁻¹) *
      ∑ i : Fin p, blockEndMean hp d a n (predecessor d (fun j => (a j:ℝ)) p w i) Q := by
  let E (i : Fin p) := {x : ℝ | uniformCode p hp x 0 = i}
  let F (x : ℝ) := Q (fun i : Fin d => (↑(pathState d (fun j => (a j:ℝ)) p w (uniformCode p hp x) (n+1) i):UnitAddCircle))
  have hF : Measurable F := hQ.comp (measurable_end_state hp d a _ (fun _ : ℝ => w) id (fun _ => measurable_const) measurable_id)
  have hE (i : Fin p) : MeasurableSet (E i) := measurableSet_eq_fun (measurable_uniformCode p hp 0) measurable_const
  have hd : Pairwise (Function.onFun Disjoint E) := by
    intro i j h
    exact Set.disjoint_left.mpr (fun _ hi hj => h (hi.symm.trans hj))
  have hc : (⋃ i, E i) = univ := iUnion_eq_univ_iff.mpr (fun x => ⟨_,rfl⟩)
  change (∫⁻ x, F x ∂unitLaw) = _
  rw [← Measure.restrict_univ (μ := unitLaw), ← hc,lintegral_iUnion hE hd,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∫⁻ x, F x ∂unitLaw.restrict {x | uniformCode p hp x 0 = i}) = _
  rw [restrict_seed_digit hp i,lintegral_smul_measure,lintegral_map hF (measurable_prefixSeed _ _),smul_eq_mul]
  congr 1
  apply lintegral_congr_ae
  have hm : ∀ᵐ x ∂unitLaw, x ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  filter_upwards [hm] with x hx
  apply congrArg Q
  funext j
  obtain ⟨h₀,h'⟩ := prefixSeed_codes hp (fun _ => i) 1 hx
  let J := uniformCode p hp (prefixSeed (fun _ => i) 1 x)
  have hz := pathState_append d (fun j => (a j:ℝ)) (p:ℝ) w J 1 n
  rw [Nat.add_comm 1 n] at hz
  change (↑(pathState d (fun t => (a t:ℝ)) p w J (n+1) j):UnitAddCircle) = _
  rw [hz,show (fun j => J (1+j)) = uniformCode p hp x from funext h',pathState,
    show J 0 = i from h₀ 0 (by decide)]
  rfl

/-- Uniform predecessor choices at *any block length* restore the full central
Haar law. Prefixes use the real lifts inherited at every intermediate step and
the true independent base-`p` stream. The test may be any nonnegative Borel
function of the terminal torus block. -/
theorem haar_blockEndMean {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (ha : a d ≠ 0) (n : ℕ)
    {Q : (Fin (d+1) → UnitAddCircle) → ℝ≥0∞} (hQ : Measurable Q) :
    (∫⁻ u : Fin (d+1) → UnitAddCircle, blockEndMean hp (d+1) a n (centralLift u) Q) = ∫⁻ u, Q u := by
  induction n with
  | zero =>
    have he (u : Fin (d+1) → UnitAddCircle) : blockEndMean hp (d+1) a 0 (centralLift u) Q = Q u := by
      have hh : (fun i : Fin (d+1) => (centralLift u i : UnitAddCircle)) = u := by
        funext i
        simp [centralLift,i.isLt,AddCircle.coe_equivIco]
      simp only [blockEndMean,pathState,hh,lintegral_const,measure_univ,mul_one]
    simp_rw [he]
  | succ n ih =>
    let H (u : Fin (d+1) → UnitAddCircle) := blockEndMean hp (d+1) a n (centralLift u) Q
    have hH : Measurable H := measurable_end_mean hp (d+1) a n centralLift (measurable_centralLift _) hQ
    have he (u : Fin (d+1) → UnitAddCircle) :
        blockEndMean hp (d+1) a (n+1) (centralLift u) Q = ∫⁻ x, H (torusPredecessor hp d a (u,x)) ∂unitLaw := by
      simp_rw [torusPredecessor_digit]
      rw [lintegral_first_digit hp (fun i => H (nextBlock d a u i)),blockEndMean_succ hp (d+1) a n _ hQ]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply end_mean_coherent hp (d+1) a n _ hQ
      intro j hj
      simp only [centralLift,dif_pos hj,AddCircle.coe_equivIco]
      rfl
    simp_rw [he]
    have h := torusPredecessor_stationary hp d a ha
    exact (lintegral_prod (fun z => H (torusPredecessor hp d a z)) (hH.comp h.measurable).aemeasurable).symm.trans
      ((h.lintegral_comp hH).trans ih)

/-- Words in which at most `m` of the `k` tested blocks are bad. -/
@[expose] def sparseStatusWords (k m : ℕ) : Finset (Fin k → Bool) :=
  Finset.univ.filter fun v => (Finset.univ.filter (fun i => v i = true)).card ≤ m

theorem status_weight (z : ℝ) {k : ℕ} (v : Fin k → Bool) :
    (∏ i, if v i = true then z else 1) = z^(Finset.univ.filter (fun i => v i = true)).card := by
  rw [Finset.prod_ite]
  simp

/-- Weighted binomial estimate. Choosing `z` small and then `m/k` small
makes the exponential growth rate of the number of possible words tend to one. -/
theorem sparseStatusWords_card (k m : ℕ) {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1) :
    ((sparseStatusWords k m).card : ℝ) ≤ (1+z)^k/z^m := by
  have he : (∑ v : Fin k → Bool, ∏ i, if v i = true then z else (1:ℝ)) = (1+z)^k := by
    rw [← Fintype.sum_pow (fun e : Bool => if e = true then z else (1:ℝ)) k]
    simp [add_comm]
  apply (le_div_iff₀ (pow_pos hz m)).mpr
  calc
    _ = ∑ v ∈ sparseStatusWords k m, z^m := by simp
    _ ≤ ∑ v ∈ sparseStatusWords k m, ∏ i, if v i = true then z else (1:ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [status_weight]
      exact pow_le_pow_of_le_one hz.le hz' (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v : Fin k → Bool, ∏ i, if v i = true then z else (1:ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v _ _
      exact Finset.prod_nonneg (fun i _ => by split <;> positivity)
    _ = _ := he

/-- The energy bound produced by any two-coefficient status recursion, for
each word with at most `m` bad symbols. `U` is the good coefficient, and a
bad step multiplies it by the additional factor `V`. -/
theorem sparseStatusWord_energy (E : List Bool → ℝ) {C U V : ℝ} (hC : 0 ≤ C) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hbase : E [] ≤ C) (hstep : ∀ s v, E (s::v) ≤ C + (U*(if s = true then V else 1))*E v)
    {k m : ℕ} {v : Fin k → Bool} (hv : v ∈ sparseStatusWords k m) :
    E (List.ofFn v) ≤ C*(k+1 : ℝ)*U^k*V^m := by
  let A (s : Bool) := U*(if s = true then V else 1)
  have hA (s : Bool) : 1 ≤ A s := by cases s <;> simp [A,hU,one_le_mul_of_one_le_of_one_le hU hV]
  have h := prescribed_status_energy E A C hC hA hbase hstep (List.ofFn v)
  have hm := (Finset.mem_filter.mp hv).2
  have hprod : ((List.ofFn v).map A).prod = U^k*V^(Finset.univ.filter (fun i => v i = true)).card := by
    rw [List.map_ofFn,List.prod_ofFn]
    simp only [A,Function.comp_def,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,status_weight]
  rw [hprod,List.length_ofFn] at h
  rw [← mul_assoc] at h
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV hm) (by positivity))

/-- On any parameter space, a submeasure of the sum of `N` status laws has
average collision at most `3 N²` times a common upper bound on their average
diagonal collisions. This applies to geometric interval partitions and to
polynomial predecessor cylinders, at the original collision radius. -/
theorem averaged_retained_collision {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (m : Measure Ω)
    (μ : Ω → Measure ℝ) (ν : Ω → ι → Measure ℝ) [∀ x, IsFiniteMeasure (μ x)]
    [∀ x i, IsFiniteMeasure (ν x i)] {r : ℝ} (hr : 0 < r) (hμ : ∀ x, μ x ≤ ∑ i, ν x i)
    {E : ℝ} (hν : ∀ i, Integrable (fun x => collision (ν x i) (ν x i) r) m)
    (hE : ∀ i, (∫ x, collision (ν x i) (ν x i) r ∂m) ≤ E) :
    (∫ x, collision (μ x) (μ x) r ∂m) ≤ 3*(Fintype.card ι : ℝ)^2*E := by
  let N : ℝ := Fintype.card ι
  have hn : 0 ≤ 3*N := by dsimp [N]; positivity
  have hpoint (x : Ω) : collision (μ x) (μ x) r ≤ 3*N * ∑ i, collision (ν x i) (ν x i) r := by
    have hm : collision (μ x) (μ x) r ≤ collision (∑ i,ν x i) (∑ i,ν x i) r :=
      ENNReal.toReal_mono (measure_ne_top _ _) (Measure.prod_mono (hμ x) (hμ x) _)
    rw [collision_sum] at hm
    have hh := neighbor_collision_bound (ν x) hr (fun _ _ => 1) (fun _ _ => zero_le_one) (fun _ _ => rfl) N
      (fun _ => by simp [N])
    simpa only [one_mul] using hm.trans (by simpa only [one_mul] using hh)
  have hsum : Integrable (fun x => ∑ i, collision (ν x i) (ν x i) r) m := integrable_finsetSum _ (fun i _ => hν i)
  calc
    _ ≤ ∫ x, 3*N*∑ i, collision (ν x i) (ν x i) r ∂m :=
      integral_mono_of_nonneg (.of_forall fun _ => measureReal_nonneg) (hsum.const_mul _) (.of_forall hpoint)
    _ = 3*N*∑ i, ∫ x, collision (ν x i) (ν x i) r ∂m := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hν i)]
    _ ≤ 3*N * ∑ _i : ι, E := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hE i)) hn
    _ = _ := by simp [N]; ring

/-- Mass lost by insisting on at most `m` bad symbols among `k` stages.
Only the individual bad probabilities are used; stages need not be
independent or identically distributed. -/
theorem sparseStatusWords_discard {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (k m : ℕ) (bits : Ω → Fin k → Bool) (hm : ∀ i, MeasurableSet {x | bits x i = true}) {e : ℝ≥0∞}
    (hbad : ∀ i, μ {x | bits x i = true} ≤ e) :
    μ {x | bits x ∉ sparseStatusWords k m} ≤ k*e/(m+1:ℕ) := by
  classical
  let B (i : Fin k) := {x | bits x i = true}
  let F (x : Ω) : ℝ≥0∞ := ∑ i : Fin k, (B i).indicator (fun _ => (1:ℝ≥0∞)) x
  have hF : Measurable F := Finset.measurable_fun_sum _ (fun i _ => measurable_const.indicator (hm i))
  have hsum : (∫⁻ x, F x ∂μ) ≤ k*e := by
    dsimp only [F]
    rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hm i))]
    simp_rw [lintegral_indicator_const (hm _),one_mul]
    exact (Finset.sum_le_sum (fun i _ => hbad i)).trans_eq (by simp)
  have he (x : Ω) : F x = (Finset.univ.filter (fun i => bits x i = true)).card := by
    simp [F,B,Set.indicator_apply,Finset.sum_boole]
  have hsub : {x | bits x ∉ sparseStatusWords k m} ⊆ {x | ((m+1:ℕ):ℝ≥0∞) ≤ F x} := by
    intro x hx
    have hn : ¬ (Finset.univ.filter (fun i => bits x i = true)).card ≤ m := by
      simpa [sparseStatusWords] using hx
    rw [Set.mem_ofPred_eq,he]
    exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hn)
  have hden : (((m+1:ℕ):ℝ≥0∞)) ≠ 0 := by positivity
  have h := meas_ge_le_lintegral_div (μ := μ) hF.aemeasurable hden (by finiteness : ((m+1:ℕ):ℝ≥0∞) ≠ ⊤)
  apply (measure_mono hsub).trans (h.trans _)
  rw [div_eq_mul_inv,div_eq_mul_inv]
  exact mul_le_mul_left hsum _

/-- Combined sparse-status estimate for a retained measure dominated by the
contributions of the admitted words. The same theorem accepts the physical
partition energy or the polynomial predecessor energy. -/
theorem retained_status_recursion_bound {Ω : Type*} [MeasurableSpace Ω] (mΩ : Measure Ω)
    (k m : ℕ) (μ : Ω → Measure ℝ) (ν : Ω → (Fin k → Bool) → Measure ℝ)
    [∀ x, IsFiniteMeasure (μ x)] [∀ x v, IsFiniteMeasure (ν x v)] {r : ℝ} (hr : 0 < r)
    (hμ : ∀ x, μ x ≤ ∑ v : sparseStatusWords k m, ν x v)
    (hν : ∀ v : sparseStatusWords k m, Integrable (fun x => collision (ν x v) (ν x v) r) mΩ)
    (E : List Bool → ℝ) {C U V z : ℝ} (hC : 0 ≤ C) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hz : 0 < z) (hz' : z ≤ 1) (hbase : E [] ≤ C)
    (hstep : ∀ s v, E (s::v) ≤ C + (U*(if s = true then V else 1))*E v)
    (hdiag : ∀ v : sparseStatusWords k m, (∫ x, collision (ν x v) (ν x v) r ∂mΩ) ≤ E (List.ofFn v.val)) :
    (∫ x, collision (μ x) (μ x) r ∂mΩ) ≤
      3*((1+z)^k/z^m)^2 * (C*(k+1:ℝ)*U^k*V^m) := by
  have h := averaged_retained_collision mΩ μ (fun x (v : sparseStatusWords k m) => ν x v) hr hμ hν
    (fun v => (hdiag v).trans (sparseStatusWord_energy E hC hU hV hbase hstep v.property))
  have hcard := sparseStatusWords_card k m hz hz'
  simp only [Fintype.card_coe] at h
  apply h.trans
  have hu := zero_le_one.trans hU
  have hv := zero_le_one.trans hV
  gcongr

/-- The actual subprobability of paths with a specified length-`n` prefix,
pushed forward to the displayed slope. -/
@[expose] def digitPrefix {p : ℕ} (hp : 0 < p) (n : ℕ) (x : ℝ) (i : Fin n) : Fin p := uniformCode p hp x i

theorem measurable_digitPrefix {p : ℕ} (hp : 0 < p) (n : ℕ) : Measurable (digitPrefix hp n) :=
  measurable_pi_lambda _ (fun i => measurable_uniformCode p hp i)

def prefixLaw {p : ℕ} (hp : 0 < p) (n : ℕ) (F : ℝ → ℝ) (v : Fin n → Fin p) : Measure ℝ :=
  (unitLaw.restrict {x | digitPrefix hp n x = v}).map F

instance {p : ℕ} (hp : 0 < p) (n : ℕ) (F : ℝ → ℝ) (v : Fin n → Fin p) :
    IsFiniteMeasure (prefixLaw hp n F v) := by unfold prefixLaw; infer_instance

/-- Exact decomposition under any pairwise prefix test. The measures on the
right already contain their prefix probabilities. This identifies sums of
non-neighbor cross collisions with the original two-sample event. -/
theorem tested_prefix_pair_collision {p : ℕ} (hp : 0 < p) (n : ℕ) {F : ℝ → ℝ} (hF : Measurable F)
    (H : (Fin n → Fin p) → (Fin n → Fin p) → Prop) [∀ i j, Decidable (H i j)] (r : ℝ) :
    (unitLaw.prod unitLaw).real {z : ℝ × ℝ | H (digitPrefix hp n z.1) (digitPrefix hp n z.2) ∧ |F z.1-F z.2| ≤ r} =
      ∑ i, ∑ j, if H i j then collision (prefixLaw hp n F i) (prefixLaw hp n F j) r else 0 := by
  classical
  let W := Fin n → Fin p
  let E (i : W) := {x | digitPrefix hp n x = i}
  let B := {z : ℝ × ℝ | |F z.1-F z.2| ≤ r}
  let A (v : W × W) : Set (ℝ × ℝ) := if H v.1 v.2 then B ∩ (E v.1 ×ˢ E v.2) else ∅
  let μ := unitLaw.prod unitLaw
  have hmE (i : W) : MeasurableSet (E i) := (measurable_digitPrefix hp n) (measurableSet_singleton i)
  have hmB : MeasurableSet B := measurableSet_le
    (continuous_abs.measurable.comp ((hF.comp measurable_fst).sub (hF.comp measurable_snd))) measurable_const
  have hm (v : W × W) : MeasurableSet (A v) := by
    dsimp [A]
    split
    · exact hmB.inter ((hmE _).prod (hmE _))
    · exact MeasurableSet.empty
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro v u hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    by_cases hv : H v.1 v.2
    · by_cases hu : H u.1 u.2
      · simp only [A,if_pos hv,if_pos hu,Set.mem_inter_iff,Set.mem_prod] at hx hy
        exact hne (Prod.ext (hx.2.1.symm.trans hy.2.1) (hx.2.2.symm.trans hy.2.2))
      · simp [A,hu] at hy
    · simp [A,hv] at hx
  have hu : {z : ℝ × ℝ | H (digitPrefix hp n z.1) (digitPrefix hp n z.2) ∧ |F z.1-F z.2| ≤ r} = ⋃ v, A v := by
    ext z
    constructor
    · rintro ⟨hz,hb⟩
      refine Set.mem_iUnion.mpr ⟨(digitPrefix hp n z.1,digitPrefix hp n z.2),?_⟩
      simp only [A,if_pos hz,Set.mem_inter_iff,Set.mem_prod]
      exact ⟨hb,rfl,rfl⟩
    · intro h
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
      by_cases hh : H v.1 v.2
      · simp only [A,if_pos hh,Set.mem_inter_iff,Set.mem_prod] at hv
        exact ⟨by rw [show digitPrefix hp n z.1 = v.1 from hv.2.1,show digitPrefix hp n z.2 = v.2 from hv.2.2];exact hh,hv.1⟩
      · simp [A,hh] at hv
  rw [hu,← (Weierstrass.Partition.hasSum_disjoint μ A hm hd).tsum_eq,tsum_fintype,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : H i j
  · simp only [A,if_pos h]
    unfold collision prefixLaw Measure.real
    have hb : MeasurableSet {v : ℝ × ℝ | |v.1-v.2| ≤ r} := PrefixEnergy.band_measurable r
    rw [Measure.map_prod_map _ _ hF hF, Measure.map_apply (hF.prodMap hF) hb,Measure.prod_restrict]
    change _ = ((unitLaw.prod unitLaw).restrict (E i ×ˢ E j) B).toReal
    rw [Measure.restrict_apply hmB]
  · simp [A,h]

/-- Haar estimate for the sum of actual, probability-weighted cross energies
over every non-neighbor pair of polynomial predecessor branches. -/
theorem haar_nonNeighbor_prefix_sum_rate {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) {b c g : ℝ}
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range d, (a k:ℝ)*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C = slopeSliceBound g c n ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ u : Fin d → UnitAddCircle, ENNReal.ofReal (let W := centralLift u
        let F := fun x => codedSlope d (fun i => (a i:ℝ)) p g W η (uniformCode p hp x)
        let S := fun v : Fin n → Fin p => truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W
          (fun k => η k+Real.pi/2) (extendWord hp v) n
        ∑ i, ∑ j, if (2*(1-g*c)⁻¹+1)*(g*c)^n < |S i-S j|
          then collision (prefixLaw hp n F i) (prefixLaw hp n F j) r else 0)) ≤ ENNReal.ofReal (C*r) := by
  obtain ⟨C,hC,hEq,hbound⟩ := haar_offDiagonal_collision_rate hp a hg hg' hc hc' hbc hpoly n
  refine ⟨C,hC,hEq,?_⟩
  intro η r hr
  apply le_trans _ (hbound η r hr)
  apply lintegral_mono
  intro u
  let W := centralLift u
  let F := fun x => codedSlope d (fun i => (a i:ℝ)) p g W η (uniformCode p hp x)
  let S := fun v : Fin n → Fin p => truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W
    (fun k => η k+Real.pi/2) (extendWord hp v) n
  let H := fun i j => (2*(1-g*c)⁻¹+1)*(g*c)^n < |S i-S j|
  have hF : Measurable F := measurable_coded_sample hp d a (fun _ : ℝ => W) (fun _ => measurable_const) id measurable_id η g
  have he (x : ℝ) : S (digitPrefix hp n x) =
      truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W (fun k => η k+Real.pi/2) (uniformCode p hp x) n :=
    truncatedSlope_congr _ _ _ _ _ _ _ _ _ (fun i hi => by simp [extendWord,digitPrefix,hi])
  change ENNReal.ofReal (∑ i, ∑ j, if H i j then collision (prefixLaw hp n F i) (prefixLaw hp n F j) r else 0) ≤ _
  rw [← tested_prefix_pair_collision hp n hF H r,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply measure_mono
  rintro z ⟨h,hb⟩
  change (2*(1-g*c)⁻¹+1)*(g*c)^n < |S (digitPrefix hp n z.1)-S (digitPrefix hp n z.2)| at h
  rw [he,he] at h
  exact ⟨h,hb⟩

theorem haar_nonNeighbor_prefix_sum {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) {b c g : ℝ}
    (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range d, (a k:ℝ)*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 ≤ r →
      (∫⁻ u : Fin d → UnitAddCircle, ENNReal.ofReal (let W := centralLift u
        let F := fun x => codedSlope d (fun i => (a i:ℝ)) p g W η (uniformCode p hp x)
        let S := fun v : Fin n → Fin p => truncatedSlope d (fun i => (a i:ℝ)) p (g*c) W
          (fun k => η k+Real.pi/2) (extendWord hp v) n
        ∑ i, ∑ j, if (2*(1-g*c)⁻¹+1)*(g*c)^n < |S i-S j|
          then collision (prefixLaw hp n F i) (prefixLaw hp n F j) r else 0)) ≤ ENNReal.ofReal (C*r) := by
  obtain ⟨C,hC,_,H⟩ := haar_nonNeighbor_prefix_sum_rate hp a hg hg' hc hc' hbc hpoly n
  exact ⟨C,hC,H⟩

theorem digitPrefix_event {p n : ℕ} (hp : 0 < p) (v : Fin n → Fin p) :
    {x | digitPrefix hp n x = v} = {x | ∀ j < n, uniformCode p hp x j = extendWord hp v j} := by
  ext x
  constructor
  · intro h j hj
    change digitPrefix hp n x = v at h
    simpa [digitPrefix,extendWord,hj] using congrFun h ⟨j,hj⟩
  · intro h
    funext i
    simpa [digitPrefix,extendWord,i.isLt] using h i i.isLt

private theorem lintegral_digitPrefix {p : ℕ} (hp : 0 < p) (n : ℕ) (f : (Fin n → Fin p) → ℝ≥0∞) :
    (∫⁻ x, f (digitPrefix hp n x) ∂unitLaw) = ENNReal.ofReal ((p:ℝ)⁻¹^n)*∑ v, f v := by
  classical
  let E (v : Fin n → Fin p) := {x | digitPrefix hp n x = v}
  have hE (v : Fin n → Fin p) : MeasurableSet (E v) := (measurable_digitPrefix hp n) (measurableSet_singleton v)
  have hmass (v : Fin n → Fin p) : unitLaw (E v) = ENNReal.ofReal ((p:ℝ)⁻¹^n) := by
    rw [show E v = _ from digitPrefix_event hp v]
    exact uniformCode_cylinder_mass hp _ _
  have he (x : ℝ) : f (digitPrefix hp n x) = ∑ v, (E v).indicator (fun _ => f v) x := by
    simp [E,Set.indicator_apply,eq_comm]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hE i)),Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [lintegral_indicator_const (hE i),hmass,mul_comm])

@[expose] def blockState {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (u : Fin d → UnitAddCircle)
    (v : Fin n → Fin p) (i : Fin d) : UnitAddCircle :=
  ↑(pathState d (fun j => (a j:ℝ)) p (centralLift u) (extendWord hp v) n i)

theorem blockEndMean_prefix_sum {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (u : Fin d → UnitAddCircle)
    (Q : (Fin d → UnitAddCircle) → ℝ≥0∞) :
    blockEndMean hp d a n (centralLift u) Q = ENNReal.ofReal ((p:ℝ)⁻¹^n) *
      ∑ v, Q (blockState hp d a n u v) := by
  rw [← lintegral_digitPrefix hp n (fun v => Q (blockState hp d a n u v))]
  apply lintegral_congr_ae (.of_forall _)
  intro x
  apply congrArg Q
  funext i
  unfold blockState
  rw [pathState_prefix d (fun j => (a j:ℝ)) p (centralLift u) (I := uniformCode p hp x)
    (J := extendWord hp (digitPrefix hp n x)) n (fun j hj => by simp [digitPrefix,extendWord,hj])]

theorem baseSlopeLaw_coherent {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) {w u : ℕ → ℝ}
    (hw : ∀ i < d, (w i:UnitAddCircle) = (u i:UnitAddCircle)) (η : ℕ → ℝ) (g : ℝ) :
    baseSlopeLaw hp d a w η g = baseSlopeLaw hp d a u η g := by
  classical
  let k (i : ℕ) : ℤ := if h : i < d then (integer_offset_of_phase_eq (hw i h)).choose else 0
  have hk (i : ℕ) (hi : i < d) : w i = u i+(k i:ℝ) := by
    simpa only [k,dif_pos hi] using (integer_offset_of_phase_eq (hw i hi)).choose_spec
  calc
    _ = baseSlopeLaw hp d a (fun i => u i+(k i:ℝ)) η g := by
      simp only [baseSlopeLaw,codedSlope_block_congr (p := p) d a hk η g]
    _ = _ := slope_law_integer_shift hp d a u η k g

/-- Canonical disintegration of an actual prefix slope law. The normalized
tail law lives on its finite torus state; no imposition on intermediate real
lifts or phase string is required. -/
theorem prefixLaw_torus_child {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (u : Fin d → UnitAddCircle)
    (v : Fin n → Fin p) (η : ℕ → ℝ) {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) :
    let F := fun x => codedSlope d (fun j => (a j:ℝ)) p g (centralLift u) η (uniformCode p hp x)
    let b := truncatedSlope d (fun j => (a j:ℝ)) p g (centralLift u) η (extendWord hp v) n
    prefixLaw hp n F v = ENNReal.ofReal ((p:ℝ)⁻¹^n) •
      (baseSlopeLaw hp d a (centralLift (blockState hp d a n u v)) (fun l => η (n+l)) g).map (fun y => b+g^n*y) := by
  intro F b
  let W := pathState d (fun j => (a j:ℝ)) p (centralLift u) (extendWord hp v) n
  let U := blockState hp d a n u v
  have hW (j : ℕ) (hj : j < d) : (W j:UnitAddCircle) = (centralLift U j:UnitAddCircle) := by
    simp only [centralLift,dif_pos hj,AddCircle.coe_equivIco]
    rfl
  have he := restricted_slope_prefix_law hp d (fun j => (a j:ℝ)) p (centralLift u) η (extendWord hp v) n hg hg'
    (T := univ) MeasurableSet.univ
  simp only [Set.preimage_univ,Measure.restrict_univ,← digitPrefix_event hp v] at he
  change prefixLaw hp n F v = _ • (baseSlopeLaw hp d a W (fun l => η (n+l)) g).map (fun y => b+g^n*y) at he
  rw [baseSlopeLaw_coherent hp d a hW] at he
  exact he

private theorem collision_mono {μ μ' ν ν' : Measure ℝ} [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hμ : μ ≤ μ') (hν : ν ≤ ν') (r : ℝ) : collision μ ν r ≤ collision μ' ν' r :=
  ENNReal.toReal_mono (measure_ne_top _ _) (Measure.prod_mono hμ hν _)

theorem marked_block_collision {ι : Type*} [Fintype ι] (ν full : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] [∀ i, IsFiniteMeasure (full i)] (z : ι → ℝ)
    {r h s : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : 0 ≤ s)
    (accept : ι → Bool) (far : ι → ι → Prop) [∀ i j, Decidable (far i j)]
    (hsym : ∀ i j, far i j ↔ far j i) {D : ℝ} (hD₀ : 0 ≤ D)
    (hD : ∀ i, (∑ j, if accept i = true ∧ accept j = true ∧ ¬ far i j then (1:ℝ) else 0) ≤ D)
    (hfull : ∀ i, ENNReal.ofReal s • (ν i).map (fun x => z i+h*x) ≤ full i) :
    let parent := ∑ i, ENNReal.ofReal s •
      ((if accept i = true then ν i else 0) : Measure ℝ).map (fun x => z i+h*x)
    collision parent parent r ≤ (∑ i, ∑ j, if far i j then collision (full i) (full j) r else 0) +
      (3*D*s^2)*∑ i, collision (ν i) (ν i) (r/h) := by
  intro parent
  let N (i : ι) : Measure ℝ := if accept i = true then ν i else 0
  let W (i : ι) := (N i).map (fun x => z i+h*x)
  let M (i j : ι) : ℝ := if accept i = true ∧ accept j = true ∧ ¬ far i j then 1 else 0
  have hN (i : ι) : IsFiniteMeasure (N i) := by dsimp [N]; split <;> infer_instance
  have hM (i j : ι) : 0 ≤ M i j := by dsimp [M]; split <;> norm_num
  have hMsym (i j : ι) : M i j = M j i := by
    by_cases hf : far i j
    · simp [M,hf,(hsym i j).mp hf]
    · have hf' : ¬ far j i := fun h => hf ((hsym i j).mpr h)
      simp [M,hf,hf',and_comm]
  have hstep := block_collision_recursion N z hr hh hs M hM hMsym D hD
  have hdiag (i : ι) : collision (N i) (N i) (r/h) ≤ collision (ν i) (ν i) (r/h) := by
    have hle : N i ≤ ν i := by
      by_cases hi : accept i = true
      · simp only [N,if_pos hi,le_refl]
      · simp only [N,if_neg hi]
        exact bot_le
    exact collision_mono hle hle _
  have hfar (i j : ι) : s^2*((1-M i j)*collision (W i) (W j) r) ≤
      if far i j then collision (full i) (full j) r else 0 := by
    have hright : 0 ≤ if far i j then collision (full i) (full j) r else 0 := by
      split
      · exact measureReal_nonneg
      · rfl
    by_cases hi : accept i = true
    · by_cases hj : accept j = true
      · by_cases hf : far i j
        · simp only [M,hi,hj,hf,not_true_eq_false,and_false,if_false,sub_zero,one_mul,if_true,W,N]
          rw [← collision_smul _ _ hs]
          exact collision_mono (hfull i) (hfull j) _
        · simp [M,hi,hj,hf]
      · simpa [W,N,hj,collision] using hright
    · simpa [W,N,hi,collision] using hright
  have hf : s^2*(∑ i, ∑ j, (1-M i j)*collision (W i) (W j) r) ≤
      ∑ i, ∑ j, if far i j then collision (full i) (full j) r else 0 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hfar i j))
  apply hstep.trans
  apply add_le_add hf
  rw [← mul_assoc,mul_comm (s^2) (3*D)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hdiag i)) (by positivity)

def separatedPrefixes {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c : ℝ) (η : ℕ → ℝ)
    (u : Fin d → UnitAddCircle) (i j : Fin n → Fin p) : Prop :=
  let S := fun v : Fin n → Fin p => truncatedSlope d (fun k => (a k:ℝ)) p (g*c) (centralLift u)
    (fun k => η k+Real.pi/2) (extendWord hp v) n
  (2*(1-g*c)⁻¹+1)*(g*c)^n < |S i-S j|

noncomputable instance {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c : ℝ) (η : ℕ → ℝ)
    (u : Fin d → UnitAddCircle) (i j : Fin n → Fin p) : Decidable (separatedPrefixes hp d a n g c η u i j) := Classical.propDecidable _

/-- The actual first-block affine mixture with a prescribed initial mark and a
common family of restricted continuations at the inherited states. -/
def markedSlopeLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g : ℝ) (η : ℕ → ℝ)
    (accept : (Fin d → UnitAddCircle) → (Fin n → Fin p) → Bool) (ξ : (Fin d → UnitAddCircle) → Measure ℝ)
    (u : Fin d → UnitAddCircle) : Measure ℝ :=
  ∑ i : Fin n → Fin p, ENNReal.ofReal ((p:ℝ)⁻¹^n) •
    ((if accept u i = true then ξ (blockState hp d a n u i) else 0) : Measure ℝ).map (fun x =>
      truncatedSlope d (fun k => (a k:ℝ)) p g (centralLift u) η (extendWord hp i) n + g^n*x)

/-- Haar-averaged conditional collision recursion at every derivative index
for an actual prefix mixture and arbitrary dominated continuation laws.
The error is `Cₙ r`; the diagonal coefficient is `3 D / pⁿ`, including the
full stationary averaging over inherited real-lift blocks. -/
theorem haar_marked_block_recursion_rate {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C = slopeSliceBound g c n ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 < r →
      ∀ (accept : (Fin (d+1) → UnitAddCircle) → (Fin n → Fin p) → Bool) (D : ℝ), 0 ≤ D →
      (∀ u i, (∑ j, if accept u i = true ∧ accept u j = true ∧ ¬ separatedPrefixes hp (d+1) a n g c η u i j
        then (1:ℝ) else 0) ≤ D) → ∀ ξ : (Fin (d+1) → UnitAddCircle) → Measure ℝ, (∀ u, IsFiniteMeasure (ξ u)) →
      (∀ u, ξ u ≤ baseSlopeLaw hp (d+1) a (centralLift u) (fun l => η (n+l)) g) →
      Measurable (fun u => ENNReal.ofReal (collision (ξ u) (ξ u) (r/g^n))) →
      (∫⁻ u : Fin (d+1) → UnitAddCircle, let μ := markedSlopeLaw hp (d+1) a n g η accept ξ u
        ENNReal.ofReal (collision μ μ r)) ≤ ENNReal.ofReal (C*r) + ENNReal.ofReal (3*D*(p:ℝ)⁻¹^n) *
        (∫⁻ u : Fin (d+1) → UnitAddCircle, ENNReal.ofReal (collision (ξ u) (ξ u) (r/g^n))) := by
  obtain ⟨C,hC,hEq,hbound⟩ := haar_nonNeighbor_prefix_sum_rate hp a hg hg' hc hc' hbc hpoly n
  refine ⟨C,hC,hEq,?_⟩
  intro η r hr accept D hD₀ hD ξ hξ hdom hmeas
  let s := (p:ℝ)⁻¹^n
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let Ω := Fin (d+1) → UnitAddCircle
  let F (u : Ω) (x : ℝ) := codedSlope (d+1) (fun j => (a j:ℝ)) p g (centralLift u) η (uniformCode p hp x)
  let far (u : Ω) := separatedPrefixes hp (d+1) a n g c η u
  let L (u : Ω) (i : Fin n → Fin p) := prefixLaw hp n (F u) i
  let Z (u : Ω) (i : Fin n → Fin p) := truncatedSlope (d+1) (fun k => (a k:ℝ)) p g (centralLift u) η (extendWord hp i) n
  let off (u : Ω) := ∑ i, ∑ j, if far u i j then collision (L u i) (L u j) r else 0
  let Q (u : Ω) := ENNReal.ofReal (collision (ξ u) (ξ u) (r/g^n))
  let gain := ENNReal.ofReal (3*D*s)
  have hpnt (u : Ω) : ENNReal.ofReal (let μ := markedSlopeLaw hp (d+1) a n g η accept ξ u
      collision μ μ r) ≤ ENNReal.ofReal (off u) + gain*blockEndMean hp (d+1) a n (centralLift u) Q := by
    let ν (i : Fin n → Fin p) := ξ (blockState hp (d+1) a n u i)
    have hfull (i : Fin n → Fin p) : ENNReal.ofReal s • (ν i).map (fun x => Z u i+g^n*x) ≤ L u i := by
      change _ ≤ prefixLaw hp n (F u) i
      rw [show prefixLaw hp n (F u) i = _ from prefixLaw_torus_child hp (d+1) a n u i η hg.le hg']
      apply _root_.smul_le_smul_left
      exact Measure.map_mono (hdom _) (measurable_const.add (measurable_const.mul measurable_id))
    have hsym (i j : Fin n → Fin p) : far u i j ↔ far u j i := by
      dsimp [far,separatedPrefixes]
      rw [abs_sub_comm]
    have h := marked_block_collision ν (L u) (Z u) hr (pow_pos hg n) hs (accept u) (far u) hsym hD₀ (hD u) hfull
    have hdiag (i : Fin n → Fin p) : 0 ≤ collision (ν i) (ν i) (r/g^n) := measureReal_nonneg
    have hoff : 0 ≤ off u := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      split
      · exact measureReal_nonneg
      · rfl))
    have hd : 0 ≤ ∑ i, collision (ν i) (ν i) (r/g^n) := Finset.sum_nonneg (fun i _ => hdiag i)
    have hcoef : 0 ≤ 3*D*s^2 := by positivity
    apply (ENNReal.ofReal_le_ofReal h).trans_eq
    change ENNReal.ofReal (off u + (3*D*s^2)*∑ i, collision (ν i) (ν i) (r/g^n)) = _
    rw [ENNReal.ofReal_add hoff (mul_nonneg hcoef hd),blockEndMean_prefix_sum]
    congr 1
    change ENNReal.ofReal ((3*D*s^2)*∑ i, collision (ν i) (ν i) (r/g^n)) =
      ENNReal.ofReal (3*D*s)*(ENNReal.ofReal s*∑ i, ENNReal.ofReal (collision (ν i) (ν i) (r/g^n)))
    rw [ENNReal.ofReal_mul hcoef,ENNReal.ofReal_sum_of_nonneg (fun i _ => hdiag i),
      show 3*D*s^2=3*D*s*s by ring,ENNReal.ofReal_mul (by positivity : 0 ≤ 3*D*s),mul_assoc]
  apply (lintegral_mono hpnt).trans
  have hE : Measurable (fun u : Ω => blockEndMean hp (d+1) a n (centralLift u) Q) :=
    measurable_end_mean hp (d+1) a n centralLift (measurable_centralLift _) hmeas
  have hG : Measurable (fun u : Ω => gain*blockEndMean hp (d+1) a n (centralLift u) Q) := measurable_const.mul hE
  rw [lintegral_add_right (fun u : Ω => ENNReal.ofReal (off u)) hG,lintegral_const_mul gain hE,haar_blockEndMean hp d a ha n (Q := Q) hmeas]
  exact add_le_add_left (hbound η r hr.le) _

theorem haar_marked_block_recursion {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℕ → ℝ) (r : ℝ), 0 < r →
      ∀ (accept : (Fin (d+1) → UnitAddCircle) → (Fin n → Fin p) → Bool) (D : ℝ), 0 ≤ D →
      (∀ u i, (∑ j, if accept u i = true ∧ accept u j = true ∧ ¬ separatedPrefixes hp (d+1) a n g c η u i j
        then (1:ℝ) else 0) ≤ D) → ∀ ξ : (Fin (d+1) → UnitAddCircle) → Measure ℝ, (∀ u, IsFiniteMeasure (ξ u)) →
      (∀ u, ξ u ≤ baseSlopeLaw hp (d+1) a (centralLift u) (fun l => η (n+l)) g) →
      Measurable (fun u => ENNReal.ofReal (collision (ξ u) (ξ u) (r/g^n))) →
      (∫⁻ u : Fin (d+1) → UnitAddCircle, let μ := markedSlopeLaw hp (d+1) a n g η accept ξ u
        ENNReal.ofReal (collision μ μ r)) ≤ ENNReal.ofReal (C*r) + ENNReal.ofReal (3*D*(p:ℝ)⁻¹^n) *
        (∫⁻ u : Fin (d+1) → UnitAddCircle, ENNReal.ofReal (collision (ξ u) (ξ u) (r/g^n))) := by
  obtain ⟨C,hC,_,H⟩ := haar_marked_block_recursion_rate hp a ha hg hg' hc hc' hbc hpoly n
  exact ⟨C,hC,H⟩

private theorem prefixLaw_sum {p : ℕ} (hp : 0 < p) (n : ℕ) {F : ℝ → ℝ} (hF : Measurable F) :
    (∑ v, prefixLaw hp n F v) = unitLaw.map F := by
  let E (v : Fin n → Fin p) := {x | digitPrefix hp n x = v}
  have hE (v : Fin n → Fin p) : MeasurableSet (E v) := (measurable_digitPrefix hp n) (measurableSet_singleton v)
  have hd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun _ hi hj => hij (hi.symm.trans hj))
  have hu : (⋃ v, E v) = univ := iUnion_eq_univ_iff.mpr (fun x => ⟨_,rfl⟩)
  have h := congrArg (fun μ : Measure ℝ => μ.map F) (Measure.restrict_iUnion (μ := unitLaw) hd hE)
  rw [hu,Measure.restrict_univ] at h
  rw [Measure.map_sum hF.aemeasurable,Measure.sum_fintype] at h
  exact h.symm

theorem baseSlopeLaw_univ {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ) (g : ℝ) :
    baseSlopeLaw hp d a w η g univ = 1 := by
  have hm := measurable_coded_sample hp d a (fun _ : ℝ => w) (fun _ => measurable_const) id measurable_id η g
  unfold baseSlopeLaw
  simp only [id_eq] at hm
  rw [Measure.map_apply hm MeasurableSet.univ]
  simp

theorem markedSlopeLaw_domination {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (η : ℕ → ℝ)
    (accept : (Fin d → UnitAddCircle) → (Fin n → Fin p) → Bool) (ξ : (Fin d → UnitAddCircle) → Measure ℝ)
    (hξ : ∀ u, ξ u ≤ baseSlopeLaw hp d a (centralLift u) (fun l => η (n+l)) g) (u : Fin d → UnitAddCircle) :
    markedSlopeLaw hp d a n g η accept ξ u ≤ baseSlopeLaw hp d a (centralLift u) η g := by
  let F (x : ℝ) := codedSlope d (fun j => (a j:ℝ)) p g (centralLift u) η (uniformCode p hp x)
  have hF : Measurable F := measurable_coded_sample hp d a (fun _ : ℝ => centralLift u) (fun _ => measurable_const) id measurable_id η g
  change _ ≤ unitLaw.map F
  rw [← prefixLaw_sum hp n hF]
  apply Finset.sum_le_sum
  intro i _
  rw [show prefixLaw hp n F i = _ from prefixLaw_torus_child hp d a n u i η hg hg']
  apply _root_.smul_le_smul_left
  apply Measure.map_mono _ (measurable_const.add (measurable_const.mul measurable_id))
  split
  · exact hξ _
  · exact bot_le

def prefixDegree {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c : ℝ) (η : ℕ → ℝ)
    (u : Fin d → UnitAddCircle) (i : Fin n → Fin p) : ℕ :=
  (Finset.univ.filter (fun j => ¬ separatedPrefixes hp d a n g c η u i j)).card

def acceptsStatus {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c T : ℝ) (η : ℕ → ℝ) (b : Bool)
    (u : Fin d → UnitAddCircle) (i : Fin n → Fin p) : Bool :=
  decide (decide (T < (prefixDegree hp d a n g c η u i:ℝ)) = b)

private theorem status_rows {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c T : ℝ)
    (hT : 0 ≤ T) (η : ℕ → ℝ) (b : Bool) (u : Fin d → UnitAddCircle) (i : Fin n → Fin p) :
    let A := acceptsStatus hp d a n g c T η b u
    (∑ j, if A i = true ∧ A j = true ∧ ¬ separatedPrefixes hp d a n g c η u i j then (1:ℝ) else 0) ≤
      if b = true then (p:ℝ)^n else T := by
  intro A
  let D := prefixDegree hp d a n g c η u i
  have hD : (∑ j : Fin n → Fin p, if ¬ separatedPrefixes hp d a n g c η u i j then (1:ℝ) else 0) = D := by
    exact Finset.sum_boole _ _
  have hcard : D ≤ p^n := by
    simpa [D,prefixDegree] using Finset.card_filter_le (Finset.univ : Finset (Fin n → Fin p)) (fun j => ¬ separatedPrefixes hp d a n g c η u i j)
  by_cases hi : A i = true
  · apply le_trans _ (show (D:ℝ) ≤ _ from ?_)
    · rw [← hD]
      apply Finset.sum_le_sum
      intro j _
      split <;> split <;> simp_all
    · cases b
      · have hb : ¬ T < (D:ℝ) := by simpa [A,acceptsStatus,D] using hi
        simpa using (le_of_not_gt hb)
      · simpa using (show (D:ℝ) ≤ (p:ℝ)^n by exact_mod_cast hcard)
  · cases b <;> simp [hi,hT]

/-- Restricted slope family for any prescribed good/bad word. Each mark
uses the true degree of its initial polynomial prefix, and each continuation
reads the shifted phases from its canonical torus state. -/
def statusSlopeLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c T : ℝ) :
    List Bool → (ℕ → ℝ) → (Fin d → UnitAddCircle) → Measure ℝ
  | [], η, u => baseSlopeLaw hp d a (centralLift u) η g
  | b::v, η, u => markedSlopeLaw hp d a n g η (acceptsStatus hp d a n g c T η b)
    (statusSlopeLaw hp d a n g c T v (fun l => η (n+l))) u

theorem statusSlopeLaw_domination {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (v : List Bool) (η : ℕ → ℝ) (u : Fin d → UnitAddCircle) :
    statusSlopeLaw hp d a n g c T v η u ≤ baseSlopeLaw hp d a (centralLift u) η g := by
  induction v generalizing η u with
  | nil => exact le_rfl
  | cons b v ih => exact markedSlopeLaw_domination hp d a n hg hg' η _ _ (fun w => ih _ w) u

private theorem measurable_blockState {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (v : Fin n → Fin p) :
    Measurable (fun u => blockState hp d a n u v) := by
  apply measurable_pi_lambda
  intro i
  apply AddCircle.measurable_mk'.comp
  exact measurable_pathState d _ _ centralLift (fun _ => extendWord hp v) (measurable_centralLift d)
    (fun _ => measurable_const) n i

private theorem measurable_truncated_block {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g : ℝ) (η : ℕ → ℝ) (I : ℕ → Fin p) :
    Measurable (fun u : Fin d → UnitAddCircle => truncatedSlope d (fun j => (a j:ℝ)) p g (centralLift u) η I n) := by
  apply Finset.measurable_fun_sum
  intro i _
  apply measurable_const.mul
  apply Real.continuous_sin.measurable.comp
  apply Measurable.add_const
  apply measurable_const.mul
  exact measurable_pathState d _ _ centralLift (fun _ => I) (measurable_centralLift d) (fun _ => measurable_const) _ _

private theorem measurable_acceptsStatus {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ)
    (g c T : ℝ) (η : ℕ → ℝ) (b : Bool) (v : Fin n → Fin p) :
    MeasurableSet {u | acceptsStatus hp d a n g c T η b u v = true} := by
  let hS (i : Fin n → Fin p) := measurable_truncated_block d a n (g*c) (fun k => η k+Real.pi/2) (extendWord hp i)
  have hf (i : Fin n → Fin p) : MeasurableSet {u | separatedPrefixes hp d a n g c η u v i} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hS v).sub (hS i)))
  have hd : Measurable (fun u => (prefixDegree hp d a n g c η u v:ℝ)) := by
    have he (u) : (prefixDegree hp d a n g c η u v:ℝ) =
        ∑ i, if ¬ separatedPrefixes hp d a n g c η u v i then (1:ℝ) else 0 :=
      (Finset.sum_boole _ _).symm
    simp_rw [he]
    exact Finset.measurable_fun_sum _ (fun i _ => measurable_const.ite (hf i).compl measurable_const)
  cases b
  · simpa [acceptsStatus] using measurableSet_le hd (measurable_const (a := T))
  · simpa [acceptsStatus] using measurableSet_lt (measurable_const (a := T)) hd

theorem measurable_baseSlopeLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (η : ℕ → ℝ) (g : ℝ) :
    Measurable (fun u : Fin d → UnitAddCircle => baseSlopeLaw hp d a (centralLift u) η g) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  let F (z : (Fin d → UnitAddCircle) × ℝ) := codedSlope d (fun j => (a j:ℝ)) p g (centralLift z.1) η (uniformCode p hp z.2)
  have hF : Measurable F := measurable_coded_sample hp d a (fun z : (Fin d → UnitAddCircle) × ℝ => centralLift z.1)
    (fun i => (measurable_centralLift _ _).comp measurable_fst) Prod.snd measurable_snd η g
  have he (u : Fin d → UnitAddCircle) : baseSlopeLaw hp d a (centralLift u) η g B = unitLaw (Prod.mk u ⁻¹' (F ⁻¹' B)) :=
    Measure.map_apply (hF.comp measurable_prodMk_left) hB
  simp_rw [he]
  exact measurable_measure_prodMk_left (hF hB)

theorem measurable_map_affine {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure ℝ) (hν : Measurable ν)
    (hbd : ∀ u, ν u univ ≤ 1) {Z : Ω → ℝ} (hZ : Measurable Z) (h : ℝ) :
    Measurable (fun u => (ν u).map (fun x => Z u+h*x)) := by
  let K : ProbabilityTheory.Kernel Ω ℝ := ⟨ν,hν⟩
  let : ProbabilityTheory.IsFiniteKernel K := ⟨1,ENNReal.one_lt_top,hbd⟩
  apply Measure.measurable_of_measurable_coe
  intro B hB
  let E := (fun y : Ω × ℝ => Z y.1+h*y.2) ⁻¹' B
  have hE : MeasurableSet E := ((hZ.comp measurable_fst).add (measurable_const.mul measurable_snd)) hB
  have he (u : Ω) : ((ν u).map (fun x => Z u+h*x)) B = K u (Prod.mk u ⁻¹' E) :=
    Measure.map_apply (measurable_const.add (measurable_const.mul measurable_id)) hB
  simp_rw [he]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hE

private theorem measurable_markedSlopeLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g : ℝ)
    (η : ℕ → ℝ) (accept : (Fin d → UnitAddCircle) → (Fin n → Fin p) → Bool)
    (hA : ∀ i, MeasurableSet {u | accept u i = true}) (ξ : (Fin d → UnitAddCircle) → Measure ℝ)
    (hξ : Measurable ξ) (hbd : ∀ u, ξ u univ ≤ 1) : Measurable (markedSlopeLaw hp d a n g η accept ξ) := by
  apply Finset.measurable_fun_sum
  intro i _
  let ρ (u : Fin d → UnitAddCircle) := if accept u i = true then ξ (blockState hp d a n u i) else 0
  have hρ : Measurable ρ := (hξ.comp (measurable_blockState hp d a n i)).ite (hA i) measurable_const
  have hb (u : Fin d → UnitAddCircle) : ρ u univ ≤ 1 := by
    dsimp [ρ]
    split
    · exact hbd _
    · simp
  have hM := measurable_map_affine ρ hρ hb (measurable_truncated_block d a n g η (extendWord hp i)) (g^n)
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp only [Measure.smul_apply, smul_eq_mul]
  exact measurable_const.mul ((Measure.measurable_coe hB).comp hM)

theorem measurable_statusSlopeLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (v : List Bool) (η : ℕ → ℝ) :
    Measurable (statusSlopeLaw hp d a n g c T v η) := by
  induction v generalizing η with
  | nil => exact measurable_baseSlopeLaw hp d a η g
  | cons b v ih =>
    apply measurable_markedSlopeLaw hp d a n g η _ (measurable_acceptsStatus hp d a n g c T η b)
      _ (ih (fun l => η (n+l)))
    intro u
    exact (statusSlopeLaw_domination hp d a n hg hg' c T v _ u univ).trans_eq (baseSlopeLaw_univ hp d a _ _ _)

open ProbabilityTheory in
theorem measurable_diagonal_collision {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure ℝ)
    (hν : Measurable ν) (hbd : ∀ u, ν u univ ≤ 1) (r : ℝ) :
    Measurable (fun u => ENNReal.ofReal (collision (ν u) (ν u) r)) := by
  let K : Kernel Ω ℝ := ⟨ν,hν⟩
  let : IsFiniteKernel K := ⟨1,ENNReal.one_lt_top,hbd⟩
  have he (u : Ω) : ENNReal.ofReal (collision (ν u) (ν u) r) = (K.prod K) u (PrefixEnergy.band r) := by
    have hi : IsFiniteMeasure (ν u) := ⟨(hbd u).trans_lt ENNReal.one_lt_top⟩
    rw [Kernel.prod_apply]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  simp_rw [he]
  exact (K.prod K).measurable_coe (PrefixEnergy.band_measurable r)

/-- The complete energy recurrence for the actual prescribed binary status
words in Appendix B. The bad mark uses the trivial degree cap `p^n`; the
good mark uses exactly the supplied threshold on the true number of neighbors.
All measures, branch weights, row counts and averaged diagonal energies are
instantiated, with no assumed correlation estimates. -/
theorem statusWord_collision_recursion_rate {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ C = slopeSliceBound g c n ∧ ∀ (η : ℕ → ℝ) (s : Bool) (v : List Bool) (r : ℝ), 0 < r →
      (∫⁻ u : Fin (d+1) → UnitAddCircle, let μ := statusSlopeLaw hp (d+1) a n g c T (s::v) η u
        ENNReal.ofReal (collision μ μ r)) ≤ ENNReal.ofReal (C*r) +
        ENNReal.ofReal (3*(if s = true then (p:ℝ)^n else T)*(p:ℝ)⁻¹^n) *
        (∫⁻ u : Fin (d+1) → UnitAddCircle, let μ := statusSlopeLaw hp (d+1) a n g c T v (fun l => η (n+l)) u
          ENNReal.ofReal (collision μ μ (r/g^n))) := by
  obtain ⟨C,hC,hEq,hbound⟩ := haar_marked_block_recursion_rate hp a ha hg hg' hc hc' hbc hpoly n
  refine ⟨C,hC,hEq,?_⟩
  intro η s v r hr
  let ξ := statusSlopeLaw hp (d+1) a n g c T v (fun l => η (n+l))
  have hdom := statusSlopeLaw_domination hp (d+1) a n hg.le hg' c T v (fun l => η (n+l))
  have hbd (u : Fin (d+1) → UnitAddCircle) : ξ u univ ≤ 1 := (hdom u univ).trans_eq (baseSlopeLaw_univ hp _ a _ _ _)
  have hξ (u : Fin (d+1) → UnitAddCircle) : IsFiniteMeasure (ξ u) := ⟨(hbd u).trans_lt ENNReal.one_lt_top⟩
  apply hbound η r hr _ _ _ (status_rows hp (d+1) a n g c T hT η s) ξ hξ hdom
  · exact measurable_diagonal_collision ξ (measurable_statusSlopeLaw hp _ a n hg.le hg' c T v _) hbd _
  · split
    · positivity
    · exact hT

theorem statusWord_collision_recursion {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℕ → ℝ) (s : Bool) (v : List Bool) (r : ℝ), 0 < r →
      (∫⁻ u : Fin (d+1) → UnitAddCircle, let μ := statusSlopeLaw hp (d+1) a n g c T (s::v) η u
        ENNReal.ofReal (collision μ μ r)) ≤ ENNReal.ofReal (C*r) +
        ENNReal.ofReal (3*(if s = true then (p:ℝ)^n else T)*(p:ℝ)⁻¹^n) *
        (∫⁻ u : Fin (d+1) → UnitAddCircle, let μ := statusSlopeLaw hp (d+1) a n g c T v (fun l => η (n+l)) u
          ENNReal.ofReal (collision μ μ (r/g^n))) := by
  obtain ⟨C,hC,_,H⟩ := statusWord_collision_recursion_rate hp a ha hg hg' hc hc' hbc hpoly n T hT
  exact ⟨C,hC,H⟩

private theorem markedSlopeLaw_sum {ι : Type*} [Fintype ι] {p : ℕ} (hp : 0 < p)
    (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g : ℝ) (η : ℕ → ℝ)
    (A : (Fin d → UnitAddCircle) → (Fin n → Fin p) → Bool)
    (ξ : ι → (Fin d → UnitAddCircle) → Measure ℝ) (u : Fin d → UnitAddCircle) :
    (∑ t, markedSlopeLaw hp d a n g η A (ξ t) u) =
      markedSlopeLaw hp d a n g η A (fun w => ∑ t, ξ t w) u := by
  unfold markedSlopeLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : A u i = true
  · simp only [hi,if_true,← Finset.smul_sum]
    congr 1
    let f (x : ℝ) := truncatedSlope d (fun k => (a k:ℝ)) p g (centralLift u) η (extendWord hp i) n+g^n*x
    have hf : Measurable f := measurable_const.add (measurable_const.mul measurable_id)
    rw [← Measure.sum_fintype,← Measure.sum_fintype,Measure.map_sum hf.aemeasurable]
  · simp [hi]

private theorem markedSlopeLaw_partition {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ)
    {g : ℝ} (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (η : ℕ → ℝ) (u : Fin d → UnitAddCircle) :
    let ξ := fun w => baseSlopeLaw hp d a (centralLift w) (fun l => η (n+l)) g
    (∑ s, markedSlopeLaw hp d a n g η (acceptsStatus hp d a n g c T η s) ξ u) =
      baseSlopeLaw hp d a (centralLift u) η g := by
  intro ξ
  let F (x : ℝ) := codedSlope d (fun k => (a k:ℝ)) p g (centralLift u) η (uniformCode p hp x)
  have hF : Measurable F := measurable_coded_sample hp d a (fun _ : ℝ => centralLift u) (fun _ => measurable_const) id measurable_id η g
  change _ = unitLaw.map F
  rw [← prefixLaw_sum hp n hF]
  unfold markedSlopeLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [show prefixLaw hp n F i = _ from prefixLaw_torus_child hp d a n u i η hg hg']
  by_cases hi : T < (prefixDegree hp d a n g c η u i:ℝ) <;> simp [acceptsStatus,hi,ξ]

private theorem boolWord_sum_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (F : List Bool → M) :
    (∑ v : Fin (k+1) → Bool, F (List.ofFn v)) = ∑ b, ∑ t : Fin k → Bool, F (b::List.ofFn t) := by
  let E := Fin.consEquiv (fun _ : Fin (k+1) => Bool)
  rw [← E.sum_comp (fun v => F (List.ofFn v)),Fintype.sum_prod_type]
  change (∑ b, ∑ t : Fin k → Bool, F (List.ofFn (Fin.cons b t))) = _
  simp only [List.ofFn_cons]

/-- The actual status laws partition the full conditional slope distribution
at each central torus state, for every finite horizon and every phase string. -/
theorem statusSlopeLaw_sum {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (k : ℕ) (η : ℕ → ℝ) (u : Fin d → UnitAddCircle) :
    (∑ v : Fin k → Bool, statusSlopeLaw hp d a n g c T (List.ofFn v) η u) =
      baseSlopeLaw hp d a (centralLift u) η g := by
  induction k generalizing η u with
  | zero => simp [statusSlopeLaw]
  | succ k ih =>
    rw [boolWord_sum_succ k (fun v => statusSlopeLaw hp d a n g c T v η u)]
    simp only [statusSlopeLaw,markedSlopeLaw_sum,ih]
    exact markedSlopeLaw_partition hp d a n hg hg' c T η u

/-- Haar-averaged mass carried by a fixed prescribed status word. -/
def statusMass {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) (g c T : ℝ)
    (v : List Bool) (η : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ u, statusSlopeLaw hp d a n g c T v η u univ

private theorem statusMass_cons {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (v : List Bool) (η : ℕ → ℝ) :
    (∑ s, statusMass hp (d+1) a n g c T (s::v) η) =
      statusMass hp (d+1) a n g c T v (fun l => η (n+l)) := by
  let ξ := statusSlopeLaw hp (d+1) a n g c T v (fun l => η (n+l))
  have hξ : Measurable (fun u => ξ u univ) := (Measure.measurable_coe MeasurableSet.univ).comp (measurable_statusSlopeLaw hp (d+1) a n hg hg' c T v (fun l => η (n+l)))
  have hM (s : Bool) : Measurable (fun u => statusSlopeLaw hp (d+1) a n g c T (s::v) η u univ) := (Measure.measurable_coe MeasurableSet.univ).comp (measurable_statusSlopeLaw hp (d+1) a n hg hg' c T (s::v) η)
  unfold statusMass
  change _ = ∫⁻ u, ξ u univ
  rw [← lintegral_finsetSum Finset.univ (fun s _ => hM s),← haar_blockEndMean hp d a ha n hξ]
  apply lintegral_congr_ae (.of_forall _)
  intro u
  rw [blockEndMean_prefix_sum,Finset.mul_sum]
  simp only [statusSlopeLaw,markedSlopeLaw,Measure.finsetSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun x : ℝ => truncatedSlope (d+1) (fun k => (a k:ℝ)) p g (centralLift u) η (extendWord hp i) n + g^n*x) :=
    measurable_const.add (measurable_const.mul measurable_id)
  by_cases hi : T < (prefixDegree hp (d+1) a n g c η u i:ℝ) <;>
    simp [acceptsStatus,hi,ξ,Measure.smul_apply,Measure.map_apply hm MeasurableSet.univ]

private theorem statusMass_sum_tail {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (s : Bool) (k : ℕ) (η : ℕ → ℝ) :
    (∑ v : Fin k → Bool, statusMass hp d a n g c T (s::List.ofFn v) η) =
      statusMass hp d a n g c T [s] η := by
  have hM (v : Fin k → Bool) : Measurable (fun u => statusSlopeLaw hp d a n g c T (s::List.ofFn v) η u univ) := (Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_statusSlopeLaw hp d a n hg hg' c T (s::List.ofFn v) η)
  unfold statusMass
  rw [← lintegral_finsetSum Finset.univ (fun v _ => hM v)]
  apply lintegral_congr_ae (.of_forall _)
  intro u
  rw [← Measure.finsetSum_apply]
  simp only [statusSlopeLaw,markedSlopeLaw_sum,statusSlopeLaw_sum hp d a n hg hg']

private def statusCount (v : List Bool) : ℝ≥0∞ :=
  (v.map (fun s => if s = true then (1:ℝ≥0∞) else 0)).sum

private theorem statusCount_ofFn {k : ℕ} (v : Fin k → Bool) :
    statusCount (List.ofFn v) = (Finset.univ.filter (fun i => v i = true)).card := by
  unfold statusCount
  rw [List.map_ofFn,List.sum_ofFn]
  exact Finset.sum_boole _ _

private theorem average_statusCount {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) {e : ℝ≥0∞}
    (hbad : ∀ η, statusMass hp (d+1) a n g c T [true] η ≤ e) (k : ℕ) (η : ℕ → ℝ) :
    (∑ v : Fin k → Bool, statusCount (List.ofFn v) * statusMass hp (d+1) a n g c T (List.ofFn v) η) ≤ k*e := by
  let M := statusMass hp (d+1) a n g c T
  change (∑ v : Fin k → Bool, statusCount (List.ofFn v)*M (List.ofFn v) η) ≤ _
  induction k generalizing η with
  | zero => simp [statusCount]
  | succ k ih =>
    rw [boolWord_sum_succ k (fun v => statusCount v*M v η)]
    have he (s : Bool) (v : List Bool) :
        statusCount (s::v)*M (s::v) η =
          (if s = true then M (s::v) η else 0)+statusCount v*M (s::v) η := by
      cases s <;> simp [statusCount,add_mul]
    simp_rw [he]
    simp only [Finset.sum_add_distrib]
    have h₁ : (∑ s : Bool, ∑ v : Fin k → Bool, if s = true then M (s::List.ofFn v) η else 0) = M [true] η := by
      simpa [M] using statusMass_sum_tail hp (d+1) a n hg hg' c T true k η
    rw [h₁,Finset.sum_comm]
    have h₂ (v : Fin k → Bool) : (∑ s, statusCount (List.ofFn v)*M (s::List.ofFn v) η) =
        statusCount (List.ofFn v)*M (List.ofFn v) (fun l => η (n+l)) := by
      rw [← Finset.mul_sum,statusMass_cons hp a ha n hg hg' c T]
    simp_rw [h₂]
    exact (add_le_add (hbad η) (ih _)).trans_eq (by simp [add_mul,add_comm])

/-- The true conditional status laws lose at most the Markov bound on
discarding every word with more than `m` bad blocks. This holds for arbitrary
phase shifts and requires only the single-block bad mass under Haar. -/
theorem statusMass_discard {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) {e : ℝ≥0∞}
    (hbad : ∀ η, statusMass hp (d+1) a n g c T [true] η ≤ e) (k m : ℕ) (η : ℕ → ℝ) :
    (∑ v ∈ (sparseStatusWords k m)ᶜ, statusMass hp (d+1) a n g c T (List.ofFn v) η) ≤ k*e/(m+1:ℕ) := by
  let M := statusMass hp (d+1) a n g c T
  have hn : ((m+1:ℕ):ℝ≥0∞) ≠ 0 := by positivity
  apply (ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl (by finiteness))).mpr
  rw [Finset.sum_mul]
  apply le_trans _ (average_statusCount hp a ha n hg hg' c T hbad k η)
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (s := (sparseStatusWords k m)ᶜ)
    (f := fun v : Fin k → Bool => statusCount (List.ofFn v)*M (List.ofFn v) η)
    (Finset.subset_univ _) (fun _ _ _ => bot_le))
  apply Finset.sum_le_sum
  intro v hv
  have hnum : m < (Finset.univ.filter (fun i => v i = true)).card := by
    simpa [sparseStatusWords] using hv
  rw [mul_comm,statusCount_ofFn]
  apply mul_le_mul_left _ (M (List.ofFn v) η)
  exact_mod_cast Nat.succ_le_of_lt hnum

private theorem phased_word_energy {X : Type*} (shift : X → X) (E : X → List Bool → ℝ≥0∞) (A : Bool → ℝ)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hA : ∀ s, 1 ≤ A s) (hbase : ∀ x, E x [] ≤ ENNReal.ofReal C)
    (hstep : ∀ x s v, E x (s::v) ≤ ENNReal.ofReal (C*q^(v.length+1)) +
      ENNReal.ofReal (q*A s)*E (shift x) v) (x : X) (v : List Bool) :
    E x v ≤ ENNReal.ofReal (C*(v.length+1:ℝ)*(v.map A).prod*q^v.length) := by
  have hprod (v : List Bool) : 1 ≤ (v.map A).prod := by
    induction v with
    | nil => simp
    | cons s v ih => simpa using one_le_mul_of_one_le_of_one_le (hA s) ih
  induction v generalizing x with
  | nil => simpa using hbase x
  | cons s v ih =>
    have ha := zero_le_one.trans (hA s)
    have hv := zero_le_one.trans (hprod v)
    apply (hstep x s v).trans (add_le_add_right (mul_le_mul_right (ih (shift x)) _) _ |>.trans _)
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q*A s),← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.map_cons,List.prod_cons,pow_succ]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprod (s::v)) hC) (pow_nonneg hq.le (v.length+1))
    simp only [List.map_cons,List.prod_cons,pow_succ] at h
    linarith only [h]

private theorem collision_subprobability (μ : Measure ℝ) (hμ : μ univ ≤ 1) (r : ℝ) :
    ENNReal.ofReal (collision μ μ r) ≤ 1 := by
  have hi : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  have hh : (μ.prod μ) (PrefixEnergy.band r) ≤ (μ.prod μ) univ := measure_mono (subset_univ _)
  change ENNReal.ofReal ((μ.prod μ) (PrefixEnergy.band r)).toReal ≤ 1
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [← Set.univ_prod_univ,Measure.prod_prod] at hh
  exact hh.trans (mul_le_one₀ hμ bot_le hμ)

/-- Iteration of the actual prescribed-word energy at geometric radii, with
arbitrary nonstationary phases. The contraction and both row-degree costs
appear explicitly. -/
theorem statusWord_collision_iteration_rate {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (R : ℝ) (hR : 0 < R) (A : Bool → ℝ) (hA : ∀ s, 1 ≤ A s)
    (hD : ∀ s, 3*(if s = true then (p:ℝ)^n else T)*(p:ℝ)⁻¹^n ≤ g^n*A s) :
    ∃ K : ℝ, 0 < K ∧ K = max 1 (slopeSliceBound g c n*R) ∧ ∀ (η : ℕ → ℝ) (v : List Bool),
      (∫⁻ u, let μ := statusSlopeLaw hp (d+1) a n g c T v η u
        ENNReal.ofReal (collision μ μ (R*(g^n)^v.length))) ≤
        ENNReal.ofReal (K*(v.length+1:ℝ)*(v.map A).prod*(g^n)^v.length) := by
  obtain ⟨C,hC,hEq,hstep⟩ := statusWord_collision_recursion_rate hp a ha hg hg' hc hc' hbc hpoly n T hT
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  let K := max 1 (C*R)
  let q := g^n
  let E (η : ℕ → ℝ) (v : List Bool) := ∫⁻ u, let μ := statusSlopeLaw hp (d+1) a n g c T v η u
    ENNReal.ofReal (collision μ μ (R*q^v.length))
  have hK : 1 ≤ K := le_max_left _ _
  have hK' : C*R ≤ K := le_max_right _ _
  have hq : 0 < q := pow_pos hg _
  refine ⟨K,zero_lt_one.trans_le hK,by rw [←hEq],?_⟩
  apply phased_word_energy (fun η l => η (n+l)) E A (zero_le_one.trans hK) hq hA
  · intro η
    have hpnt (u : Fin (d+1) → UnitAddCircle) := collision_subprobability (baseSlopeLaw hp (d+1) a (centralLift u) η g)
      (baseSlopeLaw_univ hp (d+1) a (centralLift u) η g).le (R*q^(0:ℕ))
    exact (lintegral_mono hpnt).trans (by simpa using ENNReal.ofReal_le_ofReal hK)
  · intro η s v
    have h := hstep η s v (R*q^(v.length+1)) (by positivity)
    have he : R*q^(v.length+1)/g^n = R*q^v.length := by rw [pow_succ,← mul_assoc,mul_div_cancel_right₀ _ hq.ne']
    simp only [he] at h
    apply h.trans (add_le_add _ (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hD s)) _))
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hK' (pow_nonneg hq.le _)

theorem statusWord_collision_iteration {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0 < g) (hg' : g < 1) (hc : 0 < c) (hc' : c < 1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (R : ℝ) (hR : 0 < R) (A : Bool → ℝ) (hA : ∀ s, 1 ≤ A s)
    (hD : ∀ s, 3*(if s = true then (p:ℝ)^n else T)*(p:ℝ)⁻¹^n ≤ g^n*A s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : ℕ → ℝ) (v : List Bool),
      (∫⁻ u, let μ := statusSlopeLaw hp (d+1) a n g c T v η u
        ENNReal.ofReal (collision μ μ (R*(g^n)^v.length))) ≤
        ENNReal.ofReal (K*(v.length+1:ℝ)*(v.map A).prod*(g^n)^v.length) := by
  obtain ⟨C,hC,_,H⟩ := statusWord_collision_iteration_rate hp a ha hg hg' hc hc' hbc hpoly n T hT R hR A hA hD
  exact ⟨C,hC,H⟩

/-- The mass of a single bad block is the probability of the actual
crowding test evaluated on an independent digit stream at a Haar state. -/
theorem statusMass_single_bad {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ)
    (g c T : ℝ) (η : ℕ → ℝ) :
    statusMass hp d a n g c T [true] η =
      ((volume : Measure (Fin d → UnitAddCircle)).prod unitLaw)
        {z | T < (prefixDegree hp d a n g c η z.1 (digitPrefix hp n z.2):ℝ)} := by
  let A := acceptsStatus hp d a n g c T η true
  let Ω := Fin d → UnitAddCircle
  let B := {z : Ω × ℝ | A z.1 (digitPrefix hp n z.2) = true}
  have hB : MeasurableSet B := by
    have he : B = ⋃ i : Fin n → Fin p, {u : Ω | A u i = true} ×ˢ {x | digitPrefix hp n x = i} := by
      ext z
      simp [B,eq_comm (a := digitPrefix hp n _)]
    rw [he]
    exact MeasurableSet.iUnion (fun i => (measurable_acceptsStatus hp d a n g c T η true i).prod
      ((measurable_digitPrefix hp n) (measurableSet_singleton i)))
  have he : {z : Ω × ℝ | T < (prefixDegree hp d a n g c η z.1 (digitPrefix hp n z.2):ℝ)} = B := by
    ext z
    simp [A,B,acceptsStatus]
  rw [he,Measure.prod_apply hB]
  apply lintegral_congr_ae (.of_forall _)
  intro u
  have hs : MeasurableSet (Prod.mk u ⁻¹' B) := measurable_prodMk_left hB
  rw [← show (∫⁻ x, (if A u (digitPrefix hp n x) = true then (1:ℝ≥0∞) else 0) ∂unitLaw) =
        unitLaw (Prod.mk u ⁻¹' B) from by
    rw [← lintegral_indicator_one (μ := unitLaw) hs]
    apply lintegral_congr_ae (.of_forall _)
    intro x
    by_cases h : A u (digitPrefix hp n x) = true
    · rw [if_pos h,Set.indicator_of_mem (show x ∈ Prod.mk u ⁻¹' B from h)];rfl
    · rw [if_neg h,Set.indicator_of_notMem (show x ∉ Prod.mk u ⁻¹' B from h)]]
  rw [lintegral_digitPrefix hp n (fun i => if A u i = true then (1:ℝ≥0∞) else 0),Finset.mul_sum]
  simp only [statusSlopeLaw,markedSlopeLaw,Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun x : ℝ => truncatedSlope d (fun k => (a k:ℝ)) p g (centralLift u) η (extendWord hp i) n + g^n*x) :=
    measurable_const.add (measurable_const.mul measurable_id)
  by_cases hi : A u i = true <;> simp [A] at hi ⊢ <;> simp [hi,Measure.map_apply hm MeasurableSet.univ,baseSlopeLaw_univ]

/-- At any derivative index, a bad original block forces a heavy ball in
the true next-derivative slope family, at the dilated natural scale. -/
theorem statusMass_bad_le_derivative {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n : ℕ)
    (g c T : ℝ) (hh : 0 ≤ g*c) (hh' : g*c < 1) (hT : 0 ≤ T) (η : ℕ → ℝ) :
    statusMass hp d a n g c T [true] η ≤ ((volume : Measure (Fin d → UnitAddCircle)).prod unitLaw)
      {z | let h := g*c
        let θ := fun k => η k+Real.pi/2
        let y := codedSlope d (fun j => (a j:ℝ)) p h (centralLift z.1) θ (uniformCode p hp z.2)
        let R := (4*(1-h)⁻¹+1)*h^n
        ENNReal.ofReal (T*(p:ℝ)⁻¹^n) < baseSlopeLaw hp d a (centralLift z.1) θ h (Icc (y-R) (y+R))} := by
  rw [statusMass_single_bad]
  apply measure_mono
  intro z hz
  let h := g*c
  let θ := fun k => η k+Real.pi/2
  let w := centralLift z.1
  let x := z.2
  let D := 2*(1-h)⁻¹+1
  let N := slopeNeighbors hp d (fun k => (a k:ℝ)) p h w θ (uniformCode p hp x) n D
  have hcode := truncatedSlope_congr d (fun k => (a k:ℝ)) p h w θ
    (extendWord hp (digitPrefix hp n x)) (uniformCode p hp x) n (fun i hi => by simp [extendWord,digitPrefix,hi])
  have hdeg : prefixDegree hp d a n g c η z.1 (digitPrefix hp n x) = N.card := by
    dsimp only [prefixDegree,N,slopeNeighbors]
    congr 1
    apply Finset.filter_congr
    intro i _
    change (¬ D*h^n < |truncatedSlope d (fun k => (a k:ℝ)) p h w θ (extendWord hp (digitPrefix hp n x)) n -
      truncatedSlope d (fun k => (a k:ℝ)) p h w θ (extendWord hp i) n|) ↔ _
    rw [not_lt,hcode]
  have hz' : T < (N.card:ℝ) := by rw [← hdeg]; exact hz
  have hs : 0 < (p:ℝ)⁻¹^n := by positivity
  have ht := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hT hs.le) |>.2 (mul_lt_mul_of_pos_right hz' hs)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] at ht
  have hmass := slopeNeighbor_mass_le hp d (fun k => (a k:ℝ)) p 1 (g := h) hh hh' w θ 0 x n D
  have hR : D+2*(1-h)⁻¹ = 4*(1-h)⁻¹+1 := by dsimp [D]; ring
  apply ht.trans_le
  let Y (y : ℝ) := codedSlope d (fun k => (a k:ℝ)) p h w θ (uniformCode p hp y)
  have hY : sampledSlope hp d (fun k => (a k:ℝ)) p 1 h w θ 0 = Y := by
    funext y
    simp [sampledSlope,Y]
  simp only [sampledLaw,hY,zero_mul,add_zero,hR] at hmass
  exact hmass

/-- The retained slope law after discarding every status word with more
than `m` bad stages out of the first `k`. -/
@[expose] def retainedStatusLaw {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n k m : ℕ) (g c T : ℝ)
    (η : ℕ → ℝ) (u : Fin d → UnitAddCircle) : Measure ℝ :=
  ∑ v ∈ sparseStatusWords k m, statusSlopeLaw hp d a n g c T (List.ofFn v) η u

theorem retainedStatusLaw_domination {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (n k m : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) (η : ℕ → ℝ) (u : Fin d → UnitAddCircle) :
    retainedStatusLaw hp d a n k m g c T η u ≤ baseSlopeLaw hp d a (centralLift u) η g := by
  rw [← statusSlopeLaw_sum hp d a n hg hg' c T k η u]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bot_le)

theorem retainedStatusLaw_discard {p d : ℕ} (hp : 0 < p) (a : ℕ → ℤ) (ha : a d ≠ 0) (n : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hg' : g < 1) (c T : ℝ) {e : ℝ≥0∞}
    (hbad : ∀ η, statusMass hp (d+1) a n g c T [true] η ≤ e) (k m : ℕ) (η : ℕ → ℝ) :
    (∫⁻ u, 1-retainedStatusLaw hp (d+1) a n k m g c T η u univ) ≤ k*e/(m+1:ℕ) := by
  let Ω := Fin (d+1) → UnitAddCircle
  let W (v : Fin k → Bool) (u : Ω) := statusSlopeLaw hp (d+1) a n g c T (List.ofFn v) η u
  have hm (v : Fin k → Bool) : Measurable (fun u => W v u univ) := (Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_statusSlopeLaw hp (d+1) a n hg hg' c T (List.ofFn v) η)
  have he (u : Ω) : 1-retainedStatusLaw hp (d+1) a n k m g c T η u univ =
       ∑ v ∈ (sparseStatusWords k m)ᶜ, W v u univ := by
    have h := congrArg (fun μ : Measure ℝ => μ univ) (statusSlopeLaw_sum hp (d+1) a n hg hg' c T k η u)
    simp only [Measure.finsetSum_apply,baseSlopeLaw_univ] at h
    unfold retainedStatusLaw
    rw [Measure.finsetSum_apply,← h,← Finset.sum_add_sum_compl (sparseStatusWords k m)]
    apply ENNReal.add_sub_cancel_left
    apply ne_of_lt
    simpa only [retainedStatusLaw,Measure.finsetSum_apply] using (retainedStatusLaw_domination hp (d+1) a n k m hg hg' c T η u univ).trans_lt (measure_lt_top _ _)
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun v _ => hm v)]
  exact statusMass_discard hp a ha n hg hg' c T hbad k m η

end Weierstrass.Predecessor
