module

public import Weierstrass.FullBall
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Averaging Lemma 5.2 with a different retained law for each parameter and
scale. All expectations in this statement are over the same environment w. -/
public noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Weierstrass

abbrev heavyMass (ν : Measure ℝ) (R τ : ℝ) : ℝ :=
  ν.real {x : ℝ | τ < ν.real (Icc (x-R) (x+R))}

abbrev collision (η : Measure ℝ) (R : ℝ) : ℝ :=
  (η.prod η).real {p : ℝ × ℝ | |p.1-p.2| ≤ R}

/-- Vanishing discarded mass and collision mass small compared to the tested
threshold imply the full-law information bound, for any filter of scales. -/
theorem heavyMass_tendsto_zero {ι Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω)
    [IsProbabilityMeasure m] (l : Filter ι) (ν η : ι → Ω → Measure ℝ)
    (hν : ∀ i w, IsProbabilityMeasure (ν i w)) (hην : ∀ i w, η i w ≤ ν i w)
    (R τ : ι → ℝ) (hR : ∀ i, 0 < R i) (hτ : ∀ i, 0 < τ i)
    (hmeasH : ∀ i, Integrable (fun w => heavyMass (ν i w) (R i) (τ i)) m)
    (hmeasD : ∀ i, Integrable (fun w => 1 - (η i w).real univ) m)
    (hmeasC : ∀ i, Integrable (fun w => collision (η i w) (R i) / τ i) m)
    (discard : Tendsto (fun i => ∫ w, 1 - (η i w).real univ ∂m) l (𝓝 0))
    (small : Tendsto (fun i => ∫ w, collision (η i w) (R i) / τ i ∂m) l (𝓝 0)) :
    Tendsto (fun i => ∫ w, heavyMass (ν i w) (R i) (τ i) ∂m) l (𝓝 0) := by
  have estimate (i : ι) (M : ℝ) (hM : 1 < M) :
      (∫ w, heavyMass (ν i w) (R i) (τ i) ∂m) ≤
        (∫ w, 1 - (η i w).real univ ∂m) + 3/M +
          M * ∫ w, collision (η i w) (R i) / τ i ∂m := by
    have hi := ((hmeasD i).add (integrable_const (3/M))).add ((hmeasC i).const_mul M)
    have hle (w : Ω) : heavyMass (ν i w) (R i) (τ i) ≤
        (1 - (η i w).real univ + 3/M) + M * (collision (η i w) (R i) / τ i) := by
      have := hν i w
      have h := fullBallFromRetainedCollisions _ _ (hην i w) (hR i) (hτ i) hM
      apply h.trans_eq
      unfold collision
      ring
    have h := integral_mono (hmeasH i) hi hle
    apply h.trans_eq
    simp only [Pi.add_apply]
    rw [integral_add (f := fun w => (1 - (η i w).real univ) + 3/M)
        (g := fun w => M * (collision (η i w) (R i) / τ i))
        ((hmeasD i).add (integrable_const _)) ((hmeasC i).const_mul M),
      integral_add (f := fun w => 1 - (η i w).real univ) (g := fun _ => 3/M)
        (hmeasD i) (integrable_const _), integral_const_mul, integral_const]
    simp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le (integral_nonneg fun _ => measureReal_nonneg)
  · intro e he
    let M := 2 + 6 / e
    have hM : 1 < M := by dsimp [M]; linarith [div_pos (by norm_num : (0:ℝ) < 6) he]
    have hcoef : 3/M < e := by
      apply (div_lt_iff₀ (zero_lt_one.trans hM)).mpr
      dsimp [M]
      rw [mul_add, mul_div_cancel₀ _ he.ne']
      linarith
    have ht : Tendsto (fun i => (∫ w, 1 - (η i w).real univ ∂m) + 3/M +
        M * ∫ w, collision (η i w) (R i) / τ i ∂m) l (𝓝 (3/M)) := by
      simpa using (discard.add_const (3/M)).add (small.const_mul M)
    filter_upwards [ht.eventually_lt_const hcoef] with i hi
    exact (estimate i M hM).trans_lt hi

end Weierstrass
