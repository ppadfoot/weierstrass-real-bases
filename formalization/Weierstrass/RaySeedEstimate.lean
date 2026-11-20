module

public import Weierstrass.RaySeedPhysical

/-! The small-derivative estimate (H5) for the transverse difference, uniform
over every phase string and all bounded weights with a fixed finite-window
nondegeneracy. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

abbrev Profile := (ℤ → Icc (-1:ℝ) 1) × (ℤ → Icc (-1:ℝ) 1) × PhaseTorus
def admissible (D : ℕ) (δ : ℝ) : Set Profile :=
  {x | ∀ n : ℕ, ∃ k : Fin D, δ ≤ |(x.1 (n+k.val:ℕ):ℝ)*(x.2.1 (n+k.val:ℕ):ℝ)|}

private theorem closed_admissible (D : ℕ) (δ : ℝ) : IsClosed (admissible D δ) := by
  have eq : admissible D δ = ⋂ n : ℕ, ⋃ k : Fin D,
      {x : Profile | δ ≤ |(x.1 (n+k.val:ℕ):ℝ)*(x.2.1 (n+k.val:ℕ):ℝ)|} := by
    ext x
    simp [admissible]
  rw [eq]
  apply isClosed_iInter
  intro n
  apply isClosed_iUnion_of_finite
  intro k
  exact isClosed_le continuous_const
    (((continuous_subtype_val.comp ((continuous_apply _).comp continuous_fst)).mul
      (continuous_subtype_val.comp ((continuous_apply _).comp (continuous_fst.comp continuous_snd)))).abs)

private theorem profile_bound (f : ℤ → Icc (-1:ℝ) 1) (j : ℤ) : |(f j:ℝ)| ≤ 1 :=
  abs_le.mpr (f j).property

/-- All three suprema in (H5) are included: weights, rays via their
projections, and translates of Haar by arbitrary phase strings.
The real factor u_j is the product of the original weight and the
physical-ray projection. The derivative is encoded by its two Fourier signs. -/
theorem uniform_transverse_derivative {B : ℂ} (hb : 1 < ‖B‖) {q ρ s δ : ℝ}
    (hq : 1 < q) (hρ : 0 < ρ) (hρ' : ρ < 1) (hQ : q*ρ < 1)
    (hbQ : 1 < (q*ρ)*‖B‖) (hs : s ≠ 0) (hδ : 0 < δ) (D : ℕ)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    [μ.InnerRegularCompactLTTop] {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ admissible D δ,
      μ.real {z | ‖symmetricSeries (derivativeCoeff q ρ s (fun j ↦ (x.1 j:ℝ))
        (fun j ↦ (x.2.1 j:ℝ)) x.2.2) z.val‖ ≤ r n} < ε := by
  let X := admissible D δ
  have : CompactSpace X := isCompact_iff_compactSpace.mp (closed_admissible D δ).isCompact
  let a (x : X) := derivativeCoeff q ρ s (fun j ↦ (x.val.1 j:ℝ))
    (fun j ↦ (x.val.2.1 j:ℝ)) x.val.2.2
  have cw (j : ℤ) : Continuous (fun x : X ↦ a x j) := by
    unfold a derivativeCoeff coord circleJump turn
    fun_prop
  let W := physicalEnvelope q ρ s
  have sw : Summable W := summable_physicalEnvelope hq hρ hQ s
  have ew x j : ‖a x j‖ ≤ W j := by
    have b := physical_bounds (zero_lt_one.trans hq) hρ s (profile_bound x.val.1)
        (profile_bound x.val.2.1) x.val.2.2 j
    by_cases hj : 0 ≤ j
    · simpa only [W,physicalEnvelope,if_pos hj] using b.1
    · simpa only [W,physicalEnvelope,if_neg hj] using b.2
  have C := symmetricSeries_continuous a cw sw ew
  let F (x : X) (z : complexPhaseGroup B) := symmetricSeries (a x) z.val
  have nul x : μ {z | F x z = 0} = 0 := by
    have gf : ∃ᶠ n : ℕ in atTop, δ ≤ |(x.val.1 n:ℝ)*(x.val.2.1 n:ℝ)| := by
      rw [frequently_atTop]
      intro N
      obtain ⟨k,hk⟩ := x.property N
      exact ⟨N+k.val,by omega,hk⟩
    have M (j : ℤ) := (physical_bounds (zero_lt_one.trans hq) hρ s (profile_bound x.val.1)
        (profile_bound x.val.2.1) x.val.2.2 j).1
    apply null_level_of_frequent hb (mul_pos (zero_lt_one.trans hq) hρ) hQ hbQ
        (show 0 < 4*Real.pi*|s| *δ by positivity) (a x)
        (sw.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (ew x)) M _ μ 0
    exact derivative_frequent (zero_lt_one.trans hq) hρ hρ' (profile_bound x.val.2.1) x.val.2.2 gf
  have lim := uniform_shrinking_level μ F (fun x ↦ (C.comp ((continuous_const (y:=x)).prodMk
    continuous_subtype_val)).measurable) (fun z ↦ C.comp (continuous_id.prodMk (continuous_const (y:=z.val))))
    nul hr he
  filter_upwards [lim] with n hn
  intro x hx
  exact hn ⟨x,hx⟩

end Weierstrass.RaySeed
