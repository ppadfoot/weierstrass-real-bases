module

public import Weierstrass.PhaseDensity
public import Weierstrass.SparseGap
public import Weierstrass.MomentConvergence
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The conjugate and reciprocal phase groups in §2, weighted physical rays,
the critical linearization (RC4) in §4, and transverse differentiation in §6.
The real sequences `d` and `e` are the projections of the physical and
transverse unit directions. Using only their absolute bounds includes the real
and the complex embeddings. All phases here are in turns. -/

@[expose] public noncomputable section

open scoped BigOperators
namespace Weierstrass

/-- The full physical orbit, including all directions when the multiplier is nonreal.
At a real multiplier taking the real part gives the ordinary real orbit. -/
def complexPhaseOrbit (B : ℂ) : ℂ →+ PhaseTorus where
  toFun x j := ↑((B ^ j * x).re)
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp [mul_add]

def complexPhaseGroup (B : ℂ) : AddSubgroup PhaseTorus := (complexPhaseOrbit B).range.topologicalClosure

instance complexPhaseGroupCompact (B : ℂ) : CompactSpace (complexPhaseGroup B) :=
  isCompact_iff_compactSpace.mp (complexPhaseOrbit B).range.isClosed_topologicalClosure.isCompact

theorem complexPhaseGroup_ofReal (b : ℝ) : complexPhaseGroup (b : ℂ) = phaseGroup b := by
  unfold complexPhaseGroup phaseGroup
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.re, by ext j; simp [phaseOrbit, complexPhaseOrbit, ← Complex.ofReal_zpow]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x : ℂ), by ext j; simp [phaseOrbit, complexPhaseOrbit, ← Complex.ofReal_zpow]⟩

private def frequency (B : ℂ) (S : Finset ℤ) (n : S → ℤ) : ℂ :=
  ∑ j : S, (n j : ℂ) * B ^ (j : ℤ)

private theorem orbit_character (B x : ℂ) (S : Finset ℤ) (n : S → ℤ) :
    UnitAddTorus.mFourier n (fun j : S ↦ complexPhaseOrbit B x j) =
      (AddCircle.toCircle (↑((frequency B S n * x).re) : AddCircle (1 : ℝ)) : ℂ) := by
  rw [mFourier_eq_sum_toCircle]
  let q : ℂ →+ AddCircle (1 : ℝ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp Complex.reAddGroupHom
  have ha : (∑ j : S, n j • q (B ^ (j : ℤ) * x)) = q (frequency B S n * x) := by
    simp only [frequency, Finset.sum_mul, map_sum, ← map_zsmul, zsmul_eq_mul, mul_assoc]
  exact congrArg (fun a : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle a : ℂ)) ha

private theorem half_turn_ne_one :
    (AddCircle.toCircle (↑(1/2 : ℝ) : AddCircle (1 : ℝ)) : ℂ) ≠ 1 := by
  intro h
  have hzero : (↑(1/2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa using h
  have hx := (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (show (1/2 : ℝ) ∈ Set.Ico 0 1 by constructor <;> norm_num)).mp hzero
  norm_num at hx

/-- Compact physical groups contain the transverse orbit of any other complex
embedding of the same field element. No single-ray density assumption is used. -/
theorem conjugate_orbit_mem_phaseGroup {K : Type*} [Field K] (σ τ : K →+* ℂ)
    (a : K) (u : ℂ) : complexPhaseOrbit (τ a) u ∈ complexPhaseGroup (σ a) := by
  classical
  let H := complexPhaseGroup (σ a)
  let y := complexPhaseOrbit (τ a) u
  let _ : MeasurableSpace H := borel _
  let _ : BorelSpace H := ⟨rfl⟩
  let μ := MeasureTheory.Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)
  let _ : MeasureTheory.IsProbabilityMeasure μ := ⟨by
    simpa [μ] using MeasureTheory.Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))⟩
  have finiteMem (S : Finset ℤ) : ∃ w : H, ∀ j : S, w.val j = y j := by
    let p : H →+ UnitAddTorus S :=
      { toFun := fun w j ↦ w.val j, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    have hp : Continuous p := continuous_pi (fun j ↦ (continuous_apply (j : ℤ)).comp continuous_subtype_val)
    obtain ⟨w, hw⟩ : (fun j : S ↦ y j) ∈ Set.range p := by
      apply mem_torus_image_of_characters μ p hp
      intro n hn
      let α := ∑ j : S, (n j : K) * a ^ (j : ℤ)
      have hfreq (f : K →+* ℂ) : f α = frequency (f a) S n := by simp [α, frequency]
      have hfτ : frequency (τ a) S n ≠ 0 := by
        intro hz
        apply hn
        rw [show (fun j : S ↦ y j) = (fun j : S ↦ complexPhaseOrbit (τ a) u j) from rfl,
          orbit_character, hz]
        simp
      have hα : α ≠ 0 := by intro h; apply hfτ; rw [← hfreq, h, map_zero]
      have hfσ : frequency (σ a) S n ≠ 0 := by simpa [← hfreq] using σ.injective.ne hα
      let x : ℂ := (1/2 : ℂ) / frequency (σ a) S n
      let w : H := ⟨complexPhaseOrbit (σ a) x, (complexPhaseOrbit (σ a)).range.le_topologicalClosure ⟨x, rfl⟩⟩
      refine ⟨w, ?_⟩
      change UnitAddTorus.mFourier n (fun j : S ↦ complexPhaseOrbit (σ a) x j) ≠ 1
      rw [orbit_character, show frequency (σ a) S n * x = 1/2 by dsimp [x]; field_simp]
      simpa using half_turn_ne_one
    exact ⟨w, congrFun hw⟩
  change y ∈ H
  by_contra hy
  have hclosed : IsClosed (H : Set PhaseTorus) := (complexPhaseOrbit (σ a)).range.isClosed_topologicalClosure
  obtain ⟨S, U, hU, hsub⟩ := isOpen_pi_iff.mp hclosed.isOpen_compl y hy
  obtain ⟨w, hw⟩ := finiteMem S
  apply (hsub (a := w.val) ?_) w.property
  intro j hj
  have he := hw ⟨j, hj⟩
  change w.val j = y j at he
  rw [he]
  exact (hU j hj).2

/-- Equality of the full physical compact groups at conjugate embeddings. -/
theorem conjugate_phaseGroup_eq {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K) :
    complexPhaseGroup (σ a) = complexPhaseGroup (τ a) := by
  have mono (f g : K →+* ℂ) : complexPhaseGroup (f a) ≤ complexPhaseGroup (g a) := by
    refine AddSubgroup.topologicalClosure_minimal _ ?_ (complexPhaseOrbit (g a)).range.isClosed_topologicalClosure
    rintro _ ⟨u, rfl⟩
    exact conjugate_orbit_mem_phaseGroup g f a u
  exact le_antisymm (mono σ τ) (mono τ σ)

/-- Reversal of all bilateral phase coordinates. -/
def reversePhase : PhaseTorus →+ PhaseTorus where
  toFun z j := z (-j)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem reversePhase_orbit (B x : ℂ) :
    reversePhase (complexPhaseOrbit B x) = complexPhaseOrbit B⁻¹ x := by
  ext j
  simp [reversePhase, complexPhaseOrbit, zpow_neg]

theorem reversePhase_reversePhase (z : PhaseTorus) : reversePhase (reversePhase z) = z := by
  funext j
  simp [reversePhase]

/-- Reversal maps the whole physical group onto that of the inverse multiplier. -/
theorem reversePhase_group (B : ℂ) :
    (complexPhaseGroup B).map reversePhase = complexPhaseGroup B⁻¹ := by
  have hcont : Continuous reversePhase := continuous_pi (fun j : ℤ ↦ continuous_apply (-j))
  have hin (D : ℂ) : complexPhaseGroup D ≤ (complexPhaseGroup D⁻¹).comap reversePhase := by
    refine AddSubgroup.topologicalClosure_minimal _ ?_
      ((complexPhaseOrbit D⁻¹).range.isClosed_topologicalClosure.preimage hcont)
    rintro _ ⟨x, rfl⟩
    change reversePhase (complexPhaseOrbit D x) ∈ complexPhaseGroup D⁻¹
    rw [reversePhase_orbit]
    exact (complexPhaseOrbit D⁻¹).range.le_topologicalClosure ⟨x, rfl⟩
  apply le_antisymm ((AddSubgroup.map_le_iff_le_comap).mpr (hin B))
  intro z hz
  refine ⟨reversePhase z, ?_, reversePhase_reversePhase z⟩
  have hm := hin B⁻¹ hz
  change reversePhase z ∈ complexPhaseGroup B⁻¹⁻¹ at hm
  simpa using hm

/-- The reciprocal pair in §2 has precisely the reversal of the original phase group.
The sign or complex argument of the multiplier is preserved. -/
theorem reversePhase_group_conjugate {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K) :
    (complexPhaseGroup (σ a)).map reversePhase = complexPhaseGroup (τ a)⁻¹ := by
  rw [conjugate_phaseGroup_eq σ τ a, reversePhase_group]

/-- The signed projection of a complex unit direction at index j. -/
def rayProjection (D v : ℂ) (j : ℤ) : ℝ := (v * (D / (‖D‖ : ℂ)) ^ j).re

theorem abs_rayProjection_le {D v : ℂ} (hD : D ≠ 0) (hv : ‖v‖ = 1) (j : ℤ) :
    |rayProjection D v j| ≤ 1 := by
  refine (Complex.abs_re_le_norm _).trans_eq ?_
  simp [norm_zpow, hv, hD]

/-- The normalized projection gives the original physical frequency without loss. -/
theorem norm_zpow_mul_rayProjection {D : ℂ} (hD : D ≠ 0) (v : ℂ) (j : ℤ) :
    ‖D‖ ^ j * rayProjection D v j = (D ^ j * v).re := by
  have hnorm : (‖D‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hD)
  unfold rayProjection
  rw [← Complex.re_ofReal_mul, Complex.ofReal_zpow, div_zpow]
  congr 1
  field_simp

/-- The weighted bilateral summand on a fixed physical ray. -/
def rayTerm (b g : ℝ) (c d z : ℤ → ℝ) (x : ℝ) (j : ℤ) : ℝ :=
  g ^ j * c j * (Real.cos (2 * Real.pi * (z j + b ^ j * d j * x)) -
    Real.cos (2 * Real.pi * z j))

def rayIncrement (b g : ℝ) (c d z : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℤ, rayTerm b g c d z x j

theorem rayIncrement_ones (b g : ℝ) (z : ℤ → ℝ) (x : ℝ) :
    rayIncrement b g (fun _ ↦ 1) (fun _ ↦ 1) z x = bilateralIncrement b g z x := by
  simp [rayIncrement, bilateralIncrement, rayTerm, incrementTerm]

private def rayMajorant (b g x : ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j then 2 * g ^ j else (2 * Real.pi * |x|) * (b * g) ^ j

private theorem summable_rayMajorant {b g : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b * g) (x : ℝ) : Summable (rayMajorant b g x) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa [rayMajorant] using (summable_geometric_of_lt_one hg.le hg1).mul_left 2
  · have hq := summable_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hbg)).le
        (inv_lt_one_of_one_lt₀ hbg)
    have hs := hq.mul_left ((2 * Real.pi * |x|) * (b * g)⁻¹)
    apply hs.congr
    intro j
    rw [rayMajorant, if_neg (by omega), show -(↑j + 1 : ℤ) = -((j+1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow, pow_succ]
    ring

private theorem rayTerm_bound {b g : ℝ} (hb : 0 < b) (hg : 0 < g)
    {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (z : ℤ → ℝ) (x : ℝ) (j : ℤ) : ‖rayTerm b g c d z x j‖ ≤ rayMajorant b g x j := by
  let A := 2 * Real.pi * (z j + b ^ j * d j * x)
  let B := 2 * Real.pi * z j
  have hw : |g ^ j * c j| ≤ g ^ j := by
    rw [abs_mul, abs_of_pos (zpow_pos hg _)]
    exact mul_le_of_le_one_right (zpow_pos hg _).le (hc _)
  change |(g ^ j * c j) * (Real.cos A - Real.cos B)| ≤ _
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans
  by_cases hj : 0 ≤ j
  · rw [rayMajorant, if_pos hj, mul_comm 2]
    apply mul_le_mul_of_nonneg_left _ (zpow_pos hg _).le
    exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one A, Real.abs_cos_le_one B])
  · rw [rayMajorant, if_neg hj]
    have hdiff : A - B = 2 * Real.pi * b ^ j * d j * x := by dsimp [A, B]; ring
    have hcos := Real.abs_cos_sub_cos_le A B
    rw [hdiff, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * b ^ j)] at hcos
    have hscale := mul_le_of_le_one_right (by positivity : 0 ≤ 2 * Real.pi * b ^ j) (hd j)
    calc
      _ ≤ g ^ j * ((2 * Real.pi * b ^ j * |d j|) * |x|) :=
        mul_le_mul_of_nonneg_left hcos (zpow_pos hg _).le
      _ ≤ g ^ j * ((2 * Real.pi * b ^ j) * |x|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale (abs_nonneg _)) (zpow_pos hg _).le
      _ = _ := by rw [mul_zpow]; ring

/-- Absolute convergence of both tails, for arbitrary bounded weights and directions. -/
theorem summable_rayTerm {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b * g) {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (z : ℤ → ℝ) (x : ℝ) : Summable (rayTerm b g c d z x) :=
  (summable_rayMajorant hg hg1 hbg x).of_norm_bounded (rayTerm_bound hb hg hc hd z x)

/-- Shifting the indices rotates the physical unit ray by the same number of steps. -/
theorem rayProjection_shift {D : ℂ} (hD : D ≠ 0) (v : ℂ) (i n : ℤ) :
    rayProjection D v (i+n) = rayProjection D (v * (D / (‖D‖ : ℂ)) ^ n) i := by
  have hnorm : (‖D‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hD)
  unfold rayProjection
  rw [zpow_add₀ (div_ne_zero hD hnorm)]
  ring_nf

/-- Recenter at an arbitrary point and zoom by any integer number of physical scales.
This is the child rescaling in §6; negative indices also give the fixed dilation in §2. -/
theorem rayIncrement_recenter_scale {b g : ℝ} (hb : 0 < b) (hg : 0 < g)
    (hg1 : g < 1) (hbg : 1 < b * g) {c d : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (z : ℤ → ℝ) (n : ℤ) (x y : ℝ) :
    rayIncrement b g c d z (x + b ^ (-n) * y) - rayIncrement b g c d z x =
      g ^ n * rayIncrement b g (fun i ↦ c (i+n)) (fun i ↦ d (i+n))
        (fun i ↦ z (i+n) + b ^ (i+n) * d (i+n) * x) y := by
  let diff (i : ℤ) := rayTerm b g c d z (x + b ^ (-n) * y) i - rayTerm b g c d z x i
  have hs₁ := summable_rayTerm hb hg hg1 hbg hc hd z (x + b ^ (-n) * y)
  have hs₂ := summable_rayTerm hb hg hg1 hbg hc hd z x
  unfold rayIncrement
  rw [← hs₁.tsum_sub hs₂, ← tsum_mul_left]
  change (∑' i : ℤ, diff i) = _
  rw [← (Equiv.addRight n).tsum_eq (f := diff)]
  apply tsum_congr
  intro i
  change rayTerm b g c d z (x + b ^ (-n) * y) (i+n) - rayTerm b g c d z x (i+n) = _
  unfold rayTerm
  have harg : z (i+n) + b ^ (i+n) * d (i+n) * (x + b ^ (-n) * y) =
      z (i+n) + b ^ (i+n) * d (i+n) * x + b ^ i * d (i+n) * y := by
    have hp : b ^ (i+n) * b ^ (-n) = b ^ i := by rw [← zpow_add₀ hb.ne', add_neg_cancel_right]
    linear_combination d (i+n) * y * hp
  rw [harg, zpow_add₀ hg.ne']
  ring

/-- Translation along the transverse ray, in real phase lifts. -/
def transversePhase (ρ : ℝ) (e z : ℤ → ℝ) (u : ℝ) (j : ℤ) : ℝ :=
  z j + ρ ^ j * e j * u

private theorem cosine_quarter (a : ℝ) : Real.cos (2 * Real.pi * (a + 1/4)) =
    -Real.sin (2 * Real.pi * a) := by
  rw [show 2 * Real.pi * (a + 1/4) = 2 * Real.pi * a + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two]

private theorem hasDerivAt_rayTerm (b g ρ : ℝ) (c d e z : ℤ → ℝ) (x u : ℝ) (j : ℤ) :
    HasDerivAt (fun t ↦ rayTerm b g c d (transversePhase ρ e z t) x j)
      ((2 * Real.pi) * rayTerm b (g * ρ) (fun i ↦ c i * e i) d
        (fun i ↦ transversePhase ρ e z u i + 1/4) x j) u := by
  let Z := z j
  let V := ρ ^ j * e j
  let X := b ^ j * d j * x
  have hphase : HasDerivAt (fun t : ℝ ↦ Z + V * t) V u := by
    simpa using (((hasDerivAt_id u).const_mul V).const_add Z)
  have h₁ := (((hphase.add_const X).const_mul (2 * Real.pi)).cos)
  have h₂ := ((hphase.const_mul (2 * Real.pi)).cos)
  apply ((h₁.sub h₂).const_mul (g ^ j * c j)).congr_deriv
  unfold rayTerm transversePhase
  dsimp [Z, V, X]
  rw [show z j + ρ ^ j * e j * u + 1 / 4 + b ^ j * d j * x =
    (z j + ρ ^ j * e j * u + b ^ j * d j * x) + 1 / 4 by ring,
    cosine_quarter, cosine_quarter, mul_zpow]
  ring

/-- In the regime `1 < b * (g * ρ)`, transverse differentiation replaces the amplitude
by `g * ρ`, multiplies each weight by its transverse projection, and adds a quarter turn
to every phase. The result holds at every real transverse parameter and physical input. -/
theorem hasDerivAt_transverse_rayIncrement {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hbgρ : 1 < b * (g * ρ)) {c d e : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : ℤ → ℝ) (x u : ℝ) :
    HasDerivAt (fun t ↦ rayIncrement b g c d (transversePhase ρ e z t) x)
      ((2 * Real.pi) * rayIncrement b (g * ρ) (fun j ↦ c j * e j) d
        (fun j ↦ transversePhase ρ e z u j + 1/4) x) u := by
  have hprod := mul_lt_of_lt_one_right hg hρ1
  have hbg := hbgρ.trans (mul_lt_mul_of_pos_left hprod hb)
  have hce (j : ℤ) : |c j * e j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (he j)).trans (hc j)
  unfold rayIncrement
  rw [← tsum_mul_left]
  apply hasDerivAt_tsum ((summable_rayMajorant (mul_pos hg hρ) (hprod.trans hg1) hbgρ x).mul_left (2 * Real.pi))
      (fun j t ↦ hasDerivAt_rayTerm b g ρ c d e z x t j)
  · intro j t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left (rayTerm_bound hb (mul_pos hg hρ) hce hd _ x j) (by positivity)
  · exact summable_rayTerm hb hg hg1 hbg hc hd (transversePhase ρ e z 0) x

namespace CriticalRay

abbrev τ : ℝ := 2 * Real.pi
private theorem τpos : 0 < τ := by dsimp [τ]; positivity

/-- Single-mode mixed difference of the unit-period cosine. -/
def cosineMixed (z x y : ℝ) : ℝ :=
  (Real.cos (τ * (z+y+x)) - Real.cos (τ * (z+y))) -
    (Real.cos (τ * (z+x)) - Real.cos (τ * z))

/-- Mixed Taylor bound with a phase-independent cubic error, at both signs of
each displacement. The two mean value arguments also apply to zero steps. -/
theorem cosineMixed_linearization (z x y : ℝ) :
    |cosineMixed z x y - x*y*(-τ^2 * Real.cos (τ*z))| ≤
      τ^3 * |x| * |y| * (|x| + |y|) := by
  let f (s : ℝ) := Real.cos (τ * (z + y*s + x)) - Real.cos (τ * (z + y*s))
  let f' (s : ℝ) := (-Real.sin (τ * (z + y*s + x)) + Real.sin (τ * (z+y*s))) * (τ*y)
  have hf (s : ℝ) : HasDerivAt f (f' s) s := by
    have h := (((hasDerivAt_id s).const_mul y).const_add z)
    apply HasDerivAt.congr_deriv ((((h.add_const x).const_mul τ).cos).sub ((h.const_mul τ).cos))
    dsimp [f']
    ring
  obtain ⟨s,hs,hslope⟩ := exists_hasDerivAt_eq_slope f f' zero_lt_one
    (fun a _ ↦ (hf a).continuousAt.continuousWithinAt) (fun s _ ↦ hf s)
  let g (t : ℝ) := -Real.sin (τ * (z+y*s+x*t))
  let g' (t : ℝ) := -(Real.cos (τ * (z+y*s+x*t)) * (τ*x))
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    have h := (((hasDerivAt_id t).const_mul x).const_add (z+y*s))
    apply (((h.const_mul τ).sin).neg).congr_deriv
    dsimp [g']
    ring
  obtain ⟨t,ht,htslope⟩ := exists_hasDerivAt_eq_slope g g' zero_lt_one
    (fun a _ ↦ (hg a).continuousAt.continuousWithinAt) (fun t _ ↦ hg t)
  have diff : cosineMixed z x y = x*y*(-τ^2 * Real.cos (τ * (z+y*s+x*t))) := by
    simp only [f, f', g, g', mul_one, mul_zero, add_zero, sub_zero, div_one] at hslope htslope
    unfold cosineMixed
    linear_combination -hslope - (τ*y)*htslope
  rw [diff, ← mul_sub, abs_mul]
  have hcos := Real.abs_cos_sub_cos_le (τ * (z+y*s+x*t)) (τ*z)
  rw [show τ * (z+y*s+x*t) - τ*z = τ * (y*s+x*t) by ring,
    abs_mul, abs_of_pos τpos] at hcos
  have hs' : |y*s| ≤ |y| := by
    rw [abs_mul, abs_of_pos hs.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hs.2.le
  have ht' : |x*t| ≤ |x| := by
    rw [abs_mul, abs_of_pos ht.1]
    exact mul_le_of_le_one_right (abs_nonneg _) ht.2.le
  have hadd : |y*s+x*t| ≤ |x| + |y| := by linarith [abs_add_le (y*s) (x*t)]
  rw [← mul_sub, abs_mul x y, abs_mul (-(τ^2)), abs_neg, abs_of_nonneg (sq_nonneg τ)]
  have hτ := τpos
  calc
    _ ≤ |x| * |y| * (τ^2 * (τ*(|x| + |y|))) := by gcongr; exact hcos.trans (by gcongr)
    _ = _ := by ring


private theorem projectionBound {q v t : ℝ} (hq : 0 < q) (hv : |v| ≤ 1) (j : ℤ) :
    |q ^ j * v * t| ≤ q ^ j * |t| := by
  rw [abs_mul, abs_mul, abs_of_pos (zpow_pos hq _)]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (zpow_pos hq _).le hv) (abs_nonneg _)

private theorem scaleWeight {g c : ℝ} (hg : 0 < g) (hc : |c| ≤ 1) (j : ℤ) :
    |g ^ j * c| ≤ g ^ j := by
  rw [abs_mul, abs_of_pos (zpow_pos hg _)]
  exact mul_le_of_le_one_right (zpow_pos hg _).le hc

/-- The middle block at criticality. Its main term has a scale-independent
coefficient, including for negative indices and weights of either sign. -/
theorem singleMode_critical {b g ρ c d e : ℝ} (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (he : |e| ≤ 1) (hcrit : g * b * ρ = 1)
    (j : ℤ) (z t h : ℝ) :
    |(g^j*c) * cosineMixed z (b^j*d*t) (ρ^j*e*h) -
      t*h*(c*d*e)*(-τ^2*Real.cos (τ*z))| ≤
      τ^3 * |t| * |h| * (b^j*|t| + ρ^j*|h|) := by
  let X := b^j*d*t
  let Y := ρ^j*e*h
  let W := g^j*c
  let P := -τ^2*Real.cos (τ*z)
  have hx : |X| ≤ b^j*|t| := projectionBound hb hd _
  have hy : |Y| ≤ ρ^j*|h| := projectionBound hρ he _
  have hw : |W| ≤ g^j := scaleWeight hg hc _
  have hpow : g^j*b^j*ρ^j = 1 := by rw [← mul_zpow, ← mul_zpow, hcrit, one_zpow]
  have hwxy : W*(X*Y) = t*h*(c*d*e) := by
    dsimp [W,X,Y]
    linear_combination (t*h*c*d*e)*hpow
  change |W * cosineMixed z X Y - t*h*(c*d*e)*P| ≤ _
  rw [← hwxy, mul_assoc W, ← mul_sub, abs_mul]
  calc
    _ ≤ g^j * (τ^3 * |X| * |Y| * (|X| + |Y|)) :=
      mul_le_mul hw (cosineMixed_linearization z X Y) (abs_nonneg _) (zpow_pos hg _).le
    _ ≤ g^j * (τ^3 * (b^j*|t|) * (ρ^j*|h|) * (b^j*|t| + ρ^j*|h|)) := by
      have hτ := τpos
      gcongr
    _ = _ := by linear_combination (τ^3*|t| * |h| * (b^j*|t| + ρ^j*|h|))*hpow

theorem cosineMixed_bound (z x y : ℝ) : |cosineMixed z x y| ≤ 2*τ*|x| := by
  have ha (a : ℝ) : |Real.cos (τ*(a+x)) - Real.cos (τ*a)| ≤ τ*|x| := by
    have H := Real.abs_cos_sub_cos_le (τ*(a+x)) (τ*a)
    rwa [show τ*(a+x) - τ*a = τ*x by ring, abs_mul, abs_of_pos τpos] at H
  unfold cosineMixed
  exact (abs_sub _ _).trans (by linarith [ha (z+y), ha z])

theorem cosineMixed_symm (z x y : ℝ) : cosineMixed z x y = cosineMixed z y x := by
  unfold cosineMixed
  rw [show z+y+x = z+x+y by ring]
  ring


private def envelope (q : ℝ) (m j : ℤ) : ℝ := q ^ |j-m|

set_option maxHeartbeats 1000000 in
private theorem hasSum_envelope {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (m : ℤ) :
    HasSum (envelope q m) ((1 + q) * (1-q)⁻¹) := by
  have hs := hasSum_geometric_of_lt_one hq.le hq1
  have hp : HasSum (fun j : ℕ ↦ q ^ |(j : ℤ)|) (1-q)⁻¹ := by simpa using hs
  have hn : HasSum (fun j : ℕ ↦ q ^ |-(↑j+1 : ℤ)|) (q*(1-q)⁻¹) := by
    convert! hs.mul_left q using 1
    funext j
    rw [abs_neg, abs_of_nonneg (by omega), show (↑j+1 : ℤ) = ((j+1 : ℕ) : ℤ) by omega,
      zpow_natCast, pow_succ, mul_comm]
  have hz : HasSum (fun j : ℤ ↦ q ^ |j|) ((1+q)*(1-q)⁻¹) := by
    rw [add_mul, one_mul]
    exact HasSum.of_nat_of_neg_add_one (f := fun j : ℤ ↦ q ^ |j|) hp hn
  exact (Equiv.addRight (-m)).hasSum_iff (f := fun j : ℤ ↦ q ^ |j|) |>.mpr hz

private theorem envelope_low {q : ℝ} (m j : ℤ) (hj : j ≤ m) :
    envelope q m j = q ^ (m-j) := by
  rw [envelope, abs_of_nonpos (sub_nonpos.mpr hj), neg_sub]

private theorem envelope_high {q : ℝ} (m j : ℤ) (hj : m ≤ j) :
    envelope q m j = q ^ (j-m) := by
  rw [envelope, abs_of_nonneg (sub_nonneg.mpr hj)]

private def mainTerm (c d e z : ℤ → ℝ) (j : ℤ) : ℝ :=
  c j * d j * e j * (-τ^2 * Real.cos (τ*z j))

private def modeDiff (b g ρ : ℝ) (c d e z : ℤ → ℝ) (t h : ℝ) (j : ℤ) :=
  (g^j*c j) * cosineMixed (z j) (b^j*d j*t) (ρ^j*e j*h)

private theorem modeDiff_eq (b g ρ : ℝ) (c d e z : ℤ → ℝ) (t h : ℝ) (j : ℤ) :
    modeDiff b g ρ c d e z t h j =
      rayTerm b g c d (transversePhase ρ e z h) t j - rayTerm b g c d z t j := by
  unfold modeDiff cosineMixed rayTerm transversePhase
  ring

private theorem tail_mode_bound {g b ρ : ℝ} (hg : 0 < g) (hb : 0 < b) (hρ : 0 < ρ)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : ℤ → ℝ) (t h : ℝ) (j : ℤ) :
    |modeDiff b g ρ c d e z t h j| ≤ 2*τ*(g*b)^j*|t| ∧
    |modeDiff b g ρ c d e z t h j| ≤ 2*τ*(g*ρ)^j*|h| := by
  let X := b^j*d j*t
  let Y := ρ^j*e j*h
  have hτ := τpos
  change |(g^j*c j)*cosineMixed (z j) X Y| ≤ _ ∧ |(g^j*c j)*cosineMixed (z j) X Y| ≤ _
  rw [abs_mul, mul_zpow, mul_zpow]
  have bound (p w a : ℝ) (hp : 0 < p) (hw : |w| ≤ 1)
      (hb' : |cosineMixed (z j) X Y| ≤ 2*τ*|p^j*w*a|) :
      |g^j*c j| * |cosineMixed (z j) X Y| ≤ 2*τ*(g^j*p^j)*|a| := by
    calc
      _ ≤ g^j * (2*τ*(p^j*|a|)) := by
        apply mul_le_mul (scaleWeight hg (hc j) j) _ (abs_nonneg _) (zpow_pos hg _).le
        exact hb'.trans (mul_le_mul_of_nonneg_left (projectionBound hp hw _) (by positivity))
      _ = _ := by ring
  constructor
  · exact bound b (d j) t hb (hd j) (cosineMixed_bound _ _ _)
  · apply bound ρ (e j) h hρ (he j)
    rw [cosineMixed_symm]
    exact cosineMixed_bound _ _ _


private def physicalConstant (b D : ℝ) := τ^3*D + 2*τ*b*D
private def transverseConstant (D : ℝ) := τ^3*D^2 + 2*τ

private theorem residual_bound {g b ρ D : ℝ} (hg : 0 < g) (hb : 0 < b) (hρ : 0 < ρ)
    (hD : 0 ≤ D) (hcrit : g*b*ρ = 1) {c d e : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : ℤ → ℝ) (t h : ℝ) (k N j : ℤ) (htlo : b ^ (-k-1) ≤ |t|) (hthi : |t| ≤ b ^ (-k))
    (hh : |h| ≤ D*ρ^N) :
    |modeDiff b g ρ c d e z t h j -
      (if j ∈ Finset.Icc (-N) k then t*h*mainTerm c d e z j else 0)| ≤
      (|t| * ρ^N) * (physicalConstant b D * envelope b⁻¹ k j +
        transverseConstant D * envelope ρ (-N) j) := by
  have hτ := τpos
  have EB := zpow_pos (inv_pos.mpr hb) |j-k|
  have ER := zpow_pos hρ |j-(-N)|
  change 0 < envelope b⁻¹ k j at EB
  change 0 < envelope ρ (-N) j at ER
  have p0 : 0 ≤ physicalConstant b D := by unfold physicalConstant; positivity
  have r0 : 0 ≤ transverseConstant D := by unfold transverseConstant; positivity
  have tail := tail_mode_bound hg hb hρ hc hd he z t h j
  by_cases hL : j < -N
  · rw [if_neg (by simp only [Finset.mem_Icc]; omega), sub_zero]
    have hgb : g*b = ρ⁻¹ := (eq_inv_of_mul_eq_one_left hcrit)
    have hgeom : (g*b)^j = ρ^N * envelope ρ (-N) j := by
      rw [hgb, envelope_low _ _ hL.le, inv_zpow, ← zpow_neg, ← zpow_add₀ hρ.ne']
      congr 1; omega
    calc
      _ ≤ 2*τ*(g*b)^j*|t| := tail.1
      _ = (|t| * ρ^N)*(2*τ*envelope ρ (-N) j) := by rw [hgeom]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply le_add_of_nonneg_of_le (mul_nonneg p0 EB.le)
        apply mul_le_mul_of_nonneg_right _ ER.le
        unfold transverseConstant
        exact le_add_of_nonneg_left (by positivity)
  by_cases hR : k < j
  · rw [if_neg (by simp only [Finset.mem_Icc]; omega), sub_zero]
    have hgρ : g*ρ = b⁻¹ := eq_inv_of_mul_eq_one_left (by linarith only [hcrit] : (g*ρ)*b=1)
    have hgeom : (g*ρ)^j = b * b^(-k-1) * envelope b⁻¹ k j := by
      rw [hgρ, envelope_high _ _ hR.le, inv_zpow, inv_zpow, ← zpow_neg, ← zpow_neg]
      calc
        _ = b ^ ((1:ℤ) + (-k-1) + -(j-k)) := by congr 1; omega
        _ = _ := by rw [zpow_add₀ hb.ne', zpow_add₀ hb.ne', zpow_one]
    calc
      _ ≤ 2*τ*(g*ρ)^j*|h| := tail.2
      _ ≤ 2*τ*(b * |t| * envelope b⁻¹ k j)*(D*ρ^N) := by rw [hgeom]; gcongr
      _ = (|t| * ρ^N)*(2*τ*b*D*envelope b⁻¹ k j) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply le_add_of_le_of_nonneg _ (mul_nonneg r0 ER.le)
        apply mul_le_mul_of_nonneg_right _ EB.le
        unfold physicalConstant
        exact le_add_of_nonneg_left (by positivity)
  have hL' : -N ≤ j := by omega
  have hR' : j ≤ k := by omega
  rw [if_pos (Finset.mem_Icc.mpr ⟨hL',hR'⟩)]
  have hX : b^j*|t| ≤ envelope b⁻¹ k j := by
    calc
      _ ≤ b^j*b^(-k) := mul_le_mul_of_nonneg_left hthi (zpow_pos hb _).le
      _ = _ := by
        rw [envelope_low _ _ hR', inv_zpow, ← zpow_neg, ← zpow_add₀ hb.ne']
        congr 1; omega
  have hY : ρ^j*|h| ≤ D*envelope ρ (-N) j := by
    calc
      _ ≤ ρ^j*(D*ρ^N) := mul_le_mul_of_nonneg_left hh (zpow_pos hρ _).le
      _ = _ := by rw [envelope_high _ _ hL', sub_neg_eq_add, zpow_add₀ hρ.ne']; ring
  calc
    _ ≤ τ^3 * |t| * |h| * (b^j*|t| + ρ^j*|h|) := by
      simpa only [modeDiff, mainTerm, mul_assoc] using singleMode_critical hb hg hρ (hc j)
        (hd j) (he j) hcrit j (z j) t h
    _ ≤ τ^3 * |t| * (D*ρ^N) * (envelope b⁻¹ k j + D*envelope ρ (-N) j) := by gcongr
    _ = (|t| * ρ^N)*(τ^3*D*envelope b⁻¹ k j + τ^3*D^2*envelope ρ (-N) j) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add <;> apply mul_le_mul_of_nonneg_right
      · unfold physicalConstant; exact le_add_of_nonneg_right (by positivity)
      · exact EB.le
      · unfold transverseConstant; exact le_add_of_nonneg_right (by positivity)
      · exact ER.le


/-- An admissible constant for the uniform error in (RC4). -/
def criticalErrorConstant (b ρ D : ℝ) :=
  (τ^3*D+2*τ*b*D)*((1+b⁻¹)*(1-b⁻¹)⁻¹) +
    (τ^3*D^2 + 2*τ)*((1+ρ)*(1-ρ)⁻¹)

/-- Equation (RC4) for the actual weighted bilateral increment, with a constant
independent of the two scales, all phases, all permitted weights, and the two
signed ray directions. The endpoints of the drift sum are both inclusive. -/
theorem critical_linearization {g b ρ D : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 ≤ D) (hcrit : g*b*ρ = 1) {c d e : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : ℤ → ℝ) (t h : ℝ) (k N : ℤ) (htlo : b ^ (-k-1) ≤ |t|) (hthi : |t| ≤ b ^ (-k))
    (hh : |h| ≤ D*ρ^N) :
    |(rayIncrement b g c d (transversePhase ρ e z h) t - rayIncrement b g c d z t)/t -
      h * ∑ j ∈ Finset.Icc (-N) k, c j * d j * e j * (-τ^2*Real.cos (τ*z j))| ≤
      criticalErrorConstant b ρ D * ρ^N := by
  have hb0 := zero_lt_one.trans hb
  have ht := (zpow_pos hb0 (-k-1)).trans_le htlo
  have ht0 := abs_pos.mp ht
  have hbg : 1 < b*g := by
    have h' : g*b = ρ⁻¹ := eq_inv_of_mul_eq_one_left hcrit
    rw [mul_comm, h']
    exact one_lt_inv_iff₀.mpr ⟨hρ,hρ1⟩
  let Δ := rayIncrement b g c d (transversePhase ρ e z h) t - rayIncrement b g c d z t
  let S := Finset.Icc (-N) k
  let drift := ∑ j ∈ S, mainTerm c d e z j
  let localDrift (j : ℤ) := if j ∈ S then t*h*mainTerm c d e z j else 0
  have sumDiff : HasSum (modeDiff b g ρ c d e z t h) Δ := by
    have hs := (summable_rayTerm hb0 hg hg1 hbg hc hd (transversePhase ρ e z h) t).hasSum.sub
      (summable_rayTerm hb0 hg hg1 hbg hc hd z t).hasSum
    have heq : modeDiff b g ρ c d e z t h = fun j ↦
        rayTerm b g c d (transversePhase ρ e z h) t j - rayTerm b g c d z t j :=
      funext (modeDiff_eq b g ρ c d e z t h)
    rw [heq]; exact hs
  have finD : HasSum localDrift (∑ j ∈ S, localDrift j) :=
    hasSum_sum_of_ne_finset_zero (fun j hj ↦ by simp [localDrift, hj])
  have hdval : ∑ j ∈ S, localDrift j = t*h*drift := by
    rw [show t*h*drift = ∑ j ∈ S, t*h*mainTerm c d e z j by simp [drift, Finset.mul_sum]]
    exact Finset.sum_congr rfl (fun j hj ↦ if_pos hj)
  rw [hdval] at finD
  have total := sumDiff.sub finD
  have A := (hasSum_envelope (inv_pos.mpr hb0) (inv_lt_one_of_one_lt₀ hb) k).mul_left (physicalConstant b D)
  have B := (hasSum_envelope hρ hρ1 (-N)).mul_left (transverseConstant D)
  have major := (A.add B).mul_left (|t| * ρ^N)
  have err : |Δ-t*h*drift| ≤ (|t| *ρ^N)*criticalErrorConstant b ρ D := by
    rw [← total.tsum_eq, ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded major (fun j ↦ residual_bound hg hb0 hρ hD hcrit hc hd he z t h k N j htlo hthi hh)
  change |Δ/t-h*drift| ≤ _
  rw [show Δ/t-h*drift = (Δ-t*h*drift)/t by field_simp, abs_div, div_le_iff₀ ht]
  exact err.trans_eq (by ring)

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- Number of levels in a window of radius D about a given drift value. -/
def valueCount {ι : Type*} (s : Finset ι) (v : ι → ℝ) (D t : ℝ) : ℕ :=
  (s.filter (fun j ↦ |v j - t| ≤ D)).card

private def pairSet {Ω : Type*} (V : Ω → ℤ → ℝ) (D : ℝ) (p : ℤ × ℤ) : Set Ω :=
  {z | |V z p.1 - V z p.2| ≤ 2*D}

/-- A large occupation count forces quadratically many ordered collisions. -/
theorem valueCount_sq_le_pairs {ι : Type*} (s : Finset ι) (v : ι → ℝ) (D t : ℝ) :
    (valueCount s v D t)^2 ≤ ((s ×ˢ s).filter (fun p ↦ |v p.1-v p.2| ≤ 2*D)).card := by
  classical
  let a := s.filter (fun j ↦ |v j - t| ≤ D)
  change a.card^2 ≤ _
  rw [sq, ← Finset.card_product]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  obtain ⟨his,hiv⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjs,hjv⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨his,hjs⟩,?_⟩
  have h := abs_sub (v p.1-t) (v p.2-t)
  rw [sub_sub_sub_cancel_right] at h
  linarith

private theorem pairMarkov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → ℤ → ℝ) (hV : ∀ i, Measurable (fun z ↦ V z i))
    (s : Finset ℤ) (D Q : ℝ) (hQ : 0 ≤ Q) :
    ENNReal.ofReal (Q^2) * μ {z | ∃ t, Q ≤ (valueCount s (V z) D t : ℝ)} ≤
      ∑ p ∈ s ×ˢ s, μ (pairSet V D p) := by
  classical
  let pairs := s ×ˢ s
  let I (p : ℤ × ℤ) := (pairSet V D p).indicator (fun _ : Ω ↦ (1 : ℝ≥0∞))
  have hset (p : ℤ × ℤ) : MeasurableSet (pairSet V D p) :=
    measurableSet_le (continuous_abs.measurable.comp ((hV p.1).sub (hV p.2))) measurable_const
  have hi (p : ℤ × ℤ) : Measurable (I p) := measurable_const.indicator (hset p)
  let X (z : Ω) := ∑ p ∈ pairs, I p z
  have hm : Measurable X := Finset.measurable_sum pairs (fun p _ ↦ hi p)
  have hsub : {z | ∃ t, Q ≤ (valueCount s (V z) D t : ℝ)} ⊆ {z | ENNReal.ofReal (Q^2) ≤ X z} := by
    rintro z ⟨t,ht⟩
    have h := valueCount_sq_le_pairs s (V z) D t
    have hR : Q^2 ≤ (((pairs.filter (fun p ↦ |V z p.1-V z p.2| ≤ 2*D)).card : ℕ) : ℝ) := by
      calc
        _ ≤ (valueCount s (V z) D t : ℝ)^2 := by gcongr
        _ ≤ _ := by exact_mod_cast h
    have hE := ENNReal.ofReal_le_ofReal hR
    rw [ENNReal.ofReal_natCast] at hE
    change ENNReal.ofReal (Q^2) ≤ (∑ p ∈ pairs, I p z)
    simpa only [Finset.natCast_card_filter, I, Set.indicator_apply,
      pairSet, Set.mem_ofPred_eq] using hE
  calc
    _ ≤ ENNReal.ofReal (Q^2) * μ {z | ENNReal.ofReal (Q^2) ≤ X z} :=
      by gcongr
    _ ≤ ∫⁻ z, X z ∂μ := mul_meas_ge_le_lintegral hm _
    _ = ∑ p ∈ pairs, μ (pairSet V D p) := by
      rw [show (∫⁻ z, X z ∂μ) = ∑ p ∈ pairs, ∫⁻ z, I p z ∂μ from
        lintegral_finsetSum pairs (fun p _ ↦ hi p)]
      exact Finset.sum_congr rfl (fun p _ ↦ lintegral_indicator_one (hset p))


private theorem pairSum_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℤ → ℝ) (D : ℝ) (δ : ℝ≥0∞) (K : ℕ) (s : Finset ℤ)
    (hfar : ∀ i j : ℤ, (K : ℤ) ≤ |i-j| → μ (pairSet V D (i,j)) ≤ δ) :
    ∑ p ∈ s ×ˢ s, μ (pairSet V D p) ≤ (s.card : ℝ≥0∞)*((2*K+1 : ℕ) + s.card*δ) := by
  classical
  have few (i : ℤ) : (s.filter (fun j ↦ |i-j| ≤ (K:ℤ))).card ≤ 2*K + 1 := by
    calc
      _ ≤ (Finset.Icc (i-(K:ℤ)) (i+K)).card := by
        apply Finset.card_le_card
        intro j hj
        have hk := abs_le.mp (Finset.mem_filter.mp hj).2
        apply Finset.mem_Icc.mpr
        omega
      _ = _ := by rw [Int.card_Icc]; omega
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ _ ∈ s, (((2*K+1 : ℕ) : ℝ≥0∞) + s.card*δ) := Finset.sum_le_sum ?_
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  intro i _
  calc
    _ ≤ ∑ j ∈ s, ((if |i-j| ≤ (K:ℤ) then (1:ℝ≥0∞) else 0)+δ) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h
      · exact ((measure_mono (Set.subset_univ _)).trans_eq (measure_univ)).trans (le_add_of_nonneg_right (zero_le))
      · rw [zero_add]; exact hfar i j (le_of_not_ge h)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
      apply add_le_add_left
      exact_mod_cast few i

/-- Uniform consequence of block anticoncentration (RC3) for occupation counts.
The bound is uniform over every initial level and every environment model in the
given family, and the interval center can depend on the realized environment. -/
theorem occupation_of_block_anticoncentration {A Ω : Type*} [MeasurableSpace Ω]
    (μ : A → Measure Ω) [∀ a, IsProbabilityMeasure (μ a)]
    (V : A → Ω → ℤ → ℝ) (hV : ∀ a i, Measurable (fun z ↦ V a z i)) (D : ℝ)
    (hsep : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ a i j, (K:ℤ) ≤ |i-j| →
      μ a {z | |V a z i - V a z j| ≤ 2*D} ≤ ENNReal.ofReal δ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (a : A) (o : ℤ), μ a {z | ∃ t, ε*(n:ℝ) ≤
      valueCount (Finset.Ico o (o+n)) (V a z) D t} ≤ ENNReal.ofReal η := by
  let δ := ε^2*η/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK⟩ := hsep δ hδ
  obtain ⟨N,hN⟩ := exists_nat_gt (((2*K+1:ℕ):ℝ)/δ)
  refine ⟨N,?_⟩
  intro n hn a o
  let s := Finset.Ico o (o+n)
  let E := {z | ∃ t, ε*(n:ℝ) ≤ valueCount s (V a z) D t}
  have hcard : s.card = n := by simp [s, Int.card_Ico]
  have hnR : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hCounts := (div_lt_iff₀ hδ).mp (hN.trans_le hnR)
  have hnpos : 0 < (n:ℝ) := by
    by_contra! hn0
    have := mul_nonpos_of_nonpos_of_nonneg hn0 hδ.le
    have hkpos : 0 < ((2*K+1:ℕ):ℝ) := by positivity
    linarith
  have hmark := pairMarkov (μ a) (V a) (hV a) s D (ε*n) (by positivity)
  have hsum := pairSum_bound (μ a) (V a) D (ENNReal.ofReal δ) K s (hK a)
  have hbound : ENNReal.ofReal ((ε*n)^2) * μ a E ≤
      ENNReal.ofReal ((n:ℝ) * (((2*K+1:ℕ):ℝ) + n*δ)) := by
    have h := hmark.trans hsum
    rw [hcard] at h
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hδ.le),
      ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    simpa only [ENNReal.ofReal_natCast] using h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (by positivity)] at hreal
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hη.le]
  apply le_of_mul_le_mul_left (a := (ε*n)^2) _ (by positivity)
  refine hreal.trans ?_
  calc
    _ ≤ (n:ℝ) * (n*δ + n*δ) := by gcongr
    _ = _ := by dsimp [δ]; ring

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- A Fourier character with a separately indexed list of occurrences. This
representation allows equal time indices, as required in a moment expansion. -/
def phaseCharacter {ι : Type*} (s : Finset ι) (j : ι → ℤ) (n : ι → ℤ) (z : PhaseTorus) : ℂ :=
  AddCircle.toCircle (∑ i ∈ s, n i • z (j i))

private theorem phaseCharacter_add {ι : Type*} (s : Finset ι) (j n : ι → ℤ) (v w : PhaseTorus) :
    phaseCharacter s j n (v+w) = phaseCharacter s j n v * phaseCharacter s j n w := by
  simp [phaseCharacter, Finset.sum_add_distrib, AddCircle.toCircle_add]

private theorem phaseCharacter_continuous {ι : Type*} (s : Finset ι) (j n : ι → ℤ) :
    Continuous (phaseCharacter s j n) := by
  unfold phaseCharacter
  fun_prop

private theorem phaseCharacter_orbit {ι : Type*} (s : Finset ι) (j n : ι → ℤ) (B x : ℂ) :
    phaseCharacter s j n (complexPhaseOrbit B x) =
      (AddCircle.toCircle (↑(((∑ i ∈ s, (n i : ℂ)*B^(j i))*x).re) : AddCircle (1 : ℝ)) : ℂ) := by
  let q : ℂ →+ AddCircle (1 : ℝ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp Complex.reAddGroupHom
  have h : (∑ i ∈ s, n i • q (B^(j i)*x)) = q ((∑ i ∈ s, (n i : ℂ)*B^(j i))*x) := by
    simp only [Finset.sum_mul, map_sum, ← map_zsmul, zsmul_eq_mul, mul_assoc]
  exact congrArg (fun a : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle a : ℂ)) h

/-- Exact Fourier expectation on an arbitrary Haar coset. A term of any moment
survives exactly when the corresponding signed Laurent sum vanishes. -/
theorem integral_phaseCharacter {ι : Type*} (s : Finset ι) (j n : ι → ℤ)
    (B : ℂ) (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    (ω : PhaseTorus) :
    ∫ z, phaseCharacter s j n (ω+z.val) ∂μ =
      if (∑ i ∈ s, (n i : ℂ)*B^(j i)) = 0 then phaseCharacter s j n ω else 0 := by
  classical
  let χ := phaseCharacter s j n
  let A := ∑ i ∈ s, (n i : ℂ)*B^(j i)
  have hχ := phaseCharacter_add s j n
  rw [show (fun z : complexPhaseGroup B ↦ phaseCharacter s j n (ω+z.val)) =
      fun z : complexPhaseGroup B ↦ χ ω * χ z.val from funext (fun z ↦ hχ ω z.val), integral_const_mul]
  by_cases hz : A = 0
  · rw [if_pos hz]
    have hclosed : IsClosed {v : PhaseTorus | χ v = 1} := isClosed_eq (phaseCharacter_continuous s j n) continuous_const
    have htriv (z : complexPhaseGroup B) : χ z.val = 1 := by
      apply closure_minimal _ hclosed z.property
      rintro _ ⟨x, rfl⟩
      change phaseCharacter s j n (complexPhaseOrbit B x) = 1
      rw [phaseCharacter_orbit, show (∑ i ∈ s, (n i : ℂ)*B^(j i)) = 0 from hz]
      simp
    simp [htriv, χ]
  · rw [if_neg hz]
    let x : ℂ := (1/2 : ℂ)/A
    let w : complexPhaseGroup B :=
      ⟨complexPhaseOrbit B x, (complexPhaseOrbit B).range.le_topologicalClosure ⟨x,rfl⟩⟩
    have hnot : χ w.val ≠ 1 := by
      change phaseCharacter s j n (complexPhaseOrbit B x) ≠ 1
      rw [phaseCharacter_orbit, show A*x = 1/2 by dsimp [x]; field_simp]
      simpa using half_turn_ne_one
    let v := ∫ z : complexPhaseGroup B, χ z.val ∂μ
    have hinv : χ w.val * v = v := by
      have h := integral_add_left_eq_self (μ := μ) (fun z : complexPhaseGroup B ↦ χ z.val) w
      simpa only [AddSubgroup.coe_add, phaseCharacter_add, integral_const_mul, χ, v] using h
    have hv : v = 0 := by
      by_contra hn
      exact hnot (mul_right_cancel₀ hn (hinv.trans (one_mul v).symm))
    change χ ω * v = 0
    rw [hv, mul_zero]


/-- The real cosine of an angle in turns. -/
def angleCos (θ : AddCircle (1 : ℝ)) : ℝ := (AddCircle.toCircle θ : ℂ).re

theorem angleCos_coe (x : ℝ) : angleCos (↑x) = Real.cos (2*Real.pi*x) := by
  rw [angleCos, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

private theorem angleCos_product (θ φ : AddCircle (1 : ℝ)) :
    angleCos θ * angleCos φ = (angleCos (θ+φ) + angleCos (θ-φ))/2 := by
  simp only [angleCos, sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_neg,
    Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem compactIntegrable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup Y] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → Y} (h : Continuous f) : Integrable f μ :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Every expanding-base cosine coordinate has zero mean on every translated coset. -/
theorem integral_angleCos {B : ℂ} (hB : B ≠ 0) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] (ω : PhaseTorus) (i : ℤ) :
    ∫ z, angleCos ((ω+z.val) i) ∂μ = 0 := by
  let F (z : complexPhaseGroup B) : ℂ := AddCircle.toCircle ((ω+z.val) i)
  have h : ∫ z, F z ∂μ = 0 := by
    simpa [F, phaseCharacter, zpow_ne_zero i hB] using integral_phaseCharacter ({i} : Finset ℤ)
      id (fun _ ↦ 1) B μ ω
  have cf : Continuous F := continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp
    ((continuous_apply i).comp (continuous_const.add continuous_subtype_val)))
  have hr := integral_re (compactIntegrable (μ := μ) cf)
  rw [h] at hr
  exact hr

/-- Two distinct times have zero cosine correlation on every coset, and a
single cosine has second moment one half. -/
theorem cosine_correlation {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] (ω : PhaseTorus) (i j : ℤ) :
    ∫ z, angleCos ((ω+z.val) i)*angleCos ((ω+z.val) j) ∂μ = if i=j then 1/2 else 0 := by
  let t : Bool → ℤ := fun b ↦ if b then i else j
  let plus (z : complexPhaseGroup B) : ℂ := AddCircle.toCircle ((ω+z.val) i + (ω+z.val) j)
  let minus (z : complexPhaseGroup B) : ℂ := AddCircle.toCircle ((ω+z.val) i - (ω+z.val) j)
  have hplus : B^i + B^j ≠ 0 := by
    intro h
    have hz := (SparseGap.two_term_relation_iff (B := B) (u := 1) (v := 1)
      hb (by simp) (by simp) i j).mp (by simpa using h)
    norm_num at hz
  have hminus : B^i - B^j = 0 ↔ i = j := by
    constructor
    · intro h
      have h := congrArg norm (sub_eq_zero.mp h)
      simp only [Complex.norm_zpow] at h
      exact (zpow_right_strictMono₀ hb).injective h
    · rintro rfl; exact sub_self _
  have Ip : ∫ z, plus z ∂μ = 0 := by
    simpa [phaseCharacter, Fintype.sum_bool, t, plus, hplus] using
      integral_phaseCharacter Finset.univ t (fun _ ↦ 1) B μ ω
  have Im : ∫ z, minus z ∂μ = if i=j then 1 else 0 := by
    have he := integral_phaseCharacter Finset.univ t (fun (b : Bool) ↦ if b then 1 else -1) B μ ω
    by_cases hij : i = j
    · subst j; simp [minus]
    · have hf : (∑ b : Bool, ((if b then 1 else -1 : ℤ) : ℂ)*B^(t b)) = B^i-B^j := by
        simp [t, sub_eq_add_neg]
      have ha (v : PhaseTorus) : phaseCharacter Finset.univ t (fun (b : Bool) ↦ if b then 1 else -1) v =
          (AddCircle.toCircle (v i-v j) : ℂ) := by simp [phaseCharacter, t, sub_eq_add_neg]
      rw [hf, if_neg (hminus.not.mpr hij)] at he
      simpa only [ha, minus, if_neg hij] using he
  have coord (k : ℤ) : Continuous (fun z : complexPhaseGroup B ↦ (ω+z.val) k) :=
    (continuous_apply k).comp (continuous_const.add continuous_subtype_val)
  have cp : Continuous plus := continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp ((coord i).add (coord j)))
  have cm : Continuous minus := continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp ((coord i).sub (coord j)))
  have pr := integral_re (compactIntegrable (μ := μ) cp)
  have mr := integral_re (compactIntegrable (μ := μ) cm)
  rw [Ip] at pr
  rw [Im] at mr
  simp only [angleCos_product, integral_div]
  change (∫ z, (plus z).re + (minus z).re ∂μ)/2 = _
  have hpr : Integrable (fun z ↦ (plus z).re) μ := compactIntegrable (Complex.continuous_re.comp cp)
  have hmr : Integrable (fun z ↦ (minus z).re) μ := compactIntegrable (Complex.continuous_re.comp cm)
  rw [integral_add hpr hmr]
  rw [show (∫ z, (plus z).re ∂μ) = 0 from pr, show (∫ z, (minus z).re ∂μ) =
    (if i=j then (1 : ℂ) else 0).re from mr]
  split_ifs <;> norm_num

/-- The square mean of any finite weighted drift block is exactly its half
square weight sum, including on translated cosets of the phase group. -/
theorem weighted_cosine_second_moment {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] (ω : PhaseTorus)
    (s : Finset ℤ) (w : ℤ → ℝ) :
    ∫ z, (∑ i ∈ s, w i * angleCos ((ω+z.val) i))^2 ∂μ = (∑ i ∈ s, (w i)^2)/2 := by
  let f (i : ℤ) (z : complexPhaseGroup B) := w i * angleCos ((ω+z.val) i)
  have cf (i : ℤ) : Continuous (f i) :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_subtype_val.comp
      (AddCircle.continuous_toCircle.comp ((continuous_apply i).comp (continuous_const.add continuous_subtype_val)))))
  have cross (i j : ℤ) : ∫ z, f i z * f j z ∂μ = if i=j then (w i)^2/2 else 0 := by
    have he (z : complexPhaseGroup B) : f i z * f j z =
        (w i*w j)*(angleCos ((ω+z.val) i)*angleCos ((ω+z.val) j)) := by dsimp [f]; ring
    simp_rw [he]
    rw [integral_const_mul, cosine_correlation hb]
    split_ifs with hij
    · subst j; ring
    · ring
  change (∫ z, (∑ i ∈ s, f i z)^2 ∂μ) = _
  simp only [sq, Finset.sum_mul, Finset.mul_sum]
  have crossInt (j i : ℤ) : Integrable (fun z ↦ f j z * f i z) μ := compactIntegrable ((cf j).mul (cf i))
  have sumInt (i : ℤ) : Integrable (fun z ↦ ∑ j ∈ s, f j z * f i z) μ :=
    integrable_finsetSum _ (fun j _ ↦ crossInt j i)
  rw [integral_finsetSum s (fun i _ ↦ sumInt i)]
  simp_rw [integral_finsetSum s (fun j _ ↦ crossInt j _), cross]
  simp [← Finset.sum_div, sq]


/-- Sign convention for the two exponentials in a cosine. -/
def fourierSign (v : Bool) : ℤ := if v then 1 else -1

/-- Pointwise Fourier expansion before averaging, for an arbitrary finite
family of angles. -/
theorem finite_cosine_power_expansion {ι : Type*} [Fintype ι] (u : ι → UnitAddCircle)
    (w : ι → ℝ) (q : ℕ) :
    ((2 : ℂ)*∑ i, (w i : ℂ)*(angleCos (u i) : ℂ))^q =
      ∑ p : Fin q → ι × Bool, (∏ a, (w (p a).1 : ℂ)) *
        (AddCircle.toCircle (∑ a, fourierSign (p a).2 • u (p a).1) : ℂ) := by
  classical
  let mode (p : ι × Bool) : ℂ := (w p.1 : ℂ)*(AddCircle.toCircle (fourierSign p.2 • u p.1) : ℂ)
  have h2 (z : UnitAddCircle) : (2 : ℂ)*(angleCos z : ℂ) =
      ∑ v : Bool, (AddCircle.toCircle ((fourierSign v) • z) : ℂ) := by
    rw [Fintype.sum_bool]
    simp only [fourierSign, if_true, Bool.false_eq_true, if_false, one_smul, neg_smul,
      AddCircle.toCircle_neg, Circle.coe_inv_eq_conj, Complex.add_conj, Complex.ofReal_mul]
    rfl
  have expand : (2 : ℂ)*∑ i, (w i : ℂ)*(angleCos (u i) : ℂ) = ∑ p, mode p := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [mode]
    rw [← Finset.mul_sum, ← h2]
    ring
  rw [expand,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mode, Finset.prod_mul_distrib]
  congr 1
  exact mFourier_eq_sum_toCircle _ (fun a ↦ u (p a).1)

/-- All moments reduce exactly to signed zero relations among the powers of the
physical multiplier. The tuple of time labels allows repetitions; the coset
factor is retained even when the relation vanishes. -/
theorem weighted_cosine_moment_expansion {ι : Type*} [Fintype ι]
    (B : ℂ) (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] (ω : PhaseTorus) (j : ι → ℤ) (w : ι → ℝ) (q : ℕ) :
    ∫ z, ((2 : ℂ) * ∑ i, (w i : ℂ) * (angleCos ((ω+z.val) (j i)) : ℂ))^q ∂μ =
      ∑ p : Fin q → ι × Bool, (∏ a, (w (p a).1 : ℂ)) *
        (if (∑ a, (fourierSign (p a).2 : ℂ)*B^(j (p a).1)) = 0 then
          phaseCharacter Finset.univ (fun a ↦ j (p a).1) (fun a ↦ fourierSign (p a).2) ω else 0) := by
  classical
  let time (p : Fin q → ι × Bool) (a : Fin q) := j (p a).1
  let sign (p : Fin q → ι × Bool) (a : Fin q) := fourierSign (p a).2
  let coef (p : Fin q → ι × Bool) := ∏ a, (w (p a).1 : ℂ)
  have expand (z : complexPhaseGroup B) :
      ((2 : ℂ) * ∑ i, (w i : ℂ) * (angleCos ((ω+z.val) (j i)) : ℂ))^q =
      ∑ p : Fin q → ι × Bool, coef p * phaseCharacter Finset.univ (time p) (sign p) (ω+z.val) :=
    finite_cosine_power_expansion (fun i ↦ (ω+z.val) (j i)) w q
  have hp (p : Fin q → ι × Bool) : Integrable (fun z : complexPhaseGroup B ↦
      coef p * phaseCharacter Finset.univ (time p) (sign p) (ω+z.val)) μ := by
    apply compactIntegrable (continuous_const.mul _)
    exact (phaseCharacter_continuous _ _ _).comp (continuous_const.add continuous_subtype_val)
  simp_rw [expand]
  rw [integral_finsetSum _ (fun p _ ↦ hp p)]
  simp only [integral_const_mul, integral_phaseCharacter, coef, time, sign]

/-- A bilaterally indexed relation is balanced when its signed coefficients
cancel separately at every exponent. -/
def balancedAtTimes {ι : Type*} (s : Finset ι) (e : ι → ℤ) (w : ι → ℂ) : Prop :=
  ∀ t : ℤ, ∑ i ∈ s, (if e i = t then w i else 0) = 0

private theorem lowest_cluster {ι : Type} [DecidableEq ι]
    (q J : ℕ) (s : Finset ι) (e : ι → ℤ) (hs : s.Nonempty) (hq : s.card ≤ q) :
    ∃ a ∈ s, ∃ lo : Finset ι, a ∈ lo ∧ lo ⊆ s ∧
      (∀ i ∈ lo, |e i - e a| ≤ (q:ℤ)*J) ∧
      ∃ k : ℤ, (∀ i ∈ lo, e i ≤ k) ∧ (∀ i ∈ s \ lo, k+(J:ℤ) ≤ e i) := by
  obtain ⟨a,ha,hmin⟩ := s.exists_min_image e hs
  let k (u : ℕ) := e a + (u:ℤ)*J
  let L (u : ℕ) := s.filter (fun i ↦ e i ≤ k u)
  have incl (u : ℕ) : L u ⊆ L (u+1) := by
    intro i hi
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr ⟨h₁,?_⟩
    change e i ≤ e a + ((u+1:ℕ):ℤ)*J
    dsimp [k] at h₂
    push_cast; linarith
  have item (u : ℕ) : a ∈ L u := by
    apply Finset.mem_filter.mpr ⟨ha,?_⟩
    dsimp [k]
    exact le_add_of_nonneg_right (by positivity)
  have existsFlat : ∃ u < q, L (u+1) = L u := by
    by_contra! nf
    have gain (u : ℕ) (hu : u ≤ q) : u+1 ≤ (L u).card := by
      induction u with
      | zero => exact Finset.card_pos.mpr ⟨a,item 0⟩
      | succ u ih =>
        have hlt : u < q := by omega
        have hp : L u ⊂ L (u+1) := Finset.ssubset_iff_subset_ne.mpr ⟨incl u, (nf u hlt).symm⟩
        have h := Finset.card_lt_card hp
        have := ih hlt.le
        omega
    have h := gain q le_rfl
    have ht : (L q).card ≤ s.card := Finset.card_filter_le ..
    omega
  obtain ⟨u,hu,hflat⟩ := existsFlat
  refine ⟨a,ha,L u,item u,Finset.filter_subset ..,?_,k u,?_,?_⟩
  · intro i hi
    obtain ⟨his,hik⟩ := Finset.mem_filter.mp hi
    rw [abs_of_nonneg (sub_nonneg.mpr (hmin i his))]
    have hbound : (u:ℤ)*J ≤ (q:ℤ)*J := by gcongr
    dsimp [k] at hik
    linarith
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    obtain ⟨his,hnot⟩ := Finset.mem_sdiff.mp hi
    rw [← hflat] at hnot
    have hnext : k (u+1) < e i := by
      by_contra! h
      exact hnot (Finset.mem_filter.mpr ⟨his,h⟩)
    dsimp [k] at hnext ⊢
    linarith

private theorem two_balanced {B : ℂ} (hb : 1 < ‖B‖) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℤ) (w : ι → ℂ) (hw : ∀ i ∈ s, w i = 1 ∨ w i = -1)
    (hs : s.card = 2) (hrel : ∑ i ∈ s, w i * B^(e i) = 0) : balancedAtTimes s e w := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs
  have ha : a ∈ ({a,b} : Finset ι) := by simp
  have hb' : b ∈ ({a,b} : Finset ι) := by simp
  have unit (i : ι) (hi : i ∈ ({a,b} : Finset ι)) : ‖w i‖ = 1 := by
    rcases hw i hi with h | h <;> simp [h]
  simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hab), Finset.sum_singleton] at hrel
  obtain ⟨he,ho⟩ := (SparseGap.two_term_relation_iff hb (unit a ha) (unit b hb') (e a) (e b)).mp hrel
  intro t
  simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hab), Finset.sum_singleton, he, ho]
  split_ifs <;> simp

/-- Each surviving order-q relation is covered by bounded clusters. An
unbalanced relation has strictly fewer than q/2 cluster centers. -/
theorem signed_relation_cluster_cover {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ R : ℕ, ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℤ) (w : ι → ℂ),
      s.card ≤ q → (∀ i ∈ s, w i = 1 ∨ w i = -1) → (∑ i ∈ s, w i*B^(e i)) = 0 →
      ∃ centers : Finset ι, centers ⊆ s ∧ (∀ i ∈ s, ∃ a ∈ centers, |e i-e a| ≤ R) ∧
        2*centers.card ≤ s.card ∧ (2*centers.card = s.card → balancedAtTimes s e w) := by
  obtain ⟨J,split⟩ := SparseGap.separated_relation_splits hb q
  refine ⟨q*J,?_⟩
  intro ι inst s e w hq hw hrel
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hs : s.Nonempty
  · obtain ⟨a,ha,lo,hal,hlo,hnear,k,hlk,hhk⟩ := lowest_cluster q J s e hs hq
    let hi := s \ lo
    have hhi : hi ⊆ s := Finset.sdiff_subset
    have heq : (∑ i ∈ lo, w i*B^(e i)) + (∑ i ∈ hi, w i*B^(e i)) = 0 := by
      rw [add_comm, Finset.sum_sdiff hlo, hrel]
    obtain ⟨hzeroL,hzeroH⟩ := split lo hi e w k ((Finset.card_le_card hlo).trans hq)
      ((Finset.card_le_card hhi).trans hq) (fun i h ↦ hw i (hlo h)) (fun i h ↦ hw i (hhi h))
      hlk hhk heq
    have atLeastTwo : 2 ≤ lo.card := by
      have hpos := Finset.card_pos.mpr ⟨a,hal⟩
      by_contra! h
      obtain ⟨i,hlo'⟩ := Finset.card_eq_one.mp (by omega : lo.card = 1)
      have hi : i ∈ lo := by simp [hlo']
      have hwi : w i ≠ 0 := by rcases hw i (hlo hi) with h|h <;> simp [h]
      have hB : B ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hb)
      rw [hlo', Finset.sum_singleton] at hzeroL
      exact (mul_ne_zero hwi (zpow_ne_zero _ hB)) hzeroL
    have hproper : hi ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hhi, by
      intro h
      have : a ∈ hi := h.symm ▸ ha
      exact (Finset.mem_sdiff.mp this).2 hal⟩
    obtain ⟨C,hC,cover,hcount,hbal⟩ :=
      ih hi hproper ((Finset.card_le_card hhi).trans hq) (fun i h ↦ hw i (hhi h)) hzeroH
    have hac : a ∉ C := by intro h; exact (Finset.mem_sdiff.mp (hC h)).2 hal
    have hcards : hi.card + lo.card = s.card := Finset.card_sdiff_add_card_eq_card hlo
    refine ⟨insert a C,Finset.insert_subset ha (hC.trans hhi),?_,?_,?_⟩
    · intro i his
      by_cases hil : i ∈ lo
      · exact ⟨a,Finset.mem_insert_self ..,by exact_mod_cast hnear i hil⟩
      · obtain ⟨c,hc,hci⟩ := cover i (Finset.mem_sdiff.mpr ⟨his,hil⟩)
        exact ⟨c,Finset.mem_insert_of_mem hc,hci⟩
    · rw [Finset.card_insert_of_notMem hac]; omega
    · rw [Finset.card_insert_of_notMem hac]
      intro he
      have left := two_balanced hb lo e w (fun i h ↦ hw i (hlo h)) (by omega) hzeroL
      have right := hbal (by omega)
      intro t
      have add : (∑ i ∈ lo, (if e i=t then w i else 0)) +
          (∑ i ∈ hi, (if e i=t then w i else 0)) =
          ∑ i ∈ s, (if e i=t then w i else 0) := by
        rw [add_comm, Finset.sum_sdiff hlo]
      rw [← add, left t, right t, add_zero]
  · have hnil : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    exact ⟨∅,by simp,by simp,by simp,by simp [balancedAtTimes]⟩


/-- Signed Fourier tuples giving genuine relations between different times.
Balanced relations are the same terms that survive for independent angles. -/
def unbalancedTuples (B : ℂ) (s : Finset ℤ) (q : ℕ) : Finset (Fin q → s × Bool) := by
  classical
  exact Finset.univ.filter (fun f ↦
    let e := fun i ↦ ((f i).1 : ℤ)
    let w := fun i ↦ (fourierSign (f i).2 : ℂ)
    (∑ i, w i * B^(e i)) = 0 ∧ ¬ balancedAtTimes Finset.univ e w)

/-- Uniform in the starting point, even for arbitrary finite time sets: at
order q, the non-independent Fourier tuples have at most floor((q−1)/2)
free indices. This gives the error order in the moment argument of §4. -/
theorem unbalanced_tuple_count {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ C : ℕ, ∀ s : Finset ℤ, (unbalancedTuples B s q).card ≤ C*(s.card+1)^((q-1)/2) := by
  classical
  obtain ⟨R, clusters⟩ := signed_relation_cluster_cover hb q
  let p := (q-1)/2
  let width := 2*(2*R+1)
  refine ⟨(p*width)^q,?_⟩
  intro s
  let base := insert (0:ℤ) s
  let W (v : ℤ) := Finset.univ.filter (fun a : s × Bool ↦ |(a.1:ℤ)-v| ≤ R)
  have hW (v : ℤ) : (W v).card ≤ width := by
    let I := Finset.Icc (v-(R:ℤ)) (v+R)
    have hsub : (W v).card ≤ (I ×ˢ (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn (fun a : s × Bool ↦ ((a.1:ℤ),a.2))
      · intro a ha
        have h := abs_le.mp (Finset.mem_filter.mp ha).2
        apply Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_univ _⟩
        change v-(R:ℤ) ≤ (a.1:ℤ) ∧ (a.1:ℤ) ≤ v+R
        omega
      · intro a _ b _ h
        change ((a.1:ℤ),a.2) = ((b.1:ℤ),b.2) at h
        exact Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2
    refine hsub.trans_eq ?_
    have hI : I.card = 2*R+1 := by rw [Int.card_Icc]; omega
    simp [hI, width, Nat.mul_comm]
  let allowed (v : Fin p → base) := Finset.univ.biUnion (fun j ↦ W (v j))
  let words (v : Fin p → base) := Fintype.piFinset (fun _ : Fin q ↦ allowed v)
  have hwords (v : Fin p → base) : (words v).card ≤ (p*width)^q := by
    have ha : (allowed v).card ≤ p*width := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin p)) (fun j ↦ W (v j)) width
          (fun j _ ↦ hW (v j))
    dsimp [words]
    rw [Fintype.card_piFinset_const]
    exact Nat.pow_le_pow_left ha q
  have subset : unbalancedTuples B s q ⊆ Finset.univ.biUnion words := by
    intro f hf
    let e (i : Fin q) := ((f i).1 : ℤ)
    let w (i : Fin q) := (fourierSign (f i).2 : ℂ)
    have hz : (∑ i, w i*B^(e i)) = 0 ∧ ¬ balancedAtTimes Finset.univ e w :=
      (Finset.mem_filter.mp hf).2
    have signs (i : Fin q) (_ : i ∈ Finset.univ) : w i = 1 ∨ w i = -1 := by
      dsimp [w, fourierSign]
      split <;> simp
    obtain ⟨c,_,cov,hc,bal⟩ := clusters Finset.univ e w (by simp) signs hz.1
    have hcard : c.card ≤ p := by
      have hne := mt bal hz.2
      simp only [Finset.card_univ, Fintype.card_fin] at hne hc
      dsimp [p]
      omega
    let emb : c ↪ Fin p := (Fintype.equivFin c).toEmbedding.trans (Fin.castLEEmb (by simpa using hcard))
    let loc (a : c) : base := ⟨e a,Finset.mem_insert_of_mem (f a).1.property⟩
    let centres : Fin p → base := Function.extend emb loc (fun _ ↦ ⟨0,Finset.mem_insert_self ..⟩)
    apply Finset.mem_biUnion.mpr ⟨centres, Finset.mem_univ _,?_⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨b,hb',he⟩ := cov i (Finset.mem_univ _)
    let a : c := ⟨b,hb'⟩
    have hext : centres (emb a) = loc a := emb.injective.extend_apply _ _ _
    apply Finset.mem_biUnion.mpr ⟨emb a, Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [hext]
    exact he
  calc
    _ ≤ (Finset.univ.biUnion words).card := Finset.card_le_card subset
    _ ≤ (Finset.univ : Finset (Fin p → base)).card * (p*width)^q :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun v _ ↦ hwords v)
    _ ≤ (p*width)^q*(s.card+1)^p := by
      rw [Nat.mul_comm]
      apply Nat.mul_le_mul_left
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      exact Nat.pow_le_pow_left (Finset.card_insert_le ..) _

private theorem balanced_sum {ι M : Type*} [AddCommGroup M] (s : Finset ι) (e n : ι → ℤ)
    (hb : balancedAtTimes s e (fun i ↦ (n i : ℂ))) (v : ℤ → M) :
    ∑ i ∈ s, n i • v (e i) = 0 := by
  classical
  have hbZ (t : ℤ) : ∑ i ∈ s, (if e i=t then n i else 0) = 0 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_sum, apply_ite, Int.cast_zero] using hb t
  calc
    _ = ∑ i ∈ s, ∑ t ∈ s.image e, if e i=t then n i • v t else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_image_of_mem e hi]
    _ = ∑ t ∈ s.image e, ∑ i ∈ s, if e i=t then n i • v t else 0 := Finset.sum_comm
    _ = ∑ t ∈ s.image e, ((∑ i ∈ s, if e i=t then n i else 0) • v t) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = 0 := by simp [hbZ]

private theorem balanced_values {ι : Type*} (s : Finset ι) (e n : ι → ℤ)
    (hb : balancedAtTimes s e (fun i ↦ (n i : ℂ))) (B : ℂ) (ω : PhaseTorus) :
    (∑ i ∈ s, (n i : ℂ)*B^(e i)) = 0 ∧ phaseCharacter s e n ω = 1 := by
  refine ⟨by simpa [zsmul_eq_mul] using balanced_sum s e n hb (fun j ↦ B^j),?_⟩
  simp [phaseCharacter, balanced_sum s e n hb ω]

/-- The moment contribution shared by the physical group and independent
uniform circle angles. Every time has as many positive as negative signs. -/
def balancedMoment (s : Finset ℤ) (w : ℤ → ℝ) (q : ℕ) : ℂ := by
  classical
  exact ∑ f : Fin q → s × Bool, if balancedAtTimes Finset.univ (fun i ↦ ((f i).1 : ℤ))
      (fun i ↦ (fourierSign (f i).2 : ℂ)) then (∏ i, (w (f i).1 : ℂ)) else 0

/-- Quantitative comparison of the actual weighted cosine moment and its
balanced part. On a block of length m, the error is O(m^floor((q−1)/2)),
uniformly in all cosets and all weights of modulus at most one. -/
theorem weighted_moment_error {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ C : ℕ, ∀ (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
      (ω : PhaseTorus) (s : Finset ℤ) (w : ℤ → ℝ), (∀ j ∈ s, |w j| ≤ 1) →
      ‖(∫ z, ((2 : ℂ)*∑ a : s, (w a : ℂ) * (angleCos ((ω+z.val) a) : ℂ))^q ∂μ) -
          balancedMoment s w q‖ ≤ C*((s.card:ℝ)+1)^((q-1)/2) := by
  classical
  obtain ⟨C,hC⟩ := unbalanced_tuple_count hb q
  refine ⟨C,?_⟩
  intro μ _ _ ω s w hw
  let e (f : Fin q → s × Bool) (i : Fin q) := ((f i).1 : ℤ)
  let n (f : Fin q → s × Bool) (i : Fin q) := fourierSign (f i).2
  let coef (f : Fin q → s × Bool) := ∏ i, (w (f i).1 : ℂ)
  let freq (f : Fin q → s × Bool) := ∑ i, (n f i : ℂ)*B^(e f i)
  let bal (f : Fin q → s × Bool) := balancedAtTimes Finset.univ (e f) (fun i ↦ (n f i : ℂ))
  let χ (f : Fin q → s × Bool) := phaseCharacter Finset.univ (e f) (n f) ω
  have formula := weighted_cosine_moment_expansion B μ ω (fun i : s ↦ (i:ℤ)) (fun i : s ↦ w i) q
  rw [formula]
  change ‖(∑ f, coef f * (if freq f=0 then χ f else 0)) - ∑ f, (if bal f then coef f else 0)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  have cost (f : Fin q → s × Bool) : ‖coef f * (if freq f=0 then χ f else 0) -
        (if bal f then coef f else 0)‖ ≤ (if f ∈ unbalancedTuples B s q then (1:ℝ) else 0) := by
    have hmem : f ∈ unbalancedTuples B s q ↔ freq f=0 ∧ ¬bal f := by
      simp only [unbalancedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    by_cases h : bal f
    · obtain ⟨hz,hχ⟩ := balanced_values Finset.univ (e f) (n f) h B ω
      change freq f = 0 at hz
      change χ f = 1 at hχ
      simp [hmem, h, hz, hχ]
    · by_cases hz : freq f = 0
      · rw [if_pos hz, if_neg h, sub_zero, if_pos (hmem.mpr ⟨hz,h⟩)]
        rw [norm_mul, show ‖χ f‖ = 1 from Circle.norm_coe _, mul_one]
        dsimp [coef]
        rw [Complex.norm_prod]
        apply Finset.prod_le_one (fun i _ ↦ norm_nonneg _)
        intro i _
        simpa using hw (f i).1 (f i).1.property
      · simp [hmem, h, hz]
  calc
    _ ≤ ∑ f, ‖coef f * (if freq f=0 then χ f else 0) - (if bal f then coef f else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f, (if f ∈ unbalancedTuples B s q then (1:ℝ) else 0) := Finset.sum_le_sum (fun f _ ↦ cost f)
    _ = ((unbalancedTuples B s q).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast hC s

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_mFourier_fullTorus {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    ∫ z : UnitAddTorus ι, UnitAddTorus.mFourier n z = if n=0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := ι))) (0 : ι → ℤ) n
  simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg, ← UnitAddTorus.mFourier_add,
    neg_zero, add_zero] at h
  simpa [eq_comm] using h


private def net {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (p : Fin q → ι × Bool) (i : ι) :=
  ∑ a, if (p a).1=i then fourierSign (p a).2 else 0

private theorem regroup {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (p : Fin q → ι × Bool) (u : ι → UnitAddCircle) :
    (∑ a, fourierSign (p a).2 • u (p a).1) = ∑ i, net p i • u i := by
  classical
  simp only [net, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem net_zero {q : ℕ} {s : Finset ℤ} (p : Fin q → s × Bool) :
    net p=0 ↔ balancedAtTimes Finset.univ (fun i ↦ ((p i).1:ℤ))
      (fun i ↦ (fourierSign (p i).2 : ℂ)) := by
  classical
  have atMem (t : s) : ((net p t : ℤ) : ℂ) =
      ∑ i, if ((p i).1:ℤ)=(t:ℤ) then (fourierSign (p i).2 : ℂ) else 0 := by
    simp only [net, Int.cast_sum, apply_ite, Int.cast_zero, Subtype.ext_iff]
  constructor
  · intro h t
    by_cases ht : t ∈ s
    · have hh := atMem ⟨t,ht⟩
      rw [h] at hh
      simpa using hh.symm
    · apply Finset.sum_eq_zero
      intro i _
      apply if_neg
      intro he
      exact ht (he ▸ (p i).1.property)
  · intro h
    funext t
    apply Int.cast_injective (α := ℂ)
    simpa only [atMem, Pi.zero_apply, Int.cast_zero] using h t

/-- The balanced polynomial is exactly the moment of independent uniform
angles, for the product probability measure on the finite coordinate torus. -/
theorem independent_cosine_moment (s : Finset ℤ) (w : ℤ → ℝ) (q : ℕ) :
    ∫ z : UnitAddTorus s, ((2 : ℂ)*∑ i : s, (w i : ℂ)*(angleCos (z i) : ℂ))^q =
      balancedMoment s w q := by
  classical
  let coef (p : Fin q → s × Bool) := ∏ a, (w (p a).1 : ℂ)
  have hf (z : UnitAddTorus s) : ((2 : ℂ)*∑ i : s, (w i : ℂ)*(angleCos (z i) : ℂ))^q =
      ∑ p : Fin q → s × Bool, coef p * UnitAddTorus.mFourier (net p) z := by
    rw [finite_cosine_power_expansion]
    apply Finset.sum_congr rfl
    intro p _
    rw [mFourier_eq_sum_toCircle, regroup]
  have hi (p : Fin q → s × Bool) :
      Integrable (fun z : UnitAddTorus s ↦ coef p * UnitAddTorus.mFourier (net p) z) :=
    (continuous_const.mul (UnitAddTorus.mFourier (net p)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hf]
  rw [integral_finsetSum _ (fun p _ ↦ hi p)]
  simp only [integral_const_mul, integral_mFourier_fullTorus, net_zero, balancedMoment, coef]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> simp

open ProbabilityTheory
open scoped NNReal

private def multiplicity {ι : Type*} [DecidableEq ι] {q : ℕ} (f : Fin q → ι) (x : ι) : ℕ :=
  (Finset.univ.filter (fun a ↦ f a = x)).card

private theorem small_image_count {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    (Finset.univ.filter (fun f : Fin q → ι ↦ (Finset.univ.image f).card ≤ p)).card ≤
      (Fintype.card ι + 1)^p * p^q := by
  classical
  let allowed (c : Fin p → Option ι) := Finset.univ.filter (fun x : ι ↦ ∃ i, c i = some x)
  let words (c : Fin p → Option ι) := Fintype.piFinset (fun _ : Fin q ↦ allowed c)
  have counts (c : Fin p → Option ι) : (allowed c).card ≤ p := by
    calc
      _ ≤ (Finset.univ.image c).card := by
        apply Finset.card_le_card_of_injOn some
        · intro x hx
          obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hx).2
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
        · exact (Option.some_injective ι).injOn
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = _ := by simp
  have sub : (Finset.univ.filter (fun f : Fin q → ι ↦ (Finset.univ.image f).card ≤ p)) ⊆
      Finset.univ.biUnion words := by
    intro f hf
    let vals := Finset.univ.image f
    have hcard : vals.card ≤ p := (Finset.mem_filter.mp hf).2
    let emb : vals ↪ Fin p := (Fintype.equivFin vals).toEmbedding.trans (Fin.castLEEmb (by simpa using hcard))
    let g (v : vals) := some v.val
    let c := Function.extend emb g (fun _ ↦ none)
    apply Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,?_⟩
    apply Fintype.mem_piFinset.mpr
    intro a
    let v : vals := ⟨f a, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,emb v,emb.injective.extend_apply _ _ _⟩
  apply (Finset.card_le_card sub).trans
  calc
    _ ≤ (Finset.univ : Finset (Fin p → Option ι)).card * p^q := by
      apply Finset.card_biUnion_le_card_mul
      intro c _
      exact (Fintype.card_piFinset_const (allowed c) q).le.trans (Nat.pow_le_pow_left (counts c) q)
    _ = _ := by simp

private theorem sparse_or_simple {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (f : Fin q → ι) :
    (∃ x, multiplicity f x=1) ∨ (∀ x, multiplicity f x=0 ∨ multiplicity f x=2) ∨
    (Finset.univ.image f).card ≤ (q-1)/2 := by
  classical
  by_cases one : ∃ x, multiplicity f x = 1
  · exact Or.inl one
  right
  by_cases two : ∀ x, multiplicity f x=0 ∨ multiplicity f x=2
  · exact Or.inl two
  right
  push Not at one two
  obtain ⟨a,hzero,htwo⟩ := two
  let vals := Finset.univ.image f
  have hpos (x : ι) : 0 < multiplicity f x ↔ x ∈ vals := by
    rw [multiplicity,Finset.card_pos]
    simp [vals, Finset.Nonempty]
  have hm (x : ι) (hx : x ∈ vals) : 2 ≤ multiplicity f x := by
    have h := (hpos x).mpr hx
    have := one x
    omega
  have ha := (hpos a).mp (Nat.pos_of_ne_zero hzero)
  have hmass : (∑ x ∈ vals, multiplicity f x) = q := by
    simpa only [multiplicity, vals, Finset.card_univ,Fintype.card_fin] using
      (Finset.card_eq_sum_card_image f Finset.univ).symm
  have hlt : (∑ _ ∈ vals, 2) < ∑ x ∈ vals, multiplicity f x := by
    apply Finset.sum_lt_sum (by exact hm)
    exact ⟨a,ha,by have := hm a ha; omega⟩
  simp only [Finset.sum_const, nsmul_eq_mul, hmass] at hlt
  change vals.card * 2 < q at hlt
  change vals.card ≤ _
  omega

private def independentMoment {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (m : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ f : Fin q → ι, (∏ a, w (f a)) * ∏ i, m (multiplicity f i)

private theorem compare_independent_moments {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) (a b : ℕ → ℝ) (H : ℝ) (hH : 1 ≤ H)
    (ha : ∀ r ≤ q, |a r| ≤ H^r) (hb : ∀ r ≤ q, |b r| ≤ H^r)
    (hzero : a 0 = b 0) (h1a : a 1=0) (h1b : b 1=0) (h2 : a 2=b 2) :
    |independentMoment w a q-independentMoment w b q| ≤
      (2*H^q)*(((q-1)/2:ℕ):ℝ)^q*(Fintype.card ι+1 : ℝ)^((q-1)/2) := by
  classical
  let p := (q-1)/2
  let term (c : ℕ → ℝ) (f : Fin q → ι) := (∏ i, w (f i)) * ∏ x, c (multiplicity f x)
  have absTerm (c : ℕ → ℝ) (hc : ∀ r ≤ q, |c r| ≤ H^r) (f : Fin q → ι) : |term c f| ≤ H^q := by
    have hsum : (∑ x, multiplicity f x) = q := by
      simpa only [multiplicity, Finset.card_univ, Fintype.card_fin] using
        (Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (s := Finset.univ)
          (f := f) (fun _ _ ↦ Finset.mem_univ _)).symm
    dsimp only [term]
    rw [abs_mul,Finset.abs_prod,Finset.abs_prod]
    apply (mul_le_mul (Finset.prod_le_one (fun i _ ↦ abs_nonneg _) (fun i _ ↦ hw (f i)))
      (Finset.prod_le_prod (fun x _ ↦ abs_nonneg _) (fun x _ ↦ hc _ (by
        simpa only [multiplicity, Finset.card_univ, Fintype.card_fin] using Finset.card_filter_le Finset.univ (fun j ↦ f j=x))))
      (Finset.prod_nonneg (fun x _ ↦ abs_nonneg _)) zero_le_one).trans_eq
    rw [one_mul, Finset.prod_pow_eq_pow_sum, hsum]
  let bad := Finset.univ.filter (fun f : Fin q → ι ↦ (Finset.univ.image f).card ≤ p)
  have per (f : Fin q → ι) : |term a f-term b f| ≤ if f ∈ bad then 2*H^q else 0 := by
    by_cases hf : f ∈ bad
    · rw [if_pos hf]
      exact (abs_sub _ _).trans (by linarith [absTerm a ha f,absTerm b hb f])
    rw [if_neg hf]
    have heq : term a f = term b f := by
      rcases sparse_or_simple f with ⟨x,hx⟩ | hh | h
      · have za : (∏ i, a (multiplicity f i))=0 := Finset.prod_eq_zero (Finset.mem_univ x) (by rw [hx,h1a])
        have zb : (∏ i, b (multiplicity f i))=0 := Finset.prod_eq_zero (Finset.mem_univ x) (by rw [hx,h1b])
        simp [term,za,zb]
      · dsimp only [term]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        rcases hh i with h|h
        · rwa [h]
        · rwa [h]
      · exact False.elim (hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    simp [heq]
  change |(∑ f,term a f)-(∑ f,term b f)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ f, |term a f-term b f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f, (if f ∈ bad then 2*H^q else 0) := Finset.sum_le_sum (fun f _ ↦ per f)
    _ = bad.card*(2*H^q) := by simp
    _ ≤ ((Fintype.card ι:ℝ)+1)^p * (p:ℝ)^q * (2*H^q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast small_image_count (ι := ι) p q
    _ = _ := by dsimp [p]; ring



private theorem integral_independent_power {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (X : E → ℝ)
    (hX : ∀ k : ℕ, Integrable (fun x ↦ X x ^ k) μ) (w : ι → ℝ) (q : ℕ) :
    (∫ z : ι → E, (∑ i, w i * X (z i))^q ∂Measure.pi (fun _ ↦ μ)) =
      independentMoment w (fun k ↦ ∫ x, (X x)^k ∂μ) q := by
  classical
  have regroup (f : Fin q → ι) (z : ι → E) : (∏ a, w (f a)*X (z (f a))) =
      (∏ a,w (f a))*∏ i, (X (z i))^(multiplicity f i) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    simpa [multiplicity] using (Finset.prod_fiberwise' Finset.univ f (fun i ↦ X (z i))).symm
  have hi (f : Fin q → ι) : Integrable
      (fun z : ι → E ↦ (∏ a,w (f a))*∏ i, (X (z i))^(multiplicity f i)) (Measure.pi (fun _ ↦ μ)) :=
    (Integrable.fintype_prod (fun i ↦ hX (multiplicity f i))).const_mul _
  simp_rw [Fintype.sum_pow, regroup]
  rw [integral_finsetSum _ (fun f _ ↦ hi f)]
  simp only [integral_const_mul, independentMoment]
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  exact integral_fintype_prod_eq_prod (fun i x ↦ (X x)^(multiplicity f i))

private def cosineMoment (k : ℕ) : ℝ := ∫ z : UnitAddCircle, (2*angleCos z)^k ∂AddCircle.haarAddCircle
private def gaussianMoment (k : ℕ) : ℝ := ∫ x, x^k ∂gaussianReal 0 2

private theorem circle_exp_integral {n : ℤ} (hn : n ≠ 0) :
    ∫ z : UnitAddCircle, (AddCircle.toCircle (n • z) : ℂ) ∂AddCircle.haarAddCircle = 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) 0 n
  simp only [ContinuousMap.inner_toLp, ← fourier_neg, ← fourier_add, neg_zero, add_zero,
    if_neg hn.symm] at h
  exact h

private theorem circle_cos_integral {n : ℤ} (hn : n ≠ 0) :
    ∫ z : UnitAddCircle, angleCos (n • z) ∂AddCircle.haarAddCircle = 0 := by
  let F (z : UnitAddCircle) : ℂ := AddCircle.toCircle (n • z)
  have h : Continuous F := by unfold F; fun_prop
  have hi : Integrable F AddCircle.haarAddCircle := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hi
  rw [show (∫ z, F z ∂AddCircle.haarAddCircle)=0 from circle_exp_integral hn] at hre
  exact hre

private theorem cosineMoment_two : cosineMoment 2 = 2 := by
  have formula (z : UnitAddCircle) : (2*angleCos z)^2 = 2*angleCos ((2:ℤ) • z) + 2 := by
    have hz := Circle.normSq_coe (AddCircle.toCircle z)
    rw [Complex.normSq_apply] at hz
    simp only [angleCos, two_zsmul, AddCircle.toCircle_add, Circle.coe_mul, Complex.mul_re]
    nlinarith
  have hc : Continuous (fun z : UnitAddCircle ↦ 2*angleCos ((2:ℤ) • z)) := by unfold angleCos; fun_prop
  unfold cosineMoment
  simp_rw [formula]
  rw [integral_add (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _),
      integral_const_mul, circle_cos_integral (by decide : (2:ℤ)≠0)]
  simp

private theorem gaussianMoment_two : gaussianMoment 2 = 2 := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 2)
  rw [variance_eq_integral (by fun_prop)] at hv
  simpa [gaussianMoment, integral_id_gaussianReal] using hv

private theorem gaussian_integrable_pow (q : ℕ) (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x^q) (gaussianReal 0 v) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := id) (by simp) q

/-- Replacing finitely many independent cosine coordinates by independent
centered Gaussian coordinates of the same variance changes only lower-order
moments. The bound holds for signed weights, uniformly in the index type. -/
theorem independent_gaussian_moment_comparison (q : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ), (∀ i, |w i| ≤ 1) →
      |(∫ z : ι → UnitAddCircle, (∑ i, w i*(2*angleCos (z i)))^q
        ∂Measure.pi (fun _ ↦ AddCircle.haarAddCircle)) -
      (∫ x : ι → ℝ, (∑ i, w i*x i)^q ∂Measure.pi (fun _ ↦ gaussianReal 0 2))| ≤
        C*(Fintype.card ι+1 : ℝ)^((q-1)/2) := by
  let H := 1 + ∑ r ∈ Finset.range (q+1), (|cosineMoment r| + |gaussianMoment r|)
  have hH : 1 ≤ H := by dsimp [H]; exact le_add_of_nonneg_right (by positivity)
  have cz : cosineMoment 0=1 := by simp [cosineMoment]
  have gz : gaussianMoment 0=1 := by simp [gaussianMoment]
  have c1 : cosineMoment 1=0 := by
    have h := circle_cos_integral (by decide : (1:ℤ)≠0)
    simp only [one_smul] at h
    simp [cosineMoment,integral_const_mul,h]
  have g1 : gaussianMoment 1=0 := by simp [gaussianMoment, integral_id_gaussianReal]
  have bounds (r : ℕ) (hr : r ≤ q) : |cosineMoment r| ≤ H^r ∧ |gaussianMoment r| ≤ H^r := by
    by_cases h0 : r=0
    · simp [h0,cz,gz]
    have hs := Finset.single_le_sum (f := fun k ↦ |cosineMoment k| + |gaussianMoment k|)
      (fun k _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
    have hpow : H ≤ H^r := le_self_pow₀ hH h0
    dsimp [H] at hpow
    constructor <;> linarith [abs_nonneg (cosineMoment r),abs_nonneg (gaussianMoment r)]
  let C := (2*H^q)*(((q-1)/2:ℕ):ℝ)^q
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ _ w hw
  have hc (n : ℕ) : Integrable (fun θ : UnitAddCircle ↦ (2*angleCos θ)^n) AddCircle.haarAddCircle :=
    (show Continuous (fun θ : UnitAddCircle ↦ (2*angleCos θ)^n) by unfold angleCos; fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_independent_power AddCircle.haarAddCircle _ hc w q,
    integral_independent_power (gaussianReal 0 2) (fun x : ℝ ↦ x) (fun k ↦ gaussian_integrable_pow k 2) w q]
  exact compare_independent_moments q w hw cosineMoment gaussianMoment H hH (fun r hr ↦ (bounds r hr).1)
    (fun r hr ↦ (bounds r hr).2) (cz.trans gz.symm) c1 g1 (cosineMoment_two.trans gaussianMoment_two.symm)



private theorem gaussian_weighted_unit {ι : Type*} [Fintype ι] (v : ι → ℝ) (h : 2*∑ i, v i^2=1) :
    (Measure.pi (fun _ : ι ↦ gaussianReal 0 2)).map (fun x ↦ ∑ i, v i*x i) = gaussianReal 0 1 := by
  classical
  let P := Measure.pi (fun _ : ι ↦ gaussianReal 0 2)
  let S (x : ι → ℝ) := ∑ i, v i*x i
  have hSm : Measurable S := by dsimp [S]; fun_prop
  let _ : IsProbabilityMeasure (P.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real, integral_map hSm.aemeasurable (by fun_prop)]
  have he (x : ι → ℝ) : Complex.exp ((t:ℂ) * ((∑ i, v i*x i : ℝ):ℂ) * Complex.I) =
      ∏ i, Complex.exp (((t*(v i) : ℝ):ℂ)*(x i : ℂ)*Complex.I) := by
    rw [← Complex.exp_sum, Complex.ofReal_sum]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∫ x : ι → ℝ, Complex.exp ((t:ℂ) * ((∑ i, v i*x i : ℝ):ℂ)*Complex.I) ∂P) = _
  simp_rw [he]
  dsimp only [P]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) ↦ Complex.exp (((t*(v i) : ℝ):ℂ)*(x:ℂ)*Complex.I))]
  have G (i : ι) : (∫ x, Complex.exp (((t*(v i) : ℝ):ℂ)*(x:ℂ)*Complex.I) ∂gaussianReal 0 2) =
      Complex.exp (-((t:ℂ)^2 * (v i:ℂ)^2)) := by
    rw [← charFun_apply_real, charFun_gaussianReal]; push_cast; ring_nf
  simp_rw [G]
  rw [← Complex.exp_sum, charFun_gaussianReal]
  congr 1
  have hc : (2:ℂ) * ∑ i, (v i:ℂ)^2 = 1 := by exact_mod_cast h
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  push_cast
  linear_combination -((t:ℂ)^2/2)*hc

private theorem independent_gaussian_normalize {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (σ : ℝ) (hσ : σ ≠ 0) (hvar : 2*∑ i, v i^2=σ^2) (q : ℕ) :
    (∫ x : ι → ℝ, (∑ i, v i*x i)^q ∂Measure.pi (fun _ ↦ gaussianReal 0 2)) =
      σ^q * ∫ x, x^q ∂gaussianReal 0 1 := by
  have hnorm : 2*∑ i, (v i/σ)^2 = 1 := by
    simp only [div_pow, ← Finset.sum_div]
    field_simp
    exact hvar
  have law := gaussian_weighted_unit (fun i ↦ v i/σ) hnorm
  have hm : Measurable (fun x : ι → ℝ ↦ ∑ i, v i/σ*x i) := by fun_prop
  rw [← law, integral_map hm.aemeasurable (by fun_prop), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_pow, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  field_simp




/-- Twice the cosine drift on a finite block, with arbitrary real weights. -/
def driftBlock (B : ℂ) (ω : PhaseTorus) (s : Finset ℤ) (w : ℤ → ℝ) (z : complexPhaseGroup B) : ℝ :=
  ∑ i : s, w i*(2*angleCos ((ω+z.val) i))

private theorem continuous_driftBlock (B : ℂ) (ω : PhaseTorus) (s : Finset ℤ) (w : ℤ → ℝ) :
    Continuous (driftBlock B ω s w) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_const.mul (Complex.continuous_re.comp
    (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp
      ((continuous_apply (i : ℤ)).comp (continuous_const.add continuous_subtype_val))))))

private theorem complexify_block {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : ι → ℝ) (θ : Ω → ι → UnitAddCircle) (q : ℕ) :
    (∫ z, ((2:ℂ)*∑ i, (w i:ℂ)*(angleCos (θ z i):ℂ))^q ∂μ) =
      ((∫ z, (∑ i, w i*(2*angleCos (θ z i)))^q ∂μ : ℝ):ℂ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with z
  push_cast
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Quantitative Gaussian-moment approximation for a physical cosine block, on
its original probability space. The variance of this doubled drift is σ². -/
theorem physical_gaussian_moment_error {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
        (ω : PhaseTorus) (s : Finset ℤ) (w : ℤ → ℝ), (∀ i ∈ s, |w i| ≤ 1) →
        ∀ σ : ℝ, 0 < σ → 2*(∑ i : s, w i^2)=σ^2 →
        |(∫ z, driftBlock B ω s w z^q ∂μ) - σ^q*(∫ x, x^q ∂gaussianReal 0 1)| ≤
          C*((s.card:ℝ)+1)^((q-1)/2) := by
  obtain ⟨A,hA⟩ := weighted_moment_error hb q
  obtain ⟨C,hC,hcmp⟩ := independent_gaussian_moment_comparison q
  refine ⟨A+C,by positivity,?_⟩
  intro μ _ _ ω s w hw σ hσ hvar
  let P := Measure.pi (fun _ : s ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
  let I := ∫ z : s → UnitAddCircle, (∑ i : s, w i*(2*angleCos (z i)))^q ∂P
  let G := ∫ x : s → ℝ, (∑ i : s, w i*x i)^q ∂Measure.pi (fun _ ↦ gaussianReal 0 2)
  have H₁ : |(∫ z, driftBlock B ω s w z^q ∂μ)-I| ≤ A*((s.card:ℝ)+1)^((q-1)/2) := by
    have h := hA μ ω s w hw
    have model : balancedMoment s w q = (I : ℂ) := by
      rw [← independent_cosine_moment]
      exact complexify_block P (fun i : s ↦ w i) (fun z i ↦ z i) q
    rw [model, complexify_block μ (fun i : s ↦ w i) (fun z i ↦ (ω+z.val) i) q,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have H₂ : |I-G| ≤ C*((s.card:ℝ)+1)^((q-1)/2) := by
    simpa only [Fintype.card_coe] using hcmp (fun i : s ↦ w i) (fun i ↦ hw i i.property)
  have Gval : G = σ^q*(∫ x, x^q ∂gaussianReal 0 1) :=
    independent_gaussian_normalize (fun i : s ↦ w i) σ hσ.ne' hvar q
  rw [← Gval, add_mul]
  exact (abs_sub_le _ I _).trans (add_le_add H₁ H₂)

/-- Moment convergence for any sequence of critical drift blocks whose
variances diverge and grow at least proportionally to the lengths. -/
theorem normalized_drift_moments {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    (ω : ℕ → PhaseTorus) (s : ℕ → Finset ℤ) (w : ℕ → ℤ → ℝ) (σ : ℕ → ℝ)
    (hw : ∀ n i, i ∈ s n → |w n i| ≤ 1) (hσ : ∀ n, 0 < σ n)
    (hvar : ∀ n, 2*(∑ i : s n, w n i^2)=(σ n)^2) (hlim : Tendsto σ atTop atTop)
    {K : ℝ} (hK : 0 < K) (hsize : ∀ n, ((s n).card:ℝ)+1 ≤ K*(σ n)^2) (q : ℕ) :
    Tendsto (fun n ↦ ∫ z, (driftBlock B (ω n) (s n) (w n) z / σ n)^q ∂μ) atTop
      (𝓝 (∫ x, x^q ∂gaussianReal 0 1)) := by
  by_cases hq : q=0
  · subst q; simp
  obtain ⟨C,hC,hbound⟩ := physical_gaussian_moment_error hb q
  let p := (q-1)/2
  let M := ∫ x, x^q ∂gaussianReal 0 1
  have hbnd : ∀ᶠ n : ℕ in atTop, |(∫ z, (driftBlock B (ω n) (s n) (w n) z / σ n)^q ∂μ)-M|
      ≤ (C*K^p) / σ n := by
    filter_upwards [hlim.eventually_ge_atTop 1] with n hlarge
    have hs := hσ n
    have err := hbound μ (ω n) (s n) (w n) (hw n) (σ n) hs (hvar n)
    let F (z : complexPhaseGroup B) := driftBlock B (ω n) (s n) (w n) z
    have H : |(∫ z, F z^q ∂μ)-(σ n)^q*M| ≤ C*(((s n).card:ℝ)+1)^p := err
    change |(∫ z, (F z/σ n)^q ∂μ)-M| ≤ _
    simp_rw [div_pow]
    rw [integral_div, show (∫ z, F z^q ∂μ)/(σ n)^q-M =
        ((∫ z, F z^q ∂μ)-(σ n)^q*M)/(σ n)^q by field_simp, abs_div, abs_of_pos (pow_pos hs _),
      div_le_div_iff₀ (pow_pos hs _) hs]
    calc
      _ ≤ (C*(((s n).card:ℝ)+1)^p)*σ n :=
        mul_le_mul_of_nonneg_right H hs.le
      _ ≤ (C*(K*(σ n)^2)^p)*σ n := by gcongr; exact hsize n
      _ = (C*K^p)*(σ n)^(2*p+1) := by rw [mul_pow, ← pow_mul, pow_succ]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_right₀ hlarge
        dsimp [p]; omega
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have invlim := Filter.Tendsto.inv_tendsto_atTop hlim
  have lim : Tendsto (fun n ↦ (C*K^p) / σ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := C*K^p)).mul invlim
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) hbnd lim



/-- Uniform critical drift anticoncentration (RC3). The input may be an
arbitrary finite subset of signed times. For interval blocks, the square-sum
hypothesis is exactly the lower bound supplied by (RC1); the fixed factor two
in the drift can be absorbed into the target radius and center. -/
theorem critical_drift_anticoncentration {B : ℂ} (hb : 1 < ‖B‖)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    {η : ℝ} (hη : 0 < η) (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (s : Finset ℤ) (w : ℤ → ℝ) (ω : PhaseTorus) (a : ℝ), N ≤ s.card →
      (∀ i ∈ s, |w i| ≤ 1) → η*s.card ≤ ∑ i : s, (w i)^2 →
      μ.real {z | |driftBlock B ω s w z - a| ≤ D} < ε := by
  classical
  by_contra! h
  choose s w ω a hn hw hmass hbad using fun n : ℕ ↦ h (n+1)
  let σ (n : ℕ) := Real.sqrt (2*∑ i : s n, (w n i)^2)
  have hcard (n : ℕ) : (n:ℝ)+1 ≤ ((s n).card:ℝ) := by exact_mod_cast hn n
  have hpos (n : ℕ) : 0 < σ n := by
    apply Real.sqrt_pos.mpr
    have hnpos : 0 < ((s n).card:ℝ) := by linarith [hcard n, Nat.cast_nonneg (α := ℝ) n]
    linarith [mul_pos hη hnpos, hmass n]
  have hvar (n : ℕ) : 2*(∑ i : s n, (w n i)^2) = (σ n)^2 := (Real.sq_sqrt (by positivity)).symm
  have lim : Tendsto σ atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop.const_mul_atTop hη)
    intro n
    have hh : η*(n:ℝ) ≤ η*((s n).card:ℝ) := by gcongr; exact (Nat.le_succ n).trans (hn n)
    linarith [hmass n, mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) (s n).card)]
  have budget (n : ℕ) : ((s n).card:ℝ)+1 ≤ η⁻¹*(σ n)^2 := by
    rw [← hvar, inv_mul_eq_div, le_div_iff₀ hη]
    have h1 : (1:ℝ) ≤ (s n).card := by linarith [hcard n, Nat.cast_nonneg (α := ℝ) n]
    have hηn := mul_le_mul_of_nonneg_left h1 hη.le
    nlinarith only [hηn, hmass n]
  let F (n : ℕ) (z : complexPhaseGroup B) := driftBlock B (ω n) (s n) (w n) z/σ n
  have cf (n : ℕ) : Continuous (F n) := (continuous_driftBlock _ _ _ _).div_const _
  let ν (n : ℕ) : ProbabilityMeasure ℝ :=
    ⟨μ.map (F n), Measure.isProbabilityMeasure_map (cf n).measurable.aemeasurable⟩
  have finite (n k : ℕ) : Integrable (fun x : ℝ ↦ x^k) (ν n : Measure ℝ) := by
    apply (integrable_map_measure (by fun_prop) (cf n).measurable.aemeasurable).mpr
    exact ((cf n).pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have mom (k : ℕ) : Tendsto (fun n ↦ ∫ x : ℝ, x^k ∂(ν n : Measure ℝ)) atTop
      (𝓝 (∫ x, x^k ∂gaussianReal 0 1)) := by
    have eq (n : ℕ) : (∫ x : ℝ, x^k ∂(ν n : Measure ℝ)) = ∫ z, (F n z)^k ∂μ :=
      integral_map (cf n).measurable.aemeasurable (by fun_prop)
    simp_rw [eq]
    exact normalized_drift_moments hb μ ω s w σ hw hpos hvar lim (inv_pos.mpr hη) budget k
  have small : Tendsto (fun n ↦ D/σ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := D)).mul lim.inv_tendsto_atTop
  obtain ⟨n,hn'⟩ := (shrinking_band_of_gaussian_moments ν finite mom small ε hε).exists
  have hbound := hn' (a n/σ n)
  change (μ.map (F n)).real (Icc (a n/σ n-D/σ n) (a n/σ n+D/σ n)) < ε at hbound
  rw [measureReal_def, Measure.map_apply (cf n).measurable measurableSet_Icc] at hbound
  have hset : (F n) ⁻¹' Icc (a n/σ n-D/σ n) (a n/σ n+D/σ n) =
      {z | |driftBlock B (ω n) (s n) (w n) z - a n| ≤ D} := by
    ext z
    change (a n/σ n-D/σ n ≤ driftBlock B (ω n) (s n) (w n) z/σ n ∧
      driftBlock B (ω n) (s n) (w n) z/σ n ≤ a n/σ n+D/σ n) ↔ _
    rw [← sub_div, ← add_div, div_le_div_iff_of_pos_right (hpos n), div_le_div_iff_of_pos_right (hpos n)]
    change _ ↔ |driftBlock B (ω n) (s n) (w n) z - a n| ≤ D
    rw [abs_le]; constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [hset] at hbound
  exact (not_lt_of_ge (hbad n)) hbound

end CriticalRay
end Weierstrass
