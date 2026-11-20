module

public import Weierstrass.StripFamily

/-! # Retaining good sampled centers at a finite family of meshes -/

@[expose] public noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace Weierstrass.StripProof

/-- Finite simultaneous retention, before either the physical or direction measures
are pushed forward. -/
def retain {X : Type*} {ι : Type*} (J : Finset ι) (bad : ι → Set X) : Set X :=
  (⋃ j ∈ J, bad j)ᶜ

theorem measurable_retain {X ι : Type*} [MeasurableSpace X] (J : Finset ι) {bad : ι → Set X}
    (hm : ∀ j ∈ J, MeasurableSet (bad j)) : MeasurableSet (retain J bad) :=
  (J.finite_toSet.measurableSet_biUnion hm).compl

theorem retained_mass_loss {X ι : Type*} [MeasurableSpace X] (κ : Measure X) [IsFiniteMeasure κ]
    (J : Finset ι) {bad : ι → Set X} (hm : ∀ j ∈ J, MeasurableSet (bad j)) :
    κ.real univ-(κ.restrict (retain J bad)).real univ ≤ ∑ j ∈ J, κ.real (bad j) := by
  have m : MeasurableSet (⋃ j ∈ J, bad j) := J.finite_toSet.measurableSet_biUnion hm
  rw [measureReal_restrict_apply_univ,retain,measureReal_compl m]
  simpa using measureReal_biUnion_finset_le (μ := κ) J bad

private theorem retained_test {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Measure X) [IsFiniteMeasure κ] {f : X → Y} (hf : Measurable f) (U : Set X)
    {target : Set Y} (mt : MeasurableSet target) (ball : X → Set X) {a : ℝ}
    (ha : 0 ≤ a) (good : ∀ x ∈ U, κ.real (ball x) ≤ a)
    (close : ∀ x y, f x ∈ target → f y ∈ target → y ∈ ball x) :
    ((κ.restrict U).map f).real target ≤ a := by
  rw [map_measureReal_apply hf mt,measureReal_restrict_apply (mt.preimage hf)]
  by_cases ne : (f ⁻¹' target ∩ U).Nonempty
  · obtain ⟨x,ht,hu⟩ := ne
    exact (measureReal_mono (s₂ := ball x) (fun y hy => close x y ht hy.1)).trans (good x hu)
  · simpa [Set.not_nonempty_iff_eq_empty.mp ne] using ha

/-- Retained direction subprobability satisfies B3 at every target, including those
whose centers do not themselves belong to the retained directions. -/
theorem retained_direction_bound (κ : Measure ℝ) [IsFiniteMeasure κ] {f : ℝ → ℝ}
    (hf : Measurable f) (U : Set ℝ) {l a : ℝ} (hl : 0 ≤ l) (ha : 0 ≤ a)
    (good : ∀ u ∈ U, κ.real {v | |f v - f u| ≤ 2*l} ≤ a) (x : ℝ) :
    ((κ.restrict U).map f).real (Icc x (x+l)) ≤ a := by
  apply retained_test κ hf U measurableSet_Icc _ ha good
  intro u v h1 h2
  change |f v - f u| ≤ 2*l
  exact abs_le.mpr ⟨by linarith [h1.1,h1.2,h2.1,h2.2],by linarith [h1.1,h1.2,h2.1,h2.2]⟩

/-- Physical input whose frozen output belongs to a half-open height strip. -/
def heightStrip (Y : ℝ → ℝ) (Δ : ℝ) (i : ℤ) : Set ℝ := Y ⁻¹' Ico (i*Δ) ((i+1)*Δ)

/-- The affine planar coordinates of physical input on a height strip. -/
def stripPoint (Y : ℝ → ℝ) (Δ : ℝ) (i : ℤ) (x : ℝ) : Plane := (x,(Y x-i*Δ)/Δ)

theorem measurable_stripPoint {Y : ℝ → ℝ} (mY : Measurable Y) (Δ : ℝ) (i : ℤ) :
    Measurable (stripPoint Y Δ i) := measurable_id.prodMk ((mY.sub_const _).div_const _)

def stripLaw (κ : Measure ℝ) (Q : Set ℝ) (Y : ℝ → ℝ) (Δ : ℝ) (i : ℤ) : Measure Plane :=
  (κ.restrict (Q ∩ heightStrip Y Δ i)).map (stripPoint Y Δ i)

instance (κ : Measure ℝ) [IsFiniteMeasure κ] (Q : Set ℝ) (Y : ℝ → ℝ) (Δ : ℝ) (i : ℤ) :
    IsFiniteMeasure (stripLaw κ Q Y Δ i) := by unfold stripLaw; infer_instance

/-- A retained centered physical test implies the complete B4 planar square bound. -/
theorem retained_physical_bound (κ : Measure ℝ) [IsFiniteMeasure κ] {Y : ℝ → ℝ}
    (mY : Measurable Y) (Q : Set ℝ) {Δ l a : ℝ} (hΔ : 0 < Δ) (ha : 0 ≤ a)
    (good : ∀ x ∈ Q, κ.real {y | |y-x| ≤ 2*l ∧ |Y y-Y x| ≤ 2*Δ*l} ≤ a)
    (i : ℤ) (z : Plane) : (stripLaw κ Q Y Δ i).real (box z l) ≤ a := by
  apply retained_test κ (measurable_stripPoint mY _ _) _ (measurable_box _ _) _ ha
    (fun x hx => good x hx.1)
  intro x y hx hy
  rcases hx with ⟨⟨x1,x2⟩,x3,x4⟩
  rcases hy with ⟨⟨y1,y2⟩,y3,y4⟩
  change z.1-l ≤ x at x1; change x ≤ z.1+l at x2
  change z.1-l ≤ y at y1; change y ≤ z.1+l at y2
  change z.2-l ≤ (Y x-i*Δ)/Δ at x3; change (Y x-i*Δ)/Δ ≤ z.2+l at x4
  change z.2-l ≤ (Y y-i*Δ)/Δ at y3; change (Y y-i*Δ)/Δ ≤ z.2+l at y4
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by nlinarith [(le_div_iff₀ hΔ).mp y3,(div_le_iff₀ hΔ).mp x4],
      by nlinarith [(le_div_iff₀ hΔ).mp x3,(div_le_iff₀ hΔ).mp y4]⟩⟩

/-- The zeroth-scale centered ordinate test controls the mass of each retained strip. -/
theorem retained_strip_mass (κ : Measure ℝ) [IsFiniteMeasure κ] {Y : ℝ → ℝ} (mY : Measurable Y)
    (Q : Set ℝ) {Δ a : ℝ} (ha : 0 ≤ a)
    (good : ∀ x ∈ Q, κ.real {y | |Y y-Y x| ≤ Δ} ≤ a) (i : ℤ) :
    (stripLaw κ Q Y Δ i).real univ ≤ a := by
  rw [stripLaw,map_measureReal_apply (measurable_stripPoint mY _ _) MeasurableSet.univ,
    preimage_univ,measureReal_restrict_apply_univ]
  by_cases ne : (Q ∩ heightStrip Y Δ i).Nonempty
  · obtain ⟨x,hx,lo,hi⟩ := ne
    apply (measureReal_mono ?_).trans (good x hx)
    rintro y ⟨_,lo',hi'⟩
    change (i:ℝ)*Δ ≤ Y x at lo; change Y x < ((i:ℝ)+1)*Δ at hi
    change (i:ℝ)*Δ ≤ Y y at lo'; change Y y < ((i:ℝ)+1)*Δ at hi'
    change |Y y-Y x| ≤ Δ
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  · simpa [Set.not_nonempty_iff_eq_empty.mp ne] using ha

/-- The strip masses sum to at most the full input mass, uniformly in the number of strips. -/
theorem sum_strip_mass (κ : Measure ℝ) [IsFiniteMeasure κ] {Y : ℝ → ℝ} (mY : Measurable Y)
    {Q : Set ℝ} (mQ : MeasurableSet Q) {Δ : ℝ} (hΔ : 0 < Δ) (I : Finset ℤ) :
    ∑ i ∈ I, (stripLaw κ Q Y Δ i).real univ ≤ κ.real univ := by
  let f := fun i => Q ∩ heightStrip Y Δ i
  have dis : Pairwise (Disjoint on f) := by
    intro i k hn; apply disjoint_left.mpr; rintro x ⟨_,lo,hi⟩ ⟨_,lo',hi'⟩
    change (i:ℝ)*Δ ≤ Y x at lo; change Y x < ((i:ℝ)+1)*Δ at hi
    change (k:ℝ)*Δ ≤ Y x at lo'; change Y x < ((k:ℝ)+1)*Δ at hi'
    rcases lt_or_gt_of_ne hn with e|e
    · have h : (i:ℝ)+1 ≤ k := by exact_mod_cast e
      linarith [mul_le_mul_of_nonneg_right h hΔ.le]
    · have h : (k:ℝ)+1 ≤ i := by exact_mod_cast e
      linarith [mul_le_mul_of_nonneg_right h hΔ.le]
  simp_rw [stripLaw,map_measureReal_apply (measurable_stripPoint mY _ _) MeasurableSet.univ,
    preimage_univ,measureReal_restrict_apply_univ]
  rw [← measureReal_biUnion_finset (s := I) (f := f) (dis.set_pairwise _) (fun _ _ => mQ.inter (measurableSet_Ico.preimage mY))]
  exact measureReal_mono (subset_univ _)

end Weierstrass.StripProof
