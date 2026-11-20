module

public import Weierstrass.HarmonicSums
public import Weierstrass.FirstMoment

/-! Concentration for the whole bilateral increment by Haar averaging over a
finite set of coordinate rotations. No independence of an untested tail
is assumed: every one of its phases is held fixed in the inner integral. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace Weierstrass

theorem harmonicCos_coe (x : ℝ) :
    harmonicCos (x : AddCircle (1 : ℝ)) = Real.cos (2*Real.pi*x) := by
  let a := turnRep (x : AddCircle (1 : ℝ))
  have heq : (a : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := AddCircle.coe_equivIoc
  obtain ⟨k, hk⟩ := QuotientAddGroup.eq_iff_sub_mem.mp heq
  change k • (1:ℝ) = a-x at hk
  simp only [zsmul_eq_mul, mul_one] at hk
  change Real.cos (2*Real.pi*a) = _
  rw [show 2*Real.pi*a = 2*Real.pi*x + (k:ℝ)*(2*Real.pi) by
    nlinarith only [congrArg (fun t : ℝ ↦ (2*Real.pi)*t) hk]]
  exact Real.cos_add_int_mul_two_pi _ _

private def angleLift (z : AddCircle (1 : ℝ)) : ℝ := AddCircle.equivIco (1 : ℝ) 0 z

private def harmonicWeight (b l u : ℝ) (j : ℤ) := 2*l^j * Real.sin (Real.pi*(b^j*u))

private theorem shifted_term (b l u : ℝ) (z : PhaseTorus) (j : ℤ) :
    incrementTerm b l (fun i ↦ angleLift (z i)) u j =
      harmonicWeight b l u j * harmonicCos (z j + ↑(b^j*u/2+1/4 : ℝ)) := by
  let x := angleLift (z j)
  have he : (x : AddCircle (1 : ℝ)) = z j := AddCircle.coe_equivIco
  rw [← he, ← AddCircle.coe_add, harmonicCos_coe, incrementTerm, Real.cos_sub_cos]
  change l^j * (-2 * Real.sin ((2*Real.pi*(x+b^j*u)+2*Real.pi*x)/2) *
    Real.sin ((2*Real.pi*(x+b^j*u)-2*Real.pi*x)/2)) = _
  rw [show 2*Real.pi*(x+(b^j*u/2+1/4)) =
    ((2*Real.pi*(x+b^j*u)+2*Real.pi*x)/2)+Real.pi/2 by ring,
    Real.cos_add_pi_div_two,
    show (2*Real.pi*(x+b^j*u)-2*Real.pi*x)/2=Real.pi*(b^j*u) by ring]
  unfold harmonicWeight
  ring

private def insertAngles (S : Finset ℤ) (t : S → AddCircle (1 : ℝ)) : PhaseTorus :=
  fun j ↦ if hj : j ∈ S then t ⟨j,hj⟩ else 0

private theorem continuous_insertAngles (S : Finset ℤ) : Continuous (insertAngles S) := by
  apply continuous_pi
  intro j
  by_cases hj : j ∈ S
  · simpa [insertAngles,hj] using (continuous_apply (⟨j,hj⟩ : S) :
      Continuous (fun t : S → AddCircle (1:ℝ) ↦ t ⟨j,hj⟩))
  · simp [insertAngles,hj,continuous_const]

private theorem split_rotations {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (u : ℝ) (S : Finset ℤ) (z : PhaseTorus) :
    ∃ (v : S → AddCircle (1:ℝ)) (c : ℝ), ∀ t : S → AddCircle (1:ℝ),
      circleIncrement b l (z+insertAngles S t) u =
      (∑ j : S, harmonicWeight b l u j * harmonicCos ((v+t) j)) + c := by
  let v (j : S) := z j + ↑(b^(j:ℤ)*u/2+1/4 : ℝ)
  let f (w : PhaseTorus) := incrementTerm b l (fun i ↦ angleLift (w i)) u
  refine ⟨v, ∑' j : {j : ℤ // j ∉ S}, f z j, ?_⟩
  intro t
  let w := z + insertAngles S t
  change (∑' j, f w j) = _
  rw [← (summable_incrementTerm hb hl hl' _ u).sum_add_tsum_subtype_compl S]
  apply congrArg₂ (· + ·)
  · rw [← Finset.sum_attach S]
    apply Finset.sum_congr rfl
    rintro ⟨j,hj⟩ _
    change incrementTerm b l (fun i ↦ angleLift (w i)) u j = _
    rw [shifted_term]
    congr 2
    simp [v,w,insertAngles,hj,add_right_comm]
  · apply tsum_congr
    rintro ⟨j,hj⟩
    simp [f,incrementTerm,w,insertAngles,hj]

/-- Fubini and translation invariance transfer a pointwise bound on the
average over auxiliary shifts to the measure of the original event. -/
private theorem measure_le_of_translated_slices {G X : Type*}
    [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableSpace X]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    (ν : Measure X) [IsProbabilityMeasure ν] (v : X → G) (hv : Measurable v)
    (E : Set G) (hE : MeasurableSet E) (K : ℝ≥0∞)
    (bound : ∀ z, ν {x | v x + z ∈ E} ≤ K) : μ E ≤ K := by
  let A := {p : X × G | v p.1+p.2 ∈ E}
  have hm : MeasurableSet A := ((hv.comp measurable_fst).add measurable_snd) hE
  have h₁ : ν.prod μ A = μ E := by
    rw [Measure.prod_apply hm]
    have h (x:X) : μ (Prod.mk x ⁻¹' A) = μ E := measure_preimage_add μ (v x) E
    simp_rw [h]
    simp
  rw [← h₁, Measure.prod_apply_symm hm]
  exact (lintegral_mono (fun z ↦ bound z)).trans_eq (by simp)


instance circleSecondCountable : SecondCountableTopology (AddCircle (1 : ℝ)) :=
  TopologicalSpace.Quotient.secondCountableTopology (QuotientAddGroup.isOpenMap_coe)

local instance harmonicGroupBorel (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

/-- A concentration bound for an entire bilateral increment. At a
transcendental base every finite family of coordinate rotations is available. -/
theorem circleIncrement_band_of_active_coordinates {b l u : ℝ}
    (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1) (ht : Transcendental ℤ b)
    (S : Finset ℤ) {a δ r : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hr : 0 ≤ r)
    (active : ∀ j ∈ S, a ≤ |2*l^j*Real.sin (Real.pi*(b^j*u))|)
    (ω : PhaseTorus) (y : ℝ) :
    phaseHaar b {z : phaseGroup b | |circleIncrement b l (ω+z.val) u-y| ≤ r} ≤
    ENNReal.ofReal (4*δ)^S.card + S.card • ENNReal.ofReal ((r/a)/(4*δ)) := by
  classical
  let _ : MeasurableSpace (phaseGroup b) := borel _
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : Measure.IsAddLeftInvariant (phaseHaar b) := by unfold phaseHaar; infer_instance
  let _ : SecondCountableTopology PhaseTorus := by unfold PhaseTorus; infer_instance
  let _ : SecondCountableTopology (phaseGroup b) := TopologicalSpace.Subtype.secondCountableTopology (phaseGroup b : Set PhaseTorus)
  let _ : OpensMeasurableSpace (phaseGroup b) := ⟨le_rfl⟩
  let _ : MeasurableAdd₂ (phaseGroup b) := ⟨continuous_add.measurable⟩
  let rot (t : S → AddCircle (1:ℝ)) : phaseGroup b :=
    ⟨insertAngles S t, by rw [phaseGroup_eq_top_of_transcendental (zero_lt_one.trans hb).ne' ht]; trivial⟩
  let ν := Measure.pi (fun _ : S ↦ circleUniform)
  let E := {z : phaseGroup b | |circleIncrement b l (ω+z.val) u-y| ≤ r}
  have hrot : Continuous rot := Continuous.subtype_mk (continuous_insertAngles S) _
  have hcoord : Measurable (fun z : phaseGroup b ↦ ω+z.val) :=
    (Continuous.add (continuous_const (y := ω)) (continuous_subtype_val
      (p := fun z : PhaseTorus ↦ z ∈ phaseGroup b))).measurable
  have hinc : Measurable (fun z : phaseGroup b ↦ circleIncrement b l (ω+z.val) u) := by
    have pair : Measurable (fun z : phaseGroup b ↦ (ω+z.val,u)) :=
      hcoord.prodMk (measurable_const (a := u))
    change Measurable ((fun p : PhaseTorus × ℝ ↦ circleIncrement b l p.1 p.2) ∘
      (fun z : phaseGroup b ↦ (ω+z.val,u)))
    exact (measurable_circleIncrement b l).comp pair
  have hE : MeasurableSet E := measurableSet_le (continuous_abs.measurable.comp
    (hinc.sub measurable_const)) measurable_const
  apply measure_le_of_translated_slices (phaseHaar b) ν rot hrot.measurable E hE
  intro z
  obtain ⟨v,c,hc⟩ := split_rotations hb hl hl' u S (ω+z.val)
  let F := {t : S → AddCircle (1:ℝ) | |(∑ j : S, harmonicWeight b l u j*harmonicCos (t j))-(y-c)| ≤ r}
  have hF : MeasurableSet F := by
    have hs := Finset.measurable_fun_sum Finset.univ (fun (j : S) _ ↦
      (measurable_const (a := harmonicWeight b l u j)).mul (measurable_harmonicCos.comp (measurable_pi_apply j)))
    exact measurableSet_le (continuous_abs.measurable.comp (hs.sub measurable_const)) measurable_const
  have eqn : {x | rot x + z ∈ E} = (v + ·) ⁻¹' F := by
    ext t
    change |circleIncrement b l (ω+(insertAngles S t+z.val)) u-y| ≤ r ↔ _
    rw [show ω+(insertAngles S t+z.val)=ω+z.val+insertAngles S t by abel, hc]
    change _ ↔ |(∑ j : S, harmonicWeight b l u j*harmonicCos ((v+t) j))-(y-c)| ≤ r
    rw [show (∑ j : S, harmonicWeight b l u j*harmonicCos ((v+t) j)) + c - y =
      (∑ j : S, harmonicWeight b l u j*harmonicCos ((v+t) j))-(y-c) by ring]
  rw [eqn]
  have translation : ν ((v+·) ⁻¹' F) = ν F := by
    rw [← Measure.map_apply (measurable_const_add v) hF, map_add_left_eq_self]
  rw [translation]
  simpa only [Fintype.card_coe] using harmonic_sum_band (fun j : S ↦ harmonicWeight b l u j)
    ha (fun j ↦ active j j.property) hδ hr (y-c)

end Weierstrass
