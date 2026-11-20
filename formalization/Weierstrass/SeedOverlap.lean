module

public import Weierstrass.SeedSampling

/-! Joint Haar and physical-time estimates for pairs of translated heavy
events. Both events sample the same phase and the same physical input. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex Weierstrass.CriticalRay
open scoped BigOperators Topology ENNReal
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def inputLaw : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
instance inputLaw_prob : IsProbabilityMeasure inputLaw := ⟨by simp [inputLaw,Real.volume_Icc]⟩

theorem cont_shift (a : ℝ) (d : ℤ → ℝ) : Continuous (transverseOrbit a d) := by
  apply continuous_pi
  intro j
  exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

def heavyAt {B : ℂ} (g ρ : ℝ) (p : RayParameters) (e : ℤ → ℝ) (ω : PhaseTorus)
    (T A r h v : ℝ) : Set (complexPhaseGroup B × ℝ) :=
  {zx | ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g p
    (((ω+zx.1.val)+transverseOrbit ρ e v)+transverseOrbit ‖B‖ p.2 zx.2) T A r}

theorem heavyAt_meas {B : ℂ} (g ρ : ℝ) (p : RayParameters) (e : ℤ → ℝ) (ω : PhaseTorus)
    (T A r h v : ℝ) : MeasurableSet (heavyAt (B:=B) g ρ p e ω T A r h v) :=
  measurableSet_lt measurable_const ((measurable_rayOccupation _ _ _ _ _ _).comp
    ((((continuous_const.add (continuous_subtype_val.comp continuous_fst)).add continuous_const).add
      ((cont_shift _ _).comp continuous_snd)).measurable))

theorem heavyAt_mass {B : ℂ} (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] (g ρ : ℝ) (p : RayParameters) (e : ℤ → ℝ) (ω : PhaseTorus)
    (T A r h v : ℝ) (tp : ∀ x, transverseOrbit ‖B‖ p.2 x ∈ complexPhaseGroup B)
    (te : transverseOrbit ρ e v ∈ complexPhaseGroup B) :
    (μ.prod inputLaw) (heavyAt g ρ p e ω T A r h v) =
    μ {z | ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g p (ω+z.val) T A r} := by
  let E := {z : complexPhaseGroup B | ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g p (ω+z.val) T A r}
  have byTime (x : ℝ) : μ ((fun z ↦ (z,x)) ⁻¹' heavyAt (B:=B) g ρ p e ω T A r h v) = μ E := by
    let a : complexPhaseGroup B := ⟨transverseOrbit ρ e v+transverseOrbit ‖B‖ p.2 x,
      (complexPhaseGroup B).add_mem te (tp x)⟩
    have eq : (fun z ↦ (z,x)) ⁻¹' heavyAt (B:=B) g ρ p e ω T A r h v = (fun z ↦ a+z) ⁻¹' E := by
      ext z
      simp only [heavyAt,E,mem_preimage,mem_ofPred_eq,AddSubgroup.coe_add,a]
      abel_nf
    rw [eq,measure_preimage_add]
  rw [Measure.prod_apply_symm (heavyAt_meas _ _ _ _ _ _ _ _ _ _)]
  simp_rw [byTime];simp [E]

@[fun_prop] private theorem continuous_turn : Continuous turn :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

private theorem slope_meas {B : ℂ} (g ρ : ℝ) (c d e : ℤ → ℝ) (ω : PhaseTorus) (h k : ℝ) :
    Measurable (fun zx : complexPhaseGroup B × ℝ ↦ slope ‖B‖ g ρ c d e ω zx.1.val h k zx.2) := by
  apply Measurable.tsum
  intro j
  apply Continuous.measurable
  have c₁ : Continuous (fun zx : complexPhaseGroup B × ℝ ↦ turn (ω j+↑(ρ^j*e j*k+‖B‖^j*d j*zx.2))) :=
    continuous_turn.comp (continuous_const.add (continuous_quotient_mk'.comp (continuous_const.add
      (continuous_const.mul continuous_snd))))
  have c₂ : Continuous (fun zx : complexPhaseGroup B × ℝ ↦ coord zx.1.val j) :=
    (coord_cont j).comp (continuous_subtype_val.comp continuous_fst)
  exact continuous_const.mul (Complex.continuous_re.comp
    ((((continuous_const.mul c₁).mul continuous_const).mul c₂)))

set_option maxHeartbeats 1800000 in
/-- Uniform bound on a single pair. The first term is controlled by (H5)
and the second is an explicit constant times r^(1-2h). -/
theorem pair_mass_bound {B : ℂ} (hb : 1 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hq : 1 < ‖B‖*g) (hρ : 0 < ρ) (hQ : (‖B‖*g)*ρ < 1)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ]
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (ω : PhaseTorus) {T A r κ δ η : ℝ} (hT : 0 < T) (hA : 0 < A) (hr : 0 < r)
    (hk : 0 < κ) (hη : 0 ≤ η) (h h₁ h₀ : ℝ) (N : ℕ) (cover : 1 ≤ N*δ)
    (osc : ∀ (z : complexPhaseGroup B) (t v : ℝ), |t-v| ≤ δ →
      |slope ‖B‖ g ρ c d e ω z.val h₁ h₀ t-slope ‖B‖ g ρ c d e ω z.val h₁ h₀ v| ≤ κ/2)
    (small : ∀ t, μ.real {z : complexPhaseGroup B | |slope ‖B‖ g ρ c d e ω z.val h₁ h₀ t| ≤ κ} ≤ η) :
    (μ.prod inputLaw).real (heavyAt g ρ (c,d) e ω T A r h h₁ ∩ heavyAt g ρ (c,d) e ω T A r h h₀) ≤
      η+(9*(1+2*T)*(1+2*T)/(r^h)^2)*N*(4*(A*r)/κ) := by
  let E := heavyAt (B:=B) g ρ (c,d) e ω T A r h h₁ ∩ heavyAt (B:=B) g ρ (c,d) e ω T A r h h₀
  have mE : MeasurableSet E := (heavyAt_meas _ _ _ _ _ _ _ _ _ _).inter (heavyAt_meas _ _ _ _ _ _ _ _ _ _)
  let S := {zx : complexPhaseGroup B × ℝ | |slope ‖B‖ g ρ c d e ω zx.1.val h₁ h₀ zx.2| ≤ κ}
  have mS : MeasurableSet S := measurableSet_le (slope_meas _ _ _ _ _ _ _ _).abs measurable_const
  have hs : (μ.prod inputLaw) S ≤ ENNReal.ofReal η := by
    rw [Measure.prod_apply_symm mS]
    calc
      _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal η ∂inputLaw := lintegral_mono fun t ↦
          (ofReal_measureReal (measure_ne_top μ _)) ▸ ENNReal.ofReal_le_ofReal (small t)
      _ = _ := by simp
  let cost := (9*(1+2*T)*(1+2*T)/(r^h)^2)*N*(4*(A*r)/κ)
  have large : (μ.prod inputLaw) (E \ S) ≤ ENNReal.ofReal cost := by
    have mm := mE.diff mS
    rw [Measure.prod_apply mm]
    apply le_trans (lintegral_mono (g:=fun _ ↦ ENNReal.ofReal cost) _)
    · simp
    · intro z
      let F (a : ℝ) := circleRay ‖B‖ g c d ((ω+z.val)+transverseOrbit ρ e a)
      have mf v : Measurable (F v) := (measurable_circleRay ‖B‖ g c d).comp
        ((measurable_const (a:=(ω+z.val)+transverseOrbit ρ e v)).prodMk measurable_id)
      have ds := fun t ↦ circle_derivative (zero_lt_one.trans hb) hg hg1 hq hρ hQ hc hd he ω z.val h₁ h₀ t
      have estimate := heavy_pair_bound (sampledLaw (F h₁) T) (sampledLaw (F h₀) T)
        ds hk (mul_pos hA hr) (Real.rpow_pos_of_pos hr h) (osc z) N 0 1 (by simpa using cover)
      rw [sampled_mass _ (mf _) hT,sampled_mass _ (mf _) hT] at estimate
      have ms : MeasurableSet (Prod.mk z ⁻¹' (E \ S)) := mm.preimage (measurable_prodMk_left (x:=z))
      change (volume.restrict (Icc (0:ℝ) 1)) _ ≤ _
      rw [Measure.restrict_apply ms]
      apply (measure_mono _).trans estimate
      rintro x ⟨⟨⟨hx₁,hx₀⟩,nx⟩,hx⟩
      have cmp (v : ℝ) (hxv : (z,x) ∈ heavyAt g ρ (c,d) e ω T A r h v) :
          r^h < (sampledLaw (F v) T).real (Icc (F v x-A*r) (F v x+A*r)) := by
        have hh := lt_of_lt_of_le hxv (reanchor_dominates (zero_lt_one.trans hb) hg hg1 hq hc hd
          ((ω+z.val)+transverseOrbit ρ e v) T A r x hx)
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.rpow_pos_of_pos hr h).le).mp
          ((ofReal_measureReal (measure_ne_top (sampledLaw (F v) T) _)).symm ▸ hh)
      exact ⟨hx,cmp _ hx₁,cmp _ hx₀,lt_of_not_ge nx⟩
  have u : E ⊆ S ∪ (E \ S) := fun x hx ↦ by by_cases a : x ∈ S <;> simp [a,hx]
  have H := ((measure_mono u).trans (measure_union_le S (E \ S))).trans (add_le_add hs large)
  have cp : 0 ≤ cost := by dsimp [cost];positivity
  rw [←ENNReal.ofReal_add hη cp] at H
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr H |>.trans_eq
    (ENNReal.toReal_ofReal (add_nonneg hη cp))

end Weierstrass.RaySeed
