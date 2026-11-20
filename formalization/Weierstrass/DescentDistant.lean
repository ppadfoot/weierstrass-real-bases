module

public import Weierstrass.DescentSublevel
public import Weierstrass.DescentPartition

/-! The integrated off-diagonal cost for two distinct physical children of
one parent. The continued child labels may be dropped on this event. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators
namespace Weierstrass.Descent
open Predecessor (unitLaw)
local instance distantGroupMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance distantGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def separated {N : ℕ} (T : ℝ) (G : ℝ → ℝ) (W : ℝ) (i j : Fin N) : Prop :=
  W < |G (anchor T i)-G (anchor T j)|

theorem separated_derivatives {T D R : ℝ} {N : ℕ} {G : ℝ → ℝ}
    (osc : ∀ i : Fin N, ∀ y ∈ cell N i, |G (T*y)-G (anchor T i)| ≤ D)
    {i j : Fin N} (far : separated T G (2*D+R) i j) {x y : ℝ} (hx : x ∈ cell N i)
    (hy : y ∈ cell N j) : R < |G (T*x)-G (T*y)| := by
  have a := abs_le.mp (osc i x hx)
  have b := abs_le.mp (osc j y hy)
  by_contra! near
  have d := abs_le.mp near
  apply (not_lt_of_ge (abs_le.mpr ⟨?_,?_⟩)) far
  · linarith only [d.1,a.2,b.1]
  · linarith only [d.2,a.1,b.2]

def branchEvent {B : ℂ} (g ρ T W r : ℝ) (p : RayParameters) (e : ℤ → ℝ) (ω : PhaseTorus)
    {N : ℕ} (i j : Fin N) : Set (complexPhaseGroup B × (ℝ × ℝ)) :=
  {v | separated T (derivRay ‖B‖ g ρ p.1 p.2 e (ω+v.1.val)) W i j ∧
    |ordinate ‖B‖ g T p (ω+v.1.val) (childInput i v.2.1)-ordinate ‖B‖ g T p (ω+v.1.val) (childInput j v.2.2)| ≤ r}

set_option maxHeartbeats 600000 in
theorem branchEvent_measurable {B : ℂ} (g ρ T W r : ℝ) (p : RayParameters) (e : ℤ → ℝ) (ω : PhaseTorus)
    {N : ℕ} (i j : Fin N) : MeasurableSet (branchEvent (B:=B) g ρ T W r p e ω i j) := by
  let V := complexPhaseGroup B × (ℝ × ℝ)
  let z (v : V) := ω+v.1.val
  have mz : Measurable z := measurable_const.add (continuous_subtype_val.measurable.comp measurable_fst)
  have G (x : ℝ) : Measurable (fun v : V ↦ derivRay ‖B‖ g ρ p.1 p.2 e (z v) x) :=
    (Measurable.of_uncurry_right (f:=derivRay ‖B‖ g ρ p.1 p.2 e) (derivative_measurable _ _ _ _ _ _) (y:=x)).comp mz
  have F (i : Fin N) (t : V → ℝ) (mt : Measurable t) : Measurable (fun v ↦ ordinate ‖B‖ g T p (z v) (childInput i (t v))) := by
    change Measurable ((fun v : PhaseTorus × ℝ ↦ ordinate ‖B‖ g T p v.1 v.2) ∘ (fun v : V ↦ (z v,childInput i (t v))))
    exact (ordinate_joint _ _ _ _).comp (mz.prodMk ((measurable_childInput i).comp mt))
  exact (measurableSet_lt measurable_const ((G _).sub (G _)).abs).inter
    (measurableSet_le ((F i _ (measurable_fst.comp measurable_snd)).sub (F j _ (measurable_snd.comp measurable_snd))).abs measurable_const)

/-- Uniform in the parent length, indices, weights, coset and radius. The
block-dependent constant is allowed to grow, since n stays fixed through
all depths before taking its limit. -/
theorem haar_branch_event {B : ℂ} (hb : 0 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 1 ≤ T → T ≤ 3 → ∀ (N : ℕ), 0 < N → childLength ‖B‖ T n N ≤ 2 →
    ∀ (p : RayParameters) (e : ℤ → ℝ), (∀ j, |p.1 j| ≤ 1) → (∀ j, |p.2 j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → (∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) → ∀ (ω : PhaseTorus)
      (i j : Fin N) (r : ℝ), 0 ≤ r → ((complexPhaseHaar B).prod (unitLaw.prod unitLaw))
        (branchEvent g ρ T ((2*markConstant ‖B‖ (g*ρ)+1)*(g*ρ)^n) r p e ω i j) ≤ ENNReal.ofReal (C*r) := by
  let h := g*ρ
  let D := markConstant ‖B‖ h
  have hp := pow_pos (mul_pos hg hr) n
  obtain ⟨C,hC,H⟩ := haar_distant_pair hb hg hg1 hr hr1 hh (T:=3) (by norm_num) hp (complexPhaseHaar B)
  refine ⟨C,hC,?_⟩
  intro T T1 T3 N hN len p e hc hd he hm ω i j r r0
  let E := branchEvent (B:=B) g ρ T ((2*D+1)*h^n) r p e ω i j
  have mE := branchEvent_measurable (B:=B) g ρ T ((2*D+1)*h^n) r p e ω i j
  change ((complexPhaseHaar B).prod (unitLaw.prod unitLaw)) E ≤ _
  rw [Measure.prod_apply_symm mE]
  apply (lintegral_mono_ae (g:=fun _ ↦ ENNReal.ofReal (C*r)) _).trans_eq (by simp)
  have one : ∀ᵐ x ∂unitLaw, x ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  have aa := (Measure.quasiMeasurePreserving_fst (μ:=unitLaw) (ν:=unitLaw)).ae one
  have bb := (Measure.quasiMeasurePreserving_snd (μ:=unitLaw) (ν:=unitLaw)).ae one
  filter_upwards [aa,bb] with v vi vj
  have cx := childInput_mem hN i vi
  have cy := childInput_mem hN j vj
  have bd {x : ℝ} (hx : x ∈ Ico 0 1) : |T*x| ≤ 3 := by
    rw [abs_of_nonneg (mul_nonneg (zero_le_one.trans T1) hx.1)]
    exact (mul_le_of_le_one_right (zero_le_one.trans T1) hx.2.le).trans T3
  apply (measure_mono _).trans (H p.1 p.2 e hc hd he hm ω (bd (cell_subset hN i cx)) (bd (cell_subset hN j cy)) r0)
  intro z hz
  change separated T _ ((2*D+1)*h^n) i j ∧ _ at hz
  refine ⟨hz.2,?_⟩
  have osc := derivative_cell_oscillation hb hg hg1 hr hr1 hh (zero_le_one.trans T1) hN len hc hd he (ω+z.val)
  exact separated_derivatives (D:=D*h^n) (R:=h^n) osc (by simpa only [add_mul,one_mul,mul_assoc] using hz.1) cx cy

end Weierstrass.Descent
