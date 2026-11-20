module

public import Weierstrass.DescentWordMeasures

/-! Expected bad-label mass. The equality with the physical Haar/input test
prevents replacing the original measure by a measure on cylinder centers. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal Topology
namespace Weierstrass.Descent
open Predecessor (unitLaw)
local instance massGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance massGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def badShare (b g ρ T θ : ℝ) (n N : ℕ) (p : RayParameters) (e : ℤ → ℝ) (z : PhaseTorus) : ℝ≥0∞ :=
  ∑ i : Fin N, if badCell b g ρ T θ p e z n i = true then ENNReal.ofReal (N:ℝ)⁻¹ else 0

theorem badShare_measurable (b g ρ T θ : ℝ) (n N : ℕ) (p : RayParameters) (e : ℤ → ℝ) :
    Measurable (badShare b g ρ T θ n N p e) :=
  Finset.measurable_fun_sum _ (fun i _ ↦ measurable_const.ite (badCell_measurable b g ρ T θ p e n i true) measurable_const)

theorem badShare_eq {N : ℕ} (hn : 0 < N) (b g ρ T θ : ℝ) (n : ℕ) (p : RayParameters) (e : ℤ → ℝ) (z : PhaseTorus) :
    unitLaw {x | marked (N:=N) T (derivRay b g ρ p.1 p.2 e z) (widthMark b g ρ n) θ x} =
      badShare b g ρ T θ n N p e z := by
  let X (i : Fin N) : Set ℝ := if badCell b g ρ T θ p e z n i = true then cell N i else ∅
  have bdd (i : Fin N) : X i ⊆ cell N i := by dsimp [X];split <;> simp
  have disj : Pairwise (Function.onFun Disjoint X) := fun i j h ↦ (cell_disjoint hn h).mono (bdd i) (bdd j)
  have mx (i : Fin N) : MeasurableSet (X i) := by dsimp [X];split <;> first | exact measurableSet_Ico | exact MeasurableSet.empty
  have eq : {x | marked (N:=N) T (derivRay b g ρ p.1 p.2 e z) (widthMark b g ρ n) θ x} = ⋃ i,X i := by
    ext x;constructor
    · rintro ⟨i,hi,hm⟩;refine mem_iUnion.mpr ⟨i,?_⟩
      simpa only [X,badCell,decide_eq_true_eq,if_pos hm] using hi
    · intro h;obtain ⟨i,hi⟩ := mem_iUnion.mp h
      by_cases good : badCell b g ρ T θ p e z n i = true
      · exact ⟨i,by simpa only [X,if_pos good] using hi,by simpa only [badCell,decide_eq_true_eq] using good⟩
      · simp [X,good] at hi
  rw [eq,measure_iUnion disj mx,tsum_fintype]
  unfold badShare;apply Finset.sum_congr rfl;intro i _
  dsimp only [X];split
  · exact cell_mass hn i
  · exact measure_empty

theorem badShare_haar {B : ℂ} (b g ρ T θ : ℝ) (n N : ℕ) (hn : 0 < N) (p : RayParameters) (e : ℤ → ℝ) (ω : PhaseTorus) :
    (∫⁻ z : complexPhaseGroup B, badShare b g ρ T θ n N p e (ω+z.val) ∂complexPhaseHaar B) =
      ((complexPhaseHaar B).prod unitLaw) {v : complexPhaseGroup B × ℝ | marked (N:=N) T
        (derivRay b g ρ p.1 p.2 e (ω+v.1.val)) (widthMark b g ρ n) θ v.2} := by
  let E := {v : complexPhaseGroup B × ℝ | marked (N:=N) T (derivRay b g ρ p.1 p.2 e (ω+v.1.val)) (widthMark b g ρ n) θ v.2}
  have eq : E = ⋃ i : Fin N, {v : complexPhaseGroup B × ℝ | badCell b g ρ T θ p e (ω+v.1.val) n i = true ∧ v.2 ∈ cell N i} := by
    ext v;simp only [E,marked,mem_ofPred_eq,mem_iUnion,badCell,decide_eq_true_eq];exact exists_congr fun _ ↦ and_comm
  have mz : Measurable (fun v : complexPhaseGroup B × ℝ ↦ ω+v.1.val) := measurable_const.add (continuous_subtype_val.measurable.comp measurable_fst)
  have mE : MeasurableSet E := by
    rw [eq];exact MeasurableSet.iUnion fun i ↦ ((badCell_measurable b g ρ T θ p e n i true).preimage mz).inter
      ((show MeasurableSet (cell N i) from measurableSet_Ico).preimage measurable_snd)
  change _ = ((complexPhaseHaar B).prod unitLaw) E
  rw [Measure.prod_apply mE]; exact lintegral_congr (fun z ↦ (badShare_eq hn b g ρ T θ n p e (ω+z.val)).symm)

theorem badShare_small {B : ℂ} (hb : 0 < ‖B‖) {g ρ s v : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (hv : 0 < v) (hv' : v < s)
    {P : Set RayParameters} (H : RayInformation B (g*ρ) s P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (ω : PhaseTorus) (p : RayParameters) (e : ℤ → ℝ), (∀ j, |p.1 j| ≤ 1) →
      (∀ j, |p.2 j| ≤ 1) → (∀ j, |e j| ≤ 1) → (fun j ↦ p.1 j*e j,p.2) ∈ P →
      ∀ {T : ℝ}, 1 ≤ T → T ≤ 3 → ∀ {N : ℕ}, 0 < N → childLength ‖B‖ T n N ≤ 2 →
      ∀ {θ : ℝ}, ((g*ρ)^n)^v ≤ θ →
      (∫⁻ z : complexPhaseGroup B, badShare ‖B‖ g ρ T θ n N p e (ω+z.val) ∂complexPhaseHaar B) ≤ ENNReal.ofReal ε := by
  filter_upwards [bad_label_probability hb hg hg1 hr hr1 hh hv hv' H hε] with n bound
  intro ω p e hc hd he hp T T1 T3 N hN len θ rate
  have h := bound ω p.1 p.2 e hc hd he hp T T1 T3 N hN len θ rate
  rw [badShare_haar _ _ _ _ _ _ _ hN,← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

end Weierstrass.Descent
