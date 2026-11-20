module

public import Weierstrass.BranchWindows

/-! Finite-prefix conditional contraction for the actual uniform digit code,
including every possible choice of a starting prefix. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators
namespace Weierstrass.Branch

def prefixEvent {p : ℕ} (hp : 0 < p) {n : ℕ} (v : Fin n → Fin p) :=
  {x : ℝ | ∀ j : Fin n, uniformCode p hp x j=v j}

theorem prefixEvent_measurable {p : ℕ} (hp : 0 < p) {n : ℕ} (v : Fin n → Fin p) : MeasurableSet (prefixEvent hp v) := by
  have eq : prefixEvent hp v = ⋂ j : Fin n, {x | uniformCode p hp x j=v j} := by ext x;simp [prefixEvent]
  rw [eq];exact MeasurableSet.iInter (fun j : Fin n ↦ measurableSet_eq_fun (measurable_uniformCode p hp j) measurable_const)

private def extended {p n : ℕ} (hp : 0 < p) (v : Fin n → Fin p) (j : ℕ) : Fin p := if h : j<n then v ⟨j,h⟩ else ⟨0,hp⟩

private theorem cylinder_change {p n : ℕ} (hp : 0 < p) (v : Fin n → Fin p) :
    unitLaw.restrict (prefixEvent hp v) = ENNReal.ofReal ((p:ℝ)⁻¹^n) • unitLaw.map (prefixSeed (extended hp v) n) := by
  have eq : prefixEvent hp v = {x | ∀ j<n, uniformCode p hp x j=extended hp v j} := by
    ext x;constructor
    · intro h j hj;simpa only [extended,dif_pos hj] using h ⟨j,hj⟩
    · intro h j;simpa only [extended,dif_pos j.isLt] using h j j.isLt
  rw [eq,restrict_code_prefix]

private theorem cylinder_partition {p : ℕ} (hp : 0 < p) (n : ℕ) : (∑ v : Fin n → Fin p, unitLaw.restrict (prefixEvent hp v))=unitLaw := by
  have hd : Pairwise (Function.onFun Disjoint (fun v : Fin n → Fin p ↦ prefixEvent hp v)) := by
    intro v u h;apply Set.disjoint_left.mpr;intro x a b
    exact h (funext (fun j ↦ (a j).symm.trans (b j)))
  have hu : (⋃ v : Fin n → Fin p, prefixEvent hp v)=univ := iUnion_eq_univ_iff.mpr (fun x ↦ ⟨fun j ↦ uniformCode p hp x j,fun _ ↦ rfl⟩)
  rw [←Measure.sum_fintype,←Measure.restrict_iUnion hd (prefixEvent_measurable hp),hu,Measure.restrict_univ]

/-- A prefix-measurable predicate is either identically true or identically
false on an n-cylinder. If a later event has conditional probability ≤q
on each such cylinder, their intersection costs at most q times the mass
of the first event. -/
theorem prefix_contraction {p : ℕ} (hp : 0 < p) (n : ℕ) (P Q : Set ℝ) (mP : MeasurableSet P) (mQ : MeasurableSet Q)
    (det : ∀ x y : ℝ, (∀ j<n, uniformCode p hp x j=uniformCode p hp y j) → (x∈P ↔ y∈P))
    {q : ℝ≥0∞} (cap : ∀ I : ℕ → Fin p, unitLaw (prefixSeed I n ⁻¹' Q) ≤ q) :
    unitLaw (P ∩ Q) ≤ unitLaw P*q := by
  classical
  let E (v : Fin n → Fin p) := prefixEvent hp v
  let M (v : Fin n → Fin p) := unitLaw.restrict (E v)
  have parts (S : Set ℝ) : unitLaw S = ∑ v, M v S := by
    rw [←cylinder_partition hp n,Measure.finsetSum_apply]
  rw [parts (P∩Q),parts P,Finset.sum_mul]
  apply Finset.sum_le_sum;intro v _
  by_cases ex : (P ∩ E v).Nonempty
  · obtain ⟨x,hx,hv⟩ := ex
    have sub : E v ⊆ P := by
      intro y hy;apply (det x y ?_).mp hx
      intro j hj;exact (hv ⟨j,hj⟩).trans (hy ⟨j,hj⟩).symm
    have mass : M v P = ENNReal.ofReal ((p:ℝ)⁻¹^n) := by
      change unitLaw.restrict (prefixEvent hp v) P = _
      have one : unitLaw.restrict (prefixEvent hp v) P = unitLaw.restrict (prefixEvent hp v) Set.univ := by
        rw [Measure.restrict_apply mP,inter_eq_self_of_subset_right sub,Measure.restrict_apply_univ]
      rw [one,cylinder_change,Measure.smul_apply,Measure.map_apply (show Measurable (prefixSeed (extended hp v) n) from
        (measurable_const.add measurable_id).div_const _) MeasurableSet.univ];simp
    rw [mass];apply (measure_mono (μ:=M v) inter_subset_right).trans
    change unitLaw.restrict (prefixEvent hp v) Q ≤ _
    rw [cylinder_change,Measure.smul_apply,Measure.map_apply (show Measurable (prefixSeed (extended hp v) n) from
        (measurable_const.add measurable_id).div_const _) mQ, smul_eq_mul]
    gcongr;exact cap _
  · have empty : P ∩ E v = ∅ := Set.not_nonempty_iff_eq_empty.mp ex
    have zP : M v P = 0 := by change unitLaw.restrict (E v) P=_;rw [Measure.restrict_apply mP,empty,measure_empty]
    exact (measure_mono (μ:=M v) inter_subset_left).trans (by rw [zP,zero_mul])

end Weierstrass.Branch
