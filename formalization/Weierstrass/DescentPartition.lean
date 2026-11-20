module

public import Weierstrass.DescentMarking

/-! Exact decomposition of the normalized physical Lebesgue law into child
laws, including the change of variables in the bilateral Weierstrass series. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators
namespace Weierstrass.Descent
open Predecessor (unitLaw)

def childInput {N : ℕ} (i : Fin N) (x : ℝ) := ((i:ℝ)+x)/N

theorem childInput_mem {N : ℕ} (hn : 0 < N) (i : Fin N) {x : ℝ} (hx : x ∈ Ico 0 1) : childInput i x ∈ cell N i := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hn
  exact ⟨(div_le_div_iff_of_pos_right hp).mpr (le_add_of_nonneg_right hx.1),
    (div_lt_div_iff_of_pos_right hp).mpr (by linarith only [hx.2])⟩

theorem measurable_childInput {N : ℕ} (i : Fin N) : Measurable (childInput i) :=
  (measurable_const.add measurable_id).div_const _

theorem cell_change_variables {N : ℕ} (hN : 0 < N) (i : Fin N) :
    unitLaw.restrict (cell N i) = ENNReal.ofReal (N:ℝ)⁻¹ • unitLaw.map (childInput i) := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hN
  have pre : childInput i ⁻¹' cell N i = Ico (0:ℝ) 1 := by
    ext x
    change ((i:ℝ)/N ≤ ((i:ℝ)+x)/N ∧ ((i:ℝ)+x)/N < ((i:ℝ)+1)/N) ↔ 0 ≤ x ∧ x < 1
    rw [div_le_div_iff_of_pos_right hp,div_lt_div_iff_of_pos_right hp];constructor <;> rintro ⟨l,u⟩ <;> constructor <;> linarith
  have map (S : Set ℝ) : volume (childInput i ⁻¹' S) = ENNReal.ofReal (N:ℝ)*volume S := by
    change volume (((i:ℝ)+·) ⁻¹' ((·*(N:ℝ)⁻¹) ⁻¹' S)) = _
    rw [measure_preimage_add,Real.volume_preimage_mul_right (inv_ne_zero hp.ne'),inv_inv,abs_of_pos hp]
  ext S hS
  rw [unitLaw,Measure.restrict_restrict (show MeasurableSet (cell N i) from measurableSet_Ico),
    inter_eq_self_of_subset_left (cell_subset hN i),Measure.restrict_apply hS,Measure.smul_apply,
    Measure.map_apply (measurable_childInput i) hS,Measure.restrict_apply (measurable_childInput i hS),←pre,←preimage_inter,map,
    smul_eq_mul,←mul_assoc,←ENNReal.ofReal_mul (inv_pos.mpr hp).le,inv_mul_cancel₀ hp.ne',ENNReal.ofReal_one,one_mul]

theorem cell_partition {N : ℕ} (hN : 0 < N) : (∑ i : Fin N, unitLaw.restrict (cell N i)) = unitLaw := by
  have hd : Pairwise (Function.onFun Disjoint (cell N)) := fun _ _ h ↦ cell_disjoint hN h
  have eq : (⋃ i,cell N i) = Ico 0 1 := by
    apply subset_antisymm (iUnion_subset (cell_subset hN))
    exact fun _ hx ↦ mem_iUnion.mpr (cell_covers hN hx)
  rw [← Measure.sum_fintype,←Measure.restrict_iUnion hd (fun _ ↦ measurableSet_Ico),eq,unitLaw,
    Measure.restrict_restrict measurableSet_Ico,inter_self]

def ordinate (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) (x : ℝ) := circleRay b g p.1 p.2 z (T*x)

def fullLaw (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) : Measure ℝ := unitLaw.map (ordinate b g T p z)

theorem ordinate_joint (b g T : ℝ) (p : RayParameters) : Measurable (fun v : PhaseTorus × ℝ ↦ ordinate b g T p v.1 v.2) := by
  change Measurable ((fun v : PhaseTorus × ℝ ↦ circleRay b g p.1 p.2 v.1 v.2) ∘ (fun v : PhaseTorus × ℝ ↦ (v.1,T*v.2)))
  exact (measurable_circleRay _ _ _ _).comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))

theorem ordinate_measurable (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) : Measurable (ordinate b g T p z) :=
  Measurable.of_uncurry_left (f:=ordinate b g T p) (ordinate_joint _ _ _ _)

instance (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) : IsProbabilityMeasure (fullLaw b g T p z) :=
  Measure.isProbabilityMeasure_map (ordinate_measurable b g T p z).aemeasurable

def pushChild (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) {N : ℕ} (i : Fin N) (n : ℕ) (y : ℝ) :=
  circleRay b g p.1 p.2 z (anchor T i)+g^n*y

theorem pushChild_eq {b g T : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    {p : RayParameters} (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1)
    (z : PhaseTorus) {N : ℕ} (i : Fin N) (n : ℕ) (x : ℝ) :
    ordinate b g T p z (childInput i x) = pushChild b g T p z i n
      (ordinate b g (childLength b T n N) (shiftedParameters p n) (physicalEnvironment b p.2 z n (anchor T i)) x) := by
  have H := circleRay_recenter_scale hb hg hg1 hbg hc hd z (n:ℤ) (anchor T i) (childLength b T n N*x)
  have eq : anchor T i+b^(-(n:ℤ))*(childLength b T n N*x)=T*childInput i x := by
    rw [zpow_neg,zpow_natCast];unfold childLength childInput anchor;field_simp
  rw [eq,zpow_natCast] at H
  change circleRay _ _ _ _ _ _ = _+g^n*circleRay _ _ _ _ _ _
  exact (sub_eq_iff_eq_add.mp H).trans (add_comm _ _)

theorem fullLaw_child {b g T : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    {p : RayParameters} (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1)
    (z : PhaseTorus) {N : ℕ} (hn : 0 < N) (i : Fin N) (n : ℕ) :
    (unitLaw.restrict (cell N i)).map (ordinate b g T p z) = ENNReal.ofReal (N:ℝ)⁻¹ •
      (fullLaw b g (childLength b T n N) (shiftedParameters p n) (physicalEnvironment b p.2 z n (anchor T i))).map
      (pushChild b g T p z i n) := by
  rw [cell_change_variables hn i,Measure.map_smul,Measure.map_map (ordinate_measurable _ _ _ _ _) (measurable_childInput i),
    fullLaw,Measure.map_map (show Measurable (pushChild b g T p z i n) from measurable_const.add (measurable_const.mul measurable_id))
      (ordinate_measurable _ _ _ _ _)]
  congr 2;funext x;exact pushChild_eq hb hg hg1 hbg hc hd z i n x

end Weierstrass.Descent
