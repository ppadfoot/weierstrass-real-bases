module

public import Weierstrass.DescentPartition
public import Weierstrass.DescentSublevel

/-! Recursively marked physical laws in §6. The arity, interval length and
phase translation at each level are calculated from the actual real base. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators
namespace Weierstrass.Descent
open Predecessor (unitLaw)

def arity (b T : ℝ) (n : ℕ) := max 1 ⌊T*b^n⌋₊

theorem arity_pos (b T : ℝ) (n : ℕ) : 0 < arity b T n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem arity_floor {b T : ℝ} {n : ℕ} (hn : 2 ≤ T*b^n) : arity b T n = ⌊T*b^n⌋₊ :=
  max_eq_right (mesh_length hn).1

def widthMark (b g ρ : ℝ) (n : ℕ) := (2*markConstant b (g*ρ)+1)*(g*ρ)^n

def badCell (b g ρ T θ : ℝ) (p : RayParameters) (e : ℤ → ℝ) (z : PhaseTorus) (n : ℕ) {N : ℕ} (i : Fin N) : Bool :=
  decide (θ < ((neighbors T (derivRay b g ρ p.1 p.2 e z) (widthMark b g ρ n) i).card:ℝ)/N)

def cellLaw (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) {N : ℕ} (i : Fin N) :=
  (unitLaw.restrict (cell N i)).map (ordinate b g T p z)

instance (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) {N : ℕ} (i : Fin N) :
    IsFiniteMeasure (cellLaw b g T p z i) := by unfold cellLaw;infer_instance

theorem sum_cellLaw {N : ℕ} (hN : 0 < N) (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) :
    (∑ i : Fin N, cellLaw b g T p z i) = fullLaw b g T p z := by
  have H := congrArg (fun μ : Measure ℝ ↦ μ.map (ordinate b g T p z)) (cell_partition hN)
  rw [←Measure.sum_fintype,Measure.map_sum (ordinate_measurable _ _ _ _ _).aemeasurable,Measure.sum_fintype] at H
  exact H

def wordLaw (b g ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) : List Bool → ℝ → RayParameters → PhaseTorus → Measure ℝ
  | [], T, p, z => fullLaw b g T p z
  | a::as, T, p, z =>
    let N := arity b T n
    ∑ i : Fin N, ENNReal.ofReal (N:ℝ)⁻¹ •
      ((if badCell b g ρ T θ p e z n i = a then
        wordLaw b g ρ θ n e as (childLength b T n N) (shiftedParameters p n) (physicalEnvironment b p.2 z n (anchor T i))
      else 0) : Measure ℝ).map (pushChild b g T p z i n)

theorem wordLaw_le {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (w : List Bool) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (z : PhaseTorus) :
    wordLaw b g ρ θ n e w T p z ≤ fullLaw b g T p z := by
  induction w generalizing T p z with
  | nil => exact le_rfl
  | cons a as ih =>
    let N := arity b T n
    rw [←sum_cellLaw (N:=N) (arity_pos ..) b g T p z,wordLaw]
    apply Finset.sum_le_sum
    intro i _
    rw [cellLaw,fullLaw_child hb hg hg1 hbg hc hd z (arity_pos b T n) i n]
    apply _root_.smul_le_smul_left
    apply Measure.map_mono _ (show Measurable (pushChild b g T p z i n) from measurable_const.add (measurable_const.mul measurable_id))
    split
    · exact ih _ (fun j ↦ hc (j+n)) (fun j ↦ hd (j+n)) _
    · exact bot_le

theorem badCell_measurable (b g ρ T θ : ℝ) (p : RayParameters) (e : ℤ → ℝ) (n : ℕ) {N : ℕ} (i : Fin N) (a : Bool) :
    MeasurableSet {z | badCell b g ρ T θ p e z n i = a} := by
  classical
  let G (z : PhaseTorus) (i : Fin N) := derivRay b g ρ p.1 p.2 e z (anchor T i)
  have mG (i : Fin N) : Measurable (fun z ↦ G z i) :=
    Measurable.of_uncurry_right (f:=derivRay b g ρ p.1 p.2 e) (derivative_measurable _ _ _ _ _ _)
  have mD : Measurable (fun z ↦ ((neighbors T (derivRay b g ρ p.1 p.2 e z) (widthMark b g ρ n) i).card : ℝ)) := by
    have eq (z : PhaseTorus) : ((neighbors T (derivRay b g ρ p.1 p.2 e z) (widthMark b g ρ n) i).card : ℝ) =
        ∑ j : Fin N, if |G z i-G z j| ≤ widthMark b g ρ n then (1:ℝ) else 0 := (Finset.sum_boole _ _).symm
    simp_rw [eq]
    exact Finset.measurable_fun_sum _ (fun j _ ↦ measurable_const.ite
      (measurableSet_le ((mG i).sub (mG j)).abs measurable_const) measurable_const)
  cases a
  · simpa only [badCell,decide_eq_false_iff_not,not_lt] using measurableSet_le (mD.div_const N) (measurable_const (a:=θ))
  · simpa only [badCell,decide_eq_true_eq] using measurableSet_lt (measurable_const (a:=θ)) (mD.div_const N)

theorem fullLaw_measurable (b g T : ℝ) (p : RayParameters) : Measurable (fullLaw b g T p) := by
  apply Measure.measurable_of_measurable_coe
  intro S mS
  have eq (z : PhaseTorus) : fullLaw b g T p z S = unitLaw (Prod.mk z ⁻¹' ((fun v : PhaseTorus × ℝ ↦ ordinate b g T p v.1 v.2) ⁻¹' S)) :=
    Measure.map_apply (ordinate_measurable _ _ _ _ _) mS
  simp_rw [eq];exact measurable_measure_prodMk_left (ordinate_joint _ _ _ _ mS)

end Weierstrass.Descent
