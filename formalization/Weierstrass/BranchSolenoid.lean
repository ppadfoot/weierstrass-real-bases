module

public import Weierstrass.PhaseDensity

/-! The actual Haar orbit closure and the bilateral integral polynomial
recurrence. Finite circle characters separate points of this compact torus. -/
@[expose] public noncomputable section
open Set Polynomial MeasureTheory
open scoped BigOperators
namespace Weierstrass.Branch

def applyPoly (P : ℤ[X]) (z : PhaseTorus) (m : ℤ) : UnitAddCircle :=
  P.sum (fun i k ↦ k • z (m+(i:ℤ)))

theorem applyPoly_add (P Q : ℤ[X]) (z : PhaseTorus) (m : ℤ) :
    applyPoly (P+Q) z m = applyPoly P z m + applyPoly Q z m :=
  Polynomial.sum_add_index _ _ _ (by simp) (by intros;simp [add_zsmul])

theorem applyPoly_monomial (n : ℕ) (k : ℤ) (z : PhaseTorus) (m : ℤ) :
    applyPoly (monomial n k) z m = k • z (m+n) := by simp [applyPoly]

theorem applyPoly_monomial_mul (P : ℤ[X]) (n : ℕ) (k : ℤ) (z : PhaseTorus) (m : ℤ) :
    applyPoly (monomial n k*P) z m = k • applyPoly P z (m+n) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add,applyPoly_add,applyPoly_add,hP,hQ,smul_add]
  | monomial j v => rw [monomial_mul_monomial,applyPoly_monomial,applyPoly_monomial,mul_smul,Nat.cast_add,add_assoc]

theorem applyPoly_dvd {P Q : ℤ[X]} (hd : P ∣ Q) (z : PhaseTorus) (hz : ∀ m, applyPoly P z m = 0) (m : ℤ) :
    applyPoly Q z m = 0 := by
  obtain ⟨F,rfl⟩ := hd
  rw [mul_comm];induction F using Polynomial.induction_on' with
  | add P' Q hP hQ => rw [add_mul,applyPoly_add,hP,hQ,add_zero]
  | monomial n k => rw [applyPoly_monomial_mul,hz,smul_zero]

theorem phaseGroup_of_relations {b : ℝ} (z : PhaseTorus)
    (H : ∀ (S : Finset ℤ) (n : S → ℤ), (∑ i : S, (n i:ℝ)*b^(i:ℤ)) = 0 →
      ∑ i : S, n i • z (i:ℤ) = 0) : z ∈ phaseGroup b := by
  classical
  let _ : MeasurableSpace (phaseGroup b) := borel _
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : Measure.IsAddLeftInvariant (phaseHaar b) := by unfold phaseHaar;infer_instance
  by_contra hz
  have closed : IsClosed (phaseGroup b : Set PhaseTorus) := (phaseOrbit b).range.isClosed_topologicalClosure
  obtain ⟨S,U,hU,sub⟩ := isOpen_pi_iff.mp closed.isOpen_compl z hz
  let p : phaseGroup b →+ UnitAddTorus S := {toFun := fun g i ↦ g.val i, map_zero' := rfl, map_add' := fun _ _ ↦ rfl}
  have hp : Continuous p := continuous_pi (fun i : S ↦ (continuous_apply (i:ℤ)).comp continuous_subtype_val)
  obtain ⟨w,hw⟩ : (fun i : S ↦ z (i:ℤ)) ∈ range p := by
    apply mem_torus_image_of_characters (phaseHaar b) p hp
    intro n hn
    let α := ∑ i : S, (n i:ℝ)*b^(i:ℤ)
    have hα : α ≠ 0 := by
      intro h
      apply hn;rw [mFourier_eq_sum_toCircle,H S n h];simp
    let x := (1/2:ℝ)/α
    let v : phaseGroup b := ⟨phaseOrbit b x,(phaseOrbit b).range.le_topologicalClosure ⟨x,rfl⟩⟩
    refine ⟨v,?_⟩
    have eq : (∑ i : S, n i • (p v) i) = (↑(1/2:ℝ):UnitAddCircle) := by
      let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))
      change (∑ i : S, n i • q (b^(i:ℤ)*x)) = q _
      simp only [←map_zsmul,zsmul_eq_mul,←mul_assoc,←map_sum,←Finset.sum_mul]
      congr 1;change α*((1/2)/α)=1/2;field_simp
    rw [mFourier_eq_sum_toCircle,eq]
    intro h
    have hzero : (↑(1/2:ℝ):UnitAddCircle) = 0 := by
      apply AddCircle.injective_toCircle one_ne_zero;apply Subtype.ext;simpa using h
    have t := (AddCircle.coe_eq_zero_iff_of_mem_Ico (show (1/2:ℝ) ∈ Ico 0 1 by constructor <;> norm_num)).mp hzero
    norm_num at t
  apply (sub (a:=w.val) ?_) w.property
  intro i hi
  have heq : w.val i=z i := congrFun hw ⟨i,hi⟩
  rw [heq];exact (hU i hi).2

theorem applyPoly_sum {ι : Type*} (S : Finset ι) (f : ι → ℤ[X]) (z : PhaseTorus) (m : ℤ) :
    applyPoly (∑ i ∈ S, f i) z m = ∑ i ∈ S, applyPoly (f i) z m := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [applyPoly]
  | insert j S hj ih => simp only [Finset.sum_insert hj,applyPoly_add,ih]

/-- Every bilateral solution of the primitive polynomial recurrence occurs
in the orbit closure. The integral divisibility assumption is exactly the
primitive generator property, needed at nonmonic algebraic bases. -/
theorem phaseGroup_of_recurrence {b : ℝ} (hb : b ≠ 0) (P : ℤ[X])
    (generator : ∀ Q : ℤ[X], aeval b Q = 0 → P ∣ Q) (z : PhaseTorus)
    (hz : ∀ m, applyPoly P z m=0) : z ∈ phaseGroup b := by
  classical
  apply phaseGroup_of_relations z
  intro S n ha
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    let k (i : S) := ((i:ℤ)-m).toNat
    have hk (i : S) : (k i : ℤ) = (i:ℤ)-m := Int.toNat_of_nonneg (sub_nonneg.mpr (S.min'_le _ i.property))
    let Q : ℤ[X] := ∑ i : S, monomial (k i) (n i)
    have vanish : aeval b Q = 0 := by
      simp only [Q,map_sum,aeval_monomial,eq_intCast]
      calc
        _ = ∑ i : S, ((n i:ℝ)*b^(i:ℤ))/b^m := by
          apply Finset.sum_congr rfl;intro i _
          rw [←zpow_natCast b (k i),hk,zpow_sub₀ hb,mul_div_assoc]
        _ = 0 := by rw [←Finset.sum_div,ha,zero_div]
    have h := applyPoly_dvd (generator Q vanish) z hz m
    simp only [Q,applyPoly_sum,applyPoly_monomial,hk,add_sub_cancel] at h
    simpa [add_comm m] using h
  · have h := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S;exact Finset.sum_of_isEmpty _

end Weierstrass.Branch
