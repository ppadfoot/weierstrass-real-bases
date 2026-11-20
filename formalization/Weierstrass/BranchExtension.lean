module

public import Weierstrass.BranchSolenoid
public import Weierstrass.PredecessorProof

/-! An auxiliary Haar-preserving randomization of the past. The full future
of the constructed point is determined by the central block. -/
@[expose] public noncomputable section
open Set Polynomial MeasureTheory Weierstrass.Predecessor
open scoped BigOperators ENNReal
namespace Weierstrass.Branch

def coefficient (p : ℕ) (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => p
  | k+1 => a k

def characteristic (p d : ℕ) (a : ℕ → ℤ) : ℤ[X] :=
  ∑ j ∈ Finset.range (d+1), monomial j (coefficient p a j)

theorem characteristic_form (p d : ℕ) (a : ℕ → ℤ) : characteristic p d a = C (p:ℤ) +
    ∑ k ∈ Finset.range d, monomial (k+1) (a k) := by
  unfold characteristic;rw [Finset.sum_range_succ'];simp [coefficient,add_comm,monomial_zero_left]

/-- Deterministic right extension. A degree d recurrence with nonzero last
coefficient can be solved forward on the real cover. -/
def rightLift (d : ℕ) (A : ℕ → ℤ) (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < d then w m else - (∑ j : Fin d, (A j:ℝ)*rightLift d A w (m-d+j))/(A d:ℝ)
termination_by m
decreasing_by omega

theorem rightLift_start (d : ℕ) (A : ℕ → ℤ) (w : ℕ → ℝ) {j : ℕ} (hj : j < d) :
    rightLift d A w j=w j := by rw [rightLift,if_pos hj]

theorem rightLift_recurrence (d : ℕ) (A : ℕ → ℤ) (w : ℕ → ℝ) (ha : A d ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.range (d+1), (A j:ℝ)*rightLift d A w (m+j)=0 := by
  rw [Finset.sum_range_succ]
  have eq : rightLift d A w (m+d) = -(∑ j : Fin d, (A j:ℝ)*rightLift d A w (m+j))/(A d:ℝ) := by
    rw [rightLift,if_neg (by omega : ¬ m+d < d),Nat.add_sub_cancel]
  rw [eq,← Fin.sum_univ_eq_sum_range (fun j ↦ (A j:ℝ)*rightLift d A w (m+j)) d]
  have nz : (A d:ℝ) ≠ 0 := by exact_mod_cast ha
  field_simp;ring

/-- Nonnegative coordinates are completely independent of the digit sequence.
Negative coordinates are the actual inherited predecessors. -/
def twoSidedLift {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (I : ℕ → Fin p) : ℤ → ℝ
  | (j:ℕ) => rightLift d (coefficient p a) w j
  | Int.negSucc k => pathState d (fun i ↦ (a i:ℝ)) p w I (k+1) 0

theorem state_eq_lift {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (I : ℕ → Fin p) (n : ℕ) :
    ∀ j < d, pathState d (fun i ↦ (a i:ℝ)) p w I n j = twoSidedLift d a w I ((j:ℤ)-n) := by
  induction n with
  | zero => intro j hj;rw [Nat.cast_zero,sub_zero];exact (rightLift_start d _ w hj).symm
  | succ n ih =>
    intro j hj
    cases j with
    | zero => rw [Nat.cast_zero,zero_sub];rfl
    | succ j =>
      rw [show ((j+1:ℕ):ℤ)-((n+1:ℕ):ℤ)=(j:ℤ)-(n:ℤ) by omega]
      exact ih j (by omega)

def twoSided {p : ℕ} (d : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (I : ℕ → Fin p) : PhaseTorus :=
  fun i ↦ ↑(twoSidedLift d a w I i)

/-- The recurrence holds modulo one on *every* shifted window, across the
origin as well as wholly in either tail. At a left step the lifted error is
the integer digit, which disappears on the circle. -/
theorem twoSided_recurrence {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (ha : coefficient p a d ≠ 0)
    (w : ℕ → ℝ) (I : ℕ → Fin p) (m : ℤ) : applyPoly (characteristic p d a) (twoSided d a w I) m = 0 := by
  let A := coefficient p a
  let V := twoSidedLift d a w I
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))
  have formula : applyPoly (characteristic p d a) (twoSided d a w I) m =
      q (∑ j ∈ Finset.range (d+1), (A j:ℝ)*V (m+j)) := by
    rw [characteristic,applyPoly_sum,map_sum];apply Finset.sum_congr rfl;intro j _
    rw [applyPoly_monomial,←zsmul_eq_mul, map_zsmul];rfl
  rw [formula]
  cases m with
  | ofNat m =>
    change q (∑ j ∈ Finset.range (d+1), (A j:ℝ)*rightLift d A w (m+j)) = 0
    rw [rightLift_recurrence d A w ha,map_zero]
  | negSucc n =>
    have eq (j : ℕ) (hj : j < d) : V (Int.negSucc n+((j+1:ℕ):ℤ)) = pathState d (fun i ↦ (a i:ℝ)) p w I n j := by
      rw [show Int.negSucc n+((j+1:ℕ):ℤ)=(j:ℤ)-n by omega];exact (state_eq_lift d a w I n j hj).symm
    have sum : (∑ j ∈ Finset.range d, (A (j+1):ℝ)*V (Int.negSucc n+((j+1:ℕ):ℤ))) =
        ∑ j ∈ Finset.range d, (a j:ℝ)*pathState d (fun i ↦ (a i:ℝ)) p w I n j :=
      Finset.sum_congr rfl (fun j hj ↦ by rw [eq j (Finset.mem_range.mp hj)];rfl)
    rw [Finset.sum_range_succ',sum,Nat.cast_zero,add_zero]
    change q (_+(p:ℝ)*(((I n).val-_)/(p:ℝ)))=0
    have pos : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    rw [mul_comm (p:ℝ) _,div_mul_cancel₀ _ pos,add_sub_cancel]
    change (↑(((I n).val:ℕ):ℝ):UnitAddCircle)=0
    have zz := AddCircle.coe_zsmul (p:=(1:ℝ)) (n:=((I n).val:ℤ)) (x:=(1:ℝ))
    simpa only [zsmul_eq_mul,Int.cast_natCast,mul_one,AddCircle.coe_period,smul_zero] using zz

theorem twoSided_mem {b : ℝ} (hb : b ≠ 0) {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (ha : coefficient p a d ≠ 0) (generator : ∀ Q : ℤ[X], aeval b Q=0 → characteristic p d a ∣ Q)
    (w : ℕ → ℝ) (I : ℕ → Fin p) : twoSided d a w I ∈ phaseGroup b :=
  phaseGroup_of_recurrence hb _ generator _ (twoSided_recurrence hp d a ha w I)

end Weierstrass.Branch
