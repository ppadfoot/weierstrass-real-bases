module

public import Weierstrass.BranchCylinders
public import Weierstrass.BranchLoss

/-! Measurable, prefix-determined marks on the exact inherited path. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators
namespace Weierstrass.Branch

def goodStep {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (n k : ℕ) (q : ℝ≥0∞) :=
  goodPrefix hp d a g c D (pathState d (fun j ↦ (a j:ℝ)) p w I n) (fun j ↦ η (n+j)) (fun j ↦ I (n+j)) k q

theorem measurable_goodStep {X : Type*} [MeasurableSpace X] {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ)
    (g c D : ℝ) (W η : X → ℕ → ℝ) (I : X → ℕ → Fin p) (mW : ∀ j, Measurable fun x ↦ W x j)
    (mη : ∀ j, Measurable fun x ↦ η x j) (mI : ∀ j, Measurable fun x ↦ I x j) (n k : ℕ) (q : ℝ≥0∞) :
    MeasurableSet {x | goodStep hp d a g c D (W x) (η x) (I x) n k q} :=
  measurableSet_goodPrefix hp d a g c D _ _ _ k q (measurable_pathState _ _ _ W I mW mI n)
    (fun j ↦ mη (n+j)) (fun j ↦ mI (n+j))

theorem goodStep_congr {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (w η : ℕ → ℝ)
    {I J : ℕ → Fin p} (n k : ℕ) (q : ℝ≥0∞) (e : ∀ j<n+k,I j=J j) :
    goodStep hp d a g c D w η I n k q ↔ goodStep hp d a g c D w η J n k q := by
  unfold goodStep goodPrefix
  rw [pathState_prefix d (fun j ↦ (a j:ℝ)) p w (I:=I) (J:=J) n (fun j hj ↦ e j (by omega)),
    partialSecant_prefix d (fun j ↦ (a j:ℝ)) p g c _ _ 0 k (I:=fun j ↦ I (n+j)) (J:=fun j ↦ J (n+j)) (fun j hj ↦ e (n+j) (by omega))]

end Weierstrass.Branch
