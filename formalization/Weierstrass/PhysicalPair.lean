module

public import Weierstrass.ReciprocalTransfer
public import Weierstrass.RealBootstrap

/-! The logarithmic unequal-rate recursion on the two actual conjugate Haar models. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Real
namespace Weierstrass.ConjugatePair
open Angular CriticalRay

/-- Every finite angular complexity at one physical amplitude. -/
def FamilyBound (B : ℂ) (ζ v : Circle) (g s : ℝ) : Prop :=
  ∀ k : ℕ, RayInformation B g s (physicalFamily B ζ v k)

theorem strict_family {B : ℂ} {ζ v : Circle} {g s : ℝ} :
    Bootstrap.StrictBound (FamilyBound B ζ v g) s ↔ FamilyBound B ζ v g s := by
  constructor
  · intro bound k h hh hs
    obtain ⟨t,ht,hts⟩ := exists_between hs
    exact bound t (hh.trans ht) hts k h hh ht
  · intro bound h _ hs k t ht hth
    exact bound k t ht (hth.trans hs)

/-- The single-complexity analytic transverse differentiation estimate (D) from §6. -/
def DifferentiationRule (B : ℂ) (ζ v : Circle) (ρ : ℝ) (e : ℤ → ℝ) : Prop :=
  ∀ {g s : ℝ}, 1 < ‖B‖ → 0 < g → g < 1 → 0 < ρ → ρ < 1 → 1 < ‖B‖*(g*ρ) →
    0 < s → s ≤ 1 → Weight ζ v 1 e → (∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) →
    ∀ k : ℕ, RayInformation B (g*ρ) s (physicalFamily B ζ v (k+1)) →
      RayInformation B g (min 1 (log (g*ρ)*s / log g)) (physicalFamily B ζ v k)

/-- A physical expanding conjugate and a transverse contracting conjugate,
with a permitted unit direction on the transverse Haar orbit. -/
structure Orientation (B C : ℂ) (ζ v : Circle) (L M : ℝ) where
  physical : ‖B‖ = exp L
  stable : ‖C‖ = exp (-M)
  direction : ℂ
  weight : Weight ζ v 1 (rayProjection C direction)
  orbit : ∀ x, transverseOrbit ‖C‖ (rayProjection C direction) x ∈ complexPhaseGroup B
  reversal : (complexPhaseGroup B).map reversePhase = complexPhaseGroup C⁻¹

private theorem mulExp (L x : ℝ) : exp L * exp (-x) = exp (L-x) := by rw [← exp_add,sub_eq_add_neg]
private theorem dualExp (L x : ℝ) : (exp L * exp (-x))⁻¹ = exp (-(L-x)) := by rw [mulExp,exp_neg]
private theorem stableExp (x M : ℝ) : exp (-x)*exp (-M)=exp (-(x+M)) := by rw [← exp_add,neg_add]

private theorem Orientation.critical {B C : ℂ} {ζ v : Circle} {L M : ℝ}
    (o : Orientation B C ζ v L M) (base : AdmissibleBase ζ v) (hM : 0 < M)
    {x : ℝ} (hx : 0 < x) (hxL : x < L) (edge : x+M=L) : FamilyBound B ζ v (exp (-x)) 1 := by
  have b1 : 1 < ‖B‖ := by rw [o.physical,one_lt_exp_iff]; linarith
  have c0 : 0 < ‖C‖ := by rw [o.stable]; positivity
  have c1 : ‖C‖ < 1 := by rw [o.stable,exp_lt_one_iff]; linarith
  have crit : exp (-x)*‖B‖*‖C‖=1 := by rw [o.physical,o.stable,←exp_add,←exp_add,exp_eq_one_iff]; linarith
  intro k h hh hhs T A hT hA ε hε
  filter_upwards [rayInformation_critical_family b1 (exp_pos _) (by rw [exp_lt_one_iff]; linarith)
    c0 c1 crit base o.weight o.orbit k h hh hhs T A hT hA ε hε] with r good
  exact fun ω p hp ↦ good ω p hp.1

theorem Orientation.half {B C : ℂ} {ζ v : Circle} {L M : ℝ}
    (o : Orientation B C ζ v L M) (base : AdmissibleBase ζ v) (hM : 0 < M) (hML : M ≤ L)
    {x : ℝ} (hx : 0 < x) (hxL : x < L) (edge : L < x+M) : FamilyBound B ζ v (exp (-x)) (1/2) := by
  intro k
  apply rayInformation_half_family (ρ:=‖C‖) _ (exp_pos _) _ _ _ _ _ _ base o.weight o.orbit k
  · rw [o.physical,one_lt_exp_iff]; linarith
  · rw [exp_lt_one_iff]; linarith
  · rw [o.physical,mulExp,one_lt_exp_iff]; linarith
  · rw [o.stable]; positivity
  · rw [o.stable,exp_lt_one_iff]; linarith
  · rw [o.physical,o.stable,mulExp,← exp_add,exp_lt_one_iff]; linarith
  · rw [o.physical,o.stable,mulExp,← exp_add,← exp_add,one_lt_exp_iff]; linarith

private theorem Orientation.reciprocal {B C : ℂ} {ζ v : Circle} {L M : ℝ}
    (o : Orientation B C ζ v L M) {x s : ℝ} (hx : 0 < x) (hxL : x < L) (edge : L < x+M) (hs : s ≤ 1)
    (source : FamilyBound C⁻¹ ζ v (exp (-(L-x))) s) : FamilyBound B ζ v (exp (-x)) s := by
  have c0 : 0 < ‖C‖ := by rw [o.stable]; positivity
  intro k
  apply Reciprocal.reciprocal_transfer (ρ:=‖C‖) _ (inv_ne_zero (norm_pos_iff.mp c0)) (exp_pos _) _ _ c0 _
    (norm_inv _) o.reversal hs o.weight o.orbit k
  · rw [o.physical,dualExp]; exact source _
  · rw [o.physical,one_lt_exp_iff]; linarith
  · rw [exp_lt_one_iff]; linarith
  · rw [o.physical,mulExp,one_lt_exp_iff]; linarith
  · rw [o.physical,o.stable,dualExp,exp_lt_exp]; linarith

private theorem Orientation.differentiate {B C : ℂ} {ζ v : Circle} {L M : ℝ}
    (o : Orientation B C ζ v L M) (hM : 0 < M)
    (step : DifferentiationRule B ζ v ‖C‖ (rayProjection C o.direction))
    {x s : ℝ} (hx : 0 < x) (edge : x+M<L) (hs : 0<s) (hs1 : s≤1)
    (source : FamilyBound B ζ v (exp (-(x+M))) s) :
    FamilyBound B ζ v (exp (-x)) (Bootstrap.descentExponent x M s) := by
  intro k
  have hq : exp (-x)*‖C‖ = exp (-(x+M)) := by rw [o.stable,stableExp]
  have d := @step (exp (-x)) s (by rw [o.physical,one_lt_exp_iff]; linarith) (exp_pos _)
    (by rw [exp_lt_one_iff]; linarith) (by rw [o.stable]; positivity)
    (by rw [o.stable,exp_lt_one_iff]; linarith) (by rw [hq,o.physical,mulExp,one_lt_exp_iff]; linarith)
    hs hs1 o.weight o.orbit k (by rw [hq]; exact source _)
  rw [hq,log_exp,log_exp,neg_mul,neg_div_neg_eq] at d
  simpa only [Bootstrap.descentExponent,min_def] using d

/-- Both expanding orientations at unequal logarithmic rates, with the one
analytic differentiation operation made explicit. -/
theorem unequal {B C : ℂ} {ζ v : Circle} {L M : ℝ} (o : Orientation B C ζ v L M)
    (r : Orientation C⁻¹ B⁻¹ ζ v M L) (base : AdmissibleBase ζ v) (hM : 0<M) (order : M<L)
    (step : DifferentiationRule B ζ v ‖C‖ (rayProjection C o.direction)) :
    (∀ x, 0<x → x<L → FamilyBound B ζ v (exp (-x)) 1) ∧
    (∀ y, 0<y → y<M → FamilyBound C⁻¹ ζ v (exp (-y)) 1) := by
  have full := Bootstrap.unequalRatePair Bootstrap.realArchimedeanIncrements hM order
    (fun x ↦ FamilyBound B ζ v (exp (-x))) (fun x ↦ FamilyBound C⁻¹ ζ v (exp (-x)))
    (fun _ hx hxL edge ↦ strict_family.mpr (o.critical base hM hx hxL edge))
    (fun _ hx hxL edge ↦ strict_family.mpr (o.half base hM order.le hx hxL edge))
    (fun _ _ hx hxL edge _ hs1 h ↦ strict_family.mpr (o.reciprocal hx hxL edge hs1 (strict_family.mp h)))
    (fun _ _ hy hyM edge _ hs1 h ↦ strict_family.mpr (r.reciprocal hy hyM edge hs1
      (by simpa only [inv_inv] using strict_family.mp h)))
    (fun _ _ hx edge hs hs1 h ↦ strict_family.mpr (o.differentiate hM step hx edge hs hs1 (strict_family.mp h)))
  exact ⟨fun x hx hxL ↦ strict_family.mp (full.1 x hx hxL),fun y hy hyM ↦ strict_family.mp (full.2 y hy hyM)⟩

end Weierstrass.ConjugatePair
