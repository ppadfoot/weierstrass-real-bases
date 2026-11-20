module

public import Weierstrass.EqualPair

/-! Physical conclusions for conjugate embeddings. If one multiplier is
real, all nontrivial angular weights come from the other one, regardless
of whether its rotation has finite order. -/
@[expose] public noncomputable section
open Set MeasureTheory Real
namespace Weierstrass
open Angular CriticalRay ConjugatePair

private theorem one_physical {b : ℝ} (hb : 0 < b) (ζ v : Circle) :
    ((fun _ ↦ 1),fun _ ↦ 1) ∈ physicalFamily (b:ℂ) ζ v 0 := by
  refine ⟨⟨weight_one ..,weight_one ..⟩,?_⟩
  intro x
  have eq : rayProjection (b:ℂ) 1 = fun _ ↦ 1 := by
    funext j; simp [rayProjection,abs_of_pos hb,hb.ne']
  rw [←eq]
  exact transverseOrbit_mem (RingHom.id ℂ) (RingHom.id ℂ) (b:ℂ) (by change (b:ℂ) ≠ 0;exact_mod_cast hb.ne') 1 x

/-- Complete graph and measure conclusions on the full equal-rate branch,
including every nonreal contracting image of reciprocal modulus. -/
theorem graph_and_measure_reciprocal_conjugate {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K)
    {b g : ℝ} (hσ : σ a = (b:ℂ)) (hb : 1 < b) (rate : ‖τ a‖=b⁻¹)
    (hg : b⁻¹ < g) (hg1 : g < 1) (phase : ℕ → ℝ) (I : Set ℝ) (hI : I.OrdConnected)
    (hi : (interior I).Nonempty) :
    dimH (graph b g phase I) = ENNReal.ofReal (2-alpha b g) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b g phase I) (2-alpha b g)) := by
  have bp := zero_lt_one.trans hb
  have nb : ‖σ a‖=b := by simp [hσ,abs_of_pos bp]
  have cn : τ a ≠ 0 := norm_pos_iff.mp (rate ▸ inv_pos.mpr bp)
  let ζ := rotation (τ a) cn
  obtain ⟨v,base⟩ := exists_admissibleBase ζ
  have ew : Weight ζ v 1 (rayProjection (τ a) v) := Weight.rayProjection cn v v (permitted_base _ _)
  have ew' : Weight ζ v 1 (rayProjection (σ a)⁻¹ 1) := by
    apply Weight.of_abs_eq_one
    rw [hσ,←Complex.ofReal_inv]
    exact abs_real_rayProjection (inv_ne_zero bp.ne') (v:=1) (by norm_num)
  have ray := (ConjugatePair.equal σ τ a (nb ▸ hb) (by rwa [nb]) base v 1 ew ew' (nb ▸ hg) hg1).1 0
  rw [hσ] at ray
  exact graph_of_anchored_estimate hb hg hg1 (anchoredEstimate_of_rayInformation bp.le (one_physical bp ζ v) ray) phase I hI hi

namespace ConjugatePair

def actualOrientation {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K)
    {ζ v : Circle} (bn : σ a ≠ 0) (cn : τ a ≠ 0) (w : ℂ)
    (hw : Weight ζ v 1 (rayProjection (τ a) w)) :
    Orientation (σ a) (τ a) ζ v (log ‖σ a‖) (-log ‖τ a‖) where
  physical := (exp_log (norm_pos_iff.mpr bn)).symm
  stable := by rw [neg_neg,exp_log (norm_pos_iff.mpr cn)]
  direction := w
  weight := hw
  orbit := transverseOrbit_mem σ τ a cn w
  reversal := reversePhase_group_conjugate σ τ a

/-- This argument is precisely the uniform result of §6 over its parameters. -/
def AllDifferentiationRules : Prop := ∀ (B : ℂ) (ζ v : Circle) (ρ : ℝ) (e : ℤ → ℝ),
  DifferentiationRule B ζ v ρ e

/-- All admissible amplitudes at either ordering of distinct expansion
rates. The two transverse directions may be chosen independently in
the common angular family. -/
theorem any_unequal {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K) (hb : 1< ‖σ a‖)
    (c0 : 0 < ‖τ a‖) (c1 : ‖τ a‖ < 1) (rate : -log ‖τ a‖ ≠ log ‖σ a‖)
    {ζ v : Circle} (base : AdmissibleBase ζ v) (w w' : ℂ)
    (ew : Weight ζ v 1 (rayProjection (τ a) w)) (ew' : Weight ζ v 1 (rayProjection (σ a)⁻¹ w'))
    {g : ℝ} (hg : ‖σ a‖⁻¹ < g) (hg1 : g < 1) (D : AllDifferentiationRules) : FamilyBound (σ a) ζ v g 1 := by
  let B := σ a
  let C := τ a
  let L := log ‖B‖
  let M := -log ‖C‖
  have bp := zero_lt_one.trans hb
  have bn := norm_pos_iff.mp bp
  have cn := norm_pos_iff.mp c0
  let o := actualOrientation σ τ a bn cn w ew
  have wra : Weight ζ v 1 (rayProjection (σ a⁻¹) w') := by simpa only [map_inv₀] using ew'
  let r' := actualOrientation τ σ a⁻¹ (by simpa only [map_inv₀] using inv_ne_zero cn)
    (by simpa only [map_inv₀] using inv_ne_zero bn) w' wra
  have r : Orientation C⁻¹ B⁻¹ ζ v M L := by
    simpa only [B,C,M,L,map_inv₀,norm_inv,log_inv,neg_neg] using r'
  have ml : 0<M := neg_pos.mpr (log_neg c0 c1)
  have ll : 0<L := log_pos hb
  have gp := (inv_pos.mpr bp).trans hg
  have ax : 0 < -log g := neg_pos.mpr (log_neg gp hg1)
  have al : -log g<L := by
    have z := (log_lt_log (inv_pos.mpr bp) hg);rw [log_inv] at z;exact neg_lt_of_neg_lt z
  rcases lt_or_gt_of_ne rate with ord|ord
  · have h := (unequal o r base ml ord (D B ζ v ‖C‖ (rayProjection C o.direction))).1 (-log g) ax al
    simpa only [neg_neg,exp_log gp] using h
  · have oo : Orientation (B⁻¹)⁻¹ (C⁻¹)⁻¹ ζ v L M := by simpa only [inv_inv] using o
    have h := (unequal r oo base ll ord (D C⁻¹ ζ v ‖B⁻¹‖ (rayProjection B⁻¹ r.direction))).2 (-log g) ax al
    simpa only [B,inv_inv,neg_neg,exp_log gp] using h

end ConjugatePair

/-- Complete branch for a real expanding base with a contracting conjugate,
conditional only on the single physical differentiation theorem of §6. -/
theorem anchored_of_contracting_conjugate {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K)
    {b g : ℝ} (hσ : σ a=(b:ℂ)) (hb : 1<b) (c0 : 0<‖τ a‖) (c1 : ‖τ a‖<1)
    (hg : b⁻¹ < g) (hg1 : g<1) (D : ConjugatePair.AllDifferentiationRules) : AnchoredEstimate b g 1 := by
  have bp := zero_lt_one.trans hb
  have nb : ‖σ a‖=b := by simp [hσ,abs_of_pos bp]
  have cn := norm_pos_iff.mp c0
  let ζ := rotation (τ a) cn
  obtain ⟨v,base⟩ := exists_admissibleBase ζ
  have ew : Weight ζ v 1 (rayProjection (τ a) v) := Weight.rayProjection cn v v (permitted_base _ _)
  have ew' : Weight ζ v 1 (rayProjection (σ a)⁻¹ 1) := by
    apply Weight.of_abs_eq_one
    rw [hσ,←Complex.ofReal_inv];exact abs_real_rayProjection (inv_ne_zero bp.ne') (v:=1) (by norm_num)
  have bound : FamilyBound (σ a) ζ v g 1 := by
    by_cases h : -log ‖τ a‖=log ‖σ a‖
    · have eq : ‖τ a‖=‖σ a‖⁻¹ := by
        apply (log_injOn_pos (show 0 < ‖τ a‖ from c0) (inv_pos.mpr (nb ▸ bp)))
        rw [log_inv,←h,neg_neg]
      exact (ConjugatePair.equal σ τ a (nb ▸ hb) eq base v 1 ew ew' (nb ▸ hg) hg1).1
    · exact ConjugatePair.any_unequal σ τ a (nb ▸ hb) c0 c1 h base v 1 ew ew' (nb ▸ hg) hg1 D
  rw [hσ] at bound
  exact anchoredEstimate_of_rayInformation bp.le (one_physical bp ζ v) (bound 0)

end Weierstrass
