module

public import Weierstrass.PrimitiveEquation
public import Weierstrass.PairGraph

/-! All real bases split into the transcendental, branching, or conjugate
case. A small constant coefficient forces an actual complex conjugate of
modulus strictly between zero and one, also for a nonmonic polynomial. -/
@[expose] public noncomputable section
open Set MeasureTheory Polynomial
namespace Weierstrass
namespace PrimitiveEquation

private theorem roots_norm_ge_one (S : Multiset ℂ) (h : ∀ z ∈ S, 1 ≤ ‖z‖) : 1 ≤ ‖S.prod‖ := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    rw [Multiset.prod_cons,norm_mul]
    exact one_le_mul_of_one_le_of_one_le (h z (Multiset.mem_cons_self ..)) (ih (fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)))

theorem complex_root {b : ℝ} (E : PrimitiveEquation b) : aeval (b:ℂ) E.P = 0 := by
  have H := aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) b E.P
  change aeval (b:ℂ) E.P = ((aeval b E.P:ℝ):ℂ) at H
  simpa [E.root] using H

/-- The product of the remaining root moduli is bounded by the positive
constant coefficient divided by b. No monicity or integrality assumption. -/
theorem contracting_root {b : ℝ} (E : PrimitiveEquation b) (hb : 0 < b) (small : (E.p:ℝ)<b) :
    ∃ c : ℂ, 0 < ‖c‖ ∧ ‖c‖ < 1 ∧ aeval c E.P = 0 := by
  let R := E.P.map (algebraMap ℤ ℂ)
  have emf : Function.Injective (algebraMap ℤ ℂ) := FaithfulSMul.algebraMap_injective _ _
  have R0 : R ≠ 0 := fun h ↦ E.primitive.ne_zero ((map_injective _ emf).eq_iff.mp (h.trans (Polynomial.map_zero _).symm))
  have rb : (b:ℂ) ∈ R.roots := (mem_roots R0).mpr (by simpa only [R,IsRoot,eval_map_algebraMap] using E.complex_root)
  obtain ⟨S,hs⟩ := Multiset.exists_cons_of_mem rb
  have cc : R.coeff 0 = (E.p:ℂ) := by dsimp only [R];rw [coeff_map,←E.constant];simp
  have lc : R.leadingCoeff = (E.P.leadingCoeff:ℂ) := leadingCoeff_map_of_injective emf _
  have na : E.P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr E.primitive.ne_zero
  have ao : 1 ≤ ‖R.leadingCoeff‖ := by
    rw [lc,Complex.norm_intCast,← Int.cast_abs]
    exact_mod_cast (show (1:ℤ) ≤ |E.P.leadingCoeff| by have h := abs_pos.mpr na;omega)
  have pc := congrArg (fun z : ℂ ↦ ‖z‖) ((IsAlgClosed.splits R).coeff_zero_eq_leadingCoeff_mul_prod_roots)
  simp only [cc,hs,Multiset.prod_cons,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb,Complex.norm_natCast] at pc
  have om : ∃ c ∈ S, ‖c‖<1 := by
    by_contra! bad
    have L := one_le_mul_of_one_le_of_one_le ao (roots_norm_ge_one S bad)
    have bb := mul_le_mul_of_nonneg_right L hb.le
    nlinarith only [bb,pc,small]
  obtain ⟨c,cm,c1⟩ := om
  have belongs : c ∈ R.roots := by rw [hs];exact Multiset.mem_cons_of_mem cm
  have rtc := isRoot_of_mem_roots belongs
  have cn : c ≠ 0 := by
    intro z;subst c
    have hzero := coeff_zero_eq_zero_of_zero_isRoot rtc
    rw [cc] at hzero
    have hp : 0 < E.p := by exact_mod_cast (show (0:ℤ)<(E.p:ℤ) by rw [E.constant];exact E.constant_pos)
    exact (Nat.cast_ne_zero.mpr hp.ne' : (E.p:ℂ) ≠ 0) hzero
  exact ⟨c,norm_pos_iff.mpr cn,c1,by simpa only [R,IsRoot,eval_map_algebraMap] using rtc⟩

/-- Two roots of this integer polynomial define injective homomorphisms of
one field. The distinguished field element has precisely the given images. -/
theorem conjugate_anchored {b g : ℝ} (E : PrimitiveEquation b) (hb : 1<b) (hg : b⁻¹<g) (hg1 : g<1)
    (small : (E.p:ℝ)<b*g) (D : ConjugatePair.AllDifferentiationRules) : AnchoredEstimate b g 1 := by
  have bp := zero_lt_one.trans hb
  obtain ⟨c,p₀,p₁,croot⟩ := E.contracting_root bp (small.trans (by simpa using mul_lt_mul_of_pos_left hg1 bp))
  let f := E.P.map (algebraMap ℤ ℚ)
  let : Fact (Irreducible f) := ⟨E.irreducible⟩
  have lift (z : ℂ) (hz : aeval z E.P = 0) : f.eval₂ (algebraMap ℚ ℂ) z = 0 :=
    (aeval_map_algebraMap ℚ z E.P).trans hz
  let σ := AdjoinRoot.lift (algebraMap ℚ ℂ) (b:ℂ) (lift _ E.complex_root)
  let τ := AdjoinRoot.lift (algebraMap ℚ ℂ) c (lift _ croot)
  have bb : σ (AdjoinRoot.root f) = (b:ℂ) := AdjoinRoot.lift_root _
  have ccc : τ (AdjoinRoot.root f) = c := AdjoinRoot.lift_root _
  exact anchored_of_contracting_conjugate σ τ _ bb hb (ccc ▸ p₀) (ccc ▸ p₁) hg hg1 D

end PrimitiveEquation

/-- The exact remaining analytic input for bases with enough predecessors. -/
def BranchingAnchoredRule : Prop := ∀ {b g : ℝ}, 1 < b → b⁻¹ < g → g < 1 →
  ∀ (E : PrimitiveEquation b), 2 ≤ E.p → b*g ≤ E.p → AnchoredEstimate b g 1

/-- Exhaustive assembly of Theorem 1.1. Both named arguments are analytic
statements; there is no exceptional real base in the algebraic dichotomy. -/
theorem main_of_analytic_inputs (D : ConjugatePair.AllDifferentiationRules) (A : BranchingAnchoredRule) : MainStatement := by
  intro b g hb hg hg1 phase I hc hi
  by_cases ht : Transcendental ℤ b
  · exact graph_and_measure_transcendental hb hg hg1 ht phase I hc hi
  have alg : IsAlgebraic ℤ b := of_not_not ht
  obtain ⟨E⟩ := primitiveEquation_nonempty (zero_lt_one.trans hb).ne' alg
  apply graph_of_anchored_estimate hb hg hg1 _ phase I hc hi
  rcases lt_or_ge (E.p:ℝ) (b*g) with small|large
  · exact E.conjugate_anchored hb hg hg1 small D
  · have bp := zero_lt_one.trans hb
    have bg : 1 < b*g := by simpa only [mul_inv_cancel₀ bp.ne'] using mul_lt_mul_of_pos_left hg bp
    have p2 : 1 < E.p := by exact_mod_cast bg.trans_le large
    exact A hb hg hg1 E p2 large

end Weierstrass
