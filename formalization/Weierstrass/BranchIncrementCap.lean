module

public import Weierstrass.BranchBands

/-! Conditional contraction applied to the exact increment seen in each physical band. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators Topology
namespace Weierstrass.Branch

theorem anchored_band_cap {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl1 : l < 1) (E : PrimitiveEquation b)
    (z : PhaseTorus) (w : Fin (E.d+1) → UnitAddCircle)
    {u U A r edge : ℝ} (hU : 0<U) (hA : 0<A) (hEdge : 0<edge) (hu : |u|≤U) (far : U*edge ≤ |u|)
    (n k : ℕ → ℕ) (q : ℕ → ℝ≥0∞) (L F : ℕ)
    (order : ∀ i j, i<j → j<L → n i+k i ≤ n j) (final : ∀ i<L,n i+k i ≤ F)
    (small : ∀ i<L, (b⁻¹)^(n i) ≤ (b*l)⁻¹^(k i)) (scale : r ≤ edge*(b*l)⁻¹^F)
    (D : ℝ)
    (hD : 2*(slopeError (b*l)⁻¹*U+((1-(b*l)⁻¹)⁻¹+A/(U*(2*Real.pi*(b*l)⁻¹))))+(1-(b*l)⁻¹)⁻¹ ≤ D) :
    unitLaw {x | let I := uniformCode E.p (positive_digits E) x
      (∀ i<L, goodStep (positive_digits E) (E.d+1) E.a (b*l)⁻¹ b⁻¹ D (centralLift w) (angularTail z) I (n i) (k i) (q i)) ∧
      |circleIncrement b l (z+(auxiliary (zero_lt_one.trans hb).ne' E w x).val) u| ≤ A*r} ≤ ∏ i ∈ Finset.range L,q i := by
  let g := (b*l)⁻¹
  let c := b⁻¹
  let H := 2*Real.pi*g
  let B := A/(U*H)
  let P := future b l u (E.d+1) E.p E.a (centralLift w) z
  have hb0 := zero_lt_one.trans hb
  have hl0 := (inv_pos.mpr hb0).trans hl
  have hg : 0<g := inv_pos.mpr (mul_pos hb0 hl0)
  have hg1 : g<1 := inv_lt_one_of_one_lt₀ ((inv_lt_iff_one_lt_mul₀' hb0).mp hl)
  have hc : 0 ≤ c := (inv_pos.mpr hb0).le
  have hc1 : c ≤ 1 := (inv_lt_one_of_one_lt₀ hb).le
  have hH : 0<H := by dsimp [H];positivity
  have hu0 : 0 < |u| := lt_of_lt_of_le (mul_pos hU hEdge) far
  have hB : 0≤B := (div_pos hA (mul_pos hU hH)).le
  have hi (i : ℕ) (h : i<L) : |c^(n i)*u| ≤ U*g^(k i) := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hc _),mul_comm U]
    exact mul_le_mul (small i h) hu (abs_nonneg u) (pow_nonneg hg.le _)
  apply le_trans _ (retained_window_cap (positive_digits E) (E.d+1) E.a hg hg1 hc hc1 (centralLift w)
    (angularTail z) u U (P/(u*H)) hB n k q L F order final hi hD)
  apply measure_mono;intro x hx
  refine ⟨hx.1,?_⟩
  have hit := hx.2
  rw [increment_split hb hl hl1 E] at hit
  let S := fullSecant (E.d+1) (fun j ↦ (E.a j:ℝ)) E.p g c (centralLift w) (angularTail z) (uniformCode E.p (positive_digits E) x) u
  change |P-u*H*S| ≤ A*r at hit
  change |S-P/(u*H)| ≤ B*g^F
  have neq : u*H ≠ 0 := mul_ne_zero (abs_pos.mp hu0) hH.ne'
  have eid : (S-P/(u*H))*(u*H) = -(P-u*H*S) := by rw [sub_mul,div_mul_cancel₀ _ neq];ring
  have pos : 0 < |u*H| := abs_pos.mpr neq
  apply le_of_mul_le_mul_right (a:=|u*H|) _ pos
  rw [←abs_mul,eid,abs_neg,abs_mul,abs_of_pos hH]
  apply hit.trans
  have hbound : A*r ≤ A*(edge*g^F) := mul_le_mul_of_nonneg_left scale hA.le
  have idB : B*(U*H)=A := div_mul_cancel₀ _ (mul_pos hU hH).ne'
  have sf := mul_le_mul_of_nonneg_right far hH.le
  have ef := mul_le_mul_of_nonneg_left sf (mul_nonneg hB (pow_nonneg hg.le F))
  calc
    A*r ≤ A*(edge*g^F) := hbound
    _ = B*g^F*(U*edge*H) := by rw [←idB];ring
    _ ≤ B*g^F*(|u| * H) := ef

end Weierstrass.Branch
