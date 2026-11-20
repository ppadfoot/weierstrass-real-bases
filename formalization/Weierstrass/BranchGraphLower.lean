module

public import Weierstrass.BranchAnchor
public import Weierstrass.GraphInformationLower

/-! Appendix B's lower bound at the exact predecessor exponent in every
interval and for every prescribed phase sequence. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped ENNReal
namespace Weierstrass.Branch

theorem predecessor_graph_lower {b l : ℝ} (hb : 1<b) (hl : b⁻¹<l) (hl1 : l<1)
    (E : PrimitiveEquation b) (digits : 2≤E.p) (phase : ℕ → ℝ) {I : Set ℝ} (hi : (interior I).Nonempty) :
    ENNReal.ofReal (1+slopeExponent E.p (b*l)⁻¹*(1-alpha b l)) ≤ dimH (graph b l phase I) := by
  have bp := zero_lt_one.trans hb
  have bg := (inv_lt_iff_one_lt_mul₀' bp).mp hl
  have dp : (1:ℝ)<E.p := by exact_mod_cast (show 1<E.p by omega)
  have q : 0<slopeExponent E.p (b*l)⁻¹ := by
    unfold slopeExponent;rw [one_div,inv_inv]
    exact lt_min zero_lt_one (div_pos (Real.log_pos dp) (Real.log_pos bg))
  exact graph_lower_of_anchored_information hb hl hl1 q (min_le_left ..) (predecessor_anchored hb hl hl1 E digits) phase hi

end Weierstrass.Branch
