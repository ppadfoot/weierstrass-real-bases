module

public import Weierstrass.Bootstrap
public import Mathlib.Analysis.Normed.Group.Real

public section

namespace Weierstrass.Bootstrap

/-- Instantiates the ordered-field recursion with the actual scalar field of the paper. -/
theorem realArchimedeanIncrements : ArchimedeanIncrements ℝ := by
  intro d hd b
  obtain ⟨n,hn⟩ := exists_nat_ge (b/d)
  refine ⟨n,?_⟩
  have eqn (k : ℕ) : multiple d k = (k : ℝ)*d := by
    induction k with
    | zero => simp [multiple]
    | succ k ih => simp only [multiple, ih, Nat.cast_succ, add_mul, one_mul]
  rw [eqn]
  exact (div_le_iff₀ hd).mp hn

end Weierstrass.Bootstrap
