module

public import Weierstrass.SlopeDimensionUpper
public import Weierstrass.SlopePointwise

/-! Theorem B.1, conditional exact dimensionality at every derivative index. -/
public noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

theorem conditional_slope_exact_dimension {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0<c) (hc' : c<1) (hγ : 0<γ) (hγ' : γ<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (j : ℕ) (η : ℕ → ℝ) :
    let g := γ*c^j
    let ν (w : Fin (d+1) → UnitAddCircle) := baseSlopeLaw (by omega : 0<p) (d+1) a (centralLift w) η g
    ∀ᵐ w, ∀ᵐ y ∂ν w, Tendsto (fun r : ℝ ↦ log ((ν w).real (Icc (y-r) (y+r))) / log r)
      (𝓝[>] 0) (𝓝 (min 1 (log p/log (1/g)))) := by
  intro g ν
  have gp := mul_pos hγ (pow_pos hc j)
  have g1 : g<1 := (mul_le_of_le_one_right hγ.le (pow_le_one₀ hc.le hc'.le)).trans_lt hγ'
  filter_upwards [ae_slope_lower_dimension_all hp a ha hc hc' hγ hγ' hbc hpoly j η] with w hw
  filter_upwards [hw,slope_upper_local_dimension hp (d+1) a (centralLift w) η gp g1] with y lo hi
  apply tendsto_order.mpr
  constructor
  · intro t ht
    obtain ⟨v,tv,vs⟩ := exists_between ht
    exact (lo v vs).mono (fun _ bd ↦ tv.trans_le bd)
  · intro t ht
    obtain ⟨v,sv,vt⟩ := exists_between ht
    exact (hi v sv).mono (fun _ bd ↦ bd.trans_lt vt)

end Weierstrass.Predecessor
