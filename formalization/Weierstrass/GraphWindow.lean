module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The window used in Appendix A, between horizontal and vertical depth K. -/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace Weierstrass.GraphWindow

def left (q : ℕ) (d : ℝ) (K : ℕ) : ℕ := ⌈(K:ℝ)/((q:ℝ)*d)⌉₊
def right (q : ℕ) (a : ℝ) (K : ℕ) : ℕ := ⌊(K:ℝ)/((q:ℝ)*a)⌋₊

theorem horizontal_depth {q K i : ℕ} {d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hi : left q d K ≤ i) : K ≤ ⌈d*(q*i:ℕ)⌉₊ := by
  have h : (K:ℝ)/((q:ℝ)*d) ≤ i := Nat.le_of_ceil_le hi
  have hf := (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hq) hd)).mp h
  have hcast := Nat.le_ceil (d*(q*i:ℕ))
  push_cast at hcast ⊢
  exact_mod_cast (show (K:ℝ) ≤ ⌈d*((q:ℝ)*i)⌉₊ by nlinarith only [hf,hcast])

theorem vertical_depth {q K i : ℕ} {a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hi : i ≤ right q a K) : ⌊a*(q*i:ℕ)⌋₊ ≤ K := by
  apply Nat.floor_le_of_le
  have h := (Nat.cast_le (α:=ℝ)).mpr hi
  have f := Nat.floor_le (show 0 ≤ (K:ℝ)/((q:ℝ)*a) by positivity)
  change (i:ℝ) ≤ (⌊(K:ℝ)/((q:ℝ)*a)⌋₊:ℝ) at h
  have hh := (le_div_iff₀ (mul_pos (Nat.cast_pos.mpr hq) ha)).mp (h.trans f)
  push_cast
  linarith only [hh]

theorem vertical_strictMono {q : ℕ} {a : ℝ} (h : 1 ≤ q*a) :
    StrictMono (fun i : ℕ ↦ ⌊a*(q*i:ℕ)⌋₊) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have qa : 0 ≤ (q:ℝ)*a := by linarith
  have hf : (⌊a*(q*i:ℕ)⌋₊:ℝ) ≤ a*(q*i:ℕ) := by
    apply Nat.floor_le
    push_cast
    calc
      _ = ((q:ℝ)*a)*i := by ring
      _ ≥ 0 := mul_nonneg qa (Nat.cast_nonneg _)
  change _+1 ≤ _
  apply Nat.le_floor
  push_cast at hf ⊢
  nlinarith only [hf,h]

theorem endpoint_limits {q : ℕ} {a d : ℝ} (hq : 0 < q) (ha : 0 < a) (had : a < d) :
    Tendsto (left q d) atTop atTop ∧ Tendsto (right q a) atTop atTop ∧
    (∀ᶠ K in atTop, left q d K < right q a K) ∧
    Tendsto (fun K ↦ ((right q a K-left q d K:ℕ):ℝ)/K) atTop
      (𝓝 ((q*a)⁻¹-(q*d)⁻¹)) ∧
    Tendsto (fun K ↦ (left q d K:ℝ)/((right q a K-left q d K:ℕ):ℝ)) atTop
      (𝓝 ((q*d)⁻¹/((q*a)⁻¹-(q*d)⁻¹))) ∧
    Tendsto (fun K ↦ (right q a K:ℝ)/((right q a K-left q d K:ℕ):ℝ)) atTop
      (𝓝 ((q*a)⁻¹/((q*a)⁻¹-(q*d)⁻¹))) := by
  have hqa : 0 < (q:ℝ)*a := mul_pos (Nat.cast_pos.mpr hq) ha
  have hqd : 0 < (q:ℝ)*d := mul_pos (Nat.cast_pos.mpr hq) (ha.trans had)
  have ltInv : ((q:ℝ)*d)⁻¹ < ((q:ℝ)*a)⁻¹ :=
    inv_lt_inv₀ hqd hqa |>.mpr (mul_lt_mul_of_pos_left had (Nat.cast_pos.mpr hq))
  have lc : Tendsto (fun K : ℕ ↦ (left q d K:ℝ)/K) atTop (𝓝 ((q*d)⁻¹)) := by
    simpa only [left,div_eq_inv_mul,Function.comp_def] using
      ((tendsto_nat_ceil_mul_div_atTop (inv_nonneg.mpr hqd.le)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have rc : Tendsto (fun K : ℕ ↦ (right q a K:ℝ)/K) atTop (𝓝 ((q*a)⁻¹)) := by
    simpa only [right,div_eq_inv_mul,Function.comp_def] using
      ((tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hqa.le)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have ord : ∀ᶠ K in atTop, left q d K < right q a K := by
    filter_upwards [lc.eventually_lt rc ltInv, eventually_gt_atTop (0:ℕ)] with K hk hK
    exact_mod_cast ((div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hK : 0 < (K:ℝ))).mp hk)
  have width : Tendsto (fun K ↦ ((right q a K-left q d K:ℕ):ℝ)/K) atTop
      (𝓝 ((q*a)⁻¹-(q*d)⁻¹)) := by
    apply (rc.sub lc).congr'
    filter_upwards [ord] with K hK
    simp only [Nat.cast_sub hK.le,sub_div]
  have trend (t : ℝ) (ht : 0 < t) : Tendsto (fun K : ℕ ↦ (K:ℝ)/t) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const ht
  refine ⟨tendsto_nat_ceil_atTop.comp (trend _ hqd),tendsto_nat_floor_atTop.comp (trend _ hqa),
    ord,width,?_,?_⟩
  all_goals
    first | apply (lc.div width (sub_pos.mpr ltInv).ne').congr' |
            apply (rc.div width (sub_pos.mpr ltInv).ne').congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with K hK
    have h : (K:ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
    simp [div_div_div_cancel_right₀,h]

end Weierstrass.GraphWindow
