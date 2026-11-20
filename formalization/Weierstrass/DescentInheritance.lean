module

public import Weierstrass.DescentWordMeasures

/-! Averaging at a rescaled physical child and counting accepted neighboring
branches. The shift acts on the entire compact phase group. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal
namespace Weierstrass.Descent
local instance inheritedGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance inheritedGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem child_haar_mean {B : ℂ} (hB : B ≠ 0) (d : ℤ → ℝ) (ω : PhaseTorus) (n : ℤ) (x : ℝ)
    (f : PhaseTorus → ℝ≥0∞) (mf : Measurable f) :
    (∫⁻ z : complexPhaseGroup B, f (physicalEnvironment ‖B‖ d (ω+z.val) n x) ∂complexPhaseHaar B) =
      ∫⁻ z : complexPhaseGroup B, f (physicalEnvironment ‖B‖ d ω n x+z.val) ∂complexPhaseHaar B := by
  let sh := inducedPhaseMap B B (shiftPhase n) (shiftPhase_group hB n)
  let ξ := physicalEnvironment ‖B‖ d ω n x
  have eq (z : complexPhaseGroup B) : physicalEnvironment ‖B‖ d (ω+z.val) n x = ξ+(sh z).val := by
    funext j;change (ω (j+n)+z.val (j+n))+_ = (ω (j+n)+_)+z.val (j+n);abel
  simp_rw [eq]
  exact (shiftPhase_preserving hB n).lintegral_comp (mf.comp (measurable_const.add continuous_subtype_val.measurable))

theorem status_degree {N : ℕ} (hn : 0 < N) (b g ρ T θ : ℝ) (hθ : 0 ≤ θ) (p : RayParameters) (e : ℤ → ℝ)
    (z : PhaseTorus) (n : ℕ) (a : Bool) (i : Fin N) :
    let bad := badCell b g ρ T θ p e z n (N:=N)
    let G := derivRay b g ρ p.1 p.2 e z
    let W := widthMark b g ρ n
    (∑ j : Fin N, if (bad i = a ∧ bad j=a ∧ ¬ W < |G (anchor T i)-G (anchor T j)|) then (1:ℝ) else 0) ≤
      N*(if a then 1 else θ) := by
  classical
  intro bad G W
  have pos : 0 < (N:ℝ) := by exact_mod_cast hn
  let J := neighbors T G W i
  have row : (∑ j : Fin N, if ¬W < |G (anchor T i)-G (anchor T j)| then (1:ℝ) else 0) = J.card := by
    simp only [not_lt];exact Finset.sum_boole _ _
  by_cases hi : bad i = a
  · refine le_trans (b:=(J.card:ℝ)) ?_ ?_
    · rw [←row];apply Finset.sum_le_sum;intro j _
      split <;> split <;> simp_all
    · cases a with
      | false =>
        have h : ¬ θ < (J.card:ℝ)/N := by simpa [bad,badCell,J,G,W] using hi
        have lo : (J.card:ℝ)/N ≤ θ := le_of_not_gt h
        simpa only [Bool.false_eq_true,if_false,mul_comm θ] using (div_le_iff₀ pos).mp lo
      | true =>
        have num : J.card ≤ N := (Finset.card_le_univ J).trans_eq (Fintype.card_fin N)
        simpa using (show (J.card:ℝ) ≤ N by exact_mod_cast num)
  · cases a <;> simp [hi]
    exact mul_nonneg pos.le hθ

end Weierstrass.Descent
