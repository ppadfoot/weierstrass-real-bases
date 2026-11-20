module

public import Weierstrass.DescentDistant
public import Weierstrass.DescentWords

/-! Joint Haar cost of the off-diagonal part of the actual physical partition. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal
namespace Weierstrass.Descent
open Predecessor (unitLaw)
local instance costGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance costGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- Spelling out the two Lebesgue inputs of an individual, probability-normalized child. -/
private theorem cell_pair {N : ℕ} (hN : 0 < N) (i j : Fin N) (b g T : ℝ) (p : RayParameters) (z : PhaseTorus) (r : ℝ) :
    ENNReal.ofReal (Predecessor.collision (cellLaw b g T p z i) (cellLaw b g T p z j) r) =
    (ENNReal.ofReal (N:ℝ)⁻¹*ENNReal.ofReal (N:ℝ)⁻¹)*
    (unitLaw.prod unitLaw) {v : ℝ × ℝ | |ordinate b g T p z (childInput i v.1)-ordinate b g T p z (childInput j v.2)| ≤ r} := by
  let F := ordinate b g T p z
  let band := {xy : ℝ × ℝ | |xy.1-xy.2| ≤ r}
  have mB : MeasurableSet band := PrefixEnergy.band_measurable r
  have mF := ordinate_measurable b g T p z
  have changeCell (l : Fin N) : cellLaw b g T p z l = ENNReal.ofReal (N:ℝ)⁻¹ • unitLaw.map (F ∘ childInput l) := by
    rw [cellLaw,cell_change_variables hN l,Measure.map_smul,Measure.map_map mF (measurable_childInput l)]
  have eq : ENNReal.ofReal (Predecessor.collision (cellLaw b g T p z i) (cellLaw b g T p z j) r) =
      ((cellLaw b g T p z i).prod (cellLaw b g T p z j)) band := ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [eq,changeCell,changeCell,Measure.prod_smul_left,Measure.prod_smul_right,Measure.smul_apply,Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,mul_assoc,Measure.map_prod_map _ _ (mF.comp (measurable_childInput i)) (mF.comp (measurable_childInput j)),
    Measure.map_apply ((mF.comp (measurable_childInput i)).prodMap (mF.comp (measurable_childInput j))) mB]
  rfl

/-- All far pairs combined still cost at most Cₙr. Both child probabilities
are kept in this estimate. In particular the constant is independent of N. -/
theorem haar_off_cost {B : ℂ} (hb : 0 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 1 ≤ T → T ≤ 3 → ∀ (N : ℕ), 0 < N → childLength ‖B‖ T n N ≤ 2 →
    ∀ (p : RayParameters) (e : ℤ → ℝ), (∀ j, |p.1 j| ≤ 1) → (∀ j, |p.2 j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → (∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) → ∀ (ω : PhaseTorus) (r : ℝ), 0 ≤ r →
      (∫⁻ z : complexPhaseGroup B, ∑ i : Fin N, ∑ j : Fin N,
        (if (widthMark ‖B‖ g ρ n < |derivRay ‖B‖ g ρ p.1 p.2 e (ω+z.val) (anchor T i)-derivRay ‖B‖ g ρ p.1 p.2 e (ω+z.val) (anchor T j)|)
          then ENNReal.ofReal (Predecessor.collision (cellLaw ‖B‖ g T p (ω+z.val) i) (cellLaw ‖B‖ g T p (ω+z.val) j) r) else 0)
        ∂complexPhaseHaar B) ≤ ENNReal.ofReal (C*r) := by
  obtain ⟨C,hC,all⟩ := haar_branch_event hb hg hg1 hr hr1 hh n
  refine ⟨C,hC,?_⟩;intro T T1 T3 N hp len p e hc hd he hm ω r r0
  let s := ENNReal.ofReal (N:ℝ)⁻¹
  let μ := complexPhaseHaar B
  let κ := unitLaw.prod unitLaw
  let W := widthMark ‖B‖ g ρ n
  let E (i j : Fin N) := branchEvent (B:=B) g ρ T W r p e ω i j
  have mE (i j : Fin N) : MeasurableSet (E i j) := branchEvent_measurable ..
  let mass (i j : Fin N) (z : complexPhaseGroup B) := κ (Prod.mk z ⁻¹' E i j)
  have mm (i j : Fin N) : Measurable (mass i j) := measurable_measure_prodMk_left (mE i j)
  have slice (i j : Fin N) (z : complexPhaseGroup B) :
      (if W < |derivRay ‖B‖ g ρ p.1 p.2 e (ω+z.val) (anchor T i)-derivRay ‖B‖ g ρ p.1 p.2 e (ω+z.val) (anchor T j)|
       then ENNReal.ofReal (Predecessor.collision (cellLaw ‖B‖ g T p (ω+z.val) i) (cellLaw ‖B‖ g T p (ω+z.val) j) r) else 0) = s*s*mass i j z := by
    split
    next far =>
      rw [cell_pair hp];congr 1;apply congrArg κ;ext v
      change _ ↔ separated T _ W i j ∧ _
      exact ⟨fun h ↦ ⟨far,h⟩,And.right⟩
    next close =>
      have empty : Prod.mk z ⁻¹' E i j = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr;intro v h;exact close h.1
      simp [mass,empty]
  change (∫⁻ z, ∑ i, ∑ j, (if W < _ then _ else _) ∂μ) ≤ _
  simp_rw [slice]
  have A (i j : Fin N) : (∫⁻ z, s*s*mass i j z ∂μ) ≤ s*s*ENNReal.ofReal (C*r) := by
    rw [lintegral_const_mul _ (mm i j),←Measure.prod_apply (mE i j)]
    exact mul_le_mul_right (all T T1 T3 N hp len p e hc hd he hm ω i j r r0) _
  let ff (i : Fin N) (z : complexPhaseGroup B) := ∑ j : Fin N, s*s*mass i j z
  have mf (i : Fin N) : Measurable (ff i) := Finset.measurable_fun_sum _ (fun j _ ↦ measurable_const.mul (mm i j))
  change (∫⁻ z, ∑ i : Fin N, ff i z ∂μ) ≤ _
  rw [lintegral_finsetSum _ (fun i _ ↦ mf i)]
  unfold ff
  have Ii (i : Fin N) : (∫⁻ z, ∑ j : Fin N, s*s*mass i j z ∂μ) = ∑ j : Fin N, ∫⁻ z, s*s*mass i j z ∂μ :=
    lintegral_finsetSum _ (fun j _ ↦ measurable_const.mul (mm i j))
  simp_rw [Ii]
  apply (Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ A i j))).trans_eq
  have Npos : 0 < (N:ℝ) := by exact_mod_cast hp
  have cancel : (N:ℝ≥0∞)*s=1 := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul Npos.le,mul_inv_cancel₀ Npos.ne',ENNReal.ofReal_one]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];calc
    _ = ((N:ℝ≥0∞)*s)*((N:ℝ≥0∞)*s)*ENNReal.ofReal (C*r) := by ring
    _ = _ := by rw [cancel,one_mul,one_mul]

end Weierstrass.Descent
