module

public import Weierstrass.BranchIncrementCap
public import Weierstrass.BranchGrid

/-! A retained moment for every translated environment of the original solenoid. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators Topology
namespace Weierstrass.Branch
local instance momentGroupMs (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _
local instance momentGroupBorel (b : ℝ) : BorelSpace (phaseGroup b) := ⟨rfl⟩

def prefixRadius (g T A : ℝ) := 2*(slopeError g*T+((1-g)⁻¹+A/(T*(2*Real.pi*g))))+(1-g)⁻¹

theorem measurable_aux_phase {b : ℝ} (hb : b ≠ 0) (E : PrimitiveEquation b) (z : PhaseTorus) :
    Measurable (fun v : (Fin (E.d+1) → UnitAddCircle) × ℝ ↦ z+(auxiliary hb E v.1 v.2).val) :=
  measurable_const.add (continuous_subtype_val.measurable.comp (auxiliary_measurable hb E))

theorem grid_retained_moment {b l h s : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl1 : l < 1) (E : PrimitiveEquation b)
    (G : WindowGrid (b*l)⁻¹ b⁻¹ h s) (z : PhaseTorus) {T A : ℝ} (hT : 0<T) (hA : 0<A) (m : ℕ)
    (good : Set ((Fin (E.d+1) → UnitAddCircle) × ℝ)) (mg : MeasurableSet good)
    (keep : ∀ v ∈ good, ∀ i<G.K, ∀ j<G.L, goodStep (positive_digits E) (E.d+1) E.a (b*l)⁻¹ b⁻¹
      (prefixRadius (b*l)⁻¹ T A) (centralLift v.1) (angularTail z) (uniformCode E.p (positive_digits E) v.2)
      (G.depth i j m) (G.step i j m) (ENNReal.ofReal ((((b*l)⁻¹)^(G.step i j m):ℝ)^G.σ))) :
    (∫⁻ v, good.indicator (fun v ↦ occupation b l T A (G.q^m) (z+(auxiliary (zero_lt_one.trans hb).ne' E v.1 v.2).val)) v
      ∂centerAndSeed (E.d+1)) ≤ ENNReal.ofReal ((2*T*(G.K+1))*(G.q^m)^G.e) := by
  let W := Fin (E.d+1) → UnitAddCircle
  let X := W × ℝ
  let μ := centerAndSeed (E.d+1)
  let γ := (b*l)⁻¹
  let D := prefixRadius γ T A
  let r := G.q^m
  let t (i : ℕ) := T*G.edge i m
  let c (i : ℕ) := Icc (-(t i)) (t i)
  let B (i : Fin G.K) := {u : ℝ | t (i+1) ≤ |u| ∧ |u| ≤ t i}
  let q (i j : ℕ) := (γ^(G.step i j m))^G.σ
  let Q (i : Fin G.K) := ∏ j ∈ Finset.range G.L, ENNReal.ofReal (q i j)
  let env (v : X) := z+(auxiliary (zero_lt_one.trans hb).ne' E v.1 v.2).val
  let H := {p : X × ℝ | p.2∈Icc (-T) T ∧ |circleIncrement b l (env p.1) p.2| ≤ A*r}
  let S := {p : X × ℝ | p.1∈good ∧ p∈H}
  have mr := measurable_aux_phase (zero_lt_one.trans hb).ne' E z
  have mH : MeasurableSet H := (measurable_snd measurableSet_Icc).inter (measurableSet_le (continuous_abs.measurable.comp
    ((measurable_circleIncrement b l).comp ((mr.comp measurable_fst).prodMk measurable_snd))) measurable_const)
  have mS : MeasurableSet S := (measurable_fst mg).inter mH
  have mB (i : Fin G.K) : MeasurableSet (B i) := (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)
  have mId : (∫⁻ v, good.indicator (fun v ↦ occupation b l T A r (env v)) v ∂μ) = (μ.prod volume) S := by
    rw [Measure.prod_apply mS]
    apply lintegral_congr;intro v
    by_cases hv : v∈good
    · rw [indicator_of_mem hv];apply congrArg (fun e : Set ℝ ↦ volume e);ext u;exact ⟨(fun p ↦ ⟨hv,p⟩),And.right⟩
    · rw [indicator_of_notMem hv,show Prod.mk v ⁻¹' S = ∅ from Set.eq_empty_iff_forall_notMem.mpr (fun _ p ↦ hv p.1),measure_empty]
  change (∫⁻ v, good.indicator (fun v ↦ occupation b l T A r (env v)) v ∂μ) ≤ _
  rw [mId]
  have cover (x : X × ℝ) (hx : x∈S) : x.2 ∈ c G.K ∨ ∃ i, x.2 ∈ B i := by
    have hu : |x.2| ≤ T := abs_le.mpr hx.2.1
    rcases G.locate m ((div_le_one hT).mpr hu) with h₀ | ⟨i,hi,lo,up⟩
    · exact Or.inl (abs_le.mp (by simpa only [t,mul_comm T] using (div_le_iff₀ hT).mp h₀))
    · right;refine ⟨⟨i,hi⟩,?_,?_⟩
      · simpa only [t,mul_comm T] using ((lt_div_iff₀ hT).mp lo).le
      · simpa only [t,mul_comm T] using (div_le_iff₀ hT).mp up
  have bp := zero_lt_one.trans hb
  have gp : 0<γ := inv_pos.mpr (mul_pos bp ((inv_pos.mpr bp).trans hl))
  have rp : 0<r := pow_pos G.q_pos m
  have wsz (i : Fin G.K) (u : ℝ) (hu : u∈B i) : μ ((fun v ↦ (v,u)) ⁻¹' S) ≤ Q i := by
    change ((volume : Measure W).prod unitLaw) _ ≤ _
    rw [Measure.prod_apply (measurable_prodMk_right mS)]
    let _ : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
    have ub : |u| ≤ T := by
      have tm : Antitone (fun j ↦ G.edge j m) := antitone_nat_of_succ_le (fun j ↦ G.edge_anti j m)
      exact hu.2.trans (by dsimp [t];simpa only [G.edge_zero,mul_one] using mul_le_mul_of_nonneg_left (tm (Nat.zero_le i.val)) hT.le)
    let n j := G.depth i j m
    let k j := G.step i j m
    have adv (j) (hj : j<G.L) : n j+k j=n (j+1) := G.advance i i.isLt j hj m
    have mono (s t : ℕ) (hs : s≤t) (ht : t≤G.L) : n s≤n t := by
      induction t,hs using Nat.le_induction with
      | base => exact le_rfl
      | succ t _ ih => exact (ih (by omega)).trans (by rw [←adv t (by omega)];omega)
    have cap (w : W) := anchored_band_cap hb hl hl1 E z w hT hA (G.edge_pos (i+1) m) ub hu.1 n k (fun j ↦ ENNReal.ofReal (q i j)) G.L (n G.L)
      (fun a b hab hb ↦ (adv a (by omega)) ▸ mono (a+1) b (by omega) hb.le)
      (fun j hj ↦ (adv j hj) ▸ mono (j+1) G.L (by omega) le_rfl)
      (fun j hj ↦ G.physical i i.isLt j hj m)
      (by simpa only [mul_comm] using (div_le_iff₀ (G.edge_pos (i+1) m)).mp (G.terminal i i.isLt m)) D le_rfl
    apply (lintegral_mono (g:=fun _ : W ↦ Q i) ?_).trans_eq (by simp)
    intro w
    apply le_trans _ (cap w)
    apply measure_mono;intro x hx
    exact ⟨fun j hj ↦ keep (w,x) hx.1 i i.isLt j hj,hx.2.2⟩
  apply (integral_bands μ S mS _ B mB Q cover wsz).trans
  have outer (i : ℕ) : volume (c i) = ENNReal.ofReal (2*t i) := by unfold c;rw [Real.volume_Icc];congr 1;ring
  have unit (i : Fin G.K) : volume (B i)*Q i ≤ ENNReal.ofReal (2*T*r^G.e) := by
    have mono := measure_mono (μ:=volume) (show B i ⊆ c i from fun _ hu ↦ abs_le.mp hu.2)
    apply (mul_le_mul_of_nonneg_right mono bot_le).trans
    rw [outer]
    have nonneg (j) : 0 ≤ q i j := Real.rpow_nonneg (pow_nonneg gp.le _) _
    rw [show Q i=ENNReal.ofReal (∏ j ∈ Finset.range G.L,q i j) from (ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ nonneg j)).symm,
      ←ENNReal.ofReal_mul (by dsimp [t];exact mul_nonneg (by norm_num) (mul_nonneg hT.le (G.edge_pos i m).le) : 0≤2*t i)]
    apply ENNReal.ofReal_le_ofReal
    calc _ = (2*T)*(G.edge i m*∏ j ∈ Finset.range G.L,q i j) := by unfold t;ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (G.cost i i.isLt m) (by positivity)
  have center : volume (c G.K) ≤ ENNReal.ofReal (2*T*r^G.e) := by
    rw [outer];apply ENNReal.ofReal_le_ofReal
    exact (by simpa only [t,←mul_assoc] using mul_le_mul_of_nonneg_left (G.center m) (show 0≤2*T by positivity))
  apply (add_le_add center (Finset.sum_le_sum (fun i _ ↦ unit i))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  have epos : 0≤2*T*r^G.e := mul_nonneg (by positivity) (Real.rpow_nonneg rp.le _)
  rw [nsmul_eq_mul,←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ G.K),←ENNReal.ofReal_add epos (mul_nonneg (Nat.cast_nonneg _) epos)]
  congr 1;ring

end Weierstrass.Branch
