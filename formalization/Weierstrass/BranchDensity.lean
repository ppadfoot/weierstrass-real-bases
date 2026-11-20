module

public import Weierstrass.DensityCriterion
public import Weierstrass.BranchGridLoss
public import Weierstrass.BranchGrid

/-! The quantitative density alternative for the actual conditional slope laws
and actual restarted prefixes of Appendix B. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Predecessor
open scoped Topology ENNReal NNReal
namespace Weierstrass.Branch

set_option maxHeartbeats 500000 in
/-- A uniform energy constant is only needed after integrating over the
central block. No essential-supremum bound in the central block is assumed. -/
theorem slope_density_heavy {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (g : ℝ) (η : ℕ → ℝ)
    (f : (Fin d → UnitAddCircle) → ℝ → ℝ≥0) (mf : ∀ w, Measurable (f w))
    (law : ∀ᵐ w : Fin d → UnitAddCircle,
      baseSlopeLaw hp d a (centralLift w) η g = volume.withDensity (fun y => (f w y:ℝ≥0∞)))
    {r : ℝ} (rp : 0<r) (A σ : ℝ) :
    slopeHeavy hp d a g η (A*r) (r^σ) ≤
      ENNReal.ofReal (2*A*r^(1-σ))*(∫⁻ w, ∫⁻ y, (f w y:ℝ≥0∞)^2) := by
  let Ω := Fin d → UnitAddCircle
  let F (w : Ω) (x : ℝ) := codedSlope d (fun j ↦ (a j:ℝ)) p g (centralLift w) η (uniformCode p hp x)
  have mF : Measurable (Function.uncurry F) := measurable_coded_sample hp _ a
    (fun z : Ω × ℝ ↦ centralLift z.1) (fun i ↦ (measurable_centralLift d i).comp measurable_fst)
    Prod.snd measurable_snd η g
  have meas : Measurable (fun z : Ω × ℝ ↦ ballMass (baseSlopeLaw hp d a (centralLift z.1) η g)
    (F z.1 z.2) (A*r)) := measurable_ballMass_family hp d a g _ (fun _ ↦ η) _ _
      (fun j ↦ (measurable_centralLift d j).comp measurable_fst) (fun _ ↦ measurable_const) mF
  have mt : MeasurableSet {v : Ω×ℝ | ENNReal.ofReal (r^σ) < unitLaw.map (F v.1)
      (Icc (F v.1 v.2-A*r) (F v.1 v.2+A*r))} := measurableSet_lt measurable_const meas
  have mw (w : Ω) : Measurable (F w) := measurable_coded_sample hp d a (fun _ : ℝ ↦ centralLift w)
    (fun _ => measurable_const) id measurable_id η g
  have ld : ∀ᵐ w ∂(volume : Measure Ω), unitLaw.map (F w) = volume.withDensity (fun y => (f w y:ℝ≥0∞)) := law
  have er (w : Ω) (x : ℝ) : |F w x-F w x| ≤ 0*r := by rw [sub_self,abs_zero,zero_mul]
  have H := averaged_density_bad_prefix (volume : Measure Ω) unitLaw F F f (C:=0) (D:=A) (σ:=σ)
    rp mw mf ld er mt
  change ((volume : Measure Ω).prod unitLaw) {v | ENNReal.ofReal (r^σ) < unitLaw.map (F v.1)
      (Icc (F v.1 v.2-A*r) (F v.1 v.2+A*r))} ≤ _
  simpa only [add_zero] using H

/-- Exponential probability bound for a failed prefix of length k after
any restart n. For the zero phase the same densities work at all n. -/
theorem goodPrefix_density_decay {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {g : ℝ} (hg : 0<g) (h1 : g<1) (c D σ : ℝ) (k n : ℕ) (η : ℕ → ℝ)
    (f : (Fin (d+1) → UnitAddCircle) → ℝ → ℝ≥0) (mf : ∀ w, Measurable (f w))
    (law : ∀ᵐ w : Fin (d+1) → UnitAddCircle, baseSlopeLaw hp (d+1) a (centralLift w)
      (fun j ↦ η (n+j)) g = volume.withDensity (fun y ↦ (f w y:ℝ≥0∞))) :
    ((volume : Measure (Fin (d+1) → UnitAddCircle)).prod unitLaw) {z |
      let I := uniformCode p hp z.2
      let W := pathState (d+1) (fun j ↦ (a j:ℝ)) p (centralLift z.1) I n
      ¬goodPrefix hp (d+1) a g c D W (fun j ↦ η (n+j)) (fun j ↦ I (n+j)) k
        (ENNReal.ofReal ((g^k:ℝ)^σ))} ≤
      ENNReal.ofReal (2*(|D|+(1-g)⁻¹)*(g^k:ℝ)^(1-σ))*(∫⁻ w, ∫⁻ y, (f w y:ℝ≥0∞)^2) :=
  (goodPrefix_loss_le_slopeHeavy hp a ha hg h1 c D σ k n η).trans
    (slope_density_heavy hp a g (fun j ↦ η (n+j)) f mf law (pow_pos hg k) _ σ)

/-- A polynomial bound in the physical radius for all discarded bands and
stages together at zero phase, under exactly the finite averaged energy
condition. It applies to the same array used in the graph proof. -/
theorem grid_density_discard {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {g c h s : ℝ} (hg : 0<g) (hg1 : g<1) (hs : s≤1) (G : WindowGrid g c h s) (D : ℝ)
    (f : (Fin (d+1) → UnitAddCircle) → ℝ → ℝ≥0) (mf : ∀ w, Measurable (f w))
    (law : ∀ᵐ w : Fin (d+1) → UnitAddCircle, baseSlopeLaw hp (d+1) a (centralLift w) (fun _ ↦ 0) g =
      volume.withDensity (fun y ↦ (f w y:ℝ≥0∞)))
    (finite : (∫⁻ w, ∫⁻ y, (f w y:ℝ≥0∞)^2) ≠ ∞) :
    ∃ δ : ℝ, 0<δ ∧ ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ m : ℕ, centerAndSeed (d+1)
      (gridGood hp (d+1) a g c D G.σ (fun _ ↦ 0) (fun (i : Fin G.K) (j : Fin G.L) ↦ G.depth i j)
        (fun (i : Fin G.K) (j : Fin G.L) ↦ G.step i j) m)ᶜ ≤ C*ENNReal.ofReal ((G.q^m:ℝ)^δ) := by
  let θ := 1-G.σ
  have θp : 0<θ := sub_pos.mpr (G.σ_lt.trans_le hs)
  let δ := θ*Real.log g/Real.log G.q
  have logQ := Real.log_neg G.q_pos G.q_lt_one
  have δp : 0<δ := div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg θp (Real.log_neg hg hg1)) logQ
  have scale (m : ℕ) : (g^m:ℝ)^θ=(G.q^m:ℝ)^δ := by
    apply (Real.log_injOn_pos (Real.rpow_pos_of_pos (pow_pos hg _) _)
      (Real.rpow_pos_of_pos (pow_pos G.q_pos _) _))
    rw [Real.log_rpow (pow_pos hg _),Real.log_rpow (pow_pos G.q_pos _),Real.log_pow,Real.log_pow]
    dsimp [δ];field_simp [logQ.ne]
  let I := ∫⁻ w, ∫⁻ y, (f w y:ℝ≥0∞)^2
  let A := 2*(|D|+(1-g)⁻¹)
  have ap : 0≤A := mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr hg1.le)))
  let P := ENNReal.ofReal A*I
  refine ⟨δ,δp,(G.K:ℝ≥0∞)*((G.L:ℝ≥0∞)*P),?_,?_⟩
  · exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top finite))
  intro m
  let S (i : Fin G.K) (j : Fin G.L) := {z : (Fin (d+1) → UnitAddCircle) × ℝ |
    ¬goodStep hp (d+1) a g c D (centralLift z.1) (fun _ ↦ 0) (uniformCode p hp z.2)
      (G.depth i j m) (G.step i j m) (ENNReal.ofReal ((g^(G.step i j m):ℝ)^G.σ))}
  have each (i : Fin G.K) (j : Fin G.L) : centerAndSeed (d+1) (S i j) ≤ P*ENNReal.ofReal ((G.q^m:ℝ)^δ) := by
    have cap := goodPrefix_density_decay hp a ha hg hg1 c D G.σ (G.step i j m) (G.depth i j m)
      (fun _ ↦ 0) f mf law
    apply cap.trans
    have rel := Real.rpow_le_rpow (pow_pos hg (G.step i j m)).le
      (pow_le_pow_of_le_one hg.le hg1.le (G.linear_growth i i.isLt j j.isLt m)) θp.le
    change ENNReal.ofReal (A*_)*I ≤ _
    rw [ENNReal.ofReal_mul ap,mul_right_comm]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (rel.trans_eq (scale m))) P
  have cover : (gridGood hp (d+1) a g c D G.σ (fun _ ↦ 0) (fun (i : Fin G.K) (j : Fin G.L) ↦ G.depth i j)
      (fun (i : Fin G.K) (j : Fin G.L) ↦ G.step i j) m)ᶜ ⊆ ⋃ i, ⋃ j, S i j := by
    intro z hz
    simp only [gridGood,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall] at hz
    obtain ⟨i,j,fail⟩ := hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,fail⟩⟩
  apply (measure_mono cover).trans ((measure_iUnion_fintype_le _ _).trans _)
  apply (Finset.sum_le_sum fun i _ ↦ (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ ↦ each i j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]

end Weierstrass.Branch
