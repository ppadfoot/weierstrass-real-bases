module

public import Weierstrass.BranchWindows
public import Weierstrass.SlopeDescent

/-! Loss of secant windows at every restart of the original digit stream. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Predecessor
open scoped ENNReal Topology BigOperators
namespace Weierstrass.Branch

theorem measurable_coded_family {X : Type*} [MeasurableSpace X] {p : ℕ}
    (d : ℕ) (a : ℕ → ℤ) (g : ℝ) (W η : X → ℕ → ℝ) (I : X → ℕ → Fin p)
    (mW : ∀ j, Measurable fun x ↦ W x j) (mη : ∀ j, Measurable fun x ↦ η x j)
    (mI : ∀ j, Measurable fun x ↦ I x j) :
    Measurable (fun x ↦ codedSlope d (fun j ↦ (a j:ℝ)) p g (W x) (η x) (I x)) := by
  apply Measurable.tsum;intro n
  exact measurable_const.mul (Real.continuous_sin.measurable.comp
    ((measurable_const.mul (measurable_pathState d _ _ W I mW mI (n+1) 0)).add (mη n)))

theorem measurable_ballMass_family {X : Type*} [MeasurableSpace X] {p : ℕ} (hp : 0<p)
    (d : ℕ) (a : ℕ → ℤ) (g : ℝ) (W η : X → ℕ → ℝ) (Y : X → ℝ) (R : ℝ)
    (mW : ∀ j, Measurable fun x ↦ W x j) (mη : ∀ j, Measurable fun x ↦ η x j) (mY : Measurable Y) :
    Measurable (fun x ↦ ballMass (baseSlopeLaw hp d a (W x) (η x) g) (Y x) R) := by
  let f (z : X × ℝ) := codedSlope d (fun j ↦ (a j:ℝ)) p g (W z.1) (η z.1) (uniformCode p hp z.2)
  have mf : Measurable f := measurable_coded_family d a g _ _ _
    (fun j ↦ (mW j).comp measurable_fst) (fun j ↦ (mη j).comp measurable_fst)
    (fun j ↦ (measurable_uniformCode p hp j).comp measurable_snd)
  let E := {z : X × ℝ | Y z.1-R ≤ f z ∧ f z ≤ Y z.1+R}
  have mE : MeasurableSet E := (measurableSet_le ((mY.comp measurable_fst).sub measurable_const) mf).inter
      (measurableSet_le mf ((mY.comp measurable_fst).add measurable_const))
  have eq (x : X) : ballMass (baseSlopeLaw hp d a (W x) (η x) g) (Y x) R = unitLaw (Prod.mk x ⁻¹' E) :=
    Measure.map_apply (mf.comp measurable_prodMk_left) measurableSet_Icc
  simp_rw [eq]
  exact measurable_measure_prodMk_left mE

theorem measurableSet_goodPrefix {X : Type*} [MeasurableSpace X] {p : ℕ} (hp : 0<p)
    (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (W η : X → ℕ → ℝ) (I : X → ℕ → Fin p) (k : ℕ) (q : ℝ≥0∞)
    (mW : ∀ j, Measurable fun x ↦ W x j) (mη : ∀ j, Measurable fun x ↦ η x j)
    (mI : ∀ j, Measurable fun x ↦ I x j) :
    MeasurableSet {x | goodPrefix hp d a g c D (W x) (η x) (I x) k q} :=
  measurableSet_le (measurable_ballMass_family hp d a g W η _ _ mW mη
      (measurable_partialSecant d _ _ _ _ W η I _ k mW mη mI measurable_const)) measurable_const

/-- Reducing an inherited lift to the torus changes the choice of digits,
but preserves the full *law*. Sampling the suffix after a prescribed
prefix uses exactly this law, for every Borel test on state and slope. -/
theorem restarted_slope_sample {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    (g : ℝ) (η : ℕ → ℝ) (n : ℕ) (E : Set ((Fin (d+1) → UnitAddCircle) × ℝ)) (mE : MeasurableSet E) :
    let Ω := Fin (d+1) → UnitAddCircle
    let m := (volume : Measure Ω).prod unitLaw
    let state (z : Ω × ℝ) := pathState (d+1) (fun j ↦ (a j:ℝ)) p (centralLift z.1) (uniformCode p hp z.2) n
    m {z | ((fun j : Fin (d+1) ↦ (state z j : UnitAddCircle)),
      codedSlope (d+1) (fun j ↦ (a j:ℝ)) p g (state z) η (fun i ↦ uniformCode p hp z.2 (n+i))) ∈ E} =
      m {z | (z.1,codedSlope (d+1) (fun j ↦ (a j:ℝ)) p g (centralLift z.1) η (uniformCode p hp z.2)) ∈ E} := by
  classical
  intro Ω m state
  let f (W : ℕ → ℝ) (I : ℕ → Fin p) := codedSlope (d+1) (fun j ↦ (a j:ℝ)) p g W η I
  let F (z : Ω × ℝ) := (z.1,f (centralLift z.1) (uniformCode p hp z.2))
  let G (z : Ω × ℝ) : Ω × ℝ := (fun j ↦ (state z j:UnitAddCircle),f (state z) (fun i ↦ uniformCode p hp z.2 (n+i)))
  have mI (i : ℕ) : Measurable (fun z : Ω × ℝ ↦ uniformCode p hp z.2 i) := (measurable_uniformCode p hp i).comp measurable_snd
  have mW (j : ℕ) : Measurable (fun z : Ω × ℝ ↦ state z j) := measurable_pathState _ _ _ _ _
      (fun j ↦ (measurable_centralLift _ j).comp measurable_fst) mI n j
  have mF : Measurable F := measurable_fst.prodMk (measurable_coded_sample hp _ a _
    (fun i ↦ (measurable_centralLift _ i).comp measurable_fst) _ measurable_snd η g)
  have mG : Measurable G := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun j : Fin (d+1) ↦ AddCircle.measurable_mk'.comp (mW j))
    · exact (measurable_coded_family (d+1) a g state (fun _ ↦ η) _ mW (fun _ ↦ measurable_const) (fun i ↦ mI (n+i)))
  let Q (u : Ω) := unitLaw (Prod.mk u ⁻¹' (F ⁻¹' E))
  have mQ : Measurable Q := measurable_measure_prodMk_left (mF mE)
  change m (G ⁻¹' E) = m (F ⁻¹' E)
  rw [Measure.prod_apply (mG mE),Measure.prod_apply (mF mE)]
  change _ = ∫⁻ u, Q u
  rw [← haar_blockEndMean hp d a ha n mQ]
  apply lintegral_congr
  intro u
  let J := fun v : Fin n → Fin p ↦ extendWord hp v
  let B := fun v : Fin n → Fin p ↦ {x | digitPrefix hp n x = v}
  have mB (v) : MeasurableSet (B v) := (measurable_digitPrefix hp n) (measurableSet_singleton v)
  have dis : Pairwise (Function.onFun Disjoint B) := by
    intro v v' h;exact Set.disjoint_left.mpr (fun _ hv hv' ↦ h (hv.symm.trans hv'))
  have cov : (⋃ v, B v) = univ := iUnion_eq_univ_iff.mpr (fun x ↦ ⟨_,rfl⟩)
  rw [blockEndMean_prefix_sum,Finset.mul_sum]
  let T := Prod.mk u ⁻¹' (G ⁻¹' E)
  have mT : MeasurableSet T := measurable_prodMk_left (mG mE)
  change unitLaw T = _
  rw [←Measure.restrict_univ (μ:=unitLaw),←cov,Measure.restrict_iUnion dis mB,Measure.sum_apply _ mT,tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  rw [show B v = _ from digitPrefix_event hp v, restrict_code_prefix hp (J v) n, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_prefixSeed _ _) mT]
  congr 1
  let W := pathState (d+1) (fun j ↦ (a j:ℝ)) p (centralLift u) (J v) n
  let U := blockState hp (d+1) a n u v
  let Z := Prod.mk U ⁻¹' E
  have mZ : MeasurableSet Z := measurable_prodMk_left mE
  have coh (j : ℕ) (hj : j<d+1) : (W j:UnitAddCircle)=(centralLift U j:UnitAddCircle) := by
    simp only [centralLift,dif_pos hj,AddCircle.coe_equivIco];rfl
  have bco := baseSlopeLaw_coherent hp (d+1) a coh η g
  have eq (w : ℕ → ℝ) : baseSlopeLaw hp (d+1) a w η g Z = unitLaw {x | (U,f w (uniformCode p hp x)) ∈ E} :=
    Measure.map_apply (measurable_coded_sample hp _ a (fun _ : ℝ ↦ w) (fun _ ↦ measurable_const) id measurable_id η g) mZ
  change _ = unitLaw {x | (U,f (centralLift U) (uniformCode p hp x)) ∈ E}
  rw [←eq,bco.symm,eq]
  apply measure_congr
  have hunit : ∀ᵐ x ∂unitLaw, x ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  filter_upwards [hunit] with x hx
  obtain ⟨head,tail⟩ := prefixSeed_codes hp (J v) n hx
  have st := pathState_prefix (d+1) (fun j ↦ (a j:ℝ)) (p:ℝ) (centralLift u) n head
  apply propext
  change G (u,prefixSeed (J v) n x) ∈ E ↔ (U,f W (uniformCode p hp x)) ∈ E
  dsimp only [G,state]
  rw [st,funext tail]
  rfl

/-- A failed prefix at any restart is controlled by the genuine full-law
sampled heavy ball at its inherited phase. -/
theorem goodPrefix_loss_le_slopeHeavy {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {g : ℝ} (hg : 0<g) (h1 : g<1) (c D σ : ℝ) (k n : ℕ) (η : ℕ → ℝ) :
    ((volume : Measure (Fin (d+1) → UnitAddCircle)).prod unitLaw) {z |
      let I := uniformCode p hp z.2
      let W := pathState (d+1) (fun j ↦ (a j:ℝ)) p (centralLift z.1) I n
      ¬goodPrefix hp (d+1) a g c D W (fun j ↦ η (n+j)) (fun j ↦ I (n+j)) k
        (ENNReal.ofReal ((g^k:ℝ)^σ))} ≤
      slopeHeavy hp (d+1) a g (fun j ↦ η (n+j)) ((|D|+(1-g)⁻¹)*g^k) ((g^k:ℝ)^σ) := by
  let A := |D|+(1-g)⁻¹
  let Ω := Fin (d+1) → UnitAddCircle
  let θ := fun j ↦ η (n+j)
  let q := ENNReal.ofReal ((g^k:ℝ)^σ)
  let E := {z : Ω × ℝ | q < ballMass (baseSlopeLaw hp (d+1) a (centralLift z.1) θ g) z.2 (A*g^k)}
  have mE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_ballMass_family hp (d+1) a g _ (fun _ ↦ θ) _ _ (fun i ↦ (measurable_centralLift _ i).comp measurable_fst)
      (fun _ ↦ measurable_const) measurable_snd)
  have restart := restarted_slope_sample hp a ha g θ n E mE
  apply le_trans _ restart.le
  apply measure_mono
  intro z hz
  let I := uniformCode p hp z.2
  let W := pathState (d+1) (fun j ↦ (a j:ℝ)) p (centralLift z.1) I n
  let J := fun j ↦ I (n+j)
  let U : Ω := fun j ↦ (W j:UnitAddCircle)
  let P := truncatedSlope (d+1) (fun j ↦ (a j:ℝ)) p g W θ J k
  let Y := codedSlope (d+1) (fun j ↦ (a j:ℝ)) p g W θ J
  change ¬ballMass (baseSlopeLaw hp (d+1) a W θ g) _ (D*g^k) ≤ q at hz
  rw [partialSecant_zero] at hz
  change q < ballMass (baseSlopeLaw hp (d+1) a (centralLift U) θ g) Y (A*g^k)
  have coh (j : ℕ) (hj : j<d+1) : (W j:UnitAddCircle)=(centralLift U j:UnitAddCircle) := by
    simp only [centralLift,dif_pos hj,AddCircle.coe_equivIco];rfl
  rw [← baseSlopeLaw_coherent hp (d+1) a coh]
  apply (lt_of_not_ge hz).trans_le
  apply measure_mono
  change Icc (P-D*g^k) (P+D*g^k) ⊆ Icc (Y-A*g^k) (Y+A*g^k)
  have h : |Y-P| ≤ (1-g)⁻¹*g^k := truncatedSlope_tail _ _ _ W θ J hg.le h1 k
  have dlt := mul_le_mul_of_nonneg_right (le_abs_self D) (pow_nonneg hg.le k)
  obtain ⟨hL,hR⟩ := abs_le.mp h
  dsimp only [A]
  apply Icc_subset_Icc <;> rw [add_mul] <;> linarith

/-- Probability of an unmarked window along the actual orbit. The depth
before the window and the prescribed phases may both vary with its length. -/
theorem goodPrefix_loss {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {g s σ : ℝ} (hg : 0<g) (h1 : g<1) (info : SlopeInformation hp (d+1) a g s)
    (hσ : 0<σ) (hs : σ<s) (c D : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ (n : ℕ) (η : ℕ → ℝ),
      ((volume : Measure (Fin (d+1) → UnitAddCircle)).prod unitLaw) {z |
        let I := uniformCode p hp z.2
        let W := pathState (d+1) (fun j ↦ (a j:ℝ)) p (centralLift z.1) I n
        ¬goodPrefix hp (d+1) a g c D W (fun j ↦ η (n+j)) (fun j ↦ I (n+j)) k (ENNReal.ofReal ((g^k:ℝ)^σ))} ≤ ENNReal.ofReal ε := by
  let A := |D|+(1-g)⁻¹
  have ap : 0<A := add_pos_of_nonneg_of_pos (abs_nonneg _) (inv_pos.mpr (sub_pos.mpr h1))
  have lim : Tendsto (fun k : ℕ ↦ g^k) atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hg.le h1,Eventually.of_forall (fun k ↦ pow_pos hg k)⟩
  filter_upwards [lim.eventually (info σ hσ hs A ap ε hε)] with k hsmall
  intro n η
  exact (goodPrefix_loss_le_slopeHeavy hp a ha hg h1 c D σ k n η).trans (hsmall _)

end Weierstrass.Branch
