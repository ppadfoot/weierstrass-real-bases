module

public import Weierstrass.RayProof

/-! Uniform occupation bounds for the critical transverse drifts in §4. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace Weierstrass.CriticalRay

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- The two-sided primitive starting at level zero. -/
def driftPrimitive (f : ℤ → ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i then ∑ j ∈ Finset.Ico 0 i, f j else -∑ j ∈ Finset.Ico i 0, f j

theorem driftPrimitive_sub {i j : ℤ} (h : i ≤ j) (f : ℤ → ℝ) :
    driftPrimitive f j - driftPrimitive f i = ∑ a ∈ Finset.Ico i j, f a := by
  have join {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
      ∑ k ∈ Finset.Ico a b, f k + ∑ k ∈ Finset.Ico b c, f k = ∑ k ∈ Finset.Ico a c, f k := by
    rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c),
      Finset.Ico_union_Ico_eq_Ico h₁ h₂]
  by_cases hi : 0 ≤ i
  · rw [driftPrimitive, if_pos (hi.trans h), driftPrimitive, if_pos hi, ← join hi h]
    ring
  · by_cases hj : 0 ≤ j
    · rw [driftPrimitive, if_pos hj, driftPrimitive, if_neg hi, ← join (le_of_not_ge hi) hj]
      ring
    · rw [driftPrimitive, if_neg hj, driftPrimitive, if_neg hi, ← join h (le_of_not_ge hj)]
      ring

/-- The actual second-derivative drift, in the same normalization as (RC4). -/
def cosineDrift (ω : PhaseTorus) (w : ℤ → ℝ) (z : PhaseTorus) (i : ℤ) : ℝ :=
  driftPrimitive (fun j ↦ w j * (-(2*Real.pi)^2 * angleCos ((ω+z) j))) i

theorem continuous_cosineDrift (ω : PhaseTorus) (w : ℤ → ℝ) (i : ℤ) :
    Continuous (fun z ↦ cosineDrift ω w z i) := by
  have hc (j : ℤ) : Continuous (fun z : PhaseTorus ↦ w j * (-(2*Real.pi)^2 * angleCos ((ω+z) j))) :=
    continuous_const.mul (continuous_const.mul (Complex.continuous_re.comp (continuous_subtype_val.comp
      (AddCircle.continuous_toCircle.comp ((continuous_apply j).comp (continuous_const.add continuous_id))))))
  unfold cosineDrift driftPrimitive
  split_ifs <;> fun_prop (disch := exact hc _)

theorem cosineDrift_sub {B : ℂ} (ω : PhaseTorus) (w : ℤ → ℝ) (z : complexPhaseGroup B) {i j : ℤ}
    (h : i ≤ j) : cosineDrift ω w z.val j - cosineDrift ω w z.val i =
      (-(2*Real.pi)^2/2) * driftBlock B ω (Finset.Ico i j) w z := by
  simp only [cosineDrift, driftPrimitive_sub h, driftBlock, Finset.mul_sum]
  rw [Finset.sum_coe_sort (Finset.Ico i j) (fun k ↦ (-(2*Real.pi)^2/2) * (w k*(2*angleCos ((ω+z.val) k))))]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Condition (RC1), using both endpoints of the block. -/
def DriftWeightBounds (η : ℝ) (m₀ : ℕ) (w : ℤ → ℝ) : Prop :=
  (∀ j, |w j| ≤ 1) ∧ ∀ i j : ℤ, (m₀:ℤ) ≤ j-i →
    η * ((Finset.Ico i j).card:ℝ) ≤ ∑ k : Finset.Ico i j, (w k)^2

/-- The high-probability occupation conclusion following (RC3), for the actual
second-derivative drift and a center allowed to depend on the whole environment. -/
theorem critical_drift_occupation {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] {η : ℝ} (hη : 0 < η)
    (m₀ : ℕ) (D ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (ω : PhaseTorus) (w : ℤ → ℝ), DriftWeightBounds η m₀ w →
      ∀ o : ℤ, μ {z | ∃ t, ε*(n:ℝ) ≤
        valueCount (Finset.Ico o (o+n)) (cosineDrift ω w z.val) D t} ≤ ENNReal.ofReal δ := by
  let A := PhaseTorus × {w // DriftWeightBounds η m₀ w}
  let V (a : A) (z : complexPhaseGroup B) := cosineDrift a.1 a.2.val z.val
  have measurableV (a : A) (i : ℤ) : Measurable (fun z ↦ V a z i) :=
    ((continuous_cosineDrift _ _ _).comp continuous_subtype_val).measurable
  let κ : ℝ := -(2*Real.pi)^2/2
  have hκ : 0 < |κ| := abs_pos.mpr (by dsimp [κ]; exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))) (by norm_num))
  have sep (δ' : ℝ) (hδ' : 0 < δ') : ∃ K : ℕ, ∀ a i j, (K:ℤ) ≤ |i-j| →
      μ {z | |V a z i - V a z j| ≤ 2*D} ≤ ENNReal.ofReal δ' := by
    obtain ⟨K,hK⟩ := critical_drift_anticoncentration hb μ hη (2*D/|κ|) hδ'
    refine ⟨max K m₀, ?_⟩
    intro a i j hij
    wlog order : i ≤ j generalizing i j
    · rw [abs_sub_comm] at hij
      simpa only [abs_sub_comm (V a _ i) (V a _ j)] using this j i hij (le_of_not_ge order)
    rw [abs_of_nonpos (sub_nonpos.mpr order), neg_sub] at hij
    have hm : (m₀:ℤ) ≤ j-i := by omega
    have hcard : K ≤ (Finset.Ico i j).card := by rw [Int.card_Ico]; omega
    have hs := hK (Finset.Ico i j) a.2.val a.1 0 hcard (fun k _ ↦ a.2.property.1 k)
      (a.2.property.2 i j hm)
    rw [measureReal_def] at hs
    have hset : {z | |V a z i - V a z j| ≤ 2*D} =
        {z | |driftBlock B a.1 (Finset.Ico i j) a.2.val z - 0| ≤ 2*D/|κ|} := by
      ext z
      change |cosineDrift a.1 a.2.val z.val i - cosineDrift a.1 a.2.val z.val j| ≤ 2*D ↔ _
      rw [abs_sub_comm, cosineDrift_sub _ _ _ order, abs_mul]
      change |κ| * |driftBlock B a.1 (Finset.Ico i j) a.2.val z| ≤ 2*D ↔ _
      simp only [Set.mem_ofPred_eq, sub_zero, le_div_iff₀ hκ, mul_comm]
    rw [hset]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _ ) hδ'.le).mpr hs.le
  obtain ⟨N,hN⟩ := occupation_of_block_anticoncentration (A := A) (fun _ ↦ μ) V measurableV D sep ε δ hε hδ
  exact ⟨N,fun n hn ω w hw o ↦ hN n hn (ω,⟨w,hw⟩) o⟩

/-- The number of bad marks encountered starting at a transverse scale. -/
def countBad (bad : ℕ → ℝ → Prop) [∀ l x, Decidable (bad l x)] (l : ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | J+1, x => (if bad l x then 1 else 0) + countBad bad (l+1) J x

private theorem interval_multiples {S : Set ℝ} {x L : ℝ} (m : ℕ) {q : ℝ≥0∞} (piece : ∀ a : ℝ, volume (S ∩ Icc a (a+L)) ≤ q) :
    volume (S ∩ Icc x (x+m*L)) ≤ m*q := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero, Icc_self]
    exact (measure_mono (inter_subset_right (s := S) (t := {x}))).trans_eq (measure_singleton x)
  | succ m ih =>
    have sub : S ∩ Icc x (x+(m+1:ℕ)*L) ⊆ (S ∩ Icc x (x+m*L)) ∪ (S ∩ Icc (x+m*L) (x+m*L+L)) := by
      rintro y ⟨hy,hy',hy''⟩
      by_cases h : y ≤ x+m*L
      · exact Or.inl ⟨hy,hy',h⟩
      · exact Or.inr ⟨hy,le_of_not_ge h,by push_cast at hy''; linarith⟩
    exact (measure_mono sub).trans ((measure_union_le _ _).trans (by simpa [add_mul] using add_le_add ih (piece (x+m*L))))

/-- A retained set pays for a full subdivision only when every retained point
in the parent is bad. A good reference point localizes the entire parent to
one interval of the next size, whose center may depend on that parent. -/
theorem transverse_tree_bound (m : ℕ) (hm : 1 ≤ m) (L : ℕ → ℝ) 
    (scale : ∀ l, L l ≤ m * L (l+1)) (bad : ℕ → ℝ → Prop) [∀ l x, Decidable (bad l x)]
    (S : Set ℝ) (l J budget : ℕ) (a : ℝ) (window : S ⊆ Icc a (a+L l))
    (counts : ∀ x ∈ S, countBad bad l J x ≤ budget)
    (contract : ∀ i, l ≤ i → i < l+J → ∀ x ∈ S, ¬bad i x → ∀ y ∈ S,
      |x-y| ≤ L i → |x-y| ≤ L (i+1)/2) :
    volume S ≤ (m:ℝ≥0∞)^budget * ENNReal.ofReal (L (l+J)) := by
  induction J generalizing S l budget a with
  | zero =>
    have bound : volume S ≤ ENNReal.ofReal (L l) := (measure_mono window).trans_eq (by simp [Real.volume_Icc])
    simpa only [Nat.add_zero] using bound.trans (le_mul_of_one_le_left (zero_le (a := _)) (one_le_pow₀ (by exact_mod_cast hm)))
  | succ J ih =>
    have cut {S' : Set ℝ} (hs : S' ⊆ S) : ∀ i, l+1 ≤ i → i < l+1+J → ∀ x ∈ S',
        ¬bad i x → ∀ y ∈ S', |x-y| ≤ L i → |x-y| ≤ L (i+1)/2 := by
      intro i h hl x hx hgood y hy
      exact contract i (by omega) (by omega) x (hs hx) hgood y (hs hy)
    have tend : l+1+J = l+(J+1) := by omega
    by_cases good : ∃ x ∈ S, ¬bad l x
    · obtain ⟨x,hx,gx⟩ := good
      have narrow : S ⊆ Icc (x-L (l+1)/2) (x-L (l+1)/2+L (l+1)) := by
        intro y hy
        have h := contract l le_rfl (by omega) x hx gx y hy (by
          have xx := window hx
          have yy := window hy
          rw [abs_le]; constructor <;> linarith [xx.1,xx.2,yy.1,yy.2])
        rw [abs_le] at h
        exact ⟨by linarith [h.2], by linarith [h.1]⟩
      refine (ih S (l+1) budget _ narrow (fun y hy ↦ ?_) (cut Subset.rfl)).trans_eq (by rw [tend])
      have h := counts y hy
      simp only [countBad] at h
      omega
    · push Not at good
      cases budget with
      | zero =>
        have empty : S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have h := counts x hx
          simp [countBad, good x hx] at h
        simp [empty]
      | succ b =>
        have piece (u : ℝ) : volume (S ∩ Icc u (u+L (l+1))) ≤ (m:ℝ≥0∞)^b * ENNReal.ofReal (L (l+(J+1))) := by
          let S' := S ∩ Icc u (u+L (l+1))
          refine (ih S' (l+1) b u (fun _ hy ↦ hy.2) (fun y hy ↦ ?_) (cut (fun _ hy ↦ hy.1))).trans_eq (by rw [tend])
          have h := counts y hy.1
          simp only [countBad, if_pos (good y hy.1)] at h
          omega
        have larger : S ⊆ Icc a (a+m*L (l+1)) := fun x hx ↦ ⟨(window hx).1, (window hx).2.trans (add_le_add_right (scale l) a)⟩
        rw [← Set.inter_eq_self_of_subset_left larger]
        exact (interval_multiples m piece).trans_eq (by ring)


/-- The bilateral weighted increment evaluated directly in angles modulo one. -/
def circleRay (b g : ℝ) (c d : ℤ → ℝ) (z : PhaseTorus) (t : ℝ) : ℝ :=
  ∑' j : ℤ, g^j * c j * (angleCos (z j + ↑(b^j*d j*t)) - angleCos (z j))

theorem circleRay_real (b g : ℝ) (c d z : ℤ → ℝ) (t : ℝ) :
    circleRay b g c d (fun j ↦ ↑(z j)) t = rayIncrement b g c d z t := by
  unfold circleRay rayIncrement rayTerm
  congr 1
  funext j
  rw [← AddCircle.coe_add, angleCos_coe, angleCos_coe]

theorem circleRay_ones (b g : ℝ) (z : PhaseTorus) (t : ℝ) :
    circleRay b g (fun _ ↦ 1) (fun _ ↦ 1) z t = circleIncrement b g z t := by
  have repr : (fun j ↦ (↑(AddCircle.equivIco (1:ℝ) 0 (z j) : ℝ) : AddCircle (1:ℝ))) = z := by
    funext j; exact AddCircle.coe_equivIco
  rw [← repr, circleRay_real, rayIncrement_ones, circleIncrement_of_real]

theorem measurable_circleRay (b g : ℝ) (c d : ℤ → ℝ) :
    Measurable (fun p : PhaseTorus × ℝ ↦ circleRay b g c d p.1 p.2) := by
  unfold circleRay
  apply Measurable.tsum
  intro j
  have ac : Continuous angleCos := Complex.continuous_re.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)
  exact (continuous_const.mul ((ac.comp (((continuous_apply j).comp continuous_fst).add
    ((AddCircle.continuous_mk' (1:ℝ)).comp (continuous_const.mul continuous_snd)))).sub
    (ac.comp ((continuous_apply j).comp continuous_fst)))).measurable

/-- Translation of each angle along the given transverse ray. -/
def transverseOrbit (ρ : ℝ) (e : ℤ → ℝ) (h : ℝ) : PhaseTorus := fun j ↦ ↑(ρ^j * e j * h)

theorem transverseOrbit_add (ρ : ℝ) (e : ℤ → ℝ) (x y : ℝ) :
    transverseOrbit ρ e (x+y) = transverseOrbit ρ e x + transverseOrbit ρ e y := by
  funext j
  simp [transverseOrbit, mul_add]

theorem transverseOrbit_mem {K : Type*} [Field K] (σ τ : K →+* ℂ) (u : K)
    (hu : τ u ≠ 0) (w : ℂ) (h : ℝ) :
    transverseOrbit ‖τ u‖ (rayProjection (τ u) w) h ∈ complexPhaseGroup (σ u) := by
  convert! conjugate_orbit_mem_phaseGroup σ τ u (w*(h:ℂ)) using 1
  funext i
  simp [transverseOrbit, norm_zpow_mul_rayProjection hu, complexPhaseOrbit, ← mul_assoc, sub_mul]

/-- Circle-valued form of (RC4), retaining arbitrary forcing cosets. -/
theorem circle_critical_linearization {g b ρ D : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 ≤ D) (hcrit : g*b*ρ=1) {c d e : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) (t h : ℝ) (k N : ℤ) (hkN : -N ≤ k+1)
    (htlo : b ^ (-k-1) ≤ |t|) (hthi : |t| ≤ b^(-k)) (hh : |h| ≤ D*ρ^N) :
    |(circleRay b g c d (z+transverseOrbit ρ e h) t-circleRay b g c d z t)/t -
      h*(cosineDrift 0 (fun j ↦ c j*d j*e j) z (k+1)-cosineDrift 0 (fun j ↦ c j*d j*e j) z (-N))|
      ≤ criticalErrorConstant b ρ D * ρ^N := by
  let ζ (j : ℤ) : ℝ := AddCircle.equivIco 1 0 (z j)
  have rep (j : ℤ) : (↑(ζ j) : AddCircle (1:ℝ)) = z j := AddCircle.coe_equivIco
  have rep' : (fun j ↦ (↑(ζ j) : AddCircle (1:ℝ))) = z := funext rep
  have trans : z+transverseOrbit ρ e h =
      (fun j ↦ (↑(transversePhase ρ e ζ h j) : AddCircle (1:ℝ))) := by
    funext j
    simp [transversePhase, transverseOrbit, rep]
  rw [trans, circleRay_real, ← rep', circleRay_real, cosineDrift, cosineDrift, driftPrimitive_sub hkN]
  have sets : Finset.Ico (-N) (k+1) = Finset.Icc (-N) k := by ext; simp
  simp only [sets, zero_add, angleCos_coe]
  exact critical_linearization hb hg hg1 hρ hρ1 hD hcrit hc hd he ζ t h k N htlo hthi hh

private theorem countBad_eq_card (bad : ℕ → ℝ → Prop) [∀ l x, Decidable (bad l x)]
    (l J : ℕ) (x : ℝ) :
    countBad bad l J x = ((Finset.Ico l (l+J)).filter (fun i ↦ bad i x)).card := by
  induction J generalizing l with
  | zero => simp [countBad]
  | succ J ih =>
    have split : Finset.Ico l (l+(J+1)) = insert l (Finset.Ico (l+1) (l+1+J)) := by
      ext i; simp; omega
    rw [countBad, ih, split, Finset.filter_insert]
    by_cases hx : bad l x <;> simp [hx, Nat.add_comm]

/-- Choose the retained environments before testing either the physical secant or
the transverse path. Every subset of the first n transverse scales inherits
the bound, and the target may be chosen after the environment is known. -/
theorem critical_retained_environments {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] {η : ℝ} (hη : 0 < η)
    (m₀ : ℕ) (D ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (ω : PhaseTorus) (w : ℤ → ℝ), DriftWeightBounds η m₀ w →
      ∀ M : ℤ, ∃ G : Set (complexPhaseGroup B), MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
        ∀ z ∈ G, ∀ (t : ℝ) (J : ℕ), J ≤ n → 
          (((Finset.range J).filter (fun (l : ℕ) ↦ |cosineDrift ω w z.val (-M-l)-t| ≤ D)).card:ℝ) < ε*n := by
  obtain ⟨N,hN⟩ := critical_drift_occupation hb μ hη m₀ D ε δ hε hδ
  refine ⟨N,?_⟩
  intro n hn ω w hw M
  let o : ℤ := 1-M-n
  let s := Finset.Ico o (o+n)
  let E := {z : complexPhaseGroup B | ∃ t, ε*n ≤ (valueCount s (cosineDrift ω w z.val) D t:ℝ)}
  refine ⟨(toMeasurable μ E)ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · simpa only [compl_compl, measure_toMeasurable] using hN n hn ω w hw o
  · intro z hz t J hJ
    have ht : (valueCount s (cosineDrift ω w z.val) D t : ℝ) < ε*n := by
      by_contra! ht
      exact hz (subset_toMeasurable μ E ⟨t,ht⟩)
    refine lt_of_le_of_lt ?_ ht
    exact_mod_cast (show ((Finset.range J).filter (fun (l : ℕ) ↦ |cosineDrift ω w z.val (-M-l)-t| ≤ D)).card ≤
      valueCount s (cosineDrift ω w z.val) D t from by
        apply Finset.card_le_card_of_injOn (fun l : ℕ ↦ -M-(l:ℤ))
        · intro l hl
          obtain ⟨hl,hh⟩ := Finset.mem_filter.mp hl
          refine Finset.mem_filter.mpr ⟨?_,hh⟩
          have := Finset.mem_range.mp hl
          change -M-(l:ℤ) ∈ Finset.Ico (1-M-n) (1-M-n+n)
          rw [Finset.mem_Ico]; omega
        · intro i _ j _ hh
          dsimp at hh
          omega)

/-- Bad-slope threshold sufficient to contract a whole retained interval about
a good reference point. The displacement constants depend only on the fixed
frequencies, amplitude cap, and initial transverse index. -/
def slopeThreshold (b ρ Q : ℝ) (M : ℕ) : ℝ :=
  2*(2*Q+|criticalErrorConstant b ρ ((ρ^M)⁻¹)| *ρ^M)/ρ

/-- Deterministic retained-set estimate on one physical shell. -/
theorem retained_slice {b g ρ Q : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hQ : 0 < Q) (hcrit : g*b*ρ=1)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) (hscale : 1 ≤ m*ρ)
    (M J budget : ℕ) (k : ℤ) (hkM : -(M:ℤ) ≤ k+1) (z₀ : PhaseTorus) (t : ℝ)
    (htlo : b ^ (-k-1) ≤ |t|) (hthi : |t| ≤ b^(-k)) (S : Set ℝ)
    (window : S ⊆ Icc 0 1)
    (signal : ∀ x ∈ S, |circleRay b g c d (z₀+transverseOrbit ρ e x) t| ≤ Q*ρ^J*|t|)
    (marks : ∀ x ∈ S, ((Finset.range J).filter (fun (i : ℕ) ↦
      |cosineDrift 0 (fun j ↦ c j*d j*e j) (z₀+transverseOrbit ρ e x) (-(M:ℤ)-i) -
       cosineDrift 0 (fun j ↦ c j*d j*e j) (z₀+transverseOrbit ρ e x) (k+1)| ≤ slopeThreshold b ρ Q M)).card ≤ budget) :
    volume S ≤ (m:ℝ≥0∞)^budget * ENNReal.ofReal (ρ^J) := by
  let z (x : ℝ) := z₀+transverseOrbit ρ e x
  let w (j : ℤ) := c j*d j*e j
  let P (x : ℝ) := cosineDrift 0 w (z x)
  let D := slopeThreshold b ρ Q M
  let bad (i : ℕ) (x : ℝ) := |P x (-(M:ℤ)-i)-P x (k+1)| ≤ D
  have width : ∀ l : ℕ, ρ^l ≤ m*ρ^(l+1) := by
    intro l
    simpa only [pow_succ, mul_left_comm, mul_assoc, one_mul, mul_one, mul_comm] using
      mul_le_mul_of_nonneg_right hscale (pow_pos hρ l).le
  refine (transverse_tree_bound m hm (fun l ↦ ρ^l) width bad S 0 J budget 0 (by simpa using window) ?_ ?_).trans_eq (by simp)
  · intro x hx
    simpa only [countBad_eq_card, zero_add, Nat.Ico_zero_eq_range] using
      (show ((Finset.range J).filter (fun i ↦ bad i x)).card ≤ budget from marks x hx)
  · intro i _ hi x hx good y hy close
    have ht : 0 < |t| := (zpow_pos (zero_lt_one.trans hb) _).trans_le htlo
    have hneg : -((M:ℤ)+i) = -(M:ℤ)-i := by omega
    have shift : z x + transverseOrbit ρ e (y-x) = z y := by
      dsimp [z]
      rw [add_assoc, ← transverseOrbit_add, add_sub_cancel]
    have fp : ρ^((M:ℤ)+i) = ρ^M * ρ^i := by rw [zpow_add₀ hρ.ne']; simp
    have rad : |y-x| ≤ ((ρ^M)⁻¹)*ρ^((M:ℤ)+i) := by
      rw [fp, ← mul_assoc, inv_mul_cancel₀ (pow_pos hρ M).ne', one_mul, abs_sub_comm]
      exact close
    have err := circle_critical_linearization hb hg hg1 hρ hρ1 (inv_nonneg.mpr (pow_pos hρ M).le)
      hcrit hc hd he (z x) t (y-x) k ((M:ℤ)+i) (by omega) htlo hthi rad
    rw [shift, hneg, fp] at err
    let F (u : ℝ) := circleRay b g c d (z u) t
    let slope := P x (k+1)-P x (-(M:ℤ)-i)
    let C := criticalErrorConstant b ρ ((ρ^M)⁻¹)
    change |(F y-F x)/t - (y-x)*slope| ≤ C*(ρ^M*ρ^i) at err
    have si : ρ^J ≤ ρ^i := pow_le_pow_of_le_one hρ.le hρ1.le (by omega)
    have sec : |(F y-F x)/t| ≤ 2*Q*ρ^i := by
      rw [abs_div, div_le_iff₀ ht]
      calc
        |F y-F x| ≤ |F y|+|F x| := abs_sub _ _
        _ ≤ Q*ρ^J*|t|+Q*ρ^J*|t| := add_le_add (signal y hy) (signal x hx)
        _ ≤ 2*Q*ρ^i*|t| := by linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left si hQ.le) ht.le]
    have coef : |(y-x)*slope| ≤ (2*Q+|C| *ρ^M)*ρ^i := by
      calc
        _ ≤ |(F y-F x)/t - (y-x)*slope| + |(F y-F x)/t| := by
          simpa only [abs_sub_comm ((F y-F x)/t) _, sub_zero] using abs_sub_le ((y-x)*slope) ((F y-F x)/t) 0
        _ ≤ C*(ρ^M*ρ^i) + 2*Q*ρ^i := add_le_add err sec
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right (le_abs_self C) (mul_pos (pow_pos hρ M) (pow_pos hρ i)).le]
    have steep : D < |slope| := by
      change ¬(|P x (-(M:ℤ)-i)-P x (k+1)| ≤ D) at good
      simpa only [slope, abs_sub_comm (P x (k+1)) _] using lt_of_not_ge good
    have Dpos : 0 < D := by dsimp [D,slopeThreshold]; positivity
    have shrink : |y-x| *D ≤ (2*Q+|C| *ρ^M)*ρ^i := by
      rw [abs_mul] at coef
      exact (mul_le_mul_of_nonneg_left steep.le (abs_nonneg _)).trans coef
    rw [abs_sub_comm]
    apply le_of_mul_le_mul_right (a := D) _ Dpos
    refine shrink.trans_eq ?_
    dsimp [D,slopeThreshold,C]
    rw [pow_succ]
    field_simp

private theorem continuous_transverseOrbit (ρ : ℝ) (e : ℤ → ℝ) : Continuous (transverseOrbit ρ e) :=
  continuous_pi (fun _ ↦ (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_const.mul continuous_id))

/-- Averaging along any orbit in the compact group transfers a uniform
one-dimensional slice estimate to Haar measure on each coset. -/
theorem haar_le_of_transverse_slices {B : ℂ} (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] {ρ : ℝ} {e : ℤ → ℝ}
    (hmem : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B)
    (E : Set (complexPhaseGroup B)) (hE : MeasurableSet E) (Q : ℝ≥0∞)
    (slice : ∀ z : complexPhaseGroup B, volume {x : ℝ | x ∈ Icc 0 1 ∧
      z+⟨transverseOrbit ρ e x,hmem x⟩ ∈ E} ≤ Q) : μ E ≤ Q := by
  let ν := volume.restrict (Icc (0:ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  let W (x : ℝ) : complexPhaseGroup B := ⟨transverseOrbit ρ e x,hmem x⟩
  have cW : Continuous W := (continuous_transverseOrbit ρ e).subtype_mk _
  let X : Set (complexPhaseGroup B × ℝ) := (fun p ↦ p.1+W p.2) ⁻¹' E
  have mX : MeasurableSet X := (continuous_fst.add (cW.comp continuous_snd)).measurable hE
  have byTime (x : ℝ) : μ ((fun z : complexPhaseGroup B ↦ (z,x)) ⁻¹' X) = μ E := by
    change μ ((fun z ↦ z+W x) ⁻¹' E) = μ E
    simpa only [add_comm _ (W x)] using measure_preimage_add μ (W x) E
  have byPoint (z : complexPhaseGroup B) : ν (Prod.mk z ⁻¹' X) ≤ Q := by
    have mx : MeasurableSet (Prod.mk z ⁻¹' X) := mX.preimage (measurable_const.prodMk measurable_id)
    rw [show ν = volume.restrict (Icc (0:ℝ) 1) from rfl, Measure.restrict_apply mx, inter_comm]
    exact slice z
  calc
    μ E = (μ.prod ν) X := by rw [Measure.prod_apply_symm mX]; simp_rw [byTime]; simp
    _ = ∫⁻ z, ν (Prod.mk z ⁻¹' X) ∂μ := Measure.prod_apply mX
    _ ≤ ∫⁻ _ : complexPhaseGroup B, Q ∂μ := lintegral_mono byPoint
    _ = Q := by simp



set_option maxHeartbeats 1200000 in
/-- Retained Haar mass of a secant event throughout a physical annulus. A common
retained set works simultaneously on all annuli and all physical secants. -/
theorem critical_shell_bounds {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] {g ρ η : ℝ} (hg : 0 < g)
    (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hcrit : g*‖B‖*ρ=1) (hη : 0 < η)
    (m₀ : ℕ) (m : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ m*ρ) {A K ε δ : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (ω : PhaseTorus) (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) →
      (∀ j, |d j| ≤ 1) → (∀ j, |e j| ≤ 1) → (∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) →
      DriftWeightBounds η m₀ (fun j ↦ c j*d j*e j) →
      ∃ G : Set (complexPhaseGroup B), MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
        ∀ (p : ℕ), p ≤ n → ∀ t : ℝ, A*ρ^(p+1) ≤ |t| → |t| ≤ A →
        μ {z | z ∈ G ∧ |circleRay ‖B‖ g c d (ω+z.val) t| ≤ K*ρ^n} ≤
          (m:ℝ≥0∞)^⌊ε*n⌋₊ * ENNReal.ofReal (ρ^(n-p)) := by
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt A hb
  let Q := K/(A*ρ)
  have hQ : 0 < Q := div_pos hK (mul_pos hA hρ)
  obtain ⟨N,hN⟩ := critical_retained_environments hb μ hη m₀ (slopeThreshold ‖B‖ ρ Q M) ε δ hε hδ
  refine ⟨N,?_⟩
  intro n hn ω c d e hc hd he hmem hw
  let w (j : ℤ) := c j*d j*e j
  obtain ⟨G,hG,mG,ret⟩ := hN n hn ω w hw M
  refine ⟨G,hG,mG,?_⟩
  intro p hp t lower upper
  have ht : 0 < |t| := (mul_pos hA (pow_pos hρ _)).trans_le lower
  obtain ⟨a,ha⟩ := exists_mem_Ico_zpow ht hb
  let k := -(a+1)
  have hlow : ‖B‖^(-k-1) ≤ |t| := by simpa [k] using ha.1
  have hhigh : |t| ≤ ‖B‖^(-k) := by simpa [k] using ha.2.le
  have ka : a ≤ (M:ℤ) := (zpow_le_zpow_iff_right₀ hb).mp (ha.1.trans (upper.trans (by simpa using hM.le)))
  have hk : -(M:ℤ) ≤ k+1 := by dsimp [k]; omega
  let E := {z : complexPhaseGroup B | z ∈ G ∧ |circleRay ‖B‖ g c d (ω+z.val) t| ≤ K*ρ^n}
  have cf : Measurable (fun z : complexPhaseGroup B ↦ circleRay ‖B‖ g c d (ω+z.val) t) :=
    (measurable_circleRay _ _ _ _).comp ((continuous_const.add continuous_subtype_val).measurable.prodMk measurable_const)
  have mE : MeasurableSet E := hG.inter (measurableSet_le cf.abs measurable_const)
  apply haar_le_of_transverse_slices μ hmem E mE
  intro z
  let S := {x : ℝ | x ∈ Icc 0 1 ∧ z+⟨transverseOrbit ρ e x,hmem x⟩ ∈ E}
  let zz (x : ℝ) : complexPhaseGroup B := z + ⟨transverseOrbit ρ e x,hmem x⟩
  have zr (x : ℝ) : ω+(zz x).val = (ω+z.val)+transverseOrbit ρ e x := (add_assoc _ _ _).symm
  have drift (x : ℝ) : cosineDrift 0 w ((ω+z.val)+transverseOrbit ρ e x) = cosineDrift ω w (zz x).val := by
    funext j
    simp only [cosineDrift, zero_add, zr]
  refine retained_slice hb hg hg1 hρ hρ1 hQ hcrit hc hd he m hm hs M (n-p) ⌊ε*n⌋₊ k hk
    (ω+z.val) t hlow hhigh S (fun _ hx ↦ hx.1) ?_ ?_
  · intro x hx
    have hv : |circleRay ‖B‖ g c d (ω+(zz x).val) t| ≤ K*ρ^n := hx.2.2
    rw [zr] at hv
    apply hv.trans
    have powN : ρ^(n-p)*ρ^p=ρ^n := by rw [← pow_add, Nat.sub_add_cancel hp]
    calc
      K*ρ^n = Q*ρ^(n-p)*(A*ρ^(p+1)) := by dsimp [Q]; rw [pow_succ, ← powN]; field_simp
      _ ≤ Q*ρ^(n-p)*|t| := mul_le_mul_of_nonneg_left lower (mul_pos hQ (pow_pos hρ _)).le
  · intro x hx
    change ((Finset.range (n-p)).filter (fun (i : ℕ) ↦ |cosineDrift 0 w ((ω+z.val)+transverseOrbit ρ e x) _ -
      cosineDrift 0 w ((ω+z.val)+transverseOrbit ρ e x) _| ≤ _)).card ≤ _
    simp_rw [drift]
    apply Nat.le_floor
    exact (ret (zz x) hx.2.1 _ (n-p) (Nat.sub_le _ _)).le


/-- Summing the geometric physical annuli incurs only the number of scales. -/
theorem geometric_shell_integral {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (n : ℕ) (U : ℝ≥0∞) (hU : 1 ≤ U) (F : ℝ → ℝ≥0∞) (cap : ∀ t, F t ≤ 1)
    (shell : ∀ (p : ℕ), p ≤ n → ∀ t : ℝ, A*ρ^(p+1) ≤ |t| → |t| ≤ A →
      F t ≤ U*ENNReal.ofReal (ρ^(n-p))) :
    ∫⁻ t in Icc (-A) A, F t ≤ (n+1:ℕ)*U*ENNReal.ofReal (2*A*ρ^n) := by
  let H (p : ℕ) := Icc (-(A*ρ^p)) (A*ρ^p)
  let I (p : ℕ) := ∫⁻ t in H p, F t
  let Q := U*ENNReal.ofReal (2*A*ρ^n)
  have vol (p : ℕ) : volume (H p) = ENNReal.ofReal (2*A*ρ^p) := by
    dsimp only [H]; rw [Real.volume_Icc]; congr 1; ring
  have step (p : ℕ) (hp : p < n) : I p ≤ I (p+1) + Q := by
    let R := H p \ H (p+1)
    have ringBound : (∫⁻ t in R, F t) ≤ Q := by
      have hpoint (t : ℝ) (ht : t ∈ R) : F t ≤ U*ENNReal.ofReal (ρ^(n-p)) := by
        have ab : |t| ≤ A*ρ^p := abs_le.mpr ht.1
        have low : A*ρ^(p+1) ≤ |t| := le_of_not_ge (fun h ↦ ht.2 (abs_le.mp h))
        exact shell p hp.le t low (ab.trans (mul_le_of_le_one_right hA.le (pow_le_one₀ hρ.le hρ1)))
      calc
        _ ≤ ∫⁻ _ : ℝ in R, U*ENNReal.ofReal (ρ^(n-p)) := setLIntegral_mono measurable_const hpoint
        _ ≤ (U*ENNReal.ofReal (ρ^(n-p)))*volume (H p) := by
          simpa using mul_le_mul_right (measure_mono (show R ⊆ H p from sdiff_subset)) (U*ENNReal.ofReal (ρ^(n-p)))
        _ = Q := by
          rw [vol, mul_assoc, ← ENNReal.ofReal_mul (pow_pos hρ _).le]
          congr 2
          calc ρ^(n-p)*(2*A*ρ^p) = 2*A*(ρ^(n-p)*ρ^p) := by ring
               _ = _ := by rw [← pow_add, Nat.sub_add_cancel hp.le]
    have cover : H p ⊆ H (p+1) ∪ R := by intro t ht; by_cases h : t ∈ H (p+1); exact Or.inl h; exact Or.inr ⟨ht,h⟩
    exact (lintegral_mono_set cover).trans ((lintegral_union_le F _ _).trans (add_le_add_right ringBound _))
  have iterate : ∀ p ≤ n, I 0 ≤ I p + p*Q := by
    intro p hp
    induction p with
    | zero => simp
    | succ p ih =>
      calc
        _ ≤ I p + p*Q := ih (by omega)
        _ ≤ (I (p+1)+Q)+p*Q := add_le_add_left (step p (by omega)) _
        _ = _ := by push_cast; ring
  have tail : I n ≤ Q := by
    calc
      _ ≤ ∫⁻ _ : ℝ in H n, 1 := lintegral_mono (fun t ↦ cap t)
      _ = ENNReal.ofReal (2*A*ρ^n) := by simp [vol]
      _ ≤ Q := le_mul_of_one_le_left (zero_le (a := _)) hU
  calc
    _ = I 0 := by simp [I,H]
    _ ≤ I n + n*Q := iterate n le_rfl
    _ ≤ Q+n*Q := add_le_add_left tail _
    _ = _ := by dsimp [Q]; push_cast; ring


set_option maxHeartbeats 500000 in
theorem retained_markov {B : ℂ} (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ]
    (b g : ℝ) (c d : ℤ → ℝ) (ω : PhaseTorus) {G : Set (complexPhaseGroup B)} (hG : MeasurableSet G)
    (A cap τ : ℝ) (hτ : 0 < τ) (q : ℝ≥0∞)
    (integrated : ∫⁻ t in Icc (-A) A, μ {z | z ∈ G ∧ |circleRay b g c d (ω+z.val) t| ≤ cap} ≤ q) :
    μ {z | ENNReal.ofReal τ < volume {t : ℝ | t ∈ Icc (-A) A ∧ |circleRay b g c d (ω+z.val) t| ≤ cap}} ≤
      μ Gᶜ + q / ENNReal.ofReal τ := by
  let ν := volume.restrict (Icc (-A) A)
  let X := {p : complexPhaseGroup B × ℝ | p.1 ∈ G ∧ |circleRay b g c d (ω+p.1.val) p.2| ≤ cap}
  have env : Continuous (fun p : complexPhaseGroup B × ℝ ↦ ω+p.1.val) :=
    continuous_const.add (continuous_subtype_val.comp continuous_fst)
  have mp : Measurable (fun p : complexPhaseGroup B × ℝ ↦ (ω+p.1.val,p.2)) :=
    env.measurable.prodMk measurable_snd
  have mF := (measurable_circleRay b g c d).comp mp
  have mx : MeasurableSet X := (measurable_fst hG).inter (measurableSet_le mF.abs measurable_const)
  let f (z : complexPhaseGroup B) := ν (Prod.mk z ⁻¹' X)
  have mf : Measurable f := measurable_measure_prodMk_left mx
  have area : ∫⁻ z, f z ∂μ ≤ q := by
    calc
      _ = (μ.prod ν) X := (Measure.prod_apply mx).symm
      _ = ∫⁻ t, μ ((fun z ↦ (z,t)) ⁻¹' X) ∂ν := Measure.prod_apply_symm mx
      _ ≤ q := integrated
  let W := {z : complexPhaseGroup B | ENNReal.ofReal τ < volume {t : ℝ | t ∈ Icc (-A) A ∧ |circleRay b g c d (ω+z.val) t| ≤ cap}}
  have sub : W ⊆ Gᶜ ∪ {z : complexPhaseGroup B | ENNReal.ofReal τ ≤ f z} := by
    intro z hz
    by_cases gZ : z ∈ G
    · right
      have mz : MeasurableSet (Prod.mk z ⁻¹' X) := mx.preimage (measurable_const.prodMk measurable_id)
      change ENNReal.ofReal τ ≤ ν (Prod.mk z ⁻¹' X)
      rw [show ν = volume.restrict (Icc (-A) A) from rfl, Measure.restrict_apply mz, inter_comm]
      have eq : Icc (-A) A ∩ Prod.mk z ⁻¹' X = {t : ℝ | t ∈ Icc (-A) A ∧ |circleRay b g c d (ω+z.val) t| ≤ cap} := by
        ext t
        change (_ ∧ z ∈ G ∧ _) ↔ (_ ∧ _)
        simp [gZ]
      rw [eq]
      exact le_of_lt hz
    · exact Or.inl gZ
  exact (measure_mono sub).trans ((measure_union_le _ _).trans (add_le_add_right
    ((meas_ge_le_lintegral_div (μ := μ) (f := f) mf.aemeasurable (ENNReal.ofReal_ne_zero_iff.mpr hτ)
      ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right area _)) _))

private theorem geometric_budget {ρ h A : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hh : h < 1)
    (hA : 0 < A) {m : ℕ} (hm : 1 ≤ m) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ((n:ℝ)+1)*(m:ℝ)^⌊ε*n⌋₊ * (2*A*ρ^n) / (ρ^(n+1))^h ≤ δ := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmp : 0 < (m:ℝ) := zero_lt_one.trans_le hm'
  let v : ℝ := ρ^(1-h)
  have vpos : 0 < v := Real.rpow_pos_of_pos hρ _
  have vsmall : v < 1 := Real.rpow_lt_one hρ.le hρ1 (sub_pos.mpr hh)
  have near : ∀ᶠ ε : ℝ in 𝓝[>] 0, (m:ℝ)^ε*v < 1 := by
    have cv : Continuous (fun ε : ℝ ↦ (m:ℝ)^ε*v) := (Real.continuous_const_rpow hmp.ne').mul continuous_const
    exact (cv.continuousAt.eventually_lt continuousAt_const (by simpa using vsmall)).filter_mono nhdsWithin_le_nhds
  have posE : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,small⟩ := (posE.and near).exists
  have hε' : 0 < ε := hε
  let u := (m:ℝ)^ε*v
  have upos : 0 < u := mul_pos (Real.rpow_pos_of_pos hmp _) vpos
  let C := 2*A/ρ^h
  have tend : Tendsto (fun n : ℕ ↦ C*(((n:ℝ)+1)*u^n)) atTop (𝓝 0) := by
    have t₁ := tendsto_self_mul_const_pow_of_lt_one upos.le small
    have t₂ := tendsto_pow_atTop_nhds_zero_of_lt_one upos.le small
    simpa only [add_mul, one_mul, add_zero, mul_zero] using (tendsto_const_nhds (x := C)).mul (t₁.add t₂)
  refine ⟨ε,hε',?_⟩
  intro δ hδ
  filter_upwards [tend.eventually_lt_const hδ] with n hn
  refine le_trans ?_ hn.le
  have floor : (m:ℝ)^⌊ε*n⌋₊ ≤ ((m:ℝ)^ε)^n := by
    rw [← Real.rpow_mul_natCast hmp.le, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hm' (Nat.floor_le (mul_nonneg hε'.le (Nat.cast_nonneg _)))
  have hp : 0 < (ρ^(n+1))^h := Real.rpow_pos_of_pos (pow_pos hρ _) _
  calc
    _ ≤ ((n:ℝ)+1)*((m:ℝ)^ε)^n * (2*A*ρ^n) / (ρ^(n+1))^h := by gcongr
    _ = C*(((n:ℝ)+1)*u^n) := by
      dsimp [C,u,v]
      rw [← Real.rpow_pow_comm hρ.le, pow_succ (ρ^h), mul_pow, Real.rpow_sub hρ,
        Real.rpow_one, div_pow]
      field_simp


set_option maxHeartbeats 950000 in
/-- (RC2) for the actual bilateral weighted increment in an arbitrary translated
physical Haar group. All cutoffs are simultaneous in the coset and the two
directions, provided that the square-mass parameters in (RC1) are common. -/
theorem critical_occupation {B : ℂ} (hb : 1 < ‖B‖) (μ : Measure (complexPhaseGroup B))
    [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ] {g ρ η : ℝ} (hg : 0 < g)
    (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hcrit : g*‖B‖*ρ=1) (hη : 0 < η)
    (m₀ : ℕ) {A K h δ : ℝ} (hA : 0 < A) (hK : 0 < K) (hh : 0 < h) (hh1 : h < 1) (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ (ω : PhaseTorus) (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) →
      (∀ j, |d j| ≤ 1) → (∀ j, |e j| ≤ 1) → (∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) →
      DriftWeightBounds η m₀ (fun j ↦ c j*d j*e j) →
      μ {z | ENNReal.ofReal (r^h) < volume {t : ℝ | t ∈ Icc (-A) A ∧ |circleRay ‖B‖ g c d (ω+z.val) t| ≤ K*r}} ≤
        ENNReal.ofReal δ := by
  obtain ⟨m,hm⟩ := exists_nat_gt (ρ⁻¹)
  have hs : 1 ≤ (m:ℝ)*ρ := (inv_le_iff_one_le_mul₀ hρ).mp hm.le
  have hm1 : 1 ≤ m := by
    have : 0 < (m:ℝ) := (inv_pos.mpr hρ).trans hm
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne')
  obtain ⟨ε,hε,budget⟩ := geometric_budget hρ hρ1 hh1 hA hm1
  have half : 0 < δ/2 := half_pos hδ
  obtain ⟨N,hN⟩ := critical_shell_bounds hb μ hg hg1 hρ hρ1 hcrit hη m₀ m hm1 hs hA hK hε half
  obtain ⟨N',hN'⟩ := eventually_atTop.1 (budget (δ/2) half)
  let L := max N N'
  have near : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ρ^L := nhdsWithin_le_nhds (Iio_mem_nhds (pow_pos hρ L))
  filter_upwards [self_mem_nhdsWithin, near] with r hr hsmall
  have hr0 : 0 < r := hr
  obtain ⟨n,lo,hi⟩ := exists_nat_pow_near_of_lt_one hr0 (hsmall.le.trans (pow_le_one₀ hρ.le hρ1.le)) hρ hρ1
  have ln : L ≤ n := by
    by_contra! lt
    have := pow_le_pow_of_le_one hρ.le hρ1.le (show n+1 ≤ L by omega)
    linarith
  intro ω c d e hc hd he hmem hw
  obtain ⟨G,hG,mG,shell⟩ := hN n ((Nat.le_max_left N N').trans ln) ω c d e hc hd he hmem hw
  let U := (m:ℝ≥0∞)^⌊ε*n⌋₊
  have hU : 1 ≤ U := one_le_pow₀ (by exact_mod_cast hm1)
  let X (t : ℝ) := {z : complexPhaseGroup B | z ∈ G ∧ |circleRay ‖B‖ g c d (ω+z.val) t| ≤ K*ρ^n}
  have integ := geometric_shell_integral hA hρ hρ1.le n U hU (fun t ↦ μ (X t)) (fun t ↦ prob_le_one) shell
  let τ := (ρ^(n+1))^h
  have hτ : 0 < τ := Real.rpow_pos_of_pos (pow_pos hρ _) _
  have mark := retained_markov μ ‖B‖ g c d ω hG A (K*ρ^n) τ hτ _ integ
  have sub : {z : complexPhaseGroup B | ENNReal.ofReal (r^h) < volume {t : ℝ | t ∈ Icc (-A) A ∧ |circleRay ‖B‖ g c d (ω+z.val) t| ≤ K*r}} ⊆
      {z : complexPhaseGroup B | ENNReal.ofReal τ < volume {t : ℝ | t ∈ Icc (-A) A ∧ |circleRay ‖B‖ g c d (ω+z.val) t| ≤ K*ρ^n}} := by
    intro z hz
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (pow_pos hρ _).le lo.le hh.le)) (lt_of_lt_of_le hz (measure_mono ?_))
    rintro t ⟨ht,ht'⟩
    exact ⟨ht,ht'.trans (mul_le_mul_of_nonneg_left hi hK.le)⟩
  have numeric := hN' n ((Nat.le_max_right N N').trans ln)
  have ratio : ((n+1:ℕ):ℝ≥0∞)*U*ENNReal.ofReal (2*A*ρ^n) / ENNReal.ofReal τ ≤ ENNReal.ofReal (δ/2) := by
    refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal numeric)
    rw [ENNReal.ofReal_div_of_pos hτ, ENNReal.ofReal_mul (p := ((n:ℝ)+1)*(m:ℝ)^⌊ε*n⌋₊) (by positivity),
      ENNReal.ofReal_mul (p := ((n:ℝ)+1)) (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg m)]
    simp [U, ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one]
  calc
    _ ≤ _ := (measure_mono sub).trans mark
    _ ≤ ENNReal.ofReal (δ/2)+ENNReal.ofReal (δ/2) := add_le_add mG ratio
    _ = _ := by rw [← ENNReal.ofReal_add half.le half.le, add_halves]

end Weierstrass.CriticalRay
