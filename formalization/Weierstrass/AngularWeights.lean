module

public import Weierstrass.RayInformationTransport

/-! Finite-window nondegeneracy for products of the angular factors in §2. -/
@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace Weierstrass.Angular

/-- The absolute value of one angular projection. -/
def projection (v ζ : Circle) (j : ℤ) : ℝ := |((v*ζ^j : Circle) : ℂ).re|

theorem projection_nonneg (v ζ : Circle) (j : ℤ) : 0 ≤ projection v ζ j := abs_nonneg _

theorem projection_le_one (v ζ : Circle) (j : ℤ) : projection v ζ j ≤ 1 :=
  (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe _)

theorem projection_shift (v ζ : Circle) (i j : ℤ) :
    projection v ζ (i+j) = projection (v*ζ^i) ζ j := by simp [projection, zpow_add, mul_assoc]

theorem projection_reverse (v ζ : Circle) (j : ℤ) :
    projection v ζ (-j) = projection v⁻¹ ζ j := by
  have e : (v*ζ^(-j))⁻¹ = v⁻¹*ζ^j := by simp [mul_comm]
  rw [projection, projection, ← e, Circle.coe_inv_eq_conj, Complex.conj_re]

private theorem sq_of_zero_projection (x : Circle) (hx : (x:ℂ).re = 0) : x^2 = -1 := by
  have hn := Circle.normSq_coe x
  rw [Complex.normSq_apply, hx, zero_mul, zero_add] at hn
  apply Circle.ext; apply Complex.ext <;> simp [pow_two, hx, hn]

theorem exists_nonzero_sample {ζ : Circle} (hζ : ¬IsOfFinOrder ζ)
    (k : ℕ) (v : Fin k → Circle) :
    ∃ j : Fin (k+1), ∀ i, ((v i * ζ^j.val : Circle):ℂ).re ≠ 0 := by
  by_contra! h
  choose f hf using h
  apply Fintype.not_injective_of_card_lt f (by simp)
  intro a b hab
  have z := (sq_of_zero_projection _ (hf a)).trans (sq_of_zero_projection _ (hf b)).symm
  rw [hab, mul_pow, mul_pow, mul_left_cancel_iff] at z
  simp only [← pow_mul] at z
  have eq := (pow_inj_iff_of_orderOf_eq_zero (orderOf_eq_zero_iff.mpr hζ)).mp z
  apply Fin.ext
  omega

/-- A uniform positive lower bound occurs within k+1 consecutive samples of
any product of k angular factors for an infinite-order rotation. -/
theorem infinite_rotation_window {ζ : Circle} (hζ : ¬IsOfFinOrder ζ) (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Fin k → Circle, ∀ o : ℤ, ∃ j : Fin (k+1),
      δ ≤ ∏ i, projection (v i) ζ (o+j.val) := by
  let f (j : Fin (k+1)) (v : Fin k → Circle) : ℝ := ∏ i, projection (v i) ζ j.val
  let W (v : Fin k → Circle) := Finset.univ.sup' Finset.univ_nonempty (fun j ↦ f j v)
  have cf (j : Fin (k+1)) : Continuous (f j) := by
    apply continuous_finsetProd
    intro i _
    exact (Complex.continuous_re.comp (continuous_subtype_val.comp ((continuous_apply i).mul continuous_const))).abs
  have cw : Continuous W := Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ ↦ cf i)
  have positive (v : Fin k → Circle) : 0 < W v := by
    obtain ⟨j,hj⟩ := exists_nonzero_sample hζ k v
    refine lt_of_lt_of_le ?_ (Finset.le_sup' (fun i ↦ f i v) (Finset.mem_univ j))
    apply Finset.prod_pos
    intro i _
    exact abs_pos.mpr (by simpa only [zpow_natCast] using hj i)
  obtain ⟨v₀,_,hm⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Fin k → Circle)) cw.continuousOn
  refine ⟨W v₀, positive v₀,?_⟩
  intro v o
  let v' (i : Fin k) := v i*ζ^o
  obtain ⟨j,_,eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j ↦ f j v')
  refine ⟨j, (hm (Set.mem_univ v')).trans ?_⟩
  change W v' ≤ _
  rw [show W v' = f j v' from eq]
  simp only [f, v', projection_shift, le_refl]

/-- One definite sample in each fixed window implies a linear square mass
in every sufficiently long interval of integer indices. -/
theorem square_mass_of_windows {w : ℤ → ℝ} (bounded : ∀ j, |w j| ≤ 1)
    {D : ℕ} (hD : 0 < D) {δ : ℝ} (hδ : 0 < δ)
    (hits : ∀ o : ℤ, ∃ l : Fin D, δ ≤ |w (o+l.val)|) :
    CriticalRay.DriftWeightBounds (δ^2/(2*D)) (2*D) w := by
  refine ⟨bounded,?_⟩
  intro i j gap
  let n := (j-i).toNat
  let q := n/D
  have hn : (n:ℤ) = j-i := Int.toNat_of_nonneg (by omega)
  have hcard : (Finset.Ico i j).card = n := Int.card_Ico _ _
  have qpos : 1 ≤ q := (Nat.le_div_iff_mul_le hD).mpr (by dsimp [n]; omega)
  have nq : n ≤ 2*q*D := by
    have rem := Nat.mod_lt n hD
    have eq := Nat.mod_add_div n D
    have qD : D ≤ q*D := Nat.le_mul_of_pos_left _ qpos
    dsimp [q] at *
    nlinarith
  choose l hl using hits
  let off (a : Fin q) := a.val*D+(l (i+(a.val*D:ℕ))).val
  let ix (a : Fin q) := i+(off a:ℕ)
  have bounds (a : Fin q) : a.val*D ≤ off a ∧ off a < (a.val+1)*D := by
    dsimp [off]
    rw [Nat.add_mul, Nat.one_mul]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (l _).isLt _⟩
  have ixmem (a : Fin q) : ix a ∈ Finset.Ico i j := by
    have upper : off a < n := (bounds a).2.trans_le ((Nat.mul_le_mul_right D a.isLt).trans (Nat.div_mul_le_self n D))
    change i+(off a:ℤ) ∈ Finset.Ico i j
    rw [Finset.mem_Ico]; omega
  have inject : Function.Injective ix := by
    apply StrictMono.injective
    intro a b hab
    have h := (bounds a).2.trans_le ((Nat.mul_le_mul_right D hab).trans (bounds b).1)
    dsimp only [ix]
    omega
  let select (a : Fin q) : Finset.Ico i j := ⟨ix a,ixmem a⟩
  have sinj : Function.Injective select := fun a b eq ↦ inject (congrArg Subtype.val eq)
  have lower (a : Fin q) : δ^2 ≤ (w (select a))^2 := by
    have hit := hl (i+(a.val*D:ℕ))
    simpa only [select,ix,off,Nat.cast_add, ← add_assoc,sq_abs] using pow_le_pow_left₀ hδ.le hit 2
  have mass : (q:ℝ)*δ^2 ≤ ∑ a : Finset.Ico i j, (w a)^2 := by
    calc
      _ = ∑ _ : Fin q, δ^2 := by simp
      _ ≤ ∑ a : Fin q, (w (select a))^2 := Finset.sum_le_sum (fun a _ ↦ lower a)
      _ = ∑ a ∈ Finset.univ.image select, (w a)^2 := by rw [Finset.sum_image sinj.injOn]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
  rw [hcard]
  refine le_trans ?_ mass
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2*(D:ℝ))]
  have size : (n:ℝ) ≤ 2*q*D := by exact_mod_cast nq
  nlinarith only [mul_le_mul_of_nonneg_left size (sq_nonneg δ)]


/-- A finite-order rotation admits a ray whose entire orbit stays away from
the two zeros of the real part. The ray is chosen explicitly at angle π/(4p). -/
theorem finite_rotation_ray {ζ : Circle} (fin : IsOfFinOrder ζ) :
    ∃ v : Circle, ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℤ, δ ≤ projection v ζ j := by
  classical
  let p := orderOf ζ
  have hp : 0 < p := fin.orderOf_pos
  let N := 4*p
  have hn : 0 < N := by dsimp [N]; positivity
  let v := Circle.exp (Real.pi/N)
  have vn : v^N ≠ 1 := by
    rw [show v^N = Circle.exp Real.pi from by
      dsimp [v]; rw [← Circle.exp_natCast_mul]; congr 1; field_simp]
    exact Circle.exp_pi_ne_one
  have nonzero (j : ℤ) : 0 < projection v ζ j := by
    apply abs_pos.mpr
    intro zero
    have sq := sq_of_zero_projection (v*ζ^j) zero
    have four : (v*ζ^j)^4 = 1 := by
      calc _ = ((v*ζ^j)^2)^2 := by rw [← pow_mul]
           _ = _ := by rw [sq]; simp
    have bn : (v*ζ^j)^N = 1 := by rw [show N = 4*p from rfl, pow_mul, four, one_pow]
    have zn : (ζ^j)^N = 1 := by
      rw [show N = p*4 from Nat.mul_comm _ _, pow_mul, ← zpow_natCast (ζ^j) p, ← zpow_mul, mul_comm j,
        zpow_mul, zpow_natCast, show ζ^p = 1 from pow_orderOf_eq_one ζ, one_zpow, one_pow]
    rw [mul_pow, zn, mul_one] at bn
    exact vn bn
  let samples := Finset.range p
  have nz : samples.Nonempty := Finset.nonempty_range_iff.mpr hp.ne'
  let δ := samples.inf' nz (fun i ↦ projection v ζ i)
  obtain ⟨i,_,eq⟩ := Finset.exists_mem_eq_inf' nz (fun i ↦ projection v ζ i)
  refine ⟨v,δ,by change 0 < samples.inf' nz _; rw [eq]; exact nonzero _,?_⟩
  intro j
  obtain ⟨n,hn',eq⟩ := Finset.mem_image.mp (fin.mem_zpowers_iff_mem_range_orderOf.mp
    (show ζ^j ∈ Subgroup.zpowers ζ from ⟨j,rfl⟩))
  have val : projection v ζ j = projection v ζ n := by simp only [projection,zpow_natCast,eq]
  rw [val]
  apply Finset.inf'_le _ hn'

/-- Allowed complex unit rays. For a finite-order rotation the base ray is
chosen by the preceding theorem. Reversal, rotation, and sign are explicit. -/
def Permitted (ζ v₀ v : Circle) : Prop :=
  ¬IsOfFinOrder ζ ∨ ∃ n : ℤ, v = v₀*ζ^n ∨ v = -(v₀*ζ^n) ∨ v = v₀⁻¹*ζ^n ∨ v = -(v₀⁻¹*ζ^n)

theorem permitted_base (ζ v : Circle) : Permitted ζ v v :=
  Or.inr ⟨0,Or.inl (by simp)⟩

theorem permitted_shift {ζ v₀ v : Circle} (h : Permitted ζ v₀ v) (k : ℤ) :
    Permitted ζ v₀ (v*ζ^k) := by
  rcases h with h|⟨n,h|h|h|h⟩
  · exact Or.inl h
  all_goals subst v; right; use n+k; simp [zpow_add,mul_assoc]

theorem permitted_inv {ζ v₀ v : Circle} (h : Permitted ζ v₀ v) : Permitted ζ v₀ v⁻¹ := by
  rcases h with h|⟨n,h|h|h|h⟩
  · exact Or.inl h
  all_goals subst v; right; use -n; simp [zpow_neg,mul_comm]

theorem projection_neg (v ζ : Circle) (j : ℤ) : projection (-v) ζ j = projection v ζ j := by
  simp only [projection, neg_mul, Circle.coe_neg, Complex.neg_re, abs_neg]

/-- The real directions contribute just a sign at each time, so absolute
products simultaneously represent all real sign choices. -/
def Weight (ζ v₀ : Circle) (k : ℕ) (w : ℤ → ℝ) : Prop :=
  ∃ d ≤ k, ∃ v : Fin d → Circle, (∀ i, Permitted ζ v₀ (v i)) ∧
    ∀ j, |w j| = ∏ i, projection (v i) ζ j

theorem weight_one (ζ v₀ : Circle) (k : ℕ) : Weight ζ v₀ k (fun _ ↦ 1) :=
  ⟨0,Nat.zero_le _,fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i,by simp⟩

theorem Weight.bounded {ζ v₀ : Circle} {k : ℕ} {w : ℤ → ℝ} (hw : Weight ζ v₀ k w) (j : ℤ) : |w j| ≤ 1 := by
  obtain ⟨d,_,v,_,hw⟩ := hw
  rw [hw]
  exact Finset.prod_le_one (fun _ _ ↦ projection_nonneg _ _ _) (fun _ _ ↦ projection_le_one _ _ _)

theorem Weight.shift {ζ v₀ : Circle} {k : ℕ} {w : ℤ → ℝ} (hw : Weight ζ v₀ k w) (o : ℤ) :
    Weight ζ v₀ k (fun j ↦ w (j+o)) := by
  obtain ⟨d,h,v,hv,hw⟩ := hw
  refine ⟨d,h,fun i ↦ v i*ζ^o,fun i ↦ permitted_shift (hv i) o,?_⟩
  intro j
  change |w (j+o)| = _
  rw [add_comm j o,hw]
  simp only [projection_shift]

theorem Weight.reverse {ζ v₀ : Circle} {k : ℕ} {w : ℤ → ℝ} (hw : Weight ζ v₀ k w) :
    Weight ζ v₀ k (fun j ↦ w (-j)) := by
  obtain ⟨d,h,v,hv,hw⟩ := hw
  refine ⟨d,h,fun i ↦ (v i)⁻¹,fun i ↦ permitted_inv (hv i),?_⟩
  intro j
  rw [hw]
  simp only [projection_reverse]

theorem Weight.mul_projection {ζ v₀ v : Circle} {k : ℕ} {w : ℤ → ℝ} (hw : Weight ζ v₀ k w)
    (hv : Permitted ζ v₀ v) {a : ℤ → ℝ} (ha : ∀ j, |a j| = projection v ζ j) :
    Weight ζ v₀ (k+1) (fun j ↦ w j*a j) := by
  obtain ⟨d,h,u,hu,hw⟩ := hw
  refine ⟨d+1,by omega,Fin.cons v u,?_,?_⟩
  · exact Fin.cases (by simpa using hv) (fun i ↦ by simpa using hu i)
  · intro j
    simp [abs_mul, hw, ha, Fin.prod_univ_succ, mul_comm]

theorem finite_projection_lower {ζ v₀ v : Circle} {δ : ℝ} (fin : IsOfFinOrder ζ)
    (base : ∀ j, δ ≤ projection v₀ ζ j) (hv : Permitted ζ v₀ v) (j : ℤ) : δ ≤ projection v ζ j := by
  rcases hv with h|⟨n,h|h|h|h⟩
  · exact False.elim (h fin)
  all_goals subst v
  · rw [← projection_shift]; apply base
  · rw [projection_neg, ← projection_shift]; apply base
  · rw [← projection_shift, ← projection_reverse]; apply base
  · rw [projection_neg, ← projection_shift, ← projection_reverse]; apply base


/-- The finite-orbit hypothesis on the base ray in the manuscript. -/
def AdmissibleBase (ζ v₀ : Circle) : Prop :=
  IsOfFinOrder ζ → ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℤ, δ ≤ projection v₀ ζ j

theorem exists_admissibleBase (ζ : Circle) : ∃ v : Circle, AdmissibleBase ζ v := by
  by_cases h : IsOfFinOrder ζ
  · obtain ⟨v,hv⟩ := finite_rotation_ray h
    exact ⟨v,fun _ ↦ hv⟩
  · exact ⟨1,fun eq ↦ False.elim (h eq)⟩

theorem Weight.mul {ζ v₀ : Circle} {k₁ k₂ : ℕ} {a b : ℤ → ℝ}
    (ha : Weight ζ v₀ k₁ a) (hb : Weight ζ v₀ k₂ b) :
    Weight ζ v₀ (k₁+k₂) (fun j ↦ a j*b j) := by
  obtain ⟨m,hm,u,hu,ha⟩ := ha
  obtain ⟨n,hn,v,hv,hb⟩ := hb
  refine ⟨m+n,by omega,Fin.addCases u v,?_,?_⟩
  · exact Fin.addCases (fun i ↦ by simpa using hu i) (fun j ↦ by simpa using hv j)
  · intro j
    simp only [abs_mul,ha,hb,Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right]

theorem Weight.of_abs_eq_one {ζ v₀ : Circle} (k : ℕ) {w : ℤ → ℝ} (h : ∀ j, |w j|=1) :
    Weight ζ v₀ k w :=
  ⟨0,Nat.zero_le _,fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i,by simpa using h⟩

theorem permitted_weight_windows {ζ v₀ : Circle} (base : AdmissibleBase ζ v₀) (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w, Weight ζ v₀ k w → ∀ o : ℤ, ∃ j : Fin (k+1), δ ≤ |w (o+j.val)| := by
  classical
  by_cases fin : IsOfFinOrder ζ
  · obtain ⟨a,ha,hl⟩ := base fin
    let u := min 1 a
    have hu : 0 < u := lt_min zero_lt_one ha
    refine ⟨u^k,pow_pos hu _,?_⟩
    intro w hw o
    obtain ⟨d,dk,v,hv,eq⟩ := hw
    refine ⟨0,?_⟩
    rw [eq]
    calc
      u^k ≤ u^d := pow_le_pow_of_le_one hu.le (min_le_left _ _) dk
      _ = ∏ _ : Fin d, u := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ hu.le) (fun i _ ↦ (min_le_right 1 a).trans (finite_projection_lower fin hl (hv i) _))
  · choose a pos hit using fun d : Fin (k+1) ↦ infinite_rotation_window fin d.val
    let δ := Finset.univ.inf' Finset.univ_nonempty a
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty a
    refine ⟨δ,by change 0 < Finset.univ.inf' _ a; rw [hi]; exact pos i,?_⟩
    intro w hw o
    obtain ⟨d,dk,v,_,eq⟩ := hw
    let i : Fin (k+1) := ⟨d,by omega⟩
    obtain ⟨j,hj⟩ := hit i v o
    refine ⟨⟨j.val,by have := j.isLt; dsimp [i] at *; omega⟩,?_⟩
    rw [eq]
    exact (Finset.inf'_le a (Finset.mem_univ i)).trans hj

/-- (RC1) simultaneously on all permitted products up to the specified
complexity, with constants uniform under shifts and sign choices. -/
theorem permitted_weight_square_mass {ζ v₀ : Circle} (base : AdmissibleBase ζ v₀) (k : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ w, Weight ζ v₀ k w → CriticalRay.DriftWeightBounds η (2*(k+1)) w := by
  obtain ⟨δ,hδ,hit⟩ := permitted_weight_windows base k
  refine ⟨δ^2/(2*(k+1:ℕ)),by positivity,?_⟩
  intro w hw
  exact square_mass_of_windows hw.bounded (by omega : 0 < k+1) hδ (hit w hw)

/-- The family of weighted rays allowing at most k weight factors and a single
physical projection. -/
def rayFamily (ζ v₀ : Circle) (k : ℕ) : Set RayParameters :=
  {p | Weight ζ v₀ k p.1 ∧ Weight ζ v₀ 1 p.2}

theorem rayInformation_critical_family {B : ℂ} (hb : 1 < ‖B‖) {g ρ : ℝ} (hg : 0 < g)
    (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hcrit : g*‖B‖*ρ=1)
    {ζ v₀ : Circle} (base : AdmissibleBase ζ v₀) {e : ℤ → ℝ} (he : Weight ζ v₀ 1 e)
    (hmem : ∀ x, CriticalRay.transverseOrbit ρ e x ∈ complexPhaseGroup B) (k : ℕ) :
    RayInformation B g 1 (rayFamily ζ v₀ k) := by
  obtain ⟨η,hη,sq⟩ := permitted_weight_square_mass base (k+2)
  apply rayInformation_critical hb hg hg1 hρ hρ1 hcrit hη (2*(k+2+1))
  intro p ⟨hc,hd⟩
  exact ⟨hc.bounded,hd.bounded,e,he.bounded,hmem,sq _ ((hc.mul hd).mul he)⟩


/-- Normalize a nonzero multiplier without discarding its sign or argument. -/
def rotation (D : ℂ) (hD : D ≠ 0) : Circle :=
  ⟨D/(‖D‖:ℂ), by apply mem_sphere_zero_iff_norm.mpr; simp [hD]⟩

theorem rotation_inv {D : ℂ} (hD : D ≠ 0) :
    rotation D⁻¹ (inv_ne_zero hD) = (rotation D hD)⁻¹ := by
  apply Circle.ext
  change D⁻¹/(‖D⁻¹‖:ℂ)=(D/(‖D‖:ℂ))⁻¹
  rw [norm_inv, Complex.ofReal_inv, inv_div]; simp [div_eq_mul_inv,mul_comm]

theorem abs_rayProjection {D : ℂ} (hD : D ≠ 0) (v : Circle) (j : ℤ) :
    |rayProjection D v j| = projection v (rotation D hD) j := by
  simp only [rayProjection,projection,Circle.coe_mul,Circle.coe_zpow]; rfl

theorem abs_real_rayProjection {D v : ℝ} (hD : D ≠ 0) (hv : |v|=1) (j : ℤ) :
    |rayProjection (D:ℂ) (v:ℂ) j| = 1 := by
  have eq : rayProjection (D:ℂ) (v:ℂ) j = v*(D/|D|)^j := by
    simp only [rayProjection,Complex.norm_real,Real.norm_eq_abs, ← Complex.ofReal_div,
      ← Complex.ofReal_zpow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [eq,abs_mul,abs_zpow,hv,abs_div,abs_abs,div_self (abs_pos.mpr hD).ne',one_zpow,one_mul]

theorem Weight.rayProjection {D : ℂ} (hD : D ≠ 0) (v v₀ : Circle) (hv : Permitted (rotation D hD) v₀ v) :
    Weight (rotation D hD) v₀ 1 (rayProjection D v) := by
  refine ⟨1,le_rfl,fun _ ↦ v,fun _ ↦ hv,?_⟩
  intro j; simp [abs_rayProjection hD]

theorem projection_inv_rotation (v ζ : Circle) (j : ℤ) : projection v ζ⁻¹ j = projection v⁻¹ ζ j := by
  rw [← projection_reverse]
  simp only [projection,inv_zpow,zpow_neg]

/-- Multiplying by an arbitrary real sign sequence preserves the weight complexity. -/
theorem Weight.mul_sign {ζ v₀ : Circle} {k : ℕ} {w a : ℤ → ℝ} (hw : Weight ζ v₀ k w)
    (ha : ∀ j, |a j|=1) : Weight ζ v₀ k (fun j ↦ w j*a j) := by
  obtain ⟨d,hd,v,hv,h⟩ := hw
  exact ⟨d,hd,v,hv,fun j ↦ by simp [abs_mul,ha,h]⟩

end Weierstrass.Angular
