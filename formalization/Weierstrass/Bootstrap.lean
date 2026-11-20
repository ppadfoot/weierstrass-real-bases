module

public import Std

public section

/-!
# Exponent closure at unequal and equal rates (Sections 5–6)

`S x s` denotes the manuscript's uniform information bound at log amplitude
`x` and exponent `s`, for fixed rates `L > M > 0` and all finite complexities.
The theorems take the analytic inputs as hypotheses. They prove the finite
backward bootstrap for all amplitudes in `(0,L)` at unequal rates, and the
two coupled strip iterations up to every strict test exponent at equal rates.
They use the standard library and apply in any Archimedean ordered field.
-/

namespace Weierstrass.Bootstrap

open Std Lean.Grind

variable {R : Type} [Field R] [LE R] [LT R] [LawfulOrderLT R]
    [IsLinearOrder R] [OrderedRing R]

/-- The sum of `n` copies of `d`. -/
@[expose] def multiple (d : R) : Nat → R
  | 0 => 0
  | n + 1 => multiple d n + d

/-- Positive increments eventually exceed any given bound. -/
@[expose] def ArchimedeanIncrements (R : Type) [Field R] [LE R] [LT R] : Prop :=
  ∀ d : R, 0 < d → ∀ b : R, ∃ n : Nat, b ≤ multiple d n

/-- A positive-step walk inside `(0,L)` must reach the upper boundary.
The predicate is propagated back along its finitely many interior steps. -/
private theorem ascend {L d : R} (arch : ArchimedeanIncrements R) (hd : 0 < d)
    (Q : R → Prop)
    (terminal : ∀ x, 0 < x → x < L → L ≤ x + d → Q x)
    (propagate : ∀ x, 0 < x → x < L → x + d < L → Q (x + d) → Q x) :
    ∀ x, 0 < x → x < L → Q x := by
  have bounded (n : Nat) : ∀ x, 0 < x → x < L → L ≤ x + multiple d n → Q x := by
    induction n with
    | zero => simp only [multiple]; intro x hx hL h; grind
    | succ n ih =>
      intro x hx hL h
      by_cases hstop : L ≤ x + d
      · exact terminal x hx hL hstop
      · have hnext : x + d < L := by grind
        apply propagate x hx hL hnext
        apply ih (x + d) (by grind) hnext
        simp only [multiple] at h
        grind
  obtain ⟨n, hn⟩ := arch d hd L
  intro x hx hL
  exact bounded n x hx hL (by grind)

/-- The reverse walk takes steps `x ↦ x-d` down to the lower boundary. -/
private theorem descend {L d : R} (arch : ArchimedeanIncrements R) (hd : 0 < d)
    (Q : R → Prop)
    (terminal : ∀ x, 0 < x → x < L → x ≤ d → Q x)
    (propagate : ∀ x, 0 < x → x < L → d < x → Q (x - d) → Q x) :
    ∀ x, 0 < x → x < L → Q x := by
  have reflected : ∀ y, 0 < y → y < L → Q (L - y) := by
    apply ascend arch hd
    · intro y hy hL h
      exact terminal (L-y) (by grind) (by grind) (by grind)
    · intro y hy hL hstep hnext
      apply propagate (L-y) (by grind) (by grind) (by grind)
      have e : L - y - d = L - (y + d) := by grind
      rw [e]; exact hnext
  intro x hx hL
  have e : L - (L-x) = x := by grind
  exact e ▸ reflected (L-x) (by grind) (by grind)

/-- A fixed positive gain suffices to reach any bounded target in finitely many steps. -/
private theorem finiteGainClosure {seed target gain : R} (arch : ArchimedeanIncrements R)
    (hgain : 0 < gain) (hrange : seed ≤ target) (Q : R → Prop) (base : Q seed)
    (step : ∀ s t, seed ≤ s → s ≤ target → seed ≤ t → t ≤ target → t ≤ s + gain → Q s → Q t) :
    Q target := by
  have ladder (n : Nat) : ∀ t, seed ≤ t → t ≤ target → t ≤ seed + multiple gain n → Q t := by
    induction n with
    | zero =>
      intro t ht ht1 bound
      simp only [multiple] at bound
      have e : t = seed := by grind
      rw [e]; exact base
    | succ n ih =>
      intro t ht ht1 bound
      simp only [multiple] at bound
      by_cases hfar : seed ≤ t - gain
      · exact step (t-gain) t hfar (by grind) ht ht1 (by grind)
          (ih (t-gain) hfar (by grind) (by grind))
      · exact step seed t (by grind) hrange ht ht1 (by grind) base
  obtain ⟨n, hn⟩ := arch gain hgain (target-seed)
  exact ladder n target hrange (by grind) (by grind)

/-- Inputs from Sections 2–6. At a strict descent, the inequalities on `t`
are exactly `t ≤ min 1 ((x+M)s/x)` since `x>0`. `wrap` is the composition
of the two reciprocal transfers at an amplitude above the critical value. -/
structure UnequalRateRules (S : R → R → Prop) (L M seed : R) : Prop where
  weaken : ∀ x s t, 0 < t → t ≤ s → S x s → S x t
  critical : ∀ x, 0 < x → x < L → x + M = L → S x 1
  halfSeed : ∀ x, 0 < x → x < L → L < x + M → S x seed
  wrap : ∀ x s, 0 < x → x < L → L < x + M → 0 < s → s ≤ 1 →
    S (x + M - L) s → S x s
  differentiate : ∀ x s t, 0 < x → x + M < L → 0 < s → s ≤ 1 →
    0 < t → t ≤ 1 → t * x ≤ (x + M) * s → S (x + M) s → S x t

/-- The analytic recurrence closes for every positive seed at most one.
The specific seed in the manuscript is `1/2`. No hypothesis about critical
visits or the distribution of a rotation orbit is needed. -/
theorem unequalRateClosure {S : R → R → Prop} {L M seed : R}
    (arch : ArchimedeanIncrements R) (hM : 0 < M) (hrates : M < L)
    (hseed : 0 < seed) (hseed1 : seed ≤ 1) (rules : UnequalRateRules S L M seed) :
    ∀ x, 0 < x → x < L → S x 1 := by
  have hL : 0 < L := by grind
  have hseedM : 0 < M * seed := OrderedRing.mul_pos hM hseed
  let gain := (M * seed) * L⁻¹
  have hgain : 0 < gain := OrderedRing.mul_pos hseedM (Field.IsOrdered.inv_pos_iff.mpr hL)
  have gain_eq : gain * L = M * seed := by
    simp only [gain, Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_gt hL),
      Semiring.mul_one]
  -- Reach the seed by following consecutive non-wrapping steps to a critical value or a wrap.
  have seedAt : ∀ x, 0 < x → x < L → S x seed := by
    apply ascend arch hM
    · intro x hx hxL hstop
      by_cases heq : x + M = L
      · exact rules.weaken x 1 seed hseed hseed1 (rules.critical x hx hxL heq)
      · exact rules.halfSeed x hx hxL (by grind)
    · intro x hx hxL hstep hnext
      apply rules.differentiate x seed seed hx hstep hseed hseed1 hseed hseed1 _ hnext
      grind
  -- A run of wraps must end. At the first non-wrap, descent provides an additive gain.
  have improve (s t : R) (hs : seed ≤ s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
      (hstep : t ≤ s + gain) (source : ∀ x, 0 < x → x < L → S x s) :
      ∀ x, 0 < x → x < L → S x t := by
    apply descend (d := L-M) arch (by grind)
    · intro x hx hxL hterminal
      by_cases heq : x + M = L
      · exact rules.weaken x 1 t ht ht1 (rules.critical x hx hxL heq)
      · have hbelow : x + M < L := by grind
        apply rules.differentiate x s t hx hbelow (by grind) hs1 ht ht1 _
          (source (x+M) (by grind) hbelow)
        have prod := OrderedRing.mul_le_mul_of_nonneg_right hstep (Preorder.le_of_lt hx)
        have small := OrderedRing.mul_le_mul_of_nonneg_left (Preorder.le_of_lt hxL)
          (Preorder.le_of_lt hgain)
        have gainBound := OrderedRing.mul_le_mul_of_nonneg_left hs (Preorder.le_of_lt hM)
        grind
    · intro x hx hxL hwrap hnext
      apply rules.wrap x t hx hxL (by grind) ht ht1
      have e : x + M - L = x - (L-M) := by grind
      rw [e]; exact hnext
  apply finiteGainClosure arch hgain hseed1 (fun s => ∀ x, 0 < x → x < L → S x s) seedAt
  intro s t hs hs1 ht ht1 bound
  exact improve s t hs hs1 (by grind) ht1 bound

/-- `StrictBound test s` is the quantifier over `0<h<s` in (anchor).
`test h` stands for the entire scale limit with all remaining parameters. -/
@[expose] def StrictBound (test : R → Prop) (s : R) : Prop := ∀ h, 0 < h → h < s → test h

private theorem weakenStrict {test : R → Prop} {s t : R} (hle : t ≤ s)
    (bound : StrictBound test s) : StrictBound test t := by
  intro h hh hlt
  exact bound h hh (by grind)

/-- Exact right-hand side of transverse differentiation (D). -/
@[expose] noncomputable def descentExponent (x M s : R) : R := open Classical in
  if 1 ≤ (x+M)*s/x then 1 else (x+M)*s/x

/-- Exact unequal-rate inputs from the manuscript imply `S₁` for both
orientations. The orientation with larger physical log rate is called
`original`. In the recursion a wrap uses both individual reciprocal transfers.
A single further transfer establishes the smaller-rate orientation. -/
theorem unequalRatePair {L M : R} (arch : ArchimedeanIncrements R) (hM : 0 < M)
    (hrates : M < L) (original reversed : R → R → Prop)
    (critical : ∀ x, 0 < x → x < L → x+M = L → StrictBound (original x) 1)
    (halfSeed : ∀ x, 0 < x → x < L → L < x+M → StrictBound (original x) (1/2))
    (transfer : ∀ x s, 0 < x → x < L → L < x+M → 0 < s → s ≤ 1 →
      StrictBound (reversed (L-x)) s → StrictBound (original x) s)
    (reverseTransfer : ∀ y s, 0 < y → y < M → M < y+L → 0 < s → s ≤ 1 →
      StrictBound (original (M-y)) s → StrictBound (reversed y) s)
    (differentiate : ∀ x s, 0 < x → x+M < L → 0 < s → s ≤ 1 →
      StrictBound (original (x+M)) s → StrictBound (original x) (descentExponent x M s)) :
    (∀ x, 0 < x → x < L → StrictBound (original x) 1) ∧
    (∀ y, 0 < y → y < M → StrictBound (reversed y) 1) := by
  have rules : UnequalRateRules (fun x s => StrictBound (original x) s) L M (1/2) := by
    refine ⟨fun _ _ _ _ h => weakenStrict h, critical, halfSeed, ?_, ?_⟩
    · intro x s hx hxL hwrap hs hs1 hsource
      apply transfer x s hx hxL hwrap hs hs1
      apply reverseTransfer (L-x) s (by grind) (by grind) (by grind) hs hs1
      have e : M-(L-x) = x+M-L := by grind
      rw [e]; exact hsource
    · intro x s t hx hxL hs hs1 _ ht1 hmul hsource
      apply weakenStrict _ (differentiate x s hx hxL hs hs1 hsource)
      have hdiv : t ≤ (x+M)*s/x := by
        rw [Field.div_eq_mul_inv]
        exact (Field.IsOrdered.le_mul_inv_iff_mul_le _ _ hx).2 hmul
      unfold descentExponent
      split <;> assumption
  have full := unequalRateClosure arch hM hrates (show (0:R) < 1/2 by grind)
    (show (1/2:R) ≤ 1 by grind) rules
  refine ⟨full, ?_⟩
  intro y hy hyM
  exact reverseTransfer y 1 hy hyM (by grind) (by grind) (by grind)
    (full (M-y) (by grind) (by grind))

/-- Right-hand side of (B1): `p*s + (1-p)*min(1, p*s+t)`. -/
@[expose] noncomputable def stripExponent (p s t : R) : R := open Classical in
  p*s + (1-p) * (if 1 ≤ p*s+t then 1 else p*s+t)

private theorem commonGain {a b : R} (ha : 0 < a) (hb : 0 < b) :
    ∃ d, 0 < d ∧ d ≤ a ∧ d ≤ b := by
  by_cases h : a ≤ b
  · exact ⟨a, ha, by grind, h⟩
  · exact ⟨b, hb, by grind, by grind⟩

/-- Uniform room below a fixed `target<1`, for one orientation of (B1). -/
private theorem stripGain {p seed target : R} (hp : 0 < p) (hp1 : p < 1)
    (hseed : 0 < seed) (htarget : target < 1) :
    ∃ d, 0 < d ∧ ∀ s, seed ≤ s → s ≤ target → s + d ≤ stripExponent p s s := by
  have hc : 0 < 1-p := by grind
  obtain ⟨d, hd, hcap, hlinear⟩ := commonGain
    (OrderedRing.mul_pos hc (show 0 < 1-target by grind))
    (OrderedRing.mul_pos hc (OrderedRing.mul_pos hp hseed))
  refine ⟨d, hd, ?_⟩
  intro s hlow hhigh
  unfold stripExponent
  split
  · have bound := OrderedRing.mul_le_mul_of_nonneg_left (show 1-target ≤ 1-s by grind)
        (Preorder.le_of_lt hc)
    grind
  · have inner := OrderedRing.mul_le_mul_of_nonneg_left hlow (Preorder.le_of_lt hp)
    have bound := OrderedRing.mul_le_mul_of_nonneg_left inner (Preorder.le_of_lt hc)
    grind

/-- The full equal-rate conclusion follows from (B1) in both orientations
and their `1/2` seeds. Each fixed strict test exponent is reached by finitely
many strip estimates. The endpoint follows precisely because (anchor)
quantifies over strict test exponents. -/
theorem equalRateClosure {alpha : R} (arch : ArchimedeanIncrements R)
    (ha : 0 < alpha) (ha1 : alpha < 1) (original reversed : R → Prop)
    (originalSeed : StrictBound original (1/2)) (reversedSeed : StrictBound reversed (1/2))
    (originalStrip : ∀ s t, 0 < s → s ≤ 1 → 0 < t → t ≤ 1 →
      StrictBound original s → StrictBound reversed t →
      StrictBound original (stripExponent (1-alpha) s t))
    (reversedStrip : ∀ s t, 0 < s → s ≤ 1 → 0 < t → t ≤ 1 →
      StrictBound reversed s → StrictBound original t →
      StrictBound reversed (stripExponent alpha s t)) :
    StrictBound original 1 ∧ StrictBound reversed 1 := by
  have bothNear (target : R) (ht : 1/2 ≤ target) (ht1 : target < 1) :
      StrictBound original target ∧ StrictBound reversed target := by
    obtain ⟨u, hu, leftGain⟩ := stripGain (p := 1-alpha) (seed := (1/2:R))
      (by grind) (by grind) (by grind) ht1
    obtain ⟨v, hv, rightGain⟩ := stripGain (seed := (1/2:R)) ha ha1 (by grind) ht1
    obtain ⟨d, hd, hleft, hright⟩ := commonGain hu hv
    apply finiteGainClosure arch hd ht
      (fun s => StrictBound original s ∧ StrictBound reversed s) ⟨originalSeed, reversedSeed⟩
    intro s t hs hsT _ htT htStep current
    have hs0 : 0 < s := by grind
    have hs1 : s ≤ 1 := by grind
    have orig := leftGain s hs hsT
    have rev := rightGain s hs hsT
    exact ⟨weakenStrict (by grind) (originalStrip s s hs0 hs1 hs0 hs1 current.1 current.2),
      weakenStrict (by grind) (reversedStrip s s hs0 hs1 hs0 hs1 current.2 current.1)⟩
  have bothTests (h : R) (hh : 0 < h) (hh1 : h < 1) : original h ∧ reversed h := by
    let target := (h+1)/2
    have ht : 1/2 ≤ target := by dsimp [target]; grind
    have ht1 : target < 1 := by dsimp [target]; grind
    have hlt : h < target := by dsimp [target]; grind
    obtain ⟨ho, hr⟩ := bothNear target ht ht1
    exact ⟨ho h hh hlt, hr h hh hlt⟩
  exact ⟨fun h hh hh1 => (bothTests h hh hh1).1, fun h hh hh1 => (bothTests h hh hh1).2⟩

end Weierstrass.Bootstrap
