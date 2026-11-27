import Mixes.Joint

/-!
# Part II: Lemma 25 (`j:lem:group`) and Proposition 26 (`j:prop:split`)

* `JointSplit.Step`, `JointSplit.lem25`: the grouping procedure of Lemma 25 (replace two smallest
  numbers by their sum) on a multiset of reals; it terminates, and when it stops it has two
  numbers, or three numbers any two of which add up to more than `s`, all at most `s`.
* `JointSplit.three_groups_bound`: the remark after Lemma 25 (three groups give `C_k < s - 2μ`).
* `JointSplit.prop26_kappa`, `prop26_i`, `prop26_ii`, `prop26_iii`, `prop26_iii_general`,
  `prop26`: Proposition 26, the splitting of a distribution with two steps into its two slabs.
  It uses only Proposition 24 (`prop24`) and Lemma 18 (`lem18`) from `Joint`.

Segment constructions are tracked by `SegRep s F`: `F` is the family of marginals of a finite
mixture of uniform distributions on segments with endpoints in `H_s`; it is closed under
mixtures (`SegRep.mix`) and coordinatewise affine maps (`SegRep.affine`, which covers the
grouping `X_j = ℓ_j W / C`, reorderings and the reflection `C_i - Y_i`).
-/

open MeasureTheory Set

noncomputable section

namespace Mixes

namespace JointSplit

/-! ### Lemma 25 (`j:lem:group`) -/

/-- One step of the procedure of Lemma 25: if at least three numbers remain (`R ≠ 0`) and two
smallest numbers `a`, `b` have sum at most `s`, they are replaced by `a + b`. -/
def Step (s : ℝ) (M M' : Multiset ℝ) : Prop :=
  ∃ a b R, M = a ::ₘ b ::ₘ R ∧ R ≠ 0 ∧ (∀ x ∈ R, a ≤ x ∧ b ≤ x) ∧ a + b ≤ s ∧
    M' = (a + b) ::ₘ R

/-- The procedure has stopped at `M`: no step applies. -/
def Stopped (s : ℝ) (M : Multiset ℝ) : Prop := ¬∃ M', Step s M M'

lemma Step.card {s : ℝ} {M M' : Multiset ℝ} (h : Step s M M') :
    Multiset.card M' + 1 = Multiset.card M := by
  obtain ⟨a, b, R, rfl, -, -, -, rfl⟩ := h
  simp

lemma exists_min (M : Multiset ℝ) (h : M ≠ 0) : ∃ a R, M = a ::ₘ R ∧ ∀ x ∈ R, a ≤ x := by
  induction M using Multiset.induction_on with
  | empty => exact absurd rfl h
  | cons y M ih =>
    by_cases hM : M = 0
    · exact ⟨y, 0, by simp [hM], by simp⟩
    obtain ⟨a, R, rfl, hR⟩ := ih hM
    by_cases hya : y ≤ a
    · refine ⟨y, a ::ₘ R, rfl, fun x hx => ?_⟩
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact hya
      · exact hya.trans (hR x hx)
    · refine ⟨a, y ::ₘ R, Multiset.cons_swap _ _ _, fun x hx => ?_⟩
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · linarith
      · exact hR x hx

lemma exists_two_min (M : Multiset ℝ) (h : 2 ≤ Multiset.card M) :
    ∃ a b R, M = a ::ₘ b ::ₘ R ∧ a ≤ b ∧ ∀ x ∈ R, a ≤ x ∧ b ≤ x := by
  obtain ⟨a, R1, rfl, h1⟩ := exists_min M (by rintro rfl; simp at h)
  obtain ⟨b, R, rfl, h2⟩ := exists_min R1 (by rintro rfl; simp at h)
  refine ⟨a, b, R, rfl, h1 b (by simp), fun x hx => ⟨h1 x (by simp [hx]), h2 x hx⟩⟩

/-- The invariant of Lemma 25: positive numbers, at most `s`, sum `S`, at least two of them. -/
def Inv (s S : ℝ) (M : Multiset ℝ) : Prop :=
  (∀ x ∈ M, 0 < x ∧ x ≤ s) ∧ M.sum = S ∧ 2 ≤ Multiset.card M

lemma Inv.step {s S : ℝ} {M M' : Multiset ℝ} (hI : Inv s S M) (h : Step s M M') : Inv s S M' := by
  obtain ⟨hpos, hsum, -⟩ := hI
  obtain ⟨a, b, R, rfl, hR, -, hab, rfl⟩ := h
  have ha := hpos a (by simp)
  have hb := hpos b (by simp [Multiset.mem_cons])
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ⟨by linarith, hab⟩
    · exact hpos x (by simp [hx])
  · rw [← hsum]; simp [add_assoc]
  · have : 1 ≤ Multiset.card R := Multiset.card_pos.mpr hR
    simp; omega

/-- With at least four numbers (positive, sum `< 2s`) a step applies. -/
lemma step_of_four {s S : ℝ} {M : Multiset ℝ} (hI : Inv s S M) (hS : S < 2 * s)
    (h4 : 4 ≤ Multiset.card M) : ∃ M', Step s M M' := by
  obtain ⟨hpos, hsum, -⟩ := hI
  obtain ⟨a, b, R, rfl, hab, hR⟩ := exists_two_min M (by omega)
  have hR2 : 2 ≤ Multiset.card R := by simp at h4; omega
  obtain ⟨c, d, R', rfl, -, -⟩ := exists_two_min R hR2
  have hc := hR c (by simp)
  have hd := hR d (by simp)
  have hR'0 : 0 ≤ R'.sum := Multiset.sum_nonneg fun x hx => (hpos x (by simp [hx])).1.le
  have hsum' : a + b + c + d + R'.sum = S := by rw [← hsum]; simp; ring
  refine ⟨(a + b) ::ₘ c ::ₘ d ::ₘ R', a, b, c ::ₘ d ::ₘ R', rfl, by simp, hR, ?_, rfl⟩
  linarith [hc.2, hd.2]

/-- With exactly three numbers, if the procedure has stopped, any two add up to more than `s`. -/
lemma three_of_stopped {s : ℝ} {M : Multiset ℝ} (hM : Stopped s M) (h3 : Multiset.card M = 3) :
    ∀ x y R, M = x ::ₘ y ::ₘ R → s < x + y := by
  intro x y R hxy
  subst hxy
  obtain ⟨z, rfl⟩ : ∃ z, R = {z} := by
    simp at h3; exact Multiset.card_eq_one.mp h3
  by_contra hle
  push Not at hle
  apply hM
  rcases le_or_gt x z with hxz | hxz
  · rcases le_or_gt y z with hyz | hyz
    · exact ⟨_, x, y, {z}, rfl, by simp, by simp [hxz, hyz], hle, rfl⟩
    · refine ⟨_, x, z, {y}, ?_, by simp, by simp; constructor <;> linarith, by linarith, rfl⟩
      simp only [← Multiset.singleton_add]; abel
  · rcases le_or_gt y x with hyx | hyx
    · refine ⟨_, z, y, {x}, ?_, by simp, by simp; constructor <;> linarith, by linarith, rfl⟩
      simp only [← Multiset.singleton_add]; abel
    · refine ⟨_, z, x, {y}, ?_, by simp, by simp; constructor <;> linarith, by linarith, rfl⟩
      simp only [← Multiset.singleton_add]; abel

/-- The procedure terminates: every step lowers the number of elements. -/
theorem step_wf (s : ℝ) : WellFounded (fun M' M => Step s M M') :=
  Subrelation.wf (fun {M' M} h => by
    show Multiset.card M' < Multiset.card M
    have := h.card; omega) (measure Multiset.card).wf

lemma exists_stopped {s S : ℝ} (M : Multiset ℝ) (hI : Inv s S M) :
    ∃ M', Relation.ReflTransGen (Step s) M M' ∧ Stopped s M' := by
  induction M using (step_wf s).induction with
  | _ M ih =>
    by_cases hM : Stopped s M
    · exact ⟨M, Relation.ReflTransGen.refl, hM⟩
    · unfold Stopped at hM; push Not at hM
      obtain ⟨M1, h1⟩ := hM
      obtain ⟨M2, h2, h2'⟩ := ih M1 h1 (hI.step h1)
      exact ⟨M2, Relation.ReflTransGen.head h1 h2, h2'⟩

lemma inv_of_reach {s S : ℝ} {M M' : Multiset ℝ} (hI : Inv s S M)
    (h : Relation.ReflTransGen (Step s) M M') : Inv s S M' := by
  induction h with
  | refl => exact hI
  | tail _ h ih => exact ih.step h

/-- **Lemma 25** (`j:lem:group`). Let `m ≥ 2`, `s > 0` and `0 < ℓ₁, …, ℓ_m ≤ s` (the multiset
`M₀`) with `∑ ℓ_j < 2s`. Replace two smallest numbers by their sum as long as at least three
numbers remain and the two smallest have sum at most `s` (relation `Step s`). The procedure
terminates (every run is finite, and a stopped state is reached); every state reached consists of
positive numbers at most `s` with the same sum, and a stopped state consists of two numbers, or of
three numbers any two of which have sum greater than `s`. -/
theorem lem25 {s : ℝ} (M₀ : Multiset ℝ) (hm : 2 ≤ Multiset.card M₀)
    (hpos : ∀ x ∈ M₀, 0 < x ∧ x ≤ s) (hsum : M₀.sum < 2 * s) :
    WellFounded (fun M' M => Step s M M') ∧
    (∃ M, Relation.ReflTransGen (Step s) M₀ M ∧ Stopped s M) ∧
    ∀ M, Relation.ReflTransGen (Step s) M₀ M →
      (∀ x ∈ M, 0 < x ∧ x ≤ s) ∧ M.sum = M₀.sum ∧
      (Stopped s M → Multiset.card M = 2 ∨
        (Multiset.card M = 3 ∧ ∀ x y R, M = x ::ₘ y ::ₘ R → s < x + y)) := by
  have hI : Inv s M₀.sum M₀ := ⟨hpos, rfl, hm⟩
  refine ⟨step_wf s, exists_stopped M₀ hI, fun M hM => ?_⟩
  obtain ⟨h1, h2, h3⟩ := inv_of_reach hI hM
  refine ⟨h1, h2, fun hst => ?_⟩
  have h4 : Multiset.card M < 4 := by
    by_contra h; push Not at h
    exact hst (step_of_four ⟨h1, h2, h3⟩ hsum h)
  rcases (show Multiset.card M = 2 ∨ Multiset.card M = 3 by omega) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, three_of_stopped hst h⟩

/-- The remark after Lemma 25: with three groups, `C₁ + C₂ + C₃ = 2s - 2μ` and `Cᵢ + Cⱼ > s`
give `C_k < s - 2μ`. -/
lemma three_groups_bound {C1 C2 C3 s μ : ℝ} (hsum : C1 + C2 + C3 = 2 * s - 2 * μ)
    (h12 : s < C1 + C2) (h13 : s < C1 + C3) (h23 : s < C2 + C3) :
    C1 < s - 2 * μ ∧ C2 < s - 2 * μ ∧ C3 < s - 2 * μ :=
  ⟨by linarith, by linarith, by linarith⟩


/-! ### Segment representations -/

/-- `F` is the family of marginals of a finite mixture of uniform distributions on segments with
endpoints in `H_s`, with nonnegative weights adding up to `1`. -/
def SegRep {n : ℕ} (s : ℝ) (F : Fin n → Measure ℝ) : Prop :=
  ∃ (k : ℕ) (w : Fin k → ℝ) (P Q : Fin k → Fin n → ℝ), (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1 ∧
    (∀ e, ∑ j, P e j = s) ∧ (∀ e, ∑ j, Q e j = s) ∧
    ∀ j, ∑ e, ENNReal.ofReal (w e) • unifI (min (P e j) (Q e j)) (max (P e j) (Q e j)) = F j

/-- A segment representation is a joint mix with sum `s` (Lemma 16). -/
lemma SegRep.joint {n : ℕ} {s : ℝ} {F : Fin n → Measure ℝ} (h : SegRep s F) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (P Q : Fin k → Fin n → ℝ), (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1 ∧
      (∀ e, ∑ j, P e j = s) ∧ (∀ e, ∑ j, Q e j = s) ∧ IsJointMix F (segMix w P Q) ∧
      ∀ᵐ x ∂segMix w P Q, ∑ j, x j = s := by
  obtain ⟨k, w, P, Q, hw, hw1, hP, hQ, hF⟩ := h
  obtain ⟨hprob, hsum, -, hmap⟩ := seg_mix w P Q s hw hw1 hP hQ
  exact ⟨k, w, P, Q, hw, hw1, hP, hQ, ⟨hprob, ⟨s, hsum⟩, fun j => (hmap j).trans (hF j)⟩, hsum⟩

lemma segRep_of_mix {n : ℕ} {s : ℝ} {F : Fin n → Measure ℝ} {k : ℕ} {w : Fin k → ℝ}
    {P Q : Fin k → Fin n → ℝ} (hw : ∀ e, 0 ≤ w e) (hw1 : ∑ e, w e = 1)
    (hP : ∀ e, ∑ j, P e j = s) (hQ : ∀ e, ∑ j, Q e j = s) (hmix : IsJointMix F (segMix w P Q)) :
    SegRep s F :=
  ⟨k, w, P, Q, hw, hw1, hP, hQ, fun j => by rw [← segMix_map]; exact hmix.2.2 j⟩

lemma map_affine_seg (c d p q : ℝ) :
    (unifI (min p q) (max p q)).map (fun x => c * x + d) =
      unifI (min (c * p + d) (c * q + d)) (max (c * p + d) (c * q + d)) := by
  rw [← map_seg_unifI, ← map_seg_unifI, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1; funext v; simp only [Function.comp]; ring

/-- Affine images: coordinate `j` of the new vector is `c j * x (σ j) + d j`; segments go to
segments with the same weights. -/
lemma SegRep.affine {n m : ℕ} {s s' : ℝ} {F : Fin n → Measure ℝ} (h : SegRep s F)
    (σ : Fin m → Fin n) (c d : Fin m → ℝ)
    (hs : ∀ x : Fin n → ℝ, ∑ i, x i = s → ∑ j, (c j * x (σ j) + d j) = s') :
    SegRep s' (fun j => (F (σ j)).map (fun x => c j * x + d j)) := by
  obtain ⟨k, w, P, Q, hw, hw1, hP, hQ, hF⟩ := h
  refine ⟨k, w, fun e j => c j * P e (σ j) + d j, fun e j => c j * Q e (σ j) + d j, hw, hw1,
    fun e => hs _ (hP e), fun e => hs _ (hQ e), fun j => ?_⟩
  show _ = (F (σ j)).map (fun x => c j * x + d j)
  rw [← hF (σ j), Measure.map_finset_sum' (by fun_prop)]
  congr 1; funext e
  rw [Measure.map_smul, map_affine_seg]
  fun_prop

/-- Mixing two segment representations with the weights `t` and `1 - t`. -/
lemma SegRep.mix {n : ℕ} {s : ℝ} {F G : Fin n → Measure ℝ} (hF : SegRep s F) (hG : SegRep s G)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SegRep s (fun j => ENNReal.ofReal t • F j + ENNReal.ofReal (1 - t) • G j) := by
  obtain ⟨k1, w1, P1, Q1, hw1, hs1, hP1, hQ1, hF1⟩ := hF
  obtain ⟨k2, w2, P2, Q2, hw2, hs2, hP2, hQ2, hG2⟩ := hG
  refine ⟨k1 + k2, Fin.append (fun e => t * w1 e) (fun e => (1 - t) * w2 e), Fin.append P1 P2,
    Fin.append Q1 Q2, ?_, ?_, ?_, ?_, fun j => ?_⟩
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [Fin.append_left]; exact mul_nonneg ht0 (hw1 e)
    · simp only [Fin.append_right]; exact mul_nonneg (by linarith) (hw2 e)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← Finset.mul_sum, hs1, hs2]
    ring
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [Fin.append_left]; exact hP1 e
    · simp only [Fin.append_right]; exact hP2 e
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [Fin.append_left]; exact hQ1 e
    · simp only [Fin.append_right]; exact hQ2 e
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hF1 j, ← hG2 j, smul_mix_unifI ht0, smul_mix_unifI (by linarith)]

/-- Three coordinates, all uniform: Lemma 18. -/
lemma three_rep_unif {S c1 c2 c3 : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3)
    (h1S : c1 ≤ S) (h2S : c2 ≤ S) (h3S : c3 ≤ S) (hsum : c1 + c2 + c3 = 2 * S) :
    SegRep S ![unifI 0 c1, unifI 0 c2, unifI 0 c3] := by
  have hl : ∑ j, ![c1, c2, c3] j = c1 + c2 + c3 := by simp [Fin.sum_univ_three]
  have hS : (∑ j, ![c1, c2, c3] j) / 2 = S := by rw [hl]; linarith
  obtain ⟨m, w, P, Q, -, hw, hw1, hP, hQ, hmix, -⟩ := lem18 ![c1, c2, c3]
    (fun j => by fin_cases j <;> simp <;> linarith) (by rw [hS]; linarith)
    (fun j => by rw [hS]; fin_cases j <;> simp <;> linarith)
  rw [hS] at hP hQ
  have hF : (fun j => unifI 0 (![c1, c2, c3] j)) = ![unifI 0 c1, unifI 0 c2, unifI 0 c3] := by
    funext j; fin_cases j <;> rfl
  rw [hF] at hmix
  exact segRep_of_mix hw hw1 hP hQ hmix

/-- Two uniform coordinates and one with two steps: Proposition 24. -/
lemma three_rep_g {S c1 c2 μ a b : ℝ} (h1S : c1 ≤ S) (h2S : c2 ≤ S) (ha : 0 ≤ a)
    (ha2 : a < 2 * μ) (hb : 2 * μ < b) (hbS : b ≤ S) (hS : (c1 + c2) / 2 + μ = S) :
    SegRep S ![unifI 0 c1, unifI 0 c2, gPiece μ a b] := by
  obtain ⟨k, w, P, Q, hw, hw1, hP, hQ, hmix, -⟩ := prop24 (c1 := c1) (c2 := c2) ha ha2 hb
    (by linarith) (by linarith) (by linarith)
  rw [hS] at hP hQ
  exact segRep_of_mix hw hw1 hP hQ hmix

/-! ### Proposition 26: the remainders `L_i` and their reflections -/

/-- Evaluates step densities and `min`/`max` once the order is known. -/
local macro "js_step" : tactic => `(tactic|
  simp (disch := with_unfolding_all linarith) only [dstep_left, dstep_right, dstep_mid,
    min_eq_left, min_eq_right, max_eq_left, max_eq_right])

lemma dstep_split (d : ℝ) {l m r : ℝ} (hlm : l ≤ m) (hmr : m ≤ r) (x : ℝ) :
    dstep d l r x = dstep d l m x + dstep d m r x := by
  rcases le_or_gt x l with h0 | h0
  · js_step; ring
  rcases le_or_gt x m with h1 | h1
  · js_step; ring
  rcases le_or_gt x r with h2 | h2
  · js_step; ring
  · js_step; ring

/-- Splitting `U[0,C]` at `κ`. -/
lemma split_unif {C κ : ℝ} (hκ : 0 < κ) (hκC : κ ≤ C) :
    unifI 0 C = ENNReal.ofReal (κ / C) • unifI 0 κ +
      ENNReal.ofReal ((C - κ) / C) • unifI κ C := by
  have hC : 0 < C := by linarith
  have e : ENNReal.ofReal (κ / C) • unifI 0 κ + ENNReal.ofReal ((C - κ) / C) • unifI κ C =
      ∑ e : Fin 2, ENNReal.ofReal (![κ / C, (C - κ) / C] e) • unifI (![0, κ] e) (![κ, C] e) := by
    simp [Fin.sum_univ_two]
  have t := target_unif (Λ := 1) zero_le_one hC
  rw [ENNReal.ofReal_one, one_smul] at t
  rw [e, mix_unifI_eq _ ![1 / C, 1 / C], t]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact dstep_split _ hκ.le hκC x
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp; ring
  · intro e; fin_cases e <;> simp <;> apply div_nonneg <;> linarith
  · intro e; fin_cases e <;> simp <;> positivity
  · intro e; fin_cases e <;> simp <;> linarith
  · intro e; left; fin_cases e <;> simp <;> field_simp

lemma map_reflect_unifI {l r : ℝ} (hlr : l ≤ r) (C : ℝ) :
    (unifI l r).map (fun x => C - x) = unifI (C - r) (C - l) := by
  have h := map_affine_seg (-1) C l r
  rw [min_eq_left hlr, max_eq_right hlr, min_eq_right (by linarith),
    max_eq_left (by linarith)] at h
  convert h using 2
  · funext x; ring
  · ring
  · ring

/-- `L = (U[0,C] - q U[0,κ]) / p`, written as the mixture
`((κ - qC)/(pC)) U[0,κ] + ((C - κ)/(pC)) U[κ,C]` (see `L_split`). -/
def Lm (p q C κ : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((κ - q * C) / (p * C)) • unifI 0 κ +
    ENNReal.ofReal ((C - κ) / (p * C)) • unifI κ C

/-- `L̄`: the distribution of `C - Y` for `Y ∼ L`. -/
def barL (p q C κ : ℝ) : Measure ℝ := (Lm p q C κ).map (fun x => C - x)

/-- The mean `μ̄ = C - (C - qκ)/(2p)` of `L̄`. -/
def barMu (p q C κ : ℝ) : ℝ := C - (C - q * κ) / (2 * p)

/-- Hypotheses on one coordinate: `p, q > 0`, `p + q = 1`, `C > 0`, `κ ∈ [qC, C]`. -/
structure KHyp (p q C κ : ℝ) : Prop where
  hp : 0 < p
  hq : 0 < q
  hpq : p + q = 1
  hC : 0 < C
  hl : q * C ≤ κ
  hu : κ ≤ C

section KLemmas

variable {p q C κ : ℝ}

lemma KHyp.κpos (h : KHyp p q C κ) : 0 < κ := lt_of_lt_of_le (mul_pos h.hq h.hC) h.hl

lemma Lm_isProb (h : KHyp p q C κ) : IsProbabilityMeasure (Lm p q C κ) := by
  have := unifI_isProb 0 κ
  have := unifI_isProb κ C
  have hpC : 0 < p * C := mul_pos h.hp h.hC
  constructor
  simp only [Lm, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (div_nonneg (by linarith [h.hl]) hpC.le)
    (div_nonneg (by linarith [h.hu]) hpC.le)]
  rw [← ENNReal.ofReal_one]; congr 1
  have hpC' : p * C = C - q * C := by rw [show p = 1 - q by linarith [h.hpq]]; ring
  rw [← add_div, div_eq_one_iff_eq hpC.ne']; linarith

/-- `q U[0,κ] + p L = U[0,C]`, that is `L = (U[0,C] - q U[0,κ])/p`. -/
lemma L_split (h : KHyp p q C κ) :
    ENNReal.ofReal q • unifI 0 κ + ENNReal.ofReal p • Lm p q C κ = unifI 0 C := by
  have hpC : 0 < p * C := mul_pos h.hp h.hC
  have hC := h.hC
  have hp := h.hp
  rw [split_unif h.κpos h.hu, Lm, smul_add, smul_smul, smul_smul, ← ENNReal.ofReal_mul h.hp.le,
    ← ENNReal.ofReal_mul h.hp.le, ← add_assoc, ← add_smul,
    ← ENNReal.ofReal_add h.hq.le (mul_nonneg h.hp.le (div_nonneg (by linarith [h.hl]) hpC.le))]
  congr 3
  · field_simp; ring
  · field_simp

lemma L_sub (h : KHyp p q C κ) :
    Lm p q C κ = ENNReal.ofReal p⁻¹ • (unifI 0 C - ENNReal.ofReal q • unifI 0 κ) := by
  have := unifI_isProb 0 κ
  have : IsFiniteMeasure (ENNReal.ofReal q • unifI 0 κ) :=
    ⟨by simp [measure_univ]⟩
  rw [← L_split h, add_comm, Measure.add_sub_cancel, smul_smul, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr h.hp.le), inv_mul_cancel₀ h.hp.ne', ENNReal.ofReal_one, one_smul]

lemma barL_eq (h : KHyp p q C κ) :
    barL p q C κ = ENNReal.ofReal ((κ - q * C) / (p * C)) • unifI (C - κ) C +
      ENNReal.ofReal ((C - κ) / (p * C)) • unifI 0 (C - κ) := by
  unfold barL Lm
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    map_reflect_unifI h.κpos.le, map_reflect_unifI h.hu, sub_zero, sub_self]
  all_goals fun_prop

lemma barL_low (h : KHyp p q C κ) (hκ : κ = q * C) : barL p q C κ = unifI 0 (p * C) := by
  have hpC : 0 < p * C := mul_pos h.hp h.hC
  have hpC' : p * C = C - q * C := by rw [show p = 1 - q by linarith [h.hpq]]; ring
  rw [barL_eq h, hκ, sub_self, zero_div, ENNReal.ofReal_zero, zero_smul, zero_add,
    show C - q * C = p * C by linarith, div_self hpC.ne', ENNReal.ofReal_one, one_smul]

lemma barL_high (h : KHyp p q C κ) (hκ : κ = C) : barL p q C κ = unifI 0 C := by
  have hpC : 0 < p * C := mul_pos h.hp h.hC
  have hpC' : p * C = C - q * C := by rw [show p = 1 - q by linarith [h.hpq]]; ring
  rw [barL_eq h, hκ, sub_self, zero_div, ENNReal.ofReal_zero, zero_smul, add_zero,
    show C - q * C = p * C by linarith, div_self hpC.ne', ENNReal.ofReal_one, one_smul]

lemma barMu_low (h : KHyp p q C κ) (hκ : κ = q * C) : 2 * barMu p q C κ = p * C := by
  have hp := h.hp
  unfold barMu; rw [hκ, show q = 1 - p by linarith [h.hpq]]; field_simp; ring

lemma barMu_high (h : KHyp p q C κ) (hκ : κ = C) : 2 * barMu p q C κ = C := by
  have hp := h.hp
  unfold barMu; rw [hκ, show q = 1 - p by linarith [h.hpq]]; field_simp; ring

lemma barMu_mid (h : KHyp p q C κ) (h1 : q * C < κ) (h2 : κ < C) :
    C - κ < 2 * barMu p q C κ ∧ 2 * barMu p q C κ < C := by
  have hp := h.hp
  have hq := h.hq
  have e : 2 * barMu p q C κ = 2 * C - (C - q * κ) / p := by unfold barMu; field_simp
  have hp1 : p = 1 - q := by linarith [h.hpq]
  have h1' : (C - q * κ) / p < C + κ := by
    rw [div_lt_iff₀ hp, hp1]; nlinarith
  have h2' : C < (C - q * κ) / p := by
    rw [lt_div_iff₀ hp, hp1]; nlinarith
  rw [e]
  constructor <;> linarith

/-- Part (i) of Proposition 26 in the remaining case: `L̄ = g^{μ̄}_{C-κ,C}`. -/
lemma barL_mid (h : KHyp p q C κ) (h1 : q * C < κ) (h2 : κ < C) :
    barL p q C κ = gPiece (barMu p q C κ) (C - κ) C := by
  obtain ⟨hm1, hm2⟩ := barMu_mid h h1 h2
  have hp := h.hp
  have hq := h.hq
  have hC := h.hC
  have hκ := h.κpos
  have hpC : 0 < p * C := mul_pos hp hC
  have hCκ : 0 < C - κ := by linarith
  have hpq : q = 1 - p := by linarith [h.hpq]
  have t := target_g (Λ := 1) zero_le_one hCκ.le hm1 hm2
  rw [ENNReal.ofReal_one, one_smul, show C - (C - κ) = κ by ring] at t
  have e : barL p q C κ = ∑ e : Fin 2, ENNReal.ofReal (![(κ - q * C) / (p * C),
      (C - κ) / (p * C)] e) • unifI (![C - κ, 0] e) (![C, C - κ] e) := by
    rw [barL_eq h]; simp [Fin.sum_univ_two]
  rw [t, e, mix_unifI_eq _ ![(κ - q * C) / (p * C) / κ, (C - κ) / (p * C) / (C - κ)]]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      unfold barMu
      rcases le_or_gt x 0 with h0 | h0
      · js_step
      rcases le_or_gt x (C - κ) with h3 | h3
      · js_step; rw [hpq]; field_simp; ring
      rcases le_or_gt x C with h4 | h4
      · js_step; rw [hpq]; field_simp; ring
      · js_step
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        hCκ.ne', ite_false]
      field_simp; ring
  · intro e; fin_cases e
    · exact div_nonneg (by linarith) hpC.le
    · exact div_nonneg (by linarith) hpC.le
  · intro e; fin_cases e
    · exact div_nonneg (div_nonneg (by linarith) hpC.le) hκ.le
    · exact div_nonneg (div_nonneg (by linarith) hpC.le) hCκ.le
  · intro e; fin_cases e <;> simp <;> linarith
  · intro e; left; fin_cases e <;> simp <;> field_simp

end KLemmas

lemma map_one_zero (μ : Measure ℝ) : μ.map (fun x => 1 * x + 0) = μ := by
  have : (fun x : ℝ => 1 * x + 0) = id := by funext x; simp
  rw [this, Measure.map_id]

lemma map_scale_unif {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) :
    (unifI 0 L).map (fun x => c * x + 0) = unifI 0 (c * L) := by
  have h := map_affine_seg c 0 0 L
  rw [min_eq_left hL, max_eq_right hL, mul_zero, zero_add, add_zero,
    min_eq_left (mul_nonneg hc hL), max_eq_right (mul_nonneg hc hL)] at h
  exact h

/-- Reordering the coordinates. -/
lemma SegRep.reindex {n : ℕ} {s : ℝ} {F : Fin n → Measure ℝ} (h : SegRep s F)
    (σ : Fin n → Fin n) (hσ : ∀ x : Fin n → ℝ, ∑ j, x (σ j) = ∑ j, x j) :
    SegRep s (fun j => F (σ j)) := by
  have := h.affine (s' := s) σ (fun _ => 1) (fun _ => 0) (fun x hx => by simp [hσ x, hx])
  simpa only [map_one_zero] using this

/-- Four uniform coordinates: Lemma 18. -/
lemma four_rep_unif {S c0 c1 c2 c3 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3)
    (hS0 : 0 < S) (h0S : c0 ≤ S) (h1S : c1 ≤ S) (h2S : c2 ≤ S) (h3S : c3 ≤ S)
    (hsum : c0 + c1 + c2 + c3 = 2 * S) :
    SegRep S ![unifI 0 c0, unifI 0 c1, unifI 0 c2, unifI 0 c3] := by
  have hl : ∑ j, ![c0, c1, c2, c3] j = c0 + c1 + c2 + c3 := by simp [Fin.sum_univ_four]
  have hS : (∑ j, ![c0, c1, c2, c3] j) / 2 = S := by rw [hl]; linarith
  obtain ⟨m, w, P, Q, -, hw, hw1, hP, hQ, hmix, -⟩ := lem18 ![c0, c1, c2, c3]
    (fun j => by fin_cases j <;> simp <;> linarith) (by rw [hS]; linarith)
    (fun j => by rw [hS]; fin_cases j <;> simp <;> linarith)
  rw [hS] at hP hQ
  have hF : (fun j => unifI 0 (![c0, c1, c2, c3] j)) =
      ![unifI 0 c0, unifI 0 c1, unifI 0 c2, unifI 0 c3] := by
    funext j; fin_cases j <;> rfl
  rw [hF] at hmix
  exact segRep_of_mix hw hw1 hP hQ hmix

/-- The shape of a distribution in part (ii): uniform `U[0,r]` with `r = 2m`, or `g^m_{a',b'}`;
supports in `[0, S]`. -/
def Shape (S m : ℝ) (G : Measure ℝ) : Prop :=
  (∃ r, 0 < r ∧ r ≤ S ∧ G = unifI 0 r ∧ r = 2 * m) ∨
    (∃ a' b', 0 ≤ a' ∧ a' < 2 * m ∧ 2 * m < b' ∧ b' ≤ S ∧ G = gPiece m a' b')

/-- The construction of part (ii) with the coordinates in the order `i₀, i₁, i₂, 4`:
`U[0,r₀]` and `U[0,r₁]` uniform, `Y_{i₀} = r₀W/(r₀ + a)`, `Y₄ = aW/(r₀ + a)` with
`W ∼ U[0, r₀ + a]`, and Proposition 24 or Lemma 18 for `W` and the other two coordinates.
(For `a = 0` this is `Y₄ = 0`.) -/
lemma ii_core {S a r0 r1 m2 : ℝ} {G2 : Measure ℝ} (ha : 0 ≤ a) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (h0S : r0 + a ≤ S) (h1S : r1 ≤ S) (hG : Shape S m2 G2)
    (hmean : r0 / 2 + r1 / 2 + m2 + a / 2 = S) :
    SegRep S ![unifI 0 r0, unifI 0 r1, G2, unifI 0 a] := by
  have hra : 0 < r0 + a := by linarith
  have h3 : SegRep S ![unifI 0 (r0 + a), unifI 0 r1, G2] := by
    rcases hG with ⟨r2, hr2, hr2S, rfl, hm⟩ | ⟨a', b', ha', ha2', hb', hbS', rfl⟩
    · exact three_rep_unif hra hr1 hr2 h0S h1S hr2S (by linarith)
    · exact three_rep_g h0S h1S ha' ha2' hb' hbS' (by linarith)
  have h4 := h3.affine (s' := S) ![0, 1, 2, 0] ![r0 / (r0 + a), 1, 1, a / (r0 + a)] ![0, 0, 0, 0]
    (fun x hx => by
      rw [← hx]; simp [Fin.sum_univ_four, Fin.sum_univ_three]; field_simp; ring)
  convert h4 using 1
  funext j; fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [map_scale_unif (div_nonneg hr0.le hra.le) hra.le, div_mul_cancel₀ _ hra.ne']
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [map_one_zero]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [map_scale_unif (div_nonneg ha hra.le) hra.le, div_mul_cancel₀ _ hra.ne']

/-! ### Proposition 26: the hypotheses and the choice of `κ` -/

/-- `p = (b - 2μ)/(b - a)`, the weight of `U[0,a]` in `g^μ_{a,b}`. -/
def pw (μ a b : ℝ) : ℝ := (b - 2 * μ) / (b - a)

/-- `q = (2μ - a)/(b - a)`, the weight of `U[0,b]` in `g^μ_{a,b}`. -/
def qw (μ a b : ℝ) : ℝ := (2 * μ - a) / (b - a)

/-- The hypotheses of Proposition 26: `C₁, C₂, C₃ > 0`, `0 ≤ a < 2μ < b`,
`s = (C₁ + C₂ + C₃)/2 + μ`, `b ≤ s` and `Cᵢ ≤ s - 2μ`. -/
structure Hyp (C : Fin 3 → ℝ) (μ a b s : ℝ) : Prop where
  hC : ∀ i, 0 < C i
  ha : 0 ≤ a
  ha2 : a < 2 * μ
  hb : 2 * μ < b
  hs : s = (C 0 + C 1 + C 2) / 2 + μ
  hbs : b ≤ s
  hCs : ∀ i, C i ≤ s - 2 * μ

/-- `κ` lies strictly between `qC` and `C`. -/
def Inside (q C κ : ℝ) : Prop := q * C < κ ∧ κ < C

/-- An admissible choice of `κ`: `κᵢ ∈ [qCᵢ, Cᵢ]`, `κ₁ + κ₂ + κ₃ = 2s - b`, and at most one
`κᵢ` strictly between `qCᵢ` and `Cᵢ`. -/
structure Adm (C : Fin 3 → ℝ) (μ a b s : ℝ) (κ : Fin 3 → ℝ) : Prop where
  hl : ∀ i, qw μ a b * C i ≤ κ i
  hu : ∀ i, κ i ≤ C i
  hsum : κ 0 + κ 1 + κ 2 = 2 * s - b
  hone : ∀ i j, i ≠ j → Inside (qw μ a b) (C i) (κ i) → ¬Inside (qw μ a b) (C j) (κ j)

section HypLemmas

variable {C : Fin 3 → ℝ} {μ a b s : ℝ}

lemma Hyp.hp (h : Hyp C μ a b s) : 0 < pw μ a b :=
  div_pos (by linarith [h.hb]) (by linarith [h.hb, h.ha2])

lemma Hyp.hq (h : Hyp C μ a b s) : 0 < qw μ a b :=
  div_pos (by linarith [h.ha2]) (by linarith [h.hb, h.ha2])

lemma Hyp.hpq (h : Hyp C μ a b s) : pw μ a b + qw μ a b = 1 := by
  have : b - a ≠ 0 := by linarith [h.hb, h.ha2]
  unfold pw qw; field_simp; ring

lemma Hyp.hpa (h : Hyp C μ a b s) : pw μ a b * a + qw μ a b * b = 2 * μ := by
  have : b - a ≠ 0 := by linarith [h.hb, h.ha2]
  unfold pw qw; field_simp; ring

lemma Hyp.sum_C (h : Hyp C μ a b s) : C 0 + C 1 + C 2 = 2 * s - 2 * μ := by
  linarith [h.hs]

lemma Hyp.s2μ (h : Hyp C μ a b s) : 0 < s - 2 * μ := lt_of_lt_of_le (h.hC 0) (h.hCs 0)

lemma Hyp.khyp {κ : Fin 3 → ℝ} (h : Hyp C μ a b s) (hA : Adm C μ a b s κ) (i : Fin 3) :
    KHyp (pw μ a b) (qw μ a b) (C i) (κ i) :=
  ⟨h.hp, h.hq, h.hpq, h.hC i, hA.hl i, hA.hu i⟩

/-- `q ∑ Cᵢ ≤ 2s - b` (the existence of admissible `κ`). -/
lemma Hyp.d1_nonneg (h : Hyp C μ a b s) : qw μ a b * (C 0 + C 1 + C 2) ≤ 2 * s - b := by
  have hba : 0 < b - a := by linarith [h.hb, h.ha2]
  have hs2 := h.s2μ
  rw [h.sum_C, qw, div_mul_eq_mul_div, div_le_iff₀ hba]
  have h1 : 0 ≤ (b - 2 * μ) * (2 * s - 2 * μ - b) :=
    mul_nonneg (by linarith [h.hb]) (by linarith [h.hbs])
  have h2 : 0 ≤ a * (b - 2 * μ) := mul_nonneg h.ha (by linarith [h.hb])
  nlinarith

end HypLemmas

/-- The choice of `κ` described in Proposition 26: with `d₁ = 2s - b - q ∑ Cᵢ`,
`κᵢ = qCᵢ + min(dᵢ, pCᵢ)` and `d_{i+1} = dᵢ - min(dᵢ, pCᵢ)`. -/
def kGreedy (C : Fin 3 → ℝ) (μ a b s : ℝ) : Fin 3 → ℝ :=
  let p := pw μ a b
  let q := qw μ a b
  let d1 := 2 * s - b - q * (C 0 + C 1 + C 2)
  let m1 := min d1 (p * C 0)
  let m2 := min (d1 - m1) (p * C 1)
  let m3 := min (d1 - m1 - m2) (p * C 2)
  ![q * C 0 + m1, q * C 1 + m2, q * C 2 + m3]

/-- **Proposition 26**, the choice of `κ`: the greedy choice is admissible. -/
theorem prop26_kappa {C : Fin 3 → ℝ} {μ a b s : ℝ} (h : Hyp C μ a b s) :
    Adm C μ a b s (kGreedy C μ a b s) := by
  have hd1 := h.d1_nonneg
  have hpq := h.hpq
  have hp := h.hp
  have hq := h.hq
  set p := pw μ a b
  set q := qw μ a b
  have hc : ∀ i, p * C i + q * C i = C i := fun i => by rw [← add_mul, hpq, one_mul]
  have hpC : ∀ i, 0 < p * C i := fun i => mul_pos hp (h.hC i)
  have hqC : ∀ i, 0 < q * C i := fun i => mul_pos hq (h.hC i)
  have hSC := h.sum_C
  have hb := h.hb
  have hup : 2 * s - b - q * (C 0 + C 1 + C 2) ≤ p * C 0 + p * C 1 + p * C 2 := by
    linarith [hc 0, hc 1, hc 2]
  set d1 := 2 * s - b - q * (C 0 + C 1 + C 2) with hd1def
  have hc0 := hc 0; have hc1 := hc 1; have hc2 := hc 2
  have hp0 := hpC 0; have hp1 := hpC 1; have hp2 := hpC 2
  have hq0 := hqC 0; have hq1 := hqC 1; have hq2 := hqC 2
  have k0 : kGreedy C μ a b s 0 = q * C 0 + min d1 (p * C 0) := rfl
  have k1 : kGreedy C μ a b s 1 = q * C 1 + min (d1 - min d1 (p * C 0)) (p * C 1) := rfl
  have k2 : kGreedy C μ a b s 2 = q * C 2 + min (d1 - min d1 (p * C 0) -
      min (d1 - min d1 (p * C 0)) (p * C 1)) (p * C 2) := rfl
  set m1 := min d1 (p * C 0) with hm1
  set m2 := min (d1 - m1) (p * C 1) with hm2
  set m3 := min (d1 - m1 - m2) (p * C 2) with hm3
  have e1 := min_cases d1 (p * C 0)
  have e2 := min_cases (d1 - m1) (p * C 1)
  have e3 := min_cases (d1 - m1 - m2) (p * C 2)
  rw [← hm1] at e1; rw [← hm2] at e2; rw [← hm3] at e3
  refine ⟨fun i => ?_, fun i => ?_, ?_, fun i j hij hi hj => ?_⟩
  · fin_cases i
    · show q * C 0 ≤ kGreedy C μ a b s 0
      rw [k0]; rcases e1 with ⟨e1, -⟩ | ⟨e1, -⟩ <;> linarith
    · show q * C 1 ≤ kGreedy C μ a b s 1
      rw [k1]; rcases e1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases e2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        linarith
    · show q * C 2 ≤ kGreedy C μ a b s 2
      rw [k2]; rcases e1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases e2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rcases e3 with ⟨e3, _⟩ | ⟨e3, _⟩ <;> linarith
  · fin_cases i
    · show kGreedy C μ a b s 0 ≤ C 0
      rw [k0]; rcases e1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> linarith
    · show kGreedy C μ a b s 1 ≤ C 1
      rw [k1]; rcases e2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;> linarith
    · show kGreedy C μ a b s 2 ≤ C 2
      rw [k2]; rcases e3 with ⟨e3, _⟩ | ⟨e3, _⟩ <;> linarith
  · rw [k0, k1, k2]
    rcases e1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases e2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases e3 with ⟨e3, _⟩ | ⟨e3, _⟩ <;> linarith
  · unfold Inside at hi hj
    have hk0 := k0; have hk1 := k1; have hk2 := k2
    fin_cases i <;> fin_cases j <;> simp at hij hi hj <;>
      rcases e1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases e2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases e3 with ⟨e3, _⟩ | ⟨e3, _⟩ <;> linarith [hi.1, hi.2, hj.1, hj.2]

/-! ### Proposition 26 (i) and (ii) -/

section Main

variable {C : Fin 3 → ℝ} {μ a b s : ℝ} {κ : Fin 3 → ℝ}

/-- Abbreviation: `L̄ᵢ` for the data of Proposition 26. -/
abbrev bL (C : Fin 3 → ℝ) (μ a b : ℝ) (κ : Fin 3 → ℝ) (i : Fin 3) : Measure ℝ :=
  barL (pw μ a b) (qw μ a b) (C i) (κ i)

/-- Abbreviation: `μ̄ᵢ`. -/
abbrev bM (C : Fin 3 → ℝ) (μ a b : ℝ) (κ : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  barMu (pw μ a b) (qw μ a b) (C i) (κ i)

lemma two_p_barMu {p q C κ : ℝ} (hp : 0 < p) :
    2 * p * barMu p q C κ = 2 * p * C - (C - q * κ) := by
  unfold barMu; field_simp

/-- The means of `L̄₁, L̄₂, L̄₃` and `U[0,a]` add up to `s_L = s - 2μ + a`. -/
lemma barMu_sum (h : Hyp C μ a b s) (hA : Adm C μ a b s κ) :
    bM C μ a b κ 0 + bM C μ a b κ 1 + bM C μ a b κ 2 + a / 2 = s - 2 * μ + a := by
  have hp := h.hp
  have e0 := two_p_barMu (q := qw μ a b) (C := C 0) (κ := κ 0) hp
  have e1 := two_p_barMu (q := qw μ a b) (C := C 1) (κ := κ 1) hp
  have e2 := two_p_barMu (q := qw μ a b) (C := C 2) (κ := κ 2) hp
  have hs := h.hs
  have hsum := hA.hsum
  have hpq := h.hpq
  have hpa := h.hpa
  apply mul_left_cancel₀ (show 2 * pw μ a b ≠ 0 by positivity)
  linear_combination e0 + e1 + e2 + (-2 * (2 * pw μ a b - 1)) * hs + qw μ a b * hsum +
    2 * s * hpq - hpa

/-- At an endpoint (`κ = qC` or `κ = C`), `L̄` is uniform: `U[0,pC]` or `U[0,C]`. -/
lemma endpoint_unif {p q C κ : ℝ} (h : KHyp p q C κ) (hni : ¬Inside q C κ) :
    ∃ r, 0 < r ∧ r ≤ C ∧ barL p q C κ = unifI 0 r ∧ r = 2 * barMu p q C κ := by
  unfold Inside at hni
  have hpC : p * C = C - q * C := by rw [show p = 1 - q by linarith [h.hpq]]; ring
  have hqC : 0 < q * C := mul_pos h.hq h.hC
  by_cases h1 : q * C < κ
  · have h2 : κ = C := le_antisymm h.hu (not_lt.mp fun h2 => hni ⟨h1, h2⟩)
    exact ⟨C, h.hC, le_rfl, barL_high h h2, (barMu_high h h2).symm⟩
  · have h2 : κ = q * C := le_antisymm (not_lt.mp h1) h.hl
    exact ⟨p * C, mul_pos h.hp h.hC, by linarith, barL_low h h2, (barMu_low h h2).symm⟩

lemma shape_of {p q C κ S : ℝ} (h : KHyp p q C κ) (hCS : C ≤ S) :
    Shape S (barMu p q C κ) (barL p q C κ) := by
  by_cases hi : Inside q C κ
  · obtain ⟨m1, m2⟩ := barMu_mid h hi.1 hi.2
    exact Or.inr ⟨C - κ, C, by linarith [hi.2], m1, m2, hCS, barL_mid h hi.1 hi.2⟩
  · obtain ⟨r, hr, hrC, he, hrm⟩ := endpoint_unif h hi
    exact Or.inl ⟨r, hr, hrC.trans hCS, he, hrm⟩

/-- **Proposition 26 (i)**. The `Lᵢ = (U[0,Cᵢ] - q U[0,κᵢ])/p` are probability distributions
(`Lm` is the mixture form, `L_sub` the difference form, `L_split` the identity
`q U[0,κᵢ] + p Lᵢ = U[0,Cᵢ]`); `L̄ᵢ` (the law of `Cᵢ - Y`, `Y ∼ Lᵢ`) is `U[0,pCᵢ]` if
`κᵢ = qCᵢ`, `U[0,Cᵢ]` if `κᵢ = Cᵢ`, and `g^{μ̄ᵢ}_{Cᵢ-κᵢ,Cᵢ}` with
`μ̄ᵢ = Cᵢ - (Cᵢ - qκᵢ)/(2p)` otherwise. -/
theorem prop26_i (h : Hyp C μ a b s) (hA : Adm C μ a b s κ) (i : Fin 3) :
    let p := pw μ a b
    let q := qw μ a b
    IsProbabilityMeasure (Lm p q (C i) (κ i)) ∧
    Lm p q (C i) (κ i) = ENNReal.ofReal p⁻¹ • (unifI 0 (C i) - ENNReal.ofReal q • unifI 0 (κ i)) ∧
    ENNReal.ofReal q • unifI 0 (κ i) + ENNReal.ofReal p • Lm p q (C i) (κ i) = unifI 0 (C i) ∧
    barL p q (C i) (κ i) = (Lm p q (C i) (κ i)).map (fun x => C i - x) ∧
    (κ i = q * C i → barL p q (C i) (κ i) = unifI 0 (p * C i)) ∧
    (κ i = C i → barL p q (C i) (κ i) = unifI 0 (C i)) ∧
    (q * C i < κ i → κ i < C i → barL p q (C i) (κ i) =
      gPiece (C i - (C i - q * κ i) / (2 * p)) (C i - κ i) (C i)) := by
  have hk := h.khyp hA i
  exact ⟨Lm_isProb hk, L_sub hk, L_split hk, rfl, barL_low hk, barL_high hk, barL_mid hk⟩

/-- **Proposition 26 (ii)**. The construction of the paper gives a joint mix of `L̄₁, L̄₂, L̄₃`
and `U[0,a]` with sum `s_L = s - 2μ + a`, by segments in `H_{s_L}`: choose `i₀` with
`L̄_{i₀} = U[0,r]` uniform, `Y_{i₀} = rW/(r + a)`, `Y₄ = aW/(r + a)` with `W ∼ U[0, r + a]`
(for `a = 0` this is `Y₄ = 0`), and apply Proposition 24 or Lemma 18 to `W` and the other two
coordinates. -/
theorem prop26_ii (h : Hyp C μ a b s) (hA : Adm C μ a b s κ) :
    SegRep (s - 2 * μ + a) ![bL C μ a b κ 0, bL C μ a b κ 1, bL C μ a b κ 2, unifI 0 a] := by
  have hk := h.khyp hA
  have hm := barMu_sum h hA
  have hCS : ∀ i, C i ≤ s - 2 * μ + a := fun i => by linarith [h.hCs i, h.ha]
  have hCS' : ∀ i, C i + a ≤ s - 2 * μ + a := fun i => by linarith [h.hCs i]
  by_cases h0 : Inside (qw μ a b) (C 0) (κ 0)
  · -- `i₂ = 0`, `i₀ = 1`, `i₁ = 2`
    obtain ⟨r0, hr0, hr0C, he0, hrm0⟩ := endpoint_unif (hk 1) (hA.hone 0 1 (by decide) h0)
    obtain ⟨r1, hr1, hr1C, he1, hrm1⟩ := endpoint_unif (hk 2) (hA.hone 0 2 (by decide) h0)
    have core := ii_core h.ha hr0 hr1 (by linarith [hCS' 1]) (hr1C.trans (hCS 2))
      (shape_of (hk 0) (hCS 0)) (by simp only [bM] at hm; linarith)
    rw [← he0, ← he1] at core
    have := core.reindex ![2, 0, 1, 3] (fun x => by simp [Fin.sum_univ_four]; ring)
    convert this using 1
    funext j; fin_cases j <;> simp [bL]
  by_cases h1 : Inside (qw μ a b) (C 1) (κ 1)
  · -- `i₂ = 1`, `i₀ = 0`, `i₁ = 2`
    obtain ⟨r0, hr0, hr0C, he0, hrm0⟩ := endpoint_unif (hk 0) h0
    obtain ⟨r1, hr1, hr1C, he1, hrm1⟩ := endpoint_unif (hk 2) (hA.hone 1 2 (by decide) h1)
    have core := ii_core h.ha hr0 hr1 (by linarith [hCS' 0]) (hr1C.trans (hCS 2))
      (shape_of (hk 1) (hCS 1)) (by simp only [bM] at hm; linarith)
    rw [← he0, ← he1] at core
    have := core.reindex ![0, 2, 1, 3] (fun x => by simp [Fin.sum_univ_four]; ring)
    convert this using 1
    funext j; fin_cases j <;> simp [bL]
  · -- `i₂ = 2`, `i₀ = 0`, `i₁ = 1`
    obtain ⟨r0, hr0, hr0C, he0, hrm0⟩ := endpoint_unif (hk 0) h0
    obtain ⟨r1, hr1, hr1C, he1, hrm1⟩ := endpoint_unif (hk 1) h1
    have core := ii_core h.ha hr0 hr1 (by linarith [hCS' 0]) (hr1C.trans (hCS 1))
      (shape_of (hk 2) (hCS 2)) (by simp only [bM] at hm; linarith)
    rw [← he0, ← he1] at core
    exact core

/-! ### Proposition 26 (iii) -/

lemma reflect_barL {p q C κ : ℝ} :
    (barL p q C κ).map (fun x => -1 * x + C) = Lm p q C κ := by
  unfold barL
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun x : ℝ => -1 * x + C) ∘ fun x => C - x) = id := by
    funext x; simp only [Function.comp, id]; ring
  rw [this, Measure.map_id]

lemma reflect_unif {a : ℝ} (ha : 0 ≤ a) : (unifI 0 a).map (fun x => -1 * x + a) = unifI 0 a := by
  have h := map_reflect_unifI ha a
  rw [sub_self, sub_zero] at h
  rw [← h]; congr 1; funext x; ring

/-- `q U[0,b] + p U[0,a] = g^μ_{a,b}`. -/
lemma g_split (h : Hyp C μ a b s) :
    ENNReal.ofReal (qw μ a b) • unifI 0 b + ENNReal.ofReal (1 - qw μ a b) • unifI 0 a =
      gPiece μ a b := by
  rw [show 1 - qw μ a b = pw μ a b by linarith [h.hpq], gPiece, add_comm]
  rfl

/-- **Proposition 26 (iii)**, as a construction by segments: with probability `q` a joint mix
by Lemma 18 of `U[0,κ₁], U[0,κ₂], U[0,κ₃], U[0,b]` with sum `s`, and with probability `p` the
vector `(C₁ - Y₁, C₂ - Y₂, C₃ - Y₃, a - Y₄)` for the joint mix `Y` of part (ii), give a joint
mix of `U[0,C₁], U[0,C₂], U[0,C₃]` and `g^μ_{a,b}` with sum `s`; it is a finite mixture of
uniform distributions on segments with endpoints in `H_s`. -/
theorem prop26_iii (h : Hyp C μ a b s) (hA : Adm C μ a b s κ) :
    SegRep s ![unifI 0 (C 0), unifI 0 (C 1), unifI 0 (C 2), gPiece μ a b] := by
  have hk := h.khyp hA
  have hq := h.hq
  have hpq := h.hpq
  have hp := h.hp
  have hs0 : 0 < s := by linarith [h.s2μ, h.hb, h.ha, h.ha2]
  have hκs : ∀ i, κ i ≤ s := fun i => by linarith [hA.hu i, h.hCs i, h.ha, h.ha2]
  have h1 := four_rep_unif (hk 0).κpos.le (hk 1).κpos.le (hk 2).κpos.le (by linarith [h.hb, h.ha,
    h.ha2]) hs0 (hκs 0) (hκs 1) (hκs 2) h.hbs (by linarith [hA.hsum])
  have h2 := prop26_ii h hA
  have h3 := h2.affine (s' := s) id (fun _ => -1) ![C 0, C 1, C 2, a] (fun x hx => by
    simp only [id, Fin.sum_univ_four, Matrix.cons_val] at hx ⊢
    linarith [h.hs])
  have h4 := h1.mix h3 hq.le (by linarith)
  convert h4 using 1
  funext j; fin_cases j
  · simp only [id, Fin.zero_eta, Matrix.cons_val_zero, bL]
    rw [reflect_barL, show 1 - qw μ a b = pw μ a b by linarith, L_split (hk 0)]
  · simp only [id, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, bL]
    rw [reflect_barL, show 1 - qw μ a b = pw μ a b by linarith, L_split (hk 1)]
  · simp only [id, Fin.reduceFinMk, Matrix.cons_val, bL]
    rw [reflect_barL, show 1 - qw μ a b = pw μ a b by linarith, L_split (hk 2)]
  · simp only [id, Fin.reduceFinMk, Matrix.cons_val]
    rw [reflect_unif h.ha, g_split h]

/-- **Proposition 26**, conclusion: for every admissible choice of `κ` (one exists by
`prop26_kappa`), the construction gives a joint mix of `U[0,C₁], U[0,C₂], U[0,C₃]` and
`g^μ_{a,b}` with sum `s`, a finite mixture of uniform distributions on segments in `H_s`. -/
theorem prop26 (h : Hyp C μ a b s) (hA : Adm C μ a b s κ) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (P Q : Fin k → Fin 4 → ℝ), (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1 ∧
      (∀ e, ∑ j, P e j = s) ∧ (∀ e, ∑ j, Q e j = s) ∧
      IsJointMix ![unifI 0 (C 0), unifI 0 (C 1), unifI 0 (C 2), gPiece μ a b] (segMix w P Q) ∧
      ∀ᵐ x ∂segMix w P Q, ∑ j, x j = s :=
  (prop26_iii h hA).joint

/-- The reflection `x ↦ (C₁ - x₁, C₂ - x₂, C₃ - x₃, a - x₄)`. -/
def reflect4 (C : Fin 3 → ℝ) (a : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun j => ![C 0, C 1, C 2, a] j - x j

lemma measurable_reflect4 (C : Fin 3 → ℝ) (a : ℝ) : Measurable (reflect4 C a) := by
  unfold reflect4; fun_prop

/-- **Proposition 26 (iii)**, for arbitrary joint mixes: if `P₁` is any joint mix of
`U[0,κ₁], U[0,κ₂], U[0,κ₃], U[0,b]` with sum `s` and `P₂` any joint mix of `L̄₁, L̄₂, L̄₃, U[0,a]`
with sum `s_L = s - 2μ + a`, then the mixture of `P₁` (probability `q`) and of the law of
`(C₁ - Y₁, C₂ - Y₂, C₃ - Y₃, a - Y₄)`, `Y ∼ P₂` (probability `p`), is a joint mix of
`U[0,C₁], U[0,C₂], U[0,C₃]` and `g^μ_{a,b}` with sum `s`. -/
theorem prop26_iii_general (h : Hyp C μ a b s) (hA : Adm C μ a b s κ)
    {P₁ P₂ : Measure (Fin 4 → ℝ)}
    (h1 : IsJointMix ![unifI 0 (κ 0), unifI 0 (κ 1), unifI 0 (κ 2), unifI 0 b] P₁)
    (h1s : ∀ᵐ x ∂P₁, ∑ j, x j = s)
    (h2 : IsJointMix ![bL C μ a b κ 0, bL C μ a b κ 1, bL C μ a b κ 2, unifI 0 a] P₂)
    (h2s : ∀ᵐ x ∂P₂, ∑ j, x j = s - 2 * μ + a) :
    let P := ENNReal.ofReal (qw μ a b) • P₁ + ENNReal.ofReal (pw μ a b) • P₂.map (reflect4 C a)
    IsJointMix ![unifI 0 (C 0), unifI 0 (C 1), unifI 0 (C 2), gPiece μ a b] P ∧
      ∀ᵐ x ∂P, ∑ j, x j = s := by
  intro P
  have hk := h.khyp hA
  have hR := measurable_reflect4 C a
  have := h1.1
  have := h2.1
  have hsum : ∀ᵐ x ∂P, ∑ j, x j = s := by
    simp only [P]
    rw [ae_add_measure_iff]
    refine ⟨Measure.ae_smul_measure h1s _, Measure.ae_smul_measure ?_ _⟩
    rw [ae_map_iff hR.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [h2s] with x hx
    simp only [reflect4, Finset.sum_sub_distrib, hx, Fin.sum_univ_four, Matrix.cons_val]
    linarith [h.hs]
  refine ⟨⟨⟨?_⟩, ⟨s, hsum⟩, fun j => ?_⟩, hsum⟩
  · simp only [P, add_apply, smul_apply, Measure.map_apply hR MeasurableSet.univ,
      preimage_univ, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h.hq.le h.hp.le, add_comm, h.hpq, ENNReal.ofReal_one]
  · simp only [P]
    rw [Measure.map_add _ _ (measurable_pi_apply j), Measure.map_smul, Measure.map_smul,
      Measure.map_map (measurable_pi_apply j) hR, h1.2.2 j]
    have hj : ((fun x : Fin 4 → ℝ => x j) ∘ reflect4 C a) =
        (fun y => ![C 0, C 1, C 2, a] j - y) ∘ (fun x => x j) := by
      funext x; rfl
    rw [hj, ← Measure.map_map (g := fun y => ![C 0, C 1, C 2, a] j - y) (by fun_prop)
      (measurable_pi_apply j), h2.2.2 j]
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, bL, barL]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have : ((fun y => C 0 - y) ∘ fun x => C 0 - x) = id := by funext x; simp
      rw [this, Measure.map_id, L_split (hk 0)]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, bL, barL]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have : ((fun y => C 1 - y) ∘ fun x => C 1 - x) = id := by funext x; simp
      rw [this, Measure.map_id, L_split (hk 1)]
    · simp only [Fin.reduceFinMk, Matrix.cons_val, bL, barL]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have : ((fun y => C 2 - y) ∘ fun x => C 2 - x) = id := by funext x; simp
      rw [this, Measure.map_id, L_split (hk 2)]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [map_reflect_unifI h.ha, sub_self, sub_zero, ← g_split h,
        show 1 - qw μ a b = pw μ a b by linarith [h.hpq]]
    all_goals exact (measurable_pi_apply _).aemeasurable

end Main

end JointSplit

end Mixes
