import Mixes.Defs
import Mixes.Bodies

/-!
# Sliced complete mixes of a quadrilateral (Proposition 87, `st:prop:quad`)

The proposition is formalised at the level of the laws of the levels and of the chord midpoints.
A *sliced mix* (`IsSlicedMix μ M c Q`) is a probability measure `Q` on triples of levels whose
three marginals are the law `μ` of the level and whose midpoints `M(s₀), M(s₁), M(s₂)` add up to
`3c` almost surely (the condition `M₁ + M₂ + M₃ = 3c` of the proof).

Main results.
* `Quad.Bent.no_slicedMix`: if the midpoints run along two non-parallel segments meeting at one
  point, no sliced mix exists (the chords parallel to a side or a diagonal, in the proof).
* `Quad.Quad3.prop87`: in the generic direction, with the midpoint path made of three segments
  `σ₁, σ₂, σ₃` (directions `v₀, v₁, v₂`), not all collinear: adjacent segments are not
  parallel, `c ∈ σ₂`, and if `c` is inside `σ₂` and `σ₁ ∦ σ₃` then the two triangles have equal
  mass and `3c - P₀ - P₃ ∈ σ₂`.
* `Quad.levelLaw_*`: the hypotheses of `Quad3` on the law of the level (no atoms, positivity,
  quadratic mass at the apices, linear lower bound) follow from a chord-length density.
* `Quad.side_path_straight_iff`, `Quad.diagonal_midpoint`: the elementary geometry of the
  excluded directions.
* `Quad.isSlicedMix_of_sliced`: the conditional-expectation step. For the body between two
  graphs `L ≤ R` (chord coordinates), a `3`-complete mix of `U(K)` that is sliced (`IsSliced`:
  the joint law of the levels `S` and of `Xᵢ` is `law(S) ⊗ U(chord at level Sᵢ)`) gives an
  `IsSlicedMix` of the law of the level (`map_fst_unifSet_body`: density chord length / area),
  the chord midpoints and the centroid.
* `Quad.BentBody.no_sliced`: no sliced `3`-complete mix in an excluded direction (two affine
  pieces, bent midpoint path, `bent_iff_cross`).
* `Quad.QuadBody.prop87`: Proposition 87 for a concrete quadrilateral in a generic direction:
  adjacent segments not parallel, `c ∈ σ₂`, and in the typical case equal areas of the two
  triangles (as Lebesgue measures of subsets of `K`) and `3c - P₀ - P₃ ∈ σ₂`.

* `Quad.prop87_quad`: **Proposition 87 for the quadrilateral of the paper**, the convex hull
  `K = conv {A, B, C, D}` of four points in convex position (`IsQuad`: not a trapezoid, neither
  diagonal bisects the other), with chords in an arbitrary direction `e ≠ 0` and a `3`-complete
  mix of `U(K)` sliced in that direction (`IsSlicedIn`). The geometric reduction: `hull_eq`
  (the quadrilateral is the intersection of the half-planes of its sides), the normalised
  configurations `qG1`, `qG2` (generic direction, `QuadBody`) and `bS1`, `bD1` (chords parallel
  to a side or a diagonal, `BentBody`, whose bend comes from convexity, resp. from the
  no-bisection hypothesis), the symmetries `QuadBody.flip`, `QuadBody.neg`, `BentBody.flip`,
  `BentBody.neg`, the case analysis `rep_all`, and the change of coordinates `TeL e`
  (`isCompleteMix_map`, `sliced_of_body`).

Differences from the paper: the proof works in chord coordinates (the level is the first
coordinate, the chords are vertical); `prop87_quad` transports the result back to `K` by the
linear map `T_e x = (e × x, e · x)`, and the slicing of a mix in the direction `e` is defined in
these coordinates (`IsSlicedIn`: given the levels, each point is uniform on its chord). That
the midpoints are not all on one line is proved from the slopes (exactly one chain has a corner
at each middle vertex level) instead of by the affine reflection along the chords; for chords
parallel to a side, the case `CD ∥ AB` is excluded directly by the trapezoid hypothesis (the
other vertices then have different levels and the lower chain has a corner).
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Mixes.Quad

/-! ### Linear algebra in `ℝ²` -/

/-- The cross product `u × v = u₁ v₂ - u₂ v₁` in `ℝ²`; `u` and `v` are parallel iff it is `0`. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

lemma cross_add (u a b : ℝ × ℝ) : cross u (a + b) = cross u a + cross u b := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring

lemma cross_sub (u a b : ℝ × ℝ) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

lemma cross_smul (u a : ℝ × ℝ) (t : ℝ) : cross u (t • a) = t * cross u a := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma cross_self (u : ℝ × ℝ) : cross u u = 0 := by simp only [cross]; ring

lemma cross_anti (u v : ℝ × ℝ) : cross u v = - cross v u := by simp only [cross]; ring

/-- Two linear equations with independent directions have at most one solution. -/
lemma eq_zero_of_cross {u u' w : ℝ × ℝ} (h : cross u u' ≠ 0) (h1 : cross u w = 0)
    (h2 : cross u' w = 0) : w = 0 := by
  unfold cross at *
  have e1 : (u.1 * u'.2 - u.2 * u'.1) * w.1 = 0 := by linear_combination u'.1 * h1 - u.1 * h2
  have e2 : (u.1 * u'.2 - u.2 * u'.1) * w.2 = 0 := by linear_combination u'.2 * h1 - u.2 * h2
  exact Prod.ext ((mul_eq_zero.1 e1).resolve_left h) ((mul_eq_zero.1 e2).resolve_left h)

/-- If `a u₁ + b u₂ + d u₃ = w`, then `b (u₂ × u₃) = w × u₃ - a (u₁ × u₃)`, written with the
cross product on the left: `b · cross u₃ u₂ = cross u₃ w - a · cross u₃ u₁`. -/
lemma solve_coef {a b d : ℝ} {u₁ u₂ u₃ w : ℝ × ℝ} (h : a • u₁ + b • u₂ + d • u₃ = w) :
    b * cross u₃ u₂ = cross u₃ w - a * cross u₃ u₁ := by
  rw [← h, cross_add, cross_add, cross_smul, cross_smul, cross_smul, cross_self]; ring

/-- A sum over three distinct indices of `Fin 3` is the full sum. -/
lemma sum_three_perm {V : Type*} [AddCommMonoid V] (f : Fin 3 → V) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : f 0 + f 1 + f 2 = f i + f j + f k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> abel

/-! ### Sliced mixes of the levels -/

/-- The consequence of a sliced `3`-complete mix that the proof of Proposition 87 uses: a
probability measure `Q` on triples of levels whose coordinates have the law `μ` of the level and
whose midpoints `M(S₁) + M(S₂) + M(S₃)` add up to `3c` almost surely. (The paper derives the last
condition from a sliced complete mix of `U(K)` by taking conditional expectations given the
levels; the levels themselves need not have a constant sum.) -/
structure IsSlicedMix (μ : Measure ℝ) (M : ℝ → ℝ × ℝ) (c : ℝ × ℝ) (Q : Measure (Fin 3 → ℝ)) :
    Prop where
  prob : IsProbabilityMeasure Q
  marg : ∀ i, Q.map (fun x => x i) = μ
  sum : ∀ᵐ x ∂Q, M (x 0) + M (x 1) + M (x 2) = (3 : ℝ) • c

section Sliced

variable {μ : Measure ℝ} {M : ℝ → ℝ × ℝ} {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}

lemma IsSlicedMix.le_mu (h : IsSlicedMix μ M c Q) (i : Fin 3) (B : Set ℝ) :
    Q {x | x i ∈ B} ≤ μ B := by
  have := Measure.le_map_apply (μ := Q) (measurable_pi_apply i).aemeasurable B
  rwa [h.marg i] at this

lemma IsSlicedMix.eq_mu (h : IsSlicedMix μ M c Q) (i : Fin 3) {B : Set ℝ}
    (hB : MeasurableSet B) : Q {x | x i ∈ B} = μ B := by
  rw [← h.marg i, Measure.map_apply (measurable_pi_apply i) hB]; rfl

lemma IsSlicedMix.ae_mem (h : IsSlicedMix μ M c Q) (i : Fin 3) {B : Set ℝ}
    (hB : μ Bᶜ = 0) : ∀ᵐ x ∂Q, x i ∈ B := by
  rw [ae_iff]
  exact measure_mono_null (fun x hx => hx) (le_antisymm ((h.le_mu i Bᶜ).trans hB.le) bot_le)

/-- **First paragraph of the proof.** If two midpoints lie on lines with the direction `u` and the
third on a line with a direction `u'` not parallel to `u`, the third is a fixed point, which no
`M(Sᵢ)` charges; so the event has probability `0`. -/
lemma IsSlicedMix.null_two_one (h : IsSlicedMix μ M c Q) (hat : ∀ q, μ (M ⁻¹' {q}) = 0)
    {u u' a a' a'' : ℝ × ℝ} (hu : cross u u' ≠ 0) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    Q {x | cross u (M (x i) - a) = 0 ∧ cross u (M (x j) - a') = 0 ∧
      cross u' (M (x k) - a'') = 0} = 0 := by
  set S : Set (ℝ × ℝ) := {p | cross u p = cross u ((3 : ℝ) • c - a - a') ∧ cross u' (p - a'') = 0}
  have hS : S.Subsingleton := by
    intro p hp q hq
    have h1 : cross u (p - q) = 0 := by rw [cross_sub, hp.1, hq.1, sub_self]
    have h2 : cross u' (p - q) = 0 := by
      have : p - q = (p - a'') - (q - a'') := by abel
      rw [this, cross_sub, hp.2, hq.2, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_cross hu h1 h2)
  have hsum := h.sum
  rw [ae_iff] at hsum
  refine measure_mono_null (t := {x | x k ∈ M ⁻¹' S} ∪
    {x | ¬ M (x 0) + M (x 1) + M (x 2) = (3 : ℝ) • c}) ?_ (measure_union_null ?_ hsum)
  · intro x ⟨h1, h2, h3⟩
    by_cases hx : M (x 0) + M (x 1) + M (x 2) = (3 : ℝ) • c
    · left
      refine ⟨?_, h3⟩
      rw [sum_three_perm (fun t => M (x t)) hij hik hjk] at hx
      have : M (x k) = (3 : ℝ) • c - M (x i) - M (x j) := by rw [← hx]; abel
      rw [this]
      have e1 := h1; have e2 := h2
      rw [cross_sub] at e1 e2
      simp only [cross_sub] at *
      linarith
    · exact Or.inr hx
  · refine le_antisymm ((h.le_mu k _).trans ?_) bot_le
    rcases hS.eq_empty_or_singleton with he | ⟨q, hq⟩
    · simp [he]
    · rw [hq, hat q]

/-- If all three midpoints lie on one line, so does `c`. -/
lemma three_on_line {u a : ℝ × ℝ} {p : Fin 3 → ℝ × ℝ} (hs : p 0 + p 1 + p 2 = (3 : ℝ) • c)
    (h : ∀ i, cross u (p i - a) = 0) : cross u (c - a) = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only [cross_sub] at *
  have : cross u ((3 : ℝ) • c) = 3 * cross u c := cross_smul _ _ _
  rw [← hs, cross_add, cross_add] at this
  linarith

end Sliced

/-! ### Counting the coordinates in a part -/

open Classical in
/-- The number of coordinates of a triple that lie in `B`. -/
def cnt (B : Set ℝ) (x : Fin 3 → ℝ) : ℕ := (Finset.univ.filter fun i => x i ∈ B).card

lemma cnt_pos_iff {B : Set ℝ} {x : Fin 3 → ℝ} : 1 ≤ cnt B x ↔ ∃ i, x i ∈ B := by
  classical
  unfold cnt
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

lemma cnt_two {B : Set ℝ} {x : Fin 3 → ℝ} (h : 2 ≤ cnt B x) :
    ∃ i j, i ≠ j ∧ x i ∈ B ∧ x j ∈ B := by
  classical
  unfold cnt at h
  have h' : 1 < (Finset.univ.filter fun i => x i ∈ B).card := h
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact ⟨i, j, hij, hi, hj⟩

lemma cnt_three {B : Set ℝ} {x : Fin 3 → ℝ} (h : cnt B x = 3) : ∀ i, x i ∈ B := by
  classical
  unfold cnt at h
  have : (Finset.univ.filter fun i => x i ∈ B) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using h)
  intro i
  have hi : i ∈ (Finset.univ.filter fun i => x i ∈ B) := by rw [this]; exact Finset.mem_univ i
  simpa using hi

lemma cnt_le_one {B : Set ℝ} {x : Fin 3 → ℝ} (h : cnt B x ≤ 1) {i j : Fin 3} (hi : x i ∈ B)
    (hj : x j ∈ B) : i = j := by
  by_contra hij
  classical
  unfold cnt at h
  have : 1 < (Finset.univ.filter fun i => x i ∈ B).card :=
    Finset.one_lt_card.2 ⟨i, by simpa using hi, j, by simpa using hj, hij⟩
  omega

lemma cnt_eq_sum (B : Set ℝ) (x : Fin 3 → ℝ) [DecidablePred (· ∈ B)] :
    cnt B x = ∑ i, if x i ∈ B then 1 else 0 := by
  classical
  unfold cnt
  simp only [Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => by congr

/-- Three pairwise disjoint parts that contain every coordinate. -/
lemma cnt_add_three {B₁ B₂ B₃ : Set ℝ} (h12 : Disjoint B₁ B₂) (h13 : Disjoint B₁ B₃)
    (h23 : Disjoint B₂ B₃) {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ B₁ ∪ B₂ ∪ B₃) :
    cnt B₁ x + cnt B₂ x + cnt B₃ x = 3 := by
  classical
  rw [cnt_eq_sum, cnt_eq_sum, cnt_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have : ∀ i, ((if x i ∈ B₁ then 1 else 0) + (if x i ∈ B₂ then 1 else 0) +
      (if x i ∈ B₃ then 1 else 0) : ℕ) = 1 := by
    intro i
    rcases hx i with (h1 | h2) | h3
    · rw [if_pos h1, if_neg (Set.disjoint_left.1 h12 h1), if_neg (Set.disjoint_left.1 h13 h1)]
    · rw [if_neg (Set.disjoint_right.1 h12 h2), if_pos h2, if_neg (Set.disjoint_left.1 h23 h2)]
    · rw [if_neg (Set.disjoint_right.1 h13 h3), if_neg (Set.disjoint_right.1 h23 h3), if_pos h3]
  simp [this]

section Counting

variable {μ : Measure ℝ} {M : ℝ → ℝ × ℝ} {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}

/-- Two coordinates on lines of direction `u` (in the parts `B`, `B'`) and one on a line of a
nonparallel direction (in the part `B''`, disjoint from both) has probability `0`. -/
lemma IsSlicedMix.ae_not_two_one (h : IsSlicedMix μ M c Q) (hat : ∀ q, μ (M ⁻¹' {q}) = 0)
    {B B'' : Set ℝ} (hd : Disjoint B B'') {u u' a a'' : ℝ × ℝ} (hu : cross u u' ≠ 0)
    (hB : ∀ s ∈ B, cross u (M s - a) = 0) (hB'' : ∀ s ∈ B'', cross u' (M s - a'') = 0) :
    ∀ᵐ x ∂Q, ¬ (2 ≤ cnt B x ∧ 1 ≤ cnt B'' x) := by
  rw [ae_iff]
  simp only [not_not]
  refine measure_mono_null (t := ⋃ i : Fin 3, ⋃ j : Fin 3, ⋃ k : Fin 3,
    {x | i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (cross u (M (x i) - a) = 0 ∧ cross u (M (x j) - a) = 0 ∧
      cross u' (M (x k) - a'') = 0)}) ?_ ?_
  · intro x ⟨h2, h1⟩
    obtain ⟨i, j, hij, hi, hj⟩ := cnt_two h2
    obtain ⟨k, hk⟩ := cnt_pos_iff.1 h1
    have hik : i ≠ k := fun e => Set.disjoint_left.1 hd hi (e ▸ hk)
    have hjk : j ≠ k := fun e => Set.disjoint_left.1 hd hj (e ▸ hk)
    simp only [mem_iUnion, mem_setOf_eq]
    exact ⟨i, j, k, hij, hik, hjk, hB _ hi, hB _ hj, hB'' _ hk⟩
  · refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
    by_cases hd : i ≠ j ∧ i ≠ k ∧ j ≠ k
    · refine measure_mono_null (t := {x | cross u (M (x i) - a) = 0 ∧
        cross u (M (x j) - a) = 0 ∧ cross u' (M (x k) - a'') = 0}) (fun x hx => hx.2.2.2) ?_
      exact h.null_two_one hat hu hd.1 hd.2.1 hd.2.2
    · refine measure_mono_null (fun x hx => hd ⟨hx.1, hx.2.1, hx.2.2.1⟩) measure_empty

/-- **Counting.** If almost surely at most one coordinate lies in `B`, then the probability that
some coordinate lies in `B` is `3 μ(B)`. -/
lemma IsSlicedMix.measure_exists (h : IsSlicedMix μ M c Q) {B : Set ℝ} (hB : MeasurableSet B)
    (h1 : ∀ᵐ x ∂Q, cnt B x ≤ 1) : Q {x | ∃ i, x i ∈ B} = 3 * μ B := by
  have he : {x : Fin 3 → ℝ | ∃ i, x i ∈ B} = ⋃ i, {x | x i ∈ B} := by ext x; simp
  rw [he, measure_iUnion₀, tsum_fintype]
  · simp only [fun i => h.eq_mu i hB, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  · intro i j hij
    change Q ({x : Fin 3 → ℝ | x i ∈ B} ∩ {x | x j ∈ B}) = 0
    rw [ae_iff] at h1
    exact measure_mono_null (t := {x | ¬ cnt B x ≤ 1})
      (fun x hx' hx => hij (cnt_le_one hx hx'.1 hx'.2)) h1
  · exact fun i => (measurable_pi_apply i hB).nullMeasurableSet

end Counting

/-! ### Means and positivity -/

section Mean

variable {μ : Measure ℝ} {M : ℝ → ℝ × ℝ} {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}

lemma continuous_cross_comp (hM : Continuous M) (u q : ℝ × ℝ) :
    Continuous fun s => cross u (M s - q) := by
  unfold cross; fun_prop

lemma integrable_of_supp [IsFiniteMeasure μ] {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hsupp : μ (Icc a b)ᶜ = 0) : Integrable f μ := by
  have : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hsupp)
  rw [← this]
  exact hf.continuousOn.integrableOn_compact isCompact_Icc

/-- **The mean of the midpoints is `c`**, tested against the affine functions
`p ↦ u × (p - q)`. -/
lemma IsSlicedMix.integral_cross (h : IsSlicedMix μ M c Q) [IsFiniteMeasure μ]
    (hM : Continuous M) {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0) (u q : ℝ × ℝ) :
    ∫ s, cross u (M s - q) ∂μ = cross u (c - q) := by
  have hQ := h.prob
  set f := fun s => cross u (M s - q)
  have hf := continuous_cross_comp hM u q
  have hfi : Integrable f μ := integrable_of_supp hf hsupp
  have hcoord : ∀ i : Fin 3, ∫ x, f (x i) ∂Q = ∫ s, f s ∂μ := fun i => by
    rw [← h.marg i, integral_map (measurable_pi_apply i).aemeasurable
      hf.aestronglyMeasurable]
  have hint : ∀ i : Fin 3, Integrable (fun x : Fin 3 → ℝ => f (x i)) Q := fun i => by
    have : Integrable f (Q.map fun x => x i) := by rw [h.marg i]; exact hfi
    exact this.comp_measurable (measurable_pi_apply i)
  have hae : ∀ᵐ x ∂Q, ∑ i, f (x i) = 3 * cross u (c - q) := by
    filter_upwards [h.sum] with x hx
    simp only [Fin.sum_univ_three, f, cross_sub]
    have := congrArg (cross u) hx
    rw [cross_add, cross_add, cross_smul] at this
    linarith
  have h1 := integral_congr_ae hae
  rw [integral_finsetSum _ (fun i _ => hint i), integral_const] at h1
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    probReal_univ, smul_eq_mul, one_mul] at h1
  push_cast at h1
  linarith

/-- A nonnegative integrable function with integral `0` cannot be positive on a set of positive
measure. -/
lemma false_of_integral_zero {f : ℝ → ℝ} (hfi : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f)
    (hint : ∫ s, f s ∂μ = 0) {S : Set ℝ} (hS : 0 < μ S) (hpos : ∀ s ∈ S, 0 < f s) : False := by
  have := (integral_eq_zero_iff_of_nonneg_ae hf0 hfi).1 hint
  rw [EventuallyEq, ae_iff] at this
  have : μ S = 0 := measure_mono_null (t := {s | ¬ f s = (0 : ℝ → ℝ) s})
    (fun s hs hfs => (hpos s hs).ne' hfs) this
  exact hS.ne' this

end Mean

/-! ### Two segments meeting at an angle -/

/-- The setting of the second paragraph of the proof (chords parallel to a side or a diagonal):
the level has a law `μ` on `[a, b]` without atoms that charges every subinterval, the midpoint
`M(s)` lies at level `s` (`lam (M s) = s` for a linear functional `lam`), and `M` is affine on
`[a, t]` and on `[t, b]` with the directions `w₀` and `w₁`. -/
structure Bent where
  (a t b : ℝ)
  hat : a < t
  htb : t < b
  μ : Measure ℝ
  prob : IsProbabilityMeasure μ
  noAtoms : NullSingletonClass μ
  supp : μ (Icc a b)ᶜ = 0
  pos : ∀ x y, a ≤ x → x < y → y ≤ b → 0 < μ (Ioo x y)
  M : ℝ → ℝ × ℝ
  cont : Continuous M
  lam : ℝ × ℝ →ₗ[ℝ] ℝ
  lam_M : ∀ s, lam (M s) = s
  (w₀ w₁ : ℝ × ℝ)
  aff₀ : ∀ s ∈ Icc a t, M s = M t + (s - t) • w₀
  aff₁ : ∀ s ∈ Icc t b, M s = M t + (s - t) • w₁

/-- A midpoint map that records the level has no atoms. -/
lemma measure_preimage_singleton_eq_zero {μ : Measure ℝ} [NullSingletonClass μ] {M : ℝ → ℝ × ℝ}
    {lam : ℝ × ℝ →ₗ[ℝ] ℝ} (hlam : ∀ s, lam (M s) = s) (q : ℝ × ℝ) : μ (M ⁻¹' {q}) = 0 :=
  measure_mono_null (t := {lam q}) (fun s hs => by
    simp only [mem_preimage, mem_singleton_iff] at hs ⊢; rw [← hs, hlam]) (measure_singleton _)

lemma ae_mem_of_supp {μ : Measure ℝ} [NullSingletonClass μ] {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0)
    (F : Finset ℝ) {B : Set ℝ} (hB : Icc a b \ ↑F ⊆ B) : μ Bᶜ = 0 := by
  refine measure_mono_null (t := (Icc a b)ᶜ ∪ ↑F) (fun s hs => ?_)
    (measure_union_null hsupp (F.finite_toSet.measure_zero μ))
  by_contra h
  simp only [mem_union, mem_compl_iff, not_or, not_not] at h
  exact hs (hB ⟨h.1, h.2⟩)

namespace Bent

variable (S : Bent)

lemma hat' : ∀ q, S.μ (S.M ⁻¹' {q}) = 0 := by
  have := S.noAtoms; exact measure_preimage_singleton_eq_zero S.lam_M

/-- `c` lies on neither line, since it is the mean of the midpoints. -/
lemma not_on_line₀ (hw : cross S.w₀ S.w₁ ≠ 0) {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}
    (h : IsSlicedMix S.μ S.M c Q) : cross S.w₀ (c - S.M S.t) ≠ 0 := by
  have := S.prob
  intro hc
  set k := cross S.w₀ S.w₁
  have hval : ∀ s ∈ Icc S.a S.b, cross S.w₀ (S.M s - S.M S.t) = max (s - S.t) 0 * k := by
    intro s hs
    rcases le_total s S.t with hst | hst
    · rw [S.aff₀ s ⟨hs.1, hst⟩, add_sub_cancel_left, cross_smul, cross_self,
        max_eq_right (by linarith)]; ring
    · rw [S.aff₁ s ⟨hst, hs.2⟩, add_sub_cancel_left, cross_smul, max_eq_left (by linarith)]
  have hmean := h.integral_cross S.cont S.supp S.w₀ (S.M S.t)
  rw [hc] at hmean
  have hae : ∀ᵐ s ∂S.μ, s ∈ Icc S.a S.b := by rw [ae_iff]; exact S.supp
  refine false_of_integral_zero (μ := S.μ) (f := fun s => k * cross S.w₀ (S.M s - S.M S.t))
    ((integrable_of_supp (continuous_cross_comp S.cont _ _) S.supp).const_mul k) ?_
    (by rw [integral_const_mul, hmean, mul_zero]) (S.pos S.t S.b S.hat.le S.htb le_rfl) ?_
  · filter_upwards [hae] with s hs
    simp only [Pi.zero_apply, hval s hs]
    nlinarith [le_max_right (s - S.t) 0, sq_nonneg k]
  · intro s hs
    simp only [hval s ⟨S.hat.le.trans hs.1.le, hs.2.le⟩, max_eq_left (by linarith [hs.1] :
      0 ≤ s - S.t)]
    have : 0 < s - S.t := by linarith [hs.1]
    have : 0 < k * k := mul_self_pos.2 hw
    nlinarith

lemma not_on_line₁ (hw : cross S.w₀ S.w₁ ≠ 0) {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}
    (h : IsSlicedMix S.μ S.M c Q) : cross S.w₁ (c - S.M S.t) ≠ 0 := by
  have := S.prob
  intro hc
  set k := cross S.w₁ S.w₀
  have hk : k ≠ 0 := by simp only [k]; rw [cross_anti]; exact neg_ne_zero.2 hw
  have hval : ∀ s ∈ Icc S.a S.b, cross S.w₁ (S.M s - S.M S.t) = min (s - S.t) 0 * k := by
    intro s hs
    rcases le_total s S.t with hst | hst
    · rw [S.aff₀ s ⟨hs.1, hst⟩, add_sub_cancel_left, cross_smul, min_eq_left (by linarith)]
    · rw [S.aff₁ s ⟨hst, hs.2⟩, add_sub_cancel_left, cross_smul, cross_self,
        min_eq_right (by linarith)]; ring
  have hmean := h.integral_cross S.cont S.supp S.w₁ (S.M S.t)
  rw [hc] at hmean
  have hae : ∀ᵐ s ∂S.μ, s ∈ Icc S.a S.b := by rw [ae_iff]; exact S.supp
  refine false_of_integral_zero (μ := S.μ) (f := fun s => -k * cross S.w₁ (S.M s - S.M S.t))
    ((integrable_of_supp (continuous_cross_comp S.cont _ _) S.supp).const_mul (-k)) ?_
    (by rw [integral_const_mul, hmean, mul_zero]) (S.pos S.a S.t le_rfl S.hat S.htb.le) ?_
  · filter_upwards [hae] with s hs
    simp only [Pi.zero_apply, hval s hs]
    nlinarith [min_le_right (s - S.t) 0, sq_nonneg k]
  · intro s hs
    simp only [hval s ⟨hs.1.le, hs.2.le.trans S.htb.le⟩, min_eq_left (by linarith [hs.2] :
      s - S.t ≤ 0)]
    have : s - S.t < 0 := by linarith [hs.2]
    have : 0 < k * k := mul_self_pos.2 hk
    nlinarith

/-- **Second paragraph of the proof of Proposition 87.** If the midpoints lie on two segments
that meet at an angle, there is no sliced `3`-complete mix. -/
theorem no_slicedMix (hw : cross S.w₀ S.w₁ ≠ 0) (c : ℝ × ℝ) (Q : Measure (Fin 3 → ℝ)) :
    ¬ IsSlicedMix S.μ S.M c Q := by
  intro h
  have := S.noAtoms
  have := h.prob
  have h0 := S.not_on_line₀ hw h
  have h1 := S.not_on_line₁ hw h
  have hw' : cross S.w₁ S.w₀ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 hw
  set B₀ := Ioo S.a S.t
  set B₁ := Ioo S.t S.b
  have hd : Disjoint B₀ B₁ := Set.disjoint_left.2 fun s h0 h1 => by
    linarith [h0.2, h1.1]
  have hl₀ : ∀ s ∈ B₀, cross S.w₀ (S.M s - S.M S.t) = 0 := fun s hs => by
    rw [S.aff₀ s ⟨hs.1.le, hs.2.le⟩, add_sub_cancel_left, cross_smul, cross_self, mul_zero]
  have hl₁ : ∀ s ∈ B₁, cross S.w₁ (S.M s - S.M S.t) = 0 := fun s hs => by
    rw [S.aff₁ s ⟨hs.1.le, hs.2.le⟩, add_sub_cancel_left, cross_smul, cross_self, mul_zero]
  have hcov : S.μ (B₀ ∪ B₁ ∪ ∅)ᶜ = 0 := ae_mem_of_supp S.supp {S.a, S.t, S.b} (by
    intro s ⟨hs, hF⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
      not_or] at hF
    rcases lt_or_gt_of_ne hF.2.1 with h | h
    · exact Or.inl (Or.inl ⟨lt_of_le_of_ne hs.1 (Ne.symm hF.1), h⟩)
    · exact Or.inl (Or.inr ⟨h, lt_of_le_of_ne hs.2 hF.2.2⟩))
  have hnot : ∀ᵐ x ∂Q, False := by
    filter_upwards [h.ae_mem 0 hcov, h.ae_mem 1 hcov, h.ae_mem 2 hcov, h.sum,
      h.ae_not_two_one S.hat' hd hw hl₀ hl₁, h.ae_not_two_one S.hat' hd.symm hw' hl₁ hl₀]
      with x hx0 hx1 hx2 hs n01 n10
    have hx : ∀ i, x i ∈ B₀ ∪ B₁ ∪ ∅ := fun i => by fin_cases i <;> assumption
    have htot := cnt_add_three hd (Set.disjoint_empty _) (Set.disjoint_empty _) hx
    have he : cnt ∅ x = 0 := by
      by_contra hne
      obtain ⟨i, hi⟩ := cnt_pos_iff.1 (Nat.one_le_iff_ne_zero.2 hne)
      exact hi
    have t0 : cnt B₀ x ≠ 3 := fun h3 => h0 (three_on_line (p := fun i => S.M (x i)) hs
      fun i => hl₀ _ (cnt_three h3 i))
    have t1 : cnt B₁ x ≠ 3 := fun h3 => h1 (three_on_line (p := fun i => S.M (x i)) hs
      fun i => hl₁ _ (cnt_three h3 i))
    omega
  exact (ae_neBot.2 (IsProbabilityMeasure.ne_zero Q)).ne (by
    rwa [← Filter.eventually_false_iff_eq_bot])

end Bent

/-! ### Affine images of the level distributions -/

section Affine

variable {μ : Measure ℝ} {M : ℝ → ℝ × ℝ} {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}

lemma cnt_mono {B J : Set ℝ} (hBJ : B ⊆ J) (x : Fin 3 → ℝ) : cnt B x ≤ cnt J x := by
  classical
  unfold cnt
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hBJ hi

/-- **Transfer of distributions.** Suppose that almost surely at most one coordinate lies in `I`
and at most one in `J`, that a triple meets `I` iff it meets `J`, and that the coordinate in `J`
is `φ` of the coordinate in `I`. Then the law of the level restricted to `J` is the image under
`φ` of its restriction to `I`. -/
lemma IsSlicedMix.transfer (h : IsSlicedMix μ M c Q) {I J : Set ℝ} (hI : MeasurableSet I)
    (h1 : ∀ᵐ x ∂Q, cnt I x ≤ 1) (h2 : ∀ᵐ x ∂Q, cnt J x ≤ 1)
    (h3 : ∀ᵐ x ∂Q, (1 ≤ cnt I x ↔ 1 ≤ cnt J x)) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hrel : ∀ᵐ x ∂Q, ∀ i k, x i ∈ I → x k ∈ J → x k = φ (x i)) {B : Set ℝ}
    (hB : MeasurableSet B) (hBJ : B ⊆ J) : μ B = μ (I ∩ φ ⁻¹' B) := by
  have e1 := h.measure_exists hB (by
    filter_upwards [h2] with x hx using (cnt_mono hBJ x).trans hx)
  have e2 := h.measure_exists (hI.inter (hφ hB)) (by
    filter_upwards [h1] with x hx using (cnt_mono inter_subset_left x).trans hx)
  have heq : {x : Fin 3 → ℝ | ∃ k, x k ∈ B} =ᵐ[Q] {x | ∃ i, x i ∈ I ∩ φ ⁻¹' B} := by
    filter_upwards [h3, hrel] with x h3x hrx
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨i, hi⟩ := cnt_pos_iff.1 (h3x.2 (cnt_pos_iff.2 ⟨k, hBJ hk⟩))
      exact ⟨i, hi, by simpa [mem_preimage, ← hrx i k hi (hBJ hk)] using hk⟩
    · rintro ⟨i, hi, hiB⟩
      obtain ⟨k, hk⟩ := cnt_pos_iff.1 (h3x.1 (cnt_pos_iff.2 ⟨i, hi⟩))
      exact ⟨k, by rw [hrx i k hi hk]; exact hiB⟩
  rw [measure_congr heq, e2] at e1
  exact ((ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 e1).symm

/-- An affine relation between the levels of two parts maps each part into the closure of the
other, when the level charges every subinterval. -/
lemma maps_into {a b a' b' : ℝ} (hab : a < b) {f g : ℝ → ℝ} (hf : Continuous f)
    (hfg : ∀ u, f (g u) = u) (posI : ∀ x y, a ≤ x → x < y → y ≤ b → 0 < μ (Ioo x y))
    (R : ∀ B, MeasurableSet B → B ⊆ Ioo a b → μ B = μ (Ioo a' b' ∩ g ⁻¹' B)) :
    ∀ t ∈ Icc a b, f t ∈ Icc a' b' := by
  have hin : Ioo a b ⊆ {t | f t ∈ Icc a' b'} := by
    intro t ht
    by_contra hft
    set U := Ioo a b ∩ f ⁻¹' (Icc a' b')ᶜ
    have hU : IsOpen U := isOpen_Ioo.inter (isClosed_Icc.isOpen_compl.preimage hf)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t ⟨ht, hft⟩
    set ε' := min ε (min (t - a) (b - t))
    have hε' : 0 < ε' := lt_min hε (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
    have hsub : Ioo (t - ε') (t + ε') ⊆ U := fun s hs => hball (by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [hs.1, min_le_left ε (min (t - a) (b - t))],
        by linarith [hs.2, min_le_left ε (min (t - a) (b - t))]⟩)
    have hpos := posI (t - ε') (t + ε')
      (by linarith [min_le_right ε (min (t - a) (b - t)), min_le_left (t - a) (b - t)])
      (by linarith)
      (by linarith [min_le_right ε (min (t - a) (b - t)), min_le_right (t - a) (b - t)])
    rw [R _ measurableSet_Ioo (hsub.trans inter_subset_left)] at hpos
    refine hpos.ne' (measure_mono_null (t := ∅) (fun u ⟨hu, hgu⟩ => ?_) measure_empty)
    have := (hsub hgu).2
    simp only [mem_preimage, mem_compl_iff, hfg] at this
    exact this ⟨hu.1.le, hu.2.le⟩
  have hcl : IsClosed {t | f t ∈ Icc a' b'} := isClosed_Icc.preimage hf
  intro t ht
  rw [← closure_Ioo hab.ne] at ht
  exact hcl.closure_subset_iff.2 hin ht

/-- **Endpoints correspond.** For an affine relation `u = α + β t` (`β ≠ 0`) between two parts,
each charging all of its subintervals, the endpoints are mapped onto the endpoints. -/
lemma endpoints {a b a' b' α β : ℝ} (hab : a < b) (ha'b' : a' < b') (hβ : β ≠ 0)
    (posI : ∀ x y, a ≤ x → x < y → y ≤ b → 0 < μ (Ioo x y))
    (posJ : ∀ x y, a' ≤ x → x < y → y ≤ b' → 0 < μ (Ioo x y))
    (R1 : ∀ B, MeasurableSet B → B ⊆ Ioo a' b' →
      μ B = μ (Ioo a b ∩ (fun t => α + β * t) ⁻¹' B))
    (R2 : ∀ B, MeasurableSet B → B ⊆ Ioo a b →
      μ B = μ (Ioo a' b' ∩ (fun u => (u - α) / β) ⁻¹' B)) :
    (0 < β ∧ α + β * a = a' ∧ α + β * b = b') ∨ (β < 0 ∧ α + β * a = b' ∧ α + β * b = a') := by
  have h1 := maps_into hab (f := fun t => α + β * t) (g := fun u => (u - α) / β)
    (by fun_prop) (fun u => by field_simp; ring) posI R2
  have h2 := maps_into ha'b' (f := fun u => (u - α) / β) (g := fun t => α + β * t)
    (by fun_prop) (fun u => by field_simp; ring) posJ R1
  obtain ⟨ha1, ha2⟩ := h1 a ⟨le_rfl, hab.le⟩
  obtain ⟨hb1, hb2⟩ := h1 b ⟨hab.le, le_rfl⟩
  have hp := h2 a' ⟨le_rfl, ha'b'.le⟩
  have hq := h2 b' ⟨ha'b'.le, le_rfl⟩
  set p := (a' - α) / β
  set q := (b' - α) / β
  have ep : α + β * p = a' := by simp only [p]; field_simp; ring
  have eq' : α + β * q = b' := by simp only [q]; field_simp; ring
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · right
    refine ⟨hneg, ?_, ?_⟩
    · nlinarith [hq.1]
    · nlinarith [hp.2]
  · left
    refine ⟨hpos, ?_, ?_⟩
    · nlinarith [hp.1]
    · nlinarith [hq.2]

/-- A quadratic upper bound cannot dominate a linear lower bound near `0`. -/
lemma false_of_rel {m C κ ε₀ : ℝ} (hm : 0 < m) (hε₀ : 0 < ε₀) (B A : ℝ → Set ℝ)
    (hlow : ∀ ε, 0 < ε → ε ≤ ε₀ → ENNReal.ofReal (m * ε) ≤ μ (B ε))
    (hrel : ∀ ε, 0 < ε → ε ≤ ε₀ → μ (B ε) ≤ μ (A ε))
    (hquad : ∀ ε, 0 < ε → ε ≤ ε₀ → μ (A ε) ≤ ENNReal.ofReal (C * (κ * ε) ^ 2)) : False := by
  set D := |C| * κ ^ 2 + 1
  have hD : 0 < D := by positivity
  set ε := min ε₀ (m / (2 * D))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have key := ((hlow ε hε hεle).trans (hrel ε hε hεle)).trans (hquad ε hε hεle)
  rcases (ENNReal.ofReal_le_ofReal_iff' ).1 key with h | h
  · have h2 : D * ε ≤ m / 2 := by
      have := min_le_right ε₀ (m / (2 * D))
      calc D * ε ≤ D * (m / (2 * D)) := mul_le_mul_of_nonneg_left this hD.le
        _ = m / 2 := by field_simp
    have h3 : C * (κ * ε) ^ 2 ≤ |C| * κ ^ 2 * ε * ε := by
      have : C ≤ |C| := le_abs_self C
      nlinarith [sq_nonneg (κ * ε)]
    have h4 : |C| * κ ^ 2 * ε ≤ D * ε := by nlinarith
    nlinarith
  · nlinarith

section Apex

variable {μ : Measure ℝ} {a b a' b' α β m C ε₀ : ℝ}

/-- The four ways in which an apex of a triangle (where the density of the level vanishes
linearly, so that the mass near it is quadratic) can correspond, under an affine relation `R1`,
to an endpoint of another part where the density is bounded below: all are impossible. -/
lemma apex_left_pos (hm : 0 < m) (hβ : 0 < β) (hφ : α + β * a = a') (hε₀ : 0 < ε₀)
    (hε₀' : ε₀ ≤ b' - a')
    (R1 : ∀ B, MeasurableSet B → B ⊆ Ioo a' b' →
      μ B = μ (Ioo a b ∩ (fun t => α + β * t) ⁻¹' B))
    (quad : ∀ ε, 0 < ε → μ (Ioo a (a + ε)) ≤ ENNReal.ofReal (C * ε ^ 2))
    (low : ∀ ε, 0 < ε → ε ≤ ε₀ → ENNReal.ofReal (m * ε) ≤ μ (Ioo a' (a' + ε))) : False := by
  refine false_of_rel (κ := 1 / β) hm hε₀ (fun ε => Ioo a' (a' + ε))
    (fun ε => Ioo a (a + 1 / β * ε)) low (fun ε hε hεle => ?_) (fun ε hε _ => by
      have := quad (1 / β * ε) (by positivity); simpa [mul_pow] using this)
  rw [R1 _ measurableSet_Ioo (Ioo_subset_Ioo le_rfl (by linarith))]
  refine measure_mono fun t ⟨ht, ht'⟩ => ⟨ht.1, ?_⟩
  simp only [mem_preimage, mem_Ioo] at ht'
  have : β * (t - a) < ε := by linarith [ht'.2]
  have : t - a < ε / β := (lt_div_iff₀ hβ).2 (by linarith)
  calc t < a + ε / β := by linarith
    _ = a + 1 / β * ε := by ring

lemma apex_left_neg (hm : 0 < m) (hβ : β < 0) (hφ : α + β * a = b') (hε₀ : 0 < ε₀)
    (hε₀' : ε₀ ≤ b' - a')
    (R1 : ∀ B, MeasurableSet B → B ⊆ Ioo a' b' →
      μ B = μ (Ioo a b ∩ (fun t => α + β * t) ⁻¹' B))
    (quad : ∀ ε, 0 < ε → μ (Ioo a (a + ε)) ≤ ENNReal.ofReal (C * ε ^ 2))
    (low : ∀ ε, 0 < ε → ε ≤ ε₀ → ENNReal.ofReal (m * ε) ≤ μ (Ioo (b' - ε) b')) : False := by
  have hβ' : 0 < -β := by linarith
  refine false_of_rel (κ := 1 / -β) hm hε₀ (fun ε => Ioo (b' - ε) b')
    (fun ε => Ioo a (a + 1 / -β * ε)) low (fun ε hε hεle => ?_) (fun ε hε _ => by
      have := quad (1 / -β * ε) (by positivity); simpa [mul_pow] using this)
  rw [R1 _ measurableSet_Ioo (Ioo_subset_Ioo (by linarith) le_rfl)]
  refine measure_mono fun t ⟨ht, ht'⟩ => ⟨ht.1, ?_⟩
  simp only [mem_preimage, mem_Ioo] at ht'
  have : -β * (t - a) < ε := by linarith [ht'.1]
  have : t - a < ε / -β := (lt_div_iff₀ hβ').2 (by linarith)
  calc t < a + ε / -β := by linarith
    _ = a + 1 / -β * ε := by ring

lemma apex_right_pos (hm : 0 < m) (hβ : 0 < β) (hφ : α + β * b = b') (hε₀ : 0 < ε₀)
    (hε₀' : ε₀ ≤ b' - a')
    (R1 : ∀ B, MeasurableSet B → B ⊆ Ioo a' b' →
      μ B = μ (Ioo a b ∩ (fun t => α + β * t) ⁻¹' B))
    (quad : ∀ ε, 0 < ε → μ (Ioo (b - ε) b) ≤ ENNReal.ofReal (C * ε ^ 2))
    (low : ∀ ε, 0 < ε → ε ≤ ε₀ → ENNReal.ofReal (m * ε) ≤ μ (Ioo (b' - ε) b')) : False := by
  refine false_of_rel (κ := 1 / β) hm hε₀ (fun ε => Ioo (b' - ε) b')
    (fun ε => Ioo (b - 1 / β * ε) b) low (fun ε hε hεle => ?_) (fun ε hε _ => by
      have := quad (1 / β * ε) (by positivity); simpa [mul_pow] using this)
  rw [R1 _ measurableSet_Ioo (Ioo_subset_Ioo (by linarith) le_rfl)]
  refine measure_mono fun t ⟨ht, ht'⟩ => ⟨?_, ht.2⟩
  simp only [mem_preimage, mem_Ioo] at ht'
  have : β * (b - t) < ε := by linarith [ht'.1]
  have : b - t < ε / β := (lt_div_iff₀ hβ).2 (by linarith)
  calc b - 1 / β * ε = b - ε / β := by ring
    _ < t := by linarith

lemma apex_right_neg (hm : 0 < m) (hβ : β < 0) (hφ : α + β * b = a') (hε₀ : 0 < ε₀)
    (hε₀' : ε₀ ≤ b' - a')
    (R1 : ∀ B, MeasurableSet B → B ⊆ Ioo a' b' →
      μ B = μ (Ioo a b ∩ (fun t => α + β * t) ⁻¹' B))
    (quad : ∀ ε, 0 < ε → μ (Ioo (b - ε) b) ≤ ENNReal.ofReal (C * ε ^ 2))
    (low : ∀ ε, 0 < ε → ε ≤ ε₀ → ENNReal.ofReal (m * ε) ≤ μ (Ioo a' (a' + ε))) : False := by
  have hβ' : 0 < -β := by linarith
  refine false_of_rel (κ := 1 / -β) hm hε₀ (fun ε => Ioo a' (a' + ε))
    (fun ε => Ioo (b - 1 / -β * ε) b) low (fun ε hε hεle => ?_) (fun ε hε _ => by
      have := quad (1 / -β * ε) (by positivity); simpa [mul_pow] using this)
  rw [R1 _ measurableSet_Ioo (Ioo_subset_Ioo le_rfl (by linarith))]
  refine measure_mono fun t ⟨ht, ht'⟩ => ⟨?_, ht.2⟩
  simp only [mem_preimage, mem_Ioo] at ht'
  have : -β * (b - t) < ε := by linarith [ht'.2]
  have : b - t < ε / -β := (lt_div_iff₀ hβ').2 (by linarith)
  calc b - 1 / -β * ε = b - ε / -β := by ring
    _ < t := by linarith

end Apex

end Affine

/-! ### More lemmas on sliced mixes -/

section More

variable {μ : Measure ℝ} {M : ℝ → ℝ × ℝ} {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}

/-- One midpoint on each of three lines, two of them parallel (direction `u`) and the third not:
probability `0` (projecting the equations on a normal of `u` fixes the third midpoint). -/
lemma IsSlicedMix.ae_not_one_one_one (h : IsSlicedMix μ M c Q) (hat : ∀ q, μ (M ⁻¹' {q}) = 0)
    {B B' B'' : Set ℝ} (hd : Disjoint B B') (hd' : Disjoint B B'') (hd'' : Disjoint B' B'')
    {u u' a a' a'' : ℝ × ℝ} (hu : cross u u' ≠ 0) (hB : ∀ s ∈ B, cross u (M s - a) = 0)
    (hB' : ∀ s ∈ B', cross u (M s - a') = 0) (hB'' : ∀ s ∈ B'', cross u' (M s - a'') = 0) :
    ∀ᵐ x ∂Q, ¬ (1 ≤ cnt B x ∧ 1 ≤ cnt B' x ∧ 1 ≤ cnt B'' x) := by
  rw [ae_iff]
  simp only [not_not]
  refine measure_mono_null (t := ⋃ i : Fin 3, ⋃ j : Fin 3, ⋃ k : Fin 3,
    {x | i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (cross u (M (x i) - a) = 0 ∧ cross u (M (x j) - a') = 0 ∧
      cross u' (M (x k) - a'') = 0)}) ?_ ?_
  · intro x ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := cnt_pos_iff.1 h1
    obtain ⟨j, hj⟩ := cnt_pos_iff.1 h2
    obtain ⟨k, hk⟩ := cnt_pos_iff.1 h3
    have hij : i ≠ j := fun e => Set.disjoint_left.1 hd hi (e ▸ hj)
    have hik : i ≠ k := fun e => Set.disjoint_left.1 hd' hi (e ▸ hk)
    have hjk : j ≠ k := fun e => Set.disjoint_left.1 hd'' hj (e ▸ hk)
    simp only [mem_iUnion, mem_setOf_eq]
    exact ⟨i, j, k, hij, hik, hjk, hB _ hi, hB' _ hj, hB'' _ hk⟩
  · refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
    by_cases hd : i ≠ j ∧ i ≠ k ∧ j ≠ k
    · refine measure_mono_null (t := {x | cross u (M (x i) - a) = 0 ∧
        cross u (M (x j) - a') = 0 ∧ cross u' (M (x k) - a'') = 0}) (fun x hx => hx.2.2.2) ?_
      exact h.null_two_one hat hu hd.1 hd.2.1 hd.2.2
    · refine measure_mono_null (fun x hx => hd ⟨hx.1, hx.2.1, hx.2.2.1⟩) measure_empty

/-- Both directions of the transfer for an affine relation `x_J = α + β x_I`, `β ≠ 0`. -/
lemma IsSlicedMix.rels (h : IsSlicedMix μ M c Q) {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (h1 : ∀ᵐ x ∂Q, cnt I x ≤ 1) (h2 : ∀ᵐ x ∂Q, cnt J x ≤ 1)
    (h3 : ∀ᵐ x ∂Q, (1 ≤ cnt I x ↔ 1 ≤ cnt J x)) {α β : ℝ} (hβ : β ≠ 0)
    (hrel : ∀ᵐ x ∂Q, ∀ i k, x i ∈ I → x k ∈ J → x k = α + β * x i) :
    (∀ B, MeasurableSet B → B ⊆ J → μ B = μ (I ∩ (fun t => α + β * t) ⁻¹' B)) ∧
    (∀ B, MeasurableSet B → B ⊆ I → μ B = μ (J ∩ (fun u => (u - α) / β) ⁻¹' B)) := by
  refine ⟨fun B hB hBJ => h.transfer hI h1 h2 h3 (by fun_prop) hrel hB hBJ,
    fun B hB hBI => h.transfer hJ h2 h1 (by filter_upwards [h3] with x hx using hx.symm)
      (by fun_prop) ?_ hB hBI⟩
  filter_upwards [hrel] with x hx
  intro k i hk hi
  rw [hx i k hi hk]
  field_simp
  ring

/-- If all three levels lie in a part on which `M` is affine, then `c` is the midpoint of the
mean level. -/
lemma three_in_part {l r s' : ℝ} {p v : ℝ × ℝ} (haff : ∀ s ∈ Ioo l r, M s = p + (s - s') • v)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Ioo l r) (hs : M (x 0) + M (x 1) + M (x 2) = (3 : ℝ) • c) :
    c ∈ M '' Ioo l r := by
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  refine ⟨(x 0 + x 1 + x 2) / 3, ⟨by linarith [h0.1, h1.1, h2.1], by
    linarith [h0.2, h1.2, h2.2]⟩, ?_⟩
  rw [haff _ ⟨by linarith [h0.1, h1.1, h2.1], by linarith [h0.2, h1.2, h2.2]⟩]
  rw [haff _ h0, haff _ h1, haff _ h2] at hs
  have e1 := congrArg Prod.fst hs
  have e2 := congrArg Prod.snd hs
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linarith
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linarith

end More

/-- Two directions at level `1` of a linear functional that are parallel are equal. -/
lemma eq_of_cross_eq_zero (lam : ℝ × ℝ →ₗ[ℝ] ℝ) {u v : ℝ × ℝ} (hu : lam u = 1) (hv : lam v = 1)
    (h : cross u v = 0) : u = v := by
  set l1 := lam (1, 0)
  set l2 := lam (0, 1)
  have hlam : ∀ p : ℝ × ℝ, lam p = p.1 * l1 + p.2 * l2 := fun p => by
    have : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  set w := v - u
  have e1 : l1 * w.1 + l2 * w.2 = 0 := by
    have := hlam w
    rw [show lam w = 0 by simp [w, hu, hv]] at this
    linarith
  have e2 : u.1 * w.2 - u.2 * w.1 = 0 := by
    have : cross u w = 0 := by simp only [w, cross_sub, h, cross_self, sub_self]
    simpa [cross] using this
  have hu' : u.1 * l1 + u.2 * l2 = 1 := by rw [← hlam, hu]
  have hw : w = 0 := Prod.ext (by
      rw [Prod.fst_zero]; linear_combination u.1 * e1 - l2 * e2 - w.1 * hu')
    (by rw [Prod.snd_zero]; linear_combination u.2 * e1 + l1 * e2 - w.2 * hu')
  exact (sub_eq_zero.1 hw).symm

/-! ### The general direction: three parts -/

/-- The setting of the third paragraph of the proof (a direction parallel to no side and no
diagonal). The levels `s₀ < s₁ < s₂ < s₃` of the four vertices cut the quadrilateral into a
triangle with apex `P₀ = M s₀`, a middle part and a triangle with apex `P₃ = M s₃`. The law `μ` of
the level has no atoms, lives on `[s₀, s₃]` and charges every subinterval; near the apices its
mass is quadratic (the density vanishes linearly there: `quad₀`, `quad₃`), and on the middle part
and a little beyond `s₂` the density is bounded below by `m > 0` (`lower`). The midpoint `M s` is
at level `s` and is affine on each part with the directions `v₀`, `v₁`, `v₂`; the segments are
`σⱼ = M '' [sⱼ, sⱼ₊₁]`. -/
structure Quad3 where
  (s₀ s₁ s₂ s₃ : ℝ)
  h01 : s₀ < s₁
  h12 : s₁ < s₂
  h23 : s₂ < s₃
  μ : Measure ℝ
  prob : IsProbabilityMeasure μ
  noAtoms : NullSingletonClass μ
  supp : μ (Icc s₀ s₃)ᶜ = 0
  pos : ∀ x y, s₀ ≤ x → x < y → y ≤ s₃ → 0 < μ (Ioo x y)
  C : ℝ
  quad₀ : ∀ ε, 0 < ε → μ (Ioo s₀ (s₀ + ε)) ≤ ENNReal.ofReal (C * ε ^ 2)
  quad₃ : ∀ ε, 0 < ε → μ (Ioo (s₃ - ε) s₃) ≤ ENNReal.ofReal (C * ε ^ 2)
  (m δ : ℝ)
  m_pos : 0 < m
  δ_pos : 0 < δ
  δ_le : s₂ + δ ≤ s₃
  lower : ∀ x y, s₁ ≤ x → x ≤ y → y ≤ s₂ + δ → ENNReal.ofReal (m * (y - x)) ≤ μ (Ioo x y)
  M : ℝ → ℝ × ℝ
  cont : Continuous M
  lam : ℝ × ℝ →ₗ[ℝ] ℝ
  lam_M : ∀ s, lam (M s) = s
  (v₀ v₁ v₂ : ℝ × ℝ)
  aff₀ : ∀ s ∈ Icc s₀ s₁, M s = M s₀ + (s - s₀) • v₀
  aff₁ : ∀ s ∈ Icc s₁ s₂, M s = M s₁ + (s - s₁) • v₁
  aff₂ : ∀ s ∈ Icc s₂ s₃, M s = M s₂ + (s - s₂) • v₂

namespace Quad3

variable (S : Quad3)

lemma lam_dir {M : ℝ → ℝ × ℝ} {lam : ℝ × ℝ →ₗ[ℝ] ℝ} (hlam : ∀ s, lam (M s) = s) {a b : ℝ}
    (hab : a < b) {v : ℝ × ℝ} (h : M b = M a + (b - a) • v) : lam v = 1 := by
  have := congrArg lam h
  rw [map_add, map_smul, hlam, hlam, smul_eq_mul] at this
  have h2 : (b - a) * (lam v - 1) = 0 := by linarith
  have := (mul_eq_zero.1 h2).resolve_left (by linarith)
  linarith

lemma lam_v₀ : S.lam S.v₀ = 1 := lam_dir S.lam_M S.h01 (S.aff₀ _ ⟨S.h01.le, le_rfl⟩)
lemma lam_v₁ : S.lam S.v₁ = 1 := lam_dir S.lam_M S.h12 (S.aff₁ _ ⟨S.h12.le, le_rfl⟩)
lemma lam_v₂ : S.lam S.v₂ = 1 := lam_dir S.lam_M S.h23 (S.aff₂ _ ⟨S.h23.le, le_rfl⟩)

/-- If `σ₀` and `σ₁` are collinear, the midpoints lie on two segments meeting at `M s₂`. -/
def toBent₀₁ (hv : S.v₀ = S.v₁) : Bent where
  a := S.s₀
  t := S.s₂
  b := S.s₃
  hat := S.h01.trans S.h12
  htb := S.h23
  μ := S.μ
  prob := S.prob
  noAtoms := S.noAtoms
  supp := S.supp
  pos := S.pos
  M := S.M
  cont := S.cont
  lam := S.lam
  lam_M := S.lam_M
  w₀ := S.v₁
  w₁ := S.v₂
  aff₀ := by
    intro s hs
    have e2 := S.aff₁ S.s₂ ⟨S.h12.le, le_rfl⟩
    rcases le_total s S.s₁ with h | h
    · rw [S.aff₀ s ⟨hs.1, h⟩, e2, S.aff₀ S.s₁ ⟨S.h01.le, le_rfl⟩, hv]; module
    · rw [S.aff₁ s ⟨h, hs.2⟩, e2]; module
  aff₁ := S.aff₂

/-- If `σ₁` and `σ₂` are collinear, the midpoints lie on two segments meeting at `M s₁`. -/
def toBent₁₂ (hv : S.v₁ = S.v₂) : Bent where
  a := S.s₀
  t := S.s₁
  b := S.s₃
  hat := S.h01
  htb := S.h12.trans S.h23
  μ := S.μ
  prob := S.prob
  noAtoms := S.noAtoms
  supp := S.supp
  pos := S.pos
  M := S.M
  cont := S.cont
  lam := S.lam
  lam_M := S.lam_M
  w₀ := S.v₀
  w₁ := S.v₁
  aff₀ := by
    intro s hs
    rw [S.aff₀ s hs, S.aff₀ S.s₁ ⟨S.h01.le, le_rfl⟩]; module
  aff₁ := by
    intro s hs
    rcases le_total s S.s₂ with h | h
    · exact S.aff₁ s ⟨hs.1, h⟩
    · rw [S.aff₂ s ⟨h, hs.2⟩, S.aff₁ S.s₂ ⟨S.h12.le, le_rfl⟩, hv]; module

/-- **Adjacent segments are not parallel** (unless all three are collinear): otherwise the
midpoints lie on two segments meeting at an angle, and `Bent.no_slicedMix` applies. -/
theorem cross₀₁_ne_zero (hnc : ¬ (S.v₀ = S.v₁ ∧ S.v₁ = S.v₂)) {c : ℝ × ℝ}
    {Q : Measure (Fin 3 → ℝ)} (h : IsSlicedMix S.μ S.M c Q) : cross S.v₀ S.v₁ ≠ 0 := by
  intro h0
  have e := eq_of_cross_eq_zero S.lam S.lam_v₀ S.lam_v₁ h0
  have h12 : cross S.v₁ S.v₂ ≠ 0 := fun h' =>
    hnc ⟨e, eq_of_cross_eq_zero S.lam S.lam_v₁ S.lam_v₂ h'⟩
  exact (S.toBent₀₁ e).no_slicedMix h12 c Q h

theorem cross₁₂_ne_zero (hnc : ¬ (S.v₀ = S.v₁ ∧ S.v₁ = S.v₂)) {c : ℝ × ℝ}
    {Q : Measure (Fin 3 → ℝ)} (h : IsSlicedMix S.μ S.M c Q) : cross S.v₁ S.v₂ ≠ 0 := by
  intro h0
  have e := eq_of_cross_eq_zero S.lam S.lam_v₁ S.lam_v₂ h0
  have h01 : cross S.v₀ S.v₁ ≠ 0 := fun h' =>
    hnc ⟨eq_of_cross_eq_zero S.lam S.lam_v₀ S.lam_v₁ h', e⟩
  exact (S.toBent₁₂ e).no_slicedMix h01 c Q h

/-! #### Basic facts in the three-part setting -/

lemma hat : ∀ q, S.μ (S.M ⁻¹' {q}) = 0 := by
  have := S.noAtoms; exact measure_preimage_singleton_eq_zero S.lam_M

lemma d01 : Disjoint (Ioo S.s₀ S.s₁) (Ioo S.s₁ S.s₂) :=
  Set.disjoint_left.2 fun s h0 h1 => by linarith [h0.2, h1.1]
lemma d02 : Disjoint (Ioo S.s₀ S.s₁) (Ioo S.s₂ S.s₃) :=
  Set.disjoint_left.2 fun s h0 h1 => by linarith [h0.2, h1.1, S.h12]
lemma d12 : Disjoint (Ioo S.s₁ S.s₂) (Ioo S.s₂ S.s₃) :=
  Set.disjoint_left.2 fun s h0 h1 => by linarith [h0.2, h1.1]

lemma cov : S.μ (Ioo S.s₀ S.s₁ ∪ Ioo S.s₁ S.s₂ ∪ Ioo S.s₂ S.s₃)ᶜ = 0 := by
  have := S.noAtoms
  refine ae_mem_of_supp S.supp {S.s₀, S.s₁, S.s₂, S.s₃} ?_
  intro s ⟨hs, hF⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
    not_or] at hF
  obtain ⟨n0, n1, n2, n3⟩ := hF
  rcases lt_or_gt_of_ne n1 with h1 | h1
  · exact Or.inl (Or.inl ⟨lt_of_le_of_ne hs.1 (Ne.symm n0), h1⟩)
  rcases lt_or_gt_of_ne n2 with h2 | h2
  · exact Or.inl (Or.inr ⟨h1, h2⟩)
  · exact Or.inr ⟨h2, lt_of_le_of_ne hs.2 n3⟩

lemma aff₀' : ∀ s ∈ Ioo S.s₀ S.s₁, S.M s = S.M S.s₀ + (s - S.s₀) • S.v₀ :=
  fun s hs => S.aff₀ s ⟨hs.1.le, hs.2.le⟩
lemma aff₁' : ∀ s ∈ Ioo S.s₁ S.s₂, S.M s = S.M S.s₁ + (s - S.s₁) • S.v₁ :=
  fun s hs => S.aff₁ s ⟨hs.1.le, hs.2.le⟩
lemma aff₂' : ∀ s ∈ Ioo S.s₂ S.s₃, S.M s = S.M S.s₂ + (s - S.s₂) • S.v₂ :=
  fun s hs => S.aff₂ s ⟨hs.1.le, hs.2.le⟩

lemma line_of_aff {M : ℝ → ℝ × ℝ} {I : Set ℝ} {p v : ℝ × ℝ} {s' : ℝ}
    (h : ∀ s ∈ I, M s = p + (s - s') • v) {u : ℝ × ℝ} (hu : cross u v = 0) :
    ∀ s ∈ I, cross u (M s - p) = 0 := fun s hs => by
  rw [h s hs, add_sub_cancel_left, cross_smul, hu, mul_zero]

lemma lam_mem {l r : ℝ} {c : ℝ × ℝ} (hc : c ∈ S.M '' Ioo l r) : S.lam c ∈ Ioo l r := by
  obtain ⟨s, hs, rfl⟩ := hc; rwa [S.lam_M]

lemma ae_tot {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)} (h : IsSlicedMix S.μ S.M c Q) :
    ∀ᵐ x ∂Q, cnt (Ioo S.s₀ S.s₁) x + cnt (Ioo S.s₁ S.s₂) x + cnt (Ioo S.s₂ S.s₃) x = 3 := by
  filter_upwards [h.ae_mem 0 S.cov, h.ae_mem 1 S.cov, h.ae_mem 2 S.cov] with x h0 h1 h2
  exact cnt_add_three S.d01 S.d02 S.d12 fun i => by fin_cases i <;> assumption

/-- The two linear equations for the positions of the three midpoints. -/
lemma sum_parts {c : ℝ × ℝ} {x : Fin 3 → ℝ}
    (hs : S.M (x 0) + S.M (x 1) + S.M (x 2) = (3 : ℝ) • c) {i k l : Fin 3}
    (hi : x i ∈ Ioo S.s₀ S.s₁) (hk : x k ∈ Ioo S.s₁ S.s₂) (hl : x l ∈ Ioo S.s₂ S.s₃) :
    (x i - S.s₀) • S.v₀ + (x k - S.s₁) • S.v₁ + (x l - S.s₂) • S.v₂ =
      (3 : ℝ) • c - S.M S.s₀ - S.M S.s₁ - S.M S.s₂ := by
  have hik : i ≠ k := fun e => Set.disjoint_left.1 S.d01 hi (e ▸ hk)
  have hil : i ≠ l := fun e => Set.disjoint_left.1 S.d02 hi (e ▸ hl)
  have hkl : k ≠ l := fun e => Set.disjoint_left.1 S.d12 hk (e ▸ hl)
  rw [sum_three_perm (fun t => S.M (x t)) hik hil hkl, S.aff₀' _ hi, S.aff₁' _ hk,
    S.aff₂' _ hl] at hs
  rw [← hs]; abel

lemma exists_three {x : Fin 3 → ℝ} (h0 : 1 ≤ cnt (Ioo S.s₀ S.s₁) x)
    (h1 : 1 ≤ cnt (Ioo S.s₁ S.s₂) x) (h2 : 1 ≤ cnt (Ioo S.s₂ S.s₃) x) :
    ∃ i k l, x i ∈ Ioo S.s₀ S.s₁ ∧ x k ∈ Ioo S.s₁ S.s₂ ∧ x l ∈ Ioo S.s₂ S.s₃ := by
  obtain ⟨i, hi⟩ := cnt_pos_iff.1 h0
  obtain ⟨k, hk⟩ := cnt_pos_iff.1 h1
  obtain ⟨l, hl⟩ := cnt_pos_iff.1 h2
  exact ⟨i, k, l, hi, hk, hl⟩

/-- **`c ∈ σ₁`** (the paper's `c ∈ σ₂`, the middle segment), when adjacent segments are not
parallel. -/
theorem mem_middle (h01 : cross S.v₀ S.v₁ ≠ 0) (h12 : cross S.v₁ S.v₂ ≠ 0) {c : ℝ × ℝ}
    {Q : Measure (Fin 3 → ℝ)} (h : IsSlicedMix S.μ S.M c Q) : c ∈ S.M '' Icc S.s₁ S.s₂ := by
  by_contra hc
  have := S.prob
  have := h.prob
  have h10 : cross S.v₁ S.v₀ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 h01
  have h21 : cross S.v₂ S.v₁ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 h12
  have l0 := line_of_aff S.aff₀' (cross_self S.v₀)
  have l1 := line_of_aff S.aff₁' (cross_self S.v₁)
  have l2 := line_of_aff S.aff₂' (cross_self S.v₂)
  have n01 := h.ae_not_two_one S.hat S.d01 h01 l0 l1
  have n10 := h.ae_not_two_one S.hat S.d01.symm h10 l1 l0
  have n12 := h.ae_not_two_one S.hat S.d12 h12 l1 l2
  have n21 := h.ae_not_two_one S.hat S.d12.symm h21 l2 l1
  have t1 : ∀ᵐ x ∂Q, cnt (Ioo S.s₁ S.s₂) x ≠ 3 := by
    filter_upwards [h.sum] with x hs h3
    exact hc (image_mono Ioo_subset_Icc_self (three_in_part S.aff₁' (cnt_three h3) hs))
  by_cases h02 : cross S.v₀ S.v₂ = 0
  · -- `σ₀ ∥ σ₂`: a triple meeting the middle part would have an atom there
    have l2' := line_of_aff S.aff₂' h02
    have n012 := h.ae_not_one_one_one S.hat S.d02 S.d01 S.d12.symm h01 l0 l2' l1
    have hz : ∀ᵐ x ∂Q, x 0 ∉ (Ioo S.s₁ S.s₂) := by
      filter_upwards [S.ae_tot h, n01, n10, n12, n21, t1, n012] with x ht a b c' d e f hx
      have : 1 ≤ cnt (Ioo S.s₁ S.s₂) x := cnt_pos_iff.2 ⟨0, hx⟩
      omega
    have hpos := S.pos S.s₁ S.s₂ S.h01.le S.h12 S.h23.le
    rw [← h.eq_mu 0 measurableSet_Ioo] at hpos
    exact hpos.ne' (by rw [ae_iff] at hz; simpa only [not_not] using hz)
  have h20 : cross S.v₂ S.v₀ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 h02
  have n02 := h.ae_not_two_one S.hat S.d02 h02 l0 l2
  have n20 := h.ae_not_two_one S.hat S.d02.symm h20 l2 l0
  set w := (3 : ℝ) • c - S.M S.s₀ - S.M S.s₁ - S.M S.s₂
  by_cases hl : S.lam c ∈ (Ioo S.s₀ S.s₁)
  · -- the triangle at `P₃` against the middle part
    have t2 : ∀ᵐ x ∂Q, cnt (Ioo S.s₂ S.s₃) x ≠ 3 := by
      filter_upwards [h.sum] with x hs h3
      have := S.lam_mem (three_in_part S.aff₂' (cnt_three h3) hs)
      exact Set.disjoint_left.1 S.d02 hl this
    have hall : ∀ᵐ x ∂Q, (1 ≤ cnt (Ioo S.s₁ S.s₂) x ∨ 1 ≤ cnt (Ioo S.s₂ S.s₃) x) →
        cnt (Ioo S.s₀ S.s₁) x = 1 ∧ cnt (Ioo S.s₁ S.s₂) x = 1 ∧ cnt (Ioo S.s₂ S.s₃) x = 1 := by
      filter_upwards [S.ae_tot h, n01, n10, n12, n21, n02, n20, t1, t2] with x ht a b c' d e f g k
      omega
    set k01 := cross S.v₀ S.v₁
    set k02 := cross S.v₀ S.v₂
    set α := S.s₁ + (cross S.v₀ w + S.s₂ * k02) / k01
    set β := -k02 / k01
    have hβ : β ≠ 0 := div_ne_zero (neg_ne_zero.2 h02) h01
    have hrel : ∀ᵐ x ∂Q, ∀ l k, x l ∈ (Ioo S.s₂ S.s₃) → x k ∈ (Ioo S.s₁ S.s₂) →
        x k = α + β * x l := by
      filter_upwards [hall, h.sum] with x hx hs
      intro l k hl' hk
      obtain ⟨i, -, -, hi, -, -⟩ := S.exists_three (by
          rw [(hx (Or.inl (cnt_pos_iff.2 ⟨k, hk⟩))).1]) (cnt_pos_iff.2 ⟨k, hk⟩)
        (cnt_pos_iff.2 ⟨l, hl'⟩)
      have e0 := S.sum_parts hs hi hk hl'
      have e : (x l - S.s₂) • S.v₂ + (x k - S.s₁) • S.v₁ + (x i - S.s₀) • S.v₀ = w := by
        simp only [w]; rw [← e0]; abel
      have e' := solve_coef e
      apply mul_right_cancel₀ h01
      rw [show (α + β * x l) * k01 = S.s₁ * k01 + cross S.v₀ w + S.s₂ * k02 - k02 * x l by
        simp only [α, β]; field_simp; ring]
      linear_combination e'
    obtain ⟨R1, R2⟩ := h.rels measurableSet_Ioo measurableSet_Ioo
      (by filter_upwards [hall, S.ae_tot h] with x hx ht; by_cases h1 : 1 ≤ cnt (Ioo S.s₂ S.s₃) x
          · exact (hx (Or.inr h1)).2.2.le
          · omega)
      (by filter_upwards [hall, S.ae_tot h] with x hx ht; by_cases h1 : 1 ≤ cnt (Ioo S.s₁ S.s₂) x
          · exact (hx (Or.inl h1)).2.1.le
          · omega)
      (by filter_upwards [hall] with x hx; constructor
          · intro h1; exact (hx (Or.inr h1)).2.1.ge
          · intro h1; exact (hx (Or.inl h1)).2.2.ge) hβ hrel
    have hlow₁ : ∀ ε, 0 < ε → ε ≤ S.s₂ - S.s₁ →
        ENNReal.ofReal (S.m * ε) ≤ S.μ (Ioo S.s₁ (S.s₁ + ε)) := fun ε hε hle => by
      have := S.lower S.s₁ (S.s₁ + ε) le_rfl (by linarith) (by linarith [S.δ_pos])
      simpa using this
    have hlow₂ : ∀ ε, 0 < ε → ε ≤ S.s₂ - S.s₁ →
        ENNReal.ofReal (S.m * ε) ≤ S.μ (Ioo (S.s₂ - ε) S.s₂) := fun ε hε hle => by
      have := S.lower (S.s₂ - ε) S.s₂ (by linarith) (by linarith) (by linarith [S.δ_pos])
      simpa using this
    have hd : 0 < S.s₂ - S.s₁ := by linarith [S.h12]
    rcases endpoints S.h23 S.h12 hβ (fun x y hx hxy hy => S.pos x y
        (by linarith [S.h01, S.h12]) hxy hy)
      (fun x y hx hxy hy => S.pos x y (by linarith [S.h01]) hxy (by linarith [S.h23]))
      R1 R2 with ⟨hp, -, hb⟩ | ⟨hn, -, hb⟩
    · exact apex_right_pos S.m_pos hp hb hd le_rfl R1 S.quad₃ hlow₂
    · exact apex_right_neg S.m_pos hn hb hd le_rfl R1 S.quad₃ hlow₁
  · -- the triangle at `P₀` against the middle part
    have t0 : ∀ᵐ x ∂Q, cnt (Ioo S.s₀ S.s₁) x ≠ 3 := by
      filter_upwards [h.sum] with x hs h3
      exact hl (S.lam_mem (three_in_part S.aff₀' (cnt_three h3) hs))
    have hall : ∀ᵐ x ∂Q, (1 ≤ cnt (Ioo S.s₀ S.s₁) x ∨ 1 ≤ cnt (Ioo S.s₁ S.s₂) x) →
        cnt (Ioo S.s₀ S.s₁) x = 1 ∧ cnt (Ioo S.s₁ S.s₂) x = 1 ∧ cnt (Ioo S.s₂ S.s₃) x = 1 := by
      filter_upwards [S.ae_tot h, n01, n10, n12, n21, n02, n20, t1, t0] with x ht a b c' d e f g k
      omega
    set k21 := cross S.v₂ S.v₁
    set k20 := cross S.v₂ S.v₀
    set α := S.s₁ + (cross S.v₂ w + S.s₀ * k20) / k21
    set β := -k20 / k21
    have hβ : β ≠ 0 := div_ne_zero (neg_ne_zero.2 h20) h21
    have hrel : ∀ᵐ x ∂Q, ∀ i k, x i ∈ (Ioo S.s₀ S.s₁) → x k ∈ (Ioo S.s₁ S.s₂) →
        x k = α + β * x i := by
      filter_upwards [hall, h.sum] with x hx hs
      intro i k hi hk
      obtain ⟨-, -, l, -, -, hl'⟩ := S.exists_three (cnt_pos_iff.2 ⟨i, hi⟩)
        (cnt_pos_iff.2 ⟨k, hk⟩) (by rw [(hx (Or.inl (cnt_pos_iff.2 ⟨i, hi⟩))).2.2])
      have e : (x i - S.s₀) • S.v₀ + (x k - S.s₁) • S.v₁ + (x l - S.s₂) • S.v₂ = w := by
        simp only [w]; exact S.sum_parts hs hi hk hl'
      have e' := solve_coef e
      apply mul_right_cancel₀ h21
      rw [show (α + β * x i) * k21 = S.s₁ * k21 + cross S.v₂ w + S.s₀ * k20 - k20 * x i by
        simp only [α, β]; field_simp; ring]
      linear_combination e'
    obtain ⟨R1, R2⟩ := h.rels measurableSet_Ioo measurableSet_Ioo
      (by filter_upwards [hall, S.ae_tot h] with x hx ht; by_cases h1 : 1 ≤ cnt (Ioo S.s₀ S.s₁) x
          · exact (hx (Or.inl h1)).1.le
          · omega)
      (by filter_upwards [hall, S.ae_tot h] with x hx ht; by_cases h1 : 1 ≤ cnt (Ioo S.s₁ S.s₂) x
          · exact (hx (Or.inr h1)).2.1.le
          · omega)
      (by filter_upwards [hall] with x hx; constructor
          · intro h1; exact (hx (Or.inl h1)).2.1.ge
          · intro h1; exact (hx (Or.inr h1)).1.ge) hβ hrel
    have hlow₁ : ∀ ε, 0 < ε → ε ≤ S.s₂ - S.s₁ →
        ENNReal.ofReal (S.m * ε) ≤ S.μ (Ioo S.s₁ (S.s₁ + ε)) := fun ε hε hle => by
      have := S.lower S.s₁ (S.s₁ + ε) le_rfl (by linarith) (by linarith [S.δ_pos])
      simpa using this
    have hlow₂ : ∀ ε, 0 < ε → ε ≤ S.s₂ - S.s₁ →
        ENNReal.ofReal (S.m * ε) ≤ S.μ (Ioo (S.s₂ - ε) S.s₂) := fun ε hε hle => by
      have := S.lower (S.s₂ - ε) S.s₂ (by linarith) (by linarith) (by linarith [S.δ_pos])
      simpa using this
    have hd : 0 < S.s₂ - S.s₁ := by linarith [S.h12]
    rcases endpoints S.h01 S.h12 hβ (fun x y hx hxy hy => S.pos x y hx hxy
        (by linarith [S.h12, S.h23]))
      (fun x y hx hxy hy => S.pos x y (by linarith [S.h01]) hxy (by linarith [S.h23]))
      R1 R2 with ⟨hp, ha, -⟩ | ⟨hn, ha, -⟩
    · exact apex_left_pos S.m_pos hp ha hd le_rfl R1 S.quad₀ hlow₁
    · exact apex_left_neg S.m_pos hn ha hd le_rfl R1 S.quad₀ hlow₂

/-- **Last part of Proposition 87.** If `c` is inside the middle segment and no two segments are
parallel, then the two triangles have equal mass (equal areas) and `3c - P₀ - P₃` lies on the
middle segment. -/
theorem equal_mass_and_point (h01 : cross S.v₀ S.v₁ ≠ 0) (h12 : cross S.v₁ S.v₂ ≠ 0)
    (h02 : cross S.v₀ S.v₂ ≠ 0) {c : ℝ × ℝ} (hc : c ∈ S.M '' Ioo S.s₁ S.s₂)
    {Q : Measure (Fin 3 → ℝ)} (h : IsSlicedMix S.μ S.M c Q) :
    S.μ (Ioo S.s₀ S.s₁) = S.μ (Ioo S.s₂ S.s₃) ∧
      (3 : ℝ) • c - S.M S.s₀ - S.M S.s₃ ∈ S.M '' Icc S.s₁ S.s₂ := by
  have := S.prob
  have := h.prob
  have h10 : cross S.v₁ S.v₀ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 h01
  have h21 : cross S.v₂ S.v₁ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 h12
  have h20 : cross S.v₂ S.v₀ ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.2 h02
  have l0 := line_of_aff S.aff₀' (cross_self S.v₀)
  have l1 := line_of_aff S.aff₁' (cross_self S.v₁)
  have l2 := line_of_aff S.aff₂' (cross_self S.v₂)
  have n01 := h.ae_not_two_one S.hat S.d01 h01 l0 l1
  have n10 := h.ae_not_two_one S.hat S.d01.symm h10 l1 l0
  have n12 := h.ae_not_two_one S.hat S.d12 h12 l1 l2
  have n21 := h.ae_not_two_one S.hat S.d12.symm h21 l2 l1
  have n02 := h.ae_not_two_one S.hat S.d02 h02 l0 l2
  have n20 := h.ae_not_two_one S.hat S.d02.symm h20 l2 l0
  have hl := S.lam_mem hc
  have t0 : ∀ᵐ x ∂Q, cnt (Ioo S.s₀ S.s₁) x ≠ 3 := by
    filter_upwards [h.sum] with x hs h3
    exact Set.disjoint_left.1 S.d01 (S.lam_mem (three_in_part S.aff₀' (cnt_three h3) hs)) hl
  have t2 : ∀ᵐ x ∂Q, cnt (Ioo S.s₂ S.s₃) x ≠ 3 := by
    filter_upwards [h.sum] with x hs h3
    exact Set.disjoint_left.1 S.d12 hl (S.lam_mem (three_in_part S.aff₂' (cnt_three h3) hs))
  have hall : ∀ᵐ x ∂Q, (1 ≤ cnt (Ioo S.s₀ S.s₁) x ∨ 1 ≤ cnt (Ioo S.s₂ S.s₃) x) →
      cnt (Ioo S.s₀ S.s₁) x = 1 ∧ cnt (Ioo S.s₁ S.s₂) x = 1 ∧ cnt (Ioo S.s₂ S.s₃) x = 1 := by
    filter_upwards [S.ae_tot h, n01, n10, n12, n21, n02, n20, t0, t2] with x ht a b c' d e f g k
    omega
  have hle0 : ∀ᵐ x ∂Q, cnt (Ioo S.s₀ S.s₁) x ≤ 1 := by
    filter_upwards [hall, S.ae_tot h] with x hx ht
    by_cases h1 : 1 ≤ cnt (Ioo S.s₀ S.s₁) x
    · exact (hx (Or.inl h1)).1.le
    · omega
  have hle2 : ∀ᵐ x ∂Q, cnt (Ioo S.s₂ S.s₃) x ≤ 1 := by
    filter_upwards [hall, S.ae_tot h] with x hx ht
    by_cases h1 : 1 ≤ cnt (Ioo S.s₂ S.s₃) x
    · exact (hx (Or.inr h1)).2.2.le
    · omega
  have hiff : ∀ᵐ x ∂Q, (1 ≤ cnt (Ioo S.s₀ S.s₁) x ↔ 1 ≤ cnt (Ioo S.s₂ S.s₃) x) := by
    filter_upwards [hall] with x hx
    constructor
    · intro h1; exact (hx (Or.inl h1)).2.2.ge
    · intro h1; exact (hx (Or.inr h1)).1.ge
  -- equal masses
  have hmass : S.μ (Ioo S.s₀ S.s₁) = S.μ (Ioo S.s₂ S.s₃) := by
    have e0 := h.measure_exists measurableSet_Ioo hle0
    have e2 := h.measure_exists measurableSet_Ioo hle2
    have heq : {x : Fin 3 → ℝ | ∃ i, x i ∈ Ioo S.s₀ S.s₁} =ᵐ[Q]
        {x | ∃ i, x i ∈ Ioo S.s₂ S.s₃} := by
      filter_upwards [hiff] with x hx
      show (∃ i, x i ∈ Ioo S.s₀ S.s₁) ↔ (∃ i, x i ∈ Ioo S.s₂ S.s₃)
      rw [← cnt_pos_iff, ← cnt_pos_iff]; exact hx
    rw [measure_congr heq, e2] at e0
    exact ((ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 e0).symm
  refine ⟨hmass, ?_⟩
  -- the affine relation between the two triangles
  set w := (3 : ℝ) • c - S.M S.s₀ - S.M S.s₁ - S.M S.s₂
  set k12 := cross S.v₁ S.v₂
  set k10 := cross S.v₁ S.v₀
  set α := S.s₂ + (cross S.v₁ w + S.s₀ * k10) / k12
  set β := -k10 / k12
  have hβ : β ≠ 0 := div_ne_zero (neg_ne_zero.2 h10) h12
  have hrel : ∀ᵐ x ∂Q, ∀ i l, x i ∈ Ioo S.s₀ S.s₁ → x l ∈ Ioo S.s₂ S.s₃ →
      x l = α + β * x i := by
    filter_upwards [hall, h.sum] with x hx hs
    intro i l hi hl'
    obtain ⟨-, k, -, -, hk, -⟩ := S.exists_three (cnt_pos_iff.2 ⟨i, hi⟩)
      (by rw [(hx (Or.inl (cnt_pos_iff.2 ⟨i, hi⟩))).2.1]) (cnt_pos_iff.2 ⟨l, hl'⟩)
    have e : (x i - S.s₀) • S.v₀ + (x l - S.s₂) • S.v₂ + (x k - S.s₁) • S.v₁ = w := by
      simp only [w]; rw [← S.sum_parts hs hi hk hl']; abel
    have e' := solve_coef e
    apply mul_right_cancel₀ h12
    rw [show (α + β * x i) * k12 = S.s₂ * k12 + cross S.v₁ w + S.s₀ * k10 - k10 * x i by
      simp only [α, β]; field_simp; ring]
    linear_combination e'
  obtain ⟨R1, R2⟩ := h.rels measurableSet_Ioo measurableSet_Ioo hle0 hle2 hiff hβ hrel
  have hlow : ∀ ε, 0 < ε → ε ≤ S.δ →
      ENNReal.ofReal (S.m * ε) ≤ S.μ (Ioo S.s₂ (S.s₂ + ε)) := fun ε hε hle => by
    have := S.lower S.s₂ (S.s₂ + ε) S.h12.le (by linarith) (by linarith)
    simpa using this
  have hφ : α + β * S.s₀ = S.s₃ := by
    rcases endpoints S.h01 S.h23 hβ (fun x y hx hxy hy => S.pos x y hx hxy
        (by linarith [S.h12, S.h23]))
      (fun x y hx hxy hy => S.pos x y (by linarith [S.h01, S.h12]) hxy hy)
      R1 R2 with ⟨hp, ha, -⟩ | ⟨-, ha, -⟩
    · exact (apex_left_pos S.m_pos hp ha S.δ_pos (by linarith [S.δ_le]) R1 S.quad₀
        hlow).elim
    · exact ha
  -- the closure argument
  set G : ℝ → ℝ × ℝ := fun t =>
    (3 : ℝ) • c - (S.M S.s₀ + (t - S.s₀) • S.v₀) - (S.M S.s₂ + ((α + β * t) - S.s₂) • S.v₂)
  have hG : Continuous G := by fun_prop
  have hT : IsClosed {t | G t ∈ S.M '' Icc S.s₁ S.s₂} :=
    (isCompact_Icc.image S.cont).isClosed.preimage hG
  have hgood : ∀ᵐ x ∂Q, ∀ i, x i ∈ Ioo S.s₀ S.s₁ → G (x i) ∈ S.M '' Icc S.s₁ S.s₂ := by
    filter_upwards [hall, h.sum, hrel] with x hx hs hr
    intro i hi
    obtain ⟨-, k, l, -, hk, hl'⟩ := S.exists_three (cnt_pos_iff.2 ⟨i, hi⟩)
      (by rw [(hx (Or.inl (cnt_pos_iff.2 ⟨i, hi⟩))).2.1])
      (by rw [(hx (Or.inl (cnt_pos_iff.2 ⟨i, hi⟩))).2.2])
    refine ⟨x k, Ioo_subset_Icc_self hk, ?_⟩
    have e := S.sum_parts hs hi hk hl'
    simp only [G, ← hr i l hi hl']
    rw [S.aff₁' _ hk]
    rw [← sub_eq_zero] at e ⊢
    rw [← e]; abel
  have hmem : S.s₀ ∈ closure {t | G t ∈ S.M '' Icc S.s₁ S.s₂} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set ε' := min ε (S.s₁ - S.s₀)
    have hε' : 0 < ε' := lt_min hε (by linarith [S.h01])
    have hε'1 : ε' ≤ S.s₁ - S.s₀ := min_le_right _ _
    have hε'2 : ε' ≤ ε := min_le_left _ _
    have hsub : Ioo S.s₀ (S.s₀ + ε') ⊆ Ioo S.s₀ S.s₁ :=
      Ioo_subset_Ioo le_rfl (by linarith [hε'1])
    have hpos : 0 < Q {x | ∃ i, x i ∈ Ioo S.s₀ (S.s₀ + ε')} := by
      rw [h.measure_exists measurableSet_Ioo (by
        filter_upwards [hle0] with x hx using (cnt_mono hsub x).trans hx)]
      exact ENNReal.mul_pos (by norm_num) (S.pos _ _ le_rfl (by linarith)
        (by linarith [hε'1, S.h12, S.h23])).ne'
    by_contra hno
    push Not at hno
    rw [ae_iff] at hgood
    refine hpos.ne' (measure_mono_null (t := {x | ¬ ∀ i, x i ∈ Ioo S.s₀ S.s₁ →
      G (x i) ∈ S.M '' Icc S.s₁ S.s₂}) (fun x ⟨i, hi⟩ hx => ?_) hgood)
    have := hno (x i) (hx i (hsub hi))
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hi.1])] at this
    linarith [hi.2, hε'2]
  have := hT.closure_subset hmem
  simp only [mem_setOf_eq, G, hφ] at this
  rwa [← S.aff₂ S.s₃ ⟨S.h23.le, le_rfl⟩, sub_self, zero_smul, add_zero] at this

/-- **Proposition 87** (`st:prop:quad`), measure-theoretic content, in the general direction.
Let the midpoints of the chords lie on three segments `σ₀, σ₁, σ₂` (the paper's
`σ₁, σ₂, σ₃`), not all on one line, in the setting `Quad3`, and suppose that there is a sliced
`3`-complete mix (`IsSlicedMix`). Then adjacent segments are not parallel, `c ∈ σ₁` (the middle
segment), and if moreover `c` is not an endpoint of `σ₁` and `σ₀ ∦ σ₂`, the two triangles have
equal mass, that is equal areas, and `3c - P₀ - P₃ ∈ σ₁`. -/
theorem prop87 (hnc : ¬ (S.v₀ = S.v₁ ∧ S.v₁ = S.v₂)) {c : ℝ × ℝ} {Q : Measure (Fin 3 → ℝ)}
    (h : IsSlicedMix S.μ S.M c Q) :
    cross S.v₀ S.v₁ ≠ 0 ∧ cross S.v₁ S.v₂ ≠ 0 ∧ c ∈ S.M '' Icc S.s₁ S.s₂ ∧
      (c ∈ S.M '' Ioo S.s₁ S.s₂ → cross S.v₀ S.v₂ ≠ 0 →
        S.μ (Ioo S.s₀ S.s₁) = S.μ (Ioo S.s₂ S.s₃) ∧
          (3 : ℝ) • c - S.M S.s₀ - S.M S.s₃ ∈ S.M '' Icc S.s₁ S.s₂) := by
  have h01 := S.cross₀₁_ne_zero hnc h
  have h12 := S.cross₁₂_ne_zero hnc h
  exact ⟨h01, h12, S.mem_middle h01 h12 h, fun hc h02 => S.equal_mass_and_point h01 h12 h02 hc h⟩

end Quad3

/-! ### The level law from a chord-length density -/

section Density

variable {f : ℝ → ℝ} {s₀ s₃ : ℝ}

/-- The law of the level when its density is `f` on `[s₀, s₃]` (for a uniform point of a
planar body, `f` is the chord length divided by the area). -/
def levelLaw (f : ℝ → ℝ) (s₀ s₃ : ℝ) : Measure ℝ :=
  (volume.restrict (Icc s₀ s₃)).withDensity fun s => ENNReal.ofReal (f s)

lemma levelLaw_apply {S : Set ℝ} (hS : MeasurableSet S) :
    levelLaw f s₀ s₃ S = ∫⁻ s in S ∩ Icc s₀ s₃, ENNReal.ofReal (f s) := by
  rw [levelLaw, withDensity_apply _ hS, Measure.restrict_restrict hS]

lemma levelLaw_supp : levelLaw f s₀ s₃ (Icc s₀ s₃)ᶜ = 0 := by
  rw [levelLaw_apply measurableSet_Icc.compl, compl_inter_self, Measure.restrict_empty,
    lintegral_zero_measure]

instance levelLaw_nullSingleton : NullSingletonClass (levelLaw f s₀ s₃) where
  measure_singleton x := by
    rw [levelLaw_apply (measurableSet_singleton x)]
    exact setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_left
      (measure_singleton x))

lemma levelLaw_Ioo {x y : ℝ} (hx : s₀ ≤ x) (hy : y ≤ s₃) :
    levelLaw f s₀ s₃ (Ioo x y) = ∫⁻ s in Ioo x y, ENNReal.ofReal (f s) := by
  rw [levelLaw_apply measurableSet_Ioo,
    inter_eq_left.2 ((Ioo_subset_Ioo hx hy).trans Ioo_subset_Icc_self)]

/-- A density positive inside `(s₀, s₃)` charges every subinterval. -/
lemma levelLaw_pos (hf : Measurable f) (hpos : ∀ s ∈ Ioo s₀ s₃, 0 < f s) {x y : ℝ}
    (hx : s₀ ≤ x) (hxy : x < y) (hy : y ≤ s₃) : 0 < levelLaw f s₀ s₃ (Ioo x y) := by
  rw [levelLaw_Ioo hx hy, setLIntegral_pos_iff hf.ennreal_ofReal]
  have : Function.support (fun s => ENNReal.ofReal (f s)) ∩ Ioo x y = Ioo x y :=
    inter_eq_right.2 fun s hs => by
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hpos s ⟨hx.trans_lt hs.1, hs.2.trans_le hy⟩
  rw [this, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

/-- A density bounded by `K (s - s₀)` (vanishing linearly at the apex `s₀`) gives mass at most
`K ε²` near `s₀`. -/
lemma levelLaw_quad₀ (hK : 0 ≤ K) (hq : ∀ s ∈ Icc s₀ s₃, f s ≤ K * (s - s₀))
    {ε : ℝ} (hε : 0 < ε) :
    levelLaw f s₀ s₃ (Ioo s₀ (s₀ + ε)) ≤ ENNReal.ofReal (K * ε ^ 2) := by
  rw [levelLaw_apply measurableSet_Ioo]
  calc ∫⁻ s in Ioo s₀ (s₀ + ε) ∩ Icc s₀ s₃, ENNReal.ofReal (f s)
      ≤ ∫⁻ _ in Ioo s₀ (s₀ + ε) ∩ Icc s₀ s₃, ENNReal.ofReal (K * ε) :=
        setLIntegral_mono measurable_const fun s hs => ENNReal.ofReal_le_ofReal (by
          have := hq s hs.2
          nlinarith [hs.1.2])
    _ ≤ ∫⁻ _ in Ioo s₀ (s₀ + ε), ENNReal.ofReal (K * ε) := lintegral_mono_set inter_subset_left
    _ = ENNReal.ofReal (K * ε ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul' (by linarith)]
        ring_nf

lemma levelLaw_quad₃ (hK : 0 ≤ K) (hq : ∀ s ∈ Icc s₀ s₃, f s ≤ K * (s₃ - s))
    {ε : ℝ} (hε : 0 < ε) :
    levelLaw f s₀ s₃ (Ioo (s₃ - ε) s₃) ≤ ENNReal.ofReal (K * ε ^ 2) := by
  rw [levelLaw_apply measurableSet_Ioo]
  calc ∫⁻ s in Ioo (s₃ - ε) s₃ ∩ Icc s₀ s₃, ENNReal.ofReal (f s)
      ≤ ∫⁻ _ in Ioo (s₃ - ε) s₃ ∩ Icc s₀ s₃, ENNReal.ofReal (K * ε) :=
        setLIntegral_mono measurable_const fun s hs => ENNReal.ofReal_le_ofReal (by
          have := hq s hs.2
          nlinarith [hs.1.1])
    _ ≤ ∫⁻ _ in Ioo (s₃ - ε) s₃, ENNReal.ofReal (K * ε) := lintegral_mono_set inter_subset_left
    _ = ENNReal.ofReal (K * ε ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul' (by linarith)]
        ring_nf

/-- A density bounded below by `m` on `[a, b] ⊆ [s₀, s₃]` gives the linear lower bound. -/
lemma levelLaw_lower {a b m : ℝ} (ha : s₀ ≤ a) (hb : b ≤ s₃) (hlow : ∀ s ∈ Icc a b, m ≤ f s)
    {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    ENNReal.ofReal (m * (y - x)) ≤ levelLaw f s₀ s₃ (Ioo x y) := by
  rw [levelLaw_Ioo (ha.trans hx) (hy.trans hb)]
  calc ENNReal.ofReal (m * (y - x)) ≤ ∫⁻ _ in Ioo x y, ENNReal.ofReal m := by
        rw [setLIntegral_const, Real.volume_Ioo]
        rcases le_total 0 m with hm | hm
        · rw [ENNReal.ofReal_mul hm]
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith)]; simp
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo fun s hs =>
        ENNReal.ofReal_le_ofReal (hlow s ⟨hx.trans hs.1.le, hs.2.le.trans hy⟩)

end Density

/-! ### Elementary geometry of the excluded directions -/

/-- **Chords parallel to a side.** In affine coordinates with `A = (0, 0)`, `B = (1, 0)` and the
level the second coordinate, let `C = (c₁, c₂)` and `D = (d₁, d₂)` with `0 < d₂ < c₂`. The midpoints
run from the midpoint `(1/2, 0)` of `AB` to the midpoint `m` of the chord through `D` (from `D` to
the point of `BC` at level `d₂`) and on to `C`. This path is straight iff `D` lies on the line
`AC`; so for a convex quadrilateral (no three vertices collinear) it is bent, and if `C` and `D`
are at the same level, `CD ∥ AB` and `K` is a trapezoid. -/
theorem side_path_straight_iff {c₁ c₂ d₁ d₂ : ℝ} (hc : 0 < c₂) :
    let m : ℝ × ℝ := ((d₁ + (1 + d₂ / c₂ * (c₁ - 1))) / 2, d₂)
    cross (m - (1 / 2, 0)) ((c₁, c₂) - (1 / 2, 0)) = 0 ↔ cross (c₁, c₂) (d₁, d₂) = 0 := by
  intro m
  have key : cross (m - (1 / 2, 0)) ((c₁, c₂) - (1 / 2, 0)) = -cross (c₁, c₂) (d₁, d₂) / 2 := by
    simp only [m, cross, Prod.fst_sub, Prod.snd_sub]
    field_simp
    ring
  rw [key]
  constructor <;> intro h <;> linarith

/-- **Chords parallel to a diagonal.** In the triangle `ABC`, the chords parallel to `AC` at
the fraction `θ ∈ [0, 1]` of the way from `B` have the endpoints `B + θ(A - B)` and
`B + θ(C - B)`, so their midpoints `B + θ(m_AC - B)` run straight from `B` to the midpoint of
`AC`; the whole path `B → m_AC → D` is straight iff `m_AC` lies on the line `BD`, that is iff
`BD` bisects `AC`. -/
theorem diagonal_midpoint (A B C : ℝ × ℝ) (θ : ℝ) :
    (1 / 2 : ℝ) • ((B + θ • (A - B)) + (B + θ • (C - B))) =
      B + θ • ((1 / 2 : ℝ) • (A + C) - B) := by
  ext <;> simp <;> ring

/-! ### From a sliced complete mix of a planar body to `IsSlicedMix`

The body between two continuous graphs `L ≤ R` over `[a, b]`, in chord coordinates (the level
is the first coordinate, the chords are vertical). Fubini gives the law of the level
(`map_fst_unifSet_body`); `IsSliced` formalises "given the levels, each point is uniformly
distributed on its chord" by a kernel identity; and `isSlicedMix_of_sliced` is the conditional
expectation step `M₁ + M₂ + M₃ = 3c`. -/

section Body

variable {a b : ℝ} {L R : ℝ → ℝ}

/-- The planar body between the graphs of `L ≤ R` over `[a, b]`, in chord coordinates: the
first coordinate is the level, and the chords `{s} × [L s, R s]` are vertical. -/
def body (a b : ℝ) (L R : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc a b ∧ L x.1 ≤ x.2 ∧ x.2 ≤ R x.1}

lemma body_eq (a b : ℝ) (L R : ℝ → ℝ) : body a b L R =
    Prod.fst ⁻¹' Icc a b ∩ {x | L x.1 ≤ x.2} ∩ {x | x.2 ≤ R x.1} := by
  ext x; simp only [body, mem_ofPred_eq, mem_inter_iff, mem_preimage, and_assoc]

lemma isClosed_body (hL : Continuous L) (hR : Continuous R) : IsClosed (body a b L R) := by
  rw [body_eq]
  exact ((isClosed_Icc.preimage continuous_fst).inter
    (isClosed_le (hL.comp continuous_fst) continuous_snd)).inter
    (isClosed_le continuous_snd (hR.comp continuous_fst))

lemma isCompact_body (hL : Continuous L) (hR : Continuous R) : IsCompact (body a b L R) := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hL.continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hR.continuousOn
  refine (isCompact_Icc.prod (isCompact_Icc (a := -(C₁ + C₂)) (b := C₁ + C₂))).of_isClosed_subset
    (isClosed_body hL hR) fun x hx => ⟨hx.1, ?_, ?_⟩
  · have h1 := hC₁ _ hx.1; have h2 := hC₂ _ hx.1
    rw [Real.norm_eq_abs, abs_le] at h1 h2
    have := norm_nonneg (R x.1); linarith [hx.2.1]
  · have h1 := hC₁ _ hx.1; have h2 := hC₂ _ hx.1
    rw [Real.norm_eq_abs, abs_le] at h1 h2
    have := norm_nonneg (L x.1); linarith [hx.2.2]

lemma slice_body_of_mem {S : Set ℝ} {s : ℝ} (hs : s ∈ S ∩ Icc a b) :
    Prod.mk s ⁻¹' (body a b L R ∩ Prod.fst ⁻¹' S) = Icc (L s) (R s) := by
  ext y
  simp only [body, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_Icc]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨hs.2, h⟩, hs.1⟩⟩

lemma slice_body_of_notMem {S : Set ℝ} {s : ℝ} (hs : s ∉ S ∩ Icc a b) :
    Prod.mk s ⁻¹' (body a b L R ∩ Prod.fst ⁻¹' S) = ∅ := by
  ext y
  simp only [body, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, -⟩, h2⟩; exact hs ⟨h2, h1⟩

/-- **Fubini.** The area of the part of the body over `S` is `∫_{S ∩ [a,b]} (R - L)`. -/
lemma volume_body_inter (hL : Continuous L) (hR : Continuous R) {S : Set ℝ}
    (hS : MeasurableSet S) :
    volume (body a b L R ∩ Prod.fst ⁻¹' S) =
      ∫⁻ s in S ∩ Icc a b, ENNReal.ofReal (R s - L s) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply
    ((isClosed_body hL hR).measurableSet.inter (measurable_fst hS)),
    ← lintegral_indicator (hS.inter measurableSet_Icc)]
  congr 1; funext s
  by_cases hs : s ∈ S ∩ Icc a b
  · rw [slice_body_of_mem hs, indicator_of_mem hs, Real.volume_Icc]
  · rw [slice_body_of_notMem hs, indicator_of_notMem hs, measure_empty]

/-- The area of the body. -/
def area (a b : ℝ) (L R : ℝ → ℝ) : ℝ := ∫ s in Icc a b, (R s - L s)

lemma volume_body (hL : Continuous L) (hR : Continuous R) (hLR : ∀ s ∈ Icc a b, L s ≤ R s) :
    volume (body a b L R) = ENNReal.ofReal (area a b L R) := by
  have := volume_body_inter (a := a) (b := b) hL hR MeasurableSet.univ
  rw [preimage_univ, inter_univ, univ_inter] at this
  rw [this, area, ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun s => R s - L s).continuousOn.integrableOn_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => by
      simp only [Pi.zero_apply]; linarith [hLR s hs]))]

lemma area_pos (hab : a < b) (hL : Continuous L) (hR : Continuous R)
    (hpos : ∀ s ∈ Ioo a b, L s < R s) : 0 < area a b L R := by
  rw [area, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hR.sub hL).intervalIntegrable _ _) (fun s hs => sub_pos.2 (hpos s hs)) hab

lemma unifSet_body_isProb (hab : a < b) (hL : Continuous L) (hR : Continuous R)
    (hLR : ∀ s ∈ Icc a b, L s ≤ R s) (hpos : ∀ s ∈ Ioo a b, L s < R s) :
    IsProbabilityMeasure (unifSet (body a b L R)) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul, volume_body hL hR hLR]
  exact ENNReal.inv_mul_cancel (by simpa using area_pos hab hL hR hpos) ENNReal.ofReal_ne_top

/-- **The law of the level.** The first coordinate of a uniform point of the body has the
density `(R - L)/area` on `[a, b]` (chord length over area). -/
lemma map_fst_unifSet_body (hL : Continuous L) (hR : Continuous R)
    (hLR : ∀ s ∈ Icc a b, L s ≤ R s) (hA : 0 < area a b L R) :
    (unifSet (body a b L R)).map Prod.fst =
      levelLaw (fun s => (R s - L s) / area a b L R) a b := by
  ext S hS
  rw [Measure.map_apply measurable_fst hS, levelLaw_apply hS, unifSet, smul_apply,
    Measure.restrict_apply (measurable_fst hS), inter_comm, volume_body_inter hL hR hS,
    volume_body hL hR hLR, smul_eq_mul, ← lintegral_const_mul' _ _ (by simp [hA])]
  refine setLIntegral_congr_fun (hS.inter measurableSet_Icc) fun s hs => ?_
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hA.le), ENNReal.ofReal_inv_of_pos hA]

end Body

section SlicedDef

open ProbabilityTheory

variable {a b : ℝ} {L R : ℝ → ℝ}

/-- The uniform distribution on `[0, 1]`. -/
def unit01 : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unit01 :=
  ⟨by simp [unit01, Measure.restrict_apply MeasurableSet.univ]⟩

/-- The point at the fraction `t` of the chord `{s} × [L s, R s]`. -/
def chordPt (L R : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, L p.1 + p.2 * (R p.1 - L p.1))

/-- The kernel `s ↦ U({s} × [L s, R s])`: the uniform distribution on the chord at level `s`. -/
def chordKernel (L R : ℝ → ℝ) : Kernel ℝ (ℝ × ℝ) :=
  (Kernel.deterministic id measurable_id ×ₖ Kernel.const ℝ unit01).map (chordPt L R)

lemma chordKernel_apply (hL : Continuous L) (hR : Continuous R) (s : ℝ) :
    chordKernel L R s = unit01.map fun t => (s, L s + t * (R s - L s)) := by
  rw [chordKernel, Kernel.map_apply _ (by unfold chordPt; fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by unfold chordPt; fun_prop) measurable_prodMk_left]
  rfl

/-- The midpoint of the chord at level `s`. -/
def mid (L R : ℝ → ℝ) (s : ℝ) : ℝ × ℝ := (s, (L s + R s) / 2)

lemma continuous_mid (hL : Continuous L) (hR : Continuous R) : Continuous (mid L R) := by
  unfold mid; fun_prop

lemma integral_unit01_id : ∫ t, t ∂unit01 = 1 / 2 := by
  rw [unit01, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_id]; norm_num

/-- The mean of the uniform distribution on a chord is its midpoint. -/
lemma integral_chordKernel (hL : Continuous L) (hR : Continuous R) (s : ℝ) :
    ∫ z, z ∂(chordKernel L R s) = mid L R s := by
  have hi : Integrable (fun t : ℝ => t) unit01 :=
    continuous_id.continuousOn.integrableOn_Icc
  have e := integral_map (μ := unit01) (φ := fun t => (s, L s + t * (R s - L s)))
    (by fun_prop) (f := id) aestronglyMeasurable_id
  simp only [id] at e
  rw [chordKernel_apply hL hR, e,
    integral_pair (μ := unit01) (f := fun _ => s) (g := fun t => L s + t * (R s - L s))
      (integrable_const _)
      ((by fun_prop : Continuous fun t : ℝ => L s + t * (R s - L s)).continuousOn.integrableOn_Icc)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_add (integrable_const _) (hi.mul_const _), integral_const, integral_mul_const,
    integral_unit01_id, mid]
  simp only [probReal_univ, one_smul, Prod.mk.injEq, true_and]; ring

/-- The levels of a triple of points. -/
def lev3 (x : Fin 3 → ℝ × ℝ) : Fin 3 → ℝ := fun i => (x i).1

lemma measurable_lev3 : Measurable lev3 := by unfold lev3; fun_prop

/-- **Sliced triples** (Section 21): given the levels `S = (S₁, S₂, S₃)` of its points, each
`Xᵢ` is uniformly distributed on its chord; that is, the joint law of `(S, Xᵢ)` is the law of
`S` composed with the kernel `S ↦ U(chord at level Sᵢ)`. -/
def IsSliced (L R : ℝ → ℝ) (P : Measure (Fin 3 → ℝ × ℝ)) : Prop :=
  ∀ i : Fin 3, P.map (fun x => (lev3 x, x i)) =
    (P.map lev3) ⊗ₘ ((chordKernel L R).comap (fun s : Fin 3 → ℝ => s i) (measurable_pi_apply i))

/-- **Conditional expectation step of Proposition 87.** Let `P` be a `3`-complete mix of
`U(K)` for the body `K` between `L ≤ R` over `[a, b]`, sliced in the direction of the chords.
Then the levels form a sliced mix in the sense of `IsSlicedMix`: their law `Q` has the marginals
of the level and `M(S₁) + M(S₂) + M(S₃) = 3c` almost surely, `M` the chord midpoint and `c` the
centroid. (Proof: `E[1_B(S) Xᵢ] = E[1_B(S) M(Sᵢ)]` for every Borel `B`, by the kernel identity;
summing over `i` and using `X₁ + X₂ + X₃ = 3c` gives `∫_B (∑ M(Sᵢ) - 3c) dQ = 0`.) -/
theorem isSlicedMix_of_sliced (hab : a < b) (hL : Continuous L) (hR : Continuous R)
    (hLR : ∀ s ∈ Icc a b, L s ≤ R s) (hpos : ∀ s ∈ Ioo a b, L s < R s)
    {P : Measure (Fin 3 → ℝ × ℝ)} (hP : IsCompleteMix 3 (unifSet (body a b L R)) P)
    (hsl : IsSliced L R P) :
    IsSlicedMix ((unifSet (body a b L R)).map Prod.fst) (mid L R)
      (∫ x, x ∂(unifSet (body a b L R))) (P.map lev3) := by
  set K := body a b L R
  set F := unifSet K
  set c := ∫ x, x ∂F
  set Q := P.map lev3
  obtain ⟨hPprob, ⟨s₀, hsum⟩, hmarg⟩ := hP
  have hK : IsCompact K := isCompact_body hL hR
  have hFp : IsProbabilityMeasure F := unifSet_body_isProb hab hL hR hLR hpos
  have hQp : IsProbabilityMeasure Q := inferInstance
  -- integrability
  have hvK : volume K ≠ 0 := by
    rw [volume_body hL hR hLR]; simpa using area_pos hab hL hR hpos
  have hcontInt : ∀ {f : ℝ × ℝ → ℝ × ℝ}, Continuous f → Integrable f F := fun hf =>
    (hf.continuousOn.integrableOn_compact hK).smul_measure (ENNReal.inv_ne_top.2 hvK)
  have hXi : ∀ i : Fin 3, Integrable (fun x : Fin 3 → ℝ × ℝ => x i) P := by
    intro i
    have := (integrable_map_measure (μ := P) (f := fun x => x i) (g := id)
      aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).1
    rw [hmarg i] at this
    exact this (hcontInt continuous_id)
  have hEXi : ∀ i : Fin 3, ∫ x, x i ∂P = c := by
    intro i
    have e := integral_map (μ := P) (φ := fun x => x i) (measurable_pi_apply i).aemeasurable
      (f := id) aestronglyMeasurable_id
    simp only [id] at e
    rw [← e, hmarg i]
  have hs₀ : s₀ = (3 : ℝ) • c := by
    have e1 : ∫ x, ∑ j, x j ∂P = s₀ := by
      rw [integral_congr_ae hsum, integral_const, probReal_univ, one_smul]
    rw [← e1]
    simp only [Fin.sum_univ_three]
    rw [integral_add (f := fun x => x 0 + x 1) ((hXi 0).add (hXi 1)) (hXi 2),
      integral_add (hXi 0) (hXi 1), hEXi, hEXi, hEXi]
    module
  have hsum' : ∀ᵐ x ∂P, x 0 + x 1 + x 2 = (3 : ℝ) • c := by
    filter_upwards [hsum] with x hx; rw [← hs₀, ← hx, Fin.sum_univ_three]
  -- the marginals of the levels
  have hQi : ∀ i : Fin 3, Q.map (fun s => s i) = F.map Prod.fst := by
    intro i
    have hm := hmarg i
    simp only at hm
    rw [Measure.map_map (measurable_pi_apply i) measurable_lev3, ← hm,
      Measure.map_map measurable_fst (measurable_pi_apply i)]
    rfl
  have hMi : ∀ i : Fin 3, Integrable (fun s : Fin 3 → ℝ => mid L R (s i)) Q := by
    intro i
    have h1 := (integrable_map_measure (μ := Q) (f := fun s => s i) (g := mid L R)
      (continuous_mid hL hR).aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1
    have h2 := (integrable_map_measure (μ := F) (f := Prod.fst) (g := mid L R)
      (continuous_mid hL hR).aestronglyMeasurable measurable_fst.aemeasurable).2
      (hcontInt ((continuous_mid hL hR).comp continuous_fst))
    rw [hQi i] at h1
    exact h1 h2
  -- the key identity
  have key : ∀ i : Fin 3, ∀ B : Set (Fin 3 → ℝ), MeasurableSet B →
      ∫ x, (lev3 ⁻¹' B).indicator (fun x => x i) x ∂P = ∫ s in B, mid L R (s i) ∂Q := by
    intro i B hB
    set G : (Fin 3 → ℝ × ℝ) → (Fin 3 → ℝ) × (ℝ × ℝ) := fun x => (lev3 x, x i)
    have hG : Measurable G := measurable_lev3.prodMk (measurable_pi_apply i)
    set Φ : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ × ℝ :=
      Set.indicator (B ×ˢ (univ : Set (ℝ × ℝ))) fun p => p.2
    have hΦm : Measurable Φ := measurable_snd.indicator (hB.prod MeasurableSet.univ)
    have hΦG : (fun x => Φ (G x)) = (lev3 ⁻¹' B).indicator (fun x => x i) := by
      funext x
      by_cases hx : lev3 x ∈ B
      · rw [indicator_of_mem (show x ∈ lev3 ⁻¹' B from hx)]
        exact indicator_of_mem (show G x ∈ B ×ˢ univ from ⟨hx, trivial⟩) _
      · rw [indicator_of_notMem (show x ∉ lev3 ⁻¹' B from hx)]
        exact indicator_of_notMem (fun h : G x ∈ B ×ˢ univ => hx h.1) _
    have hint : Integrable Φ (P.map G) :=
      (integrable_map_measure hΦm.aestronglyMeasurable hG.aemeasurable).2 (by
        show Integrable (fun x => Φ (G x)) P
        rw [hΦG]; exact (hXi i).indicator (measurable_lev3 hB))
    rw [← hΦG, ← integral_map hG.aemeasurable hΦm.aestronglyMeasurable]
    have hG' : P.map G = Q ⊗ₘ ((chordKernel L R).comap (fun s : Fin 3 → ℝ => s i)
        (measurable_pi_apply i)) := hsl i
    rw [hG'] at hint ⊢
    have : IsSFiniteKernel (chordKernel L R) := by unfold chordKernel; infer_instance
    rw [Measure.integral_compProd hint, ← integral_indicator hB]
    congr 1; funext s
    rw [Kernel.comap_apply]
    by_cases hs : s ∈ B
    · rw [indicator_of_mem hs, ← integral_chordKernel hL hR]
      congr 1; funext z
      exact indicator_of_mem (show (s, z) ∈ B ×ˢ univ from ⟨hs, trivial⟩) _
    · rw [indicator_of_notMem hs]
      have : (fun z => Φ (s, z)) = fun _ => 0 := by
        funext z; exact indicator_of_notMem (fun h : (s, z) ∈ B ×ˢ univ => hs h.1) _
      simp only [this, integral_zero]
  refine ⟨hQp, hQi, ?_⟩
  -- conclude by the vanishing of all set integrals
  set f : (Fin 3 → ℝ) → ℝ × ℝ := fun s =>
    mid L R (s 0) + mid L R (s 1) + mid L R (s 2) - (3 : ℝ) • c
  have hfi : Integrable f Q := (((hMi 0).add (hMi 1)).add (hMi 2)).sub (integrable_const _)
  have hf0 : f =ᵐ[Q] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun B _ _ => hfi.integrableOn)
      fun B hB _ => ?_
    have hB' : MeasurableSet (lev3 ⁻¹' B) := measurable_lev3 hB
    have hsumB : ∫ x, (lev3 ⁻¹' B).indicator (fun x => x 0) x ∂P +
        ∫ x, (lev3 ⁻¹' B).indicator (fun x => x 1) x ∂P +
        ∫ x, (lev3 ⁻¹' B).indicator (fun x => x 2) x ∂P = (Q B).toReal • ((3 : ℝ) • c) := by
      rw [← integral_add ((hXi 0).indicator hB') ((hXi 1).indicator hB'),
        ← integral_add (f := fun x => (lev3 ⁻¹' B).indicator (fun x => x 0) x +
          (lev3 ⁻¹' B).indicator (fun x => x 1) x)
          (((hXi 0).indicator hB').add ((hXi 1).indicator hB')) ((hXi 2).indicator hB')]
      have : (fun x => (lev3 ⁻¹' B).indicator (fun x => x 0) x +
          (lev3 ⁻¹' B).indicator (fun x => x 1) x + (lev3 ⁻¹' B).indicator (fun x => x 2) x)
          =ᵐ[P] (lev3 ⁻¹' B).indicator (fun _ => (3 : ℝ) • c) := by
        filter_upwards [hsum'] with x hx
        by_cases hxB : x ∈ lev3 ⁻¹' B
        · simp only [indicator_of_mem hxB, hx]
        · simp only [indicator_of_notMem hxB, add_zero]
      rw [integral_congr_ae this, integral_indicator_const _ hB',
        Measure.map_apply measurable_lev3 hB, Measure.real]
    rw [key 0 B hB, key 1 B hB, key 2 B hB] at hsumB
    simp only [f]
    rw [integral_sub (f := fun s : Fin 3 → ℝ => mid L R (s 0) + mid L R (s 1) + mid L R (s 2))
      (((hMi 0).add (hMi 1)).add (hMi 2)).integrableOn (integrable_const _),
      integral_add (f := fun s : Fin 3 → ℝ => mid L R (s 0) + mid L R (s 1))
        ((hMi 0).add (hMi 1)).integrableOn (hMi 2).integrableOn,
      integral_add (hMi 0).integrableOn (hMi 1).integrableOn, hsumB, setIntegral_const,
      Measure.real, sub_self]
  filter_upwards [hf0] with s hs
  simp only [f, Pi.zero_apply, sub_eq_zero] at hs
  exact hs

end SlicedDef

/-! ### Concrete bodies: the excluded directions and the generic direction -/

/-- **Chords parallel to a side or a diagonal** (second paragraph of the proof), in chord
coordinates: the body between `L ≤ R` over `[a, b]`, where `L` and `R` are affine on `[a, t]`
and on `[t, b]` (the level `t` of the remaining vertices; for chords parallel to the side `AB`,
the chord at level `a` is that side), with `L < R` inside. The midpoint path is bent at `t`
(`bent`): by `side_path_straight_iff` and `diagonal_midpoint` this is the case unless `K` is a
trapezoid or a diagonal bisects the other. -/
structure BentBody where
  (a t b : ℝ)
  hat : a < t
  htb : t < b
  (L R : ℝ → ℝ)
  contL : Continuous L
  contR : Continuous R
  (l₀ l₁ r₀ r₁ : ℝ)
  affL₀ : ∀ s ∈ Icc a t, L s = L t + (s - t) * l₀
  affL₁ : ∀ s ∈ Icc t b, L s = L t + (s - t) * l₁
  affR₀ : ∀ s ∈ Icc a t, R s = R t + (s - t) * r₀
  affR₁ : ∀ s ∈ Icc t b, R s = R t + (s - t) * r₁
  le : ∀ s ∈ Icc a b, L s ≤ R s
  pos : ∀ s ∈ Ioo a b, L s < R s
  bent : l₀ + r₀ ≠ l₁ + r₁

namespace BentBody

variable (B : BentBody)

lemma hab : B.a < B.b := B.hat.trans B.htb

lemma area_pos' : 0 < area B.a B.b B.L B.R := area_pos B.hab B.contL B.contR B.pos

lemma map_fst_eq : (unifSet (body B.a B.b B.L B.R)).map Prod.fst =
    levelLaw (fun s => (B.R s - B.L s) / area B.a B.b B.L B.R) B.a B.b :=
  map_fst_unifSet_body B.contL B.contR B.le B.area_pos'

/-- The setting `Bent` of the second paragraph, built from the body. -/
def toBent : Bent where
  a := B.a
  t := B.t
  b := B.b
  hat := B.hat
  htb := B.htb
  μ := (unifSet (body B.a B.b B.L B.R)).map Prod.fst
  prob := by
    have := unifSet_body_isProb B.hab B.contL B.contR B.le B.pos
    infer_instance
  noAtoms := by rw [B.map_fst_eq]; infer_instance
  supp := by rw [B.map_fst_eq]; exact levelLaw_supp
  pos := fun x y hx hxy hy => by
    rw [B.map_fst_eq]
    exact levelLaw_pos (Continuous.measurable
      (f := fun s => (B.R s - B.L s) / area B.a B.b B.L B.R)
      (by have := B.contL; have := B.contR; fun_prop))
      (fun s hs => div_pos (sub_pos.2 (B.pos s hs)) B.area_pos') hx hxy hy
  M := mid B.L B.R
  cont := continuous_mid B.contL B.contR
  lam := LinearMap.fst ℝ ℝ ℝ
  lam_M := fun _ => rfl
  w₀ := (1, (B.l₀ + B.r₀) / 2)
  w₁ := (1, (B.l₁ + B.r₁) / 2)
  aff₀ := fun s hs => by
    simp only [mid, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, B.affL₀ s hs, B.affR₀ s hs]
    ext <;> simp only <;> ring
  aff₁ := fun s hs => by
    simp only [mid, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, B.affL₁ s hs, B.affR₁ s hs]
    ext <;> simp only <;> ring

/-- **No sliced `3`-complete mix in an excluded direction.** If the midpoint path of the body
is bent, `U(K)` has no `3`-complete mix that is sliced in the direction of the chords. -/
theorem no_sliced (P : Measure (Fin 3 → ℝ × ℝ))
    (hP : IsCompleteMix 3 (unifSet (body B.a B.b B.L B.R)) P) : ¬ IsSliced B.L B.R P := by
  intro hsl
  have h := isSlicedMix_of_sliced B.hab B.contL B.contR B.le B.pos hP hsl
  refine B.toBent.no_slicedMix ?_ _ _ h
  show cross (1, (B.l₀ + B.r₀) / 2) (1, (B.l₁ + B.r₁) / 2) ≠ 0
  simp only [cross]
  intro h'; exact B.bent (by linarith)

/-- The slope condition `bent` says exactly that the three midpoints `M a`, `M t`, `M b` (for
chords parallel to a diagonal `AC`: the vertex `B`, the midpoint of `AC` and the vertex `D`) are
not collinear. -/
lemma bent_iff_cross (B : BentBody) :
    B.l₀ + B.r₀ ≠ B.l₁ + B.r₁ ↔
      cross (mid B.L B.R B.t - mid B.L B.R B.a) (mid B.L B.R B.b - mid B.L B.R B.t) ≠ 0 := by
  have ea := B.affL₀ B.a ⟨le_rfl, B.hat.le⟩
  have ea' := B.affR₀ B.a ⟨le_rfl, B.hat.le⟩
  have eb := B.affL₁ B.b ⟨B.htb.le, le_rfl⟩
  have eb' := B.affR₁ B.b ⟨B.htb.le, le_rfl⟩
  have key : cross (mid B.L B.R B.t - mid B.L B.R B.a) (mid B.L B.R B.b - mid B.L B.R B.t) =
      (B.t - B.a) * (B.b - B.t) * ((B.l₁ + B.r₁) / 2 - (B.l₀ + B.r₀) / 2) := by
    simp only [cross, mid, Prod.fst_sub, Prod.snd_sub]; rw [ea, ea', eb, eb']; ring
  have h1 := sub_pos.2 B.hat
  have h2 := sub_pos.2 B.htb
  rw [key]
  constructor
  · intro h h'
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact (mul_pos h1 h2).ne' h''
    · exact h (by linarith)
  · intro h h'
    exact h (by rw [h']; ring)

end BentBody


/-- **A convex quadrilateral in a generic direction**, in chord coordinates: the levels
`s₀ < s₁ < s₂ < s₃` of the four vertices, the lower and upper ends `L ≤ R` of the chords,
affine between consecutive vertex levels (slopes `lⱼ`, `rⱼ`), meeting at the apices
`P₀ = (s₀, L s₀)` and `P₃ = (s₃, L s₃)`, with `L < R` inside. Exactly one vertex lies at each
of the levels `s₁`, `s₂`: one of the two chains is straight there and the other has a genuine
corner (`vert₁`, `vert₂`). (Convexity of the quadrilateral, `L` convex and `R` concave, is not
needed.) -/
structure QuadBody where
  (s₀ s₁ s₂ s₃ : ℝ)
  h01 : s₀ < s₁
  h12 : s₁ < s₂
  h23 : s₂ < s₃
  (L R : ℝ → ℝ)
  contL : Continuous L
  contR : Continuous R
  (l₀ l₁ l₂ r₀ r₁ r₂ : ℝ)
  affL₀ : ∀ s ∈ Icc s₀ s₁, L s = L s₀ + (s - s₀) * l₀
  affL₁ : ∀ s ∈ Icc s₁ s₂, L s = L s₁ + (s - s₁) * l₁
  affL₂ : ∀ s ∈ Icc s₂ s₃, L s = L s₂ + (s - s₂) * l₂
  affR₀ : ∀ s ∈ Icc s₀ s₁, R s = R s₀ + (s - s₀) * r₀
  affR₁ : ∀ s ∈ Icc s₁ s₂, R s = R s₁ + (s - s₁) * r₁
  affR₂ : ∀ s ∈ Icc s₂ s₃, R s = R s₂ + (s - s₂) * r₂
  apex₀ : L s₀ = R s₀
  apex₃ : L s₃ = R s₃
  pos : ∀ s ∈ Ioo s₀ s₃, L s < R s
  vert₁ : (l₀ = l₁ ∧ r₀ ≠ r₁) ∨ (r₀ = r₁ ∧ l₀ ≠ l₁)
  vert₂ : (l₁ = l₂ ∧ r₁ ≠ r₂) ∨ (r₁ = r₂ ∧ l₁ ≠ l₂)

namespace QuadBody

variable (B : QuadBody)

/-- The quadrilateral. -/
def K : Set (ℝ × ℝ) := body B.s₀ B.s₃ B.L B.R

/-- The chord length. -/
def g (s : ℝ) : ℝ := B.R s - B.L s

lemma h03 : B.s₀ < B.s₃ := (B.h01.trans B.h12).trans B.h23

lemma le' : ∀ s ∈ Icc B.s₀ B.s₃, B.L s ≤ B.R s := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h, B.apex₀]
  rcases eq_or_lt_of_le hs.2 with h' | h'
  · rw [h', B.apex₃]
  exact (B.pos s ⟨h, h'⟩).le

lemma area_pos' : 0 < area B.s₀ B.s₃ B.L B.R := area_pos B.h03 B.contL B.contR B.pos

lemma map_fst_eq : (unifSet B.K).map Prod.fst =
    levelLaw (fun s => B.g s / area B.s₀ B.s₃ B.L B.R) B.s₀ B.s₃ :=
  map_fst_unifSet_body B.contL B.contR B.le' B.area_pos'

lemma g_pos {s : ℝ} (hs : s ∈ Ioo B.s₀ B.s₃) : 0 < B.g s := sub_pos.2 (B.pos s hs)

lemma g_part₀ {s : ℝ} (hs : s ∈ Icc B.s₀ B.s₁) : B.g s = (s - B.s₀) * (B.r₀ - B.l₀) := by
  simp only [g]; rw [B.affL₀ s hs, B.affR₀ s hs, B.apex₀]; ring

lemma g_part₂ {s : ℝ} (hs : s ∈ Icc B.s₂ B.s₃) : B.g s = (B.s₃ - s) * (B.l₂ - B.r₂) := by
  have e3 := B.affL₂ B.s₃ ⟨B.h23.le, le_rfl⟩
  have e3' := B.affR₂ B.s₃ ⟨B.h23.le, le_rfl⟩
  simp only [g]; rw [B.affL₂ s hs, B.affR₂ s hs]
  have := B.apex₃; nlinarith

lemma g_part₁ {s : ℝ} (hs : s ∈ Icc B.s₁ B.s₂) :
    B.g s = B.g B.s₁ + (s - B.s₁) * (B.r₁ - B.l₁) := by
  simp only [g]; rw [B.affL₁ s hs, B.affR₁ s hs]; ring

/-- The density of the level vanishes linearly at both apices. -/
lemma g_le : ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc B.s₀ B.s₃, B.g s ≤ C * (s - B.s₀) ∧
    B.g s ≤ C * (B.s₃ - s) := by
  obtain ⟨G, hG⟩ := (isCompact_Icc : IsCompact (Icc B.s₀ B.s₃)).exists_bound_of_continuousOn
    (f := B.g) (Continuous.continuousOn (f := B.g)
      (by unfold g; have := B.contL; have := B.contR; fun_prop))
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG B.s₀ ⟨le_rfl, B.h03.le⟩)
  have h1 := sub_pos.2 B.h01
  have h3 := sub_pos.2 B.h23
  set C := |B.r₀ - B.l₀| + |B.l₂ - B.r₂| + G / (B.s₁ - B.s₀) + G / (B.s₃ - B.s₂)
  have hC1 : 0 ≤ G / (B.s₁ - B.s₀) := div_nonneg hG0 h1.le
  have hC3 : 0 ≤ G / (B.s₃ - B.s₂) := div_nonneg hG0 h3.le
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, fun s hs => ⟨?_, ?_⟩⟩
  · have hs0 : 0 ≤ s - B.s₀ := by linarith [hs.1]
    rcases le_total s B.s₁ with h | h
    · rw [B.g_part₀ ⟨hs.1, h⟩]
      have := le_abs_self (B.r₀ - B.l₀)
      have : (s - B.s₀) * (B.r₀ - B.l₀) ≤ (s - B.s₀) * |B.r₀ - B.l₀| :=
        mul_le_mul_of_nonneg_left this hs0
      nlinarith [abs_nonneg (B.l₂ - B.r₂)]
    · have hb : B.g s ≤ G := (le_abs_self _).trans (hG s hs)
      have : G ≤ G / (B.s₁ - B.s₀) * (s - B.s₀) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ h1]; nlinarith
      nlinarith [abs_nonneg (B.l₂ - B.r₂), abs_nonneg (B.r₀ - B.l₀)]
  · have hs3 : 0 ≤ B.s₃ - s := by linarith [hs.2]
    rcases le_total B.s₂ s with h | h
    · rw [B.g_part₂ ⟨h, hs.2⟩]
      have := le_abs_self (B.l₂ - B.r₂)
      have : (B.s₃ - s) * (B.l₂ - B.r₂) ≤ (B.s₃ - s) * |B.l₂ - B.r₂| :=
        mul_le_mul_of_nonneg_left this hs3
      nlinarith [abs_nonneg (B.r₀ - B.l₀)]
    · have hb : B.g s ≤ G := (le_abs_self _).trans (hG s hs)
      have : G ≤ G / (B.s₃ - B.s₂) * (B.s₃ - s) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ h3]; nlinarith
      nlinarith [abs_nonneg (B.l₂ - B.r₂), abs_nonneg (B.r₀ - B.l₀)]

/-- The density of the level is bounded below on the middle part and a little beyond. -/
lemma g_ge : ∃ m, 0 < m ∧ ∀ s ∈ Icc B.s₁ (B.s₂ + (B.s₃ - B.s₂) / 2), m ≤ B.g s := by
  have g1 := B.g_pos ⟨B.h01, B.h12.trans B.h23⟩
  have g2 := B.g_pos ⟨B.h01.trans B.h12, B.h23⟩
  refine ⟨min (B.g B.s₁) (B.g B.s₂ / 2), lt_min g1 (by linarith), fun s hs => ?_⟩
  rcases le_total s B.s₂ with h | h
  · have e := B.g_part₁ ⟨hs.1, h⟩
    have e2 := B.g_part₁ ⟨B.h12.le, le_rfl⟩
    have hd := sub_pos.2 B.h12
    -- `g` is affine on `[s₁, s₂]`, hence at least the smaller end value
    rcases le_total 0 (B.r₁ - B.l₁) with hk | hk
    · exact (min_le_left _ _).trans (by rw [e]; nlinarith [hs.1])
    · refine (min_le_right _ _).trans ?_
      rw [e]; rw [e2] at g2 ⊢; nlinarith [hs.1]
  · have e := B.g_part₂ ⟨h, hs.2.trans (by linarith [B.h23])⟩
    have e2 := B.g_part₂ ⟨le_rfl, B.h23.le⟩
    have hk : 0 < B.l₂ - B.r₂ := by
      rw [e2] at g2; exact pos_of_mul_pos_right g2 (sub_pos.2 B.h23).le
    refine (min_le_right _ _).trans ?_
    rw [e, e2]; nlinarith [hs.2]

/-- The setting `Quad3` of the third paragraph, built from the quadrilateral. -/
def toQuad3 : Quad3 where
  s₀ := B.s₀
  s₁ := B.s₁
  s₂ := B.s₂
  s₃ := B.s₃
  h01 := B.h01
  h12 := B.h12
  h23 := B.h23
  μ := (unifSet B.K).map Prod.fst
  prob := by
    have : IsProbabilityMeasure (unifSet B.K) :=
      unifSet_body_isProb B.h03 B.contL B.contR B.le' B.pos
    infer_instance
  noAtoms := by rw [B.map_fst_eq]; infer_instance
  supp := by rw [B.map_fst_eq]; exact levelLaw_supp
  pos := fun x y hx hxy hy => by
    rw [B.map_fst_eq]
    exact levelLaw_pos (Continuous.measurable
      (f := fun s => B.g s / area B.s₀ B.s₃ B.L B.R)
      (by unfold g; have := B.contL; have := B.contR; fun_prop))
      (fun s hs => div_pos (B.g_pos hs) B.area_pos') hx hxy hy
  C := B.g_le.choose / area B.s₀ B.s₃ B.L B.R
  quad₀ := fun ε hε => by
    rw [B.map_fst_eq]
    obtain ⟨hC, hb⟩ := B.g_le.choose_spec
    exact levelLaw_quad₀ (div_nonneg hC B.area_pos'.le) (fun s hs => by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hb s hs).1 B.area_pos'.le) hε
  quad₃ := fun ε hε => by
    rw [B.map_fst_eq]
    obtain ⟨hC, hb⟩ := B.g_le.choose_spec
    exact levelLaw_quad₃ (div_nonneg hC B.area_pos'.le) (fun s hs => by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hb s hs).2 B.area_pos'.le) hε
  m := B.g_ge.choose / area B.s₀ B.s₃ B.L B.R
  δ := (B.s₃ - B.s₂) / 2
  m_pos := div_pos B.g_ge.choose_spec.1 B.area_pos'
  δ_pos := by have := B.h23; linarith
  δ_le := by have := B.h23; linarith
  lower := fun x y hx hxy hy => by
    rw [B.map_fst_eq]
    exact levelLaw_lower (B.h01.le) (by have := B.h23; linarith) (fun s hs =>
      div_le_div_of_nonneg_right (B.g_ge.choose_spec.2 s hs) B.area_pos'.le) hx hxy hy
  M := mid B.L B.R
  cont := continuous_mid B.contL B.contR
  lam := LinearMap.fst ℝ ℝ ℝ
  lam_M := fun _ => rfl
  v₀ := (1, (B.l₀ + B.r₀) / 2)
  v₁ := (1, (B.l₁ + B.r₁) / 2)
  v₂ := (1, (B.l₂ + B.r₂) / 2)
  aff₀ := fun s hs => by
    simp only [mid, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, B.affL₀ s hs, B.affR₀ s hs]
    ext <;> simp only <;> ring
  aff₁ := fun s hs => by
    simp only [mid, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, B.affL₁ s hs, B.affR₁ s hs]
    ext <;> simp only <;> ring
  aff₂ := fun s hs => by
    simp only [mid, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, B.affL₂ s hs, B.affR₂ s hs]
    ext <;> simp only <;> ring

/-- The midpoints are not all on one line (third paragraph): already the first two segments
have different directions, since exactly one chain has a corner at the level `s₁`. (The paper
argues with the affine reflection along the chords.) -/
lemma v₀_ne_v₁ : B.toQuad3.v₀ ≠ B.toQuad3.v₁ := by
  show ((1 : ℝ), (B.l₀ + B.r₀) / 2) ≠ (1, (B.l₁ + B.r₁) / 2)
  intro h
  have h2 : B.l₀ + B.r₀ = B.l₁ + B.r₁ := by
    have := congrArg Prod.snd h; simp only at this; linarith
  rcases B.vert₁ with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact hr (by linarith)
  · exact hl (by linarith)

lemma v₁_ne_v₂ : B.toQuad3.v₁ ≠ B.toQuad3.v₂ := by
  show ((1 : ℝ), (B.l₁ + B.r₁) / 2) ≠ (1, (B.l₂ + B.r₂) / 2)
  intro h
  have h2 : B.l₁ + B.r₁ = B.l₂ + B.r₂ := by
    have := congrArg Prod.snd h; simp only at this; linarith
  rcases B.vert₂ with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact hr (by linarith)
  · exact hl (by linarith)

lemma mass_eq_iff {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    (unifSet B.K).map Prod.fst I = (unifSet B.K).map Prod.fst J ↔
      volume (B.K ∩ Prod.fst ⁻¹' I) = volume (B.K ∩ Prod.fst ⁻¹' J) := by
  have hv : volume B.K = ENNReal.ofReal (area B.s₀ B.s₃ B.L B.R) :=
    volume_body B.contL B.contR B.le'
  have h0 : (volume B.K)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by rw [hv]; exact ENNReal.ofReal_ne_top)
  have ht : (volume B.K)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by rw [hv]; simpa using B.area_pos')
  rw [Measure.map_apply measurable_fst hI, Measure.map_apply measurable_fst hJ, unifSet,
    smul_apply, smul_apply, Measure.restrict_apply (measurable_fst hI),
    Measure.restrict_apply (measurable_fst hJ), smul_eq_mul, smul_eq_mul,
    ENNReal.mul_right_inj h0 ht, inter_comm, inter_comm (Prod.fst ⁻¹' J)]

/-- **Proposition 87 for a quadrilateral in a generic direction.** Let `K` be a quadrilateral
in a direction of chords in which the four vertices have different levels (`QuadBody`), with
centroid `c`, and suppose that `U(K)` has a `3`-complete mix that is sliced in this direction.
Then the midpoints lie on three segments `σ₁ = M[s₀, s₁]`, `σ₂ = M[s₁, s₂]`, `σ₃ = M[s₂, s₃]`
with adjacent ones not parallel, and `c ∈ σ₂`. If moreover `c` is not an endpoint of `σ₂` and
`σ₁ ∦ σ₃`, then the two triangles have equal areas and `3c - P₀ - P₃ ∈ σ₂`, `P₀ = (s₀, L s₀)`,
`P₃ = (s₃, L s₃)` the apices. -/
theorem prop87 (P : Measure (Fin 3 → ℝ × ℝ)) (hP : IsCompleteMix 3 (unifSet B.K) P)
    (hsl : IsSliced B.L B.R P) :
    let c := ∫ x, x ∂(unifSet B.K)
    cross B.toQuad3.v₀ B.toQuad3.v₁ ≠ 0 ∧ cross B.toQuad3.v₁ B.toQuad3.v₂ ≠ 0 ∧
      c ∈ mid B.L B.R '' Icc B.s₁ B.s₂ ∧
      (c ∈ mid B.L B.R '' Ioo B.s₁ B.s₂ → cross B.toQuad3.v₀ B.toQuad3.v₂ ≠ 0 →
        volume (B.K ∩ Prod.fst ⁻¹' Ioo B.s₀ B.s₁) = volume (B.K ∩ Prod.fst ⁻¹' Ioo B.s₂ B.s₃) ∧
        (3 : ℝ) • c - (B.s₀, B.L B.s₀) - (B.s₃, B.L B.s₃) ∈ mid B.L B.R '' Icc B.s₁ B.s₂) := by
  intro c
  have h := isSlicedMix_of_sliced B.h03 B.contL B.contR B.le' B.pos hP hsl
  obtain ⟨h1, h2, h3, h4⟩ := B.toQuad3.prop87 (fun h => B.v₀_ne_v₁ h.1) h
  refine ⟨h1, h2, h3, fun hc h02 => ?_⟩
  obtain ⟨hm, hpt⟩ := h4 hc h02
  refine ⟨(B.mass_eq_iff measurableSet_Ioo measurableSet_Ioo).1 hm, ?_⟩
  have e0 : mid B.L B.R B.s₀ = (B.s₀, B.L B.s₀) := by
    simp only [mid, B.apex₀]; ext <;> simp only; ring
  have e3 : mid B.L B.R B.s₃ = (B.s₃, B.L B.s₃) := by
    simp only [mid, B.apex₃]; ext <;> simp only; ring
  rw [← e0, ← e3]; exact hpt

end QuadBody

set_option linter.unusedSectionVars false

/-! ### Lines through two points, and the convex quadrilateral as an intersection -/

/-- The slope of the line through `P` and `Q`. -/
def slp (P Q : ℝ × ℝ) : ℝ := (Q.2 - P.2) / (Q.1 - P.1)

/-- The line through `P` and `Q`, as a function of the first coordinate. -/
def lin (P Q : ℝ × ℝ) (s : ℝ) : ℝ := P.2 + (s - P.1) * slp P Q

lemma continuous_lin (P Q : ℝ × ℝ) : Continuous (lin P Q) := by unfold lin; fun_prop

lemma slp_comm (P Q : ℝ × ℝ) : slp P Q = slp Q P := by
  unfold slp; rw [← neg_sub Q.2, ← neg_sub Q.1, neg_div_neg_eq]

lemma lin_fst (P Q : ℝ × ℝ) : lin P Q P.1 = P.2 := by simp [lin]

lemma lin_snd {P Q : ℝ × ℝ} (h : P.1 ≠ Q.1) : lin P Q Q.1 = Q.2 := by
  have : Q.1 - P.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  simp only [lin, slp]; field_simp; ring

lemma lin_eq (P Q : ℝ × ℝ) (s t : ℝ) : lin P Q s = lin P Q t + (s - t) * slp P Q := by
  simp only [lin]; ring

lemma lin_comm {P Q : ℝ × ℝ} (h : P.1 ≠ Q.1) (s : ℝ) : lin P Q s = lin Q P s := by
  rw [lin_eq P Q s Q.1, lin_snd h, slp_comm]; rfl

lemma cross_eq_lin {P Q : ℝ × ℝ} (h : P.1 ≠ Q.1) (X : ℝ × ℝ) :
    cross (Q - P) (X - P) = (Q.1 - P.1) * (X.2 - lin P Q X.1) := by
  have : Q.1 - P.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  simp only [cross, lin, slp, Prod.fst_sub, Prod.snd_sub]; field_simp; ring

lemma above {P Q : ℝ × ℝ} (h : P.1 < Q.1) (X : ℝ × ℝ) :
    0 ≤ cross (Q - P) (X - P) ↔ lin P Q X.1 ≤ X.2 := by
  rw [cross_eq_lin h.ne X]
  rw [mul_nonneg_iff_of_pos_left (sub_pos.2 h), sub_nonneg]

lemma above_lt {P Q : ℝ × ℝ} (h : P.1 < Q.1) (X : ℝ × ℝ) :
    0 < cross (Q - P) (X - P) ↔ lin P Q X.1 < X.2 := by
  rw [cross_eq_lin h.ne X]
  constructor
  · intro h'; exact sub_pos.1 (pos_of_mul_pos_right h' (sub_pos.2 h).le)
  · intro h'; exact mul_pos (sub_pos.2 h) (sub_pos.2 h')

lemma below {P Q : ℝ × ℝ} (h : Q.1 < P.1) (X : ℝ × ℝ) :
    0 ≤ cross (Q - P) (X - P) ↔ X.2 ≤ lin P Q X.1 := by
  rw [cross_eq_lin h.ne' X]
  constructor
  · intro h'
    by_contra hc; push Not at hc
    have := mul_neg_of_neg_of_pos (sub_neg.2 h) (sub_pos.2 hc); linarith
  · intro h'; exact mul_nonneg_of_nonpos_of_nonpos (sub_neg.2 h).le (sub_nonpos.2 h')

lemma below_lt {P Q : ℝ × ℝ} (h : Q.1 < P.1) (X : ℝ × ℝ) :
    0 < cross (Q - P) (X - P) ↔ X.2 < lin P Q X.1 := by
  rw [cross_eq_lin h.ne' X]
  constructor
  · intro h'
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg (sub_neg.2 h).le (sub_nonneg.2 hc); linarith
  · intro h'; exact mul_pos_of_neg_of_neg (sub_neg.2 h) (sub_neg.2 h')

/-- The turn at `Y` of the path `X, Y, Z` in terms of slopes. -/
lemma cross_turn {X Y Z : ℝ × ℝ} (h1 : X.1 ≠ Y.1) (h2 : Y.1 ≠ Z.1) :
    cross (Y - X) (Z - X) = (Y.1 - X.1) * (Z.1 - Y.1) * (slp Y Z - slp X Y) := by
  have e1 : Y.1 - X.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e2 : Z.1 - Y.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  simp only [cross, slp, Prod.fst_sub, Prod.snd_sub]; field_simp; ring

/-- An affine function nonnegative at both ends of `[a, b]` is nonnegative on `[a, b]`, and
positive inside if it is positive at one end. -/
lemma aff_nonneg {h : ℝ → ℝ} {a b k : ℝ} (hh : ∀ s, h s = h a + (s - a) * k) (hab : a < b)
    (ha : 0 ≤ h a) (hb : 0 ≤ h b) : ∀ s ∈ Icc a b, 0 ≤ h s := by
  intro s hs
  have e : (b - a) * h s = (b - s) * h a + (s - a) * h b := by
    rw [hh s, hh b]; ring
  have : 0 ≤ (b - a) * h s := by rw [e]; nlinarith [hs.1, hs.2]
  exact (mul_nonneg_iff_of_pos_left (sub_pos.2 hab)).1 this

lemma aff_pos {h : ℝ → ℝ} {a b k : ℝ} (hh : ∀ s, h s = h a + (s - a) * k) (hab : a < b)
    (ha : 0 ≤ h a) (hb : 0 ≤ h b) (hp : 0 < h a + h b) : ∀ s ∈ Ioo a b, 0 < h s := by
  intro s hs
  have e : (b - a) * h s = (b - s) * h a + (s - a) * h b := by
    rw [hh s, hh b]; ring
  have h1 : 0 < b - s := sub_pos.2 hs.2
  have h2 : 0 < s - a := sub_pos.2 hs.1
  have : 0 < (b - a) * h s := by
    rw [e]
    rcases lt_or_eq_of_le ha with ha' | ha'
    · nlinarith
    · have : 0 < h b := by linarith
      nlinarith
  exact pos_of_mul_pos_right this (sub_pos.2 hab).le

/-- A convex quadrilateral with the vertices `A, B, C, D` in counterclockwise order: each vertex
lies strictly to the left of the two sides not through it. -/
structure ConvQuad (A B C D : ℝ × ℝ) : Prop where
  ab_c : 0 < cross (B - A) (C - A)
  ab_d : 0 < cross (B - A) (D - A)
  bc_d : 0 < cross (C - B) (D - B)
  bc_a : 0 < cross (C - B) (A - B)
  cd_a : 0 < cross (D - C) (A - C)
  cd_b : 0 < cross (D - C) (B - C)
  da_b : 0 < cross (A - D) (B - D)
  da_c : 0 < cross (A - D) (C - D)

/-- The closed half-plane to the left of the line from `P` to `Q`. -/
def halfP (P Q : ℝ × ℝ) : Set (ℝ × ℝ) := {x | 0 ≤ cross (Q - P) (x - P)}

lemma convex_halfP (P Q : ℝ × ℝ) : Convex ℝ (halfP P Q) := by
  intro x hx y hy a b ha hb hab
  simp only [halfP, mem_ofPred_eq] at *
  have e : cross (Q - P) (a • x + b • y - P) =
      a * cross (Q - P) (x - P) + b * cross (Q - P) (y - P) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    obtain rfl : b = 1 - a := by linarith
    ring
  rw [e]; positivity

lemma mem_hull3 {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) {P Q R : ℝ × ℝ} (hP : P ∈ S) (hQ : Q ∈ S)
    (hR : R ∈ S) {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hs : α + β + γ = 1) :
    α • P + β • Q + γ • R ∈ S := by
  rcases eq_or_lt_of_le (add_nonneg hβ hγ) with h0 | h0
  · have hb : β = 0 := by linarith
    have hc : γ = 0 := by linarith
    have ha : α = 1 := by linarith
    subst hb hc ha; simpa using hP
  · have hQR : (β / (β + γ)) • Q + (γ / (β + γ)) • R ∈ S :=
      hS hQ hR (div_nonneg hβ h0.le) (div_nonneg hγ h0.le) (by field_simp)
    have := hS hP hQR hα h0.le (by linarith)
    convert this using 1
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h0.ne',
      mul_div_cancel₀ _ h0.ne', add_assoc]

lemma combo3 {Δ b g : ℝ} {x A P Q : ℝ × ℝ} (hΔ : Δ ≠ 0)
    (key : Δ • x = (Δ - b - g) • A + b • P + g • Q) :
    x = (1 - b / Δ - g / Δ) • A + (b / Δ) • P + (g / Δ) • Q := by
  calc x = Δ⁻¹ • (Δ • x) := by rw [smul_smul, inv_mul_cancel₀ hΔ, one_smul]
    _ = _ := by
      have e : Δ⁻¹ * (Δ - b - g) = 1 - b / Δ - g / Δ := by field_simp
      rw [key, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e, inv_mul_eq_div,
        inv_mul_eq_div]

/-- **A convex quadrilateral is the intersection of the four half-planes of its sides.** -/
theorem hull_eq {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) :
    convexHull ℝ {A, B, C, D} = halfP A B ∩ halfP B C ∩ halfP C D ∩ halfP D A := by
  apply Subset.antisymm
  · refine convexHull_min ?_ ((((convex_halfP _ _).inter (convex_halfP _ _)).inter
      (convex_halfP _ _)).inter (convex_halfP _ _))
    have := h.ab_c; have := h.ab_d; have := h.bc_d; have := h.bc_a
    have := h.cd_a; have := h.cd_b; have := h.da_b; have := h.da_c
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    simp only [halfP, mem_inter_iff, mem_ofPred_eq]
    rcases hx with rfl | rfl | rfl | rfl <;>
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      first | linarith | (simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; nlinarith)
  · rintro x ⟨⟨⟨hab, hbc⟩, hcd⟩, hda⟩
    simp only [halfP, mem_ofPred_eq] at hab hbc hcd hda
    have hS := convex_convexHull ℝ ({A, B, C, D} : Set (ℝ × ℝ))
    have mA : A ∈ convexHull ℝ ({A, B, C, D} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    have mB : B ∈ convexHull ℝ ({A, B, C, D} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    have mC : C ∈ convexHull ℝ ({A, B, C, D} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    have mD : D ∈ convexHull ℝ ({A, B, C, D} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    rcases le_or_gt 0 (cross (C - A) (x - A)) with hx | hx
    · -- the triangle `A C D`
      have hΔ : 0 < cross (C - A) (D - A) := by
        have := h.cd_a; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; nlinarith
      set Δ := cross (C - A) (D - A)
      have hβ : 0 ≤ cross (x - A) (D - A) / Δ := by
        apply div_nonneg _ hΔ.le
        simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; nlinarith
      have hγ : 0 ≤ cross (C - A) (x - A) / Δ := div_nonneg hx hΔ.le
      have hα : 0 ≤ 1 - cross (x - A) (D - A) / Δ - cross (C - A) (x - A) / Δ := by
        rw [sub_sub, ← add_div, sub_nonneg, div_le_one hΔ]
        simp only [Δ, cross, Prod.fst_sub, Prod.snd_sub] at *; nlinarith
      convert mem_hull3 hS mA mC mD hα hβ hγ (by ring) using 1
      exact combo3 hΔ.ne' (by ext <;> simp only [Δ, cross, Prod.fst_sub, Prod.snd_sub,
        Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring)
    · -- the triangle `A B C`
      have hΔ : 0 < cross (B - A) (C - A) := h.ab_c
      set Δ := cross (B - A) (C - A)
      have hβ : 0 ≤ cross (x - A) (C - A) / Δ := by
        apply div_nonneg _ hΔ.le
        simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; nlinarith
      have hγ : 0 ≤ cross (B - A) (x - A) / Δ := div_nonneg hab hΔ.le
      have hα : 0 ≤ 1 - cross (x - A) (C - A) / Δ - cross (B - A) (x - A) / Δ := by
        rw [sub_sub, ← add_div, sub_nonneg, div_le_one hΔ]
        simp only [Δ, cross, Prod.fst_sub, Prod.snd_sub] at *; nlinarith
      convert mem_hull3 hS mA mB mC hα hβ hγ (by ring) using 1
      exact combo3 hΔ.ne' (by ext <;> simp only [Δ, cross, Prod.fst_sub, Prod.snd_sub,
        Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring)

lemma hull_strip {A B C D : ℝ × ℝ} {m M : ℝ} (hA : A.1 ∈ Icc m M) (hB : B.1 ∈ Icc m M)
    (hC : C.1 ∈ Icc m M) (hD : D.1 ∈ Icc m M) {x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ {A, B, C, D}) : x.1 ∈ Icc m M := by
  have := convexHull_min (s := ({A, B, C, D} : Set (ℝ × ℝ))) (t := Prod.fst ⁻¹' Icc m M)
    (by intro y hy; simp only [mem_insert_iff, mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> assumption)
    ((convex_Icc m M).linear_preimage (LinearMap.fst ℝ ℝ ℝ)) hx
  exact this


lemma lin_thru {P Q : ℝ × ℝ} (h : P.1 ≠ Q.1) (s : ℝ) : lin P Q s = Q.2 + (s - Q.1) * slp P Q := by
  rw [lin_eq P Q s Q.1, lin_snd h]

lemma lin_def (P Q : ℝ × ℝ) (s : ℝ) : lin P Q s = P.2 + (s - P.1) * slp P Q := rfl

lemma slp_lt {X Y Z : ℝ × ℝ} (h1 : X.1 < Y.1) (h2 : Y.1 < Z.1)
    (h : 0 < cross (Y - X) (Z - X)) : slp X Y < slp Y Z := by
  rw [cross_turn h1.ne h2.ne] at h
  exact sub_pos.1 (pos_of_mul_pos_right h (mul_pos (sub_pos.2 h1) (sub_pos.2 h2)).le)

lemma slp_gt {X Y Z : ℝ × ℝ} (h1 : X.1 < Y.1) (h2 : Y.1 < Z.1)
    (h : cross (Y - X) (Z - X) < 0) : slp Y Z < slp X Y := by
  rw [cross_turn h1.ne h2.ne] at h
  have hp := mul_pos (sub_pos.2 h1) (sub_pos.2 h2)
  by_contra hc; push Not at hc
  have := mul_nonneg hp.le (sub_nonneg.2 hc); linarith

lemma nd_max_l {y x s m₁ m₂ : ℝ} (hm : m₁ ≤ m₂) (hs : s ≤ x) :
    max (y + (s - x) * m₁) (y + (s - x) * m₂) = y + (s - x) * m₁ :=
  max_eq_left (by nlinarith)

lemma nd_max_r {y x s m₁ m₂ : ℝ} (hm : m₁ ≤ m₂) (hs : x ≤ s) :
    max (y + (s - x) * m₁) (y + (s - x) * m₂) = y + (s - x) * m₂ :=
  max_eq_right (by nlinarith)

lemma nd_min_l {y x s m₁ m₂ : ℝ} (hm : m₂ ≤ m₁) (hs : s ≤ x) :
    min (y + (s - x) * m₁) (y + (s - x) * m₂) = y + (s - x) * m₁ :=
  min_eq_left (by nlinarith)

lemma nd_min_r {y x s m₁ m₂ : ℝ} (hm : m₂ ≤ m₁) (hs : x ≤ s) :
    min (y + (s - x) * m₁) (y + (s - x) * m₂) = y + (s - x) * m₂ :=
  min_eq_right (by nlinarith)

/-- Two lines, ordered at both ends of `[a, b]` and strictly at one of them, are strictly
ordered inside. -/
lemma lin_lt {P Q P' Q' : ℝ × ℝ} {a b : ℝ} (hab : a < b) (ha : lin P Q a ≤ lin P' Q' a)
    (hb : lin P Q b ≤ lin P' Q' b) (hs : lin P Q a < lin P' Q' a ∨ lin P Q b < lin P' Q' b) :
    ∀ s ∈ Ioo a b, lin P Q s < lin P' Q' s := by
  intro s hs'
  have := aff_pos (h := fun s => lin P' Q' s - lin P Q s) (k := slp P' Q' - slp P Q)
    (fun s => by rw [lin_eq P Q s a, lin_eq P' Q' s a]; ring) hab
    (by linarith) (by linarith)
    (by rcases hs with hs | hs <;> linarith) s hs'
  linarith

lemma lin_le {P Q P' Q' : ℝ × ℝ} {a b : ℝ} (hab : a < b) (ha : lin P Q a ≤ lin P' Q' a)
    (hb : lin P Q b ≤ lin P' Q' b) : ∀ s ∈ Icc a b, lin P Q s ≤ lin P' Q' s := by
  intro s hs'
  have := aff_nonneg (h := fun s => lin P' Q' s - lin P Q s) (k := slp P' Q' - slp P Q)
    (fun s => by rw [lin_eq P Q s a, lin_eq P' Q' s a]; ring) hab
    (by linarith) (by linarith) s hs'
  linarith

/-! ### Configuration `G1`: `A` lowest, `C` highest, `B` below `D` in level -/

section G1

variable {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 < B.1) (h2 : B.1 < D.1)
  (h3 : D.1 < C.1)
include h h1 h2 h3

lemma g1_sl : slp A B < slp B C := slp_lt h1 (h2.trans h3) h.ab_c

lemma g1_su : slp C D < slp D A := by
  have := slp_gt (X := A) (Y := D) (Z := C) (h1.trans h2) h3
    (by have := h.da_c; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith)
  rwa [slp_comm D C, slp_comm A D] at this

lemma g1_L_l {s : ℝ} (hs : s ≤ B.1) : max (lin A B s) (lin B C s) = lin A B s := by
  rw [lin_thru h1.ne s, lin_def B C s, nd_max_l (g1_sl h h1 h2 h3).le hs]

lemma g1_L_r {s : ℝ} (hs : B.1 ≤ s) : max (lin A B s) (lin B C s) = lin B C s := by
  rw [lin_thru h1.ne s, lin_def B C s, nd_max_r (g1_sl h h1 h2 h3).le hs]

lemma g1_R_l {s : ℝ} (hs : s ≤ D.1) : min (lin D A s) (lin C D s) = lin D A s := by
  rw [lin_thru h3.ne' s, lin_def D A s, nd_min_l (g1_su h h1 h2 h3).le hs]

lemma g1_R_r {s : ℝ} (hs : D.1 ≤ s) : min (lin D A s) (lin C D s) = lin C D s := by
  rw [lin_thru h3.ne' s, lin_def D A s, nd_min_r (g1_su h h1 h2 h3).le hs]

end G1

/-- The quadrilateral of configuration `G1` as a `QuadBody`. -/
def qG1 {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 < B.1) (h2 : B.1 < D.1)
    (h3 : D.1 < C.1) : QuadBody where
  s₀ := A.1
  s₁ := B.1
  s₂ := D.1
  s₃ := C.1
  h01 := h1
  h12 := h2
  h23 := h3
  L s := max (lin A B s) (lin B C s)
  R s := min (lin D A s) (lin C D s)
  contL := (continuous_lin A B).max (continuous_lin B C)
  contR := (continuous_lin D A).min (continuous_lin C D)
  l₀ := slp A B
  l₁ := slp B C
  l₂ := slp B C
  r₀ := slp D A
  r₁ := slp D A
  r₂ := slp C D
  affL₀ s hs := by
    rw [g1_L_l h h1 h2 h3 hs.2, g1_L_l h h1 h2 h3 h1.le, lin_eq A B s A.1]
  affL₁ s hs := by
    rw [g1_L_r h h1 h2 h3 hs.1, g1_L_r h h1 h2 h3 le_rfl, lin_eq B C s B.1]
  affL₂ s hs := by
    rw [g1_L_r h h1 h2 h3 (h2.le.trans hs.1), g1_L_r h h1 h2 h3 h2.le,
      lin_eq B C s D.1]
  affR₀ s hs := by
    rw [g1_R_l h h1 h2 h3 (hs.2.trans h2.le), g1_R_l h h1 h2 h3 (h1.trans h2).le,
      lin_eq D A s A.1]
  affR₁ s hs := by
    rw [g1_R_l h h1 h2 h3 hs.2, g1_R_l h h1 h2 h3 h2.le, lin_eq D A s B.1]
  affR₂ s hs := by
    rw [g1_R_r h h1 h2 h3 hs.1, g1_R_r h h1 h2 h3 le_rfl, lin_eq C D s D.1]
  apex₀ := by
    rw [g1_L_l h h1 h2 h3 h1.le, g1_R_l h h1 h2 h3 (h1.trans h2).le, lin_fst,
      lin_snd (h1.trans h2).ne']
  apex₃ := by
    rw [g1_L_r h h1 h2 h3 (h2.trans h3).le, g1_R_r h h1 h2 h3 h3.le, lin_fst,
      lin_snd (h2.trans h3).ne]
  pos s hs := by
    have hAC : A.1 < C.1 := (h1.trans h2).trans h3
    -- the four pairs (lower line, upper line)
    have p1 := lin_lt (P := A) (Q := B) (P' := D) (Q' := A) hAC
      (by rw [lin_fst, lin_snd (h1.trans h2).ne'])
      (by have := (above_lt h1 C).1 h.ab_c
          have := (below_lt (h1.trans h2) C).1 h.da_c; linarith)
      (Or.inr (by have := (above_lt h1 C).1 h.ab_c
                  have := (below_lt (h1.trans h2) C).1 h.da_c; linarith)) s hs
    have p2 := lin_lt (P := A) (Q := B) (P' := C) (Q' := D) hAC
      (by rw [lin_fst]; exact ((below_lt h3 A).1 h.cd_a).le)
      (by rw [lin_fst]; exact ((above_lt h1 C).1 h.ab_c).le)
      (Or.inl (by rw [lin_fst]; exact (below_lt h3 A).1 h.cd_a)) s hs
    have p3 := lin_lt (P := B) (Q := C) (P' := D) (Q' := A) hAC
      (by rw [lin_snd (h1.trans h2).ne']; exact ((above_lt (h2.trans h3) A).1 h.bc_a).le)
      (by rw [lin_snd (h2.trans h3).ne]; exact ((below_lt (h1.trans h2) C).1 h.da_c).le)
      (Or.inl (by rw [lin_snd (h1.trans h2).ne']; exact (above_lt (h2.trans h3) A).1 h.bc_a))
      s hs
    have p4 := lin_lt (P := B) (Q := C) (P' := C) (Q' := D) hAC
      (by have := (above_lt (h2.trans h3) A).1 h.bc_a
          have := (below_lt h3 A).1 h.cd_a; linarith)
      (by rw [lin_snd (h2.trans h3).ne, lin_fst])
      (Or.inl (by have := (above_lt (h2.trans h3) A).1 h.bc_a
                  have := (below_lt h3 A).1 h.cd_a; linarith)) s hs
    exact max_lt (lt_min p1 p2) (lt_min p3 p4)
  vert₁ := Or.inr ⟨rfl, (g1_sl h h1 h2 h3).ne⟩
  vert₂ := Or.inl ⟨rfl, (g1_su h h1 h2 h3).ne'⟩


lemma mem_hull_iff {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (x : ℝ × ℝ) :
    x ∈ convexHull ℝ {A, B, C, D} ↔ 0 ≤ cross (B - A) (x - A) ∧ 0 ≤ cross (C - B) (x - B) ∧
      0 ≤ cross (D - C) (x - C) ∧ 0 ≤ cross (A - D) (x - D) := by
  rw [hull_eq h]; simp only [halfP, mem_inter_iff, mem_ofPred_eq, and_assoc]

lemma qG1_K {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 < B.1) (h2 : B.1 < D.1)
    (h3 : D.1 < C.1) : (qG1 h h1 h2 h3).K = convexHull ℝ {A, B, C, D} := by
  ext x
  simp only [QuadBody.K, qG1, body, mem_ofPred_eq]
  constructor
  · rintro ⟨-, hL, hR⟩
    rw [mem_hull_iff h, above h1, above (h2.trans h3), below h3, below (h1.trans h2)]
    exact ⟨(le_max_left _ _).trans hL, (le_max_right _ _).trans hL,
      hR.trans (min_le_right _ _), hR.trans (min_le_left _ _)⟩
  · intro hx
    have r := hull_strip (m := A.1) (M := C.1) ⟨le_rfl, (h1.trans h2).trans h3 |>.le⟩
      ⟨h1.le, (h2.trans h3).le⟩ ⟨((h1.trans h2).trans h3).le, le_rfl⟩
      ⟨(h1.trans h2).le, h3.le⟩ hx
    rw [mem_hull_iff h, above h1, above (h2.trans h3), below h3, below (h1.trans h2)] at hx
    exact ⟨r, max_le hx.1 hx.2.1, le_min hx.2.2.2 hx.2.2.1⟩


/-! ### Configuration `G2`: `A` lowest, `B` highest, then `D` below `C` in level -/

section G2

variable {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 < D.1) (h2 : D.1 < C.1)
  (h3 : C.1 < B.1)
include h h1 h2 h3

lemma g2_su1 : slp C D < slp D A := by
  have := slp_gt (X := A) (Y := D) (Z := C) h1 h2
    (by have := h.da_c; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith)
  rwa [slp_comm D C, slp_comm A D] at this

lemma g2_su2 : slp B C < slp C D := by
  have := slp_gt (X := D) (Y := C) (Z := B) h2 h3
    (by have := h.cd_b; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith)
  rwa [slp_comm C B, slp_comm D C] at this

lemma g2_in_l {s : ℝ} (hs : s ≤ C.1) : min (lin C D s) (lin B C s) = lin C D s := by
  rw [lin_thru h3.ne' s, lin_def C D s, nd_min_l (g2_su2 h h1 h2 h3).le hs]

lemma g2_in_r {s : ℝ} (hs : C.1 ≤ s) : min (lin C D s) (lin B C s) = lin B C s := by
  rw [lin_thru h3.ne' s, lin_def C D s, nd_min_r (g2_su2 h h1 h2 h3).le hs]

lemma g2_o_l {s : ℝ} (hs : s ≤ D.1) : min (lin D A s) (lin C D s) = lin D A s := by
  rw [lin_thru h2.ne' s, lin_def D A s, nd_min_l (g2_su1 h h1 h2 h3).le hs]

lemma g2_o_r {s : ℝ} (hs : D.1 ≤ s) : min (lin D A s) (lin C D s) = lin C D s := by
  rw [lin_thru h2.ne' s, lin_def D A s, nd_min_r (g2_su1 h h1 h2 h3).le hs]

lemma g2_R1 {s : ℝ} (hs : s ≤ D.1) :
    min (lin D A s) (min (lin C D s) (lin B C s)) = lin D A s := by
  rw [g2_in_l h h1 h2 h3 (hs.trans h2.le), g2_o_l h h1 h2 h3 hs]

lemma g2_R2 {s : ℝ} (hs : D.1 ≤ s) (hs' : s ≤ C.1) :
    min (lin D A s) (min (lin C D s) (lin B C s)) = lin C D s := by
  rw [g2_in_l h h1 h2 h3 hs', g2_o_r h h1 h2 h3 hs]

lemma g2_R3 {s : ℝ} (hs : C.1 ≤ s) :
    min (lin D A s) (min (lin C D s) (lin B C s)) = lin B C s := by
  have e1 := g2_in_r h h1 h2 h3 hs
  have e2 := g2_o_r h h1 h2 h3 (h2.le.trans hs)
  rw [e1]
  exact min_eq_right ((min_eq_right_iff.1 e1).trans (min_eq_right_iff.1 e2))

end G2

/-- The quadrilateral of configuration `G2` as a `QuadBody`. -/
def qG2 {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 < D.1) (h2 : D.1 < C.1)
    (h3 : C.1 < B.1) : QuadBody where
  s₀ := A.1
  s₁ := D.1
  s₂ := C.1
  s₃ := B.1
  h01 := h1
  h12 := h2
  h23 := h3
  L s := lin A B s
  R s := min (lin D A s) (min (lin C D s) (lin B C s))
  contL := continuous_lin A B
  contR := (continuous_lin D A).min ((continuous_lin C D).min (continuous_lin B C))
  l₀ := slp A B
  l₁ := slp A B
  l₂ := slp A B
  r₀ := slp D A
  r₁ := slp C D
  r₂ := slp B C
  affL₀ s _ := lin_eq A B s A.1
  affL₁ s _ := lin_eq A B s D.1
  affL₂ s _ := lin_eq A B s C.1
  affR₀ s hs := by
    rw [g2_R1 h h1 h2 h3 hs.2, g2_R1 h h1 h2 h3 h1.le, lin_eq D A s A.1]
  affR₁ s hs := by
    rw [g2_R2 h h1 h2 h3 hs.1 hs.2, g2_R2 h h1 h2 h3 le_rfl h2.le, lin_eq C D s D.1]
  affR₂ s hs := by
    rw [g2_R3 h h1 h2 h3 hs.1, g2_R3 h h1 h2 h3 le_rfl, lin_eq B C s C.1]
  apex₀ := by rw [g2_R1 h h1 h2 h3 h1.le, lin_fst, lin_snd h1.ne']
  apex₃ := by rw [g2_R3 h h1 h2 h3 h3.le, lin_fst, lin_snd ((h1.trans h2).trans h3).ne]
  pos s hs := by
    have hAB : A.1 < B.1 := (h1.trans h2).trans h3
    have p1 := lin_lt (P := A) (Q := B) (P' := D) (Q' := A) hAB
      (by rw [lin_fst, lin_snd h1.ne'])
      (by rw [lin_snd hAB.ne]; exact ((below_lt h1 B).1 h.da_b).le)
      (Or.inr (by rw [lin_snd hAB.ne]; exact (below_lt h1 B).1 h.da_b)) s hs
    have p2 := lin_lt (P := A) (Q := B) (P' := C) (Q' := D) hAB
      (by rw [lin_fst]; exact ((below_lt h2 A).1 h.cd_a).le)
      (by rw [lin_snd hAB.ne]; exact ((below_lt h2 B).1 h.cd_b).le)
      (Or.inl (by rw [lin_fst]; exact (below_lt h2 A).1 h.cd_a)) s hs
    have p3 := lin_lt (P := A) (Q := B) (P' := B) (Q' := C) hAB
      (by rw [lin_fst]; exact ((below_lt h3 A).1 h.bc_a).le)
      (by rw [lin_snd hAB.ne, lin_fst])
      (Or.inl (by rw [lin_fst]; exact (below_lt h3 A).1 h.bc_a)) s hs
    exact lt_min p1 (lt_min p2 p3)
  vert₁ := Or.inl ⟨rfl, (g2_su1 h h1 h2 h3).ne'⟩
  vert₂ := Or.inl ⟨rfl, (g2_su2 h h1 h2 h3).ne'⟩

lemma qG2_K {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 < D.1) (h2 : D.1 < C.1)
    (h3 : C.1 < B.1) : (qG2 h h1 h2 h3).K = convexHull ℝ {A, B, C, D} := by
  have hAB : A.1 < B.1 := (h1.trans h2).trans h3
  ext x
  simp only [QuadBody.K, qG2, body, mem_ofPred_eq, le_min_iff]
  constructor
  · rintro ⟨-, hL, hR1, hR2, hR3⟩
    rw [mem_hull_iff h, above hAB, below h3, below h2, below h1]
    exact ⟨hL, hR3, hR2, hR1⟩
  · intro hx
    have r := hull_strip (m := A.1) (M := B.1) ⟨le_rfl, hAB.le⟩ ⟨hAB.le, le_rfl⟩
      ⟨(h1.trans h2).le, h3.le⟩ ⟨h1.le, (h2.trans h3).le⟩ hx
    rw [mem_hull_iff h, above hAB, below h3, below h2, below h1] at hx
    exact ⟨r, hx.1, hx.2.2.2, hx.2.2.1, hx.2.1⟩

/-! ### Configuration `S1`: the side `AB` at the lowest level, then `C`, then `D` -/

section S1

variable {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 = B.1) (h2 : B.1 < C.1)
  (h3 : C.1 < D.1)
include h h1 h2 h3

lemma s1_below : B.2 < A.2 := by
  have := h.ab_c
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at this
  rw [h1, sub_self, zero_mul, zero_sub] at this
  have hC : 0 < C.1 - B.1 := sub_pos.2 h2
  nlinarith

lemma s1_sl : slp B C < slp C D := slp_lt h2 h3 h.bc_d

lemma s1_L_l {s : ℝ} (hs : s ≤ C.1) : max (lin B C s) (lin C D s) = lin B C s := by
  rw [lin_thru h2.ne s, lin_def C D s, nd_max_l (s1_sl h h1 h2 h3).le hs]

lemma s1_L_r {s : ℝ} (hs : C.1 ≤ s) : max (lin B C s) (lin C D s) = lin C D s := by
  rw [lin_thru h2.ne s, lin_def C D s, nd_max_r (s1_sl h h1 h2 h3).le hs]

lemma s1_half_ab (x : ℝ × ℝ) : 0 ≤ cross (B - A) (x - A) ↔ A.1 ≤ x.1 := by
  have hb := s1_below h h1 h2 h3
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  rw [← h1, sub_self, zero_mul, zero_sub, neg_nonneg]
  constructor
  · intro h'; by_contra hc; push Not at hc; nlinarith
  · intro h'; nlinarith

lemma s1_pairs : (∀ s ∈ Icc A.1 D.1, lin B C s ≤ lin D A s ∧ lin C D s ≤ lin D A s) ∧
    ∀ s ∈ Ioo A.1 D.1, lin B C s < lin D A s ∧ lin C D s < lin D A s := by
  have hb := s1_below h h1 h2 h3
  have hAD : A.1 < D.1 := (h1.trans_lt h2).trans h3
  have a1 : lin B C A.1 < lin D A A.1 := by rw [h1, lin_fst, ← h1, lin_snd hAD.ne']; exact hb
  have b1 : lin B C D.1 < lin D A D.1 := by
    rw [lin_fst]; exact (above_lt h2 D).1 h.bc_d
  have a2 : lin C D A.1 < lin D A A.1 := by
    rw [lin_snd hAD.ne']; exact (above_lt h3 A).1 h.cd_a
  have b2 : lin C D D.1 = lin D A D.1 := by rw [lin_fst, lin_snd h3.ne]
  exact ⟨fun s hs => ⟨lin_le hAD a1.le b1.le s hs, lin_le hAD a2.le b2.le s hs⟩,
    fun s hs => ⟨lin_lt hAD a1.le b1.le (Or.inl a1) s hs, lin_lt hAD a2.le b2.le (Or.inl a2) s hs⟩⟩

end S1

/-- The quadrilateral of configuration `S1` (chords parallel to the side `AB`) as a
`BentBody`. -/
def bS1 {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 = B.1) (h2 : B.1 < C.1)
    (h3 : C.1 < D.1) : BentBody where
  a := A.1
  t := C.1
  b := D.1
  hat := h1.trans_lt h2
  htb := h3
  L s := max (lin B C s) (lin C D s)
  R s := lin D A s
  contL := (continuous_lin B C).max (continuous_lin C D)
  contR := continuous_lin D A
  l₀ := slp B C
  l₁ := slp C D
  r₀ := slp D A
  r₁ := slp D A
  affL₀ s hs := by
    rw [s1_L_l h h1 h2 h3 hs.2, s1_L_l h h1 h2 h3 le_rfl, lin_eq B C s C.1]
  affL₁ s hs := by
    rw [s1_L_r h h1 h2 h3 hs.1, s1_L_r h h1 h2 h3 le_rfl, lin_eq C D s C.1]
  affR₀ s _ := lin_eq D A s C.1
  affR₁ s _ := lin_eq D A s C.1
  le s hs := max_le ((s1_pairs h h1 h2 h3).1 s hs).1 ((s1_pairs h h1 h2 h3).1 s hs).2
  pos s hs := max_lt ((s1_pairs h h1 h2 h3).2 s hs).1 ((s1_pairs h h1 h2 h3).2 s hs).2
  bent := by
    have := s1_sl h h1 h2 h3
    intro h'; linarith

lemma bS1_K {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : A.1 = B.1) (h2 : B.1 < C.1)
    (h3 : C.1 < D.1) :
    body (bS1 h h1 h2 h3).a (bS1 h h1 h2 h3).b (bS1 h h1 h2 h3).L (bS1 h h1 h2 h3).R =
      convexHull ℝ {A, B, C, D} := by
  have hAD : A.1 < D.1 := (h1.trans_lt h2).trans h3
  ext x
  simp only [bS1, body, mem_ofPred_eq]
  constructor
  · rintro ⟨hr, hL, hR⟩
    rw [mem_hull_iff h, s1_half_ab h h1 h2 h3, above h2, above h3, below hAD]
    exact ⟨hr.1, (le_max_left _ _).trans hL, (le_max_right _ _).trans hL, hR⟩
  · intro hx
    have r := hull_strip (m := A.1) (M := D.1) ⟨le_rfl, hAD.le⟩ ⟨h1.le, (h2.trans h3).le⟩
      ⟨(h1.trans_lt h2).le, h3.le⟩ ⟨hAD.le, le_rfl⟩ hx
    rw [mem_hull_iff h, s1_half_ab h h1 h2 h3, above h2, above h3, below hAD] at hx
    exact ⟨r, max_le hx.2.1 hx.2.2.1, hx.2.2.2⟩


/-! ### Configuration `D1`: the diagonal `AC` parallel to the chords, `D` lowest, `B` highest -/

/-- For chords parallel to the diagonal `AC`, the midpoints `D`, `(A + C) / 2`, `B` are collinear
exactly when the sums of the slopes of the two sides at `A, C` agree. -/
lemma cross_mid_eq {A B C D : ℝ × ℝ} (hC : C.1 = A.1) (hDA : D.1 ≠ A.1) (hAB : A.1 ≠ B.1) :
    cross (D - B) ((1 / 2 : ℝ) • (A + C) - B) =
      (A.1 - D.1) * (B.1 - A.1) / 2 * ((slp A B + slp B C) - (slp D A + slp C D)) := by
  have e1 : A.1 - D.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hDA)
  have e2 : B.1 - A.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hAB)
  have e3 : C.1 - B.1 ≠ 0 := by rw [hC]; exact sub_ne_zero.2 hAB
  have e4 : D.1 - C.1 ≠ 0 := by rw [hC]; exact sub_ne_zero.2 hDA
  simp only [cross, slp, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul]
  field_simp
  rw [hC]
  ring

section D1

variable {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : D.1 < A.1) (h2 : A.1 = C.1)
  (h3 : A.1 < B.1)
include h h1 h2 h3

lemma d1_sl : slp D A < slp A B := slp_lt h1 h3 h.da_b

lemma d1_su : slp B C < slp C D := by
  have := slp_gt (X := D) (Y := C) (Z := B) (h2 ▸ h1) (h2 ▸ h3)
    (by have := h.cd_b; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith)
  rwa [slp_comm C B, slp_comm D C] at this

lemma d1_L_l {s : ℝ} (hs : s ≤ A.1) : max (lin D A s) (lin A B s) = lin D A s := by
  rw [lin_thru h1.ne s, lin_def A B s, nd_max_l (d1_sl h h1 h2 h3).le hs]

lemma d1_L_r {s : ℝ} (hs : A.1 ≤ s) : max (lin D A s) (lin A B s) = lin A B s := by
  rw [lin_thru h1.ne s, lin_def A B s, nd_max_r (d1_sl h h1 h2 h3).le hs]

lemma d1_R_l {s : ℝ} (hs : s ≤ A.1) : min (lin C D s) (lin B C s) = lin C D s := by
  rw [lin_thru (P := B) (Q := C) (h2 ▸ h3).ne' s, lin_def C D s,
    nd_min_l (d1_su h h1 h2 h3).le (h2 ▸ hs)]

lemma d1_R_r {s : ℝ} (hs : A.1 ≤ s) : min (lin C D s) (lin B C s) = lin B C s := by
  rw [lin_thru (P := B) (Q := C) (h2 ▸ h3).ne' s, lin_def C D s,
    nd_min_r (d1_su h h1 h2 h3).le (h2 ▸ hs)]

lemma d1_pairs :
    (∀ s ∈ Icc D.1 B.1, max (lin D A s) (lin A B s) ≤ min (lin C D s) (lin B C s)) ∧
    ∀ s ∈ Ioo D.1 B.1, max (lin D A s) (lin A B s) < min (lin C D s) (lin B C s) := by
  have hDB : D.1 < B.1 := h1.trans h3
  have hDC : D.1 < C.1 := h2 ▸ h1
  have hCB : C.1 < B.1 := h2 ▸ h3
  -- values at the ends
  have uDB : lin D A B.1 < B.2 := (above_lt h1 B).1 h.da_b
  have uCDB : B.2 < lin C D B.1 := (below_lt hDC B).1 h.cd_b
  have uBCD : D.2 < lin B C D.1 := (below_lt hCB D).1 h.bc_d
  have uABD : lin A B D.1 < D.2 := (above_lt h3 D).1 h.ab_d
  have q1a : lin D A D.1 ≤ lin C D D.1 := by rw [lin_fst, lin_snd hDC.ne']
  have q2a : lin D A D.1 < lin B C D.1 := by rw [lin_fst]; exact uBCD
  have q2b : lin D A B.1 < lin B C B.1 := by rw [lin_fst]; exact uDB
  have q3a : lin A B D.1 < lin C D D.1 := by rw [lin_snd hDC.ne']; exact uABD
  have q3b : lin A B B.1 < lin C D B.1 := by rw [lin_snd h3.ne]; exact uCDB
  have q4a : lin A B D.1 < lin B C D.1 := uABD.trans uBCD
  have q4b : lin A B B.1 ≤ lin B C B.1 := by rw [lin_snd h3.ne, lin_fst]
  have q1b : lin D A B.1 < lin C D B.1 := uDB.trans uCDB
  refine ⟨fun s hs => max_le (le_min (lin_le hDB q1a q1b.le s hs) (lin_le hDB q2a.le q2b.le s hs))
    (le_min (lin_le hDB q3a.le q3b.le s hs) (lin_le hDB q4a.le q4b s hs)),
    fun s hs => max_lt (lt_min (lin_lt hDB q1a q1b.le (Or.inr q1b) s hs)
      (lin_lt hDB q2a.le q2b.le (Or.inl q2a) s hs))
      (lt_min (lin_lt hDB q3a.le q3b.le (Or.inl q3a) s hs)
        (lin_lt hDB q4a.le q4b (Or.inl q4a) s hs))⟩

end D1

/-- The quadrilateral of configuration `D1` (chords parallel to the diagonal `AC`) as a
`BentBody`; the bend is the condition that `BD` does not bisect `AC`. -/
def bD1 {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : D.1 < A.1) (h2 : A.1 = C.1)
    (h3 : A.1 < B.1) (hbis : cross (D - B) ((1 / 2 : ℝ) • (A + C) - B) ≠ 0) : BentBody where
  a := D.1
  t := A.1
  b := B.1
  hat := h1
  htb := h3
  L s := max (lin D A s) (lin A B s)
  R s := min (lin C D s) (lin B C s)
  contL := (continuous_lin D A).max (continuous_lin A B)
  contR := (continuous_lin C D).min (continuous_lin B C)
  l₀ := slp D A
  l₁ := slp A B
  r₀ := slp C D
  r₁ := slp B C
  affL₀ s hs := by
    rw [d1_L_l h h1 h2 h3 hs.2, d1_L_l h h1 h2 h3 le_rfl, lin_eq D A s A.1]
  affL₁ s hs := by
    rw [d1_L_r h h1 h2 h3 hs.1, d1_L_r h h1 h2 h3 le_rfl, lin_eq A B s A.1]
  affR₀ s hs := by
    rw [d1_R_l h h1 h2 h3 hs.2, d1_R_l h h1 h2 h3 le_rfl, lin_eq C D s A.1]
  affR₁ s hs := by
    rw [d1_R_r h h1 h2 h3 hs.1, d1_R_r h h1 h2 h3 le_rfl, lin_eq B C s A.1]
  le := (d1_pairs h h1 h2 h3).1
  pos := (d1_pairs h h1 h2 h3).2
  bent := by
    intro h'
    apply hbis
    rw [cross_mid_eq h2.symm h1.ne h3.ne]
    have : slp A B + slp B C - (slp D A + slp C D) = 0 := by linarith
    rw [this, mul_zero]

lemma bD1_K {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) (h1 : D.1 < A.1) (h2 : A.1 = C.1)
    (h3 : A.1 < B.1) (hbis : cross (D - B) ((1 / 2 : ℝ) • (A + C) - B) ≠ 0) :
    body (bD1 h h1 h2 h3 hbis).a (bD1 h h1 h2 h3 hbis).b (bD1 h h1 h2 h3 hbis).L
      (bD1 h h1 h2 h3 hbis).R = convexHull ℝ {A, B, C, D} := by
  have hDB : D.1 < B.1 := h1.trans h3
  have hDC : D.1 < C.1 := h2 ▸ h1
  have hCB : C.1 < B.1 := h2 ▸ h3
  ext x
  simp only [bD1, body, mem_ofPred_eq, le_min_iff, max_le_iff]
  constructor
  · rintro ⟨-, ⟨hL1, hL2⟩, hR1, hR2⟩
    rw [mem_hull_iff h, above h3, below hCB, below hDC, above h1]
    exact ⟨hL2, hR2, hR1, hL1⟩
  · intro hx
    have r := hull_strip (m := D.1) (M := B.1) ⟨h1.le, h3.le⟩ ⟨hDB.le, le_rfl⟩
      ⟨hDC.le, hCB.le⟩ ⟨le_rfl, hDB.le⟩ hx
    rw [mem_hull_iff h, above h3, below hCB, below hDC, above h1] at hx
    exact ⟨r, ⟨hx.2.2.2, hx.1⟩, hx.2.2.1, hx.2.1⟩


/-! ### Symmetries: the reflection `(s, y) ↦ (s, -y)` and the rotation `x ↦ -x` -/

/-- The reflection in the first axis; it keeps the level and the chords. -/
def flipY (x : ℝ × ℝ) : ℝ × ℝ := (x.1, -x.2)

lemma flipY_flipY (x : ℝ × ℝ) : flipY (flipY x) = x := by simp [flipY]

lemma image_flipY (S : Set (ℝ × ℝ)) : flipY '' S = flipY ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse flipY_flipY flipY_flipY) S

lemma image_neg' (S : Set (ℝ × ℝ)) : (fun x => -x) '' S = (fun x => -x) ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse (f := fun x : ℝ × ℝ => -x) neg_neg neg_neg) S

/-- The reflection of a `QuadBody` in the first axis. -/
def QuadBody.flip (B : QuadBody) : QuadBody where
  s₀ := B.s₀
  s₁ := B.s₁
  s₂ := B.s₂
  s₃ := B.s₃
  h01 := B.h01
  h12 := B.h12
  h23 := B.h23
  L s := -B.R s
  R s := -B.L s
  contL := B.contR.neg
  contR := B.contL.neg
  l₀ := -B.r₀
  l₁ := -B.r₁
  l₂ := -B.r₂
  r₀ := -B.l₀
  r₁ := -B.l₁
  r₂ := -B.l₂
  affL₀ s hs := by rw [B.affR₀ s hs]; ring
  affL₁ s hs := by rw [B.affR₁ s hs]; ring
  affL₂ s hs := by rw [B.affR₂ s hs]; ring
  affR₀ s hs := by rw [B.affL₀ s hs]; ring
  affR₁ s hs := by rw [B.affL₁ s hs]; ring
  affR₂ s hs := by rw [B.affL₂ s hs]; ring
  apex₀ := by rw [B.apex₀]
  apex₃ := by rw [B.apex₃]
  pos s hs := neg_lt_neg (B.pos s hs)
  vert₁ := by
    rcases B.vert₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by rw [h1], fun h => h2 (neg_injective h)⟩
    · exact Or.inl ⟨by rw [h1], fun h => h2 (neg_injective h)⟩
  vert₂ := by
    rcases B.vert₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by rw [h1], fun h => h2 (neg_injective h)⟩
    · exact Or.inl ⟨by rw [h1], fun h => h2 (neg_injective h)⟩

lemma QuadBody.flip_K (B : QuadBody) : B.flip.K = flipY '' B.K := by
  rw [image_flipY]
  ext x
  simp only [QuadBody.K, QuadBody.flip, body, mem_ofPred_eq, mem_preimage, flipY]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩

/-- The rotation by `π` of a `QuadBody`: the levels are negated and reversed. -/
def QuadBody.neg (B : QuadBody) : QuadBody where
  s₀ := -B.s₃
  s₁ := -B.s₂
  s₂ := -B.s₁
  s₃ := -B.s₀
  h01 := neg_lt_neg B.h23
  h12 := neg_lt_neg B.h12
  h23 := neg_lt_neg B.h01
  L s := -B.R (-s)
  R s := -B.L (-s)
  contL := (B.contR.comp continuous_neg).neg
  contR := (B.contL.comp continuous_neg).neg
  l₀ := B.r₂
  l₁ := B.r₁
  l₂ := B.r₀
  r₀ := B.l₂
  r₁ := B.l₁
  r₂ := B.l₀
  affL₀ s hs := by
    rw [neg_neg, B.affR₂ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B.affR₂ B.s₃ ⟨B.h23.le, le_rfl⟩]; ring
  affL₁ s hs := by
    rw [neg_neg, B.affR₁ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B.affR₁ B.s₂ ⟨B.h12.le, le_rfl⟩]; ring
  affL₂ s hs := by
    rw [neg_neg, B.affR₀ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B.affR₀ B.s₁ ⟨B.h01.le, le_rfl⟩]; ring
  affR₀ s hs := by
    rw [neg_neg, B.affL₂ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B.affL₂ B.s₃ ⟨B.h23.le, le_rfl⟩]; ring
  affR₁ s hs := by
    rw [neg_neg, B.affL₁ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B.affL₁ B.s₂ ⟨B.h12.le, le_rfl⟩]; ring
  affR₂ s hs := by
    rw [neg_neg, B.affL₀ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B.affL₀ B.s₁ ⟨B.h01.le, le_rfl⟩]; ring
  apex₀ := by rw [neg_neg, B.apex₃]
  apex₃ := by rw [neg_neg, B.apex₀]
  pos s hs := neg_lt_neg (B.pos (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  vert₁ := by
    rcases B.vert₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
  vert₂ := by
    rcases B.vert₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩

lemma QuadBody.neg_K (B : QuadBody) : B.neg.K = (fun x => -x) '' B.K := by
  rw [image_neg']
  ext x
  simp only [QuadBody.K, QuadBody.neg, body, mem_ofPred_eq, mem_preimage, Prod.fst_neg,
    Prod.snd_neg, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h1'⟩, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h1'⟩, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The reflection of a `BentBody` in the first axis. -/
def BentBody.flip (B : BentBody) : BentBody where
  a := B.a
  t := B.t
  b := B.b
  hat := B.hat
  htb := B.htb
  L s := -B.R s
  R s := -B.L s
  contL := B.contR.neg
  contR := B.contL.neg
  l₀ := -B.r₀
  l₁ := -B.r₁
  r₀ := -B.l₀
  r₁ := -B.l₁
  affL₀ s hs := by rw [B.affR₀ s hs]; ring
  affL₁ s hs := by rw [B.affR₁ s hs]; ring
  affR₀ s hs := by rw [B.affL₀ s hs]; ring
  affR₁ s hs := by rw [B.affL₁ s hs]; ring
  le s hs := neg_le_neg (B.le s hs)
  pos s hs := neg_lt_neg (B.pos s hs)
  bent h := B.bent (by linarith)

lemma BentBody.flip_body (B : BentBody) :
    body B.flip.a B.flip.b B.flip.L B.flip.R = flipY '' body B.a B.b B.L B.R := by
  rw [image_flipY]
  ext x
  simp only [BentBody.flip, body, mem_ofPred_eq, mem_preimage, flipY]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩

/-- The rotation by `π` of a `BentBody`. -/
def BentBody.neg (B : BentBody) : BentBody where
  a := -B.b
  t := -B.t
  b := -B.a
  hat := neg_lt_neg B.htb
  htb := neg_lt_neg B.hat
  L s := -B.R (-s)
  R s := -B.L (-s)
  contL := (B.contR.comp continuous_neg).neg
  contR := (B.contL.comp continuous_neg).neg
  l₀ := B.r₁
  l₁ := B.r₀
  r₀ := B.l₁
  r₁ := B.l₀
  affL₀ s hs := by
    rw [neg_neg, B.affR₁ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]; ring
  affL₁ s hs := by
    rw [neg_neg, B.affR₀ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]; ring
  affR₀ s hs := by
    rw [neg_neg, B.affL₁ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]; ring
  affR₁ s hs := by
    rw [neg_neg, B.affL₀ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]; ring
  le s hs := neg_le_neg (B.le (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  pos s hs := neg_lt_neg (B.pos (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  bent h := B.bent (by linarith)

lemma BentBody.neg_body (B : BentBody) :
    body B.neg.a B.neg.b B.neg.L B.neg.R = (fun x => -x) '' body B.a B.b B.L B.R := by
  rw [image_neg']
  ext x
  simp only [BentBody.neg, body, mem_ofPred_eq, mem_preimage, Prod.fst_neg, Prod.snd_neg,
    mem_Icc]
  constructor
  · rintro ⟨⟨h1, h1'⟩, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h1'⟩, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩


/-! ### Representations in chord coordinates and the case analysis -/

/-- `K` is represented in chord coordinates: either as a `QuadBody` whose vertex levels are the
levels of the points of `V`, labelled `P₀, Q₁, Q₂, P₃` in increasing order, or as a `BentBody`
(an excluded direction). -/
def Rep (V K : Set (ℝ × ℝ)) : Prop :=
  (∃ P₀ Q₁ Q₂ P₃ : ℝ × ℝ, V = {P₀, Q₁, Q₂, P₃} ∧ ∃ Bq : QuadBody, Bq.K = K ∧
      Bq.s₀ = P₀.1 ∧ Bq.s₁ = Q₁.1 ∧ Bq.s₂ = Q₂.1 ∧ Bq.s₃ = P₃.1) ∨
    ∃ Bb : BentBody, body Bb.a Bb.b Bb.L Bb.R = K

lemma Rep.flip {V K : Set (ℝ × ℝ)} (h : Rep V K) : Rep (flipY '' V) (flipY '' K) := by
  rcases h with ⟨P₀, Q₁, Q₂, P₃, hV, Bq, hK, e0, e1, e2, e3⟩ | ⟨Bb, hb⟩
  · refine Or.inl ⟨flipY P₀, flipY Q₁, flipY Q₂, flipY P₃, ?_, Bq.flip, ?_, e0, e1, e2, e3⟩
    · rw [hV]; simp only [image_insert_eq, image_singleton]
    · rw [Bq.flip_K, hK]
  · exact Or.inr ⟨Bb.flip, by rw [Bb.flip_body, hb]⟩

lemma Rep.neg {V K : Set (ℝ × ℝ)} (h : Rep V K) :
    Rep ((fun x => -x) '' V) ((fun x => -x) '' K) := by
  rcases h with ⟨P₀, Q₁, Q₂, P₃, hV, Bq, hK, e0, e1, e2, e3⟩ | ⟨Bb, hb⟩
  · refine Or.inl ⟨-P₃, -Q₂, -Q₁, -P₀, ?_, Bq.neg, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hV]; simp only [image_insert_eq, image_singleton]
      ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    · rw [Bq.neg_K, hK]
    all_goals simp only [QuadBody.neg, Prod.fst_neg, e0, e1, e2, e3]
  · exact Or.inr ⟨Bb.neg, by rw [Bb.neg_body, hb]⟩

/-- The reflection `flipY` as a linear map. -/
def flipYL : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ := (LinearMap.fst ℝ ℝ ℝ).prod (-LinearMap.snd ℝ ℝ ℝ)

lemma coe_flipYL : ⇑flipYL = flipY := rfl

lemma rep_of_flip {A B C D : ℝ × ℝ}
    (h : Rep {flipY A, flipY B, flipY C, flipY D}
      (convexHull ℝ {flipY A, flipY B, flipY C, flipY D})) :
    Rep {A, B, C, D} (convexHull ℝ {A, B, C, D}) := by
  have h' := h.flip
  rw [← coe_flipYL, LinearMap.image_convexHull] at h'
  simp only [coe_flipYL, image_insert_eq, image_singleton, flipY_flipY] at h'
  exact h'

lemma rep_of_neg {A B C D : ℝ × ℝ}
    (h : Rep {-A, -B, -C, -D} (convexHull ℝ {-A, -B, -C, -D})) :
    Rep {A, B, C, D} (convexHull ℝ {A, B, C, D}) := by
  have h' := h.neg
  have e : (fun x : ℝ × ℝ => -x) = ⇑(-LinearMap.id : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := rfl
  rw [e, LinearMap.image_convexHull] at h'
  rw [← e] at h'
  simp only [image_insert_eq, image_singleton, neg_neg] at h'
  exact h'

lemma rep_perm {V W : Set (ℝ × ℝ)} (e : V = W) (h : Rep V (convexHull ℝ V)) :
    Rep W (convexHull ℝ W) := e ▸ h

/-- The hypotheses of Proposition 87 on the quadrilateral `ABCD` (counterclockwise): convex,
not a trapezoid (no two opposite sides parallel), and neither diagonal bisects the other (the
line of one diagonal does not pass through the midpoint of the other). -/
structure QuadHyp (A B C D : ℝ × ℝ) : Prop where
  conv : ConvQuad A B C D
  trap₁ : cross (B - A) (D - C) ≠ 0
  trap₂ : cross (C - B) (A - D) ≠ 0
  bis₁ : cross (D - B) ((1 / 2 : ℝ) • (A + C) - B) ≠ 0
  bis₂ : cross (C - A) ((1 / 2 : ℝ) • (B + D) - A) ≠ 0

lemma QuadHyp.rot {A B C D : ℝ × ℝ} (h : QuadHyp A B C D) : QuadHyp B C D A where
  conv := ⟨h.conv.bc_d, h.conv.bc_a, h.conv.cd_a, h.conv.cd_b, h.conv.da_b, h.conv.da_c,
    h.conv.ab_c, h.conv.ab_d⟩
  trap₁ := h.trap₂
  trap₂ := fun e => h.trap₁ (by simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith)
  bis₁ := fun e => h.bis₂ (by
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul] at *; linarith)
  bis₂ := fun e => h.bis₁ (by
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul] at *; linarith)

lemma QuadHyp.neg {A B C D : ℝ × ℝ} (h : QuadHyp A B C D) : QuadHyp (-A) (-B) (-C) (-D) := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, t1, t2, b1, b2⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] at *; linarith)
  | (intro e
     first
     | exact t1 (by simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg,
          Prod.snd_neg] at *; linarith)
     | exact t2 (by simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg,
          Prod.snd_neg] at *; linarith)
     | exact b1 (by simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
          Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at *; linarith)
     | exact b2 (by simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
          Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at *; linarith))

lemma QuadHyp.flip {A B C D : ℝ × ℝ} (h : QuadHyp A B C D) :
    QuadHyp (flipY B) (flipY A) (flipY D) (flipY C) := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, t1, t2, b1, b2⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (simp only [cross, flipY, Prod.fst_sub, Prod.snd_sub] at *; linarith)
  | (intro e
     first
     | exact t1 (by simp only [cross, flipY, Prod.fst_sub, Prod.snd_sub] at *; linarith)
     | exact t2 (by simp only [cross, flipY, Prod.fst_sub, Prod.snd_sub] at *; linarith)
     | exact b1 (by simp only [cross, flipY, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at *; linarith)
     | exact b2 (by simp only [cross, flipY, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at *; linarith))

/-- The diagonals of a convex quadrilateral cross: their common point has the level
`A₁ + t (C₁ - A₁) = B₁ + u (D₁ - B₁)` with `t, u ∈ (0, 1)`. -/
lemma diag_level {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) :
    ∃ t u : ℝ, 0 < t ∧ t < 1 ∧ 0 < u ∧ u < 1 ∧ A.1 + t * (C.1 - A.1) = B.1 + u * (D.1 - B.1) := by
  have c1 := h.ab_c; have c2 := h.ab_d; have c3 := h.bc_d; have c5 := h.cd_a
  have hΔ : 0 < cross (C - A) (D - B) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith
  refine ⟨cross (B - A) (D - B) / cross (C - A) (D - B),
    cross (B - A) (C - A) / cross (C - A) (D - B), div_pos ?_ hΔ, ?_, div_pos c1 hΔ, ?_, ?_⟩
  · simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith
  · rw [div_lt_one hΔ]; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith
  · rw [div_lt_one hΔ]; simp only [cross, Prod.fst_sub, Prod.snd_sub] at *; linarith
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_eq_zero]
    have : A.1 + cross (B - A) (D - B) * (C.1 - A.1) / cross (C - A) (D - B) -
        (B.1 + cross (B - A) (C - A) * (D.1 - B.1) / cross (C - A) (D - B)) =
        (cross (C - A) (D - B) * (A.1 - B.1) + cross (B - A) (D - B) * (C.1 - A.1) -
          cross (B - A) (C - A) * (D.1 - B.1)) / cross (C - A) (D - B) := by
      field_simp; ring
    rw [this, div_eq_zero_iff]; left
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring


/-- The side `AB` at the lowest level. -/
lemma rep_side {A B C D : ℝ × ℝ} (h : QuadHyp A B C D) (hAB : A.1 = B.1) (hC : A.1 ≤ C.1)
    (hD : A.1 ≤ D.1) : Rep {A, B, C, D} (convexHull ℝ {A, B, C, D}) := by
  have hC' : A.1 < C.1 := by
    refine lt_of_le_of_ne hC fun e => ?_
    have := h.conv.ab_c
    simp only [cross, Prod.fst_sub, Prod.snd_sub] at this; rw [← hAB, ← e] at this; simp at this
  have hD' : A.1 < D.1 := by
    refine lt_of_le_of_ne hD fun e => ?_
    have := h.conv.ab_d
    simp only [cross, Prod.fst_sub, Prod.snd_sub] at this; rw [← hAB, ← e] at this; simp at this
  have hCD : C.1 ≠ D.1 := fun e => h.trap₁ (by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; rw [← hAB, e]; ring)
  rcases lt_or_gt_of_ne hCD with hCD | hCD
  · exact Or.inr ⟨bS1 h.conv hAB (hAB ▸ hC') hCD, bS1_K h.conv hAB (hAB ▸ hC') hCD⟩
  · have h' := h.flip
    refine rep_of_flip (rep_perm (V := {flipY B, flipY A, flipY D, flipY C}) ?_
      (Or.inr ⟨bS1 h'.conv (by simp [flipY, hAB]) (by simpa [flipY] using hD')
        (by simpa [flipY] using hCD), bS1_K h'.conv _ _ _⟩))
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-- The case analysis, with `A` at the lowest level. -/
lemma rep_amin {A B C D : ℝ × ℝ} (h : QuadHyp A B C D) (hB : A.1 ≤ B.1) (hC : A.1 ≤ C.1)
    (hD : A.1 ≤ D.1) : Rep {A, B, C, D} (convexHull ℝ {A, B, C, D}) := by
  obtain ⟨t, u, ht0, ht1, hu0, hu1, hX⟩ := diag_level h.conv
  rcases eq_or_lt_of_le hB with hAB | hAB
  · exact rep_side h hAB hC hD
  rcases eq_or_lt_of_le hD with hAD | hAD
  · refine rep_perm ?_ (rep_side h.rot.rot.rot hAD.symm (hAD ▸ hB) (hAD ▸ hC))
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  rcases eq_or_lt_of_le hC with hAC | hAC
  · exfalso; rw [← hAC] at hX; nlinarith
  have hq := h.conv
  rcases lt_trichotomy B.1 D.1 with hBD | hBD | hBD
  · rcases lt_trichotomy B.1 C.1 with hBC | hBC | hBC <;>
    rcases lt_trichotomy C.1 D.1 with hCD | hCD | hCD
    · -- `A < B < C < D`: the reflection of configuration `G2`
      refine rep_of_flip (rep_perm (V := {flipY A, flipY D, flipY C, flipY B}) ?_
        (Or.inl ⟨flipY A, flipY B, flipY C, flipY D, ?_, qG2 h.flip.rot.conv hAB hBC hCD,
          qG2_K _ _ _ _, rfl, rfl, rfl, rfl⟩)) <;>
      · ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    · -- the side `CD` at the highest level
      refine rep_of_neg (rep_perm (V := {-C, -D, -A, -B}) ?_ (rep_side h.neg.rot.rot
        (by simp only [Prod.fst_neg, hCD]) (by simp only [Prod.fst_neg]; linarith)
        (by simp only [Prod.fst_neg]; linarith)))
      ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    · exact Or.inl ⟨A, B, D, C, by ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto,
        qG1 hq hAB hBD hCD, qG1_K hq hAB hBD hCD, rfl, rfl, rfl, rfl⟩
    · exfalso; nlinarith
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; nlinarith
    · exfalso; linarith
    · exfalso; linarith
  · -- the diagonal `BD` parallel to the chords
    have hBC : B.1 < C.1 := by rw [← hBD, sub_self, mul_zero, add_zero] at hX; nlinarith
    refine rep_perm ?_ (Or.inr ⟨bD1 h.rot.conv hAB hBD hBC h.rot.bis₁,
      bD1_K h.rot.conv hAB hBD hBC h.rot.bis₁⟩)
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  · rcases lt_trichotomy B.1 C.1 with hBC | hBC | hBC <;>
    rcases lt_trichotomy C.1 D.1 with hCD | hCD | hCD
    · exfalso; linarith
    · exfalso; linarith
    · -- `A < D < B < C`: the reflection of configuration `G1`
      refine rep_of_flip (rep_perm (V := {flipY A, flipY D, flipY C, flipY B}) ?_
        (Or.inl ⟨flipY A, flipY D, flipY B, flipY C, ?_, qG1 h.flip.rot.conv hAD hBD hBC,
          qG1_K _ _ _ _, rfl, rfl, rfl, rfl⟩)) <;>
      · ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    · exfalso; linarith
    · exfalso; linarith
    · -- the side `BC` at the highest level
      refine rep_of_neg (rep_perm (V := {-B, -C, -D, -A}) ?_ (rep_side h.neg.rot
        (by simp only [Prod.fst_neg, hBC]) (by simp only [Prod.fst_neg]; linarith)
        (by simp only [Prod.fst_neg]; linarith)))
      ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    · exfalso; nlinarith
    · exfalso; rw [← hCD] at hBD; nlinarith
    · exact Or.inl ⟨A, D, C, B, by ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto,
        qG2 hq hAD hCD hBC, qG2_K hq hAD hCD hBC, rfl, rfl, rfl, rfl⟩

/-- **Every quadrilateral satisfying the hypotheses has a chord-coordinate representation.** -/
theorem rep_all {A B C D : ℝ × ℝ} (h : QuadHyp A B C D) :
    Rep {A, B, C, D} (convexHull ℝ {A, B, C, D}) := by
  have pB : ({B, C, D, A} : Set (ℝ × ℝ)) = {A, B, C, D} := by
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  have pC : ({C, D, A, B} : Set (ℝ × ℝ)) = {A, B, C, D} := by
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  have pD : ({D, A, B, C} : Set (ℝ × ℝ)) = {A, B, C, D} := by
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  rcases le_total A.1 B.1 with h1 | h1 <;> rcases le_total C.1 D.1 with h2 | h2
  · rcases le_total A.1 C.1 with h3 | h3
    · exact rep_amin h h1 h3 (h3.trans h2)
    · exact rep_perm pC (rep_amin h.rot.rot h2 h3 (h3.trans h1))
  · rcases le_total A.1 D.1 with h3 | h3
    · exact rep_amin h h1 (h3.trans h2) h3
    · exact rep_perm pD (rep_amin h.rot.rot.rot h3 (h3.trans h1) h2)
  · rcases le_total B.1 C.1 with h3 | h3
    · exact rep_perm pB (rep_amin h.rot h3 (h3.trans h2) h1)
    · exact rep_perm pC (rep_amin h.rot.rot h2 (h3.trans h1) h3)
  · rcases le_total B.1 D.1 with h3 | h3
    · exact rep_perm pB (rep_amin h.rot (h3.trans h2) h3 h1)
    · exact rep_perm pD (rep_amin h.rot.rot.rot (h3.trans h1) h3 h2)


/-! ### A general direction of the chords -/

open ProbabilityTheory in
instance isSFiniteKernel_chordKernel (L R : ℝ → ℝ) : IsSFiniteKernel (chordKernel L R) := by
  unfold chordKernel; infer_instance

/-- For a direction `e` of the chords, the coordinates `T_e x = (e × x, e · x)`: the first
coordinate is the level `e × x = e₁ x₂ - e₂ x₁`, constant along the chords (the lines parallel to
`e`), and the second is the position along the chord. -/
def TeL (e : ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun x := (e.1 * x.2 - e.2 * x.1, e.1 * x.1 + e.2 * x.2)
  map_add' x y := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The inverse of `T_e` (for `e ≠ 0`). -/
def TeInv (e : ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun p := ((-e.2 * p.1 + e.1 * p.2) / (e.1 ^ 2 + e.2 ^ 2),
    (e.1 * p.1 + e.2 * p.2) / (e.1 ^ 2 + e.2 ^ 2))
  map_add' x y := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

lemma TeL_fst (e x : ℝ × ℝ) : (TeL e x).1 = cross e x := rfl

lemma norm2_pos {e : ℝ × ℝ} (he : e ≠ 0) : 0 < e.1 ^ 2 + e.2 ^ 2 := by
  rcases e with ⟨a, b⟩
  have : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h; exact he (by simp [h.1, h.2])
  rcases this with h | h
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; simp only; positivity
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; simp only; positivity

lemma TeInv_TeL {e : ℝ × ℝ} (he : e ≠ 0) (x : ℝ × ℝ) : TeInv e (TeL e x) = x := by
  have := (norm2_pos he).ne'
  simp only [TeInv, TeL, LinearMap.coe_mk, AddHom.coe_mk]
  ext <;> simp only <;> field_simp <;> ring

lemma TeL_TeInv {e : ℝ × ℝ} (he : e ≠ 0) (p : ℝ × ℝ) : TeL e (TeInv e p) = p := by
  have := (norm2_pos he).ne'
  simp only [TeInv, TeL, LinearMap.coe_mk, AddHom.coe_mk]
  ext <;> simp only <;> field_simp <;> ring

/-- `T_e` as a linear equivalence. -/
def TeE {e : ℝ × ℝ} (he : e ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.ofLinearMap (TeL e) (TeInv e)
    (LinearMap.ext fun p => TeL_TeInv he p) (LinearMap.ext fun x => TeInv_TeL he x)
    ).toContinuousLinearEquiv

lemma coe_TeE {e : ℝ × ℝ} (he : e ≠ 0) : ⇑(TeE he) = TeL e := rfl

lemma det_TeL_ne {e : ℝ × ℝ} (he : e ≠ 0) : LinearMap.det (TeL e) ≠ 0 :=
  (LinearEquiv.isUnit_det' (LinearEquiv.ofLinearMap (TeL e) (TeInv e)
    (LinearMap.ext fun p => TeL_TeInv he p) (LinearMap.ext fun x => TeInv_TeL he x))).ne_zero

lemma cross_TeL (e u v : ℝ × ℝ) :
    cross (TeL e u) (TeL e v) = -(e.1 ^ 2 + e.2 ^ 2) * cross u v := by
  simp only [cross, TeL, LinearMap.coe_mk, AddHom.coe_mk]; ring

lemma cross_TeInv {e : ℝ × ℝ} (he : e ≠ 0) (u v : ℝ × ℝ) :
    cross (TeInv e u) (TeInv e v) = -(e.1 ^ 2 + e.2 ^ 2)⁻¹ * cross u v := by
  have h := cross_TeL e (TeInv e u) (TeInv e v)
  rw [TeL_TeInv he, TeL_TeInv he] at h
  have := (norm2_pos he).ne'
  rw [h]; field_simp

lemma measurable_TeL (e : ℝ × ℝ) : Measurable (TeL e) :=
  (TeL e).continuous_of_finiteDimensional.measurable

/-- The lower end of the chord at level `s` of a set `S` in chord coordinates. -/
def chordLo (S : Set (ℝ × ℝ)) (s : ℝ) : ℝ := sInf {y | (s, y) ∈ S}

/-- The upper end of the chord at level `s` of a set `S` in chord coordinates. -/
def chordHi (S : Set (ℝ × ℝ)) (s : ℝ) : ℝ := sSup {y | (s, y) ∈ S}

/-- **Sliced triples in the direction `e`**: in the coordinates `T_e` (level, position along the
chord), given the levels of its points, each point of the triple is uniformly distributed on its
chord (`IsSliced`, with the chords of `T_e K`). -/
def IsSlicedIn (K : Set (ℝ × ℝ)) (e : ℝ × ℝ) (P : Measure (Fin 3 → ℝ × ℝ)) : Prop :=
  IsSliced (chordLo (TeL e '' K)) (chordHi (TeL e '' K)) (P.map fun x i => TeL e (x i))

/-- The midpoint of the chord of `K` in the direction `e` at level `s` (a point with
`e × x = s`). -/
def chordMid (K : Set (ℝ × ℝ)) (e : ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  TeInv e (mid (chordLo (TeL e '' K)) (chordHi (TeL e '' K)) s)

lemma slice_body {a b : ℝ} {L R : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc a b) :
    {y | (s, y) ∈ body a b L R} = Icc (L s) (R s) := by
  ext y; simp only [body, mem_ofPred_eq, mem_Icc]; exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩

lemma slice_body_out {a b : ℝ} {L R : ℝ → ℝ} {s : ℝ} (hs : s ∉ Icc a b) :
    {y | (s, y) ∈ body a b L R} = ∅ := by
  ext y; simp only [body, mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact fun h => hs h.1

lemma chordLo_body {a b : ℝ} {L R : ℝ → ℝ} (hLR : ∀ s ∈ Icc a b, L s ≤ R s) :
    chordLo (body a b L R) = fun s => if s ∈ Icc a b then L s else 0 := by
  funext s
  split_ifs with hs
  · rw [chordLo, slice_body hs, csInf_Icc (hLR s hs)]
  · rw [chordLo, slice_body_out hs, Real.sInf_empty]

lemma chordHi_body {a b : ℝ} {L R : ℝ → ℝ} (hLR : ∀ s ∈ Icc a b, L s ≤ R s) :
    chordHi (body a b L R) = fun s => if s ∈ Icc a b then R s else 0 := by
  funext s
  split_ifs with hs
  · rw [chordHi, slice_body hs, csSup_Icc (hLR s hs)]
  · rw [chordHi, slice_body_out hs, Real.sSup_empty]

open ProbabilityTheory in
lemma chordKernel_apply' {L R : ℝ → ℝ} (hL : Measurable L) (hR : Measurable R) (s : ℝ) :
    chordKernel L R s = unit01.map fun t => (s, L s + t * (R s - L s)) := by
  rw [chordKernel, Kernel.map_apply _ (by unfold chordPt; fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by unfold chordPt; fun_prop) measurable_prodMk_left]
  rfl

/-- The slicing condition only involves the chords at levels that the points take. -/
lemma isSliced_congr {L R L' R' : ℝ → ℝ} {a b : ℝ} (hL : Measurable L) (hR : Measurable R)
    (hL' : Measurable L') (hR' : Measurable R') (he : ∀ s ∈ Icc a b, L s = L' s ∧ R s = R' s)
    {P : Measure (Fin 3 → ℝ × ℝ)} (hae : ∀ i : Fin 3, ∀ᵐ x ∂P, (x i).1 ∈ Icc a b)
    (h : IsSliced L R P) : IsSliced L' R' P := by
  intro i
  rw [h i]
  apply Measure.compProd_congr
  have : ∀ᵐ s ∂(P.map lev3), s i ∈ Icc a b := by
    rw [ae_map_iff measurable_lev3.aemeasurable
      (measurableSet_Icc.preimage (measurable_pi_apply i))]
    exact hae i
  filter_upwards [this] with s hs
  rw [ProbabilityTheory.Kernel.comap_apply, ProbabilityTheory.Kernel.comap_apply,
    chordKernel_apply' hL hR, chordKernel_apply' hL' hR', (he _ hs).1, (he _ hs).2]

/-- A linear bijection carries a complete mix of `U(K)` to one of `U(T K)`. -/
lemma isCompleteMix_map {T : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ} (hT : LinearMap.det T ≠ 0)
    {K : Set (ℝ × ℝ)} {P : Measure (Fin 3 → ℝ × ℝ)} (h : IsCompleteMix 3 (unifSet K) P) :
    IsCompleteMix 3 (unifSet (T '' K)) (P.map fun x i => T (x i)) := by
  obtain ⟨hp, ⟨s, hs⟩, hm⟩ := h
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have hF : Measurable fun (x : Fin 3 → ℝ × ℝ) (i : Fin 3) => T (x i) :=
    by fun_prop
  refine ⟨(Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 hp, ⟨T s, ?_⟩, fun j => ?_⟩
  · rw [ae_map_iff hF.aemeasurable
      (isClosed_eq (by fun_prop) continuous_const).measurableSet]
    filter_upwards [hs] with x hx
    rw [← hx, map_sum]
  · rw [Measure.map_map (measurable_pi_apply j) hF]
    have : ((fun x : Fin 3 → ℝ × ℝ => x j) ∘ fun x i => T (x i)) =
        T ∘ fun x : Fin 3 → ℝ × ℝ => x j := rfl
    rw [this, ← Measure.map_map hTm (measurable_pi_apply j), hm j]
    simpa using unifSet_map_affine K hT 0


/-! ### The quadrilateral of the paper -/

/-- The hypotheses of Proposition 87 on the quadrilateral with vertices `A, B, C, D` in this
cyclic order (either orientation): convex position, not a trapezoid (`AB ∦ CD`, `BC ∦ DA`), and
neither diagonal bisects the other (the line `BD` misses the midpoint of `AC`, and the line `AC`
misses the midpoint of `BD`). -/
structure IsQuad (A B C D : ℝ × ℝ) : Prop where
  conv : ConvQuad A B C D ∨ ConvQuad A D C B
  trap₁ : cross (B - A) (D - C) ≠ 0
  trap₂ : cross (C - B) (A - D) ≠ 0
  bis₁ : cross (D - B) (midpoint ℝ A C - B) ≠ 0
  bis₂ : cross (C - A) (midpoint ℝ B D - A) ≠ 0

lemma midpoint_eq_half (x y : ℝ × ℝ) : midpoint ℝ x y = (1 / 2 : ℝ) • (x + y) := by
  rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]

lemma IsQuad.hyp {A B C D : ℝ × ℝ} (h : IsQuad A B C D) :
    QuadHyp A B C D ∨ QuadHyp A D C B := by
  have b1 := h.bis₁; have b2 := h.bis₂
  rw [midpoint_eq_half] at b1 b2
  rcases h.conv with c | c
  · exact Or.inl ⟨c, h.trap₁, h.trap₂, b1, b2⟩
  · refine Or.inr ⟨c, fun e => h.trap₂ ?_, fun e => h.trap₁ ?_, fun e => b1 ?_, fun e => b2 ?_⟩ <;>
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul] at * <;> linarith

lemma IsQuad.rep {A B C D : ℝ × ℝ} (h : IsQuad A B C D) :
    Rep {A, B, C, D} (convexHull ℝ {A, B, C, D}) := by
  rcases h.hyp with q | q
  · exact rep_all q
  · refine rep_perm ?_ (rep_all q)
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-- The convexity conditions of the reversed quadrilateral, all negative. -/
structure ConvQuadN (A B C D : ℝ × ℝ) : Prop where
  ab_c : cross (B - A) (C - A) < 0
  ab_d : cross (B - A) (D - A) < 0
  bc_d : cross (C - B) (D - B) < 0
  bc_a : cross (C - B) (A - B) < 0
  cd_a : cross (D - C) (A - C) < 0
  cd_b : cross (D - C) (B - C) < 0
  da_b : cross (A - D) (B - D) < 0
  da_c : cross (A - D) (C - D) < 0

lemma ConvQuad.rev {A B C D : ℝ × ℝ} (h : ConvQuad A B C D) : ConvQuadN A D C B := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  constructor <;> simp only [cross, Prod.fst_sub, Prod.snd_sub] at * <;> linarith

lemma ConvQuad.map {A B C D : ℝ × ℝ} {T : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ} {k : ℝ} (hk : 0 < k)
    (hT : ∀ u v, cross (T u) (T v) = k * cross u v) (h : ConvQuad A B C D) :
    ConvQuad (T A) (T B) (T C) (T D) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  constructor <;> rw [← map_sub, ← map_sub, hT] <;> positivity

lemma ConvQuadN.map {A B C D : ℝ × ℝ} {T : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ} {k : ℝ} (hk : k < 0)
    (hT : ∀ u v, cross (T u) (T v) = k * cross u v) (h : ConvQuadN A B C D) :
    ConvQuad (T A) (T B) (T C) (T D) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  constructor <;> rw [← map_sub, ← map_sub, hT] <;> exact mul_pos_of_neg_of_neg hk ‹_›

lemma IsQuad.map {A B C D : ℝ × ℝ} {T : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ} {k : ℝ} (hk : k ≠ 0)
    (hT : ∀ u v, cross (T u) (T v) = k * cross u v) (h : IsQuad A B C D) :
    IsQuad (T A) (T B) (T C) (T D) := by
  have hmid : ∀ x y, T (midpoint ℝ x y) = midpoint ℝ (T x) (T y) := fun x y => by
    rw [midpoint_eq_half, midpoint_eq_half, map_smul, map_add]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases h.conv with c | c <;> rcases lt_or_gt_of_ne hk with hk' | hk'
    · exact Or.inr (c.rev.map hk' hT)
    · exact Or.inl (c.map hk' hT)
    · exact Or.inl (c.rev.map hk' hT)
    · exact Or.inr (c.map hk' hT)
  · rw [← map_sub, ← map_sub, hT]; exact mul_ne_zero hk h.trap₁
  · rw [← map_sub, ← map_sub, hT]; exact mul_ne_zero hk h.trap₂
  · rw [← hmid, ← map_sub, ← map_sub, hT]; exact mul_ne_zero hk h.bis₁
  · rw [← hmid, ← map_sub, ← map_sub, hT]; exact mul_ne_zero hk h.bis₂

lemma IsQuad.ne {A B C D : ℝ × ℝ} (h : IsQuad A B C D) :
    A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D := by
  have key : ∀ {X Y Z : ℝ × ℝ}, cross (Y - X) (Z - X) ≠ 0 → X ≠ Y ∧ X ≠ Z := by
    intro X Y Z hc
    refine ⟨fun e => hc ?_, fun e => hc ?_⟩ <;> subst e <;> simp [cross]
  rcases h.conv with c | c
  · exact ⟨(key c.ab_c.ne').1, (key c.bc_d.ne').1, (key c.cd_a.ne').1, (key c.da_b.ne').1,
      (key c.ab_c.ne').2, (key c.bc_d.ne').2⟩
  · exact ⟨fun e => (key c.da_b.ne').1 e.symm, fun e => (key c.cd_a.ne').1 e.symm,
      fun e => (key c.bc_d.ne').1 e.symm, fun e => (key c.ab_c.ne').1 e.symm,
      (key c.ab_c.ne').2,
      fun e => (key c.bc_d.ne').2 e.symm⟩

lemma lev_ne {f : ℝ × ℝ → ℝ} {P₀ Q₁ Q₂ P₃ x y : ℝ × ℝ} (h01 : f P₀ < f Q₁) (h12 : f Q₁ < f Q₂)
    (h23 : f Q₂ < f P₃) (hx : x ∈ ({P₀, Q₁, Q₂, P₃} : Set (ℝ × ℝ)))
    (hy : y ∈ ({P₀, Q₁, Q₂, P₃} : Set (ℝ × ℝ))) (hxy : x ≠ y) : f x ≠ f y := by
  simp only [mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | (intro e; linarith)

/-- The slicing condition for the chords of `K'` transfers to any representation of `K'` as a
body between two continuous graphs. -/
lemma sliced_of_body {K' : Set (ℝ × ℝ)} {P' : Measure (Fin 3 → ℝ × ℝ)}
    (hP' : IsCompleteMix 3 (unifSet K') P') {a b : ℝ} {L R : ℝ → ℝ} (hL : Continuous L)
    (hR : Continuous R) (hLR : ∀ s ∈ Icc a b, L s ≤ R s) (hK : K' = body a b L R)
    (hsl : IsSliced (chordLo K') (chordHi K') P') : IsSliced L R P' := by
  subst hK
  have h1 : ∀ᵐ y ∂(unifSet (body a b L R)), y.1 ∈ Icc a b := by
    unfold unifSet
    exact Measure.ae_smul_measure ((ae_restrict_mem (isClosed_body hL hR).measurableSet).mono
      fun y hy => hy.1) _
  refine isSliced_congr (a := a) (b := b) ?_ ?_ hL.measurable hR.measurable ?_ ?_ hsl
  · rw [chordLo_body hLR]; exact Measurable.ite measurableSet_Icc hL.measurable measurable_const
  · rw [chordHi_body hLR]; exact Measurable.ite measurableSet_Icc hR.measurable measurable_const
  · intro s hs; rw [chordLo_body hLR, chordHi_body hLR]; simp [hs]
  · intro i
    have hm : P'.map (fun x => x i) = unifSet (body a b L R) := hP'.2.2 i
    rw [← hm] at h1
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h1


lemma image_TeL {e : ℝ × ℝ} (he : e ≠ 0) (S : Set (ℝ × ℝ)) : TeL e '' S = TeInv e ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse (TeInv_TeL he) (TeL_TeInv he)) S

lemma volume_image_TeL (e : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    volume (TeL e '' S) = ENNReal.ofReal |LinearMap.det (TeL e)| * volume S :=
  Measure.addHaar_image_linearMap volume (TeL e) S

/-- **Proposition 87** (`st:prop:quad`) for the quadrilateral `K = conv {A, B, C, D}` of the
paper. Let `ABCD` be convex, not a trapezoid, and such that neither diagonal bisects the other
(`IsQuad`), let `e ≠ 0` be the direction of the chords (the level of `x` is `e × x`), and let
`P` be a `3`-complete mix of `U(K)` that is sliced in this direction. Then:
* the chords are parallel to no side and no diagonal;
* the vertices, labelled `P₀, Q₁, Q₂, P₃` by increasing level `s₀ < s₁ < s₂ < s₃`, are such that
  the chord midpoints `m s` lie on three segments `σ₁ = m [s₀, s₁]`, `σ₂ = m [s₁, s₂]`,
  `σ₃ = m [s₂, s₃]` with directions `w₀, w₁, w₂`, starting at the apex `P₀ = m s₀` and ending at
  the apex `P₃ = m s₃`; adjacent segments are not parallel;
* the centroid `c` lies on `σ₂`;
* if moreover `c` is not an endpoint of `σ₂` and `σ₁ ∦ σ₃`, then the two triangles
  `{s₀ < e × x < s₁}` and `{s₂ < e × x < s₃}` of `K` have equal areas and `3c - P₀ - P₃ ∈ σ₂`. -/
theorem prop87_quad {A B C D e : ℝ × ℝ} (he : e ≠ 0) (hq : IsQuad A B C D)
    {P : Measure (Fin 3 → ℝ × ℝ)}
    (hP : IsCompleteMix 3 (unifSet (convexHull ℝ {A, B, C, D})) P)
    (hsl : IsSlicedIn (convexHull ℝ {A, B, C, D}) e P) :
    let K := convexHull ℝ {A, B, C, D}
    let m := chordMid K e
    let c := ∫ x, x ∂(unifSet K)
    (cross e (B - A) ≠ 0 ∧ cross e (C - B) ≠ 0 ∧ cross e (D - C) ≠ 0 ∧ cross e (A - D) ≠ 0 ∧
      cross e (C - A) ≠ 0 ∧ cross e (D - B) ≠ 0) ∧
    ∃ P₀ Q₁ Q₂ P₃ : ℝ × ℝ, ({P₀, Q₁, Q₂, P₃} : Set (ℝ × ℝ)) = {A, B, C, D} ∧
      cross e P₀ < cross e Q₁ ∧ cross e Q₁ < cross e Q₂ ∧ cross e Q₂ < cross e P₃ ∧
      ∃ w₀ w₁ w₂ : ℝ × ℝ,
        m (cross e P₀) = P₀ ∧ m (cross e P₃) = P₃ ∧
        (∀ s ∈ Icc (cross e P₀) (cross e Q₁), m s = P₀ + (s - cross e P₀) • w₀) ∧
        (∀ s ∈ Icc (cross e Q₁) (cross e Q₂), m s = m (cross e Q₁) + (s - cross e Q₁) • w₁) ∧
        (∀ s ∈ Icc (cross e Q₂) (cross e P₃), m s = m (cross e Q₂) + (s - cross e Q₂) • w₂) ∧
        cross w₀ w₁ ≠ 0 ∧ cross w₁ w₂ ≠ 0 ∧
        c ∈ m '' Icc (cross e Q₁) (cross e Q₂) ∧
        (c ∈ m '' Ioo (cross e Q₁) (cross e Q₂) → cross w₀ w₂ ≠ 0 →
          volume (K ∩ {x | cross e x ∈ Ioo (cross e P₀) (cross e Q₁)}) =
            volume (K ∩ {x | cross e x ∈ Ioo (cross e Q₂) (cross e P₃)}) ∧
          (3 : ℝ) • c - P₀ - P₃ ∈ m '' Icc (cross e Q₁) (cross e Q₂)) := by
  intro K m c
  have hdet := det_TeL_ne he
  have hinv : ∀ x, TeInv e (TeL e x) = x := TeInv_TeL he
  have hinv' : ∀ p, TeL e (TeInv e p) = p := TeL_TeInv he
  have hTK : TeL e '' K = convexHull ℝ {TeL e A, TeL e B, TeL e C, TeL e D} := by
    simp only [K, LinearMap.image_convexHull, image_insert_eq, image_singleton]
  have hq' : IsQuad (TeL e A) (TeL e B) (TeL e C) (TeL e D) :=
    hq.map (neg_ne_zero.2 (norm2_pos he).ne') (cross_TeL e)
  have hrep : Rep {TeL e A, TeL e B, TeL e C, TeL e D} (TeL e '' K) := by
    rw [hTK]; exact hq'.rep
  have hP' : IsCompleteMix 3 (unifSet (TeL e '' K)) (P.map fun x i => TeL e (x i)) :=
    isCompleteMix_map hdet hP
  rcases hrep with ⟨P₀', Q₁', Q₂', P₃', hV, Bq, hBK, e0, e1, e2, e3⟩ | ⟨Bb, hb⟩
  swap
  · exfalso
    have hsl' := sliced_of_body hP' Bb.contL Bb.contR Bb.le hb.symm hsl
    rw [← hb] at hP'
    exact Bb.no_sliced _ hP' hsl'
  -- the generic direction
  have hBK' : TeL e '' K = body Bq.s₀ Bq.s₃ Bq.L Bq.R := hBK.symm
  have hsl' : IsSliced Bq.L Bq.R (P.map fun x i => TeL e (x i)) :=
    sliced_of_body hP' Bq.contL Bq.contR Bq.le' hBK' hsl
  have hP'' : IsCompleteMix 3 (unifSet Bq.K) (P.map fun x i => TeL e (x i)) := hBK ▸ hP'
  obtain ⟨h1, h2, h3, h4⟩ := Bq.prop87 _ hP'' hsl'
  have hc : ∫ x, x ∂(unifSet Bq.K) = TeL e c := by
    have hmap : (unifSet K).map (TeL e) = unifSet (TeL e '' K) := by
      simpa using unifSet_map_affine K hdet 0
    have := integral_map (μ := unifSet K) (measurable_TeL e).aemeasurable
      (f := fun y : ℝ × ℝ => y) aestronglyMeasurable_id
    rw [hBK, ← hmap, this]
    exact (TeE he).integral_comp_comm id
  have hm : ∀ s ∈ Icc Bq.s₀ Bq.s₃, m s = TeInv e (mid Bq.L Bq.R s) := by
    intro s hs
    simp only [m, chordMid]
    rw [hBK', chordLo_body Bq.le', chordHi_body Bq.le']
    simp only [mid, hs, ite_true]
  -- the labelling of the vertices of `K`
  have hPV : ({TeInv e P₀', TeInv e Q₁', TeInv e Q₂', TeInv e P₃'} : Set (ℝ × ℝ)) =
      {A, B, C, D} := by
    have := congrArg (image (TeInv e)) hV
    simp only [image_insert_eq, image_singleton, hinv] at this
    exact this.symm
  have lev : ∀ p, cross e (TeInv e p) = p.1 := fun p => by rw [← TeL_fst, hinv']
  have hmemK : ∀ p ∈ ({P₀', Q₁', Q₂', P₃'} : Set (ℝ × ℝ)), p ∈ Bq.K := by
    intro p hp
    rw [hBK, hTK, hV]
    exact subset_convexHull ℝ _ hp
  have apex0 : P₀' = (Bq.s₀, Bq.L Bq.s₀) := by
    have hp := hmemK P₀' (by simp)
    simp only [QuadBody.K, body, mem_ofPred_eq] at hp
    have := Bq.apex₀
    refine Prod.ext e0.symm ?_
    show P₀'.2 = Bq.L Bq.s₀
    rw [e0] at this ⊢; linarith [hp.2.1, hp.2.2]
  have apex3 : P₃' = (Bq.s₃, Bq.L Bq.s₃) := by
    have hp := hmemK P₃' (by simp)
    simp only [QuadBody.K, body, mem_ofPred_eq] at hp
    have := Bq.apex₃
    refine Prod.ext e3.symm ?_
    show P₃'.2 = Bq.L Bq.s₃
    rw [e3] at this ⊢; linarith [hp.2.1, hp.2.2]
  have mid0 : mid Bq.L Bq.R Bq.s₀ = P₀' := by
    rw [apex0]; simp only [mid, Bq.apex₀]; ext <;> simp only; ring
  have mid3 : mid Bq.L Bq.R Bq.s₃ = P₃' := by
    rw [apex3]; simp only [mid, Bq.apex₃]; ext <;> simp only; ring
  have hs01 := Bq.h01
  have hs12 := Bq.h12
  have hs23 := Bq.h23
  have a0 : ∀ s ∈ Icc Bq.s₀ Bq.s₁, mid Bq.L Bq.R s =
      mid Bq.L Bq.R Bq.s₀ + (s - Bq.s₀) • Bq.toQuad3.v₀ := Bq.toQuad3.aff₀
  have a1 : ∀ s ∈ Icc Bq.s₁ Bq.s₂, mid Bq.L Bq.R s =
      mid Bq.L Bq.R Bq.s₁ + (s - Bq.s₁) • Bq.toQuad3.v₁ := Bq.toQuad3.aff₁
  have a2 : ∀ s ∈ Icc Bq.s₂ Bq.s₃, mid Bq.L Bq.R s =
      mid Bq.L Bq.R Bq.s₂ + (s - Bq.s₂) • Bq.toQuad3.v₂ := Bq.toQuad3.aff₂
  have hcr : ∀ u v, cross (TeInv e u) (TeInv e v) = -(e.1 ^ 2 + e.2 ^ 2)⁻¹ * cross u v :=
    cross_TeInv he
  have hn : -(e.1 ^ 2 + e.2 ^ 2)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (norm2_pos he).ne')
  have h03 : Bq.s₀ < Bq.s₃ := (hs01.trans hs12).trans hs23
  have lv01 : cross e (TeInv e P₀') < cross e (TeInv e Q₁') := by
    rw [lev, lev, ← e0, ← e1]; exact hs01
  have lv12 : cross e (TeInv e Q₁') < cross e (TeInv e Q₂') := by
    rw [lev, lev, ← e1, ← e2]; exact hs12
  have lv23 : cross e (TeInv e Q₂') < cross e (TeInv e P₃') := by
    rw [lev, lev, ← e2, ← e3]; exact hs23
  refine ⟨?_, TeInv e P₀', TeInv e Q₁', TeInv e Q₂', TeInv e P₃', hPV, lv01, lv12, lv23,
    TeInv e Bq.toQuad3.v₀, TeInv e Bq.toQuad3.v₁, TeInv e Bq.toQuad3.v₂, ?_⟩
  · -- no two vertices at the same level
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hq.ne
    have mem : ∀ x ∈ ({A, B, C, D} : Set (ℝ × ℝ)),
        x ∈ ({TeInv e P₀', TeInv e Q₁', TeInv e Q₂', TeInv e P₃'} : Set (ℝ × ℝ)) := by
      intro x hx; rwa [hPV]
    have hne : ∀ x ∈ ({A, B, C, D} : Set (ℝ × ℝ)), ∀ y ∈ ({A, B, C, D} : Set (ℝ × ℝ)),
        x ≠ y → cross e (x - y) ≠ 0 := fun x hx y hy hxy => by
      rw [cross_sub]; exact sub_ne_zero.2 (lev_ne lv01 lv12 lv23 (mem x hx) (mem y hy) hxy)
    exact ⟨hne B (by simp) A (by simp) n1.symm, hne C (by simp) B (by simp) n2.symm,
      hne D (by simp) C (by simp) n3.symm, hne A (by simp) D (by simp) n4.symm,
      hne C (by simp) A (by simp) n5.symm, hne D (by simp) B (by simp) n6.symm⟩
  simp only [lev, ← e0, ← e1, ← e2, ← e3]
  have i01 : ∀ s ∈ Icc Bq.s₀ Bq.s₁, s ∈ Icc Bq.s₀ Bq.s₃ := fun s hs =>
    ⟨hs.1, hs.2.trans (hs12.trans hs23).le⟩
  have i12 : ∀ s ∈ Icc Bq.s₁ Bq.s₂, s ∈ Icc Bq.s₀ Bq.s₃ := fun s hs =>
    ⟨hs01.le.trans hs.1, hs.2.trans hs23.le⟩
  have i23 : ∀ s ∈ Icc Bq.s₂ Bq.s₃, s ∈ Icc Bq.s₀ Bq.s₃ := fun s hs =>
    ⟨(hs01.trans hs12).le.trans hs.1, hs.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm _ ⟨le_rfl, h03.le⟩, mid0]
  · rw [hm _ ⟨h03.le, le_rfl⟩, mid3]
  · intro s hs
    rw [hm s (i01 s hs), a0 s hs, mid0, map_add, map_smul]
  · intro s hs
    rw [hm s (i12 s hs), hm _ (i12 _ ⟨le_rfl, hs12.le⟩), a1 s hs, map_add, map_smul]
  · intro s hs
    rw [hm s (i23 s hs), hm _ (i23 _ ⟨le_rfl, hs23.le⟩), a2 s hs, map_add, map_smul]
  · rw [hcr]; exact mul_ne_zero hn h1
  · rw [hcr]; exact mul_ne_zero hn h2
  · obtain ⟨s, hs, hcs⟩ := h3
    refine ⟨s, hs, ?_⟩
    rw [hm s (i12 s hs), hcs, hc, hinv]
  · intro hc' hw
    have hc'' : ∫ x, x ∂(unifSet Bq.K) ∈ mid Bq.L Bq.R '' Ioo Bq.s₁ Bq.s₂ := by
      obtain ⟨s, hs, hms⟩ := hc'
      refine ⟨s, hs, ?_⟩
      rw [hc, ← hms, hm s (i12 s (Ioo_subset_Icc_self hs)), hinv']
    have hv : cross Bq.toQuad3.v₀ Bq.toQuad3.v₂ ≠ 0 := fun h0 => hw (by rw [hcr, h0, mul_zero])
    obtain ⟨hvol, hpt⟩ := h4 hc'' hv
    constructor
    · have himg : ∀ I : Set ℝ, TeL e '' (K ∩ {x | cross e x ∈ I}) = Bq.K ∩ Prod.fst ⁻¹' I := by
        intro I
        rw [image_TeL he, preimage_inter, ← image_TeL he, ← hBK]
        congr 1
        ext p; simp only [mem_preimage, mem_ofPred_eq, lev]
      rw [← himg, ← himg, volume_image_TeL, volume_image_TeL] at hvol
      have h0 : ENNReal.ofReal |LinearMap.det (TeL e)| ≠ 0 := by
        simpa [ENNReal.ofReal_eq_zero, not_le] using hdet
      exact (ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top).1 hvol
    · obtain ⟨s, hs, hms⟩ := hpt
      refine ⟨s, hs, ?_⟩
      rw [hm s (i12 s hs), hms, hc, ← apex0, ← apex3, map_sub, map_sub, map_smul, hinv]

end Mixes.Quad
