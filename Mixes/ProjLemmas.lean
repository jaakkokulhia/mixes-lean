import Mixes.Defs

/-!
# Projections onto proper subspaces: the three lemmas (Section `pj:sec:proj`)

Lemmas `pj:lem:three`, `pj:lem:example` and `pj:lem:gadget` of the paper.

## Notation

* `tr v ν = ν.map (· + v)`: the translate `τ_v ν`.
* `twoPoint w = ½ (δ_w + δ_{-w})`.
* `ZeroSumMixable G`: there are random vectors `X_i ∼ G_i` with `∑ X_i = 0` (a joint mix with
  sum `0`).
* `DeconvEq G₁ Q w m`: equation `(pj:eq:deconv)` `Q = τ_w m + τ_{-w}(G₁ - m)` for a finite signed
  measure `m`, evaluated on measurable sets.

## Main results

* `three_a`: **Lemma pj:lem:three (a)**.
* `three_b`: **Lemma pj:lem:three (b)**.
* `ex_isProb_Q`, `ex_Qf_nonneg`, `ex_Qf_le`, `ex_Q_compl`, `ex_mean`: **Lemma pj:lem:example (i)**
  (with `ex_deconv`: `Q = τ_w m₀ + τ_{-w}(G₁ - m₀)`).
* `ex_not_jointlyMixable`: **Lemma pj:lem:example (ii)**.
* `ex_map_jointlyMixable`: **Lemma pj:lem:example (iii)**.
* `gadget_a`, `gadget_b`: **Lemma pj:lem:gadget (a), (b)**.

## Differences from the paper

* Lemma three: the spaces are real normed spaces with Borel σ-algebra, second countable (e.g.
  `ℝ^d`). Part (b) is stated with `DeconvEq`, i.e. equation `(pj:eq:deconv)` on measurable sets.
  In (a) the proof's `m(A) = P(X₁ ∈ A, X₃ = w)` has mass `½` only for `w ≠ 0`; for `w = 0` the
  formalisation takes `m = G₁ / 2`.
* Lemma example: `ℝ^d = EuclideanSpace ℝ (Fin d)`. `Q` is defined by its density `exQf`, and
  `m₀` as `m₀⁺ - m₀⁻` (`exMP`, `exMN`), whose density is `μ / |D|`; `ex_KI` is the definition of
  `Q` as an identity of positive measures. The bound of the density is `3 / |D|`. Part (iii) is
  proved for linear maps into any real normed space; the proof reduces to lines in the kernel
  (`line_le`: chord lengths `2 √(r² - s)`), which covers subspaces of every dimension `j ≥ 1`.
* Lemma gadget: the index `i` runs over `Fin n` (the paper's `i + 1`). Part (a) needs none of the
  hypotheses on `e`, `λ`, supports or means; the uniform random permutation is replaced by a
  uniform random cyclic shift. Part (b) derives `ρ₀ ≥ 0` from the hypotheses.
-/

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Mixes.ProjLemmas

section General

variable {E : Type*} [MeasurableSpace E] [AddCommGroup E]

/-- The translate `τ_v ν` of a measure, `τ_v ν (A) = ν (A - v)`. -/
def tr (v : E) (ν : Measure E) : Measure E := ν.map (· + v)

/-- The distribution `½ (δ_w + δ_{-w})` on the two points `± w`. -/
def twoPoint (w : E) : Measure E := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac w + Measure.dirac (-w))

/-- There are random vectors `X_j ∼ G j` with `∑ X_j = 0`: a joint mix of the `G j` with sum
`0`. -/
def ZeroSumMixable {n : ℕ} (G : Fin n → Measure E) : Prop :=
  ∃ P : Measure (Fin n → E), IsProbabilityMeasure P ∧ (∀ᵐ x ∂P, ∑ j, x j = 0) ∧
    ∀ j, P.map (fun x => x j) = G j

/-- Equation `(pj:eq:deconv)`, `Q = τ_w m + τ_{-w} (G₁ - m)`, for a finite signed measure `m`,
evaluated on every measurable set `A`: `τ_w m (A) = m (A - w)`, `τ_{-w} ν (A) = ν (A + w)`. -/
def DeconvEq (G₁ Q : Measure E) (w : E) (m : SignedMeasure E) : Prop :=
  ∀ A, MeasurableSet A →
    (Q A).toReal = m ((· + w) ⁻¹' A) + (G₁ ((· - w) ⁻¹' A)).toReal - m ((· - w) ⁻¹' A)

end General

/-! ## Lemma pj:lem:three -/

section Three

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

lemma measurableSet_sum_eq {n : ℕ} (s : E) : MeasurableSet {x : Fin n → E | ∑ j, x j = s} :=
  measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const

lemma map_neg_neg (Q : Measure E) : (Q.map Neg.neg).map Neg.neg = Q := by
  rw [Measure.map_map measurable_neg measurable_neg]
  have : (Neg.neg ∘ Neg.neg : E → E) = id := funext fun x => neg_neg x
  rw [this, Measure.map_id]

lemma twoPoint_isProb (w : E) : IsProbabilityMeasure (twoPoint w) := by
  constructor
  simp only [twoPoint, smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- **Lemma pj:lem:three (a)**: for distributions `G₁`, `Q`, the distributions `G₁`, `G₂ = (-)_# Q`
and `G₃ = ½(δ_w + δ_{-w})` admit `X_i ∼ G_i` with `X₁ + X₂ + X₃ = 0` iff there is a measure `m`
with `0 ≤ m ≤ G₁`, `m(ℝ^d) = ½` and `Q = τ_w m + τ_{-w}(G₁ - m)`. Here `w` may vanish. -/
theorem three_a (G₁ Q : Measure E) [IsProbabilityMeasure G₁] [IsProbabilityMeasure Q] (w : E) :
    ZeroSumMixable (n := 3) ![G₁, Q.map Neg.neg, twoPoint w] ↔
      ∃ m : Measure E, m ≤ G₁ ∧ m univ = 2⁻¹ ∧ Q = tr w m + tr (-w) (G₁ - m) := by
  constructor
  · rintro ⟨P, hP, hsum, hmarg⟩
    have h0 : P.map (fun x => x 0) = G₁ := hmarg 0
    have h1 : P.map (fun x => x 1) = Q.map Neg.neg := hmarg 1
    have h2 : P.map (fun x => x 2) = twoPoint w := hmarg 2
    -- the law of `X₁ + X₃` is `Q`
    have hQ : P.map (fun x => x 0 + x 2) = Q := by
      have : P.map (fun x => x 0 + x 2) = P.map (fun x => -x 1) := by
        apply Measure.map_congr
        filter_upwards [hsum] with x hx
        simp only [Fin.sum_univ_three] at hx
        rw [eq_neg_iff_add_eq_zero]; rw [← hx]; abel
      have hm1 : Measurable (fun x : Fin 3 → E => x 1) := measurable_pi_apply 1
      rw [this, show (fun x : Fin 3 → E => -x 1) = Neg.neg ∘ (fun x => x 1) from rfl,
        ← Measure.map_map measurable_neg hm1, h1, map_neg_neg]
    by_cases hw : w = 0
    · subst hw
      refine ⟨(2⁻¹ : NNReal) • G₁, ?_, ?_, ?_⟩
      · intro s
        simp only [smul_apply, ENNReal.smul_def, smul_eq_mul]
        calc ((2⁻¹ : NNReal) : ℝ≥0∞) * G₁ s ≤ 1 * G₁ s := by gcongr; norm_num
          _ = G₁ s := one_mul _
      · simp
      · have hx2 : ∀ᵐ x ∂P, x 2 = 0 := by
          rw [ae_iff]
          show P ((fun f => f 2) ⁻¹' {0}ᶜ) = 0
          rw [← Measure.map_apply (measurable_pi_apply 2) (measurableSet_singleton 0).compl, h2]
          simp [twoPoint]
        have : P.map (fun x => x 0 + x 2) = G₁ := by
          rw [← h0]; apply Measure.map_congr
          filter_upwards [hx2] with x hx; simp [hx]
        rw [← hQ, this]
        simp only [tr, neg_zero, add_zero, Measure.map_id']
        rw [add_comm, Measure.sub_add_cancel_of_le]
        intro s
        simp only [smul_apply, ENNReal.smul_def, smul_eq_mul]
        calc ((2⁻¹ : NNReal) : ℝ≥0∞) * G₁ s ≤ 1 * G₁ s := by gcongr; norm_num
          _ = G₁ s := one_mul _
    · have hm0 : Measurable (fun x : Fin 3 → E => x 0) := measurable_pi_apply 0
      have hm2 : Measurable (fun x : Fin 3 → E => x 2) := measurable_pi_apply 2
      set S : Set (Fin 3 → E) := (fun x => x 2) ⁻¹' {w} with hS
      have hSm : MeasurableSet S := hm2 (measurableSet_singleton w)
      have hwne : w ≠ -w := by
        intro h
        apply hw
        have : (2 : ℝ) • w = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel w
        exact (smul_eq_zero.1 this).resolve_left two_ne_zero
      -- off `S`, the third coordinate is `-w`
      have hoff : ∀ᵐ x ∂P.restrict Sᶜ, x 2 = -w := by
        have hall : ∀ᵐ x ∂P, x 2 = w ∨ x 2 = -w := by
          rw [ae_iff]
          show P ((fun f => f 2) ⁻¹' ({w, -w} : Set E)ᶜ) = 0
          rw [← Measure.map_apply hm2 (measurableSet_insert.2 (measurableSet_singleton _)).compl, h2]
          simp [twoPoint, hwne.symm]
        rw [ae_restrict_iff' hSm.compl]
        filter_upwards [hall] with x hx hxS
        exact hx.resolve_left hxS
      set m := (P.restrict S).map (fun x => x 0) with hmdef
      have hsplit : (P.restrict S).map (fun x => x 0) + (P.restrict Sᶜ).map (fun x => x 0) = G₁ := by
        rw [← Measure.map_add _ _ hm0, Measure.restrict_add_restrict_compl hSm, h0]
      have hmle : m ≤ G₁ := by
        rw [← hsplit]; exact Measure.le_add_right le_rfl
      have : IsFiniteMeasure m := by rw [hmdef]; infer_instance
      have hrest : G₁ - m = (P.restrict Sᶜ).map (fun x => x 0) := by
        rw [← hsplit, add_comm, Measure.add_sub_cancel]
      refine ⟨m, hmle, ?_, ?_⟩
      · rw [hmdef, Measure.map_apply hm0 MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply_univ, hS, ← Measure.map_apply hm2 (measurableSet_singleton w), h2]
        simp [twoPoint, hwne.symm]
      · have hm02 : Measurable (fun x : Fin 3 → E => x 0 + x 2) := hm0.add hm2
        rw [← hQ, hrest]
        conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P) hSm]
        rw [Measure.map_add _ _ hm02]
        congr 1
        · rw [tr, hmdef, Measure.map_map (measurable_add_const w) hm0]
          apply Measure.map_congr
          rw [Filter.EventuallyEq, ae_restrict_iff' hSm]
          exact Filter.Eventually.of_forall fun x hx => by simp only [Function.comp]; rw [show x 2 = w from hx]
        · rw [tr, Measure.map_map (measurable_add_const (-w)) hm0]
          apply Measure.map_congr
          filter_upwards [hoff] with x hx
          simp only [Function.comp]; rw [hx]
  · rintro ⟨m, hmle, hm, hQ⟩
    have : IsFiniteMeasure m := isFiniteMeasure_of_le G₁ hmle
    set f₁ : E → Fin 3 → E := fun x => ![x, -(x + w), w]
    set f₂ : E → Fin 3 → E := fun x => ![x, -(x + -w), -w]
    have hf₁ : Measurable f₁ := by
      rw [measurable_pi_iff]; intro j; fin_cases j <;> simp [f₁] <;> fun_prop
    have hf₂ : Measurable f₂ := by
      rw [measurable_pi_iff]; intro j; fin_cases j <;> simp [f₂] <;> fun_prop
    have hGm : m + (G₁ - m) = G₁ := by rw [add_comm, Measure.sub_add_cancel_of_le hmle]
    have hmarg : ∀ j, (m.map f₁ + (G₁ - m).map f₂).map (fun x => x j) =
        ![G₁, Q.map Neg.neg, twoPoint w] j := by
      intro j
      rw [Measure.map_add _ _ (measurable_pi_apply j), Measure.map_map (measurable_pi_apply j) hf₁,
        Measure.map_map (measurable_pi_apply j) hf₂]
      fin_cases j
      · simp [f₁, f₂, Function.comp_def, hGm]
      · show m.map (fun x => -(x + w)) + (G₁ - m).map (fun x => -(x + -w)) = Q.map Neg.neg
        rw [hQ, tr, tr, Measure.map_add _ _ measurable_neg,
          Measure.map_map measurable_neg (measurable_add_const _),
          Measure.map_map measurable_neg (measurable_add_const _)]
        rfl
      · show m.map (fun _ => w) + (G₁ - m).map (fun _ => -w) = twoPoint w
        rw [Measure.map_const, Measure.map_const, hm, Measure.sub_apply MeasurableSet.univ hmle, hm,
          measure_univ, ENNReal.one_sub_inv_two, twoPoint, smul_add]
    refine ⟨m.map f₁ + (G₁ - m).map f₂, ?_, ?_, hmarg⟩
    · constructor
      have hm0 : Measurable (fun x : Fin 3 → E => x 0) := measurable_pi_apply 0
      rw [← preimage_univ (f := fun x : Fin 3 → E => x 0), ← Measure.map_apply hm0 MeasurableSet.univ,
        hmarg 0]
      exact measure_univ (μ := G₁)
    · rw [ae_iff]
      have : {x : Fin 3 → E | ¬ ∑ j, x j = 0} = {x | ∑ j, x j = 0}ᶜ := rfl
      rw [this, add_apply, Measure.map_apply hf₁ (measurableSet_sum_eq 0).compl,
        Measure.map_apply hf₂ (measurableSet_sum_eq 0).compl]
      have e1 : f₁ ⁻¹' {x : Fin 3 → E | ∑ j, x j = 0}ᶜ = ∅ := by
        ext x; simp [f₁, Fin.sum_univ_three]
      have e2 : f₂ ⁻¹' {x : Fin 3 → E | ∑ j, x j = 0}ᶜ = ∅ := by
        ext x; simp [f₂, Fin.sum_univ_three]
      rw [e1, e2]; simp


/-- A finite signed measure invariant under the translation by `u ≠ 0` vanishes on every
measurable subset of a ball of radius `‖u‖ / 2`. -/
lemma vanish_small {σ : SignedMeasure E} {u : E}
    (hσ : ∀ B, MeasurableSet B → σ ((· + u) ⁻¹' B) = σ B) {c : E} {B : Set E}
    (hB : MeasurableSet B) (hBc : B ⊆ ball c (‖u‖ / 2)) : σ B = 0 := by
  set T : ℕ → Set E := fun k => (· + (k : ℝ) • u) ⁻¹' B
  have hTm : ∀ k, MeasurableSet (T k) := fun k => (measurable_add_const _) hB
  have hTσ : ∀ k, σ (T k) = σ B := by
    intro k
    induction k with
    | zero => simp [T]
    | succ k ih =>
      have : T (k + 1) = (· + u) ⁻¹' T k := by
        ext x; simp only [T, mem_preimage, Nat.cast_succ, add_smul, one_smul]; rw [add_assoc,
          add_comm u]
      rw [this, hσ _ (hTm k), ih]
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    have hi := hBc hxi
    have hj := hBc hxj
    rw [mem_ball] at hi hj
    have hu : 0 < ‖u‖ := by
      by_contra h
      have : ‖u‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
      rw [this, zero_div] at hi; exact absurd hi (not_lt.2 dist_nonneg)
    have h1 : dist (x + (i : ℝ) • u) (x + (j : ℝ) • u) < ‖u‖ := by
      calc _ ≤ dist (x + (i : ℝ) • u) c + dist c (x + (j : ℝ) • u) := dist_triangle _ _ _
        _ < ‖u‖ / 2 + ‖u‖ / 2 := by rw [dist_comm c]; exact add_lt_add hi hj
        _ = ‖u‖ := by ring
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs] at h1
    have hz : (1 : ℤ) ≤ |(i : ℤ) - j| := Int.one_le_abs (sub_ne_zero.2 (by exact_mod_cast hij))
    have : (1 : ℝ) ≤ |(i : ℝ) - j| := by exact_mod_cast hz
    nlinarith
  have hs := σ.hasSum_of_disjoint_iUnion hTm hdisj
  simp only [hTσ] at hs
  by_contra hne
  exact hne (summable_const_iff (σ B) |>.1 hs.summable)

/-- **Lemma pj:lem:three (b)**: if `w ≠ 0`, at most one finite signed measure `m` satisfies
`(pj:eq:deconv)`. -/
theorem three_b {G₁ Q : Measure E} {w : E} (hw : w ≠ 0) {m₁ m₂ : SignedMeasure E}
    (h₁ : DeconvEq G₁ Q w m₁) (h₂ : DeconvEq G₁ Q w m₂) : m₁ = m₂ := by
  set σ := m₁ - m₂
  have hinv : ∀ B, MeasurableSet B → σ ((· + (2 : ℝ) • w) ⁻¹' B) = σ B := by
    intro B hB
    have hA : MeasurableSet ((· + w) ⁻¹' B) := (measurable_add_const w) hB
    have e1 := h₁ _ hA
    have e2 := h₂ _ hA
    have p1 : (· + w) ⁻¹' ((· + w) ⁻¹' B) = (· + (2 : ℝ) • w) ⁻¹' B := by
      ext x; simp only [mem_preimage, two_smul, add_assoc]
    have p2 : (· - w) ⁻¹' ((· + w) ⁻¹' B) = B := by
      ext x; simp
    rw [p1, p2] at e1 e2
    simp only [σ, sub_apply]
    linarith
  have hu : ‖(2 : ℝ) • w‖ / 2 > 0 := by
    have := norm_pos_iff.2 hw; rw [norm_smul, Real.norm_two]; linarith
  rw [← sub_eq_zero]
  ext A hA
  rw [zero_apply]
  -- cover by countably many small balls
  set r := ‖(2 : ℝ) • w‖ / 2
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq E
  set U : ℕ → Set E := fun k => A ∩ ball (c k) r
  have hcov : (⋃ k, U k) = A := by
    apply Subset.antisymm (iUnion_subset fun k => inter_subset_left)
    intro x hx
    obtain ⟨k, hk⟩ := (hc.exists_dist_lt x hu)
    exact mem_iUnion.2 ⟨k, hx, hk⟩
  have hUm : ∀ k, MeasurableSet (U k) := fun k => hA.inter measurableSet_ball
  rw [← hcov, ← iUnion_disjointed]
  have hs := σ.hasSum_of_disjoint_iUnion (MeasurableSet.disjointed hUm) (disjoint_disjointed U)
  have h0 : ∀ k, σ (disjointed U k) = 0 := fun k =>
    vanish_small hinv (MeasurableSet.disjointed hUm k)
      ((disjointed_subset U k).trans inter_subset_right)
  simp only [h0] at hs
  exact hs.unique hasSum_zero


/-- A solution `m ≤ G₁` of `(pj:eq:deconv)` in the sense of measures solves it as a signed
measure. -/
lemma deconvEq_of_measure {G₁ Q m : Measure E} [IsFiniteMeasure G₁] [IsFiniteMeasure m] {w : E}
    (hle : m ≤ G₁) (hQ : Q = tr w m + tr (-w) (G₁ - m)) : DeconvEq G₁ Q w m.toSignedMeasure := by
  intro A hA
  have hA1 : MeasurableSet ((· + w) ⁻¹' A) := (measurable_add_const w) hA
  have hA2 : MeasurableSet ((· - w) ⁻¹' A) := (measurable_sub_const w) hA
  have e : (fun x : E => x + -w) = (· - w) := funext fun x => (sub_eq_add_neg x w).symm
  rw [hQ, add_apply, tr, tr, Measure.map_apply (measurable_add_const w) hA,
    Measure.map_apply (measurable_add_const (-w)) hA, e, Measure.sub_apply hA2 hle,
    Measure.toSignedMeasure_apply_measurable hA1, Measure.toSignedMeasure_apply_measurable hA2,
    ENNReal.toReal_add (measure_ne_top _ _) (by simp [ENNReal.sub_eq_top_iff, measure_ne_top]),
    ENNReal.toReal_sub_of_le (hle _) (measure_ne_top _ _), measureReal_def, measureReal_def]
  ring

end Three

/-! ## Lemma pj:lem:example -/

section Example

/-- `κ = 9/10`. -/
def exKappa : ℝ := 9 / 10

/-- `c = κ 4^{-d}`. -/
def exC (d : ℕ) : ℝ := exKappa * (1 / 4 : ℝ) ^ d

/-- The indicator function `𝟏_S` with real values. -/
def ind {α : Type*} (S : Set α) : α → ℝ := S.indicator fun _ => 1

/-- `|D|`, the volume of the closed unit ball `D` of `ℝ^d`. -/
def exVol (d : ℕ) : ℝ := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- `μ = (½ + c) 𝟏_D - κ 𝟏_E`, with `D` the closed unit ball and `E = ¼ D`. -/
def exMu (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 + exC d) * ind (closedBall 0 1) x - exKappa * ind (closedBall 0 (1 / 4)) x

/-- The density of `Q = τ_w m₀ + τ_{-w}(G₁ - m₀)`:
`x ↦ (μ(x - w) + (𝟏_D - μ)(x + w)) / |D|`. -/
def exQf (d : ℕ) (w x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (exMu d (x - w) + (ind (closedBall 0 1) (x + w) - exMu d (x + w))) / exVol d

/-- `G₁ = U(D)`. -/
def exG1 (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) := unifSet (closedBall 0 1)

/-- The distribution `Q`, with density `exQf d w`. -/
def exQ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) : Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensity fun x => ENNReal.ofReal (exQf d w x)

/-- The three distributions `G₁ = U(D)`, `G₂ = (-)_# Q`, `G₃ = ½(δ_w + δ_{-w})` of
Lemma pj:lem:example. -/
def exG (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) : Fin 3 → Measure (EuclideanSpace ℝ (Fin d)) :=
  ![exG1 d, (exQ d w).map Neg.neg, twoPoint w]

variable {d : ℕ} {w : EuclideanSpace ℝ (Fin d)}


lemma volume_sq_le (a : ℝ) : volume {t : ℝ | t ^ 2 ≤ a} = ENNReal.ofReal (2 * √a) := by
  rcases lt_or_ge a 0 with ha | ha
  · have : {t : ℝ | t ^ 2 ≤ a} = ∅ := by
      ext t; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ha (sq_nonneg t)
    rw [this, Real.sqrt_eq_zero'.2 ha.le]; simp
  · have : {t : ℝ | t ^ 2 ≤ a} = Icc (-√a) (√a) := by
      ext t
      simp only [mem_ofPred_eq, mem_Icc, ← abs_le]
      constructor
      · exact Real.abs_le_sqrt
      · intro h
        calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
          _ ≤ (√a) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) h 2
          _ = a := Real.sq_sqrt ha
    rw [this, Real.volume_Icc]; congr 1; ring

/-- The chord inequality behind Lemma pj:lem:example (iii), in coordinates `ℝ × ℝ^k`: for a set
`A₀` of the base, the cylinder `ℝ × A₀` meets the ball of radius `r` in at most `r / R` times the
volume in which it meets the ball of radius `R ≥ r`. -/
lemma cyl_le (k : ℕ) {A₀ : Set (Fin k → ℝ)} (hA₀ : MeasurableSet A₀) {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ≤ R) (hR0 : 0 < R) :
    volume {p : ℝ × (Fin k → ℝ) | p.2 ∈ A₀ ∧ p.1 ^ 2 + ∑ i, p.2 i ^ 2 ≤ r ^ 2} ≤
      ENNReal.ofReal (r / R) *
        volume {p : ℝ × (Fin k → ℝ) | p.2 ∈ A₀ ∧ p.1 ^ 2 + ∑ i, p.2 i ^ 2 ≤ R ^ 2} := by
  have hm : ∀ ρ : ℝ, MeasurableSet {p : ℝ × (Fin k → ℝ) | p.2 ∈ A₀ ∧ p.1 ^ 2 + ∑ i, p.2 i ^ 2 ≤ ρ ^ 2} :=
    fun ρ => (measurable_snd hA₀).inter (measurableSet_le (by fun_prop : Measurable fun p : ℝ × (Fin k → ℝ) => p.1 ^ 2 + ∑ i, p.2 i ^ 2) measurable_const)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (hm r), Measure.prod_apply_symm (hm R),
    ← lintegral_const_mul _ (by
      exact measurable_measure_prodMk_right (hm R))]
  apply lintegral_mono
  intro y
  simp only []
  by_cases hy : y ∈ A₀
  · have e : ∀ ρ : ℝ, (fun t => (t, y)) ⁻¹'
        {p : ℝ × (Fin k → ℝ) | p.2 ∈ A₀ ∧ p.1 ^ 2 + ∑ i, p.2 i ^ 2 ≤ ρ ^ 2} =
        {t : ℝ | t ^ 2 ≤ ρ ^ 2 - ∑ i, y i ^ 2} := by
      intro ρ; ext t; simp only [mem_preimage, mem_ofPred_eq, hy, true_and]; constructor <;>
        intro h <;> linarith
    rw [e, e, volume_sq_le, volume_sq_le, ← ENNReal.ofReal_mul (div_nonneg hr (hr.trans hrR))]
    apply ENNReal.ofReal_le_ofReal
    have hs : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hq : 0 ≤ r / R := div_nonneg hr hR0.le
    have hle : r ^ 2 - ∑ i, y i ^ 2 ≤ (r / R) ^ 2 * (R ^ 2 - ∑ i, y i ^ 2) := by
      have h1 : (r / R) ^ 2 ≤ 1 := by
        rw [div_pow]; exact (div_le_one (by positivity)).2 (pow_le_pow_left₀ hr hrR 2)
      have h2 : (r / R) ^ 2 * R ^ 2 = r ^ 2 := by field_simp
      nlinarith
    have := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq] at this
    nlinarith
  · have e : ∀ ρ : ℝ, (fun t => (t, y)) ⁻¹'
        {p : ℝ × (Fin k → ℝ) | p.2 ∈ A₀ ∧ p.1 ^ 2 + ∑ i, p.2 i ^ 2 ≤ ρ ^ 2} = ∅ := by
      intro ρ; ext t; simp [hy]
    rw [e, e]; simp


/-- Coordinates `x ↦ (x₀, (x_{i+1})_i)` on `ℝ^{k+1}`. -/
def coordE (k : ℕ) : EuclideanSpace ℝ (Fin (k + 1)) ≃ᵐ ℝ × (Fin k → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)

lemma coordE_mp (k : ℕ) : MeasurePreserving (coordE k) volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (k + 1))
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure ℝ)) 0
  exact h2.comp h1

lemma coordE_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    coordE k x = (x 0, fun i => x i.succ) := by
  rfl

lemma coordE_shift (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) (c : ℝ) :
    coordE k (x + c • EuclideanSpace.single 0 1) = (x 0 + c, (coordE k x).2) := by
  rw [coordE_apply, coordE_apply]
  simp [Fin.succ_ne_zero]

lemma normsq_coordE (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ‖x‖ ^ 2 = (coordE k x).1 ^ 2 + ∑ i, (coordE k x).2 i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, coordE_apply, Fin.sum_univ_succ]
  simp

/-- Lemma pj:lem:example (iii), the chord step: a measurable set `A ⊆ ℝ^{k+1}` invariant under the
translations along the first basis vector meets the ball of radius `r ≤ R` in at most `r / R`
times the volume in which it meets the ball of radius `R`. -/
lemma line_le_e0 (k : ℕ) {A : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hA : MeasurableSet A)
    (hinv : ∀ x ∈ A, ∀ t : ℝ, x + t • EuclideanSpace.single 0 1 ∈ A) {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ≤ R) (hR0 : 0 < R) :
    volume (A ∩ closedBall 0 r) ≤ ENNReal.ofReal (r / R) * volume (A ∩ closedBall 0 R) := by
  set A₀ : Set (Fin k → ℝ) := {y | (coordE k).symm (0, y) ∈ A}
  have hA₀ : MeasurableSet A₀ :=
    ((coordE k).symm.measurable.comp (measurable_const.prodMk measurable_id)) hA
  have hmem : ∀ x, x ∈ A ↔ (coordE k x).2 ∈ A₀ := by
    intro x
    have hx : (coordE k).symm (0, (coordE k x).2) = x + (-x 0) • EuclideanSpace.single 0 1 := by
      apply (coordE k).injective
      rw [MeasurableEquiv.apply_symm_apply, coordE_shift, add_neg_cancel]
    simp only [A₀, mem_ofPred_eq, hx]
    constructor
    · intro h; exact hinv x h _
    · intro h
      have := hinv _ h (x 0)
      rwa [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero] at this
  have hset : ∀ ρ : ℝ, 0 ≤ ρ → A ∩ closedBall 0 ρ = coordE k ⁻¹'
      {p : ℝ × (Fin k → ℝ) | p.2 ∈ A₀ ∧ p.1 ^ 2 + ∑ i, p.2 i ^ 2 ≤ ρ ^ 2} := by
    intro ρ hρ
    ext x
    simp only [mem_inter_iff, mem_closedBall, dist_zero_right, mem_preimage, mem_ofPred_eq,
      ← hmem, ← normsq_coordE]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, pow_le_pow_left₀ (norm_nonneg _) h2 2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (pow_le_pow_iff_left₀ (norm_nonneg _) hρ two_ne_zero).1 h2⟩
  rw [hset r hr, hset R (hr.trans hrR), (coordE_mp k).measure_preimage_equiv,
    (coordE_mp k).measure_preimage_equiv]
  exact cyl_le k hA₀ hr hrR hR0

/-- The chord step in every direction `u ≠ 0`. -/
lemma line_le {d : ℕ} (hd : 1 ≤ d) {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ≠ 0) (hinv : ∀ x ∈ A, ∀ t : ℝ, x + t • u ∈ A)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hR0 : 0 < R) :
    volume (A ∩ closedBall 0 r) ≤ ENNReal.ofReal (r / R) * volume (A ∩ closedBall 0 R) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  set e₀ : EuclideanSpace ℝ (Fin (k + 1)) := EuclideanSpace.single 0 1
  set u' := ‖u‖⁻¹ • u
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hn : ‖e₀‖ = ‖u'‖ := by
    simp only [e₀, u', PiLp.norm_single, norm_one, norm_smul, norm_inv, norm_norm]
    field_simp
  set ρ := (ℝ ∙ (e₀ - u'))ᗮ.reflection
  have hρ : ρ e₀ = u' := Submodule.reflection_sub hn
  set A' := ρ ⁻¹' A
  have hA' : MeasurableSet A' := ρ.continuous.measurable hA
  have hinv' : ∀ x ∈ A', ∀ t : ℝ, x + t • e₀ ∈ A' := by
    intro x hx t
    show ρ (x + t • e₀) ∈ A
    rw [map_add, map_smul, hρ, smul_smul]
    exact hinv _ hx _
  have hmp : MeasurePreserving ρ volume volume := ρ.measurePreserving
  have hball : ∀ s : ℝ, ρ ⁻¹' closedBall 0 s = closedBall 0 s := by
    intro s; ext x; simp
  have hvol : ∀ s : ℝ, volume (A' ∩ closedBall 0 s) = volume (A ∩ closedBall 0 s) := by
    intro s
    rw [show A' ∩ closedBall 0 s = ρ ⁻¹' (A ∩ closedBall 0 s) by rw [preimage_inter, hball]]
    exact hmp.measure_preimage (hA.inter measurableSet_closedBall).nullMeasurableSet
  rw [← hvol, ← hvol]
  exact line_le_e0 k hA' hinv' hr hrR hR0


local notation "𝔼" d => EuclideanSpace ℝ (Fin d)

/-- `m₀⁺ = (½ + c) |D|⁻¹ λ|_D`. -/
def exMP (d : ℕ) : Measure (𝔼 d) :=
  ENNReal.ofReal ((1 / 2 + exC d) / exVol d) • volume.restrict (closedBall 0 1)
/-- `m₀⁻ = κ |D|⁻¹ λ|_E`. -/
def exMN (d : ℕ) : Measure (𝔼 d) :=
  ENNReal.ofReal (exKappa / exVol d) • volume.restrict (closedBall 0 (1 / 4))
/-- `G₁ - m₀ = (½ - c) |D|⁻¹ λ|_D + κ |D|⁻¹ λ|_E`. -/
def exR (d : ℕ) : Measure (𝔼 d) :=
  ENNReal.ofReal ((1 / 2 - exC d) / exVol d) • volume.restrict (closedBall 0 1) + exMN d


lemma exVol_pos (d : ℕ) : 0 < exVol d :=
  ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne

lemma vol_D (d : ℕ) : volume (closedBall (0 : 𝔼 d) 1) = ENNReal.ofReal (exVol d) :=
  (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm

lemma vol_ball (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall (0 : 𝔼 d) r) = ENNReal.ofReal (r ^ d * exVol d) := by
  rw [Measure.addHaar_closedBall' _ _ hr, finrank_euclideanSpace_fin, vol_D,
    ← ENNReal.ofReal_mul (by positivity)]

lemma exC_nonneg (d : ℕ) : 0 ≤ exC d := by unfold exC exKappa; positivity

lemma exC_le (hd : 2 ≤ d) : exC d ≤ 9 / 160 := by
  unfold exC exKappa
  have : (1 / 4 : ℝ) ^ d ≤ (1 / 4) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
  nlinarith

lemma ind_mem {α : Type*} {S : Set α} {x : α} (h : x ∈ S) : ind S x = 1 := by
  simp [ind, h]
lemma ind_nmem {α : Type*} {S : Set α} {x : α} (h : x ∉ S) : ind S x = 0 := by
  simp [ind, h]

lemma measurable_ind {α : Type*} [MeasurableSpace α] {S : Set α} (hS : MeasurableSet S) :
    Measurable (ind S) := measurable_const.indicator hS

lemma smul_restrict_eq (a : ℝ) {S : Set (𝔼 d)} (hS : MeasurableSet S) :
    ENNReal.ofReal a • volume.restrict S = volume.withDensity (fun y => ENNReal.ofReal (a * ind S y)) := by
  have : (fun y => ENNReal.ofReal (a * ind S y)) = S.indicator (fun _ => ENNReal.ofReal a) := by
    funext y; by_cases hy : y ∈ S <;> simp [ind, hy]
  rw [this, withDensity_indicator hS, withDensity_const]

lemma tr_withDensity (v : 𝔼 d) {f : (𝔼 d) → ℝ≥0∞} (hf : Measurable f) :
    tr v (volume.withDensity f) = volume.withDensity (fun x => f (x - v)) := by
  have hφ : Measurable (· + v : (𝔼 d) → 𝔼 d) := measurable_add_const v
  have hg : Measurable (fun x : 𝔼 d => f (x - v)) := hf.comp (measurable_sub_const v)
  have e : f = (fun x => f (x - v)) ∘ (· + v) := by funext x; simp
  ext A hA
  rw [tr, Measure.map_apply hφ hA, withDensity_apply _ (hφ hA), withDensity_apply _ hA]
  conv_lhs => rw [e]
  change ∫⁻ a in (· + v) ⁻¹' A, (fun x => f (x - v)) (a + v) ∂volume = _
  rw [← setLIntegral_map hA hg hφ, map_add_right_eq_self]

lemma tr_add' {F : Type*} [AddCommGroup F] [MeasurableSpace F] [MeasurableAdd F] (v : F)
    (μ ν : Measure F) : tr v (μ + ν) = tr v μ + tr v ν :=
  Measure.map_add _ _ (measurable_add_const v)

lemma tr_add (v : 𝔼 d) (μ ν : Measure (𝔼 d)) : tr v (μ + ν) = tr v μ + tr v ν :=
  Measure.map_add _ _ (measurable_add_const v)

lemma exG1_eq (d : ℕ) : exG1 d = ENNReal.ofReal (1 / exVol d) • volume.restrict (closedBall 0 1) := by
  rw [exG1, unifSet, vol_D, ENNReal.ofReal_div_of_pos (exVol_pos d), ENNReal.ofReal_one, one_div]

/-- The relation `G₁ + m₀⁻ = m₀⁺ + (G₁ - m₀)`. -/
lemma exG1_add (hd : 2 ≤ d) : exG1 d + exMN d = exMP d + exR d := by
  rw [exG1_eq, exMP, exR, ← add_assoc, ← add_smul, ← ENNReal.ofReal_add]
  · congr 3; ring
  · have := exC_nonneg d; have := exVol_pos d; positivity
  · have := exC_le hd; have := exVol_pos d
    exact div_nonneg (by linarith) this.le

lemma E_sub_D {y : 𝔼 d} (h : y ∈ closedBall (0 : 𝔼 d) (1 / 4)) : y ∈ closedBall (0 : 𝔼 d) 1 :=
  closedBall_subset_closedBall (by norm_num) h

lemma mu_cases (y : 𝔼 d) :
    (y ∈ closedBall (0 : 𝔼 d) (1 / 4) ∧ exMu d y = 1 / 2 + exC d - exKappa ∧
        ind (closedBall 0 1) y - exMu d y = 1 / 2 - exC d + exKappa) ∨
    (y ∉ closedBall (0 : 𝔼 d) (1 / 4) ∧ y ∈ closedBall (0 : 𝔼 d) 1 ∧ exMu d y = 1 / 2 + exC d ∧
        ind (closedBall 0 1) y - exMu d y = 1 / 2 - exC d) ∨
    (y ∉ closedBall (0 : 𝔼 d) 1 ∧ exMu d y = 0 ∧ ind (closedBall 0 1) y - exMu d y = 0) := by
  by_cases hE : y ∈ closedBall (0 : 𝔼 d) (1 / 4)
  · left
    simp only [exMu, ind_mem hE, ind_mem (E_sub_D hE)]
    exact ⟨hE, by ring, by ring⟩
  · by_cases hD : y ∈ closedBall (0 : 𝔼 d) 1
    · right; left
      simp only [exMu, ind_nmem hE, ind_mem hD]
      exact ⟨hE, hD, by ring, by ring⟩
    · right; right
      simp only [exMu, ind_nmem hE, ind_nmem hD]
      exact ⟨hD, by ring, by ring⟩

lemma exQf_mul (x : 𝔼 d) : exQf d w x * exVol d =
    exMu d (x - w) + (ind (closedBall 0 1) (x + w) - exMu d (x + w)) := by
  rw [exQf, div_mul_cancel₀ _ (exVol_pos d).ne']

theorem ex_Qf_nonneg' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (x : 𝔼 d) : 0 ≤ exQf d w x := by
  have hv := exVol_pos d
  have hc := exC_le hd
  have hc0 := exC_nonneg d
  have hk : exKappa = 9 / 10 := rfl
  suffices 0 ≤ exQf d w x * exVol d from nonneg_of_mul_nonneg_left this hv
  rw [exQf_mul]
  rcases mu_cases (d := d) (x - w) with ⟨hE, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, h1, -⟩
  · -- `x - w ∈ E`, so `x + w ∈ D \ E`
    have hn : ‖x - w‖ ≤ 1 / 4 := by simpa using hE
    have hxw : x + w = (x - w) + (2 : ℝ) • w := by rw [two_smul]; abel
    have hup : ‖x + w‖ ≤ 1 := by
      rw [hxw]; refine (norm_add_le _ _).trans ?_; rw [norm_smul, hw]; norm_num; linarith
    have hlo : 1 / 4 < ‖x + w‖ := by
      have := norm_sub_norm_le ((2 : ℝ) • w) (-(x - w))
      rw [norm_neg, norm_smul, hw, sub_neg_eq_add, add_comm, ← hxw] at this
      norm_num at this; linarith
    rcases mu_cases (d := d) (x + w) with ⟨hE', -, -⟩ | ⟨-, -, -, h2⟩ | ⟨hD', -, -⟩
    · exact absurd (by simpa using hE') (not_le.2 hlo)
    · rw [h1, h2, hk]; linarith
    · exact absurd (by simpa using hup) hD'
  · rcases mu_cases (d := d) (x + w) with ⟨-, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, h2⟩ <;>
      rw [h1, h2] <;> linarith
  · rcases mu_cases (d := d) (x + w) with ⟨-, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, h2⟩ <;>
      rw [h1, h2] <;> linarith

theorem ex_Qf_le' (hd : 2 ≤ d) (x : 𝔼 d) : exQf d w x ≤ 3 / exVol d := by
  have hv := exVol_pos d
  have hc := exC_le hd
  have hc0 := exC_nonneg d
  have hk : exKappa = 9 / 10 := rfl
  rw [le_div_iff₀ hv, exQf_mul]
  rcases mu_cases (d := d) (x - w) with ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, h1, -⟩ <;>
  rcases mu_cases (d := d) (x + w) with ⟨-, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, h2⟩ <;>
      rw [h1, h2] <;> linarith

lemma exQf_out (hw : ‖w‖ = 3 / 10) {x : 𝔼 d} (hx : x ∉ closedBall (0 : 𝔼 d) (13 / 10)) :
    exQf d w x = 0 := by
  have hx' : 13 / 10 < ‖x‖ := by simpa using hx
  have h1 : x - w ∉ closedBall (0 : 𝔼 d) 1 := by
    simp only [mem_closedBall, dist_zero_right, not_le]
    have := norm_sub_norm_le x w; linarith
  have h2 : x + w ∉ closedBall (0 : 𝔼 d) 1 := by
    simp only [mem_closedBall, dist_zero_right, not_le]
    have := norm_sub_norm_le x (-w); rw [norm_neg, sub_neg_eq_add] at this; linarith
  have hv := exVol_pos d
  have : exQf d w x * exVol d = 0 := by
    rw [exQf_mul]
    rcases mu_cases (d := d) (x - w) with ⟨hE, -, -⟩ | ⟨-, hD, -, -⟩ | ⟨-, e1, -⟩
    · exact absurd (E_sub_D hE) h1
    · exact absurd hD h1
    rcases mu_cases (d := d) (x + w) with ⟨hE, -, -⟩ | ⟨-, hD, -, -⟩ | ⟨-, -, e2⟩
    · exact absurd (E_sub_D hE) h2
    · exact absurd hD h2
    rw [e1, e2, add_zero]
  exact (mul_eq_zero.1 this).resolve_right hv.ne'

lemma ind_nonneg {α : Type*} (S : Set α) (x : α) : 0 ≤ ind S x :=
  indicator_nonneg (fun _ _ => zero_le_one) x

lemma measurable_exMu (d : ℕ) : Measurable (exMu d) :=
  (measurable_const.mul (measurable_ind measurableSet_closedBall)).sub
    (measurable_const.mul (measurable_ind measurableSet_closedBall))

lemma measurable_exQf (w : 𝔼 d) : Measurable (exQf d w) := by
  unfold exQf
  refine Measurable.div_const ?_ _
  exact ((measurable_exMu d).comp (measurable_sub_const w)).add
    (((measurable_ind measurableSet_closedBall).comp (measurable_add_const w)).sub
      ((measurable_exMu d).comp (measurable_add_const w)))

/-- The identity of measures `Q + τ_w m₀⁻ = τ_w m₀⁺ + τ_{-w} (G₁ - m₀)`, the definition of `Q`
in terms of positive measures. -/
theorem ex_KI (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) :
    exQ d w + tr w (exMN d) = tr w (exMP d) + tr (-w) (exR d) := by
  have hv := exVol_pos d
  have hc := exC_le hd
  have hc0 := exC_nonneg d
  have hk : exKappa = 9 / 10 := rfl
  have hD : MeasurableSet (closedBall (0 : 𝔼 d) 1) := measurableSet_closedBall
  have hE : MeasurableSet (closedBall (0 : 𝔼 d) (1 / 4)) := measurableSet_closedBall
  have hm : ∀ (a : ℝ) {S : Set (𝔼 d)}, MeasurableSet S →
      Measurable fun y => ENNReal.ofReal (a * ind S y) :=
    fun a S hS => ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_ind hS))
  rw [exR, exMP, exMN, smul_restrict_eq _ hD, smul_restrict_eq _ hD, smul_restrict_eq _ hE,
    tr_add, tr_withDensity _ (hm _ hD), tr_withDensity _ (hm _ hE), tr_withDensity _ (hm _ hD),
    tr_withDensity _ (hm _ hE), exQ, ← withDensity_add_left, ← withDensity_add_left,
    ← withDensity_add_left]
  · congr 1
    funext x
    simp only [Pi.add_apply, sub_neg_eq_add]
    have n1 := ex_Qf_nonneg' hd hw x
    have nE : ∀ y : 𝔼 d, 0 ≤ exKappa / exVol d * ind (closedBall 0 (1 / 4)) y := fun y =>
      mul_nonneg (by rw [hk]; positivity) (ind_nonneg _ _)
    have nP : ∀ y : 𝔼 d, 0 ≤ (1 / 2 + exC d) / exVol d * ind (closedBall 0 1) y := fun y =>
      mul_nonneg (by positivity) (ind_nonneg _ _)
    have nR : ∀ y : 𝔼 d, 0 ≤ (1 / 2 - exC d) / exVol d * ind (closedBall 0 1) y := fun y =>
      mul_nonneg (div_nonneg (by linarith) hv.le) (ind_nonneg _ _)
    rw [← ENNReal.ofReal_add n1 (nE (x - w)), ← ENNReal.ofReal_add (nR (x + w)) (nE (x + w)),
      ← ENNReal.ofReal_add (nP (x - w)) (add_nonneg (nR (x + w)) (nE (x + w)))]
    congr 1
    rw [exQf, exMu, exMu]
    ring
  · exact (hm _ hD).comp (measurable_sub_const _)
  · exact (hm _ hD).comp (measurable_sub_const _)
  · exact ENNReal.measurable_ofReal.comp (measurable_exQf w)

lemma isFinite_smul_ball (a r : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal a • volume.restrict (closedBall (0 : 𝔼 d) r)) :=
  ⟨by rw [smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top⟩

instance (d : ℕ) : IsFiniteMeasure (exMP d) := isFinite_smul_ball _ _
instance (d : ℕ) : IsFiniteMeasure (exMN d) := isFinite_smul_ball _ _
instance (d : ℕ) : IsFiniteMeasure (exR d) := by
  have := isFinite_smul_ball (d := d) ((1 / 2 - exC d) / exVol d) 1; unfold exR; infer_instance
instance (d : ℕ) : IsFiniteMeasure (exG1 d) := by rw [exG1_eq]; exact isFinite_smul_ball _ _

/-- The signed measure `m₀` with density `μ / |D|`, written as `m₀⁺ - m₀⁻` with
`m₀⁺ = (½ + c) |D|⁻¹ λ|_D` and `m₀⁻ = κ |D|⁻¹ λ|_E` (so that its density is
`((½ + c) 𝟏_D - κ 𝟏_E) / |D| = μ / |D|`). -/
def exM0 (d : ℕ) : SignedMeasure (𝔼 d) := (exMP d).toSignedMeasure - (exMN d).toSignedMeasure

lemma tr_univ (v : 𝔼 d) (μ : Measure (𝔼 d)) : tr v μ univ = μ univ := by
  rw [tr, Measure.map_apply (measurable_add_const v) MeasurableSet.univ, preimage_univ]

lemma vol_E_eq (d : ℕ) : volume (closedBall (0 : 𝔼 d) (1 / 4)) =
    ENNReal.ofReal ((1 / 4) ^ d * exVol d) := vol_ball d (by norm_num)

lemma exMP_apply {A : Set (𝔼 d)} (hA : MeasurableSet A) :
    exMP d A = ENNReal.ofReal ((1 / 2 + exC d) / exVol d) * volume (A ∩ closedBall 0 1) := by
  rw [exMP, smul_apply, smul_eq_mul, Measure.restrict_apply hA]

lemma exMN_apply {A : Set (𝔼 d)} (hA : MeasurableSet A) :
    exMN d A = ENNReal.ofReal (exKappa / exVol d) * volume (A ∩ closedBall 0 (1 / 4)) := by
  rw [exMN, smul_apply, smul_eq_mul, Measure.restrict_apply hA]

lemma exMP_univ (_hd : 2 ≤ d) : exMP d univ = ENNReal.ofReal (1 / 2 + exC d) := by
  have := exC_nonneg d; have hv := exVol_pos d
  rw [exMP_apply MeasurableSet.univ, univ_inter, vol_D, ← ENNReal.ofReal_mul (by positivity),
    div_mul_cancel₀ _ hv.ne']

lemma exMN_univ (d : ℕ) : exMN d univ = ENNReal.ofReal (exC d) := by
  have hv := exVol_pos d
  rw [exMN_apply MeasurableSet.univ, univ_inter, vol_E_eq,
    ← ENNReal.ofReal_mul (by unfold exKappa; positivity), exC]
  congr 1; field_simp

lemma exR_univ (hd : 2 ≤ d) :
    exR d univ = ENNReal.ofReal (1 / 2 - exC d) + ENNReal.ofReal (exC d) := by
  have := exC_le hd; have hv := exVol_pos d
  rw [exR, add_apply, exMN_univ, smul_apply, smul_eq_mul, Measure.restrict_apply_univ, vol_D,
    ← ENNReal.ofReal_mul (div_nonneg (by linarith) hv.le), div_mul_cancel₀ _ hv.ne']

theorem ex_isProb_Q' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) : IsProbabilityMeasure (exQ d w) := by
  constructor
  have h := congrArg (fun μ : Measure (𝔼 d) => μ univ) (ex_KI hd hw)
  simp only [add_apply, tr_univ, exMN_univ, exMP_univ hd, exR_univ hd] at h
  have := exC_le hd; have := exC_nonneg d
  rw [← add_assoc] at h
  have h2 := (ENNReal.add_left_inj ENNReal.ofReal_ne_top).1 h
  rw [h2, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  norm_num

theorem ex_Q_compl' (hw : ‖w‖ = 3 / 10) : exQ d w (closedBall 0 (13 / 10))ᶜ = 0 := by
  rw [exQ, withDensity_apply _ measurableSet_closedBall.compl]
  rw [setLIntegral_congr_fun measurableSet_closedBall.compl (g := fun _ => 0)
    (fun x hx => by simp only; rw [exQf_out hw hx, ENNReal.ofReal_zero])]
  simp

theorem ex_deconv' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) :
    DeconvEq (exG1 d) (exQ d w) w (exM0 d) := by
  have : IsProbabilityMeasure (exQ d w) := ex_isProb_Q' hd hw
  intro A hA
  set A₁ := (· + w) ⁻¹' A
  set A₂ := (· - w) ⁻¹' A
  have hA₁ : MeasurableSet A₁ := (measurable_add_const w) hA
  have hA₂ : MeasurableSet A₂ := (measurable_sub_const w) hA
  have h1 := congrArg (fun μ : Measure (𝔼 d) => μ A) (ex_KI hd hw)
  have e : (fun x : 𝔼 d => x + -w) = (· - w) := funext fun x => (sub_eq_add_neg x w).symm
  simp only [add_apply, tr, Measure.map_apply (measurable_add_const _) hA, e] at h1
  rw [Measure.map_apply (measurable_sub_const _) hA] at h1
  have h2 := congrArg (fun μ : Measure (𝔼 d) => μ A₂) (exG1_add hd)
  simp only [add_apply] at h2
  have r1 := congrArg ENNReal.toReal h1
  have r2 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at r1 r2
  simp only [exM0, sub_apply, Measure.toSignedMeasure_apply_measurable hA₁,
    Measure.toSignedMeasure_apply_measurable hA₂, measureReal_def]
  linarith

theorem ex_m0_neg' (hd : 2 ≤ d) : exM0 d (closedBall 0 (1 / 4)) < 0 := by
  have hE : MeasurableSet (closedBall (0 : 𝔼 d) (1 / 4)) := measurableSet_closedBall
  have hv := exVol_pos d; have hc := exC_le hd; have hc0 := exC_nonneg d
  simp only [exM0, sub_apply, Measure.toSignedMeasure_apply_measurable hE,
    measureReal_def]
  rw [exMP_apply hE, exMN_apply hE, inter_eq_left.2 (closedBall_subset_closedBall (by norm_num)),
    inter_self, vol_E_eq, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hk : (0 : ℝ) ≤ exKappa / exVol d := by unfold exKappa; positivity
  have h1 : (0 : ℝ) ≤ (1 / 2 + exC d) / exVol d := by positivity
  have h2 : (0 : ℝ) ≤ (1 / 4) ^ d * exVol d := by positivity
  rw [ENNReal.toReal_ofReal hk, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2, ← sub_mul]
  apply mul_neg_of_neg_of_pos _ (by positivity)
  rw [div_sub_div_same]
  apply div_neg_of_neg_of_pos _ hv
  unfold exKappa; linarith

lemma integrable_supp {G : Measure (𝔼 d)} [IsFiniteMeasure G] {ρ : ℝ}
    (h : G (closedBall 0 ρ)ᶜ = 0) : Integrable (fun x => x) G := by
  refine Integrable.of_bound (continuous_id' : Continuous fun x : 𝔼 d => x).aestronglyMeasurable ρ ?_
  have : ∀ᵐ x ∂G, x ∈ closedBall (0 : 𝔼 d) ρ := by rw [ae_iff]; exact h
  filter_upwards [this] with x hx
  simpa using hx

lemma ball_compl_null (a r : ℝ) :
    (ENNReal.ofReal a • volume.restrict (closedBall (0 : 𝔼 d) r)) (closedBall 0 r)ᶜ = 0 := by
  rw [smul_apply, Measure.restrict_apply measurableSet_closedBall.compl, compl_inter_self]; simp

lemma integrable_ball (a r : ℝ) :
    Integrable (fun x => x) (ENNReal.ofReal a • volume.restrict (closedBall (0 : 𝔼 d) r)) := by
  have := isFinite_smul_ball (d := d) a r
  exact integrable_supp (ball_compl_null a r)

lemma mean_ball (a r : ℝ) :
    ∫ x, x ∂(ENNReal.ofReal a • volume.restrict (closedBall (0 : 𝔼 d) r)) = 0 := by
  rw [integral_smul_measure]
  set B := closedBall (0 : 𝔼 d) r
  have hI : ∫ x in B, x = 0 := by
    rw [← integral_indicator measurableSet_closedBall]
    have h := integral_neg_eq_self (fun x => B.indicator (fun x => x) x) (volume : Measure (𝔼 d))
    have e : (fun x : 𝔼 d => B.indicator (fun x => x) (-x)) = fun x => -(B.indicator (fun x => x) x) := by
      funext x
      by_cases hx : x ∈ B
      · have : -x ∈ B := by simpa [B] using hx
        simp [indicator_of_mem hx, indicator_of_mem this]
      · have : -x ∉ B := by simpa [B] using hx
        simp [indicator_of_notMem hx, indicator_of_notMem this]
    simp only [e, integral_neg] at h
    set I := ∫ x, B.indicator (fun x => x) x
    have h2 : (2 : ℝ) • I = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel I
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hI, smul_zero]

lemma integral_tr_fin {G : Measure (𝔼 d)} [IsFiniteMeasure G] (hG : Integrable (fun x => x) G)
    (v : 𝔼 d) : Integrable (fun x => x) (tr v G) ∧
      ∫ x, x ∂(tr v G) = ∫ x, x ∂G + G.real univ • v := by
  have hm : Measurable (· + v : (𝔼 d) → 𝔼 d) := measurable_add_const v
  refine ⟨?_, ?_⟩
  · rw [tr, integrable_map_measure (continuous_id' : Continuous fun x : 𝔼 d => x).aestronglyMeasurable
      hm.aemeasurable]
    exact hG.add (integrable_const v)
  · rw [tr, integral_map hm.aemeasurable
      (continuous_id' : Continuous fun x : 𝔼 d => x).aestronglyMeasurable,
      integral_add hG (integrable_const v), integral_const]

lemma integrable_exR (d : ℕ) : Integrable (fun x => x) (exR d) := by
  unfold exR exMN; exact (integrable_ball _ _).add_measure (integrable_ball _ _)

lemma mean_exR (d : ℕ) : ∫ x, x ∂(exR d) = 0 := by
  unfold exR exMN
  rw [integral_add_measure (integrable_ball _ _) (integrable_ball _ _), mean_ball, mean_ball,
    add_zero]

theorem ex_mean_Q (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) : ∫ x, x ∂(exQ d w) = 0 := by
  have : IsProbabilityMeasure (exQ d w) := ex_isProb_Q' hd hw
  have hQ : Integrable (fun x => x) (exQ d w) := integrable_supp (ex_Q_compl' hw)
  have iN : Integrable (fun x => x) (exMN d) := by unfold exMN; exact integrable_ball _ _
  have iP : Integrable (fun x => x) (exMP d) := by unfold exMP; exact integrable_ball _ _
  have mN : ∫ x, x ∂(exMN d) = 0 := by unfold exMN; exact mean_ball _ _
  have mP : ∫ x, x ∂(exMP d) = 0 := by unfold exMP; exact mean_ball _ _
  have hN := integral_tr_fin iN w
  have hP := integral_tr_fin iP w
  have hR := integral_tr_fin (integrable_exR d) (-w)
  have h := congrArg (fun μ : Measure (𝔼 d) => ∫ x, x ∂μ) (ex_KI hd hw)
  beta_reduce at h
  rw [integral_add_measure hQ hN.1, integral_add_measure hP.1 hR.1, hN.2, hP.2, hR.2, mN, mP,
    mean_exR] at h
  have e1 : (exMN d).real univ = exC d := by
    rw [measureReal_def, exMN_univ, ENNReal.toReal_ofReal (exC_nonneg d)]
  have e2 : (exMP d).real univ = 1 / 2 + exC d := by
    rw [measureReal_def, exMP_univ hd, ENNReal.toReal_ofReal (by have := exC_nonneg d; positivity)]
  have e3 : (exR d).real univ = 1 / 2 := by
    have := exC_le hd; have := exC_nonneg d
    rw [measureReal_def, exR_univ hd, ← ENNReal.ofReal_add (by linarith) (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [e1, e2, e3] at h
  simp only [zero_add] at h
  have : ∫ x, x ∂(exQ d w) = (1 / 2 + exC d) • w + (1 / 2 : ℝ) • (-w) - exC d • w := by
    rw [← h]; abel
  rw [this, smul_neg, add_smul]; abel

theorem ex_isProb' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (i : Fin 3) :
    IsProbabilityMeasure (exG d w i) := by
  have := ex_isProb_Q' hd hw
  fin_cases i
  · show IsProbabilityMeasure (exG1 d)
    constructor
    rw [exG1_eq, smul_apply, Measure.restrict_apply_univ, vol_D, smul_eq_mul,
      ← ENNReal.ofReal_mul (by have := exVol_pos d; positivity),
      one_div_mul_cancel (exVol_pos d).ne', ENNReal.ofReal_one]
  · show IsProbabilityMeasure ((exQ d w).map Neg.neg)
    infer_instance
  · show IsProbabilityMeasure (twoPoint w)
    exact twoPoint_isProb w

theorem ex_support' (hw : ‖w‖ = 3 / 10) (i : Fin 3) :
    exG d w i (closedBall 0 (13 / 10))ᶜ = 0 := by
  fin_cases i
  · show exG1 d (closedBall 0 (13 / 10))ᶜ = 0
    rw [exG1_eq, smul_apply, Measure.restrict_apply measurableSet_closedBall.compl]
    have : (closedBall (0 : 𝔼 d) (13 / 10))ᶜ ∩ closedBall 0 1 = ∅ := by
      rw [← disjoint_iff_inter_eq_empty, disjoint_compl_left_iff_subset]
      exact closedBall_subset_closedBall (by norm_num)
    rw [this]; simp
  · show (exQ d w).map Neg.neg (closedBall 0 (13 / 10))ᶜ = 0
    rw [Measure.map_apply measurable_neg measurableSet_closedBall.compl]
    have : Neg.neg ⁻¹' (closedBall (0 : 𝔼 d) (13 / 10))ᶜ = (closedBall 0 (13 / 10))ᶜ := by
      ext x; simp
    rw [this]; exact ex_Q_compl' hw
  · show twoPoint w (closedBall 0 (13 / 10))ᶜ = 0
    have h1 : w ∈ closedBall (0 : 𝔼 d) (13 / 10) := by simp [hw]; norm_num
    have h2 : -w ∈ closedBall (0 : 𝔼 d) (13 / 10) := by simp [hw]; norm_num
    simp [twoPoint, Measure.dirac_apply' _ measurableSet_closedBall.compl, h1, h2]

theorem ex_mean' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (i : Fin 3) : ∫ x, x ∂(exG d w i) = 0 := by
  fin_cases i
  · show ∫ x, x ∂(exG1 d) = 0
    rw [exG1_eq]; exact mean_ball _ _
  · show ∫ x, x ∂((exQ d w).map Neg.neg) = 0
    rw [integral_map measurable_neg.aemeasurable
      (continuous_id' : Continuous fun x : 𝔼 d => x).aestronglyMeasurable, integral_neg,
      ex_mean_Q hd hw, neg_zero]
  · show ∫ x, x ∂(twoPoint w) = 0
    rw [twoPoint, integral_smul_measure, integral_add_measure, integral_dirac, integral_dirac,
      add_neg_cancel, smul_zero]
    · exact integrable_supp (ρ := ‖w‖) (by simp [Measure.dirac_apply' _ measurableSet_closedBall.compl])
    · exact integrable_supp (ρ := ‖w‖) (by simp [Measure.dirac_apply' _ measurableSet_closedBall.compl])

/-- The constant sum of a joint mix is the sum of the means. -/
lemma jointMix_sum {n : ℕ} {F : Fin n → Measure (𝔼 d)} {P : Measure (Fin n → 𝔼 d)}
    (hP : IsProbabilityMeasure P) {s : 𝔼 d} (hs : ∀ᵐ x ∂P, ∑ j, x j = s)
    (hmarg : ∀ j, P.map (fun x => x j) = F j) (hint : ∀ j, Integrable (fun x => x) (F j)) :
    s = ∑ j, ∫ x, x ∂(F j) := by
  have hcoord : ∀ j, Integrable (fun x : Fin n → 𝔼 d => x j) P ∧
      ∫ x, x j ∂P = ∫ x, x ∂(F j) := by
    intro j
    have hmj : Measurable (fun x : Fin n → 𝔼 d => x j) := measurable_pi_apply j
    have h1 := hint j
    rw [← hmarg j, integrable_map_measure
      (continuous_id' : Continuous fun x : 𝔼 d => x).aestronglyMeasurable hmj.aemeasurable] at h1
    refine ⟨h1, ?_⟩
    rw [← hmarg j, integral_map hmj.aemeasurable
      (continuous_id' : Continuous fun x : 𝔼 d => x).aestronglyMeasurable]
  have : ∫ x, ∑ j, x j ∂P = s := by
    rw [integral_congr_ae hs, integral_const]; simp
  rw [← this, integral_finsetSum _ (fun j _ => (hcoord j).1)]
  exact Finset.sum_congr rfl fun j _ => (hcoord j).2

theorem ex_not_jointlyMixable' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) : ¬ JointlyMixable (exG d w) := by
  rintro ⟨P, hP, ⟨s, hs⟩, hmarg⟩
  have hint : ∀ j, Integrable (fun x => x) (exG d w j) := fun j => by
    have := ex_isProb' hd hw j; exact integrable_supp (ex_support' hw j)
  have hs0 : s = 0 := by
    rw [jointMix_sum hP hs hmarg hint]
    exact Finset.sum_eq_zero fun j _ => ex_mean' hd hw j
  subst hs0
  have : IsProbabilityMeasure (exG1 d) := ex_isProb' hd hw 0
  have : IsProbabilityMeasure (exQ d w) := ex_isProb_Q' hd hw
  obtain ⟨m, hle, -, hQ⟩ := (three_a (exG1 d) (exQ d w) w).1 ⟨P, hP, hs, hmarg⟩
  have : IsFiniteMeasure m := isFiniteMeasure_of_le _ hle
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
  have heq := three_b hw0 (deconvEq_of_measure hle hQ) (ex_deconv' hd hw)
  have h1 := ex_m0_neg' (d := d) hd
  rw [← heq, Measure.toSignedMeasure_apply_measurable measurableSet_closedBall] at h1
  exact absurd h1 (not_lt.2 ENNReal.toReal_nonneg)

lemma meas_cancel {α : Type*} [MeasurableSpace α] {μ μ' ν : Measure α} [IsFiniteMeasure ν]
    (h : μ + ν = μ' + ν) : μ = μ' := by
  ext s hs
  have := congrArg (fun ρ : Measure α => ρ s) h
  simp only [add_apply] at this
  exact (ENNReal.add_left_inj (measure_ne_top ν s)).1 this

lemma map_tr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (L : (𝔼 d) →ₗ[ℝ] F) (v : 𝔼 d) (ν : Measure (𝔼 d)) :
    (tr v ν).map L = tr (L v) (ν.map L) := by
  have hLm : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  rw [tr, tr, Measure.map_map hLm (measurable_add_const v),
    Measure.map_map (measurable_add_const (L v)) hLm]
  congr 1; funext x; simp [map_add]

theorem ex_map_jointlyMixable' (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : (𝔼 d) →ₗ[ℝ] F) (hL : LinearMap.ker L ≠ ⊥) :
    JointlyMixable fun i => (exG d w i).map L := by
  have hLm : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  have hv := exVol_pos d; have hc := exC_le hd; have hc0 := exC_nonneg d
  have hk : exKappa = 9 / 10 := rfl
  have : IsProbabilityMeasure (exG1 d) := ex_isProb' hd hw 0
  have : IsProbabilityMeasure (exQ d w) := ex_isProb_Q' hd hw
  obtain ⟨u, huK, hu0⟩ := (Submodule.ne_bot_iff _).1 hL
  -- `L_# m₀⁻ ≤ L_# m₀⁺`: the fibres of `L` are unions of lines parallel to `u`
  have hle : (exMN d).map L ≤ (exMP d).map L := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.map_apply hLm hS, Measure.map_apply hLm hS]
    have hA : MeasurableSet (L ⁻¹' S) := hLm hS
    have hinv : ∀ x ∈ L ⁻¹' S, ∀ t : ℝ, x + t • u ∈ L ⁻¹' S := by
      intro x hx t
      simp only [mem_preimage, map_add, map_smul, LinearMap.mem_ker.1 huK, smul_zero, add_zero]
      exact hx
    have hline := line_le (by omega) hA hu0 hinv (r := 1 / 4) (R := 1) (by norm_num) (by norm_num)
      one_pos
    rw [exMN_apply hA, exMP_apply hA]
    calc ENNReal.ofReal (exKappa / exVol d) * volume (L ⁻¹' S ∩ closedBall 0 (1 / 4))
        ≤ ENNReal.ofReal (exKappa / exVol d) *
            (ENNReal.ofReal (1 / 4 / 1) * volume (L ⁻¹' S ∩ closedBall 0 1)) := by gcongr
      _ = ENNReal.ofReal (exKappa / exVol d * (1 / 4 / 1)) * volume (L ⁻¹' S ∩ closedBall 0 1) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by rw [hk]; positivity)]
      _ ≤ ENNReal.ofReal ((1 / 2 + exC d) / exVol d) * volume (L ⁻¹' S ∩ closedBall 0 1) := by
        gcongr
        rw [hk, div_one, div_mul_eq_mul_div]
        gcongr
        linarith
  set m' := (exMP d).map L - (exMN d).map L with hm'
  -- `m' ≤ L_# G₁`
  have hPG : exMP d ≤ exG1 d := by
    rw [Measure.le_iff]
    intro A hA
    rw [exMP_apply hA, exG1_eq, smul_apply, Measure.restrict_apply hA, smul_eq_mul]
    gcongr
    linarith
  have hm'le : m' ≤ (exG1 d).map L := Measure.sub_le.trans (Measure.map_mono hPG hLm)
  have hm'univ : m' univ = 2⁻¹ := by
    rw [hm', Measure.sub_apply MeasurableSet.univ hle, Measure.map_apply hLm MeasurableSet.univ,
      Measure.map_apply hLm MeasurableSet.univ, preimage_univ, exMP_univ hd, exMN_univ,
      ← ENNReal.ofReal_sub _ hc0]
    rw [show 1 / 2 + exC d - exC d = 2⁻¹ by ring, ENNReal.ofReal_inv_of_pos two_pos]
    simp
  -- the deconvolution equation for the images
  have hK := congrArg (fun μ : Measure (𝔼 d) => μ.map L) (ex_KI hd hw)
  simp only [Measure.map_add _ _ hLm, map_tr, map_neg] at hK
  have hG := congrArg (fun μ : Measure (𝔼 d) => μ.map L) (exG1_add hd)
  simp only [Measure.map_add _ _ hLm] at hG
  have hsplit : (exMP d).map L = m' + (exMN d).map L := (Measure.sub_add_cancel_of_le hle).symm
  have hLG1 : (exG1 d).map L = m' + (exR d).map L := by
    apply meas_cancel (ν := (exMN d).map L)
    rw [hG, hsplit]; abel
  have hdiff : (exG1 d).map L - m' = (exR d).map L := by
    rw [hLG1, add_comm, Measure.add_sub_cancel]
  have hQ : (exQ d w).map L = tr (L w) m' + tr (-(L w)) ((exG1 d).map L - m') := by
    rw [hdiff]
    have : IsFiniteMeasure (tr (L w) ((exMN d).map L)) := by unfold tr; infer_instance
    apply meas_cancel (ν := tr (L w) ((exMN d).map L))
    rw [hK, hsplit, tr_add']
    abel
  have hZ := (three_a ((exG1 d).map L) ((exQ d w).map L) (L w)).2 ⟨m', hm'le, hm'univ, hQ⟩
  obtain ⟨P, hP, hsum, hmarg⟩ := hZ
  refine ⟨P, hP, ⟨0, hsum⟩, fun j => ?_⟩
  rw [hmarg j]
  fin_cases j
  · rfl
  · show ((exQ d w).map L).map Neg.neg = ((exQ d w).map Neg.neg).map L
    rw [Measure.map_map measurable_neg hLm, Measure.map_map hLm measurable_neg]
    congr 1; funext x; simp
  · show twoPoint (L w) = (twoPoint w).map L
    rw [twoPoint, twoPoint, Measure.map_smul, Measure.map_add _ _ hLm, Measure.map_dirac' hLm,
      Measure.map_dirac' hLm, map_neg]
    exact hLm.aemeasurable


/-! ### The statements of Lemma pj:lem:example -/


/-- **Lemma pj:lem:example (i)**: the density of `Q` is nonnegative. -/
theorem ex_Qf_nonneg (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ exQf d w x :=
  ex_Qf_nonneg' hd hw x

/-- **Lemma pj:lem:example (i)**: the density of `Q` is bounded. -/
theorem ex_Qf_le (hd : 2 ≤ d) (_hw : ‖w‖ = 3 / 10) (x : EuclideanSpace ℝ (Fin d)) :
    exQf d w x ≤ 3 / exVol d :=
  ex_Qf_le' hd x

/-- **Lemma pj:lem:example (i)**: `Q` is a probability measure. -/
theorem ex_isProb_Q (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) : IsProbabilityMeasure (exQ d w) :=
  ex_isProb_Q' hd hw

/-- **Lemma pj:lem:example (i)**: `Q` is carried by `13/10 D`. -/
theorem ex_Q_compl (_hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) :
    exQ d w (closedBall 0 (13 / 10))ᶜ = 0 :=
  ex_Q_compl' hw

/-- `Q = τ_w m₀ + τ_{-w}(G₁ - m₀)`, i.e. `m₀` satisfies `(pj:eq:deconv)` (definition of `Q`). -/
theorem ex_deconv (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) : DeconvEq (exG1 d) (exQ d w) w (exM0 d) :=
  ex_deconv' hd hw

/-- `m₀` is negative on `E = ¼ D`. -/
theorem ex_m0_neg (hd : 2 ≤ d) : exM0 d (closedBall 0 (1 / 4)) < 0 :=
  ex_m0_neg' hd

/-- The three distributions are probability measures. -/
theorem ex_isProb (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (i : Fin 3) :
    IsProbabilityMeasure (exG d w i) :=
  ex_isProb' hd hw i

/-- The three distributions are carried by `13/10 D`. -/
theorem ex_support (_hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (i : Fin 3) :
    exG d w i (closedBall 0 (13 / 10))ᶜ = 0 :=
  ex_support' hw i

/-- **Lemma pj:lem:example (i)**: `G₁`, `G₂`, `G₃` have mean `0`. -/
theorem ex_mean (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) (i : Fin 3) : ∫ x, x ∂(exG d w i) = 0 :=
  ex_mean' hd hw i

/-- **Lemma pj:lem:example (ii)**: `G₁`, `G₂`, `G₃` are not jointly mixable. -/
theorem ex_not_jointlyMixable (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10) : ¬ JointlyMixable (exG d w) :=
  ex_not_jointlyMixable' hd hw

/-- **Lemma pj:lem:example (iii)**: for every linear map `L` on `ℝ^d` with a nonzero kernel (into
any real normed space `F`), `L_# G₁`, `L_# G₂`, `L_# G₃` are jointly mixable. -/
theorem ex_map_jointlyMixable (hd : 2 ≤ d) (hw : ‖w‖ = 3 / 10)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) (hL : LinearMap.ker L ≠ ⊥) :
    JointlyMixable fun i => (exG d w i).map L :=
  ex_map_jointlyMixable' hd hw L hL

end Example

/-! ## Lemma pj:lem:gadget -/

section Gadget

/-- The integers `a_i` of Lemma pj:lem:gadget, indexed by `i : Fin n` (the paper's `i + 1`):
`a_i = (2n+1)^i` for `i < n - 1` and `a_{n-1} = -∑_{i < n-1} a_i`. -/
def gadA (n : ℕ) (i : Fin n) : ℤ :=
  if (i : ℕ) < n - 1 then (2 * n + 1 : ℤ) ^ (i : ℕ)
  else -∑ j ∈ Finset.range (n - 1), (2 * n + 1 : ℤ) ^ j

lemma sum_gadA {n : ℕ} (hn : 1 ≤ n) : ∑ i : Fin n, gadA n i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin k, gadA (k + 1) (Fin.castSucc j) = (2 * ((k + 1 : ℕ) : ℤ) + 1) ^ (j : ℕ) := by
    intro j; simp [gadA, j.isLt]
  have h2 : gadA (k + 1) (Fin.last k) = -∑ j ∈ Finset.range k, (2 * ((k + 1 : ℕ) : ℤ) + 1) ^ j := by
    simp [gadA]
  rw [h2, Finset.sum_congr rfl (fun j _ => h1 j),
    Fin.sum_univ_eq_sum_range (fun j => (2 * ((k + 1 : ℕ) : ℤ) + 1) ^ j) k]
  ring

/-- Digits: `∑_{i<k} b_i B^i = 0` with `|b_i| < B` forces all `b_i = 0`. -/
lemma digits_zero (B : ℤ) : ∀ (k : ℕ) (b : ℕ → ℤ), (∀ i < k, |b i| < B) →
    ∑ i ∈ Finset.range k, b i * B ^ i = 0 → ∀ i < k, b i = 0 := by
  intro k
  induction k with
  | zero => intro b _ _ i hi; omega
  | succ k ih =>
    intro b hb hsum
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, mul_one] at hsum
    have hB : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hb 0 (Nat.succ_pos k))
    have hrest : ∑ i ∈ Finset.range k, b (i + 1) * B ^ (i + 1) =
        B * ∑ i ∈ Finset.range k, b (i + 1) * B ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hrest] at hsum
    have hdvd : B ∣ b 0 := ⟨-∑ i ∈ Finset.range k, b (i + 1) * B ^ i, by linarith⟩
    have h0 : b 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (hb 0 (Nat.succ_pos k))
    rw [h0, add_zero] at hsum
    have hs' : ∑ i ∈ Finset.range k, b (i + 1) * B ^ i = 0 :=
      (mul_eq_zero.1 hsum).resolve_left hB.ne'
    have := ih (fun i => b (i + 1)) (fun i hi => hb (i + 1) (by omega)) hs'
    intro i hi
    rcases i with _ | i
    · exact h0
    · exact this i (by omega)

/-- The counting step of Lemma pj:lem:gadget (b): if `∑_l a_{f(l)} = 0` for a map
`f : Fin n → Fin n`, then `f` is a bijection (each `C_i` receives exactly one `X_l`). -/
lemma count_bij {n : ℕ} (hn : 2 ≤ n) (f : Fin n → Fin n) (h : ∑ l, gadA n (f l) = 0) :
    Function.Bijective f := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  set N : Fin (k + 2) → ℤ := fun i => ((Finset.univ.filter fun l => f l = i).card : ℤ)
  have hfib : ∑ l, gadA (k + 2) (f l) = ∑ i, N i * gadA (k + 2) i := by
    rw [← Finset.sum_fiberwise Finset.univ f (fun l => gadA (k + 2) (f l))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (fun l hl => by rw [(Finset.mem_filter.1 hl).2])]
    simp [N]
  have hN : ∑ i, N i = k + 2 := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := f)
      (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [N]; exact_mod_cast this.symm
  have hN0 : ∀ i, 0 ≤ N i := fun i => Nat.cast_nonneg _
  have hNle : ∀ i, N i ≤ k + 2 := fun i => by
    have := Finset.single_le_sum (fun j _ => hN0 j) (Finset.mem_univ i)
    rw [hN] at this; exact this
  set B : ℤ := 2 * ((k + 2 : ℕ) : ℤ) + 1
  have h1 : ∀ j : Fin (k + 1), gadA (k + 2) (Fin.castSucc j) = B ^ (j : ℕ) := by
    intro j; simp [gadA, B, j.isLt]
  have h2 : gadA (k + 2) (Fin.last (k + 1)) = -∑ j ∈ Finset.range (k + 1), B ^ j := by
    simp [gadA, B]
  rw [hfib, Fin.sum_univ_castSucc, h2, Finset.sum_congr rfl (fun j _ => by rw [h1 j])] at h
  set b : ℕ → ℤ := fun j => if hj : j < k + 1 then N (Fin.castSucc ⟨j, hj⟩) - N (Fin.last (k + 1))
    else 0
  have hb : ∑ j ∈ Finset.range (k + 1), b j * B ^ j = 0 := by
    rw [← h, ← Fin.sum_univ_eq_sum_range (fun j => b j * B ^ j) (k + 1), mul_neg,
      ← Fin.sum_univ_eq_sum_range (fun j => B ^ j) (k + 1), Finset.mul_sum, ← sub_eq_add_neg,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [b, dite_eq_left i.isLt, Fin.eta]
    ring
  have hbB : ∀ j < k + 1, |b j| < B := by
    intro j hj
    simp only [b, dite_eq_left hj]
    have := hN0 (Fin.castSucc ⟨j, hj⟩); have := hNle (Fin.castSucc ⟨j, hj⟩)
    have := hN0 (Fin.last (k + 1)); have := hNle (Fin.last (k + 1))
    rw [abs_lt]; constructor <;> push_cast [B] <;> linarith
  have hb0 := digits_zero B (k + 1) b hbB hb
  have hall : ∀ i, N i = N (Fin.last (k + 1)) := by
    intro i
    induction i using Fin.lastCases with
    | last => rfl
    | cast j =>
      have := hb0 j j.isLt
      simp only [b, dite_eq_left j.isLt, Fin.eta] at this
      linarith
  have hone : ∀ i, N i = 1 := by
    intro i
    rw [Finset.sum_congr rfl (fun i _ => hall i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hN
    push_cast at hN
    rw [hall i]; nlinarith
  have hsurj : Function.Surjective f := by
    intro i
    have : 0 < (Finset.univ.filter fun l => f l = i).card := by
      have := hone i; simp only [N] at this; omega
    obtain ⟨l, hl⟩ := Finset.card_pos.1 this
    exact ⟨l, (Finset.mem_filter.1 hl).2⟩
  exact ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩


lemma gadA_inj {n : ℕ} (hn : 2 ≤ n) : Function.Injective (gadA n) := by
  have hB : (2 : ℤ) ≤ 2 * n + 1 := by omega
  have hpos : 0 < ∑ j ∈ Finset.range (n - 1), (2 * n + 1 : ℤ) ^ j :=
    Finset.sum_pos (fun j _ => by positivity) ⟨0, Finset.mem_range.2 (by omega)⟩
  intro i j hij
  simp only [gadA] at hij
  split_ifs at hij with hi hj hj
  · exact Fin.ext (pow_right_injective₀ (by omega) (by omega) hij)
  · have : (0 : ℤ) < (2 * n + 1) ^ (i : ℕ) := by positivity
    linarith
  · have : (0 : ℤ) < (2 * n + 1) ^ (j : ℕ) := by positivity
    linarith
  · apply Fin.ext; omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The points `v_i = λ a_i e`. -/
def gadV (n : ℕ) (lam : ℝ) (e : E) (i : Fin n) : E := (lam * gadA n i) • e

/-- `P = (1/n) ∑_i τ_{v_i} G_i`. -/
def gadP {n : ℕ} (G : Fin n → Measure E) (lam : ℝ) (e : E) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, tr (gadV n lam e i) (G i)

lemma sum_gadV {n : ℕ} (hn : 1 ≤ n) (lam : ℝ) (e : E) : ∑ i, gadV n lam e i = 0 := by
  simp only [gadV, ← Finset.sum_smul, ← Finset.mul_sum]
  have : (∑ i : Fin n, (gadA n i : ℝ)) = 0 := by exact_mod_cast sum_gadA hn
  rw [this, mul_zero, zero_smul]

lemma gadP_apply {n : ℕ} (G : Fin n → Measure E) (lam : ℝ) (e : E) {A : Set E}
    (hA : MeasurableSet A) :
    gadP G lam e A = (n : ℝ≥0∞)⁻¹ * ∑ i, G i ((· + gadV n lam e i) ⁻¹' A) := by
  simp only [gadP, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply, tr,
    Measure.map_apply (measurable_add_const _) hA]

lemma integral_fsum {α ι : Type*} [MeasurableSpace α] (s : Finset ι) (μ : ι → Measure α)
    (f : α → E) (hf : ∀ i ∈ s, Integrable f (μ i)) :
    Integrable f (∑ i ∈ s, μ i) ∧ ∫ x, f x ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ x, f x ∂(μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hfa.add_measure ih'.1, by rw [integral_add_measure hfa ih'.1, ih'.2]⟩

lemma integrable_of_supp {G : Measure E} [IsProbabilityMeasure G] {ρ₀ : ℝ}
    (h : G (closedBall 0 ρ₀)ᶜ = 0) : Integrable (fun x => x) G := by
  refine Integrable.of_bound (continuous_id' : Continuous fun x : E => x).aestronglyMeasurable ρ₀ ?_
  have : ∀ᵐ x ∂G, x ∈ closedBall (0 : E) ρ₀ := by rw [ae_iff]; exact h
  filter_upwards [this] with x hx
  simpa using hx

lemma integral_tr {G : Measure E} [IsProbabilityMeasure G] (hG : Integrable (fun x => x) G)
    (v : E) : Integrable (fun x => x) (tr v G) ∧ ∫ x, x ∂(tr v G) = ∫ x, x ∂G + v := by
  have hm : Measurable (· + v) := measurable_add_const v
  refine ⟨?_, ?_⟩
  · rw [tr, integrable_map_measure (continuous_id' : Continuous fun x : E => x).aestronglyMeasurable hm.aemeasurable]
    exact hG.add (integrable_const v)
  · rw [tr, integral_map hm.aemeasurable (continuous_id' : Continuous fun x : E => x).aestronglyMeasurable,
      integral_add hG (integrable_const v), integral_const]
    simp

/-- **Lemma pj:lem:gadget (a)**: if the images `L_# G_i` are jointly mixable, then `L_# P` is
`n`-completely mixable. (No assumption on `e`, `λ`, the supports or the means is needed.) -/
theorem gadget_a {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Measure E) [∀ i, IsProbabilityMeasure (G i)]
    (lam : ℝ) (e : E) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] (L : E →ₗ[ℝ] F)
    (h : JointlyMixable fun i => (G i).map L) : CompletelyMixable n ((gadP G lam e).map L) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, hP, ⟨s, hs⟩, hmarg⟩ := h
  have hLm : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  set v := gadV (k + 1) lam e
  set φ : Fin (k + 1) → (Fin (k + 1) → F) → (Fin (k + 1) → F) :=
    fun j y l => y (l + j) + L (v (l + j))
  have hφ : ∀ j, Measurable (φ j) := fun j => by
    rw [measurable_pi_iff]; intro l; exact (measurable_pi_apply _).add_const _
  have hcoord : ∀ i (c : F) {A : Set F}, MeasurableSet A →
      P {y | y i + c ∈ A} = G i (L ⁻¹' ((· + c) ⁻¹' A)) := by
    intro i c A hA
    have := congrArg (fun μ => μ ((· + c) ⁻¹' A)) (hmarg i)
    simp only at this
    rw [Measure.map_apply (measurable_pi_apply i) ((measurable_add_const c) hA),
      Measure.map_apply hLm ((measurable_add_const c) hA)] at this
    exact this
  refine ⟨((k + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j, P.map (φ j), ?_, ⟨s, ?_⟩, ?_⟩
  · constructor
    simp only [smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      Measure.map_apply (hφ _) MeasurableSet.univ, preimage_univ, measure_univ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  · rw [ae_iff]
    have hm : MeasurableSet {x : Fin (k + 1) → F | ∑ j, x j = s} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
        measurable_const
    have hnull : P {x | ∑ j, x j = s}ᶜ = 0 := ae_iff.1 hs
    show (_ : Measure (Fin (k + 1) → F)) {x | ∑ j, x j = s}ᶜ = 0
    simp only [smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      Measure.map_apply (hφ _) hm.compl]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    apply measure_mono_null _ hnull
    intro y hy
    simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq] at hy ⊢
    intro hys
    apply hy
    simp only [φ]
    rw [Finset.sum_add_distrib, ← map_sum,
      Fintype.sum_equiv (Equiv.addRight j) (fun l => y (l + j)) y (fun _ => rfl),
      Fintype.sum_equiv (Equiv.addRight j) (fun l => v (l + j)) v (fun _ => rfl),
      sum_gadV (by omega), map_zero, add_zero, hys]
  · intro l
    ext A hA
    rw [Measure.map_apply (measurable_pi_apply l) hA, Measure.map_apply hLm hA,
      gadP_apply G lam e (hLm hA)]
    simp only [smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      Measure.map_apply (hφ _) ((measurable_pi_apply l) hA)]
    congr 1
    rw [← Fintype.sum_equiv (Equiv.addLeft l) (fun j => G (l + j) ((· + v (l + j)) ⁻¹' (L ⁻¹' A)))
      (fun i => G i ((· + v i) ⁻¹' (L ⁻¹' A))) (fun _ => rfl)]
    apply Finset.sum_congr rfl
    intro j _
    have : (φ j ⁻¹' ((fun x => x l) ⁻¹' A)) = {y | y (l + j) + L (v (l + j)) ∈ A} := rfl
    rw [this, hcoord _ _ hA]
    congr 1
    ext x; simp [map_add]


/-- **Lemma pj:lem:gadget (b)**: for distributions `G_i` with mean `0` carried by the closed ball
of radius `ρ₀` about `0`, a unit vector `e` and `λ > n ρ₀`: if `P` is `n`-completely mixable, then
`G_1, …, G_n` are jointly mixable. -/
theorem gadget_b {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Measure E) [∀ i, IsProbabilityMeasure (G i)]
    {ρ₀ lam : ℝ} {e : E} (hsupp : ∀ i, G i (closedBall 0 ρ₀)ᶜ = 0)
    (hmean : ∀ i, ∫ x, x ∂(G i) = 0) (he : ‖e‖ = 1) (hlam : n * ρ₀ < lam)
    (h : CompletelyMixable n (gadP G lam e)) : JointlyMixable G := by
  obtain ⟨P, hP, ⟨s, hs⟩, hmarg⟩ := h
  set v := gadV n lam e
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- `ρ₀ ≥ 0` and `λ > 0`
  have hρ : 0 ≤ ρ₀ := by
    by_contra hneg
    have : closedBall (0 : E) ρ₀ = ∅ := closedBall_eq_empty.2 (not_le.1 hneg)
    have h1 := hsupp ⟨0, by omega⟩
    rw [this, compl_empty, measure_univ] at h1
    exact one_ne_zero h1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlam0 : 0 < lam := by nlinarith
  -- the sum is `0`
  have hint : ∀ i, Integrable (fun x => x) (G i) := fun i => integrable_of_supp (hsupp i)
  have hPint : Integrable (fun x => x) (gadP G lam e) ∧ ∫ x, x ∂(gadP G lam e) = 0 := by
    have hf := integral_fsum Finset.univ (fun i => tr (v i) (G i)) (fun x => x)
      (fun i _ => (integral_tr (hint i) (v i)).1)
    refine ⟨hf.1.smul_measure (ENNReal.inv_ne_top.2 hn0), ?_⟩
    rw [gadP, integral_smul_measure, hf.2,
      Finset.sum_congr rfl (fun i _ => (integral_tr (hint i) (v i)).2)]
    simp only [hmean, zero_add]
    rw [sum_gadV (by omega), smul_zero]
  have hs0 : s = 0 := by
    have hcoord : ∀ j, Integrable (fun x : Fin n → E => x j) P ∧ ∫ x, x j ∂P = 0 := by
      intro j
      have hmj : Measurable (fun x : Fin n → E => x j) := measurable_pi_apply j
      have h1 := hPint.1
      have h2 := hPint.2
      have hmj' : P.map (fun x => x j) = gadP G lam e := hmarg j
      rw [← hmj'] at h1 h2
      rw [integrable_map_measure (continuous_id' : Continuous fun x : E => x).aestronglyMeasurable
        hmj.aemeasurable] at h1
      rw [integral_map hmj.aemeasurable
        (continuous_id' : Continuous fun x : E => x).aestronglyMeasurable] at h2
      exact ⟨h1, h2⟩
    have : ∫ x, ∑ j, x j ∂P = s := by
      rw [integral_congr_ae hs, integral_const]; simp
    rw [← this, integral_finsetSum _ (fun j _ => (hcoord j).1)]
    exact Finset.sum_eq_zero fun j _ => (hcoord j).2
  subst hs0
  set C : Fin n → Set E := fun i => closedBall (v i) ρ₀ with hC
  have hCm : ∀ i, MeasurableSet (C i) := fun i => measurableSet_closedBall
  -- (F1) the balls `C i` are pairwise disjoint
  have hdisj : ∀ i j y, y ∈ C i → y ∈ C j → i = j := by
    intro i j y hi hj
    by_contra hij
    have hd : dist (v i) (v j) ≤ 2 * ρ₀ := by
      simp only [C, mem_closedBall] at hi hj
      calc dist (v i) (v j) ≤ dist (v i) y + dist y (v j) := dist_triangle _ _ _
        _ ≤ ρ₀ + ρ₀ := add_le_add (by rw [dist_comm]; exact hi) hj
        _ = 2 * ρ₀ := by ring
    have ha : (1 : ℝ) ≤ |(gadA n i : ℝ) - gadA n j| := by
      have := Int.one_le_abs (sub_ne_zero.2 ((gadA_inj hn).ne hij))
      exact_mod_cast this
    have : dist (v i) (v j) = lam * |(gadA n i : ℝ) - gadA n j| := by
      simp only [v, gadV, dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
        ← mul_sub, abs_mul, abs_of_pos hlam0]
    nlinarith
  -- (F2) shifting into `C i`
  have hshift : ∀ i y, y + v i ∈ C i ↔ y ∈ closedBall (0 : E) ρ₀ := by
    intro i y; simp [C, mem_closedBall, dist_eq_norm]
  -- (F3) almost every tuple lies in `⋃ C i` with sum `0`
  have hU : MeasurableSet (⋃ i, C i) := MeasurableSet.iUnion hCm
  have hgadU : gadP G lam e (⋃ i, C i)ᶜ = 0 := by
    rw [gadP_apply G lam e hU.compl]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i _
    apply measure_mono_null _ (hsupp i)
    intro y hy hy'
    exact hy (mem_iUnion.2 ⟨i, (hshift i y).2 hy'⟩)
  have hgood : ∀ᵐ x ∂P, (∀ l, ∃ i, x l ∈ C i) ∧ ∑ j, x j = 0 := by
    refine Filter.Eventually.and ?_ hs
    rw [ae_all_iff]
    intro l
    have hml : Measurable (fun x : Fin n → E => x l) := measurable_pi_apply l
    have hmj' : P.map (fun x => x l) = gadP G lam e := hmarg l
    rw [ae_iff]
    have : {x : Fin n → E | ¬ ∃ i, x l ∈ C i} = (fun x => x l) ⁻¹' (⋃ i, C i)ᶜ := by
      ext x; simp
    rw [this, ← Measure.map_apply hml hU.compl, hmj', hgadU]
  -- (F4) for a good tuple, each `C i` contains exactly one coordinate
  have hbij : ∀ x : Fin n → E, (∀ l, ∃ i, x l ∈ C i) → ∑ j, x j = 0 →
      ∃ σ : Fin n ≃ Fin n, ∀ l i, x l ∈ C i ↔ σ l = i := by
    intro x hx hsum
    choose f hf using hx
    have hM : ∑ l, gadA n (f l) = 0 := by
      have hle : ‖∑ l, v (f l)‖ ≤ n * ρ₀ := by
        have : ∑ l, v (f l) = ∑ l, (v (f l) - x l) := by
          rw [Finset.sum_sub_distrib, hsum, sub_zero]
        rw [this]
        refine (norm_sum_le _ _).trans ?_
        have : ∀ l, ‖v (f l) - x l‖ ≤ ρ₀ := fun l => by
          have := hf l; simp only [C, mem_closedBall, dist_eq_norm] at this
          rwa [norm_sub_rev]
        refine (Finset.sum_le_sum fun l _ => this l).trans ?_
        simp
      have heq : ‖∑ l, v (f l)‖ = lam * |((∑ l, gadA n (f l) : ℤ) : ℝ)| := by
        simp only [v, gadV, ← Finset.sum_smul, ← Finset.mul_sum, norm_smul, he, mul_one,
          Real.norm_eq_abs, abs_mul, abs_of_pos hlam0]
        push_cast; rfl
      rw [heq] at hle
      have h1 : |((∑ l, gadA n (f l) : ℤ) : ℝ)| < 1 := by
        by_contra hc; rw [not_lt] at hc; nlinarith
      have h2 : |∑ l, gadA n (f l)| < 1 := by exact_mod_cast h1
      exact Int.abs_lt_one_iff.1 h2
    refine ⟨Equiv.ofBijective f (count_bij hn f hM), fun l i => ?_⟩
    simp only [Equiv.ofBijective_apply]
    constructor
    · intro h; exact hdisj _ _ _ (hf l) h
    · rintro rfl; exact hf l
  -- (F5) the joint mix of the `G i`
  set Ψ : (Fin n → E) → (Fin n → E) :=
    fun x i => ∑ l, (C i).indicator (fun y => y - v i) (x l) with hΨdef
  have hΨm : Measurable Ψ := by
    rw [measurable_pi_iff]; intro i
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_sub_const (v i)).indicator (hCm i)).comp (measurable_pi_apply l)
  have hΨ : ∀ x : Fin n → E, (∀ l, ∃ i, x l ∈ C i) → ∑ j, x j = 0 →
      ∃ σ : Fin n ≃ Fin n, (∀ l i, x l ∈ C i ↔ σ l = i) ∧ ∀ i, Ψ x i = x (σ.symm i) - v i := by
    intro x hx hsum
    obtain ⟨σ, hσ⟩ := hbij x hx hsum
    refine ⟨σ, hσ, fun i => ?_⟩
    simp only [Ψ]
    rw [Finset.sum_eq_single (σ.symm i)]
    · rw [indicator_of_mem ((hσ _ _).2 (σ.apply_symm_apply i))]
    · intro l _ hl
      apply indicator_of_notMem
      rw [hσ]; intro h; apply hl; rw [← h, σ.symm_apply_apply]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨P.map Ψ, ⟨(Measure.isProbabilityMeasure_map_iff hΨm.aemeasurable).2 hP, ⟨0, ?_⟩, ?_⟩⟩
  · have hm : MeasurableSet {y : Fin n → E | ∑ j, y j = 0} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
        measurable_const
    rw [ae_map_iff hΨm.aemeasurable hm]
    filter_upwards [hgood] with x hx
    obtain ⟨σ, -, hσΨ⟩ := hΨ x hx.1 hx.2
    simp only [hσΨ, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp σ.symm (fun l => x l), hx.2, sum_gadV (by omega), sub_zero]
  · intro i
    ext A hA
    set B : Set E := C i ∩ (· - v i) ⁻¹' A with hB
    have hBm : MeasurableSet B := (hCm i).inter ((measurable_sub_const _) hA)
    rw [Measure.map_apply (measurable_pi_apply i) hA, Measure.map_apply hΨm
      ((measurable_pi_apply i) hA), ← lintegral_indicator_one (hΨm ((measurable_pi_apply i) hA))]
    have hpt : ∀ᵐ x ∂P, (Ψ ⁻¹' ((fun x => x i) ⁻¹' A)).indicator 1 x =
        ∑ l, ((fun x : Fin n → E => x l) ⁻¹' B).indicator (1 : (Fin n → E) → ℝ≥0∞) x := by
      filter_upwards [hgood] with x hx
      obtain ⟨σ, hσ, hσΨ⟩ := hΨ x hx.1 hx.2
      rw [Finset.sum_eq_single (σ.symm i)]
      · have hxC : x (σ.symm i) ∈ C i := (hσ _ _).2 (σ.apply_symm_apply i)
        by_cases hA' : x (σ.symm i) - v i ∈ A
        · rw [indicator_of_mem, indicator_of_mem]
          · exact ⟨hxC, hA'⟩
          · show Ψ x i ∈ A; rw [hσΨ]; exact hA'
        · rw [indicator_of_notMem, indicator_of_notMem]
          · intro h; exact hA' h.2
          · show Ψ x i ∉ A; rw [hσΨ]; exact hA'
      · intro l _ hl
        apply indicator_of_notMem
        intro h
        have := (hσ _ _).1 h.1
        apply hl; rw [← this, σ.symm_apply_apply]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [lintegral_congr_ae hpt, lintegral_finsetSum _ (fun l _ =>
      (measurable_one.indicator ((measurable_pi_apply l) hBm)))]
    have hl : ∀ l, ∫⁻ x, ((fun x : Fin n → E => x l) ⁻¹' B).indicator 1 x ∂P = (n : ℝ≥0∞)⁻¹ * G i A := by
      intro l
      rw [lintegral_indicator_one ((measurable_pi_apply l) hBm),
        ← Measure.map_apply (measurable_pi_apply l) hBm]
      have hmj' : P.map (fun x => x l) = gadP G lam e := hmarg l
      rw [hmj', gadP_apply G lam e hBm, Finset.sum_eq_single i]
      · congr 1
        have : (· + v i) ⁻¹' B = closedBall 0 ρ₀ ∩ A := by
          ext y; simp only [B, mem_preimage, mem_inter_iff, hshift, add_sub_cancel_right]
        rw [this, inter_comm, measure_inter_conull (hsupp i)]
      · intro j _ hj
        apply measure_mono_null _ (hsupp j)
        intro y hy hy'
        exact hj (hdisj _ _ _ ((hshift j y).2 hy') hy.1)
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun l _ => hl l), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hn0 (by simp), one_mul]


end Gadget

end Mixes.ProjLemmas
