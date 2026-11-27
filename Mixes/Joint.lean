import Mixes.Defs

/-!
# Part II: joint mixes from segments in the hyperplane of constant sum

* `segMeasure P Q`: the uniform distribution `ν_{[P,Q]}` on the segment `[P, Q]` of `ℝⁿ`
  (the point mass at `P` when `P = Q`); `segMix w P Q = ∑ wₑ ν_{[Pₑ,Qₑ]}`.
* `seg_mix`, `seg_mix_density` (Lemma 16, `j:lem:seg`).
* `lem17` (Lemma 17, `j:lem:three`) and `lem18` (Lemma 18, `j:lem:uni`).
* `P24.caseI_mix`, …, `P24.caseIIIb_mix`, `P24.cases_cover`, `P24.cases_exclusive`,
  `P24.wI_sum` and `prop24` (Proposition 24, `j:prop:three`).

The marginals are identified by writing every finite mixture of uniform distributions as a step
density plus an atom at `0` (`mix_unifI_eq`) and comparing the step densities pointwise on the
intervals between consecutive endpoints. The coordinate lemmas `P24.caseX_coordj` were produced
by a small generator from the table of the paper and share the tactics `step_simp`,
`region_close`, `alg_close` and `disj_close`.
-/

open MeasureTheory Set

-- The generated proofs of Proposition 24 share one simp set for all cases.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Mixes

lemma unifI_self (l : ℝ) : unifI l l = Measure.dirac l := by simp [unifI]

lemma unifI_of_lt {l r : ℝ} (h : l < r) :
    unifI l r = (ENNReal.ofReal (r - l))⁻¹ • volume.restrict (Icc l r) := by
  simp [unifI, h]

lemma unifI01 : unifI 0 1 = volume.restrict (Icc (0 : ℝ) 1) := by
  rw [unifI_of_lt one_pos]; simp

/-- The image of `U[0,1]` under an affine map with nonzero slope. -/
lemma map_affine_unifI (p a : ℝ) (ha : a ≠ 0) :
    (unifI 0 1).map (fun v => p + a * v) = unifI (min p (p + a)) (max p (p + a)) := by
  set f : ℝ → ℝ := fun v => p + a * v with hfdef
  have hemb : MeasurableEmbedding f := by
    have : f = (Homeomorph.addLeft p) ∘ (Homeomorph.mulLeft₀ a ha) := by
      funext v; simp [hfdef]
    rw [this]
    exact (Homeomorph.addLeft p).measurableEmbedding.comp
      (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  have hlt : min p (p + a) < max p (p + a) := by
    rcases lt_or_gt_of_ne ha with h | h
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; linarith
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; linarith
  have hlen : max p (p + a) - min p (p + a) = |a| := by
    rcases lt_or_gt_of_ne ha with h | h
    · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_neg h]; ring
    · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_pos h]; ring
  have hpre : f ⁻¹' Icc (min p (p + a)) (max p (p + a)) = Icc 0 1 := by
    ext v
    simp only [mem_preimage, mem_Icc, hfdef]
    rcases lt_or_gt_of_ne ha with h | h
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · by_contra hc; rw [not_le] at hc; nlinarith
        · by_contra hc; rw [not_le] at hc; nlinarith
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · by_contra hc; rw [not_le] at hc; nlinarith
        · by_contra hc; rw [not_le] at hc; nlinarith
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  have hmapvol : volume.map f = ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ) := by
    have : f = (fun v => p + v) ∘ (fun v => a * v) := by funext v; simp [hfdef]
    rw [this, ← Measure.map_map (measurable_const_add p) (measurable_const_mul a),
      Real.map_volume_mul_left ha, Measure.map_smul,
      (measurePreserving_add_left volume p).map_eq]
    exact (measurable_const_add p).aemeasurable
  rw [unifI01, ← hpre, ← hemb.restrict_map, hmapvol, Measure.restrict_smul, unifI_of_lt hlt,
    hlen, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr ha)]

/-- The image of `U[0,1]` under `v ↦ p + v (q - p)` is the uniform distribution on the interval
with endpoints `p` and `q` (the point mass when `p = q`). -/
lemma map_seg_unifI (p q : ℝ) :
    (unifI 0 1).map (fun v => p + v * (q - p)) = unifI (min p q) (max p q) := by
  by_cases hpq : p = q
  · subst hpq
    simp only [sub_self, mul_zero, add_zero, min_self, max_self, unifI_self]
    rw [Measure.map_const]
    have := unifI_isProb 0 1
    simp
  · have := map_affine_unifI p (q - p) (sub_ne_zero.mpr (Ne.symm hpq))
    simp only [add_sub_cancel] at this
    rw [← this]
    congr 1; funext v; ring

/-! ### Segment measures and Lemma 16 -/

variable {n : ℕ}

/-- The uniform distribution `ν_{[P,Q]}` on the segment `[P, Q]` of `ℝⁿ`: the law of
`P + V (Q - P)` with `V ∼ U[0,1]` (the point mass at `P` if `P = Q`). -/
def segMeasure (P Q : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (unifI 0 1).map (fun v : ℝ => P + v • (Q - P))

lemma measurable_segMap (P Q : Fin n → ℝ) : Measurable (fun v : ℝ => P + v • (Q - P)) := by
  fun_prop

instance segMeasure_isProb (P Q : Fin n → ℝ) : IsProbabilityMeasure (segMeasure P Q) := by
  have := unifI_isProb 0 1
  unfold segMeasure; infer_instance

/-- The `j`-th marginal of `ν_{[P,Q]}` is the uniform distribution on the projection. -/
lemma segMeasure_map_coord (P Q : Fin n → ℝ) (j : Fin n) :
    (segMeasure P Q).map (fun x => x j) = unifI (min (P j) (Q j)) (max (P j) (Q j)) := by
  unfold segMeasure
  rw [Measure.map_map (measurable_pi_apply j) (measurable_segMap P Q), ← map_seg_unifI]
  congr 1

lemma segMeasure_ae_sum {P Q : Fin n → ℝ} {s : ℝ} (hP : ∑ j, P j = s) (hQ : ∑ j, Q j = s) :
    ∀ᵐ x ∂segMeasure P Q, ∑ j, x j = s := by
  unfold segMeasure
  rw [ae_map_iff (measurable_segMap P Q).aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine Filter.Eventually.of_forall (fun v => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hP, hQ]
  ring

lemma segMeasure_integrable_coord (P Q : Fin n → ℝ) (j : Fin n) :
    Integrable (fun x => x j) (segMeasure P Q) := by
  unfold segMeasure
  rw [integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable
    (measurable_segMap P Q).aemeasurable, unifI01]
  exact Continuous.integrableOn_Icc (by fun_prop)

lemma integrable_finset_sum_measure' {α : Type*} [MeasurableSpace α] {ι : Type*}
    (s : Finset ι) (μ : ι → Measure α) (f : α → ℝ) (h : ∀ e ∈ s, Integrable f (μ e)) :
    Integrable f (∑ e ∈ s, μ e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add_measure (ih fun e he => h e (by simp [he]))

/-- A finite mixture `∑ₑ wₑ ν_{[Pₑ,Qₑ]}` of segment measures (weights given as reals). -/
def segMix {ι : Type*} [Fintype ι] (w : ι → ℝ) (P Q : ι → Fin n → ℝ) : Measure (Fin n → ℝ) :=
  ∑ e, ENNReal.ofReal (w e) • segMeasure (P e) (Q e)

lemma segMix_map {ι : Type*} [Fintype ι] (w : ι → ℝ) (P Q : ι → Fin n → ℝ) (j : Fin n) :
    (segMix w P Q).map (fun x => x j) =
      ∑ e, ENNReal.ofReal (w e) • unifI (min (P e j) (Q e j)) (max (P e j) (Q e j)) := by
  unfold segMix
  rw [Measure.map_finset_sum' (measurable_pi_apply j).aemeasurable]
  congr 1; funext e
  rw [Measure.map_smul, segMeasure_map_coord]
  exact (measurable_pi_apply j).aemeasurable

lemma segMix_univ {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ e, 0 ≤ w e)
    (P Q : ι → Fin n → ℝ) : segMix w P Q univ = ENNReal.ofReal (∑ e, w e) := by
  unfold segMix
  rw [sum_apply, ENNReal.ofReal_sum_of_nonneg (fun e _ => hw e)]
  congr 1; funext e
  simp

lemma segMix_ae_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) {P Q : ι → Fin n → ℝ} {s : ℝ}
    (hP : ∀ e, ∑ j, P e j = s) (hQ : ∀ e, ∑ j, Q e j = s) :
    ∀ᵐ x ∂segMix w P Q, ∑ j, x j = s := by
  rw [ae_iff]
  unfold segMix
  rw [sum_apply]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [smul_apply, ← ae_iff.mp (segMeasure_ae_sum (hP e) (hQ e)), smul_eq_mul]
  simp [ae_iff.mp (segMeasure_ae_sum (hP e) (hQ e))]

/-- **Lemma 16** (`j:lem:seg`), first part. Let `[Pₑ, Qₑ]` be finitely many segments with
endpoints in `H_s = {x : x₁ + ⋯ + xₙ = s}` and `wₑ ≥ 0` weights with `∑ wₑ = 1`. Then the mixture
`X ∼ ∑ wₑ ν_{[Pₑ,Qₑ]}` is a probability measure with `X₁ + ⋯ + Xₙ = s` almost surely, the means
of its coordinates add up to `s`, and `Xⱼ ∼ ∑ wₑ U(Iⱼᵉ)`, where `Iⱼᵉ` is the projection of the
`e`-th segment on coordinate `j`. -/
theorem seg_mix {ι : Type*} [Fintype ι] (w : ι → ℝ) (P Q : ι → Fin n → ℝ) (s : ℝ)
    (hw : ∀ e, 0 ≤ w e) (hw1 : ∑ e, w e = 1)
    (hP : ∀ e, ∑ j, P e j = s) (hQ : ∀ e, ∑ j, Q e j = s) :
    IsProbabilityMeasure (segMix w P Q) ∧ (∀ᵐ x ∂segMix w P Q, ∑ j, x j = s) ∧
      (∑ j, ∫ x, x j ∂segMix w P Q) = s ∧
      ∀ j, (segMix w P Q).map (fun x => x j) =
        ∑ e, ENNReal.ofReal (w e) • unifI (min (P e j) (Q e j)) (max (P e j) (Q e j)) := by
  have hprob : IsProbabilityMeasure (segMix w P Q) := ⟨by rw [segMix_univ hw, hw1]; simp⟩
  refine ⟨hprob, segMix_ae_sum w hP hQ, ?_, segMix_map w P Q⟩
  have hint : ∀ j, Integrable (fun x : Fin n → ℝ => x j) (segMix w P Q) := fun j =>
    integrable_finset_sum_measure' _ _ _ (fun e _ =>
      (segMeasure_integrable_coord _ _ j).smul_measure ENNReal.ofReal_ne_top)
  rw [← integral_finsetSum _ (fun j _ => hint j),
    integral_congr_ae (segMix_ae_sum w hP hQ)]
  simp

lemma unifI_restrict_Ioo {l r u v : ℝ} (hlr : l ≤ r) (hl : l ∉ Ioo u v) (hr : r ∉ Ioo u v) :
    (unifI l r).restrict (Ioo u v) =
      if l < r ∧ l ≤ u ∧ v ≤ r then (ENNReal.ofReal (r - l))⁻¹ • volume.restrict (Ioo u v)
      else 0 := by
  rcases hlr.lt_or_eq with hlt | rfl
  · rw [unifI_of_lt hlt, Measure.restrict_smul, Measure.restrict_restrict measurableSet_Ioo]
    by_cases hc : l ≤ u ∧ v ≤ r
    · simp only [show (l < r ∧ l ≤ u ∧ v ≤ r) = True from eq_true ⟨hlt, hc⟩, ite_true]
      rw [inter_eq_left.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc hc.1 hc.2))]
    · simp only [show (l < r ∧ l ≤ u ∧ v ≤ r) = False from eq_false (fun h => hc h.2),
        ite_false]
      have : Ioo u v ∩ Icc l r = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        rintro ⟨hux, hxv⟩ hlx hxr
        simp only [mem_Ioo, not_and, not_lt] at hl hr
        apply hc
        constructor
        · by_contra h1; push Not at h1; linarith [hl h1]
        · by_contra h2; push Not at h2; linarith [hr (by linarith)]
      rw [this, Measure.restrict_empty, smul_zero]
  · simp only [show (l < l ∧ l ≤ u ∧ v ≤ l) = False from eq_false (fun h => lt_irrefl _ h.1),
      ite_false]
    rw [unifI_self, Measure.restrict_eq_zero, Measure.dirac_apply' _ measurableSet_Ioo]
    simp [hl]

lemma restrict_finset_sum' {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ) (t : Set ℝ) :
    (∑ i ∈ s, μ i).restrict t = ∑ i ∈ s, (μ i).restrict t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.restrict_add, ih]

/-- **Lemma 16** (`j:lem:seg`), second part. On an open interval `(u, v)` that contains no
endpoint of a projection on coordinate `j`, the `j`-th marginal of `∑ wₑ ν_{[Pₑ,Qₑ]}` has the
constant density `∑ wₑ/|Iⱼᵉ|`, the sum running over the non-degenerate projections `Iⱼᵉ` that
contain `(u, v)`. -/
theorem seg_mix_density {ι : Type*} [Fintype ι] (w : ι → ℝ) (P Q : ι → Fin n → ℝ)
    (hw : ∀ e, 0 ≤ w e) (j : Fin n) {u v : ℝ}
    (hend : ∀ e, min (P e j) (Q e j) ∉ Ioo u v ∧ max (P e j) (Q e j) ∉ Ioo u v) :
    ((segMix w P Q).map (fun x => x j)).restrict (Ioo u v) =
      ENNReal.ofReal (∑ e ∈ Finset.univ.filter (fun e => min (P e j) (Q e j) < max (P e j) (Q e j)
          ∧ min (P e j) (Q e j) ≤ u ∧ v ≤ max (P e j) (Q e j)),
        w e / (max (P e j) (Q e j) - min (P e j) (Q e j))) • volume.restrict (Ioo u v) := by
  classical
  rw [segMix_map, restrict_finset_sum']
  simp only [Measure.restrict_smul]
  rw [Finset.sum_filter, ENNReal.ofReal_sum_of_nonneg, Finset.sum_smul]
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [unifI_restrict_Ioo min_le_max (hend e).1 (hend e).2]
    split_ifs with hc
    · rw [smul_smul, div_eq_mul_inv, ENNReal.ofReal_mul (hw e),
        ENNReal.ofReal_inv_of_pos (sub_pos.mpr hc.1)]
    · simp
  · intro e _
    split_ifs with hc
    · exact div_nonneg (hw e) (sub_pos.mpr hc.1).le
    · exact le_refl 0

/-! ### Step densities

To identify the marginals of the constructions we write every finite mixture of uniform
distributions on `ℝ` as a measure with a step density plus an atom at `0`. -/

/-- The step function equal to `d` on `(l, r]` and to `0` elsewhere. -/
def dstep (d l r x : ℝ) : ℝ := Set.indicator (Ioc l r) (fun _ => d) x

lemma dstep_left {d l r x : ℝ} (h : x ≤ l) : dstep d l r x = 0 := by
  simp [dstep, Set.indicator, mem_Ioc, not_lt.mpr h]

lemma dstep_right {d l r x : ℝ} (h : r < x) : dstep d l r x = 0 := by
  simp [dstep, Set.indicator, mem_Ioc, not_le.mpr h]

lemma dstep_mid {d l r x : ℝ} (h1 : l < x) (h2 : x ≤ r) : dstep d l r x = d := by
  simp [dstep, Set.indicator, mem_Ioc, h1, h2]

lemma dstep_nonneg {d l r : ℝ} (hd : 0 ≤ d) (x : ℝ) : 0 ≤ dstep d l r x := by
  unfold dstep; by_cases h : x ∈ Ioc l r <;> simp [h, hd]

lemma measurable_dstep (d l r : ℝ) : Measurable (dstep d l r) :=
  measurable_const.indicator measurableSet_Ioc

/-- A measure with the step density `f` and an atom of mass `α` at `0`. -/
def stepRep (f : ℝ → ℝ) (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x)) + ENNReal.ofReal α • Measure.dirac 0

lemma stepRep_congr {f g : ℝ → ℝ} {α β : ℝ} (hfg : ∀ x, f x = g x) (hαβ : α = β) :
    stepRep f α = stepRep g β := by
  have : f = g := funext hfg
  subst this hαβ; rfl

/-- One term: `w • U[l,r] = (step density d on (l,r]) + (w - d (r - l)) δ₀` when either
`w = d (r - l)` or the interval is `{0}`. -/
lemma smul_unifI_eq {w d l r : ℝ} (hd : 0 ≤ d) (hlr : l ≤ r)
    (h : w = d * (r - l) ∨ (l = 0 ∧ r = 0)) :
    ENNReal.ofReal w • unifI l r =
      volume.withDensity (fun x => ENNReal.ofReal (dstep d l r x)) +
        ENNReal.ofReal (w - d * (r - l)) • Measure.dirac 0 := by
  rcases h with h | ⟨rfl, rfl⟩
  · rw [h, sub_self, ENNReal.ofReal_zero, zero_smul, add_zero]
    rcases hlr.lt_or_eq with hlt | rfl
    · rw [unifI_of_lt hlt, smul_smul, ENNReal.ofReal_mul hd,
        mul_assoc, ENNReal.mul_inv_cancel (by simpa using hlt) ENNReal.ofReal_ne_top, mul_one,
        Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      have : (fun x => ENNReal.ofReal (dstep d l r x)) =
          (Ioc l r).indicator (fun _ => ENNReal.ofReal d) := by
        funext x; unfold dstep; by_cases hx : x ∈ Ioc l r <;> simp [hx]
      rw [this, withDensity_indicator measurableSet_Ioc, withDensity_const]
    · have : (fun x => ENNReal.ofReal (dstep d l l x)) = fun _ => 0 := by
        funext x; simp [dstep]
      simp [this]
  · have : (fun x => ENNReal.ofReal (dstep d 0 0 x)) = fun _ => 0 := by
      funext x; simp [dstep]
    simp [this, unifI_self]

lemma withDensity_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x) :
    volume.withDensity (fun x => ENNReal.ofReal (∑ i ∈ s, f i x)) =
      ∑ i ∈ s, volume.withDensity (fun x => ENNReal.ofReal (f i x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have : (fun x => ENNReal.ofReal (∑ i ∈ insert a s, f i x)) =
        (fun x => ENNReal.ofReal (f a x)) + fun x => ENNReal.ofReal (∑ i ∈ s, f i x) := by
      funext x
      rw [Finset.sum_insert ha, Pi.add_apply,
        ENNReal.ofReal_add (hf0 a x) (Finset.sum_nonneg fun i _ => hf0 i x)]
    rw [this, withDensity_add_left (hf a).ennreal_ofReal]

/-- A finite mixture `∑ wₑ U[lₑ, rₑ]` as a step density plus an atom at `0`, given for each term
either `wₑ = dₑ (rₑ - lₑ)` or `lₑ = rₑ = 0`. -/
lemma mix_unifI_eq {ι : Type*} [Fintype ι] (w d lo hi : ι → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hd : ∀ e, 0 ≤ d e) (hlh : ∀ e, lo e ≤ hi e)
    (h : ∀ e, w e = d e * (hi e - lo e) ∨ (lo e = 0 ∧ hi e = 0)) :
    ∑ e, ENNReal.ofReal (w e) • unifI (lo e) (hi e) =
      stepRep (fun x => ∑ e, dstep (d e) (lo e) (hi e) x)
        (∑ e, (w e - d e * (hi e - lo e))) := by
  have hα : ∀ e, 0 ≤ w e - d e * (hi e - lo e) := by
    intro e; rcases h e with h | ⟨h1, h2⟩
    · rw [h, sub_self]
    · rw [h1, h2]; simpa using hw e
  simp only [fun e => smul_unifI_eq (hd e) (hlh e) (h e), Finset.sum_add_distrib]
  rw [stepRep, withDensity_finset_sum' _ _ (fun e => measurable_dstep _ _ _)
    (fun e x => dstep_nonneg (hd e) x), ← Finset.sum_smul,
    ENNReal.ofReal_sum_of_nonneg (fun e _ => hα e)]

/-- Scaling: `Λ • (∑ wₑ U[lₑ,rₑ]) = ∑ (Λ wₑ) U[lₑ,rₑ]`. -/
lemma smul_mix_unifI {ι : Type*} [Fintype ι] {Λ : ℝ} (hΛ : 0 ≤ Λ) (w lo hi : ι → ℝ) :
    ENNReal.ofReal Λ • ∑ e, ENNReal.ofReal (w e) • unifI (lo e) (hi e) =
      ∑ e, ENNReal.ofReal (Λ * w e) • unifI (lo e) (hi e) := by
  rw [Finset.smul_sum]
  congr 1; funext e
  rw [smul_smul, ENNReal.ofReal_mul hΛ]

/-- Normalising a finite mixture of segment measures: if the unnormalised marginals are
`Λ • F j`, the normalised mixture is a joint mix of the `F j` with sum `s`. -/
lemma isJointMix_segMix {ι : Type*} [Fintype ι] (w : ι → ℝ) (P Q : ι → Fin n → ℝ) (s Λ : ℝ)
    (F : Fin n → Measure ℝ) (hw : ∀ e, 0 ≤ w e) (hΛ : ∑ e, w e = Λ) (hΛ0 : 0 < Λ)
    (hP : ∀ e, ∑ j, P e j = s) (hQ : ∀ e, ∑ j, Q e j = s)
    (hF : ∀ j, ∑ e, ENNReal.ofReal (w e) • unifI (min (P e j) (Q e j)) (max (P e j) (Q e j)) =
      ENNReal.ofReal Λ • F j) :
    IsJointMix F (segMix (fun e => w e / Λ) P Q) ∧ (∀ᵐ x ∂segMix (fun e => w e / Λ) P Q,
      ∑ j, x j = s) := by
  have hw' : ∀ e, 0 ≤ w e / Λ := fun e => div_nonneg (hw e) hΛ0.le
  have hw1 : ∑ e, w e / Λ = 1 := by rw [← Finset.sum_div, hΛ, div_self hΛ0.ne']
  obtain ⟨hprob, hsum, -, hmap⟩ := seg_mix (fun e => w e / Λ) P Q s hw' hw1 hP hQ
  refine ⟨⟨hprob, ⟨s, hsum⟩, fun j => ?_⟩, hsum⟩
  rw [hmap j]
  simp_rw [div_eq_inv_mul]
  rw [← smul_mix_unifI (inv_nonneg.mpr hΛ0.le), hF j, smul_smul, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr hΛ0.le), inv_mul_cancel₀ hΛ0.ne']
  simp

/-- The distribution `g^μ_{a,b} = p U[0,a] + q U[0,b]` with `p = (b - 2μ)/(b - a)` and
`q = (2μ - a)/(b - a)` (a "piece" with two steps; `U[0,0] = δ₀`). -/
def gPiece (μ a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((b - 2 * μ) / (b - a)) • unifI 0 a +
    ENNReal.ofReal ((2 * μ - a) / (b - a)) • unifI 0 b

lemma target_unif {Λ c : ℝ} (hΛ : 0 ≤ Λ) (hc : 0 < c) :
    ENNReal.ofReal Λ • unifI 0 c = stepRep (dstep (Λ / c) 0 c) 0 := by
  rw [smul_unifI_eq (div_nonneg hΛ hc.le) hc.le (Or.inl (by field_simp; ring))]
  unfold stepRep; congr 2; rw [sub_zero, div_mul_cancel₀ _ hc.ne', sub_self]

lemma target_g {Λ μ a b : ℝ} (hΛ : 0 ≤ Λ) (ha : 0 ≤ a) (ha2 : a < 2 * μ) (hb : 2 * μ < b) :
    ENNReal.ofReal Λ • gPiece μ a b =
      stepRep (fun x => dstep (Λ * ((b - 2 * μ) / (b - a)) / a) 0 a x +
          dstep (Λ * ((2 * μ - a) / (b - a)) / b) 0 b x)
        (if a = 0 then Λ * ((b - 2 * μ) / (b - a)) else 0) := by
  have hba : 0 < b - a := by linarith
  have hp : 0 ≤ (b - 2 * μ) / (b - a) := div_nonneg (by linarith) hba.le
  have hq : 0 ≤ (2 * μ - a) / (b - a) := div_nonneg (by linarith) hba.le
  have hb0 : 0 < b := by linarith
  have e : gPiece μ a b = ∑ e : Fin 2, ENNReal.ofReal (![(b - 2 * μ) / (b - a),
      (2 * μ - a) / (b - a)] e) • unifI (![0, 0] e) (![a, b] e) := by
    simp [gPiece, Fin.sum_univ_two]
  rw [e, smul_mix_unifI hΛ, mix_unifI_eq _ ![Λ * ((b - 2 * μ) / (b - a)) / a,
    Λ * ((2 * μ - a) / (b - a)) / b]]
  · apply stepRep_congr
    · intro x; simp [Fin.sum_univ_two]
    · rcases ha.lt_or_eq with ha0 | rfl
      · simp only [Fin.sum_univ_two, Matrix.cons_val, ha0.ne', ite_false]
        field_simp; ring
      · simp only [Fin.sum_univ_two, Matrix.cons_val, ite_true]
        field_simp; ring
  · intro e; fin_cases e <;> simp <;> positivity
  · intro e; fin_cases e <;> simp <;> positivity
  · intro e; fin_cases e <;> simp <;> linarith
  · intro e; fin_cases e
    · rcases ha.lt_or_eq with ha0 | rfl
      · left; simp; field_simp
      · right; simp
    · left; simp; field_simp

/-! ### Proposition 24 (`j:prop:three`)

We use the parameters `y₁ = s - c₁`, `y₂ = s - c₂`, `σ = s - 2μ`, `a`, `b`; then
`s = σ + y₁ + y₂`, `c₁ = σ + y₂`, `c₂ = σ + y₁`, `2μ = y₁ + y₂`. The hypotheses
`c₂ ≤ c₁ ≤ s`, `0 ≤ a < 2μ < b ≤ s` become `0 ≤ y₁ ≤ y₂` and `0 ≤ a < y₁ + y₂ < b ≤ σ + y₁ + y₂`
(and `c₂ > 0` follows). -/

namespace P24

/-- The hypotheses of Proposition 24 in the parameters `y₁, y₂, σ, a, b`. -/
structure Hyp (y1 y2 σ a b : ℝ) : Prop where
  hy1 : 0 ≤ y1
  hy12 : y1 ≤ y2
  ha : 0 ≤ a
  ha2 : a < y1 + y2
  hb : y1 + y2 < b
  hbs : b ≤ σ + y1 + y2

/-- `K_ℓ = σ ℓ + y₁ y₂`. -/
def K (y1 y2 σ l : ℝ) : ℝ := l * σ + y1 * y2

/-- `A(ℓ) = (0, s - ℓ, ℓ)`. -/
def A (y1 y2 σ l : ℝ) : Fin 3 → ℝ := ![0, σ + y1 + y2 - l, l]
/-- `A'(ℓ) = (s - ℓ, 0, ℓ)`. -/
def A' (y1 y2 σ l : ℝ) : Fin 3 → ℝ := ![σ + y1 + y2 - l, 0, l]
/-- `B = (y₂, c₂, 0)`. -/
def B (y1 y2 σ : ℝ) : Fin 3 → ℝ := ![y2, σ + y1, 0]
/-- `C = (c₁, 0, y₁)`. -/
def C (y1 y2 σ : ℝ) : Fin 3 → ℝ := ![σ + y2, 0, y1]
/-- `D(ℓ) = (y₂ - ℓ, c₂, ℓ)`. -/
def D (y1 y2 σ l : ℝ) : Fin 3 → ℝ := ![y2 - l, σ + y1, l]
/-- `D'(ℓ) = (c₁, y₁ - ℓ, ℓ)`. -/
def D' (y1 y2 σ l : ℝ) : Fin 3 → ℝ := ![σ + y2, y1 - l, l]
/-- `E = (0, c₂, y₂)`. -/
def E (y1 y2 σ : ℝ) : Fin 3 → ℝ := ![0, σ + y1, y2]

/-! #### Case (I): `a ≥ y₂` -/

/-- The weights of case (I): `u_a, v_a, u_b, v_b, w`. -/
def wI (y1 y2 σ a b : ℝ) : Fin 5 → ℝ :=
  let s := σ + y1 + y2
  let p := (b - (y1 + y2)) / (b - a)
  let q := ((y1 + y2) - a) / (b - a)
  ![p * (a - y1) * (a - y2) / K y1 y2 σ a, p * (s - a) * (a - y1) / K y1 y2 σ a,
    q * (b - y1) * (b - y2) / K y1 y2 σ b, q * (s - b) * (b - y1) / K y1 y2 σ b,
    y1 * (p * (s - a) / K y1 y2 σ a + q * (s - b) / K y1 y2 σ b)]

/-- The segments of case (I): `[A(a),B], [A(a),C], [A(b),B], [A(b),C], [B,C]`. -/
def PI (y1 y2 σ a b : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![A y1 y2 σ a, A y1 y2 σ a, A y1 y2 σ b, A y1 y2 σ b, B y1 y2 σ]
/-- Second endpoints of the segments of case (I). -/
def QI (y1 y2 σ : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![B y1 y2 σ, C y1 y2 σ, B y1 y2 σ, C y1 y2 σ, C y1 y2 σ]

/-- Evaluates step densities and `min`/`max` once the order is known. -/
macro "step_simp" : tactic => `(tactic|
  simp (disch := with_unfolding_all linarith) only [dstep_left, dstep_right, dstep_mid,
      min_eq_left, min_eq_right,
    max_eq_left, max_eq_right])

/-- Closes an algebraic identity. -/
macro "fs_disch" : tactic => `(tactic|
  first
  | assumption
  | (apply ne_of_gt; with_unfolding_all linarith)
  | (apply ne_of_lt; with_unfolding_all linarith)
  | with_unfolding_all linarith)

/-- Closes an algebraic identity. -/
macro "alg_close" : tactic => `(tactic|
  first
  | (simp; done)
  | ring1
  | (field_simp (disch := fs_disch); done)
  | (field_simp (disch := fs_disch); ring1))

/-- Closes the goal of one region: empty region, or an algebraic identity. -/
macro "region_close" : tactic => `(tactic|
  first
  | (exfalso; linarith)
  | ((try step_simp); alg_close))

/-! #### Cases (II), (II₀), (IIIa), (IIIb): weights and segments -/

/-- The weights of case (II): `α, β, γ, δ, ε`. -/
def wII (y1 y2 σ a b : ℝ) : Fin 5 → ℝ :=
  let s := σ + y1 + y2
  let P := (b - y1) * (b - y2)
  let Q := (y2 - a) * (a - y1)
  let N := (s - b) * Q + (σ + a) * P
  let β := y1 * y2 * N
  let δ := (b - (y1 + y2)) * K y1 y2 σ b * Q
  ![(s - b) * (β + δ) / (b - y2), β, σ * y1 * N, δ,
    (b - (y1 + y2)) * K y1 y2 σ b * (a - y1) * (σ + a)]

/-- Case (II): `[A(b),C], [A(b),B], [B,C], [A(b),D(a)], [D(a),C]`. -/
def PII (y1 y2 σ a b : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![A y1 y2 σ b, A y1 y2 σ b, B y1 y2 σ, A y1 y2 σ b, D y1 y2 σ a]
/-- Second endpoints of the segments of case (II). -/
def QII (y1 y2 σ a : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![C y1 y2 σ, B y1 y2 σ, C y1 y2 σ, D y1 y2 σ a, C y1 y2 σ]

/-- The weights of case (II₀): `α₀, δ₀, ε₀`. -/
def wII0 (y1 y2 σ a b : ℝ) : Fin 3 → ℝ :=
  let s := σ + y1 + y2
  ![(s - b) * ((y1 + y2) - a) / (b - (y1 + y2)), (y1 + y2) - a, σ + a]

/-- Case (II₀): `[A(b),C], [A(b),D(a)], [D(a),C]`. -/
def PII0 (y1 y2 σ a b : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![A y1 y2 σ b, A y1 y2 σ b, D y1 y2 σ a]
/-- Second endpoints of the segments of case (II₀). -/
def QII0 (y1 y2 σ a : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![C y1 y2 σ, D y1 y2 σ a, C y1 y2 σ]

/-- `N₂ = σ (y₁ - a) + (σ + a)(b - y₁)`. -/
def N2 (y1 σ a b : ℝ) : ℝ := σ * (y1 - a) + (σ + a) * (b - y1)

/-- `N₄ = (σ + a)(b - y₁)(b - y₂) - (s - b)(y₁ - a)(y₂ - a)`. -/
def N4 (y1 y2 σ a b : ℝ) : ℝ :=
  (σ + a) * (b - y1) * (b - y2) - (σ + y1 + y2 - b) * (y1 - a) * (y2 - a)

/-- The weights of case (IIIa): `κ₁, …, κ₅`. -/
def wIIIa (y1 y2 σ a b : ℝ) : Fin 5 → ℝ :=
  let s := σ + y1 + y2
  let κ2 := σ * N4 y1 y2 σ a b
  let κ4 := (s - b) * (y2 - a) * N2 y1 σ a b
  ![(y1 - a) * (κ2 + κ4) / (σ + a), κ2, (b - (σ + y1)) * N4 y1 y2 σ a b, κ4,
    (s - b) * (b - y2) * N2 y1 σ a b]

/-- Case (IIIa): `[D'(a),A'(b)], [D'(a),B], [A'(b),B], [D'(a),E], [A'(b),E]`. -/
def PIIIa (y1 y2 σ a b : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![D' y1 y2 σ a, D' y1 y2 σ a, A' y1 y2 σ b, D' y1 y2 σ a, A' y1 y2 σ b]
/-- Second endpoints of the segments of case (IIIa). -/
def QIIIa (y1 y2 σ b : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![A' y1 y2 σ b, B y1 y2 σ, B y1 y2 σ, E y1 y2 σ, E y1 y2 σ]

/-- The weights of case (IIIb): `λ₁, …, λ₅`, with `R = σ b + a y₂`. -/
def wIIIb (y1 y2 σ a b : ℝ) : Fin 5 → ℝ :=
  let R := σ * b + a * y2
  ![σ * (σ + a) * (b * (b - (y1 + y2)) + a * y2), y2 * (b - y2) * N2 y1 σ a b,
    y2 * ((σ + y2) - b + a) * N2 y1 σ a b, ((σ + y1) - b) * (y1 - a) * R,
    (b - y1) * (y1 - a) * R]

/-- Case (IIIb): `[B,D'(a)], [B,A(b)], [D'(a),A(b)], [B,A'(b)], [D'(a),A'(b)]`. -/
def PIIIb (y1 y2 σ a : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![B y1 y2 σ, B y1 y2 σ, D' y1 y2 σ a, B y1 y2 σ, D' y1 y2 σ a]
/-- Second endpoints of the segments of case (IIIb). -/
def QIIIb (y1 y2 σ a b : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![D' y1 y2 σ a, A y1 y2 σ b, A y1 y2 σ b, A' y1 y2 σ b, A' y1 y2 σ b]

set_option hygiene false in
/-- Closes the disjunction `w = d (r - l) ∨ (l = 0 ∧ r = 0)` of `mix_unifI_eq`. -/
macro "disj_close" : tactic => `(tactic|
  first
  | (left; (try step_simp);
     (try simp only [wI, wII, wII0, wIIIa, wIIIb, N2, N4, K, Matrix.cons_val]); alg_close; done)
  | (rcases ha.lt_or_eq with ha0 | ha0
     (left; (try step_simp); alg_close)
     (right; subst ha0; (try step_simp); simp)))

section CaseI
variable {y1 y2 σ a b : ℝ}

lemma wI_nonneg (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) (e : Fin 5) : 0 ≤ wI y1 y2 σ a b e := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hp : 0 ≤ (b - (y1 + y2)) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ ((y1 + y2) - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hKa : 0 < K y1 y2 σ a := by unfold K; nlinarith
  have hKb : 0 < K y1 y2 σ b := by unfold K; nlinarith
  fin_cases e <;> simp only [wI, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact div_nonneg (mul_nonneg (mul_nonneg hp (by linarith)) (by linarith)) hKa.le
  · exact div_nonneg (mul_nonneg (mul_nonneg hp (by linarith)) (by linarith)) hKa.le
  · exact div_nonneg (mul_nonneg (mul_nonneg hq (by linarith)) (by linarith)) hKb.le
  · exact div_nonneg (mul_nonneg (mul_nonneg hq (by linarith)) (by linarith)) hKb.le
  · exact mul_nonneg hy1 (add_nonneg (div_nonneg (mul_nonneg hp (by linarith)) hKa.le)
      (div_nonneg (mul_nonneg hq (by linarith)) hKb.le))

lemma caseI_coord0 (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) :
    ∑ e, ENNReal.ofReal (wI y1 y2 σ a b e) •
      unifI (min (PI y1 y2 σ a b e 0) (QI y1 y2 σ e 0))
        (max (PI y1 y2 σ a b e 0) (QI y1 y2 σ e 0)) = ENNReal.ofReal 1 • unifI 0 (σ + y2) := by
  have hw := wI_nonneg h hI
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hy1p : 0 < y1 := by linarith
  have hy2p : 0 < y2 := by linarith
  have hKa : 0 < K y1 y2 σ a := by unfold K; nlinarith
  have hKb : 0 < K y1 y2 σ b := by unfold K; nlinarith
  have hba : 0 < b - a := by linarith
  have hKa' : a * σ + y1 * y2 ≠ 0 := hKa.ne'
  have hKb' : b * σ + y1 * y2 ≠ 0 := hKb.ne'
  rw [target_unif zero_le_one (by linarith), mix_unifI_eq (wI y1 y2 σ a b)
    ![wI y1 y2 σ a b 0 / y2, wI y1 y2 σ a b 1 / (σ + y2), wI y1 y2 σ a b 2 / y2,
      wI y1 y2 σ a b 3 / (σ + y2), wI y1 y2 σ a b 4 / σ] _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PI, QI, A, B, C, Matrix.cons_val]
      step_simp
      simp only [wI, K, Matrix.cons_val]
      rcases le_or_gt x 0 with h0 | h0
      · region_close
      rcases le_or_gt x y2 with h1 | h1
      · region_close
      rcases le_or_gt x (σ + y2) with h2 | h2
      · region_close
      · region_close
    · simp only [Fin.sum_univ_five, PI, QI, A, B, C, Matrix.cons_val]
      step_simp
      alg_close
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;> apply div_nonneg (hw _) (by linarith)
  · intro e; left
    fin_cases e <;> simp only [PI, QI, A, B, C, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;> step_simp <;> alg_close

lemma caseI_coord1 (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) :
    ∑ e, ENNReal.ofReal (wI y1 y2 σ a b e) •
      unifI (min (PI y1 y2 σ a b e 1) (QI y1 y2 σ e 1))
        (max (PI y1 y2 σ a b e 1) (QI y1 y2 σ e 1)) =
      ENNReal.ofReal 1 • unifI 0 (σ + y1) := by
  have hw := wI_nonneg h hI
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hy1p : 0 < y1 := by linarith
  have hKa : 0 < a * σ + y1 * y2 := by nlinarith
  have hKb : 0 < b * σ + y1 * y2 := by nlinarith
  have hp : 0 ≤ (b - (y1 + y2)) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ ((y1 + y2) - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  rw [target_unif (c := σ + y1) zero_le_one (by linarith), mix_unifI_eq (wI y1 y2 σ a b)
    ![(b - (y1 + y2)) / (b - a) * (a - y1) / K y1 y2 σ a, (b - (y1 + y2)) / (b - a) * (a - y1) / K
        y1 y2 σ a, ((y1 + y2) - a) / (b - a) * (b - y1) / K y1 y2 σ b, ((y1 + y2) - a) / (b -
            a) * (b - y1) / K y1 y2 σ b, wI y1 y2 σ a b 4 / (σ + y1)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PI, QI, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wI, K, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1 + y2 - b) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1 + y2 - a) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PI, QI, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wI, K, Matrix.cons_val, Fin.sum_univ_five]
      alg_close
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (mul_nonneg hp (by linarith)) (by unfold K; linarith)
    · exact div_nonneg (mul_nonneg hp (by linarith)) (by unfold K; linarith)
    · exact div_nonneg (mul_nonneg hq (by linarith)) (by unfold K; linarith)
    · exact div_nonneg (mul_nonneg hq (by linarith)) (by unfold K; linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PI, QI, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

lemma caseI_coord2 (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) :
    ∑ e, ENNReal.ofReal (wI y1 y2 σ a b e) •
      unifI (min (PI y1 y2 σ a b e 2) (QI y1 y2 σ e 2))
        (max (PI y1 y2 σ a b e 2) (QI y1 y2 σ e 2)) =
      ENNReal.ofReal 1 • gPiece ((y1 + y2) / 2) a b := by
  have hw := wI_nonneg h hI
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hy1p : 0 < y1 := by linarith
  have hKa : 0 < a * σ + y1 * y2 := by nlinarith
  have hKb : 0 < b * σ + y1 * y2 := by nlinarith
  have hp : 0 ≤ (b - (y1 + y2)) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ ((y1 + y2) - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  rw [target_g (μ := (y1 + y2) / 2) (a := a) (b := b) zero_le_one ha (by linarith) (by linarith),
      mix_unifI_eq (wI y1 y2 σ a b)
    ![wI y1 y2 σ a b 0 / a, (b - (y1 + y2)) / (b - a) * (σ + y1 + y2 - a) / K y1 y2 σ a, wI y1 y2
        σ a b 2 / b, ((y1 + y2) - a) / (b - a) * (σ + y1 + y2 -
            b) / K y1 y2 σ b, wI y1 y2 σ a b 4 / y1]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PI, QI, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wI, K, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y1) with hx | hx
      · region_close
      rcases le_or_gt x (a) with hx | hx
      · region_close
      rcases le_or_gt x (b) with hx | hx
      · region_close
      region_close
    · rcases ha.lt_or_eq with ha0 | ha0
      · simp only [ha0.ne', ↓reduceIte]
        simp only [Fin.sum_univ_five, PI, QI, A, A', B, C, D, D', E, Matrix.cons_val]
        try step_simp
        simp only [wI, K, Matrix.cons_val, Fin.sum_univ_five]
        alg_close
      · subst ha0
        simp only [↓reduceIte]
        first
        | (exfalso; linarith)
        | (simp only [Fin.sum_univ_five, PI, QI, A, A', B, C, D, D', E, Matrix.cons_val]
           try step_simp
           simp only [wI, K, Matrix.cons_val, Fin.sum_univ_five]
           alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (mul_nonneg hp (by linarith)) (by unfold K; linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (mul_nonneg hq (by linarith)) (by unfold K; linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PI, QI, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

end CaseI

/-- Proves `0 ≤ e` for products, quotients and sums of factors that `linarith` shows
nonnegative. -/
macro "nonneg_tac" : tactic => `(tactic|
  repeat' (first
    | with_unfolding_all linarith
    | apply div_nonneg
    | apply mul_nonneg
    | apply add_nonneg))

/-- Proves `0 < e` similarly. -/
macro "pos_tac" : tactic => `(tactic|
  repeat' (first
    | with_unfolding_all linarith
    | apply div_pos
    | apply mul_pos
    | apply add_pos_of_pos_of_nonneg))

lemma N4_eq (y1 y2 σ a b : ℝ) : N4 y1 y2 σ a b =
    (a + b - (y1 + y2)) * (b - y1) * (b - y2) +
      (σ + y1 + y2 - b) * (b - a) * (b + a - (y1 + y2)) := by
  unfold N4; ring

lemma N2_pos {y1 σ a b : ℝ} (hσ : 0 < σ) (h3 : a < y1) (hb : y1 < b) (ha : 0 ≤ a) :
    0 < N2 y1 σ a b := by
  unfold N2; nlinarith

lemma N4_pos {y1 y2 σ a b : ℝ} (ha : 0 ≤ a) (ha2 : a < y1 + y2) (hy1 : 0 ≤ y1) (hy12 : y1 ≤ y2)
    (hb : y1 + y2 < b) (hbs : b ≤ σ + y1 + y2) : 0 < N4 y1 y2 σ a b := by
  rw [N4_eq]
  have h1 : 0 < (a + b - (y1 + y2)) * (b - y1) * (b - y2) := by pos_tac
  have h2 : 0 ≤ (σ + y1 + y2 - b) * (b - a) * (b + a - (y1 + y2)) := by
    nonneg_tac
  linarith

section Cases
variable {y1 y2 σ a b : ℝ}

lemma wII_nonneg (h : Hyp y1 y2 σ a b) (hII : y1 ≤ a) (hII' : a < y2) (hy1p : 0 < y1)
    (e : Fin 5) : 0 ≤ wII y1 y2 σ a b e := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  fin_cases e <;> simp only [wII, K, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> nonneg_tac

lemma wII0_nonneg (h : Hyp y1 y2 σ a b) (_hII0 : y1 = 0) (e : Fin 3) :
    0 ≤ wII0 y1 y2 σ a b e := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  fin_cases e <;> simp only [wII0, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> nonneg_tac

lemma wIIIa_nonneg (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : σ + y1 ≤ b) (e : Fin 5) :
    0 ≤ wIIIa y1 y2 σ a b e := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hN4 := N4_pos ha ha2 hy1 hy12 hb hbs
  have hN2 := N2_pos (b := b) hσ h3 (by linarith) ha
  fin_cases e <;> simp only [wIIIa, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> nonneg_tac

lemma wIIIb_nonneg (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : b < σ + y1) (e : Fin 5) :
    0 ≤ wIIIb y1 y2 σ a b e := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hN2 := N2_pos (b := b) hσ h3 (by linarith) ha
  fin_cases e <;> simp only [wIIIb, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> nonneg_tac

set_option maxRecDepth 20000 in
lemma caseII_coord0 (h : Hyp y1 y2 σ a b) (hII : y1 ≤ a) (hII' : a < y2) (hy1p : 0 < y1) :
    ∑ e, ENNReal.ofReal (wII y1 y2 σ a b e) •
      unifI (min (PII y1 y2 σ a b e 0) (QII y1 y2 σ a e 0))
        (max (PII y1 y2 σ a b e 0) (QII y1 y2 σ a e 0)) =
      ENNReal.ofReal (∑ e, wII y1 y2 σ a b e) • unifI 0 (σ + y2) := by
  have hw := wII_nonneg h hII hII' hy1p
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hKb : 0 < b * σ + y1 * y2 := by nlinarith
  rw [target_unif (c := σ + y2) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wII y1 y2 σ a b)
    ![wII y1 y2 σ a b 0 / (σ + y2), wII y1 y2 σ a b 1 / y2, wII y1 y2 σ a b 2 / σ, wII y1 y2 σ a b
        3 / (y2 - a), wII y1 y2 σ a b 4 / (σ + a)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y2 - a) with hx | hx
      · region_close
      rcases le_or_gt x (y2) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y2) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PII, QII, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseII_coord1 (h : Hyp y1 y2 σ a b) (hII : y1 ≤ a) (hII' : a < y2) (hy1p : 0 < y1) :
    ∑ e, ENNReal.ofReal (wII y1 y2 σ a b e) •
      unifI (min (PII y1 y2 σ a b e 1) (QII y1 y2 σ a e 1))
        (max (PII y1 y2 σ a b e 1) (QII y1 y2 σ a e 1)) =
      ENNReal.ofReal (∑ e, wII y1 y2 σ a b e) • unifI 0 (σ + y1) := by
  have hw := wII_nonneg h hII hII' hy1p
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hKb : 0 < b * σ + y1 * y2 := by nlinarith
  rw [target_unif (c := σ + y1) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wII y1 y2 σ a b)
    ![(wII y1 y2 σ a b 1 + wII y1 y2 σ a b 3) / (b - y2), wII y1 y2 σ a b 1 / (b - y2), wII y1 y2
        σ a b 2 / (σ + y1), wII y1 y2 σ a b 3 / (b - y2), wII y1 y2 σ a b 4 / (σ + y1)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1 + y2 - b) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (add_nonneg (hw _) (hw _)) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PII, QII, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseII_coord2 (h : Hyp y1 y2 σ a b) (hII : y1 ≤ a) (hII' : a < y2) (hy1p : 0 < y1) :
    ∑ e, ENNReal.ofReal (wII y1 y2 σ a b e) •
      unifI (min (PII y1 y2 σ a b e 2) (QII y1 y2 σ a e 2))
        (max (PII y1 y2 σ a b e 2) (QII y1 y2 σ a e 2)) =
      ENNReal.ofReal (∑ e, wII y1 y2 σ a b e) • gPiece ((y1 + y2) / 2) a b := by
  have hw := wII_nonneg h hII hII' hy1p
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hKb : 0 < b * σ + y1 * y2 := by nlinarith
  rw [target_g (μ := (y1 + y2) / 2) (a := a) (b := b) (Finset.sum_nonneg fun e _ => hw e) ha (by
      linarith) (by linarith), mix_unifI_eq (wII y1 y2 σ a b)
    ![wII y1 y2 σ a b 0 / (b - y1), wII y1 y2 σ a b 1 / b, wII y1 y2 σ a b 2 / y1, wII y1 y2 σ a b
        3 / (b - a), (b - (y1 + y2)) * K y1 y2 σ b * (σ + a)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y1) with hx | hx
      · region_close
      rcases le_or_gt x (a) with hx | hx
      · region_close
      rcases le_or_gt x (b) with hx | hx
      · region_close
      region_close
    · rcases ha.lt_or_eq with ha0 | ha0
      · simp only [ha0.ne', ↓reduceIte]
        simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
        try step_simp
        simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
        alg_close
      · subst ha0
        simp only [↓reduceIte]
        first
        | (exfalso; linarith)
        | (simp only [Fin.sum_univ_five, PII, QII, A, A', B, C, D, D', E, Matrix.cons_val]
           try step_simp
           simp only [wII, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
           alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact mul_nonneg (mul_nonneg (by linarith) (by unfold K; linarith)) (by linarith)
  · intro e; fin_cases e <;> simp only [PII, QII, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseII0_coord0 (h : Hyp y1 y2 σ a b) (hII0 : y1 = 0) :
    ∑ e, ENNReal.ofReal (wII0 y1 y2 σ a b e) •
      unifI (min (PII0 y1 y2 σ a b e 0) (QII0 y1 y2 σ a e 0))
        (max (PII0 y1 y2 σ a b e 0) (QII0 y1 y2 σ a e 0)) =
      ENNReal.ofReal (∑ e, wII0 y1 y2 σ a b e) • unifI 0 (σ + y2) := by
  have hw := wII0_nonneg h hII0
  subst hII0
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  rw [target_unif (c := σ + y2) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wII0 0 y2 σ a b)
    ![wII0 0 y2 σ a b 0 / (σ + y2), wII0 0 y2 σ a b 1 / (y2 - a), wII0 0 y2 σ a b 2 / (σ + a)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y2 - a) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y2) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseII0_coord1 (h : Hyp y1 y2 σ a b) (hII0 : y1 = 0) :
    ∑ e, ENNReal.ofReal (wII0 y1 y2 σ a b e) •
      unifI (min (PII0 y1 y2 σ a b e 1) (QII0 y1 y2 σ a e 1))
        (max (PII0 y1 y2 σ a b e 1) (QII0 y1 y2 σ a e 1)) =
      ENNReal.ofReal (∑ e, wII0 y1 y2 σ a b e) • unifI 0 (σ + y1) := by
  have hw := wII0_nonneg h hII0
  subst hII0
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  rw [target_unif (c := σ + 0) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wII0 0 y2 σ a b)
    ![((0 + y2) - a) / (b - (0 + y2)), wII0 0 y2 σ a b 1 / (b - y2), wII0 0 y2 σ a b 2 / (σ + 0)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (σ + 0 + y2 - b) with hx | hx
      · region_close
      rcases le_or_gt x (σ + 0) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseII0_coord2 (h : Hyp y1 y2 σ a b) (hII0 : y1 = 0) :
    ∑ e, ENNReal.ofReal (wII0 y1 y2 σ a b e) •
      unifI (min (PII0 y1 y2 σ a b e 2) (QII0 y1 y2 σ a e 2))
        (max (PII0 y1 y2 σ a b e 2) (QII0 y1 y2 σ a e 2)) =
      ENNReal.ofReal (∑ e, wII0 y1 y2 σ a b e) • gPiece ((y1 + y2) / 2) a b := by
  have hw := wII0_nonneg h hII0
  subst hII0
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  rw [target_g (μ := (0 + y2) / 2) (a := a) (b := b) (Finset.sum_nonneg fun e _ => hw e) ha (by
      linarith) (by linarith), mix_unifI_eq (wII0 0 y2 σ a b)
    ![wII0 0 y2 σ a b 0 / b, wII0 0 y2 σ a b 1 / (b - a), wII0 0 y2 σ a b 2 / a]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (a) with hx | hx
      · region_close
      rcases le_or_gt x (b) with hx | hx
      · region_close
      region_close
    · rcases ha.lt_or_eq with ha0 | ha0
      · simp only [ha0.ne', ↓reduceIte]
        simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
        try step_simp
        simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]
        alg_close
      · subst ha0
        simp only [↓reduceIte]
        first
        | (exfalso; linarith)
        | (simp only [Fin.sum_univ_three, PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val]
           try step_simp
           simp only [wII0, K, N2, N4, Matrix.cons_val, Fin.sum_univ_three]
           alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PII0, QII0, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseIIIa_coord0 (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : σ + y1 ≤ b) :
    ∑ e, ENNReal.ofReal (wIIIa y1 y2 σ a b e) •
      unifI (min (PIIIa y1 y2 σ a b e 0) (QIIIa y1 y2 σ b e 0))
        (max (PIIIa y1 y2 σ a b e 0) (QIIIa y1 y2 σ b e 0)) =
      ENNReal.ofReal (∑ e, wIIIa y1 y2 σ a b e) • unifI 0 (σ + y2) := by
  have hw := wIIIa_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hN2 : 0 < N2 y1 σ a b := N2_pos (b := b) hσ h3 (by linarith) ha
  have hN4 : 0 < N4 y1 y2 σ a b := N4_pos ha ha2 hy1 hy12 hb hbs
  rw [target_unif (c := σ + y2) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wIIIa y1 y2 σ a b)
    ![wIIIa y1 y2 σ a b 0 / (b - y1), wIIIa y1 y2 σ a b 1 / σ, N4 y1 y2 σ a b, wIIIa y1 y2 σ a b 3
        / (σ + y2), (b - y2) * N2 y1 σ a b]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1 + y2 - b) with hx | hx
      · region_close
      rcases le_or_gt x (y2) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y2) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact hN4.le
    · exact div_nonneg (hw _) (by linarith)
    · exact mul_nonneg (by linarith) hN2.le
  · intro e; fin_cases e <;> simp only [PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseIIIa_coord1 (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : σ + y1 ≤ b) :
    ∑ e, ENNReal.ofReal (wIIIa y1 y2 σ a b e) •
      unifI (min (PIIIa y1 y2 σ a b e 1) (QIIIa y1 y2 σ b e 1))
        (max (PIIIa y1 y2 σ a b e 1) (QIIIa y1 y2 σ b e 1)) =
      ENNReal.ofReal (∑ e, wIIIa y1 y2 σ a b e) • unifI 0 (σ + y1) := by
  have hw := wIIIa_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hN2 : 0 < N2 y1 σ a b := N2_pos (b := b) hσ h3 (by linarith) ha
  have hN4 : 0 < N4 y1 y2 σ a b := N4_pos ha ha2 hy1 hy12 hb hbs
  rw [target_unif (c := σ + y1) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wIIIa y1 y2 σ a b)
    ![wIIIa y1 y2 σ a b 0 / (y1 - a), wIIIa y1 y2 σ a b 1 / (σ + a), wIIIa y1 y2 σ a b 2 / (σ +
        y1), wIIIa y1 y2 σ a b 3 / (σ + a), wIIIa y1 y2 σ a b 4 / (σ + y1)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y1 - a) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseIIIa_coord2 (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : σ + y1 ≤ b) :
    ∑ e, ENNReal.ofReal (wIIIa y1 y2 σ a b e) •
      unifI (min (PIIIa y1 y2 σ a b e 2) (QIIIa y1 y2 σ b e 2))
        (max (PIIIa y1 y2 σ a b e 2) (QIIIa y1 y2 σ b e 2)) =
      ENNReal.ofReal (∑ e, wIIIa y1 y2 σ a b e) • gPiece ((y1 + y2) / 2) a b := by
  have hw := wIIIa_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hN2 : 0 < N2 y1 σ a b := N2_pos (b := b) hσ h3 (by linarith) ha
  have hN4 : 0 < N4 y1 y2 σ a b := N4_pos ha ha2 hy1 hy12 hb hbs
  rw [target_g (μ := (y1 + y2) / 2) (a := a) (b := b) (Finset.sum_nonneg fun e _ => hw e) ha (by
      linarith) (by linarith), mix_unifI_eq (wIIIa y1 y2 σ a b)
    ![wIIIa y1 y2 σ a b 0 / (b - a), wIIIa y1 y2 σ a b 1 / a, wIIIa y1 y2 σ a b 2 / b, wIIIa y1 y2
        σ a b 3 / (y2 - a), wIIIa y1 y2 σ a b 4 / (b - y2)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (a) with hx | hx
      · region_close
      rcases le_or_gt x (y2) with hx | hx
      · region_close
      rcases le_or_gt x (b) with hx | hx
      · region_close
      region_close
    · rcases ha.lt_or_eq with ha0 | ha0
      · simp only [ha0.ne', ↓reduceIte]
        simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
        try step_simp
        simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
        alg_close
      · subst ha0
        simp only [↓reduceIte]
        first
        | (exfalso; linarith)
        | (simp only [Fin.sum_univ_five, PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val]
           try step_simp
           simp only [wIIIa, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
           alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PIIIa, QIIIa, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseIIIb_coord0 (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : b < σ + y1) :
    ∑ e, ENNReal.ofReal (wIIIb y1 y2 σ a b e) •
      unifI (min (PIIIb y1 y2 σ a e 0) (QIIIb y1 y2 σ a b e 0))
        (max (PIIIb y1 y2 σ a e 0) (QIIIb y1 y2 σ a b e 0)) =
      ENNReal.ofReal (∑ e, wIIIb y1 y2 σ a b e) • unifI 0 (σ + y2) := by
  have hw := wIIIb_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  rw [target_unif (c := σ + y2) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wIIIb y1 y2 σ a b)
    ![wIIIb y1 y2 σ a b 0 / σ, wIIIb y1 y2 σ a b 1 / y2, wIIIb y1 y2 σ a b 2 / (σ + y2), wIIIb y1
        y2 σ a b 3 / (σ + y1 - b), wIIIb y1 y2 σ a b 4 / (b - y1)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y2) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1 + y2 - b) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y2) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseIIIb_coord1 (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : b < σ + y1) :
    ∑ e, ENNReal.ofReal (wIIIb y1 y2 σ a b e) •
      unifI (min (PIIIb y1 y2 σ a e 1) (QIIIb y1 y2 σ a b e 1))
        (max (PIIIb y1 y2 σ a e 1) (QIIIb y1 y2 σ a b e 1)) =
      ENNReal.ofReal (∑ e, wIIIb y1 y2 σ a b e) • unifI 0 (σ + y1) := by
  have hw := wIIIb_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  rw [target_unif (c := σ + y1) (Finset.sum_nonneg fun e _ => hw e) (by linarith), mix_unifI_eq
      (wIIIb y1 y2 σ a b)
    ![wIIIb y1 y2 σ a b 0 / (σ + a), wIIIb y1 y2 σ a b 1 / (b - y2), wIIIb y1 y2 σ a b 2 / (σ + y2
        - b + a), wIIIb y1 y2 σ a b 3 / (σ + y1), wIIIb y1 y2 σ a b 4 / (y1 - a)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (y1 - a) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1 + y2 - b) with hx | hx
      · region_close
      rcases le_or_gt x (σ + y1) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

set_option maxRecDepth 20000 in
lemma caseIIIb_coord2 (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : b < σ + y1) :
    ∑ e, ENNReal.ofReal (wIIIb y1 y2 σ a b e) •
      unifI (min (PIIIb y1 y2 σ a e 2) (QIIIb y1 y2 σ a b e 2))
        (max (PIIIb y1 y2 σ a e 2) (QIIIb y1 y2 σ a b e 2)) =
      ENNReal.ofReal (∑ e, wIIIb y1 y2 σ a b e) • gPiece ((y1 + y2) / 2) a b := by
  have hw := wIIIb_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  rw [target_g (μ := (y1 + y2) / 2) (a := a) (b := b) (Finset.sum_nonneg fun e _ => hw e) ha (by
      linarith) (by linarith), mix_unifI_eq (wIIIb y1 y2 σ a b)
    ![wIIIb y1 y2 σ a b 0 / a, wIIIb y1 y2 σ a b 1 / b, wIIIb y1 y2 σ a b 2 / (b - a), wIIIb y1 y2
        σ a b 3 / b, wIIIb y1 y2 σ a b 4 / (b - a)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
      try step_simp
      simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (a) with hx | hx
      · region_close
      rcases le_or_gt x (b) with hx | hx
      · region_close
      region_close
    · rcases ha.lt_or_eq with ha0 | ha0
      · simp only [ha0.ne', ↓reduceIte]
        simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
        try step_simp
        simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
        alg_close
      · subst ha0
        simp only [↓reduceIte]
        first
        | (exfalso; linarith)
        | (simp only [Fin.sum_univ_five, PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val]
           try step_simp
           simp only [wIIIb, K, N2, N4, Matrix.cons_val, Fin.sum_univ_five]
           alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [PIIIb, QIIIb, A, A', B, C, D, D', E, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> disj_close

/-- In case (I) the weights add up to `1`. -/
lemma wI_sum (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) : ∑ e, wI y1 y2 σ a b e = 1 := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  have hy1p : 0 < y1 := by linarith
  have hKa : 0 < a * σ + y1 * y2 := by nlinarith
  have hKb : 0 < b * σ + y1 * y2 := by nlinarith
  simp only [Fin.sum_univ_five, wI, K, Matrix.cons_val]
  alg_close

lemma wI_sum_pos (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) : 0 < ∑ e, wI y1 y2 σ a b e := by
  rw [wI_sum h hI]; exact one_pos

lemma PI_mem (e : Fin 5) : ∑ j, PI y1 y2 σ a b e j = σ + y1 + y2 := by
  fin_cases e <;> simp [PI, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

lemma QI_mem (e : Fin 5) : ∑ j, QI y1 y2 σ e j = σ + y1 + y2 := by
  fin_cases e <;> simp [QI, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

/-- Proposition 24, case (I): the normalised mixture of the segments of the case is a joint mix
of `U[0,c₁]`, `U[0,c₂]` and `g^μ_{a,b}` with sum `s` (in the parameters `y₁, y₂, σ, a, b`). -/
theorem caseI_mix (h : Hyp y1 y2 σ a b) (hI : y2 ≤ a) :
    IsJointMix ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b]
      (segMix (fun e => wI y1 y2 σ a b e / ∑ e, wI y1 y2 σ a b e) (PI y1 y2 σ a b) (QI y1 y2 σ)) ∧
    ∀ᵐ x ∂segMix (fun e => wI y1 y2 σ a b e / ∑ e, wI y1 y2 σ a b e) (PI y1 y2 σ a b) (QI y1 y2 σ),
      ∑ j, x j = σ + y1 + y2 := by
  refine isJointMix_segMix _ _ _ _ _ _ (wI_nonneg h hI) rfl (wI_sum_pos h hI)
    PI_mem QI_mem ?_
  intro j; fin_cases j
  · rw [wI_sum h hI]; exact caseI_coord0 h hI
  · rw [wI_sum h hI]; exact caseI_coord1 h hI
  · rw [wI_sum h hI]; exact caseI_coord2 h hI

lemma wII_sum_pos (h : Hyp y1 y2 σ a b) (hII : y1 ≤ a) (hII' : a < y2) (hy1p : 0 <
    y1) : 0 < ∑ e, wII y1 y2 σ a b e := by
  have hw := wII_nonneg h hII hII' hy1p
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  refine Finset.sum_pos' (fun e _ => hw e) ⟨2, Finset.mem_univ _, ?_⟩
  simp only [wII, K, N2, Matrix.cons_val]
  apply mul_pos (mul_pos hσ hy1p)
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (mul_nonneg (by linarith)
    (by linarith))) (mul_pos (by linarith) (mul_pos (by linarith) (by linarith)))

lemma PII_mem (e : Fin 5) : ∑ j, PII y1 y2 σ a b e j = σ + y1 + y2 := by
  fin_cases e <;> simp [PII, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

lemma QII_mem (e : Fin 5) : ∑ j, QII y1 y2 σ a e j = σ + y1 + y2 := by
  fin_cases e <;> simp [QII, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

/-- Proposition 24, case (II): the normalised mixture of the segments of the case is a joint mix
of `U[0,c₁]`, `U[0,c₂]` and `g^μ_{a,b}` with sum `s` (in the parameters `y₁, y₂, σ, a, b`). -/
theorem caseII_mix (h : Hyp y1 y2 σ a b) (hII : y1 ≤ a) (hII' : a < y2) (hy1p : 0 < y1) :
    IsJointMix ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b]
      (segMix (fun e => wII y1 y2 σ a b e / ∑ e, wII y1 y2 σ a b e) (PII y1 y2 σ a b) (QII y1 y2 σ
          a)) ∧
    ∀ᵐ x ∂segMix (fun e => wII y1 y2 σ a b e / ∑ e, wII y1 y2 σ a b e) (PII y1 y2 σ a b) (QII y1
        y2 σ a),
      ∑ j, x j = σ + y1 + y2 := by
  refine isJointMix_segMix _ _ _ _ _ _ (wII_nonneg h hII hII' hy1p) rfl (wII_sum_pos h hII hII'
      hy1p)
    PII_mem QII_mem ?_
  intro j; fin_cases j
  · exact caseII_coord0 h hII hII' hy1p
  · exact caseII_coord1 h hII hII' hy1p
  · exact caseII_coord2 h hII hII' hy1p

lemma wII0_sum_pos (h : Hyp y1 y2 σ a b) (hII0 : y1 = 0) : 0 < ∑ e, wII0 y1 y2 σ a b e := by
  have hw := wII0_nonneg h hII0
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  refine Finset.sum_pos' (fun e _ => hw e) ⟨1, Finset.mem_univ _, ?_⟩
  simp only [wII0, K, N2, Matrix.cons_val]
  linarith

lemma PII0_mem (e : Fin 3) : ∑ j, PII0 y1 y2 σ a b e j = σ + y1 + y2 := by
  fin_cases e <;> simp [PII0, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

lemma QII0_mem (e : Fin 3) : ∑ j, QII0 y1 y2 σ a e j = σ + y1 + y2 := by
  fin_cases e <;> simp [QII0, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

/-- Proposition 24, case (II0): the normalised mixture of the segments of the case is a joint mix
of `U[0,c₁]`, `U[0,c₂]` and `g^μ_{a,b}` with sum `s` (in the parameters `y₁, y₂, σ, a, b`). -/
theorem caseII0_mix (h : Hyp y1 y2 σ a b) (hII0 : y1 = 0) :
    IsJointMix ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b]
      (segMix (fun e => wII0 y1 y2 σ a b e / ∑ e, wII0 y1 y2 σ a b e) (PII0 y1 y2 σ a b) (QII0 y1
          y2 σ a)) ∧
    ∀ᵐ x ∂segMix (fun e => wII0 y1 y2 σ a b e / ∑ e, wII0 y1 y2 σ a b e) (PII0 y1 y2 σ a b) (QII0
        y1 y2 σ a),
      ∑ j, x j = σ + y1 + y2 := by
  refine isJointMix_segMix _ _ _ _ _ _ (wII0_nonneg h hII0) rfl (wII0_sum_pos h hII0)
    PII0_mem QII0_mem ?_
  intro j; fin_cases j
  · exact caseII0_coord0 h hII0
  · exact caseII0_coord1 h hII0
  · exact caseII0_coord2 h hII0

lemma wIIIa_sum_pos (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : σ + y1 ≤
    b) : 0 < ∑ e, wIIIa y1 y2 σ a b e := by
  have hw := wIIIa_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  refine Finset.sum_pos' (fun e _ => hw e) ⟨1, Finset.mem_univ _, ?_⟩
  simp only [wIIIa, K, N2, Matrix.cons_val]
  exact mul_pos hσ (N4_pos ha ha2 hy1 hy12 hb hbs)

lemma PIIIa_mem (e : Fin 5) : ∑ j, PIIIa y1 y2 σ a b e j = σ + y1 + y2 := by
  fin_cases e <;> simp [PIIIa, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

lemma QIIIa_mem (e : Fin 5) : ∑ j, QIIIa y1 y2 σ b e j = σ + y1 + y2 := by
  fin_cases e <;> simp [QIIIa, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

/-- Proposition 24, case (IIIa): the normalised mixture of the segments of the case is a joint mix
of `U[0,c₁]`, `U[0,c₂]` and `g^μ_{a,b}` with sum `s` (in the parameters `y₁, y₂, σ, a, b`). -/
theorem caseIIIa_mix (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : σ + y1 ≤ b) :
    IsJointMix ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b]
      (segMix (fun e => wIIIa y1 y2 σ a b e / ∑ e, wIIIa y1 y2 σ a b e) (PIIIa y1 y2 σ a b) (QIIIa
          y1 y2 σ b)) ∧
    ∀ᵐ x ∂segMix (fun e => wIIIa y1 y2 σ a b e / ∑ e, wIIIa y1 y2 σ a b e) (PIIIa y1 y2 σ a
        b) (QIIIa y1 y2 σ b),
      ∑ j, x j = σ + y1 + y2 := by
  refine isJointMix_segMix _ _ _ _ _ _ (wIIIa_nonneg h h3 h3') rfl (wIIIa_sum_pos h h3 h3')
    PIIIa_mem QIIIa_mem ?_
  intro j; fin_cases j
  · exact caseIIIa_coord0 h h3 h3'
  · exact caseIIIa_coord1 h h3 h3'
  · exact caseIIIa_coord2 h h3 h3'

lemma wIIIb_sum_pos (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : b < σ +
    y1) : 0 < ∑ e, wIIIb y1 y2 σ a b e := by
  have hw := wIIIb_nonneg h h3 h3'
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  have hσ : 0 < σ := by linarith
  refine Finset.sum_pos' (fun e _ => hw e) ⟨1, Finset.mem_univ _, ?_⟩
  simp only [wIIIb, K, N2, Matrix.cons_val]
  exact mul_pos (mul_pos (by linarith) (by linarith)) (N2_pos (b := b) hσ h3 (by linarith) ha)

lemma PIIIb_mem (e : Fin 5) : ∑ j, PIIIb y1 y2 σ a e j = σ + y1 + y2 := by
  fin_cases e <;> simp [PIIIb, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

lemma QIIIb_mem (e : Fin 5) : ∑ j, QIIIb y1 y2 σ a b e j = σ + y1 + y2 := by
  fin_cases e <;> simp [QIIIb, A, A', B, C, D, D', E, Fin.sum_univ_three] <;> ring

/-- Proposition 24, case (IIIb): the normalised mixture of the segments of the case is a joint mix
of `U[0,c₁]`, `U[0,c₂]` and `g^μ_{a,b}` with sum `s` (in the parameters `y₁, y₂, σ, a, b`). -/
theorem caseIIIb_mix (h : Hyp y1 y2 σ a b) (h3 : a < y1) (h3' : b < σ + y1) :
    IsJointMix ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b]
      (segMix (fun e => wIIIb y1 y2 σ a b e / ∑ e, wIIIb y1 y2 σ a b e) (PIIIb y1 y2 σ a) (QIIIb
          y1 y2 σ a b)) ∧
    ∀ᵐ x ∂segMix (fun e => wIIIb y1 y2 σ a b e / ∑ e, wIIIb y1 y2 σ a b e) (PIIIb y1 y2 σ
        a) (QIIIb y1 y2 σ a b),
      ∑ j, x j = σ + y1 + y2 := by
  refine isJointMix_segMix _ _ _ _ _ _ (wIIIb_nonneg h h3 h3') rfl (wIIIb_sum_pos h h3 h3')
    PIIIb_mem QIIIb_mem ?_
  intro j; fin_cases j
  · exact caseIIIb_coord0 h h3 h3'
  · exact caseIIIb_coord1 h h3 h3'
  · exact caseIIIb_coord2 h h3 h3'

/-- The data of Proposition 24 in one of its cases: finitely many weighted segments with endpoints
in `H_s` whose unnormalised marginals are `Λ • F j`, `Λ = ∑ wₑ > 0`. -/
def SegData (s : ℝ) (F : Fin 3 → Measure ℝ) : Prop :=
  ∃ (k : ℕ) (w : Fin k → ℝ) (P Q : Fin k → Fin 3 → ℝ), (∀ e, 0 ≤ w e) ∧ 0 < ∑ e, w e ∧
    (∀ e, ∑ j, P e j = s) ∧ (∀ e, ∑ j, Q e j = s) ∧
    ∀ j, ∑ e, ENNReal.ofReal (w e) • unifI (min (P e j) (Q e j)) (max (P e j) (Q e j)) =
      ENNReal.ofReal (∑ e, w e) • F j

/-- The five cases of Proposition 24 cover all parameters, and exclude each other. -/
lemma cases_cover (h : Hyp y1 y2 σ a b) :
    (y2 ≤ a) ∨ (y1 ≤ a ∧ a < y2 ∧ 0 < y1) ∨ (y1 = 0) ∨ (a < y1 ∧ σ + y1 ≤ b) ∨
      (a < y1 ∧ b < σ + y1) := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  rcases le_or_gt y2 a with h1 | h1
  · exact Or.inl h1
  rcases hy1.lt_or_eq with h2 | h2
  · rcases le_or_gt y1 a with h3 | h3
    · exact Or.inr (Or.inl ⟨h3, h1, h2⟩)
    rcases le_or_gt (σ + y1) b with h4 | h4
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, h4⟩)))
  · exact Or.inr (Or.inr (Or.inl h2.symm))

/-- Exclusivity of the five cases (as in the paper, (II) and (III) require `y₁ > 0`). -/
lemma cases_exclusive (h : Hyp y1 y2 σ a b) :
    let cI := y2 ≤ a
    let cII := y1 ≤ a ∧ a < y2 ∧ 0 < y1
    let cII0 := y1 = 0
    let cIIIa := a < y1 ∧ σ + y1 ≤ b
    let cIIIb := a < y1 ∧ b < σ + y1
    ¬(cI ∧ cII) ∧ ¬(cI ∧ cII0) ∧ ¬(cI ∧ cIIIa) ∧ ¬(cI ∧ cIIIb) ∧ ¬(cII ∧ cII0) ∧
      ¬(cII ∧ cIIIa) ∧ ¬(cII ∧ cIIIb) ∧ ¬(cII0 ∧ cIIIa) ∧ ¬(cII0 ∧ cIIIb) ∧
      ¬(cIIIa ∧ cIIIb) := by
  obtain ⟨hy1, hy12, ha, ha2, hb, hbs⟩ := h
  intro cI cII cII0 cIIIa cIIIb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cI, cII, cII0, cIIIa, cIIIb]; intro hh; obtain ⟨h1, h2⟩ := hh) <;>
    (try obtain ⟨h1, h1', h1''⟩ := h1) <;> (try obtain ⟨h2, h2'⟩ := h2) <;>
    (try obtain ⟨h2, h2', h2''⟩ := h2) <;> linarith

lemma segData_of_hyp (h : Hyp y1 y2 σ a b) :
    SegData (σ + y1 + y2) ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b] := by
  rcases cases_cover h with hc | ⟨h1, h2, h3⟩ | hc | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨5, wI y1 y2 σ a b, PI y1 y2 σ a b, QI y1 y2 σ, wI_nonneg h hc, wI_sum_pos h hc,
      PI_mem, QI_mem, fun j => ?_⟩
    rw [wI_sum h hc]
    fin_cases j
    · exact caseI_coord0 h hc
    · exact caseI_coord1 h hc
    · exact caseI_coord2 h hc
  · refine ⟨5, wII y1 y2 σ a b, PII y1 y2 σ a b, QII y1 y2 σ a, wII_nonneg h h1 h2 h3,
      wII_sum_pos h h1 h2 h3, PII_mem, QII_mem, fun j => ?_⟩
    fin_cases j
    · exact caseII_coord0 h h1 h2 h3
    · exact caseII_coord1 h h1 h2 h3
    · exact caseII_coord2 h h1 h2 h3
  · refine ⟨3, wII0 y1 y2 σ a b, PII0 y1 y2 σ a b, QII0 y1 y2 σ a, wII0_nonneg h hc,
      wII0_sum_pos h hc, PII0_mem, QII0_mem, fun j => ?_⟩
    fin_cases j
    · exact caseII0_coord0 h hc
    · exact caseII0_coord1 h hc
    · exact caseII0_coord2 h hc
  · refine ⟨5, wIIIa y1 y2 σ a b, PIIIa y1 y2 σ a b, QIIIa y1 y2 σ b, wIIIa_nonneg h h1 h2,
      wIIIa_sum_pos h h1 h2, PIIIa_mem, QIIIa_mem, fun j => ?_⟩
    fin_cases j
    · exact caseIIIa_coord0 h h1 h2
    · exact caseIIIa_coord1 h h1 h2
    · exact caseIIIa_coord2 h h1 h2
  · refine ⟨5, wIIIb y1 y2 σ a b, PIIIb y1 y2 σ a, QIIIb y1 y2 σ a b, wIIIb_nonneg h h1 h2,
      wIIIb_sum_pos h h1 h2, PIIIb_mem, QIIIb_mem, fun j => ?_⟩
    fin_cases j
    · exact caseIIIb_coord0 h h1 h2
    · exact caseIIIb_coord1 h h1 h2
    · exact caseIIIb_coord2 h h1 h2

end Cases

end P24

/-- Swapping the first two coordinates of every endpoint. -/
lemma P24.SegData.swap {s : ℝ} {F : Fin 3 → Measure ℝ} (hD : P24.SegData s F) :
    P24.SegData s ![F 1, F 0, F 2] := by
  obtain ⟨k, w, P, Q, hw, hΛ, hP, hQ, hF⟩ := hD
  let τ : Fin 3 → Fin 3 := ![1, 0, 2]
  have hτ : ∀ x : Fin 3 → ℝ, ∑ j, x (τ j) = ∑ j, x j := by
    intro x; simp [τ, Fin.sum_univ_three]; ring
  refine ⟨k, w, fun e j => P e (τ j), fun e j => Q e (τ j), hw, hΛ, fun e => ?_, fun e => ?_,
    fun j => ?_⟩
  · rw [hτ (P e), hP e]
  · rw [hτ (Q e), hQ e]
  · rw [hF (τ j)]
    fin_cases j <;> rfl

/-- **Proposition 24** (`j:prop:three`). Let `0 ≤ a < 2μ < b` (the paper also assumes
`c₁, c₂ > 0`, which follows from the other hypotheses), put
`s = (c₁ + c₂)/2 + μ`, and assume `c₁ ≤ s`, `c₂ ≤ s` and `b ≤ s`. Then finitely many segments
with endpoints in `H_s` and nonnegative weights adding up to `1` give a joint mix of `U[0,c₁]`,
`U[0,c₂]` and `g^μ_{a,b}` with sum `s`. For `c₁ ≥ c₂` the segments and weights are those of the
case `(I)`, `(II)`, `(II₀)`, `(IIIa)` or `(IIIb)` of the table (theorems `P24.caseI_mix`, …,
with `y₁ = s - c₁`, `y₂ = s - c₂`, `σ = s - 2μ`); for `c₁ < c₂` the first two coordinates of
all points are exchanged. -/
theorem prop24 {c1 c2 μ a b : ℝ} (ha : 0 ≤ a) (ha2 : a < 2 * μ)
    (hb : 2 * μ < b) (hc1s : c1 ≤ (c1 + c2) / 2 + μ) (hc2s : c2 ≤ (c1 + c2) / 2 + μ)
    (hbs : b ≤ (c1 + c2) / 2 + μ) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (P Q : Fin k → Fin 3 → ℝ), (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1 ∧
      (∀ e, ∑ j, P e j = (c1 + c2) / 2 + μ) ∧ (∀ e, ∑ j, Q e j = (c1 + c2) / 2 + μ) ∧
      IsJointMix ![unifI 0 c1, unifI 0 c2, gPiece μ a b] (segMix w P Q) ∧
      ∀ᵐ x ∂segMix w P Q, ∑ j, x j = (c1 + c2) / 2 + μ := by
  set s := (c1 + c2) / 2 + μ with hs
  have hD : P24.SegData s ![unifI 0 c1, unifI 0 c2, gPiece μ a b] := by
    rcases le_total c2 c1 with h12 | h12
    · have hyp : P24.Hyp (s - c1) (s - c2) (s - 2 * μ) a b :=
        ⟨by linarith, by linarith, ha, by linarith, by linarith, by linarith⟩
      have := P24.segData_of_hyp hyp
      rwa [show s - 2 * μ + (s - c1) + (s - c2) = s by ring,
        show s - 2 * μ + (s - c2) = c1 by ring, show s - 2 * μ + (s - c1) = c2 by ring,
        show (s - c1 + (s - c2)) / 2 = μ by ring] at this
    · have hyp : P24.Hyp (s - c2) (s - c1) (s - 2 * μ) a b :=
        ⟨by linarith, by linarith, ha, by linarith, by linarith, by linarith⟩
      have := (P24.segData_of_hyp hyp).swap
      rw [show s - 2 * μ + (s - c2) + (s - c1) = s by ring,
        show s - 2 * μ + (s - c1) = c2 by ring, show s - 2 * μ + (s - c2) = c1 by ring,
        show (s - c2 + (s - c1)) / 2 = μ by ring] at this
      exact this
  obtain ⟨k, w, P, Q, hw, hΛ, hP, hQ, hF⟩ := hD
  obtain ⟨hmix, hsum⟩ := isJointMix_segMix w P Q s _ _ hw rfl hΛ hP hQ hF
  refine ⟨k, fun e => w e / ∑ e, w e, P, Q, fun e => div_nonneg (hw e) hΛ.le, ?_, hP, hQ,
    hmix, hsum⟩
  rw [← Finset.sum_div, div_self hΛ.ne']

/-! ### Lemma 17 (`j:lem:three`): three uniform distributions

Parameters `t_j = s - c_j ≥ 0`, so `c₁ = t₂ + t₃`, `c₂ = t₁ + t₃`, `c₃ = t₁ + t₂`,
`s = t₁ + t₂ + t₃`. -/

namespace L17

/-- Hypotheses of Lemma 17 in the parameters `t_j`: `t_j ≥ 0` and `c_j > 0`. -/
structure Hyp17 (t1 t2 t3 : ℝ) : Prop where
  h1 : 0 ≤ t1
  h2 : 0 ≤ t2
  h3 : 0 ≤ t3
  h12 : 0 < t1 + t2
  h23 : 0 < t2 + t3
  h13 : 0 < t1 + t3

/-- `A = (0, t₃, c₃)`. -/
def A17 (t1 t2 t3 : ℝ) : Fin 3 → ℝ := ![0, t3, t1 + t2]
/-- `B = (t₂, c₂, 0)`. -/
def B17 (t1 t2 t3 : ℝ) : Fin 3 → ℝ := ![t2, t1 + t3, 0]
/-- `C = (c₁, 0, t₁)`. -/
def C17 (t1 t2 t3 : ℝ) : Fin 3 → ℝ := ![t2 + t3, 0, t1]

/-- The weights `t₁t₂/K, t₂t₃/K, t₁t₃/K` of `[A,B], [A,C], [B,C]`. -/
def w17 (t1 t2 t3 : ℝ) : Fin 3 → ℝ :=
  let K := t1 * t2 + t2 * t3 + t1 * t3
  ![t1 * t2 / K, t2 * t3 / K, t1 * t3 / K]

/-- First endpoints: `A, A, B`. -/
def P17 (t1 t2 t3 : ℝ) : Fin 3 → Fin 3 → ℝ := ![A17 t1 t2 t3, A17 t1 t2 t3, B17 t1 t2 t3]
/-- Second endpoints: `B, C, C`. -/
def Q17 (t1 t2 t3 : ℝ) : Fin 3 → Fin 3 → ℝ := ![B17 t1 t2 t3, C17 t1 t2 t3, C17 t1 t2 t3]

variable {t1 t2 t3 : ℝ}

lemma K17_pos (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h3 : 0 ≤ t3) (h12 : 0 < t1 + t2) (h23 : 0 < t2 + t3)
    (h13 : 0 < t1 + t3) : 0 < t1 * t2 + t2 * t3 + t1 * t3 := by
  rcases h1.lt_or_eq with h1' | h1'
  · rcases h2.lt_or_eq with h2' | h2'
    · nlinarith [mul_pos h1' h2']
    · subst h2'; nlinarith
  · subst h1'; nlinarith

lemma w17_nonneg (h : Hyp17 t1 t2 t3) (e : Fin 3) : 0 ≤ w17 t1 t2 t3 e := by
  obtain ⟨h1, h2, h3, h12, h23, h13⟩ := h
  have hK := K17_pos h1 h2 h3 h12 h23 h13
  fin_cases e <;> simp only [w17, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> exact div_nonneg (mul_nonneg (by assumption) (by assumption)) hK.le

lemma w17_sum (h : Hyp17 t1 t2 t3) : ∑ e, w17 t1 t2 t3 e = 1 := by
  obtain ⟨h1, h2, h3, h12, h23, h13⟩ := h
  have hK := K17_pos h1 h2 h3 h12 h23 h13
  simp only [w17, Fin.sum_univ_three, Matrix.cons_val]
  rw [← add_div, ← add_div, div_self hK.ne']

lemma lem17_coord0 (h : Hyp17 t1 t2 t3) :
    ∑ e, ENNReal.ofReal (w17 t1 t2 t3 e) •
      unifI (min (P17 t1 t2 t3 e 0) (Q17 t1 t2 t3 e 0))
        (max (P17 t1 t2 t3 e 0) (Q17 t1 t2 t3 e 0)) =
      ENNReal.ofReal 1 • unifI 0 (t2 + t3) := by
  have hw := w17_nonneg h
  obtain ⟨h1, h2, h3, h12, h23, h13⟩ := h
  have hK : 0 < t1 * t2 + t2 * t3 + t1 * t3 := K17_pos h1 h2 h3 h12 h23 h13
  rw [target_unif (c := t2 + t3) zero_le_one (by linarith), mix_unifI_eq (w17 t1 t2 t3)
    ![t1 / (t1 * t2 + t2 * t3 + t1 * t3), w17 t1 t2 t3 1 / (t2 + t3), t1 / (t1 * t2 + t2 * t3 + t1
        * t3)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_three, P17, Q17, A17, B17, C17, Matrix.cons_val]
      try step_simp
      simp only [w17, Matrix.cons_val, Fin.sum_univ_three]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (t2) with hx | hx
      · region_close
      rcases le_or_gt x (t2 + t3) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_three, P17, Q17, A17, B17, C17, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [w17, Matrix.cons_val, Fin.sum_univ_three]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (by linarith) hK.le
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (by linarith) hK.le
  · intro e; fin_cases e <;> simp only [P17, Q17, A17, B17, C17, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> left <;> (try step_simp) <;>
      simp only [w17, Matrix.cons_val] <;> alg_close

lemma lem17_coord1 (h : Hyp17 t1 t2 t3) :
    ∑ e, ENNReal.ofReal (w17 t1 t2 t3 e) •
      unifI (min (P17 t1 t2 t3 e 1) (Q17 t1 t2 t3 e 1))
        (max (P17 t1 t2 t3 e 1) (Q17 t1 t2 t3 e 1)) =
      ENNReal.ofReal 1 • unifI 0 (t1 + t3) := by
  have hw := w17_nonneg h
  obtain ⟨h1, h2, h3, h12, h23, h13⟩ := h
  have hK : 0 < t1 * t2 + t2 * t3 + t1 * t3 := K17_pos h1 h2 h3 h12 h23 h13
  rw [target_unif (c := t1 + t3) zero_le_one (by linarith), mix_unifI_eq (w17 t1 t2 t3)
    ![t2 / (t1 * t2 + t2 * t3 + t1 * t3), t2 / (t1 * t2 + t2 * t3 + t1 * t3), w17 t1 t2 t3 2 / (t1
        + t3)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_three, P17, Q17, A17, B17, C17, Matrix.cons_val]
      try step_simp
      simp only [w17, Matrix.cons_val, Fin.sum_univ_three]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (t3) with hx | hx
      · region_close
      rcases le_or_gt x (t1 + t3) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_three, P17, Q17, A17, B17, C17, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [w17, Matrix.cons_val, Fin.sum_univ_three]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (by linarith) hK.le
    · exact div_nonneg (by linarith) hK.le
    · exact div_nonneg (hw _) (by linarith)
  · intro e; fin_cases e <;> simp only [P17, Q17, A17, B17, C17, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> left <;> (try step_simp) <;>
      simp only [w17, Matrix.cons_val] <;> alg_close

lemma lem17_coord2 (h : Hyp17 t1 t2 t3) :
    ∑ e, ENNReal.ofReal (w17 t1 t2 t3 e) •
      unifI (min (P17 t1 t2 t3 e 2) (Q17 t1 t2 t3 e 2))
        (max (P17 t1 t2 t3 e 2) (Q17 t1 t2 t3 e 2)) =
      ENNReal.ofReal 1 • unifI 0 (t1 + t2) := by
  have hw := w17_nonneg h
  obtain ⟨h1, h2, h3, h12, h23, h13⟩ := h
  have hK : 0 < t1 * t2 + t2 * t3 + t1 * t3 := K17_pos h1 h2 h3 h12 h23 h13
  rw [target_unif (c := t1 + t2) zero_le_one (by linarith), mix_unifI_eq (w17 t1 t2 t3)
    ![w17 t1 t2 t3 0 / (t1 + t2), t3 / (t1 * t2 + t2 * t3 + t1 * t3), t3 / (t1 * t2 + t2 * t3 + t1
        * t3)]
    _ _ hw ?_ (fun e => min_le_max) ?_]
  · apply stepRep_congr
    · intro x
      simp only [Fin.sum_univ_three, P17, Q17, A17, B17, C17, Matrix.cons_val]
      try step_simp
      simp only [w17, Matrix.cons_val, Fin.sum_univ_three]
      rcases le_or_gt x (0) with hx | hx
      · region_close
      rcases le_or_gt x (t1) with hx | hx
      · region_close
      rcases le_or_gt x (t1 + t2) with hx | hx
      · region_close
      region_close
    · simp only [Fin.sum_univ_three, P17, Q17, A17, B17, C17, Matrix.cons_val]
      try step_simp
      first
      | alg_close
      | (simp only [w17, Matrix.cons_val, Fin.sum_univ_three]; alg_close)
  · intro e; fin_cases e <;> simp only [Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact div_nonneg (hw _) (by linarith)
    · exact div_nonneg (by linarith) hK.le
    · exact div_nonneg (by linarith) hK.le
  · intro e; fin_cases e <;> simp only [P17, Q17, A17, B17, C17, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> left <;> (try step_simp) <;>
      simp only [w17, Matrix.cons_val] <;> alg_close

end L17

/-- **Lemma 17** (`j:lem:three`). Let `c₁, c₂, c₃ > 0` with `max c_j ≤ s = (c₁ + c₂ + c₃)/2`,
`t_j = s - c_j`, `A = (0, t₃, c₃)`, `B = (t₂, c₂, 0)`, `C = (c₁, 0, t₁)` and
`K = t₁t₂ + t₂t₃ + t₁t₃`. Then `K > 0`, and the segments `[A,B]`, `[A,C]`, `[B,C]` with
weights `t₁t₂/K`, `t₂t₃/K`, `t₁t₃/K` (which add up to `1`) give a joint mix of `U[0,c₁]`,
`U[0,c₂]`, `U[0,c₃]` with sum `s`. -/
theorem lem17 {c1 c2 c3 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3)
    (h1 : c1 ≤ (c1 + c2 + c3) / 2) (h2 : c2 ≤ (c1 + c2 + c3) / 2)
    (h3 : c3 ≤ (c1 + c2 + c3) / 2) :
    let s := (c1 + c2 + c3) / 2
    0 < (s - c1) * (s - c2) + (s - c2) * (s - c3) + (s - c1) * (s - c3) ∧
    ∑ e, L17.w17 (s - c1) (s - c2) (s - c3) e = 1 ∧
    IsJointMix ![unifI 0 c1, unifI 0 c2, unifI 0 c3]
      (segMix (L17.w17 (s - c1) (s - c2) (s - c3)) (L17.P17 (s - c1) (s - c2) (s - c3))
        (L17.Q17 (s - c1) (s - c2) (s - c3))) ∧
    ∀ᵐ x ∂segMix (L17.w17 (s - c1) (s - c2) (s - c3)) (L17.P17 (s - c1) (s - c2) (s - c3))
        (L17.Q17 (s - c1) (s - c2) (s - c3)), ∑ j, x j = s := by
  intro s
  have hs : s = (c1 + c2 + c3) / 2 := rfl
  have h : L17.Hyp17 (s - c1) (s - c2) (s - c3) :=
    ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hsum := L17.w17_sum h
  have hmem : ∀ (R : Fin 3 → Fin 3 → ℝ), (R = L17.P17 (s - c1) (s - c2) (s - c3) ∨
      R = L17.Q17 (s - c1) (s - c2) (s - c3)) → ∀ e, ∑ j, R e j = s := by
    rintro R (rfl | rfl) e <;> fin_cases e <;>
      simp [L17.P17, L17.Q17, L17.A17, L17.B17, L17.C17, Fin.sum_univ_three, s] <;> ring
  have hmix := isJointMix_segMix (L17.w17 (s - c1) (s - c2) (s - c3))
    (L17.P17 (s - c1) (s - c2) (s - c3)) (L17.Q17 (s - c1) (s - c2) (s - c3)) s 1
    ![unifI 0 c1, unifI 0 c2, unifI 0 c3] (L17.w17_nonneg h) hsum one_pos
    (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl)) (by
      intro j; fin_cases j
      · have := L17.lem17_coord0 h
        rwa [show s - c2 + (s - c3) = c1 by ring] at this
      · have := L17.lem17_coord1 h
        rwa [show s - c1 + (s - c3) = c2 by ring] at this
      · have := L17.lem17_coord2 h
        rwa [show s - c1 + (s - c2) = c3 by ring] at this)
  simp only [div_one] at hmix
  exact ⟨L17.K17_pos h.h1 h.h2 h.h3 h.h12 h.h23 h.h13, hsum, hmix⟩

/-! ### Lemma 18 (`j:lem:uni`): any number of uniform distributions -/

lemma map_mul_unifI {t l r : ℝ} (ht : 0 < t) (hlr : l ≤ r) :
    (unifI l r).map (fun x => t * x) = unifI (t * l) (t * r) := by
  rcases hlr.lt_or_eq with hlt | rfl
  · have h1 := map_affine_unifI l (r - l) (sub_pos.mpr hlt).ne'
    rw [min_eq_left (by linarith), max_eq_right (by linarith), add_sub_cancel] at h1
    have h2 := map_affine_unifI (t * l) (t * (r - l)) (mul_pos ht (sub_pos.mpr hlt)).ne'
    have hle : t * l ≤ t * l + t * (r - l) := by nlinarith
    rw [min_eq_left hle, max_eq_right hle, show t * l + t * (r - l) = t * r by ring] at h2
    rw [← h1, Measure.map_map (measurable_const_mul t) (by fun_prop), ← h2]
    congr 1; funext v; simp only [Function.comp]; ring
  · rw [unifI_self, unifI_self, Measure.map_dirac' (measurable_const_mul t)]

/-- Scaling a finite mixture of uniform distributions with weights adding up to `1`. -/
lemma mix_unifI_scale {m : ℕ} (w : Fin m → ℝ) (p q : Fin m → ℝ) {t C : ℝ} (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hw : ∀ e, 0 ≤ w e) (hw1 : ∑ e, w e = 1)
    (hF : ∑ e, ENNReal.ofReal (w e) • unifI (min (p e) (q e)) (max (p e) (q e)) = unifI 0 C) :
    ∑ e, ENNReal.ofReal (w e) • unifI (min (t * p e) (t * q e)) (max (t * p e) (t * q e)) =
      unifI 0 (t * C) := by
  rcases ht.lt_or_eq with ht | rfl
  · have hmn : ∀ e, min (t * p e) (t * q e) = t * min (p e) (q e) := fun e =>
      (mul_min_of_nonneg _ _ ht.le).symm
    have hmx : ∀ e, max (t * p e) (t * q e) = t * max (p e) (q e) := fun e =>
      (mul_max_of_nonneg _ _ ht.le).symm
    simp only [hmn, hmx, ← map_mul_unifI ht min_le_max]
    rw [← mul_zero t, ← map_mul_unifI ht hC, ← hF,
      Measure.map_finset_sum' (measurable_const_mul t).aemeasurable]
    congr 1; funext e
    rw [Measure.map_smul]
    exact (measurable_const_mul t).aemeasurable
  · simp only [zero_mul, min_self, max_self]
    rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun e _ => hw e), hw1]
    simp

namespace L18

/-- Prefix sums `S n = L 0 + ⋯ + L (n-1)`. -/
def S (L : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, L j

lemma S_succ (L : ℕ → ℝ) (n : ℕ) : S L (n + 1) = S L n + L n := Finset.sum_range_succ _ _

lemma S_mono {L : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) : Monotone (S L) :=
  monotone_nat_of_le_succ fun n => by rw [S_succ]; linarith [hL n]

lemma bound0 {L : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∑ j ∈ Finset.range n, (if S L (j + 1) ≤ s then L j else 0) ≤ min (S L n) s := by
  induction n with
  | zero => simp [S, hs]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hm := S_mono hL (Nat.le_succ n)
    split_ifs with h
    · rw [S_succ] at h ⊢
      exact le_min (by linarith [min_le_left (S L n) s]) (by linarith [min_le_left (S L n) s])
    · exact le_min (by linarith [min_le_left (S L n) s]) (by linarith [min_le_right (S L n) s])

lemma bound1 {L : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) {s : ℝ} (hLs : ∀ j, L j ≤ s) (hs : 0 ≤ s)
    (n : ℕ) :
    ∑ j ∈ Finset.range n, (if s < S L (j + 1) ∧ S L j < s then L j else 0) ≤ s ∧
      (S L n ≤ s → ∑ j ∈ Finset.range n, (if s < S L (j + 1) ∧ S L j < s then L j else 0) = 0)
    := by
  induction n with
  | zero => simp [hs]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hm := S_mono hL (Nat.le_succ n)
    split_ifs with h
    · rw [ih.2 h.2.le, zero_add]
      exact ⟨hLs n, fun h' => absurd h' (not_le.mpr h.1)⟩
    · rw [add_zero]
      exact ⟨ih.1, fun h' => ih.2 (le_trans hm h')⟩

lemma bound2 {L : ℕ → ℝ} (hL : ∀ j, 0 ≤ L j) {s : ℝ} (n : ℕ) :
    ∑ j ∈ Finset.range n, (if s < S L (j + 1) ∧ s ≤ S L j then L j else 0) ≤
      max 0 (S L n - s) := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hm := S_mono hL (Nat.le_succ n)
    split_ifs with h
    · rw [max_eq_right (by linarith [h.2] : 0 ≤ S L n - s)] at ih
      rw [S_succ]
      exact le_max_of_le_right (by linarith)
    · rw [add_zero]
      exact ih.trans (max_le_max le_rfl (by linarith))

/-- The grouping: consecutive lengths are cut at `s`; the straddling one forms its own group. -/
def grp (L : ℕ → ℝ) (s : ℝ) (j : ℕ) : Fin 3 :=
  if S L (j + 1) ≤ s then 0 else if s ≤ S L j then 2 else 1

/-- Extension of a finite tuple by zeros. -/
def ext {k : ℕ} (ℓ : Fin k → ℝ) (j : ℕ) : ℝ := if h : j < k then ℓ ⟨j, h⟩ else 0

lemma group_sum_le {k : ℕ} (ℓ : Fin k → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) {s : ℝ}
    (hsum : ∑ j, ℓ j = 2 * s) (hs : 0 ≤ s) (hmax : ∀ j, ℓ j ≤ s) (i : Fin 3) :
    ∑ j, (if grp (ext ℓ) s j.val = i then ℓ j else 0) ≤ s := by
  have hL : ∀ j, 0 ≤ (ext ℓ) j := fun j => by
    simp only [ext]; split_ifs <;> simp [hℓ]
  have hLs : ∀ j, (ext ℓ) j ≤ s := fun j => by
    simp only [ext]; split_ifs <;> simp [hmax, hs]
  have hrange : ∀ f : ℕ → ℝ, ∑ j : Fin k, (if grp (ext ℓ) s j.val = i then ℓ j else 0) =
      ∑ j ∈ Finset.range k, (if grp (ext ℓ) s j = i then (ext ℓ) j else 0) := by
    intro f
    rw [Finset.sum_range (fun j => if grp (ext ℓ) s j = i then (ext ℓ) j else 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [ext, j.isLt]
  have hSk : S (ext ℓ) k = 2 * s := by
    rw [S, ← hsum, Finset.sum_range (fun j => (ext ℓ) j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [ext, j.isLt]
  rw [hrange (ext ℓ)]
  fin_cases i
  · calc _ = ∑ j ∈ Finset.range k, (if S (ext ℓ) (j + 1) ≤ s then (ext ℓ) j else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [grp]; split_ifs <;> first | rfl | (exfalso; linarith) | simp_all
      _ ≤ min (S (ext ℓ) k) s := bound0 hL hs k
      _ ≤ s := min_le_right _ _
  · calc _ = ∑ j ∈ Finset.range k,
          (if s < S (ext ℓ) (j + 1) ∧ S (ext ℓ) j < s then (ext ℓ) j else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          unfold grp
          by_cases h1 : S (ext ℓ) (j + 1) ≤ s
          · have : ¬(s < S (ext ℓ) (j + 1) ∧ S (ext ℓ) j < s) := fun h =>
              absurd h1 (not_le.mpr h.1)
            simp [h1, this]
          · by_cases h2 : s ≤ S (ext ℓ) j
            · have : ¬(s < S (ext ℓ) (j + 1) ∧ S (ext ℓ) j < s) := fun h =>
                absurd h2 (not_le.mpr h.2)
              simp [h1, h2, this]
            · have : s < S (ext ℓ) (j + 1) ∧ S (ext ℓ) j < s := ⟨not_le.mp h1, not_le.mp h2⟩
              simp [h1, h2, this]
      _ ≤ s := (bound1 hL hLs hs k).1
  · calc _ = ∑ j ∈ Finset.range k,
          (if s < S (ext ℓ) (j + 1) ∧ s ≤ S (ext ℓ) j then (ext ℓ) j else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [grp]; split_ifs <;> first | rfl | (exfalso; linarith) | simp_all
      _ ≤ max 0 (S (ext ℓ) k - s) := bound2 hL k
      _ ≤ s := max_le hs (by rw [hSk]; linarith)

end L18

namespace L18

/-- A joint mix of `U[0,C₀], U[0,C₁], U[0,C₂]` with sum `s` by at most three weighted segments
with endpoints in `H_s`, whose endpoints vanish on the coordinates with `Cᵢ = 0`. -/
def GroupData (s : ℝ) (C : Fin 3 → ℝ) : Prop :=
  ∃ (m : ℕ) (w : Fin m → ℝ) (P Q : Fin m → Fin 3 → ℝ), m ≤ 3 ∧ (∀ e, 0 ≤ w e) ∧
    ∑ e, w e = 1 ∧ (∀ e, ∑ i, P e i = s) ∧ (∀ e, ∑ i, Q e i = s) ∧
    (∀ e i, C i = 0 → P e i = 0 ∧ Q e i = 0) ∧
    ∀ i, ∑ e, ENNReal.ofReal (w e) • unifI (min (P e i) (Q e i)) (max (P e i) (Q e i)) =
      unifI 0 (C i)

lemma groupData_pos {s : ℝ} {C : Fin 3 → ℝ} (hC : ∀ i, 0 < C i) (hCs : ∀ i, C i ≤ s)
    (hsum : C 0 + C 1 + C 2 = 2 * s) : GroupData s C := by
  have hs : s = (C 0 + C 1 + C 2) / 2 := by linarith
  obtain ⟨-, hw1, hmix, -⟩ := lem17 (hC 0) (hC 1) (hC 2) (by linarith [hCs 0])
    (by linarith [hCs 1]) (by linarith [hCs 2])
  rw [← hs] at hw1 hmix
  have h : L17.Hyp17 (s - C 0) (s - C 1) (s - C 2) :=
    ⟨by linarith [hCs 0], by linarith [hCs 1], by linarith [hCs 2], by linarith [hC 2],
      by linarith [hC 0], by linarith [hC 1]⟩
  refine ⟨3, _, L17.P17 (s - C 0) (s - C 1) (s - C 2), L17.Q17 (s - C 0) (s - C 1) (s - C 2),
    le_rfl, L17.w17_nonneg h, hw1, fun e => ?_, fun e => ?_,
    fun e i hi => absurd hi (hC i).ne', fun i => ?_⟩
  · fin_cases e <;> simp [L17.P17, L17.A17, L17.B17, Fin.sum_univ_three] <;> linarith
  · fin_cases e <;> simp [L17.Q17, L17.B17, L17.C17, Fin.sum_univ_three] <;> linarith
  · rw [← segMix_map, hmix.2.2 i]
    fin_cases i <;> rfl

lemma groupData_zero {s : ℝ} (hs0 : 0 ≤ s) {C : Fin 3 → ℝ} (i0 : Fin 3) (h0 : C i0 = 0)
    (hs : ∀ i, i ≠ i0 → C i = s) : GroupData s C := by
  refine ⟨1, fun _ => 1, fun _ => if i0 = 0 then ![0, s, 0] else ![s, 0, 0],
    fun _ => if i0 = 2 then ![0, s, 0] else ![0, 0, s], le_refl _ |>.trans (by norm_num),
    fun _ => zero_le_one, by simp, fun e => ?_, fun e => ?_, fun e i hi => ?_, fun i => ?_⟩
  · split_ifs <;> simp [Fin.sum_univ_three]
  · split_ifs <;> simp [Fin.sum_univ_three]
  · fin_cases i0 <;> fin_cases i <;> simp_all
  · simp only [Finset.univ_unique, Finset.sum_singleton, ENNReal.ofReal_one, one_smul]
    fin_cases i0 <;> fin_cases i <;>
      simp_all [unifI_self, min_eq_left, min_eq_right, max_eq_left, max_eq_right]

lemma groupData_exists {s : ℝ} (hs : 0 < s) {C : Fin 3 → ℝ} (hC0 : ∀ i, 0 ≤ C i)
    (hCs : ∀ i, C i ≤ s) (hsum : C 0 + C 1 + C 2 = 2 * s) : GroupData s C := by
  by_cases hpos : ∀ i, 0 < C i
  · exact groupData_pos hpos hCs hsum
  push Not at hpos
  obtain ⟨i0, hi0⟩ := hpos
  have h0 : C i0 = 0 := le_antisymm hi0 (hC0 i0)
  refine groupData_zero hs.le i0 h0 (fun i hi => ?_)
  have := hCs 0; have := hCs 1; have := hCs 2
  fin_cases i0 <;> fin_cases i <;> simp_all <;> linarith [hCs 0, hCs 1, hCs 2]

end L18

/-- **Lemma 18** (`j:lem:uni`). Let `ℓ₁, …, ℓ_k ≥ 0` with `s = (ℓ₁ + ⋯ + ℓ_k)/2 > 0` and
`max ℓ_j ≤ s`. Then there is a joint mix of `U[0,ℓ₁], …, U[0,ℓ_k]` with sum `s` that is a mixture
of at most three uniform distributions on segments with endpoints in `H_s`.

(The paper obtains it by repeatedly merging two shortest lengths and applying Lemma 17; here the
coordinates are grouped into at most three groups of total length `≤ s` by cutting the
consecutive lengths at `s`, each group is a linear image of one coordinate of Lemma 17 or of a
single segment, as in the paper's merging step.) -/
theorem lem18 {k : ℕ} (ℓ : Fin k → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) (hs : 0 < (∑ j, ℓ j) / 2)
    (hmax : ∀ j, ℓ j ≤ (∑ j, ℓ j) / 2) :
    ∃ (m : ℕ) (w : Fin m → ℝ) (P Q : Fin m → Fin k → ℝ), m ≤ 3 ∧ (∀ e, 0 ≤ w e) ∧
      ∑ e, w e = 1 ∧ (∀ e, ∑ j, P e j = (∑ j, ℓ j) / 2) ∧
      (∀ e, ∑ j, Q e j = (∑ j, ℓ j) / 2) ∧
      IsJointMix (fun j => unifI 0 (ℓ j)) (segMix w P Q) ∧
      ∀ᵐ x ∂segMix w P Q, ∑ j, x j = (∑ j, ℓ j) / 2 := by
  classical
  set s := (∑ j, ℓ j) / 2 with hsdef
  have hsum : ∑ j, ℓ j = 2 * s := by rw [hsdef]; ring
  let g : Fin k → Fin 3 := fun j => L18.grp (L18.ext ℓ) s j.val
  let C : Fin 3 → ℝ := fun i => ∑ j, if g j = i then ℓ j else 0
  have hC0 : ∀ i, 0 ≤ C i := fun i =>
    Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hℓ]
  have hCs : ∀ i, C i ≤ s := fun i => L18.group_sum_le ℓ hℓ hsum hs.le hmax i
  have hCsum : C 0 + C 1 + C 2 = 2 * s := by
    rw [← hsum, ← Fin.sum_univ_three (f := C)]
    simp only [C]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  have hlC : ∀ j, ℓ j ≤ C (g j) := fun j => by
    have := Finset.single_le_sum (f := fun j' => if g j' = g j then ℓ j' else 0)
      (fun j' _ => by split_ifs <;> simp [hℓ]) (Finset.mem_univ j)
    simpa using this
  obtain ⟨m, w, P, Q, hm, hw, hw1, hP, hQ, hZ, hF⟩ := L18.groupData_exists hs hC0 hCs hCsum
  let lift : (Fin m → Fin 3 → ℝ) → Fin m → Fin k → ℝ :=
    fun R e j => ℓ j / C (g j) * R e (g j)
  have hlift : ∀ R : Fin m → Fin 3 → ℝ, (∀ e, ∑ i, R e i = s) →
      (∀ e i, C i = 0 → R e i = 0) → ∀ e, ∑ j, lift R e j = s := by
    intro R hR hRZ e
    rw [← hR e]
    simp only [lift]
    rw [← Finset.sum_fiberwise Finset.univ g]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : ∀ j ∈ Finset.univ.filter (fun j => g j = i),
        ℓ j / C (g j) * R e (g j) = ℓ j * (R e i / C i) := by
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]; ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    have hCi : ∑ j ∈ Finset.univ.filter (fun j => g j = i), ℓ j = C i := by
      simp only [C]; rw [Finset.sum_filter]
    rw [hCi]
    by_cases h : C i = 0
    · rw [h, hRZ e i h]; simp
    · field_simp
  have hFj : ∀ j, ∑ e, ENNReal.ofReal (w e) •
      unifI (min (lift P e j) (lift Q e j)) (max (lift P e j) (lift Q e j)) =
        ENNReal.ofReal 1 • unifI 0 (ℓ j) := by
    intro j
    rw [ENNReal.ofReal_one, one_smul]
    have := mix_unifI_scale w (fun e => P e (g j)) (fun e => Q e (g j))
      (t := ℓ j / C (g j)) (div_nonneg (hℓ j) (hC0 _)) (hC0 _) hw hw1 (hF (g j))
    convert this using 2
    by_cases h : C (g j) = 0
    · have : ℓ j = 0 := le_antisymm (h ▸ hlC j) (hℓ j)
      rw [h, this]; simp
    · field_simp
  obtain ⟨hmix, hae⟩ := isJointMix_segMix w (lift P) (lift Q) s 1 (fun j => unifI 0 (ℓ j)) hw hw1
    one_pos (hlift P hP fun e i hi => (hZ e i hi).1) (hlift Q hQ fun e i hi => (hZ e i hi).2) hFj
  simp only [div_one] at hmix hae
  exact ⟨m, w, lift P, lift Q, hm, hw, hw1, hlift P hP (fun e i hi => (hZ e i hi).1),
    hlift Q hQ (fun e i hi => (hZ e i hi).2), hmix, hae⟩

/-- The merging step of Lemma 18: among at least four nonnegative lengths, two shortest add up to
at most half the sum of four shortest, hence to at most `s`, the half of the total. -/
lemma two_shortest_le {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : b ≤ d) :
    a + b ≤ (a + b + c + d) / 2 := by linarith

/-- In Lemma 18, if exactly two lengths are positive, both equal `s`. -/
lemma two_positive_eq {a b s : ℝ} (hsum : a + b = 2 * s) (ha : a ≤ s) (hb : b ≤ s) :
    a = s ∧ b = s := ⟨by linarith, by linarith⟩

end Mixes
