import Mixes.Defs
import Mixes.Cone
import Mixes.NormAtom

/-!
# The norm condition and unimodal densities (Theorem `nc:thm:unimodal`, Corollary `nc:cor:alln`,
# Remark `nc:rem:classes`)

Setting. `q = 1 - p`, `c = 1/2 - β`, `μ = pc + q/2`. `W` has a law `ν` that is symmetric
(`ν.map Neg.neg = ν`) and carried by `[-1,1]`; for the densities, `ν = wLaw w` with `w` as in the
theorem (`IsBump w`: measurable, nonnegative, zero for `|x| > 1`, total mass `1`, even,
non-increasing on `[0,1]`).
* `F0 p c = p δ_c + q U[0,1]`, `F1 p c η ν = p (c + ηW) + q U[0,1]`, `F2 p c η ν` the law of
  `X₀ + ηW` (`X₀ ∼ F0` independent of `W`), as the image of `F0 ⊗ ν`.
* `f1 = q 1_{[0,1]} + p w_η(· - c)`, `uη = 1_{[0,1]} * w_η` (Mathlib convolution),
  `f2 = p w_η(· - c) + q uη`, with `w_η(x) = w(x/η)/η`.

## Convex order
* `CxLe F G`: equal means and `E(X-t)_+ ≤ E(Y-t)_+` for all `t` (stop-loss form of the convex
  order); `CxCondSL n F`: relation (nc:eq:cx) in this form.
* `cxCond_of_SL`: to `NormAtom.CxCond` (all convex functions) under the classical
  `NormAtom.H_stoploss_cx`; `normIneqs_of_SL`: to the norm inequalities `NormAtom.NormIneqs`
  under that hypothesis and the cited `NormAtom.H_shmalo26b` (both defined by agent NC1).
* `stopLoss_scale`: `E(y + aW - t)_+ ≤ E(y + bW - t)_+` for symmetric `W`, `0 ≤ a ≤ b`.
* `stopLoss_mix`: the proof of Proposition `nc:prop:atom`(b) for `p A + q U[0,1]`.
* `cxCond_F1`, `cxCond_F2`: relation (nc:eq:cx) for `f₁` and `f₂` under `CxParams` (only
  `n ≥ 2`, `0 < p < 1`, `0 < β < 1/2`, `0 < η < c/2`, `nμ ≥ √(n-1)`).

## Theorem `nc:thm:unimodal` (`Params n p β η`: the assumptions of the theorem)
* `thm_unimodal`: densities (`F1_eq_withDensity`, `F2_eq_withDensity`), unimodality with mode
  `c`, no symmetry about any point, mean `μ`, relation (nc:eq:cx), not `n`-completely mixable,
  `f₁` bounded / `≥ q` on `[0,1]` / zero outside, `f₂` is `C^k` when `w` is.
* `cx_F1_F2`, `thm_unimodal_norm`: the convex order by all convex functions and (nc:eq:norm).
* `miss_bound_F1`, `miss_bound_F2`: `P(∑ Xᵢ ≠ nμ) ≥ (n/2)(p - 2(n-1)ηq) - (n-2)/2` for every
  coupling, from `NormAtom.peak`; non-mixability from `NormAtom.peak_interval` (Lemma
  `nc:lem:peak`, proved by NC1, used without hypothesis).
* `example_params`, `example_values`: the example `n = 3`, `p = 2/5`, `c = 9/20`, `η = 1/50`.

## Corollary `nc:cor:alln` (`CorParams n₀ p β η`)
* `cor_alln`: (nc:eq:cx) for every `n ≥ 3`; not `n`-completely mixable for `1 ≤ n ≤ n₀`
  (`n = 1, 2` by the lack of symmetry, `symm_of_completelyMixable_le_two`).
* `cor_alln_norm`: (nc:eq:norm) for every `n ≥ 3` (under NC1's two hypotheses).
* `cor_alln_mixable`: `f₁` is `n`-completely mixable for `n ≥ 3/q`, under `H_as_cor_three_b`
  (the statement of `AsymThree.cor_three_b` of agent AS4).
* `exists_corParams`, `exists_params`: admissible parameters exist for every `n₀ ≥ 3`, so the least
  `n` can be arbitrarily large.

## Remark `nc:rem:classes`
* `meanCond_of_cx`: (nc:eq:cx) implies the mean condition (eq:meancond) for a law on `[a,b]`
  whose support has the ends `a`, `b` (no hypothesis).
* `rem_classes`: for every `n ≥ 3` a unimodal non-symmetric density bounded away from zero on its
  support (`f₁`, `w = bumpUnif`) and a `C^∞` one (`f₂`, `exists_smooth_bump`), both with
  (nc:eq:cx) and not `n`-completely mixable.
* `threshold_unimodal`: the explicit threshold for unimodal densities, under
  `H_as_cor_three_a` (the statement of `AsymThree.cor_three_a`).

Differences from the paper: the convex order is used in its stop-loss form, the version with all
convex functions needs NC1's `H_stoploss_cx`; the norm inequalities enter through NC1's
`H_shmalo26b`; Corollary `as:cor:three` enters as a hypothesis; "not symmetric" is proved for the
distributions (no reflection `x ↦ a - x` preserves them); "not `n`-completely mixable for
`n ≤ n₀`" is stated for `1 ≤ n ≤ n₀` (every law is `0`-completely mixable in the formal sense);
`meanCond_of_cx` derives the mean condition from (nc:eq:cx), not from (nc:eq:norm).
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Mixes.NormUnimodal

/-! ## Convex order, the relation (nc:eq:cx) and the norm inequalities -/

/-- The mean `∫ x dF`. -/
def mean (F : Measure ℝ) : ℝ := ∫ x, x ∂F

/-- The stop-loss transform `t ↦ E (X - t)_+` of a law, as a lower Lebesgue integral. -/
def stopLoss (F : Measure ℝ) (t : ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (x - t) ∂F

/-- Convex order `F ≤_cx G` of integrable laws, in its standard characterisation: equal means and
ordered stop-loss transforms (Shaked and Shanthikumar, *Stochastic Orders*, Theorem 3.A.1). -/
def CxLe (F G : Measure ℝ) : Prop :=
  Integrable id F ∧ Integrable id G ∧ mean F = mean G ∧ ∀ t, stopLoss F t ≤ stopLoss G t

/-- Relation (nc:eq:cx), `X - μ ≤_cx -(n-1)(X - μ)` for `X ∼ F` with mean `μ`, with the convex
order in its stop-loss form `CxLe`. (`NormAtom.CxCondSL` is the same relation with the convex order
defined by all convex functions; `cxCond_of_SL` passes from this one to that one.) -/
def CxCondSL (n : ℕ) (F : Measure ℝ) : Prop :=
  CxLe (F.map fun x => x - mean F) (F.map fun x => -((n : ℝ) - 1) * (x - mean F))

/-! ## Elementary facts on stop-loss transforms -/

lemma ofReal_max_zero (u : ℝ) : ENNReal.ofReal (max u 0) = ENNReal.ofReal u := by
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- Integration against a symmetric law is invariant under `w ↦ -w`. -/
lemma lintegral_neg_of_symm {ν : Measure ℝ} (hν : ν.map Neg.neg = ν) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ w, g (-w) ∂ν = ∫⁻ w, g w ∂ν := by
  conv_rhs => rw [← hν]
  rw [lintegral_map hg measurable_neg]

/-- Scaling in convex order: for a symmetric probability law `ν` and `0 ≤ a ≤ b`,
`E (y + aW - t)_+ ≤ E (y + bW - t)_+`. -/
lemma stopLoss_scale {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    (y t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ w, ENNReal.ofReal (y + a * w - t) ∂ν ≤ ∫⁻ w, ENNReal.ofReal (y + b * w - t) ∂ν := by
  rcases eq_or_lt_of_le (ha.trans hab) with hb | hb
  · have : a = 0 := le_antisymm (hb ▸ hab) ha
    subst this; rw [← hb]
  set S := ∫⁻ w, ENNReal.ofReal (y + b * w - t) ∂ν with hS
  have hm : Measurable fun w : ℝ => ENNReal.ofReal (y + b * w - t) := by fun_prop
  have hS' : ∫⁻ w, ENNReal.ofReal (y - b * w - t) ∂ν = S := by
    rw [hS, ← lintegral_neg_of_symm hν hm]; congr 1; ext w; ring_nf
  -- `(y - t)_+ ≤ S`
  have h0 : ENNReal.ofReal (y - t) ≤ S := by
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (y - t) ≤ 2 * S := by
      calc (2 : ℝ≥0∞) * ENNReal.ofReal (y - t)
          = ∫⁻ _w, 2 * ENNReal.ofReal (y - t) ∂ν := by simp
        _ ≤ ∫⁻ w, (ENNReal.ofReal (y + b * w - t) + ENNReal.ofReal (y - b * w - t)) ∂ν := by
          refine lintegral_mono fun w => ?_
          rw [two_mul, ← ofReal_max_zero (y + b * w - t), ← ofReal_max_zero (y - b * w - t),
            ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
            ← ofReal_max_zero (y - t), ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
          apply ENNReal.ofReal_le_ofReal
          have := le_max_left (y + b * w - t) 0
          have := le_max_left (y - b * w - t) 0
          rcases le_total (y - t) 0 with h | h
          · rw [max_eq_right h]; linarith [le_max_right (y + b * w - t) 0, le_max_right (y - b * w - t) 0]
          · rw [max_eq_left h]; linarith
        _ = 2 * S := by rw [lintegral_add_left hm, hS', two_mul]
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h2
  set l := a / b with hl
  have hl0 : 0 ≤ l := div_nonneg ha hb.le
  have hl1 : l ≤ 1 := (div_le_one hb).2 hab
  have hlb : l * b = a := by rw [hl]; field_simp
  calc ∫⁻ w, ENNReal.ofReal (y + a * w - t) ∂ν
      ≤ ∫⁻ w, (ENNReal.ofReal l * ENNReal.ofReal (y + b * w - t) +
          ENNReal.ofReal (1 - l) * ENNReal.ofReal (y - t)) ∂ν := by
        refine lintegral_mono fun w => ?_
        rw [← ofReal_max_zero (y + b * w - t), ← ofReal_max_zero (y - t),
          ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) (le_max_right _ _))]
        apply ENNReal.ofReal_le_ofReal
        have h1 := mul_le_mul_of_nonneg_left (le_max_left (y + b * w - t) 0) hl0
        have h2 := mul_le_mul_of_nonneg_left (le_max_left (y - t) 0)
          (show 0 ≤ 1 - l by linarith)
        have h3 : l * (y + b * w - t) + (1 - l) * (y - t) = y + a * w - t := by
          rw [← hlb]; ring
        linarith
    _ = ENNReal.ofReal l * S + ENNReal.ofReal (1 - l) * ENNReal.ofReal (y - t) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hm]; simp [S]
    _ ≤ ENNReal.ofReal l * S + ENNReal.ofReal (1 - l) * S := by gcongr
    _ = S := by
        rw [← add_mul, ← ENNReal.ofReal_add hl0 (by linarith)]; simp

/-! ## From stop-loss inequalities to (nc:eq:cx) -/

lemma cxCond_of_stopLoss {n : ℕ} {F : Measure ℝ} [IsProbabilityMeasure F] (hi : Integrable id F)
    (h : ∀ t, ∫⁻ x, ENNReal.ofReal (x - t) ∂F ≤
      ∫⁻ x, ENNReal.ofReal (n * mean F - (n - 1) * x - t) ∂F) : CxCondSL n F := by
  have hi' : Integrable (fun x : ℝ => x) F := hi
  have m1 : Measurable fun x : ℝ => x - mean F := by fun_prop
  have m2 : Measurable fun x : ℝ => -((n : ℝ) - 1) * (x - mean F) := by fun_prop
  refine ⟨?_, ?_, ?_, fun t => ?_⟩
  · rw [integrable_map_measure aestronglyMeasurable_id m1.aemeasurable]
    exact hi'.sub (integrable_const _)
  · rw [integrable_map_measure aestronglyMeasurable_id m2.aemeasurable]
    exact (hi'.sub (integrable_const _)).const_mul _
  · have e1 : mean (F.map fun x => x - mean F) = ∫ x, (x - mean F) ∂F :=
      integral_map (f := fun x : ℝ => x) m1.aemeasurable (by fun_prop)
    have e2 : mean (F.map fun x => -((n : ℝ) - 1) * (x - mean F)) =
        ∫ x, -((n : ℝ) - 1) * (x - mean F) ∂F :=
      integral_map (f := fun x : ℝ => x) m2.aemeasurable (by fun_prop)
    rw [e1, e2, integral_sub hi' (integrable_const _), integral_const_mul,
      integral_sub hi' (integrable_const _)]
    simp [mean]
  · unfold stopLoss
    rw [lintegral_map (by fun_prop) m1, lintegral_map (by fun_prop) m2]
    refine (le_of_eq ?_).trans ((h (mean F + t)).trans (le_of_eq ?_)) <;> congr 1 <;> ext x <;>
      ring_nf

lemma stopLoss_of_cxCond {n : ℕ} {F : Measure ℝ} (h : CxCondSL n F) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (x - t) ∂F ≤
      ∫⁻ x, ENNReal.ofReal (n * mean F - (n - 1) * x - t) ∂F := by
  have := h.2.2.2 (t - mean F)
  unfold stopLoss at this
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)] at this
  refine (le_of_eq ?_).trans (this.trans (le_of_eq ?_)) <;> congr 1 <;> ext x <;> ring_nf

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f`. -/
lemma ofReal_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun x => le_max_left _ _)
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part
          (Filter.Eventually.of_forall fun x => le_max_right _ _)
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by simp only [ofReal_max_zero]

/-! ## The uniform distribution on `[0,1]` -/

lemma unifI01 : unifI 0 1 = volume.restrict (Icc (0 : ℝ) 1) := by simp [unifI]

instance : IsProbabilityMeasure (unifI 0 1) := unifI_isProb 0 1

lemma lintegral_unif_ofReal {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂unifI 0 1 = ENNReal.ofReal (∫ x in (0 : ℝ)..1, f x) := by
  rw [unifI01, ← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc)
    (Filter.Eventually.of_forall h0), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

lemma integral_posPart_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ x in (0 : ℝ)..1, max (x - t) 0 = (1 - t) ^ 2 / 2 := by
  have hc : Continuous fun x : ℝ => max (x - t) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := t) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0 : ℝ)..t, max (x - t) 0 = ∫ x in (0 : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le ht0] at hx
    exact max_eq_right (by linarith [hx.2])
  have e2 : ∫ x in t..1, max (x - t) 0 = ∫ x in t..1, (x - t) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le ht1] at hx
    exact max_eq_left (by linarith [hx.1])
  rw [e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  ring

lemma integral_posPart_two {k r t : ℝ} (hk : 0 < k) (h0 : 0 ≤ r - t) (h1 : r - t ≤ k) :
    ∫ x in (0 : ℝ)..1, max (r - k * x - t) 0 = (r - t) ^ 2 / (2 * k) := by
  set x0 := (r - t) / k with hx0
  have hx00 : 0 ≤ x0 := div_nonneg h0 hk.le
  have hx01 : x0 ≤ 1 := (div_le_one hk).2 h1
  have hkx : k * x0 = r - t := by rw [hx0]; field_simp
  have hc : Continuous fun x : ℝ => max (r - k * x - t) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0 : ℝ)..x0, max (r - k * x - t) 0 = ∫ x in (0 : ℝ)..x0, (r - t - k * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hx00] at hx
    have : k * x ≤ k * x0 := mul_le_mul_of_nonneg_left hx.2 hk.le
    exact (max_eq_left (by linarith)).trans (by ring)
  have e2 : ∫ x in x0..1, max (r - k * x - t) 0 = ∫ x in x0..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hx01] at hx
    have : k * x0 ≤ k * x := mul_le_mul_of_nonneg_left hx.1 hk.le
    exact max_eq_right (by linarith)
  rw [e1, e2, intervalIntegral.integral_zero, add_zero, intervalIntegral.integral_sub
    intervalIntegrable_const (intervalIntegral.intervalIntegrable_id.const_mul k),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul, sub_zero]
  rw [hx0]; field_simp; ring

/-- The uniform parts are ordered for `0 ≤ t ≤ 1`: `E (U - t)_+ ≤ E (r - kU - t)_+`. -/
lemma unif_stopLoss {k r t : ℝ} (hk : 1 ≤ k) (hr : √k ≤ r) (hrk : r ≤ k) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (x - t) ∂unifI 0 1 ≤ ∫⁻ x, ENNReal.ofReal (r - k * x - t) ∂unifI 0 1 := by
  simp only [← ofReal_max_zero (_ - t)]
  have hs1 : 1 ≤ √k := by have := Real.sqrt_le_sqrt hk; rwa [Real.sqrt_one] at this
  have hss : √k * √k = k := Real.mul_self_sqrt (by linarith)
  rw [lintegral_unif_ofReal (by fun_prop) (fun _ => le_max_right _ _),
    lintegral_unif_ofReal (by fun_prop) (fun _ => le_max_right _ _),
    integral_posPart_one ht0 ht1, integral_posPart_two (by linarith) (by linarith) (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : √k * (1 - t) ≤ r - t := by nlinarith
  have h2 : k * (1 - t) ^ 2 ≤ (r - t) ^ 2 := by
    have : 0 ≤ √k * (1 - t) := by nlinarith
    nlinarith
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-! ## Mixtures with a uniform part -/

/-- `p A + (1-p) U[0,1]`. -/
def mix (p : ℝ) (A : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal p • A + ENNReal.ofReal (1 - p) • unifI 0 1

section Mix

variable {p : ℝ} {A : Measure ℝ}

lemma mix_isProb [IsProbabilityMeasure A] (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (mix p A) := by
  constructor
  rw [mix, add_apply, smul_apply, smul_apply, measure_univ, measure_univ, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

lemma unif_ae : ∀ᵐ x ∂(unifI 0 1), x ∈ Icc (0 : ℝ) 1 := by
  rw [unifI01]; exact ae_restrict_mem measurableSet_Icc

lemma mix_ae (hA : ∀ᵐ x ∂A, x ∈ Icc (0 : ℝ) 1) : ∀ᵐ x ∂(mix p A), x ∈ Icc (0 : ℝ) 1 := by
  rw [mix, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure hA _, Measure.ae_smul_measure unif_ae _⟩

lemma integrable_of_Icc01 {G : Measure ℝ} [IsFiniteMeasure G] (h : ∀ᵐ x ∂G, x ∈ Icc (0 : ℝ) 1) :
    Integrable id G :=
  Integrable.of_bound aestronglyMeasurable_id 1 (by
    filter_upwards [h] with x hx
    simp only [id, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2])

lemma integral_unif01 : ∫ x, x ∂(unifI 0 1) = 1 / 2 := by
  rw [unifI01, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp [integral_id]

lemma mean_mix [IsProbabilityMeasure A] (hA : ∀ᵐ x ∂A, x ∈ Icc (0 : ℝ) 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : mean (mix p A) = p * mean A + (1 - p) / 2 := by
  have iA : Integrable (fun x : ℝ => x) A := integrable_of_Icc01 hA
  have iU : Integrable (fun x : ℝ => x) (unifI 0 1) := integrable_of_Icc01 unif_ae
  unfold mean mix
  rw [integral_add_measure (iA.smul_measure ENNReal.ofReal_ne_top)
      (iU.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith), integral_unif01]
  simp; ring

/-- The stop-loss inequality for `p A + (1-p) U[0,1]` from the one for `A`, when
`√(n-1) ≤ nμ ≤ n - 1` (the proof of Proposition `nc:prop:atom`(b) and of Theorem
`nc:thm:unimodal` for `f₁`). -/
lemma stopLoss_mix {n : ℕ} (hn : 2 ≤ n) [IsProbabilityMeasure A]
    (hA : ∀ᵐ x ∂A, x ∈ Icc (0 : ℝ) 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {r : ℝ}
    (hAsl : ∀ t, ∫⁻ x, ENNReal.ofReal (x - t) ∂A ≤ ∫⁻ x, ENNReal.ofReal (r - (n - 1) * x - t) ∂A)
    (hr : r = n * mean (mix p A)) (hr1 : √((n : ℝ) - 1) ≤ r) (hr2 : r ≤ n - 1) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (x - t) ∂mix p A ≤
      ∫⁻ x, ENNReal.ofReal (r - (n - 1) * x - t) ∂mix p A := by
  have := mix_isProb (A := A) hp0 hp1
  have hae := mix_ae (p := p) hA
  have hi : Integrable (fun x : ℝ => x) (mix p A) := integrable_of_Icc01 hae
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt t 0 with ht | ht
  · -- `t ≤ 0`: both sides are at least `μ - t`, the left side equals it
    have hsub : Integrable (fun x : ℝ => x - t) (mix p A) := hi.sub (integrable_const t)
    have key : ∫⁻ x, ENNReal.ofReal (x - t) ∂mix p A = ENNReal.ofReal (∫ x, (x - t) ∂mix p A) :=
      (ofReal_integral_eq_lintegral_ofReal hsub
        (by filter_upwards [hae] with x hx; show 0 ≤ x - t; linarith [hx.1])).symm
    rw [key]
    have h2 : Integrable (fun x : ℝ => r - (n - 1) * x - t) (mix p A) :=
      ((integrable_const r).sub (hi.const_mul _)).sub (integrable_const t)
    refine le_trans (le_of_eq ?_) (ofReal_integral_le h2)
    congr 1
    have e1 : ∫ x, (x - t) ∂mix p A = mean (mix p A) - t := by
      rw [integral_sub hi (integrable_const t)]; simp [mean]
    have e2 : ∫ x, (r - (n - 1) * x - t) ∂mix p A = r - (n - 1) * mean (mix p A) - t := by
      have h3 : Integrable (fun x : ℝ => (n - 1) * x) (mix p A) := hi.const_mul _
      have h4 : Integrable (fun x : ℝ => r - (n - 1) * x) (mix p A) := (integrable_const r).sub h3
      rw [integral_sub (f := fun x : ℝ => r - (n - 1) * x) (g := fun _ => t) h4
        (integrable_const t), integral_sub (f := fun _ => r) (g := fun x : ℝ => (n - 1) * x)
        (integrable_const r) h3, integral_const_mul]; simp [mean]
    rw [e1, e2, hr]; ring
  rcases le_or_gt 1 t with ht1 | ht1
  · -- `t ≥ 1`: the left side vanishes
    have : ∫⁻ x, ENNReal.ofReal (x - t) ∂mix p A = 0 := by
      rw [← lintegral_zero (μ := mix p A)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      exact ENNReal.ofReal_of_nonpos (by linarith [hx.2])
    rw [this]; exact bot_le
  · -- `0 < t < 1`: the two parts separately
    unfold mix
    rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure,
      lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure]
    exact add_le_add (mul_le_mul_of_nonneg_left (hAsl t) bot_le)
      (mul_le_mul_of_nonneg_left (unif_stopLoss (by linarith) hr1 hr2 ht.le ht1.le) bot_le)

end Mix

/-! ## The parameters of Theorem `nc:thm:unimodal` -/

/-- The assumptions of Theorem `nc:thm:unimodal` on `n`, `p`, `β` and `η`; here `q = 1 - p` and
`c = 1/2 - β`. -/
structure Params (n : ℕ) (p β η : ℝ) : Prop where
  n3 : 3 ≤ n
  p_lo : 1 - 2 / (n : ℝ) < p
  p_hi : p < 1
  β_pos : 0 < β
  β_le : β ≤ ((n : ℝ) / 2 - √((n : ℝ) - 1)) / (n * p)
  η_pos : 0 < η
  η_lt1 : η < (1 - p) * β
  η_lt2 : η < (p - 1 + 2 / (n : ℝ)) / (2 * ((n : ℝ) - 1) * (1 - p))
  η_lt3 : η < (1 / 2 - β) / 2

namespace Params

variable {n : ℕ} {p β η : ℝ} (h : Params n p β η)
include h

lemma n_real : (3 : ℝ) ≤ n := by exact_mod_cast h.n3

lemma q_pos : 0 < 1 - p := by linarith [h.p_hi]

lemma p_pos : 0 < p := by
  have h3 := h.n_real
  have : 2 / (n : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
  linarith [h.p_lo]

lemma sqrt_gt : 1 < √((n : ℝ) - 1) := by
  have h3 := h.n_real
  have := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < n - 1 by linarith)
  rwa [Real.sqrt_one] at this

lemma np_gt : (n : ℝ) - 2 < n * p := by
  have h3 := h.n_real
  have := h.p_lo
  have e : (n : ℝ) * (1 - 2 / n) = n - 2 := by field_simp
  nlinarith

lemma βnp : β * (n * p) ≤ (n : ℝ) / 2 - √((n : ℝ) - 1) := by
  have := h.β_le
  have hnp : 0 < (n : ℝ) * p := mul_pos (by linarith [h.n_real]) h.p_pos
  rwa [le_div_iff₀ hnp] at this

lemma β_lt : β < 1 / 2 := by
  have := h.βnp; have := h.sqrt_gt; have := h.np_gt
  have hnp : 0 < (n : ℝ) * p := mul_pos (by linarith [h.n_real]) h.p_pos
  nlinarith

lemma c_pos : 0 < 1 / 2 - β := by linarith [h.β_lt]

/-- `μ = pc + q/2 = 1/2 - pβ`. -/
lemma r_ge : √((n : ℝ) - 1) ≤ n * (p * (1 / 2 - β) + (1 - p) / 2) := by
  have := h.βnp; nlinarith

lemma r_le : (n : ℝ) * (p * (1 / 2 - β) + (1 - p) / 2) ≤ n - 1 := by
  have := h.n_real; have := h.p_pos; have := h.β_pos
  have : 0 ≤ (n : ℝ) * p * β := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

lemma η_lt_c : η < (1 / 2 - β) / 2 := h.η_lt3

lemma key : 2 * ((n : ℝ) - 1) * (1 - p) * η < p - 1 + 2 / n := by
  have := h.η_lt2
  have hpos : 0 < 2 * ((n : ℝ) - 1) * (1 - p) := by
    have := h.n_real; have := h.q_pos
    exact mul_pos (mul_pos two_pos (by linarith)) (by linarith)
  rw [lt_div_iff₀ hpos] at this; linarith

end Params

/-- The weaker assumptions under which relation (nc:eq:cx) is proved: `n ≥ 2`, `0 < p < 1`,
`0 < β < 1/2`, `0 < η < c/2` and `nμ ≥ √(n-1)`. -/
structure CxParams (n : ℕ) (p β η : ℝ) : Prop where
  n2 : 2 ≤ n
  p_pos : 0 < p
  p_hi : p < 1
  β_pos : 0 < β
  β_lt : β < 1 / 2
  η_pos : 0 < η
  η_lt3 : η < (1 / 2 - β) / 2
  r_ge : √((n : ℝ) - 1) ≤ n * (p * (1 / 2 - β) + (1 - p) / 2)

namespace CxParams

variable {n : ℕ} {p β η : ℝ} (h : CxParams n p β η)
include h

lemma n_real : (2 : ℝ) ≤ n := by exact_mod_cast h.n2
lemma q_pos : 0 < 1 - p := by linarith [h.p_hi]
lemma c_pos : 0 < 1 / 2 - β := by linarith [h.β_lt]
lemma r_le : (n : ℝ) * (p * (1 / 2 - β) + (1 - p) / 2) ≤ n - 1 := by
  have := h.n_real; have := h.p_pos; have := h.β_pos
  have : 0 ≤ (n : ℝ) * p * β := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

end CxParams

lemma Params.toCx {n : ℕ} {p β η : ℝ} (h : Params n p β η) : CxParams n p β η :=
  ⟨by linarith [h.n3], h.p_pos, h.p_hi, h.β_pos, h.β_lt, h.η_pos, h.η_lt3, h.r_ge⟩

/-! ## The distributions -/

/-- `F₀ = p δ_c + q U[0,1]`. -/
def F0 (p c : ℝ) : Measure ℝ := mix p (Measure.dirac c)

/-- The distribution with the density `f₁`: `p (c + ηW) + q U[0,1]`, with `W ∼ ν`. -/
def F1 (p c η : ℝ) (ν : Measure ℝ) : Measure ℝ := mix p (ν.map fun w => c + η * w)

/-- The distribution of `X₀ + ηW`, with `X₀ ∼ F₀` and `W ∼ ν` independent. -/
def F2 (p c η : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ((F0 p c).prod ν).map fun z => z.1 + η * z.2

section Laws

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma integrable_of_Icc {G : Measure ℝ} [IsFiniteMeasure G] {a b : ℝ}
    (h : ∀ᵐ x ∂G, x ∈ Icc a b) : Integrable id G :=
  Integrable.of_bound aestronglyMeasurable_id (max |a| |b|) (by
    filter_upwards [h] with x hx
    simp only [id, Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx.1 hx.2)

omit [IsProbabilityMeasure ν] in
lemma integral_symm_eq_zero (hν : ν.map Neg.neg = ν) : ∫ w, w ∂ν = 0 := by
  have : ∫ w, w ∂ν = ∫ w, -w ∂ν := by
    conv_lhs => rw [← hν]
    exact integral_map measurable_neg.aemeasurable (by fun_prop)
  rw [integral_neg] at this; linarith

variable {c η : ℝ}

lemma peak_isProb : IsProbabilityMeasure (ν.map fun w => c + η * w) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

omit [IsProbabilityMeasure ν] in
lemma peak_ae (hη : 0 ≤ η) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) :
    ∀ᵐ x ∂(ν.map fun w => c + η * w), x ∈ Icc (c - η) (c + η) := by
  refine (ae_map_iff (p := fun x => x ∈ Icc (c - η) (c + η)) (by fun_prop) measurableSet_Icc).2 ?_
  filter_upwards [hs] with w hw
  constructor <;> nlinarith [hw.1, hw.2]

omit [IsProbabilityMeasure ν] in
lemma peak_ae01 (hη : 0 ≤ η) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) (h0 : η ≤ c) (h1 : c + η ≤ 1) :
    ∀ᵐ x ∂(ν.map fun w => c + η * w), x ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [peak_ae hη hs] with x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma mean_peak (hν : ν.map Neg.neg = ν) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) :
    mean (ν.map fun w => c + η * w) = c := by
  have iw : Integrable (fun w : ℝ => w) ν := integrable_of_Icc hs
  rw [mean, integral_map (by fun_prop) (by fun_prop), integral_add (integrable_const c)
    (iw.const_mul η), integral_const_mul, integral_symm_eq_zero hν]
  simp

/-- The stop-loss inequality for the peak `c + ηW` against `r - (n-1)(c + ηW)` when `r ≥ nc`. -/
lemma stopLoss_peak (hν : ν.map Neg.neg = ν) {n : ℕ} (hn : 2 ≤ n) (hη : 0 ≤ η) {r : ℝ}
    (hr : n * c ≤ r) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (x - t) ∂(ν.map fun w => c + η * w) ≤
      ∫⁻ x, ENNReal.ofReal (r - (n - 1) * x - t) ∂(ν.map fun w => c + η * w) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)]
  calc ∫⁻ w, ENNReal.ofReal (c + η * w - t) ∂ν
      ≤ ∫⁻ w, ENNReal.ofReal (c + ((n - 1) * η) * w - t) ∂ν :=
        stopLoss_scale hν c t hη (by nlinarith)
    _ = ∫⁻ w, ENNReal.ofReal (c + ((n - 1) * η) * (-w) - t) ∂ν :=
        (lintegral_neg_of_symm hν (g := fun w => ENNReal.ofReal (c + ((n - 1) * η) * w - t))
          (by fun_prop)).symm
    _ ≤ ∫⁻ w, ENNReal.ofReal (r - (n - 1) * (c + η * w) - t) ∂ν := by
        refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
        nlinarith

/-! ### Relation (nc:eq:cx) for `F₀`, `F₁`, `F₂` -/

variable {n : ℕ} {p β : ℝ}

lemma F0_isProb (h : CxParams n p β η) : IsProbabilityMeasure (F0 p (1 / 2 - β)) :=
  mix_isProb h.p_pos.le h.p_hi.le

lemma F0_ae (h : CxParams n p β η) : ∀ᵐ x ∂(F0 p (1 / 2 - β)), x ∈ Icc (0 : ℝ) 1 :=
  mix_ae (by
    exact (ae_dirac_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc).2
      ⟨h.c_pos.le, by linarith [h.β_pos]⟩)

lemma mean_F0 (h : CxParams n p β η) :
    mean (F0 p (1 / 2 - β)) = p * (1 / 2 - β) + (1 - p) / 2 := by
  rw [F0, mean_mix (by
    exact (ae_dirac_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc).2
      ⟨h.c_pos.le, by linarith [h.β_pos]⟩)
    h.p_pos.le h.p_hi.le]
  simp [mean]

/-- The stop-loss inequality for `F₀` (the proof of Proposition `nc:prop:atom`(b)). -/
lemma stopLoss_F0 (h : CxParams n p β η) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (x - t) ∂F0 p (1 / 2 - β) ≤
      ∫⁻ x, ENNReal.ofReal (n * mean (F0 p (1 / 2 - β)) - (n - 1) * x - t) ∂F0 p (1 / 2 - β) := by
  have hn : 2 ≤ n := h.n2
  refine stopLoss_mix hn (by
    exact (ae_dirac_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc).2
      ⟨h.c_pos.le, by linarith [h.β_pos]⟩)
    h.p_pos.le h.p_hi.le (fun t => ?_) rfl ?_ ?_ t
  · rw [lintegral_dirac, lintegral_dirac]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← F0, mean_F0 h]
    have := h.q_pos; have := h.β_pos
    have : 0 ≤ (n : ℝ) * (1 - p) * β := by have := h.n_real; positivity
    nlinarith
  · rw [← F0, mean_F0 h]; exact h.r_ge
  · rw [← F0, mean_F0 h]; exact h.r_le

variable (hν : ν.map Neg.neg = ν) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1)
include hν hs

omit hν hs in
lemma F1_isProb (h : CxParams n p β η) : IsProbabilityMeasure (F1 p (1 / 2 - β) η ν) :=
  have := peak_isProb (ν := ν) (c := 1 / 2 - β) (η := η)
  mix_isProb h.p_pos.le h.p_hi.le

omit hν [IsProbabilityMeasure ν] in
lemma peak_ae01' (h : CxParams n p β η) :
    ∀ᵐ x ∂(ν.map fun w => (1 / 2 - β) + η * w), x ∈ Icc (0 : ℝ) 1 :=
  peak_ae01 h.η_pos.le hs (by linarith [h.η_lt3, h.c_pos]) (by linarith [h.η_lt3, h.β_pos])

omit hν [IsProbabilityMeasure ν] in
lemma F1_ae (h : CxParams n p β η) : ∀ᵐ x ∂(F1 p (1 / 2 - β) η ν), x ∈ Icc (0 : ℝ) 1 :=
  mix_ae (peak_ae01' hs h)

lemma mean_F1 (h : CxParams n p β η) :
    mean (F1 p (1 / 2 - β) η ν) = p * (1 / 2 - β) + (1 - p) / 2 := by
  have := peak_isProb (ν := ν) (c := 1 / 2 - β) (η := η)
  rw [F1, mean_mix (peak_ae01' hs h) h.p_pos.le h.p_hi.le, mean_peak hν hs]

/-- Relation (nc:eq:cx) for `f₁`. -/
theorem cxCond_F1 (h : CxParams n p β η) : CxCondSL n (F1 p (1 / 2 - β) η ν) := by
  have := peak_isProb (ν := ν) (c := 1 / 2 - β) (η := η)
  have := F1_isProb (ν := ν) h
  have hn : 2 ≤ n := h.n2
  refine cxCond_of_stopLoss (integrable_of_Icc01 (F1_ae hs h)) fun t => ?_
  refine stopLoss_mix hn (peak_ae01' hs h) h.p_pos.le h.p_hi.le (fun t => ?_) rfl ?_ ?_ t
  · refine stopLoss_peak hν hn h.η_pos.le ?_ t
    rw [← F1, mean_F1 hν hs h]
    have := h.q_pos; have := h.β_pos
    have : 0 ≤ (n : ℝ) * (1 - p) * β := by have := h.n_real; positivity
    nlinarith
  · rw [← F1, mean_F1 hν hs h]; exact h.r_ge
  · rw [← F1, mean_F1 hν hs h]; exact h.r_le

omit hν hs in
lemma F2_isProb (h : CxParams n p β η) : IsProbabilityMeasure (F2 p (1 / 2 - β) η ν) := by
  have := F0_isProb h
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

omit hν hs in
lemma lintegral_F2 (h : CxParams n p β η) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂F2 p (1 / 2 - β) η ν = ∫⁻ x, ∫⁻ w, g (x + η * w) ∂ν ∂F0 p (1 / 2 - β) := by
  have := F0_isProb h
  rw [F2, lintegral_map hg (by fun_prop)]
  exact lintegral_prod (fun z : ℝ × ℝ => g (z.1 + η * z.2)) (hg.comp (by fun_prop)).aemeasurable

omit hν in
lemma integrable_F2 (h : CxParams n p β η) : Integrable id (F2 p (1 / 2 - β) η ν) := by
  have := F0_isProb h
  have iF0 : Integrable (fun x : ℝ => x) (F0 p (1 / 2 - β)) := integrable_of_Icc01 (F0_ae h)
  have iν : Integrable (fun w : ℝ => w) ν := integrable_of_Icc hs
  rw [F2, integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  exact (iF0.comp_fst ν).add ((iν.comp_snd _).const_mul η)

lemma mean_F2 (h : CxParams n p β η) :
    mean (F2 p (1 / 2 - β) η ν) = p * (1 / 2 - β) + (1 - p) / 2 := by
  have := F0_isProb h
  have iF0 : Integrable (fun x : ℝ => x) (F0 p (1 / 2 - β)) := integrable_of_Icc01 (F0_ae h)
  have iν : Integrable (fun w : ℝ => w) ν := integrable_of_Icc hs
  have i1 : Integrable (fun z : ℝ × ℝ => z.1) ((F0 p (1 / 2 - β)).prod ν) := iF0.comp_fst ν
  have i2 : Integrable (fun z : ℝ × ℝ => η * z.2) ((F0 p (1 / 2 - β)).prod ν) :=
    (iν.comp_snd _).const_mul η
  rw [mean, F2, integral_map (by fun_prop) (by fun_prop), integral_add i1 i2, integral_const_mul,
    integral_fun_fst (f := fun x : ℝ => x), integral_fun_snd (f := fun w : ℝ => w),
    integral_symm_eq_zero hν]
  simp only [probReal_univ, one_smul, smul_zero, mul_zero, add_zero]
  exact mean_F0 h

/-- Relation (nc:eq:cx) for `f₂`: the stop-loss inequality of `F₀` is integrated against the law
of `ηW`, and `ηW ≤_cx (n-1)ηW`, which has the law of `-(n-1)ηW`. -/
theorem cxCond_F2 (h : CxParams n p β η) : CxCondSL n (F2 p (1 / 2 - β) η ν) := by
  have := F0_isProb h
  have := F2_isProb (ν := ν) h
  have hn' : (2 : ℝ) ≤ n := by have := h.n_real; linarith
  have hη := h.η_pos.le
  refine cxCond_of_stopLoss (integrable_F2 hs h) fun t => ?_
  rw [mean_F2 hν hs h, lintegral_F2 h (by fun_prop), lintegral_F2 h (by fun_prop)]
  set r := (n : ℝ) * (p * (1 / 2 - β) + (1 - p) / 2) with hr
  have hr0 : r = n * mean (F0 p (1 / 2 - β)) := by rw [mean_F0 h]
  set F := F0 p (1 / 2 - β)
  calc ∫⁻ x, ∫⁻ w, ENNReal.ofReal (x + η * w - t) ∂ν ∂F
      = ∫⁻ w, ∫⁻ x, ENNReal.ofReal (x - (t - η * w)) ∂F ∂ν := by
        rw [lintegral_lintegral_swap ((show Measurable fun z : ℝ × ℝ =>
          ENNReal.ofReal (z.1 + η * z.2 - t) by fun_prop).aemeasurable)]
        congr 1; ext w; congr 1; ext x; ring_nf
    _ ≤ ∫⁻ w, ∫⁻ x, ENNReal.ofReal (r - (n - 1) * x - (t - η * w)) ∂F ∂ν := by
        refine lintegral_mono fun w => ?_
        rw [hr0]; exact stopLoss_F0 h (t - η * w)
    _ = ∫⁻ x, ∫⁻ w, ENNReal.ofReal ((r - (n - 1) * x) + η * w - t) ∂ν ∂F := by
        rw [lintegral_lintegral_swap ((show Measurable fun z : ℝ × ℝ =>
          ENNReal.ofReal (r - (n - 1) * z.2 - (t - η * z.1)) by fun_prop).aemeasurable)]
        congr 1; ext x; congr 1; ext w; ring_nf
    _ ≤ ∫⁻ x, ∫⁻ w, ENNReal.ofReal ((r - (n - 1) * x) + ((n - 1) * η) * w - t) ∂ν ∂F :=
        lintegral_mono fun x => stopLoss_scale hν _ t hη (by nlinarith)
    _ = ∫⁻ x, ∫⁻ w, ENNReal.ofReal ((r - (n - 1) * x) + ((n - 1) * η) * (-w) - t) ∂ν ∂F := by
        congr 1; ext x
        exact (lintegral_neg_of_symm hν (by fun_prop)).symm
    _ = ∫⁻ x, ∫⁻ w, ENNReal.ofReal (r - (n - 1) * (x + η * w) - t) ∂ν ∂F := by
        congr 1; ext x; congr 1; ext w; ring_nf

end Laws

/-! ## Masses of intervals -/

lemma unif_Icc_le (a b : ℝ) : unifI 0 1 (Icc a b) ≤ ENNReal.ofReal (b - a) := by
  rw [unifI01]; exact (Measure.restrict_apply_le _ _).trans (by rw [Real.volume_Icc])

lemma measure_eq_one_of_ae {G : Measure ℝ} [IsProbabilityMeasure G] {S : Set ℝ}
    (hS : MeasurableSet S) (h : ∀ᵐ x ∂G, x ∈ S) : G S = 1 :=
  (prob_compl_eq_zero_iff hS).1 (ae_iff.1 h)

lemma measure_eq_zero_of_ae {α : Type*} [MeasurableSpace α] {G : Measure α} {S : Set α}
    (h : ∀ᵐ x ∂G, x ∉ S) : G S = 0 := by
  have := ae_iff.1 h; simpa using this

section Masses

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {p c η : ℝ}

lemma mix_apply {A : Measure ℝ} (S : Set ℝ) :
    mix p A S = ENNReal.ofReal p * A S + ENNReal.ofReal (1 - p) * unifI 0 1 S := by
  rw [mix, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

omit [IsProbabilityMeasure ν] in
lemma F1_apply {S : Set ℝ} (hS : MeasurableSet S) :
    F1 p c η ν S = ENNReal.ofReal p * ν {w | c + η * w ∈ S} +
      ENNReal.ofReal (1 - p) * unifI 0 1 S := by
  rw [F1, mix_apply, Measure.map_apply (by fun_prop) hS]; rfl

lemma F2_apply [SFinite (F0 p c)] {S : Set ℝ} (hS : MeasurableSet S) :
    F2 p c η ν S = ∫⁻ w, F0 p c {x | x + η * w ∈ S} ∂ν := by
  rw [F2, Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply_symm (hS.preimage (by fun_prop))]
  rfl

lemma peak_mem (hη : 0 ≤ η) {w : ℝ} (hw : w ∈ Icc (-1 : ℝ) 1) : c + η * w ∈ Icc (c - η) (c + η) :=
  ⟨by nlinarith [hw.1], by nlinarith [hw.2]⟩

lemma F1_I_ge (hη : 0 ≤ η) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) :
    ENNReal.ofReal p ≤ F1 p c η ν (Icc (c - η) (c + η)) := by
  rw [F1_apply measurableSet_Icc]
  have : ν {w | c + η * w ∈ Icc (c - η) (c + η)} = 1 :=
    measure_eq_one_of_ae (measurableSet_Icc.preimage (by fun_prop))
      (by filter_upwards [hs] with w hw; exact peak_mem hη hw)
  rw [this, mul_one]; exact le_self_add

omit [IsProbabilityMeasure ν] in
lemma F1_K_le (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) {a b : ℝ}
    (hK : ∀ w ∈ Icc (-1 : ℝ) 1, c + η * w ∉ Icc a b) :
    F1 p c η ν (Icc a b) ≤ ENNReal.ofReal (1 - p) * ENNReal.ofReal (b - a) := by
  rw [F1_apply measurableSet_Icc,
    measure_eq_zero_of_ae (S := {w | c + η * w ∈ Icc a b})
      (by filter_upwards [hs] with w hw; exact hK w hw), mul_zero, zero_add]
  exact mul_le_mul_of_nonneg_left (unif_Icc_le a b) bot_le

lemma F0_preimage_le {a b w : ℝ} (hK : c + η * w ∉ Icc a b) :
    F0 p c {x | x + η * w ∈ Icc a b} ≤ ENNReal.ofReal (1 - p) * ENNReal.ofReal (b - a) := by
  have e : {x | x + η * w ∈ Icc a b} = Icc (a - η * w) (b - η * w) := by
    ext x; simp only [mem_ofPred_eq, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hc : c ∉ Icc (a - η * w) (b - η * w) := fun hc =>
    hK ⟨by linarith [hc.1], by linarith [hc.2]⟩
  rw [e, F0, mix_apply, Measure.dirac_apply, indicator_of_notMem hc, mul_zero, zero_add]
  refine mul_le_mul_of_nonneg_left ((unif_Icc_le _ _).trans (le_of_eq ?_)) bot_le
  congr 1; ring

lemma F2_K_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) {a b : ℝ}
    (hK : ∀ w ∈ Icc (-1 : ℝ) 1, c + η * w ∉ Icc a b) :
    F2 p c η ν (Icc a b) ≤ ENNReal.ofReal (1 - p) * ENNReal.ofReal (b - a) := by
  have : IsProbabilityMeasure (F0 p c) := mix_isProb hp0 hp1
  rw [F2_apply measurableSet_Icc]
  calc ∫⁻ w, F0 p c {x | x + η * w ∈ Icc a b} ∂ν
      ≤ ∫⁻ _w, ENNReal.ofReal (1 - p) * ENNReal.ofReal (b - a) ∂ν :=
        lintegral_mono_ae (by filter_upwards [hs] with w hw; exact F0_preimage_le (hK w hw))
    _ = _ := by simp

lemma F2_I_ge (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 ≤ η) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1) :
    ENNReal.ofReal p ≤ F2 p c η ν (Icc (c - η) (c + η)) := by
  have : IsProbabilityMeasure (F0 p c) := mix_isProb hp0 hp1
  rw [F2_apply measurableSet_Icc]
  calc ENNReal.ofReal p = ∫⁻ _w, ENNReal.ofReal p ∂ν := by simp
    _ ≤ ∫⁻ w, F0 p c {x | x + η * w ∈ Icc (c - η) (c + η)} ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hs] with w hw
        rw [F0, mix_apply, Measure.dirac_apply_of_mem (show c ∈ {x | x + η * w ∈ Icc (c - η) (c + η)}
          from peak_mem hη hw), mul_one]
        exact le_self_add

end Masses

/-! ## Complete mixability and symmetry from masses -/

/-- From the masses of a peak `I = [c-η, c+η]` and of `J = nμ - (n-1)I`, Lemma `nc:lem:peak`
(`NormAtom.peak`) bounds from below the probability that a sum of `n` variables with law `F`
misses `nμ`, under any coupling. -/
theorem miss_bound_of_mass {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ}
    [IsProbabilityMeasure F] {c η p m : ℝ} (hcμ : n * (c + η) < n * mean F)
    (hI : ENNReal.ofReal p ≤ F (Icc (c - η) (c + η)))
    (hJ : F (Icc (n * mean F - (n - 1) * (c + η)) (n * mean F - (n - 1) * (c - η))) ≤
      ENNReal.ofReal m) (hm : 0 ≤ m)
    (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hPm : ∀ i, P.map (fun x => x i) = F) :
    (n : ℝ) / 2 * (p - m) - ((n : ℝ) - 2) / 2 ≤ (P {x | ∑ i, x i ≠ n * mean F}).toReal := by
  set I := Icc (c - η) (c + η)
  have hsep : n * mean F ∉ NormAtom.sumSet (fun _ : Fin n => I) := by
    rintro ⟨x, hx, hsum⟩
    have : ∑ i, x i ≤ ∑ _i : Fin n, (c + η) := Finset.sum_le_sum fun i _ => (hx i).2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have key := NormAtom.peak P (fun _ => F) hPm hn (n * mean F) (fun _ => I)
    (fun _ => isCompact_Icc) hsep
  refine le_trans ?_ key
  have hJsub : ∀ j : Fin n, NormAtom.peakJ (n * mean F) (fun _ => I) j \ I ⊆
      Icc (n * mean F - (n - 1) * (c + η)) (n * mean F - (n - 1) * (c - η)) := by
    rintro j y ⟨⟨x, hx, rfl⟩, -⟩
    have hcard : (((Finset.univ : Finset (Fin n)).erase j).card : ℝ) = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega)]
      simp
    have hu : ∑ i ∈ Finset.univ.erase j, x i ≤ ∑ _i ∈ Finset.univ.erase j, (c + η) :=
      Finset.sum_le_sum fun i hi => (hx i (Finset.ne_of_mem_erase hi)).2
    have hl : ∑ _i ∈ Finset.univ.erase j, (c - η) ≤ ∑ i ∈ Finset.univ.erase j, x i :=
      Finset.sum_le_sum fun i hi => (hx i (Finset.ne_of_mem_erase hi)).1
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at hu hl
    constructor <;> linarith
  have hT : p ≤ (F I).toReal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hI
  have hS : ∀ j : Fin n, (F (NormAtom.peakJ (n * mean F) (fun _ => I) j \ I)).toReal ≤ m :=
    fun j => ENNReal.toReal_le_of_le_ofReal hm ((measure_mono (hJsub j)).trans hJ)
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hS j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum ⊢
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hT hn0]

/-- If `F(I) - F(J) > 1 - 2/n`, then `F` is not `n`-completely mixable (Lemma `nc:lem:peak`,
`NormAtom.peak_interval`). -/
theorem not_completelyMixable_of_mass {n : ℕ} (hn : 2 ≤ n)
    {F : Measure ℝ} [IsProbabilityMeasure F] (hi : Integrable id F) {c η p m : ℝ}
    (hcμ : c + η < mean F) (hI : ENNReal.ofReal p ≤ F (Icc (c - η) (c + η)))
    (hJ : F (Icc (n * mean F - (n - 1) * (c + η)) (n * mean F - (n - 1) * (c - η))) ≤
      ENNReal.ofReal m) (hm : 0 ≤ m) (hlt : 1 - 2 / (n : ℝ) < p - m) :
    ¬ CompletelyMixable n F := by
  intro hF
  have key := NormAtom.peak_interval hn hF hi (μ := mean F) rfl (u := c - η) (v := c + η)
    (fun h => by linarith [h.2])
  have hT : p ≤ (F (Icc (c - η) (c + η))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hI
  have hS := ENNReal.toReal_le_of_le_ofReal hm ((measure_mono (sdiff_subset (t := Icc (c - η) (c + η)))).trans hJ)
  linarith

/-- A law whose peak `I` is heavier than the reflected interval `2μ - I` is not symmetric. -/
theorem not_symm_of_mass {F : Measure ℝ} [IsProbabilityMeasure F] (hi : Integrable id F)
    {c η p m : ℝ} (hI : ENNReal.ofReal p ≤ F (Icc (c - η) (c + η)))
    (hK : F (Icc (2 * mean F - c - η) (2 * mean F - c + η)) ≤ ENNReal.ofReal m) (hm0 : 0 ≤ m)
    (hmp : m < p) (a : ℝ) : F.map (fun x => a - x) ≠ F := by
  intro ha
  have hi' : Integrable (fun x : ℝ => x) F := hi
  have hmean : mean F = a - mean F := by
    conv_lhs => rw [← ha]
    rw [mean, integral_map (f := fun y : ℝ => y) (by fun_prop) (by fun_prop),
      integral_sub (integrable_const a) hi']
    simp [mean]
  have ha2 : a = 2 * mean F := by linarith
  have hpre : F (Icc (c - η) (c + η)) = F (Icc (2 * mean F - c - η) (2 * mean F - c + η)) := by
    conv_lhs => rw [← ha]
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
    congr 1; ext x; simp only [mem_preimage, mem_Icc, ha2]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have := hI.trans (hpre ▸ hK)
  exact absurd this (not_le.2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hmp))

/-! ## The convex order by all convex functions, and the norm inequalities

`NormAtom.CxCond` is relation (nc:eq:cx) with the convex order defined by all convex functions;
the classical equivalence with the stop-loss form for bounded laws is the hypothesis
`NormAtom.H_stoploss_cx`, and the cited theorem of Shmalo that (nc:eq:cx) implies (nc:eq:norm)
is `NormAtom.H_shmalo26b` (both stated by agent NC1). -/

lemma integral_posPart_eq_stopLoss {L : Measure ℝ} (t : ℝ) :
    ∫ x, max (x - t) 0 ∂L = (stopLoss L t).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => max (x - t) 0)
    (Filter.Eventually.of_forall fun x => le_max_right _ _) (by fun_prop)]
  simp only [ofReal_max_zero, stopLoss]

theorem cxCond_of_SL (H : NormAtom.H_stoploss_cx) {n : ℕ} {F : Measure ℝ} [IsProbabilityMeasure F]
    {a b : ℝ} (hF : ∀ᵐ x ∂F, x ∈ Icc a b) (h : CxCondSL n F) : NormAtom.CxCond n F (mean F) := by
  obtain ⟨R₁, h₁⟩ := NormAtom.map_compl_Icc_eq_zero hF (f := fun x => x - mean F) (by fun_prop)
  obtain ⟨R₂, h₂⟩ := NormAtom.map_compl_Icc_eq_zero hF
    (f := fun x => -((n : ℝ) - 1) * (x - mean F)) (by fun_prop)
  refine H _ _ ((Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance)
    ((Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance) ?_ h.2.2.1 ?_
  · refine ⟨max R₁ R₂, measure_mono_null ?_ h₁, measure_mono_null ?_ h₂⟩ <;>
    · intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx ⊢
      rcases hx with h | h
      · left; linarith [le_max_left R₁ R₂, le_max_right R₁ R₂]
      · right; linarith [le_max_left R₁ R₂, le_max_right R₁ R₂]
  · intro t
    rw [integral_posPart_eq_stopLoss, integral_posPart_eq_stopLoss]
    refine ENNReal.toReal_mono ?_ (h.2.2.2 t)
    have hi : Integrable (fun x : ℝ => max (x - t) 0)
        (F.map fun x => -((n : ℝ) - 1) * (x - mean F)) :=
      (h.2.1.sub (integrable_const t)).pos_part
    have := hi.lintegral_lt_top
    simp only [ofReal_max_zero] at this
    exact this.ne

theorem normIneqs_of_SL (H1 : NormAtom.H_stoploss_cx) (H2 : NormAtom.H_shmalo26b) {n : ℕ}
    (hn : 2 ≤ n) {F : Measure ℝ} [IsProbabilityMeasure F] {a b : ℝ} (hF : ∀ᵐ x ∂F, x ∈ Icc a b)
    (h : CxCondSL n F) : NormAtom.NormIneqs n F (mean F) := by
  obtain ⟨R, hR⟩ := NormAtom.map_compl_Icc_eq_zero hF continuous_id
  rw [Measure.map_id] at hR
  exact H2 n F (mean F) hn inferInstance ⟨R, hR⟩ (integrable_of_Icc hF) rfl (cxCond_of_SL H1 hF h)

/-! ## Theorem `nc:thm:unimodal` for the laws `F₁` and `F₂` -/

section Main

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {n : ℕ} {p β η : ℝ}

lemma disj_J (h : Params n p β η) {w : ℝ} (hw : w ∈ Icc (-1 : ℝ) 1) :
    (1 / 2 - β) + η * w ∉ Icc (n * (p * (1 / 2 - β) + (1 - p) / 2) - (n - 1) * ((1 / 2 - β) + η))
      (n * (p * (1 / 2 - β) + (1 - p) / 2) - (n - 1) * ((1 / 2 - β) - η)) := by
  intro hm
  have h1 := hm.1
  have hn : (0 : ℝ) < n := by linarith [h.n_real]
  have h2 : (n : ℝ) * η < n * ((1 - p) * β) := mul_lt_mul_of_pos_left h.η_lt1 hn
  have h3 : η * w ≤ η := by nlinarith [hw.2, h.η_pos]
  nlinarith

lemma disj_K (h : Params n p β η) {w : ℝ} (hw : w ∈ Icc (-1 : ℝ) 1) :
    (1 / 2 - β) + η * w ∉ Icc (2 * (p * (1 / 2 - β) + (1 - p) / 2) - (1 / 2 - β) - η)
      (2 * (p * (1 / 2 - β) + (1 - p) / 2) - (1 / 2 - β) + η) := by
  intro hm
  have h1 := hm.1
  have h3 : η * w ≤ η := by nlinarith [hw.2, h.η_pos]
  nlinarith [h.η_lt1]

lemma mean_gt (h : Params n p β η) : (1 / 2 - β) + η < p * (1 / 2 - β) + (1 - p) / 2 := by
  nlinarith [h.η_lt1]

lemma hlt_J (h : Params n p β η) :
    1 - 2 / (n : ℝ) < p - (1 - p) * (2 * ((n : ℝ) - 1) * η) := by
  have := h.key; nlinarith

lemma hlt_K (h : Params n p β η) : (1 - p) * (2 * η) < p := by
  have := h.key; have := h.n_real; have := h.q_pos; have := h.η_pos
  have : 2 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have e : 2 * ((n : ℝ) - 1) * (1 - p) * η - (1 - p) * (2 * η) = 2 * (((n : ℝ) - 2) * ((1 - p) * η)) := by
    ring
  have : 0 ≤ ((n : ℝ) - 2) * ((1 - p) * η) := mul_nonneg (by linarith) (by positivity)
  linarith

lemma len_J (h : Params n p β η) :
    ENNReal.ofReal (1 - p) * ENNReal.ofReal
        ((n * (p * (1 / 2 - β) + (1 - p) / 2) - (n - 1) * ((1 / 2 - β) - η)) -
          (n * (p * (1 / 2 - β) + (1 - p) / 2) - (n - 1) * ((1 / 2 - β) + η))) =
      ENNReal.ofReal ((1 - p) * (2 * ((n : ℝ) - 1) * η)) := by
  rw [← ENNReal.ofReal_mul h.q_pos.le]; congr 1; ring

lemma len_K (h : Params n p β η) :
    ENNReal.ofReal (1 - p) * ENNReal.ofReal
        ((2 * (p * (1 / 2 - β) + (1 - p) / 2) - (1 / 2 - β) + η) -
          (2 * (p * (1 / 2 - β) + (1 - p) / 2) - (1 / 2 - β) - η)) =
      ENNReal.ofReal ((1 - p) * (2 * η)) := by
  rw [← ENNReal.ofReal_mul h.q_pos.le]; congr 1; ring

lemma mJ_nonneg (h : Params n p β η) : 0 ≤ (1 - p) * (2 * ((n : ℝ) - 1) * η) := by
  have hq := h.q_pos; have hη := h.η_pos; have hn := h.n_real
  exact mul_nonneg hq.le (by nlinarith)

variable (hν : ν.map Neg.neg = ν) (hs : ∀ᵐ w ∂ν, w ∈ Icc (-1 : ℝ) 1)
include hν hs

/-- `F₁` is not `n`-completely mixable. -/
theorem not_completelyMixable_F1 (h : Params n p β η) :
    ¬ CompletelyMixable n (F1 p (1 / 2 - β) η ν) := by
  have := F1_isProb (ν := ν) h.toCx
  refine not_completelyMixable_of_mass (by linarith [h.n3]) (integrable_of_Icc01 (F1_ae hs h.toCx))
    (c := 1 / 2 - β) (η := η) ?_ (F1_I_ge h.η_pos.le hs) ?_ (mJ_nonneg h) (hlt_J h)
  · rw [mean_F1 hν hs h.toCx]; exact mean_gt h
  · rw [mean_F1 hν hs h.toCx, ← len_J h]; exact F1_K_le hs fun w hw => disj_J h hw

/-- `F₂` is not `n`-completely mixable. -/
theorem not_completelyMixable_F2 (h : Params n p β η) :
    ¬ CompletelyMixable n (F2 p (1 / 2 - β) η ν) := by
  have := F2_isProb (ν := ν) h.toCx
  refine not_completelyMixable_of_mass (by linarith [h.n3]) (integrable_F2 hs h.toCx)
    (c := 1 / 2 - β) (η := η) ?_ (F2_I_ge h.p_pos.le h.p_hi.le h.η_pos.le hs) ?_ (mJ_nonneg h)
    (hlt_J h)
  · rw [mean_F2 hν hs h.toCx]; exact mean_gt h
  · rw [mean_F2 hν hs h.toCx, ← len_J h]
    exact F2_K_le h.p_pos.le h.p_hi.le hs fun w hw => disj_J h hw

/-- Under every coupling `P` of `n` copies of `F₁`, the sum misses `nμ` with probability at least
`(n/2)(p - 2(n-1)ηq) - (n-2)/2`. -/
theorem miss_bound_F1 (h : Params n p β η) (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hPm : ∀ i, P.map (fun x => x i) = F1 p (1 / 2 - β) η ν) :
    (n : ℝ) / 2 * (p - 2 * ((n : ℝ) - 1) * η * (1 - p)) - ((n : ℝ) - 2) / 2 ≤
      (P {x | ∑ i, x i ≠ n * (p * (1 / 2 - β) + (1 - p) / 2)}).toReal := by
  have := F1_isProb (ν := ν) h.toCx
  have hb := miss_bound_of_mass (by linarith [h.n3]) (F := F1 p (1 / 2 - β) η ν)
    (c := 1 / 2 - β) (η := η) ?_ (F1_I_ge h.η_pos.le hs) ?_ (mJ_nonneg h) P hPm
  · rw [mean_F1 hν hs h.toCx] at hb
    refine le_trans (le_of_eq ?_) hb; ring
  · rw [mean_F1 hν hs h.toCx]; nlinarith [mean_gt h, h.n_real]
  · rw [mean_F1 hν hs h.toCx, ← len_J h]; exact F1_K_le hs fun w hw => disj_J h hw

theorem miss_bound_F2 (h : Params n p β η) (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hPm : ∀ i, P.map (fun x => x i) = F2 p (1 / 2 - β) η ν) :
    (n : ℝ) / 2 * (p - 2 * ((n : ℝ) - 1) * η * (1 - p)) - ((n : ℝ) - 2) / 2 ≤
      (P {x | ∑ i, x i ≠ n * (p * (1 / 2 - β) + (1 - p) / 2)}).toReal := by
  have := F2_isProb (ν := ν) h.toCx
  have hb := miss_bound_of_mass (by linarith [h.n3]) (F := F2 p (1 / 2 - β) η ν)
    (c := 1 / 2 - β) (η := η) ?_ (F2_I_ge h.p_pos.le h.p_hi.le h.η_pos.le hs) ?_ (mJ_nonneg h)
    P hPm
  · rw [mean_F2 hν hs h.toCx] at hb
    refine le_trans (le_of_eq ?_) hb; ring
  · rw [mean_F2 hν hs h.toCx]; nlinarith [mean_gt h, h.n_real]
  · rw [mean_F2 hν hs h.toCx, ← len_J h]
    exact F2_K_le h.p_pos.le h.p_hi.le hs fun w hw => disj_J h hw

/-- `F₁` is not symmetric about any point. -/
theorem not_symm_F1 (h : Params n p β η) (a : ℝ) :
    (F1 p (1 / 2 - β) η ν).map (fun x => a - x) ≠ F1 p (1 / 2 - β) η ν := by
  have := F1_isProb (ν := ν) h.toCx
  refine not_symm_of_mass (integrable_of_Icc01 (F1_ae hs h.toCx)) (c := 1 / 2 - β) (η := η)
    (F1_I_ge h.η_pos.le hs) ?_ (by have := h.q_pos; have := h.η_pos; positivity) (hlt_K h) a
  rw [mean_F1 hν hs h.toCx, ← len_K h]; exact F1_K_le hs fun w hw => disj_K h hw

/-- `F₂` is not symmetric about any point. -/
theorem not_symm_F2 (h : Params n p β η) (a : ℝ) :
    (F2 p (1 / 2 - β) η ν).map (fun x => a - x) ≠ F2 p (1 / 2 - β) η ν := by
  have := F2_isProb (ν := ν) h.toCx
  refine not_symm_of_mass (integrable_F2 hs h.toCx) (c := 1 / 2 - β) (η := η)
    (F2_I_ge h.p_pos.le h.p_hi.le h.η_pos.le hs) ?_
    (by have := h.q_pos; have := h.η_pos; positivity) (hlt_K h) a
  rw [mean_F2 hν hs h.toCx, ← len_K h]
  exact F2_K_le h.p_pos.le h.p_hi.le hs fun w hw => disj_K h hw

omit hν in
/-- `F₂` is carried by `[-1, 2]`. -/
lemma F2_ae (h : CxParams n p β η) : ∀ᵐ x ∂(F2 p (1 / 2 - β) η ν), x ∈ Icc (-1 : ℝ) 2 := by
  have := F0_isProb h
  refine ae_iff.2 ?_
  have e : {x : ℝ | ¬ x ∈ Icc (-1 : ℝ) 2} = (Icc (-1 : ℝ) 2)ᶜ := rfl
  rw [e, F2_apply measurableSet_Icc.compl]
  rw [← lintegral_zero (μ := ν)]
  refine lintegral_congr_ae ?_
  filter_upwards [hs] with w hw
  refine measure_eq_zero_of_ae ?_
  filter_upwards [F0_ae h] with x hx
  have hη1 : η ≤ 1 := by linarith [h.η_lt3, h.c_pos, h.β_pos]
  have : -1 ≤ η * w := by nlinarith [hw.1, h.η_pos]
  have : η * w ≤ 1 := by nlinarith [hw.2, h.η_pos]
  simp only [mem_compl_iff, mem_Icc, not_not]
  constructor <;> linarith [hx.1, hx.2]

end Main

/-! ## The densities `f₁` and `f₂` -/

/-- `w` is a probability density on `[-1,1]` that is even and non-increasing on `[0,1]`. -/
structure IsBump (w : ℝ → ℝ) : Prop where
  meas : Measurable w
  nonneg : ∀ x, 0 ≤ w x
  supp : ∀ x, 1 < |x| → w x = 0
  total : ∫⁻ x, ENNReal.ofReal (w x) = 1
  even : ∀ x, w (-x) = w x
  anti : AntitoneOn w (Icc 0 1)

/-- The law of `W` with the density `w`. -/
def wLaw (w : ℝ → ℝ) : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (w x)

/-- `w_η(x) = w(x/η)/η`. -/
def wη (w : ℝ → ℝ) (η : ℝ) (x : ℝ) : ℝ := w (x / η) / η

/-- The density `f₁(x) = q 1_{[0,1]}(x) + p w_η(x - c)`. -/
def f1 (w : ℝ → ℝ) (p c η : ℝ) (x : ℝ) : ℝ :=
  (1 - p) * (Icc (0 : ℝ) 1).indicator (fun _ => 1) x + p * wη w η (x - c)

/-- `u_η = 1_{[0,1]} * w_η`. -/
def uη (w : ℝ → ℝ) (η : ℝ) : ℝ → ℝ :=
  convolution ((Icc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) (wη w η) (ContinuousLinearMap.mul ℝ ℝ)
    volume

/-- The density `f₂ = p w_η(· - c) + q u_η` of `X₀ + ηW`. -/
def f2 (w : ℝ → ℝ) (p c η : ℝ) (x : ℝ) : ℝ := p * wη w η (x - c) + (1 - p) * uη w η x

namespace IsBump

variable {w : ℝ → ℝ} (hw : IsBump w)
include hw

lemma isProb : IsProbabilityMeasure (wLaw w) :=
  ⟨by rw [wLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hw.total⟩

lemma symm : (wLaw w).map Neg.neg = wLaw w := by
  ext S hS
  rw [Measure.map_apply measurable_neg hS, wLaw, withDensity_apply _ (hS.preimage measurable_neg),
    withDensity_apply _ hS, ← lintegral_indicator (hS.preimage measurable_neg),
    ← lintegral_indicator hS]
  have : ∀ x, (Neg.neg ⁻¹' S).indicator (fun x => ENNReal.ofReal (w x)) x =
      S.indicator (fun x => ENNReal.ofReal (w x)) (-x) := by
    intro x
    by_cases hx : -x ∈ S
    · rw [indicator_of_mem (show x ∈ Neg.neg ⁻¹' S from hx), indicator_of_mem hx, hw.even]
    · rw [indicator_of_notMem (show x ∉ Neg.neg ⁻¹' S from hx), indicator_of_notMem hx]
  simp_rw [this]
  exact lintegral_neg_eq_self _

lemma ae_Icc : ∀ᵐ x ∂(wLaw w), x ∈ Icc (-1 : ℝ) 1 := by
  rw [wLaw, ae_withDensity_iff (f := fun x => ENNReal.ofReal (w x))
    (ENNReal.measurable_ofReal.comp hw.meas)]
  refine Filter.Eventually.of_forall fun x hx => ?_
  by_contra hxI
  apply hx
  rw [hw.supp x (by rw [← not_le, abs_le]; exact hxI), ENNReal.ofReal_zero]

lemma integrable : Integrable w := by
  refine ⟨hw.meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hw.nonneg), hw.total]
  exact ENNReal.one_lt_top

lemma le_zero (x : ℝ) : w x ≤ w 0 := by
  by_cases hx : 1 < |x|
  · rw [hw.supp x hx]; exact hw.nonneg 0
  · rw [not_lt] at hx
    have h1 : w x = w |x| := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, hw.even]
    rw [h1]
    exact hw.anti ⟨le_refl 0, zero_le_one⟩ ⟨abs_nonneg x, hx⟩ (abs_nonneg x)

lemma monotoneOn_Iic : MonotoneOn w (Iic 0) := by
  intro u hu v hv huv
  by_cases h1 : u < -1
  · rw [hw.supp u (by rw [abs_of_neg (by linarith)]; linarith)]; exact hw.nonneg v
  · rw [not_lt] at h1
    rw [← hw.even u, ← hw.even v]
    exact hw.anti ⟨by linarith [show v ≤ 0 from hv], by linarith⟩
      ⟨by linarith [show u ≤ 0 from hu], by linarith⟩ (by linarith)

lemma antitoneOn_Ici : AntitoneOn w (Ici 0) := by
  intro u hu v hv huv
  by_cases h1 : 1 < v
  · rw [hw.supp v (by rw [abs_of_pos (by linarith)]; linarith)]; exact hw.nonneg u
  · rw [not_lt] at h1
    exact hw.anti ⟨hu, by linarith⟩ ⟨hv, h1⟩ huv

end IsBump

/-- Change of variables `x = c + ηw`. -/
lemma lintegral_affine {g : ℝ → ℝ≥0∞} (hg : Measurable g) {η : ℝ} (hη : 0 < η) (c : ℝ) :
    ∫⁻ w, g (c + η * w) = ENNReal.ofReal (1 / η) * ∫⁻ x, g x := by
  have := lintegral_map (μ := volume) (f := fun y => g (c + y)) (g := fun w => η * w)
    (by fun_prop) (by fun_prop)
  rw [← this, Real.map_volume_mul_left hη.ne', lintegral_smul_measure,
    lintegral_add_left_eq_self (fun y => g y) c, abs_inv, abs_of_pos hη, one_div, smul_eq_mul]

/-- The law of `c + ηW` has the density `w_η(· - c)`. -/
lemma peak_eq_withDensity {w : ℝ → ℝ} (hw : IsBump w) {η : ℝ} (hη : 0 < η) (c : ℝ) :
    (wLaw w).map (fun x => c + η * x) =
      volume.withDensity fun y => ENNReal.ofReal (wη w η (y - c)) := by
  ext S hS
  rw [Measure.map_apply (by fun_prop) hS, wLaw, withDensity_apply _ (hS.preimage (by fun_prop)),
    withDensity_apply _ hS, ← lintegral_indicator (hS.preimage (by fun_prop)),
    ← lintegral_indicator hS]
  set G : ℝ → ℝ≥0∞ := fun y => S.indicator (fun y => ENNReal.ofReal (w ((y - c) / η))) y with hG
  have hGm : Measurable G :=
    (Measurable.indicator (ENNReal.measurable_ofReal.comp (hw.meas.comp (by fun_prop))) hS)
  have e1 : ∀ x, ((fun x => c + η * x) ⁻¹' S).indicator (fun x => ENNReal.ofReal (w x)) x =
      G (c + η * x) := by
    intro x
    have : (c + η * x - c) / η = x := by field_simp; ring
    by_cases hx : c + η * x ∈ S
    · rw [indicator_of_mem (show x ∈ (fun x => c + η * x) ⁻¹' S from hx), hG]
      simp only; rw [indicator_of_mem hx, this]
    · rw [indicator_of_notMem (show x ∉ (fun x => c + η * x) ⁻¹' S from hx), hG]
      simp only; rw [indicator_of_notMem hx]
  simp_rw [e1]
  rw [lintegral_affine hGm hη c, ← lintegral_const_mul _ hGm]
  congr 1; ext y
  rw [hG]; simp only
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem hy, wη, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

section Densities

variable {w : ℝ → ℝ} (hw : IsBump w) {η : ℝ} (hη : 0 < η)
include hw hη

lemma wη_nonneg (x : ℝ) : 0 ≤ wη w η x := div_nonneg (hw.nonneg _) hη.le

omit hη in
lemma measurable_wη : Measurable (wη w η) := (hw.meas.comp (by fun_prop)).div_const η

lemma wη_eq_zero {x : ℝ} (hx : η < |x|) : wη w η x = 0 := by
  rw [wη, hw.supp, zero_div]
  rw [abs_div, abs_of_pos hη, lt_div_iff₀ hη, one_mul]; exact hx

lemma integrable_wη : Integrable (wη w η) := (hw.integrable.comp_div hη.ne').div_const η

lemma wη_le (x : ℝ) : wη w η x ≤ w 0 / η := div_le_div_of_nonneg_right (hw.le_zero _) hη.le

lemma wη_monotoneOn {c : ℝ} : MonotoneOn (fun x => wη w η (x - c)) (Iic c) := by
  intro x hx y hy hxy
  refine div_le_div_of_nonneg_right (hw.monotoneOn_Iic ?_ ?_
    (div_le_div_of_nonneg_right (by linarith) hη.le)) hη.le
  · exact div_nonpos_iff.2 (Or.inr ⟨by linarith [show x ≤ c from hx], hη.le⟩)
  · exact div_nonpos_iff.2 (Or.inr ⟨by linarith [show y ≤ c from hy], hη.le⟩)

lemma wη_antitoneOn {c : ℝ} : AntitoneOn (fun x => wη w η (x - c)) (Ici c) := by
  intro x hx y hy hxy
  refine div_le_div_of_nonneg_right (hw.antitoneOn_Ici ?_ ?_
    (div_le_div_of_nonneg_right (by linarith) hη.le)) hη.le
  · exact div_nonneg (by linarith [show c ≤ x from hx]) hη.le
  · exact div_nonneg (by linarith [show c ≤ y from hy]) hη.le

/-- `F₁` has the density `f₁`. -/
theorem F1_eq_withDensity {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    F1 p c η (wLaw w) = volume.withDensity fun x => ENNReal.ofReal (f1 w p c η x) := by
  ext S hS
  have e : ∀ x, ENNReal.ofReal (f1 w p c η x) = ENNReal.ofReal p * ENNReal.ofReal (wη w η (x - c))
      + ENNReal.ofReal (1 - p) * (Icc (0 : ℝ) 1).indicator 1 x := by
    intro x
    have hi : (0 : ℝ) ≤ (Icc (0 : ℝ) 1).indicator (fun _ => 1) x :=
      indicator_nonneg (fun _ _ => zero_le_one) x
    rw [f1, ENNReal.ofReal_add (mul_nonneg (by linarith) hi) (mul_nonneg hp0 (wη_nonneg hw hη _)),
      ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul hp0, add_comm]
    congr 2
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  rw [F1, mix_apply, peak_eq_withDensity hw hη c, withDensity_apply _ hS, withDensity_apply _ hS,
    unifI01, Measure.restrict_apply hS]
  simp_rw [e]
  have hm : Measurable fun x => ENNReal.ofReal (wη w η (x - c)) :=
    ENNReal.measurable_ofReal.comp ((measurable_wη hw).comp (measurable_id.sub_const c))
  rw [lintegral_add_left (hm.const_mul _), lintegral_const_mul _ hm,
    lintegral_const_mul _ ((measurable_one.indicator measurableSet_Icc)),
    lintegral_indicator_one measurableSet_Icc, Measure.restrict_apply measurableSet_Icc, inter_comm]

/-- `f₁` is unimodal with mode `c`, for `0 ≤ c ≤ 1`. -/
theorem f1_unimodal {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    MonotoneOn (f1 w p c η) (Iic c) ∧ AntitoneOn (f1 w p c η) (Ici c) := by
  have hi : ∀ x, (0 : ℝ) ≤ (Icc (0 : ℝ) 1).indicator (fun _ => 1) x :=
    indicator_nonneg (fun _ _ => zero_le_one)
  constructor
  · intro x hx y hy hxy
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by linarith))
      (mul_le_mul_of_nonneg_left (wη_monotoneOn hw hη hx hy hxy) hp0)
    by_cases hx0 : x ∈ Icc (0 : ℝ) 1
    · have hy0 : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx0.1], by linarith [show y ≤ c from hy]⟩
      rw [indicator_of_mem hx0, indicator_of_mem hy0]
    · rw [indicator_of_notMem hx0]; exact hi y
  · intro x hx y hy hxy
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by linarith))
      (mul_le_mul_of_nonneg_left (wη_antitoneOn hw hη hx hy hxy) hp0)
    by_cases hy0 : y ∈ Icc (0 : ℝ) 1
    · have hx0 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [show c ≤ x from hx], by linarith [hy0.2]⟩
      rw [indicator_of_mem hx0, indicator_of_mem hy0]
    · rw [indicator_of_notMem hy0]; exact hi x

/-- `f₁` is bounded, at least `q` on `[0,1]` and `0` outside `[0,1]` (when `η ≤ c ≤ 1 - η`). -/
theorem f1_bounds {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : η ≤ c) (hc1 : c + η ≤ 1) :
    (∀ x, f1 w p c η x ≤ (1 - p) + p * (w 0 / η)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, 1 - p ≤ f1 w p c η x) ∧ (∀ x ∉ Icc (0 : ℝ) 1, f1 w p c η x = 0) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have : (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
      by_cases h : x ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h]; exact zero_le_one
    exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left (wη_le hw hη _) hp0)
  · rw [f1, indicator_of_mem hx, mul_one]
    have := mul_nonneg hp0 (wη_nonneg hw hη (x - c)); linarith
  · rw [f1, indicator_of_notMem hx, mul_zero, zero_add, wη_eq_zero hw hη, mul_zero]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

omit hw hη in
lemma uη_eq (y : ℝ) :
    uη w η y = ∫ s, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (y - s) * wη w η s := by
  rw [uη, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_sub_left_eq_self _ volume y]
  simp only [sub_sub_cancel]

lemma integrable_uη_integrand (y : ℝ) :
    Integrable (fun s => (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (y - s) * wη w η s) := by
  refine (integrable_wη hw hη).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact (((measurable_const.indicator measurableSet_Icc).comp
      (measurable_const.sub measurable_id)).mul (measurable_wη hw)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wη_nonneg hw hη s)]
    by_cases h : y - s ∈ Icc (0 : ℝ) 1
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h, wη_nonneg hw hη s]

lemma uη_nonneg (y : ℝ) : 0 ≤ uη w η y := by
  rw [uη_eq]
  exact integral_nonneg fun s =>
    mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (wη_nonneg hw hη s)

lemma uη_monotoneOn {c : ℝ} (hc : c + η ≤ 1) : MonotoneOn (uη w η) (Iic c) := by
  intro x hx y hy hxy
  rw [uη_eq, uη_eq]
  refine integral_mono (integrable_uη_integrand hw hη x) (integrable_uη_integrand hw hη y)
    fun s => ?_
  by_cases hs : η < |s|
  · simp [wη_eq_zero hw hη hs]
  rw [not_lt, abs_le] at hs
  by_cases h : x - s ∈ Icc (0 : ℝ) 1
  · have h' : y - s ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [h.1], by linarith [show y ≤ c from hy, hs.1]⟩
    rw [indicator_of_mem h, indicator_of_mem h']
  · rw [indicator_of_notMem h, zero_mul]
    exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (wη_nonneg hw hη s)

lemma uη_antitoneOn {c : ℝ} (hc : η ≤ c) : AntitoneOn (uη w η) (Ici c) := by
  intro x hx y hy hxy
  rw [uη_eq, uη_eq]
  refine integral_mono (integrable_uη_integrand hw hη y) (integrable_uη_integrand hw hη x)
    fun s => ?_
  by_cases hs : η < |s|
  · simp [wη_eq_zero hw hη hs]
  rw [not_lt, abs_le] at hs
  by_cases h : y - s ∈ Icc (0 : ℝ) 1
  · have h' : x - s ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [show c ≤ x from hx, hs.2], by linarith [h.2]⟩
    rw [indicator_of_mem h, indicator_of_mem h']
  · rw [indicator_of_notMem h, zero_mul]
    exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (wη_nonneg hw hη s)

/-- `f₂` is unimodal with mode `c`, for `η ≤ c ≤ 1 - η`. -/
theorem f2_unimodal {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : η ≤ c) (hc1 : c + η ≤ 1) :
    MonotoneOn (f2 w p c η) (Iic c) ∧ AntitoneOn (f2 w p c η) (Ici c) := by
  constructor
  · intro x hx y hy hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (wη_monotoneOn hw hη hx hy hxy) hp0)
      (mul_le_mul_of_nonneg_left (uη_monotoneOn hw hη hc1 hx hy hxy) (by linarith))
  · intro x hx y hy hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (wη_antitoneOn hw hη hx hy hxy) hp0)
      (mul_le_mul_of_nonneg_left (uη_antitoneOn hw hη hc0 hx hy hxy) (by linarith))

/-- `f₂` is `C^k` if `w` is (`k = ⊤`: `C^∞`). -/
theorem f2_contDiff {p c : ℝ} {k : ℕ∞} (hwk : ContDiff ℝ k w) : ContDiff ℝ k (f2 w p c η) := by
  have h1 : ContDiff ℝ k (wη w η) := (hwk.comp (contDiff_id.div_const η)).div_const η
  have hcs : HasCompactSupport (wη w η) :=
    HasCompactSupport.intro (isCompact_Icc (a := -η) (b := η)) fun x hx => by
      rw [mem_Icc, ← abs_le, not_le] at hx; exact wη_eq_zero hw hη hx
  have hli : LocallyIntegrable ((Icc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume :=
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp))).locallyIntegrable
  have h2 : ContDiff ℝ k (uη w η) := hcs.contDiff_convolution_right _ hli h1
  exact ((h1.comp (contDiff_id.sub contDiff_const)).const_smul p).add (h2.const_smul (1 - p))

/-- `F₂`, the law of `X₀ + ηW`, has the density `f₂`. -/
theorem F2_eq_withDensity {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    F2 p c η (wLaw w) = volume.withDensity fun x => ENNReal.ofReal (f2 w p c η x) := by
  have := hw.isProb
  have : IsProbabilityMeasure (F0 p c) := mix_isProb hp0 hp1
  ext S hS
  have hm : Measurable fun x => ENNReal.ofReal (wη w η (x - c)) :=
    ENNReal.measurable_ofReal.comp ((measurable_wη hw).comp (measurable_id.sub_const c))
  -- the right-hand side
  have e : ∀ x, ENNReal.ofReal (f2 w p c η x) = ENNReal.ofReal p * ENNReal.ofReal (wη w η (x - c))
      + ENNReal.ofReal (1 - p) * ENNReal.ofReal (uη w η x) := by
    intro x
    rw [f2, ENNReal.ofReal_add (mul_nonneg hp0 (wη_nonneg hw hη _))
      (mul_nonneg (by linarith) (uη_nonneg hw hη x)), ENNReal.ofReal_mul hp0,
      ENNReal.ofReal_mul (by linarith)]
  rw [withDensity_apply _ hS]
  simp_rw [e]
  rw [lintegral_add_left (hm.const_mul _), lintegral_const_mul _ hm]
  -- the left-hand side
  rw [F2_apply hS]
  have e2 : ∀ v : ℝ, F0 p c {x | x + η * v ∈ S} = ENNReal.ofReal p *
      {v : ℝ | c + η * v ∈ S}.indicator 1 v + ENNReal.ofReal (1 - p) *
      unifI 0 1 {x | x + η * v ∈ S} := by
    intro v
    rw [F0, mix_apply, Measure.dirac_apply]
    by_cases hv : c + η * v ∈ S
    · rw [indicator_of_mem (show c ∈ {x | x + η * v ∈ S} from hv),
        indicator_of_mem (show v ∈ {v : ℝ | c + η * v ∈ S} from hv)]
      simp only [Pi.one_apply]
    · rw [indicator_of_notMem (show c ∉ {x | x + η * v ∈ S} from hv),
        indicator_of_notMem (show v ∉ {v : ℝ | c + η * v ∈ S} from hv)]
  simp_rw [e2]
  have hmeas1 : MeasurableSet {v : ℝ | c + η * v ∈ S} := hS.preimage (by fun_prop)
  rw [lintegral_add_left ((measurable_one.indicator hmeas1).const_mul _),
    lintegral_const_mul _ (measurable_one.indicator hmeas1), lintegral_indicator_one hmeas1]
  have hA : wLaw w {v : ℝ | c + η * v ∈ S} = ∫⁻ y in S, ENNReal.ofReal (wη w η (y - c)) := by
    rw [← withDensity_apply _ hS, ← peak_eq_withDensity hw hη c,
      Measure.map_apply (by fun_prop) hS]
    rfl
  have hB : ∫⁻ v, unifI 0 1 {x | x + η * v ∈ S} ∂wLaw w =
      ∫⁻ y in S, ENNReal.ofReal (uη w η y) := by
    -- Tonelli on `U[0,1] ⊗ W`
    set T : Set (ℝ × ℝ) := {z | z.1 + η * z.2 ∈ S}
    have hT : MeasurableSet T := hS.preimage (by fun_prop)
    have h1 : ∫⁻ v, unifI 0 1 {x | x + η * v ∈ S} ∂wLaw w = ((unifI 0 1).prod (wLaw w)) T := by
      rw [Measure.prod_apply_symm hT]; rfl
    rw [h1, Measure.prod_apply hT, unifI01]
    have h2 : ∀ x, wLaw w (Prod.mk x ⁻¹' T) =
        ∫⁻ y in S, ENNReal.ofReal (wη w η (y - x)) := by
      intro x
      rw [← withDensity_apply _ hS, ← peak_eq_withDensity hw hη x,
        Measure.map_apply (by fun_prop) hS]
      rfl
    simp_rw [h2]
    have hmeas : Measurable (Function.uncurry fun x y : ℝ => ENNReal.ofReal (wη w η (y - x))) := by
      simp only [Function.uncurry_def]
      exact ENNReal.measurable_ofReal.comp ((measurable_wη hw).comp (by fun_prop))
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    refine setLIntegral_congr_fun hS fun y _ => ?_
    rw [uη, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    have e3 : (fun t => (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t * wη w η (y - t)) =
        (Icc (0 : ℝ) 1).indicator fun t => wη w η (y - t) := by
      ext t
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    rw [e3, integral_indicator measurableSet_Icc, ofReal_integral_eq_lintegral_ofReal
      ((integrable_wη hw hη).comp_sub_left y).integrableOn
      (Filter.Eventually.of_forall fun t => wη_nonneg hw hη _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    hA, hB]

end Densities

/-! ## Theorem `nc:thm:unimodal` -/

section Theorem

variable {n : ℕ} {p β η : ℝ} {w : ℝ → ℝ}

lemma Params.η_le_c (h : Params n p β η) : η ≤ 1 / 2 - β := by linarith [h.η_lt3, h.c_pos]

lemma Params.c_add_η (h : Params n p β η) : (1 / 2 - β) + η ≤ 1 := by
  linarith [h.η_lt3, h.β_pos]

/-- **Theorem `nc:thm:unimodal`.** Let `n ≥ 3`, `1 - 2/n < p < 1`, `q = 1 - p`,
`0 < β ≤ (n/2 - √(n-1))/(np)`, `c = 1/2 - β`, `0 < η < min(qβ, (p-1+2/n)/(2(n-1)q), c/2)`, and
let `w` be a probability density on `[-1,1]`, even and non-increasing on `[0,1]`. Then:
`F₁` and `F₂` (the law of `X₀ + ηW`) have the densities `f₁` and `f₂`, which are unimodal with
mode `c`; `F₁` and `F₂` are not symmetric about any point, have the mean `μ = pc + q/2`, satisfy
relation (nc:eq:cx) (stop-loss form) and are not `n`-completely mixable; `f₁` is bounded, at least
`q` on `[0,1]` and zero outside `[0,1]`; and `f₂` is `C^k` whenever `w` is (`k = ⊤`: `C^∞`).
The norm inequalities are `thm_unimodal_norm`, the bound on missing the sum `miss_bound_F1/F2`. -/
theorem thm_unimodal (h : Params n p β η) (hw : IsBump w) :
    F1 p (1 / 2 - β) η (wLaw w) =
        volume.withDensity (fun x => ENNReal.ofReal (f1 w p (1 / 2 - β) η x)) ∧
      F2 p (1 / 2 - β) η (wLaw w) =
        volume.withDensity (fun x => ENNReal.ofReal (f2 w p (1 / 2 - β) η x)) ∧
      (MonotoneOn (f1 w p (1 / 2 - β) η) (Iic (1 / 2 - β)) ∧
        AntitoneOn (f1 w p (1 / 2 - β) η) (Ici (1 / 2 - β))) ∧
      (MonotoneOn (f2 w p (1 / 2 - β) η) (Iic (1 / 2 - β)) ∧
        AntitoneOn (f2 w p (1 / 2 - β) η) (Ici (1 / 2 - β))) ∧
      (∀ a, (F1 p (1 / 2 - β) η (wLaw w)).map (fun x => a - x) ≠ F1 p (1 / 2 - β) η (wLaw w)) ∧
      (∀ a, (F2 p (1 / 2 - β) η (wLaw w)).map (fun x => a - x) ≠ F2 p (1 / 2 - β) η (wLaw w)) ∧
      mean (F1 p (1 / 2 - β) η (wLaw w)) = p * (1 / 2 - β) + (1 - p) / 2 ∧
      mean (F2 p (1 / 2 - β) η (wLaw w)) = p * (1 / 2 - β) + (1 - p) / 2 ∧
      CxCondSL n (F1 p (1 / 2 - β) η (wLaw w)) ∧ CxCondSL n (F2 p (1 / 2 - β) η (wLaw w)) ∧
      ¬ CompletelyMixable n (F1 p (1 / 2 - β) η (wLaw w)) ∧
      ¬ CompletelyMixable n (F2 p (1 / 2 - β) η (wLaw w)) ∧
      (∀ x, f1 w p (1 / 2 - β) η x ≤ (1 - p) + p * (w 0 / η)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, 1 - p ≤ f1 w p (1 / 2 - β) η x) ∧
      (∀ x ∉ Icc (0 : ℝ) 1, f1 w p (1 / 2 - β) η x = 0) ∧
      (∀ k : ℕ∞, ContDiff ℝ k w → ContDiff ℝ k (f2 w p (1 / 2 - β) η)) := by
  have := hw.isProb
  have hν := hw.symm
  have hs := hw.ae_Icc
  have hη := h.η_pos
  have hb := f1_bounds hw hη h.p_pos.le h.p_hi.le h.η_le_c h.c_add_η
  exact ⟨F1_eq_withDensity hw hη h.p_pos.le h.p_hi.le, F2_eq_withDensity hw hη h.p_pos.le h.p_hi.le,
    f1_unimodal hw hη h.p_pos.le h.p_hi.le h.c_pos.le (by linarith [h.β_pos]),
    f2_unimodal hw hη h.p_pos.le h.p_hi.le h.η_le_c h.c_add_η,
    not_symm_F1 hν hs h, not_symm_F2 hν hs h, mean_F1 hν hs h.toCx, mean_F2 hν hs h.toCx,
    cxCond_F1 hν hs h.toCx, cxCond_F2 hν hs h.toCx,
    not_completelyMixable_F1 hν hs h, not_completelyMixable_F2 hν hs h,
    hb.1, hb.2.1, hb.2.2, fun k hk => f2_contDiff hw hη hk⟩

/-- Relation (nc:eq:cx) with the convex order by all convex functions, under the classical
`NormAtom.H_stoploss_cx`, for laws with the relation in stop-loss form (`F₁` and `F₂`). -/
theorem cx_F1_F2 (H1 : NormAtom.H_stoploss_cx) (h : CxParams n p β η) (hw : IsBump w) :
    NormAtom.CxCond n (F1 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) ∧
      NormAtom.CxCond n (F2 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) := by
  have := hw.isProb
  have := F1_isProb (ν := wLaw w) h
  have := F2_isProb (ν := wLaw w) h
  constructor
  · rw [← mean_F1 hw.symm hw.ae_Icc h]
    exact cxCond_of_SL H1 (F1_ae hw.ae_Icc h) (cxCond_F1 hw.symm hw.ae_Icc h)
  · rw [← mean_F2 hw.symm hw.ae_Icc h]
    exact cxCond_of_SL H1 (F2_ae hw.ae_Icc h) (cxCond_F2 hw.symm hw.ae_Icc h)

/-- The inequalities (nc:eq:norm) for all law-determined norms, for `f₁` and `f₂`, under the
classical `NormAtom.H_stoploss_cx` and the cited `NormAtom.H_shmalo26b`. -/
theorem thm_unimodal_norm (H1 : NormAtom.H_stoploss_cx) (H2 : NormAtom.H_shmalo26b)
    (h : CxParams n p β η) (hw : IsBump w) :
    NormAtom.NormIneqs n (F1 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) ∧
      NormAtom.NormIneqs n (F2 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) := by
  have := hw.isProb
  have := F1_isProb (ν := wLaw w) h
  have := F2_isProb (ν := wLaw w) h
  constructor
  · rw [← mean_F1 hw.symm hw.ae_Icc h]
    exact normIneqs_of_SL H1 H2 h.n2 (F1_ae hw.ae_Icc h) (cxCond_F1 hw.symm hw.ae_Icc h)
  · rw [← mean_F2 hw.symm hw.ae_Icc h]
    exact normIneqs_of_SL H1 H2 h.n2 (F2_ae hw.ae_Icc h) (cxCond_F2 hw.symm hw.ae_Icc h)

end Theorem

/-! ## Corollary `nc:cor:alln` -/

/-- **Hypothesis** `as:cor:three`(b) (agent AS4's `AsymThree.cor_three_b`, there proved from
`PropThree` and `H_conc_a`): a distribution on `[a,b]` with `F ≥ (3/n) U[a,b]`, `n ≥ 3`, is
`n`-completely mixable. -/
def H_as_cor_three_b : Prop :=
  ∀ (F : Measure ℝ), IsProbabilityMeasure F → ∀ {a b : ℝ}, a < b → F (Icc a b)ᶜ = 0 →
    ∀ n : ℕ, 3 ≤ n → ENNReal.ofReal (3 / n) • unifI a b ≤ F → CompletelyMixable n F

/-- A distribution that is `1`- or `2`-completely mixable is symmetric about a point. -/
lemma symm_of_completelyMixable_le_two {F : Measure ℝ} [IsProbabilityMeasure F] {n : ℕ}
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2) (hF : CompletelyMixable n F) :
    ∃ a, F.map (fun x => a - x) = F := by
  interval_cases n
  · obtain ⟨P, hprob, ⟨s, hs⟩, hm⟩ := hF
    have hF' : F = Measure.dirac s := by
      have hm0 : P.map (fun x => x 0) = F := hm 0
      rw [← hm0, Measure.map_congr (g := fun _ => s) (by
        filter_upwards [hs] with x hx; simpa using hx), Measure.map_const, measure_univ, one_smul]
    refine ⟨2 * s, ?_⟩
    rw [hF', Measure.map_dirac]; congr 1; ring
  · exact (completelyMixable_two_iff F).1 hF

/-- The assumptions of Corollary `nc:cor:alln`. -/
structure CorParams (n₀ : ℕ) (p β η : ℝ) : Prop where
  n3 : 3 ≤ n₀
  p_lo : 1 - 2 / (n₀ : ℝ) < p
  p_hi : p < 1
  β_pos : 0 < β
  β_le : β ≤ (3 / 2 - √2) / (3 * p)
  η_pos : 0 < η
  η_lt1 : η < (1 - p) * β
  η_lt2 : η < (p - 1 + 2 / (n₀ : ℝ)) / (2 * ((n₀ : ℝ) - 1) * (1 - p))
  η_lt3 : η < (1 / 2 - β) / 2

namespace CorParams

variable {n₀ : ℕ} {p β η : ℝ} (h : CorParams n₀ p β η)
include h

lemma p_gt : 1 / 3 < p := by
  have h3 : (3 : ℝ) ≤ n₀ := by exact_mod_cast h.n3
  have : 2 / (n₀ : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
  linarith [h.p_lo]

lemma pβ : p * β ≤ (3 / 2 - √2) / 3 := by
  have := h.β_le
  rw [le_div_iff₀ (by linarith [h.p_gt])] at this
  linarith

omit h in
lemma sqrt2 : 1 < √2 ∧ √2 < 3 / 2 := by
  constructor
  · have := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)
    rwa [Real.sqrt_one] at this
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma β_lt : β < 1 / 2 := by
  have := h.pβ; have := sqrt2; have := h.p_gt
  nlinarith

omit h in
/-- `√(n-1) ≤ n √2 / 3` for `n ≥ 3`. -/
lemma sqrt_le {n : ℕ} (hn : 3 ≤ n) : √((n : ℝ) - 1) ≤ n * √2 / 3 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ (n : ℝ) * √2 / 3 := by positivity
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith

lemma r_ge {n : ℕ} (hn : 3 ≤ n) : √((n : ℝ) - 1) ≤ n * (p * (1 / 2 - β) + (1 - p) / 2) := by
  have := sqrt_le hn; have := h.pβ
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (n : ℝ) * (p * β) ≤ n * ((3 / 2 - √2) / 3) := mul_le_mul_of_nonneg_left h.pβ hn'
  nlinarith

lemma toCx {n : ℕ} (hn : 3 ≤ n) : CxParams n p β η :=
  ⟨by omega, by linarith [h.p_gt], h.p_hi, h.β_pos, h.β_lt, h.η_pos, h.η_lt3, h.r_ge hn⟩

lemma toParams {n : ℕ} (hn : 3 ≤ n) (hn0 : n ≤ n₀) : Params n p β η := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0' : (n : ℝ) ≤ n₀ := by exact_mod_cast hn0
  have hq := h.p_hi
  have h2 : 2 / (n₀ : ℝ) ≤ 2 / n := div_le_div_of_nonneg_left (by norm_num) (by linarith) hn0'
  refine ⟨hn, by linarith [h.p_lo], h.p_hi, h.β_pos, ?_, h.η_pos, h.η_lt1, ?_, h.η_lt3⟩
  · have hnp : 0 < (n : ℝ) * p := mul_pos (by linarith) (by linarith [h.p_gt])
    rw [le_div_iff₀ hnp]
    have := sqrt_le hn
    have : (n : ℝ) * (p * β) ≤ n * ((3 / 2 - √2) / 3) :=
      mul_le_mul_of_nonneg_left h.pβ (by linarith)
    nlinarith
  · refine lt_of_lt_of_le h.η_lt2 ?_
    have ha : 0 ≤ p - 1 + 2 / (n₀ : ℝ) := by linarith [h.p_lo]
    have hd : 0 < 2 * ((n : ℝ) - 1) * (1 - p) := mul_pos (by linarith) (by linarith)
    calc (p - 1 + 2 / (n₀ : ℝ)) / (2 * ((n₀ : ℝ) - 1) * (1 - p))
        ≤ (p - 1 + 2 / (n₀ : ℝ)) / (2 * ((n : ℝ) - 1) * (1 - p)) :=
          div_le_div_of_nonneg_left ha hd (by nlinarith)
      _ ≤ (p - 1 + 2 / (n : ℝ)) / (2 * ((n : ℝ) - 1) * (1 - p)) :=
          div_le_div_of_nonneg_right (by linarith) hd.le

end CorParams

section Corollary

variable {n₀ : ℕ} {p β η : ℝ} {w : ℝ → ℝ}

/-- **Corollary `nc:cor:alln`.** Under the assumptions for `n₀`, the laws with the densities `f₁`
and `f₂` satisfy relation (nc:eq:cx) for every `n ≥ 3` and are not `n`-completely mixable for any
`1 ≤ n ≤ n₀`. (The norm inequalities: `cor_alln_norm`; complete mixability of `f₁` for
`n ≥ 3/q`: `cor_alln_mixable`.) -/
theorem cor_alln (h : CorParams n₀ p β η) (hw : IsBump w) :
    (∀ n, 3 ≤ n → CxCondSL n (F1 p (1 / 2 - β) η (wLaw w)) ∧
        CxCondSL n (F2 p (1 / 2 - β) η (wLaw w))) ∧
      (∀ n, 1 ≤ n → n ≤ n₀ → ¬ CompletelyMixable n (F1 p (1 / 2 - β) η (wLaw w)) ∧
        ¬ CompletelyMixable n (F2 p (1 / 2 - β) η (wLaw w))) := by
  have := hw.isProb
  have hν := hw.symm
  have hs := hw.ae_Icc
  refine ⟨fun n hn => ⟨cxCond_F1 hν hs (h.toCx hn), cxCond_F2 hν hs (h.toCx hn)⟩,
    fun n hn1 hn0 => ?_⟩
  have h0 := h.toParams h.n3 le_rfl
  rcases le_or_gt 3 n with hn3 | hn3
  · exact ⟨not_completelyMixable_F1 hν hs (h.toParams hn3 hn0),
      not_completelyMixable_F2 hν hs (h.toParams hn3 hn0)⟩
  · have := F1_isProb (ν := wLaw w) h0.toCx
    have := F2_isProb (ν := wLaw w) h0.toCx
    constructor
    · intro hF
      obtain ⟨a, ha⟩ := symm_of_completelyMixable_le_two hn1 (by omega) hF
      exact not_symm_F1 hν hs h0 a ha
    · intro hF
      obtain ⟨a, ha⟩ := symm_of_completelyMixable_le_two hn1 (by omega) hF
      exact not_symm_F2 hν hs h0 a ha

/-- Corollary `nc:cor:alln`, the norm inequalities for every `n ≥ 3`, under the classical
`NormAtom.H_stoploss_cx` and the cited `NormAtom.H_shmalo26b`. -/
theorem cor_alln_norm (H1 : NormAtom.H_stoploss_cx) (H2 : NormAtom.H_shmalo26b)
    (h : CorParams n₀ p β η) (hw : IsBump w) (n : ℕ) (hn : 3 ≤ n) :
    NormAtom.NormIneqs n (F1 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) ∧
      NormAtom.NormIneqs n (F2 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) :=
  thm_unimodal_norm H1 H2 (h.toCx hn) hw

/-- Corollary `nc:cor:alln`: `f₁` is `n`-completely mixable for every `n ≥ 3/q`, by
Corollary `as:cor:three`(b). -/
theorem cor_alln_mixable (H : H_as_cor_three_b) (h : CorParams n₀ p β η) (hw : IsBump w)
    (n : ℕ) (hn : 3 / (1 - p) ≤ n) : CompletelyMixable n (F1 p (1 / 2 - β) η (wLaw w)) := by
  have := hw.isProb
  have hc := (h.toParams h.n3 le_rfl).toCx
  have := F1_isProb (ν := wLaw w) hc
  have hq : 0 < 1 - p := by linarith [h.p_hi]
  have h3q : (3 : ℝ) < 3 / (1 - p) := by
    rw [lt_div_iff₀ hq]; nlinarith [h.p_gt]
  have hn3 : 3 ≤ n := by exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  refine H _ this zero_lt_one ?_ n hn3 ?_
  · exact ae_iff.1 (F1_ae hw.ae_Icc hc)
  · rw [Measure.le_iff]
    intro S hS
    rw [F1, mix_apply, smul_apply, smul_eq_mul]
    refine le_add_left (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
    rw [div_le_iff₀ hnpos]
    rw [div_le_iff₀ hq] at hn
    linarith

end Corollary

/-! ## Remark `nc:rem:classes` -/

/-- Remark `nc:rem:classes`, first claim: relation (nc:eq:cx) (here in stop-loss form) implies the
mean condition (eq:meancond) for a law on `[a,b]` whose support has the ends `a` and `b`. -/
theorem meanCond_of_cx {n : ℕ} (hn : 1 ≤ n) {F : Measure ℝ} [IsProbabilityMeasure F] {a b : ℝ}
    (hF : ∀ᵐ x ∂F, x ∈ Icc a b) (ha : ∀ ε > 0, 0 < F (Iio (a + ε)))
    (hb : ∀ ε > 0, 0 < F (Ioi (b - ε))) (h : CxCondSL n F) : NormAtom.MeanCond n a b (mean F) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi : Integrable (fun x : ℝ => x) F := integrable_of_Icc hF
  have hμb : mean F ≤ b := by
    have : ∫ x, x ∂F ≤ ∫ _x, b ∂F := integral_mono_ae hi (integrable_const b)
      (by filter_upwards [hF] with x hx; exact hx.2)
    simpa [mean] using this
  constructor
  · -- `b ≤ nmean F - (n-1)a`
    have key : b ≤ n * mean F - (n - 1) * a := by
      by_contra hc
      push Not at hc
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (n * mean F - (n - 1) * a + b) / 2 := ⟨_, rfl⟩
      have hsl := stopLoss_of_cxCond h t
      have hR : ∫⁻ x, ENNReal.ofReal (n * mean F - (n - 1) * x - t) ∂F = 0 := by
        rw [← lintegral_zero (μ := F)]
        refine lintegral_congr_ae ?_
        filter_upwards [hF] with x hx
        refine ENNReal.ofReal_of_nonpos ?_
        have : (n - 1) * a ≤ (n - 1) * x := mul_le_mul_of_nonneg_left hx.1 (by linarith)
        linarith
      rw [hR, nonpos_iff_eq_zero, lintegral_eq_zero_iff (by fun_prop)] at hsl
      have hpos := hb (b - t) (by linarith)
      rw [sub_sub_cancel] at hpos
      apply hpos.ne'
      refine measure_eq_zero_of_ae ?_
      filter_upwards [hsl] with x hx
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
      simp only [mem_Ioi, not_lt]; linarith
    rw [add_div' _ _ _ hn0.ne', div_le_iff₀ hn0]; nlinarith
  · -- `nmean F - (n-1)b ≤ a`
    have key : n * mean F - (n - 1) * b ≤ a := by
      by_contra hc
      push Not at hc
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (a + (n * mean F - (n - 1) * b)) / 2 := ⟨_, rfl⟩
      have ht : t < mean F := by
        have : (n - 1) * mean F ≤ (n - 1) * b := mul_le_mul_of_nonneg_left hμb (by linarith)
        linarith
      have hsl := stopLoss_of_cxCond h t
      -- the right-hand side equals `mean F - t`
      have hR : ∫⁻ x, ENNReal.ofReal (n * mean F - (n - 1) * x - t) ∂F =
          ENNReal.ofReal (mean F - t) := by
        have hint : Integrable (fun x : ℝ => n * mean F - (n - 1) * x - t) F :=
          ((integrable_const _).sub (hi.const_mul _)).sub (integrable_const t)
        rw [← ofReal_integral_eq_lintegral_ofReal hint (by
          filter_upwards [hF] with x hx
          have : (n - 1) * x ≤ (n - 1) * b := mul_le_mul_of_nonneg_left hx.2 (by linarith)
          show 0 ≤ n * mean F - (n - 1) * x - t
          linarith)]
        congr 1
        have h3 : Integrable (fun x : ℝ => (n - 1) * x) F := hi.const_mul _
        rw [integral_sub (f := fun x : ℝ => n * mean F - (n - 1) * x) (g := fun _ => t)
          ((integrable_const _).sub h3) (integrable_const t),
          integral_sub (f := fun _ => n * mean F) (g := fun x : ℝ => (n - 1) * x)
          (integrable_const _) h3, integral_const_mul ((n : ℝ) - 1) (fun x : ℝ => x), integral_const,
          integral_const]
        simp only [probReal_univ, one_smul]; rw [mean]; ring
      -- the left-hand side is larger
      have hp1 : Integrable (fun x : ℝ => max (x - t) 0) F := (hi.sub (integrable_const t)).pos_part
      have hp2 : Integrable (fun x : ℝ => max (t - x) 0) F := ((integrable_const t).sub hi).pos_part
      have hp3 : Integrable (fun x : ℝ => x - t) F := hi.sub (integrable_const t)
      have hL : ∫⁻ x, ENNReal.ofReal (x - t) ∂F = ENNReal.ofReal (∫ x, max (x - t) 0 ∂F) := by
        rw [ofReal_integral_eq_lintegral_ofReal hp1
          (Filter.Eventually.of_forall fun x => le_max_right _ _)]
        simp only [ofReal_max_zero]
      have hsplit : ∫ x, max (x - t) 0 ∂F = (mean F - t) + ∫ x, max (t - x) 0 ∂F := by
        have e : ∀ x : ℝ, max (x - t) 0 = (x - t) + max (t - x) 0 := by
          intro x; rcases le_total x t with h1 | h1
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
        simp_rw [e]
        rw [integral_add hp3 hp2, integral_sub hi (integrable_const t), integral_const]
        simp only [probReal_univ, one_smul]; rw [mean]
      have hδ : 0 < ∫ x, max (t - x) 0 ∂F := by
        rw [integral_pos_iff_support_of_nonneg (f := fun x => max (t - x) 0)
          (fun x => le_max_right _ _)
          hp2]
        have hsupp : Function.support (fun x : ℝ => max (t - x) 0) = Iio t := by
          ext x; simp only [Function.mem_support, mem_Iio, ne_eq]
          constructor
          · intro hx; by_contra h'; push Not at h'; exact hx (max_eq_right (by linarith))
          · intro hx h'; rw [max_eq_left (by linarith)] at h'; linarith
        rw [hsupp]
        have := ha (t - a) (by linarith)
        rwa [add_sub_cancel] at this
      rw [hL, hR, hsplit, ENNReal.ofReal_le_ofReal_iff (by linarith)] at hsl
      linarith
    have : (b - a) / n ≤ b - mean F := by rw [div_le_iff₀ hn0]; nlinarith
    linarith

/-- The uniform density `w = 1/2` on `[-1,1]`. -/
def bumpUnif (x : ℝ) : ℝ := (Icc (-1 : ℝ) 1).indicator (fun _ => 1 / 2) x

lemma bumpUnif_isBump : IsBump bumpUnif := by
  have hmem : ∀ x : ℝ, -x ∈ Icc (-1 : ℝ) 1 ↔ x ∈ Icc (-1 : ℝ) 1 := by
    intro x; simp only [mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  refine ⟨measurable_const.indicator measurableSet_Icc, fun x => ?_, fun x hx => ?_, ?_,
    fun x => ?_, ?_⟩
  · exact indicator_nonneg (fun _ _ => by norm_num) x
  · refine indicator_of_notMem (fun h => ?_) _
    rw [mem_Icc, ← abs_le] at h; linarith
  · have : (fun x => ENNReal.ofReal (bumpUnif x)) =
        (Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / 2)) := by
      ext x; by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · simp [bumpUnif, indicator_of_mem hx]
      · simp [bumpUnif, indicator_of_notMem hx]
    rw [this, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · unfold bumpUnif
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).2 hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).1 h))]
  · intro x hx y hy _
    have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hy' : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
    simp only [bumpUnif, indicator_of_mem hx', indicator_of_mem hy', le_refl]

/-- The unnormalised smooth bump `smoothTransition (2 - 2|x|)`. -/
def bumpRaw (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * |x|)

lemma bumpRaw_contDiff {k : ℕ∞} : ContDiff ℝ k bumpRaw := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hev : ∀ᶠ y in nhds (0 : ℝ), |y| < 1 / 2 :=
      (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
    refine contDiffAt_const (c := (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    exact Real.smoothTransition.one_of_one_le (by linarith)
  · exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_abs hx)))

/-- There is a `C^∞` density `w` with the properties of Theorem `nc:thm:unimodal`. -/
theorem exists_smooth_bump : ∃ w : ℝ → ℝ, IsBump w ∧ ∀ k : ℕ∞, ContDiff ℝ k w := by
  have hcont : Continuous bumpRaw := bumpRaw_contDiff (k := 0).continuous
  have hm : Measurable bumpRaw := hcont.measurable
  have h0 : ∀ x, 0 ≤ bumpRaw x := fun x => Real.smoothTransition.nonneg _
  have hsupp : ∀ x, 1 < |x| → bumpRaw x = 0 := fun x hx =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  set C := ∫⁻ x, ENNReal.ofReal (bumpRaw x) with hC
  have hCtop : C ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ x, (Icc (-1 : ℝ) 1).indicator (fun _ => 1) x) ?_
      (lintegral_mono fun x => ?_)
    · rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]; simp
    · by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hx, ENNReal.ofReal_le_one]; exact Real.smoothTransition.le_one _
      · rw [hsupp x (by rw [mem_Icc, ← abs_le, not_le] at hx; exact hx), ENNReal.ofReal_zero]
        exact bot_le
  have hC0 : C ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (lintegral_mono (f := (Icc (-1 / 2 : ℝ) (1 / 2)).indicator
      (fun _ => 1)) fun x => ?_)).ne'
    · rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]; norm_num
    · by_cases hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)
      · rw [indicator_of_mem hx, bumpRaw, Real.smoothTransition.one_of_one_le, ENNReal.ofReal_one]
        have := abs_le.2 ⟨by linarith [hx.1], hx.2⟩; linarith
      · rw [indicator_of_notMem hx]; exact bot_le
  set Cr := C.toReal
  have hCr : 0 < Cr := ENNReal.toReal_pos hC0 hCtop
  refine ⟨fun x => bumpRaw x / Cr, ⟨hm.div_const _, fun x => div_nonneg (h0 x) hCr.le,
    fun x hx => by rw [hsupp x hx, zero_div], ?_, fun x => by simp [bumpRaw, abs_neg], ?_⟩,
    fun k => bumpRaw_contDiff.div_const _⟩
  · simp_rw [div_eq_mul_inv]
    rw [show (fun x => ENNReal.ofReal (bumpRaw x * Cr⁻¹)) =
        fun x => ENNReal.ofReal (bumpRaw x) * ENNReal.ofReal Cr⁻¹ from
      funext fun x => ENNReal.ofReal_mul (h0 x), lintegral_mul_const _ (by fun_prop), ← hC,
      ENNReal.ofReal_inv_of_pos hCr, ENNReal.ofReal_toReal hCtop]
    exact ENNReal.mul_inv_cancel hC0 hCtop
  · intro x hx y hy hxy
    refine div_le_div_of_nonneg_right (Real.smoothTransition.monotone ?_) hCr.le
    rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]; linarith

/-- For every `n₀ ≥ 3` there are parameters satisfying the assumptions of Corollary
`nc:cor:alln`: `p = 1 - 1/n₀`, `β = (3/2 - √2)/(3p)` and `η` half the minimum of the bounds. -/
theorem exists_corParams {n₀ : ℕ} (hn₀ : 3 ≤ n₀) : ∃ p β η : ℝ, CorParams n₀ p β η := by
  have hn : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  set p : ℝ := 1 - 1 / n₀
  have hinv : 0 < 1 / (n₀ : ℝ) := by positivity
  have hinv3 : 1 / (n₀ : ℝ) ≤ 1 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  have hp : 2 / 3 ≤ p := by simp only [p]; linarith
  have hs := CorParams.sqrt2
  set β := (3 / 2 - √2) / (3 * p)
  have hβ0 : 0 < β := div_pos (by linarith) (by linarith)
  have hβ1 : β < 1 / 2 := by rw [div_lt_iff₀ (by linarith)]; nlinarith
  set m := min (min ((1 - p) * β) ((p - 1 + 2 / (n₀ : ℝ)) / (2 * ((n₀ : ℝ) - 1) * (1 - p))))
    ((1 / 2 - β) / 2)
  have hq : 1 - p = 1 / n₀ := by simp only [p]; ring
  have hm : 0 < m := by
    refine lt_min (lt_min (by rw [hq]; positivity) (div_pos ?_ ?_)) (by linarith)
    · have : 2 / (n₀ : ℝ) = 2 * (1 / n₀) := by ring
      rw [this]; linarith
    · rw [hq]; exact mul_pos (mul_pos two_pos (by linarith)) hinv
  refine ⟨p, β, m / 2, hn₀, ?_, by linarith, hβ0, le_rfl, by linarith, ?_, ?_, ?_⟩
  · have : 2 / (n₀ : ℝ) = 2 * (1 / n₀) := by ring
    simp only [p]; linarith
  · exact (half_lt_self hm).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  · exact (half_lt_self hm).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  · exact (half_lt_self hm).trans_le (min_le_right _ _)

/-- For every `n ≥ 3` the assumptions of Theorem `nc:thm:unimodal` can be met. -/
theorem exists_params {n : ℕ} (hn : 3 ≤ n) : ∃ p β η : ℝ, Params n p β η := by
  obtain ⟨p, β, η, h⟩ := exists_corParams hn
  exact ⟨p, β, η, h.toParams hn le_rfl⟩

/-- Remark `nc:rem:classes`, second claim: for every `n ≥ 3` there is a unimodal, non-symmetric
density bounded away from zero on its support `[0,1]` (`f₁` with `w = 1/2` on `[-1,1]`) and one
that is `C^∞` (`f₂` with a smooth `w`), both satisfying relation (nc:eq:cx) and not
`n`-completely mixable. -/
theorem rem_classes {n : ℕ} (hn : 3 ≤ n) :
    (∃ (f : ℝ → ℝ) (c q : ℝ), 0 < q ∧
        MonotoneOn f (Iic c) ∧ AntitoneOn f (Ici c) ∧ (∀ x ∈ Icc (0 : ℝ) 1, q ≤ f x) ∧
        (∀ x ∉ Icc (0 : ℝ) 1, f x = 0) ∧
        IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
        (∀ a, (volume.withDensity fun x => ENNReal.ofReal (f x)).map (fun x => a - x) ≠
          volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
        CxCondSL n (volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
        ¬ CompletelyMixable n (volume.withDensity fun x => ENNReal.ofReal (f x))) ∧
    (∃ (f : ℝ → ℝ) (c : ℝ), (∀ k : ℕ∞, ContDiff ℝ k f) ∧
        MonotoneOn f (Iic c) ∧ AntitoneOn f (Ici c) ∧
        IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
        (∀ a, (volume.withDensity fun x => ENNReal.ofReal (f x)).map (fun x => a - x) ≠
          volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
        CxCondSL n (volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
        ¬ CompletelyMixable n (volume.withDensity fun x => ENNReal.ofReal (f x))) := by
  obtain ⟨p, β, η, h⟩ := exists_params hn
  obtain ⟨w, hw, hwk⟩ := exists_smooth_bump
  have T1 := thm_unimodal h bumpUnif_isBump
  have T2 := thm_unimodal h hw
  have := bumpUnif_isBump.isProb
  have := hw.isProb
  constructor
  · refine ⟨f1 bumpUnif p (1 / 2 - β) η, 1 / 2 - β, 1 - p, h.q_pos, T1.2.2.1.1, T1.2.2.1.2,
      T1.2.2.2.2.2.2.2.2.2.2.2.2.2.1, T1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_⟩ <;>
      rw [← T1.1]
    · exact F1_isProb h.toCx
    · exact T1.2.2.2.2.1
    · exact T1.2.2.2.2.2.2.2.2.1
    · exact T1.2.2.2.2.2.2.2.2.2.2.1
  · refine ⟨f2 w p (1 / 2 - β) η, 1 / 2 - β, fun k => T2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k (hwk k),
      T2.2.2.2.1.1, T2.2.2.2.1.2, ?_, ?_, ?_, ?_⟩ <;> rw [← T2.2.1]
    · exact F2_isProb h.toCx
    · exact T2.2.2.2.2.2.1
    · exact T2.2.2.2.2.2.2.2.2.2.1
    · exact T2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Hypothesis** `as:cor:three`(a) (agent AS4's `AsymThree.cor_three_a`, there proved from
`PropThree` and `H_conc_a`). -/
def H_as_cor_three_a : Prop :=
  ∀ (F : Measure ℝ), IsProbabilityMeasure F → ∀ R : ℝ, (∃ a, F (Icc a (a + R))ᶜ = 0) →
    ∀ c H q : ℝ, 0 < H → 0 < q → q ≤ 1 → ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F →
      ∀ n : ℕ, 4 ≤ ⌊q * n⌋₊ → R / H ≤ ⌊q * n⌋₊ → CompletelyMixable n F

/-- Remark `nc:rem:classes`, the explicit threshold for unimodal densities (stated after
Corollary `nc:cor:alln`): a unimodal density `f` on `[a,b]` is `n`-completely mixable as soon as
`⌊n(y-x) min(f(x), f(y))⌋ ≥ max(4, 2(b-a)/(y-x))` for two points `x < y`. -/
theorem threshold_unimodal (H : H_as_cor_three_a) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {a b m : ℝ}
    (hF : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)))
    (hsupp : (volume.withDensity fun x => ENNReal.ofReal (f x)) (Icc a b)ᶜ = 0)
    (hmono : MonotoneOn f (Iic m)) (hanti : AntitoneOn f (Ici m)) {x y : ℝ} (hxy : x < y)
    (n : ℕ) (h4 : 4 ≤ ⌊(y - x) * min (f x) (f y) * n⌋₊)
    (hR : 2 * (b - a) / (y - x) ≤ ⌊(y - x) * min (f x) (f y) * n⌋₊) :
    CompletelyMixable n (volume.withDensity fun x => ENNReal.ofReal (f x)) := by
  set F := volume.withDensity fun x => ENNReal.ofReal (f x)
  set q := (y - x) * min (f x) (f y)
  have hyx : 0 < y - x := by linarith
  have hqn : 0 < q * n := by
    by_contra hc; push Not at hc; rw [Nat.floor_of_nonpos hc] at h4; omega
  have hq0 : 0 < q := by
    by_contra hc; push Not at hc
    have : q * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg n)
    linarith
  have hmin0 : 0 ≤ min (f x) (f y) := le_min (hf0 x) (hf0 y)
  -- `F ≥ q U[x, y]`
  have hU : ENNReal.ofReal q • unifI x y ≤ F := by
    rw [Measure.le_iff]
    intro S hS
    simp only [unifI, hxy, ↓reduceIte]
    rw [smul_apply, smul_eq_mul, smul_apply, smul_eq_mul,
      Measure.restrict_apply hS, ← mul_assoc]
    have e : ENNReal.ofReal q * (ENNReal.ofReal (y - x))⁻¹ = ENNReal.ofReal (min (f x) (f y)) := by
      rw [show q = (y - x) * min (f x) (f y) from rfl, ENNReal.ofReal_mul hyx.le, mul_comm,
        ← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hyx) ENNReal.ofReal_ne_top, one_mul]
    rw [e, ← setLIntegral_const, show F S = ∫⁻ z in S, ENNReal.ofReal (f z) from
      withDensity_apply _ hS]
    refine le_trans (setLIntegral_mono (ENNReal.measurable_ofReal.comp hfm) fun z hz =>
      ENNReal.ofReal_le_ofReal ?_) (lintegral_mono_set inter_subset_left)
    rcases le_total z m with hzm | hzm
    · exact (min_le_left _ _).trans (hmono (show x ≤ m by linarith [hz.2.1]) hzm hz.2.1)
    · exact (min_le_right _ _).trans (hanti hzm (show m ≤ y by linarith [hz.2.2]) hz.2.2)
  have hq1 : q ≤ 1 := by
    have := unifI_isProb x y
    have h1 := hU univ
    rw [smul_apply, smul_eq_mul, measure_univ, measure_univ, mul_one] at h1
    exact (ENNReal.ofReal_le_one).1 h1
  have hc : unifI ((x + y) / 2 - (y - x) / 2) ((x + y) / 2 + (y - x) / 2) = unifI x y := by
    congr 1 <;> ring
  refine H F hF (b - a) ⟨a, by rwa [add_sub_cancel]⟩ ((x + y) / 2) ((y - x) / 2) q
    (by linarith) hq0 hq1 (by rw [hc]; exact hU) n h4 ?_
  rw [div_div_eq_mul_div]; linarith [show (b - a) * 2 / (y - x) = 2 * (b - a) / (y - x) by ring]

/-! ## The example after Theorem `nc:thm:unimodal` -/

/-- For `n = 3` the parameters `p = 2/5`, `c = 9/20` (`β = 1/20`) and `η = 1/50` are admissible. -/
theorem example_params : Params 3 (2 / 5) (1 / 20) (1 / 50) := by
  have hs : √((3 : ℕ) - 1 : ℝ) ≤ 36 / 25 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  refine ⟨le_rfl, by norm_num, by norm_num, by norm_num, ?_, by norm_num, by norm_num, by norm_num,
    by norm_num⟩
  rw [le_div_iff₀ (by norm_num)]
  push_cast at hs ⊢
  linarith

/-- With `w = 1/2` on `[-1,1]`, the density `f₁` of the example equals `3/5` on `[0,1]` outside
`[c - η, c + η]` and `53/5 = 10.6` on `[c - η, c + η]`. -/
theorem example_values :
    (∀ x ∈ Icc (0 : ℝ) 1, x ∉ Icc (9 / 20 - 1 / 50 : ℝ) (9 / 20 + 1 / 50) →
      f1 bumpUnif (2 / 5) (9 / 20) (1 / 50) x = 3 / 5) ∧
    (∀ x ∈ Icc (9 / 20 - 1 / 50 : ℝ) (9 / 20 + 1 / 50),
      f1 bumpUnif (2 / 5) (9 / 20) (1 / 50) x = 53 / 5) := by
  constructor
  · intro x hx hxI
    have : (x - 9 / 20) / (1 / 50) ∉ Icc (-1 : ℝ) 1 := by
      intro h; apply hxI; simp only [mem_Icc] at h ⊢
      constructor <;> nlinarith [h.1, h.2]
    simp only [f1, wη, bumpUnif, indicator_of_mem hx, indicator_of_notMem this]
    norm_num
  · intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have : (x - 9 / 20) / (1 / 50) ∈ Icc (-1 : ℝ) 1 := by
      simp only [mem_Icc] at hx ⊢; constructor <;> nlinarith [hx.1, hx.2]
    simp only [f1, wη, bumpUnif, indicator_of_mem hx01, indicator_of_mem this]
    norm_num

end Mixes.NormUnimodal
