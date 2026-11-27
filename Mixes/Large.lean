import Mixes.Defs

/-!
# Large `n`: exponential tilts and maximal entropy (Sections 22 and 23)

Lemma 101 (`lemma101`), Lemma 102 (`lemma102`), Lemma 111 (`lemma111a`, `lemma111b`,
`lemma111c`), Proposition 106 (`prop106`, `prop106_kernel`, `prop106_unique`), Proposition 116
(`prop116`), Corollaries 105, 114, 115 (`cor105`, `cor114`, `cor115`) and Remark 85 /
`g:rem:asym` (`centroid_support`, `asymLE_cent`, `neg_sub_cent_mem`) of `mixes/main.tex`.

Results cited from outside and stated as explicit hypotheses: `Thm113` (statement of
Theorem 113), `Thm113Sym` (its symmetric form, from its proof), `Thm104T` (Theorem 104 with its
constants tracked), `JohnThm` (John's theorem), `FourierGapJohn` (the Fourier step of
Corollary 105: Blaschke selection and the divergence-theorem bound) and `KernelAffine` (the
kernel argument of Theorem 91 with Lemma 89).

We work in a finite-dimensional real inner product space `E` (e.g. `EuclideanSpace ℝ (Fin d)`)
whose `volume` is an additive Haar measure.

For a finite measure `μ` on `E` concentrated on a bounded set, `lap μ v = ∫ exp ⟪v, p⟫ dμ` is its
Laplace transform and `tiltMean μ v` is the mean of the exponential tilt
`e^{⟪v, ·⟫} μ / lap μ v` (`integral_tilt` identifies it with the mean of the tilted measure
`tilt μ v`). The paper's `Λ = log lap` has gradient `tiltMean`; we do not differentiate under the
integral sign, but prove directly what the paper deduces from strict convexity and coercivity:

* `sum_tiltMean_injective`: the gradient of a (finite, nonempty) sum of log-Laplace transforms of
  measures absolutely continuous with respect to a Haar measure is injective (Lemma 101,
  Lemma 102, Lemma 111(c)), by the monotonicity `(a - b)(e^a - e^b) ≥ 0`;
* `exists_sum_tiltMean_eq`, `exists_tiltMean_eq_zero`: a coercive `∑ log lap - ⟪·, T⟫` has a
  minimiser in the ball of coercivity, where `∑ tiltMean = T` (existence in Lemmas 102 and
  111(b)), by the bound `|e^x - 1 - x| ≤ x²` for `|x| ≤ 1`.

For Proposition 106 the reference measure `λ` on `𝒯_n(K)` is an arbitrary finite measure on
tuples concentrated on `Kⁿ`; the identification of `𝒯_n(K)` with a subset of `(ℝ^d)^{n-1}` is
not needed for the argument.
-/

open MeasureTheory Real RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Large

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]

/-- The Laplace transform `v ↦ ∫ exp ⟪v, p⟫ dμ(p)` of a measure `μ` on `E`. -/
def lap (μ : Measure E) (v : E) : ℝ := ∫ p, exp ⟪v, p⟫ ∂μ

/-- The mean of the exponential tilt of `μ` by `v`, i.e. of the probability measure with density
`e^{⟪v, ·⟫} / lap μ v` with respect to `μ`. -/
def tiltMean (μ : Measure E) (v : E) : E := ∫ p, (exp ⟪v, p⟫ / lap μ v) • p ∂μ

/-- The exponential tilt of `μ` by `v` as a measure. -/
def tilt (μ : Measure E) (v : E) : Measure E :=
  μ.withDensity fun p => ((Real.toNNReal (exp ⟪v, p⟫ / lap μ v) : NNReal) : ENNReal)

section Basic

variable {μ : Measure E} {R : ℝ}

lemma exp_inner_le {v p : E} (hp : ‖p‖ ≤ R) : exp ⟪v, p⟫ ≤ exp (‖v‖ * R) :=
  exp_le_exp.2 ((real_inner_le_norm v p).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg v)))

lemma integrable_exp_inner [IsFiniteMeasure μ] (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    Integrable (fun p => exp ⟪v, p⟫) μ := by
  refine Integrable.mono' (integrable_const (exp (‖v‖ * R))) ?_ ?_
  · exact (continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  · filter_upwards [hR] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_inner_le hp

lemma integrable_exp_smul [IsFiniteMeasure μ] (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) (c : E → ℝ)
    (hc : Continuous c) (C : ℝ) (hC : ∀ p, |c p| ≤ C) :
    Integrable (fun p => (c p * exp ⟪v, p⟫) • p) μ := by
  refine Integrable.mono' (integrable_const (C * exp (‖v‖ * R) * R)) ?_ ?_
  · exact ((hc.mul (continuous_exp.comp (continuous_const.inner continuous_id))).smul
      continuous_id).aestronglyMeasurable
  · filter_upwards [hR] with p hp
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    have h0 : 0 ≤ |c p| := abs_nonneg _
    have h1 : 0 ≤ C := h0.trans (hC p)
    exact mul_le_mul (mul_le_mul (hC p) (exp_inner_le hp) (exp_pos _).le h1) hp (norm_nonneg _)
      (mul_nonneg h1 (exp_pos _).le)

lemma lap_pos [IsFiniteMeasure μ] [NeZero μ] (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) : 0 < lap μ v :=
  integral_exp_pos (integrable_exp_inner hR v)

lemma tiltMean_eq [IsFiniteMeasure μ] (v : E) :
    tiltMean μ v = (lap μ v)⁻¹ • ∫ p, exp ⟪v, p⟫ • p ∂μ := by
  unfold tiltMean
  rw [← integral_smul]
  congr 1
  funext p
  rw [smul_smul, div_eq_inv_mul]

/-- `tiltMean μ v` is the mean of the tilted measure `tilt μ v`. -/
lemma integral_tilt [IsFiniteMeasure μ] [NeZero μ] (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    ∫ p, p ∂(tilt μ v) = tiltMean μ v := by
  unfold tilt tiltMean
  rw [integral_withDensity_eq_integral_smul]
  · congr 1
    funext p
    rw [NNReal.smul_def, Real.coe_toNNReal _ (div_pos (exp_pos _) (lap_pos hR v)).le]
  · exact (continuous_real_toNNReal.comp
      ((continuous_exp.comp (continuous_const.inner continuous_id)).div_const _)).measurable

/-- `tilt μ v` is a probability measure. -/
lemma tilt_isProb [IsFiniteMeasure μ] [NeZero μ] (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    IsProbabilityMeasure (tilt μ v) := by
  have hZ := lap_pos hR v
  constructor
  unfold tilt
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hm : Measurable fun p : E => exp ⟪v, p⟫ / lap μ v :=
    ((continuous_exp.comp (continuous_const.inner continuous_id)).div_const _).measurable
  have := ofReal_integral_eq_lintegral_ofReal
    ((integrable_exp_inner hR v).div_const (lap μ v))
    (Filter.Eventually.of_forall fun p => (div_pos (exp_pos _) hZ).le)
  simp only [ENNReal.ofReal] at this
  rw [← this, integral_div, show (∫ x, exp ⟪v, x⟫ ∂μ) = lap μ v from rfl, div_self hZ.ne',
    Real.toNNReal_one, ENNReal.coe_one]

end Basic

section Injective

variable {ν : Measure E} [ν.IsAddHaarMeasure]

/-- A level set `{p | ⟪c, p⟫ = κ}` with `c ≠ 0` is null for a Haar measure. -/
lemma haar_level_null {c : E} (hc : c ≠ 0) (κ : ℝ) : ν {p | ⟪c, p⟫ = κ} = 0 := by
  have hcc : ⟪c, c⟫ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hc)
  set p₀ : E := (κ / ⟪c, c⟫) • c with hp₀
  let S : AffineSubspace ℝ E := AffineSubspace.mk' p₀ (LinearMap.ker (innerₛₗ ℝ c))
  have hsub : {p | ⟪c, p⟫ = κ} ⊆ (S : Set E) := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    change p ∈ S
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, innerₛₗ_apply_apply, vsub_eq_sub,
      inner_sub_right,
      hp, hp₀, inner_smul_right, div_mul_cancel₀ _ hcc, sub_self]
  have hne : S ≠ ⊤ := by
    intro htop
    have : p₀ + c ∈ S := htop ▸ AffineSubspace.mem_top ℝ E _
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, innerₛₗ_apply_apply, vsub_eq_sub,
      add_sub_cancel_left] at this
    exact hcc this
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace ν S hne)

variable {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {R : ℝ}

/-- The integrand of the monotonicity argument. -/
private def mono (μ : Measure E) (v w p : E) : ℝ :=
  ((⟪v, p⟫ - log (lap μ v)) - (⟪w, p⟫ - log (lap μ w))) *
    (exp (⟪v, p⟫ - log (lap μ v)) - exp (⟪w, p⟫ - log (lap μ w)))

private lemma mono_nonneg (μ : Measure E) (v w p : E) : 0 ≤ mono μ v w p := by
  unfold mono
  set a := ⟪v, p⟫ - log (lap μ v)
  set b := ⟪w, p⟫ - log (lap μ w)
  rcases le_total a b with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [exp_le_exp.2 h])
  · exact mul_nonneg (by linarith) (by linarith [exp_le_exp.2 h])

private lemma mono_eq_zero {v w p : E} (h : mono μ v w p = 0) :
    ⟪v - w, p⟫ = log (lap μ v) - log (lap μ w) := by
  unfold mono at h
  rcases mul_eq_zero.1 h with h | h
  · rw [inner_sub_left]; linarith
  · have := exp_injective (sub_eq_zero.1 h)
    rw [inner_sub_left]; linarith

private lemma exp_sub_log (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v p : E) :
    exp (⟪v, p⟫ - log (lap μ v)) = exp ⟪v, p⟫ / lap μ v := by
  rw [exp_sub, exp_log (lap_pos hR v)]

private lemma mono_eq (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v w p : E) :
    mono μ v w p = ⟪v - w, (exp ⟪v, p⟫ / lap μ v) • p - (exp ⟪w, p⟫ / lap μ w) • p⟫
      - (log (lap μ v) - log (lap μ w)) * (exp ⟪v, p⟫ / lap μ v - exp ⟪w, p⟫ / lap μ w) := by
  unfold mono
  rw [exp_sub_log hR, exp_sub_log hR, inner_sub_right, inner_smul_right, inner_smul_right,
    inner_sub_left]
  ring

private lemma integrable_div (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    Integrable (fun p => exp ⟪v, p⟫ / lap μ v) μ :=
  (integrable_exp_inner hR v).div_const _

private lemma integrable_div_smul (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    Integrable (fun p => (exp ⟪v, p⟫ / lap μ v) • p) μ := by
  have := integrable_exp_smul hR v (fun _ => (lap μ v)⁻¹) continuous_const |(lap μ v)⁻¹|
    (fun _ => le_rfl)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [div_eq_inv_mul]

private lemma integral_div_one (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    ∫ p, exp ⟪v, p⟫ / lap μ v ∂μ = 1 := by
  rw [integral_div]; exact div_self (lap_pos hR v).ne'

private lemma integrable_mono (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v w : E) :
    Integrable (mono μ v w) μ := by
  have h1 := Integrable.const_inner (𝕜 := ℝ) (v - w)
    ((integrable_div_smul hR v).sub (integrable_div_smul hR w))
  have h2 := ((integrable_div hR v).sub (integrable_div hR w)).const_mul
    (log (lap μ v) - log (lap μ w))
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.sub_apply]
  rw [mono_eq hR]

private lemma integral_mono_eq (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v w : E) :
    ∫ p, mono μ v w p ∂μ = ⟪v - w, tiltMean μ v - tiltMean μ w⟫ := by
  simp_rw [mono_eq hR]
  rw [integral_sub, integral_inner, integral_sub, integral_const_mul, integral_sub,
    integral_div_one hR, integral_div_one hR]
  · simp [tiltMean]
  all_goals first
    | exact integrable_div hR _
    | exact integrable_div_smul hR _
    | exact (integrable_div_smul hR v).sub (integrable_div_smul hR w)
    | exact Integrable.const_inner (𝕜 := ℝ) _
        ((integrable_div_smul hR v).sub (integrable_div_smul hR w))
    | exact ((integrable_div hR v).sub (integrable_div hR w)).const_mul _

/-- If the monotonicity integral of one measure vanishes and the measure is absolutely
continuous with respect to a Haar measure, then `v = w`. -/
private lemma eq_of_integral_mono (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (hac : μ ≪ ν) {v w : E}
    (h : ∫ p, mono μ v w p ∂μ = 0) : v = w := by
  by_contra hvw
  have hae := (integral_eq_zero_iff_of_nonneg (mono_nonneg μ v w) (integrable_mono hR v w)).1 h
  have hlev : ∀ᵐ p ∂μ, p ∈ {p | ⟪v - w, p⟫ = log (lap μ v) - log (lap μ w)} := by
    filter_upwards [hae] with p hp
    exact mono_eq_zero hp
  have hnull : μ {p | ⟪v - w, p⟫ = log (lap μ v) - log (lap μ w)} = 0 :=
    hac (haar_level_null (ν := ν) (sub_ne_zero.2 hvw) _)
  have h3 : ∀ᵐ p ∂μ, False := by
    filter_upwards [hlev, measure_eq_zero_iff_ae_notMem.1 hnull] with p h1 h2 using h2 h1
  exact NeZero.ne μ (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 h3))

/-- **Injectivity of the gradient of a sum of log-Laplace transforms** (Lemma 101, the strict
convexity step of Lemma 102, Lemma 111(c)). If finitely many (at least one) nonzero finite
measures, each concentrated on a bounded set and absolutely continuous with respect to a Haar
measure `ν`, have `∑ᵢ tiltMean (μ i) v = ∑ᵢ tiltMean (μ i) w`, then `v = w`. -/
theorem sum_tiltMean_injective {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (μ : ι → Measure E)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NeZero (μ i)] (R : ι → ℝ)
    (hR : ∀ i, ∀ᵐ p ∂(μ i), ‖p‖ ≤ R i) (hac : ∀ i, μ i ≪ ν) {v w : E}
    (h : ∑ i ∈ s, tiltMean (μ i) v = ∑ i ∈ s, tiltMean (μ i) w) : v = w := by
  have hsum : ∑ i ∈ s, ∫ p, mono (μ i) v w p ∂(μ i) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => integral_mono_eq (hR i) v w, ← inner_sum,
      Finset.sum_sub_distrib, h, sub_self, inner_zero_right]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => integral_nonneg (mono_nonneg (μ i) v w))).1 hsum
  obtain ⟨i, hi⟩ := hs
  exact eq_of_integral_mono (hR i) (hac i) (hz i hi)

/-- Injectivity of the gradient of one log-Laplace transform. -/
theorem tiltMean_injective (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (hac : μ ≪ ν) {v w : E}
    (h : tiltMean μ v = tiltMean μ w) : v = w :=
  sum_tiltMean_injective (ι := Unit) {()} (Finset.singleton_nonempty _) (fun _ => μ)
    (fun _ => R) (fun _ => hR) (fun _ => hac) (by simpa using h)

end Injective

section Exists

variable {μ : Measure E} [IsFiniteMeasure μ] {R : ℝ}

lemma integrable_exp_smul' (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v : E) :
    Integrable (fun p => exp ⟪v, p⟫ • p) μ :=
  (integrable_exp_smul hR v (fun _ => 1) continuous_const 1 (by simp)).congr
    (Filter.Eventually.of_forall fun p => by simp)

lemma continuous_lap (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) : Continuous (lap μ) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  refine continuousAt_of_dominated (bound := fun _ => exp ((‖v₀‖ + 1) * max R 0)) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun v =>
      (continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds v₀ one_pos] with v hv
    filter_upwards [hR] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    have hv' : ‖v‖ ≤ ‖v₀‖ + 1 := by
      have h1 := norm_add_le v₀ (v - v₀)
      rw [add_sub_cancel] at h1
      linarith [mem_ball_iff_norm.1 hv]
    calc exp ⟪v, p⟫ ≤ exp (‖v‖ * max R 0) := exp_inner_le (hp.trans (le_max_left _ _))
      _ ≤ _ := exp_le_exp.2 (mul_le_mul_of_nonneg_right hv' (le_max_right _ _))
  · exact Filter.Eventually.of_forall fun p =>
      (continuous_exp.comp (continuous_id.inner continuous_const)).continuousAt

/-- Second-order upper bound for the Laplace transform along a line, from the elementary bound
`|e^x - 1 - x| ≤ x²` for `|x| ≤ 1` (replaces differentiation under the integral sign). -/
lemma lap_sub_le (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (v₀ M : E) {s : ℝ} (hs : 0 < s)
    (hs1 : s * (‖M‖ * R) ≤ 1) :
    lap μ (v₀ - s • M) ≤ lap μ v₀ - s * ⟪M, ∫ p, exp ⟪v₀, p⟫ • p ∂μ⟫
      + s ^ 2 * ‖M‖ ^ 2 * R ^ 2 * lap μ v₀ := by
  set C := s ^ 2 * ‖M‖ ^ 2 * R ^ 2
  have hpt : ∀ᵐ p ∂μ, exp ⟪v₀ - s • M, p⟫ ≤
      exp ⟪v₀, p⟫ + (-s) * ⟪M, exp ⟪v₀, p⟫ • p⟫ + C * exp ⟪v₀, p⟫ := by
    filter_upwards [hR] with p hp
    set x := -s * ⟪M, p⟫ with hx
    have hxa : |x| ≤ s * (‖M‖ * R) := by
      rw [hx, abs_mul, abs_neg, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm M p).trans
        (mul_le_mul_of_nonneg_left hp (norm_nonneg M))) hs.le
    have hx1 : |x| ≤ 1 := hxa.trans hs1
    have hx2 : x ^ 2 ≤ C := by
      have h0 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [h0]
      calc |x| ^ 2 ≤ (s * (‖M‖ * R)) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxa 2
        _ = C := by ring
    have he := abs_le.1 (Real.abs_exp_sub_one_sub_id_le hx1)
    have hsplit : exp ⟪v₀ - s • M, p⟫ = exp ⟪v₀, p⟫ * exp x := by
      rw [← exp_add, inner_sub_left, real_inner_smul_left, hx]
      ring_nf
    rw [hsplit, inner_smul_right]
    have hE := exp_pos ⟪v₀, p⟫
    have : exp x ≤ 1 + x + C := by linarith
    have h3 : exp ⟪v₀, p⟫ * exp x ≤ exp ⟪v₀, p⟫ * (1 + x + C) :=
      mul_le_mul_of_nonneg_left this hE.le
    rw [hx] at h3
    linarith
  have hiE := integrable_exp_inner hR v₀
  have hiI : Integrable (fun p => (-s) * ⟪M, exp ⟪v₀, p⟫ • p⟫) μ :=
    (Integrable.const_inner (𝕜 := ℝ) M (integrable_exp_smul' hR v₀)).const_mul _
  have hrhs : ∫ p, (exp ⟪v₀, p⟫ + (-s) * ⟪M, exp ⟪v₀, p⟫ • p⟫ + C * exp ⟪v₀, p⟫) ∂μ
      = lap μ v₀ + (-s) * ⟪M, ∫ p, exp ⟪v₀, p⟫ • p ∂μ⟫ + C * lap μ v₀ := by
    have hiEI : Integrable (fun p => exp ⟪v₀, p⟫ + (-s) * ⟪M, exp ⟪v₀, p⟫ • p⟫) μ :=
      hiE.add hiI
    rw [integral_add hiEI (hiE.const_mul C), integral_add hiE hiI, integral_const_mul,
      integral_const_mul, integral_inner (integrable_exp_smul' hR v₀)]
    rfl
  have hint : ∫ p, exp ⟪v₀ - s • M, p⟫ ∂μ ≤
      ∫ p, (exp ⟪v₀, p⟫ + (-s) * ⟪M, exp ⟪v₀, p⟫ • p⟫ + C * exp ⟪v₀, p⟫) ∂μ :=
    integral_mono_ae (integrable_exp_inner hR _) ((hiE.add hiI).add (hiE.const_mul C)) hpt
  rw [hrhs] at hint
  change lap μ (v₀ - s • M) ≤ _ at hint
  linarith

/-- The function `F(v) = ∑ᵢ log (lap (μ i) v) - ⟪v, T⟫` whose minimiser gives the tilt with
`∑ᵢ tiltMean (μ i) v = T`. -/
def sumLogLap {ι : Type*} (s : Finset ι) (μ : ι → Measure E) (T v : E) : ℝ :=
  ∑ i ∈ s, log (lap (μ i) v) - ⟪v, T⟫

variable {ι : Type*} (s : Finset ι) (μs : ι → Measure E) [∀ i, IsFiniteMeasure (μs i)]
  [∀ i, NeZero (μs i)] (Rs : ι → ℝ) (hRs : ∀ i, ∀ᵐ p ∂(μs i), ‖p‖ ≤ Rs i) (T : E)

include hRs in
lemma continuous_sumLogLap : Continuous (sumLogLap s μs T) := by
  unfold sumLogLap
  refine Continuous.sub (continuous_finsetSum _ fun i _ => ?_)
    (continuous_id.inner continuous_const)
  exact (continuous_lap (hRs i)).log fun v => (lap_pos (hRs i) v).ne'

include hRs in
/-- First-order condition at a minimiser of `sumLogLap`. -/
lemma firstOrder_sum {v₀ : E} (hmin : ∀ v, sumLogLap s μs T v₀ ≤ sumLogLap s μs T v) :
    ∑ i ∈ s, tiltMean (μs i) v₀ = T := by
  set M := ∑ i ∈ s, tiltMean (μs i) v₀ - T with hM
  set R' : ι → ℝ := fun i => max (Rs i) 0
  have hR' : ∀ i, ∀ᵐ p ∂(μs i), ‖p‖ ≤ R' i := fun i =>
    (hRs i).mono fun p hp => hp.trans (le_max_left _ _)
  have hR0 : ∀ i, 0 ≤ R' i := fun i => le_max_right _ _
  set SR := ∑ i ∈ s, R' i
  set S2 := ∑ i ∈ s, R' i ^ 2
  have hSR : 0 ≤ SR := Finset.sum_nonneg fun i _ => hR0 i
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hden : 0 < ‖M‖ * SR + S2 + 1 := by positivity
  set t := 1 / (‖M‖ * SR + S2 + 1) with htdef
  have ht : 0 < t := by positivity
  have ht2 : t * S2 < 1 := by
    rw [htdef, one_div, inv_mul_eq_div, div_lt_one hden]
    nlinarith [norm_nonneg M]
  -- the bound for each measure
  have hbound : ∀ i ∈ s, log (lap (μs i) (v₀ - t • M)) - log (lap (μs i) v₀) ≤
      -t * ⟪M, tiltMean (μs i) v₀⟫ + t ^ 2 * ‖M‖ ^ 2 * R' i ^ 2 := by
    intro i hi
    have hRi : R' i ≤ SR := Finset.single_le_sum (fun j _ => hR0 j) hi
    have ht1 : t * (‖M‖ * R' i) ≤ 1 := by
      rw [htdef, one_div, inv_mul_eq_div, div_le_one hden]
      nlinarith [norm_nonneg M, mul_le_mul_of_nonneg_left hRi (norm_nonneg M)]
    have hZ := lap_pos (hR' i) v₀
    have h1 := lap_sub_le (hR' i) v₀ M ht ht1
    have hmean : ∫ p, exp ⟪v₀, p⟫ • p ∂(μs i) = lap (μs i) v₀ • tiltMean (μs i) v₀ := by
      rw [tiltMean_eq, smul_smul, mul_inv_cancel₀ hZ.ne', one_smul]
    rw [hmean, inner_smul_right] at h1
    have hpos := lap_pos (hR' i) (v₀ - t • M)
    rw [← log_div hpos.ne' hZ.ne']
    refine (log_le_sub_one_of_pos (div_pos hpos hZ)).trans ?_
    rw [div_sub_one hZ.ne', div_le_iff₀ hZ]
    nlinarith
  have hsum := Finset.sum_le_sum hbound
  have hmin' := hmin (v₀ - t • M)
  unfold sumLogLap at hmin'
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← inner_sum] at hsum
  have hTM : ⟪M, ∑ i ∈ s, tiltMean (μs i) v₀⟫ = ‖M‖ ^ 2 + ⟪M, T⟫ := by
    have hMT : ∑ i ∈ s, tiltMean (μs i) v₀ = M + T := by rw [hM, sub_add_cancel]
    rw [hMT, inner_add_right, real_inner_self_eq_norm_sq]
  rw [hTM] at hsum
  have hlin : ⟪v₀ - t • M, T⟫ = ⟪v₀, T⟫ - t * ⟪M, T⟫ := by
    rw [inner_sub_left, real_inner_smul_left]
  rw [hlin] at hmin'
  have key : 0 ≤ -t * ‖M‖ ^ 2 + t ^ 2 * ‖M‖ ^ 2 * S2 := by nlinarith
  have hpos : 0 < t * (1 - t * S2) := mul_pos ht (by linarith)
  have : ‖M‖ ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc hpos
    nlinarith
  have hM0 : M = 0 := norm_eq_zero.1 (pow_eq_zero_iff (n := 2) two_ne_zero |>.1
    (le_antisymm this (sq_nonneg _)))
  rw [hM] at hM0
  exact sub_eq_zero.1 hM0

include hRs in
/-- **Existence of the common tilt** (Lemma 111(b), and Lemma 102 for one measure): if
`F(v) = ∑ᵢ log (lap (μ i) v) - ⟪v, T⟫` exceeds `F(0)` outside the ball of radius `V`, there is
`v` with `‖v‖ ≤ V` and `∑ᵢ tiltMean (μ i) v = T`. -/
theorem exists_sum_tiltMean_eq (V : ℝ)
    (hcoer : ∀ v : E, V < ‖v‖ → sumLogLap s μs T 0 < sumLogLap s μs T v) :
    ∃ v, ‖v‖ ≤ V ∧ ∑ i ∈ s, tiltMean (μs i) v = T := by
  have hV : 0 ≤ V := by
    by_contra h
    push Not at h
    exact lt_irrefl _ (hcoer 0 (by simpa using h))
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_closedBall (0 : E) V).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hV⟩ (continuous_sumLogLap s μs Rs hRs T).continuousOn
  rw [isMinOn_iff] at hmin
  have hv₀' : ‖v₀‖ ≤ V := by simpa using hv₀
  have hglob : ∀ v, sumLogLap s μs T v₀ ≤ sumLogLap s μs T v := by
    intro v
    by_cases hv : ‖v‖ ≤ V
    · exact hmin v (by simpa using hv)
    · push Not at hv
      exact (hmin 0 (Metric.mem_closedBall_self hV)).trans (hcoer v hv).le
  exact ⟨v₀, hv₀', firstOrder_sum s μs Rs hRs T hglob⟩

omit [∀ i, IsFiniteMeasure (μs i)] [∀ i, NeZero (μs i)] in
/-- **Existence of the mean-zero tilt** (Lemma 102): if the Laplace transform exceeds its value
at `0` outside the ball of radius `V`, the tilt by some `v` with `‖v‖ ≤ V` has mean `0`. -/
theorem exists_tiltMean_eq_zero [NeZero μ] (hR : ∀ᵐ p ∂μ, ‖p‖ ≤ R) (V : ℝ)
    (hcoer : ∀ v : E, V < ‖v‖ → lap μ 0 < lap μ v) : ∃ v, ‖v‖ ≤ V ∧ tiltMean μ v = 0 := by
  obtain ⟨v, hv, h⟩ := exists_sum_tiltMean_eq (ι := Unit) {()} (fun _ => μ) (fun _ => R)
    (fun _ => hR) 0 V (fun v hv => by
      unfold sumLogLap
      simp only [Finset.sum_singleton, inner_zero_right, sub_zero]
      exact log_lt_log (lap_pos hR 0) (hcoer v hv))
  exact ⟨v, hv, by simpa using h⟩

end Exists


section Lemma101

/-- The marginal means of a probability measure on tuples with `xⱼ ∈ K j` (bounded sets) and
sum `s` add up to `s`. -/
theorem sum_marginal_means_eq {n : ℕ} {K : Fin n → Set E} {R : ℝ}
    (hK : ∀ j, ∀ p ∈ K j, ‖p‖ ≤ R) (β : Measure (Fin n → E)) [IsProbabilityMeasure β] {s : E}
    (hsum : ∀ᵐ x ∂β, ∑ j, x j = s) (hsupp : ∀ᵐ x ∂β, ∀ j, x j ∈ K j) :
    ∑ j, ∫ p, p ∂(β.map fun x => x j) = s := by
  have hint : ∀ j, Integrable (fun x : Fin n → E => x j) β := fun j =>
    Integrable.mono' (integrable_const R) (measurable_pi_apply j).aestronglyMeasurable
      (by filter_upwards [hsupp] with x hx using hK j _ (hx j))
  have hmap : ∀ j, ∫ p, p ∂(β.map fun x => x j) = ∫ x, x j ∂β := fun j =>
    integral_map (measurable_pi_apply j).aemeasurable aestronglyMeasurable_id
  simp_rw [hmap]
  rw [← integral_finsetSum _ (fun j _ => hint j)]
  rw [integral_congr_ae hsum, integral_const, probReal_univ, one_smul]

/-- The marginal means of a probability measure on tuples in a bounded set `K` with sum `0` add
up to `0`; so the (averaged) marginal of a measure on `𝒯_n(K)` has mean `0` (first step of
Lemma 101). -/
theorem sum_marginal_means_eq_zero {n : ℕ} {K : Set E} {R : ℝ} (hK : ∀ p ∈ K, ‖p‖ ≤ R)
    (β : Measure (Fin n → E)) [IsProbabilityMeasure β] (hsum : ∀ᵐ x ∂β, ∑ j, x j = 0)
    (hsupp : ∀ᵐ x ∂β, ∀ j, x j ∈ K) :
    ∑ j, ∫ p, p ∂(β.map fun x => x j) = 0 :=
  sum_marginal_means_eq (K := fun _ => K) (fun _ => hK) β hsum hsupp

variable [(volume : Measure E).IsAddHaarMeasure]

lemma bdd_isFinite {K : Set E} {R : ℝ} (hK : ∀ p ∈ K, ‖p‖ ≤ R) : volume K < ⊤ :=
  (measure_mono (fun p hp => mem_closedBall_zero_iff.2 (hK p hp))).trans_lt
    measure_closedBall_lt_top

/-- **Lemma 101** (`lg:lem:affine`). Let `K` be a bounded measurable set of positive volume with
centroid `0`, and `β` a probability measure on `n`-tuples (`n ≥ 1`) of points of `K` with sum
`0` (a probability measure on `𝒯_n(K)`). If every marginal of `β` has the density
`e^{a + ⟪b, p⟫}` on `K`, then `b = 0` and `β` is an `n`-complete mix of `U(K)`. -/
theorem lemma101 {n : ℕ} (hn : 0 < n) {K : Set E} (hKm : MeasurableSet K) {R : ℝ}
    (hK : ∀ p ∈ K, ‖p‖ ≤ R) (hpos : volume K ≠ 0) (hcen : ∫ p in K, p = 0) (a : ℝ) (b : E)
    (β : Measure (Fin n → E)) [IsProbabilityMeasure β] (hsum : ∀ᵐ x ∂β, ∑ j, x j = 0)
    (hsupp : ∀ᵐ x ∂β, ∀ j, x j ∈ K)
    (hmarg : ∀ j, β.map (fun x => x j) =
      (volume.restrict K).withDensity fun p => ENNReal.ofReal (exp (a + ⟪b, p⟫))) :
    b = 0 ∧ IsCompleteMix n (unifSet K) β := by
  set ν := (volume.restrict K).withDensity fun p => ENNReal.ofReal (exp (a + ⟪b, p⟫)) with hν
  -- the mean of the marginal is `0`
  have hmean : ∫ p, p ∂ν = 0 := by
    have h := sum_marginal_means_eq_zero hK β hsum hsupp
    simp_rw [hmarg] at h
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ] at h
    exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn.ne')
  have hmean' : ∫ p, p ∂ν = exp a • ∫ p, exp ⟪b, p⟫ • p ∂(volume.restrict K) := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul₀, ← integral_smul]
    · congr 1
      funext p
      rw [ENNReal.toReal_ofReal (exp_pos _).le, exp_add, smul_smul]
    · exact (ENNReal.measurable_ofReal.comp
        (continuous_exp.comp (continuous_const.add
          (continuous_const.inner continuous_id))).measurable).aemeasurable
    · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hzero : ∫ p, exp ⟪b, p⟫ • p ∂(volume.restrict K) = 0 := by
    rw [hmean', smul_eq_zero] at hmean
    exact hmean.resolve_left (exp_pos a).ne'
  -- the restricted Lebesgue measure
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 (bdd_isFinite hK).ne
  have : NeZero (volume.restrict K) := ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
  have hR : ∀ᵐ p ∂(volume.restrict K), ‖p‖ ≤ R := by
    filter_upwards [ae_restrict_mem hKm] with p hp using hK p hp
  have hac : volume.restrict K ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hb : b = 0 := by
    refine tiltMean_injective (ν := volume) hR hac ?_
    rw [tiltMean_eq, tiltMean_eq, hzero, smul_zero]
    simp only [inner_zero_left, exp_zero, one_smul, hcen, smul_zero]
  refine ⟨hb, inferInstance, ⟨0, hsum⟩, fun j => ?_⟩
  have hj := hmarg j
  rw [hν] at hj
  subst hb
  simp only [inner_zero_left, add_zero] at hj
  rw [withDensity_const] at hj
  have hprob : (β.map fun x => x j) Set.univ = 1 :=
    measure_univ
  rw [hj, smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul] at hprob
  rw [hj, unifSet, ENNReal.eq_inv_of_mul_eq_one_left hprob]

end Lemma101

section Lemma102

variable [(volume : Measure E).IsAddHaarMeasure]

/-- The tilt `h_v = h e^{⟪v, ·⟫} / ∫_K h e^{⟪v, ·⟫}` of a density `h` on `K`. -/
def tiltDens (K : Set E) (h : E → ℝ) (v y : E) : ℝ :=
  h y * exp ⟪v, y⟫ / ∫ z in K, h z * exp ⟪v, z⟫

/-- The measure with density `h` on `K`. -/
def wmeas (K : Set E) (h : E → ℝ) : Measure E :=
  (volume.restrict K).withDensity fun y => ENNReal.ofReal (h y)

/-- The constant `V` of Lemma 102: `2 (A + log (|K| / |B_{r/4}|)) / r`. -/
def constV (K : Set E) (r A : ℝ) : ℝ :=
  2 * (A + log ((volume K).toReal / (volume (Metric.ball (0 : E) (r / 4))).toReal)) / r

variable {K : Set E} {h : E → ℝ}

lemma integral_wmeas {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hKm : MeasurableSet K)
    (hm : Measurable h) (h0 : ∀ y ∈ K, 0 ≤ h y) (g : E → F) :
    ∫ y, g y ∂(wmeas K h) = ∫ y in K, h y • g y := by
  unfold wmeas
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  exact setIntegral_congr_fun hKm fun y hy => by simp only [ENNReal.toReal_ofReal (h0 y hy)]

lemma lap_wmeas (hKm : MeasurableSet K) (hm : Measurable h) (h0 : ∀ y ∈ K, 0 ≤ h y) (v : E) :
    lap (wmeas K h) v = ∫ y in K, h y * exp ⟪v, y⟫ := by
  unfold lap; rw [integral_wmeas hKm hm h0]; rfl

lemma tiltMean_wmeas (hKm : MeasurableSet K) (hm : Measurable h) (h0 : ∀ y ∈ K, 0 ≤ h y)
    (v : E) : tiltMean (wmeas K h) v = ∫ y in K, tiltDens K h v y • y := by
  unfold tiltMean
  rw [integral_wmeas hKm hm h0, lap_wmeas hKm hm h0]
  congr 1
  funext y
  rw [smul_smul, tiltDens, mul_div_assoc]

lemma integrableOn_mul_exp (hKm : MeasurableSet K) (hKfin : volume K < ⊤) (hm : Measurable h)
    (h0 : ∀ y ∈ K, 0 ≤ h y) {C : ℝ} (hup : ∀ y ∈ K, h y ≤ C) {Rb : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ Rb) (v : E) : IntegrableOn (fun y => h y * exp ⟪v, y⟫) K volume := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKfin.ne
  refine Integrable.mono' (integrable_const (C * exp (‖v‖ * Rb)))
    (hm.mul (continuous_exp.comp (continuous_const.inner continuous_id)).measurable
      ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hKm] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 y hy) (exp_pos _).le)]
  exact mul_le_mul (hup y hy) (exp_inner_le (hK y hy)) (exp_pos _).le ((h0 y hy).trans (hup y hy))

lemma integrableOn_dens (hKm : MeasurableSet K) (hKfin : volume K < ⊤) (hm : Measurable h)
    (h0 : ∀ y ∈ K, 0 ≤ h y) {C : ℝ} (hup : ∀ y ∈ K, h y ≤ C) : IntegrableOn h K volume := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKfin.ne
  refine Integrable.mono' (integrable_const C) hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hKm] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 y hy)]; exact hup y hy

/-- The measure `h · vol|K` of a bounded probability density `h` on a bounded set `K` is finite,
nonzero, absolutely continuous and concentrated on a ball. -/
lemma wmeas_facts (hKm : MeasurableSet K) (hKfin : volume K < ⊤) (hm : Measurable h)
    (h0 : ∀ y ∈ K, 0 ≤ h y) {C : ℝ} (hup : ∀ y ∈ K, h y ≤ C) (hint : ∫ y in K, h y = 1)
    {Rb : ℝ} (hK : ∀ y ∈ K, ‖y‖ ≤ Rb) :
    IsFiniteMeasure (wmeas K h) ∧ NeZero (wmeas K h) ∧ wmeas K h ≪ volume ∧
      (∀ᵐ p ∂(wmeas K h), ‖p‖ ≤ Rb) ∧ lap (wmeas K h) 0 = 1 := by
  have hfin : IsFiniteMeasure (wmeas K h) := isFiniteMeasure_withDensity_ofReal
    (integrableOn_dens hKm hKfin hm h0 hup).hasFiniteIntegral
  have hlap0 : lap (wmeas K h) 0 = 1 := by
    rw [lap_wmeas hKm hm h0]; simpa using hint
  refine ⟨hfin, ⟨fun h' => by rw [h', lap] at hlap0; simp at hlap0⟩, ?_, ?_, hlap0⟩
  · exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · exact (withDensity_absolutelyContinuous _ _).ae_le
      (by filter_upwards [ae_restrict_mem hKm] with p hp using hK p hp)

/-- The coercivity estimate of Lemmas 102 and 111(b): if `K` contains the closed ball of radius
`ρ` about `m` and `h ≥ c` on `K`, then
`∫_K h e^{⟪v, ·⟫} ≥ c e^{⟪v, m⟫ + ‖v‖ρ/2} |B_{ρ/4}|`. -/
lemma lap_wmeas_ge (hKm : MeasurableSet K) (hKfin : volume K < ⊤) (hm : Measurable h)
    (h0 : ∀ y ∈ K, 0 ≤ h y) {C : ℝ} (hup : ∀ y ∈ K, h y ≤ C) {Rb : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ Rb) {m : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall m ρ ⊆ K) {c : ℝ} (hlow : ∀ y ∈ K, c ≤ h y) {v : E} (hv : v ≠ 0) :
    c * exp (⟪v, m⟫ + ‖v‖ * ρ / 2) * (volume (Metric.ball (0 : E) (ρ / 4))).toReal ≤
      lap (wmeas K h) v := by
  set t := ‖v‖ with ht
  have htpos : 0 < t := norm_pos_iff.2 hv
  set c0 : E := m + (3 * ρ / (4 * t)) • v with hc0
  have hc0n : ‖c0 - m‖ = 3 * ρ / 4 := by
    rw [hc0, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← ht]
    field_simp
  have hS : Metric.ball c0 (ρ / 4) ⊆ K := by
    intro y hy
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := norm_add_le (c0 - m) (y - c0)
    rw [show c0 - m + (y - c0) = y - m by abel] at h1
    linarith [mem_ball_iff_norm.1 hy]
  have hSin : ∀ y ∈ Metric.ball c0 (ρ / 4), ⟪v, m⟫ + t * ρ / 2 ≤ ⟪v, y⟫ := by
    intro y hy
    have h1 : ⟪v, y⟫ = ⟪v, m⟫ + ⟪v, c0 - m⟫ + ⟪v, y - c0⟫ := by
      rw [inner_sub_right, inner_sub_right]; ring
    have h2 : ⟪v, c0 - m⟫ = 3 * ρ / 4 * t := by
      rw [hc0, add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq, ← ht]
      field_simp
    have h3 : -(t * (ρ / 4)) ≤ ⟪v, y - c0⟫ := by
      have := neg_abs_le ⟪v, y - c0⟫
      have h4 := abs_real_inner_le_norm v (y - c0)
      have h5 : ‖v‖ * ‖y - c0‖ ≤ t * (ρ / 4) :=
        mul_le_mul_of_nonneg_left (mem_ball_iff_norm.1 hy).le (norm_nonneg v)
      linarith
    rw [h1, h2]; nlinarith
  have hvolS : volume.real (Metric.ball c0 (ρ / 4)) =
      (volume (Metric.ball (0 : E) (ρ / 4))).toReal := by
    rw [Measure.real, Measure.addHaar_ball_center]
  have hIexp := integrableOn_mul_exp hKm hKfin hm h0 hup hK v
  rw [lap_wmeas hKm hm h0]
  calc c * exp (⟪v, m⟫ + t * ρ / 2) * (volume (Metric.ball (0 : E) (ρ / 4))).toReal
      = ∫ y in Metric.ball c0 (ρ / 4), c * exp (⟪v, m⟫ + t * ρ / 2) := by
        rw [setIntegral_const, hvolS, smul_eq_mul]; ring
    _ ≤ ∫ y in Metric.ball c0 (ρ / 4), h y * exp ⟪v, y⟫ := by
        refine setIntegral_mono_on (integrableOn_const ((measure_mono hS).trans_lt hKfin).ne)
          (hIexp.mono_set hS) measurableSet_ball fun y hy => ?_
        exact mul_le_mul (hlow y (hS hy)) (exp_le_exp.2 (hSin y hy)) (exp_pos _).le
          (h0 y (hS hy))
    _ ≤ ∫ y in K, h y * exp ⟪v, y⟫ := by
        refine setIntegral_mono_set hIexp ?_ (Filter.Eventually.of_forall hS)
        filter_upwards [ae_restrict_mem hKm] with y hy
        exact mul_nonneg (h0 y hy) (exp_pos _).le

/-- Bounds for a tilted density: if `|⟪v, y - m⟫| ≤ B` on `K` and `lo ≤ h ≤ hi` on `K`, then
`lo e^{-2B} ≤ h_v ≤ hi e^{2B}` on `K`. -/
lemma tiltDens_bounds (hKm : MeasurableSet K) (hKfin : volume K < ⊤) (hm : Measurable h)
    (h0 : ∀ y ∈ K, 0 ≤ h y) {lo hi : ℝ} (hlo : ∀ y ∈ K, lo ≤ h y) (hhi : ∀ y ∈ K, h y ≤ hi)
    (hint : ∫ y in K, h y = 1) {Rb : ℝ} (hK : ∀ y ∈ K, ‖y‖ ≤ Rb) {m v : E} {B : ℝ}
    (hin : ∀ y ∈ K, |⟪v, y - m⟫| ≤ B) :
    ∀ y ∈ K, lo * exp (-(2 * B)) ≤ tiltDens K h v y ∧ tiltDens K h v y ≤ hi * exp (2 * B) := by
  have hIexp := integrableOn_mul_exp hKm hKfin hm h0 hhi hK v
  have hIh := integrableOn_dens hKm hKfin hm h0 hhi
  have hsplit : ∀ y, exp ⟪v, y⟫ = exp ⟪v, m⟫ * exp ⟪v, y - m⟫ := fun y => by
    rw [← exp_add, inner_sub_right]; ring_nf
  set Z := ∫ z in K, h z * exp ⟪v, z⟫ with hZ
  set a := exp ⟪v, m⟫
  have ha : 0 < a := exp_pos _
  have hZup : Z ≤ a * exp B := by
    calc Z ≤ ∫ z in K, h z * (a * exp B) :=
          setIntegral_mono_on hIexp (hIh.mul_const _) hKm fun y hy => by
            rw [hsplit]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (exp_le_exp.2 (abs_le.1 (hin y hy)).2) ha.le) (h0 y hy)
      _ = a * exp B := by rw [integral_mul_const, hint, one_mul]
  have hZlow : a * exp (-B) ≤ Z := by
    calc a * exp (-B) = ∫ z in K, h z * (a * exp (-B)) := by
          rw [integral_mul_const, hint, one_mul]
      _ ≤ Z := setIntegral_mono_on (hIh.mul_const _) hIexp hKm fun y hy => by
            rw [hsplit]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (exp_le_exp.2 (abs_le.1 (hin y hy)).1) ha.le) (h0 y hy)
  have hZpos : 0 < Z := (mul_pos ha (exp_pos _)).trans_le hZlow
  intro y hy
  have hy1 := abs_le.1 (hin y hy)
  have hlo0 : lo ≤ hi := (hlo y hy).trans (hhi y hy)
  unfold tiltDens
  rw [← hZ, hsplit y]
  constructor
  · by_cases hlo' : lo ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hlo' (exp_pos _).le).trans
        (div_nonneg (mul_nonneg (h0 y hy) (by positivity)) hZpos.le)
    push Not at hlo'
    calc lo * exp (-(2 * B)) = lo * (a * exp (-B)) / (a * exp B) := by
          rw [show -(2 * B) = -B - B by ring, exp_sub]; field_simp
      _ ≤ h y * (a * exp ⟪v, y - m⟫) / Z :=
          div_le_div₀ (mul_nonneg (h0 y hy) (by positivity))
            (mul_le_mul (hlo y hy) (mul_le_mul_of_nonneg_left (exp_le_exp.2 hy1.1) ha.le)
              (by positivity) (h0 y hy)) hZpos hZup
  · calc h y * (a * exp ⟪v, y - m⟫) / Z ≤ hi * (a * exp B) / (a * exp (-B)) :=
          div_le_div₀ (mul_nonneg ((h0 y hy).trans (hhi y hy)) (by positivity))
            (mul_le_mul (hhi y hy) (mul_le_mul_of_nonneg_left (exp_le_exp.2 hy1.2) ha.le)
              (by positivity) ((h0 y hy).trans (hhi y hy))) (by positivity) hZlow
      _ = hi * exp (2 * B) := by
          rw [show 2 * B = B - -B by ring, exp_sub]; field_simp

/-- **Lemma 102** (`lg:lem:tilt`). Let `K` be a measurable set with `‖y‖ ≤ R` on `K` that contains
the closed ball of radius `r > 0` about `0`, let `A ≥ 0`, and let `h` be a measurable probability
density on `K` with `e^{-A}/|K| ≤ h ≤ e^A/|K|` on `K`. Then exactly one `v` makes the tilt `h_v`
have mean `0`; it satisfies `‖v‖ ≤ V = 2(A + log(|K|/|B_{r/4}|))/r`, and
`e^{-A'}/|K| ≤ h_v ≤ e^{A'}/|K|` on `K` with `A' = A + 2VR`. -/
theorem lemma102 (hKm : MeasurableSet K) {R : ℝ} (hK : ∀ y ∈ K, ‖y‖ ≤ R) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : E) r ⊆ K) {A : ℝ} (hA : 0 ≤ A) (hm : Measurable h)
    (hlow : ∀ y ∈ K, exp (-A) / (volume K).toReal ≤ h y)
    (hup : ∀ y ∈ K, h y ≤ exp A / (volume K).toReal) (hint : ∫ y in K, h y = 1) :
    (∃! v : E, ∫ y in K, tiltDens K h v y • y = 0) ∧
    ∀ v : E, ∫ y in K, tiltDens K h v y • y = 0 → ‖v‖ ≤ constV K r A ∧
      ∀ y ∈ K, exp (-(A + 2 * constV K r A * R)) / (volume K).toReal ≤ tiltDens K h v y ∧
        tiltDens K h v y ≤ exp (A + 2 * constV K r A * R) / (volume K).toReal := by
  set V := constV K r A with hVdef
  set vK := (volume K).toReal with hvK
  set vB := (volume (Metric.ball (0 : E) (r / 4))).toReal with hvB
  have hKfin : volume K < ⊤ := bdd_isFinite hK
  have hKpos : 0 < volume K :=
    (Metric.measure_closedBall_pos volume 0 hr).trans_le (measure_mono hball)
  have hvKpos : 0 < vK := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have hB4 : Metric.ball (0 : E) (r / 4) ⊆ K := fun y hy => hball
    (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hy))
  have hvBpos : 0 < vB := ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by linarith)).ne'
    ((measure_mono hB4).trans_lt hKfin).ne
  have hvBK : vB ≤ vK := ENNReal.toReal_mono hKfin.ne (measure_mono hB4)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hK 0 (hball (Metric.mem_closedBall_self hr.le)))
  have h0 : ∀ y ∈ K, 0 ≤ h y := fun y hy => (div_pos (exp_pos _) hvKpos).le.trans (hlow y hy)
  have hV0 : 0 ≤ V := by
    have : 0 ≤ log (vK / vB) := log_nonneg ((one_le_div hvBpos).2 hvBK)
    rw [hVdef, constV]; positivity
  obtain ⟨_, _, hac, hR, hlap0⟩ := wmeas_facts hKm hKfin hm h0 hup hint hK
  -- coercivity
  have hcoer : ∀ v : E, V < ‖v‖ → lap (wmeas K h) 0 < lap (wmeas K h) v := by
    intro v hv
    have hv0 : v ≠ 0 := norm_pos_iff.1 (hV0.trans_lt hv)
    have hlow2 := lap_wmeas_ge hKm hKfin hm h0 hup hK hr hball hlow hv0
    rw [inner_zero_right, zero_add] at hlow2
    rw [hlap0]
    refine lt_of_lt_of_le ?_ hlow2
    have hexp : exp A * (vK / vB) < exp (‖v‖ * r / 2) := by
      rw [← exp_log (div_pos hvKpos hvBpos), ← exp_add]
      apply exp_lt_exp.2
      have : V * r < ‖v‖ * r := mul_lt_mul_of_pos_right hv hr
      rw [hVdef, constV, div_mul_cancel₀ _ hr.ne'] at this
      linarith
    have e1 : exp (-A) / vK * exp (‖v‖ * r / 2) * vB
        = exp (-A) * exp (‖v‖ * r / 2) * (vB / vK) := by ring
    rw [← hvB, e1]
    have hq : 0 < vB / vK := div_pos hvBpos hvKpos
    calc (1 : ℝ) = exp (-A) * (exp A * (vK / vB)) * (vB / vK) := by
          field_simp; rw [← exp_add]; simp
      _ < exp (-A) * exp (‖v‖ * r / 2) * (vB / vK) := by gcongr
  -- existence and uniqueness
  obtain ⟨v₀, hv₀V, hv₀⟩ := exists_tiltMean_eq_zero hR V hcoer
  have huniq : ∀ v, ∫ y in K, tiltDens K h v y • y = 0 → v = v₀ := fun v hv =>
    tiltMean_injective (ν := volume) hR hac (by rw [hv₀, tiltMean_wmeas hKm hm h0, hv])
  refine ⟨⟨v₀, show ∫ y in K, tiltDens K h v₀ y • y = 0 by
    rw [← tiltMean_wmeas hKm hm h0]; exact hv₀, fun v hv => huniq v hv⟩, ?_⟩
  intro v hv
  have hvV : ‖v‖ ≤ V := huniq v hv ▸ hv₀V
  refine ⟨hvV, ?_⟩
  have hin : ∀ y ∈ K, |⟪v, y - 0⟫| ≤ V * R := fun y hy => by
    rw [sub_zero]
    exact (abs_real_inner_le_norm v y).trans (mul_le_mul hvV (hK y hy) (norm_nonneg _) hV0)
  intro y hy
  have hb := tiltDens_bounds hKm hKfin hm h0 hlow hup hint hK hin y hy
  constructor
  · calc exp (-(A + 2 * V * R)) / vK = exp (-A) / vK * exp (-(2 * (V * R))) := by
          rw [show -(A + 2 * V * R) = -A + -(2 * (V * R)) by ring, exp_add]; ring
      _ ≤ _ := hb.1
  · calc tiltDens K h v y ≤ exp A / vK * exp (2 * (V * R)) := hb.2
      _ = exp (A + 2 * V * R) / vK := by
          rw [show A + 2 * V * R = A + 2 * (V * R) by ring, exp_add]; ring

end Lemma102

section Lemma111

variable [(volume : Measure E).IsAddHaarMeasure]

/-- The constant `V` of Lemma 111(b): `2 (A' + log (|B_R| / |B_{ρ/4}|)) / ρ`. -/
def constV' (R ρ A' : ℝ) : ℝ :=
  2 * (A' + log ((volume (Metric.closedBall (0 : E) R)).toReal /
    (volume (Metric.ball (0 : E) (ρ / 4))).toReal)) / ρ

/-- **Lemma 111(b)** (`jl:lem:tilt`). Let `n ≥ 1`, and for each `j` let `K j` be a measurable set
of diameter at most `R` that contains the closed ball of radius `ρ > 0` about `m j` (in the
paper `ρ = r_A`, by part (a), `lemma111a`), and `k j` a measurable probability
density on `K j` with `e^{-A'} ≤ |K j| k j ≤ e^{A'}` on `K j`, `A' ≥ 0`. Then exactly one `v`
satisfies `∑ⱼ m_{(k j)_v} = ∑ⱼ m j`; it has `‖v‖ ≤ V = 2(A' + log(|B_R|/|B_{ρ/4}|))/ρ` and
`e^{-A'-2VR} ≤ |K j| (k j)_v ≤ e^{A'+2VR}` on `K j`. -/
theorem lemma111b {n : ℕ} (hn : 0 < n) (K : Fin n → Set E) (hKm : ∀ j, MeasurableSet (K j))
    (m : Fin n → E) {ρ R : ℝ} (hρ : 0 < ρ) (hball : ∀ j, Metric.closedBall (m j) ρ ⊆ K j)
    (hdiam : ∀ j, ∀ x ∈ K j, ∀ y ∈ K j, ‖x - y‖ ≤ R) {A' : ℝ} (hA' : 0 ≤ A')
    (k : Fin n → E → ℝ) (hm : ∀ j, Measurable (k j))
    (hlow : ∀ j, ∀ y ∈ K j, exp (-A') ≤ (volume (K j)).toReal * k j y)
    (hup : ∀ j, ∀ y ∈ K j, (volume (K j)).toReal * k j y ≤ exp A')
    (hint : ∀ j, ∫ y in K j, k j y = 1) :
    (∃! v : E, ∑ j, ∫ y in K j, tiltDens (K j) (k j) v y • y = ∑ j, m j) ∧
    ∀ v : E, ∑ j, ∫ y in K j, tiltDens (K j) (k j) v y • y = ∑ j, m j →
      ‖v‖ ≤ constV' (E := E) R ρ A' ∧ ∀ j, ∀ y ∈ K j,
        exp (-A' - 2 * constV' (E := E) R ρ A' * R) ≤
          (volume (K j)).toReal * tiltDens (K j) (k j) v y ∧
        (volume (K j)).toReal * tiltDens (K j) (k j) v y ≤
          exp (A' + 2 * constV' (E := E) R ρ A' * R) := by
  set V := constV' (E := E) R ρ A' with hVdef
  set vR := (volume (Metric.closedBall (0 : E) R)).toReal with hvR
  set vB := (volume (Metric.ball (0 : E) (ρ / 4))).toReal with hvB
  have hmK : ∀ j, m j ∈ K j := fun j => hball j (Metric.mem_closedBall_self hρ.le)
  have hKR : ∀ j, K j ⊆ Metric.closedBall (m j) R := fun j y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hdiam j y hy (m j) (hmK j)
  have hR0 : 0 ≤ R := by
    have := hdiam ⟨0, hn⟩ _ (hmK ⟨0, hn⟩) _ (hmK ⟨0, hn⟩); simpa using this
  have hvolR : ∀ j, volume (Metric.closedBall (m j) R) = volume (Metric.closedBall (0 : E) R) :=
    fun j => Measure.addHaar_closedBall_center _ _ _
  have hRfin : volume (Metric.closedBall (0 : E) R) < ⊤ := measure_closedBall_lt_top
  have hKfin : ∀ j, volume (K j) < ⊤ := fun j =>
    (measure_mono (hKR j)).trans_lt (by rw [hvolR]; exact hRfin)
  have hKpos : ∀ j, 0 < volume (K j) := fun j =>
    (Metric.measure_closedBall_pos volume _ hρ).trans_le (measure_mono (hball j))
  set vK : Fin n → ℝ := fun j => (volume (K j)).toReal with hvK
  have hvKpos : ∀ j, 0 < vK j := fun j => ENNReal.toReal_pos (hKpos j).ne' (hKfin j).ne
  have hvKR : ∀ j, vK j ≤ vR := fun j => by
    rw [hvK, hvR, ← hvolR j]; exact ENNReal.toReal_mono (by rw [hvolR]; exact hRfin.ne)
      (measure_mono (hKR j))
  have hB4 : ∀ j, Metric.ball (m j) (ρ / 4) ⊆ K j := fun j y hy => hball j
    (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hy))
  have hvBK : ∀ j, vB ≤ vK j := fun j => by
    rw [hvB, ← Measure.addHaar_ball_center volume (m j)]
    exact ENNReal.toReal_mono (hKfin j).ne (measure_mono (hB4 j))
  have hvBpos : 0 < vB := ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV0 : 0 ≤ V := by
    have : 0 ≤ log (vR / vB) :=
      log_nonneg ((one_le_div hvBpos).2 ((hvBK ⟨0, hn⟩).trans (hvKR ⟨0, hn⟩)))
    rw [hVdef, constV']; positivity
  -- densities in the form `lo ≤ k ≤ hi`
  have hlow' : ∀ j, ∀ y ∈ K j, exp (-A') / vK j ≤ k j y := fun j y hy => by
    rw [div_le_iff₀' (hvKpos j)]; exact hlow j y hy
  have hup' : ∀ j, ∀ y ∈ K j, k j y ≤ exp A' / vK j := fun j y hy => by
    rw [le_div_iff₀' (hvKpos j)]; exact hup j y hy
  have h0 : ∀ j, ∀ y ∈ K j, 0 ≤ k j y := fun j y hy =>
    (div_pos (exp_pos _) (hvKpos j)).le.trans (hlow' j y hy)
  have hKb : ∀ j, ∀ y ∈ K j, ‖y‖ ≤ ‖m j‖ + R := fun j y hy => by
    have h1 := norm_add_le (m j) (y - m j)
    rw [add_sub_cancel] at h1
    linarith [hdiam j y hy (m j) (hmK j)]
  set μ : Fin n → Measure E := fun j => wmeas (K j) (k j) with hμ
  have hfacts := fun j => wmeas_facts (hKm j) (hKfin j) (hm j) (h0 j) (hup' j) (hint j) (hKb j)
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => (hfacts j).1
  have : ∀ j, NeZero (μ j) := fun j => (hfacts j).2.1
  have hac : ∀ j, μ j ≪ volume := fun j => (hfacts j).2.2.1
  have hRb : ∀ j, ∀ᵐ p ∂(μ j), ‖p‖ ≤ ‖m j‖ + R := fun j => (hfacts j).2.2.2.1
  have hlap0 : ∀ j, lap (μ j) 0 = 1 := fun j => (hfacts j).2.2.2.2
  have htm : ∀ v, ∑ j, tiltMean (μ j) v = ∑ j, ∫ y in K j, tiltDens (K j) (k j) v y • y :=
    fun v => Finset.sum_congr rfl fun j _ => tiltMean_wmeas (hKm j) (hm j) (h0 j) v
  -- coercivity
  have hcoer : ∀ v : E, V < ‖v‖ →
      sumLogLap Finset.univ μ (∑ j, m j) 0 < sumLogLap Finset.univ μ (∑ j, m j) v := by
    intro v hv
    have hv0 : v ≠ 0 := norm_pos_iff.1 (hV0.trans_lt hv)
    have hF0 : sumLogLap Finset.univ μ (∑ j, m j) 0 = 0 := by
      simp [sumLogLap, hlap0]
    rw [hF0, sumLogLap, inner_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_pos (fun j _ => ?_) (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩)
    have hlow2 := lap_wmeas_ge (hKm j) (hKfin j) (hm j) (h0 j) (hup' j) (hKb j) hρ (hball j)
      (hlow' j) hv0
    have hZ := lap_pos (hRb j) v
    rw [sub_pos, ← log_exp ⟪v, m j⟫]
    refine log_lt_log (exp_pos _) (lt_of_lt_of_le ?_ hlow2)
    rw [← hvB, exp_add]
    have hexp : exp A' * (vK j / vB) < exp (‖v‖ * ρ / 2) := by
      rw [← exp_log (div_pos (hvKpos j) hvBpos), ← exp_add]
      apply exp_lt_exp.2
      have : V * ρ < ‖v‖ * ρ := mul_lt_mul_of_pos_right hv hρ
      rw [hVdef, constV', div_mul_cancel₀ _ hρ.ne'] at this
      have : log (vK j / vB) ≤ log (vR / vB) :=
        log_le_log (div_pos (hvKpos j) hvBpos) (div_le_div_of_nonneg_right (hvKR j) hvBpos.le)
      linarith
    have e1 : exp (-A') / vK j * (exp ⟪v, m j⟫ * exp (‖v‖ * ρ / 2)) * vB
        = exp ⟪v, m j⟫ * (exp (-A') * exp (‖v‖ * ρ / 2) * (vB / vK j)) := by
      have := (hvKpos j).ne'
      field_simp
    rw [e1]
    have hq : 0 < vB / vK j := div_pos hvBpos (hvKpos j)
    have : 1 < exp (-A') * exp (‖v‖ * ρ / 2) * (vB / vK j) := by
      calc (1 : ℝ) = exp (-A') * (exp A' * (vK j / vB)) * (vB / vK j) := by
            have := (hvKpos j).ne'
            have := hvBpos.ne'
            field_simp; rw [← exp_add]; simp
        _ < exp (-A') * exp (‖v‖ * ρ / 2) * (vB / vK j) := by gcongr
    nlinarith [exp_pos ⟪v, m j⟫]
  -- existence and uniqueness
  obtain ⟨v₀, hv₀V, hv₀⟩ := exists_sum_tiltMean_eq Finset.univ μ (fun j => ‖m j‖ + R) hRb
    (∑ j, m j) V hcoer
  have huniq : ∀ v, ∑ j, ∫ y in K j, tiltDens (K j) (k j) v y • y = ∑ j, m j → v = v₀ :=
    fun v hv => sum_tiltMean_injective (ν := volume) Finset.univ
      (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) μ _ hRb hac (by rw [hv₀, htm, hv])
  refine ⟨⟨v₀, show ∑ j, ∫ y in K j, tiltDens (K j) (k j) v₀ y • y = ∑ j, m j by
    rw [← htm]; exact hv₀, fun v hv => huniq v hv⟩, ?_⟩
  intro v hv
  have hvV : ‖v‖ ≤ V := huniq v hv ▸ hv₀V
  refine ⟨hvV, fun j y hy => ?_⟩
  have hin : ∀ y ∈ K j, |⟪v, y - m j⟫| ≤ V * R := fun y hy =>
    (abs_real_inner_le_norm v _).trans
      (mul_le_mul hvV (hdiam j y hy (m j) (hmK j)) (norm_nonneg _) hV0)
  have hb := tiltDens_bounds (hKm j) (hKfin j) (hm j) (h0 j) (hlow' j) (hup' j) (hint j) (hKb j)
    hin y hy
  have hvKj := hvKpos j
  constructor
  · calc exp (-A' - 2 * V * R) = vK j * (exp (-A') / vK j * exp (-(2 * (V * R)))) := by
          rw [show -A' - 2 * V * R = -A' + -(2 * (V * R)) by ring, exp_add]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hb.1 hvKj.le
  · calc vK j * tiltDens (K j) (k j) v y ≤ vK j * (exp A' / vK j * exp (2 * (V * R))) :=
          mul_le_mul_of_nonneg_left hb.2 hvKj.le
      _ = exp (A' + 2 * V * R) := by
          rw [show A' + 2 * V * R = A' + 2 * (V * R) by ring, exp_add]; field_simp

/-- **Lemma 111(c)** (`jl:lem:tilt`). Let `g j` be bounded measurable probability densities on
bounded measurable sets `K j` of positive volume, with means `m j`. If a probability measure on
`n`-tuples (`n ≥ 1`) with `xⱼ ∈ K j` and `∑ⱼ xⱼ = ∑ⱼ m j` has the marginals `(g j)_w` for one
`w`, then `w = 0`. -/
theorem lemma111c {n : ℕ} (hn : 0 < n) (K : Fin n → Set E) (hKm : ∀ j, MeasurableSet (K j))
    {R C : ℝ} (hK : ∀ j, ∀ y ∈ K j, ‖y‖ ≤ R) (g : Fin n → E → ℝ) (hm : ∀ j, Measurable (g j))
    (h0 : ∀ j, ∀ y ∈ K j, 0 ≤ g j y) (hup : ∀ j, ∀ y ∈ K j, g j y ≤ C)
    (hint : ∀ j, ∫ y in K j, g j y = 1) (m : Fin n → E) (hmean : ∀ j, m j = ∫ y in K j, g j y • y)
    (β : Measure (Fin n → E)) [IsProbabilityMeasure β] (hsum : ∀ᵐ x ∂β, ∑ j, x j = ∑ j, m j)
    (hsupp : ∀ᵐ x ∂β, ∀ j, x j ∈ K j) (w : E)
    (hmarg : ∀ j, β.map (fun x => x j) = (volume.restrict (K j)).withDensity
      fun y => ENNReal.ofReal (tiltDens (K j) (g j) w y)) : w = 0 := by
  have hKfin : ∀ j, volume (K j) < ⊤ := fun j => bdd_isFinite (hK j)
  set μ : Fin n → Measure E := fun j => wmeas (K j) (g j) with hμ
  have hfacts := fun j => wmeas_facts (hKm j) (hKfin j) (hm j) (h0 j) (hup j) (hint j) (hK j)
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => (hfacts j).1
  have : ∀ j, NeZero (μ j) := fun j => (hfacts j).2.1
  have hac : ∀ j, μ j ≪ volume := fun j => (hfacts j).2.2.1
  have hRb : ∀ j, ∀ᵐ p ∂(μ j), ‖p‖ ≤ R := fun j => (hfacts j).2.2.2.1
  have hlap0 : ∀ j, lap (μ j) 0 = 1 := fun j => (hfacts j).2.2.2.2
  -- the tilted densities are measurable and nonnegative on `K j`
  have htm : ∀ j, ∫ p, p ∂(β.map fun x => x j) = tiltMean (μ j) w := fun j => by
    rw [hmarg j, tiltMean_wmeas (hKm j) (hm j) (h0 j)]
    refine integral_wmeas (hKm j) ?_ (fun y hy => ?_) id
    · exact ((hm j).mul (continuous_exp.comp (continuous_const.inner continuous_id)).measurable
        ).div_const _
    · exact div_nonneg (mul_nonneg (h0 j y hy) (exp_pos _).le)
        (setIntegral_nonneg (hKm j) fun z hz => mul_nonneg (h0 j z hz) (exp_pos _).le)
  have htm0 : ∀ j, tiltMean (μ j) 0 = m j := fun j => by
    rw [tiltMean_eq, hlap0, inv_one, one_smul, hmean, integral_wmeas (hKm j) (hm j) (h0 j)]
    simp
  have h := sum_marginal_means_eq hK β hsum hsupp
  simp_rw [htm] at h
  refine sum_tiltMean_injective (ν := volume) Finset.univ
    (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) μ _ hRb hac ?_
  rw [h]
  exact (Finset.sum_congr rfl fun j _ => htm0 j).symm

end Lemma111

section MinkowskiRadon

/-- The limit `s → 1⁻` of `a (1 - s^{d+1}) ≤ b (1 - s^d)`. -/
lemma limit_geom {a b : ℝ} (d : ℕ)
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) 1, a * (1 - s ^ (d + 1)) ≤ b * (1 - s ^ d)) :
    a * (d + 1) ≤ b * d := by
  have h' : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Iio 1),
      a * ∑ i ∈ Finset.range (d + 1), s ^ i ≤ b * ∑ i ∈ Finset.range d, s ^ i := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
    have h1 := h s hs
    have hs1 : 0 < 1 - s := by linarith [hs.2]
    have e1 := geom_sum_mul s (d + 1)
    have e2 := geom_sum_mul s d
    have : (a * ∑ i ∈ Finset.range (d + 1), s ^ i) * (1 - s) ≤
        (b * ∑ i ∈ Finset.range d, s ^ i) * (1 - s) := by
      have q1 : (a * ∑ i ∈ Finset.range (d + 1), s ^ i) * (1 - s) = a * (1 - s ^ (d + 1)) := by
        linear_combination (-a) * e1
      have q2 : (b * ∑ i ∈ Finset.range d, s ^ i) * (1 - s) = b * (1 - s ^ d) := by
        linear_combination (-b) * e2
      rw [q1, q2]; exact h1
    exact le_of_mul_le_mul_right this hs1
  have hc : ∀ k : ℕ, Filter.Tendsto (fun s : ℝ => ∑ i ∈ Finset.range k, s ^ i)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (k : ℝ)) := by
    intro k
    have hcont : Continuous fun s : ℝ => ∑ i ∈ Finset.range k, s ^ i :=
      continuous_finsetSum _ fun i _ => continuous_pow i
    have := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  have := le_of_tendsto_of_tendsto ((hc (d + 1)).const_mul a) ((hc d).const_mul b) h'
  push_cast at this
  exact this

variable [(volume : Measure E).IsAddHaarMeasure]

/-- The homothetic copy `p + s (K - p)` of `K`, written as a preimage. -/
def homot (K : Set E) (p : E) (s : ℝ) : Set E := {x | s⁻¹ • (x - (1 - s) • p) ∈ K}

lemma homot_subset {K : Set E} (hK : Convex ℝ K) {p : E} (hp : p ∈ K) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) : homot K p s ⊆ K := by
  intro x hx
  have hx' : s • (s⁻¹ • (x - (1 - s) • p)) + (1 - s) • p = x := by
    rw [smul_smul, mul_inv_cancel₀ hs.1.ne', one_smul, sub_add_cancel]
  rw [← hx']
  exact hK hx hp hs.1.le (by linarith [hs.2]) (by ring)

lemma isClosed_homot {K : Set E} (hK : IsClosed K) (p : E) (s : ℝ) : IsClosed (homot K p s) :=
  hK.preimage ((continuous_id.sub continuous_const).const_smul _)

lemma measurableSet_homot {K : Set E} (hK : MeasurableSet K) (p : E) (s : ℝ) :
    MeasurableSet (homot K p s) :=
  hK.preimage ((measurable_id.sub_const _).const_smul _)

/-- Change of variables for the homothety `x = s y + (1 - s) p`. -/
lemma setIntegral_homot {K : Set E} (hKm : MeasurableSet K) (p : E) {s : ℝ} (hs : 0 < s)
    (φ : E → ℝ) :
    ∫ x in homot K p s, φ x = s ^ Module.finrank ℝ E * ∫ y in K, φ (s • y + (1 - s) • p) := by
  set q := (1 - s) • p
  have hind : ∀ y, (homot K p s).indicator φ (s • y + q) =
      K.indicator (fun y => φ (s • y + q)) y := by
    intro y
    have : s • y + q ∈ homot K p s ↔ y ∈ K := by
      simp only [homot, Set.mem_ofPred_eq, add_sub_cancel_right, smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul, q]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem (this.2 hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy (this.1 h)), Set.indicator_of_notMem hy]
  rw [← integral_indicator (measurableSet_homot hKm p s),
    ← integral_add_right_eq_self _ q]
  have h2 := Measure.integral_comp_smul (μ := (volume : Measure E))
    (fun x => (homot K p s).indicator φ (x + q)) s
  simp_rw [hind] at h2
  rw [integral_indicator hKm] at h2
  have hpow : 0 < s ^ Module.finrank ℝ E := pow_pos hs _
  rw [abs_of_pos (inv_pos.2 hpow), smul_eq_mul] at h2
  rw [h2]
  field_simp

/-- **The centroid lies at depth at least `1/(d+1)` of the width** (the theorem of Minkowski and
Radon, remark `g:rem:asym`), in the form: if `mn ≤ f` on a convex body `K` and `p ∈ K`, then
`(d + 1) (f p - f c) ≤ d (f p - mn)` for the centroid `c = ∫_K y / |K|`, written without
division. Proof: the homothetic copies `K_s = p + s (K - p) ⊆ K` have
`∫_{K_s} (f p - f) = s^{d+1} ∫_K (f p - f)` and volume `s^d |K|`, and `f p - f ≤ f p - mn` on
`K \ K_s`; let `s → 1`. -/
theorem centroid_support {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (f : StrongDual ℝ E) {p : E} (hp : p ∈ K) {mn : ℝ}
    (hmn : ∀ y ∈ K, mn ≤ f y) :
    ((Module.finrank ℝ E : ℝ) + 1) * (volume.real K * f p - f (∫ y in K, y)) ≤
      Module.finrank ℝ E * (f p - mn) * volume.real K := by
  set d := Module.finrank ℝ E
  set vK := volume.real K
  obtain ⟨F, hF⟩ : ∃ F : E → ℝ, F = fun y => f p - f y := ⟨_, rfl⟩
  set W := f p - mn
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hfin : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  have hFc : Continuous F := hF ▸ continuous_const.sub f.continuous
  have hFi : IntegrableOn F K := hFc.continuousOn.integrableOn_compact hKc
  have hidi : IntegrableOn (fun y : E => y) K := continuous_id.continuousOn.integrableOn_compact hKc
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ y in K, F y := ⟨_, rfl⟩
  have hIeq : I = vK * f p - f (∫ y in K, y) := by
    rw [hI, hF, integral_sub (integrableOn_const hfin)
      (f.continuous.continuousOn.integrableOn_compact hKc),
      setIntegral_const, smul_eq_mul, f.integral_comp_comm hidi]
  have key : ∀ s ∈ Set.Ioo (0 : ℝ) 1, I * (1 - s ^ (d + 1)) ≤ W * vK * (1 - s ^ d) := by
    intro s hs
    set S := homot K p s
    have hSK : S ⊆ K := homot_subset hKconv hp hs
    have hSm : MeasurableSet S := measurableSet_homot hKm p s
    have hintS : ∫ x in S, F x = s ^ d * (s * I) := by
      have h1 : ∫ y in K, F (s • y + (1 - s) • p) = s * I := by
        rw [hI, ← integral_const_mul]
        refine setIntegral_congr_fun hKm fun y _ => ?_
        simp only [hF, map_add, map_smul, smul_eq_mul]
        ring
      rw [setIntegral_homot hKm p hs.1, h1]
    have hvolS : volume.real S = s ^ d * vK := by
      have h := setIntegral_homot hKm p hs.1 (fun _ => (1 : ℝ))
      simp only [setIntegral_const, smul_eq_mul, mul_one] at h
      exact h
    have hsplit : I = (∫ x in S, F x) + ∫ x in K \ S, F x := by
      have h := setIntegral_union Set.disjoint_sdiff_right (hKm.diff hSm) (hFi.mono_set hSK)
        (hFi.mono_set Set.sdiff_subset)
      rw [Set.union_sdiff_cancel hSK] at h
      rw [hI, h]
    have hbound : ∫ x in K \ S, F x ≤ W * (vK - s ^ d * vK) := by
      calc ∫ x in K \ S, F x ≤ ∫ x in K \ S, W :=
            setIntegral_mono_on (hFi.mono_set Set.sdiff_subset)
              (integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hfin)) (hKm.diff hSm)
              fun y hy => by simp only [hF, W]; linarith [hmn y hy.1]
        _ = W * (vK - s ^ d * vK) := by
            rw [setIntegral_const, measureReal_sdiff hSK hSm hfin, hvolS, smul_eq_mul, mul_comm]
    rw [hintS] at hsplit
    have : I * (1 - s ^ (d + 1)) = ∫ x in K \ S, F x := by
      rw [pow_succ]; linear_combination hsplit
    rw [this]; linarith
  have hlim := limit_geom d key
  rw [hIeq] at hlim
  linarith

/-- The centroid `|K|⁻¹ ∫_K y` of a set `K`. -/
def cent (K : Set E) : E := (volume.real K)⁻¹ • ∫ y in K, y

lemma map_cent {K : Set E} (hpos : volume.real K ≠ 0)
    (f : StrongDual ℝ E) : f (∫ y in K, y) = volume.real K * f (cent K) := by
  rw [cent, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

lemma real_pos_of_compact {K : Set E} (hKc : IsCompact K) (hpos : 0 < volume K) :
    0 < volume.real K :=
  ENNReal.toReal_pos hpos.ne' hKc.measure_lt_top.ne

/-- `cent K` is the mean of `U(K)` (the form of the centroid used in `Room.lean`). -/
lemma cent_eq_integral_unifSet (K : Set E) : cent K = ∫ x, x ∂(unifSet K) := by
  rw [cent, unifSet, integral_smul_measure, ENNReal.toReal_inv]
  rfl

/-- **Minkowski–Radon** (remark `g:rem:asym`): `as(K) ≤ d` about the centroid, in the form of the
predicate `AsymLE K c d` of `Room.lean`: for every continuous linear functional `u` and `x ∈ K`
there is `y ∈ K` with `u x - u c ≤ d (u c - u y)`. Here `K` is a compact convex set of positive
volume in a space of dimension `d`. -/
theorem asymLE_cent {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hpos : 0 < volume K) :
    ∀ u : StrongDual ℝ E, ∀ x ∈ K, ∃ y ∈ K, u x - u (cent K) ≤
      (Module.finrank ℝ E : ℝ) * (u (cent K) - u y) := by
  intro u x hx
  obtain ⟨y, hy, hmin⟩ := hKc.exists_isMinOn ⟨x, hx⟩ u.continuous.continuousOn
  refine ⟨y, hy, ?_⟩
  have hvK := real_pos_of_compact hKc hpos
  have h := centroid_support hKc hKconv u hx (mn := u y) fun z hz => hmin hz
  rw [map_cent hvK.ne'] at h
  have h2 : ((Module.finrank ℝ E : ℝ) + 1) * (u x - u (cent K)) * volume.real K ≤
      (Module.finrank ℝ E : ℝ) * (u x - u y) * volume.real K := by linarith
  have h3 := le_of_mul_le_mul_right h2 hvK
  linarith

/-- **Remark 85 / `g:rem:asym`: `-(K - c) ⊂ d (K - c)`** for a convex body `K` (compact, convex,
positive volume) in a space of dimension `d ≥ 1`, `c` its centroid: `c - d⁻¹ (x - c) ∈ K` for
every `x ∈ K`. By separation from `asymLE_cent`. -/
theorem neg_sub_cent_mem {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hpos : 0 < volume K) (hd : 0 < Module.finrank ℝ E) {x : E} (hx : x ∈ K) :
    cent K - (Module.finrank ℝ E : ℝ)⁻¹ • (x - cent K) ∈ K := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd' : 0 < d := Nat.cast_pos.2 hd
  by_contra hz
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hKconv hKc.isClosed hz
  obtain ⟨y, hy, hxy⟩ := asymLE_cent hKc hKconv hpos (-f) x hx
  have h1 := hfu y hy
  have e : f (cent K - d⁻¹ • (x - cent K)) = f (cent K) - d⁻¹ * (f x - f (cent K)) := by
    simp [map_sub, map_smul, smul_eq_mul]
  rw [e] at hux
  simp only [neg_apply] at hxy
  have h2 : f (cent K) - f x ≤ d * (f y - f (cent K)) := by linarith
  have h3 : d⁻¹ * (f (cent K) - f x) ≤ f y - f (cent K) := by
    rw [inv_mul_le_iff₀ hd']; exact h2
  linarith

/-- **Lemma 111(a)** (`jl:lem:tilt`) from the inclusion `-(K - c) ⊂ D (K - c)`, `D > 0`. Let `K`
be compact and convex, containing a closed ball of radius `r > 0`, with centroid `c` such that
`c - D⁻¹ (x - c) ∈ K` for `x ∈ K`, and let `g` be a measurable probability density on `K` with
`e^{-A} ≤ |K| g ≤ e^A` on `K`. Then the closed ball of radius `2 e^{-A} r / (D + 1)` about the
mean `m = ∫_K g y dy` lies in `K`. (The paper's case is `D = d`, Remark 85.) -/
theorem lemma111a_of {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) {b : E} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall b r ⊆ K) {D : ℝ} (hD : 0 < D)
    (hMR : ∀ x ∈ K, cent K - D⁻¹ • (x - cent K) ∈ K) {A : ℝ} {g : E → ℝ} (hgm : Measurable g)
    (hlow : ∀ y ∈ K, exp (-A) ≤ volume.real K * g y)
    (hup : ∀ y ∈ K, volume.real K * g y ≤ exp A) (hint : ∫ y in K, g y = 1) :
    Metric.closedBall (∫ y in K, g y • y) (2 * exp (-A) * r / (D + 1)) ⊆ K := by
  set m := ∫ y in K, g y • y
  set vK := volume.real K
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hbK : b ∈ K := hball (Metric.mem_closedBall_self hr.le)
  have hpos : 0 < volume K := (Metric.measure_closedBall_pos volume b hr).trans_le
    (measure_mono hball)
  have hvK : 0 < vK := real_pos_of_compact hKc hpos
  have hfin : volume K < ⊤ := hKc.measure_lt_top
  have hlow' : ∀ y ∈ K, exp (-A) / vK ≤ g y := fun y hy => by
    rw [div_le_iff₀' hvK]; exact hlow y hy
  have hup' : ∀ y ∈ K, g y ≤ exp A / vK := fun y hy => by
    rw [le_div_iff₀' hvK]; exact hup y hy
  have hg0 : ∀ y ∈ K, 0 ≤ g y := fun y hy => (div_pos (exp_pos _) hvK).le.trans (hlow' y hy)
  have hgi : IntegrableOn g K := integrableOn_dens hKm hfin hgm hg0 hup'
  have hgy : IntegrableOn (fun y => g y • y) K :=
    hgi.smul_continuousOn continuous_id.continuousOn hKc
  intro x hx
  by_contra hxK
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hKconv hKc.isClosed hxK
  obtain ⟨p, hp, hmax⟩ := hKc.exists_isMaxOn ⟨b, hbK⟩ f.continuous.continuousOn
  obtain ⟨q, hq, hmin⟩ := hKc.exists_isMinOn ⟨b, hbK⟩ f.continuous.continuousOn
  have hmax' : ∀ y ∈ K, f y ≤ f p := fun y hy => hmax hy
  have hmin' : ∀ y ∈ K, f q ≤ f y := fun y hy => hmin hy
  have hpx : f p < f x := (hfu p hp).trans hux
  -- (1) `f p - f m ≥ e^{-A} (f p - f c)`
  have hfm : f m = ∫ y in K, g y * f y := by
    rw [← f.integral_comp_comm hgy]; simp [map_smul]
  have h1 : exp (-A) * (f p - f (cent K)) ≤ f p - f m := by
    have hFi : IntegrableOn (fun y => g y * (f p - f y)) K :=
      hgi.mul_continuousOn (continuous_const.sub f.continuous).continuousOn hKc
    have e1 : f p - f m = ∫ y in K, g y * (f p - f y) := by
      rw [hfm]
      simp_rw [mul_sub]
      rw [integral_sub (hgi.mul_const _) (hgi.mul_continuousOn f.continuous.continuousOn hKc),
        integral_mul_const, hint, one_mul]
    have e2 : ∫ y in K, exp (-A) / vK * (f p - f y) = exp (-A) * (f p - f (cent K)) := by
      rw [integral_const_mul, integral_sub (integrableOn_const hfin.ne)
        (f.continuous.continuousOn.integrableOn_compact hKc), setIntegral_const, smul_eq_mul,
        show ∫ y in K, f y = f (∫ y in K, y) from
          f.integral_comp_comm (continuous_id.continuousOn.integrableOn_compact hKc),
        map_cent hvK.ne']
      field_simp
      rfl
    rw [e1, ← e2]
    refine setIntegral_mono_on ((continuous_const.sub f.continuous).continuousOn
      |>.integrableOn_compact hKc |>.const_mul _) hFi hKm fun y hy => ?_
    exact mul_le_mul_of_nonneg_right (hlow' y hy) (by linarith [hmax' y hy])
  -- (2) the width is at most `(D + 1) (f p - f c)`
  have h2 : f p - f q ≤ (D + 1) * (f p - f (cent K)) := by
    have hz := hmax' _ (hMR q hq)
    have e : f (cent K - D⁻¹ • (q - cent K)) = f (cent K) - D⁻¹ * (f q - f (cent K)) := by
      simp [map_sub, map_smul, smul_eq_mul]
    rw [e] at hz
    have : D⁻¹ * (f (cent K) - f q) ≤ f p - f (cent K) := by linarith
    rw [inv_mul_le_iff₀ hD] at this
    linarith
  -- (3) the width is at least `2 r ‖v‖`, `v` the Riesz vector of `f`
  set v := (InnerProductSpace.toDual ℝ E).symm f
  have hv : ∀ y, f y = ⟪v, y⟫ := fun y => (InnerProductSpace.toDual_symm_apply).symm
  have hv0 : v ≠ 0 := by
    intro h0; rw [hv, hv, h0, inner_zero_left, inner_zero_left] at hpx; exact lt_irrefl _ hpx
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have h3 : 2 * r * ‖v‖ ≤ f p - f q := by
    have hb1 : b + (r / ‖v‖) • v ∈ K := hball (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr hvn), div_mul_cancel₀ _ hvn.ne'])
    have hb2 : b - (r / ‖v‖) • v ∈ K := hball (by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos (div_pos hr hvn), div_mul_cancel₀ _ hvn.ne'])
    have e1 : f (b + (r / ‖v‖) • v) = f b + r * ‖v‖ := by
      rw [hv, hv, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have e2 : f (b - (r / ‖v‖) • v) = f b - r * ‖v‖ := by
      rw [hv, hv, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have := hmax' _ hb1
    have := hmin' _ hb2
    linarith
  -- (4) `f x ≤ f m + ‖v‖ r_A`
  have h4 : f x - f m ≤ ‖v‖ * (2 * exp (-A) * r / (D + 1)) := by
    rw [← map_sub, hv]
    refine (real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left ?_ hvn.le)
    rw [← dist_eq_norm]; exact hx
  have hA : 0 < exp (-A) := exp_pos _
  have h5 : ‖v‖ * (2 * exp (-A) * r / (D + 1)) ≤ exp (-A) * (f p - f (cent K)) := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    have : exp (-A) * (2 * r * ‖v‖) ≤ exp (-A) * ((D + 1) * (f p - f (cent K))) :=
      mul_le_mul_of_nonneg_left (h3.trans h2) hA.le
    linarith
  linarith

/-- **Lemma 111(a)** (`jl:lem:tilt`). Let `K` be a convex body (compact, convex) in a space of
dimension `d ≥ 1` that contains a closed ball of radius `r > 0`, and let `g` be a measurable
probability density on `K` with `e^{-A} ≤ |K| g ≤ e^A` on `K`. Then the closed ball of radius
`r_A = 2 e^{-A} r / (d + 1)` about the mean of `g` lies in `K`. -/
theorem lemma111a {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) {b : E} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall b r ⊆ K) {A : ℝ} {g : E → ℝ} (hgm : Measurable g)
    (hlow : ∀ y ∈ K, exp (-A) ≤ volume.real K * g y)
    (hup : ∀ y ∈ K, volume.real K * g y ≤ exp A) (hint : ∫ y in K, g y = 1) :
    Metric.closedBall (∫ y in K, g y • y) (2 * exp (-A) * r / (Module.finrank ℝ E + 1)) ⊆ K := by
  have hpos : 0 < volume K := (Metric.measure_closedBall_pos volume b hr).trans_le
    (measure_mono hball)
  by_cases hd : 0 < Module.finrank ℝ E
  swap
  · have : Subsingleton E := Module.finrank_zero_iff (R := ℝ).1 (by omega)
    intro x _
    rw [Subsingleton.elim x b]
    exact hball (Metric.mem_closedBall_self hr.le)
  exact lemma111a_of hKc hKconv hr hball (Nat.cast_pos.2 hd)
    (fun x hx => neg_sub_cent_mem hKc hKconv hpos hd hx) hgm hlow hup hint

end MinkowskiRadon

section Prop106

lemma gibbs_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * log a - a * log b - a + b := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp [hb.le]
  · have hx : 0 < b / a := div_pos hb h
    have hb' : b = a * (b / a) := by field_simp
    have hlog : log b = log a + log (b / a) := by
      conv_lhs => rw [hb']
      rw [log_mul h.ne' hx.ne']
    have := log_le_sub_one_of_pos hx
    rw [hlog]
    have e : a * log a - a * (log a + log (b / a)) - a + b = a * (b / a - 1 - log (b / a)) := by
      field_simp; ring
    rw [e]; exact mul_nonneg h.le (by linarith)

lemma gibbs_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h0 : a * log a - a * log b - a + b = 0) :
    a = b := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp at h0; linarith
  · have hx : 0 < b / a := div_pos hb h
    have hb' : b = a * (b / a) := by field_simp
    have hlog : log b = log a + log (b / a) := by
      conv_lhs => rw [hb']
      rw [log_mul h.ne' hx.ne']
    rw [hlog] at h0
    have e : a * log a - a * (log a + log (b / a)) - a + b = a * (b / a - 1 - log (b / a)) := by
      field_simp; ring
    rw [e] at h0
    have h1 : b / a - 1 - log (b / a) = 0 := (mul_eq_zero.1 h0).resolve_left h.ne'
    by_contra hne
    have hx1 : b / a ≠ 1 := fun h2 => hne (by field_simp at h2; linarith)
    have := log_lt_sub_one_of_pos hx hx1
    linarith

variable {α : Type*} [MeasurableSpace α] {lam : Measure α}

/-- A nonnegative measurable density of a probability measure is integrable with integral 1. -/
lemma density_prob {w : α → ℝ} (hwm : Measurable w) (hw0 : 0 ≤ᵐ[lam] w)
    (hP : IsProbabilityMeasure (lam.withDensity fun x => ENNReal.ofReal (w x))) :
    Integrable w lam ∧ ∫ x, w x ∂lam = 1 := by
  have h1 : ∫⁻ x, ENNReal.ofReal (w x) ∂lam = 1 := by
    have := hP.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hi : Integrable w lam := ⟨hwm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hw0).2 (by rw [h1]; exact ENNReal.one_lt_top)⟩
  refine ⟨hi, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hi hw0
  rwa [h1, ENNReal.ofReal_eq_one] at this

lemma integral_density {w : α → ℝ} (hwm : Measurable w) (hw0 : 0 ≤ᵐ[lam] w) (g : α → ℝ) :
    ∫ x, g x ∂(lam.withDensity fun x => ENNReal.ofReal (w x)) = ∫ x, w x * g x ∂lam := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hwm.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hw0] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

variable {n : ℕ} {K : Set E} {h : E → ℝ}

/-- The density `w_h(x) = ∏ᵢ h(xᵢ) / ∫ ∏ᵢ h(yᵢ) dλ(y)` of the conditioned product with respect to
a reference measure `λ` on tuples (in the paper, Lebesgue measure on `𝒯_n(K)`, for which the
normalising constant is `h^{*n}(0)`). -/
def condProd (lam : Measure (Fin n → E)) (h : E → ℝ) (x : Fin n → E) : ℝ :=
  (∏ i, h (x i)) / ∫ y, ∏ i, h (y i) ∂lam

lemma log_condProd (lam : Measure (Fin n → E)) {a : ℝ} (ha : 0 < a) (hlo : ∀ y ∈ K, a ≤ h y)
    (hZ : 0 < ∫ y, ∏ i, h (y i) ∂lam) {x : Fin n → E} (hx : ∀ i, x i ∈ K) :
    log (condProd lam h x) = ∑ i, log (h (x i)) - log (∫ y, ∏ i, h (y i) ∂lam) := by
  have hpos : ∀ i, 0 < h (x i) := fun i => ha.trans_le (hlo _ (hx i))
  rw [condProd, log_div (Finset.prod_pos fun i _ => hpos i).ne' hZ.ne',
    log_prod fun i _ => (hpos i).ne']

/-- `∫ log w_h dβ` is the same for every probability measure `β` on `Kⁿ` with marginals `U(K)`. -/
lemma integral_log_condProd (lam : Measure (Fin n → E)) (hm : Measurable h) {a b : ℝ}
    (ha : 0 < a) (hlo : ∀ y ∈ K, a ≤ h y) (hhi : ∀ y ∈ K, h y ≤ b)
    (hZ : 0 < ∫ y, ∏ i, h (y i) ∂lam) (β : Measure (Fin n → E)) [IsProbabilityMeasure β]
    (hβK : ∀ᵐ x ∂β, ∀ i, x i ∈ K) (hmarg : ∀ i, β.map (fun x => x i) = unifSet K) :
    ∫ x, log (condProd lam h x) ∂β =
      ∑ _i : Fin n, ∫ y, log (h y) ∂(unifSet K) - log (∫ y, ∏ i, h (y i) ∂lam) := by
  set Lb := max |log a| |log b|
  have hlogh : ∀ y ∈ K, |log (h y)| ≤ Lb := fun y hy =>
    abs_le_max_abs_abs (log_le_log ha (hlo y hy)) (log_le_log (ha.trans_le (hlo y hy)) (hhi y hy))
  have hpt : ∀ᵐ x ∂β, log (condProd lam h x) =
      ∑ i, log (h (x i)) - log (∫ y, ∏ i, h (y i) ∂lam) := by
    filter_upwards [hβK] with x hx using log_condProd lam ha hlo hZ hx
  have hint : ∀ i, Integrable (fun x : Fin n → E => log (h (x i))) β := fun i =>
    Integrable.mono' (integrable_const Lb)
      (hm.log.comp (measurable_pi_apply i)).aestronglyMeasurable
      (by filter_upwards [hβK] with x hx; exact hlogh _ (hx i))
  rw [integral_congr_ae hpt, integral_sub (integrable_finsetSum _ fun i _ => hint i)
    (integrable_const _), integral_finsetSum _ fun i _ => hint i, integral_const, probReal_univ,
    one_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmarg i, integral_map (measurable_pi_apply i).aemeasurable hm.log.aestronglyMeasurable]

/-- **Proposition 106** (`lg:prop:entropy`), first statement. Let `λ` be a finite reference
measure on `n`-tuples concentrated on `Kⁿ` (in the paper, Lebesgue measure on `𝒯_n(K)`), and `h`
a measurable function with `0 < a ≤ h ≤ b` on `K`, whose conditioned product `β_h` (density
`w_h = condProd λ h`) is an `n`-complete mix of `U(K)`. Then among all `n`-complete mixes of
`U(K)` with a density `w` with respect to `λ` for which `w log w` is integrable, `β_h` has the
largest entropy `-∫ w log w dλ`, and it is the only maximiser (up to `λ`-null sets). -/
theorem prop106 (lam : Measure (Fin n → E)) [IsFiniteMeasure lam] (hm : Measurable h) {a b : ℝ}
    (ha : 0 < a) (hlo : ∀ y ∈ K, a ≤ h y) (hhi : ∀ y ∈ K, h y ≤ b)
    (hlamK : ∀ᵐ x ∂lam, ∀ i, x i ∈ K)
    (hmix : IsCompleteMix n (unifSet K)
      (lam.withDensity fun x => ENNReal.ofReal (condProd lam h x)))
    (w : (Fin n → E) → ℝ) (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwmix : IsCompleteMix n (unifSet K) (lam.withDensity fun x => ENNReal.ofReal (w x)))
    (hwlog : Integrable (fun x => w x * log (w x)) lam) :
    -∫ x, w x * log (w x) ∂lam ≤ -∫ x, condProd lam h x * log (condProd lam h x) ∂lam ∧
    (-∫ x, w x * log (w x) ∂lam = -∫ x, condProd lam h x * log (condProd lam h x) ∂lam ↔
      w =ᵐ[lam] condProd lam h) := by
  set Z := ∫ y, ∏ i, h (y i) ∂lam with hZdef
  set wh := condProd lam h with hwh
  have hprodm : Measurable fun x : Fin n → E => ∏ i, h (x i) :=
    Finset.measurable_prod _ fun i _ => hm.comp (measurable_pi_apply i)
  have hwhm : Measurable wh := hprodm.div_const _
  have hZ0 : 0 ≤ Z := integral_nonneg_of_ae (by
    filter_upwards [hlamK] with x hx
    exact Finset.prod_nonneg fun i _ => ha.le.trans (hlo _ (hx i)))
  have hZpos : 0 < Z := by
    rcases hZ0.eq_or_lt with h0 | h0
    · exfalso
      have := hmix.1.measure_univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      simp [wh, condProd, ← hZdef, ← h0] at this
    · exact h0
  have hwhpos : ∀ᵐ x ∂lam, 0 < wh x := by
    filter_upwards [hlamK] with x hx
    exact div_pos (Finset.prod_pos fun i _ => ha.trans_le (hlo _ (hx i))) hZpos
  have hwh0 : 0 ≤ᵐ[lam] wh := hwhpos.mono fun x hx => hx.le
  have hw0' : 0 ≤ᵐ[lam] w := Filter.Eventually.of_forall hw0
  obtain ⟨hwi, hw1⟩ := density_prob hwm hw0' hwmix.1
  obtain ⟨hwhi, hwh1⟩ := density_prob hwhm hwh0 hmix.1
  -- `log w_h` is bounded `λ`-almost everywhere
  set Lb := max |log a| |log b|
  have hlogh : ∀ y ∈ K, |log (h y)| ≤ Lb := fun y hy =>
    abs_le_max_abs_abs (log_le_log ha (hlo y hy)) (log_le_log (ha.trans_le (hlo y hy)) (hhi y hy))
  have hbound : ∀ᵐ x ∂lam, ‖log (wh x)‖ ≤ n * Lb + |log Z| := by
    filter_upwards [hlamK] with x hx
    rw [Real.norm_eq_abs, hwh, log_condProd lam ha hlo hZpos hx]
    calc |∑ i, log (h (x i)) - log Z| ≤ |∑ i, log (h (x i))| + |log Z| := abs_sub _ _
      _ ≤ ∑ i, |log (h (x i))| + |log Z| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, Lb + |log Z| := by gcongr with i; exact hlogh _ (hx i)
      _ = n * Lb + |log Z| := by simp
  have hI1 : Integrable (fun x => w x * log (wh x)) lam :=
    (hwi.bdd_mul hwhm.log.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hI2 : Integrable (fun x => wh x * log (wh x)) lam :=
    (hwhi.bdd_mul hwhm.log.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  -- the cross term is the same for all complete mixes
  have hcross : ∫ x, w x * log (wh x) ∂lam = ∫ x, wh x * log (wh x) ∂lam := by
    rw [← integral_density hwm hw0', ← integral_density hwhm hwh0]
    have : IsProbabilityMeasure (lam.withDensity fun x => ENNReal.ofReal (w x)) := hwmix.1
    have : IsProbabilityMeasure (lam.withDensity fun x => ENNReal.ofReal (wh x)) := hmix.1
    rw [integral_log_condProd lam hm ha hlo hhi hZpos _
        ((withDensity_absolutelyContinuous _ _).ae_le hlamK) hwmix.2.2,
      integral_log_condProd lam hm ha hlo hhi hZpos _
        ((withDensity_absolutelyContinuous _ _).ae_le hlamK) hmix.2.2]
  -- Gibbs' inequality
  set G := fun x => w x * log (w x) - w x * log (wh x) - w x + wh x with hG
  have hG0 : 0 ≤ᵐ[lam] G := by
    filter_upwards [hwhpos] with x hx using gibbs_nonneg (hw0 x) hx
  have hGi : Integrable G lam := ((hwlog.sub hI1).sub hwi).add hwhi
  have hGint : ∫ x, G x ∂lam =
      ∫ x, w x * log (w x) ∂lam - ∫ x, wh x * log (wh x) ∂lam := by
    have hA : Integrable (fun x => w x * log (w x) - w x * log (wh x)) lam := hwlog.sub hI1
    have hB : Integrable (fun x => w x * log (w x) - w x * log (wh x) - w x) lam := hA.sub hwi
    simp only [hG]
    rw [integral_add hB hwhi, integral_sub hA hwi, integral_sub hwlog hI1, hw1, hwh1, hcross]
    ring
  have hpos := integral_nonneg_of_ae hG0
  refine ⟨by linarith, ⟨fun heq => ?_, fun heq => ?_⟩⟩
  · have h0 : ∫ x, G x ∂lam = 0 := by linarith
    have := (integral_eq_zero_iff_of_nonneg_ae hG0 hGi).1 h0
    filter_upwards [this, hwhpos] with x hx hxpos using gibbs_eq (hw0 x) hxpos hx
  · have h0 : G =ᵐ[lam] 0 := by
      filter_upwards [heq] with x hx
      simp only [hG, Pi.zero_apply, hx]; ring
    have := integral_congr_ae h0
    simp only [Pi.zero_apply, integral_zero] at this
    linarith

/-- Proposition 106, first step of the uniqueness of `h`: if two conditioned products agree
`λ`-almost everywhere, then `∑ᵢ φ(xᵢ)` is `λ`-almost everywhere constant for
`φ = log h' - log h`. The remaining step of the paper (`φ` is affine when `as(K) < n - 1`, by the
kernel argument of Theorem 91 with Lemma 89) is not formalised. -/
theorem prop106_kernel (lam : Measure (Fin n → E)) {h' : E → ℝ} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ y ∈ K, a ≤ h y) (hlo' : ∀ y ∈ K, a ≤ h' y) (hlamK : ∀ᵐ x ∂lam, ∀ i, x i ∈ K)
    (hZ : 0 < ∫ y, ∏ i, h (y i) ∂lam) (hZ' : 0 < ∫ y, ∏ i, h' (y i) ∂lam)
    (heq : condProd lam h' =ᵐ[lam] condProd lam h) :
    ∀ᵐ x ∂lam, ∑ i, (log (h' (x i)) - log (h (x i))) =
      log (∫ y, ∏ i, h' (y i) ∂lam) - log (∫ y, ∏ i, h (y i) ∂lam) := by
  filter_upwards [heq, hlamK] with x hx hxK
  have h1 := log_condProd lam ha hlo' hZ' hxK
  have h2 := log_condProd lam ha hlo hZ hxK
  rw [hx, h2] at h1
  rw [Finset.sum_sub_distrib]
  linarith

/-- The density `w_h(x) = ∏ⱼ hⱼ(xⱼ) / ∫ ∏ⱼ hⱼ(yⱼ) dλ(y)` of the conditioned product of different
densities with respect to a reference measure `λ` on tuples (in the paper, Lebesgue measure on
`𝒯(K₁, …, Kₙ; s)`, for which the normalising constant is `f(s)`, `f = h₁ * ⋯ * hₙ`). -/
def condProdJ (lam : Measure (Fin n → E)) (h : Fin n → E → ℝ) (x : Fin n → E) : ℝ :=
  (∏ i, h i (x i)) / ∫ y, ∏ i, h i (y i) ∂lam

lemma log_condProdJ (lam : Measure (Fin n → E)) {Ks : Fin n → Set E} {hs : Fin n → E → ℝ}
    {a : ℝ} (ha : 0 < a) (hlo : ∀ i, ∀ y ∈ Ks i, a ≤ hs i y)
    (hZ : 0 < ∫ y, ∏ i, hs i (y i) ∂lam) {x : Fin n → E} (hx : ∀ i, x i ∈ Ks i) :
    log (condProdJ lam hs x) = ∑ i, log (hs i (x i)) - log (∫ y, ∏ i, hs i (y i) ∂lam) := by
  have hpos : ∀ i, 0 < hs i (x i) := fun i => ha.trans_le (hlo i _ (hx i))
  rw [condProdJ, log_div (Finset.prod_pos fun i _ => hpos i).ne' hZ.ne',
    log_prod fun i _ => (hpos i).ne']

/-- `∫ log w_h dβ` is the same for every probability measure `β` on `∏ Kⱼ` with marginals `Fⱼ`. -/
lemma integral_log_condProdJ (lam : Measure (Fin n → E)) {Ks : Fin n → Set E}
    {hs : Fin n → E → ℝ} (hm : ∀ i, Measurable (hs i)) {a b : ℝ}
    (ha : 0 < a) (hlo : ∀ i, ∀ y ∈ Ks i, a ≤ hs i y) (hhi : ∀ i, ∀ y ∈ Ks i, hs i y ≤ b)
    (hZ : 0 < ∫ y, ∏ i, hs i (y i) ∂lam) (F : Fin n → Measure E) (β : Measure (Fin n → E))
    [IsProbabilityMeasure β] (hβK : ∀ᵐ x ∂β, ∀ i, x i ∈ Ks i)
    (hmarg : ∀ i, β.map (fun x => x i) = F i) :
    ∫ x, log (condProdJ lam hs x) ∂β =
      ∑ i, ∫ y, log (hs i y) ∂(F i) - log (∫ y, ∏ i, hs i (y i) ∂lam) := by
  set Lb := max |log a| |log b|
  have hlogh : ∀ i, ∀ y ∈ Ks i, |log (hs i y)| ≤ Lb := fun i y hy =>
    abs_le_max_abs_abs (log_le_log ha (hlo i y hy))
      (log_le_log (ha.trans_le (hlo i y hy)) (hhi i y hy))
  have hpt : ∀ᵐ x ∂β, log (condProdJ lam hs x) =
      ∑ i, log (hs i (x i)) - log (∫ y, ∏ i, hs i (y i) ∂lam) := by
    filter_upwards [hβK] with x hx using log_condProdJ lam ha hlo hZ hx
  have hint : ∀ i, Integrable (fun x : Fin n → E => log (hs i (x i))) β := fun i =>
    Integrable.mono' (integrable_const Lb)
      ((hm i).log.comp (measurable_pi_apply i)).aestronglyMeasurable
      (by filter_upwards [hβK] with x hx; exact hlogh i _ (hx i))
  rw [integral_congr_ae hpt, integral_sub (integrable_finsetSum _ fun i _ => hint i)
    (integrable_const _), integral_finsetSum _ fun i _ => hint i, integral_const, probReal_univ,
    one_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmarg i, integral_map (measurable_pi_apply i).aemeasurable
    (hm i).log.aestronglyMeasurable]

/-- **Proposition 116** (`jl:prop:entropy`). Let `λ` be a finite reference measure on `n`-tuples
concentrated on `K₁ × ⋯ × Kₙ` (in the paper, Lebesgue measure on `𝒯(K₁, …, Kₙ; s)`), and `hⱼ`
measurable functions with `0 < a ≤ hⱼ ≤ b` on `Kⱼ`, whose conditioned product `β_h` (density
`w_h = condProdJ λ h`) is a joint mix of `F₁, …, Fₙ`. Then among all joint mixes of
`F₁, …, Fₙ` with a density `w` with respect to `λ` for which `w log w` is integrable, `β_h` has
the largest entropy `-∫ w log w dλ`, and it is the only maximiser (up to `λ`-null sets).
(The sum `s` is fixed by the support of `λ`.) -/
theorem prop116 (lam : Measure (Fin n → E)) [IsFiniteMeasure lam] {Ks : Fin n → Set E}
    {hs : Fin n → E → ℝ} (hm : ∀ i, Measurable (hs i)) {a b : ℝ}
    (ha : 0 < a) (hlo : ∀ i, ∀ y ∈ Ks i, a ≤ hs i y) (hhi : ∀ i, ∀ y ∈ Ks i, hs i y ≤ b)
    (hlamK : ∀ᵐ x ∂lam, ∀ i, x i ∈ Ks i) (F : Fin n → Measure E)
    (hmix : IsJointMix F (lam.withDensity fun x => ENNReal.ofReal (condProdJ lam hs x)))
    (w : (Fin n → E) → ℝ) (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwmix : IsJointMix F (lam.withDensity fun x => ENNReal.ofReal (w x)))
    (hwlog : Integrable (fun x => w x * log (w x)) lam) :
    -∫ x, w x * log (w x) ∂lam ≤ -∫ x, condProdJ lam hs x * log (condProdJ lam hs x) ∂lam ∧
    (-∫ x, w x * log (w x) ∂lam = -∫ x, condProdJ lam hs x * log (condProdJ lam hs x) ∂lam ↔
      w =ᵐ[lam] condProdJ lam hs) := by
  set Z := ∫ y, ∏ i, hs i (y i) ∂lam with hZdef
  set wh := condProdJ lam hs with hwh
  have hprodm : Measurable fun x : Fin n → E => ∏ i, hs i (x i) :=
    Finset.measurable_prod _ fun i _ => (hm i).comp (measurable_pi_apply i)
  have hwhm : Measurable wh := hprodm.div_const _
  have hZ0 : 0 ≤ Z := integral_nonneg_of_ae (by
    filter_upwards [hlamK] with x hx
    exact Finset.prod_nonneg fun i _ => ha.le.trans (hlo i _ (hx i)))
  have hZpos : 0 < Z := by
    rcases hZ0.eq_or_lt with h0 | h0
    · exfalso
      have := hmix.1.measure_univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      simp [wh, condProdJ, ← hZdef, ← h0] at this
    · exact h0
  have hwhpos : ∀ᵐ x ∂lam, 0 < wh x := by
    filter_upwards [hlamK] with x hx
    exact div_pos (Finset.prod_pos fun i _ => ha.trans_le (hlo i _ (hx i))) hZpos
  have hwh0 : 0 ≤ᵐ[lam] wh := hwhpos.mono fun x hx => hx.le
  have hw0' : 0 ≤ᵐ[lam] w := Filter.Eventually.of_forall hw0
  obtain ⟨hwi, hw1⟩ := density_prob hwm hw0' hwmix.1
  obtain ⟨hwhi, hwh1⟩ := density_prob hwhm hwh0 hmix.1
  set Lb := max |log a| |log b|
  have hlogh : ∀ i, ∀ y ∈ Ks i, |log (hs i y)| ≤ Lb := fun i y hy =>
    abs_le_max_abs_abs (log_le_log ha (hlo i y hy))
      (log_le_log (ha.trans_le (hlo i y hy)) (hhi i y hy))
  have hbound : ∀ᵐ x ∂lam, ‖log (wh x)‖ ≤ n * Lb + |log Z| := by
    filter_upwards [hlamK] with x hx
    rw [Real.norm_eq_abs, hwh, log_condProdJ lam ha hlo hZpos hx]
    calc |∑ i, log (hs i (x i)) - log Z| ≤ |∑ i, log (hs i (x i))| + |log Z| := abs_sub _ _
      _ ≤ ∑ i, |log (hs i (x i))| + |log Z| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, Lb + |log Z| := by gcongr with i; exact hlogh i _ (hx i)
      _ = n * Lb + |log Z| := by simp
  have hI1 : Integrable (fun x => w x * log (wh x)) lam :=
    (hwi.bdd_mul hwhm.log.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hI2 : Integrable (fun x => wh x * log (wh x)) lam :=
    (hwhi.bdd_mul hwhm.log.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hcross : ∫ x, w x * log (wh x) ∂lam = ∫ x, wh x * log (wh x) ∂lam := by
    rw [← integral_density hwm hw0', ← integral_density hwhm hwh0]
    have : IsProbabilityMeasure (lam.withDensity fun x => ENNReal.ofReal (w x)) := hwmix.1
    have : IsProbabilityMeasure (lam.withDensity fun x => ENNReal.ofReal (wh x)) := hmix.1
    rw [integral_log_condProdJ lam hm ha hlo hhi hZpos F _
        ((withDensity_absolutelyContinuous _ _).ae_le hlamK) hwmix.2.2,
      integral_log_condProdJ lam hm ha hlo hhi hZpos F _
        ((withDensity_absolutelyContinuous _ _).ae_le hlamK) hmix.2.2]
  set G := fun x => w x * log (w x) - w x * log (wh x) - w x + wh x with hG
  have hG0 : 0 ≤ᵐ[lam] G := by
    filter_upwards [hwhpos] with x hx using gibbs_nonneg (hw0 x) hx
  have hGi : Integrable G lam := ((hwlog.sub hI1).sub hwi).add hwhi
  have hGint : ∫ x, G x ∂lam =
      ∫ x, w x * log (w x) ∂lam - ∫ x, wh x * log (wh x) ∂lam := by
    have hA : Integrable (fun x => w x * log (w x) - w x * log (wh x)) lam := hwlog.sub hI1
    have hB : Integrable (fun x => w x * log (w x) - w x * log (wh x) - w x) lam := hA.sub hwi
    simp only [hG]
    rw [integral_add hB hwhi, integral_sub hA hwi, integral_sub hwlog hI1, hw1, hwh1, hcross]
    ring
  have hpos := integral_nonneg_of_ae hG0
  refine ⟨by linarith, ⟨fun heq => ?_, fun heq => ?_⟩⟩
  · have h0 : ∫ x, G x ∂lam = 0 := by linarith
    have := (integral_eq_zero_iff_of_nonneg_ae hG0 hGi).1 h0
    filter_upwards [this, hwhpos] with x hx hxpos using gibbs_eq (hw0 x) hxpos hx
  · have h0 : G =ᵐ[lam] 0 := by
      filter_upwards [heq] with x hx
      simp only [hG, Pi.zero_apply, hx]; ring
    have := integral_congr_ae h0
    simp only [Pi.zero_apply, integral_zero] at this
    linarith

/-- The kernel property used for the uniqueness of `h` in Proposition 106, stated as a hypothesis
(the kernel argument for `G₀` in the proof of Theorem 91, with Lemma 89, under `as(K) < n - 1`):
every measurable function `φ`, bounded on `K`, with `∑ᵢ φ(xᵢ) = 0` for `λ`-almost every tuple, is
almost everywhere on `K` equal to an affine function. -/
def KernelAffine (lam : Measure (Fin n → E)) (K : Set E) : Prop :=
  ∀ φ : E → ℝ, Measurable φ → (∃ C, ∀ y ∈ K, |φ y| ≤ C) →
    (∀ᵐ x ∂lam, ∑ i, φ (x i) = 0) →
    ∃ (c : ℝ) (v : E), ∀ᵐ y ∂(volume.restrict K), φ y = c + ⟪v, y⟫

lemma condProd_bounds (lam : Measure (Fin n → E)) {a b : ℝ} (ha : 0 < a)
    (hlo : ∀ y ∈ K, a ≤ h y) (hhi : ∀ y ∈ K, h y ≤ b) (hZ : 0 < ∫ y, ∏ i, h (y i) ∂lam)
    {x : Fin n → E} (hx : ∀ i, x i ∈ K) :
    a ^ n / (∫ y, ∏ i, h (y i) ∂lam) ≤ condProd lam h x ∧
      condProd lam h x ≤ b ^ n / (∫ y, ∏ i, h (y i) ∂lam) := by
  have h1 : a ^ n ≤ ∏ i, h (x i) := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => a) (g := fun i => h (x i))
      (fun i _ => ha.le) (fun i _ => hlo _ (hx i))
    simpa using this
  have h2 : ∏ i, h (x i) ≤ b ^ n := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun i => h (x i)) (g := fun _ => b)
      (fun i _ => ha.le.trans (hlo _ (hx i))) (fun i _ => hhi _ (hx i))
    simpa using this
  exact ⟨div_le_div_of_nonneg_right h1 hZ.le, div_le_div_of_nonneg_right h2 hZ.le⟩

/-- `w log w` is integrable for the density of a conditioned product (bounded below and above
on `Kⁿ`, `λ` finite). -/
lemma integrable_condProd_log (lam : Measure (Fin n → E)) [IsFiniteMeasure lam]
    (hm : Measurable h) {a b : ℝ} (ha : 0 < a) (hlo : ∀ y ∈ K, a ≤ h y)
    (hhi : ∀ y ∈ K, h y ≤ b) (hZ : 0 < ∫ y, ∏ i, h (y i) ∂lam)
    (hlamK : ∀ᵐ x ∂lam, ∀ i, x i ∈ K) :
    Integrable (fun x => max (condProd lam h x) 0 * log (max (condProd lam h x) 0)) lam := by
  set Z := ∫ y, ∏ i, h (y i) ∂lam
  set lo := a ^ n / Z
  set hi := b ^ n / Z
  have hlo0 : 0 < lo := div_pos (pow_pos ha n) hZ
  have hwm : Measurable (condProd lam h) :=
    (Finset.measurable_prod _ fun i _ => hm.comp (measurable_pi_apply i)).div_const _
  refine Integrable.mono' (integrable_const (hi * max |log lo| |log hi|)) ?_ ?_
  · exact ((hwm.max measurable_const).mul (hwm.max measurable_const).log).aestronglyMeasurable
  · filter_upwards [hlamK] with x hx
    obtain ⟨h1, h2⟩ := condProd_bounds lam ha hlo hhi hZ hx
    have hw0 : 0 < condProd lam h x := hlo0.trans_le h1
    rw [max_eq_left hw0.le, Real.norm_eq_abs, abs_mul, abs_of_pos hw0]
    exact mul_le_mul h2 (abs_le_max_abs_abs (log_le_log hlo0 h1) (log_le_log hw0 h2))
      (abs_nonneg _) (hlo0.le.trans (h1.trans h2))

/-- **Proposition 106**, uniqueness of `h`, given the kernel property `KernelAffine` (the kernel
argument of Theorem 91 with Lemma 89, valid when `as(K) < n - 1`). If the conditioned products
of `h` and `h'` (both bounded and bounded below on `K`) are `n`-complete mixes of `U(K)`, `n ≥ 1`,
then `h' = h e^{c + ⟪v, ·⟫}` almost everywhere on `K` for some `c` and `v`. -/
theorem prop106_unique (lam : Measure (Fin n → E)) [IsFiniteMeasure lam] (hn : 0 < n)
    (hKm : MeasurableSet K) {h' : E → ℝ} (hm : Measurable h) (hm' : Measurable h') {a b : ℝ}
    (ha : 0 < a) (hlo : ∀ y ∈ K, a ≤ h y) (hhi : ∀ y ∈ K, h y ≤ b) (hlo' : ∀ y ∈ K, a ≤ h' y)
    (hhi' : ∀ y ∈ K, h' y ≤ b) (hlamK : ∀ᵐ x ∂lam, ∀ i, x i ∈ K)
    (hmix : IsCompleteMix n (unifSet K)
      (lam.withDensity fun x => ENNReal.ofReal (condProd lam h x)))
    (hmix' : IsCompleteMix n (unifSet K)
      (lam.withDensity fun x => ENNReal.ofReal (condProd lam h' x)))
    (hker : KernelAffine lam K) :
    ∃ (c : ℝ) (v : E), ∀ᵐ y ∂(volume.restrict K), h' y = h y * exp (c + ⟪v, y⟫) := by
  -- normalising constants are positive
  have hZpos : ∀ {k : E → ℝ}, (∀ y ∈ K, a ≤ k y) →
      IsCompleteMix n (unifSet K) (lam.withDensity fun x => ENNReal.ofReal (condProd lam k x)) →
      0 < ∫ y, ∏ i, k (y i) ∂lam := by
    intro k hk hmk
    have hZ0 : 0 ≤ ∫ y, ∏ i, k (y i) ∂lam := integral_nonneg_of_ae (by
      filter_upwards [hlamK] with x hx
      exact Finset.prod_nonneg fun i _ => ha.le.trans (hk _ (hx i)))
    rcases hZ0.eq_or_lt with h0 | h0
    · exfalso
      have := hmk.1.measure_univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      simp [condProd, ← h0] at this
    · exact h0
  have hZ := hZpos hlo hmix
  have hZ' := hZpos hlo' hmix'
  set w := condProd lam h
  set w' := condProd lam h'
  have hwm : Measurable w :=
    (Finset.measurable_prod _ fun i _ => hm.comp (measurable_pi_apply i)).div_const _
  have hwm' : Measurable w' :=
    (Finset.measurable_prod _ fun i _ => hm'.comp (measurable_pi_apply i)).div_const _
  -- the clipped densities define the same measures
  have hclip : ∀ u : (Fin n → E) → ℝ, (fun x => ENNReal.ofReal (max (u x) 0)) =
      fun x => ENNReal.ofReal (u x) := fun u => funext fun x => by
    rcases le_total (u x) 0 with h0 | h0
    · rw [max_eq_right h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]
    · rw [max_eq_left h0]
  have hae : ∀ {k : E → ℝ}, (∀ y ∈ K, a ≤ k y) →
      (fun x => max (condProd lam k x) 0) =ᵐ[lam] condProd lam k := by
    intro k hk
    filter_upwards [hlamK] with x hx
    exact max_eq_left (div_nonneg (Finset.prod_nonneg fun i _ => ha.le.trans (hk _ (hx i)))
      (integral_nonneg_of_ae (by
        filter_upwards [hlamK] with y hy
        exact Finset.prod_nonneg fun i _ => ha.le.trans (hk _ (hy i)))))
  have hent : ∀ {k : E → ℝ}, (∀ y ∈ K, a ≤ k y) →
      ∫ x, max (condProd lam k x) 0 * log (max (condProd lam k x) 0) ∂lam =
        ∫ x, condProd lam k x * log (condProd lam k x) ∂lam := by
    intro k hk
    refine integral_congr_ae ?_
    filter_upwards [hae hk] with x hx
    rw [hx]
  have hA := prop106 lam hm ha hlo hhi hlamK hmix (fun x => max (w' x) 0)
    (hwm'.max measurable_const) (fun x => le_max_right _ _) (by rw [hclip]; exact hmix')
    (integrable_condProd_log lam hm' ha hlo' hhi' hZ' hlamK)
  have hB := prop106 lam hm' ha hlo' hhi' hlamK hmix' (fun x => max (w x) 0)
    (hwm.max measurable_const) (fun x => le_max_right _ _) (by rw [hclip]; exact hmix)
    (integrable_condProd_log lam hm ha hlo hhi hZ hlamK)
  rw [hent hlo'] at hA
  rw [hent hlo] at hB
  have heq' : (fun x => max (w' x) 0) =ᵐ[lam] w := hA.2.1 (le_antisymm hA.1 hB.1)
  have heq : w' =ᵐ[lam] w := (hae hlo').symm.trans heq'
  -- `∑ φ(xᵢ)` is constant, hence `φ` is affine
  have hk := prop106_kernel lam ha hlo hlo' hlamK hZ hZ' heq
  set C := log (∫ y, ∏ i, h' (y i) ∂lam) - log (∫ y, ∏ i, h (y i) ∂lam)
  set φ : E → ℝ := fun y => log (h' y) - log (h y) - C / n
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨c, v, hφ⟩ := hker φ ((hm'.log.sub hm.log).sub measurable_const)
    ⟨max |log a| |log b| + max |log a| |log b| + |C / n|, fun y hy => by
      have h1 := abs_le_max_abs_abs (log_le_log ha (hlo y hy))
        (log_le_log (ha.trans_le (hlo y hy)) (hhi y hy))
      have h2 := abs_le_max_abs_abs (log_le_log ha (hlo' y hy))
        (log_le_log (ha.trans_le (hlo' y hy)) (hhi' y hy))
      calc |φ y| ≤ |log (h' y) - log (h y)| + |C / n| := abs_sub _ _
        _ ≤ |log (h' y)| + |log (h y)| + |C / n| := by gcongr; exact abs_sub _ _
        _ ≤ _ := by linarith⟩
    (by
      filter_upwards [hk] with x hx
      simp only [φ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_sub_distrib] at hx
      rw [hx]; field_simp; ring)
  refine ⟨c + C / n, v, ?_⟩
  filter_upwards [hφ, ae_restrict_mem hKm] with y hy hyK
  have hp : 0 < h y := ha.trans_le (hlo y hyK)
  have hp' : 0 < h' y := ha.trans_le (hlo' y hyK)
  have : log (h' y) = log (h y) + (c + C / n + ⟪v, y⟫) := by
    simp only [φ] at hy; linarith
  rw [← exp_log hp', this, exp_add, exp_log hp]

/-- The last sentence of Proposition 116: the relative entropy of `β = w λ` with respect to the
normalised reference measure `λ / λ(𝒯)` is `∫ w log w dλ + log λ(𝒯)`, so maximising the entropy
is minimising this relative entropy (the I-projection of `λ / λ(𝒯)`). -/
lemma relEntropy_normalised {α : Type*} [MeasurableSpace α] (lam : Measure α)
    [IsFiniteMeasure lam] {w : α → ℝ} (hwi : Integrable w lam) (hw1 : ∫ x, w x ∂lam = 1)
    (hwlog : Integrable (fun x => w x * log (w x)) lam) (hpos : 0 < lam.real Set.univ) :
    ∫ x, w x * log (w x / (lam.real Set.univ)⁻¹) ∂lam =
      ∫ x, w x * log (w x) ∂lam + log (lam.real Set.univ) := by
  set c := lam.real Set.univ
  have hpt : ∀ x, w x * log (w x / c⁻¹) = w x * log (w x) + w x * log c := fun x => by
    rcases eq_or_ne (w x) 0 with h0 | h0
    · simp [h0]
    · rw [div_inv_eq_mul, log_mul h0 hpos.ne', mul_add]
  simp_rw [hpt]
  rw [integral_add hwlog (hwi.mul_const _), integral_mul_const, hw1, one_mul]

end Prop106

open Filter Topology

variable [(volume : Measure E).IsAddHaarMeasure]

section Affine

/-- The affine bijection `x ↦ L x + t`. -/
def aff (L : E ≃L[ℝ] E) (t : E) (x : E) : E := L x + t

/-- `x ↦ L x + t` as a measurable equivalence. -/
def affE (L : E ≃L[ℝ] E) (t : E) : E ≃ᵐ E :=
  (L.toHomeomorph.trans (Homeomorph.addRight t)).toMeasurableEquiv

@[simp] lemma affE_apply (L : E ≃L[ℝ] E) (t x : E) : affE L t x = L x + t := rfl

@[simp] lemma affE_symm_apply (L : E ≃L[ℝ] E) (t y : E) : (affE L t).symm y = L.symm (y - t) := by
  rw [MeasurableEquiv.symm_apply_eq]; simp

/-- The absolute value of the determinant of `L`. -/
def jac (L : E ≃L[ℝ] E) : ℝ := |LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E)|

lemma det_ne_zero (L : E ≃L[ℝ] E) : LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0 :=
  (L.toLinearEquiv.isUnit_det').ne_zero

lemma jac_pos (L : E ≃L[ℝ] E) : 0 < jac L := abs_pos.2 (det_ne_zero L)

lemma map_volume_affE (L : E ≃L[ℝ] E) (t : E) :
    (volume : Measure E).map (affE L t) = ENNReal.ofReal (jac L)⁻¹ • volume := by
  have h1 : (affE L t : E → E) = (fun x => x + t) ∘ (L : E → E) := rfl
  rw [h1, ← Measure.map_map (measurable_add_const t) L.continuous.measurable]
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) (det_ne_zero L)
  have h3 : ((((L : E →L[ℝ] E) : E →ₗ[ℝ] E)) : E → E) = (L : E → E) := rfl
  rw [h3] at h2
  rw [h2, Measure.map_smul, map_add_right_eq_self, jac,
    abs_inv]
  exact (measurable_add_const t).aemeasurable

/-- Change of variables for an affine bijection. -/
lemma integral_comp_affE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] E)
    (t : E) (f : E → F) : ∫ x, f (L x + t) = (jac L)⁻¹ • ∫ y, f y := by
  have := integral_map_equiv (μ := (volume : Measure E)) (affE L t) f
  simp only [affE_apply] at this
  rw [← this, map_volume_affE, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 (jac_pos L).le)]

lemma integral_comp_affE_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] E) (t : E) (f : E → F) : ∫ y, f (L.symm (y - t)) = jac L • ∫ x, f x := by
  have h := integral_comp_affE L t (fun y => f (L.symm (y - t)))
  simp only [add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply] at h
  rw [h, smul_smul, mul_inv_cancel₀ (jac_pos L).ne', one_smul]

lemma volume_image_affE (L : E ≃L[ℝ] E) (t : E) (K : Set E) :
    volume.real (affE L t '' K) = jac L * volume.real K := by
  have h := congrArg (fun μ : Measure E => μ (affE L t '' K)) (map_volume_affE L t)
  simp only [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, smul_apply,
    smul_eq_mul] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (jac_pos L).le)] at h2
  change volume.real K = (jac L)⁻¹ * volume.real (affE L t '' K) at h2
  rw [h2, ← mul_assoc, mul_inv_cancel₀ (jac_pos L).ne', one_mul]

end Affine


section Classes

/-- The class `𝒢_d(A, L, r, R)` of Section 23: `K` is a convex body (compact, convex) that
contains a closed ball of radius `r` and has diameter at most `R`, and `g` is a measurable
probability density vanishing outside `K` with `e^{-A} ≤ |K| g ≤ e^A` on `K` and `log g`
`L`-Lipschitz on `K`. -/
structure InG (A L r R : ℝ) (K : Set E) (g : E → ℝ) : Prop where
  compact : IsCompact K
  convex : Convex ℝ K
  ball : ∃ b, Metric.closedBall b r ⊆ K
  diam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R
  meas : Measurable g
  zero : ∀ y ∉ K, g y = 0
  int : ∫ y, g y = 1
  low : ∀ y ∈ K, exp (-A) ≤ volume.real K * g y
  up : ∀ y ∈ K, volume.real K * g y ≤ exp A
  lip : ∀ x ∈ K, ∀ y ∈ K, |log (g x) - log (g y)| ≤ L * dist x y

/-- The probability measure with density `g`. -/
def densMeas (g : E → ℝ) : Measure E := volume.withDensity fun y => ENNReal.ofReal (g y)

/-- The mean `m_g = ∫ y g(y) dy`. -/
def meanD (g : E → ℝ) : E := ∫ y, g y • y

/-- The image density `y ↦ g(T⁻¹ y) / |det L|` of `g` under `T x = L x + t`. -/
def pushD (L : E ≃L[ℝ] E) (t : E) (g : E → ℝ) (y : E) : ℝ := g (L.symm (y - t)) / jac L

lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS, e.measurableEmbedding.restrict_map, lintegral_map_equiv]
  simp

lemma densMeas_map (L : E ≃L[ℝ] E) (t : E) {g : E → ℝ} :
    (densMeas g).map (affE L t) = densMeas (pushD L t g) := by
  rw [densMeas, map_withDensity_equiv, map_volume_affE, withDensity_smul_measure, densMeas,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  simp only [Function.comp, pushD, affE_symm_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 (jac_pos L).le)]

lemma integral_pushD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] E)
    (t : E) (g : E → ℝ) (Φ : E → F) :
    ∫ y, pushD L t g y • Φ y = ∫ x, g x • Φ (L x + t) := by
  have h := integral_comp_affE_symm L t (fun x => (g x / jac L) • Φ (L x + t))
  simp only [ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel] at h
  rw [show (fun y => pushD L t g y • Φ y) = fun y => (g (L.symm (y - t)) / jac L) • Φ y from rfl,
    h, ← integral_smul]
  congr 1; funext x
  rw [smul_smul, mul_div_assoc', mul_comm, mul_div_assoc, div_self (jac_pos L).ne', mul_one]

lemma integral_pushD_one (L : E ≃L[ℝ] E) (t : E) (g : E → ℝ) :
    ∫ y, pushD L t g y = ∫ x, g x := by
  have := integral_pushD L t g (fun _ => (1 : ℝ))
  simpa using this

end Classes


section Push

variable {A Lg r R : ℝ} {K : Set E} {g : E → ℝ}

lemma InG.gpos (hG : InG A Lg r R K g) {y : E} (hy : y ∈ K) : 0 < g y := by
  have h := (exp_pos (-A)).trans_le (hG.low y hy)
  exact pos_of_mul_pos_right h measureReal_nonneg

lemma InG.volPos (hG : InG A Lg r R K g) : 0 < volume.real K := by
  rcases K.eq_empty_or_nonempty with hK | ⟨y, hy⟩
  · have h0 : g = fun _ => 0 := funext fun y => hG.zero y (by simp [hK])
    have := hG.int
    rw [h0, integral_zero] at this
    exact absurd this zero_ne_one
  · have h := (exp_pos (-A)).trans_le (hG.low y hy)
    exact pos_of_mul_pos_left h (hG.gpos hy).le

lemma InG.supp (hG : InG A Lg r R K g) : Function.support g ⊆ K := fun y hy => by
  by_contra h; exact hy (hG.zero y h)

lemma InG.integrable (hG : InG A Lg r R K g) : Integrable g := by
  have hv := hG.volPos
  refine (integrableOn_iff_integrable_of_support_subset hG.supp).1 ?_
  exact integrableOn_dens hG.compact.isClosed.measurableSet hG.compact.measure_lt_top hG.meas
    (fun y hy => (hG.gpos hy).le) (C := exp A / volume.real K)
    (fun y hy => by rw [le_div_iff₀' hv]; exact hG.up y hy)

lemma InG.integrable_smul (hG : InG A Lg r R K g) : Integrable fun y => g y • y := by
  have hs : Function.support (fun y => g y • y) ⊆ K := fun y hy => by
    by_contra h; exact hy (by simp [hG.zero y h])
  refine (integrableOn_iff_integrable_of_support_subset hs).1 ?_
  exact (hG.integrable.integrableOn).smul_continuousOn continuous_id.continuousOn hG.compact

lemma meanD_pushD (hG : InG A Lg r R K g) (L : E ≃L[ℝ] E) (t : E) :
    meanD (pushD L t g) = L (meanD g) + t := by
  have h := integral_pushD L t g id
  simp only [id] at h
  rw [meanD, h]
  simp only [smul_add]
  rw [integral_add (L.toContinuousLinearMap.integrable_comp hG.integrable_smul |>.congr
      (Filter.Eventually.of_forall fun y => by simp)) (hG.integrable.smul_const t),
    integral_smul_const, hG.int, one_smul]
  congr 1
  have := L.toContinuousLinearMap.integral_comp_comm hG.integrable_smul
  simp only [ContinuousLinearEquiv.coe_coe, map_smul] at this
  rw [meanD, this]

/-- Transfer of the class `𝒢` under an affine bijection `T x = L x + t`: the image density
`pushD L t g` on `T K` keeps the bounds `e^{∓A}`, its logarithm is `Lg ‖L⁻¹‖`-Lipschitz, and
the radius and diameter are given. -/
lemma InG.push (hG : InG A Lg r R K g) (hLg : 0 ≤ Lg) (L : E ≃L[ℝ] E) (t : E) {L' r' R' : ℝ}
    (hball : ∃ b, Metric.closedBall b r' ⊆ affE L t '' K)
    (hdiam : ∀ x ∈ affE L t '' K, ∀ y ∈ affE L t '' K, dist x y ≤ R')
    (hL' : Lg * ‖(L.symm : E →L[ℝ] E)‖ ≤ L') :
    InG A L' r' R' (affE L t '' K) (pushD L t g) := by
  have hj := jac_pos L
  have hmem : ∀ y, y ∈ affE L t '' K ↔ L.symm (y - t) ∈ K := fun y => by
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro h; exact ⟨_, h, by simp⟩
  have hvol := volume_image_affE L t K
  have hval : ∀ y, volume.real (affE L t '' K) * pushD L t g y =
      volume.real K * g (L.symm (y - t)) := fun y => by
    rw [hvol, pushD]; field_simp
  refine ⟨hG.compact.image (show Continuous (affE L t) from L.continuous.add continuous_const),
    ?_, hball, hdiam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rw [hmem] at hx hy ⊢
    have e : L.symm (a • x + b • y - t) = a • L.symm (x - t) + b • L.symm (y - t) := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      have ht : a • t + b • t = t := by rw [← add_smul, hab, one_smul]
      calc a • x + b • y - t = a • x + b • y - (a • t + b • t) := by rw [ht]
        _ = a • (x - t) + b • (y - t) := by rw [smul_sub, smul_sub]; abel
    rw [e]; exact hG.convex hx hy ha hb hab
  · exact (hG.meas.comp (L.symm.continuous.measurable.comp (measurable_sub_const t))).div_const _
  · intro y hy
    rw [pushD, hG.zero _ (fun h => hy ((hmem y).2 h)), zero_div]
  · rw [integral_pushD_one, hG.int]
  · intro y hy; rw [hval]; exact hG.low _ ((hmem y).1 hy)
  · intro y hy; rw [hval]; exact hG.up _ ((hmem y).1 hy)
  · intro y hy z hz
    have hy' := (hmem y).1 hy
    have hz' := (hmem z).1 hz
    rw [pushD, pushD, log_div (hG.gpos hy').ne' hj.ne', log_div (hG.gpos hz').ne' hj.ne',
      sub_sub_sub_cancel_right]
    refine (hG.lip _ hy' _ hz').trans ?_
    have hd : dist (L.symm (y - t)) (L.symm (z - t)) ≤ ‖(L.symm : E →L[ℝ] E)‖ * dist y z := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right]
      exact (L.symm : E →L[ℝ] E).le_opNorm _
    calc Lg * dist (L.symm (y - t)) (L.symm (z - t))
        ≤ Lg * (‖(L.symm : E →L[ℝ] E)‖ * dist y z) := mul_le_mul_of_nonneg_left hd hLg
      _ = (Lg * ‖(L.symm : E →L[ℝ] E)‖) * dist y z := by ring
      _ ≤ L' * dist y z := mul_le_mul_of_nonneg_right hL' dist_nonneg

end Push


section CondProd

variable {n : ℕ}

/-- The conditioned product `β_h` with respect to a reference measure `λ` on tuples: the measure
with density `condProdJ λ h`. -/
def condMeas (lam : Measure (Fin n → E)) (h : Fin n → E → ℝ) : Measure (Fin n → E) :=
  lam.withDensity fun x => ENNReal.ofReal (condProdJ lam h x)

/-- `(y₁, …, y_m) ↦ (y₁, …, y_m, s - y₁ - ⋯ - y_m)`: the identification of
`{x ∈ E^{m+1} : ∑ xⱼ = s}` with `E^m` by eliminating the last coordinate. -/
def embedT (m : ℕ) (s : E) (y : Fin m → E) : Fin (m + 1) → E :=
  Fin.snoc (α := fun _ => E) y (s - ∑ i, y i)

lemma measurable_embedT (m : ℕ) (s : E) : Measurable (embedT m s) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [embedT, Fin.snoc_last]
    exact measurable_const.sub (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
  · simp only [embedT, Fin.snoc_castSucc]
    exact measurable_pi_apply k

lemma sum_embedT (m : ℕ) (s : E) (y : Fin m → E) : ∑ j, embedT m s y j = s := by
  simp [embedT, Fin.sum_univ_castSucc]

/-- The Lebesgue measure `λ` on the hyperplane `{x ∈ E^{m+1} : ∑ xⱼ = s}` (Section 23: Lebesgue
measure on `(ℝ^d)^{n-1}` through the first `n - 1 = m` coordinates). -/
def lebT (m : ℕ) (s : E) : Measure (Fin (m + 1) → E) :=
  (Measure.pi fun _ : Fin m => (volume : Measure E)).map (embedT m s)

lemma ae_sum_lebT (m : ℕ) (s : E) : ∀ᵐ x ∂(lebT m s), ∑ j, x j = s := by
  rw [lebT, ae_map_iff (measurable_embedT m s).aemeasurable]
  · exact Filter.Eventually.of_forall fun y => sum_embedT m s y
  · exact (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j)
      continuous_const).measurableSet

lemma ae_condMeas {lam : Measure (Fin n → E)} {h : Fin n → E → ℝ} {p : (Fin n → E) → Prop}
    (hp : ∀ᵐ x ∂lam, p x) : ∀ᵐ x ∂(condMeas lam h), p x :=
  (withDensity_absolutelyContinuous _ _).ae_le hp

/-- Image of a conditioned product under coordinatewise measurable bijections. -/
lemma condMeas_map (lam : Measure (Fin n → E)) (h : Fin n → E → ℝ) (e : Fin n → E ≃ᵐ E) :
    (condMeas lam h).map (MeasurableEquiv.piCongrRight e) =
      condMeas (lam.map (MeasurableEquiv.piCongrRight e)) (fun j y => h j ((e j).symm y)) := by
  rw [condMeas, map_withDensity_equiv, condMeas]
  congr 1
  funext x
  simp only [Function.comp, condProdJ]
  congr 2
  rw [integral_map_equiv]
  congr 1
  funext y
  congr 1; funext i
  rw [show (MeasurableEquiv.piCongrRight e) y i = e i (y i) from rfl,
    MeasurableEquiv.symm_apply_apply]

/-- Conditioned products do not change when the densities are multiplied by nonzero constants. -/
lemma condProdJ_smul (lam : Measure (Fin n → E)) (h : Fin n → E → ℝ) (c : Fin n → ℝ)
    (hc : ∀ j, c j ≠ 0) : condProdJ lam (fun j y => c j * h j y) = condProdJ lam h := by
  funext x
  simp only [condProdJ, Finset.prod_mul_distrib, integral_const_mul]
  rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun j _ => hc j)]

/-- The tilted density `g e^φ / ∫ g e^φ`. -/
def tiltD (g φ : E → ℝ) (y : E) : ℝ := g y * exp (φ y) / ∫ z, g z * exp (φ z)

end CondProd


section Thm113

/-- The bound `sup_K |φ| + Lip_K(φ) ≤ ε` (Theorem 113), with explicit `S ≥ sup |φ|` and
`Lc ≥ Lip(φ)`. -/
def SupLipLE (K : Set E) (φ : E → ℝ) (ε : ℝ) : Prop :=
  ∃ S Lc : ℝ, 0 ≤ S ∧ 0 ≤ Lc ∧ (∀ y ∈ K, |φ y| ≤ S) ∧
    (∀ x ∈ K, ∀ y ∈ K, |φ x - φ y| ≤ Lc * dist x y) ∧ S + Lc ≤ ε

/-- **Statement of Theorem 113** (`jl:thm:main`), used as an explicit hypothesis. For `A, L ≥ 0`
and `0 < r ≤ R` there are `N` and `ε_n → 0` such that for `n = m + 1 ≥ N` and
`(K_j, g_j) ∈ 𝒢_d(A, L, r, R)`, with `s = ∑ m_{g_j}`, there are `φ_j` with `∫ φ_j g_j = 0` and
`sup_{K_j} |φ_j| + Lip(φ_j) ≤ ε_n` for which the conditioned product of the
`h_j = g_j e^{φ_j} / ∫ g_j e^{φ_j}` on `𝒯(K_1, …, K_n; s)` (reference measure `lebT m s`) is a
joint mix of `g_1, …, g_n`, with density bounded below by a positive constant on `𝒯`. -/
def Thm113 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] : Prop :=
  ∀ A L r R : ℝ, 0 ≤ A → 0 ≤ L → 0 < r → r ≤ R →
  ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
  ∀ m : ℕ, N ≤ m + 1 → ∀ (K : Fin (m + 1) → Set E) (g : Fin (m + 1) → E → ℝ),
    (∀ j, InG A L r R (K j) (g j)) →
    ∃ φ : Fin (m + 1) → E → ℝ, (∀ j, ∫ y in K j, φ j y * g j y = 0) ∧
      (∀ j, SupLipLE (K j) (φ j) (ε (m + 1))) ∧
      IsJointMix (fun j => densMeas (g j))
        (condMeas (lebT m (∑ j, meanD (g j))) fun j => tiltD (g j) (φ j)) ∧
      ∃ c > 0, ∀ x : Fin (m + 1) → E, (∀ j, x j ∈ K j) → ∑ j, x j = ∑ j, meanD (g j) →
        c ≤ condProdJ (lebT m (∑ j, meanD (g j))) (fun j => tiltD (g j) (φ j)) x

/-- **Theorem 113 for equal data, with equal corrections**, used as an explicit hypothesis by
Corollary 114. The proof of Corollary 114 obtains it from the *proof* of Theorem 113 (with equal
data the map `Φ` preserves the subset of `𝒟` with equal coordinates); it does not follow from the
statement `Thm113`. -/
def Thm113Sym (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] : Prop :=
  ∀ A L r R : ℝ, 0 ≤ A → 0 ≤ L → 0 < r → r ≤ R →
  ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
  ∀ m : ℕ, N ≤ m + 1 → ∀ (K : Set E) (g : E → ℝ), InG A L r R K g →
    ∃ φ : E → ℝ, ∫ y in K, φ y * g y = 0 ∧ SupLipLE K φ (ε (m + 1)) ∧
      IsCompleteMix (m + 1) (densMeas g)
        (condMeas (lebT m (((m + 1 : ℕ) : ℝ) • meanD g)) fun _ => tiltD g φ)

end Thm113

section Cor115

lemma jac_symm (L : E ≃L[ℝ] E) : jac L.symm = (jac L)⁻¹ := by
  rw [jac, jac, ← abs_inv]
  congr 1
  exact L.toLinearEquiv.det_coe_symm

lemma pushD_symm (L : E ≃L[ℝ] E) (t : E) (g : E → ℝ) :
    pushD L.symm (-L.symm t) (pushD L t g) = g := by
  funext y
  simp only [pushD, ContinuousLinearEquiv.symm_symm, sub_neg_eq_add, map_add,
    ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel_right,
    ContinuousLinearEquiv.symm_apply_apply, jac_symm]
  field_simp [(jac_pos L).ne']

lemma condMeas_smul {n : ℕ} (lam : Measure (Fin n → E)) (h : Fin n → E → ℝ) (c : Fin n → ℝ)
    (hc : ∀ j, c j ≠ 0) : condMeas lam (fun j y => c j * h j y) = condMeas lam h := by
  rw [condMeas, condMeas, condProdJ_smul lam h c hc]

lemma tiltD_pushD (L : E ≃L[ℝ] E) (g φ : E → ℝ) (y : E) :
    tiltD (pushD L 0 g) φ (L y) = (jac L)⁻¹ * tiltD g (fun x => φ (L x)) y := by
  have hZ := integral_pushD L 0 g (fun z => exp (φ z))
  simp only [smul_eq_mul, add_zero] at hZ
  simp only [tiltD]
  rw [hZ]
  simp only [pushD, sub_zero, ContinuousLinearEquiv.symm_apply_apply]
  ring

/-- **Corollary 115** (`jl:cor:weights`), given Theorem 113 (`Thm113`). Let `κ ≥ 1`. There are
`N` and `ε_n → 0` (depending only on `d, A, L, r, R, κ`) such that for `n = m + 1 ≥ N`,
`(K_j, g_j) ∈ 𝒢_d(A, L, r, R)` and invertible linear maps `M_j` with `‖M_j‖, ‖M_j⁻¹‖ ≤ κ`,
there are functions `φ_j` with `sup_{K_j} |φ_j| ≤ ε_n` such that the conditioned product `P` of
the densities `g_j e^{φ_j} / ∫ g_j e^{φ_j}` on `{x : ∑ M_j x_j = s}`, `s = ∑ M_j m_{g_j}` (reference
measure: the image of `lebT m s` under `y ↦ (M_j⁻¹ y_j)_j`), is a probability measure with
marginals `g_j` and `∑ M_j x_j = s` almost surely. -/
theorem cor115 (h113 : Thm113 E) {A Lg r R κ : ℝ} (hA : 0 ≤ A) (hLg : 0 ≤ Lg) (hr : 0 < r)
    (hrR : r ≤ R) (hκ : 1 ≤ κ) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ (K : Fin (m + 1) → Set E) (g : Fin (m + 1) → E → ℝ),
      (∀ j, InG A Lg r R (K j) (g j)) → ∀ M : Fin (m + 1) → E ≃L[ℝ] E,
      (∀ j, ‖(M j : E →L[ℝ] E)‖ ≤ κ) → (∀ j, ‖((M j).symm : E →L[ℝ] E)‖ ≤ κ) →
      ∃ φ : Fin (m + 1) → E → ℝ, (∀ j, ∀ y ∈ K j, |φ j y| ≤ ε (m + 1)) ∧
        IsProbabilityMeasure (condMeas ((lebT m (∑ j, M j (meanD (g j)))).map
          (MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0))
          fun j => tiltD (g j) (φ j)) ∧
        (∀ j, (condMeas ((lebT m (∑ j, M j (meanD (g j)))).map
          (MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0))
          fun j => tiltD (g j) (φ j)).map (fun x => x j) = densMeas (g j)) ∧
        ∀ᵐ x ∂(condMeas ((lebT m (∑ j, M j (meanD (g j)))).map
          (MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0))
          fun j => tiltD (g j) (φ j)), ∑ j, M j (x j) = ∑ j, M j (meanD (g j)) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨N, ε, hε, H⟩ := h113 A (κ * Lg) (r / κ) (κ * R) hA (by positivity) (by positivity)
    (by
      calc r / κ ≤ r := div_le_self hr.le hκ
        _ ≤ R := hrR
        _ ≤ κ * R := le_mul_of_one_le_left (hr.le.trans hrR) hκ)
  refine ⟨N, ε, hε, fun m hm K g hG M hM hMi => ?_⟩
  set K' : Fin (m + 1) → Set E := fun j => affE (M j) 0 '' K j
  set g' : Fin (m + 1) → E → ℝ := fun j => pushD (M j) 0 (g j)
  have hG' : ∀ j, InG A (κ * Lg) (r / κ) (κ * R) (K' j) (g' j) := by
    intro j
    refine (hG j).push hLg (M j) 0 ?_ ?_ ?_
    · obtain ⟨b, hb⟩ := (hG j).ball
      refine ⟨M j b, fun z hz => ⟨(M j).symm z, hb ?_, by simp⟩⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      have : (M j).symm z - b = (M j).symm (z - M j b) := by simp
      rw [this]
      calc ‖(M j).symm (z - M j b)‖ ≤ ‖((M j).symm : E →L[ℝ] E)‖ * ‖z - M j b‖ :=
            ((M j).symm : E →L[ℝ] E).le_opNorm _
        _ ≤ κ * (r / κ) := mul_le_mul (hMi j) hz (norm_nonneg _) hκ0.le
        _ = r := by field_simp
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [affE_apply, add_zero, dist_eq_norm, ← map_sub]
      calc ‖M j (x - y)‖ ≤ ‖(M j : E →L[ℝ] E)‖ * ‖x - y‖ := (M j : E →L[ℝ] E).le_opNorm _
        _ ≤ κ * R := mul_le_mul (hM j) (by rw [← dist_eq_norm]; exact (hG j).diam x hx y hy)
            (norm_nonneg _) hκ0.le
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hMi j) hLg
  obtain ⟨φ', -, hφb, hmix, -⟩ := H m hm K' g' hG'
  have hs : ∑ j, meanD (g' j) = ∑ j, M j (meanD (g j)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [meanD_pushD (hG j), add_zero]
  rw [hs] at hmix
  set Φ := MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0
  set s := ∑ j, M j (meanD (g j))
  refine ⟨fun j y => φ' j (M j y), fun j y hy => ?_, ?_⟩
  · obtain ⟨S, Lc, -, hLc, hS, -, hSL⟩ := hφb j
    exact (hS _ ⟨y, hy, by simp⟩).trans (by linarith)
  -- the conditioned product is the image of the one for the `M_j X_j`
  have hP : condMeas ((lebT m s).map Φ) (fun j => tiltD (g j) (fun y => φ' j (M j y))) =
      (condMeas (lebT m s) fun j => tiltD (g' j) (φ' j)).map Φ := by
    rw [condMeas_map, ← condMeas_smul _ _ (fun j => (jac (M j))⁻¹)
      (fun j => inv_ne_zero (jac_pos (M j)).ne')]
    congr 1
    funext j y
    simp only [g', affE_symm_apply, ContinuousLinearEquiv.symm_symm, sub_zero]
    rw [tiltD_pushD]
  rw [hP]
  have hprob : IsProbabilityMeasure (condMeas (lebT m s) fun j => tiltD (g' j) (φ' j)) := hmix.1
  refine ⟨inferInstance, fun j => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply j) Φ.measurable]
    have : (fun x : Fin (m + 1) → E => x j) ∘ Φ = affE (M j).symm 0 ∘ fun x => x j := rfl
    rw [this, ← Measure.map_map (affE (M j).symm 0).measurable (measurable_pi_apply j),
      hmix.2.2 j, densMeas_map]
    congr 1
    simpa using pushD_symm (M j) 0 (g j)
  · rw [ae_map_iff Φ.measurable.aemeasurable]
    · refine (ae_condMeas (ae_sum_lebT m s)).mono fun x hx => ?_
      show ∑ j, M j ((M j).symm (x j) + 0) = s
      simp [hx]
    · exact (isClosed_eq (continuous_finsetSum _ fun j _ =>
        (M j).continuous.comp (continuous_apply j)) continuous_const).measurableSet
end Cor115

section Cor114

lemma pi_smul_const {m : ℕ} (c : NNReal) (μ : Measure E) [SigmaFinite μ] :
    Measure.pi (fun _ : Fin m => (c : ENNReal) • μ) =
      (c : ENNReal) ^ m • Measure.pi (fun _ : Fin m => μ) := by
  have : SigmaFinite ((c : ENNReal) • μ) := SMul.sigmaFinite (μ := μ) c
  refine Measure.pi_eq fun S hS => ?_
  rw [smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

lemma embedT_aff (m : ℕ) (L : E ≃L[ℝ] E) (t s : E) (y : Fin m → E) :
    (fun j => L (embedT m s y j) + t) =
      embedT m (L s + ((m + 1 : ℕ) : ℝ) • t) (fun i => L (y i) + t) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [embedT, Fin.snoc_last, map_sub, map_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, ← Nat.cast_smul_eq_nsmul ℝ]
    abel
  · simp only [embedT, Fin.snoc_castSucc]

/-- The image of `λ = lebT m s` under the coordinatewise affine map `x ↦ L x + t` is a constant
multiple of `lebT m (L s + n t)`, `n = m + 1`. -/
lemma lebT_map_aff (m : ℕ) (L : E ≃L[ℝ] E) (t s : E) :
    (lebT m s).map (MeasurableEquiv.piCongrRight fun _ => affE L t) =
      (ENNReal.ofReal (jac L)⁻¹) ^ m • lebT m (L s + ((m + 1 : ℕ) : ℝ) • t) := by
  have hΨ : Measurable fun (y : Fin m → E) (i : Fin m) => L (y i) + t :=
    measurable_pi_iff.2 fun i => (affE L t).measurable.comp (measurable_pi_apply i)
  rw [lebT, Measure.map_map (MeasurableEquiv.piCongrRight fun _ => affE L t).measurable
    (measurable_embedT m s)]
  have hc : (MeasurableEquiv.piCongrRight fun _ => affE L t) ∘ embedT m s =
      embedT m (L s + ((m + 1 : ℕ) : ℝ) • t) ∘ fun y i => L (y i) + t := by
    funext y; exact embedT_aff m L t s y
  rw [hc, ← Measure.map_map (measurable_embedT _ _) hΨ]
  have hpi : (Measure.pi fun _ : Fin m => (volume : Measure E)).map (fun y i => L (y i) + t) =
      Measure.pi fun _ : Fin m => (volume : Measure E).map (affE L t) :=
    Measure.pi_map_pi (f := fun _ => (affE L t : E → E))
      (hμ := fun _ => (affE L t).sigmaFinite_map)
      (fun _ => (affE L t).measurable.aemeasurable)
  rw [hpi, map_volume_affE, show ENNReal.ofReal (jac L)⁻¹ = (((jac L)⁻¹).toNNReal : ENNReal)
    from rfl, pi_smul_const, Measure.map_smul, lebT]
  exact (measurable_embedT _ _).aemeasurable

/-- Conditioned products do not change when the reference measure is multiplied by a constant
`c ∈ (0, ∞)`. -/
lemma condMeas_smul_measure {n : ℕ} (lam : Measure (Fin n → E)) (h : Fin n → E → ℝ)
    {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) : condMeas (c • lam) h = condMeas lam h := by
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  have hp : ∀ x, condProdJ (c • lam) h x = condProdJ lam h x / c.toReal := fun x => by
    simp only [condProdJ, integral_smul_measure, smul_eq_mul]
    rw [div_div, mul_comm (∫ y, _ ∂lam)]
  rw [condMeas, condMeas, withDensity_smul_measure, ← withDensity_smul' _ _ hct]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, hp]
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_toReal hct, ENNReal.mul_div_cancel hc0 hct]

lemma tiltD_pushD' (L : E ≃L[ℝ] E) (t : E) (g φ : E → ℝ) (y : E) :
    tiltD (pushD L t g) φ (L y + t) = (jac L)⁻¹ * tiltD g (fun x => φ (L x + t)) y := by
  have hZ := integral_pushD L t g (fun z => exp (φ z))
  simp only [smul_eq_mul] at hZ
  simp only [tiltD]
  rw [hZ]
  simp only [pushD, add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
  ring

/-- **John's theorem**, used as an explicit hypothesis (Mathlib lacks it): every convex body
`K` (compact, convex, with interior points) has an affine image `T K`, `T x = L x + t`, with
`B ⊆ T K ⊆ d B`, `B` the closed unit ball and `d` the dimension. -/
def JohnThm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] : Prop :=
  ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
    ∃ (L : E ≃L[ℝ] E) (t : E), Metric.closedBall (0 : E) 1 ⊆ affE L t '' K ∧
      affE L t '' K ⊆ Metric.closedBall 0 (Module.finrank ℝ E)

lemma mem_of_mem_affE_image {L : E ≃L[ℝ] E} {t : E} {K : Set E} {x : E}
    (hx : x ∈ affE L t '' K) : L.symm (x - t) ∈ K := by
  obtain ⟨a, ha, rfl⟩ := hx; simpa using ha

/-- `‖T₀⁻¹‖ ≤ diam(K)/2` when `T K ⊇ B` (proof of Corollary 114). -/
lemma norm_symm_le_diam {L : E ≃L[ℝ] E} {t : E} {K : Set E} (hKb : Bornology.IsBounded K)
    (hB : Metric.closedBall (0 : E) 1 ⊆ affE L t '' K) :
    2 * ‖(L.symm : E →L[ℝ] E)‖ ≤ Metric.diam K := by
  have h : ‖(L.symm : E →L[ℝ] E)‖ ≤ Metric.diam K / 2 := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun x hx => ?_
    have h1 := mem_of_mem_affE_image (hB (show x ∈ Metric.closedBall 0 1 by simp [hx]))
    have h2 := mem_of_mem_affE_image (hB (show -x ∈ Metric.closedBall 0 1 by simp [hx]))
    have h3 := Metric.dist_le_diam_of_mem hKb h1 h2
    rw [dist_eq_norm, ← map_sub, show x - t - (-x - t) = (2 : ℝ) • x by
      rw [two_smul]; abel, map_smul, norm_smul, Real.norm_two] at h3
    simp only [ContinuousLinearEquiv.coe_coe]
    linarith
  linarith

/-- **Corollary 114** (`jl:cor:density`), given John's theorem (`JohnThm`) and Theorem 113 in
the symmetric form of its proof (`Thm113Sym`). For `A, Λ ≥ 0` there are `N` and `ε_n → 0` such
that for every convex body `K` and probability density `g` vanishing outside `K` with
`e^{-A} ≤ |K| g ≤ e^A` on `K` and `log g` Lipschitz on `K` with constant `Λ / diam K`, and every
`n = m + 1 ≥ N`, there is `φ` with `sup_K |φ| ≤ ε_n` such that `n` independent random vectors with
density `g e^φ / ∫ g e^φ`, conditioned on their sum being `n m_g` (the conditioned product with
respect to `lebT m (n m_g)`), form an `n`-complete mix of `g`. -/
theorem cor114 (hJ : JohnThm E) (h113 : Thm113Sym E) (hd : 0 < Module.finrank ℝ E) {A Λ : ℝ}
    (hA : 0 ≤ A) (hΛ : 0 ≤ Λ) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ (K : Set E) (g : E → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
      Measurable g → (∀ y ∉ K, g y = 0) → ∫ y, g y = 1 →
      (∀ y ∈ K, exp (-A) ≤ volume.real K * g y) → (∀ y ∈ K, volume.real K * g y ≤ exp A) →
      (∀ x ∈ K, ∀ y ∈ K, |log (g x) - log (g y)| ≤ Λ / Metric.diam K * dist x y) →
      ∀ m : ℕ, N ≤ m + 1 → ∃ φ : E → ℝ, (∀ y ∈ K, |φ y| ≤ ε (m + 1)) ∧
        IsCompleteMix (m + 1) (densMeas g)
          (condMeas (lebT m (((m + 1 : ℕ) : ℝ) • meanD g)) fun _ => tiltD g φ) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd1 : (1 : ℝ) ≤ d := by
    have : 1 ≤ Module.finrank ℝ E := hd
    exact Nat.one_le_cast.2 this
  obtain ⟨N, ε, hε, H⟩ := h113 A (Λ / 2) 1 (2 * d) hA (by positivity) one_pos (by linarith)
  refine ⟨N, ε, hε, fun K g hKc hKconv hKi hgm hz hi hlow hup hlip m hm => ?_⟩
  obtain ⟨L, t, hB, hD⟩ := hJ K hKc hKconv hKi
  -- `K` itself is in a class `𝒢`
  obtain ⟨x0, hx0⟩ := hKi
  obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx0)
  have hdiam : 2 * ‖(L.symm : E →L[ℝ] E)‖ ≤ Metric.diam K :=
    norm_symm_le_diam hKc.isBounded hB
  have hLpos : 0 < ‖(L.symm : E →L[ℝ] E)‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have : Subsingleton E := by
      refine ⟨fun x y => ?_⟩
      have hx : x = L ((L.symm : E →L[ℝ] E) x) := by simp
      have hy : y = L ((L.symm : E →L[ℝ] E) y) := by simp
      rw [hx, hy, h0]; rfl
    have := Module.finrank_zero_of_subsingleton (R := ℝ) (M := E)
    omega
  have hdpos : 0 < Metric.diam K := by linarith
  have hGK : InG A (Λ / Metric.diam K) (δ / 2) (Metric.diam K) K g :=
    ⟨hKc, hKconv, ⟨x0, (Metric.closedBall_subset_ball (by linarith)).trans hδK⟩,
      fun x hx y hy => Metric.dist_le_diam_of_mem hKc.isBounded hx hy, hgm, hz, hi, hlow, hup,
      hlip⟩
  have hG' : InG A (Λ / 2) 1 (2 * d) (affE L t '' K) (pushD L t g) := by
    refine hGK.push (by positivity) L t ⟨0, hB⟩ (fun x hx y hy => ?_) ?_
    · have h1 := hD hx
      have h2 := hD hy
      rw [Metric.mem_closedBall, dist_zero_right] at h1 h2
      calc dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
        _ ≤ 2 * d := by linarith
    · calc Λ / Metric.diam K * ‖(L.symm : E →L[ℝ] E)‖
          ≤ Λ / Metric.diam K * (Metric.diam K / 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = Λ / 2 := by field_simp
  obtain ⟨φ', -, hφb, hmix⟩ := H m hm _ _ hG'
  rw [meanD_pushD hGK] at hmix
  set n : ℝ := ((m + 1 : ℕ) : ℝ)
  set Φ := MeasurableEquiv.piCongrRight fun _ : Fin (m + 1) => affE L.symm (-L.symm t)
  refine ⟨fun y => φ' (L y + t), fun y hy => ?_, ?_⟩
  · obtain ⟨S, Lc, -, hLc, hS, -, hSL⟩ := hφb
    exact (hS _ ⟨y, hy, rfl⟩).trans (by linarith)
  have hsum : L.symm (n • (L (meanD g) + t)) + n • -L.symm t = n • meanD g := by
    rw [map_smul, map_add, ContinuousLinearEquiv.symm_apply_apply, smul_add, smul_neg,
      add_neg_cancel_right]
  have hP : condMeas (lebT m (n • meanD g)) (fun _ => tiltD g fun y => φ' (L y + t)) =
      (condMeas (lebT m (n • (L (meanD g) + t))) fun _ => tiltD (pushD L t g) φ').map Φ := by
    rw [condMeas_map, lebT_map_aff, hsum, condMeas_smul_measure _ _
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 (inv_pos.2 (jac_pos _))).ne')
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      ← condMeas_smul _ _ (fun _ => (jac L)⁻¹) (fun _ => inv_ne_zero (jac_pos L).ne')]
    congr 1
    funext j y
    have : (affE L.symm (-L.symm t)).symm y = L y + t := by
      simp [affE_symm_apply, map_add]
    rw [this, tiltD_pushD']
  rw [hP]
  have hprob : IsProbabilityMeasure
      (condMeas (lebT m (n • (L (meanD g) + t))) fun _ => tiltD (pushD L t g) φ') := hmix.1
  refine ⟨inferInstance, ⟨n • meanD g, ?_⟩, fun j => ?_⟩
  · rw [← hP]; exact ae_condMeas (ae_sum_lebT m _)
  · rw [Measure.map_map (measurable_pi_apply j) Φ.measurable]
    have : (fun x : Fin (m + 1) → E => x j) ∘ Φ =
        affE L.symm (-L.symm t) ∘ fun x => x j := rfl
    rw [this, ← Measure.map_map (affE _ _).measurable (measurable_pi_apply j),
      hmix.2.2 j, densMeas_map, pushD_symm]

end Cor114

section Cor105

lemma volume_image_affE' (L : E ≃L[ℝ] E) (t : E) (K : Set E) :
    volume (affE L t '' K) = ENNReal.ofReal (jac L) * volume K := by
  have h := congrArg (fun μ : Measure E => μ (affE L t '' K)) (map_volume_affE L t)
  simp only [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, smul_apply,
    smul_eq_mul] at h
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (jac_pos L).le, mul_inv_cancel₀ (jac_pos L).ne',
    ENNReal.ofReal_one, one_mul]

lemma affE_symm_eq (L : E ≃L[ℝ] E) (t : E) :
    ((affE L t).symm : E → E) = affE L.symm (-L.symm t) := by
  funext y; simp [sub_eq_add_neg]

/-- The image of `U(T K)` under `T⁻¹` is `U(K)`, for `T x = L x + t`. -/
lemma unifSet_map_affE (L : E ≃L[ℝ] E) (t : E) (K : Set E) :
    (unifSet (affE L t '' K)).map (affE L.symm (-L.symm t)) = unifSet K := by
  have hj0 : ENNReal.ofReal (jac L) ≠ 0 := (ENNReal.ofReal_pos.2 (jac_pos L)).ne'
  have hjt : ENNReal.ofReal (jac L) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← affE_symm_eq]
  ext S hS
  rw [Measure.map_apply (affE L t).symm.measurable hS, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply ((affE L t).symm.measurable hS), Measure.restrict_apply hS,
    volume_image_affE', smul_eq_mul, smul_eq_mul]
  have : (affE L t).symm ⁻¹' S ∩ affE L t '' K = affE L t '' (S ∩ K) := by
    rw [MeasurableEquiv.image_eq_preimage_symm, MeasurableEquiv.image_eq_preimage_symm,
      Set.preimage_inter]
  rw [this, volume_image_affE', ENNReal.mul_inv (Or.inl hj0) (Or.inl hjt)]
  calc (ENNReal.ofReal (jac L))⁻¹ * (volume K)⁻¹ * (ENNReal.ofReal (jac L) * volume (S ∩ K))
      = ((ENNReal.ofReal (jac L))⁻¹ * ENNReal.ofReal (jac L)) * ((volume K)⁻¹ *
          volume (S ∩ K)) := by ring
    _ = (volume K)⁻¹ * volume (S ∩ K) := by rw [ENNReal.inv_mul_cancel hj0 hjt, one_mul]

/-- Affine images of complete mixes are complete mixes. -/
lemma isCompleteMix_affE {n : ℕ} {F : Measure E} {P : Measure (Fin n → E)}
    (h : IsCompleteMix n F P) (L : E ≃L[ℝ] E) (t : E) :
    IsCompleteMix n (F.map (affE L t))
      (P.map (MeasurableEquiv.piCongrRight fun _ => affE L t)) := by
  have := h.1
  set Φ := MeasurableEquiv.piCongrRight fun _ : Fin n => affE L t
  obtain ⟨s, hs⟩ := h.2.1
  refine ⟨inferInstance, ⟨L s + (n : ℝ) • t, ?_⟩, fun j => ?_⟩
  · rw [ae_map_iff Φ.measurable.aemeasurable]
    · refine hs.mono fun x hx => ?_
      show ∑ j, (L (x j) + t) = L s + (n : ℝ) • t
      rw [Finset.sum_add_distrib, ← map_sum, hx, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Nat.cast_smul_eq_nsmul]
    · exact (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j)
        continuous_const).measurableSet
  · rw [Measure.map_map (measurable_pi_apply j) Φ.measurable]
    have : (fun x : Fin n → E => x j) ∘ Φ = affE L t ∘ fun x => x j := rfl
    rw [this, ← Measure.map_map (affE L t).measurable (measurable_pi_apply j), h.2.2 j]

/-- The ball of radius `2r/(d+1)` about the centroid (proof of Corollary 105): a convex body that
contains a closed ball of radius `r > 0` contains the closed ball of radius `2r/(d+1)` about its
centroid (Lemma 111(a) with `A = 0` and the uniform density). -/
lemma closedBall_cent_subset {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) {b : E}
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall b r ⊆ K) :
    Metric.closedBall (cent K) (2 * r / (Module.finrank ℝ E + 1)) ⊆ K := by
  have hpos : 0 < volume K := (Metric.measure_closedBall_pos volume b hr).trans_le
    (measure_mono hball)
  have hv := real_pos_of_compact hKc hpos
  have h := lemma111a hKc hKconv hr hball (A := 0) (g := fun _ => (volume.real K)⁻¹)
    measurable_const (fun y _ => by simp [hv.ne'])
    (fun y _ => by simp [hv.ne'])
    (by rw [setIntegral_const, smul_eq_mul, mul_inv_cancel₀ hv.ne'])
  have hm : ∫ y in K, (fun _ => (volume.real K)⁻¹) y • y = cent K := by
    simp only [cent]; rw [integral_smul]
  rw [hm, neg_zero, exp_zero, mul_one] at h
  exact h

/-- The covariance lower bound of the proof of Corollary 105: if `K ⊇ B(c, ρ)`, `c` the centroid,
then `∫ ⟪e, y - c⟫² dU(K) ≥ (ρ/2)² |B_{ρ/4}| / |K|` for every unit vector `e`. -/
lemma var_unifSet_ge {K : Set E} (hKc : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall (cent K) ρ ⊆ K) {e : E} (he : ‖e‖ = 1) :
    (ρ / 2) ^ 2 * volume.real (Metric.ball (0 : E) (ρ / 4)) / volume.real K ≤
      ∫ y, ⟪e, y - cent K⟫ ^ 2 ∂(unifSet K) := by
  set c := cent K
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hfin : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  set c0 := c + (3 * ρ / 4) • e
  have hS : Metric.ball c0 (ρ / 4) ⊆ K := fun y hy => hball (by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := norm_add_le (y - c0) (c0 - c)
    rw [show y - c0 + (c0 - c) = y - c by abel] at h1
    have h2 : ‖c0 - c‖ = 3 * ρ / 4 := by
      simp only [c0, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos (show 0 < 3 * ρ / 4 by positivity)]
    linarith [mem_ball_iff_norm.1 hy])
  have hlow : ∀ y ∈ Metric.ball c0 (ρ / 4), (ρ / 2) ^ 2 ≤ ⟪e, y - c⟫ ^ 2 := fun y hy => by
    have h1 : ⟪e, y - c⟫ = 3 * ρ / 4 + ⟪e, y - c0⟫ := by
      simp only [c0, inner_sub_right, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he]
      ring
    have h2 : -(ρ / 4) ≤ ⟪e, y - c0⟫ := by
      have := abs_real_inner_le_norm e (y - c0)
      rw [he, one_mul] at this
      linarith [neg_abs_le ⟪e, y - c0⟫, mem_ball_iff_norm.1 hy]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hint : IntegrableOn (fun y => ⟪e, y - c⟫ ^ 2) K :=
    ((continuous_const.inner (continuous_id.sub continuous_const)).pow 2).continuousOn
      |>.integrableOn_compact hKc
  have hI : (ρ / 2) ^ 2 * volume.real (Metric.ball (0 : E) (ρ / 4)) ≤
      ∫ y in K, ⟪e, y - c⟫ ^ 2 := by
    calc (ρ / 2) ^ 2 * volume.real (Metric.ball (0 : E) (ρ / 4))
        = ∫ y in Metric.ball c0 (ρ / 4), (ρ / 2) ^ 2 := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Measure.real,
            Measure.addHaar_ball_center volume c0, mul_comm]
      _ ≤ ∫ y in Metric.ball c0 (ρ / 4), ⟪e, y - c⟫ ^ 2 :=
          setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne) (hint.mono_set hS)
            measurableSet_ball hlow
      _ ≤ ∫ y in K, ⟪e, y - c⟫ ^ 2 :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => sq_nonneg _)
            (Filter.Eventually.of_forall hS)
  rw [unifSet, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hI (inv_nonneg.2 measureReal_nonneg)

lemma convex_affE_image (L : E ≃L[ℝ] E) (t : E) {K : Set E} (hK : Convex ℝ K) :
    Convex ℝ (affE L t '' K) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hK hx hy ha hb hab, ?_⟩
  simp only [affE_apply, map_add, map_smul, smul_add]
  rw [add_add_add_comm, ← add_smul, hab, one_smul]

/-- **Theorem 104 with its constants tracked**, used as an explicit hypothesis by Corollary 105:
for a class `𝒦` of convex bodies on which `|K|` lies in `[v₀, v₁]`, `R_K = max_K |y - c| ≤ R`,
the ball of radius `ρ` about the centroid `c` lies in `K`, the covariance of `U(K)` is at least
`σ I`, and `sup_{|ξ| ≥ r} |û_K(ξ)|` is bounded away from `1` uniformly for every `r > 0`, the
constant `N` of Theorem 104 can be chosen uniformly. (The paper lists `S(K)` too; for convex
bodies it is bounded through `R_K` by the monotonicity of the surface area, which is not
formalised and is part of this hypothesis.) -/
def Thm104T (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] : Prop :=
  ∀ (𝒦 : Set (Set E)) (v₀ v₁ R ρ σ : ℝ), 0 < v₀ → 0 < ρ → 0 < σ →
    (∀ K ∈ 𝒦, IsCompact K ∧ Convex ℝ K ∧ v₀ ≤ volume.real K ∧ volume.real K ≤ v₁ ∧
      (∀ y ∈ K, ‖y - cent K‖ ≤ R) ∧ Metric.closedBall (cent K) ρ ⊆ K ∧
      ∀ e : E, ‖e‖ = 1 → σ ≤ ∫ y, ⟪e, y - cent K⟫ ^ 2 ∂(unifSet K)) →
    (∀ r > 0, ∃ q < 1, ∀ K ∈ 𝒦, ∀ ξ : E, r ≤ ‖ξ‖ → ‖charFun (unifSet K) ξ‖ ≤ q) →
    ∃ N : ℕ, ∀ K ∈ 𝒦, ∀ n, N ≤ n → CompletelyMixable n (unifSet K)

/-- The Fourier step of the proof of Corollary 105, used as an explicit hypothesis (Blaschke's
selection theorem, continuity of `û` in the Hausdorff metric, `|û(ξ)| < 1` for `ξ ≠ 0` and the
bound `|û(ξ)| ≤ S(K)/(|K| |ξ|)` from the divergence theorem): on the bodies `B ⊆ K ⊆ d B`,
`sup_{|ξ| ≥ r} |û_K(ξ)|` is bounded away from `1` uniformly, for every `r > 0`. -/
def FourierGapJohn (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] : Prop :=
  ∀ r > 0, ∃ q < 1, ∀ K : Set E, IsCompact K → Convex ℝ K → Metric.closedBall (0 : E) 1 ⊆ K →
    K ⊆ Metric.closedBall 0 (Module.finrank ℝ E) →
    ∀ ξ : E, r ≤ ‖ξ‖ → ‖charFun (unifSet K) ξ‖ ≤ q

/-- **Corollary 105** (`lg:cor:uniform`), given John's theorem, Theorem 104 with its constants
tracked and the Fourier step (`JohnThm`, `Thm104T`, `FourierGapJohn`): in dimension `d ≥ 1` there
is `N_d` such that the uniform distribution on every convex body is `n`-completely mixable for
every `n ≥ N_d`. Proved here: the bounds `|B| ≤ |K| ≤ d^d |B|`, `R_K ≤ 2d`, the ball of radius
`2/(d+1)` about the centroid (Remark 85, `closedBall_cent_subset`), the covariance bound
(`var_unifSet_ge`) and the affine invariance (`unifSet_map_affE`, `isCompleteMix_affE`). -/
theorem cor105 (hJ : JohnThm E) (h104 : Thm104T E) (hF : FourierGapJohn E)
    (hd : 0 < Module.finrank ℝ E) :
    ∃ N : ℕ, ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∀ n, N ≤ n → CompletelyMixable n (unifSet K) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd1 : (1 : ℝ) ≤ d := by
    have : 1 ≤ Module.finrank ℝ E := hd
    exact Nat.one_le_cast.2 this
  set 𝒦 : Set (Set E) := {K | IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall (0 : E) 1 ⊆ K ∧
    K ⊆ Metric.closedBall 0 d}
  set v₀ := volume.real (Metric.closedBall (0 : E) 1)
  have hv₀ : 0 < v₀ := ENNReal.toReal_pos (Metric.measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne
  set v₁ := d ^ Module.finrank ℝ E * v₀
  have hv₁ : 0 < v₁ := by positivity
  set ρ : ℝ := 2 * 1 / (d + 1)
  have hρ : 0 < ρ := by positivity
  set vB := volume.real (Metric.ball (0 : E) (ρ / 4))
  have hvB : 0 < vB := ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by positivity)).ne'
    measure_ball_lt_top.ne
  obtain ⟨N, hN⟩ := h104 𝒦 v₀ v₁ (2 * d) ρ ((ρ / 2) ^ 2 * vB / v₁) hv₀ hρ (by positivity)
    (fun K ⟨hKc, hKconv, hB, hD⟩ => by
      have hvK : volume.real K ≤ v₁ := by
        rw [show v₁ = volume.real (Metric.closedBall (0 : E) d) by
          rw [Measure.addHaar_real_closedBall' volume 0 (by linarith)]]
        exact measureReal_mono hD measure_closedBall_lt_top.ne
      have hball := closedBall_cent_subset hKc hKconv one_pos hB
      have hcK : cent K ∈ K := hball (Metric.mem_closedBall_self hρ.le)
      refine ⟨hKc, hKconv, measureReal_mono hB hKc.measure_lt_top.ne, hvK, fun y hy => ?_, hball,
        fun e he => ?_⟩
      · have h1 := hD hy
        have h2 := hD hcK
        rw [Metric.mem_closedBall, dist_zero_right] at h1 h2
        calc ‖y - cent K‖ ≤ ‖y‖ + ‖cent K‖ := norm_sub_le _ _
          _ ≤ 2 * d := by linarith
      · refine le_trans ?_ (var_unifSet_ge hKc hρ hball he)
        have hvK0 : 0 < volume.real K := (hv₀.trans_le (measureReal_mono hB
          hKc.measure_lt_top.ne))
        exact div_le_div_of_nonneg_left (by positivity) hvK0 hvK)
    (fun r hr => by
      obtain ⟨q, hq, hq'⟩ := hF r hr
      exact ⟨q, hq, fun K ⟨hKc, hKconv, hB, hD⟩ => hq' K hKc hKconv hB hD⟩)
  refine ⟨N, fun K hKc hKconv hKi n hn => ?_⟩
  obtain ⟨L, t, hB, hD⟩ := hJ K hKc hKconv hKi
  have hT : affE L t '' K ∈ 𝒦 :=
    ⟨hKc.image (show Continuous (affE L t) from L.continuous.add continuous_const),
      convex_affE_image L t hKconv, hB, hD⟩
  obtain ⟨P, hP⟩ := hN _ hT n hn
  exact ⟨_, by simpa [unifSet_map_affE] using isCompleteMix_affE hP L.symm (-L.symm t)⟩

end Cor105

end Mixes.Large
