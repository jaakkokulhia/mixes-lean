import Mixes.Remarks14

/-!
# The theorem of Archimedes on the sphere `S² ⊂ ℝ³`

`archimedes : Remarks14.H_archimedes`: under the uniform distribution `Ball.sphUnif` on the unit
sphere of `ℝ³` (the law of `G / ‖G‖` for a standard Gaussian `G`), the first coordinate is
uniform on `[-1, 1]` (Archimedes' hat-box theorem).

Proof. Write `G = (X, Y, Z)` with independent standard Gaussian coordinates (`mp_split`), so
`ξ₀ = X / √(X² + Y² + Z²)` (`law_eq`).
* `gauss2_tail`: `P(Y² + Z² ≥ r) = exp(-r/2)` (polar coordinates, `lintegral_comp_polarCoord_symm`).
* `key_sq`: for `0 < s < 1`, `P(ξ₀² ≤ s) = P(Y² + Z² ≥ ((1-s)/s) X²) = E exp(-((1-s)/s) X²/2) = √s`
  (Fubini and the Gaussian integral).
* `P3_sym`, `unif_sym`: both laws are symmetric; `sym_ext`: a symmetric finite measure on `ℝ` is
  determined by the law of the square; the squares have the same distribution function
  `min (√s) 1` (`P3_sq_cdf`, `unif_sq_cdf`).

The unconditional versions of the results of `Remarks14` that assume `H_archimedes` are
`isArchimedesMeasure_sphUnif_uncond` and its consequence `sphUnif_map_inner_uncond`.
-/

open MeasureTheory Set ProbabilityTheory Real Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section
namespace Mixes.Archimedes

lemma lintegral_Ioi_exp {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (x * exp (-x ^ 2 / 2)) = ENNReal.ofReal (exp (-a ^ 2 / 2)) := by
  have hd : ∀ x ∈ Ici a, HasDerivAt (fun x => -exp (-x ^ 2 / 2)) (x * exp (-x ^ 2 / 2)) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).neg).div_const 2).exp.neg
    convert this using 1
    simp; ring
  have hpos : ∀ x ∈ Ioi a, 0 ≤ x * exp (-x ^ 2 / 2) :=
    fun x hx => mul_nonneg (ha.trans hx.out.le) (exp_pos _).le
  have hlim : Tendsto (fun x : ℝ => -exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => -x ^ 2 / 2) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const two_pos
    simpa using (tendsto_exp_atBot.comp h1).neg
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hpos x hx),
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim]
  simp

lemma gaussianPDF_mul (x y : ℝ) :
    gaussianPDF 0 1 x * gaussianPDF 0 1 y
      = ENNReal.ofReal ((2 * π)⁻¹ * exp (-(x ^ 2 + y ^ 2) / 2)) := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have h2 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [show -(x ^ 2 + y ^ 2) / 2 = -x ^ 2 / 2 + -y ^ 2 / 2 by ring, exp_add, ← h2]
  ring

lemma gauss2_tail {r : ℝ} (hr : 0 ≤ r) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {q : ℝ × ℝ | r ≤ q.1 ^ 2 + q.2 ^ 2}
      = ENNReal.ofReal (exp (-r / 2)) := by
  set S := {q : ℝ × ℝ | r ≤ q.1 ^ 2 + q.2 ^ 2}
  have hm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hT : MeasurableSet {x : ℝ | r ≤ x ^ 2} := measurableSet_le measurable_const (by fun_prop)
  set h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal x *
    {x : ℝ | r ≤ x ^ 2}.indicator (fun x => ENNReal.ofReal ((2 * π)⁻¹ * exp (-x ^ 2 / 2))) x
  have hmeas : Measurable h := by
    refine ENNReal.measurable_ofReal.mul (Measurable.indicator (by fun_prop) hT)
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    withDensity_apply _ hm, ← Measure.volume_eq_prod, ← lintegral_indicator hm,
    ← lintegral_comp_polarCoord_symm, polarCoord_target]
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal p.1 • S.indicator
      (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) (polarCoord.symm p) = h p.1 := by
    intro p
    have hsq : (p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2 = p.1 ^ 2 := by
      have := sin_sq_add_cos_sq p.2
      linear_combination p.1 ^ 2 * this
    simp only [polarCoord_symm_apply, smul_eq_mul, h, S, indicator, mem_ofPred_eq, hsq,
      gaussianPDF_mul]
  simp_rw [hpt]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ => h p.1) (hmeas.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_Ioo]
  have h2 : ∀ x ∈ Ioi (0 : ℝ), h x * ENNReal.ofReal (π - -π) =
      {x : ℝ | r ≤ x ^ 2}.indicator (fun x => ENNReal.ofReal (x * exp (-x ^ 2 / 2))) x := by
    intro x hx
    simp only [h, indicator]
    split_ifs
    · rw [← ENNReal.ofReal_mul hx.out.le, ← ENNReal.ofReal_mul (mul_nonneg hx.out.le (by positivity))]
      congr 1
      field_simp
      ring
    · simp
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, setLIntegral_indicator hT]
  rcases eq_or_lt_of_le hr with h0 | hpos
  · subst h0
    have : {x : ℝ | 0 ≤ x ^ 2} ∩ Ioi (0 : ℝ) = Ioi 0 := by
      ext x; simp [sq_nonneg]
    rw [this, lintegral_Ioi_exp le_rfl]; simp
  · have : {x : ℝ | r ≤ x ^ 2} ∩ Ioi (0 : ℝ) = Ici (√r) := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_Ici]
      constructor
      · rintro ⟨hrx, hx⟩
        exact Real.sqrt_le_iff.mpr ⟨hx.le, hrx⟩
      · intro hx
        have hs := Real.sqrt_pos.mpr hpos
        refine ⟨?_, hs.trans_le hx⟩
        calc r = √r ^ 2 := (Real.sq_sqrt hr).symm
          _ ≤ x ^ 2 := pow_le_pow_left₀ hs.le hx 2
    rw [this, setLIntegral_congr Ioi_ae_eq_Ici.symm, lintegral_Ioi_exp (Real.sqrt_nonneg r),
      Real.sq_sqrt hr]


lemma integral_gauss_exp {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ a, ENNReal.ofReal (exp (-(c * a ^ 2) / 2)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (√(1 / (1 + c))) := by
  have hint : Integrable (fun a : ℝ => exp (-(c * a ^ 2) / 2)) (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    have : 0 ≤ c * a ^ 2 := by positivity
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (exp_pos _).le),
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x • exp (-(c * x ^ 2) / 2)
      = (√(2 * π))⁻¹ * exp (-((1 + c) / 2) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc,
      ← exp_add]
    congr 2; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian]
  congr 1
  have h1 : π / ((1 + c) / 2) = (2 * π) * (1 / (1 + c)) := by field_simp
  have : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  rw [h1, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π), ← mul_assoc, inv_mul_cancel₀ this.ne',
    one_mul]

lemma key_sq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
      {p : ℝ × ℝ × ℝ | p.1 ^ 2 ≤ s * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)}
      = ENNReal.ofReal (√s) := by
  have hm : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ^ 2 ≤ s * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [Measure.prod_apply hm]
  set c := (1 - s) / s
  have hc : 0 ≤ c := div_nonneg (by linarith) hs0.le
  have hpre : ∀ a : ℝ, Prod.mk a ⁻¹' {p : ℝ × ℝ × ℝ | p.1 ^ 2 ≤ s * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)}
      = {q : ℝ × ℝ | c * a ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2} := by
    intro a
    ext q
    simp only [mem_preimage, mem_ofPred_eq, c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
    constructor <;> intro h <;> nlinarith
  simp_rw [hpre]
  simp_rw [gauss2_tail (mul_nonneg hc (sq_nonneg _))]
  rw [integral_gauss_exp hc]
  congr 2
  simp only [c]
  field_simp
  ring


/-- A symmetric finite measure on `ℝ` is determined by the law of the square. -/
lemma sym_ext {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.map (fun x => -x) = μ) (hν : ν.map (fun x => -x) = ν)
    (h : μ.map (fun x => x ^ 2) = ν.map (fun x => x ^ 2)) : μ = ν := by
  have pos : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi 0 → μ A = ν A := by
    intro A hA hAp
    have hB : MeasurableSet {y : ℝ | √y ∈ A} := Real.continuous_sqrt.measurable hA
    have hpre : (fun x : ℝ => x ^ 2) ⁻¹' {y | √y ∈ A} = A ∪ (fun x => -x) ⁻¹' A := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, Real.sqrt_sq_eq_abs, mem_union]
      constructor
      · intro hx
        rcases le_or_gt 0 x with h0 | h0
        · left; rwa [abs_of_nonneg h0] at hx
        · right; rwa [abs_of_neg h0] at hx
      · rintro (hx | hx)
        · rwa [abs_of_pos (hAp hx)]
        · have : (0 : ℝ) < -x := hAp hx
          rwa [abs_of_neg (by linarith)]
    have hdisj : Disjoint A ((fun x => -x) ⁻¹' A) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      have h1 : (0 : ℝ) < x := hAp hx
      have h2 : (0 : ℝ) < -x := hAp hx'
      linarith
    have e : ∀ m : Measure ℝ, m.map (fun x => -x) = m →
        (m.map (fun x => x ^ 2)) {y | √y ∈ A} = 2 * m A := by
      intro m hm
      rw [Measure.map_apply (by fun_prop) hB, hpre, measure_union hdisj (measurable_neg hA),
        ← Measure.map_apply measurable_neg hA, hm, two_mul]
    have h1 := e μ hμ
    rw [h, e ν hν] at h1
    exact ((ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp h1).symm
  have zero : μ {0} = ν {0} := by
    have hz : ({0} : Set ℝ) = (fun x : ℝ => x ^ 2) ⁻¹' {0} := by
      ext x; simp
    rw [hz, ← Measure.map_apply (by fun_prop) (measurableSet_singleton 0),
      ← Measure.map_apply (by fun_prop) (measurableSet_singleton 0), h]
  ext S hS
  have hT : MeasurableSet ((fun x : ℝ => -x) ⁻¹' S ∩ Ioi 0) := (measurable_neg hS).inter measurableSet_Ioi
  have hsplit : ∀ m : Measure ℝ, m.map (fun x => -x) = m →
      m S = m (S ∩ Ioi 0) + (m ((fun x : ℝ => -x) ⁻¹' S ∩ Ioi 0) + m (S ∩ {0})) := by
    intro m hm
    rw [← measure_inter_add_sdiff S measurableSet_Ioi,
      ← measure_inter_add_sdiff (S \ Ioi 0) measurableSet_Iio]
    have e1 : (S \ Ioi 0) ∩ Iio 0 = (fun x : ℝ => -x) ⁻¹' ((fun x : ℝ => -x) ⁻¹' S ∩ Ioi 0) := by
      ext x
      simp only [mem_inter_iff, Set.mem_sdiff, mem_Ioi, mem_Iio, mem_preimage, neg_neg, not_lt]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, by linarith⟩
    have e2 : (S \ Ioi 0) \ Iio 0 = S ∩ {0} := by
      ext x
      simp only [Set.mem_sdiff, mem_Ioi, mem_Iio, not_lt, mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, le_antisymm h2 h3⟩
      · rintro ⟨h1, rfl⟩; exact ⟨⟨h1, le_rfl⟩, le_rfl⟩
    rw [e1, e2, ← Measure.map_apply measurable_neg hT, hm]
  rw [hsplit μ hμ, hsplit ν hν, pos _ (hS.inter measurableSet_Ioi) inter_subset_right,
    pos _ hT inter_subset_right]
  congr 2
  by_cases h0 : (0 : ℝ) ∈ S
  · rw [inter_eq_right.mpr (singleton_subset_iff.mpr h0), zero]
  · rw [inter_singleton_eq_empty.mpr h0]; simp


/-- The product of three standard Gaussians. -/
def P3 : Measure (ℝ × ℝ × ℝ) :=
  (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance : IsProbabilityMeasure P3 := by unfold P3; infer_instance

/-- The first coordinate of `p / ‖p‖`. -/
def g (p : ℝ × ℝ × ℝ) : ℝ := (√(p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))⁻¹ * p.1

lemma measurable_g : Measurable g := by unfold g; fun_prop

lemma mp_split : MeasurePreserving (fun x : Fin 3 → ℝ => (x 0, x 1, x 2))
    (Measure.pi fun _ => gaussianReal 0 1) P3 := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 1) 0
  have h2 := (MeasurePreserving.id (gaussianReal 0 1)).prod
    (measurePreserving_finTwoArrow (gaussianReal 0 1))
  exact h2.comp h1

lemma law_eq : (Ball.sphUnif (EuclideanSpace ℝ (Fin 3))).map (fun ξ => ξ 0) = P3.map g := by
  rw [Ball.sphUnif, ← map_pi_eq_stdGaussian, Measure.map_map Ball.measurable_dir (by fun_prop),
    Measure.map_map (by fun_prop) (Ball.measurable_dir.comp (by fun_prop)), ← mp_split.map_eq,
    Measure.map_map measurable_g (by fun_prop)]
  congr 1
  ext x
  simp [Ball.dir, EuclideanSpace.norm_eq, Fin.sum_univ_three, g]


lemma P3_sym : (P3.map g).map (fun x => -x) = P3.map g := by
  rw [Measure.map_map measurable_neg measurable_g]
  have hP : P3.map (Prod.map (fun x : ℝ => -x) id) = P3 := by
    unfold P3
    rw [← Measure.map_prod_map _ _ measurable_neg measurable_id, gaussianReal_map_neg,
      Measure.map_id, neg_zero]
  have : (fun x => -x) ∘ g = g ∘ Prod.map (fun x : ℝ => -x) id := by
    ext p; simp [g]
  rw [this, ← Measure.map_map measurable_g (by fun_prop), hP]

lemma unifI_apply'' {l r : ℝ} (h : l < r) {S : Set ℝ} (hS : MeasurableSet S) :
    unifI l r S = (ENNReal.ofReal (r - l))⁻¹ * volume (S ∩ Icc l r) := by
  simp only [unifI, h, ↓reduceIte, smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply hS]

lemma unif_sym : (unifI (-1) 1).map (fun x => -x) = unifI (-1) 1 := by
  ext S hS
  rw [Measure.map_apply measurable_neg hS, unifI_apply'' (by norm_num) (measurable_neg hS),
    unifI_apply'' (by norm_num) hS]
  congr 1
  have : (fun x : ℝ => -x) ⁻¹' S ∩ Icc (-1) 1 = (fun x : ℝ => -x) ⁻¹' (S ∩ Icc (-1) 1) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  rw [this]
  exact Measure.measure_preimage_neg volume _

lemma unif_sq_cdf {s : ℝ} (hs : 0 ≤ s) :
    ((unifI (-1) 1).map (fun x => x ^ 2)) (Iic s) = ENNReal.ofReal (min (√s) 1) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x : ℝ => x ^ 2) ⁻¹' Iic s = Icc (-√s) (√s) := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Icc]
    rw [← abs_le, Real.le_sqrt (abs_nonneg x) hs, sq_abs]
  rw [hpre, unifI_apply'' (by norm_num) measurableSet_Icc, Icc_inter_Icc, max_neg_neg,
    Real.volume_Icc]
  have hm : 0 ≤ min (√s) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  rw [show (1 : ℝ) - -1 = 2 by norm_num, show min (√s) 1 - -min (√s) 1 = 2 * min (√s) 1 by ring,
    ENNReal.ofReal_mul (by norm_num), ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    one_mul]

lemma P3_sq_cdf {s : ℝ} (hs : 0 ≤ s) :
    ((P3.map g).map (fun x => x ^ 2)) (Iic s) = ENNReal.ofReal (min (√s) 1) := by
  rw [Measure.map_map (by fun_prop) measurable_g,
    Measure.map_apply ((by fun_prop : Measurable fun x : ℝ => x ^ 2).comp measurable_g)
      measurableSet_Iic]
  have hset : ((fun x : ℝ => x ^ 2) ∘ g) ⁻¹' Iic s
      = {p : ℝ × ℝ × ℝ | p.1 ^ 2 ≤ s * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)} := by
    ext p
    simp only [mem_preimage, Function.comp, mem_Iic, g, mem_ofPred_eq]
    have hD : 0 ≤ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by positivity
    have h1 : p.1 ^ 2 ≤ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]
    rw [mul_pow, inv_pow, Real.sq_sqrt hD]
    rcases eq_or_lt_of_le hD with h0 | h0
    · rw [← h0] at h1 ⊢
      have : p.1 ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      simp [this, hs]
    · rw [inv_mul_le_iff₀ h0, mul_comm]
  rw [hset]
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    simp only [Real.sqrt_zero, zero_le_one, min_eq_left, ENNReal.ofReal_zero]
    refine measure_mono_null (t := {0} ×ˢ univ) ?_ ?_
    · intro p hp
      simp only [zero_mul, mem_ofPred_eq] at hp
      exact ⟨pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hp (sq_nonneg _)), mem_univ _⟩
    · have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
      unfold P3; rw [Measure.prod_prod, measure_singleton, zero_mul]
  · rcases lt_or_ge s 1 with h1 | h1
    · rw [P3, key_sq hpos h1, min_eq_left]
      calc √s ≤ √1 := Real.sqrt_le_sqrt h1.le
        _ = 1 := Real.sqrt_one
    · have : {p : ℝ × ℝ × ℝ | p.1 ^ 2 ≤ s * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)} = univ := by
        ext p
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        nlinarith [sq_nonneg p.1, sq_nonneg p.2.1, sq_nonneg p.2.2]
      rw [this, measure_univ, min_eq_right (Real.one_le_sqrt.mpr h1), ENNReal.ofReal_one]

/-- **Archimedes' hat-box theorem**: the first coordinate of a uniform random point of the unit
sphere `S² ⊂ ℝ³` is uniform on `[-1, 1]`. This discharges `Remarks14.H_archimedes`. -/
theorem archimedes : Remarks14.H_archimedes := by
  unfold Remarks14.H_archimedes
  rw [law_eq]
  have := unifI_isProb (-1) 1
  refine sym_ext P3_sym unif_sym (Measure.ext_of_Iic _ _ fun s => ?_)
  rcases lt_or_ge s 0 with hs | hs
  · have hpre : (fun x : ℝ => x ^ 2) ⁻¹' Iic s = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact hs.trans_le (sq_nonneg x)
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic, Measure.map_apply (by fun_prop)
      measurableSet_Iic, hpre, measure_empty, measure_empty]
  · rw [P3_sq_cdf hs, unif_sq_cdf hs]


/-! ### Unconditional versions of the results of `Remarks14` that assume `H_archimedes` -/

/-- `Remarks14.isArchimedesMeasure_sphUnif` without hypothesis: the uniform distribution on `S²`
is an Archimedes measure, so Lemma 1 (`lem_arch`) holds with `ξ` uniform on `S²`. -/
theorem isArchimedesMeasure_sphUnif_uncond :
    IsArchimedesMeasure (Ball.sphUnif (EuclideanSpace ℝ (Fin 3))) :=
  Remarks14.isArchimedesMeasure_sphUnif archimedes

/-- Every projection `ξ ↦ ⟪e, ξ⟫` of the uniform distribution on `S²` is `U[-‖e‖, ‖e‖]`. -/
theorem sphUnif_map_inner_uncond (e : EuclideanSpace ℝ (Fin 3)) :
    (Ball.sphUnif (EuclideanSpace ℝ (Fin 3))).map (fun ξ => ⟪e, ξ⟫_ℝ) = unifI (-‖e‖) ‖e‖ :=
  isArchimedesMeasure_sphUnif_uncond.2 e

end Mixes.Archimedes
