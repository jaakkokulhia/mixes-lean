import Mixes.Large

/-!
# The local limit theorem for densities (Lemma 103) and Theorem 104

Work in progress; see `mixes/progress/W4d.md`.

Conventions. `E` is a finite-dimensional real inner product space with its canonical volume
(`measureSpaceOfInnerProductSpace`). The Fourier transform is Mathlib's
`𝓕 f ξ = ∫ e^{-2πi⟪x, ξ⟫} f x dx`, so the characteristic function `ĥ(ξ)` of the paper is
`𝓕 h (ξ / (2π))`, and the covariance form `ξᵀ Σ_h ξ` becomes `quadF h ξ = ∫ ⟪x, ξ⟫² h x dx`.
-/

open MeasureTheory Real Filter Topology RealInnerProductSpace
open scoped Convolution FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.LLT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The convolution power `h^{*m}` for `m ≥ 1` (`convPow h 0 = h` is a convention). -/
def convPow (h : E → ℝ) : ℕ → E → ℝ
  | 0 => h
  | 1 => h
  | (m + 2) => h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] convPow h (m + 1)

/-- The Fourier transform of a real function, as a complex function. -/
def hatC (h : E → ℝ) : E → ℂ := 𝓕 (fun x => (h x : ℂ))

/-- The covariance form `ξ ↦ ∫ ⟪x, ξ⟫² h(x) dx`. -/
def quadF (h : E → ℝ) (ξ : E) : ℝ := ∫ x, ⟪x, ξ⟫ ^ 2 * h x

/-- The centred normal density with covariance form `quadF h`, defined through its Fourier
transform `e^{-2π² quadF h ξ}` (which is the paper's `e^{-ξᵀΣ_hξ/2}` in Mathlib's convention). -/
def gaussD (h : E → ℝ) (x : E) : ℝ :=
  (𝓕⁻ (fun ξ => ((Real.exp (-2 * π ^ 2 * quadF h ξ) : ℝ) : ℂ)) x).re

/-- The class of densities of Lemma 103, with explicit parameters: measurable, `0 ≤ h ≤ M`,
vanishing outside the ball of radius `R`, total mass `1`, mean `0`, covariance at least `σ`. -/
structure InH (M R σ : ℝ) (h : E → ℝ) : Prop where
  meas : Measurable h
  nonneg : ∀ x, 0 ≤ h x
  le : ∀ x, h x ≤ M
  supp : ∀ x, R < ‖x‖ → h x = 0
  int1 : ∫ x, h x = 1
  mean : ∫ x, h x • x = 0
  var : ∀ ξ, σ * ‖ξ‖ ^ 2 ≤ quadF h ξ

section Basic

variable {M R σ : ℝ} {h : E → ℝ}

lemma InH.integrable (hh : InH M R σ h) : Integrable h := by
  by_contra hc
  have := integral_undef hc
  rw [hh.int1] at this
  exact one_ne_zero this

lemma InH.M_nonneg (hh : InH M R σ h) : 0 ≤ M := (hh.nonneg 0).trans (hh.le 0)

lemma InH.norm_le (hh : InH M R σ h) {x : E} (hx : h x ≠ 0) : ‖x‖ ≤ R := by
  by_contra hc
  exact hx (hh.supp x (not_le.1 hc))

/-- Convolution with a density preserves `0 ≤ · ≤ M`, integrability and mass `1`. -/
lemma conv_props (hh : InH M R σ h) {g : E → ℝ} (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgM : ∀ x, g x ≤ M) (hg1 : ∫ x, g x = 1) :
    let f := h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g
    Integrable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ M) ∧ ∫ x, f x = 1 := by
  intro f
  refine ⟨hh.integrable.integrable_convolution _ hg, fun x => ?_, fun x => ?_, ?_⟩
  · simp only [f, convolution_def, ContinuousLinearMap.mul_apply']
    exact integral_nonneg fun t => mul_nonneg (hh.nonneg t) (hg0 _)
  · simp only [f, convolution_def, ContinuousLinearMap.mul_apply']
    calc ∫ t, h t * g (x - t) ≤ ∫ t, h t * M := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t =>
            mul_nonneg (hh.nonneg t) (hg0 _)) (hh.integrable.mul_const M)
            (Eventually.of_forall fun t => mul_le_mul_of_nonneg_left (hgM _) (hh.nonneg t))
      _ = M := by rw [integral_mul_const, hh.int1, one_mul]
  · simp only [f]
    rw [integral_convolution _ hh.integrable hg, hh.int1, hg1]
    simp

lemma convPow_props (hh : InH M R σ h) (m : ℕ) :
    Integrable (convPow h m) ∧ (∀ x, 0 ≤ convPow h m x) ∧ (∀ x, convPow h m x ≤ M) ∧
      ∫ x, convPow h m x = 1 := by
  induction m with
  | zero => exact ⟨hh.integrable, hh.nonneg, hh.le, hh.int1⟩
  | succ k ih =>
    rcases k with _ | k
    · exact ⟨hh.integrable, hh.nonneg, hh.le, hh.int1⟩
    · exact conv_props hh ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

lemma convPow_add_two (h : E → ℝ) (m : ℕ) :
    convPow h (m + 2) = h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] convPow h (m + 1) := rfl

/-- `h ⋆ g` is continuous when `h` is integrable and `g` is bounded and measurable: it is a
uniform limit of the continuous functions `φ ⋆ g`, `φ` continuous with compact support. -/
lemma continuous_conv_of_bdd {h g : E → ℝ} (hh : Integrable h) (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) :
    Continuous (h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
  have hgi : LocallyIntegrable g volume := by
    refine fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    exact Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne
      hg.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hgM x)
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨φ, hφs, hφε, hφc, hφi⟩ :=
    hh.exists_hasCompactSupport_integral_sub_le (ε := ε / (2 * (M + 1))) (by positivity)
  refine ⟨φ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g,
    hφs.continuous_convolution_left _ hφc hgi, fun y => hεu ?_⟩
  rw [dist_eq_norm, Real.norm_eq_abs]
  have hgs : ∀ f : E → ℝ, Integrable f → Integrable (fun t => f t * g (y - t)) := fun f hf =>
    hf.mul_bdd (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa using hgM (y - t))
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_sub (hgs h hh) (hgs φ hφi)]
  calc |∫ t, (h t * g (y - t) - φ t * g (y - t))|
      ≤ ∫ t, |h t * g (y - t) - φ t * g (y - t)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, ‖h t - φ t‖ * M := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
          ((hh.sub hφi).norm.mul_const M) (Eventually.of_forall fun t => ?_)
        show |h t * g (y - t) - φ t * g (y - t)| ≤ ‖h t - φ t‖ * M
        rw [← sub_mul, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hgM _) (abs_nonneg _)
    _ = (∫ t, ‖h t - φ t‖) * M := integral_mul_const _ _
    _ ≤ ε / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hφε hM
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

end Basic

section Fourier

open ComplexConjugate

variable {M R σ : ℝ} {h : E → ℝ}

lemma ofReal_conv (h g : E → ℝ) (x : E) :
    (((h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x : ℝ) : ℂ) =
      ((fun x => (h x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun x => (g x : ℂ))) x := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  push_cast
  rfl

lemma fourier_mul_conv {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : E) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ξ = 𝓕 f ξ * 𝓕 g ξ :=
  Real.fourier_mul_convolution_eq (R := ℂ) hf hg ξ

lemma fourier_convPow (hh : InH M R σ h) (m : ℕ) (ξ : E) :
    𝓕 (fun x => (convPow h (m + 1) x : ℂ)) ξ = hatC h ξ ^ (m + 1) := by
  induction m with
  | zero => simp [convPow, hatC]
  | succ k ih =>
    have hf : (fun x => (convPow h (k + 2) x : ℂ)) =
        (fun x => (h x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun x => (convPow h (k + 1) x : ℂ)) := funext fun x => ofReal_conv _ _ x
    rw [show k + 1 + 1 = k + 2 by ring, hf, fourier_mul_conv (f := fun x => (h x : ℂ))
      (g := fun x => (convPow h (k + 1) x : ℂ)) hh.integrable.ofReal
      (convPow_props hh (k + 1)).1.ofReal ξ, ih, hatC]
    ring

lemma norm_hatC_le (hh : InH M R σ h) (ξ : E) : ‖hatC h ξ‖ ≤ 1 := by
  refine (Real.norm_fourier_le_integral_norm _ ξ).trans ?_
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hh.nonneg _), hh.int1, le_refl]

lemma continuous_hatC (hh : InH M R σ h) : Continuous (hatC h) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner hh.integrable.ofReal

lemma fourier_neg_conj (h : E → ℝ) (ξ : E) :
    𝓕 (fun x => ((h (-x)) : ℂ)) ξ = conj (hatC h ξ) := by
  rw [hatC, Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  rw [← integral_neg_eq_self]
  congr 1; funext v
  simp only [neg_neg, inner_neg_left, smul_eq_mul, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  simp [Complex.conj_ofReal, map_ofNat]

lemma integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : E => Real.exp (-b * ‖ξ‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine this.congr (Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero]
  rw [show -(b : ℂ) * (‖v‖ : ℂ) ^ 2 = ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_ofReal]

/-- Gaussian-weighted Plancherel bound: `∫ e^{-a|ξ|²} |ĥ(ξ)|² ≤ M`. -/
lemma gauss_hatC_sq_le (hh : InH M R σ h) {a : ℝ} (ha : 0 < a) :
    ∫ ξ, Real.exp (-a * ‖ξ‖ ^ 2) * ‖hatC h ξ‖ ^ 2 ≤ M := by
  set hr : E → ℝ := fun x => h (-x)
  have hri : Integrable hr := hh.integrable.comp_neg
  have hr1 : ∫ x, hr x = 1 := by rw [integral_neg_eq_self (fun x => h x), hh.int1]
  obtain ⟨hgi, hg0, hgM, -⟩ := conv_props hh hri (fun x => hh.nonneg _) (fun x => hh.le _) hr1
  set g := h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] hr
  have hFg : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = ((‖hatC h ξ‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
    have hf : (fun x => (g x : ℂ)) = (fun x => (h x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun x => (hr x : ℂ)) := funext fun x => ofReal_conv _ _ x
    rw [hf, fourier_mul_conv (f := fun x => (h x : ℂ)) (g := fun x => (hr x : ℂ))
      hh.integrable.ofReal hri.ofReal ξ,
      fourier_neg_conj, ← hatC, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set Gc : E → ℂ := fun v => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2)
  have hGc : Integrable Gc := by
    simpa [Gc] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (a : ℂ)) (by simpa using ha) 0 0
  have hmul : ∫ ξ, 𝓕 Gc ξ * (g ξ : ℂ) = ∫ x, Gc x * 𝓕 (fun x => (g x : ℂ)) x := by
    have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
      (e := Real.fourierChar) (μ := volume) (ν := volume) (f := Gc) (g := fun x => (g x : ℂ))
      Real.continuous_fourierChar continuous_inner hGc hgi.ofReal
    rw [show (innerₗ E).flip = innerₗ E from LinearMap.ext₂ fun x y => real_inner_comm x y] at this
    simp only [smul_eq_mul] at this
    exact this
  set c : ℝ := (π / a) ^ ((Module.finrank ℝ E : ℝ) / 2)
  have hc : 0 ≤ c := by positivity
  have hFG : ∀ ξ, 𝓕 Gc ξ = ((c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) : ℝ) : ℂ) := fun ξ => by
    rw [fourier_gaussian_innerProductSpace (by simpa using ha)]
    simp only [c, Complex.ofReal_mul, Complex.ofReal_exp]
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 2
    ring
  have hL : ∫ ξ, Real.exp (-a * ‖ξ‖ ^ 2) * ‖hatC h ξ‖ ^ 2 =
      ∫ ξ, c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) * g ξ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    have e1 : (fun ξ => ((Real.exp (-a * ‖ξ‖ ^ 2) * ‖hatC h ξ‖ ^ 2 : ℝ) : ℂ)) =
        fun x => Gc x * 𝓕 (fun x => (g x : ℂ)) x := funext fun x => by
      rw [hFg]; simp only [Gc]; push_cast; rfl
    have e2 : (fun ξ => ((c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) * g ξ : ℝ) : ℂ)) =
        fun ξ => 𝓕 Gc ξ * (g ξ : ℂ) := funext fun x => by
      rw [hFG]; push_cast; rfl
    rw [e1, e2, hmul]
  have hGi : Integrable fun ξ : E => c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) := by
    exact (integrable_gauss (E := E) (b := π ^ 2 / a) (by positivity)).const_mul c
  have hG1 : ∫ ξ : E, c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) = 1 := by
    rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    simp only [c]
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show π / a * (π / (π ^ 2 / a)) = 1 by field_simp, Real.one_rpow]
  rw [hL]
  calc ∫ ξ, c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) * g ξ
      ≤ ∫ ξ, c * Real.exp (-(π ^ 2 / a) * ‖ξ‖ ^ 2) * M :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => by
          have := hg0 ξ; positivity) (hGi.mul_const M)
          (Eventually.of_forall fun ξ => mul_le_mul_of_nonneg_left (hgM ξ) (by positivity))
    _ = M := by rw [integral_mul_const, hG1, one_mul]

/-- Plancherel bound: `|ĥ|²` is integrable with `∫ |ĥ|² ≤ M` (by Fatou's lemma from
`gauss_hatC_sq_le`). -/
lemma hatC_sq (hh : InH M R σ h) :
    Integrable (fun ξ => ‖hatC h ξ‖ ^ 2) ∧ ∫ ξ, ‖hatC h ξ‖ ^ 2 ≤ M := by
  set F : E → ℝ := fun ξ => ‖hatC h ξ‖ ^ 2
  have hFc : Continuous F := (continuous_hatC hh).norm.pow 2
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => by positivity
  set f : ℕ → E → ℝ := fun k ξ => Real.exp (-(1 / ((k : ℝ) + 1)) * ‖ξ‖ ^ 2) * F ξ
  have hfi : ∀ k, Integrable (f k) := fun k =>
    (integrable_gauss (E := E) (b := 1 / ((k : ℝ) + 1)) (by positivity)).mul_bdd
      hFc.aestronglyMeasurable (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
        exact pow_le_one₀ (norm_nonneg _) (norm_hatC_le hh ξ))
  have hfle : ∀ k, ∫⁻ ξ, ENNReal.ofReal (f k ξ) ≤ ENNReal.ofReal M := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k)
      (Eventually.of_forall fun ξ => by have := hF0 ξ; simp only [f]; positivity)]
    exact ENNReal.ofReal_le_ofReal (gauss_hatC_sq_le hh (by positivity))
  have hlim : ∀ ξ, Tendsto (fun k => ENNReal.ofReal (f k ξ)) atTop (𝓝 (ENNReal.ofReal (F ξ))) :=
    fun ξ => by
      refine ENNReal.tendsto_ofReal ?_
      have h1 : Tendsto (fun k : ℕ => Real.exp (-(1 / ((k : ℝ) + 1)) * ‖ξ‖ ^ 2)) atTop
          (𝓝 (Real.exp (-0 * ‖ξ‖ ^ 2))) :=
        (Real.continuous_exp.tendsto _).comp
          ((tendsto_one_div_add_atTop_nhds_zero_nat.neg).mul_const _)
      simpa [f] using h1.mul_const (F ξ)
  have hlin : ∫⁻ ξ, ENNReal.ofReal (F ξ) ≤ ENNReal.ofReal M := by
    calc ∫⁻ ξ, ENNReal.ofReal (F ξ)
        = ∫⁻ ξ, liminf (fun k => ENNReal.ofReal (f k ξ)) atTop :=
          lintegral_congr fun ξ => (hlim ξ).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ ξ, ENNReal.ofReal (f k ξ)) atTop :=
          lintegral_liminf_le fun k => ENNReal.measurable_ofReal.comp
            ((Real.continuous_exp.comp (continuous_const.mul
              (continuous_norm.pow 2))).mul hFc).measurable
      _ ≤ ENNReal.ofReal M :=
          liminf_le_of_frequently_le' (Frequently.of_forall hfle)
  have hFi : Integrable F := by
    refine ⟨hFc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hFi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hFc.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hh.M_nonneg hlin

end Fourier

section Inversion

variable {M R σ : ℝ} {h : E → ℝ}

lemma convPow_cont (hh : InH M R σ h) (k : ℕ) :
    Measurable (convPow h (k + 1)) ∧ Continuous (convPow h (k + 2)) := by
  have step : ∀ k, Measurable (convPow h (k + 1)) → Continuous (convPow h (k + 2)) := fun k hk =>
    continuous_conv_of_bdd hh.integrable hk (M := M) fun x => by
      rw [abs_of_nonneg ((convPow_props hh _).2.1 x)]; exact (convPow_props hh _).2.2.1 x
  induction k with
  | zero => exact ⟨hh.meas, step 0 hh.meas⟩
  | succ k ih => exact ⟨ih.2.measurable, step (k + 1) ih.2.measurable⟩

lemma integrable_hatC_pow (hh : InH M R σ h) (k : ℕ) :
    Integrable (fun ξ => hatC h ξ ^ (k + 2)) := by
  refine (hatC_sq hh).1.mono' ((continuous_hatC hh).pow _).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_pow, pow_add]
  exact mul_le_of_le_one_left (sq_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_hatC_le hh ξ))

/-- Fourier inversion for `h^{*m}`, `m ≥ 2`, at every point. -/
lemma convPow_eq_inv (hh : InH M R σ h) (k : ℕ) (y : E) :
    (convPow h (k + 2) y : ℂ) = ∫ ξ, 𝐞 ⟪ξ, y⟫ • hatC h ξ ^ (k + 2) := by
  have hF : 𝓕 (fun x => (convPow h (k + 2) x : ℂ)) = fun ξ => hatC h ξ ^ (k + 2) :=
    funext fun ξ => fourier_convPow hh (k + 1) ξ
  have hi : Integrable (fun x => (convPow h (k + 2) x : ℂ)) := (convPow_props hh (k + 2)).1.ofReal
  have := hi.fourierInv_fourier_eq (by rw [hF]; exact integrable_hatC_pow hh k)
    (Complex.continuous_ofReal.comp (convPow_cont hh k).2).continuousAt (v := y)
  rw [← this, hF, Real.fourierInv_eq]

end Inversion

section Taylor

variable {M R σ : ℝ} {h : E → ℝ}

lemma integrable_supp (hh : InH M R σ h) {g : E → ℝ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hC : ∀ v, ‖v‖ ≤ R → |g v| ≤ C) : Integrable (fun v => g v * h v) := by
  refine (hh.integrable.const_mul C).mono' (hg.mul hh.meas.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh.nonneg v)]
  by_cases h0 : h v = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hC v (hh.norm_le h0)) (hh.nonneg v)

lemma integrable_inner_mul (hh : InH M R σ h) (ζ : E) (k : ℕ) :
    Integrable (fun v => ⟪v, ζ⟫ ^ k * h v) :=
  integrable_supp hh ((continuous_id.inner continuous_const).pow k).aestronglyMeasurable
    (C := (R * ‖ζ‖) ^ k) fun v hv => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm v ζ).trans
        (mul_le_mul_of_nonneg_right hv (norm_nonneg _))) k

lemma integral_inner_mul (hh : InH M R σ h) (ζ : E) : ∫ v, ⟪v, ζ⟫ * h v = 0 := by
  have hi : Integrable (fun v => h v • v) := by
    refine (hh.integrable.const_mul R).mono' (hh.meas.aestronglyMeasurable.smul
      aestronglyMeasurable_id) (Eventually.of_forall fun v => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hh.nonneg v), mul_comm]
    by_cases h0 : h v = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (hh.norm_le h0) (hh.nonneg v)
  have := integral_inner (𝕜 := ℝ) hi ζ
  rw [hh.mean, inner_zero_right] at this
  rw [← this]
  congr 1; funext v
  rw [real_inner_smul_right, real_inner_comm, mul_comm]

lemma quadF_le (hh : InH M R σ h) (ζ : E) : quadF h ζ ≤ R ^ 2 * ‖ζ‖ ^ 2 := by
  have hR : ∀ v, ⟪v, ζ⟫ ^ 2 * h v ≤ (R * ‖ζ‖) ^ 2 * h v := fun v => by
    by_cases h0 : h v = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_right ?_ (hh.nonneg v)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm v ζ).trans
        (mul_le_mul_of_nonneg_right (hh.norm_le h0) (norm_nonneg _))) 2
  calc quadF h ζ ≤ ∫ v, (R * ‖ζ‖) ^ 2 * h v :=
        integral_mono (integrable_inner_mul hh ζ 2) (hh.integrable.const_mul _) hR
    _ = R ^ 2 * ‖ζ‖ ^ 2 := by rw [integral_const_mul, hh.int1]; ring

lemma quadF_nonneg (hh : InH M R σ h) (ζ : E) : 0 ≤ quadF h ζ :=
  integral_nonneg fun v => mul_nonneg (sq_nonneg _) (hh.nonneg v)

lemma quadF_smul (h : E → ℝ) (c : ℝ) (ζ : E) : quadF h (c • ζ) = c ^ 2 * quadF h ζ := by
  simp only [quadF, inner_smul_right, mul_pow, mul_assoc]
  rw [integral_const_mul]

lemma continuous_quadF (hh : InH M R σ h) : Continuous (quadF h) := by
  refine continuous_iff_continuousAt.2 fun ζ₀ => ?_
  refine continuousAt_of_dominated (bound := fun v => (R * (‖ζ₀‖ + 1)) ^ 2 * h v) ?_ ?_
    (hh.integrable.const_mul _) (Eventually.of_forall fun v => by fun_prop)
  · exact Eventually.of_forall fun ζ => (integrable_inner_mul hh ζ 2).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds ζ₀ one_pos] with ζ hζ
    refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hh.nonneg v))]
    by_cases h0 : h v = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_right ?_ (hh.nonneg v)
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm v ζ).trans
        (mul_le_mul (hh.norm_le h0) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hh.norm_le h0))))
        2
      have := norm_le_norm_add_norm_sub' ζ ζ₀
      rw [Metric.mem_ball, dist_eq_norm] at hζ
      linarith

lemma norm_exp_sub_taylor (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 := by
  have := Complex.exp_bound hz (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  calc ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ = ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ := by
        ring_nf
    _ ≤ ‖z‖ ^ 3 * (4 * (6 * 3 : ℝ)⁻¹) := by convert this using 2; norm_num
    _ ≤ ‖z‖ ^ 3 := by
        have := pow_nonneg (norm_nonneg z) 3
        nlinarith

/-- Second-order Taylor bound for `ĥ` at `0` (mean `0`, covariance form `quadF h`). -/
lemma hatC_taylor (hh : InH M R σ h) {ζ : E} (hζ : 2 * π * R * ‖ζ‖ ≤ 1) :
    ‖hatC h ζ - (1 - 2 * π ^ 2 * quadF h ζ)‖ ≤ (2 * π * R * ‖ζ‖) ^ 3 := by
  set z : E → ℂ := fun v => ((-2 * π * ⟪v, ζ⟫ : ℝ) : ℂ) * Complex.I
  have hz : ∀ v, ‖v‖ ≤ R → ‖z v‖ ≤ 2 * π * R * ‖ζ‖ := fun v hv => by
    simp only [z, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos pi_pos]
    have := (abs_real_inner_le_norm v ζ).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg ζ))
    norm_num
    nlinarith [pi_pos]
  have hzc : Continuous z := by fun_prop
  have hhC : Integrable (fun v => (h v : ℂ)) := hh.integrable.ofReal
  have hexp : hatC h ζ = ∫ v, Complex.exp (z v) * (h v : ℂ) := by
    rw [hatC, Real.fourier_eq']
    rfl
  have hi1 : Integrable (fun v => Complex.exp (z v) * (h v : ℂ)) := by
    refine hhC.bdd_mul (c := 1) (hzc.cexp).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    simp only [z, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    simp
  have hi2 : Integrable (fun v => (((1 - 2 * π ^ 2 * ⟪v, ζ⟫ ^ 2) * h v : ℝ) : ℂ)) := by
    have : Integrable (fun v => (1 - 2 * π ^ 2 * ⟪v, ζ⟫ ^ 2) * h v) := by
      have := hh.integrable.sub ((integrable_inner_mul hh ζ 2).const_mul (2 * π ^ 2))
      refine this.congr (Eventually.of_forall fun v => ?_)
      simp only [Pi.sub_apply]
      ring
    exact this.ofReal
  have hi3 : Integrable (fun v => ((-2 * π * (⟪v, ζ⟫ * h v) : ℝ) : ℂ) * Complex.I) :=
    (((integrable_inner_mul hh ζ 1).const_mul (-2 * π)).ofReal.mul_const Complex.I).congr
      (Eventually.of_forall fun v => by simp)
  have hpt : ∀ v, (Complex.exp (z v) - 1 - z v - z v ^ 2 / 2) * (h v : ℂ) =
      Complex.exp (z v) * (h v : ℂ) - ((((1 - 2 * π ^ 2 * ⟪v, ζ⟫ ^ 2) * h v : ℝ) : ℂ) +
        ((-2 * π * (⟪v, ζ⟫ * h v) : ℝ) : ℂ) * Complex.I) := fun v => by
    simp only [z]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hdiff : hatC h ζ - (1 - 2 * π ^ 2 * quadF h ζ) =
      ∫ v, (Complex.exp (z v) - 1 - z v - z v ^ 2 / 2) * (h v : ℂ) := by
    simp_rw [hpt]
    have hs := integral_sub hi1 (hi2.add hi3)
    simp only [Pi.add_apply] at hs
    rw [hs, integral_add hi2 hi3, ← hexp, integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
    have e1 : ∫ v, (1 - 2 * π ^ 2 * ⟪v, ζ⟫ ^ 2) * h v = 1 - 2 * π ^ 2 * quadF h ζ := by
      have := integral_sub hh.integrable ((integrable_inner_mul hh ζ 2).const_mul (2 * π ^ 2))
      rw [integral_const_mul, hh.int1, ← quadF] at this
      rw [← this]
      congr 1; funext v; ring
    have e2 : ∫ v, -2 * π * (⟪v, ζ⟫ * h v) = 0 := by
      rw [integral_const_mul, integral_inner_mul hh ζ, mul_zero]
    rw [e1, e2]
    push_cast
    ring
  rw [hdiff]
  calc ‖∫ v, (Complex.exp (z v) - 1 - z v - z v ^ 2 / 2) * (h v : ℂ)‖
      ≤ ∫ v, ‖(Complex.exp (z v) - 1 - z v - z v ^ 2 / 2) * (h v : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v, (2 * π * R * ‖ζ‖) ^ 3 * h v := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          (hh.integrable.const_mul _) (Eventually.of_forall fun v => ?_)
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hh.nonneg v)]
        by_cases h0 : h v = 0
        · simp [h0]
        · refine mul_le_mul_of_nonneg_right ?_ (hh.nonneg v)
          have h1 := hz v (hh.norm_le h0)
          exact (norm_exp_sub_taylor _ (h1.trans hζ)).trans
            (pow_le_pow_left₀ (norm_nonneg _) h1 3)
    _ = (2 * π * R * ‖ζ‖) ^ 3 := by rw [integral_const_mul, hh.int1, mul_one]

end Taylor

section Pointwise

variable {M R σ : ℝ} {h : E → ℝ}

lemma norm_pow_sub_pow_le (a b : ℂ) {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) (m : ℕ) :
    ‖a ^ (m + 1) - b ^ (m + 1)‖ ≤ (m + 1) * ‖a - b‖ * c ^ m := by
  have hc : 0 ≤ c := (norm_nonneg _).trans ha
  induction m with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) = a * (a ^ (k + 1) - b ^ (k + 1)) +
        (a - b) * b ^ (k + 1) := by ring
    rw [e]
    calc ‖a * (a ^ (k + 1) - b ^ (k + 1)) + (a - b) * b ^ (k + 1)‖
        ≤ ‖a‖ * ‖a ^ (k + 1) - b ^ (k + 1)‖ + ‖a - b‖ * ‖b‖ ^ (k + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ c * ((k + 1) * ‖a - b‖ * c ^ k) + ‖a - b‖ * c ^ (k + 1) := by
          gcongr
      _ = ((k + 1 : ℕ) + 1 : ℝ) * ‖a - b‖ * c ^ (k + 1) := by push_cast; ring

/-- The radius of the inner region. -/
def r0 (R σ : ℝ) : ℝ := min (1 / (2 * π * R)) (σ / (8 * π * R ^ 3))

lemma r0_pos (hR : 0 < R) (hσ : 0 < σ) : 0 < r0 R σ := by
  unfold r0; positivity

/-- Pointwise bounds in the inner region `‖ζ‖ ≤ r₀`. -/
lemma inner_bounds (hh : InH M R σ h) (hR : 0 < R) {ζ : E} (hζ : ‖ζ‖ ≤ r0 R σ) :
    ‖hatC h ζ - (Real.exp (-2 * π ^ 2 * quadF h ζ) : ℂ)‖ ≤ 10 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 ∧
      ‖hatC h ζ‖ ≤ Real.exp (-(π ^ 2 * σ) * ‖ζ‖ ^ 2) ∧
      Real.exp (-2 * π ^ 2 * quadF h ζ) ≤ Real.exp (-(π ^ 2 * σ) * ‖ζ‖ ^ 2) := by
  have h1 : ‖ζ‖ ≤ 1 / (2 * π * R) := hζ.trans (min_le_left _ _)
  have h2 : ‖ζ‖ ≤ σ / (8 * π * R ^ 3) := hζ.trans (min_le_right _ _)
  have hpR : 0 < 2 * π * R := by positivity
  have hs : 2 * π * R * ‖ζ‖ ≤ 1 := by
    rw [le_div_iff₀ hpR] at h1; linarith
  have hs' : 8 * π * R ^ 3 * ‖ζ‖ ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at h2; linarith
  have hT := hatC_taylor hh hs
  have hQ := quadF_le hh ζ
  have hQ0 := quadF_nonneg hh ζ
  have hQσ := hh.var ζ
  have hn := norm_nonneg ζ
  have hx : 2 * π ^ 2 * quadF h ζ ≤ 1 / 2 := by
    have h0 : 0 ≤ 2 * π * R * ‖ζ‖ := by positivity
    have : (2 * π * R * ‖ζ‖) ^ 2 ≤ 1 := by nlinarith
    have e : 2 * π ^ 2 * (R ^ 2 * ‖ζ‖ ^ 2) = (2 * π * R * ‖ζ‖) ^ 2 / 2 := by ring
    have : 2 * π ^ 2 * quadF h ζ ≤ 2 * π ^ 2 * (R ^ 2 * ‖ζ‖ ^ 2) := by
      have := pi_pos; gcongr
    linarith
  -- the exponential
  have hE : ‖((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) - (1 - 2 * π ^ 2 * quadF h ζ)‖ ≤
      (2 * π ^ 2 * quadF h ζ) ^ 2 := by
    have := Real.norm_exp_sub_one_sub_id_le (x := -2 * π ^ 2 * quadF h ζ) (by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at this
    rw [show ((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) - (1 - 2 * π ^ 2 * quadF h ζ) =
      ((Real.exp (-2 * π ^ 2 * quadF h ζ) - 1 - -2 * π ^ 2 * quadF h ζ : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    convert this using 1; ring
  have hcube : (2 * π * R * ‖ζ‖) ^ 3 = 8 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 := by ring
  refine ⟨?_, ?_, ?_⟩
  · calc ‖hatC h ζ - (Real.exp (-2 * π ^ 2 * quadF h ζ) : ℂ)‖
        ≤ ‖hatC h ζ - (1 - 2 * π ^ 2 * quadF h ζ)‖ +
          ‖((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) - (1 - 2 * π ^ 2 * quadF h ζ)‖ := by
          refine (norm_sub_le_norm_sub_add_norm_sub _ ((1 : ℂ) - 2 * π ^ 2 * quadF h ζ) _).trans
            (le_of_eq ?_)
          rw [norm_sub_rev ((1 : ℂ) - _)]
      _ ≤ 8 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 + (2 * π ^ 2 * quadF h ζ) ^ 2 := by
          rw [← hcube]; exact add_le_add hT hE
      _ ≤ 10 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 := by
          have hq : (2 * π ^ 2 * quadF h ζ) ^ 2 ≤ (2 * π ^ 2 * (R ^ 2 * ‖ζ‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by nlinarith [pi_pos]) 2
          have : (2 * π ^ 2 * (R ^ 2 * ‖ζ‖ ^ 2)) ^ 2 ≤ 2 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 := by
            have e : (2 * π ^ 2 * (R ^ 2 * ‖ζ‖ ^ 2)) ^ 2 =
                (2 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3) * (2 * π * R * ‖ζ‖) := by ring
            rw [e]
            exact mul_le_of_le_one_right (by positivity) hs
          linarith
  · calc ‖hatC h ζ‖ ≤ ‖((1 - 2 * π ^ 2 * quadF h ζ : ℝ) : ℂ)‖ +
          ‖hatC h ζ - (1 - 2 * π ^ 2 * quadF h ζ)‖ := by
          have := norm_le_insert' (hatC h ζ) ((1 : ℂ) - 2 * π ^ 2 * quadF h ζ)
          push_cast; exact this
      _ ≤ (1 - 2 * π ^ 2 * quadF h ζ) + 8 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), ← hcube]
          linarith
      _ ≤ 1 - π ^ 2 * σ * ‖ζ‖ ^ 2 := by
          have : 8 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 ≤ π ^ 2 * σ * ‖ζ‖ ^ 2 := by
            have e : 8 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3 = (8 * π * R ^ 3 * ‖ζ‖) * (π ^ 2 * ‖ζ‖ ^ 2) := by
              ring
            rw [e, show π ^ 2 * σ * ‖ζ‖ ^ 2 = σ * (π ^ 2 * ‖ζ‖ ^ 2) by ring]
            exact mul_le_mul_of_nonneg_right hs' (by positivity)
          nlinarith [pi_pos]
      _ ≤ Real.exp (-(π ^ 2 * σ) * ‖ζ‖ ^ 2) := by
          have := Real.add_one_le_exp (-(π ^ 2 * σ) * ‖ζ‖ ^ 2); linarith
  · exact Real.exp_le_exp.2 (by nlinarith [pi_pos, sq_nonneg ‖ζ‖])

end Pointwise

section Pointwise2

variable {M R σ : ℝ} {h : E → ℝ}

/-- The pointwise bound on `|ĥ(η/√m)^m - e^{-2π² Q(η)}|`, `m = k + 2`, valid for all `η`: the
inner region gives the first term, the outer region the other two. -/
lemma pt_bound (hh : InH M R σ h) (hR : 0 < R) (hσ : 0 < σ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ ξ, r0 R σ ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) (k : ℕ) (η : E) :
    ‖hatC h ((Real.sqrt (k + 2))⁻¹ • η) ^ (k + 2) - (Real.exp (-2 * π ^ 2 * quadF h η) : ℂ)‖ ≤
      10 * π ^ 3 * R ^ 3 / Real.sqrt (k + 2) *
          (‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2)) +
        q ^ k * ‖hatC h ((Real.sqrt (k + 2))⁻¹ • η)‖ ^ 2 +
        Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) * Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2) := by
  set s := Real.sqrt (k + 2) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (k + 2 : ℝ) := Real.sq_sqrt (by positivity)
  set ζ := s⁻¹ • η with hζ_def
  have hηζ : η = s • ζ := by rw [hζ_def, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hnζ : ‖ζ‖ = ‖η‖ / s := by
    rw [hζ_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_eq_div]
  have hQ : quadF h η = (k + 2) * quadF h ζ := by rw [hηζ, quadF_smul, hs2]
  have hb : ((Real.exp (-2 * π ^ 2 * quadF h η) : ℝ) : ℂ) =
      ((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) ^ (k + 2) := by
    rw [← Complex.ofReal_pow, ← Real.exp_natCast_mul, hQ]; push_cast; ring_nf
  have hT1 : 0 ≤ 10 * π ^ 3 * R ^ 3 / s * (‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2)) := by
    positivity
  have hT2 : 0 ≤ q ^ k * ‖hatC h ζ‖ ^ 2 := by positivity
  have hT3 : 0 ≤ Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) *
      Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2) := by positivity
  rw [hb]
  rcases le_or_gt ‖ζ‖ (r0 R σ) with hin | hout
  · obtain ⟨h1, h2, h3⟩ := inner_bounds hh hR hin
    have hb' : ‖((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ)‖ ≤
        Real.exp (-(π ^ 2 * σ) * ‖ζ‖ ^ 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact h3
    have := norm_pow_sub_pow_le _ _ h2 hb' (k + 1)
    refine le_trans ?_ (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg le_rfl hT2) hT3)
    refine this.trans ?_
    calc ((k + 1 : ℕ) + 1 : ℝ) * ‖hatC h ζ - ((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ)‖ *
          Real.exp (-(π ^ 2 * σ) * ‖ζ‖ ^ 2) ^ (k + 1)
        ≤ ((k + 1 : ℕ) + 1 : ℝ) * (10 * π ^ 3 * R ^ 3 * ‖ζ‖ ^ 3) *
          Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2) := by
          gcongr
          rw [← Real.exp_natCast_mul, hnζ, div_pow, hs2]
          refine Real.exp_le_exp.2 ?_
          have : (0 : ℝ) ≤ π ^ 2 * σ * ‖η‖ ^ 2 := by positivity
          rw [show ((k + 1 : ℕ) : ℝ) * (-(π ^ 2 * σ) * (‖η‖ ^ 2 / (k + 2))) =
            -(π ^ 2 * σ * ‖η‖ ^ 2) * ((k + 1) / (k + 2)) by push_cast; ring]
          have hk : (1 : ℝ) / 2 ≤ (k + 1) / (k + 2) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
          nlinarith
      _ = 10 * π ^ 3 * R ^ 3 / s * (‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2)) := by
          rw [hnζ, div_pow]
          have : ((k + 1 : ℕ) + 1 : ℝ) = s ^ 2 := by rw [hs2]; push_cast; ring
          rw [this]
          field_simp
  · have hqa : ‖hatC h ζ‖ ≤ q := hq ζ hout.le
    have hb1 : ‖((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) ^ (k + 2)‖ ≤
        Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) * Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2) := by
      rw [← hb, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hQσ := hh.var η
      have hη2 : (k + 2) * r0 R σ ^ 2 ≤ ‖η‖ ^ 2 := by
        have : ‖η‖ = s * ‖ζ‖ := by rw [hnζ]; field_simp
        rw [this, mul_pow, hs2]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (r0_pos hR hσ).le hout.le 2)
          (by positivity)
      have a1 := mul_le_mul_of_nonneg_left hη2 (by positivity : (0 : ℝ) ≤ π ^ 2 * σ)
      have a2 := mul_le_mul_of_nonneg_left hQσ (by positivity : (0 : ℝ) ≤ π ^ 2)
      nlinarith
    have ha1 : ‖hatC h ζ ^ (k + 2)‖ ≤ q ^ k * ‖hatC h ζ‖ ^ 2 := by
      rw [norm_pow, pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hqa k) (by positivity)
    calc ‖hatC h ζ ^ (k + 2) - ((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) ^ (k + 2)‖
        ≤ ‖hatC h ζ ^ (k + 2)‖ + ‖((Real.exp (-2 * π ^ 2 * quadF h ζ) : ℝ) : ℂ) ^ (k + 2)‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith

end Pointwise2

section Integral

variable {M R σ : ℝ} {h : E → ℝ}

lemma integrable_char_smul {f : E → ℂ} (hf : Integrable f) (x : E) :
    Integrable (fun η => 𝐞 ⟪η, x⟫ • f η) := by
  have := (Real.fourierIntegral_convergent_iff (μ := volume) (-x)).2 hf
  simpa only [inner_neg_right, neg_neg] using this

lemma integrable_cube_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun η : E => ‖η‖ ^ 3 * Real.exp (-c * ‖η‖ ^ 2)) := by
  refine ((integrable_gauss (E := E) hc).add
    ((integrable_gauss (E := E) (b := c / 2) (by positivity)).const_mul (8 / c ^ 2))).mono'
    (by fun_prop) (Eventually.of_forall fun η => ?_)
  set t := ‖η‖
  have ht : 0 ≤ t := norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : t ^ 3 ≤ 1 + t ^ 4 := by
    rcases le_or_gt t 1 with h | h
    · have : t ^ 3 ≤ 1 := pow_le_one₀ ht h
      nlinarith [pow_nonneg ht 4]
    · have : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ h.le (by norm_num)
      linarith
  have h2 : t ^ 4 * Real.exp (-c * t ^ 2) ≤ 8 / c ^ 2 * Real.exp (-(c / 2) * t ^ 2) := by
    have := Real.pow_div_factorial_le_exp (x := c * t ^ 2 / 2) (by positivity) 2
    simp only [Nat.factorial] at this
    have e : Real.exp (-(c / 2) * t ^ 2) = Real.exp (-c * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have hE := Real.exp_pos (-c * t ^ 2)
    have : t ^ 4 ≤ 8 / c ^ 2 * Real.exp (c * t ^ 2 / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      norm_num at this
      nlinarith
    nlinarith
  calc t ^ 3 * Real.exp (-c * t ^ 2) ≤ (1 + t ^ 4) * Real.exp (-c * t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ Real.exp (-c * t ^ 2) + 8 / c ^ 2 * Real.exp (-(c / 2) * t ^ 2) := by
        rw [add_mul, one_mul]; linarith

lemma integrable_gaussQ (hh : InH M R σ h) (hσ : 0 < σ) :
    Integrable (fun η => Real.exp (-2 * π ^ 2 * quadF h η)) := by
  refine (integrable_gauss (E := E) (b := 2 * π ^ 2 * σ) (by positivity)).mono'
    (by have := continuous_quadF hh; fun_prop) (Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (hh.var η) (by positivity : (0 : ℝ) ≤ 2 * π ^ 2)
  nlinarith

/-- The scaled density as an inverse Fourier integral. -/
lemma scaled_repr (hh : InH M R σ h) (k : ℕ) (x : E) :
    (((Real.sqrt (k + 2)) ^ Module.finrank ℝ E *
        convPow h (k + 2) (Real.sqrt (k + 2) • x) : ℝ) : ℂ) =
      ∫ η, 𝐞 ⟪η, x⟫ • hatC h ((Real.sqrt (k + 2))⁻¹ • η) ^ (k + 2) := by
  set s := Real.sqrt (k + 2)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have := Measure.integral_comp_smul (μ := (volume : Measure E))
    (fun ξ => 𝐞 ⟪ξ, s • x⟫ • hatC h ξ ^ (k + 2)) s⁻¹
  have e : ∀ η : E, ⟪s⁻¹ • η, s • x⟫ = ⟪η, x⟫ := fun η => by
    rw [inner_smul_left, inner_smul_right]; simp [hs.ne']
  simp_rw [e] at this
  rw [this, ← convPow_eq_inv hh k, inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [Complex.real_smul]
  push_cast
  ring

end Integral

section Bound

variable {M R σ : ℝ} {h : E → ℝ}

variable (E) in
/-- The explicit error bound of the local limit theorem for `m = k + 2`. -/
def epsB (M R σ q : ℝ) (k : ℕ) : ℝ :=
  10 * π ^ 3 * R ^ 3 / Real.sqrt (k + 2) *
      (∫ η : E, ‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2)) +
    q ^ k * Real.sqrt (k + 2) ^ Module.finrank ℝ E * M +
    Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) * ∫ η : E, Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2)

/-- The quantitative local limit theorem: `|m^{d/2} h^{*m}(√m x) - φ_h(x)| ≤ epsB … k` for
`m = k + 2`, with `q` a bound for `|ĥ|` outside the ball of radius `r0 R σ`. -/
theorem llt_bound (hh : InH M R σ h) (hR : 0 < R) (hσ : 0 < σ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ ξ, r0 R σ ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) (k : ℕ) (x : E) :
    |Real.sqrt (k + 2) ^ Module.finrank ℝ E * convPow h (k + 2) (Real.sqrt (k + 2) • x) -
      gaussD h x| ≤ epsB E M R σ q k := by
  set s := Real.sqrt (k + 2)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set G : E → ℂ := fun η => ((Real.exp (-2 * π ^ 2 * quadF h η) : ℝ) : ℂ)
  have hGi : Integrable G := (integrable_gaussQ hh hσ).ofReal
  have hAi : Integrable (fun η => hatC h (s⁻¹ • η) ^ (k + 2)) :=
    (integrable_hatC_pow hh k).comp_smul (inv_ne_zero hs.ne')
  have hgd : gaussD h x = (∫ η, 𝐞 ⟪η, x⟫ • G η).re := by
    rw [gaussD, Real.fourierInv_eq]
  have hD : s ^ Module.finrank ℝ E * convPow h (k + 2) (s • x) - gaussD h x =
      (∫ η, 𝐞 ⟪η, x⟫ • (hatC h (s⁻¹ • η) ^ (k + 2) - G η)).re := by
    rw [hgd, ← Complex.ofReal_re (s ^ Module.finrank ℝ E * convPow h (k + 2) (s • x)),
      scaled_repr hh k x, ← Complex.sub_re, ← integral_sub (integrable_char_smul hAi x)
      (integrable_char_smul hGi x)]
    simp_rw [smul_sub]
  rw [hD]
  refine (Complex.abs_re_le_norm _).trans ((norm_integral_le_integral_norm _).trans ?_)
  simp_rw [Circle.norm_smul]
  -- the three integrable majorants
  have hT1 : Integrable fun η : E => 10 * π ^ 3 * R ^ 3 / s *
      (‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2)) :=
    (integrable_cube_gauss (by positivity)).const_mul _
  have hT2 : Integrable fun η : E => q ^ k * ‖hatC h (s⁻¹ • η)‖ ^ 2 :=
    ((hatC_sq hh).1.comp_smul (inv_ne_zero hs.ne')).const_mul _
  have hT3 : Integrable fun η : E => Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) *
      Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2) :=
    (integrable_gauss (E := E) (by positivity)).const_mul _
  calc ∫ η, ‖hatC h (s⁻¹ • η) ^ (k + 2) - G η‖
      ≤ ∫ η, (10 * π ^ 3 * R ^ 3 / s * (‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2)) +
          q ^ k * ‖hatC h (s⁻¹ • η)‖ ^ 2 +
          Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) *
            Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun η => norm_nonneg _)
          ((hT1.add hT2).add hT3) (Eventually.of_forall fun η => ?_)
        have := pt_bound hh hR hσ hq0 hq k η
        exact this
    _ = epsB E M R σ q k - q ^ k * (s ^ Module.finrank ℝ E * M) +
          q ^ k * (s ^ Module.finrank ℝ E * ∫ ξ, ‖hatC h ξ‖ ^ 2) := by
        have e1 := integral_add (hT1.add hT2) hT3
        have e2 := integral_add hT1 hT2
        simp only [Pi.add_apply] at e1 e2
        rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
        have := Measure.integral_comp_smul (μ := (volume : Measure E))
          (fun ξ => ‖hatC h ξ‖ ^ 2) s⁻¹
        rw [this, inv_pow, inv_inv, abs_of_pos (by positivity), smul_eq_mul, epsB]
        ring
    _ ≤ epsB E M R σ q k := by
        have := mul_le_mul_of_nonneg_left (hatC_sq hh).2
          (by positivity : (0 : ℝ) ≤ s ^ Module.finrank ℝ E)
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ q ^ k)
        linarith

end Bound

section Limit

lemma tendsto_epsB {M R σ q : ℝ} (hM : 0 ≤ M) (hσ : 0 < σ) (hR : 0 < R) (hq0 : 0 ≤ q)
    (hq1 : q < 1) : Tendsto (epsB E M R σ q) atTop (𝓝 0) := by
  have hk2 : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  -- first term
  have t1 : Tendsto (fun k : ℕ => 10 * π ^ 3 * R ^ 3 / Real.sqrt (k + 2) *
      (∫ η : E, ‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2))) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := 10 * π ^ 3 * R ^ 3)).div_atTop
      (Real.tendsto_sqrt_atTop.comp hk2)).mul_const
        (∫ η : E, ‖η‖ ^ 3 * Real.exp (-(π ^ 2 * σ / 2) * ‖η‖ ^ 2))
    rw [zero_mul] at this
    exact this
  -- third term
  have t3 : Tendsto (fun k : ℕ => Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2)) *
      ∫ η : E, Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2)) atTop (𝓝 0) := by
    have hc : 0 < π ^ 2 * σ * r0 R σ ^ 2 := by have := r0_pos hR hσ; positivity
    have : Tendsto (fun k : ℕ => Real.exp (-(π ^ 2 * σ * r0 R σ ^ 2) * (k + 2))) atTop
        (𝓝 0) := Real.tendsto_exp_atBot.comp
          (Tendsto.const_mul_atTop_of_neg (by linarith) hk2)
    have := this.mul_const (∫ η : E, Real.exp (-(π ^ 2 * σ) * ‖η‖ ^ 2))
    rw [zero_mul] at this
    exact this
  -- second term
  set q' := max q (1 / 2)
  have hq'0 : 0 < q' := lt_max_of_lt_right (by norm_num)
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  set d := Module.finrank ℝ E
  have t2' : Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ) ^ d * q' ^ (k + 2)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ) ^ d * q' ^ n) 2).2
      (tendsto_pow_const_mul_const_pow_of_lt_one d hq'0.le hq'1)
  have t2 : Tendsto (fun k : ℕ => q ^ k * Real.sqrt (k + 2) ^ d * M) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => by positivity) (fun k => ?_)
      (by have := t2'.const_mul ((q' ^ 2)⁻¹ * M); rwa [mul_zero] at this :
        Tendsto (fun k : ℕ => (q' ^ 2)⁻¹ * M * (((k + 2 : ℕ) : ℝ) ^ d * q' ^ (k + 2))) atTop
          (𝓝 0))
    have hs : Real.sqrt (k + 2) ≤ ((k + 2 : ℕ) : ℝ) := by
      push_cast
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have h1 : q ^ k ≤ q' ^ k := pow_le_pow_left₀ hq0 (le_max_left _ _) k
    have h2 : Real.sqrt (k + 2) ^ d ≤ ((k + 2 : ℕ) : ℝ) ^ d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hs d
    calc q ^ k * Real.sqrt (k + 2) ^ d * M ≤ q' ^ k * ((k + 2 : ℕ) : ℝ) ^ d * M := by gcongr
      _ = (q' ^ 2)⁻¹ * M * (((k + 2 : ℕ) : ℝ) ^ d * q' ^ (k + 2)) := by
          rw [pow_add]; field_simp
  have := (t1.add t2).add t3
  rw [add_zero, add_zero] at this
  exact this

end Limit

section Gauss

variable {M R σ : ℝ} {h : E → ℝ}

lemma gaussD_eq (h : E → ℝ) (x : E) :
    gaussD h x = (∫ η, 𝐞 ⟪η, x⟫ • ((Real.exp (-2 * π ^ 2 * quadF h η) : ℝ) : ℂ)).re := by
  rw [gaussD, Real.fourierInv_eq]

lemma gaussD_zero (h : E → ℝ) :
    gaussD h 0 = ∫ η, Real.exp (-2 * π ^ 2 * quadF h η) := by
  rw [gaussD_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- `φ_h(0) ≥ (2πR²)^{-d/2}`. -/
lemma gaussD_zero_ge (hh : InH M R σ h) (hR : 0 < R) (hσ : 0 < σ) :
    (1 / (2 * π * R ^ 2)) ^ ((Module.finrank ℝ E : ℝ) / 2) ≤ gaussD h 0 := by
  rw [gaussD_zero h]
  have e : (1 / (2 * π * R ^ 2)) = π / (2 * π ^ 2 * R ^ 2) := by
    field_simp
  rw [e, ← GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  refine integral_mono (integrable_gauss (by positivity)) (integrable_gaussQ hh hσ)
    fun η => Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (quadF_le hh η) (by positivity : (0 : ℝ) ≤ 2 * π ^ 2)
  nlinarith

/-- The Lipschitz constant of `φ_h` (uniform on the class). -/
def lipG (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (σ : ℝ) : ℝ :=
  2 * π * ∫ η : E, (1 + ‖η‖ ^ 3) * Real.exp (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2)

lemma gaussD_lip (hh : InH M R σ h) (hσ : 0 < σ) (x : E) :
    |gaussD h x - gaussD h 0| ≤ lipG E σ * ‖x‖ := by
  set G : E → ℂ := fun η => ((Real.exp (-2 * π ^ 2 * quadF h η) : ℝ) : ℂ)
  have hGi : Integrable G := (integrable_gaussQ hh hσ).ofReal
  rw [gaussD_eq, gaussD_eq, ← Complex.sub_re, ← integral_sub (integrable_char_smul hGi x)
    (integrable_char_smul hGi 0)]
  have hB : Integrable fun η : E => (1 + ‖η‖ ^ 3) * Real.exp (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2) := by
    have := (integrable_gauss (E := E) (b := 2 * π ^ 2 * σ) (by positivity)).add
      (integrable_cube_gauss (E := E) (c := 2 * π ^ 2 * σ) (by positivity))
    refine this.congr (Eventually.of_forall fun η => ?_)
    simp only [Pi.add_apply]; ring
  refine (Complex.abs_re_le_norm _).trans ((norm_integral_le_integral_norm _).trans ?_)
  calc ∫ η, ‖𝐞 ⟪η, x⟫ • G η - 𝐞 ⟪η, 0⟫ • G η‖
      ≤ ∫ η, 2 * π * ‖x‖ * ((1 + ‖η‖ ^ 3) * Real.exp (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun η => norm_nonneg _)
          (hB.const_mul _) (Eventually.of_forall fun η => ?_)
        simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, G]
        rw [Circle.smul_def, smul_eq_mul,
          show ∀ a b : ℂ, a * b - b = (a - 1) * b from fun a b => by ring, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.fourierChar_apply]
        have h1 : ‖Complex.exp (↑(2 * π * ⟪η, x⟫) * Complex.I) - 1‖ ≤ 2 * π * ‖η‖ * ‖x‖ := by
          rw [mul_comm _ Complex.I]
          refine norm_exp_I_mul_ofReal_sub_one_le.trans ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
          have := abs_real_inner_le_norm η x
          have := pi_pos
          nlinarith
        have h2 : Real.exp (-2 * π ^ 2 * quadF h η) ≤ Real.exp (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2) :=
          Real.exp_le_exp.2 (by
            have := mul_le_mul_of_nonneg_left (hh.var η) (by positivity : (0 : ℝ) ≤ 2 * π ^ 2)
            nlinarith)
        have h3 : ‖η‖ ≤ 1 + ‖η‖ ^ 3 := by
          rcases le_or_gt ‖η‖ 1 with h | h
          · nlinarith [pow_nonneg (norm_nonneg η) 3]
          · nlinarith [pow_le_pow_right₀ h.le (show 1 ≤ 3 by norm_num)]
        calc ‖Complex.exp (↑(2 * π * ⟪η, x⟫) * Complex.I) - 1‖ * Real.exp (-2 * π ^ 2 * quadF h η)
            ≤ (2 * π * ‖η‖ * ‖x‖) * Real.exp (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2) :=
              mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
          _ ≤ 2 * π * ‖x‖ * ((1 + ‖η‖ ^ 3) * Real.exp (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2)) := by
              have := Real.exp_pos (-(2 * π ^ 2 * σ) * ‖η‖ ^ 2)
              have : 0 ≤ 2 * π * ‖x‖ := by positivity
              nlinarith [mul_le_mul_of_nonneg_left h3 this]
    _ = lipG E σ * ‖x‖ := by rw [integral_const_mul, lipG]; ring

end Gauss

section Lemma103

variable {M R σ : ℝ} {𝓗 : Set (E → ℝ)}

/-- **Lemma 103** (`lg:lem:llt`), first statement, for an explicit class: let `𝓗` be a set of
densities in `InH M R σ` (bounded by `M`, vanishing outside the ball of radius `R`, mean `0`,
covariance at least `σ`) whose Fourier transforms are bounded away from `1` outside every ball,
uniformly on `𝓗`. Then `sup_{h ∈ 𝓗} sup_x |m^{d/2} h^{*m}(√m x) - φ_h(x)| → 0`. -/
theorem lemma103_eps (hR : 0 < R) (hσ : 0 < σ) (hH : ∀ h ∈ 𝓗, InH M R σ h)
    (hgap : ∀ r > 0, ∃ q < 1, ∀ h ∈ 𝓗, ∀ ξ : E, r ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m, N ≤ m → ∀ h ∈ 𝓗, ∀ x : E,
      |Real.sqrt m ^ Module.finrank ℝ E * convPow h m (Real.sqrt m • x) - gaussD h x| ≤ ε := by
  intro ε hε
  rcases 𝓗.eq_empty_or_nonempty with he | ⟨h₀, hh₀⟩
  · exact ⟨0, fun m _ h hh => by simp [he] at hh⟩
  have hM := (hH h₀ hh₀).M_nonneg
  obtain ⟨q, hq1, hq⟩ := hgap (r0 R σ) (r0_pos hR hσ)
  have T := tendsto_epsB (E := E) hM hσ hR (le_max_right q 0) (max_lt hq1 zero_lt_one)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((tendsto_order.1 T).2 ε hε)
  refine ⟨N0 + 2, fun m hm h hh x => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have := llt_bound (hH h hh) hR hσ (le_max_right q 0)
    (fun ξ hξ => (hq h hh ξ hξ).trans (le_max_left _ _)) k x
  push_cast
  exact this.trans (hN0 k (by omega)).le

/-- The approximation at the centre: `m^{d/2} h^{*m}(y)` is uniformly close to `φ_h(0)` for
`|y| ≤ ρ`. -/
theorem approx_center (hR : 0 < R) (hσ : 0 < σ) (hH : ∀ h ∈ 𝓗, InH M R σ h)
    (hgap : ∀ r > 0, ∃ q < 1, ∀ h ∈ 𝓗, ∀ ξ : E, r ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) (ρ : ℝ) :
    ∀ e > 0, ∃ N : ℕ, ∀ m, N ≤ m → ∀ h ∈ 𝓗, ∀ y : E, ‖y‖ ≤ ρ →
      |Real.sqrt m ^ Module.finrank ℝ E * convPow h m y - gaussD h 0| ≤ e := by
  intro e he
  obtain ⟨N1, hN1⟩ := lemma103_eps hR hσ hH hgap (e / 2) (by positivity)
  -- `lipG E σ * ρ / √m ≤ e / 2` eventually
  have hT : Tendsto (fun m : ℕ => lipG E σ * |ρ| / Real.sqrt m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 ((tendsto_order.1 hT).2 (e / 2) (by positivity))
  refine ⟨max (max N1 N2) 1, fun m hm h hh y hy => ?_⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm1)
  set x := (Real.sqrt m)⁻¹ • y
  have hyx : y = Real.sqrt m • x := by simp [x, smul_smul, hs.ne']
  have h1 := hN1 m (le_of_max_le_left (le_of_max_le_left hm)) h hh x
  rw [← hyx] at h1
  have h2 := gaussD_lip (hH h hh) hσ x
  have h3 : lipG E σ * ‖x‖ ≤ lipG E σ * |ρ| / Real.sqrt m := by
    have hL : 0 ≤ lipG E σ := by
      unfold lipG
      exact mul_nonneg (by positivity) (integral_nonneg fun η => by positivity)
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL
    simp only [x, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hy.trans (le_abs_self ρ)) hs.le
  have h4 := hN2 m (le_of_max_le_right (le_of_max_le_left hm))
  calc |Real.sqrt m ^ Module.finrank ℝ E * convPow h m y - gaussD h 0|
      ≤ |Real.sqrt m ^ Module.finrank ℝ E * convPow h m y - gaussD h x| +
        |gaussD h x - gaussD h 0| := abs_sub_le _ _ _
    _ ≤ e := by linarith

/-- The lower bound `(2πR²)^{-d/2}` of `φ_h(0)`. -/
def g0 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : ℝ) : ℝ := (1 / (2 * π * R ^ 2)) ^ ((Module.finrank ℝ E : ℝ) / 2)

/-- **Lemma 103** (`lg:lem:llt`), second statement: for every `ρ`,
`δ_m(ρ) = sup {|h^{*m}(y)/h^{*m}(y') - 1| : h ∈ 𝓗, |y|, |y'| ≤ ρ} → 0`; and `h^{*m} > 0` on the
ball of radius `ρ` for large `m`. -/
theorem lemma103_delta (hR : 0 < R) (hσ : 0 < σ) (hH : ∀ h ∈ 𝓗, InH M R σ h)
    (hgap : ∀ r > 0, ∃ q < 1, ∀ h ∈ 𝓗, ∀ ξ : E, r ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) (ρ : ℝ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m, N ≤ m → ∀ h ∈ 𝓗, ∀ y y' : E, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      0 < convPow h m y ∧ |convPow h m y / convPow h m y' - 1| ≤ ε := by
  intro ε hε
  have hg0 : 0 < g0 E R := by unfold g0; positivity
  set e := min (g0 E R / 2) (ε * g0 E R / 4)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := approx_center hR hσ hH hgap ρ e he
  refine ⟨max N 1, fun m hm h hh y y' hy hy' => ?_⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have hs : 0 < Real.sqrt m ^ Module.finrank ℝ E :=
    pow_pos (Real.sqrt_pos.2 (by exact_mod_cast hm1)) _
  have ha := hN m (le_of_max_le_left hm) h hh y hy
  have hb := hN m (le_of_max_le_left hm) h hh y' hy'
  have hφ := gaussD_zero_ge (hH h hh) hR hσ
  have he1 : e ≤ g0 E R / 2 := min_le_left _ _
  have he2 : e ≤ ε * g0 E R / 4 := min_le_right _ _
  set a := Real.sqrt m ^ Module.finrank ℝ E * convPow h m y
  set b := Real.sqrt m ^ Module.finrank ℝ E * convPow h m y'
  have hb0 : g0 E R / 2 ≤ b := by
    have := (abs_le.1 hb).1; unfold g0 at *; linarith
  have ha0 : g0 E R / 2 ≤ a := by
    have := (abs_le.1 ha).1; unfold g0 at *; linarith
  have hbpos : 0 < b := lt_of_lt_of_le (by positivity) hb0
  refine ⟨?_, ?_⟩
  · have : 0 < a := lt_of_lt_of_le (by positivity) ha0
    exact pos_of_mul_pos_right this hs.le
  · have hq : convPow h m y / convPow h m y' = a / b := by
      simp only [a, b]; rw [mul_div_mul_left _ _ hs.ne']
    rw [hq, div_sub_one hbpos.ne', abs_div, abs_of_pos hbpos, div_le_iff₀ hbpos]
    have hab : |a - b| ≤ 2 * e := by
      have := abs_sub_le a (gaussD h 0) b
      rw [abs_sub_comm (gaussD h 0) b] at this
      linarith
    calc |a - b| ≤ 2 * e := hab
      _ ≤ ε * (g0 E R / 2) := by linarith
      _ ≤ ε * b := mul_le_mul_of_nonneg_left hb0 hε.le

end Lemma103

section CondProd

variable {M R σ : ℝ} {g : E → ℝ}

lemma lintegral_fin_succ (k : ℕ) (F : (Fin (k + 1) → E) → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ x0 : E, ∫⁻ x' : Fin k → E, F (Fin.cons x0 x' : Fin (k + 1) → E) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => E) 0).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ => E) 0).symm p))
      (hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
  congr 1; funext x0; congr 1; funext x'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

/-- `∫_{E^k} ∏ g(x_i) g(y - ∑ x_i) dx = g^{*(k+1)}(y)`. -/
lemma lintegral_prod_eq_convPow (hh : InH M R σ g) (k : ℕ) (y : E) :
    ∫⁻ x : Fin k → E, ENNReal.ofReal (∏ i, g (x i)) * ENNReal.ofReal (g (y - ∑ i, x i)) =
      ENNReal.ofReal (convPow g (k + 1) y) := by
  induction k generalizing y with
  | zero =>
    rw [show (volume : Measure (Fin 0 → E)) = Measure.dirac (fun i => Fin.elim0 i) from
      Measure.pi_of_empty _ _, lintegral_dirac]
    simp [convPow]
  | succ k ih =>
    have hm : Measurable fun x : Fin (k + 1) → E =>
        ENNReal.ofReal (∏ i, g (x i)) * ENNReal.ofReal (g (y - ∑ i, x i)) := by
      refine (ENNReal.measurable_ofReal.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_)
      · exact Finset.measurable_prod _ fun i _ => hh.meas.comp (measurable_pi_apply i)
      · exact hh.meas.comp (measurable_const.sub (Finset.measurable_sum _
          fun i _ => measurable_pi_apply i))
    rw [lintegral_fin_succ k _ hm]
    have e : ∀ (x0 : E) (x' : Fin k → E),
        ENNReal.ofReal (∏ i, g ((Fin.cons x0 x' : Fin (k + 1) → E) i)) *
            ENNReal.ofReal (g (y - ∑ i, (Fin.cons x0 x' : Fin (k + 1) → E) i)) =
          ENNReal.ofReal (g x0) * (ENNReal.ofReal (∏ i, g (x' i)) *
            ENNReal.ofReal (g ((y - x0) - ∑ i, x' i))) := fun x0 x' => by
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [ENNReal.ofReal_mul (hh.nonneg x0), sub_sub, mul_assoc]
    simp_rw [e]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ih]
    have hi : Integrable fun t => g t * convPow g (k + 1) (y - t) :=
      hh.integrable.mul_bdd ((convPow_cont hh k).1.comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable (c := M)
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg ((convPow_props hh _).2.1 _)]
          exact (convPow_props hh _).2.2.1 _)
    simp_rw [← ENNReal.ofReal_mul (hh.nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t =>
      mul_nonneg (hh.nonneg t) ((convPow_props hh _).2.1 _))]
    rfl

end CondProd

lemma piCongrLeft_swap_apply (k : ℕ) (i : Fin (k + 1)) (x : Fin (k + 1) → E) (j : Fin (k + 1)) :
    MeasurableEquiv.piCongrLeft (fun _ => E) (Equiv.swap 0 i) x j = x (Equiv.swap 0 i j) := by
  simp only [MeasurableEquiv.piCongrLeft]
  change (Equiv.piCongrLeft (fun _ => E) (Equiv.swap 0 i)) x j = _
  rw [Equiv.piCongrLeft_apply, eqRec_eq_cast, cast_eq, Equiv.symm_swap]

section CondProd2

variable {M R σ : ℝ} {g : E → ℝ}

/-- The unnormalised weight `∏ g(x_i) · g(-∑ x_i)` on `E^{k+1}` (the free coordinates of a
tuple in `𝒯_{k+2}`). -/
def wt (g : E → ℝ) (k : ℕ) (x : Fin (k + 1) → E) : ENNReal :=
  ENNReal.ofReal (∏ i, g (x i)) * ENNReal.ofReal (g (-∑ i, x i))

/-- The tuple `(x_0, …, x_k, -∑ x_i)`. -/
def emb (k : ℕ) (x : Fin (k + 1) → E) : Fin (k + 2) → E := Fin.snoc x (-∑ i, x i)

/-- The conditioned product `β_g` (`n = k + 2` independent points with density `g` conditioned on
their sum being `0`), as a measure on `n`-tuples. -/
def condMeas (g : E → ℝ) (k : ℕ) : Measure (Fin (k + 2) → E) :=
  ((volume : Measure (Fin (k + 1) → E)).withDensity
    fun x => wt g k x / ENNReal.ofReal (convPow g (k + 2) 0)).map (emb k)

lemma measurable_wt (hh : InH M R σ g) (k : ℕ) : Measurable (wt g k) :=
  (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
    hh.meas.comp (measurable_pi_apply i))).mul (ENNReal.measurable_ofReal.comp
      (hh.meas.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg))

lemma measurable_emb (k : ℕ) : Measurable (emb (E := E) k) := by
  refine measurable_pi_iff.2 fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [emb, Fin.snoc_last]
    exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg
  · simp only [emb, Fin.snoc_castSucc]
    exact measurable_pi_apply i

lemma lintegral_wt (hh : InH M R σ g) (k : ℕ) :
    ∫⁻ x, wt g k x = ENNReal.ofReal (convPow g (k + 2) 0) := by
  have := lintegral_prod_eq_convPow hh (k + 1) 0
  simp only [zero_sub] at this
  exact this

lemma wt_swap (k : ℕ) (i : Fin (k + 1)) (x : Fin (k + 1) → E) :
    wt g k (MeasurableEquiv.piCongrLeft (fun _ => E) (Equiv.swap 0 i) x) = wt g k x := by
  simp only [wt, piCongrLeft_swap_apply]
  rw [Equiv.prod_comp (Equiv.swap 0 i) (fun j => g (x j)),
    Equiv.sum_comp (Equiv.swap 0 i) x]

/-- The common form of the marginals, after Fubini in the first coordinate. -/
lemma lintegral_marg0 (hh : InH M R σ g) (k : ℕ) {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator 1 (x 0) * wt g k x =
      ∫⁻ x' : Fin k → E, ENNReal.ofReal (∏ i, g (x' i)) *
        ∫⁻ z : E, A.indicator 1 z * ENNReal.ofReal (g z) *
          ENNReal.ofReal (g (-z - ∑ i, x' i)) := by
  have hm : Measurable fun x : Fin (k + 1) → E => A.indicator 1 (x 0) * wt g k x :=
    ((measurable_one.indicator hA).comp (measurable_pi_apply 0)).mul (measurable_wt hh k)
  rw [lintegral_fin_succ k _ hm, lintegral_lintegral_swap]
  · congr 1; funext x'
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext z
    simp only [wt, Fin.cons_zero, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_succ]
    rw [ENNReal.ofReal_mul (hh.nonneg z), neg_add, sub_eq_add_neg]
    ring
  · have hc : Measurable fun p : E × (Fin k → E) => (Fin.cons p.1 p.2 : Fin (k + 1) → E) := by
      have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) 0).symm.measurable
      convert this using 1
      funext p
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
    exact (((measurable_one.indicator hA).comp measurable_fst).mul
      ((measurable_wt hh k).comp hc)).aemeasurable

lemma lintegral_marg0_direct (hh : InH M R σ g) (k : ℕ) {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator 1 (x 0) * wt g k x =
      ∫⁻ z, A.indicator 1 z * ENNReal.ofReal (g z * convPow g (k + 1) (-z)) := by
  have hm : Measurable fun x : Fin (k + 1) → E => A.indicator 1 (x 0) * wt g k x :=
    ((measurable_one.indicator hA).comp (measurable_pi_apply 0)).mul (measurable_wt hh k)
  rw [lintegral_fin_succ k _ hm]
  congr 1; funext z
  have e : ∀ x' : Fin k → E, A.indicator 1 ((Fin.cons z x' : Fin (k + 1) → E) 0) *
      wt g k (Fin.cons z x') = A.indicator 1 z * ENNReal.ofReal (g z) *
        (ENNReal.ofReal (∏ i, g (x' i)) * ENNReal.ofReal (g (-z - ∑ i, x' i))) := fun x' => by
    simp only [wt, Fin.cons_zero, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_succ]
    rw [ENNReal.ofReal_mul (hh.nonneg z), neg_add, sub_eq_add_neg]
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by
      by_cases hz : z ∈ A <;> simp [hz]) ENNReal.ofReal_ne_top),
    lintegral_prod_eq_convPow hh k (-z), mul_assoc, ← ENNReal.ofReal_mul (hh.nonneg z)]

lemma lintegral_sub_left' (F : E → ENNReal) (c : E) : ∫⁻ x, F (c - x) = ∫⁻ x, F x :=
  lintegral_sub_left_eq_self F c

lemma lintegral_marg_last (hh : InH M R σ g) (k : ℕ) {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator 1 (-∑ i, x i) * wt g k x = ∫⁻ x, A.indicator 1 (x 0) * wt g k x := by
  rw [lintegral_marg0 hh k hA]
  have hm : Measurable fun x : Fin (k + 1) → E => A.indicator 1 (-∑ i, x i) * wt g k x :=
    ((measurable_one.indicator hA).comp
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg).mul (measurable_wt hh k)
  have hc : Measurable fun p : E × (Fin k → E) => (Fin.cons p.1 p.2 : Fin (k + 1) → E) := by
    have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) 0).symm.measurable
    convert this using 1
    funext p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
  rw [lintegral_fin_succ k _ hm, lintegral_lintegral_swap (by exact (hm.comp hc).aemeasurable)]
  congr 1; funext x'
  set s := ∑ i, x' i
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_sub_left' _ (-s)]
  congr 1; funext z
  simp only [wt, Fin.cons_zero, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_succ]
  rw [ENNReal.ofReal_mul (hh.nonneg _)]
  have e1 : -(-s - z + s) = z := by abel
  have e2 : -(-s - z + s) = z := by abel
  rw [e1, show -z - s = -s - z by abel]
  ring

lemma lintegral_marg_i (k : ℕ) (i : Fin (k + 1)) (A : Set E) :
    ∫⁻ x, A.indicator 1 (x i) * wt g k x = ∫⁻ x, A.indicator 1 (x 0) * wt g k x := by
  have hp := volume_measurePreserving_piCongrLeft (fun _ : Fin (k + 1) => E) (Equiv.swap 0 i)
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1; funext x
  rw [wt_swap, piCongrLeft_swap_apply, Equiv.swap_apply_right]

end CondProd2

section CondProd3

variable {M R σ : ℝ} {g : E → ℝ}

lemma setLIntegral_preimage_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → E)
    {A : Set E} (hS : MeasurableSet (φ ⁻¹' A)) (F : α → ENNReal) :
    ∫⁻ x in φ ⁻¹' A, F x ∂μ = ∫⁻ x, A.indicator 1 (φ x) * F x ∂μ := by
  rw [← lintegral_indicator hS]
  congr 1; funext x
  by_cases hx : φ x ∈ A
  · simp [hx]
  · simp [hx]

/-- The marginal formula (`lg:eq:marg`): every coordinate of `β_g` has the density
`p ↦ g(p) g^{*(n-1)}(-p) / g^{*n}(0)`. -/
lemma condMeas_marg (hh : InH M R σ g) (k : ℕ) (j : Fin (k + 2)) :
    (condMeas g k).map (fun x => x j) = volume.withDensity
      (fun p => ENNReal.ofReal (g p * convPow g (k + 1) (-p)) /
        ENNReal.ofReal (convPow g (k + 2) 0)) := by
  ext A hA
  set Z := ENNReal.ofReal (convPow g (k + 2) 0)
  have hS : MeasurableSet ((fun x : Fin (k + 1) → E => emb k x j) ⁻¹' A) :=
    ((measurable_pi_apply j).comp (measurable_emb k)) hA
  have hR : ∫⁻ a in A, ENNReal.ofReal (g a * convPow g (k + 1) (-a)) / Z =
      ∫⁻ a, A.indicator 1 a * (ENNReal.ofReal (g a * convPow g (k + 1) (-a)) / Z) :=
    setLIntegral_preimage_eq volume id hA _
  rw [Measure.map_apply (measurable_pi_apply j) hA, condMeas,
    Measure.map_apply (measurable_emb k) (measurable_pi_apply j hA),
    show emb k ⁻¹' ((fun f => f j) ⁻¹' A) = (fun x : Fin (k + 1) → E => emb k x j) ⁻¹' A from rfl,
    withDensity_apply _ hS, withDensity_apply _ hA, setLIntegral_preimage_eq _ _ hS, hR]
  simp only [div_eq_mul_inv, ← mul_assoc]
  rw [lintegral_mul_const _ ?_, lintegral_mul_const _ ?_]
  · congr 1
    rw [← lintegral_marg0_direct hh k hA]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [emb, Fin.snoc_last]
      exact lintegral_marg_last hh k hA
    · simp only [emb, Fin.snoc_castSucc]
      exact lintegral_marg_i k i A
  · exact (measurable_one.indicator hA).mul (ENNReal.measurable_ofReal.comp
      (hh.meas.mul ((convPow_cont hh k).1.comp measurable_neg)))
  · exact ((measurable_one.indicator hA).comp
      ((measurable_pi_apply j).comp (measurable_emb k))).mul (measurable_wt hh k)

/-- **The fixed-point step of Theorem 104** (with Lemma 101): if the marginal density
`g(p) g^{*(n-1)}(-p) / g^{*n}(0)` of the conditioned product `β_g` (`n = k + 2`) is the
exponential of an affine function on `K`, `g` vanishing outside `K`, then `β_g` is an `n`-complete
mix of `U(K)`. Here `K` is a bounded measurable set of positive volume with centroid `0`. -/
theorem completelyMixable_of_marg (hh : InH M R σ g) {K : Set E} (hKm : MeasurableSet K)
    {R' : ℝ} (hKb : ∀ p ∈ K, ‖p‖ ≤ R') (hpos : volume K ≠ 0) (hcen : ∫ p in K, p = 0)
    (hgK : ∀ p ∉ K, g p = 0) (k : ℕ) (hZ : 0 < convPow g (k + 2) 0) (a : ℝ) (b : E)
    (hmarg : ∀ p ∈ K, g p * convPow g (k + 1) (-p) / convPow g (k + 2) 0 =
      Real.exp (a + ⟪b, p⟫)) :
    CompletelyMixable (k + 2) (unifSet K) := by
  have hZ' : ENNReal.ofReal (convPow g (k + 2) 0) ≠ 0 := by simpa using hZ
  have hprob : IsProbabilityMeasure (condMeas g k) := by
    constructor
    rw [condMeas, Measure.map_apply (measurable_emb k) MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const _ (measurable_wt hh k), lintegral_wt hh k,
      ENNReal.mul_inv_cancel hZ' ENNReal.ofReal_ne_top]
  have hsum : ∀ᵐ x ∂(condMeas g k), ∑ j, x j = 0 := by
    rw [condMeas, ae_map_iff (measurable_emb k).aemeasurable
      (measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
        measurable_const)]
    refine Eventually.of_forall fun x => ?_
    simp [emb, Fin.sum_univ_castSucc]
  have hsupp : ∀ᵐ x ∂(condMeas g k), ∀ j, x j ∈ K := by
    rw [condMeas, ae_map_iff (measurable_emb k).aemeasurable
      (by
        have := MeasurableSet.univ_pi (fun _ : Fin (k + 2) => hKm)
        convert this using 1
        ext y; simp : MeasurableSet {y : Fin (k + 2) → E | ∀ j, y j ∈ K})]
    rw [ae_withDensity_iff ((measurable_wt hh k).div_const _)]
    refine Eventually.of_forall fun x hx j => ?_
    have hw : wt g k x ≠ 0 := fun h => hx (by simp [h])
    simp only [wt, ne_eq, mul_eq_zero, not_or, ENNReal.ofReal_eq_zero, not_le] at hw
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [emb, Fin.snoc_last]
      by_contra hc
      have := hgK _ hc
      linarith [hw.2]
    · simp only [emb, Fin.snoc_castSucc]
      by_contra hc
      have := Finset.prod_eq_zero (f := fun i => g (x i)) (Finset.mem_univ i) (hgK _ hc)
      linarith [hw.1]
  have hm : ∀ j, (condMeas g k).map (fun x => x j) =
      (volume.restrict K).withDensity fun p => ENNReal.ofReal (Real.exp (a + ⟪b, p⟫)) := by
    intro j
    rw [condMeas_marg hh k j, ← withDensity_indicator hKm]
    congr 1; funext p
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp, ← hmarg p hp, ENNReal.ofReal_div_of_pos hZ]
    · rw [Set.indicator_of_notMem hp, hgK p hp, zero_mul, ENNReal.ofReal_zero, ENNReal.zero_div]
  exact ⟨condMeas g k,
    (Large.lemma101 (by omega) hKm hKb hpos hcen a b (condMeas g k) hsum hsupp hm).2⟩

end CondProd3

section KeyEstimate

variable {M R σ : ℝ} {h : E → ℝ}

/-- `h^{*(k+3)}(y) - h^{*(k+3)}(y')
  = ∫ (h(y - z) - h(y' - z)) (h^{*(k+2)}(z) - h^{*(k+2)}(y)) dz`. -/
lemma convPow_sub_eq (hh : InH M R σ h) (k : ℕ) (y y' : E) :
    convPow h (k + 3) y - convPow h (k + 3) y' =
      ∫ z, (h (y - z) - h (y' - z)) * (convPow h (k + 2) z - convPow h (k + 2) y) := by
  set f := convPow h (k + 2)
  have hf := convPow_props hh (k + 2)
  have hfm : Measurable f := (convPow_cont hh k).2.measurable
  have hc : ∀ w, convPow h (k + 3) w = ∫ z, h (w - z) * f z := fun w => by
    rw [show k + 3 = (k + 1) + 2 by ring, convPow_add_two, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_sub_left_eq_self _ volume w]
    simp only [sub_sub_cancel]
    rfl
  have hi : ∀ w, Integrable fun z => h (w - z) * f z := fun w =>
    (hf.1.bdd_mul (c := M) (hh.meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hh.nonneg _)]; exact hh.le _))
  have hhi : ∀ w, Integrable fun z => h (w - z) := fun w =>
    (hh.integrable.comp_sub_left w)
  have h1 : ∀ w, ∫ z, h (w - z) = 1 := fun w => by
    rw [integral_sub_left_eq_self (fun z => h z) volume w, hh.int1]
  rw [hc, hc, ← integral_sub (hi y) (hi y')]
  have e : ∀ z, (h (y - z) - h (y' - z)) * (f z - f y) =
      (h (y - z) * f z - h (y' - z) * f z) - (h (y - z) - h (y' - z)) * f y := fun z => by ring
  simp_rw [e]
  have e1 := integral_sub ((hi y).sub (hi y')) (((hhi y).sub (hhi y')).mul_const (f y))
  have e2 := integral_sub (hhi y) (hhi y')
  simp only [Pi.sub_apply] at e1 e2
  rw [e1, integral_mul_const, e2, h1, h1, sub_self, zero_mul, sub_zero]

lemma abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  rw [abs_le]
  have hm : 0 < min a b := lt_min ha hb
  constructor
  · have := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at this
    have h2 : (b / a - 1) ≤ |a - b| / min a b := by
      rw [div_sub_one ha.ne', div_le_div_iff₀ ha hm]
      have : b - a ≤ |a - b| := by rw [abs_sub_comm]; exact le_abs_self _
      have h3 := min_le_left a b
      nlinarith [abs_nonneg (a - b)]
    linarith
  · have := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at this
    have h2 : (a / b - 1) ≤ |a - b| / min a b := by
      rw [div_sub_one hb.ne', div_le_div_iff₀ hb hm]
      have : a - b ≤ |a - b| := le_abs_self _
      have h3 := min_le_right a b
      nlinarith [abs_nonneg (a - b)]
    linarith

variable {𝓗 : Set (E → ℝ)}

/-- The ratio bound `h^{*(m-1)}(y) ≤ 3·2^d h^{*m}(y)` on a ball, for large `m`. -/
lemma ratio_bound (hR : 0 < R) (hσ : 0 < σ) (hH : ∀ h ∈ 𝓗, InH M R σ h)
    (hgap : ∀ r > 0, ∃ q < 1, ∀ h ∈ 𝓗, ∀ ξ : E, r ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) (ρ : ℝ) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ h ∈ 𝓗, ∀ y : E, ‖y‖ ≤ ρ →
      convPow h (k + 2) y ≤ 3 * 2 ^ Module.finrank ℝ E * convPow h (k + 3) y := by
  have hg0 : 0 < g0 E R := by unfold g0; positivity
  obtain ⟨N, hN⟩ := approx_center hR hσ hH hgap ρ (g0 E R / 2) (by positivity)
  refine ⟨N, fun k hk h hh y hy => ?_⟩
  set d := Module.finrank ℝ E
  have h1 := hN (k + 2) (by omega) h hh y hy
  have h2 := hN (k + 3) (by omega) h hh y hy
  have hφ := gaussD_zero_ge (hH h hh) hR hσ
  have hφ' : g0 E R ≤ gaussD h 0 := hφ
  set s1 := Real.sqrt ((k + 2 : ℕ) : ℝ)
  set s2 := Real.sqrt ((k + 3 : ℕ) : ℝ)
  have hs1 : 0 < s1 := Real.sqrt_pos.2 (by positivity)
  have hs2 : 0 < s2 := Real.sqrt_pos.2 (by positivity)
  have hss : s2 ≤ 2 * s1 := by
    rw [show (2 : ℝ) * s1 = Real.sqrt (4 * ((k + 2 : ℕ) : ℝ)) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hA : s1 ^ d * convPow h (k + 2) y ≤ 3 / 2 * gaussD h 0 := by
    have := (abs_le.1 h1).2; linarith
  have hB : 1 / 2 * gaussD h 0 ≤ s2 ^ d * convPow h (k + 3) y := by
    have := (abs_le.1 h2).1; linarith
  have hpos : 0 < gaussD h 0 := hg0.trans_le hφ'
  have hp1 : 0 < s1 ^ d := pow_pos hs1 d
  have hss' : s2 ^ d ≤ 2 ^ d * s1 ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs2.le hss d
  have hc3 : 0 ≤ convPow h (k + 3) y := (convPow_props (hH h hh) _).2.1 y
  -- `s1^d f ≤ 3/2 φ ≤ 3 s2^d a ≤ 3·2^d s1^d a`
  have : s1 ^ d * convPow h (k + 2) y ≤ s1 ^ d * (3 * 2 ^ d * convPow h (k + 3) y) := by
    calc s1 ^ d * convPow h (k + 2) y ≤ 3 / 2 * gaussD h 0 := hA
      _ ≤ 3 * (s2 ^ d * convPow h (k + 3) y) := by linarith
      _ ≤ 3 * (2 ^ d * s1 ^ d * convPow h (k + 3) y) := by gcongr
      _ = s1 ^ d * (3 * 2 ^ d * convPow h (k + 3) y) := by ring
  exact le_of_mul_le_mul_left this hp1

/-- **The Lipschitz estimate of Theorem 104** (`∇ log h^{*m} → 0`): for a class as in
Lemma 103 whose members have the `L¹` modulus of continuity
`∫ |h(y - z) - h(y' - z)| dz ≤ D |y - y'|`, the Lipschitz constant of `log h^{*m}` on the ball of
radius `ρ` tends to `0`, uniformly on the class. -/
theorem lip_log_convPow (hR : 0 < R) (hσ : 0 < σ) (hH : ∀ h ∈ 𝓗, InH M R σ h)
    (hgap : ∀ r > 0, ∃ q < 1, ∀ h ∈ 𝓗, ∀ ξ : E, r ≤ ‖ξ‖ → ‖hatC h ξ‖ ≤ q) {D : ℝ}
    (hD : ∀ h ∈ 𝓗, ∀ y y' : E, ∫ z, |h (y - z) - h (y' - z)| ≤ D * ‖y - y'‖) (ρ : ℝ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m, N ≤ m → ∀ h ∈ 𝓗, ∀ y y' : E, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      0 < convPow h m y ∧
        |Real.log (convPow h m y) - Real.log (convPow h m y')| ≤ ε * ‖y - y'‖ := by
  intro ε hε
  set d := Module.finrank ℝ E
  set D' := max D 0
  set C : ℝ := 3 * 2 ^ d
  have hC : 0 < C := by positivity
  set δ := min (1 / 2) (ε / (2 * (D' * C + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨N1, hN1⟩ := lemma103_delta hR hσ hH hgap (ρ + R) δ hδ
  obtain ⟨N2, hN2⟩ := lemma103_delta hR hσ hH hgap ρ (1 / 2) (by norm_num)
  obtain ⟨N3, hN3⟩ := ratio_bound hR hσ hH hgap ρ
  refine ⟨N1 + N2 + N3 + 3, fun m hm h hh y y' hy hy' => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hh' := hH h hh
  set f := convPow h (k + 2)
  set a := convPow h (k + 3) y
  set b := convPow h (k + 3) y'
  have hy2 : ‖y‖ ≤ ρ + R := by linarith
  obtain ⟨hb, hab⟩ := hN2 (k + 3) (by omega) h hh y' y hy' hy
  obtain ⟨ha, -⟩ := hN2 (k + 3) (by omega) h hh y y' hy hy'
  have hfy := (hN1 (k + 2) (by omega) h hh y y hy2 hy2).1
  have hratio : f y ≤ C * a := hN3 k (by omega) h hh y hy
  refine ⟨ha, ?_⟩
  -- `b ≥ a / 2`
  have hb2 : a / 2 ≤ b := by
    have := (abs_le.1 hab).1
    have h3 : 1 / 2 ≤ b / a := by linarith
    rw [le_div_iff₀ ha] at h3
    linarith
  -- the difference
  have hdiff : |a - b| ≤ δ * f y * (D' * ‖y - y'‖) := by
    rw [show a - b = _ from convPow_sub_eq hh' k y y']
    have hint : Integrable fun z => |h (y - z) - h (y' - z)| :=
      ((hh'.integrable.comp_sub_left y).sub (hh'.integrable.comp_sub_left y')).abs
    calc |∫ z, (h (y - z) - h (y' - z)) * (f z - f y)|
        ≤ ∫ z, |(h (y - z) - h (y' - z)) * (f z - f y)| := abs_integral_le_integral_abs
      _ ≤ ∫ z, |h (y - z) - h (y' - z)| * (δ * f y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
            (hint.mul_const _) (Eventually.of_forall fun z => ?_)
          simp only
          rw [abs_mul]
          by_cases h0 : h (y - z) = 0 ∧ h (y' - z) = 0
          · rw [h0.1, h0.2, sub_zero, abs_zero, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            have hz : ‖z‖ ≤ ρ + R := by
              rcases not_and_or.1 h0 with h1 | h1
              · have := hh'.norm_le h1
                have := norm_sub_norm_le z (z - y)
                rw [show z - (z - y) = y by abel, norm_sub_rev] at this
                linarith [norm_sub_rev y z]
              · have := hh'.norm_le h1
                have := norm_sub_norm_le z (z - y')
                rw [show z - (z - y') = y' by abel, norm_sub_rev] at this
                linarith [norm_sub_rev y' z]
            have := (hN1 (k + 2) (by omega) h hh z y hz hy2).2
            rw [div_sub_one hfy.ne', abs_div, abs_of_pos hfy, div_le_iff₀ hfy] at this
            linarith
      _ = δ * f y * ∫ z, |h (y - z) - h (y' - z)| := by rw [integral_mul_const]; ring
      _ ≤ δ * f y * (D' * ‖y - y'‖) := by
          refine mul_le_mul_of_nonneg_left ((hD h hh y y').trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hmin : a / 2 ≤ min a b := le_min (by linarith) hb2
  have hδ2 : δ ≤ ε / (2 * (D' * C + 1)) := min_le_right _ _
  have hD' : 0 ≤ D' := le_max_right _ _
  calc |Real.log a - Real.log b| ≤ |a - b| / min a b := abs_log_sub_log_le ha hb
    _ ≤ (δ * f y * (D' * ‖y - y'‖)) / (a / 2) :=
        div_le_div₀ (by positivity) hdiff (by positivity) hmin
    _ ≤ (δ * (C * a) * (D' * ‖y - y'‖)) / (a / 2) := by gcongr
    _ = 2 * δ * (D' * C) * ‖y - y'‖ := by
        have ha0 : a ≠ 0 := ha.ne'
        field_simp
    _ ≤ ε * ‖y - y'‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [le_div_iff₀ (by positivity)] at hδ2
        nlinarith

end KeyEstimate

section Convex

open scoped Pointwise

/-- For a convex `K` containing the closed ball of radius `ρ` about `0`,
`|{x ∈ K : x - t ∉ K}| ≤ d |t| |K| / ρ` (replacing the surface-area bound of the paper). -/
lemma vol_diff_translate {K : Set E} (hKm : MeasurableSet K) (hK : Convex ℝ K) {ρ : ℝ}
    (hρ : 0 < ρ) (hball : Metric.closedBall (0 : E) ρ ⊆ K) (hfin : volume K ≠ ⊤)
    (hd : 1 ≤ Module.finrank ℝ E) (t : E) :
    volume.real {x | x ∈ K ∧ x - t ∉ K} ≤ Module.finrank ℝ E * ‖t‖ / ρ * volume.real K := by
  set d := Module.finrank ℝ E
  have hsub : {x | x ∈ K ∧ x - t ∉ K} ⊆ K := fun x hx => hx.1
  rcases le_or_gt ρ ‖t‖ with ht | ht
  · refine (measureReal_mono hsub hfin).trans ?_
    refine le_mul_of_one_le_left measureReal_nonneg ?_
    rw [le_div_iff₀ hρ, one_mul]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [norm_nonneg t]
  set s := ‖t‖ / ρ
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s < 1 := by rw [div_lt_one hρ]; exact ht
  have h0K : (0 : E) ∈ K := hball (Metric.mem_closedBall_self hρ.le)
  set S := (1 - s) • K
  have hSK : S ⊆ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact hK.smul_mem_of_zero_mem h0K hk
      (show (1 - s) ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  have hSt : ∀ x ∈ S, x - t ∈ K := by
    rintro _ ⟨k, hk, rfl⟩
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · have ht0 : t = 0 := by
        rw [← norm_eq_zero]
        have h1 : ‖t‖ / ρ = 0 := h0.symm
        rcases div_eq_zero_iff.1 h1 with h | h
        · exact h
        · exact absurd h hρ.ne'
      simp [← h0, ht0, hk]
    · have hb : -(s⁻¹ • t) ∈ K := hball (by
        rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hpos]
        have htpos : 0 < ‖t‖ := by
          rcases (norm_nonneg t).lt_or_eq with h | h
          · exact h
          · simp [s, ← h] at hpos
        simp only [s]
        rw [inv_div]
        exact le_of_eq (by field_simp))
      have := hK hk hb (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
      convert this using 1
      rw [smul_neg, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, sub_eq_add_neg]
  have hdiff : {x | x ∈ K ∧ x - t ∉ K} ⊆ K \ S := fun x hx =>
    ⟨hx.1, fun hS => hx.2 (hSt x hS)⟩
  have hSm : MeasurableSet S := hKm.const_smul₀ _
  have hvS : volume S = ENNReal.ofReal ((1 - s) ^ d) * volume K := by
    rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg (by linarith) _)]
  refine (measureReal_mono hdiff (measure_ne_top_of_subset Set.sdiff_subset hfin)).trans ?_
  have hvS' : volume.real S = (1 - s) ^ d * volume.real K := by
    rw [Measure.real, hvS, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith) _),
      ← Measure.real]
  rw [measureReal_sdiff hSK hSm hfin, hvS']
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -s by linarith) d
  have : volume.real K - (1 - s) ^ d * volume.real K = (1 - (1 - s) ^ d) * volume.real K := by
    ring
  rw [this]
  refine mul_le_mul_of_nonneg_right ?_ measureReal_nonneg
  simp only [s] at hb ⊢
  rw [← sub_eq_add_neg] at hb
  have : (d : ℝ) * ‖t‖ / ρ = d * (‖t‖ / ρ) := by ring
  rw [this]
  linarith

end Convex

section Modulus

/-- `L¹` modulus of continuity for a function `h` that equals a bounded Lipschitz function `g`
on a convex body `K ⊇ B(0, ρ)` and vanishes outside `K`:
`∫ |h (y - z) - h (y' - z)| dz ≤ (L |K| + 2 G d |K| / ρ) ‖y - y'‖`. -/
theorem l1_modulus {K : Set E} (hKm : MeasurableSet K) (hK : Convex ℝ K) {ρ : ℝ}
    (hρ : 0 < ρ) (hball : Metric.closedBall (0 : E) ρ ⊆ K) (hfin : volume K ≠ ⊤)
    (hd : 1 ≤ Module.finrank ℝ E) {h : E → ℝ} {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hhK : ∀ x, x ∉ K → h x = 0) (hgG : ∀ x ∈ K, |h x| ≤ G)
    (hgL : ∀ x ∈ K, ∀ x' ∈ K, |h x - h x'| ≤ L * ‖x - x'‖) (y y' : E) :
    ∫ z, |h (y - z) - h (y' - z)| ≤
      (L * volume.real K + 2 * G * Module.finrank ℝ E * volume.real K / ρ) * ‖y - y'‖ := by
  set d := Module.finrank ℝ E
  set t := y - y'
  set A : Set E := {x | x ∈ K ∧ x - t ∉ K}
  set A' : Set E := {x | x ∈ K ∧ x - -t ∉ K}
  have hAm : MeasurableSet A := hKm.inter ((measurable_id.sub_const t) hKm).compl
  have hA'm : MeasurableSet A' := hKm.inter ((measurable_id.sub_const (-t)) hKm).compl
  have hAf : volume A ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono fun x hx => hx.1)
  have hA'f : volume A' ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono fun x hx => hx.1)
  have hshift : ∫ z, |h (y - z) - h (y' - z)| = ∫ w, |h w - h (w - t)| := by
    have := integral_sub_left_eq_self (fun w => |h w - h (w - t)|) volume y
    rw [← this]
    congr 1; ext z; congr 3; simp [t]
  rw [hshift]
  set F : E → ℝ := fun w => L * ‖t‖ * K.indicator 1 w + G * A.indicator 1 w +
    G * A'.indicator 1 (w - t)
  have iK : Integrable (K.indicator (1 : E → ℝ)) :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hfin)
  have iA : Integrable (A.indicator (1 : E → ℝ)) :=
    (integrable_indicator_iff hAm).2 (integrableOn_const hAf)
  have iA' : Integrable (A'.indicator (1 : E → ℝ)) :=
    (integrable_indicator_iff hA'm).2 (integrableOn_const hA'f)
  have iA't : Integrable (fun w => A'.indicator (1 : E → ℝ) (w - t)) := iA'.comp_sub_right t
  have hpt : ∀ w, |h w - h (w - t)| ≤ F w := by
    intro w
    simp only [F, Set.indicator, Pi.one_apply]
    by_cases hw : w ∈ K <;> by_cases hwt : w - t ∈ K
    · have := hgL w hw (w - t) hwt
      simp only [sub_sub_cancel] at this
      have h1 : w ∉ A := fun hA => hA.2 hwt
      have h2 : w - t ∉ A' := fun hA => hA.2 (by simpa using hw)
      simp [hw, h1, h2]; linarith
    · have h1 : w ∈ A := ⟨hw, hwt⟩
      have h2 : w - t ∉ A' := fun hA => hwt hA.1
      rw [hhK _ hwt, sub_zero]
      simp [hw, h1, h2]
      linarith [hgG w hw, mul_nonneg hL (norm_nonneg t)]
    · have h1 : w ∉ A := fun hA => hw hA.1
      have h2 : w - t ∈ A' := ⟨hwt, by simpa using hw⟩
      rw [hhK _ hw, zero_sub, abs_neg]
      simp [hw, h1, h2]; linarith [hgG _ hwt, mul_nonneg hL (norm_nonneg t)]
    · have h1 : w ∉ A := fun hA => hw hA.1
      have h2 : w - t ∉ A' := fun hA => hwt hA.1
      rw [hhK _ hw, hhK _ hwt]
      simp [hw, h1, h2]
  have iF : Integrable F := ((iK.const_mul _).add (iA.const_mul _)).add (iA't.const_mul _)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) iF
    (Eventually.of_forall hpt)).trans ?_
  have hIF : ∫ w, F w = L * ‖t‖ * volume.real K + G * volume.real A + G * volume.real A' := by
    have e1 := integral_add ((iK.const_mul (L * ‖t‖)).add (iA.const_mul G))
      (iA't.const_mul G)
    have e2 := integral_add (iK.const_mul (L * ‖t‖)) (iA.const_mul G)
    simp only [Pi.add_apply] at e1 e2
    simp only [F]
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self (fun w => A'.indicator (1 : E → ℝ) w) t,
      integral_indicator_one hKm, integral_indicator_one hAm, integral_indicator_one hA'm]
  rw [hIF]
  have b1 := vol_diff_translate hKm hK hρ hball hfin hd t
  have b2 := vol_diff_translate hKm hK hρ hball hfin hd (-t)
  rw [norm_neg] at b2
  have hK0 : 0 ≤ volume.real K := measureReal_nonneg
  have e : (L * volume.real K + 2 * G * d * volume.real K / ρ) * ‖t‖ =
      L * ‖t‖ * volume.real K + G * (d * ‖t‖ / ρ * volume.real K) +
        G * (d * ‖t‖ / ρ * volume.real K) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left b1 hG
  have := mul_le_mul_of_nonneg_left b2 hG
  linarith

end Modulus

end Mixes.LLT
