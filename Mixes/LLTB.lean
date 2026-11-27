import Mixes.LLT
import Mixes.Thm113

/-!
# Theorem 104 (`lg:thm:large`) and the hypothesis-free form of Corollary 105

* `thm104T`: `Large.Thm104T E` (Theorem 104 with its constants tracked, uniformly over a class
  of bodies) for any additive Haar `volume`, from Schauder's fixed point theorem `SchauderFPT`
  (not in Mathlib; the only hypothesis). Arzelà–Ascoli is Mathlib's.
* `fourierGapJohn`: `Large.FourierGapJohn E`, proved without hypotheses (the ball component of
  `U(K)`, as in Lemma 112; no Blaschke selection, no divergence theorem).
* `cor105_full`: Corollary 105 from `JohnThm` and `SchauderFPT` only.

Proof of Theorem 104 (`thm104_centred`, `cm_of_body`): `𝒞 = {ψ ∈ C(K) : |ψ| ≤ 1, Lip ψ ≤ 1}`
(compact by Arzelà–Ascoli), `h_ψ` the tilt of mean `0` of `e^ψ u` (Lemma 102 with `A = 2`), and
`Ψψ(p) = log h_ψ^{*m}(0) - log h_ψ^{*m}(-p)`. Differences from the paper: the projection `P`
onto affine functions is replaced by subtracting the value at `0` (the tilt absorbs the affine
part, so a fixed point still gives an affine exponent); continuity of `Ψ` is proved
quantitatively (`tv_lip`: the tilt vector is Lipschitz in `ψ` by strong monotonicity of the
tilt mean; `Hd_diff`, `convPow_diff`), so `Ψ` is Lipschitz on `𝒞`; the surface-area bound is
replaced by `LLT.l1_modulus`. The core works with the canonical volume and is transferred to
any Haar measure (`unifSet_eq_can`, `measureReal_eq_can`) and to bodies not centred at `0`
(translation by the centroid).
-/

open MeasureTheory Real RealInnerProductSpace Filter Topology
open scoped BoundedContinuousFunction

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.LLTB

universe u

/-- **Schauder's fixed point theorem** (not in Mathlib; an explicit hypothesis): a continuous
self-map of a nonempty compact convex subset of a real normed space has a fixed point. -/
def SchauderFPT : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] (C : Set X) (f : X → X),
    IsCompact C → Convex ℝ C → C.Nonempty → ContinuousOn f C → Set.MapsTo f C C →
      ∃ x ∈ C, f x = x


section HaarTransfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The canonical volume of the inner product space `E` (for the measurable structure of the
given `MeasureSpace`). -/
abbrev canV (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Measure E :=
  @volume E measureSpaceOfInnerProductSpace

/-- Any additive Haar `volume` is a positive finite multiple of the canonical volume. -/
lemma volume_eq_smul_can : ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
    (volume : Measure E) = c • canV E := by
  obtain ⟨s, hs⟩ : ∃ s : NNReal, (volume : Measure E) = s • canV E :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (volume : Measure E) (canV E)⟩
  refine ⟨(s : ENNReal), ?_, ENNReal.coe_ne_top, by rw [hs, ENNReal.smul_def]⟩
  intro h0
  rw [ENNReal.coe_eq_zero] at h0
  have hpos := isOpen_univ.measure_pos (volume : Measure E) Set.univ_nonempty
  rw [hs, h0, zero_smul] at hpos
  exact (lt_irrefl _ hpos)

lemma unifSet_eq_can (K : Set E) : unifSet K = @unifSet E measureSpaceOfInnerProductSpace K := by
  obtain ⟨c, hc0, hct, hc⟩ := volume_eq_smul_can (E := E)
  show (volume K)⁻¹ • (volume : Measure E).restrict K = (canV E K)⁻¹ • (canV E).restrict K
  rw [hc, Measure.restrict_smul, smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm _ c, ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 hct, one_mul]

lemma measureReal_eq_can :
    ∃ c : ℝ, 0 < c ∧ ∀ K : Set E, volume.real K = c * (canV E).real K := by
  obtain ⟨c, hc0, hct, hc⟩ := volume_eq_smul_can (E := E)
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, fun K => ?_⟩
  rw [measureReal_def, measureReal_def, hc, smul_apply, smul_eq_mul, ENNReal.toReal_mul]

end HaarTransfer

section GapCan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The characteristic function of `U(K)` (canonical volume) as the Fourier transform `ft` of
Lemma 112 of the density `1_K / |K|`, at `-(2π)⁻¹ ξ`. -/
lemma charFun_unifSet_eq_ft {K : Set E} (hKm : MeasurableSet K) (ξ : E) :
    charFun (unifSet K) ξ =
      Thm113.ft (K.indicator fun _ => (volume.real K)⁻¹) (-(2 * π)⁻¹ • ξ) := by
  rw [charFun_apply, unifSet, integral_smul_measure, ENNReal.toReal_inv, Thm113.ft]
  have hpi : (2 * π) ≠ 0 := by positivity
  have hfun : (fun y => (((K.indicator fun _ => (volume.real K)⁻¹) y : ℝ) : ℂ) *
      Thm113.ex y (-(2 * π)⁻¹ • ξ)) = K.indicator fun y =>
        (((volume.real K)⁻¹ : ℝ) : ℂ) * Complex.exp (⟪y, ξ⟫ * Complex.I) := by
    funext y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Thm113.ex, inner_smul_right]
      congr 2
      push_cast
      field_simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp
  rw [hfun, integral_indicator hKm, integral_const_mul, Complex.real_smul]
  rfl

/-- `FourierGapJohn` for the canonical volume. -/
lemma fourierGapJohn_can : ∀ r > 0, ∃ q < 1, ∀ K : Set E, IsCompact K → Convex ℝ K →
    Metric.closedBall (0 : E) 1 ⊆ K → K ⊆ Metric.closedBall 0 (Module.finrank ℝ E) →
    ∀ ξ : E, r ≤ ‖ξ‖ → ‖charFun (unifSet K) ξ‖ ≤ q := by
  intro r hr
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hd | hd
  · have : Subsingleton E := Module.finrank_zero_iff.1 hd
    refine ⟨0, zero_lt_one, fun K _ _ _ _ ξ hξ => ?_⟩
    rw [Subsingleton.elim ξ 0, norm_zero] at hξ
    linarith
  set d : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ)
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  set R : ℝ := 2 * d
  have hR : 0 < R := by positivity
  set r₀ : ℝ := r / (2 * π)
  have hr₀ : 0 < r₀ := by positivity
  obtain ⟨qB, hqB, hgap⟩ := Thm113.ballInt_gap (E := E) one_pos hr₀
  set α := Thm113.alph E 0 1 R
  have hV1 := Thm113.vB_pos (E := E) one_pos
  have hVR := Thm113.vB_pos (E := E) hR
  have hα : 0 < α := by unfold α Thm113.alph; positivity
  refine ⟨1 - α + α * qB, by nlinarith, fun K hKc hKconv hB hD ξ hξ => ?_⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hvK : 0 < volume.real K := ENNReal.toReal_pos
    ((Metric.measure_closedBall_pos volume (0 : E) one_pos).trans_le (measure_mono hB)).ne'
    hKc.measure_lt_top.ne
  set h : E → ℝ := K.indicator fun _ => (volume.real K)⁻¹
  have hH : Thm113.InH 0 1 R K h := by
    refine ⟨hKc, hKconv, ⟨0, hB⟩, fun x hx y hy => ?_, ?_, fun y hy => ?_, ?_,
      fun y hy => ?_, fun y hy => ?_⟩
    · have h1 := hD hx; have h2 := hD hy
      rw [Metric.mem_closedBall, dist_zero_right] at h1 h2
      calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ R := by simp only [R]; linarith
    · exact measurable_const.indicator hKm
    · simp [h, Set.indicator_of_notMem hy]
    · rw [integral_indicator hKm, setIntegral_const, smul_eq_mul, mul_inv_cancel₀ hvK.ne']
    · simp [h, Set.indicator_of_mem hy, mul_inv_cancel₀ hvK.ne']
    · simp [h, Set.indicator_of_mem hy, mul_inv_cancel₀ hvK.ne']
  set ξ' : E := -(2 * π)⁻¹ • ξ
  have hξ' : r₀ ≤ ‖ξ'‖ := by
    simp only [ξ', r₀, norm_smul, norm_neg, norm_inv, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * π by positivity)]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hξ (by positivity)
  rw [charFun_unifSet_eq_ft hKm ξ]
  refine (hH.norm_ft_le one_pos ξ').trans ?_
  have : ‖Thm113.ballInt E 1 ξ'‖ / Thm113.vB E 1 ≤ qB := by
    rw [div_le_iff₀ hV1]; exact hgap ξ' hξ'
  nlinarith

end GapCan

section GapHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **The Fourier step of Corollary 105** (`Large.FourierGapJohn`), proved: on the convex bodies
`B ⊆ K ⊆ d B`, `sup_{|ξ| ≥ r} |û_K(ξ)|` is bounded away from `1` uniformly, for every
`r > 0`.
No selection theorem is needed: `U(K)` has the component `U(B)` with weight `|B|/|K| ≥ d^{-d}`,
and `|û_B|` is bounded away from `1` outside every ball (Riemann–Lebesgue and compactness). -/
theorem fourierGapJohn : Large.FourierGapJohn E := by
  intro r hr
  obtain ⟨q, hq, H⟩ := fourierGapJohn_can (E := E) r hr
  exact ⟨q, hq, fun K hKc hKconv hB hD ξ hξ => by
    rw [unifSet_eq_can]; exact H K hKc hKconv hB hD ξ hξ⟩

end GapHaar

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma intOn_bdd {K : Set E} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤) {F : Type*}
    [NormedAddCommGroup F] {f : E → F} (hf : AEStronglyMeasurable f (volume.restrict K))
    {C : ℝ} (hb : ∀ y ∈ K, ‖f y‖ ≤ C) : IntegrableOn f K := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hfin
  refine Integrable.mono' (integrable_const C) hf ?_
  filter_upwards [ae_restrict_mem hKm] with y hy using hb y hy

/-- A centred convex body with the parameters of Theorem 104. -/
structure Body (v₀ v₁ R ρ σ : ℝ) (K : Set E) : Prop where
  compact : IsCompact K
  convex : Convex ℝ K
  vlo : v₀ ≤ volume.real K
  vhi : volume.real K ≤ v₁
  bdd : ∀ y ∈ K, ‖y‖ ≤ R
  ball : Metric.closedBall (0 : E) ρ ⊆ K
  cen : ∫ y in K, y = 0
  var : ∀ e : E, ‖e‖ = 1 → σ ≤ ∫ y, ⟪e, y⟫ ^ 2 ∂(unifSet K)

variable {v₀ v₁ R ρ σ : ℝ} {K : Set E}

lemma Body.meas (hB : Body v₀ v₁ R ρ σ K) : MeasurableSet K := hB.compact.isClosed.measurableSet

lemma Body.fin (hB : Body v₀ v₁ R ρ σ K) : volume K ≠ ⊤ := hB.compact.measure_lt_top.ne

lemma Body.vpos (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) : 0 < volume.real K :=
  hv₀.trans_le hB.vlo

lemma Body.mem0 (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) : (0 : E) ∈ K :=
  hB.ball (Metric.mem_closedBall_self hρ.le)

lemma Body.R_nonneg (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) : 0 ≤ R := by
  simpa using hB.bdd 0 (hB.mem0 hρ)

lemma Body.ne0 (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) : volume K ≠ 0 := by
  intro h; have := hB.vpos hv₀; rw [measureReal_def, h] at this; simp at this

/-- The set `𝒞` of the proof: functions on `K` bounded by `1` and `1`-Lipschitz. -/
def Cset (K : Set E) : Set (K →ᵇ ℝ) :=
  {ψ | (∀ p, |ψ p| ≤ 1) ∧ ∀ p q, |ψ p - ψ q| ≤ dist p q}

open Classical in
/-- `e^ψ` on `K`, extended by `0`. -/
def gE (K : Set E) (ψ : K →ᵇ ℝ) (y : E) : ℝ := if hy : y ∈ K then exp (ψ ⟨y, hy⟩) else 0

lemma gE_of_mem {ψ : K →ᵇ ℝ} {y : E} (hy : y ∈ K) : gE K ψ y = exp (ψ ⟨y, hy⟩) := by simp [gE, hy]

lemma gE_of_not_mem {ψ : K →ᵇ ℝ} {y : E} (hy : y ∉ K) : gE K ψ y = 0 := by simp [gE, hy]

lemma measurable_gE (hKm : MeasurableSet K) (ψ : K →ᵇ ℝ) : Measurable (gE K ψ) := by
  classical
  unfold gE
  exact Measurable.dite (continuous_exp.comp ψ.continuous).measurable measurable_const hKm

lemma gE_nonneg (ψ : K →ᵇ ℝ) (y : E) : 0 ≤ gE K ψ y := by
  by_cases hy : y ∈ K
  · rw [gE_of_mem hy]; exact (exp_pos _).le
  · rw [gE_of_not_mem hy]

lemma gE_bounds {ψ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K) {y : E} (hy : y ∈ K) :
    exp (-1) ≤ gE K ψ y ∧ gE K ψ y ≤ exp 1 := by
  rw [gE_of_mem hy]
  have := abs_le.1 (hψ.1 ⟨y, hy⟩)
  exact ⟨exp_le_exp.2 this.1, exp_le_exp.2 this.2⟩

lemma tiltDens_const_mul (K : Set E) (g : E → ℝ) {c : ℝ} (hc : c ≠ 0) (v y : E) :
    Large.tiltDens K (fun z => c * g z) v y = Large.tiltDens K g v y := by
  unfold Large.tiltDens
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_div_mul_left _ _ hc]

/-- The tilt vector `v_ψ`: the `v` for which the tilt of `e^ψ u` by `v` has mean `0`. -/
def tv (K : Set E) (ψ : K →ᵇ ℝ) : E :=
  Classical.epsilon fun v => ∫ y in K, Large.tiltDens K (gE K ψ) v y • y = 0

/-- The density `h_ψ` of the proof: the tilt of `e^ψ u` of mean `0`. -/
def Hd (K : Set E) (ψ : K →ᵇ ℝ) : E → ℝ := Large.tiltDens K (gE K ψ) (tv K ψ)

variable (E) in
/-- `|B_{ρ/4}|`. -/
def vBq (ρ : ℝ) : ℝ := (volume (Metric.ball (0 : E) (ρ / 4))).toReal

variable (E) in
/-- The bound `V` of Lemma 102 with `A = 2`, uniform over `|K| ≤ v₁`. -/
def V0 (v₁ ρ : ℝ) : ℝ := 2 * (2 + log (v₁ / vBq E ρ)) / ρ

variable (E) in
/-- The constant `A'` of the proof: `e^{-A'} u ≤ h_ψ ≤ e^{A'} u`. -/
def A1 (v₁ R ρ : ℝ) : ℝ := 2 + 2 * V0 E v₁ ρ * R

lemma vBq_pos (hρ : 0 < ρ) : 0 < vBq E ρ :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by positivity)).ne'
    measure_ball_lt_top.ne

lemma Body.vBq_le (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) : vBq E ρ ≤ volume.real K := by
  refine measureReal_mono (fun y hy => hB.ball ?_) hB.fin
  rw [Metric.mem_ball, dist_zero_right] at hy
  rw [Metric.mem_closedBall, dist_zero_right]; linarith

lemma Body.V0_nonneg (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) : 0 ≤ V0 E v₁ ρ := by
  have h1 := hB.vBq_le hρ
  have h0 := vBq_pos (E := E) hρ
  have : 0 ≤ log (v₁ / vBq E ρ) :=
    log_nonneg ((one_le_div h0).2 (h1.trans hB.vhi))
  unfold V0; positivity

lemma Body.constV_le (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) :
    Large.constV K ρ 2 ≤ V0 E v₁ ρ := by
  unfold Large.constV V0
  have h0 := vBq_pos (E := E) hρ
  have hK := hB.vpos hv₀
  have : log ((volume K).toReal / (volume (Metric.ball (0 : E) (ρ / 4))).toReal) ≤
      log (v₁ / vBq E ρ) :=
    log_le_log (div_pos hK h0) (div_le_div_of_nonneg_right hB.vhi h0.le)
  gcongr

/-- The tilt facts (Lemma 102 with `A = 2`) for `ψ ∈ 𝒞`. -/
lemma tilt_facts (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ}
    (hψ : ψ ∈ Cset K) :
    (∫ y in K, Hd K ψ y • y = 0) ∧ ‖tv K ψ‖ ≤ V0 E v₁ ρ ∧
      ∀ y ∈ K, exp (-A1 E v₁ R ρ) / volume.real K ≤ Hd K ψ y ∧
        Hd K ψ y ≤ exp (A1 E v₁ R ρ) / volume.real K := by
  have hKm := hB.meas
  have hvK := hB.vpos hv₀
  set Z := ∫ y in K, gE K ψ y with hZ
  have hint : IntegrableOn (gE K ψ) K :=
    intOn_bdd hKm hB.fin (measurable_gE hKm ψ).aestronglyMeasurable (C := exp 1) fun y hy => by
      rw [Real.norm_of_nonneg (gE_nonneg ψ y)]; exact (gE_bounds hψ hy).2
  have hZlo : exp (-1) * volume.real K ≤ Z := by
    have := setIntegral_mono_on (integrableOn_const hB.fin) hint hKm
      fun y hy => (gE_bounds hψ hy).1
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hZhi : Z ≤ exp 1 * volume.real K := by
    have := setIntegral_mono_on hint (integrableOn_const hB.fin) hKm
      fun y hy => (gE_bounds hψ hy).2
    rwa [setIntegral_const, smul_eq_mul, mul_comm (volume.real K)] at this
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZlo
  set h0 : E → ℝ := fun y => Z⁻¹ * gE K ψ y
  have ht : ∀ v y, Large.tiltDens K h0 v y = Large.tiltDens K (gE K ψ) v y :=
    tiltDens_const_mul K _ (inv_ne_zero hZpos.ne')
  have hvK' : (volume K).toReal = volume.real K := rfl
  have L := Large.lemma102 hKm hB.bdd hρ hB.ball (A := 2) (by norm_num) (h := h0)
    ((measurable_gE hKm ψ).const_mul _)
    (fun y hy => by
      rw [hvK']
      have := (gE_bounds hψ hy).1
      calc exp (-2) / volume.real K = (exp 1 * volume.real K)⁻¹ * exp (-1) := by
            rw [show (-2 : ℝ) = -1 + -1 by norm_num, exp_add, exp_neg 1]; field_simp
        _ ≤ Z⁻¹ * gE K ψ y := by gcongr)
    (fun y hy => by
      rw [hvK']
      have := (gE_bounds hψ hy).2
      have := gE_nonneg ψ y
      calc Z⁻¹ * gE K ψ y ≤ (exp (-1) * volume.real K)⁻¹ * exp 1 := by gcongr
        _ = exp 2 / volume.real K := by
            rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add, exp_neg 1]; field_simp)
    (by rw [integral_const_mul, ← hZ, inv_mul_cancel₀ hZpos.ne'])
  simp_rw [ht] at L
  obtain ⟨⟨v, hv, -⟩, hb⟩ := L
  have hspec : ∫ y in K, Large.tiltDens K (gE K ψ) (tv K ψ) y • y = 0 :=
    Classical.epsilon_spec (p := fun v => ∫ y in K, Large.tiltDens K (gE K ψ) v y • y = 0)
      ⟨v, hv⟩
  obtain ⟨hn, hb2⟩ := hb _ hspec
  have hc := hB.constV_le hv₀ hρ
  have hR := hB.R_nonneg hρ
  refine ⟨hspec, hn.trans hc, fun y hy => ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (hb2 y hy).1
    rw [hvK']
    unfold A1
    gcongr
  · refine (hb2 y hy).2.trans ?_
    rw [hvK']
    unfold A1
    gcongr

/-- The normalising constant of `h_ψ`. -/
def Zt (K : Set E) (ψ : K →ᵇ ℝ) : ℝ := ∫ z in K, gE K ψ z * exp ⟪tv K ψ, z⟫

lemma Hd_eq (ψ : K →ᵇ ℝ) (y : E) : Hd K ψ y = gE K ψ y * exp ⟪tv K ψ, y⟫ / Zt K ψ := rfl

lemma Hd_of_not_mem {ψ : K →ᵇ ℝ} {y : E} (hy : y ∉ K) : Hd K ψ y = 0 := by
  rw [Hd_eq, gE_of_not_mem hy]; simp

lemma Zt_pos (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ}
    (hψ : ψ ∈ Cset K) : 0 < Zt K ψ := by
  have h0 := ((tilt_facts hB hv₀ hρ hψ).2.2 0 (hB.mem0 hρ)).1
  have hpos : 0 < Hd K ψ 0 := lt_of_lt_of_le (div_pos (exp_pos _) (hB.vpos hv₀)) h0
  have hnn : 0 ≤ Zt K ψ :=
    setIntegral_nonneg hB.meas fun z _ => mul_nonneg (gE_nonneg ψ z) (exp_pos _).le
  rcases hnn.lt_or_eq with h | h
  · exact h
  · rw [Hd_eq, ← h, div_zero] at hpos; exact absurd hpos (lt_irrefl 0)

/-- `h_ψ` lies in the class of Lemma 103 with constants depending only on the parameters. -/
lemma Hd_inH (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ}
    (hψ : ψ ∈ Cset K) :
    LLT.InH (exp (A1 E v₁ R ρ) / v₀) R (exp (-A1 E v₁ R ρ) * σ) (Hd K ψ) := by
  obtain ⟨hmean, -, hb⟩ := tilt_facts hB hv₀ hρ hψ
  have hvK := hB.vpos hv₀
  have hZ := Zt_pos hB hv₀ hρ hψ
  have hcompl : ∀ x ∉ K, Hd K ψ x = 0 := fun x hx => Hd_of_not_mem hx
  refine ⟨((measurable_gE hB.meas ψ).mul (by fun_prop)).div_const _, fun y => ?_, fun y => ?_,
    fun x hx => Hd_of_not_mem fun hxK => by linarith [hB.bdd x hxK], ?_, ?_, fun ξ => ?_⟩
  · by_cases hy : y ∈ K
    · exact le_trans (by positivity) (hb y hy).1
    · rw [Hd_of_not_mem hy]
  · by_cases hy : y ∈ K
    · exact (hb y hy).2.trans (div_le_div_of_nonneg_left (exp_pos _).le hv₀ hB.vlo)
    · rw [Hd_of_not_mem hy]; positivity
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    show ∫ y in K, gE K ψ y * exp ⟪tv K ψ, y⟫ / Zt K ψ = 1
    rw [integral_div, ← Zt, div_self hZ.ne']
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [Hd_of_not_mem hx, zero_smul])]
    exact hmean
  · -- covariance
    have hvar : σ * ‖ξ‖ ^ 2 ≤ ∫ x, ⟪x, ξ⟫ ^ 2 ∂(unifSet K) := by
      rcases eq_or_ne ξ 0 with rfl | hξ
      · simp
      set e := ‖ξ‖⁻¹ • ξ
      have he : ‖e‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ)]
      have h1 := hB.var e he
      have h2 : (fun x => ⟪x, ξ⟫ ^ 2) = fun x => ‖ξ‖ ^ 2 * ⟪e, x⟫ ^ 2 := by
        funext x
        have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
        simp only [e, inner_smul_left, real_inner_comm ξ x]
        simp only [conj_trivial]
        field_simp
      rw [h2, integral_const_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hU : ∫ x, ⟪x, ξ⟫ ^ 2 ∂(unifSet K) = (volume.real K)⁻¹ * ∫ x in K, ⟪x, ξ⟫ ^ 2 := by
      rw [unifSet, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]; rfl
    have i1 : IntegrableOn (fun x => ⟪x, ξ⟫ ^ 2 * (exp (-A1 E v₁ R ρ) / volume.real K)) K :=
      (by fun_prop : Continuous fun x : E => ⟪x, ξ⟫ ^ 2 *
        (exp (-A1 E v₁ R ρ) / volume.real K)).continuousOn.integrableOn_compact hB.compact
    have i2 : IntegrableOn (fun x => ⟪x, ξ⟫ ^ 2 * Hd K ψ x) K := by
      refine intOn_bdd hB.meas hB.fin (C := (R * ‖ξ‖) ^ 2 * (exp (A1 E v₁ R ρ) / volume.real K))
        (((by fun_prop : Continuous fun x : E => ⟪x, ξ⟫ ^ 2).measurable.mul
          (((measurable_gE hB.meas ψ).mul (by fun_prop)).div_const _)).aestronglyMeasurable)
        fun y hy => ?_
      have hy0 : 0 ≤ Hd K ψ y := le_trans (by positivity) (hb y hy).1
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hy0)]
      refine mul_le_mul ?_ (hb y hy).2 hy0 (by positivity)
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      exact (abs_real_inner_le_norm y ξ).trans
        (mul_le_mul_of_nonneg_right (hB.bdd y hy) (norm_nonneg _))
    unfold LLT.quadF
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [Hd_of_not_mem hx, mul_zero])]
    calc exp (-A1 E v₁ R ρ) * σ * ‖ξ‖ ^ 2
        ≤ exp (-A1 E v₁ R ρ) * ((volume.real K)⁻¹ * ∫ x in K, ⟪x, ξ⟫ ^ 2) := by
          rw [mul_assoc, ← hU]; exact mul_le_mul_of_nonneg_left hvar (exp_pos _).le
      _ = ∫ x in K, ⟪x, ξ⟫ ^ 2 * (exp (-A1 E v₁ R ρ) / volume.real K) := by
          rw [integral_mul_const]; ring
      _ ≤ _ := setIntegral_mono_on i1 i2 hB.meas fun y hy =>
          mul_le_mul_of_nonneg_left (hb y hy).1 (sq_nonneg _)

lemma abs_exp_sub_exp_le (a b : ℝ) : |exp a - exp b| ≤ max (exp a) (exp b) * |a - b| := by
  wlog h : b ≤ a generalizing a b
  · rw [abs_sub_comm, max_comm, abs_sub_comm a b]; exact this b a (le_of_not_ge h)
  rw [abs_of_nonneg (sub_nonneg.2 (exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h),
    max_eq_left (exp_le_exp.2 h)]
  have h1 := add_one_le_exp (b - a)
  have h2 : exp b = exp a * exp (b - a) := by rw [← exp_add]; ring_nf
  have h3 := mul_le_mul_of_nonneg_left h1 (exp_pos a).le
  nlinarith

/-- `h_ψ` is Lipschitz on `K`. -/
lemma Hd_lip (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ}
    (hψ : ψ ∈ Cset K) {y y' : E} (hy : y ∈ K) (hy' : y' ∈ K) :
    |Hd K ψ y - Hd K ψ y'| ≤ exp (A1 E v₁ R ρ) / v₀ * (1 + V0 E v₁ ρ) * ‖y - y'‖ := by
  obtain ⟨-, hv, hb⟩ := tilt_facts hB hv₀ hρ hψ
  have hZ := Zt_pos hB hv₀ hρ hψ
  set M := exp (A1 E v₁ R ρ) / v₀
  have hHM : ∀ z (hz : z ∈ K), exp (ψ ⟨z, hz⟩ + ⟪tv K ψ, z⟫) / Zt K ψ ≤ M := fun z hz => by
    have := (hb z hz).2
    rw [Hd_eq, gE_of_mem hz, ← exp_add] at this
    exact this.trans (div_le_div_of_nonneg_left (exp_pos _).le hv₀ hB.vlo)
  rw [Hd_eq, Hd_eq, gE_of_mem hy, gE_of_mem hy', ← exp_add, ← exp_add, ← sub_div, abs_div,
    abs_of_pos hZ]
  set a := ψ ⟨y, hy⟩ + ⟪tv K ψ, y⟫
  set b := ψ ⟨y', hy'⟩ + ⟪tv K ψ, y'⟫
  have hab : |a - b| ≤ (1 + V0 E v₁ ρ) * ‖y - y'‖ := by
    have e1 : |ψ ⟨y, hy⟩ - ψ ⟨y', hy'⟩| ≤ ‖y - y'‖ := by
      have := hψ.2 ⟨y, hy⟩ ⟨y', hy'⟩
      rwa [Subtype.dist_eq, dist_eq_norm] at this
    have e2 : |⟪tv K ψ, y⟫ - ⟪tv K ψ, y'⟫| ≤ V0 E v₁ ρ * ‖y - y'‖ := by
      rw [← inner_sub_right]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
    calc |a - b| = |(ψ ⟨y, hy⟩ - ψ ⟨y', hy'⟩) + (⟪tv K ψ, y⟫ - ⟪tv K ψ, y'⟫)| := by
          congr 1; simp only [a, b]; ring
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  have hmax : max (exp a) (exp b) / Zt K ψ ≤ M := by
    rw [← max_div_div_right hZ.le]
    exact max_le (hHM y hy) (hHM y' hy')
  calc |exp a - exp b| / Zt K ψ ≤ max (exp a) (exp b) * |a - b| / Zt K ψ := by
        gcongr; exact abs_exp_sub_exp_le a b
    _ = max (exp a) (exp b) / Zt K ψ * |a - b| := by ring
    _ ≤ M * ((1 + V0 E v₁ ρ) * ‖y - y'‖) :=
        mul_le_mul hmax hab (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma ft_mix_le {h u : E → ℝ} (hh : Integrable h) (hu : Integrable u) {a : ℝ} (ha : 0 ≤ a)
    (hk : ∀ x, a * u x ≤ h x) (h1 : ∫ x, h x = 1) (u1 : ∫ x, u x = 1) (ξ : E) :
    ‖Thm113.ft h ξ‖ ≤ 1 - a + a * ‖Thm113.ft u ξ‖ := by
  have hk' : Integrable (fun x => h x - a * u x) := hh.sub (hu.const_mul a)
  have e : Thm113.ft h ξ = Thm113.ft (fun x => h x - a * u x) ξ + (a : ℂ) * Thm113.ft u ξ := by
    unfold Thm113.ft
    rw [← integral_const_mul, ← integral_add (Thm113.integrable_ft_mul hk' ξ)
      ((Thm113.integrable_ft_mul hu ξ).const_mul _)]
    congr 1; funext y; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · calc ‖Thm113.ft (fun x => h x - a * u x) ξ‖ ≤ ∫ x, (h x - a * u x) :=
          norm_integral_le_of_norm_le hk' (ae_of_all _ fun y => by
            rw [norm_mul, Thm113.norm_ex, mul_one, Complex.norm_real,
              Real.norm_of_nonneg (sub_nonneg.2 (hk y))])
      _ = 1 - a := by rw [integral_sub hh (hu.const_mul a), integral_const_mul, h1, u1, mul_one]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]

/-- The Fourier gap of `h_ψ` from that of `U(K)`. -/
lemma Hd_gap (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ}
    (hψ : ψ ∈ Cset K) (ξ : E) :
    ‖LLT.hatC (Hd K ψ) ξ‖ ≤ 1 - exp (-A1 E v₁ R ρ) +
      exp (-A1 E v₁ R ρ) * ‖charFun (unifSet K) (-(2 * π) • ξ)‖ := by
  have hH := Hd_inH hB hv₀ hρ hψ
  obtain ⟨-, -, hb⟩ := tilt_facts hB hv₀ hρ hψ
  have hvK := hB.vpos hv₀
  show ‖FourierTransform.fourier (fun x => ((Hd K ψ x : ℝ) : ℂ)) ξ‖ ≤ _
  rw [← Thm113.ft_eq_fourier, charFun_unifSet_eq_ft hB.meas, smul_smul,
    show -(2 * π)⁻¹ * -(2 * π) = 1 by field_simp, one_smul]
  refine ft_mix_le hH.integrable ((integrableOn_const hB.fin).integrable_indicator hB.meas)
    (exp_pos _).le (fun x => ?_) hH.int1 ?_ ξ
  · by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, ← div_eq_mul_inv]; exact (hb x hx).1
    · rw [Set.indicator_of_notMem hx, Hd_of_not_mem hx, mul_zero]
  · rw [integral_indicator hB.meas, setIntegral_const, smul_eq_mul, mul_inv_cancel₀ hvK.ne']

/-- The `L¹` modulus of `h_ψ`, uniform over the class. -/
lemma Hd_l1 (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ)
    (hd : 1 ≤ Module.finrank ℝ E) {ψ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K) (y y' : E) :
    ∫ z, |Hd K ψ (y - z) - Hd K ψ (y' - z)| ≤
      (exp (A1 E v₁ R ρ) / v₀ * (1 + V0 E v₁ ρ) * v₁ +
        2 * (exp (A1 E v₁ R ρ) / v₀) * Module.finrank ℝ E * v₁ / ρ) * ‖y - y'‖ := by
  have hH := Hd_inH hB hv₀ hρ hψ
  have hV := hB.V0_nonneg hρ
  have hM : 0 ≤ exp (A1 E v₁ R ρ) / v₀ := by positivity
  refine (LLT.l1_modulus hB.meas hB.convex hρ hB.ball hB.fin hd (G := exp (A1 E v₁ R ρ) / v₀)
    (L := exp (A1 E v₁ R ρ) / v₀ * (1 + V0 E v₁ ρ)) hM (by positivity)
    (fun x hx => Hd_of_not_mem hx)
    (fun x _ => by rw [abs_of_nonneg (hH.nonneg x)]; exact hH.le x)
    (fun x hx x' hx' => Hd_lip hB hv₀ hρ hψ hx hx') y y').trans ?_
  gcongr
  · exact hB.vhi
  · exact hB.vhi

/-! ### Continuity of `ψ ↦ h_ψ` (quantitative) -/

lemma gE_diff {ψ φ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K) (hφ : φ ∈ Cset K) {y : E} (hy : y ∈ K) :
    |gE K φ y - gE K ψ y| ≤ exp 1 * dist φ ψ := by
  rw [gE_of_mem hy, gE_of_mem hy]
  refine (abs_exp_sub_exp_le _ _).trans (mul_le_mul ?_ ?_ (abs_nonneg _) (exp_pos _).le)
  · exact max_le (exp_le_exp.2 (abs_le.1 (hφ.1 _)).2) (exp_le_exp.2 (abs_le.1 (hψ.1 _)).2)
  · rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist _

lemma exp_inner_le' {v y : E} {V : ℝ} (hv : ‖v‖ ≤ V) (hy : ‖y‖ ≤ R) (_hR : 0 ≤ R) :
    exp (-(V * R)) ≤ exp ⟪v, y⟫ ∧ exp ⟪v, y⟫ ≤ exp (V * R) := by
  have h1 := abs_real_inner_le_norm v y
  have h2 : ‖v‖ * ‖y‖ ≤ V * R := mul_le_mul hv hy (norm_nonneg _) ((norm_nonneg _).trans hv)
  have := abs_le.1 (h1.trans h2)
  exact ⟨exp_le_exp.2 (by linarith), exp_le_exp.2 this.2⟩

/-- The unnormalised mean of the tilt of `e^ψ u` by `v`. -/
def Mn (K : Set E) (ψ : K →ᵇ ℝ) (v : E) : E := ∫ y in K, (gE K ψ y * exp ⟪v, y⟫) • y

lemma intOn_Mn (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K) (v : E) :
    IntegrableOn (fun y => (gE K ψ y * exp ⟪v, y⟫) • y) K := by
  have hR := hB.R_nonneg hρ
  refine intOn_bdd hB.meas hB.fin (C := exp 1 * exp (‖v‖ * R) * R)
    (((measurable_gE hB.meas ψ).mul (by fun_prop)).smul measurable_id).aestronglyMeasurable
    fun y hy => ?_
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (gE_nonneg ψ y) (exp_pos _).le)]
  exact mul_le_mul (mul_le_mul (gE_bounds hψ hy).2
    (exp_inner_le' le_rfl (hB.bdd y hy) hR).2 (exp_pos _).le (exp_pos _).le) (hB.bdd y hy)
    (norm_nonneg _) (by positivity)

lemma Mn_tv (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) {ψ : K →ᵇ ℝ}
    (hψ : ψ ∈ Cset K) : Mn K ψ (tv K ψ) = 0 := by
  have h := (tilt_facts hB hv₀ hρ hψ).1
  have e : (fun y => Hd K ψ y • y) =
      fun y => (Zt K ψ)⁻¹ • ((gE K ψ y * exp ⟪tv K ψ, y⟫) • y) := by
    funext y; rw [Hd_eq, smul_smul, div_eq_inv_mul]
  rw [e, integral_smul] at h
  exact (smul_eq_zero.1 h).resolve_left (inv_ne_zero (Zt_pos hB hv₀ hρ hψ).ne')

lemma Body.varK (hB : Body v₀ v₁ R ρ σ K) (ξ : E) :
    σ * ‖ξ‖ ^ 2 * volume.real K ≤ ∫ x in K, ⟪x, ξ⟫ ^ 2 := by
  have hvar : σ * ‖ξ‖ ^ 2 ≤ ∫ x, ⟪x, ξ⟫ ^ 2 ∂(unifSet K) := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    set e := ‖ξ‖⁻¹ • ξ
    have he : ‖e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ)]
    have h1 := hB.var e he
    have h2 : (fun x => ⟪x, ξ⟫ ^ 2) = fun x => ‖ξ‖ ^ 2 * ⟪e, x⟫ ^ 2 := by
      funext x
      have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
      simp only [e, inner_smul_left, real_inner_comm ξ x]
      simp only [conj_trivial]
      field_simp
    rw [h2, integral_const_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hU : ∫ x, ⟪x, ξ⟫ ^ 2 ∂(unifSet K) = (volume.real K)⁻¹ * ∫ x in K, ⟪x, ξ⟫ ^ 2 := by
    rw [unifSet, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]; rfl
  rw [hU] at hvar
  rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ volume.real K) with h0 | h0
  · rw [← h0, mul_zero]
    exact setIntegral_nonneg hB.meas fun _ _ => sq_nonneg _
  · calc σ * ‖ξ‖ ^ 2 * volume.real K
        ≤ (volume.real K)⁻¹ * (∫ x in K, ⟪x, ξ⟫ ^ 2) * volume.real K :=
          mul_le_mul_of_nonneg_right hvar h0.le
      _ = _ := by field_simp

lemma exp_sub_mul_ge {a b c : ℝ} (ha : c ≤ a) (hb : c ≤ b) :
    exp c * (a - b) ^ 2 ≤ (exp a - exp b) * (a - b) := by
  wlog h : b ≤ a generalizing a b
  · have := this hb ha (le_of_not_ge h)
    nlinarith
  have h1 := add_one_le_exp (a - b)
  have h2 : exp a = exp b * exp (a - b) := by rw [← exp_add]; ring_nf
  have h3 : exp b * (a - b) ≤ exp a - exp b := by
    have := mul_le_mul_of_nonneg_left h1 (exp_pos b).le
    nlinarith
  have h4 : exp c ≤ exp b := exp_le_exp.2 hb
  have h5 : 0 ≤ a - b := sub_nonneg.2 h
  nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg (a - b))]

/-- Strong monotonicity of `v ↦ Mn ψ v` on the ball of radius `V0`. -/
lemma Mn_mono (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) {φ : K →ᵇ ℝ} (hφ : φ ∈ Cset K) {v w : E}
    (hv : ‖v‖ ≤ V0 E v₁ ρ) (hw : ‖w‖ ≤ V0 E v₁ ρ) :
    exp (-1) * exp (-(V0 E v₁ ρ * R)) * (σ * ‖v - w‖ ^ 2 * volume.real K) ≤
      ⟪Mn K φ v - Mn K φ w, v - w⟫ := by
  have hR := hB.R_nonneg hρ
  set V := V0 E v₁ ρ
  have i1 := intOn_Mn hB hρ hφ v
  have i2 := intOn_Mn hB hρ hφ w
  have i12 : Integrable (fun y => (gE K φ y * exp ⟪v, y⟫) • y - (gE K φ y * exp ⟪w, y⟫) • y)
      (volume.restrict K) := i1.sub i2
  rw [Mn, Mn, ← integral_sub i1 i2, real_inner_comm, ← integral_inner i12]
  have i3 : IntegrableOn (fun x => ⟪x, v - w⟫ ^ 2) K :=
    (by fun_prop : Continuous fun x : E => ⟪x, v - w⟫ ^ 2).continuousOn.integrableOn_compact
      hB.compact
  calc exp (-1) * exp (-(V * R)) * (σ * ‖v - w‖ ^ 2 * volume.real K)
      ≤ exp (-1) * exp (-(V * R)) * ∫ x in K, ⟪x, v - w⟫ ^ 2 :=
        mul_le_mul_of_nonneg_left (hB.varK _) (by positivity)
    _ = ∫ x in K, exp (-1) * exp (-(V * R)) * ⟪x, v - w⟫ ^ 2 := (integral_const_mul _ _).symm
    _ ≤ _ := by
        refine setIntegral_mono_on (i3.const_mul _) (i12.const_inner _) hB.meas
          fun y hy => ?_
        rw [← sub_smul, inner_smul_right]
        have hyR := hB.bdd y hy
        have e1 : -(V * R) ≤ ⟪v, y⟫ := by
          have := abs_le.1 ((abs_real_inner_le_norm v y).trans
            (mul_le_mul hv hyR (norm_nonneg _) ((norm_nonneg _).trans hv)))
          linarith
        have e2 : -(V * R) ≤ ⟪w, y⟫ := by
          have := abs_le.1 ((abs_real_inner_le_norm w y).trans
            (mul_le_mul hw hyR (norm_nonneg _) ((norm_nonneg _).trans hw)))
          linarith
        have key := exp_sub_mul_ge e1 e2
        have hi : ⟪y, v - w⟫ = ⟪v, y⟫ - ⟪w, y⟫ := by
          rw [inner_sub_right, real_inner_comm v y, real_inner_comm w y]
        have hi' : ⟪v - w, y⟫ = ⟪v, y⟫ - ⟪w, y⟫ := by rw [inner_sub_left]
        rw [hi, hi']
        have hg := (gE_bounds hφ hy).1
        calc exp (-1) * exp (-(V * R)) * (⟪v, y⟫ - ⟪w, y⟫) ^ 2
            ≤ gE K φ y * ((exp ⟪v, y⟫ - exp ⟪w, y⟫) * (⟪v, y⟫ - ⟪w, y⟫)) := by
              rw [mul_assoc]
              exact mul_le_mul hg key (by positivity) (gE_nonneg φ y)
          _ = _ := by ring

lemma Mn_diff (hB : Body v₀ v₁ R ρ σ K) (hρ : 0 < ρ) {ψ φ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K)
    (hφ : φ ∈ Cset K) {v : E} (hv : ‖v‖ ≤ V0 E v₁ ρ) :
    ‖Mn K φ v - Mn K ψ v‖ ≤ exp 1 * dist φ ψ * exp (V0 E v₁ ρ * R) * R * volume.real K := by
  have hR := hB.R_nonneg hρ
  rw [Mn, Mn, ← integral_sub (intOn_Mn hB hρ hφ v) (intOn_Mn hB hρ hψ v)]
  refine norm_setIntegral_le_of_norm_le_const hB.compact.measure_lt_top fun y hy => ?_
  rw [← sub_smul, ← sub_mul, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (exp_pos _)]
  exact mul_le_mul (mul_le_mul (gE_diff hψ hφ hy) (exp_inner_le' hv (hB.bdd y hy) hR).2
    (exp_pos _).le (by positivity)) (hB.bdd y hy) (norm_nonneg _) (by positivity)

/-- The tilt vector is Lipschitz in `ψ` on `𝒞`. -/
lemma tv_lip (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) (hσ : 0 < σ)
    {ψ φ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K) (hφ : φ ∈ Cset K) :
    ‖tv K ψ - tv K φ‖ ≤ exp 2 * exp (2 * (V0 E v₁ ρ * R)) * R / σ * dist φ ψ := by
  set v := tv K ψ
  set w := tv K φ
  have hv := (tilt_facts hB hv₀ hρ hψ).2.1
  have hw := (tilt_facts hB hv₀ hρ hφ).2.1
  have hvK := hB.vpos hv₀
  have hR := hB.R_nonneg hρ
  set V := V0 E v₁ ρ
  have h1 := Mn_mono hB hρ hφ hv hw
  rw [Mn_tv hB hv₀ hρ hφ, sub_zero, show Mn K φ v = Mn K φ v - Mn K ψ v by
    rw [Mn_tv hB hv₀ hρ hψ, sub_zero]] at h1
  have h2 := (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (Mn_diff hB hρ hψ hφ hv) (norm_nonneg (v - w)))
  have h3 := h1.trans h2
  rcases eq_or_lt_of_le (norm_nonneg (v - w)) with h0 | h0
  · rw [← h0]; positivity
  have hc : 0 < exp (-1) * exp (-(V * R)) * σ * volume.real K := by positivity
  have h4 : exp (-1) * exp (-(V * R)) * σ * volume.real K * ‖v - w‖ ≤
      exp 1 * dist φ ψ * exp (V * R) * R * volume.real K := by
    have : exp (-1) * exp (-(V * R)) * σ * volume.real K * ‖v - w‖ * ‖v - w‖ ≤
        exp 1 * dist φ ψ * exp (V * R) * R * volume.real K * ‖v - w‖ := by
      nlinarith
    exact le_of_mul_le_mul_right this h0
  rw [div_mul_eq_mul_div, le_div_iff₀ hσ]
  have e1 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
  have e2 : exp (2 * (V * R)) = exp (V * R) * exp (V * R) := by rw [← exp_add]; ring_nf
  have e3 : exp (-1) * exp 1 = 1 := by rw [← exp_add]; norm_num
  have e4 : exp (-(V * R)) * exp (V * R) = 1 := by rw [← exp_add]; norm_num
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ exp 1 * exp (V * R))
  have h6 : exp 1 * exp (V * R) * (exp (-1) * exp (-(V * R)) * σ * volume.real K * ‖v - w‖) =
      σ * volume.real K * ‖v - w‖ := by
    calc _ = (exp (-1) * exp 1) * (exp (-(V * R)) * exp (V * R)) * σ * volume.real K *
          ‖v - w‖ := by ring
      _ = _ := by rw [e3, e4]; ring
  rw [h6] at h5
  have h7 : σ * volume.real K * ‖v - w‖ ≤
      volume.real K * (exp 2 * exp (2 * (V * R)) * R * dist φ ψ) := by
    rw [e1, e2]; nlinarith
  have := le_of_mul_le_mul_left (by nlinarith : volume.real K * (‖v - w‖ * σ) ≤
    volume.real K * (exp 2 * exp (2 * (V * R)) * R * dist φ ψ)) hvK
  linarith

lemma ratio_diff {a1 a2 Z1 Z2 z A : ℝ} (hz : 0 < z) (h1 : z ≤ Z1) (h2 : z ≤ Z2) (ha2 : 0 ≤ a2)
    (hA : a2 ≤ A) : |a1 / Z1 - a2 / Z2| ≤ |a1 - a2| / z + A * |Z1 - Z2| / z ^ 2 := by
  have hZ1 : 0 < Z1 := hz.trans_le h1
  have hZ2 : 0 < Z2 := hz.trans_le h2
  rw [show a1 / Z1 - a2 / Z2 = (a1 - a2) / Z1 + a2 * (Z2 - Z1) / (Z1 * Z2) by
    field_simp; ring]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hZ1]; exact div_le_div_of_nonneg_left (abs_nonneg _) hz h1
  · rw [abs_div, abs_mul, abs_of_nonneg ha2, abs_of_pos (mul_pos hZ1 hZ2), abs_sub_comm Z2 Z1,
      sq]
    exact div_le_div₀ (by nlinarith [abs_nonneg (Z1 - Z2)])
      (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) (by positivity) (mul_le_mul h1 h2 hz.le
        hZ1.le)

/-- `ψ ↦ h_ψ` is Lipschitz on `𝒞` in the supremum norm. -/
lemma Hd_diff (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀) (hρ : 0 < ρ) (hσ : 0 < σ)
    {ψ : K →ᵇ ℝ} (hψ : ψ ∈ Cset K) :
    ∃ C, 0 ≤ C ∧ ∀ φ ∈ Cset K, ∀ y, |Hd K φ y - Hd K ψ y| ≤ C * dist φ ψ := by
  have hR := hB.R_nonneg hρ
  have hvK := hB.vpos hv₀
  set V := V0 E v₁ ρ
  have hV : 0 ≤ V := hB.V0_nonneg hρ
  set Cv := exp 2 * exp (2 * (V * R)) * R / σ
  have hCv : 0 ≤ Cv := by positivity
  set Ca := exp 1 * exp (V * R) * (1 + R * Cv)
  set z := exp (-1) * exp (-(V * R)) * volume.real K
  set A := exp 1 * exp (V * R)
  have hz : 0 < z := by positivity
  refine ⟨Ca / z + A * (Ca * volume.real K) / z ^ 2, by positivity, fun φ hφ y => ?_⟩
  by_cases hy : y ∉ K
  · rw [Hd_of_not_mem hy, Hd_of_not_mem hy, sub_zero, abs_zero]
    exact mul_nonneg (by positivity) dist_nonneg
  push Not at hy
  set δ := dist φ ψ
  have hδ : 0 ≤ δ := dist_nonneg
  -- bounds on the numerators
  have ha : ∀ (χ : K →ᵇ ℝ), χ ∈ Cset K → ∀ x ∈ K,
      0 ≤ gE K χ x * exp ⟪tv K χ, x⟫ ∧ gE K χ x * exp ⟪tv K χ, x⟫ ≤ A ∧
        exp (-1) * exp (-(V * R)) ≤ gE K χ x * exp ⟪tv K χ, x⟫ := fun χ hχ x hx => by
    have hv := (tilt_facts hB hv₀ hρ hχ).2.1
    have e := exp_inner_le' hv (hB.bdd x hx) hR
    have g := gE_bounds hχ hx
    exact ⟨mul_nonneg (gE_nonneg χ x) (exp_pos _).le,
      mul_le_mul g.2 e.2 (exp_pos _).le (exp_pos _).le,
      mul_le_mul g.1 e.1 (exp_pos _).le (gE_nonneg χ x)⟩
  have hdiff : ∀ x ∈ K, |gE K φ x * exp ⟪tv K φ, x⟫ - gE K ψ x * exp ⟪tv K ψ, x⟫| ≤ Ca * δ :=
    fun x hx => by
    have hvφ := (tilt_facts hB hv₀ hρ hφ).2.1
    have hvψ := (tilt_facts hB hv₀ hρ hψ).2.1
    have eφ := exp_inner_le' hvφ (hB.bdd x hx) hR
    have eψ := exp_inner_le' hvψ (hB.bdd x hx) hR
    have h1 := gE_diff hψ hφ hx
    have h2 : |exp ⟪tv K φ, x⟫ - exp ⟪tv K ψ, x⟫| ≤ exp (V * R) * (R * (Cv * δ)) := by
      refine (abs_exp_sub_exp_le _ _).trans (mul_le_mul (max_le eφ.2 eψ.2) ?_ (abs_nonneg _)
        (exp_pos _).le)
      rw [← inner_sub_left]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [mul_comm]
      refine mul_le_mul (hB.bdd x hx) ?_ (norm_nonneg _) hR
      rw [norm_sub_rev]; exact tv_lip hB hv₀ hρ hσ hψ hφ
    have hg := gE_bounds hψ hx
    calc |gE K φ x * exp ⟪tv K φ, x⟫ - gE K ψ x * exp ⟪tv K ψ, x⟫|
        = |(gE K φ x - gE K ψ x) * exp ⟪tv K φ, x⟫ +
            gE K ψ x * (exp ⟪tv K φ, x⟫ - exp ⟪tv K ψ, x⟫)| := by congr 1; ring
      _ ≤ |gE K φ x - gE K ψ x| * exp ⟪tv K φ, x⟫ +
            gE K ψ x * |exp ⟪tv K φ, x⟫ - exp ⟪tv K ψ, x⟫| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_nonneg (gE_nonneg ψ x)]
      _ ≤ exp 1 * δ * exp (V * R) + exp 1 * (exp (V * R) * (R * (Cv * δ))) :=
          add_le_add (mul_le_mul h1 eφ.2 (exp_pos _).le (by positivity))
            (mul_le_mul hg.2 h2 (abs_nonneg _) (exp_pos _).le)
      _ = Ca * δ := by simp only [Ca]; ring
  -- the normalising constants
  have hZlo : ∀ (χ : K →ᵇ ℝ), χ ∈ Cset K → z ≤ Zt K χ := fun χ hχ => by
    have := setIntegral_mono_on (integrableOn_const hB.fin (C := exp (-1) * exp (-(V * R))))
      (intOn_bdd hB.meas hB.fin (f := fun x => gE K χ x * exp ⟪tv K χ, x⟫) (C := A)
        (((measurable_gE hB.meas χ).mul
        (by fun_prop)).aestronglyMeasurable) fun x hx => by
          rw [Real.norm_of_nonneg (ha χ hχ x hx).1]; exact (ha χ hχ x hx).2.1)
      hB.meas fun x hx => (ha χ hχ x hx).2.2
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hZd : |Zt K φ - Zt K ψ| ≤ Ca * δ * volume.real K := by
    have iφ := intOn_bdd hB.meas hB.fin (f := fun x => gE K φ x * exp ⟪tv K φ, x⟫) (C := A)
        (((measurable_gE hB.meas φ).mul
        (by fun_prop : Measurable fun x => exp ⟪tv K φ, x⟫)).aestronglyMeasurable)
        fun x hx => by
          rw [Real.norm_of_nonneg (ha φ hφ x hx).1]; exact (ha φ hφ x hx).2.1
    have iψ := intOn_bdd hB.meas hB.fin (f := fun x => gE K ψ x * exp ⟪tv K ψ, x⟫) (C := A)
        (((measurable_gE hB.meas ψ).mul
        (by fun_prop : Measurable fun x => exp ⟪tv K ψ, x⟫)).aestronglyMeasurable)
        fun x hx => by
          rw [Real.norm_of_nonneg (ha ψ hψ x hx).1]; exact (ha ψ hψ x hx).2.1
    rw [Zt, Zt, ← integral_sub iφ iψ, ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const hB.compact.measure_lt_top fun x hx => by
      rw [Real.norm_eq_abs]; exact hdiff x hx
  rw [Hd_eq, Hd_eq]
  refine (ratio_diff hz (hZlo φ hφ) (hZlo ψ hψ) (ha ψ hψ y hy).1 (ha ψ hψ y hy).2.1).trans ?_
  calc |gE K φ y * exp ⟪tv K φ, y⟫ - gE K ψ y * exp ⟪tv K ψ, y⟫| / z +
        A * |Zt K φ - Zt K ψ| / z ^ 2 ≤ Ca * δ / z + A * (Ca * δ * volume.real K) / z ^ 2 := by
        gcongr
        exact hdiff y hy
    _ = _ := by ring

/-- `‖h₁^{*j} - h₂^{*j}‖_∞ ≤ (j + 1) ‖h₁ - h₂‖_∞` for densities in the class. -/
lemma convPow_diff {M R' σ' : ℝ} {h1 h2 : E → ℝ} (hh1 : LLT.InH M R' σ' h1)
    (hh2 : LLT.InH M R' σ' h2) {η : ℝ} (hη : ∀ x, |h1 x - h2 x| ≤ η) :
    ∀ j x, |LLT.convPow h1 j x - LLT.convPow h2 j x| ≤ (j + 1) * η := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0)
  intro j
  induction j with
  | zero => intro x; simp only [LLT.convPow]; push_cast; linarith [hη x]
  | succ j ih =>
    rcases j with _ | j
    · intro x; simp only [LLT.convPow]; push_cast; linarith [hη x]
    intro x
    rw [LLT.convPow_add_two, LLT.convPow_add_two, convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    set c1 := LLT.convPow h1 (j + 1)
    set c2 := LLT.convPow h2 (j + 1)
    have p1 := LLT.convPow_props hh1 (j + 1)
    have p2 := LLT.convPow_props hh2 (j + 1)
    have m1 := (LLT.convPow_cont hh1 j).1
    have m2 := (LLT.convPow_cont hh2 j).1
    have ic1 : Integrable fun t => c1 (x - t) := p1.1.comp_sub_left x
    have ic2 : Integrable fun t => c2 (x - t) := p2.1.comp_sub_left x
    have hM : 0 ≤ M := hh1.M_nonneg
    have f1 : Integrable fun t => h1 t * c1 (x - t) := by
      refine Integrable.mono' (ic1.const_mul M)
        (hh1.meas.mul (m1.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
        (ae_of_all _ fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hh1.nonneg t) (p1.2.1 _))]
      exact mul_le_mul_of_nonneg_right (hh1.le t) (p1.2.1 _)
    have f2 : Integrable fun t => h2 t * c2 (x - t) := by
      refine Integrable.mono' (ic2.const_mul M)
        (hh2.meas.mul (m2.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
        (ae_of_all _ fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hh2.nonneg t) (p2.2.1 _))]
      exact mul_le_mul_of_nonneg_right (hh2.le t) (p2.2.1 _)
    rw [← integral_sub f1 f2, ← Real.norm_eq_abs]
    have hG : Integrable fun t => η * c1 (x - t) + ((j + 1 + 1 : ℕ) : ℝ) * η * h2 t :=
      (ic1.const_mul η).add (hh2.integrable.const_mul _)
    refine (norm_integral_le_of_norm_le hG (ae_of_all _ fun t => ?_)).trans (le_of_eq ?_)
    · rw [Real.norm_eq_abs]
      have e1 := hη t
      have e2 := ih (x - t)
      have q1 := p1.2.1 (x - t)
      have q2 := hh2.nonneg t
      calc |h1 t * c1 (x - t) - h2 t * c2 (x - t)|
          = |(h1 t - h2 t) * c1 (x - t) + h2 t * (c1 (x - t) - c2 (x - t))| := by
            congr 1; ring
        _ ≤ |h1 t - h2 t| * c1 (x - t) + h2 t * |c1 (x - t) - c2 (x - t)| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_of_nonneg q1, abs_of_nonneg q2]
        _ ≤ η * c1 (x - t) + h2 t * (((j + 1 : ℕ) : ℝ) + 1) * η := by
            rw [mul_assoc]; gcongr
        _ = _ := by push_cast; ring
    · rw [integral_add (ic1.const_mul η) (hh2.integrable.const_mul _), integral_const_mul,
        integral_const_mul, integral_sub_left_eq_self (fun t => c1 t) volume x, p1.2.2.2,
        hh2.int1]
      push_cast; ring

end Core

section FixedPoint

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {v₀ v₁ R ρ σ : ℝ} {K : Set E}

/-- `F_ψ(0) - F_ψ(p)` with `F_ψ(p) = log h_ψ^{*m}(-p)`, `m = j + 2`. -/
def Fn (K : Set E) (j : ℕ) (ψ : K →ᵇ ℝ) (p : K) : ℝ :=
  log (LLT.convPow (Hd K ψ) (j + 2) 0) - log (LLT.convPow (Hd K ψ) (j + 2) (-(p : E)))

open Classical in
/-- The map `Ψ` of the proof of Theorem 104 (normalised by its value at `0` instead of the
projection onto affine functions). -/
def PsiMap (K : Set E) [CompactSpace K] (j : ℕ) (ψ : K →ᵇ ℝ) : K →ᵇ ℝ :=
  if hc : Continuous (Fn K j ψ) then BoundedContinuousFunction.mkOfCompact ⟨Fn K j ψ, hc⟩
  else 0

lemma PsiMap_apply [CompactSpace K] {j : ℕ} {ψ : K →ᵇ ℝ} (hc : Continuous (Fn K j ψ))
    (p : K) : PsiMap K j ψ p = Fn K j ψ p := by
  rw [PsiMap, dite_eq_left_of_eq_true (eq_true hc)]; rfl

lemma isCompact_Cset [CompactSpace K] : IsCompact (Cset K) := by
  refine BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-1 : ℝ) 1) isCompact_Icc _ ?_
    (fun ψ p hψ => abs_le.1 (hψ.1 p)) ?_
  · have e : Cset K = (⋂ p, {ψ : K →ᵇ ℝ | |ψ p| ≤ 1}) ∩
        ⋂ p, ⋂ q, {ψ : K →ᵇ ℝ | |ψ p - ψ q| ≤ dist p q} := by
      ext ψ; simp [Cset]
    rw [e]
    refine (isClosed_iInter fun p => isClosed_le
      (continuous_eval_const p).abs continuous_const).inter
      (isClosed_iInter fun p => isClosed_iInter fun q => isClosed_le
        ((continuous_eval_const p).sub
          (continuous_eval_const q)).abs continuous_const)
  · refine (LipschitzWith.uniformEquicontinuous _ 1 fun ψ => ?_).equicontinuous
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact ψ.2.2 p q

lemma convex_Cset : Convex ℝ (Cset K) := by
  intro ψ hψ φ hφ a b ha hb hab
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · simp only [add_apply, smul_apply,
      smul_eq_mul]
    calc |a * ψ p + b * φ p| ≤ a * |ψ p| + b * |φ p| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr; exacts [hψ.1 p, hφ.1 p]
      _ = 1 := by linarith
  · simp only [add_apply, smul_apply,
      smul_eq_mul]
    calc |a * ψ p + b * φ p - (a * ψ q + b * φ q)|
        = |a * (ψ p - ψ q) + b * (φ p - φ q)| := by congr 1; ring
      _ ≤ a * |ψ p - ψ q| + b * |φ p - φ q| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * dist p q + b * dist p q := by gcongr; exacts [hψ.2 p q, hφ.2 p q]
      _ = dist p q := by rw [← add_mul, hab, one_mul]

lemma zero_mem_Cset : (0 : K →ᵇ ℝ) ∈ Cset K :=
  ⟨fun p => by simp, fun p q => by simp⟩

/-- **Theorem 104 for one body, given the estimates of Lemma 103**: if `h_ψ^{*(j+2)}` is bounded
below by `c₀ > 0` and its logarithm is `ε`-Lipschitz on the ball of radius `R`, uniformly for
`ψ ∈ 𝒞`, with `ε ≤ 1` and `εR ≤ 1`, then Schauder's theorem gives a fixed point of `Ψ`, whose
conditioned product is a `(j+3)`-complete mix of `U(K)`. -/
theorem cm_of_body (hS : SchauderFPT.{u}) (hB : Body v₀ v₁ R ρ σ K) (hv₀ : 0 < v₀)
    (hρ : 0 < ρ) (hσ : 0 < σ) (j : ℕ) {ε c0 : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hεR : ε * R ≤ 1)
    (hc0 : 0 < c0)
    (hlow : ∀ ψ ∈ Cset K, ∀ y : E, ‖y‖ ≤ R → c0 ≤ LLT.convPow (Hd K ψ) (j + 2) y)
    (hlip : ∀ ψ ∈ Cset K, ∀ y y' : E, ‖y‖ ≤ R → ‖y'‖ ≤ R →
      |log (LLT.convPow (Hd K ψ) (j + 2) y) - log (LLT.convPow (Hd K ψ) (j + 2) y')| ≤
        ε * ‖y - y'‖)
    (hpos3 : ∀ ψ ∈ Cset K, 0 < LLT.convPow (Hd K ψ) (j + 3) 0) :
    CompletelyMixable (j + 3) (unifSet K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hB.compact
  have hR := hB.R_nonneg hρ
  have hnorm : ∀ p : K, ‖-(p : E)‖ ≤ R := fun p => by rw [norm_neg]; exact hB.bdd p p.2
  have hcont : ∀ ψ ∈ Cset K, Continuous (Fn K j ψ) := fun ψ hψ => by
    have hH := Hd_inH hB hv₀ hρ hψ
    have hc := (LLT.convPow_cont hH j).2
    exact continuous_const.sub ((hc.comp continuous_subtypeVal.neg).log fun p =>
      (hc0.trans_le (hlow ψ hψ _ (hnorm p))).ne')
  have h0R : ‖(0 : E)‖ ≤ R := by rw [norm_zero]; exact hR
  -- `Ψ(𝒞) ⊆ 𝒞`
  have hmaps : Set.MapsTo (PsiMap K j) (Cset K) (Cset K) := fun ψ hψ => by
    refine ⟨fun p => ?_, fun p q => ?_⟩
    · rw [PsiMap_apply (hcont ψ hψ), Fn]
      refine (hlip ψ hψ 0 _ h0R (hnorm p)).trans ?_
      rw [zero_sub, norm_neg, norm_neg]
      calc ε * ‖(p : E)‖ ≤ ε * R := mul_le_mul_of_nonneg_left (hB.bdd p p.2) hε0
        _ ≤ 1 := hεR
    · rw [PsiMap_apply (hcont ψ hψ), PsiMap_apply (hcont ψ hψ), Fn, Fn]
      have := hlip ψ hψ _ _ (hnorm q) (hnorm p)
      rw [show log (LLT.convPow (Hd K ψ) (j + 2) 0) -
          log (LLT.convPow (Hd K ψ) (j + 2) (-(p : E))) -
          (log (LLT.convPow (Hd K ψ) (j + 2) 0) -
            log (LLT.convPow (Hd K ψ) (j + 2) (-(q : E)))) =
          log (LLT.convPow (Hd K ψ) (j + 2) (-(q : E))) -
            log (LLT.convPow (Hd K ψ) (j + 2) (-(p : E))) by ring]
      refine this.trans ?_
      rw [neg_sub_neg, ← dist_eq_norm, ← Subtype.dist_eq]
      exact mul_le_of_le_one_left dist_nonneg hε
  -- continuity of `Ψ` on `𝒞`
  have hcontOn : ContinuousOn (PsiMap K j) (Cset K) := by
    rw [Metric.continuousOn_iff]
    intro ψ hψ e he
    obtain ⟨CH, hCH, hdiff⟩ := Hd_diff hB hv₀ hρ hσ hψ
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 2 * ((j + 2 + 1 : ℝ) * CH) / c0 := ⟨_, rfl⟩
    have hL : 0 ≤ L := by rw [hLdef]; positivity
    refine ⟨e / (L + 1), by positivity, fun φ hφ hd => ?_⟩
    have hH := Hd_inH hB hv₀ hρ hψ
    have hH' := Hd_inH hB hv₀ hρ hφ
    have hcv := convPow_diff hH' hH (hdiff φ hφ) (j + 2)
    have hlog : ∀ y : E, ‖y‖ ≤ R → |log (LLT.convPow (Hd K φ) (j + 2) y) -
        log (LLT.convPow (Hd K ψ) (j + 2) y)| ≤ (j + 2 + 1 : ℝ) * (CH * dist φ ψ) / c0 :=
      fun y hy => by
      have a1 := hlow φ hφ y hy
      have a2 := hlow ψ hψ y hy
      refine (LLT.abs_log_sub_log_le (hc0.trans_le a1) (hc0.trans_le a2)).trans ?_
      have := hcv y
      push_cast at this
      exact div_le_div₀ (by positivity) this hc0 (le_min a1 a2)
    have hb : dist (PsiMap K j φ) (PsiMap K j ψ) ≤ L * dist φ ψ := by
      refine (BoundedContinuousFunction.dist_le (mul_nonneg hL dist_nonneg)).2 fun p => ?_
      rw [PsiMap_apply (hcont φ hφ), PsiMap_apply (hcont ψ hψ), Fn, Fn, Real.dist_eq]
      have t1 := abs_le.1 (hlog 0 h0R)
      have t2 := abs_le.1 (hlog _ (hnorm p))
      have hLe : L * dist φ ψ = 2 * ((j + 2 + 1 : ℝ) * (CH * dist φ ψ) / c0) := by
        rw [hLdef]; ring
      rw [hLe, abs_le]
      constructor <;> linarith [t1.1, t1.2, t2.1, t2.2]
    calc dist (PsiMap K j φ) (PsiMap K j ψ) ≤ L * dist φ ψ := hb
      _ ≤ L * (e / (L + 1)) := mul_le_mul_of_nonneg_left hd.le hL
      _ < e := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨ψ, hψ, hfix⟩ := hS (K →ᵇ ℝ) (Cset K) (PsiMap K j) isCompact_Cset convex_Cset
    ⟨0, zero_mem_Cset⟩ hcontOn hmaps
  -- the fixed point gives the complete mix
  have hH := Hd_inH hB hv₀ hρ hψ
  have hZ := Zt_pos hB hv₀ hρ hψ
  set c := LLT.convPow (Hd K ψ) (j + 2)
  have hc00 : 0 < c 0 := hc0.trans_le (hlow ψ hψ 0 h0R)
  have hn0 := hpos3 ψ hψ
  refine LLT.completelyMixable_of_marg hH hB.meas hB.bdd (hB.ne0 hv₀) hB.cen
    (fun p hp => Hd_of_not_mem hp) (j + 1) hn0
    (log (c 0 / (Zt K ψ * LLT.convPow (Hd K ψ) (j + 3) 0))) (tv K ψ) fun p hp => ?_
  have hcp : 0 < c (-p) := hc0.trans_le (hlow ψ hψ _ (by rw [norm_neg]; exact hB.bdd p hp))
  have hψp : ψ ⟨p, hp⟩ = log (c 0) - log (c (-p)) := by
    have := congrArg (fun f : K →ᵇ ℝ => f ⟨p, hp⟩) hfix
    rw [← this]; exact PsiMap_apply (hcont ψ hψ) _
  show Hd K ψ p * c (-p) / LLT.convPow (Hd K ψ) (j + 3) 0 = _
  rw [exp_add, exp_log (div_pos hc00 (mul_pos hZ hn0)), Hd_eq, gE_of_mem hp, hψp, exp_sub,
    exp_log hc00, exp_log hcp]
  field_simp

/-- **Theorem 104 for a class of centred bodies** (canonical volume), given Schauder's theorem:
for convex bodies with `|K| ∈ [v₀, v₁]`, `K ⊆ B(0, R)`, `B(0, ρ) ⊆ K`, centroid `0`, covariance of
`U(K)` at least `σ I` and a uniform Fourier gap, there is `N` such that `U(K)` is
`n`-completely mixable for all `n ≥ N` and all bodies of the class. -/
theorem thm104_centred (hS : SchauderFPT.{u}) (𝒦 : Set (Set E)) (hv₀ : 0 < v₀) (hρ : 0 < ρ)
    (hσ : 0 < σ) (hd : 1 ≤ Module.finrank ℝ E) (hK : ∀ K ∈ 𝒦, Body v₀ v₁ R ρ σ K)
    (hgap : ∀ r > 0, ∃ q < 1, ∀ K ∈ 𝒦, ∀ ξ : E, r ≤ ‖ξ‖ → ‖charFun (unifSet K) ξ‖ ≤ q) :
    ∃ N : ℕ, ∀ K ∈ 𝒦, ∀ n, N ≤ n → CompletelyMixable n (unifSet K) := by
  rcases 𝒦.eq_empty_or_nonempty with he | ⟨K₀, hK₀⟩
  · exact ⟨0, fun K hK' => by simp [he] at hK'⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hR : 0 < R := by
    obtain ⟨x, hx⟩ := exists_norm_eq E hρ.le
    have := (hK K₀ hK₀).bdd x ((hK K₀ hK₀).ball (by
      rw [Metric.mem_closedBall, dist_zero_right, hx]))
    linarith
  set A := A1 E v₁ R ρ
  set M := exp A / v₀
  set σ1 := exp (-A) * σ
  have hσ1 : 0 < σ1 := by positivity
  set 𝓗 : Set (E → ℝ) := {h | ∃ K ∈ 𝒦, ∃ ψ ∈ Cset K, h = Hd K ψ}
  have hH : ∀ h ∈ 𝓗, LLT.InH M R σ1 h := by
    rintro h ⟨K, hK', ψ, hψ, rfl⟩; exact Hd_inH (hK K hK') hv₀ hρ hψ
  have hgapH : ∀ r > 0, ∃ q < 1, ∀ h ∈ 𝓗, ∀ ξ : E, r ≤ ‖ξ‖ → ‖LLT.hatC h ξ‖ ≤ q := by
    intro r hr
    obtain ⟨q, hq, hq'⟩ := hgap (2 * π * r) (by positivity)
    have ha : 0 < exp (-A) := exp_pos _
    refine ⟨1 - exp (-A) + exp (-A) * q, by nlinarith, ?_⟩
    rintro h ⟨K, hK', ψ, hψ, rfl⟩ ξ hξ
    refine (Hd_gap (hK K hK') hv₀ hρ hψ ξ).trans ?_
    have : 2 * π * r ≤ ‖-(2 * π) • ξ‖ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hξ (by positivity : (0 : ℝ) ≤ 2 * π)
    have := hq' K hK' _ this
    nlinarith
  set D := M * (1 + V0 E v₁ ρ) * v₁ + 2 * M * Module.finrank ℝ E * v₁ / ρ
  have hD : ∀ h ∈ 𝓗, ∀ y y' : E, ∫ z, |h (y - z) - h (y' - z)| ≤ D * ‖y - y'‖ := by
    rintro h ⟨K, hK', ψ, hψ, rfl⟩ y y'
    exact Hd_l1 (hK K hK') hv₀ hρ hd hψ y y'
  set ε := min 1 (1 / R)
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεR : ε * R ≤ 1 := by
    calc ε * R ≤ 1 / R * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
      _ = 1 := by field_simp
  obtain ⟨N1, hN1⟩ := LLT.lip_log_convPow hR hσ1 hH hgapH hD R ε hε0
  have hg0 : 0 < LLT.g0 E R := by unfold LLT.g0; positivity
  obtain ⟨N2, hN2⟩ := LLT.approx_center hR hσ1 hH hgapH R (LLT.g0 E R / 2) (by positivity)
  refine ⟨N1 + N2 + 3, fun K hK' n hn => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hm1 : N1 ≤ j + 2 := by omega
  have hm2 : N2 ≤ j + 2 := by omega
  set s := Real.sqrt ((j + 2 : ℕ) : ℝ) ^ Module.finrank ℝ E
  have hs : 0 < s := pow_pos (Real.sqrt_pos.2 (by positivity)) _
  refine cm_of_body hS (hK K hK') hv₀ hρ hσ j hε0.le hε1 hεR (c0 := LLT.g0 E R / 2 / s)
    (by positivity) (fun ψ hψ y hy => ?_) (fun ψ hψ y y' hy hy' => ?_) (fun ψ hψ => ?_)
  · have hmem : Hd K ψ ∈ 𝓗 := ⟨K, hK', ψ, hψ, rfl⟩
    have h1 := hN2 (j + 2) hm2 _ hmem y hy
    have h2 : LLT.g0 E R ≤ LLT.gaussD (Hd K ψ) 0 := LLT.gaussD_zero_ge (hH _ hmem) hR hσ1
    rw [div_le_iff₀ hs, mul_comm]
    have := (abs_le.1 h1).1
    linarith
  · exact (hN1 (j + 2) hm1 _ ⟨K, hK', ψ, hψ, rfl⟩ y y' hy hy').2
  · exact (hN1 (j + 3) (by omega) _ ⟨K, hK', ψ, hψ, rfl⟩ 0 0 (by simp [hR.le])
      (by simp [hR.le])).1

lemma affE_refl_apply (t x : E) :
    Large.affE (ContinuousLinearEquiv.refl ℝ E) t x = x + t := by simp [Large.affE_apply]

lemma unifSet_tr (K : Set E) (c : E) :
    unifSet (Large.affE (ContinuousLinearEquiv.refl ℝ E) (-c) '' K) =
      (unifSet K).map (fun y => y + -c) := by
  have h := Large.unifSet_map_affE (ContinuousLinearEquiv.refl ℝ E) (-c) K
  rw [← h, Measure.map_map (by fun_prop) (Large.affE _ _).measurable]
  have e : ((fun y => y + -c) ∘ Large.affE (ContinuousLinearEquiv.refl ℝ E).symm
      (-(ContinuousLinearEquiv.refl ℝ E).symm (-c))) = id := by
    funext y; simp [Large.affE_apply]
  rw [e, Measure.map_id]

lemma isProb_unifSet {K : Set E} (h0 : volume K ≠ 0) (ht : volume K ≠ ⊤) :
    IsProbabilityMeasure (unifSet K) :=
  ⟨by rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]⟩

/-- **Theorem 104 with constants tracked** (`Large.Thm104T`) for the canonical volume of `E`,
`dim E ≥ 1`, given Schauder's fixed point theorem. -/
theorem thm104T_can (hS : SchauderFPT.{u}) (hd : 1 ≤ Module.finrank ℝ E) : Large.Thm104T E := by
  intro 𝒦 v₀ v₁ R ρ σ hv₀ hρ hσ hK hgap
  set L := ContinuousLinearEquiv.refl ℝ E
  set T : Set E → Set E := fun K => Large.affE L (-Large.cent K) '' K
  have hTmem : ∀ K : Set E, ∀ z, z ∈ T K ↔ z + Large.cent K ∈ K := fun K z =>
    ⟨by rintro ⟨y, hy, rfl⟩; simpa [L, affE_refl_apply] using hy,
      fun h => ⟨z + Large.cent K, h, by simp [L]⟩⟩
  have hjac : Large.jac L = 1 := by simp [Large.jac, L]
  have hbody : ∀ K' ∈ T '' 𝒦, Body v₀ v₁ R ρ σ K' := by
    rintro _ ⟨K, hK', rfl⟩
    obtain ⟨hKc, hKconv, hlo, hhi, hbdd, hball, hvar⟩ := hK K hK'
    set c := Large.cent K
    have hvol : volume.real (T K) = volume.real K := by
      rw [Large.volume_image_affE, hjac, one_mul]
    have hK0 : volume K ≠ 0 := by
      intro h; rw [measureReal_def, h] at hlo; simp at hlo; linarith
    have hKt : volume K ≠ ⊤ := hKc.measure_lt_top.ne
    have := isProb_unifSet hK0 hKt
    have hU : unifSet (T K) = (unifSet K).map (fun y => y + -c) := unifSet_tr K c
    have hmap : AEMeasurable (fun y : E => y + -c) (unifSet K) := by fun_prop
    refine ⟨hKc.image (show Continuous (Large.affE L (-c)) from
      L.continuous.add continuous_const), Large.convex_affE_image L (-c) hKconv,
      hvol ▸ hlo, hvol ▸ hhi, fun z hz => ?_, fun z hz => ?_, ?_, fun e he => ?_⟩
    · have := hbdd _ ((hTmem K z).1 hz); simpa [c] using this
    · refine (hTmem K z).2 (hball ?_)
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    · have hint : Integrable (fun y : E => y) (unifSet K) := by
        rw [unifSet]
        exact (continuous_id.continuousOn.integrableOn_compact hKc).smul_measure
          (ENNReal.inv_ne_top.2 hK0)
      have h1 : ∫ y, y ∂(unifSet (T K)) = 0 := by
        rw [hU, integral_map hmap (by fun_prop), integral_add hint (integrable_const _),
          integral_const, ← Large.cent_eq_integral_unifSet]
        simp [c]
      have h2 : ∫ y, y ∂(unifSet (T K)) = (volume.real (T K))⁻¹ • ∫ y in T K, y := by
        rw [unifSet, integral_smul_measure, ENNReal.toReal_inv]; rfl
      rw [h2] at h1
      have hpos : volume.real (T K) ≠ 0 := by rw [hvol]; linarith
      exact (smul_eq_zero.1 h1).resolve_left (inv_ne_zero hpos)
    · rw [hU, integral_map hmap (by fun_prop)]
      simpa [sub_eq_add_neg] using hvar e he
  have hgapT : ∀ r > 0, ∃ q < 1, ∀ K' ∈ T '' 𝒦, ∀ ξ : E, r ≤ ‖ξ‖ →
      ‖charFun (unifSet K') ξ‖ ≤ q := by
    intro r hr
    obtain ⟨q, hq, h⟩ := hgap r hr
    refine ⟨q, hq, ?_⟩
    rintro _ ⟨K, hK', rfl⟩ ξ hξ
    rw [unifSet_tr, charFun_map_add_const, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact h K hK' ξ hξ
  obtain ⟨N, hN⟩ := thm104_centred hS (T '' 𝒦) hv₀ hρ hσ hd hbody hgapT
  · refine ⟨N, fun K hK' n hn => ?_⟩
    obtain ⟨P, hP⟩ := hN (T K) ⟨K, hK', rfl⟩ n hn
    have h := Large.isCompleteMix_affE hP L.symm (-L.symm (-Large.cent K))
    simp only [T] at h
    rw [Large.unifSet_map_affE] at h
    exact ⟨_, h⟩

end FixedPoint

section Final

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

lemma cent_eq_can (K : Set E) :
    Large.cent K = @Large.cent E _ _ measureSpaceOfInnerProductSpace K := by
  rw [Large.cent_eq_integral_unifSet,
    @Large.cent_eq_integral_unifSet E _ _ _ measureSpaceOfInnerProductSpace _ _, unifSet_eq_can]

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- In a zero-dimensional space every probability measure is `n`-completely mixable. -/
lemma cm_subsingleton [Subsingleton E] (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    CompletelyMixable n μ := by
  have hm : Measurable fun x : E => fun _ : Fin n => x := by fun_prop
  refine ⟨μ.map fun x => fun _ => x, inferInstance,
    ⟨0, ae_of_all _ fun x => Subsingleton.elim _ _⟩, fun j => ?_⟩
  rw [Measure.map_map (measurable_pi_apply j) hm]
  exact Measure.map_id

/-- **Theorem 104 with its constants tracked** (`Large.Thm104T`, the hypothesis of
`Large.cor105`), proved from Schauder's fixed point theorem (`SchauderFPT`), for any additive
Haar measure as `volume`. -/
theorem thm104T (hS : SchauderFPT.{u}) : Large.Thm104T E := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hd | hd
  · have : Subsingleton E := Module.finrank_zero_iff.1 hd
    intro 𝒦 v₀ v₁ R ρ σ hv₀ _ _ hK _
    refine ⟨0, fun K hK' n _ => ?_⟩
    obtain ⟨hKc, -, hlo, -⟩ := hK K hK'
    have h0 : volume K ≠ 0 := by
      intro h; rw [measureReal_def, h] at hlo; simp at hlo; linarith
    have : IsProbabilityMeasure (unifSet K) :=
      ⟨by rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel h0 hKc.measure_lt_top.ne]⟩
    exact cm_subsingleton _ n
  intro 𝒦 v₀ v₁ R ρ σ hv₀ hρ hσ hK hgap
  obtain ⟨c, hc, hvol⟩ := measureReal_eq_can (E := E)
  have key := thm104T_can (E := E) hS hd 𝒦 (v₀ / c) (v₁ / c) R ρ σ (div_pos hv₀ hc) hρ hσ
  simp only [← cent_eq_can, ← unifSet_eq_can] at key
  refine key (fun K hK' => ?_) hgap
  obtain ⟨hKc, hconv, hlo, hhi, hbdd, hball, hvar⟩ := hK K hK'
  rw [hvol K] at hlo hhi
  exact ⟨hKc, hconv, (div_le_iff₀ hc).2 (by linarith), (le_div_iff₀ hc).2 (by linarith), hbdd,
    hball, hvar⟩

/-- **Corollary 105** (`lg:cor:uniform`) with only John's theorem and Schauder's fixed point
theorem as hypotheses: in dimension `d ≥ 1` there is `N_d` such that the uniform distribution
on every convex body is `n`-completely mixable for every `n ≥ N_d`. -/
theorem cor105_full (hJ : Large.JohnThm E) (hS : SchauderFPT.{u})
    (hd : 0 < Module.finrank ℝ E) :
    ∃ N : ℕ, ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∀ n, N ≤ n → CompletelyMixable n (unifSet K) :=
  Large.cor105 hJ (thm104T hS) fourierGapJohn hd

end Final

end Mixes.LLTB
