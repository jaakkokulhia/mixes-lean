import Mixes.PolyB
import Mixes.ConeMix
import Mixes.PrekopaLeindler

/-!
# Corollary 96 (d) with the triangle, square and hexagon discharged

`PolyB.cor96d_poly` (Corollary 96 (d), `st:cor:poly`) takes the triangle, the square and the
hexagon as hypotheses `htri`, `hsq`, `hhex`. Here they are proved for the concrete polygons
`PolyB.poly 3`, `poly 4`, `poly 6`:

* the triangle and the square are affine images of trapezoids in normal form, so Theorem 40
  (`Assembly.completelyMixable_trapSet`, `Assembly.completelyMixable_trapAbsc`, unconditional) and
  the affine invariance `ConeMix.completelyMixable_image_equiv` give all `n ≥ 3`;
* the hexagon is invariant under the rotation of order `3`, which gives `n = 3` (Remark 81,
  `Poly.completelyMixable_of_rest` as in `PolyB.cm_self`); `n = 2` holds by central symmetry
  (`PolyB.completelyMixable_two_iff_even`), and `4 = 2 + 2`, `5 = 2 + 3` (Remark 81).

Two of the floating-point constants of Section 25 have closed forms, proved here:
`a₄(1) = λ₃(1) = 3π²/4 - 4` (`aF_one_one`, by polar coordinates about the point `1`) and
`c₄ = λ₄(0) = ∫ λ₂² = π³ - 16π/3` (`aF_two_zero`), which give `aF11_ge : 3.398 ≤ aF 1 1` and
`aF20_le : aF 2 0 ≤ 14.252`. Prékopa–Leindler is `PrekopaLeindler.plHyp`.

Main results: `tri_cm`, `sq_cm`, `hex_cm`, `small_iff` (unconditional); `cor96d_from_cond(_iff)`
(Corollary 96 (d) for all `k ≥ 3`, under the four remaining floating-point bounds on
`a₄(sec π/8)`, `a₄(sec π/9)`, `a₅(1)`, `a₅(sec π/9)`, the corner bound for `k = 7` and the four
Table 15 cases); `cor96d_noc(_iff)` (`k ≥ 8` and `k = 3, 4, 6`, under the four floating-point
bounds only). The `_of` variants keep `PLHyp`, `a₄(1)` and `c₄` as hypotheses.
-/

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Mixes

namespace Poly96

open PolyB

lemma re_conj_nrm (z : ℂ) (k j : ℕ) :
    (z * (starRingEnd ℂ) (nrm k j)).re =
      z.re * cos (2 * π * j / k) + z.im * sin (2 * π * j / k) := by
  rw [nrm_eq_ee, re_mul_conj_ee]; simp

/-! ### The triangle -/

lemma mem_poly3 (z : ℂ) : z ∈ poly 3 ↔
    z.re ≤ 1 ∧ -z.re / 2 + √3 / 2 * z.im ≤ 1 ∧ -z.re / 2 - √3 / 2 * z.im ≤ 1 := by
  have c1 : cos (2 * π * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = -1 / 2 := by
    rw [show 2 * π * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = π - π / 3 by push_cast; ring, cos_pi_sub,
      cos_pi_div_three]; ring
  have s1 : sin (2 * π * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = √3 / 2 := by
    rw [show 2 * π * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = π - π / 3 by push_cast; ring, sin_pi_sub,
      sin_pi_div_three]
  have c2 : cos (2 * π * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = -1 / 2 := by
    rw [show 2 * π * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = π / 3 + π by push_cast; ring, cos_add_pi,
      cos_pi_div_three]; ring
  have s2 : sin (2 * π * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = -(√3 / 2) := by
    rw [show 2 * π * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = π / 3 + π by push_cast; ring, sin_add_pi,
      sin_pi_div_three]
  have c0 : cos (2 * π * ((0 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 1 := by simp
  have s0 : sin (2 * π * ((0 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 0 := by simp
  simp only [poly, mem_ofPred_eq, re_conj_nrm]
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    rw [c0, s0] at h0; rw [c1, s1] at h1; rw [c2, s2] at h2
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c⟩ j hj
    interval_cases j
    · rw [c0, s0]; linarith
    · rw [c1, s1]; linarith
    · rw [c2, s2]; linarith

/-- The linear part of the affine map from the normal-form triangle onto `P_3`. -/
def triLE : (ℝ × ℝ) ≃ₗ[ℝ] ℂ where
  toFun p := ⟨3 * p.1, √3 * (2 * p.2 - p.1)⟩
  invFun z := (z.re / 3, (z.im / √3 + z.re / 3) / 2)
  map_add' p q := by apply Complex.ext <;> simp <;> ring
  map_smul' c p := by apply Complex.ext <;> simp <;> ring
  left_inv p := by
    have hs : (√3 : ℝ) ≠ 0 := by positivity
    ext
    · simp
    · simp
  right_inv z := by
    have hs : (√3 : ℝ) ≠ 0 := by positivity
    apply Complex.ext
    · simp; ring
    · simp; field_simp; ring

lemma tri_image :
    (fun x => triLE.toContinuousLinearEquiv x + (-2 : ℂ)) '' Assembly.trapSet 0 0 0 = poly 3 := by
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √3 := by positivity
  ext z
  rw [mem_poly3]
  simp only [mem_image, Assembly.trapSet, trapH, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx0, hx1, hy0, hy1⟩, rfl⟩
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat] at *
    simp only [triLE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at *
    refine ⟨by linarith, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨a, b, c⟩
    refine ⟨((z.re + 2) / 3, (√3 * z.im / 3 + (z.re + 2) / 3) / 2), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · nlinarith
    · linarith
    · nlinarith
    · nlinarith
    · simp only [LinearEquiv.coe_toContinuousLinearEquiv', triLE, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk]
      apply Complex.ext <;> simp
      · ring
      · linear_combination (z.im / 3) * hs3

/-- **The triangle** (Theorem 40 / Corollary 44): `U(P_3)` is `n`-completely mixable for every
`n ≥ 3`. -/
theorem tri_cm {n : ℕ} (hn : 3 ≤ n) : CompletelyMixable n (unifSet (poly 3)) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h := Assembly.completelyMixable_trapSet le_rfl zero_le_one hn 0 0
    (Assembly.completelyMixable_trapAbsc hn le_rfl zero_le_one)
  have h2 := ConeMix.completelyMixable_image_equiv h triLE.toContinuousLinearEquiv (-2)
  rwa [tri_image] at h2

/-! ### The square -/

lemma mem_poly4 (z : ℂ) : z ∈ poly 4 ↔ z.re ≤ 1 ∧ z.im ≤ 1 ∧ -z.re ≤ 1 ∧ -z.im ≤ 1 := by
  have c1 : cos (2 * π * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 0 := by
    rw [show 2 * π * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = π / 2 by push_cast; ring, cos_pi_div_two]
  have s1 : sin (2 * π * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 1 := by
    rw [show 2 * π * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = π / 2 by push_cast; ring, sin_pi_div_two]
  have c2 : cos (2 * π * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = -1 := by
    rw [show 2 * π * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = π by push_cast; ring, cos_pi]
  have s2 : sin (2 * π * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 0 := by
    rw [show 2 * π * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = π by push_cast; ring, sin_pi]
  have c3 : cos (2 * π * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 0 := by
    rw [show 2 * π * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = π / 2 + π by push_cast; ring, cos_add_pi,
      cos_pi_div_two]; ring
  have s3 : sin (2 * π * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = -1 := by
    rw [show 2 * π * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = π / 2 + π by push_cast; ring, sin_add_pi,
      sin_pi_div_two]
  have c0 : cos (2 * π * ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 1 := by simp
  have s0 : sin (2 * π * ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 0 := by simp
  simp only [poly, mem_ofPred_eq, re_conj_nrm]
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    rw [c0, s0] at h0; rw [c1, s1] at h1; rw [c2, s2] at h2; rw [c3, s3] at h3
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c, d⟩ j hj
    interval_cases j
    · rw [c0, s0]; linarith
    · rw [c1, s1]; linarith
    · rw [c2, s2]; linarith
    · rw [c3, s3]; linarith

/-- The linear part of the affine map from the unit square onto `P_4`. -/
def sqLE : (ℝ × ℝ) ≃ₗ[ℝ] ℂ where
  toFun p := ⟨2 * p.1, 2 * p.2⟩
  invFun z := (z.re / 2, z.im / 2)
  map_add' p q := by apply Complex.ext <;> simp <;> ring
  map_smul' c p := by apply Complex.ext <;> simp <;> ring
  left_inv p := by ext <;> simp
  right_inv z := by apply Complex.ext <;> simp <;> ring

lemma sq_image :
    (fun x => sqLE.toContinuousLinearEquiv x + (⟨-1, -1⟩ : ℂ)) '' Assembly.trapSet 1 0 0 =
      poly 4 := by
  ext z
  rw [mem_poly4]
  simp only [mem_image, Assembly.trapSet, trapH, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx0, hx1, hy0, hy1⟩, rfl⟩
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', sqLE, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, Complex.add_re, Complex.add_im] at *
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c, d⟩
    refine ⟨((z.re + 1) / 2, (z.im + 1) / 2), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
    · simp only [LinearEquiv.coe_toContinuousLinearEquiv', sqLE, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk]
      apply Complex.ext <;> simp <;> ring

/-- **The square** (Theorem 40, or Lemma 50): `U(P_4)` is `n`-completely mixable for every
`n ≥ 3`. -/
theorem sq_cm {n : ℕ} (hn : 3 ≤ n) : CompletelyMixable n (unifSet (poly 4)) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h := Assembly.completelyMixable_trapSet zero_le_one le_rfl hn 0 0
    (Assembly.completelyMixable_trapAbsc hn zero_le_one le_rfl)
  have h2 := ConeMix.completelyMixable_image_equiv h sqLE.toContinuousLinearEquiv ⟨-1, -1⟩
  rwa [sq_image] at h2

/-! ### The hexagon -/

lemma nrm3_eq : nrm 3 1 = nrm 6 2 := by
  unfold nrm; congr 3; push_cast; ring

/-- The rotation of order `3` gives a `3`-complete mix of `U(P_6)` (Remark 81). -/
theorem hex_three : CompletelyMixable 3 (unifSet (poly 6)) := by
  have hk0 : 0 < 6 := by norm_num
  have hLK : (rot (nrm 3 1)) ⁻¹' poly 6 = poly 6 := by
    ext z; simp [rot_apply, nrm3_eq, mul_nrm_mem_poly hk0]
  refine Poly.completelyMixable_of_rest (by norm_num) (rot (nrm 3 1)) (rot_pow_eq_one (by norm_num))
    (rot_fix (by norm_num)) (isCompact_poly (by norm_num)) (volume_poly_pos 6)
    (centroid_poly (by norm_num))
    subset_rfl (fun x hx => by simpa [rot_apply, nrm3_eq, mul_nrm_mem_poly hk0] using hx) 0
    (fun σ => Measure.map_zero _) (by simp) (Mixes.unifSet (poly 6))
    (Room.unifSet_compl (measurableSet_poly 6))
    (Room.unifSet_map _ (measurePreserving_rot norm_nrm).map_eq (measurableSet_poly 6) hLK) ?_
  ext S hS
  simp [Room.marginal]

/-- **The hexagon**: `U(P_6)` is `n`-completely mixable for every `n ≥ 2`. -/
theorem hex_cm {n : ℕ} (hn : 2 ≤ n) : CompletelyMixable n (unifSet (poly 6)) := by
  have h2 : CompletelyMixable 2 (unifSet (poly 6)) :=
    (completelyMixable_two_iff_even (by norm_num)).2 (by decide)
  have h4 : CompletelyMixable 4 (unifSet (poly 6)) := ScaledB.completelyMixable_add_add h2 h2
  have h5 : CompletelyMixable 5 (unifSet (poly 6)) := ScaledB.completelyMixable_add_add h2 hex_three
  rcases (show n = 2 ∨ 3 ≤ n by omega) with h | h
  · subst h; exact h2
  · exact Poly.all_of_three_four_five hex_three h4 h5 n h

/-! ### Two of the floating-point constants in closed form: `a₄(1)` and `c₄` -/

/-- The antiderivative of `r ↦ r · lens r`. -/
def Hf (r : ℝ) : ℝ := (r ^ 2 - 1) * arccos (r / 2) - √(4 - r ^ 2) * (r ^ 3 + 2 * r) / 8

lemma hasDerivAt_Hf {r : ℝ} (h0 : 0 < r) (h1 : r < 2) : HasDerivAt Hf (r * Poly.lens r) r := by
  have hpos : 0 < 4 - r ^ 2 := by nlinarith
  have hq : √(1 - (r / 2) ^ 2) = √(4 - r ^ 2) / 2 := by
    rw [show 4 - r ^ 2 = 2 ^ 2 * (1 - (r / 2) ^ 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]; ring
  have hs : 0 < √(4 - r ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : √(4 - r ^ 2) ^ 2 = 4 - r ^ 2 := Real.sq_sqrt hpos.le
  have hA := (Real.hasDerivAt_arccos (x := r / 2) (by linarith) (by linarith)).comp r
    ((hasDerivAt_id' r).div_const 2)
  have h := (((hasDerivAt_pow 2 r).sub_const 1).mul hA).sub
    (((((hasDerivAt_pow 2 r).const_sub 4).sqrt hpos.ne').mul
      ((hasDerivAt_pow 3 r).add ((hasDerivAt_id' r).const_mul 2))).div_const 8)
  convert h using 1
  · funext x
    simp only [Hf, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Function.comp_apply]
  simp only [Function.comp_apply, Pi.add_apply]
  rw [hq, Mixes.Poly.lens]
  field_simp
  push_cast; ring_nf; rw [hsq]; ring

lemma continuous_Hf : Continuous Hf := by
  unfold Hf
  exact ((continuous_pow 2).sub continuous_const).mul
    (Real.continuous_arccos.comp (continuous_id.div_const 2)) |>.sub
    ((((continuous_const.sub (continuous_pow 2)).sqrt).mul
      ((continuous_pow 3).add (continuous_const.mul continuous_id))).div_const 8)

lemma continuous_rlens : Continuous fun r : ℝ => r * Poly.lens r := by
  unfold Poly.lens; fun_prop

lemma integral_rlens {c : ℝ} (h0 : 0 ≤ c) (h2 : c ≤ 2) :
    ∫ r in (0 : ℝ)..c, r * Poly.lens r = Hf c - Hf 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0 continuous_Hf.continuousOn
    (fun r hr => hasDerivAt_Hf hr.1 (by linarith [hr.2])) (continuous_rlens.intervalIntegrable _ _)

lemma Hf_sub_nonneg {c : ℝ} (h0 : 0 ≤ c) (h2 : c ≤ 2) : 0 ≤ Hf c - Hf 0 := by
  rw [← integral_rlens h0 h2]
  exact intervalIntegral.integral_nonneg h0 fun r hr =>
    mul_nonneg hr.1 (lens_nonneg hr.1 (by linarith [hr.2]))

open Complex in
lemma norm_one_sub_polar_le {ρ θ : ℝ} (hρ : 0 < ρ) :
    ‖1 - (ρ : ℂ) * cexp (θ * I)‖ ≤ 1 ↔ ρ ≤ 2 * Real.cos θ := by
  have key : ‖1 - (ρ : ℂ) * cexp (θ * I)‖ ^ 2 = 1 - 2 * ρ * Real.cos θ + ρ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ
  have hn := norm_nonneg (1 - (ρ : ℂ) * cexp (θ * I))
  constructor
  · intro h
    have : ‖1 - (ρ : ℂ) * cexp (θ * I)‖ ^ 2 ≤ 1 := by nlinarith
    rw [key] at this; nlinarith
  · intro h
    have : ‖1 - (ρ : ℂ) * cexp (θ * I)‖ ^ 2 ≤ 1 := by rw [key]; nlinarith
    nlinarith

/-- The polar integrand. -/
def gP (p : ℝ × ℝ) : ℝ≥0∞ :=
  if p.1 ≤ 2 * Real.cos p.2 then ENNReal.ofReal (p.1 * Poly.lens p.1) else 0

lemma measurable_gP : Measurable gP := by
  unfold gP
  refine Measurable.ite (measurableSet_le measurable_fst
    ((Real.continuous_cos.measurable.comp measurable_snd).const_mul 2)) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp (continuous_rlens.measurable.comp measurable_fst)

/-- The radial integral at angle `θ`. -/
def Jt (θ : ℝ) : ℝ := Hf (max (2 * Real.cos θ) 0) - Hf 0

lemma continuous_Jt : Continuous Jt := by
  unfold Jt
  exact (continuous_Hf.comp ((continuous_const.mul Real.continuous_cos).max continuous_const)).sub
    continuous_const

lemma Jt_nonneg (θ : ℝ) : 0 ≤ Jt θ :=
  Hf_sub_nonneg (le_max_right _ _)
    (max_le (by linarith [Real.cos_le_one θ]) (by norm_num))

lemma inner_eq (θ : ℝ) : ∫⁻ ρ in Ioi (0 : ℝ), gP (ρ, θ) = ENNReal.ofReal (Jt θ) := by
  by_cases hc : 2 * Real.cos θ ≤ 0
  · have : Jt θ = 0 := by simp [Jt, max_eq_right hc]
    rw [this, ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) (fun ρ hρ => ?_)]
    · simp
    · simp only [gP]
      rw [ite_eq_right_iff.2 (fun h => absurd h (by have : (0 : ℝ) < ρ := hρ; linarith))]
  · push Not at hc
    set c := 2 * Real.cos θ with hcdef
    have hc2 : c ≤ 2 := by linarith [Real.cos_le_one θ]
    have hg : (fun ρ => gP (ρ, θ)) =
        (Iic c).indicator (fun ρ => ENNReal.ofReal (ρ * Poly.lens ρ)) := by
      funext ρ; simp only [gP, indicator, mem_Iic]; rfl
    rw [hg, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi, ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le
      hc.le, integral_rlens hc.le hc2, Jt, max_eq_left hc.le]
    · exact continuous_rlens.integrableOn_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      exact mul_nonneg hr.1.le (lens_nonneg hr.1.le (by linarith [hr.2]))

/-- An antiderivative of `Jt` on `[0, π/2]`. -/
def Kf (θ : ℝ) : ℝ :=
  θ ^ 2 / 2 + 2 * θ * Real.sin θ * Real.cos θ + Real.cos θ ^ 2 + Real.cos θ ^ 4 / 2 +
    Real.cos θ ^ 2 / 2 + π / 2 * θ

lemma hasDerivAt_Kf (θ : ℝ) : HasDerivAt Kf
    ((4 * Real.cos θ ^ 2 - 1) * θ - Real.sin θ * (2 * Real.cos θ ^ 3 + Real.cos θ) + π / 2) θ := by
  have hs := Real.hasDerivAt_sin θ
  have hc := Real.hasDerivAt_cos θ
  have e1 := (hasDerivAt_pow 2 θ).div_const 2
  have e2 := (((hasDerivAt_id' θ).const_mul 2).mul hs).mul hc
  have e3 := hc.pow 2
  have e4 := (hc.pow 4).div_const 2
  have e5 := (hc.pow 2).div_const 2
  have e6 := (hasDerivAt_id' θ).const_mul (π / 2)
  have h := ((((e1.add e2).add e3).add e4).add e5).add e6
  convert h using 1
  · funext x; simp only [Kf, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  · simp only [Pi.mul_apply]
    push_cast
    linear_combination (2 * θ) * Real.sin_sq_add_cos_sq θ

lemma Jt_eq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    Jt θ = (4 * Real.cos θ ^ 2 - 1) * θ - Real.sin θ * (2 * Real.cos θ ^ 3 + Real.cos θ) + π / 2 := by
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  have hsq : √(4 - (2 * Real.cos θ) ^ 2) = 2 * Real.sin θ := by
    rw [show 4 - (2 * Real.cos θ) ^ 2 = (2 * Real.sin θ) ^ 2 by
      linear_combination (-4 : ℝ) * Real.sin_sq_add_cos_sq θ, Real.sqrt_sq (by linarith)]
  have ha : arccos (2 * Real.cos θ / 2) = θ := by
    rw [show 2 * Real.cos θ / 2 = Real.cos θ by ring, Real.arccos_cos h0 (by linarith [pi_pos])]
  simp only [Jt, Hf, max_eq_left (by linarith : (0 : ℝ) ≤ 2 * Real.cos θ), hsq, ha]
  simp
  ring

lemma Jt_zero {θ : ℝ} (h0 : π / 2 ≤ θ) (h1 : θ ≤ π) : Jt θ = 0 := by
  have hc : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h0 (by linarith)
  simp [Jt, max_eq_right (by linarith : 2 * Real.cos θ ≤ 0)]

lemma integral_Jt : ∫ θ in (-π)..π, Jt θ = 3 * π ^ 2 / 4 - 4 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable Jt volume a b := fun a b =>
    continuous_Jt.intervalIntegrable a b
  have hneg : ∫ θ in (-π)..0, Jt θ = ∫ θ in (0 : ℝ)..π, Jt θ := by
    have : ∫ θ in (0 : ℝ)..π, Jt (-θ) = ∫ θ in (0 : ℝ)..π, Jt θ := by
      simp only [Jt, Real.cos_neg]
    rw [← this, intervalIntegral.integral_comp_neg, neg_zero]
  have hp : ∫ θ in (0 : ℝ)..π, Jt θ = 3 * π ^ 2 / 8 - 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (π / 2)) (hi (π / 2) π)]
    have h2 : ∫ θ in (π / 2)..π, Jt θ = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ hθ => ?_]
      · simp
      · rw [uIcc_of_le (by linarith [pi_pos])] at hθ
        exact Jt_zero hθ.1 hθ.2
    have h1 : ∫ θ in (0 : ℝ)..(π / 2), Jt θ = 3 * π ^ 2 / 8 - 2 := by
      rw [intervalIntegral.integral_congr (g := fun θ => (4 * Real.cos θ ^ 2 - 1) * θ -
          Real.sin θ * (2 * Real.cos θ ^ 3 + Real.cos θ) + π / 2) fun θ hθ => ?_]
      · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hasDerivAt_Kf θ)
          (by apply Continuous.intervalIntegrable; fun_prop)]
        simp only [Kf, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
        ring
      · rw [uIcc_of_le (by linarith [pi_pos])] at hθ
        exact Jt_eq hθ.1 hθ.2
    rw [h1, h2, add_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-π) 0) (hi 0 π), hneg, hp]
  ring

/-- `λ₃(1) = 3π²/4 - 4`. -/
theorem cp_two_one : cp 2 1 = ENNReal.ofReal (3 * π ^ 2 / 4 - 4) := by
  have step1 : cp 2 1 = ∫⁻ w, {w : ℂ | ‖1 - w‖ ≤ 1}.indicator
      (fun w => ENNReal.ofReal (Poly.lens ‖w‖)) w := by
    rw [cp_succ, ← lintegral_indicator (s := disc) measurableSet_closedBall,
      ← lintegral_sub_left_eq_self _ (1 : ℂ)]
    congr 1; funext w
    by_cases hw : ‖1 - w‖ ≤ 1
    · have h2 : ‖w‖ ≤ 2 := by
        have := norm_sub_le (1 : ℂ) (1 - w)
        simp only [sub_sub_cancel, norm_one] at this; linarith
      have hm : (1 : ℂ) - w ∈ disc := by simpa [disc] using hw
      rw [indicator_of_mem hm, indicator_of_mem (show w ∈ {w : ℂ | ‖1 - w‖ ≤ 1} from hw),
        sub_sub_cancel, cp_one_eq h2]
    · have hm : (1 : ℂ) - w ∉ disc := by simpa [disc] using hw
      rw [indicator_of_notMem hm, indicator_of_notMem (show w ∉ {w : ℂ | ‖1 - w‖ ≤ 1} from hw)]
  have step2 : ∫⁻ w, {w : ℂ | ‖1 - w‖ ≤ 1}.indicator
      (fun w => ENNReal.ofReal (Poly.lens ‖w‖)) w = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, gP p := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have h0 : 0 < p.1 := hp.1
    rw [p2_polar_symm]
    simp only [gP, indicator, mem_ofPred_eq, norm_one_sub_polar_le h0, p2_norm_polar,
      abs_of_pos h0]
    split_ifs
    · rw [smul_eq_mul, ← ENNReal.ofReal_mul h0.le]
    · simp
  have step3 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, gP p =
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (Jt θ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod_symm _ measurable_gP.aemeasurable]
    simp only [inner_eq]
  have step4 : ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (Jt θ) =
      ENNReal.ofReal (3 * π ^ 2 / 4 - 4) := by
    rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Jt]
    · exact (continuous_Jt.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · exact Filter.Eventually.of_forall fun θ => Jt_nonneg θ
  rw [step1, step2, step3, step4]

theorem aF_one_one : aF 1 1 = 3 * π ^ 2 / 4 - 4 := by
  have hp := pi_gt_three
  unfold aF
  rw [show (1 : ℕ) + 1 = 2 from rfl, cp_two_one, ENNReal.toReal_ofReal (by nlinarith)]

theorem aF11_ge : 3.398 ≤ aF 1 1 := by
  rw [aF_one_one]; have := pi_gt_d4; nlinarith

/-! ### `c₄ = λ₄(0) = π³ - 16π/3` -/

/-- `λ₂ = cp 1` as an explicit function. -/
def Lf (s : ℂ) : ℝ≥0∞ := {s : ℂ | ‖s‖ ≤ 2}.indicator (fun s => ENNReal.ofReal (Poly.lens ‖s‖)) s

lemma cp_one_eq_Lf (s : ℂ) : cp 1 s = Lf s := by
  by_cases h : ‖s‖ ≤ 2
  · rw [Lf, indicator_of_mem (show s ∈ {s : ℂ | ‖s‖ ≤ 2} from h), cp_one_eq h]
  · rw [Lf, indicator_of_notMem (show s ∉ {s : ℂ | ‖s‖ ≤ 2} from h),
      cp_one_eq_zero (not_le.1 h)]

lemma continuous_lens : Continuous Poly.lens := by unfold Poly.lens; fun_prop

lemma measurable_Lf : Measurable Lf := by
  unfold Lf
  exact (ENNReal.measurable_ofReal.comp (continuous_lens.comp continuous_norm).measurable).indicator
    (measurableSet_le continuous_norm.measurable measurable_const)

lemma cp_two_eq (y : ℂ) : cp 2 y = ∫⁻ s, disc.indicator 1 (y - s) * Lf s := by
  rw [cp_succ, ← lintegral_indicator (s := disc) measurableSet_closedBall,
    ← lintegral_sub_left_eq_self _ y]
  congr 1; funext s
  by_cases h : y - s ∈ disc
  · rw [indicator_of_mem h, indicator_of_mem h, sub_sub_cancel, cp_one_eq_Lf, Pi.one_apply,
      one_mul]
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

lemma cp_one_eq_int (s : ℂ) : cp 1 s = ∫⁻ y, disc.indicator 1 y * disc.indicator 1 (y - s) := by
  have hmeas : MeasurableSet {z : ℂ | ‖z‖ ≤ 1 ∧ ‖s - z‖ ≤ 1} :=
    (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le (continuous_const.sub continuous_id).norm.measurable measurable_const)
  rw [cp_one_eq_vol, ← lintegral_indicator_one hmeas]
  congr 1; funext y
  have e : ‖y - s‖ = ‖s - y‖ := norm_sub_rev _ _
  by_cases h1 : ‖y‖ ≤ 1 <;> by_cases h2 : ‖s - y‖ ≤ 1 <;>
    simp [indicator, disc, h1, h2, e]

lemma cp_three_zero_eq : cp 3 0 = ∫⁻ s, Lf s * Lf s := by
  have hm1 : Measurable (disc.indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_closedBall
  have hF : Measurable (Function.uncurry fun (y s : ℂ) =>
      disc.indicator 1 y * (disc.indicator 1 (y - s) * Lf s)) := by
    refine (hm1.comp measurable_fst).mul ((hm1.comp (measurable_fst.sub measurable_snd)).mul
      (measurable_Lf.comp measurable_snd))
  rw [cp_succ, ← lintegral_indicator (s := disc) measurableSet_closedBall]
  have h1 : ∀ y, disc.indicator (fun y => cp 2 (0 - y)) y =
      disc.indicator 1 y * ∫⁻ s, disc.indicator 1 (y - s) * Lf s := by
    intro y
    by_cases h : y ∈ disc
    · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, one_mul, zero_sub, cp_neg,
        cp_two_eq]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  rw [lintegral_congr h1]
  have hy : ∀ y, disc.indicator 1 y * ∫⁻ s, disc.indicator 1 (y - s) * Lf s =
      ∫⁻ s, disc.indicator 1 y * (disc.indicator 1 (y - s) * Lf s) := fun y =>
    (lintegral_const_mul _ ((hm1.comp (measurable_const.sub measurable_id)).mul measurable_Lf)).symm
  rw [lintegral_congr hy]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  congr 1; funext s
  simp_rw [← mul_assoc]
  have hz : ∫⁻ y, disc.indicator 1 y * disc.indicator 1 (y - s) * Lf s =
      (∫⁻ y, disc.indicator 1 y * disc.indicator 1 (y - s)) * Lf s :=
    lintegral_mul_const _ (hm1.mul (hm1.comp (measurable_id.sub measurable_const)))
  rw [hz, ← cp_one_eq_int, cp_one_eq_Lf]

/-- `u ↦ ∫ (u - sin u)² sin u du`. -/
def Af (u : ℝ) : ℝ :=
  -u ^ 2 * Real.cos u + 2 * u * Real.sin u + 2 * Real.cos u - u ^ 2 / 2 +
    u * Real.sin u * Real.cos u + (2 * Real.cos u ^ 2 - 1) / 4 - Real.cos u + Real.cos u ^ 3 / 3

lemma hasDerivAt_Af (u : ℝ) : HasDerivAt Af ((u - Real.sin u) ^ 2 * Real.sin u) u := by
  have hs := Real.hasDerivAt_sin u
  have hc := Real.hasDerivAt_cos u
  have hu := hasDerivAt_id' u
  have h := (((((((((hasDerivAt_pow 2 u).neg.mul hc).add ((hu.const_mul 2).mul hs)).add
    (hc.const_mul 2)).sub ((hasDerivAt_pow 2 u).div_const 2)).add ((hu.mul hs).mul hc)).add
    (((hc.pow 2).const_mul 2).sub_const 1 |>.div_const 4)).sub hc).add ((hc.pow 3).div_const 3))
  convert h using 1
  · funext x; simp only [Af, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
      Pi.sub_apply]
  · simp only [Pi.mul_apply, Pi.neg_apply]
    push_cast
    linear_combination (Real.sin u - u) * Real.sin_sq_add_cos_sq u

/-- The antiderivative of `ρ ↦ ρ · lens(ρ)²` on `[0, 2]`. -/
def Fh (ρ : ℝ) : ℝ := -Af (2 * arccos (ρ / 2))

lemma hasDerivAt_Fh {ρ : ℝ} (h0 : 0 < ρ) (h2 : ρ < 2) :
    HasDerivAt Fh (ρ * Poly.lens ρ ^ 2) ρ := by
  have hq : 0 < 1 - (ρ / 2) ^ 2 := by nlinarith
  have hw0 : 0 < √(1 - (ρ / 2) ^ 2) := Real.sqrt_pos.2 hq
  have hA := (Real.hasDerivAt_arccos (x := ρ / 2) (by linarith) (by linarith)).comp ρ
    ((hasDerivAt_id' ρ).div_const 2)
  simp only [Function.comp_def] at hA
  have hU := hA.const_mul 2
  have hAf := hasDerivAt_Af (2 * arccos (ρ / 2))
  have h0' := (HasDerivAt.comp (h := fun x => 2 * arccos (x / 2)) (h₂ := Af) ρ hAf hU).neg
  simp only [Function.comp_def] at h0'
  refine h0'.congr_deriv ?_
  have hsin : Real.sin (2 * arccos (ρ / 2)) = 2 * √(1 - (ρ / 2) ^ 2) * (ρ / 2) := by
    rw [Real.sin_two_mul, Real.sin_arccos, Real.cos_arccos (by linarith) (by linarith)]
  have h4 : √(4 - ρ ^ 2) = 2 * √(1 - (ρ / 2) ^ 2) := by
    rw [show 4 - ρ ^ 2 = 2 ^ 2 * (1 - (ρ / 2) ^ 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hlens : Poly.lens ρ = 2 * arccos (ρ / 2) - 2 * √(1 - (ρ / 2) ^ 2) * (ρ / 2) := by
    rw [Poly.lens, h4]; ring
  rw [hsin, hlens]
  generalize √(1 - (ρ / 2) ^ 2) = w at hw0 ⊢
  generalize arccos (ρ / 2) = a
  field_simp

lemma continuous_Fh : Continuous Fh := by
  unfold Fh Af
  have : Continuous fun ρ : ℝ => 2 * arccos (ρ / 2) :=
    continuous_const.mul (Real.continuous_arccos.comp (continuous_id.div_const 2))
  fun_prop

lemma integral_rlens_sq : ∫ ρ in (0 : ℝ)..2, ρ * Poly.lens ρ ^ 2 = π ^ 2 / 2 - 8 / 3 := by
  have hc : Continuous fun ρ : ℝ => ρ * Poly.lens ρ ^ 2 := by unfold Poly.lens; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_two continuous_Fh.continuousOn
    (fun ρ hρ => hasDerivAt_Fh hρ.1 hρ.2) (hc.intervalIntegrable _ _)]
  simp only [Fh, Af, show (2 : ℝ) / 2 = 1 by norm_num, show (0 : ℝ) / 2 = 0 by norm_num,
    Real.arccos_one, Real.arccos_zero, mul_zero, show 2 * (π / 2) = π by ring, Real.cos_pi,
    Real.sin_pi, Real.cos_zero, Real.sin_zero]
  ring

/-- `c₄ = λ₄(0) = π³ - 16π/3`. -/
theorem cp_three_zero : cp 3 0 = ENNReal.ofReal (π ^ 3 - 16 * π / 3) := by
  set g : ℝ → ℝ≥0∞ := (Iic (2 : ℝ)).indicator fun r => ENNReal.ofReal (r * Poly.lens r ^ 2)
    with hgdef
  have hc : Continuous fun r : ℝ => r * Poly.lens r ^ 2 := by unfold Poly.lens; fun_prop
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.comp hc.measurable).indicator measurableSet_Iic
  have step2 : ∫⁻ s, Lf s * Lf s = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g p.1 := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have h0 : 0 < p.1 := hp.1
    rw [p2_polar_symm]
    simp only [Lf, hgdef, indicator, mem_ofPred_eq, mem_Iic, p2_norm_polar, abs_of_pos h0]
    split_ifs with h2
    · have hl := lens_nonneg h0.le h2
      rw [smul_eq_mul, ← ENNReal.ofReal_mul hl, ← ENNReal.ofReal_mul h0.le]
      congr 1; ring
    · simp
  have step3 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g p.1 =
      (∫⁻ r in Ioi (0 : ℝ), g r) * ENNReal.ofReal (2 * π) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod (fun p : ℝ × ℝ => g p.1) (hg.comp measurable_fst).aemeasurable]
    simp only [setLIntegral_const, Real.volume_Ioo]
    rw [lintegral_mul_const _ hg]
    congr 2; ring
  have step4 : ∫⁻ r in Ioi (0 : ℝ), g r = ENNReal.ofReal (π ^ 2 / 2 - 8 / 3) := by
    rw [hgdef, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi, ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le
      zero_le_two, integral_rlens_sq]
    · exact hc.integrableOn_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      exact mul_nonneg hr.1.le (sq_nonneg _)
  rw [cp_three_zero_eq, step2, step3, step4, ← ENNReal.ofReal_mul]
  · congr 1; ring
  · have := pi_gt_three
    have : 0 < π * (π ^ 2 - 16 / 3) := mul_pos (by linarith) (by nlinarith)
    nlinarith

theorem aF_two_zero : aF 2 0 = π ^ 3 - 16 * π / 3 := by
  have hp := pi_gt_three
  unfold aF
  have : 0 < π * (π ^ 2 - 16 / 3) := mul_pos (by linarith) (by nlinarith)
  rw [show (2 : ℕ) + 1 = 3 from rfl, cp_three_zero, ENNReal.toReal_ofReal (by nlinarith)]

theorem aF20_le : aF 2 0 ≤ 14.252 := by
  rw [aF_two_zero]
  have h1 := pi_lt_d6
  have h2 := pi_gt_three
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 3.141593 - π) (by nlinarith : (0 : ℝ) < π ^ 2 + 3.141593 * π + 3.141593 ^ 2 - 16 / 3)]

/-! ### Corollary 96 (d) -/

lemma htri : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (unifSet (poly 3)) :=
  fun _ h => tri_cm (by omega)

lemma hsq : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (unifSet (poly 4)) :=
  fun _ h => sq_cm (by omega)

lemma hhex : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (unifSet (poly 6)) :=
  fun _ h => hex_cm (by omega)

/-- **Corollary 96 (d), `n ≥ 3`**, with the triangle, square and hexagon proved: every regular
polygon `P_k`, `k ≥ 3`, is `n`-completely mixable for every `n ≥ 3`, given Prékopa–Leindler
(`hPL`), the floating-point bounds on `a₄ = aF 1`, `a₅ = aF 2`, `c₄ = aF 2 0`, the corner-area
bound for `k = 7`, and the four Table 15 cases `(k, n) = (5,3), (5,4), (7,4), (7,5)`. -/
theorem cor96d_from_cond_of (hPL : PLHyp)
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Poly.secR 7 : ℂ) ∧ Cond22 2 7) :
    ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, 3 ≤ n → CompletelyMixable n (unifSet (poly k)) :=
  cor96d_poly hPL ha41 ha49 ha48 ha51 ha59 hc4u hcap h53 h54 h74 h75 htri hsq hhex

/-- **Corollary 96 (d), complete**, with the triangle, square and hexagon proved (hypotheses of
`cor96d_from_cond`): for `k ≥ 3`, `n ≥ 2`, `U(P_k)` is `n`-completely mixable iff `n ≥ 3` or
`k` is even. -/
theorem cor96d_from_cond_iff_of (hPL : PLHyp)
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Poly.secR 7 : ℂ) ∧ Cond22 2 7)
    {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (poly k)) ↔ 3 ≤ n ∨ Even k :=
  cor96d_poly_iff hPL ha41 ha49 ha48 ha51 ha59 hc4u hcap h53 h54 h74 h75 htri hsq hhex hk hn

/-- **Corollary 96 (d) without the Table 15 cases.** Given Prékopa–Leindler (`hPL`) and the
floating-point bounds on `a₄ = aF 1` (at `1`, `sec(π/8)`, `sec(π/9)`), `a₅ = aF 2` (at `1`,
`sec(π/9)`) and `c₄ = aF 2 0`, every regular polygon `P_k` with `k ≥ 8`, and the triangle, the
square and the hexagon, is `n`-completely mixable for every `n ≥ 3`. (The corner bound for
`k = 7` and condition (22) for `k = 5, 7` are not needed.) -/
theorem cor96d_noc_of (hPL : PLHyp)
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252) :
    ∀ k : ℕ, (8 ≤ k ∨ k = 3 ∨ k = 4 ∨ k = 6) →
      ∀ n : ℕ, 3 ≤ n → CompletelyMixable n (unifSet (poly k)) := by
  have hpi := pi_gt_three
  have hpi' := pi_lt_d2
  have hc3 := Poly.c3_le
  have hF00 : hF 0 0 = 1 := by simp [hF, cp_zero_zero]
  have aF00 : aF 0 0 = π := by
    simp only [aF, zero_add, cp_one_zero, ENNReal.toReal_ofReal pi_pos.le]
  have hF10 : hF 1 0 = π := by simp only [hF, cp_one_zero, ENNReal.toReal_ofReal pi_pos.le]
  have aF10 : aF 1 0 = π ^ 2 - 3 / 4 * √3 * π := by rw [c3_eq]; rfl
  have hF20 : hF 2 0 = π ^ 2 - 3 / 4 * √3 * π := by rw [c3_eq]; rfl
  have aF01 : aF 0 1 = Poly.lens 1 := by
    have := aF_zero_eq_lens (r := 1) zero_le_one one_le_two; simpa using this
  have hR2 : ∀ k, 3 ≤ k → Poly.secR k ≤ 2 := fun k hk => p2_secR_le_two hk
  have hR0 : ∀ k, 3 ≤ k → 0 ≤ Poly.secR k := fun k hk =>
    le_trans zero_le_one (Poly.one_le_secR hk)
  have aF0R : ∀ k, 3 ≤ k → aF 0 (Poly.secR k : ℂ) = Poly.lens (Poly.secR k) := fun k hk =>
    aF_zero_eq_lens (hR0 k hk) (hR2 k hk)
  have hanti : ∀ m, AntitoneOn (fun ρ : ℝ => aF m (ρ : ℂ)) (Icc 1 2) := fun m =>
    (hPL (m + 1)).mono fun x hx => le_trans zero_le_one hx.1
  have hR9 : ∀ m k, 9 ≤ k → aF m (Poly.secR 9 : ℂ) ≤ aF m (Poly.secR k : ℂ) := by
    intro m k hk
    obtain ⟨h1, h2, -⟩ := Poly.trig_ge_nine hk
    refine p2_aF_anti hPL ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact h2
  -- n = 3 for k ≥ 8
  have h3 : ∀ k, 8 ≤ k → CompletelyMixable 3 (unifSet (poly k)) := by
    intro k h
    obtain ⟨h1, h2, -⟩ := Poly.trig_ge_eight h
    have hl := Poly.lens_ge_eight h1 h2
    have hR : 0 < aF 0 (Poly.secR k : ℂ) := by rw [aF0R k (by omega)]; linarith
    refine thm95 hPL 0 k (by omega) hR (fun q _ => nu_le_Nb hPL (by omega) hR q) ?_
    have := Poly.cor96a_ge_eight h (Poly.Ssum_nonneg 3 k) (Poly.Ssum_le 3 k)
    rw [aF01, aF0R k (by omega), hF00, aF00]; exact this
  -- n = 4 for k ≥ 8
  have h4 : ∀ k, 8 ≤ k → CompletelyMixable 4 (unifSet (poly k)) := by
    intro k hk
    rcases (show k = 8 ∨ 9 ≤ k by omega) with h | h
    · subst h
      have hR : 0 < aF 1 (Poly.secR 8 : ℂ) := by linarith
      refine thm95 hPL 1 8 (by norm_num) hR (fun q _ => nu_le_Nb hPL (by norm_num) hR q) ?_
      have := Poly.cor96b_four_eight ha41 ha48
      rw [hF10, aF10]; exact this
    · have hR : 0 < aF 1 (Poly.secR k : ℂ) := by linarith [hR9 1 k h]
      refine thm95 hPL 1 k (by omega) hR (fun q _ => nu_le_Nb hPL (by omega) hR q) ?_
      have := Poly.cor96b_four (hanti 1) (by simpa using ha41) ha49 h
      simp only [Complex.ofReal_one] at this
      rw [hF10, aF10]; exact this
  -- n = 5 for k ≥ 9
  have h5 : ∀ k, 9 ≤ k → CompletelyMixable 5 (unifSet (poly k)) := by
    intro k hk
    have hR : 0 < aF 2 (Poly.secR k : ℂ) := by linarith [hR9 2 k hk]
    refine thm95 hPL 2 k (by omega) hR (fun q _ => nu_le_Nb hPL (by omega) hR q) ?_
    have hc4 : 0 < aF 2 0 := by linarith [aF_le hPL (m := 2) 1]
    have := Poly.cor96b_five (hanti 2) (by simpa using ha51) ha59 hc4 hc4u hk
    simp only [Complex.ofReal_one] at this
    rw [hF20]; exact this
  intro k hk n hn
  rcases hk with hk | hk | hk | hk
  · apply Poly.all_of_three_four_five (h3 k hk) (h4 k hk) _ n hn
    rcases (show k = 8 ∨ 9 ≤ k by omega) with h | h
    · subst h
      have h2 : CompletelyMixable 2 (unifSet (poly 8)) :=
        (completelyMixable_two_iff_even (by norm_num)).2 (by decide)
      exact ScaledB.completelyMixable_add_add h2 (h3 8 le_rfl)
    · exact h5 k h
  · subst hk; exact tri_cm hn
  · subst hk; exact sq_cm hn
  · subst hk; exact hex_cm (by omega)

/-- **Corollary 96 (d), complete, without the Table 15 cases** (hypotheses of `cor96d_noc`):
for `k ≥ 8` or `k ∈ {3, 4, 6}`, and `n ≥ 2`, `U(P_k)` is `n`-completely mixable iff `n ≥ 3` or
`k` is even. -/
theorem cor96d_noc_iff_of (hPL : PLHyp)
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    {k n : ℕ} (hk : 8 ≤ k ∨ k = 3 ∨ k = 4 ∨ k = 6) (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (poly k)) ↔ 3 ≤ n ∨ Even k := by
  have hk3 : 3 ≤ k := by omega
  rcases (show n = 2 ∨ 3 ≤ n by omega) with h | h
  · subst h; rw [completelyMixable_two_iff_even hk3]; simp
  · exact ⟨fun _ => Or.inl h, fun _ => cor96d_noc_of hPL ha41 ha49 ha48 ha51 ha59 hc4u k hk n h⟩

/-! ### The final statements: Prékopa–Leindler (`PrekopaLeindler.plHyp`), `a₄(1)` and `c₄` proved -/

/-- **Corollary 96 (d), `n ≥ 3`**, with Prékopa–Leindler, `a₄(1) = 3π²/4 - 4 ≥ 3.398`,
`c₄ = π³ - 16π/3 ≤ 14.252` and the triangle, square and hexagon proved. Remaining hypotheses:
the floating-point bounds `a₄(sec π/9) ≥ 3.143`, `a₄(sec π/8) ≥ 3.071`, `a₅(1) ≥ 9.242`,
`a₅(sec π/9) ≥ 8.724`, the corner-area bound for `k = 7`, and the four Table 15 cases. Then
every regular polygon `P_k`, `k ≥ 3`, is `n`-completely mixable for every `n ≥ 3`. -/
theorem cor96d_from_cond
    (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ)) (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ))
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Poly.secR 7 : ℂ) ∧ Cond22 2 7) :
    ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, 3 ≤ n → CompletelyMixable n (unifSet (poly k)) :=
  cor96d_from_cond_of PrekopaLeindler.plHyp aF11_ge ha49 ha48 ha51 ha59 aF20_le hcap h53 h54 h74
    h75

/-- **Corollary 96 (d), complete** (hypotheses of `cor96d_from_cond`): for `k ≥ 3`, `n ≥ 2`,
`U(P_k)` is `n`-completely mixable iff `n ≥ 3` or `k` is even. -/
theorem cor96d_from_cond_iff
    (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ)) (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ))
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Poly.secR 7 : ℂ) ∧ Cond22 2 7)
    {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (poly k)) ↔ 3 ≤ n ∨ Even k :=
  cor96d_from_cond_iff_of PrekopaLeindler.plHyp aF11_ge ha49 ha48 ha51 ha59 aF20_le hcap h53
    h54 h74 h75 hk hn

/-- **Corollary 96 (d) for `k ≥ 8` and `k = 3, 4, 6`, `n ≥ 3`.** The only hypotheses are the
four floating-point bounds `a₄(sec π/9) ≥ 3.143`, `a₄(sec π/8) ≥ 3.071`, `a₅(1) ≥ 9.242`,
`a₅(sec π/9) ≥ 8.724`. -/
theorem cor96d_noc
    (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ)) (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) :
    ∀ k : ℕ, (8 ≤ k ∨ k = 3 ∨ k = 4 ∨ k = 6) →
      ∀ n : ℕ, 3 ≤ n → CompletelyMixable n (unifSet (poly k)) :=
  cor96d_noc_of PrekopaLeindler.plHyp aF11_ge ha49 ha48 ha51 ha59 aF20_le

/-- **Corollary 96 (d) for `k ≥ 8` and `k = 3, 4, 6`, complete** (hypotheses of `cor96d_noc`):
for `n ≥ 2`, `U(P_k)` is `n`-completely mixable iff `n ≥ 3` or `k` is even. -/
theorem cor96d_noc_iff
    (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ)) (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ))
    {k n : ℕ} (hk : 8 ≤ k ∨ k = 3 ∨ k = 4 ∨ k = 6) (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (poly k)) ↔ 3 ≤ n ∨ Even k :=
  cor96d_noc_iff_of PrekopaLeindler.plHyp aF11_ge ha49 ha48 ha51 ha59 aF20_le hk hn

/-- **The triangle, square and hexagon, unconditionally**: for `k ∈ {3, 4, 6}` and `n ≥ 2`,
`U(P_k)` is `n`-completely mixable iff `n ≥ 3` or `k` is even. -/
theorem small_iff {k n : ℕ} (hk : k = 3 ∨ k = 4 ∨ k = 6) (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (poly k)) ↔ 3 ≤ n ∨ Even k := by
  have hk3 : 3 ≤ k := by omega
  rcases (show n = 2 ∨ 3 ≤ n by omega) with h | h
  · subst h; rw [completelyMixable_two_iff_even hk3]; simp
  · refine ⟨fun _ => Or.inl h, fun _ => ?_⟩
    rcases hk with rfl | rfl | rfl
    · exact tri_cm h
    · exact sq_cm h
    · exact hex_cm (by omega)

end Poly96

end Mixes
