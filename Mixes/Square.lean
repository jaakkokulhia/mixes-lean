import Mixes.Defs

/-!
# The square sliced parallel to a diagonal (Proposition 86, `st:prop:square`)

Let `K = {(t, y) : |t| + |y| ≤ 1}`, sliced parallel to a diagonal with the level `t`. The level
`t` has the density `1 - |t|` on `[-1, 1]` and the chord at level `t` has half-length
`r t = 1 - |t|`. Proposition 86 states that no `3`-complete mix `(T₁, T₂, T₃)` of the levels
satisfies the polygon inequality `2 r(Tᵢ) ≤ r(T₁) + r(T₂) + r(T₃)` almost surely.

Main results:
* `Mixes.SquareSlice.levelDist`: the distribution of the levels, with
  `levelDist_isProb` (it is a probability measure).
* `Mixes.SquareSlice.not_two_large`: at most one `|Tᵢ|` exceeds `1/2`.
* `Mixes.SquareSlice.cert_sum_nonpos`: the certificate inequality `f(T₁) + f(T₂) + f(T₃) ≤ 0`,
  pointwise on triples of levels in `[-1, 1]` with sum `0` and the polygon inequality.
* `Mixes.SquareSlice.integral_cert`: `∫ f(t) (1 - |t|) dt = 2x₀(1/8 - x₀/2 + x₀²/6)`.
* `Mixes.SquareSlice.no_polygon_complete_mix`: Proposition 86 for probability measures on
  triples.
-/

open MeasureTheory Set

noncomputable section

namespace Mixes

namespace SquareSlice

/-- The half-length of the chord of `K` at level `t`. -/
def r (t : ℝ) : ℝ := 1 - |t|

/-- The density `1 - |t|` of the level, as a nonnegative real (positive part). -/
def levelDensity (t : ℝ) : NNReal := (1 - |t|).toNNReal

/-- The distribution of the level `t` of a uniform point of `K`: density `1 - |t|` on
`[-1, 1]`. -/
def levelDist : Measure ℝ :=
  (volume.restrict (Icc (-1 : ℝ) 1)).withDensity fun t => (levelDensity t : ENNReal)

/-- The polygon inequality for the half-lengths of a triple of levels. -/
def PolygonIneq (x : Fin 3 → ℝ) : Prop := ∀ i, 2 * r (x i) ≤ ∑ j, r (x j)

/-- The certificate of the proof: `|t| - 2x₀` for `|t| > 1/2`, `-(|t| - x₀)⁺` otherwise. -/
def cert (x0 t : ℝ) : ℝ := if 1 / 2 < |t| then |t| - 2 * x0 else -max (|t| - x0) 0

/-! ### The finite-dimensional core -/

/-- At most one level of a triple exceeds `1/2` in absolute value. -/
lemma not_two_large {a b c : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (hs : a + b + c = 0) (hpa : 2 * r a ≤ r a + r b + r c) (hpb : 2 * r b ≤ r a + r b + r c)
    (hpc : 2 * r c ≤ r a + r b + r c) : ¬ (1 / 2 < |a| ∧ 1 / 2 < |b|) := by
  have ea := abs_cases a
  have eb := abs_cases b
  have ec := abs_cases c
  unfold r at *
  generalize |a| = A at *
  generalize |b| = B at *
  generalize |c| = C at *
  rcases ea with ⟨ea, ea'⟩ | ⟨ea, ea'⟩ <;> rcases eb with ⟨eb, eb'⟩ | ⟨eb, eb'⟩ <;>
    rcases ec with ⟨ec, ec'⟩ | ⟨ec, ec'⟩ <;> subst ea eb ec <;> rintro ⟨h1, h2⟩ <;> linarith

/-- The certificate inequality: for levels in `[-1, 1]` with sum `0` satisfying the polygon
inequality, `f(a) + f(b) + f(c) ≤ 0` (for every `x₀ ≥ 0`). -/
lemma cert_sum_nonpos {x0 : ℝ} (hx0 : 0 ≤ x0) {a b c : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ 1) (hs : a + b + c = 0) (hpa : 2 * r a ≤ r a + r b + r c)
    (hpb : 2 * r b ≤ r a + r b + r c) (hpc : 2 * r c ≤ r a + r b + r c) :
    cert x0 a + cert x0 b + cert x0 c ≤ 0 := by
  have ea := abs_cases a
  have eb := abs_cases b
  have ec := abs_cases c
  unfold cert r at *
  generalize |a| = A at *
  generalize |b| = B at *
  generalize |c| = C at *
  simp only [max_def]
  rcases ea with ⟨ea, ea'⟩ | ⟨ea, ea'⟩ <;> rcases eb with ⟨eb, eb'⟩ | ⟨eb, eb'⟩ <;>
    rcases ec with ⟨ec, ec'⟩ | ⟨ec, ec'⟩ <;> subst ea eb ec <;> split_ifs <;> linarith

/-! ### Measurability and bounds -/

lemma measurable_cert (x0 : ℝ) : Measurable (cert x0) := by
  unfold cert
  refine Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
    (continuous_abs.sub continuous_const).measurable ?_
  exact ((continuous_abs.sub continuous_const).max continuous_const).neg.measurable

lemma abs_cert_le {x0 t : ℝ} (hx0 : 0 ≤ x0) (hx0' : x0 ≤ 1 / 2) (ht : |t| ≤ 1) :
    |cert x0 t| ≤ 2 := by
  unfold cert
  have := abs_nonneg t
  rw [abs_le]
  split_ifs with h
  · constructor <;> linarith
  · constructor
    · have : max (|t| - x0) 0 ≤ 1 := max_le (by linarith) (by norm_num)
      linarith
    · have : 0 ≤ max (|t| - x0) 0 := le_max_right _ _
      linarith

lemma measurable_levelDensity : Measurable levelDensity :=
  (continuous_const.sub continuous_abs).measurable.real_toNNReal

/-! ### Integrals against the level distribution -/

/-- Integrals against `levelDist` are integrals against `(1 - |t|) dt` on `[-1, 1]`. -/
lemma integral_levelDist (g : ℝ → ℝ) :
    ∫ t, g t ∂levelDist = ∫ t in (-1 : ℝ)..1, (1 - |t|) * g t := by
  rw [levelDist, integral_withDensity_eq_integral_smul measurable_levelDensity,
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  have : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  simp only [levelDensity, NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (by linarith)]

lemma levelDist_ae_mem : ∀ᵐ t ∂levelDist, t ∈ Icc (-1 : ℝ) 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

/-- `∫ (p + q t + s t²) dt` on `[a, b]`. -/
lemma integral_quad (p q s a b : ℝ) :
    ∫ t in a..b, (p + q * t + s * t ^ 2) =
      p * (b - a) + q * (b ^ 2 - a ^ 2) / 2 + s * (b ^ 3 - a ^ 3) / 3 := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
    integral_id, intervalIntegral.integral_const]
  · simp; ring
  all_goals first
    | exact intervalIntegrable_const
    | exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    | exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
    | exact (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- For an even function integrable on `[-1, 1]`, `∫_{-1}^1 g = 2 ∫_0^1 g`. -/
lemma integral_even {g : ℝ → ℝ} (hg : ∀ t, g (-t) = g t)
    (hi : IntervalIntegrable g volume (-1) 1) :
    ∫ t in (-1 : ℝ)..1, g t = 2 * ∫ t in (0 : ℝ)..1, g t := by
  have h1 : IntervalIntegrable g volume (-1) 0 :=
    hi.mono_set (by rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
                    exact Icc_subset_Icc le_rfl (by norm_num))
  have h2 : IntervalIntegrable g volume 0 1 :=
    hi.mono_set (by rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
                    exact Icc_subset_Icc (by norm_num) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have : ∫ t in (-1 : ℝ)..0, g t = ∫ t in (0 : ℝ)..1, g t := by
    have e := intervalIntegral.integral_comp_neg (a := -1) (b := 0) g
    simp only [neg_zero, neg_neg] at e
    rw [← e]
    exact intervalIntegral.integral_congr (fun t _ => (hg t).symm)
  rw [this]; ring

/-- `∫_{-1}^1 (1 - |t|) dt = 1`. -/
lemma integral_density : ∫ t in (-1 : ℝ)..1, (1 - |t|) = 1 := by
  rw [integral_even (g := fun t => 1 - |t|) (fun t => by simp)
    ((by fun_prop : Continuous fun t : ℝ => 1 - |t|).intervalIntegrable _ _)]
  have : ∫ t in (0 : ℝ)..1, (1 - |t|) = ∫ t in (0 : ℝ)..1, (1 + (-1) * t + 0 * t ^ 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [abs_of_nonneg ht.1]; ring
  rw [this, integral_quad]; norm_num

/-- The level distribution is a probability measure. -/
lemma levelDist_isProb : IsProbabilityMeasure levelDist := by
  constructor
  rw [levelDist, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ t in Icc (-1 : ℝ) 1, ENNReal.ofReal (1 - |t|) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      integral_density, ENNReal.ofReal_one]
  · exact (continuous_const.sub continuous_abs).integrableOn_Icc
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
    have : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    simp only [Pi.zero_apply]; linarith

/-- The levels have mean `0`. -/
lemma integral_levelDist_id : ∫ t, t ∂levelDist = 0 := by
  rw [integral_levelDist]
  have e := intervalIntegral.integral_comp_neg (a := -1) (b := 1) (fun t : ℝ => (1 - |t|) * t)
  simp only [neg_neg, abs_neg, mul_neg, intervalIntegral.integral_neg] at e
  linarith

/-- The integrand `(1 - |t|) f(t)` is interval integrable on `[-1, 1]`. -/
lemma intervalIntegrable_cert {x0 : ℝ} (hx0 : 0 ≤ x0) (hx0' : x0 ≤ 1 / 2) :
    IntervalIntegrable (fun t => (1 - |t|) * cert x0 t) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  refine Measure.integrableOn_of_bounded (M := 2) (by simp)
    (((continuous_const.sub continuous_abs).measurable.mul
      (measurable_cert x0)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
  have h1 : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h2 := abs_cert_le hx0 hx0' h1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - |t|)]
  have := abs_nonneg t
  nlinarith [abs_nonneg (cert x0 t)]

/-- The integral of the certificate against the level density:
`∫_{-1}^1 f(t) (1 - |t|) dt = 2x₀(1/8 - x₀/2 + x₀²/6)` for `0 ≤ x₀ ≤ 1/2`. -/
theorem integral_cert {x0 : ℝ} (hx0 : 0 ≤ x0) (hx0' : x0 ≤ 1 / 2) :
    ∫ t in (-1 : ℝ)..1, (1 - |t|) * cert x0 t = 2 * x0 * (1 / 8 - x0 / 2 + x0 ^ 2 / 6) := by
  have hi := intervalIntegrable_cert hx0 hx0'
  rw [integral_even (fun t => by simp [cert]) hi]
  have hsub : ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => (1 - |t|) * cert x0 t) volume a b := fun a b ha hab hb =>
    hi.mono_set (by rw [uIcc_of_le hab, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc ha hb)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x0)
      (hsub 0 x0 (by norm_num) hx0 (by linarith)) (hsub x0 1 (by linarith) (by linarith) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (a := x0) (b := 1 / 2)
      (hsub x0 (1 / 2) (by linarith) hx0' (by norm_num))
      (hsub (1 / 2) 1 (by norm_num) (by norm_num) le_rfl)]
  have e1 : ∫ t in (0 : ℝ)..x0, (1 - |t|) * cert x0 t =
      ∫ t in (0 : ℝ)..x0, (0 + 0 * t + 0 * t ^ 2) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hx0] at ht
    have : |t| = t := abs_of_nonneg ht.1.le
    have hn : ¬ (1 / 2 < t) := by linarith [ht.2]
    simp only [cert, this, hn, ite_false,
      max_eq_right (show t - x0 ≤ 0 by linarith [ht.2])]
    ring
  have e2 : ∫ t in x0..(1 / 2), (1 - |t|) * cert x0 t =
      ∫ t in x0..(1 / 2), (x0 + (-(1 + x0)) * t + 1 * t ^ 2) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hx0'] at ht
    have : |t| = t := abs_of_nonneg (by linarith [ht.1])
    have hn : ¬ (1 / 2 < t) := by linarith [ht.2]
    simp only [cert, this, hn, ite_false,
      max_eq_left (show 0 ≤ t - x0 by linarith [ht.1])]
    ring
  have e3 : ∫ t in (1 / 2 : ℝ)..1, (1 - |t|) * cert x0 t =
      ∫ t in (1 / 2 : ℝ)..1, (-2 * x0 + (1 + 2 * x0) * t + (-1) * t ^ 2) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le (by norm_num)] at ht
    have : |t| = t := abs_of_nonneg (by linarith [ht.1])
    simp only [cert, this, ht.1, ite_true]
    ring
  rw [e1, e2, e3, integral_quad, integral_quad, integral_quad]
  ring

/-- The integral of the certificate is positive for `0 < x₀ < 1/4`. -/
theorem integral_cert_pos {x0 : ℝ} (hx0 : 0 < x0) (hx0' : x0 < 1 / 4) :
    0 < ∫ t in (-1 : ℝ)..1, (1 - |t|) * cert x0 t := by
  rw [integral_cert hx0.le (by linarith)]
  have : 0 < 1 / 8 - x0 / 2 + x0 ^ 2 / 6 := by nlinarith
  positivity

/-! ### Proposition 86 -/

/-- **Proposition 86** (`st:prop:square`). Let the level `t` have the density `1 - |t|` on
`[-1, 1]` (the levels of the square `|t| + |y| ≤ 1` sliced parallel to a diagonal). No
`3`-complete mix `P` of the levels (a probability measure on triples with marginals `levelDist`
whose coordinates have a constant sum almost surely) satisfies the polygon inequality
`2 r(Tᵢ) ≤ r(T₁) + r(T₂) + r(T₃)` for the half-lengths `r(t) = 1 - |t|` almost surely. -/
theorem no_polygon_complete_mix (P : Measure (Fin 3 → ℝ)) (hP : IsCompleteMix 3 levelDist P) :
    ¬ ∀ᵐ x ∂P, PolygonIneq x := by
  intro hpoly
  obtain ⟨hprob, ⟨s, hs⟩, hmarg⟩ := hP
  have hmarg' : ∀ j : Fin 3, P.map (fun x => x j) = levelDist := hmarg
  have hmeas : ∀ j : Fin 3, Measurable fun x : Fin 3 → ℝ => x j := fun j => measurable_pi_apply j
  have hsupp : ∀ j : Fin 3, ∀ᵐ x ∂P, x j ∈ Icc (-1 : ℝ) 1 := fun j =>
    ae_of_ae_map (hmeas j).aemeasurable (by rw [hmarg' j]; exact levelDist_ae_mem)
  have hcoord : ∀ (j : Fin 3) (g : ℝ → ℝ), Measurable g →
      ∫ x, g (x j) ∂P = ∫ t, g t ∂levelDist := fun j g hg => by
    rw [← hmarg' j, integral_map (hmeas j).aemeasurable hg.aestronglyMeasurable]
  -- the constant sum is `0`
  have hint : ∀ j : Fin 3, Integrable (fun x : Fin 3 → ℝ => x j) P := fun j =>
    Integrable.of_bound (hmeas j).aestronglyMeasurable 1 (by
      filter_upwards [hsupp j] with x hx
      rw [Real.norm_eq_abs]; exact abs_le.2 ⟨hx.1, hx.2⟩)
  have hs0 : s = 0 := by
    have h1 : ∫ x, ∑ j, x j ∂P = s := by
      rw [integral_congr_ae hs]; simp
    rw [integral_finsetSum _ (fun j _ => hint j)] at h1
    have h2 : ∀ j : Fin 3, ∫ x, x j ∂P = 0 := fun j => by
      have := hcoord j id measurable_id
      simp only [id] at this
      rw [this, integral_levelDist_id]
    simp only [h2, Finset.sum_const_zero] at h1
    exact h1.symm
  subst hs0
  -- the certificate with `x₀ = 1/8`
  set x0 : ℝ := 1 / 8
  have hcint : ∀ j : Fin 3, Integrable (fun x : Fin 3 → ℝ => cert x0 (x j)) P := fun j =>
    Integrable.of_bound ((measurable_cert x0).comp (hmeas j)).aestronglyMeasurable 2 (by
      filter_upwards [hsupp j] with x hx
      rw [Real.norm_eq_abs]
      exact abs_cert_le (by norm_num) (by norm_num) (abs_le.2 ⟨hx.1, hx.2⟩))
  have hle : ∫ x, ∑ j, cert x0 (x j) ∂P ≤ 0 := by
    refine integral_nonpos_of_ae ?_
    filter_upwards [hs, hpoly, hsupp 0, hsupp 1, hsupp 2] with x hx hp h0 h1 h2
    simp only [Fin.sum_univ_three, Pi.zero_apply] at hx ⊢
    have hp0 := hp 0
    have hp1 := hp 1
    have hp2 := hp 2
    simp only [Fin.sum_univ_three] at hp0 hp1 hp2
    exact cert_sum_nonpos (by norm_num) (abs_le.2 ⟨h0.1, h0.2⟩) (abs_le.2 ⟨h1.1, h1.2⟩)
      (abs_le.2 ⟨h2.1, h2.2⟩) hx hp0 hp1 hp2
  rw [integral_finsetSum _ (fun j _ => hcint j)] at hle
  simp only [fun j => hcoord j (cert x0) (measurable_cert x0), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, integral_levelDist, nsmul_eq_mul] at hle
  have := integral_cert_pos (x0 := x0) (by norm_num) (by norm_num)
  push_cast at hle
  linarith

/-- Proposition 86, existential form: there is no `3`-complete mix of the levels satisfying the
polygon inequality almost surely. -/
theorem no_sliced_mix : ¬ ∃ P : Measure (Fin 3 → ℝ),
    IsCompleteMix 3 levelDist P ∧ ∀ᵐ x ∂P, PolygonIneq x :=
  fun ⟨P, hP, hpoly⟩ => no_polygon_complete_mix P hP hpoly

end SquareSlice

end Mixes
