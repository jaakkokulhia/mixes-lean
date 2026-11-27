import Mixes.ScaledB
import Mixes.FrustumMix

/-!
# Section 20, remaining parts: the levels of Lemma 82, Theorem 83 for the body, frusta in `𝒦⁺`

Item M1j (third part) of the verification priorities. The analytic part of Lemma 82 and the
one-dimensional parts of Theorem 83 and Corollary 84 are in `Mixes.Scaled`; the class
`𝒦⁺` (`KPlus`) is in `Mixes.ScaledB`.

* Lemma 82 (`g:lem:levels`), the construction of the levels: `levels82` (the `3`-complete mix
  `levelMix82 ν h` of `symNu ν`, built as in Lemma 69 with `δ(a) = min(a, 2h - a)/2`, sum `0`,
  absolute values `A = B + C` with `B, C ≤ h`), `levels82_paper` (the paper's hypotheses),
  `levelMix82_half` (for `h = 1/2` it is the construction of Lemma 69).
* Theorem 83 (`g:thm:bipyr`) for the body `K = {(z, y) : |z| ≤ 1, y ∈ r(z) F}`: `thm83_three`
  (the explicit `3`-complete mix), `thm83_two`, `thm83` (every `n ≥ 2`). Ingredients:
  `antitoneOn_of_even_concave`, `ac_of_concave` (absolute continuity of a concave profile),
  `levelDist_eq_symNu`, `hyp82_of_profile`, `fibre_of_shape`.
* Corollary 84 (b) (`g:cor:flat`): `condP_of_tail`, `cor84b_cond`, `cor84b`.
* Theorem 79 (`g:thm:class`), the frustum step of `𝒦 ⊂ 𝒦⁺`: `frustumSet_eq_hull` (a frustum is
  an affine image of the hull of Corollary 77 with `J = 1`, `a = q`, `b = 1`, `t = 0`),
  `unifSet_image_affineEquiv`, `KPlus_frustum`.
-/

open Set MeasureTheory intervalIntegral ProbabilityTheory
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes

namespace ScaledC

/-! ## Lemma 82: the levels -/

section Levels82

/-- The hypotheses of **Lemma 82** (`g:lem:levels`) used in the construction: `1/2 ≤ h < 1`,
`ν ≥ 0` a probability density on `[0, 1]`, non-increasing and absolutely continuous on `[0, 1]`,
`a ↦ ν(a)/(2h - a)` integrable on `[h, 1]` (automatic for `h > 1/2`), and condition (`g:eq:Ph`).
(The Lipschitz property on `[0, h]` and, for `h = 1/2`, `ν(1) = 0` are not needed; see
`levels82_paper` for the statement with the paper's hypotheses.) -/
structure Hyp82 (ν : ℝ → ℝ) (h : ℝ) : Prop where
  hh : 1 / 2 ≤ h
  hh1 : h < 1
  nonneg : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x
  int_one : ∫ x in (0:ℝ)..1, ν x = 1
  anti : AntitoneOn ν (Icc 0 1)
  ac : AbsolutelyContinuousOnInterval ν 0 1
  tail : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1
  P : 2 * ∫ a in h..1, ν a / (2 * h - a) ≤ ν h

variable {ν : ℝ → ℝ} {h : ℝ}

/-- The density `α` of the largest level `A` in Lemma 82, extended by `0` outside `(0, 1]`. -/
def alpha (ν : ℝ → ℝ) (h : ℝ) (x : ℝ) : ℝ := (Ioc (0:ℝ) 1).indicator (Scaled.alphaL ν h) x

lemma alpha_of_mem {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) : alpha ν h x = Scaled.alphaL ν h x :=
  indicator_of_mem hx _

lemma alpha_of_not_mem {x : ℝ} (hx : x ∉ Ioc (0:ℝ) 1) : alpha ν h x = 0 :=
  indicator_of_notMem hx _

lemma alphaL_low {x : ℝ} (hx : x ≤ h) :
    Scaled.alphaL ν h x = x ^ 2 * Scaled.Qf ν h x := by
  simp [Scaled.alphaL, hx]

lemma alphaL_high {x : ℝ} (hx : h < x) : Scaled.alphaL ν h x = 3 * ν x := by
  simp [Scaled.alphaL, not_le.2 hx]

theorem alpha_nonneg (H : Hyp82 ν h) (x : ℝ) : 0 ≤ alpha ν h x := by
  by_cases hx : x ∈ Ioc (0:ℝ) 1
  · rw [alpha_of_mem hx]
    exact Scaled.lemma82_alpha_nonneg H.hh H.hh1 H.anti H.nonneg H.P hx.1 hx.2
  · rw [alpha_of_not_mem hx]

lemma alphaL_div_nonneg (H : Hyp82 ν h) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ Scaled.alphaL ν h a / a := by
  rcases eq_or_lt_of_le ha0 with rfl | ha
  · simp
  · exact div_nonneg (Scaled.lemma82_alpha_nonneg H.hh H.hh1 H.anti H.nonneg H.P ha ha1) ha.le

lemma bL_nonneg (H : Hyp82 ν h) {x : ℝ} (hx : x ∈ Icc (0:ℝ) h) : 0 ≤ Scaled.bL ν h x := by
  unfold Scaled.bL
  refine add_nonneg (intervalIntegral.integral_nonneg hx.2 fun a ha =>
    alphaL_div_nonneg H (by linarith [hx.1, ha.1]) (by linarith [ha.2, H.hh1]))
    (Scaled.bL_tail_nonneg H.hh H.hh1 H.nonneg hx.1)

lemma nu_continuousAt (H : Hyp82 ν h) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : ContinuousAt ν x := by
  have := H.ac.continuousOn
  rw [uIcc_of_le zero_le_one] at this
  exact this.continuousAt (Icc_mem_nhds hx.1 hx.2)

lemma qInt_ii (H : Hyp82 ν h) {x : ℝ} (hx0 : 0 ≤ x) (hxh : x ≤ h) :
    IntervalIntegrable (Scaled.qInt ν h) volume x h :=
  Scaled.qInt_integrable H.hh H.hh1 H.ac H.tail hx0 hxh

lemma alpha_continuousAt (H : Hyp82 ν h) {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ h)
    (hx2 : x ≠ 1) : ContinuousAt (alpha ν h) x := by
  have hh1 := H.hh1
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact alpha_of_not_mem fun hh => by linarith [hh.1, show y < 0 from hy]
  rcases lt_or_gt_of_ne hx1 with hx' | hx'
  · have hc := (Scaled.Qf_ac (half_pos hx) (by linarith)
      (qInt_ii H (half_pos hx).le (by linarith))).continuousOn
    rw [uIcc_of_le (by linarith)] at hc
    have hc2 : ContinuousAt (fun y => y ^ 2 * Scaled.Qf ν h y) x :=
      (continuousAt_id.pow 2).mul (hc.continuousAt (Icc_mem_nhds (by linarith) hx'))
    refine hc2.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx hx'] with y hy
    rw [alpha_of_mem ⟨hy.1, by linarith [hy.2]⟩, alphaL_low hy.2.le]
  rcases lt_or_gt_of_ne hx2 with hx'' | hx''
  · refine ((nu_continuousAt H ⟨by linarith, hx''⟩).const_mul 3).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx' hx''] with y hy
    rw [alpha_of_mem ⟨by linarith [hy.1, H.hh], hy.2.le⟩, alphaL_high hy.1]
  · refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx''] with y hy
    exact alpha_of_not_mem fun hh => by linarith [hh.2, show 1 < y from hy]

lemma alpha_measurable (H : Hyp82 ν h) : Measurable (alpha ν h) := by
  refine measurable_of_countable_not_continuousAt ?_
  refine ((({0, h, 1} : Set ℝ)).toFinite.countable).mono fun x hx => ?_
  by_contra hne
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
  exact hx (alpha_continuousAt H hne.1 hne.2.1 hne.2.2)

/-! ### The complete mix of the levels -/

/-- `δ(a) = min(a, 2h - a) / 2`. -/
def delta (h a : ℝ) : ℝ := min a (2 * h - a) / 2

lemma delta_pos (H : Hyp82 ν h) {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : 0 < delta h a := by
  unfold delta
  have := lt_min ha.1 (show 0 < 2 * h - a by linarith [ha.2, H.hh])
  linarith

lemma continuous_delta (h : ℝ) : Continuous (delta h) :=
  (continuous_id.min (continuous_const.sub continuous_id)).div_const 2

lemma delta_of_le {a : ℝ} (ha : a ≤ h) : delta h a = a / 2 := by
  unfold delta; rw [min_eq_left (by linarith)]

lemma delta_of_ge {a : ℝ} (ha : h ≤ a) : delta h a = (2 * h - a) / 2 := by
  unfold delta; rw [min_eq_right (by linarith)]

lemma alphaDiv_ii (H : Hyp82 ν h) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ h) :
    IntervalIntegrable (fun a => alpha ν h a / a) volume x h := by
  have hI := Scaled.alpha_div_integrable H.hh H.hh1 H.ac H.anti H.nonneg H.tail H.P
  refine (hI.mono_set ?_).congr_ae ?_
  · rw [uIcc_of_le hx1, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hx0 le_rfl
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun a ha => ?_)
    rw [uIoc_of_le hx1] at ha
    simp only
    rw [alpha_of_mem ⟨by linarith [ha.1], by linarith [ha.2, H.hh1]⟩]

/-- The distribution of the largest level `A`, with density `α`. -/
def muA (ν : ℝ → ℝ) (h : ℝ) : Measure ℝ :=
  volume.withDensity fun a => ENNReal.ofReal (alpha ν h a)

/-- `B = A/2 + D` with `D = δ(A) V`. -/
def Bv (h : ℝ) (p : ℝ × ℝ) : ℝ := p.1 / 2 + delta h p.1 * p.2

/-- `C = A/2 - D` with `D = δ(A) V`. -/
def Cv (h : ℝ) (p : ℝ × ℝ) : ℝ := p.1 / 2 - delta h p.1 * p.2

/-- The joint distribution of `(A, V)`, `V ∼ U[-1, 1]` independent of `A`. -/
def P0 (ν : ℝ → ℝ) (h : ℝ) : Measure (ℝ × ℝ) := (muA ν h).prod Bipyramid.muV

lemma continuous_Bv (h : ℝ) : Continuous (Bv h) :=
  (continuous_fst.div_const 2).add (((continuous_delta h).comp continuous_fst).mul
    continuous_snd)

lemma continuous_Cv (h : ℝ) : Continuous (Cv h) :=
  (continuous_fst.div_const 2).sub (((continuous_delta h).comp continuous_fst).mul
    continuous_snd)

/-- The density `b` of `B` and `C`, extended by `0` outside `[0, h]`. -/
def bI (ν : ℝ → ℝ) (h : ℝ) (x : ℝ) : ℝ := (Icc (0:ℝ) h).indicator (Scaled.bL ν h) x

/-- The weight `α(a) / (2 δ(a))` of the uniform distribution on `[a/2 - δ(a), a/2 + δ(a)]`. -/
def phi (ν : ℝ → ℝ) (h : ℝ) (a : ℝ) : ENNReal := ENNReal.ofReal (alpha ν h a / (2 * delta h a))

/-- The set `{(a, x) : 0 < a < 1, x ∈ T, |x - a/2| ≤ δ(a)}`. -/
def Eset (h : ℝ) (T : Set ℝ) : Set (ℝ × ℝ) :=
  Prod.fst ⁻¹' Ioo 0 1 ∩ Prod.snd ⁻¹' T ∩ {p | p.1 / 2 - delta h p.1 ≤ p.2} ∩
    {p | p.2 ≤ p.1 / 2 + delta h p.1}

lemma measurableSet_Eset {T : Set ℝ} (hT : MeasurableSet T) : MeasurableSet (Eset h T) := by
  have c1 : Continuous fun p : ℝ × ℝ => p.1 / 2 - delta h p.1 :=
    (continuous_fst.div_const 2).sub ((continuous_delta h).comp continuous_fst)
  have c2 : Continuous fun p : ℝ × ℝ => p.1 / 2 + delta h p.1 :=
    (continuous_fst.div_const 2).add ((continuous_delta h).comp continuous_fst)
  exact (((measurable_fst measurableSet_Ioo).inter (measurable_snd hT)).inter
    (measurableSet_le c1.measurable measurable_snd)).inter
    (measurableSet_le measurable_snd c2.measurable)

lemma mem_Eset {T : Set ℝ} {a x : ℝ} : (a, x) ∈ Eset h T ↔
    a ∈ Ioo 0 1 ∧ x ∈ T ∧ a / 2 - delta h a ≤ x ∧ x ≤ a / 2 + delta h a := by
  simp only [Eset, mem_inter_iff, mem_preimage, mem_ofPred_eq, and_assoc]

lemma phi_measurable (H : Hyp82 ν h) : Measurable (phi ν h) :=
  ((alpha_measurable H).div ((continuous_delta h).measurable.const_mul 2)).ennreal_ofReal

lemma inner_a (H : Hyp82 ν h) {a : ℝ} (ha : a ≠ 1) {T : Set ℝ} (hT : MeasurableSet T) :
    ENNReal.ofReal (alpha ν h a) * Bipyramid.muV (Prod.mk a ⁻¹' (Bv h ⁻¹' T)) =
      ∫⁻ x, (Eset h T).indicator (fun p => phi ν h p.1) (a, x) := by
  by_cases haI : a ∈ Ioo (0:ℝ) 1
  · have hd := delta_pos H haI
    have e : (fun x => (Eset h T).indicator (fun p => phi ν h p.1) (a, x)) =
        (T ∩ Icc (a / 2 - delta h a) (a / 2 + delta h a)).indicator fun _ => phi ν h a := by
      ext x
      by_cases hx : (a, x) ∈ Eset h T
      · have hx' := mem_Eset.1 hx
        have hx'' : x ∈ T ∩ Icc (a / 2 - delta h a) (a / 2 + delta h a) := ⟨hx'.2.1, hx'.2.2⟩
        rw [indicator_of_mem hx, indicator_of_mem hx'']
      · have hx' : x ∉ T ∩ Icc (a / 2 - delta h a) (a / 2 + delta h a) := fun hh =>
          hx (mem_Eset.2 ⟨haI, hh.1, hh.2.1, hh.2.2⟩)
        rw [indicator_of_notMem hx, indicator_of_notMem hx']
    rw [e, lintegral_indicator_const (hT.inter measurableSet_Icc)]
    have e2 : Prod.mk a ⁻¹' (Bv h ⁻¹' T) = {v | a / 2 + delta h a * v ∈ T} := rfl
    rw [e2, Bipyramid.muV_preimage hd, ← mul_assoc, phi,
      ← ENNReal.ofReal_mul (alpha_nonneg H a), div_eq_mul_one_div (alpha ν h a)]
  · have h0 : alpha ν h a = 0 := alpha_of_not_mem fun hh =>
      haI ⟨hh.1, lt_of_le_of_ne hh.2 ha⟩
    have e : (fun x => (Eset h T).indicator (fun p => phi ν h p.1) (a, x)) = fun _ => 0 := by
      ext x
      exact indicator_of_notMem (fun hh => haI (mem_Eset.1 hh).1) _
    rw [e, h0]; simp

lemma Eset_slice (H : Hyp82 ν h) {x : ℝ} (hx0 : 0 < x) (hx1 : x < h) {a : ℝ} (ha1 : a ≠ 1) :
    (a ∈ Ioo (0:ℝ) 1 ∧ a / 2 - delta h a ≤ x ∧ x ≤ a / 2 + delta h a) ↔
      a ∈ Icc x h ∪ Ioc h (min 1 (x + h)) := by
  have hh1 := H.hh1
  constructor
  · rintro ⟨⟨a0, a1⟩, l, r⟩
    rcases le_or_gt a h with ha | ha
    · rw [delta_of_le ha] at l r; left; exact ⟨by linarith, ha⟩
    · rw [delta_of_ge ha.le] at l r; right; exact ⟨ha, le_min a1.le (by linarith)⟩
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · rw [delta_of_le r]; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have r1 := le_trans r (min_le_left _ _)
      have r2 := le_trans r (min_le_right _ _)
      rw [delta_of_ge l.le]
      exact ⟨⟨by linarith, lt_of_le_of_ne r1 ha1⟩, by linarith, by linarith⟩

lemma delta_le {a : ℝ} :
    delta h a ≤ a / 2 ∧ delta h a ≤ (2 * h - a) / 2 := by
  unfold delta
  exact ⟨by linarith [min_le_left a (2 * h - a)], by linarith [min_le_right a (2 * h - a)]⟩

lemma Eset_empty {x : ℝ} (hx : x < 0 ∨ h < x) {a : ℝ} :
    ¬ (a ∈ Ioo (0:ℝ) 1 ∧ a / 2 - delta h a ≤ x ∧ x ≤ a / 2 + delta h a) := by
  rintro ⟨_, l, r⟩
  obtain ⟨h1, h2⟩ := delta_le (h := h) (a := a)
  rcases hx with hx | hx <;> linarith

lemma P_nonneg (H : Hyp82 ν h) {x : ℝ} (hx : x ∈ Icc (0:ℝ) h) :
    0 ≤ ∫ a in x..h, alpha ν h a / a :=
  intervalIntegral.integral_nonneg hx.2 fun a ha =>
    div_nonneg (alpha_nonneg H a) (by linarith [hx.1, ha.1])

lemma bL_eq (H : Hyp82 ν h) {x : ℝ} (hx : 0 < x) (hxh : x ≤ h) :
    Scaled.bL ν h x = (∫ a in x..h, alpha ν h a / a) +
      ∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a) := by
  unfold Scaled.bL
  congr 1
  refine intervalIntegral.integral_congr fun a ha => ?_
  rw [uIcc_of_le hxh] at ha
  rw [alpha_of_mem ⟨by linarith [ha.1], by linarith [ha.2, H.hh1]⟩]

lemma inner_x (H : Hyp82 ν h) {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ h) (T : Set ℝ) :
    ∫⁻ a, (Eset h T).indicator (fun p => phi ν h p.1) (a, x) =
      T.indicator (fun x => ENNReal.ofReal (bI ν h x)) x := by
  have hh1 := H.hh1
  have hh := H.hh
  by_cases hxT : x ∉ T
  · rw [indicator_of_notMem hxT]
    have e : (fun a => (Eset h T).indicator (fun p => phi ν h p.1) (a, x)) = fun _ => 0 := by
      ext a; exact indicator_of_notMem (fun hh => hxT (mem_Eset.1 hh).2.1) _
    rw [e, lintegral_zero]
  push Not at hxT
  rw [indicator_of_mem hxT]
  by_cases hxI : x < 0 ∨ h < x
  · have e : (fun a => (Eset h T).indicator (fun p => phi ν h p.1) (a, x)) = fun _ => 0 := by
      ext a
      exact indicator_of_notMem (fun hh => Eset_empty hxI
        ⟨(mem_Eset.1 hh).1, (mem_Eset.1 hh).2.2⟩) _
    have hb : bI ν h x = 0 := indicator_of_notMem (fun hh => by
      rcases hxI with hh' | hh' <;> linarith [hh.1, hh.2]) _
    rw [e, lintegral_zero, hb, ENNReal.ofReal_zero]
  push Not at hxI
  have hxp : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
  have hxq : x < h := lt_of_le_of_ne hxI.2 hx1
  set m := min 1 (x + h) with hm
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmh : h ≤ m := le_min hh1.le (by linarith)
  set S := Icc x h ∪ Ioc h m with hS
  have ha1 : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1 := by simp [ae_iff, measure_singleton]
  have e : (fun a => (Eset h T).indicator (fun p => phi ν h p.1) (a, x)) =ᵐ[volume]
      S.indicator (phi ν h) := by
    filter_upwards [ha1] with a ha
    by_cases haS : a ∈ S
    · obtain ⟨h1, h2, h3⟩ := (Eset_slice H hxp hxq ha).2 haS
      rw [indicator_of_mem haS, indicator_of_mem (mem_Eset.2 ⟨h1, hxT, h2, h3⟩)]
    · rw [indicator_of_notMem haS, indicator_of_notMem fun hh => haS ((Eset_slice H hxp hxq ha).1
        ⟨(mem_Eset.1 hh).1, (mem_Eset.1 hh).2.2⟩)]
  have hdisj : Disjoint (Icc x h) (Ioc h m) :=
    Set.disjoint_left.2 fun a h1 h2 => by linarith [h1.2, h2.1]
  rw [lintegral_congr_ae e, lintegral_indicator (measurableSet_Icc.union measurableSet_Ioc),
    lintegral_union measurableSet_Ioc hdisj]
  have hxI' : x ∈ Icc (0:ℝ) h := ⟨hxp.le, hxq.le⟩
  have I1 : ∫⁻ a in Icc x h, phi ν h a = ENNReal.ofReal (∫ a in x..h, alpha ν h a / a) := by
    rw [setLIntegral_congr_fun measurableSet_Icc
      (g := fun a => ENNReal.ofReal (alpha ν h a / a))
      fun a ha => by rw [phi, delta_of_le ha.2, show 2 * (a / 2) = a by ring]]
    rw [intervalIntegral.integral_of_le hxq.le, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal]
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxq.le).1
        (alphaDiv_ii H hxp.le hxq.le)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      exact div_nonneg (alpha_nonneg H a) (by linarith [ha.1])
  have I2 : ∫⁻ a in Ioc h m, phi ν h a =
      ENNReal.ofReal (∫ a in h..m, 3 * ν a / (2 * h - a)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun a => ENNReal.ofReal (3 * ν a / (2 * h - a))) fun a ha => by
        rw [phi, delta_of_ge ha.1.le, alpha_of_mem ⟨by linarith [ha.1], ha.2.trans hm1⟩,
          alphaL_high ha.1, show 2 * ((2 * h - a) / 2) = 2 * h - a by ring]]
    rw [intervalIntegral.integral_of_le hmh, ofReal_integral_eq_lintegral_ofReal]
    · have hsub : Ioc h m ⊆ Ioc h 1 := Ioc_subset_Ioc le_rfl hm1
      have ht := H.tail
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh1.le] at ht
      refine ((ht.mono_set hsub).const_mul 3).congr ?_
      filter_upwards with a
      simp only [mul_div_assoc]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have := H.nonneg a ⟨by linarith [ha.1], ha.2.trans hm1⟩
      exact div_nonneg (by linarith) (by linarith [ha.2.trans hm1])
  rw [I1, I2, bI, indicator_of_mem hxI', bL_eq H hxp hxq.le,
    ENNReal.ofReal_add (P_nonneg H hxI') (Scaled.bL_tail_nonneg hh hh1 H.nonneg hxp.le)]

instance : SFinite (muA ν h) := by unfold muA; infer_instance

/-- The distribution of `B` has the density `b` on `[0, h]` (Fubini). -/
theorem lawB (H : Hyp82 ν h) {T : Set ℝ} (hT : MeasurableSet T) :
    P0 ν h (Bv h ⁻¹' T) = ∫⁻ x in T, ENNReal.ofReal (bI ν h x) := by
  have hS : MeasurableSet (Bv h ⁻¹' T) := (continuous_Bv h).measurable hT
  have hmA : Measurable fun a => ENNReal.ofReal (alpha ν h a) :=
    (alpha_measurable H).ennreal_ofReal
  rw [P0, Measure.prod_apply hS, muA,
    lintegral_withDensity_eq_lintegral_mul _ hmA (measurable_measure_prodMk_left hS)]
  have ha1 : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1 := by simp [ae_iff, measure_singleton]
  have hx0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  have hx1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ h := by simp [ae_iff, measure_singleton]
  calc ∫⁻ a, ((fun a => ENNReal.ofReal (alpha ν h a)) *
        fun a => Bipyramid.muV (Prod.mk a ⁻¹' (Bv h ⁻¹' T))) a
      = ∫⁻ a, ∫⁻ x, (Eset h T).indicator (fun p => phi ν h p.1) (a, x) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ha1] with a ha
        exact inner_a H ha hT
    _ = ∫⁻ x, ∫⁻ a, (Eset h T).indicator (fun p => phi ν h p.1) (a, x) := by
        refine lintegral_lintegral_swap ?_
        exact (((phi_measurable H).comp measurable_fst).indicator
          (measurableSet_Eset hT)).aemeasurable
    _ = ∫⁻ x, T.indicator (fun x => ENNReal.ofReal (bI ν h x)) x := by
        refine lintegral_congr_ae ?_
        filter_upwards [hx0, hx1] with x h0 h1
        exact inner_x H h0 h1 T
    _ = ∫⁻ x in T, ENNReal.ofReal (bI ν h x) := lintegral_indicator hT _

/-- `C` has the same distribution as `B`, because `V` is symmetric. -/
theorem lawC (T : Set ℝ) (hT : MeasurableSet T) :
    P0 ν h (Cv h ⁻¹' T) = P0 ν h (Bv h ⁻¹' T) := by
  have hm : Measurable (Prod.map (id : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
    measurable_id.prodMap measurable_neg
  have hP : (P0 ν h).map (Prod.map id Neg.neg) = P0 ν h := by
    rw [P0, ← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id,
      Bipyramid.muV_map_neg]
  have e : Cv h ⁻¹' T = Prod.map id Neg.neg ⁻¹' (Bv h ⁻¹' T) := by
    ext p; simp [Cv, Bv, sub_eq_add_neg]
  rw [e, ← Measure.map_apply hm ((continuous_Bv h).measurable hT), hP]

lemma dens_ae (H : Hyp82 ν h) : ∀ᵐ x ∂(volume : Measure ℝ),
    ENNReal.ofReal (alpha ν h x) + 2 * ENNReal.ofReal (bI ν h x) =
      3 * ENNReal.ofReal ((Icc (0:ℝ) 1).indicator ν x) := by
  have hh1 := H.hh1
  have hx0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [hx0] with x hx
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h1 : alpha ν h x = 0 := alpha_of_not_mem fun hh => by linarith [hh.1]
    have h2 : bI ν h x = 0 := indicator_of_notMem (fun hh => by linarith [hh.1]) _
    have h3 : (Icc (0:ℝ) 1).indicator ν x = 0 :=
      indicator_of_notMem (fun hh => by linarith [hh.1]) _
    simp [h1, h2, h3]
  rcases le_or_gt x h with hx1 | hx1
  · have h2 : bI ν h x = Scaled.bL ν h x :=
      indicator_of_mem (show x ∈ Icc (0:ℝ) h from ⟨hx.le, hx1⟩) _
    have h3 : (Icc (0:ℝ) 1).indicator ν x = ν x :=
      indicator_of_mem (show x ∈ Icc (0:ℝ) 1 from ⟨hx.le, by linarith⟩) _
    rw [h2, h3, alpha_of_mem ⟨hx, by linarith⟩]
    exact Bipyramid.ennreal_comb
      (Scaled.lemma82_alpha_nonneg H.hh H.hh1 H.anti H.nonneg H.P hx (by linarith))
      (bL_nonneg H ⟨hx.le, hx1⟩) (Scaled.lemma82_identity H.hh H.hh1 H.ac H.tail hx hx1)
  have h2 : bI ν h x = 0 := indicator_of_notMem (fun hh => by linarith [hh.2]) _
  rcases le_or_gt x 1 with hx2 | hx2
  · have h3 : (Icc (0:ℝ) 1).indicator ν x = ν x :=
      indicator_of_mem (show x ∈ Icc (0:ℝ) 1 from ⟨hx.le, hx2⟩) _
    rw [h2, h3, alpha_of_mem ⟨hx, hx2⟩, alphaL_high hx1]
    exact Bipyramid.ennreal_comb (by linarith [H.nonneg x ⟨hx.le, hx2⟩]) le_rfl (by ring)
  · have h1 : alpha ν h x = 0 := alpha_of_not_mem fun hh => by linarith [hh.2]
    have h3 : (Icc (0:ℝ) 1).indicator ν x = 0 :=
      indicator_of_notMem (fun hh => by linarith [hh.2]) _
    simp [h1, h2, h3]

/-- `α + 2 b = 3 ν` as distributions: `P(A ∈ T) + 2 P(B ∈ T) = 3 ∫_T ν`. -/
theorem sumAB (H : Hyp82 ν h) {T : Set ℝ} (hT : MeasurableSet T) :
    muA ν h T + 2 * P0 ν h (Bv h ⁻¹' T) = 3 * Bipyramid.nuMeas ν T := by
  rw [lawB H hT, muA, Bipyramid.nuMeas, withDensity_apply _ hT, withDensity_apply _ hT,
    ← lintegral_const_mul' _ _ (by simp),
    ← lintegral_add_left (alpha_measurable H).ennreal_ofReal,
    ← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_congr_ae (ae_restrict_of_ae (dens_ae H))

lemma P0_fst (T : Set ℝ) : P0 ν h (Prod.fst ⁻¹' T) = muA ν h T := by
  rw [← prod_univ, P0, Measure.prod_prod, measure_univ, mul_one]

lemma nuMeas_univ (H : Hyp82 ν h) : Bipyramid.nuMeas ν univ = 1 := by
  rw [Bipyramid.nuMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have e : (fun x => ENNReal.ofReal ((Icc (0:ℝ) 1).indicator ν x)) =
      (Icc (0:ℝ) 1).indicator fun x => ENNReal.ofReal (ν x) := by
    ext x; by_cases hx : x ∈ Icc (0:ℝ) 1 <;> simp [hx]
  have hc := H.ac.continuousOn
  rw [uIcc_of_le zero_le_one] at hc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)] ν := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact H.nonneg x hx
  rw [e, lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc hnn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, H.int_one,
    ENNReal.ofReal_one]

lemma muA_univ (H : Hyp82 ν h) : muA ν h univ = 1 := by
  have e := sumAB H MeasurableSet.univ
  rw [preimage_univ, ← P0_fst univ, preimage_univ, nuMeas_univ H, mul_one] at e
  have hfin : P0 ν h univ ≠ ⊤ := by
    intro htop; rw [htop] at e; simp at e
  have : 3 * P0 ν h univ = 3 * 1 := by
    rw [mul_one]
    calc 3 * P0 ν h univ = P0 ν h univ + 2 * P0 ν h univ := by ring
      _ = 3 := e
  have := (ENNReal.mul_right_inj (by norm_num) (by simp)).1 this
  rw [← P0_fst univ, preimage_univ, this]

/-- `α` is a probability density on `[0, 1]` (also `Scaled.lemma82_integral`). -/
theorem alpha_integral (H : Hyp82 ν h) : ∫ x in (0:ℝ)..1, alpha ν h x = 1 := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => alpha_of_not_mem hx,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (alpha_nonneg H))
      (alpha_measurable H).aestronglyMeasurable]
  have := muA_univ H
  rw [muA, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  rw [this, ENNReal.toReal_one]

/-- The vector `(A, -B, -C)`. -/
def W (h : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1, -Bv h p, -Cv h p]

lemma measurable_W (h : ℝ) (j : Fin 3) : Measurable fun p => W h p j := by
  fin_cases j
  · exact measurable_fst
  · exact (continuous_Bv h).measurable.neg
  · exact (continuous_Cv h).measurable.neg

/-- The map `(A, V) ↦ (ε W_{π(1)}, ε W_{π(2)}, ε W_{π(3)})` for a sign `ε` and a permutation
`π`. -/
def zmap (h : ℝ) (b : Bool) (σ : Equiv.Perm (Fin 3)) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  fun i => Bipyramid.sgn b * W h p (σ i)

lemma measurable_zmap (h : ℝ) (b : Bool) (σ : Equiv.Perm (Fin 3)) : Measurable (zmap h b σ) :=
  Measurable.of_eval fun i => measurable_const.mul (measurable_W h (σ i))

/-- The levels `(Z₁, Z₂, Z₃)` of **Lemma 82**: the average over the random sign `ε` and the
uniformly random permutation `π` of the images of the law of `(A, V)`. -/
def levelMix82 (ν : ℝ → ℝ) (h : ℝ) : Measure (Fin 3 → ℝ) :=
  (12 : ENNReal)⁻¹ • ∑ b : Bool, ∑ σ : Equiv.Perm (Fin 3), (P0 ν h).map (zmap h b σ)

lemma levelMix82_apply {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S) :
    levelMix82 ν h S = (12 : ENNReal)⁻¹ *
      ∑ b : Bool, ∑ σ : Equiv.Perm (Fin 3), P0 ν h (zmap h b σ ⁻¹' S) := by
  simp only [levelMix82, smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
  simp only [Measure.map_apply (measurable_zmap _ _ _) hS]

lemma P0_sgn_W (b : Bool) {T : Set ℝ} (hT : MeasurableSet T) :
    ∑ j, P0 ν h ((fun p => Bipyramid.sgn b * W h p j) ⁻¹' T) =
      muA ν h ((fun x => Bipyramid.sgn b * x) ⁻¹' T) +
        2 * P0 ν h (Bv h ⁻¹' ((fun x => -(Bipyramid.sgn b * x)) ⁻¹' T)) := by
  have hT' : MeasurableSet ((fun x => -(Bipyramid.sgn b * x)) ⁻¹' T) :=
    (measurable_const.mul measurable_id).neg hT
  rw [Fin.sum_univ_three, two_mul, ← add_assoc]
  congr 1
  · congr 1
    · rw [← P0_fst]; rfl
    · congr 1; ext p; simp [W, mul_neg]
  · rw [← lawC _ hT']; congr 1; ext p; simp [W, mul_neg]

/-- Each coordinate of `levelMix82 ν h` has the distribution `symNu ν`. -/
theorem levelMix82_marginal (H : Hyp82 ν h) (i : Fin 3) :
    (levelMix82 ν h).map (fun z => z i) = Bipyramid.symNu ν := by
  ext T hT
  rw [Measure.map_apply (measurable_pi_apply i) hT,
    levelMix82_apply (measurable_pi_apply i hT)]
  have e1 : ∀ b, ∑ σ : Equiv.Perm (Fin 3), P0 ν h (zmap h b σ ⁻¹' ((fun z => z i) ⁻¹' T)) =
      2 * (muA ν h ((fun x => Bipyramid.sgn b * x) ⁻¹' T) +
        2 * P0 ν h (Bv h ⁻¹' ((fun x => -(Bipyramid.sgn b * x)) ⁻¹' T))) := fun b => by
    rw [← P0_sgn_W b hT]
    exact Bipyramid.perm_sum (fun j => P0 ν h ((fun p => Bipyramid.sgn b * W h p j) ⁻¹' T)) i
  rw [Fintype.sum_bool, e1, e1, Bipyramid.sgn_preimage_true, Bipyramid.sgn_preimage_false,
    Bipyramid.sgn_neg_preimage_true, Bipyramid.sgn_neg_preimage_false]
  have hTn : MeasurableSet (Neg.neg ⁻¹' T) := measurable_neg hT
  have k : muA ν h T + 2 * P0 ν h (Bv h ⁻¹' (Neg.neg ⁻¹' T)) +
      (muA ν h (Neg.neg ⁻¹' T) + 2 * P0 ν h (Bv h ⁻¹' T)) =
      3 * (Bipyramid.nuMeas ν T + Bipyramid.nuMeas ν (Neg.neg ⁻¹' T)) := by
    rw [mul_add, ← sumAB H hT, ← sumAB H hTn]; ring
  rw [← mul_add, k, Bipyramid.symNu, smul_apply, add_apply,
    Measure.map_apply measurable_neg hT, smul_eq_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (12 : ENNReal) = 2 * 6 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    mul_assoc, mul_assoc, show (2 : ENNReal) * 3 = 6 by norm_num,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

lemma P0_ae :
    ∀ᵐ p ∂(P0 ν h), p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ Icc (-1:ℝ) 1 := by
  rw [ae_iff]
  refine measure_mono_null (t := Prod.fst ⁻¹' (Icc (0:ℝ) 1)ᶜ ∪ Prod.snd ⁻¹' (Icc (-1:ℝ) 1)ᶜ)
    (fun p hp => ?_) (measure_union_null ?_ ?_)
  · simp only [mem_ofPred_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  · rw [P0_fst, muA, withDensity_apply _ measurableSet_Icc.compl]
    refine (setLIntegral_congr_fun measurableSet_Icc.compl (g := fun _ => 0)
      fun x hx => ?_).trans lintegral_zero
    have : alpha ν h x = 0 := alpha_of_not_mem fun hh => hx (Ioc_subset_Icc_self hh)
    simp [this]
  · rw [← univ_prod, P0, Measure.prod_prod, Bipyramid.muV_apply, compl_inter_self,
      measure_empty, mul_zero, mul_zero]

lemma levelMix82_ae {Pr : (Fin 3 → ℝ) → Prop} (hP : MeasurableSet {z | Pr z})
    (hall : ∀ b σ (p : ℝ × ℝ), p.1 ∈ Icc (0:ℝ) 1 → p.2 ∈ Icc (-1:ℝ) 1 →
      Pr (zmap h b σ p)) :
    ∀ᵐ z ∂(levelMix82 ν h), Pr z := by
  rw [ae_iff]
  change levelMix82 ν h {z | Pr z}ᶜ = 0
  rw [levelMix82_apply hP.compl]
  have : ∀ b σ, P0 ν h (zmap h b σ ⁻¹' {z | Pr z}ᶜ) = 0 := fun b σ => by
    have := P0_ae (ν := ν) (h := h)
    have h2 : ∀ᵐ p ∂(P0 ν h), Pr (zmap h b σ p) := by
      filter_upwards [this] with p hp using hall b σ p hp.1 hp.2
    exact ae_iff.1 h2
  simp only [this, Finset.sum_const_zero, mul_zero]

lemma zmap_sum (b : Bool) (σ : Equiv.Perm (Fin 3)) (p : ℝ × ℝ) :
    ∑ i, zmap h b σ p i = 0 := by
  simp only [zmap]
  rw [← Finset.mul_sum, Equiv.sum_comp σ (fun j => W h p j), Fin.sum_univ_three]
  simp only [W, Bv, Cv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one]
  ring_nf

lemma B_mem (H : Hyp82 ν h) {p : ℝ × ℝ} (h1 : p.1 ∈ Icc (0:ℝ) 1)
    (h2 : p.2 ∈ Icc (-1:ℝ) 1) : Bv h p ∈ Icc 0 h ∧ Cv h p ∈ Icc 0 h := by
  have hh := H.hh
  obtain ⟨d1, d2⟩ := delta_le (h := h) (a := p.1)
  have d0 : 0 ≤ delta h p.1 := by
    unfold delta; have := le_min h1.1 (show 0 ≤ 2 * h - p.1 by linarith [h1.2]); linarith
  have u1 : delta h p.1 * p.2 ≤ delta h p.1 := by nlinarith [h2.2]
  have u2 : -delta h p.1 ≤ delta h p.1 * p.2 := by nlinarith [h2.1]
  simp only [Bv, Cv]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The structural property of the levels: some permutation `σ` puts the largest absolute value
first, `|Z_{σ 0}| = |Z_{σ 1}| + |Z_{σ 2}|`, with `|Z_{σ 1}|, |Z_{σ 2}| ≤ h`, and all `|Z_i| ≤ 1`. -/
def LevelShape (h : ℝ) (z : Fin 3 → ℝ) : Prop :=
  (∀ i, |z i| ≤ 1) ∧ ∃ σ : Equiv.Perm (Fin 3),
    |z (σ 0)| = |z (σ 1)| + |z (σ 2)| ∧ |z (σ 1)| ≤ h ∧ |z (σ 2)| ≤ h

lemma measurableSet_levelShape (h : ℝ) : MeasurableSet {z : Fin 3 → ℝ | LevelShape h z} := by
  have ha : ∀ i, Measurable fun z : Fin 3 → ℝ => |z i| := fun i =>
    continuous_abs.measurable.comp (measurable_pi_apply i)
  simp only [LevelShape, ofPred_and, ofPred_exists, ofPred_forall]
  refine (MeasurableSet.iInter fun i => measurableSet_le (ha i) measurable_const).inter
    (MeasurableSet.iUnion fun σ => ?_)
  exact (measurableSet_eq_fun (ha _) ((ha _).add (ha _))).inter
    ((measurableSet_le (ha _) measurable_const).inter (measurableSet_le (ha _) measurable_const))

lemma zmap_shape (H : Hyp82 ν h) (b : Bool) (σ : Equiv.Perm (Fin 3)) {p : ℝ × ℝ}
    (h1 : p.1 ∈ Icc (0:ℝ) 1) (h2 : p.2 ∈ Icc (-1:ℝ) 1) : LevelShape h (zmap h b σ p) := by
  obtain ⟨hB, hC⟩ := B_mem H h1 h2
  have hW : ∀ j, |W h p j| ≤ 1 := by
    intro j; fin_cases j
    · simp [W, abs_le]; constructor <;> linarith [h1.1, h1.2]
    · simp [W, abs_le]; constructor <;> linarith [hB.1, hB.2, H.hh1]
    · simp [W, abs_le]; constructor <;> linarith [hC.1, hC.2, H.hh1]
  refine ⟨fun i => ?_, σ.symm, ?_⟩
  · simp only [zmap, abs_mul, Bipyramid.abs_sgn, one_mul]; exact hW _
  simp only [zmap, Equiv.apply_symm_apply, abs_mul, Bipyramid.abs_sgn, one_mul]
  simp only [W, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one, abs_neg,
    abs_of_nonneg hB.1, abs_of_nonneg hC.1, abs_of_nonneg h1.1]
  refine ⟨by simp only [Bv, Cv]; ring, hB.2, hC.2⟩

/-- **Lemma 82** (`g:lem:levels`). Under `Hyp82 ν h` (`1/2 ≤ h < 1`): `α ≥ 0` and
`∫₀¹ α = 1`, so `α` is a probability density on `[0, 1]`; the law `levelMix82 ν h` of
`(Z₁, Z₂, Z₃)`, built as in Lemma 69 from `A` with density `α`, `D` uniform on
`[-δ(A), δ(A)]` with `δ(a) = min(a, 2h - a)/2`, `B = A/2 + D`, `C = A/2 - D`, a random sign and
a uniformly random permutation, is a `3`-complete mix of the symmetric distribution `symNu ν` on
`[-1, 1]` whose absolute value has the density `ν`; almost surely `Z₁ + Z₂ + Z₃ = 0`, and the
absolute values are `A`, `B`, `C` (in some order) with `A = B + C`, `B, C ≤ h` (and `A ≤ 1`). -/
theorem levels82 (H : Hyp82 ν h) :
    (∀ x, 0 ≤ alpha ν h x) ∧ (∫ x in (0:ℝ)..1, alpha ν h x = 1) ∧
      IsCompleteMix 3 (Bipyramid.symNu ν) (levelMix82 ν h) ∧
      (∀ᵐ z ∂(levelMix82 ν h), ∑ i, z i = 0) ∧
      (∀ᵐ z ∂(levelMix82 ν h), LevelShape h z) := by
  have hsum : ∀ᵐ z ∂(levelMix82 ν h), ∑ i, z i = 0 :=
    levelMix82_ae (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
      measurable_pi_apply i) measurable_const) fun b σ p _ _ => zmap_sum b σ p
  have hprob : IsProbabilityMeasure (levelMix82 ν h) := by
    constructor
    have := congrArg (fun m : Measure ℝ => m univ) (levelMix82_marginal H 0)
    rw [Measure.map_apply (measurable_pi_apply 0) MeasurableSet.univ, preimage_univ] at this
    rw [this, Bipyramid.symNu, smul_apply, add_apply,
      Measure.map_apply measurable_neg MeasurableSet.univ, preimage_univ, nuMeas_univ H,
      smul_eq_mul, one_add_one_eq_two, ENNReal.inv_mul_cancel (by simp) (by simp)]
  refine ⟨alpha_nonneg H, alpha_integral H,
    ⟨hprob, ⟨0, hsum⟩, levelMix82_marginal H⟩, hsum, ?_⟩
  exact levelMix82_ae (measurableSet_levelShape h) fun b σ p h1 h2 => zmap_shape H b σ h1 h2

/-- **Lemma 82** (`g:lem:levels`) with the hypotheses of the paper: `1/2 ≤ h < 1`, `ν` a
probability density on `[0, 1]`, non-increasing and absolutely continuous on `[0, 1]`, Lipschitz
on `[0, h]`; if `h = 1/2`, also `ν(1) = 0` and `∫_{1/2}^1 ν(a)/(1 - a) da < ∞`; and (`g:eq:Ph`).
The Lipschitz property and `ν(1) = 0` are not used. -/
theorem levels82_paper (hh : 1 / 2 ≤ h) (hh1 : h < 1) (hν0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x)
    (hν1 : ∫ x in (0:ℝ)..1, ν x = 1) (hanti : AntitoneOn ν (Icc 0 1))
    (hac : AbsolutelyContinuousOnInterval ν 0 1)
    (_hlip : ∃ K, LipschitzOnWith K ν (Icc 0 h))
    (hhalf : h = 1 / 2 → ν 1 = 0 ∧ IntegrableOn (fun a => ν a / (1 - a)) (Icc (1 / 2) 1))
    (hP : 2 * ∫ a in h..1, ν a / (2 * h - a) ≤ ν h) :
    (∀ x, 0 ≤ alpha ν h x) ∧ (∫ x in (0:ℝ)..1, alpha ν h x = 1) ∧
      IsCompleteMix 3 (Bipyramid.symNu ν) (levelMix82 ν h) ∧
      (∀ᵐ z ∂(levelMix82 ν h), ∑ i, z i = 0) ∧
      (∀ᵐ z ∂(levelMix82 ν h), LevelShape h z) := by
  have htail : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1 := by
    rcases eq_or_lt_of_le hh with e | hlt
    · subst e
      obtain ⟨-, hI⟩ := hhalf rfl
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
      refine hI.congr_fun (fun a _ => ?_) measurableSet_Icc
      simp only; ring_nf
    · exact Scaled.tail_integrable_of_gt hlt hh1 hac
  exact levels82 ⟨hh, hh1, hν0, hν1, hanti, hac, htail, hP⟩

/-- For `h = 1/2` the density `α` of Lemma 82 is that of Lemma 69. -/
lemma alpha_half (ν : ℝ → ℝ) : alpha ν (1 / 2) = Bipyramid.alpha ν := by
  funext x
  have hQ : ∀ y, 0 < y → y ≤ 1 / 2 →
      Scaled.Qf ν (1 / 2) y = 4 * Bipyramid.alpha0 ν + ∫ t in y..(1 / 2), Bipyramid.gInt ν t := by
    intro y hy0 hy1
    simp only [Scaled.Qf, Scaled.alpha0, Bipyramid.alpha0, Bipyramid.I1]
    congr 1
    · have : ∀ a : ℝ, 2 * (1 / 2) - a = 1 - a := fun a => by ring
      simp only [this]; ring
    · refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hy1] at ht
      simp only [Scaled.qInt, Scaled.gTail, Bipyramid.gInt]
      rcases eq_or_lt_of_le ht.2 with e | hlt
      · subst e; norm_num
      · have : t < 1 - 1 / 2 := by linarith
        simp only [this, ite_true]
  unfold alpha Bipyramid.alpha Bipyramid.alphaF
  by_cases hx : x ∈ Ioc (0:ℝ) 1
  · have h0 : ¬ x ≤ 0 := not_le.2 hx.1
    rw [indicator_of_mem hx]
    by_cases hx2 : x ≤ 1 / 2
    · simp only [h0, hx2, ite_true, ite_false]
      rw [alphaL_low hx2, hQ x hx.1 hx2]
    · simp only [h0, hx2, hx.2, ite_true, ite_false]
      rw [alphaL_high (not_le.1 hx2)]
  · rw [indicator_of_notMem hx]
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · simp only [hx, ite_true]
    · have h1 : ¬ x ≤ 0 := by linarith
      have h2 : ¬ x ≤ 1 / 2 := by linarith
      have h3 : ¬ x ≤ 1 := not_le.2 hx
      simp only [h1, h2, h3, ite_false]

/-- **Lemma 82, last sentence**: for `h = 1/2` the construction is that of Lemma 69. -/
theorem levelMix82_half (ν : ℝ → ℝ) : levelMix82 ν (1 / 2) = Bipyramid.levelMix ν := by
  have hd : delta (1 / 2) = Bipyramid.delta := by
    funext a; simp only [delta, Bipyramid.delta]; ring_nf
  have hP : P0 ν (1 / 2) = Bipyramid.P0 ν := by
    simp only [P0, Bipyramid.P0, muA, Bipyramid.muA, alpha_half]
  have hz : ∀ b σ, zmap (1 / 2) b σ = Bipyramid.zmap b σ := by
    intro b σ
    funext p i
    simp only [zmap, Bipyramid.zmap, W, Bipyramid.W, Bv, Bipyramid.Bv, Cv, Bipyramid.Cv, hd]
  simp only [levelMix82, Bipyramid.levelMix, hP, hz]

end Levels82

/-! ## Analytic facts on even concave profiles -/

section Profile

variable {r : ℝ → ℝ}

/-- An even function, concave on `[-1, 1]`, is non-increasing on `[0, 1]`. -/
lemma antitoneOn_of_even_concave (hconc : ConcaveOn ℝ (Icc (-1) 1) r)
    (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z) : AntitoneOn r (Icc 0 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le (hx.1.trans hxy) with hy0 | hy0
  · have : x = y := by linarith [hx.1]
    rw [this]
  set θ := (y - x) / (2 * y)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : 0 ≤ 1 - θ := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith [hx.1]
  have := hconc.2 (show -y ∈ Icc (-1:ℝ) 1 from ⟨by linarith [hy.2], by linarith⟩)
    (show y ∈ Icc (-1:ℝ) 1 from ⟨by linarith, hy.2⟩) hθ0 hθ1 (by ring)
  simp only [smul_eq_mul] at this
  have e : θ * -y + (1 - θ) * y = x := by simp only [θ]; field_simp; ring
  rw [e, heven y ⟨by linarith, hy.2⟩] at this
  linarith

/-- A function that is concave and continuous on `[-1, 1]` and non-increasing on `[0, 1]` is
absolutely continuous on `[0, 1]` (it is Lipschitz on each `[0, c]`, `c < 1`, and equals the
integral of its derivative, which is integrable because the function is monotone). -/
lemma ac_of_concave (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hcont : ContinuousOn r (Icc (-1) 1))
    (hanti : AntitoneOn r (Icc 0 1)) : AbsolutelyContinuousOnInterval r 0 1 := by
  -- Lipschitz on `[0, c]` for `c < 1`
  have hbdd : Bornology.IsBounded (r '' Metric.ball (0:ℝ) 1) := by
    refine (isCompact_Icc.image_of_continuousOn hcont).isBounded.subset (image_mono ?_)
    intro x hx
    rw [Real.ball_eq_Ioo] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hball : ConcaveOn ℝ (Metric.ball (0:ℝ) 1) r := by
    refine hconc.subset (fun x hx => ?_) (convex_ball _ _)
    rw [Real.ball_eq_Ioo] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hacc : ∀ c, 0 ≤ c → c < 1 → AbsolutelyContinuousOnInterval r 0 c := by
    intro c hc0 hc1
    obtain ⟨K, hK⟩ := hball.exists_lipschitzOnWith_of_isBounded
      (show (c + 1) / 2 < 1 by linarith) hbdd
    refine (hK.mono fun x hx => ?_).absolutelyContinuousOnInterval
    rw [uIcc_of_le hc0] at hx
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith [hx.1, hx.2]
  -- the derivative is integrable on `[0, 1]`
  have hneg : MonotoneOn (fun x => -r x) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    intro x hx y hy hxy; simp only [neg_le_neg_iff]; exact hanti hx hy hxy
  have hg : IntervalIntegrable (deriv r) volume 0 1 := by
    have := hneg.intervalIntegrable_deriv.neg
    refine this.congr fun x _ => ?_
    simp
  -- `r x = r 0 + ∫_0^x r'` on `[0, 1)`, then on `[0, 1]` by continuity
  set G : ℝ → ℝ := fun x => r 0 + ∫ t in (0:ℝ)..x, deriv r t
  have hEq : EqOn r G (Ico 0 1) := by
    intro x hx
    simp only [G]
    rw [(hacc x hx.1 hx.2).integral_deriv_eq_sub]; ring
  have hGc : ContinuousOn G (Icc 0 1) := by
    have := continuousOn_primitive_interval' hg (left_mem_uIcc (a := (0:ℝ)) (b := 1))
    rw [uIcc_of_le zero_le_one] at this
    exact continuousOn_const.add this
  have hrc : ContinuousOn r (Icc 0 1) := hcont.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hEq' : EqOn r G (Icc 0 1) :=
    hEq.of_subset_closure hrc hGc Ico_subset_Icc_self (by rw [closure_Ico zero_ne_one])
  have hGac : AbsolutelyContinuousOnInterval G 0 1 := by
    have h1 := hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
    have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => r 0) 0 1 :=
      (LipschitzWith.const (r 0)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h0.add h1
  refine hGac.congr ?_
  rw [uIcc_of_le zero_le_one]
  exact hEq'.symm

/-- Powers of absolutely continuous functions are absolutely continuous. -/
lemma ac_pow {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (d : ℕ) :
    AbsolutelyContinuousOnInterval (fun x => f x ^ d) a b := by
  induction d with
  | zero => simpa using (LipschitzWith.const (1:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ d ih =>
    have := ih.mul hf
    refine this.congr fun x _ => ?_
    simp [pow_succ]

end Profile

/-! ## The level distribution of a symmetric body -/

section LevelDist

variable {r : ℝ → ℝ}

/-- `r` with its argument clamped to `[-1, 1]`: continuous on `ℝ` when `r` is continuous on
`[-1, 1]`, and equal to `r` there. -/
def clampR (r : ℝ → ℝ) (s : ℝ) : ℝ := r (max (-1) (min 1 s))

lemma clampR_eq {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) : clampR r s = r s := by
  simp [clampR, min_eq_right hs.2, max_eq_right hs.1]

lemma continuous_clampR (hcont : ContinuousOn r (Icc (-1) 1)) : Continuous (clampR r) :=
  hcont.comp_continuous (by fun_prop)
    (fun s => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)

lemma clampR_neg (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z) (s : ℝ) :
    clampR r (-s) = clampR r s := by
  have hcl : max (-1) (min 1 (-s)) = -max (-1) (min 1 s) := by
    simp only [max_def, min_def]; split_ifs <;> linarith
  simp only [clampR]
  rw [hcl, heven _ ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩]

/-- The normalised density `ν = r^d / ∫_0^1 r^d` of the absolute value of the level. -/
def nuR (r : ℝ → ℝ) (d : ℕ) (a : ℝ) : ℝ := clampR r a ^ d / ∫ x in (0:ℝ)..1, clampR r x ^ d

lemma map_neg_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map Neg.neg = volume.withDensity (fun x => f (-x)) := by
  ext T hT
  rw [Measure.map_apply measurable_neg hT, withDensity_apply _ (measurable_neg hT),
    withDensity_apply _ hT]
  have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage hT
    (f := fun x => f (-x)) (hf.comp measurable_neg)
  simpa using this

/-- For `r` even, nonnegative and continuous on `[-1, 1]` and positive on `(-1, 1)`, the level
distribution of the body (density `∝ r^d` on `[-1, 1]`) is the symmetric distribution whose
absolute value has the density `ν = r^d / ∫_0^1 r^d`. -/
theorem levelDist_eq_symNu (hcont : ContinuousOn r (Icc (-1) 1))
    (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
    (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) (d : ℕ) :
    Homothetic.levelDist (-1) 1 (clampR r) d = Bipyramid.symNu (nuR r d) := by
  have hc := continuous_clampR hcont
  have hc0 : ∀ s ∈ Icc (-1:ℝ) 1, 0 ≤ clampR r s := fun s hs => by rw [clampR_eq hs]; exact hr0 s hs
  have hcp : ∀ s ∈ Ioo (-1:ℝ) 1, 0 < clampR r s := fun s hs => by
    rw [clampR_eq (Ioo_subset_Icc_self hs)]; exact hpos s hs
  have hcl : ∀ s : ℝ, max (-1) (min 1 (-s)) = -max (-1) (min 1 s) := by
    intro s; simp only [max_def, min_def]; split_ifs <;> linarith
  have hcev : ∀ s, clampR r (-s) = clampR r s := by
    intro s
    simp only [clampR]
    rw [hcl, heven _ ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩]
  set Z := ∫ x in (0:ℝ)..1, clampR r x ^ d with hZ
  have hZpos : 0 < Z := by
    have := Homothetic.levelZ_pos (d := d) (show (0:ℝ) < 1 by norm_num) hc
      (fun s hs => hc0 s ⟨by linarith [hs.1], hs.2⟩) (fun s hs => hcp s ⟨by linarith [hs.1], hs.2⟩)
    simpa [Homothetic.levelZ] using this
  have hpc : Continuous fun x => clampR r x ^ d := hc.pow d
  have hZ2 : Homothetic.levelZ (-1) 1 (clampR r) d = 2 * Z := by
    simp only [Homothetic.levelZ]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hpc.intervalIntegrable _ _) (hpc.intervalIntegrable _ _)]
    have : ∫ x in (-1:ℝ)..0, clampR r x ^ d = Z := by
      calc ∫ x in (-1:ℝ)..0, clampR r x ^ d = ∫ x in (-1:ℝ)..(-0), clampR r x ^ d := by
            norm_num
        _ = ∫ x in (0:ℝ)..1, clampR r (-x) ^ d :=
            (intervalIntegral.integral_comp_neg (fun x => clampR r x ^ d)).symm
        _ = Z := by simp only [hcev, hZ]
    rw [this]; ring
  have hN : Homothetic.levelNorm (-1) 1 (clampR r) d = ENNReal.ofReal (2 * Z) := by
    rw [Homothetic.levelNorm_eq (by norm_num) hc hc0, hZ2]
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((Icc (0:ℝ) 1).indicator (nuR r d) x) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp (Measurable.indicator ?_ measurableSet_Icc)
    exact ((hc.pow d).div_const _).measurable
  rw [Homothetic.levelDist_eq hc, Bipyramid.symNu, Bipyramid.nuMeas, map_neg_withDensity hfm,
    ← withDensity_add_left hfm,
    ← withDensity_smul _ (hfm.add (show Measurable fun x => f (-x) from
      hfm.comp measurable_neg)),
    ← withDensity_smul _ (show Measurable fun s =>
      ENNReal.ofReal (Homothetic.levelFun (-1) 1 (clampR r) d s) from
      ENNReal.measurable_ofReal.comp (Homothetic.measurable_levelFun hc))]
  refine withDensity_congr_ae ?_
  have hx0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [hx0] with x hx
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hf, hN, Homothetic.levelFun]
  have key : ∀ y, 0 < y → y ≤ 1 →
      (ENNReal.ofReal (2 * Z))⁻¹ * ENNReal.ofReal (clampR r y ^ d) =
        2⁻¹ * ENNReal.ofReal (nuR r d y) := by
    intro y hy0 hy1
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
      show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (2⁻¹) by simp, ← ENNReal.ofReal_mul (by norm_num),
      nuR, ← hZ]
    congr 1; field_simp
  rcases lt_or_gt_of_ne hx with hx | hx
  · by_cases hx1 : -1 ≤ x
    · rw [indicator_of_mem (show x ∈ Icc (-1:ℝ) 1 from ⟨hx1, by linarith⟩),
        indicator_of_notMem (show x ∉ Icc (0:ℝ) 1 from fun hh => by linarith [hh.1]),
        indicator_of_mem (show -x ∈ Icc (0:ℝ) 1 from ⟨by linarith, by linarith⟩),
        ← hcev x, key (-x) (by linarith) (by linarith)]
      simp
    · push Not at hx1
      rw [indicator_of_notMem (show x ∉ Icc (-1:ℝ) 1 from fun hh => by linarith [hh.1]),
        indicator_of_notMem (show x ∉ Icc (0:ℝ) 1 from fun hh => by linarith [hh.1]),
        indicator_of_notMem (show -x ∉ Icc (0:ℝ) 1 from fun hh => by linarith [hh.2])]
      simp
  · by_cases hx1 : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Icc (-1:ℝ) 1 from ⟨by linarith, hx1⟩),
        indicator_of_mem (show x ∈ Icc (0:ℝ) 1 from ⟨hx.le, hx1⟩),
        indicator_of_notMem (show -x ∉ Icc (0:ℝ) 1 from fun hh => by linarith [hh.1]),
        key x hx hx1]
      simp
    · push Not at hx1
      rw [indicator_of_notMem (show x ∉ Icc (-1:ℝ) 1 from fun hh => by linarith [hh.2]),
        indicator_of_notMem (show x ∉ Icc (0:ℝ) 1 from fun hh => by linarith [hh.2]),
        indicator_of_notMem (show -x ∉ Icc (0:ℝ) 1 from fun hh => by linarith [hh.1])]
      simp

/-- `symNu ν` is symmetric. -/
lemma symNu_map_neg (ν : ℝ → ℝ) : (Bipyramid.symNu ν).map Neg.neg = Bipyramid.symNu ν := by
  have : (Neg.neg ∘ Neg.neg : ℝ → ℝ) = id := by funext x; simp
  rw [Bipyramid.symNu, Measure.map_smul, Measure.map_add _ _ measurable_neg,
    Measure.map_map measurable_neg measurable_neg, this, Measure.map_id, add_comm]
  exact measurable_neg.aemeasurable

end LevelDist

/-! ## Theorem 83 for the body -/

section Thm83Body

open Homothetic Module

variable {r : ℝ → ℝ} {h : ℝ}

lemma condF_clampR (hF : Scaled.CondF r h) (hh : 1 / 2 ≤ h) :
    Scaled.CondF (clampR r) h := by
  intro c hc0 hc1
  have m : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ∈ Icc (-1:ℝ) 1 := fun x h0 h1 => ⟨by linarith, h1⟩
  rw [clampR_eq (m c hc0 (by linarith)), clampR_eq (m h (by linarith) (by linarith)),
    clampR_eq (m (h + c) (by linarith) (by linarith))]
  exact hF c hc0 hc1

lemma condP_clampR {k : ℕ} (hP : Scaled.CondP r h k) (hh : 1 / 2 ≤ h) (hh1 : h < 1) :
    Scaled.CondP (clampR r) h k := by
  have hE : EqOn (fun a => clampR r a ^ (k - 1) / (2 * h - a))
      (fun a => r a ^ (k - 1) / (2 * h - a)) (uIcc h 1) := by
    intro a ha
    rw [uIcc_of_le hh1.le] at ha
    simp only
    rw [clampR_eq ⟨by linarith [ha.1], ha.2⟩]
  have hEh : clampR r h = r h := clampR_eq ⟨by linarith, hh1.le⟩
  refine ⟨hP.1.congr fun a ha => (hE (uIoc_subset_uIcc ha)).symm, ?_⟩
  · rw [intervalIntegral.integral_congr hE, hEh]; exact hP.2

/-- The hypotheses of Lemma 82 hold for `ν = r^d / ∫_0^1 r^d` (proof of Theorem 83). -/
theorem hyp82_of_profile (hcont : ContinuousOn r (Icc (-1) 1))
    (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z) (hconc : ConcaveOn ℝ (Icc (-1) 1) r)
    (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z) (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) (d : ℕ)
    (hh : 1 / 2 ≤ h) (hh1 : h < 1) (hP : Scaled.CondP r h (d + 1)) :
    Hyp82 (nuR r d) h := by
  have hc := continuous_clampR hcont
  have hc0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ clampR r s := fun s hs => by
    rw [clampR_eq ⟨by linarith [hs.1], hs.2⟩]; exact hr0 s ⟨by linarith [hs.1], hs.2⟩
  set Z := ∫ x in (0:ℝ)..1, clampR r x ^ d with hZ
  have hZpos : 0 < Z := by
    have := Homothetic.levelZ_pos (d := d) (show (0:ℝ) < 1 by norm_num) hc hc0
      (fun s hs => by
        rw [clampR_eq ⟨by linarith [hs.1], hs.2.le⟩]; exact hpos s ⟨by linarith [hs.1], hs.2⟩)
    simpa [Homothetic.levelZ] using this
  have hanti0 := antitoneOn_of_even_concave hconc heven
  have hanti : AntitoneOn (clampR r) (Icc 0 1) := by
    intro x hx y hy hxy
    rw [clampR_eq ⟨by linarith [hx.1], hx.2⟩, clampR_eq ⟨by linarith [hy.1], hy.2⟩]
    exact hanti0 hx hy hxy
  have hac0 := ac_of_concave hconc hcont hanti0
  have hac : AbsolutelyContinuousOnInterval (clampR r) 0 1 := by
    refine hac0.congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact (clampR_eq ⟨by linarith [hx.1], hx.2⟩).symm
  have hPc := condP_clampR hP hh hh1
  rw [Scaled.condP_iff_nu (d + 1) hZpos] at hPc
  simp only [Nat.add_sub_cancel] at hPc
  refine ⟨hh, hh1, fun x hx => div_nonneg (pow_nonneg (hc0 x hx) d) hZpos.le, ?_,
    fun x hx y hy hxy => ?_, ?_, hPc.1, hPc.2⟩
  · simp only [nuR, ← hZ]
    rw [intervalIntegral.integral_div, div_self hZpos.ne']
  · simp only [nuR, ← hZ]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hc0 y hy) (hanti hx hy hxy) d) hZpos.le
  · refine ((ac_pow hac d).const_mul Z⁻¹).congr fun x _ => ?_
    simp only [nuR, ← hZ]; ring

/-- The fibre condition `2 max_i r(Z_i) ≤ ∑_i r(Z_i)` for levels with the shape of Lemma 82
(proof of Theorem 83). -/
theorem fibre_of_shape (hanti : AntitoneOn (clampR r) (Icc 0 1))
    (heven : ∀ s, clampR r (-s) = clampR r s) (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hF : Scaled.CondF (clampR r) h) {z : Fin 3 → ℝ} (hz : LevelShape h z) :
    ∀ k, 2 * clampR r (z k) ≤ ∑ i, clampR r (z i) := by
  set g := clampR r
  have habs : ∀ x, g x = g |x| := by
    intro x; rcases abs_choice x with e | e <;> rw [e]; exact (heven x).symm
  obtain ⟨h1, σ, hA, hB, hC⟩ := hz
  have key := Scaled.thm83_fibre_max hanti hh hh1 hF (abs_nonneg _) (abs_nonneg _) hB hC hA
    (h1 (σ 0))
  have hsum : ∑ i, g (z i) = g |z (σ 0)| + g |z (σ 1)| + g |z (σ 2)| := by
    rw [← Equiv.sum_comp σ (fun i => g (z i)), Fin.sum_univ_three, ← habs, ← habs, ← habs]
  intro k
  rw [hsum, habs]
  have hk : k = σ (σ.symm k) := (Equiv.apply_symm_apply σ k).symm
  rw [hk]
  generalize σ.symm k = j
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    linarith [le_max_left (g |z (σ 0)|) (max (g |z (σ 1)|) (g |z (σ 2)|)),
      le_max_right (g |z (σ 0)|) (max (g |z (σ 1)|) (g |z (σ 2)|)),
      le_max_left (g |z (σ 1)|) (g |z (σ 2)|), le_max_right (g |z (σ 1)|) (g |z (σ 2)|)]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The body `K = {(z, y) : |z| ≤ 1, y ∈ r(z) F}` of Theorem 83, with the level written first. -/
def bodyK (r : ℝ → ℝ) (F : Set V) : Set (ℝ × V) := {p | |p.1| ≤ 1 ∧ p.2 ∈ r p.1 • F}

lemma bodyK_eq (r : ℝ → ℝ) (F : Set V) :
    bodyK r F = body (-1) 1 (clampR r) (fun s => (0:V) + s • (0:V)) F := by
  ext ⟨z, y⟩
  simp only [bodyK, body, secMap, mem_image, mem_prod, Prod.mk.injEq,
    smul_zero, add_zero, Prod.exists, mem_Icc]
  simp only [mem_ofPred_eq, Set.mem_smul_set, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, x, hx, rfl⟩
    exact ⟨z, x, ⟨⟨h1, h2⟩, hx⟩, rfl, by rw [clampR_eq ⟨h1, h2⟩, zero_add]⟩
  · rintro ⟨s, x, ⟨⟨h1, h2⟩, hx⟩, rfl, rfl⟩
    exact ⟨⟨h1, h2⟩, x, hx, by rw [clampR_eq ⟨h1, h2⟩, zero_add]⟩

/-- The joint mixes of the scaling property of `F` (with translations `0`), in the form used by
Theorem 62. -/
lemma mixer_of_scaling {F : Set V} {m : ℝ} (hsp : ScalingProperty (unifSet F) m) {n : ℕ}
    (hn : 2 ≤ n) : ∃ Φ : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → V),
      Measurable (Function.uncurry Φ) ∧
      ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) → (∀ k, m * lam k ≤ ∑ i, lam i) →
        IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (unifSeq.map (Φ lam)) := by
  obtain ⟨Φ, hΦ, hmix⟩ := hsp n hn
  refine ⟨fun lam ω => Φ (lam, 0) ω, ?_, fun lam h1 h2 h3 => ?_⟩
  · exact hΦ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  · have := hmix lam 0 h1 h2 h3
    simpa using this

section Setting

variable {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
  (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
  (hcont : ContinuousOn r (Icc (-1) 1)) (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z)
  (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
  (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z)
include hF hFi hcen hk hcont heven hconc hr0 hpos

/-- **Theorem 83** (`g:thm:bipyr`), the complete mix for `n = 3`. Let `k - 1 = dim V ≥ 1`, `F`
compact with nonempty interior and centroid `0`, and `Φ` the joint mix of `U(λ₁F), U(λ₂F), U(λ₃F)`
given by the scaling property of `F` with constant `2`. Let `r` be even, concave, continuous and
`≥ 0` on `[-1, 1]`, positive on `(-1, 1)`, and suppose `(P_h)` and `(F_h)` for some
`h ∈ [1/2, 1)`. Then `X_i = (Z_i, W_i)`, with `(Z₁, Z₂, Z₃)` the levels of Lemma 82 for
`ν = r^{k-1} / ∫_0^1 r^{k-1}` and, given them, `W` the joint mix of the `U(r(Z_i) F)` given by `Φ`,
is a `3`-complete mix of `U(K)`, `K = {(z, y) : |z| ≤ 1, y ∈ r(z) F}`. -/
theorem thm83_three (hh : 1 / 2 ≤ h) (hh1 : h < 1) (hP : Scaled.CondP r h (finrank ℝ V + 1))
    (hFh : Scaled.CondF r h) {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω}
    [IsProbabilityMeasure ρ] {Φ : (Fin 3 → ℝ) → Ω → (Fin 3 → V)}
    (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin 3 → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, 2 * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam))) :
    IsCompleteMix 3 (unifSet (bodyK r F))
      (homMix (clampR r) (fun s => (0:V) + s • (0:V)) 2 Φ
        (levelMix82 (nuR r (finrank ℝ V)) h) ρ) := by
  set d := finrank ℝ V
  have hc := continuous_clampR hcont
  have hc0 : ∀ s ∈ Icc (-1:ℝ) 1, 0 ≤ clampR r s := fun s hs => by
    rw [clampR_eq hs]; exact hr0 s hs
  have hcp : ∀ s ∈ Ioo (-1:ℝ) 1, 0 < clampR r s := fun s hs => by
    rw [clampR_eq (Ioo_subset_Icc_self hs)]; exact hpos s hs
  have H := hyp82_of_profile hcont heven hconc hr0 hpos d hh hh1 hP
  obtain ⟨-, -, hmixL, -, hshape⟩ := levels82 H
  have hanti : AntitoneOn (clampR r) (Icc 0 1) := by
    intro x hx y hy hxy
    rw [clampR_eq ⟨by linarith [hx.1], hx.2⟩, clampR_eq ⟨by linarith [hy.1], hy.2⟩]
    exact antitoneOn_of_even_concave hconc heven hx hy hxy
  have hfib : ∀ᵐ S ∂(levelMix82 (nuR r d) h), ∀ k, 2 * clampR r (S k) ≤ ∑ i, clampR r (S i) := by
    filter_upwards [hshape] with z hz
    exact fibre_of_shape hanti (clampR_neg heven) hh hh1 (condF_clampR hFh hh) hz
  rw [← levelDist_eq_symNu hcont heven hr0 hpos d] at hmixL
  rw [bodyK_eq]
  exact isCompleteMix_homMix (by norm_num) hc hc0 hcp 0 0 hF hFi hcen hk hΦ hmix
    (by norm_num) hmixL hfib

/-- **Theorem 83**, `n = 2`: the level `Z₂ = -Z₁` and the scaling property of `F` (this is the
paper's `X₂ = -X₁`, written through Theorem 62). -/
theorem thm83_two (hsp : ScalingProperty (unifSet F) 2) :
    CompletelyMixable 2 (unifSet (bodyK r F)) := by
  set d := finrank ℝ V
  have hc := continuous_clampR hcont
  have hc0 : ∀ s ∈ Icc (-1:ℝ) 1, 0 ≤ clampR r s := fun s hs => by
    rw [clampR_eq hs]; exact hr0 s hs
  have hcp : ∀ s ∈ Ioo (-1:ℝ) 1, 0 < clampR r s := fun s hs => by
    rw [clampR_eq (Ioo_subset_Icc_self hs)]; exact hpos s hs
  obtain ⟨Φ, hΦ, hmix⟩ := mixer_of_scaling hsp (le_refl 2)
  set L := levelDist (-1) 1 (clampR r) d
  have hL : L = Bipyramid.symNu (nuR r d) := levelDist_eq_symNu hcont heven hr0 hpos d
  have hLp : IsProbabilityMeasure L := isProbabilityMeasure_levelDist (by norm_num) hc hcp d
  set τ : ℝ → Fin 2 → ℝ := fun s => ![s, -s]
  have hτ : Measurable τ := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact measurable_id
    · exact measurable_neg
  have hP : IsCompleteMix 2 L (L.map τ) := by
    refine ⟨⟨by rw [Measure.map_apply hτ MeasurableSet.univ]; simp⟩, ⟨0, ?_⟩, fun j => ?_⟩
    · rw [ae_map_iff hτ.aemeasurable (measurableSet_eq_fun (Finset.measurable_sum _
        fun i _ => measurable_pi_apply i) measurable_const)]
      exact ae_of_all _ fun s => by simp [τ, Fin.sum_univ_two]
    · rw [Measure.map_map (measurable_pi_apply j) hτ]
      fin_cases j
      · exact Measure.map_id
      · change L.map Neg.neg = L
        rw [hL]; exact symNu_map_neg _
  have hfib : ∀ᵐ S ∂(L.map τ), ∀ k, 2 * clampR r (S k) ≤ ∑ i, clampR r (S i) := by
    have hm : ∀ k : Fin 2, Measurable fun S : Fin 2 → ℝ => clampR r (S k) :=
      fun k => hc.measurable.comp (measurable_pi_apply k)
    have hset : MeasurableSet
        {S : Fin 2 → ℝ | ∀ k, 2 * clampR r (S k) ≤ ∑ i, clampR r (S i)} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_le
        (measurable_const.mul (hm k)) (Finset.measurable_sum _ fun i _ => hm i)
    rw [ae_map_iff hτ.aemeasurable hset]
    refine ae_of_all _ fun s k => ?_
    simp only [τ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      clampR_neg heven]
    fin_cases k <;> simp [clampR_neg heven] <;> linarith
  rw [bodyK_eq]
  exact ⟨_, isCompleteMix_homMix (by norm_num) hc hc0 hcp 0 0 hF hFi hcen hk hΦ hmix
    (le_refl 2) hP hfib⟩

/-- **Theorem 83** (`g:thm:bipyr`). Let `k - 1 = dim V ≥ 1`, let `F ⊆ V` be compact with
nonempty interior (dimension `k - 1`), centroid `0` and the scaling property with constant `2`,
let `r : [-1, 1] → [0, ∞)` be even, concave and continuous, and positive on `(-1, 1)`, and let
`K = {(z, y) : |z| ≤ 1, y ∈ r(z) F}` (level written first). If `(P_h)` and `(F_h)` hold for some
`h ∈ [1/2, 1)`, then `U(K)` is `n`-completely mixable for every `n ≥ 2`. -/
theorem thm83 (hsp : ScalingProperty (unifSet F) 2) (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hP : Scaled.CondP r h (finrank ℝ V + 1)) (hFh : Scaled.CondF r h) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (bodyK r F)) := by
  have h2 := thm83_two hF hFi hcen hk hcont heven hconc hr0 hpos hsp
  have h3 : CompletelyMixable 3 (unifSet (bodyK r F)) := by
    obtain ⟨Φ, hΦ, hmix⟩ := mixer_of_scaling hsp (show 2 ≤ 3 by norm_num)
    exact ⟨_, thm83_three hF hFi hcen hk hcont heven hconc hr0 hpos hh hh1 hP hFh hΦ hmix⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · exact h2
    · exact h3
    · have := ScaledB.completelyMixable_add_add (ih (n - 2) (by omega) (by omega)) h2
      rwa [show n - 2 + 2 = n by omega] at this

end Setting

end Thm83Body

/-! ## Corollary 84 (b) -/

section Cor84b

variable {r : ℝ → ℝ}

/-- `(P_h)` for the tail `r(a) = σ (1 - a)` on `[h, 1]`, `1/2 ≤ h < 1`, `σ ≥ 0`, `k ≥ 3`:
`2 ∫_h^1 r^{k-1}/(2h - a) ≤ 2 σ^{k-1} (1-h)^{k-1}/(k-1) ≤ (σ (1 - h))^{k-1}`. -/
theorem condP_of_tail {h σ : ℝ} (hh : 1 / 2 ≤ h) (hh1 : h < 1) (hσ : 0 ≤ σ) {k : ℕ}
    (hk : 3 ≤ k) (haff : ∀ a ∈ Icc h 1, r a = σ * (1 - a)) : Scaled.CondP r h k := by
  set q : ℝ → ℝ := fun a => (σ * (1 - a)) ^ (k - 1) / (2 * h - a)
  set g : ℝ → ℝ := fun a => σ ^ (k - 1) * (1 - a) ^ (k - 2)
  have hg : Continuous g := by fun_prop
  have hae : ∀ᵐ a ∂(volume.restrict (uIoc h 1)), r a ^ (k - 1) / (2 * h - a) = q a := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun a ha => ?_)
    rw [uIoc_of_le hh1.le] at ha
    simp only [q, haff a ⟨ha.1.le, ha.2⟩]
  have hqg : ∀ a ∈ Ioc h 1, 0 ≤ q a ∧ q a ≤ g a := by
    intro a ha
    have h1a : 0 ≤ 1 - a := by linarith [ha.2]
    have hd : 1 - a ≤ 2 * h - a := by linarith
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    simp only [q, g]
    rw [mul_pow, hk1, pow_succ (1 - a)]
    rcases eq_or_lt_of_le h1a with e | hpos
    · rw [← e]; simp only [mul_zero, zero_div]; exact ⟨le_rfl, by positivity⟩
    have hP : 0 ≤ σ ^ (k - 2 + 1) * (1 - a) ^ (k - 2) := by positivity
    refine ⟨div_nonneg (by positivity) (by linarith), ?_⟩
    calc σ ^ (k - 2 + 1) * ((1 - a) ^ (k - 2) * (1 - a)) / (2 * h - a)
        = σ ^ (k - 2 + 1) * (1 - a) ^ (k - 2) * (1 - a) / (2 * h - a) := by ring
      _ ≤ σ ^ (k - 2 + 1) * (1 - a) ^ (k - 2) := by
          rw [div_le_iff₀ (by linarith)]; exact mul_le_mul_of_nonneg_left hd hP
  have hqm : AEStronglyMeasurable q (volume.restrict (uIoc h 1)) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (by fun_prop : Measurable fun a : ℝ => (σ * (1 - a)) ^ (k - 1)).div (by fun_prop)
  have hqi : IntervalIntegrable q volume h 1 := by
    refine (intervalIntegrable_iff.2 ?_)
    refine Integrable.mono' (intervalIntegrable_iff.1 (hg.intervalIntegrable h 1)) hqm ?_
    · refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun a ha => ?_)
      rw [uIoc_of_le hh1.le] at ha
      rw [Real.norm_eq_abs, abs_of_nonneg (hqg a ha).1]; exact (hqg a ha).2
  have hint : IntervalIntegrable (fun a => r a ^ (k - 1) / (2 * h - a)) volume h 1 :=
    hqi.congr_ae (by simpa [Filter.EventuallyEq] using
      (show ∀ᵐ a ∂(volume.restrict (uIoc h 1)), q a = r a ^ (k - 1) / (2 * h - a) from
        hae.mono fun a ha => ha.symm))
  refine ⟨hint, ?_⟩
  have hgint : ∫ a in h..1, g a = σ ^ (k - 1) * (1 - h) ^ (k - 1) / (k - 1) := by
    simp only [g]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ (k - 2)) 1, integral_pow]
    have e : k - 2 + 1 = k - 1 := by omega
    have hk1 : ((k - 2 : ℕ) : ℝ) + 1 = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e, hk1, sub_self, zero_pow (by omega), sub_zero]
    ring
  have hle : ∫ a in h..1, r a ^ (k - 1) / (2 * h - a) ≤ ∫ a in h..1, g a := by
    rw [intervalIntegral.integral_congr_ae ((ae_restrict_iff' measurableSet_uIoc).1 hae)]
    refine intervalIntegral.integral_mono_ae_restrict hh1.le hqi (hg.intervalIntegrable h 1) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [Measure.ae_ne volume h] with a hah ha
    exact (hqg a ⟨lt_of_le_of_ne ha.1 (Ne.symm hah), ha.2⟩).2
  rw [hgint] at hle
  rw [haff h ⟨le_rfl, hh1.le⟩, mul_pow]
  have hk1 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpos : 0 ≤ σ ^ (k - 1) * (1 - h) ^ (k - 1) := by
    have : 0 ≤ 1 - h := by linarith
    positivity
  calc 2 * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a)
      ≤ 2 * (σ ^ (k - 1) * (1 - h) ^ (k - 1) / (k - 1)) := by linarith
    _ ≤ σ ^ (k - 1) * (1 - h) ^ (k - 1) := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith

/-- **Corollary 84 (b)**, the conditions: let `r ≥ 0` be concave and non-increasing on `[0, 1]`,
with `r = r(0)` on `[0, h']` and `r(a) = r(0)(1 - a)/(1 - h')` on `[h', 1]` (affine with
`r(1) = 0`), `0 ≤ h' < 1`, and `k ≥ 3`. Then `(F_h)` and `(P_h)` hold for some `h ∈ [1/2, 1)`:
`h = 1/2` if `h' < 1/2` (Theorem 70), `h = h'` otherwise. -/
theorem cor84b_cond (hanti : AntitoneOn r (Icc 0 1)) (hconc : ConcaveOn ℝ (Icc 0 1) r)
    (hr00 : 0 ≤ r 0) {h' : ℝ} (h0 : 0 ≤ h') (h1 : h' < 1)
    (hflat : ∀ a ∈ Icc 0 h', r a = r 0) (haff : ∀ a ∈ Icc h' 1, r a = r 0 * (1 - a) / (1 - h'))
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ h, 1 / 2 ≤ h ∧ h < 1 ∧ Scaled.CondF r h ∧ Scaled.CondP r h k := by
  have h1' : 0 < 1 - h' := by linarith
  set σ := r 0 / (1 - h')
  have hσ : 0 ≤ σ := div_nonneg hr00 h1'.le
  have haff' : ∀ a ∈ Icc h' 1, r a = σ * (1 - a) := fun a ha => by
    rw [haff a ha]; simp only [σ]; ring
  rcases lt_or_ge h' (1 / 2) with hlt | hge
  · refine ⟨1 / 2, le_rfl, by norm_num, ?_, ?_⟩
    · have := Scaled.condF_of_affine (σ := σ) hconc le_rfl (by norm_num) fun a ha => by
        rw [haff' a ⟨by linarith [ha.1], ha.2⟩]; ring
      exact this.2
    · exact condP_of_tail le_rfl (by norm_num) hσ hk fun a ha =>
        haff' a ⟨by linarith [ha.1], ha.2⟩
  · refine ⟨h', hge, h1, ?_, condP_of_tail hge h1 hσ hk fun a ha => haff' a ha⟩
    refine Scaled.condF_of_crude hanti hge h1 ?_
    rw [hflat h' ⟨h0, le_rfl⟩, haff 1 ⟨h1.le, le_rfl⟩]
    simp

open Module in
/-- **Corollary 84 (b)** (`g:cor:flat`), for the body: in the setting of Theorem 83 with
`k = dim V + 1 ≥ 3`, if `r = r(0)` on `[0, h']` and `r` is affine on `[h', 1]` with `r(1) = 0`
(`r(a) = r(0)(1 - a)/(1 - h')`), `0 ≤ h' < 1` (the elongated bipyramids
`conv((F × [-h', h']) ∪ {(0, ±1)})`), then `U(K)` is `n`-completely mixable for every `n ≥ 2`. -/
theorem cor84b {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]
    {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 2 ≤ finrank ℝ V)
    (hsp : ScalingProperty (unifSet F) 2)
    (hcont : ContinuousOn r (Icc (-1) 1)) (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z)
    (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
    (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) {h' : ℝ} (h0 : 0 ≤ h') (h1 : h' < 1)
    (hflat : ∀ a ∈ Icc 0 h', r a = r 0) (haff : ∀ a ∈ Icc h' 1, r a = r 0 * (1 - a) / (1 - h'))
    {n : ℕ} (hn : 2 ≤ n) : CompletelyMixable n (unifSet (bodyK r F)) := by
  obtain ⟨h, hh, hh1, hFh, hP⟩ := cor84b_cond (antitoneOn_of_even_concave hconc heven)
    (hconc.subset (Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc 0 1))
    (hr0 0 ⟨by norm_num, by norm_num⟩) h0 h1 hflat haff (k := finrank ℝ V + 1) (by omega)
  exact thm83 hF hFi hcen (by omega) hcont heven hconc hr0 hpos hsp hh hh1 hP hFh hn

end Cor84b

/-! ## Theorem 79: frusta are hulls, `𝒦 ⊂ 𝒦⁺` for the frustum step -/

section FrustumHull

open Module ScaledB

section Image

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

/-- A bijective affine map between spaces with Haar measures multiplies volumes by a constant. -/
lemma volume_image_affineEquiv (L : E ≃L[ℝ] F) (b : F) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ S : Set E, volume ((fun x => L x + b) '' S) = c * volume S := by
  set μ' : Measure F := (volume : Measure E).map L
  have : μ'.IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  have hμ := Measure.isAddLeftInvariant_eq_smul μ' (volume : Measure F)
  set c0 := Measure.addHaarScalarFactor μ' (volume : Measure F)
  have hc0 : (c0 : ℝ≥0∞) ≠ 0 := by
    simpa using (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume).ne'
  refine ⟨(c0 : ℝ≥0∞)⁻¹, by simp, by simpa using hc0, fun S => ?_⟩
  have e1 : (fun x => L x + b) '' S = (fun y => y + b) '' (L '' S) := by
    rw [image_image]
  have e2 : μ' (L '' S) = volume S := by
    have e : μ' = (volume : Measure E).map L.toHomeomorph.toMeasurableEquiv := rfl
    rw [e, MeasurableEquiv.map_apply]
    congr 1
    exact L.toEquiv.preimage_image S
  rw [e1, image_add_right, measure_preimage_add_right]
  rw [hμ, smul_apply, ENNReal.smul_def, smul_eq_mul] at e2
  rw [← e2, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]

/-- The uniform distribution on the image of `K` under a bijective affine map is the image of
`U(K)`. -/
lemma unifSet_image_affineEquiv (L : E ≃L[ℝ] F) (b : F) (K : Set E) :
    unifSet ((fun x => L x + b) '' K) = (unifSet K).map (fun x => L x + b) := by
  obtain ⟨c, hc0, hct, hc⟩ := volume_image_affineEquiv L b
  have hA : Measurable (fun x => L x + b) := (L.continuous.add continuous_const).measurable
  ext T hT
  rw [Measure.map_apply hA hT, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply (hA hT), Measure.restrict_apply hT, smul_eq_mul, smul_eq_mul,
    ← Set.image_preimage_inter, hc, hc, ENNReal.mul_inv (Or.inl hc0) (Or.inl hct),
    mul_mul_mul_comm, ENNReal.inv_mul_cancel hc0 hct, one_mul]

end Image

variable (X : Sp)

/-- The real line as a space of `𝒦⁺`. -/
abbrev spR : Sp := ⟨ℝ⟩

/-- The linear part `(θ, y) ↦ ((1 - q) θ, y 0)` of the affine map that turns the hull of
Corollary 77 with `J = 1`, `a = q`, `b = 1`, `t = 0` into the frustum `K_q`. -/
def frL {q : ℝ} (hq1 : q < 1) : (ℝ × (Fin 1 → X.carrier)) ≃L[ℝ] (ℝ × X.carrier) :=
  ((LinearEquiv.smulOfNeZero ℝ ℝ (1 - q) (by linarith)).prodCongr
    (LinearEquiv.funUnique (Fin 1) ℝ X.carrier)).toContinuousLinearEquiv

lemma frL_apply {q : ℝ} (hq1 : q < 1) (p : ℝ × (Fin 1 → X.carrier)) :
    frL X hq1 p = ((1 - q) * p.1, p.2 0) := rfl

/-- **The frustum as a hull** (proof of Theorem 79): for a convex base `B`, the frustum
`K_q = {(s, s b) : q ≤ s ≤ 1, b ∈ B}` is the image of the hull of Corollary 77 with `J = 1`,
`a = q`, `b = 1`, `t = 0` under `(θ, y) ↦ (q + (1 - q) θ, y 0)`. -/
theorem frustumSet_eq_hull {B : Set X.carrier} (hBc : Convex ℝ B) (hBne : B.Nonempty) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    FrustumMix.frustumSet q B = (fun p => frL X hq1 p + (q, 0)) ''
      hullC (fun _ : Fin 1 => B) (fun _ => q) (fun _ => 1) 0 := by
  rw [hullC_eq (fun _ => hBc) (fun _ => hBne) (fun _ => hq0) (fun _ => zero_le_one)]
  ext ⟨s, x⟩
  simp only [FrustumMix.frustumSet, bodyL, secL, mem_ofPred_eq,
    mem_image, mem_prod, mem_Icc, mem_pi, mem_univ, true_implies, smul_zero, zero_add,
    Prod.exists, frL_apply, Prod.mk_add_mk, add_zero, Prod.mk.injEq]
  have h1q : 0 < 1 - q := by linarith
  constructor
  · rintro ⟨hs0, hs1, y, hy, rfl⟩
    set θ := (s - q) / (1 - q)
    refine ⟨θ, diagMap (Scaled.prof (fun _ => q) fun _ => 1) θ (fun _ => y),
      ⟨θ, fun _ => y, ⟨⟨?_, ?_⟩, fun _ => hy⟩, rfl, rfl⟩, ?_, ?_⟩
    · exact div_nonneg (by linarith) h1q.le
    · rw [div_le_one h1q]; linarith
    · simp only [θ]; field_simp; ring
    · simp only [diagMap, Scaled.prof, θ]
      congr 1; field_simp; ring
  · rintro ⟨a, b, ⟨a1, b1, ⟨⟨h0, h1⟩, hy⟩, rfl, rfl⟩, rfl, rfl⟩
    refine ⟨by nlinarith, by nlinarith, b1 0, hy 0, ?_⟩
    simp only [diagMap, Scaled.prof]
    congr 1; ring

/-- **Theorem 79**, `𝒦 ⊂ 𝒦⁺`, the frustum step: the frustum `K_q` (`0 ≤ q < 1`) over a compact
convex full-dimensional member `B` of `𝒦⁺` of dimension `≥ 1` is a member of `𝒦⁺`, of dimension
`dim B + 1`. -/
theorem KPlus_frustum {B : Set X.carrier} (hB : IsCompact B) (hBc : Convex ℝ B)
    (hBi : (interior B).Nonempty) (hK : KPlus X (unifSet B) (finrank ℝ X.carrier))
    (hk : 1 ≤ finrank ℝ X.carrier) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    KPlus (Sp.prod spR X) (unifSet (FrustumMix.frustumSet q B)) (1 + finrank ℝ X.carrier) := by
  have hH := KPlus.hull (fun _ : Fin 1 => X) (fun _ => B) (fun _ => hB) (fun _ => hBc)
    (fun _ => hBi) (fun _ => hK) (fun _ => hk) (fun _ => q) (fun _ => 1) (fun _ => hq0)
    (fun _ => zero_le_one) (fun _ => by linarith) 0
  simp only [Finset.univ_unique, Finset.sum_singleton] at hH
  have hA := KPlus.affine (Y := Sp.prod spR X) hH (frL X hq1 : _ →L[ℝ] (ℝ × X.carrier))
    (frL X hq1).injective (q, 0)
  rw [frustumSet_eq_hull X hBc (hBi.mono interior_subset) hq0 hq1]
  convert hA using 1
  have : (volume : Measure (ℝ × (Fin 1 → X.carrier))).IsAddHaarMeasure :=
    (Sp.hull fun _ : Fin 1 => X).haar
  have : (volume : Measure (ℝ × X.carrier)).IsAddHaarMeasure := (Sp.prod spR X).haar
  exact unifSet_image_affineEquiv (E := ℝ × (Fin 1 → X.carrier)) (F := ℝ × X.carrier)
    (frL X hq1) (q, 0) _

end FrustumHull

end ScaledC

end Mixes
