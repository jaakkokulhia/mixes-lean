import Mixes.Bridges
import Mixes.Cone

/-!
# One-dimensional projections of uniform distributions on convex bodies (Corollary 68)

Corollary 68 (`o:cor:proj` in `mixes/main.tex`).

* `CompletelyMixable.map_affine`: complete mixability is preserved by `x ↦ a + c x`.
* `concave_extend`: a nonnegative concave function on `(0, 1)` agrees there with a continuous
  concave function on `[0, 1]` (the end point step of the proof of Theorem 67).
* `pconc_Ioo`: **Theorem 67** in the paper's form: a probability density `h ^ p` on `[a, b]`,
  `h ≥ 0` concave on the open interval `(a, b)`, `p ≥ 1`, is `n`-completely mixable for every
  `n ≥ p + 2` (from `Bridges.pconc`).
* `exists_chart`: linear coordinates `L : V ≃ ℝ × ℝ^m` whose first coordinate is `u`.
* `map_unifSet_eq`: the density step: the law of `u(X)`, `X ∼ U(K)`, is proportional to the
  section volume `t ↦ vol_{d-1}{b : L⁻¹(t, b) ∈ K}` (Fubini in the coordinates `L`).
* `BrunnSections`: Brunn's theorem (the `(d-1)`-th root of the section volume of a compact convex
  set is concave on its projection), stated as a proposition; it is not in Mathlib and is a
  hypothesis of `cor68`.
* `cor68`: **Corollary 68**, first statement.
* `cor68_cone`: **Corollary 68**, sharpness: for a cone over a base on which `u` is constant the
  law of `u(X)` is not `n`-completely mixable for `n ≤ d`.
-/

open MeasureTheory Set Filter Topology Module
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Proj

/-! ## Affine images -/

/-- Complete mixability is preserved by the affine maps `x ↦ a + c x` of `ℝ`. -/
theorem CompletelyMixable.map_affine {n : ℕ} {F : Measure ℝ} (h : CompletelyMixable n F)
    (a c : ℝ) : CompletelyMixable n (F.map fun x => a + c * x) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨_, IsJointMix.map_affine hP (AddMonoidHom.mulLeft c) (measurable_const_mul c)
    (fun _ => a)⟩

/-! ## The end point step -/

/-- The right limit at `0` of a nonnegative concave function on `(0, 1)` exists. -/
lemma exists_lim_zero {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ioo 0 1) g)
    (hg0 : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ g x) : ∃ L, Tendsto g (𝓝[>] 0) (𝓝 L) := by
  set s : ℝ → ℝ := fun x => (g x - g (1/2)) / (x - 1/2)
  have hhalf : (1/2 : ℝ) ∈ Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hanti : AntitoneOn s (Ioo 0 (1/4)) := by
    intro x hx y hy hxy
    have hxI : x ∈ Ioo (0:ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have hyI : y ∈ Ioo (0:ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    have := hg.neg.secant_mono hhalf hxI hyI (by linarith [hx.2]) (by linarith [hy.2]) hxy
    simp only [Pi.neg_apply] at this
    have e1 : (-g x - -g (1/2)) / (x - 1/2) = -s x := by simp only [s]; ring
    have e2 : (-g y - -g (1/2)) / (y - 1/2) = -s y := by simp only [s]; ring
    rw [e1, e2] at this
    linarith
  have hbdd : BddAbove (s '' Ioo 0 (1/4)) := by
    refine ⟨4 * g (1/2), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxI : x ∈ Ioo (0:ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have h0 := hg0 x hxI
    have hgh := hg0 _ hhalf
    simp only [s]
    rw [div_le_iff_of_neg (by linarith [hx.2])]
    nlinarith [hx.1, hx.2]
  have hs := hanti.tendsto_nhdsWithin_Ioo_right (by norm_num) hbdd
  refine ⟨g (1/2) + (0 - 1/2) * sSup (s '' Ioo 0 (1/4)), ?_⟩
  have hlin : Tendsto (fun x : ℝ => g (1/2) + (x - 1/2) * s x) (𝓝[>] 0)
      (𝓝 (g (1/2) + (0 - 1/2) * sSup (s '' Ioo 0 (1/4)))) := by
    refine tendsto_const_nhds.add (Tendsto.mul ?_ hs)
    exact ((continuous_id.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  refine hlin.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/4)] with x hx
  have : x - 1/2 ≠ 0 := by linarith [hx.2]
  simp only [s]
  rw [mul_comm, div_mul_cancel₀ _ this]
  ring

/-- A nonnegative concave function on `(0, 1)` agrees on `(0, 1)` with a nonnegative function
that is concave and continuous on `[0, 1]` (its values at the end points are the one-sided
limits). -/
theorem concave_extend {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ioo 0 1) g)
    (hg0 : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ g x) :
    ∃ G : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) G ∧ ContinuousOn G (Icc 0 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, 0 ≤ G x) ∧ ∀ x ∈ Ioo (0:ℝ) 1, G x = g x := by
  obtain ⟨L0, h0⟩ := exists_lim_zero hg hg0
  have hg' : ConcaveOn ℝ (Ioo 0 1) (fun x => g (1 - x)) := by
    refine ⟨convex_Ioo 0 1, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : 1 - x ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : 1 - y ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have := hg.2 hx' hy' ha hb hab
    have e : a • (1 - x) + b • (1 - y) = 1 - (a • x + b • y) := by
      have : b = 1 - a := by linarith
      subst this; simp only [smul_eq_mul]; ring
    rw [e] at this
    exact this
  obtain ⟨L1, h1'⟩ := exists_lim_zero hg' fun x hx =>
    hg0 _ ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hrefl : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have : Tendsto (fun x : ℝ => 1 - x) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · simp only [mem_Ioi, sub_pos]; exact hx
  have h1 : Tendsto g (𝓝[<] 1) (𝓝 L1) := by
    have := h1'.comp hrefl
    simpa [Function.comp_def] using this
  set G : ℝ → ℝ := fun x => if x = 0 then L0 else if x = 1 then L1 else g x with hGdef
  have hGg : ∀ x ∈ Ioo (0:ℝ) 1, G x = g x := fun x hx => by
    simp only [G, hx.1.ne', hx.2.ne, ite_false]
  have hcont : ContinuousOn G (Icc 0 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · rw [show Icc (0:ℝ) 1 = insert 0 (Ioc 0 1) from (insert_left_Ioc zero_le_one).symm,
        continuousWithinAt_insert_self, continuousWithinAt_Ioc_iff_Ioi zero_lt_one]
      have e : G 0 = L0 := by simp [G]
      rw [ContinuousWithinAt, e]
      refine h0.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy using (hGg y hy).symm
    rcases eq_or_lt_of_le hx.2 with rfl | hx1
    · rw [show Icc (0:ℝ) 1 = insert 1 (Ico 0 1) from (insert_right_Ico zero_le_one).symm,
        continuousWithinAt_insert_self, continuousWithinAt_Ico_iff_Iio zero_lt_one]
      have e : G 1 = L1 := by simp [G]
      rw [ContinuousWithinAt, e]
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with y hy using (hGg y hy).symm
    · have hxI : x ∈ Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
      have hc := hg.continuousOn isOpen_Ioo x hxI
      rw [continuousWithinAt_iff_continuousAt (Ioo_mem_nhds hx0 hx1)] at hc
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy using (hGg y hy).symm
  have hpath : ∀ w ∈ Icc (0:ℝ) 1,
      Tendsto (fun e : ℝ => G ((1 - e) * w + e / 2)) (𝓝[>] 0) (𝓝 (G w)) := by
    intro w hw
    refine (hcont w hw).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have : Tendsto (fun e : ℝ => (1 - e) * w + e / 2) (𝓝 0) (𝓝 ((1 - 0) * w + 0 / 2)) :=
        (by fun_prop : Continuous fun e : ℝ => (1 - e) * w + e / 2).tendsto 0
      simp only [sub_zero, one_mul, zero_div, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with e he
      constructor <;> nlinarith [hw.1, hw.2, he.1, he.2]
  have hin : ∀ w ∈ Icc (0:ℝ) 1, ∀ e ∈ Ioo (0:ℝ) 1, (1 - e) * w + e / 2 ∈ Ioo (0:ℝ) 1 := by
    intro w hw e he
    constructor <;> nlinarith [hw.1, hw.2, he.1, he.2]
  refine ⟨G, ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩, hcont, ?_, hGg⟩
  · have hz : a • x + b • y ∈ Icc (0:ℝ) 1 := (convex_Icc 0 1) hx hy ha hb hab
    have hL := ((hpath x hx).const_mul a).add ((hpath y hy).const_mul b)
    refine le_of_tendsto_of_tendsto hL (hpath _ hz) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with e he
    have hxe := hin x hx e he
    have hye := hin y hy e he
    have hze := hin _ hz e he
    have key := hg.2 hxe hye ha hb hab
    have e1 : a • ((1 - e) * x + e / 2) + b • ((1 - e) * y + e / 2) =
        (1 - e) * (a • x + b • y) + e / 2 := by
      simp only [smul_eq_mul]
      have : b = 1 - a := by linarith
      subst this; ring
    rw [e1] at key
    simp only [smul_eq_mul] at key hze ⊢
    rw [hGg _ hxe, hGg _ hye, hGg _ hze]
    exact key
  · intro x hx
    have hev : ∀ᶠ e in 𝓝[>] (0:ℝ), 0 ≤ G ((1 - e) * x + e / 2) := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with e he
      rw [hGg _ (hin x hx e he)]
      exact hg0 _ (hin x hx e he)
    exact ge_of_tendsto (hpath x hx) hev

/-! ## Theorem 67 on an interval, with concavity on the open interval -/

/-- Pushing a measure with density `F ∘ φ` forward by `φ`. -/
lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {F : β → ℝ≥0∞} (hF : Measurable F) :
    (μ.withDensity (F ∘ φ)).map φ = (μ.map φ).withDensity F := by
  ext A hA
  rw [Measure.map_apply hφ hA, withDensity_apply _ (hφ hA), withDensity_apply _ hA,
    setLIntegral_map hA hF hφ]
  rfl

/-- The uniform measure on `[0, 1]` pushed by `y ↦ a + c y` (`c > 0`) is `c⁻¹` times Lebesgue
measure on `[a, a + c]`. -/
lemma map_restrict_affine {a c : ℝ} (hc : 0 < c) :
    (volume.restrict (Icc (0:ℝ) 1)).map (fun y => a + c * y) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Icc a (a + c)) := by
  have hφ : Measurable fun y : ℝ => a + c * y := by fun_prop
  have hvol : (volume : Measure ℝ).map (fun y => a + c * y) = ENNReal.ofReal c⁻¹ • volume := by
    have e : (fun y : ℝ => a + c * y) = (fun x => a + x) ∘ (fun y => c * y) := rfl
    rw [e, ← Measure.map_map (measurable_const_add a) (measurable_const_mul c),
      Real.map_volume_mul_left hc.ne', Measure.map_smul, map_add_left_eq_self,
      abs_of_pos (inv_pos.2 hc)]
    exact (measurable_const_add a).aemeasurable
  have hpre : (fun y : ℝ => a + c * y) ⁻¹' Icc a (a + c) = Icc 0 1 := by
    ext y
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [← hpre, ← Measure.restrict_map hφ measurableSet_Icc, hvol, Measure.restrict_smul]

/-- **Theorem 67** (`o:thm:pconc`) in the form of the paper: let `p ≥ 1`, `a < b`, and let `h ≥ 0`
be concave on the open interval `(a, b)` such that `h ^ p` is a probability density on
`[a, b]`. Then this distribution is `n`-completely mixable for every integer `n ≥ p + 2`.
(The end point values of `h` are irrelevant; `h` is replaced by its continuous extension, and
the interval is mapped affinely onto `[0, 1]`, where `Bridges.pconc` applies.) -/
theorem pconc_Ioo {p a b : ℝ} (hp : 1 ≤ p) (hab : a < b) {h : ℝ → ℝ}
    (hh : ConcaveOn ℝ (Ioo a b) h) (hh0 : ∀ x ∈ Ioo a b, 0 ≤ h x)
    (hprob : IsProbabilityMeasure
      ((volume.restrict (Icc a b)).withDensity fun x => ENNReal.ofReal (h x ^ p))) :
    ∀ n : ℕ, p + 2 ≤ n → CompletelyMixable n
      ((volume.restrict (Icc a b)).withDensity fun x => ENNReal.ofReal (h x ^ p)) := by
  intro n hn
  set c := b - a with hcdef
  have hc : 0 < c := by linarith
  have hp0 : p ≠ 0 := by linarith
  set φ : ℝ → ℝ := fun y => a + c * y with hφdef
  have hφ : Measurable φ := by fun_prop
  have hφI : ∀ y ∈ Ioo (0:ℝ) 1, φ y ∈ Ioo a b := fun y hy =>
    ⟨by simp only [φ]; nlinarith [hy.1], by simp only [φ, c]; nlinarith [hy.2]⟩
  set g0 : ℝ → ℝ := fun y => c ^ (1 / p) * h (φ y)
  have hcp : 0 ≤ c ^ (1 / p) := Real.rpow_nonneg hc.le _
  have hg0c : ConcaveOn ℝ (Ioo 0 1) g0 := by
    refine ⟨convex_Ioo 0 1, fun x hx y hy α β hα hβ hαβ => ?_⟩
    have key := hh.2 (hφI x hx) (hφI y hy) hα hβ hαβ
    have e : α • φ x + β • φ y = φ (α • x + β • y) := by
      simp only [φ, smul_eq_mul]
      have : β = 1 - α := by linarith
      subst this; ring
    rw [e] at key
    simp only [g0, smul_eq_mul] at key ⊢
    nlinarith [mul_le_mul_of_nonneg_left key hcp]
  have hg0n : ∀ y ∈ Ioo (0:ℝ) 1, 0 ≤ g0 y := fun y hy => mul_nonneg hcp (hh0 _ (hφI y hy))
  obtain ⟨G, hGc, hGcont, hG0, hGg⟩ := concave_extend hg0c hg0n
  set T := (volume.restrict (Icc a b)).withDensity fun x => ENNReal.ofReal (h x ^ p)
  set D := Bipyramid.densityOn01 fun x => G x ^ p
  -- the measure identity `T = D.map φ`
  have hTD : D.map φ = T := by
    have hhae : AEMeasurable h (volume.restrict (Icc a b)) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact (hh.continuousOn isOpen_Ioo).aemeasurable measurableSet_Ioo
    have hFae : AEMeasurable (fun x => ENNReal.ofReal (h x ^ p)) (volume.restrict (Icc a b)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((Real.continuous_rpow_const (by linarith)).measurable.comp_aemeasurable hhae)
    obtain ⟨F', hF, hFF'⟩ := hFae
    have hab' : Icc a b = Icc a (a + c) := by rw [hcdef]; ring_nf
    have h1 : volume.restrict (Icc a b) =
        ENNReal.ofReal c • (volume.restrict (Icc (0:ℝ) 1)).map φ := by
      rw [map_restrict_affine hc, smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
        ENNReal.ofReal_one, one_smul, hab']
    have hae : ∀ᵐ y ∂(volume.restrict (Icc (0:ℝ) 1)), y ∈ Ioo (0:ℝ) 1 := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    have hae2 : ∀ᵐ y ∂(volume.restrict (Icc (0:ℝ) 1)),
        ENNReal.ofReal (h (φ y) ^ p) = F' (φ y) := by
      have := hFF'
      rw [Filter.EventuallyEq, h1,
        Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 hc).ne'] at this
      exact ae_of_ae_map hφ.aemeasurable this
    simp only [T, D, Bipyramid.densityOn01]
    rw [withDensity_congr_ae hFF', h1, withDensity_smul_measure,
      ← map_withDensity_comp _ hφ hF, ← Measure.map_smul,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    swap; · exact hφ.aemeasurable
    congr 1
    refine withDensity_congr_ae ?_
    filter_upwards [hae, hae2] with y hy hy2
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [hGg y hy, ← hy2, ← ENNReal.ofReal_mul hc.le]
    congr 1
    simp only [g0]
    rw [Real.mul_rpow hcp (hh0 _ (hφI y hy)), ← Real.rpow_mul hc.le, one_div,
      inv_mul_cancel₀ hp0, Real.rpow_one]
  -- `G ^ p` is a probability density on `[0, 1]`
  have hDuniv : D univ = 1 := by
    have := hprob.measure_univ
    rw [← hTD, Measure.map_apply hφ MeasurableSet.univ, preimage_univ] at this
    exact this
  have hdens : ∫ x in (0:ℝ)..1, G x ^ p = 1 := by
    have hcont : ContinuousOn (fun x => G x ^ p) (Icc 0 1) :=
      hGcont.rpow_const fun x _ => Or.inr (by linarith)
    have hint : IntegrableOn (fun x => G x ^ p) (Icc 0 1) := hcont.integrableOn_Icc
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    have h1 : ENNReal.ofReal (∫ x in Icc (0:ℝ) 1, G x ^ p) = 1 := by
      rw [ofReal_integral_eq_lintegral_ofReal hint]
      · rw [← hDuniv]
        simp only [D, Bipyramid.densityOn01]
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      · exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx =>
          Real.rpow_nonneg (hG0 x hx) _
    exact (ENNReal.ofReal_eq_one).1 h1
  have hCM := Bridges.pconc hp hGc hGcont hG0 hdens n hn
  have := CompletelyMixable.map_affine hCM a c
  rw [← hTD]
  exact this

/-! ## Coordinates adapted to a linear functional -/

section Chart

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- For a nonzero linear functional `u` on a space of dimension `m + 1` there are linear
coordinates `L : V ≃ ℝ × ℝ^m` whose first coordinate is `u`. -/
theorem exists_chart {m : ℕ} (hV : finrank ℝ V = m + 1) (u : V →L[ℝ] ℝ) (hu : u ≠ 0) :
    ∃ L : V ≃L[ℝ] ℝ × (Fin m → ℝ), ∀ x, (L x).1 = u x := by
  obtain ⟨v0, hv0⟩ : ∃ v, u v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (ContinuousLinearMap.ext hcon)
  set v := (u v0)⁻¹ • v0
  have hv : u v = 1 := by simp [v, hv0]
  set uL : V →ₗ[ℝ] ℝ := (u : V →ₗ[ℝ] ℝ)
  have hsurj : uL.range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun r => ⟨r • v, ?_⟩
    simp [uL, hv]
  have hker : finrank ℝ (LinearMap.ker uL) = m := by
    have := LinearMap.finrank_range_add_finrank_ker uL
    rw [hsurj, finrank_top, finrank_self, hV] at this
    omega
  let e : LinearMap.ker uL ≃ₗ[ℝ] (Fin m → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hker, Module.finrank_fin_fun])
  let q : V →ₗ[ℝ] V := LinearMap.id - (uL.smulRight v)
  have hq : ∀ x, q x ∈ LinearMap.ker uL := fun x => by
    simp [q, uL, hv]
  let proj : V →ₗ[ℝ] LinearMap.ker uL := LinearMap.codRestrict _ q hq
  let T : V →ₗ[ℝ] ℝ × (Fin m → ℝ) := uL.prod (e.toLinearMap ∘ₗ proj)
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : u x = 0 := congrArg Prod.fst hx
    have h2 : e (proj x) = 0 := congrArg Prod.snd hx
    have h3 : proj x = 0 := by simpa using h2
    have h4 : q x = 0 := by
      have := congrArg Subtype.val h3
      simpa [proj] using this
    simpa [q, uL, h1] using h4
  have hdim : finrank ℝ V = finrank ℝ (ℝ × (Fin m → ℝ)) := by
    rw [Module.finrank_prod, finrank_self, Module.finrank_fin_fun, hV]; ring
  have hbij : Function.Bijective T :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  refine ⟨(LinearEquiv.ofBijective T hbij).toContinuousLinearEquiv, fun x => ?_⟩
  rfl

end Chart

/-! ## The density step and Corollary 68 -/

section Density

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}

/-- The `(d-1)`-dimensional volume of the section `K ∩ {u = t}`, measured in the coordinates `L`
(`u = (L ·).1`): `vol_{d-1}{b ∈ ℝ^m : L⁻¹(t, b) ∈ K}`. -/
def sectionVol (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (K : Set V) (t : ℝ) : ℝ≥0∞ :=
  volume (Prod.mk t ⁻¹' (L.symm ⁻¹' K))

/-- Linear coordinates scale volume by a constant factor. -/
lemma map_volume_chart (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ volume.map L = c • volume := by
  obtain ⟨c, h0, ht, he⟩ := map_coneChart L 0
  refine ⟨c, h0, ht, ?_⟩
  have : (coneChart L 0 : V → ℝ × (Fin m → ℝ)) = L := by
    funext x; rw [coneChart_apply, sub_zero]
  rw [← this, he]

/-- **The density step** of Corollary 68: if `u = (L ·).1` and `volume.map L = c • volume`, then
the image of Lebesgue measure on `K` under `u` has the density `c · sectionVol L K` (Fubini). -/
theorem map_restrict_eq (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (u : V →L[ℝ] ℝ)
    (hL : ∀ x, (L x).1 = u x) {c : ℝ≥0∞} (hc : volume.map L = c • volume) {K : Set V}
    (hK : MeasurableSet K) :
    (volume.restrict K).map u = c • volume.withDensity (sectionVol L K) := by
  have hC : MeasurableSet (L.symm ⁻¹' K) := L.symm.continuous.measurable hK
  ext A hA
  set S := (Prod.fst ⁻¹' A) ∩ L.symm ⁻¹' K
  have hS : MeasurableSet S := (measurable_fst hA).inter hC
  have hpre : u ⁻¹' A ∩ K = L ⁻¹' S := by
    ext x
    simp only [S, mem_inter_iff, mem_preimage, hL, ContinuousLinearEquiv.symm_apply_apply]
  rw [Measure.map_apply u.measurable hA, Measure.restrict_apply (u.measurable hA), hpre,
    ← Measure.map_apply L.continuous.measurable hS, hc, smul_apply,
    smul_apply, withDensity_apply _ hA, Measure.volume_eq_prod, Measure.prod_apply hS,
    ← lintegral_indicator hA]
  congr 1
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ A
  · rw [indicator_of_mem ht]
    congr 1
    ext b
    simp [S, ht]
  · rw [indicator_of_notMem ht]
    have : Prod.mk t ⁻¹' S = ∅ := by
      ext b; simp [S, ht]
    rw [this, measure_empty]

/-- **Brunn's theorem** (Gardner 2002), in the form used in Corollary 68: for a compact convex set
`C ⊆ ℝ × ℝ^m`, the `m`-th root of the `m`-dimensional volume of the section `{b : (t, b) ∈ C}` is a
concave function of `t` on the projection of `C`. It follows from the Brunn–Minkowski inequality
in `ℝ^m`, which is not in Mathlib; it is used as an explicit hypothesis. -/
def BrunnSections (m : ℕ) : Prop :=
  ∀ C : Set (ℝ × (Fin m → ℝ)), IsCompact C → Convex ℝ C →
    ConcaveOn ℝ (Prod.fst '' C) fun t => (volume (Prod.mk t ⁻¹' C)).toReal ^ ((m : ℝ)⁻¹)

/-- **Corollary 68** (`o:cor:proj`), first statement. Let `K` be a convex body (compact, convex,
with nonempty interior) in a real space `V` of dimension `d ≥ 2`, let `X ∼ U(K)` and let `u` be a
nonzero linear functional. Then the law of `u(X)` is `n`-completely mixable for every
`n ≥ d + 1` (the complete mix is that of Theorem 67, `pconc_Ioo`). Brunn's theorem in dimension
`d - 1` (`BrunnSections (d - 1)`) is a hypothesis. -/
theorem cor68 {d : ℕ} (hd : 2 ≤ d) (hV : finrank ℝ V = d) (hBrunn : BrunnSections (d - 1))
    {K : Set V} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (u : V →L[ℝ] ℝ) (hu : u ≠ 0) :
    ∀ n : ℕ, d + 1 ≤ n → CompletelyMixable n ((unifSet K).map u) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  simp only [Nat.add_sub_cancel] at hBrunn
  intro n hn
  obtain ⟨L, hL⟩ := exists_chart hV u hu
  obtain ⟨c, hc0, hct, hc⟩ := map_volume_chart (V := V) L
  have hK : MeasurableSet K := hKc.isClosed.measurableSet
  set C := L.symm ⁻¹' K with hCdef
  have hCim : C = L '' K := (L.toEquiv.image_eq_preimage_symm K).symm
  have hCc : IsCompact C := by rw [hCim]; exact hKc.image L.continuous
  have hCconv : Convex ℝ C := by rw [hCim]; exact hKconv.linear_image L.toLinearMap
  have hCmeas : MeasurableSet C := hCc.isClosed.measurableSet
  set σ := sectionVol L K with hσdef
  have hσm : Measurable σ := measurable_measure_prodMk_left hCmeas
  have hfst : Prod.fst '' C = u '' K := by
    ext t
    simp only [mem_image, hCdef, mem_preimage]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨L.symm q, hq, by rw [← hL, ContinuousLinearEquiv.apply_symm_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨L x, by rwa [ContinuousLinearEquiv.symm_apply_apply], hL x⟩
  -- the projection is an interval `[a, b]` with `a < b`
  have hUc : IsCompact (u '' K) := hKc.image u.continuous
  obtain ⟨x0, hx0⟩ := hKi
  have hUne : (u '' K).Nonempty := ⟨u x0, x0, interior_subset hx0, rfl⟩
  set a := sInf (u '' K)
  set b := sSup (u '' K)
  have haK := hUc.sInf_mem hUne
  have hbK := hUc.sSup_mem hUne
  have hUI : u '' K = Icc a b := by
    apply Subset.antisymm
    · intro t ht
      exact ⟨csInf_le hUc.bddBelow ht, le_csSup hUc.bddAbove ht⟩
    · have hconvU : Convex ℝ (u '' K) := hKconv.linear_image u.toLinearMap
      exact hconvU.ordConnected.out haK hbK
  have hab : a < b := by
    obtain ⟨v0, hv0⟩ : ∃ v, u v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (ContinuousLinearMap.ext hcon)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx0)
    set δ := ε / (2 * (‖v0‖ + 1))
    have hδ : 0 < δ := by positivity
    have hx1 : x0 + δ • v0 ∈ K := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
      have : δ * ‖v0‖ ≤ ε / 2 := by
        simp only [δ]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [norm_nonneg v0]
      linarith
    have hne : u (x0 + δ • v0) ≠ u x0 := by
      rw [map_add, map_smul, smul_eq_mul]
      intro h
      have : δ * u v0 = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact hδ.ne' h'
      · exact hv0 h'
    have h1 : u x0 ∈ Icc a b := hUI ▸ ⟨x0, interior_subset hx0, rfl⟩
    have h2 : u (x0 + δ • v0) ∈ Icc a b := hUI ▸ ⟨_, hx1, rfl⟩
    by_contra hle
    push Not at hle
    apply hne
    have := h1.1; have := h1.2; have := h2.1; have := h2.2
    linarith
  -- the sections
  have hσtop : ∀ t, σ t ≠ ⊤ := by
    intro t
    have hsub : Prod.mk t ⁻¹' C ⊆ Prod.snd '' C := fun q hq => ⟨(t, q), hq, rfl⟩
    exact ((hCc.image continuous_snd).measure_lt_top.trans_le' (measure_mono hsub)).ne
  have hσzero : ∀ t, t ∉ Icc a b → σ t = 0 := by
    intro t ht
    have : Prod.mk t ⁻¹' C = ∅ := by
      ext q
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hq
      exact ht (hUI ▸ hfst ▸ ⟨(t, q), hq, rfl⟩)
    simp only [σ, sectionVol, ← hCdef, this, measure_empty]
  -- the law of `u(X)`
  have hvK0 : volume K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ ⟨x0, hx0⟩).ne'
  have hvKt : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  set κ := (volume K)⁻¹ * c
  have hκt : κ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hvK0) hct
  set k := κ.toReal
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hmR : (m : ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set h : ℝ → ℝ := fun t => k ^ ((m : ℝ)⁻¹) * (σ t).toReal ^ ((m : ℝ)⁻¹)
  have hlaw : (unifSet K).map u =
      (volume.restrict (Icc a b)).withDensity fun t => ENNReal.ofReal (h t ^ (m : ℝ)) := by
    have e1 : (unifSet K).map u = volume.withDensity (κ • σ) := by
      rw [unifSet, Measure.map_smul, map_restrict_eq L u hL hc hK, smul_smul,
        withDensity_smul' _ _ hκt]
      exact u.measurable.aemeasurable
    have hae : ∀ᵐ t ∂(volume.withDensity (κ • σ)), t ∈ Icc a b := by
      rw [ae_withDensity_iff (hσm.const_smul κ)]
      refine Filter.Eventually.of_forall fun t ht => ?_
      by_contra hn'
      exact ht (by simp [hσzero t hn'])
    rw [e1, ← Measure.restrict_eq_self_of_ae_mem hae, restrict_withDensity measurableSet_Icc]
    refine withDensity_congr_ae (ae_of_all _ fun t => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, h]
    rw [Real.mul_rpow (Real.rpow_nonneg hk0 _) (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      Real.rpow_inv_rpow hk0 hmR, Real.rpow_inv_rpow ENNReal.toReal_nonneg hmR,
      ENNReal.ofReal_mul hk0, ENNReal.ofReal_toReal hκt, ENNReal.ofReal_toReal (hσtop t)]
  have hprob : IsProbabilityMeasure ((volume.restrict (Icc a b)).withDensity
      fun t => ENNReal.ofReal (h t ^ (m : ℝ))) := by
    rw [← hlaw]
    have := unifSet_isProb hvK0 hvKt
    infer_instance
  -- Brunn's theorem gives the concavity of `h` on `(a, b)`
  have hBr := hBrunn C hCc hCconv
  rw [hfst, hUI] at hBr
  have hconc : ConcaveOn ℝ (Ioo a b) h := by
    have := (hBr.subset Ioo_subset_Icc_self (convex_Ioo a b)).smul
      (Real.rpow_nonneg hk0 ((m : ℝ)⁻¹))
    exact this
  have hh0 : ∀ t ∈ Ioo a b, 0 ≤ h t := fun t _ =>
    mul_nonneg (Real.rpow_nonneg hk0 _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  rw [hlaw]
  refine pconc_Ioo (by exact_mod_cast hm) hab hconc hh0 hprob n ?_
  have : ((m + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at this
  linarith

end Density

/-! ## Sharpness: cones over a base on which `u` is constant -/

section Cone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}

/-- A level set of a nonzero linear functional on `ℝ^m` is Lebesgue null. -/
lemma volume_level_null (β : (Fin m → ℝ) →ₗ[ℝ] ℝ) (hβ : β ≠ 0) (k : ℝ) :
    volume {b : Fin m → ℝ | β b = k} = 0 := by
  rcases eq_empty_or_nonempty {b : Fin m → ℝ | β b = k} with he | ⟨b0, hb0⟩
  · rw [he, measure_empty]
  obtain ⟨b1, hb1⟩ : ∃ b, β b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hβ (LinearMap.ext hcon)
  set S := AffineSubspace.mk' b0 (LinearMap.ker β)
  have hsub : {b : Fin m → ℝ | β b = k} ⊆ S := fun b hb => by
    simp only [mem_ofPred_eq] at hb hb0
    simp only [S, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker,
      map_sub, hb, hb0, sub_self]
  have hS : S ≠ ⊤ := by
    intro htop
    have : b1 + b0 ∈ S := by rw [htop]; exact AffineSubspace.mem_top _ _ _
    simp only [S, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_right,
      LinearMap.mem_ker] at this
    exact hb1 this
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume S hS)

/-- **Corollary 68**, sharpness. Let `K = t + C` be the cone with apex `t` over the base
`t + F`, `F = L⁻¹({1} × B)` (`coneSet`, `dim V = d = m + 1`, `B` of finite positive volume), and
let `u ≠ 0` be a linear functional that is constant on the base. If the law of `u(X)`,
`X ∼ U(K)`, is `n`-completely mixable (`n ≥ 1`), then `n ≥ d + 1 = m + 2`; so it is not
`n`-completely mixable for `n ≤ d`, and the bound of `cor68` is attained. -/
theorem cor68_cone (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) {B : Set (Fin m → ℝ)} (hB : MeasurableSet B)
    (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤) (t : V) (u : V →L[ℝ] ℝ) (hu : u ≠ 0)
    (hconst : ∃ c0, ∀ y ∈ coneBase L B, u (t + y) = c0) {n : ℕ} (hn : 0 < n)
    (h : CompletelyMixable n ((unifSet (scaledTranslate t 1 (coneSet L B))).map u)) :
    m + 2 ≤ n := by
  obtain ⟨c0, hc0⟩ := hconst
  set α := u (L.symm (1, 0))
  let β : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    (u : V →ₗ[ℝ] ℝ) ∘ₗ (L.symm : ℝ × (Fin m → ℝ) →ₗ[ℝ] V) ∘ₗ LinearMap.inr ℝ ℝ (Fin m → ℝ)
  have hβapp : ∀ b, β b = u (L.symm (0, b)) := fun b => rfl
  have hdec : ∀ s b, u (L.symm (s, b)) = s * α + β b := by
    intro s b
    have : ((s, b) : ℝ × (Fin m → ℝ)) = s • ((1 : ℝ), (0 : Fin m → ℝ)) + (0, b) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_add, map_smul, hβapp, smul_eq_mul]
  have hβ0 : β = 0 := by
    by_contra hβ
    apply hB0
    refine measure_mono_null (fun b hb => ?_) (volume_level_null β hβ (c0 - u t - α))
    have := hc0 _ ⟨b, hb, rfl⟩
    rw [map_add, hdec] at this
    show β b = c0 - u t - α
    linarith
  have hlin : ∀ y, u y = α * (L y).1 := by
    intro y
    have := hdec (L y).1 (L y).2
    rw [hβ0, LinearMap.zero_apply, add_zero] at this
    rw [mul_comm, ← this, L.symm_apply_apply]
  have hα : α ≠ 0 := by
    intro h0
    apply hu
    ext y
    rw [hlin y, h0, zero_mul]; rfl
  -- the law of `u(X)` is an affine image of the law of `S = ℓ(X - t)`
  have hlaw : (unifSet (scaledTranslate t 1 (coneSet L B))).map u =
      (coneRadial m 1).map (fun s => u t + α * s) := by
    rw [← unifSet_scaledCone_map_ell L hB hB0 hBt t one_pos,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [← hlin, map_sub]
    ring
  rw [hlaw] at h
  have h2 := CompletelyMixable.map_affine h (1 + u t / α) (-1 / α)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h2
  have e : ((fun x => 1 + u t / α + -1 / α * x) ∘ fun s => u t + α * s) = fun s => 1 - s := by
    funext s
    simp only [Function.comp_apply]
    field_simp
    ring
  rw [e] at h2
  have hT : (coneRadial m 1).map (fun s => 1 - s) = coneTLaw m 1 := by
    simp [coneTLaw]
  rw [hT] at h2
  obtain ⟨Q, hQ⟩ := h2
  have hae := hQ.ae_le_sum_lintegral (fun _ => coneTLaw_nonneg m) ⟨0, hn⟩
  simp only [lintegral_coneTLaw m zero_le_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hae
  by_contra hlt
  push Not at hlt
  have hlt' : (n : ℝ) < m + 2 := by exact_mod_cast hlt
  have hpos : (0:ℝ) < m + 2 := by positivity
  have hae' : ∀ᵐ x ∂coneTLaw m 1, x ≤ (n : ℝ) * (1 / ((m : ℝ) + 2)) := by
    filter_upwards [hae] with x hx
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hx
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hx
  refine coneTLaw_not_ae_le m one_pos ?_ hae'
  rw [mul_one_div, div_lt_one hpos]
  exact hlt'

end Cone

end Mixes.Proj
