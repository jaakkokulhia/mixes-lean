import Mathlib
import Mixes.AsymThree

/-!
# The convolution square of a distribution with an absolutely continuous part

Discharges the hypothesis `AsymThree.H_convSq`: if a probability measure `G` on `ℝ`, carried by a
bounded interval, has a nonzero absolutely continuous part, then `G ∗ G` dominates a positive
multiple of a uniform distribution on an interval.

Proof: the density `f` of the absolutely continuous part exceeds some `δ > 0` on a set `E` of
positive Lebesgue measure. By the Lebesgue density theorem there is a closed ball `I = [x-r, x+r]`
with `λ(I \ E) ≤ r/5`. Then `G ≥ δ·λ|_{E ∩ I}`, so `G ∗ G` dominates the measure with density
`h ⋆ h`, `h = δ·1_{E ∩ I}`, and for `|t - 2x| ≤ r/2` one has `(h ⋆ h)(t) ≥ δ²·(3r/5)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Mixes.ConvSq

/-- Convolution of measures is monotone in both arguments. -/
lemma conv_mono {μ μ' ν ν' : Measure ℝ} [SFinite ν] [SFinite ν'] (h1 : μ ≤ μ') (h2 : ν ≤ ν') :
    μ ∗ ν ≤ μ' ∗ ν' := by
  refine Measure.le_iff.mpr fun s hs => ?_
  have hm : Measurable (s.indicator (1 : ℝ → ENNReal)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, Measure.lintegral_conv hm,
    Measure.lintegral_conv hm]
  exact lintegral_mono' h1 (fun x => lintegral_mono' h2 le_rfl)

/-- A nonzero density exceeds some positive constant on a set of positive measure. -/
lemma exists_level {f : ℝ → ENNReal} (hf : Measurable f) (h0 : volume.withDensity f ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ volume {x | ENNReal.ofReal d < f x} ≠ 0 := by
  have hne : ¬ f =ᵐ[volume] 0 := fun h => h0 ((withDensity_eq_zero_iff hf.aemeasurable).mpr h)
  have hpos : volume {x | f x ≠ 0} ≠ 0 := by
    intro h; apply hne
    rw [Filter.EventuallyEq, ae_iff]; simpa using h
  have hsub : {x | f x ≠ 0} ⊆ ⋃ n : ℕ, {x | ENNReal.ofReal (1 / ((n : ℝ) + 1)) < f x} := by
    intro x hx
    have h1 : 0 < f x := pos_iff_ne_zero.mpr hx
    obtain ⟨d, hd0, hd1, hd2⟩ := ENNReal.lt_iff_exists_real_btwn.mp h1
    have hd : 0 < d := by
      by_contra hc; push Not at hc
      rw [ENNReal.ofReal_of_nonpos hc] at hd1; exact lt_irrefl _ hd1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
    exact mem_iUnion.mpr ⟨n, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hn.le) hd2⟩
  by_contra hc
  push Not at hc
  apply hpos
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  exact hc _ (by positivity)

/-- A Lebesgue density point: a measurable set of positive measure contains most of some small
closed ball. -/
lemma exists_dense_ball {E : Set ℝ} (hE : MeasurableSet E) (hpos : volume E ≠ 0) :
    ∃ x r : ℝ, 0 < r ∧ volume (Metric.closedBall x r \ E) ≤ ENNReal.ofReal (r / 5) := by
  have hae := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hE
  obtain ⟨x, hxE, hx⟩ : ∃ x ∈ E, Tendsto (fun r => volume (E ∩ Metric.closedBall x r) /
      volume (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 (E.indicator 1 x)) := by
    by_contra hc
    push Not at hc
    apply hpos
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyE
    exact hc y hyE hy
  rw [indicator_of_mem hxE, Pi.one_apply] at hx
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (9 / 10) <
      volume (E ∩ Metric.closedBall x r) / volume (Metric.closedBall x r) :=
    hx.eventually (lt_mem_nhds (by rw [← ENNReal.ofReal_one]; exact
      (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num)))
  obtain ⟨r, hr, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0 : 0 < r := hr0
  refine ⟨x, r, hr0, ?_⟩
  rw [Real.volume_closedBall] at hr
  have hball : (ENNReal.ofReal (2 * r)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; linarith
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hball) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (by norm_num)] at hr
  have hsplit := measure_inter_add_sdiff (μ := volume) (Metric.closedBall x r) hE
  rw [Real.volume_closedBall, inter_comm] at hsplit
  by_contra hc
  push Not at hc
  have := ENNReal.add_lt_add hr hc
  rw [hsplit, ← ENNReal.ofReal_add (by positivity) (by positivity)] at this
  have h2 : 9 / 10 * (2 * r) + r / 5 = 2 * r := by ring
  rw [h2] at this
  exact lt_irrefl _ this

/-- **`H_convSq`**: the convolution square of a probability measure on a bounded interval with a
nonzero absolutely continuous part dominates a positive multiple of a uniform distribution. -/
theorem convSq : AsymThree.H_convSq := by
  intro G hGP _ hac
  set f := G.rnDeriv volume with hfdef
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  obtain ⟨d, hd, hEpos⟩ := exists_level hf hac
  set E := {x | ENNReal.ofReal d < f x} with hEdef
  have hE : MeasurableSet E := measurableSet_lt measurable_const hf
  obtain ⟨x, r, hr, hB⟩ := exists_dense_ball hE hEpos
  set I := Metric.closedBall x r with hIdef
  set B := I \ E with hBdef
  have hBm : MeasurableSet B := measurableSet_closedBall.diff hE
  set δ := ENNReal.ofReal d with hδ
  set h : ℝ → ENNReal := (E ∩ I).indicator (fun _ => δ) with hhdef
  have hhm : Measurable h := measurable_const.indicator (hE.inter measurableSet_closedBall)
  -- `G` dominates `h · λ`
  have hGh : volume.withDensity h ≤ G := by
    refine le_trans (withDensity_mono (Eventually.of_forall fun y => ?_))
      (Measure.withDensity_rnDeriv_le G volume)
    simp only [hhdef]
    by_cases hy : y ∈ E ∩ I
    · rw [indicator_of_mem hy]; exact (hy.1 : ENNReal.ofReal d < f y).le
    · rw [indicator_of_notMem hy]; exact bot_le
  have hGG : volume.withDensity (h ⋆ₗ h) ≤ G ∗ G := by
    rw [← conv_withDensity_eq_lconvolution hhm hhm]
    exact conv_mono hGh hGh
  -- the lower bound of `h ⋆ h` near `2x`
  set K := Icc (x - r / 2) (x + r / 2) with hKdef
  set J := Icc (2 * x - r / 2) (2 * x + r / 2) with hJdef
  have hlow : ∀ t ∈ J, δ * δ * ENNReal.ofReal (3 * r / 5) ≤ (h ⋆ₗ h) t := by
    intro t ht
    set X := B ∪ (fun y => -y + t) ⁻¹' B with hXdef
    have hXm : MeasurableSet X :=
      hBm.union (hBm.preimage (measurable_neg.add_const t))
    have hX : volume X ≤ ENNReal.ofReal (2 * r / 5) := by
      have hpre : volume ((fun y => -y + t) ⁻¹' B) = volume B := by
        have : (fun y : ℝ => -y + t) ⁻¹' B = Neg.neg ⁻¹' ((fun z => z + t) ⁻¹' B) := rfl
        rw [this, Measure.measure_preimage_neg, measure_preimage_add_right]
      calc volume X ≤ volume B + volume ((fun y => -y + t) ⁻¹' B) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (r / 5) + ENNReal.ofReal (r / 5) := by rw [hpre]; exact add_le_add hB hB
        _ = ENNReal.ofReal (2 * r / 5) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    have hKX : ENNReal.ofReal (3 * r / 5) ≤ volume (K \ X) := by
      have hK : volume K = ENNReal.ofReal r := by
        rw [hKdef, Real.volume_Icc]; ring_nf
      calc ENNReal.ofReal (3 * r / 5) = ENNReal.ofReal r - ENNReal.ofReal (2 * r / 5) := by
            rw [← ENNReal.ofReal_sub _ (by positivity)]; ring_nf
        _ ≤ volume K - volume X := by rw [hK]; exact tsub_le_tsub_left hX _
        _ ≤ volume (K \ X) := le_measure_sdiff
    calc δ * δ * ENNReal.ofReal (3 * r / 5) ≤ δ * δ * volume (K \ X) := by gcongr
      _ = ∫⁻ y, (K \ X).indicator (fun _ => δ * δ) y := by
          rw [lintegral_indicator_const (measurableSet_Icc.diff hXm)]
      _ ≤ (h ⋆ₗ h) t := by
          rw [lconvolution_def]
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ K \ X
          · rw [indicator_of_mem hy]
            obtain ⟨hyK, hyX⟩ := hy
            simp only [hXdef, mem_union, mem_preimage, not_or] at hyX
            obtain ⟨hyB, hyB'⟩ := hyX
            have hyI : y ∈ I := by
              rw [hIdef, Real.closedBall_eq_Icc]
              obtain ⟨h1, h2⟩ := hyK
              constructor <;> linarith
            have hyI' : -y + t ∈ I := by
              rw [hIdef, Real.closedBall_eq_Icc]
              obtain ⟨h1, h2⟩ := hyK
              obtain ⟨h3, h4⟩ := ht
              constructor <;> linarith
            have hyE : y ∈ E := by
              by_contra hc; exact hyB ⟨hyI, hc⟩
            have hyE' : -y + t ∈ E := by
              by_contra hc; exact hyB' ⟨hyI', hc⟩
            simp only [hhdef]
            rw [indicator_of_mem (show y ∈ E ∩ I from ⟨hyE, hyI⟩), indicator_of_mem (show -y + t ∈ E ∩ I from ⟨hyE', hyI'⟩)]
          · rw [indicator_of_notMem hy]; exact bot_le
  -- conclusion
  refine ⟨2 * x, r / 2, d * d * (3 * r / 5) * r, by positivity, by positivity, ?_⟩
  refine le_trans ?_ hGG
  have hlt : 2 * x - r / 2 < 2 * x + r / 2 := by linarith
  have hlen : 2 * x + r / 2 - (2 * x - r / 2) = r := by ring
  unfold unifI
  rw [ite_eq_left hlt, hlen, smul_smul]
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [smul_apply, Measure.restrict_apply hA, withDensity_apply _ hA, smul_eq_mul]
  have hq : ENNReal.ofReal (d * d * (3 * r / 5) * r) * (ENNReal.ofReal r)⁻¹ =
      δ * δ * ENNReal.ofReal (3 * r / 5) := by
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc,
      ENNReal.mul_inv_cancel (by rw [ne_eq, ENNReal.ofReal_eq_zero]; linarith) ENNReal.ofReal_ne_top,
      mul_one, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hd.le]
  rw [hq]
  calc δ * δ * ENNReal.ofReal (3 * r / 5) * volume (A ∩ J)
      = ∫⁻ t in A ∩ J, δ * δ * ENNReal.ofReal (3 * r / 5) := by rw [setLIntegral_const]
    _ ≤ ∫⁻ t in A ∩ J, (h ⋆ₗ h) t :=
        setLIntegral_mono' (hA.inter measurableSet_Icc) fun t ht => hlow t ht.2
    _ ≤ ∫⁻ t in A, (h ⋆ₗ h) t := lintegral_mono_set inter_subset_left

/-- **Corollary `as:cor:repeat`** with `H_convSq` discharged. -/
theorem cor_repeat_cs (hW : AsymThree.H_window_line) (hC : AsymThree.H_conc_a)
    (G : Measure ℝ) [IsProbabilityMeasure G] {a0 R : ℝ} (hG : G (Icc a0 (a0 + R))ᶜ = 0)
    (hac : volume.withDensity (G.rnDeriv volume) ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ N0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, N0 ≤ N → ∀ (r : ℕ) (F : Fin r → Measure ℝ)
      [∀ j, IsProbabilityMeasure (F j)], (∀ j, ∃ a, F j (Icc a (a + L))ᶜ = 0) →
      ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        ∫ x, x ∂ν = N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) →
        ν (Icc (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) - κ * N)
          (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) + κ * N))ᶜ = 0 →
        ν ∈ AsymThree.aggSet (Sum.elim (fun _ : Fin N => G) F) :=
  AsymThree.cor_repeat hW hC convSq G hG hac hL

end Mixes.ConvSq
