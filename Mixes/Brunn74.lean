import Mixes.PrekopaLeindler

/-!
# Corollary 74 (b) with Brunn's theorem proved

`ScaledB.cor74b` and `Bridges.cor74b` (Corollary 74 (b), `g:cor:scaled`) take Brunn's theorem as
the hypothesis `hBrunn`: the law of `u(X)`, `X ∼ U(K)`, is the image under `y ↦ a + c y`
(`c > 0`) of the law on `[0, 1]` with density `g ^ (d - 1)`, `g ≥ 0` concave and continuous on
`[0, 1]`. With `PrekopaLeindler.brunnSections` this is now a theorem for convex bodies.

* `law_Ioo`: the density step of Corollary 68 (`Proj.cor68`) with `brunnSections`: the law of
  `u(X)` has density `h ^ (d - 1)` on `[a, b]`, `a < b`, `h ≥ 0` concave on `(a, b)`.
* `affine_of_Ioo`: the normalisation step of Theorem 67 (`Proj.pconc_Ioo`): such a law is the
  image of `densityOn01 (G ^ p)` under `y ↦ a + (b - a) y`, `G ≥ 0` concave and continuous on
  `[0, 1]`, `∫₀¹ G ^ p = 1`.
* `exists_brunn`: the data `(a, c, g)` for `hBrunn`, with all properties used by `cor74b`.
* `cor74b_brunn`: `ScaledB.cor74b` without `hBrunn` (the peeling and Theorem 27 data for this
  `g` and `G = densityOn01 (g ^ (d - 1))` remain hypotheses).
* `cor74b_bridges`: `Bridges.cor74b` without `hBrunn`: fully unconditional.
-/

open MeasureTheory Set Filter Topology Module
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Brunn74

open Mixes.Proj

section Density

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The density step of Corollary 68 with Brunn's theorem proved: for a convex body `K` in a
space of dimension `d ≥ 2` and `u ≠ 0`, the law of `u(X)`, `X ∼ U(K)`, is the probability measure
with density `h ^ (d - 1)` on `[a, b]`, `a < b`, where `h ≥ 0` is concave on `(a, b)`. -/
theorem law_Ioo {d : ℕ} (hd : 2 ≤ d) (hV : finrank ℝ V = d)
    {K : Set V} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (u : V →L[ℝ] ℝ) (hu : u ≠ 0) :
    ∃ a b : ℝ, ∃ h : ℝ → ℝ, a < b ∧ ConcaveOn ℝ (Ioo a b) h ∧ (∀ t ∈ Ioo a b, 0 ≤ h t) ∧
      IsProbabilityMeasure ((volume.restrict (Icc a b)).withDensity
        fun t => ENNReal.ofReal (h t ^ ((d : ℝ) - 1))) ∧
      (unifSet K).map u = (volume.restrict (Icc a b)).withDensity
        fun t => ENNReal.ofReal (h t ^ ((d : ℝ) - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hBrunn := PrekopaLeindler.brunnSections m
  have edm : ((m + 1 : ℕ) : ℝ) - 1 = m := by push_cast; ring
  rw [edm]
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
  have hBr := hBrunn C hCc hCconv
  rw [hfst, hUI] at hBr
  have hconc : ConcaveOn ℝ (Ioo a b) h := by
    have := (hBr.subset Ioo_subset_Icc_self (convex_Ioo a b)).smul
      (Real.rpow_nonneg hk0 ((m : ℝ)⁻¹))
    exact this
  have hh0 : ∀ t ∈ Ioo a b, 0 ≤ h t := fun t _ =>
    mul_nonneg (Real.rpow_nonneg hk0 _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  exact ⟨a, b, h, hab, hconc, hh0, hprob, hlaw⟩

end Density

/-- The normalisation step of Theorem 67: a probability density `h ^ p` on `[a, b]` (`p ≥ 1`,
`a < b`, `h ≥ 0` concave on `(a, b)`) is the image of `densityOn01 (G ^ p)` under
`y ↦ a + (b - a) y`, where `G ≥ 0` is concave and continuous on the closed interval `[0, 1]`
and `∫₀¹ G ^ p = 1`. -/
theorem affine_of_Ioo {p a b : ℝ} (hp : 1 ≤ p) (hab : a < b) {h : ℝ → ℝ}
    (hh : ConcaveOn ℝ (Ioo a b) h) (hh0 : ∀ x ∈ Ioo a b, 0 ≤ h x)
    (hprob : IsProbabilityMeasure
      ((volume.restrict (Icc a b)).withDensity fun x => ENNReal.ofReal (h x ^ p))) :
    ∃ G : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) G ∧ ContinuousOn G (Icc 0 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, 0 ≤ G x) ∧ ∫ x in (0:ℝ)..1, G x ^ p = 1 ∧
      (volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (h x ^ p)) =
        (Bipyramid.densityOn01 fun x => G x ^ p).map (fun y => a + (b - a) * y) := by
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
  exact ⟨G, hGc, hGcont, hG0, hdens, hTD.symm⟩

section Main

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Brunn's theorem in the form of `hBrunn`.** For a convex body `K` (compact, convex, with
nonempty interior) in a real space of dimension `d ≥ 2` and a nonzero linear functional `u`, there
are `a`, `c > 0` and `g ≥ 0`, concave and continuous on the closed interval `[0, 1]`, with
`∫₀¹ g ^ (d - 1) = 1`, such that the law of `u(X)`, `X ∼ U(K)`, is the image of the law
`densityOn01 (g ^ (d - 1))` (density `g ^ (d - 1)` on `[0, 1]`) under `y ↦ a + c y`. -/
theorem exists_brunn {d : ℕ} (hd : 2 ≤ d) (hV : finrank ℝ V = d)
    {K : Set V} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (u : V →L[ℝ] ℝ) (hu : u ≠ 0) :
    ∃ a c : ℝ, ∃ g : ℝ → ℝ, 0 < c ∧ ConcaveOn ℝ (Icc 0 1) g ∧ ContinuousOn g (Icc 0 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) ∧ ∫ x in (0:ℝ)..1, g x ^ ((d : ℝ) - 1) = 1 ∧
      IsProbabilityMeasure (Bipyramid.densityOn01 fun x => g x ^ ((d : ℝ) - 1)) ∧
      (unifSet K).map u =
        (Bipyramid.densityOn01 fun x => g x ^ ((d : ℝ) - 1)).map (fun y => a + c * y) := by
  obtain ⟨a, b, h, hab, hconc, hh0, hprob, hlaw⟩ := law_Ioo hd hV hKc hKconv hKi u hu
  have hp : (1:ℝ) ≤ (d : ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨g, hgc, hgcont, hg0, hdens, hT⟩ := affine_of_Ioo hp hab hconc hh0 hprob
  refine ⟨a, b - a, g, by linarith, hgc, hgcont, hg0, hdens, ?_, hlaw.trans hT⟩
  have hφ : Measurable fun y : ℝ => a + (b - a) * y := by fun_prop
  constructor
  have := hprob.measure_univ
  rw [hT, Measure.map_apply hφ MeasurableSet.univ, preimage_univ] at this
  exact this

open Bipyramid Scaled in
/-- **Corollary 74 (b)** in the form of `ScaledB.cor74b`, with Brunn's theorem proved. Let `K` be a
convex body in a real space of dimension `d ≥ 2` and `u ≠ 0` a linear functional. There are
`a`, `c > 0` and `g ≥ 0`, concave and continuous on `[0, 1]`, such that, with
`G = densityOn01 (g ^ (d - 1))` (the law of `(u(X) - a) / c`, `X ∼ U(K)`), the conclusion of
`ScaledB.cor74b` holds under its remaining hypotheses (`H34`, `hω`, `hdecomp`, `H27` for this `g`
and `G`): the laws of `u(X_i)`, `X_i ∼ U(t_i + λ_i K)`, are jointly mixable whenever
`λ ≥ 0` and `(d + 1) max λ_i ≤ ∑ λ_i`. -/
theorem cor74b_brunn {d : ℕ} (hd : 2 ≤ d) (hV : finrank ℝ V = d)
    {K : Set V} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (u : V →L[ℝ] ℝ) (hu : u ≠ 0) :
    ∃ a c : ℝ, ∃ g : ℝ → ℝ, 0 < c ∧ ConcaveOn ℝ (Icc 0 1) g ∧ ContinuousOn g (Icc 0 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) ∧
      (unifSet K).map u = (densityOn01 fun x => g x ^ ((d : ℝ) - 1)).map (fun y => a + c * y) ∧
      ∀ {n : ℕ} (ω : Measure ℝ) [IsProbabilityMeasure ω] (μ : ℝ) {A B : ℝ → ℝ}
        (_hA : Measurable A) (_hB : Measurable B)
        (_H34 : PeelingProps (fun x => g x ^ ((d : ℝ) - 1)) μ A B)
        (_hω : ∀ᵐ U ∂ω, 0 ≤ U ∧ U < g μ ^ ((d : ℝ) - 1))
        (_hdecomp : ∀ S, MeasurableSet S →
          (densityOn01 fun x => g x ^ ((d : ℝ) - 1)) S =
            ∫⁻ U, (pieceP (beta μ (A U) (B U))).map (pieceMap μ (μ - A U) (B U - μ)) S ∂ω)
        (_H27 : ∀ lam' : Fin n → ℝ, ∃ κ : ProbabilityTheory.Kernel ℝ (Fin n → ℝ),
          ProbabilityTheory.IsMarkovKernel κ ∧
          ∀ U, (∀ i, beta μ (A U) (B U) * lam' i ≤ ∑ j, lam' j) →
            IsJointMix (fun i => scaledPiece (beta μ (A U) (B U)) (lam' i)) (κ U) ∧
              ∀ᵐ v ∂(κ U), ∑ i, v i = ∑ i, lam' i)
        (t : Fin n → V) (lam : Fin n → ℝ) (_hlam : ∀ i, 0 ≤ lam i)
        (_hcond : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i),
        JointlyMixable fun i => ((unifSet K).map (fun x => t i + lam i • x)).map u := by
  obtain ⟨a, c, g, hc, hgc, hgcont, hg0, -, -, hBrunn⟩ := exists_brunn hd hV hKc hKconv hKi u hu
  refine ⟨a, c, g, hc, hgc, hgcont, hg0, hBrunn, ?_⟩
  intro n ω _ μ A B hA hB H34 hω hdecomp H27 t lam hlam hcond
  exact ScaledB.cor74b K d hd u hc hgc hgcont hg0 _ ω hBrunn μ hA hB H34 hω hdecomp H27 t lam
    hlam hcond

/-- **Corollary 74 (b)** (`g:cor:scaled`), unconditionally (`Bridges.cor74b` with Brunn's theorem
proved). Let `K` be a convex body (compact, convex, with nonempty interior) in a real space of
dimension `d ≥ 2`, `u` a nonzero linear functional, `n ≥ 2`, `t_i ∈ V` and `λ_i ≥ 0`, not all
zero, with `(d + 1) max λ_i ≤ ∑ λ_i`. Then the laws of `u(X_1), …, u(X_n)`,
`X_i ∼ U(t_i + λ_i K)`, are jointly mixable. -/
theorem cor74b_bridges {d : ℕ} (hd : 2 ≤ d) (hV : finrank ℝ V = d)
    {K : Set V} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (u : V →L[ℝ] ℝ) (hu : u ≠ 0) {n : ℕ} (hn : 2 ≤ n) (t : Fin n → V) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (hcond : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => ((unifSet K).map (fun x => t i + lam i • x)).map u := by
  obtain ⟨a, c, g, hc, hgc, hgcont, hg0, hdens, -, hBrunn⟩ :=
    exists_brunn hd hV hKc hKconv hKi u hu
  exact Bridges.cor74b K d hd u hc hgc hgcont hg0 hdens hBrunn hn t lam hlam hne hcond

end Main

end Mixes.Brunn74
