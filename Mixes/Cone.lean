import Mixes.Defs

/-!
# Cones: slicing and necessity (Lemma 42, Theorem 43 (a), Remark 47)

Item M1b of the verification priorities (`s:lem:cone`, `s:thm:cone`, `s:rem:two` in
`mixes/main.tex`).

## Setting

`V` is a finite-dimensional real space with an additive Haar measure `volume`, and
`L : V ≃L[ℝ] ℝ × ℝ^m` are linear coordinates whose first coordinate is the functional `ℓ`
(`k = dim V = m + 1`). The base is `F = L⁻¹({1} × B)` (`coneBase`), with `B ⊆ ℝ^m` measurable of
finite positive volume, and the cone is `K = {s y : 0 ≤ s ≤ 1, y ∈ F}` (`coneSet`). Every cone of
the paper (`F` compact convex of dimension `k - 1` in `{ℓ = 1}`) is of this form. `U(sF)` is
`sliceUnif L B s`, the image of `U(B)` under `b ↦ s L⁻¹(1, b)`; `U(t + lam K)` is `coneUnif`,
with `U({t}) = δ_t` for `lam = 0`.

## Main results

* `IsJointMix.map_affine`: images of a joint mix under `x ↦ aᵢ + φ x`, `φ` additive.
* `IsJointMix.ae_le_sum_lintegral`: the one-dimensional necessary condition: nonnegative jointly
  mixable distributions on `ℝ` are each concentrated on `[0, ∑ᵢ meanᵢ]`.
* Lemma 42: `unifSet_scaledCone` (the converse statement), `unifSet_scaledCone_bind` (given `S`,
  `X - t ∼ U(S F)`), `unifSet_scaledCone_split` (`S` and the base point `Y` are independent with
  laws `coneRadial m lam` and `U(B)`), `unifSet_scaledCone_map_ell` (`S` has the density
  `k s^(k-1) lam^(-k)` on `[0, lam]`), `unifSet_scaledCone_ae_reconstruct`.
* Theorem 43 (a): `cone_jointlyMixable_le` (`(k + 1) λⱼ ≤ ∑ λᵢ`), `cone_completelyMixable_le`
  (`n ≥ k + 1`), and the instances `simplex_completelyMixable_le`,
  `pyramid_completelyMixable_le`.
* Remark 47: `completelyMixable_two_iff` (two copies mix exactly the distributions symmetric about a
  point) and `trap_completelyMixable_two_iff` (for the normalised trapezoids of Theorem 40,
  `n = 2` works exactly for parallelograms).
-/

open MeasureTheory Set

noncomputable section

namespace Mixes

/-! ### Images of joint mixes -/

section General

variable {n : ℕ} {E E' : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableSpace E'] [AddCommMonoid E'] [MeasurableSingletonClass E'] [MeasurableAdd₂ E']

/-- The coordinatewise image of a joint mix under affine maps `x ↦ aᵢ + φ x` with the same
additive part `φ` is a joint mix of the image distributions. -/
theorem IsJointMix.map_affine {F : Fin n → Measure E} {P : Measure (Fin n → E)}
    (h : IsJointMix F P) (φ : E →+ E') (hφ : Measurable φ) (a : Fin n → E') :
    IsJointMix (fun i => (F i).map (fun x => a i + φ x))
      (P.map (fun x i => a i + φ (x i))) := by
  obtain ⟨hP, ⟨s, hs⟩, hm⟩ := h
  have hf : Measurable (fun (x : Fin n → E) (i : Fin n) => a i + φ (x i)) :=
    measurable_pi_iff.mpr fun i => (hφ.comp (measurable_pi_apply i)).const_add _
  refine ⟨inferInstance, ⟨∑ i, a i + φ s, ?_⟩, fun j => ?_⟩
  · have hmeas : MeasurableSet {y : Fin n → E' | ∑ j, y j = ∑ i, a i + φ s} :=
      (measurableSet_singleton _).preimage
        (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
    rw [ae_map_iff hf.aemeasurable hmeas]
    filter_upwards [hs] with x hx
    simp only [Finset.sum_add_distrib, ← map_sum, hx]
  · show _ = (F j).map _
    rw [Measure.map_map (measurable_pi_apply j) hf, ← hm j,
      Measure.map_map (hφ.const_add _) (measurable_pi_apply j)]
    rfl

end General

/-! ### The one-dimensional necessary condition -/

/-- If `G 0, …, G (n-1)` on `ℝ` are concentrated on `[0, ∞)` and `Q` is a joint mix of them, then
each `G j` is concentrated on `[0, ∑ᵢ mean(G i)]` (means as `lintegral`s, possibly infinite). -/
theorem IsJointMix.ae_le_sum_lintegral {n : ℕ} {G : Fin n → Measure ℝ} {Q : Measure (Fin n → ℝ)}
    (h : IsJointMix G Q) (hpos : ∀ i, ∀ᵐ x ∂G i, 0 ≤ x) (j : Fin n) :
    ∀ᵐ x ∂G j, ENNReal.ofReal x ≤ ∑ i, ∫⁻ y, ENNReal.ofReal y ∂G i := by
  obtain ⟨hQ, ⟨s, hs⟩, hm⟩ := h
  have hposQ : ∀ᵐ x ∂Q, ∀ i, 0 ≤ x i := by
    rw [ae_all_iff]
    intro i
    have := hpos i
    rw [← hm i] at this
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable this
  have hsum : ∑ i, ∫⁻ y, ENNReal.ofReal y ∂G i = ENNReal.ofReal s := by
    simp_rw [← hm]
    rw [Finset.sum_congr rfl fun i _ =>
      lintegral_map (ENNReal.measurable_ofReal) (measurable_pi_apply i)]
    rw [← lintegral_finsetSum (f := fun i (x : Fin n → ℝ) => ENNReal.ofReal (x i)) _
      fun i _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply i)]
    rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal s), lintegral_const, measure_univ,
      mul_one]
    filter_upwards [hs, hposQ] with x hx hx'
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hx' i, hx]
  rw [hsum, ← hm j]
  refine (ae_map_iff (measurable_pi_apply j).aemeasurable ?_).2 ?_
  · exact measurableSet_le ENNReal.measurable_ofReal measurable_const
  filter_upwards [hs, hposQ] with x hx hx'
  apply ENNReal.ofReal_le_ofReal
  rw [← hx]
  exact Finset.single_le_sum (fun i _ => hx' i) (Finset.mem_univ j)

/-! ### Two copies (Remark 47, first paragraph) -/

/-- A distribution is `2`-completely mixable if and only if it is symmetric about a point:
if `X₁ + X₂ = s`, then `X₂ = s - X₁`. -/
theorem completelyMixable_two_iff {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [MeasurableSub E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] (F : Measure E)
    [IsProbabilityMeasure F] :
    CompletelyMixable 2 F ↔ ∃ c : E, F.map (fun x => c - x) = F := by
  constructor
  · rintro ⟨P, hP, ⟨s, hs⟩, hm⟩
    refine ⟨s, ?_⟩
    have h1 : P.map (fun x => x 1) = P.map (fun x => s - x 0) := by
      apply Measure.map_congr
      filter_upwards [hs] with x hx
      rw [Fin.sum_univ_two] at hx
      rw [← hx]; abel
    have h2 := hm 1
    rw [h1] at h2
    calc F.map (fun x => s - x) = (P.map (fun x => x 0)).map (fun x => s - x) := by rw [hm 0]
      _ = P.map (fun x => s - x 0) :=
        Measure.map_map (measurable_const_sub s) (measurable_pi_apply 0)
      _ = F := h2
  · rintro ⟨c, hc⟩
    have hf : Measurable (fun x : E => (![x, c - x] : Fin 2 → E)) := by
      refine measurable_pi_iff.mpr fun i => ?_
      fin_cases i
      · exact measurable_id
      · exact measurable_const_sub c
    refine ⟨F.map (fun x => ![x, c - x]), inferInstance,
      ⟨c, ?_⟩, fun j => ?_⟩
    · rw [ae_map_iff hf.aemeasurable]
      · exact Filter.Eventually.of_forall fun x => by simp
      · exact (measurableSet_singleton _).preimage
          (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
    · rw [Measure.map_map (measurable_pi_apply j) hf]
      fin_cases j
      · exact Measure.map_id
      · exact hc

/-! ### Trapezoids with two copies (Remark 47, first paragraph) -/

/-- The normalised trapezoid of Theorem 40: `{(x, y) : 0 ≤ x ≤ 1, g x ≤ y ≤ g x + h x}` with
`g x = a + b x` and `h x = q + (1 - q) x`. For `0 ≤ q ≤ 1` it is a triangle (`q = 0`), a
trapezoid, or a parallelogram (`q = 1`). -/
def trapSet (q a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc (a + b * p.1) (a + b * p.1 + (q + (1 - q) * p.1))}

lemma measurableSet_trapSet (q a b : ℝ) : MeasurableSet (trapSet q a b) := by
  have : IsClosed (trapSet q a b) :=
    ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).inter
      ((isClosed_le (by fun_prop) continuous_snd).inter (isClosed_le continuous_snd (by fun_prop)))
  exact this.measurableSet

/-- Fubini for the trapezoid: the mass of the strip over `A` is `∫_{A ∩ [0,1]} h`. -/
lemma volume_trapSet_inter (q a b : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    volume (trapSet q a b ∩ Prod.fst ⁻¹' A) =
      ∫⁻ x in A ∩ Icc 0 1, ENNReal.ofReal (q + (1 - q) * x) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply
    ((measurableSet_trapSet q a b).inter (measurable_fst hA)),
    ← lintegral_indicator (hA.inter measurableSet_Icc)]
  congr 1
  funext x
  by_cases hx : x ∈ A ∩ Icc 0 1
  · rw [indicator_of_mem hx]
    have : Prod.mk x ⁻¹' (trapSet q a b ∩ Prod.fst ⁻¹' A) =
        Icc (a + b * x) (a + b * x + (q + (1 - q) * x)) := by
      ext y
      simp only [trapSet, mem_preimage, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1.2, fun h => ⟨⟨hx.2, h⟩, hx.1⟩⟩
    rw [this, Real.volume_Icc]
    ring_nf
  · rw [indicator_of_notMem hx]
    have : Prod.mk x ⁻¹' (trapSet q a b ∩ Prod.fst ⁻¹' A) = ∅ := by
      ext y
      simp only [trapSet, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      exact fun h => hx ⟨h.2, h.1.1⟩
    rw [this, measure_empty]

/-- `∫_{[u,v]} h = q (v - u) + (1 - q) (v² - u²) / 2` for `0 ≤ u ≤ v ≤ 1`. -/
lemma lintegral_trapH_Icc {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (_hv : v ≤ 1) :
    ∫⁻ x in Icc u v, ENNReal.ofReal (q + (1 - q) * x) =
      ENNReal.ofReal (q * (v - u) + (1 - q) * (v ^ 2 - u ^ 2) / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
      intervalIntegral.integral_add (f := fun _ => q) (g := fun x => (1 - q) * x)
        intervalIntegrable_const
        ((by fun_prop : Continuous fun x : ℝ => (1 - q) * x).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring_nf
  · exact (by fun_prop : Continuous fun x : ℝ => q + (1 - q) * x).integrableOn_Icc
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx => ?_
    show 0 ≤ q + (1 - q) * x
    have : 0 ≤ (1 - q) * x := mul_nonneg (by linarith) (by linarith [hx.1])
    linarith

lemma volume_trapSet {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a b : ℝ) :
    volume (trapSet q a b) = ENNReal.ofReal ((q + 1) / 2) := by
  have := volume_trapSet_inter q a b MeasurableSet.univ
  rw [preimage_univ, inter_univ, univ_inter, lintegral_trapH_Icc hq0 hq1 le_rfl zero_le_one
    le_rfl] at this
  rw [this]
  congr 1
  ring

/-- Two copies mix the uniform distribution on a normalised trapezoid (`0 ≤ q ≤ 1`, which
includes the triangle) if and only if it is a parallelogram (`q = 1`). -/
theorem trap_completelyMixable_two_iff {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a b : ℝ) :
    CompletelyMixable 2 (unifSet (trapSet q a b)) ↔ q = 1 := by
  set T := trapSet q a b with hTdef
  have hT := measurableSet_trapSet q a b
  have hvol := volume_trapSet hq0 hq1 a b
  have hvol0 : volume T ≠ 0 := by
    rw [hvol]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hvolt : volume T ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have : IsProbabilityMeasure (unifSet T) := by
    constructor
    rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel hvol0 hvolt]
  rw [completelyMixable_two_iff]
  constructor
  · rintro ⟨c, hc⟩
    -- the mass of the strip over `A`
    set M : Set ℝ → ENNReal := fun A => ∫⁻ x in A ∩ Icc 0 1, ENNReal.ofReal (q + (1 - q) * x)
    have key : ∀ A : Set ℝ, MeasurableSet A → M A = M {x | c.1 - x ∈ A} := by
      intro A hA
      have hA' : MeasurableSet {x : ℝ | c.1 - x ∈ A} := (measurable_const_sub c.1) hA
      have h1 : (Measure.map (fun x => c - x) (unifSet T)) (Prod.fst ⁻¹' A) =
          unifSet T (Prod.fst ⁻¹' A) := by rw [hc]
      rw [Measure.map_apply (measurable_const_sub c) (measurable_fst hA)] at h1
      have hpre : (fun x : ℝ × ℝ => c - x) ⁻¹' (Prod.fst ⁻¹' A) =
          Prod.fst ⁻¹' {x | c.1 - x ∈ A} := by
        ext p; simp
      rw [hpre, unifSet, smul_apply, smul_apply,
        Measure.restrict_apply (measurable_fst hA'), Measure.restrict_apply (measurable_fst hA),
        smul_eq_mul, smul_eq_mul, inter_comm, inter_comm _ T] at h1
      have h2 := (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 hvolt)
        (ENNReal.inv_ne_top.2 hvol0)).1 h1
      rw [volume_trapSet_inter q a b hA', volume_trapSet_inter q a b hA] at h2
      exact h2.symm
    have Mpos : ∀ u v, 0 ≤ u → u < v → v ≤ 1 → ∀ S : Set ℝ, Icc u v ⊆ S → 0 < M S := by
      intro u v hu huv hv S hS
      have hsub : Icc u v ⊆ S ∩ Icc 0 1 := fun x hx =>
        ⟨hS hx, le_trans hu hx.1, le_trans hx.2 hv⟩
      refine lt_of_lt_of_le ?_ (lintegral_mono_set hsub)
      rw [lintegral_trapH_Icc hq0 hq1 hu huv.le hv, ENNReal.ofReal_pos]
      have : 0 < v - u := by linarith
      have : 0 ≤ v ^ 2 - u ^ 2 := by nlinarith
      rcases eq_or_lt_of_le hq0 with h | h
      · subst h; nlinarith
      · nlinarith
    have Mzero : ∀ S : Set ℝ, S ∩ Icc 0 1 = ∅ → M S = 0 := by
      intro S hS; simp only [M, hS, Measure.restrict_empty, lintegral_zero_measure]
    -- the centre of symmetry has abscissa `1`
    have hc1 : c.1 ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h0 := key (Ioi 1) measurableSet_Ioi
      have hE : Ioi (1 : ℝ) ∩ Icc 0 1 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_empty_iff_false, iff_false]
        intro h; linarith [h.2.2]
      rw [Mzero (Ioi 1) hE] at h0
      set ε := min (c.1 - 1) 1
      have hε : 0 < ε := lt_min (by linarith) one_pos
      have hε1 : ε ≤ c.1 - 1 := min_le_left _ _
      have hε2 : ε ≤ 1 := min_le_right _ _
      have := Mpos (ε / 4) (ε / 2) (by positivity) (by linarith) (by linarith)
        {x | c.1 - x ∈ Ioi 1} (fun x hx => by
          simp only [mem_ofPred_eq, mem_Ioi]; linarith [hx.2])
      rw [← h0] at this
      exact lt_irrefl _ this
    have hc2 : 1 ≤ c.1 := by
      by_contra hlt
      push Not at hlt
      have h0 := key (Iio 0) measurableSet_Iio
      have hE : Iio (0 : ℝ) ∩ Icc 0 1 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_empty_iff_false, iff_false]
        intro h; linarith [h.2.1]
      rw [Mzero (Iio 0) hE] at h0
      set δ := min (1 - c.1) 1
      have hδ : 0 < δ := lt_min (by linarith) one_pos
      have hδ1 : δ ≤ 1 - c.1 := min_le_left _ _
      have hδ2 : δ ≤ 1 := min_le_right _ _
      have := Mpos (1 - δ / 2) 1 (by linarith) (by linarith) le_rfl
        {x | c.1 - x ∈ Iio 0} (fun x hx => by
          simp only [mem_ofPred_eq, mem_Iio]; linarith [hx.1])
      rw [← h0] at this
      exact lt_irrefl _ this
    have hc : c.1 = 1 := le_antisymm hc1 hc2
    have h := key (Iic (1 / 2)) measurableSet_Iic
    have e1 : Iic (1 / 2 : ℝ) ∩ Icc 0 1 = Icc 0 (1 / 2) := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    have e2 : {x : ℝ | c.1 - x ∈ Iic (1 / 2)} ∩ Icc 0 1 = Icc (1 / 2) 1 := by
      ext x; simp only [hc, mem_inter_iff, mem_ofPred_eq, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨by linarith, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, h2⟩
    simp only [M, e1, e2] at h
    rw [lintegral_trapH_Icc hq0 hq1 le_rfl (by norm_num) (by norm_num),
      lintegral_trapH_Icc hq0 hq1 (by norm_num) (by norm_num) le_rfl,
      ENNReal.ofReal_eq_ofReal_iff (by nlinarith) (by nlinarith)] at h
    linarith
  · rintro rfl
    refine ⟨(1, 2 * a + b + 1), ?_⟩
    have hpre : (fun x : ℝ × ℝ => ((1 : ℝ), 2 * a + b + 1) - x) ⁻¹' T = T := by
      ext p
      simp only [hTdef, trapSet, mem_preimage, mem_ofPred_eq, mem_Icc, Prod.fst_sub, Prod.snd_sub]
      constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩ <;>
        nlinarith
    have hmp := (Measure.measurePreserving_sub_left (volume : Measure (ℝ × ℝ))
      ((1 : ℝ), 2 * a + b + 1)).restrict_preimage hT
    rw [hpre] at hmp
    rw [unifSet, Measure.map_smul, hmp.map_eq]
    exact (measurable_const_sub _).aemeasurable

/-! ### Cones and their slicing (Lemma 42) -/

section ConeDefs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ}

/-- The base `F = L⁻¹({1} × B)` of a cone. It lies in the hyperplane `{ℓ = 1}`, where
`ℓ x = (L x).1`; the linear coordinates `L` have `ℓ` as first coordinate, and `B ⊆ ℝ^m` is the
image of `F` in the remaining coordinates (`k = m + 1`). -/
def coneBase (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (B : Set (Fin m → ℝ)) : Set V :=
  {y | ∃ b ∈ B, y = L.symm (1, b)}

/-- The cone `K = {s y : 0 ≤ s ≤ 1, y ∈ F}` over `F = coneBase L B`. -/
def coneSet (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (B : Set (Fin m → ℝ)) : Set V :=
  {x | ∃ s ∈ Icc (0 : ℝ) 1, ∃ y ∈ coneBase L B, x = s • y}

/-- The scaled translate `t + lam K`. -/
def scaledTranslate (t : V) (lam : ℝ) (K : Set V) : Set V :=
  {x | ∃ y ∈ K, x = t + lam • y}

/-- The distribution with density `k s^(k-1) lam^(-k)` on `[0, lam]`, `k = m + 1`. -/
def coneRadial (m : ℕ) (lam : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 lam)).withDensity
    fun s => ENNReal.ofReal ((m + 1) * s ^ m / lam ^ (m + 1))

/-- `U(sF)`: the uniform distribution on the slice `s F`, as the image of `U(B)` under the affine
parametrisation `b ↦ s L⁻¹(1, b)`; for `s = 0` it is the point mass at `0`. Any two affine
parametrisations of the hyperplane give Lebesgue measures that differ by a constant factor, so
this is the normalised Lebesgue measure on the affine hull of `s F` for `s ≠ 0`. -/
def sliceUnif [MeasurableSpace V] (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (B : Set (Fin m → ℝ)) (s : ℝ) :
    Measure V :=
  (unifSet B).map fun b => s • L.symm (1, b)

end ConeDefs

/-- Integrals against `coneRadial`. -/
lemma lintegral_coneRadial {m : ℕ} {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ s ∈ Icc 0 lam, 0 ≤ f s) :
    ∫⁻ s, ENNReal.ofReal (f s) ∂coneRadial m lam =
      ENNReal.ofReal (∫ s in (0 : ℝ)..lam, f s * ((m + 1) * s ^ m / lam ^ (m + 1))) := by
  rw [coneRadial, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hcont : Continuous fun s : ℝ => f s * ((m + 1) * s ^ m / lam ^ (m + 1)) := by fun_prop
  rw [intervalIntegral.integral_of_le hlam.le, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc]
  · refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm, ENNReal.ofReal_mul (hf0 s hs)]
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_
    have := hs.1
    exact mul_nonneg (hf0 s hs) (by positivity)

lemma coneRadial_isProb (m : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    IsProbabilityMeasure (coneRadial m lam) := by
  constructor
  have h := lintegral_coneRadial (m := m) hlam (f := fun _ => 1) continuous_const
    (fun _ _ => zero_le_one)
  simp only [ENNReal.ofReal_one, lintegral_one, one_mul] at h
  rw [h]
  have : (fun s : ℝ => (m + 1) * s ^ m / lam ^ (m + 1)) =
      fun s => ((m + 1) / lam ^ (m + 1)) * s ^ m := by funext s; ring
  rw [this, intervalIntegral.integral_const_mul, integral_pow]
  have hl : lam ^ (m + 1) ≠ 0 := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [zero_pow (Nat.succ_ne_zero m)]
  field_simp
  simp [hlam.ne']

lemma coneRadial_ae_mem (m : ℕ) (lam : ℝ) : ∀ᵐ s ∂coneRadial m lam, s ∈ Icc 0 lam :=
  (ae_restrict_mem measurableSet_Icc).filter_mono (withDensity_absolutelyContinuous _ _).ae_le

lemma coneRadial_ae_ne_zero (m : ℕ) (lam : ℝ) : ∀ᵐ s ∂coneRadial m lam, s ≠ 0 := by
  have h : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
    rw [ae_iff]; simp
  exact (h.filter_mono (ae_restrict_le)).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

/-- Uniform distributions on sets that agree almost everywhere coincide. -/
lemma unifSet_congr {α : Type*} [MeasureSpace α] {S S' : Set α} (h : S =ᵐ[volume] S') :
    unifSet S = unifSet S' := by
  rw [unifSet, unifSet, measure_congr h, Measure.restrict_congr_set h]

/-- Transport of uniform distributions along a measurable equivalence that scales volume by a
constant factor. -/
lemma unifSet_preimage {α β : Type*} [MeasureSpace α] [MeasureSpace β] (e : α ≃ᵐ β)
    {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (he : volume.map e = c • volume) {C : Set β}
    (hC : MeasurableSet C) : unifSet (e ⁻¹' C) = (unifSet C).map e.symm := by
  have h1 : (unifSet (e ⁻¹' C)).map e = unifSet C := by
    rw [unifSet, Measure.map_smul, ← Measure.restrict_map e.measurable hC, he,
      ← Measure.map_apply e.measurable hC, he, Measure.restrict_smul, smul_smul, unifSet,
      smul_apply, smul_eq_mul]
    congr 1
    by_cases hv : volume C = ⊤
    · rw [hv, ENNReal.mul_top hc0]; simp
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel hc0 hct, mul_one]
    exact e.measurable.aemeasurable
  rw [← h1, e.map_symm_map]

lemma unifSet_isProb {α : Type*} [MeasureSpace α] {S : Set α} (h0 : volume S ≠ 0)
    (ht : volume S ≠ ⊤) : IsProbabilityMeasure (unifSet S) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]

section Coord

variable {m : ℕ} {B : Set (Fin m → ℝ)} {lam : ℝ}

/-- The scaled cone in the coordinates `ℝ × ℝ^m`, without its apex:
`{(s, z) : 0 < s ≤ lam, s⁻¹ z ∈ B}`. -/
def coneCoord (m : ℕ) (B : Set (Fin m → ℝ)) (lam : ℝ) : Set (ℝ × (Fin m → ℝ)) :=
  {p | 0 < p.1 ∧ p.1 ≤ lam ∧ p.1⁻¹ • p.2 ∈ B}

lemma measurableSet_coneCoord (hB : MeasurableSet B) : MeasurableSet (coneCoord m B lam) := by
  have h3 : MeasurableSet {p : ℝ × (Fin m → ℝ) | p.1⁻¹ • p.2 ∈ B} :=
    hB.preimage (measurable_fst.inv.smul measurable_snd)
  exact (measurableSet_lt (measurable_const (a := (0 : ℝ))) measurable_fst).inter
    ((measurableSet_le measurable_fst (measurable_const (a := lam))).inter h3)

lemma measurable_coneMap :
    Measurable (fun p : ℝ × (Fin m → ℝ) => (p.1, p.1 • p.2)) :=
  measurable_fst.prodMk (measurable_fst.smul measurable_snd)

/-- Fubini's theorem for the cone in coordinates: the section at `s ∈ (0, lam]` is `s B`, of
measure `s^m` times that of `B`. -/
lemma volume_restrict_coneCoord (hB : MeasurableSet B) :
    volume.restrict (coneCoord m B lam) =
      (((volume.restrict (Ioc 0 lam)).withDensity fun s => ENNReal.ofReal (s ^ m)).prod
        (volume.restrict B)).map (fun p => (p.1, p.1 • p.2)) := by
  ext A hA
  have hΦA := measurable_coneMap hA
  rw [Measure.restrict_apply hA, Measure.map_apply measurable_coneMap hA,
    Measure.prod_apply hΦA,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_left hΦA),
    Measure.volume_eq_prod, Measure.prod_apply (hA.inter (measurableSet_coneCoord hB)),
    ← lintegral_indicator measurableSet_Ioc]
  congr 1
  funext s
  by_cases hs : s ∈ Ioc 0 lam
  · rw [indicator_of_mem hs, Pi.mul_apply,
      Measure.restrict_apply (measurable_prodMk_left hΦA)]
    have hs0 : s ≠ 0 := hs.1.ne'
    have hsec : Prod.mk s ⁻¹' (A ∩ coneCoord m B lam) =
        (fun z => s⁻¹ • z) ⁻¹' (Prod.mk s ⁻¹' ((fun p : ℝ × (Fin m → ℝ) => (p.1, p.1 • p.2)) ⁻¹' A)
          ∩ B) := by
      ext z
      simp only [coneCoord, mem_preimage, mem_inter_iff, mem_ofPred_eq, smul_inv_smul₀ hs0]
      exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, hs.1, hs.2, h.2⟩⟩
    rw [hsec, Measure.addHaar_preimage_smul _ (inv_ne_zero hs0), Module.finrank_fin_fun,
      inv_pow, inv_inv, abs_of_pos (pow_pos hs.1 m)]
  · rw [indicator_of_notMem hs]
    have : Prod.mk s ⁻¹' (A ∩ coneCoord m B lam) = ∅ := by
      ext z
      simp only [coneCoord, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      exact fun h => hs ⟨h.2.1, h.2.2.1⟩
    rw [this, measure_empty]

/-- Lemma 42 in coordinates. -/
lemma unifSet_coneCoord (hB : MeasurableSet B) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    (hlam : 0 < lam) :
    unifSet (coneCoord m B lam) =
      ((coneRadial m lam).prod (unifSet B)).map (fun p => (p.1, p.1 • p.2)) := by
  set ν := (((volume.restrict (Ioc 0 lam)).withDensity fun s => ENNReal.ofReal (s ^ m)).prod
    (volume.restrict B)).map (fun p : ℝ × (Fin m → ℝ) => (p.1, p.1 • p.2)) with hν
  have hA := volume_restrict_coneCoord (lam := lam) hB
  set c : ENNReal := ENNReal.ofReal ((m + 1) / lam ^ (m + 1)) * (volume B)⁻¹
  have hρ : coneRadial m lam = ENNReal.ofReal ((m + 1) / lam ^ (m + 1)) •
      ((volume.restrict (Ioc 0 lam)).withDensity fun s => ENNReal.ofReal (s ^ m)) := by
    rw [coneRadial, Measure.restrict_congr_set Ioc_ae_eq_Icc.symm,
      ← withDensity_smul _ (by fun_prop)]
    congr 1
    funext s
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  have hR : ((coneRadial m lam).prod (unifSet B)).map (fun p => (p.1, p.1 • p.2)) = c • ν := by
    rw [hρ, unifSet, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul,
      Measure.map_smul, smul_smul]
    all_goals exact measurable_coneMap.aemeasurable
  have hprob : IsProbabilityMeasure (((coneRadial m lam).prod (unifSet B)).map
      (fun p : ℝ × (Fin m → ℝ) => (p.1, p.1 • p.2))) := by
    have := coneRadial_isProb m hlam
    have := unifSet_isProb hB0 hBt
    infer_instance
  have h1 : c * ν univ = 1 := by
    have := hprob.measure_univ
    rw [hR, smul_apply, smul_eq_mul] at this
    exact this
  have hvol : volume (coneCoord m B lam) = ν univ := by
    rw [← Measure.restrict_apply_univ, hA]
  rw [hR, unifSet, hvol, hA, ← ENNReal.eq_inv_of_mul_eq_one_left h1]

end Coord

section ConeV

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}
  (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) {B : Set (Fin m → ℝ)}

/-- The chart `x ↦ L (x - t)`. -/
def coneChart (t : V) : V ≃ᵐ ℝ × (Fin m → ℝ) :=
  ((Homeomorph.addRight (-t)).trans L.toHomeomorph).toMeasurableEquiv

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
lemma coneChart_apply (t x : V) : coneChart L t x = L (x - t) := by
  simp [coneChart, sub_eq_add_neg]

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
lemma coneChart_symm_apply (t : V) (w : ℝ × (Fin m → ℝ)) :
    (coneChart L t).symm w = t + L.symm w := by
  apply (coneChart L t).injective
  rw [MeasurableEquiv.apply_symm_apply, coneChart_apply, add_sub_cancel_left,
    ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ V] in
lemma map_coneChart (t : V) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ volume.map (coneChart L t) = c • volume := by
  have h1 : volume.map (coneChart L t) = (volume.map (fun x : V => x + -t)).map L := by
    rw [Measure.map_map L.continuous.measurable (measurable_add_const _)]
    rfl
  rw [h1, map_add_right_eq_self]
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  refine ⟨(Measure.addHaarScalarFactor (volume.map L) volume : ENNReal),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map L) volume]
  ext s hs
  simp

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma smul_symm_one (s : ℝ) (b : Fin m → ℝ) : L.symm (s, s • b) = s • L.symm (1, b) := by
  rw [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one]

lemma preimage_coneChart_ae_eq (t : V) {lam : ℝ} (hlam : 0 < lam) :
    coneChart L t ⁻¹' coneCoord m B lam =ᵐ[volume] scaledTranslate t lam (coneSet L B) := by
  have hsub : coneChart L t ⁻¹' coneCoord m B lam ⊆ scaledTranslate t lam (coneSet L B) := by
    intro x hx
    simp only [mem_preimage, coneChart_apply, coneCoord, mem_ofPred_eq] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    set w := L (x - t)
    refine ⟨(w.1 / lam) • L.symm (1, w.1⁻¹ • w.2),
      ⟨w.1 / lam, ⟨by positivity, (div_le_one hlam).2 h2⟩, _, ⟨_, h3, rfl⟩, rfl⟩, ?_⟩
    rw [smul_smul, mul_div_cancel₀ _ hlam.ne', ← smul_symm_one, smul_inv_smul₀ h1.ne']
    have : (w.1, w.2) = L (x - t) := rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hsup : scaledTranslate t lam (coneSet L B) \ coneChart L t ⁻¹' coneCoord m B lam ⊆
      {t} := by
    rintro x ⟨⟨y, ⟨r, hr, z, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩, hx⟩
    rcases eq_or_lt_of_le hr.1 with h | h
    · subst h; simp
    · exfalso
      apply hx
      have hL : L (lam • r • L.symm (1, b)) = (lam * r, (lam * r) • b) := by
        rw [smul_smul, map_smul, ContinuousLinearEquiv.apply_symm_apply, Prod.smul_mk,
          smul_eq_mul, mul_one]
      simp only [mem_preimage, coneChart_apply, coneCoord, mem_ofPred_eq, add_sub_cancel_left, hL]
      have hpos : 0 < lam * r := mul_pos hlam h
      refine ⟨hpos, ?_, ?_⟩
      · nlinarith [hr.2]
      · rwa [inv_smul_smul₀ hpos.ne']
  have : Nontrivial V := L.toEquiv.nontrivial
  refine ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 hsub, measure_empty], ?_⟩
  exact measure_mono_null hsup (measure_singleton t)

/-- **Lemma 42 (slicing of a cone), converse direction.** Let `K` be the cone over
`F = L⁻¹({1} × B)`, `lam > 0` and `t ∈ V`. If `S` has the density `k s^(k-1) lam^(-k)` on
`[0, lam]` (`k = m + 1`) and, independently, `Y ∼ U(B)`, so that given `S` the vector
`W = S L⁻¹(1, Y)` is uniform on `S F`, then `t + W ∼ U(t + lam K)`. -/
theorem unifSet_scaledCone (hB : MeasurableSet B) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    (t : V) {lam : ℝ} (hlam : 0 < lam) :
    unifSet (scaledTranslate t lam (coneSet L B)) =
      ((coneRadial m lam).prod (unifSet B)).map (fun p => t + p.1 • L.symm (1, p.2)) := by
  obtain ⟨c, hc0, hct, he⟩ := map_coneChart L t
  rw [← unifSet_congr (preimage_coneChart_ae_eq L t hlam),
    unifSet_preimage (coneChart L t) hc0 hct he (measurableSet_coneCoord hB),
    unifSet_coneCoord hB hB0 hBt hlam,
    Measure.map_map (coneChart L t).symm.measurable measurable_coneMap]
  congr 1
  funext p
  simp only [Function.comp_apply, coneChart_symm_apply, smul_symm_one]

/-- **Lemma 42, conditional form.** `U(t + lam K)` is the mixture over `S ∼ coneRadial m lam` of
the translates by `t` of `U(S F)` (`sliceUnif`): given `S`, `X - t` is uniform on `S F`. -/
theorem unifSet_scaledCone_bind (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (t : V) {lam : ℝ} (hlam : 0 < lam) :
    unifSet (scaledTranslate t lam (coneSet L B)) =
      (coneRadial m lam).bind fun s => (sliceUnif L B s).map (fun w => t + w) := by
  have hf : Measurable fun p : ℝ × (Fin m → ℝ) => t + p.1 • L.symm (1, p.2) := by fun_prop
  have hk : ∀ s, (sliceUnif L B s).map (fun w => t + w) =
      (unifSet B).map (fun b => t + s • L.symm (1, b)) := by
    intro s
    rw [sliceUnif, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  simp only [hk]
  have := unifSet_isProb hB0 hBt
  have hmeas : Measurable fun s : ℝ => (unifSet B).map (fun b => t + s • L.symm (1, b)) := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : (fun s : ℝ => (unifSet B).map (fun b => t + s • L.symm (1, b)) A) =
        fun s => unifSet B (Prod.mk s ⁻¹' ((fun p : ℝ × (Fin m → ℝ) =>
          t + p.1 • L.symm (1, p.2)) ⁻¹' A)) := by
      funext s
      rw [Measure.map_apply (by fun_prop) hA]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hf hA)
  ext A hA
  rw [unifSet_scaledCone L hB hB0 hBt t hlam, Measure.map_apply hf hA,
    Measure.prod_apply (hf hA), Measure.bind_apply hA hmeas.aemeasurable]
  congr 1
  funext s
  rw [Measure.map_apply (by fun_prop) hA]
  rfl

/-- The map `x ↦ (S, Y)` with `S = ℓ(x - t)`, `Y = S⁻¹ (L (x - t)).2`, so that
`x - t = S L⁻¹(1, Y)` when `S ≠ 0`. -/
def coneSplit (t : V) (x : V) : ℝ × (Fin m → ℝ) :=
  ((L (x - t)).1, ((L (x - t)).1)⁻¹ • (L (x - t)).2)

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
lemma measurable_coneSplit (t : V) : Measurable (coneSplit L t) := by
  have h : Measurable fun x : V => L (x - t) :=
    L.continuous.measurable.comp (measurable_sub_const t)
  exact (measurable_fst.comp h).prodMk
    (((measurable_fst.comp h).inv).smul (measurable_snd.comp h))

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma coneSplit_apply (t : V) {s : ℝ} (hs : s ≠ 0) (b : Fin m → ℝ) :
    coneSplit L t (t + s • L.symm (1, b)) = (s, b) := by
  simp only [coneSplit, add_sub_cancel_left, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    Prod.smul_mk, smul_eq_mul, mul_one, inv_smul_smul₀ hs]

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma coneSplit_reconstruct (t x : V) (hx : (L (x - t)).1 ≠ 0) :
    x = t + (coneSplit L t x).1 • L.symm (1, (coneSplit L t x).2) := by
  simp only [coneSplit]
  rw [← smul_symm_one, smul_inv_smul₀ hx]
  have : ((L (x - t)).1, (L (x - t)).2) = L (x - t) := rfl
  rw [this, ContinuousLinearEquiv.symm_apply_apply]
  abel

/-- **Lemma 42 (slicing of a cone).** If `X ∼ U(t + lam K)`, then `S = ℓ(X - t)` and
`Y = S⁻¹ (L (X - t)).2` are independent, `S` has the density `k s^(k-1) lam^(-k)` on `[0, lam]`
and `Y ∼ U(B)`; since `X - t = S L⁻¹(1, Y)` almost surely (`coneSplit_reconstruct`), this says
that given `S`, `X - t` is uniform on `S F` (`sliceUnif`). -/
theorem unifSet_scaledCone_split (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (t : V) {lam : ℝ} (hlam : 0 < lam) :
    (unifSet (scaledTranslate t lam (coneSet L B))).map (coneSplit L t) =
      (coneRadial m lam).prod (unifSet B) := by
  have := coneRadial_isProb m hlam
  have := unifSet_isProb hB0 hBt
  rw [unifSet_scaledCone L hB hB0 hBt t hlam, Measure.map_map (measurable_coneSplit L t)
    (by fun_prop)]
  conv_rhs => rw [← Measure.map_id (μ := (coneRadial m lam).prod (unifSet B))]
  apply Measure.map_congr
  have h : ∀ᵐ p ∂(coneRadial m lam).prod (unifSet B), p.1 ≠ 0 := by
    have h0 := coneRadial_ae_ne_zero m lam
    have hm : coneRadial m lam = ((coneRadial m lam).prod (unifSet B)).map Prod.fst := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [hm] at h0
    exact ae_of_ae_map measurable_fst.aemeasurable h0
  filter_upwards [h] with p hp
  simp only [Function.comp_apply, id]
  exact coneSplit_apply L t hp p.2

/-- **Lemma 42**, the law of `S = ℓ(X - t)` for `X ∼ U(t + lam K)`. -/
theorem unifSet_scaledCone_map_ell (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (t : V) {lam : ℝ} (hlam : 0 < lam) :
    (unifSet (scaledTranslate t lam (coneSet L B))).map (fun x => (L (x - t)).1) =
      coneRadial m lam := by
  have := unifSet_isProb hB0 hBt
  have h := congrArg (Measure.map Prod.fst) (unifSet_scaledCone_split L hB hB0 hBt t hlam)
  rw [Measure.map_map measurable_fst (measurable_coneSplit L t), Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h

/-- The reconstruction `X - t = S L⁻¹(1, Y)` holds almost surely under `U(t + lam K)`. -/
theorem unifSet_scaledCone_ae_reconstruct (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (t : V) {lam : ℝ} (hlam : 0 < lam) :
    ∀ᵐ x ∂unifSet (scaledTranslate t lam (coneSet L B)),
      x = t + (coneSplit L t x).1 • L.symm (1, (coneSplit L t x).2) := by
  have h0 := coneRadial_ae_ne_zero m lam
  rw [← unifSet_scaledCone_map_ell L hB hB0 hBt t hlam] at h0
  have h1 := ae_of_ae_map (by fun_prop) h0
  filter_upwards [h1] with x hx
  exact coneSplit_reconstruct L t x hx

/-! ### Necessity (Theorem 43 (a)) -/

/-- The law `G_{k,lam}` of `T = lam - S`, `S ∼ coneRadial m lam`; `G_{k,0} = δ₀`. -/
def coneTLaw (m : ℕ) (lam : ℝ) : Measure ℝ :=
  if 0 < lam then (coneRadial m lam).map (fun s => lam - s) else Measure.dirac 0

lemma coneTLaw_nonneg (m : ℕ) {lam : ℝ} : ∀ᵐ x ∂coneTLaw m lam, 0 ≤ x := by
  unfold coneTLaw
  split_ifs with h
  · refine (ae_map_iff (measurable_const.sub measurable_id).aemeasurable measurableSet_Ici).2 ?_
    filter_upwards [coneRadial_ae_mem m lam] with s hs
    simpa using hs.2
  · exact ae_dirac_iff (measurableSet_le measurable_const measurable_id) |>.2 le_rfl

/-- The mean of `G_{k,lam}` is `lam / (k + 1)`. -/
lemma lintegral_coneTLaw (m : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫⁻ x, ENNReal.ofReal x ∂coneTLaw m lam = ENNReal.ofReal (lam / (m + 2)) := by
  unfold coneTLaw
  split_ifs with h
  · rw [lintegral_map ENNReal.measurable_ofReal (by fun_prop),
      lintegral_coneRadial h (by fun_prop) (fun s hs => by linarith [hs.2])]
    congr 1
    have hfun : (fun s : ℝ => (lam - s) * ((m + 1) * s ^ m / lam ^ (m + 1))) =
        fun s => ((m + 1) / lam ^ m) * s ^ m - ((m + 1) / lam ^ (m + 1)) * s ^ (m + 1) := by
      funext s
      field_simp
      ring
    rw [hfun, intervalIntegral.integral_sub (f := fun s => ((m + 1) / lam ^ m) * s ^ m)
      (g := fun s => ((m + 1) / lam ^ (m + 1)) * s ^ (m + 1))
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable _ _)
      ((continuous_const.mul (continuous_pow (m + 1))).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
      integral_pow]
    have hl : lam ≠ 0 := h.ne'
    rw [zero_pow (Nat.succ_ne_zero m), zero_pow (Nat.succ_ne_zero (m + 1))]
    field_simp
    push_cast
    ring
  · have : lam = 0 := le_antisymm (not_lt.1 h) hlam
    subst this
    simp

/-- `G_{k,lam}` charges every neighbourhood of its right end `lam`. -/
lemma coneTLaw_not_ae_le (m : ℕ) {lam c : ℝ} (hlam : 0 < lam) (hc : c < lam) :
    ¬ ∀ᵐ x ∂coneTLaw m lam, x ≤ c := by
  intro hae
  simp only [coneTLaw, hlam, ↓reduceIte] at hae
  have hae2 := (ae_map_iff (measurable_const.sub measurable_id).aemeasurable
    measurableSet_Iic).1 hae
  rw [ae_iff] at hae2
  set S := {s : ℝ | ¬ lam - s ≤ c}
  have hS : MeasurableSet S :=
    (measurableSet_le (measurable_const.sub measurable_id) measurable_const).compl
  set d := min (lam - c) lam
  have hd : 0 < d := lt_min (by linarith) hlam
  have hd1 : d ≤ lam - c := min_le_left _ _
  have hd2 : d ≤ lam := min_le_right _ _
  have hsub : Icc (d / 4) (d / 2) ⊆ S ∩ Icc 0 lam := fun s hs =>
    ⟨by simp only [S, mem_ofPred_eq, not_le]; linarith [hs.2], by linarith [hs.1], by
      linarith [hs.2]⟩
  set κ := ((m : ℝ) + 1) * (d / 4) ^ m / lam ^ (m + 1)
  have hκ : 0 < κ := by positivity
  have : 0 < coneRadial m lam S := by
    rw [coneRadial, withDensity_apply _ hS, Measure.restrict_restrict hS]
    calc (0 : ENNReal) < ENNReal.ofReal κ * volume (Icc (d / 4) (d / 2)) := by
          rw [Real.volume_Icc]
          exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hκ).ne'
            (ENNReal.ofReal_pos.2 (by linarith)).ne'
      _ = ∫⁻ _ in Icc (d / 4) (d / 2), ENNReal.ofReal κ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ s in Icc (d / 4) (d / 2), ENNReal.ofReal ((m + 1) * s ^ m / lam ^ (m + 1)) := by
          refine setLIntegral_mono (by fun_prop) fun s hs => ENNReal.ofReal_le_ofReal ?_
          have : (d / 4) ^ m ≤ s ^ m := pow_le_pow_left₀ (by positivity) hs.1 m
          simp only [κ]
          gcongr
      _ ≤ _ := lintegral_mono_set hsub
  exact this.ne' hae2

/-- `U(t + lam K)`, with the paper's convention `U({t}) = δ_t` for `lam = 0`
(`unifSet` of a null set is the zero measure). -/
def coneUnif (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (B : Set (Fin m → ℝ)) (t : V) (lam : ℝ) :
    Measure V :=
  if 0 < lam then unifSet (scaledTranslate t lam (coneSet L B)) else Measure.dirac t

/-- **Theorem 43 (a).** Let `K ⊆ V` (`dim V = k = m + 1`) be the cone over
`F = L⁻¹({1} × B)` with `B` of finite positive volume. If `U(t₁ + λ₁K), …, U(tₙ + λₙK)`
(`λᵢ ≥ 0`) are jointly mixable, then `(k + 1) λⱼ ≤ ∑ᵢ λᵢ` for every `j`, i.e.
`(k + 1) maxᵢ λᵢ ≤ ∑ᵢ λᵢ`. -/
theorem cone_jointlyMixable_le (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) {n : ℕ} (t : Fin n → V) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (h : JointlyMixable fun i => coneUnif L B (t i) (lam i)) (j : Fin n) :
    ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i := by
  obtain ⟨P, hP⟩ := h
  let φ : V →+ ℝ :=
    (-((ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).comp (L : V →L[ℝ] ℝ × (Fin m → ℝ)))
      ).toLinearMap.toAddMonoidHom
  have hφ : ∀ x, φ x = -(L x).1 := fun x => rfl
  have hφm : Measurable φ := by
    have : (φ : V → ℝ) = fun x => -(L x).1 := funext hφ
    rw [this]; fun_prop
  have hQ := hP.map_affine φ hφm (fun i => lam i + (L (t i)).1)
  have hG : ∀ i, (coneUnif L B (t i) (lam i)).map (fun x => (lam i + (L (t i)).1) + φ x) =
      coneTLaw m (lam i) := by
    intro i
    have hfun : (fun x => (lam i + (L (t i)).1) + φ x) =
        (fun s => lam i - s) ∘ (fun x => (L (x - t i)).1) := by
      funext x; simp only [hφ, Function.comp_apply, map_sub, Prod.fst_sub]; ring
    unfold coneUnif coneTLaw
    split_ifs with hi
    · rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
        unifSet_scaledCone_map_ell L hB hB0 hBt (t i) hi]
    · rw [Measure.map_dirac' (f := fun x => lam i + (L (t i)).1 + φ x)
        (measurable_const.add hφm), hφ]
      have : lam i = 0 := le_antisymm (not_lt.1 hi) (hlam i)
      rw [this]; simp
  simp only [hG] at hQ
  have hsum0 : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ => hlam i
  by_cases hj : 0 < lam j
  · have hae := hQ.ae_le_sum_lintegral (fun i => coneTLaw_nonneg m) j
    simp only [fun i => lintegral_coneTLaw m (hlam i)] at hae
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by have := hlam i; positivity] at hae
    have hae' : ∀ᵐ x ∂coneTLaw m (lam j), x ≤ ∑ i, lam i / (m + 2) := by
      filter_upwards [hae, coneTLaw_nonneg m] with x hx hx0
      exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => by
        have := hlam i; positivity)).1 hx
    by_contra hlt
    push Not at hlt
    apply coneTLaw_not_ae_le m hj _ hae'
    rw [← Finset.sum_div, div_lt_iff₀ (by positivity)]
    linarith
  · have : lam j = 0 := le_antisymm (not_lt.1 hj) (hlam j)
    rw [this, mul_zero]
    exact hsum0

/-- **Theorem 43 (a), complete mixes.** If `U(t + K)` is `n`-completely mixable (`n ≥ 1`), then
`n ≥ k + 1 = m + 2`. -/
theorem cone_completelyMixable_le (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (t : V) {n : ℕ} (hn : 0 < n)
    (h : CompletelyMixable n (unifSet (scaledTranslate t 1 (coneSet L B)))) : m + 2 ≤ n := by
  have h' : JointlyMixable fun _ : Fin n => coneUnif L B t 1 := by
    simp only [coneUnif, one_pos, ↓reduceIte]; exact h
  have := cone_jointlyMixable_le L hB hB0 hBt (fun _ => t) (fun _ => 1) (fun _ => zero_le_one)
    h' ⟨0, hn⟩
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact_mod_cast this

end ConeV

/-! ### Simplices and pyramids -/

section Examples

variable {m : ℕ}

/-- The standard simplex `{b ∈ ℝ^m : b ≥ 0, ∑ bᵢ ≤ 1}`. -/
def stdSimplexSet (m : ℕ) : Set (Fin m → ℝ) := {b | (∀ i, 0 ≤ b i) ∧ ∑ i, b i ≤ 1}

lemma measurableSet_stdSimplexSet (m : ℕ) : MeasurableSet (stdSimplexSet m) := by
  have : stdSimplexSet m = (⋂ i, {b : Fin m → ℝ | 0 ≤ b i}) ∩ {b | ∑ i, b i ≤ 1} := by
    ext b; simp [stdSimplexSet]
  rw [this]
  exact (MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const)

lemma volume_stdSimplexSet_ne_top (m : ℕ) : volume (stdSimplexSet m) ≠ ⊤ := by
  have hsub : stdSimplexSet m ⊆ Icc (0 : Fin m → ℝ) 1 := fun b hb => ⟨fun i => hb.1 i,
    fun i => le_trans (Finset.single_le_sum (fun j _ => hb.1 j) (Finset.mem_univ i)) hb.2⟩
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [Real.volume_Icc_pi]
  simp

lemma volume_stdSimplexSet_ne_zero (m : ℕ) : volume (stdSimplexSet m) ≠ 0 := by
  have hsub : Icc (0 : Fin m → ℝ) (fun _ => 1 / (m + 1)) ⊆ stdSimplexSet m := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    calc ∑ i, b i ≤ ∑ _i : Fin m, (1 / ((m : ℝ) + 1)) := Finset.sum_le_sum fun i _ => hb.2 i
      _ = m / (m + 1) := by simp [div_eq_mul_inv]
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  refine fun h => ?_
  have h0 := measure_mono_null hsub h
  rw [Real.volume_Icc_pi, Finset.prod_eq_zero_iff] at h0
  obtain ⟨i, _, hi⟩ := h0
  simp only [Pi.zero_apply, sub_zero, ENNReal.ofReal_eq_zero] at hi
  have : (0 : ℝ) < 1 / (m + 1) := by positivity
  linarith

/-- The cone over `{1} × stdSimplexSet m` is the `(m+1)`-simplex
`{(s, z) : z ≥ 0, ∑ zᵢ ≤ s ≤ 1}` with vertices `0`, `(1, 0)` and `(1, eᵢ)`. -/
lemma coneSet_stdSimplex :
    coneSet (ContinuousLinearEquiv.refl ℝ (ℝ × (Fin m → ℝ))) (stdSimplexSet m) =
      {p | (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ p.1 ∧ p.1 ≤ 1} := by
  ext ⟨s, z⟩
  simp only [coneSet, coneBase, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl', id, mem_ofPred_eq, stdSimplexSet]
  constructor
  · rintro ⟨r, hr, _, ⟨b, ⟨hb0, hb1⟩, rfl⟩, h⟩
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun i => mul_nonneg hr.1 (hb0 i), ?_, hr.2⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    nlinarith [hr.1]
  · rintro ⟨hz0, hzs, hs1⟩
    have hs0 : 0 ≤ s := le_trans (Finset.sum_nonneg fun i _ => hz0 i) hzs
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h
      have hz : z = 0 := by
        funext i
        exact le_antisymm (le_trans (Finset.single_le_sum (fun j _ => hz0 j)
          (Finset.mem_univ i)) hzs) (hz0 i)
      subst hz
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, _, ⟨0, ⟨fun _ => le_rfl, by simp⟩, rfl⟩, by simp⟩
    · refine ⟨s, ⟨hs0, hs1⟩, _, ⟨s⁻¹ • z, ⟨fun i => ?_, ?_⟩, rfl⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hs0) (hz0 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ h]; linarith
      · simp [Prod.smul_mk, smul_inv_smul₀ h.ne']

/-- **Simplices.** The uniform distribution on the `d`-simplex (`d = m + 1`)
`{(s, z) : z ≥ 0, ∑ zᵢ ≤ s ≤ 1}`, or a translate of it, is `n`-completely mixable only if
`n ≥ d + 1`. -/
theorem simplex_completelyMixable_le (t : ℝ × (Fin m → ℝ)) {n : ℕ} (hn : 0 < n)
    (h : CompletelyMixable n (unifSet (scaledTranslate t 1
      {p : ℝ × (Fin m → ℝ) | (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ p.1 ∧ p.1 ≤ 1}))) :
    m + 2 ≤ n := by
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [← coneSet_stdSimplex] at h
  exact cone_completelyMixable_le _ (measurableSet_stdSimplexSet m)
    (volume_stdSimplexSet_ne_zero m) (volume_stdSimplexSet_ne_top m) t hn h

/-- The cone over `{1} × [0,1]^m` is the pyramid `{(s, z) : 0 ≤ zᵢ ≤ s ≤ 1}` over the cube. -/
lemma coneSet_cube :
    coneSet (ContinuousLinearEquiv.refl ℝ (ℝ × (Fin m → ℝ))) (Icc 0 1) =
      {p | (∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ p.1) ∧ 0 ≤ p.1 ∧ p.1 ≤ 1} := by
  ext ⟨s, z⟩
  simp only [coneSet, coneBase, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl', id, mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr, _, ⟨b, ⟨hb0, hb1⟩, rfl⟩, h⟩
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun i => ⟨mul_nonneg hr.1 (hb0 i), ?_⟩, hr.1, hr.2⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    have hbi : b i ≤ 1 := hb1 i
    nlinarith [hr.1]
  · rintro ⟨hz, hs0, hs1⟩
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h
      have hz' : z = 0 := funext fun i => le_antisymm (hz i).2 (hz i).1
      subst hz'
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, _, ⟨0, ⟨le_rfl, fun _ => zero_le_one⟩, rfl⟩, by simp⟩
    · refine ⟨s, ⟨hs0, hs1⟩, _, ⟨s⁻¹ • z, ⟨fun i => ?_, fun i => ?_⟩, rfl⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact mul_nonneg (inv_nonneg.2 hs0) (hz i).1
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
        rw [inv_mul_le_iff₀ h]; linarith [(hz i).2]
      · simp [Prod.smul_mk, smul_inv_smul₀ h.ne']

/-- **Pyramids.** The uniform distribution on the pyramid `{(s, z) : 0 ≤ zᵢ ≤ s ≤ 1}` over a
cube, of dimension `d = m + 1`, or a translate of it, is `n`-completely mixable only if
`n ≥ d + 1`. -/
theorem pyramid_completelyMixable_le (t : ℝ × (Fin m → ℝ)) {n : ℕ} (hn : 0 < n)
    (h : CompletelyMixable n (unifSet (scaledTranslate t 1
      {p : ℝ × (Fin m → ℝ) | (∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ p.1) ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}))) :
    m + 2 ≤ n := by
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [← coneSet_cube] at h
  have hv : volume (Icc (0 : Fin m → ℝ) 1) = 1 := by rw [Real.volume_Icc_pi]; simp
  exact cone_completelyMixable_le _ measurableSet_Icc (by rw [hv]; exact one_ne_zero)
    (by rw [hv]; exact ENNReal.one_ne_top) t hn h

end Examples

end Mixes
