import Mixes.Defs

/-!
# Proposition 71(a): complete mixability passes to Hausdorff limits

Proposition 71(a) (`o:prop:reduce`): if convex bodies `K j` converge to a convex body `K` in the
Hausdorff metric and every `U(K j)` is `n`-completely mixable, so is `U(K)`; hence Open
Problem 5 holds in `ℝ^d` iff it holds for all polytopes in `ℝ^d`.

* `Mixes.Reduce.completelyMixable_of_tendsto`: weak limits of `n`-completely mixable probability
  measures on a common compact set are `n`-completely mixable (Prokhorov compactness and the
  portmanteau bound for closed sets).
* `Mixes.Reduce.tendsto_unifP`: uniform distributions converge weakly when the sets converge
  almost everywhere inside a common set of finite volume.
* `Mixes.Reduce.reduce_a`: Proposition 71(a), first sentence.
* `Mixes.Reduce.exists_polytopes_tendsto`, `Mixes.Reduce.op5_iff_polytopes`: Proposition 71(a),
  second sentence.

Convex bodies are compact convex sets with nonempty interior in `Fin d → ℝ` (sup norm; the
Hausdorff distance is `Metric.hausdorffDist` for this norm, equivalent to the Euclidean one).
-/

open MeasureTheory Filter Topology Set Metric

noncomputable section

namespace Mixes

namespace Reduce

variable {d n : ℕ}

local notation "E" => Fin d → ℝ

/-- Weak limits of `n`-completely mixable probability measures that live on a common compact set
are `n`-completely mixable. -/
theorem completelyMixable_of_tendsto {μs : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E}
    (hlim : Tendsto μs atTop (𝓝 μ)) {C : Set E} (hC : IsCompact C)
    (hsupp : ∀ j, (μs j : Measure E) Cᶜ = 0)
    (hmix : ∀ j, CompletelyMixable n (μs j : Measure E)) :
    CompletelyMixable n (μ : Measure E) := by
  choose P hP using hmix
  have hPp : ∀ j, IsProbabilityMeasure (P j) := fun j => (hP j).1
  choose s hs using fun j => (hP j).2.1
  have hmarg : ∀ j i, (P j).map (fun x => x i) = μs j := fun j => (hP j).2.2
  let Pp : ℕ → ProbabilityMeasure (Fin n → E) := fun j => ⟨P j, hPp j⟩
  set D : Set (Fin n → E) := Set.pi univ (fun _ => C) with hD
  have hDc : IsCompact D := isCompact_univ_pi fun _ => hC
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hPD : ∀ j, P j Dᶜ = 0 := by
    intro j
    have : Dᶜ ⊆ ⋃ i, (fun x : Fin n → E => x i) ⁻¹' Cᶜ := by
      intro x hx
      simp only [hD, mem_compl_iff, Set.mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact mem_iUnion.2 ⟨i, hi⟩
    refine measure_mono_null this (measure_iUnion_null fun i => ?_)
    rw [← Measure.map_apply (measurable_pi_apply i) hCm.compl, hmarg j i]
    exact hsupp j
  -- compactness of the set of probability measures on `D`
  have hS :
      IsCompact {Q : ProbabilityMeasure (Fin n → E) | ∀ _k : ℕ, Q Dᶜ ≤ (0 : NNReal)} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le (u := fun _ => 0)
      tendsto_const_nhds (fun _ => hDc) (Or.inr monotone_const)
  have hmem : ∀ j,
      Pp j ∈ {Q : ProbabilityMeasure (Fin n → E) | ∀ _k : ℕ, Q Dᶜ ≤ (0 : NNReal)} := by
    intro j _
    have : (Pp j : Measure (Fin n → E)) Dᶜ = 0 := hPD j
    exact ((ProbabilityMeasure.null_iff_toMeasure_null _ _).2 this).le
  obtain ⟨Q, -, φ, hφ, hQ⟩ := hS.tendsto_subseq hmem
  -- the constant sums lie in a compact set
  set T : Set E := (fun x : Fin n → E => ∑ i, x i) '' D
  have hT : IsCompact T := hDc.image (by fun_prop)
  have hsT : ∀ j, s j ∈ T := by
    intro j
    have h1 : ∀ᵐ x ∂(P j), x ∈ D := by
      rw [ae_iff]; simpa [compl_def] using hPD j
    obtain ⟨x, hxD, hx⟩ := (h1.and (hs j)).exists
    exact ⟨x, hxD, hx⟩
  obtain ⟨s0, -, ψ, hψ, hs0⟩ := hT.tendsto_subseq (fun k => hsT (φ k))
  have hQψ : Tendsto (fun k => Pp (φ (ψ k))) atTop (𝓝 Q) := hQ.comp hψ.tendsto_atTop
  have hμψ : Tendsto (fun k => μs (φ (ψ k))) atTop (𝓝 μ) :=
    hlim.comp (hφ.comp hψ).tendsto_atTop
  refine ⟨Q, Q.prop, ⟨s0, ?_⟩, fun i => ?_⟩
  · -- the sum condition passes to the limit
    have hF : ∀ m : ℕ, ∀ᵐ x ∂(Q : Measure (Fin n → E)),
        x ∈ {x : Fin n → E | dist (∑ i, x i) s0 ≤ 1 / ((m : ℝ) + 1)} := by
      intro m
      set F := {x : Fin n → E | dist (∑ i, x i) s0 ≤ 1 / ((m : ℝ) + 1)} with hFdef
      have hFc : IsClosed F := isClosed_le (by fun_prop) continuous_const
      have hev : ∀ᶠ k in atTop, (Pp (φ (ψ k)) : Measure (Fin n → E)) F = 1 := by
        have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        filter_upwards [(Metric.tendsto_nhds.1 hs0) _ hpos] with k hk
        show P (φ (ψ k)) F = 1
        rw [← prob_compl_eq_zero_iff hFc.measurableSet]
        refine measure_mono_null (fun x hx => ?_) (ae_iff.1 (hs (φ (ψ k))))
        intro hxs
        apply hx
        show dist (∑ i, x i) s0 ≤ _
        rw [hxs]; exact hk.le
      have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hQψ hFc
      rw [limsup_congr hev, limsup_const] at hle
      have : (Q : Measure (Fin n → E)) F = 1 := le_antisymm prob_le_one hle
      rw [ae_iff]
      exact measure_mono_null (fun x hx => hx) ((prob_compl_eq_zero_iff hFc.measurableSet).2 this)
    filter_upwards [ae_all_iff.2 hF] with x hx
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    exact (hx m).trans hm.le
  · have h1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hQψ
      (continuous_apply i)
    have h2 : (fun k => (Pp (φ (ψ k))).map (fun x => x i)) = fun k => μs (φ (ψ k)) := by
      funext k; apply Subtype.ext; exact hmarg _ i
    rw [h2] at h1
    have := tendsto_nhds_unique h1 hμψ
    exact congrArg Subtype.val this.symm |>.symm

/-! ## Convergence of uniform distributions -/

lemma unifSet_isProb' {K : Set E} (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤) :
    IsProbabilityMeasure (unifSet K) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

/-- The uniform distribution on a set of finite positive volume, as a probability measure. -/
def unifP (K : Set E) (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤) : ProbabilityMeasure E :=
  ⟨unifSet K, unifSet_isProb' h0 htop⟩

lemma integral_unifSet (K : Set E) (f : E → ℝ) :
    ∫ x, f x ∂(unifSet K) = (volume.real K)⁻¹ * ∫ x in K, f x := by
  rw [unifSet, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, measureReal_def]

/-- If the sets `K j` eventually lie in a set `B` of finite volume and, for almost every `x`,
`x ∈ K j ↔ x ∈ K0` eventually, then the uniform distributions on `K j` converge weakly to the
uniform distribution on `K0`. -/
theorem tendsto_unifP {K : ℕ → Set E} {K0 : Set E} (hKm : ∀ j, MeasurableSet (K j))
    (hK0m : MeasurableSet K0) (h0 : ∀ j, volume (K j) ≠ 0) (htop : ∀ j, volume (K j) ≠ ⊤)
    (h00 : volume K0 ≠ 0) (h0top : volume K0 ≠ ⊤) {B : Set E} (hBm : MeasurableSet B)
    (hB : volume B ≠ ⊤) (hsub : ∀ᶠ j in atTop, K j ⊆ B)
    (hmem : ∀ᵐ x, ∀ᶠ j in atTop, (x ∈ K j ↔ x ∈ K0)) :
    Tendsto (fun j => unifP (K j) (h0 j) (htop j)) atTop (𝓝 (unifP K0 h00 h0top)) := by
  have hI : ∀ f : E → ℝ, Continuous f → ∀ c, (∀ x, ‖f x‖ ≤ c) →
      Tendsto (fun j => ∫ x in K j, f x) atTop (𝓝 (∫ x in K0, f x)) := by
    intro f hf c hc
    simp_rw [← integral_indicator (hKm _), ← integral_indicator hK0m]
    refine tendsto_integral_filter_of_dominated_convergence (B.indicator fun _ => c)
      (Eventually.of_forall fun j => hf.aestronglyMeasurable.indicator (hKm j)) ?_ ?_ ?_
    · filter_upwards [hsub] with j hj
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ K j
      · rw [indicator_of_mem hx, indicator_of_mem (hj hx)]; exact hc x
      · rw [indicator_of_notMem hx, norm_zero]
        exact indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hc x)) x
    · exact (integrable_indicator_iff hBm).2 (integrableOn_const hB)
    · filter_upwards [hmem] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hx] with j hj
      by_cases h : x ∈ K0
      · rw [indicator_of_mem h, indicator_of_mem (hj.2 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt hj.1 h)]
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [unifP, ProbabilityMeasure.coe_mk, integral_unifSet]
  have hv := hI (fun _ => (1 : ℝ)) continuous_const 1 (fun _ => by simp)
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hv
  have hne : volume.real K0 ≠ 0 := by
    rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h00, h0top⟩
  exact (hv.inv₀ hne).mul (hI f f.continuous ‖f‖ f.norm_coe_le_norm)

/-! ## Hausdorff convergence of convex bodies -/

/-- If a closed convex set `L` is Hausdorff-close to `K` (closer than `δ / 2`) and `K` contains
the ball of radius `δ` about `x`, then `x ∈ L`. -/
lemma mem_of_ball_subset {K L : Set E} (hL : Convex ℝ L) (hLc : IsClosed L)
    (hfin : hausdorffEDist K L ≠ ⊤) {x : E} {δ : ℝ} (hball : ball x δ ⊆ K)
    (hd : hausdorffDist K L < δ / 2) : x ∈ L := by
  have hδ : 0 < δ := by linarith [hausdorffDist_nonneg (s := K) (t := L)]
  by_contra hx
  obtain ⟨f, u, hfL, hfx⟩ := geometric_hahn_banach_closed_point hL hLc hx
  obtain ⟨z0, hz0, -⟩ := exists_dist_lt_of_hausdorffDist_lt (hball (mem_ball_self hδ)) hd hfin
  have hf0 : 0 < ‖f‖ := by
    rcases (norm_nonneg f).lt_or_eq with h | h
    · exact h
    · have : f = 0 := norm_eq_zero.1 h.symm
      have h1 := hfL z0 hz0
      simp [this] at h1 hfx
      linarith
  obtain ⟨v, hv1, hv2⟩ := f.exists_lt_apply_of_lt_opNorm (r := 2 / 3 * ‖f‖) (by linarith)
  obtain ⟨w, hw1, hw2⟩ : ∃ w : E, ‖w‖ < 1 ∧ 2 / 3 * ‖f‖ < f w := by
    rcases le_or_gt 0 (f v) with h | h
    · exact ⟨v, hv1, by rwa [Real.norm_of_nonneg h] at hv2⟩
    · refine ⟨-v, by rwa [norm_neg], ?_⟩
      rw [Real.norm_eq_abs, abs_of_neg h] at hv2
      simpa using hv2
  set y := x + δ • w
  have hy : y ∈ K := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
    nlinarith
  obtain ⟨z, hz, hyz⟩ := exists_dist_lt_of_hausdorffDist_lt hy hd hfin
  have h1 : f (y - z) ≤ ‖f‖ * (δ / 2) := by
    calc f (y - z) ≤ ‖f (y - z)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖y - z‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (δ / 2) := by
        rw [← dist_eq_norm]; exact mul_le_mul_of_nonneg_left hyz.le hf0.le
  have h2 : f y = f x + δ * f w := by simp [y, map_add, map_smul]
  have h3 : f z = f y - f (y - z) := by simp [map_sub]
  have := hfL z hz
  nlinarith

variable {K : ℕ → Set (Fin d → ℝ)} {K0 : Set (Fin d → ℝ)}

lemma hausdorffEDist_ne_top' (hK : ∀ j, IsCompact (K j)) (hKn : ∀ j, (K j).Nonempty)
    (hK0 : IsCompact K0) (hK0n : K0.Nonempty) (j : ℕ) : hausdorffEDist (K j) K0 ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded (hKn j) hK0n (hK j).isBounded hK0.isBounded

/-- Under Hausdorff convergence, the `K j` eventually lie in the closed `1`-neighbourhood of
`K0`. -/
lemma eventually_subset_cthickening (hK : ∀ j, IsCompact (K j)) (hKn : ∀ j, (K j).Nonempty)
    (hK0 : IsCompact K0) (hK0n : K0.Nonempty)
    (hlim : Tendsto (fun j => hausdorffDist (K j) K0) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, K j ⊆ cthickening 1 K0 := by
  filter_upwards [(tendsto_order.1 hlim).2 1 one_pos] with j hj x hx
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hj
    (hausdorffEDist_ne_top' hK hKn hK0 hK0n j)
  exact mem_cthickening_of_dist_le x y 1 K0 hy hxy.le

/-- Under Hausdorff convergence of convex compact sets to a convex compact set `K0`, almost every
point eventually lies in `K j` exactly when it lies in `K0` (the frontier of `K0` is null). -/
lemma ae_eventually_mem_iff (hK : ∀ j, IsCompact (K j)) (hKc : ∀ j, Convex ℝ (K j))
    (hKn : ∀ j, (K j).Nonempty) (hK0 : IsCompact K0) (hK0c : Convex ℝ K0)
    (hK0n : K0.Nonempty) (hlim : Tendsto (fun j => hausdorffDist (K j) K0) atTop (𝓝 0)) :
    ∀ᵐ x, ∀ᶠ j in atTop, (x ∈ K j ↔ x ∈ K0) := by
  have hfr : volume (frontier K0) = 0 := hK0c.addHaar_frontier volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfr] with x hx
  rw [hK0.isClosed.frontier_eq, Set.mem_sdiff, not_and_or, not_not] at hx
  rcases hx with hx | hx
  · have hpos : 0 < infDist x K0 := (hK0.isClosed.notMem_iff_infDist_pos hK0n).1 hx
    filter_upwards [(tendsto_order.1 hlim).2 _ hpos] with j hj
    refine ⟨fun hxj => absurd (infDist_le_hausdorffDist_of_mem hxj
      (hausdorffEDist_ne_top' hK hKn hK0 hK0n j)) (not_le.2 hj), fun h => absurd h hx⟩
  · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    filter_upwards [(tendsto_order.1 hlim).2 (δ / 2) (by positivity)] with j hj
    refine ⟨fun _ => interior_subset hx, fun _ => ?_⟩
    refine mem_of_ball_subset (hKc j) (hK j).isClosed ?_ (hball.trans interior_subset) ?_
    · rw [hausdorffEDist_comm]; exact hausdorffEDist_ne_top' hK hKn hK0 hK0n j
    · rwa [hausdorffDist_comm]

/-- **Proposition 71(a)** (`o:prop:reduce`): if convex bodies `K j` converge to a convex body `K0`
in the Hausdorff metric and every `U(K j)` is `n`-completely mixable, so is `U(K0)`. Convex
bodies are compact convex sets with nonempty interior. -/
theorem reduce_a (hK : ∀ j, IsCompact (K j)) (hKc : ∀ j, Convex ℝ (K j))
    (hKi : ∀ j, (interior (K j)).Nonempty) (hK0 : IsCompact K0) (hK0c : Convex ℝ K0)
    (hK0i : (interior K0).Nonempty)
    (hlim : Tendsto (fun j => hausdorffDist (K j) K0) atTop (𝓝 0))
    (hmix : ∀ j, CompletelyMixable n (unifSet (K j))) :
    CompletelyMixable n (unifSet K0) := by
  have hKn : ∀ j, (K j).Nonempty := fun j => (hKi j).mono interior_subset
  have hK0n : K0.Nonempty := hK0i.mono interior_subset
  have h0 : ∀ j, volume (K j) ≠ 0 := fun j =>
    (Measure.measure_pos_of_nonempty_interior _ (hKi j)).ne'
  have htop : ∀ j, volume (K j) ≠ ⊤ := fun j => (hK j).measure_lt_top.ne
  have h00 : volume K0 ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ hK0i).ne'
  have h0top : volume K0 ≠ ⊤ := hK0.measure_lt_top.ne
  set C := cthickening 1 K0
  have hC : IsCompact C := hK0.cthickening
  have hsub := eventually_subset_cthickening hK hKn hK0 hK0n hlim
  have hT := tendsto_unifP (fun j => (hK j).isClosed.measurableSet) hK0.isClosed.measurableSet
    h0 htop h00 h0top hC.isClosed.measurableSet hC.measure_lt_top.ne hsub
    (ae_eventually_mem_iff hK hKc hKn hK0 hK0c hK0n hlim)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsub
  refine completelyMixable_of_tendsto (μs := fun j => unifP (K (j + N)) (h0 _) (htop _))
    (hT.comp (tendsto_add_atTop_nat N)) hC (fun j => ?_) (fun j => hmix (j + N))
  show unifSet (K (j + N)) Cᶜ = 0
  rw [unifSet, smul_apply, Measure.restrict_apply hC.isClosed.measurableSet.compl,
    smul_eq_mul]
  have : Cᶜ ∩ K (j + N) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx => hx.1 (hN _ (by omega) hx.2)
  rw [this, measure_empty, mul_zero]
/-! ## Polytopes suffice -/

/-- A polytope: the convex hull of a finite set. -/
def IsPolytope (K : Set (Fin d → ℝ)) : Prop :=
  ∃ s : Finset (Fin d → ℝ), K = convexHull ℝ ↑s

/-- Open Problem 5 in `ℝ^d` for the convex bodies with property `Q`: the uniform distribution on
every convex body `K` with `Q K` is `n`-completely mixable for every `n ≥ d + 1`. -/
def OP5For (d : ℕ) (Q : Set (Fin d → ℝ) → Prop) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty → Q K →
    ∀ n, d + 1 ≤ n → CompletelyMixable n (unifSet K)

/-- Every convex body is a Hausdorff limit of polytopes with nonempty interior. -/
theorem exists_polytopes_tendsto {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0)
    (hK0c : Convex ℝ K0) (hK0i : (interior K0).Nonempty) :
    ∃ P : ℕ → Set (Fin d → ℝ), (∀ j, IsPolytope (P j)) ∧
      (∀ j, (interior (P j)).Nonempty) ∧
      Tendsto (fun j => hausdorffDist (P j) K0) atTop (𝓝 0) := by
  have hK0n : K0.Nonempty := hK0i.mono interior_subset
  have hnet :
      ∀ j : ℕ, ∃ t ⊆ K0, t.Finite ∧ K0 ⊆ ⋃ x ∈ t, ball x (1 / ((j : ℝ) + 1)) :=
    fun j => hK0.finite_cover_balls (by positivity)
  choose t ht htf hcov using hnet
  set P : ℕ → Set (Fin d → ℝ) := fun j => convexHull ℝ (t j)
  have hPpoly : ∀ j, IsPolytope (P j) := fun j => ⟨(htf j).toFinset, by simp [P]⟩
  have hPc : ∀ j, IsCompact (P j) := fun j => (htf j).isCompact_convexHull (𝕜 := ℝ)
  have hPsub : ∀ j, P j ⊆ K0 := fun j => (hK0c.convexHull_subset_iff).2 (ht j)
  have hPd : ∀ j, hausdorffDist (P j) K0 ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    refine hausdorffDist_le_of_mem_dist (by positivity)
      (fun x hx => ⟨x, hPsub j hx, by simp; positivity⟩) (fun x hx => ?_)
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov j hx)
    exact ⟨y, subset_convexHull ℝ _ hy, (mem_ball.1 hxy).le⟩
  have hlim : Tendsto (fun j => hausdorffDist (P j) K0) atTop (𝓝 0) :=
    squeeze_zero (fun _ => hausdorffDist_nonneg) hPd tendsto_one_div_add_atTop_nhds_zero_nat
  have hPn : ∀ j, (P j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hK0n
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 (hcov j hx)
    exact ⟨y, subset_convexHull ℝ _ hy⟩
  -- eventually the polytopes contain a fixed ball
  obtain ⟨x, hx⟩ := hK0i
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 (δ / 4) (by positivity))
  have hint : ∀ j, N ≤ j → (interior (P j)).Nonempty := by
    intro j hj
    refine ⟨x, mem_interior.2 ⟨ball x (δ / 2), fun y hy => ?_, isOpen_ball,
      mem_ball_self (by positivity)⟩⟩
    refine mem_of_ball_subset (convex_convexHull ℝ _) (hPc j).isClosed (K := K0) ?_ ?_
      (δ := δ / 2) ?_
    · exact hausdorffEDist_ne_top_of_nonempty_of_bounded hK0n (hPn j) hK0.isBounded
        (hPc j).isBounded
    · intro z hz
      apply interior_subset
      apply hball
      rw [mem_ball] at hz hy ⊢
      linarith [dist_triangle z y x]
    · rw [hausdorffDist_comm]; linarith [hN j hj]
  refine ⟨fun j => P (j + N), fun j => hPpoly _, fun j => hint _ (by omega),
    hlim.comp (tendsto_add_atTop_nat N)⟩

/-- **Proposition 71(a)**, second sentence (`o:prop:reduce`): Open Problem 5 has an affirmative
answer in `ℝ^d` if and only if it has one for all polytopes in `ℝ^d`. -/
theorem op5_iff_polytopes : OP5For d IsPolytope ↔ OP5For d (fun _ => True) := by
  constructor
  · intro h K hK hKc hKi _ n hn
    obtain ⟨P, hPp, hPi, hlim⟩ := exists_polytopes_tendsto hK hKc hKi
    have hPc : ∀ j, IsCompact (P j) := fun j => by
      obtain ⟨s, hs⟩ := hPp j; rw [hs]; exact s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
    have hPcv : ∀ j, Convex ℝ (P j) := fun j => by
      obtain ⟨s, hs⟩ := hPp j; rw [hs]; exact convex_convexHull ℝ _
    exact reduce_a hPc hPcv hPi hK hKc hKi hlim
      (fun j => h (P j) (hPc j) (hPcv j) (hPi j) (hPp j) n hn)
  · intro h K hK hKc hKi _ n hn
    exact h K hK hKc hKi trivial n hn

end Reduce

end Mixes
