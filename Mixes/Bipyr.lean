import Mixes.ScaledC
import Mixes.SymmCor
import Mixes.Ball
import Mixes.ConeMix

/-!
# Theorem 70 (`o:thm:bipyr`): bipyramids over bodies with the scaling property

Let `F ⊆ V` be compact with nonempty interior, centroid `0` and the scaling property with
constant `2`, `k - 1 = dim V`, and let `r : [-1, 1] → [0, ∞)` be even, concave and continuous,
positive on `(-1, 1)`. The body is `K = {(z, y) : |z| ≤ 1, y ∈ r(z) F}` (`ScaledC.bodyK`, with
the level written first).

* `thm70_three`: the explicit `3`-complete mix of the paper (levels of Lemma 69, sections mixed
  by the scaling property of `F`, assembled by Theorem 62), under condition (`o:eq:starr`).
* `thm70`: under (`o:eq:starr`), `U(K)` is `n`-completely mixable for every `n ≥ 2`.
* `starr_of_affine`, `thm70_affine`, `thm70_bipyramid`: (`o:eq:starr`) holds when `k ≥ 3` and
  `r` is affine on `[1/2, 1]`, in particular for the bipyramids `r(z) = 1 - |z|`.
* Instances: `thm70_image`, `bipyr_image` (linear images of `F`), `bipyr_ellipsoid` (ellipsoids, by
  Theorem 51), `bipyr_parallelotope` (centred parallelotopes, by Lemma 1 / Corollary 45 for the
  cube), and `octahedron` (`n`-complete mixability of the regular octahedron for every `n ≥ 2`).
* Transfer: `unifSet_map_equiv`, `completelyMixable_map_equiv`, `completelyMixable_swap` (level
  written last, as in `SymmCor`), `integral_unifSet_eq_zero` (symmetric sets are centred).
* Corollary 99(b) without the hypothesis `hL3`: `dcone_completelyMixable` (the double cone over
  a ball, `m ≥ 2`), `cor99b`, `cor99b_four`, `cor99b_five`.
-/

open MeasureTheory Set Metric Module ProbabilityTheory
open scoped ENNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace Mixes.Bipyr

open ScaledC

/-! ## Theorem 70 -/

section Thm70

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- Condition (`o:eq:starr`) of Theorem 70, `r(1/2)^{k-1} ≥ 2 ∫_{1/2}^1 r(a)^{k-1}/(1-a) da`,
together with the finiteness of the integral (in the paper implicit in the inequality). It is
`Scaled.CondP r (1/2) k`. -/
def Starr (r : ℝ → ℝ) (k : ℕ) : Prop :=
  IntervalIntegrable (fun a => r a ^ (k - 1) / (1 - a)) volume (1 / 2) 1 ∧
    2 * ∫ a in (1 / 2 : ℝ)..1, r a ^ (k - 1) / (1 - a) ≤ r (1 / 2) ^ (k - 1)

lemma starr_iff (r : ℝ → ℝ) (k : ℕ) : Starr r k ↔ Scaled.CondP r (1 / 2) k := by
  have e : (fun a => r a ^ (k - 1) / (2 * (1 / 2 : ℝ) - a)) = fun a => r a ^ (k - 1) / (1 - a) := by
    funext a; norm_num
  simp only [Starr, Scaled.CondP, e]

/-- `(F_{1/2})` holds for every even concave profile with `r(1) ≥ 0`. -/
lemma condF_half_of {r : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc (-1) 1) r)
    (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z) : Scaled.CondF r (1 / 2) :=
  Scaled.condF_half (hconc.subset (Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc 0 1))
    (hr0 1 ⟨by norm_num, le_rfl⟩)

/-- **Theorem 70** (`o:thm:bipyr`), the complete mix for `n = 3`. Let `k - 1 = dim V ≥ 1`, `F`
compact with nonempty interior and centroid `0`, and `Φ` a joint mix of `U(λ₁F), U(λ₂F), U(λ₃F)`
whenever `2 max λ ≤ ∑ λ` (the scaling property of `F` with constant `2`). Let `r` be even,
concave, continuous and `≥ 0` on `[-1, 1]`, positive on `(-1, 1)`, and suppose (`o:eq:starr`).
Then `X_i = (Z_i, W_i)`, where `(Z₁, Z₂, Z₃)` is the complete mix of the levels of Lemma 69
(`Bipyramid.levelMix`) for `ν = r^{k-1}/∫_0^1 r^{k-1}` and, given the levels, `W` is the joint
mix of the `U(r(Z_i) F)` given by `Φ`, is a `3`-complete mix of `U(K)`. -/
theorem thm70_three {r : ℝ → ℝ} {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    (hcont : ContinuousOn r (Icc (-1) 1)) (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z)
    (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
    (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) (hstar : Starr r (finrank ℝ V + 1))
    {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {Φ : (Fin 3 → ℝ) → Ω → (Fin 3 → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin 3 → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, 2 * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam))) :
    IsCompleteMix 3 (unifSet (bodyK r F))
      (Homothetic.homMix (clampR r) (fun s => (0:V) + s • (0:V)) 2 Φ
        (Bipyramid.levelMix (nuR r (finrank ℝ V))) ρ) := by
  rw [← levelMix82_half]
  exact thm83_three hF hFi hcen hk hcont heven hconc hr0 hpos (le_refl _) (by norm_num)
    ((starr_iff r _).1 hstar) (condF_half_of hconc hr0) hΦ hmix

/-- **Theorem 70** (`o:thm:bipyr`). Let `k - 1 = dim V ≥ 1`, let `F ⊆ V` be compact with
nonempty interior, centroid `0` and the scaling property with constant `2`, let
`r : [-1, 1] → [0, ∞)` be even, concave and continuous, positive on `(-1, 1)`, and
`K = {(z, y) : |z| ≤ 1, y ∈ r(z) F}`. Under condition (`o:eq:starr`), `U(K)` is `n`-completely
mixable for every `n ≥ 2`. -/
theorem thm70 {r : ℝ → ℝ} {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    (hsp : ScalingProperty (unifSet F) 2)
    (hcont : ContinuousOn r (Icc (-1) 1)) (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z)
    (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
    (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) (hstar : Starr r (finrank ℝ V + 1))
    {n : ℕ} (hn : 2 ≤ n) : CompletelyMixable n (unifSet (bodyK r F)) :=
  thm83 hF hFi hcen hk hcont heven hconc hr0 hpos hsp (le_refl _) (by norm_num)
    ((starr_iff r _).1 hstar) (condF_half_of hconc hr0) hn

/-- (`o:eq:starr`) holds when `k ≥ 3` and `r ≥ 0` is affine on `[1/2, 1]` with `r(1) = 0`:
then `r(a) = 2 r(1/2) (1 - a)` there and the right-hand side is `2 r(1/2)^{k-1}/(k-1)`. -/
theorem starr_of_affine {r : ℝ → ℝ} {k : ℕ} (hk : 3 ≤ k) (h1 : r 1 = 0) (hh : 0 ≤ r (1 / 2))
    {a b : ℝ} (haff : ∀ x ∈ Icc (1 / 2 : ℝ) 1, r x = a * x + b) : Starr r k := by
  have hb : b = -a := by have := haff 1 ⟨by norm_num, le_rfl⟩; linarith
  have hσ : -a = 2 * r (1 / 2) := by
    have := haff (1 / 2) ⟨le_rfl, by norm_num⟩; rw [this, hb]; ring
  refine (starr_iff r k).2 (condP_of_tail le_rfl (by norm_num) (σ := -a)
    (by rw [hσ]; positivity) hk fun x hx => ?_)
  rw [haff x hx, hb]; ring

/-- **Theorem 70** for profiles affine on `[1/2, 1]` (`k = dim V + 1 ≥ 3`): `U(K)` is
`n`-completely mixable for every `n ≥ 2`. -/
theorem thm70_affine {r : ℝ → ℝ} {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 2 ≤ finrank ℝ V)
    (hsp : ScalingProperty (unifSet F) 2)
    (hcont : ContinuousOn r (Icc (-1) 1)) (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z)
    (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
    (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) (h1 : r 1 = 0)
    {a b : ℝ} (haff : ∀ x ∈ Icc (1 / 2 : ℝ) 1, r x = a * x + b)
    {n : ℕ} (hn : 2 ≤ n) : CompletelyMixable n (unifSet (bodyK r F)) :=
  thm70 hF hFi hcen (by omega) hsp hcont heven hconc hr0 hpos
    (starr_of_affine (by omega) h1 (hr0 _ ⟨by norm_num, by norm_num⟩) haff) hn

/-- **Theorem 70, bipyramids** (`r(z) = 1 - |z|`, `k = dim V + 1 ≥ 3`): the uniform distribution
on the bipyramid `{(z, y) : |z| ≤ 1, y ∈ (1 - |z|) F}` is `n`-completely mixable for every
`n ≥ 2`. -/
theorem thm70_bipyramid {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 2 ≤ finrank ℝ V)
    (hsp : ScalingProperty (unifSet F) 2) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (bodyK (fun z => 1 - |z|) F)) := by
  refine thm70_affine hF hFi hcen hk hsp (by fun_prop) (fun z _ => by simp) ?_
    (fun z hz => by simp only [mem_Icc] at hz; simp only [sub_nonneg, abs_le]; constructor
                    <;> linarith)
    (fun z hz => by simp only [mem_Ioo] at hz; simp only [sub_pos, abs_lt]; constructor
                    <;> linarith)
    (by simp) (a := -1) (b := 1) (fun x hx => ?_) hn
  · have : ConcaveOn ℝ univ (fun z : ℝ => 1 - |z|) := by
      have h := (convexOn_univ_norm (E := ℝ)).neg.add
        (concaveOn_const (𝕜 := ℝ) (c := (1:ℝ)) convex_univ)
      convert h using 1; funext z; simp [Real.norm_eq_abs]; ring
    exact this.subset (subset_univ _) (convex_Icc _ _)
  · rw [abs_of_nonneg (by linarith [hx.1])]; ring

end Thm70

/-! ## Transfer lemmas -/

section Transfer

/-- A measure-preserving measurable equivalence carries `U(K)` to `U(e K)`. -/
theorem unifSet_map_equiv {E F : Type*} [MeasureSpace E] [MeasureSpace F] (e : E ≃ᵐ F)
    (he : MeasurePreserving e) (K : Set E) : (unifSet K).map e = unifSet (e '' K) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply (e.measurable hs), Measure.restrict_apply hs, e.image_eq_preimage_symm]
  have h1 : volume (e.symm ⁻¹' K) = volume K := (he.symm e).measure_preimage_equiv K
  have h2 : volume (s ∩ e.symm ⁻¹' K) = volume (e ⁻¹' s ∩ K) := by
    rw [← he.measure_preimage_equiv]; congr 1; ext x; simp
  rw [h1, h2]

/-- **Transfer of complete mixability** along an additive, measure-preserving measurable
equivalence. -/
theorem completelyMixable_map_equiv {E F : Type*} [MeasureSpace E] [MeasureSpace F]
    [AddCommGroup E] [AddCommGroup F] [MeasurableSingletonClass F] [MeasurableAdd₂ F]
    (e : E ≃ᵐ F) (he : MeasurePreserving e) (hadd : ∀ x y, e (x + y) = e x + e y) {K : Set E}
    {n : ℕ} (h : CompletelyMixable n (unifSet K)) : CompletelyMixable n (unifSet (e '' K)) := by
  obtain ⟨P, hP⟩ := h
  have e0 : e 0 = 0 := by
    have := hadd 0 0; simp only [add_zero] at this
    exact (left_eq_add.1 this)
  let L : E →+ F := ⟨⟨e, e0⟩, hadd⟩
  have := hP.map_add_hom L e.measurable (fun _ => 0)
  refine ⟨P.map (fun x i => 0 + L (x i)), ?_⟩
  have hfun : (fun x : E => (0 : F) + L x) = e := by funext x; simp [L]
  simp only [hfun] at this
  rw [← unifSet_map_equiv e he K]
  exact this

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Lemma 48** for sets: the scaling property passes to images under bijective affine maps. -/
theorem scalingProperty_image {K : Set V} {m : ℝ} (h : ScalingProperty (unifSet K) m)
    {M : V →ₗ[ℝ] V} (hM : LinearMap.det M ≠ 0) (b : V) :
    ScalingProperty (unifSet ((fun x => M x + b) '' K)) m := by
  rw [← unifSet_map_affine K hM b]
  simpa using scalingProperty_map_affine h (LinearMap.toContinuousLinearMap M) b

/-- The swap `ℝ × V → V × ℝ` as an additive measure-preserving equivalence. -/
theorem completelyMixable_swap {K : Set (ℝ × V)} {n : ℕ} (h : CompletelyMixable n (unifSet K)) :
    CompletelyMixable n (unifSet (Prod.swap '' K)) := by
  have := completelyMixable_map_equiv (MeasurableEquiv.prodComm : (ℝ × V) ≃ᵐ (V × ℝ))
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure V)))
    (fun x y => rfl) h
  exact this

/-- A set symmetric about `0` has centroid `0`. -/
theorem integral_unifSet_eq_zero {K : Set V} (hK : ∀ x ∈ K, -x ∈ K) :
    ∫ y, y ∂(unifSet K) = 0 := by
  set M : V →ₗ[ℝ] V := (-1 : ℝ) • LinearMap.id
  have hdet : LinearMap.det M ≠ 0 := by
    simp only [M, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have himg : (fun x => M x + 0) '' K = K := by
    ext x
    simp only [M, neg_smul, one_smul, add_zero,
      mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hK y hy
    · intro hx; exact ⟨-x, hK x hx, neg_neg x⟩
  have hmap := unifSet_map_affine K hdet 0
  rw [himg] at hmap
  have hm : Measurable (fun x => M x + 0) :=
    (M.continuous_of_finiteDimensional.add continuous_const).measurable
  have key : ∫ y, y ∂(unifSet K) = -∫ y, y ∂(unifSet K) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (f := fun y : V => y) hm.aemeasurable aestronglyMeasurable_id,
      ← integral_neg]
    simp [M]
  have h2 : (2 : ℝ) • ∫ y, y ∂(unifSet K) = 0 := by
    rw [two_smul]; nth_rewrite 2 [key]; exact add_neg_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Linear images of a body: compactness, nonempty interior. -/
theorem image_props {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    {M : V →ₗ[ℝ] V} (hM : LinearMap.det M ≠ 0) :
    IsCompact (M '' F) ∧ (interior (M '' F)).Nonempty := by
  let e : V ≃L[ℝ] V := (LinearMap.equivOfDetNeZero M hM).toContinuousLinearEquiv
  have he : ∀ x, e x = M x := fun x => rfl
  have hset : M '' F = e '' F := by simp only [he]
  refine ⟨hset ▸ hF.image e.continuous, ?_⟩
  rw [hset]
  exact (hFi.image e).mono
    ((e.isOpenMap _ isOpen_interior).subset_interior_iff.2 (image_mono interior_subset))

/-- **Theorem 70 over linear images**: if `F` is compact, symmetric about `0`, with nonempty
interior and the scaling property with constant `2`, the conclusion of Theorem 70 holds for the
body over `M F`, for every linear bijection `M` (ellipsoids from balls, parallelotopes from
cubes). -/
theorem thm70_image {r : ℝ → ℝ} {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hsymm : ∀ x ∈ F, -x ∈ F) (hk : 1 ≤ finrank ℝ V) (hsp : ScalingProperty (unifSet F) 2)
    (hcont : ContinuousOn r (Icc (-1) 1)) (heven : ∀ z ∈ Icc (-1:ℝ) 1, r (-z) = r z)
    (hconc : ConcaveOn ℝ (Icc (-1) 1) r) (hr0 : ∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ r z)
    (hpos : ∀ z ∈ Ioo (-1:ℝ) 1, 0 < r z) (hstar : Starr r (finrank ℝ V + 1))
    {M : V →ₗ[ℝ] V} (hM : LinearMap.det M ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (bodyK r (M '' F))) := by
  obtain ⟨hc, hi⟩ := image_props hF hFi hM
  have hsp' := scalingProperty_image hsp hM 0
  simp only [add_zero] at hsp'
  have hs : ∀ x ∈ M '' F, -x ∈ M '' F := by
    rintro _ ⟨y, hy, rfl⟩; exact ⟨-y, hsymm y hy, by simp⟩
  exact thm70 hc hi (integral_unifSet_eq_zero hs) hk hsp' hcont heven hconc hr0 hpos hstar hn

end Transfer

/-! ## The bipyramid profile -/

section Profile

/-- The profile `r(z) = 1 - |z|` of the bipyramids satisfies the hypotheses of Theorem 70, and
(`o:eq:starr`) for `k ≥ 3`. -/
theorem bip_profile {k : ℕ} (hk : 3 ≤ k) :
    ContinuousOn (fun z : ℝ => 1 - |z|) (Icc (-1) 1) ∧
    (∀ z ∈ Icc (-1:ℝ) 1, 1 - |-z| = 1 - |z|) ∧
    ConcaveOn ℝ (Icc (-1) 1) (fun z : ℝ => 1 - |z|) ∧
    (∀ z ∈ Icc (-1:ℝ) 1, 0 ≤ 1 - |z|) ∧ (∀ z ∈ Ioo (-1:ℝ) 1, 0 < 1 - |z|) ∧
    Starr (fun z : ℝ => 1 - |z|) k := by
  refine ⟨by fun_prop, fun z _ => by simp, ?_,
    fun z hz => by simp only [mem_Icc] at hz; simp only [sub_nonneg, abs_le]; constructor
                   <;> linarith,
    fun z hz => by simp only [mem_Ioo] at hz; simp only [sub_pos, abs_lt]; constructor
                   <;> linarith,
    starr_of_affine hk (by simp) (by norm_num) (a := -1) (b := 1) fun x hx => ?_⟩
  · have h := (convexOn_univ_norm (E := ℝ)).neg.add
      (concaveOn_const (𝕜 := ℝ) (c := (1:ℝ)) convex_univ)
    have h' : ConcaveOn ℝ univ (fun z : ℝ => 1 - |z|) := by
      convert h using 1; funext z; simp [Real.norm_eq_abs]; ring
    exact h'.subset (subset_univ _) (convex_Icc _ _)
  · rw [abs_of_nonneg (by linarith [hx.1])]; ring

end Profile

/-! ## Ellipsoids, parallelotopes, the octahedron -/

section Instances

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Theorem 70, bipyramids over linear images** of a compact set `F`, symmetric about `0`,
with nonempty interior and the scaling property with constant `2`, `dim V ≥ 2`. -/
theorem bipyr_image {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hsymm : ∀ x ∈ F, -x ∈ F) (hk : 2 ≤ finrank ℝ V) (hsp : ScalingProperty (unifSet F) 2)
    {M : V →ₗ[ℝ] V} (hM : LinearMap.det M ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (bodyK (fun z => 1 - |z|) (M '' F))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bip_profile (k := finrank ℝ V + 1) (by omega)
  exact thm70_image hF hFi hsymm (by omega) hsp h1 h2 h3 h4 h5 h6 hM hn

/-- **Theorem 70, ellipsoids** (with Theorem 51): for `j ≥ 2` and every linear bijection `M` of
`ℝ^j`, the uniform distribution on the double cone `{(z, y) : |z| ≤ 1, y ∈ (1 - |z|) M(B)}`
over the ellipsoid `M(B)` is `n`-completely mixable for every `n ≥ 2`. -/
theorem bipyr_ellipsoid {j : ℕ} (hj : 2 ≤ j) {M : EuclideanSpace ℝ (Fin j) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin j)} (hM : LinearMap.det M ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n
      (unifSet (bodyK (fun z => 1 - |z|) (M '' closedBall (0 : EuclideanSpace ℝ (Fin j)) 1))) :=
  bipyr_image (isCompact_closedBall _ _)
    ⟨0, interior_mono ball_subset_closedBall (by rw [isOpen_ball.interior_eq]; simp)⟩
    (fun x hx => by simpa using hx) (by simpa using hj) (Ball.ball_scalingProperty j) hM hn

/-- The centred cube `[-1, 1]^m`. -/
def ccube (m : ℕ) : Set (Fin m → ℝ) := Set.pi univ fun _ => Icc (-1) 1

lemma ccube_eq (m : ℕ) :
    ccube m = (fun x => ((2:ℝ) • LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] _) x + (fun _ => -1)) ''
      FrustumMix.cubeSet m := by
  ext y
  simp only [ccube, FrustumMix.cubeSet, mem_pi, mem_univ, mem_Icc, forall_const, mem_image,
    LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · intro hy
    refine ⟨fun i => (y i + 1) / 2, fun i => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩, ?_⟩
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · rintro ⟨x, hx, rfl⟩ i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith [(hx i).1, (hx i).2]

lemma ccube_props (m : ℕ) : IsCompact (ccube m) ∧ (interior (ccube m)).Nonempty ∧
    (∀ x ∈ ccube m, -x ∈ ccube m) ∧ ScalingProperty (unifSet (ccube m)) 2 := by
  refine ⟨isCompact_univ_pi fun _ => isCompact_Icc, ⟨0, ?_⟩, ?_, ?_⟩
  · have ho : IsOpen (Set.pi univ fun _ : Fin m => Ioo (-1 : ℝ) 1) :=
      isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
    refine interior_mono (pi_mono fun _ _ => Ioo_subset_Icc_self) ?_
    rw [ho.interior_eq]; simp
  · intro x hx i _
    have := hx i (mem_univ _)
    simp only [mem_Icc, Pi.neg_apply] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · rw [ccube_eq]
    refine scalingProperty_image (ConeMix.scalingProperty_cube m) ?_ _
    simp [LinearMap.det_smul]

/-- **Theorem 70, parallelotopes** (with the scaling property of the cube): for `m ≥ 2` and
every linear bijection `M` of `ℝ^m`, the uniform distribution on the bipyramid
`{(z, y) : |z| ≤ 1, y ∈ (1 - |z|) M([-1, 1]^m)}` over the centred parallelotope
`M([-1, 1]^m)` is `n`-completely mixable for every `n ≥ 2`. -/
theorem bipyr_parallelotope {m : ℕ} (hm : 2 ≤ m) {M : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)}
    (hM : LinearMap.det M ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (bodyK (fun z => 1 - |z|) (M '' ccube m))) := by
  obtain ⟨h1, h2, h3, h4⟩ := ccube_props m
  exact bipyr_image h1 h2 h3 (by simpa using hm) h4 hM hn

end Instances

/-! ## Sections given by a gauge -/

/-- For an absolutely homogeneous `g` vanishing only at `0`, `t ≥ 0` and `ρ ≥ 0`:
`y ∈ t • {g ≤ ρ}` iff `g y ≤ t ρ`. -/
lemma mem_smul_sublevel {X : Type*} [AddCommGroup X] [Module ℝ X] (g : X → ℝ)
    (hg : ∀ (c : ℝ) y, g (c • y) = |c| * g y) (h0 : ∀ y, g y ≤ 0 → y = 0) {t ρ : ℝ}
    (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (y : X) : y ∈ t • {x | g x ≤ ρ} ↔ g y ≤ t * ρ := by
  have g0 : g 0 = 0 := by have := hg 0 0; simpa using this
  rcases ht.eq_or_lt with rfl | ht
  · have hne : ({x | g x ≤ ρ} : Set X).Nonempty := ⟨0, by simp [g0, hρ]⟩
    rw [zero_smul_set hne, zero_mul, mem_zero]
    exact ⟨fun h => by rw [h, g0], h0 y⟩
  · rw [mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_ofPred_eq, hg, abs_inv, abs_of_pos ht,
      inv_mul_le_iff₀ ht]

/-! ## The octahedron and the cross-polytopes -/

section Cross

open SymmCor

lemma sumAbs_smul {m : ℕ} (c : ℝ) (y : Fin m → ℝ) : ∑ i, |(c • y) i| = |c| * ∑ i, |y i| := by
  simp [abs_mul, Finset.mul_sum]

lemma sumAbs_zero {m : ℕ} (y : Fin m → ℝ) (h : ∑ i, |y i| ≤ 0) : y = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (y i))).1
    (le_antisymm h (Finset.sum_nonneg fun i _ => abs_nonneg _))
  funext i; simpa using this i (Finset.mem_univ _)

/-- The cross-polytope of `ℝ^{m+1}` is the bipyramid over the cross-polytope of `ℝ^m`. -/
lemma crossPoly_eq (m : ℕ) :
    crossPoly m = Prod.swap '' bodyK (fun z => 1 - |z|) (crossO m) := by
  ext ⟨y, z⟩
  rw [image_swap_eq_preimage_swap]
  simp only [crossPoly, mem_preimage, Prod.swap_prod_mk, bodyK, mem_ofPred_eq]
  have hc : crossO m = {x | ∑ i, |x i| ≤ 1} := rfl
  rw [hc]
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (y i))
  constructor
  · intro h
    have hz : |z| ≤ 1 := by linarith
    refine ⟨hz, (mem_smul_sublevel _ sumAbs_smul sumAbs_zero (by linarith) zero_le_one y).2 ?_⟩
    linarith
  · rintro ⟨hz, hy⟩
    have := (mem_smul_sublevel _ sumAbs_smul sumAbs_zero (by linarith) zero_le_one y).1 hy
    linarith

/-- The square `{|y₁| + |y₂| ≤ 1}` is the image of `[-1, 1]²` under
`x ↦ ((x₁ + x₂)/2, (x₁ - x₂)/2)`. -/
def sqMap : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![1/2, 1/2; 1/2, -1/2]

lemma det_sqMap : LinearMap.det sqMap ≠ 0 := by
  rw [sqMap, LinearMap.det_toLin', Matrix.det_fin_two_of]; norm_num

lemma sqMap_apply (x : Fin 2 → ℝ) : sqMap x = ![(x 0 + x 1) / 2, (x 0 - x 1) / 2] := by
  funext i
  fin_cases i <;> simp [sqMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma crossO_two : crossO 2 = sqMap '' ccube 2 := by
  ext y
  simp only [crossO, mem_ofPred_eq, Fin.sum_univ_two, mem_image, ccube, mem_pi, mem_univ,
    mem_Icc, forall_const, sqMap_apply]
  constructor
  · intro h
    refine ⟨![y 0 + y 1, y 0 - y 1], fun i => ?_, ?_⟩
    · fin_cases i <;> simp <;> constructor <;>
        cases abs_cases (y 0) <;> cases abs_cases (y 1) <;> linarith
    · funext i; fin_cases i <;> simp
  · rintro ⟨x, hx, rfl⟩
    have h0 := hx 0; have h1 := hx 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    cases abs_cases ((x 0 + x 1) / 2) <;> cases abs_cases ((x 0 - x 1) / 2) <;> linarith

/-- **Theorem 70, the regular octahedron** (as the cross-polytope `{|y₁| + |y₂| + |z| ≤ 1}`,
an affine image of the regular octahedron): its uniform distribution is `n`-completely mixable
for every `n ≥ 2`. -/
theorem octahedron {n : ℕ} (hn : 2 ≤ n) : CompletelyMixable n (unifSet (crossPoly 2)) := by
  rw [crossPoly_eq, crossO_two]
  exact completelyMixable_swap (bipyr_parallelotope le_rfl det_sqMap hn)

end Cross

/-! ## Double cones over balls and Corollary 99(b) -/

section DCone

open SymmCor

variable {m : ℕ}

lemma norm_eq_eNorm (x : EuclideanSpace ℝ (Fin m)) : ‖x‖ = SymmCor.eNorm (WithLp.ofLp x) := by
  rw [EuclideanSpace.norm_eq, SymmCor.eNorm]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

lemma eNorm_zero_of {y : Fin m → ℝ} (h : SymmCor.eNorm y ≤ 0) : y = 0 := by
  have h1 : ∑ i, y i ^ 2 = 0 := by
    have := Real.sqrt_eq_zero'.1 (le_antisymm h (Real.sqrt_nonneg _))
    exact le_antisymm this (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i))).1 h1
  funext i; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (this i (Finset.mem_univ _))

/-- The unit ball `{eNorm ≤ 1}` of `ℝ^m` is the image of the ball of
`EuclideanSpace ℝ (Fin m)` under the measure-preserving identification. -/
lemma ballE_one_eq : ballE m 1 =
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm '' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  ext y
  simp only [ballE, mem_ofPred_eq, mem_image, mem_closedBall_zero_iff]
  constructor
  · intro hy
    exact ⟨WithLp.toLp 2 y, by rw [norm_eq_eNorm]; simpa using hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    rw [norm_eq_eNorm] at hx; simpa using hx

lemma ballE_smul {ρ : ℝ} (hρ : 0 < ρ) :
    ((ρ • LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) '' ballE m 1) = ballE m ρ := by
  ext y
  simp only [ballE, mem_ofPred_eq, mem_image, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SymmCor.eNorm_smul, abs_of_pos hρ]; nlinarith
  · intro hy
    refine ⟨ρ⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]⟩
    rw [SymmCor.eNorm_smul, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ, mul_one]; exact hy

lemma ballE_one_props :
    IsCompact (ballE m 1) ∧ (interior (ballE m 1)).Nonempty ∧ (∀ x ∈ ballE m 1, -x ∈ ballE m 1) ∧
      ScalingProperty (unifSet (ballE m 1)) 2 := by
  have hpres := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)
  refine ⟨?_, ⟨0, ?_⟩, fun x hx => ?_, ?_⟩
  · rw [ballE_one_eq]
    exact (isCompact_closedBall _ _).image (PiLp.continuous_ofLp 2 _)
  · have ho : IsOpen {y : Fin m → ℝ | SymmCor.eNorm y < 1} :=
      isOpen_lt continuous_eNorm continuous_const
    refine interior_mono (s := {y : Fin m → ℝ | SymmCor.eNorm y < 1})
      (fun y (hy : SymmCor.eNorm y < 1) => (show SymmCor.eNorm y ≤ 1 from hy.le)) ?_
    rw [ho.interior_eq]
    show SymmCor.eNorm (0 : Fin m → ℝ) < 1
    simp [SymmCor.eNorm]
  · have : SymmCor.eNorm (-x) = SymmCor.eNorm x := by
      rw [show -x = (-1 : ℝ) • x by simp, SymmCor.eNorm_smul]; simp
    show SymmCor.eNorm (-x) ≤ 1; rw [this]; exact hx
  · rw [ballE_one_eq, ← unifSet_map_equiv _ hpres]
    have := scalingProperty_map_affine (Ball.ball_scalingProperty m)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ)) 0
    have hf : (⇑(MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm) =
        fun x => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)) x := rfl
    rw [hf]; simpa using this

/-- The double cone over `B_ρ` is the body of Theorem 70 over `B_ρ` (level written last). -/
lemma dcone_eq {ρ : ℝ} (hρ : 0 ≤ ρ) :
    dcone m ρ = Prod.swap '' bodyK (fun z => 1 - |z|) (ballE m ρ) := by
  ext ⟨y, z⟩
  rw [image_swap_eq_preimage_swap]
  simp only [dcone, mem_preimage, Prod.swap_prod_mk, bodyK, mem_ofPred_eq]
  have hb : ballE m ρ = {x | SymmCor.eNorm x ≤ ρ} := rfl
  rw [hb]
  constructor
  · rintro ⟨hz, hy⟩
    exact ⟨hz, (mem_smul_sublevel _ SymmCor.eNorm_smul (fun _ => eNorm_zero_of) (by linarith)
      hρ y).2
      (by linarith)⟩
  · rintro ⟨hz, hy⟩
    exact ⟨hz, by
      have := (mem_smul_sublevel _ SymmCor.eNorm_smul (fun _ => eNorm_zero_of)
        (by linarith) hρ y).1 hy
      linarith⟩

/-- **Theorem 70 for the double cone over a ball** (with Theorem 51): for `m ≥ 2` (dimension
`m + 1 ≥ 3`) and `ρ > 0`, the uniform distribution on
`{(y, z) : |z| ≤ 1, ‖y‖ ≤ ρ (1 - |z|)}` is `n`-completely mixable for every `n ≥ 2`. -/
theorem dcone_completelyMixable (hm : 2 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (dcone m ρ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := ballE_one_props (m := m)
  have hdet : LinearMap.det (ρ • LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) ≠ 0 := by
    simp [LinearMap.det_smul, hρ.ne']
  have := bipyr_image h1 h2 h3 (by simpa using hm) h4 hdet hn
  rw [ballE_smul hρ] at this
  rw [dcone_eq hρ.le]
  exact completelyMixable_swap this

/-- **Corollary 99(b)** (`st:cor:symm`), without the hypothesis `hL3` of `SymmCor.partB`: for
`d = m + 1 ≥ 3`, the uniform distribution on the cross-polytope of `ℝ^d` is `n`-completely
mixable for every even `n ≥ 2` and every odd `n ≥ 3 v_{d-1}`. -/
theorem cor99b (hm : 2 ≤ m) :
    (∀ n : ℕ, Even n → n ≠ 0 → CompletelyMixable n (unifSet (crossPoly m))) ∧
      (∀ n : ℕ, Odd n → 3 * vcross m ≤ n → CompletelyMixable n (unifSet (crossPoly m))) :=
  partB (by omega) (dcone_completelyMixable hm (by positivity) (by norm_num))

/-- **Corollary 99(b), `d = 4`**: the cross-polytope of `ℝ⁴` is `n`-completely mixable for every
`n ≥ 2` other than `3`. -/
theorem cor99b_four : ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet (crossPoly 3)) :=
  partB_four (dcone_completelyMixable (by norm_num) (by positivity) (by norm_num))

/-- **Corollary 99(b), `d = 5`**: the cross-polytope of `ℝ⁵` is `n`-completely mixable for every
`n ≥ 2` other than `3` and `5`. -/
theorem cor99b_five :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → n ≠ 5 → CompletelyMixable n (unifSet (crossPoly 4)) :=
  partB_five (dcone_completelyMixable (by norm_num) (by positivity) (by norm_num))

end DCone

end Mixes.Bipyr
