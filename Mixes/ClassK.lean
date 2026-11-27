import Mixes.Cone
import Mixes.FrustumMix
import Mixes.Uniform
import Mixes.Ball

/-!
# The class `𝒦` (Lemma 59, Definition 60, Theorem 61)

Item M1g of the verification priorities (`b:lem:join`, `b:def:class`, `b:thm:class` in
`mixes/main.tex`).

* `transport`: measure-preserving linear equivalences keep the scaling property; `eProd`, `eFr`,
  `eJ` identify `ℝ^{d₁} × ℝ^{d₂}`, `ℝ × ℝ^m`, `ℝ × ℝ^a × ℝ^a` with `ℝ^{d₁+d₂}`, `ℝ^{m+1}`,
  `ℝ^{2a+1}`. `Good K`: measurable, bounded, of finite positive volume.
* Lemma 59 (`b:lem:join`), joins `joinSet K₁ K₂` in the coordinates `(θ, x, y)`:
  `unifSet_joinSet` (the slicing, with the Jacobian `(1-θ)^a θ^a`, so `θ` has the density
  `gLaw a`); `khintchine` (`g` is the mixture of the uniform distributions on its level sets
  `[1/2 - w, 1/2 + w]`, `w ∼ wLaw a`); `isJointMix_levels` (the levels from Lemma 1 for the
  centred intervals `[-λᵢ, λᵢ]`); `isJointMix_stepJ` (the fibres); `joinMix_isJointMix` (the
  construction of the paper); `join_scalingProperty` (the constant `2m`, for `m ≥ 1`).
  `join_points_not_scaling`: the hypothesis `m ≥ 1` cannot be dropped (two points).
* Definition 60 (`b:def:class`): `InK d K`, full-dimensional members `K ⊆ ℝ^d`.
* Theorem 61 (`b:thm:class`): `classK_scalingProperty` (constant `d + 1`),
  `classK_scalingProperty_map` (lower-dimensional members, as images of measures),
  `classK_jointlyMixable`, `classK_completelyMixable` (`n ≥ d + 1`),
  `cone_completelyMixable_iff` (cones over members: `n ≥ d + 1` is also necessary).

`thm51Ball` discharges `Thm51Ball` from `Ball.ball_scalingPropertySet`; the primed versions
`classK_scalingProperty'`, `classK_jointlyMixable'`, `classK_completelyMixable'`,
`cone_completelyMixable_iff'` assume only Theorem 27.

Hypotheses of the unprimed theorems: `Thm51Ball` (Theorem 51, sufficiency: balls of
dimension `j ≥ 1` have the scaling property with constant `2`; its case `j = 1` is Lemma 1 for
centred intervals, used in Lemma 59) and `Thm27Frustum` (Theorem 27 for the level laws of the
frusta, from `FrustumMix.lean`).
-/

open MeasureTheory Set

noncomputable section

namespace Mixes

namespace ClassK

open FrustumMix

/-! ### Good sets, monotonicity of the constant, transport -/

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F]
  [BorelSpace F] [FiniteDimensional ℝ F]

/-- The regularity carried along the induction: a measurable bounded set of finite positive
volume (every member of `𝒦` is a compact convex body with nonempty interior). -/
structure Good (K : Set E) : Prop where
  meas : MeasurableSet K
  pos : volume K ≠ 0
  fin : volume K ≠ ⊤
  bdd : Bornology.IsBounded K

omit [MeasureSpace E] [BorelSpace E] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F] in
lemma isBounded_image_of_continuous {K : Set E} (hK : Bornology.IsBounded K) {f : E → F}
    (hf : Continuous f) : Bornology.IsBounded (f '' K) :=
  ((hK.isCompact_closure.image hf).isBounded).subset (image_mono subset_closure)

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The scaling property is monotone in the constant. -/
lemma ScalingPropertySet.mono {K : Set E} {m m' : ℝ} (h : ScalingPropertySet K m)
    (hm : m ≤ m') : ScalingPropertySet K m' := by
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := h n hn
  exact ⟨Φ, hΦ, fun lam t hlam hne hc => hmix lam t hlam hne fun k =>
    (mul_le_mul_of_nonneg_right hm (hlam k)).trans (hc k)⟩

variable [(volume : Measure E).IsAddHaarMeasure] [(volume : Measure F).IsAddHaarMeasure]

omit [(volume : Measure E).IsAddHaarMeasure] in
lemma Good.integrable {K : Set E} (hK : Good K) : Integrable id (unifSet K) := by
  obtain ⟨R, hR⟩ := hK.bdd.subset_closedBall 0
  exact integrable_unifSet_of_subset hK.meas hK.pos hK.fin hR

/-- Transport along a measure-preserving linear equivalence keeps goodness and the scaling
property. -/
theorem transport (g : E ≃ᵐ F) (hg : MeasurePreserving g volume volume)
    (hlin : IsLinearMap ℝ g) {K : Set E} (hK : Good K) {m : ℝ} (hs : ScalingPropertySet K m) :
    Good (g '' K) ∧ ScalingPropertySet (g '' K) m := by
  let L : E →ₗ[ℝ] F := IsLinearMap.mk' g hlin
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  let CL : E →L[ℝ] F := ⟨L, hLc⟩
  have hCL : ∀ x, CL x = g x := fun x => rfl
  have himg : g '' K = g.symm ⁻¹' K := g.image_eq_preimage_symm K
  have hvol : volume (g '' K) = volume K := by
    rw [himg]; exact (hg.symm g).measure_preimage_equiv K
  have hG : Good (g '' K) := by
    refine ⟨?_, hvol ▸ hK.pos, hvol ▸ hK.fin, ?_⟩
    · rw [himg]; exact g.symm.measurable hK.meas
    · have : (g : E → F) = CL := funext fun x => (hCL x).symm
      rw [this]; exact isBounded_image_of_continuous hK.bdd CL.continuous
  refine ⟨hG, ?_⟩
  have hmap : (unifSet K).map g = unifSet (g '' K) := by
    have := unifSet_map_preimage g hg (g '' K)
    rwa [g.preimage_image K] at this
  rw [scalingPropertySet_iff hG.pos hG.fin, ← hmap]
  rw [scalingPropertySet_iff hK.pos hK.fin] at hs
  have := scalingProperty_map_affine hs CL 0
  have e : (fun x => CL x + 0) = (g : E → F) := funext fun x => by rw [add_zero, hCL]
  rwa [e] at this

end Transport

/-! ### The coordinate equivalences -/

section Equivs

/-- Concatenation `(Fin d₁ → ℝ) × (Fin d₂ → ℝ) ≃ (Fin (d₁ + d₂) → ℝ)`. -/
def eProd (d₁ d₂ : ℕ) : (Fin d₁ → ℝ) × (Fin d₂ → ℝ) ≃ᵐ (Fin (d₁ + d₂) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d₁ ⊕ Fin d₂ => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ))

lemma eProd_apply (d₁ d₂ : ℕ) (x : (Fin d₁ → ℝ) × (Fin d₂ → ℝ)) (i : Fin (d₁ + d₂)) :
    eProd d₁ d₂ x i = Sum.elim x.1 x.2 (finSumFinEquiv.symm i) := rfl

lemma eProd_mp (d₁ d₂ : ℕ) : MeasurePreserving (eProd d₁ d₂) volume volume :=
  (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d₁ ⊕ Fin d₂ => ℝ))

lemma eProd_lin (d₁ d₂ : ℕ) : IsLinearMap ℝ (eProd d₁ d₂) := by
  constructor
  · intro x y; funext i; simp only [eProd_apply, Pi.add_apply]
    cases finSumFinEquiv.symm i <;> rfl
  · intro c x; funext i; simp only [eProd_apply, Pi.smul_apply]
    cases finSumFinEquiv.symm i <;> rfl

/-- `ℝ × (Fin m → ℝ) ≃ (Fin (m + 1) → ℝ)`, `(s, y) ↦ (s, y₀, …, y_{m-1})`. -/
def eFr (m : ℕ) : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm

lemma eFr_apply (m : ℕ) (p : ℝ × (Fin m → ℝ)) : eFr m p = Fin.cons p.1 p.2 := by
  simp [eFr, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma eFr_mp (m : ℕ) : MeasurePreserving (eFr m) volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _

lemma eFr_lin (m : ℕ) : IsLinearMap ℝ (eFr m) := by
  constructor
  · intro x y; funext i; simp only [eFr_apply, Pi.add_apply]
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · intro c x; funext i; simp only [eFr_apply, Pi.smul_apply]
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- `ℝ × ((Fin a → ℝ) × (Fin a → ℝ)) ≃ (Fin (a + a + 1) → ℝ)`. -/
def eJ (a : ℕ) : ℝ × ((Fin a → ℝ) × (Fin a → ℝ)) ≃ᵐ (Fin (a + a + 1) → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (eProd a a)).trans (eFr (a + a))

lemma eJ_apply (a : ℕ) (p : ℝ × ((Fin a → ℝ) × (Fin a → ℝ))) :
    eJ a p = eFr (a + a) (p.1, eProd a a p.2) := rfl

lemma eJ_mp (a : ℕ) : MeasurePreserving (eJ a) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (eProd_mp a a)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h
  exact (eFr_mp (a + a)).comp h

lemma eJ_lin (a : ℕ) : IsLinearMap ℝ (eJ a) := by
  constructor
  · intro x y
    simp only [eJ_apply, Prod.fst_add, Prod.snd_add, (eProd_lin a a).map_add]
    rw [← (eFr_lin (a + a)).map_add]; rfl
  · intro c x
    simp only [eJ_apply, Prod.smul_fst, Prod.smul_snd, (eProd_lin a a).map_smul]
    rw [← (eFr_lin (a + a)).map_smul]; rfl

end Equivs

/-! ### Points, balls, affine images, products and frusta -/

section Ops

/-- The closed Euclidean unit ball of `ℝ^j`. -/
def eBall (j : ℕ) : Set (Fin j → ℝ) := {x | ∑ i, x i ^ 2 ≤ 1}

/-- **The hypothesis taken from Theorem 51** (`b:thm:ball`, sufficiency, with its Borel
construction): closed balls of dimension `j ≥ 1` have the scaling property with constant `2`.
Not formalised in `Bodies.lean` (it needs the polar decomposition of the uniform distribution on
a ball and Lemma 50). For `j = 1` it is Lemma 1 for the intervals `[-λᵢ, λᵢ]`. -/
def Thm51Ball : Prop := ∀ j : ℕ, 1 ≤ j → ScalingPropertySet (eBall j) 2

lemma good_point : Good (univ : Set (Fin 0 → ℝ)) :=
  ⟨MeasurableSet.univ, by simp [volume_pi], by simp [volume_pi],
    Metric.isBounded_iff.2 ⟨0, fun x _ y _ => by simp [Subsingleton.elim x y]⟩⟩

/-- A point has the scaling property with every constant. -/
lemma scaling_point (c : ℝ) : ScalingPropertySet (univ : Set (Fin 0 → ℝ)) c := by
  have h : simplexSet 0 = univ := by ext x; simp [simplexSet]
  rw [scalingPropertySet_iff good_point.pos good_point.fin, ← h]
  exact scalingProperty_simplex_zero c

lemma eBall_subset (j : ℕ) : eBall j ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have : x i ^ 2 ≤ 1 :=
    le_trans (Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i)) hx
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

lemma good_eBall (j : ℕ) : Good (eBall j) := by
  have hc : Continuous (fun x : Fin j → ℝ => ∑ i, x i ^ 2) := by fun_prop
  refine ⟨(isClosed_le hc continuous_const).measurableSet, ?_, ?_, ?_⟩
  · have hopen : IsOpen {x : Fin j → ℝ | ∑ i, x i ^ 2 < 1} := isOpen_lt hc continuous_const
    have : 0 < volume {x : Fin j → ℝ | ∑ i, x i ^ 2 < 1} :=
      hopen.measure_pos volume ⟨0, by simp⟩
    exact (this.trans_le (measure_mono (s := {x : Fin j → ℝ | ∑ i, x i ^ 2 < 1}) (t := eBall j)
      fun x hx => by simp only [eBall, mem_ofPred_eq] at hx ⊢; exact hx.le)).ne'
  · exact ((Metric.isBounded_closedBall).subset (eBall_subset j)).measure_lt_top.ne
  · exact Metric.isBounded_closedBall.subset (eBall_subset j)

lemma good_affine {d : ℕ} {K : Set (Fin d → ℝ)} (hK : Good K)
    (M : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (hM : LinearMap.det M ≠ 0) (b : Fin d → ℝ) :
    Good ((fun x => M x + b) '' K) := by
  have hc : Continuous (fun x => M x + b) :=
    M.continuous_of_finiteDimensional.add continuous_const
  have hinj : Function.Injective (fun x => M x + b) := by
    intro x y h
    exact (M.equivOfDetNeZero hM).injective (add_right_cancel h)
  have hv := volume_image_affine M b K
  have hD0 : ENNReal.ofReal |LinearMap.det M| ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hM
  refine ⟨hK.meas.image_of_continuousOn_injOn hc.continuousOn hinj.injOn, ?_, ?_,
    isBounded_image_of_continuous hK.bdd hc⟩
  · rw [hv]; exact mul_ne_zero hD0 hK.pos
  · rw [hv]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.fin

lemma good_prod {d₁ d₂ : ℕ} {K₁ : Set (Fin d₁ → ℝ)} {K₂ : Set (Fin d₂ → ℝ)} (h₁ : Good K₁)
    (h₂ : Good K₂) : Good (K₁ ×ˢ K₂) := by
  have hv : volume (K₁ ×ˢ K₂) = volume K₁ * volume K₂ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ⟨h₁.meas.prod h₂.meas, by rw [hv]; exact mul_ne_zero h₁.pos h₂.pos,
    by rw [hv]; exact ENNReal.mul_ne_top h₁.fin h₂.fin, h₁.bdd.prod h₂.bdd⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure]

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurableSet_frustumSet {q : ℝ} {B : Set G} (hB : MeasurableSet B) :
    MeasurableSet (frustumSet q B) := by
  have e : frustumSet q B = {p : ℝ × G | q ≤ p.1 ∧ p.1 ≤ 1 ∧ p.1 ≠ 0 ∧ p.1⁻¹ • p.2 ∈ B} ∪
      (frustumSet q B ∩ {(0, 0)}) := by
    ext ⟨s, y⟩
    simp only [frustumSet, mem_union, mem_ofPred_eq, mem_inter_iff, mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, b, hb, rfl⟩
      by_cases hs : s = 0
      · right; exact ⟨⟨h1, h2, b, hb, rfl⟩, hs, by simp [hs]⟩
      · left; exact ⟨h1, h2, hs, by rwa [inv_smul_smul₀ hs]⟩
    · rintro (⟨h1, h2, hs, hb⟩ | ⟨h, -⟩)
      · exact ⟨h1, h2, _, hb, (smul_inv_smul₀ hs y).symm⟩
      · exact h
  rw [e]
  refine MeasurableSet.union ?_ (Set.subsingleton_singleton.anti inter_subset_right).measurableSet
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      (((measurableSet_singleton 0).compl.preimage measurable_fst).inter
        ((measurable_fst.inv.smul measurable_snd) hB)))

omit [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [(volume : Measure G).IsAddHaarMeasure] in
lemma isBounded_frustumSet {q : ℝ} (hq0 : 0 ≤ q) {B : Set G} (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (frustumSet q B) := by
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × G)) (r := max 1 R)).subset ?_
  rintro ⟨s, y⟩ ⟨h1, h2, b, hb, hy⟩
  simp only at h1 h2 hy
  subst hy
  have hbR : ‖b‖ ≤ R := by simpa using hR hb
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  have hs : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  refine ⟨hs.trans (le_max_left _ _), ?_⟩
  rw [norm_smul]
  calc ‖s‖ * ‖b‖ ≤ 1 * R := mul_le_mul hs hbR (norm_nonneg _) zero_le_one
    _ = R := one_mul R
    _ ≤ max 1 R := le_max_right _ _

/-- The frustum step of Theorem 61: a frustum over a base of dimension `m` with constant
`m + 1` has the constant `m + 2` (Theorem 56 with Lemma 54), given Theorem 27. -/
lemma frustum_step (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {m : ℕ}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set (Fin m → ℝ)} (hB : Good B)
    (hs : ScalingPropertySet B ((m : ℝ) + 1)) :
    Good (frustumSet q B) ∧ ScalingPropertySet (frustumSet q B) (((m + 1 : ℕ) : ℝ) + 1) := by
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
  refine ⟨⟨measurableSet_frustumSet hB.meas, ?_, ?_, isBounded_frustumSet hq0 hB.bdd⟩, ?_⟩
  · exact volume_frustumSet_ne_zero hq0 hq1 hB.meas hB.pos
  · exact volume_frustumSet_ne_top hq0 hq1 hB.meas hB.fin
  have h := frustum_scalingProperty hq0 hq1 hB.meas hB.pos hB.fin hB.integrable
    (h27 _ q hq0 hq1) ((scalingPropertySet_iff hB.pos hB.fin _).1 hs)
  rw [hfin] at h
  refine ScalingPropertySet.mono h ?_
  have hle := frustum_constant_le (k := m + 1) (by omega) hq0 hq1 (m := (m : ℝ) + 1)
    (by positivity)
  refine hle.trans (max_le (by push_cast; rfl) ?_)
  push_cast
  rw [mul_div_cancel_left₀ _ (by positivity)]

end Ops

/-! ### Lemma 59: the join, its slicing -/

section JoinSlicing

/-- The unnormalised law `θ^a (1-θ)^a dθ` on `(0, 1)`: the Jacobian of the join. -/
def jacPre (a : ℕ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity fun θ => ENNReal.ofReal (θ ^ a * (1 - θ) ^ a)

/-- The law with density `g(θ) = θ^a (1-θ)^a / B(a+1, a+1)` on `[0, 1]`. -/
def gLaw (a : ℕ) : Measure ℝ := (jacPre a univ)⁻¹ • jacPre a

instance (a : ℕ) : SFinite (jacPre a) := by unfold jacPre; infer_instance

lemma jacPre_univ (a : ℕ) :
    jacPre a univ = ENNReal.ofReal (∫ θ in (0 : ℝ)..1, θ ^ a * (1 - θ) ^ a) := by
  rw [jacPre, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  · exact ((by fun_prop : Continuous fun θ : ℝ => θ ^ a * (1 - θ) ^ a).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact mul_nonneg (pow_nonneg hθ.1.le _) (pow_nonneg (by linarith [hθ.2]) _)

lemma jacPre_univ_ne_zero (a : ℕ) : jacPre a univ ≠ 0 := by
  rw [jacPre_univ, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun θ hθ => ?_) zero_lt_one
  · exact (by fun_prop : Continuous fun θ : ℝ => θ ^ a * (1 - θ) ^ a).intervalIntegrable _ _
  · exact mul_pos (pow_pos hθ.1 _) (pow_pos (by linarith [hθ.2]) _)

lemma jacPre_univ_ne_top (a : ℕ) : jacPre a univ ≠ ⊤ := by
  rw [jacPre_univ]; exact ENNReal.ofReal_ne_top

instance gLaw_isProb (a : ℕ) : IsProbabilityMeasure (gLaw a) := by
  constructor
  rw [gLaw, smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (jacPre_univ_ne_zero a) (jacPre_univ_ne_top a)]

lemma gLaw_ae_mem (a : ℕ) : ∀ᵐ θ ∂gLaw a, θ ∈ Icc (0 : ℝ) 1 := by
  have h1 : ∀ᵐ θ ∂jacPre a, θ ∈ Icc (0 : ℝ) 1 := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Ioo_subset_Icc_self hθ
  exact Measure.ae_smul_measure h1 _

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure]

/-- The join `J(K₁, K₂)`, in the coordinates `(θ, x, y)`: the points
`(θ, (1 - θ) u, θ v)`, `u ∈ K₁`, `v ∈ K₂`, `0 ≤ θ ≤ 1` (the paper writes `((1-θ)u, θv, θ)`). -/
def joinSet (K₁ K₂ : Set G) : Set (ℝ × (G × G)) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ ∃ u ∈ K₁, ∃ v ∈ K₂, p.2 = ((1 - p.1) • u, p.1 • v)}

/-- The map `(θ, u, v) ↦ (θ, (1 - θ) u, θ v)`. -/
def joinMap (p : ℝ × (G × G)) : ℝ × (G × G) := (p.1, ((1 - p.1) • p.2.1, p.1 • p.2.2))

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurable_joinMap : Measurable (joinMap : ℝ × (G × G) → ℝ × (G × G)) := by
  unfold joinMap; fun_prop

/-- The join up to a null set: `0 < θ < 1`, `(1 - θ)⁻¹ x ∈ K₁`, `θ⁻¹ y ∈ K₂`. -/
def joinCore (K₁ K₂ : Set G) : Set (ℝ × (G × G)) :=
  {p | p.1 ∈ Ioo 0 1 ∧ (1 - p.1)⁻¹ • p.2.1 ∈ K₁ ∧ p.1⁻¹ • p.2.2 ∈ K₂}

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurableSet_joinCore {K₁ K₂ : Set G} (h₁ : MeasurableSet K₁) (h₂ : MeasurableSet K₂) :
    MeasurableSet (joinCore K₁ K₂) :=
  (measurable_fst measurableSet_Ioo).inter
    ((((measurable_const.sub measurable_fst).inv.smul
      (measurable_fst.comp measurable_snd)) h₁).inter
      ((measurable_fst.inv.smul (measurable_snd.comp measurable_snd)) h₂))

/-- Fubini and the Jacobian `(1 - θ)^a θ^a`: Lebesgue measure on the join is the image of
`θ^a (1-θ)^a dθ ⊗ vol|_{K₁ × K₂}` under `joinMap`. -/
lemma volume_restrict_joinCore {K₁ K₂ : Set G} (h₁ : MeasurableSet K₁) (h₂ : MeasurableSet K₂) :
    volume.restrict (joinCore K₁ K₂) =
      ((jacPre (Module.finrank ℝ G)).prod (volume.restrict (K₁ ×ˢ K₂))).map joinMap := by
  set a := Module.finrank ℝ G
  have : (volume : Measure (G × G)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  ext C hC
  have hC' : MeasurableSet (joinMap ⁻¹' C) := measurable_joinMap hC
  rw [Measure.restrict_apply hC, Measure.map_apply measurable_joinMap hC,
    Measure.volume_eq_prod, Measure.prod_apply (hC.inter (measurableSet_joinCore h₁ h₂)),
    Measure.prod_apply hC', jacPre,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (measurable_measure_prodMk_left hC')]
  have h1 : ∀ x : ℝ, volume (Prod.mk x ⁻¹' (C ∩ joinCore K₁ K₂)) =
      (Ioo 0 1).indicator (fun x => volume {y : G × G | (x, y) ∈ C ∧
        (1 - x)⁻¹ • y.1 ∈ K₁ ∧ x⁻¹ • y.2 ∈ K₂}) x := by
    intro x
    by_cases hx : x ∈ Ioo 0 1
    · rw [indicator_of_mem hx]
      congr 1
      ext y
      simp [joinCore, hx.1, hx.2]
    · rw [indicator_of_notMem hx]
      convert measure_empty (μ := (volume : Measure (G × G)))
      ext y
      simp only [joinCore, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      rintro ⟨_, h, _⟩
      exact hx h
  rw [lintegral_congr h1, lintegral_indicator measurableSet_Ioo]
  refine setLIntegral_congr_fun measurableSet_Ioo ?_
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  let Lx : (G × G) →ₗ[ℝ] (G × G) :=
    LinearMap.prodMap ((1 - x)⁻¹ • LinearMap.id) (x⁻¹ • LinearMap.id)
  have hdet : LinearMap.det Lx = ((1 - x)⁻¹) ^ a * (x⁻¹) ^ a := by
    simp only [Lx, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, mul_one]
    rfl
  have hdet0 : LinearMap.det Lx ≠ 0 := by
    rw [hdet]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hx1.ne'))
      (pow_ne_zero _ (inv_ne_zero hx0.ne'))
  have hset : {y : G × G | (x, y) ∈ C ∧ (1 - x)⁻¹ • y.1 ∈ K₁ ∧ x⁻¹ • y.2 ∈ K₂} =
      Lx ⁻¹' (Prod.mk x ⁻¹' (joinMap ⁻¹' C) ∩ K₁ ×ˢ K₂) := by
    ext y
    simp [Lx, joinMap, smul_inv_smul₀ hx1.ne', smul_inv_smul₀ hx0.ne']
  simp only [Pi.mul_apply]
  rw [hset, Measure.addHaar_preimage_linearMap _ hdet0, Measure.restrict_apply' (h₁.prod h₂),
    hdet, mul_inv, inv_pow, inv_pow, inv_inv, inv_inv, abs_of_pos (by positivity), mul_comm
      ((1 - x) ^ a)]

omit [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [(volume : Measure G).IsAddHaarMeasure] in
lemma joinCore_subset (K₁ K₂ : Set G) : joinCore K₁ K₂ ⊆ joinSet K₁ K₂ := by
  rintro ⟨θ, x, y⟩ ⟨⟨h0, h1⟩, hx, hy⟩
  simp only at h0 h1 hx hy
  refine ⟨h0.le, h1.le, _, hx, _, hy, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨(smul_inv_smul₀ (by linarith : (1 - θ) ≠ 0) x).symm, (smul_inv_smul₀ h0.ne' y).symm⟩

omit [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [(volume : Measure G).IsAddHaarMeasure] in
lemma joinSet_diff_subset (K₁ K₂ : Set G) :
    joinSet K₁ K₂ \ joinCore K₁ K₂ ⊆ ({0, 1} : Set ℝ) ×ˢ (univ : Set (G × G)) := by
  rintro ⟨θ, x, y⟩ ⟨⟨h0, h1, u, hu, v, hv, he⟩, hn⟩
  simp only [Prod.mk.injEq] at he h0 h1
  obtain ⟨rfl, rfl⟩ := he
  simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true]
  by_contra hθ
  push Not at hθ
  have h0' : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ.1)
  have h1' : θ < 1 := lt_of_le_of_ne h1 hθ.2
  exact hn ⟨⟨h0', h1'⟩, by simpa [inv_smul_smul₀ (by linarith : (1 - θ) ≠ 0)] using hu,
    by simpa [inv_smul_smul₀ h0'.ne'] using hv⟩

omit [BorelSpace G] in
lemma joinSet_ae_eq (K₁ K₂ : Set G) : joinSet K₁ K₂ =ᵐ[volume] joinCore K₁ K₂ := by
  rw [ae_eq_set, sdiff_eq_empty.2 (joinCore_subset K₁ K₂), measure_empty]
  refine ⟨measure_mono_null (joinSet_diff_subset K₁ K₂) ?_, rfl⟩
  rw [Measure.volume_eq_prod, Measure.prod_prod, (Set.toFinite _).measure_zero, zero_mul]

omit [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [(volume : Measure G).IsAddHaarMeasure] in
lemma joinSet_eq (K₁ K₂ : Set G) : joinSet K₁ K₂ = joinCore K₁ K₂ ∪
    ({0} ×ˢ (K₁ ×ˢ {y : G | y = 0 ∧ K₂.Nonempty})) ∪
      ({1} ×ˢ ({x : G | x = 0 ∧ K₁.Nonempty} ×ˢ K₂)) := by
  apply Subset.antisymm
  · rintro ⟨θ, x, y⟩ hp
    by_cases hc : (θ, x, y) ∈ joinCore K₁ K₂
    · exact Or.inl (Or.inl hc)
    · have hd := joinSet_diff_subset K₁ K₂ ⟨hp, hc⟩
      obtain ⟨h0, h1, u, hu, v, hv, he⟩ := hp
      simp only [Prod.mk.injEq] at he h0 h1
      obtain ⟨rfl, rfl⟩ := he
      simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, and_true] at hd
      rcases hd with rfl | rfl
      · left; right
        simp only [mem_prod, mem_singleton_iff, mem_ofPred_eq]
        exact ⟨by simp, by simpa using hu, by simp, v, hv⟩
      · right
        simp only [mem_prod, mem_singleton_iff, mem_ofPred_eq]
        exact ⟨by simp, ⟨by simp, u, hu⟩, by simpa using hv⟩
  · rintro ⟨θ, x, y⟩ ((hp | hp) | hp)
    · exact joinCore_subset K₁ K₂ hp
    · simp only [mem_prod, mem_singleton_iff, mem_ofPred_eq] at hp
      obtain ⟨rfl, hx, rfl, v, hv⟩ := hp
      exact ⟨le_rfl, zero_le_one, x, hx, v, hv, by simp⟩
    · simp only [mem_prod, mem_singleton_iff, mem_ofPred_eq] at hp
      obtain ⟨rfl, ⟨rfl, u, hu⟩, hy⟩ := hp
      exact ⟨zero_le_one, le_rfl, u, hu, y, hy, by simp⟩

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurableSet_joinSet {K₁ K₂ : Set G} (h₁ : MeasurableSet K₁) (h₂ : MeasurableSet K₂) :
    MeasurableSet (joinSet K₁ K₂) := by
  rw [joinSet_eq]
  refine ((measurableSet_joinCore h₁ h₂).union ((measurableSet_singleton 0).prod
    (h₁.prod ?_))).union ((measurableSet_singleton 1).prod (MeasurableSet.prod ?_ h₂))
  · exact (Set.Subsingleton.anti (s := {y : G | y = 0 ∧ K₂.Nonempty})
      (Set.subsingleton_singleton (a := (0 : G))) (fun y hy => hy.1)).measurableSet
  · exact (Set.Subsingleton.anti (s := {y : G | y = 0 ∧ K₁.Nonempty})
      (Set.subsingleton_singleton (a := (0 : G))) (fun y hy => hy.1)).measurableSet

omit [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [(volume : Measure G).IsAddHaarMeasure] in
lemma isBounded_joinSet {K₁ K₂ : Set G} (h₁ : Bornology.IsBounded K₁)
    (h₂ : Bornology.IsBounded K₂) : Bornology.IsBounded (joinSet K₁ K₂) := by
  obtain ⟨R₁, hR₁⟩ := h₁.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := h₂.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × (G × G)))
    (r := max 1 (max R₁ R₂))).subset ?_
  rintro ⟨θ, x, y⟩ ⟨h0, h1, u, hu, v, hv, he⟩
  simp only [Prod.mk.injEq] at he h0 h1
  obtain ⟨rfl, rfl⟩ := he
  have hu' : ‖u‖ ≤ R₁ := by simpa using hR₁ hu
  have hv' : ‖v‖ ≤ R₂ := by simpa using hR₂ hv
  have ha : ‖θ‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hb : ‖1 - θ‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def, norm_smul, norm_smul]
  refine max_le (ha.trans (le_max_left _ _)) (max_le ?_ ?_)
  · calc ‖1 - θ‖ * ‖u‖ ≤ 1 * R₁ := mul_le_mul hb hu' (norm_nonneg _) zero_le_one
      _ ≤ max 1 (max R₁ R₂) := by
        rw [one_mul]; exact (le_max_left _ _).trans (le_max_right _ _)
  · calc ‖θ‖ * ‖v‖ ≤ 1 * R₂ := mul_le_mul ha hv' (norm_nonneg _) zero_le_one
      _ ≤ max 1 (max R₁ R₂) := by
        rw [one_mul]; exact (le_max_right _ _).trans (le_max_right _ _)

lemma volume_joinSet {K₁ K₂ : Set G} (h₁ : MeasurableSet K₁) (h₂ : MeasurableSet K₂) :
    volume (joinSet K₁ K₂) = jacPre (Module.finrank ℝ G) univ * (volume K₁ * volume K₂) := by
  rw [measure_congr (joinSet_ae_eq K₁ K₂), ← Measure.restrict_apply_univ,
    volume_restrict_joinCore h₁ h₂, Measure.map_apply measurable_joinMap MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.volume_eq_prod, Measure.prod_prod]

lemma good_joinSet {K₁ K₂ : Set G} (h₁ : Good K₁) (h₂ : Good K₂) : Good (joinSet K₁ K₂) := by
  have hv := volume_joinSet h₁.meas h₂.meas
  refine ⟨measurableSet_joinSet h₁.meas h₂.meas, ?_, ?_, isBounded_joinSet h₁.bdd h₂.bdd⟩
  · rw [hv]; exact mul_ne_zero (jacPre_univ_ne_zero _) (mul_ne_zero h₁.pos h₂.pos)
  · rw [hv]; exact ENNReal.mul_ne_top (jacPre_univ_ne_top _) (ENNReal.mul_ne_top h₁.fin h₂.fin)

/-- **Lemma 59, the slicing**: the uniform distribution on the join is the law of
`(θ, (1 - θ) u, θ v)` with `θ ∼ g`, `u ∼ U(K₁)` and `v ∼ U(K₂)` independent. -/
theorem unifSet_joinSet {K₁ K₂ : Set G} (h₁ : Good K₁) (h₂ : Good K₂) :
    unifSet (joinSet K₁ K₂) =
      ((gLaw (Module.finrank ℝ G)).prod ((unifSet K₁).prod (unifSet K₂))).map joinMap := by
  set a := Module.finrank ℝ G
  have hres : volume.restrict (joinSet K₁ K₂) =
      ((jacPre a).prod ((volume.restrict K₁).prod (volume.restrict K₂))).map joinMap := by
    rw [Measure.restrict_congr_set (joinSet_ae_eq K₁ K₂), volume_restrict_joinCore h₁.meas h₂.meas,
      Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [unifSet, hres, volume_joinSet h₁.meas h₂.meas, gLaw, unifSet, unifSet]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [Measure.map_smul _ (measurable_joinMap (G := G)).aemeasurable]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (jacPre_univ_ne_zero a)) (Or.inl (jacPre_univ_ne_top a)),
    ENNReal.mul_inv (Or.inl h₁.pos) (Or.inl h₁.fin)]
  ring

lemma isAddHaar_joinSpace : (volume : Measure (ℝ × (G × G))).IsAddHaarMeasure := by
  have : (volume : Measure (G × G)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance

/-- **Lemma 59, the slicing**, for `U(t + λ J)`, every `λ` (a point mass for `λ = 0`). -/
theorem unifScaled_joinSet {K₁ K₂ : Set G} (h₁ : Good K₁) (h₂ : Good K₂)
    (t : ℝ × (G × G)) (lam : ℝ) :
    unifScaled (joinSet K₁ K₂) t lam =
      ((gLaw (Module.finrank ℝ G)).prod ((unifSet K₁).prod (unifSet K₂))).map
        (fun p => t + lam • joinMap p) := by
  have := isAddHaar_joinSpace (G := G)
  have hJ := good_joinSet h₁ h₂
  rw [unifScaled_eq_map hJ.pos hJ.fin, unifSet_joinSet h₁ h₂,
    Measure.map_map (by fun_prop) measurable_joinMap]
  rfl

end JoinSlicing

/-! ### Lemma 59: the density `θ^a (1-θ)^a` as a mixture of uniform distributions -/

section Khintchine

/-- `r(w) = 2 a w (1/4 - w²)^(a-1)`, minus the derivative of `(1/4 - w²)^a`. -/
def rDens (a : ℕ) (w : ℝ) : ℝ := 2 * a * w * (1 / 4 - w ^ 2) ^ (a - 1)

lemma continuous_rDens (a : ℕ) : Continuous (rDens a) := by unfold rDens; fun_prop

/-- The unnormalised law of the half-width `w` of the level set through a uniform point under
the graph of `θ^a (1-θ)^a` (`a ≥ 1`): density `2 w r(w)` on `(0, 1/2)`. -/
def wPre (a : ℕ) : Measure ℝ :=
  (volume.restrict (Ioo 0 (1 / 2))).withDensity fun w => ENNReal.ofReal (2 * w * rDens a w)

instance (a : ℕ) : SFinite (wPre a) := by unfold wPre; infer_instance

lemma integral_rDens {a : ℕ} (ha : 1 ≤ a) (c : ℝ) :
    ∫ w in c..(1 / 2), rDens a w = (1 / 4 - c ^ 2) ^ a := by
  have hderiv : ∀ x ∈ uIcc c (1 / 2),
      HasDerivAt (fun w : ℝ => -(1 / 4 - w ^ 2) ^ a) (rDens a x) x := by
    intro x _
    have h := (((hasDerivAt_pow 2 x).const_sub (1 / 4 : ℝ)).pow a).neg
    convert h using 1
    simp only [rDens]
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_rDens a).intervalIntegrable _ _)]
  have : (1 / 4 - (1 / 2 : ℝ) ^ 2) = 0 := by norm_num
  rw [this, zero_pow (by omega)]
  ring

lemma unifI_map_affine {w : ℝ} (hw : 0 < w) :
    (unifI (-1) 1).map (fun z => 1 / 2 + w * z) = unifI (1 / 2 - w) (1 / 2 + w) := by
  have e : (fun z : ℝ => 1 / 2 + w * z) = (fun z => 1 / 2 + z) ∘ (fun z => w * z) := rfl
  rw [e, ← Measure.map_map (measurable_const_add _) (measurable_const_mul _),
    map_unifI_const_mul hw, map_unifI_const_add]
  congr 1 <;> ring

lemma unifI_apply {l r : ℝ} (h : l < r) {S : Set ℝ} (hS : MeasurableSet S) :
    unifI l r S = (ENNReal.ofReal (r - l))⁻¹ * volume (S ∩ Icc l r) := by
  simp only [unifI, h, ↓reduceIte, smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply hS]

/-- The integrand of the mixture: `r(w)` on `{(w, θ) : |θ - 1/2| ≤ w}`. -/
def mixInt (a : ℕ) (p : ℝ × ℝ) : ENNReal :=
  {p : ℝ × ℝ | |p.2 - 1 / 2| ≤ p.1}.indicator (fun p => ENNReal.ofReal (rDens a p.1)) p

lemma measurable_mixInt (a : ℕ) : Measurable (mixInt a) :=
  Measurable.indicator (by unfold rDens; fun_prop) (measurableSet_le (by fun_prop) measurable_fst)

/-- Integrating `r` over the level sets containing `θ` gives `θ^a (1-θ)^a` (Khintchine). -/
lemma lintegral_mixInt {a : ℕ} (ha : 1 ≤ a) (θ : ℝ) :
    ∫⁻ w in Ioo 0 (1 / 2), mixInt a (w, θ) =
      (Ioo 0 1).indicator (fun θ => ENNReal.ofReal (θ ^ a * (1 - θ) ^ a)) θ := by
  set c := |θ - 1 / 2| with hc_def
  have hc0 : 0 ≤ c := abs_nonneg _
  have e1 : ∀ w, mixInt a (w, θ) = (Ici c).indicator (fun w => ENNReal.ofReal (rDens a w)) w := by
    intro w
    by_cases h : c ≤ w
    · rw [mixInt, indicator_of_mem (show (w, θ) ∈ {p : ℝ × ℝ | |p.2 - 1 / 2| ≤ p.1} from h),
        indicator_of_mem (show w ∈ Ici c from h)]
    · rw [mixInt, indicator_of_notMem (show (w, θ) ∉ {p : ℝ × ℝ | |p.2 - 1 / 2| ≤ p.1} from h),
        indicator_of_notMem (show w ∉ Ici c from h)]
  simp_rw [e1]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  by_cases hc : c < 1 / 2
  · have hθ : θ ∈ Ioo 0 1 := by
      have := abs_lt.1 hc; constructor <;> linarith [this.1, this.2]
    rw [indicator_of_mem hθ]
    have hae : (Ici c ∩ Ioo 0 (1 / 2) : Set ℝ) =ᵐ[volume] Ioc c (1 / 2) := by
      refine ae_eq_set.2 ⟨measure_mono_null (t := {c}) ?_ (measure_singleton c),
        measure_mono_null (t := {1 / 2}) ?_ (measure_singleton _)⟩
      · rintro w ⟨⟨h1, h2, h3⟩, h4⟩
        have h1' : c ≤ w := h1
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at h4
        simp only [mem_singleton_iff]
        rcases h4 with h4 | h4 <;> linarith
      · rintro w ⟨⟨h1, h2⟩, h4⟩
        simp only [mem_inter_iff, mem_Ici, mem_Ioo, not_and_or, not_le, not_lt] at h4
        simp only [mem_singleton_iff]
        rcases h4 with h4 | h4 | h4 <;> linarith
    rw [Measure.restrict_congr_set hae, ← ofReal_integral_eq_lintegral_ofReal,
      ← intervalIntegral.integral_of_le hc.le, integral_rDens ha]
    · congr 1
      rw [hc_def, sq_abs, ← mul_pow]
      congr 1
      ring
    · exact (continuous_rDens a).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      have hw0 : 0 < w := lt_of_le_of_lt hc0 hw.1
      have : 0 ≤ 1 / 4 - w ^ 2 := by nlinarith [hw.2]
      unfold rDens
      positivity
  · have hθ : θ ∉ Ioo 0 1 := by
      rintro ⟨h0, h1⟩
      apply hc
      rw [hc_def, abs_lt]
      constructor <;> linarith
    rw [indicator_of_notMem hθ]
    have : (Ici c ∩ Ioo 0 (1 / 2) : Set ℝ) = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_empty_iff_false, iff_false]
      rintro ⟨h1, -, h2⟩
      push Not at hc
      linarith
    rw [this, Measure.restrict_empty, lintegral_zero_measure]

/-- **Khintchine's representation** (unnormalised): mixing `U[1/2 - w, 1/2 + w]` over
`w ∼ wPre a` gives `θ^a (1-θ)^a dθ` on `(0, 1)`. -/
lemma khintchine_pre {a : ℕ} (ha : 1 ≤ a) {S : Set ℝ} (hS : MeasurableSet S) :
    ((wPre a).prod (unifI (-1) 1)).map (fun p => 1 / 2 + p.1 * p.2) S = jacPre a S := by
  have hf : Measurable (fun p : ℝ × ℝ => 1 / 2 + p.1 * p.2) := by fun_prop
  rw [Measure.map_apply hf hS, Measure.prod_apply (hf hS), wPre,
    lintegral_withDensity_eq_lintegral_mul _ (by unfold rDens; fun_prop)
      (measurable_measure_prodMk_left (hf hS))]
  have step1 : ∀ w ∈ Ioo (0 : ℝ) (1 / 2),
      ((fun w => ENNReal.ofReal (2 * w * rDens a w)) * fun w => unifI (-1) 1
        (Prod.mk w ⁻¹' ((fun p : ℝ × ℝ => 1 / 2 + p.1 * p.2) ⁻¹' S))) w =
        ∫⁻ θ in S, mixInt a (w, θ) := by
    intro w hw
    have hw0 : 0 < w := hw.1
    have hpre : Prod.mk w ⁻¹' ((fun p : ℝ × ℝ => 1 / 2 + p.1 * p.2) ⁻¹' S) =
        (fun z => 1 / 2 + w * z) ⁻¹' S := rfl
    have hint : ∀ θ, mixInt a (w, θ) =
        (Icc (1 / 2 - w) (1 / 2 + w)).indicator (fun _ => ENNReal.ofReal (rDens a w)) θ := by
      intro θ
      by_cases h : |θ - 1 / 2| ≤ w
      · have h' := abs_le.1 h
        rw [mixInt, indicator_of_mem (show (w, θ) ∈ {p : ℝ × ℝ | |p.2 - 1 / 2| ≤ p.1} from h),
          indicator_of_mem (show θ ∈ Icc (1 / 2 - w) (1 / 2 + w) from
            ⟨by linarith [h'.1], by linarith [h'.2]⟩)]
      · rw [mixInt, indicator_of_notMem (show (w, θ) ∉ {p : ℝ × ℝ | |p.2 - 1 / 2| ≤ p.1}
          from h), indicator_of_notMem]
        rintro ⟨h1, h2⟩
        exact h (abs_le.2 ⟨by linarith, by linarith⟩)
    simp only [Pi.mul_apply]
    rw [hpre, ← Measure.map_apply (by fun_prop) hS, unifI_map_affine hw0,
      unifI_apply (by linarith) hS, show 1 / 2 + w - (1 / 2 - w) = 2 * w by ring,
      lintegral_congr hint, lintegral_indicator_const measurableSet_Icc,
      Measure.restrict_apply measurableSet_Icc, inter_comm,
      ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (2 * w)), mul_assoc,
      ← mul_assoc (ENNReal.ofReal (2 * w)),
      ENNReal.mul_inv_cancel (by simpa using hw0) ENNReal.ofReal_ne_top, one_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioo step1,
    lintegral_lintegral_swap (f := fun w θ => mixInt a (w, θ))
      (μ := volume.restrict (Ioo 0 (1 / 2))) (ν := volume.restrict S)
      (measurable_mixInt a).aemeasurable]
  simp_rw [lintegral_mixInt ha]
  rw [jacPre, withDensity_apply _ hS, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, Measure.restrict_restrict hS, inter_comm]

lemma wPre_univ {a : ℕ} (ha : 1 ≤ a) : wPre a univ = jacPre a univ := by
  have h := khintchine_pre ha MeasurableSet.univ
  have hU : unifI (-1) 1 univ = 1 := measure_univ
  rwa [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
    Measure.prod_prod, hU, mul_one] at h

/-- The law of the half-width `w` (Lemma 59): the point mass at `1/2` for `a = 0`, where `g` is
uniform, and the normalised `wPre a` for `a ≥ 1`. -/
def wLaw (a : ℕ) : Measure ℝ := if a = 0 then Measure.dirac (1 / 2) else (wPre a univ)⁻¹ • wPre a

instance wLaw_isProb (a : ℕ) : IsProbabilityMeasure (wLaw a) := by
  unfold wLaw
  split_ifs with ha
  · infer_instance
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 ha
    constructor
    rw [smul_apply, smul_eq_mul, wPre_univ ha1,
      ENNReal.inv_mul_cancel (jacPre_univ_ne_zero a) (jacPre_univ_ne_top a)]

lemma gLaw_zero : gLaw 0 = unifI 0 1 := by
  have hj : jacPre 0 = volume.restrict (Ioo 0 1) := by
    simp [jacPre]
  have hu : unifI 0 1 = volume.restrict (Icc 0 1) := by
    simp [unifI]
  rw [gLaw, hj, hu, Measure.restrict_apply_univ, Real.volume_Ioo]
  simp only [sub_zero, ENNReal.ofReal_one, inv_one, one_smul]
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc

/-- **Khintchine's representation** (Lemma 59): if `w ∼ wLaw a` and `Z ∼ U[-1, 1]` are
independent, then `1/2 + w Z` has the density `g(θ) = θ^a (1-θ)^a / B(a+1, a+1)`; that is, `g` is
the mixture of the uniform distributions on its level sets `[1/2 - w, 1/2 + w]`. -/
theorem khintchine (a : ℕ) :
    ((wLaw a).prod (unifI (-1) 1)).map (fun p => 1 / 2 + p.1 * p.2) = gLaw a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [wLaw, ↓reduceIte]
    rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop), gLaw_zero]
    have := unifI_map_affine (w := 1 / 2) (by norm_num)
    convert this using 2 <;> first | rfl | norm_num
  · simp only [wLaw, show a ≠ 0 by omega, ↓reduceIte]
    rw [Measure.prod_smul_left,
      Measure.map_smul _ (by fun_prop : Measurable fun p : ℝ × ℝ => 1 / 2 + p.1 * p.2).aemeasurable,
      gLaw, wPre_univ ha]
    congr 1
    ext S hS
    exact khintchine_pre ha hS

/-- A Borel function of one uniform variable with a given law. -/
lemma exists_sampler (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ f : ℝ → ℝ, Measurable f ∧ (unifI 0 1).map f = μ := by
  obtain ⟨g, hg, hgμ⟩ := μ.exists_measurable_map_eq
  have hp : Measurable (Set.projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc.measurable
  refine ⟨fun x => g (Set.projIcc 0 1 zero_le_one x), hg.comp hp, ?_⟩
  have hmap : (unifI 0 1).map (Set.projIcc (0 : ℝ) 1 zero_le_one) = volume := by
    ext S hS
    rw [Measure.map_apply hp hS, unitInterval.volume_def,
      (MeasurableEmbedding.subtypeVal measurableSet_Icc).comap_apply]
    have hu : unifI 0 1 = volume.restrict (Icc 0 1) := by simp [unifI]
    rw [hu, Measure.restrict_apply (hp hS)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, by rw [Set.projIcc_of_mem _ h2]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by rwa [Set.projIcc_val], y.2⟩
  rw [show (fun x => g (Set.projIcc (0 : ℝ) 1 zero_le_one x)) =
      g ∘ Set.projIcc (0 : ℝ) 1 zero_le_one from rfl, ← Measure.map_map hg hp, hmap, hgμ]

end Khintchine

/-! ### Lemma 59: the levels, from Lemma 1 for centred intervals -/

section Levels

lemma eBall_one : eBall 1 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc (-1) 1 := by
  ext x
  simp only [eBall, Fin.sum_univ_one, mem_ofPred_eq, mem_preimage, mem_Icc]
  rw [sq_le_one_iff_abs_le_one, abs_le]
  rfl

lemma unifI_neg_one_eq : unifI (-1) 1 = unifSet (Icc (-1 : ℝ) 1) := by
  simp only [unifI, show (-1 : ℝ) < 1 by norm_num, ↓reduceIte, unifSet, Real.volume_Icc]

/-- The coordinate of the uniform distribution on the one-dimensional ball is `U[-1, 1]`. -/
lemma unifSet_eBall_one_map : (unifSet (eBall 1)).map (fun x => x 0) = unifI (-1) 1 := by
  have h := unifSet_map_preimage (MeasurableEquiv.funUnique (Fin 1) ℝ)
    (volume_preserving_funUnique (Fin 1) ℝ) (Icc (-1) 1)
  rw [← eBall_one] at h
  rw [unifI_neg_one_eq, ← h]
  rfl

instance : IsProbabilityMeasure (unifI (-1) 1) := unifI_isProb _ _

lemma integrable_unifI_neg_one : Integrable id (unifI (-1) 1) := by
  rw [unifI_neg_one_eq]
  exact integrable_unifSet_of_subset measurableSet_Icc (by simp [Real.volume_Icc])
    (by simp [Real.volume_Icc]) (R := 1) (fun x hx => by
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le]; exact hx)

lemma integral_unifI_neg_one : ∫ z, z ∂(unifI (-1) 1) = 0 := by
  simp only [unifI, show (-1 : ℝ) < 1 by norm_num, ↓reduceIte]
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

variable {n : ℕ}

/-- The level vector of Lemma 59 from `w` and a joint mix `z` of `U[-λᵢ, λᵢ]`:
`Lᵢ = λᵢ/2 + w zᵢ`, i.e. `Lᵢ` is uniform on `[λᵢ(1/2 - w), λᵢ(1/2 + w)]` given `w`. -/
def levelOf (lam : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => lam i / 2 + p.1 * p.2 i

lemma measurable_levelOf (lam : Fin n → ℝ) : Measurable (levelOf lam) := by
  unfold levelOf; fun_prop

/-- The levels of Lemma 59: if `ZP` is a joint mix of the `U[-λᵢ, λᵢ]` (Lemma 1; here the
coordinate of the scaling property of the segment), then mixing over `w ∼ wLaw a` gives a joint
mix of the laws of `λᵢ θ`, `θ ∼ g`, with sum `∑ λᵢ / 2`. -/
theorem isJointMix_levels (a : ℕ) (lam : Fin n → ℝ) {ZP : Measure (Fin n → ℝ)}
    (hZ : IsJointMix (fun i => (unifI (-1) 1).map (fun z => lam i * z)) ZP) :
    IsJointMix (fun i => (gLaw a).map (fun θ => lam i * θ)) (((wLaw a).prod ZP).map (levelOf lam))
      ∧ ∀ᵐ T ∂(((wLaw a).prod ZP).map (levelOf lam)), ∑ i, T i = (∑ i, lam i) / 2 := by
  obtain ⟨hZp, ⟨sZ, hsZ⟩, hZm⟩ := hZ
  have hsZ0 : sZ = 0 := by
    rw [IsJointMix.sum_eq_integral ⟨hZp, ⟨sZ, hsZ⟩, hZm⟩ (fun i => ?_) hsZ]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [show (∫ y, y ∂(unifI (-1) 1).map (fun z => lam i * z)) =
          ∫ z, lam i * z ∂unifI (-1) 1 from
        integral_map (by fun_prop : Measurable fun z : ℝ => lam i * z).aemeasurable
          aestronglyMeasurable_id, integral_const_mul, integral_unifI_neg_one, mul_zero]
    · rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
      exact integrable_unifI_neg_one.const_mul (lam i)
  subst hsZ0
  have hsum : ∀ᵐ T ∂(((wLaw a).prod ZP).map (levelOf lam)), ∑ i, T i = (∑ i, lam i) / 2 := by
    rw [ae_map_iff (measurable_levelOf lam).aemeasurable (measurableSet_sum_eq' _)]
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hsZ] with p hp
    simp only [levelOf, Finset.sum_add_distrib, ← Finset.mul_sum, hp, mul_zero, add_zero,
      Finset.sum_div]
  refine ⟨⟨inferInstance, ⟨_, hsum⟩, fun i => ?_⟩, hsum⟩
  have e1 : (fun T : Fin n → ℝ => T i) ∘ levelOf lam =
      (fun p : ℝ × ℝ => lam i / 2 + p.1 * p.2) ∘ Prod.map id (fun z : Fin n → ℝ => z i) := rfl
  rw [Measure.map_map (measurable_pi_apply i) (measurable_levelOf lam), e1,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply i), Measure.map_id, hZm i]
  have hpm : (wLaw a).prod ((unifI (-1) 1).map (fun z => lam i * z)) =
      ((wLaw a).prod (unifI (-1) 1)).map (Prod.map id (fun z => lam i * z)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
  show Measure.map _ ((wLaw a).prod ((unifI (-1) 1).map (fun z => lam i * z))) =
    (gLaw a).map _
  rw [hpm, Measure.map_map (by fun_prop) (by fun_prop), ← khintchine a,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  ring

end Levels

/-! ### Lemma 59: the fibres -/

section Fibres

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure] {n : ℕ}

/-- The last step of Lemma 59 for a given level vector `T = (Lᵢ)`: `Xᵢ = tᵢ + (Lᵢ, Uᵢ, Vᵢ)` with
`U = Φ₁ (λ - T, 0) ω₁` and `V = Φ₂ (T, 0) ω₂`. -/
def stepJ (Φ₁ Φ₂ : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)) (lam : Fin n → ℝ)
    (t : Fin n → ℝ × (G × G)) (z : (Fin n → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))) : Fin n → ℝ × (G × G) :=
  fun i => t i + (z.1 i, (Φ₁ (fun j => lam j - z.1 j, 0) z.2.1 i, Φ₂ (z.1, 0) z.2.2 i))

omit [(volume : Measure G).IsAddHaarMeasure] in
lemma measurable_stepJ {Φ₁ Φ₂ : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΦ₁ : Measurable (Function.uncurry Φ₁)) (hΦ₂ : Measurable (Function.uncurry Φ₂))
    (lam : Fin n → ℝ) (t : Fin n → ℝ × (G × G)) : Measurable (stepJ Φ₁ Φ₂ lam t) := by
  have h1 : Measurable (fun z : (Fin n → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
      Φ₁ (fun j => lam j - z.1 j, 0) z.2.1) :=
    hΦ₁.comp (f := fun z : (Fin n → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
      ((fun j => lam j - z.1 j, 0), z.2.1)) (by fun_prop)
  have h2 : Measurable (fun z : (Fin n → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => Φ₂ (z.1, 0) z.2.2) :=
    hΦ₂.comp (f := fun z : (Fin n → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => ((z.1, 0), z.2.2))
      (by fun_prop)
  exact measurable_pi_iff.2 fun i => measurable_const.add
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp h1).prodMk ((measurable_pi_apply i).comp h2)))

/-- The core of Lemma 59: if `P₁` is a joint mix of the laws of `λᵢ θ` (`θ ∼ g`) with sum
`∑ λᵢ / 2`, and `Φ₁, Φ₂` are the Borel constructions of the scaling properties of `K₁, K₂`, then
`stepJ` turns `P₁ ⊗ unifSeq ⊗ unifSeq` into a joint mix of the `U(tᵢ + λᵢ J)`. -/
theorem isJointMix_stepJ {K₁ K₂ : Set G} (h₁ : Good K₁) (h₂ : Good K₂) {m₁ m₂ : ℝ}
    {Φ₁ Φ₂ : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΦ₁ : Measurable (Function.uncurry Φ₁)) (hΦ₂ : Measurable (Function.uncurry Φ₂))
    (hmix₁ : ∀ σ : Fin n → ℝ, (∀ i, 0 ≤ σ i) → (∃ i, σ i ≠ 0) → (∀ k, m₁ * σ k ≤ ∑ i, σ i) →
      IsJointMix (fun i => (unifSet K₁).map (fun x => (0 : Fin n → G) i + σ i • x))
        (unifSeq.map (Φ₁ (σ, 0))))
    (hmix₂ : ∀ σ : Fin n → ℝ, (∀ i, 0 ≤ σ i) → (∃ i, σ i ≠ 0) → (∀ k, m₂ * σ k ≤ ∑ i, σ i) →
      IsJointMix (fun i => (unifSet K₂).map (fun x => (0 : Fin n → G) i + σ i • x))
        (unifSeq.map (Φ₂ (σ, 0))))
    (lam : Fin n → ℝ) (t : Fin n → ℝ × (G × G)) (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (hc : ∀ k, 2 * max m₁ m₂ * lam k ≤ ∑ i, lam i)
    {P₁ : Measure (Fin n → ℝ)} [IsProbabilityMeasure P₁]
    (hm1 : ∀ i, P₁.map (fun T => T i) = (gLaw (Module.finrank ℝ G)).map (fun θ => lam i * θ))
    (hsum : ∀ᵐ T ∂P₁, ∑ i, T i = (∑ i, lam i) / 2) :
    IsJointMix (fun i => unifScaled (joinSet K₁ K₂) (t i) (lam i))
      ((P₁.prod (unifSeq.prod unifSeq)).map (stepJ Φ₁ Φ₂ lam t)) := by
  set a := Module.finrank ℝ G
  set S := (∑ i, lam i) / 2 with hS_def
  have hU₁ := unifSet_isProb h₁.pos h₁.fin
  have hU₂ := unifSet_isProb h₂.pos h₂.fin
  have hsum0 : 0 < ∑ i, lam i := by
    obtain ⟨i, hi⟩ := hne
    exact lt_of_lt_of_le ((hlam i).lt_of_ne hi.symm)
      (Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i))
  have hS0 : 0 < S := by positivity
  have hstep := measurable_stepJ hΦ₁ hΦ₂ lam t
  -- the good level vectors
  have hgood : ∀ᵐ T ∂P₁, (∀ i, 0 ≤ T i ∧ T i ≤ lam i) ∧ ∑ i, T i = S := by
    refine (ae_all_iff.2 fun i => ?_).and hsum
    have h : ∀ᵐ x ∂(gLaw a).map (fun θ => lam i * θ), 0 ≤ x ∧ x ≤ lam i := by
      rw [ae_map_iff (by fun_prop : Measurable fun θ : ℝ => lam i * θ).aemeasurable
        (show MeasurableSet {x : ℝ | 0 ≤ x ∧ x ≤ lam i} from
          measurableSet_Ici.inter measurableSet_Iic)]
      filter_upwards [gLaw_ae_mem a] with θ hθ
      exact ⟨mul_nonneg (hlam i) hθ.1, mul_le_of_le_one_right (hlam i) hθ.2⟩
    rw [← hm1 i] at h
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h
  -- the conditions for the fibres
  have hcond : ∀ T : Fin n → ℝ, ((∀ i, 0 ≤ T i ∧ T i ≤ lam i) ∧ ∑ i, T i = S) →
      ((∀ i, 0 ≤ lam i - T i) ∧ (∃ i, lam i - T i ≠ 0) ∧
        (∀ k, m₁ * (lam k - T k) ≤ ∑ i, (lam i - T i)) ∧ ∑ i, (lam i - T i) = S) ∧
      ((∀ i, 0 ≤ T i) ∧ (∃ i, T i ≠ 0) ∧ (∀ k, m₂ * T k ≤ ∑ i, T i)) := by
    rintro T ⟨hT, hTs⟩
    have hS' : ∑ i, (lam i - T i) = S := by
      rw [Finset.sum_sub_distrib, hTs, hS_def]; ring
    have hm : ∀ k, max m₁ m₂ * lam k ≤ S := fun k => by rw [hS_def]; linarith [hc k]
    refine ⟨⟨fun i => by linarith [(hT i).2], ?_, fun k => ?_, hS'⟩,
      ⟨fun i => (hT i).1, ?_, fun k => ?_⟩⟩
    · by_contra h
      push Not at h
      have : ∑ i, (lam i - T i) = 0 := Finset.sum_eq_zero fun i _ => h i
      linarith
    · rw [hS']
      rcases le_or_gt 0 m₁ with h0 | h0
      · have := mul_le_mul_of_nonneg_left (show lam k - T k ≤ lam k by linarith [(hT k).1]) h0
        have := mul_le_mul_of_nonneg_right (le_max_left m₁ m₂) (hlam k)
        linarith [hm k]
      · nlinarith [(hT k).2]
    · by_contra h
      push Not at h
      have : ∑ i, T i = 0 := Finset.sum_eq_zero fun i _ => h i
      linarith
    · rw [hTs]
      rcases le_or_gt 0 m₂ with h0 | h0
      · have := mul_le_mul_of_nonneg_left (hT k).2 h0
        have := mul_le_mul_of_nonneg_right (le_max_right m₁ m₂) (hlam k)
        linarith [hm k]
      · nlinarith [(hT k).1]
  have hW1 : ∀ T : Fin n → ℝ, ((∀ i, 0 ≤ T i ∧ T i ≤ lam i) ∧ ∑ i, T i = S) →
      IsJointMix (fun i => (unifSet K₁).map (fun x => (lam i - T i) • x))
        (unifSeq.map (Φ₁ (fun j => lam j - T j, 0))) := by
    intro T hT
    obtain ⟨⟨c1, c2, c3, -⟩, -⟩ := hcond T hT
    simpa using hmix₁ (fun j => lam j - T j) c1 c2 c3
  have hW2 : ∀ T : Fin n → ℝ, ((∀ i, 0 ≤ T i ∧ T i ≤ lam i) ∧ ∑ i, T i = S) →
      IsJointMix (fun i => (unifSet K₂).map (fun x => T i • x)) (unifSeq.map (Φ₂ (T, 0))) := by
    intro T hT
    obtain ⟨-, c1, c2, c3⟩ := hcond T hT
    simpa using hmix₂ T c1 c2 c3
  have cB_int : ∀ (K : Set G), Good K → ∀ c : ℝ,
      Integrable id ((unifSet K).map (fun x => c • x)) := fun K hK c => by
    rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
    exact hK.integrable.smul c
  have cB_mean : ∀ (K : Set G) (c : ℝ), ∫ y, y ∂(unifSet K).map (fun x => c • x) =
      c • ∫ y, y ∂unifSet K := fun K c => by
    rw [show ∫ y, y ∂(unifSet K).map (fun x => c • x) = ∫ x, c • x ∂unifSet K from
      integral_map (by fun_prop : Measurable fun x : G => c • x).aemeasurable
        aestronglyMeasurable_id, integral_smul]
  refine ⟨inferInstance, ⟨∑ i, t i + (S, (S • ∫ y, y ∂unifSet K₁, S • ∫ y, y ∂unifSet K₂)),
    ?_⟩, fun i => ?_⟩
  · -- constant sum
    rw [ae_map_iff hstep.aemeasurable (measurableSet_sum_eq' _)]
    refine (Measure.ae_prod_iff_ae_ae (p := fun z => ∑ j, stepJ Φ₁ Φ₂ lam t z j = _)
      (hstep (measurableSet_sum_eq' _))).2 ?_
    filter_upwards [hgood] with T hT
    obtain ⟨⟨-, -, -, hS'⟩, -⟩ := hcond T hT
    obtain ⟨-, ⟨s1, hs1⟩, -⟩ := hW1 T hT
    obtain ⟨-, ⟨s2, hs2⟩, -⟩ := hW2 T hT
    have hs1_eq : s1 = S • ∫ y, y ∂unifSet K₁ := by
      rw [IsJointMix.sum_eq_integral (hW1 T hT) (fun i => cB_int K₁ h₁ _) hs1]
      simp_rw [cB_mean, ← Finset.sum_smul, hS']
    have hs2_eq : s2 = S • ∫ y, y ∂unifSet K₂ := by
      rw [IsJointMix.sum_eq_integral (hW2 T hT) (fun i => cB_int K₂ h₂ _) hs2]
      simp_rw [cB_mean, ← Finset.sum_smul, hT.2]
    have hs1' := (ae_map_iff (hΦ₁.comp measurable_prodMk_left).aemeasurable
      (measurableSet_sum_eq' s1)).1 hs1
    have hs2' := (ae_map_iff (hΦ₂.comp measurable_prodMk_left).aemeasurable
      (measurableSet_sum_eq' s2)).1 hs2
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs1',
      Measure.quasiMeasurePreserving_snd.ae hs2'] with ω hω1 hω2
    simp only [Function.comp_apply, Function.uncurry_apply_pair] at hω1 hω2
    simp only [stepJ, Finset.sum_add_distrib]
    congr 1
    simp only [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
    exact ⟨hT.2, by rw [hω1, hs1_eq], by rw [hω2, hs2_eq]⟩
  · -- marginals
    show _ = unifScaled (joinSet K₁ K₂) (t i) (lam i)
    rw [unifScaled_joinSet h₁ h₂]
    ext C hC
    have hA : MeasurableSet (stepJ Φ₁ Φ₂ lam t ⁻¹' ((fun x : Fin n → ℝ × (G × G) => x i) ⁻¹' C)) :=
      hstep ((measurable_pi_apply i) hC)
    have hjm : Measurable (fun p : ℝ × (G × G) => t i + lam i • joinMap p) :=
      measurable_const.add (measurable_joinMap.const_smul (lam i))
    set A' : Set (ℝ × (G × G)) :=
      {p | t i + (p.1, ((lam i - p.1) • p.2.1, p.1 • p.2.2)) ∈ C} with hA'
    have hA'm : MeasurableSet A' :=
      (by fun_prop : Measurable fun p : ℝ × (G × G) =>
        t i + (p.1, ((lam i - p.1) • p.2.1, p.1 • p.2.2))) hC
    set f : ℝ → ENNReal := fun x => ((unifSet K₁).prod (unifSet K₂)) (Prod.mk x ⁻¹' A')
      with hf
    have hfmeas : Measurable f := measurable_measure_prodMk_left hA'm
    rw [Measure.map_apply (measurable_pi_apply i) hC, Measure.map_apply hstep
      ((measurable_pi_apply i) hC), Measure.map_apply hjm hC,
      Measure.prod_apply hA, Measure.prod_apply (hjm hC)]
    have h1 : ∀ᵐ T ∂P₁, (unifSeq.prod unifSeq) (Prod.mk T ⁻¹' ((stepJ Φ₁ Φ₂ lam t) ⁻¹'
        ((fun x : Fin n → ℝ × (G × G) => x i) ⁻¹' C))) = f (T i) := by
      filter_upwards [hgood] with T hT
      obtain ⟨-, -, hW1m⟩ := hW1 T hT
      obtain ⟨-, -, hW2m⟩ := hW2 T hT
      have hΦ1m : Measurable (Φ₁ (fun j => lam j - T j, 0)) := hΦ₁.comp measurable_prodMk_left
      have hΦ2m : Measurable (Φ₂ (T, 0)) := hΦ₂.comp measurable_prodMk_left
      have hu : Measurable (fun ω => Φ₁ (fun j => lam j - T j, 0) ω i) :=
        (measurable_pi_apply i).comp hΦ1m
      have hv : Measurable (fun ω => Φ₂ (T, 0) ω i) := (measurable_pi_apply i).comp hΦ2m
      have hset : MeasurableSet {y : G × G | t i + (T i, y) ∈ C} :=
        (measurable_const.add (measurable_const.prodMk measurable_id)) hC
      have e1 : Prod.mk T ⁻¹' ((stepJ Φ₁ Φ₂ lam t) ⁻¹'
          ((fun x : Fin n → ℝ × (G × G) => x i) ⁻¹' C)) =
          (Prod.map (fun ω => Φ₁ (fun j => lam j - T j, 0) ω i) (fun ω => Φ₂ (T, 0) ω i)) ⁻¹'
            {y | t i + (T i, y) ∈ C} := by
        ext ω; exact Iff.rfl
      have hl1 : unifSeq.map (fun ω => Φ₁ (fun j => lam j - T j, 0) ω i) =
          (unifSet K₁).map (fun x => (lam i - T i) • x) := by
        have := hW1m i; rwa [Measure.map_map (measurable_pi_apply i) hΦ1m] at this
      have hl2 : unifSeq.map (fun ω => Φ₂ (T, 0) ω i) = (unifSet K₂).map (fun x => T i • x) := by
        have := hW2m i; rwa [Measure.map_map (measurable_pi_apply i) hΦ2m] at this
      rw [e1, ← Measure.map_apply (hu.prodMap hv) hset, ← Measure.map_prod_map _ _ hu hv, hl1,
        hl2, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
        Measure.map_apply (by fun_prop) hset]
      rfl
    rw [lintegral_congr_ae h1]
    rw [show (∫⁻ T, f (T i) ∂P₁) = ∫⁻ x, f x ∂P₁.map (fun T => T i) from
      (lintegral_map hfmeas (measurable_pi_apply i)).symm, hm1 i,
      lintegral_map hfmeas (by fun_prop)]
    refine lintegral_congr fun θ => ?_
    simp only [hf]
    congr 1
    ext ⟨u, v⟩
    simp only [hA', mem_preimage, mem_ofPred_eq, joinMap, Prod.smul_mk, smul_eq_mul, smul_smul]
    rw [show lam i * (1 - θ) = lam i - lam i * θ by ring]

end Fibres

/-! ### Lemma 59: the construction and the scaling property of the join -/

section JoinMix

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure] {n : ℕ}

/-- The levels of Lemma 59 from a uniform sequence `ω`, split into `ω₁, ω₂`: `w = f(ω₁ 0)` (a
sampler of `wLaw a`) and `z = Φ_seg (λ, 0) ω₂` (Lemma 1 for `[-λᵢ, λᵢ]`), `Lᵢ = λᵢ/2 + w zᵢ`. -/
def levelSample (Φs : (Fin n → ℝ) × (Fin n → (Fin 1 → ℝ)) → (ℕ → ℝ) → (Fin n → (Fin 1 → ℝ)))
    (fw : ℝ → ℝ) (lam : Fin n → ℝ) (ω : ℕ → ℝ) : Fin n → ℝ :=
  levelOf lam (fw ((splitSeq ω).1 0), fun i => Φs (lam, 0) (splitSeq ω).2 i 0)

/-- **The construction of Lemma 59**: levels `L = levelSample ω₁`, then
`Xᵢ = tᵢ + (Lᵢ, Uᵢ, Vᵢ)` with `U = Φ₁ (λ - L, 0) ω₃`, `V = Φ₂ (L, 0) ω₄`, where `ω₁` and
`(ω₃, ω₄)` are independent parts of the uniform sequence `ω`. -/
def joinMix (Φs : (Fin n → ℝ) × (Fin n → (Fin 1 → ℝ)) → (ℕ → ℝ) → (Fin n → (Fin 1 → ℝ)))
    (fw : ℝ → ℝ) (Φ₁ Φ₂ : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G))
    (p : (Fin n → ℝ) × (Fin n → ℝ × (G × G))) (ω : ℕ → ℝ) : Fin n → ℝ × (G × G) :=
  stepJ Φ₁ Φ₂ p.1 p.2 (levelSample Φs fw p.1 (splitSeq ω).1, splitSeq (splitSeq ω).2)

omit [(volume : Measure G).IsAddHaarMeasure] in
lemma measurable_joinMix
    {Φs : (Fin n → ℝ) × (Fin n → (Fin 1 → ℝ)) → (ℕ → ℝ) → (Fin n → (Fin 1 → ℝ))}
    {fw : ℝ → ℝ} {Φ₁ Φ₂ : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΦs : Measurable (Function.uncurry Φs)) (hfw : Measurable fw)
    (hΦ₁ : Measurable (Function.uncurry Φ₁)) (hΦ₂ : Measurable (Function.uncurry Φ₂)) :
    Measurable (Function.uncurry (joinMix Φs fw Φ₁ Φ₂)) := by
  have hs1 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      splitSeq (splitSeq q.2).1) := measurable_splitSeq.comp
        (measurable_fst.comp (measurable_splitSeq.comp measurable_snd))
  have hs2 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      splitSeq (splitSeq q.2).2) := measurable_splitSeq.comp
        (measurable_snd.comp (measurable_splitSeq.comp measurable_snd))
  have hl : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hz : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      Φs (q.1.1, 0) (splitSeq (splitSeq q.2).1).2) :=
    hΦs.comp (f := fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      ((q.1.1, 0), (splitSeq (splitSeq q.2).1).2)) ((hl.prodMk measurable_const).prodMk
        (measurable_snd.comp hs1))
  have hw : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      fw ((splitSeq (splitSeq q.2).1).1 0)) :=
    hfw.comp ((measurable_pi_apply 0).comp (measurable_fst.comp hs1))
  have hT : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      levelSample Φs fw q.1.1 (splitSeq q.2).1) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (((measurable_pi_apply i).comp hl).div_const 2).add
      (hw.mul ((measurable_pi_apply 0).comp ((measurable_pi_apply i).comp hz)))
  have h1 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      Φ₁ (fun j => q.1.1 j - levelSample Φs fw q.1.1 (splitSeq q.2).1 j, 0)
        (splitSeq (splitSeq q.2).2).1) :=
    hΦ₁.comp (f := fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      ((fun j => q.1.1 j - levelSample Φs fw q.1.1 (splitSeq q.2).1 j, 0),
        (splitSeq (splitSeq q.2).2).1))
      (((measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp hl).sub
        ((measurable_pi_apply j).comp hT)).prodMk measurable_const).prodMk
        (measurable_fst.comp hs2))
  have h2 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      Φ₂ (levelSample Φs fw q.1.1 (splitSeq q.2).1, 0) (splitSeq (splitSeq q.2).2).2) :=
    hΦ₂.comp (f := fun q : ((Fin n → ℝ) × (Fin n → ℝ × (G × G))) × (ℕ → ℝ) =>
      ((levelSample Φs fw q.1.1 (splitSeq q.2).1, 0), (splitSeq (splitSeq q.2).2).2))
      ((hT.prodMk measurable_const).prodMk (measurable_snd.comp hs2))
  refine measurable_pi_iff.2 fun i => ?_
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
    (((measurable_pi_apply i).comp hT).prodMk
      (((measurable_pi_apply i).comp h1).prodMk ((measurable_pi_apply i).comp h2)))

lemma unifSeq_map_eval_zero : unifSeq.map (fun ω : ℕ → ℝ => ω 0) = unifI 0 1 :=
  Measure.infinitePi_map_eval _ 0

/-- **Lemma 59** (`b:lem:join`), the construction: given Lemma 1 for centred intervals (the
scaling property of the segment, `Φs`), a sampler `fw` of `wLaw a`, and the Borel constructions
`Φ₁, Φ₂` of the scaling properties of `K₁` and `K₂` with constants `m₁, m₂`, the construction
`joinMix` of the paper gives a joint mix of the `U(tᵢ + λᵢ J)` whenever `λ ≥ 0`, not all zero,
`2 m maxᵢ λᵢ ≤ ∑ λᵢ` with `m = max m₁ m₂ ≥ 1`. -/
theorem joinMix_isJointMix {K₁ K₂ : Set G} (h₁ : Good K₁) (h₂ : Good K₂) {m₁ m₂ : ℝ}
    (hm : 1 ≤ max m₁ m₂)
    {Φs : (Fin n → ℝ) × (Fin n → (Fin 1 → ℝ)) → (ℕ → ℝ) → (Fin n → (Fin 1 → ℝ))}
    (hΦs : Measurable (Function.uncurry Φs))
    (hmixs : ∀ (lam : Fin n → ℝ) (t : Fin n → (Fin 1 → ℝ)), (∀ i, 0 ≤ lam i) →
      (∃ i, lam i ≠ 0) → (∀ k, 2 * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => unifScaled (eBall 1) (t i) (lam i)) (unifSeq.map (Φs (lam, t))))
    {fw : ℝ → ℝ} (hfw : Measurable fw)
    (hfwmap : (unifI 0 1).map fw = wLaw (Module.finrank ℝ G))
    {Φ₁ Φ₂ : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΦ₁ : Measurable (Function.uncurry Φ₁)) (hΦ₂ : Measurable (Function.uncurry Φ₂))
    (hmix₁ : ∀ (σ : Fin n → ℝ) (t : Fin n → G), (∀ i, 0 ≤ σ i) → (∃ i, σ i ≠ 0) →
      (∀ k, m₁ * σ k ≤ ∑ i, σ i) →
      IsJointMix (fun i => (unifSet K₁).map (fun x => t i + σ i • x))
        (unifSeq.map (Φ₁ (σ, t))))
    (hmix₂ : ∀ (σ : Fin n → ℝ) (t : Fin n → G), (∀ i, 0 ≤ σ i) → (∃ i, σ i ≠ 0) →
      (∀ k, m₂ * σ k ≤ ∑ i, σ i) →
      IsJointMix (fun i => (unifSet K₂).map (fun x => t i + σ i • x))
        (unifSeq.map (Φ₂ (σ, t))))
    (lam : Fin n → ℝ) (t : Fin n → ℝ × (G × G)) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0) (hc : ∀ k, 2 * max m₁ m₂ * lam k ≤ ∑ i, lam i) :
    IsJointMix (fun i => unifScaled (joinSet K₁ K₂) (t i) (lam i))
      (unifSeq.map (joinMix Φs fw Φ₁ Φ₂ (lam, t))) := by
  set a := Module.finrank ℝ G
  have hΦsl : Measurable (Φs (lam, 0)) := hΦs.comp measurable_prodMk_left
  have hZf : Measurable (fun ω : ℕ → ℝ => fun i => Φs (lam, 0) ω i 0) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply 0).comp
      ((measurable_pi_apply i).comp hΦsl)
  set ZP := unifSeq.map (fun ω : ℕ → ℝ => fun i => Φs (lam, 0) ω i 0) with hZP
  -- the joint mix of the `U[-λᵢ, λᵢ]`
  have hZ : IsJointMix (fun i => (unifI (-1) 1).map (fun z => lam i * z)) ZP := by
    have h2 : ∀ k, 2 * lam k ≤ ∑ i, lam i := fun k => by
      have := mul_le_mul_of_nonneg_right hm (hlam k)
      linarith [hc k]
    have h := (hmixs lam 0 hlam hne h2).map_add_hom
      (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0) (measurable_pi_apply 0) 0
    simp only [Pi.evalAddMonoidHom_apply, Pi.zero_apply, zero_add] at h
    have hlaw : ∀ i, (unifScaled (eBall 1) 0 (lam i)).map (fun x => x 0) =
        (unifI (-1) 1).map (fun z => lam i * z) := by
      intro i
      rw [unifScaled_eq_map (good_eBall 1).pos (good_eBall 1).fin,
        Measure.map_map (by fun_prop) (by fun_prop), ← unifSet_eBall_one_map,
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      simp
    simp only [hlaw] at h
    convert h using 1
    rw [hZP, Measure.map_map (by fun_prop) hΦsl]
    rfl
  obtain ⟨hP₁, hsum⟩ := isJointMix_levels a lam hZ
  have e : levelSample Φs fw lam = levelOf lam ∘
      Prod.map (fun ω : ℕ → ℝ => fw (ω 0)) (fun ω : ℕ → ℝ => fun i => Φs (lam, 0) ω i 0) ∘
        splitSeq := rfl
  have hw0 : Measurable (fun ω : ℕ → ℝ => fw (ω 0)) := hfw.comp (measurable_pi_apply 0)
  have hTm : Measurable (levelSample Φs fw lam) := by
    rw [e]
    exact (measurable_levelOf lam).comp ((hw0.prodMap hZf).comp measurable_splitSeq)
  -- the law of the levels
  have hlev : unifSeq.map (levelSample Φs fw lam) = ((wLaw a).prod ZP).map (levelOf lam) := by
    rw [e, ← Measure.map_map (measurable_levelOf lam) ((hw0.prodMap hZf).comp measurable_splitSeq),
      ← Measure.map_map (hw0.prodMap hZf) measurable_splitSeq, map_splitSeq,
      ← Measure.map_prod_map _ _ hw0 hZf, ← hfwmap, ← unifSeq_map_eval_zero,
      Measure.map_map hfw (measurable_pi_apply 0)]
    rfl
  -- the law of the whole construction
  have e2 : unifSeq.map (joinMix Φs fw Φ₁ Φ₂ (lam, t)) =
      ((unifSeq.map (levelSample Φs fw lam)).prod (unifSeq.prod unifSeq)).map
        (stepJ Φ₁ Φ₂ lam t) := by
    have e' : joinMix Φs fw Φ₁ Φ₂ (lam, t) =
        stepJ Φ₁ Φ₂ lam t ∘ Prod.map (levelSample Φs fw lam) splitSeq ∘ splitSeq := rfl
    rw [e', ← Measure.map_map (measurable_stepJ hΦ₁ hΦ₂ lam t)
        ((hTm.prodMap measurable_splitSeq).comp measurable_splitSeq),
      ← Measure.map_map (hTm.prodMap measurable_splitSeq) measurable_splitSeq, map_splitSeq,
      ← Measure.map_prod_map _ _ hTm measurable_splitSeq, map_splitSeq]
  rw [e2]
  rw [← hlev] at hP₁ hsum
  have := hP₁.1
  exact isJointMix_stepJ h₁ h₂ hΦ₁ hΦ₂ (fun σ c1 c2 c3 => hmix₁ σ 0 c1 c2 c3)
    (fun σ c1 c2 c3 => hmix₂ σ 0 c1 c2 c3) lam t hlam hne hc hP₁.2.2 hsum

/-- **Lemma 59** (`b:lem:join`): if `K₁, K₂ ⊆ G` (of dimension `a = dim G`) have the scaling
property with constants `m₁, m₂`, with `m = max m₁ m₂ ≥ 1`, then the join `J(K₁, K₂)` has the
scaling property with constant `2m`. It uses Lemma 1 for the centred intervals `[-λᵢ, λᵢ]`, in
the form of the scaling property of the segment (`hseg`, Theorem 51 with `j = 1`). -/
theorem join_scalingProperty (hseg : ScalingPropertySet (eBall 1) 2) {K₁ K₂ : Set G}
    (h₁ : Good K₁) (h₂ : Good K₂) {m₁ m₂ : ℝ} (hs₁ : ScalingPropertySet K₁ m₁)
    (hs₂ : ScalingPropertySet K₂ m₂) (hm : 1 ≤ max m₁ m₂) :
    ScalingPropertySet (joinSet K₁ K₂) (2 * max m₁ m₂) := by
  intro n hn
  obtain ⟨Φs, hΦs, hmixs⟩ := hseg n hn
  obtain ⟨Φ₁, hΦ₁, hmix₁⟩ := (scalingPropertySet_iff h₁.pos h₁.fin m₁).1 hs₁ n hn
  obtain ⟨Φ₂, hΦ₂, hmix₂⟩ := (scalingPropertySet_iff h₂.pos h₂.fin m₂).1 hs₂ n hn
  obtain ⟨fw, hfw, hfwmap⟩ := exists_sampler (wLaw (Module.finrank ℝ G))
  refine ⟨joinMix Φs fw Φ₁ Φ₂, measurable_joinMix hΦs hfw hΦ₁ hΦ₂,
    fun lam t hlam hne hc => ?_⟩
  exact joinMix_isJointMix h₁ h₂ hm hΦs hmixs hfw hfwmap hΦ₁ hΦ₂ hmix₁ hmix₂ lam t hlam hne
    fun k => by have := hc k; linarith

/-- **Finding** (edge case of Lemma 59): the hypothesis `m ≥ 1` is needed. Points have the
scaling property with every constant (`scaling_point`), in particular with `m₁ = m₂ = 0`, but the
join of two points, a segment, does not have the scaling property with constant `2m = 0`:
for `n = 2`, `λ = (1, 0)`, a joint mix of `U(J)` and a point mass would make `U(J)` a point
mass. -/
theorem join_points_not_scaling :
    ¬ ScalingPropertySet (joinSet (univ : Set (Fin 0 → ℝ)) univ) (2 * max 0 0) := by
  intro h
  obtain ⟨Φ, -, hmix⟩ := h 2 le_rfl
  have hJ := good_joinSet good_point good_point
  have := isAddHaar_joinSpace (G := Fin 0 → ℝ)
  obtain ⟨hP, ⟨s, hs⟩, hm⟩ := hmix ![1, 0] 0 (fun i => by fin_cases i <;> simp)
    ⟨0, by simp⟩ (fun k => by simp)
  set P := unifSeq.map (Φ (![1, 0], 0))
  have h0 : P.map (fun x => x 0) = unifSet (joinSet (univ : Set (Fin 0 → ℝ)) univ) := by
    rw [hm 0]
    simp only [Pi.zero_apply, Matrix.cons_val_zero]
    rw [unifScaled_eq_map hJ.pos hJ.fin]
    simp
  have h1 : P.map (fun x => x 1) = Measure.dirac 0 := by
    rw [hm 1]
    simp [unifScaled]
  have hx1 : ∀ᵐ x ∂P, x 1 = 0 := by
    have : ∀ᵐ y ∂P.map (fun x => x 1), y = (0 : ℝ × ((Fin 0 → ℝ) × (Fin 0 → ℝ))) := by
      rw [h1]; exact (ae_dirac_iff (measurableSet_singleton _)).2 rfl
    exact ae_of_ae_map (measurable_pi_apply 1).aemeasurable this
  have hx0 : ∀ᵐ y ∂P.map (fun x => x 0), y = s := by
    rw [ae_map_iff (by fun_prop : Measurable fun x : Fin 2 → ℝ × ((Fin 0 → ℝ) × (Fin 0 → ℝ)) =>
      x 0).aemeasurable (show MeasurableSet {y : ℝ × ((Fin 0 → ℝ) × (Fin 0 → ℝ)) | y = s} from
        measurableSet_singleton s)]
    filter_upwards [hs, hx1] with x hx hx1'
    simp only [Fin.sum_univ_two, hx1', add_zero] at hx
    exact hx
  rw [h0] at hx0
  have := unifSet_isProb hJ.pos hJ.fin
  have hnull : unifSet (joinSet (univ : Set (Fin 0 → ℝ)) univ) {s}ᶜ = 0 := by
    exact ae_iff.1 hx0
  have hpt : unifSet (joinSet (univ : Set (Fin 0 → ℝ)) univ) {s} = 0 := by
    rw [unifSet, smul_apply, Measure.restrict_apply (measurableSet_singleton s), smul_eq_mul]
    have : volume ({s} : Set (ℝ × ((Fin 0 → ℝ) × (Fin 0 → ℝ)))) = 0 := by
      rw [← Set.singleton_prod_singleton, Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_singleton, zero_mul]
    rw [measure_mono_null inter_subset_left this, mul_zero]
  have := measure_univ (μ := unifSet (joinSet (univ : Set (Fin 0 → ℝ)) univ))
  rw [← Set.union_compl_self {s}] at this
  have := (measure_union_le (μ := unifSet (joinSet (univ : Set (Fin 0 → ℝ)) univ)) {s} {s}ᶜ)
  simp_all

end JoinMix

/-! ### Definition 60 and Theorem 61 -/

section Class

/-- **Definition 60** (`b:def:class`), for the full-dimensional members: `InK d K` says that
`K ⊆ ℝ^d` (as `Fin d → ℝ`), of dimension `d`, is generated from the points (`d = 0`) and the
closed balls of dimension `j ≥ 1` by
(i) bijective affine maps of `ℝ^d` (images under injective affine maps into larger spaces are
handled at the level of measures, see `classK_scalingProperty_map`);
(ii) Cartesian products, `ℝ^{d₁} × ℝ^{d₂} = ℝ^{d₁+d₂}` by concatenation;
(iii) frusta `K_q` (`0 ≤ q < 1`) over a base `F = {1} × B` with `B ⊆ ℝ^m` in the class, in
the coordinates `(s, y) ∈ ℝ × ℝ^m` (`frustumSet`, the hyperplane `ℓ = 1` being `s = 1`); any
other hyperplane `{ℓ = 1}` and base are a bijective linear image of this one;
(iv) joins of equal dimension, `J(K₁, K₂) ⊆ ℝ × ℝ^a × ℝ^a = ℝ^{2a+1}` in the coordinates
`(θ, x, y)` (`joinSet`). -/
inductive InK : (d : ℕ) → Set (Fin d → ℝ) → Prop
  | point : InK 0 univ
  | ball (j : ℕ) (hj : 1 ≤ j) : InK j (eBall j)
  | affine {d : ℕ} {K : Set (Fin d → ℝ)} (M : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      (hM : LinearMap.det M ≠ 0) (b : Fin d → ℝ) : InK d K → InK d ((fun x => M x + b) '' K)
  | prod {d₁ d₂ : ℕ} {K₁ : Set (Fin d₁ → ℝ)} {K₂ : Set (Fin d₂ → ℝ)} :
      InK d₁ K₁ → InK d₂ K₂ → InK (d₁ + d₂) (eProd d₁ d₂ '' K₁ ×ˢ K₂)
  | frustum {m : ℕ} {B : Set (Fin m → ℝ)} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
      InK m B → InK (m + 1) (eFr m '' frustumSet q B)
  | join {a : ℕ} {K₁ K₂ : Set (Fin a → ℝ)} :
      InK a K₁ → InK a K₂ → InK (a + a + 1) (eJ a '' joinSet K₁ K₂)

/-- The induction of Theorem 61, with the regularity it needs. -/
theorem good_and_scaling (h51 : Thm51Ball)
    (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {d : ℕ}
    {K : Set (Fin d → ℝ)} (hK : InK d K) : Good K ∧ ScalingPropertySet K ((d : ℝ) + 1) := by
  induction hK with
  | point => exact ⟨good_point, scaling_point _⟩
  | ball j hj =>
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    exact ⟨good_eBall j, ScalingPropertySet.mono (h51 j hj) (by linarith)⟩
  | affine M hM b _ ih =>
    exact ⟨good_affine ih.1 M hM b, scalingPropertySet_image_affine ih.1.pos ih.1.fin ih.2 hM b⟩
  | @prod d₁ d₂ K₁ K₂ _ _ ih₁ ih₂ =>
    have : (volume : Measure ((Fin d₁ → ℝ) × (Fin d₂ → ℝ))).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]; infer_instance
    have hs := scalingPropertySet_prod ih₁.1.pos ih₁.1.fin ih₂.1.pos ih₂.1.fin ih₁.2 ih₂.2
    have h0 : (0 : ℝ) ≤ d₁ := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ d₂ := Nat.cast_nonneg _
    refine transport (eProd d₁ d₂) (eProd_mp d₁ d₂) (eProd_lin d₁ d₂) (good_prod ih₁.1 ih₂.1)
      (ScalingPropertySet.mono hs ?_)
    push_cast
    exact max_le (by linarith) (by linarith)
  | @frustum m B q hq0 hq1 _ ih =>
    have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]; infer_instance
    obtain ⟨hg, hs⟩ := frustum_step h27 hq0 hq1 ih.1 ih.2
    exact transport (eFr m) (eFr_mp m) (eFr_lin m) hg hs
  | @join a K₁ K₂ _ _ ih₁ ih₂ =>
    have := isAddHaar_joinSpace (G := Fin a → ℝ)
    have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have hs := join_scalingProperty (h51 1 le_rfl) ih₁.1 ih₂.1 ih₁.2 ih₂.2
      (by rw [max_self]; linarith)
    refine transport (eJ a) (eJ_mp a) (eJ_lin a) (good_joinSet ih₁.1 ih₂.1)
      (ScalingPropertySet.mono hs ?_)
    push_cast
    rw [max_self]
    linarith

/-- **Theorem 61** (`b:thm:class`), main statement: given Theorem 51 for balls (`Thm51Ball`) and
Theorem 27 for the level laws of frusta (`Thm27Frustum`), every `K ∈ 𝒦` of dimension `d` has the
scaling property with constant `d + 1`, with the explicit Borel construction obtained by
composing those of Lemmas 48, 53, 59 and Theorems 51, 56. -/
theorem classK_scalingProperty (h51 : Thm51Ball)
    (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {d : ℕ}
    {K : Set (Fin d → ℝ)} (hK : InK d K) : ScalingPropertySet K ((d : ℝ) + 1) :=
  (good_and_scaling h51 h27 hK).2

/-- Members of `𝒦` of lower dimension: for `K ∈ 𝒦` of dimension `d` and an affine map
`x ↦ A x + b` into any space (injective in Definition 60), the uniform distribution
`U(A K + b) = U(K).map (A · + b)` has the scaling property with constant `d + 1` (Lemma 48 at
the level of measures). -/
theorem classK_scalingProperty_map (h51 : Thm51Ball)
    (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {d : ℕ}
    {K : Set (Fin d → ℝ)} (hK : InK d K) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (A : (Fin d → ℝ) →L[ℝ] F)
    (b : F) : ScalingProperty ((unifSet K).map (fun x => A x + b)) ((d : ℝ) + 1) := by
  obtain ⟨hg, hs⟩ := good_and_scaling h51 h27 hK
  exact scalingProperty_map_affine ((scalingPropertySet_iff hg.pos hg.fin _).1 hs) A b

/-- Two probability measures on a subsingleton space agree. -/
lemma prob_eq_of_subsingleton {E : Type*} [MeasurableSpace E] [Subsingleton E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext S hS
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  · have hS' : S = univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    simp [hS']

/-- On `ℝ^0` all probability measures are jointly mixable (`n ≥ 1`). -/
lemma jointlyMixable_dim_zero {n : ℕ} (F : Fin n → Measure (Fin 0 → ℝ))
    [∀ i, IsProbabilityMeasure (F i)] : JointlyMixable F := by
  refine ⟨Measure.dirac 0, inferInstance,
    ⟨0, Filter.Eventually.of_forall fun x => Subsingleton.elim _ _⟩, fun i => ?_⟩
  have : IsProbabilityMeasure ((Measure.dirac (0 : Fin n → Fin 0 → ℝ)).map fun x => x i) :=
    inferInstance
  exact prob_eq_of_subsingleton _ _

lemma unifScaled_isProb {d : ℕ} {K : Set (Fin d → ℝ)} (hK : Good K) (t : Fin d → ℝ) (r : ℝ) :
    IsProbabilityMeasure (unifScaled K t r) := by
  have := unifSet_isProb hK.pos hK.fin
  rw [unifScaled_eq_map hK.pos hK.fin]
  infer_instance

/-- **Theorem 61**, joint mixes: for `K ∈ 𝒦` of dimension `d`, `U(t₁ + λ₁K), …, U(tₙ + λₙK)` are
jointly mixable whenever `λ ≥ 0`, not all zero, and `(d + 1) maxᵢ λᵢ ≤ ∑ᵢ λᵢ`. -/
theorem classK_jointlyMixable (h51 : Thm51Ball)
    (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {d : ℕ}
    {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ} (lam : Fin n → ℝ) (t : Fin n → Fin d → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0) (hc : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => unifScaled K (t i) (lam i) := by
  obtain ⟨hg, hs⟩ := good_and_scaling h51 h27 hK
  rcases le_or_gt 2 n with hn | hn
  · obtain ⟨Φ, -, hmix⟩ := hs n hn
    exact ⟨_, hmix lam t hlam hne hc⟩
  · -- `n = 1`, hence `d = 0`
    obtain ⟨i, hi⟩ := hne
    have hn1 : n = 1 := by have := i.pos; omega
    subst hn1
    have hsum : ∑ j, lam j = lam i := by
      rw [Fin.sum_univ_one]; exact congrArg lam (Subsingleton.elim _ _)
    have hpos : 0 < lam i := (hlam i).lt_of_ne hi.symm
    have hd : d = 0 := by
      have := hc i
      rw [hsum] at this
      have h0 : (d : ℝ) ≤ 0 := by nlinarith
      exact_mod_cast le_antisymm h0 (Nat.cast_nonneg d)
    subst hd
    have := fun j => unifScaled_isProb hg (t j) (lam j)
    exact jointlyMixable_dim_zero _

/-- **Theorem 61**, complete mixes: for `K ∈ 𝒦` of dimension `d`, `U(K)` is `n`-completely
mixable for every `n ≥ d + 1`. -/
theorem classK_completelyMixable (h51 : Thm51Ball)
    (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {d : ℕ}
    {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ} (hn : d + 1 ≤ n) :
    CompletelyMixable n (unifSet K) := by
  have hg := (good_and_scaling h51 h27 hK).1
  have h := classK_jointlyMixable h51 h27 hK (fun _ : Fin n => 1) (fun _ => 0)
    (fun _ => zero_le_one) ⟨⟨0, by omega⟩, one_ne_zero⟩ (fun k => by
      simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact_mod_cast hn)
  have e : unifScaled K 0 1 = unifSet K := by
    rw [unifScaled_eq_map hg.pos hg.fin]
    simp
  simp only [e] at h
  exact h

/-- `ℝ × ℝ^m ≃ ℝ^{m+1}` as a linear equivalence. -/
def eFrL (m : ℕ) : (ℝ × (Fin m → ℝ)) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun := eFr m
  invFun := (eFr m).symm
  map_add' := (eFr_lin m).map_add
  map_smul' := (eFr_lin m).map_smul
  left_inv := (eFr m).symm_apply_apply
  right_inv := (eFr m).apply_symm_apply

/-- The cone over `{L⁻¹(1, b) : b ∈ B}` (Cone.lean) is the linear image of the frustum with
`q = 0`. -/
lemma coneSet_eq {m : ℕ} (L : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ × (Fin m → ℝ)) (B : Set (Fin m → ℝ)) :
    coneSet L B = L.symm '' frustumSet 0 B := by
  ext x
  simp only [coneSet, coneBase, frustumSet, mem_image, mem_Icc, mem_ofPred_eq]
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, y, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨(s, s • b), ⟨hs0, hs1, b, hb, rfl⟩, ?_⟩
    rw [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one]
  · rintro ⟨⟨s, y⟩, ⟨hs0, hs1, b, hb, hy⟩, rfl⟩
    simp only at hs0 hs1 hy
    subst hy
    refine ⟨s, ⟨hs0, hs1⟩, _, ⟨b, hb, rfl⟩, ?_⟩
    rw [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one]

/-- **Theorem 61**, cones: if `K` is the cone over a member `F = L⁻¹({1} × B)` of `𝒦`
(`B ∈ 𝒦` of dimension `m`, so `K` has dimension `d = m + 1`), then `U(K)` is `n`-completely
mixable (`n ≥ 1`) if and only if `n ≥ d + 1`. The necessity is Theorem 43 (a). -/
theorem cone_completelyMixable_iff (h51 : Thm51Ball)
    (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q) {m : ℕ}
    {B : Set (Fin m → ℝ)} (hB : InK m B) (L : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ × (Fin m → ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (coneSet L B)) ↔ m + 1 + 1 ≤ n := by
  have hgB := (good_and_scaling h51 h27 hB).1
  constructor
  · intro h
    have e : scaledTranslate 0 1 (coneSet L B) = coneSet L B := by
      ext x; simp [scaledTranslate]
    rw [← e] at h
    have := cone_completelyMixable_le L hgB.meas hgB.pos hgB.fin 0 hn h
    omega
  · intro h
    let M : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) :=
      (eFrL m).symm.trans L.symm.toLinearEquiv
    have hM : LinearMap.det (M : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) ≠ 0 :=
      (LinearEquiv.isUnit_det' M).ne_zero
    have hK := InK.affine (M : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) hM 0
      (InK.frustum 0 le_rfl zero_lt_one hB)
    have e : (fun x => (M : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) x + 0) ''
        (eFr m '' frustumSet 0 B) = coneSet L B := by
      rw [coneSet_eq, image_image]
      congr 1
      funext p
      simp only [add_zero, LinearEquiv.coe_coe]
      show L.symm ((eFr m).symm (eFr m p)) = L.symm p
      rw [MeasurableEquiv.symm_apply_apply]
    rw [e] at hK
    exact classK_completelyMixable h51 h27 hK h

end Class

/-! ### Discharging `Thm51Ball` (Theorem 51 is proved in `Ball.lean`) -/

section Thm51

/-- The coordinates `EuclideanSpace ℝ (Fin j) ≃ (Fin j → ℝ)`. -/
def eEuc (j : ℕ) : EuclideanSpace ℝ (Fin j) ≃ᵐ (Fin j → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin j → ℝ)).symm

lemma eEuc_image_ball (j : ℕ) :
    eEuc j '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1 = eBall j := by
  rw [MeasurableEquiv.image_eq_preimage_symm]
  ext y
  simp only [eEuc, MeasurableEquiv.symm_symm, mem_preimage, mem_closedBall_zero_iff, eBall,
    mem_ofPred_eq, MeasurableEquiv.coe_toLp, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_one]

lemma good_euclideanBall (j : ℕ) : Good (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1) :=
  ⟨measurableSet_closedBall, (Metric.measure_closedBall_pos _ _ one_pos).ne',
    measure_closedBall_lt_top.ne, Metric.isBounded_closedBall⟩

/-- **Theorem 51** in the coordinates of this file (from `Ball.ball_scalingPropertySet`). -/
theorem thm51Ball : Thm51Ball := by
  intro j _
  have h := transport (eEuc j)
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin j))
    ⟨fun x y => rfl, fun c x => rfl⟩ (good_euclideanBall j) (Ball.ball_scalingPropertySet j)
  rw [eEuc_image_ball] at h
  exact h.2

/-- **Theorem 61**, scaling property, with Theorem 51 proved (only Theorem 27 assumed). -/
theorem classK_scalingProperty' (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q)
    {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) : ScalingPropertySet K ((d : ℝ) + 1) :=
  classK_scalingProperty thm51Ball h27 hK

/-- **Theorem 61**, joint mixes, with Theorem 51 proved (only Theorem 27 assumed). -/
theorem classK_jointlyMixable' (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q)
    {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ} (lam : Fin n → ℝ)
    (t : Fin n → Fin d → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (hc : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => unifScaled K (t i) (lam i) :=
  classK_jointlyMixable thm51Ball h27 hK lam t hlam hne hc

/-- **Theorem 61**, complete mixes, with Theorem 51 proved (only Theorem 27 assumed). -/
theorem classK_completelyMixable' (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q)
    {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ} (hn : d + 1 ≤ n) :
    CompletelyMixable n (unifSet K) :=
  classK_completelyMixable thm51Ball h27 hK hn

/-- **Theorem 61**, cones, with Theorem 51 proved (only Theorem 27 assumed). -/
theorem cone_completelyMixable_iff' (h27 : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → Thm27Frustum m q)
    {m : ℕ} {B : Set (Fin m → ℝ)} (hB : InK m B) (L : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ × (Fin m → ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (coneSet L B)) ↔ m + 1 + 1 ≤ n :=
  cone_completelyMixable_iff thm51Ball h27 hB L hn

end Thm51

end ClassK

end Mixes
