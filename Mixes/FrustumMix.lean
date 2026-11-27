import Mixes.Frustum
import Mixes.Bodies

/-!
# Frusta: slicing, necessity and sufficiency (Lemma 55, Theorem 56, Corollaries 57, 58)

Item M1f of the verification priorities (the algebra of Lemma 54 is in `Frustum.lean`).

## Setting

A frustum is formed in coordinates `ℝ × G`, with `G` a finite-dimensional real normed space of
dimension `m` carrying an additive Haar measure (so `k = m + 1`), the functional `ℓ = fst`, and
the base `F = {1} × B` with `B ⊆ G` measurable of finite positive volume:
`frustumSet q B = {s y : q ≤ s ≤ 1, y ∈ F} = {(s, s b) : q ≤ s ≤ 1, b ∈ B}`.
Every frustum of the paper is the image of such a set under a linear bijection (choose a basis
whose dual first vector is `ℓ`).

## Main results

* `unifSet_frustumSet`, `unifScaled_frustumSet`, `integral_levelLaw`: **Lemma 55** (the uniform
  distribution on `t + λ K_q` is the law of `t + λ (S, S b)`, `S ∼ levelLaw` with density
  `k s^{k-1}/(1-q^k)` on `[q, 1]` and mean `μ_{k,q}`, `b ∼ U(B)` independent).
* `frustum_level_necessity`: **Theorem 56 (a)**, the level condition (14).
* `frustum_sufficiency`, `frustum_scalingProperty`, `frustum_constant_le`: **Theorem 56 (b)**
  and its last sentence, with Theorem 27 for the level laws taken as the explicit hypothesis
  `Thm27Frustum` (existence and Borel dependence on `λ`).
* `tsimplex_necessity`, `tsimplex_completelyMixable_le` (unconditional), `simplex_scalingProperty`
  (Corollary 44 via Theorem 56 with `q = 0`), `tsimplex_jointlyMixable_iff`,
  `tsimplex_completelyMixable_iff`: **Corollary 57**.
* `pyramid_necessity`, `circCone_necessity`, `frustum_completelyMixable_le` (unconditional),
  `pyramid_jointlyMixable_iff`, `pyramid_completelyMixable_iff`, `circCone_sufficiency`,
  `circCone_completelyMixable_iff`: **Corollary 58**; sufficiency assumes Theorem 27 and the
  scaling property of the cube, resp. the ball, with constant `2`.
-/

open MeasureTheory Set Pointwise

noncomputable section

namespace Mixes

namespace FrustumMix

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure]

/-! ### The frustum and its slicing (Lemma 55) -/

/-- The frustum `K_q = {s y : q ≤ s ≤ 1, y ∈ {1} × B}` in coordinates `ℝ × G`. -/
def frustumSet (q : ℝ) (B : Set G) : Set (ℝ × G) :=
  {p | q ≤ p.1 ∧ p.1 ≤ 1 ∧ ∃ b ∈ B, p.2 = p.1 • b}

/-- The map `(s, b) ↦ (s, s b)`. -/
def frustumMap (p : ℝ × G) : ℝ × G := (p.1, p.1 • p.2)

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurable_frustumMap : Measurable (frustumMap : ℝ × G → ℝ × G) :=
  measurable_fst.prodMk (measurable_fst.smul measurable_snd)

/-- The unnormalised level measure `s^m ds` on `(q, 1]`. -/
def levelPre (m : ℕ) (q : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc q 1)).withDensity fun s => ENNReal.ofReal (s ^ m)

/-- The level law of Lemma 55 for `λ = 1`: density `k s^{k-1} / (1 - q^k)` on `[q, 1]`, with
`k = m + 1` (see `levelLaw_eq_withDensity`). -/
def levelLaw (m : ℕ) (q : ℝ) : Measure ℝ := (levelPre m q univ)⁻¹ • levelPre m q

lemma levelPre_univ (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    levelPre m q univ = ENNReal.ofReal ((1 - q ^ (m + 1)) / (m + 1)) := by
  rw [levelPre, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hq1.le, integral_pow]
    simp
  · exact (continuous_pow m).integrableOn_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact pow_nonneg (hq0.trans hs.1.le) m

lemma levelPre_univ_ne_zero (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    levelPre m q univ ≠ 0 := by
  rw [levelPre_univ m hq0 hq1, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : q ^ (m + 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  apply div_pos <;> [linarith; positivity]

lemma levelPre_univ_ne_top (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    levelPre m q univ ≠ ⊤ := by
  rw [levelPre_univ m hq0 hq1]; exact ENNReal.ofReal_ne_top

instance (m : ℕ) (q : ℝ) : SFinite (levelPre m q) := by unfold levelPre; infer_instance

lemma levelLaw_isProb (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    IsProbabilityMeasure (levelLaw m q) := by
  constructor
  rw [levelLaw, smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (levelPre_univ_ne_zero m hq0 hq1) (levelPre_univ_ne_top m hq0 hq1)]

/-- The set `{(s, y) : q < s ≤ 1, s⁻¹ y ∈ B}`, equal to the frustum up to a null set. -/
def frustumCore (q : ℝ) (B : Set G) : Set (ℝ × G) :=
  {p | p.1 ∈ Ioc q 1 ∧ p.1⁻¹ • p.2 ∈ B}

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurableSet_frustumCore {B : Set G} (hB : MeasurableSet B) (q : ℝ) :
    MeasurableSet (frustumCore q B) :=
  (measurable_fst measurableSet_Ioc).inter ((measurable_fst.inv.smul measurable_snd) hB)

/-- Fubini and the scaling of volume in `G`: Lebesgue measure on the frustum is the image of
`s^m ds ⊗ vol|_B` under `(s, b) ↦ (s, s b)`. -/
lemma volume_restrict_frustumCore {q : ℝ} (hq0 : 0 ≤ q) {B : Set G} (hB : MeasurableSet B) :
    volume.restrict (frustumCore q B) =
      ((levelPre (Module.finrank ℝ G) q).prod (volume.restrict B)).map frustumMap := by
  ext C hC
  have hC' : MeasurableSet (frustumMap ⁻¹' C) := measurable_frustumMap hC
  rw [Measure.restrict_apply hC, Measure.map_apply measurable_frustumMap hC,
    Measure.volume_eq_prod, Measure.prod_apply (hC.inter (measurableSet_frustumCore hB q)),
    Measure.prod_apply hC', levelPre,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (measurable_measure_prodMk_left hC')]
  have h1 : ∀ x : ℝ, volume (Prod.mk x ⁻¹' (C ∩ frustumCore q B)) =
      (Ioc q 1).indicator (fun x => volume {y : G | (x, y) ∈ C ∧ x⁻¹ • y ∈ B}) x := by
    intro x
    by_cases hx : x ∈ Ioc q 1
    · rw [indicator_of_mem hx]
      congr 1
      ext y
      simp only [mem_Ioc] at hx
      simp [frustumCore, hx]
    · rw [indicator_of_notMem hx]
      convert measure_empty (μ := (volume : Measure G))
      ext y
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
      simp only [frustumCore, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_Ioc,
        mem_empty_iff_false, iff_false]
      rintro ⟨_, ⟨h1, h2⟩, _⟩
      rcases hx with hx | hx <;> linarith
  rw [lintegral_congr h1, lintegral_indicator measurableSet_Ioc]
  refine setLIntegral_congr_fun measurableSet_Ioc ?_
  intro x hx
  have hx0 : 0 < x := hq0.trans_lt hx.1
  have hset : {y : G | (x, y) ∈ C ∧ x⁻¹ • y ∈ B} =
      x • (Prod.mk x ⁻¹' (frustumMap ⁻¹' C) ∩ B) := by
    ext y
    rw [mem_smul_set_iff_inv_smul_mem₀ hx0.ne']
    simp [frustumMap, smul_inv_smul₀ hx0.ne']
  simp only [Pi.mul_apply]
  rw [hset, Measure.addHaar_smul, Measure.restrict_apply' hB, abs_of_pos (pow_pos hx0 _)]

lemma frustumSet_ae_eq {q : ℝ} (hq0 : 0 ≤ q) (B : Set G) :
    frustumSet q B =ᵐ[volume] frustumCore q B := by
  have hsub : frustumCore q B ⊆ frustumSet q B := by
    rintro ⟨s, y⟩ ⟨⟨hs1, hs2⟩, hb⟩
    have hs0 : s ≠ 0 := (hq0.trans_lt hs1).ne'
    exact ⟨hs1.le, hs2, _, hb, (smul_inv_smul₀ hs0 y).symm⟩
  rw [ae_eq_set, sdiff_eq_empty.2 hsub, measure_empty]
  refine ⟨?_, rfl⟩
  refine measure_mono_null (t := {q} ×ˢ univ) ?_ ?_
  · rintro ⟨s, y⟩ ⟨⟨hs1, hs2, b, hb, hy⟩, hn⟩
    simp only at hs1 hs2 hy
    subst hy
    simp only [mem_prod, mem_singleton_iff, mem_univ, and_true]
    by_contra hsq
    have hs : q < s := lt_of_le_of_ne hs1 (Ne.symm hsq)
    have hs0 : s ≠ 0 := (hq0.trans_lt hs).ne'
    exact hn ⟨⟨hs, hs2⟩, by simpa [inv_smul_smul₀ hs0] using hb⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

/-- **Lemma 55** (`b:lem:frustum`), for `λ = 1` and `t = 0`: the uniform distribution on the
frustum is the law of `(S, S b)` with `S ∼ levelLaw` (density `k s^{k-1}/(1-q^k)` on `[q,1]`)
and `b ∼ U(B)` independent. In other words `S = ℓ(X)` has the level law and, given `S`, `X` is
uniform on `S F`. -/
theorem unifSet_frustumSet {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) :
    unifSet (frustumSet q B) =
      ((levelLaw (Module.finrank ℝ G) q).prod (unifSet B)).map frustumMap := by
  set m := Module.finrank ℝ G
  have hres : volume.restrict (frustumSet q B) =
      ((levelPre m q).prod (volume.restrict B)).map frustumMap := by
    rw [Measure.restrict_congr_set (frustumSet_ae_eq hq0 B), volume_restrict_frustumCore hq0 hB]
  have hvol : volume (frustumSet q B) = levelPre m q univ * volume B := by
    rw [← Measure.restrict_apply_univ, hres, Measure.map_apply measurable_frustumMap
      MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ]
  rw [unifSet, hres, hvol, levelLaw, unifSet, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.map_smul _ (measurable_frustumMap (G := G)).aemeasurable,
    ENNReal.mul_inv (Or.inl (levelPre_univ_ne_zero m hq0 hq1))
      (Or.inl (levelPre_univ_ne_top m hq0 hq1))]


/-! ### Properties of the level law -/

section Level

variable {m : ℕ} {q : ℝ}

lemma levelLaw_ac (m : ℕ) (q : ℝ) : levelLaw m q ≪ volume.restrict (Ioc q 1) :=
  (withDensity_absolutelyContinuous _ _).smul_left _

lemma levelLaw_ae_mem (m : ℕ) (q : ℝ) : ∀ᵐ s ∂levelLaw m q, s ∈ Ioc q 1 :=
  (levelLaw_ac m q).ae_le (ae_restrict_mem measurableSet_Ioc)

lemma levelLaw_pos_of_Ioo {a b : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hqa : q ≤ a) (hab : a < b)
    (hb1 : b ≤ 1) {T : Set ℝ} (hT : MeasurableSet T) (hsub : Ioo a b ⊆ T) :
    0 < levelLaw m q T := by
  rw [levelLaw, smul_apply, smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (levelPre_univ_ne_top m hq0 hq1)) ?_
  rw [levelPre, ne_eq, withDensity_apply_eq_zero (by fun_prop),
    Measure.restrict_apply' measurableSet_Ioc]
  intro h
  have hsub' : Ioo a b ⊆ ({x : ℝ | ENNReal.ofReal (x ^ m) ≠ 0} ∩ T) ∩ Ioc q 1 := by
    intro x hx
    have hx0 : 0 < x := hq0.trans_lt (hqa.trans_lt hx.1)
    refine ⟨⟨?_, hsub hx⟩, hqa.trans_lt hx.1, hx.2.le.trans hb1⟩
    simp only [mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have := measure_mono_null hsub' h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
  linarith

lemma levelLaw_Iio_pos (hq0 : 0 ≤ q) (hq1 : q < 1) {c : ℝ} (hc : q < c) :
    0 < levelLaw m q (Iio c) :=
  levelLaw_pos_of_Ioo hq0 hq1 le_rfl (lt_min hc hq1) (min_le_right _ _) measurableSet_Iio
    fun x hx => lt_of_lt_of_le hx.2 (min_le_left _ _)

lemma levelLaw_Ioi_pos (hq0 : 0 ≤ q) (hq1 : q < 1) {c : ℝ} (hc : c < 1) :
    0 < levelLaw m q (Ioi c) :=
  levelLaw_pos_of_Ioo hq0 hq1 (le_max_right c q) (max_lt hc hq1) le_rfl measurableSet_Ioi
    fun x hx => lt_of_le_of_lt (le_max_left _ _) hx.1

lemma levelLaw_integrable (hq0 : 0 ≤ q) (hq1 : q < 1) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (levelLaw m q) := by
  have := levelLaw_isProb m hq0 hq1
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [levelLaw_ae_mem m q] with s hs
  exact hC s ⟨hq0.trans hs.1.le, hs.2⟩

/-- **Lemma 55**, the mean: the level law has mean `μ_{k,q}`, `k = m + 1`. -/
theorem integral_levelLaw (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∫ s, s ∂levelLaw m q = muKQ (m + 1) q := by
  have hpk : q ^ (m + 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  have hpk2 : q ^ (m + 1 + 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  rw [levelLaw, integral_smul_measure, levelPre_univ m hq0 hq1, levelPre]
  change (ENNReal.ofReal _)⁻¹.toReal • ∫ s, s ∂(volume.restrict (Ioc q 1)).withDensity
    (fun s => ((s ^ m).toNNReal : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul (by fun_prop), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by apply div_nonneg <;> [linarith; positivity])]
  have : ∫ s in Ioc q 1, (s ^ m).toNNReal • s = ∫ s in Ioc q 1, s ^ (m + 1) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 ≤ s := hq0.trans hs.1.le
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (pow_nonneg hs0 m), pow_succ]
  rw [this, ← intervalIntegral.integral_of_le hq1.le, integral_pow, muKQ, smul_eq_mul]
  have h1 : (0 : ℝ) < 1 - q ^ (m + 1) := by linarith
  have h1' : (1 : ℝ) - q ^ (m + 1) ≠ 0 := h1.ne'
  push_cast
  rw [one_pow]
  field_simp

end Level

/-! ### The one-dimensional necessary conditions -/

section OneDim

variable {n : ℕ}

/-- If `Gs` are integrable distributions on `ℝ` with `Gs i` concentrated on `[l i, ∞)` and they
have a joint mix, then `Gs j` is concentrated on `(-∞, ∑ means - ∑_{i ≠ j} l i]`. -/
theorem ae_le_of_jointMix {Gs : Fin n → Measure ℝ} {Q : Measure (Fin n → ℝ)}
    (h : IsJointMix Gs Q) (hint : ∀ i, Integrable id (Gs i)) {l : Fin n → ℝ}
    (hl : ∀ i, ∀ᵐ x ∂Gs i, l i ≤ x) (j : Fin n) :
    ∀ᵐ x ∂Gs j, x ≤ ∑ i, ∫ y, y ∂Gs i - ∑ i ∈ Finset.univ.erase j, l i := by
  obtain ⟨hQ, ⟨s, hs⟩, hm⟩ := h
  have hlQ : ∀ i, ∀ᵐ x ∂Q, l i ≤ x i := fun i => by
    have := hl i
    rw [← hm i] at this
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable this
  have hintQ : ∀ i, Integrable (fun x : Fin n → ℝ => x i) Q := fun i => by
    have := hint i
    rw [← hm i] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply i).aemeasurable).1 this
  have hsum : s = ∑ i, ∫ y, y ∂Gs i := by
    have h1 : ∫ x, ∑ i, x i ∂Q = s := by
      rw [integral_congr_ae hs]; simp
    rw [← h1, integral_finsetSum _ (fun i _ => hintQ i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hm i]
    exact (integral_map (measurable_pi_apply i : Measurable fun x : Fin n → ℝ => x i).aemeasurable
      aestronglyMeasurable_id).symm
  have key : ∀ᵐ x ∂Q, x j ≤ s - ∑ i ∈ Finset.univ.erase j, l i := by
    filter_upwards [hs, ae_all_iff.2 hlQ] with x hx hx'
    have h1 := Finset.add_sum_erase Finset.univ x (Finset.mem_univ j)
    have h2 : ∑ i ∈ Finset.univ.erase j, l i ≤ ∑ i ∈ Finset.univ.erase j, x i :=
      Finset.sum_le_sum fun i _ => hx' i
    linarith
  rw [← hm j, ← hsum]
  exact (ae_map_iff (measurable_pi_apply j).aemeasurable measurableSet_Iic).2 key

/-- An upper bound that holds almost surely is at least every point `r` such that every
`(r', ∞)` with `r' < r` has positive measure. -/
lemma le_of_ae_le {ν : Measure ℝ} {c r : ℝ} (h : ∀ᵐ x ∂ν, x ≤ c)
    (hpos : ∀ r' < r, 0 < ν (Ioi r')) : r ≤ c := by
  by_contra hlt
  push Not at hlt
  have h1 := hpos c hlt
  rw [ae_iff] at h
  have : {a : ℝ | ¬a ≤ c} = Ioi c := by ext; simp
  rw [this] at h
  exact h1.ne' h

end OneDim

/-! ### Necessity through a linear functional -/

section Necessity

variable {n : ℕ}

/-- The product law `levelLaw ⊗ U(B)` of the pair `(S, b)`. -/
def pairLaw (q : ℝ) (B : Set G) : Measure (ℝ × G) :=
  (levelLaw (Module.finrank ℝ G) q).prod (unifSet B)

lemma pairLaw_isProb {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G} (h0 : volume B ≠ 0)
    (htop : volume B ≠ ⊤) : IsProbabilityMeasure (pairLaw q B) := by
  have := levelLaw_isProb (Module.finrank ℝ G) hq0 hq1
  have := unifSet_isProb h0 htop
  unfold pairLaw; infer_instance

lemma volume_frustumSet {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G} (hB : MeasurableSet B) :
    volume (frustumSet q B) = levelPre (Module.finrank ℝ G) q univ * volume B := by
  rw [measure_congr (frustumSet_ae_eq hq0 B), ← Measure.restrict_apply_univ,
    volume_restrict_frustumCore hq0 hB, Measure.map_apply measurable_frustumMap
      MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ]

lemma volume_frustumSet_ne_zero {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) : volume (frustumSet q B) ≠ 0 := by
  rw [volume_frustumSet hq0 hq1 hB]
  exact mul_ne_zero (levelPre_univ_ne_zero _ hq0 hq1) h0

lemma volume_frustumSet_ne_top {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (htop : volume B ≠ ⊤) : volume (frustumSet q B) ≠ ⊤ := by
  rw [volume_frustumSet hq0 hq1 hB]
  exact ENNReal.mul_ne_top (levelPre_univ_ne_top _ hq0 hq1) htop

/-- **Lemma 55** for `U(t + λ K_q)`, every `λ ≥ 0` (a point mass for `λ = 0`): it is the law of
`t + λ (S, S b)` with `(S, b) ∼ levelLaw ⊗ U(B)`. -/
theorem unifScaled_frustumSet {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤) (t : ℝ × G) (lam : ℝ) :
    unifScaled (frustumSet q B) t lam =
      (pairLaw q B).map (fun p => t + lam • frustumMap p) := by
  have : (volume : Measure (ℝ × G)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [unifScaled_eq_map (volume_frustumSet_ne_zero hq0 hq1 hB h0)
    (volume_frustumSet_ne_top hq0 hq1 hB htop), unifSet_frustumSet hq0 hq1 hB, pairLaw,
    Measure.map_map (by fun_prop) measurable_frustumMap]
  rfl

/-- The general necessary condition. Let `φ` be a linear functional on `ℝ × G` and
`g = φ ∘ frustumMap`, with `α ≤ g ≤ β` almost surely under `levelLaw ⊗ U(B)` and every
`{g > c}`, `c < β`, of positive probability. If the `U(t i + λ i K_q)` are jointly mixable,
then `β λ_j ≤ E[g] ∑ λ_i - α ∑_{i ≠ j} λ_i`. -/
theorem necessity_functional {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (φ : ℝ × G →L[ℝ] ℝ) {α β : ℝ}
    (hα : ∀ᵐ p ∂pairLaw q B, α ≤ φ (frustumMap p))
    (hβ : ∀ᵐ p ∂pairLaw q B, φ (frustumMap p) ≤ β)
    (hpos : ∀ c < β, 0 < pairLaw q B {p | c < φ (frustumMap p)})
    (t : Fin n → ℝ × G) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => unifScaled (frustumSet q B) (t i) (lam i)) (j : Fin n) :
    β * lam j ≤ (∫ p, φ (frustumMap p) ∂pairLaw q B) * ∑ i, lam i -
      α * ∑ i ∈ Finset.univ.erase j, lam i := by
  have hP := pairLaw_isProb hq0 hq1 h0 htop
  obtain ⟨Q, hQ⟩ := hmix
  set g : ℝ × G → ℝ := fun p => φ (frustumMap p) with hg_def
  have hgm : Measurable g := φ.measurable.comp measurable_frustumMap
  have hgint : Integrable g (pairLaw q B) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (max |α| |β|) ?_
    filter_upwards [hα, hβ] with p h1 h2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le α; have := le_max_left |α| |β|; linarith
    · have := le_abs_self β; have := le_max_right |α| |β|; linarith
  -- the image joint mix on `ℝ`
  have hQ' := hQ.map_add_hom φ.toLinearMap.toAddMonoidHom φ.measurable 0
  set Gs : Fin n → Measure ℝ := fun i =>
    (unifScaled (frustumSet q B) (t i) (lam i)).map (fun x => (0 : Fin n → ℝ) i +
      φ.toLinearMap.toAddMonoidHom x) with hGs
  have hGs_eq : ∀ i, Gs i = (pairLaw q B).map (fun p => φ (t i) + lam i * g p) := by
    intro i
    simp only [hGs, unifScaled_frustumSet hq0 hq1 hB h0 htop]
    rw [Measure.map_map (show Measurable (fun x : ℝ × G =>
        (0 : Fin n → ℝ) i + φ.toLinearMap.toAddMonoidHom x) from measurable_const.add φ.measurable)
      (show Measurable (fun p : ℝ × G => t i + lam i • frustumMap p) from
        measurable_const.add (measurable_frustumMap.const_smul (lam i)))]
    congr 1
    funext p
    simp [g, map_add, map_smul]
  have hfm : ∀ i, Measurable (fun p => φ (t i) + lam i * g p) := fun i =>
    measurable_const.add (measurable_const.mul hgm)
  have hint : ∀ i, Integrable id (Gs i) := fun i => by
    rw [hGs_eq, integrable_map_measure aestronglyMeasurable_id (hfm i).aemeasurable]
    exact (integrable_const _).add (hgint.const_mul _)
  have hmean : ∀ i, ∫ y, y ∂Gs i = φ (t i) + lam i * ∫ p, g p ∂pairLaw q B := by
    intro i
    rw [hGs_eq, show ∫ y, y ∂(pairLaw q B).map (fun p => φ (t i) + lam i * g p) =
        ∫ p, φ (t i) + lam i * g p ∂pairLaw q B from
      integral_map (hfm i).aemeasurable aestronglyMeasurable_id]
    rw [integral_add (integrable_const _) (hgint.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hl : ∀ i, ∀ᵐ x ∂Gs i, φ (t i) + lam i * α ≤ x := by
    intro i
    rw [hGs_eq]
    refine (ae_map_iff (hfm i).aemeasurable measurableSet_Ici).2 ?_
    filter_upwards [hα] with p hp
    have := mul_le_mul_of_nonneg_left hp (hlam i)
    linarith
  have hae := ae_le_of_jointMix hQ' hint hl j
  have hr := le_of_ae_le hae (r := φ (t j) + lam j * β) (by
    intro r' hr'
    rw [hGs_eq, Measure.map_apply (hfm j) measurableSet_Ioi]
    rcases (hlam j).lt_or_eq with hl0 | hl0
    · have hc : (r' - φ (t j)) / lam j < β := by
        rw [div_lt_iff₀ hl0]; linarith
      refine (hpos _ hc).trans_le (measure_mono fun p hp => ?_)
      simp only [mem_ofPred_eq] at hp
      simp only [mem_preimage, mem_Ioi]
      rw [div_lt_iff₀ hl0] at hp
      simp only [g]
      linarith
    · have : (fun p => φ (t j) + lam j * g p) ⁻¹' Ioi r' = univ := by
        ext p
        rw [← hl0] at hr'
        simp only [mem_preimage, mem_Ioi, mem_univ, iff_true, ← hl0, zero_mul, add_zero]
        linarith
      rw [this, measure_univ]; exact one_pos)
  rw [Finset.sum_congr rfl fun i _ => hmean i] at hr
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul] at hr
  have h1 := Finset.add_sum_erase Finset.univ (fun i => φ (t i)) (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => lam i) (Finset.mem_univ j)

  nlinarith

end Necessity

/-! ### Theorem 56 (a) and the fibre condition -/

section Necessity2

variable {n : ℕ}

lemma pairLaw_ae_fst {q : ℝ} (B : Set G) : ∀ᵐ p ∂pairLaw q B, p.1 ∈ Ioc q 1 :=
  Measure.quasiMeasurePreserving_fst.ae (levelLaw_ae_mem _ q)

lemma pairLaw_ae_snd {q : ℝ} {B : Set G} {P : G → Prop} (h : ∀ᵐ b ∂unifSet B, P b) :
    ∀ᵐ p ∂pairLaw q B, P p.2 :=
  Measure.quasiMeasurePreserving_snd.ae h

instance (B : Set G) : SFinite (unifSet B) := by unfold unifSet; infer_instance

lemma pairLaw_prod {q : ℝ} {B : Set G} (S : Set ℝ) (T : Set G) :
    pairLaw q B (S ×ˢ T) = levelLaw (Module.finrank ℝ G) q S * unifSet B T := by
  rw [pairLaw, Measure.prod_prod]

/-- **Theorem 56 (a)** (`b:thm:frustum`): if the uniform distributions on the scaled translates
`t i + λ i K_q` are jointly mixable, then the level condition (14) holds:
`(1 - q) λ_j ≤ (1 - μ_{k,q}) ∑ λ_i`, where `k = dim G + 1` is the dimension of the frustum. -/
theorem frustum_level_necessity {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (t : Fin n → ℝ × G) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => unifScaled (frustumSet q B) (t i) (lam i)) (j : Fin n) :
    (1 - q) * lam j ≤ (1 - muKQ (Module.finrank ℝ G + 1) q) * ∑ i, lam i := by
  have hU := unifSet_isProb h0 htop
  have hL := levelLaw_isProb (Module.finrank ℝ G) hq0 hq1
  let φ : ℝ × G →L[ℝ] ℝ := -ContinuousLinearMap.fst ℝ ℝ G
  have hφ : ∀ p : ℝ × G, φ (frustumMap p) = -p.1 := fun p => by simp [φ, frustumMap]
  have key := necessity_functional hq0 hq1 hB h0 htop φ (α := -1) (β := -q) ?_ ?_ ?_ t lam hlam
    hmix j
  · have hmean : ∫ p, φ (frustumMap p) ∂pairLaw q B = -muKQ (Module.finrank ℝ G + 1) q := by
      simp_rw [hφ]
      have := integral_prod_mul (μ := levelLaw (Module.finrank ℝ G) q) (ν := unifSet B)
        (fun s : ℝ => -s) (fun _ : G => (1 : ℝ))
      simp only [mul_one, integral_const, smul_eq_mul, measureReal_def, measure_univ,
        ENNReal.toReal_one] at this
      rw [pairLaw, this, integral_neg, integral_levelLaw hq0 hq1]
    rw [hmean] at key
    have h2 := Finset.add_sum_erase Finset.univ (fun i => lam i) (Finset.mem_univ j)
    nlinarith
  · filter_upwards [pairLaw_ae_fst B] with p hp
    rw [hφ]; linarith [hp.2]
  · filter_upwards [pairLaw_ae_fst B] with p hp
    rw [hφ]; linarith [hp.1]
  · intro c hc
    have hsub : Iio (-c) ×ˢ (univ : Set G) ⊆ {p | c < φ (frustumMap p)} := by
      rintro p ⟨hp, -⟩
      simp only [mem_Iio] at hp
      simp only [mem_ofPred_eq, hφ]
      linarith
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [pairLaw_prod, measure_univ, mul_one]
    exact levelLaw_Iio_pos hq0 hq1 (by linarith)

/-- The fibre necessary condition (used for Corollaries 57 and 58): let `ψ` be a linear
functional on `G` with `α ≤ ψ ≤ 1` on `B` (almost surely under `U(B)`), `α ≤ 0`, and with every
`{ψ > c}`, `c < 1`, of positive probability. If the `U(t i + λ i K_q)` are jointly mixable, then
`λ_j ≤ μ_{k,q} E[ψ] ∑ λ_i - α ∑_{i ≠ j} λ_i`. -/
theorem frustum_fibre_necessity {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (ψ : G →L[ℝ] ℝ) {α : ℝ} (hα0 : α ≤ 0) (hψα : ∀ᵐ b ∂unifSet B, α ≤ ψ b)
    (hψ1 : ∀ᵐ b ∂unifSet B, ψ b ≤ 1) (hpos : ∀ c < 1, 0 < unifSet B {b | c < ψ b})
    (t : Fin n → ℝ × G) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => unifScaled (frustumSet q B) (t i) (lam i)) (j : Fin n) :
    lam j ≤ muKQ (Module.finrank ℝ G + 1) q * (∫ b, ψ b ∂unifSet B) * ∑ i, lam i -
      α * ∑ i ∈ Finset.univ.erase j, lam i := by
  have hU := unifSet_isProb h0 htop
  have hL := levelLaw_isProb (Module.finrank ℝ G) hq0 hq1
  let φ : ℝ × G →L[ℝ] ℝ := ψ.comp (ContinuousLinearMap.snd ℝ ℝ G)
  have hφ : ∀ p : ℝ × G, φ (frustumMap p) = p.1 * ψ p.2 := fun p => by
    simp [φ, frustumMap, map_smul]
  have key := necessity_functional hq0 hq1 hB h0 htop φ (α := α) (β := 1) ?_ ?_ ?_ t lam hlam
    hmix j
  · have hmean : ∫ p, φ (frustumMap p) ∂pairLaw q B =
        muKQ (Module.finrank ℝ G + 1) q * ∫ b, ψ b ∂unifSet B := by
      simp_rw [hφ]
      rw [pairLaw, integral_prod_mul (fun s : ℝ => s) (fun b : G => ψ b),
        integral_levelLaw hq0 hq1]
    rw [hmean, one_mul] at key
    exact key
  · filter_upwards [pairLaw_ae_fst B, pairLaw_ae_snd hψα] with p hp hb
    rw [hφ]
    have h1 : 0 ≤ p.1 := hq0.trans hp.1.le
    nlinarith [hp.2]
  · filter_upwards [pairLaw_ae_fst B, pairLaw_ae_snd hψ1] with p hp hb
    rw [hφ]
    have h1 : 0 ≤ p.1 := hq0.trans hp.1.le
    nlinarith [hp.2]
  · intro c hc
    set M := max c 0
    set c' := (1 + M) / 2
    have hM1 : M < 1 := max_lt hc one_pos
    have hc'0 : 0 < c' := by have := le_max_right c 0; simp only [c']; linarith
    have hc'1 : c' < 1 := by simp only [c']; linarith
    have hcc : c < c' * c' := by
      have := le_max_left c 0
      have : c' * c' - M = ((1 - M) / 2) ^ 2 := by simp only [c']; ring
      nlinarith [sq_nonneg ((1 - M) / 2), mul_pos (by linarith : (0:ℝ) < 1 - M)
        (by linarith : (0:ℝ) < 1 - M)]
    have hsub : Ioi c' ×ˢ {b : G | c' < ψ b} ⊆ {p | c < φ (frustumMap p)} := by
      rintro p ⟨hp1, hp2⟩
      simp only [mem_Ioi] at hp1
      simp only [mem_ofPred_eq] at hp2
      simp only [mem_ofPred_eq, hφ]
      have : c' * c' < p.1 * ψ p.2 := mul_lt_mul'' hp1 hp2 hc'0.le hc'0.le
      linarith
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [pairLaw_prod]
    exact ENNReal.mul_pos (levelLaw_Ioi_pos hq0 hq1 hc'1).ne' (hpos c' hc'1).ne'

end Necessity2

/-! ### Theorem 56 (b): sufficiency, with Theorem 27 as a hypothesis -/

section Sufficiency

/-- The sum of a joint mix of integrable distributions is the sum of their means. -/
theorem IsJointMix.sum_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] {n : ℕ}
    {Gs : Fin n → Measure E} {Q : Measure (Fin n → E)} (h : IsJointMix Gs Q)
    (hint : ∀ i, Integrable id (Gs i)) {s : E} (hs : ∀ᵐ x ∂Q, ∑ j, x j = s) :
    s = ∑ i, ∫ y, y ∂Gs i := by
  obtain ⟨hQ, -, hm⟩ := h
  have hintQ : ∀ i, Integrable (fun x : Fin n → E => x i) Q := fun i => by
    have := hint i
    rw [← hm i] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply i).aemeasurable).1 this
  have h1 : ∫ x, ∑ i, x i ∂Q = s := by
    rw [integral_congr_ae hs, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul]
  rw [← h1, integral_finsetSum _ (fun i _ => hintQ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hm i]
  exact (integral_map (measurable_pi_apply i : Measurable fun x : Fin n → E => x i).aemeasurable
    aestronglyMeasurable_id).symm

/-- `H_{k,q,λ}`: the law of `λ - λ S` with `S ∼ levelLaw` (the point mass at `0` for
`λ = 0`), `k = m + 1`. -/
def hLaw (m : ℕ) (q lam : ℝ) : Measure ℝ := (levelLaw m q).map (fun s => lam * (1 - s))

lemma hLaw_isProb (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (lam : ℝ) :
    IsProbabilityMeasure (hLaw m q lam) := by
  have := levelLaw_isProb m hq0 hq1
  unfold hLaw; infer_instance

lemma hLaw_ae {m : ℕ} {q lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ᵐ x ∂hLaw m q lam, 0 ≤ x ∧ x ≤ (1 - q) * lam := by
  unfold hLaw
  refine (ae_map_iff (by fun_prop : Measurable fun s : ℝ => lam * (1 - s)).aemeasurable
    ((measurableSet_Ici).inter (measurableSet_Iic))).2 ?_
  filter_upwards [levelLaw_ae_mem m q] with s hs
  simp only [mem_inter_iff, mem_Ici, mem_Iic]
  exact ⟨mul_nonneg hlam (by linarith [hs.2]), by
    nlinarith [mul_nonneg hlam (sub_nonneg.2 hs.1.le)]⟩

lemma hLaw_integrable {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (lam : ℝ) :
    Integrable id (hLaw m q lam) := by
  unfold hLaw
  rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  exact levelLaw_integrable hq0 hq1 (by fun_prop)

lemma integral_hLaw {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (lam : ℝ) :
    ∫ x, x ∂hLaw m q lam = (1 - muKQ (m + 1) q) * lam := by
  have := levelLaw_isProb m hq0 hq1
  unfold hLaw
  rw [show ∫ x, x ∂(levelLaw m q).map (fun s => lam * (1 - s)) =
      ∫ s, lam * (1 - s) ∂levelLaw m q from
    integral_map (by fun_prop : Measurable fun s : ℝ => lam * (1 - s)).aemeasurable
      aestronglyMeasurable_id, integral_const_mul,
    integral_sub (integrable_const _) (levelLaw_integrable hq0 hq1 (f := fun s => s)
      continuous_id),
    integral_const, integral_levelLaw hq0 hq1]
  simp; ring

/-- **The hypothesis taken from Theorem 27** (`j:thm:main`), for the family `H_{k,q,λ}`
(`k = m + 1`): for every `n ≥ 2` there is a Borel function `Ψ` of `λ` and of a sequence of
independent uniform variables such that, whenever `λ ≥ 0`, not all zero, satisfies the level
condition (14) — the condition `max_j B_j ≤ ∑_j μ_j` of Theorem 27, since `H_{k,q,λ}` has right
end `(1 - q) λ` and mean `(1 - μ_{k,q}) λ` — the law of `Ψ λ` is a joint mix of the
`H_{k,q,λ_i}`. Theorem 27 gives the existence (each `H_{k,q,λ}` has a concave distribution
function); the Borel dependence on `λ` is the measurability claim in the proof of Theorem 56. -/
def Thm27Frustum (m : ℕ) (q : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ Ψ : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → ℝ),
    Measurable (Function.uncurry Ψ) ∧
    ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) →
      IsJointMix (fun i => hLaw m q (lam i)) (unifSeq.map (Ψ lam))

variable [SecondCountableTopology G]

/-- Step (2)-(3) of the construction, for a given level vector `T`: `X_i = t_i + (S_i, W_i)` with
`S = λ - T` and `W = Φ_B (S, 0) ω`. -/
def stepFun {n : ℕ} (ΦB : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G))
    (lam : Fin n → ℝ) (t : Fin n → ℝ × G) (z : (Fin n → ℝ) × (ℕ → ℝ)) : Fin n → ℝ × G :=
  fun i => t i + (lam i - z.1 i, ΦB (fun j => lam j - z.1 j, 0) z.2 i)

/-- The construction of Theorem 56 (b): `T = Ψ λ ω'`, then `stepFun`, with `ω', ω''` the two
halves of the uniform sequence `ω`. -/
def frustumMix {n : ℕ} (Ψ : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → ℝ))
    (ΦB : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G))
    (p : (Fin n → ℝ) × (Fin n → ℝ × G)) (ω : ℕ → ℝ) : Fin n → ℝ × G :=
  stepFun ΦB p.1 p.2 (Ψ p.1 (splitSeq ω).1, (splitSeq ω).2)

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurable_stepFun {n : ℕ} {ΦB : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΦB : Measurable (Function.uncurry ΦB)) (lam : Fin n → ℝ) (t : Fin n → ℝ × G) :
    Measurable (stepFun ΦB lam t) := by
  have h1 : Measurable (fun z : (Fin n → ℝ) × (ℕ → ℝ) =>
      ΦB (fun j => lam j - z.1 j, 0) z.2) :=
    hΦB.comp (f := fun z : (Fin n → ℝ) × (ℕ → ℝ) => ((fun j => lam j - z.1 j, 0), z.2))
      (by fun_prop)
  exact measurable_pi_iff.2 fun i => measurable_const.add
    ((measurable_const.sub ((measurable_pi_apply i).comp measurable_fst)).prodMk
      ((measurable_pi_apply i).comp h1))

omit [FiniteDimensional ℝ G] [(volume : Measure G).IsAddHaarMeasure] in
lemma measurable_frustumMix {n : ℕ} {Ψ : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → ℝ)}
    {ΦB : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΨ : Measurable (Function.uncurry Ψ)) (hΦB : Measurable (Function.uncurry ΦB)) :
    Measurable (Function.uncurry (frustumMix Ψ ΦB)) := by
  have hT : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ × G)) × (ℕ → ℝ) =>
      Ψ z.1.1 (splitSeq z.2).1) :=
    hΨ.comp (f := fun z : ((Fin n → ℝ) × (Fin n → ℝ × G)) × (ℕ → ℝ) =>
      (z.1.1, (splitSeq z.2).1)) ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_splitSeq.comp measurable_snd)))
  have hσ : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ × G)) × (ℕ → ℝ) =>
      fun j => z.1.1 j - Ψ z.1.1 (splitSeq z.2).1 j) :=
    measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp
      (measurable_fst.comp measurable_fst)).sub ((measurable_pi_apply j).comp hT)
  have hW : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ × G)) × (ℕ → ℝ) =>
      ΦB (fun j => z.1.1 j - Ψ z.1.1 (splitSeq z.2).1 j, 0) (splitSeq z.2).2) :=
    hΦB.comp (f := fun z : ((Fin n → ℝ) × (Fin n → ℝ × G)) × (ℕ → ℝ) =>
      ((fun j => z.1.1 j - Ψ z.1.1 (splitSeq z.2).1 j, 0), (splitSeq z.2).2))
      ((hσ.prodMk measurable_const).prodMk
      (measurable_snd.comp (measurable_splitSeq.comp measurable_snd)))
  refine measurable_pi_iff.2 fun i => ?_
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
    ((((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_pi_apply i).comp hT)).prodMk ((measurable_pi_apply i).comp hW))

/-- The core of Theorem 56 (b): if `P₁` is a joint mix of the `H_{k,q,λ_i}` and the base has
the scaling property, `stepFun` turns `P₁ ⊗ unifSeq` into a joint mix of the
`U(t_i + λ_i K_q)`. -/
theorem isJointMix_stepFun {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (hBint : Integrable id (unifSet B)) {mB : ℝ} {n : ℕ}
    {ΦB : (Fin n → ℝ) × (Fin n → G) → (ℕ → ℝ) → (Fin n → G)}
    (hΦB : Measurable (Function.uncurry ΦB))
    (hBmix : ∀ (σ : Fin n → ℝ), (∀ i, 0 ≤ σ i) → (∃ i, σ i ≠ 0) →
      (∀ k, mB * σ k ≤ ∑ i, σ i) →
      IsJointMix (fun i => (unifSet B).map (fun x => (0 : Fin n → G) i + σ i • x))
        (unifSeq.map (ΦB (σ, 0))))
    (lam : Fin n → ℝ) (t : Fin n → ℝ × G) (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (h15 : ∀ j, mB * lam j ≤ muKQ (Module.finrank ℝ G + 1) q * ∑ i, lam i)
    {P₁ : Measure (Fin n → ℝ)}
    (hP₁ : IsJointMix (fun i => hLaw (Module.finrank ℝ G) q (lam i)) P₁) :
    IsJointMix (fun i => unifScaled (frustumSet q B) (t i) (lam i))
      ((P₁.prod unifSeq).map (stepFun ΦB lam t)) := by
  set m := Module.finrank ℝ G
  set μ := muKQ (m + 1) q
  have hU := unifSet_isProb h0 htop
  have hL := levelLaw_isProb m hq0 hq1
  obtain ⟨hP₁prob, ⟨sT, hsT⟩, hm1'⟩ := hP₁
  have hm1 : ∀ i, P₁.map (fun x => x i) = hLaw m q (lam i) := hm1'
  have hsT_eq : sT = (1 - μ) * ∑ i, lam i := by
    rw [IsJointMix.sum_eq_integral ⟨hP₁prob, ⟨sT, hsT⟩, hm1'⟩
      (fun i => hLaw_integrable hq0 hq1 _) hsT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => integral_hLaw hq0 hq1 _
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) (muKQ_ge (by omega) hq0 hq1)
  have hsum0 : 0 < ∑ i, lam i := by
    obtain ⟨i, hi⟩ := hne
    exact lt_of_lt_of_le ((hlam i).lt_of_ne hi.symm)
      (Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i))
  have hstep := measurable_stepFun hΦB lam t
  -- the good level vectors
  have hgood : ∀ᵐ T ∂P₁, (∀ i, 0 ≤ T i ∧ T i ≤ (1 - q) * lam i) ∧ ∑ i, T i = sT := by
    refine (ae_all_iff.2 fun i => ?_).and hsT
    have := hLaw_ae (m := m) (q := q) (hlam i)
    rw [← hm1 i] at this
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable this
  -- consequences for `σ = λ - T`
  have hσ : ∀ T : Fin n → ℝ, ((∀ i, 0 ≤ T i ∧ T i ≤ (1 - q) * lam i) ∧ ∑ i, T i = sT) →
      (∀ i, 0 ≤ lam i - T i) ∧ (∃ i, lam i - T i ≠ 0) ∧
        (∀ k, mB * (lam k - T k) ≤ ∑ i, (lam i - T i)) ∧
        ∑ i, (lam i - T i) = μ * ∑ i, lam i := by
    rintro T ⟨hT, hTs⟩
    have hS : ∑ i, (lam i - T i) = μ * ∑ i, lam i := by
      rw [Finset.sum_sub_distrib, hTs, hsT_eq]; ring
    have hS0 : ∀ i, 0 ≤ lam i - T i := fun i => by nlinarith [(hT i).2, hlam i]
    refine ⟨hS0, ?_, fun k => ?_, hS⟩
    · by_contra hc
      push Not at hc
      have : ∑ i, (lam i - T i) = 0 := Finset.sum_eq_zero fun i _ => hc i
      rw [hS] at this
      exact (mul_pos hμ0 hsum0).ne' this
    · rw [hS]
      rcases le_or_gt 0 mB with hmB | hmB
      · nlinarith [(hT k).1, h15 k]
      · nlinarith [hS0 k, mul_pos hμ0 hsum0]
  -- the joint mix of the fibres, for good `T`
  have hW : ∀ T : Fin n → ℝ, ((∀ i, 0 ≤ T i ∧ T i ≤ (1 - q) * lam i) ∧ ∑ i, T i = sT) →
      IsJointMix (fun i => (unifSet B).map (fun x => (lam i - T i) • x))
        (unifSeq.map (ΦB (fun j => lam j - T j, 0))) := by
    intro T hT
    obtain ⟨h1, h2, h3, -⟩ := hσ T hT
    simpa using hBmix (fun j => lam j - T j) h1 h2 h3
  have cB_int : ∀ c : ℝ, Integrable id ((unifSet B).map (fun x => c • x)) := fun c => by
    rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
    exact hBint.smul c
  have cB_mean : ∀ c : ℝ, ∫ y, y ∂(unifSet B).map (fun x => c • x) =
      c • ∫ y, y ∂unifSet B := fun c => by
    rw [show ∫ y, y ∂(unifSet B).map (fun x => c • x) = ∫ x, c • x ∂unifSet B from
      integral_map (by fun_prop : Measurable fun x : G => c • x).aemeasurable
        aestronglyMeasurable_id, integral_smul]
  refine ⟨inferInstance, ⟨∑ i, t i + (μ * ∑ i, lam i,
    (μ * ∑ i, lam i) • ∫ y, y ∂unifSet B), ?_⟩, fun i => ?_⟩
  · -- constant sum
    rw [ae_map_iff hstep.aemeasurable (measurableSet_sum_eq' _)]
    refine (Measure.ae_prod_iff_ae_ae (p := fun z => ∑ j, stepFun ΦB lam t z j = _)
      (hstep (measurableSet_sum_eq' _))).2 ?_
    filter_upwards [hgood] with T hT
    obtain ⟨-, -, -, hS⟩ := hσ T hT
    obtain ⟨-, ⟨sW, hsW⟩, -⟩ := hW T hT
    have hsW_eq : sW = ∑ i, ∫ y, y ∂(unifSet B).map (fun x => (lam i - T i) • x) :=
      IsJointMix.sum_eq_integral (hW T hT) (fun i => cB_int _) hsW
    simp_rw [cB_mean, ← Finset.sum_smul, hS] at hsW_eq
    have hsW' := (ae_map_iff (by exact (hΦB.comp measurable_prodMk_left).aemeasurable)
      (measurableSet_sum_eq' sW)).1 hsW
    filter_upwards [hsW'] with ω hω
    simp only [stepFun, Finset.sum_add_distrib]
    congr 1
    ext
    · simp only [Prod.fst_sum]
      exact hS
    · simp only [Prod.snd_sum]
      rw [hω, hsW_eq]
  · -- marginals
    show _ = unifScaled (frustumSet q B) (t i) (lam i)
    rw [unifScaled_frustumSet hq0 hq1 hB h0 htop]
    ext C hC
    have hA : MeasurableSet (stepFun ΦB lam t ⁻¹' ((fun x : Fin n → ℝ × G => x i) ⁻¹' C)) :=
      hstep ((measurable_pi_apply i) hC)
    have hfm : Measurable (fun p : ℝ × G => t i + lam i • frustumMap p) :=
      measurable_const.add (measurable_frustumMap.const_smul (lam i))
    set A' : Set (ℝ × G) := {p | t i + (lam i - p.1, (lam i - p.1) • p.2) ∈ C} with hA'
    have hA'm : MeasurableSet A' :=
      (measurable_const.add ((measurable_const.sub measurable_fst).prodMk
        ((measurable_const.sub measurable_fst).smul measurable_snd))) hC
    set f : ℝ → ENNReal := fun x => unifSet B (Prod.mk x ⁻¹' A') with hf
    have hfmeas : Measurable f := measurable_measure_prodMk_left hA'm
    rw [Measure.map_apply (measurable_pi_apply i) hC, Measure.map_apply hstep
      ((measurable_pi_apply i) hC), Measure.map_apply hfm hC, pairLaw,
      Measure.prod_apply hA, Measure.prod_apply (hfm hC)]
    have h1 : ∀ᵐ T ∂P₁, unifSeq (Prod.mk T ⁻¹' ((stepFun ΦB lam t) ⁻¹'
        ((fun x : Fin n → ℝ × G => x i) ⁻¹' C))) = f (T i) := by
      filter_upwards [hgood] with T hT
      obtain ⟨-, -, hWm⟩ := hW T hT
      have hWi := hWm i
      have hΦm : Measurable (ΦB (fun j => lam j - T j, 0)) := hΦB.comp measurable_prodMk_left
      have hset : MeasurableSet {w : G | t i + (lam i - T i, w) ∈ C} :=
        (measurable_const.add (measurable_const.prodMk measurable_id)) hC
      have e1 : Prod.mk T ⁻¹' ((stepFun ΦB lam t) ⁻¹' ((fun x : Fin n → ℝ × G => x i) ⁻¹' C)) =
          (ΦB (fun j => lam j - T j, 0)) ⁻¹' ((fun x : Fin n → G => x i) ⁻¹'
            {w | t i + (lam i - T i, w) ∈ C}) := by
        ext ω; simp [stepFun]
      rw [e1, ← Measure.map_apply hΦm ((measurable_pi_apply i) hset),
        ← Measure.map_apply (measurable_pi_apply i) hset, hWi,
        Measure.map_apply (by fun_prop) hset]
      simp only [hf]
      congr 1
    rw [lintegral_congr_ae h1]
    rw [show (∫⁻ T, f (T i) ∂P₁) = ∫⁻ x, f x ∂P₁.map (fun T => T i) from
      (lintegral_map hfmeas (measurable_pi_apply i)).symm, hm1 i, hLaw,
      lintegral_map hfmeas (by fun_prop)]
    refine lintegral_congr fun s => ?_
    simp only [hf]
    congr 1
    ext b
    simp only [hA', mem_preimage, mem_ofPred_eq, frustumMap, Prod.smul_mk, smul_eq_mul,
      smul_smul]
    constructor <;> intro h <;> convert h using 3 <;> ring_nf

/-- **Theorem 56 (b)** (`b:thm:frustum`): given Theorem 27 for the level laws (`Thm27Frustum`)
and the scaling property of the base `F = {1} × B` with constant `m_B` (stated for `U(B)`,
with its Borel construction `Φ_B`), the construction of the paper (`frustumMix`: levels `T` from
Theorem 27, `S = λ - T`, fibres from `Φ_B (S, 0)`) is a Borel function of the parameters and
of a uniform sequence whose law is a joint mix of the `U(t i + λ i K_q)` whenever `λ ≥ 0`, not
all zero, satisfies (14) and (15). -/
theorem frustum_sufficiency {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (hBint : Integrable id (unifSet B)) {mB : ℝ}
    (h27 : Thm27Frustum (Module.finrank ℝ G) q) (hBsc : ScalingProperty (unifSet B) mB)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ Φ : (Fin n → ℝ) × (Fin n → ℝ × G) → (ℕ → ℝ) → (Fin n → ℝ × G),
      Measurable (Function.uncurry Φ) ∧
      ∀ (lam : Fin n → ℝ) (t : Fin n → ℝ × G), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
        (∀ j, (1 - q) * lam j ≤ (1 - muKQ (Module.finrank ℝ G + 1) q) * ∑ i, lam i) →
        (∀ j, mB * lam j ≤ muKQ (Module.finrank ℝ G + 1) q * ∑ i, lam i) →
        IsJointMix (fun i => unifScaled (frustumSet q B) (t i) (lam i))
          (unifSeq.map (Φ (lam, t))) := by
  obtain ⟨Ψ, hΨ, hΨmix⟩ := h27 n hn
  obtain ⟨ΦB, hΦB, hΦBmix⟩ := hBsc n hn
  refine ⟨frustumMix Ψ ΦB, measurable_frustumMix hΨ hΦB, fun lam t hlam hne h14 h15 => ?_⟩
  have hΨl : Measurable (Ψ lam) := hΨ.comp measurable_prodMk_left
  have hP₁ := hΨmix lam hlam hne h14
  have e : unifSeq.map (frustumMix Ψ ΦB (lam, t)) =
      ((unifSeq.map (Ψ lam)).prod unifSeq).map (stepFun ΦB lam t) := by
    have : frustumMix Ψ ΦB (lam, t) =
        stepFun ΦB lam t ∘ Prod.map (Ψ lam) id ∘ splitSeq := rfl
    rw [this, ← Measure.map_map (measurable_stepFun hΦB lam t)
        ((hΨl.prodMap measurable_id).comp measurable_splitSeq),
      ← Measure.map_map (hΨl.prodMap measurable_id) measurable_splitSeq, map_splitSeq,
      ← Measure.map_prod_map _ _ hΨl measurable_id, Measure.map_id]
  rw [e]
  have := hP₁.1
  exact isJointMix_stepFun hq0 hq1 hB h0 htop hBint hΦB
    (fun σ h1 h2 h3 => hΦBmix σ 0 h1 h2 h3) lam t hlam hne h15 hP₁

/-- **Theorem 56**, last sentence: under the hypotheses of `frustum_sufficiency`, the frustum
has the scaling property with constant `max (a_{k,q}, m_B / μ_{k,q})`. -/
theorem frustum_scalingProperty {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (hBint : Integrable id (unifSet B)) {mB : ℝ}
    (h27 : Thm27Frustum (Module.finrank ℝ G) q) (hBsc : ScalingProperty (unifSet B) mB) :
    ScalingPropertySet (frustumSet q B)
      (max (aKQ (Module.finrank ℝ G + 1) q) (mB / muKQ (Module.finrank ℝ G + 1) q)) := by
  set k := Module.finrank ℝ G + 1
  have hμ1 : muKQ k q < 1 := muKQ_lt_one (by omega) hq0 hq1
  have hμ0 : 0 < muKQ k q := lt_of_lt_of_le (by positivity) (muKQ_ge (by omega) hq0 hq1)
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := frustum_sufficiency hq0 hq1 hB h0 htop hBint h27 hBsc n hn
  refine ⟨Φ, hΦ, fun lam t hlam hne hc => hmix lam t hlam hne (fun j => ?_) (fun j => ?_)⟩
  · have h1 : aKQ k q * lam j ≤ ∑ i, lam i :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlam j)).trans (hc j)
    rw [aKQ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h1
    linarith
  · have h1 : mB / muKQ k q * lam j ≤ ∑ i, lam i :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlam j)).trans (hc j)
    rw [div_mul_eq_mul_div, div_le_iff₀ hμ0] at h1
    linarith

/-- **Theorem 56**, the bound on the constant (Lemma 54):
`max (a_{k,q}, m / μ_{k,q}) ≤ max (k + 1, m (k + 1) / k)` for `m ≥ 0`, `k ≥ 1`. -/
theorem frustum_constant_le {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {m : ℝ}
    (hm : 0 ≤ m) :
    max (aKQ k q) (m / muKQ k q) ≤ max ((k : ℝ) + 1) (m * (k + 1) / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hμ := muKQ_ge hk hq0 hq1
  have hμ0 : 0 < muKQ k q := lt_of_lt_of_le (by positivity) hμ
  refine max_le_max (akq_le hk hq0 hq1) ?_
  rw [div_le_div_iff₀ hμ0 hk0]
  rw [div_le_iff₀ (by positivity)] at hμ
  nlinarith

end Sufficiency

/-! ### Generic facts for the corollaries -/

section Generic

variable {α β : Type*} [MeasureSpace α] [MeasureSpace β]

/-- A measure-preserving equivalence carries `U(e⁻¹ K)` to `U(K)`. -/
lemma unifSet_map_preimage (e : α ≃ᵐ β) (he : MeasurePreserving e volume volume) (K : Set β) :
    (unifSet (e ⁻¹' K)).map e = unifSet K := by
  rw [unifSet, unifSet, Measure.map_smul _ e.measurable.aemeasurable,
    (he.restrict_preimage_emb e.measurableEmbedding K).map_eq, he.measure_preimage_equiv]

lemma unifSet_ae_mem {K : Set α} (hK : MeasurableSet K) : ∀ᵐ x ∂unifSet K, x ∈ K :=
  Measure.ae_smul_measure (ae_restrict_mem hK) _

end Generic

/-! ### Corollary 57: truncated simplices -/

section Simplex

/-- The corner simplex `{b ∈ ℝ^m : b ≥ 0, ∑ b ≤ 1}`. Its frustum `frustumSet q (simplexSet m)`
is the image of `Δ^q = {x ∈ ℝ^{m+1} : x ≥ 0, q ≤ ∑ x ≤ 1}` under the linear bijection
`x ↦ (∑ x, x_2, …, x_{m+1})`. -/
def simplexSet (m : ℕ) : Set (Fin m → ℝ) := {b | (∀ i, 0 ≤ b i) ∧ ∑ i, b i ≤ 1}

lemma measurableSet_simplexSet (m : ℕ) : MeasurableSet (simplexSet m) := by
  have : simplexSet m = (⋂ i, {b : Fin m → ℝ | 0 ≤ b i}) ∩ {b | ∑ i, b i ≤ 1} := by
    ext b; simp [simplexSet]
  rw [this]
  exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
    (measurable_pi_apply i)).inter (measurableSet_le (by fun_prop) measurable_const)

lemma volume_simplexSet_ne_top (m : ℕ) : volume (simplexSet m) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Set.pi univ fun _ : Fin m => Icc (0 : ℝ) 1)) ?_
    (measure_mono fun b hb i _ => ⟨hb.1 i, ?_⟩)
  · rw [volume_pi_pi]; simp
  · exact (Finset.single_le_sum (fun j _ => hb.1 j) (Finset.mem_univ i)).trans hb.2

lemma volume_simplexSet_ne_zero (m : ℕ) : volume (simplexSet m) ≠ 0 := by
  have hsub : (Set.pi univ fun _ : Fin m => Icc (0 : ℝ) (1 / (m + 1))) ⊆ simplexSet m := by
    intro b hb
    refine ⟨fun i => (hb i (mem_univ i)).1, ?_⟩
    calc ∑ i, b i ≤ ∑ _i : Fin m, (1 / ((m : ℝ) + 1)) :=
          Finset.sum_le_sum fun i _ => (hb i (mem_univ i)).2
      _ ≤ 1 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [mul_one_div, div_le_one (by positivity)]; linarith
  refine fun h => ?_
  have := measure_mono_null hsub h
  rw [volume_pi_pi, Finset.prod_eq_zero_iff] at this
  obtain ⟨i, -, hi⟩ := this
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at hi
  have : (0 : ℝ) < 1 / (m + 1) := by positivity
  linarith

/-- `b ↦ (1 - b₀, (b₁, …, b_{m'}))`: the corner simplex of dimension `m' + 1` is the cone
(frustum with `q = 0`) over the corner simplex of dimension `m'`, reflected. -/
def simplexEquiv (m' : ℕ) : (Fin (m' + 1) → ℝ) ≃ᵐ ℝ × (Fin m' → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.subLeft 1) (MeasurableEquiv.refl _))

lemma simplexEquiv_apply (m' : ℕ) (b : Fin (m' + 1) → ℝ) :
    simplexEquiv m' b = (1 - b 0, fun j => b j.succ) := by
  have : MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 b = (b 0, fun j => b j.succ) := by
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]; rfl
  simp only [simplexEquiv, MeasurableEquiv.trans_apply, this]
  rfl

lemma measurePreserving_simplexEquiv (m' : ℕ) :
    MeasurePreserving (simplexEquiv m') volume volume := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m' + 1) => (volume : Measure ℝ)) 0
  rw [← volume_pi, ← volume_pi, ← Measure.volume_eq_prod] at h1
  have h2 : MeasurePreserving (Prod.map (MeasurableEquiv.subLeft (1 : ℝ))
      (MeasurableEquiv.refl (Fin m' → ℝ))) (volume : Measure (ℝ × (Fin m' → ℝ))) volume :=
    (Measure.measurePreserving_sub_left volume (1 : ℝ)).prod (MeasurePreserving.id volume)
  exact h2.comp h1

lemma simplexSet_succ (m' : ℕ) :
    simplexSet (m' + 1) = simplexEquiv m' ⁻¹' frustumSet 0 (simplexSet m') := by
  ext b
  simp only [mem_preimage, simplexEquiv_apply, frustumSet, simplexSet, mem_ofPred_eq]
  rw [Fin.sum_univ_succ]
  constructor
  · rintro ⟨h0, h1⟩
    have hs : 0 ≤ ∑ j : Fin m', b j.succ := Finset.sum_nonneg fun j _ => h0 _
    refine ⟨by linarith, by linarith [h0 0], ?_⟩
    rcases (show 0 ≤ 1 - b 0 by linarith).lt_or_eq with hpos | hzero
    · refine ⟨fun j => b j.succ / (1 - b 0), ⟨fun j => div_nonneg (h0 _) hpos.le, ?_⟩, ?_⟩
      · rw [← Finset.sum_div, div_le_one hpos]; linarith
      · ext j; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    · refine ⟨0, ⟨fun _ => le_rfl, by simp⟩, ?_⟩
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, ← hzero, zero_mul]
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 (Fin.succ j)).1
        (by linarith) j (Finset.mem_univ j)
      exact this
  · rintro ⟨hq, h1, c, ⟨hc0, hc1⟩, hc⟩
    have hb : ∀ j : Fin m', b j.succ = (1 - b 0) * c j := fun j => by
      have := congrFun hc j; simpa using this
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases (by linarith) (fun j => ?_) i
      rw [hb]; exact mul_nonneg hq (hc0 j)
    · simp_rw [hb, ← Finset.mul_sum]
      nlinarith

/-- The law of the coordinate `b₀` under `U(simplexSet (m' + 1))`: that of `1 - S` with
`S ∼ levelLaw m' 0` (density `(m'+1) s^{m'}` on `[0, 1]`). -/
lemma unifSet_simplex_map_coord (m' : ℕ) :
    (unifSet (simplexSet (m' + 1))).map (fun b => b 0) =
      (levelLaw m' 0).map (fun s => 1 - s) := by
  have hfin : Module.finrank ℝ (Fin m' → ℝ) = m' := Module.finrank_fin_fun ℝ
  have e1 : (fun b : Fin (m' + 1) → ℝ => b 0) =
      (fun p : ℝ × (Fin m' → ℝ) => 1 - p.1) ∘ simplexEquiv m' := by
    funext b; simp [simplexEquiv_apply]
  have := levelLaw_isProb m' le_rfl one_pos
  have := unifSet_isProb (volume_simplexSet_ne_zero m') (volume_simplexSet_ne_top m')
  rw [e1, ← Measure.map_map (by fun_prop) (simplexEquiv m').measurable, simplexSet_succ,
    unifSet_map_preimage _ (measurePreserving_simplexEquiv m'),
    unifSet_frustumSet le_rfl one_pos (measurableSet_simplexSet m'),
    Measure.map_map (by fun_prop) measurable_frustumMap, hfin]
  have e2 : (fun p : ℝ × (Fin m' → ℝ) => 1 - p.1) ∘ frustumMap =
      (fun s => 1 - s) ∘ Prod.fst := by funext p; rfl
  rw [e2, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul]

lemma unifSet_simplex_coord_ae (m' : ℕ) :
    ∀ᵐ b ∂unifSet (simplexSet (m' + 1)), 0 ≤ b 0 ∧ b 0 ≤ 1 := by
  filter_upwards [unifSet_ae_mem (measurableSet_simplexSet (m' + 1))] with b hb
  exact ⟨hb.1 0, (Finset.single_le_sum (fun j _ => hb.1 j) (Finset.mem_univ 0)).trans hb.2⟩

lemma unifSet_simplex_coord_pos (m' : ℕ) {c : ℝ} (hc : c < 1) :
    0 < unifSet (simplexSet (m' + 1)) {b | c < b 0} := by
  have hm : MeasurableSet {b : Fin (m' + 1) → ℝ | c < b 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  have := congrArg (fun ν : Measure ℝ => ν (Ioi c)) (unifSet_simplex_map_coord m')
  rw [Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi,
    Measure.map_apply (by fun_prop) measurableSet_Ioi] at this
  change unifSet (simplexSet (m' + 1)) {b | c < b 0} = _ at this
  rw [this]
  refine (levelLaw_Iio_pos le_rfl one_pos (c := 1 - c) (by linarith)).trans_le
    (measure_mono fun s hs => ?_)
  simp only [mem_Iio] at hs
  simp only [mem_preimage, mem_Ioi]
  linarith

lemma integral_simplex_coord (m' : ℕ) :
    ∫ b, b 0 ∂unifSet (simplexSet (m' + 1)) = 1 / (m' + 2) := by
  have := levelLaw_isProb m' le_rfl one_pos
  rw [show ∫ b, b 0 ∂unifSet (simplexSet (m' + 1)) =
      ∫ x, x ∂(unifSet (simplexSet (m' + 1))).map (fun b => b 0) from
    (integral_map (measurable_pi_apply 0 : Measurable fun b : Fin (m' + 1) → ℝ => b 0).aemeasurable
      aestronglyMeasurable_id).symm,
    unifSet_simplex_map_coord, show ∫ x, x ∂(levelLaw m' 0).map (fun s => 1 - s) =
      ∫ s, 1 - s ∂levelLaw m' 0 from
    integral_map (by fun_prop : Measurable fun s : ℝ => 1 - s).aemeasurable
      aestronglyMeasurable_id]
  rw [integral_sub (integrable_const _) (levelLaw_integrable le_rfl one_pos (f := fun s => s)
    continuous_id), integral_const, integral_levelLaw le_rfl one_pos, muKQ]
  simp
  field_simp
  ring

variable {n : ℕ}

lemma muKQ_one {q : ℝ} (hq1 : q < 1) : muKQ 1 q = (1 + q) / 2 := by
  have : (1 : ℝ) - q ≠ 0 := by linarith
  rw [muKQ]
  field_simp
  ring

/-- **Corollary 57** (`b:cor:tsimplex`), necessity: if the uniform distributions on the scaled
translates of a frustum `Δ^q` of a `k`-simplex (`k = m + 1`) are jointly mixable, then
`(1 - q) λ_j ≤ (1 - μ_{k,q}) ∑ λ_i` and `k λ_j ≤ μ_{k,q} ∑ λ_i` for every `j`. -/
theorem tsimplex_necessity {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (t : Fin n → ℝ × (Fin m → ℝ)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => unifScaled (frustumSet q (simplexSet m)) (t i) (lam i)) :
    (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) ∧
      (∀ j, ((m : ℝ) + 1) * lam j ≤ muKQ (m + 1) q * ∑ i, lam i) := by
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
  have h14 : ∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i := fun j => by
    have := frustum_level_necessity hq0 hq1 (measurableSet_simplexSet m)
      (volume_simplexSet_ne_zero m) (volume_simplexSet_ne_top m) t lam hlam hmix j
    rwa [hfin] at this
  refine ⟨h14, fun j => ?_⟩
  have hsum : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ => hlam i
  rcases m with _ | m'
  · -- `k = 1`: the second condition follows from the first
    have h := h14 j
    rw [zero_add, muKQ_one hq1] at h ⊢
    have h1q : 0 < 1 - q := by linarith
    have : 2 * lam j ≤ ∑ i, lam i := by nlinarith
    simp only [CharP.cast_eq_zero, zero_add, one_mul]
    nlinarith
  · have := frustum_fibre_necessity hq0 hq1 (measurableSet_simplexSet (m' + 1))
      (volume_simplexSet_ne_zero _) (volume_simplexSet_ne_top _)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m' + 1) => ℝ) 0) le_rfl
      ((unifSet_simplex_coord_ae m').mono fun b hb => hb.1)
      ((unifSet_simplex_coord_ae m').mono fun b hb => hb.2)
      (fun c hc => unifSet_simplex_coord_pos m' hc) t lam hlam hmix j
    simp only [ContinuousLinearMap.proj_apply, zero_mul, sub_zero] at this
    rw [integral_simplex_coord, hfin] at this
    push_cast
    have h2 : (0 : ℝ) < m' + 2 := by positivity
    rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ h2] at this
    linarith

/-- **Corollary 57**, threshold, necessity: if `U(Δ^q)` (here `k = m + 1`) is `n`-completely
mixable with `n ≥ 1`, then `n ≥ k + 1`. -/
theorem tsimplex_completelyMixable_le {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hn : 1 ≤ n) (h : CompletelyMixable n (unifSet (frustumSet q (simplexSet m)))) :
    m + 2 ≤ n := by
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h0 := volume_frustumSet_ne_zero hq0 hq1 (measurableSet_simplexSet m)
    (volume_simplexSet_ne_zero m)
  have ht := volume_frustumSet_ne_top hq0 hq1 (measurableSet_simplexSet m)
    (volume_simplexSet_ne_top m)
  have hmix : JointlyMixable fun i : Fin n =>
      unifScaled (frustumSet q (simplexSet m)) 0 ((fun _ => (1 : ℝ)) i) := by
    obtain ⟨P, hP⟩ := h
    have e : (fun i : Fin n => unifScaled (frustumSet q (simplexSet m)) 0 ((fun _ => (1 : ℝ)) i))
        = fun _ => unifSet (frustumSet q (simplexSet m)) := by
      funext i; rw [unifScaled_eq_map h0 ht]; simp
    exact ⟨P, e ▸ hP⟩
  have := (tsimplex_necessity hq0 hq1 (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one)
    hmix).2 ⟨0, hn⟩
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hμ := muKQ_lt_one (k := m + 1) (by omega) hq0 hq1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ((m : ℝ) + 1) < n := by
    nlinarith [mul_lt_mul_of_pos_right hμ (by linarith : (0 : ℝ) < n)]
  exact_mod_cast this

/-- **Corollary 57**, threshold, the algebra of sufficiency: for `n ≥ k + 1` both conditions
hold with `λ ≡ 1`. -/
theorem tsimplex_conditions_of_le {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hn : k + 1 ≤ n) :
    (1 - q) ≤ (1 - muKQ k q) * n ∧ (k : ℝ) ≤ muKQ k q * n := by
  have hμ1 := muKQ_lt_one hk hq0 hq1
  have hμ := muKQ_ge hk hq0 hq1
  have ha := akq_le hk hq0 hq1
  have hn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hn
  rw [aKQ, div_le_iff₀ (by linarith)] at ha
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_iff₀ hk0] at hμ
  constructor <;> nlinarith

end Simplex

/-! ### Corollary 57: sufficiency, and the scaling property of simplices -/

section SimplexSuff

/-- A bounded set has an integrable uniform distribution. -/
lemma integrable_unifSet_of_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E] {K : Set E} (hK : MeasurableSet K)
    (h0 : volume K ≠ 0)
    (htop : volume K ≠ ⊤) {R : ℝ} (hR : K ⊆ Metric.closedBall 0 R) :
    Integrable id (unifSet K) := by
  have := unifSet_isProb h0 htop
  refine Integrable.of_bound aestronglyMeasurable_id R ?_
  filter_upwards [unifSet_ae_mem hK] with x hx
  simpa using hR hx

lemma simplexSet_subset_ball (m : ℕ) : simplexSet m ⊆ Metric.closedBall 0 1 := by
  intro b hb
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hb.1 i)]
  exact (Finset.single_le_sum (fun j _ => hb.1 j) (Finset.mem_univ i)).trans hb.2

/-- The affine inverse of `simplexEquiv`: `(s, y) ↦ (1 - s, y) = (-s, y) + (1, 0)`. -/
def simplexLin (m' : ℕ) : (ℝ × (Fin m' → ℝ)) →ₗ[ℝ] (Fin (m' + 1) → ℝ) where
  toFun p := Fin.cons (-p.1) p.2
  map_add' p p' := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [add_comm]
  map_smul' c p := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma simplexEquiv_symm_eq (m' : ℕ) (p : ℝ × (Fin m' → ℝ)) :
    (simplexEquiv m').symm p =
      (simplexLin m').toContinuousLinearMap p + Fin.cons 1 0 := by
  rw [MeasurableEquiv.symm_apply_eq, simplexEquiv_apply]
  ext
  · simp [simplexLin]
  · simp [simplexLin]

lemma scalingProperty_simplex_zero (c : ℝ) : ScalingProperty (unifSet (simplexSet 0)) c := by
  have := unifSet_isProb (volume_simplexSet_ne_zero 0) (volume_simplexSet_ne_top 0)
  intro n _
  refine ⟨fun _ _ _ => 0, measurable_const, fun lam t _ _ _ => ?_⟩
  refine ⟨inferInstance, ⟨0, Filter.Eventually.of_forall fun x => Subsingleton.elim _ _⟩,
    fun j => ?_⟩
  ext S hS
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  · have hS' : S = univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    simp [hS']

lemma muKQ_zero {k : ℕ} (hk : 1 ≤ k) : muKQ k 0 = k / (k + 1) := by
  rw [muKQ]; simp [zero_pow (by omega : k ≠ 0)]

/-- **Corollary 44 via Theorem 56 with `q = 0`** (the proof of `s:cor:simplex`): given Theorem 27
for the cone levels in every dimension, the corner simplex of dimension `m` has the scaling
property with constant `m + 1`. -/
theorem simplex_scalingProperty (h27 : ∀ m, Thm27Frustum m 0) :
    ∀ m : ℕ, ScalingProperty (unifSet (simplexSet m)) ((m : ℝ) + 1) := by
  intro m
  induction m with
  | zero => exact scalingProperty_simplex_zero _
  | succ m' ih =>
    have hfin : Module.finrank ℝ (Fin m' → ℝ) = m' := Module.finrank_fin_fun ℝ
    have : (volume : Measure (ℝ × (Fin m' → ℝ))).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]; infer_instance
    have hB := measurableSet_simplexSet m'
    have hS := frustum_scalingProperty le_rfl one_pos hB (volume_simplexSet_ne_zero m')
      (volume_simplexSet_ne_top m') (integrable_unifSet_of_subset hB
        (volume_simplexSet_ne_zero m') (volume_simplexSet_ne_top m') (simplexSet_subset_ball m'))
      (by rw [hfin]; exact h27 m') ih
    rw [hfin] at hS
    have hk : (1 : ℕ) ≤ m' + 1 := by omega
    have hc : max (aKQ (m' + 1) 0) (((m' : ℝ) + 1) / muKQ (m' + 1) 0) = ((m' + 1 : ℕ) : ℝ) + 1 := by
      rw [(akq_eq_iff hk le_rfl one_pos).2 (Or.inl rfl), muKQ_zero hk]
      have : ((m' : ℝ) + 1) / (((m' + 1 : ℕ) : ℝ) / ((m' + 1 : ℕ) + 1)) =
          ((m' + 1 : ℕ) : ℝ) + 1 := by
        push_cast; field_simp
      rw [this]; push_cast; simp
    rw [hc, scalingPropertySet_iff (volume_frustumSet_ne_zero le_rfl one_pos hB
      (volume_simplexSet_ne_zero m')) (volume_frustumSet_ne_top le_rfl one_pos hB
      (volume_simplexSet_ne_top m'))] at hS
    have hmap := scalingProperty_map_affine hS (simplexLin m').toContinuousLinearMap
      (Fin.cons 1 0)
    have e : (unifSet (frustumSet 0 (simplexSet m'))).map
        (fun x => (simplexLin m').toContinuousLinearMap x + Fin.cons 1 0) =
        unifSet (simplexSet (m' + 1)) := by
      rw [← unifSet_map_preimage _ (measurePreserving_simplexEquiv m'), ← simplexSet_succ,
        Measure.map_map (by fun_prop) (simplexEquiv m').measurable]
      have : (fun x => (simplexLin m').toContinuousLinearMap x + Fin.cons 1 0) ∘
          simplexEquiv m' = id := by
        funext b
        have := simplexEquiv_symm_eq m' (simplexEquiv m' b)
        rw [MeasurableEquiv.symm_apply_apply] at this
        exact this.symm
      rw [this, Measure.map_id]
    rwa [e] at hmap

/-- **Corollary 57**, sufficiency (with Theorem 27 as a hypothesis, for the frustum levels and
for the cone levels in every dimension): if `(1 - q) λ_j ≤ (1 - μ_{k,q}) ∑ λ_i` and
`k λ_j ≤ μ_{k,q} ∑ λ_i` for every `j` (`k = m + 1`), then the uniform distributions on the scaled
translates of `Δ^q` are jointly mixable. -/
theorem tsimplex_sufficiency {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum m q) (h27c : ∀ m, Thm27Frustum m 0) {n : ℕ} (hn : 2 ≤ n)
    (t : Fin n → ℝ × (Fin m → ℝ)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0)
    (h14 : ∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i)
    (h15 : ∀ j, ((m : ℝ) + 1) * lam j ≤ muKQ (m + 1) q * ∑ i, lam i) :
    JointlyMixable fun i => unifScaled (frustumSet q (simplexSet m)) (t i) (lam i) := by
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
  have hB := measurableSet_simplexSet m
  obtain ⟨Φ, -, hΦ⟩ := frustum_sufficiency hq0 hq1 hB (volume_simplexSet_ne_zero m)
    (volume_simplexSet_ne_top m) (integrable_unifSet_of_subset hB
      (volume_simplexSet_ne_zero m) (volume_simplexSet_ne_top m) (simplexSet_subset_ball m))
    (by rw [hfin]; exact h27) (simplex_scalingProperty h27c m) n hn
  exact ⟨_, hΦ lam t hlam hne (by rw [hfin]; exact h14) (by rw [hfin]; exact h15)⟩

/-- **Corollary 57**: under the Theorem 27 hypotheses, joint mixability of the scaled translates
of `Δ^q` is equivalent to the two conditions. -/
theorem tsimplex_jointlyMixable_iff {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum m q) (h27c : ∀ m, Thm27Frustum m 0) {n : ℕ} (hn : 2 ≤ n)
    (t : Fin n → ℝ × (Fin m → ℝ)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0) :
    (JointlyMixable fun i => unifScaled (frustumSet q (simplexSet m)) (t i) (lam i)) ↔
      (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) ∧
        (∀ j, ((m : ℝ) + 1) * lam j ≤ muKQ (m + 1) q * ∑ i, lam i) :=
  ⟨tsimplex_necessity hq0 hq1 t lam hlam, fun h =>
    tsimplex_sufficiency hq0 hq1 h27 h27c hn t lam hlam hne h.1 h.2⟩

/-- **Corollary 57**, the threshold: under the Theorem 27 hypotheses, for `n ≥ 2` the uniform
distribution on a frustum of a `k`-simplex (`k = m + 1`) is `n`-completely mixable if and only if
`n ≥ k + 1`. -/
theorem tsimplex_completelyMixable_iff {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum m q) (h27c : ∀ m, Thm27Frustum m 0) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (frustumSet q (simplexSet m))) ↔ m + 2 ≤ n := by
  refine ⟨tsimplex_completelyMixable_le hq0 hq1 (by omega), fun hle => ?_⟩
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h0 := volume_frustumSet_ne_zero hq0 hq1 (measurableSet_simplexSet m)
    (volume_simplexSet_ne_zero m)
  have ht := volume_frustumSet_ne_top hq0 hq1 (measurableSet_simplexSet m)
    (volume_simplexSet_ne_top m)
  obtain ⟨c1, c2⟩ := tsimplex_conditions_of_le (k := m + 1) (n := n) (by omega) hq0 hq1
    (by omega)
  obtain ⟨P, hP⟩ := tsimplex_sufficiency hq0 hq1 h27 h27c hn (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) ⟨⟨0, by omega⟩, one_ne_zero⟩
    (fun j => by simpa using c1) (fun j => by push_cast at c2; simpa using c2)
  have e : (fun i : Fin n => unifScaled (frustumSet q (simplexSet m)) 0 ((fun _ => (1 : ℝ)) i))
      = fun _ => unifSet (frustumSet q (simplexSet m)) := by
    funext i; rw [unifScaled_eq_map h0 ht]; simp
  rw [e] at hP
  exact ⟨P, hP⟩

end SimplexSuff

/-! ### Corollary 58: frusta over cubes and balls -/

section CubeBall

/-- Necessity of `n ≥ a_{k,q}` for every base: if `U(K_q)` is `n`-completely mixable, `n ≥ 1`,
then `a_{k,q} ≤ n` (`k = dim G + 1`). -/
theorem frustum_completelyMixable_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤) {n : ℕ} (hn : 1 ≤ n)
    (h : CompletelyMixable n (unifSet (frustumSet q B))) :
    aKQ (Module.finrank ℝ G + 1) q ≤ n := by
  have : (volume : Measure (ℝ × G)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hK0 := volume_frustumSet_ne_zero hq0 hq1 hB h0
  have hKt := volume_frustumSet_ne_top hq0 hq1 hB htop
  have hmix : JointlyMixable fun i : Fin n =>
      unifScaled (frustumSet q B) 0 ((fun _ => (1 : ℝ)) i) := by
    obtain ⟨P, hP⟩ := h
    have e : (fun i : Fin n => unifScaled (frustumSet q B) 0 ((fun _ => (1 : ℝ)) i))
        = fun _ => unifSet (frustumSet q B) := by
      funext i; rw [unifScaled_eq_map hK0 hKt]; simp
    exact ⟨P, e ▸ hP⟩
  have := frustum_level_necessity hq0 hq1 hB h0 htop (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) hmix ⟨0, hn⟩
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hμ := muKQ_lt_one (k := Module.finrank ℝ G + 1) (by omega) hq0 hq1
  rw [aKQ, div_le_iff₀ (by linarith)]
  linarith

/-- The algebra of Corollary 58: for `d ≥ 2` and an integer `n ≥ a_{d,q}`, both
`(1 - q) ≤ (1 - μ_{d,q}) n` and `2 ≤ μ_{d,q} n` hold. -/
theorem frustumBall_conditions_of_le {d : ℕ} (hd : 2 ≤ d) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {n : ℕ} (hn : aKQ d q ≤ n) :
    (1 - q) ≤ (1 - muKQ d q) * n ∧ 2 ≤ muKQ d q * n := by
  have hμ1 := muKQ_lt_one (by omega : 1 ≤ d) hq0 hq1
  have hμ := muKQ_ge (by omega : 1 ≤ d) hq0 hq1
  have ha := two_lt_akq hd hq0 hq1
  have hn3 : (3 : ℝ) ≤ n := by
    have : (2 : ℝ) < n := ha.trans_le hn
    have : 2 < n := by exact_mod_cast this
    exact_mod_cast this
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hμ23 : (2 : ℝ) / 3 ≤ muKQ d q := by
    refine le_trans ?_ hμ
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  refine ⟨?_, by nlinarith⟩
  rw [aKQ, div_le_iff₀ (by linarith)] at hn
  linarith

/-- The cube `[0,1]^m`, the base of `P_q`. -/
def cubeSet (m : ℕ) : Set (Fin m → ℝ) := Set.pi univ fun _ => Icc 0 1

lemma measurableSet_cubeSet (m : ℕ) : MeasurableSet (cubeSet m) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma volume_cubeSet (m : ℕ) : volume (cubeSet m) = 1 := by
  rw [cubeSet, volume_pi_pi]; simp

lemma cubeSet_succ (m' : ℕ) : cubeSet (m' + 1) =
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 ⁻¹' (Icc 0 1 ×ˢ cubeSet m') := by
  have : ∀ b : Fin (m' + 1) → ℝ,
      MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 b = (b 0, fun j => b j.succ) := fun b => by
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]; rfl
  ext b
  simp only [cubeSet, mem_preimage, this, mem_prod, mem_pi, mem_univ, true_implies]
  exact ⟨fun h => ⟨h 0, fun j => h j.succ⟩, fun h i => Fin.cases h.1 h.2 i⟩

lemma measurePreserving_piFinSuccAbove_zero (m' : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 1) => ℝ) 0)
      volume volume := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m' + 1) => (volume : Measure ℝ)) 0
  rwa [← volume_pi, ← volume_pi, ← Measure.volume_eq_prod] at h1

lemma unifSet_cube_map_coord (m' : ℕ) :
    (unifSet (cubeSet (m' + 1))).map (fun b => b 0) = unifSet (Icc (0 : ℝ) 1) := by
  have he : (fun b : Fin (m' + 1) → ℝ => b 0) =
      Prod.fst ∘ MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 := by
    funext b; simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  have hc0 : volume (cubeSet m') ≠ 0 := by rw [volume_cubeSet]; exact one_ne_zero
  have hct : volume (cubeSet m') ≠ ⊤ := by rw [volume_cubeSet]; exact ENNReal.one_ne_top
  have hi0 : volume (Icc (0 : ℝ) 1) ≠ 0 := by simp
  have hit : volume (Icc (0 : ℝ) 1) ≠ ⊤ := by simp
  have := unifSet_isProb hc0 hct
  rw [he, ← Measure.map_map measurable_fst (MeasurableEquiv.measurable _), cubeSet_succ,
    unifSet_map_preimage _ (measurePreserving_piFinSuccAbove_zero m'),
    unifSet_prod hi0 hit hc0 hct, Measure.map_fst_prod, measure_univ, one_smul]

lemma unifSet_Icc01_apply (S : Set ℝ) (hS : MeasurableSet S) :
    unifSet (Icc (0 : ℝ) 1) S = volume (S ∩ Icc 0 1) := by
  rw [unifSet, smul_apply, Measure.restrict_apply hS, Real.volume_Icc]; simp

lemma integral_cube_coord (m' : ℕ) : ∫ b, b 0 ∂unifSet (cubeSet (m' + 1)) = 1 / 2 := by
  rw [show ∫ b, b 0 ∂unifSet (cubeSet (m' + 1)) =
      ∫ x, x ∂(unifSet (cubeSet (m' + 1))).map (fun b => b 0) from
    (integral_map (measurable_pi_apply 0 : Measurable fun b : Fin (m' + 1) → ℝ => b 0).aemeasurable
      aestronglyMeasurable_id).symm, unifSet_cube_map_coord, unifSet, integral_smul_measure,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  simp

/-- **Corollary 58** for `P_q` (frustum of a pyramid over a cube, `d = m + 1 ≥ 2`), necessity:
joint mixability implies (14) and `2 λ_j ≤ μ_{d,q} ∑ λ_i`. -/
theorem pyramid_necessity {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {n : ℕ}
    (t : Fin n → ℝ × (Fin (m' + 1) → ℝ)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => unifScaled (frustumSet q (cubeSet (m' + 1))) (t i) (lam i)) :
    (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i) ∧
      (∀ j, 2 * lam j ≤ muKQ (m' + 2) q * ∑ i, lam i) := by
  have hfin : Module.finrank ℝ (Fin (m' + 1) → ℝ) = m' + 1 := Module.finrank_fin_fun ℝ
  have hB := measurableSet_cubeSet (m' + 1)
  have h0 : volume (cubeSet (m' + 1)) ≠ 0 := by rw [volume_cubeSet]; exact one_ne_zero
  have ht : volume (cubeSet (m' + 1)) ≠ ⊤ := by rw [volume_cubeSet]; exact ENNReal.one_ne_top
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := frustum_level_necessity hq0 hq1 hB h0 ht t lam hlam hmix j
    rwa [hfin] at this
  · have hcoord : ∀ {P : ℝ → Prop}, (∀ x ∈ Icc (0 : ℝ) 1, P x) → MeasurableSet {x | P x} →
        ∀ᵐ b ∂unifSet (cubeSet (m' + 1)), P (b 0) := by
      intro P hP hPm
      filter_upwards [unifSet_ae_mem hB] with b hb
      exact hP _ (hb 0 (mem_univ 0))
    have hpos : ∀ c < 1, 0 < unifSet (cubeSet (m' + 1)) {b | c < b 0} := by
      intro c hc
      have := congrArg (fun ν : Measure ℝ => ν (Ioi c)) (unifSet_cube_map_coord m')
      rw [Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi] at this
      change unifSet (cubeSet (m' + 1)) {b | c < b 0} = _ at this
      rw [this, unifSet_Icc01_apply _ measurableSet_Ioi]
      refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (max c 0) 1) fun x hx =>
        ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_le_of_lt (le_max_right _ _) hx.1 |>.le,
          hx.2.le⟩)
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      exact sub_pos.2 (max_lt hc one_pos)
    have := frustum_fibre_necessity hq0 hq1 hB h0 ht
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m' + 1) => ℝ) 0) le_rfl
      (hcoord (fun x hx => hx.1) (measurableSet_le measurable_const measurable_id))
      (hcoord (fun x hx => hx.2) (measurableSet_le measurable_id measurable_const))
      hpos t lam hlam hmix j
    simp only [ContinuousLinearMap.proj_apply, zero_mul, sub_zero] at this
    rw [integral_cube_coord, hfin] at this
    linarith

/-- The unit ball of `ℝ^m`, the base of `C_q`. -/
def ballSet (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) := Metric.closedBall 0 1

lemma unifSet_ball_neg (m : ℕ) :
    (unifSet (ballSet m)).map (fun x => -x) = unifSet (ballSet m) := by
  have hdet : LinearMap.det ((-1 : ℝ) • LinearMap.id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id]; simp
  have := unifSet_map_affine (ballSet m) hdet 0
  simp only [add_zero, neg_one_smul, LinearMap.neg_apply, LinearMap.id_apply] at this
  rw [this]
  congr 1
  ext y
  simp only [ballSet, mem_image, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro hy; exact ⟨-y, by simpa using hy, neg_neg y⟩

/-- **Corollary 58** for `C_q` (frustum of a circular cone, `d = m + 1 ≥ 2`), necessity: joint
mixability implies (14) and `2 λ_j ≤ ∑ λ_i`. -/
theorem circCone_necessity {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {n : ℕ}
    (t : Fin n → ℝ × EuclideanSpace ℝ (Fin (m' + 1))) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => unifScaled (frustumSet q (ballSet (m' + 1))) (t i) (lam i)) :
    (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i) ∧
      (∀ j, 2 * lam j ≤ ∑ i, lam i) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m' + 1))) = m' + 1 := by simp
  have hB : MeasurableSet (ballSet (m' + 1)) := Metric.isClosed_closedBall.measurableSet
  have h0 : volume (ballSet (m' + 1)) ≠ 0 := (Metric.measure_closedBall_pos _ _ one_pos).ne'
  have ht : volume (ballSet (m' + 1)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hU := unifSet_isProb h0 ht
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := frustum_level_necessity hq0 hq1 hB h0 ht t lam hlam hmix j
    rwa [hfin] at this
  · let ψ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m' + 1))
    have hψ : ∀ x, ψ x = x 0 := fun x => rfl
    have hbd : ∀ x ∈ ballSet (m' + 1), |x 0| ≤ 1 := fun x hx => by
      have := PiLp.norm_apply_le x 0
      rw [Real.norm_eq_abs] at this
      exact this.trans (mem_closedBall_zero_iff.1 hx)
    have hmean : ∫ x, ψ x ∂unifSet (ballSet (m' + 1)) = 0 := by
      have h1 : ∫ x, ψ x ∂unifSet (ballSet (m' + 1)) = ∫ x, ψ (-x) ∂unifSet (ballSet (m' + 1)) := by
        conv_lhs => rw [← unifSet_ball_neg]
        exact integral_map (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin (m' + 1)) =>
          -x).aemeasurable
          ψ.continuous.aestronglyMeasurable
      simp only [map_neg, integral_neg] at h1
      linarith
    have hpos : ∀ c < 1, 0 < unifSet (ballSet (m' + 1)) {b | c < ψ b} := by
      intro c hc
      set c' := max c 0
      have hc'1 : c' < 1 := max_lt hc one_pos
      set x0 : EuclideanSpace ℝ (Fin (m' + 1)) := EuclideanSpace.single 0 ((1 + c') / 2)
      have hsub : Metric.ball x0 ((1 - c') / 2) ⊆ {b | c < ψ b} ∩ ballSet (m' + 1) := by
        intro x hx
        rw [Metric.mem_ball, dist_eq_norm] at hx
        have h1 := PiLp.norm_apply_le (x - x0) 0
        have hx0 : x0 0 = (1 + c') / 2 := by simp [x0]
        have hn0 : ‖x0‖ = (1 + c') / 2 := by
          simp only [x0]
          have : 0 ≤ 1 + c' := by have := le_max_right c 0; linarith
          simp [abs_of_nonneg this]
        rw [Real.norm_eq_abs, PiLp.sub_apply, hx0] at h1
        refine ⟨?_, ?_⟩
        · simp only [mem_ofPred_eq, hψ]
          have := le_max_left c 0
          have := (abs_lt.1 (h1.trans_lt hx)).1
          linarith
        · rw [ballSet, mem_closedBall_zero_iff]
          calc ‖x‖ = ‖(x - x0) + x0‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - x0‖ + ‖x0‖ := norm_add_le _ _
            _ ≤ 1 := by rw [hn0]; linarith
      rw [unifSet, smul_apply, Measure.restrict_apply
        (measurableSet_lt measurable_const ψ.measurable), smul_eq_mul]
      refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ht) ?_
      exact ((Metric.measure_ball_pos _ _ (by linarith)).trans_le (measure_mono hsub)).ne'
    have := frustum_fibre_necessity hq0 hq1 hB h0 ht ψ (α := -1) (by norm_num)
      (by filter_upwards [unifSet_ae_mem hB] with x hx; rw [hψ]; exact (abs_le.1 (hbd x hx)).1)
      (by filter_upwards [unifSet_ae_mem hB] with x hx; rw [hψ]; exact (abs_le.1 (hbd x hx)).2)
      hpos t lam hlam hmix j
    rw [hmean, mul_zero, zero_mul, zero_sub, neg_one_mul, neg_neg] at this
    have h2 := Finset.add_sum_erase Finset.univ (fun i => lam i) (Finset.mem_univ j)
    linarith

end CubeBall

/-! ### Corollary 58: sufficiency and thresholds (with hypotheses) -/

section CubeBallSuff

variable [SecondCountableTopology G]

/-- Theorem 56 (b) for `λ ≡ 1`: `U(K_q)` is `n`-completely mixable when
`1 - q ≤ (1 - μ_{k,q}) n` and `m_B ≤ μ_{k,q} n`. -/
theorem frustum_completelyMixable_of {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {B : Set G}
    (hB : MeasurableSet B) (h0 : volume B ≠ 0) (htop : volume B ≠ ⊤)
    (hBint : Integrable id (unifSet B)) {mB : ℝ}
    (h27 : Thm27Frustum (Module.finrank ℝ G) q) (hBsc : ScalingProperty (unifSet B) mB)
    {n : ℕ} (hn : 2 ≤ n) (c1 : 1 - q ≤ (1 - muKQ (Module.finrank ℝ G + 1) q) * n)
    (c2 : mB ≤ muKQ (Module.finrank ℝ G + 1) q * n) :
    CompletelyMixable n (unifSet (frustumSet q B)) := by
  have : (volume : Measure (ℝ × G)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hK0 := volume_frustumSet_ne_zero hq0 hq1 hB h0
  have hKt := volume_frustumSet_ne_top hq0 hq1 hB htop
  obtain ⟨Φ, -, hΦ⟩ := frustum_sufficiency hq0 hq1 hB h0 htop hBint h27 hBsc n hn
  have hP := hΦ (fun _ => 1) (fun _ => 0) (fun _ => zero_le_one) ⟨⟨0, by omega⟩, one_ne_zero⟩
    (fun j => by simpa using c1) (fun j => by simpa using c2)
  have e : (fun i : Fin n => unifScaled (frustumSet q B) 0 ((fun _ => (1 : ℝ)) i))
      = fun _ => unifSet (frustumSet q B) := by
    funext i; rw [unifScaled_eq_map hK0 hKt]; simp
  exact ⟨_, e ▸ hP⟩

/-- **Corollary 58** for `P_q` (`d = m' + 2 ≥ 2`), the threshold: with Theorem 27 for the levels
and the scaling property of the cube with constant `2` as hypotheses, for `n ≥ 2`, `U(P_q)` is
`n`-completely mixable if and only if `n ≥ a_{d,q}`. (The direction `⇒` uses no hypothesis.) -/
theorem pyramid_completelyMixable_iff {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum (m' + 1) q) (hcube : ScalingProperty (unifSet (cubeSet (m' + 1))) 2)
    {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (frustumSet q (cubeSet (m' + 1)))) ↔ aKQ (m' + 2) q ≤ n := by
  have hfin : Module.finrank ℝ (Fin (m' + 1) → ℝ) = m' + 1 := Module.finrank_fin_fun ℝ
  have hB := measurableSet_cubeSet (m' + 1)
  have h0 : volume (cubeSet (m' + 1)) ≠ 0 := by rw [volume_cubeSet]; exact one_ne_zero
  have ht : volume (cubeSet (m' + 1)) ≠ ⊤ := by rw [volume_cubeSet]; exact ENNReal.one_ne_top
  constructor
  · intro h
    have := frustum_completelyMixable_le hq0 hq1 hB h0 ht (by omega) h
    rwa [hfin] at this
  · intro ha
    obtain ⟨c1, c2⟩ := frustumBall_conditions_of_le (d := m' + 2) (by omega) hq0 hq1 ha
    refine frustum_completelyMixable_of hq0 hq1 hB h0 ht
      (integrable_unifSet_of_subset hB h0 ht (R := 1) fun b hb => ?_) (by rw [hfin]; exact h27)
      hcube hn (by rw [hfin]; exact c1) (by rw [hfin]; exact c2)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have := hb i (mem_univ i)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]

/-- **Corollary 58** for `P_q`, joint mixability: with the same hypotheses, the scaled translates
are jointly mixable if and only if (14) and `2 λ_j ≤ μ_{d,q} ∑ λ_i`. -/
theorem pyramid_jointlyMixable_iff {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum (m' + 1) q) (hcube : ScalingProperty (unifSet (cubeSet (m' + 1))) 2)
    {n : ℕ} (hn : 2 ≤ n) (t : Fin n → ℝ × (Fin (m' + 1) → ℝ)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0) :
    (JointlyMixable fun i => unifScaled (frustumSet q (cubeSet (m' + 1))) (t i) (lam i)) ↔
      (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i) ∧
        (∀ j, 2 * lam j ≤ muKQ (m' + 2) q * ∑ i, lam i) := by
  have hfin : Module.finrank ℝ (Fin (m' + 1) → ℝ) = m' + 1 := Module.finrank_fin_fun ℝ
  have hB := measurableSet_cubeSet (m' + 1)
  have h0 : volume (cubeSet (m' + 1)) ≠ 0 := by rw [volume_cubeSet]; exact one_ne_zero
  have ht : volume (cubeSet (m' + 1)) ≠ ⊤ := by rw [volume_cubeSet]; exact ENNReal.one_ne_top
  refine ⟨pyramid_necessity hq0 hq1 t lam hlam, fun h => ?_⟩
  obtain ⟨Φ, -, hΦ⟩ := frustum_sufficiency hq0 hq1 hB h0 ht
    (integrable_unifSet_of_subset hB h0 ht (R := 1) fun b hb => by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have := hb i (mem_univ i)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
    (by rw [hfin]; exact h27) hcube n hn
  exact ⟨_, hΦ lam t hlam hne (by rw [hfin]; exact h.1) (by rw [hfin]; exact h.2)⟩

/-- **Corollary 58** for `C_q` (`d = m' + 2 ≥ 2`): with Theorem 27 for the levels and the scaling
property of the ball with constant `2` (Theorem 51, not formalised here) as hypotheses, (14) and
`2 λ_j ≤ μ_{d,q} ∑ λ_i` imply joint mixability (necessity: `circCone_necessity`). -/
theorem circCone_sufficiency {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum (m' + 1) q) (hball : ScalingProperty (unifSet (ballSet (m' + 1))) 2)
    {n : ℕ} (hn : 2 ≤ n) (t : Fin n → ℝ × EuclideanSpace ℝ (Fin (m' + 1))) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (h14 : ∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i)
    (h15 : ∀ j, 2 * lam j ≤ muKQ (m' + 2) q * ∑ i, lam i) :
    JointlyMixable fun i => unifScaled (frustumSet q (ballSet (m' + 1))) (t i) (lam i) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m' + 1))) = m' + 1 := by simp
  have hB : MeasurableSet (ballSet (m' + 1)) := Metric.isClosed_closedBall.measurableSet
  have h0 : volume (ballSet (m' + 1)) ≠ 0 := (Metric.measure_closedBall_pos _ _ one_pos).ne'
  have ht : volume (ballSet (m' + 1)) ≠ ⊤ := measure_closedBall_lt_top.ne
  obtain ⟨Φ, -, hΦ⟩ := frustum_sufficiency hq0 hq1 hB h0 ht
    (integrable_unifSet_of_subset hB h0 ht le_rfl) (by rw [hfin]; exact h27) hball n hn
  exact ⟨_, hΦ lam t hlam hne (by rw [hfin]; exact h14) (by rw [hfin]; exact h15)⟩

/-- **Corollary 58** for `C_q`, the threshold: with the same hypotheses, for `n ≥ 2`, `U(C_q)` is
`n`-completely mixable if and only if `n ≥ a_{d,q}`. (The direction `⇒` uses no hypothesis.) -/
theorem circCone_completelyMixable_iff {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : Thm27Frustum (m' + 1) q) (hball : ScalingProperty (unifSet (ballSet (m' + 1))) 2)
    {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (frustumSet q (ballSet (m' + 1)))) ↔ aKQ (m' + 2) q ≤ n := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m' + 1))) = m' + 1 := by simp
  have hB : MeasurableSet (ballSet (m' + 1)) := Metric.isClosed_closedBall.measurableSet
  have h0 : volume (ballSet (m' + 1)) ≠ 0 := (Metric.measure_closedBall_pos _ _ one_pos).ne'
  have ht : volume (ballSet (m' + 1)) ≠ ⊤ := measure_closedBall_lt_top.ne
  constructor
  · intro h
    have := frustum_completelyMixable_le hq0 hq1 hB h0 ht (by omega) h
    rwa [hfin] at this
  · intro ha
    obtain ⟨c1, c2⟩ := frustumBall_conditions_of_le (d := m' + 2) (by omega) hq0 hq1 ha
    exact frustum_completelyMixable_of hq0 hq1 hB h0 ht
      (integrable_unifSet_of_subset hB h0 ht le_rfl) (by rw [hfin]; exact h27)
      hball hn (by rw [hfin]; exact c1) (by rw [hfin]; exact c2)

end CubeBallSuff

end FrustumMix

end Mixes
