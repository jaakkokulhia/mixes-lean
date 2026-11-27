import Mixes.Cone
import Mixes.FrustumMix
import Mixes.Assembly

/-!
# The cone theorem and its corollaries (Theorem 43 (b), Corollaries 44, 45, Remark 46)

Item M1c of the verification priorities (`s:thm:cone`, `s:cor:simplex`, `s:cor:pyramid`,
`s:rem:tetra` in `mixes/main.tex`).

## Setting

As in `Cone.lean`: `V` is a finite-dimensional real space with an additive Haar measure,
`L : V ≃L[ℝ] ℝ × ℝ^m` are linear coordinates whose first coordinate is the functional `ℓ`
(`k = m + 1`), the base is `F = L⁻¹({1} × B)` and `K = coneSet L B` is the cone over `F`;
`coneUnif L B t λ` is `U(t + λ K)` (the point mass at `t` for `λ = 0`), and `sliceUnif L B 1`
is `U(F)`. The scaling property is `ScalingProperty` of `Bodies.lean` (Borel dependence on the
parameters and on a sequence of independent uniform variables included).

**Theorem 27** enters only through the hypothesis `Thm27Frustum m 0` of `FrustumMix.lean`: for
every `n ≥ 2` a Borel function `Ψ (λ, ω)` of `λ` and of a sequence `ω` of independent uniform
variables such that, whenever `λ ≥ 0`, not all zero, and `(k + 1) λ_j ≤ ∑ λ_i` (the condition
`max_j B_j ≤ ∑_j μ_j` of Theorem 27 for these laws), the law of `Ψ λ` is a joint mix of the laws
`G_{k, λ_i}` of `λ_i (1 - S)`, `S` with density `k s^{k-1}` on `[0, 1]` (`hLaw m 0 λ_i`, which is
the paper's definition of `G_{k,λ}` with `V = S`).

## Main results

* `cone_sufficiency`, `cone_scalingProperty`: **Theorem 43 (b)** and its last sentence.
* `simplex_scalingPropertySet`, `simplex_jointlyMixable_iff`, `simplex_completelyMixable_iff`,
  `simplex_necessity`: **Corollary 44** for every `k`-simplex `conv (p 0, …, p k)` in a
  `k`-dimensional space.
* `scalingProperty_Icc`, `scalingProperty_cube`: the segment and the cube have the scaling
  property with constant `2` (Lemma 1, unconditional, with the Borel dependence on the
  parameters).
* `pyramid_scalingPropertySet`, `pyramid_jointlyMixable_iff`, `pyramid_completelyMixable_iff`,
  `pyramid_necessity`: **Corollary 45** for every pyramid over a parallelotope.
* `khintchine`, `tetra_isCompleteMix`, `tetra_completelyMixable`,
  `tetrahedron_completelyMixable`: **Remark 46**, unconditionally.
-/

open MeasureTheory Set Pointwise

noncomputable section

namespace Mixes

namespace ConeMix

open FrustumMix

/-! ### Transport along measurable equivalences -/

/-- Transport of uniform distributions along a measurable equivalence that scales volume by a
constant factor (no measurability of the set needed). -/
lemma unifSet_preimage_equiv {α β : Type*} [MeasureSpace α] [MeasureSpace β] (e : α ≃ᵐ β)
    {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (he : volume.map e = c • volume) (C : Set β) :
    unifSet (e ⁻¹' C) = (unifSet C).map e.symm := by
  have h1 : (unifSet (e ⁻¹' C)).map e = unifSet C := by
    have hv : volume (e ⁻¹' C) = c * volume C := by
      rw [← e.map_apply, he, smul_apply, smul_eq_mul]
    rw [unifSet, Measure.map_smul, ← e.restrict_map, he, Measure.restrict_smul, smul_smul, hv,
      unifSet]
    congr 1
    by_cases hv : volume C = ⊤
    · rw [hv, ENNReal.mul_top hc0]; simp
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel hc0 hct, mul_one]
    exact e.measurable.aemeasurable
  rw [← h1, e.map_symm_map]

/-! ### The cone as a frustum with `q = 0` -/

section ConeFrustum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}
  (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) {B : Set (Fin m → ℝ)}

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
/-- In the coordinates `L`, the scaled translate `t + λ K` of the cone is the scaled translate
`L t + λ K_0` of the frustum with `q = 0` of `FrustumMix.lean`. -/
lemma preimage_frustum (t : V) (lam : ℝ) :
    coneChart L 0 ⁻¹' ((fun x => L t + lam • x) '' frustumSet 0 B) =
      scaledTranslate t lam (coneSet L B) := by
  ext x
  simp only [mem_preimage, coneChart_apply, sub_zero, mem_image, frustumSet, mem_ofPred_eq,
    scaledTranslate, coneSet, coneBase, mem_Icc]
  constructor
  · rintro ⟨⟨s, y⟩, ⟨hs0, hs1, b, hb, hy⟩, hx⟩
    simp only at hs0 hs1 hy
    subst hy
    refine ⟨s • L.symm (1, b), ⟨s, ⟨hs0, hs1⟩, _, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    rw [← smul_symm_one, ← map_smul, ← ContinuousLinearEquiv.symm_apply_apply L t, ← map_add,
      hx, ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨y, ⟨s, ⟨hs0, hs1⟩, _, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(s, s • b), ⟨hs0, hs1, b, hb, rfl⟩, ?_⟩
    rw [map_add, map_smul, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    simp

omit [FiniteDimensional ℝ V] in
/-- `U(t + λ K)` is the image under `L⁻¹` of `U(L t + λ K_0)`. -/
lemma coneUnif_eq_map (t : V) {lam : ℝ} (hlam : 0 ≤ lam) :
    coneUnif L B t lam = (unifScaled (frustumSet 0 B) (L t) lam).map L.symm := by
  unfold coneUnif unifScaled
  rcases eq_or_lt_of_le hlam with h | h
  · subst h
    simp only [lt_irrefl, ↓reduceIte]
    rw [Measure.map_dirac' L.symm.continuous.measurable,
      ContinuousLinearEquiv.symm_apply_apply]
  · simp only [h, h.ne', ↓reduceIte]
    obtain ⟨c, hc0, hct, he⟩ := map_coneChart L (0 : V)
    rw [← preimage_frustum, unifSet_preimage_equiv _ hc0 hct he]
    congr 1
    funext w
    rw [coneChart_symm_apply, zero_add]

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma scaledTranslate_eq_image (t : V) (lam : ℝ) (K : Set V) :
    scaledTranslate t lam K = (fun x => t + lam • x) '' K := by
  ext x; simp [scaledTranslate, eq_comm]

omit [FiniteDimensional ℝ V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] in
/-- `coneUnif` is `unifScaled` of the cone (both are the point mass for `λ = 0`). -/
lemma coneUnif_eq_unifScaled (t : V) {lam : ℝ} (hlam : 0 ≤ lam) :
    coneUnif L B t lam = unifScaled (coneSet L B) t lam := by
  unfold coneUnif unifScaled
  rcases eq_or_lt_of_le hlam with h | h
  · subst h; simp
  · simp only [h, h.ne', ↓reduceIte, scaledTranslate_eq_image]

omit [FiniteDimensional ℝ V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] in
/-- The scaling property of the base `F` (for `U(F) = sliceUnif L B 1`) is that of `B`. -/
lemma scalingProperty_sliceUnif_iff [SecondCountableTopology V] [BorelSpace V] {c : ℝ} :
    ScalingProperty (sliceUnif L B 1) c ↔ ScalingProperty (unifSet B) c := by
  let M₁ : (Fin m → ℝ) →L[ℝ] V :=
    (L.symm : ℝ × (Fin m → ℝ) →L[ℝ] V).comp (ContinuousLinearMap.inr ℝ ℝ (Fin m → ℝ))
  let M₂ : V →L[ℝ] (Fin m → ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)).comp (L : V →L[ℝ] ℝ × (Fin m → ℝ))
  have h1 : (fun b => M₁ b + L.symm (1, 0)) = fun b : Fin m → ℝ => (1 : ℝ) • L.symm (1, b) := by
    funext b
    simp only [M₁, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      Function.comp_apply, ContinuousLinearMap.inr_apply, one_smul, ← map_add, Prod.mk_add_mk,
      zero_add, add_zero]
  have h2 : (fun y => M₂ y + 0) ∘ (fun b : Fin m → ℝ => (1 : ℝ) • L.symm (1, b)) = id := by
    funext b
    simp [M₂]
  constructor
  · intro h
    have := scalingProperty_map_affine h M₂ 0
    rwa [sliceUnif, Measure.map_map (by fun_prop) (by fun_prop), h2, Measure.map_id] at this
  · intro h
    have := scalingProperty_map_affine h M₁ (L.symm (1, 0))
    rwa [h1] at this

/-- The joint mixes given by `frustum_sufficiency` with `q = 0`, moved to `V` by `L⁻¹`. -/
def coneMix {n : ℕ} (Φ : (Fin n → ℝ) × (Fin n → ℝ × (Fin m → ℝ)) → (ℕ → ℝ) →
    (Fin n → ℝ × (Fin m → ℝ))) (p : (Fin n → ℝ) × (Fin n → V)) (ω : ℕ → ℝ) : Fin n → V :=
  fun i => L.symm (Φ (p.1, fun j => L (p.2 j)) ω i)

omit [FiniteDimensional ℝ V] [MeasureSpace V] [(volume : Measure V).IsAddHaarMeasure] in
lemma measurable_coneMix [MeasurableSpace V] [BorelSpace V] {n : ℕ}
    {Φ : (Fin n → ℝ) × (Fin n → ℝ × (Fin m → ℝ)) → (ℕ → ℝ) → (Fin n → ℝ × (Fin m → ℝ))}
    (hΦ : Measurable (Function.uncurry Φ)) : Measurable (Function.uncurry (coneMix L Φ)) := by
  have h1 : Measurable fun z : ((Fin n → ℝ) × (Fin n → V)) × (ℕ → ℝ) =>
      Φ (z.1.1, fun j => L (z.1.2 j)) z.2 :=
    hΦ.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_pi_iff.2 fun j => L.continuous.measurable.comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))
      |>.prodMk measurable_snd)
  exact measurable_pi_iff.2 fun i =>
    L.symm.continuous.measurable.comp ((measurable_pi_apply i).comp h1)

/-- **Theorem 43 (b)** (`s:thm:cone`). Let `K` be the cone over `F = L⁻¹({1} × B)`, with `B`
measurable, bounded and of finite positive volume, and let `F` have the scaling property with
constant `m_F`. Assume Theorem 27 for the laws `G_{k,λ}` (`Thm27Frustum m 0`). Then for every
`n ≥ 2` the construction of the paper (levels `T` from Theorem 27, `S = λ - T`, slices from the
scaling property of `F`) is a Borel function `Φ` of `(λ, t)` and of a sequence of independent
uniform variables, and its law is a joint mix of `U(t₁ + λ₁K), …, U(tₙ + λₙK)` whenever
`λ ≥ 0`, not all zero, `(k + 1) max λ ≤ ∑ λ` and `m_F (k + 1) max λ ≤ k ∑ λ` (`k = m + 1`). -/
theorem cone_sufficiency (hB : MeasurableSet B) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    (hBb : Bornology.IsBounded B) {mF : ℝ} (h27 : Thm27Frustum m 0)
    (hF : ScalingProperty (sliceUnif L B 1) mF) (n : ℕ) (hn : 2 ≤ n) :
    ∃ Φ : (Fin n → ℝ) × (Fin n → V) → (ℕ → ℝ) → (Fin n → V),
      Measurable (Function.uncurry Φ) ∧
      ∀ (lam : Fin n → ℝ) (t : Fin n → V), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
        (∀ j, ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i) →
        (∀ j, mF * ((m : ℝ) + 2) * lam j ≤ ((m : ℝ) + 1) * ∑ i, lam i) →
        IsJointMix (fun i => coneUnif L B (t i) (lam i)) (unifSeq.map (Φ (lam, t))) := by
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
  have hBF : ScalingProperty (unifSet B) mF := (scalingProperty_sliceUnif_iff L).1 hF
  obtain ⟨R, hR⟩ := hBb.subset_closedBall 0
  have hBint := integrable_unifSet_of_subset hB hB0 hBt hR
  obtain ⟨Φ, hΦ, hmix⟩ := frustum_sufficiency le_rfl one_pos hB hB0 hBt hBint
    (by rw [hfin]; exact h27) hBF n hn
  refine ⟨coneMix L Φ, measurable_coneMix L hΦ, fun lam t hlam hne h1 h2 => ?_⟩
  have hμ : muKQ (Module.finrank ℝ (Fin m → ℝ) + 1) 0 = ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
    rw [hfin, muKQ_zero (by omega)]; push_cast; ring
  have hP := hmix lam (fun j => L (t j)) hlam hne (fun j => by
      rw [hμ, sub_zero, one_mul]
      have := h1 j
      rw [show 1 - ((m : ℝ) + 1) / ((m : ℝ) + 2) = 1 / ((m : ℝ) + 2) by field_simp; ring]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith)
    (fun j => by
      rw [hμ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith [h2 j])
  have hQ := hP.map_affine (L.symm : ℝ × (Fin m → ℝ) →L[ℝ] V).toLinearMap.toAddMonoidHom
    L.symm.continuous.measurable (fun _ => 0)
  have e1 : (fun i => (unifScaled (frustumSet 0 B) (L (t i)) (lam i)).map
      (fun x => (0 : V) + (L.symm : ℝ × (Fin m → ℝ) →L[ℝ] V).toLinearMap.toAddMonoidHom x)) =
      fun i => coneUnif L B (t i) (lam i) := by
    funext i
    rw [coneUnif_eq_map L (t i) (hlam i)]
    congr 1
    funext x
    simp
  have hΦl : Measurable (Φ (lam, fun j => L (t j))) := hΦ.comp measurable_prodMk_left
  have e2 : (unifSeq.map (Φ (lam, fun j => L (t j)))).map
      (fun x i => (0 : V) + (L.symm : ℝ × (Fin m → ℝ) →L[ℝ] V).toLinearMap.toAddMonoidHom (x i))
      = unifSeq.map (coneMix L Φ (lam, t)) := by
    have hg : Measurable (fun (x : Fin n → ℝ × (Fin m → ℝ)) (i : Fin n) =>
        (0 : V) + (L.symm : ℝ × (Fin m → ℝ) →L[ℝ] V).toLinearMap.toAddMonoidHom (x i)) :=
      measurable_pi_iff.2 fun i => measurable_const.add
        (L.symm.continuous.measurable.comp (measurable_pi_apply i))
    rw [Measure.map_map hg hΦl]
    congr 1
    funext ω i
    simp [coneMix]
  rw [e1, e2] at hQ
  exact hQ

/-- **Theorem 43**, last sentence: under the hypotheses of `cone_sufficiency`, the cone has
the scaling property with constant `max (k + 1) (m_F (k + 1) / k)`, `k = m + 1`. -/
theorem cone_scalingProperty (hB : MeasurableSet B) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    (hBb : Bornology.IsBounded B) {mF : ℝ} (h27 : Thm27Frustum m 0)
    (hF : ScalingProperty (sliceUnif L B 1) mF) :
    ScalingPropertySet (coneSet L B)
      (max ((m : ℝ) + 2) (mF * ((m : ℝ) + 2) / ((m : ℝ) + 1))) := by
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := cone_sufficiency L hB hB0 hBt hBb h27 hF n hn
  refine ⟨Φ, hΦ, fun lam t hlam hne hc => ?_⟩
  have e : (fun i => unifScaled (coneSet L B) (t i) (lam i)) =
      fun i => coneUnif L B (t i) (lam i) :=
    funext fun i => (coneUnif_eq_unifScaled L (t i) (hlam i)).symm
  rw [e]
  refine hmix lam t hlam hne (fun j => ?_) (fun j => ?_)
  · exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlam j)).trans (hc j)
  · have h1 := (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlam j)).trans (hc j)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    linarith

end ConeFrustum

/-! ### Translated cones -/

section Translate

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}
  (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) {B : Set (Fin m → ℝ)}

omit [FiniteDimensional ℝ V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] in
/-- `U(t + λ (a + K)) = U((t + λ a) + λ K)`. -/
lemma unifScaled_translate (a t : V) {lam : ℝ} (hlam : 0 ≤ lam) :
    unifScaled ((fun x => a + x) '' coneSet L B) t lam = coneUnif L B (t + lam • a) lam := by
  unfold unifScaled coneUnif
  rcases eq_or_lt_of_le hlam with h | h
  · subst h; simp
  · simp only [h, h.ne', ↓reduceIte, scaledTranslate_eq_image, image_image]
    congr 2
    funext x
    rw [smul_add, add_assoc]

/-- Necessity (Theorem 43 (a)) for a translated cone `a + K`. -/
theorem translate_necessity (hB : MeasurableSet B) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    (a : V) {n : ℕ} (t : Fin n → V) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (h : JointlyMixable fun i => unifScaled ((fun x => a + x) '' coneSet L B) (t i) (lam i))
    (j : Fin n) : ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i := by
  simp only [unifScaled_translate L a _ (hlam _)] at h
  exact cone_jointlyMixable_le L hB hB0 hBt (fun i => t i + lam i • a) lam hlam h j

/-- Theorem 43 (b) for a translated cone `a + K`: the scaling property with constant
`max (k + 1) (m_F (k + 1) / k)`. -/
theorem translate_scalingProperty (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (hBb : Bornology.IsBounded B) {mF : ℝ} (h27 : Thm27Frustum m 0)
    (hF : ScalingProperty (sliceUnif L B 1) mF) (a : V) :
    ScalingPropertySet ((fun x => a + x) '' coneSet L B)
      (max ((m : ℝ) + 2) (mF * ((m : ℝ) + 2) / ((m : ℝ) + 1))) := by
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := cone_scalingProperty L hB hB0 hBt hBb h27 hF n hn
  refine ⟨fun p ω => Φ (p.1, fun i => p.2 i + p.1 i • a) ω, ?_, fun lam t hlam hne hc => ?_⟩
  · exact hΦ.comp (((measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
        (((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).smul_const a)))
      |>.prodMk measurable_snd)
  · have e : (fun i => unifScaled ((fun x => a + x) '' coneSet L B) (t i) (lam i)) =
        fun i => unifScaled (coneSet L B) (t i + lam i • a) (lam i) := by
      funext i
      rw [unifScaled_translate L a (t i) (hlam i), coneUnif_eq_unifScaled L _ (hlam i)]
    rw [e]
    exact hmix lam (fun i => t i + lam i • a) hlam hne hc

omit [FiniteDimensional ℝ V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] in
lemma unifScaled_zero_one (K : Set V) : unifScaled K 0 1 = unifSet K := by
  simp [unifScaled]

/-- Joint mixability of the scaled translates of `a + K` from a scaling property with constant
`k + 1`, together with the necessity: the condition `(k + 1) max λ ≤ ∑ λ` is necessary and
sufficient. -/
theorem translate_jointlyMixable_iff (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (a : V)
    (hsc : ScalingPropertySet ((fun x => a + x) '' coneSet L B) ((m : ℝ) + 2)) {n : ℕ}
    (hn : 2 ≤ n) (t : Fin n → V) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0) :
    (JointlyMixable fun i => unifScaled ((fun x => a + x) '' coneSet L B) (t i) (lam i)) ↔
      ∀ j, ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i := by
  refine ⟨translate_necessity L hB hB0 hBt a t lam hlam, fun h => ?_⟩
  obtain ⟨Φ, -, hΦ⟩ := hsc n hn
  exact ⟨_, hΦ lam t hlam hne h⟩

/-- The threshold: for `n ≥ 1`, `U(a + K)` is `n`-completely mixable if and only if
`n ≥ k + 1 = m + 2`, given a scaling property with constant `k + 1`. -/
theorem translate_completelyMixable_iff (hB : MeasurableSet B) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (a : V)
    (hsc : ScalingPropertySet ((fun x => a + x) '' coneSet L B) ((m : ℝ) + 2)) {n : ℕ}
    (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet ((fun x => a + x) '' coneSet L B)) ↔ m + 2 ≤ n := by
  have e : (fun _ : Fin n => unifSet ((fun x => a + x) '' coneSet L B)) =
      fun i => unifScaled ((fun x => a + x) '' coneSet L B) ((fun _ => (0 : V)) i)
        ((fun _ => (1 : ℝ)) i) := by
    funext i; rw [unifScaled_zero_one]
  constructor
  · intro h
    have h' : JointlyMixable fun i : Fin n => unifScaled ((fun x => a + x) '' coneSet L B)
        ((fun _ => (0 : V)) i) ((fun _ => (1 : ℝ)) i) := by
      obtain ⟨P, hP⟩ := h; exact ⟨P, e ▸ hP⟩
    have := translate_necessity L hB hB0 hBt a _ _ (fun _ => zero_le_one) h' ⟨0, hn⟩
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    exact_mod_cast this
  · intro hle
    obtain ⟨Φ, -, hΦ⟩ := hsc n (by omega)
    have hP := hΦ (fun _ => 1) (fun _ => 0) (fun _ => zero_le_one) ⟨⟨0, by omega⟩, one_ne_zero⟩
      (fun j => by
        simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        exact_mod_cast hle)
    exact ⟨_, (e ▸ hP : IsCompleteMix n _ _)⟩

end Translate

/-! ### Linear coordinates from a basis -/

section Coords

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {m : ℕ}

/-- The linear map `x ↦ ∑ τ(x)_i w_i`. -/
def coordsLin (w : Fin (m + 1) → V) (τ : ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) :
    ℝ × (Fin m → ℝ) →ₗ[ℝ] V :=
  Fintype.linearCombination ℝ w ∘ₗ τ

lemma coordsLin_bijective {w : Fin (m + 1) → V} (hw : LinearIndependent ℝ w)
    {τ : ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)} (hτ : Function.Injective τ)
    (hV : Module.finrank ℝ V = m + 1) : Function.Bijective (coordsLin w τ) := by
  have hinj : Function.Injective (coordsLin w τ) :=
    (linearIndependent_iff_injective_fintypeLinearCombination.1 hw).comp hτ
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, hV, add_comm]

/-- Linear coordinates `L` with `L⁻¹ x = ∑ τ(x)_i w_i`. -/
def coords {w : Fin (m + 1) → V} (hw : LinearIndependent ℝ w)
    {τ : ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)} (hτ : Function.Injective τ)
    (hV : Module.finrank ℝ V = m + 1) : V ≃L[ℝ] ℝ × (Fin m → ℝ) :=
  (LinearEquiv.ofBijective _ (coordsLin_bijective hw hτ hV)).symm.toContinuousLinearEquiv

lemma coords_symm_apply {w : Fin (m + 1) → V} (hw : LinearIndependent ℝ w)
    {τ : ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)} (hτ : Function.Injective τ)
    (hV : Module.finrank ℝ V = m + 1) (x : ℝ × (Fin m → ℝ)) :
    (coords hw hτ hV).symm x = ∑ i, τ x i • w i := by
  rfl

end Coords

/-! ### Corollary 44: simplices -/

section Simplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {m : ℕ}

/-- `(s, b) ↦ (s - ∑ b, b)`. -/
def simplexTau (m : ℕ) : ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun x := Fin.cons (x.1 - ∑ j, x.2 j) x.2
  map_add' x y := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib]; ring
    · simp
  map_smul' c x := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
        RingHom.id_apply, ← Finset.mul_sum]; ring
    · simp

lemma simplexTau_apply (x : ℝ × (Fin m → ℝ)) :
    simplexTau m x = Fin.cons (x.1 - ∑ j, x.2 j) x.2 := rfl

lemma simplexTau_injective (m : ℕ) : Function.Injective (simplexTau m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨s, b⟩ h
  have hb : b = 0 := funext fun j => by simpa [simplexTau_apply] using congrFun h j.succ
  subst hb
  have := congrFun h 0
  simp only [simplexTau_apply, Fin.cons_zero, Pi.zero_apply, Finset.sum_const_zero,
    sub_zero] at this
  simp [this]

lemma convex_simplexSet (m : ℕ) : Convex ℝ (simplexSet m) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx0 i, hy0 i]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith

/-- The edge vectors `p (i + 1) - p 0` of the simplex. -/
def simplexVec (p : Fin (m + 2) → V) : Fin (m + 1) → V := fun i => p i.succ - p 0

omit [FiniteDimensional ℝ V] in
lemma linearIndependent_simplexVec {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p) :
    LinearIndependent ℝ (simplexVec p) := by
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ p 0).1 hp
  have h2 := h.comp
    (fun i : Fin (m + 1) => (⟨i.succ, Fin.succ_ne_zero i⟩ : {x : Fin (m + 2) // x ≠ 0}))
    (fun i j hij => Fin.succ_injective _ (congrArg Subtype.val hij))
  convert h2 using 1
  funext i
  simp [simplexVec, vsub_eq_sub]

/-- The coordinates of the simplex: `L⁻¹ (s, b) = s v₀ + ∑ b_j (v_{j+1} - v₀)` with the edge
vectors `v_i = p (i + 1) - p 0`; `ℓ` is the functional with `ℓ(v_i) = 1`. -/
def simplexCoords {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) : V ≃L[ℝ] ℝ × (Fin m → ℝ) :=
  coords (linearIndependent_simplexVec hp) (simplexTau_injective m) hV

lemma simplexCoords_symm_apply {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) (x : ℝ × (Fin m → ℝ)) :
    (simplexCoords hp hV).symm x = Fintype.linearCombination ℝ (simplexVec p) (simplexTau m x) :=
  rfl

/-- The cone over `L⁻¹({1} × Δ_{m})` is the image of the corner simplex of dimension `m + 1`
under `c ↦ ∑ c_i v_i`. -/
lemma coneSet_simplexCoords {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) :
    coneSet (simplexCoords hp hV) (simplexSet m) =
      Fintype.linearCombination ℝ (simplexVec p) '' simplexSet (m + 1) := by
  set lin := Fintype.linearCombination ℝ (simplexVec p)
  ext x
  constructor
  · rintro ⟨s, hs, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨s • simplexTau m (1, b), ⟨fun i => ?_, ?_⟩, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Pi.smul_apply, simplexTau_apply, Fin.cons_zero, smul_eq_mul]
        exact mul_nonneg hs.1 (by linarith [hb.2])
      · simp only [Pi.smul_apply, simplexTau_apply, Fin.cons_succ, smul_eq_mul]
        exact mul_nonneg hs.1 (hb.1 j)
    · simp only [Pi.smul_apply, simplexTau_apply, smul_eq_mul, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
      nlinarith [hs.2]
    · rw [map_smul, simplexCoords_symm_apply]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    have hsplit : ∑ i, c i = c 0 + ∑ j : Fin m, c j.succ := Fin.sum_univ_succ c
    set S := ∑ i, c i
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hc0 i
    rcases eq_or_lt_of_le hS0 with h | h
    · have hc : c = 0 := funext fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc0 i)).1 h.symm i (Finset.mem_univ i)
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, _, ⟨0, ⟨fun _ => le_rfl, by simp⟩, rfl⟩, ?_⟩
      rw [hc, map_zero, zero_smul]
    · refine ⟨S, ⟨hS0, hc1⟩, _, ⟨fun j => c j.succ / S, ⟨fun j => div_nonneg (hc0 _) hS0,
        ?_⟩, rfl⟩, ?_⟩
      · rw [← Finset.sum_div, div_le_one h]; linarith [hc0 0]
      · rw [simplexCoords_symm_apply, ← map_smul]
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Pi.smul_apply, simplexTau_apply, Fin.cons_zero, smul_eq_mul,
            ← Finset.sum_div]
          field_simp
          linarith
        · simp only [Pi.smul_apply, simplexTau_apply, Fin.cons_succ, smul_eq_mul]
          field_simp

/-- A `k`-simplex (`k = m + 1`) is a translate of a cone: `conv (p 0, …, p k) = p 0 + K`. -/
lemma convexHull_eq_translate_cone {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) :
    convexHull ℝ (range p) =
      (fun x => p 0 + x) '' coneSet (simplexCoords hp hV) (simplexSet m) := by
  rw [coneSet_simplexCoords]
  set lin := Fintype.linearCombination ℝ (simplexVec p)
  apply Subset.antisymm
  · refine convexHull_min ?_ (((convex_simplexSet (m + 1)).linear_image lin).translate (p 0))
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨0, ⟨0, ⟨fun _ => le_rfl, by simp⟩, map_zero lin⟩, add_zero _⟩
    · refine ⟨lin (Pi.single j 1), ⟨Pi.single j 1, ⟨fun i => ?_, ?_⟩, rfl⟩, ?_⟩
      · by_cases h : i = j
        · subst h; simp
        · simp [h]
      · simp
      · simp [lin, simplexVec]
  · rintro _ ⟨_, ⟨c, ⟨hc0, hc1⟩, rfl⟩, rfl⟩
    let W : Fin (m + 2) → ℝ := Fin.cons (1 - ∑ i, c i) c
    have hmem := (convex_convexHull ℝ (range p)).sum_mem (t := Finset.univ) (w := W) (z := p)
      (fun i _ => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [W, Fin.cons_zero]; linarith
        · simp only [W, Fin.cons_succ]; exact hc0 j)
      (by simp [W, Fin.sum_univ_succ])
      (fun i _ => subset_convexHull ℝ _ (mem_range_self i))
    convert hmem using 1
    simp only [W, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, lin,
      Fintype.linearCombination_apply, simplexVec, smul_sub, Finset.sum_sub_distrib, sub_smul,
      one_smul, Finset.sum_smul, add_smul]
    abel

variable [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

lemma isBounded_simplexSet (m : ℕ) : Bornology.IsBounded (simplexSet m) :=
  Metric.isBounded_closedBall.subset (simplexSet_subset_ball m)

/-- **Corollary 44** (`s:cor:simplex`), the scaling property: given Theorem 27 for the laws
`G_{k,λ}` in every dimension, every `k`-simplex `Δ = conv (p 0, …, p k)` (`p` affinely
independent, `k = m + 1 = dim V`) has the scaling property with constant `k + 1`. -/
theorem simplex_scalingPropertySet (h27 : ∀ m', Thm27Frustum m' 0) {p : Fin (m + 2) → V}
    (hp : AffineIndependent ℝ p) (hV : Module.finrank ℝ V = m + 1) :
    ScalingPropertySet (convexHull ℝ (range p)) ((m : ℝ) + 2) := by
  rw [convexHull_eq_translate_cone hp hV]
  have hF := (scalingProperty_sliceUnif_iff (simplexCoords hp hV)).2 (simplex_scalingProperty h27 m)
  have := translate_scalingProperty (simplexCoords hp hV) (measurableSet_simplexSet m)
    (volume_simplexSet_ne_zero m) (volume_simplexSet_ne_top m) (isBounded_simplexSet m) (h27 m)
    hF (p 0)
  have hmax : max ((m : ℝ) + 2) (((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 1)) =
      (m : ℝ) + 2 := by
    rw [mul_div_cancel_left₀ _ (by positivity), max_self]
  rwa [hmax] at this

/-- **Corollary 44** (`s:cor:simplex`): given Theorem 27 for the laws `G_{k,λ}` in every
dimension, for a `k`-simplex `Δ` (`k = m + 1`), `n ≥ 2`, `t_i ∈ V` and `λ_i ≥ 0` not all zero,
`U(t₁ + λ₁Δ), …, U(tₙ + λₙΔ)` are jointly mixable if and only if `(k + 1) max λ ≤ ∑ λ`. -/
theorem simplex_jointlyMixable_iff (h27 : ∀ m', Thm27Frustum m' 0) {p : Fin (m + 2) → V}
    (hp : AffineIndependent ℝ p) (hV : Module.finrank ℝ V = m + 1) {n : ℕ} (hn : 2 ≤ n)
    (t : Fin n → V) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0) :
    (JointlyMixable fun i => unifScaled (convexHull ℝ (range p)) (t i) (lam i)) ↔
      ∀ j, ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i := by
  have hsc := simplex_scalingPropertySet h27 hp hV
  rw [convexHull_eq_translate_cone hp hV] at hsc ⊢
  exact translate_jointlyMixable_iff _ (measurableSet_simplexSet m)
    (volume_simplexSet_ne_zero m) (volume_simplexSet_ne_top m) (p 0) hsc hn t lam hlam hne

/-- **Corollary 44**, last sentence: given Theorem 27, for `n ≥ 1` the uniform distribution on
a `d`-simplex (`d = m + 1`) is `n`-completely mixable if and only if `n ≥ d + 1`. -/
theorem simplex_completelyMixable_iff (h27 : ∀ m', Thm27Frustum m' 0) {p : Fin (m + 2) → V}
    (hp : AffineIndependent ℝ p) (hV : Module.finrank ℝ V = m + 1) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (convexHull ℝ (range p))) ↔ m + 2 ≤ n := by
  have hsc := simplex_scalingPropertySet h27 hp hV
  rw [convexHull_eq_translate_cone hp hV] at hsc ⊢
  exact translate_completelyMixable_iff _ (measurableSet_simplexSet m)
    (volume_simplexSet_ne_zero m) (volume_simplexSet_ne_top m) (p 0) hsc hn

/-- Corollary 44, necessity, unconditionally: if the `U(t_i + λ_i Δ)` are jointly mixable then
`(k + 1) max λ ≤ ∑ λ`. -/
theorem simplex_necessity {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) {n : ℕ} (t : Fin n → V) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (h : JointlyMixable fun i => unifScaled (convexHull ℝ (range p)) (t i) (lam i)) (j : Fin n) :
    ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i := by
  rw [convexHull_eq_translate_cone hp hV] at h
  exact translate_necessity _ (measurableSet_simplexSet m) (volume_simplexSet_ne_zero m)
    (volume_simplexSet_ne_top m) (p 0) t lam hlam h j

end Simplex

/-! ### The scaling property of the cube (Lemma 1, with Borel dependence) -/

section Cube

/-- A Borel sample of the planar Archimedes measure from a sequence of independent uniform
variables (only the first one is used): the quantile representation of a probability measure on
a standard Borel space (`Measure.exists_measurable_map_eq` of Mathlib). -/
lemma exists_archSample : ∃ g : (ℕ → ℝ) → EuclideanSpace ℝ (Fin 2),
    Measurable g ∧ unifSeq.map g = archPlane := by
  have : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1
  obtain ⟨f, hf, hfmap⟩ := Measure.exists_measurable_map_eq archPlane
  have hp : Measurable fun ω : ℕ → ℝ => Set.projIcc (0 : ℝ) 1 zero_le_one (ω 0) :=
    continuous_projIcc.measurable.comp (measurable_pi_apply 0)
  refine ⟨fun ω => f (Set.projIcc 0 1 zero_le_one (ω 0)), hf.comp hp, ?_⟩
  have h1 : unifSeq.map (fun ω : ℕ → ℝ => ω 0) = unifI 0 1 := by
    unfold unifSeq; exact Measure.infinitePi_map_eval _ 0
  have h2 : (unifI 0 1).map (Set.projIcc (0 : ℝ) 1 zero_le_one) =
      (volume : Measure unitInterval) := by
    have hI : unifI 0 1 = volume.restrict unitInterval := by
      simp [unifI, unitInterval]
    rw [hI, ← unitInterval.measurePreserving_subtypeVal.map_eq,
      Measure.map_map continuous_projIcc.measurable measurable_subtypeVal]
    have : (Set.projIcc (0 : ℝ) 1 zero_le_one ∘ Subtype.val : unitInterval → unitInterval) = id :=
      funext fun x => Set.projIcc_val zero_le_one x
    rw [this, Measure.map_id]
  calc unifSeq.map (fun ω => f (Set.projIcc 0 1 zero_le_one (ω 0)))
      = ((unifSeq.map (fun ω : ℕ → ℝ => ω 0)).map (Set.projIcc (0 : ℝ) 1 zero_le_one)).map f := by
        have he : Measurable fun ω : ℕ → ℝ => ω 0 := measurable_pi_apply 0
        have hq : Measurable (Set.projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc.measurable
        rw [Measure.map_map hq he, Measure.map_map hf (hq.comp he)]
        rfl
    _ = archPlane := by rw [h1, h2, hfmap]

lemma unifSet_Icc01 : unifSet (Icc (0 : ℝ) 1) = unifI 0 1 := by
  simp [unifI, unifSet, Real.volume_Icc]

lemma unifI01_map_affine (t : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (unifI 0 1).map (fun x => t + c • x) = unifI t (t + c) := by
  have := unifI_isProb 0 1
  rcases eq_or_lt_of_le hc with h | h
  · subst h
    simp only [zero_smul, add_zero]
    rw [Measure.map_const, measure_univ, one_smul]
    simp [unifI]
  · have e : (fun x : ℝ => t + c • x) = (fun x => t + x) ∘ (fun x => c * x) := by
      funext x; simp [smul_eq_mul]
    rw [e, ← Measure.map_map (measurable_const_add t) (measurable_const_mul c),
      map_unifI_const_mul h, map_unifI_const_add]
    simp

/-- **Lemma 1** (`lem:arch`) as a scaling property: the segment `[0, 1]` has the scaling property
with constant `2`, with a joint mix that is a Borel function of `(λ, t)` and of a uniform
sequence (the choices of Lemma 1 made measurably as in `Assembly.chordVec`). -/
theorem scalingProperty_Icc : ScalingProperty (unifSet (Icc (0 : ℝ) 1)) 2 := by
  obtain ⟨g, hg, hgmap⟩ := exists_archSample
  intro n hn
  have hcv := Assembly.measurable_chordVec (n := n) 0 0 0
  refine ⟨fun p ω i => p.2 i + Assembly.chordVec 0 0 0 p.1 (g ω) i, ?_, ?_⟩
  · have h1 : Measurable fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ) =>
        Assembly.chordVec 0 0 0 z.1.1 (g z.2) :=
      hcv.comp (f := fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ) => (z.1.1, g z.2))
        ((measurable_fst.comp measurable_fst).prodMk (hg.comp measurable_snd))
    exact measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp
      (measurable_snd.comp measurable_fst)).add ((measurable_pi_apply i).comp h1)
  · intro lam t hlam hne hm
    have htr : ∀ x, trapH 0 x = x := fun x => by simp [trapH]
    have hx : Assembly.LemOneHyp fun j => trapH 0 (lam j) := by
      simp only [htr]
      obtain ⟨j, hj⟩ := hne
      exact ⟨hlam, ⟨j, lt_of_le_of_ne (hlam j) (Ne.symm hj)⟩, hm⟩
    obtain ⟨hJ, -⟩ := Assembly.chordVec_spec 0 0 0 lam hx
    have hQ := hJ.map_affine (AddMonoidHom.id ℝ) measurable_id t
    simp only [AddMonoidHom.id_apply] at hQ
    have hcvl : Measurable (Assembly.chordVec (n := n) 0 0 0 lam) :=
      hcv.comp (f := fun ξ => (lam, ξ)) measurable_prodMk_left
    have hT : Measurable (fun (x : Fin n → ℝ) (i : Fin n) => t i + x i) :=
      measurable_pi_iff.2 fun i => measurable_const.add (measurable_pi_apply i)
    have e2 : unifSeq.map (fun ω i => t i + Assembly.chordVec 0 0 0 lam (g ω) i) =
        (archPlane.map (Assembly.chordVec 0 0 0 lam)).map (fun x i => t i + x i) := by
      rw [← hgmap, Measure.map_map hcvl hg, Measure.map_map hT (hcvl.comp hg)]
      rfl
    have e1 : (fun i => (unifSet (Icc (0 : ℝ) 1)).map (fun x => t i + lam i • x)) =
        fun i => (Assembly.chord 0 0 0 (lam i)).map (fun x => t i + x) := by
      funext i
      rw [unifSet_Icc01, unifI01_map_affine _ (hlam i)]
      simp only [Assembly.chord, htr, zero_mul, add_zero, zero_add]
      rw [map_unifI_const_add, add_zero]
    show IsJointMix _ (unifSeq.map (fun ω i => t i + Assembly.chordVec 0 0 0 lam (g ω) i))
    rw [e1, e2]
    exact hQ

/-- `(x, y) ↦ Fin.cons x y`. -/
def consLin (m : ℕ) : ℝ × (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun p := Fin.cons p.1 p.2
  map_add' p q := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c p := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma consLin_apply (m : ℕ) (p : ℝ × (Fin m → ℝ)) : consLin m p = Fin.cons p.1 p.2 := rfl

lemma consLin_injective (m : ℕ) : Function.Injective (consLin m) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [consLin_apply, Fin.cons_inj] at h
  rw [h.1, h.2]

lemma scalingProperty_cube_zero (c : ℝ) : ScalingProperty (unifSet (cubeSet 0)) c := by
  have := unifSet_isProb (K := cubeSet 0) (by rw [volume_cubeSet]; exact one_ne_zero)
    (by rw [volume_cubeSet]; exact ENNReal.one_ne_top)
  intro n _
  refine ⟨fun _ _ _ => 0, measurable_const, fun lam t _ _ _ => ?_⟩
  refine ⟨inferInstance, ⟨0, Filter.Eventually.of_forall fun x => Subsingleton.elim _ _⟩,
    fun j => ?_⟩
  ext S hS
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  · have hS' : S = univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    simp [hS']

/-- **The base of Corollary 45**: the cube `[0,1]^m` has the scaling property with constant
`2`, by Lemma 1 applied to each coordinate with independent randomness (Lemma 53 for products),
unconditionally. -/
theorem scalingProperty_cube : ∀ m : ℕ, ScalingProperty (unifSet (cubeSet m)) 2
  | 0 => scalingProperty_cube_zero 2
  | m' + 1 => by
    have hi0 : volume (Icc (0 : ℝ) 1) ≠ 0 := by simp
    have hit : volume (Icc (0 : ℝ) 1) ≠ ⊤ := by simp
    have hc0 : volume (cubeSet m') ≠ 0 := by rw [volume_cubeSet]; exact one_ne_zero
    have hct : volume (cubeSet m') ≠ ⊤ := by rw [volume_cubeSet]; exact ENNReal.one_ne_top
    have := unifSet_isProb hi0 hit
    have := unifSet_isProb hc0 hct
    have hprod := scalingProperty_prod scalingProperty_Icc (scalingProperty_cube m')
    rw [max_self] at hprod
    have hmap := scalingProperty_map_affine hprod (consLin m').toContinuousLinearMap 0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 1) => ℝ) 0
    have he : (unifSet (cubeSet (m' + 1))).map e = (unifSet (Icc (0 : ℝ) 1)).prod
        (unifSet (cubeSet m')) := by
      rw [cubeSet_succ, unifSet_map_preimage _ (measurePreserving_piFinSuccAbove_zero m'),
        unifSet_prod hi0 hit hc0 hct]
    have hfun : (fun x => (consLin m').toContinuousLinearMap x + 0) = e.symm := by
      funext x
      simp [e, consLin_apply, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [hfun, ← he, Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self,
      Measure.map_id] at hmap
    exact hmap

end Cube

/-! ### Corollary 45: pyramids over parallelotopes -/

section Pyramid

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {m : ℕ}

/-- The parallelotope `{o + ∑ c_j u_j : c ∈ [0,1]^m}`. -/
def parallelotope (o : V) (u : Fin m → V) : Set V :=
  {x | ∃ c ∈ cubeSet m, x = o + ∑ j, c j • u j}

omit [FiniteDimensional ℝ V] in
lemma parallelotope_eq (o : V) (u : Fin m → V) :
    parallelotope o u = (fun x => o + x) '' (Fintype.linearCombination ℝ u '' cubeSet m) := by
  ext x
  simp only [parallelotope, mem_ofPred_eq, mem_image, Fintype.linearCombination_apply,
    exists_exists_and_eq_and]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

omit [FiniteDimensional ℝ V] in
lemma convex_parallelotope (o : V) (u : Fin m → V) : Convex ℝ (parallelotope o u) := by
  rw [parallelotope_eq]
  exact ((convex_pi fun _ _ => convex_Icc (0 : ℝ) 1).linear_image _).translate o

omit [FiniteDimensional ℝ V] in
/-- If the apex `a` lies outside the affine hull of the parallelotope, then `o - a` is not in the
span of the edge vectors. -/
lemma sub_notMem_span {o a : V} {u : Fin m → V} (ha : a ∉ affineSpan ℝ (parallelotope o u)) :
    o - a ∉ Submodule.span ℝ (range u) := by
  intro h
  apply ha
  have ho : o ∈ parallelotope o u := ⟨0, fun _ _ => ⟨le_rfl, zero_le_one⟩, by simp⟩
  have hsp : Submodule.span ℝ (range u) ≤ (affineSpan ℝ (parallelotope o u)).direction := by
    rw [direction_affineSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : o + u j ∈ parallelotope o u := by
      refine ⟨Pi.single j 1, fun i _ => ?_, by simp⟩
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have := vsub_mem_vectorSpan ℝ hj ho
    simpa using this
  have := AffineSubspace.vadd_mem_of_mem_direction (neg_mem (hsp h))
    (subset_affineSpan ℝ _ ho)
  simpa using this

/-- The coordinates of the pyramid: `L⁻¹ (s, b) = s (o - a) + ∑ b_j u_j`. -/
def pyramidCoords {o a : V} {u : Fin m → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m + 1) :
    V ≃L[ℝ] ℝ × (Fin m → ℝ) :=
  coords (hu.finCons (sub_notMem_span ha)) (consLin_injective m) hV

lemma pyramidCoords_symm_apply {o a : V} {u : Fin m → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m + 1)
    (x : ℝ × (Fin m → ℝ)) :
    (pyramidCoords hu ha hV).symm x = x.1 • (o - a) + ∑ j, x.2 j • u j := by
  rw [pyramidCoords, coords_symm_apply, Fin.sum_univ_succ]
  simp [consLin_apply]

/-- A pyramid over a parallelotope is a translate of a cone over a cube:
`conv ({a} ∪ Q) = a + K` with `K` the cone over `L⁻¹({1} × [0,1]^m)`. -/
lemma convexHull_pyramid_eq {o a : V} {u : Fin m → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m + 1) :
    convexHull ℝ (insert a (parallelotope o u)) =
      (fun x => a + x) '' coneSet (pyramidCoords hu ha hV) (cubeSet m) := by
  have hne : (parallelotope o u).Nonempty := ⟨o, 0, fun _ _ => ⟨le_rfl, zero_le_one⟩, by simp⟩
  rw [convexHull_insert hne, (convex_parallelotope o u).convexHull_eq,
    convexJoin_singleton_left]
  ext x
  simp only [mem_iUnion, segment_eq_image', mem_image, coneSet, coneBase, mem_ofPred_eq,
    parallelotope, exists_prop]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, θ, hθ, rfl⟩
    refine ⟨θ • (pyramidCoords hu ha hV).symm (1, c), ⟨θ, hθ, _, ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
    rw [pyramidCoords_symm_apply]
    congr 2
    simp only [one_smul]
    abel
  · rintro ⟨_, ⟨θ, hθ, _, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨c, hc, rfl⟩, θ, hθ, ?_⟩
    rw [pyramidCoords_symm_apply]
    congr 2
    simp only [one_smul]
    abel

variable [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

lemma isBounded_cubeSet (m : ℕ) : Bornology.IsBounded (cubeSet m) := by
  rw [cubeSet, pi_univ_Icc]; exact Metric.isBounded_Icc _ _

lemma volume_cubeSet_ne_zero (m : ℕ) : volume (cubeSet m) ≠ 0 := by
  rw [volume_cubeSet]; exact one_ne_zero

lemma volume_cubeSet_ne_top (m : ℕ) : volume (cubeSet m) ≠ ⊤ := by
  rw [volume_cubeSet]; exact ENNReal.one_ne_top

/-- **Corollary 45** (`s:cor:pyramid`), the scaling property: given Theorem 27 for the laws
`G_{d,λ}`, every pyramid `P = conv ({a} ∪ Q)` over a `(d-1)`-dimensional parallelotope
`Q = {o + ∑ c_j u_j : c ∈ [0,1]^{d-1}}` (`u` linearly independent) with apex `a` outside the
affine hull of `Q`, in a space of dimension `d = m' + 2 ≥ 2`, has the scaling property with
constant `d + 1`. -/
theorem pyramid_scalingPropertySet {m' : ℕ} (h27 : Thm27Frustum (m' + 1) 0) {o a : V}
    {u : Fin (m' + 1) → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m' + 2) :
    ScalingPropertySet (convexHull ℝ (insert a (parallelotope o u))) (((m' + 1 : ℕ) : ℝ) + 2) := by
  rw [convexHull_pyramid_eq hu ha hV]
  have hF := (scalingProperty_sliceUnif_iff (pyramidCoords hu ha hV)).2 (scalingProperty_cube _)
  have := translate_scalingProperty (pyramidCoords hu ha hV) (measurableSet_cubeSet _)
    (volume_cubeSet_ne_zero _) (volume_cubeSet_ne_top _) (isBounded_cubeSet _) h27 hF a
  have hmax : max (((m' + 1 : ℕ) : ℝ) + 2) (2 * (((m' + 1 : ℕ) : ℝ) + 2) /
      (((m' + 1 : ℕ) : ℝ) + 1)) = ((m' + 1 : ℕ) : ℝ) + 2 := by
    refine max_eq_left ?_
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
    push_cast
    nlinarith
  rwa [hmax] at this

/-- **Corollary 45** (`s:cor:pyramid`): given Theorem 27 for the laws `G_{d,λ}`, for a pyramid
`P` over a parallelotope in dimension `d = m' + 2 ≥ 2`, `n ≥ 2`, `t_i ∈ V` and `λ_i ≥ 0` not all
zero, `U(t₁ + λ₁P), …, U(tₙ + λₙP)` are jointly mixable if and only if
`(d + 1) max λ ≤ ∑ λ`. -/
theorem pyramid_jointlyMixable_iff {m' : ℕ} (h27 : Thm27Frustum (m' + 1) 0) {o a : V}
    {u : Fin (m' + 1) → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m' + 2) {n : ℕ}
    (hn : 2 ≤ n) (t : Fin n → V) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0) :
    (JointlyMixable fun i => unifScaled (convexHull ℝ (insert a (parallelotope o u))) (t i)
      (lam i)) ↔ ∀ j, ((m' : ℝ) + 3) * lam j ≤ ∑ i, lam i := by
  have hsc := pyramid_scalingPropertySet h27 hu ha hV
  have hc : ((m' + 1 : ℕ) : ℝ) + 2 = (m' : ℝ) + 3 := by push_cast; ring
  rw [convexHull_pyramid_eq hu ha hV] at hsc ⊢
  rw [← hc]
  exact translate_jointlyMixable_iff _ (measurableSet_cubeSet _) (volume_cubeSet_ne_zero _)
    (volume_cubeSet_ne_top _) a hsc hn t lam hlam hne

/-- **Corollary 45**, last sentence: given Theorem 27, for `n ≥ 1` the uniform distribution on a
pyramid over a parallelotope in dimension `d = m' + 2` is `n`-completely mixable if and only if
`n ≥ d + 1`. -/
theorem pyramid_completelyMixable_iff {m' : ℕ} (h27 : Thm27Frustum (m' + 1) 0) {o a : V}
    {u : Fin (m' + 1) → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m' + 2) {n : ℕ}
    (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (convexHull ℝ (insert a (parallelotope o u)))) ↔ m' + 3 ≤ n := by
  have hsc := pyramid_scalingPropertySet h27 hu ha hV
  rw [convexHull_pyramid_eq hu ha hV] at hsc ⊢
  exact translate_completelyMixable_iff _ (measurableSet_cubeSet _) (volume_cubeSet_ne_zero _)
    (volume_cubeSet_ne_top _) a hsc hn

/-- Corollary 45, necessity, unconditionally. -/
theorem pyramid_necessity {m' : ℕ} {o a : V} {u : Fin (m' + 1) → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (parallelotope o u)) (hV : Module.finrank ℝ V = m' + 2) {n : ℕ}
    (t : Fin n → V) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (h : JointlyMixable fun i => unifScaled (convexHull ℝ (insert a (parallelotope o u))) (t i)
      (lam i)) (j : Fin n) :
    ((m' : ℝ) + 3) * lam j ≤ ∑ i, lam i := by
  rw [convexHull_pyramid_eq hu ha hV] at h
  have := translate_necessity _ (measurableSet_cubeSet _) (volume_cubeSet_ne_zero _)
    (volume_cubeSet_ne_top _) a t lam hlam h j
  push_cast at this
  linarith

end Pyramid

/-! ### Remark 46: the tetrahedron with Lemma 1 only -/

section Tetra

lemma ite_of {c : Prop} [Decidable c] {α : Sort*} {a b : α} (h : c) : ite c a b = a := by
  simp [h]

lemma ite_of_not {c : Prop} [Decidable c] {α : Sort*} {a b : α} (h : ¬c) : ite c a b = b := by
  simp [h]

/-- The tetrahedron of Remark 46: `{(x, y, z) : 0 ≤ x ≤ 1, 0 ≤ y ≤ 1 - x, 0 ≤ z ≤ x}`. -/
def tetraSet : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ 1 - p.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ p.1}

lemma measurableSet_tetraSet : MeasurableSet tetraSet := by
  unfold tetraSet
  refine (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
    ((measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
    ((measurableSet_le (measurable_fst.comp measurable_snd)
      (measurable_const.sub measurable_fst)).inter
    ((measurableSet_le measurable_const (measurable_snd.comp measurable_snd)).inter
      (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)))))

/-- The section of the tetrahedron at `x ∈ [0, 1]` is the rectangle `[0, 1 - x] × [0, x]`. -/
lemma slice_tetraSet (A : Set (ℝ × ℝ × ℝ)) (x : ℝ) :
    Prod.mk x ⁻¹' (A ∩ tetraSet) =
      if x ∈ Icc (0 : ℝ) 1 then Prod.mk x ⁻¹' A ∩ (Icc 0 (1 - x) ×ˢ Icc 0 x) else ∅ := by
  ext ⟨y, z⟩
  split_ifs with hx
  · simp only [mem_preimage, mem_inter_iff, tetraSet, mem_ofPred_eq, mem_prod, mem_Icc]
    constructor
    · rintro ⟨h, -, -, h1, h2, h3, h4⟩; exact ⟨h, ⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨h, ⟨h1, h2⟩, h3, h4⟩; exact ⟨h, hx.1, hx.2, h1, h2, h3, h4⟩
  · simp only [mem_preimage, mem_inter_iff, tetraSet, mem_ofPred_eq, mem_empty_iff_false,
      iff_false, not_and]
    intro _ h0 h1; exact absurd ⟨h0, h1⟩ hx

/-- `g_A(x)`: the area of the section of `A ∩ T` at `x`. -/
def secArea (A : Set (ℝ × ℝ × ℝ)) (x : ℝ) : ENNReal := volume (Prod.mk x ⁻¹' (A ∩ tetraSet))

lemma measurable_secArea {A : Set (ℝ × ℝ × ℝ)} (hA : MeasurableSet A) :
    Measurable (secArea A) :=
  measurable_measure_prodMk_left (hA.inter measurableSet_tetraSet)

/-- Fubini: `vol (A ∩ T) = ∫ g_A`. -/
lemma volume_inter_tetraSet {A : Set (ℝ × ℝ × ℝ)} (hA : MeasurableSet A) :
    volume (A ∩ tetraSet) = ∫⁻ x in Icc (0 : ℝ) 1, secArea A x := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (hA.inter measurableSet_tetraSet),
    ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]; rfl
  · rw [indicator_of_notMem hx, slice_tetraSet, ite_of_not hx,
      measure_empty]

lemma secArea_univ {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    secArea univ x = ENNReal.ofReal ((1 - x) * x) := by
  rw [secArea, slice_tetraSet, ite_of hx, preimage_univ, univ_inter, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero,
    ← ENNReal.ofReal_mul (by linarith [hx.2])]

lemma volume_tetraSet : volume tetraSet = ENNReal.ofReal (1 / 6) := by
  have := volume_inter_tetraSet MeasurableSet.univ
  rw [univ_inter] at this
  rw [this, setLIntegral_congr_fun measurableSet_Icc (fun x hx => secArea_univ hx),
    ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [show (fun x : ℝ => (1 - x) * x) = fun x => x - x ^ 2 by funext x; ring,
      intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun x : ℝ => x ^ 2)
        (continuous_id'.intervalIntegrable 0 1) ((continuous_pow 2).intervalIntegrable 0 1),
      integral_id, integral_pow]
    norm_num
  · exact (by fun_prop : Continuous fun x : ℝ => (1 - x) * x).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg (by linarith [hx.2]) hx.1

/-- `U(T)(A) = 6 ∫ g_A`. -/
lemma unifSet_tetraSet_apply {A : Set (ℝ × ℝ × ℝ)} (hA : MeasurableSet A) :
    unifSet tetraSet A = 6 * ∫⁻ x in Icc (0 : ℝ) 1, secArea A x := by
  rw [unifSet, smul_apply, Measure.restrict_apply hA, volume_inter_tetraSet hA, volume_tetraSet,
    smul_eq_mul]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The conditional law of `(y, z)` given the abscissa `x`: `U[0, 1 - x] ⊗ U[0, x]`. -/
def secLaw (x : ℝ) : Measure (ℝ × ℝ) := (unifI 0 (1 - x)).prod (unifI 0 x)

lemma secLaw_apply {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {C : Set (ℝ × ℝ)} (hC : MeasurableSet C) :
    secLaw x C = (ENNReal.ofReal (1 - x))⁻¹ * (ENNReal.ofReal x)⁻¹ *
      volume (C ∩ (Icc 0 (1 - x) ×ˢ Icc 0 x)) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  rw [secLaw, unifI, unifI, ite_of h1, ite_of hx.1, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.prod_restrict, ← Measure.volume_eq_prod, smul_apply,
    smul_apply, Measure.restrict_apply hC, sub_zero, sub_zero, smul_eq_mul, smul_eq_mul,
    mul_assoc]

/-- The density `h_A(x) = g_A(x) / (x (1 - x))` of `x ↦ secLaw x (A_x)`. -/
def secDens (A : Set (ℝ × ℝ × ℝ)) (x : ℝ) : ENNReal :=
  (ENNReal.ofReal (1 - x))⁻¹ * (ENNReal.ofReal x)⁻¹ * secArea A x

lemma measurable_secDens {A : Set (ℝ × ℝ × ℝ)} (hA : MeasurableSet A) :
    Measurable (secDens A) :=
  (((measurable_const.sub measurable_id).ennreal_ofReal.inv).mul
    measurable_id.ennreal_ofReal.inv).mul (measurable_secArea hA)

lemma secLaw_slice {A : Set (ℝ × ℝ × ℝ)} (hA : MeasurableSet A) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : secLaw x (Prod.mk x ⁻¹' A) = secDens A x := by
  rw [secLaw_apply hx (measurable_prodMk_left hA), secDens, secArea, slice_tetraSet,
    ite_of (Ioo_subset_Icc_self hx)]

/-- The law of the level `v` in the decomposition of the abscissa: density `3 v²` on `[0, 1]`. -/
def rhoLaw : Measure ℝ :=
  (volume.restrict (Icc 0 1)).withDensity fun v => ENNReal.ofReal (3 * v ^ 2)

lemma rhoLaw_isProb : IsProbabilityMeasure rhoLaw := by
  constructor
  rw [rhoLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · exact (by fun_prop : Continuous fun v : ℝ => 3 * v ^ 2).integrableOn_Icc
  · exact Filter.Eventually.of_forall fun v => by positivity

lemma rhoLaw_ae_mem : ∀ᵐ v ∂rhoLaw, v ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) 1)), v ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 0 ∧ v ≠ 1 := by
      filter_upwards [Measure.ae_ne volume 0, Measure.ae_ne volume 1] with v h0 h1
      exact ⟨h0, h1⟩
    filter_upwards [this] with v hv hv'
    exact ⟨lt_of_le_of_ne hv'.1 (Ne.symm hv.1), lt_of_le_of_ne hv'.2 hv.2⟩
  exact (withDensity_absolutelyContinuous _ _).ae_le h

lemma mem_Icc_half_iff {v s : ℝ} : s ∈ Icc (1 / 2 - v / 2) (1 / 2 + v / 2) ↔ |2 * s - 1| ≤ v := by
  rw [mem_Icc, abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma lintegral_Icc_three_mul {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫⁻ v in Icc a 1, ENNReal.ofReal (3 * v) = ENNReal.ofReal (3 / 2 * (1 - a ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha1,
      intervalIntegral.integral_const_mul, integral_id]
    congr 1; ring
  · exact (by fun_prop : Continuous fun v : ℝ => 3 * v).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    simp only [Pi.zero_apply]
    linarith [hv.1]

/-- **Khintchine's decomposition** of the abscissa density `6 x (1 - x)`: it is the mixture over
`v ∼ 3 v² dv` of the uniform distributions on `[1/2 - v/2, 1/2 + v/2]`. -/
theorem khintchine {h : ℝ → ENNReal} (hh : Measurable h) :
    ∫⁻ v, (∫⁻ s, h s ∂unifI (1 / 2 - v / 2) (1 / 2 + v / 2)) ∂rhoLaw =
      ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (6 * s * (1 - s)) * h s := by
  set S : Set (ℝ × ℝ) := {p | |2 * p.2 - 1| ≤ p.1}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_fst
  set G : ℝ × ℝ → ENNReal := S.indicator fun p => ENNReal.ofReal (3 * p.1) * h p.2
  have hG : Measurable G := (((measurable_fst.const_mul 3).ennreal_ofReal).mul
    (hh.comp measurable_snd)).indicator hS
  rw [rhoLaw, lintegral_withDensity_eq_lintegral_mul_non_measurable _ (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h1 : ∀ v ∈ Icc (0 : ℝ) 1, ((fun v => ENNReal.ofReal (3 * v ^ 2)) *
      fun v => ∫⁻ s, h s ∂unifI (1 / 2 - v / 2) (1 / 2 + v / 2)) v = ∫⁻ s, G (v, s) := by
    intro v hv
    simp only [Pi.mul_apply, G]
    rcases eq_or_lt_of_le hv.1 with h0 | h0
    · subst h0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        ENNReal.ofReal_zero, zero_mul]
      rw [eq_comm]
      refine (lintegral_congr fun s => ?_).trans lintegral_zero
      simp [Set.indicator_apply]
    · have hlr : 1 / 2 - v / 2 < 1 / 2 + v / 2 := by linarith
      rw [unifI, ite_of hlr, lintegral_smul_measure, ← lintegral_indicator measurableSet_Icc]
      have hGv : (fun s => G (v, s)) = fun s => ENNReal.ofReal (3 * v) *
          (Icc (1 / 2 - v / 2) (1 / 2 + v / 2)).indicator h s := by
        funext s
        simp only [G, S, Set.indicator_apply, mem_ofPred_eq, mem_Icc_half_iff]
        split_ifs <;> simp
      rw [show (∫⁻ s, G (v, s)) = ∫⁻ s, (fun s => G (v, s)) s from rfl, hGv,
        lintegral_const_mul _ ((hh.indicator measurableSet_Icc)), smul_eq_mul, ← mul_assoc]
      congr 1
      rw [show 1 / 2 + v / 2 - (1 / 2 - v / 2) = v by ring,
        ← ENNReal.ofReal_inv_of_pos h0, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
  have h2 : ∀ s, ∫⁻ v in Icc (0 : ℝ) 1, G (v, s) =
      (Icc 0 1).indicator (fun s => ENNReal.ofReal (6 * s * (1 - s)) * h s) s := by
    intro s
    have hGs : (fun v => G (v, s)) =
        (Ici |2 * s - 1|).indicator (fun v => ENNReal.ofReal (3 * v) * h s) := by
      funext v
      simp only [G, S, Set.indicator_apply, mem_ofPred_eq, mem_Ici]
    rw [show (∫⁻ v in Icc (0 : ℝ) 1, G (v, s)) = ∫⁻ v in Icc (0 : ℝ) 1, (fun v => G (v, s)) v
      from rfl, hGs, lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, lintegral_mul_const _ (by fun_prop)]
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · have ha0 : 0 ≤ |2 * s - 1| := abs_nonneg _
      have ha1 : |2 * s - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      have hI : Ici |2 * s - 1| ∩ Icc 0 1 = Icc |2 * s - 1| 1 := by
        ext v; simp only [mem_inter_iff, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, ha0.trans h1, h2⟩
      rw [indicator_of_mem hs, hI, lintegral_Icc_three_mul ha0 ha1,
        sq_abs]
      congr 2
      ring
    · rw [indicator_of_notMem hs]
      have ha : 1 < |2 * s - 1| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hs
        rcases hs with hs | hs
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hI : Ici |2 * s - 1| ∩ Icc 0 1 = ∅ := by
        ext v; simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, h2⟩; linarith
      rw [hI, Measure.restrict_empty, lintegral_zero_measure, zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Icc h1]
  rw [lintegral_lintegral_swap (f := fun v s => G (v, s)) hG.aemeasurable]
  simp only [h2]
  rw [lintegral_indicator measurableSet_Icc]

end Tetra

/-! #### The construction of Remark 46 -/

section TetraMix

variable {n : ℕ}

/-- The planar space of the Archimedes measure. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

lemma unifI_ae_mem {l r : ℝ} (h : l ≤ r) : ∀ᵐ x ∂unifI l r, x ∈ Icc l r := by
  unfold unifI
  split_ifs with hlr
  · exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  · exact (ae_dirac_iff measurableSet_Icc).2 ⟨le_rfl, h⟩

/-- Lemma 1 for the chords `[0, y_j]`: the marginals are `U[0, y_i]` and the sum is
`(1/2) ∑ y_j` almost surely. -/
lemma chord0_spec (y : Fin n → ℝ) (hy : ∀ j, 0 ≤ y j) (hpos : ∃ j, 0 < y j)
    (hpoly : ∀ j, 2 * y j ≤ ∑ i, y i) :
    (∀ i, archPlane.map (fun ξ => Assembly.chordVec 0 0 0 y ξ i) = unifI 0 (y i)) ∧
      ∀ᵐ ξ ∂archPlane, ∑ i, Assembly.chordVec 0 0 0 y ξ i = 1 / 2 * ∑ i, y i := by
  have htr : ∀ x, trapH 0 x = x := fun x => by simp [trapH]
  have hx : Assembly.LemOneHyp fun j => trapH 0 (y j) := by
    simp only [htr]; exact ⟨hy, hpos, hpoly⟩
  obtain ⟨hJ, hs⟩ := Assembly.chordVec_spec 0 0 0 y hx
  have hcv : Measurable (Assembly.chordVec (n := n) 0 0 0 y) :=
    (Assembly.measurable_chordVec (n := n) 0 0 0).comp (f := fun ξ => (y, ξ))
      measurable_prodMk_left
  refine ⟨fun i => ?_, ?_⟩
  · have := hJ.2.2 i
    rw [Measure.map_map (measurable_pi_apply i) hcv] at this
    rw [show (fun ξ => Assembly.chordVec 0 0 0 y ξ i) =
      (fun x : Fin n → ℝ => x i) ∘ Assembly.chordVec 0 0 0 y from rfl, this]
    simp [Assembly.chord, htr]
  · have := (ae_map_iff hcv.aemeasurable (measurableSet_sum_eq _)).1 hs
    filter_upwards [this] with ξ hξ
    rw [hξ]
    simp [Assembly.lo, Assembly.hi, htr]

/-- The abscissae: Lemma 1 for `n` copies of `[1/2 - v/2, 1/2 + v/2]`. -/
def absVec (v : ℝ) (ξ : E2) : Fin n → ℝ := Assembly.chordVec 0 (1 / 2) (-1 / 2) (fun _ => v) ξ

lemma measurable_absVec : Measurable fun w : ℝ × E2 => absVec (n := n) w.1 w.2 :=
  (Assembly.measurable_chordVec (n := n) 0 (1 / 2) (-1 / 2)).comp
    (f := fun w : ℝ × E2 => ((fun _ => w.1 : Fin n → ℝ), w.2))
    ((measurable_pi_iff.2 fun _ => measurable_fst).prodMk measurable_snd)

/-- The good abscissae: all in `(0, 1)`, with sum `n / 2`. -/
def goodSet (n : ℕ) : Set (Fin n → ℝ) :=
  (⋂ j, (fun x : Fin n → ℝ => x j) ⁻¹' Ioo 0 1) ∩ {x | ∑ j, x j = n / 2}

lemma measurableSet_goodSet : MeasurableSet (goodSet n) :=
  (MeasurableSet.iInter fun j => measurableSet_Ioo.preimage (measurable_pi_apply j)).inter
    (measurableSet_sum_eq _)

lemma absVec_spec (hn : 2 ≤ n) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∀ i, archPlane.map (fun ξ => absVec (n := n) v ξ i) =
      unifI (1 / 2 - v / 2) (1 / 2 + v / 2)) ∧
      ∀ᵐ ξ ∂archPlane, absVec (n := n) v ξ ∈ goodSet n := by
  have htr : ∀ x, trapH 0 x = x := fun x => by simp [trapH]
  have hx : Assembly.LemOneHyp fun _ : Fin n => trapH 0 v := by
    simp only [htr]
    refine ⟨fun _ => hv.1.le, ⟨⟨0, by omega⟩, hv.1⟩, fun _ => ?_⟩
    show 2 * v ≤ ∑ _i : Fin n, v
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [hv.1]
  obtain ⟨hJ, hs⟩ := Assembly.chordVec_spec 0 (1 / 2) (-1 / 2) (fun _ => v) hx
  have hcv : Measurable (absVec (n := n) v) :=
    measurable_absVec.comp (f := fun ξ => (v, ξ)) measurable_prodMk_left
  have hmarg : ∀ i, archPlane.map (fun ξ => absVec (n := n) v ξ i) =
      unifI (1 / 2 - v / 2) (1 / 2 + v / 2) := by
    intro i
    have := hJ.2.2 i
    change Measure.map (fun x => x i) (Measure.map (absVec v) archPlane) = _ at this
    rw [Measure.map_map (measurable_pi_apply i) hcv] at this
    rw [show (fun ξ => absVec (n := n) v ξ i) =
      (fun x : Fin n → ℝ => x i) ∘ absVec v from rfl, this]
    simp only [Assembly.chord, htr]
    congr 1 <;> ring
  refine ⟨hmarg, ?_⟩
  have hI : Icc (1 / 2 - v / 2) (1 / 2 + v / 2) ⊆ Ioo 0 1 := fun s hs =>
    ⟨by linarith [hs.1, hv.2], by linarith [hs.2, hv.2]⟩
  have h1 : ∀ i, ∀ᵐ ξ ∂archPlane, absVec (n := n) v ξ i ∈ Ioo 0 1 := by
    intro i
    have := unifI_ae_mem (l := 1 / 2 - v / 2) (r := 1 / 2 + v / 2) (by linarith [hv.1])
    rw [← hmarg i] at this
    filter_upwards [(ae_map_iff ((measurable_pi_apply i).comp hcv).aemeasurable
      measurableSet_Icc).1 this] with ξ hξ
    exact hI hξ
  have h2 : ∀ᵐ ξ ∂archPlane, ∑ j, absVec (n := n) v ξ j = n / 2 := by
    filter_upwards [(ae_map_iff hcv.aemeasurable (measurableSet_sum_eq _)).1 hs] with ξ hξ
    rw [hξ]
    simp only [Assembly.lo, Assembly.hi, htr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  filter_upwards [ae_all_iff.2 h1, h2] with ξ hξ1 hξ2
  exact ⟨mem_iInter.2 hξ1, hξ2⟩

/-- The output of the construction of Remark 46, from `(v, ξ₀, ξ₁, ξ₂)`: abscissae
`X = absVec v ξ₀`, then Lemma 1 for the chords `[0, 1 - X_i]` (with `ξ₁`) and `[0, X_i]`
(with `ξ₂`). -/
def tetraOut (w : ℝ × E2 × E2 × E2) : Fin n → ℝ × ℝ × ℝ := fun i =>
  (absVec w.1 w.2.1 i, Assembly.chordVec 0 0 0 (fun j => 1 - absVec w.1 w.2.1 j) w.2.2.1 i,
    Assembly.chordVec 0 0 0 (absVec w.1 w.2.1) w.2.2.2 i)

lemma measurable_tetraOut : Measurable (tetraOut (n := n)) := by
  have hX : Measurable fun w : ℝ × E2 × E2 × E2 => absVec (n := n) w.1 w.2.1 :=
    measurable_absVec.comp (f := fun w : ℝ × E2 × E2 × E2 => (w.1, w.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hcv := Assembly.measurable_chordVec (n := n) 0 0 0
  have hY : Measurable fun w : ℝ × E2 × E2 × E2 =>
      Assembly.chordVec 0 0 0 (fun j => 1 - absVec (n := n) w.1 w.2.1 j) w.2.2.1 :=
    hcv.comp (f := fun w : ℝ × E2 × E2 × E2 => ((fun j => 1 - absVec w.1 w.2.1 j), w.2.2.1))
      ((measurable_pi_iff.2 fun j => measurable_const.sub ((measurable_pi_apply j).comp hX)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hZ : Measurable fun w : ℝ × E2 × E2 × E2 =>
      Assembly.chordVec 0 0 0 (absVec (n := n) w.1 w.2.1) w.2.2.2 :=
    hcv.comp (f := fun w : ℝ × E2 × E2 × E2 => (absVec w.1 w.2.1, w.2.2.2))
      (hX.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp hX).prodMk
    (((measurable_pi_apply i).comp hY).prodMk ((measurable_pi_apply i).comp hZ))

/-- The randomness: `v ∼ 3 v² dv` and three independent Archimedes vectors. -/
def tetraIn : Measure (ℝ × E2 × E2 × E2) := rhoLaw.prod (archPlane.prod (archPlane.prod archPlane))

lemma tetraIn_isProb : IsProbabilityMeasure tetraIn := by
  have := rhoLaw_isProb
  have : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1
  unfold tetraIn; infer_instance

lemma good_conditions (hn : 4 ≤ n) {x : Fin n → ℝ} (hx : x ∈ goodSet n) :
    ((∀ j, 0 ≤ 1 - x j) ∧ (∃ j, 0 < 1 - x j) ∧ ∀ j, 2 * (1 - x j) ≤ ∑ i, (1 - x i)) ∧
      ((∀ j, 0 ≤ x j) ∧ (∃ j, 0 < x j) ∧ ∀ j, 2 * x j ≤ ∑ i, x i) := by
  obtain ⟨h1, h2⟩ := hx
  have h1' : ∀ j, x j ∈ Ioo 0 1 := fun j => mem_iInter.1 h1 j
  have h2' : ∑ j, x j = n / 2 := h2
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : ∑ i, (1 - x i) = n / 2 := by
    rw [Finset.sum_sub_distrib, h2']; simp; ring
  refine ⟨⟨fun j => by linarith [(h1' j).2], ⟨⟨0, by omega⟩, by linarith [(h1' ⟨0, by omega⟩).2]⟩,
    fun j => by rw [hs]; linarith [(h1' j).1]⟩,
    ⟨fun j => (h1' j).1.le, ⟨⟨0, by omega⟩, (h1' ⟨0, by omega⟩).1⟩,
    fun j => by rw [h2']; linarith [(h1' j).2]⟩⟩

/-- Given good abscissae `x`, the conditional law of `(Y_i, Z_i)` is `U[0, 1 - x_i] ⊗ U[0, x_i]`. -/
lemma inner_eq (hn : 4 ≤ n) {x : Fin n → ℝ} (hx : x ∈ goodSet n) (i : Fin n)
    {C : Set (ℝ × ℝ)} (hC : MeasurableSet C) :
    (archPlane.prod archPlane) {z | (Assembly.chordVec 0 0 0 (fun j => 1 - x j) z.1 i,
      Assembly.chordVec 0 0 0 x z.2 i) ∈ C} = secLaw (x i) C := by
  have : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := good_conditions hn hx
  have hY := (chord0_spec _ a1 a2 a3).1 i
  have hZ := (chord0_spec _ b1 b2 b3).1 i
  have hcv := Assembly.measurable_chordVec (n := n) 0 0 0
  have hf1 : Measurable fun ξ : E2 => Assembly.chordVec 0 0 0 (fun j => 1 - x j) ξ i :=
    (measurable_pi_apply i).comp (hcv.comp (f := fun ξ => ((fun j => 1 - x j), ξ))
      measurable_prodMk_left)
  have hf2 : Measurable fun ξ : E2 => Assembly.chordVec 0 0 0 x ξ i :=
    (measurable_pi_apply i).comp (hcv.comp (f := fun ξ => (x, ξ)) measurable_prodMk_left)
  rw [secLaw, ← hY, ← hZ, Measure.map_prod_map _ _ hf1 hf2,
    Measure.map_apply (hf1.prodMap hf2) hC]
  rfl

/-- **Remark 46** (`s:rem:tetra`) in normal form, unconditionally: for `n ≥ 4` the
construction of the remark (abscissae from Khintchine's decomposition and Lemma 1, then two
independent joint mixes of Lemma 1 for the sides of the rectangular sections) is an `n`-complete
mix of the uniform distribution on `T = {0 ≤ x ≤ 1, 0 ≤ y ≤ 1 - x, 0 ≤ z ≤ x}`. -/
theorem tetra_isCompleteMix (hn : 4 ≤ n) :
    IsCompleteMix n (unifSet tetraSet) (tetraIn.map (tetraOut (n := n))) := by
  have := tetraIn_isProb
  have hA : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1
  have hO := measurable_tetraOut (n := n)
  refine ⟨inferInstance, ⟨((n : ℝ) / 2, (n / 4 : ℝ), (n / 4 : ℝ)), ?_⟩, fun i => ?_⟩
  · have hS : MeasurableSet {x : Fin n → ℝ × ℝ × ℝ |
        ∑ j, x j = ((n : ℝ) / 2, (n / 4 : ℝ), (n / 4 : ℝ))} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
        measurable_const
    set c : ℝ × ℝ × ℝ := ((n : ℝ) / 2, (n / 4 : ℝ), (n / 4 : ℝ))
    have hS1 : MeasurableSet {w : ℝ × E2 × E2 × E2 | ∑ j, tetraOut (n := n) w j = c} := hO hS
    rw [ae_map_iff hO.aemeasurable hS, tetraIn, Measure.ae_prod_iff_ae_ae hS1]
    filter_upwards [rhoLaw_ae_mem] with v hv
    have hS2 : MeasurableSet {y : E2 × E2 × E2 | ∑ j, tetraOut (n := n) (v, y) j = c} :=
      measurable_prodMk_left hS1
    rw [Measure.ae_prod_iff_ae_ae hS2]
    filter_upwards [(absVec_spec (n := n) (by omega) hv).2] with ξ0 hξ0
    have hS3 : MeasurableSet {z : E2 × E2 | ∑ j, tetraOut (n := n) (v, ξ0, z) j = c} :=
      measurable_prodMk_left hS2
    rw [Measure.ae_prod_iff_ae_ae hS3]
    obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := good_conditions hn hξ0
    filter_upwards [(chord0_spec _ a1 a2 a3).2] with ξ1 h1
    filter_upwards [(chord0_spec _ b1 b2 b3).2] with ξ2 h2
    have hX : ∑ j, absVec (n := n) v ξ0 j = n / 2 := hξ0.2
    have hs : ∑ i, (1 - absVec (n := n) v ξ0 i) = n / 2 := by
      rw [Finset.sum_sub_distrib, hX]; simp; ring
    simp only [tetraOut]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_sum]; exact hX
    · simp only [Prod.snd_sum, Prod.fst_sum]; rw [h1, hs]; ring
    · simp only [Prod.snd_sum]; rw [h2, hX]; ring
  · have hOi : Measurable fun w => tetraOut (n := n) w i := (measurable_pi_apply i).comp hO
    rw [Measure.map_map (measurable_pi_apply i) hO]
    ext A hA
    show (tetraIn.map (fun w => tetraOut (n := n) w i)) A = unifSet tetraSet A
    rw [Measure.map_apply hOi hA, unifSet_tetraSet_apply hA, tetraIn,
      Measure.prod_apply (hOi hA)]
    have hstep : ∀ᵐ v ∂rhoLaw, (archPlane.prod (archPlane.prod archPlane))
        (Prod.mk v ⁻¹' ((fun w => tetraOut (n := n) w i) ⁻¹' A)) =
        ∫⁻ s, secDens A s ∂unifI (1 / 2 - v / 2) (1 / 2 + v / 2) := by
      filter_upwards [rhoLaw_ae_mem] with v hv
      obtain ⟨hmarg, hgood⟩ := absVec_spec (n := n) (by omega) hv
      have hXi : Measurable fun ξ : E2 => absVec (n := n) v ξ i :=
        (measurable_pi_apply i).comp
          (measurable_absVec.comp (f := fun ξ => (v, ξ)) measurable_prodMk_left)
      rw [Measure.prod_apply (measurable_prodMk_left (hOi hA)), ← hmarg i,
        lintegral_map (measurable_secDens hA) hXi]
      refine lintegral_congr_ae ?_
      filter_upwards [hgood] with ξ0 hξ0
      rw [← secLaw_slice hA (mem_iInter.1 hξ0.1 i), ← inner_eq hn hξ0 i (measurable_prodMk_left hA)]
      rfl
    rw [lintegral_congr_ae hstep, khintchine (measurable_secDens hA),
      ← lintegral_const_mul _ (measurable_secArea hA), ← setLIntegral_congr Ioo_ae_eq_Icc,
      ← setLIntegral_congr Ioo_ae_eq_Icc]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have ha0 : ENNReal.ofReal s ≠ 0 := by simpa using hs.1
    have hb0 : ENNReal.ofReal (1 - s) ≠ 0 := by simpa using hs.2
    have hsplit : ENNReal.ofReal (6 * s * (1 - s)) =
        6 * ENNReal.ofReal s * ENNReal.ofReal (1 - s) := by
      rw [ENNReal.ofReal_mul (by linarith [hs.1]), ENNReal.ofReal_mul (by norm_num)]
      simp
    calc ENNReal.ofReal (6 * s * (1 - s)) * secDens A s
        = 6 * (ENNReal.ofReal s * (ENNReal.ofReal s)⁻¹) *
          (ENNReal.ofReal (1 - s) * (ENNReal.ofReal (1 - s))⁻¹) * secArea A s := by
          rw [hsplit, secDens]; ring
      _ = 6 * secArea A s := by
          rw [ENNReal.mul_inv_cancel ha0 ENNReal.ofReal_ne_top,
            ENNReal.mul_inv_cancel hb0 ENNReal.ofReal_ne_top]; ring

/-- **Remark 46** in normal form: `U(T)` is `n`-completely mixable for every `n ≥ 4`, using only
Lemma 1 (no Theorem 27). -/
theorem tetra_completelyMixable (hn : 4 ≤ n) : CompletelyMixable n (unifSet tetraSet) :=
  ⟨_, tetra_isCompleteMix hn⟩

end TetraMix

/-! #### Every tetrahedron -/

section TetraAffine

/-- Complete mixability is preserved by bijective affine maps between finite-dimensional
spaces (with additive Haar measures as volumes). -/
theorem completelyMixable_image_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
    [(volume : Measure F).IsAddHaarMeasure] {n : ℕ} {K : Set E}
    (h : CompletelyMixable n (unifSet K)) (e : E ≃L[ℝ] F) (b : F) :
    CompletelyMixable n (unifSet ((fun x => e x + b) '' K)) := by
  let φ : F ≃ᵐ E := ((Homeomorph.addRight (-b)).trans e.symm.toHomeomorph).toMeasurableEquiv
  have hφ : ∀ y, φ y = e.symm (y + -b) := fun y => rfl
  have hφs : ∀ x, φ.symm x = e x + b := by
    intro x
    apply φ.injective
    rw [MeasurableEquiv.apply_symm_apply, hφ, add_neg_cancel_right,
      ContinuousLinearEquiv.symm_apply_apply]
  have hmap : ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ volume.map φ = c • volume := by
    have h1 : volume.map φ = (volume.map (fun y : F => y + -b)).map e.symm := by
      rw [Measure.map_map e.symm.continuous.measurable (measurable_add_const _)]
      rfl
    rw [h1, map_add_right_eq_self]
    refine ⟨(Measure.addHaarScalarFactor (volume.map e.symm) volume : ENNReal),
      ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
      ENNReal.coe_ne_top, ?_⟩
    conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map e.symm) volume]
    ext s hs
    simp
  obtain ⟨c, hc0, hct, he⟩ := hmap
  have hpre : φ ⁻¹' K = (fun x => e x + b) '' K := by
    ext y
    constructor
    · intro hy
      refine ⟨φ y, hy, ?_⟩
      show e (φ y) + b = y
      rw [← hφs, MeasurableEquiv.symm_apply_apply]
    · rintro ⟨x, hx, rfl⟩
      show φ (e x + b) ∈ K
      rw [← hφs, MeasurableEquiv.apply_symm_apply]; exact hx
  obtain ⟨P, hP⟩ := h
  have hQ := hP.map_affine (e : E →L[ℝ] F).toLinearMap.toAddMonoidHom e.continuous.measurable
    (fun _ => b)
  refine ⟨P.map (fun x i => b + (e : E →L[ℝ] F).toLinearMap.toAddMonoidHom (x i)), ?_⟩
  have e1 : (fun _ : Fin n => unifSet ((fun x => e x + b) '' K)) = fun i => (unifSet K).map
      (fun x => (fun _ : Fin n => b) i + (e : E →L[ℝ] F).toLinearMap.toAddMonoidHom x) := by
    funext i
    rw [← hpre, unifSet_preimage_equiv φ hc0 hct he]
    congr 1
    funext x
    rw [hφs, add_comm]
    rfl
  unfold IsCompleteMix
  rw [e1]
  exact hQ

/-- The vertices of the normal form `T`: `(0,0,0)`, `(0,1,0)`, `(1,0,0)`, `(1,0,1)`, two
opposite edges in the planes `x = 0` and `x = 1`. -/
def tetraVert : Fin 4 → ℝ × ℝ × ℝ := ![(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 0, 1)]

lemma convex_tetraSet : Convex ℝ tetraSet := by
  rintro ⟨x, y, z⟩ ⟨h1, h2, h3, h4, h5, h6⟩ ⟨x', y', z'⟩ ⟨h1', h2', h3', h4', h5', h6'⟩ a b ha hb
    hab
  simp only [tetraSet, mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine ⟨by positivity, by nlinarith, by positivity, by nlinarith, by positivity, by nlinarith⟩

/-- `T` is the tetrahedron with vertices `tetraVert`. -/
lemma tetraSet_eq_convexHull : tetraSet = convexHull ℝ (range tetraVert) := by
  apply Subset.antisymm
  · rintro ⟨x, y, z⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    let W : Fin 4 → ℝ := ![1 - x - y, y, x - z, z]
    have hmem := (convex_convexHull ℝ (range tetraVert)).sum_mem (t := Finset.univ) (w := W)
      (z := tetraVert) (fun i _ => by
        fin_cases i <;> simp [W] <;> linarith)
      (by simp [W, Fin.sum_univ_four])
      (fun i _ => subset_convexHull ℝ _ (mem_range_self i))
    convert hmem using 1
    simp only [Fin.sum_univ_four, W, tetraVert]
    simp
  · refine convexHull_min ?_ convex_tetraSet
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [tetraVert, tetraSet]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The linear part of the affine map sending `tetraVert` to `p`. -/
def tetraLin (p : Fin 4 → V) : ℝ × ℝ × ℝ →ₗ[ℝ] V where
  toFun w := w.1 • (p 2 - p 0) + w.2.1 • (p 1 - p 0) + w.2.2 • (p 3 - p 2)
  map_add' w w' := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c w := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul,
    RingHom.id_apply, smul_add]

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma tetraLin_injective {p : Fin 4 → V} (hp : AffineIndependent ℝ p) :
    Function.Injective (tetraLin p) := by
  have hli := linearIndependent_simplexVec (m := 2) hp
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, y, z⟩ h
  have key := Fintype.linearIndependent_iff.1 hli ![y, x - z, z] (by
    rw [Fin.sum_univ_three]
    simp only [simplexVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    rw [← h]
    simp only [tetraLin, LinearMap.coe_mk, AddHom.coe_mk]
    have e3 : (Fin.succ 2 : Fin 4) = 3 := rfl
    rw [e3]
    module)
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  simp at h0 h1 h2
  simp only [Prod.mk_eq_zero]
  exact ⟨by linarith, h0, h2⟩

/-- The affine bijection `w ↦ tetraLin p w + p 0` of `ℝ³` onto a `3`-dimensional `V`, sending
`tetraVert` to `p`. -/
def tetraEquiv {p : Fin 4 → V} (hp : AffineIndependent ℝ p) (hV : Module.finrank ℝ V = 3) :
    (ℝ × ℝ × ℝ) ≃L[ℝ] V :=
  (LinearEquiv.ofBijective (tetraLin p) ⟨tetraLin_injective hp,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, hV])).1
      (tetraLin_injective hp)⟩).toContinuousLinearEquiv

omit [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] in
lemma image_tetraSet {p : Fin 4 → V} (hp : AffineIndependent ℝ p) (hV : Module.finrank ℝ V = 3) :
    (fun x => tetraEquiv hp hV x + p 0) '' tetraSet = convexHull ℝ (range p) := by
  let f : (ℝ × ℝ × ℝ) →ᵃ[ℝ] V := (tetraLin p).toAffineMap + AffineMap.const ℝ (ℝ × ℝ × ℝ) (p 0)
  have hf : (fun x => tetraEquiv hp hV x + p 0) = f := by
    funext x; rfl
  have hv : ⇑f ∘ tetraVert = p := by
    funext i
    fin_cases i <;> simp [f, tetraVert, tetraLin]
  rw [hf, tetraSet_eq_convexHull, f.image_convexHull, ← range_comp, hv]

/-- **Remark 46** (`s:rem:tetra`), unconditionally: the uniform distribution on every
tetrahedron `conv (p 0, p 1, p 2, p 3)` (`p` affinely independent, `dim V = 3`) is
`n`-completely mixable for every `n ≥ 4`, by the construction of the remark (Lemma 1 only). -/
theorem tetrahedron_completelyMixable {p : Fin 4 → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = 3) {n : ℕ} (hn : 4 ≤ n) :
    CompletelyMixable n (unifSet (convexHull ℝ (range p))) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [← image_tetraSet hp hV]
  exact completelyMixable_image_equiv (tetra_completelyMixable hn) _ _

end TetraAffine

end ConeMix

end Mixes
