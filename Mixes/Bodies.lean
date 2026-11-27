import Mixes.Defs

/-!
# Balls, products and affine images (Lemmas 48 and 53, Theorem 51)

This file formalises part of Section 17 of the paper (`b:lem:affine`, `b:lem:product`,
`b:thm:ball`).

* `IsJointMix.map_add_hom`: a joint mix pushed forward coordinatewise by maps `x ↦ c i + L x`
  with a common additive map `L` is a joint mix of the pushforwards.
* `IsJointMix.prod`: the coordinatewise pairing of independent joint mixes is a joint mix of the
  products; `IsJointMix.map_fst`, `IsJointMix.map_snd`: the converse by projection.
* `ScalingProperty μ m`: the scaling property with constant `m`, stated for the probability
  measure `μ = U(K)`, using `U(t + λ K) = μ.map (x ↦ t + λ • x)` (also for `λ = 0`).
* `unifSeq`: the law of an i.i.d. sequence of `U[0, 1]` variables; `map_splitSeq`: it splits
  into two independent such sequences.
* `scalingProperty_map_affine`: Lemma 48. `scalingProperty_prod`, `isJointMix_map_fst_of_prod`,
  `isJointMix_map_snd_of_prod`, `completelyMixable_prod_iff`: Lemma 53.
* `ball_necessity` (in `ℝ^j`, `j ≥ 1`) and `ball_necessity_gen`: the necessity half of
  Theorem 51.
* Full-dimensional sets: `unifScaled K t r = U(t + r K)`; `unifScaled_eq_map`,
  `unifSet_map_affine`, `unifSet_prod`; `ScalingPropertySet` (the paper's form) and
  `scalingPropertySet_iff`; `scalingPropertySet_image_affine` (Lemma 48 for bijective affine
  maps), `scalingPropertySet_prod`, `completelyMixable_unifSet_prod_iff` (Lemma 53).

Not formalised: Lemma 49 (see `Polygon.lean`), Lemma 50 and the sufficiency half of Theorem 51
(they need the uniform distribution on the sphere and the polar decomposition of `U(B)`).
-/

open MeasureTheory

noncomputable section

namespace Mixes

instance instIsProbabilityMeasureUnifI (l r : ℝ) : IsProbabilityMeasure (unifI l r) :=
  unifI_isProb l r

/-! ### Generic lemmas on joint mixes -/

section Generic

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] {n : ℕ}

lemma measurableSet_sum_eq' [AddCommMonoid F] [MeasurableSingletonClass F] [MeasurableAdd₂ F]
    (s : F) : MeasurableSet {y : Fin n → F | ∑ j, y j = s} :=
  (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton s)

/-- Pushforward of a joint mix under coordinatewise maps `x ↦ c i + L x`, with one additive map
`L` for all coordinates: a joint mix of the pushforwards. -/
theorem IsJointMix.map_add_hom [AddCommMonoid E] [AddCommMonoid F] [MeasurableSingletonClass F]
    [MeasurableAdd₂ F] {G : Fin n → Measure E} {P : Measure (Fin n → E)} (h : IsJointMix G P)
    (L : E →+ F) (hL : Measurable L) (c : Fin n → F) :
    IsJointMix (fun i => (G i).map (fun x => c i + L x)) (P.map (fun x i => c i + L (x i))) := by
  obtain ⟨hP, ⟨s, hs⟩, hm⟩ := h
  have hg : Measurable (fun x : Fin n → E => fun i => c i + L (x i)) :=
    measurable_pi_iff.2 fun i => measurable_const.add (hL.comp (measurable_pi_apply i))
  refine ⟨inferInstance, ⟨∑ i, c i + L s, ?_⟩, fun j => ?_⟩
  · rw [ae_map_iff hg.aemeasurable (measurableSet_sum_eq' _)]
    filter_upwards [hs] with x hx
    simp [Finset.sum_add_distrib, ← map_sum, hx]
  · dsimp only
    rw [Measure.map_map (measurable_pi_apply j) hg, ← hm j,
      Measure.map_map (g := fun x => c j + L x) (measurable_const.add hL)
        (measurable_pi_apply j)]
    rfl

/-- The coordinatewise pairing of two independent joint mixes is a joint mix of the products. -/
theorem IsJointMix.prod [AddCommMonoid E] [AddCommMonoid F] [MeasurableSingletonClass E]
    [MeasurableSingletonClass F] [MeasurableAdd₂ E] [MeasurableAdd₂ F]
    {G : Fin n → Measure E} {H : Fin n → Measure F} {P : Measure (Fin n → E)}
    {Q : Measure (Fin n → F)} (hP : IsJointMix G P) (hQ : IsJointMix H Q) :
    IsJointMix (fun i => (G i).prod (H i)) ((P.prod Q).map (fun z i => (z.1 i, z.2 i))) := by
  obtain ⟨hP1, ⟨s, hs⟩, hPm⟩ := hP
  obtain ⟨hQ1, ⟨u, hu⟩, hQm⟩ := hQ
  have hg : Measurable (fun z : (Fin n → E) × (Fin n → F) => fun i => (z.1 i, z.2 i)) :=
    measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  refine ⟨inferInstance, ⟨(s, u), ?_⟩, fun j => ?_⟩
  · have hset : MeasurableSet {y : Fin n → E × F | ∑ j, y j = (s, u)} := by
      have e : {y : Fin n → E × F | ∑ j, y j = (s, u)} =
          (fun y j => (y j).1) ⁻¹' {y | ∑ j, y j = s} ∩
            (fun y j => (y j).2) ⁻¹' {y | ∑ j, y j = u} := by
        ext y; simp [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
      rw [e]
      exact ((measurable_pi_iff.2 fun j => measurable_fst.comp (measurable_pi_apply j))
          (measurableSet_sum_eq' s)).inter
        ((measurable_pi_iff.2 fun j => measurable_snd.comp (measurable_pi_apply j))
          (measurableSet_sum_eq' u))
    rw [ae_map_iff hg.aemeasurable hset]
    have h1 : ∀ᵐ z ∂(P.prod Q), ∑ j, z.1 j = s := Measure.quasiMeasurePreserving_fst.ae hs
    have h2 : ∀ᵐ z ∂(P.prod Q), ∑ j, z.2 j = u := Measure.quasiMeasurePreserving_snd.ae hu
    filter_upwards [h1, h2] with z hz1 hz2
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, hz1, hz2]
  · dsimp only
    rw [Measure.map_map (measurable_pi_apply j) hg, ← hPm j, ← hQm j,
      Measure.map_prod_map _ _ (measurable_pi_apply j) (measurable_pi_apply j)]
    rfl

/-- Projection of a joint mix of products on the first factor. -/
theorem IsJointMix.map_fst [AddCommMonoid E] [AddCommMonoid F] [MeasurableSingletonClass E]
    [MeasurableAdd₂ E] {G : Fin n → Measure E} {H : Fin n → Measure F}
    [∀ i, IsProbabilityMeasure (H i)] {P : Measure (Fin n → E × F)}
    (h : IsJointMix (fun i => (G i).prod (H i)) P) :
    IsJointMix G (P.map (fun x i => (x i).1)) := by
  have := h.map_add_hom (AddMonoidHom.fst E F) measurable_fst 0
  simp only [Pi.zero_apply, zero_add, AddMonoidHom.coe_fst] at this
  convert this using 2 with i
  rw [Measure.map_fst_prod]
  simp

/-- Projection of a joint mix of products on the second factor. -/
theorem IsJointMix.map_snd [AddCommMonoid E] [AddCommMonoid F] [MeasurableSingletonClass F]
    [MeasurableAdd₂ F] {G : Fin n → Measure E} {H : Fin n → Measure F}
    [∀ i, IsProbabilityMeasure (G i)] [∀ i, SFinite (H i)] {P : Measure (Fin n → E × F)}
    (h : IsJointMix (fun i => (G i).prod (H i)) P) :
    IsJointMix H (P.map (fun x i => (x i).2)) := by
  have := h.map_add_hom (AddMonoidHom.snd E F) measurable_snd 0
  simp only [Pi.zero_apply, zero_add, AddMonoidHom.coe_snd] at this
  convert this using 2 with i
  rw [Measure.map_snd_prod]
  simp

end Generic

/-! ### The source of randomness: independent uniform variables -/

/-- The law of a sequence of independent random variables uniform on `[0, 1]`. -/
def unifSeq : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => unifI 0 1

instance : IsProbabilityMeasure unifSeq := by unfold unifSeq; infer_instance

/-- A fixed bijection `ℕ ≃ Fin 2 × ℕ`, used to split one sequence into two. -/
def natEquivFinTwoProd : ℕ ≃ Fin 2 × ℕ := (Nat.divModEquiv 2).trans (Equiv.prodComm _ _)

/-- Splitting a sequence into two subsequences. -/
def splitSeq : (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  MeasurableEquiv.piFinTwo (fun _ => ℕ → ℝ) ∘ MeasurableEquiv.curry (Fin 2) ℕ ℝ ∘
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) natEquivFinTwoProd

lemma measurable_splitSeq : Measurable splitSeq := by
  unfold splitSeq
  exact (MeasurableEquiv.measurable _).comp
    ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _))

/-- The two subsequences of an i.i.d. uniform sequence are independent i.i.d. uniform sequences. -/
lemma map_splitSeq : unifSeq.map splitSeq = unifSeq.prod unifSeq := by
  unfold splitSeq
  rw [← Measure.map_map (MeasurableEquiv.measurable _)
      ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _)),
    ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  have h1 : unifSeq.map (MeasurableEquiv.piCongrLeft (fun _ => ℝ) natEquivFinTwoProd) =
      Measure.infinitePi (fun _ : Fin 2 × ℕ => unifI 0 1) :=
    Measure.infinitePi_map_piCongrLeft (fun _ : Fin 2 × ℕ => unifI 0 1) natEquivFinTwoProd
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin 2) (_ : ℕ) => unifI 0 1)
  rw [h1]
  erw [h2]
  rw [Measure.infinitePi_eq_pi]
  exact (measurePreserving_piFinTwo (fun _ => unifSeq)).map_eq

/-! ### The scaling property -/

section Scaling

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- The scaling property with constant `m` (Section 17), stated for the probability measure
`μ = U(K)`: for every `n ≥ 2` there is a Borel function `Φ` of the parameters `(λ, t)` and of a
sequence of independent uniform variables on `[0, 1]` such that, whenever `λ i ≥ 0`, not all
zero, and `m · max λ ≤ ∑ λ`, the law of `Φ (λ, t)` is a joint mix of the
`U(t i + λ i K) = μ.map (x ↦ t i + λ i • x)`. -/
def ScalingProperty (μ : Measure E) (m : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ Φ : (Fin n → ℝ) × (Fin n → E) → (ℕ → ℝ) → (Fin n → E),
    Measurable (Function.uncurry Φ) ∧
    ∀ (lam : Fin n → ℝ) (t : Fin n → E), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => μ.map (fun x => t i + lam i • x)) (unifSeq.map (Φ (lam, t)))

omit [SecondCountableTopology E] in
/-- **Lemma 48** (`b:lem:affine`), at the level of measures: if `μ` has the scaling property
with constant `m`, so has its image under the affine map `x ↦ M x + b`. (Injectivity of `M` is
only needed to identify the image of `U(K)` with `U(A K)`; see `unifSet_map_affine`.) -/
theorem scalingProperty_map_affine {μ : Measure E} {m : ℝ} (h : ScalingProperty μ m)
    (M : E →L[ℝ] F) (b : F) : ScalingProperty (μ.map (fun x => M x + b)) m := by
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := h n hn
  refine ⟨fun p ω i => (p.2 i + p.1 i • b) + M (Φ (p.1, 0) ω i), ?_, ?_⟩
  · have h0 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → F)) × (ℕ → ℝ) =>
        Φ (q.1.1, 0) q.2) :=
      hΦ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_const |>.prodMk
        measurable_snd)
    refine measurable_pi_iff.2 fun i => ?_
    exact (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).smul
        measurable_const)).add (M.measurable.comp ((measurable_pi_apply i).comp h0))
  · intro lam t hlam hne hm
    have hΦl : Measurable (Φ (lam, 0)) := hΦ.comp measurable_prodMk_left
    have key := (hmix lam 0 hlam hne hm).map_add_hom M.toLinearMap.toAddMonoidHom M.measurable
      (fun i => t i + lam i • b)
    have hA : Measurable (fun x : E => M x + b) := M.measurable.add_const b
    convert key using 1
    · funext i
      rw [Measure.map_map (by fun_prop) hA, Measure.map_map ?_ (by fun_prop)]
      swap
      · exact measurable_const.add M.measurable
      congr 1
      funext x
      simp only [Function.comp_apply, Pi.zero_apply, zero_add, smul_add, map_smul,
        LinearMap.toAddMonoidHom_coe, ContinuousLinearMap.coe_coe]
      abel
    · rw [Measure.map_map ?_ hΦl]
      · rfl
      · exact measurable_pi_iff.2 fun i => measurable_const.add
          (M.measurable.comp (measurable_pi_apply i))

omit [SecondCountableTopology E] [SecondCountableTopology F] in
/-- The image of a product measure under a homothety `z ↦ c + r • z` of `E × F`. -/
lemma map_homothety_prod (μ₁ : Measure E) (μ₂ : Measure F) [SFinite μ₁] [SFinite μ₂]
    (c : E × F) (r : ℝ) :
    (μ₁.prod μ₂).map (fun z => c + r • z) =
      (μ₁.map (fun x => c.1 + r • x)).prod (μ₂.map (fun x => c.2 + r • x)) := by
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rfl

/-- **Lemma 53** (`b:lem:product`), first part, at the level of measures: products keep the
scaling property, with the larger constant. -/
theorem scalingProperty_prod {μ₁ : Measure E} {μ₂ : Measure F} [SFinite μ₁] [SFinite μ₂]
    {m₁ m₂ : ℝ} (h₁ : ScalingProperty μ₁ m₁) (h₂ : ScalingProperty μ₂ m₂) :
    ScalingProperty (μ₁.prod μ₂) (max m₁ m₂) := by
  intro n hn
  obtain ⟨Φ₁, hΦ₁, hmix₁⟩ := h₁ n hn
  obtain ⟨Φ₂, hΦ₂, hmix₂⟩ := h₂ n hn
  refine ⟨fun p ω i => (Φ₁ (p.1, fun i => (p.2 i).1) (splitSeq ω).1 i,
    Φ₂ (p.1, fun i => (p.2 i).2) (splitSeq ω).2 i), ?_, ?_⟩
  · have hp1 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → E × F)) × (ℕ → ℝ) =>
        Φ₁ (q.1.1, fun i => (q.1.2 i).1) (splitSeq q.2).1) :=
      hΦ₁.comp (((measurable_fst.comp measurable_fst).prodMk
        (measurable_pi_iff.2 fun i => measurable_fst.comp
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))).prodMk
        (measurable_fst.comp (measurable_splitSeq.comp measurable_snd)))
    have hp2 : Measurable (fun q : ((Fin n → ℝ) × (Fin n → E × F)) × (ℕ → ℝ) =>
        Φ₂ (q.1.1, fun i => (q.1.2 i).2) (splitSeq q.2).2) :=
      hΦ₂.comp (((measurable_fst.comp measurable_fst).prodMk
        (measurable_pi_iff.2 fun i => measurable_snd.comp
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))).prodMk
        (measurable_snd.comp (measurable_splitSeq.comp measurable_snd)))
    exact measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp hp1).prodMk ((measurable_pi_apply i).comp hp2)
  · intro lam t hlam hne hm
    have hm₁ : ∀ k, m₁ * lam k ≤ ∑ i, lam i := fun k =>
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlam k)).trans (hm k)
    have hm₂ : ∀ k, m₂ * lam k ≤ ∑ i, lam i := fun k =>
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlam k)).trans (hm k)
    have k₁ := hmix₁ lam (fun i => (t i).1) hlam hne hm₁
    have k₂ := hmix₂ lam (fun i => (t i).2) hlam hne hm₂
    have key := k₁.prod k₂
    have hf₁ : Measurable (Φ₁ (lam, fun i => (t i).1)) := hΦ₁.comp measurable_prodMk_left
    have hf₂ : Measurable (Φ₂ (lam, fun i => (t i).2)) := hΦ₂.comp measurable_prodMk_left
    have hpair : Measurable (fun z : (Fin n → E) × (Fin n → F) => fun i => (z.1 i, z.2 i)) :=
      measurable_pi_iff.2 fun i =>
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)
    convert key using 1
    · funext i
      exact map_homothety_prod μ₁ μ₂ (t i) (lam i)
    · rw [Measure.map_prod_map _ _ hf₁ hf₂, ← map_splitSeq,
        Measure.map_map (hf₁.prodMap hf₂) measurable_splitSeq,
        Measure.map_map hpair ((hf₁.prodMap hf₂).comp measurable_splitSeq)]
      rfl

/-- **Lemma 53**, converse: the projection on the first factor of a joint mix of the scaled
translates of `μ₁ ⊗ μ₂` is a joint mix of the scaled translates of `μ₁`. -/
theorem isJointMix_map_fst_of_prod {n : ℕ} {μ₁ : Measure E} {μ₂ : Measure F}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (lam : Fin n → ℝ) (t : Fin n → E × F)
    {P : Measure (Fin n → E × F)}
    (h : IsJointMix (fun i => (μ₁.prod μ₂).map (fun z => t i + lam i • z)) P) :
    IsJointMix (fun i => μ₁.map (fun x => (t i).1 + lam i • x)) (P.map fun x i => (x i).1) := by
  refine IsJointMix.map_fst (H := fun i => μ₂.map (fun x => (t i).2 + lam i • x)) ?_
  convert h using 2 with i
  exact (map_homothety_prod μ₁ μ₂ (t i) (lam i)).symm

/-- **Lemma 53**, converse: the projection on the second factor. -/
theorem isJointMix_map_snd_of_prod {n : ℕ} {μ₁ : Measure E} {μ₂ : Measure F}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (lam : Fin n → ℝ) (t : Fin n → E × F)
    {P : Measure (Fin n → E × F)}
    (h : IsJointMix (fun i => (μ₁.prod μ₂).map (fun z => t i + lam i • z)) P) :
    IsJointMix (fun i => μ₂.map (fun x => (t i).2 + lam i • x)) (P.map fun x i => (x i).2) := by
  refine IsJointMix.map_snd (G := fun i => μ₁.map (fun x => (t i).1 + lam i • x)) ?_
  convert h using 2 with i
  exact (map_homothety_prod μ₁ μ₂ (t i) (lam i)).symm

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **Lemma 53**, last sentence: `μ₁ ⊗ μ₂` is `n`-completely mixable if and only if `μ₁` and
`μ₂` are. -/
theorem completelyMixable_prod_iff {n : ℕ} {μ₁ : Measure E} {μ₂ : Measure F}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    CompletelyMixable n (μ₁.prod μ₂) ↔ CompletelyMixable n μ₁ ∧ CompletelyMixable n μ₂ := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨⟨_, IsJointMix.map_fst (H := fun _ => μ₂) hP⟩,
      ⟨_, IsJointMix.map_snd (G := fun _ => μ₁) hP⟩⟩
  · rintro ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩
    have := hP.1
    have := hQ.1
    exact ⟨_, IsJointMix.prod hP hQ⟩

end Scaling

/-! ### Balls: the necessity half of Theorem 51 -/

section Ball

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]

/-- `U(t + r K)`, read as the point mass at `t` when `r = 0` (as in the paper). -/
def unifScaled (K : Set E) (t : E) (r : ℝ) : Measure E :=
  if r = 0 then Measure.dirac t else unifSet ((fun x => t + r • x) '' K)

omit [MeasureSpace E] in
lemma image_homothety_closedBall (t : E) {r : ℝ} (hr : 0 < r) :
    (fun x => t + r • x) '' closedBall (0 : E) 1 = closedBall t r := by
  ext y
  simp only [Set.mem_image, mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg x]
  · intro hy
    refine ⟨r⁻¹ • (y - t), ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
      calc r⁻¹ * ‖y - t‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

variable [BorelSpace E]

/-- `U(t + r B)` is concentrated on the ball `closedBall t r`. -/
lemma unifScaled_ball_compl (t : E) {r : ℝ} (hr : 0 ≤ r) :
    unifScaled (closedBall (0 : E) 1) t r (closedBall t r)ᶜ = 0 := by
  unfold unifScaled
  split_ifs with h0
  · rw [Measure.dirac_apply' _ measurableSet_closedBall.compl]
    simp [h0]
  · rw [image_homothety_closedBall t (lt_of_le_of_ne hr (Ne.symm h0)), unifSet,
      smul_apply, Measure.restrict_apply measurableSet_closedBall.compl]
    simp

variable [FiniteDimensional ℝ E] [Nontrivial E] [(volume : Measure E).IsAddHaarMeasure]

/-- If `U(t + r B)` with `r > 0` gives mass `1` to a ball of radius `R`, then `r ≤ R`. -/
lemma le_of_unifScaled_ball_eq_one (t c : E) {r R : ℝ} (hr : 0 < r)
    (h : unifScaled (closedBall (0 : E) 1) t r (closedBall c R) = 1) : r ≤ R := by
  unfold unifScaled at h
  simp only [hr.ne', ↓reduceIte] at h
  rw [image_homothety_closedBall t hr, unifSet, smul_apply,
    Measure.restrict_apply measurableSet_closedBall, smul_eq_mul] at h
  have h0 : volume (closedBall t r) ≠ 0 := (measure_closedBall_pos volume t hr).ne'
  have htop : volume (closedBall t r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have heq : volume (closedBall c R ∩ closedBall t r) = volume (closedBall t r) := by
    have := congrArg (volume (closedBall t r) * ·) h
    rwa [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul, mul_one] at this
  have hle : volume (closedBall t r) ≤ volume (closedBall c R) :=
    heq ▸ measure_mono Set.inter_subset_left
  have hR : 0 ≤ R := by
    by_contra hR
    push Not at hR
    rw [closedBall_eq_empty.2 hR, measure_empty] at hle
    exact h0 (nonpos_iff_eq_zero.1 hle)
  rw [Measure.addHaar_closedBall _ _ hr.le, Measure.addHaar_closedBall _ _ hR] at hle
  have hB0 : volume (ball (0 : E) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hBt : volume (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hB0 hBt, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  exact (pow_le_pow_iff_left₀ hr.le hR (Module.finrank_pos (R := ℝ) (M := E)).ne').1 hle

/-- **Theorem 51** (`b:thm:ball`), necessity, in a nontrivial finite-dimensional normed space
with an additive Haar measure: if `U(t i + λ i B)` are jointly mixable, then
`2 λ k ≤ ∑ λ` for every `k`. The proof compares volumes instead of using means: almost surely
`X_k = s - ∑_{i ≠ k} X_i` lies in a ball of radius `∑_{i ≠ k} λ i`. -/
theorem ball_necessity_gen {n : ℕ} (t : Fin n → E) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (h : JointlyMixable (fun i => unifScaled (closedBall (0 : E) 1) (t i) (lam i)))
    (k : Fin n) : 2 * lam k ≤ ∑ i, lam i := by
  obtain ⟨P, hP1, ⟨s, hs⟩, hm⟩ := h
  have hin : ∀ i, ∀ᵐ x ∂P, x i ∈ closedBall (t i) (lam i) := by
    intro i
    refine ae_iff.2 ?_
    have : {x : Fin n → E | ¬x i ∈ closedBall (t i) (lam i)} =
        (fun x => x i) ⁻¹' (closedBall (t i) (lam i))ᶜ := rfl
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_closedBall.compl, hm i]
    exact unifScaled_ball_compl _ (hlam i)
  have hsum := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ k)
  rcases (hlam k).eq_or_lt with hk | hk
  · rw [← hk]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hlam i]
  set R := ∑ i ∈ Finset.univ.erase k, lam i
  set c := s - ∑ i ∈ Finset.univ.erase k, t i with hc
  have hae : ∀ᵐ x ∂P, x k ∈ closedBall c R := by
    filter_upwards [hs, ae_all_iff.2 hin] with x hx hx'
    rw [mem_closedBall, dist_eq_norm]
    have e : x k - c = ∑ i ∈ Finset.univ.erase k, (t i - x i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hx
      rw [hc, Finset.sum_sub_distrib, ← hx]
      abel
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← dist_eq_norm, dist_comm]
    exact hx' i
  have h1 : unifScaled (closedBall (0 : E) 1) (t k) (lam k) (closedBall c R) = 1 := by
    have hk' := hm k
    simp only at hk'
    rw [← hk', Measure.map_apply (measurable_pi_apply k) measurableSet_closedBall]
    refine (prob_compl_eq_zero_iff ((measurable_pi_apply k) measurableSet_closedBall)).1 ?_
    exact ae_iff.1 hae
  have := le_of_unifScaled_ball_eq_one (t k) c hk h1
  linarith

/-- **Theorem 51** (`b:thm:ball`), necessity, in `ℝ^j` with `j ≥ 1`: if
`U(t_1 + λ_1 B), …, U(t_n + λ_n B)` are jointly mixable, then `2 max λ ≤ ∑ λ`. -/
theorem ball_necessity {j n : ℕ} (hj : 1 ≤ j) (t : Fin n → EuclideanSpace ℝ (Fin j))
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (h : JointlyMixable (fun i => unifScaled (closedBall 0 1) (t i) (lam i))) (k : Fin n) :
    2 * lam k ≤ ∑ i, lam i := by
  have : Nontrivial (EuclideanSpace ℝ (Fin j)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  exact ball_necessity_gen t lam hlam h k

end Ball

/-! ### Uniform distributions on full-dimensional sets

For a set `K` of finite positive volume in a finite-dimensional space, `U(t + λ K)` is the image
of `U(K)` under `x ↦ t + λ • x`, also for `λ = 0`; bijective affine maps carry uniform
distributions to uniform distributions, and the uniform distribution on a product is the product.
So `ScalingProperty (unifSet K) m` is the scaling property of the paper for such `K`. -/

section Uniform

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma unifSet_isProb {K : Set E} (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤) :
    IsProbabilityMeasure (unifSet K) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- The volume of an affine image. -/
lemma volume_image_affine (M : E →ₗ[ℝ] E) (b : E) (S : Set E) :
    volume ((fun x => M x + b) '' S) = ENNReal.ofReal |LinearMap.det M| * volume S := by
  have : (fun x => M x + b) '' S = (fun y => -b + y) ⁻¹' (M '' S) := by
    rw [← Set.image_add_left', Set.image_image]
    simp only [neg_neg, add_comm b]
  rw [this, measure_preimage_add, Measure.addHaar_image_linearMap]

/-- A bijective affine map carries `U(K)` to `U(A K)`. -/
theorem unifSet_map_affine (K : Set E) {M : E →ₗ[ℝ] E} (hM : LinearMap.det M ≠ 0) (b : E) :
    (unifSet K).map (fun x => M x + b) = unifSet ((fun x => M x + b) '' K) := by
  have hA : Measurable (fun x => M x + b) :=
    (M.continuous_of_finiteDimensional.add continuous_const).measurable
  have hD0 : ENNReal.ofReal |LinearMap.det M| ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hM
  have hDtop : ENNReal.ofReal |LinearMap.det M| ≠ ⊤ := ENNReal.ofReal_ne_top
  ext s hs
  rw [Measure.map_apply hA hs, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply (hA hs), Measure.restrict_apply hs, smul_eq_mul, smul_eq_mul,
    ← Set.image_preimage_inter, volume_image_affine, volume_image_affine,
    ENNReal.mul_inv (Or.inl hD0) (Or.inl hDtop), mul_mul_mul_comm,
    ENNReal.inv_mul_cancel hD0 hDtop, one_mul]

/-- `U(t + r K) = U(K).map (x ↦ t + r • x)`, for every real `r` (for `r = 0` both sides are the
point mass at `t`). -/
theorem unifScaled_eq_map {K : Set E} (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤) (t : E) (r : ℝ) :
    unifScaled K t r = (unifSet K).map (fun x => t + r • x) := by
  have := unifSet_isProb h0 htop
  unfold unifScaled
  split_ifs with hr
  · subst hr
    simp only [zero_smul, add_zero]
    rw [Measure.map_const, measure_univ, one_smul]
  · have hdet : LinearMap.det (r • LinearMap.id : E →ₗ[ℝ] E) ≠ 0 := by
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
      exact pow_ne_zero _ hr
    have := unifSet_map_affine K hdet t
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    have e : (fun x : E => t + r • x) = fun x => r • x + t := funext fun x => add_comm _ _
    rw [e, this]

/-- The scaling property of the paper, stated with `U(t i + λ i K)` (`unifScaled`) directly. -/
def ScalingPropertySet (K : Set E) (m : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ Φ : (Fin n → ℝ) × (Fin n → E) → (ℕ → ℝ) → (Fin n → E),
    Measurable (Function.uncurry Φ) ∧
    ∀ (lam : Fin n → ℝ) (t : Fin n → E), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => unifScaled K (t i) (lam i)) (unifSeq.map (Φ (lam, t)))

variable [SecondCountableTopology E]

omit [SecondCountableTopology E] in
/-- For a set of finite positive volume the two forms of the scaling property agree. -/
theorem scalingPropertySet_iff {K : Set E} (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤) (m : ℝ) :
    ScalingPropertySet K m ↔ ScalingProperty (unifSet K) m := by
  simp only [ScalingPropertySet, ScalingProperty, unifScaled_eq_map h0 htop]

/-- **Lemma 48** for a bijective affine map `A x = M x + b` of `E` and a set `K` of finite
positive volume. -/
theorem scalingPropertySet_image_affine {K : Set E} (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤)
    {m : ℝ} (hK : ScalingPropertySet K m) {M : E →ₗ[ℝ] E} (hM : LinearMap.det M ≠ 0) (b : E) :
    ScalingPropertySet ((fun x => M x + b) '' K) m := by
  have hD0 : ENNReal.ofReal |LinearMap.det M| ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hM
  have hv : volume ((fun x => M x + b) '' K) = ENNReal.ofReal |LinearMap.det M| * volume K :=
    volume_image_affine M b K
  rw [scalingPropertySet_iff (by rw [hv]; exact mul_ne_zero hD0 h0)
    (by rw [hv]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop),
    ← unifSet_map_affine K hM b]
  rw [scalingPropertySet_iff h0 htop] at hK
  exact scalingProperty_map_affine hK M.toContinuousLinearMap b

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F] [(volume : Measure F).IsAddHaarMeasure] [SecondCountableTopology F]

omit [(volume : Measure E).IsAddHaarMeasure] in
/-- The uniform distribution on a product is the product of the uniform distributions. -/
theorem unifSet_prod {K₁ : Set E} {K₂ : Set F} (h₁ : volume K₁ ≠ 0) (h₁' : volume K₁ ≠ ⊤)
    (h₂ : volume K₂ ≠ 0) (h₂' : volume K₂ ≠ ⊤) :
    unifSet (K₁ ×ˢ K₂) = (unifSet K₁).prod (unifSet K₂) := by
  have := unifSet_isProb h₁ h₁'
  have := unifSet_isProb h₂ h₂'
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [unifSet, unifSet, unifSet, smul_apply, smul_apply, smul_apply,
    Measure.restrict_apply (hs.prod ht), Measure.restrict_apply hs, Measure.restrict_apply ht,
    Set.prod_inter_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.prod_prod,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, ENNReal.mul_inv (Or.inl h₁) (Or.inl h₁'),
    mul_mul_mul_comm]

/-- **Lemma 53** for sets of finite positive volume: `K₁ × K₂` has the scaling property with
constant `max m₁ m₂`. -/
theorem scalingPropertySet_prod {K₁ : Set E} {K₂ : Set F} (h₁ : volume K₁ ≠ 0)
    (h₁' : volume K₁ ≠ ⊤) (h₂ : volume K₂ ≠ 0) (h₂' : volume K₂ ≠ ⊤) {m₁ m₂ : ℝ}
    (hK₁ : ScalingPropertySet K₁ m₁) (hK₂ : ScalingPropertySet K₂ m₂) :
    ScalingPropertySet (K₁ ×ˢ K₂) (max m₁ m₂) := by
  have := unifSet_isProb h₁ h₁'
  have := unifSet_isProb h₂ h₂'
  have hv : volume (K₁ ×ˢ K₂) = volume K₁ * volume K₂ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
  have : (volume : Measure (E × F)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [scalingPropertySet_iff (by rw [hv]; exact mul_ne_zero h₁ h₂)
    (by rw [hv]; exact ENNReal.mul_ne_top h₁' h₂'), unifSet_prod h₁ h₁' h₂ h₂']
  rw [scalingPropertySet_iff h₁ h₁'] at hK₁
  rw [scalingPropertySet_iff h₂ h₂'] at hK₂
  exact scalingProperty_prod hK₁ hK₂

omit [(volume : Measure E).IsAddHaarMeasure] in
/-- **Lemma 53**, last sentence, for sets of finite positive volume: `U(K₁ × K₂)` is
`n`-completely mixable if and only if `U(K₁)` and `U(K₂)` are. -/
theorem completelyMixable_unifSet_prod_iff {n : ℕ} {K₁ : Set E} {K₂ : Set F}
    (h₁ : volume K₁ ≠ 0) (h₁' : volume K₁ ≠ ⊤) (h₂ : volume K₂ ≠ 0) (h₂' : volume K₂ ≠ ⊤) :
    CompletelyMixable n (unifSet (K₁ ×ˢ K₂)) ↔
      CompletelyMixable n (unifSet K₁) ∧ CompletelyMixable n (unifSet K₂) := by
  have := unifSet_isProb h₁ h₁'
  have := unifSet_isProb h₂ h₂'
  rw [unifSet_prod h₁ h₁' h₂ h₂']
  exact completelyMixable_prod_iff

end Uniform

end Mixes
