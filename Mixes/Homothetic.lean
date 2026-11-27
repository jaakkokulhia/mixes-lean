import Mixes.Defs
import Mixes.Means

/-!
# Bodies with homothetic sections (Theorem 62, Corollary 64)

Item M1h of the verification priorities (`b:thm:hom`, `b:cor:monotone`; Lemma 63 is
`Mixes.brunn_mean` in `Mixes.Means`).

Setting. `V` is a finite-dimensional real normed space with an additive Haar measure as `volume`
(the paper's `ℝ^{k-1}`, so `k - 1 = finrank ℝ V`), `F ⊆ V` is compact with nonempty interior,
`r : ℝ → ℝ` is the scale of the sections and `c s = c₀ + s • c₁` is their (affine) position.

* `body α β r c F = {(s, c s + r s • y) : s ∈ [α, β], y ∈ F}` (the set `K`).
* `levelDist α β r d`: the distribution with density proportional to `r ^ d` on `[α, β]`.
* `bodyLaw`: the law of `(S, c S + r S • Y)` with `S ∼ levelDist`, `Y ∼ U(F)` independent.
* `unifSet_body_eq`: Fubini's theorem, `U(K) = bodyLaw` (first paragraph of the proof).
* `homMix`: the construction of Theorem 62 at the level of laws.
* `isCompleteMix_homMix`: **Theorem 62**, the complete mix.
* `convex_body`: **Theorem 62**, convexity of `K` for concave `r`.
* `cor_monotone_a`, `cor_monotone_b`: **Corollary 64**, with Corollary 30 as an explicit
  hypothesis (`Cor30 n`).
-/

open MeasureTheory Set Module Filter
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Homothetic

/-! ### Joint mixes: the constant is the sum of the means -/

section JointMean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {n : ℕ}

/-- The almost sure sum of a joint mix of integrable distributions is the sum of their means. -/
theorem IsJointMix.ae_sum_eq {G : Fin n → Measure E} {P : Measure (Fin n → E)}
    (h : IsJointMix G P) (hi : ∀ j, Integrable id (G j)) :
    ∀ᵐ x ∂P, ∑ j, x j = ∑ j, ∫ y, y ∂(G j) := by
  obtain ⟨hP, ⟨s, hs⟩, hm⟩ := h
  have hint : ∀ j, Integrable (fun x : Fin n → E => x j) P := by
    intro j
    have := hi j
    rw [← hm j] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply j).aemeasurable).1 this
  have h1 : ∫ x, ∑ j, x j ∂P = s := by
    rw [integral_congr_ae hs]; simp
  have h2 : ∫ x, ∑ j, x j ∂P = ∑ j, ∫ y, y ∂(G j) := by
    rw [integral_finsetSum _ fun j _ => hint j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm j]
    exact (integral_map (by fun_prop : Measurable fun x : Fin n → E => x j).aemeasurable
      (aestronglyMeasurable_id (μ := P.map fun x => x j))).symm
  filter_upwards [hs] with x hx
  rw [hx, ← h1, h2]

end JointMean

/-! ### The body, the level distribution and Fubini's theorem -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The map `(s, y) ↦ (s, c s + r s • y)`. -/
def secMap (r : ℝ → ℝ) (c : ℝ → V) (p : ℝ × V) : ℝ × V := (p.1, c p.1 + r p.1 • p.2)

/-- The body `K = {(s, c s + r s • y) : α ≤ s ≤ β, y ∈ F}` of Theorem 62. -/
def body (α β : ℝ) (r : ℝ → ℝ) (c : ℝ → V) (F : Set V) : Set (ℝ × V) :=
  secMap r c '' (Icc α β ×ˢ F)

/-- The (unnormalised) level density `r ^ d`, as an extended nonnegative real. -/
def levelDens (r : ℝ → ℝ) (d : ℕ) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (r s ^ d)

/-- The normalising constant `∫_α^β r ^ d`. -/
def levelNorm (α β : ℝ) (r : ℝ → ℝ) (d : ℕ) : ℝ≥0∞ := ∫⁻ s in Icc α β, levelDens r d s

/-- The level distribution: density proportional to `r ^ d` on `[α, β]`. -/
def levelDist (α β : ℝ) (r : ℝ → ℝ) (d : ℕ) : Measure ℝ :=
  (levelNorm α β r d)⁻¹ • (volume.restrict (Icc α β)).withDensity (levelDens r d)

/-- The law of `(S, c S + r S • Y)` with `S ∼ levelDist α β r d` and `Y ∼ U(F)` independent: first
coordinate with density `∝ r ^ d`, and given it, the rest uniform on the section
`c S + r S • F`. -/
def bodyLaw (α β : ℝ) (r : ℝ → ℝ) (c : ℝ → V) (F : Set V) (d : ℕ) : Measure (ℝ × V) :=
  ((levelDist α β r d).prod (unifSet F)).map (secMap r c)

lemma measurable_levelDens {r : ℝ → ℝ} (hr : Measurable r) (d : ℕ) :
    Measurable (levelDens r d) :=
  ENNReal.measurable_ofReal.comp (hr.pow_const d)

lemma measurable_secMap {r : ℝ → ℝ} {c : ℝ → V} (hr : Measurable r) (hc : Measurable c) :
    Measurable (secMap r c) :=
  measurable_fst.prodMk ((hc.comp measurable_fst).add ((hr.comp measurable_fst).smul
    measurable_snd))

lemma continuous_secMap {r : ℝ → ℝ} {c : ℝ → V} (hr : Continuous r) (hc : Continuous c) :
    Continuous (secMap r c) := by
  unfold secMap; fun_prop

lemma isCompact_body {α β : ℝ} {r : ℝ → ℝ} {c : ℝ → V} {F : Set V} (hr : Continuous r)
    (hc : Continuous c) (hF : IsCompact F) : IsCompact (body α β r c F) :=
  (isCompact_Icc.prod hF).image (continuous_secMap hr hc)

lemma levelNorm_lt_top {α β : ℝ} {r : ℝ → ℝ} (hr : Continuous r) (d : ℕ) :
    levelNorm α β r d < ∞ := by
  unfold levelNorm levelDens
  exact (((hr.pow d).continuousOn).integrableOn_compact isCompact_Icc).setLIntegral_lt_top
    |>.trans_le' (le_of_eq (by rfl)) |>.trans_le' le_rfl

lemma levelNorm_pos {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) (d : ℕ) : 0 < levelNorm α β r d := by
  unfold levelNorm
  have hm : Measurable (levelDens r d) := measurable_levelDens hr.measurable d
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hm]
  intro h0
  have hsub : Ioo α β ⊆ {s | ¬ levelDens r d s = 0} := by
    intro s hs
    simp only [levelDens, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (hpos s hs) d
  have hnull : volume.restrict (Icc α β) {s | ¬ levelDens r d s = 0} = 0 := by
    rw [EventuallyEq, ae_iff] at h0
    simpa using h0
  have := measure_mono_null hsub hnull
  rw [Measure.restrict_apply' measurableSet_Icc, inter_eq_left.2 Ioo_subset_Icc_self,
    Real.volume_Ioo] at this
  simp only [ENNReal.ofReal_eq_zero, tsub_le_iff_right, zero_add] at this
  linarith

lemma isProbabilityMeasure_unifSet {F : Set V} (h0 : volume F ≠ 0) (ht : volume F ≠ ∞) :
    IsProbabilityMeasure (unifSet F) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 ht

/-- Volume of the image of a set under `y ↦ a + t • y`. -/
lemma volume_image_homothety (a : V) (t : ℝ) (S : Set V) :
    volume ((fun y => a + t • y) '' S) = ENNReal.ofReal |t ^ finrank ℝ V| * volume S := by
  have : (fun y => a + t • y) '' S = (fun y => a + y) '' (t • S) := by
    rw [← image_smul, image_image]
  rw [this, image_add_left, measure_preimage_add, Measure.addHaar_smul]

/-- The section of `A ∩ K` at the level `s`. -/
lemma preimage_inter_body {α β : ℝ} {r : ℝ → ℝ} {c : ℝ → V} {F : Set V} (A : Set (ℝ × V))
    (s : ℝ) : Prod.mk s ⁻¹' (A ∩ body α β r c F) =
      if s ∈ Icc α β then (fun y => c s + r s • y) '' (Prod.mk s ⁻¹' (secMap r c ⁻¹' A) ∩ F)
      else ∅ := by
  ext y
  simp only [mem_preimage, mem_inter_iff, body, mem_image, secMap, mem_prod, Prod.mk.injEq]
  split_ifs with hs
  · constructor
    · rintro ⟨hA, p, ⟨-, hp⟩, h1, h2⟩
      subst h1
      exact ⟨p.2, ⟨show (p.1, c p.1 + r p.1 • p.2) ∈ A by rw [h2]; exact hA, hp⟩, h2⟩
    · rintro ⟨x, ⟨hA, hx⟩, rfl⟩
      exact ⟨hA, (s, x), ⟨hs, hx⟩, rfl, rfl⟩
  · simp only [mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨p, ⟨hp, -⟩, h1, -⟩
    exact hs (h1 ▸ hp)

/-- Fubini's theorem for the body:
`vol (A ∩ K) = ∫_α^β r(s)^d vol({y ∈ F : (s, c s + r s y) ∈ A}) ds`. -/
lemma volume_inter_body {α β : ℝ} {r : ℝ → ℝ} {c : ℝ → V} {F : Set V} (hr : Continuous r)
    (hc : Continuous c) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hF : IsCompact F)
    {A : Set (ℝ × V)} (hA : MeasurableSet A) :
    volume (A ∩ body α β r c F) = ∫⁻ s in Icc α β,
      levelDens r (finrank ℝ V) s * volume (Prod.mk s ⁻¹' (secMap r c ⁻¹' A) ∩ F) := by
  have hK : MeasurableSet (A ∩ body α β r c F) :=
    hA.inter (isCompact_body hr hc hF).isClosed.measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hK, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun s => ?_
  rw [preimage_inter_body]
  by_cases hs : s ∈ Icc α β
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs), indicator_of_mem hs, volume_image_homothety,
      levelDens, abs_of_nonneg (pow_nonneg (hr0 s hs) _)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs), indicator_of_notMem hs, measure_empty]

lemma measurable_measure_section {r : ℝ → ℝ} {c : ℝ → V} (hr : Measurable r) (hc : Measurable c)
    {F : Set V} (hF : MeasurableSet F) {A : Set (ℝ × V)} (hA : MeasurableSet A)
    (μ : Measure V) [SFinite μ] :
    Measurable fun s => μ (Prod.mk s ⁻¹' (secMap r c ⁻¹' A) ∩ F) := by
  have : (fun s => μ (Prod.mk s ⁻¹' (secMap r c ⁻¹' A) ∩ F)) =
      fun s => μ (Prod.mk s ⁻¹' (secMap r c ⁻¹' A ∩ (univ ×ˢ F))) := by
    funext s; congr 1; ext y; simp
  rw [this]
  exact measurable_measure_prodMk_left
    ((measurable_secMap hr hc hA).inter (MeasurableSet.univ.prod hF))

lemma volume_body {α β : ℝ} {r : ℝ → ℝ} {c : ℝ → V} {F : Set V} (hr : Continuous r)
    (hc : Continuous c) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hF : IsCompact F) :
    volume (body α β r c F) = levelNorm α β r (finrank ℝ V) * volume F := by
  have := volume_inter_body hr hc hr0 hF MeasurableSet.univ
  simp only [univ_inter, preimage_univ] at this
  rw [this, levelNorm, ← lintegral_mul_const _ (measurable_levelDens hr.measurable _)]

/-- **Fubini's theorem for `K`** (first sentence of the proof of Theorem 62): the uniform
distribution on `K` is the law of `(S, c S + r S • Y)`, where `S` has the density proportional to
`r ^ (k-1)` on `[α, β]` and `Y ∼ U(F)` is independent of `S`. -/
theorem unifSet_body_eq {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} {c : ℝ → V} {F : Set V}
    (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s)
    (hc : Continuous c) (hF : IsCompact F) (hFi : (interior F).Nonempty) :
    unifSet (body α β r c F) = bodyLaw α β r c F (finrank ℝ V) := by
  set d := finrank ℝ V
  have hFm : MeasurableSet F := hF.isClosed.measurableSet
  have hF0 : volume F ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ hFi).ne'
  have hFt : volume F ≠ ∞ := hF.measure_lt_top.ne
  have hN0 : levelNorm α β r d ≠ 0 := (levelNorm_pos hαβ hr hpos d).ne'
  have hNt : levelNorm α β r d ≠ ∞ := (levelNorm_lt_top hr d).ne
  have hρ := measurable_levelDens hr.measurable d
  have := isProbabilityMeasure_unifSet hF0 hFt
  ext A hA
  have hT := measurable_measure_section hr.measurable hc.measurable hFm hA volume
  rw [unifSet, smul_apply, Measure.restrict_apply hA, volume_inter_body hr hc hr0 hF hA,
    volume_body hr hc hr0 hF, bodyLaw, Measure.map_apply (measurable_secMap hr.measurable
      hc.measurable) hA, Measure.prod_apply (measurable_secMap hr.measurable hc.measurable hA),
    levelDist, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hρ
      (measurable_measure_prodMk_left (measurable_secMap hr.measurable hc.measurable hA))]
  have e : ∀ s, (levelDens r d * fun x => unifSet F (Prod.mk x ⁻¹' (secMap r c ⁻¹' A))) s =
      (volume F)⁻¹ * (levelDens r d s * volume (Prod.mk s ⁻¹' (secMap r c ⁻¹' A) ∩ F)) := by
    intro s
    simp only [Pi.mul_apply, unifSet, smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (measurable_prodMk_left (measurable_secMap hr.measurable
      hc.measurable hA))]
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hF0), smul_eq_mul,
    ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt), mul_assoc]
  rfl

/-! ### The construction of Theorem 62 -/

section Construction

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The levels `S` allow the scaling property of `F` to mix the sections `U(r(S i) F)`:
`r(S i) ≥ 0`, not all zero, and the fibre condition `m · max r(S i) ≤ ∑ r(S i)`. -/
def Good (r : ℝ → ℝ) (m : ℝ) (S : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ r (S i)) ∧ (∃ i, r (S i) ≠ 0) ∧ ∀ k, m * r (S k) ≤ ∑ i, r (S i)

open Classical in
/-- The section components `W`: given the levels `S` and the randomness `ω`, the joint mix
`Φ (r ∘ S) ω` of `U(r(S i) F)` given by the scaling property, and `0` when `S` is not `Good`
(a null event under the hypotheses of Theorem 62). -/
def secW (r : ℝ → ℝ) (m : ℝ) (Φ : (Fin n → ℝ) → Ω → (Fin n → V)) (S : Fin n → ℝ) (ω : Ω) :
    Fin n → V :=
  if Good r m S then Φ (fun i => r (S i)) ω else 0

/-- The joint law of `X_i = (S_i, c(S_i) + W_i)`, `i < n`, where `S ∼ P` and the randomness `ω ∼ ρ`
of the section mixer `Φ` is independent of `S`. -/
def homMix (r : ℝ → ℝ) (c : ℝ → V) (m : ℝ) (Φ : (Fin n → ℝ) → Ω → (Fin n → V))
    (P : Measure (Fin n → ℝ)) (ρ : Measure Ω) : Measure (Fin n → ℝ × V) :=
  (P.prod ρ).map (fun p i => (p.1 i, c (p.1 i) + secW r m Φ p.1 p.2 i))

lemma measurableSet_good {r : ℝ → ℝ} (hr : Measurable r) (m : ℝ) :
    MeasurableSet {S : Fin n → ℝ | Good r m S} := by
  have h1 : ∀ i, Measurable fun S : Fin n → ℝ => r (S i) :=
    fun i => hr.comp (measurable_pi_apply i)
  have hs : Measurable fun S : Fin n → ℝ => ∑ i, r (S i) :=
    Finset.measurable_sum _ fun i _ => h1 i
  have e : {S : Fin n → ℝ | Good r m S} = (⋂ i, {S | 0 ≤ r (S i)}) ∩
      ((⋃ i, (fun S : Fin n → ℝ => r (S i)) ⁻¹' {0}ᶜ) ∩ ⋂ k, {S | m * r (S k) ≤ ∑ i, r (S i)}) := by
    ext S; simp [Good]
  rw [e]
  exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const (h1 i)).inter
    ((MeasurableSet.iUnion fun i => (h1 i) (measurableSet_singleton 0).compl).inter
      (MeasurableSet.iInter fun k => measurableSet_le (measurable_const.mul (h1 k)) hs))

lemma measurable_secW {r : ℝ → ℝ} (hr : Measurable r) (m : ℝ)
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ)) :
    Measurable fun p : (Fin n → ℝ) × Ω => secW r m Φ p.1 p.2 := by
  have hg : Measurable fun p : (Fin n → ℝ) × Ω => Φ (fun i => r (p.1 i)) p.2 :=
    hΦ.comp ((measurable_pi_iff.2 fun i => (hr.comp (measurable_pi_apply i)).comp
      measurable_fst).prodMk measurable_snd)
  exact Measurable.ite ((measurableSet_good hr m).preimage measurable_fst) hg measurable_const

lemma measurable_homMap {r : ℝ → ℝ} {c : ℝ → V} (hr : Measurable r) (hc : Measurable c) (m : ℝ)
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ)) :
    Measurable fun p : (Fin n → ℝ) × Ω => fun i => (p.1 i, c (p.1 i) + secW r m Φ p.1 p.2 i) :=
  measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((hc.comp ((measurable_pi_apply i).comp measurable_fst)).add
      ((measurable_pi_apply i).comp (measurable_secW hr m hΦ)))

/-- The marginals of the construction: if a.s. the levels are `Good` and `S_j ∼ λ`, then
`X_j = (S_j, c(S_j) + W_j)` has the law of `(S, c S + r S • Y)`, `S ∼ λ`, `Y ∼ μF`
independent. -/
theorem homMix_map_eval {r : ℝ → ℝ} {c : ℝ → V} (hr : Measurable r) (hc : Measurable c) {m : ℝ}
    {μF : Measure V} [SFinite μF] {ρ : Measure Ω} [SFinite ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => μF.map (fun y => lam i • y)) (ρ.map (Φ lam)))
    {P : Measure (Fin n → ℝ)} [SFinite P] (hgood : ∀ᵐ S ∂P, Good r m S)
    {lev : Measure ℝ} {j : Fin n} (hPj : P.map (fun x => x j) = lev) :
    (homMix r c m Φ P ρ).map (fun x => x j) = (lev.prod μF).map (secMap r c) := by
  have hX := measurable_homMap hr hc m hΦ
  have hsec := measurable_secMap hr hc
  ext A hA
  have hXj : Measurable fun p : (Fin n → ℝ) × Ω =>
      (p.1 j, c (p.1 j) + secW r m Φ p.1 p.2 j) := (measurable_pi_apply j).comp hX
  rw [homMix, Measure.map_map (measurable_pi_apply j) hX, Measure.map_apply hsec hA,
    Measure.map_apply (by exact hXj) hA, Measure.prod_apply ((measurable_pi_apply j).comp hX hA),
    Measure.prod_apply (hsec hA), ← hPj,
    lintegral_map (measurable_measure_prodMk_left (hsec hA)) (measurable_pi_apply j)]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with S hS
  have hΦS : Measurable (Φ fun i => r (S i)) := hΦ.comp measurable_prodMk_left
  have hB : MeasurableSet {w : V | (S j, c (S j) + w) ∈ A} :=
    (measurable_const.prodMk (measurable_const.add measurable_id)) hA
  have e : Prod.mk S ⁻¹' (((fun f : Fin n → ℝ × V => f j) ∘ fun p : (Fin n → ℝ) × Ω =>
      fun i => (p.1 i, c (p.1 i) + secW r m Φ p.1 p.2 i)) ⁻¹' A) =
      (Φ fun i => r (S i)) ⁻¹' ((fun w : Fin n → V => w j) ⁻¹' {w | (S j, c (S j) + w) ∈ A}) := by
    ext ω; simp [secW, hS]
  rw [e, ← Measure.map_apply hΦS ((measurable_pi_apply j) hB),
    ← Measure.map_apply (measurable_pi_apply j) hB,
    (hmix _ hS.1 hS.2.1 hS.2.2).2.2 j, Measure.map_apply (measurable_const_smul _) hB]
  rfl

/-- The sum of the construction: if `P` has a.s. constant sum `s₀`, the levels are a.s. `Good`
and `μF` is integrable with mean `0`, then with `c s = c₀ + s • c₁` the sum `∑ X_i` is a.s. equal
to `(s₀, n • c₀ + s₀ • c₁)`. -/
theorem homMix_ae_sum {r : ℝ → ℝ} (hr : Measurable r) {c₀ c₁ : V} {m : ℝ}
    {μF : Measure V} (hint : Integrable id μF) (hcen : ∫ y, y ∂μF = 0)
    {ρ : Measure Ω} [SFinite ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => μF.map (fun y => lam i • y)) (ρ.map (Φ lam)))
    {P : Measure (Fin n → ℝ)} [SFinite P] (hgood : ∀ᵐ S ∂P, Good r m S)
    {s₀ : ℝ} (hs₀ : ∀ᵐ S ∂P, ∑ i, S i = s₀) :
    ∀ᵐ x ∂(homMix r (fun s => c₀ + s • c₁) m Φ P ρ),
      ∑ i, x i = (s₀, (n : ℝ) • c₀ + s₀ • c₁) := by
  have hX := measurable_homMap hr (c := fun s => c₀ + s • c₁) (by fun_prop) m hΦ
  have hset : ∀ t : ℝ × V, MeasurableSet {x : Fin n → ℝ × V | ∑ i, x i = t} := fun t =>
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton t)
  have hsetV : MeasurableSet {w : Fin n → V | ∑ i, w i = 0} :=
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton 0)
  rw [homMix, ae_map_iff hX.aemeasurable (hset _)]
  refine (Measure.ae_prod_iff_ae_ae (hX (hset _))).2 ?_
  filter_upwards [hgood, hs₀] with S hS hsum
  have hΦS : Measurable (Φ fun i => r (S i)) := hΦ.comp measurable_prodMk_left
  have hJ := hmix _ hS.1 hS.2.1 hS.2.2
  have hi : ∀ j, Integrable id (μF.map fun y => r (S j) • y) := by
    intro j
    rw [integrable_map_measure aestronglyMeasurable_id (measurable_const_smul _).aemeasurable]
    exact hint.smul (r (S j))
  have hW := IsJointMix.ae_sum_eq hJ hi
  have hmean : ∀ j, ∫ y, y ∂(μF.map fun y => r (S j) • y) = 0 := by
    intro j
    rw [integral_map (f := fun y : V => y) (measurable_const_smul _).aemeasurable
      (aestronglyMeasurable_id (μ := μF.map fun y => r (S j) • y)),
      integral_smul, hcen, smul_zero]
  simp only [hmean, Finset.sum_const_zero] at hW
  filter_upwards [(ae_map_iff hΦS.aemeasurable hsetV).1 hW] with ω hω
  simp only [secW, hS, ite_true]
  ext
  · simp [Prod.fst_sum, hsum]
  · rw [Prod.snd_sum]
    simp only [Finset.sum_add_distrib, hω, add_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Finset.sum_smul, hsum]
    simp [Nat.cast_smul_eq_nsmul]

end Construction

/-! ### Theorem 62 -/

section Theorem62

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma levelDist_ae_mem (α β : ℝ) (r : ℝ → ℝ) (d : ℕ) :
    ∀ᵐ s ∂levelDist α β r d, s ∈ Icc α β :=
  Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)) _

lemma levelDist_ae_ne (α β : ℝ) {r : ℝ → ℝ} (hr : Measurable r) {d : ℕ} (hd : d ≠ 0) :
    ∀ᵐ s ∂levelDist α β r d, r s ≠ 0 := by
  refine Measure.ae_smul_measure ?_ _
  rw [ae_withDensity_iff (measurable_levelDens hr d)]
  exact ae_of_all _ fun s hs h0 => hs (by simp [levelDens, h0, zero_pow hd])

lemma isProbabilityMeasure_levelDist {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) (d : ℕ) : IsProbabilityMeasure (levelDist α β r d) := by
  constructor
  rw [levelDist, smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (levelNorm_pos hαβ hr hpos d).ne' (levelNorm_lt_top hr d).ne

lemma integrable_unifSet {F : Set V} (hF : IsCompact F) (hF0 : volume F ≠ 0) :
    Integrable id (unifSet F) :=
  (continuous_id.continuousOn.integrableOn_compact hF).smul_measure (ENNReal.inv_ne_top.2 hF0)

/-- **Theorem 62** (`b:thm:hom`), the complete mix. Let `k - 1 = finrank ℝ V ≥ 1`, let `F ⊆ V` be
compact with nonempty interior (dimension `k - 1`) and centroid `0`, and let `Φ` be the joint mix
of `U(λ₁ F), …, U(λₙ F)` given by the scaling property of `F` with constant `m` (a jointly
measurable function of `λ` and of an independent random element `ω ∼ ρ`). Let `α < β`, let `r` be
continuous, `≥ 0` on `[α, β]` and `> 0` on `(α, β)`, let `c s = c₀ + s • c₁` (affine), and let
`K = body α β r c F`. Let `P` be an `n`-complete mix of the level distribution (density
`∝ r ^ (k-1)` on `[α, β]`) satisfying the fibre condition `m · max r(S i) ≤ ∑ r(S i)` a.s.
Then the law of `X_i = (S_i, c(S_i) + W_i)` is an `n`-complete mix of `U(K)`. -/
theorem isCompleteMix_homMix {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s) (c₀ c₁ : V)
    {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    {m : ℝ} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam)))
    (hn : 2 ≤ n) {P : Measure (Fin n → ℝ)}
    (hP : IsCompleteMix n (levelDist α β r (finrank ℝ V)) P)
    (hfib : ∀ᵐ S ∂P, ∀ k, m * r (S k) ≤ ∑ i, r (S i)) :
    IsCompleteMix n (unifSet (body α β r (fun s => c₀ + s • c₁) F))
      (homMix r (fun s => c₀ + s • c₁) m Φ P ρ) := by
  obtain ⟨hPp, ⟨s₀, hs₀⟩, hPm⟩ := hP
  have hc : Continuous fun s : ℝ => c₀ + s • c₁ := by fun_prop
  have hF0 : volume F ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ hFi).ne'
  have hFt : volume F ≠ ∞ := hF.measure_lt_top.ne
  have := isProbabilityMeasure_unifSet hF0 hFt
  have hgood : ∀ᵐ S ∂P, Good r m S := by
    have h1 : ∀ i, ∀ᵐ S ∂P, S i ∈ Icc α β ∧ r (S i) ≠ 0 := by
      intro i
      have h := (levelDist_ae_mem α β r (finrank ℝ V)).and
        (levelDist_ae_ne α β hr.measurable (by omega : finrank ℝ V ≠ 0))
      rw [← show P.map (fun x => x i) = levelDist α β r (finrank ℝ V) from hPm i] at h
      exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h
    filter_upwards [ae_all_iff.2 h1, hfib] with S hS hf
    exact ⟨fun i => hr0 _ (hS i).1, ⟨⟨0, by omega⟩, (hS _).2⟩, hf⟩
  refine ⟨?_, ⟨_, homMix_ae_sum hr.measurable (integrable_unifSet hF hF0) hcen hΦ hmix hgood
    hs₀⟩, fun j => ?_⟩
  · unfold homMix; infer_instance
  · rw [homMix_map_eval hr.measurable hc.measurable hΦ hmix hgood (hPm j),
      unifSet_body_eq hαβ hr hr0 hpos hc hF hFi]
    rfl

/-- **Theorem 62** (`b:thm:hom`), convexity, for a convex `F` containing `0`: if `r ≥ 0` is
concave on `[α, β]` and `c` is affine, the body `K` is convex. -/
theorem convex_body_of_zero_mem {α β : ℝ} {r : ℝ → ℝ} (hrc : ConcaveOn ℝ (Icc α β) r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (c₀ c₁ : V) {F : Set V} (hFc : Convex ℝ F)
    (h0F : (0 : V) ∈ F) : Convex ℝ (body α β r (fun s => c₀ + s • c₁) F) := by
  rintro _ ⟨⟨s₁, y₁⟩, ⟨hs₁, hy₁⟩, rfl⟩ _ ⟨⟨s₂, y₂⟩, ⟨hs₂, hy₂⟩, rfl⟩ a b ha hb hab
  simp only at hs₁ hy₁ hs₂ hy₂
  set s := a * s₁ + b * s₂ with hs_def
  have hs : s ∈ Icc α β := convex_Icc α β hs₁ hs₂ ha hb hab
  have hle : a * r s₁ + b * r s₂ ≤ r s := by
    have := hrc.2 hs₁ hs₂ ha hb hab
    simpa [smul_eq_mul] using this
  have h1 : 0 ≤ a * r s₁ := mul_nonneg ha (hr0 _ hs₁)
  have h2 : 0 ≤ b * r s₂ := mul_nonneg hb (hr0 _ hs₂)
  set t₁ := a * r s₁ / r s
  set t₂ := b * r s₂ / r s
  have ht₁ : 0 ≤ t₁ := div_nonneg h1 (hr0 _ hs)
  have ht₂ : 0 ≤ t₂ := div_nonneg h2 (hr0 _ hs)
  have ht : t₁ + t₂ ≤ 1 := by
    rcases (hr0 _ hs).eq_or_lt with h | h
    · simp [t₁, t₂, ← h]
    · rw [← add_div, div_le_one h]; exact hle
  have hy : t₁ • y₁ + t₂ • y₂ ∈ F := by
    have := hFc.sum_mem (t := Finset.univ) (w := ![t₁, t₂, 1 - t₁ - t₂]) (z := ![y₁, y₂, 0])
      (by intro i _; fin_cases i <;> simp [ht₁, ht₂]; linarith)
      (by simp [Fin.sum_univ_three])
      (by intro i _; fin_cases i <;> simp [hy₁, hy₂, h0F])
    simpa [Fin.sum_univ_three] using this
  have heq : r s • (t₁ • y₁ + t₂ • y₂) = (a * r s₁) • y₁ + (b * r s₂) • y₂ := by
    rcases (hr0 _ hs).eq_or_lt with h | h
    · have e1 : a * r s₁ = 0 := by linarith
      have e2 : b * r s₂ = 0 := by linarith
      simp [← h, e1, e2]
    · rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h.ne', mul_div_cancel₀ _ h.ne']
  refine ⟨(s, t₁ • y₁ + t₂ • y₂), ⟨hs, hy⟩, ?_⟩
  simp only [secMap, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [heq]
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [hs_def, smul_add, add_smul, smul_smul, sub_smul, one_smul]
  abel

/-- The centroid of a compact convex set of positive volume lies in it. -/
lemma integral_mem_of_convex {F : Set V} (hF : IsCompact F) (hFc : Convex ℝ F)
    (hF0 : volume F ≠ 0) : ∫ y, y ∂(unifSet F) ∈ F := by
  have := isProbabilityMeasure_unifSet hF0 hF.measure_lt_top.ne
  exact hFc.integral_mem hF.isClosed
    (Measure.ae_smul_measure (ae_restrict_mem hF.isClosed.measurableSet) _)
    (integrable_unifSet hF hF0)

/-- **Theorem 62** (`b:thm:hom`), convexity, with the hypotheses of the paper: `F` compact and
convex of dimension `k - 1` (nonempty interior) with centroid `0`, `r ≥ 0` concave on `[α, β]`,
`c` affine. Then `K` is convex. -/
theorem convex_body {α β : ℝ} {r : ℝ → ℝ} (hrc : ConcaveOn ℝ (Icc α β) r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (c₀ c₁ : V) {F : Set V} (hF : IsCompact F)
    (hFc : Convex ℝ F) (hFi : (interior F).Nonempty) (hcen : ∫ y, y ∂(unifSet F) = 0) :
    Convex ℝ (body α β r (fun s => c₀ + s • c₁) F) :=
  convex_body_of_zero_mem hrc hr0 c₀ c₁ hFc (hcen ▸ integral_mem_of_convex hF hFc
    (Measure.measure_pos_of_nonempty_interior _ hFi).ne')

end Theorem62

/-! ### Formulas for the level distribution -/

section LevelFormulas

variable {α β : ℝ} {r : ℝ → ℝ} {d : ℕ}

/-- The level density `r ^ d` on `[α, β]`, extended by `0`. -/
def levelFun (α β : ℝ) (r : ℝ → ℝ) (d : ℕ) : ℝ → ℝ := (Icc α β).indicator fun s => r s ^ d

lemma levelFun_nonneg (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (s : ℝ) : 0 ≤ levelFun α β r d s := by
  unfold levelFun
  by_cases hs : s ∈ Icc α β
  · rw [indicator_of_mem hs]; exact pow_nonneg (hr0 s hs) d
  · rw [indicator_of_notMem hs]

lemma integrable_levelFun (hr : Continuous r) : Integrable (levelFun α β r d) :=
  (((hr.pow d).continuousOn).integrableOn_compact isCompact_Icc).integrable_indicator
    measurableSet_Icc

lemma levelDist_eq (_hr : Continuous r) :
    levelDist α β r d = (levelNorm α β r d)⁻¹ •
      volume.withDensity fun s => ENNReal.ofReal (levelFun α β r d s) := by
  rw [levelDist, ← withDensity_indicator measurableSet_Icc]
  congr 2
  funext s
  by_cases hs : s ∈ Icc α β <;> simp [levelFun, levelDens, hs]

/-- The normalising constant as a real integral. -/
def levelZ (α β : ℝ) (r : ℝ → ℝ) (d : ℕ) : ℝ := ∫ s in α..β, r s ^ d

lemma levelNorm_eq (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) :
    levelNorm α β r d = ENNReal.ofReal (levelZ α β r d) := by
  rw [levelNorm, levelZ, intervalIntegral.integral_of_le hαβ.le, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (f := fun s => r s ^ d)
      (((hr.pow d).continuousOn).integrableOn_compact isCompact_Icc)]
  · rfl
  · exact (ae_restrict_mem measurableSet_Icc).mono fun s hs => pow_nonneg (hr0 s hs) d

lemma levelZ_pos (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) : 0 < levelZ α β r d := by
  have h := levelNorm_pos hαβ hr hpos d
  rw [levelNorm_eq hαβ hr hr0] at h
  exact ENNReal.ofReal_pos.1 h

/-- Measures of the level distribution as integrals of the density. -/
lemma levelDist_apply_toReal (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) {A : Set ℝ} (hA : MeasurableSet A) :
    (levelDist α β r d A).toReal = (levelZ α β r d)⁻¹ * ∫ s in A, levelFun α β r d s := by
  rw [levelDist_eq hr, smul_apply, withDensity_apply _ hA, smul_eq_mul,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_levelFun hr).integrableOn
      (Eventually.of_forall fun s => levelFun_nonneg hr0 s),
    levelNorm_eq hαβ hr hr0, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg fun s => levelFun_nonneg hr0 s),
    ENNReal.toReal_ofReal (levelZ_pos hαβ hr hr0 hpos).le]

lemma measurable_levelFun (hr : Continuous r) : Measurable (levelFun α β r d) :=
  (hr.pow d).measurable.indicator measurableSet_Icc

/-- Integrals against the level distribution. -/
lemma integral_levelDist (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) (φ : ℝ → ℝ) :
    ∫ s, φ s ∂levelDist α β r d = (levelZ α β r d)⁻¹ * ∫ s in α..β, φ s * r s ^ d := by
  rw [levelDist_eq hr, integral_smul_measure, levelNorm_eq hαβ hr hr0, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (levelZ_pos hαβ hr hr0 hpos).le, smul_eq_mul]
  congr 1
  have hm : Measurable fun s => (levelFun α β r d s).toNNReal :=
    (measurable_levelFun hr).real_toNNReal
  rw [show (fun s => ENNReal.ofReal (levelFun α β r d s)) =
      fun s => ((levelFun α β r d s).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hm, intervalIntegral.integral_of_le hαβ.le,
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  congr 1
  funext s
  by_cases hs : s ∈ Icc α β
  · simp [levelFun, hs, NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (hr0 s hs) d),
      mul_comm]
  · simp [levelFun, hs]

/-- The mean of the level distribution is `meanOn α β (r ^ d)`. -/
lemma levelDist_mean (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) :
    ∫ s, s ∂levelDist α β r d = meanOn α β (fun s => r s ^ d) := by
  rw [integral_levelDist hαβ hr hr0 hpos, meanOn, levelZ, div_eq_inv_mul]

lemma integrable_id_levelDist (hαβ : α < β) (hr : Continuous r)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) : Integrable id (levelDist α β r d) := by
  have := isProbabilityMeasure_levelDist hαβ hr hpos d
  refine Integrable.of_bound aestronglyMeasurable_id (max |α| |β|) ?_
  filter_upwards [levelDist_ae_mem α β r d] with s hs
  exact abs_le_max_abs_abs hs.1 hs.2

/-- The distribution function of the level distribution shifted by `-α`. -/
lemma cdf_shift (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) {x : ℝ} (hx : 0 ≤ x) :
    ((levelDist α β r d).map (fun s => s - α) (Iic x)).toReal =
      (levelZ α β r d)⁻¹ * ∫ u in (0:ℝ)..x, levelFun α β r d (u + α) := by
  rw [Measure.map_apply (measurable_sub_const α) measurableSet_Iic]
  have e : (fun s => s - α) ⁻¹' Iic x = Iic (x + α) := by
    ext s; simp
  rw [e, levelDist_apply_toReal hαβ hr hr0 hpos measurableSet_Iic,
    intervalIntegral.integral_comp_add_right, zero_add,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Icc_subset_Iic_self]
  intro s hs
  have : s ∉ Icc α β := fun h => hs.2 ⟨h.1, hs.1⟩
  simp [levelFun, this]

/-- The distribution function of the level distribution reflected by `s ↦ β - s`. -/
lemma cdf_reflect (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) {x : ℝ} (hx : 0 ≤ x) :
    ((levelDist α β r d).map (fun s => β - s) (Iic x)).toReal =
      (levelZ α β r d)⁻¹ * ∫ u in (0:ℝ)..x, levelFun α β r d (β - u) := by
  rw [Measure.map_apply (measurable_const_sub β) measurableSet_Iic]
  have e : (fun s => β - s) ⁻¹' Iic x = Ici (β - x) := by
    ext s; simp only [mem_preimage, mem_Iic, mem_Ici]; constructor <;> intro h <;> linarith
  rw [e, levelDist_apply_toReal hαβ hr hr0 hpos measurableSet_Ici,
    intervalIntegral.integral_comp_sub_left, sub_zero,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self]
  intro s hs
  have : s ∉ Icc α β := fun h => hs.2 ⟨hs.1, h.2⟩
  simp [levelFun, this]

lemma antitoneOn_shift (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hanti : AntitoneOn r (Icc α β)) :
    AntitoneOn (fun u => levelFun α β r d (u + α)) (Ici 0) := by
  intro u hu v hv huv
  simp only [mem_Ici] at hu hv
  by_cases hv' : v + α ∈ Icc α β
  · have hu' : u + α ∈ Icc α β := ⟨by linarith, by linarith [hv'.2]⟩
    simp only [levelFun, indicator_of_mem hu', indicator_of_mem hv']
    exact pow_le_pow_left₀ (hr0 _ hv') (hanti hu' hv' (by linarith)) d
  · have h := levelFun_nonneg (d := d) hr0 (u + α)
    simp only [levelFun, indicator_of_notMem hv'] at h ⊢
    exact h

lemma antitoneOn_reflect (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hmono : MonotoneOn r (Icc α β)) :
    AntitoneOn (fun u => levelFun α β r d (β - u)) (Ici 0) := by
  intro u hu v hv huv
  simp only [mem_Ici] at hu hv
  by_cases hv' : β - v ∈ Icc α β
  · have hu' : β - u ∈ Icc α β := ⟨by linarith [hv'.1], by linarith⟩
    simp only [levelFun, indicator_of_mem hu', indicator_of_mem hv']
    exact pow_le_pow_left₀ (hr0 _ hv') (hmono hv' hu' (by linarith)) d
  · have h := levelFun_nonneg (d := d) hr0 (β - u)
    simp only [levelFun, indicator_of_notMem hv'] at h ⊢
    exact h

end LevelFormulas

/-! ### Auxiliary facts for Corollary 64 -/

/-- The integral of a function that is non-increasing on `[0, ∞)` is concave there. -/
lemma concaveOn_integral_of_antitoneOn {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 0))
    (hi : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    ConcaveOn ℝ (Ici 0) fun x => ∫ u in (0:ℝ)..x, f u := by
  refine concaveOn_of_slope_anti_adjacent (convex_Ici 0) fun {x y z} hx hz hxy hyz => ?_
  simp only [mem_Ici] at hx hz
  have hy : y ∈ Ici (0:ℝ) := mem_Ici.2 (by linarith)
  rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _),
    intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  have h1 : ∫ u in y..z, f u ≤ (z - y) * f y := by
    have := intervalIntegral.integral_mono_on hyz.le (hi y z) intervalIntegrable_const
      (fun u hu => hf hy (mem_Ici.2 (le_trans (mem_Ici.1 hy) hu.1)) hu.1)
    simpa using this
  have h2 : (y - x) * f y ≤ ∫ u in x..y, f u := by
    have := intervalIntegral.integral_mono_on hxy.le intervalIntegrable_const (hi x y)
      (fun u hu => hf (mem_Ici.2 (le_trans hx hu.1)) hy hu.2)
    simpa using this
  calc (∫ u in y..z, f u) / (z - y) ≤ f y := (div_le_iff₀ (sub_pos.2 hyz)).2 (by linarith)
    _ ≤ (∫ u in x..y, f u) / (y - x) := (le_div_iff₀ (sub_pos.2 hxy)).2 (by linarith)

/-- Complete mixes of real distributions are preserved by affine maps `x ↦ a + b x`. -/
lemma isCompleteMix_map_affine {n : ℕ} {G : Measure ℝ} {Q : Measure (Fin n → ℝ)}
    (h : IsCompleteMix n G Q) (a b : ℝ) :
    IsCompleteMix n (G.map fun x => a + b * x) (Q.map fun x i => a + b * x i) := by
  obtain ⟨hQ, ⟨s, hs⟩, hm⟩ := h
  have hf : Measurable fun (x : Fin n → ℝ) (i : Fin n) => a + b * x i :=
    measurable_pi_iff.2 fun i => measurable_const.add (measurable_const.mul (measurable_pi_apply i))
  refine ⟨inferInstance, ⟨n * a + b * s, ?_⟩, fun j => ?_⟩
  · have hS : MeasurableSet {y : Fin n → ℝ | ∑ j, y j = n * a + b * s} :=
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton _)
    rw [ae_map_iff hf.aemeasurable hS]
    filter_upwards [hs] with x hx
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, hx]
  · show _ = G.map _
    rw [Measure.map_map (measurable_pi_apply j) hf, ← show Q.map (fun x => x j) = G from hm j,
      Measure.map_map (g := fun x : ℝ => a + b * x) (by fun_prop) (measurable_pi_apply j)]
    rfl

/-- A non-increasing continuous density on `[a, b]` has its mean at most `(a + b)/2`
(Chebyshev's inequality). -/
lemma meanOn_le_mid {a b : ℝ} (hab : a < b) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hanti : AntitoneOn ρ (Icc a b))
    (hpos : 0 < ∫ x in a..b, ρ x) : meanOn a b ρ ≤ (a + b) / 2 := by
  have h := chebyshev_monotoneOn hab.le (w := fun _ => 1) (f := id) (h := fun x => -ρ x)
    (fun _ _ => zero_le_one) monotoneOn_id hanti.neg (by simp)
    (Continuous.intervalIntegrable (by fun_prop) a b)
    (Continuous.intervalIntegrable (by fun_prop) a b)
    (Continuous.intervalIntegrable (by fun_prop) a b)
  simp only [one_mul, id, mul_neg, intervalIntegral.integral_neg, integral_id,
    intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  unfold meanOn
  rw [div_le_iff₀ hpos]
  have hba : 0 < b - a := sub_pos.2 hab
  have e : (b ^ 2 - a ^ 2) / 2 = (b - a) * ((a + b) / 2) := by ring
  rw [e] at h
  nlinarith

/-- A non-decreasing continuous density on `[a, b]` has its mean at least `(a + b)/2`. -/
lemma mid_le_meanOn {a b : ℝ} (hab : a < b) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hmono : MonotoneOn ρ (Icc a b))
    (hpos : 0 < ∫ x in a..b, ρ x) : (a + b) / 2 ≤ meanOn a b ρ := by
  have h := chebyshev_monotoneOn hab.le (w := fun _ => 1) (f := id) (h := ρ)
    (fun _ _ => zero_le_one) monotoneOn_id hmono (by simp)
    (Continuous.intervalIntegrable (by fun_prop) a b)
    (Continuous.intervalIntegrable (by fun_prop) a b)
    (Continuous.intervalIntegrable (by fun_prop) a b)
  simp only [one_mul, id, integral_id, intervalIntegral.integral_const, smul_eq_mul,
    mul_one] at h
  unfold meanOn
  rw [le_div_iff₀ hpos]
  have hba : 0 < b - a := sub_pos.2 hab
  have e : (b ^ 2 - a ^ 2) / 2 = (b - a) * ((a + b) / 2) := by ring
  rw [e] at h
  nlinarith

/-! ### Corollary 64 -/

/-- **Corollary 30** (`j:cor:cm`, Part II of the paper), the sufficiency for a fixed `n`, taken
as an explicit hypothesis: a probability distribution `G` on `[0, ∞)` with a concave
distribution function on `[0, ∞)`, support in `[0, B]` and mean `μ > 0` with `B ≤ n μ` is
`n`-completely mixable. (Corollary 30 is stated with the right end of the support; any upper
bound `B` of the support with `B ≤ n μ` bounds the right end, so this is implied by it.) -/
def Cor30 (n : ℕ) : Prop :=
  ∀ G : Measure ℝ, IsProbabilityMeasure G → G (Iio 0) = 0 →
    ConcaveOn ℝ (Ici 0) (fun x => (G (Iic x)).toReal) → ∀ B : ℝ, G (Ioi B) = 0 →
    0 < ∫ x, x ∂G → B ≤ n * ∫ x, x ∂G → CompletelyMixable n G

/-- The affine function `ℓ` with `ℓ α = r α` and `ℓ β = r β`. -/
def chord (α β : ℝ) (r : ℝ → ℝ) (s : ℝ) : ℝ := r α + (s - α) / (β - α) * (r β - r α)

lemma chord_le {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hrc : ConcaveOn ℝ (Icc α β) r) {s : ℝ}
    (hs : s ∈ Icc α β) : chord α β r s ≤ r s := by
  have hL : 0 < β - α := sub_pos.2 hαβ
  have ha : 0 ≤ (β - s) / (β - α) := div_nonneg (by linarith [hs.2]) hL.le
  have hb : 0 ≤ (s - α) / (β - α) := div_nonneg (by linarith [hs.1]) hL.le
  have hab : (β - s) / (β - α) + (s - α) / (β - α) = 1 := by field_simp; ring
  have h := hrc.2 (left_mem_Icc.2 hαβ.le) (right_mem_Icc.2 hαβ.le) ha hb hab
  have e : (β - s) / (β - α) * α + (s - α) / (β - α) * β = s := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hL.ne']; ring
  simp only [smul_eq_mul] at h
  rw [e] at h
  have e1 : (β - s) / (β - α) = 1 - (s - α) / (β - α) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hL.ne']; ring
  have e2 : chord α β r s = (β - s) / (β - α) * r α + (s - α) / (β - α) * r β := by
    rw [e1]; unfold chord; ring
  linarith

lemma sum_chord {n : ℕ} (α β : ℝ) (r : ℝ → ℝ) {S : Fin n → ℝ} {t : ℝ}
    (hsum : ∑ i, S i = n * t) : ∑ i, chord α β r (S i) = n * chord α β r t := by
  unfold chord
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_sub_distrib,
    hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

section Levels

variable {α β : ℝ} {r : ℝ → ℝ} {d : ℕ}

lemma levelDist_compl_null (α β : ℝ) (r : ℝ → ℝ) (d : ℕ) :
    levelDist α β r d (Icc α β)ᶜ = 0 :=
  ae_iff.1 (levelDist_ae_mem α β r d)

/-- The levels of Corollary 64 (a) are `n`-completely mixable, by Corollary 30 after the
translation `s ↦ s - α` (non-increasing `r`) or the reflection `s ↦ β - s` (non-decreasing `r`). -/
theorem levels_mixable (hαβ : α < β) (hr : Continuous r) (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s)
    (hpos : ∀ s ∈ Ioo α β, 0 < r s) (hmono : MonotoneOn r (Icc α β) ∨ AntitoneOn r (Icc α β))
    {n : ℕ} (hn : 2 ≤ n)
    (hmean : α + (β - α) / n ≤ ∫ s, s ∂levelDist α β r d ∧
      ∫ s, s ∂levelDist α β r d ≤ β - (β - α) / n) (hC : Cor30 n) :
    ∃ P, IsCompleteMix n (levelDist α β r d) P := by
  have := isProbabilityMeasure_levelDist hαβ hr hpos d
  have hnull := levelDist_compl_null α β r d
  have hint := integrable_id_levelDist (d := d) hαβ hr hpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < β - α := sub_pos.2 hαβ
  have hq : 0 < (β - α) / n := div_pos hL hnpos
  set sbar := ∫ s, s ∂levelDist α β r d
  have hZ := levelZ_pos (d := d) hαβ hr hr0 hpos
  have hi : ∀ (g : ℝ → ℝ), Integrable g → ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun g hg a b => hg.intervalIntegrable
  rcases hmono with hmono | hanti
  · -- non-decreasing: reflect
    set G := (levelDist α β r d).map fun s => β - s
    have hmeas : Measurable fun s : ℝ => β - s := measurable_const_sub β
    have hG0 : G (Iio 0) = 0 := by
      rw [Measure.map_apply hmeas measurableSet_Iio]
      exact measure_mono_null (fun s hs => by
        simp only [mem_preimage, mem_Iio] at hs
        exact fun h => by linarith [h.2]) hnull
    have hGB : G (Ioi (β - α)) = 0 := by
      rw [Measure.map_apply hmeas measurableSet_Ioi]
      exact measure_mono_null (fun s hs => by
        simp only [mem_preimage, mem_Ioi] at hs
        exact fun h => by linarith [h.1]) hnull
    have hGmean : ∫ x, x ∂G = β - sbar := by
      rw [integral_map (f := fun x : ℝ => x) hmeas.aemeasurable
        (aestronglyMeasurable_id (μ := (levelDist α β r d).map fun s => β - s)),
        integral_sub (integrable_const β) (by exact hint)]
      simp [sbar]
    have hconc : ConcaveOn ℝ (Ici 0) fun x => (G (Iic x)).toReal := by
      have h1 := (concaveOn_integral_of_antitoneOn (antitoneOn_reflect (d := d) hr0 hmono)
        (hi _ ((integrable_levelFun hr).comp_sub_left β))).smul (inv_nonneg.2 hZ.le)
      refine h1.congr fun x hx => ?_
      simp only [smul_eq_mul]
      rw [cdf_reflect hαβ hr hr0 hpos (mem_Ici.1 hx)]
    obtain ⟨Q, hQ⟩ := hC G inferInstance hG0 hconc (β - α) hGB (by rw [hGmean]; linarith)
      (by rw [hGmean, ← div_le_iff₀' hnpos]; linarith)
    have h := isCompleteMix_map_affine hQ β (-1)
    rw [Measure.map_map (by fun_prop) hmeas, show ((fun x : ℝ => β + -1 * x) ∘ fun s => β - s)
      = id by funext s; simp, Measure.map_id] at h
    exact ⟨_, h⟩
  · -- non-increasing: translate
    set G := (levelDist α β r d).map fun s => s - α
    have hmeas : Measurable fun s : ℝ => s - α := measurable_sub_const α
    have hG0 : G (Iio 0) = 0 := by
      rw [Measure.map_apply hmeas measurableSet_Iio]
      exact measure_mono_null (fun s hs => by
        simp only [mem_preimage, mem_Iio] at hs
        exact fun h => by linarith [h.1]) hnull
    have hGB : G (Ioi (β - α)) = 0 := by
      rw [Measure.map_apply hmeas measurableSet_Ioi]
      exact measure_mono_null (fun s hs => by
        simp only [mem_preimage, mem_Ioi] at hs
        exact fun h => by linarith [h.2]) hnull
    have hGmean : ∫ x, x ∂G = sbar - α := by
      rw [integral_map (f := fun x : ℝ => x) hmeas.aemeasurable
        (aestronglyMeasurable_id (μ := (levelDist α β r d).map fun s => s - α)),
        integral_sub (by exact hint) (integrable_const α)]
      simp [sbar]
    have hconc : ConcaveOn ℝ (Ici 0) fun x => (G (Iic x)).toReal := by
      have h1 := (concaveOn_integral_of_antitoneOn (antitoneOn_shift (d := d) hr0 hanti)
        (hi _ ((integrable_levelFun hr).comp_add_right α))).smul (inv_nonneg.2 hZ.le)
      refine h1.congr fun x hx => ?_
      simp only [smul_eq_mul]
      rw [cdf_shift hαβ hr hr0 hpos (mem_Ici.1 hx)]
    obtain ⟨Q, hQ⟩ := hC G inferInstance hG0 hconc (β - α) hGB (by rw [hGmean]; linarith)
      (by rw [hGmean, ← div_le_iff₀' hnpos]; linarith)
    have h := isCompleteMix_map_affine hQ α 1
    rw [Measure.map_map (by fun_prop) hmeas, show ((fun x : ℝ => α + 1 * x) ∘ fun s => s - α)
      = id by funext s; simp, Measure.map_id] at h
    exact ⟨_, h⟩

end Levels

section Corollary64

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **Corollary 64 (a)** (`b:cor:monotone`). In the setting of Theorem 62 (`isCompleteMix_homMix`)
let `r` be concave and monotone on `[α, β]`, let `s̄` be the mean of the level distribution
(density `∝ r ^ (k-1)`) and `ℓ = chord α β r` the affine function with `ℓ α = r α`,
`ℓ β = r β`. If `n ≥ 2`, the level distribution satisfies the mean condition
`α + (β-α)/n ≤ s̄ ≤ β - (β-α)/n`, and `m · max r ≤ n ℓ(s̄)`, then `U(K)` is `n`-completely
mixable. Corollary 30 is the hypothesis `hC`. -/
theorem cor_monotone_a {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s)
    (hrc : ConcaveOn ℝ (Icc α β) r) (hmono : MonotoneOn r (Icc α β) ∨ AntitoneOn r (Icc α β))
    (c₀ c₁ : V) {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    {m : ℝ} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam)))
    (hn : 2 ≤ n)
    (hmean : α + (β - α) / n ≤ ∫ s, s ∂levelDist α β r (finrank ℝ V) ∧
      ∫ s, s ∂levelDist α β r (finrank ℝ V) ≤ β - (β - α) / n)
    (hmax : ∀ s ∈ Icc α β, m * r s ≤ n * chord α β r (∫ s, s ∂levelDist α β r (finrank ℝ V)))
    (hC : Cor30 n) :
    CompletelyMixable n (unifSet (body α β r (fun s => c₀ + s • c₁) F)) := by
  set D := finrank ℝ V
  obtain ⟨P, hP⟩ := levels_mixable (d := D) hαβ hr hr0 hpos hmono hn hmean hC
  set sbar := ∫ s, s ∂levelDist α β r D
  have hsum : ∀ᵐ S ∂P, ∑ i, S i = n * sbar := by
    filter_upwards [IsJointMix.ae_sum_eq hP fun _ => integrable_id_levelDist hαβ hr hpos]
      with S hS
    rw [hS]; simp [sbar]
  have hmem : ∀ᵐ S ∂P, ∀ i, S i ∈ Icc α β := by
    refine ae_all_iff.2 fun i => ae_of_ae_map (measurable_pi_apply i).aemeasurable ?_
    rw [show P.map (fun x => x i) = levelDist α β r D from hP.2.2 i]
    exact levelDist_ae_mem α β r D
  have hfib : ∀ᵐ S ∂P, ∀ k, m * r (S k) ≤ ∑ i, r (S i) := by
    filter_upwards [hsum, hmem] with S hS hSm k
    calc m * r (S k) ≤ n * chord α β r sbar := hmax _ (hSm k)
      _ = ∑ i, chord α β r (S i) := (sum_chord α β r hS).symm
      _ ≤ ∑ i, r (S i) := Finset.sum_le_sum fun i _ => chord_le hαβ hrc (hSm i)
  exact ⟨_, isCompleteMix_homMix hαβ hr hr0 hpos c₀ c₁ hF hFi hcen hk hΦ hmix hn hP hfib⟩

/-- **Corollary 64 (b)** (`b:cor:monotone`). In the setting of Theorem 62 with `k = finrank + 1`,
let `r` be concave and monotone on `[α, β]` and `m ≤ (k+1)/2`. Then `U(K)` is `n`-completely
mixable for every `n ≥ k + 1`. (The paper asks `k ≥ 3`; the proof does not use it.) Corollary 30
is the hypothesis `hC`; Lemma 63 enters through `Mixes.root_mean`. -/
theorem cor_monotone_b {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s)
    (hrc : ConcaveOn ℝ (Icc α β) r) (hmono : MonotoneOn r (Icc α β) ∨ AntitoneOn r (Icc α β))
    (c₀ c₁ : V) {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    {m : ℝ} (hm : m ≤ ((finrank ℝ V + 1 : ℕ) + 1 : ℝ) / 2) {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam)))
    (hn : finrank ℝ V + 1 + 1 ≤ n) (hC : Cor30 n) :
    CompletelyMixable n (unifSet (body α β r (fun s => c₀ + s • c₁) F)) := by
  set D := finrank ℝ V
  have hL : 0 < β - α := sub_pos.2 hαβ
  have hnR : ((D : ℝ) + 2) ≤ n := by exact_mod_cast (show D + 2 ≤ n by omega)
  have hD2 : (0 : ℝ) < D + 2 := by positivity
  have hmean_eq := levelDist_mean (d := D) hαβ hr hr0 hpos
  set sbar := ∫ s, s ∂levelDist α β r D
  -- Lemma 63 (for a general interval)
  have hmid : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have hB := root_mean (γ := (D : ℝ)) (Nat.cast_nonneg D) hαβ hrc hr0
    ⟨_, Ioo_subset_Icc_self hmid, (hpos _ hmid).ne'⟩
  simp only [Real.rpow_natCast] at hB
  rw [← hmean_eq] at hB
  have hq : (β - α) / n ≤ (β - α) / (D + 2) := div_le_div_of_nonneg_left hL.le hD2 hnR
  have hmean : α + (β - α) / n ≤ sbar ∧ sbar ≤ β - (β - α) / n :=
    ⟨by linarith [hB.1], by linarith [hB.2]⟩
  have hZ := levelZ_pos (d := D) hαβ hr hr0 hpos
  have hρc : Continuous fun s => r s ^ D := hr.pow D
  have hnpos : (0 : ℝ) < n := by linarith
  have hm' : m ≤ ((D : ℝ) + 2) / 2 := by
    have : (((D + 1 : ℕ) : ℝ) + 1) = (D : ℝ) + 2 := by push_cast; ring
    rw [this] at hm; exact hm
  -- the chord at `sbar`, written with `t = (sbar - α)/(β - α)`
  set t := (sbar - α) / (β - α) with ht
  have hchord : chord α β r sbar = (1 - t) * r α + t * r β := by unfold chord; rw [← ht]; ring
  have hα0 := hr0 α (left_mem_Icc.2 hαβ.le)
  have hβ0 := hr0 β (right_mem_Icc.2 hαβ.le)
  refine cor_monotone_a hαβ hr hr0 hpos hrc hmono c₀ c₁ hF hFi hcen hk hΦ hmix (by omega)
    hmean ?_ hC
  intro s hs
  rcases hmono with hmono | hanti
  · have hmid' : (α + β) / 2 ≤ sbar := by
      rw [hmean_eq]
      exact mid_le_meanOn hαβ hρc
        (fun x hx y hy hxy => pow_le_pow_left₀ (hr0 x hx) (hmono hx hy hxy) D) hZ
    have ht1 : 1 / 2 ≤ t := by rw [ht, le_div_iff₀ hL]; linarith
    have ht2 : t ≤ 1 := by rw [ht, div_le_one hL]; linarith [hmean.2, div_pos hL hnpos]
    have hrs : r s ≤ r β := hmono hs (right_mem_Icc.2 hαβ.le) hs.2
    have hc : r β / 2 ≤ chord α β r sbar := by rw [hchord]; nlinarith
    rcases le_or_gt 0 m with hm0 | hm0
    · calc m * r s ≤ m * r β := mul_le_mul_of_nonneg_left hrs hm0
        _ ≤ ((D : ℝ) + 2) / 2 * r β := mul_le_mul_of_nonneg_right hm' hβ0
        _ ≤ n * (r β / 2) := by nlinarith
        _ ≤ n * chord α β r sbar := mul_le_mul_of_nonneg_left hc hnpos.le
    · have : m * r s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm0.le (hr0 s hs)
      nlinarith
  · have hmid' : sbar ≤ (α + β) / 2 := by
      rw [hmean_eq]
      exact meanOn_le_mid hαβ hρc
        (fun x hx y hy hxy => pow_le_pow_left₀ (hr0 y hy) (hanti hx hy hxy) D) hZ
    have ht1 : t ≤ 1 / 2 := by rw [ht, div_le_iff₀ hL]; linarith
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith [hmean.1, div_pos hL hnpos]) hL.le
    have hrs : r s ≤ r α := hanti (left_mem_Icc.2 hαβ.le) hs hs.1
    have hc : r α / 2 ≤ chord α β r sbar := by rw [hchord]; nlinarith
    rcases le_or_gt 0 m with hm0 | hm0
    · calc m * r s ≤ m * r α := mul_le_mul_of_nonneg_left hrs hm0
        _ ≤ ((D : ℝ) + 2) / 2 * r α := mul_le_mul_of_nonneg_right hm' hα0
        _ ≤ n * (r α / 2) := by nlinarith
        _ ≤ n * chord α β r sbar := mul_le_mul_of_nonneg_left hc hnpos.le
    · have : m * r s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm0.le (hr0 s hs)
      nlinarith

end Corollary64

end Mixes.Homothetic
