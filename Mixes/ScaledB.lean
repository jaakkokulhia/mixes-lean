import Mixes.Scaled
import Mixes.Bodies
import Mixes.Homothetic
import Mixes.Bipyramid
import Mixes.Symm

/-!
# Section 20, measure-level parts: product sections, hulls, the class `𝒦⁺`

Item M1j (second part) of the verification priorities. The one-dimensional parts are in
`Mixes.Scaled` (namespace `Mixes.Scaled`).

* Theorem 75 (`g:thm:prod`), measure level: `scalingProperty_sliceLaw` (the construction of
  Theorem 75 for an abstract sliced law, with the scaling property of the level law and a fibre
  mixer as hypotheses).
-/

open MeasureTheory Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes

namespace ScaledB

/-! ### Monotonicity of the scaling property -/

section Mono

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- A scaling property with constant `m` gives one with every larger constant. -/
theorem scalingProperty_mono {μ : Measure E} {m m' : ℝ} (h : ScalingProperty μ m)
    (hm : m ≤ m') : ScalingProperty μ m' := by
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := h n hn
  exact ⟨Φ, hΦ, fun lam t hlam hne hk => hmix lam t hlam hne fun k =>
    (mul_le_mul_of_nonneg_right hm (hlam k)).trans (hk k)⟩

end Mono

/-! ### The construction of Theorem 75 for an abstract sliced law -/

section Core

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [SecondCountableTopology W] {n : ℕ}

/-- The map `(s, y) ↦ (s, c s + D s y)`. -/
def secL (D : ℝ → W → W) (c : ℝ → W) (p : ℝ × W) : ℝ × W := (p.1, c p.1 + D p.1 p.2)

/-- The sliced law: the law of `(S, c S + D S Y)` with `S ∼ ν` and `Y ∼ μY` independent. -/
def sliceLaw (ν : Measure ℝ) (μY : Measure W) (D : ℝ → W → W) (c : ℝ → W) : Measure (ℝ × W) :=
  (ν.prod μY).map (secL D c)

lemma measurable_secL {D : ℝ → W → W} {c : ℝ → W} (hD : Measurable fun p : ℝ × W => D p.1 p.2)
    (hc : Measurable c) : Measurable (secL D c) :=
  measurable_fst.prodMk ((hc.comp measurable_fst).add hD)

/-- The marginal of a construction in which, given the first-stage tuple `L ∼ P`, the second stage
`w L ω`, `ω ∼ ρ`, has its `i`-th coordinate distributed as `μY.map (h (L i))`. -/
theorem map_eval_cond {Ω : Type*} [MeasurableSpace Ω] {P : Measure (Fin n → ℝ)} [SFinite P]
    {ρ : Measure Ω} [SFinite ρ] {μY : Measure W} [SFinite μY]
    {w : (Fin n → ℝ) → Ω → (Fin n → W)} (hw : Measurable fun p : (Fin n → ℝ) × Ω => w p.1 p.2)
    {h : ℝ → W → W} (hh : Measurable fun q : ℝ × W => h q.1 q.2) (i : Fin n)
    (hcond : ∀ᵐ L ∂P, (ρ.map (w L)).map (fun v => v i) = μY.map (h (L i))) :
    (P.prod ρ).map (fun p => (p.1 i, w p.1 p.2 i)) =
      ((P.map fun L => L i).prod μY).map (fun q => (q.1, h q.1 q.2)) := by
  have hX : Measurable fun p : (Fin n → ℝ) × Ω => (p.1 i, w p.1 p.2 i) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp hw)
  have hY : Measurable fun q : ℝ × W => (q.1, h q.1 q.2) := measurable_fst.prodMk hh
  ext A hA
  rw [Measure.map_apply hX hA, Measure.map_apply hY hA, Measure.prod_apply (hX hA),
    Measure.prod_apply (hY hA),
    lintegral_map (measurable_measure_prodMk_left (hY hA)) (measurable_pi_apply i)]
  refine lintegral_congr_ae ?_
  filter_upwards [hcond] with L hL
  have hwL : Measurable (w L) := hw.comp measurable_prodMk_left
  have hhL : Measurable (h (L i)) := hh.comp measurable_prodMk_left
  have hB : MeasurableSet {v : W | (L i, v) ∈ A} := measurable_prodMk_left hA
  have e1 : Prod.mk L ⁻¹' ((fun p : (Fin n → ℝ) × Ω => (p.1 i, w p.1 p.2 i)) ⁻¹' A) =
      w L ⁻¹' ((fun v : Fin n → W => v i) ⁻¹' {v | (L i, v) ∈ A}) := rfl
  have e2 : Prod.mk (L i) ⁻¹' ((fun q : ℝ × W => (q.1, h q.1 q.2)) ⁻¹' A) =
      h (L i) ⁻¹' {v | (L i, v) ∈ A} := rfl
  rw [e1, e2, ← Measure.map_apply hwL ((measurable_pi_apply i) hB),
    ← Measure.map_apply (measurable_pi_apply i) hB, hL, Measure.map_apply hhL hB]

/-- The tuple of Theorem 75: `X_i = t_i + (L_i, λ_i c(S_i) + W_i)` with `S_i = L_i / λ_i`
(so `S_i = 0` and, almost surely, `X_i = t_i` when `λ_i = 0`). -/
def sliceTuple (c : ℝ → W) (lam : Fin n → ℝ) (t : Fin n → ℝ × W) (L : Fin n → ℝ)
    (w : Fin n → W) : Fin n → ℝ × W :=
  fun i => t i + (L i, lam i • c (L i / lam i) + w i)

/-- The levels `S_i = L_i / λ_i`. -/
def levels (lam L : Fin n → ℝ) : Fin n → ℝ := fun k => L k / lam k

lemma measurable_levels : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => levels p.1 p.2 :=
  measurable_pi_iff.2 fun k => ((measurable_pi_apply k).comp measurable_snd).div
    ((measurable_pi_apply k).comp measurable_fst)

lemma integrable_of_ae_Icc {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν01 : ∀ᵐ s ∂ν, s ∈ Icc (0:ℝ) 1) : Integrable id ν :=
  (integrable_const (1:ℝ)).mono' aestronglyMeasurable_id (hν01.mono fun s hs => by
    simp only [id, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hs.1, hs.2])

/-- **Theorem 75** (`g:thm:prod`), the construction, for an abstract sliced law
`law(S, c S + D S Y)`, `S ∼ ν` on `[0, 1]`, `Y ∼ μY`, `c s = c₀ + s c₁`. Hypotheses:

* `hlev`: the level law `ν` has the scaling property with constant `m_K` (Theorem 73 (b), with
  `β* ≤ m_K`), which gives the joint mix `(L_1, …, L_n)` of the laws of `λ_i S`;
* `hfib`: a measurable fibre mixer `Ψ`: whenever the scales satisfy the condition with constant
  `m_K` and the levels `S_i ∈ [0, 1]` satisfy `∑ λ_i S_i = s̄ ∑ λ_i` (the sum of the levels), the
  law of `Ψ (λ, S)` is a joint mix of the laws of `λ_i D(S_i) Y`, with sum `0`.

Then the sliced law has the scaling property with constant `m_K`; the joint mix is
`X_i = t_i + (L_i, λ_i c(S_i) + W_i)` with `S_i = L_i / λ_i` and `W = Ψ (λ, S)`, the randomness
of the two stages being independent subsequences of one uniform sequence. -/
theorem scalingProperty_sliceLaw {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν01 : ∀ᵐ s ∂ν, s ∈ Icc (0:ℝ) 1) {μY : Measure W} [IsProbabilityMeasure μY]
    {D : ℝ → W → W} (hD : Measurable fun p : ℝ × W => D p.1 p.2) (c₀ c₁ : W) {mK : ℝ}
    (hlev : ScalingProperty ν mK)
    (hfib : ∀ n : ℕ, 2 ≤ n → ∃ Ψ : (Fin n → ℝ) × (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → W),
      Measurable (Function.uncurry Ψ) ∧
      ∀ lam S : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
        (∀ k, mK * lam k ≤ ∑ i, lam i) → (∀ i, S i ∈ Icc (0:ℝ) 1) →
        ∑ i, lam i * S i = (∫ s, s ∂ν) * ∑ i, lam i →
        IsJointMix (fun i => μY.map (fun y => lam i • D (S i) y)) (unifSeq.map (Ψ (lam, S))) ∧
          ∀ᵐ v ∂(unifSeq.map (Ψ (lam, S))), ∑ i, v i = 0) :
    ScalingProperty (sliceLaw ν μY D (fun s => c₀ + s • c₁)) mK := by
  intro n hn
  obtain ⟨Φl, hΦl, hmixl⟩ := hlev n hn
  obtain ⟨Ψ, hΨ, hΨmix⟩ := hfib n hn
  set c : ℝ → W := fun s => c₀ + s • c₁ with hcdef
  have hc : Measurable c := by fun_prop
  set sbar := ∫ s, s ∂ν
  -- the first stage, as a function of the parameters and of the first subsequence
  have hL : Measurable fun q : ((Fin n → ℝ) × (Fin n → ℝ × W)) × (ℕ → ℝ) =>
      Φl (q.1.1, 0) (splitSeq q.2).1 :=
    hΦl.comp (((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk
      (measurable_fst.comp (measurable_splitSeq.comp measurable_snd)))
  have hST : ∀ {lam : Fin n → ℝ} {t : Fin n → ℝ × W},
      Measurable fun p : (Fin n → ℝ) × (Fin n → W) => sliceTuple c lam t p.1 p.2 := by
    intro lam t
    refine measurable_pi_iff.2 fun i => measurable_const.add
      (((measurable_pi_apply i).comp measurable_fst).prodMk (Measurable.add ?_
        ((measurable_pi_apply i).comp measurable_snd)))
    exact measurable_const.smul (hc.comp
      (((measurable_pi_apply i).comp measurable_fst).div_const _))
  refine ⟨fun p ω => sliceTuple c p.1 p.2 (Φl (p.1, 0) (splitSeq ω).1)
    (Ψ (p.1, levels p.1 (Φl (p.1, 0) (splitSeq ω).1)) (splitSeq ω).2), ?_, ?_⟩
  · have hS : Measurable fun q : ((Fin n → ℝ) × (Fin n → ℝ × W)) × (ℕ → ℝ) =>
        levels q.1.1 (Φl (q.1.1, 0) (splitSeq q.2).1) :=
      measurable_levels.comp ((measurable_fst.comp measurable_fst).prodMk hL)
    have hW : Measurable fun q : ((Fin n → ℝ) × (Fin n → ℝ × W)) × (ℕ → ℝ) =>
        Ψ (q.1.1, levels q.1.1 (Φl (q.1.1, 0) (splitSeq q.2).1)) (splitSeq q.2).2 :=
      hΨ.comp (((measurable_fst.comp measurable_fst).prodMk hS).prodMk
        (measurable_snd.comp (measurable_splitSeq.comp measurable_snd)))
    refine measurable_pi_iff.2 fun i => ?_
    refine ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
      (((measurable_pi_apply i).comp hL).prodMk (Measurable.add ?_
        ((measurable_pi_apply i).comp hW)))
    exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).smul
      (hc.comp (((measurable_pi_apply i).comp hL).div
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))))
  intro lam t hlam hne hm
  set P := unifSeq.map (Φl (lam, 0)) with hPdef
  have hΦl0 : Measurable (Φl (lam, 0)) := hΦl.comp measurable_prodMk_left
  have hP := hmixl lam 0 hlam hne hm
  obtain ⟨hPprob, -, hPm⟩ := hP
  set w : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → W) := fun L ω => Ψ (lam, levels lam L) ω with hwdef
  have hw : Measurable fun p : (Fin n → ℝ) × (ℕ → ℝ) => w p.1 p.2 :=
    hΨ.comp ((measurable_const.prodMk (measurable_levels.comp
      (measurable_const.prodMk measurable_fst))).prodMk measurable_snd)
  set G : (Fin n → ℝ) × (ℕ → ℝ) → (Fin n → ℝ × W) := fun p => sliceTuple c lam t p.1 (w p.1 p.2)
    with hGdef
  have hG : Measurable G := hST.comp (measurable_fst.prodMk hw)
  have hrepr : unifSeq.map (fun ω => sliceTuple c lam t (Φl (lam, 0) (splitSeq ω).1)
      (Ψ (lam, levels lam (Φl (lam, 0) (splitSeq ω).1)) (splitSeq ω).2)) =
      (P.prod unifSeq).map G := by
    rw [hPdef, ← Measure.map_id (μ := unifSeq), Measure.map_prod_map _ _ hΦl0 measurable_id,
      Measure.map_id, ← map_splitSeq, Measure.map_map (hΦl0.prodMap measurable_id)
        measurable_splitSeq, Measure.map_map hG ((hΦl0.prodMap measurable_id).comp
        measurable_splitSeq)]
    rfl
  -- facts about the levels
  have hνint := integrable_of_ae_Icc hν01
  have hmapi : ∀ i, Measurable fun x : ℝ => (0 : Fin n → ℝ) i + lam i • x := fun i => by
    fun_prop
  have hint : ∀ i, Integrable id (ν.map fun x => (0 : Fin n → ℝ) i + lam i • x) := by
    intro i
    rw [integrable_map_measure aestronglyMeasurable_id (hmapi i).aemeasurable]
    exact (integrable_const _).add (hνint.smul (lam i))
  have hmean : ∀ i, ∫ y, y ∂(ν.map fun x => (0 : Fin n → ℝ) i + lam i • x) = lam i * sbar := by
    intro i
    rw [integral_map (f := fun y : ℝ => y) (hmapi i).aemeasurable
      (aestronglyMeasurable_id (μ := ν.map fun x => (0 : Fin n → ℝ) i + lam i • x))]
    simp only [Pi.zero_apply, zero_add, smul_eq_mul]
    exact integral_const_mul _ _
  have hsum : ∀ᵐ L ∂P, ∑ i, L i = sbar * ∑ i, lam i := by
    filter_upwards [Homothetic.IsJointMix.ae_sum_eq (hmixl lam 0 hlam hne hm) hint] with L hL
    rw [hL, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hmean]; ring
  have hlev01 : ∀ i, ∀ᵐ L ∂P, L i / lam i ∈ Icc (0:ℝ) 1 ∧ lam i * (L i / lam i) = L i := by
    intro i
    have hset : MeasurableSet {x : ℝ | x / lam i ∈ Icc (0:ℝ) 1 ∧ lam i * (x / lam i) = x} :=
      ((measurable_id.div_const _) measurableSet_Icc).inter
        (measurableSet_eq_fun (measurable_const.mul (measurable_id.div_const _)) measurable_id)
    have h1 : ∀ᵐ x ∂(P.map fun L => L i), x / lam i ∈ Icc (0:ℝ) 1 ∧ lam i * (x / lam i) = x := by
      rw [hPm i, ae_map_iff (hmapi i).aemeasurable hset]
      filter_upwards [hν01] with s hs
      simp only [Pi.zero_apply, zero_add, smul_eq_mul]
      rcases eq_or_ne (lam i) 0 with h0 | h0
      · simp [h0]
      · rw [mul_div_cancel_left₀ _ h0]; exact ⟨hs, rfl⟩
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h1
  have hgood : ∀ᵐ L ∂P, (∀ i, levels lam L i ∈ Icc (0:ℝ) 1) ∧
      ∑ i, lam i * levels lam L i = sbar * ∑ i, lam i := by
    filter_upwards [ae_all_iff.2 hlev01, hsum] with L hL hs
    refine ⟨fun i => (hL i).1, ?_⟩
    rw [← hs]
    exact Finset.sum_congr rfl fun i _ => (hL i).2
  refine ⟨?_, ⟨∑ i, t i + (sbar * ∑ i, lam i, (∑ i, lam i) • c₀ + (sbar * ∑ i, lam i) • c₁),
    ?_⟩, fun i => ?_⟩
  · rw [hrepr]; infer_instance
  · -- the sum
    have hset : ∀ z : ℝ × W, MeasurableSet {x : Fin n → ℝ × W | ∑ i, x i = z} := fun z =>
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton z)
    have hsetW : MeasurableSet {v : Fin n → W | ∑ i, v i = 0} :=
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton 0)
    rw [hrepr, ae_map_iff hG.aemeasurable (hset _)]
    refine (Measure.ae_prod_iff_ae_ae (hG (hset _))).2 ?_
    filter_upwards [hgood, hsum, ae_all_iff.2 hlev01] with L hgL hsL hlL
    have hwL : Measurable (w L) := hw.comp measurable_prodMk_left
    have h0 := (hΨmix lam (levels lam L) hlam hne hm hgL.1 hgL.2).2
    filter_upwards [(ae_map_iff hwL.aemeasurable hsetW).1 h0] with ω hω
    simp only [hGdef, sliceTuple, Finset.sum_add_distrib]
    congr 1
    ext
    · simp [Prod.fst_sum, hsL]
    · rw [Prod.snd_sum]
      simp only [Finset.sum_add_distrib, hω, add_zero, hcdef, smul_add, smul_smul,
        ← Finset.sum_smul]
      congr 2
      rw [← hsL]
      exact Finset.sum_congr rfl fun i _ => (hlL i).2
  · -- the marginals
    have hcond : ∀ᵐ L ∂P, (unifSeq.map (w L)).map (fun v => v i) =
        μY.map (fun y => lam i • D (L i / lam i) y) := by
      filter_upwards [hgood] with L hgL
      exact (hΨmix lam (levels lam L) hlam hne hm hgL.1 hgL.2).1.2.2 i
    have hh : Measurable fun q : ℝ × W => lam i • D (q.1 / lam i) q.2 :=
      measurable_const.smul (hD.comp ((measurable_fst.div_const _).prodMk measurable_snd))
    have key := map_eval_cond (h := fun l y => lam i • D (l / lam i) y) hw hh i hcond
    have hA : Measurable fun q : ℝ × W => t i + (q.1, lam i • c (q.1 / lam i) + q.2) :=
      measurable_const.add (measurable_fst.prodMk ((measurable_const.smul
        (hc.comp (measurable_fst.div_const _))).add measurable_snd))
    have e1 : (fun x : Fin n → ℝ × W => x i) ∘ G = (fun q : ℝ × W =>
        t i + (q.1, lam i • c (q.1 / lam i) + q.2)) ∘
          (fun p : (Fin n → ℝ) × (ℕ → ℝ) => (p.1 i, w p.1 p.2 i)) := rfl
    have hX : Measurable fun p : (Fin n → ℝ) × (ℕ → ℝ) => (p.1 i, w p.1 p.2 i) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp hw)
    have hY : Measurable fun q : ℝ × W => (q.1, lam i • D (q.1 / lam i) q.2) :=
      measurable_fst.prodMk hh
    rw [hrepr, Measure.map_map (measurable_pi_apply i) hG, e1, ← Measure.map_map hA hX, key,
      hPm i, Measure.map_map hA hY, ← Measure.map_id (μ := μY),
      Measure.map_prod_map _ _ (hmapi i) measurable_id, Measure.map_id,
      Measure.map_map (hA.comp hY) ((hmapi i).prodMap measurable_id)]
    show _ = Measure.map (fun x => t i + lam i • x) (Measure.map (secL D c) (ν.prod μY))
    rw [Measure.map_map (g := fun x : ℝ × W => t i + lam i • x) (by fun_prop)
      (measurable_secL hD hc)]
    congr 1
    funext q
    simp only [Function.comp, Prod.map, id, secL, Pi.zero_apply, zero_add, smul_eq_mul, hcdef]
    rcases eq_or_ne (lam i) 0 with h0 | h0
    · simp [h0]
    · rw [mul_div_cancel_left₀ _ h0]
      ext <;> simp [smul_add]

end Core

/-! ### Fubini's theorem for bodies with linear sections -/

section Fubini

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

/-- The body `K = {(s, c s + D s y) : 0 ≤ s ≤ 1, y ∈ F}`. -/
def bodyL (D : ℝ → W → W) (c : ℝ → W) (F : Set W) : Set (ℝ × W) :=
  secL D c '' (Icc 0 1 ×ˢ F)

/-- The normalising constant `∫_0^1 ρ`. -/
def levNorm (ρ : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (ρ s)

/-- The level law: density proportional to `ρ` on `[0, 1]`. -/
def levLaw (ρ : ℝ → ℝ) : Measure ℝ :=
  (levNorm ρ)⁻¹ • (volume.restrict (Icc (0:ℝ) 1)).withDensity fun s => ENNReal.ofReal (ρ s)

lemma levNorm_lt_top {ρ : ℝ → ℝ} (hρ : Continuous ρ) : levNorm ρ < ∞ :=
  (hρ.continuousOn.integrableOn_compact isCompact_Icc).setLIntegral_lt_top

lemma levNorm_pos {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s) :
    0 < levNorm ρ := by
  unfold levNorm
  have hm : Measurable fun s => ENNReal.ofReal (ρ s) := ENNReal.measurable_ofReal.comp
    hρ.measurable
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hm]
  intro h0
  have hsub : Ioo (0:ℝ) 1 ⊆ {s | ¬ ENNReal.ofReal (ρ s) = 0} := by
    intro s hs
    simp only [mem_ofPred_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos s hs
  have hnull : volume.restrict (Icc (0:ℝ) 1) {s | ¬ ENNReal.ofReal (ρ s) = 0} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at h0
    simpa using h0
  have := measure_mono_null hsub hnull
  rw [Measure.restrict_apply' measurableSet_Icc, inter_eq_left.2 Ioo_subset_Icc_self,
    Real.volume_Ioo] at this
  norm_num at this

lemma isProbabilityMeasure_levLaw {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s) : IsProbabilityMeasure (levLaw ρ) := by
  constructor
  rw [levLaw, smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (levNorm_pos hρ hpos).ne' (levNorm_lt_top hρ).ne

lemma levLaw_ae_mem (ρ : ℝ → ℝ) : ∀ᵐ s ∂levLaw ρ, s ∈ Icc (0:ℝ) 1 :=
  Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)) _

lemma isCompact_bodyL {D : ℝ → W → W} {c : ℝ → W} {F : Set W}
    (hD : Continuous fun p : ℝ × W => D p.1 p.2) (hc : Continuous c) (hF : IsCompact F) :
    IsCompact (bodyL D c F) :=
  (isCompact_Icc.prod hF).image (continuous_fst.prodMk ((hc.comp continuous_fst).add hD))

lemma preimage_inter_bodyL {D : ℝ → W → W} {c : ℝ → W} {F : Set W} (A : Set (ℝ × W)) (s : ℝ) :
    Prod.mk s ⁻¹' (A ∩ bodyL D c F) =
      if s ∈ Icc (0:ℝ) 1 then (fun y => c s + D s y) '' (Prod.mk s ⁻¹' (secL D c ⁻¹' A) ∩ F)
      else ∅ := by
  ext y
  simp only [mem_preimage, mem_inter_iff, bodyL, mem_image, secL, mem_prod, Prod.mk.injEq]
  split_ifs with hs
  · constructor
    · rintro ⟨hA, p, ⟨-, hp⟩, h1, h2⟩
      subst h1
      exact ⟨p.2, ⟨show (p.1, c p.1 + D p.1 p.2) ∈ A by rw [h2]; exact hA, hp⟩, h2⟩
    · rintro ⟨x, ⟨hA, hx⟩, rfl⟩
      exact ⟨hA, (s, x), ⟨hs, hx⟩, rfl, rfl⟩
  · simp only [mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨p, ⟨hp, -⟩, h1, -⟩
    exact hs (h1 ▸ hp)

/-- Fubini's theorem for `K = bodyL D c F`, when each `D s`, `0 ≤ s ≤ 1`, multiplies volumes by
`ρ s ≥ 0`. -/
lemma volume_inter_bodyL {D : ℝ → W → W} {c : ℝ → W} {F : Set W} {ρ : ℝ → ℝ}
    (hD : Continuous fun p : ℝ × W => D p.1 p.2) (hc : Continuous c) (hF : IsCompact F)
    (hvol : ∀ s ∈ Icc (0:ℝ) 1, ∀ T : Set W, volume (D s '' T) = ENNReal.ofReal (ρ s) * volume T)
    {A : Set (ℝ × W)} (hA : MeasurableSet A) :
    volume (A ∩ bodyL D c F) = ∫⁻ s in Icc (0:ℝ) 1,
      ENNReal.ofReal (ρ s) * volume (Prod.mk s ⁻¹' (secL D c ⁻¹' A) ∩ F) := by
  have hK : MeasurableSet (A ∩ bodyL D c F) :=
    hA.inter (isCompact_bodyL hD hc hF).isClosed.measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hK, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun s => ?_
  rw [preimage_inter_bodyL]
  by_cases hs : s ∈ Icc (0:ℝ) 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs), indicator_of_mem hs]
    have e : (fun y => c s + D s y) '' (Prod.mk s ⁻¹' (secL D c ⁻¹' A) ∩ F) =
        (fun y => c s + y) '' (D s '' (Prod.mk s ⁻¹' (secL D c ⁻¹' A) ∩ F)) := by
      rw [image_image]
    rw [e, image_add_left, measure_preimage_add, hvol s hs]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs), indicator_of_notMem hs, measure_empty]

/-- **Fubini's theorem** for bodies with linear sections (as in the proof of Theorem 75): if
`D s` multiplies volumes by `ρ s` (continuous, `> 0` on `(0, 1)`) and `F` is compact with
nonempty interior, then `U(K)` is the law of `(S, c S + D S Y)`, `S` with density `∝ ρ` on
`[0, 1]` and `Y ∼ U(F)` independent. -/
theorem unifSet_bodyL_eq {D : ℝ → W → W} {c : ℝ → W} {F : Set W} {ρ : ℝ → ℝ}
    (hD : Continuous fun p : ℝ × W => D p.1 p.2) (hc : Continuous c) (hF : IsCompact F)
    (hFi : (interior F).Nonempty) (hρ : Continuous ρ)
    (hpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s)
    (hvol : ∀ s ∈ Icc (0:ℝ) 1, ∀ T : Set W, volume (D s '' T) = ENNReal.ofReal (ρ s) * volume T) :
    unifSet (bodyL D c F) = sliceLaw (levLaw ρ) (unifSet F) D c := by
  have hFm : MeasurableSet F := hF.isClosed.measurableSet
  have hF0 : volume F ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ hFi).ne'
  have hFt : volume F ≠ ∞ := hF.measure_lt_top.ne
  have hN0 : levNorm ρ ≠ 0 := (levNorm_pos hρ hpos).ne'
  have hNt : levNorm ρ ≠ ∞ := (levNorm_lt_top hρ).ne
  have hρm : Measurable fun s => ENNReal.ofReal (ρ s) := ENNReal.measurable_ofReal.comp
    hρ.measurable
  have hsec : Measurable (secL D c) := measurable_secL hD.measurable hc.measurable
  have := isProbabilityMeasure_unifSet hF0 hFt
  ext A hA
  have hvolK := volume_inter_bodyL hD hc hF hvol MeasurableSet.univ
  simp only [univ_inter, preimage_univ] at hvolK
  rw [unifSet, smul_apply, Measure.restrict_apply hA, volume_inter_bodyL hD hc hF hvol hA,
    hvolK, sliceLaw, Measure.map_apply hsec hA, Measure.prod_apply (hsec hA), levLaw,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hρm
      (measurable_measure_prodMk_left (hsec hA))]
  have e : ∀ s, ((fun s => ENNReal.ofReal (ρ s)) *
      fun x => unifSet F (Prod.mk x ⁻¹' (secL D c ⁻¹' A))) s =
      (volume F)⁻¹ * (ENNReal.ofReal (ρ s) * volume (Prod.mk s ⁻¹' (secL D c ⁻¹' A) ∩ F)) := by
    intro s
    simp only [Pi.mul_apply, unifSet, smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (measurable_prodMk_left (hsec hA))]
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hF0), smul_eq_mul,
    lintegral_mul_const _ hρm, ← levNorm, ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt)]
  ring

end Fubini

/-! ### Splitting a uniform sequence into `J` independent ones -/

section Split

variable {J : ℕ} [NeZero J]

/-- A fixed bijection `ℕ ≃ Fin J × ℕ`. -/
def natEquivFinProd (J : ℕ) [NeZero J] : ℕ ≃ Fin J × ℕ :=
  (Nat.divModEquiv J).trans (Equiv.prodComm _ _)

/-- Splitting a sequence into `J` subsequences. -/
def splitJ (J : ℕ) [NeZero J] : (ℕ → ℝ) → (Fin J → ℕ → ℝ) :=
  MeasurableEquiv.curry (Fin J) ℕ ℝ ∘ MeasurableEquiv.piCongrLeft (fun _ => ℝ) (natEquivFinProd J)

lemma measurable_splitJ : Measurable (splitJ J) :=
  (MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _)

/-- The `J` subsequences of an i.i.d. uniform sequence are independent i.i.d. uniform
sequences. -/
lemma map_splitJ : unifSeq.map (splitJ J) = Measure.pi fun _ : Fin J => unifSeq := by
  unfold splitJ
  rw [← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  have h1 : unifSeq.map (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (natEquivFinProd J)) =
      Measure.infinitePi (fun _ : Fin J × ℕ => unifI 0 1) :=
    Measure.infinitePi_map_piCongrLeft (fun _ : Fin J × ℕ => unifI 0 1) (natEquivFinProd J)
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin J) (_ : ℕ) => unifI 0 1)
  rw [h1]
  erw [h2]
  rw [Measure.infinitePi_eq_pi]
  rfl

end Split

/-! ### Fibre mixers from scaling properties -/

section FibreMixer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {n : ℕ}

/-- The scaling property of a centred law `μ` gives a measurable mixer of the scaled copies
`μ.map (a i • ·)` with sum `0`, for every `a ≥ 0` (all zero allowed) with `m max a ≤ ∑ a`. -/
theorem exists_fibreMixer {μ : Measure E} [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (hcen : ∫ y, y ∂μ = 0) {m : ℝ} (h : ScalingProperty μ m) (hn : 2 ≤ n) :
    ∃ ψ : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → E), Measurable (Function.uncurry ψ) ∧
      ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ k, m * a k ≤ ∑ i, a i) →
        IsJointMix (fun i => μ.map (fun y => a i • y)) (unifSeq.map (ψ a)) ∧
          ∀ᵐ v ∂(unifSeq.map (ψ a)), ∑ i, v i = 0 := by
  classical
  obtain ⟨Φ, hΦ, hmix⟩ := h n hn
  set C : (Fin n → ℝ) → Prop := fun a => (∃ i, a i ≠ 0) ∧ (∀ i, 0 ≤ a i) ∧
    ∀ k, m * a k ≤ ∑ i, a i with hCdef
  have hC : MeasurableSet {a | C a} := by
    have h1 : ∀ i, Measurable fun a : Fin n → ℝ => a i := fun i => measurable_pi_apply i
    have hs : Measurable fun a : Fin n → ℝ => ∑ i, a i := Finset.measurable_sum _ fun i _ => h1 i
    have e : {a | C a} = (⋃ i, (fun a : Fin n → ℝ => a i) ⁻¹' {0}ᶜ) ∩
        ((⋂ i, {a | 0 ≤ a i}) ∩ ⋂ k, {a | m * a k ≤ ∑ i, a i}) := by
      ext a; simp [hCdef]
    rw [e]
    exact (MeasurableSet.iUnion fun i => (h1 i) (measurableSet_singleton 0).compl).inter
      ((MeasurableSet.iInter fun i => measurableSet_le measurable_const (h1 i)).inter
        (MeasurableSet.iInter fun k => measurableSet_le (measurable_const.mul (h1 k)) hs))
  refine ⟨fun a ω => if C a then Φ (a, 0) ω else 0, ?_, ?_⟩
  · exact Measurable.ite (hC.preimage measurable_fst)
      (hΦ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)) measurable_const
  intro a ha hm
  by_cases hz : ∃ i, a i ≠ 0
  · have hCa : C a := ⟨hz, ha, hm⟩
    simp only [hCa, ite_true]
    have hJ := hmix a 0 ha hz hm
    simp only [Pi.zero_apply, zero_add] at hJ
    refine ⟨hJ, ?_⟩
    have hi : ∀ j, Integrable id (μ.map fun y => a j • y) := by
      intro j
      rw [integrable_map_measure aestronglyMeasurable_id (measurable_const_smul _).aemeasurable]
      exact hint.smul (a j)
    have hmean : ∀ j, ∫ y, y ∂(μ.map fun y => a j • y) = 0 := by
      intro j
      rw [integral_map (f := fun y : E => y) (measurable_const_smul _).aemeasurable
        (aestronglyMeasurable_id (μ := μ.map fun y => a j • y)), integral_smul, hcen, smul_zero]
    have := Homothetic.IsJointMix.ae_sum_eq hJ hi
    simpa only [hmean, Finset.sum_const_zero] using this
  · push Not at hz
    have hCa : ¬ C a := fun h => by obtain ⟨i, hi⟩ := h.1; exact hi (hz i)
    simp only [hCa, ite_false]
    rw [Measure.map_const, measure_univ, one_smul]
    have hs0 : ∀ᵐ v ∂(Measure.dirac (0 : Fin n → E)), ∑ i, v i = 0 := by
      rw [ae_dirac_eq]; simp
    refine ⟨⟨inferInstance, ⟨0, hs0⟩, fun i => ?_⟩, hs0⟩
    show (Measure.dirac (0 : Fin n → E)).map (fun x => x i) = μ.map (fun y => a i • y)
    rw [Measure.map_dirac' (measurable_pi_apply i), hz i]
    simp only [zero_smul, Pi.zero_apply]
    rw [Measure.map_const, measure_univ, one_smul]

end FibreMixer

/-! ### Products of homothetic copies: the fibre mixer and the volume factor -/

section Product

variable {J : ℕ} [NeZero J] {V : Fin J → Type*} [∀ j, NormedAddCommGroup (V j)]
  [∀ j, NormedSpace ℝ (V j)] [∀ j, CompleteSpace (V j)] [∀ j, MeasurableSpace (V j)]
  [∀ j, BorelSpace (V j)] [∀ j, SecondCountableTopology (V j)] {n : ℕ}

/-- The section map of a product of homothetic copies: `y ↦ (r_j(s) y_j)_j`. -/
def diagMap (r : Fin J → ℝ → ℝ) (s : ℝ) (y : (j : Fin J) → V j) : (j : Fin J) → V j :=
  fun j => r j s • y j

lemma measurable_diagMap {r : Fin J → ℝ → ℝ} (hr : ∀ j, Measurable (r j)) :
    Measurable fun p : ℝ × ((j : Fin J) → V j) => diagMap r p.1 p.2 :=
  measurable_pi_iff.2 fun j => ((hr j).comp measurable_fst).smul
    ((measurable_pi_apply j).comp measurable_snd)

lemma continuous_diagMap {r : Fin J → ℝ → ℝ} (hr : ∀ j, Continuous (r j)) :
    Continuous fun p : ℝ × ((j : Fin J) → V j) => diagMap r p.1 p.2 :=
  continuous_pi fun j => ((hr j).comp continuous_fst).smul
    ((continuous_apply j).comp continuous_snd)

/-- The fibre mixer of Theorem 75: independent joint mixes, one for each factor `F_j`, given by
the scaling properties of the `F_j`, of the scaled copies `λ_i r_j(S_i) F_j`. -/
theorem exists_prodFibreMixer {μ : (j : Fin J) → Measure (V j)}
    [∀ j, IsProbabilityMeasure (μ j)] (hint : ∀ j, Integrable id (μ j))
    (hcen : ∀ j, ∫ y, y ∂(μ j) = 0) {m : Fin J → ℝ} (h : ∀ j, ScalingProperty (μ j) (m j))
    (hn : 2 ≤ n) {r : Fin J → ℝ → ℝ} (hr : ∀ j, Measurable (r j)) :
    ∃ Ψ : (Fin n → ℝ) × (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → (j : Fin J) → V j),
      Measurable (Function.uncurry Ψ) ∧
      ∀ lam S : Fin n → ℝ, (∀ j i, 0 ≤ lam i * r j (S i)) →
        (∀ j k, m j * (lam k * r j (S k)) ≤ ∑ i, lam i * r j (S i)) →
        IsJointMix (fun i => (Measure.pi μ).map (fun y => lam i • diagMap r (S i) y))
            (unifSeq.map (Ψ (lam, S))) ∧
          ∀ᵐ v ∂(unifSeq.map (Ψ (lam, S))), ∑ i, v i = 0 := by
  choose ψ hψ hψmix using fun j => exists_fibreMixer (hint j) (hcen j) (h j) hn
  set a : (Fin n → ℝ) × (Fin n → ℝ) → Fin J → Fin n → ℝ := fun p j i => p.1 i * r j (p.2 i)
    with hadef
  have ha : ∀ j, Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => a p j :=
    fun j => measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp measurable_fst).mul
      ((hr j).comp ((measurable_pi_apply i).comp measurable_snd))
  refine ⟨fun p ω i j => ψ j (a p j) (splitJ J ω j) i, ?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact (measurable_pi_apply i).comp ((hψ j).comp ((ha j).comp measurable_fst |>.prodMk
      ((measurable_pi_apply j).comp (measurable_splitJ.comp measurable_snd))))
  intro lam S h0 hm
  have hψj : ∀ j, Measurable (ψ j (a (lam, S) j)) := fun j => (hψ j).comp measurable_prodMk_left
  set Q := Measure.pi fun j => unifSeq.map (ψ j (a (lam, S) j)) with hQdef
  have hT : Measurable fun z : (j : Fin J) → (Fin n → V j) => fun i j => z j i :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hrepr : unifSeq.map (fun ω i j => ψ j (a (lam, S) j) (splitJ J ω j) i) =
      Q.map fun z i j => z j i := by
    have hU : Measurable fun ω : Fin J → ℕ → ℝ => fun j => ψ j (a (lam, S) j) (ω j) :=
      measurable_pi_iff.2 fun j => (hψj j).comp (measurable_pi_apply j)
    rw [hQdef, ← Measure.pi_map_pi (fun j => (hψj j).aemeasurable), ← map_splitJ,
      Measure.map_map hU measurable_splitJ, Measure.map_map hT (hU.comp measurable_splitJ)]
    rfl
  have hgood : ∀ j, (∀ i, 0 ≤ a (lam, S) j i) ∧ ∀ k, m j * a (lam, S) j k ≤ ∑ i, a (lam, S) j i :=
    fun j => ⟨fun i => h0 j i, fun k => hm j k⟩
  rw [hrepr]
  have hsum0 : ∀ᵐ v ∂(Q.map fun z i j => z j i), ∑ i, v i = 0 := by
    have hset : MeasurableSet {v : Fin n → (j : Fin J) → V j | ∑ i, v i = 0} :=
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (measurableSet_singleton 0)
    rw [ae_map_iff hT.aemeasurable hset]
    have hj : ∀ j, ∀ᵐ z ∂Q, ∑ i, z j i = 0 := fun j =>
      (Measure.tendsto_eval_ae_ae (μ := fun j => unifSeq.map (ψ j (a (lam, S) j)))
        (i := j)).eventually ((hψmix j _ (hgood j).1 (hgood j).2).2)
    filter_upwards [ae_all_iff.2 hj] with z hz
    funext j
    simp only [Finset.sum_apply, hz j, Pi.zero_apply]
  refine ⟨⟨?_, ⟨0, hsum0⟩, fun i => ?_⟩, hsum0⟩
  · constructor
    rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ, measure_univ]
  · have he : Measurable fun z : (j : Fin J) → (Fin n → V j) => fun j => z j i :=
      measurable_pi_iff.2 fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)
    rw [Measure.map_map (measurable_pi_apply i) hT]
    show Q.map (fun z j => z j i) = _
    rw [hQdef, Measure.pi_map_pi (fun j => (measurable_pi_apply i).aemeasurable)]
    have e : (fun y : (j : Fin J) → V j => lam i • diagMap r (S i) y) =
        fun y j => (lam i * r j (S i)) • y j := by
      funext y j; simp [diagMap, smul_smul]
    show _ = (Measure.pi μ).map (fun y => lam i • diagMap r (S i) y)
    rw [e, Measure.pi_map_pi (fun j => (measurable_const_smul _).aemeasurable)]
    congr 1
    funext j
    exact (hψmix j _ (hgood j).1 (hgood j).2).1.2.2 i

end Product

/-! ### Theorem 75 -/

section Thm75

open Module

variable {J : ℕ} [NeZero J] {V : Fin J → Type*} [∀ j, NormedAddCommGroup (V j)]
  [∀ j, NormedSpace ℝ (V j)] [∀ j, FiniteDimensional ℝ (V j)] [∀ j, MeasureSpace (V j)]
  [∀ j, BorelSpace (V j)] [∀ j, (volume : Measure (V j)).IsAddHaarMeasure]

lemma image_diag_pi (a : Fin J → ℝ) (B : (j : Fin J) → Set (V j)) :
    (fun y : (j : Fin J) → V j => fun j => a j • y j) '' univ.pi B =
      univ.pi fun j => a j • B j := by
  ext x
  simp only [mem_image, mem_pi, mem_univ, true_implies, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩ j; exact ⟨y j, hy j, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, fun j => (hy j).1, funext fun j => (hy j).2⟩

/-- The section map `y ↦ (a_j y_j)_j` multiplies volumes by `∏_j a_j ^ (dim V_j)`. -/
lemma volume_image_diag (a : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (T : Set ((j : Fin J) → V j)) :
    volume ((fun y : (j : Fin J) → V j => fun j => a j • y j) '' T) =
      ENNReal.ofReal (∏ j, a j ^ finrank ℝ (V j)) * volume T := by
  set M : ((j : Fin J) → V j) →ₗ[ℝ] ((j : Fin J) → V j) :=
    LinearMap.pi fun j => a j • LinearMap.proj j with hMdef
  have hM : ⇑M = fun y j => a j • y j := by funext y j; simp [hMdef]
  have key : ∀ T, volume ((fun y : (j : Fin J) → V j => fun j => a j • y j) '' T) =
      ENNReal.ofReal |LinearMap.det M| * volume T := by
    intro T; rw [← hM]; exact Measure.addHaar_image_linearMap _ M T
  rw [key]
  congr 1
  set B : (j : Fin J) → Set (V j) := fun j => Metric.closedBall 0 1
  have hB0 : ∏ j, volume (B j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => (Metric.measure_closedBall_pos _ _ one_pos).ne'
  have hBt : ∏ j, volume (B j) ≠ ∞ :=
    ENNReal.prod_ne_top fun j _ => (isCompact_closedBall _ _).measure_lt_top.ne
  have h1 := key (univ.pi B)
  rw [image_diag_pi, volume_pi_pi, volume_pi_pi] at h1
  simp only [Measure.addHaar_smul] at h1
  rw [Finset.prod_mul_distrib] at h1
  have h2 := (ENNReal.mul_left_inj hB0 hBt).1 h1
  rw [← h2, ENNReal.ofReal_prod_of_nonneg fun j _ => pow_nonneg (ha j) _]
  exact Finset.prod_congr rfl fun j _ => by rw [abs_of_nonneg (pow_nonneg (ha j) _)]

/-- The uniform distribution on a product of sets is the product of the uniform distributions. -/
theorem unifSet_pi {F : (j : Fin J) → Set (V j)} (h0 : ∀ j, volume (F j) ≠ 0)
    (ht : ∀ j, volume (F j) ≠ ∞) :
    unifSet (univ.pi F) = Measure.pi fun j => unifSet (F j) := by
  have := fun j => isProbabilityMeasure_unifSet (h0 j) (ht j)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [unifSet, smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← pi_inter_distrib, volume_pi_pi, volume_pi_pi, smul_eq_mul]
  rw [Finset.prod_congr rfl fun j _ => show unifSet (F j) (s j) =
    (volume (F j))⁻¹ * volume (s j ∩ F j) by
      rw [unifSet, smul_apply, Measure.restrict_apply (hs j), smul_eq_mul]]
  rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib fun i _ j _ _ => Or.inl (h0 i)]

/-- The level density of Theorem 75, `∏_j r_j ^ (dim F_j)` (unnormalised). -/
def prodDens (r : Fin J → ℝ → ℝ) (k : Fin J → ℕ) (s : ℝ) : ℝ := ∏ j, r j s ^ k j

set_option maxHeartbeats 800000 in
/-- **Theorem 75** (`g:thm:prod`). Let `F_j ⊆ V_j`, `j < J` (`J ≥ 1`), be compact with nonempty
interior (dimension `k_j = dim V_j`) and centroid `0`, with the scaling property with constant
`m_j ≥ 0`. Let `r_j` be continuous and concave on `[0, 1]`, `≥ 0` there and `> 0` on `(0, 1)`,
let `c(s) = c₀ + s c₁`, and let
`K = {(s, c(s) + (r_1(s) y_1, …, r_J(s) y_J)) : 0 ≤ s ≤ 1, y_j ∈ F_j}` (the level is written
first). Let `ν` be the level law, with density proportional to `∏_j r_j ^ k_j`, and `s̄` its mean.
Assume (Theorem 73 (b) for `ν`, with `β* = sup β(U)`) that `ν` has the scaling property with
constant `β*`. If `M_j ≥ r_j` on `[0, 1]`, `ℓ_j(s̄) ≥ 0` for the chord `ℓ_j` of `r_j`,
`β* ≤ m_K` and `m_j M_j ≤ m_K ℓ_j(s̄)` for every `j`, then `U(K)` has the scaling property with
constant `m_K`, with the joint mix of `scalingProperty_sliceLaw` and `exists_prodFibreMixer`. -/
theorem thm75 {F : (j : Fin J) → Set (V j)} (hF : ∀ j, IsCompact (F j))
    (hFi : ∀ j, (interior (F j)).Nonempty) (hcen : ∀ j, ∫ y, y ∂(unifSet (F j)) = 0)
    {m : Fin J → ℝ} (hm0 : ∀ j, 0 ≤ m j) (hmF : ∀ j, ScalingProperty (unifSet (F j)) (m j))
    {r : Fin J → ℝ → ℝ} (hr : ∀ j, Continuous (r j)) (hrc : ∀ j, ConcaveOn ℝ (Icc 0 1) (r j))
    (hr0 : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r j s) (hrpos : ∀ j, ∀ s ∈ Ioo (0:ℝ) 1, 0 < r j s)
    (c₀ c₁ : (j : Fin J) → V j) {βstar mK sbar : ℝ}
    (hlev : ScalingProperty (levLaw (prodDens r fun j => finrank ℝ (V j))) βstar)
    (hsbar : sbar = ∫ s, s ∂(levLaw (prodDens r fun j => finrank ℝ (V j))))
    (hβ : βstar ≤ mK) {M : Fin J → ℝ} (hM : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, r j s ≤ M j)
    (hl : ∀ j, 0 ≤ (1 - sbar) * r j 0 + sbar * r j 1)
    (hmK : ∀ j, m j * M j ≤ mK * ((1 - sbar) * r j 0 + sbar * r j 1)) :
    ScalingProperty (unifSet (bodyL (diagMap r) (fun s => c₀ + s • c₁) (univ.pi F))) mK := by
  set ρ := prodDens r fun j => finrank ℝ (V j) with hρdef
  have hρ : Continuous ρ := continuous_finsetProd _ fun j _ => (hr j).pow _
  have hρpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s := fun s hs =>
    Finset.prod_pos fun j _ => pow_pos (hrpos j s hs) _
  have hF0 : ∀ j, volume (F j) ≠ 0 := fun j =>
    (Measure.measure_pos_of_nonempty_interior _ (hFi j)).ne'
  have hFt : ∀ j, volume (F j) ≠ ∞ := fun j => (hF j).measure_lt_top.ne
  have := fun j => isProbabilityMeasure_unifSet (hF0 j) (hFt j)
  have := isProbabilityMeasure_levLaw hρ hρpos
  have hPi : IsCompact (univ.pi F) := isCompact_univ_pi hF
  have hPii : (interior (univ.pi F)).Nonempty := by
    rw [interior_pi_set finite_univ]
    exact univ_pi_nonempty_iff.2 hFi
  rw [unifSet_bodyL_eq (D := diagMap r) (continuous_diagMap hr) (by fun_prop) hPi hPii hρ hρpos
    (fun s hs T => volume_image_diag (fun j => r j s) (fun j => hr0 j s hs) T),
    unifSet_pi hF0 hFt]
  have hPprob : IsProbabilityMeasure (Measure.pi fun j => unifSet (F j)) := inferInstance
  have hlev' := scalingProperty_mono hlev hβ
  have hDm := measurable_diagMap (V := V) fun j => (hr j).measurable
  refine scalingProperty_sliceLaw (μY := Measure.pi fun j => unifSet (F j)) (levLaw_ae_mem ρ)
    hDm c₀ c₁ hlev' fun n hn => ?_
  obtain ⟨Ψ, hΨ, hmix⟩ := exists_prodFibreMixer (μ := fun j => unifSet (F j))
    (fun j => Homothetic.integrable_unifSet (hF j) (hF0 j)) hcen hmF hn
    (r := r) fun j => (hr j).measurable
  refine ⟨Ψ, hΨ, fun lam S hlam hne hscale hS01 hS => hmix lam S
    (fun j i => mul_nonneg (hlam i) (hr0 j _ (hS01 i))) fun j k => ?_⟩
  rw [← hsbar] at hS
  exact Scaled.thm75_fibre (hrc j) (hM j) (hm0 j) (hmK j) (hl j) lam S hlam hS01 hS hscale k

end Thm75

/-! ### Corollary 77: the convex hull of two products of scaled copies -/

section Cor77

open Module Scaled

variable {J : ℕ} [NeZero J] {V : Fin J → Type*} [∀ j, NormedAddCommGroup (V j)]
  [∀ j, NormedSpace ℝ (V j)] [∀ j, FiniteDimensional ℝ (V j)] [∀ j, MeasureSpace (V j)]
  [∀ j, BorelSpace (V j)] [∀ j, (volume : Measure (V j)).IsAddHaarMeasure]

lemma levLaw_eq (ρ : ℝ → ℝ) : levLaw ρ = Homothetic.levelDist 0 1 ρ 1 := by
  have e : Homothetic.levelDens ρ 1 = fun s => ENNReal.ofReal (ρ s) := by
    funext s; simp [Homothetic.levelDens]
  simp only [levLaw, Homothetic.levelDist, levNorm, Homothetic.levelNorm, e]

/-- The mean of the level law is `meanOn 0 1 ρ`. -/
lemma levLaw_mean {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ ρ s)
    (hpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s) : ∫ s, s ∂levLaw ρ = meanOn 0 1 ρ := by
  have h0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ ρ s := hρ0
  rw [levLaw_eq, Homothetic.levelDist_mean zero_lt_one hρ h0 hpos]
  simp

/-- The hull of Corollary 77, `conv((C₀ × {0}) ∪ (C₁ × {1}))` with `C₀ = ∏ a_j F_j` and
`C₁ = t + ∏ b_j F_j`, written with the level first. -/
def hullC (F : (j : Fin J) → Set (V j)) (a b : Fin J → ℝ) (t : (j : Fin J) → V j) :
    Set (ℝ × ((j : Fin J) → V j)) :=
  convexHull ℝ (({(0:ℝ)} ×ˢ univ.pi (fun j => a j • F j)) ∪
    ({(1:ℝ)} ×ˢ ((fun y => t + y) '' univ.pi (fun j => b j • F j))))

/-- The sections of the hull (first step of the proof of Corollary 77): for convex `F_j`,
`(1 - s) a_j F_j + s b_j F_j = r_j(s) F_j`, so the hull is the body with the affine profiles
`r_j(s) = (1 - s) a_j + s b_j` and the position `s t`. -/
theorem hullC_eq {F : (j : Fin J) → Set (V j)} (hFc : ∀ j, Convex ℝ (F j))
    (hFne : ∀ j, (F j).Nonempty) {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (t : (j : Fin J) → V j) :
    hullC F a b t = bodyL (diagMap (prof a b)) (fun s => s • t) (univ.pi F) := by
  set A0 : Set (ℝ × ((j : Fin J) → V j)) := {(0:ℝ)} ×ˢ univ.pi (fun j => a j • F j)
  set A1 : Set (ℝ × ((j : Fin J) → V j)) :=
    {(1:ℝ)} ×ˢ ((fun y => t + y) '' univ.pi (fun j => b j • F j))
  have hA0c : Convex ℝ A0 :=
    (convex_singleton _).prod (convex_pi fun j _ => (hFc j).smul (a j))
  have hA1c : Convex ℝ A1 :=
    (convex_singleton _).prod ((convex_pi fun j _ => (hFc j).smul (b j)).translate t)
  choose f hf using hFne
  have hA0n : A0.Nonempty := ⟨(0, fun j => a j • f j), rfl, fun j _ => smul_mem_smul_set (hf j)⟩
  have hA1n : A1.Nonempty := ⟨(1, t + fun j => b j • f j), rfl,
    ⟨fun j => b j • f j, fun j _ => smul_mem_smul_set (hf j), rfl⟩⟩
  have hsum : ∀ j (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      ((1 - θ) * a j) • F j + (θ * b j) • F j = prof a b j θ • F j := by
    intro j θ h0 h1
    rw [← (hFc j).add_smul (mul_nonneg (by linarith) (ha j)) (mul_nonneg h0 (hb j))]
    rfl
  unfold hullC
  rw [convexHull_union hA0n hA1n, hA0c.convexHull_eq, hA1c.convexHull_eq]
  ext x
  rw [mem_convexJoin]
  constructor
  · rintro ⟨p, ⟨hp1, hp2⟩, q, ⟨hq1, y1, hy1, hq2⟩, hx⟩
    rw [segment_eq_image] at hx
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
    have hmem : ∀ j, (1 - θ) • p.2 j + θ • y1 j ∈ prof a b j θ • F j := by
      intro j
      rw [← hsum j θ h0 h1, mul_smul, mul_smul]
      exact add_mem_add (smul_mem_smul_set (hp2 j (mem_univ _)))
        (smul_mem_smul_set (hy1 j (mem_univ _)))
    choose y hy hyeq using fun j => Set.mem_smul_set.1 (hmem j)
    refine ⟨(θ, y), ⟨⟨h0, h1⟩, fun j _ => hy j⟩, ?_⟩
    simp only [mem_singleton_iff] at hp1 hq1
    refine Prod.ext ?_ (funext fun j => ?_)
    · simp [secL, hp1, hq1]
    · simp only [secL, diagMap, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
        hyeq j, ← hq2]
      rw [smul_add]
      abel
  · rintro ⟨⟨θ, y⟩, ⟨⟨h0, h1⟩, hy⟩, rfl⟩
    have hmem : ∀ j, prof a b j θ • y j ∈ ((1 - θ) * a j) • F j + (θ * b j) • F j := by
      intro j; rw [hsum j θ h0 h1]; exact smul_mem_smul_set (hy j (mem_univ _))
    choose u hu v hv huv using fun j => Set.mem_add.1 (hmem j)
    choose u' hu' hu'eq using fun j => Set.mem_smul_set.1 (hu j)
    choose v' hv' hv'eq using fun j => Set.mem_smul_set.1 (hv j)
    refine ⟨(0, fun j => a j • u' j), ⟨rfl, fun j _ => smul_mem_smul_set (hu' j)⟩,
      (1, t + fun j => b j • v' j), ⟨rfl, fun j => b j • v' j,
        fun j _ => smul_mem_smul_set (hv' j), rfl⟩, ?_⟩
    rw [segment_eq_image]
    refine ⟨θ, ⟨h0, h1⟩, ?_⟩
    refine Prod.ext ?_ (funext fun j => ?_)
    · simp [secL]
    · simp only [secL, diagMap, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
        smul_add, ← huv j, ← hu'eq j, ← hv'eq j, mul_smul]
      abel

/-- Recentring the factors: with `g_j` the centroid of `F_j`, the body with sets `F_j` and
position `s t` is the body with the centred sets `F_j - g_j` and the affine position
`c(s) = s t + (r_j(s) g_j)_j`. -/
lemma bodyL_recentre (F : (j : Fin J) → Set (V j)) (a b : Fin J → ℝ) (t g : (j : Fin J) → V j) :
    bodyL (diagMap (prof a b)) (fun s => s • t) (univ.pi F) =
      bodyL (diagMap (prof a b))
        (fun s => (fun j => a j • g j) + s • (t + fun j => (b j - a j) • g j))
        (univ.pi fun j => (fun y => y + -g j) '' F j) := by
  ext x
  simp only [bodyL, mem_image, mem_prod, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
    refine ⟨(s, fun j => y j + -g j), ⟨hs, fun j => ⟨y j, hy j, rfl⟩⟩, ?_⟩
    refine Prod.ext rfl (funext fun j => ?_)
    simp only [secL, diagMap, prof, Pi.add_apply, Pi.smul_apply]
    module
  · rintro ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
    choose z hz hzeq using hy
    refine ⟨(s, z), ⟨hs, hz⟩, ?_⟩
    refine Prod.ext rfl (funext fun j => ?_)
    simp only [secL, diagMap, prof, Pi.add_apply, Pi.smul_apply]
    have h := hzeq j
    simp only at h
    rw [← h]
    module

lemma concaveOn_prof (a b : Fin J → ℝ) (j : Fin J) : ConcaveOn ℝ (Icc 0 1) (prof a b j) := by
  refine ⟨convex_Icc 0 1, fun x _ y _ u v _ _ huv => le_of_eq ?_⟩
  have : v = 1 - u := by linarith
  subst this
  simp only [prof, smul_eq_mul]
  ring

/-- **Corollary 77** (`g:cor:cayley`), measure level. Let `F_j ⊆ V_j` (`j < J`, `J ≥ 1`) be
compact convex with nonempty interior (dimension `k_j = dim V_j`) and the scaling property with a
constant `0 ≤ m_j ≤ k_j + 1`, let `a, b ≥ 0` with `a_j + b_j > 0`, and `t ∈ ∏ V_j`. Assume
(Theorem 73 (b) with `β* ≤ d + 1`, Theorem 75) that the level law, with density
`∏_j r_j ^ k_j`, `r_j(s) = (1 - s) a_j + s b_j`, has the scaling property with constant `d + 1`,
`d = 1 + ∑ k_j`. Then the hull `C = conv((C₀ × {0}) ∪ (C₁ × {1}))` (level written first) has the
scaling property with constant `d + 1`. -/
theorem cor77 {F : (j : Fin J) → Set (V j)} (hF : ∀ j, IsCompact (F j))
    (hFc : ∀ j, Convex ℝ (F j)) (hFi : ∀ j, (interior (F j)).Nonempty) {m : Fin J → ℝ}
    (hm0 : ∀ j, 0 ≤ m j) (hmk : ∀ j, m j ≤ finrank ℝ (V j) + 1)
    (hmF : ∀ j, ScalingProperty (unifSet (F j)) (m j)) {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j) (t : (j : Fin J) → V j)
    (hlev : ScalingProperty (levLaw (prodDens (prof a b) fun j => finrank ℝ (V j)))
      ((∑ j, (finrank ℝ (V j) : ℝ)) + 2)) :
    ScalingProperty (unifSet (hullC F a b t)) ((∑ j, (finrank ℝ (V j) : ℝ)) + 2) := by
  set k : Fin J → ℕ := fun j => finrank ℝ (V j) with hkdef
  set g : (j : Fin J) → V j := fun j => ∫ y, y ∂(unifSet (F j)) with hgdef
  have hF0 : ∀ j, volume (F j) ≠ 0 := fun j =>
    (Measure.measure_pos_of_nonempty_interior _ (hFi j)).ne'
  have hFt : ∀ j, volume (F j) ≠ ∞ := fun j => (hF j).measure_lt_top.ne
  have hP := fun j => isProbabilityMeasure_unifSet (hF0 j) (hFt j)
  have hU : ∀ j, unifSet ((fun y => y + -g j) '' F j) =
      (unifSet (F j)).map (fun y => y + -g j) := by
    intro j
    have := unifSet_map_affine (F j) (M := LinearMap.id) (by simp) (-g j)
    simp only [LinearMap.id_apply] at this
    exact this.symm
  have hmF' : ∀ j, ScalingProperty (unifSet ((fun y => y + -g j) '' F j)) (m j) := by
    intro j
    rw [hU]
    have := scalingProperty_map_affine (hmF j) (ContinuousLinearMap.id ℝ (V j)) (-g j)
    simpa only [ContinuousLinearMap.id_apply] using this
  have hcen' : ∀ j, ∫ y, y ∂(unifSet ((fun y => y + -g j) '' F j)) = 0 := by
    intro j
    rw [hU, integral_map (f := fun y : V j => y) (measurable_add_const _).aemeasurable
      (aestronglyMeasurable_id (μ := (unifSet (F j)).map fun y => y + -g j)),
      integral_add (f := fun x : V j => x) (g := fun _ => -g j)
        (Homothetic.integrable_unifSet (hF j) (hF0 j)) (integrable_const _),
      integral_const]
    simp [hgdef]
  have hF'c : ∀ j, IsCompact ((fun y => y + -g j) '' F j) := fun j =>
    (hF j).image (continuous_id.add continuous_const)
  have hF'i : ∀ j, (interior ((fun y => y + -g j) '' F j)).Nonempty := by
    intro j
    have := (Homeomorph.addRight (-g j)).image_interior (F j)
    simp only [Homeomorph.coe_addRight] at this
    rw [← this]
    exact (hFi j).image _
  have hne : ∀ j, (F j).Nonempty := fun j => (hFi j).mono interior_subset
  rw [hullC_eq hFc hne ha hb, bodyL_recentre F a b t g]
  have hρ : Continuous (profDens k a b) := continuous_profDens k a b
  have hρ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ profDens k a b s := fun s hs =>
    Finset.prod_nonneg fun j _ => pow_nonneg (prof_nonneg ha hb j hs) _
  have hρpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < profDens k a b s := fun s hs =>
    Finset.prod_pos fun j _ => pow_pos (prof_pos ha hb hab j hs) _
  have hmean := levLaw_mean hρ hρ0 hρpos
  obtain ⟨hpos, -, -⟩ := cor77_mK (k := k) ha hb hab m (fun j => hmk j) 0 (by positivity)
  have hchord : ∀ j, (1 - meanOn 0 1 (profDens k a b)) * prof a b j 0 +
      meanOn 0 1 (profDens k a b) * prof a b j 1 = prof a b j (meanOn 0 1 (profDens k a b)) := by
    intro j; simp only [prof]; ring
  refine thm75 hF'c hF'i hcen' hm0 hmF' (r := prof a b) (fun j => by unfold prof; fun_prop)
    (concaveOn_prof a b) (fun j s hs => prof_nonneg ha hb j hs)
    (fun j s hs => prof_pos ha hb hab j hs) _ _ hlev hmean.symm le_rfl
    (M := fun j => max (a j) (b j)) (fun j s hs => ?_) (fun j => ?_) (fun j => ?_)
  · simp only [prof]
    nlinarith [hs.1, hs.2, le_max_left (a j) (b j), le_max_right (a j) (b j)]
  · rw [hchord]; exact (hpos j).le
  · rw [hchord]
    have h1 := cor77_ratio (k := k) ha hb hab j
    have hmax : 0 ≤ max (a j) (b j) := le_max_of_le_left (ha j)
    calc m j * max (a j) (b j) ≤ ((k j : ℝ) + 1) * max (a j) (b j) :=
          mul_le_mul_of_nonneg_right (hmk j) hmax
      _ ≤ _ := h1

end Cor77

/-! ### Definition 78 and Theorem 79: the class `𝒦⁺` -/

section ClassKPlus

open Module

/-- A finite-dimensional real normed space with an additive Haar measure as `volume` (a model of
some `ℝ^k`); the ambient spaces of the members of `𝒦⁺`. -/
structure Sp where
  /-- The underlying type. -/
  carrier : Type
  [ng : NormedAddCommGroup carrier]
  [ns : NormedSpace ℝ carrier]
  [fd : FiniteDimensional ℝ carrier]
  [ms : MeasureSpace carrier]
  [bs : BorelSpace carrier]
  [haar : (volume : Measure carrier).IsAddHaarMeasure]

attribute [instance] Sp.ng Sp.ns Sp.fd Sp.ms Sp.bs Sp.haar

/-- The product of two spaces. -/
abbrev Sp.prod (X Y : Sp) : Sp where
  carrier := X.carrier × Y.carrier
  haar := by rw [Measure.volume_eq_prod]; infer_instance

/-- The space `ℝ × ∏_j X_j` of the hulls of Corollary 77 (level first). -/
abbrev Sp.hull {J : ℕ} (X : Fin J → Sp) : Sp where
  carrier := ℝ × ((j : Fin J) → (X j).carrier)
  haar := by rw [Measure.volume_eq_prod]; infer_instance

/-- Euclidean space `ℝ^j`. -/
abbrev Sp.euc (j : ℕ) : Sp := ⟨EuclideanSpace ℝ (Fin j)⟩

/-- **Definition 78** (`g:def:class`). `KPlus X μ d`: `μ` is the uniform distribution of a member
of `𝒦⁺` of dimension `d` in the space `X`. Members of lower dimension than their ambient space
(points, affine images) are represented by their uniform distributions on their affine hulls,
pushed forward. The class is generated by points, closed balls of every dimension `j ≥ 1`,
images under injective affine maps, Cartesian products, and the hulls of Corollary 77 of compact
convex full-dimensional members `F_j ⊆ X_j` (`J ≥ 1`, `dim F_j ≥ 1`). -/
inductive KPlus : (X : Sp) → Measure X.carrier → ℕ → Prop
  | point (X : Sp) : KPlus X (Measure.dirac 0) 0
  | ball (j : ℕ) (hj : 1 ≤ j) :
      KPlus (Sp.euc j) (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) j
  | affine {X Y : Sp} {μ : Measure X.carrier} {d : ℕ} (h : KPlus X μ d)
      (M : X.carrier →L[ℝ] Y.carrier) (hM : Function.Injective M) (b : Y.carrier) :
      KPlus Y (μ.map fun x => M x + b) d
  | prod {X Y : Sp} {μ : Measure X.carrier} {ν : Measure Y.carrier} {d₁ d₂ : ℕ}
      (h₁ : KPlus X μ d₁) (h₂ : KPlus Y ν d₂) : KPlus (Sp.prod X Y) (μ.prod ν) (d₁ + d₂)
  | hull {J : ℕ} [NeZero J] (X : Fin J → Sp) (F : (j : Fin J) → Set (X j).carrier)
      (hF : ∀ j, IsCompact (F j)) (hFc : ∀ j, Convex ℝ (F j))
      (hFi : ∀ j, (interior (F j)).Nonempty)
      (hK : ∀ j, KPlus (X j) (unifSet (F j)) (finrank ℝ (X j).carrier))
      (hk : ∀ j, 1 ≤ finrank ℝ (X j).carrier) (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j)
      (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j) (t : (j : Fin J) → (X j).carrier) :
      KPlus (Sp.hull X) (unifSet (hullC F a b t)) (1 + ∑ j, finrank ℝ (X j).carrier)

/-- A point has the scaling property with constant `1`. -/
theorem scalingProperty_dirac (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] :
    ScalingProperty (Measure.dirac (0 : E)) 1 := by
  intro n _
  refine ⟨fun p _ => p.2, measurable_snd.comp measurable_fst, fun lam t _ _ _ => ?_⟩
  rw [Measure.map_const, measure_univ, one_smul]
  refine ⟨inferInstance, ⟨∑ i, t i, by rw [ae_dirac_eq]; simp⟩, fun i => ?_⟩
  show (Measure.dirac t).map (fun x => x i) = (Measure.dirac (0 : E)).map _
  rw [Measure.map_dirac' (measurable_pi_apply i), Measure.map_dirac' (by fun_prop)]
  simp

/-- A scaling property with constant `m ≤ n`, `n ≥ 2`, gives `n`-complete mixability. -/
theorem completelyMixable_of_scalingProperty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {μ : Measure E} {m : ℝ} (h : ScalingProperty μ m)
    {n : ℕ} (hn : 2 ≤ n) (hmn : m ≤ n) : CompletelyMixable n μ := by
  obtain ⟨Φ, -, hmix⟩ := h n hn
  have := hmix (fun _ => 1) 0 (fun _ => zero_le_one) ⟨⟨0, by omega⟩, one_ne_zero⟩
    (fun _ => by simpa using hmn)
  simp only [Pi.zero_apply, one_smul, zero_add, Measure.map_id'] at this
  exact ⟨_, this⟩

section Volume

open Module Scaled

variable {J : ℕ} [NeZero J] {V : Fin J → Type*} [∀ j, NormedAddCommGroup (V j)]
  [∀ j, NormedSpace ℝ (V j)] [∀ j, FiniteDimensional ℝ (V j)] [∀ j, MeasureSpace (V j)]
  [∀ j, BorelSpace (V j)] [∀ j, (volume : Measure (V j)).IsAddHaarMeasure]

/-- The hull of Corollary 77 has positive finite volume. -/
lemma volume_hullC {F : (j : Fin J) → Set (V j)} (hF : ∀ j, IsCompact (F j))
    (hFc : ∀ j, Convex ℝ (F j)) (hFi : ∀ j, (interior (F j)).Nonempty) {a b : Fin J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j)
    (t : (j : Fin J) → V j) : volume (hullC F a b t) ≠ 0 ∧ volume (hullC F a b t) ≠ ∞ := by
  have hne : ∀ j, (F j).Nonempty := fun j => (hFi j).mono interior_subset
  rw [hullC_eq hFc hne ha hb]
  set ρ := prodDens (prof a b) fun j => finrank ℝ (V j)
  have hρ : Continuous ρ := continuous_finsetProd _ fun j _ =>
    (show Continuous (prof a b j) by unfold prof; fun_prop).pow _
  have hρpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s := fun s hs =>
    Finset.prod_pos fun j _ => pow_pos (prof_pos ha hb hab j hs) _
  have hPi : IsCompact (univ.pi F) := isCompact_univ_pi hF
  have hP0 : volume (univ.pi F) ≠ 0 := by
    rw [volume_pi_pi]
    exact Finset.prod_ne_zero_iff.2 fun j _ =>
      (Measure.measure_pos_of_nonempty_interior _ (hFi j)).ne'
  have h := volume_inter_bodyL (D := diagMap (prof a b)) (c := fun s => s • t)
    (continuous_diagMap fun j => by unfold prof; fun_prop) (by fun_prop) hPi
    (ρ := ρ) (fun s hs T => volume_image_diag (fun j => prof a b j s)
      (fun j => prof_nonneg ha hb j hs) T) MeasurableSet.univ
  simp only [univ_inter, preimage_univ] at h
  rw [h, lintegral_mul_const _ (show Measurable fun s => ENNReal.ofReal (ρ s) from
    ENNReal.measurable_ofReal.comp hρ.measurable), ← levNorm]
  exact ⟨mul_ne_zero (levNorm_pos hρ hρpos).ne' hP0,
    ENNReal.mul_ne_top (levNorm_lt_top hρ).ne hPi.measure_lt_top.ne⟩

end Volume

/-- **Theorem 79** (`g:thm:class`), the scaling property: every member of `𝒦⁺` of dimension `d`
has the scaling property with constant `d + 1` (and its uniform distribution is a probability
measure). Hypotheses (cited results): `Hball`, the sufficiency in Theorem 51 (a ball of
dimension `j ≥ 1` has the scaling property with constant `2`); `Hlev`, Theorem 73 (b) with the
bound `β ≤ p + 2` of Theorem 67, for the level laws of the hulls (density `∏ r_j ^ k_j` with
affine `r_j`, whose `(∑ k_j)`-th root is concave by `Scaled.concaveOn_prod_rpow`): such a law has
the scaling property with constant `∑ k_j + 2`. -/
theorem thm79
    (Hball : ∀ j : ℕ, 1 ≤ j →
      ScalingProperty (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) 2)
    (Hlev : ∀ (J : ℕ) [NeZero J] (k : Fin J → ℕ) (a b : Fin J → ℝ), (∀ j, 0 ≤ a j) →
      (∀ j, 0 ≤ b j) → (∀ j, 0 < a j + b j) →
      ScalingProperty (levLaw (prodDens (Scaled.prof a b) k)) ((∑ j, (k j : ℝ)) + 2))
    {X : Sp} {μ : Measure X.carrier} {d : ℕ} (h : KPlus X μ d) :
    IsProbabilityMeasure μ ∧ ScalingProperty μ (d + 1) := by
  induction h with
  | point X => exact ⟨inferInstance, by simpa using scalingProperty_dirac X.carrier⟩
  | ball j hj =>
    refine ⟨isProbabilityMeasure_unifSet (Metric.measure_closedBall_pos _ _ one_pos).ne'
      (isCompact_closedBall _ _).measure_lt_top.ne, scalingProperty_mono (Hball j hj) ?_⟩
    have : (1:ℝ) ≤ j := by exact_mod_cast hj
    linarith
  | affine h M hM b ih =>
    obtain ⟨hP, hS⟩ := ih
    exact ⟨inferInstance, scalingProperty_map_affine hS M b⟩
  | @prod X Y μ ν d₁ d₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨hP₁, hS₁⟩ := ih₁
    obtain ⟨hP₂, hS₂⟩ := ih₂
    refine ⟨inferInstance, scalingProperty_mono (scalingProperty_prod hS₁ hS₂) ?_⟩
    push_cast
    exact max_le (by linarith [(Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂)])
      (by linarith [(Nat.cast_nonneg d₁ : (0:ℝ) ≤ d₁)])
  | @hull J _ X F hF hFc hFi hK hk a b ha hb hab t ih =>
    obtain ⟨h0, ht⟩ := volume_hullC hF hFc hFi ha hb hab t
    refine ⟨unifSet_isProb h0 ht, ?_⟩
    have key := cor77 hF hFc hFi (m := fun j => (finrank ℝ (X j).carrier : ℝ) + 1)
      (fun j => by positivity) (fun j => le_rfl) (fun j => (ih j).2) ha hb hab t
      (Hlev J _ a b ha hb hab)
    convert key using 1
    push_cast
    ring

/-- **Theorem 79**, complete mixability: a member of `𝒦⁺` of dimension `d` has an `n`-completely
mixable uniform distribution for every `n ≥ max(2, d + 1)`. -/
theorem thm79_completelyMixable
    (Hball : ∀ j : ℕ, 1 ≤ j →
      ScalingProperty (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) 2)
    (Hlev : ∀ (J : ℕ) [NeZero J] (k : Fin J → ℕ) (a b : Fin J → ℝ), (∀ j, 0 ≤ a j) →
      (∀ j, 0 ≤ b j) → (∀ j, 0 < a j + b j) →
      ScalingProperty (levLaw (prodDens (Scaled.prof a b) k)) ((∑ j, (k j : ℝ)) + 2))
    {X : Sp} {μ : Measure X.carrier} {d : ℕ} (h : KPlus X μ d) {n : ℕ} (hn : 2 ≤ n)
    (hdn : d + 1 ≤ n) : CompletelyMixable n μ :=
  completelyMixable_of_scalingProperty (thm79 Hball Hlev h).2 hn (by exact_mod_cast hdn)

section Join

variable {V : Fin 2 → Type*} [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
  [∀ j, FiniteDimensional ℝ (V j)] [∀ j, MeasureSpace (V j)] [∀ j, BorelSpace (V j)]
  [∀ j, (volume : Measure (V j)).IsAddHaarMeasure]

/-- The join `conv((K₁ × {0} × {0}) ∪ ({0} × K₂ × {1}))` (level first) is the hull of
Corollary 77 with `J = 2`, `a = (1, 0)`, `b = (0, 1)`, `t = 0`. -/
theorem hullC_join (F : (j : Fin 2) → Set (V j)) (hFne : ∀ j, (F j).Nonempty) :
    hullC F ![1, 0] ![0, 1] 0 = convexHull ℝ (({(0:ℝ)} ×ˢ {y | y 0 ∈ F 0 ∧ y 1 = 0}) ∪
      ({(1:ℝ)} ×ˢ {y | y 0 = 0 ∧ y 1 ∈ F 1})) := by
  unfold hullC
  congr 3
  · ext y
    simp only [mem_pi, mem_univ, true_implies, Fin.forall_fin_two, mem_ofPred_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, zero_smul_set (hFne 1),
      Set.mem_zero]
  · ext y
    simp only [zero_add, image_id', mem_pi, mem_univ, true_implies, Fin.forall_fin_two,
      mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
      zero_smul_set (hFne 0), Set.mem_zero]

end Join

/-- **Theorem 79**, closure under joins of any dimensions: the join of two compact convex
members of `𝒦⁺` of dimensions `k₀, k₁ ≥ 1` is a member of `𝒦⁺` of dimension `k₀ + k₁ + 1`. -/
theorem KPlus.join (X : Fin 2 → Sp) (F : (j : Fin 2) → Set (X j).carrier)
    (hF : ∀ j, IsCompact (F j)) (hFc : ∀ j, Convex ℝ (F j))
    (hFi : ∀ j, (interior (F j)).Nonempty)
    (hK : ∀ j, KPlus (X j) (unifSet (F j)) (Module.finrank ℝ (X j).carrier))
    (hk : ∀ j, 1 ≤ Module.finrank ℝ (X j).carrier) :
    KPlus (Sp.hull X) (unifSet (convexHull ℝ (({(0:ℝ)} ×ˢ {y | y 0 ∈ F 0 ∧ y 1 = 0}) ∪
      ({(1:ℝ)} ×ˢ {y | y 0 = 0 ∧ y 1 ∈ F 1}))))
      (1 + ∑ j, Module.finrank ℝ (X j).carrier) := by
  rw [← hullC_join F fun j => (hFi j).mono interior_subset]
  exact KPlus.hull X F hF hFc hFi hK hk _ _ (fun j => by fin_cases j <;> simp)
    (fun j => by fin_cases j <;> simp) (fun j => by fin_cases j <;> simp) 0

end ClassKPlus

/-! ### Theorem 75: `β* ≤ d + 1` -/

section Beta

variable {J : ℕ}

/-- **Theorem 75**, the bound `β* ≤ d + 1`: let `r_j ≥ 0` be continuous and concave on `[0, 1]`
and `k_j` natural numbers with `p = ∑ k_j ≥ 1` (`p = d - 1`), and let `f = ∏ r_j ^ k_j / Z`,
`Z > 0`. If, at a level `U`, the ends `A < μ < B` of the peeling (Theorem 34, as hypotheses:
`[A, B] ⊆ [0, 1]`, `U ≤ f` on `[A, B]`, `U < f(μ)`, and `f - U` has mean `μ` on `[A, B]`), then
`β(U) = (B - A)/min(μ - A, B - μ) ≤ p + 2 = d + 1`. The `p`-th root of `f` is a positive multiple
of the geometric mean `∏ r_j ^ (k_j / p)`, concave by `Scaled.concaveOn_prod_rpow`, and
Theorem 67 (`Bipyramid.beta_le`) applies. -/
theorem thm75_beta (k : Fin J → ℕ) (hk : 1 ≤ ∑ j, k j) {r : Fin J → ℝ → ℝ}
    (hr : ∀ j, ContinuousOn (r j) (Icc 0 1)) (hrc : ∀ j, ConcaveOn ℝ (Icc 0 1) (r j))
    (hr0 : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r j s) {Z : ℝ} (hZ : 0 < Z) {U A B μ : ℝ}
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : B ≤ 1)
    (hfU : ∀ x ∈ Icc A B, U ≤ prodDens r k x / Z) (hμ : μ ∈ Ioo A B)
    (hpos : U < prodDens r k μ / Z)
    (hmean : ∫ x in A..B, (x - μ) * (prodDens r k x / Z - U) = 0) :
    Bipyramid.beta μ A B ≤ (∑ j, (k j : ℝ)) + 2 := by
  set p : ℝ := ∑ j, (k j : ℝ) with hpdef
  have hp1 : 1 ≤ p := by rw [hpdef]; exact_mod_cast hk
  have hp0 : 0 < p := by linarith
  have sub : Icc A B ⊆ Icc 0 1 := Icc_subset_Icc hA hB
  set g : ℝ → ℝ := fun s => Z ^ (-1 / p) * ∏ j, r j s ^ ((k j : ℝ) / p) with hgdef
  have hw1 : ∑ j, (k j : ℝ) / p = 1 := by rw [← Finset.sum_div, ← hpdef, div_self hp0.ne']
  have hgconc : ConcaveOn ℝ (Icc 0 1) g := by
    have := Scaled.concaveOn_prod_rpow (convex_Icc 0 1) Finset.univ (fun j => (k j : ℝ) / p)
      (fun j _ => div_nonneg (Nat.cast_nonneg _) hp0.le) hw1 r (fun j _ => hrc j)
      (fun j _ s hs => hr0 j s hs)
    exact this.smul (Real.rpow_nonneg hZ.le _)
  have hg0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ g s := fun s hs =>
    mul_nonneg (Real.rpow_nonneg hZ.le _)
      (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hr0 j s hs) _)
  have hgp : ∀ s ∈ Icc (0:ℝ) 1, g s ^ p = prodDens r k s / Z := by
    intro s hs
    rw [hgdef, Real.mul_rpow (Real.rpow_nonneg hZ.le _)
      (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hr0 j s hs) _),
      ← Real.rpow_mul hZ.le, div_mul_cancel₀ _ hp0.ne',
      ← Real.finsetProd_rpow _ _ fun j _ => Real.rpow_nonneg (hr0 j s hs) _]
    rw [Finset.prod_congr rfl fun j _ => by
      rw [← Real.rpow_mul (hr0 j s hs), div_mul_cancel₀ _ hp0.ne', Real.rpow_natCast]]
    rw [Real.rpow_neg_one, prodDens, div_eq_mul_inv, mul_comm]
  have hgc : ContinuousOn g (Icc 0 1) := by
    have : ContinuousOn (fun s => ∏ j, r j s ^ ((k j : ℝ) / p)) (Icc 0 1) :=
      continuousOn_finsetProd Finset.univ fun j _ =>
        (hr j).rpow_const fun x _ => Or.inr (div_nonneg (Nat.cast_nonneg _) hp0.le)
    exact continuousOn_const.mul this
  have hμ01 : μ ∈ Icc (0:ℝ) 1 := sub ⟨hμ.1.le, hμ.2.le⟩
  obtain ⟨h1, h2⟩ := Bipyramid.beta_le hp1 hU (hgconc.subset sub (convex_Icc _ _))
    (hgc.mono sub) (fun x hx => hg0 x (sub hx))
    (fun x hx => by rw [hgp x (sub hx)]; exact hfU x hx) hμ (by rw [hgp μ hμ01]; exact hpos)
    (by
      rw [← hmean]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (hμ.1.trans hμ.2).le] at hx
      simp only [hgp x (sub hx)])
  exact Bipyramid.beta_le_of hp0 hμ h1 h2

end Beta

/-! ### Corollary 74 -/

section Cor74

open ProbabilityTheory Scaled Bipyramid

variable {n : ℕ}

/-- **Corollary 74 (a)** (`g:cor:scaled`), sufficiency, on `[0, 1]`. Let `p ≥ 1` and let `F` be
the law of `X` with density `f = g ^ p`, `g ≥ 0` concave and continuous on `[0, 1]`, with mean
`μ`. Cited results as hypotheses: the ends `A(U)`, `B(U)` of the peeling (Theorem 34,
`PeelingProps`), the decomposition of Theorem 35 (`hdecomp`, with `ℓ = μ - A`, `r = B - μ`,
`β = (ℓ + r)/min(ℓ, r)`, levels `U ∼ ω` in `[0, f(μ))`), and Theorem 27 for the scaled pieces
(the kernel `κ`). If `(p + 2) max λ_i ≤ ∑ λ_i`, the construction of Theorem 73 (b) is a joint mix
of the laws of `t_i + λ_i X`, with sum `∑ t_i + μ ∑ λ_i`: Theorem 67 gives `β(U) ≤ p + 2`. -/
theorem cor74a {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (F ω : Measure ℝ) [IsProbabilityMeasure ω] (μ : ℝ) {A B : ℝ → ℝ} (hA : Measurable A)
    (hB : Measurable B) (H34 : PeelingProps (fun x => g x ^ p) μ A B)
    (hω : ∀ᵐ U ∂ω, 0 ≤ U ∧ U < g μ ^ p)
    (hdecomp : ∀ S, MeasurableSet S →
      F S = ∫⁻ U, (pieceP (beta μ (A U) (B U))).map (pieceMap μ (μ - A U) (B U - μ)) S ∂ω)
    (t lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (κ : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel κ]
    (hT27 : ∀ U, (∀ i, beta μ (A U) (B U) * lam i ≤ ∑ j, lam j) →
      IsJointMix (fun i => scaledPiece (beta μ (A U) (B U)) (lam i)) (κ U) ∧
        ∀ᵐ v ∂(κ U), ∑ i, v i = ∑ i, lam i)
    (hcond : ∀ k, (p + 2) * lam k ≤ ∑ i, lam i) :
    IsJointMix (fun i => F.map (fun x => t i + lam i * x))
        (ω.bind fun U => (κ U).map (scaledTuple t lam μ (μ - A U) (B U - μ))) ∧
      ∀ᵐ x ∂(ω.bind fun U => (κ U).map (scaledTuple t lam μ (μ - A U) (B U - μ))),
        ∑ i, x i = ∑ i, t i + μ * ∑ i, lam i := by
  refine thm73b F ω μ (measurable_const.sub hA) (hB.sub measurable_const) hdecomp t lam κ hT27 ?_
  filter_upwards [hω] with U hU
  obtain ⟨hA0, hAμ, hμB, hB1, hfU, hmean⟩ := H34 U hU.1 hU.2
  have sub : Icc (A U) (B U) ⊆ Icc 0 1 := Icc_subset_Icc hA0 hB1
  have hμI : μ ∈ Ioo (A U) (B U) := ⟨hAμ, hμB⟩
  obtain ⟨h1, h2⟩ := beta_le hp hU.1 (hg.subset sub (convex_Icc _ _)) (hgc.mono sub)
    (fun x hx => hg0 x (sub hx)) hfU hμI hU.2 hmean
  have hβ := beta_le_of (by linarith) hμI h1 h2
  intro i
  exact (mul_le_mul_of_nonneg_right hβ (hlam i)).trans (hcond i)

/-- The density `(p + 1)(1 - x)^p` on `[0, 1]`. -/
def sharpLaw (p : ℝ) : Measure ℝ := densityOn01 fun x => (p + 1) * (1 - x) ^ p

lemma sharpLaw_apply {p : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    sharpLaw p S = ∫⁻ x in S ∩ Icc 0 1, ENNReal.ofReal ((p + 1) * (1 - x) ^ p) := by
  rw [sharpLaw, densityOn01, withDensity_apply _ hS, Measure.restrict_restrict hS]

lemma sharpLaw_pos {p : ℝ} (hp : 0 ≤ p) {S : Set ℝ} (hS : MeasurableSet S)
    (hSv : 0 < volume (S ∩ Ico 0 1)) : 0 < sharpLaw p S := by
  rw [sharpLaw_apply hS, setLIntegral_pos_iff
    (f := fun x => ENNReal.ofReal ((p + 1) * (1 - x) ^ p))
    (ENNReal.measurable_ofReal.comp (by fun_prop))]
  refine hSv.trans_le (measure_mono fun x hx => ⟨?_, hx.1, hx.2.1, hx.2.2.le⟩)
  simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith [hx.2.2]) _)

lemma sharpLaw_integral {p : ℝ} (hp : 0 ≤ p) (φ : ℝ → ℝ) :
    ∫ x, φ x ∂sharpLaw p = ∫ x in Icc (0:ℝ) 1, φ x * ((p + 1) * (1 - x) ^ p) := by
  rw [sharpLaw, densityOn01]
  have hm : Measurable fun x : ℝ => ((p + 1) * (1 - x) ^ p).toNNReal := by
    exact (by fun_prop : Measurable fun x : ℝ => (p + 1) * (1 - x) ^ p).real_toNNReal
  rw [show (fun x : ℝ => ENNReal.ofReal ((p + 1) * (1 - x) ^ p)) =
      fun x => (((p + 1) * (1 - x) ^ p).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hm]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith [hx.2]) _)),
    mul_comm]

lemma sharpLaw_integral_one {p : ℝ} (hp : 0 ≤ p) :
    ∫ x in Icc (0:ℝ) 1, (p + 1) * (1 - x) ^ p = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x => x ^ p) 1]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith))]
  simp only [Real.one_rpow, Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  field_simp
  ring

lemma sharpLaw_isProb {p : ℝ} (hp : 0 ≤ p) : IsProbabilityMeasure (sharpLaw p) := by
  constructor
  rw [sharpLaw_apply MeasurableSet.univ, univ_inter,
    ← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun x : ℝ => (p + 1) * (1 - x) ^ p).continuousOn
        |>.integrableOn_compact isCompact_Icc)
      ((ae_restrict_mem measurableSet_Icc).mono fun x hx =>
        mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith [hx.2]) _)),
    sharpLaw_integral_one hp, ENNReal.ofReal_one]

/-- **Corollary 74 (a)**, necessity: for the density `(p + 1)(1 - x)^p` on `[0, 1]` (`p ≥ 0`), if
the laws of `t_i + λ_i X` (`λ_i ≥ 0`) are jointly mixable, then `(p + 2) max λ_i ≤ ∑ λ_i`
(Theorem 73 (a) and the mean `1/(p + 2)`). -/
theorem cor74a_sharp {p : ℝ} (hp : 0 ≤ p) (t lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => (sharpLaw p).map (fun x => t i + lam i * x)) (k : Fin n) :
    (p + 2) * lam k ≤ ∑ i, lam i := by
  have := sharpLaw_isProb hp
  have hsupp : sharpLaw p (Icc 0 1)ᶜ = 0 := by
    rw [sharpLaw_apply measurableSet_Icc.compl, compl_inter_self, Measure.restrict_empty,
      lintegral_zero_measure]
  have hhi : ∀ ε > 0, 0 < sharpLaw p (Ioi (1 - ε)) := by
    intro ε hε
    refine sharpLaw_pos hp measurableSet_Ioi ?_
    have : Ioo (max (1 - ε) 0) 1 ⊆ Ioi (1 - ε) ∩ Ico 0 1 := fun x hx =>
      ⟨(le_max_left _ _).trans_lt hx.1, (le_max_right _ _).trans hx.1.le, hx.2⟩
    refine lt_of_lt_of_le ?_ (measure_mono this)
    rw [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos]
    exact max_lt (by linarith) one_pos
  have h1 := thm73a_core (sharpLaw p) hsupp hhi t lam hlam hmix k
  have hmean : ∫ x, x ∂sharpLaw p = 1 / (p + 2) := by
    rw [sharpLaw_integral hp, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, pconc_sharp hp]
  rw [hmean] at h1
  have hp2 : 0 < p + 2 := by linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hp2] at h1
  linarith

/-- **Corollary 74 (b)** (`g:cor:scaled`). Let `K` be a set in a `d`-dimensional space (`d ≥ 2`,
in the paper a convex body), `u` a linear functional, and `X_i ∼ U(t_i + λ_i K)`. Brunn's
theorem is taken as the hypothesis `hBrunn`: the law of `u(X)`, `X ∼ U(K)`, is the image of a law
`G` on `[0, 1]` with density `g ^ (d - 1)`, `g ≥ 0` concave, under an affine map `y ↦ a + c y`,
`c > 0`. With the cited one-dimensional results for `G` as in `cor74a` (`H27` gives Theorem 27's
kernel for every vector of scales), the laws of `u(X_1), …, u(X_n)` are jointly mixable whenever
`(d + 1) max λ_i ≤ ∑ λ_i`. -/
theorem cor74b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [BorelSpace E] (K : Set E) (d : ℕ) (hd : 2 ≤ d) (u : E →L[ℝ] ℝ)
    {a c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (G ω : Measure ℝ) [IsProbabilityMeasure ω]
    (hBrunn : (unifSet K).map u = G.map (fun y => a + c * y))
    (μ : ℝ) {A B : ℝ → ℝ} (hA : Measurable A) (hB : Measurable B)
    (H34 : PeelingProps (fun x => g x ^ ((d : ℝ) - 1)) μ A B)
    (hω : ∀ᵐ U ∂ω, 0 ≤ U ∧ U < g μ ^ ((d : ℝ) - 1))
    (hdecomp : ∀ S, MeasurableSet S →
      G S = ∫⁻ U, (pieceP (beta μ (A U) (B U))).map (pieceMap μ (μ - A U) (B U - μ)) S ∂ω)
    (H27 : ∀ lam' : Fin n → ℝ, ∃ κ : Kernel ℝ (Fin n → ℝ), IsMarkovKernel κ ∧
      ∀ U, (∀ i, beta μ (A U) (B U) * lam' i ≤ ∑ j, lam' j) →
        IsJointMix (fun i => scaledPiece (beta μ (A U) (B U)) (lam' i)) (κ U) ∧
          ∀ᵐ v ∂(κ U), ∑ i, v i = ∑ i, lam' i)
    (t : Fin n → E) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hcond : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => ((unifSet K).map (fun x => t i + lam i • x)).map u := by
  obtain ⟨κ, hκ, hT27⟩ := H27 (fun i => c * lam i)
  haveI := hκ
  have hp : (1:ℝ) ≤ (d : ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h := (cor74a hp hg hgc hg0 G ω μ hA hB H34 hω hdecomp
    (fun i => u (t i) + lam i * a) (fun i => c * lam i) (fun i => mul_nonneg hc.le (hlam i))
    κ hT27 (fun k => by
      rw [← Finset.mul_sum]
      have := hcond k
      nlinarith)).1
  have hJ : JointlyMixable fun i => G.map (fun x => (u (t i) + lam i * a) + c * lam i * x) :=
    ⟨_, h⟩
  convert hJ using 2 with i
  rw [Measure.map_map u.measurable (by fun_prop)]
  have e : (u ∘ fun x => t i + lam i • x) = (fun z => u (t i) + lam i * z) ∘ u := by
    funext x; simp [map_add, map_smul]
  rw [e, ← Measure.map_map (by fun_prop) u.measurable, hBrunn,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y
  simp only [Function.comp]
  ring

end Cor74

/-! ### Remark 81 and the regular pentagon -/

section Rem81

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [MeasurableSingletonClass E]
  [MeasurableAdd₂ E]

/-- **Remark 81**, first sentence: the set of `n` for which `μ` is `n`-completely mixable is closed
under addition (independent complete mixes side by side). -/
theorem completelyMixable_add_add {μ : Measure E} {n m : ℕ} (hn : CompletelyMixable n μ)
    (hm : CompletelyMixable m μ) : CompletelyMixable (n + m) μ := by
  obtain ⟨P, hPp, ⟨s, hs⟩, hPm⟩ := hn
  obtain ⟨Q, hQp, ⟨s', hs'⟩, hQm⟩ := hm
  haveI := hPp
  haveI := hQp
  have hA : Measurable fun z : (Fin n → E) × (Fin m → E) => Fin.append z.1 z.2 := by
    refine measurable_pi_iff.2 fun k => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.append_left]; exact (measurable_pi_apply i).comp measurable_fst
    · simp only [Fin.append_right]; exact (measurable_pi_apply j).comp measurable_snd
  have hset : MeasurableSet {x : Fin (n + m) → E | ∑ k, x k = s + s'} :=
    (Finset.measurable_sum _ fun k _ => measurable_pi_apply k) (measurableSet_singleton _)
  refine ⟨(P.prod Q).map fun z => Fin.append z.1 z.2, ⟨inferInstance, ⟨s + s', ?_⟩, fun k => ?_⟩⟩
  · rw [ae_map_iff hA.aemeasurable hset]
    have h1 : ∀ᵐ z ∂(P.prod Q), ∑ i, z.1 i = s := Measure.quasiMeasurePreserving_fst.ae hs
    have h2 : ∀ᵐ z ∂(P.prod Q), ∑ j, z.2 j = s' := Measure.quasiMeasurePreserving_snd.ae hs'
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [mem_ofPred_eq, Fin.sum_univ_add, Fin.append_left, Fin.append_right, hz1, hz2]
  · rw [Measure.map_map (measurable_pi_apply k) hA]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · have e : (fun x : Fin (n + m) → E => x (Fin.castAdd m i)) ∘
          (fun z : (Fin n → E) × (Fin m → E) => Fin.append z.1 z.2) =
          (fun x : Fin n → E => x i) ∘ Prod.fst := by
        funext z; simp
      rw [e, ← Measure.map_map (measurable_pi_apply i) measurable_fst, Measure.map_fst_prod,
        measure_univ, one_smul]
      exact hPm i
    · have e : (fun x : Fin (n + m) → E => x (Fin.natAdd n j)) ∘
          (fun z : (Fin n → E) × (Fin m → E) => Fin.append z.1 z.2) =
          (fun x : Fin m → E => x j) ∘ Prod.snd := by
        funext z; simp
      rw [e, ← Measure.map_map (measurable_pi_apply j) measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul]
      exact hQm j

end Rem81

section Rem81b

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Remark 81**, second part: if an affine map `A` with `A^m = id` (`m ≥ 1`) maps `K` onto
itself and its linear part has no eigenvalue `1`, then `U(K)` is `m`-completely mixable, by
`(X, AX, …, A^{m-1}X)` (this is `Mixes.completelyMixable_mul` with `j = 1`). -/
theorem rem81_cyclic (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm0 : m ≠ 0) (hm : (⇑A)^[m] = id)
    (h1 : ∀ v, A.linear v = v → v = 0) {K : Set V} (hK : MeasurableSet K) (hAK : A '' K = K)
    (hK0 : volume K ≠ 0) (hKfin : volume K ≠ ∞) : CompletelyMixable m (unifSet K) := by
  simpa using completelyMixable_mul A hm0 hm h1 hK hAK hK0 hKfin one_ne_zero

/-- **Remark 81**, last sentence: if `U(K)` is `5`-completely mixable (the rotation of order `5`
of the regular pentagon) and `n`-completely mixable for every `n ≥ 6` (Corollary 80 (b)), then it
is `n`-completely mixable for every `n ≥ 5`. -/
theorem rem81_pentagon {K : Set V} (h5 : CompletelyMixable 5 (unifSet K))
    (h6 : ∀ n : ℕ, 6 ≤ n → CompletelyMixable n (unifSet K)) :
    ∀ n : ℕ, 5 ≤ n → CompletelyMixable n (unifSet K) := by
  intro n hn
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h]; exact h5
  · exact h6 n h

end Rem81b

/-- **Corollary 80 (b)**, the pentagon constant: for the regular pentagon with circumradius `1`,
sliced perpendicular to an axis of symmetry from the midpoint of a side (`r(0) = sin(π/5)`,
`r(1) = 0`, `max r = sin(2π/5)`) with the centroid at the level `s̄ = cos(π/5)/(1 + cos(π/5))`,
`2 max r / ℓ(s̄) = 4 cos(π/5)(1 + cos(π/5)) = (5 + 3√5)/2`, which lies in `(5, 6)`. -/
theorem cor80b_pentagon :
    let c := Real.cos (Real.pi / 5)
    let sbar := c / (1 + c)
    let ell := (1 - sbar) * Real.sin (Real.pi / 5) + sbar * 0
    2 * Real.sin (2 * Real.pi / 5) / ell = 4 * c * (1 + c) ∧
      4 * c * (1 + c) = (5 + 3 * Real.sqrt 5) / 2 ∧
      5 < (5 + 3 * Real.sqrt 5) / 2 ∧ (5 + 3 * Real.sqrt 5) / 2 < 6 := by
  intro c sbar ell
  have hc : c = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5p : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hcpos : 0 < c := by rw [hc]; positivity
  have hs : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin2 : Real.sin (2 * Real.pi / 5) = 2 * Real.sin (Real.pi / 5) * c := by
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.sin_two_mul]
  have hell : ell = Real.sin (Real.pi / 5) / (1 + c) := by
    simp only [ell, sbar]; field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hell, hsin2]; field_simp; norm_num
  · rw [hc]; ring_nf; rw [h5]; ring
  · nlinarith
  · nlinarith [sq_nonneg (Real.sqrt 5 - 7 / 3)]

/-! ### Corollary 80 -/

section Cor80

open Module

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

lemma levLaw_mean_nonneg {ρ : ℝ → ℝ} : 0 ≤ ∫ s, s ∂levLaw ρ :=
  integral_nonneg_of_ae ((levLaw_ae_mem ρ).mono fun s hs => hs.1)

/-- **Corollary 80 (a)** (`g:cor:more`), for a non-increasing profile (the paper reflects an
increasing one): in Theorem 75 with `J = 1`, let `r ≥ 0` be continuous, concave and
non-increasing on `[0, 1]`, `> 0` on `(0, 1)`, and let `F ⊆ W` (`dim W = d - 1 ≥ 0`) be compact
with nonempty interior, centroid `0` and the scaling property with a constant `0 ≤ m ≤ (d+1)/2`
(the hypotheses of Corollary 64 (b)). With Theorem 73 (b) for the level law (constant
`β* ≤ d + 1`) as hypothesis, `K` has the scaling property with constant `d + 1`:
`m max r / ℓ(s̄) ≤ 2m ≤ d + 1` since `max r = r(0)`, `ℓ(s̄) ≥ r(0)(1 - s̄)` and `s̄ ≤ 1/2`. -/
theorem cor80a {F : Set W} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ (((finrank ℝ W + 1 : ℕ) : ℝ) + 1) / 2) (hmF : ScalingProperty (unifSet F) m)
    {r : ℝ → ℝ} (hr : Continuous r) (hrc : ConcaveOn ℝ (Icc 0 1) r)
    (hanti : AntitoneOn r (Icc 0 1)) (hr0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r s)
    (hrpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < r s) (c₀ c₁ : Fin 1 → W)
    (hlev : ScalingProperty (levLaw (prodDens (fun _ : Fin 1 => r) fun _ => finrank ℝ W))
      (((finrank ℝ W + 1 : ℕ) : ℝ) + 1)) :
    ScalingProperty (unifSet (bodyL (diagMap (V := fun _ : Fin 1 => W) fun _ => r)
      (fun s => c₀ + s • c₁) (univ.pi fun _ => F))) (((finrank ℝ W + 1 : ℕ) : ℝ) + 1) := by
  set ρ := prodDens (fun _ : Fin 1 => r) fun _ => finrank ℝ W with hρdef
  have hρe : ∀ s, ρ s = r s ^ finrank ℝ W := fun s => by simp [hρdef, prodDens]
  have hρ : Continuous ρ := by
    have : ρ = fun s => r s ^ finrank ℝ W := funext hρe
    rw [this]; fun_prop
  have hρ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ ρ s := fun s hs => by rw [hρe]; exact pow_nonneg (hr0 s hs) _
  have hρpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < ρ s := fun s hs => by
    rw [hρe]; exact pow_pos (hrpos s hs) _
  have hρanti : AntitoneOn ρ (Icc 0 1) := fun x hx y hy hxy => by
    rw [hρe, hρe]; exact pow_le_pow_left₀ (hr0 y hy) (hanti hx hy hxy) _
  have hint : 0 < ∫ x in (0:ℝ)..1, ρ x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hρ.intervalIntegrable _ _)
      (fun x hx => hρpos x hx) zero_lt_one
  have hhalf : ∫ s, s ∂levLaw ρ ≤ 1 / 2 := by
    rw [levLaw_mean hρ hρ0 hρpos]
    have := Homothetic.meanOn_le_mid zero_lt_one hρ hρanti hint
    linarith
  have h0 := levLaw_mean_nonneg (ρ := ρ)
  have hr00 := hr0 0 ⟨le_rfl, zero_le_one⟩
  have hr10 := hr0 1 ⟨zero_le_one, le_rfl⟩
  refine thm75 (J := 1) (fun _ => hF) (fun _ => hFi) (fun _ => hcen) (fun _ => hm0)
    (fun _ => hmF) (fun _ => hr) (fun _ => hrc) (fun _ => hr0) (fun _ => hrpos) c₀ c₁ hlev rfl
    le_rfl (M := fun _ => r 0) (fun _ s hs => hanti ⟨le_rfl, zero_le_one⟩ hs hs.1)
    (fun _ => ?_) (fun _ => ?_)
  · change 0 ≤ (1 - ∫ s, s ∂levLaw ρ) * r 0 + (∫ s, s ∂levLaw ρ) * r 1
    nlinarith
  · change m * r 0 ≤ (((finrank ℝ W + 1 : ℕ) : ℝ) + 1) *
      ((1 - ∫ s, s ∂levLaw ρ) * r 0 + (∫ s, s ∂levLaw ρ) * r 1)
    have hK : 0 ≤ (((finrank ℝ W + 1 : ℕ) : ℝ) + 1) := by positivity
    nlinarith [mul_nonneg (mul_nonneg hK (sub_nonneg.2 hhalf)) hr00,
      mul_nonneg (mul_nonneg hK h0) hr10, mul_nonneg (sub_nonneg.2 hm) hr00]

/-- The centroid of `U[-1, 1]` is `0`. -/
lemma integral_unifSet_Icc : ∫ x, x ∂(unifSet (Icc (-1:ℝ) 1)) = 0 := by
  rw [unifSet, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

/-- **Corollary 80 (b)** (`g:cor:more`), measure level: for the planar body
`K = {(s, c(s) + r(s) y) : 0 ≤ s ≤ 1, -1 ≤ y ≤ 1}` with `r ≥ 0` continuous and concave, `> 0` on
`(0, 1)`, `c` affine and `ℓ(s̄) > 0`, given the scaling property of the segment `[-1, 1]` with
constant `2` (Theorem 51, `d = 1`) and Theorem 73 (b) for the level law (constant `β* ≤ 3`), `K`
has the scaling property with constant `max(3, 2 max r / ℓ(s̄))`, hence `U(K)` is
`n`-completely mixable for every `n ≥ max(3, 2 max r / ℓ(s̄))`. -/
theorem cor80b {r : ℝ → ℝ} (hr : Continuous r) (hrc : ConcaveOn ℝ (Icc 0 1) r)
    (hr0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r s) (hrpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < r s)
    (c₀ c₁ : Fin 1 → ℝ) (Hseg : ScalingProperty (unifSet (Icc (-1:ℝ) 1)) 2)
    (hlev : ScalingProperty (levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)) 3)
    {M : ℝ} (hM : ∀ s ∈ Icc (0:ℝ) 1, r s ≤ M)
    (hl : 0 < (1 - ∫ s, s ∂levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)) * r 0 +
      (∫ s, s ∂levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)) * r 1) :
    let sbar := ∫ s, s ∂levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)
    let K := bodyL (diagMap (V := fun _ : Fin 1 => ℝ) fun _ => r) (fun s => c₀ + s • c₁)
      (univ.pi fun _ => Icc (-1:ℝ) 1)
    ScalingProperty (unifSet K) (max 3 (2 * M / ((1 - sbar) * r 0 + sbar * r 1))) ∧
      ∀ n : ℕ, max 3 (2 * M / ((1 - sbar) * r 0 + sbar * r 1)) ≤ n →
        CompletelyMixable n (unifSet K) := by
  intro sbar K
  have hfin : finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  have hS : ScalingProperty (unifSet K) (max 3 (2 * M / ((1 - sbar) * r 0 + sbar * r 1))) := by
    refine thm75 (J := 1) (V := fun _ : Fin 1 => ℝ) (fun _ => isCompact_Icc)
      (fun _ => by rw [interior_Icc]; exact ⟨0, by norm_num, by norm_num⟩)
      (fun _ => integral_unifSet_Icc) (fun _ => zero_le_two) (fun _ => Hseg) (fun _ => hr)
      (fun _ => hrc) (fun _ => hr0) (fun _ => hrpos) c₀ c₁ (βstar := 3) (sbar := sbar)
      (by simpa [hfin] using hlev) (by simp only [sbar, hfin]) (le_max_left _ _)
      (M := fun _ => M) (fun _ => hM) (fun _ => hl.le) (fun _ => ?_)
    rw [← div_le_iff₀ hl, mul_div_assoc]
    exact le_max_right _ _
  refine ⟨hS, fun n hn => completelyMixable_of_scalingProperty hS ?_ hn⟩
  have : (3:ℝ) ≤ n := (le_max_left _ _).trans hn
  exact_mod_cast (show (2:ℝ) ≤ n by linarith)

end Cor80

end ScaledB

end Mixes
