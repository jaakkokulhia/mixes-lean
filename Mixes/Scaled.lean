import Mixes.Uniform
import Mixes.Pieces
import Mixes.Means

/-!
# Section 20: scaled copies, product sections, flat ends

* Proposition 32, last sentence: `completelyMixable_pieceP`.
* Theorem 73 (`g:thm:scaled`): (a) `thm73a`; (b) `thm73b`, with Theorem 27 (as a Markov kernel of
  joint mixes of the scaled pieces) and Theorem 35 (the decomposition) as hypotheses; the scaled
  pieces: `scaledPiece_eq`, `scaledPiece_cdf_concave`, `scaledPiece_support`, `scaledPiece_mean`.
* Theorem 75 (`g:thm:prod`), one-dimensional parts: `concaveOn_prod_rpow`, `thm75_fibre`.
* Corollary 77 (`g:cor:cayley`): `cor77_ratio`, `cor77_mK` (from Lemma 76, `weighted_mean`).
* Lemma 82 (`g:lem:levels`), analytic part: `lemma82_identity`, `lemma82_alpha_nonneg`,
  `lemma82_integral`, `levels_range`.
* Theorem 83 (`g:thm:bipyr`), one-dimensional parts: `thm83_fibre_max`, `condF_half`,
  `condF_of_crude`, `condF_of_affine`, `condP_of_affine`.
* Corollary 84 (a), (c), (d), (e): `cor84a`, `cor84c`, `cor84d`, `cor84e`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Mixes

namespace Scaled

/-- **Proposition 32, last sentence.** For `n ≥ 3` and `2 ≤ β ≤ n`, `P_β` is `n`-completely
mixable, by a complete mix with sum `n` (Lemmas 1 and 3 applied to the mixture of
Proposition 32). -/
theorem pieceP_completeMix {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n) :
    ∃ Q : Measure (Fin n → ℝ), IsCompleteMix n (pieceP β) Q ∧ ∀ᵐ x ∂Q, ∑ j, x j = (n : ℝ) := by
  obtain ⟨τ₁, τ₂, w, hw0, hw1, -, -, hmix⟩ := pieces_mixture hn hβ hβn
  let wt : Fin 2 → ℝ≥0∞ := ![ENNReal.ofReal w, ENNReal.ofReal (1 - w)]
  let τ : Fin 2 → Admissible n := ![τ₁, τ₂]
  have hwt : ∑ i, wt i = 1 := by
    simp only [Fin.sum_univ_two, wt, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add hw0 (by linarith)]; simp
  obtain ⟨Q, hQ, hs⟩ := completelyMixable_mixtureMarginal' wt hwt τ
  refine ⟨Q, ?_, hs⟩
  have : mixtureMarginal wt τ = pieceP β := by
    rw [← hmix]
    simp [mixtureMarginal, Fin.sum_univ_two, wt, τ]
  rwa [this] at hQ

/-- `P_β` is `n`-completely mixable for `n ≥ 3` and `2 ≤ β ≤ n`. -/
theorem completelyMixable_pieceP {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n) :
    CompletelyMixable n (pieceP β) :=
  let ⟨Q, hQ, _⟩ := pieceP_completeMix hn hβ hβn; ⟨Q, hQ⟩


/-! ### The scaled pieces of Theorem 73 (b) -/

section ScaledPiece

/-- The scaled piece: the law of `λ Y` with `Y ∼ P_β`. -/
def scaledPiece (β lam : ℝ) : Measure ℝ := (pieceP β).map (fun y => lam * y)

/-- The scaled piece is `(1 - 2/β) U[0,0] + (2/β) U[0, λβ]` for `λ ≥ 0`, `β ≥ 2`; in
particular it is `δ₀` for `λ = 0`. -/
theorem scaledPiece_eq {β lam : ℝ} (hβ : 2 ≤ β) (hlam : 0 ≤ lam) :
    scaledPiece β lam =
      ENNReal.ofReal (1 - 2 / β) • unifI 0 0 + ENNReal.ofReal (2 / β) • unifI 0 (lam * β) := by
  have hβ0 : 0 < β := by linarith
  rcases eq_or_lt_of_le hlam with h | h
  · subst h
    have := pieceP_isProb hβ
    simp only [scaledPiece, zero_mul, Measure.map_const, measure_univ, one_smul]
    rw [← add_smul, ← ENNReal.ofReal_add (by rw [sub_nonneg, div_le_one hβ0]; exact hβ)
      (by positivity)]
    simp [unifI]
  · simp only [scaledPiece, pieceP, Measure.map_add _ _ (measurable_const_mul lam)]
    rw [Measure.map_smul, Measure.map_smul, map_unifI_const_mul h, map_unifI_const_mul h,
      mul_zero]
    all_goals exact (measurable_const_mul lam).aemeasurable

lemma scaledPiece_isProb {β lam : ℝ} (hβ : 2 ≤ β) : IsProbabilityMeasure (scaledPiece β lam) := by
  have := pieceP_isProb hβ
  unfold scaledPiece; infer_instance

/-- The scaled piece has an atom `1 - 2/β` at `0` and density `2/(λβ²)` on `[0, λβ]`. -/
lemma scaledPiece_eq' {β lam : ℝ} (hβ : 2 ≤ β) (hlam : 0 < lam) :
    scaledPiece β lam = ENNReal.ofReal (1 - 2 / β) • Measure.dirac 0 +
      ENNReal.ofReal (2 / (lam * β ^ 2)) • volume.restrict (Set.Icc 0 (lam * β)) := by
  have hβ0 : 0 < β := by linarith
  have hb : 0 < lam * β := mul_pos hlam hβ0
  rw [scaledPiece_eq hβ hlam.le]
  simp only [unifI, lt_irrefl, hb, ↓reduceIte, sub_zero, smul_smul]
  congr 2
  rw [← ENNReal.ofReal_inv_of_pos hb, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; field_simp

/-- The distribution function of the scaled piece on `[0, ∞)`:
`min(1, (1 - 2/β) + 2x/(λβ²))`. -/
theorem scaledPiece_cdf {β lam x : ℝ} (hβ : 2 ≤ β) (hlam : 0 < lam) (hx : 0 ≤ x) :
    (scaledPiece β lam (Set.Iic x)).toReal = min 1 ((1 - 2 / β) + 2 * x / (lam * β ^ 2)) := by
  have hβ0 : 0 < β := by linarith
  have hb : 0 < lam * β := mul_pos hlam hβ0
  have h1 : 0 ≤ 1 - 2 / β := by rw [sub_nonneg, div_le_one hβ0]; exact hβ
  have hl2 : 0 < lam * β ^ 2 := mul_pos hlam (pow_pos hβ0 2)
  rw [scaledPiece_eq' hβ hlam]
  have hI : Set.Iic x ∩ Set.Icc 0 (lam * β) = Set.Icc 0 (min x (lam * β)) := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]; tauto
  simp only [add_apply, smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_of_mem (show (0:ℝ) ∈ Set.Iic x from hx), Pi.one_apply, mul_one]
  have hm : 0 ≤ min x (lam * β) := le_min hx hb.le
  have hq : 0 ≤ 2 / (lam * β ^ 2) := div_nonneg zero_le_two hl2.le
  rw [hI, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hq,
    ← ENNReal.ofReal_add h1 (mul_nonneg hq hm), ENNReal.toReal_ofReal (by nlinarith)]
  rcases le_total x (lam * β) with hxb | hxb
  · rw [min_eq_left hxb, min_eq_right]
    · ring
    · have : 2 * x / (lam * β ^ 2) ≤ 2 / β := by
        rw [div_le_div_iff₀ hl2 hβ0]; nlinarith
      linarith
  · rw [min_eq_right hxb, min_eq_left]
    · field_simp; ring
    · have : 2 / β ≤ 2 * x / (lam * β ^ 2) := by
        rw [div_le_div_iff₀ hβ0 hl2]; nlinarith
      linarith

/-- The distribution function of the scaled piece is concave on `[0, ∞)`. -/
theorem scaledPiece_cdf_concave {β lam : ℝ} (hβ : 2 ≤ β) (hlam : 0 < lam) :
    ConcaveOn ℝ (Set.Ici 0) fun x => (scaledPiece β lam (Set.Iic x)).toReal := by
  have hβ0 : 0 < β := by linarith
  have hc : ConcaveOn ℝ (Set.Ici (0:ℝ)) fun x => min 1 ((1 - 2 / β) + 2 * x / (lam * β ^ 2)) := by
    have ha : ConcaveOn ℝ (Set.Ici (0:ℝ)) fun x => (1 - 2 / β) + (2 / (lam * β ^ 2)) • x :=
      (concaveOn_const _ (convex_Ici 0)).add ((concaveOn_id (convex_Ici 0)).smul (by positivity))
    have := (concaveOn_const (1:ℝ) (convex_Ici 0)).inf ha
    refine this.congr fun x _ => ?_
    simp only [Pi.inf_apply, smul_eq_mul]
    rw [show (2 / (lam * β ^ 2)) * x = 2 * x / (lam * β ^ 2) by ring]
  exact hc.congr fun x hx => (scaledPiece_cdf hβ hlam hx).symm

/-- The scaled piece lives on `[0, λβ]`, and `λβ` is its right end: every `x < λβ` has
`F(x) < 1`. -/
theorem scaledPiece_support {β lam : ℝ} (hβ : 2 ≤ β) (hlam : 0 < lam) :
    scaledPiece β lam (Set.Icc 0 (lam * β))ᶜ = 0 ∧
      ∀ x < lam * β, (scaledPiece β lam (Set.Iic x)).toReal < 1 := by
  have hβ0 : 0 < β := by linarith
  have hb : 0 < lam * β := mul_pos hlam hβ0
  constructor
  · rw [scaledPiece_eq' hβ hlam]
    simp [Measure.restrict_apply measurableSet_Icc.compl,
      Measure.dirac_apply' _ measurableSet_Icc.compl, hb.le]
  · intro x hx
    rcases lt_or_ge x 0 with h0 | h0
    · rw [scaledPiece_eq' hβ hlam]
      have : Set.Iic x ∩ Set.Icc 0 (lam * β) = ∅ := by
        ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
          iff_false]; intro h; linarith [h.1, h.2.1]
      simp [Measure.restrict_apply measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic,
        this, not_le.2 h0]
    · rw [scaledPiece_cdf hβ hlam h0]
      refine min_lt_iff.2 (Or.inr ?_)
      have hl2 : 0 < lam * β ^ 2 := mul_pos hlam (pow_pos hβ0 2)
      have : 2 * x / (lam * β ^ 2) < 2 / β := by
        rw [div_lt_div_iff₀ hl2 hβ0]; nlinarith
      linarith

/-- The scaled piece has mean `λ`. -/
theorem scaledPiece_mean {β lam : ℝ} (hβ : 2 ≤ β) :
    ∫ x, x ∂(scaledPiece β lam) = lam := by
  have hβ0 : 0 < β := by linarith
  rw [scaledPiece, integral_map (measurable_const_mul lam).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) _), integral_const_mul,
    pieceP_eq hβ0]
  have i1 : Integrable (fun y : ℝ => y) (volume.restrict (Set.Icc 0 β)) :=
    continuous_id.integrableOn_Icc
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    (i1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hβ0.le,
    integral_id]
  simp only [smul_eq_mul, mul_zero, zero_add,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 / β ^ 2)]
  field_simp; ring

end ScaledPiece

/-! ### Theorem 73 (b): the joint mix of scaled copies -/

section Thm73b

open ProbabilityTheory

variable {n : ℕ}

/-- The affine map of Theorem 35 that carries `P_β` to the normalised piece `π_U / W(U)`:
`y ↦ μ - ℓ + ℓ y` if `ℓ ≤ r`, and `y ↦ μ + r - r y` otherwise. -/
def pieceMap (μ l r : ℝ) (y : ℝ) : ℝ := if l ≤ r then μ - l + l * y else μ + r - r * y

/-- The tuple of Theorem 73 (b) built from `(V_1, …, V_n)` at the level with `ℓ = l`, `r = r`. -/
def scaledTuple (t lam : Fin n → ℝ) (μ l r : ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if l ≤ r then t i + lam i * (μ - l) + l * v i else t i + lam i * (μ + r) - r * v i

lemma measurable_scaledTuple (t lam : Fin n → ℝ) (μ : ℝ) {l r : ℝ → ℝ} (hl : Measurable l)
    (hr : Measurable r) :
    Measurable fun p : ℝ × (Fin n → ℝ) => scaledTuple t lam μ (l p.1) (r p.1) p.2 := by
  have hs : MeasurableSet {p : ℝ × (Fin n → ℝ) | l p.1 ≤ r p.1} :=
    measurableSet_le (hl.comp measurable_fst) (hr.comp measurable_fst)
  refine measurable_pi_iff.2 fun i => ?_
  unfold scaledTuple
  refine Measurable.ite hs ?_ ?_ <;> fun_prop

/-- The sum of the tuple of Theorem 73 (b). -/
lemma sum_scaledTuple (t lam : Fin n → ℝ) (μ l r : ℝ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = ∑ i, lam i) :
    ∑ i, scaledTuple t lam μ l r v i = ∑ i, t i + μ * ∑ i, lam i := by
  unfold scaledTuple
  split_ifs
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hv]; ring
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hv]; ring

/-- The `i`-th coordinate of the tuple is an affine function of `v i`. -/
lemma scaledTuple_coord (t lam : Fin n → ℝ) (μ l r : ℝ) (i : Fin n) :
    (fun v => scaledTuple t lam μ l r v i) =
      (fun x => if l ≤ r then t i + lam i * (μ - l) + l * x else t i + lam i * (μ + r) - r * x) ∘
        (fun v : Fin n → ℝ => v i) := rfl

lemma scaled_coord_map (t lam : Fin n → ℝ) (μ l r β : ℝ) (i : Fin n) :
    (scaledPiece β (lam i)).map
        (fun x => if l ≤ r then t i + lam i * (μ - l) + l * x else t i + lam i * (μ + r) - r * x)
      = ((pieceP β).map (pieceMap μ l r)).map (fun x => t i + lam i * x) := by
  unfold scaledPiece
  rw [Measure.map_map (by split_ifs <;> fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by unfold pieceMap; split_ifs <;> fun_prop)]
  congr 1
  funext y
  simp only [Function.comp, pieceMap]
  split_ifs <;> ring

/-- **Theorem 73 (b)** (`g:thm:scaled`), with Theorem 27 and Theorem 35 as hypotheses.

* `ω` is the law of the level `U` (in the paper `W(U) dU` on `[0, f(μ))`), and `l`, `r`, `β`
  are the measurable functions `ℓ(U)`, `r(U)`, `β(U)`.
* `hdecomp` is the decomposition of Theorem 35, equation `(c:eq:decomp)`: the law `F` of `X` is
  the mixture over `U ∼ ω` of the images of `P_{β(U)}` under `pieceMap μ ℓ(U) r(U)`.
* `κ` is a Markov kernel giving, at every level `U` at which `β(U) max_i λ_i ≤ ∑ λ_i`, a joint
  mix of the scaled pieces `G_i = law of λ_i Y`, `Y ∼ P_{β(U)}`, with sum `∑ λ_i` (Theorem 27,
  `j:thm:main`, for these pieces, together with the measurable dependence on `U`).

If `β(U) max_i λ_i ≤ ∑ λ_i` for `ω`-almost every `U`, then the mixture over `U` of the laws of
`X_i = t_i + λ_i(μ - ℓ) + ℓ V_i` (if `ℓ ≤ r`), resp. `t_i + λ_i(μ + r) - r V_i`, is a joint mix of
the laws `F_i` of `t_i + λ_i X`, with sum `∑ t_i + μ ∑ λ_i`. -/
theorem thm73b (F ω : Measure ℝ) [IsProbabilityMeasure ω] (μ : ℝ) {l r β : ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r)
    (hdecomp : ∀ A, MeasurableSet A →
      F A = ∫⁻ U, (pieceP (β U)).map (pieceMap μ (l U) (r U)) A ∂ω)
    (t lam : Fin n → ℝ) (κ : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel κ]
    (hT27 : ∀ U, (∀ i, β U * lam i ≤ ∑ j, lam j) →
      IsJointMix (fun i => scaledPiece (β U) (lam i)) (κ U) ∧
        ∀ᵐ v ∂(κ U), ∑ i, v i = ∑ i, lam i)
    (hβ : ∀ᵐ U ∂ω, ∀ i, β U * lam i ≤ ∑ j, lam j) :
    IsJointMix (fun i => F.map (fun x => t i + lam i * x))
        (ω.bind fun U => (κ U).map (scaledTuple t lam μ (l U) (r U))) ∧
      ∀ᵐ x ∂(ω.bind fun U => (κ U).map (scaledTuple t lam μ (l U) (r U))),
        ∑ i, x i = ∑ i, t i + μ * ∑ i, lam i := by
  set Φ := fun p : ℝ × (Fin n → ℝ) => scaledTuple t lam μ (l p.1) (r p.1) p.2 with hΦdef
  have hΦ : Measurable Φ := measurable_scaledTuple t lam μ hl hr
  have hΦU : ∀ U, Measurable (scaledTuple t lam μ (l U) (r U)) := fun U =>
    hΦ.comp measurable_prodMk_left
  set K := fun U => (κ U).map (scaledTuple t lam μ (l U) (r U)) with hKdef
  have hKapp : ∀ U s, MeasurableSet s → K U s = κ U (Prod.mk U ⁻¹' (Φ ⁻¹' s)) := by
    intro U s hs
    simp only [hKdef]
    rw [Measure.map_apply (hΦU U) hs]; rfl
  have hK : Measurable K := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [hKapp _ s hs]
    exact Kernel.measurable_kernel_prodMk_left (hΦ hs)
  have hgood := hβ.mono fun U hU => hT27 U hU
  -- the sum
  set c := ∑ i, t i + μ * ∑ i, lam i
  have hsumset : MeasurableSet {x : Fin n → ℝ | ∑ i, x i = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hae : ∀ᵐ x ∂(ω.bind K), ∑ i, x i = c := by
    rw [ae_iff]
    have hc : MeasurableSet {x : Fin n → ℝ | ¬ ∑ i, x i = c} := hsumset.compl
    rw [Measure.bind_apply hc hK.aemeasurable]
    refine (lintegral_congr_ae (hgood.mono fun U hU => ?_)).trans (lintegral_zero)
    rw [hKapp U _ hc]
    refine measure_mono_null (fun v hv => ?_) (ae_iff.1 hU.2)
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦdef] at hv ⊢
    exact fun h => hv (sum_scaledTuple t lam μ _ _ v h)
  refine ⟨⟨⟨?_⟩, ⟨c, hae⟩, fun i => ?_⟩, hae⟩
  · rw [Measure.bind_apply MeasurableSet.univ hK.aemeasurable]
    have : ∀ U, K U Set.univ = 1 := fun U => by
      simp only [hKdef]
      rw [Measure.map_apply (hΦU U) MeasurableSet.univ]; simp
    simp [this]
  · ext A hA
    have hev : Measurable fun x : Fin n → ℝ => x i := measurable_pi_apply i
    have hlin : Measurable fun x : ℝ => t i + lam i * x := by fun_prop
    rw [Measure.map_apply hev hA, Measure.bind_apply (hev hA) hK.aemeasurable,
      Measure.map_apply hlin hA, hdecomp _ (hlin hA)]
    refine lintegral_congr_ae (hgood.mono fun U hU => ?_)
    have hcoord : Measurable (fun x => if l U ≤ r U then t i + lam i * (μ - l U) + l U * x
        else t i + lam i * (μ + r U) - r U * x) := by split_ifs <;> fun_prop
    simp only [hKdef]
    have e : (fun x : Fin n → ℝ => x i) ∘ scaledTuple t lam μ (l U) (r U) =
        (fun v => scaledTuple t lam μ (l U) (r U) v i) := rfl
    rw [← Measure.map_apply hev hA, Measure.map_map hev (hΦU U), e, scaledTuple_coord,
      ← Measure.map_map hcoord hev, hU.1.2.2 i, scaled_coord_map,
      Measure.map_apply hlin hA]

end Thm73b

/-! ### Theorem 73 (a): the necessary condition -/

section Thm73a

variable {n : ℕ}

lemma ae_mem_of_supp {F : Measure ℝ} (hsupp : F (Set.Icc 0 1)ᶜ = 0) :
    ∀ᵐ x ∂F, x ∈ Set.Icc (0:ℝ) 1 := ae_iff.2 hsupp

lemma integrable_affine_of_supp {F : Measure ℝ} [IsProbabilityMeasure F]
    (hsupp : F (Set.Icc 0 1)ᶜ = 0) (a b : ℝ) : Integrable (fun x => a + b * x) F := by
  refine (integrable_const (|a| + |b|)).mono' (by fun_prop) ?_
  filter_upwards [ae_mem_of_supp hsupp] with x hx
  rw [Real.norm_eq_abs]
  calc |a + b * x| ≤ |a| + |b| * |x| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ |a| + |b| * 1 := by
        gcongr; rw [abs_of_nonneg hx.1]; exact hx.2
    _ = |a| + |b| := by ring

/-- The core of Theorem 73 (a): if `F` lives on `[0, 1]`, has mean `μ` and charges every
`(1 - ε, ∞)`, and the laws of `t_i + λ_i X`, `X ∼ F`, `λ_i ≥ 0`, have a joint mix, then
`λ_j ≤ μ ∑ λ_i`. -/
theorem thm73a_core (F : Measure ℝ) [IsProbabilityMeasure F] (hsupp : F (Set.Icc 0 1)ᶜ = 0)
    (hhi : ∀ ε > 0, 0 < F (Set.Ioi (1 - ε))) (t lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => F.map (fun x => t i + lam i * x)) (j : Fin n) :
    lam j ≤ (∫ x, x ∂F) * ∑ i, lam i := by
  obtain ⟨P, hP, ⟨s, hs⟩, hmarg⟩ := hmix
  have hev : ∀ i, Measurable fun x : Fin n → ℝ => x i := fun i => measurable_pi_apply i
  have haff : ∀ i, Measurable fun x : ℝ => t i + lam i * x := fun i => by fun_prop
  set μ := ∫ x, x ∂F
  -- integrability and means of the coordinates
  have hint : ∀ i, Integrable (fun x : Fin n → ℝ => x i) P := by
    intro i
    have h1 : Integrable (fun y : ℝ => y) (P.map fun x => x i) := by
      rw [hmarg i, integrable_map_measure (by fun_prop) (haff i).aemeasurable]
      exact integrable_affine_of_supp hsupp _ _
    exact (integrable_map_measure (by fun_prop) (hev i).aemeasurable).1 h1
  have hmean : ∀ i, ∫ x, x i ∂P = t i + lam i * μ := by
    intro i
    have : ∫ x, x i ∂P = ∫ y, y ∂(P.map fun x => x i) :=
      (integral_map (hev i).aemeasurable aestronglyMeasurable_id).symm
    rw [this, hmarg i, integral_map (haff i).aemeasurable (by fun_prop),
      integral_add (integrable_const _) (integrable_affine_of_supp hsupp 0 (lam i) |>.congr
        (by simp)), integral_const_mul]
    simp [μ]
  have hsval : s = ∑ i, t i + μ * ∑ i, lam i := by
    have h1 : ∫ x, ∑ i, x i ∂P = s := by
      rw [integral_congr_ae hs]; simp
    rw [integral_finsetSum _ fun i _ => hint i] at h1
    simp only [hmean, Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    rw [← h1]; ring
  -- almost surely every coordinate is at least `t_i`
  have hge : ∀ i, ∀ᵐ x ∂P, t i ≤ x i := by
    intro i
    rw [ae_iff]
    have : P {x | ¬ t i ≤ x i} = (P.map fun x => x i) (Set.Iio (t i)) := by
      rw [Measure.map_apply (hev i) measurableSet_Iio]; congr 1; ext x; simp
    rw [this, hmarg i, Measure.map_apply (haff i) measurableSet_Iio]
    refine measure_mono_null (fun x hx => ?_) hsupp
    simp only [Set.mem_preimage, Set.mem_Iio] at hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
    left
    by_contra h; push Not at h; nlinarith [hlam i]
  have hall : ∀ᵐ x ∂P, (∀ i, t i ≤ x i) ∧ ∑ i, x i = s := by
    rw [Filter.eventually_and, ae_all_iff]; exact ⟨hge, hs⟩
  -- the bound
  rcases eq_or_lt_of_le (hlam j) with h0 | hpos
  · rw [← h0]
    have : 0 ≤ μ := integral_nonneg_of_ae (by
      filter_upwards [ae_mem_of_supp hsupp] with x hx; exact hx.1)
    exact mul_nonneg this (Finset.sum_nonneg fun i _ => hlam i)
  by_contra hlt
  push Not at hlt
  set ε := (lam j - μ * ∑ i, lam i) / lam j
  have hε : 0 < ε := div_pos (by linarith) hpos
  have hposP : 0 < P {x | t j + lam j * (1 - ε) < x j} := by
    have : P {x | t j + lam j * (1 - ε) < x j} =
        (P.map fun x => x j) (Set.Ioi (t j + lam j * (1 - ε))) := by
      rw [Measure.map_apply (hev j) measurableSet_Ioi]; rfl
    rw [this, hmarg j, Measure.map_apply (haff j) measurableSet_Ioi]
    refine lt_of_lt_of_le (hhi ε hε) (measure_mono fun x hx => ?_)
    simp only [Set.mem_Ioi, Set.mem_preimage] at hx ⊢
    nlinarith
  obtain ⟨x, hx3, hx1, hx2⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hposP.ne' (ae_restrict_of_ae hall)
  -- `x j - t j ≤ ∑ (x i - t i) = μ ∑ λ`
  have hle : x j - t j ≤ ∑ i, (x i - t i) :=
    Finset.single_le_sum (f := fun i => x i - t i) (fun i _ => by linarith [hx1 i])
      (Finset.mem_univ j)
  rw [Finset.sum_sub_distrib, hx2, hsval] at hle
  simp only [Set.mem_ofPred_eq] at hx3
  have : lam j * (1 - ε) = μ * ∑ i, lam i := by
    simp only [ε]; field_simp; ring
  linarith

/-- **Theorem 73 (a)** (`g:thm:scaled`). Let `F` be a probability measure on `[0, 1]` with mean
`μ` that charges every neighbourhood of `0` and of `1` (as the distribution with density `f`
does, since `f > 0` on `(0, 1)`), let `λ_i ≥ 0`, and suppose the laws of `t_i + λ_i X`, `X ∼ F`,
are jointly mixable. Then `max_i λ_i ≤ min(μ, 1 - μ) ∑ λ_i`. -/
theorem thm73a (F : Measure ℝ) [IsProbabilityMeasure F] (hsupp : F (Set.Icc 0 1)ᶜ = 0)
    (hlo : ∀ ε > 0, 0 < F (Set.Iio ε)) (hhi : ∀ ε > 0, 0 < F (Set.Ioi (1 - ε)))
    (t lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hmix : JointlyMixable fun i => F.map (fun x => t i + lam i * x)) (j : Fin n) :
    lam j ≤ min (∫ x, x ∂F) (1 - ∫ x, x ∂F) * ∑ i, lam i := by
  have h1 := thm73a_core F hsupp hhi t lam hlam hmix j
  -- reflect: `1 - X ∼ F'`, and `-(t_i + λ_i X) = (-t_i - λ_i) + λ_i (1 - X)`
  have hneg : Measurable fun y : ℝ => 1 - y := by fun_prop
  set F' := F.map fun y => 1 - y
  have hsupp' : F' (Set.Icc 0 1)ᶜ = 0 := by
    rw [Measure.map_apply hneg measurableSet_Icc.compl]
    refine measure_mono_null (fun x hx => ?_) hsupp
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx ⊢
    rcases hx with h | h
    · right; linarith
    · left; linarith
  have hhi' : ∀ ε > 0, 0 < F' (Set.Ioi (1 - ε)) := by
    intro ε hε
    rw [Measure.map_apply hneg measurableSet_Ioi]
    refine lt_of_lt_of_le (hlo ε hε) (measure_mono fun x hx => ?_)
    simp only [Set.mem_Iio] at hx; simp only [Set.mem_preimage, Set.mem_Ioi]; linarith
  have hmix' : JointlyMixable fun i => F'.map (fun x => (-t i - lam i) + lam i * x) := by
    obtain ⟨P, hP, ⟨s, hs⟩, hmarg⟩ := hmix
    have hm : Measurable fun x : Fin n → ℝ => -x := measurable_neg
    refine ⟨P.map (fun x => -x), ?_, ⟨-s, ?_⟩, fun i => ?_⟩
    · infer_instance
    · rw [ae_map_iff hm.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
      filter_upwards [hs] with x hx
      simp [Finset.sum_neg_distrib, hx]
    · show (P.map fun x => -x).map (fun x => x i) =
        (F.map fun y => 1 - y).map (fun x => (-t i - lam i) + lam i * x)
      rw [Measure.map_map (measurable_pi_apply i) hm, Measure.map_map (by fun_prop) hneg]
      have e : (fun x : Fin n → ℝ => x i) ∘ (fun x => -x) =
          (fun y : ℝ => -y) ∘ (fun x : Fin n → ℝ => x i) := rfl
      rw [e, ← Measure.map_map (g := fun y : ℝ => -y) (by fun_prop) (measurable_pi_apply i),
        hmarg i, Measure.map_map (g := fun y : ℝ => -y) (by fun_prop) (by fun_prop)]
      congr 1; funext y; simp only [Function.comp]; ring
  have := thm73a_core F' hsupp' hhi' _ lam hlam hmix' j
  have hmean' : ∫ x, x ∂F' = 1 - ∫ x, x ∂F := by
    rw [integral_map hneg.aemeasurable (by fun_prop), integral_sub (integrable_const _)
      (integrable_affine_of_supp hsupp 0 1 |>.congr (by simp))]
    simp
  rw [hmean'] at this
  rcases le_total (∫ x, x ∂F) (1 - ∫ x, x ∂F) with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact this

end Thm73a

/-! ### Theorem 75: the weighted geometric mean of concave functions is concave -/

section GeomMean

variable {ι : Type*}

/-- Superadditivity of the weighted geometric mean on nonnegative vectors. -/
theorem geomMean_superadd (s : Finset ι) (w a b : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i := by
  by_cases hz : ∃ i ∈ s, a i + b i = 0 ∧ w i ≠ 0
  · obtain ⟨i, hi, hc, hwi⟩ := hz
    have hai : a i = 0 := by linarith [ha i hi, hb i hi]
    have hbi : b i = 0 := by linarith [ha i hi, hb i hi]
    rw [Finset.prod_eq_zero hi (by rw [hai, Real.zero_rpow hwi]),
      Finset.prod_eq_zero hi (by rw [hbi, Real.zero_rpow hwi]), add_zero]
    exact Finset.prod_nonneg fun j hj => Real.rpow_nonneg (add_nonneg (ha j hj) (hb j hj)) _
  · push Not at hz
    set c := fun i => a i + b i
    have hc0 : ∀ i ∈ s, 0 ≤ c i := fun i hi => add_nonneg (ha i hi) (hb i hi)
    have hsplit : ∀ x : ι → ℝ, (∀ i ∈ s, 0 ≤ x i) → (∀ i ∈ s, c i = 0 → x i = 0) →
        ∏ i ∈ s, x i ^ w i = (∏ i ∈ s, (x i / c i) ^ w i) * ∏ i ∈ s, c i ^ w i := by
      intro x hx hxc
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      by_cases hci : c i = 0
      · rw [hz i hi hci, Real.rpow_zero, Real.rpow_zero, Real.rpow_zero, mul_one]
      · rw [← Real.mul_rpow (div_nonneg (hx i hi) (hc0 i hi)) (hc0 i hi), div_mul_cancel₀ _ hci]
    have hac : ∀ i ∈ s, c i = 0 → a i = 0 := fun i hi h => by linarith [ha i hi, hb i hi]
    have hbc : ∀ i ∈ s, c i = 0 → b i = 0 := fun i hi h => by linarith [ha i hi, hb i hi]
    rw [hsplit a ha hac, hsplit b hb hbc, ← add_mul]
    set P := ∏ i ∈ s, c i ^ w i
    have hP : 0 ≤ P := Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hc0 i hi) _
    have h1 := Real.geom_mean_le_arith_mean_weighted s w (fun i => a i / c i) hw hw1
      (fun i hi => div_nonneg (ha i hi) (hc0 i hi))
    have h2 := Real.geom_mean_le_arith_mean_weighted s w (fun i => b i / c i) hw hw1
      (fun i hi => div_nonneg (hb i hi) (hc0 i hi))
    have h3 : ∑ i ∈ s, w i * (a i / c i) + ∑ i ∈ s, w i * (b i / c i) ≤ 1 := by
      rw [← Finset.sum_add_distrib, ← hw1]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [← mul_add, ← add_div]
      by_cases hci : c i = 0
      · simp only [c] at hci; rw [hci, zero_div, mul_zero]; exact hw i hi
      · rw [show a i + b i = c i from rfl, div_self hci, mul_one]
    calc ((∏ i ∈ s, (a i / c i) ^ w i) + ∏ i ∈ s, (b i / c i) ^ w i) * P
        ≤ 1 * P := mul_le_mul_of_nonneg_right (by linarith) hP
      _ = P := one_mul P

/-- **The concavity used in Theorem 75**: a weighted geometric mean `∏ f_i^{w_i}`, weights
`w_i ≥ 0` adding up to `1`, of nonnegative concave functions is concave. -/
theorem concaveOn_prod_rpow {S : Set ℝ} (hS : Convex ℝ S) (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ConcaveOn ℝ S (f i)) (hf0 : ∀ i ∈ s, ∀ x ∈ S, 0 ≤ f i x) :
    ConcaveOn ℝ S fun x => ∏ i ∈ s, f i x ^ w i := by
  refine ⟨hS, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ S,
      t * ∏ i ∈ s, f i z ^ w i = ∏ i ∈ s, (t * f i z) ^ w i := by
    intro t ht z hz
    conv_lhs => rw [← Real.rpow_one t, ← hw1, Real.rpow_sum_of_nonneg ht hw]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i hi => (Real.mul_rpow ht (hf0 i hi z hz)).symm
  simp only [smul_eq_mul]
  rw [hhom θ hθ x hx, hhom φ hφ y hy]
  refine (geomMean_superadd s w _ _ hw hw1 (fun i hi => mul_nonneg hθ (hf0 i hi x hx))
    (fun i hi => mul_nonneg hφ (hf0 i hi y hy))).trans ?_
  refine Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg (add_nonneg
    (mul_nonneg hθ (hf0 i hi x hx)) (mul_nonneg hφ (hf0 i hi y hy))) _) fun i hi => ?_
  refine Real.rpow_le_rpow (add_nonneg (mul_nonneg hθ (hf0 i hi x hx))
    (mul_nonneg hφ (hf0 i hi y hy))) ?_ (hw i hi)
  have := (hf i hi).2 hx hy hθ hφ hθφ
  simpa only [smul_eq_mul] using this

end GeomMean

/-! ### Theorem 75: the fibre condition from the chord bound -/

section Fibre

variable {n : ℕ}

/-- A concave function on `[0, 1]` lies above its chord `ℓ(s) = (1 - s) r(0) + s r(1)`. -/
lemma chord_le {r : ℝ → ℝ} (hr : ConcaveOn ℝ (Set.Icc 0 1) r) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    (1 - s) * r 0 + s * r 1 ≤ r s := by
  have := hr.2 (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (1:ℝ) ∈ Set.Icc 0 1 by simp)
    (show 0 ≤ 1 - s by linarith [hs.2]) hs.1 (by ring)
  simpa [smul_eq_mul] using this

/-- An affine function commutes with weighted sums: `∑ λ_i ℓ(S_i) = ℓ(s̄) ∑ λ_i` when
`∑ λ_i S_i = s̄ ∑ λ_i`. -/
lemma sum_affine (lam S : Fin n → ℝ) (sbar p q : ℝ)
    (hS : ∑ i, lam i * S i = sbar * ∑ i, lam i) :
    ∑ i, lam i * (p + q * S i) = (p + q * sbar) * ∑ i, lam i := by
  have : ∑ i, lam i * (p + q * S i) = p * ∑ i, lam i + q * ∑ i, lam i * S i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hS]; ring

/-- **The fibre condition in the proof of Theorem 75.** Let `r` be concave on `[0, 1]` and
bounded by `M` there, `ℓ` its chord, `m ≥ 0`, and let the levels `S_i ∈ [0, 1]` and the scales
`λ_i ≥ 0` satisfy `∑ λ_i S_i = s̄ ∑ λ_i` (the sum of the joint mix of Theorem 73) and
`m_K max_i λ_i ≤ ∑ λ_i`, where `m M ≤ m_K ℓ(s̄)` and `ℓ(s̄) ≥ 0` (definition `(g:eq:mK)` of
`m_K`). Then `m max_i λ_i r(S_i) ≤ ∑ λ_i r(S_i)`, the condition of the scaling property of
`F_j` with constant `m`. -/
theorem thm75_fibre {r : ℝ → ℝ} (hr : ConcaveOn ℝ (Set.Icc 0 1) r) {M m mK sbar : ℝ}
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1, r s ≤ M) (hm : 0 ≤ m)
    (hmK : m * M ≤ mK * ((1 - sbar) * r 0 + sbar * r 1))
    (hl : 0 ≤ (1 - sbar) * r 0 + sbar * r 1)
    (lam S : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hS01 : ∀ i, S i ∈ Set.Icc (0:ℝ) 1)
    (hS : ∑ i, lam i * S i = sbar * ∑ i, lam i) (hscale : ∀ i, mK * lam i ≤ ∑ j, lam j)
    (i : Fin n) :
    m * (lam i * r (S i)) ≤ ∑ k, lam k * r (S k) := by
  set ℓs := (1 - sbar) * r 0 + sbar * r 1
  calc m * (lam i * r (S i)) ≤ m * M * lam i := by
        have := mul_le_mul_of_nonneg_left (hM _ (hS01 i)) (hlam i)
        nlinarith
    _ ≤ mK * ℓs * lam i := mul_le_mul_of_nonneg_right hmK (hlam i)
    _ = ℓs * (mK * lam i) := by ring
    _ ≤ ℓs * ∑ j, lam j := mul_le_mul_of_nonneg_left (hscale i) hl
    _ = ∑ k, lam k * (r 0 + (r 1 - r 0) * S k) := by
        rw [sum_affine lam S sbar _ _ hS]; simp only [ℓs]; ring
    _ ≤ ∑ k, lam k * r (S k) := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (by have := chord_le hr (hS01 k); linarith) (hlam k)

end Fibre

/-! ### Corollary 77: the constant `d + 1` for affine profiles -/

section Cor77

open Set

lemma meanOn_congr {f g : ℝ → ℝ} (h : EqOn f g (Icc 0 1)) : meanOn 0 1 f = meanOn 0 1 g := by
  have h' : EqOn f g (uIcc 0 1) := by rwa [uIcc_of_le zero_le_one]
  unfold meanOn
  rw [intervalIntegral.integral_congr h',
    intervalIntegral.integral_congr (g := fun x => x * g x) fun x hx => by simp only [h' hx]]

lemma meanOn_const_mul {f : ℝ → ℝ} {C : ℝ} (hC : C ≠ 0) :
    meanOn 0 1 (fun s => C * f s) = meanOn 0 1 f := by
  unfold meanOn
  simp_rw [mul_left_comm _ C, intervalIntegral.integral_const_mul]
  by_cases h : ∫ x in (0:ℝ)..1, f x = 0
  · simp [h]
  · field_simp

/-- The reflection `s ↦ 1 - s` maps the mean `s̄` to `1 - s̄`. -/
lemma meanOn_reflect {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∫ x in (0:ℝ)..1, f x ≠ 0) :
    meanOn 0 1 (fun s => f (1 - s)) = 1 - meanOn 0 1 f := by
  unfold meanOn
  have e1 : ∫ x in (0:ℝ)..1, f (1 - x) = ∫ x in (0:ℝ)..1, f x := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => f x) 1]; norm_num
  have e2 : ∫ x in (0:ℝ)..1, x * f (1 - x) = ∫ x in (0:ℝ)..1, (1 - x) * f x := by
    calc ∫ x in (0:ℝ)..1, x * f (1 - x) = ∫ x in (0:ℝ)..1, (fun y => (1 - y) * f y) (1 - x) := by
          congr 1; funext x; simp
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left (fun y => (1 - y) * f y) 1]; norm_num
  have e3 : ∫ x in (0:ℝ)..1, (1 - x) * f x =
      (∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..1, x * f x := by
    have i2 : IntervalIntegrable (fun x => x * f x) volume 0 1 :=
      (continuous_id.mul hf).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) i2]
    congr 1; funext x; ring
  rw [e1, e2, e3]; field_simp

variable {J : ℕ}

/-- The affine profile `r_j(s) = (1 - s) a_j + s b_j`. -/
def prof (a b : Fin J → ℝ) (j : Fin J) (s : ℝ) : ℝ := (1 - s) * a j + s * b j

/-- The density of the level, `∏_j r_j^{k_j}` (unnormalised). -/
def profDens (k : Fin J → ℕ) (a b : Fin J → ℝ) (s : ℝ) : ℝ := ∏ j, prof a b j s ^ k j

lemma prof_nonneg {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (j : Fin J)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : 0 ≤ prof a b j s := by
  unfold prof; nlinarith [hs.1, hs.2, ha j, hb j]

lemma prof_pos {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hab : ∀ j, 0 < a j + b j) (j : Fin J) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    0 < prof a b j s := by
  unfold prof
  rcases eq_or_lt_of_le (ha j) with h | h
  · have : 0 < b j := by linarith [hab j]
    nlinarith [hs.1, hs.2]
  · nlinarith [hs.1, hs.2, hb j]

lemma continuous_profDens (k : Fin J → ℕ) (a b : Fin J → ℝ) : Continuous (profDens k a b) := by
  unfold profDens prof; fun_prop

lemma profDens_integral_pos {k : Fin J → ℕ} {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j) : 0 < ∫ s in (0:ℝ)..1, profDens k a b s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_profDens k a b).intervalIntegrable _ _)
    (fun _ hs => Finset.prod_pos fun j _ => pow_pos (prof_pos ha hb hab j hs) _) zero_lt_one

lemma profDens_reflect (k : Fin J → ℕ) (a b : Fin J → ℝ) (s : ℝ) :
    profDens k a b (1 - s) = profDens k b a s := by
  unfold profDens prof
  refine Finset.prod_congr rfl fun j _ => ?_
  ring_nf

/-- Corollary 77, decreasing profile `r_j` (`b_j < a_j`), from Lemma 76. -/
lemma cor77_decr {k : Fin J → ℕ} {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hab : ∀ j, 0 < a j + b j) (j : Fin J) (hj : b j < a j) :
    ((k j : ℝ) + 1) * a j ≤ ((∑ i, (k i : ℝ)) + 2) * prof a b j (meanOn 0 1 (profDens k a b)) := by
  have haj : 0 < a j := by linarith [hb j]
  set c := 1 - b j / a j with hc
  have hc0 : 0 ≤ c := by rw [hc, sub_nonneg, div_le_one haj]; exact hj.le
  have hc1 : c ≤ 1 := by have := div_nonneg (hb j) haj.le; linarith
  have hprofj : ∀ s, prof a b j s = a j * (1 - c * s) := fun s => by
    simp only [prof, hc]; field_simp; ring
  set γ : ℝ := ∑ i ∈ Finset.univ.erase j, (k i : ℝ) with hγ
  have hγ0 : 0 ≤ γ := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hsum : ∑ i, (k i : ℝ) = k j + γ := by
    rw [hγ, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  set g : ℝ → ℝ := fun s => ∏ i ∈ Finset.univ.erase j, prof a b i s ^ ((k i : ℝ) / γ) with hg
  have hg0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ g s := fun s hs =>
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (prof_nonneg ha hb i hs) _
  have hgpow : ∀ s ∈ Icc (0:ℝ) 1, g s ^ γ = ∏ i ∈ Finset.univ.erase j, prof a b i s ^ k i := by
    intro s hs
    rcases eq_or_lt_of_le hγ0 with h0 | hpos
    · rw [← h0, Real.rpow_zero]
      have hk0 : ∀ i ∈ Finset.univ.erase j, (k i : ℝ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Nat.cast_nonneg _).1 (by rw [← hγ, ← h0])
      refine (Finset.prod_eq_one fun i hi => ?_).symm
      rw [show k i = 0 by exact_mod_cast hk0 i hi, pow_zero]
    · rw [hg, ← Real.finsetProd_rpow _ _ (fun i _ => Real.rpow_nonneg
        (prof_nonneg ha hb i hs) _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_mul (prof_nonneg ha hb i hs), div_mul_cancel₀ _ hpos.ne',
        Real.rpow_natCast]
  have hgconc : ConcaveOn ℝ (Icc 0 1) g := by
    rcases eq_or_lt_of_le hγ0 with h0 | hpos
    · have : g = fun _ => 1 := by
        funext s; simp only [hg, ← h0, div_zero, Real.rpow_zero, Finset.prod_const_one]
      rw [this]; exact concaveOn_const _ (convex_Icc 0 1)
    · refine concaveOn_prod_rpow (convex_Icc 0 1) _ _ (fun i _ => div_nonneg (Nat.cast_nonneg _)
        hpos.le) ?_ (fun i => prof a b i) (fun i _ => ?_) (fun i _ s hs => prof_nonneg ha hb i hs)
      · rw [← Finset.sum_div, ← hγ, div_self hpos.ne']
      · have : prof a b i = fun s => a i + (b i - a i) • s := by
          funext s; simp only [prof, smul_eq_mul]; ring
        rw [this]
        exact (concaveOn_const _ (convex_Icc 0 1)).add
          (LinearMap.concaveOn (LinearMap.lsmul ℝ ℝ (b i - a i)) (convex_Icc 0 1) |>.congr
            fun x _ => by simp; ring)
  have hne : ∃ x ∈ Icc (0:ℝ) 1, g x ≠ 0 := ⟨1 / 2, ⟨by norm_num, by norm_num⟩,
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
      (prof_pos ha hb hab i ⟨by norm_num, by norm_num⟩) _).ne'⟩
  have hmean : meanOn 0 1 (profDens k a b) =
      meanOn 0 1 (fun s => (1 - c * s) ^ (k j : ℝ) * g s ^ γ) := by
    rw [← meanOn_const_mul (f := fun s => (1 - c * s) ^ (k j : ℝ) * g s ^ γ)
      (pow_pos haj (k j)).ne']
    refine meanOn_congr fun s hs => ?_
    simp only [profDens]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), hgpow s hs, hprofj, mul_pow,
      Real.rpow_natCast, mul_assoc]
  have key := weighted_mean (Nat.cast_nonneg (k j)) hγ0 hc0 hc1 hgconc hg0 hne
  rw [← hmean] at key
  rw [hprofj, hsum]
  have h2 : 0 < (k j : ℝ) + γ + 2 := by positivity
  rw [div_le_iff₀ h2] at key
  nlinarith

/-- **Corollary 77, the key inequality** (`g:cor:cayley`): for the affine profiles
`r_j(s) = (1 - s) a_j + s b_j`, `a_j, b_j ≥ 0`, `a_j + b_j > 0`, and the level density `ν`
proportional to `∏ r_j^{k_j}` with mean `s̄`, every `j` has
`r_j(s̄) / max r_j ≥ (k_j + 1)/(d + 1)`, `d = 1 + ∑ k_i`, in multiplied form. -/
theorem cor77_ratio {k : Fin J → ℕ} {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hab : ∀ j, 0 < a j + b j) (j : Fin J) :
    ((k j : ℝ) + 1) * max (a j) (b j) ≤
      ((∑ i, (k i : ℝ)) + 2) * prof a b j (meanOn 0 1 (profDens k a b)) := by
  rcases lt_trichotomy (b j) (a j) with h | h | h
  · rw [max_eq_left h.le]; exact cor77_decr ha hb hab j h
  · -- constant profile
    rw [h, max_self]
    have : prof a b j (meanOn 0 1 (profDens k a b)) = a j := by simp only [prof, h]; ring
    rw [this]
    have : (k j : ℝ) ≤ ∑ i, (k i : ℝ) :=
      Finset.single_le_sum (f := fun i => (k i : ℝ)) (fun i _ => Nat.cast_nonneg _)
        (Finset.mem_univ j)
    nlinarith [ha j]
  · -- increasing profile: reflect `s ↦ 1 - s`
    rw [max_eq_right h.le]
    have hab' : ∀ j, 0 < b j + a j := fun j => by linarith [hab j]
    have key := cor77_decr (k := k) hb ha hab' j h
    have hrefl : meanOn 0 1 (profDens k a b) = 1 - meanOn 0 1 (profDens k b a) := by
      have := meanOn_reflect (continuous_profDens k b a) (profDens_integral_pos hb ha hab').ne'
      rw [← this]
      congr 1; funext s; rw [profDens_reflect]
    rw [hrefl]
    have : prof a b j (1 - meanOn 0 1 (profDens k b a)) =
        prof b a j (meanOn 0 1 (profDens k b a)) := by simp only [prof]; ring
    rw [this]; exact key

/-- **Corollary 77** (`g:cor:cayley`), the bound on the constant `(g:eq:mK)` of Theorem 75: for
affine profiles, if `m_j ≤ k_j + 1` and `β* ≤ d + 1` (Theorem 75, from the bound `β ≤ p + 2` of
Theorem 67, taken as a hypothesis), then
`max(β*, max_j m_j max r_j / ℓ_j(s̄)) ≤ d + 1`, where `ℓ_j = r_j`. -/
theorem cor77_mK {k : Fin J → ℕ} {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hab : ∀ j, 0 < a j + b j) (m : Fin J → ℝ)
    (hm : ∀ j, m j ≤ k j + 1) (βstar : ℝ) (hβ : βstar ≤ (∑ i, (k i : ℝ)) + 2) :
    (∀ j, 0 < prof a b j (meanOn 0 1 (profDens k a b))) ∧
      βstar ≤ (∑ i, (k i : ℝ)) + 2 ∧
      ∀ j, m j * max (a j) (b j) / prof a b j (meanOn 0 1 (profDens k a b)) ≤
        (∑ i, (k i : ℝ)) + 2 := by
  have hpos : ∀ j, 0 < prof a b j (meanOn 0 1 (profDens k a b)) := by
    intro j
    have h1 := cor77_ratio (k := k) ha hb hab j
    have hmax : 0 < max (a j) (b j) := by
      rcases le_total (a j) (b j) with h | h
      · rw [max_eq_right h]; linarith [hab j, ha j]
      · rw [max_eq_left h]; linarith [hab j, hb j]
    have : 0 < ((k j : ℝ) + 1) * max (a j) (b j) := by positivity
    have hS : 0 ≤ (∑ i, (k i : ℝ)) + 2 := by positivity
    by_contra hc; push Not at hc
    nlinarith
  refine ⟨hpos, hβ, fun j => ?_⟩
  rw [div_le_iff₀ (hpos j)]
  have h1 := cor77_ratio (k := k) ha hb hab j
  have hmax : 0 ≤ max (a j) (b j) := le_max_of_le_left (ha j)
  calc m j * max (a j) (b j) ≤ ((k j : ℝ) + 1) * max (a j) (b j) :=
        mul_le_mul_of_nonneg_right (hm j) hmax
    _ ≤ _ := h1

end Cor77

/-! ### Theorem 83: the one-dimensional conditions -/

section Thm83

open Set

variable {r : ℝ → ℝ} {h : ℝ}

/-- Condition `(F_h)` of Theorem 83: `r(c) ≤ r(h) + r(h + c)` for `0 ≤ c ≤ 1 - h`. -/
def CondF (r : ℝ → ℝ) (h : ℝ) : Prop := ∀ c, 0 ≤ c → c ≤ 1 - h → r c ≤ r h + r (h + c)

/-- Condition `(P_h)` of Theorem 83, with the integrability of the integrand (which the paper
uses implicitly; for `h = 1/2` it is the finiteness of the integral). -/
def CondP (r : ℝ → ℝ) (h : ℝ) (k : ℕ) : Prop :=
  IntervalIntegrable (fun a => r a ^ (k - 1) / (2 * h - a)) volume h 1 ∧
    2 * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a) ≤ r h ^ (k - 1)

/-- `(P_h)` for `r` is condition `(g:eq:Ph)` for the normalised `ν = r^{k-1} / Z`, `Z > 0`. -/
theorem condP_iff_nu (k : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    CondP r h k ↔
      IntervalIntegrable (fun a => r a ^ (k - 1) / Z / (2 * h - a)) volume h 1 ∧
        2 * ∫ a in h..1, r a ^ (k - 1) / Z / (2 * h - a) ≤ r h ^ (k - 1) / Z := by
  have e : (fun a => r a ^ (k - 1) / Z / (2 * h - a)) =
      fun a => Z⁻¹ * (r a ^ (k - 1) / (2 * h - a)) := by funext a; field_simp
  rw [e, intervalIntegral.integral_const_mul, CondP]
  constructor
  · rintro ⟨hi, hle⟩
    refine ⟨hi.const_mul _, ?_⟩
    rw [le_div_iff₀ hZ]
    have : 2 * (Z⁻¹ * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a)) * Z =
        2 * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a) := by field_simp
    rw [this]; exact hle
  · rintro ⟨hi, hle⟩
    refine ⟨?_, ?_⟩
    · have := hi.const_mul Z
      refine this.congr ?_
      intro a _; simp only; field_simp
    · rw [le_div_iff₀ hZ] at hle
      have : 2 * (Z⁻¹ * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a)) * Z =
          2 * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a) := by field_simp
      rwa [this] at hle

/-- **The fibre condition of Theorem 83.** Let `r` be non-increasing on `[0, 1]` and satisfy
`(F_h)` for some `h ∈ [1/2, 1)`. For levels `A = B + C` with `0 ≤ C ≤ B ≤ h` and `A ≤ 1` (the
absolute values of the levels of Lemma 82), `r(C) ≤ r(A) + r(B)`. -/
theorem thm83_fibre (hanti : AntitoneOn r (Icc 0 1)) (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hF : CondF r h) {A B C : ℝ} (hC0 : 0 ≤ C) (hCB : C ≤ B) (hBh : B ≤ h) (hA : A = B + C)
    (hA1 : A ≤ 1) : r C ≤ r A + r B := by
  have mem : ∀ x, 0 ≤ x → x ≤ 1 → x ∈ Icc (0:ℝ) 1 := fun x h0 h1 => ⟨h0, h1⟩
  have hB0 : 0 ≤ B := le_trans hC0 hCB
  rcases le_total C (1 - h) with hc | hc
  · have h1 : r h ≤ r B := hanti (mem B hB0 (by linarith)) (mem h (by linarith) hh1.le) hBh
    have h2 : r (h + C) ≤ r A := hanti (mem A (by linarith) hA1)
      (mem (h + C) (by linarith) (by linarith)) (by linarith)
    linarith [hF C hC0 hc]
  · have h1 : r h ≤ r B := hanti (mem B hB0 (by linarith)) (mem h (by linarith) hh1.le) hBh
    have h2 : r 1 ≤ r A := hanti (mem A (by linarith) hA1) (mem 1 zero_le_one le_rfl) hA1
    have h3 : r C ≤ r (1 - h) := hanti (mem (1 - h) (by linarith) (by linarith))
      (mem C hC0 (by linarith)) hc
    have h4 := hF (1 - h) (by linarith) le_rfl
    rw [show h + (1 - h) = 1 by ring] at h4
    linarith

/-- The fibre condition in the form `2 max_i r(Z_i) ≤ ∑_i r(Z_i)` for the three absolute values
`A = B + C`, `C ≤ B ≤ h`, `A ≤ 1` (with the roles of `B` and `C` symmetric). -/
theorem thm83_fibre_max (hanti : AntitoneOn r (Icc 0 1)) (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hF : CondF r h) {A B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hBh : B ≤ h) (hCh : C ≤ h)
    (hA : A = B + C) (hA1 : A ≤ 1) :
    2 * max (r A) (max (r B) (r C)) ≤ r A + r B + r C := by
  have mem : ∀ x, 0 ≤ x → x ≤ 1 → x ∈ Icc (0:ℝ) 1 := fun x h0 h1 => ⟨h0, h1⟩
  rcases le_total C B with hCB | hBC
  · have := thm83_fibre hanti hh hh1 hF hC0 hCB hBh hA hA1
    have hAC : r A ≤ r C := hanti (mem C hC0 (by linarith)) (mem A (by linarith) hA1) (by linarith)
    have hBC : r B ≤ r C := hanti (mem C hC0 (by linarith)) (mem B hB0 (by linarith)) hCB
    rw [max_eq_right hBC, max_eq_right hAC]
    linarith
  · have := thm83_fibre hanti hh hh1 hF hB0 hBC hCh (by rw [hA]; ring) hA1
    have hAB : r A ≤ r B := hanti (mem B hB0 (by linarith)) (mem A (by linarith) hA1) (by linarith)
    have hCB : r C ≤ r B := hanti (mem B hB0 (by linarith)) (mem C hC0 (by linarith)) hBC
    rw [max_eq_left hCB, max_eq_right hAB]
    linarith

/-- `(F_{1/2})` holds for every concave `r` on `[0, 1]` with `r(1) ≥ 0`. -/
theorem condF_half (hconc : ConcaveOn ℝ (Icc 0 1) r) (h1 : 0 ≤ r 1) : CondF r (1 / 2) := by
  intro c hc0 hc1
  have hc1' : c < 1 := by linarith
  -- `r(x) ≥ r(c) (1 - x)/(1 - c)` for `c ≤ x ≤ 1`
  have key : ∀ x, c ≤ x → x ≤ 1 → (1 - x) / (1 - c) * r c ≤ r x := by
    intro x hx1 hx2
    have hθ0 : 0 ≤ (1 - x) / (1 - c) := div_nonneg (by linarith) (by linarith)
    have hθ1 : 0 ≤ 1 - (1 - x) / (1 - c) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have := hconc.2 (show c ∈ Icc (0:ℝ) 1 from ⟨hc0, hc1'.le⟩)
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by simp) hθ0 hθ1 (by ring)
    simp only [smul_eq_mul] at this
    have e : (1 - x) / (1 - c) * c + (1 - (1 - x) / (1 - c)) * 1 = x := by
      field_simp; ring
    rw [e] at this
    nlinarith
  have k1 := key (1 / 2) (by linarith) (by norm_num)
  have k2 := key (1 / 2 + c) (by linarith) (by linarith)
  have e : (1 - 1 / 2) / (1 - c) * r c + (1 - (1 / 2 + c)) / (1 - c) * r c = r c := by
    field_simp; ring
  linarith

/-- `(F_h)` holds if `r` is non-increasing on `[0, 1]` and `r(0) ≤ r(h) + r(1)`. -/
theorem condF_of_crude (hanti : AntitoneOn r (Icc 0 1)) (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hcrude : r 0 ≤ r h + r 1) : CondF r h := by
  intro c hc0 hc1
  have mem : ∀ x, 0 ≤ x → x ≤ 1 → x ∈ Icc (0:ℝ) 1 := fun x h0 h1 => ⟨h0, h1⟩
  have h1 : r c ≤ r 0 := hanti (mem 0 le_rfl zero_le_one) (mem c hc0 (by linarith)) hc0
  have h2 : r 1 ≤ r (h + c) := hanti (mem (h + c) (by linarith) (by linarith))
    (mem 1 zero_le_one le_rfl) (by linarith)
  linarith

/-- `(F_h)` holds if `r` is concave on `[0, 1]` and agrees on `[h, 1]` with an affine function
`σ (2h - a)` vanishing at `2h`; moreover `r ≤ σ (2h - ·)` on `[0, h]`. -/
theorem condF_of_affine (hconc : ConcaveOn ℝ (Icc 0 1) r) (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    {σ : ℝ} (haff : ∀ a ∈ Icc h 1, r a = σ * (2 * h - a)) :
    (∀ x ∈ Icc 0 h, r x ≤ σ * (2 * h - x)) ∧ CondF r h := by
  have below : ∀ x ∈ Icc 0 h, r x ≤ σ * (2 * h - x) := by
    intro x hx
    have hx1 : x < 1 := by linarith [hx.2]
    set θ := (1 - h) / (1 - x)
    have hθ : 0 < θ := div_pos (by linarith) (by linarith)
    have hθ1 : 0 ≤ 1 - θ := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith [hx.2]
    have := hconc.2 (show x ∈ Icc (0:ℝ) 1 from ⟨hx.1, hx1.le⟩)
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by simp) hθ.le hθ1 (by ring)
    simp only [smul_eq_mul] at this
    have e : θ * x + (1 - θ) * 1 = h := by simp only [θ]; field_simp; ring
    rw [e, haff h ⟨le_rfl, hh1.le⟩, haff 1 ⟨hh1.le, le_rfl⟩] at this
    have e2 : σ * (2 * h - h) - (1 - θ) * (σ * (2 * h - 1)) = θ * (σ * (2 * h - x)) := by
      simp only [θ]; field_simp; ring
    have : θ * r x ≤ θ * (σ * (2 * h - x)) := by linarith
    exact le_of_mul_le_mul_left this hθ
  refine ⟨below, fun c hc0 hc1 => ?_⟩
  rcases le_total c h with hch | hch
  · have := below c ⟨hc0, hch⟩
    rw [haff h ⟨le_rfl, hh1.le⟩, haff (h + c) ⟨by linarith, by linarith⟩]
    linarith
  · -- `c ≥ h` forces `c = h = 1/2`... in general `c ≤ 1 - h ≤ h`
    have : c = h := le_antisymm (by linarith) hch
    subst this
    have := below c ⟨hc0, le_rfl⟩
    rw [haff c ⟨le_rfl, hh1.le⟩, haff (c + c) ⟨by linarith, by linarith⟩]
    linarith

/-- The integral of `(P_h)` for an affine tail: if `r = σ (2h - ·)` on `[h, 1]`, then
`2 ∫_h^1 r^{k-1}/(2h - a) = 2 σ^{k-1} (h^{k-1} - (2h-1)^{k-1})/(k-1)` for `k ≥ 2`. -/
theorem condP_affine_integral (hh : 1 / 2 ≤ h) (hh1 : h < 1) {σ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (haff : ∀ a ∈ Icc h 1, r a = σ * (2 * h - a)) :
    IntervalIntegrable (fun a => r a ^ (k - 1) / (2 * h - a)) volume h 1 ∧
      ∫ a in h..1, r a ^ (k - 1) / (2 * h - a) =
        σ ^ (k - 1) * (h ^ (k - 1) - (2 * h - 1) ^ (k - 1)) / (k - 1) := by
  have hae : ∀ᵐ a ∂volume, a ∈ Set.uIoc h 1 →
      r a ^ (k - 1) / (2 * h - a) = σ ^ (k - 1) * (2 * h - a) ^ (k - 2) := by
    filter_upwards [Measure.ae_ne volume 1] with a ha1 ha
    rw [uIoc_of_le hh1.le] at ha
    have hpos : 0 < 2 * h - a := by
      have : a < 1 := lt_of_le_of_ne ha.2 ha1
      linarith
    rw [haff a ⟨ha.1.le, ha.2⟩, mul_pow]
    have e : k - 1 = (k - 2) + 1 := by omega
    rw [e, pow_succ (2 * h - a)]
    field_simp
  have hcont : Continuous fun a : ℝ => σ ^ (k - 1) * (2 * h - a) ^ (k - 2) := by fun_prop
  have hint : ∫ a in h..1, σ ^ (k - 1) * (2 * h - a) ^ (k - 2) =
      σ ^ (k - 1) * (h ^ (k - 1) - (2 * h - 1) ^ (k - 1)) / (k - 1) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ (k - 2)) (2 * h), integral_pow]
    have e : k - 2 + 1 = k - 1 := by omega
    rw [e, show 2 * h - h = h by ring]
    have hk1 : ((k - 2 : ℕ) : ℝ) + 1 = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [hk1]; ring
  refine ⟨(hcont.intervalIntegrable h 1).congr_ae ?_, ?_⟩
  · exact ((ae_restrict_iff' measurableSet_uIoc).2 hae).mono fun a ha => ha.symm
  · rw [intervalIntegral.integral_congr_ae hae, hint]

/-- **Theorem 83, `(P_h)` for an affine tail**: if `r = σ (2h - ·)` on `[h, 1]` with `σ ≥ 0`,
then `(P_h)` holds for `k ≥ 3`, and for `k = 2` when `h ≥ 2/3`. -/
theorem condP_of_affine (hh : 1 / 2 ≤ h) (hh1 : h < 1) {σ : ℝ} (hσ : 0 ≤ σ) {k : ℕ}
    (hk : 3 ≤ k ∨ (k = 2 ∧ 2 / 3 ≤ h)) (haff : ∀ a ∈ Icc h 1, r a = σ * (2 * h - a)) :
    CondP r h k := by
  have hk2 : 2 ≤ k := by rcases hk with hk | hk <;> omega
  obtain ⟨hi, he⟩ := condP_affine_integral hh hh1 hk2 haff
  refine ⟨hi, ?_⟩
  rw [he, haff h ⟨le_rfl, hh1.le⟩, show 2 * h - h = h by ring, mul_pow]
  rcases hk with hk | ⟨rfl, h23⟩
  · have hk1 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hA : 0 ≤ (2 * h - 1) ^ (k - 1) := pow_nonneg (by linarith) _
    have hB : 0 ≤ σ ^ (k - 1) := pow_nonneg hσ _
    have hC : 0 ≤ h ^ (k - 1) := pow_nonneg (by linarith) _
    rw [mul_div_assoc, ← mul_assoc, mul_comm 2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  · norm_num
    nlinarith

end Thm83

/-! ### Lemma 82: the wider coupling of the levels (analytic part) -/

section Lemma82

open Set

variable (ν : ℝ → ℝ) (h : ℝ)

/-- The tail term `ν(t + h) 1[t < 1 - h] / (h - t)` of the integrand of Lemma 82. -/
def gTail (t : ℝ) : ℝ := if t < 1 - h then ν (t + h) / (h - t) else 0

/-- The integrand `-3 ν'(t) + 6 ν(t + h) 1[t < 1 - h] / (h - t)` of Lemma 82. -/
def qInt (t : ℝ) : ℝ := -3 * deriv ν t + 6 * gTail ν h t

/-- `α₀ = 3 ν(h) - 6 ∫_h^1 ν(a)/(2h - a) da`. -/
def alpha0 : ℝ := 3 * ν h - 6 * ∫ a in h..1, ν a / (2 * h - a)

/-- `α(x)/x² = α₀/h² + ∫_x^h q(t)/t² dt` on `(0, h]`. -/
def Qf (x : ℝ) : ℝ := alpha0 ν h / h ^ 2 + ∫ t in x..h, qInt ν h t / t ^ 2

/-- The density `α` of Lemma 82: `x² Qf(x)` on `(0, h]`, `3 ν(x)` on `(h, 1]`. -/
def alphaL (x : ℝ) : ℝ := if x ≤ h then x ^ 2 * Qf ν h x else 3 * ν x

/-- The density `b` of `B` (and `C`) in Lemma 82, on `[0, h]`. -/
def bL (x : ℝ) : ℝ :=
  (∫ a in x..h, alphaL ν h a / a) + ∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a)

variable {ν h}

/-- The tail term, integrated: `∫_x^h gTail = ∫_{min(1, x+h)}^1 ν(a)/(2h - a) da`. -/
lemma integral_gTail (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hG : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1) {x : ℝ}
    (hx0 : 0 ≤ x) :
    IntervalIntegrable (gTail ν h) volume x h ∧
      ∫ t in x..h, gTail ν h t = ∫ a in min 1 (x + h)..1, ν a / (2 * h - a) := by
  have zero_on : ∀ y, 1 - h ≤ y → EqOn (gTail ν h) 0 (uIcc y h) := by
    intro y hy t ht
    have : 1 - h ≤ t := by
      rcases le_total y h with hyh | hyh
      · rw [uIcc_of_le hyh] at ht; linarith [ht.1]
      · rw [uIcc_of_ge hyh] at ht; linarith [ht.1]
    simp [gTail, not_lt.2 this]
  rcases lt_or_ge (1 - h) x with hx | hx
  · have hm : min 1 (x + h) = 1 := min_eq_left (by linarith)
    rw [hm, intervalIntegral.integral_same, intervalIntegral.integral_congr (zero_on x hx.le)]
    refine ⟨(intervalIntegrable_const (c := (0:ℝ))).congr ?_, by simp⟩
    exact fun t ht => (zero_on x hx.le (uIoc_subset_uIcc ht)).symm
  · have hm : min 1 (x + h) = x + h := min_eq_right (by linarith)
    rw [hm]
    -- on `[x, 1 - h]` the tail is the shifted `G`, except at `1 - h`
    have hshift : IntervalIntegrable (fun t => ν (t + h) / (2 * h - (t + h))) volume x (1 - h) := by
      have hG' : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume (x + h) (1 - h + h) := by
        rw [show 1 - h + h = 1 by ring]
        exact hG.mono_set (by
          rw [uIcc_of_le (by linarith), uIcc_of_le hh1.le]
          exact Icc_subset_Icc (by linarith) le_rfl)
      have := hG'.comp_add_right h
      simpa using this
    have hae : ∀ᵐ t ∂volume, t ∈ uIoc x (1 - h) →
        gTail ν h t = ν (t + h) / (2 * h - (t + h)) := by
      filter_upwards [Measure.ae_ne volume (1 - h)] with t ht hmem
      rw [uIoc_of_le hx] at hmem
      have : t < 1 - h := lt_of_le_of_ne hmem.2 ht
      simp only [gTail, this, ↓reduceIte]; congr 1; ring
    have i1 : IntervalIntegrable (gTail ν h) volume x (1 - h) :=
      hshift.congr_ae (((ae_restrict_iff' measurableSet_uIoc).2 hae).mono fun t ht => ht.symm)
    have i2 : IntervalIntegrable (gTail ν h) volume (1 - h) h :=
      (intervalIntegrable_const (c := (0:ℝ))).congr
        fun t ht => (zero_on (1 - h) le_rfl (uIoc_subset_uIcc ht)).symm
    refine ⟨i1.trans i2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
      intervalIntegral.integral_congr (zero_on (1 - h) le_rfl),
      intervalIntegral.integral_congr_ae hae]
    simp only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero]
    rw [intervalIntegral.integral_comp_add_right (fun a => ν a / (2 * h - a)) h]
    norm_num

/-- Integration by parts in Lemma 82: for `0 < x ≤ h`,
`2 ∫_x^h a Qf(a) da = h² Qf(h) - x² Qf(x) + ∫_x^h q`. -/
lemma ibp_Qf {x : ℝ} (hx0 : 0 < x) (hxh : x ≤ h)
    (hq : IntervalIntegrable (qInt ν h) volume x h) :
    2 * ∫ a in x..h, a * Qf ν h a =
      h ^ 2 * Qf ν h h - x ^ 2 * Qf ν h x + ∫ a in x..h, qInt ν h a := by
  set φ := fun t => qInt ν h t / t ^ 2 with hφdef
  have hpos : ∀ a ∈ uIcc x h, 0 < a := fun a ha => by
    rw [uIcc_of_le hxh] at ha; linarith [ha.1]
  have hφ : IntervalIntegrable φ volume x h := by
    have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc x h) :=
      (continuousOn_pow 2).inv₀ fun a ha => by positivity [hpos a ha]
    have := hq.mul_continuousOn hc
    simpa [hφdef, div_eq_mul_inv] using this
  set C := alpha0 ν h / h ^ 2
  have hQeq : Qf ν h = fun a => C - ∫ t in h..a, φ t := by
    funext a; simp only [Qf, C, hφdef]; rw [intervalIntegral.integral_symm]; ring
  have hF := hφ.absolutelyContinuousOnInterval_intervalIntegral (c := h) right_mem_uIcc
  have hQac : AbsolutelyContinuousOnInterval (Qf ν h) x h := by
    rw [hQeq]
    exact (contDiffOn_const (c := C)).absolutelyContinuousOnInterval.sub hF
  have hderiv : ∀ᵐ a ∂volume, a ∈ uIcc x h → deriv (Qf ν h) a = -φ a := by
    filter_upwards [hφ.ae_hasDerivAt_integral] with a ha hmem
    have := (ha hmem h right_mem_uIcc).const_sub C
    rw [hQeq]; exact this.deriv
  have hfac : AbsolutelyContinuousOnInterval (fun a : ℝ => a ^ 2 / 2) x h :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have hibp := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hfac hQac
  have hd : ∀ a : ℝ, deriv (fun a : ℝ => a ^ 2 / 2) a = a := fun a => by
    have : HasDerivAt (fun a : ℝ => a ^ 2 / 2) a a := by
      simpa using ((hasDerivAt_pow 2 a).div_const 2)
    exact this.deriv
  simp only [hd] at hibp
  have hL : ∫ a in x..h, a ^ 2 / 2 * deriv (Qf ν h) a = ∫ a in x..h, (-1 / 2) * qInt ν h a := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv] with a ha hmem
    have hmem' := uIoc_subset_uIcc hmem
    rw [ha hmem']
    have := (hpos a hmem').ne'
    simp only [hφdef]; field_simp
  rw [hL, intervalIntegral.integral_const_mul] at hibp
  linarith

lemma qInt_integrable (hh : 1 / 2 ≤ h) (hh1 : h < 1) (hac : AbsolutelyContinuousOnInterval ν 0 1)
    (hG : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1) {x : ℝ}
    (hx0 : 0 ≤ x) (hxh : x ≤ h) : IntervalIntegrable (qInt ν h) volume x h := by
  have hd : IntervalIntegrable (deriv ν) volume x h :=
    hac.intervalIntegrable_deriv.mono_set (by
      rw [uIcc_of_le hxh, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hx0 hh1.le)
  exact (hd.const_mul (-3)).add ((integral_gTail hh hh1 hG hx0).1.const_mul 6)

/-- **Lemma 82, the identity** `α + 2b = 3ν` on `(0, h]` (`g:lem:levels`). Here `ν` is absolutely
continuous on `[0, 1]` and `a ↦ ν(a)/(2h - a)` is integrable on `[h, 1]` (automatic for
`h > 1/2` and a hypothesis of the paper for `h = 1/2`). -/
theorem lemma82_identity (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hac : AbsolutelyContinuousOnInterval ν 0 1)
    (hG : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1) {x : ℝ}
    (hx0 : 0 < x) (hxh : x ≤ h) :
    alphaL ν h x + 2 * bL ν h x = 3 * ν x := by
  have hh0 : 0 < h := by linarith
  have hq := qInt_integrable hh hh1 hac hG hx0.le hxh
  have hibp := ibp_Qf hx0 hxh hq
  have hcongr : ∫ a in x..h, alphaL ν h a / a = ∫ a in x..h, a * Qf ν h a := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [uIcc_of_le hxh] at ha
    have ha0 : a ≠ 0 := by linarith [ha.1]
    simp only [alphaL, ha.2, ↓reduceIte]; field_simp
  have hQh : h ^ 2 * Qf ν h h = alpha0 ν h := by
    simp only [Qf, intervalIntegral.integral_same, add_zero]; field_simp
  obtain ⟨hgi, hgint⟩ := integral_gTail hh hh1 hG hx0.le
  have hdi : IntervalIntegrable (deriv ν) volume x h :=
    hac.intervalIntegrable_deriv.mono_set (by
      rw [uIcc_of_le hxh, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hx0.le hh1.le)
  have hftc : ∫ t in x..h, deriv ν t = ν h - ν x :=
    (hac.mono (by
      rw [uIcc_of_le hxh, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hx0.le hh1.le)).integral_deriv_eq_sub
  have hqint : ∫ t in x..h, qInt ν h t =
      -3 * (ν h - ν x) + 6 * ∫ a in min 1 (x + h)..1, ν a / (2 * h - a) := by
    simp only [qInt]
    rw [intervalIntegral.integral_add (hdi.const_mul _) (hgi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hftc, hgint]
  set m := min 1 (x + h)
  have hm1 : h ≤ m := le_min hh1.le (by linarith)
  have hm2 : m ≤ 1 := min_le_left _ _
  have hG1 : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h m :=
    hG.mono_set (by rw [uIcc_of_le hm1, uIcc_of_le hh1.le]; exact Icc_subset_Icc le_rfl hm2)
  have hG2 : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume m 1 :=
    hG.mono_set (by rw [uIcc_of_le hm2, uIcc_of_le hh1.le]; exact Icc_subset_Icc hm1 le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hG1 hG2
  have hb2 : ∫ a in h..m, 3 * ν a / (2 * h - a) = 3 * ∫ a in h..m, ν a / (2 * h - a) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext a; ring
  have hax : alphaL ν h x = x ^ 2 * Qf ν h x := by simp [alphaL, hxh]
  simp only [bL]
  rw [hcongr, hb2, hax]
  rw [hQh, hqint] at hibp
  simp only [alpha0] at hibp
  linarith

/-- `ν' ≤ 0` inside `(0, 1)` for `ν` non-increasing on `[0, 1]` (`deriv` is `0` where `ν` is not
differentiable). -/
lemma deriv_nonpos_of_antitoneOn (hanti : AntitoneOn ν (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    deriv ν t ≤ 0 := by
  by_cases hd : DifferentiableAt ℝ ν t
  · have := hanti.derivWithin_nonpos (x := t)
    rwa [hd.derivWithin (uniqueDiffOn_Icc zero_lt_one t (Ioo_subset_Icc_self ht))] at this
  · rw [deriv_zero_of_not_differentiableAt hd]

/-- **Lemma 82, nonnegativity**: under `(P_h)` (`g:eq:Ph`), with `ν ≥ 0` non-increasing, the
density `α` is nonnegative on `(0, 1]`. -/
theorem lemma82_alpha_nonneg (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hanti : AntitoneOn ν (Icc 0 1)) (hν0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x)
    (hP : 2 * ∫ a in h..1, ν a / (2 * h - a) ≤ ν h) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ alphaL ν h x := by
  have hh0 : 0 < h := by linarith
  by_cases hxh : x ≤ h
  · simp only [alphaL, hxh, ↓reduceIte]
    refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
    · simp only [alpha0]; exact div_nonneg (by linarith) (by positivity)
    · refine intervalIntegral.integral_nonneg_of_ae_restrict hxh ?_
      have hne : ∀ᵐ t ∂volume, t ≠ h := Measure.ae_ne volume h
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hne] with t htne ht
      have ht0 : 0 < t := by linarith [ht.1]
      have htlt : t < h := lt_of_le_of_ne ht.2 htne
      refine div_nonneg ?_ (by positivity)
      simp only [qInt, gTail]
      have h1 := deriv_nonpos_of_antitoneOn hanti ⟨ht0, by linarith⟩
      split_ifs with hc
      · have : 0 ≤ ν (t + h) := hν0 _ ⟨by linarith, by linarith⟩
        have : 0 ≤ ν (t + h) / (h - t) := div_nonneg this (by linarith)
        linarith
      · linarith
  · simp only [alphaL, hxh, ↓reduceIte]
    linarith [hν0 x ⟨hx0.le, hx1⟩]

/-- `Qf` is absolutely continuous on `[x, h]` for `0 < x ≤ h`. -/
lemma Qf_ac {x : ℝ} (hx0 : 0 < x) (hxh : x ≤ h)
    (hq : IntervalIntegrable (qInt ν h) volume x h) :
    AbsolutelyContinuousOnInterval (Qf ν h) x h := by
  set φ := fun t => qInt ν h t / t ^ 2 with hφdef
  have hpos : ∀ a ∈ uIcc x h, 0 < a := fun a ha => by
    rw [uIcc_of_le hxh] at ha; linarith [ha.1]
  have hφ : IntervalIntegrable φ volume x h := by
    have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc x h) :=
      (continuousOn_pow 2).inv₀ fun a ha => by positivity [hpos a ha]
    have := hq.mul_continuousOn hc
    simpa [hφdef, div_eq_mul_inv] using this
  set C := alpha0 ν h / h ^ 2
  have hQeq : Qf ν h = fun a => C - ∫ t in h..a, φ t := by
    funext a; simp only [Qf, C, hφdef]; rw [intervalIntegral.integral_symm]; ring
  have hF := hφ.absolutelyContinuousOnInterval_intervalIntegral (c := h) right_mem_uIcc
  rw [hQeq]
  exact (contDiffOn_const (c := C)).absolutelyContinuousOnInterval.sub hF

lemma bL_tail_nonneg (hh : 1 / 2 ≤ h) (hh1 : h < 1) (hν0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x)
    {x : ℝ} (hx0 : 0 ≤ x) : 0 ≤ ∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a) := by
  have hm1 : h ≤ min 1 (x + h) := le_min hh1.le (by linarith)
  refine intervalIntegral.integral_nonneg hm1 fun a ha => ?_
  have ha1 : a ≤ 1 := ha.2.trans (min_le_left _ _)
  exact div_nonneg (by linarith [hν0 a ⟨by linarith [ha.1], ha1⟩]) (by linarith)

/-- `α(a)/a` is integrable on `[0, h]`: the integrals `∫_x^h α(a)/a = b(x) - (tail) ≤ 3ν(0)/2`
are bounded, by the identity `α + 2b = 3ν` and `α ≥ 0`. (The paper uses the Lipschitz property
of `ν` on `[0, h]` here, to get `α(x) = O(x)`; it is not needed.) -/
lemma alpha_div_integrable (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hac : AbsolutelyContinuousOnInterval ν 0 1) (hanti : AntitoneOn ν (Icc 0 1))
    (hν0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x)
    (hG : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1)
    (hP : 2 * ∫ a in h..1, ν a / (2 * h - a) ≤ ν h) :
    IntervalIntegrable (fun a => alphaL ν h a / a) volume 0 h := by
  have hh0 : 0 < h := by linarith
  set xs : ℕ → ℝ := fun n => h / (n + 1)
  have hxs0 : ∀ n, 0 < xs n := fun n => by positivity
  have hxsh : ∀ n, xs n ≤ h := fun n => by
    simp only [xs]; rw [div_le_iff₀ (by positivity)]; nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hcont : ∀ n, ContinuousOn (fun a => alphaL ν h a / a) (Icc (xs n) h) := by
    intro n
    have hQ := (Qf_ac (hxs0 n) (hxsh n)
      (qInt_integrable hh hh1 hac hG (hxs0 n).le (hxsh n))).continuousOn
    rw [uIcc_of_le (hxsh n)] at hQ
    refine (continuousOn_id.mul hQ).congr fun a ha => ?_
    have ha0 : a ≠ 0 := by linarith [ha.1, hxs0 n]
    simp only [alphaL, ha.2, ↓reduceIte]; field_simp; rfl
  have hint : ∀ n, IntegrableOn (fun a => alphaL ν h a / a) (Ioc (xs n) h) := fun n =>
    ((hcont n).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hlim : Filter.Tendsto xs Filter.atTop (nhds 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul h
    rw [mul_zero] at this
    exact this.congr fun n => by simp only [xs]; ring
  have hI := integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (I := 3 / 2 * ν 0)
    hint hlim (Filter.Eventually.of_forall fun n => ?_)
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh0.le]; exact hI
  · -- the bound
    have hnn : ∀ a ∈ Ioc (xs n) h, 0 ≤ alphaL ν h a / a := fun a ha =>
      div_nonneg (lemma82_alpha_nonneg hh hh1 hanti hν0 hP (by linarith [ha.1, hxs0 n])
        (by linarith [ha.2])) (by linarith [ha.1, hxs0 n])
    have e : ∫ x in Ioc (xs n) h, ‖alphaL ν h x / x‖ = ∫ a in xs n..h, alphaL ν h a / a := by
      rw [intervalIntegral.integral_of_le (hxsh n)]
      refine setIntegral_congr_fun measurableSet_Ioc fun a ha => ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg (hnn a ha)]
    rw [e]
    have hid := lemma82_identity hh hh1 hac hG (hxs0 n) (hxsh n)
    have ha := lemma82_alpha_nonneg hh hh1 hanti hν0 hP (hxs0 n) ((hxsh n).trans hh1.le)
    have ht := bL_tail_nonneg hh hh1 hν0 (hxs0 n).le
    have hν : ν (xs n) ≤ ν 0 := hanti ⟨le_rfl, zero_le_one⟩
      ⟨(hxs0 n).le, (hxsh n).trans hh1.le⟩ (hxs0 n).le
    simp only [bL] at hid
    linarith

/-- `∫_0^h ∫_x^h f = ∫_0^h x f(x)` for `f` integrable on `[0, h]`, with the integrability of the
inner integral. -/
lemma integral_integral_tail {f : ℝ → ℝ} {H : ℝ}
    (hf : IntervalIntegrable f volume 0 H) :
    IntervalIntegrable (fun x => ∫ a in x..H, f a) volume 0 H ∧
      ∫ x in (0:ℝ)..H, (∫ a in x..H, f a) = ∫ x in (0:ℝ)..H, x * f x := by
  have hB : (fun x => ∫ a in x..H, f a) = fun x => -∫ a in H..x, f a := by
    funext x; rw [intervalIntegral.integral_symm]
  have hF := hf.absolutelyContinuousOnInterval_intervalIntegral (c := H) right_mem_uIcc
  have hBac : AbsolutelyContinuousOnInterval (fun x => ∫ a in x..H, f a) 0 H := by
    rw [hB]; exact hF.neg
  refine ⟨hBac.continuousOn.intervalIntegrable, ?_⟩
  have hderiv : ∀ᵐ x ∂volume, x ∈ uIcc 0 H → deriv (fun x => ∫ a in x..H, f a) x = -f x := by
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hmem
    rw [hB]; exact (hx hmem H right_mem_uIcc).neg.deriv
  have hid : AbsolutelyContinuousOnInterval (fun x : ℝ => x) 0 H :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have hibp := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hid hBac
  simp only [deriv_id'', one_mul, intervalIntegral.integral_same, mul_zero, sub_zero,
    zero_mul] at hibp
  have hL : ∫ x in (0:ℝ)..H, x * deriv (fun x => ∫ a in x..H, f a) x =
      ∫ x in (0:ℝ)..H, -(x * f x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv] with x hx hmem
    rw [hx (uIoc_subset_uIcc hmem)]; ring
  rw [hL, intervalIntegral.integral_neg] at hibp
  linarith

/-- `∫_0^h t · gTail(t) dt = ∫_h^1 (a - h) ν(a)/(2h - a) da`. -/
lemma integral_mul_gTail (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hG : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1) :
    ∫ t in (0:ℝ)..h, t * gTail ν h t = ∫ a in h..1, (a - h) * (ν a / (2 * h - a)) := by
  have zero_on : EqOn (fun t => t * gTail ν h t) 0 (uIcc (1 - h) h) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    simp [gTail, not_lt.2 ht.1]
  have hGw : IntervalIntegrable (fun a => (a - h) * (ν a / (2 * h - a))) volume h 1 :=
    hG.continuousOn_mul (by fun_prop)
  have hshift : IntervalIntegrable (fun t => (t + h - h) * (ν (t + h) / (2 * h - (t + h))))
      volume 0 (1 - h) := by
    have hG' : IntervalIntegrable (fun a => (a - h) * (ν a / (2 * h - a))) volume (0 + h)
        (1 - h + h) := by
      rw [show 1 - h + h = 1 by ring, zero_add]; exact hGw
    have := hG'.comp_add_right h
    simpa using this
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc 0 (1 - h) →
      t * gTail ν h t = (t + h - h) * (ν (t + h) / (2 * h - (t + h))) := by
    filter_upwards [Measure.ae_ne volume (1 - h)] with t ht hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have : t < 1 - h := lt_of_le_of_ne hmem.2 ht
    simp only [gTail, this, ↓reduceIte]
    rw [show t + h - h = t by ring, show 2 * h - (t + h) = h - t by ring]
  have i1 : IntervalIntegrable (fun t => t * gTail ν h t) volume 0 (1 - h) :=
    hshift.congr_ae (((ae_restrict_iff' measurableSet_uIoc).2 hae).mono fun t ht => ht.symm)
  have i2 : IntervalIntegrable (fun t => t * gTail ν h t) volume (1 - h) h :=
    (intervalIntegrable_const (c := (0:ℝ))).congr
      fun t ht => (zero_on (uIoc_subset_uIcc ht)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr zero_on, intervalIntegral.integral_congr_ae hae]
  simp only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero]
  rw [intervalIntegral.integral_comp_add_right
    (fun a => (a - h) * (ν a / (2 * h - a))) h]
  norm_num

/-- **Lemma 82, total mass**: under the hypotheses of the lemma (`ν ≥ 0` a non-increasing,
absolutely continuous probability density on `[0, 1]`, `ν(a)/(2h - a)` integrable on `[h, 1]`,
and `(P_h)`), the function `α` is integrable on `[0, 1]` with `∫_0^1 α = 1`; with
`lemma82_alpha_nonneg`, it is a probability density. -/
theorem lemma82_integral (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hac : AbsolutelyContinuousOnInterval ν 0 1) (hanti : AntitoneOn ν (Icc 0 1))
    (hν0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x) (hν1 : ∫ x in (0:ℝ)..1, ν x = 1)
    (hG : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1)
    (hP : 2 * ∫ a in h..1, ν a / (2 * h - a) ≤ ν h) :
    IntervalIntegrable (alphaL ν h) volume 0 1 ∧ ∫ x in (0:ℝ)..1, alphaL ν h x = 1 := by
  have hh0 : 0 < h := by linarith
  have hνc : ContinuousOn ν (uIcc 0 1) := hac.continuousOn
  have hνi : ∀ a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → IntervalIntegrable ν volume a b :=
    fun a b ha hb => (hνc.mono (by
      rw [uIcc_of_le zero_le_one]
      exact uIcc_subset_Icc ha hb)).intervalIntegrable
  have hfi := alpha_div_integrable hh hh1 hac hanti hν0 hG hP
  -- `α` on `[0, h]` and on `[h, 1]`
  have hαae : ∀ᵐ x ∂volume, x ∈ uIoc 0 h → x * (alphaL ν h x / x) = alphaL ν h x := by
    filter_upwards [Measure.ae_ne volume 0] with x hx _
    field_simp
  have hα1 : IntervalIntegrable (alphaL ν h) volume 0 h :=
    (hfi.continuousOn_mul continuousOn_id).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 hαae)
  have hα2eq : EqOn (fun x => 3 * ν x) (alphaL ν h) (uIoc h 1) := by
    intro x hx
    rw [uIoc_of_le hh1.le] at hx
    simp [alphaL, not_le.2 hx.1]
  have hα2 : IntervalIntegrable (alphaL ν h) volume h 1 :=
    ((hνi h 1 ⟨hh0.le, hh1.le⟩ ⟨zero_le_one, le_rfl⟩).const_mul 3).congr hα2eq
  refine ⟨hα1.trans hα2, ?_⟩
  -- the two parts of `b`
  obtain ⟨hB1i, hB1⟩ := integral_integral_tail hfi
  rw [intervalIntegral.integral_congr_ae hαae] at hB1
  obtain ⟨hgi, -⟩ := integral_gTail hh hh1 hG le_rfl
  have hgi0 : IntervalIntegrable (gTail ν h) volume 0 h := (integral_gTail hh hh1 hG le_rfl).1
  obtain ⟨hTi, hT⟩ := integral_integral_tail hgi0
  set I0 := ∫ a in h..1, ν a / (2 * h - a)
  have hB2eq : EqOn (fun x => 3 * (I0 - ∫ a in x..h, gTail ν h a))
      (fun x => ∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a)) (uIcc 0 h) := by
    intro x hx
    rw [uIcc_of_le hh0.le] at hx
    simp only
    rw [(integral_gTail hh hh1 hG hx.1).2]
    set m := min 1 (x + h)
    have hm1 : h ≤ m := le_min hh1.le (by linarith [hx.1])
    have hm2 : m ≤ 1 := min_le_left _ _
    have hG1 : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h m :=
      hG.mono_set (by rw [uIcc_of_le hm1, uIcc_of_le hh1.le]; exact Icc_subset_Icc le_rfl hm2)
    have hG2 : IntervalIntegrable (fun a => ν a / (2 * h - a)) volume m 1 :=
      hG.mono_set (by rw [uIcc_of_le hm2, uIcc_of_le hh1.le]; exact Icc_subset_Icc hm1 le_rfl)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hG1 hG2
    have hb2 : ∫ a in h..m, 3 * ν a / (2 * h - a) = 3 * ∫ a in h..m, ν a / (2 * h - a) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext a; ring
    rw [hb2]; simp only [I0]; linarith
  have hB2i : IntervalIntegrable
      (fun x => ∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a)) volume 0 h :=
    ((intervalIntegrable_const.sub hTi).const_mul 3).congr
      fun x hx => hB2eq (uIoc_subset_uIcc hx)
  have hB2 : ∫ x in (0:ℝ)..h, (∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a)) =
      3 * ∫ a in h..1, ν a := by
    rw [← intervalIntegral.integral_congr hB2eq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const hTi, hT,
      integral_mul_gTail hh hh1 hG, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hGw : IntervalIntegrable (fun a => (a - h) * (ν a / (2 * h - a))) volume h 1 :=
      hG.continuousOn_mul (by fun_prop)
    have e : h * I0 - ∫ a in h..1, (a - h) * (ν a / (2 * h - a)) = ∫ a in h..1, ν a := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        (hG.const_mul h) hGw]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume (2 * h)] with a ha _
      have : 2 * h - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
      show h * (ν a / (2 * h - a)) - (a - h) * (ν a / (2 * h - a)) = ν a
      rw [show h * (ν a / (2 * h - a)) - (a - h) * (ν a / (2 * h - a)) =
        (2 * h - a) * (ν a / (2 * h - a)) by ring, mul_div_cancel₀ _ this]
    rw [e]
  -- integrate the identity over `(0, h]`
  have hid : ∫ x in (0:ℝ)..h, (alphaL ν h x + 2 * ((∫ a in x..h, alphaL ν h a / a) +
      ∫ a in h..min 1 (x + h), 3 * ν a / (2 * h - a))) = ∫ x in (0:ℝ)..h, 3 * ν x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x hx
    rw [uIoc_of_le hh0.le] at hx
    exact lemma82_identity hh hh1 hac hG hx.1 hx.2
  rw [intervalIntegral.integral_add hα1 ((hB1i.add hB2i).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hB1i hB2i, hB1, hB2,
    intervalIntegral.integral_const_mul] at hid
  have hα2int : ∫ x in h..1, alphaL ν h x = ∫ x in h..1, 3 * ν x :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => (hα2eq hx).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hα1 hα2, hα2int,
    intervalIntegral.integral_const_mul]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hνi 0 h ⟨le_rfl, zero_le_one⟩ ⟨hh0.le, hh1.le⟩)
    (hνi h 1 ⟨hh0.le, hh1.le⟩ ⟨zero_le_one, le_rfl⟩)
  rw [hν1] at hsplit
  linarith

/-- For `h > 1/2` the integrability hypothesis of Lemma 82 is automatic. -/
lemma tail_integrable_of_gt (hh : 1 / 2 < h) (hh1 : h < 1)
    (hac : AbsolutelyContinuousOnInterval ν 0 1) :
    IntervalIntegrable (fun a => ν a / (2 * h - a)) volume h 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hν := hac.continuousOn
  rw [uIcc_of_le zero_le_one] at hν
  rw [uIcc_of_le hh1.le]
  refine (hν.mono (Icc_subset_Icc (by linarith) le_rfl)).div (by fun_prop) fun a ha => ?_
  linarith [ha.2]

/-- The levels of Lemma 82: with `δ(a) = min(a, 2h - a)/2`, `B = a/2 + D`, `C = a/2 - D` and
`|D| ≤ δ(a)`, we have `A = B + C` and `B, C ∈ [0, h]`; the range of `B` is
`[0, a]` for `a ≤ h` and `[a - h, h]` for `a > h`. -/
lemma levels_range {a D : ℝ}
    (hD : |D| ≤ min a (2 * h - a) / 2) :
    a = (a / 2 + D) + (a / 2 - D) ∧ a / 2 + D ∈ Icc 0 h ∧ a / 2 - D ∈ Icc 0 h ∧
      a / 2 - min a (2 * h - a) / 2 = (if a ≤ h then 0 else a - h) ∧
      a / 2 + min a (2 * h - a) / 2 = (if a ≤ h then a else h) := by
  have h1 := le_abs_self D
  have h2 := neg_abs_le D
  have m1 := min_le_left a (2 * h - a)
  have m2 := min_le_right a (2 * h - a)
  refine ⟨by ring, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_, ?_⟩ <;>
  · split_ifs with hah
    · rw [min_eq_left (by linarith)]; ring
    · rw [min_eq_right (by linarith)]; ring

end Lemma82

/-! ### Corollary 84 (a), (c), (d), (e) -/

section Cor84

open Set

variable {r : ℝ → ℝ}

/-- **Corollary 84 (a)**: if `r ≥ 0` is non-increasing on `[0, 1]` with `r(1) ≥ r(0)/2`, then any
three levels in `[0, 1]` satisfy the fibre condition `2 max r(Z_i) ≤ ∑ r(Z_i)`. -/
theorem cor84a (hanti : AntitoneOn r (Icc 0 1)) (h1 : r 0 / 2 ≤ r 1) {x y z : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) (hz : z ∈ Icc (0:ℝ) 1) :
    2 * max (r x) (max (r y) (r z)) ≤ r x + r y + r z := by
  have lo : ∀ w ∈ Icc (0:ℝ) 1, r 1 ≤ r w := fun w hw => hanti hw ⟨zero_le_one, le_rfl⟩ hw.2
  have hi : ∀ w ∈ Icc (0:ℝ) 1, r w ≤ r 0 := fun w hw => hanti ⟨le_rfl, zero_le_one⟩ hw hw.1
  have := lo x hx; have := lo y hy; have := lo z hz
  have := hi x hx; have := hi y hy; have := hi z hz
  rcases max_cases (r y) (r z) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases max_cases (r x) (max (r y) (r z)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rw [h2] <;> (try rw [h1]) <;> linarith

/-- **Corollary 84 (c)**: if `r` is non-increasing, continuous and nonnegative on `[0, 1]`, and
`r = r(0)` on `[0, h]` with `e^{1/2}/(2e^{1/2} - 1) ≤ h < 1`, then `(F_h)` and `(P_h)` hold (for
every `k ≥ 1`). -/
theorem cor84c (hanti : AntitoneOn r (Icc 0 1)) (hcont : ContinuousOn r (Icc 0 1))
    (hr0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ r x) {h : ℝ}
    (hh : Real.exp (1 / 2) / (2 * Real.exp (1 / 2) - 1) ≤ h) (hh1 : h < 1)
    (hflat : r h = r 0) (k : ℕ) : CondF r h ∧ CondP r h k := by
  set E := Real.exp (1 / 2)
  have hE : 1 < E := by have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  have hE2 : 0 < 2 * E - 1 := by linarith
  have hhE : E ≤ h * (2 * E - 1) := by rwa [div_le_iff₀ hE2] at hh
  have hh2 : 1 / 2 < h := by nlinarith
  have hh0 : 0 < h := by linarith
  refine ⟨condF_of_crude hanti hh2.le hh1 (by rw [hflat]; linarith [hr0 1 ⟨zero_le_one, le_rfl⟩]),
    ?_⟩
  have hden : ∀ a ∈ Icc h 1, 0 < 2 * h - a := fun a ha => by linarith [ha.2]
  have hsub : Icc h 1 ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc hh0.le le_rfl
  have hci : ContinuousOn (fun a => r a ^ (k - 1) / (2 * h - a)) (Icc h 1) :=
    ((hcont.mono hsub).pow _).div (continuousOn_const.sub continuousOn_id)
      fun a ha => (hden a ha).ne'
  have hint : IntervalIntegrable (fun a => r a ^ (k - 1) / (2 * h - a)) volume h 1 := by
    rw [← uIcc_of_le hh1.le] at hci; exact hci.intervalIntegrable
  refine ⟨hint, ?_⟩
  have hci2 : ContinuousOn (fun a => r 0 ^ (k - 1) / (2 * h - a)) (Icc h 1) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun a ha => (hden a ha).ne'
  have hint2 : IntervalIntegrable (fun a => r 0 ^ (k - 1) / (2 * h - a)) volume h 1 := by
    rw [← uIcc_of_le hh1.le] at hci2; exact hci2.intervalIntegrable
  have hmono : ∫ a in h..1, r a ^ (k - 1) / (2 * h - a) ≤
      ∫ a in h..1, r 0 ^ (k - 1) / (2 * h - a) := by
    refine intervalIntegral.integral_mono_on hh1.le hint hint2 fun a ha => ?_
    refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (hr0 a (hsub ha)) ?_ _) (hden a ha).le
    exact hanti ⟨le_rfl, zero_le_one⟩ (hsub ha) (hsub ha).1
  have hlog : ∫ a in h..1, r 0 ^ (k - 1) / (2 * h - a) =
      r 0 ^ (k - 1) * Real.log (h / (2 * h - 1)) := by
    have e : (fun a => r 0 ^ (k - 1) / (2 * h - a)) = fun a => r 0 ^ (k - 1) * (2 * h - a)⁻¹ := by
      funext a; rw [div_eq_mul_inv]
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) (2 * h),
      integral_inv_of_pos (by linarith) (by linarith)]
    congr 2; ring
  have hlog2 : Real.log (h / (2 * h - 1)) ≤ 1 / 2 := by
    rw [Real.log_le_iff_le_exp (div_pos hh0 (by linarith)), div_le_iff₀ (by linarith)]
    nlinarith
  have hr0' : 0 ≤ r 0 ^ (k - 1) := pow_nonneg (hr0 0 ⟨le_rfl, zero_le_one⟩) _
  rw [hflat]
  calc 2 * ∫ a in h..1, r a ^ (k - 1) / (2 * h - a)
      ≤ 2 * (r 0 ^ (k - 1) * Real.log (h / (2 * h - 1))) := by rw [← hlog]; linarith
    _ ≤ 2 * (r 0 ^ (k - 1) * (1 / 2)) := by gcongr
    _ = r 0 ^ (k - 1) := by ring

/-- **Corollary 84 (d)**, `ρ < 1/2`: for the double frustum `r(z) = 1 - (1 - ρ)|z|`, with
`h = 1/(2(1 - ρ))`, `r = (1 - ρ)(2h - ·)` on `[h, 1]`, `(F_h)` holds, and `(P_h)` holds for
`k ≥ 3`, and for `k = 2` when `ρ ≥ 1/4`. (For `ρ ≥ 1/2` part (a) applies.) -/
theorem cor84d {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) {k : ℕ} (hk : 3 ≤ k ∨ (k = 2 ∧ 1 / 4 ≤ ρ)) :
    let r := fun z : ℝ => 1 - (1 - ρ) * |z|
    let h := 1 / (2 * (1 - ρ))
    1 / 2 ≤ h ∧ h < 1 ∧ CondF r h ∧ CondP r h k := by
  intro r h
  have h1ρ : 0 < 1 - ρ := by linarith
  have hh : 1 / 2 ≤ h := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hh1 : h < 1 := by simp only [h]; rw [div_lt_one (by positivity)]; linarith
  have haff : ∀ a ∈ Icc h 1, r a = (1 - ρ) * (2 * h - a) := by
    intro a ha
    have ha0 : 0 ≤ a := by linarith [ha.1]
    simp only [r, abs_of_nonneg ha0, h]; field_simp
  have hconc : ConcaveOn ℝ (Icc 0 1) r := by
    have : ConcaveOn ℝ (Icc (0:ℝ) 1) fun z => 1 + (-(1 - ρ)) • z :=
      (concaveOn_const _ (convex_Icc 0 1)).add
        (LinearMap.concaveOn (LinearMap.lsmul ℝ ℝ (-(1 - ρ))) (convex_Icc 0 1) |>.congr
          fun x _ => by simp; ring)
    refine this.congr fun z hz => ?_
    simp only [r, abs_of_nonneg hz.1, smul_eq_mul]; ring
  refine ⟨hh, hh1, (condF_of_affine hconc hh hh1 haff).2, condP_of_affine hh hh1 h1ρ.le ?_ haff⟩
  rcases hk with hk | ⟨hk, hρ4⟩
  · exact Or.inl hk
  · refine Or.inr ⟨hk, ?_⟩
    simp only [h]; rw [le_div_iff₀ (by positivity)]; nlinarith

/-- **Corollary 84 (e)**: for the octagons `r(z) = min(1, 2 - e - |z|)`, `0 < e < 1`, with
`h = (2 - e)/2`, `r = 2h - ·` on `[h, 1]`, `(F_h)` holds, and `(P_h)` holds for `k ≥ 3`, and for
`k = 2` when `e ≤ 2/3`. -/
theorem cor84e {e : ℝ} (he0 : 0 < e) (he1 : e < 1) {k : ℕ} (hk : 3 ≤ k ∨ (k = 2 ∧ e ≤ 2 / 3)) :
    let r := fun z : ℝ => min 1 (2 - e - |z|)
    let h := (2 - e) / 2
    1 / 2 ≤ h ∧ h < 1 ∧ CondF r h ∧ CondP r h k := by
  intro r h
  have hh : 1 / 2 ≤ h := by simp only [h]; linarith
  have hh1 : h < 1 := by simp only [h]; linarith
  have haff : ∀ a ∈ Icc h 1, r a = 1 * (2 * h - a) := by
    intro a ha
    simp only [h] at ha
    have ha0 : 0 ≤ a := by linarith [ha.1]
    simp only [r, abs_of_nonneg ha0, h]
    rw [min_eq_right (by linarith [ha.1, he0])]; ring
  have hconc : ConcaveOn ℝ (Icc 0 1) r := by
    have h2 : ConcaveOn ℝ (Icc (0:ℝ) 1) fun z => (2 - e) + (-1 : ℝ) • z :=
      (concaveOn_const _ (convex_Icc 0 1)).add
        (LinearMap.concaveOn (LinearMap.lsmul ℝ ℝ (-1)) (convex_Icc 0 1) |>.congr
          fun x _ => by simp)
    have := (concaveOn_const (1:ℝ) (convex_Icc 0 1)).inf h2
    refine this.congr fun z hz => ?_
    simp only [r, abs_of_nonneg hz.1, Pi.inf_apply, smul_eq_mul]
    show min 1 _ = min 1 _
    congr 1; ring
  refine ⟨hh, hh1, (condF_of_affine hconc hh hh1 haff).2,
    condP_of_affine hh hh1 zero_le_one ?_ haff⟩
  rcases hk with hk | ⟨hk, he⟩
  · exact Or.inl hk
  · exact Or.inr ⟨hk, by simp only [h]; linarith⟩

end Cor84

end Scaled

end Mixes
