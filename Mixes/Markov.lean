import Mixes.Masking
import Mixes.Ball
import Mixes.Large

/-!
# Markov joint mixes (Section 24): Lemma 119, Corollary 122, Proposition 123

This file formalises parts of Section 24 of the paper (`mk:sec:markov`).

* `Mixes.etv`: the total variation distance `sup_A |μ A - ν A|` over measurable sets `A`, with
  values in `ℝ≥0∞` (defined for all measures). `etv_toReal` shows that for finite measures it is
  the real-valued `Mixes.tv` of `Mixes.Masking`, which this file imports.
  (Mathlib's `MeasureTheory.etvDist` is the total variation norm of `μ - ν`, which is twice this
  for probability measures; the paper does not fix a normalisation, and both conventions give the
  same inequalities.)
* `etv_map_le`: total variation does not increase under measurable maps.
* `etv_comp_le`: convexity of total variation, `TV(μ ∘ k, μ ∘ k') ≤ ∫ TV(k x, k' x) dμ`.
* `etv_compProd_eq`: two distributions of pairs with the same first marginal `μ` are at the total
  variation that is the average of the total variations of their conditional distributions:
  `TV(μ ⊗ k, μ ⊗ k') = ∫ TV(k x, k' x) dμ`, for Markov kernels on a countably generated space.
* `prop_price`, `prop_price_affine`, `prop_price_tv`: Proposition 123 (`mk:prop:price`).
* `cor_ball_polygon`, `cor_ball_polygon_max`, `cor_ball_subball`, `cor_ball_step`,
  `cor_ball_iterate`, `cor_ball_central`: the elementary parts of Corollary 122 (`mk:cor:ball`):
  the polygon inequality for the radii and the geometry of the Doeblin argument.
* `doeblin_unique`, `doeblin_minorization`, `doeblin_unique_of_bounds`, `invariant_map_eq`:
  Doeblin's condition and uniqueness of the invariant law, for general Markov kernels;
  `ball_step_bound`, `ball_central_bound`, `cor_ball_unique`, `cor_ball_symm`: for the kernels
  `k_ρ` of Corollary 122, at most one invariant law, and it is invariant under the orthogonal
  maps (the kernel, a measurable object, is a hypothesis there).
* Krylov–Bogolyubov for Feller kernels: `cesaro_limit_invariant`, `exists_invariant_of_feller`.
* Theorem 120 (`mk:thm:markov`): `markov_stationary` (the core of (b)), `thm120_a`, `thm120_b`,
  with the measurable selection theorem stated as the hypothesis `BorelSelection`; the chain is
  described by its step kernel (`IsMarkovStep`) and the laws `kpow P t ∘ₘ β₀`.
* Corollary 122 in full: `ballKernel` (the kernel `k_ρ`, Feller and with mean `ρ y`),
  `cor_ball_invariant` (existence, uniqueness and orthogonal invariance of the invariant law),
  `ballStep`, `cor_ball` (a Markov step kernel and a stationary joint mix for `n ≥ 2/(1-ρ)`,
  in `EuclideanSpace ℝ (Fin d)`; the step uses the measurable map of Theorem 51, so no selection
  hypothesis is needed).
* Theorem 121 (`mk:thm:bounded-markov`): `thm121_a` (the conditioned step is a joint mix with a
  small correction `φ`, Theorem 113 taken as a hypothesis), `thm121_b` (a stationary joint mix
  when the step kernel is weakly continuous, which is a hypothesis).
* `pexider_step`, `lem_mean_global`: Lemma 119 (`mk:lem:mean`) when the identity
  `∑ m_j(x_j) = s` holds everywhere on the whole hyperplane, for Borel measurable `m_j`.
* `lem_mean`: Lemma 119 in the paper's local, almost-everywhere form, for bounded Borel `m_j`
  (mollification `moll_identity`, the smooth case `core_affine`, the limit `affine_limit`, the
  last coordinate `transfer_last`); `lem_mean_markov`: the same from the data of a Markov joint
  mix (the law of `X(t)` with a density positive on `U`, the conditional law of `X(t+1)`).

No path measure of the Markov chain is constructed: Theorems 120 and 121 work with the step
kernel and its powers, and Proposition 123 and Lemma 119 take as hypotheses the
facts about the chain that their proofs use (the law `g ⊗ k` of the pair `(Y_j(t-1), Y_j(t))`,
the conditional law of `X(t+1)` given `X(t)`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Mixes

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Total variation -/

/-- The total variation distance `sup_A |μ A - ν A|`, the supremum over measurable sets `A`
(with truncated subtraction in `ℝ≥0∞`, the maximum of the two differences is `|μ A - ν A|`
when both values are finite). -/
def etv (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ (A : Set α) (_ : MeasurableSet A), max (μ A - ν A) (ν A - μ A)

lemma etv_comm (μ ν : Measure α) : etv μ ν = etv ν μ := by
  simp only [etv, max_comm]

lemma etv_le_iff {μ ν : Measure α} {c : ℝ≥0∞} :
    etv μ ν ≤ c ↔ ∀ A, MeasurableSet A → μ A - ν A ≤ c ∧ ν A - μ A ≤ c := by
  simp only [etv, iSup_le_iff, max_le_iff]

lemma le_etv {μ ν : Measure α} {A : Set α} (hA : MeasurableSet A) :
    μ A - ν A ≤ etv μ ν :=
  le_trans (le_max_left _ _) (le_iSup₂ (f := fun A (_ : MeasurableSet A) =>
    max (μ A - ν A) (ν A - μ A)) A hA)

lemma max_tsub_toReal {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (max (a - b) (b - a)).toReal = |a.toReal - b.toReal| := by
  rcases le_total b a with h | h
  · rw [tsub_eq_zero_of_le h, max_eq_left (by simp), ENNReal.toReal_sub_of_le h ha,
      abs_of_nonneg (sub_nonneg.2 ((ENNReal.toReal_le_toReal hb ha).2 h))]
  · rw [tsub_eq_zero_of_le h, max_eq_right (by simp), ENNReal.toReal_sub_of_le h hb,
      abs_of_nonpos (sub_nonpos.2 ((ENNReal.toReal_le_toReal ha hb).2 h)), neg_sub]

/-- **The two total variations agree.** For finite measures, the `ℝ≥0∞`-valued `etv` of this
file is the real-valued `tv` of `Mixes.Masking`. -/
theorem etv_toReal (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (etv μ ν).toReal = tv μ ν := by
  rw [etv, iSup_subtype', tv, ENNReal.toReal_iSup]
  · congr with A
    rw [max_tsub_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    rfl
  · intro A
    exact (max_lt (lt_of_le_of_lt tsub_le_self (measure_lt_top _ _))
      (lt_of_le_of_lt tsub_le_self (measure_lt_top _ _))).ne

lemma etv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : etv μ ν ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨measure_ne_top μ Set.univ,
    measure_ne_top ν Set.univ⟩) ?_
  rw [etv_le_iff]
  intro A _
  exact ⟨tsub_le_self.trans ((measure_mono (Set.subset_univ A)).trans le_self_add),
    tsub_le_self.trans ((measure_mono (Set.subset_univ A)).trans le_add_self)⟩

lemma etv_eq_ofReal (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etv μ ν = ENNReal.ofReal (tv μ ν) := by
  rw [← etv_toReal, ENNReal.ofReal_toReal (etv_ne_top μ ν)]

/-- Total variation does not increase under measurable maps (data processing). -/
lemma etv_map_le {μ ν : Measure α} {f : α → β} (hf : Measurable f) :
    etv (μ.map f) (ν.map f) ≤ etv μ ν := by
  rw [etv_le_iff]
  intro A hA
  rw [Measure.map_apply hf hA, Measure.map_apply hf hA]
  exact ⟨le_etv (hf hA), by rw [etv_comm]; exact le_etv (hf hA)⟩

/-- Total variation is invariant under a measurable map with a measurable left inverse. -/
lemma etv_map_eq {μ ν : Measure α} {f : α → β} {g : β → α} (hf : Measurable f)
    (hg : Measurable g) (hgf : ∀ x, g (f x) = x) :
    etv (μ.map f) (ν.map f) = etv μ ν := by
  refine le_antisymm (etv_map_le hf) ?_
  have h : ∀ ξ : Measure α, (ξ.map f).map g = ξ := fun ξ => by
    rw [Measure.map_map hg hf]
    have : g ∘ f = id := funext hgf
    rw [this, Measure.map_id]
  calc etv μ ν = etv ((μ.map f).map g) ((ν.map f).map g) := by rw [h, h]
    _ ≤ _ := etv_map_le hg

/-- Convexity of total variation: `TV(μ ∘ k, μ ∘ k') ≤ ∫ TV(k x, k' x) dμ(x)`. -/
theorem etv_comp_le (μ : Measure α) (k k' : Kernel α β) :
    etv (k ∘ₘ μ) (k' ∘ₘ μ) ≤ ∫⁻ x, etv (k x) (k' x) ∂μ := by
  have key : ∀ (k k' : Kernel α β) (A : Set α → Set β) (A : Set β), MeasurableSet A →
      (k ∘ₘ μ) A - (k' ∘ₘ μ) A ≤ ∫⁻ x, etv (k x) (k' x) ∂μ := by
    intro k k' _ A hA
    rw [Measure.bind_apply hA (Kernel.aemeasurable _),
      Measure.bind_apply hA (Kernel.aemeasurable _), tsub_le_iff_right]
    calc ∫⁻ x, k x A ∂μ ≤ ∫⁻ x, ((k x A - k' x A) + k' x A) ∂μ :=
          lintegral_mono fun x => le_tsub_add
      _ = ∫⁻ x, (k x A - k' x A) ∂μ + ∫⁻ x, k' x A ∂μ :=
          lintegral_add_right _ (Kernel.measurable_coe _ hA)
      _ ≤ _ := by
          gcongr with x
          exact le_etv hA
  rw [etv_le_iff]
  intro A hA
  refine ⟨key k k' (fun _ => ∅) A hA, ?_⟩
  have := key k' k (fun _ => ∅) A hA
  simpa only [etv_comm] using this

/-! ### Total variation of measures with densities -/

section Density

variable {m : Measure α} {F G : α → ℝ≥0∞}

lemma withDensity_sub_le (hG : Measurable G) {A : Set α} (hA : MeasurableSet A) :
    m.withDensity F A - m.withDensity G A ≤ ∫⁻ x, (F x - G x) ∂m := by
  rw [withDensity_apply _ hA, withDensity_apply _ hA, tsub_le_iff_right]
  calc ∫⁻ x in A, F x ∂m ≤ ∫⁻ x in A, ((F x - G x) + G x) ∂m :=
        lintegral_mono fun x => le_tsub_add
    _ = ∫⁻ x in A, (F x - G x) ∂m + ∫⁻ x in A, G x ∂m := lintegral_add_right _ hG
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

lemma withDensity_sub_eq (hF : Measurable F) (hG : Measurable G) (hGfin : ∫⁻ x, G x ∂m ≠ ∞) :
    m.withDensity F {x | G x < F x} - m.withDensity G {x | G x < F x} =
      ∫⁻ x, (F x - G x) ∂m := by
  set A := {x | G x < F x}
  have hA : MeasurableSet A := measurableSet_lt hG hF
  rw [withDensity_apply _ hA, withDensity_apply _ hA]
  have h1 : ∫⁻ x in A, F x ∂m = ∫⁻ x in A, (F x - G x) ∂m + ∫⁻ x in A, G x ∂m := by
    rw [← lintegral_add_right _ hG]
    refine setLIntegral_congr_fun hA fun x hx => ?_
    exact (tsub_add_cancel_of_le (le_of_lt hx)).symm
  have h2 : ∫⁻ x in A, G x ∂m ≠ ∞ :=
    ne_top_of_le_ne_top hGfin (setLIntegral_le_lintegral _ _)
  rw [h1, ENNReal.add_sub_cancel_right h2]
  refine setLIntegral_eq_of_support_subset fun x hx => ?_
  simpa [A, Function.mem_support, tsub_eq_zero_iff_le, not_le] using hx

/-- For finite measures with densities, the total variation is the larger of the integrals of
the positive and of the negative part of the difference of the densities. -/
lemma etv_withDensity (hF : Measurable F) (hG : Measurable G) (hFfin : ∫⁻ x, F x ∂m ≠ ∞)
    (hGfin : ∫⁻ x, G x ∂m ≠ ∞) :
    etv (m.withDensity F) (m.withDensity G) =
      max (∫⁻ x, (F x - G x) ∂m) (∫⁻ x, (G x - F x) ∂m) := by
  refine le_antisymm ?_ ?_
  · rw [etv_le_iff]
    intro A hA
    exact ⟨(withDensity_sub_le hG hA).trans (le_max_left _ _),
      (withDensity_sub_le hF hA).trans (le_max_right _ _)⟩
  · refine max_le ?_ ?_
    · rw [← withDensity_sub_eq hF hG hGfin]
      exact le_etv (measurableSet_lt hG hF)
    · rw [← withDensity_sub_eq hG hF hFfin, etv_comm]
      exact le_etv (measurableSet_lt hF hG)

/-- With equal finite total masses, the positive and negative parts have equal integrals. -/
lemma lintegral_tsub_eq_of_lintegral_eq (hF : Measurable F) (hG : Measurable G)
    (hfin : ∫⁻ x, F x ∂m ≠ ∞) (heq : ∫⁻ x, F x ∂m = ∫⁻ x, G x ∂m) :
    ∫⁻ x, (F x - G x) ∂m = ∫⁻ x, (G x - F x) ∂m := by
  have hmin : Measurable fun x => min (F x) (G x) := hF.min hG
  have e1 : ∫⁻ x, F x ∂m = ∫⁻ x, (F x - G x) ∂m + ∫⁻ x, min (F x) (G x) ∂m := by
    rw [← lintegral_add_right _ hmin]
    exact lintegral_congr fun x => (tsub_add_min).symm
  have e2 : ∫⁻ x, G x ∂m = ∫⁻ x, (G x - F x) ∂m + ∫⁻ x, min (F x) (G x) ∂m := by
    rw [← lintegral_add_right _ hmin]
    exact lintegral_congr fun x => by rw [min_comm]; exact (tsub_add_min).symm
  have hminfin : ∫⁻ x, min (F x) (G x) ∂m ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun x => min_le_left _ _)
  rw [e1, e2] at heq
  exact (ENNReal.add_left_inj hminfin).mp heq

/-- For probability densities, `TV = ∫ (F - G)⁺`. -/
lemma etv_withDensity_of_lintegral_eq_one (hF : Measurable F) (hG : Measurable G)
    (hF1 : ∫⁻ x, F x ∂m = 1) (hG1 : ∫⁻ x, G x ∂m = 1) :
    etv (m.withDensity F) (m.withDensity G) = ∫⁻ x, (F x - G x) ∂m := by
  rw [etv_withDensity hF hG (by simp [hF1]) (by simp [hG1]),
    lintegral_tsub_eq_of_lintegral_eq hF hG (by simp [hF1]) (by rw [hF1, hG1]), max_self]

end Density

/-! ### Distributions of pairs with the same first marginal -/

lemma compProd_eq_withDensity (μ : Measure α) [SFinite μ] (η : Kernel α β) [IsSFiniteKernel η]
    (k : Kernel α β) [IsSFiniteKernel k] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hk : ∀ x, k x = (η x).withDensity (f x)) :
    μ ⊗ₘ k = (μ ⊗ₘ η).withDensity (fun p => f p.1 p.2) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
    Measure.lintegral_compProd]
  · congr with a
    rw [hk, withDensity_apply' _ _, ← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

/-- The density form of `etv_compProd_eq`: conditional distributions `k x`, `k' x` with jointly
measurable densities `f x`, `g x` with respect to a reference kernel `η`. -/
theorem etv_compProd_eq_of_density (μ : Measure α) [IsProbabilityMeasure μ]
    (η : Kernel α β) [IsSFiniteKernel η] (k k' : Kernel α β) [IsMarkovKernel k]
    [IsMarkovKernel k'] {f g : α → β → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) (hk : ∀ x, k x = (η x).withDensity (f x))
    (hk' : ∀ x, k' x = (η x).withDensity (g x)) :
    etv (μ ⊗ₘ k) (μ ⊗ₘ k') = ∫⁻ x, etv (k x) (k' x) ∂μ := by
  have hf1 : ∀ x, ∫⁻ z, f x z ∂η x = 1 := fun x => by
    have := measure_univ (μ := k x)
    rwa [hk, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hg1 : ∀ x, ∫⁻ z, g x z ∂η x = 1 := fun x => by
    have := measure_univ (μ := k' x)
    rwa [hk', withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hfx : ∀ x, Measurable (f x) := fun x => hf.comp measurable_prodMk_left
  have hgx : ∀ x, Measurable (g x) := fun x => hg.comp measurable_prodMk_left
  have hF : Measurable fun p : α × β => f p.1 p.2 := hf
  have hG : Measurable fun p : α × β => g p.1 p.2 := hg
  have hFG : Measurable fun p : α × β => f p.1 p.2 - g p.1 p.2 := hF.sub hG
  have hF1 : ∫⁻ p, f p.1 p.2 ∂(μ ⊗ₘ η) = 1 := by
    rw [Measure.lintegral_compProd hF]; simp [hf1]
  have hG1 : ∫⁻ p, g p.1 p.2 ∂(μ ⊗ₘ η) = 1 := by
    rw [Measure.lintegral_compProd hG]; simp [hg1]
  rw [compProd_eq_withDensity μ η k hf hk, compProd_eq_withDensity μ η k' hg hk',
    etv_withDensity_of_lintegral_eq_one hF hG hF1 hG1,
    Measure.lintegral_compProd hFG]
  congr with x
  rw [hk, hk', etv_withDensity_of_lintegral_eq_one (hfx x) (hgx x) (hf1 x) (hg1 x)]

/-- **Total variation of pairs with a common first marginal.** Two distributions of pairs with
the same first marginal `μ` and conditional distributions `k x`, `k' x` are at the total
variation that is the average of the total variations of the conditional distributions. -/
theorem etv_compProd_eq [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsProbabilityMeasure μ] (k k' : Kernel α β) [IsMarkovKernel k]
    [IsMarkovKernel k'] :
    etv (μ ⊗ₘ k) (μ ⊗ₘ k') = ∫⁻ x, etv (k x) (k' x) ∂μ := by
  set η := k + k'
  have hac : ∀ x, k x ≪ η x := fun x => by
    simp only [η, add_apply]
    exact Measure.AbsolutelyContinuous.rfl.add_right _
  have hac' : ∀ x, k' x ≪ η x := fun x => by
    simp only [η, add_apply]
    rw [add_comm]
    exact Measure.AbsolutelyContinuous.rfl.add_right _
  have hk : ∀ x, k x = (η x).withDensity (k.rnDeriv η x) := fun x => by
    rw [← Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv k η)]
    exact (Kernel.withDensity_rnDeriv_eq (hac x)).symm
  have hk' : ∀ x, k' x = (η x).withDensity (k'.rnDeriv η x) := fun x => by
    rw [← Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv k' η)]
    exact (Kernel.withDensity_rnDeriv_eq (hac' x)).symm
  exact etv_compProd_eq_of_density μ η k k' (f := k.rnDeriv η) (g := k'.rnDeriv η)
    (Kernel.measurable_rnDeriv k η) (Kernel.measurable_rnDeriv k' η) hk hk'

/-! ### Proposition 123 -/

section Price

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- **Proposition 123** (`mk:prop:price`), for one coordinate `j`.

The law of `Y_j(t-1)` is `g`, and `Y_j(t)` given `Y_j(t-1) = y` has the law `k y`, so the pair
`(Y_j(t-1), Y_j(t))` has the law `g ⊗ k`. The masked data `Z = x + Y` and `Z' = x' + Y` have laws
`Q`, `Q'` on any space `Ω` of paths over an interval of times, and the projection `π` to the pair
`(Z_j(t-1), Z_j(t))` maps them to the translates of `g ⊗ k` by `(a, b)` and by `(a, b')`, where
`a = x_j(t-1) = x'_j(t-1)`, `b = x_j(t)` and `b' = x'_j(t)`, so `δ_j = b' - b`. Then
`TV(Z, Z') ≥ ∫ TV(k y, k y (· - δ)) dg(y) ≥ TV(ḡ, ḡ(· - δ))` with `ḡ = g ∘ k`; the measure
`E ↦ ν (E - δ)` is the image `ν.map (· + δ)`. -/
theorem prop_price [MeasurableSpace.CountablyGenerated E] {Ω : Type*} [MeasurableSpace Ω]
    (g : Measure E) [IsProbabilityMeasure g] (k : Kernel E E) [IsMarkovKernel k] (a b b' : E)
    (Q Q' : Measure Ω) (π : Ω → E × E) (hπ : Measurable π)
    (hQ : Q.map π = (g ⊗ₘ k).map (fun p => (a + p.1, b + p.2)))
    (hQ' : Q'.map π = (g ⊗ₘ k).map (fun p => (a + p.1, b' + p.2))) :
    ∫⁻ y, etv (k y) ((k y).map (· + (b' - b))) ∂g ≤ etv Q Q' ∧
      etv (k ∘ₘ g) ((k ∘ₘ g).map (· + (b' - b))) ≤
        ∫⁻ y, etv (k y) ((k y).map (· + (b' - b))) ∂g := by
  set δ := b' - b
  have hh : Measurable fun z : E => z + δ := measurable_add_const δ
  have : IsMarkovKernel (k.map fun z => z + δ) := Kernel.IsMarkovKernel.map k hh
  have hφ : Measurable fun p : E × E => (a + p.1, b + p.2) :=
    ((measurable_const_add a).comp measurable_fst).prodMk
      ((measurable_const_add b).comp measurable_snd)
  have hφinv : Measurable fun p : E × E => (-a + p.1, -b + p.2) :=
    ((measurable_const_add (-a)).comp measurable_fst).prodMk
      ((measurable_const_add (-b)).comp measurable_snd)
  have hψ : Measurable (Prod.map (id : E → E) fun z : E => z + δ) := measurable_id.prodMap hh
  have hcomp : (fun p : E × E => (a + p.1, b' + p.2)) =
      (fun p : E × E => (a + p.1, b + p.2)) ∘ Prod.map (id : E → E) fun z : E => z + δ := by
    funext p
    simp only [Function.comp, Prod.map, id, δ]
    congr 1
    abel
  refine ⟨?_, ?_⟩
  · calc ∫⁻ y, etv (k y) ((k y).map (· + δ)) ∂g
        = ∫⁻ y, etv (k y) ((k.map fun z => z + δ) y) ∂g := by
          congr with y
          rw [Kernel.map_apply _ hh]
      _ = etv (g ⊗ₘ k) (g ⊗ₘ (k.map fun z => z + δ)) := (etv_compProd_eq g _ _).symm
      _ = etv ((g ⊗ₘ k).map fun p => (a + p.1, b + p.2))
            (((g ⊗ₘ k).map (Prod.map (id : E → E) fun z : E => z + δ)).map
              fun p => (a + p.1, b + p.2)) := by
          rw [Measure.compProd_map hh, etv_map_eq hφ hφinv]
          intro p
          simp
      _ = etv (Q.map π) (Q'.map π) := by
          rw [hQ, hQ', hcomp, Measure.map_map hφ hψ]
      _ ≤ etv Q Q' := etv_map_le hπ
  · calc etv (k ∘ₘ g) ((k ∘ₘ g).map (· + δ))
        = etv (k ∘ₘ g) ((k.map fun z => z + δ) ∘ₘ g) := by rw [Measure.map_comp _ _ hh]
      _ ≤ ∫⁻ y, etv (k y) ((k.map fun z => z + δ) y) ∂g := etv_comp_le g _ _
      _ = ∫⁻ y, etv (k y) ((k y).map (· + δ)) ∂g := by
          congr with y
          rw [Kernel.map_apply _ hh]

/-- Proposition 123, the outer inequality, for the real-valued `tv` of
`Mixes.Masking` (for probability measures `Q`, `Q'`):
`TV(ḡ, ḡ(· - δ)) ≤ TV(Z, Z')`. -/
theorem prop_price_tv [MeasurableSpace.CountablyGenerated E] {Ω : Type*} [MeasurableSpace Ω]
    (g : Measure E) [IsProbabilityMeasure g] (k : Kernel E E) [IsMarkovKernel k] (a b b' : E)
    (Q Q' : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (π : Ω → E × E)
    (hπ : Measurable π)
    (hQ : Q.map π = (g ⊗ₘ k).map (fun p => (a + p.1, b + p.2)))
    (hQ' : Q'.map π = (g ⊗ₘ k).map (fun p => (a + p.1, b' + p.2))) :
    tv (k ∘ₘ g) ((k ∘ₘ g).map (· + (b' - b))) ≤ tv Q Q' := by
  have h := prop_price g k a b b' Q Q' π hπ hQ hQ'
  rw [← etv_toReal, ← etv_toReal]
  exact ENNReal.toReal_mono (etv_ne_top _ _) (h.2.trans h.1)

end Price

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The last claim of Proposition 123: if `k y` is the law of `ρ y + (1 - ρ) V` with `V ∼ q`, then
`TV(k y, k y (· - δ)) = TV(q, q(· - δ/(1 - ρ)))`, as both are images of `q` and of its translate
under one affine bijection. -/
theorem etv_affine_kernel (q : Measure E) {ρ : ℝ} (hρ : ρ < 1) (y δ : E) :
    etv (q.map fun v => ρ • y + (1 - ρ) • v) ((q.map fun v => ρ • y + (1 - ρ) • v).map (· + δ)) =
      etv q (q.map (· + (1 - ρ)⁻¹ • δ)) := by
  have h1 : (1 - ρ) ≠ 0 := by linarith
  have hφ : Measurable fun v : E => ρ • y + (1 - ρ) • v := by fun_prop
  have hψ : Measurable fun w : E => (1 - ρ)⁻¹ • (w - ρ • y) := by fun_prop
  have hh : Measurable fun z : E => z + δ := measurable_add_const δ
  have hh' : Measurable fun z : E => z + (1 - ρ)⁻¹ • δ := measurable_add_const _
  have hcomm : ((fun z : E => z + δ) ∘ fun v => ρ • y + (1 - ρ) • v) =
      (fun v => ρ • y + (1 - ρ) • v) ∘ fun z : E => z + (1 - ρ)⁻¹ • δ := by
    funext v
    simp only [Function.comp, smul_add, smul_smul, mul_inv_cancel₀ h1, one_smul]
    abel
  rw [Measure.map_map hh hφ, hcomm, ← Measure.map_map hφ hh', etv_map_eq hφ hψ]
  intro v
  simp [smul_smul, inv_mul_cancel₀ h1]

/-- Proposition 123 for the kernels `k y = law of ρ y + (1 - ρ) V`, `V ∼ q`: the middle term is
`TV(q, q(· - δ/(1 - ρ)))`. -/
theorem prop_price_affine [MeasurableSpace.CountablyGenerated E] {Ω : Type*} [MeasurableSpace Ω]
    (g : Measure E) [IsProbabilityMeasure g] (q : Measure E) [IsProbabilityMeasure q]
    {ρ : ℝ} (hρ : ρ < 1) (k : Kernel E E) [IsMarkovKernel k]
    (hk : ∀ y, k y = q.map fun v => ρ • y + (1 - ρ) • v) (a b b' : E)
    (Q Q' : Measure Ω) (π : Ω → E × E) (hπ : Measurable π)
    (hQ : Q.map π = (g ⊗ₘ k).map (fun p => (a + p.1, b + p.2)))
    (hQ' : Q'.map π = (g ⊗ₘ k).map (fun p => (a + p.1, b' + p.2))) :
    etv q (q.map (· + (1 - ρ)⁻¹ • (b' - b))) ≤ etv Q Q' ∧
      etv (k ∘ₘ g) ((k ∘ₘ g).map (· + (b' - b))) ≤ etv q (q.map (· + (1 - ρ)⁻¹ • (b' - b))) := by
  have hmid : ∫⁻ y, etv (k y) ((k y).map (· + (b' - b))) ∂g =
      etv q (q.map (· + (1 - ρ)⁻¹ • (b' - b))) := by
    simp_rw [hk, etv_affine_kernel q hρ]
    simp
  rw [← hmid]
  exact prop_price g k a b b' Q Q' π hπ hQ hQ'

end Affine

/-! ### Corollary 122: the elementary parts -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The radii `1 - ρ|y|` of the balls of Corollary 122 lie in `[1 - ρ, 1]`. -/
lemma ball_radius_mem {ρ : ℝ} (hρ0 : 0 ≤ ρ) {y : E} (hy : ‖y‖ ≤ 1) :
    1 - ρ ≤ 1 - ρ * ‖y‖ ∧ 1 - ρ * ‖y‖ ≤ 1 :=
  ⟨by nlinarith [norm_nonneg y], by nlinarith [norm_nonneg y]⟩

/-- **Corollary 122, the polygon inequality.** For `0 ≤ ρ < 1`, `n ≥ 2/(1 - ρ)` and points
`x_j` of the unit ball, the radii `λ_j = 1 - ρ|x_j|` satisfy `2 λ_i ≤ ∑ λ_j` for every `i`
(including `ρ = 0`, `n ≥ 2`, and the equality case `n = 2/(1 - ρ)`), and the centres `ρ x_j`
add up to `0` when the `x_j` do. -/
theorem cor_ball_polygon {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (hn : 2 / (1 - ρ) ≤ n)
    (x : Fin n → E) (hx : ∀ j, ‖x j‖ ≤ 1) :
    (∀ i, 2 * (1 - ρ * ‖x i‖) ≤ ∑ j, (1 - ρ * ‖x j‖)) ∧
      (∑ j, x j = 0 → ∑ j, ρ • x j = 0) := by
  refine ⟨fun i => ?_, fun h => by rw [← Finset.smul_sum, h, smul_zero]⟩
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 2 ≤ (n : ℝ) * (1 - ρ) := by rwa [div_le_iff₀ h1] at hn
  have h3 : (n : ℝ) * (1 - ρ) ≤ ∑ j, (1 - ρ * ‖x j‖) := by
    calc (n : ℝ) * (1 - ρ) = ∑ _j : Fin n, (1 - ρ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => (ball_radius_mem hρ0 (hx j)).1
  have h4 := (ball_radius_mem hρ0 (hx i)).2
  linarith

/-- The polygon inequality in the form `2 max_j λ_j ≤ ∑_j λ_j`. -/
theorem cor_ball_polygon_max {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (hpos : 0 < n)
    (hn : 2 / (1 - ρ) ≤ n) (x : Fin n → E) (hx : ∀ j, ‖x j‖ ≤ 1) :
    2 * (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hpos⟩⟩)
      fun j => 1 - ρ * ‖x j‖) ≤ ∑ j, (1 - ρ * ‖x j‖) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hpos⟩⟩)
    fun j => 1 - ρ * ‖x j‖
  rw [hi]
  exact (cor_ball_polygon hρ0 hρ1 hn x hx).1 i

/-- **Corollary 122, the sub-ball of the Doeblin argument.** Let `0 ≤ ρ < 1`, `η = (1 - ρ)/2`,
`|y| ≤ 1`, and let `c` be the point of the ray through `y` at distance
`r₀ = max(0, 2ρ|y| - 1 + η)` from `0`. Then `c` lies on the segment from `ρ y` to `0`, the ball
`B(c, η)` lies in `B(ρ y, 1 - ρ|y|)`, and its points have norm at most `max(η, 2ρ|y| - ρ)`. -/
theorem cor_ball_subball {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {y : E} (hy : ‖y‖ ≤ 1) :
    let η := (1 - ρ) / 2
    let r₀ := max 0 (2 * ρ * ‖y‖ - 1 + η)
    let c := (r₀ / ‖y‖) • y
    ‖c‖ = r₀ ∧ r₀ ≤ ρ * ‖y‖ ∧ ‖c - ρ • y‖ = ρ * ‖y‖ - r₀ ∧
      Metric.closedBall c η ⊆ Metric.closedBall (ρ • y) (1 - ρ * ‖y‖) ∧
      ∀ z ∈ Metric.closedBall c η, ‖z‖ ≤ max η (2 * ρ * ‖y‖ - ρ) := by
  intro η r₀ c
  have hN := norm_nonneg y
  have hr0 : 0 ≤ r₀ := le_max_left _ _
  have hr0le : r₀ ≤ ρ * ‖y‖ := by
    refine max_le (by positivity) ?_
    simp only [η]; nlinarith
  have hc : ‖c‖ = r₀ ∧ ‖c - ρ • y‖ = ρ * ‖y‖ - r₀ := by
    rcases eq_or_lt_of_le hN with h0 | hpos
    · have hy0 : y = 0 := norm_eq_zero.mp h0.symm
      have : r₀ = 0 := by
        simp only [r₀, η, hy0, norm_zero, mul_zero]
        exact max_eq_left (by linarith)
      simp [c, hy0, this]
    · constructor
      · simp only [c, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hr0, abs_norm]
        field_simp
      · have : c - ρ • y = (r₀ / ‖y‖ - ρ) • y := by simp only [c, sub_smul]
        rw [this, norm_smul, Real.norm_eq_abs, ← abs_norm, ← abs_mul, abs_norm]
        rw [sub_mul, div_mul_cancel₀ _ hpos.ne', abs_of_nonpos (by linarith)]
        ring
  refine ⟨hc.1, hr0le, hc.2, ?_, ?_⟩
  · refine Metric.closedBall_subset_closedBall' ?_
    rw [dist_eq_norm, hc.2]
    have : 2 * ρ * ‖y‖ - 1 + η ≤ r₀ := le_max_right _ _
    linarith
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hz' : ‖z‖ ≤ r₀ + η := by
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ η + r₀ := by rw [hc.1]; linarith
        _ = r₀ + η := add_comm _ _
    refine hz'.trans ?_
    simp only [r₀, η]
    rcases le_total 0 (2 * ρ * ‖y‖ - 1 + (1 - ρ) / 2) with h | h
    · rw [max_eq_right h]; exact le_max_of_le_right (by linarith)
    · rw [max_eq_left h]; exact le_max_of_le_left (by linarith)

/-- The norm bound of the sub-ball moves towards `0` by `θ = min(ρ, 1 - ρ)`:
`max(η, 2ρ|y| - ρ) ≤ max(η, |y| - θ)` for `|y| ≤ 1`. -/
lemma cor_ball_step {ρ η t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    max η (2 * ρ * t - ρ) ≤ max η (t - min ρ (1 - ρ)) := by
  refine max_le_max le_rfl ?_
  rcases le_total ρ (1 - ρ) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- After `m = ⌈1/θ⌉` steps that each move a bound `≤ 1` to `max(η, · - θ)`, the bound is at
most `η`. -/
lemma cor_ball_iterate {θ η : ℝ} (hθ : 0 < θ) (hη : 0 ≤ η) (u : ℕ → ℝ) (h0 : u 0 ≤ 1)
    (hstep : ∀ i, u (i + 1) ≤ max η (u i - θ)) : u ⌈1 / θ⌉₊ ≤ η := by
  have key : ∀ i : ℕ, u i ≤ max η (1 - i * θ) := by
    intro i
    induction i with
    | zero => simpa using le_max_of_le_right h0
    | succ i ih =>
      refine (hstep i).trans (max_le (le_max_left _ _) ?_)
      have : u i - θ ≤ max η (1 - i * θ) - θ := by linarith
      refine this.trans ?_
      rcases le_total η (1 - i * θ) with h | h
      · rw [max_eq_right h]; push_cast; exact le_max_of_le_right (by linarith)
      · rw [max_eq_left h]; exact le_max_of_le_left (by linarith)
  refine (key _).trans (max_le le_rfl ?_)
  have : 1 / θ ≤ ⌈1 / θ⌉₊ := Nat.le_ceil _
  rw [div_le_iff₀ hθ] at this
  linarith

/-- **Corollary 122, the central ball.** For `|y| ≤ η = (1 - ρ)/2`,
`(3/4) B ⊆ (1 - 2ρη) B ⊆ B(ρ y, 1 - ρ|y|)`. -/
theorem cor_ball_central {ρ : ℝ} (hρ0 : 0 ≤ ρ) {y : E}
    (hy : ‖y‖ ≤ (1 - ρ) / 2) :
    Metric.closedBall (0 : E) (3 / 4) ⊆ Metric.closedBall 0 (1 - 2 * ρ * ((1 - ρ) / 2)) ∧
      Metric.closedBall (0 : E) (1 - 2 * ρ * ((1 - ρ) / 2)) ⊆
        Metric.closedBall (ρ • y) (1 - ρ * ‖y‖) := by
  refine ⟨Metric.closedBall_subset_closedBall (by nlinarith [sq_nonneg (ρ - 1 / 2)]), ?_⟩
  refine Metric.closedBall_subset_closedBall' ?_
  rw [dist_comm, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ0]
  nlinarith [norm_nonneg y]

end Ball

/-! ### Lemma 119: the case of the whole hyperplane -/

section Mean

variable {E : Type*} [AddCommGroup E] {n : ℕ}

/-- Two tuples that agree off two indices. -/
lemma sum_eq_of_agree (f : Fin n → E → E) {j l : Fin n} (hjl : j ≠ l)
    (x y : Fin n → E) (hxy : ∀ k, k ≠ j → k ≠ l → x k = y k) :
    ∑ k, f k (x k) - ∑ k, f k (y k) =
      (f j (x j) + f l (x l)) - (f j (y j) + f l (y l)) := by
  have hl : l ∈ (Finset.univ : Finset (Fin n)).erase j := Finset.mem_erase.mpr ⟨hjl.symm, by simp⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ hl,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ hl]
  have : ∑ k ∈ ((Finset.univ.erase j).erase l), f k (x k) =
      ∑ k ∈ ((Finset.univ.erase j).erase l), f k (y k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_erase] at hk
    rw [hxy k hk.2.1 hk.1]
  rw [this]
  abel

/-- The Pexider step: for distinct `j`, `l`, if `∑ m_k(x_k) = s` for every tuple with sum `s`,
then `m_j(a + u) + m_l(b) = m_j(a) + m_l(b + u)` (here `n ≥ 3` supplies a third index). -/
lemma pexider_step (hn : 3 ≤ n) (m : Fin n → E → E) (s : E)
    (h : ∀ x : Fin n → E, ∑ j, x j = s → ∑ j, m j (x j) = s) {j l : Fin n} (hjl : j ≠ l)
    (a b u : E) : m j (a + u) + m l b = m j a + m l (b + u) := by
  classical
  obtain ⟨i, hi⟩ : ((Finset.univ.erase j).erase l).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (by simp [hjl.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  simp only [Finset.mem_erase] at hi
  have hij : i ≠ j := hi.2.1
  have hil : i ≠ l := hi.1
  set w := s - a - b - u
  let x : Fin n → E := Pi.single j (a + u) + Pi.single l b + Pi.single i w
  let y : Fin n → E := Pi.single j a + Pi.single l (b + u) + Pi.single i w
  have hx : ∑ k, x k = s := by
    simp only [x, Finset.sum_add_distrib, Pi.add_apply, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, w]
    abel
  have hy : ∑ k, y k = s := by
    simp only [y, Finset.sum_add_distrib, Pi.add_apply, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, w]
    abel
  have hagree : ∀ k, k ≠ j → k ≠ l → x k = y k := by
    intro k hkj hkl
    simp [x, y, Pi.single_apply, hkj, hkl]
  have := sum_eq_of_agree m hjl x y hagree
  rw [h x hx, h y hy, sub_self] at this
  have hxj : x j = a + u := by simp [x, hjl, hij.symm]
  have hxl : x l = b := by simp [x, hjl.symm, hil.symm]
  have hyj : y j = a := by simp [y, hjl, hij.symm]
  have hyl : y l = b + u := by simp [y, hjl.symm, hil.symm]
  rw [hxj, hxl, hyj, hyl] at this
  exact (sub_eq_zero.mp this.symm)

end Mean

section MeanGlobal

variable {E : Type*} {n : ℕ}

/-- **Lemma 119** (`mk:lem:mean`) in the case where the identity `∑_j m_j(x_j) = s` holds for
every tuple of the hyperplane `∑_j x_j = s` (the case `U` = the whole hyperplane, with the identity
everywhere rather than almost everywhere), for Borel measurable maps `m_j` on a finite-dimensional
real normed space and `n ≥ 3`: there are a linear map `Γ` and vectors `c_j` with
`Γ s + ∑_j c_j = s` and `m_j(y) = Γ y + c_j` for all `j` and `y`. -/
theorem lem_mean_global [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hn : 3 ≤ n) (m : Fin n → E → E)
    (hm : ∀ j, Measurable (m j)) (s : E)
    (h : ∀ x : Fin n → E, ∑ j, x j = s → ∑ j, m j (x j) = s) :
    ∃ Γ : E →L[ℝ] E, ∃ c : Fin n → E, Γ s + ∑ j, c j = s ∧ ∀ j y, m j y = Γ y + c j := by
  have h0 : 0 < n := by omega
  set j₀ : Fin n := ⟨0, h0⟩
  -- `D_j(u) = m_j(u) - m_j(0)` is the same for all `j`, and additive.
  have hD : ∀ j l, ∀ u, m j u - m j 0 = m l u - m l 0 := by
    intro j l u
    by_cases hjl : j = l
    · rw [hjl]
    · have := pexider_step hn m s h hjl 0 0 u
      simp only [zero_add] at this
      rw [sub_eq_sub_iff_add_eq_add, this, add_comm]
  have hadd : ∀ a u, m j₀ (a + u) - m j₀ 0 = (m j₀ a - m j₀ 0) + (m j₀ u - m j₀ 0) := by
    intro a u
    obtain ⟨l, hl⟩ : ∃ l : Fin n, l ≠ j₀ := ⟨⟨1, by omega⟩, by simp [j₀, Fin.ext_iff]⟩
    have := pexider_step hn m s h hl.symm a 0 u
    rw [zero_add] at this
    rw [hD j₀ l u]
    have e : m j₀ (a + u) = m j₀ a + m l u - m l 0 := by rw [← this]; abel
    rw [e]; abel
  let D : E →+ E := AddMonoidHom.mk' (fun u => m j₀ u - m j₀ 0) hadd
  have hDc : Continuous D :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable D ((hm j₀).sub measurable_const)
  let Γ : E →L[ℝ] E := D.toRealLinearMap hDc
  have hΓ : ∀ j y, m j y = Γ y + m j 0 := by
    intro j y
    have e : Γ y = m j₀ y - m j₀ 0 := rfl
    rw [e, hD j₀ j y]; abel
  refine ⟨Γ, fun j => m j 0, ?_, hΓ⟩
  have hx : ∑ k, (Pi.single j₀ s : Fin n → E) k = s := by simp
  have := h _ hx
  rw [Finset.sum_congr rfl fun k _ => hΓ k _, Finset.sum_add_distrib, ← map_sum, hx] at this
  exact this

end MeanGlobal


/-! ### Lemma 119: the local, almost-everywhere version

The proof follows the paper: mollify, use the identity everywhere for the smooth functions
(their derivatives agree, by moving two coordinates in opposite directions, and are locally
constant, hence constant on the convex set), and pass to the limit with the Lebesgue
differentiation theorem. -/

section MeanCore

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A function with zero derivative on an open convex set is constant there. -/
lemma eq_of_hasFDerivAt_zero {O : Set X} (hO : IsOpen O) (hc : Convex ℝ O) {f : X → F}
    (hf : ∀ z ∈ O, HasFDerivAt f (0 : X →L[ℝ] F) z) {a b : X} (ha : a ∈ O) (hb : b ∈ O) :
    f a = f b :=
  hc.is_const_of_fderivWithin_eq_zero
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [fderivWithin_of_isOpen hO hz, (hf z hz).fderiv]) ha hb

/-- A function that is locally constant on an open set has zero derivative there. -/
lemma hasFDerivAt_zero_of_eventually {f : X → F} {z : X} (h : ∀ᶠ z' in nhds z, f z' = f z) :
    HasFDerivAt f (0 : X →L[ℝ] F) z :=
  (hasFDerivAt_const (f z) z).congr_of_eventuallyEq h

end MeanCore

section MeanCoreFin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

lemma sum_apply_single_sub (L : Fin m → E →L[ℝ] E) {j l : Fin m} (hjl : j ≠ l) (v : E) :
    ∑ k, L k ((Pi.single j v : Fin m → E) k - (Pi.single l v : Fin m → E) k) = L j v - L l v := by
  rw [Finset.sum_eq_add (s := Finset.univ) j l hjl (fun k _ hk => by
    simp [hk.1, hk.2]) (by simp) (by simp)]
  simp [hjl, hjl.symm, sub_eq_add_neg]

/-- **The smooth case.** If `∑_k M_k(z_k) = G(∑_k z_k)` on an open convex set `O` of tuples,
`m ≥ 2` and the `M_k` are differentiable, then the `M_k` are affine on `O` with a common linear
part. -/
lemma core_affine (hm : 2 ≤ m) (M : Fin m → E → E) (hM : ∀ k, Differentiable ℝ (M k))
    {O : Set (Fin m → E)} (hO : IsOpen O) (hOc : Convex ℝ O) (G : E → E)
    (h : ∀ z ∈ O, ∑ k, M k (z k) = G (∑ k, z k)) :
    ∃ Γ : E →L[ℝ] E, ∃ c : Fin m → E, ∀ k, ∀ z ∈ O, M k (z k) = Γ (z k) + c k := by
  rcases O.eq_empty_or_nonempty with hO0 | ⟨z0, hz0⟩
  · exact ⟨0, 0, fun k z hz => by simp [hO0] at hz⟩
  -- (a) the derivatives at the coordinates of a point of `O` agree
  have ha : ∀ z ∈ O, ∀ j l, fderiv ℝ (M j) (z j) = fderiv ℝ (M l) (z l) := by
    intro z hz j l
    by_cases hjl : j = l
    · rw [hjl]
    ext v
    set d : Fin m → E := Pi.single j v - Pi.single l v
    set g : ℝ → E := fun t => ∑ k, M k (z k + t • d k)
    have hg : HasDerivAt g (∑ k, fderiv ℝ (M k) (z k) (d k)) 0 := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have h1 : HasDerivAt (fun t : ℝ => z k + t • d k) (d k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (d k)).const_add (z k)
      have h2 := ((hM k) (z k + (0 : ℝ) • d k)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
      simp only [zero_smul, add_zero] at h2
      exact h2
    have hev : ∀ᶠ t in nhds (0 : ℝ), g t = g 0 := by
      have hcont : Continuous fun t : ℝ => z + t • d := by fun_prop
      have : ∀ᶠ t in nhds (0 : ℝ), z + t • d ∈ O :=
        hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hz)
      filter_upwards [this] with t ht
      have e1 := h _ ht
      have e2 := h z hz
      have hsum : ∑ k, (z + t • d) k = ∑ k, z k := by
        simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, d,
          Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true,
          sub_self, smul_zero, add_zero]
      simp only [g, zero_smul, add_zero]
      simp only [Pi.add_apply, Pi.smul_apply] at e1 hsum
      rw [e1, e2, hsum]
    have h0 : HasDerivAt g 0 0 := (hasDerivAt_const (0 : ℝ) (g 0)).congr_of_eventuallyEq hev
    have := hg.unique h0
    have h3 := sum_apply_single_sub (fun k => fderiv ℝ (M k) (z k)) hjl v
    simp only [d, Pi.sub_apply] at this
    rw [h3] at this
    exact sub_eq_zero.mp this
  obtain ⟨j0, l0, hjl0⟩ : ∃ j l : Fin m, j ≠ l :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  -- (b) each derivative is constant on `O`
  have hb : ∀ l, ∀ z ∈ O, fderiv ℝ (M l) (z l) = fderiv ℝ (M l) (z0 l) := by
    intro l z hz
    obtain ⟨j, hjl⟩ : ∃ j, j ≠ l := by
      by_cases h : j0 = l
      · exact ⟨l0, fun h' => hjl0 (h.trans h'.symm)⟩
      · exact ⟨j0, h⟩
    refine eq_of_hasFDerivAt_zero (f := fun z : Fin m → E => fderiv ℝ (M l) (z l)) hO hOc
      (fun z hz => hasFDerivAt_zero_of_eventually ?_) hz hz0
    -- the hybrid point `update z l (z' l)` stays in `O` near `z`
    have hcont : Continuous fun z' : Fin m → E => Function.update z l (z' l) := by fun_prop
    have : ∀ᶠ z' in nhds z, Function.update z l (z' l) ∈ O :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hz)
    filter_upwards [this] with z' hz'
    have e1 := ha _ hz' l j
    have e2 := ha z hz l j
    simp only [Function.update_self, Function.update_of_ne hjl] at e1
    rw [e1, ← e2]
  set Γ := fderiv ℝ (M j0) (z0 j0)
  have hΓ : ∀ l, ∀ z ∈ O, fderiv ℝ (M l) (z l) = Γ := fun l z hz => by
    rw [hb l z hz, ha z0 hz0 l j0]
  -- (c) `M_l - Γ` is constant on `O`
  refine ⟨Γ, fun l => M l (z0 l) - Γ (z0 l), fun l z hz => ?_⟩
  have := eq_of_hasFDerivAt_zero (f := fun z : Fin m → E => M l (z l) - Γ (z l)) hO hOc
    (fun z hz => ?_) hz hz0
  · simp only; rw [← this]; abel
  · have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => E) l z
    have h2 := ((hM l) (z l)).hasFDerivAt.comp z h1
    have h3 := (Γ.hasFDerivAt.comp z h1)
    have h4 := h2.sub h3
    rw [hΓ l z hz, sub_self] at h4
    exact h4

end MeanCoreFin


section MeanMoll

open scoped Convolution

/-- Products of absolutely continuous measures are absolutely continuous. -/
lemma pi_absolutelyContinuous {α : Type*} [MeasurableSpace α] (μ μ' : Measure α) [SigmaFinite μ]
    [SigmaFinite μ'] (h : μ ≪ μ') :
    ∀ m : ℕ, Measure.pi (fun _ : Fin m => μ) ≪ Measure.pi (fun _ : Fin m => μ')
  | 0 => by rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | m + 1 => by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) 0
    have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).map_eq
    have h2 := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ') 0).map_eq
    have hpi : ∀ (ξ : Measure (Fin (m + 1) → α)), ξ = (ξ.map e).map e.symm := fun ξ => by
      rw [Measure.map_map e.symm.measurable e.measurable]; simp
    rw [hpi (Measure.pi fun _ => μ), hpi (Measure.pi fun _ => μ'), h1, h2]
    exact (h.prod (pi_absolutelyContinuous μ μ' h m)).map e.symm.measurable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {m : ℕ}

lemma measurable_normed (ψ : ContDiffBump (0 : E)) : Measurable (ψ.normed volume) :=
  (ψ.contDiff_normed (n := 0)).continuous.measurable

/-- The probability measure with the density of a normed bump function. -/
def bumpMeasure (ψ : ContDiffBump (0 : E)) : Measure E :=
  volume.withDensity fun v => ENNReal.ofReal (ψ.normed volume v)

instance (ψ : ContDiffBump (0 : E)) : IsProbabilityMeasure (bumpMeasure ψ) := by
  constructor
  rw [bumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ψ.integrable_normed
      (Filter.Eventually.of_forall fun v => ψ.nonneg_normed v), ψ.integral_normed,
    ENNReal.ofReal_one]

lemma bumpMeasure_ae_norm_le (ψ : ContDiffBump (0 : E)) : ∀ᵐ v ∂bumpMeasure ψ, ‖v‖ ≤ ψ.rOut := by
  rw [bumpMeasure, ae_withDensity_iff (measurable_normed ψ).ennreal_ofReal]
  refine Filter.Eventually.of_forall fun v hv => ?_
  by_contra h
  apply hv
  have : v ∉ Function.support (ψ.normed volume) := by
    rw [ψ.support_normed_eq, Metric.mem_ball, dist_zero_right]; linarith
  rw [Function.notMem_support] at this
  simp [this]

lemma bumpMeasure_ac (ψ : ContDiffBump (0 : E)) : bumpMeasure ψ ≪ volume :=
  withDensity_absolutelyContinuous _ _

lemma integral_bumpMeasure (ψ : ContDiffBump (0 : E)) (g : E → E) :
    ∫ v, g v ∂bumpMeasure ψ = ∫ v, ψ.normed volume v • g v := by
  rw [bumpMeasure]
  have : (fun v => ENNReal.ofReal (ψ.normed volume v)) =
      fun v => ((fun v => (ψ.normed volume v).toNNReal) v : ℝ≥0∞) := rfl
  rw [this, integral_withDensity_eq_integral_smul (measurable_normed ψ).real_toNNReal]
  congr with v
  rw [NNReal.smul_def, Real.coe_toNNReal _ (ψ.nonneg_normed v)]

/-- The mollified last coordinate: `R(y) = ∫ f(y + ∑ w) dν(w)`, `ν` the product of bump
measures. -/
def mollR (ψ : ContDiffBump (0 : E)) (f : E → E) (y : E) : E :=
  ∫ w, f (y + ∑ i, w i) ∂(Measure.pi fun _ : Fin m => bumpMeasure ψ)

/-- **The mollified identity.** If `∑_j m_j(x_j) = s` for almost every point of `W` (in the
coordinates `z` of the hyperplane), then everywhere on the points of `W` at distance more than
the radius of the bump from its complement, the mollified functions satisfy the identity. -/
lemma moll_identity (mf : Fin (m + 1) → E → E) (hmeas : ∀ j, Measurable (mf j)) {C : ℝ}
    (hC : ∀ j y, ‖mf j y‖ ≤ C) (s : E) {W : Set (Fin m → E)}
    (hW : ∀ᵐ z ∂(volume : Measure (Fin m → E)), z ∈ W → ∑ j, mf j (hypEmb s z j) = s)
    (ψ : ContDiffBump (0 : E)) {z : Fin m → E} (hz : Metric.closedBall z ψ.rOut ⊆ W) :
    ∑ k : Fin m, (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      mf (Fin.castSucc k)) (z k) + mollR (m := m) ψ (mf (Fin.last m)) (s - ∑ k, z k) = s := by
  set ρ := bumpMeasure ψ
  set ν := Measure.pi fun _ : Fin m => ρ
  have hac : ν ≪ (volume : Measure (Fin m → E)) := by
    rw [volume_pi]; exact pi_absolutelyContinuous _ _ (bumpMeasure_ac ψ) m
  have h1 : ∀ᵐ w ∂ν, ∀ k, ‖w k‖ ≤ ψ.rOut := ae_all_iff.2 fun k =>
    (measurePreserving_eval (fun _ : Fin m => ρ) k).quasiMeasurePreserving.ae
      (bumpMeasure_ae_norm_le ψ)
  have h2 : ∀ᵐ w ∂ν, z - w ∈ W → ∑ j, mf j (hypEmb s (z - w) j) = s :=
    hac.ae_le ((Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hW)
  have hF : ∀ᵐ w ∂ν, ∑ k, mf (Fin.castSucc k) (z k - w k) +
      mf (Fin.last m) ((s - ∑ k, z k) + ∑ i, w i) = s := by
    filter_upwards [h1, h2] with w hw1 hw2
    have hzw : z - w ∈ W := by
      apply hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact (pi_norm_le_iff_of_nonneg ψ.rOut_pos.le).2 hw1
    have := hw2 hzw
    rw [Fin.sum_univ_castSucc] at this
    simp only [hypEmb, Fin.snoc_castSucc, Fin.snoc_last, Pi.sub_apply,
      Finset.sum_sub_distrib] at this
    have e : s - (∑ k, z k - ∑ k, w k) = (s - ∑ k, z k) + ∑ i, w i := by abel
    rwa [e] at this
  have hint : ∀ (g : E → E), Measurable g → (∀ y, ‖g y‖ ≤ C) → ∀ (q : (Fin m → E) → E),
      Measurable q → Integrable (fun w => g (q w)) ν := fun g hg hgC q hq =>
    Integrable.of_bound (hg.comp hq).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun w => hgC _)
  have i1 : ∀ k, Integrable (fun w : Fin m → E => mf (Fin.castSucc k) (z k - w k)) ν :=
    fun k => hint _ (hmeas _) (hC _) (fun w => z k - w k)
      (measurable_const.sub (measurable_pi_apply k))
  have i2 : Integrable (fun w : Fin m → E => mf (Fin.last m) ((s - ∑ k, z k) + ∑ i, w i)) ν :=
    hint _ (hmeas _) (hC _) (fun w => (s - ∑ k, z k) + ∑ i, w i)
      (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
  calc _ = ∫ w, (∑ k, mf (Fin.castSucc k) (z k - w k) +
        mf (Fin.last m) ((s - ∑ k, z k) + ∑ i, w i)) ∂ν := by
        rw [integral_add (integrable_finsetSum _ fun k _ => i1 k) i2,
          integral_finsetSum _ fun k _ => i1 k]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_comp_eval (μ := fun _ : Fin m => ρ) (f := fun v => mf (Fin.castSucc k)
          (z k - v)) ((hmeas _).comp (measurable_const.sub measurable_id)).aestronglyMeasurable,
          integral_bumpMeasure]
        rfl
    _ = ∫ _w, s ∂ν := integral_congr_ae hF
    _ = s := by simp

end MeanMoll


section MeanLimit

open scoped Convolution Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {m : ℕ}

lemma locallyIntegrable_of_bdd {g : E → E} (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    LocallyIntegrable g volume := fun x =>
  ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos,
    Measure.integrableOn_of_bounded measure_ball_lt_top.ne hg.aestronglyMeasurable
      (ae_of_all _ fun y => hC y)⟩

lemma differentiable_moll (ψ : ContDiffBump (0 : E)) {g : E → E} (hg : Measurable g) {C : ℝ}
    (hC : ∀ y, ‖g y‖ ≤ C) :
    Differentiable ℝ (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
  (ψ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (ψ.contDiff_normed (n := 1)) (locallyIntegrable_of_bdd hg hC)).differentiable one_ne_zero

/-- Preimages of null sets under a coordinate projection are null. -/
lemma volume_eval_preimage_null {N : Set E} (hN : volume N = 0) (k : Fin m) :
    volume ((fun z : Fin m → E => z k) ⁻¹' N) = 0 := by
  classical
  have : (fun z : Fin m → E => z k) ⁻¹' N =
      Set.univ.pi (Function.update (fun _ => Set.univ) k N) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hz i
      by_cases hik : i = k
      · subst hik; simpa using hz
      · simp [Function.update_of_ne hik]
    · intro hz; simpa using hz k
  rw [this, volume_pi, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simpa using hN)

lemma ae_comp_eval {P : E → Prop} (h : ∀ᵐ y ∂(volume : Measure E), P y) (k : Fin m) :
    ∀ᵐ z ∂(volume : Measure (Fin m → E)), P (z k) := by
  rw [ae_iff] at h ⊢
  exact volume_eval_preimage_null h k

/-- The points whose closed `r`-ball lies in `W`, made open. -/
def inner (W : Set (Fin m → E)) (r : ℝ) : Set (Fin m → E) :=
  interior {z | Metric.closedBall z r ⊆ W}

lemma convex_inner {W : Set (Fin m → E)} (hW : Convex ℝ W) (r : ℝ) : Convex ℝ (inner W r) := by
  refine Convex.interior ?_
  intro z1 hz1 z2 hz2 a b ha hb hab p hp
  simp only [Set.mem_ofPred_eq] at hz1 hz2
  set c := a • z1 + b • z2
  have e : p = a • (z1 + (p - c)) + b • (z2 + (p - c)) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
    simp [c]
  have h1 : z1 + (p - c) ∈ W := hz1 (by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ← dist_eq_norm]; exact hp)
  have h2 : z2 + (p - c) ∈ W := hz2 (by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ← dist_eq_norm]; exact hp)
  rw [e]; exact hW h1 h2 ha hb hab

lemma inner_mono {W : Set (Fin m → E)} {r r' : ℝ} (h : r' ≤ r) : inner W r ⊆ inner W r' :=
  interior_mono fun _ hz => (Metric.closedBall_subset_closedBall h).trans hz

lemma inner_subset {W : Set (Fin m → E)} {r : ℝ} {z : Fin m → E} (hz : z ∈ inner W r) :
    Metric.closedBall z r ⊆ W := interior_subset hz

lemma exists_mem_inner {W : Set (Fin m → E)} (hW : IsOpen W) {z : Fin m → E} (hz : z ∈ W)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) : ∃ N, ∀ N' ≥ N, z ∈ inner W (r N') := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW z hz
  obtain ⟨N, hN⟩ := (hr.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
  refine ⟨N, fun N' hN' => ?_⟩
  refine mem_interior.2 ⟨Metric.ball z (ε / 2), fun z' hz' => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos hε)⟩
  intro p hp
  apply hball
  rw [Metric.mem_ball] at hz' ⊢
  rw [Metric.mem_closedBall] at hp
  have := hN N' hN'
  linarith [dist_triangle p z' z]

/-- **Limits of affine maps.** If `Γ_N y + c_N` converges to `f y` for almost every `y` in a
ball, then `Γ_N` converges pointwise to a linear map and `c_N` converges. -/
lemma affine_limit (Γs : ℕ → E →L[ℝ] E) (cs : ℕ → E) (f : E → E) {a : E} {δ : ℝ} (hδ : 0 < δ)
    (hconv : ∀ᵐ y ∂volume, y ∈ Metric.ball a δ →
      Tendsto (fun N => Γs N y + cs N) atTop (𝓝 (f y))) :
    ∃ Γ : E →L[ℝ] E, ∃ c : E, (∀ u, Tendsto (fun N => Γs N u) atTop (𝓝 (Γ u))) ∧
      Tendsto cs atTop (𝓝 c) := by
  set G := {y | y ∈ Metric.ball a δ → Tendsto (fun N => Γs N y + cs N) atTop (𝓝 (f y))}
  have hG : volume Gᶜ = 0 := hconv
  -- a good point `y` with `y + u` good, for small `u`
  have hsmall : ∀ u : E, ‖u‖ < δ / 2 → ∃ L, Tendsto (fun N => Γs N u) atTop (𝓝 L) := by
    intro u hu
    have hne : (Metric.ball a (δ / 2) ∩ G ∩ (fun y => y + u) ⁻¹' G).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hsub : Metric.ball a (δ / 2) ⊆ Gᶜ ∪ (fun y => y + u) ⁻¹' Gᶜ := by
        intro y hy
        by_contra h'
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, not_or, not_not] at h'
        have : y ∈ Metric.ball a (δ / 2) ∩ G ∩ (fun y => y + u) ⁻¹' G := ⟨⟨hy, h'.1⟩, h'.2⟩
        rw [hcon] at this; exact this
      have h0 : volume (Metric.ball a (δ / 2)) = 0 := measure_mono_null hsub
        (measure_union_null hG (by rw [measure_preimage_add_right]; exact hG))
      exact (Metric.measure_ball_pos volume a (half_pos hδ)).ne' h0
    obtain ⟨y, ⟨hy, hyG⟩, hyuG⟩ := hne
    have hyb : y ∈ Metric.ball a δ := Metric.ball_subset_ball (by linarith) hy
    have hyub : y + u ∈ Metric.ball a δ := by
      rw [Metric.mem_ball] at hy ⊢
      calc dist (y + u) a ≤ dist (y + u) y + dist y a := dist_triangle _ _ _
        _ < δ := by rw [dist_eq_norm, add_sub_cancel_left]; linarith
    refine ⟨f (y + u) - f y, ?_⟩
    have := (hyuG hyub).sub (hyG hyb)
    refine this.congr fun N => ?_
    simp only [map_add]; abel
  have hall : ∀ u : E, ∃ L, Tendsto (fun N => Γs N u) atTop (𝓝 L) := by
    intro u
    set t : ℝ := δ / (4 * (‖u‖ + 1))
    have ht : 0 < t := by positivity
    have htu : ‖t • u‖ < δ / 2 := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      have h1 : t * ‖u‖ ≤ δ / 4 := by
        simp only [t]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [norm_nonneg u]
      linarith
    obtain ⟨L, hL⟩ := hsmall _ htu
    refine ⟨t⁻¹ • L, (hL.const_smul t⁻¹).congr fun N => ?_⟩
    rw [map_smul, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  choose Lim hLim using hall
  let Γl : E →ₗ[ℝ] E :=
    { toFun := Lim
      map_add' := fun u v => tendsto_nhds_unique (hLim (u + v))
        (((hLim u).add (hLim v)).congr fun N => (map_add _ _ _).symm)
      map_smul' := fun r u => tendsto_nhds_unique (hLim (r • u))
        (((hLim u).const_smul r).congr fun N => (map_smul _ _ _).symm) }
  set Γ := LinearMap.toContinuousLinearMap Γl
  have hΓ : ∀ u, Tendsto (fun N => Γs N u) atTop (𝓝 (Γ u)) := hLim
  -- a good point for the constants
  obtain ⟨y, hyb, hyG⟩ : (Metric.ball a δ ∩ G).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : Metric.ball a δ ⊆ Gᶜ := fun y hy hyG => by
      have : y ∈ Metric.ball a δ ∩ G := ⟨hy, hyG⟩
      rw [hcon] at this; exact this
    exact (Metric.measure_ball_pos volume a hδ).ne' (measure_mono_null hsub hG)
  refine ⟨Γ, f y - Γ y, hΓ, ((hyG hyb).sub (hΓ y)).congr fun N => ?_⟩
  simp


/-- The linear involution `z ↦ update z k₀ (-∑ z)`. -/
def tauL (k0 : Fin m) : (Fin m → E) →ₗ[ℝ] (Fin m → E) :=
  LinearMap.id - (LinearMap.single ℝ (fun _ : Fin m => E) k0).comp
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => E) k0 +
      ∑ i : Fin m, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => E) i)

lemma tauL_apply (k0 : Fin m) (z : Fin m → E) :
    tauL k0 z = z - Pi.single k0 (z k0 + ∑ i, z i) := by
  simp [tauL]

lemma sum_tauL (k0 : Fin m) (z : Fin m → E) : ∑ i, tauL k0 z i = -z k0 := by
  rw [tauL_apply]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  abel

lemma tauL_tauL (k0 : Fin m) (z : Fin m → E) : tauL k0 (tauL k0 z) = z := by
  rw [tauL_apply (z := tauL k0 z), sum_tauL, tauL_apply]
  simp only [Pi.sub_apply, Pi.single_eq_same]
  rw [sub_sub, ← Pi.single_add]
  simp

/-- **Transfer to the last coordinate.** If a property holds at `s - ∑ z` for almost every `z`
of an open set `W`, it holds almost everywhere on the image of `W` under `z ↦ s - ∑ z`. -/
lemma transfer_last (hm : 1 ≤ m) {W : Set (Fin m → E)} (hWo : IsOpen W) (s : E) {P : E → Prop}
    (h : ∀ᵐ z ∂(volume : Measure (Fin m → E)), z ∈ W → P (s - ∑ i, z i)) :
    ∀ᵐ y ∂(volume : Measure E), y ∈ (fun z : Fin m → E => s - ∑ i, z i) '' W → P y := by
  classical
  set k0 : Fin m := ⟨0, hm⟩
  set Nset := {z : Fin m → E | z ∈ W ∧ ¬ P (s - ∑ i, z i)}
  have hN : volume Nset = 0 := by
    rw [ae_iff] at h
    convert h using 2
    simp [Nset]
  set τ : (Fin m → E) → (Fin m → E) := fun z => tauL k0 z + Pi.single k0 s
  have hτN : volume (τ ⁻¹' Nset) = 0 := by
    let e : (Fin m → E) ≃ₗ[ℝ] (Fin m → E) :=
      LinearEquiv.ofInvolutive (tauL k0) (fun z => tauL_tauL k0 z)
    have : τ ⁻¹' Nset = e.toContinuousLinearEquiv ⁻¹' ((· + Pi.single k0 s) ⁻¹' Nset) := rfl
    rw [this, Measure.addHaar_preimage_continuousLinearEquiv, measure_preimage_add_right, hN,
      mul_zero]
  have hτsum : ∀ z, s - ∑ i, τ z i = z k0 := fun z => by
    simp only [τ, Pi.add_apply, Finset.sum_add_distrib, sum_tauL, Finset.sum_pi_single',
      Finset.mem_univ, ite_true]
    abel
  have hτk : ∀ z k, k ≠ k0 → τ z k = z k := fun z k hk => by
    simp [τ, tauL_apply, hk]
  have hτk0 : ∀ z, τ z k0 = s - ∑ i, z i := fun z => by
    simp only [τ, tauL_apply, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
    abel
  set B := {y | y ∈ (fun z : Fin m → E => s - ∑ i, z i) '' W ∧ ¬ P y}
  suffices hB : volume B = 0 by
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hB
    simp only [Set.mem_ofPred_eq, not_imp] at hy
    exact hy
  refine measure_null_of_locally_null B fun y0 hy0 => ?_
  obtain ⟨⟨z', hz'W, hz'y⟩, -⟩ := hy0
  have hz'y : s - ∑ i, z' i = y0 := hz'y
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hWo z' hz'W
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set η := δ / m
  have hη : 0 < η := div_pos hδ hm'
  refine ⟨B ∩ Metric.ball y0 η, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hη), ?_⟩
  set Q := Set.univ.pi (Function.update (fun k => Metric.ball (z' k) η) k0 (B ∩ Metric.ball y0 η))
  have hQ : Q ⊆ τ ⁻¹' Nset := by
    intro q hq
    simp only [Q, Set.mem_pi, Set.mem_univ, true_implies] at hq
    have hq0 : q k0 ∈ B ∩ Metric.ball y0 η := by simpa using hq k0
    have hqk : ∀ k, k ≠ k0 → q k ∈ Metric.ball (z' k) η := fun k hk => by
      simpa [Function.update_of_ne hk] using hq k
    refine ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_pi_lt_iff hδ]
      intro k
      by_cases hk : k = k0
      · subst hk
        rw [hτk0, dist_eq_norm]
        have e : s - ∑ i, q i - z' k0 = (y0 - q k0) + ∑ i ∈ {k0}ᶜ, (z' i - q i) := by
          rw [← hz'y, Fintype.sum_eq_add_sum_compl k0 q, Fintype.sum_eq_add_sum_compl k0 z',
            Finset.sum_sub_distrib]
          abel
        rw [e]
        have h1 : ‖y0 - q k0‖ < η := by
          rw [← dist_eq_norm, dist_comm]; exact hq0.2
        have h2 : ∑ i ∈ ({k0}ᶜ : Finset (Fin m)), ‖z' i - q i‖ ≤
            ∑ i ∈ ({k0}ᶜ : Finset (Fin m)), η := Finset.sum_le_sum fun i hi => by
          have := hqk i (by simpa using hi)
          rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
          exact this.le
        have h3 : ∑ i ∈ ({k0}ᶜ : Finset (Fin m)), η = ((m : ℝ) - 1) * η := by
          rw [Finset.sum_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_sub hm, Nat.cast_one]
        calc ‖y0 - q k0 + ∑ i ∈ {k0}ᶜ, (z' i - q i)‖
            ≤ ‖y0 - q k0‖ + ∑ i ∈ ({k0}ᶜ : Finset (Fin m)), ‖z' i - q i‖ :=
              (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
          _ < η + ((m : ℝ) - 1) * η := by linarith
          _ = δ := by simp only [η]; field_simp; ring
      · rw [hτk q k hk]
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact lt_of_lt_of_le (hqk k hk) (div_le_self hδ.le hm1)
    · rw [hτsum]; exact hq0.1.2
  have hQ0 : volume Q = 0 := measure_mono_null hQ hτN
  rw [volume_pi, Measure.pi_pi] at hQ0
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hQ0
  by_cases hk0 : k = k0
  · subst hk0; simpa using hk
  · rw [Function.update_of_ne hk0] at hk
    exact absurd hk (Metric.measure_ball_pos volume _ hη).ne'

end MeanLimit


section MeanMain

open scoped Convolution Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [SecondCountableTopology E] {m : ℕ}

@[simp] lemma hypEmb_castSucc (s : E) (z : Fin m → E) (k : Fin m) :
    hypEmb s z (Fin.castSucc k) = z k := by simp [hypEmb]

@[simp] lemma hypEmb_last (s : E) (z : Fin m → E) : hypEmb s z (Fin.last m) = s - ∑ i, z i := by
  simp [hypEmb]

lemma hypEmb_initL {s : E} {x : Fin (m + 1) → E} (hx : ∑ i, x i = s) : hypEmb s (initL x) = x := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [hypEmb_last, ← hx, Fin.sum_univ_castSucc]
    simp [initL]
  · simp [initL]

lemma hypEmb_affine (s : E) {a b : ℝ} (hab : a + b = 1) (z z' : Fin m → E) :
    hypEmb s (a • z + b • z') = a • hypEmb s z + b • hypEmb s z' := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [hypEmb_last, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib,
      ← Finset.smul_sum, smul_sub]
    have : s = a • s + b • s := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [this]
    abel
  · simp

lemma update_mem_ball (z : Fin m → E) (k : Fin m) {y : E} {δ : ℝ} (hδ : 0 < δ)
    (hy : y ∈ Metric.ball (z k) δ) : Function.update z k y ∈ Metric.ball z δ := by
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro i
  by_cases hik : i = k
  · subst hik; simpa using hy
  · simpa [Function.update_of_ne hik] using hδ

/-- **Lemma 119** (`mk:lem:mean`), the analytic core in the local, almost-everywhere form.
Let `n = m + 1 ≥ 3`, let `m_0, …, m_m : E → E` be bounded Borel functions (the conditional means
of kernels on bounded bodies), and let `U` be a nonempty convex subset of the hyperplane
`∑ x_j = s` that is open in it (its preimage under the parametrisation `hypEmb s` is open). If
`∑_j m_j(x_j) = s` for Lebesgue-almost every `x ∈ U` (Lebesgue measure `hypMeasure s` on the
hyperplane), then there are a linear map `Γ` and vectors `c_j` with `Γ s + ∑_j c_j = s` and,
for every `j`, `m_j(y) = Γ y + c_j` for almost every `y` in the projection `U_j` of `U`. -/
theorem lem_mean (hm : 2 ≤ m) (mf : Fin (m + 1) → E → E) (hmeas : ∀ j, Measurable (mf j))
    {C : ℝ} (hC : ∀ j y, ‖mf j y‖ ≤ C) (s : E) {U : Set (Fin (m + 1) → E)}
    (hUs : ∀ x ∈ U, ∑ i, x i = s) (hUo : IsOpen (hypEmb s ⁻¹' U)) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) (h : ∀ᵐ x ∂(hypMeasure s), x ∈ U → ∑ j, mf j (x j) = s) :
    ∃ Γ : E →L[ℝ] E, ∃ c : Fin (m + 1) → E, Γ s + ∑ j, c j = s ∧
      ∀ j, ∀ᵐ y ∂(volume : Measure E), y ∈ (fun x => x j) '' U → mf j y = Γ y + c j := by
  set W := hypEmb s ⁻¹' U
  have hWc : Convex ℝ W := fun z hz z' hz' a b ha hb hab => by
    show hypEmb s (a • z + b • z') ∈ U
    rw [hypEmb_affine s hab]; exact hUc hz hz' ha hb hab
  have hW0 : ∀ᵐ z ∂(volume : Measure (Fin m → E)), z ∈ W → ∑ j, mf j (hypEmb s z j) = s :=
    ae_of_ae_map (measurable_hypEmb s).aemeasurable h
  have hWmem : ∀ x ∈ U, initL x ∈ W := fun x hx => by
    show hypEmb s (initL x) ∈ U
    rw [hypEmb_initL (hUs x hx)]; exact hx
  -- the bump functions, of radii `2 / (N + 2)`
  let ψ : ℕ → ContDiffBump (0 : E) := fun N =>
    { rIn := 1 / ((N : ℝ) + 2), rOut := 2 / ((N : ℝ) + 2), rIn_pos := by positivity,
      rIn_lt_rOut := by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num }
  have hψr : Tendsto (fun N => (ψ N).rOut) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    refine this.congr fun N => ?_
    simp [ψ]
  have hψK : ∀ N, (ψ N).rOut ≤ 2 * (ψ N).rIn := fun N => le_of_eq (by simp [ψ]; ring)
  have hψmono : ∀ N0 N, N0 ≤ N → (ψ N).rOut ≤ (ψ N0).rOut := fun N0 N hN => by
    show 2 / ((N : ℝ) + 2) ≤ 2 / ((N0 : ℝ) + 2)
    gcongr
  set Mk : ℕ → Fin m → E → E := fun N k =>
    (ψ N).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mf (Fin.castSucc k)
  set O : ℕ → Set (Fin m → E) := fun N => inner W (ψ N).rOut
  -- the smooth case on each `O N`
  have hcore : ∀ N, ∃ Γ : E →L[ℝ] E, ∃ c : Fin m → E,
      ∀ k, ∀ z ∈ O N, Mk N k (z k) = Γ (z k) + c k := fun N =>
    core_affine hm (Mk N) (fun k => differentiable_moll (ψ N) (hmeas _) (hC _)) isOpen_interior
      (convex_inner hWc _) (fun σ => s - mollR (m := m) (ψ N) (mf (Fin.last m)) (s - σ))
      (fun z hz => eq_sub_of_add_eq (moll_identity mf hmeas hC s hW0 (ψ N) (inner_subset hz)))
  choose Γs cs hΓcs using hcore
  have hconv : ∀ᵐ y ∂(volume : Measure E), ∀ k,
      Tendsto (fun N => Mk N k y) atTop (𝓝 (mf (Fin.castSucc k) y)) :=
    ae_all_iff.2 fun k => ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hψr
      (Eventually.of_forall hψK) (locallyIntegrable_of_bdd (hmeas _) (hC _))
  -- a base point and a ball around it in `O N0`
  obtain ⟨x0, hx0⟩ := hUne
  obtain ⟨N0, hN0⟩ := exists_mem_inner hUo (hWmem x0 hx0) hψr
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.1 isOpen_interior _ (hN0 N0 le_rfl)
  have hloc : ∀ k, ∀ᵐ y ∂(volume : Measure E), y ∈ Metric.ball (initL x0 k) δ →
      Tendsto (fun N => Γs N y + cs N k) atTop (𝓝 (mf (Fin.castSucc k) y)) := by
    intro k
    filter_upwards [hconv] with y hy hyb
    refine (hy k).congr' ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hmem : Function.update (initL x0) k y ∈ O N :=
      inner_mono (hψmono N0 N hN) (hδball (update_mem_ball _ k hδ hyb))
    have := hΓcs N k _ hmem
    simpa using this
  have hlim : ∀ k, ∃ Γ : E →L[ℝ] E, ∃ c : E,
      (∀ u, Tendsto (fun N => Γs N u) atTop (𝓝 (Γ u))) ∧
        Tendsto (fun N => cs N k) atTop (𝓝 c) := fun k =>
    affine_limit Γs (fun N => cs N k) _ hδ (hloc k)
  choose Γk ck hΓk hck using hlim
  set Γ := Γk ⟨0, by omega⟩
  have hΓ : ∀ u, Tendsto (fun N => Γs N u) atTop (𝓝 (Γ u)) := hΓk _
  -- the first `m` coordinates
  have hfirst : ∀ k, ∀ᵐ y ∂(volume : Measure E), y ∈ (fun z : Fin m → E => z k) '' W →
      mf (Fin.castSucc k) y = Γ y + ck k := by
    intro k
    filter_upwards [hconv] with y hy hyW
    obtain ⟨z, hzW, rfl⟩ := hyW
    obtain ⟨N1, hN1⟩ := exists_mem_inner hUo hzW hψr
    refine tendsto_nhds_unique (hy k) (((hΓ (z k)).add (hck k)).congr' ?_)
    filter_upwards [eventually_ge_atTop N1] with N hN
    exact (hΓcs N k z (hN1 N hN)).symm
  -- the last coordinate
  set clast := s - Γ s - ∑ k, ck k
  have hlast0 : ∀ᵐ z ∂(volume : Measure (Fin m → E)), z ∈ W →
      mf (Fin.last m) (s - ∑ i, z i) = Γ (s - ∑ i, z i) + clast := by
    have hall : ∀ᵐ z ∂(volume : Measure (Fin m → E)), ∀ k, z ∈ W →
        mf (Fin.castSucc k) (z k) = Γ (z k) + ck k :=
      ae_all_iff.2 fun k => (ae_comp_eval (hfirst k) k).mono fun z hz hzW => hz ⟨z, hzW, rfl⟩
    filter_upwards [hW0, hall] with z hz1 hz2 hzW
    have e := hz1 hzW
    rw [Fin.sum_univ_castSucc] at e
    simp only [hypEmb_castSucc, hypEmb_last] at e
    rw [Finset.sum_congr rfl fun k _ => hz2 k hzW, Finset.sum_add_distrib, ← map_sum] at e
    have : mf (Fin.last m) (s - ∑ i, z i) = s - Γ (∑ i, z i) - ∑ k, ck k := by
      calc _ = (Γ (∑ i, z i) + ∑ k, ck k + mf (Fin.last m) (s - ∑ i, z i)) - Γ (∑ i, z i) -
            ∑ k, ck k := by abel
        _ = _ := by rw [e]
    rw [this, map_sub]
    simp only [clast]
    abel
  have hlast := transfer_last (P := fun y => mf (Fin.last m) y = Γ y + clast) (by omega) hUo s
    hlast0
  -- assembly
  refine ⟨Γ, Fin.snoc ck clast, ?_, fun j => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, clast]
    abel
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · filter_upwards [hlast] with y hy hyU
      obtain ⟨x, hxU, rfl⟩ := hyU
      simp only [Fin.snoc_last]
      apply hy
      refine ⟨initL x, hWmem x hxU, ?_⟩
      have := congrFun (hypEmb_initL (hUs x hxU)) (Fin.last m)
      rwa [hypEmb_last] at this
    · filter_upwards [hfirst k] with y hy hyU
      obtain ⟨x, hxU, rfl⟩ := hyU
      simp only [Fin.snoc_castSucc]
      exact hy ⟨initL x, hWmem x hxU, rfl⟩

/-- **Lemma 119** (`mk:lem:mean`) for a Markov joint mix. At a time `t`, the law of `X(t)` is
`λ.withDensity w` (with `λ = hypMeasure s`), with `w > 0` almost everywhere on `U`; given
`X(t) = x`, the law `κ x` of `X(t + 1)` is concentrated on the hyperplane of sum `s` and has the
marginals `k_j(x_j, ·)` (the defining property of a Markov joint mix). The means
`m_j(y) = ∫ z k_j(y, dz)` are bounded (as for kernels on bounded bodies `K_j`). Then the
conclusion of `lem_mean` holds for the `m_j`. -/
theorem lem_mean_markov (hm : 2 ≤ m) (k : Fin (m + 1) → Kernel E E)
    [∀ j, IsMarkovKernel (k j)] (hkint : ∀ j y, Integrable id (k j y)) {C : ℝ}
    (hkC : ∀ j y, ‖∫ z, z ∂(k j y)‖ ≤ C) (s : E) {U : Set (Fin (m + 1) → E)}
    (hUs : ∀ x ∈ U, ∑ i, x i = s) (hUo : IsOpen (hypEmb s ⁻¹' U)) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) {w : (Fin (m + 1) → E) → ℝ≥0∞} (hw : Measurable w)
    (hwpos : ∀ᵐ x ∂(hypMeasure s), x ∈ U → w x ≠ 0)
    (κ : Kernel (Fin (m + 1) → E) (Fin (m + 1) → E)) [IsMarkovKernel κ]
    (hmarg : ∀ᵐ x ∂((hypMeasure s).withDensity w), ∀ j, (κ x).map (fun y => y j) = k j (x j))
    (hsum : ∀ᵐ x ∂((hypMeasure s).withDensity w), ∀ᵐ y ∂(κ x), ∑ j, y j = s) :
    ∃ Γ : E →L[ℝ] E, ∃ c : Fin (m + 1) → E, Γ s + ∑ j, c j = s ∧
      ∀ j, ∀ᵐ y ∂(volume : Measure E), y ∈ (fun x => x j) '' U →
        ∫ z, z ∂(k j y) = Γ y + c j := by
  set mf : Fin (m + 1) → E → E := fun j y => ∫ z, z ∂(k j y)
  have hmeas : ∀ j, Measurable (mf j) := fun j =>
    (stronglyMeasurable_id.integral_kernel (κ := k j)).measurable
  -- the conditional means add up to `s` under the law of `X(t)`
  have hβ : ∀ᵐ x ∂((hypMeasure s).withDensity w), ∑ j, mf j (x j) = s := by
    filter_upwards [hmarg, hsum] with x hx1 hx2
    have hint : ∀ j, Integrable (fun y : Fin (m + 1) → E => y j) (κ x) := fun j => by
      have := hkint j (x j)
      rw [← hx1 j] at this
      exact (integrable_map_measure (f := fun y : Fin (m + 1) → E => y j) (g := id)
        aestronglyMeasurable_id (measurable_pi_apply j).aemeasurable).1 this
    have hmj : ∀ j, mf j (x j) = ∫ y, y j ∂(κ x) := fun j => by
      simp only [mf]
      rw [← hx1 j]
      exact integral_map (μ := κ x) (φ := fun y : Fin (m + 1) → E => y j) (f := fun z : E => z)
        (measurable_pi_apply j).aemeasurable aestronglyMeasurable_id
    simp_rw [hmj]
    rw [← integral_finsetSum _ fun j _ => hint j]
    rw [integral_congr_ae hx2]
    simp
  have h : ∀ᵐ x ∂(hypMeasure s), x ∈ U → ∑ j, mf j (x j) = s := by
    rw [ae_withDensity_iff hw] at hβ
    filter_upwards [hβ, hwpos] with x h1 h2 hxU
    exact h1 (h2 hxU)
  exact lem_mean hm mf hmeas hkC s hUs hUo hUc hUne h

end MeanMain


/-! ### Corollary 122: Doeblin's condition and the invariant law

`doeblin_unique`: a minorization `κ(x, ·) ≥ c ν` with `c > 0` for all `x` allows at most one
invariant probability measure (the contraction of the total variation by `1 - c`).
`doeblin_minorization`: the two one-step bounds of the paper give such a minorization for
`κ^{N+1}`, `N = ⌈1/θ⌉`. `invariant_map_eq`: a unique invariant law is invariant under every
measurable map that commutes with the kernel. -/

section Doeblin

variable {α : Type*} [MeasurableSpace α]

/-- `n` steps of a kernel: `kpow κ (n + 1) = κ ∘ₖ kpow κ n`. -/
def kpow (κ : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => κ ∘ₖ kpow κ n

instance isMarkovKernel_kpow (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => rw [kpow]; infer_instance
  | succ n ih => rw [kpow]; infer_instance

lemma kpow_comp_invariant (κ : Kernel α α) {π : Measure α} (hπ : κ ∘ₘ π = π) :
    ∀ n, kpow κ n ∘ₘ π = π
  | 0 => by rw [kpow, Measure.id_comp]
  | n + 1 => by rw [kpow, ← Measure.comp_assoc, kpow_comp_invariant κ hπ n, hπ]

lemma comp_real_eq_integral (κ : Kernel α α) [IsMarkovKernel κ] (μ : Measure α)
    {A : Set α} (hA : MeasurableSet A) :
    (κ ∘ₘ μ).real A = ∫ x, (κ x).real A ∂μ := by
  rw [measureReal_def, Measure.bind_apply hA κ.aemeasurable,
    ← integral_toReal (κ.measurable_coe hA).aemeasurable (ae_of_all _ fun x => measure_lt_top _ _)]
  rfl

/-- **Doeblin's condition gives uniqueness.** If `c ν(A) ≤ κ(x, A)` for all `x` and measurable
`A`, with `c > 0` and `ν` a probability measure, then `κ` has at most one invariant probability
measure. -/
theorem doeblin_unique (κ : Kernel α α) [IsMarkovKernel κ] {c : ℝ} (hc : 0 < c)
    (ν : Measure α) [IsProbabilityMeasure ν]
    (hmin : ∀ x A, MeasurableSet A → c * ν.real A ≤ (κ x).real A)
    {π π' : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : κ ∘ₘ π = π) (hπ' : κ ∘ₘ π' = π') : π = π' := by
  have key : ∀ A, MeasurableSet A →
      |(κ ∘ₘ π).real A - (κ ∘ₘ π').real A| ≤ (1 - c) * tv π π' := by
    intro A hA
    rw [comp_real_eq_integral κ π hA, comp_real_eq_integral κ π' hA]
    have hmeas : Measurable fun x => (κ x).real A := (κ.measurable_coe hA).ennreal_toReal
    have hup : ∀ x, (κ x).real A ≤ 1 - c * ν.real Aᶜ := fun x => by
      have h1 := hmin x Aᶜ hA.compl
      rw [measureReal_compl hA, probReal_univ] at h1 ⊢
      rw [measureReal_compl hA, probReal_univ] at h1
      linarith
    have := abs_integral_sub_le_tv π π' hmeas (fun x => hmin x A hA) hup
    convert this using 2
    rw [measureReal_compl hA, probReal_univ]
    ring
  have htv : tv π π' ≤ (1 - c) * tv π π' := by
    have := tv_le_of_forall (κ ∘ₘ π) (κ ∘ₘ π') key
    rwa [hπ, hπ'] at this
  have h0 : tv π π' = 0 := le_antisymm (by nlinarith [tv_nonneg π π']) (tv_nonneg π π')
  ext A hA
  have := le_tv π π' hA
  rw [h0, abs_nonpos_iff, sub_eq_zero, measureReal_def, measureReal_def] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- A unique invariant probability measure is invariant under every measurable map `g` that
commutes with the kernel: `κ(g x, ·) = κ(x, ·) ∘ g⁻¹`. -/
theorem invariant_map_eq (κ : Kernel α α) [IsMarkovKernel κ] {g : α → α} (hg : Measurable g)
    (hcomm : ∀ x, κ (g x) = (κ x).map g)
    (huniq : ∀ π π' : Measure α, IsProbabilityMeasure π → IsProbabilityMeasure π' →
      κ ∘ₘ π = π → κ ∘ₘ π' = π' → π = π')
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ ∘ₘ π = π) : π.map g = π := by
  refine huniq _ _ inferInstance inferInstance ?_ hπ
  ext A hA
  rw [Measure.bind_apply hA κ.aemeasurable, lintegral_map (κ.measurable_coe hA) hg]
  simp_rw [hcomm, Measure.map_apply hg hA]
  rw [← Measure.bind_apply (hg hA) κ.aemeasurable, hπ]

/-- The first half of the Doeblin argument: if from every `x` (with `u ≤ 1` everywhere) the
kernel moves into `{u ≤ max(η, u x - θ)}` with probability at least `a`, then after `i` steps
the chain lies in `{u ≤ max(η, 1 - iθ)}` with probability at least `aⁱ`. -/
lemma doeblin_chain (κ : Kernel α α) [IsMarkovKernel κ] {u : α → ℝ} (hu : Measurable u)
    (hu1 : ∀ x, u x ≤ 1) {θ η a : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hstep : ∀ x, a ≤ (κ x).real {z | u z ≤ max η (u x - θ)}) :
    ∀ (i : ℕ) x, a ^ i ≤ (kpow κ i x).real {z | u z ≤ max η (1 - i * θ)} := by
  intro i
  induction i with
  | zero =>
    intro x
    simp only [kpow, pow_zero, Nat.cast_zero, zero_mul, sub_zero, Kernel.id_apply]
    rw [measureReal_def, Measure.dirac_apply' _ (measurableSet_le hu measurable_const),
      Set.indicator_of_mem (le_max_of_le_right (hu1 x))]
    simp
  | succ i ih =>
    intro x
    have hS : ∀ t : ℝ, MeasurableSet {z | u z ≤ t} := fun t => measurableSet_le hu measurable_const
    rw [kpow, Kernel.comp_apply, comp_real_eq_integral κ _ (hS _)]
    have hle : ∀ z, ({z | u z ≤ max η (1 - i * θ)}).indicator (fun _ => a) z ≤
        (κ z).real {w | u w ≤ max η (1 - ((i + 1 : ℕ) : ℝ) * θ)} := by
      intro z
      by_cases hz : u z ≤ max η (1 - i * θ)
      · rw [Set.indicator_of_mem (show z ∈ {z | u z ≤ max η (1 - i * θ)} from hz)]
        refine (hstep z).trans (measureReal_mono fun w (hw : u w ≤ max η (u z - θ)) => ?_)
        show u w ≤ max η (1 - ((i + 1 : ℕ) : ℝ) * θ)
        refine hw.trans (max_le (le_max_left _ _) ?_)
        push_cast
        rcases le_max_iff.1 hz with h | h
        · exact le_max_of_le_left (by linarith)
        · exact le_max_of_le_right (by linarith)
      · rw [Set.indicator_of_notMem (show z ∉ {z | u z ≤ max η (1 - i * θ)} from hz)]
        exact measureReal_nonneg
    calc a ^ (i + 1) = a * a ^ i := pow_succ' a i
      _ ≤ a * (kpow κ i x).real {z | u z ≤ max η (1 - i * θ)} :=
          mul_le_mul_of_nonneg_left (ih x) ha
      _ = ∫ z, ({z | u z ≤ max η (1 - i * θ)}).indicator (fun _ => a) z ∂(kpow κ i x) := by
          rw [integral_indicator_const _ (hS _), smul_eq_mul, mul_comm]
      _ ≤ _ := integral_mono ((integrable_const a).indicator (hS _))
          (Integrable.of_bound (κ.measurable_coe (hS _)).ennreal_toReal.aestronglyMeasurable 1
            (ae_of_all _ fun z => by
              change ‖(κ z).real _‖ ≤ 1
              rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one)) hle

/-- **The minorization of Corollary 122.** With the step bound of `doeblin_chain` (`θ > 0`) and
a lower bound `κ(z, ·) ≥ b ν` on `{u ≤ η}`, the kernel `κ^{N+1}`, `N = ⌈1/θ⌉`, satisfies
`κ^{N+1}(x, ·) ≥ aᴺ b ν` for every `x`. -/
theorem doeblin_minorization (κ : Kernel α α) [IsMarkovKernel κ] {u : α → ℝ} (hu : Measurable u)
    (hu1 : ∀ x, u x ≤ 1) {θ η a b : ℝ} (hθ : 0 < θ) (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ x, a ≤ (κ x).real {z | u z ≤ max η (u x - θ)}) (ν : Measure α)
    [IsProbabilityMeasure ν]
    (hcen : ∀ z, u z ≤ η → ∀ A, MeasurableSet A → b * ν.real A ≤ (κ z).real A) :
    ∀ x A, MeasurableSet A →
      a ^ ⌈1 / θ⌉₊ * b * ν.real A ≤ (kpow κ (⌈1 / θ⌉₊ + 1) x).real A := by
  intro x A hA
  set N := ⌈1 / θ⌉₊
  have hN : max η (1 - N * θ) = η := by
    have : 1 / θ ≤ N := Nat.le_ceil _
    rw [div_le_iff₀ hθ] at this
    exact max_eq_left (by linarith)
  have hch := doeblin_chain κ hu hu1 hθ.le ha hstep N x
  rw [hN] at hch
  have hS : MeasurableSet {z | u z ≤ η} := measurableSet_le hu measurable_const
  rw [kpow, Kernel.comp_apply, comp_real_eq_integral κ _ hA]
  have hbA : 0 ≤ b * ν.real A := mul_nonneg hb measureReal_nonneg
  calc a ^ N * b * ν.real A = (b * ν.real A) * a ^ N := by ring
    _ ≤ (b * ν.real A) * (kpow κ N x).real {z | u z ≤ η} := mul_le_mul_of_nonneg_left hch hbA
    _ = ∫ z, ({z | u z ≤ η}).indicator (fun _ => b * ν.real A) z ∂(kpow κ N x) := by
        rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]
    _ ≤ _ := by
        refine integral_mono ((integrable_const _).indicator hS)
          (Integrable.of_bound (κ.measurable_coe hA).ennreal_toReal.aestronglyMeasurable 1
            (ae_of_all _ fun z => ?_)) fun z => ?_
        · change ‖(κ z).real A‖ ≤ 1
          rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one
        · by_cases hz : u z ≤ η
          · rw [Set.indicator_of_mem (show z ∈ {z | u z ≤ η} from hz)]; exact hcen z hz A hA
          · rw [Set.indicator_of_notMem (show z ∉ {z | u z ≤ η} from hz)]
            exact measureReal_nonneg

/-- **Uniqueness of the invariant law under the two bounds of the Doeblin argument** (`θ, a,
b > 0`): any two invariant probability measures of `κ` coincide. -/
theorem doeblin_unique_of_bounds (κ : Kernel α α) [IsMarkovKernel κ] {u : α → ℝ}
    (hu : Measurable u) (hu1 : ∀ x, u x ≤ 1) {θ η a b : ℝ} (hθ : 0 < θ) (hη : 0 ≤ η)
    (ha : 0 < a) (hb : 0 < b) (hstep : ∀ x, a ≤ (κ x).real {z | u z ≤ max η (u x - θ)})
    (ν : Measure α) [IsProbabilityMeasure ν]
    (hcen : ∀ z, u z ≤ η → ∀ A, MeasurableSet A → b * ν.real A ≤ (κ z).real A)
    {π π' : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : κ ∘ₘ π = π) (hπ' : κ ∘ₘ π' = π') : π = π' :=
  doeblin_unique (kpow κ (⌈1 / θ⌉₊ + 1)) (by positivity) ν
    (doeblin_minorization κ hu hu1 hθ hη ha.le hb.le hstep ν hcen)
    (kpow_comp_invariant κ hπ _) (kpow_comp_invariant κ hπ' _)

end Doeblin


section BallKernel

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

lemma volume_real_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = r ^ Module.finrank ℝ E * volume.real (closedBall (0 : E) 1) := by
  rw [measureReal_def, Measure.addHaar_closedBall' volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

lemma volume_real_closedBall_one_pos : 0 < volume.real (closedBall (0 : E) 1) :=
  ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne

lemma unifSet_closedBall_isProb (x : E) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (unifSet (closedBall x r)) :=
  unifSet_isProb (measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne

/-- **Corollary 122, the step bound**: `k_ρ(y, ·)` gives the set `{|z| ≤ max(η, |y| - θ)}`
probability at least `η^d`, `η = (1 - ρ)/2`, `θ = min(ρ, 1 - ρ)`. -/
lemma ball_step_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {y : E} (hy : ‖y‖ ≤ 1) :
    ((1 - ρ) / 2) ^ Module.finrank ℝ E ≤ (unifSet (closedBall (ρ • y) (1 - ρ * ‖y‖))).real
      {z | ‖z‖ ≤ max ((1 - ρ) / 2) (‖y‖ - min ρ (1 - ρ))} := by
  have h := cor_ball_subball hρ0 hρ1 hy
  simp only at h
  obtain ⟨-, -, -, hsub, hnorm⟩ := h
  set η := (1 - ρ) / 2
  set c := (max 0 (2 * ρ * ‖y‖ - 1 + η) / ‖y‖) • y
  set lam := 1 - ρ * ‖y‖
  have hη : 0 < η := by simp only [η]; linarith
  have hlam : 0 < lam := by simp only [lam]; nlinarith [norm_nonneg y]
  have hlam1 : lam ≤ 1 := by simp only [lam]; nlinarith [norm_nonneg y]
  have := unifSet_closedBall_isProb (ρ • y) hlam
  have hV := volume_real_closedBall_one_pos (E := E)
  calc η ^ Module.finrank ℝ E ≤ (η / lam) ^ Module.finrank ℝ E :=
        pow_le_pow_left₀ hη.le (le_div_self hη.le hlam hlam1) _
    _ = volume.real (closedBall c η ∩ closedBall (ρ • y) lam) /
          volume.real (closedBall (ρ • y) lam) := by
        rw [Set.inter_eq_left.2 hsub, volume_real_closedBall _ hη.le,
          volume_real_closedBall _ hlam.le, div_pow]
        field_simp
    _ = (unifSet (closedBall (ρ • y) lam)).real (closedBall c η) :=
        (unifSet_real_apply measurableSet_closedBall).symm
    _ ≤ _ := measureReal_mono (fun z hz =>
        (hnorm z hz).trans (cor_ball_step (norm_nonneg y) hy)) (measure_ne_top _ _)

/-- **Corollary 122, the central bound**: for `|y| ≤ η`, `k_ρ(y, ·) ≥ (3/4)^d U((3/4) B)`. -/
lemma ball_central_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {y : E} (hy : ‖y‖ ≤ (1 - ρ) / 2)
    {A : Set E} (hA : MeasurableSet A) :
    (3 / 4 : ℝ) ^ Module.finrank ℝ E * (unifSet (closedBall (0 : E) (3 / 4))).real A ≤
      (unifSet (closedBall (ρ • y) (1 - ρ * ‖y‖))).real A := by
  set lam := 1 - ρ * ‖y‖
  have hlam : 0 < lam := by simp only [lam]; nlinarith [norm_nonneg y]
  have hlam1 : lam ≤ 1 := by simp only [lam]; nlinarith [norm_nonneg y]
  have hV := volume_real_closedBall_one_pos (E := E)
  set d := Module.finrank ℝ E
  set V := volume.real (closedBall (0 : E) 1)
  rw [unifSet_real_apply hA, unifSet_real_apply hA, volume_real_closedBall _ (by norm_num),
    volume_real_closedBall _ hlam.le]
  have hsub := (cor_ball_central hρ0 hy).1.trans (cor_ball_central hρ0 hy).2
  have h1 : volume.real (A ∩ closedBall (0 : E) (3 / 4)) ≤
      volume.real (A ∩ closedBall (ρ • y) lam) :=
    measureReal_mono (Set.inter_subset_inter_right _ hsub)
      ((measure_mono Set.inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  have h2 : lam ^ d ≤ 1 := pow_le_one₀ hlam.le hlam1
  have h34 : (0 : ℝ) < (3 / 4) ^ d := by positivity
  have hld : 0 < lam ^ d := by positivity
  calc (3 / 4 : ℝ) ^ d * (volume.real (A ∩ closedBall 0 (3 / 4)) / ((3 / 4) ^ d * V))
      = volume.real (A ∩ closedBall 0 (3 / 4)) / V := by field_simp
    _ ≤ volume.real (A ∩ closedBall (ρ • y) lam) / V := div_le_div_of_nonneg_right h1 hV.le
    _ ≤ volume.real (A ∩ closedBall (ρ • y) lam) / (lam ^ d * V) :=
        div_le_div_of_nonneg_left measureReal_nonneg (by positivity)
          (by nlinarith)

/-- **Corollary 122, uniqueness of the invariant law.** Let `0 ≤ ρ < 1` and let `κ` be a Markov
kernel on `E` with `κ(y, ·) = U(B(ρ r(y), 1 - ρ|r(y)|))`, where `r` maps into the closed unit
ball `B` and fixes its points (so that `κ` is the kernel `k_ρ` of the paper on `B`, extended to
`E` through `r`). Then `κ` has at most one invariant probability measure. (The existence of the
kernel, i.e. measurability in `y`, is a hypothesis.) -/
theorem cor_ball_unique {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (κ : Kernel E E) [IsMarkovKernel κ]
    (r : E → E) (hr1 : ∀ y, ‖r y‖ ≤ 1) (hr : ∀ y, ‖y‖ ≤ 1 → r y = y)
    (hk : ∀ y, κ y = unifSet (closedBall (ρ • r y) (1 - ρ * ‖r y‖)))
    {π π' : Measure E} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : κ ∘ₘ π = π) (hπ' : κ ∘ₘ π' = π') : π = π' := by
  rcases eq_or_lt_of_le hρ0 with h0 | hpos
  · -- `ρ = 0`: the kernel is constant, `U(B)`
    subst h0
    have hconst : ∀ (μ : Measure E) [IsProbabilityMeasure μ],
        κ ∘ₘ μ = unifSet (closedBall (0 : E) 1) := by
      intro μ _
      have hk0 : ∀ y, κ y = unifSet (closedBall (0 : E) 1) := fun y => by
        rw [hk]; simp only [zero_smul, zero_mul, sub_zero]
      ext A hA
      rw [Measure.bind_apply hA κ.aemeasurable]
      simp_rw [hk0]
      rw [lintegral_const, measure_univ, mul_one]
    rw [← hπ, ← hπ', hconst, hconst]
  · have := unifSet_closedBall_isProb (0 : E) (by norm_num : (0 : ℝ) < 3 / 4)
    have hrx : ∀ x, ‖r x‖ ≤ min ‖x‖ 1 := fun x => by
      by_cases hx : ‖x‖ ≤ 1
      · rw [hr x hx, min_eq_left hx]
      · rw [min_eq_right (le_of_not_ge hx)]; exact hr1 x
    refine doeblin_unique_of_bounds κ (u := fun y => min ‖y‖ 1)
      (continuous_norm.min continuous_const).measurable (fun y => min_le_right _ _)
      (θ := min ρ (1 - ρ)) (η := (1 - ρ) / 2) (a := ((1 - ρ) / 2) ^ Module.finrank ℝ E)
      (b := (3 / 4 : ℝ) ^ Module.finrank ℝ E) (lt_min hpos (by linarith)) (by linarith)
      (by apply pow_pos; linarith) (by positivity) (fun x => ?_)
      (unifSet (closedBall (0 : E) (3 / 4))) (fun z hz A hA => ?_) hπ hπ'
    · rw [hk x]
      have hlam : 0 < 1 - ρ * ‖r x‖ := by nlinarith [norm_nonneg (r x), hr1 x]
      have := unifSet_closedBall_isProb (ρ • r x) hlam
      refine (ball_step_bound hρ0 hρ1 (hr1 x)).trans (measureReal_mono (fun z hz => ?_)
        (measure_ne_top _ _))
      simp only [Set.mem_ofPred_eq] at hz ⊢
      exact (min_le_left _ _).trans (hz.trans (max_le_max le_rfl (by linarith [hrx x])))
    · have hz' : ‖z‖ ≤ (1 - ρ) / 2 := by
        rcases le_total ‖z‖ 1 with h | h
        · rwa [min_eq_left h] at hz
        · rw [min_eq_right h] at hz; linarith
      rw [hk z, hr z (hz'.trans (by linarith))]
      exact ball_central_bound hρ0 hρ1 hz' hA

lemma unifSet_closedBall_map_isometry (g : E ≃ₗᵢ[ℝ] E)
    (hg : MeasurePreserving g volume volume) (c : E) (lam : ℝ) :
    (unifSet (closedBall c lam)).map g = unifSet (closedBall (g c) lam) := by
  have hgm : Measurable g := g.continuous.measurable
  have hpre : g ⁻¹' closedBall (g c) lam = closedBall c lam := by
    ext z; rw [Set.mem_preimage, Metric.mem_closedBall, Metric.mem_closedBall, g.dist_map]
  ext A hA
  rw [Measure.map_apply hgm hA, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply (hgm hA), Measure.restrict_apply hA, smul_eq_mul, smul_eq_mul,
    ← hpre, ← Set.preimage_inter, hg.measure_preimage measurableSet_closedBall.nullMeasurableSet,
    hg.measure_preimage (hA.inter measurableSet_closedBall).nullMeasurableSet]

/-- **Corollary 122, the invariant law is invariant under the orthogonal group**: for every
linear isometry `g` that preserves the volume and commutes with `r`, the invariant law is
`g`-invariant. -/
theorem cor_ball_symm {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (κ : Kernel E E) [IsMarkovKernel κ]
    (r : E → E) (hr1 : ∀ y, ‖r y‖ ≤ 1) (hr : ∀ y, ‖y‖ ≤ 1 → r y = y)
    (hk : ∀ y, κ y = unifSet (closedBall (ρ • r y) (1 - ρ * ‖r y‖)))
    (g : E ≃ₗᵢ[ℝ] E) (hg : MeasurePreserving g volume volume) (hrg : ∀ y, r (g y) = g (r y))
    (π : Measure E) [IsProbabilityMeasure π] (hπ : κ ∘ₘ π = π) : π.map g = π := by
  refine invariant_map_eq κ g.continuous.measurable (fun x => ?_)
    (fun π π' _ _ h h' => cor_ball_unique hρ0 hρ1 κ r hr1 hr hk h h') π hπ
  rw [hk, hk, hrg, LinearIsometryEquiv.norm_map, unifSet_closedBall_map_isometry g hg,
    LinearIsometryEquiv.map_smul]

end BallKernel

/-! ### Feller kernels on compact sets: Krylov–Bogolyubov

Invariant laws as weak limits of Cesàro averages, with Prokhorov's theorem on a compact set
(`isCompact_setOfPred_finiteMeasure_le_of_isCompact` in Mathlib) and the Tietze extension
theorem. -/

section Feller

open Filter Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `κ y` as a point of the space of probability measures (topology of weak convergence). -/
def kPM {Y : Type*} [MeasurableSpace Y] (κ : Kernel Y X) [IsMarkovKernel κ] (y : Y) :
    ProbabilityMeasure X := ⟨κ y, inferInstance⟩

/-- The Cesàro average `(T + 1)⁻¹ ∑_{t ≤ T} κ^t(x, ·)`. -/
def cesaro (κ : Kernel X X) (x : X) (T : ℕ) : Measure X :=
  ((T + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ t ∈ Finset.range (T + 1), kpow κ t x

instance isProbabilityMeasure_cesaro (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (T : ℕ) :
    IsProbabilityMeasure (cesaro κ x T) := by
  constructor
  simp [cesaro, ENNReal.inv_mul_cancel]

/-- The Cesàro average as a probability measure. -/
def cesPM (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (T : ℕ) : ProbabilityMeasure X :=
  ⟨cesaro κ x T, inferInstance⟩

lemma kpow_apply_compl {κ : Kernel X X} {K : Set X} (hK : MeasurableSet K)
    (hκK : ∀ y ∈ K, κ y Kᶜ = 0) : ∀ t, ∀ x ∈ K, kpow κ t x Kᶜ = 0
  | 0, x, hx => by
    rw [kpow, Kernel.id_apply, Measure.dirac_apply' _ hK.compl]
    simp [hx]
  | t + 1, x, hx => by
    rw [kpow, Kernel.comp_apply' _ _ _ hK.compl]
    have h : ∀ᵐ b ∂(kpow κ t x), b ∈ K := by
      rw [ae_iff]; exact kpow_apply_compl hK hκK t x hx
    rw [lintegral_congr_ae (h.mono fun b hb => hκK b hb), lintegral_zero]

lemma cesaro_compl {κ : Kernel X X} {K : Set X} (hK : MeasurableSet K)
    (hκK : ∀ y ∈ K, κ y Kᶜ = 0) {x : X} (hx : x ∈ K) (T : ℕ) : cesaro κ x T Kᶜ = 0 := by
  simp [cesaro, kpow_apply_compl hK hκK _ x hx]

lemma integral_cesaro (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (T : ℕ) (g : X →ᵇ ℝ) :
    ∫ z, g z ∂(cesaro κ x T) =
      ((T : ℝ) + 1)⁻¹ * ∑ t ∈ Finset.range (T + 1), ∫ z, g z ∂(kpow κ t x) := by
  rw [cesaro, integral_smul_measure, integral_finsetSum_measure (fun t _ => g.integrable _)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  push_cast; rfl

lemma integral_comp_measure (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X)
    [IsProbabilityMeasure μ] (g : X →ᵇ ℝ) :
    ∫ z, g z ∂(κ ∘ₘ μ) = ∫ y, ∫ z, g z ∂(κ y) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (g.integrable _)]
  rfl

/-- Tietze: a bounded function continuous on a closed set agrees there with a bounded continuous
function. -/
lemma exists_bcf_eqOn {K : Set X} (hK : IsClosed K) {φ : X → ℝ} (hφ : ContinuousOn φ K) {C : ℝ}
    (hC : ∀ y, ‖φ y‖ ≤ C) : ∃ h : X →ᵇ ℝ, ∀ y ∈ K, h y = φ y := by
  let f : K →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (K.domRestrict φ)
    hφ.domRestrict C (fun y => hC y)
  obtain ⟨g, -, hg⟩ := BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed f hK
  refine ⟨g, fun y hy => ?_⟩
  exact congrArg (fun F : K →ᵇ ℝ => F ⟨y, hy⟩) hg

lemma integral_bound (μ : Measure X) [IsProbabilityMeasure μ] (g : X →ᵇ ℝ) :
    ‖∫ z, g z ∂μ‖ ≤ ‖g‖ := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun z => g z) (C := ‖g‖)
    (Eventually.of_forall fun z => g.norm_coe_le_norm z)
  simpa using this

/-- **Krylov–Bogolyubov for Feller kernels.** Let `κ` be a Markov kernel that maps a closed set
`K` into itself and is Feller on `K` (`y ↦ κ(y, ·)` weakly continuous on `K`), and `x ∈ K`. Every
weak limit `π` of the Cesàro averages `(T + 1)⁻¹ ∑_{t ≤ T} κ^t(x, ·)` along a filter finer than
`atTop` is invariant: `π κ = π`. -/
theorem cesaro_limit_invariant (κ : Kernel X X) [IsMarkovKernel κ] {K : Set X}
    (hK : IsClosed K) (hκK : ∀ y ∈ K, κ y Kᶜ = 0) (hfel : ContinuousOn (kPM κ) K) {x : X}
    (hx : x ∈ K) {F : Filter ℕ} [F.NeBot] (hF : F ≤ atTop) {π : ProbabilityMeasure X}
    (hπ : Tendsto (cesPM κ x) F (𝓝 π)) : κ ∘ₘ (π : Measure X) = π := by
  have hπK : (π : Measure X) Kᶜ = 0 := by
    have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hπ hK.isOpen_compl
    have h0 : (fun T => ((cesPM κ x T : ProbabilityMeasure X) : Measure X) Kᶜ) = fun _ => 0 :=
      funext fun T => cesaro_compl hK.measurableSet hκK hx T
    rw [h0, liminf_const] at h
    exact nonpos_iff_eq_zero.1 h
  have haeK : ∀ᵐ y ∂(π : Measure X), y ∈ K := by rw [ae_iff]; exact hπK
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  set φ : X → ℝ := fun y => ∫ z, g z ∂(κ y)
  have hφc : ContinuousOn φ K := fun y hy =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hfel y hy) g
  obtain ⟨h, hh⟩ := exists_bcf_eqOn hK hφc (C := ‖g‖) fun y => integral_bound (κ y) g
  -- `∫ g d(πκ) = ∫ h dπ`
  have hA : ∫ z, g z ∂(κ ∘ₘ (π : Measure X)) = ∫ y, h y ∂(π : Measure X) := by
    rw [integral_comp_measure]
    exact integral_congr_ae (haeK.mono fun y hy => (hh y hy).symm)
  -- the step identity along the chain
  have hstep : ∀ t, ∫ y, h y ∂(kpow κ t x) = ∫ z, g z ∂(kpow κ (t + 1) x) := by
    intro t
    have haet : ∀ᵐ y ∂(kpow κ t x), y ∈ K := by
      rw [ae_iff]; exact kpow_apply_compl hK.measurableSet hκK t x hx
    rw [integral_congr_ae (haet.mono fun y hy => hh y hy), kpow,
      Kernel.integral_comp (g.integrable _)]
  have hdiff : ∀ T, ∫ y, h y ∂(cesaro κ x T) - ∫ z, g z ∂(cesaro κ x T) =
      ((T : ℝ) + 1)⁻¹ * (∫ z, g z ∂(kpow κ (T + 1) x) - g x) := by
    intro T
    rw [integral_cesaro, integral_cesaro, ← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [hstep]
    rw [Finset.sum_range_sub (fun t => ∫ z, g z ∂(kpow κ t x))]
    simp [kpow, Kernel.id_apply]
  have hlim0 : Tendsto (fun T : ℕ => ∫ y, h y ∂(cesaro κ x T) - ∫ z, g z ∂(cesaro κ x T)) F
      (𝓝 0) := by
    refine (squeeze_zero_norm (a := fun T : ℕ => 2 * ‖g‖ * (1 / ((T : ℝ) + 1))) (fun T => ?_)
      ?_).mono_left hF
    · rw [hdiff, norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity), one_div,
        mul_comm]
      gcongr
      calc ‖∫ z, g z ∂(kpow κ (T + 1) x) - g x‖ ≤ ‖∫ z, g z ∂(kpow κ (T + 1) x)‖ + ‖g x‖ :=
            norm_sub_le _ _
        _ ≤ ‖g‖ + ‖g‖ := add_le_add (integral_bound _ g) (g.norm_coe_le_norm x)
        _ = 2 * ‖g‖ := by ring
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 * ‖g‖)
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ g
  have hh' := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ h
  have hh'' : Tendsto (fun T => ∫ y, h y ∂(cesaro κ x T)) F (𝓝 (∫ z, g z ∂(π : Measure X))) := by
    have := hg.add hlim0
    simp only [add_zero] at this
    refine this.congr fun T => ?_
    simp [cesPM]
  rw [hA]
  exact tendsto_nhds_unique hh' hh''


/-- Prokhorov on a compact set: the probability measures concentrated on a compact set form a
compact set. -/
lemma isCompact_supported {K : Set X} (hK : IsCompact K) :
    IsCompact {μ : ProbabilityMeasure X | (μ : Measure X) Kᶜ = 0} := by
  rw [(ProbabilityMeasure.toFiniteMeasure_isEmbedding X).isCompact_iff]
  have : ProbabilityMeasure.toFiniteMeasure '' {μ : ProbabilityMeasure X | (μ : Measure X) Kᶜ = 0}
      = {ν : FiniteMeasure X | ν.mass ≤ 1 ∧ ν Kᶜ = 0} ∩ {ν | ν.mass = 1} := by
    ext ν
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨⟨by simp, ?_⟩, by simp⟩
      rw [← ENNReal.coe_eq_zero, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact hμ
    · rintro ⟨⟨-, h0⟩, h1⟩
      have hprob : IsProbabilityMeasure (ν : Measure X) :=
        ⟨by rw [← FiniteMeasure.ennreal_mass]; simp [show ν.mass = 1 from h1]⟩
      refine ⟨⟨ν, hprob⟩, ?_, rfl⟩
      show (ν : Measure X) Kᶜ = 0
      rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, h0]; rfl
  rw [this]
  exact (isCompact_setOfPred_finiteMeasure_le_of_isCompact 1 hK).inter_right
    (isClosed_eq (by fun_prop) continuous_const)

/-- **Existence of an invariant law** (Krylov–Bogolyubov): a Markov kernel that maps a nonempty
compact set `K` into itself and is Feller on `K` has an invariant probability measure concentrated
on `K`. -/
theorem exists_invariant_of_feller (κ : Kernel X X) [IsMarkovKernel κ] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hκK : ∀ y ∈ K, κ y Kᶜ = 0)
    (hfel : ContinuousOn (kPM κ) K) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ π Kᶜ = 0 ∧ κ ∘ₘ π = π := by
  obtain ⟨x, hx⟩ := hKne
  obtain ⟨π, hπS, hcl⟩ := (isCompact_supported hK).exists_mapClusterPt (f := atTop)
    (u := cesPM κ x) (tendsto_principal.2 (Eventually.of_forall fun T =>
      cesaro_compl hK.isClosed.measurableSet hκK hx T))
  obtain ⟨U, hU, hUπ⟩ := mapClusterPt_iff_ultrafilter.1 hcl
  exact ⟨π, inferInstance, hπS,
    cesaro_limit_invariant κ hK.isClosed hκK hfel hx (F := (U : Filter ℕ)) hU hUπ⟩

end Feller


/-! ### Theorem 120 (`mk:thm:markov`) -/

section Thm120

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] {n : ℕ}

/-- `𝒯(K₁, …, Kₙ; s)`: the tuples with `xⱼ ∈ Kⱼ` and `∑ xⱼ = s`. -/
def tset (K : Fin n → Set E) (s : E) : Set (Fin n → E) :=
  Set.univ.pi K ∩ {x | ∑ j, x j = s}

lemma isCompact_tset {K : Fin n → Set E} (hK : ∀ j, IsCompact (K j)) (s : E) :
    IsCompact (tset K s) :=
  (isCompact_univ_pi hK).inter_right
    (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

lemma compl_tset_subset (K : Fin n → Set E) (s : E) :
    (tset K s)ᶜ ⊆ (⋃ j, (fun x : Fin n → E => x j) ⁻¹' (K j)ᶜ) ∪ {x | ∑ j, x j ≠ s} := by
  intro x hx
  simp only [tset, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    forall_const, Set.mem_ofPred_eq, not_and_or, not_forall] at hx
  rcases hx with ⟨j, hj⟩ | h
  · exact Or.inl (Set.mem_iUnion.2 ⟨j, hj⟩)
  · exact Or.inr h

/-- The step of a Markov joint mix, at the level of kernels: `P(x, ·)` is concentrated on `𝒯` and
has the marginals `kⱼ(xⱼ, ·)`, for every `x ∈ 𝒯`. The chain with kernel `P` is then a Markov joint
mix of `k₁, …, kₙ` (its law at time `t` is `β₀ Pᵗ`; see `kpow_comp_marg`). -/
def IsMarkovStep (k : Fin n → Kernel E E) (T : Set (Fin n → E))
    (P : Kernel (Fin n → E) (Fin n → E)) : Prop :=
  ∀ x ∈ T, P x Tᶜ = 0 ∧ ∀ j, (P x).map (fun y => y j) = k j (x j)

lemma comp_compl_eq_zero {α : Type*} [MeasurableSpace α] {P : Kernel α α} {T : Set α}
    (hPT : ∀ x ∈ T, P x Tᶜ = 0) (hTm : MeasurableSet T) {μ : Measure α} (hμ : μ Tᶜ = 0) :
    (P ∘ₘ μ) Tᶜ = 0 := by
  rw [Measure.bind_apply hTm.compl P.aemeasurable]
  have h : ∀ᵐ y ∂μ, y ∈ T := by rw [ae_iff]; exact hμ
  rw [lintegral_congr_ae (h.mono fun y hy => hPT y hy), lintegral_zero]

lemma map_comp_eval {P : Kernel (Fin n → E) (Fin n → E)} {k : Kernel E E} {T : Set (Fin n → E)}
    (j : Fin n) (hPk : ∀ x ∈ T, (P x).map (fun y => y j) = k (x j))
    {μ : Measure (Fin n → E)} (hμ : μ Tᶜ = 0) :
    (P ∘ₘ μ).map (fun y => y j) = k ∘ₘ μ.map (fun y => y j) := by
  ext A hA
  have hj : Measurable fun y : Fin n → E => y j := measurable_pi_apply j
  rw [Measure.map_apply hj hA, Measure.bind_apply (hj hA) P.aemeasurable,
    Measure.bind_apply hA k.aemeasurable, lintegral_map (k.measurable_coe hA) hj]
  have h : ∀ᵐ y ∂μ, y ∈ T := by rw [ae_iff]; exact hμ
  refine lintegral_congr_ae (h.mono fun y hy => ?_)
  simp only
  rw [← Measure.map_apply hj hA, hPk y hy]

/-- Along a Markov joint mix the coordinates evolve with their own kernels: if `μ` is
concentrated on `𝒯`, so is `μ Pᵗ`, and its `j`-th marginal is `(μ ∘ eⱼ⁻¹) kⱼᵗ`. -/
lemma kpow_comp_marg {k : Fin n → Kernel E E} {T : Set (Fin n → E)} (hTm : MeasurableSet T)
    {P : Kernel (Fin n → E) (Fin n → E)} (hP : IsMarkovStep k T P)
    {μ : Measure (Fin n → E)} (hμ : μ Tᶜ = 0) :
    ∀ t, (kpow P t ∘ₘ μ) Tᶜ = 0 ∧
      ∀ j, (kpow P t ∘ₘ μ).map (fun y => y j) = kpow (k j) t ∘ₘ μ.map (fun y => y j)
  | 0 => by simp only [kpow, Measure.id_comp]; exact ⟨hμ, fun j => trivial⟩
  | t + 1 => by
    obtain ⟨h1, h2⟩ := kpow_comp_marg hTm hP hμ t
    simp only [kpow, ← Measure.comp_assoc]
    refine ⟨comp_compl_eq_zero (fun x hx => (hP x hx).1) hTm h1, fun j => ?_⟩
    rw [map_comp_eval j (fun x hx => (hP x hx).2 j) h1, h2 j]

lemma kpow_apply_eq_comp {α : Type*} [MeasurableSpace α] (P : Kernel α α) (t : ℕ) (x : α) :
    kpow P t x = kpow P t ∘ₘ Measure.dirac x :=
  (Measure.dirac_bind (Kernel.measurable _) x).symm


lemma kpow_apply_marg {k : Fin n → Kernel E E} {T : Set (Fin n → E)} (hTm : MeasurableSet T)
    {P : Kernel (Fin n → E) (Fin n → E)} (hP : IsMarkovStep k T P) {x : Fin n → E} (hx : x ∈ T)
    (t : ℕ) (j : Fin n) : (kpow P t x).map (fun y => y j) = kpow (k j) t (x j) := by
  have hd : Measure.dirac x Tᶜ = 0 := by
    rw [Measure.dirac_apply' _ hTm.compl]; simp [hx]
  rw [kpow_apply_eq_comp, (kpow_comp_marg hTm hP hd t).2 j,
    Measure.map_dirac' (measurable_pi_apply j), ← kpow_apply_eq_comp]

lemma cesaro_map {k : Fin n → Kernel E E} {T : Set (Fin n → E)} (hTm : MeasurableSet T)
    {P : Kernel (Fin n → E) (Fin n → E)} (hP : IsMarkovStep k T P) {x : Fin n → E} (hx : x ∈ T)
    (T' : ℕ) (j : Fin n) : (cesaro P x T').map (fun y => y j) = cesaro (k j) (x j) T' := by
  ext A hA
  have hj : Measurable fun y : Fin n → E => y j := measurable_pi_apply j
  rw [Measure.map_apply hj hA]
  simp only [cesaro, smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Measure.map_apply hj hA, kpow_apply_marg hTm hP hx]

/-- **Theorem 120(b), core** (`mk:thm:markov`). Let `kⱼ` be Markov kernels that map compact sets
`Kⱼ` into themselves and are Feller on `Kⱼ`, each with exactly one invariant probability measure
`gⱼ` concentrated on `Kⱼ`, and let `P` be the step of a Markov joint mix on `𝒯 = 𝒯(K; s) ≠ ∅`.
Then a weak limit point `π` of the Cesàro averages of the chain started at a point of `𝒯` is a
joint mix of `g₁, …, gₙ` with sum `s`, and the chain with kernel `P` started from `π` has the
stationary marginals `gⱼ` at every time. -/
theorem markov_stationary {K : Fin n → Set E} (hK : ∀ j, IsCompact (K j)) {s : E}
    (hT : (tset K s).Nonempty) (k : Fin n → Kernel E E) [∀ j, IsMarkovKernel (k j)]
    (hkK : ∀ j, ∀ y ∈ K j, k j y (K j)ᶜ = 0) (hfel : ∀ j, ContinuousOn (kPM (k j)) (K j))
    (g : Fin n → Measure E)
    (huniq : ∀ j (μ : Measure E), IsProbabilityMeasure μ → μ (K j)ᶜ = 0 → k j ∘ₘ μ = μ →
      μ = g j)
    (P : Kernel (Fin n → E) (Fin n → E)) [IsMarkovKernel P] (hP : IsMarkovStep k (tset K s) P) :
    ∃ π : Measure (Fin n → E), IsProbabilityMeasure π ∧ π (tset K s)ᶜ = 0 ∧ IsJointMix g π ∧
      ∀ t j, (kpow P t ∘ₘ π).map (fun y => y j) = g j := by
  set T := tset K s
  have hTc : IsCompact T := isCompact_tset hK s
  have hTm : MeasurableSet T := hTc.isClosed.measurableSet
  obtain ⟨x, hx⟩ := hT
  obtain ⟨π, hπS, hcl⟩ := (isCompact_supported hTc).exists_mapClusterPt (f := atTop)
    (u := cesPM P x) (tendsto_principal.2 (Eventually.of_forall fun T' =>
      cesaro_compl hTm (fun y hy => (hP y hy).1) hx T'))
  obtain ⟨U, hU, hUπ⟩ := mapClusterPt_iff_ultrafilter.1 hcl
  have hπT : (π : Measure (Fin n → E)) Tᶜ = 0 := hπS
  have hinv : ∀ j, k j ∘ₘ (π : Measure (Fin n → E)).map (fun y => y j) =
      (π : Measure (Fin n → E)).map (fun y => y j) := by
    intro j
    have hlim : Tendsto (cesPM (k j) (x j)) (U : Filter ℕ) (𝓝 (π.map (fun y => y j))) := by
      have := ((ProbabilityMeasure.continuous_map (continuous_apply j)).tendsto π).comp hUπ
      refine this.congr fun T' => ?_
      apply Subtype.ext
      simp only [Function.comp]
      exact cesaro_map hTm hP hx T' j
    have h := cesaro_limit_invariant (k j) (hK j).isClosed (hkK j) (hfel j)
      (hx.1 j (Set.mem_univ _)) hU hlim
    simp only [ProbabilityMeasure.toMeasure_map] at h
    exact h
  have hmarg : ∀ j, (π : Measure (Fin n → E)).map (fun y => y j) = g j := by
    intro j
    have hj : Measurable fun y : Fin n → E => y j := measurable_pi_apply j
    refine huniq j _ inferInstance ?_ (hinv j)
    rw [Measure.map_apply hj (hK j).isClosed.measurableSet.compl]
    refine measure_mono_null (fun y hy => ?_) hπT
    intro hyT
    exact hy (hyT.1 j (Set.mem_univ _))
  refine ⟨π, inferInstance, hπT, ⟨inferInstance, ⟨s, ?_⟩, hmarg⟩, fun t j => ?_⟩
  · have h : ∀ᵐ y ∂(π : Measure (Fin n → E)), y ∈ T := by rw [ae_iff]; exact hπT
    exact h.mono fun y hy => hy.2
  · rw [(kpow_comp_marg hTm hP hπT t).2 j, hmarg j]
    refine kpow_comp_invariant (k j) ?_ t
    rw [← hmarg j]; exact hinv j

/-- **Borel selection, as a hypothesis** (the selection theorem of Kuratowski and
Ryll-Nardzewski, together with the identification of the Borel sets of the weak topology with the
σ-algebra of measures, Aliprantis–Border, Chapters 17 and 18). A correspondence from a closed set
`D` into a compact set of probability measures, with nonempty values and a closed graph, has a
selection that is a Markov kernel. -/
def BorelSelection (X Y : Type*) [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] : Prop :=
  ∀ (D : Set X) (C : Set (ProbabilityMeasure Y)) (J : X → Set (ProbabilityMeasure Y)),
    IsClosed D → IsCompact C → (∀ x ∈ D, (J x).Nonempty ∧ J x ⊆ C) →
    IsClosed {p : X × ProbabilityMeasure Y | p.1 ∈ D ∧ p.2 ∈ J p.1} →
    ∃ P : Kernel X Y, ∃ _ : IsMarkovKernel P, ∀ x ∈ D, kPM P x ∈ J x

lemma integrable_id_of_compact {μ : Measure E} [IsFiniteMeasure μ] {K : Set E}
    (hK : IsCompact K) (hμ : μ Kᶜ = 0) : Integrable (fun z : E => z) μ := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have h : ∀ᵐ z ∂μ, z ∈ K := by rw [ae_iff]; exact hμ
  exact (integrable_const C).mono' aestronglyMeasurable_id (h.mono fun z hz => by
    simpa using hC z hz)

/-- A joint mix of `k₁(x₁, ·), …, kₙ(xₙ, ·)`, with `x ∈ 𝒯` and affine means with a common linear
part, is concentrated on `𝒯`: its sum is `∑ⱼ mⱼ(xⱼ) = Γ s + ∑ⱼ cⱼ = s`. -/
lemma jointMix_concentrated {K : Fin n → Set E} (hK : ∀ j, IsCompact (K j)) {s : E}
    (k : Fin n → Kernel E E) [∀ j, IsMarkovKernel (k j)]
    (hkK : ∀ j, ∀ y ∈ K j, k j y (K j)ᶜ = 0) (Γ : E →L[ℝ] E) (c : Fin n → E)
    (hmean : ∀ j, ∀ y ∈ K j, ∫ z, z ∂(k j y) = Γ y + c j) (hs : Γ s + ∑ j, c j = s)
    {x : Fin n → E} (hx : x ∈ tset K s) {π : Measure (Fin n → E)}
    (hπ : IsJointMix (fun j => k j (x j)) π) : π (tset K s)ᶜ = 0 := by
  obtain ⟨hprob, ⟨s', hs'⟩, hm0⟩ := hπ
  have hm : ∀ j, π.map (fun y => y j) = k j (x j) := hm0
  have hxj : ∀ j, x j ∈ K j := fun j => hx.1 j (Set.mem_univ _)
  have hj : ∀ j, Measurable fun y : Fin n → E => y j := fun j => measurable_pi_apply j
  have hcoord : ∀ j, π ((fun y : Fin n → E => y j) ⁻¹' (K j)ᶜ) = 0 := by
    intro j
    rw [← Measure.map_apply (hj j) (hK j).isClosed.measurableSet.compl, hm j]
    exact hkK j _ (hxj j)
  -- the sum is `s`
  have hint : ∀ j, Integrable (fun y : Fin n → E => y j) π := by
    intro j
    have := integrable_id_of_compact (μ := k j (x j)) (hK j) (hkK j _ (hxj j))
    rw [← hm j] at this
    exact (integrable_map_measure aestronglyMeasurable_id (hj j).aemeasurable).1 this
  have hss : s' = s := by
    have e1 : ∫ y, ∑ j, y j ∂π = s' := by
      rw [integral_congr_ae hs', integral_const, probReal_univ, one_smul]
    have e2 : ∫ y, ∑ j, y j ∂π = ∑ j, (Γ (x j) + c j) := by
      rw [integral_finsetSum _ fun j _ => hint j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hmean j _ (hxj j), ← hm j,
        integral_map (hj j).aemeasurable (f := fun z : E => z) aestronglyMeasurable_id]
    rw [← e1, e2, Finset.sum_add_distrib, ← map_sum, hx.2, hs]
  subst hss
  refine measure_mono_null (compl_tset_subset K s') (measure_union_null
    (measure_iUnion_null hcoord) ?_)
  rw [← ae_iff] at *
  exact hs'

/-- **Theorem 120(a)** (`mk:thm:markov`), given the selection theorem (`BorelSelection`). Let
`kⱼ` be Markov kernels that map compact sets `Kⱼ` into themselves and are Feller on `Kⱼ`, with
means `mⱼ(y) = Γ y + cⱼ` on `Kⱼ`, let `Γ s + ∑ cⱼ = s`, and suppose that for every `x ∈ 𝒯` the
distributions `kⱼ(xⱼ, ·)` are jointly mixable. Then there is a Markov kernel `P` that is the
step of a Markov joint mix on `𝒯` (`IsMarkovStep`): the chain with kernel `P` and any initial law
on `𝒯` is a Markov joint mix of `k₁, …, kₙ` with sum `s`. -/
theorem thm120_a (hsel : BorelSelection (Fin n → E) (Fin n → E)) {K : Fin n → Set E}
    (hK : ∀ j, IsCompact (K j)) {s : E} (k : Fin n → Kernel E E) [∀ j, IsMarkovKernel (k j)]
    (hkK : ∀ j, ∀ y ∈ K j, k j y (K j)ᶜ = 0) (hfel : ∀ j, ContinuousOn (kPM (k j)) (K j))
    (Γ : E →L[ℝ] E) (c : Fin n → E) (hmean : ∀ j, ∀ y ∈ K j, ∫ z, z ∂(k j y) = Γ y + c j)
    (hs : Γ s + ∑ j, c j = s)
    (hmix : ∀ x ∈ tset K s, JointlyMixable fun j => k j (x j)) :
    ∃ P : Kernel (Fin n → E) (Fin n → E), IsMarkovKernel P ∧ IsMarkovStep k (tset K s) P := by
  set T := tset K s
  have hTc : IsCompact T := isCompact_tset hK s
  set S := {μ : ProbabilityMeasure (Fin n → E) | (μ : Measure (Fin n → E)) Tᶜ = 0}
  have hSc : IsCompact S := isCompact_supported hTc
  set J : (Fin n → E) → Set (ProbabilityMeasure (Fin n → E)) := fun x =>
    {μ | (μ : Measure (Fin n → E)) Tᶜ = 0 ∧
      ∀ j, μ.map (fun y => y j) = kPM (k j) (x j)}
  have hJ : ∀ x ∈ T, (J x).Nonempty ∧ J x ⊆ S := by
    intro x hx
    refine ⟨?_, fun μ hμ => hμ.1⟩
    obtain ⟨π, hπ⟩ := hmix x hx
    have := hπ.1
    refine ⟨⟨π, this⟩, jointMix_concentrated hK k hkK Γ c hmean hs hx hπ, fun j => ?_⟩
    apply Subtype.ext
    exact hπ.2.2 j
  have hG :
      IsClosed {p : (Fin n → E) × ProbabilityMeasure (Fin n → E) | p.1 ∈ T ∧ p.2 ∈ J p.1} := by
    have hD : IsClosed {p : (Fin n → E) × ProbabilityMeasure (Fin n → E) | p.1 ∈ T} :=
      hTc.isClosed.preimage continuous_fst
    have hS' : IsClosed {p : (Fin n → E) × ProbabilityMeasure (Fin n → E) | p.2 ∈ S} :=
      hSc.isClosed.preimage continuous_snd
    have hj : ∀ j, IsClosed ({p : (Fin n → E) × ProbabilityMeasure (Fin n → E) | p.1 ∈ T} ∩
        (fun p => (p.2.map (fun y => y j), kPM (k j) (p.1 j))) ⁻¹'
          {q : ProbabilityMeasure E × ProbabilityMeasure E | q.1 = q.2}) := by
      intro j
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hD isClosed_diagonal
      refine ContinuousOn.prodMk ?_ ?_
      · exact ((ProbabilityMeasure.continuous_map (continuous_apply j)).comp
          continuous_snd).continuousOn
      · refine (hfel j).comp ((continuous_apply j).comp continuous_fst).continuousOn ?_
        intro p hp
        exact hp.1 j (Set.mem_univ _)
    have : {p : (Fin n → E) × ProbabilityMeasure (Fin n → E) | p.1 ∈ T ∧ p.2 ∈ J p.1} =
        ({p | p.1 ∈ T} ∩ {p | p.2 ∈ S}) ∩ ⋂ j, ({p : (Fin n → E) × ProbabilityMeasure (Fin n → E) |
          p.1 ∈ T} ∩ (fun p => (p.2.map (fun y => y j), kPM (k j) (p.1 j))) ⁻¹'
          {q : ProbabilityMeasure E × ProbabilityMeasure E | q.1 = q.2}) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, J, S]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun j => ⟨h1, h3 j⟩⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, fun j => (h3 j).2⟩
    rw [this]
    exact (hD.inter hS').inter (isClosed_iInter hj)
  obtain ⟨P, hPm, hPJ⟩ := hsel T S J hTc.isClosed hSc hJ hG
  refine ⟨P, hPm, fun x hx => ⟨(hPJ x hx).1, fun j => ?_⟩⟩
  have := congrArg (fun μ : ProbabilityMeasure E => (μ : Measure E)) ((hPJ x hx).2 j)
  exact this

/-- **Theorem 120(b)** (`mk:thm:markov`), given the selection theorem. Under the hypotheses of
`thm120_a`, if each `kⱼ` has exactly one invariant probability measure `gⱼ` concentrated on `Kⱼ`,
then `g₁, …, gₙ` are jointly mixable with sum `s`, and there is a Markov joint mix (kernel `P`,
initial law `π`) in which every coordinate is stationary, `Yⱼ(t) ∼ gⱼ` for all `t`. -/
theorem thm120_b (hsel : BorelSelection (Fin n → E) (Fin n → E)) {K : Fin n → Set E}
    (hK : ∀ j, IsCompact (K j)) {s : E} (hT : (tset K s).Nonempty)
    (k : Fin n → Kernel E E) [∀ j, IsMarkovKernel (k j)]
    (hkK : ∀ j, ∀ y ∈ K j, k j y (K j)ᶜ = 0) (hfel : ∀ j, ContinuousOn (kPM (k j)) (K j))
    (Γ : E →L[ℝ] E) (c : Fin n → E) (hmean : ∀ j, ∀ y ∈ K j, ∫ z, z ∂(k j y) = Γ y + c j)
    (hs : Γ s + ∑ j, c j = s)
    (hmix : ∀ x ∈ tset K s, JointlyMixable fun j => k j (x j)) (g : Fin n → Measure E)
    (huniq : ∀ j (μ : Measure E), IsProbabilityMeasure μ → μ (K j)ᶜ = 0 → k j ∘ₘ μ = μ →
      μ = g j) :
    ∃ P : Kernel (Fin n → E) (Fin n → E), IsMarkovKernel P ∧ IsMarkovStep k (tset K s) P ∧
      ∃ π : Measure (Fin n → E), IsProbabilityMeasure π ∧ π (tset K s)ᶜ = 0 ∧ IsJointMix g π ∧
        ∀ t j, (kpow P t ∘ₘ π).map (fun y => y j) = g j := by
  obtain ⟨P, hPm, hP⟩ := thm120_a hsel hK k hkK hfel Γ c hmean hs hmix
  exact ⟨P, hPm, hP, markov_stationary hK hT k hkK hfel g huniq P hP⟩

/-- **Theorem 121(b), second half** (`mk:thm:large`). If the step `P` of a Markov joint mix on
`𝒯 ≠ ∅` is weakly continuous on `𝒯` (the first half of 121(b), which needs the proof of
Theorem 113, is this hypothesis), the chain has an invariant distribution `π` on `𝒯`, under which
every coordinate is stationary: its law `π ∘ eⱼ⁻¹` is invariant for `kⱼ` and is the law of
`Yⱼ(t)` for every `t`. -/
theorem thm121_b {K : Fin n → Set E} (hK : ∀ j, IsCompact (K j)) {s : E}
    (hT : (tset K s).Nonempty) (k : Fin n → Kernel E E)
    (P : Kernel (Fin n → E) (Fin n → E)) [IsMarkovKernel P] (hP : IsMarkovStep k (tset K s) P)
    (hfel : ContinuousOn (kPM P) (tset K s)) :
    ∃ π : Measure (Fin n → E), IsProbabilityMeasure π ∧ π (tset K s)ᶜ = 0 ∧ P ∘ₘ π = π ∧
      (∀ j, k j ∘ₘ π.map (fun y => y j) = π.map (fun y => y j)) ∧
      ∀ t j, (kpow P t ∘ₘ π).map (fun y => y j) = π.map (fun y => y j) := by
  obtain ⟨π, hπ, hπT, hinv⟩ := exists_invariant_of_feller P (isCompact_tset hK s) hT
    (fun x hx => (hP x hx).1) hfel
  refine ⟨π, hπ, hπT, hinv, fun j => ?_, fun t j => by rw [kpow_comp_invariant P hinv t]⟩
  rw [← map_comp_eval j (fun x hx => (hP x hx).2 j) hπT, hinv]

end Thm120

/-! ### Corollary 122: the kernel `k_ρ`, its invariant law and the stationary joint mix -/

section BallExist

open Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The retraction `y ↦ y / max(1, |y|)` onto the closed unit ball. -/
def ballRet (y : E) : E := (max 1 ‖y‖)⁻¹ • y

lemma max_one_norm_pos (y : E) : 0 < max 1 ‖y‖ := lt_of_lt_of_le one_pos (le_max_left _ _)

lemma continuous_ballRet : Continuous (ballRet (E := E)) :=
  ((continuous_const.max continuous_norm).inv₀ fun y => (max_one_norm_pos y).ne').smul
    continuous_id

lemma norm_ballRet_le (y : E) : ‖ballRet y‖ ≤ 1 := by
  rw [ballRet, norm_smul, norm_inv, Real.norm_of_nonneg (max_one_norm_pos y).le, inv_mul_le_iff₀
    (max_one_norm_pos y), mul_one]
  exact le_max_right _ _

lemma ballRet_of_norm_le {y : E} (hy : ‖y‖ ≤ 1) : ballRet y = y := by
  rw [ballRet, max_eq_left hy, inv_one, one_smul]

lemma ballRet_isometry (L : E ≃ₗᵢ[ℝ] E) (y : E) : ballRet (L y) = L (ballRet y) := by
  rw [ballRet, ballRet, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.map_smul]

/-- `w ↦ ρ r(y) + (1 - ρ |r(y)|) w`, which maps `U(B)` to `U(B(ρ r(y), 1 - ρ |r(y)|))`. -/
def ballMap (ρ : ℝ) (y w : E) : E := ρ • ballRet y + (1 - ρ * ‖ballRet y‖) • w

lemma continuous_ballMap (ρ : ℝ) : Continuous (Function.uncurry (ballMap (E := E) ρ)) := by
  unfold ballMap
  have h := continuous_ballRet.comp (continuous_fst (X := E) (Y := E))
  exact (continuous_const.smul h).add
    ((continuous_const.sub (continuous_const.mul (continuous_norm.comp h))).smul continuous_snd)

lemma continuous_ballMap_right (ρ : ℝ) (y : E) : Continuous (ballMap ρ y) :=
  (continuous_ballMap ρ).comp (Continuous.prodMk_right y)

lemma continuous_ballMap_left (ρ : ℝ) (w : E) : Continuous fun y => ballMap ρ y w :=
  (continuous_ballMap ρ).comp (Continuous.prodMk_left w)

instance unifBall_isProb : IsProbabilityMeasure (unifSet (closedBall (0 : E) 1)) :=
  unifSet_closedBall_isProb 0 one_pos

/-- **The kernel `k_ρ` of Corollary 122**, `k_ρ(y, ·) = U(B(ρ y, 1 - ρ|y|))` on the unit ball `B`,
extended to `E` through the retraction `r` (`ballKernel_eq`). -/
def ballKernel (ρ : ℝ) : Kernel E E where
  toFun y := (unifSet (closedBall (0 : E) 1)).map (ballMap ρ y)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hF := (continuous_ballMap (E := E) ρ).measurable
    have : (fun y => (unifSet (closedBall (0 : E) 1)).map (ballMap ρ y) s) =
        fun y => unifSet (closedBall (0 : E) 1)
          (Prod.mk y ⁻¹' (Function.uncurry (ballMap ρ) ⁻¹' s)) := by
      funext y
      rw [Measure.map_apply (continuous_ballMap_right ρ y).measurable hs]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hF hs)

lemma ballKernel_apply (ρ : ℝ) (y : E) :
    ballKernel ρ y = (unifSet (closedBall (0 : E) 1)).map (ballMap ρ y) := rfl

instance (ρ : ℝ) : IsMarkovKernel (ballKernel (E := E) ρ) :=
  ⟨fun y => by
    rw [ballKernel_apply]
    infer_instance⟩

lemma radius_pos {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (y : E) : 0 < 1 - ρ * ‖ballRet y‖ := by
  nlinarith [norm_ballRet_le y, norm_nonneg (ballRet y)]

lemma ballKernel_eq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (y : E) :
    ballKernel ρ y = unifSet (closedBall (ρ • ballRet y) (1 - ρ * ‖ballRet y‖)) := by
  have h0 : volume (closedBall (0 : E) 1) ≠ 0 := (measure_closedBall_pos volume 0 one_pos).ne'
  rw [ballKernel_apply, show ballMap ρ y = fun w => ρ • ballRet y + (1 - ρ * ‖ballRet y‖) • w
    from rfl, ← unifScaled_eq_map h0 measure_closedBall_lt_top.ne]
  simp only [unifScaled, (radius_pos hρ0 hρ1 y).ne', ↓reduceIte]
  rw [image_homothety_closedBall _ (radius_pos hρ0 hρ1 y)]

lemma unifBall_compl : unifSet (closedBall (0 : E) 1) (closedBall 0 1)ᶜ = 0 := by
  rw [unifSet, smul_apply, Measure.restrict_apply measurableSet_closedBall.compl]
  simp

lemma ballKernel_compl {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (y : E) :
    ballKernel ρ y (closedBall 0 1)ᶜ = 0 := by
  have hm := (continuous_ballMap_right (E := E) ρ y).measurable
  rw [ballKernel_apply, Measure.map_apply hm measurableSet_closedBall.compl]
  refine measure_mono_null (fun w hw => ?_) unifBall_compl
  intro hwB
  apply hw
  simp only [mem_closedBall, dist_zero_right, ballMap] at hwB ⊢
  have h1 := norm_ballRet_le y
  have h2 := radius_pos hρ0 hρ1 y
  calc ‖ρ • ballRet y + (1 - ρ * ‖ballRet y‖) • w‖
      ≤ ‖ρ • ballRet y‖ + ‖(1 - ρ * ‖ballRet y‖) • w‖ := norm_add_le _ _
    _ = ρ * ‖ballRet y‖ + (1 - ρ * ‖ballRet y‖) * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hρ0, Real.norm_of_nonneg h2.le]
    _ ≤ ρ * ‖ballRet y‖ + (1 - ρ * ‖ballRet y‖) * 1 := by gcongr
    _ = 1 := by ring

/-- `k_ρ` is Feller (weakly continuous in `y`). -/
lemma ballKernel_feller (ρ : ℝ) : Continuous (kPM (ballKernel (E := E) ρ)) := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hF := continuous_ballMap (E := E) ρ
  have key : ∀ y', ∫ z, g z ∂(kPM (ballKernel ρ) y' : Measure E) =
      ∫ w, g (ballMap ρ y' w) ∂(unifSet (closedBall (0 : E) 1)) := by
    intro y'
    show ∫ z, g z ∂(ballKernel ρ y') = _
    rw [ballKernel_apply, integral_map (continuous_ballMap_right ρ y').measurable.aemeasurable
      g.continuous.aestronglyMeasurable]
  simp_rw [key]
  refine (continuous_of_dominated (bound := fun _ => ‖g‖) (fun y' => ?_)
    (fun y' => Eventually.of_forall fun w => g.norm_coe_le_norm _) (integrable_const _)
    (Eventually.of_forall fun w => ?_)).tendsto y
  · exact (g.continuous.comp (continuous_ballMap_right ρ y')).aestronglyMeasurable
  · exact g.continuous.comp (continuous_ballMap_left ρ w)

lemma integral_unifBall : ∫ w, w ∂(unifSet (closedBall (0 : E) 1)) = 0 := by
  have hg : MeasurePreserving (LinearIsometryEquiv.neg ℝ (E := E)) volume volume :=
    Measure.measurePreserving_neg volume
  have hmap := unifSet_closedBall_map_isometry (LinearIsometryEquiv.neg ℝ (E := E)) hg 0 1
  simp only [LinearIsometryEquiv.coe_neg, neg_zero] at hmap
  have h : ∫ w, w ∂(unifSet (closedBall (0 : E) 1)) =
      -∫ w, w ∂(unifSet (closedBall (0 : E) 1)) := by
    conv_lhs => rw [← hmap]
    rw [integral_map continuous_neg.measurable.aemeasurable (f := fun w : E => w)
      aestronglyMeasurable_id, ← integral_neg]
  have h2 : (2 : ℝ) • ∫ w, w ∂(unifSet (closedBall (0 : E) 1)) = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- The mean of `k_ρ(y, ·)` is `ρ y` on the unit ball. -/
lemma ballKernel_mean {ρ : ℝ} {y : E} (hy : ‖y‖ ≤ 1) :
    ∫ z, z ∂(ballKernel ρ y) = ρ • y := by
  have hF := continuous_ballMap (E := E) ρ
  rw [ballKernel_apply, integral_map (continuous_ballMap_right ρ y).measurable.aemeasurable
    (f := fun w : E => w) aestronglyMeasurable_id]
  simp only [ballMap]
  have hint : Integrable (fun w : E => w) (unifSet (closedBall (0 : E) 1)) :=
    integrable_id_of_compact (isCompact_closedBall 0 1) unifBall_compl
  have hint2 : Integrable (fun w : E => (1 - ρ * ‖ballRet y‖) • w)
      (unifSet (closedBall (0 : E) 1)) := hint.smul _
  rw [integral_add (integrable_const _) hint2, integral_const, integral_smul,
    integral_unifBall, smul_zero, add_zero, probReal_univ, one_smul, ballRet_of_norm_le hy]

/-- **Corollary 122, the invariant law** (`mk:cor:ball`). For `0 ≤ ρ < 1` the kernel `k_ρ` has
exactly one invariant probability measure `g_ρ`; it is concentrated on the unit ball and invariant
under every volume-preserving linear isometry. (Existence: Krylov–Bogolyubov, as `k_ρ` is Feller
on the compact ball; uniqueness: Doeblin, `cor_ball_unique`.) -/
theorem cor_ball_invariant {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ g : Measure E, IsProbabilityMeasure g ∧ g (closedBall 0 1)ᶜ = 0 ∧
      ballKernel ρ ∘ₘ g = g ∧
      (∀ g' : Measure E, IsProbabilityMeasure g' → ballKernel ρ ∘ₘ g' = g' → g' = g) ∧
      ∀ L : E ≃ₗᵢ[ℝ] E, MeasurePreserving L volume volume → g.map L = g := by
  obtain ⟨g, hg, hgB, hinv⟩ := exists_invariant_of_feller (ballKernel (E := E) ρ)
    (isCompact_closedBall 0 1) ⟨0, mem_closedBall_self zero_le_one⟩
    (fun y _ => ballKernel_compl hρ0 hρ1 y) (ballKernel_feller ρ).continuousOn
  have hk := ballKernel_eq (E := E) hρ0 hρ1
  refine ⟨g, hg, hgB, hinv, fun g' _ h' => ?_, fun L hL => ?_⟩
  · exact cor_ball_unique hρ0 hρ1 (ballKernel ρ) ballRet norm_ballRet_le
      (fun y hy => ballRet_of_norm_le hy) hk h' hinv
  · exact cor_ball_symm hρ0 hρ1 (ballKernel ρ) ballRet norm_ballRet_le
      (fun y hy => ballRet_of_norm_le hy) hk L hL (ballRet_isometry L) g hinv

end BallExist

section BallJoint

open Metric

open Mixes.Ball

variable {d n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The radii `1 - ρ|r(xⱼ)|` and centres `ρ r(xⱼ)` of the step of Corollary 122. -/
def ballParams (ρ : ℝ) (x : Fin n → 𝔼) : (Fin n → ℝ) × (Fin n → 𝔼) :=
  (fun j => 1 - ρ * ‖ballRet (x j)‖, fun j => ρ • ballRet (x j))

lemma continuous_ballParams (ρ : ℝ) : Continuous (ballParams (n := n) (d := d) ρ) :=
  (continuous_pi fun j => continuous_const.sub (continuous_const.mul
    (continuous_norm.comp (continuous_ballRet.comp (continuous_apply j))))).prodMk
  (continuous_pi fun j => (continuous_ballRet.comp (continuous_apply j)).const_smul ρ)

/-- The step of the Markov joint mix of Corollary 122: from `x`, the joint mix of Theorem 51 of
`U(B(ρ xⱼ, 1 - ρ|xⱼ|))`, given by a Borel map `Φ` of the radii, the centres and a sequence of
independent uniform variables. -/
def ballStep (ρ : ℝ) (Φ : (Fin n → ℝ) × (Fin n → 𝔼) → (ℕ → ℝ) → (Fin n → 𝔼))
    (hΦ : Measurable (Function.uncurry Φ)) : Kernel (Fin n → 𝔼) (Fin n → 𝔼) where
  toFun x := unifSeq.map (Φ (ballParams ρ x))
  measurable' := by
    set G : (Fin n → 𝔼) × (ℕ → ℝ) → (Fin n → 𝔼) := fun p => Φ (ballParams ρ p.1) p.2
    have hG : Measurable G :=
      hΦ.comp (((continuous_ballParams ρ).measurable.comp measurable_fst).prodMk measurable_snd)
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have : (fun x => unifSeq.map (Φ (ballParams ρ x)) s) =
        fun x => unifSeq (Prod.mk x ⁻¹' (G ⁻¹' s)) := by
      funext x
      have hx : Measurable (Φ (ballParams ρ x)) := hΦ.of_uncurry_left
      rw [Measure.map_apply hx hs]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hG hs)

instance (ρ : ℝ) Φ hΦ : IsMarkovKernel (ballStep (n := n) (d := d) ρ Φ hΦ) :=
  ⟨fun x => by
    show IsProbabilityMeasure (unifSeq.map _)
    infer_instance⟩

/-- **Corollary 122** (`mk:cor:ball`). Let `0 ≤ ρ < 1` and `n ≥ 2/(1 - ρ)`. The kernel `k_ρ` on
the unit ball `B ⊂ ℝ^d` has exactly one invariant law `g_ρ`, which is invariant under the
orthogonal group, and there is a Markov joint mix of `n` copies of `k_ρ` with sum `0` in which
every coordinate is stationary: a kernel `P` whose step from `x ∈ 𝒯(B, …, B; 0)` is a joint mix of
the `U(B(ρ xⱼ, 1 - ρ|xⱼ|))` (the joint mix of Theorem 51), and an initial law `π` that is an
`n`-complete mix of `g_ρ`, with `Yⱼ(t) ∼ g_ρ` for all `t`. -/
theorem cor_ball {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hn : 2 / (1 - ρ) ≤ n) :
    ∃ g : Measure 𝔼, IsProbabilityMeasure g ∧ g (closedBall 0 1)ᶜ = 0 ∧
      ballKernel ρ ∘ₘ g = g ∧
      (∀ g' : Measure 𝔼, IsProbabilityMeasure g' → ballKernel ρ ∘ₘ g' = g' → g' = g) ∧
      (∀ L : 𝔼 ≃ₗᵢ[ℝ] 𝔼, g.map L = g) ∧
      ∃ P : Kernel (Fin n → 𝔼) (Fin n → 𝔼), IsMarkovKernel P ∧
        IsMarkovStep (fun _ => ballKernel ρ) (tset (fun _ => closedBall 0 1) 0) P ∧
        (∀ x ∈ tset (fun _ => closedBall (0 : 𝔼) 1) 0,
          IsJointMix (fun j => unifSet (closedBall (ρ • x j) (1 - ρ * ‖x j‖))) (P x)) ∧
        ∃ π : Measure (Fin n → 𝔼), IsCompleteMix n g π ∧
          π (tset (fun _ => closedBall 0 1) 0)ᶜ = 0 ∧
          ∀ t j, (kpow P t ∘ₘ π).map (fun y => y j) = g := by
  have h1 : 0 < 1 - ρ := by linarith
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ n := le_trans (by rw [le_div_iff₀ h1]; linarith) hn
    exact_mod_cast this
  obtain ⟨g, hg, hgB, hinv, huniq, hsym0⟩ := cor_ball_invariant (E := 𝔼) hρ0 hρ1
  have hsymm : ∀ L : 𝔼 ≃ₗᵢ[ℝ] 𝔼, g.map L = g := fun L => hsym0 L L.measurePreserving
  obtain ⟨Φ, hΦm, hΦ⟩ := ball_scalingProperty d n hn2
  set P := ballStep (n := n) ρ Φ hΦm
  set T := tset (fun _ : Fin n => closedBall (0 : 𝔼) 1) 0
  have hmixP : ∀ x ∈ T, IsJointMix (fun j => ballKernel ρ (x j)) (P x) := by
    intro x hx
    have hxj : ∀ j, ‖x j‖ ≤ 1 := fun j => by
      simpa using hx.1 j (Set.mem_univ _)
    have hr : ∀ j, ballRet (x j) = x j := fun j => ballRet_of_norm_le (hxj j)
    have := hΦ (fun j => 1 - ρ * ‖ballRet (x j)‖) (fun j => ρ • ballRet (x j))
      (fun j => (radius_pos hρ0 hρ1 (x j)).le) ⟨⟨0, by omega⟩, (radius_pos hρ0 hρ1 _).ne'⟩
      (fun k => by simpa [hr] using (cor_ball_polygon hρ0 hρ1 hn x hxj).1 k)
    exact this
  have hstep : IsMarkovStep (fun _ => ballKernel ρ) T P := by
    intro x hx
    refine ⟨?_, fun j => (hmixP x hx).2.2 j⟩
    refine jointMix_concentrated (fun _ => isCompact_closedBall (0 : 𝔼) 1)
      (fun _ => ballKernel ρ) (fun _ y _ => ballKernel_compl hρ0 hρ1 y)
      (ρ • ContinuousLinearMap.id ℝ 𝔼) 0 (fun j y hy => ?_) (by simp) hx (hmixP x hx)
    simp only [smul_apply, ContinuousLinearMap.id_apply, Pi.zero_apply,
      add_zero]
    exact ballKernel_mean (by simpa using hy)
  have hT : T.Nonempty := ⟨0, fun j _ => mem_closedBall_self zero_le_one, by simp⟩
  obtain ⟨π, hπ, hπT, hmix, hstat⟩ := markov_stationary (fun _ => isCompact_closedBall 0 1) hT
    (fun _ => ballKernel ρ) (fun _ y _ => ballKernel_compl hρ0 hρ1 y)
    (fun _ => (ballKernel_feller ρ).continuousOn) (fun _ => g)
    (fun _ μ hμ _ hμinv => huniq μ hμ hμinv) P hstep
  refine ⟨g, hg, hgB, hinv, huniq, hsymm, P, inferInstance, hstep, fun x hx => ?_,
    π, hmix, hπT, hstat⟩
  have hxj : ∀ j, ‖x j‖ ≤ 1 := fun j => by simpa using hx.1 j (Set.mem_univ _)
  have := hmixP x hx
  simp only [ballKernel_eq hρ0 hρ1, ballRet_of_norm_le (hxj _)] at this
  exact this

end BallJoint

/-! ### Theorem 121 (`mk:thm:large`) -/

section Thm121

open Filter Topology

open Mixes.Large

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The law `k(y, ·)` of `a(y) + M(y) V` with `V ∼ q`. -/
def affLaw (q : E → ℝ) (a : E) (M : E ≃L[ℝ] E) : Measure E :=
  (densMeas q).map fun v => a + M v

/-- **Theorem 121(a)** (`mk:thm:large`), given Theorem 113 (`Large.Thm113`, through
Corollary 115). Let `κ ≥ 1` and `(Q_j, q_j) ∈ 𝒢_d(A, L, r, R)`, and let `k_j(y, ·)` be the law of
`a_j(y) + M_j(y) V` with `V ∼ q_j`, where `‖M_j(y)‖, ‖M_j(y)⁻¹‖ ≤ κ`,
`a_j(y) + M_j(y) Q_j ⊆ K_j` and `a_j(y) + M_j(y) m_{q_j} = Γ y + c_j` on `K_j`; let
`Γ s + ∑ c_j = s`. There are `N` and `ε_n → 0`, depending only on `A, L, r, R, κ` (and `E`), such
that for `n = m + 1 ≥ N` and every `x ∈ 𝒯(K; s)` there are corrections `φ_j` with
`sup_{Q_j} |φ_j| ≤ ε_n` for which the law `P(x, ·)` of `(a_j(x_j) + M_j(x_j) V_j)_j`, with
`V` the conditioned product of the `q_j e^{φ_j} / ∫ q_j e^{φ_j}` on `∑ M_j(x_j) V_j =
s - ∑ a_j(x_j)`, is a joint mix of the `k_j(x_j, ·)` with sum `s`, concentrated on `𝒯`. -/
theorem thm121_a (h113 : Thm113 E) {A Lg r R κ : ℝ} (hA : 0 ≤ A) (hLg : 0 ≤ Lg) (hr : 0 < r)
    (hrR : r ≤ R) (hκ : 1 ≤ κ) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ (Q : Fin (m + 1) → Set E) (q : Fin (m + 1) → E → ℝ),
      (∀ j, InG A Lg r R (Q j) (q j)) →
      ∀ (K : Fin (m + 1) → Set E), (∀ j, MeasurableSet (K j)) → ∀ (a : Fin (m + 1) → E → E)
        (M : Fin (m + 1) → E → E ≃L[ℝ] E) (Γ : E →L[ℝ] E) (c : Fin (m + 1) → E) (s : E),
      (∀ j y, ‖(M j y : E →L[ℝ] E)‖ ≤ κ) → (∀ j y, ‖((M j y).symm : E →L[ℝ] E)‖ ≤ κ) →
      (∀ j, ∀ y ∈ K j, ∀ v ∈ Q j, a j y + M j y v ∈ K j) →
      (∀ j, ∀ y ∈ K j, a j y + M j y (meanD (q j)) = Γ y + c j) → Γ s + ∑ j, c j = s →
      ∀ x ∈ tset K s, ∃ φ : Fin (m + 1) → E → ℝ, (∀ j, ∀ v ∈ Q j, |φ j v| ≤ ε (m + 1)) ∧
        IsJointMix (fun j => affLaw (q j) (a j (x j)) (M j (x j)))
          ((condMeas ((lebT m (∑ j, M j (x j) (meanD (q j)))).map
            (MeasurableEquiv.piCongrRight fun j => affE (M j (x j)).symm 0))
            fun j => tiltD (q j) (φ j)).map fun v j => a j (x j) + M j (x j) (v j)) ∧
        ((condMeas ((lebT m (∑ j, M j (x j) (meanD (q j)))).map
            (MeasurableEquiv.piCongrRight fun j => affE (M j (x j)).symm 0))
            fun j => tiltD (q j) (φ j)).map fun v j => a j (x j) + M j (x j) (v j))
          (tset K s)ᶜ = 0 := by
  obtain ⟨N, ε, hε, H⟩ := cor115 h113 hA hLg hr hrR hκ
  refine ⟨N, ε, hε, fun m hm Q q hG K hKm a M Γ c s hM hMi haK hmean hs x hx => ?_⟩
  obtain ⟨φ, hφ, hprob, hmarg, hsum⟩ := H m hm Q q hG (fun j => M j (x j)) (fun j => hM j _)
    (fun j => hMi j _)
  set Pv := condMeas ((lebT m (∑ j, M j (x j) (meanD (q j)))).map
    (MeasurableEquiv.piCongrRight fun j => affE (M j (x j)).symm 0)) fun j => tiltD (q j) (φ j)
  set F : (Fin (m + 1) → E) → (Fin (m + 1) → E) := fun v j => a j (x j) + M j (x j) (v j)
  have hF : Measurable F := by
    refine measurable_pi_iff.2 fun j => ?_
    exact (measurable_const.add ((M j (x j)).continuous.measurable.comp (measurable_pi_apply j)))
  have hxj : ∀ j, x j ∈ K j := fun j => hx.1 j (Set.mem_univ _)
  have hmargF : ∀ j, (Pv.map F).map (fun y => y j) = affLaw (q j) (a j (x j)) (M j (x j)) := by
    intro j
    have hA : Measurable fun v : E => a j (x j) + M j (x j) v :=
      (continuous_const.add (M j (x j)).continuous).measurable
    rw [Measure.map_map (measurable_pi_apply j) hF, affLaw, ← hmarg j,
      Measure.map_map hA (measurable_pi_apply j)]
    rfl
  have hsumF : ∀ᵐ y ∂(Pv.map F), ∑ j, y j = s := by
    rw [ae_map_iff hF.aemeasurable]
    · refine hsum.mono fun v hv => ?_
      simp only [F, Finset.sum_add_distrib, hv]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => hmean j _ (hxj j)),
        Finset.sum_add_distrib, ← map_sum, hx.2, hs]
    · exact (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j)
        continuous_const).measurableSet
  refine ⟨φ, hφ, ⟨inferInstance, ⟨s, hsumF⟩, hmargF⟩, ?_⟩
  refine measure_mono_null (compl_tset_subset K s) (measure_union_null
    (measure_iUnion_null fun j => ?_) ?_)
  · have hA : Measurable fun v : E => a j (x j) + M j (x j) v :=
      (continuous_const.add (M j (x j)).continuous).measurable
    rw [← Measure.map_apply (measurable_pi_apply j) (hKm j).compl, hmargF j, affLaw,
      Measure.map_apply hA (hKm j).compl]
    have hQc : MeasurableSet (Q j)ᶜ := (hG j).compact.isClosed.measurableSet.compl
    refine measure_mono_null (show _ ⊆ (Q j)ᶜ from fun v hv hvQ => hv (haK j _ (hxj j) v hvQ)) ?_
    rw [densMeas, withDensity_apply _ hQc]
    rw [setLIntegral_congr_fun hQc (g := fun _ => 0) (fun y hy => by simp [(hG j).zero y hy])]
    simp
  · rw [← ae_iff]; exact hsumF

end Thm121

end Mixes
