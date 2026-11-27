import Mixes.Uniform

/-!
# Joint mixes of pairwise different distributions (Theorem as:thm:hetero, Corollary as:cor:hetero)

Draft 14, Section `as:sec:asym`, subsection "Pairwise different distributions".

* `AggSet F`: the aggregation set `𝒜(F_1, …, F_N)`, the set of the laws of `X_1 + ⋯ + X_N` over
  all couplings with `X_i ∼ F_i`, for a family indexed by a finite type.
* `H_lem_conc_a`, `H_prop_window`: Lemma `as:lem:conc`(a) and Proposition `as:prop:window`
  (case `d = 1`, `m ≥ 4`), proved elsewhere, enter as explicit hypotheses.
* `glue`: gluing two probability measures along a common image law (regular conditional
  distributions, `Measure.condKernel`).
* `absorb`: a family coupled by `as:lem:conc`(a) together with `m₂ ≥ 4` uniform distributions
  absorbs every prescribed law of the sum in a window.
* `thm_hetero`: Theorem `as:thm:hetero`; `cor_hetero`: Corollary `as:cor:hetero`.

The proof follows the paper (random selection of one index per block, individual tilts `t_k` that
do not depend on the choice in their own block, second group absorbing the rest by
Proposition `as:prop:window`) with one simplification: the variables of the first group, which
have the tilted laws `c + P_{H,γ_k}` given the selection, are coupled *together with* the
variables `Y_i` by Lemma `as:lem:conc`(a) (their laws are carried by intervals of length
`2H ≤ ℓ`), instead of by the indicators `ξ_k` and the complete mix `w`. The sum then stays within
`ℓ` of its conditional mean, so the conclusion holds even with the larger half-width
`m₂H/2 - ℓ` (`thm_hetero_strong`), of which the paper's `ρ = m₂H/2 - ℓ - H` is a special case.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Mixes.AsymHetero

/-! ## Aggregation sets and the hypotheses -/

/-- The aggregation set of a finite family of distributions on the line: the laws of the sum
`∑ i, X i` over all random vectors with `X i ∼ F i` (a coupling is a probability measure on
tuples with the given coordinate marginals). -/
def AggSet {ι : Type*} [Fintype ι] (F : ι → Measure ℝ) : Set (Measure ℝ) :=
  {L | ∃ P : Measure (ι → ℝ), IsProbabilityMeasure P ∧ (∀ i, P.map (fun x => x i) = F i) ∧
    P.map (fun x => ∑ i, x i) = L}

/-- Lemma `as:lem:conc`(a): distributions on the line, each carried by an interval of length at
most `ℓ`, can be coupled so that their sum takes its values in an interval of length at most `ℓ`. -/
def H_lem_conc_a : Prop :=
  ∀ (k : ℕ) (ℓ : ℝ) (T : Fin k → Measure ℝ), 0 ≤ ℓ → (∀ j, IsProbabilityMeasure (T j)) →
    (∀ j, ∃ α : ℝ, T j (Icc α (α + ℓ))ᶜ = 0) →
    ∃ P : Measure (Fin k → ℝ), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = T j) ∧
      ∃ α : ℝ, ∀ᵐ x ∂P, ∑ j, x j ∈ Icc α (α + ℓ)

/-- Proposition `as:prop:window` for `d = 1` and `m ≥ 4`: a probability measure with mean `mc`
carried by `[mc - mH/2, mc + mH/2]` belongs to `𝒜_m(U[c-H, c+H])`. -/
def H_prop_window : Prop :=
  ∀ (m : ℕ) (c H : ℝ) (ν : Measure ℝ), 4 ≤ m → 0 < H → IsProbabilityMeasure ν →
    ν (Icc (m * c - m * H / 2) (m * c + m * H / 2))ᶜ = 0 → ∫ x, x ∂ν = m * c →
    ν ∈ AggSet (fun _ : Fin m => unifI (c - H) (c + H))

/-! ## Generic lemmas -/

lemma measurable_sum_coord {ι : Type*} [Fintype ι] :
    Measurable (fun x : ι → ℝ => ∑ i, x i) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

/-- Reindexing an aggregation set along an equivalence. -/
lemma aggSet_of_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (F : κ → Measure ℝ)
    {L : Measure ℝ} (h : L ∈ AggSet (fun i => F (e i))) : L ∈ AggSet F := by
  obtain ⟨P, hP, hmarg, hsum⟩ := h
  have hm : Measurable (fun x : ι → ℝ => fun k => x (e.symm k)) :=
    by fun_prop
  refine ⟨P.map (fun x k => x (e.symm k)), inferInstance,
    fun k => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply k) hm]
    have := hmarg (e.symm k)
    simp only [Equiv.apply_symm_apply] at this
    exact this
  · rw [Measure.map_map measurable_sum_coord hm, ← hsum]
    congr 1
    funext x
    exact e.symm.sum_comp (fun i => x i)

/-- Translating every coordinate translates the sum. -/
lemma aggSet_shift {ι : Type*} [Fintype ι] (F : ι → Measure ℝ) (c : ι → ℝ) {L : Measure ℝ}
    (h : L ∈ AggSet F) :
    L.map (fun t => (∑ i, c i) + t) ∈ AggSet (fun i => (F i).map (fun t => c i + t)) := by
  obtain ⟨P, hP, hmarg, hsum⟩ := h
  have hm : Measurable (fun x : ι → ℝ => fun i => c i + x i) :=
    by fun_prop
  refine ⟨P.map (fun x i => c i + x i), inferInstance,
    fun i => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hm]
    show _ = (F i).map _
    rw [← hmarg i, Measure.map_map (by fun_prop : Measurable (fun t : ℝ => c i + t))
      (measurable_pi_apply i)]
    rfl
  · rw [Measure.map_map measurable_sum_coord hm, ← hsum,
      Measure.map_map (measurable_const_add _) measurable_sum_coord]
    congr 1
    funext x
    simp [Finset.sum_add_distrib]

/-- Gluing: two probability measures whose images under `f` and `g` agree have a coupling under
which `f` and `g` agree almost surely. -/
theorem glue {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace β]
    [Nonempty β] (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g) (h : μ.map f = ν.map g) :
    ∃ γ : Measure (α × β), IsProbabilityMeasure γ ∧ γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν ∧
      ∀ᵐ p ∂γ, f p.1 = g p.2 := by
  have hm : Measurable (fun y => (g y, y)) := hg.prodMk measurable_id
  set ν' : Measure (ℝ × β) := ν.map (fun y => (g y, y)) with hν'
  have : IsProbabilityMeasure ν' := by rw [hν']; infer_instance
  set κ := ν'.condKernel
  have hdis : ν'.fst ⊗ₘ κ = ν' := Measure.disintegrate ν' κ
  have hfst : ν'.fst = ν.map g := by
    rw [Measure.fst, hν', Measure.map_map measurable_fst hm]; rfl
  have hcomp : (κ.comap f hf) ∘ₘ μ = κ ∘ₘ (μ.map f) := by
    ext s hs
    rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_map (Kernel.measurable_coe _ hs) hf]
    rfl
  refine ⟨μ ⊗ₘ κ.comap f hf, inferInstance, Measure.fst_compProd _ _, ?_, ?_⟩
  · rw [← Measure.snd, Measure.snd_compProd, hcomp, h, ← hfst, ← Measure.snd_compProd, hdis,
      Measure.snd, hν', Measure.map_map measurable_snd hm]
    exact Measure.map_id
  · rw [ae_iff]
    have hS : MeasurableSet {p : α × β | ¬ f p.1 = g p.2} :=
      (measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd)).compl
    have hT : MeasurableSet {p : ℝ × β | ¬ p.1 = g p.2} :=
      (measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)).compl
    have key : ν' {p | ¬ p.1 = g p.2} = 0 := by
      rw [hν', Measure.map_apply hm hT]; simp
    rw [← hdis, Measure.compProd_apply hT, hfst, ← h] at key
    rw [Measure.compProd_apply hS]
    rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hT) hf] at key
    exact key

/-! ## Means of distributions carried by intervals -/

lemma ae_mem_of_carried {μ : Measure ℝ} {a b : ℝ} (h : μ (Icc a b)ᶜ = 0) :
    ∀ᵐ x ∂μ, x ∈ Icc a b := mem_ae_iff.2 h

lemma integrable_of_carried {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (h : μ (Icc a b)ᶜ = 0) : Integrable (fun x => x) μ := by
  refine Integrable.mono' (integrable_const (max |a| |b|)) aestronglyMeasurable_id ?_
  filter_upwards [ae_mem_of_carried h] with x hx
  simp only [Real.norm_eq_abs]
  exact abs_le_max_abs_abs hx.1 hx.2

lemma mean_mem_of_carried {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (h : μ (Icc a b)ᶜ = 0) : ∫ x, x ∂μ ∈ Icc a b := by
  have hi := integrable_of_carried h
  constructor
  · have := integral_mono_ae (integrable_const a) hi
      (by filter_upwards [ae_mem_of_carried h] with x hx using hx.1)
    simpa using this
  · have := integral_mono_ae hi (integrable_const b)
      (by filter_upwards [ae_mem_of_carried h] with x hx using hx.2)
    simpa using this

/-- The mean of an element of an aggregation set is the sum of the means. -/
lemma mean_of_aggSet {ι : Type*} [Fintype ι] {F : ι → Measure ℝ} {P : Measure (ι → ℝ)}
    [IsProbabilityMeasure P] (hmarg : ∀ i, P.map (fun x => x i) = F i)
    (hint : ∀ i, Integrable (fun x => x) (F i)) :
    ∫ t, t ∂(P.map (fun x => ∑ i, x i)) = ∑ i, ∫ t, t ∂(F i) := by
  have hint' : ∀ i, Integrable (fun x : ι → ℝ => x i) P := by
    intro i
    have := hint i
    rw [← hmarg i] at this
    exact (integrable_map_measure (f := fun x : ι → ℝ => x i) (g := fun t : ℝ => t)
      aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).1 this
  rw [integral_map measurable_sum_coord.aemeasurable measurable_id'.aestronglyMeasurable,
    integral_finsetSum _ (fun i _ => hint' i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hmarg i, integral_map (by fun_prop : Measurable (fun x : ι → ℝ => x i)).aemeasurable
    measurable_id'.aestronglyMeasurable]

/-! ## Uniform distributions, tilts and the remainder `T` -/

lemma unifI_of_lt' {l r : ℝ} (h : l < r) :
    unifI l r = (ENNReal.ofReal (r - l))⁻¹ • volume.restrict (Icc l r) := by
  simp [unifI, h]

lemma unifI_carried {l r : ℝ} (h : l ≤ r) : unifI l r (Icc l r)ᶜ = 0 := by
  rcases h.lt_or_eq with h | rfl
  · rw [unifI_of_lt' h, smul_apply, Measure.restrict_apply measurableSet_Icc.compl]
    simp
  · simp [unifI]

/-- If `U[l, r]`, `l < r`, gives no mass to the complement of `[α, β]`, then `[l, r] ⊆ [α, β]`. -/
lemma icc_subset_of_unifI_null {c H α β : ℝ} (hH : 0 < H)
    (h : unifI (c - H) (c + H) (Icc α β)ᶜ = 0) : Icc (c - H) (c + H) ⊆ Icc α β := by
  rw [unifI_of_lt' (by linarith), smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Icc.compl, mul_eq_zero] at h
  rcases h with h | h
  · simp at h
  have hsub : Icc (c - H) (c + H) ⊆ Icc α β := by
    by_contra hns
    have hαβ : ¬ (α ≤ c - H ∧ c + H ≤ β) := fun h' =>
      hns (Icc_subset_Icc h'.1 h'.2)
    rcases not_and_or.1 hαβ with h1 | h1
    · push Not at h1
      have : volume (Ico (c - H) (min α (c + H))) ≤ volume ((Icc α β)ᶜ ∩ Icc (c - H) (c + H)) := by
        apply measure_mono
        intro x hx
        refine ⟨fun hx' => ?_, hx.1, hx.2.le.trans (min_le_right _ _)⟩
        exact absurd (hx.2.trans_le (min_le_left _ _)) (not_lt.2 hx'.1)
      rw [h, Real.volume_Ico, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
      have : c - H < min α (c + H) := lt_min h1 (by linarith)
      linarith
    · push Not at h1
      have : volume (Ioc (max β (c - H)) (c + H)) ≤ volume ((Icc α β)ᶜ ∩ Icc (c - H) (c + H)) := by
        apply measure_mono
        intro x hx
        refine ⟨fun hx' => ?_, (le_max_right _ _).trans hx.1.le, hx.2⟩
        exact absurd ((le_max_left _ _).trans_lt hx.1) (not_lt.2 hx'.2)
      rw [h, Real.volume_Ioc, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
      have : max β (c - H) < c + H := max_lt h1 (by linarith)
      linarith
  exact hsub

lemma integral_unifI {l r : ℝ} (h : l ≤ r) : ∫ x, x ∂(unifI l r) = (l + r) / 2 := by
  rcases h.lt_or_eq with h | rfl
  · rw [unifI_of_lt' h, integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h.le, integral_id, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    have : r - l ≠ 0 := by linarith
    field_simp
    ring
  · simp [unifI]

/-- `U[c-H, c+H] = ½ U[c-H, c] + ½ U[c, c+H]`. -/
lemma unifI_halves {c H : ℝ} (hH : 0 < H) :
    unifI (c - H) (c + H) =
      ENNReal.ofReal (1 / 2) • unifI (c - H) c + ENNReal.ofReal (1 / 2) • unifI c (c + H) := by
  rw [unifI_of_lt' (by linarith : c - H < c + H), unifI_of_lt' (by linarith : c - H < c),
    unifI_of_lt' (by linarith : c < c + H), smul_smul, smul_smul]
  have hU : volume.restrict (Icc (c - H) (c + H)) =
      volume.restrict (Icc (c - H) c) + volume.restrict (Icc c (c + H)) := by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := c) (b := c + H)),
      ← Measure.restrict_union ((Set.Iic_disjoint_Ioi le_rfl).mono Set.Icc_subset_Iic_self
        Set.Ioc_subset_Ioi_self) measurableSet_Ioc,
      Set.Icc_union_Ioc_eq_Icc (by linarith) (by linarith)]
  have e1 : c + H - (c - H) = 2 * H := by ring
  have e2 : c - (c - H) = H := by ring
  have e3 : c + H - c = H := by ring
  rw [e1, e2, e3, hU, smul_add]
  have hs : ENNReal.ofReal (1 / 2) * (ENNReal.ofReal H)⁻¹ = (ENNReal.ofReal (2 * H))⁻¹ := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
      one_div, ENNReal.ofReal_inv_of_pos two_pos]
  rw [hs]

/-- The tilted uniform distribution `c + P_{H,γ}`: density `(1-γ)/(2H)` on `(c-H, c)` and
`(1+γ)/(2H)` on `(c, c+H)`. -/
def tilt (c H γ : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 - γ) / 2) • unifI (c - H) c + ENNReal.ofReal ((1 + γ) / 2) • unifI c (c + H)

lemma tilt_zero {c H : ℝ} (hH : 0 < H) : tilt c H 0 = unifI (c - H) (c + H) := by
  rw [unifI_halves hH, tilt]; norm_num

lemma tilt_isProb {c H γ : ℝ} (hγ : |γ| ≤ 1) : IsProbabilityMeasure (tilt c H γ) := by
  have := abs_le.1 hγ
  constructor
  rw [tilt, add_apply, smul_apply, smul_apply,
    (unifI_isProb _ _).measure_univ, (unifI_isProb _ _).measure_univ, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) (by linarith),
    show (1 - γ) / 2 + (1 + γ) / 2 = 1 by ring]
  simp

lemma tilt_carried {c H γ : ℝ} (hH : 0 < H) : tilt c H γ (Icc (c - H) (c + H))ᶜ = 0 := by
  rw [tilt, add_apply, smul_apply, smul_apply]
  have h1 : unifI (c - H) c (Icc (c - H) (c + H))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (Icc_subset_Icc le_rfl (by linarith)))
      (unifI_carried (by linarith))
  have h2 : unifI c (c + H) (Icc (c - H) (c + H))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (Icc_subset_Icc (by linarith) le_rfl))
      (unifI_carried (by linarith))
  simp [h1, h2]

lemma tilt_mean {c H γ : ℝ} (hH : 0 < H) (hγ : |γ| ≤ 1) :
    ∫ x, x ∂(tilt c H γ) = c + γ * H / 2 := by
  have := abs_le.1 hγ
  have := unifI_isProb (c - H) c
  have := unifI_isProb c (c + H)
  have i1 : Integrable (fun x : ℝ => x) (unifI (c - H) c) :=
    integrable_of_carried (unifI_carried (by linarith))
  have i2 : Integrable (fun x : ℝ => x) (unifI c (c + H)) :=
    integrable_of_carried (unifI_carried (by linarith))
  rw [tilt, integral_add_measure (i1.smul_measure ENNReal.ofReal_ne_top)
    (i2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_unifI (by linarith), integral_unifI (by linarith),
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
    smul_eq_mul]
  ring

lemma smul_le_smul_measure {μ ν : Measure ℝ} (h : μ ≤ ν) (a : ℝ≥0∞) : a • μ ≤ a • ν := by
  rw [Measure.le_iff'] at h ⊢
  intro s
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (h s)

/-- The remainder `T = (bF - U)/(b - 1)` of a distribution `F ≥ U/b`. -/
def restPart (b : ℕ) (F U : Measure ℝ) : Measure ℝ :=
  ((b : ℝ≥0∞) - 1)⁻¹ • ((b : ℝ≥0∞) • F - U)

section restPart

variable {b : ℕ} {F U : Measure ℝ} [IsProbabilityMeasure F] [IsProbabilityMeasure U]

omit [IsProbabilityMeasure F] [IsProbabilityMeasure U] in
lemma le_smul_of_inv_le (hb : 1 ≤ b) (h : (b : ℝ≥0∞)⁻¹ • U ≤ F) : U ≤ (b : ℝ≥0∞) • F := by
  have := smul_le_smul_measure h (b : ℝ≥0∞)
  rwa [smul_smul, ENNReal.mul_inv_cancel (by simp; omega) (by simp), one_smul] at this

omit [IsProbabilityMeasure F] in
lemma restPart_spec (hb : 2 ≤ b) (h : (b : ℝ≥0∞)⁻¹ • U ≤ F) :
    U + ((b : ℝ≥0∞) - 1) • restPart b F U = (b : ℝ≥0∞) • F := by
  have hb1 : (b : ℝ≥0∞) - 1 ≠ 0 := by
    have : (1 : ℝ≥0∞) < b := by exact_mod_cast (show 1 < b by omega)
    exact (tsub_pos_of_lt this).ne'
  have hb2 : (b : ℝ≥0∞) - 1 ≠ ⊤ := by simp
  rw [restPart, smul_smul, ENNReal.mul_inv_cancel hb1 hb2, one_smul, add_comm,
    Measure.sub_add_cancel_of_le (le_smul_of_inv_le (by omega) h)]

lemma restPart_isProb (hb : 2 ≤ b) (h : (b : ℝ≥0∞)⁻¹ • U ≤ F) :
    IsProbabilityMeasure (restPart b F U) := by
  have hb1 : (b : ℝ≥0∞) - 1 ≠ 0 := by
    have : (1 : ℝ≥0∞) < b := by exact_mod_cast (show 1 < b by omega)
    exact (tsub_pos_of_lt this).ne'
  constructor
  rw [restPart, smul_apply, Measure.sub_apply MeasurableSet.univ
    (le_smul_of_inv_le (by omega) h), smul_apply, measure_univ, measure_univ, smul_eq_mul,
    smul_eq_mul, mul_one, ENNReal.inv_mul_cancel hb1 (by simp)]

omit [IsProbabilityMeasure F] [IsProbabilityMeasure U] in
lemma restPart_carried {S : Set ℝ} (hS : F S = 0) : restPart b F U S = 0 := by
  rw [restPart, smul_apply, smul_eq_mul]
  have : ((b : ℝ≥0∞) • F - U) S = 0 := by
    refine le_antisymm ?_ bot_le
    refine (Measure.le_iff'.1 (Measure.sub_le (μ := (b : ℝ≥0∞) • F) (ν := U)) S).trans ?_
    simp [hS]
  simp [this]

end restPart

/-! ## Absorbing a prescribed sum by uniform distributions -/

lemma measurable_sumElim {I J : Type*} :
    Measurable (fun p : (I → ℝ) × (J → ℝ) => (Sum.elim p.1 p.2 : I ⊕ J → ℝ)) := by
  rw [measurable_pi_iff]
  rintro (i | j)
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The common step of Theorem `as:thm:hetero` and Proposition `as:prop:complete`: distributions
`G i` on intervals of length at most `ℓ`, coupled by Lemma `as:lem:conc`(a), together with `|J| ≥ 4`
uniform distributions `U[c_j - H, c_j + H]`, whose window `|J| H / 2` exceeds `ρ + ℓ`, have every
distribution with the mean `s` of the sum that is carried by `[s - ρ, s + ρ]` in their aggregation
set. -/
theorem absorb (hconc : H_lem_conc_a) (hwin : H_prop_window)
    {I J : Type*} [Fintype I] [Fintype J]
    (G : I → Measure ℝ) (hGp : ∀ i, IsProbabilityMeasure (G i)) {ℓ H ρ s : ℝ} (hℓ : 0 ≤ ℓ)
    (hG : ∀ i, ∃ α, G i (Icc α (α + ℓ))ᶜ = 0)
    (hJ : 4 ≤ Fintype.card J) (hH : 0 < H) (c : J → ℝ)
    (hρ : ρ + ℓ ≤ Fintype.card J * H / 2)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνc : ν (Icc (s - ρ) (s + ρ))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = s) (hs : s = ∑ i, ∫ x, x ∂(G i) + ∑ j, c j) :
    ν ∈ AggSet (Sum.elim G (fun j => unifI (c j - H) (c j + H))) := by
  classical
  -- Step 1: a coupling of the `G i` with a concentrated sum.
  set k := Fintype.card I
  let eI := Fintype.equivFin I
  obtain ⟨P0, hP0, hm0, α, hα⟩ :=
    hconc k ℓ (fun j => G (eI.symm j)) hℓ (fun j => hGp _) (fun j => hG _)
  set L := P0.map (fun x => ∑ j, x j) with hLdef
  have hL : L ∈ AggSet G := aggSet_of_equiv eI.symm G ⟨P0, hP0, hm0, rfl⟩
  obtain ⟨PI, hPI, hmI, hsI⟩ := hL
  have hLp : IsProbabilityMeasure L := by rw [hLdef]; infer_instance
  have hLc : L (Icc α (α + ℓ))ᶜ = 0 := by
    rw [hLdef, Measure.map_apply measurable_sum_coord measurableSet_Icc.compl]
    exact ae_iff.1 hα
  have hGi : ∀ i, Integrable (fun x => x) (G i) := fun i => by
    obtain ⟨β, hβ⟩ := hG i
    have := hGp i
    exact integrable_of_carried hβ
  set M := ∑ i, ∫ x, x ∂(G i) with hM
  have hLm : ∫ x, x ∂L = M := by rw [← hsI]; exact mean_of_aggSet hmI hGi
  have hMα : M ∈ Icc α (α + ℓ) := hLm ▸ mean_mem_of_carried hLc
  -- Step 2: the law that the uniform block has to produce.
  set C := ∑ j, c j with hC
  set m := Fintype.card J
  have hsub : Measurable (fun p : ℝ × ℝ => p.2 - p.1) := by fun_prop
  set μ2 := (L.prod ν).map (fun p => p.2 - p.1) with hμ2
  have hμ2p : IsProbabilityMeasure μ2 := by rw [hμ2]; infer_instance
  have hae : ∀ᵐ p ∂(L.prod ν), p.1 ∈ Icc α (α + ℓ) ∧ p.2 ∈ Icc (s - ρ) (s + ρ) := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := L) (ν := ν)).ae (ae_mem_of_carried hLc)
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := L) (ν := ν)).ae (ae_mem_of_carried hνc)
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  set μ3 := μ2.map (fun t => t - C) with hμ3
  have hμ3p : IsProbabilityMeasure μ3 := by rw [hμ3]; infer_instance
  have hμ3c : μ3 (Icc (m * 0 - m * H / 2) (m * 0 + m * H / 2))ᶜ = 0 := by
    rw [hμ3, hμ2, Measure.map_map (by fun_prop) hsub,
      Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hcon
    apply hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
    have := hMα.1
    have := hMα.2
    simp only [Function.comp, mem_Icc, mul_zero, zero_sub, zero_add]
    constructor <;> linarith
  have hint1 : Integrable (fun p : ℝ × ℝ => p.1) (L.prod ν) := by
    have := integrable_of_carried hLc
    have h := Measure.map_fst_prod (μ := L) (ν := ν)
    rw [measure_univ, one_smul] at h
    rw [← h] at this
    exact (integrable_map_measure (f := Prod.fst) (g := fun t : ℝ => t)
      measurable_id'.aestronglyMeasurable measurable_fst.aemeasurable).1 this
  have hint2 : Integrable (fun p : ℝ × ℝ => p.2) (L.prod ν) := by
    have := integrable_of_carried hνc
    have h := Measure.map_snd_prod (μ := L) (ν := ν)
    rw [measure_univ, one_smul] at h
    rw [← h] at this
    exact (integrable_map_measure (f := Prod.snd) (g := fun t : ℝ => t)
      measurable_id'.aestronglyMeasurable measurable_snd.aemeasurable).1 this
  have hμ3m : ∫ x, x ∂μ3 = m * 0 := by
    rw [hμ3, hμ2, Measure.map_map (by fun_prop) hsub,
      integral_map (by fun_prop) measurable_id'.aestronglyMeasurable]
    simp only [Function.comp]
    rw [integral_sub (f := fun x : ℝ × ℝ => x.2 - x.1) (g := fun _ => C) (hint2.sub hint1)
      (integrable_const C), integral_sub (f := fun x : ℝ × ℝ => x.2) (g := fun x => x.1) hint2 hint1]
    have e1 : ∫ p, p.1 ∂(L.prod ν) = M := by
      rw [← hLm, ← integral_map measurable_fst.aemeasurable measurable_id'.aestronglyMeasurable,
        Measure.map_fst_prod, measure_univ, one_smul]
    have e2 : ∫ p, p.2 ∂(L.prod ν) = s := by
      rw [← hνm, ← integral_map measurable_snd.aemeasurable measurable_id'.aestronglyMeasurable,
        Measure.map_snd_prod, measure_univ, one_smul]
    rw [e1, e2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
      mul_zero]
    linarith
  have hw := hwin m 0 H μ3 hJ hH hμ3p hμ3c hμ3m
  have hwJ : μ3 ∈ AggSet (fun _ : J => unifI (0 - H) (0 + H)) :=
    aggSet_of_equiv (Fintype.equivFin J).symm (fun _ : J => unifI (0 - H) (0 + H)) hw
  have hQ := aggSet_shift _ c hwJ
  have e3 : μ3.map (fun t => (∑ j, c j) + t) = μ2 := by
    rw [hμ3, Measure.map_map (by fun_prop) (by fun_prop)]
    conv_rhs => rw [← Measure.map_id (μ := μ2)]
    congr 1
    funext t
    simp [hC]
  have e4 : (fun j => (unifI (0 - H) (0 + H)).map (fun t => c j + t)) =
      fun j => unifI (c j - H) (c j + H) := by
    funext j
    rw [Mixes.map_unifI_const_add]
    congr 1 <;> ring
  rw [e3, e4] at hQ
  obtain ⟨Q, hQp, hQm, hQs⟩ := hQ
  -- Step 3: gluing.
  have hf : Measurable (fun p : (I → ℝ) × ℝ => p.2 - ∑ i, p.1 i) :=
    measurable_snd.sub (measurable_sum_coord.comp measurable_fst)
  have hglue : (PI.prod ν).map (fun p => p.2 - ∑ i, p.1 i) = Q.map (fun y => ∑ j, y j) := by
    rw [hQs, hμ2, ← hsI, ← Measure.map_id (μ := ν), Measure.map_prod_map _ _ measurable_sum_coord
      measurable_id, Measure.map_map hsub (measurable_sum_coord.prodMap measurable_id), Measure.map_id]
    rfl
  obtain ⟨γ, hγp, hγ1, hγ2, hγae⟩ := glue (PI.prod ν) Q hf measurable_sum_coord hglue
  have hE : Measurable (fun p : ((I → ℝ) × ℝ) × (J → ℝ) => (Sum.elim p.1.1 p.2 : I ⊕ J → ℝ)) :=
    measurable_sumElim.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  refine ⟨γ.map (fun p => Sum.elim p.1.1 p.2), inferInstance, ?_, ?_⟩
  · rintro (i | j)
    · rw [Measure.map_map (measurable_pi_apply _) hE]
      have : ((fun x : I ⊕ J → ℝ => x (Sum.inl i)) ∘ fun p : ((I → ℝ) × ℝ) × (J → ℝ) =>
          (Sum.elim p.1.1 p.2 : I ⊕ J → ℝ)) = (fun q : (I → ℝ) × ℝ => q.1 i) ∘ Prod.fst := rfl
      have h2 : (fun q : (I → ℝ) × ℝ => q.1 i) = (fun x : I → ℝ => x i) ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map (by fun_prop) measurable_fst, hγ1, h2,
        ← Measure.map_map (by fun_prop : Measurable (fun x : I → ℝ => x i)) measurable_fst,
        Measure.map_fst_prod, measure_univ, one_smul, hmI]
      rfl
    · rw [Measure.map_map (measurable_pi_apply _) hE]
      have : ((fun x : I ⊕ J → ℝ => x (Sum.inr j)) ∘ fun p : ((I → ℝ) × ℝ) × (J → ℝ) =>
          (Sum.elim p.1.1 p.2 : I ⊕ J → ℝ)) = (fun y : J → ℝ => y j) ∘ Prod.snd := rfl
      rw [this, ← Measure.map_map (measurable_pi_apply j) measurable_snd, hγ2, hQm]
      rfl
  · rw [Measure.map_map measurable_sum_coord hE]
    have : (fun x : I ⊕ J → ℝ => ∑ i, x i) ∘ (fun p : ((I → ℝ) × ℝ) × (J → ℝ) =>
        (Sum.elim p.1.1 p.2 : I ⊕ J → ℝ)) =ᵐ[γ] (fun q : (I → ℝ) × ℝ => q.2) ∘ Prod.fst := by
      filter_upwards [hγae] with p hp
      simp only [Function.comp, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      linarith
    rw [Measure.map_congr this, ← Measure.map_map measurable_snd measurable_fst, hγ1,
      Measure.map_snd_prod, measure_univ, one_smul]

/-! ## The selection and the tilts -/

section Selection

variable {K : Type*} [Fintype K] [DecidableEq K] {b : ℕ}

/-- `∑_o [o k = x] φ(o j) = 0` over all selections `o : K → Fin b` if `j ≠ k` and `∑ φ = 0`. -/
lemma sum_sel_eq_zero (k j : K) (hjk : j ≠ k) (x : Fin b) (φ : Fin b → ℝ)
    (hφ : ∑ y, φ y = 0) :
    ∑ o : K → Fin b, (if o k = x then φ (o j) else 0) = 0 := by
  have h : ∀ o : K → Fin b, (if o k = x then φ (o j) else 0) =
      ∏ i, ((if i = k then (if o i = x then (1 : ℝ) else 0) else 1) *
        (if i = j then φ (o i) else 1)) := by
    intro o
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k,
      Finset.prod_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, ite_true]
    split_ifs <;> simp
  simp_rw [h]
  rw [← Fintype.prod_sum (fun i y => (if i = k then (if y = x then (1 : ℝ) else 0) else 1) *
    (if i = j then φ y else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hjk, hφ]

/-- The number of selections with `o k = x` is `b ^ (|K| - 1)`. -/
lemma card_sel (k : K) (x : Fin b) :
    (Finset.univ.filter (fun o : K → Fin b => o k = x)).card = b ^ (Fintype.card K - 1) := by
  rw [Finset.card_filter]
  have h : ∀ o : K → Fin b, (if o k = x then 1 else 0 : ℕ) =
      ∏ i, (if i = k then (if o i = x then 1 else 0) else 1) := by
    intro o
    rw [Finset.prod_ite_eq' Finset.univ k]
    simp
  simp_rw [h]
  rw [← Fintype.prod_sum (fun i y => (if i = k then (if y = x then 1 else 0) else 1 : ℕ))]
  have : ∀ i, (∑ y : Fin b, (if i = k then (if y = x then 1 else 0) else 1 : ℕ)) =
      if i = k then 1 else b := by
    intro i
    split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    Finset.filter_ne' Finset.univ k, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ]

end Selection

section Tilts

variable {m1 m2 b : ℕ}

/-- The blocks: the first group `Fin m1` and the second group `Fin m2`. -/
abbrev Blk (m1 m2 : ℕ) := Fin m1 ⊕ Fin m2

/-- The weights of the tilts: `t_k = ∑_j wt k j e_j`, i.e.
`t_k = (∑_{j ≤ m₁, j ≠ k} e_j)/(m₁ - 1) + (∑_{j > m₁} e_j)/m₁` for `k` in the first group, and
`0` in the second. -/
def wt (m1 m2 : ℕ) : Blk m1 m2 → Blk m1 m2 → ℝ
  | Sum.inl k, Sum.inl j => if j = k then 0 else 1 / ((m1 : ℝ) - 1)
  | Sum.inl _, Sum.inr _ => 1 / (m1 : ℝ)
  | Sum.inr _, _ => 0

lemma wt_self (k : Blk m1 m2) : wt m1 m2 k k = 0 := by
  rcases k with k | k <;> simp [wt]

lemma abs_wt_le (hm1 : 2 ≤ m1) (k j : Blk m1 m2) : |wt m1 m2 k j| ≤ 1 / ((m1 : ℝ) - 1) := by
  have h1 : (2 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hpos : 0 < (m1 : ℝ) - 1 := by linarith
  rcases k with k | k <;> rcases j with j | j <;> simp only [wt]
  · split_ifs
    · simp only [abs_zero]; positivity
    · rw [abs_of_pos (by positivity)]
  · rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le hpos (by linarith)
  · simp only [abs_zero]; positivity
  · simp only [abs_zero]; positivity

lemma sum_wt (hm1 : 2 ≤ m1) (j : Blk m1 m2) : ∑ k, wt m1 m2 k j = 1 := by
  have h1 : (2 : ℝ) ≤ m1 := by exact_mod_cast hm1
  rw [Fintype.sum_sum_type]
  rcases j with j | j <;> simp only [wt, Finset.sum_const_zero, add_zero]
  · rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
      Finset.filter_ne Finset.univ j, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
    have : (m1 : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    simp
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m1 : ℝ) ≠ 0 := by linarith
    field_simp

/-- The block means `ā_k`. -/
def abar (a : Blk m1 m2 × Fin b → ℝ) (k : Blk m1 m2) : ℝ := (∑ x, a (k, x)) / b

/-- The deviations `e_k = a_{o_k} - ā_k` of a selection. -/
def dev (a : Blk m1 m2 × Fin b → ℝ) (o : Blk m1 m2 → Fin b) (k : Blk m1 m2) : ℝ :=
  a (k, o k) - abar a k

/-- The tilts `t_k`. -/
def tlt (a : Blk m1 m2 × Fin b → ℝ) (o : Blk m1 m2 → Fin b) (k : Blk m1 m2) : ℝ :=
  ∑ j, wt m1 m2 k j * dev a o j

lemma tlt_inr (a : Blk m1 m2 × Fin b → ℝ) (o : Blk m1 m2 → Fin b) (k : Fin m2) :
    tlt a o (Sum.inr k) = 0 := by
  simp [tlt, wt]

lemma sum_tlt (hm1 : 2 ≤ m1) (a : Blk m1 m2 × Fin b → ℝ) (o : Blk m1 m2 → Fin b) :
    ∑ k, tlt a o k = ∑ k, dev a o k := by
  simp only [tlt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, sum_wt hm1, one_mul]

lemma abs_tlt_le (hm1 : 2 ≤ m1) (a : Blk m1 m2 × Fin b → ℝ) (o : Blk m1 m2 → Fin b)
    (k : Blk m1 m2) : |tlt a o k| ≤ 1 / ((m1 : ℝ) - 1) * ∑ j, |dev a o j| := by
  simp only [tlt]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_wt_le hm1 k j) (abs_nonneg _)

lemma sum_sel_tlt (hb : 1 ≤ b) (a : Blk m1 m2 × Fin b → ℝ) (k : Blk m1 m2) (x : Fin b) :
    ∑ o : Blk m1 m2 → Fin b, (if o k = x then tlt a o k else 0) = 0 := by
  classical
  have h : ∀ o : Blk m1 m2 → Fin b, (if o k = x then tlt a o k else 0) =
      ∑ j, wt m1 m2 k j * (if o k = x then dev a o j else 0) := by
    intro o
    split_ifs <;> simp [tlt]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [← Finset.mul_sum]
  by_cases hjk : j = k
  · rw [hjk, wt_self, zero_mul]
  · have hz := sum_sel_eq_zero k j hjk x (fun y => a (j, y) - abar a j) ?_
    · beta_reduce at hz
      simp only [dev]
      rw [hz, mul_zero]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, abar]
    field_simp
    ring

end Tilts

/-! ## The laws given a selection -/

section Core

variable {m1 m2 b : ℕ}

/-- The law of the `p`-th variable given the selection `o`: the tilted uniform distribution
`c_p + P_{H, 2t_k/H}` if `p = (k, o k)` is selected, and the remainder `T_p` otherwise. -/
def selLaw (H : ℝ) (c : Blk m1 m2 × Fin b → ℝ) (T : Blk m1 m2 × Fin b → Measure ℝ)
    (a : Blk m1 m2 × Fin b → ℝ) (o : Blk m1 m2 → Fin b) (p : Blk m1 m2 × Fin b) : Measure ℝ :=
  if p.2 = o p.1 then tilt (c p) H (2 * tlt a o p.1 / H) else T p

lemma selLaw_isProb {H : ℝ} {c : Blk m1 m2 × Fin b → ℝ} {T : Blk m1 m2 × Fin b → Measure ℝ}
    {a : Blk m1 m2 × Fin b → ℝ} (hT : ∀ p, IsProbabilityMeasure (T p))
    (hγ : ∀ o k, |2 * tlt a o k / H| ≤ 1) (o : Blk m1 m2 → Fin b) (p : Blk m1 m2 × Fin b) :
    IsProbabilityMeasure (selLaw H c T a o p) := by
  unfold selLaw; split_ifs
  · exact tilt_isProb (hγ o p.1)
  · exact hT p

lemma selLaw_carried {H ℓ : ℝ} (hH : 0 < H) (h2H : 2 * H ≤ ℓ) {c : Blk m1 m2 × Fin b → ℝ}
    {T : Blk m1 m2 × Fin b → Measure ℝ} {a : Blk m1 m2 × Fin b → ℝ}
    (hTc : ∀ p, ∃ α, T p (Icc α (α + ℓ))ᶜ = 0) (o : Blk m1 m2 → Fin b) (p : Blk m1 m2 × Fin b) :
    ∃ α, selLaw H c T a o p (Icc α (α + ℓ))ᶜ = 0 := by
  unfold selLaw; split_ifs
  · exact ⟨c p - H, measure_mono_null (compl_subset_compl.2 (Icc_subset_Icc le_rfl (by linarith)))
      (tilt_carried hH)⟩
  · exact hTc p

lemma mean_selLaw {H : ℝ} (hH : 0 < H) {c : Blk m1 m2 × Fin b → ℝ}
    {T : Blk m1 m2 × Fin b → Measure ℝ} {a : Blk m1 m2 × Fin b → ℝ}
    (ha : ∀ p, ∫ x, x ∂(T p) = c p + a p) (hγ : ∀ o k, |2 * tlt a o k / H| ≤ 1)
    (o : Blk m1 m2 → Fin b) (p : Blk m1 m2 × Fin b) :
    ∫ x, x ∂(selLaw H c T a o p) =
      c p + a p + (if p.2 = o p.1 then tlt a o p.1 - a p else 0) := by
  unfold selLaw; split_ifs
  · rw [tilt_mean hH (hγ o p.1)]; field_simp; ring
  · rw [ha p]; ring

/-- The selection identity `(as:eq:select)`: given any selection, the means add up to `s`. -/
lemma sum_mean_selLaw (hm1 : 2 ≤ m1) {H : ℝ} (hH : 0 < H)
    {c : Blk m1 m2 × Fin b → ℝ} {T : Blk m1 m2 × Fin b → Measure ℝ} {a : Blk m1 m2 × Fin b → ℝ}
    (ha : ∀ p, ∫ x, x ∂(T p) = c p + a p) (hγ : ∀ o k, |2 * tlt a o k / H| ≤ 1)
    (o : Blk m1 m2 → Fin b) :
    ∑ p, ∫ x, x ∂(selLaw H c T a o p) = ∑ p, (c p + (1 - 1 / (b : ℝ)) * a p) := by
  simp_rw [mean_selLaw hH ha hγ o]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ p : Blk m1 m2 × Fin b, (if p.2 = o p.1 then tlt a o p.1 - a p else 0) =
      ∑ k, (tlt a o k - a (k, o k)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_ite_eq' Finset.univ (o k)]
    simp
  rw [h1, Finset.sum_sub_distrib, sum_tlt hm1]
  simp only [dev, abar, Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Fintype.sum_prod_type (fun p => a p),
    ← Finset.sum_div, Fintype.sum_prod_type (fun p => (1 - 1 / (b : ℝ)) * a p)]
  simp_rw [← Finset.mul_sum]
  ring

/-- The mixture over the selections has the marginals `F_p`. -/
lemma sum_selLaw (hm1 : 2 ≤ m1) (hb : 2 ≤ b) {H : ℝ} (hH : 0 < H)
    {c : Blk m1 m2 × Fin b → ℝ} {T F : Blk m1 m2 × Fin b → Measure ℝ}
    {a : Blk m1 m2 × Fin b → ℝ}
    (hspec : ∀ p, unifI (c p - H) (c p + H) + ((b : ℝ≥0∞) - 1) • T p = (b : ℝ≥0∞) • F p)
    (hγ : ∀ o k, |2 * tlt a o k / H| ≤ 1) (p : Blk m1 m2 × Fin b) :
    ∑ o, selLaw H c T a o p = ((b : ℝ≥0∞) ^ (m1 + m2)) • F p := by
  classical
  obtain ⟨k, x⟩ := p
  set N := b ^ (m1 + m2 - 1) with hN
  have hcard : (Finset.univ.filter (fun o : Blk m1 m2 → Fin b => x = o k)).card = N := by
    calc (Finset.univ.filter (fun o : Blk m1 m2 → Fin b => x = o k)).card
        = (Finset.univ.filter (fun o : Blk m1 m2 → Fin b => o k = x)).card := by
          congr 1; ext o; simp [eq_comm]
      _ = N := by rw [card_sel]; simp [hN]
  have hpow : b ^ (m1 + m2) = N * b := by
    rw [hN, ← pow_succ]; congr 1; omega
  have hcard' : (Finset.univ.filter (fun o : Blk m1 m2 → Fin b => ¬ x = o k)).card =
      N * (b - 1) := by
    have h : (Finset.univ.filter (fun o : Blk m1 m2 → Fin b => x = o k)).card +
        (Finset.univ.filter (fun o : Blk m1 m2 → Fin b => ¬ x = o k)).card = b ^ (m1 + m2) := by
      rw [Finset.card_filter_add_card_filter_not]; simp
    rw [hcard, hpow] at h
    rw [Nat.mul_sub_one]
    omega
  simp only [selLaw]
  rw [Finset.sum_ite, Finset.sum_const, hcard']
  -- the selected part
  have hzero : ∑ o ∈ Finset.univ.filter (fun o : Blk m1 m2 → Fin b => x = o k),
      2 * tlt a o k / H = 0 := by
    rw [Finset.sum_filter]
    have := sum_sel_tlt (by omega : 1 ≤ b) a k x
    have h2 : ∀ o : Blk m1 m2 → Fin b, (if x = o k then 2 * tlt a o k / H else 0) =
        2 / H * (if o k = x then tlt a o k else 0) := by
      intro o
      by_cases h : o k = x
      · simp only [h, ite_true]; ring
      · simp only [h, Ne.symm h, ite_false, mul_zero]
    simp_rw [h2]
    rw [← Finset.mul_sum, this, mul_zero]
  have hsel : ∑ o ∈ Finset.univ.filter (fun o : Blk m1 m2 → Fin b => x = o k),
      tilt (c (k, x)) H (2 * tlt a o k / H) = (N : ℝ≥0∞) • unifI (c (k, x) - H) (c (k, x) + H) := by
    simp only [tilt, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hγ' := fun o => abs_le.1 (hγ o k)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => by linarith [(hγ' o).2]),
      ← ENNReal.ofReal_sum_of_nonneg (fun o _ => by linarith [(hγ' o).1]),
      ← Finset.sum_div, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hzero,
      Finset.sum_const, hcard, unifI_halves hH, smul_add, smul_smul, smul_smul]
    simp only [nsmul_eq_mul, mul_one, sub_zero, add_zero]
    congr 2 <;>
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
  rw [hsel]
  have hb1 : ((b - 1 : ℕ) : ℝ≥0∞) = (b : ℝ≥0∞) - 1 := by
    rw [ENNReal.natCast_sub, Nat.cast_one]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, Nat.cast_mul, hb1, ← smul_smul, ← smul_add, hspec (k, x),
    smul_smul, hN]
  congr 1
  have hm : m1 + m2 = (m1 + m2 - 1) + 1 := by omega
  conv_rhs => rw [hm]
  push_cast
  rw [pow_succ]

end Core

/-! ## Blocks of consecutive indices -/

/-- If the blocks `{k} × Fin b` are ordered (every value in block `k` is at most every value in a
later block) and all values lie in `[-D, D]`, then the deviations of any selection satisfy
`∑_k |g(k, o k) - ḡ_k| ≤ 2D`. -/
lemma sum_abs_dev_fin {M b : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b) (g : Fin M × Fin b → ℝ) {D : ℝ}
    (hsort : ∀ k k' : Fin M, k < k' → ∀ x y, g (k, x) ≤ g (k', y)) (hD : ∀ p, |g p| ≤ D)
    (o : Fin M → Fin b) :
    ∑ k, |g (k, o k) - (∑ x, g (k, x)) / b| ≤ 2 * D := by
  have hne : (Finset.univ : Finset (Fin b)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set lo : Fin M → ℝ := fun k => Finset.univ.inf' hne (fun x => g (k, x)) with hlo
  set hi : Fin M → ℝ := fun k => Finset.univ.sup' hne (fun x => g (k, x)) with hhi
  have hlo_le : ∀ k x, lo k ≤ g (k, x) := fun k x => Finset.inf'_le _ (Finset.mem_univ x)
  have hle_hi : ∀ k x, g (k, x) ≤ hi k := fun k x => Finset.le_sup' (fun x => g (k, x))
    (Finset.mem_univ x)
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hdev : ∀ k, |g (k, o k) - (∑ x, g (k, x)) / b| ≤ hi k - lo k := by
    intro k
    have h1 : (b : ℝ) * lo k ≤ ∑ x, g (k, x) := by
      have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hlo_le k x)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have h2 : ∑ x, g (k, x) ≤ (b : ℝ) * hi k := by
      have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hle_hi k x)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have h3 : lo k ≤ (∑ x, g (k, x)) / b := by rw [le_div_iff₀ hb']; linarith
    have h4 : (∑ x, g (k, x)) / b ≤ hi k := by rw [div_le_iff₀ hb']; linarith
    have := hlo_le k (o k)
    have := hle_hi k (o k)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- telescoping
  set L : ℕ → ℝ := fun j => if h : j < M then lo ⟨j, h⟩ else hi ⟨M - 1, by omega⟩ with hL
  have hstep : ∀ k : Fin M, hi k - lo k ≤ L (k + 1) - L k := by
    intro k
    have hLk : L k = lo k := by simp [hL, k.2]
    rw [hLk]
    by_cases hk : (k : ℕ) + 1 < M
    · have : L (k + 1) = lo ⟨k + 1, hk⟩ := by simp [hL, hk]
      rw [this]
      have : hi k ≤ lo ⟨k + 1, hk⟩ := by
        apply Finset.sup'_le
        intro x _
        apply Finset.le_inf'
        intro y _
        exact hsort k ⟨k + 1, hk⟩ (Fin.mk_lt_mk.2 (by simp)) x y
      linarith
    · have hkM : (k : ℕ) = M - 1 := by omega
      have : L (k + 1) = hi ⟨M - 1, by omega⟩ := by simp [hL, hk]
      rw [this]
      have : k = ⟨M - 1, by omega⟩ := Fin.ext hkM
      rw [← this]
  calc ∑ k, |g (k, o k) - (∑ x, g (k, x)) / b| ≤ ∑ k : Fin M, (L (k + 1) - L k) :=
        Finset.sum_le_sum (fun k _ => (hdev k).trans (hstep k))
    _ = L M - L 0 := by
        rw [Fin.sum_univ_eq_sum_range (fun j => L (j + 1) - L j), Finset.sum_range_sub]
    _ ≤ 2 * D := by
        have h0 : L 0 = lo ⟨0, by omega⟩ := by simp [hL, show 0 < M by omega]
        have hM' : L M = hi ⟨M - 1, by omega⟩ := by simp [hL]
        rw [h0, hM']
        obtain ⟨x1, -, hx1⟩ := Finset.exists_mem_eq_sup' hne (fun x => g (⟨M - 1, by omega⟩, x))
        obtain ⟨x0, -, hx0⟩ := Finset.exists_mem_eq_inf' hne (fun x => g (⟨0, by omega⟩, x))
        simp only [hhi, hlo] at hx1 hx0 ⊢
        rw [hx1, hx0]
        have := abs_le.1 (hD (⟨M - 1, by omega⟩, x1))
        have := abs_le.1 (hD (⟨0, by omega⟩, x0))
        linarith

/-! ## The theorem with the blocks given -/

section Main

variable {m1 m2 b : ℕ} {R : Type*} [Fintype R]

/-- Given the selection `o`, the laws `selLaw … o` together with the other distributions have
every distribution of the window in their aggregation set. -/
theorem perSel (hconc : H_lem_conc_a) (hwin : H_prop_window) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2)
    {H ℓ ρ s : ℝ} (hH : 0 < H) (h2H : 2 * H ≤ ℓ)
    {c : Blk m1 m2 × Fin b → ℝ} {T : Blk m1 m2 × Fin b → Measure ℝ} {a : Blk m1 m2 × Fin b → ℝ}
    (hT : ∀ p, IsProbabilityMeasure (T p)) (hTc : ∀ p, ∃ α, T p (Icc α (α + ℓ))ᶜ = 0)
    (ha : ∀ p, ∫ x, x ∂(T p) = c p + a p) (hγ : ∀ o k, |2 * tlt a o k / H| ≤ 1)
    (Fo : R → Measure ℝ) (hFo : ∀ r, IsProbabilityMeasure (Fo r))
    (hFoc : ∀ r, ∃ α, Fo r (Icc α (α + ℓ))ᶜ = 0)
    (hρ : ρ + ℓ ≤ m2 * H / 2) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc (s - ρ) (s + ρ))ᶜ = 0) (hνm : ∫ x, x ∂ν = s)
    (hs : s = ∑ p, (c p + (1 - 1 / (b : ℝ)) * a p) + ∑ r, ∫ x, x ∂(Fo r))
    (o : Blk m1 m2 → Fin b) :
    ν ∈ AggSet (Sum.elim (selLaw H c T a o) Fo) := by
  classical
  set f : Fin m2 → Blk m1 m2 × Fin b := fun j => (Sum.inr j, o (Sum.inr j)) with hf
  have hfi : Function.Injective f := by
    intro j j' h
    simp only [hf, Prod.mk.injEq, Sum.inr.injEq] at h
    exact h.1
  set q : Blk m1 m2 × Fin b → Prop := fun p => p ∈ Set.range f with hq
  have hqsel : ∀ p, q p → selLaw H c T a o p = unifI (c p - H) (c p + H) := by
    rintro p ⟨j, rfl⟩
    simp only [selLaw, hf, ite_true, tlt_inr, mul_zero, zero_div]
    exact tilt_zero hH
  have hcardJ : Fintype.card {p // q p} = m2 := by
    exact (Fintype.card_congr (Equiv.ofInjective f hfi).symm).trans (Fintype.card_fin m2)
  have key := absorb hconc hwin (I := {p // ¬ q p} ⊕ R) (J := {p // q p}) (ℓ := ℓ) (ρ := ρ) (s := s)
    (Sum.elim (fun p => selLaw H c T a o p.1) Fo) ?_ (by linarith) ?_ (by rw [hcardJ]; exact hm2)
    hH (fun j => c j.1) (by rw [hcardJ]; exact hρ) ν hνc hνm ?_
  · let e : ({p // ¬ q p} ⊕ R) ⊕ {p // q p} ≃ (Blk m1 m2 × Fin b) ⊕ R :=
      (Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
        ((Equiv.sumAssoc _ _ _).symm.trans
          (Equiv.sumCongr ((Equiv.sumComm _ _).trans (Equiv.sumCompl q)) (Equiv.refl R))))
    refine aggSet_of_equiv e _ ?_
    convert key using 2
    funext i
    rcases i with ((p | r) | j)
    · simp [e]
    · simp [e]
    · simpa [e] using hqsel j.1 j.2
  · rintro (p | r)
    · exact selLaw_isProb hT hγ o p.1
    · exact hFo r
  · rintro (p | r)
    · exact selLaw_carried hH h2H hTc o p.1
    · exact hFoc r
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ j : {p // q p}, c j.1 = ∑ j : {p // q p}, ∫ x, x ∂(selLaw H c T a o j.1) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hqsel j.1 j.2, integral_unifI (by linarith)]
      ring
    rw [h1]
    have h2 := Fintype.sum_subtype_add_sum_subtype q (fun p => ∫ x, x ∂(selLaw H c T a o p))
    rw [sum_mean_selLaw hm1 hH ha hγ o] at h2
    rw [hs, ← h2]
    have e : ∀ x y z : ℝ, x + y + z = y + z + x := fun _ _ _ => by ring
    convert e _ _ _ using 3
    exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

lemma map_finset_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (s : Finset ι) (μ : ι → Measure α) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  rw [← Measure.mapₗ_apply_of_measurable hf, map_sum]
  exact Finset.sum_congr rfl (fun i _ => Measure.mapₗ_apply_of_measurable hf _)

lemma mean_of_spec {b : ℕ} (hb : 2 ≤ b) {F U T : Measure ℝ} [IsProbabilityMeasure F]
    [IsProbabilityMeasure U] [IsProbabilityMeasure T] {α β : ℝ}
    (hUc : U (Icc α (α + β))ᶜ = 0) (hTc : T (Icc α (α + β))ᶜ = 0)
    (hspec : U + ((b : ℝ≥0∞) - 1) • T = (b : ℝ≥0∞) • F) :
    ∫ x, x ∂F = (∫ x, x ∂U + ((b : ℝ) - 1) * ∫ x, x ∂T) / b := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have h := congrArg (fun μ => ∫ x, x ∂μ) hspec
  have hb1 : ((b : ℝ≥0∞) - 1) = ((b - 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.natCast_sub, Nat.cast_one]
  rw [integral_add_measure (integrable_of_carried hUc)
    ((integrable_of_carried hTc).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, hb1, ENNReal.toReal_natCast, ENNReal.toReal_natCast, smul_eq_mul,
    smul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one] at h
  field_simp
  linarith

/-- Theorem `as:thm:hetero` with the blocks `B_k` given as `Blk m1 m2 × Fin b` and with the
bound `∑_k |e_k| ≤ 2(ℓ - H)` on the deviations of every selection as a hypothesis (it holds when
the blocks consist of consecutive indices in the order of the numbers `a_i`, see
`sum_abs_dev_le`). -/
theorem core (hconc : H_lem_conc_a) (hwin : H_prop_window) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2)
    (hb : 2 ≤ b) {H ℓ ρ s : ℝ} (hH : 0 < H) (h2H : 2 * H ≤ ℓ)
    (h1 : 4 * (ℓ - H) ≤ ((m1 : ℝ) - 1) * H)
    (Fu : Blk m1 m2 × Fin b → Measure ℝ) (hFu : ∀ p, IsProbabilityMeasure (Fu p))
    (hFuc : ∀ p, ∃ α, Fu p (Icc α (α + ℓ))ᶜ = 0)
    (c : Blk m1 m2 × Fin b → ℝ) (hU : ∀ p, (b : ℝ≥0∞)⁻¹ • unifI (c p - H) (c p + H) ≤ Fu p)
    (hsel : ∀ o, ∑ k, |dev (fun p => ∫ x, x ∂(restPart b (Fu p) (unifI (c p - H) (c p + H))) -
      c p) o k| ≤ 2 * (ℓ - H))
    (Fo : R → Measure ℝ) (hFo : ∀ r, IsProbabilityMeasure (Fo r))
    (hFoc : ∀ r, ∃ α, Fo r (Icc α (α + ℓ))ᶜ = 0)
    (hρ : ρ + ℓ ≤ m2 * H / 2) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc (s - ρ) (s + ρ))ᶜ = 0) (hνm : ∫ x, x ∂ν = s)
    (hs : s = ∑ p, ∫ x, x ∂(Fu p) + ∑ r, ∫ x, x ∂(Fo r)) :
    ν ∈ AggSet (Sum.elim Fu Fo) := by
  classical
  set U : Blk m1 m2 × Fin b → Measure ℝ := fun p => unifI (c p - H) (c p + H) with hUdef
  set T : Blk m1 m2 × Fin b → Measure ℝ := fun p => restPart b (Fu p) (U p) with hTdef
  set a : Blk m1 m2 × Fin b → ℝ := fun p => ∫ x, x ∂(T p) - c p with hadef
  have hUp : ∀ p, IsProbabilityMeasure (U p) := fun p => unifI_isProb _ _
  have hT : ∀ p, IsProbabilityMeasure (T p) := fun p => by
    have := hFu p; have := hUp p
    exact restPart_isProb hb (hU p)
  have hTc : ∀ p, ∃ α, T p (Icc α (α + ℓ))ᶜ = 0 := fun p => by
    obtain ⟨α, h⟩ := hFuc p
    exact ⟨α, restPart_carried h⟩
  have ha : ∀ p, ∫ x, x ∂(T p) = c p + a p := fun p => by simp only [hadef]; ring
  have hm1' : (0 : ℝ) < (m1 : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m1 := by exact_mod_cast hm1
    linarith
  have hγ : ∀ o k, |2 * tlt a o k / H| ≤ 1 := by
    intro o k
    have h3 := abs_tlt_le hm1 a o k
    have h4 := hsel o
    have h5 : 1 / ((m1 : ℝ) - 1) * ∑ j, |dev a o j| ≤ H / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm1']
      nlinarith
    rw [abs_div, abs_mul, abs_two, abs_of_pos hH, div_le_one hH]
    linarith
  have hspec : ∀ p, U p + ((b : ℝ≥0∞) - 1) • T p = (b : ℝ≥0∞) • Fu p := fun p => by
    have := hFu p; have := hUp p
    exact restPart_spec hb (hU p)
  have hmeanF : ∀ p, ∫ x, x ∂(Fu p) = c p + (1 - 1 / (b : ℝ)) * a p := by
    intro p
    have := hFu p; have := hUp p; have := hT p
    obtain ⟨α, hα⟩ := hFuc p
    have hsub : Icc (c p - H) (c p + H) ⊆ Icc α (α + ℓ) := by
      have hle := le_smul_of_inv_le (by omega) (hU p)
      have h0 : U p (Icc α (α + ℓ))ᶜ = 0 := by
        refine le_antisymm ((Measure.le_iff'.1 hle _).trans ?_) bot_le
        simp [hα]
      exact icc_subset_of_unifI_null hH h0
    have hUc : U p (Icc α (α + ℓ))ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.2 hsub) (unifI_carried (by linarith))
    rw [mean_of_spec hb hUc (restPart_carried hα) (hspec p), ha p, hUdef]
    simp only
    rw [integral_unifI (by linarith)]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    field_simp
    ring
  have hper : ∀ o, ν ∈ AggSet (Sum.elim (selLaw H c T a o) Fo) := fun o =>
    perSel hconc hwin hm1 hm2 hH h2H hT hTc ha hγ Fo hFo hFoc hρ ν hνc hνm
      (by rw [hs]; simp_rw [hmeanF]) o
  choose P hPp hPm hPs using hper
  have hcard : (Finset.univ : Finset (Blk m1 m2 → Fin b)).card = b ^ (m1 + m2) := by
    simp
  have hbk0 : ((b : ℝ≥0∞) ^ (m1 + m2)) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast (show b ≠ 0 by omega)
  have hbkt : ((b : ℝ≥0∞) ^ (m1 + m2)) ≠ ⊤ := by simp
  have hsumc : ∀ μ : Measure ℝ, ∑ _o : Blk m1 m2 → Fin b, μ = ((b : ℝ≥0∞) ^ (m1 + m2)) • μ := by
    intro μ
    rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]
    push_cast
    rfl
  refine ⟨((b : ℝ≥0∞) ^ (m1 + m2))⁻¹ • ∑ o, P o, ?_, ?_, ?_⟩
  · constructor
    have hs1 : (∑ o, P o) univ = ∑ _o : Blk m1 m2 → Fin b, (1 : ℝ≥0∞) := by
      simp only [sum_apply, measure_univ]
    rw [smul_apply, hs1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact ENNReal.inv_mul_cancel hbk0 hbkt
  · intro i
    rw [Measure.map_smul _ (measurable_pi_apply i).aemeasurable,
      map_finset_sum (measurable_pi_apply i)]
    simp_rw [hPm]
    rcases i with p | r
    · simp only [Sum.elim_inl]
      rw [sum_selLaw hm1 hb hH hspec hγ p, smul_smul, ENNReal.inv_mul_cancel hbk0 hbkt, one_smul]
    · simp only [Sum.elim_inr]
      rw [hsumc, smul_smul, ENNReal.inv_mul_cancel hbk0 hbkt, one_smul]
  · rw [Measure.map_smul _ measurable_sum_coord.aemeasurable, map_finset_sum measurable_sum_coord]
    simp_rw [hPs]
    rw [hsumc, smul_smul, ENNReal.inv_mul_cancel hbk0 hbkt, one_smul]

/-- Theorem `as:thm:hetero` for a family indexed by any finite type, the `n` distributions with a
uniform part being given by an embedding `e : Fin n ↪ ι`, with the window half-width `ρ` only
required to satisfy `ρ + ℓ ≤ m₂H/2`. -/
theorem thm_hetero_gen (hconc : H_lem_conc_a) (hwin : H_prop_window) {b m1 m2 n : ℕ}
    (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ ρ s : ℝ} (hH : 0 < H)
    (h1 : 4 * (ℓ - H) ≤ ((m1 : ℝ) - 1) * H) (hρ : ρ + ℓ ≤ m2 * H / 2)
    (hn : n = b * (m1 + m2)) {ι : Type*} [Fintype ι] (e : Fin n ↪ ι) (F : ι → Measure ℝ)
    (hF : ∀ i, IsProbabilityMeasure (F i)) (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0)
    (c : Fin n → ℝ) (hU : ∀ j, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (e j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνc : ν (Icc (s - ρ) (s + ρ))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = s) (hs : s = ∑ i, ∫ x, x ∂(F i)) : ν ∈ AggSet F := by
  classical
  have hsub : ∀ j α, F (e j) (Icc α (α + ℓ))ᶜ = 0 →
      Icc (c j - H) (c j + H) ⊆ Icc α (α + ℓ) := by
    intro j α hα
    have hle := le_smul_of_inv_le (by omega) (hU j)
    apply icc_subset_of_unifI_null hH
    refine le_antisymm ((Measure.le_iff'.1 hle _).trans ?_) bot_le
    simp [hα]
  have hn0 : 0 < n := by rw [hn]; exact Nat.mul_pos (by omega) (by omega)
  have h2H : 2 * H ≤ ℓ := by
    obtain ⟨α, hα⟩ := hFc (e ⟨0, hn0⟩)
    have hs' := hsub _ _ hα
    have hl := hs' ⟨le_refl _, by linarith⟩
    have hr := hs' ⟨by linarith, le_refl _⟩
    linarith [hl.1, hr.2]
  set a' : Fin n → ℝ := fun j =>
    ∫ x, x ∂(restPart b (F (e j)) (unifI (c j - H) (c j + H))) - c j with ha'def
  have ha' : ∀ j, |a' j| ≤ ℓ - H := by
    intro j
    obtain ⟨α, hα⟩ := hFc (e j)
    have := hF (e j)
    have := unifI_isProb (c j - H) (c j + H)
    have := restPart_isProb hb (hU j)
    have hm := mean_mem_of_carried
      (restPart_carried (b := b) (U := unifI (c j - H) (c j + H)) hα)
    have hs' := hsub j α hα
    have hl := hs' ⟨le_refl _, by linarith⟩
    have hr := hs' ⟨by linarith, le_refl _⟩
    rw [abs_le]
    constructor <;> simp only [ha'def] <;> linarith [hm.1, hm.2, hl.1, hr.2]
  -- the blocks: consecutive indices in the order of the `a'`
  set σ := Tuple.sort a'
  have hmono := Tuple.monotone_sort a'
  have hcast : (m1 + m2) * b = n := by rw [hn]; ring
  let β : Blk m1 m2 × Fin b ≃ Fin n :=
    ((Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin b))).trans
      (finProdFinEquiv.trans (finCongr hcast))).trans σ
  have hβ : ∀ K : Fin (m1 + m2), ∀ x : Fin b,
      β (finSumFinEquiv.symm K, x) = σ ⟨x + b * K, by
        have h1 := x.2
        have h2 : (K : ℕ) + 1 ≤ m1 + m2 := K.2
        have := Nat.mul_le_mul_left b h2
        rw [hn]; nlinarith⟩ := by
    intro K x
    simp only [β, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.apply_symm_apply,
      Equiv.refl_apply]
    congr 1
  have hsort : ∀ K K' : Fin (m1 + m2), K < K' → ∀ x y,
      a' (β (finSumFinEquiv.symm K, x)) ≤ a' (β (finSumFinEquiv.symm K', y)) := by
    intro K K' hK x y
    rw [hβ, hβ]
    apply hmono
    rw [Fin.le_iff_val_le_val]
    simp only
    have h1 : (K : ℕ) + 1 ≤ K' := hK
    have h2 := Nat.mul_le_mul_left b h1
    have h3 := x.2
    rw [mul_add, mul_one] at h2
    nlinarith
  -- the index type as the blocks and the rest
  let E : (Blk m1 m2 × Fin b) ⊕ {i // i ∉ Set.range e} ≃ ι :=
    (Equiv.sumCongr (β.trans (Equiv.ofInjective e e.injective))
      (Equiv.refl {i // i ∉ Set.range e})).trans (Equiv.sumCompl (fun i => i ∈ Set.range e))
  have hEl : ∀ p, E (Sum.inl p) = e (β p) := fun p => by simp [E]
  have hEr : ∀ r, E (Sum.inr r) = r.1 := fun r => by simp [E]
  refine aggSet_of_equiv E F ?_
  have hfam : (fun u => F (E u)) =
      Sum.elim (fun p => F (e (β p))) (fun r : {i // i ∉ Set.range e} => F r.1) := by
    funext u
    rcases u with p | r
    · simp [hEl]
    · simp [hEr]
  rw [hfam]
  refine core hconc hwin hm1 hm2 hb hH h2H h1 (fun p => F (e (β p))) (fun p => hF _)
    (fun p => hFc _) (fun p => c (β p)) (fun p => hU (β p)) ?_
    (fun r : {i // i ∉ Set.range e} => F r.1) (fun r => hF _) (fun r => hFc _) hρ ν hνc hνm ?_
  · intro o
    have hM : 1 ≤ m1 + m2 := by omega
    have key := sum_abs_dev_fin hM (by omega)
      (fun p => a' (β (finSumFinEquiv.symm p.1, p.2))) (D := ℓ - H)
      (fun K K' hK x y => hsort K K' hK x y) (fun p => ha' _)
      (fun K => o (finSumFinEquiv.symm K))
    rw [← (finSumFinEquiv.symm).sum_comp]
    convert key using 1
    rfl
  · rw [hs, ← E.sum_comp, Fintype.sum_sum_type]
    simp only [hEl, hEr]

/-- **Theorem `as:thm:hetero`**, strong form: the conclusion holds for every half-width `ρ` with
`ρ + ℓ ≤ m₂H/2`. The distributions are `F : Fin (n + r) → Measure ℝ`, the first `n` of which
satisfy `F_i ≥ (1/b) U[c_i - H, c_i + H]`. -/
theorem thm_hetero_strong (hconc : H_lem_conc_a) (hwin : H_prop_window) {b m1 m2 n r : ℕ}
    (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ ρ : ℝ} (hH : 0 < H)
    (h1 : (m1 - 1 : ℝ) * H ≥ 4 * (ℓ - H)) (hρ : ρ + ℓ ≤ m2 * H / 2) (hn : n = b * (m1 + m2))
    (F : Fin (n + r) → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0) (c : Fin n → ℝ)
    (hU : ∀ j : Fin n, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (Fin.castAdd r j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc ((∑ i, ∫ x, x ∂(F i)) - ρ) ((∑ i, ∫ x, x ∂(F i)) + ρ))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = ∑ i, ∫ x, x ∂(F i)) : ν ∈ AggSet F :=
  thm_hetero_gen hconc hwin hb hm1 hm2 hH h1 hρ hn (Fin.castAddEmb r) F hF hFc c hU ν hνc hνm rfl

/-- **Theorem `as:thm:hetero`** (the paper's statement): with `(m₁-1)H ≥ 4(ℓ-H)` and
`ρ = m₂H/2 - ℓ - H ≥ 0`, the aggregation set `𝒜_{n+r}(F_1, …, F_{n+r})` contains every
distribution with mean `s = ∑ m_{F_i}` carried by `[s - ρ, s + ρ]`. -/
theorem thm_hetero (hconc : H_lem_conc_a) (hwin : H_prop_window) {b m1 m2 n r : ℕ}
    (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ ρ : ℝ} (hH : 0 < H) (_hℓ : 0 < ℓ)
    (h1 : (m1 - 1 : ℝ) * H ≥ 4 * (ℓ - H)) (hρ : ρ = m2 * H / 2 - ℓ - H) (_hρ0 : 0 ≤ ρ)
    (hn : n = b * (m1 + m2))
    (F : Fin (n + r) → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0) (c : Fin n → ℝ)
    (hU : ∀ j : Fin n, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (Fin.castAdd r j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc ((∑ i, ∫ x, x ∂(F i)) - ρ) ((∑ i, ∫ x, x ∂(F i)) + ρ))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = ∑ i, ∫ x, x ∂(F i)) : ν ∈ AggSet F :=
  thm_hetero_strong hconc hwin hb hm1 hm2 hH h1 (by rw [hρ]; linarith) hn F hF hFc c hU ν hνc hνm

/-- A point mass in the aggregation set gives a joint mix. -/
lemma jointlyMixable_of_dirac {N : ℕ} {F : Fin N → Measure ℝ} {s : ℝ}
    (h : Measure.dirac s ∈ AggSet F) : JointlyMixable F := by
  obtain ⟨P, hP, hm, hsum⟩ := h
  refine ⟨P, hP, ⟨s, ?_⟩, hm⟩
  have h0 : P.map (fun x => ∑ i, x i) {s}ᶜ = 0 := by
    rw [hsum, Measure.dirac_apply' _ (measurableSet_singleton s).compl]
    simp
  rw [Measure.map_apply measurable_sum_coord (measurableSet_singleton s).compl] at h0
  rw [ae_iff]
  exact h0

lemma dirac_carried (s ρ : ℝ) (hρ : 0 ≤ ρ) : Measure.dirac s (Icc (s - ρ) (s + ρ))ᶜ = 0 := by
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  simp [hρ]

/-- **Theorem `as:thm:hetero`**, "in particular": the distributions are jointly mixable. -/
theorem thm_hetero_jointlyMixable (hconc : H_lem_conc_a) (hwin : H_prop_window)
    {b m1 m2 n r : ℕ} (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ : ℝ} (hH : 0 < H)
    (h1 : (m1 - 1 : ℝ) * H ≥ 4 * (ℓ - H)) (hρ0 : 0 ≤ m2 * H / 2 - ℓ - H)
    (hn : n = b * (m1 + m2))
    (F : Fin (n + r) → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0) (c : Fin n → ℝ)
    (hU : ∀ j : Fin n, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (Fin.castAdd r j)) :
    JointlyMixable F :=
  jointlyMixable_of_dirac (thm_hetero_strong hconc hwin hb hm1 hm2 hH h1
    (ρ := m2 * H / 2 - ℓ - H) (by linarith) hn F hF hFc c hU _
    (dirac_carried _ _ hρ0) (by simp))

end Main

/-! ## Corollary `as:cor:hetero` -/

lemma smul_le_smul_scalar {μ : Measure ℝ} {a a' : ℝ≥0∞} (h : a ≤ a') : a • μ ≤ a' • μ := by
  rw [Measure.le_iff']
  intro s
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul' h le_rfl

/-- **Corollary `as:cor:hetero`**: distributions `F_1, …, F_n` on `[u, v]` with
`F_i ≥ q U[u, v]`, together with any finite family `G` of distributions carried by intervals of
length at most `v - u`, have every distribution with the mean `s` of the sum carried by
`[s - ρ, s + ρ]`, `ρ = (m - 11)(v - u)/4`, in their aggregation set, where
`m = ⌊n / ⌈1/q⌉⌋ ≥ 11`. -/
theorem cor_hetero (hconc : H_lem_conc_a) (hwin : H_prop_window) {n r : ℕ} {u v q : ℝ}
    (huv : u < v) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, F i (Icc u v)ᶜ = 0) (hFq : ∀ i, ENNReal.ofReal q • unifI u v ≤ F i)
    (G : Fin r → Measure ℝ) (hG : ∀ j, IsProbabilityMeasure (G j))
    (hGc : ∀ j, ∃ α, G j (Icc α (α + (v - u)))ᶜ = 0)
    (hm : 11 ≤ n / ⌈1 / q⌉₊) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc ((∑ i, ∫ x, x ∂(F i)) + (∑ j, ∫ x, x ∂(G j)) -
        (((n / ⌈1 / q⌉₊ : ℕ) : ℝ) - 11) * (v - u) / 4)
      ((∑ i, ∫ x, x ∂(F i)) + (∑ j, ∫ x, x ∂(G j)) +
        (((n / ⌈1 / q⌉₊ : ℕ) : ℝ) - 11) * (v - u) / 4))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = (∑ i, ∫ x, x ∂(F i)) + ∑ j, ∫ x, x ∂(G j)) :
    ν ∈ AggSet (Sum.elim F G) := by
  classical
  set b := ⌈1 / q⌉₊ with hbdef
  set m := n / b with hmdef
  set H := (v - u) / 2 with hHdef
  set c := (u + v) / 2 with hcdef
  have hH : 0 < H := by rw [hHdef]; linarith
  have hcH1 : c - H = u := by rw [hcdef, hHdef]; ring
  have hcH2 : c + H = v := by rw [hcdef, hHdef]; ring
  have hmR : (11 : ℝ) ≤ m := by exact_mod_cast hm
  have hmeanU : ∫ x, x ∂(unifI u v) = c := by rw [integral_unifI huv.le]
  rcases hq1.lt_or_eq with hq1 | hq1
  · -- `q < 1`: Theorem `as:thm:hetero` with `m₁ = 5`, `m₂ = m - 5`
    have hb : 2 ≤ b := by
      have : (1 : ℝ) < 1 / q := by rw [lt_div_iff₀ hq0]; linarith
      have := (Nat.lt_ceil (n := 1)).2 (by exact_mod_cast this)
      omega
    have hbm : b * m ≤ n := by rw [hmdef, mul_comm]; exact Nat.div_mul_le_self n b
    let e : Fin (b * m) ↪ Fin n ⊕ Fin r :=
      ⟨fun j => Sum.inl (Fin.castLE hbm j), fun j j' h => by
        simpa using (Sum.inl_injective h)⟩
    have hbinv : (b : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal q := by
      have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
      have h1 : 1 / q ≤ b := Nat.le_ceil _
      have h2 : 1 / (b : ℝ) ≤ q := by
        rw [div_le_iff₀ hb0]; rw [div_le_iff₀ hq0] at h1; linarith
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hb0]
      exact ENNReal.ofReal_le_ofReal (by simpa using h2)
    have hm5 : ((m - 5 : ℕ) : ℝ) = (m : ℝ) - 5 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    refine thm_hetero_gen hconc hwin (b := b) (m1 := 5) (m2 := m - 5) (n := b * m)
      (ℓ := v - u) (H := H) hb (by norm_num) (by omega) hH ?_ ?_ (by congr 1; omega) e
      (Sum.elim F G) ?_ ?_ (fun _ => c) ?_ ν hνc hνm ?_
    · rw [hHdef]; norm_num
    · rw [hm5, hHdef]; nlinarith
    · rintro (i | j)
      · exact hF i
      · exact hG j
    · rintro (i | j)
      · exact ⟨u, by rw [show u + (v - u) = v by ring]; exact hFc i⟩
      · exact hGc j
    · intro j
      simp only [e, hcH1, hcH2]
      exact (smul_le_smul_scalar hbinv).trans (hFq _)
    · rw [Fintype.sum_sum_type]
      rfl
  · -- `q = 1`: all `F_i` are uniform; the uniform block of `absorb` is the whole of them
    subst hq1
    have hb1 : b = 1 := by rw [hbdef]; simp
    have hmn : m = n := by rw [hmdef, hb1, Nat.div_one]
    have hFU : ∀ i, F i = unifI u v := by
      intro i
      have := unifI_isProb u v
      have h := hFq i
      rw [ENNReal.ofReal_one, one_smul] at h
      exact (Measure.eq_of_le_of_measure_univ_eq h (by simp)).symm
    have key := absorb hconc hwin (I := Fin r) (J := Fin n) (ℓ := v - u) (H := H)
      (s := (∑ i, ∫ x, x ∂(F i)) + ∑ j, ∫ x, x ∂(G j))
      (ρ := (((n / ⌈1 / (1 : ℝ)⌉₊ : ℕ) : ℝ) - 11) * (v - u) / 4)
      G hG (by linarith) hGc (by simp; omega) hH (fun _ => c) ?_ ν hνc hνm ?_
    · refine aggSet_of_equiv (Equiv.sumComm (Fin r) (Fin n)) _ ?_
      convert key using 2
      funext i
      rcases i with j | i
      · simp
      · simp [hFU, hcH1, hcH2]
    · simp only [Fintype.card_fin]
      have : ((n / ⌈1 / (1 : ℝ)⌉₊ : ℕ) : ℝ) = n := by
        rw [← hbdef, ← hmdef, hmn]
      rw [this, hHdef]
      nlinarith
    · simp only [hFU, hmeanU, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- **Corollary `as:cor:hetero`**, joint mixability of the whole family. -/
theorem cor_hetero_jointlyMixable (hconc : H_lem_conc_a) (hwin : H_prop_window) {n r : ℕ}
    {u v q : ℝ} (huv : u < v) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, F i (Icc u v)ᶜ = 0) (hFq : ∀ i, ENNReal.ofReal q • unifI u v ≤ F i)
    (G : Fin r → Measure ℝ) (hG : ∀ j, IsProbabilityMeasure (G j))
    (hGc : ∀ j, ∃ α, G j (Icc α (α + (v - u)))ᶜ = 0)
    (hm : 11 ≤ n / ⌈1 / q⌉₊) : JointlyMixable (Fin.append F G) := by
  have hρ : (0 : ℝ) ≤ (((n / ⌈1 / q⌉₊ : ℕ) : ℝ) - 11) * (v - u) / 4 := by
    have : (11 : ℝ) ≤ ((n / ⌈1 / q⌉₊ : ℕ) : ℝ) := by exact_mod_cast hm
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by linarith) (by linarith)
  have h := cor_hetero hconc hwin huv hq0 hq1 F hF hFc hFq G hG hGc hm _
    (dirac_carried _ _ hρ) (by simp)
  apply jointlyMixable_of_dirac
  refine aggSet_of_equiv finSumFinEquiv _ ?_
  convert h using 2
  funext i
  rcases i with i | j <;> simp

/-- **Corollary `as:cor:hetero`**, last sentence: any `n ≥ 11⌈1/q⌉` distributions on `[u, v]`
with `F_i ≥ q U[u, v]` are jointly mixable. -/
theorem cor_hetero_n (hconc : H_lem_conc_a) (hwin : H_prop_window) {n : ℕ} {u v q : ℝ}
    (huv : u < v) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, F i (Icc u v)ᶜ = 0) (hFq : ∀ i, ENNReal.ofReal q • unifI u v ≤ F i)
    (hn : 11 * ⌈1 / q⌉₊ ≤ n) : JointlyMixable F := by
  have hb : 0 < ⌈1 / q⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hm : 11 ≤ n / ⌈1 / q⌉₊ := (Nat.le_div_iff_mul_le hb).2 hn
  obtain ⟨P, hP, ⟨s, hs⟩, hmarg⟩ := cor_hetero_jointlyMixable hconc hwin huv hq0 hq1 F hF hFc
    hFq (Fin.elim0 : Fin 0 → Measure ℝ) (fun j => j.elim0) (fun j => j.elim0) hm
  exact ⟨P, hP, ⟨s, by simpa using hs⟩, fun i => by simpa using hmarg i⟩

end Mixes.AsymHetero
