import Mixes.Defs
import Mixes.Large

/-!
# Masking: total variation against means and translations

Propositions 108 (`lg:prop:lower`), 109 (`lg:prop:joint`) and 117 (`jl:prop:mask`) of the paper.

* `tv μ ν = sup_A |μ A - ν A|` over measurable `A` (Mathlib has no total variation distance).
* Prop. 108: `exists_tv_ge_width` (lower bound), `tv_shares` (the equality for shares of a
  complete mix of `U(K)`), `tfun_Icc_le` (the projection bound in dimension one),
  `volume_sdiff_tr_le_proj_of_convex`, `tfun_le_proj` (the projection bound in every dimension,
  for `ℝ^d = ℝ × ℝ^{d-1}` and `t` along the first factor), `volume_sdiff_tr_le_proj_dir`,
  `tfun_le_proj_dir` (the projection bound for a general direction `t` in a finite-dimensional
  inner product space), `factor_one_dim` (the factor `1 + σ/(nw)`).
* Prop. 109: `prop109_a`, `prop109_b`, `prop109_b_conditioned`, `tv_eq_one_ae` (c);
  with `λ` Lebesgue measure on the hyperplane: `prop109_b_hyp`, `prop109_c_hyp`;
  `hypMeasure_affine_null` (lower-dimensional affine subspaces are null) and `prop109_c_cyclic`
  (the cyclic complete mixes `(X, AX, …, A^{n-1}X)`, `n ≥ 3`).
* Prop. 117: `prop117_a`, `prop117_b`, `prop117_b_conditioned`, `prop117_b_hyp`;
  `prop117_thm113` (the bound with `L' ≤ L + ε_n`, Theorem 113 taken as a hypothesis).

The density `w` of `β` is taken with respect to an arbitrary measure `λ` on tuples that is
invariant under translation by `δ`; `hypMeasure` constructs Lebesgue measure on the hyperplane
and `hypMeasure_map_add` checks this invariance for every `δ` with `∑ δᵢ = 0`.
-/

open MeasureTheory
open scoped Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace Mixes

section TV

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The total variation distance `sup_A |μ A - ν A|` over measurable sets `A`. -/
def tv (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |μ.real A - ν.real A|

lemma abs_real_sub_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) : |μ.real A - ν.real A| ≤ 1 := by
  have h1 : μ.real A ≤ 1 := measureReal_le_one
  have h2 : ν.real A ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ μ.real A := measureReal_nonneg
  have h4 : 0 ≤ ν.real A := measureReal_nonneg
  rw [abs_le]; constructor <;> linarith

lemma tv_bdd (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove (Set.range fun A : {A : Set α // MeasurableSet A} => |μ.real A - ν.real A|) :=
  ⟨1, by rintro _ ⟨A, rfl⟩; exact abs_real_sub_le_one μ ν A⟩

lemma le_tv (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ tv μ ν :=
  le_ciSup (tv_bdd μ ν) ⟨A, hA⟩

lemma tv_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tv μ ν ≤ 1 :=
  ciSup_le fun A => abs_real_sub_le_one μ ν A

lemma tv_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tv μ ν :=
  (abs_nonneg _).trans (le_tv μ ν MeasurableSet.empty)

lemma tv_le_of_forall (μ ν : Measure α) {c : ℝ}
    (h : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ c) : tv μ ν ≤ c :=
  ciSup_le fun A => h A.1 A.2

lemma tv_comm (μ ν : Measure α) : tv μ ν = tv ν μ := by
  unfold tv; simp_rw [abs_sub_comm]

/-- The total variation does not increase under measurable maps. -/
lemma tv_map_le (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → β} (hf : Measurable f) : tv (μ.map f) (ν.map f) ≤ tv μ ν := by
  apply tv_le_of_forall
  intro A hA
  rw [map_measureReal_apply hf hA, map_measureReal_apply hf hA]
  exact le_tv μ ν (hf hA)

lemma tv_map_equiv (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : α ≃ᵐ β) : tv (μ.map e) (ν.map e) = tv μ ν := by
  apply le_antisymm (tv_map_le μ ν e.measurable)
  have := tv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rw [Measure.map_map e.symm.measurable e.measurable,
    Measure.map_map e.symm.measurable e.measurable] at this
  simpa using this


lemma integral_layer (μ : Measure α) [IsProbabilityMeasure μ] {h : α → ℝ} (hm : Measurable h)
    {c : ℝ} (h0 : ∀ x, 0 ≤ h x) (hc : ∀ x, h x ≤ c) :
    ∫ x, h x ∂μ = ∫ t in Set.Ioc 0 c, μ.real {x | t < h x} := by
  have hint : Integrable h μ :=
    Integrable.of_bound hm.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hc x)
  rw [hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall h0)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
  intro t ht
  have : c < t := by
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
    exact ht.2 ht.1
  have : {x | t < h x} = ∅ := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (hc x).trans this.le
  simp [this]

/-- For probability measures and a measurable `g` with values in `[a, b]`,
`|∫ g dμ - ∫ g dν| ≤ (b - a) TV(μ, ν)`. -/
lemma abs_integral_sub_le_tv (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : α → ℝ} (hg : Measurable g) {a b : ℝ} (ha : ∀ x, a ≤ g x) (hb : ∀ x, g x ≤ b) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ (b - a) * tv μ ν := by
  obtain ⟨x0⟩ : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := (ha x0).trans (hb x0)
  set h : α → ℝ := fun x => g x - a
  have hm : Measurable h := hg.sub_const a
  have h0 : ∀ x, 0 ≤ h x := fun x => sub_nonneg.2 (ha x)
  have hc : ∀ x, h x ≤ b - a := fun x => sub_le_sub_right (hb x) a
  have hgμ : ∫ x, g x ∂μ = ∫ x, h x ∂μ + a := by
    simp only [h]; rw [integral_sub (Integrable.of_bound hg.aestronglyMeasurable (max |a| |b|)
      (Filter.Eventually.of_forall fun x => ?_)) (integrable_const a)]
    · simp
    · rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (ha x) (hb x)
  have hgν : ∫ x, g x ∂ν = ∫ x, h x ∂ν + a := by
    simp only [h]; rw [integral_sub (Integrable.of_bound hg.aestronglyMeasurable (max |a| |b|)
      (Filter.Eventually.of_forall fun x => ?_)) (integrable_const a)]
    · simp
    · rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (ha x) (hb x)
  rw [hgμ, hgν, add_sub_add_right_eq_sub, integral_layer μ hm h0 hc, integral_layer ν hm h0 hc]
  have hanti : ∀ (m : Measure α) [IsProbabilityMeasure m],
      IntegrableOn (fun t => m.real {x | t < h x}) (Set.Ioc 0 (b - a)) := by
    intro m _
    refine (AntitoneOn.integrableOn_isCompact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro s _ t _ hst
    exact measureReal_mono (fun x (hx : t < h x) => lt_of_le_of_lt hst hx)
  rw [← integral_sub (hanti μ) (hanti ν), ← Real.norm_eq_abs]
  calc _ ≤ tv μ ν * volume.real (Set.Ioc (0:ℝ) (b - a)) :=
        norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top
          (fun t _ => le_tv μ ν (measurableSet_lt measurable_const hm))
    _ = _ := by rw [Real.volume_real_Ioc_of_le (by linarith)]; ring
end TV


/-! ## Proposition 108: a lower bound through a linear functional -/

section Lower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {n : ℕ}

/-- The coordinate marginal of a measure on tuples. -/
abbrev marg (P : Measure (Fin n → E)) (i : Fin n) : Measure E := P.map (fun x => x i)

lemma integral_clamp_sum (P : Measure (Fin n → E)) [IsProbabilityMeasure P] (L : Set E)
    (hL : ∀ᵐ x ∂P, ∀ i, x i ∈ L) {s : E} (hs : ∀ᵐ x ∂P, ∑ i, x i = s) (f : E →L[ℝ] ℝ)
    {a b : ℝ} (hab : ∀ y ∈ L, a ≤ f y ∧ f y ≤ b) :
    ∑ i, ∫ y, max a (min b (f y)) ∂(marg P i) = f s := by
  set g : E → ℝ := fun y => max a (min b (f y))
  have hg : Continuous g := continuous_const.max (continuous_const.min f.continuous)
  have hgi : ∀ i : Fin n, Integrable (fun x : Fin n → E => g (x i)) P := by
    intro i
    refine Integrable.of_bound ((hg.measurable.comp (measurable_pi_apply i)).aestronglyMeasurable)
      (|a| + |b|) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    simp only [g]
    rcases le_total a (min b (f (x i))) with h | h
    · rw [max_eq_right h]
      rcases le_total b (f (x i)) with h' | h'
      · rw [min_eq_left h']; have := abs_nonneg a; linarith
      · rw [min_eq_right h']
        calc |f (x i)| ≤ max |a| |b| := abs_le_max_abs_abs (by
              have := min_le_right b (f (x i)); linarith [min_eq_right h' ▸ h]) h'
          _ ≤ |a| + |b| := max_le (by linarith [abs_nonneg b]) (by linarith [abs_nonneg a])
    · rw [max_eq_left h]; have := abs_nonneg b; linarith
  have hmap : ∀ i, ∫ y, g y ∂(marg P i) = ∫ x, g (x i) ∂P := fun i =>
    integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable
  simp_rw [hmap]
  rw [← integral_finsetSum _ (fun i _ => hgi i)]
  have : (fun x : Fin n → E => ∑ i, g (x i)) =ᵐ[P] fun _ => f s := by
    filter_upwards [hL, hs] with x hx hsx
    have : ∀ i, g (x i) = f (x i) := fun i => by
      simp only [g]; rw [min_eq_right (hab _ (hx i)).2, max_eq_right (hab _ (hx i)).1]
    simp_rw [this, ← map_sum, hsx]
  rw [integral_congr_ae this]
  simp

/-- **Proposition 108, first part** (summed form). If `P`, `P'` are distributions of tuples in
`L` with sums `s`, `s'`, and `f` is a linear functional with `a ≤ f ≤ b` on `L`, then
`|f (s - s')| ≤ (b - a) ∑ᵢ TV(Pᵢ, P'ᵢ)`. -/
theorem abs_sub_le_sum_tv (P P' : Measure (Fin n → E)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (L : Set E) (hL : ∀ᵐ x ∂P, ∀ i, x i ∈ L)
    (hL' : ∀ᵐ x ∂P', ∀ i, x i ∈ L) {s s' : E} (hs : ∀ᵐ x ∂P, ∑ i, x i = s)
    (hs' : ∀ᵐ x ∂P', ∑ i, x i = s') (f : E →L[ℝ] ℝ) {a b : ℝ}
    (hab : ∀ y ∈ L, a ≤ f y ∧ f y ≤ b) :
    |f (s - s')| ≤ (b - a) * ∑ i, tv (marg P i) (marg P' i) := by
  by_cases hab' : a ≤ b
  swap
  · have hLe : L = ∅ := Set.eq_empty_of_forall_notMem fun y hy =>
      hab' ((hab y hy).1.trans (hab y hy).2)
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · have h1 : s = 0 := by
        obtain ⟨x, hx⟩ := hs.exists; rw [← hx]; simp
      have h2 : s' = 0 := by
        obtain ⟨x, hx⟩ := hs'.exists; rw [← hx]; simp
      simp [h1, h2]
    · exfalso
      obtain ⟨x, hx⟩ := hL.exists
      simpa [hLe] using hx i
  rw [map_sub, ← integral_clamp_sum P L hL hs f hab, ← integral_clamp_sum P' L hL' hs' f hab,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact abs_integral_sub_le_tv _ _
    ((continuous_const.max (continuous_const.min f.continuous)).measurable)
    (fun y => le_max_left _ _) (fun y => max_le hab' (min_le_left _ _))

/-- **Proposition 108, first part.** For `n ≥ 1`, some coordinate has
`TV(Pᵢ, P'ᵢ) ≥ |f (s - s')| / (n (b - a))` (read as `0` when `b = a`). -/
theorem exists_tv_ge (hn : 0 < n) (P P' : Measure (Fin n → E)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (L : Set E) (hL : ∀ᵐ x ∂P, ∀ i, x i ∈ L)
    (hL' : ∀ᵐ x ∂P', ∀ i, x i ∈ L) {s s' : E} (hs : ∀ᵐ x ∂P, ∑ i, x i = s)
    (hs' : ∀ᵐ x ∂P', ∑ i, x i = s') (f : E →L[ℝ] ℝ) {a b : ℝ}
    (hab : ∀ y ∈ L, a ≤ f y ∧ f y ≤ b) :
    ∃ i, |f (s - s')| / (n * (b - a)) ≤ tv (marg P i) (marg P' i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => tv (marg P i) (marg P' i)) hne
  refine ⟨i, ?_⟩
  have key := abs_sub_le_sum_tv P P' L hL hL' hs hs' f hab
  have hsum : ∑ j, tv (marg P j) (marg P' j) ≤ n * tv (marg P i) (marg P' i) := by
    calc _ ≤ ∑ _j : Fin n, tv (marg P i) (marg P' i) := Finset.sum_le_sum fun j _ => hi j (by simp)
      _ = _ := by simp
  have htv := tv_nonneg (marg P i) (marg P' i)
  rcases le_or_gt b a with hba | hba
  · exact (div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith))).trans htv
  · apply div_le_of_le_mul₀ (by positivity) htv
    calc _ ≤ (b - a) * ∑ j, tv (marg P j) (marg P' j) := key
      _ ≤ (b - a) * (n * tv (marg P i) (marg P' i)) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
      _ = _ := by ring

/-- **Proposition 108, first part, as stated**: with `L` compact and the width
`max_L f - min_L f` of `f(L)`. -/
theorem exists_tv_ge_width (hn : 0 < n) (P P' : Measure (Fin n → E)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {L : Set E} (hLc : IsCompact L) (hL : ∀ᵐ x ∂P, ∀ i, x i ∈ L)
    (hL' : ∀ᵐ x ∂P', ∀ i, x i ∈ L) {s s' : E} (hs : ∀ᵐ x ∂P, ∑ i, x i = s)
    (hs' : ∀ᵐ x ∂P', ∑ i, x i = s') (f : E →L[ℝ] ℝ) :
    ∃ i, |f (s - s')| / (n * (sSup (f '' L) - sInf (f '' L))) ≤ tv (marg P i) (marg P' i) := by
  have hc : IsCompact (f '' L) := hLc.image f.continuous
  exact exists_tv_ge hn P P' L hL hL' hs hs' f fun y hy =>
    ⟨csInf_le hc.bddBelow (Set.mem_image_of_mem f hy),
      le_csSup hc.bddAbove (Set.mem_image_of_mem f hy)⟩

end Lower

/-! ## Uniform distributions and their translates -/

section Unif

variable {E : Type*} [MeasureSpace E]

lemma unifSet_isProb {K : Set E} (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤) :
    IsProbabilityMeasure (unifSet K) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

lemma unifSet_real_apply {K C : Set E} (hC : MeasurableSet C) :
    (unifSet K).real C = volume.real (C ∩ K) / volume.real K := by
  rw [unifSet, measureReal_def, smul_apply, Measure.restrict_apply hC, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def]
  ring

/-- `TV(U(A), U(B)) = |A \ B| / |A|` for measurable sets of equal finite positive volume. -/
theorem tv_unifSet {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h0 : volume A ≠ 0) (htop : volume A ≠ ⊤) (hAB : volume A = volume B) :
    tv (unifSet A) (unifSet B) = volume.real (A \ B) / volume.real A := by
  have hB0 : volume B ≠ 0 := hAB ▸ h0
  have hBtop : volume B ≠ ⊤ := hAB ▸ htop
  have := unifSet_isProb h0 htop
  have := unifSet_isProb hB0 hBtop
  have hreal : volume.real A = volume.real B := by rw [measureReal_def, measureReal_def, hAB]
  have hvpos : 0 < volume.real A := ENNReal.toReal_pos h0 htop
  have hsymm : volume.real (A \ B) = volume.real (B \ A) := by
    have h1 := measureReal_sdiff_add_inter (μ := volume) (s := A) hB (by finiteness)
    have h2 := measureReal_sdiff_add_inter (μ := volume) (s := B) hA (by finiteness)
    rw [Set.inter_comm] at h2
    linarith
  apply le_antisymm
  · apply tv_le_of_forall
    intro C hC
    rw [unifSet_real_apply hC, unifSet_real_apply hC, ← hreal, ← sub_div, abs_div,
      abs_of_pos hvpos]
    apply div_le_div_of_nonneg_right _ hvpos.le
    rw [abs_le]
    have hfA : volume (A) ≠ ⊤ := htop
    constructor
    · have : volume.real (C ∩ B) ≤ volume.real (C ∩ A) + volume.real (B \ A) := by
        calc _ ≤ volume.real ((C ∩ A) ∪ (B \ A)) :=
              measureReal_mono (fun x hx => by by_cases h : x ∈ A <;> simp_all)
                (measure_union_ne_top (measure_ne_top_of_subset Set.inter_subset_right htop)
                  (measure_ne_top_of_subset Set.sdiff_subset hBtop))
          _ ≤ _ := measureReal_union_le _ _
      linarith
    · have : volume.real (C ∩ A) ≤ volume.real (C ∩ B) + volume.real (A \ B) := by
        calc _ ≤ volume.real ((C ∩ B) ∪ (A \ B)) :=
              measureReal_mono (fun x hx => by by_cases h : x ∈ B <;> simp_all)
                (measure_union_ne_top (measure_ne_top_of_subset Set.inter_subset_right hBtop)
                  (measure_ne_top_of_subset Set.sdiff_subset htop))
          _ ≤ _ := measureReal_union_le _ _
      linarith
  · have := le_tv (unifSet A) (unifSet B) (hA.diff hB)
    rw [unifSet_real_apply (hA.diff hB), unifSet_real_apply (hA.diff hB)] at this
    have e1 : A \ B ∩ A = A \ B := Set.inter_eq_left.2 Set.sdiff_subset
    have e2 : A \ B ∩ B = ∅ := by ext x; simp
    rw [e1, e2, measureReal_empty, zero_div, sub_zero,
      abs_of_nonneg (div_nonneg measureReal_nonneg measureReal_nonneg)] at this
    exact this

end Unif

section Translate

variable {E : Type*} [NormedAddCommGroup E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddRightInvariant]

/-- The translate `K + u = {y | y - u ∈ K}`. -/
def tr (K : Set E) (u : E) : Set E := (fun y => y - u) ⁻¹' K

/-- `t(e) = |K \ (K + e)| / |K|`. -/
def tfun (K : Set E) (e : E) : ℝ := volume.real (K \ tr K e) / volume.real K

lemma measurableSet_tr {K : Set E} (hK : MeasurableSet K) (u : E) : MeasurableSet (tr K u) :=
  (measurable_sub_const u) hK

lemma volume_tr (K : Set E) (u : E) : volume (tr K u) = volume K := by
  simp only [tr, sub_eq_add_neg]
  exact measure_preimage_add_right _ _ _

lemma measureReal_tr (K : Set E) (u : E) : volume.real (tr K u) = volume.real K := by
  rw [measureReal_def, measureReal_def, volume_tr]

lemma tr_tr (K : Set E) (u v : E) : tr (tr K u) v = tr K (u + v) := by
  ext y; simp [tr, sub_sub, add_comm]

lemma tr_zero (K : Set E) : tr K 0 = K := by ext y; simp [tr]

lemma map_add_unifSet (K : Set E) (u : E) :
    (unifSet K).map (· + u) = unifSet (tr K u) := by
  ext C hC
  rw [Measure.map_apply (measurable_add_const u) hC, unifSet, unifSet, smul_apply, smul_apply,
    volume_tr, Measure.restrict_apply ((measurable_add_const u) hC),
    Measure.restrict_apply hC]
  congr 1
  have : (fun y => y + u) ⁻¹' C ∩ K = (fun y => y + u) ⁻¹' (C ∩ tr K u) := by
    ext y; simp [tr]
  rw [this]
  exact measure_preimage_add_right (volume : Measure E) u _

/-- Translating by `u` and `u'`: `TV(U(K + u), U(K + u')) = t(u' - u)`. -/
theorem tv_unifSet_translate {K : Set E} (hK : MeasurableSet K) (h0 : volume K ≠ 0)
    (htop : volume K ≠ ⊤) (u u' : E) :
    tv ((unifSet K).map (· + u)) ((unifSet K).map (· + u')) = tfun K (u' - u) := by
  rw [map_add_unifSet, map_add_unifSet, tv_unifSet (measurableSet_tr hK u)
    (measurableSet_tr hK u') (by rwa [volume_tr]) (by rwa [volume_tr])
    (by rw [volume_tr, volume_tr]), tfun, measureReal_tr]
  have : tr K u \ tr K u' = tr (K \ tr K (u' - u)) u := by
    ext y; simp [tr, sub_sub, add_sub_cancel]
  rw [this, measureReal_tr]

lemma tfun_neg {K : Set E} (hK : MeasurableSet K) (htop : volume K ≠ ⊤) (e : E) :
    tfun K (-e) = tfun K e := by
  unfold tfun
  congr 1
  have h1 := measureReal_sdiff_add_inter (μ := volume) (s := K) (measurableSet_tr hK e)
    (by finiteness)
  have h2 := measureReal_sdiff_add_inter (μ := volume) (s := K) (measurableSet_tr hK (-e))
    (by finiteness)
  -- `K ∩ (K - e)` is the translate by `-e` of `(K + e) ∩ K`
  have h3 : volume.real (K ∩ tr K (-e)) = volume.real (K ∩ tr K e) := by
    have : K ∩ tr K (-e) = tr (tr K e ∩ K) (-e) := by
      ext y; simp [tr]
    rw [this, measureReal_def, measureReal_def, volume_tr, Set.inter_comm]
  linarith

lemma tfun_zero (K : Set E) : tfun K 0 = 0 := by simp [tfun, tr_zero]

lemma tfun_nonneg (K : Set E) (e : E) : 0 ≤ tfun K e :=
  div_nonneg measureReal_nonneg measureReal_nonneg

end Translate

section Shares

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddRightInvariant] {n : ℕ}

/-- **Proposition 108, second part.** For shares `X^s_i = s/n + Y_i` built from an
`n`-complete mix `Y` of `U(K)`, `TV(X^s_i, X^{s'}_i) = |K \ (K + (s' - s)/n)| / |K|`. -/
theorem tv_shares {K : Set E} (hK : MeasurableSet K) (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤)
    {P : Measure (Fin n → E)} (hP : IsCompleteMix n (unifSet K) P) (i : Fin n) (s s' : E) :
    tv ((marg P i).map (· + (n : ℝ)⁻¹ • s)) ((marg P i).map (· + (n : ℝ)⁻¹ • s')) =
      tfun K ((n : ℝ)⁻¹ • (s' - s)) := by
  rw [show marg P i = unifSet K from hP.2.2 i, tv_unifSet_translate hK h0 htop, smul_sub]

end Shares

section OneDim

/-- In dimension one, `|K \ (K + t)| ≤ |t|` for an interval `K = [p, q]`. -/
lemma volume_Icc_sdiff_tr_le (p q t : ℝ) :
    volume.real (Set.Icc p q \ tr (Set.Icc p q) t) ≤ |t| := by
  rcases le_total 0 t with ht | ht
  · calc _ ≤ volume.real (Set.Ico p (p + t)) := by
          apply measureReal_mono _ measure_Ico_lt_top.ne
          intro y hy
          simp only [tr, Set.mem_sdiff, Set.mem_Icc, Set.mem_preimage, not_and, not_le] at hy
          refine ⟨hy.1.1, ?_⟩
          by_contra h
          have := hy.2 (by linarith); linarith [hy.1.2]
      _ = |t| := by rw [Real.volume_real_Ico_of_le (by linarith), abs_of_nonneg ht]; ring
  · calc _ ≤ volume.real (Set.Ioc (q + t) q) := by
          apply measureReal_mono _ measure_Ioc_lt_top.ne
          intro y hy
          simp only [tr, Set.mem_sdiff, Set.mem_Icc, Set.mem_preimage, not_and, not_le] at hy
          refine ⟨?_, hy.1.2⟩
          by_contra h
          have := hy.2 (by linarith [hy.1.1]); linarith
      _ = |t| := by rw [Real.volume_real_Ioc_of_le (by linarith), abs_of_nonpos ht]; ring

/-- **Proposition 108, upper bound for `d = 1`**: for `K = [-w, w]`,
`t(e) ≤ |e| / |K| = |e| / (2w)`. -/
lemma tfun_Icc_le {w : ℝ} (hw : 0 < w) (e : ℝ) : tfun (Set.Icc (-w) w) e ≤ |e| / (2 * w) := by
  unfold tfun
  rw [Real.volume_real_Icc_of_le (by linarith), show w - -w = 2 * w by ring]
  exact div_le_div_of_nonneg_right (volume_Icc_sdiff_tr_le _ _ _) (by linarith)

/-- **Proposition 108, the factor `1 + σ/(nw)`**: with `K = [-w, w]`, `S = [-σ, σ]` and
`L = [-w - σ/n, w + σ/n]`, the upper bound `|s' - s| / (n · 2w)` is `1 + σ/(nw)` times the lower
bound `|s - s'| / (n (max_L f - min_L f))` for `f = id`. -/
lemma factor_one_dim {n : ℕ} (hn : 0 < n) {w σ : ℝ} (hw : 0 < w) (hσ : 0 ≤ σ) (s s' : ℝ) :
    |s' - s| / (n * (2 * w)) =
      (1 + σ / (n * w)) * (|s - s'| / (n * ((w + σ / n) - (-w - σ / n)))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [abs_sub_comm s s']
  have h1 : (w + σ / n) - (-w - σ / n) = 2 * (n * w + σ) / n := by field_simp; ring
  have h2 : 0 < n * w + σ := by positivity
  rw [h1]
  field_simp

end OneDim


/-! ## Propositions 109 and 117: translations of a joint mix with a density -/

section Density

variable {α : Type*} [MeasurableSpace α]

/-- The measure with density `w` (a nonnegative real function) with respect to `λ`. -/
def dens (lam : Measure α) (w : α → ℝ) : Measure α :=
  lam.withDensity fun y => ENNReal.ofReal (w y)

lemma dens_real_apply (lam : Measure α) {w : α → ℝ} (hint : Integrable w lam)
    (hw0 : ∀ y, 0 ≤ w y) {A : Set α} (hA : MeasurableSet A) :
    (dens lam w).real A = ∫ y in A, w y ∂lam := by
  rw [measureReal_def, dens, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn (Filter.Eventually.of_forall hw0),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun y _ => hw0 y)]

lemma dens_isProb (lam : Measure α) {w : α → ℝ} (hint : Integrable w lam)
    (hw0 : ∀ y, 0 ≤ w y) (h1 : ∫ y, w y ∂lam = 1) : IsProbabilityMeasure (dens lam w) := by
  constructor
  have := dens_real_apply lam hint hw0 MeasurableSet.univ
  rw [Measure.restrict_univ, h1, measureReal_def] at this
  have hne : dens lam w Set.univ ≠ ⊤ := by
    intro h; rw [h] at this; simp at this
  rw [← ENNReal.ofReal_toReal hne, this, ENNReal.ofReal_one]

/-- `TV ≤ ½ ∫ |w - g|` for two probability densities. -/
lemma tv_dens_le (lam : Measure α) {w g : α → ℝ} (hw : Integrable w lam) (hg : Integrable g lam)
    (hw0 : ∀ y, 0 ≤ w y) (hg0 : ∀ y, 0 ≤ g y) (hw1 : ∫ y, w y ∂lam = 1)
    (hg1 : ∫ y, g y ∂lam = 1) :
    tv (dens lam w) (dens lam g) ≤ (1 / 2) * ∫ y, |w y - g y| ∂lam := by
  apply tv_le_of_forall
  intro A hA
  rw [dens_real_apply lam hw hw0 hA, dens_real_apply lam hg hg0 hA,
    ← integral_sub hw.integrableOn hg.integrableOn, ← integral_indicator hA]
  have hD : Integrable (fun y => w y - g y) lam := hw.sub hg
  have hD0 : ∫ y, (w y - g y) ∂lam = 0 := by rw [integral_sub hw hg, hw1, hg1, sub_self]
  have hInd : Integrable (A.indicator fun y => w y - g y) lam := hD.indicator hA
  rw [abs_le]; constructor
  · have : ∫ y, -(A.indicator (fun y => w y - g y) y) ∂lam ≤
        ∫ y, (1 / 2) * (|w y - g y| - (w y - g y)) ∂lam := by
      apply integral_mono hInd.neg ((hD.abs.sub hD).const_mul _)
      intro y
      by_cases hy : y ∈ A
      · simp only [Pi.neg_apply, Pi.sub_apply, Set.indicator_of_mem hy]
        have := neg_abs_le (w y - g y); have := le_abs_self (w y - g y); nlinarith
      · simp only [Pi.neg_apply, Pi.sub_apply, Set.indicator_of_notMem hy, neg_zero]
        have := le_abs_self (w y - g y); nlinarith
    rw [integral_neg, integral_const_mul, integral_sub hD.abs hD, hD0] at this
    linarith
  · have : ∫ y, A.indicator (fun y => w y - g y) y ∂lam ≤
        ∫ y, (1 / 2) * (|w y - g y| + (w y - g y)) ∂lam := by
      apply integral_mono hInd ((hD.abs.add hD).const_mul _)
      intro y
      by_cases hy : y ∈ A
      · simp only [Pi.add_apply, Set.indicator_of_mem hy]
        have := le_abs_self (w y - g y); nlinarith
      · simp only [Pi.add_apply, Set.indicator_of_notMem hy]
        have := neg_abs_le (w y - g y); nlinarith
    rw [integral_const_mul, integral_add hD.abs hD, hD0] at this
    linarith

end Density

section Core

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The support set `{y ∈ H | ∀ j, y j ∈ K j}`. -/
def supp (H : Set (Fin n → E)) (K : Fin n → Set E) : Set (Fin n → E) :=
  H ∩ ⋂ j, (fun y => y j) ⁻¹' K j

lemma measurableSet_supp {H : Set (Fin n → E)} (hH : MeasurableSet H) {K : Fin n → Set E}
    (hK : ∀ j, MeasurableSet (K j)) : MeasurableSet (supp H K) :=
  hH.inter (MeasurableSet.iInter fun j => measurable_pi_apply j (hK j))

/-- **Core estimate of Propositions 109(b) and 117(b).** Let `λ` be a measure on tuples that is
invariant under translation by `δ`, let `H` be a measurable set invariant under translation by
`δ`, and let `β` have a density `w` with respect to `λ` vanishing off `T = H ∩ ∏ K j`, with
`w (y - δ) ≤ e^c w y` and `w y ≤ e^c w (y - δ)` whenever `y, y - δ ∈ T`. Then
`TV(β, β(· - δ)) ≤ ½ (e^c - 1) + ½ ∑ⱼ (β(Yⱼ - δⱼ ∉ Kⱼ) + β(Yⱼ + δⱼ ∉ Kⱼ))`. -/
theorem tv_translate_le (lam : Measure (Fin n → E)) (δ : Fin n → E)
    (hlam : lam.map (· + δ) = lam) {H : Set (Fin n → E)} (hH : MeasurableSet H)
    (hHδ : ∀ y, y - δ ∈ H ↔ y ∈ H) {K : Fin n → Set E} (hK : ∀ j, MeasurableSet (K j))
    {w : (Fin n → E) → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hwT : ∀ y, y ∉ supp H K → w y = 0) (hint : Integrable w lam) (h1 : ∫ y, w y ∂lam = 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hratio : ∀ y, y ∈ supp H K → y - δ ∈ supp H K →
      w (y - δ) ≤ Real.exp c * w y ∧ w y ≤ Real.exp c * w (y - δ)) :
    tv (dens lam w) ((dens lam w).map (· + δ)) ≤
      (1 / 2) * (Real.exp c - 1) + (1 / 2) * ∑ j,
        ((dens lam w).real {y | y j - δ j ∉ K j} + (dens lam w).real {y | y j + δ j ∉ K j}) := by
  set T := supp H K with hTdef
  have hT : MeasurableSet T := measurableSet_supp hH hK
  set β := dens lam w
  have hβ : IsProbabilityMeasure β := dens_isProb lam hint hw0 h1
  set g : (Fin n → E) → ℝ := fun y => w (y - δ)
  have hg : Measurable g := hw.comp (measurable_sub_const δ)
  have hg0 : ∀ y, 0 ≤ g y := fun y => hw0 _
  have mp : MeasurePreserving (· + δ) lam lam := ⟨measurable_add_const δ, hlam⟩
  have mp' : MeasurePreserving (· - δ) lam lam := by
    refine ⟨measurable_sub_const δ, ?_⟩
    conv_lhs => rw [← hlam]
    rw [Measure.map_map (measurable_sub_const δ) (measurable_add_const δ)]
    simp [Function.comp_def]
  have hgint : Integrable g lam :=
    (mp'.integrable_comp hw.aestronglyMeasurable).2 hint
  have hg1 : ∫ y, g y ∂lam = 1 := by
    rw [← h1]; exact mp'.integral_comp (MeasurableEquiv.subRight δ).measurableEmbedding w
  -- the translate of `β` has density `g`
  have hβ' : β.map (· + δ) = dens lam g := by
    ext A hA
    rw [Measure.map_apply (measurable_add_const δ) hA]
    simp only [β, dens]
    rw [withDensity_apply _ hA, withDensity_apply _ ((measurable_add_const δ) hA)]
    rw [← mp.setLIntegral_comp_preimage hA (f := fun y => ENNReal.ofReal (g y))
      (ENNReal.measurable_ofReal.comp hg)]
    simp [g]
  rw [hβ']
  refine (tv_dens_le lam hint hgint hw0 hg0 h1 hg1).trans ?_
  -- pointwise bound
  set S1 : Set (Fin n → E) := (· - δ) ⁻¹' Tᶜ
  set S2 : Set (Fin n → E) := Tᶜ
  have hS1 : MeasurableSet S1 := (measurable_sub_const δ) hT.compl
  have hS2 : MeasurableSet S2 := hT.compl
  have hpt : ∀ y, |w y - g y| ≤ (Real.exp c - 1) * w y + S1.indicator w y + S2.indicator g y := by
    intro y
    have he : 1 ≤ Real.exp c := Real.one_le_exp hc
    by_cases hy : y ∈ T <;> by_cases hy' : y - δ ∈ T
    · have hS1y : y ∉ S1 := fun h => h hy'
      have hS2y : y ∉ S2 := fun h => h hy
      rw [Set.indicator_of_notMem hS1y, Set.indicator_of_notMem hS2y]
      obtain ⟨r1, r2⟩ := hratio y hy hy'
      have : 0 < Real.exp c := Real.exp_pos c
      have hwy := hw0 y
      have hgy := hg0 y
      simp only [g] at *
      rw [abs_le]; constructor
      · nlinarith
      · nlinarith
    · have hS1y : y ∈ S1 := hy'
      have hS2y : y ∉ S2 := fun h => h hy
      rw [Set.indicator_of_mem hS1y, Set.indicator_of_notMem hS2y]
      have : g y = 0 := hwT _ hy'
      rw [this, sub_zero, abs_of_nonneg (hw0 y)]
      nlinarith [hw0 y]
    · have hS2y : y ∈ S2 := hy
      rw [Set.indicator_of_mem hS2y, hwT y hy, zero_sub, abs_neg, abs_of_nonneg (hg0 y)]
      have := Set.indicator_nonneg (fun z _ => hw0 z) (s := S1) y
      linarith
    · rw [hwT y hy, show g y = 0 from hwT _ hy']
      simp only [sub_self, abs_zero, mul_zero, zero_add]
      exact add_nonneg (Set.indicator_nonneg (fun z _ => hw0 z) y)
        (Set.indicator_nonneg (fun z _ => hg0 z) y)
  have hI1 : Integrable (S1.indicator w) lam := hint.indicator hS1
  have hI2 : Integrable (S2.indicator g) lam := hgint.indicator hS2
  have hbound : ∫ y, |w y - g y| ∂lam ≤
      (Real.exp c - 1) + β.real S1 + β.real {y | y + δ ∉ T} := by
    have := integral_mono (f := fun y => |w y - g y|)
      (g := fun y => (Real.exp c - 1) * w y + S1.indicator w y + S2.indicator g y)
      (hint.sub hgint).abs (((hint.const_mul _).add hI1).add hI2) hpt
    have hA1 : Integrable (fun x => (Real.exp c - 1) * w x) lam := hint.const_mul _
    rw [integral_add (f := fun x => (Real.exp c - 1) * w x + S1.indicator w x) (hA1.add hI1) hI2,
      integral_add hA1 hI1, integral_const_mul, h1, mul_one, integral_indicator hS1,
      integral_indicator hS2] at this
    have e1 : β.real S1 = ∫ y in S1, w y ∂lam := dens_real_apply lam hint hw0 hS1
    have e2 : β.real {y | y + δ ∉ T} = ∫ y in S2, g y ∂lam := by
      rw [← dens_real_apply lam hgint hg0 hS2, ← hβ', map_measureReal_apply
        (measurable_add_const δ) hS2]
      rfl
    linarith
  -- union bounds
  have hβT : β.real Tᶜ = 0 := by
    rw [dens_real_apply lam hint hw0 hT.compl]
    exact setIntegral_eq_zero_of_forall_eq_zero fun y hy => hwT y hy
  have union : ∀ (σ : Fin n → E) (hσ : ∀ y, y + σ ∈ H ↔ y ∈ H),
      β.real {y | y + σ ∉ T} ≤ ∑ j, β.real {y | y j + σ j ∉ K j} := by
    intro σ hσ
    have hsub : {y | y + σ ∉ T} ⊆ Tᶜ ∪ ⋃ j ∈ (Finset.univ : Finset (Fin n)),
        {y | y j + σ j ∉ K j} := by
      intro y hy
      by_cases hyT : y ∈ T
      · right
        simp only [Set.mem_ofPred_eq, hTdef, supp, Set.mem_inter_iff, Set.mem_iInter,
          Set.mem_preimage, not_and, not_forall] at hy hyT
        obtain ⟨j, hj⟩ := hy ((hσ y).2 hyT.1)
        simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_ofPred_eq]
        exact ⟨j, by simpa using hj⟩
      · left; exact hyT
    calc β.real {y | y + σ ∉ T} ≤ β.real (Tᶜ ∪ ⋃ j ∈ (Finset.univ : Finset (Fin n)),
          {y | y j + σ j ∉ K j}) := measureReal_mono hsub
      _ ≤ β.real Tᶜ + β.real (⋃ j ∈ (Finset.univ : Finset (Fin n)), {y | y j + σ j ∉ K j}) :=
          measureReal_union_le _ _
      _ ≤ 0 + ∑ j, β.real {y | y j + σ j ∉ K j} := by
          rw [hβT]; gcongr; exact measureReal_biUnion_finset_le _ _
      _ = _ := zero_add _
  have u1 : β.real S1 ≤ ∑ j, β.real {y | y j - δ j ∉ K j} := by
    have := union (-δ) (fun y => by rw [← sub_eq_add_neg]; exact hHδ y)
    have e : S1 = {y | y + -δ ∉ T} := by ext y; simp [S1, sub_eq_add_neg]
    rw [e]
    simpa [sub_eq_add_neg] using this
  have u2 : β.real {y | y + δ ∉ T} ≤ ∑ j, β.real {y | y j + δ j ∉ K j} :=
    union δ (fun y => by rw [← hHδ (y + δ)]; simp)
  rw [Finset.sum_add_distrib]
  nlinarith

end Core

section Reduce

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- `TV(x + Y, x' + Y) = TV(Y, Y + δ)` with `δ = x' - x`. -/
lemma tv_add_left_eq (β : Measure (Fin n → E)) [IsProbabilityMeasure β] (x x' : Fin n → E) :
    tv (β.map (x + ·)) (β.map (x' + ·)) = tv β (β.map (· + (x' - x))) := by
  have h : β.map (x' + ·) = (β.map (· + (x' - x))).map (x + ·) := by
    rw [Measure.map_map (measurable_const_add x) (measurable_add_const _)]
    congr 1; funext y; simp only [Function.comp_apply]
    rw [add_comm y, ← add_assoc, add_sub_cancel]
  rw [h]
  have := tv_map_equiv β (β.map (· + (x' - x))) (MeasurableEquiv.addLeft x)
  simpa using this

/-- The coordinate marginals of `x + Y` are the translates of those of `Y`. -/
lemma marg_map_add_left (β : Measure (Fin n → E)) (x : Fin n → E) (j : Fin n) :
    marg (β.map (x + ·)) j = (marg β j).map (· + x j) := by
  simp only [marg]
  rw [Measure.map_map (measurable_pi_apply j) (measurable_const_add x),
    Measure.map_map (measurable_add_const (x j)) (measurable_pi_apply j)]
  congr 1; funext y; simp [add_comm]

/-- Projection to one coordinate: `TV(x + Y, x' + Y) ≥ TV(x_j + Y_j, x'_j + Y_j)`. -/
lemma tv_marg_le (β : Measure (Fin n → E)) [IsProbabilityMeasure β] (x x' : Fin n → E)
    (j : Fin n) :
    tv ((marg β j).map (· + x j)) ((marg β j).map (· + x' j)) ≤
      tv (β.map (x + ·)) (β.map (x' + ·)) := by
  rw [← marg_map_add_left, ← marg_map_add_left]
  exact tv_map_le _ _ (measurable_pi_apply j)

/-- Proposition 109(c), core: if `β(E) = 1` and `δ ∉ E - E`, then `TV(β, β(· - δ)) = 1`. -/
lemma tv_eq_one_of_disjoint (β : Measure (Fin n → E)) [IsProbabilityMeasure β]
    {S : Set (Fin n → E)} (hS : MeasurableSet S) (hβS : β S = 1) {δ : Fin n → E}
    (hδ : δ ∉ S - S) : tv β (β.map (· + δ)) = 1 := by
  apply le_antisymm (tv_le_one _ _)
  have h1 : β.real S = 1 := by rw [measureReal_def, hβS]; rfl
  have h2 : (β.map (· + δ)).real S = 0 := by
    rw [map_measureReal_apply (measurable_add_const δ) hS]
    have : (· + δ) ⁻¹' S ⊆ Sᶜ := by
      intro y hy hyS
      exact hδ ⟨y + δ, hy, y, hyS, add_sub_cancel_left y δ⟩
    have hc : β.real Sᶜ = 0 := by
      rw [measureReal_compl hS, h1]; simp
    exact le_antisymm ((measureReal_mono this).trans hc.le) measureReal_nonneg
  have := le_tv β (β.map (· + δ)) hS
  rw [h1, h2, sub_zero, abs_one] at this
  exact this

/-- **Proposition 109(c).** If `β(E) = 1` for a measurable `E` whose difference set `E - E` is
`λ`-null, then `TV(x + Y, x + δ + Y) = 1` for `λ`-almost every `δ`. (In the paper `λ` is
Lebesgue measure on the hyperplane `∑ δᵢ = 0`.) -/
theorem tv_eq_one_ae (β : Measure (Fin n → E)) [IsProbabilityMeasure β]
    {S : Set (Fin n → E)} (hS : MeasurableSet S) (hβS : β S = 1) (lam : Measure (Fin n → E))
    (hnull : lam (S - S) = 0) (x : Fin n → E) :
    ∀ᵐ δ ∂lam, tv (β.map (x + ·)) (β.map ((x + δ) + ·)) = 1 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with δ hδ
  rw [tv_add_left_eq, add_sub_cancel_left]
  exact tv_eq_one_of_disjoint β hS hβS hδ

end Reduce

section LogLip

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

lemma ratio_of_log {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : |Real.log a - Real.log b| ≤ c) :
    b ≤ Real.exp c * a ∧ a ≤ Real.exp c * b := by
  rw [abs_le] at h
  constructor
  · calc b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ ≤ Real.exp (c + Real.log a) := Real.exp_le_exp.2 (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log ha]
  · calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (c + Real.log b) := Real.exp_le_exp.2 (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hb]

/-- For a product density `w y = C ∏ⱼ exp (uⱼ yⱼ)`, the logarithmic increment is a sum. -/
lemma log_prod_sub {C : ℝ} (hC : 0 < C) (u : Fin n → E → ℝ) (y z : Fin n → E) :
    Real.log (C * ∏ j, Real.exp (u j (y j))) - Real.log (C * ∏ j, Real.exp (u j (z j))) =
      ∑ j, (u j (y j) - u j (z j)) := by
  rw [← Real.exp_sum, ← Real.exp_sum, Real.log_mul hC.ne' (Real.exp_pos _).ne',
    Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp, Finset.sum_sub_distrib]
  ring

variable [NormedSpace ℝ E]

/-- **Proposition 109(b), conditioned products.** If `log h = ψ + ℓ` on `K` with `ℓ` affine and
`ψ` Lipschitz with constant `Lψ` on `K`, then for `w = C ∏ h(yᵢ)` and `∑ δᵢ = 0`,
`|log w y - log w (y - δ)| ≤ Lψ ‖δ‖₁` whenever all `yᵢ, yᵢ - δᵢ ∈ K`. -/
lemma log_incr_conditioned {C : ℝ} (hC : 0 < C) {K : Set E} (ψ : E → ℝ) (a : ℝ)
    (φ : E →ₗ[ℝ] ℝ) {Lψ : ℝ} (hψ : ∀ p ∈ K, ∀ q ∈ K, |ψ p - ψ q| ≤ Lψ * ‖p - q‖)
    (y δ : Fin n → E) (hδ : ∑ j, δ j = 0) (hy : ∀ j, y j ∈ K) (hyδ : ∀ j, y j - δ j ∈ K) :
    |Real.log (C * ∏ j, Real.exp (ψ (y j) + (a + φ (y j)))) -
      Real.log (C * ∏ j, Real.exp (ψ ((y - δ) j) + (a + φ ((y - δ) j))))| ≤
      Lψ * ∑ j, ‖δ j‖ := by
  rw [log_prod_sub hC (fun _ p => ψ p + (a + φ p))]
  have : ∑ j, (ψ (y j) + (a + φ (y j)) - (ψ ((y - δ) j) + (a + φ ((y - δ) j)))) =
      ∑ j, (ψ (y j) - ψ (y j - δ j)) := by
    have hφ : ∑ j, (φ (y j) - φ (y j - δ j)) = 0 := by
      simp_rw [← map_sub, sub_sub_cancel, ← map_sum, hδ, map_zero]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← hφ]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.sub_apply]; ring
  rw [this, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := hψ _ (hy j) _ (hyδ j)
  rwa [sub_sub_cancel] at this

/-- **Proposition 117(b), conditioned products.** If `w = C ∏ⱼ gⱼ(yⱼ) e^{φⱼ(yⱼ)}` with `gⱼ > 0` on
`Kⱼ`, `log gⱼ` `L`-Lipschitz and `φⱼ` `Lφ`-Lipschitz on `Kⱼ`, then
`|log w y - log w (y - δ)| ≤ (L + Lφ) ‖δ‖₁` whenever all `yⱼ, yⱼ - δⱼ ∈ Kⱼ`. -/
lemma log_incr_joint {C : ℝ} (hC : 0 < C) {K : Fin n → Set E} (g φ : Fin n → E → ℝ)
    (hg : ∀ j, ∀ p ∈ K j, 0 < g j p) {L Lφ : ℝ}
    (hgL : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j, |Real.log (g j p) - Real.log (g j q)| ≤ L * ‖p - q‖)
    (hφL : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j, |φ j p - φ j q| ≤ Lφ * ‖p - q‖)
    (y δ : Fin n → E) (hy : ∀ j, y j ∈ K j) (hyδ : ∀ j, y j - δ j ∈ K j) :
    |Real.log (C * ∏ j, (g j (y j) * Real.exp (φ j (y j)))) -
      Real.log (C * ∏ j, (g j ((y - δ) j) * Real.exp (φ j ((y - δ) j))))| ≤
      (L + Lφ) * ∑ j, ‖δ j‖ := by
  have conv : ∀ z : Fin n → E, (∀ j, z j ∈ K j) →
      ∏ j, (g j (z j) * Real.exp (φ j (z j))) =
        ∏ j, Real.exp (Real.log (g j (z j)) + φ j (z j)) := by
    intro z hz
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.exp_add, Real.exp_log (hg j _ (hz j))]
  rw [conv y hy, conv (y - δ) (fun j => by simpa using hyδ j),
    log_prod_sub hC (fun j p => Real.log (g j p) + φ j p), Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have h1 := hgL j _ (hy j) _ (hyδ j)
  have h2 := hφL j _ (hy j) _ (hyδ j)
  rw [sub_sub_cancel] at h1 h2
  simp only [Pi.sub_apply]
  calc _ = |(Real.log (g j (y j)) - Real.log (g j (y j - δ j))) +
        (φ j (y j) - φ j (y j - δ j))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end LogLip

section Final

variable {E : Type*} [NormedAddCommGroup E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] {n : ℕ}

/-- The hyperplane `{y | ∑ᵢ yᵢ = s}` of tuples. -/
def hyp (s : E) : Set (Fin n → E) := {y | ∑ i, y i = s}

lemma measurableSet_hyp (s : E) : MeasurableSet (hyp (n := n) s) :=
  (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) (measurableSet_singleton s)

lemma hyp_sub_iff {s : E} {δ : Fin n → E} (hδ : ∑ i, δ i = 0) (y : Fin n → E) :
    y - δ ∈ hyp s ↔ y ∈ hyp s := by
  simp [hyp, Finset.sum_sub_distrib, hδ]

lemma sum_sub_eq_zero {x x' : Fin n → E} (h : ∑ i, x i = ∑ i, x' i) :
    ∑ i, (x' - x) i = 0 := by
  simp [Finset.sum_sub_distrib, h]

lemma real_coord_sub_notMem (β : Measure (Fin n → E)) (j : Fin n) (e : E) {K : Set E}
    (hK : MeasurableSet K) :
    β.real {y | y j - e ∉ K} = (marg β j).real {z | z - e ∉ K} := by
  rw [map_measureReal_apply (measurable_pi_apply j) ((measurable_sub_const e) hK.compl)]
  rfl

/-- `TV` of translates of one measure on a group. -/
lemma tv_map_add_right {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [IsProbabilityMeasure μ] (u u' : G) :
    tv (μ.map (· + u)) (μ.map (· + u')) = tv μ (μ.map (· + (u' - u))) := by
  have h : μ.map (· + u') = (μ.map (· + (u' - u))).map (· + u) := by
    rw [Measure.map_map (measurable_add_const u) (measurable_add_const _)]
    congr 1; funext y; simp only [Function.comp_apply]
    rw [add_assoc, sub_add_cancel]
  rw [h]
  have := tv_map_equiv μ (μ.map (· + (u' - u))) (MeasurableEquiv.addRight u)
  simpa using this

variable [(volume : Measure E).IsAddRightInvariant]

/-- **Proposition 109(a).** For a complete mix `Y` of `U(K)` (no density needed),
`TV(x + Y, x' + Y) ≥ t(δᵢ)` for every `i`, where `δ = x' - x`. -/
theorem prop109_a {K : Set E} (hK : MeasurableSet K) (h0 : volume K ≠ 0) (htop : volume K ≠ ⊤)
    {β : Measure (Fin n → E)} (hP : IsCompleteMix n (unifSet K) β) (x x' : Fin n → E)
    (i : Fin n) : tfun K ((x' - x) i) ≤ tv (β.map (x + ·)) (β.map (x' + ·)) := by
  have := hP.1
  have h := tv_marg_le β x x' i
  rwa [show marg β i = unifSet K from hP.2.2 i, tv_unifSet_translate hK h0 htop] at h

lemma real_unif_sub_notMem {K : Set E} (hK : MeasurableSet K) (e : E) :
    (unifSet K).real {z | z - e ∉ K} = tfun K e := by
  rw [unifSet_real_apply (C := {z | z - e ∉ K}) ((measurable_sub_const e) hK.compl), tfun]
  congr 2
  ext z; simp [tr, and_comm]

/-- **Proposition 109(b).** Let `Y` be an `n`-complete mix of `U(K)` whose distribution `β` has a
density `w` with respect to a measure `λ` invariant under translation by `δ = x' - x`
(in the paper, Lebesgue measure on the hyperplane), with `w = 0` off
`𝒯 = {y ∈ Kⁿ | ∑ yᵢ = s}`, and `|log w y - log w (y - δ)| ≤ L ‖δ‖₁` (with `w > 0`) whenever
`y, y - δ ∈ 𝒯`. Then `TV(x + Y, x' + Y) ≤ ½ (e^{L‖δ‖₁} - 1) + ∑ᵢ t(δᵢ)`. -/
theorem prop109_b {K : Set E} (hK : MeasurableSet K) (htop : volume K ≠ ⊤)
    (lam : Measure (Fin n → E)) {w : (Fin n → E) → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hint : Integrable w lam) (h1 : ∫ y, w y ∂lam = 1) (s : E)
    (hwT : ∀ y, y ∉ supp (hyp s) (fun _ => K) → w y = 0)
    (hP : IsCompleteMix n (unifSet K) (dens lam w)) (x x' : Fin n → E)
    (hsum : ∑ i, x i = ∑ i, x' i) (hlam : lam.map (· + (x' - x)) = lam) {L : ℝ} (hL : 0 ≤ L)
    (hlog : ∀ y, y ∈ supp (hyp s) (fun _ => K) → y - (x' - x) ∈ supp (hyp s) (fun _ => K) →
      0 < w y ∧ 0 < w (y - (x' - x)) ∧
        |Real.log (w y) - Real.log (w (y - (x' - x)))| ≤ L * ∑ i, ‖(x' - x) i‖) :
    tv ((dens lam w).map (x + ·)) ((dens lam w).map (x' + ·)) ≤
      (1 / 2) * (Real.exp (L * ∑ i, ‖(x' - x) i‖) - 1) + ∑ i, tfun K ((x' - x) i) := by
  have := dens_isProb lam hint hw0 h1
  set δ := x' - x
  have hδ : ∑ i, δ i = 0 := sum_sub_eq_zero hsum
  rw [tv_add_left_eq]
  refine (tv_translate_le lam δ hlam (measurableSet_hyp s) (hyp_sub_iff hδ) (fun _ => hK) hw
    hw0 hwT hint h1 (c := L * ∑ i, ‖δ i‖)
    (mul_nonneg hL (Finset.sum_nonneg fun i _ => norm_nonneg _)) fun y hy hyδ => ?_).trans
    (le_of_eq ?_)
  · obtain ⟨a, b, c⟩ := hlog y hy hyδ
    exact ratio_of_log a b c
  · congr 1
    rw [Finset.mul_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := real_coord_sub_notMem (dens lam w) j (δ j) hK
      have e2 := real_coord_sub_notMem (dens lam w) j (-δ j) hK
      have e3 := real_unif_sub_notMem hK (-δ j)
      simp only [sub_neg_eq_add] at e2 e3
      rw [e1, e2, show marg (dens lam w) j = unifSet K from hP.2.2 j, real_unif_sub_notMem hK,
        e3, tfun_neg hK htop]
      ring

/-- **Proposition 109(b) for conditioned products** `β_h`: if `w = C ∏ᵢ h(yᵢ)` on `𝒯` with
`log h = ψ + ℓ`, `ℓ` affine and `ψ` `Lψ`-Lipschitz on `K`, the bound holds with `L = Lψ`. -/
theorem prop109_b_conditioned {K : Set E} (hK : MeasurableSet K) (htop : volume K ≠ ⊤)
    [NormedSpace ℝ E] (lam : Measure (Fin n → E)) {w : (Fin n → E) → ℝ} (hw : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hint : Integrable w lam) (h1 : ∫ y, w y ∂lam = 1) (s : E)
    (hwT : ∀ y, y ∉ supp (hyp s) (fun _ => K) → w y = 0)
    {C : ℝ} (hC : 0 < C) (ψ : E → ℝ) (a : ℝ) (φ : E →ₗ[ℝ] ℝ) {Lψ : ℝ} (hLψ : 0 ≤ Lψ)
    (hψ : ∀ p ∈ K, ∀ q ∈ K, |ψ p - ψ q| ≤ Lψ * ‖p - q‖)
    (hwh : ∀ y ∈ supp (hyp s) (fun _ => K), w y = C * ∏ j, Real.exp (ψ (y j) + (a + φ (y j))))
    (hP : IsCompleteMix n (unifSet K) (dens lam w)) (x x' : Fin n → E)
    (hsum : ∑ i, x i = ∑ i, x' i) (hlam : lam.map (· + (x' - x)) = lam) :
    tv ((dens lam w).map (x + ·)) ((dens lam w).map (x' + ·)) ≤
      (1 / 2) * (Real.exp (Lψ * ∑ i, ‖(x' - x) i‖) - 1) + ∑ i, tfun K ((x' - x) i) := by
  refine prop109_b hK htop lam hw hw0 hint h1 s hwT hP x x' hsum hlam hLψ fun y hy hyδ => ?_
  have hyK : ∀ j, y j ∈ K := fun j => by
    have := hy.2; simp only [Set.mem_iInter, Set.mem_preimage] at this; exact this j
  have hyδK : ∀ j, y j - (x' - x) j ∈ K := fun j => by
    have := hyδ.2; simp only [Set.mem_iInter, Set.mem_preimage] at this; simpa using this j
  rw [hwh y hy, hwh _ hyδ]
  refine ⟨by positivity, by positivity, ?_⟩
  exact log_incr_conditioned hC ψ a φ hψ y (x' - x) (sum_sub_eq_zero hsum) hyK hyδK

/-- `tⱼ(e) = ∫_{Kⱼ \ (Kⱼ + e)} gⱼ`. -/
def tdens (K : Set E) (g : E → ℝ) (e : E) : ℝ := ∫ z in K \ tr K e, g z

lemma real_dens_sub_notMem {K : Set E} (hK : MeasurableSet K) {g : E → ℝ}
    (hgi : Integrable g volume) (hg0 : ∀ z, 0 ≤ g z) (hgK : ∀ z, z ∉ K → g z = 0) (e : E) :
    (dens volume g).real {z | z - e ∉ K} = tdens K g e := by
  rw [dens_real_apply volume hgi hg0 (A := {z | z - e ∉ K}) ((measurable_sub_const e) hK.compl),
    tdens]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (t := {z | z - e ∉ K})
    ((measurable_sub_const e) hK.compl)
  · intro z hz; exact hz.2
  · intro z hz
    apply hgK
    intro hzK
    exact hz.2 ⟨hzK, hz.1⟩

/-- **Proposition 117(a).** For a joint mix `Y` with marginals `μⱼ`,
`TV(x + Y, x' + Y) ≥ TV(μⱼ, μⱼ(· - δⱼ))` for every `j`. -/
theorem prop117_a {β : Measure (Fin n → E)} [IsProbabilityMeasure β] (x x' : Fin n → E)
    (j : Fin n) :
    tv (marg β j) ((marg β j).map (· + (x' - x) j)) ≤ tv (β.map (x + ·)) (β.map (x' + ·)) := by
  have h := tv_marg_le β x x' j
  rwa [tv_map_add_right] at h

/-- **Proposition 117(b).** Let `Y` be a joint mix of densities `gⱼ` vanishing outside `Kⱼ`, whose
distribution `β` has a density `w` with respect to a measure `λ` invariant under translation by
`δ = x' - x`, with `w = 0` off `𝒯 = {y ∈ ∏ Kⱼ | ∑ yⱼ = s}` and
`|log w y - log w (y - δ)| ≤ L' ‖δ‖₁` (with `w > 0`) whenever `y, y - δ ∈ 𝒯`. Then
`TV(x + Y, x' + Y) ≤ ½ (e^{L'‖δ‖₁} - 1) + ½ ∑ⱼ (tⱼ(δⱼ) + tⱼ(-δⱼ))`. -/
theorem prop117_b {K : Fin n → Set E} (hK : ∀ j, MeasurableSet (K j)) (g : Fin n → E → ℝ)
    (hgi : ∀ j, Integrable (g j) volume) (hg0 : ∀ j z, 0 ≤ g j z)
    (hgK : ∀ j z, z ∉ K j → g j z = 0)
    (lam : Measure (Fin n → E)) {w : (Fin n → E) → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hint : Integrable w lam) (h1 : ∫ y, w y ∂lam = 1) (s : E)
    (hwT : ∀ y, y ∉ supp (hyp s) K → w y = 0)
    (hP : IsJointMix (fun j => dens volume (g j)) (dens lam w)) (x x' : Fin n → E)
    (hsum : ∑ i, x i = ∑ i, x' i) (hlam : lam.map (· + (x' - x)) = lam) {L' : ℝ} (hL : 0 ≤ L')
    (hlog : ∀ y, y ∈ supp (hyp s) K → y - (x' - x) ∈ supp (hyp s) K →
      0 < w y ∧ 0 < w (y - (x' - x)) ∧
        |Real.log (w y) - Real.log (w (y - (x' - x)))| ≤ L' * ∑ i, ‖(x' - x) i‖) :
    tv ((dens lam w).map (x + ·)) ((dens lam w).map (x' + ·)) ≤
      (1 / 2) * (Real.exp (L' * ∑ i, ‖(x' - x) i‖) - 1) +
        (1 / 2) * ∑ j, (tdens (K j) (g j) ((x' - x) j) + tdens (K j) (g j) (-(x' - x) j)) := by
  have := dens_isProb lam hint hw0 h1
  set δ := x' - x
  have hδ : ∑ i, δ i = 0 := sum_sub_eq_zero hsum
  rw [tv_add_left_eq]
  refine (tv_translate_le lam δ hlam (measurableSet_hyp s) (hyp_sub_iff hδ) hK hw
    hw0 hwT hint h1 (c := L' * ∑ i, ‖δ i‖)
    (mul_nonneg hL (Finset.sum_nonneg fun i _ => norm_nonneg _)) fun y hy hyδ => ?_).trans
    (le_of_eq ?_)
  · obtain ⟨a, b, c⟩ := hlog y hy hyδ
    exact ratio_of_log a b c
  · congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := real_coord_sub_notMem (dens lam w) j (δ j) (hK j)
    have e2 := real_coord_sub_notMem (dens lam w) j (-δ j) (hK j)
    have e3 := real_dens_sub_notMem (hK j) (hgi j) (hg0 j) (hgK j) (-δ j)
    simp only [sub_neg_eq_add] at e2 e3
    rw [e1, e2, show marg (dens lam w) j = dens volume (g j) from hP.2.2 j,
      real_dens_sub_notMem (hK j) (hgi j) (hg0 j) (hgK j), e3]

/-- **Proposition 117(b) for conditioned products**: if `w = C ∏ⱼ gⱼ(yⱼ) e^{φⱼ(yⱼ)}` on `𝒯`,
`gⱼ > 0` and `log gⱼ` `L`-Lipschitz on `Kⱼ`, and `φⱼ` `Lφ`-Lipschitz on `Kⱼ`, the bound holds
with `L' = L + Lφ`. -/
theorem prop117_b_conditioned [NormedSpace ℝ E] {K : Fin n → Set E}
    (hK : ∀ j, MeasurableSet (K j)) (g : Fin n → E → ℝ)
    (hgi : ∀ j, Integrable (g j) volume) (hg0 : ∀ j z, 0 ≤ g j z)
    (hgK : ∀ j z, z ∉ K j → g j z = 0) (hgpos : ∀ j, ∀ p ∈ K j, 0 < g j p)
    {L Lφ : ℝ} (hL : 0 ≤ L) (hLφ : 0 ≤ Lφ)
    (hgL : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j, |Real.log (g j p) - Real.log (g j q)| ≤ L * ‖p - q‖)
    (φ : Fin n → E → ℝ) (hφL : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j, |φ j p - φ j q| ≤ Lφ * ‖p - q‖)
    (lam : Measure (Fin n → E)) {w : (Fin n → E) → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hint : Integrable w lam) (h1 : ∫ y, w y ∂lam = 1) (s : E)
    (hwT : ∀ y, y ∉ supp (hyp s) K → w y = 0) {C : ℝ} (hC : 0 < C)
    (hwh : ∀ y ∈ supp (hyp s) K, w y = C * ∏ j, (g j (y j) * Real.exp (φ j (y j))))
    (hP : IsJointMix (fun j => dens volume (g j)) (dens lam w)) (x x' : Fin n → E)
    (hsum : ∑ i, x i = ∑ i, x' i) (hlam : lam.map (· + (x' - x)) = lam) :
    tv ((dens lam w).map (x + ·)) ((dens lam w).map (x' + ·)) ≤
      (1 / 2) * (Real.exp ((L + Lφ) * ∑ i, ‖(x' - x) i‖) - 1) +
        (1 / 2) * ∑ j, (tdens (K j) (g j) ((x' - x) j) + tdens (K j) (g j) (-(x' - x) j)) := by
  refine prop117_b hK g hgi hg0 hgK lam hw hw0 hint h1 s hwT hP x x' hsum hlam
    (add_nonneg hL hLφ) fun y hy hyδ => ?_
  have hyK : ∀ j, y j ∈ K j := fun j => by
    have := hy.2; simp only [Set.mem_iInter, Set.mem_preimage] at this; exact this j
  have hyδK : ∀ j, y j - (x' - x) j ∈ K j := fun j => by
    have := hyδ.2; simp only [Set.mem_iInter, Set.mem_preimage] at this; simpa using this j
  have hpos : ∀ z : Fin n → E, (∀ j, z j ∈ K j) →
      0 < C * ∏ j, (g j (z j) * Real.exp (φ j (z j))) := fun z hz =>
    mul_pos hC (Finset.prod_pos fun j _ => mul_pos (hgpos j _ (hz j)) (Real.exp_pos _))
  rw [hwh y hy, hwh _ hyδ]
  refine ⟨hpos y hyK, hpos _ (fun j => by simpa using hyδK j), ?_⟩
  exact log_incr_joint hC g φ hgpos hgL hφL y (x' - x) hyK hyδK

end Final

/-! ### Lebesgue measure on the hyperplane

The paper's `λ` is Lebesgue measure on `{y | ∑ yᵢ = s}`, through the coordinates
`(y₁, …, y_{n-1})`. We construct it and check that it satisfies the invariance hypothesis of
Propositions 109 and 117 for every `δ` with `∑ δᵢ = 0`. -/

section Hyperplane

variable {E : Type*} [NormedAddCommGroup E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [SigmaFinite (volume : Measure E)]
  [(volume : Measure E).IsAddRightInvariant] {m : ℕ}

/-- The parametrisation `z ↦ (z, s - ∑ z)` of the hyperplane `∑ yᵢ = s`. -/
def hypEmb (s : E) (z : Fin m → E) : Fin (m + 1) → E := Fin.snoc z (s - ∑ i, z i)

lemma measurable_hypEmb (s : E) : Measurable (hypEmb (m := m) s) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [hypEmb, Fin.snoc_last]
    exact measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  · simp only [hypEmb, Fin.snoc_castSucc]
    exact measurable_pi_apply j

/-- Lebesgue measure on the hyperplane `∑ yᵢ = s`. -/
def hypMeasure (s : E) : Measure (Fin (m + 1) → E) :=
  (volume : Measure (Fin m → E)).map (hypEmb s)

lemma hypEmb_add (s : E) (z : Fin m → E) (δ : Fin (m + 1) → E) (hδ : ∑ i, δ i = 0) :
    hypEmb s z + δ = hypEmb s (z + Fin.init δ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [hypEmb, Pi.add_apply, Fin.snoc_last, Fin.init]
    rw [Fin.sum_univ_castSucc] at hδ
    simp only [Finset.sum_add_distrib]
    have : δ (Fin.last m) = -∑ i : Fin m, δ (Fin.castSucc i) := eq_neg_of_add_eq_zero_right hδ
    rw [this]; abel
  · simp [hypEmb, Fin.init]

theorem hypMeasure_map_add (s : E) (δ : Fin (m + 1) → E) (hδ : ∑ i, δ i = 0) :
    (hypMeasure (m := m) s).map (· + δ) = hypMeasure s := by
  rw [hypMeasure, Measure.map_map (measurable_add_const δ) (measurable_hypEmb s)]
  have : (· + δ) ∘ hypEmb (m := m) s = hypEmb s ∘ (· + Fin.init δ) := by
    funext z; exact hypEmb_add s z δ hδ
  rw [this, ← Measure.map_map (measurable_hypEmb s) (measurable_add_const _),
    map_add_right_eq_self]

lemma hypMeasure_hyp (s : E) : ∀ᵐ y ∂(hypMeasure (m := m) s), ∑ i, y i = s := by
  rw [hypMeasure]
  refine (ae_map_iff (measurable_hypEmb s).aemeasurable (p := fun y => ∑ i, y i = s)
    ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i) (measurableSet_singleton s))).2 ?_
  exact Filter.Eventually.of_forall fun z => by simp [hypEmb, Fin.sum_univ_castSucc]

/-- **Proposition 109(b)** with `λ` Lebesgue measure on the hyperplane (`n = m + 1`). -/
theorem prop109_b_hyp {K : Set E} (hK : MeasurableSet K) (htop : volume K ≠ ⊤) (s : E)
    {w : (Fin (m + 1) → E) → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hint : Integrable w (hypMeasure s)) (h1 : ∫ y, w y ∂(hypMeasure s) = 1)
    (hwT : ∀ y, y ∉ supp (hyp s) (fun _ => K) → w y = 0)
    (hP : IsCompleteMix (m + 1) (unifSet K) (dens (hypMeasure s) w)) (x x' : Fin (m + 1) → E)
    (hsum : ∑ i, x i = ∑ i, x' i) {L : ℝ} (hL : 0 ≤ L)
    (hlog : ∀ y, y ∈ supp (hyp s) (fun _ => K) → y - (x' - x) ∈ supp (hyp s) (fun _ => K) →
      0 < w y ∧ 0 < w (y - (x' - x)) ∧
        |Real.log (w y) - Real.log (w (y - (x' - x)))| ≤ L * ∑ i, ‖(x' - x) i‖) :
    tv ((dens (hypMeasure s) w).map (x + ·)) ((dens (hypMeasure s) w).map (x' + ·)) ≤
      (1 / 2) * (Real.exp (L * ∑ i, ‖(x' - x) i‖) - 1) + ∑ i, tfun K ((x' - x) i) :=
  prop109_b hK htop _ hw hw0 hint h1 s hwT hP x x' hsum
    (hypMeasure_map_add s _ (sum_sub_eq_zero hsum)) hL hlog

/-- **Proposition 109(c)** with `λ` Lebesgue measure on the hyperplane `∑ δᵢ = 0`: if
`β(S) = 1` and `S - S` is null for it, then `TV(x + Y, x + δ + Y) = 1` for almost every such
`δ`. -/
theorem prop109_c_hyp (β : Measure (Fin (m + 1) → E)) [IsProbabilityMeasure β]
    {S : Set (Fin (m + 1) → E)} (hS : MeasurableSet S) (hβS : β S = 1)
    (hnull : hypMeasure (0 : E) (S - S) = 0) (x : Fin (m + 1) → E) :
    ∀ᵐ δ ∂(hypMeasure (0 : E)), tv (β.map (x + ·)) (β.map ((x + δ) + ·)) = 1 :=
  tv_eq_one_ae β hS hβS _ hnull x

/-- **Proposition 117(b)** with `λ` Lebesgue measure on the hyperplane (`n = m + 1`). -/
theorem prop117_b_hyp {K : Fin (m + 1) → Set E} (hK : ∀ j, MeasurableSet (K j))
    (g : Fin (m + 1) → E → ℝ) (hgi : ∀ j, Integrable (g j) volume) (hg0 : ∀ j z, 0 ≤ g j z)
    (hgK : ∀ j z, z ∉ K j → g j z = 0) (s : E) {w : (Fin (m + 1) → E) → ℝ} (hw : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hint : Integrable w (hypMeasure s))
    (h1 : ∫ y, w y ∂(hypMeasure s) = 1) (hwT : ∀ y, y ∉ supp (hyp s) K → w y = 0)
    (hP : IsJointMix (fun j => dens volume (g j)) (dens (hypMeasure s) w))
    (x x' : Fin (m + 1) → E) (hsum : ∑ i, x i = ∑ i, x' i) {L' : ℝ} (hL : 0 ≤ L')
    (hlog : ∀ y, y ∈ supp (hyp s) K → y - (x' - x) ∈ supp (hyp s) K →
      0 < w y ∧ 0 < w (y - (x' - x)) ∧
        |Real.log (w y) - Real.log (w (y - (x' - x)))| ≤ L' * ∑ i, ‖(x' - x) i‖) :
    tv ((dens (hypMeasure s) w).map (x + ·)) ((dens (hypMeasure s) w).map (x' + ·)) ≤
      (1 / 2) * (Real.exp (L' * ∑ i, ‖(x' - x) i‖) - 1) +
        (1 / 2) * ∑ j, (tdens (K j) (g j) ((x' - x) j) + tdens (K j) (g j) (-(x' - x) j)) :=
  prop117_b hK g hgi hg0 hgK _ hw hw0 hint h1 s hwT hP x x' hsum
    (hypMeasure_map_add s _ (sum_sub_eq_zero hsum)) hL hlog

end Hyperplane


/-! ### Proposition 108: the projection bound in every dimension

Write `ℝ^d = ℝ × F` with `F = ℝ^{d-1}` and let the translation `t = (τ, 0)` point along the
first factor (every direction is of this form after a rotation, which preserves volumes). Then
the projection of `K` onto the hyperplane orthogonal to `t` is `Prod.snd '' K ⊆ F`, and every
line parallel to `t` meets `K \ (K + t)` in a set of length at most `|τ|` when it meets `K` in an
interval. -/

section Projection

/-- In dimension one, `|I \ (I + τ)| ≤ |τ|` for every interval (order-connected set) `I`. -/
lemma volume_sdiff_tr_le_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected) (τ : ℝ) :
    volume (I \ tr I τ) ≤ ENNReal.ofReal |τ| := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_)
  simp only [tr, Set.mem_sdiff, Set.mem_preimage] at hx hy
  rw [Real.dist_eq]
  -- if `x - τ` lay between two points of `I`, it would lie in `I`
  have key : ∀ a ∈ I, ∀ b ∈ I, b - τ ∉ I → a ≤ b - τ → b - τ ≤ b → False :=
    fun a ha b hb hbτ h1 h2 => hbτ (hI.out ha hb ⟨h1, h2⟩)
  have key' : ∀ a ∈ I, ∀ b ∈ I, b - τ ∉ I → b ≤ b - τ → b - τ ≤ a → False :=
    fun a ha b hb hbτ h1 h2 => hbτ (hI.out hb ha ⟨h1, h2⟩)
  rcases le_total 0 τ with hτ | hτ
  · rw [abs_of_nonneg hτ, abs_le]
    constructor
    · by_contra h; exact key x hx.1 y hy.1 hy.2 (by linarith) (by linarith)
    · by_contra h; exact key y hy.1 x hx.1 hx.2 (by linarith) (by linarith)
  · rw [abs_of_nonpos hτ, abs_le]
    constructor
    · by_contra h; exact key' y hy.1 x hx.1 hx.2 (by linarith) (by linarith)
    · by_contra h; exact key' x hx.1 y hy.1 hy.2 (by linarith) (by linarith)

variable {F : Type*} [NormedAddCommGroup F] [MeasureSpace F] [BorelSpace F]
  [SecondCountableTopology F] [SFinite (volume : Measure F)]

/-- **Proposition 108, the projection bound** (Fubini along lines). For a measurable
`K ⊆ ℝ × F` whose lines parallel to `t = (τ, 0)` meet it in intervals (for instance a convex
`K`, see `volume_sdiff_tr_le_proj_of_convex`), `|K \ (K + t)| ≤ |τ| · |Prod.snd '' K|`; here
`Prod.snd '' K` is the projection of `K` onto the hyperplane orthogonal to `t`. -/
theorem volume_sdiff_tr_le_proj {K : Set (ℝ × F)} (hK : MeasurableSet K)
    (hline : ∀ y : F, ((fun x : ℝ => (x, y)) ⁻¹' K).OrdConnected) (τ : ℝ) :
    volume (K \ tr K ((τ, 0) : ℝ × F)) ≤ ENNReal.ofReal |τ| * volume (Prod.snd '' K) := by
  have hD : MeasurableSet (K \ tr K ((τ, 0) : ℝ × F)) := hK.diff ((measurable_sub_const _) hK)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hD]
  set P := Prod.snd '' K
  calc ∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹' (K \ tr K ((τ, 0) : ℝ × F)))
      ≤ ∫⁻ y, (toMeasurable volume P).indicator (fun _ => ENNReal.ofReal |τ|) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ P
        · rw [Set.indicator_of_mem (subset_toMeasurable _ _ hy)]
          have : (fun x : ℝ => (x, y)) ⁻¹' (K \ tr K ((τ, 0) : ℝ × F)) =
              ((fun x : ℝ => (x, y)) ⁻¹' K) \ tr ((fun x : ℝ => (x, y)) ⁻¹' K) τ := by
            ext x; simp [tr]
          rw [this]
          exact volume_sdiff_tr_le_of_ordConnected (hline y) τ
        · have : (fun x : ℝ => (x, y)) ⁻¹' (K \ tr K ((τ, 0) : ℝ × F)) = ∅ := by
            ext x
            simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false,
              not_and]
            intro hx
            exact absurd ⟨(x, y), hx, rfl⟩ hy
          simp [this]
    _ = ENNReal.ofReal |τ| * volume P := by
        rw [lintegral_indicator (measurableSet_toMeasurable _ _), setLIntegral_const,
          measure_toMeasurable]

/-- The projection bound for the function `t` of Proposition 108:
`t((τ, 0)) = |K \ (K + t)| / |K| ≤ |τ| |K|_t / |K|`. -/
theorem tfun_le_proj {K : Set (ℝ × F)} (hK : MeasurableSet K)
    (hline : ∀ y : F, ((fun x : ℝ => (x, y)) ⁻¹' K).OrdConnected) (τ : ℝ)
    (hP : volume (Prod.snd '' K) ≠ ⊤) :
    tfun K ((τ, 0) : ℝ × F) ≤ |τ| * volume.real (Prod.snd '' K) / volume.real K := by
  unfold tfun
  refine div_le_div_of_nonneg_right ?_ measureReal_nonneg
  have h := volume_sdiff_tr_le_proj hK hline τ
  rw [measureReal_def, measureReal_def, ← ENNReal.toReal_ofReal (abs_nonneg τ),
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP) h

omit [NormedAddCommGroup F] [MeasureSpace F] [BorelSpace F] [SecondCountableTopology F]
  [SFinite (volume : Measure F)] in
/-- The lines of a convex set are intervals. -/
lemma ordConnected_line_of_convex {F : Type*} [AddCommGroup F] [Module ℝ F] {K : Set (ℝ × F)}
    (hK : Convex ℝ K) (y : F) : ((fun x : ℝ => (x, y)) ⁻¹' K).OrdConnected := by
  refine Convex.ordConnected ?_
  intro a ha b hb θ η hθ hη hθη
  simp only [Set.mem_preimage] at ha hb ⊢
  have := hK ha hb hθ hη hθη
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
  rwa [← add_smul, hθη, one_smul] at this

/-- **Proposition 108, the projection bound for convex `K`** in `ℝ^d = ℝ × F`:
`|K \ (K + t)| ≤ |t| · |K|_t` for `t = (τ, 0)`. -/
theorem volume_sdiff_tr_le_proj_of_convex [NormedSpace ℝ F] {K : Set (ℝ × F)}
    (hK : MeasurableSet K) (hc : Convex ℝ K) (τ : ℝ) :
    volume (K \ tr K ((τ, 0) : ℝ × F)) ≤ ENNReal.ofReal |τ| * volume (Prod.snd '' K) :=
  volume_sdiff_tr_le_proj hK (ordConnected_line_of_convex hc) τ

end Projection

/-! ### Proposition 108: the projection bound in a general direction

A linear isometry of `E` onto `ℝ × t^⊥` sends `t` to `(|t|, 0)` and preserves volume, so the
bound for a general direction follows from the coordinate case. -/

section ProjectionDir

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The linear coordinates `x ↦ (e(P_t x), P_{t⊥} x) ∈ ℝ × t^⊥` adapted to a direction `t`, with
`e` a linear isometry of the line `ℝ t` onto `ℝ` that sends `t` to `|t|`. -/
def dirCoord (t : E) (ht : t ≠ 0) : E ≃ₗ[ℝ] ℝ × (ℝ ∙ t)ᗮ :=
  let u : E := ‖t‖⁻¹ • t
  have hu : ‖u‖ = 1 := norm_smul_inv_norm ht
  have hLu : (ℝ ∙ t) = (ℝ ∙ u) :=
    (Submodule.span_singleton_smul_eq (inv_ne_zero (norm_ne_zero_iff.2 ht)).isUnit t).symm
  let e : (ℝ ∙ t) ≃ₗᵢ[ℝ] ℝ :=
    (LinearIsometryEquiv.ofEq _ _ hLu).trans (LinearIsometryEquiv.toSpanUnitSingleton u hu).symm
  (ℝ ∙ t).orthogonalDecomposition.toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ _ ≪≫ₗ
    LinearEquiv.prodCongr e.toLinearEquiv (LinearEquiv.refl ℝ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dirCoord_apply (t : E) (ht : t ≠ 0) (x : E) :
    (dirCoord t ht x).2 = (ℝ ∙ t)ᗮ.orthogonalProjectionOnto x := by
  simp [dirCoord]

lemma dirCoord_self (t : E) (ht : t ≠ 0) : dirCoord t ht t = (‖t‖, 0) := by
  have hmem : t ∈ (ℝ ∙ t) := Submodule.mem_span_singleton_self t
  have hP : (ℝ ∙ t).orthogonalProjectionOnto t = ⟨t, hmem⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨t, hmem⟩
  have hQ : (ℝ ∙ t)ᗮ.orthogonalProjectionOnto t = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact hmem
  ext
  · simp [dirCoord, hP]
    rw [LinearIsometryEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [LinearIsometryEquiv.toSpanUnitSingleton_apply, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 ht)]
  · rw [dirCoord_apply, hQ]

lemma measurePreserving_dirCoord (t : E) (ht : t ≠ 0) :
    MeasurePreserving (dirCoord t ht) volume volume := by
  set L := (ℝ ∙ t)
  have h1 := (L.orthogonalDecomposition).measurePreserving
  have h2 := WithLp.volume_preserving_ofLp L Lᗮ
  set e : L ≃ₗᵢ[ℝ] ℝ := (LinearIsometryEquiv.ofEq _ _
      (Submodule.span_singleton_smul_eq (inv_ne_zero (norm_ne_zero_iff.2 ht)).isUnit t).symm).trans
      (LinearIsometryEquiv.toSpanUnitSingleton (‖t‖⁻¹ • t) (norm_smul_inv_norm ht)).symm
  have h3 : MeasurePreserving (Prod.map e (id : Lᗮ → Lᗮ)) volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact e.measurePreserving.prod (MeasurePreserving.id _)
  exact (h3.comp h2).comp h1

/-- **Proposition 108, the projection bound for convex `K` in a general direction**: for a
measurable convex `K ⊆ E` and any `t`, `|K \ (K + t)| ≤ |t| · |P_{t⊥} K|`, where `P_{t⊥} K` is the
orthogonal projection of `K` onto the hyperplane `t^⊥`, measured by its Lebesgue measure. The
proof rotates `t` onto the first axis with `dirCoord` and applies
`volume_sdiff_tr_le_proj_of_convex`. -/
theorem volume_sdiff_tr_le_proj_dir {K : Set E} (hK : MeasurableSet K) (hc : Convex ℝ K)
    (t : E) :
    volume (K \ tr K t) ≤
      ENNReal.ofReal ‖t‖ * volume ((ℝ ∙ t)ᗮ.orthogonalProjectionOnto '' K) := by
  by_cases ht : t = 0
  · subst ht; simp [tr_zero]
  set D := dirCoord t ht
  have hDc : Continuous D := LinearMap.continuous_of_finiteDimensional D.toLinearMap
  have hDsc : Continuous D.symm := LinearMap.continuous_of_finiteDimensional D.symm.toLinearMap
  set K' : Set (ℝ × (ℝ ∙ t)ᗮ) := D.symm ⁻¹' K
  have hK' : MeasurableSet K' := hDsc.measurable hK
  have hc' : Convex ℝ K' := hc.linear_preimage D.symm.toLinearMap
  have hpre : D ⁻¹' (K' \ tr K' ((‖t‖, 0) : ℝ × (ℝ ∙ t)ᗮ)) = K \ tr K t := by
    ext x
    simp only [K', tr, Set.mem_preimage, Set.mem_sdiff, ← dirCoord_self t ht, ← map_sub,
      LinearEquiv.symm_apply_apply, D]
  have himg : Prod.snd '' K' = (ℝ ∙ t)ᗮ.orthogonalProjectionOnto '' K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨D.symm z, hz, by rw [← dirCoord_apply t ht]; simp [D]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨D x, by simpa [K'] using hx, dirCoord_apply t ht x⟩
  have hD : volume (D ⁻¹' (K' \ tr K' ((‖t‖, 0) : ℝ × (ℝ ∙ t)ᗮ))) =
      volume (K' \ tr K' ((‖t‖, 0) : ℝ × (ℝ ∙ t)ᗮ)) :=
    (measurePreserving_dirCoord t ht).measure_preimage
      ((hK'.diff ((measurable_sub_const ((‖t‖, 0) : ℝ × (ℝ ∙ t)ᗮ)) hK')).nullMeasurableSet)
  rw [hpre] at hD
  rw [hD, ← himg]
  have h := volume_sdiff_tr_le_proj_of_convex hK' hc' ‖t‖
  rwa [abs_norm] at h

/-- The projection bound for `t` of Proposition 108 in a general direction:
`t(e) = |K \ (K + e)| / |K| ≤ |e| · |P_{e⊥} K| / |K|` for measurable convex `K`. -/
theorem tfun_le_proj_dir {K : Set E} (hK : MeasurableSet K) (hc : Convex ℝ K) (t : E)
    (hP : volume ((ℝ ∙ t)ᗮ.orthogonalProjectionOnto '' K) ≠ ⊤) :
    tfun K t ≤ ‖t‖ * volume.real ((ℝ ∙ t)ᗮ.orthogonalProjectionOnto '' K) / volume.real K := by
  unfold tfun
  refine div_le_div_of_nonneg_right ?_ measureReal_nonneg
  have h := volume_sdiff_tr_le_proj_dir hK hc t
  rw [measureReal_def, measureReal_def, ← ENNReal.toReal_ofReal (norm_nonneg t),
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP) h

end ProjectionDir

/-! ### Proposition 109(c) for complete mixes on sets of lower dimension

Lebesgue measure on the hyperplane gives measure zero to every affine subspace of smaller
dimension than the hyperplane; this applies to the cyclic complete mixes `(X, AX, …, A^{n-1}X)`
of the paper (Remark `g:rem:semigroup`). -/

section LowDim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {m : ℕ}

/-- The first `m` coordinates of an `(m + 1)`-tuple, as a linear map. -/
def initL : (Fin (m + 1) → E) →ₗ[ℝ] (Fin m → E) where
  toFun y := fun i => y (Fin.castSucc i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma initL_hypEmb (s : E) (z : Fin m → E) : initL (hypEmb s z) = z := by
  funext i; simp [initL, hypEmb]

/-- **Lower-dimensional sets are null on the hyperplane.** An affine subspace `c + V` with
`dim V < m · dim E` (the dimension of the hyperplane in `(E)^{m+1}`) is null for `hypMeasure s`. -/
theorem hypMeasure_affine_null [SecondCountableTopology E] (s : E) (c : Fin (m + 1) → E)
    (V : Submodule ℝ (Fin (m + 1) → E)) (hV : Module.finrank ℝ V < m * Module.finrank ℝ E) :
    hypMeasure (m := m) s {y | y - c ∈ V} = 0 := by
  have hclosed : IsClosed {y : Fin (m + 1) → E | y - c ∈ V} :=
    (Submodule.isClosed_of_finiteDimensional V).preimage (continuous_id.sub continuous_const)
  rw [hypMeasure, Measure.map_apply (measurable_hypEmb s) hclosed.measurableSet]
  set W := V.map (initL (E := E) (m := m))
  have hW : W ≠ ⊤ := by
    intro h
    have h1 : Module.finrank ℝ W = m * Module.finrank ℝ E := by
      rw [h, finrank_top, Module.finrank_pi_fintype]; simp
    have h2 : Module.finrank ℝ W ≤ Module.finrank ℝ V := Submodule.finrank_map_le _ _
    omega
  have hsub : hypEmb s ⁻¹' {y | y - c ∈ V} ⊆ (fun z => z - initL c) ⁻¹' (W : Set (Fin m → E)) := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
    have : z - initL c = initL (hypEmb s z - c) := by rw [map_sub, initL_hypEmb]
    rw [this]
    exact Submodule.mem_map_of_mem hz
  refine measure_mono_null hsub ?_
  simp only [sub_eq_add_neg]
  rw [measure_preimage_add_right]
  exact Measure.addHaar_submodule _ W hW

/-- If `S` lies in an affine subspace `c + V` with `dim V < m · dim E`, then `S - S` is null for
Lebesgue measure on the hyperplane `∑ δᵢ = 0`: the hypothesis of Proposition 109(c). -/
lemma hypMeasure_sub_null [SecondCountableTopology E] {S : Set (Fin (m + 1) → E)}
    (c : Fin (m + 1) → E) (V : Submodule ℝ (Fin (m + 1) → E))
    (hV : Module.finrank ℝ V < m * Module.finrank ℝ E) (hS : ∀ y ∈ S, y - c ∈ V) :
    hypMeasure (0 : E) (S - S) = 0 := by
  refine measure_mono_null ?_ (hypMeasure_affine_null 0 0 V hV)
  rintro _ ⟨y, hy, y', hy', rfl⟩
  simp only [Set.mem_ofPred_eq, sub_zero]
  have := V.sub_mem (hS y hy) (hS y' hy')
  rwa [sub_sub_sub_cancel_right] at this

/-- The orbit map `x ↦ (x, A x, …, A^m x)` of an affine map `A`. -/
def orbitMap (A : E →ᵃ[ℝ] E) (x : E) : Fin (m + 1) → E := fun i => (A ^ (i : ℕ)) x

/-- The linear part of the orbit map. -/
def orbitLin (A : E →ᵃ[ℝ] E) : E →ₗ[ℝ] (Fin (m + 1) → E) :=
  LinearMap.pi fun i => A.linear ^ (i : ℕ)

lemma pow_apply_eq (A : E →ᵃ[ℝ] E) (k : ℕ) (x : E) :
    (A ^ k) x = (A ^ k) 0 + (A.linear ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ']
    change A ((A ^ k) x) = A ((A ^ k) 0) + A.linear ((A.linear ^ k) x)
    rw [ih]
    have := A.map_vadd ((A ^ k) 0) ((A.linear ^ k) x)
    rw [vadd_eq_add, vadd_eq_add] at this
    rw [add_comm ((A ^ k) 0), this, add_comm]

lemma orbitMap_sub_mem (A : E →ᵃ[ℝ] E) (x : E) :
    orbitMap (m := m) A x - orbitMap A 0 ∈ LinearMap.range (orbitLin (m := m) A) := by
  refine ⟨x, ?_⟩
  funext i
  simp only [orbitLin, LinearMap.pi_apply, orbitMap, Pi.sub_apply]
  rw [pow_apply_eq A i x]; abel

lemma continuous_orbitMap (A : E →ᵃ[ℝ] E) : Continuous (orbitMap (m := m) A) := by
  have : orbitMap (m := m) A = fun x => orbitMap A 0 + orbitLin A x := by
    funext x
    have := orbitMap_sub_mem (m := m) A x
    obtain ⟨y, hy⟩ := this
    funext i
    simp only [orbitLin, LinearMap.pi_apply, orbitMap, Pi.add_apply]
    rw [pow_apply_eq A i x]
  rw [this]
  exact continuous_const.add (LinearMap.continuous_of_finiteDimensional _)

/-- **Proposition 109(c) for the cyclic complete mixes.** Let `n = m + 1 ≥ 3`, `E ≠ 0`, let `A`
be an affine map of `E`, and let `β` be the distribution of `(X, AX, …, A^m X)` for a random `X`
with any distribution `μ`. Then `TV(x + Y, x + δ + Y) = 1` for Lebesgue-almost every `δ` in the
hyperplane `∑ δᵢ = 0`: the set `E` of the paper lies in an affine subspace of dimension
`≤ dim E < m · dim E`. -/
theorem prop109_c_cyclic [SecondCountableTopology E] [Nontrivial E] (hm : 2 ≤ m)
    (A : E →ᵃ[ℝ] E) (μ : Measure E) [IsProbabilityMeasure μ] (x : Fin (m + 1) → E) :
    ∀ᵐ δ ∂(hypMeasure (0 : E)),
      tv ((μ.map (orbitMap A)).map (x + ·)) ((μ.map (orbitMap A)).map ((x + δ) + ·)) = 1 := by
  set V := LinearMap.range (orbitLin (m := m) A)
  set S := {y : Fin (m + 1) → E | y - orbitMap A 0 ∈ V}
  have hSc : IsClosed S :=
    (Submodule.isClosed_of_finiteDimensional V).preimage (continuous_id.sub continuous_const)
  have hmeas : Measurable (orbitMap (m := m) A) := (continuous_orbitMap A).measurable
  have hβS : μ.map (orbitMap A) S = 1 := by
    rw [Measure.map_apply hmeas hSc.measurableSet]
    have : orbitMap A ⁻¹' S = Set.univ := by
      ext y; simpa [S, V] using orbitMap_sub_mem (m := m) A y
    rw [this, measure_univ]
  have hV : Module.finrank ℝ V < m * Module.finrank ℝ E := by
    have h1 : Module.finrank ℝ V ≤ Module.finrank ℝ E := LinearMap.finrank_range_le _
    have h2 : 0 < Module.finrank ℝ E := Module.finrank_pos
    nlinarith
  exact prop109_c_hyp _ hSc.measurableSet hβS (hypMeasure_sub_null _ V hV fun y hy => hy) x

end LowDim

/-! ### Proposition 117(b) for the joint mixes of Theorem 113: `L' ≤ L + ε_n` -/

section Thm113Mask

open Filter Topology

open Mixes.Large

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

lemma lebT_eq_hypMeasure (m : ℕ) (s : E) : lebT m s = hypMeasure (m := m) s := rfl

lemma measurable_mul_exp_of_lipschitzOn {K : Set E} (hK : IsClosed K) {g φ : E → ℝ}
    (hg : Measurable g) (hgK : ∀ y ∉ K, g y = 0) {Lc : ℝ}
    (hφ : ∀ x ∈ K, ∀ y ∈ K, |φ x - φ y| ≤ Lc * dist x y) :
    Measurable fun y => g y * Real.exp (φ y) := by
  classical
  have hc : ContinuousOn φ K :=
    (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal Lc) fun x hx y hy => by
      rw [Real.dist_eq]
      exact (hφ x hx y hy).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal Lc)
        dist_nonneg)).continuousOn
  have hpw : Measurable (K.piecewise φ 0) :=
    hc.measurable_piecewise continuousOn_const hK.measurableSet
  have : (fun y => g y * Real.exp (φ y)) = fun y => g y * Real.exp (K.piecewise φ 0 y) := by
    funext y
    by_cases hy : y ∈ K
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
    · rw [hgK y hy, zero_mul, zero_mul]
  rw [this]
  exact hg.mul (Real.continuous_exp.measurable.comp hpw)

/-- **Proposition 117(b) for the joint mixes of Theorem 113: `L' ≤ L + ε_n`** (`jl:prop:mask`),
given Theorem 113 (`Large.Thm113`). For `(K_j, g_j) ∈ 𝒢_d(A, L, r, R)` and `n = m + 1 ≥ N`, the
conditioned product `β` of Theorem 113 (density with respect to Lebesgue measure on the
hyperplane `∑ yⱼ = s`) satisfies, for all `x, x'` with equal sums and `δ = x' - x`,
`TV(x + Y, x' + Y) ≤ ½ (e^{(L + ε_n) ‖δ‖₁} - 1) + ½ ∑ⱼ (tⱼ(δⱼ) + tⱼ(-δⱼ))`. -/
theorem prop117_thm113 (h113 : Thm113 E) {A L r R : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r)
    (hrR : r ≤ R) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ (K : Fin (m + 1) → Set E) (g : Fin (m + 1) → E → ℝ),
      (∀ j, InG A L r R (K j) (g j)) →
      ∃ φ : Fin (m + 1) → E → ℝ, (∀ j, SupLipLE (K j) (φ j) (ε (m + 1))) ∧
        IsJointMix (fun j => densMeas (g j))
          (condMeas (lebT m (∑ j, meanD (g j))) fun j => tiltD (g j) (φ j)) ∧
        ∀ x x' : Fin (m + 1) → E, ∑ i, x i = ∑ i, x' i →
          tv ((condMeas (lebT m (∑ j, meanD (g j))) fun j => tiltD (g j) (φ j)).map (x + ·))
            ((condMeas (lebT m (∑ j, meanD (g j))) fun j => tiltD (g j) (φ j)).map (x' + ·)) ≤
          (1 / 2) * (Real.exp ((L + ε (m + 1)) * ∑ i, ‖(x' - x) i‖) - 1) +
            (1 / 2) * ∑ j, (tdens (K j) (g j) ((x' - x) j) + tdens (K j) (g j) (-(x' - x) j)) := by
  obtain ⟨N, ε, hε, H⟩ := h113 A L r R hA hL hr hrR
  refine ⟨N, ε, hε, fun m hm K g hG => ?_⟩
  obtain ⟨φ, -, hφ, hmix, -⟩ := H m hm K g hG
  refine ⟨φ, hφ, hmix, fun x x' hsum => ?_⟩
  set s := ∑ j, meanD (g j)
  set lam := lebT m s
  set h : Fin (m + 1) → E → ℝ := fun j => tiltD (g j) (φ j)
  set w0 := condProdJ lam h
  set w := (hyp (n := m + 1) s).indicator w0
  have hKc : ∀ j, IsClosed (K j) := fun j => (hG j).compact.isClosed
  have hKm : ∀ j, MeasurableSet (K j) := fun j => (hKc j).measurableSet
  have hε0 : 0 ≤ ε (m + 1) := by
    obtain ⟨S, Lc, hS, hLc, -, -, hSL⟩ := hφ 0
    linarith
  have hφL : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j, |φ j p - φ j q| ≤ ε (m + 1) * ‖p - q‖ := by
    intro j p hp q hq
    obtain ⟨S, Lc, hS, hLc, -, hL', hSL⟩ := hφ j
    calc |φ j p - φ j q| ≤ Lc * dist p q := hL' p hp q hq
      _ ≤ ε (m + 1) * ‖p - q‖ := by
        rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hg0 : ∀ j z, 0 ≤ g j z := fun j z => by
    by_cases hz : z ∈ K j
    · exact ((hG j).gpos hz).le
    · rw [(hG j).zero z hz]
  have hgL : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j,
      |Real.log (g j p) - Real.log (g j q)| ≤ L * ‖p - q‖ := fun j p hp q hq => by
    rw [← dist_eq_norm]; exact (hG j).lip p hp q hq
  have hgm : ∀ j, Measurable fun y => g j y * Real.exp (φ j y) := fun j => by
    obtain ⟨S, Lc, -, -, -, hL', -⟩ := hφ j
    exact measurable_mul_exp_of_lipschitzOn (hKc j) (hG j).meas (hG j).zero hL'
  have hh0 : ∀ j y, 0 ≤ h j y := fun j y =>
    div_nonneg (mul_nonneg (hg0 j y) (Real.exp_pos _).le)
      (integral_nonneg fun z => mul_nonneg (hg0 j z) (Real.exp_pos _).le)
  have hw0m : Measurable w0 :=
    (Finset.measurable_prod _ fun i _ =>
      ((hgm i).div_const _).comp (measurable_pi_apply i)).div_const
      _
  have hw0nn : ∀ y, 0 ≤ w0 y := fun y =>
    div_nonneg (Finset.prod_nonneg fun i _ => hh0 i _)
      (integral_nonneg fun z => Finset.prod_nonneg fun i _ => hh0 i _)
  have hw : Measurable w := hw0m.indicator (measurableSet_hyp s)
  have hw0 : ∀ y, 0 ≤ w y := fun y => Set.indicator_nonneg (fun y _ => hw0nn y) y
  have hcm : condMeas lam h = dens lam w := by
    rw [condMeas, dens]
    refine withDensity_congr_ae ?_
    have hae : ∀ᵐ y ∂lam, ∑ i, y i = s := hypMeasure_hyp (m := m) s
    refine hae.mono fun y hy => ?_
    simp only [w, Set.indicator_of_mem (show y ∈ hyp s from hy)]
    rfl
  have hP : IsJointMix (fun j => dens volume (g j)) (dens lam w) := hcm ▸ hmix
  have hprob : IsProbabilityMeasure (dens lam w) := hP.1
  have hlin : ∫⁻ y, ENNReal.ofReal (w y) ∂lam = 1 := by
    have := hprob.measure_univ
    rwa [dens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hint : Integrable w lam :=
    (lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable
      (Eventually.of_forall hw0)).1 (by rw [hlin]; exact ENNReal.one_ne_top)
  have h1 : ∫ y, w y ∂lam = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hw0) hw.aestronglyMeasurable,
      hlin, ENNReal.toReal_one]
  have hwT : ∀ y, y ∉ supp (hyp s) K → w y = 0 := by
    intro y hy
    by_cases hys : y ∈ hyp (n := m + 1) s
    · have : ∃ j, y j ∉ K j := by
        by_contra hc
        push Not at hc
        exact hy ⟨hys, Set.mem_iInter.2 fun j => hc j⟩
      obtain ⟨j, hj⟩ := this
      simp only [w, Set.indicator_of_mem hys, w0, condProdJ]
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [h, tiltD, (hG j).zero _ hj]),
        zero_div]
    · exact Set.indicator_of_notMem hys _
  set C : ℝ := (∏ j, ∫ z, g j z * Real.exp (φ j z))⁻¹ * (∫ y, ∏ i, h i (y i) ∂lam)⁻¹
  have hwh : ∀ y ∈ supp (hyp s) K, w y = C * ∏ j, (g j (y j) * Real.exp (φ j (y j))) := by
    intro y hy
    simp only [w, Set.indicator_of_mem hy.1, w0, condProdJ, h, tiltD, C, div_eq_mul_inv,
      Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    ring
  have hC : 0 < C := by
    by_contra hC
    push Not at hC
    have hle : ∀ y, w y ≤ 0 := fun y => by
      by_cases hy : y ∈ supp (hyp s) K
      · rw [hwh y hy]
        exact mul_nonpos_of_nonpos_of_nonneg hC (Finset.prod_nonneg fun j _ =>
          mul_nonneg (hg0 j _) (Real.exp_pos _).le)
      · rw [hwT y hy]
    have := integral_nonpos hle (μ := lam)
    linarith
  rw [hcm]
  exact prop117_b_conditioned hKm g (fun j => (hG j).integrable) hg0 (fun j => (hG j).zero)
    (fun j p hp => (hG j).gpos hp) hL hε0 hgL φ hφL lam hw hw0 hint h1 s hwT hC hwh hP x x'
    hsum (hypMeasure_map_add s _ (sum_sub_eq_zero hsum))

end Thm113Mask

end Mixes
