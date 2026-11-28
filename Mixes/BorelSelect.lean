import Mixes.Markov

/-!
# The Borel selection hypothesis of Theorem 120

`Mixes.thm120_a` and `Mixes.thm120_b` (Theorem 120, `mk:thm:markov`) were proved under the
hypothesis `Mixes.BorelSelection`: a correspondence from a closed set `D` into a compact set of
probability measures, with nonempty values and a closed graph over `D`, has a selection that is a
Markov kernel. Here that hypothesis is proved (a form of the measurable selection theorem of
Kuratowski and Ryll-Nardzewski), for any target space `Y` that is a separable pseudometric Borel
space, and so in particular for `Y = Fin n → E` with `E` a separable normed space.

* `exists_selection`: an abstract selection lemma. If `J : X → Set Z` (with `Z` metric) has
  nonempty closed values in a compact set and `{x | J x ∩ F ≠ ∅}` is measurable for every closed
  `F`, then `J` has a selection `f` with `f ⁻¹' F` measurable for every closed `F`. The proof
  shrinks `J x` by closed balls of radius `1/(m+1)` around the first point of a dense sequence that
  works, and takes the point of the intersection.
* `borelSelection_of_pseudoMetric`: `BorelSelection X Y` for `X` with measurable open sets and `Y`
  a nonempty separable pseudometric Borel space.
* `borelSelection_pi`: the instance `BorelSelection (Fin n → E) (Fin n → E)` used by Theorem 120.
* `thm120_a_uncond`, `thm120_uncond`: Theorem 120 (a) and (b) without the selection hypothesis,
  for a separable normed space `E` (second countable topology), for instance `E = ℝ^d`.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace Mixes.BorelSelect

section Abstract

variable {X Z : Type*} [MeasurableSpace X] [MetricSpace Z]

open Classical in
/-- The first index `k` such that the closed ball of radius `r` about `c k` meets `A`. -/
noncomputable def idx (c : ℕ → Z) (r : ℝ) (A : Set Z) : ℕ :=
  if h : ∃ k, (A ∩ closedBall (c k) r).Nonempty then Nat.find h else 0

/-- One shrinking step: `A` intersected with the first closed ball that meets it. -/
noncomputable def step (c : ℕ → Z) (r : ℝ) (A : Set Z) : Set Z :=
  A ∩ closedBall (c (idx c r A)) r

/-- The shrinking sequence of correspondences. -/
noncomputable def seqS (c : ℕ → Z) (J : X → Set Z) : ℕ → X → Set Z
  | 0 => J
  | m + 1 => fun x => step c (1 / ((m : ℝ) + 1)) (seqS c J m x)

lemma idx_eq_iff {c : ℕ → Z} {r : ℝ} {A : Set Z} (h : ∃ k, (A ∩ closedBall (c k) r).Nonempty)
    (k : ℕ) : idx c r A = k ↔
      (A ∩ closedBall (c k) r).Nonempty ∧ ∀ n < k, ¬ (A ∩ closedBall (c n) r).Nonempty := by
  classical
  simp only [idx, h, ↓reduceDIte]
  exact Nat.find_eq_iff h

lemma step_nonempty {c : ℕ → Z} {r : ℝ} {A : Set Z}
    (h : ∃ k, (A ∩ closedBall (c k) r).Nonempty) : (step c r A).Nonempty :=
  ((idx_eq_iff h _).1 rfl).1

/-- **Measurable selection** (Kuratowski–Ryll-Nardzewski, for compact values). -/
theorem exists_selection {C : Set Z} (hC : IsCompact C) (J : X → Set Z)
    (hne : ∀ x, (J x).Nonempty) (hsub : ∀ x, J x ⊆ C) (hcl : ∀ x, IsClosed (J x))
    (hmeas : ∀ F : Set Z, IsClosed F → MeasurableSet {x | (J x ∩ F).Nonempty}) :
    ∃ f : X → Z, (∀ x, f x ∈ J x) ∧ ∀ F : Set Z, IsClosed F → MeasurableSet (f ⁻¹' F) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x0⟩⟩
  · exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x,
      fun F _ => by simp [Set.eq_empty_of_isEmpty]⟩
  have hCne : C.Nonempty := (hne x0).mono (hsub x0)
  obtain ⟨t, -, htc, hCt⟩ := hC.isSeparable.exists_countable_dense_subset
  have htne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hCt
    exact hCne.ne_empty (Set.subset_empty_iff.1 hCt)
  obtain ⟨c, rfl⟩ := htc.exists_eq_range htne
  have hdense : ∀ z ∈ C, ∀ ε > 0, ∃ k, dist z (c k) < ε := by
    intro z hz ε hε
    obtain ⟨y, hy, hzy⟩ := Metric.mem_closure_iff.1 (hCt hz) ε hε
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, hzy⟩
  set r : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hr_def
  have hr : ∀ m, 0 < r m := fun m => by positivity
  set S := seqS c J with hS_def
  have hSs : ∀ m x, S (m + 1) x = step c (r m) (S m x) := fun m x => rfl
  have hmono : ∀ m x, S (m + 1) x ⊆ S m x := fun m x => by
    rw [hSs]; exact Set.inter_subset_left
  have hsubJ : ∀ m x, S m x ⊆ J x := by
    intro m
    induction m with
    | zero => intro x; exact subset_rfl
    | succ m ih => intro x; exact (hmono m x).trans (ih x)
  have hclS : ∀ m x, IsClosed (S m x) := by
    intro m
    induction m with
    | zero => exact hcl
    | succ m ih => intro x; rw [hSs]; exact (ih x).inter isClosed_closedBall
  have hex : ∀ m x, (S m x).Nonempty → ∃ k, (S m x ∩ closedBall (c k) (r m)).Nonempty := by
    rintro m x ⟨z, hz⟩
    obtain ⟨k, hk⟩ := hdense z (hsub x (hsubJ m x hz)) (r m) (hr m)
    exact ⟨k, z, hz, Metric.mem_closedBall.2 hk.le⟩
  have hneS : ∀ m x, (S m x).Nonempty := by
    intro m
    induction m with
    | zero => exact hne
    | succ m ih => intro x; rw [hSs]; exact step_nonempty (hex m x (ih x))
  have hball : ∀ m x, S (m + 1) x ⊆ closedBall (c (idx c (r m) (S m x))) (r m) := fun m x => by
    rw [hSs]; exact Set.inter_subset_right
  have hmS : ∀ m, ∀ F : Set Z, IsClosed F → MeasurableSet {x | (S m x ∩ F).Nonempty} := by
    intro m
    induction m with
    | zero => exact hmeas
    | succ m ih =>
      intro F hF
      have hidx : ∀ k, MeasurableSet {x | idx c (r m) (S m x) = k} := by
        intro k
        have : {x | idx c (r m) (S m x) = k} =
            {x | (S m x ∩ closedBall (c k) (r m)).Nonempty} ∩
              ⋂ n ∈ Finset.range k, {x | (S m x ∩ closedBall (c n) (r m)).Nonempty}ᶜ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
            Finset.mem_range]
          exact idx_eq_iff (hex m x (hneS m x)) k
        rw [this]
        exact (ih _ isClosed_closedBall).inter
          (Finset.measurableSet_biInter _ fun n _ => (ih _ isClosed_closedBall).compl)
      have : {x | (S (m + 1) x ∩ F).Nonempty} = ⋃ k, {x | idx c (r m) (S m x) = k} ∩
          {x | (S m x ∩ (closedBall (c k) (r m) ∩ F)).Nonempty} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, hSs, step]
        constructor
        · intro h; exact ⟨_, rfl, by rwa [Set.inter_assoc] at h⟩
        · rintro ⟨k, rfl, h⟩; rwa [Set.inter_assoc]
      rw [this]
      exact MeasurableSet.iUnion fun k => (hidx k).inter (ih _ (isClosed_closedBall.inter hF))
  have hcpt : ∀ m x, IsCompact (S m x) := fun m x =>
    hC.of_isClosed_subset (hclS m x) ((hsubJ m x).trans (hsub x))
  have hcantor : ∀ x (F : Set Z), IsClosed F → (∀ m, (S m x ∩ F).Nonempty) →
      (⋂ m, (S m x ∩ F)).Nonempty := by
    intro x F hF h
    exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun m => S m x ∩ F)
      (fun m => Set.inter_subset_inter_left _ (hmono m x)) h ((hcpt 0 x).inter_right hF)
      (fun m => (hclS m x).inter hF)
  choose f hf using fun x => hcantor x univ isClosed_univ (fun m => by simpa using hneS m x)
  have hfS : ∀ m x, f x ∈ S m x := fun m x => (Set.mem_iInter.1 (hf x) m).1
  have huniq : ∀ x z, (∀ m, z ∈ S m x) → z = f x := by
    intro x z hz
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
    have h1 := hball m x (hz (m + 1))
    have h2 := hball m x (hfS (m + 1) x)
    rw [Metric.mem_closedBall] at h1 h2
    calc dist z (f x) ≤ dist z (c (idx c (r m) (S m x))) + dist (f x) (c (idx c (r m) (S m x))) :=
          dist_triangle_right _ _ _
      _ ≤ r m + r m := add_le_add h1 h2
      _ ≤ ε := by simp only [hr_def]; linarith
  refine ⟨f, fun x => hsubJ 0 x (hfS 0 x), fun F hF => ?_⟩
  have : f ⁻¹' F = ⋂ m, {x | (S m x ∩ F).Nonempty} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hx m; exact ⟨f x, hfS m x, hx⟩
    · intro h
      obtain ⟨z, hz⟩ := hcantor x F hF h
      have hz' : ∀ m, z ∈ S m x ∩ F := Set.mem_iInter.1 hz
      rw [← huniq x z fun m => (hz' m).1]
      exact (hz' 0).2
  rw [this]
  exact MeasurableSet.iInter fun m => hmS m F hF

end Abstract


section Kernel

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- The measure of a closed set is the infimum of the integrals of its thickened indicators. -/
lemma measure_closed_eq_iInf (μ : ProbabilityMeasure Y) {A : Set Y} (hA : IsClosed A) :
    (μ : Measure Y) A = ⨅ m : ℕ, ∫⁻ ω, (thickenedIndicator (Nat.one_div_pos_of_nat (n := m)) A ω
      : ℝ≥0∞) ∂(μ : Measure Y) := by
  refine le_antisymm (le_iInf fun m => ?_) ?_
  · calc (μ : Measure Y) A = ∫⁻ ω, A.indicator 1 ω ∂(μ : Measure Y) :=
          (lintegral_indicator_one hA.measurableSet).symm
      _ ≤ _ := lintegral_mono fun ω => by
          have := indicator_le_thickenedIndicator (Nat.one_div_pos_of_nat (n := m)) A ω
          by_cases hω : ω ∈ A
          · simp only [Set.indicator_of_mem hω, Pi.one_apply] at this ⊢
            exact_mod_cast this
          · simp [Set.indicator_of_notMem hω]
  · exact ge_of_tendsto' (tendsto_lintegral_thickenedIndicator_of_isClosed (μ : Measure Y) hA
      (fun m => Nat.one_div_pos_of_nat (n := m)) tendsto_one_div_add_atTop_nhds_zero_nat)
      fun m => iInf_le _ m

/-- For a closed set `A`, the sublevel sets `{μ | μ A < t}` are open in the weak topology. -/
lemma isOpen_measure_lt {A : Set Y} (hA : IsClosed A) (t : ℝ≥0∞) :
    IsOpen {μ : ProbabilityMeasure Y | (μ : Measure Y) A < t} := by
  have : {μ : ProbabilityMeasure Y | (μ : Measure Y) A < t} = ⋃ m : ℕ,
      (fun μ : ProbabilityMeasure Y => ∫⁻ ω, (thickenedIndicator
        (Nat.one_div_pos_of_nat (n := m)) A ω : ℝ≥0∞) ∂(μ : Measure Y)) ⁻¹' Set.Iio t := by
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_Iio,
      measure_closed_eq_iInf μ hA, iInf_lt_iff]
  rw [this]
  exact isOpen_iUnion fun m => isOpen_Iio.preimage
    (ProbabilityMeasure.continuous_iff_forall_continuous_lintegral.1 continuous_id _)

variable {X : Type*} [MeasurableSpace X] [BorelSpace Y]

/-- A map into probability measures whose preimages of weakly closed sets are measurable defines
a Markov kernel. -/
theorem exists_kernel_of_closed_measurable (f : X → ProbabilityMeasure Y)
    (hf : ∀ F : Set (ProbabilityMeasure Y), IsClosed F → MeasurableSet (f ⁻¹' F)) :
    ∃ P : Kernel X Y, ∃ _ : IsMarkovKernel P, ∀ x, kPM P x = f x := by
  have hm : Measurable fun x => (f x : Measure Y) := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (S := {s | IsClosed s})
      (by rw [BorelSpace.measurable_eq (α := Y), borel_eq_generateFrom_isClosed])
      isPiSystem_isClosed fun A hA => ?_
    refine measurable_of_Iio fun t => ?_
    have := (hf _ (isOpen_measure_lt hA t).isClosed_compl).compl
    rwa [← Set.preimage_compl, compl_compl] at this
  exact ⟨⟨fun x => (f x : Measure Y), hm⟩, ⟨fun x => (f x).prop⟩, fun x => rfl⟩

end Kernel


section Selection

/-- **`BorelSelection X Y`** for a nonempty separable pseudometric Borel space `Y` (and any `X`
whose open sets are measurable). -/
theorem borelSelection_of_pseudoMetric (X Y : Type*) [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [PseudoMetricSpace Y] [SeparableSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [Nonempty Y] : BorelSelection X Y := by
  intro D C J hD hC hJ hG
  set G := {p : X × ProbabilityMeasure Y | p.1 ∈ D ∧ p.2 ∈ J p.1}
  have hJcl : ∀ x ∈ D, IsClosed (J x) := by
    intro x hx
    have : J x = (fun μ => (x, μ)) ⁻¹' G := by
      ext μ; simp [G, hx]
    rw [this]
    exact hG.preimage (Continuous.prodMk_right x)
  have hproj : ∀ F : Set (ProbabilityMeasure Y), IsClosed F →
      IsClosed {x | x ∈ D ∧ (J x ∩ F).Nonempty} := by
    intro F hF
    have hK : IsCompact (C ∩ F) := hC.inter_right hF
    have : CompactSpace (C ∩ F : Set (ProbabilityMeasure Y)) := isCompact_iff_compactSpace.1 hK
    let g : X × (C ∩ F : Set (ProbabilityMeasure Y)) → X × ProbabilityMeasure Y :=
      fun p => (p.1, p.2.1)
    have hg : Continuous g := continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)
    have hT := isClosedMap_fst_of_compactSpace _ (hG.preimage hg)
    convert hT using 1
    ext x
    constructor
    · rintro ⟨hx, μ, hμJ, hμF⟩
      exact ⟨(x, ⟨μ, (hJ x hx).2 hμJ, hμF⟩), ⟨hx, hμJ⟩, rfl⟩
    · rintro ⟨⟨x', μ, hμC, hμF⟩, ⟨hx, hμJ⟩, rfl⟩
      exact ⟨hx, μ, hμJ, hμF⟩
  obtain ⟨y0⟩ := ‹Nonempty Y›
  let μ0 : ProbabilityMeasure Y := ⟨Measure.dirac y0, inferInstance⟩
  classical
  let J' : X → Set (ProbabilityMeasure Y) := fun x => if x ∈ D then J x else {μ0}
  have hmeas : ∀ F : Set (ProbabilityMeasure Y), IsClosed F →
      MeasurableSet {x | (J' x ∩ F).Nonempty} := by
    intro F hF
    have : {x | (J' x ∩ F).Nonempty} = {x | x ∈ D ∧ (J x ∩ F).Nonempty} ∪ (Dᶜ ∩ {_x | μ0 ∈ F}) := by
      ext x
      by_cases hx : x ∈ D
      · simp [J', hx]
      · simp [J', hx]
    rw [this]
    exact (hproj F hF).measurableSet.union (hD.measurableSet.compl.inter (MeasurableSet.const _))
  let := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure Y)
  obtain ⟨f, hfJ, hfm⟩ := exists_selection (hC.insert μ0) J'
    (fun x => by by_cases hx : x ∈ D <;> simp [J', hx, (hJ x _).1])
    (fun x => by
      by_cases hx : x ∈ D
      · simp only [J', hx, ite_true]; exact (hJ x hx).2.trans (Set.subset_insert _ _)
      · simp [J', hx])
    (fun x => by
      by_cases hx : x ∈ D
      · simp only [J', hx, ite_true]; exact hJcl x hx
      · simp only [J', hx, ite_false]; exact isClosed_singleton)
    hmeas
  obtain ⟨P, hP, hPf⟩ := exists_kernel_of_closed_measurable f hfm
  refine ⟨P, hP, fun x hx => ?_⟩
  rw [hPf]
  have := hfJ x
  simpa [J', hx] using this

end Selection


section Thm120

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] {n : ℕ}

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The selection hypothesis of Theorem 120 holds for `Fin n → E`, `E` a separable normed space. -/
theorem borelSelection_pi : BorelSelection (Fin n → E) (Fin n → E) :=
  borelSelection_of_pseudoMetric _ _

/-- **Theorem 120(a)** (`mk:thm:markov`), unconditional for a separable normed space `E` (for
instance `ℝ^d`): `Mixes.thm120_a` with the selection hypothesis discharged by
`borelSelection_pi`. -/
theorem thm120_a_uncond {K : Fin n → Set E}
    (hK : ∀ j, IsCompact (K j)) {s : E} (k : Fin n → Kernel E E) [∀ j, IsMarkovKernel (k j)]
    (hkK : ∀ j, ∀ y ∈ K j, k j y (K j)ᶜ = 0) (hfel : ∀ j, ContinuousOn (kPM (k j)) (K j))
    (Γ : E →L[ℝ] E) (c : Fin n → E) (hmean : ∀ j, ∀ y ∈ K j, ∫ z, z ∂(k j y) = Γ y + c j)
    (hs : Γ s + ∑ j, c j = s)
    (hmix : ∀ x ∈ tset K s, JointlyMixable fun j => k j (x j)) :
    ∃ P : Kernel (Fin n → E) (Fin n → E), IsMarkovKernel P ∧ IsMarkovStep k (tset K s) P :=
  thm120_a borelSelection_pi hK k hkK hfel Γ c hmean hs hmix

/-- **Theorem 120(b)** (`mk:thm:markov`), unconditional for a separable normed space `E` (for
instance `ℝ^d`): `Mixes.thm120_b` with the selection hypothesis discharged by
`borelSelection_pi`. If each `kⱼ` has exactly one invariant probability measure `gⱼ` on `Kⱼ`,
then there is a Markov joint mix on `𝒯` in which every coordinate is stationary with law `gⱼ`. -/
theorem thm120_uncond {K : Fin n → Set E}
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
        ∀ t j, (kpow P t ∘ₘ π).map (fun y => y j) = g j :=
  thm120_b borelSelection_pi hK hT k hkK hfel Γ c hmean hs hmix g huniq

end Thm120

end Mixes.BorelSelect
