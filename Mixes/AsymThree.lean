import Mathlib
import Mixes.Defs
import Mixes.ConeMix
import Mixes.Joint
import Mixes.TwoStep
import Mixes.Pieces

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Mixes.AsymThree

/-- General gluing: two probability measures that agree on a common image are coupled. -/
theorem glue {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [MeasurableSingletonClass X] [MeasurableEq X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → X} (hf : Measurable f)
    (P : Measure Y) [IsProbabilityMeasure P] {g : Y → X} (hg : Measurable g)
    (h : μ.map f = P.map g) :
    ∃ Q : Measure (Ω × Y), IsProbabilityMeasure Q ∧ Q.map Prod.fst = μ ∧ Q.map Prod.snd = P ∧
      ∀ᵐ q ∂Q, g q.2 = f q.1 := by
  set K : Kernel X Y := condDistrib id g P
  set Q : Measure (Ω × Y) := μ ⊗ₘ (K.comap f hf)
  have hQ : Q.map (Prod.map f id) = (P.map g) ⊗ₘ K := by
    ext s hs
    rw [Measure.map_apply (hf.prodMap measurable_id) hs, Measure.compProd_apply
      ((hf.prodMap measurable_id) hs), Measure.compProd_apply hs, ← h,
      lintegral_map (K.measurable_kernel_prodMk_left hs) hf]
    rfl
  have hK : (P.map g) ⊗ₘ K = P.map (fun y => (g y, id y)) :=
    compProd_map_condDistrib hg.aemeasurable aemeasurable_id
  refine ⟨Q, by infer_instance, Measure.fst_compProd _ _, ?_, ?_⟩
  · have : Q.map Prod.snd = ((P.map g) ⊗ₘ K).map Prod.snd := by
      rw [← hQ, Measure.map_map measurable_snd (hf.prodMap measurable_id)]; rfl
    rw [this, hK, Measure.map_map measurable_snd (hg.prodMk measurable_id)]
    exact Measure.map_id
  · have hmeas : MeasurableSet {p : X × Y | g p.2 = p.1} :=
      measurableSet_eq_fun (hg.comp measurable_snd) measurable_fst
    have h1 : ((P.map g) ⊗ₘ K) {p : X × Y | g p.2 = p.1}ᶜ = 0 := by
      rw [hK, Measure.map_apply (hg.prodMk measurable_id) hmeas.compl]
      simp
    have h2 : Q.map (Prod.map f id) {p : X × Y | g p.2 = p.1}ᶜ = 0 := by rw [hQ]; exact h1
    rw [Measure.map_apply (hf.prodMap measurable_id) hmeas.compl] at h2
    exact measure_mono_null (fun q hq => by simpa using hq) h2


/-- The aggregation set `𝒜(A)` of a finite family of distributions on the line: the laws of
`∑ i, X i` over all random vectors with `X i ∼ A i`, written with measures on tuples. -/
def aggSet {ι : Type*} [Fintype ι] (A : ι → Measure ℝ) : Set (Measure ℝ) :=
  {ν | ∃ P : Measure (ι → ℝ), IsProbabilityMeasure P ∧ (∀ i, P.map (fun x => x i) = A i) ∧
    P.map (fun x => ∑ i, x i) = ν}

lemma measurable_sum_coord {ι : Type*} [Fintype ι] : Measurable (fun x : ι → ℝ => ∑ i, x i) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

lemma aggSet_isProb {ι : Type*} [Fintype ι] {A : ι → Measure ℝ} {ν : Measure ℝ}
    (h : ν ∈ aggSet A) : IsProbabilityMeasure ν := by
  obtain ⟨P, hP, -, rfl⟩ := h
  exact inferInstance

/-- Reindexing. -/
lemma aggSet_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) {A : ι → Measure ℝ}
    {ν : Measure ℝ} (h : ν ∈ aggSet A) : ν ∈ aggSet (fun k => A (e.symm k)) := by
  obtain ⟨P, hP, hm, rfl⟩ := h
  have hme : Measurable (fun (x : ι → ℝ) (k : κ) => x (e.symm k)) :=
    measurable_pi_iff.mpr (fun k => measurable_pi_apply _)
  refine ⟨P.map (fun x k => x (e.symm k)), inferInstance, ?_, ?_⟩
  · intro k
    rw [Measure.map_map (measurable_pi_apply k) hme]
    exact hm (e.symm k)
  · rw [Measure.map_map measurable_sum_coord hme]
    congr 1
    funext x
    exact Equiv.sum_comp e.symm x

lemma aggSet_congr {ι : Type*} [Fintype ι] {A B : ι → Measure ℝ} (hAB : A = B) {ν : Measure ℝ}
    (h : ν ∈ aggSet A) : ν ∈ aggSet B := hAB ▸ h

/-- A point mass in the aggregation set gives a joint mix. -/
lemma jointlyMixable_of_dirac {n : ℕ} {A : Fin n → Measure ℝ} {s : ℝ}
    (h : Measure.dirac s ∈ aggSet A) : JointlyMixable A := by
  obtain ⟨P, hP, hm, hs⟩ := h
  refine ⟨P, hP, ⟨s, ?_⟩, hm⟩
  have h1 : P.map (fun x => ∑ i, x i) {s}ᶜ = 0 := by rw [hs]; simp
  rw [Measure.map_apply measurable_sum_coord (measurableSet_singleton s).compl] at h1
  exact measure_mono_null (fun x hx => by simpa using hx) h1

/-- Absorption: if the deviation `Z - ∑ Y` of a target `Z` from the sum of a coupled family `Y`
lies in the aggregation set of `B`, then the law of `Z` lies in that of `B` followed by `A`. -/
theorem absorb {Ω ιA ιB : Type*} [MeasurableSpace Ω] [Fintype ιA] [Fintype ιB]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ιA → ℝ} (hY : Measurable Y)
    {Z : Ω → ℝ} (hZ : Measurable Z) {A : ιA → Measure ℝ} {B : ιB → Measure ℝ}
    (hA : ∀ i, μ.map (fun ω => Y ω i) = A i)
    (hB : μ.map (fun ω => Z ω - ∑ i, Y ω i) ∈ aggSet B) :
    μ.map Z ∈ aggSet (Sum.elim B A) := by
  obtain ⟨PB, hPB, hmB, hsB⟩ := hB
  have hf : Measurable (fun ω => Z ω - ∑ i, Y ω i) := hZ.sub (measurable_sum_coord.comp hY)
  obtain ⟨Q, hQ, hQ1, hQ2, hQs⟩ := glue μ hf PB measurable_sum_coord hsB.symm
  have hel : Measurable (fun q : Ω × (ιB → ℝ) => (Sum.elim q.2 (Y q.1) : ιB ⊕ ιA → ℝ)) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    cases j with
    | inl i => exact (measurable_pi_apply i).comp measurable_snd
    | inr i => exact (measurable_pi_apply i).comp (hY.comp measurable_fst)
  refine ⟨Q.map (fun q => Sum.elim q.2 (Y q.1)), inferInstance,
    ?_, ?_⟩
  · intro j
    rw [Measure.map_map (measurable_pi_apply j) hel]
    cases j with
    | inl i =>
      rw [Sum.elim_inl, ← hmB i, ← hQ2, Measure.map_map (measurable_pi_apply i) measurable_snd]; rfl
    | inr i =>
      rw [Sum.elim_inr, ← hA i, ← hQ1, Measure.map_map (show Measurable (fun ω => Y ω i) from (measurable_pi_apply i).comp hY) measurable_fst]; rfl
  · rw [Measure.map_map measurable_sum_coord hel, ← hQ1,
      Measure.map_map hZ measurable_fst]
    apply Measure.map_congr
    filter_upwards [hQs] with q hq
    simp only [Function.comp_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hq]; ring

/-- Splitting a target into two summands that are functions of it. -/
theorem split {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {A : ιA → Measure ℝ} {B : ιB → Measure ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hA : ν.map f ∈ aggSet A) (hB : ν.map (fun x => x - f x) ∈ aggSet B) :
    ν ∈ aggSet (Sum.elim B A) := by
  obtain ⟨PA, hPA, hmA, hsA⟩ := hA
  obtain ⟨Q, hQ, hQ1, hQ2, hQs⟩ := glue ν hf PA measurable_sum_coord hsA.symm
  have key := absorb Q (Y := fun q => q.2) (Z := fun q => q.1) measurable_snd measurable_fst
    (A := A) (B := B) (fun i => by rw [← hmA i, ← hQ2, Measure.map_map (measurable_pi_apply i) measurable_snd]; rfl) ?_
  · rwa [hQ1] at key
  · have : Q.map (fun q : ℝ × (ιA → ℝ) => q.1 - ∑ i, q.2 i) = Q.map (fun q => q.1 - f q.1) := by
      apply Measure.map_congr
      filter_upwards [hQs] with q hq
      simp [hq]
    have e : (fun q : ℝ × (ιA → ℝ) => q.1 - f q.1) = (fun x => x - f x) ∘ Prod.fst := rfl
    rw [this, e, ← Measure.map_map (show Measurable (fun x : ℝ => x - f x) from measurable_id.sub hf) measurable_fst, hQ1]
    exact hB

open Set

lemma aggSet_reindex' {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) {A : ι → Measure ℝ}
    {B : κ → Measure ℝ} (hBA : ∀ i, B (e i) = A i) {ν : Measure ℝ} (h : ν ∈ aggSet A) :
    ν ∈ aggSet B := by
  have := aggSet_reindex e h
  convert this using 2
  funext k
  rw [← hBA, e.apply_symm_apply]

/-! ### Supports and means -/

lemma ae_mem_of_null {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {s : Set Ω}
    (h : ν sᶜ = 0) : ∀ᵐ x ∂ν, x ∈ s := ae_iff.mpr h

lemma map_null_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Measurable f) {s : Set ℝ} (hs : MeasurableSet s) (h : ∀ᵐ ω ∂μ, f ω ∈ s) :
    (μ.map f) sᶜ = 0 := by
  rw [Measure.map_apply hf hs.compl]; exact ae_iff.mp h

lemma integrable_of_ae_Icc {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {l u : ℝ} (h : ∀ᵐ ω ∂μ, f ω ∈ Icc l u) :
    Integrable f μ :=
  Integrable.of_bound hf (max |l| |u|) (h.mono fun x hx => by
    rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs hx.1 hx.2)

lemma integrable_id_of_null {ν : Measure ℝ} [IsFiniteMeasure ν] {l u : ℝ}
    (h : ν (Icc l u)ᶜ = 0) : Integrable (fun x => x) ν :=
  integrable_of_ae_Icc aestronglyMeasurable_id (ae_mem_of_null h)

lemma integral_mem_Icc_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {l u : ℝ}
    (h : ∀ᵐ ω ∂μ, f ω ∈ Icc l u) : ∫ ω, f ω ∂μ ∈ Icc l u := by
  have hi := integrable_of_ae_Icc hf h
  constructor
  · have := integral_mono_ae (integrable_const l) hi (h.mono fun x hx => hx.1)
    simpa using this
  · have := integral_mono_ae hi (integrable_const u) (h.mono fun x hx => hx.2)
    simpa using this

lemma eq_dirac_of_null {ν : Measure ℝ} [IsProbabilityMeasure ν] {a : ℝ} (h : ν {a}ᶜ = 0) :
    ν = Measure.dirac a := by
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
    have h1 : ν sᶜ = 0 := measure_mono_null (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; rintro rfl; exact hx ha) h
    rw [prob_compl_eq_zero_iff hs] at h1
    simpa using h1
  · rw [Set.indicator_of_notMem ha]
    exact measure_mono_null (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; rintro rfl; exact ha hx) h

lemma integral_id_map {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Measurable f) : ∫ x, x ∂(μ.map f) = ∫ ω, f ω ∂μ :=
  integral_map (f := fun x : ℝ => x) hf.aemeasurable aestronglyMeasurable_id

/-! ### Windows -/

/-- `Win B a w`: every probability measure with mean `a` carried by `[a - w, a + w]` lies in the
aggregation set of `B`. -/
def Win {ι : Type*} [Fintype ι] (B : ι → Measure ℝ) (a w : ℝ) : Prop :=
  ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Icc (a - w) (a + w))ᶜ = 0 → ∫ x, x ∂ν = a →
    ν ∈ aggSet B

lemma win_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) {A : ι → Measure ℝ}
    {B : κ → Measure ℝ} (hBA : ∀ i, B (e i) = A i) {a w : ℝ} (hA : Win A a w) : Win B a w :=
  fun ν hν h1 h2 => aggSet_reindex' e hBA (hA ν hν h1 h2)

lemma win_empty {ι : Type*} [Fintype ι] [IsEmpty ι] (B : ι → Measure ℝ) : Win B 0 0 := by
  intro ν hν h1 _
  have : ν = Measure.dirac 0 := eq_dirac_of_null (by simpa using h1)
  subst this
  refine ⟨Measure.dirac (fun _ => 0), inferInstance, fun i => isEmptyElim i, ?_⟩
  rw [Measure.map_dirac' measurable_sum_coord]
  simp

lemma integral_affine {ν : Measure ℝ} [IsProbabilityMeasure ν] (hi : Integrable (fun x => x) ν)
    (p t : ℝ) : ∫ x, p + t * x ∂ν = p + t * ∫ x, x ∂ν := by
  rw [integral_add (integrable_const p) (hi.const_mul t), integral_const_mul]
  simp

theorem win_sum {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] {A : ιA → Measure ℝ}
    {B : ιB → Measure ℝ} {a b wA wB : ℝ} (hwA : 0 ≤ wA) (hwB : 0 ≤ wB) (hA : Win A a wA)
    (hB : Win B b wB) : Win (Sum.elim B A) (a + b) (wA + wB) := by
  intro ν hν hsupp hmean
  set θ := wA / (wA + wB) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg hwA (add_nonneg hwA hwB)
  have hθw : θ * (wA + wB) = wA := by
    rcases eq_or_lt_of_le (add_nonneg hwA hwB) with h | h
    · have : wA = 0 := by linarith
      rw [← h, this]; simp
    · rw [hθdef]; field_simp
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by linarith) (add_nonneg hwA hwB)
  have hae := ae_mem_of_null hsupp
  have hint := integrable_id_of_null hsupp
  have hf : Measurable (fun x : ℝ => (a - θ * (a + b)) + θ * x) := by fun_prop
  apply split ν hf
  · apply hA _ inferInstance
    · apply map_null_of_ae hf measurableSet_Icc
      filter_upwards [hae] with x hx
      have h1 : θ * (x - (a + b)) ≤ θ * (wA + wB) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) hθ0
      have h2 : θ * (-(wA + wB)) ≤ θ * (x - (a + b)) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.1]) hθ0
      constructor <;> nlinarith
    · rw [integral_id_map hf, integral_affine hint, hmean]
      ring
  · have hg : Measurable (fun x : ℝ => (b - (1 - θ) * (a + b)) + (1 - θ) * x) := by fun_prop
    have heq : (fun x : ℝ => x - ((a - θ * (a + b)) + θ * x)) =
        (fun x : ℝ => (b - (1 - θ) * (a + b)) + (1 - θ) * x) := by funext x; ring
    rw [heq]
    apply hB _ inferInstance
    · apply map_null_of_ae hg measurableSet_Icc
      filter_upwards [hae] with x hx
      have h1 : (1 - θ) * (x - (a + b)) ≤ (1 - θ) * (wA + wB) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by linarith)
      have h2 : (1 - θ) * (-(wA + wB)) ≤ (1 - θ) * (x - (a + b)) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by linarith)
      constructor <;> nlinarith
    · rw [integral_id_map hg, integral_affine hint, hmean]
      ring

/-- The equivalence `(Σ j : Fin K, κ j.succ) ⊕ κ 0 ≃ Σ k : Fin (K+1), κ k`. -/
def sigmaSuccEquiv {K : ℕ} (κ : Fin (K + 1) → Type) :
    (Σ j : Fin K, κ j.succ) ⊕ κ 0 ≃ Σ k : Fin (K + 1), κ k where
  toFun := Sum.elim (fun p => ⟨p.1.succ, p.2⟩) (fun x => ⟨0, x⟩)
  invFun := fun p => Fin.cases (motive := fun k => κ k → (Σ j : Fin K, κ j.succ) ⊕ κ 0)
    (fun x => Sum.inr x) (fun j x => Sum.inl ⟨j, x⟩) p.1 p.2
  left_inv := by rintro (⟨j, x⟩ | x) <;> rfl
  right_inv := by
    rintro ⟨k, x⟩
    cases k using Fin.cases <;> rfl

theorem win_sigma : ∀ (K : ℕ) (κ : Fin K → Type) [∀ k, Fintype (κ k)]
    (B : ∀ k, κ k → Measure ℝ) (a w : Fin K → ℝ), (∀ k, 0 ≤ w k) →
    (∀ k, Win (B k) (a k) (w k)) →
    Win (fun p : Σ k, κ k => B p.1 p.2) (∑ k, a k) (∑ k, w k)
  | 0, κ, _, B, a, w, _, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact win_empty _
  | K + 1, κ, _, B, a, w, hw, hB => by
    have ih := win_sigma K (fun j => κ j.succ) (fun j => B j.succ) (fun j => a j.succ)
      (fun j => w j.succ) (fun j => hw _) (fun j => hB _)
    have h2 := win_sum (hw 0) (Finset.sum_nonneg fun j _ => hw j.succ) (hB 0) ih
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact win_reindex (sigmaSuccEquiv κ) (by rintro (⟨j, x⟩ | x) <;> rfl) h2

/-! ### Random order within blocks -/

open scoped ENNReal

lemma map_finset_sum {α γ δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {f : α → δ}
    (hf : Measurable f) (s : Finset γ) (μ : γ → Measure α) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

section shuffle

variable {β : Type} [Fintype β] [DecidableEq β] (N : β → ℕ) [∀ b, NeZero (N b)]

/-- Shift every block `b` cyclically by `g b`. -/
def shiftMap {ιB : Type*} (g : ∀ b, Fin (N b)) (x : (Σ b, Fin (N b)) ⊕ ιB → ℝ) :
    (Σ b, Fin (N b)) ⊕ ιB → ℝ :=
  Sum.elim (fun p => x (Sum.inl ⟨p.1, p.2 + g p.1⟩)) (fun i => x (Sum.inr i))

omit [Fintype β] [DecidableEq β] [∀ b, NeZero (N b)] in
lemma measurable_shiftMap {ιB : Type*} (g : ∀ b, Fin (N b)) :
    Measurable (shiftMap N (ιB := ιB) g) :=
  measurable_pi_iff.mpr (by rintro (p | i) <;> exact measurable_pi_apply _)

omit [DecidableEq β] in
lemma sum_shiftMap {ιB : Type*} [Fintype ιB] (g : ∀ b, Fin (N b))
    (x : (Σ b, Fin (N b)) ⊕ ιB → ℝ) : ∑ j, shiftMap N g x j = ∑ j, x j := by
  simp only [Fintype.sum_sum_type, shiftMap, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sigma]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Fintype.sum_equiv (Equiv.addRight (g b)) _ _ (fun j => rfl)

lemma sum_shift_count {M : Type*} [AddCommMonoid M] (b : β) (j : Fin (N b))
    (φ : Fin (N b) → M) :
    N b • ∑ g : (∀ b, Fin (N b)), φ (j + g b) =
      Fintype.card (∀ b, Fin (N b)) • ∑ i, φ i := by
  have hinv : ∀ c : Fin (N b), ∑ g : (∀ b, Fin (N b)), φ (j + g b) =
      ∑ g : (∀ b, Fin (N b)), φ (j + c + g b) := by
    intro c
    refine (Fintype.sum_equiv (Equiv.addRight (Pi.single b c)) _ _ (fun g => ?_)).symm
    simp only [Equiv.coe_addRight, Pi.add_apply, Pi.single_eq_same]
    congr 1; abel
  calc N b • ∑ g : (∀ b, Fin (N b)), φ (j + g b)
      = ∑ c : Fin (N b), ∑ g : (∀ b, Fin (N b)), φ (j + g b) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = ∑ c : Fin (N b), ∑ g : (∀ b, Fin (N b)), φ (j + c + g b) :=
        Finset.sum_congr rfl (fun c _ => hinv c)
    _ = ∑ g : (∀ b, Fin (N b)), ∑ c : Fin (N b), φ (j + c + g b) := Finset.sum_comm
    _ = ∑ g : (∀ b, Fin (N b)), ∑ i, φ i := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        exact Fintype.sum_equiv ((Equiv.addRight (g b)).trans (Equiv.addLeft j)) _ _
          (fun c => by simp [add_assoc])
    _ = Fintype.card (∀ b, Fin (N b)) • ∑ i, φ i := by
        simp [Finset.sum_const, Finset.card_univ]

/-- Arranging the variables of every block in a uniformly random (cyclic) order replaces their
distributions by the average distribution of the block. -/
theorem aggSet_shuffle {ιB : Type*} [Fintype ιB] (A : (Σ b, Fin (N b)) → Measure ℝ)
    (B : ιB → Measure ℝ) {ν : Measure ℝ} (h : ν ∈ aggSet (Sum.elim A B)) :
    ν ∈ aggSet (Sum.elim (fun p : Σ b, Fin (N b) => ((N p.1 : ℝ≥0∞)⁻¹) • ∑ i, A ⟨p.1, i⟩) B) := by
  obtain ⟨P, hP, hm, rfl⟩ := h
  set c := Fintype.card (∀ b, Fin (N b)) with hc
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    have : 0 < c := Fintype.card_pos
    exact_mod_cast this.ne'
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
  have hcc : ∀ μ : Measure ℝ, (c : ℝ≥0∞)⁻¹ • (c • μ) = μ := by
    intro μ
    rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
  refine ⟨(c : ℝ≥0∞)⁻¹ • ∑ g : (∀ b, Fin (N b)), P.map (shiftMap N g), ?_, ?_, ?_⟩
  · constructor
    simp [← hc]
    exact ENNReal.inv_mul_cancel hc0 hcT
  · intro j
    rw [Measure.map_smul _ (measurable_pi_apply j).aemeasurable, map_finset_sum (measurable_pi_apply j)]
    simp only [Measure.map_map (measurable_pi_apply j) (measurable_shiftMap N _)]
    cases j with
    | inr i =>
      have : ∀ g : (∀ b, Fin (N b)),
          P.map ((fun x => x (Sum.inr i)) ∘ shiftMap N g) = B i := fun g => hm (Sum.inr i)
      simp only [this, Finset.sum_const, Finset.card_univ, ← hc, Sum.elim_inr]
      exact hcc _
    | inl p =>
      obtain ⟨b, k⟩ := p
      have : ∀ g : (∀ b, Fin (N b)),
          P.map ((fun x => x (Sum.inl ⟨b, k⟩)) ∘ shiftMap N g) = A ⟨b, k + g b⟩ :=
        fun g => hm (Sum.inl ⟨b, k + g b⟩)
      simp only [this, Sum.elim_inl]
      have key := sum_shift_count N b k (fun i => A ⟨b, i⟩)
      have hN0 : (N b : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne (N b))
      have hNT : (N b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, ← Nat.cast_smul_eq_nsmul ℝ≥0∞] at key
      calc (c : ℝ≥0∞)⁻¹ • ∑ g : (∀ b, Fin (N b)), A ⟨b, k + g b⟩
          = (c : ℝ≥0∞)⁻¹ • ((N b : ℝ≥0∞)⁻¹ • ((N b : ℝ≥0∞) •
              ∑ g : (∀ b, Fin (N b)), A ⟨b, k + g b⟩)) := by
            rw [smul_smul (N b : ℝ≥0∞)⁻¹, ENNReal.inv_mul_cancel hN0 hNT, one_smul]
        _ = (N b : ℝ≥0∞)⁻¹ • ∑ i, A ⟨b, i⟩ := by
            rw [key, smul_smul, smul_smul, mul_comm (c : ℝ≥0∞)⁻¹, mul_assoc,
              ENNReal.inv_mul_cancel hc0 hcT, mul_one]
  · rw [Measure.map_smul _ measurable_sum_coord.aemeasurable, map_finset_sum measurable_sum_coord]
    simp only [Measure.map_map measurable_sum_coord (measurable_shiftMap N _)]
    have : ∀ g : (∀ b, Fin (N b)),
        P.map ((fun x => ∑ i, x i) ∘ shiftMap N g) = P.map (fun x => ∑ i, x i) := by
      intro g; congr 1; funext x; exact sum_shiftMap N g x
    simp only [this, Finset.sum_const, Finset.card_univ, ← hc]
    exact hcc _

end shuffle

/-! ### Uniform distributions and the decomposition  -/

lemma unifI_null {l r : ℝ} (h : l ≤ r) : unifI l r (Icc l r)ᶜ = 0 := by
  unfold unifI
  split_ifs with hlr
  · rw [smul_apply, Measure.restrict_apply measurableSet_Icc.compl]; simp
  · simp [Measure.dirac_apply' _ measurableSet_Icc.compl, h]

lemma integral_unifI {l r : ℝ} (h : l < r) : ∫ x, x ∂(unifI l r) = (l + r) / 2 := by
  unfold unifI
  rw [if_pos h, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le h.le, integral_id, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.mpr h.le), smul_eq_mul]
  have : r - l ≠ 0 := sub_ne_zero.mpr h.ne'
  field_simp
  ring

lemma integrable_unifI (l r : ℝ) (h : l ≤ r) : Integrable (fun x => x) (unifI l r) := by
  have := unifI_isProb l r
  exact integrable_id_of_null (unifI_null h)

theorem decomp {G U : Measure ℝ} [IsProbabilityMeasure G] [IsProbabilityMeasure U] {q : ℝ}
    (hGU : ENNReal.ofReal q • U ≤ G) {N m : ℕ} (hm : (m : ℝ) ≤ q * N) (hmN : m ≤ N)
    (hN : 0 < N) :
    ∃ T : Measure ℝ, IsProbabilityMeasure T ∧ (∀ s, G s = 0 → T s = 0) ∧
      (N : ℝ≥0∞) • G = (m : ℝ≥0∞) • U + ((N - m : ℕ) : ℝ≥0∞) • T := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ q := by
    by_contra hc; push Not at hc
    have : q * N < 0 := mul_neg_of_neg_of_pos hc hNr
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hle : (m : ℝ≥0∞) • U ≤ (N : ℝ≥0∞) • G := by
    rw [Measure.le_iff']
    intro s
    have h1 := Measure.le_iff'.mp hGU s
    simp only [smul_apply, smul_eq_mul] at h1 ⊢
    calc (m : ℝ≥0∞) * U s = ENNReal.ofReal m * U s := by rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (q * N) * U s := by gcongr
      _ = N * (ENNReal.ofReal q * U s) := by
          rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_natCast]; ring
      _ ≤ N * G s := by gcongr
  by_cases hn : N - m = 0
  · have hmN' : m = N := by omega
    subst hmN'
    have hq1 : 1 ≤ q := by
      have : (1 : ℝ) * m ≤ q * m := by linarith
      exact le_of_mul_le_mul_right this hNr
    have hUG : U ≤ G := by
      rw [Measure.le_iff']
      intro s
      have h1 := Measure.le_iff'.mp hGU s
      simp only [smul_apply, smul_eq_mul] at h1
      calc U s = 1 * U s := (one_mul _).symm
        _ ≤ ENNReal.ofReal q * U s := by
            gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1
        _ ≤ G s := h1
    have := Measure.eq_of_le_of_isProbabilityMeasure hUG
    subst this
    exact ⟨U, inferInstance, fun s hs => hs, by simp⟩
  · set n := N - m with hndef
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
    have hnT : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hfin : IsFiniteMeasure ((m : ℝ≥0∞) • U) := ⟨by
      rw [smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top m) (measure_lt_top U _)⟩
    refine ⟨(n : ℝ≥0∞)⁻¹ • ((N : ℝ≥0∞) • G - (m : ℝ≥0∞) • U), ?_, ?_, ?_⟩
    · constructor
      rw [smul_apply, Measure.sub_apply MeasurableSet.univ hle]
      simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.natCast_sub, ← hndef]
      exact ENNReal.inv_mul_cancel hn0 hnT
    · intro s hs
      have h1 : ((N : ℝ≥0∞) • G - (m : ℝ≥0∞) • U) s ≤ ((N : ℝ≥0∞) • G) s :=
        Measure.sub_le (μ := (N : ℝ≥0∞) • G) s
      rw [smul_apply, smul_eq_mul]
      have : ((N : ℝ≥0∞) • G) s = 0 := by rw [smul_apply, hs, smul_zero]
      rw [this, nonpos_iff_eq_zero] at h1
      rw [h1, mul_zero]
    · rw [smul_smul, ENNReal.mul_inv_cancel hn0 hnT, one_smul, add_comm,
        Measure.sub_add_cancel_of_le hle]

lemma integral_decomp {G U T : Measure ℝ} [IsFiniteMeasure G] [IsFiniteMeasure U]
    [IsFiniteMeasure T] {N m n : ℕ}
    (h : (N : ℝ≥0∞) • G = (m : ℝ≥0∞) • U + (n : ℝ≥0∞) • T)
    (hiU : Integrable (fun x => x) U) (hiT : Integrable (fun x => x) T) :
    (N : ℝ) * ∫ x, x ∂G = m * ∫ x, x ∂U + n * ∫ x, x ∂T := by
  have := congrArg (fun μ => ∫ x, x ∂μ) h
  rw [integral_smul_measure, integral_add_measure (hiU.smul_measure (ENNReal.natCast_ne_top m))
    (hiT.smul_measure (ENNReal.natCast_ne_top n)), integral_smul_measure,
    integral_smul_measure] at this
  simpa using this

/-! ### Hypotheses: results of other agents -/

/-- Proposition `as:prop:window` of the paper, the case `d = 1` with `m ≥ 4` (the only case used
here): for a box `[c - H, c + H]` and `m ≥ 4`, every probability measure with mean `m c` carried by
`[m c - m H / 2, m c + m H / 2]` lies in `𝒜_m(U[c - H, c + H])`. -/
def H_window_line : Prop :=
  ∀ (m : ℕ) (c H : ℝ) (ν : Measure ℝ), 4 ≤ m → 0 < H → IsProbabilityMeasure ν →
    ∫ x, x ∂ν = m * c → ν (Icc (m * c - m * H / 2) (m * c + m * H / 2))ᶜ = 0 →
    ν ∈ aggSet (fun _ : Fin m => unifI (c - H) (c + H))

/-- Lemma `as:lem:conc` (a) of the paper: distributions `T_1, …, T_k` on the line, each carried
by an interval of length at most `ℓ`, admit random variables `Y_j ∼ T_j` whose sum takes its
values in an interval of length at most `ℓ`, so that `|∑ Y_j - ∑ m_{T_j}| ≤ ℓ`. -/
def H_conc_a : Prop :=
  ∀ (k : ℕ) (ℓ : ℝ) (T : Fin k → Measure ℝ), (∀ j, IsProbabilityMeasure (T j)) →
    (∀ j, ∃ a, T j (Icc a (a + ℓ))ᶜ = 0) →
    ∃ P : Measure (Fin k → ℝ), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = T j) ∧
      ∃ α : ℝ, ∀ᵐ x ∂P, ∑ j, x j ∈ Icc α (α + ℓ) ∧ |∑ j, x j - ∑ j, ∫ y, y ∂(T j)| ≤ ℓ

lemma win_of_window (hW : H_window_line) {m : ℕ} (hm : 4 ≤ m) (c H : ℝ) (hH : 0 < H) :
    Win (fun _ : Fin m => unifI (c - H) (c + H)) (m * c) (m * H / 2) :=
  fun ν hν h1 h2 => hW m c H ν hm hH hν h2 h1

lemma conc_fintype (hC : H_conc_a) {ι : Type*} [Fintype ι] (T : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (T i)] {ℓ : ℝ} (hT : ∀ i, ∃ a, T i (Icc a (a + ℓ))ᶜ = 0) :
    ∃ P : Measure (ι → ℝ), IsProbabilityMeasure P ∧ (∀ i, P.map (fun x => x i) = T i) ∧
      ∃ α : ℝ, ∀ᵐ x ∂P, ∑ i, x i ∈ Icc α (α + ℓ) := by
  let e := Fintype.equivFin ι
  obtain ⟨P, hP, hm, α, hα⟩ := hC (Fintype.card ι) ℓ (fun j => T (e.symm j))
    (fun j => inferInstance) (fun j => hT _)
  have hme : Measurable (fun (x : Fin (Fintype.card ι) → ℝ) (i : ι) => x (e i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  refine ⟨P.map (fun x i => x (e i)), inferInstance, fun i => ?_, α, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hme]
    have := hm (e i)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · rw [ae_map_iff hme.aemeasurable (measurable_sum_coord measurableSet_Icc)]
    filter_upwards [hα] with x hx
    rw [Equiv.sum_comp e (fun j => x j)]
    exact hx.1

lemma sum_ite_block (U T : Measure ℝ) {N m n : ℕ} (h : m + n = N) :
    ∑ i : Fin N, (if (i : ℕ) < m then U else T) = (m : ℝ≥0∞) • U + (n : ℝ≥0∞) • T := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then U else T) N, ← h,
    Finset.sum_range_add]
  have h1 : ∑ j ∈ Finset.range m, (if j < m then U else T) = ∑ j ∈ Finset.range m, U :=
    Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.mp hj)
  have h2 : ∑ j ∈ Finset.range n, (if m + j < m then U else T) = ∑ j ∈ Finset.range n, T :=
    Finset.sum_congr rfl fun j _ => if_neg (by omega)
  rw [h1, h2, Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

lemma integrable_coord_of_map {ι : Type*} {P : Measure (ι → ℝ)} [IsFiniteMeasure P] (i : ι)
    {T : Measure ℝ} (hm : P.map (fun x => x i) = T) {a b : ℝ} (hT : T (Icc a b)ᶜ = 0) :
    Integrable (fun x => x i) P := by
  apply integrable_of_ae_Icc (measurable_pi_apply i).aestronglyMeasurable
  apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
  rw [hm]; exact ae_mem_of_null hT

/-! ### Proposition `as:prop:complete` -/

/-- The common engine of Proposition `as:prop:complete` and Corollary `as:cor:three`: the proof
of Proposition `as:prop:complete`, with the block of `m_k = ⌊q_k N_k⌋` uniform variables taken as
a hypothesis `hBlock` on the deviation `Z - S` (mean `C = ∑ m_k c_k`, carried by
`[β - ρ - ℓ, β + ρ]` for some `β` with `C ∈ [β - ℓ, β]`). -/
theorem engine (hC : H_conc_a) {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hNpos : ∀ k, 0 < N k)
    (s ρ : ℝ) (hs : s = ∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = s)
    (hν : ν (Icc (s - ρ) (s + ρ))ᶜ = 0)
    (hBlock : ∀ (lam : Measure ℝ) (β : ℝ), IsProbabilityMeasure lam →
      ∫ x, x ∂lam = ∑ k, (⌊q k * N k⌋₊ : ℝ) * c k →
      ∑ k, (⌊q k * N k⌋₊ : ℝ) * c k ∈ Icc (β - ℓ) β → lam (Icc (β - ρ - ℓ) (β + ρ))ᶜ = 0 →
      lam ∈ aggSet (fun p : Σ k, Fin ⌊q k * N k⌋₊ => unifI (c p.1 - H p.1) (c p.1 + H p.1))) :
    ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) := by
  classical
  set m : Fin K → ℕ := fun k => ⌊q k * N k⌋₊ with hmdef
  have hmle : ∀ k, (m k : ℝ) ≤ q k * N k := fun k =>
    Nat.floor_le (mul_nonneg (hq0 k).le (Nat.cast_nonneg _))
  have hmN : ∀ k, m k ≤ N k := fun k => by
    have h1 : q k * N k ≤ N k := by
      have := hq1 k; have : (0 : ℝ) ≤ N k := Nat.cast_nonneg _; nlinarith
    have : (m k : ℝ) ≤ N k := (hmle k).trans h1
    exact_mod_cast this
  set n : Fin K → ℕ := fun k => N k - m k with hndef
  set U : Fin K → Measure ℝ := fun k => unifI (c k - H k) (c k + H k) with hUdef
  have hUp : ∀ k, IsProbabilityMeasure (U k) := fun k => unifI_isProb _ _
  choose T hTp hTs hTd using fun k => decomp (hGU k) (hmle k) (hmN k) (hNpos k)
  choose aG haG using hGℓ
  have hTℓ : ∀ k, T k (Icc (aG k) (aG k + ℓ))ᶜ = 0 := fun k => hTs k _ (haG k)
  have hUmean : ∀ k, ∫ x, x ∂(U k) = c k := fun k => by
    rw [hUdef]; dsimp only
    rw [integral_unifI (by linarith [hH k])]; ring
  have hTint : ∀ k, Integrable (fun x => x) (T k) := fun k => integrable_id_of_null (hTℓ k)
  have hGmean : ∀ k, (N k : ℝ) * ∫ x, x ∂(G k) = m k * c k + n k * ∫ x, x ∂(T k) := fun k => by
    rw [integral_decomp (hTd k) (integrable_unifI _ _ (by linarith [hH k])) (hTint k), hUmean k]
  -- the coupling of the `T_k` and the `F_j`
  set TF : (Σ k, Fin (n k)) ⊕ Fin r → Measure ℝ := Sum.elim (fun p => T p.1) F with hTFdef
  have hTFp : ∀ i, IsProbabilityMeasure (TF i) := by
    rintro (p | j)
    · simp only [hTFdef, Sum.elim_inl]; exact hTp p.1
    · simp only [hTFdef, Sum.elim_inr]; infer_instance
  have hTFℓ : ∀ i, ∃ a, TF i (Icc a (a + ℓ))ᶜ = 0 := by
    rintro (p | j)
    · exact ⟨_, hTℓ p.1⟩
    · exact hFℓ j
  obtain ⟨PY, hPY, hmY, α, hα⟩ := conc_fintype hC TF hTFℓ
  set E := ∑ i, ∫ x, x ∂(TF i) with hEdef
  have hEsum : E = ∑ k, (n k : ℝ) * ∫ x, x ∂(T k) + ∑ j, ∫ x, x ∂(F j) := by
    simp [hEdef, hTFdef, Fintype.sum_sum_type, Fintype.sum_sigma, Finset.sum_const]
  have hint_coord : ∀ i, Integrable (fun x : _ → ℝ => x i) PY := fun i => by
    obtain ⟨a, ha⟩ := hTFℓ i
    exact integrable_coord_of_map i (hmY i) ha
  have hESY : ∫ x, ∑ i, x i ∂PY = E := by
    rw [integral_finsetSum _ (fun i _ => hint_coord i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_id_map (measurable_pi_apply i), hmY i]
  have hEmem : E ∈ Icc α (α + ℓ) := hESY ▸
    integral_mem_Icc_of_ae measurable_sum_coord.aestronglyMeasurable hα
  -- the product with the target
  set μ := PY.prod ν with hμdef
  have hμ1 : μ.map Prod.fst = PY := by simp [hμdef]
  have hμ2 : μ.map Prod.snd = ν := by simp [hμdef]
  set C := ∑ k, (m k : ℝ) * c k with hCdef
  have hsC : s = C + E := by
    rw [hs, hEsum, hCdef, ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hGmean k
  have h1 : ∀ᵐ ω ∂μ, ∑ i, ω.1 i ∈ Icc α (α + ℓ) :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hμ1]; exact hα)
  have h2 : ∀ᵐ ω ∂μ, ω.2 ∈ Icc (s - ρ) (s + ρ) :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hμ2]; exact ae_mem_of_null hν)
  have hDm : Measurable (fun ω : ((Σ k, Fin (n k)) ⊕ Fin r → ℝ) × ℝ => ω.2 - ∑ i, ω.1 i) :=
    measurable_snd.sub (measurable_sum_coord.comp measurable_fst)
  have hD : μ.map (fun ω => ω.2 - ∑ i, ω.1 i) ∈ aggSet (fun p : Σ k, Fin (m k) => U p.1) := by
    apply hBlock _ (s - α) inferInstance
    rotate_left
    · constructor <;> linarith [hEmem.1, hEmem.2]
    · apply map_null_of_ae hDm measurableSet_Icc
      filter_upwards [h1, h2] with ω h1 h2
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have hi1 : Integrable (fun ω : ((Σ k, Fin (n k)) ⊕ Fin r → ℝ) × ℝ => ω.2) μ :=
        integrable_of_ae_Icc measurable_snd.aestronglyMeasurable h2
      have hi2 : Integrable (fun ω : ((Σ k, Fin (n k)) ⊕ Fin r → ℝ) × ℝ => ∑ i, ω.1 i) μ :=
        integrable_of_ae_Icc (measurable_sum_coord.comp measurable_fst).aestronglyMeasurable h1
      rw [integral_id_map hDm, integral_sub hi1 hi2]
      have e1 : ∫ ω, ω.2 ∂μ = s := by
        rw [← hνm, ← hμ2, integral_id_map measurable_snd]
      have e2 : ∫ ω, ∑ i, ω.1 i ∂μ = E := by
        rw [← hESY, ← hμ1, integral_map measurable_fst.aemeasurable
          measurable_sum_coord.aestronglyMeasurable]
      rw [e1, e2, hsC]; ring
  have hν' : ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (m k) => U p.1) TF) := by
    have := absorb μ (Y := Prod.fst) (Z := Prod.snd) (A := TF) measurable_fst measurable_snd
      (fun i => by
        rw [← hmY i, ← hμ1, Measure.map_map (measurable_pi_apply i) measurable_fst]; rfl)
      hD
    rwa [hμ2] at this
  -- regrouping into blocks and random order
  have hNmn : ∀ k, m k + n k = N k := fun k => by have := hmN k; simp only [hndef]; omega
  haveI : ∀ k, NeZero (N k) := fun k => ⟨(hNpos k).ne'⟩
  set A : (Σ k, Fin (N k)) → Measure ℝ := fun p => if (p.2 : ℕ) < m p.1 then U p.1 else T p.1
    with hAdef
  let e : (Σ k, Fin (m k)) ⊕ ((Σ k, Fin (n k)) ⊕ Fin r) ≃ (Σ k, Fin (N k)) ⊕ Fin r :=
    (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr
      ((Equiv.sigmaSumDistrib (fun k => Fin (m k)) (fun k => Fin (n k))).symm.trans
        (Equiv.sigmaCongrRight (fun k => finSumFinEquiv.trans (finCongr (hNmn k)))))
      (Equiv.refl _))
  have hfam : ∀ x, Sum.elim A F (e x) = Sum.elim (fun p : Σ k, Fin (m k) => U p.1) TF x := by
    rintro (⟨k, i⟩ | ⟨k, i⟩ | j)
    · simp [e, hAdef, Equiv.sigmaSumDistrib, Sigma.map]
    · simp [e, hAdef, hTFdef, Equiv.sigmaSumDistrib, Sigma.map]
    · simp [e, hTFdef]
  have h3 := aggSet_shuffle N A F (aggSet_reindex' e hfam hν')
  refine aggSet_congr ?_ h3
  funext x
  cases x with
  | inr j => rfl
  | inl p =>
    obtain ⟨k, i⟩ := p
    show (N k : ℝ≥0∞)⁻¹ • ∑ i, A ⟨k, i⟩ = G k
    have hsum : ∑ i, A ⟨k, i⟩ = (m k : ℝ≥0∞) • U k + (n k : ℝ≥0∞) • T k :=
      sum_ite_block (U k) (T k) (hNmn k)
    rw [hsum, ← hTd k, smul_smul, ENNReal.inv_mul_cancel (by exact_mod_cast (hNpos k).ne')
      (ENNReal.natCast_ne_top _), one_smul]


/-- **Proposition `as:prop:complete`.** `N_k` copies of `G_k ≥ q_k U[c_k - H_k, c_k + H_k]`
(`k < K`) and further distributions `F_1, …, F_r`, all carried by intervals of length at most
`ℓ`: if `m_k = ⌊q_k N_k⌋ ≥ 4` and `ρ = ∑ m_k H_k / 2 - ℓ ≥ 0`, the aggregation set contains every
distribution with mean `s` (the sum of all means) carried by `[s - ρ, s + ρ]`.
(The hypothesis `ρ ≥ 0` is not needed for this part: it follows from the existence of `ν`.) -/
theorem prop_complete (hW : H_window_line) (hC : H_conc_a) {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hm4 : ∀ k, 4 ≤ ⌊q k * N k⌋₊)
    (s ρ : ℝ) (hs : s = ∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j))
    (hρ : ρ = ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 - ℓ) (_hρ0 : 0 ≤ ρ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = s)
    (hν : ν (Icc (s - ρ) (s + ρ))ᶜ = 0) :
    ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) := by
  have hNpos : ∀ k, 0 < N k := fun k => by
    by_contra h
    have h0 : N k = 0 := by omega
    have := hm4 k
    rw [h0] at this
    simp at this
  refine engine hC G F ℓ hGℓ hFℓ c H q hH hq0 hq1 hGU N hNpos s ρ hs ν hνm hν ?_
  intro lam β hlam hmean hC' hsupp
  have hWin := win_sigma K (fun k => Fin ⌊q k * N k⌋₊) (fun k _ => unifI (c k - H k) (c k + H k))
    (fun k => ⌊q k * N k⌋₊ * c k) (fun k => ⌊q k * N k⌋₊ * H k / 2)
    (fun k => by have := hH k; positivity) (fun k => win_of_window hW (hm4 k) _ _ (hH k))
  apply hWin lam hlam _ hmean
  refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hsupp
  intro x hx
  have hW : ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 = ρ + ℓ := by rw [hρ]; ring
  rw [hW]
  constructor <;> linarith [hx.1, hx.2, hC'.1, hC'.2]

/-- Proposition `as:prop:complete`, "in particular they are jointly mixable": the point mass at
the sum of the means lies in the aggregation set. -/
theorem prop_complete_dirac (hW : H_window_line) (hC : H_conc_a) {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hm4 : ∀ k, 4 ≤ ⌊q k * N k⌋₊)
    (hρ0 : 0 ≤ ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 - ℓ) :
    Measure.dirac (∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) := by
  refine prop_complete hW hC G F ℓ hGℓ hFℓ c H q hH hq0 hq1 hGU N hm4 _ _ rfl rfl hρ0 _
    (by simp) ?_
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_not]
  constructor <;> linarith

/-- A point mass in the aggregation set of a family indexed by any finite type gives a joint mix
for every enumeration of the family. -/
lemma jointlyMixable_of_dirac_equiv {ι : Type*} [Fintype ι] {A : ι → Measure ℝ} {s : ℝ}
    (h : Measure.dirac s ∈ aggSet A) {n : ℕ} (e : ι ≃ Fin n) :
    JointlyMixable (fun j => A (e.symm j)) :=
  jointlyMixable_of_dirac (aggSet_reindex e h)

lemma integral_unifI01 : ∫ x, x ∂(unifI 0 1) = 1 / 2 := by
  rw [integral_unifI one_pos]; norm_num

/-- Proposition `as:prop:complete`, "for instance": four uniform distributions on `[0, 1]`
together with any finite family of distributions on intervals of length at most `1` are jointly
mixable. -/
theorem four_uniform_jointlyMixable (hW : H_window_line) (hC : H_conc_a) {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 4 => unifI 0 1) F) := by
  have hU : unifI (1 / 2 - 1 / 2) (1 / 2 + 1 / 2) = unifI 0 1 := by norm_num
  have := unifI_isProb 0 1
  have h := prop_complete_dirac hW hC (fun _ : Fin 1 => unifI 0 1) F 1
    (fun _ => ⟨0, by simpa using unifI_null zero_le_one⟩) hF (fun _ => 1 / 2) (fun _ => 1 / 2)
    (fun _ => 1) (fun _ => by norm_num) (fun _ => one_pos) (fun _ => le_rfl)
    (fun _ => by rw [hU]; simp) (fun _ => 4) (fun _ => by norm_num) (by norm_num)
  convert h using 2
  simp [integral_unifI01]
  norm_num

/-! ### Corollary `as:cor:three`, from the statement of Proposition `as:prop:three` -/

/-- The length `L` of Proposition `as:prop:three`: `m H` for `m ≥ 4` and `2 H` for `m = 3`. -/
def lenThree (m : ℕ) (H : ℝ) : ℝ := if 4 ≤ m then m * H else 2 * H

/-- The statement of **Proposition `as:prop:three`**: for `m ≥ 3` and `H > 0`, a probability
measure with mean `m c` carried by an interval of length `L` that contains `m c` lies in
`𝒜_m(U[c - H, c + H])`; for `m = 3` the same holds for measures carried by `[3c - H, 3c + 2H]` or
by `[3c - 2H, 3c + H]`. -/
def PropThree : Prop :=
  (∀ (m : ℕ) (c H : ℝ) (ν : Measure ℝ), 3 ≤ m → 0 < H → IsProbabilityMeasure ν →
    ∫ x, x ∂ν = m * c → ∀ a : ℝ, a ≤ m * c → m * c ≤ a + lenThree m H →
    ν (Icc a (a + lenThree m H))ᶜ = 0 → ν ∈ aggSet (fun _ : Fin m => unifI (c - H) (c + H))) ∧
  (∀ (c H : ℝ) (ν : Measure ℝ), 0 < H → IsProbabilityMeasure ν → ∫ x, x ∂ν = 3 * c →
    (ν (Icc (3 * c - H) (3 * c + 2 * H))ᶜ = 0 ∨ ν (Icc (3 * c - 2 * H) (3 * c + H))ᶜ = 0) →
    ν ∈ aggSet (fun _ : Fin 3 => unifI (c - H) (c + H)))

lemma lenThree_ge (m : ℕ) {H : ℝ} (hH : 0 < H) (hm : 3 ≤ m) : 2 * H ≤ lenThree m H := by
  unfold lenThree
  split_ifs with h
  · have : (4 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith
  · exact le_rfl

/-- The block hypothesis of `engine` for one block, from Proposition `as:prop:three`. -/
lemma block_of_three (h3 : PropThree) {m : ℕ} (hm : 3 ≤ m) (c H R ρ : ℝ) (hH : 0 < H)
    (hρ : 2 * ρ + R = lenThree m H) (hρ0 : 0 ≤ ρ) (lam : Measure ℝ) (β : ℝ)
    (hlam : IsProbabilityMeasure lam) (hmean : ∫ x, x ∂lam = ∑ _k : Fin 1, (m : ℝ) * c)
    (hC : ∑ _k : Fin 1, (m : ℝ) * c ∈ Icc (β - R) β)
    (hsupp : lam (Icc (β - ρ - R) (β + ρ))ᶜ = 0) :
    lam ∈ aggSet (fun _ : Σ _k : Fin 1, Fin m => unifI (c - H) (c + H)) := by
  simp only [Finset.univ_unique, Finset.sum_singleton] at hmean hC
  have h := h3.1 m c H lam hm hH hlam hmean (β - ρ - R) (by linarith [hC.1])
    (by linarith [hC.2]) (by rw [← hρ]; ring_nf; ring_nf at hsupp; exact hsupp)
  exact aggSet_reindex' (Equiv.uniqueSigma (fun _ : Fin 1 => Fin m)).symm (fun _ => rfl) h

/-- **Corollary `as:cor:three`** (main statement). Let `F` have mean `μ`, be carried by an
interval of length `R`, and satisfy `F ≥ q U[c - H, c + H]`; let `m = ⌊q n⌋ ≥ 3` and `L ≥ R`.
Then `𝒜_n(F)` contains every distribution with mean `n μ` carried by
`[n μ - (L - R)/2, n μ + (L - R)/2]`. -/
theorem cor_three (h3 : PropThree) (hC : H_conc_a) (F : Measure ℝ) [IsProbabilityMeasure F]
    (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H) (hq0 : 0 < q)
    (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hν : ν (Icc (n * ∫ x, x ∂F - (lenThree ⌊q * n⌋₊ H - R) / 2)
      (n * ∫ x, x ∂F + (lenThree ⌊q * n⌋₊ H - R) / 2))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin n => F) := by
  have hn : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hm3; simp at hm3
  have : ∀ j : Fin 0, IsProbabilityMeasure ((Fin.elim0 : Fin 0 → Measure ℝ) j) := fun j => j.elim0
  have h := engine hC (fun _ : Fin 1 => F) (Fin.elim0 : Fin 0 → Measure ℝ) R (fun _ => hR)
    (fun j => j.elim0) (fun _ => c) (fun _ => H) (fun _ => q) (fun _ => hH) (fun _ => hq0)
    (fun _ => hq1) (fun _ => hFU) (fun _ => n) (fun _ => hn) (n * ∫ x, x ∂F)
    ((lenThree ⌊q * n⌋₊ H - R) / 2) (by simp) ν hνm hν
    (fun lam β hlam hmean hC' hsupp => block_of_three h3 hm3 c H R _ hH (by ring)
      (by linarith) lam β hlam hmean hC' hsupp)
  refine aggSet_reindex' ((Equiv.sumEmpty _ _).trans (Equiv.uniqueSigma _)) ?_ h
  rintro (p | j)
  · rfl
  · exact j.elim0

/-- Corollary `as:cor:three`: `F` is `n`-completely mixable. -/
theorem cor_three_mixable (h3 : PropThree) (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H) : CompletelyMixable n F := by
  refine jointlyMixable_of_dirac (cor_three h3 hC F R hR c H q hH hq0 hq1 hFU n hm3 hLR
    (Measure.dirac (n * ∫ x, x ∂F)) (by simp) ?_)
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_not]
  constructor <;> linarith

/-- Corollary `as:cor:three` (a): `F` is `n`-completely mixable as soon as
`⌊q n⌋ ≥ max(4, R/H)`. -/
theorem cor_three_a (h3 : PropThree) (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (h4 : 4 ≤ ⌊q * n⌋₊) (hRH : R / H ≤ ⌊q * n⌋₊) : CompletelyMixable n F := by
  refine cor_three_mixable h3 hC F R hR c H q hH hq0 hq1 hFU n (by omega) ?_
  unfold lenThree
  rw [if_pos h4]
  rwa [div_le_iff₀ hH] at hRH

/-- Corollary `as:cor:three` (b), the theorem of Puccetti, Wang and Wang with an explicit
complete mix: a distribution on `[a, b]` with `F ≥ (3/n) U[a, b]` is `n`-completely mixable.
(Such an `F` forces `n ≥ 3`; this is assumed.) -/
theorem cor_three_b (h3 : PropThree) (hC : H_conc_a) (F : Measure ℝ) [IsProbabilityMeasure F]
    {a b : ℝ} (hab : a < b) (hF : F (Icc a b)ᶜ = 0) (n : ℕ) (hn : 3 ≤ n)
    (hFU : ENNReal.ofReal (3 / n) • unifI a b ≤ F) : CompletelyMixable n F := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hq : (3 / n : ℝ) * n = 3 := by field_simp
  have hU : unifI ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) = unifI a b := by
    congr 1 <;> ring
  refine cor_three_mixable h3 hC F (b - a) ⟨a, by rwa [add_sub_cancel]⟩ ((a + b) / 2)
    ((b - a) / 2) (3 / n) (by linarith) (by positivity) (by rw [div_le_one (by positivity)]; exact hnr)
    (by rw [hU]; exact hFU) n (by rw [hq]; simp) ?_
  rw [hq]
  simp only [lenThree]
  norm_num
  linarith

/-- Corollary `as:cor:three` (c): three uniform distributions on `[0, 1]` together with any
finite family of distributions on intervals of length at most `1` are jointly mixable. -/
theorem cor_three_c (h3 : PropThree) (hC : H_conc_a) {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 3 => unifI 0 1) F) := by
  have hU : unifI (1 / 2 - 1 / 2) (1 / 2 + 1 / 2) = unifI 0 1 := by norm_num
  have := unifI_isProb 0 1
  have h3eq : ⌊(1 : ℝ) * (3 : ℕ)⌋₊ = 3 := by norm_num
  have h := engine hC (fun _ : Fin 1 => unifI 0 1) F 1
    (fun _ => ⟨0, by simpa using unifI_null zero_le_one⟩) hF (fun _ => 1 / 2) (fun _ => 1 / 2)
    (fun _ => 1) (fun _ => by norm_num) (fun _ => one_pos) (fun _ => le_rfl)
    (fun _ => by rw [hU]; simp) (fun _ => 3) (fun _ => by norm_num)
    (3 / 2 + ∑ j, ∫ x, x ∂(F j)) 0 (by simp [integral_unifI01]; norm_num)
    (Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j))) (by simp) (by
      rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
      simp)
    (fun lam β hlam hmean hC' hsupp => by
      have hm' : 3 ≤ ⌊(1 : ℝ) * ((3 : ℕ) : ℝ)⌋₊ := by rw [h3eq]
      exact block_of_three h3 hm' (1 / 2) (1 / 2) 1 0 (by norm_num)
        (by rw [h3eq]; simp [lenThree]) le_rfl lam β hlam hmean hC' hsupp)
  exact h

open Set
open scoped ENNReal

/-! ### Kernels with a parameter, uniform complete mixes, the density `g_{a,b}` -/

open ProbabilityTheory

/-- The kernel `a ↦ (K a).map (Ψ (a, ·))`. -/
def paramMap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (K : Kernel α β) (Ψ : α × β → γ) : Kernel α γ :=
  Kernel.map (Kernel.id ×ₖ K) Ψ

lemma paramMap_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (K : Kernel α β) [IsSFiniteKernel K] {Ψ : α × β → γ}
    (hΨ : Measurable Ψ) (a : α) : paramMap K Ψ a = (K a).map (fun y => Ψ (a, y)) := by
  rw [paramMap, Kernel.map_apply _ hΨ, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hΨ measurable_prodMk_left]
  rfl

lemma paramMap_isMarkov {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (K : Kernel α β) [IsMarkovKernel K] {Ψ : α × β → γ}
    (hΨ : Measurable Ψ) : IsMarkovKernel (paramMap K Ψ) := by
  unfold paramMap
  exact Kernel.IsMarkovKernel.map _ hΨ

/-- An affine image of a uniform distribution. -/
lemma unifI_map_affine {l r : ℝ} (hlr : l < r) (p d : ℝ) (hd : d ≠ 0) :
    (unifI l r).map (fun x => p + d * x) =
      unifI (min (p + d * l) (p + d * r)) (max (p + d * l) (p + d * r)) := by
  have h1 := map_affine_unifI l (r - l) (sub_ne_zero.mpr hlr.ne')
  rw [min_eq_left (by linarith), max_eq_right (by linarith), add_sub_cancel] at h1
  rw [← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := map_affine_unifI (p + d * l) (d * (r - l)) (mul_ne_zero hd (sub_ne_zero.mpr hlr.ne'))
  have e : p + d * l + d * (r - l) = p + d * r := by ring
  rw [e] at h2
  rw [← h2]
  congr 1
  funext v
  simp only [Function.comp_apply]
  ring

lemma unifI_map_incr {l r : ℝ} (hlr : l < r) (p d : ℝ) (hd : 0 < d) :
    (unifI l r).map (fun x => p + d * x) = unifI (p + d * l) (p + d * r) := by
  rw [unifI_map_affine hlr p d hd.ne', min_eq_left, max_eq_right] <;> nlinarith

lemma unifI_map_decr {l r : ℝ} (hlr : l < r) (p d : ℝ) (hd : 0 < d) :
    (unifI l r).map (fun x => p - d * x) = unifI (p - d * r) (p - d * l) := by
  have := unifI_map_affine hlr p (-d) (by linarith)
  rw [min_eq_right (by nlinarith), max_eq_left (by nlinarith)] at this
  convert this using 2 <;> ring

/-- A complete mix of `U[0, 1]` for `m ≥ 2`, from Lemma `lem:arch` (`ConeMix.chord0_spec`). -/
def M1 (m : ℕ) : Measure (Fin m → ℝ) :=
  archPlane.map (fun ξ => Assembly.chordVec 0 0 0 (fun _ : Fin m => (1 : ℝ)) ξ)

lemma M1_spec {m : ℕ} (hm : 2 ≤ m) : IsProbabilityMeasure (M1 m) ∧
    (∀ i, (M1 m).map (fun x => x i) = unifI 0 1) ∧ ∀ᵐ x ∂(M1 m), ∑ i, x i = (m : ℝ) / 2 := by
  have hmeas := Assembly.measurable_chordVec_right (n := m) 0 0 0 (fun _ => (1 : ℝ))
  obtain ⟨hmarg, hsum⟩ := ConeMix.chord0_spec (n := m) (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    ⟨⟨0, by omega⟩, one_pos⟩ (fun j => by simp; exact_mod_cast (show 2 ≤ m from hm))
  refine ⟨by unfold M1; infer_instance, fun i => ?_, ?_⟩
  · rw [M1, Measure.map_map (measurable_pi_apply i) hmeas]
    exact hmarg i
  · refine (ae_map_iff hmeas.aemeasurable (measurableSet_eq_fun measurable_sum_coord
      measurable_const)).mpr ?_
    filter_upwards [hsum] with ξ hξ
    rw [hξ]; simp; ring

/-- The uniform complete mixes as a kernel: `(l, r) ↦` a complete mix of `U[l, r]`. -/
def unifKernel (m : ℕ) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  paramMap (Kernel.const _ (M1 m)) (fun z => fun i => z.1.1 + (z.1.2 - z.1.1) * z.2 i)

lemma measurable_unifPsi (m : ℕ) :
    Measurable (fun z : (ℝ × ℝ) × (Fin m → ℝ) => fun i => z.1.1 + (z.1.2 - z.1.1) * z.2 i) :=
  measurable_pi_iff.mpr fun i => by fun_prop

lemma unifKernel_apply {m : ℕ} (hm : 2 ≤ m) (l r : ℝ) :
    unifKernel m (l, r) = (M1 m).map (fun x i => l + (r - l) * x i) := by
  have := (M1_spec hm).1
  rw [unifKernel, paramMap_apply _ (measurable_unifPsi m)]
  rfl

lemma unifKernel_isMarkov {m : ℕ} (hm : 2 ≤ m) : IsMarkovKernel (unifKernel m) := by
  have := (M1_spec hm).1
  exact paramMap_isMarkov _ (measurable_unifPsi m)

lemma unifKernel_marg {m : ℕ} (hm : 2 ≤ m) {l r : ℝ} (hlr : l < r) (i : Fin m) :
    (unifKernel m (l, r)).map (fun x => x i) = unifI l r := by
  have hme : Measurable (fun (x : Fin m → ℝ) (j : Fin m) => l + (r - l) * x j) :=
    measurable_pi_iff.mpr fun j => by fun_prop
  rw [unifKernel_apply hm, Measure.map_map (measurable_pi_apply i) hme]
  have : (fun x : Fin m → ℝ => x i) ∘ (fun (x : Fin m → ℝ) (j : Fin m) => l + (r - l) * x j) =
      (fun v => l + (r - l) * v) ∘ (fun x : Fin m → ℝ => x i) := rfl
  rw [this, ← Measure.map_map (g := fun v => l + (r - l) * v) (f := fun x : Fin m → ℝ => x i)
    (by fun_prop) (measurable_pi_apply i), (M1_spec hm).2.1 i,
    unifI_map_incr zero_lt_one l (r - l) (by linarith)]
  congr 1 <;> ring

lemma unifKernel_sum {m : ℕ} (hm : 2 ≤ m) (l r : ℝ) :
    ∀ᵐ x ∂(unifKernel m (l, r)), ∑ i, x i = m * (l + r) / 2 := by
  have hme : Measurable (fun (x : Fin m → ℝ) (j : Fin m) => l + (r - l) * x j) :=
    measurable_pi_iff.mpr fun j => by fun_prop
  rw [unifKernel_apply hm, ae_map_iff hme.aemeasurable
    (measurableSet_eq_fun measurable_sum_coord measurable_const)]
  filter_upwards [(M1_spec hm).2.2] with x hx
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx]
  simp; ring

/-- The density `g_{a,b}` as a combination of two uniform distributions. -/
lemma gMeas_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (h1 : 0 ≤ TwoStep.h1 a b)
    (h2 : 0 ≤ TwoStep.h2 a b) :
    volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g a b x)) =
      ENNReal.ofReal (TwoStep.h1 a b * a) • unifI 0 a +
        ENNReal.ofReal (TwoStep.h2 a b * (b - a)) • unifI a b := by
  have hfun : (fun x => ENNReal.ofReal (TwoStep.g a b x)) =
      (Ico 0 a).indicator (fun _ => ENNReal.ofReal (TwoStep.h1 a b)) +
        (Ico a b).indicator (fun _ => ENNReal.ofReal (TwoStep.h2 a b)) := by
    funext x
    simp only [TwoStep.g, Pi.add_apply, Set.indicator, mem_Ico]
    by_cases hx1 : 0 ≤ x ∧ x < a
    · have : ¬ (a ≤ x ∧ x < b) := fun h => by linarith [h.1, hx1.2]
      simp [hx1, this]
    · by_cases hx2 : a ≤ x ∧ x < b
      · simp [hx1, hx2]
      · simp [hx1, hx2]
  rw [hfun, withDensity_add_left (measurable_const.indicator measurableSet_Ico),
    withDensity_indicator measurableSet_Ico, withDensity_indicator measurableSet_Ico,
    withDensity_const, withDensity_const, unifI, unifI, if_pos ha, if_pos hab,
    Measure.restrict_congr_set Ico_ae_eq_Icc, Measure.restrict_congr_set Ico_ae_eq_Icc,
    smul_smul, smul_smul, ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h2, sub_zero, mul_assoc,
    mul_assoc, ENNReal.mul_inv_cancel (by simpa using ha) ENNReal.ofReal_ne_top,
    ENNReal.mul_inv_cancel (by simpa using hab) ENNReal.ofReal_ne_top, mul_one, mul_one]

/-! ### Proposition `as:prop:three`: the two distributions of a pair -/

/-- Theorem `m:thm:two` with Lemma `lem:sym` (whose existence part is verified as
`Mixes.completelyMixable_g`), together with the Borel dependence on `(a, b)` that the paper asserts
in the proofs of Lemma `as:lem:tilt` and Proposition `as:prop:three`: for `m ≥ 3` there is a
Markov kernel `(a, b) ↦` an `m`-complete mix of `g_{a,b}` with sum `m`, for `0 < a < 2 < b ≤ m`. -/
def H_twoStepBorel : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∃ K : Kernel (ℝ × ℝ) (Fin m → ℝ), IsMarkovKernel K ∧
    ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ m →
      (∀ i, (K (a, b)).map (fun x => x i) =
        volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g a b x))) ∧
      ∀ᵐ x ∂(K (a, b)), ∑ i, x i = (m : ℝ)

/-- The reflection `y ↦ 2 - y` of all coordinates. -/
def reflT {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => 2 - x i

lemma measurable_reflT {m : ℕ} : Measurable (reflT (m := m)) :=
  measurable_pi_iff.mpr fun i => by unfold reflT; fun_prop

/-- Case `v ≤ m - 2`, the negative deviation: a complete mix of `U[0, 2 - 2u/m]`. -/
def KmI (m : ℕ) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  (unifKernel m).comap (fun p => ((0 : ℝ), 2 - 2 * p.1 / m)) (by fun_prop)

/-- Case `v ≤ m - 2`, `u + v = m`, the positive deviation: a complete mix of
`U[2 - 2u/m, 2]`. -/
def KpU (m : ℕ) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  (unifKernel m).comap (fun p => (2 - 2 * p.1 / m, (2 : ℝ))) (by fun_prop)

/-- The parameters `a = 2u/(m - v)`, `b = 2m/(m - v)` of the density with two steps. -/
def abMap (m : ℕ) (p : ℝ × ℝ) : ℝ × ℝ := (2 * p.1 / (m - p.2), 2 * m / (m - p.2))

lemma measurable_abMap (m : ℕ) : Measurable (abMap m) := by unfold abMap; fun_prop

lemma measurable_KpGPsi (m : ℕ) : Measurable (fun z : (ℝ × ℝ) × (Fin m → ℝ) =>
    fun i => 2 - (1 - z.1.2 / m) * z.2 i) :=
  measurable_pi_iff.mpr fun i => by fun_prop

/-- Case `v ≤ m - 2`, `u + v < m`, the positive deviation: the image of the complete mix of
`g_{a,b}` under `y ↦ 2 - (1 - v/m) y`. -/
def KpG (m : ℕ) (Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  paramMap (Kg.comap (abMap m) (measurable_abMap m)) (fun z => fun i => 2 - (1 - z.1.2 / m) * z.2 i)

lemma measurableSet_sumEq (m : ℕ) : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 = m} :=
  measurableSet_eq_fun (by fun_prop) measurable_const

lemma measurableSet_vle (m : ℕ) : MeasurableSet {p : ℝ × ℝ | p.2 ≤ m - 2} :=
  measurableSet_le measurable_snd measurable_const

open Classical in
def KpI (m : ℕ) (Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  Kernel.piecewise (measurableSet_sumEq m) (KpU m) (KpG m Kg)

open Classical in
/-- The kernel of the negative deviation of a pair `(u, v)`. -/
def Pm (m : ℕ) (Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  Kernel.piecewise (measurableSet_vle m) (KmI m)
    (((KpI m Kg).comap Prod.swap measurable_swap).map reflT)

open Classical in
/-- The kernel of the positive deviation of a pair `(u, v)`. -/
def Pp (m : ℕ) (Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)) : Kernel (ℝ × ℝ) (Fin m → ℝ) :=
  Kernel.piecewise (measurableSet_vle m) (KpI m Kg)
    (((KmI m).comap Prod.swap measurable_swap).map reflT)

section pair

variable {m : ℕ} (hm : 3 ≤ m) {Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)} [IsMarkovKernel Kg]

include hm in
lemma KmI_spec {u v : ℝ} (hu : 0 < u) (hum : u < m) :
    (∀ i, (KmI m (u, v)).map (fun x => x i) = unifI 0 (2 - 2 * u / m)) ∧
      ∀ᵐ x ∂(KmI m (u, v)), ∑ i, x i = m - u := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlt : (0 : ℝ) < 2 - 2 * u / m := by
    have : u / m < 1 := (div_lt_one hm0).mpr hum
    have : 2 * u / m = 2 * (u / m) := by ring
    linarith
  refine ⟨fun i => ?_, ?_⟩
  · rw [KmI, Kernel.comap_apply]; exact unifKernel_marg (by omega) hlt i
  · rw [KmI, Kernel.comap_apply]
    filter_upwards [unifKernel_sum (by omega) 0 (2 - 2 * u / m)] with x hx
    rw [hx]; field_simp; ring

include hm in
lemma KpU_spec {u v : ℝ} (hu : 0 < u) (hum : u < m) :
    (∀ i, (KpU m (u, v)).map (fun x => x i) = unifI (2 - 2 * u / m) 2) ∧
      ∀ᵐ x ∂(KpU m (u, v)), ∑ i, x i = 2 * m - u := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlt : 2 - 2 * u / m < 2 := by
    have : 0 < 2 * u / m := by positivity
    linarith
  refine ⟨fun i => ?_, ?_⟩
  · rw [KpU, Kernel.comap_apply]; exact unifKernel_marg (by omega) hlt i
  · rw [KpU, Kernel.comap_apply]
    filter_upwards [unifKernel_sum (by omega) (2 - 2 * u / m) 2] with x hx
    rw [hx]; field_simp; ring

/-- The image of `g_{a,b}` under `y ↦ 2 - (1 - v/m) y`. -/
lemma gMeas_map {u v : ℝ} (hm0 : (0 : ℝ) < m) (hu : 0 < u) (hv : 0 < v) (huv : u + v < m) :
    (volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g (abMap m (u, v)).1
        (abMap m (u, v)).2 x))).map (fun y => 2 - (1 - v / m) * y) =
      ENNReal.ofReal (TwoStep.h1 (abMap m (u, v)).1 (abMap m (u, v)).2 * (abMap m (u, v)).1) •
        unifI (2 - 2 * u / m) 2 +
      ENNReal.ofReal (TwoStep.h2 (abMap m (u, v)).1 (abMap m (u, v)).2 *
        ((abMap m (u, v)).2 - (abMap m (u, v)).1)) • unifI 0 (2 - 2 * u / m) := by
  simp only [abMap]
  have hmv : (0 : ℝ) < m - v := by linarith
  set a := 2 * u / (m - v) with ha
  set b := 2 * m / (m - v) with hb
  have ha0 : 0 < a := by positivity
  have hab : a < b := by rw [ha, hb]; gcongr; linarith
  have ha2 : a < 2 := by rw [ha, div_lt_iff₀ hmv]; linarith
  have hb2 : 2 < b := by rw [hb, lt_div_iff₀ hmv]; linarith
  have hh1 : 0 ≤ TwoStep.h1 a b := by unfold TwoStep.h1; apply div_nonneg <;> nlinarith
  have hh2 : 0 ≤ TwoStep.h2 a b := by
    unfold TwoStep.h2; apply div_nonneg (by linarith); nlinarith
  have hc : 0 < 1 - v / m := by rw [sub_pos, div_lt_one hm0]; linarith
  rw [gMeas_eq ha0 hab hh1 hh2, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop),
    unifI_map_decr ha0 2 _ hc, unifI_map_decr hab 2 _ hc]
  have e1 : 2 - (1 - v / m) * a = 2 - 2 * u / m := by rw [ha]; field_simp; try ring
  have e2 : 2 - (1 - v / m) * b = 0 := by rw [hb]; field_simp; try ring
  rw [e1, e2, mul_zero, sub_zero]

include hm in
/-- The two-step identity of Proposition `as:prop:three` in the case `v ≤ m - 2`. -/
lemma caseI (hK : ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ m →
      (∀ i, (Kg (a, b)).map (fun x => x i) =
        volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g a b x))) ∧
      ∀ᵐ x ∂(Kg (a, b)), ∑ i, x i = (m : ℝ))
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hvm : v ≤ m - 2) (huv : u + v ≤ m) :
    (∀ᵐ x ∂(KmI m (u, v)), ∑ i, x i = m - u) ∧ (∀ᵐ x ∂(KpI m Kg (u, v)), ∑ i, x i = m + v) ∧
    ∀ i, ENNReal.ofReal v • (KmI m (u, v)).map (fun x => x i) +
      ENNReal.ofReal u • (KpI m Kg (u, v)).map (fun x => x i) =
        ENNReal.ofReal (u + v) • unifI 0 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hum : u < m := by linarith
  obtain ⟨hmI, hsI⟩ := KmI_spec hm (v := v) hu hum
  set t := 2 - 2 * u / m with ht
  have ht0 : 0 < t := by
    have : u / m < 1 := (div_lt_one hm0).mpr hum
    have : 2 * u / m = 2 * (u / m) := by ring
    linarith
  have ht2 : t < 2 := by
    have : 0 < 2 * u / m := by positivity
    linarith
  have hsplit := unifI_split two_pos ht0.le ht2.le
  refine ⟨hsI, ?_, fun i => ?_⟩
  · by_cases he : u + v = m
    · rw [KpI, Kernel.piecewise_apply,
        if_pos (show (u, v) ∈ {p : ℝ × ℝ | p.1 + p.2 = m} from he)]
      filter_upwards [(KpU_spec hm (v := v) hu hum).2] with x hx
      rw [hx]; linarith
    · rw [KpI, Kernel.piecewise_apply,
        if_neg (show (u, v) ∉ {p : ℝ × ℝ | p.1 + p.2 = m} from he)]
      have hlt : u + v < m := lt_of_le_of_ne huv he
      have hmv : (0 : ℝ) < m - v := by linarith
      obtain ⟨-, hs⟩ := hK (abMap m (u, v)).1 (abMap m (u, v)).2
        (by simp only [abMap]; positivity)
        (by simp only [abMap]; rw [div_lt_iff₀ hmv]; linarith)
        (by simp only [abMap]; rw [lt_div_iff₀ hmv]; linarith)
        (by simp only [abMap]; rw [div_le_iff₀ hmv]; nlinarith)
      rw [KpG, paramMap_apply _ (measurable_KpGPsi m), Kernel.comap_apply,
        ae_map_iff (measurable_pi_iff.mpr fun i => by fun_prop).aemeasurable
          (measurableSet_eq_fun measurable_sum_coord measurable_const)]
      filter_upwards [hs] with x hx
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, hx]
      field_simp; ring
  · rw [hmI i, hsplit]
    by_cases he : u + v = m
    · rw [KpI, Kernel.piecewise_apply,
        if_pos (show (u, v) ∈ {p : ℝ × ℝ | p.1 + p.2 = m} from he), (KpU_spec hm (v := v) hu hum).1 i, smul_add,
        smul_smul, smul_smul, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_mul (by linarith)]
      have hv' : v = m - u := by linarith
      have e1 : (u + v) * (t / 2) = v := by rw [ht, hv']; field_simp; ring
      have e2 : (u + v) * (1 - t / 2) = u := by rw [ht, hv']; field_simp; ring
      rw [e1, e2]
    · rw [KpI, Kernel.piecewise_apply,
        if_neg (show (u, v) ∉ {p : ℝ × ℝ | p.1 + p.2 = m} from he)]
      have hlt : u + v < m := lt_of_le_of_ne huv he
      have hmv : (0 : ℝ) < m - v := by linarith
      obtain ⟨hmg, -⟩ := hK (abMap m (u, v)).1 (abMap m (u, v)).2
        (by simp only [abMap]; positivity)
        (by simp only [abMap]; rw [div_lt_iff₀ hmv]; linarith)
        (by simp only [abMap]; rw [lt_div_iff₀ hmv]; linarith)
        (by simp only [abMap]; rw [div_le_iff₀ hmv]; nlinarith)
      have hmap : (KpG m Kg (u, v)).map (fun x => x i) =
          (volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g (abMap m (u, v)).1
            (abMap m (u, v)).2 x))).map (fun y => 2 - (1 - v / m) * y) := by
        have hΦ : Measurable (fun (y : Fin m → ℝ) (j : Fin m) => 2 - (1 - v / m) * y j) :=
          measurable_pi_iff.mpr fun j => by fun_prop
        rw [KpG, paramMap_apply _ (measurable_KpGPsi m), Kernel.comap_apply]
        change Measure.map (fun x : Fin m → ℝ => x i)
          (Measure.map (fun (y : Fin m → ℝ) (j : Fin m) => 2 - (1 - v / m) * y j)
            (Kg (abMap m (u, v)))) = _
        rw [Measure.map_map (measurable_pi_apply i) hΦ]
        have : (fun x : Fin m → ℝ => x i) ∘ (fun (y : Fin m → ℝ) (j : Fin m) =>
            2 - (1 - v / m) * y j) = (fun y : ℝ => 2 - (1 - v / m) * y) ∘
            (fun x : Fin m → ℝ => x i) := rfl
        rw [this, ← Measure.map_map (g := fun y : ℝ => 2 - (1 - v / m) * y)
          (f := fun x : Fin m → ℝ => x i) (by fun_prop) (measurable_pi_apply i)]
        congr 1
        exact hmg i
      rw [hmap, gMeas_map hm0 hu hv hlt]
      simp only [abMap]
      set a := 2 * u / (m - v) with ha
      set b := 2 * m / (m - v) with hb
      have hab : a < b := by rw [ha, hb]; gcongr; try linarith
      have ha2 : a < 2 := by rw [ha, div_lt_iff₀ hmv]; linarith
      have ha0 : 0 < a := by rw [ha]; positivity
      have hb2 : 2 < b := by rw [hb, lt_div_iff₀ hmv]; linarith
      have hA : 0 ≤ TwoStep.h1 a b * a := by
        unfold TwoStep.h1; apply mul_nonneg _ ha0.le; apply div_nonneg <;> nlinarith
      have hB : 0 ≤ TwoStep.h2 a b * (b - a) := by
        unfold TwoStep.h2; apply mul_nonneg _ (by linarith)
        apply div_nonneg (by linarith); nlinarith
      rw [smul_add, smul_smul, smul_smul, smul_add, smul_smul, smul_smul,
        ← ENNReal.ofReal_mul hu.le, ← ENNReal.ofReal_mul hu.le,
        ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith)]
      have e1 : (u + v) * (t / 2) = v + u * (TwoStep.h2 a b * (b - a)) := by
        rw [ht, ha, hb]; unfold TwoStep.h2
        have : (2 * m / (m - v) - 2 * u / (m - v)) ≠ 0 := by
          rw [← sub_div]; apply div_ne_zero _ hmv.ne'; linarith
        field_simp; ring
      have e2 : (u + v) * (1 - t / 2) = u * (TwoStep.h1 a b * a) := by
        rw [ht, ha, hb]; unfold TwoStep.h1
        field_simp; ring
      rw [e1, e2, ENNReal.ofReal_add hv.le (mul_nonneg hu.le hB), add_smul]
      abel

end pair

lemma map_reflT_marg {m : ℕ} (K : Measure (Fin m → ℝ)) (i : Fin m) :
    (K.map reflT).map (fun x => x i) = (K.map (fun x => x i)).map (fun y => 2 - y) := by
  rw [Measure.map_map (measurable_pi_apply i) measurable_reflT,
    Measure.map_map (g := fun y : ℝ => 2 - y) (f := fun x : Fin m → ℝ => x i) (by fun_prop)
      (measurable_pi_apply i)]
  rfl

lemma unifI02_refl : (unifI 0 2).map (fun y => 2 - y) = unifI 0 2 := by
  have := unifI_map_decr (zero_lt_two : (0 : ℝ) < 2) 2 1 one_pos
  simp only [one_mul, sub_zero, sub_self] at this
  exact this

lemma sum_reflT {m : ℕ} (x : Fin m → ℝ) : ∑ i, reflT x i = 2 * m - ∑ i, x i := by
  simp only [reflT, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- The pair lemma of Proposition `as:prop:three`: for `0 < u`, `0 < v`, `u + v ≤ m` and
`min(u, v) ≤ m - 2`, the two kernels give complete mixes with sums `m - u` and `m + v` whose
marginals `P_-`, `P_+` satisfy `v P_- + u P_+ = (u + v) U[0, 2]`. -/
lemma pair_spec {m : ℕ} (hm : 3 ≤ m) {Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)} [IsMarkovKernel Kg]
    (hK : ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ m →
      (∀ i, (Kg (a, b)).map (fun x => x i) =
        volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g a b x))) ∧
      ∀ᵐ x ∂(Kg (a, b)), ∑ i, x i = (m : ℝ))
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u + v ≤ m) (hmin : v ≤ m - 2 ∨ u ≤ m - 2) :
    (∀ᵐ x ∂(Pm m Kg (u, v)), ∑ i, x i = m - u) ∧ (∀ᵐ x ∂(Pp m Kg (u, v)), ∑ i, x i = m + v) ∧
    ∀ i, ENNReal.ofReal v • (Pm m Kg (u, v)).map (fun x => x i) +
      ENNReal.ofReal u • (Pp m Kg (u, v)).map (fun x => x i) =
        ENNReal.ofReal (u + v) • unifI 0 2 := by
  classical
  by_cases hv2 : v ≤ m - 2
  · have hs : (u, v) ∈ {p : ℝ × ℝ | p.2 ≤ m - 2} := hv2
    rw [Pm, Pp, Kernel.piecewise_apply, Kernel.piecewise_apply, if_pos hs, if_pos hs]
    exact caseI hm hK hu hv hv2 huv
  · have hu2 : u ≤ m - 2 := hmin.resolve_left hv2
    have hs : (u, v) ∉ {p : ℝ × ℝ | p.2 ≤ m - 2} := hv2
    rw [Pm, Pp, Kernel.piecewise_apply, Kernel.piecewise_apply, if_neg hs, if_neg hs,
      Kernel.map_apply _ measurable_reflT, Kernel.map_apply _ measurable_reflT,
      Kernel.comap_apply, Kernel.comap_apply]
    simp only [Prod.swap_prod_mk]
    obtain ⟨h1, h2, h3⟩ := caseI hm hK hv hu hu2 (by linarith)
    have hS : ∀ c : ℝ, MeasurableSet {x : Fin m → ℝ | ∑ i, x i = c} :=
      fun c => measurableSet_eq_fun measurable_sum_coord measurable_const
    refine ⟨?_, ?_, fun i => ?_⟩
    · rw [ae_map_iff measurable_reflT.aemeasurable (hS ((m : ℝ) - u))]
      filter_upwards [h2] with x hx
      rw [sum_reflT, hx]; ring
    · rw [ae_map_iff measurable_reflT.aemeasurable (hS ((m : ℝ) + v))]
      filter_upwards [h1] with x hx
      rw [sum_reflT, hx]; ring
    · have hr : Measurable (fun y : ℝ => 2 - y) := by fun_prop
      rw [map_reflT_marg, map_reflT_marg]
      have : ENNReal.ofReal v • ((KpI m Kg (v, u)).map (fun x => x i)).map (fun y => 2 - y) +
          ENNReal.ofReal u • ((KmI m (v, u)).map (fun x => x i)).map (fun y => 2 - y) =
          (ENNReal.ofReal u • (KmI m (v, u)).map (fun x => x i) +
            ENNReal.ofReal v • (KpI m Kg (v, u)).map (fun x => x i)).map (fun y => 2 - y) := by
        rw [Measure.map_add _ _ hr, Measure.map_smul _ hr.aemeasurable,
          Measure.map_smul _ hr.aemeasurable, add_comm]
      rw [this, h3 i, Measure.map_smul _ hr.aemeasurable, unifI02_refl, add_comm v u]

lemma map_eq_dirac_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {c : ℝ} (h : ∀ᵐ x ∂μ, f x = c) : μ.map f = Measure.dirac c := by
  rw [Measure.map_congr h, Measure.map_const, measure_univ, one_smul]

lemma measure_preimage_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {c : ℝ} (h : ∀ᵐ x ∂μ, f x = c)
    {s : Set ℝ} (hs : MeasurableSet s) : μ (f ⁻¹' s) = s.indicator 1 c := by
  rw [← Measure.map_apply hf hs, map_eq_dirac_of_ae hf h, Measure.dirac_apply' _ hs]

lemma Pm_isMarkov {m : ℕ} (hm : 3 ≤ m) (Kg : Kernel (ℝ × ℝ) (Fin m → ℝ)) [IsMarkovKernel Kg] :
    IsMarkovKernel (Pm m Kg) ∧ IsMarkovKernel (Pp m Kg) := by
  have hU := unifKernel_isMarkov (m := m) (by omega)
  have h1 : IsMarkovKernel (KmI m) := by unfold KmI; infer_instance
  have h2 : IsMarkovKernel (KpU m) := by unfold KpU; infer_instance
  have h3 : IsMarkovKernel (KpG m Kg) := paramMap_isMarkov _ (measurable_KpGPsi m)
  have h4 : IsMarkovKernel (KpI m Kg) := by unfold KpI; infer_instance
  have h5 : IsMarkovKernel (((KpI m Kg).comap Prod.swap measurable_swap).map reflT) :=
    Kernel.IsMarkovKernel.map _ measurable_reflT
  have h6 : IsMarkovKernel (((KmI m).comap Prod.swap measurable_swap).map reflT) :=
    Kernel.IsMarkovKernel.map _ measurable_reflT
  constructor
  · unfold Pm; infer_instance
  · unfold Pp; infer_instance

lemma lintegral_ofReal_ne_top {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ᵐ t ∂ν, f t ≤ C) : ∫⁻ t, ENNReal.ofReal (f t) ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae (h.mono fun t ht => ENNReal.ofReal_le_ofReal ht))
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- The core of Proposition `as:prop:three`, normalised to `U[0, 2]` (`c = H = 1`): a probability
measure with mean `m` carried by `[m - u₀, m + v₀]`, where all pairs `0 < u ≤ u₀`, `0 < v ≤ v₀`
satisfy `u + v ≤ m` and `min(u, v) ≤ m - 2`, lies in `𝒜_m(U[0, 2])`. -/
theorem three_core (hTS : H_twoStepBorel) {m : ℕ} (hm : 3 ≤ m) {u0 v0 : ℝ}
    (hok : ∀ u v : ℝ, 0 < u → u ≤ u0 → 0 < v → v ≤ v0 → u + v ≤ m ∧ (v ≤ m - 2 ∨ u ≤ m - 2))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ x, x ∂ν = m)
    (hsupp : ν (Icc (m - u0) (m + v0))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin m => unifI 0 2) := by
  classical
  obtain ⟨Kg, hKgM, hK⟩ := hTS m hm
  obtain ⟨hPmM, hPpM⟩ := Pm_isMarkov hm Kg
  have hm2 : 2 ≤ m := by omega
  have hUM := unifKernel_isMarkov hm2
  set M0 := unifKernel m (0, 2) with hM0
  have hM0marg : ∀ i, M0.map (fun x => x i) = unifI 0 2 := fun i => unifKernel_marg hm2 two_pos i
  have hM0sum : ∀ᵐ x ∂M0, ∑ i, x i = (m : ℝ) := by
    filter_upwards [unifKernel_sum hm2 0 2] with x hx; rw [hx]; ring
  have hae := ae_mem_of_null hsupp
  have hint : Integrable (fun t => t) ν := integrable_id_of_null hsupp
  set κ := ∫⁻ t, ENNReal.ofReal (t - m) ∂ν with hκdef
  have hfin1 : κ ≠ ⊤ := lintegral_ofReal_ne_top (hae.mono fun t ht => by
    show t - m ≤ v0; linarith [ht.2])
  have hκ' : ∫⁻ t, ENNReal.ofReal (m - t) ∂ν = κ := by
    have h0 : ∫ t, (t - m) ∂ν = 0 := by
      have e : ∫ t, (t - m) ∂ν = ∫ t, t ∂ν - ∫ _t, (m : ℝ) ∂ν :=
        integral_sub hint (integrable_const _)
      rw [e, hmean]; simp
    have hI : Integrable (fun t => t - (m : ℝ)) ν := hint.sub (integrable_const _)
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI] at h0
    have hfin2 : ∫⁻ t, ENNReal.ofReal (-(t - m)) ∂ν ≠ ⊤ := lintegral_ofReal_ne_top
      (hae.mono fun t ht => by show -(t - m) ≤ u0; linarith [ht.1])
    have := (ENNReal.toReal_eq_toReal_iff' hfin2 hfin1).mp (by linarith)
    simpa [neg_sub] using this
  by_cases hκ0 : κ = 0
  · have h1 : ∀ᵐ t ∂ν, t ≤ (m : ℝ) := by
      have := (lintegral_eq_zero_iff (by fun_prop)).mp hκ0
      filter_upwards [this] with t ht
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht; linarith
    have h2 : ∀ᵐ t ∂ν, (m : ℝ) ≤ t := by
      have := (lintegral_eq_zero_iff (by fun_prop)).mp (hκ'.trans hκ0)
      filter_upwards [this] with t ht
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht; linarith
    have hν : ν = Measure.dirac (m : ℝ) := by
      apply eq_dirac_of_null
      have : ∀ᵐ t ∂ν, t ∈ ({(m : ℝ)} : Set ℝ) := by
        filter_upwards [h1, h2] with t a b; exact le_antisymm a b
      exact ae_iff.mp this
    refine ⟨M0, inferInstance, fun _ => hM0marg _, ?_⟩
    rw [hν]; exact map_eq_dirac_of_ae measurable_sum_coord hM0sum
  -- the laws of the negative and of the positive deviation
  set lamN : Measure ℝ := (ν.restrict (Iio (m : ℝ))).map (fun t => m - t) with hlamN
  set lamP : Measure ℝ := (ν.restrict (Ioi (m : ℝ))).map (fun t => t - m) with hlamP
  have hIn : ∫⁻ x, ENNReal.ofReal x ∂lamN = κ := by
    rw [hlamN, lintegral_map (by fun_prop) (by fun_prop), setLIntegral_eq_of_support_subset, hκ']
    intro t ht
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at ht
    exact sub_pos.mp ht
  have hIp : ∫⁻ x, ENNReal.ofReal x ∂lamP = κ := by
    rw [hlamP, lintegral_map (by fun_prop) (by fun_prop), setLIntegral_eq_of_support_subset]
    intro t ht
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at ht
    exact sub_pos.mp ht
  have hlamN_univ : lamN univ = ν (Iio (m : ℝ)) := by
    rw [hlamN, Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hlamP_univ : lamP univ = ν (Ioi (m : ℝ)) := by
    rw [hlamP, Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have htot : ν (Iio (m : ℝ)) + ν {(m : ℝ)} + ν (Ioi (m : ℝ)) = 1 := by
    rw [← measure_union (Set.disjoint_singleton_right.mpr (by simp))
      (measurableSet_singleton _), Set.Iio_union_right,
      ← measure_union (Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx hx') measurableSet_Ioi,
      Set.Iic_union_Ioi, measure_univ]
  set PiM := lamN.prod lamP with hPi
  have hn_ae : ∀ᵐ x ∂lamN, 0 < x ∧ x ≤ u0 := by
    rw [hlamN]
    refine (ae_map_iff (Measurable.aemeasurable (by fun_prop)) (p := fun x => 0 < x ∧ x ≤ u0)
      measurableSet_Ioc).mpr ?_
    rw [ae_restrict_iff' measurableSet_Iio]
    filter_upwards [hae] with t ht htm
    exact ⟨by simp only [mem_Iio] at htm; linarith, by linarith [ht.1]⟩
  have hp_ae : ∀ᵐ x ∂lamP, 0 < x ∧ x ≤ v0 := by
    rw [hlamP]
    refine (ae_map_iff (Measurable.aemeasurable (by fun_prop)) (p := fun x => 0 < x ∧ x ≤ v0)
      measurableSet_Ioc).mpr ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with t ht htm
    exact ⟨by simp only [mem_Ioi] at htm; linarith, by linarith [ht.2]⟩
  have hPi_ae : ∀ᵐ p ∂PiM, (0 < p.1 ∧ p.1 ≤ u0) ∧ (0 < p.2 ∧ p.2 ≤ v0) := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := lamN) (ν := lamP)).ae hn_ae
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := lamN) (ν := lamP)).ae hp_ae
    filter_upwards [h1, h2] with p a b
    exact ⟨a, b⟩
  set fm : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.2 / κ with hfmdef
  set fp : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 / κ with hfpdef
  have hfm : Measurable fm := (ENNReal.measurable_ofReal.comp measurable_snd).div_const κ
  have hfp : Measurable fp := (ENNReal.measurable_ofReal.comp measurable_fst).div_const κ
  have hJ1 : ∀ g : ℝ → ℝ≥0∞, Measurable g → ∫⁻ p, fm p * g p.1 ∂PiM = ∫⁻ x, g x ∂lamN := by
    intro g hg
    have : (fun p : ℝ × ℝ => fm p * g p.1) = fun p => g p.1 * (ENNReal.ofReal p.2 * κ⁻¹) := by
      funext p; simp only [hfmdef, div_eq_mul_inv]; ring
    rw [this, hPi, lintegral_prod_mul (f := g) (g := fun y => ENNReal.ofReal y * κ⁻¹)
      hg.aemeasurable (by fun_prop),
      lintegral_mul_const _ ENNReal.measurable_ofReal, hIp, ENNReal.mul_inv_cancel hκ0 hfin1,
      mul_one]
  have hJ2 : ∀ g : ℝ → ℝ≥0∞, Measurable g → ∫⁻ p, fp p * g p.2 ∂PiM = ∫⁻ y, g y ∂lamP := by
    intro g hg
    have : (fun p : ℝ × ℝ => fp p * g p.2) = fun p => (ENNReal.ofReal p.1 * κ⁻¹) * g p.2 := by
      funext p; simp only [hfpdef, div_eq_mul_inv]
    rw [this, hPi, lintegral_prod_mul (f := fun x => ENNReal.ofReal x * κ⁻¹) (g := g)
      (by fun_prop) hg.aemeasurable,
      lintegral_mul_const _ ENNReal.measurable_ofReal, hIn, ENNReal.mul_inv_cancel hκ0 hfin1,
      one_mul]
  set P : Measure (Fin m → ℝ) := ν {(m : ℝ)} • M0 + (PiM.withDensity fm).bind (Pm m Kg) +
    (PiM.withDensity fp).bind (Pp m Kg) with hPdef
  have hPapply : ∀ s, MeasurableSet s → P s = ν {(m : ℝ)} * M0 s +
      ∫⁻ p, fm p * Pm m Kg p s ∂PiM + ∫⁻ p, fp p * Pp m Kg p s ∂PiM := by
    intro s hs
    simp only [hPdef, Measure.add_apply, smul_apply, smul_eq_mul]
    rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_withDensity_eq_lintegral_mul _ hfm (Kernel.measurable_coe _ hs),
      lintegral_withDensity_eq_lintegral_mul _ hfp (Kernel.measurable_coe _ hs)]
    rfl
  -- the sum
  have hsum : P.map (fun x => ∑ i, x i) = ν := by
    refine Measure.ext fun s hs => ?_
    have hpre := measurable_sum_coord (ι := Fin m) hs
    rw [Measure.map_apply measurable_sum_coord hs, hPapply _ hpre,
      measure_preimage_of_ae measurable_sum_coord hM0sum hs]
    have hkm : ∀ᵐ p ∂PiM, fm p * Pm m Kg p ((fun x : Fin m → ℝ => ∑ i, x i) ⁻¹' s) =
        fm p * s.indicator 1 (m - p.1) := by
      filter_upwards [hPi_ae] with p hp
      obtain ⟨u, v⟩ := p
      obtain ⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩ := hp
      obtain ⟨huv, hmin⟩ := hok u v hu hu0 hv hv0
      rw [measure_preimage_of_ae measurable_sum_coord (pair_spec hm hK hu hv huv hmin).1 hs]
    have hkp : ∀ᵐ p ∂PiM, fp p * Pp m Kg p ((fun x : Fin m → ℝ => ∑ i, x i) ⁻¹' s) =
        fp p * s.indicator 1 (m + p.2) := by
      filter_upwards [hPi_ae] with p hp
      obtain ⟨u, v⟩ := p
      obtain ⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩ := hp
      obtain ⟨huv, hmin⟩ := hok u v hu hu0 hv hv0
      rw [measure_preimage_of_ae measurable_sum_coord (pair_spec hm hK hu hv huv hmin).2.1 hs]
    have hgm : Measurable (fun x : ℝ => s.indicator (1 : ℝ → ℝ≥0∞) (m - x)) :=
      (measurable_const.indicator hs).comp (by fun_prop)
    have hgp : Measurable (fun y : ℝ => s.indicator (1 : ℝ → ℝ≥0∞) (m + y)) :=
      (measurable_const.indicator hs).comp (by fun_prop)
    rw [lintegral_congr_ae hkm, lintegral_congr_ae hkp, hJ1 _ hgm, hJ2 _ hgp]
    have e1 : ∫⁻ x, s.indicator (1 : ℝ → ℝ≥0∞) (m - x) ∂lamN = ν (s ∩ Iio (m : ℝ)) := by
      rw [hlamN, lintegral_map hgm (by fun_prop)]
      simp only [sub_sub_cancel]
      rw [lintegral_indicator_one hs, Measure.restrict_apply hs]
    have e2 : ∫⁻ y, s.indicator (1 : ℝ → ℝ≥0∞) (m + y) ∂lamP = ν (s ∩ Ioi (m : ℝ)) := by
      rw [hlamP, lintegral_map hgp (by fun_prop)]
      simp only [add_sub_cancel]
      rw [lintegral_indicator_one hs, Measure.restrict_apply hs]
    have e0 : ν {(m : ℝ)} * s.indicator 1 (m : ℝ) = ν (s ∩ {(m : ℝ)}) := by
      by_cases hms : (m : ℝ) ∈ s
      · rw [Set.indicator_of_mem hms, Pi.one_apply, mul_one, Set.inter_eq_right.mpr
          (Set.singleton_subset_iff.mpr hms)]
      · rw [Set.indicator_of_notMem hms, mul_zero, Set.inter_singleton_eq_empty.mpr hms,
          measure_empty]
    rw [e0, e1, e2]
    have d1 := measure_inter_add_diff s (measurableSet_Iio (a := (m : ℝ))) (μ := ν)
    have d2 := measure_inter_add_diff (s \ Iio (m : ℝ)) (measurableSet_singleton (m : ℝ)) (μ := ν)
    have s1 : (s \ Iio (m : ℝ)) ∩ ({(m : ℝ)} : Set ℝ) = s ∩ ({(m : ℝ)} : Set ℝ) := by
      ext x; simp only [mem_inter_iff, mem_diff, mem_Iio, mem_singleton_iff, not_lt]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, rfl⟩; exact ⟨⟨h1, le_rfl⟩, rfl⟩
    have s2 : (s \ Iio (m : ℝ)) \ ({(m : ℝ)} : Set ℝ) = s ∩ Ioi (m : ℝ) := by
      ext x; simp only [mem_inter_iff, mem_diff, mem_Iio, mem_singleton_iff, not_lt, mem_Ioi]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 (Ne.symm h3)⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2.ne'⟩
    rw [s1, s2] at d2
    rw [← d1, ← d2]
    ring
  have hP : IsProbabilityMeasure P := by
    constructor
    have := congrArg (fun μ : Measure ℝ => μ univ) hsum
    simp only [Measure.map_apply measurable_sum_coord MeasurableSet.univ, Set.preimage_univ,
      measure_univ] at this
    exact this
  refine ⟨P, hP, fun i => ?_, hsum⟩
  -- the marginals
  refine Measure.ext fun s hs => ?_
  have hpre : MeasurableSet ((fun x : Fin m → ℝ => x i) ⁻¹' s) := measurable_pi_apply i hs
  rw [Measure.map_apply (measurable_pi_apply i) hs, hPapply _ hpre]
  have hM : M0 ((fun x : Fin m → ℝ => x i) ⁻¹' s) = unifI 0 2 s := by
    rw [← Measure.map_apply (measurable_pi_apply i) hs, hM0marg]
  have hkey : ∀ᵐ p ∂PiM, fm p * Pm m Kg p ((fun x : Fin m → ℝ => x i) ⁻¹' s) +
      fp p * Pp m Kg p ((fun x : Fin m → ℝ => x i) ⁻¹' s) = (fm p + fp p) * unifI 0 2 s := by
    filter_upwards [hPi_ae] with p hp
    obtain ⟨u, v⟩ := p
    obtain ⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩ := hp
    obtain ⟨huv, hmin⟩ := hok u v hu hu0 hv hv0
    have h3 := congrArg (fun μ : Measure ℝ => μ s) ((pair_spec hm hK hu hv huv hmin).2.2 i)
    simp only [Measure.add_apply, smul_apply, smul_eq_mul,
      Measure.map_apply (f := fun x : Fin m → ℝ => x i) (measurable_pi_apply i) hs] at h3
    rw [ENNReal.ofReal_add hu.le hv.le] at h3
    simp only [hfmdef, hfpdef, div_eq_mul_inv]
    calc ENNReal.ofReal v * κ⁻¹ * Pm m Kg (u, v) ((fun x : Fin m → ℝ => x i) ⁻¹' s) +
          ENNReal.ofReal u * κ⁻¹ * Pp m Kg (u, v) ((fun x : Fin m → ℝ => x i) ⁻¹' s)
        = (ENNReal.ofReal v * Pm m Kg (u, v) ((fun x : Fin m → ℝ => x i) ⁻¹' s) +
          ENNReal.ofReal u * Pp m Kg (u, v) ((fun x : Fin m → ℝ => x i) ⁻¹' s)) * κ⁻¹ := by ring
      _ = ((ENNReal.ofReal u + ENNReal.ofReal v) * unifI 0 2 s) * κ⁻¹ := by rw [h3]
      _ = (ENNReal.ofReal v * κ⁻¹ + ENNReal.ofReal u * κ⁻¹) * unifI 0 2 s := by ring
  have hsumf : ∫⁻ p, (fm p + fp p) ∂PiM = ν (Iio (m : ℝ)) + ν (Ioi (m : ℝ)) := by
    rw [lintegral_add_left hfm]
    have a1 := hJ1 (fun _ => 1) measurable_const
    have a2 := hJ2 (fun _ => 1) measurable_const
    simp only [mul_one, lintegral_one] at a1 a2
    rw [a1, a2, hlamN_univ, hlamP_univ]
  beta_reduce
  rw [add_assoc, ← lintegral_add_left
    (f := fun p => fm p * Pm m Kg p ((fun x : Fin m → ℝ => x i) ⁻¹' s))
    (hfm.mul (Kernel.measurable_coe _ hpre)),
    lintegral_congr_ae hkey, lintegral_mul_const (f := fun p => fm p + fp p) _ (hfm.add hfp),
    hsumf, hM]
  calc ν {(m : ℝ)} * unifI 0 2 s + (ν (Iio (m : ℝ)) + ν (Ioi (m : ℝ))) * unifI 0 2 s
      = (ν (Iio (m : ℝ)) + ν {(m : ℝ)} + ν (Ioi (m : ℝ))) * unifI 0 2 s := by ring
    _ = unifI 0 2 s := by rw [htot, one_mul]

/-! ### Proposition `as:prop:three` -/

/-- Affine images of aggregation sets with equal marginals. -/
lemma aggSet_map_affine {m : ℕ} (μ : Measure ℝ) (p d : ℝ) {ν : Measure ℝ}
    (hν : ν ∈ aggSet (fun _ : Fin m => μ)) :
    ν.map (fun t => m * p + d * t) ∈ aggSet (fun _ : Fin m => μ.map (fun x => p + d * x)) := by
  obtain ⟨P, hP, hmarg, hsum⟩ := hν
  haveI := hP
  have hT : Measurable (fun x : Fin m → ℝ => fun i => p + d * x i) :=
    by fun_prop
  refine ⟨P.map (fun x i => p + d * x i), inferInstance, fun i => ?_, ?_⟩
  · have hmi : P.map (fun x => x i) = μ := hmarg i
    show _ = μ.map (fun x => p + d * x)
    rw [Measure.map_map (measurable_pi_apply i) hT, ← hmi,
      Measure.map_map (g := fun x => p + d * x) (by fun_prop) (measurable_pi_apply i)]
    rfl
  · rw [Measure.map_map measurable_sum_coord hT, ← hsum,
      Measure.map_map (g := fun t => (m : ℝ) * p + d * t) (by fun_prop) measurable_sum_coord]
    congr 1
    funext x
    show ∑ i, (p + d * x i) = (m : ℝ) * p + d * ∑ i, x i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp

/-- Proposition `as:prop:three` for a general pair of bounds `u₀, v₀` (in units of `H`). -/
theorem three_scaled (hTS : H_twoStepBorel) {m : ℕ} (hm : 3 ≤ m) {c H : ℝ} (hH : 0 < H)
    {u0 v0 : ℝ}
    (hok : ∀ u v : ℝ, 0 < u → u ≤ u0 → 0 < v → v ≤ v0 → u + v ≤ m ∧ (v ≤ m - 2 ∨ u ≤ m - 2))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ x, x ∂ν = m * c)
    (hsupp : ν (Icc (m * c - H * u0) (m * c + H * v0))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin m => unifI (c - H) (c + H)) := by
  set p : ℝ := -(H⁻¹ * (m * (c - H))) with hp
  have hf : Measurable (fun t : ℝ => p + H⁻¹ * t) := by fun_prop
  set ν' := ν.map (fun t : ℝ => p + H⁻¹ * t) with hν'
  have hint := integrable_id_of_null hsupp
  have hmean' : ∫ x, x ∂ν' = m := by
    rw [hν', integral_id_map hf, integral_affine hint, hmean, hp]
    field_simp; ring
  have hsupp' : ν' (Icc (m - u0) (m + v0))ᶜ = 0 := by
    apply map_null_of_ae hf measurableSet_Icc
    filter_upwards [ae_mem_of_null hsupp] with t ht
    have e1 : p + H⁻¹ * t = (m - u0) + H⁻¹ * (t - (m * c - H * u0)) := by
      rw [hp]; field_simp; ring
    have e2 : p + H⁻¹ * t = (m + v0) - H⁻¹ * ((m * c + H * v0) - t) := by
      rw [hp]; field_simp; ring
    have hHi : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
    constructor
    · rw [e1]; nlinarith [mul_nonneg hHi (sub_nonneg.mpr ht.1)]
    · rw [e2]; nlinarith [mul_nonneg hHi (sub_nonneg.mpr ht.2)]
  have h0 := three_core hTS hm hok ν' hmean' hsupp'
  have h1 := aggSet_map_affine (m := m) (unifI 0 2) (c - H) H h0
  have hU : (unifI 0 2).map (fun x => (c - H) + H * x) = unifI (c - H) (c + H) := by
    rw [unifI_map_incr (by norm_num : (0 : ℝ) < 2) _ _ hH]
    congr 1 <;> ring
  have hback : ν'.map (fun t => (m : ℝ) * (c - H) + H * t) = ν := by
    rw [hν', Measure.map_map (by fun_prop) hf]
    conv_rhs => rw [← Measure.map_id (μ := ν)]
    congr 1
    funext t
    simp only [Function.comp_apply, id, hp]
    field_simp; ring
  rw [hU, hback] at h1
  exact h1

lemma three_pairs {m : ℕ} {u0 v0 : ℝ} (h1 : u0 + v0 ≤ m) (h2 : u0 + v0 ≤ 2 * m - 4) :
    ∀ u v : ℝ, 0 < u → u ≤ u0 → 0 < v → v ≤ v0 → u + v ≤ m ∧ (v ≤ m - 2 ∨ u ≤ m - 2) := by
  intro u v _ hu0 _ hv0
  refine ⟨by linarith, ?_⟩
  by_contra h
  push Not at h
  linarith [h.1, h.2]

/-- **Proposition `as:prop:three`**, under the hypothesis `H_twoStepBorel` (Borel dependence of
the mixes of Theorem `m:thm:two` on the parameters). -/
theorem prop_three (hTS : H_twoStepBorel) : PropThree := by
  refine ⟨fun m c H ν hm hH hν hmean a ha1 ha2 hsupp => ?_, fun c H ν hH hν hmean hsupp => ?_⟩
  · haveI := hν
    have hL : lenThree m H / H ≤ m ∧ lenThree m H / H ≤ 2 * m - 4 := by
      unfold lenThree
      have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
      split_ifs with h4
      · have : (4 : ℝ) ≤ m := by exact_mod_cast h4
        rw [mul_div_assoc, div_self hH.ne', mul_one]; constructor <;> linarith
      · rw [mul_div_assoc, div_self hH.ne', mul_one]; constructor <;> linarith
    apply three_scaled hTS hm hH (u0 := (m * c - a) / H) (v0 := (a + lenThree m H - m * c) / H)
      (three_pairs (by rw [← add_div]; convert hL.1 using 2; ring)
        (by rw [← add_div]; convert hL.2 using 2; ring)) ν hmean
    convert hsupp using 4
    · field_simp; ring
    · field_simp; ring
  · haveI := hν
    have hm3 : (3 : ℕ) ≤ 3 := le_rfl
    rcases hsupp with hs | hs
    · apply three_scaled hTS hm3 hH (u0 := 1) (v0 := 2)
        (fun u v _ hu0 _ hv0 => ⟨by norm_num; linarith, Or.inr (by norm_num; linarith)⟩) ν
        (by rw [hmean]; norm_num)
      convert hs using 4 <;> norm_num <;> ring
    · apply three_scaled hTS hm3 hH (u0 := 2) (v0 := 1)
        (fun u v _ hu0 _ hv0 => ⟨by norm_num; linarith, Or.inl (by norm_num; linarith)⟩) ν
        (by rw [hmean]; norm_num)
      convert hs using 4 <;> norm_num <;> ring

/-! ### Corollary `as:cor:repeat`: reindexing and splitting pairs -/

lemma aggSet_assoc {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] {A : α → Measure ℝ}
    {B : β → Measure ℝ} {C : ι → Measure ℝ} {ν : Measure ℝ}
    (h : ν ∈ aggSet (Sum.elim A (Sum.elim B C))) : ν ∈ aggSet (Sum.elim (Sum.elim A B) C) :=
  aggSet_reindex' (Equiv.sumAssoc α β ι).symm (by rintro (a | b | c) <;> rfl) h

lemma aggSet_assoc' {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] {A : α → Measure ℝ}
    {B : β → Measure ℝ} {C : ι → Measure ℝ} {ν : Measure ℝ}
    (h : ν ∈ aggSet (Sum.elim (Sum.elim A B) C)) : ν ∈ aggSet (Sum.elim A (Sum.elim B C)) :=
  aggSet_reindex' (Equiv.sumAssoc α β ι) (by rintro ((a | b) | c) <;> rfl) h

lemma aggSet_comm_left {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] {A : α → Measure ℝ}
    {B : β → Measure ℝ} {C : ι → Measure ℝ} {ν : Measure ℝ}
    (h : ν ∈ aggSet (Sum.elim A (Sum.elim B C))) : ν ∈ aggSet (Sum.elim B (Sum.elim A C)) := by
  have h1 := aggSet_assoc h
  have h2 : ν ∈ aggSet (Sum.elim (Sum.elim B A) C) :=
    aggSet_reindex' (Equiv.sumCongr (Equiv.sumComm α β) (Equiv.refl ι))
      (by rintro ((a | b) | c) <;> rfl) h1
  exact aggSet_assoc' h2

lemma aggSet_const_block {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (h : Fintype.card α = Fintype.card β) (G : Measure ℝ) (C : ι → Measure ℝ) {ν : Measure ℝ}
    (hν : ν ∈ aggSet (Sum.elim (fun _ : α => G) C)) : ν ∈ aggSet (Sum.elim (fun _ : β => G) C) :=
  aggSet_reindex' (Equiv.sumCongr (Fintype.equivOfCardEq h) (Equiv.refl ι))
    (by rintro (a | c) <;> rfl) hν

lemma sum_elim_const {α β ι : Type*} (G : Measure ℝ) (C : ι → Measure ℝ) :
    Sum.elim (Sum.elim (fun _ : α => G) (fun _ : β => G)) C = Sum.elim (fun _ : α ⊕ β => G) C := by
  funext x; rcases x with ((a | b) | c) <;> rfl

/-- One distribution of a family is replaced by distributions whose aggregation set contains it. -/
lemma aggSet_refine_one {κ ι : Type*} [Fintype κ] [Fintype ι] {C : Measure ℝ}
    {D : κ → Measure ℝ} {B : ι → Measure ℝ} (hC : C ∈ aggSet D) {ν : Measure ℝ}
    (h : ν ∈ aggSet (Sum.elim (fun _ : Unit => C) B)) : ν ∈ aggSet (Sum.elim D B) := by
  obtain ⟨P, hP, hm, rfl⟩ := h
  haveI := hP
  have hY : Measurable (fun x : Unit ⊕ ι → ℝ => fun i => x (Sum.inr i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  refine absorb P (Y := fun x : Unit ⊕ ι → ℝ => fun i => x (Sum.inr i))
    (Z := fun x => ∑ i, x i) hY measurable_sum_coord (A := B) (B := D)
    (fun i => hm (Sum.inr i)) ?_
  have e : (fun x : Unit ⊕ ι → ℝ => ∑ i, x i - ∑ i, x (Sum.inr i)) =
      fun x => x (Sum.inl ()) := by
    funext x; rw [Fintype.sum_sum_type]; simp
  rw [e, hm (Sum.inl ())]
  exact hC

instance isProb_conv (G : Measure ℝ) [IsProbabilityMeasure G] : IsProbabilityMeasure (G ∗ G) := by
  unfold Measure.conv; infer_instance

lemma conv_mem_aggSet (G : Measure ℝ) [IsProbabilityMeasure G] :
    G ∗ G ∈ aggSet (fun _ : Fin 2 => G) := by
  have hme : Measurable (fun p : ℝ × ℝ => ![p.1, p.2]) := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd
  refine ⟨(G.prod G).map (fun p => ![p.1, p.2]), inferInstance, fun i => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hme]
    fin_cases i
    · exact Measure.fst_prod
    · exact Measure.snd_prod
  · rw [Measure.map_map measurable_sum_coord hme]
    unfold Measure.conv
    congr 1
    funext p
    simp [Fin.sum_univ_two]

lemma integral_conv (G : Measure ℝ) [IsProbabilityMeasure G] {a b : ℝ} (hG : G (Icc a b)ᶜ = 0) :
    ∫ x, x ∂(G ∗ G) = 2 * ∫ x, x ∂G := by
  have hi := integrable_id_of_null hG
  have h1 : ∫ p : ℝ × ℝ, p.1 ∂(G.prod G) = ∫ x, x ∂G := by
    rw [← integral_id_map measurable_fst]
    change ∫ x, x ∂((G.prod G).fst) = _
    rw [Measure.fst_prod]
  have h2 : ∫ p : ℝ × ℝ, p.2 ∂(G.prod G) = ∫ x, x ∂G := by
    rw [← integral_id_map measurable_snd]
    change ∫ x, x ∂((G.prod G).snd) = _
    rw [Measure.snd_prod]
  unfold Measure.conv
  rw [integral_id_map (by fun_prop), integral_add (hi.comp_fst G) (hi.comp_snd G), h1, h2]
  ring

lemma conv_null (G : Measure ℝ) [IsProbabilityMeasure G] {a b : ℝ} (hG : G (Icc a b)ᶜ = 0) :
    (G ∗ G) (Icc (2 * a) (2 * b))ᶜ = 0 := by
  unfold Measure.conv
  apply map_null_of_ae (by fun_prop) measurableSet_Icc
  have hae := ae_mem_of_null hG
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := G) (ν := G)).ae hae
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := G) (ν := G)).ae hae
  filter_upwards [h1, h2] with p a1 a2
  exact ⟨by linarith [a1.1, a2.1], by linarith [a1.2, a2.2]⟩

/-- `n` copies of `G ∗ G` are replaced by `2 n` copies of `G`. -/
lemma split_pairs (G : Measure ℝ) [IsProbabilityMeasure G] : ∀ (n : ℕ) {ι : Type} [Fintype ι]
    (B : ι → Measure ℝ) (ν : Measure ℝ), ν ∈ aggSet (Sum.elim (fun _ : Fin n => G ∗ G) B) →
    ν ∈ aggSet (Sum.elim (fun _ : Fin (2 * n) => G) B) := by
  intro n
  induction n with
  | zero =>
    intro ι _ B ν h
    refine aggSet_reindex' (Equiv.sumCongr (Fintype.equivOfCardEq (by simp) : Fin 0 ≃ Fin (2 * 0))
      (Equiv.refl ι)) ?_ h
    rintro (a | c)
    · exact a.elim0
    · rfl
  | succ n ih =>
    intro ι _ B ν h
    have h1 := aggSet_const_block (β := Fin n ⊕ Unit) (by simp) (G ∗ G) B h
    have h2 : ν ∈ aggSet (Sum.elim (Sum.elim (fun _ : Fin n => G ∗ G) (fun _ : Unit => G ∗ G)) B) := by
      rw [sum_elim_const]; exact h1
    have h3 := aggSet_assoc' h2
    have h4 := ih (Sum.elim (fun _ : Unit => G ∗ G) B) ν h3
    have h5 := aggSet_comm_left h4
    have h6 := aggSet_refine_one (conv_mem_aggSet G) h5
    have h7 := aggSet_assoc h6
    rw [sum_elim_const] at h7
    exact aggSet_const_block (by simp; ring) G B h7

/-- The step of the proof of Theorem `as:thm:general` that Corollary `as:cor:repeat` uses: for a
probability measure `G` on a bounded interval whose absolutely continuous part is not zero, the
convolution `G ∗ G` dominates a positive multiple of a uniform distribution. (Classical: the
convolution of two nonzero integrable functions is continuous and not identically zero.) -/
def H_convSq : Prop :=
  ∀ G : Measure ℝ, IsProbabilityMeasure G → (∃ a b : ℝ, G (Icc a b)ᶜ = 0) →
    volume.withDensity (G.rnDeriv volume) ≠ 0 →
    ∃ c H q : ℝ, 0 < H ∧ 0 < q ∧ ENNReal.ofReal q • unifI (c - H) (c + H) ≤ G ∗ G

/-- **Corollary `as:cor:repeat`**: for `G` on a bounded interval with nonzero absolutely
continuous part and `L > 0` there are `N₀` and `κ > 0` such that for `N ≥ N₀` and every finite
family `F` of distributions on intervals of length at most `L`, the aggregation set of `N` copies
of `G` together with `F` contains every distribution with mean `s` carried by
`[s - κ N, s + κ N]`, where `s` is the sum of the means. -/
theorem cor_repeat (hW : H_window_line) (hC : H_conc_a) (hCS : H_convSq)
    (G : Measure ℝ) [IsProbabilityMeasure G] {a0 R : ℝ} (hG : G (Icc a0 (a0 + R))ᶜ = 0)
    (hac : volume.withDensity (G.rnDeriv volume) ≠ 0) {L : ℝ} (_hL : 0 < L) :
    ∃ N0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, N0 ≤ N → ∀ (r : ℕ) (F : Fin r → Measure ℝ)
      [∀ j, IsProbabilityMeasure (F j)], (∀ j, ∃ a, F j (Icc a (a + L))ᶜ = 0) →
      ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        ∫ x, x ∂ν = N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) →
        ν (Icc (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) - κ * N)
          (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) + κ * N))ᶜ = 0 →
        ν ∈ aggSet (Sum.elim (fun _ : Fin N => G) F) := by
  have hR : 0 ≤ R := by
    by_contra h
    push Not at h
    have : Icc a0 (a0 + R) = ∅ := Icc_eq_empty (by linarith)
    rw [this, compl_empty, measure_univ] at hG
    exact one_ne_zero hG
  obtain ⟨c, H, q0, hH, hq0, hGU0⟩ := hCS G inferInstance ⟨a0, a0 + R, hG⟩ hac
  set q := min q0 1 with hqdef
  have hq : 0 < q := lt_min hq0 one_pos
  have hq1 : q ≤ 1 := min_le_right _ _
  have hGU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ G ∗ G := by
    refine le_trans (Measure.le_iff'.mpr fun s => ?_) hGU0
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left _ _)) _
  set ℓ := max (2 * R) L with hℓ
  have hℓR : 2 * R ≤ ℓ := le_max_left _ _
  have hℓL : L ≤ ℓ := le_max_right _ _
  have hqH : 0 < q * H := mul_pos hq hH
  refine ⟨⌈2 + 8 / q + 8 * ℓ / (q * H)⌉₊ + 1, q * H / 8, by positivity, ?_⟩
  intro N hN r F hF hFL ν hν hνm hνs
  set N' := N / 2 with hN'
  set e := N % 2 with he
  have hNe : N = 2 * N' + e := (Nat.div_add_mod N 2).symm
  have he1 : e ≤ 1 := by omega
  set F' : Fin (e + r) → Measure ℝ := Fin.append (fun _ : Fin e => G) F with hF'def
  have hF'G : ∀ a : Fin e, F' (finSumFinEquiv (Sum.inl a)) = G := fun a => by
    simp [hF'def]
  have hF'F : ∀ b : Fin r, F' (finSumFinEquiv (Sum.inr b)) = F b := fun b => by
    simp [hF'def]
  haveI hF'P : ∀ j, IsProbabilityMeasure (F' j) := fun j => by
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    rcases k with a | b
    · rw [hF'G]; infer_instance
    · rw [hF'F]; infer_instance
  have hFℓ' : ∀ j, ∃ a, F' j (Icc a (a + ℓ))ᶜ = 0 := fun j => by
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    rcases k with a | b
    · rw [hF'G]
      exact ⟨a0, measure_mono_null (compl_subset_compl.mpr
        (Icc_subset_Icc le_rfl (by linarith))) hG⟩
    · rw [hF'F]
      obtain ⟨a, ha⟩ := hFL b
      exact ⟨a, measure_mono_null (compl_subset_compl.mpr
        (Icc_subset_Icc le_rfl (by linarith))) ha⟩
  have hGG : ∃ a, (G ∗ G) (Icc a (a + ℓ))ᶜ = 0 := by
    refine ⟨2 * a0, measure_mono_null (compl_subset_compl.mpr ?_) (conv_null G hG)⟩
    exact Icc_subset_Icc le_rfl (by linarith)
  -- arithmetic
  have hNr : (N : ℝ) = 2 * N' + e := by exact_mod_cast hNe
  have he1r : (e : ℝ) ≤ 1 := by exact_mod_cast he1
  have he0r : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hN0 : 2 + 8 / q + 8 * ℓ / (q * H) < N := by
    have h1 := Nat.le_ceil (2 + 8 / q + 8 * ℓ / (q * H))
    have h2 : ((⌈2 + 8 / q + 8 * ℓ / (q * H)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hN1 : 2 * (q * H) + 8 * H + 8 * ℓ < q * H * N := by
    have := mul_lt_mul_of_pos_left hN0 hqH
    have e2 : q * H * (2 + 8 / q + 8 * ℓ / (q * H)) = 2 * (q * H) + 8 * H + 8 * ℓ := by
      field_simp
    linarith
  have hN2 : 8 < q * ((N : ℝ) - 2) := by
    have h8 : 8 / q < (N : ℝ) - 2 := by
      have : 0 ≤ 8 * ℓ / (q * H) := by positivity
      linarith
    rw [div_lt_iff₀ hq] at h8
    linarith
  set m := ⌊q * N'⌋₊ with hm
  have hfl : q * N' < m + 1 := Nat.lt_floor_add_one _
  have hqN : q * ((N : ℝ) - 1) / 2 ≤ q * N' := by
    rw [hNr]; nlinarith
  have hm4 : 4 ≤ m := by
    have : (3 : ℝ) < m := by nlinarith
    have : 3 < m := by exact_mod_cast this
    omega
  have hmH : (q * ((N : ℝ) - 1) / 2 - 1) * H ≤ m * H := by
    apply mul_le_mul_of_nonneg_right _ hH.le
    linarith
  set s := (N : ℝ) * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) with hsdef
  set ρ := ∑ _k : Fin 1, (m : ℝ) * H / 2 - ℓ with hρdef
  have hρ' : ρ = m * H / 2 - ℓ := by rw [hρdef, Fin.sum_univ_one]
  have hκρ : q * H / 8 * N ≤ ρ := by rw [hρ']; nlinarith
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hκρ
  have hs : s = ∑ _k : Fin 1, (N' : ℝ) * ∫ x, x ∂(G ∗ G) + ∑ j, ∫ x, x ∂(F' j) := by
    rw [Fin.sum_univ_one, integral_conv G hG, Fin.sum_univ_add, hsdef]
    have h1 : ∀ a : Fin e, ∫ x, x ∂(F' (Fin.castAdd r a)) = ∫ x, x ∂G := fun a => by
      have := hF'G a; simp only [finSumFinEquiv_apply_left] at this; rw [this]
    have h2 : ∀ b : Fin r, ∫ x, x ∂(F' (Fin.natAdd e b)) = ∫ x, x ∂(F b) := fun b => by
      have := hF'F b; simp only [finSumFinEquiv_apply_right] at this; rw [this]
    simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hNr]; ring
  have hν' : ν (Icc (s - ρ) (s + ρ))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (Icc_subset_Icc (by linarith) (by linarith))) hνs
  have h0 := prop_complete hW hC (K := 1) (fun _ => G ∗ G) F' ℓ (fun _ => hGG) hFℓ'
    (fun _ => c) (fun _ => H) (fun _ => q) (fun _ => hH) (fun _ => hq) (fun _ => hq1)
    (fun _ => hGU) (fun _ => N') (fun _ => hm4) s ρ hs hρdef hρ0 ν hνm hν'
  have h1 := aggSet_const_block (β := Fin N') (by simp) (G ∗ G) F' h0
  have h2 : ν ∈ aggSet (Sum.elim (fun _ : Fin N' => G ∗ G) (Sum.elim (fun _ : Fin e => G) F)) := by
    refine aggSet_reindex' (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm) ?_ h1
    rintro (a | j)
    · rfl
    · obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
      rcases k with a | b
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply, Sum.elim_inr]
        rw [hF'G]; rfl
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply, Sum.elim_inr]
        rw [hF'F]
  have h3 := split_pairs G N' _ ν h2
  have h4 := aggSet_assoc h3
  rw [sum_elim_const] at h4
  exact aggSet_const_block (by simp; omega) G F h4

/-! ### Corollary `as:cor:three` and Remark `as:rem:three` with Proposition `as:prop:three` -/

/-- Corollary `as:cor:three` (main statement), with Proposition `as:prop:three` proved. -/
theorem cor_three' (hTS : H_twoStepBorel) (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hν : ν (Icc (n * ∫ x, x ∂F - (lenThree ⌊q * n⌋₊ H - R) / 2)
      (n * ∫ x, x ∂F + (lenThree ⌊q * n⌋₊ H - R) / 2))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin n => F) :=
  cor_three (prop_three hTS) hC F R hR c H q hH hq0 hq1 hFU n hm3 hLR ν hνm hν

/-- Corollary `as:cor:three`: `F` is `n`-completely mixable. -/
theorem cor_three_mixable' (hTS : H_twoStepBorel) (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H) : CompletelyMixable n F :=
  cor_three_mixable (prop_three hTS) hC F R hR c H q hH hq0 hq1 hFU n hm3 hLR

/-- Corollary `as:cor:three` (a). -/
theorem cor_three_a' (hTS : H_twoStepBorel) (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (h4 : 4 ≤ ⌊q * n⌋₊) (hRH : R / H ≤ ⌊q * n⌋₊) : CompletelyMixable n F :=
  cor_three_a (prop_three hTS) hC F R hR c H q hH hq0 hq1 hFU n h4 hRH

/-- Corollary `as:cor:three` (b), the theorem of Puccetti, Wang and Wang: a distribution `F` on
`[a, b]` with `F ≥ (3/n) U[a, b]` is `n`-completely mixable. -/
theorem cor_three_b' (hTS : H_twoStepBorel) (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] {a b : ℝ} (hab : a < b) (hF : F (Icc a b)ᶜ = 0) (n : ℕ) (hn : 3 ≤ n)
    (hFU : ENNReal.ofReal (3 / n) • unifI a b ≤ F) : CompletelyMixable n F :=
  cor_three_b (prop_three hTS) hC F hab hF n hn hFU

/-- Corollary `as:cor:three` (c): three uniform distributions on `[0, 1]` together with any finite
family of distributions on intervals of length at most `1` are jointly mixable. -/
theorem cor_three_c' (hTS : H_twoStepBorel) (hC : H_conc_a) {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 3 => unifI 0 1) F) :=
  cor_three_c (prop_three hTS) hC F hF

/-- Remark `as:rem:three`: a probability measure with mean `3/2` that is carried by an interval
of length `1` containing `3/2`, or by `[1, 5/2]`, or by `[1/2, 2]`, lies in `𝒜_3(U[0, 1])`.
(The characterisation of `𝒜_3(U[0, 1])` by Mao et al. is cited, not used.) -/
theorem rem_three (hTS : H_twoStepBorel) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ x, x ∂ν = 3 / 2)
    (hsupp : (∃ a : ℝ, a ≤ 3 / 2 ∧ 3 / 2 ≤ a + 1 ∧ ν (Icc a (a + 1))ᶜ = 0) ∨
      ν (Icc 1 (5 / 2))ᶜ = 0 ∨ ν (Icc (1 / 2) 2)ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin 3 => unifI 0 1) := by
  obtain ⟨h1, h2⟩ := prop_three hTS
  have hU : unifI (1 / 2 - 1 / 2) (1 / 2 + 1 / 2) = unifI 0 1 := by norm_num
  have hL : lenThree 3 (1 / 2) = 1 := by unfold lenThree; norm_num
  rw [← hU]
  rcases hsupp with ⟨a, ha1, ha2, hs⟩ | hs | hs
  · exact h1 3 (1 / 2) (1 / 2) ν le_rfl (by norm_num) inferInstance
      (by rw [hmean]; norm_num) a (by norm_num; linarith) (by rw [hL]; norm_num; linarith)
      (by rw [hL]; exact hs)
  · refine h2 (1 / 2) (1 / 2) ν (by norm_num) inferInstance (by rw [hmean]; norm_num) (Or.inl ?_)
    convert hs using 3 <;> norm_num
  · refine h2 (1 / 2) (1 / 2) ν (by norm_num) inferInstance (by rw [hmean]; norm_num) (Or.inr ?_)
    convert hs using 3 <;> norm_num

end Mixes.AsymThree
