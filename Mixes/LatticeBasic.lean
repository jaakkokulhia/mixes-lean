import Mixes.Defs

/-!
# Lattice distributions and allocations (Section `lt:sec:lattice`), part 1

This file verifies Lemma `lt:lem:count`, Proposition `lt:prop:ops`, Theorem `lt:thm:pb` and
Proposition `lt:prop:three` of the paper.

## Finite laws

All distributions in this section have finite support, and all mixes are built from finitely
many tuples. We work with *finite laws*: for a finite type `Ω` with weights `w : Ω → ℝ` and a
map `X : Ω → β`, `law w X = ∑ ω, w ω • δ_{X ω}` is the distribution of the random variable `X` on
the finite probability space `(Ω, w)`. Independence is a product of finite spaces, and the
distribution of a sum of independent indicators with success probabilities `q i` is `pbLaw q`.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.LatticeBasic

open Mixes

/-! ### Finite laws -/

section FiniteLaw

variable {Ω Ω' β γ : Type*} [Fintype Ω] [Fintype Ω'] [MeasurableSpace β] [MeasurableSpace γ]

/-- The distribution of `X : Ω → β` on the finite space `Ω` with weights `w`. -/
def law (w : Ω → ℝ) (X : Ω → β) : Measure β :=
  ∑ ω, ENNReal.ofReal (w ω) • Measure.dirac (X ω)

/-- The mass that `X` puts on the value `v` under the weights `w`. -/
def mass (w : Ω → ℝ) (X : Ω → β) (v : β) : ℝ := by
  classical exact ∑ ω, if X ω = v then w ω else 0

lemma law_apply (w : Ω → ℝ) (X : Ω → β) {A : Set β} (hA : MeasurableSet A) :
    law w X A = ∑ ω, ENNReal.ofReal (w ω) * A.indicator 1 (X ω) := by
  simp [law, Measure.dirac_apply' _ hA]

lemma law_apply_real {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) {A : Set β}
    (hA : MeasurableSet A) :
    law w X A = ENNReal.ofReal (∑ ω, w ω * A.indicator 1 (X ω)) := by
  rw [law_apply _ _ hA, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : X ω ∈ A <;> simp [h]
  · intro ω _
    by_cases h : X ω ∈ A <;> simp [h, hw ω]

lemma lintegral_law (w : Ω → ℝ) (X : Ω → β) {f : β → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f x ∂(law w X) = ∑ ω, ENNReal.ofReal (w ω) * f (X ω) := by
  simp [law, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac' _ hf]

lemma law_map (w : Ω → ℝ) (X : Ω → β) {f : β → γ} (hf : Measurable f) :
    (law w X).map f = law w (f ∘ X) := by
  ext A hA
  rw [Measure.map_apply hf hA, law_apply _ _ (hf hA), law_apply _ _ hA]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : f (X ω) ∈ A <;> simp [Set.indicator, h]

lemma law_comp_equiv (w : Ω → ℝ) (X : Ω → β) (e : Ω' ≃ Ω) :
    law (w ∘ e) (X ∘ e) = law w X := by
  unfold law
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma law_isProb {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h1 : ∑ ω, w ω = 1) (X : Ω → β) :
    IsProbabilityMeasure (law w X) := by
  constructor
  rw [law_apply_real hw X MeasurableSet.univ]
  simp [h1]

lemma mass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (v : β) : 0 ≤ mass w X v := by
  classical
  unfold mass
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [hw ω]

/-- An expectation over a finite space, grouped by the values of `X`. -/
lemma sum_eq_sum_mass (w : Ω → ℝ) (X : Ω → β) (U : Finset β) (hU : ∀ ω, X ω ∈ U)
    (g : β → ℝ) : ∑ ω, w ω * g (X ω) = ∑ v ∈ U, mass w X v * g v := by
  classical
  unfold mass
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_ite_eq]
  simp [hU ω]

variable [MeasurableSingletonClass β]

lemma law_singleton {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (v : β) :
    law w X {v} = ENNReal.ofReal (mass w X v) := by
  classical
  rw [law_apply_real hw X (measurableSet_singleton v)]
  congr 1
  unfold mass
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = v <;> simp [h]

/-- Two finite laws with the same masses are equal. -/
lemma law_ext {w : Ω → ℝ} {w' : Ω' → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw' : ∀ ω, 0 ≤ w' ω)
    {X : Ω → β} {X' : Ω' → β} (h : ∀ v, mass w X v = mass w' X' v) : law w X = law w' X' := by
  classical
  ext A hA
  rw [law_apply_real hw X hA, law_apply_real hw' X' hA]
  congr 1
  let U := Finset.univ.image X ∪ Finset.univ.image X'
  rw [sum_eq_sum_mass w X U (fun ω => by simp [U]) (A.indicator 1),
    sum_eq_sum_mass w' X' U (fun ω => by simp [U]) (A.indicator 1)]
  simp_rw [h]

lemma mass_eq_of_law_eq {w : Ω → ℝ} {w' : Ω' → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw' : ∀ ω, 0 ≤ w' ω)
    {X : Ω → β} {X' : Ω' → β} (h : law w X = law w' X') (v : β) :
    mass w X v = mass w' X' v := by
  have := congrArg (fun P : Measure β => P {v}) h
  simp only [law_singleton hw, law_singleton hw'] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (mass_nonneg hw X v) (mass_nonneg hw' X' v)).1 this

/-- Two finite laws with the same expectations are equal. -/
lemma law_eq_of_expect {w : Ω → ℝ} {w' : Ω' → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw' : ∀ ω, 0 ≤ w' ω)
    {X : Ω → β} {X' : Ω' → β}
    (h : ∀ g : β → ℝ, ∑ ω, w ω * g (X ω) = ∑ ω, w' ω * g (X' ω)) : law w X = law w' X' := by
  classical
  refine law_ext hw hw' fun v => ?_
  have := h (fun x => if x = v then 1 else 0)
  simpa [mass, mul_ite] using this

lemma expect_eq_of_law_eq {w : Ω → ℝ} {w' : Ω' → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw' : ∀ ω, 0 ≤ w' ω)
    {X : Ω → β} {X' : Ω' → β} (h : law w X = law w' X') (g : β → ℝ) :
    ∑ ω, w ω * g (X ω) = ∑ ω, w' ω * g (X' ω) := by
  classical
  let U := Finset.univ.image X ∪ Finset.univ.image X'
  rw [sum_eq_sum_mass w X U (fun ω => by simp [U]) g,
    sum_eq_sum_mass w' X' U (fun ω => by simp [U]) g]
  simp_rw [mass_eq_of_law_eq hw hw' h]

/-- A finite measure carried by the range of an injective map from a finite type is a finite
law. -/
lemma eq_law_of_carried (P : Measure β) [IsFiniteMeasure P] {Y : Ω → β}
    (hY : Function.Injective Y) (hP : P (Set.range Y)ᶜ = 0) :
    P = law (fun ω => (P {Y ω}).toReal) Y := by
  classical
  ext A hA
  rw [law_apply _ _ hA]
  have hT : ((Finset.univ.image Y : Finset β) : Set β) = Set.range Y := by simp
  have h1 : P A = P (A ∩ ↑((Finset.univ.image Y).filter (· ∈ A))) := by
    rw [Finset.coe_filter]
    have : A ∩ {x | x ∈ Finset.univ.image Y ∧ x ∈ A} = A ∩ Set.range Y := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at *
      rw [← Finset.mem_coe, hT]; tauto
    rw [this, ← Measure.restrict_apply' (by rw [← hT]; exact Finset.measurableSet _)]
    rw [Measure.restrict_eq_self_of_ae_mem]
    exact measure_mono_null (fun x hx => hx) hP
  rw [h1, Set.inter_eq_right.2 (fun x hx => by simp at hx; exact hx.2), ← sum_measure_singleton,
    Finset.sum_filter, Finset.sum_image (fun a _ b _ h => hY h)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  by_cases h : Y ω ∈ A <;> simp [h]

lemma integral_law {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (g : β → ℝ) :
    ∫ x, g x ∂(law w X) = ∑ ω, w ω * g (X ω) := by
  unfold law
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw ω), smul_eq_mul]
  · intro ω _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

end FiniteLaw

/-! ### Joint mixes from finite laws, and finite laws from joint mixes -/

section Bridge

variable {Ω : Type*} [Fintype Ω] {n : ℕ}

/-- A finite law of tuples with constant sum (on the tuples of positive weight) is a joint mix
of its coordinate laws. -/
theorem isJointMix_law {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h1 : ∑ ω, w ω = 1)
    (Y : Ω → Fin n → ℝ) (s : ℝ) (hs : ∀ ω, w ω ≠ 0 → ∑ b, Y ω b = s)
    {F : Fin n → Measure ℝ} (hF : ∀ b, law w (fun ω => Y ω b) = F b) :
    IsJointMix F (law w Y) := by
  refine ⟨law_isProb hw h1 Y, ⟨s, ?_⟩, fun b => ?_⟩
  · rw [ae_iff]
    have hm : MeasurableSet {x : Fin n → ℝ | ¬∑ j, x j = s} :=
      (measurableSet_singleton s).compl.preimage
        (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
    rw [law_apply _ _ hm]
    refine Finset.sum_eq_zero fun ω _ => ?_
    by_cases h : w ω = 0
    · simp [h]
    · simp [hs ω h]
  · rw [law_map _ _ (measurable_pi_apply b)]
    exact hF b

theorem completelyMixable_of_law {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h1 : ∑ ω, w ω = 1)
    (Y : Ω → Fin n → ℝ) (s : ℝ) (hs : ∀ ω, w ω ≠ 0 → ∑ b, Y ω b = s)
    {F : Measure ℝ} (hF : ∀ b, law w (fun ω => Y ω b) = F) : CompletelyMixable n F :=
  ⟨_, isJointMix_law hw h1 Y s hs hF⟩

theorem jointlyMixable_of_law {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h1 : ∑ ω, w ω = 1)
    (Y : Ω → Fin n → ℝ) (s : ℝ) (hs : ∀ ω, w ω ≠ 0 → ∑ b, Y ω b = s)
    {F : Fin n → Measure ℝ} (hF : ∀ b, law w (fun ω => Y ω b) = F b) : JointlyMixable F :=
  ⟨_, isJointMix_law hw h1 Y s hs hF⟩

/-- A joint mix of distributions carried by a finite set `S` is a finite law of tuples with
entries in `S` and constant sum. -/
theorem exists_law_of_isJointMix {F : Fin n → Measure ℝ} {P : Measure (Fin n → ℝ)}
    (hP : IsJointMix F P) (S : Finset ℝ) (hS : ∀ b, F b (↑S)ᶜ = 0) :
    ∃ (Ω : Type) (_ : Fintype Ω) (w : Ω → ℝ) (Y : Ω → Fin n → ℝ) (s : ℝ),
      (∀ ω, 0 ≤ w ω) ∧ ∑ ω, w ω = 1 ∧ (∀ ω, ∑ b, Y ω b = s) ∧ (∀ ω b, Y ω b ∈ S) ∧
        P = law w Y := by
  classical
  obtain ⟨hprob, ⟨s, hs⟩, hmar⟩ := hP
  let Ω := {y : Fin n → S // ∑ b, (y b : ℝ) = s}
  let Y : Ω → Fin n → ℝ := fun ω b => ω.1 b
  have hY : Function.Injective Y := by
    intro a c h
    apply Subtype.ext; funext b
    exact Subtype.ext (congrFun h b)
  have hnull : P (Set.range Y)ᶜ = 0 := by
    have hsub : (Set.range Y)ᶜ ⊆ (⋃ b, {x : Fin n → ℝ | x b ∈ (↑S : Set ℝ)ᶜ}) ∪
        {x | ¬∑ j, x j = s} := by
      intro x hx
      by_contra hc
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff,
        Finset.mem_coe, not_or, not_exists, not_not] at hc
      exact hx ⟨⟨fun b => ⟨x b, hc.1 b⟩, hc.2⟩, rfl⟩
    refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun b => ?_) ?_)
    · have := hmar b
      rw [← hS b, ← this, Measure.map_apply (measurable_pi_apply b)
        (Finset.measurableSet S).compl]
      rfl
    · exact ae_iff.1 hs
  have hPeq := eq_law_of_carried P hY hnull
  refine ⟨Ω, inferInstance, _, Y, s, fun ω => ENNReal.toReal_nonneg, ?_, fun ω => ω.2,
    fun ω b => (ω.1 b).2, hPeq⟩
  have h1 := congrArg (fun Q : Measure (Fin n → ℝ) => Q Set.univ) hPeq
  simp only [measure_univ] at h1
  rw [law_apply_real (fun ω => ENNReal.toReal_nonneg) Y MeasurableSet.univ] at h1
  simp only [Set.indicator_univ, Pi.one_apply, mul_one] at h1
  have := (ENNReal.ofReal_eq_one).1 h1.symm
  exact this

end Bridge

/-! ### Lemma `lt:lem:count`: count vectors -/

section Count

variable {ι : Type} [Fintype ι]

/-- The count vectors `𝒦_n`: vectors `k` of nonnegative integers indexed by the support points
`x i`, with `∑ k_i = n` and `∑ x_i k_i = m` (in the paper `m = nμ`). -/
def countVecs (x : ι → ℝ) (n : ℕ) (m : ℝ) : Set (ι → ℕ) :=
  {k | ∑ i, k i = n ∧ ∑ i, x i * (k i : ℝ) = m}

/-- The masses `f_i = F{x_i}` of a distribution at the points `x i`. -/
def masses (F : Measure ℝ) (x : ι → ℝ) : ι → ℝ := fun i => (F {x i}).toReal

lemma eq_law_masses {x : ι → ℝ} (hx : Function.Injective x) (F : Measure ℝ)
    [IsFiniteMeasure F] (hF : F (Set.range x)ᶜ = 0) : F = law (masses F x) x :=
  eq_law_of_carried F hx hF

lemma mean_eq_sum {x : ι → ℝ} (hx : Function.Injective x) (F : Measure ℝ)
    [IsFiniteMeasure F] (hF : F (Set.range x)ᶜ = 0) :
    ∫ t, t ∂F = ∑ i, masses F x i * x i := by
  conv_lhs => rw [eq_law_masses hx F hF]
  exact integral_law (fun i => ENNReal.toReal_nonneg) x id

lemma sum_ite_inj {x : ι → ℝ} (hx : Function.Injective x) {y : ℝ} {i₀ : ι} (hy : y = x i₀)
    (c : ι → ℝ) : ∑ i, (if y = x i then c i else 0) = c i₀ := by
  rw [Fintype.sum_eq_single i₀]
  · simp [hy]
  · intro i hi
    rw [ite_eq_right]
    intro h; exact hi (hx (h.symm.trans hy))

/-- Lemma `lt:lem:count`, for support points given by an injective map `x : ι → ℝ` from a
finite type: `F` is `n`-completely mixable if and only if its vector of masses is a convex
combination of the vectors `k / n`, `k ∈ 𝒦_n`. -/
theorem count_iff_fintype {x : ι → ℝ} (hx : Function.Injective x) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.range x)ᶜ = 0) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n F ↔ masses F x ∈ convexHull ℝ
      ((fun k : ι → ℕ => fun i => (k i : ℝ) / n) '' countVecs x n (n * ∫ t, t ∂F)) := by
  classical
  set f := masses F x with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => ENNReal.toReal_nonneg
  have hFl : F = law f x := eq_law_masses hx F hF
  have hμ := mean_eq_sum hx F hF
  rw [← hf] at hμ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨P, hP⟩
    have hS : ∀ b : Fin n, F (↑(Finset.univ.image x) : Set ℝ)ᶜ = 0 := by
      intro b; simpa using hF
    obtain ⟨Ω, _, w, Y, s, hw0, hw1, hsum, hY, rfl⟩ := exists_law_of_isJointMix hP _ hS
    obtain ⟨-, -, hmar⟩ := hP
    have hmarg : ∀ b, law w (fun ω => Y ω b) = law f x := by
      intro b; rw [← hFl]; exact (law_map w Y (measurable_pi_apply b)).symm.trans (hmar b)
    have hexp : ∀ b (g : ℝ → ℝ), ∑ ω, w ω * g (Y ω b) = ∑ i, f i * g (x i) :=
      fun b g => expect_eq_of_law_eq hw0 hf0 (hmarg b) g
    have hYx : ∀ ω b, ∃ i, Y ω b = x i := by
      intro ω b; have := hY ω b; simp at this; obtain ⟨i, hi⟩ := this; exact ⟨i, hi.symm⟩
    let cnt : Ω → ι → ℕ := fun ω i => (Finset.univ.filter fun b => Y ω b = x i).card
    have hcnt : ∀ ω i, (cnt ω i : ℝ) = ∑ b, if Y ω b = x i then 1 else 0 := by
      intro ω i; simp [cnt, Finset.sum_boole]
    have hs : s = n * ∫ t, t ∂law f x := by
      rw [← hFl, hμ]
      have h1 : ∑ ω, w ω * (∑ b, Y ω b) = s := by simp [hsum, ← Finset.sum_mul, hw1]
      rw [← h1]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have := fun b => hexp b id
      simp only [id] at this
      simp [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
    refine mem_convexHull_of_exists_fintype w (fun ω i => (cnt ω i : ℝ) / n) hw0 hw1 ?_ ?_
    · intro ω
      refine ⟨cnt ω, ⟨?_, ?_⟩, rfl⟩
      · have : (∑ i, cnt ω i : ℝ) = n := by
          simp_rw [hcnt]
          rw [Finset.sum_comm]
          have : ∀ b, ∑ i, (if Y ω b = x i then (1:ℝ) else 0) = 1 := by
            intro b; obtain ⟨i₀, hi₀⟩ := hYx ω b; exact sum_ite_inj hx hi₀ _
          simp [this]
        exact_mod_cast this
      · rw [← hFl] at hs; rw [← hs, ← hsum ω]
        simp_rw [hcnt, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        obtain ⟨i₀, hi₀⟩ := hYx ω b
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [sum_ite_inj hx hi₀ x, hi₀]
    · funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have this : ∀ b, ∑ ω, w ω * (if Y ω b = x i then (1:ℝ) else 0) = f i := by
        intro b
        have := hexp b (fun y => if y = x i then 1 else 0)
        rw [this]
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Fintype.sum_eq_single i]
        · simp
        · intro j hj; rw [ite_eq_right]; exact fun h => hj (hx h)
      have h2 : ∀ ω, w ω * ((cnt ω i : ℝ) / n) =
          (∑ b, w ω * (if Y ω b = x i then (1:ℝ) else 0)) / n := by
        intro ω; rw [hcnt, mul_div_assoc', Finset.mul_sum]
      simp_rw [h2, ← Finset.sum_div]
      rw [Finset.sum_comm]
      simp_rw [this]
      simp
      field_simp
  · intro hmem
    obtain ⟨κ, _, w, z, hw0, hw1, hz, hsumz⟩ := mem_convexHull_iff_exists_fintype.1 hmem
    choose k hk hkz using hz
    have : NeZero n := ⟨by omega⟩
    have hcard : ∀ t, Fintype.card (Σ i : ι, Fin (k t i)) = n := by
      intro t; simp [Fintype.card_sigma, (hk t).1]
    let e : ∀ t, Fin n ≃ Σ i : ι, Fin (k t i) := fun t => (Fintype.equivFinOfCardEq (hcard t)).symm
    let u : κ → Fin n → ℝ := fun t j => x (e t j).1
    have hu : ∀ t (g : ℝ → ℝ), ∑ j, g (u t j) = ∑ i, (k t i : ℝ) * g (x i) := by
      intro t g
      rw [Fintype.sum_equiv (e t) (fun j => g (u t j)) (fun σ => g (x σ.1)) (fun j => rfl),
        Fintype.sum_sigma]
      simp
    let W : κ × Fin n → ℝ := fun p => w p.1 / n
    let Y : κ × Fin n → Fin n → ℝ := fun p b => u p.1 (b + p.2)
    have hW0 : ∀ p, 0 ≤ W p := fun p => div_nonneg (hw0 p.1) hnR.le
    have hshift : ∀ t r (g : ℝ → ℝ), ∑ b, g (u t (b + r)) = ∑ j, g (u t j) := by
      intro t r g
      exact Fintype.sum_equiv (Equiv.addRight r) _ _ (fun b => rfl)
    refine completelyMixable_of_law (w := W) hW0 ?_ Y (n * ∫ t, t ∂F) ?_ ?_
    · rw [Fintype.sum_prod_type]
      simp [W, Finset.sum_const, Finset.card_univ]
      field_simp
      exact hw1
    · intro p _
      show ∑ b, u p.1 (b + p.2) = _
      have h3 := hshift p.1 p.2 id
      simp only [id] at h3
      rw [h3]
      have := hu p.1 id
      simp only [id] at this
      rw [this, ← (hk p.1).2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · intro b
      rw [hFl]
      refine law_eq_of_expect hW0 hf0 fun g => ?_
      rw [Fintype.sum_prod_type]
      have hfi : ∀ i, f i = ∑ t, w t * ((k t i : ℝ) / n) := by
        intro i
        have := congrFun hsumz i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [← this]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hkz t]
      simp only [W, Y]
      have hin : ∀ t, ∑ r, w t / n * g (u t (b + r)) = w t / n * ∑ i, (k t i : ℝ) * g (x i) := by
        intro t
        rw [← Finset.mul_sum, ← hu t g]
        congr 1
        exact Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun r => rfl)
      simp_rw [hin, hfi, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
      ring

/-- Lemma `lt:lem:count` as stated in the paper: `S` is a finite set of real numbers that
carries `F`, and `𝒦_n` is the set of count vectors indexed by `S`. -/
theorem count_iff (S : Finset ℝ) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (↑S)ᶜ = 0) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n F ↔ (fun v : S => (F {(v : ℝ)}).toReal) ∈ convexHull ℝ
      ((fun k : S → ℕ => fun v => (k v : ℝ) / n) ''
        countVecs (fun v : S => (v : ℝ)) n (n * ∫ t, t ∂F)) :=
  count_iff_fintype (x := fun v : S => (v : ℝ)) Subtype.val_injective F
    (by simpa using hF) hn

end Count

/-! ### Sums of independent indicators -/

section PB

/-- The weight of the value `e` of an indicator with success probability `q`. -/
def bern (q : ℝ) (e : Bool) : ℝ := if e then q else 1 - q

/-- The indicator `1` or `0` of a Boolean. -/
def ind (e : Bool) : ℝ := if e then 1 else 0

/-- The distribution of a sum of independent indicators with the success probabilities `q i`. -/
def pbLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) : Measure ℝ :=
  law (fun ε : ι → Bool => ∏ i, bern (q i) (ε i)) (fun ε => ∑ i, ind (ε i))

/-- The binomial distribution `B(N, p)`. -/
def binom (N : ℕ) (p : ℝ) : Measure ℝ := pbLaw (fun _ : Fin N => p)

variable {ι ι' α : Type*} [Fintype ι] [Fintype ι'] [Fintype α] [DecidableEq ι] [DecidableEq ι']

lemma bern_nonneg {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (e : Bool) : 0 ≤ bern q e := by
  cases e <;> simp [bern] <;> linarith [hq.1, hq.2]

lemma pbW_nonneg {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (ε : ι → Bool) :
    0 ≤ ∏ i, bern (q i) (ε i) :=
  Finset.prod_nonneg fun i _ => bern_nonneg (hq i) _

lemma sum_prod_eq_one {β : ι → Type*} [∀ i, Fintype (β i)] (ρ : ∀ i, β i → ℝ)
    (h : ∀ i, ∑ a, ρ i a = 1) : ∑ D : (∀ i, β i), ∏ i, ρ i (D i) = 1 := by
  rw [← Fintype.prod_sum]
  simp [h]

lemma pbW_sum (q : ι → ℝ) : ∑ ε : ι → Bool, ∏ i, bern (q i) (ε i) = 1 :=
  sum_prod_eq_one (fun i => bern (q i)) (fun i => by simp [bern])

lemma pbLaw_isProb {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) : IsProbabilityMeasure (pbLaw q) :=
  law_isProb (pbW_nonneg hq) (pbW_sum q) _

/-- Reindexing the indicators does not change the distribution of their sum. -/
lemma pbLaw_equiv (q : ι → ℝ) (e : ι' ≃ ι) : pbLaw (q ∘ e) = pbLaw q := by
  let E : (ι' → Bool) ≃ (ι → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  unfold pbLaw
  rw [← law_comp_equiv _ _ E.symm]
  congr 1
  · funext ε
    simp only [Function.comp, E, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm,
      Equiv.coe_refl, Function.comp_apply, id]
    exact Fintype.prod_equiv e _ _ (fun i => by simp)
  · funext ε
    simp only [Function.comp, E, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm,
      Equiv.coe_refl, Function.comp_apply, id]
    exact Fintype.sum_equiv e _ _ (fun i => by simp)

/-- Indicators with success probability `0` can be dropped. -/
lemma pbLaw_sum_zero (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    pbLaw (Sum.elim q (fun _ : ι' => (0 : ℝ))) = pbLaw q := by
  let E := Equiv.sumArrowEquivProdArrow ι ι' Bool
  rw [pbLaw, ← law_comp_equiv _ _ E.symm]
  have hq' : ∀ i, 0 ≤ Sum.elim q (fun _ : ι' => (0 : ℝ)) i ∧ Sum.elim q (fun _ => 0) i ≤ 1 := by
    intro i; cases i <;> simp [hq]
  refine law_eq_of_expect (fun p => pbW_nonneg hq' _) (pbW_nonneg hq) fun g => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single (fun _ => false)]
  · simp only [Function.comp, E, Fintype.prod_sum_type, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]
    simp [bern, ind]
  · intro c hc
    obtain ⟨i', hi'⟩ : ∃ i', c i' = true := by
      by_contra h; push Not at h; exact hc (funext fun i => by simpa using h i)
    simp only [Function.comp, E, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
    rw [Finset.prod_eq_zero (Finset.mem_univ i') (by simp [bern, hi'])]
    simp

/-- A sum of `#T` indicators with success probability `p` and others with probability `0` is
binomial. -/
lemma pbLaw_eq_binom (T : Finset ι) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) :
    pbLaw (fun i => if i ∈ T then p else 0) = binom T.card p := by
  let e : {i // i ∈ T} ⊕ {i // i ∉ T} ≃ ι := Equiv.sumCompl (· ∈ T)
  rw [← pbLaw_equiv _ e]
  have : ((fun i => if i ∈ T then p else 0) ∘ e) = Sum.elim (fun _ => p) (fun _ => 0) := by
    funext i; rcases i with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp [e, hi]
  rw [this, pbLaw_sum_zero _ (fun _ => hp)]
  let e' : {i // i ∈ T} ≃ Fin T.card := Fintype.equivFinOfCardEq (by simp)
  rw [binom, ← pbLaw_equiv _ e']
  rfl

/-- The distribution of the number of indicators `E i (D i)` that hold, for independent `D i`
with distributions `ρ i`, is that of a sum of independent indicators. -/
theorem law_count_prod (ρ : ι → α → ℝ) (hρ0 : ∀ i a, 0 ≤ ρ i a) (hρ1 : ∀ i, ∑ a, ρ i a = 1)
    (E : ι → α → Bool) :
    law (fun D : ι → α => ∏ i, ρ i (D i)) (fun D => ∑ i, ind (E i (D i))) =
      pbLaw (fun i => ∑ a, if E i a then ρ i a else 0) := by
  set q := fun i => ∑ a, if E i a then ρ i a else 0 with hqdef
  have hq1 : ∀ i, ∑ a, (if E i a = false then ρ i a else 0) = 1 - q i := by
    intro i
    rw [← hρ1 i, hqdef]
    simp only
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    cases E i a <;> simp
  have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := by
    intro i
    refine ⟨Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hρ0], ?_⟩
    have := hq1 i
    have h0 : 0 ≤ ∑ a, (if E i a = false then ρ i a else 0) :=
      Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hρ0]
    linarith
  refine law_eq_of_expect (fun D => Finset.prod_nonneg fun i _ => hρ0 i _) (pbW_nonneg hq)
    fun g => ?_
  let φ : (ι → α) → (ι → Bool) := fun D i => E i (D i)
  rw [← Finset.sum_fiberwise Finset.univ φ]
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hfib : ∀ D ∈ Finset.univ.filter (fun D => φ D = ε),
      (∏ i, ρ i (D i)) * g (∑ i, ind (E i (D i))) = (∏ i, ρ i (D i)) * g (∑ i, ind (ε i)) := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
    rw [← hD]
  rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul]
  congr 1
  have hset : Finset.univ.filter (fun D => φ D = ε) =
      Fintype.piFinset (fun i => Finset.univ.filter (fun a => E i a = ε i)) := by
    ext D; simp [φ, Fintype.mem_piFinset, funext_iff]
  rw [hset, ← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]
  cases h : ε i
  · simp [bern, hq1 i]
  · simp [bern, hqdef]

/-- The hypersimplex: a vector `z ∈ [0,1]^β` with integer sum `j` is the vector of inclusion
probabilities of a random set with `j` elements. -/
theorem exists_set_law {β : Type*} [Fintype β] [DecidableEq β] (z : β → ℝ)
    (hz : ∀ b, 0 ≤ z b ∧ z b ≤ 1) (j : ℕ) (hj : ∑ b, z b = j) :
    ∃ L : Finset β → ℝ, (∀ A, 0 ≤ L A) ∧ ∑ A, L A = 1 ∧ (∀ A, L A ≠ 0 → A.card = j) ∧
      ∀ b, ∑ A, (if b ∈ A then L A else 0) = z b := by
  -- strong induction on the number of fractional coordinates
  suffices H : ∀ m : ℕ, ∀ z : β → ℝ, (Finset.univ.filter fun b => 0 < z b ∧ z b < 1).card = m →
      (∀ b, 0 ≤ z b ∧ z b ≤ 1) → ∑ b, z b = j →
      ∃ L : Finset β → ℝ, (∀ A, 0 ≤ L A) ∧ ∑ A, L A = 1 ∧ (∀ A, L A ≠ 0 → A.card = j) ∧
        ∀ b, ∑ A, (if b ∈ A then L A else 0) = z b from H _ z rfl hz hj
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro z hm hz hj
  by_cases hfr : ∃ b, 0 < z b ∧ z b < 1
  · obtain ⟨b₁, hb₁⟩ := hfr
    -- a second fractional coordinate
    obtain ⟨b₂, hb₂ne, hb₂⟩ : ∃ b₂, b₂ ≠ b₁ ∧ 0 < z b₂ ∧ z b₂ < 1 := by
      by_contra hcon
      push Not at hcon
      have hint : ∀ b, b ≠ b₁ → z b = if z b = 1 then 1 else 0 := by
        intro b hb
        have h1 := hz b
        by_cases h : z b = 1
        · simp [h]
        · rw [if_neg h]
          by_contra h0
          have := hcon b hb (lt_of_le_of_ne h1.1 (Ne.symm h0))
          exact h (le_antisymm h1.2 this)
      have hsplit := Finset.sum_erase_add Finset.univ z (Finset.mem_univ b₁)
      have hN : ∑ b ∈ Finset.univ.erase b₁, z b =
          ((Finset.univ.erase b₁).filter (fun b => z b = 1)).card := by
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun b hb => ?_
        have := hint b (Finset.ne_of_mem_erase hb)
        by_cases h : z b = 1
        · simp [h]
        · rw [if_neg h] at this; simp [h, this]
      rw [hN, hj] at hsplit
      set N := ((Finset.univ.erase b₁).filter (fun b => z b = 1)).card
      have hzb : z b₁ = (((j : ℤ) - N : ℤ) : ℝ) := by push_cast; linarith
      rcases lt_or_ge ((j : ℤ) - N) 1 with h | h
      · have h' : (j : ℤ) - N ≤ 0 := by omega
        have : (((j : ℤ) - N : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h'
        linarith [hb₁.1]
      · have : (1 : ℝ) ≤ (((j : ℤ) - N : ℤ) : ℝ) := by exact_mod_cast h
        linarith [hb₁.2]
    -- the two moves
    set d₁ := min (1 - z b₁) (z b₂) with hd₁
    set d₂ := min (z b₁) (1 - z b₂) with hd₂
    have hd₁p : 0 < d₁ := lt_min (by linarith [hb₁.2]) hb₂.1
    have hd₂p : 0 < d₂ := lt_min hb₁.1 (by linarith [hb₂.2])
    let mv : ℝ → β → ℝ := fun d b => z b + (if b = b₁ then d else 0) - (if b = b₂ then d else 0)
    have mv_sum : ∀ d, ∑ b, mv d b = j := by
      intro d
      simp only [mv, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, hj]
      ring
    have mv_other : ∀ d b, b ≠ b₁ → b ≠ b₂ → mv d b = z b := by
      intro d b h1 h2; simp [mv, h1, h2]
    have mv_b₁ : ∀ d, mv d b₁ = z b₁ + d := by intro d; simp [mv, hb₂ne.symm]
    have mv_b₂ : ∀ d, mv d b₂ = z b₂ - d := by intro d; simp [mv, hb₂ne]
    have frac_lt : ∀ d, (d = d₁ ∨ d = -d₂) →
        (∀ b, 0 ≤ mv d b ∧ mv d b ≤ 1) ∧
        (Finset.univ.filter fun b => 0 < mv d b ∧ mv d b < 1).card < m := by
      intro d hd
      have hbox : ∀ b, 0 ≤ mv d b ∧ mv d b ≤ 1 := by
        intro b
        by_cases h1 : b = b₁
        · subst h1; rw [mv_b₁]
          rcases hd with rfl | rfl
          · constructor <;> [linarith [hb₁.1]; linarith [min_le_left (1 - z b) (z b₂)]]
          · constructor <;> [linarith [min_le_left (z b) (1 - z b₂)]; linarith [hb₁.2]]
        by_cases h2 : b = b₂
        · subst h2; rw [mv_b₂]
          rcases hd with rfl | rfl
          · constructor <;> [linarith [min_le_right (1 - z b₁) (z b)]; linarith [hb₂.2]]
          · constructor <;> [linarith [hb₂.1]; linarith [min_le_right (z b₁) (1 - z b)]]
        rw [mv_other d b h1 h2]; exact hz b
      refine ⟨hbox, ?_⟩
      rw [← hm]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · -- one of b₁, b₂ stops being fractional
        have key : ∀ b, b ∈ (Finset.univ.filter fun b => 0 < z b ∧ z b < 1) →
            (mv d b ≤ 0 ∨ 1 ≤ mv d b) →
            ∃ x ∈ (Finset.univ.filter fun b => 0 < z b ∧ z b < 1),
              x ∉ (Finset.univ.filter fun b => 0 < mv d b ∧ mv d b < 1) := by
          intro b hb hcase
          refine ⟨b, hb, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
          intro h0
          rcases hcase with h | h <;> linarith
        have hb₁m : b₁ ∈ (Finset.univ.filter fun b => 0 < z b ∧ z b < 1) := by simp [hb₁]
        have hb₂m : b₂ ∈ (Finset.univ.filter fun b => 0 < z b ∧ z b < 1) := by simp [hb₂]
        rcases hd with rfl | rfl
        · rcases min_choice (1 - z b₁) (z b₂) with h | h
          · exact key b₁ hb₁m (Or.inr (by rw [mv_b₁, hd₁.trans h]; linarith))
          · exact key b₂ hb₂m (Or.inl (by rw [mv_b₂, hd₁.trans h]; linarith))
        · rcases min_choice (z b₁) (1 - z b₂) with h | h
          · exact key b₁ hb₁m (Or.inl (by rw [mv_b₁, hd₂.trans h]; linarith))
          · exact key b₂ hb₂m (Or.inr (by rw [mv_b₂, hd₂.trans h]; linarith))
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        by_cases h1 : b = b₁
        · subst h1; exact hb₁
        by_cases h2 : b = b₂
        · subst h2; exact hb₂
        rwa [mv_other d b h1 h2] at hb
    obtain ⟨hbox₁, hlt₁⟩ := frac_lt d₁ (Or.inl rfl)
    obtain ⟨hbox₂, hlt₂⟩ := frac_lt (-d₂) (Or.inr rfl)
    obtain ⟨L₁, h0₁, h1₁, hc₁, hm₁⟩ := IH _ hlt₁ (mv d₁) rfl hbox₁ (mv_sum d₁)
    obtain ⟨L₂, h0₂, h1₂, hc₂, hm₂⟩ := IH _ hlt₂ (mv (-d₂)) rfl hbox₂ (mv_sum (-d₂))
    have hs : 0 < d₁ + d₂ := by linarith
    refine ⟨fun A => (d₂ * L₁ A + d₁ * L₂ A) / (d₁ + d₂), fun A => ?_, ?_, fun A hA => ?_,
      fun b => ?_⟩
    · exact div_nonneg (by nlinarith [h0₁ A, h0₂ A]) hs.le
    · rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1₁, h1₂]
      field_simp; ring
    · by_cases h : L₁ A = 0
      · apply hc₂; intro h'; apply hA; simp [h, h']
      · exact hc₁ A h
    · have e1 := hm₁ b
      have e2 := hm₂ b
      have : ∑ A, (if b ∈ A then (d₂ * L₁ A + d₁ * L₂ A) / (d₁ + d₂) else 0) =
          (d₂ * ∑ A, (if b ∈ A then L₁ A else 0) + d₁ * ∑ A, (if b ∈ A then L₂ A else 0)) /
            (d₁ + d₂) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun A _ => ?_
        split_ifs <;> simp
      rw [this, e1, e2]
      field_simp
      simp only [mv]
      split_ifs <;> ring
  · -- all coordinates are 0 or 1
    push Not at hfr
    have h01 : ∀ b, z b = if z b = 1 then 1 else 0 := by
      intro b
      by_cases h : z b = 1
      · simp [h]
      · rw [if_neg h]
        by_contra h0
        exact h (le_antisymm (hz b).2 (hfr b (lt_of_le_of_ne (hz b).1 (Ne.symm h0))))
    let A₀ := Finset.univ.filter fun b => z b = 1
    have hcard : A₀.card = j := by
      have : (A₀.card : ℝ) = j := by
        rw [← hj, Finset.card_filter]; push_cast
        refine Finset.sum_congr rfl fun b _ => ?_
        have := h01 b
        by_cases h : z b = 1
        · simp [h]
        · rw [if_neg h] at this; simp [h, this]
      exact_mod_cast this
    refine ⟨fun A => if A = A₀ then 1 else 0, fun A => by dsimp only; split_ifs <;> norm_num,
      by simp,
      fun A hA => ?_, fun b => ?_⟩
    · by_cases h : A = A₀
      · rw [h, hcard]
      · simp [h] at hA
    · rw [Finset.sum_eq_single A₀]
      · simp only [ite_true]
        rw [h01 b]
        simp [A₀]
      · intro A _ hA; simp [hA]
      · simp

end PB

/-! ### Theorem `lt:thm:pb`: independent sources -/

section Sources

lemma completelyMixable_zero (F : Measure ℝ) : CompletelyMixable 0 F :=
  completelyMixable_of_law (Ω := Unit) (w := fun _ => 1) (fun _ => zero_le_one) (by simp)
    (fun _ => Fin.elim0) 0 (fun _ _ => by simp) (fun b => Fin.elim0 b)

/-- Theorem `lt:thm:pb`, main statement: if the rows of the matrix `z i b ∈ [0,1]` (source `i`,
box `b`) have integer sums, the distributions `F_b` of the sums of independent indicators with
the success probabilities `z i b`, `i ∈ S`, are jointly mixable. -/
theorem pb_jointlyMixable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (z : S → Fin n → ℝ)
    (hz : ∀ i b, 0 ≤ z i b ∧ z i b ≤ 1) (j : S → ℕ) (hj : ∀ i, ∑ b, z i b = j i) :
    JointlyMixable (fun b => pbLaw (fun i => z i b)) := by
  choose L hL0 hL1 hLc hLm using fun i => exists_set_law (z i) (hz i) (j i) (hj i)
  refine jointlyMixable_of_law (w := fun A : S → Finset (Fin n) => ∏ i, L i (A i))
    (fun A => Finset.prod_nonneg fun i _ => hL0 i _) (sum_prod_eq_one L hL1)
    (fun A b => ∑ i, ind (decide (b ∈ A i))) (∑ i, (j i : ℝ)) ?_ ?_
  · intro A hA
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : L i (A i) ≠ 0 := by
      intro h0; apply hA; exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [← hLc i (A i) hne]
    simp [ind, Finset.sum_boole]
  · intro b
    rw [law_count_prod L hL0 hL1 (fun i A => decide (b ∈ A))]
    congr 1
    funext i
    rw [← hLm i b]
    refine Finset.sum_congr rfl fun A _ => ?_
    simp

/-- Theorem `lt:thm:pb`, second statement: if `z₁, …, z_n ∈ [0,1]` have an integer sum, the
distribution of a sum of independent indicators with the success probabilities `z₁, …, z_n`
is `n`-completely mixable. -/
theorem pb_completelyMixable {n : ℕ} (z : Fin n → ℝ) (hz : ∀ b, 0 ≤ z b ∧ z b ≤ 1) (j : ℕ)
    (hj : ∑ b, z b = j) : CompletelyMixable n (pbLaw z) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact completelyMixable_zero _
  have : NeZero n := ⟨by omega⟩
  have h := pb_jointlyMixable (S := Fin n) (fun i b => z (b - i)) (fun i b => hz _) (fun _ => j)
    (fun i => by rw [← hj]; exact Fintype.sum_equiv (Equiv.subRight i) _ _ (fun b => rfl))
  have hcol : ∀ b, pbLaw (fun i => z (b - i)) = pbLaw z := fun b =>
    pbLaw_equiv z (Equiv.subLeft b)
  simp only [hcol] at h
  exact h

/-- Theorem `lt:thm:pb`, last statement: the binomial distribution `B(sK, j/s)` is
`n`-completely mixable for all integers `1 ≤ j ≤ s ≤ n` and `K ≥ 1`. -/
theorem binom_completelyMixable {n j s K : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (hsn : s ≤ n)
    (_hK : 1 ≤ K) : CompletelyMixable n (binom (s * K) ((j : ℝ) / s)) := by
  have hs : 0 < s := by omega
  have : NeZero n := ⟨by omega⟩
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  set p : ℝ := (j : ℝ) / s with hp
  have hp01 : 0 ≤ p ∧ p ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hsR.le, (div_le_one hsR).2 (by exact_mod_cast hjs)⟩
  let zz : Fin n → ℝ := fun c => if c.val < s then p else 0
  have hzz : ∀ c, 0 ≤ zz c ∧ zz c ≤ 1 := by
    intro c; simp only [zz]; split_ifs
    · exact hp01
    · simp
  have hzzsum : ∑ c, zz c = j := by
    simp only [zz]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Fin.card_filter_val_lt, min_eq_right hsn, hp]
    field_simp
  have h := pb_jointlyMixable (S := Fin K × Fin n) (fun i b => zz (b - i.2))
    (fun i b => hzz _) (fun _ => j)
    (fun i => by rw [← hzzsum]; exact Fintype.sum_equiv (Equiv.subRight i.2) _ _ (fun b => rfl))
  let T : Finset (Fin K × Fin n) := Finset.univ ×ˢ Finset.univ.filter (fun c : Fin n => c.val < s)
  have hT : T.card = s * K := by
    simp [T, Finset.card_product, Fin.card_filter_val_lt, min_eq_right hsn, mul_comm]
  have hcol : ∀ b, pbLaw (fun i : Fin K × Fin n => zz (b - i.2)) = binom (s * K) p := by
    intro b
    rw [show (fun i : Fin K × Fin n => zz (b - i.2)) = (fun i : Fin K × Fin n => zz i.2) ∘
      ((Equiv.refl (Fin K)).prodCongr (Equiv.subLeft b)) from funext fun i => rfl,
      pbLaw_equiv, ← hT, ← pbLaw_eq_binom T hp01]
    congr 1
    funext i
    simp [T, zz]
  simp only [hcol] at h
  exact h

end Sources

/-! ### Proposition `lt:prop:ops`: operations on allocations -/

section Ops

/-- The distribution of `Y`, where `X ∼ F` and, given `X = m`, `Y ∼ κ m` (`F` is carried by the
nonnegative integers). -/
def mixN (F : Measure ℝ) (κ : ℕ → Measure ℝ) : Measure ℝ := F.bind (fun x => κ ⌊x⌋₊)

lemma law_ae_sum {Ω : Type*} [Fintype Ω] {n : ℕ} (w : Ω → ℝ) (Y : Ω → Fin n → ℝ) (s : ℝ)
    (hs : ∀ ω, w ω ≠ 0 → ∑ b, Y ω b = s) : ∀ᵐ x ∂(law w Y), ∑ b, x b = s := by
  rw [ae_iff]
  have hm : MeasurableSet {x : Fin n → ℝ | ¬∑ j, x j = s} :=
    (measurableSet_singleton s).compl.preimage
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
  rw [law_apply _ _ hm]
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases h : w ω = 0
  · simp [h]
  · simp [hs ω h]

/-- Labelling the balls of an allocation: a map from `M` balls to the boxes with `y b` balls in
box `b`. -/
lemma exists_ballMap {n M : ℕ} (y : Fin n → ℕ) (h : ∑ b, y b = M) :
    ∃ β : Fin M → Fin n, ∀ b, (Finset.univ.filter fun ℓ => β ℓ = b).card = y b := by
  have hc : Fintype.card (Σ b : Fin n, Fin (y b)) = M := by simp [Fintype.card_sigma, h]
  let e : Fin M ≃ Σ b : Fin n, Fin (y b) := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun ℓ => (e ℓ).1, fun b => ?_⟩
  rw [Finset.card_filter]
  rw [Fintype.sum_equiv e (fun ℓ => if (e ℓ).1 = b then 1 else 0)
    (fun σ => if σ.1 = b then 1 else 0) (fun ℓ => rfl), Fintype.sum_sigma,
    Fintype.sum_eq_single b (fun b' hb' => by simp [hb'])]
  simp

/-- The general principle: an operation on the balls of an allocation in which every box has
distribution `F`, such that the new content of box `b` has the distribution `κ (y b)` given the
old contents `y`, and the new total is constant, yields a complete mix of `mixN F κ`. -/
theorem ops_general {n M : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.range (Nat.cast : ℕ → ℝ))ᶜ = 0) (hcm : CompletelyMixable n F)
    (hM : (M : ℝ) = n * ∫ t, t ∂F) (hn : 1 ≤ n) (κ : ℕ → Measure ℝ)
    {Ω : Type*} [Fintype Ω] (W : ∀ y : Fin n → ℕ, ∑ b, y b = M → Ω → ℝ)
    (Z : ∀ y : Fin n → ℕ, ∑ b, y b = M → Ω → Fin n → ℝ) (s' : ℝ)
    (hW0 : ∀ y h ω, 0 ≤ W y h ω) (hW1 : ∀ y h, ∑ ω, W y h ω = 1)
    (hZ : ∀ y h ω, W y h ω ≠ 0 → ∑ b, Z y h ω b = s')
    (hκ : ∀ y h b, law (W y h) (fun ω => Z y h ω b) = κ (y b)) :
    ∃ P, IsCompleteMix n (mixN F κ) P ∧ ∀ᵐ x ∂P, ∑ b, x b = s' := by
  classical
  obtain ⟨P, hprob, ⟨s, hs⟩, hmar⟩ := hcm
  have hmar' : ∀ b, P.map (fun x => x b) = F := fun b => hmar b
  have hmeasN : MeasurableSet (Set.range (Nat.cast : ℕ → ℝ)) :=
    (Set.countable_range _).measurableSet
  have hnat : ∀ b, P {x | x b ∈ (Set.range (Nat.cast : ℕ → ℝ))ᶜ} = 0 := by
    intro b
    rw [← hF, ← hmar' b, Measure.map_apply (measurable_pi_apply b) hmeasN.compl]
    rfl
  let b₀ : Fin n := ⟨0, hn⟩
  let S : Finset ℝ := (Finset.range (⌊s⌋₊ + 1)).image (Nat.cast)
  have hS : ∀ b : Fin n, F (↑S)ᶜ = 0 := by
    intro _
    have hsub : (↑S : Set ℝ)ᶜ ⊆ (Set.range (Nat.cast : ℕ → ℝ))ᶜ ∪ Set.Ioi s := by
      intro v hv
      by_cases hvn : v ∈ Set.range (Nat.cast : ℕ → ℝ)
      · right
        obtain ⟨m, rfl⟩ := hvn
        simp only [S, Finset.coe_image, Finset.coe_range, Set.mem_compl_iff, Set.mem_image,
          Set.mem_Iio, not_exists, not_and] at hv
        have : ⌊s⌋₊ + 1 ≤ m := by
          by_contra hc; exact hv m (by omega) rfl
        have h2 := Nat.lt_floor_add_one s
        simp only [Set.mem_Ioi]
        calc s < ⌊s⌋₊ + 1 := h2
          _ ≤ m := by exact_mod_cast this
      · left; exact hvn
    refine measure_mono_null hsub (measure_union_null hF ?_)
    rw [← hmar' b₀, Measure.map_apply (measurable_pi_apply b₀) measurableSet_Ioi]
    have hsub2 : (fun x : Fin n → ℝ => x b₀) ⁻¹' Set.Ioi s ⊆
        {x | ¬∑ j, x j = s} ∪ ⋃ b, {x | x b ∈ (Set.range (Nat.cast : ℕ → ℝ))ᶜ} := by
      intro x hx
      by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_compl_iff, not_or,
        not_not, not_exists] at hc
      have hnn : ∀ j, 0 ≤ x j := by
        intro j; obtain ⟨m, hm⟩ := hc.2 j; rw [← hm]; exact Nat.cast_nonneg m
      have : x b₀ ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ b₀)
      simp only [Set.mem_preimage, Set.mem_Ioi] at hx
      linarith [hc.1]
    exact measure_mono_null hsub2 (measure_union_null (ae_iff.1 hs)
      (measure_iUnion_null hnat))
  obtain ⟨Ω₀, _, w₀, Y, s₀, hw0, hw1, hsum, hY, rfl⟩ :=
    exists_law_of_isJointMix ⟨hprob, ⟨s, hs⟩, hmar⟩ S hS
  have hFb : ∀ b, law w₀ (fun ω => Y ω b) = F := fun b =>
    (law_map w₀ Y (measurable_pi_apply b)).symm.trans (hmar b)
  have hs₀ : s₀ = M := by
    rw [hM]
    have h1 : ∑ ω, w₀ ω * (∑ b, Y ω b) = s₀ := by simp [hsum, ← Finset.sum_mul, hw1]
    rw [← h1]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ ω, w₀ ω * Y ω b = ∫ t, t ∂F := by
      intro b; rw [← hFb b, integral_law hw0]
    simp [this]
  let y : Ω₀ → Fin n → ℕ := fun ω b => ⌊Y ω b⌋₊
  have hYy : ∀ ω b, Y ω b = y ω b := by
    intro ω b
    have := hY ω b
    simp only [S, Finset.mem_image] at this
    obtain ⟨m, _, hm⟩ := this
    simp [y, ← hm]
  have hy : ∀ ω, ∑ b, y ω b = M := by
    intro ω
    have : ((∑ b, y ω b : ℕ) : ℝ) = M := by
      push_cast; simp_rw [← hYy]; rw [hsum, hs₀]
    exact_mod_cast this
  let Wt : Ω₀ × Ω → ℝ := fun p => w₀ p.1 * W (y p.1) (hy p.1) p.2
  let Z' : Ω₀ × Ω → Fin n → ℝ := fun p => Z (y p.1) (hy p.1) p.2
  have hWt0 : ∀ p, 0 ≤ Wt p := fun p => mul_nonneg (hw0 _) (hW0 _ _ _)
  have hWt1 : ∑ p, Wt p = 1 := by
    rw [Fintype.sum_prod_type]
    have : ∀ x, ∑ i, W (y x) (hy x) i = 1 := fun x => hW1 _ _
    simp only [Wt, ← Finset.mul_sum, this, mul_one, hw1]
  have hZ' : ∀ p, Wt p ≠ 0 → ∑ b, Z' p b = s' := by
    intro p hp
    exact hZ _ _ _ (fun h => hp (by simp [Wt, h]))
  refine ⟨law Wt Z', isJointMix_law hWt0 hWt1 Z' s' hZ' fun b => ?_, law_ae_sum Wt Z' s' hZ'⟩
  have hmeasf : ∀ A : Set ℝ, Measurable fun x : ℝ => κ ⌊x⌋₊ A := fun A =>
    (measurable_from_nat (f := fun m => κ m A)).comp Nat.measurable_floor
  ext A hA
  have hae : AEMeasurable (fun x : ℝ => κ ⌊x⌋₊) F :=
    ((measurable_from_nat (f := κ)).comp Nat.measurable_floor).aemeasurable
  rw [law_apply _ _ hA, mixN, Measure.bind_apply hA hae,
    ← hFb b, lintegral_law _ _ (hmeasf A), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω₀ _ => ?_
  show _ = ENNReal.ofReal (w₀ ω₀) * κ (y ω₀ b) A
  rw [← hκ (y ω₀) (hy ω₀) b, law_apply _ _ hA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Wt, Z']
  rw [ENNReal.ofReal_mul (hw0 ω₀), mul_assoc]

instance law_isFinite {Ω β : Type*} [Fintype Ω] [MeasurableSpace β] (w : Ω → ℝ) (X : Ω → β) :
    IsFiniteMeasure (law w X) := by
  constructor
  rw [law_apply _ _ MeasurableSet.univ]
  exact ENNReal.sum_lt_top.2 fun ω _ => by simp

/-- The convolution of two finite laws is the law of the sum on the product space. -/
lemma conv_law {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] {w : Ω → ℝ} {w' : Ω' → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (X : Ω → ℝ) (X' : Ω' → ℝ) :
    law w X ∗ law w' X' = law (fun p : Ω × Ω' => w p.1 * w' p.2) (fun p => X p.1 + X' p.2) := by
  ext A hA
  have hind : Measurable (A.indicator (1 : ℝ → ENNReal)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, Measure.lintegral_conv hind, law_apply _ _ hA,
    Fintype.sum_prod_type]
  have inner : ∀ x, ∫⁻ y, A.indicator 1 (x + y) ∂(law w' X') =
      ∑ ω', ENNReal.ofReal (w' ω') * A.indicator 1 (x + X' ω') := fun x =>
    lintegral_law _ _ (hind.comp (measurable_const_add x))
  simp_rw [inner]
  rw [lintegral_law (f := fun x => ∑ ω', ENNReal.ofReal (w' ω') * A.indicator 1 (x + X' ω'))
    _ _ (Finset.measurable_sum _ fun ω' _ =>
    measurable_const.mul (hind.comp (measurable_add_const _)))]
  simp_rw [Finset.mul_sum, ENNReal.ofReal_mul (hw _), mul_assoc]

lemma pbLaw_sum {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (q : ι → ℝ) (q' : ι' → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    pbLaw (Sum.elim q q') = pbLaw q ∗ pbLaw q' := by
  let E := Equiv.sumArrowEquivProdArrow ι ι' Bool
  rw [pbLaw, pbLaw, pbLaw, conv_law (pbW_nonneg hq), ← law_comp_equiv _ _ E.symm]
  congr 1
  · funext ⟨p₁, p₂⟩
    simp only [Function.comp, E, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  · funext ⟨p₁, p₂⟩
    simp only [Function.comp, E, Fintype.sum_sum_type,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Indicators with two success probabilities: the sum is a convolution of two binomial
distributions. -/
lemma pbLaw_split {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) {a c : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) :
    pbLaw (fun i => if i ∈ T then a else c) = binom T.card a ∗ binom (Fintype.card ι - T.card) c := by
  let e : {i // i ∈ T} ⊕ {i // i ∉ T} ≃ ι := Equiv.sumCompl (· ∈ T)
  rw [← pbLaw_equiv _ e]
  have : ((fun i => if i ∈ T then a else c) ∘ e) = Sum.elim (fun _ => a) (fun _ => c) := by
    funext i; rcases i with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp [e, hi]
  rw [this, pbLaw_sum _ _ (fun _ => ha)]
  let e₁ : {i // i ∈ T} ≃ Fin T.card := Fintype.equivFinOfCardEq (by simp)
  let e₂ : {i // i ∉ T} ≃ Fin (Fintype.card ι - T.card) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_subtype_compl])
  rw [binom, binom, ← pbLaw_equiv _ e₁, ← pbLaw_equiv (fun _ : Fin _ => c) e₂]
  rfl

/-- The hypergeometric distribution: the number of marked balls in a uniformly random sample of
`M'` of `M` balls, of which the first `x` are marked. -/
def hyperLaw (M x M' : ℕ) : Measure ℝ :=
  law (fun _ : {R : Finset (Fin M) // R.card = M'} => (1 : ℝ) / M.choose M')
    (fun R => ((R.1.filter fun ℓ => ℓ.val < x).card : ℝ))

lemma hyper_congr {M M' : ℕ} (B : Finset (Fin M)) :
    law (fun _ : {R : Finset (Fin M) // R.card = M'} => (1 : ℝ) / M.choose M')
      (fun R => ((R.1.filter fun ℓ => ℓ ∈ B).card : ℝ)) = hyperLaw M B.card M' := by
  set B' : Finset (Fin M) := Finset.univ.filter fun ℓ => ℓ.val < B.card with hB'def
  have hBM : B.card ≤ M := by simpa using B.card_le_univ
  have hB' : B'.card = B.card := by
    simp [B', Fin.card_filter_val_lt, min_eq_right hBM]
  let e1 : {x // x ∈ B'} ≃ {x // x ∈ B} := Fintype.equivOfCardEq (by simp [hB'])
  let e2 : {x // x ∉ B'} ≃ {x // x ∉ B} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl, hB'])
  let σ := Equiv.subtypeCongr e1 e2
  have hσ : ∀ x, σ x ∈ B ↔ x ∈ B' := by
    intro x
    by_cases h : x ∈ B'
    · simp [σ, Equiv.subtypeCongr, h]
    · simp [σ, Equiv.subtypeCongr, h]; exact (e2 ⟨x, h⟩).2
  let E : {R : Finset (Fin M) // R.card = M'} ≃ {R : Finset (Fin M) // R.card = M'} :=
    (Equiv.finsetCongr σ).subtypeEquiv (fun R => by simp)
  unfold hyperLaw
  rw [← law_comp_equiv _ _ E]
  congr 1
  funext R
  simp only [Function.comp, E, Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply]
  rw [Finset.filter_map, Finset.card_map]
  congr 3
  ext ℓ
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  rw [hσ ℓ]
  simp [B']

lemma n_pos_of {n M : ℕ} {F : Measure ℝ} (hM : (M : ℝ) = n * ∫ t, t ∂F) (hM1 : 1 ≤ M) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp at hM; omega
  · exact h

/-- Proposition `lt:prop:ops` (a): the number of marked balls in a sample of `M'` balls drawn
without replacement from `M` balls of which `X ∼ F` are marked has an `n`-completely mixable
distribution, with complete mixes of sum `M'`. -/
theorem ops_a {n M : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.range (Nat.cast : ℕ → ℝ))ᶜ = 0) (hcm : CompletelyMixable n F)
    (hM : (M : ℝ) = n * ∫ t, t ∂F) (hM1 : 1 ≤ M) (M' : ℕ) (hM' : M' ≤ M) :
    ∃ P, IsCompleteMix n (mixN F (fun m => hyperLaw M m M')) P ∧
      ∀ᵐ x ∂P, ∑ b, x b = (M' : ℝ) := by
  choose β hβ using fun (y : Fin n → ℕ) (h : ∑ b, y b = M) => exists_ballMap y h
  have hch : (0 : ℝ) < M.choose M' := by exact_mod_cast Nat.choose_pos hM'
  refine ops_general F hF hcm hM (n_pos_of hM hM1) _
    (Ω := {R : Finset (Fin M) // R.card = M'}) (fun _ _ _ => (1 : ℝ) / M.choose M')
    (fun y h R b => ((R.1.filter fun ℓ => β y h ℓ = b).card : ℝ)) M'
    (fun _ _ _ => div_nonneg zero_le_one hch.le) ?_ ?_ ?_
  · intro _ _
    simp [Finset.sum_const, Fintype.card_finset_len]
    field_simp
  · intro y h R _
    have := Finset.card_eq_sum_card_fiberwise (f := β y h) (s := R.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [R.2] at this
    exact_mod_cast this.symm
  · intro y h b
    have hfil : ∀ R : {R : Finset (Fin M) // R.card = M'},
        R.1.filter (fun ℓ => β y h ℓ = b) =
          R.1.filter (fun ℓ => ℓ ∈ Finset.univ.filter fun ℓ => β y h ℓ = b) := by
      intro R; ext ℓ; simp
    simp_rw [hfil]
    rw [hyper_congr, hβ y h b]

/-- The distribution of `m + B`, where `B ∈ {0,1}` equals `1` with probability `m/M`. -/
def plusOneLaw (M m : ℕ) : Measure ℝ := law (bern ((m : ℝ) / M)) (fun e => (m : ℝ) + ind e)

/-- Proposition `lt:prop:ops` (b): `X + B`, where `B ∈ {0,1}` equals `1` with probability `X/M`
given `X`, has an `n`-completely mixable distribution, with complete mixes of sum `M + 1`. -/
theorem ops_b {n M : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.range (Nat.cast : ℕ → ℝ))ᶜ = 0) (hcm : CompletelyMixable n F)
    (hM : (M : ℝ) = n * ∫ t, t ∂F) (hM1 : 1 ≤ M) :
    ∃ P, IsCompleteMix n (mixN F (plusOneLaw M)) P ∧ ∀ᵐ x ∂P, ∑ b, x b = (M : ℝ) + 1 := by
  choose β hβ using fun (y : Fin n → ℕ) (h : ∑ b, y b = M) => exists_ballMap y h
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  refine ops_general F hF hcm hM (n_pos_of hM hM1) _ (Ω := Fin M) (fun _ _ _ => (1 : ℝ) / M)
    (fun y h ℓ b => (y b : ℝ) + ind (decide (β y h ℓ = b))) ((M : ℝ) + 1)
    (fun _ _ _ => div_nonneg zero_le_one hMR.le) ?_ ?_ ?_
  · intro _ _
    simp
    field_simp
  · intro y h ℓ _
    rw [Finset.sum_add_distrib]
    have : ((∑ b, y b : ℕ) : ℝ) = M := by exact_mod_cast h
    push_cast at this
    rw [this]
    simp [ind]
  · intro y h b
    have hyb : y b ≤ M := by
      rw [← h]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have hq : 0 ≤ (y b : ℝ) / M ∧ (y b : ℝ) / M ≤ 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hMR.le, (div_le_one hMR).2 (by exact_mod_cast hyb)⟩
    refine law_eq_of_expect (fun _ => div_nonneg zero_le_one hMR.le) (bern_nonneg hq)
      fun g => ?_
    have hcard := hβ y h b
    have hcard' := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun ℓ : Fin M => β y h ℓ = b)
    rw [hcard, Finset.card_univ, Fintype.card_fin] at hcard'
    have hsplit : ∑ ℓ : Fin M, 1 / (M : ℝ) * g ((y b : ℝ) + ind (decide (β y h ℓ = b))) =
        ∑ ℓ : Fin M, (if β y h ℓ = b then 1 / (M : ℝ) * g ((y b : ℝ) + 1)
          else 1 / (M : ℝ) * g (y b)) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      by_cases hh : β y h ℓ = b <;> simp [hh, ind]
    rw [hsplit, Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard]
    simp only [Fintype.sum_bool, bern, ind, ite_true, Bool.false_eq_true, ite_false, add_zero,
      nsmul_eq_mul]
    have : ((Finset.univ.filter fun ℓ : Fin M => ¬β y h ℓ = b).card : ℝ) = M - y b := by
      rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast hcard'
    rw [this]
    field_simp

/-- The distribution of `B' + B''` for independent binomial `B'` and `B''` with the parameters
`(m, 1 - θ + θ/n)` and `(M - m, θ/n)`. -/
def moveLaw (n M : ℕ) (θ : ℝ) (m : ℕ) : Measure ℝ :=
  binom m (1 - θ + θ / n) ∗ binom (M - m) (θ / n)

/-- Proposition `lt:prop:ops` (c): `B' + B''`, where given `X` the variables `B'` and `B''` are
independent and binomial with the parameters `(X, 1-θ+θ/n)` and `(M-X, θ/n)`, has an
`n`-completely mixable distribution for `0 ≤ θ ≤ n/(n-1)`, with complete mixes of sum `M`. -/
theorem ops_c {n M : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.range (Nat.cast : ℕ → ℝ))ᶜ = 0) (hcm : CompletelyMixable n F)
    (hM : (M : ℝ) = n * ∫ t, t ∂F) (hM1 : 1 ≤ M) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ (n : ℝ) / ((n : ℝ) - 1)) :
    ∃ P, IsCompleteMix n (mixN F (moveLaw n M θ)) P ∧ ∀ᵐ x ∂P, ∑ b, x b = (M : ℝ) := by
  choose β hβ using fun (y : Fin n → ℕ) (h : ∑ b, y b = M) => exists_ballMap y h
  have hn := n_pos_of hM hM1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℝ := 1 - θ + θ / n with ha
  have ha0 : 0 ≤ a := by
    rcases Nat.lt_or_ge 1 n with h2 | h1
    · have h2R : (1 : ℝ) < n := by exact_mod_cast h2
      have h3 : θ * ((n : ℝ) - 1) ≤ n := by rwa [le_div_iff₀ (by linarith)] at hθ1
      have key : θ - θ / n = θ * ((n : ℝ) - 1) / n := by field_simp
      have : θ * ((n : ℝ) - 1) / n ≤ 1 := (div_le_one hnR).2 h3
      rw [ha]; linarith
    · have h1' : n = 1 := by omega
      subst h1'
      simp [ha]
  have ha1 : 0 ≤ a ∧ a ≤ 1 := by
    refine ⟨ha0, ?_⟩
    rw [ha]
    have : θ / n ≤ θ := div_le_self hθ0 (by exact_mod_cast hn)
    linarith
  let ρ : Fin n → Fin n → ℝ := fun c d => if d = c then a else θ / n
  have hρ0 : ∀ c d, 0 ≤ ρ c d := by
    intro c d; simp only [ρ]; split_ifs
    · exact ha0
    · exact div_nonneg hθ0 hnR.le
  have hρ1 : ∀ c, ∑ d, ρ c d = 1 := by
    intro c
    have : ∀ d, ρ c d = θ / n + (if d = c then a - θ / n else 0) := by
      intro d; simp only [ρ]; split_ifs <;> ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha]
    field_simp
    ring
  refine ops_general F hF hcm hM hn _ (Ω := Fin M → Fin n)
    (fun y h D => ∏ ℓ, ρ (β y h ℓ) (D ℓ))
    (fun y h D b => ∑ ℓ, ind (decide (D ℓ = b))) (M : ℝ)
    (fun _ _ _ => Finset.prod_nonneg fun ℓ _ => hρ0 _ _)
    (fun y h => sum_prod_eq_one (fun ℓ => ρ (β y h ℓ)) (fun ℓ => hρ1 _)) ?_ ?_
  · intro y h D _
    rw [Finset.sum_comm]
    simp [ind]
  · intro y h b
    rw [law_count_prod (fun ℓ => ρ (β y h ℓ)) (fun ℓ d => hρ0 _ _) (fun ℓ => hρ1 _)
      (fun ℓ d => decide (d = b))]
    have hq : (fun ℓ => ∑ d, if decide (d = b) then ρ (β y h ℓ) d else 0) =
        fun ℓ => if ℓ ∈ Finset.univ.filter (fun ℓ => β y h ℓ = b) then a else θ / n := by
      funext ℓ
      simp only [decide_eq_true_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ρ,
        Finset.mem_filter, true_and]
      by_cases hh : β y h ℓ = b
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [hq, pbLaw_split _ ha1, hβ y h b, Fintype.card_fin]
    rfl

end Ops

/-! ### Proposition `lt:prop:three`: three points -/

section Three

/-- `k ∈ ℤ³` solves `k₀ + k₁ + k₂ = n` and `x₀k₀ + x₁k₁ + x₂k₂ = nμ`. -/
def IsSol (x : Fin 3 → ℤ) (n : ℕ) (μ : ℝ) (k : Fin 3 → ℤ) : Prop :=
  ∑ i, k i = n ∧ ∑ i, (x i : ℝ) * k i = n * μ

/-- `r_i`: the least nonnegative value of `k_i` among the integer solutions. -/
def rmin (x : Fin 3 → ℤ) (n : ℕ) (μ : ℝ) (i : Fin 3) : ℕ :=
  sInf {m : ℕ | ∃ k, IsSol x n μ k ∧ k i = m}

/-- `g = gcd(x₁ - x₀, x₂ - x₁)`. -/
def gcd3 (x : Fin 3 → ℤ) : ℕ := Int.gcd (x 1 - x 0) (x 2 - x 1)

/-- The generator `v = (x₂ - x₁, -(x₂ - x₀), x₁ - x₀)/g` of the lattice of integer vectors on
which both sums vanish. -/
def vv (x : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![(x 2 - x 1) / gcd3 x, -((x 1 - x 0) / gcd3 x + (x 2 - x 1) / gcd3 x), (x 1 - x 0) / gcd3 x]

variable {x : Fin 3 → ℤ}

lemma vv_spec (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    0 < (gcd3 x : ℤ) ∧ x 1 - x 0 = gcd3 x * vv x 2 ∧ x 2 - x 1 = gcd3 x * vv x 0 ∧
      vv x 1 = -(vv x 2 + vv x 0) ∧ 0 < vv x 0 ∧ 0 < vv x 2 ∧ IsCoprime (vv x 2) (vv x 0) := by
  have hg : 0 < gcd3 x := Int.gcd_pos_of_ne_zero_left _ (by omega)
  have hgZ : (0 : ℤ) < gcd3 x := by exact_mod_cast hg
  have ha : x 1 - x 0 = gcd3 x * vv x 2 := by
    simp only [vv, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hb : x 2 - x 1 = gcd3 x * vv x 0 := by
    simp only [vv, Matrix.cons_val_zero]
    exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  refine ⟨hgZ, ha, hb, by simp [vv], ?_, ?_, ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · have hbez := Int.gcd_eq_gcd_ab (x 1 - x 0) (x 2 - x 1)
    set A := Int.gcdA (x 1 - x 0) (x 2 - x 1)
    set B := Int.gcdB (x 1 - x 0) (x 2 - x 1)
    change ((gcd3 x : ℕ) : ℤ) = (x 1 - x 0) * A + (x 2 - x 1) * B at hbez
    refine ⟨A, B, ?_⟩
    have : (gcd3 x : ℤ) * (A * vv x 2 + B * vv x 0) = gcd3 x * 1 := by
      linear_combination -hbez - A * ha - B * hb
    exact mul_left_cancel₀ hgZ.ne' this

lemma isSol_add {n : ℕ} {μ : ℝ} (h01 : x 0 < x 1) (h12 : x 1 < x 2) {k : Fin 3 → ℤ}
    (hk : IsSol x n μ k) (m : ℤ) : IsSol x n μ (fun i => k i + m * vv x i) := by
  obtain ⟨-, ha, hb, h1, -⟩ := vv_spec h01 h12
  obtain ⟨hk1, hk2⟩ := hk
  simp only [IsSol, Fin.sum_univ_three] at *
  constructor
  · rw [h1]; linarith
  · rw [← hk2]; push_cast; rw [h1]; push_cast
    have ha' : ((x 1 : ℝ) - x 0) = (gcd3 x : ℝ) * vv x 2 := by exact_mod_cast ha
    have hb' : ((x 2 : ℝ) - x 1) = (gcd3 x : ℝ) * vv x 0 := by exact_mod_cast hb
    linear_combination (-(m : ℝ) * (vv x 0 : ℝ)) * ha' + (m : ℝ) * (vv x 2 : ℝ) * hb'

/-- Any two integer solutions differ by a multiple of `v`. -/
lemma isSol_diff {n : ℕ} {μ : ℝ} (h01 : x 0 < x 1) (h12 : x 1 < x 2) {k k' : Fin 3 → ℤ}
    (hk : IsSol x n μ k) (hk' : IsSol x n μ k') : ∃ m : ℤ, ∀ i, k' i = k i + m * vv x i := by
  obtain ⟨hg, ha, hb, h1, h0p, h2p, hcop⟩ := vv_spec h01 h12
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hk1', hk2'⟩ := hk'
  simp only [Fin.sum_univ_three] at *
  set d0 := k' 0 - k 0
  set d1 := k' 1 - k 1
  set d2 := k' 2 - k 2
  have hs : d0 + d1 + d2 = 0 := by simp only [d0, d1, d2]; linarith
  have hx : (x 0 : ℝ) * d0 + x 1 * d1 + x 2 * d2 = 0 := by
    simp only [d0, d1, d2]; push_cast; linarith
  have hxZ : x 0 * d0 + x 1 * d1 + x 2 * d2 = 0 := by exact_mod_cast hx
  -- a d1 + (a + b) d2 = 0
  have key : vv x 2 * d1 + (vv x 2 + vv x 0) * d2 = 0 := by
    have : (gcd3 x : ℤ) * (vv x 2 * d1 + (vv x 2 + vv x 0) * d2) = 0 := by
      have hd0 : d0 = -d1 - d2 := by linarith
      rw [hd0] at hxZ
      linear_combination hxZ - d1 * ha - d2 * ha - d2 * hb
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hg.ne'
    · exact h
  have hdvd : vv x 2 ∣ vv x 0 * d2 := ⟨-(d1 + d2), by linarith⟩
  obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdvd
  refine ⟨m, fun i => ?_⟩
  have hd1 : d1 = -(vv x 2 + vv x 0) * m := by
    rw [hm] at key
    have : vv x 2 * (d1 + (vv x 2 + vv x 0) * m) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2p.ne'
    · linarith
  fin_cases i
  · show k' 0 = k 0 + m * vv x 0
    have : d0 = vv x 0 * m := by linarith
    simp only [d0] at this; linarith
  · show k' 1 = k 1 + m * vv x 1
    rw [h1]; simp only [d1] at hd1; linarith
  · show k' 2 = k 2 + m * vv x 2
    simp only [d2] at hm; linarith

/-- A real vector with the two sums of `nf` differs from a solution by a real multiple of `v`. -/
lemma real_diff {n : ℕ} {μ : ℝ} (h01 : x 0 < x 1) (h12 : x 1 < x 2) {k : Fin 3 → ℤ}
    (hk : IsSol x n μ k) {y : Fin 3 → ℝ} (hy1 : ∑ i, y i = n) (hy2 : ∑ i, (x i : ℝ) * y i = n * μ) :
    ∃ t : ℝ, ∀ i, y i = k i + t * vv x i := by
  obtain ⟨hg, ha, hb, h1, h0p, h2p, -⟩ := vv_spec h01 h12
  obtain ⟨hk1, hk2⟩ := hk
  simp only [Fin.sum_univ_three] at *
  have hk1R : ((k 0 : ℝ) + k 1 + k 2) = n := by exact_mod_cast hk1
  have ha' : ((x 1 : ℝ) - x 0) = (gcd3 x : ℝ) * vv x 2 := by exact_mod_cast ha
  have hb' : ((x 2 : ℝ) - x 1) = (gcd3 x : ℝ) * vv x 0 := by exact_mod_cast hb
  have hgR : (0 : ℝ) < gcd3 x := by exact_mod_cast hg
  have h2R : (0 : ℝ) < vv x 2 := by exact_mod_cast h2p
  set d0 := y 0 - k 0
  set d1 := y 1 - k 1
  set d2 := y 2 - k 2
  have hs : d0 + d1 + d2 = 0 := by simp only [d0, d1, d2]; linarith
  have hx : (x 0 : ℝ) * d0 + x 1 * d1 + x 2 * d2 = 0 := by
    simp only [d0, d1, d2]; linarith
  have key : (vv x 2 : ℝ) * d1 + (vv x 2 + vv x 0) * d2 = 0 := by
    have : (gcd3 x : ℝ) * ((vv x 2 : ℝ) * d1 + (vv x 2 + vv x 0) * d2) = 0 := by
      have hd0 : d0 = -d1 - d2 := by linarith
      rw [hd0] at hx
      linear_combination hx - d1 * ha' - d2 * ha' - d2 * hb'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hgR.ne'
    · exact h
  refine ⟨d2 / vv x 2, fun i => ?_⟩
  fin_cases i
  · show y 0 = k 0 + d2 / vv x 2 * vv x 0
    have : d0 = d2 / vv x 2 * vv x 0 := by
      rw [div_mul_eq_mul_div, eq_div_iff h2R.ne']
      linear_combination (vv x 2 : ℝ) * hs - key
    simp only [d0] at this; linarith
  · show y 1 = k 1 + d2 / vv x 2 * (vv x 1 : ℤ)
    rw [h1]; push_cast
    have : d1 = d2 / vv x 2 * (-(vv x 2 + vv x 0)) := by
      rw [div_mul_eq_mul_div, eq_div_iff h2R.ne']
      linear_combination key
    simp only [d1] at this; linarith
  · show y 2 = k 2 + d2 / vv x 2 * vv x 2
    field_simp
    simp only [d2]; ring

/-- Proposition `lt:prop:three`, first statement: integer solutions exist if and only if
`n(μ - x₀)/g` is an integer. -/
theorem three_sol_iff (h01 : x 0 < x 1) (h12 : x 1 < x 2) (n : ℕ) (μ : ℝ) :
    (∃ k, IsSol x n μ k) ↔ ∃ m : ℤ, (n : ℝ) * (μ - x 0) / gcd3 x = m := by
  obtain ⟨hg, ha, hb, h1, h0p, h2p, hcop⟩ := vv_spec h01 h12
  have hgR : (0 : ℝ) < gcd3 x := by exact_mod_cast hg
  have ha' : ((x 1 : ℝ) - x 0) = (gcd3 x : ℝ) * vv x 2 := by exact_mod_cast ha
  have hb' : ((x 2 : ℝ) - x 1) = (gcd3 x : ℝ) * vv x 0 := by exact_mod_cast hb
  constructor
  · rintro ⟨k, hk1, hk2⟩
    simp only [Fin.sum_univ_three] at hk1 hk2
    have hk1R : ((k 0 : ℝ) + k 1 + k 2) = n := by exact_mod_cast hk1
    refine ⟨vv x 2 * k 1 + (vv x 2 + vv x 0) * k 2, ?_⟩
    rw [div_eq_iff hgR.ne']
    push_cast
    linear_combination -hk2 + (x 0 : ℝ) * hk1R + (k 1 : ℝ) * ha' + (k 2 : ℝ) * ha' +
      (k 2 : ℝ) * hb'
  · rintro ⟨m, hm⟩
    rw [div_eq_iff hgR.ne'] at hm
    obtain ⟨u, w, huw⟩ := hcop
    refine ⟨![n - (u - w) * m - w * m, (u - w) * m, w * m], ?_, ?_⟩
    · simp [Fin.sum_univ_three]; ring
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      have huwR : (u : ℝ) * vv x 2 + w * vv x 0 = 1 := by exact_mod_cast huw
      push_cast
      linear_combination -hm + (m : ℝ) * (gcd3 x : ℝ) * huwR + ((u : ℝ) - w) * m * ha' +
        (w : ℝ) * m * ha' + (w : ℝ) * m * hb'

lemma solSet_nonempty {n : ℕ} {μ : ℝ} (h01 : x 0 < x 1) (h12 : x 1 < x 2) {k : Fin 3 → ℤ}
    (hk : IsSol x n μ k) (i : Fin 3) :
    {m : ℕ | ∃ k', IsSol x n μ k' ∧ k' i = m}.Nonempty := by
  obtain ⟨-, -, -, h1, h0p, h2p, -⟩ := vv_spec h01 h12
  have hpos : ∃ c : ℤ, 0 ≤ k i + c * vv x i := by
    have h0' : 1 ≤ vv x 0 := h0p
    have h2' : 1 ≤ vv x 2 := h2p
    have e0 : 0 ≤ k 0 + |k 0| * vv x 0 := by
      nlinarith [abs_nonneg (k 0), le_abs_self (k 0), neg_abs_le (k 0)]
    have e1 : 0 ≤ k 1 + (-|k 1|) * vv x 1 := by
      rw [h1]; nlinarith [abs_nonneg (k 1), le_abs_self (k 1), neg_abs_le (k 1)]
    have e2 : 0 ≤ k 2 + |k 2| * vv x 2 := by
      nlinarith [abs_nonneg (k 2), le_abs_self (k 2), neg_abs_le (k 2)]
    fin_cases i
    exacts [⟨_, e0⟩, ⟨_, e1⟩, ⟨_, e2⟩]
  obtain ⟨c, hc⟩ := hpos
  exact ⟨(k i + c * vv x i).toNat, _, isSol_add h01 h12 hk c, by simp [Int.toNat_of_nonneg hc]⟩

lemma rmin_spec {n : ℕ} {μ : ℝ} (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (hsol : ∃ k, IsSol x n μ k) (i : Fin 3) :
    ∃ k', IsSol x n μ k' ∧ k' i = rmin x n μ i := by
  obtain ⟨k, hk⟩ := hsol
  exact Nat.sInf_mem (solSet_nonempty h01 h12 hk i)

lemma rmin_le {n : ℕ} {μ : ℝ} {k : Fin 3 → ℤ} (hk : IsSol x n μ k) {i : Fin 3}
    (hi : 0 ≤ k i) : (rmin x n μ i : ℤ) ≤ k i := by
  have : rmin x n μ i ≤ (k i).toNat := Nat.sInf_le ⟨k, hk, by simp [Int.toNat_of_nonneg hi]⟩
  have h2 : ((k i).toNat : ℤ) = k i := Int.toNat_of_nonneg hi
  omega

/-- Proposition `lt:prop:three`, bounds: `r₀ < (x₂-x₁)/g`, `r₁ < (x₂-x₀)/g`, `r₂ < (x₁-x₀)/g`. -/
theorem three_rmin_lt {n : ℕ} {μ : ℝ} (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (hsol : ∃ k, IsSol x n μ k) :
    (rmin x n μ 0 : ℝ) < ((x 2 - x 1 : ℤ) : ℝ) / gcd3 x ∧
      (rmin x n μ 1 : ℝ) < ((x 2 - x 0 : ℤ) : ℝ) / gcd3 x ∧
      (rmin x n μ 2 : ℝ) < ((x 1 - x 0 : ℤ) : ℝ) / gcd3 x := by
  obtain ⟨hg, ha, hb, h1, h0p, h2p, -⟩ := vv_spec h01 h12
  have hgR : (0 : ℝ) < gcd3 x := by exact_mod_cast hg
  have e0 : ((x 2 - x 1 : ℤ) : ℝ) / gcd3 x = vv x 0 := by
    rw [div_eq_iff hgR.ne', hb]; push_cast; ring
  have e1 : ((x 2 - x 0 : ℤ) : ℝ) / gcd3 x = vv x 2 + vv x 0 := by
    rw [div_eq_iff hgR.ne', show x 2 - x 0 = (x 1 - x 0) + (x 2 - x 1) by ring, ha, hb]
    push_cast; ring
  have e2 : ((x 1 - x 0 : ℤ) : ℝ) / gcd3 x = vv x 2 := by
    rw [div_eq_iff hgR.ne', ha]; push_cast; ring
  rw [e0, e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨k, hk, hki⟩ := rmin_spec h01 h12 hsol 0
    by_contra hc; push Not at hc
    have hc' : vv x 0 ≤ (rmin x n μ 0 : ℤ) := by exact_mod_cast hc
    have := rmin_le (isSol_add h01 h12 hk (-1)) (i := 0)
      (by show 0 ≤ k 0 + (-1) * vv x 0; omega)
    change (rmin x n μ 0 : ℤ) ≤ k 0 + (-1) * vv x 0 at this; omega
  · obtain ⟨k, hk, hki⟩ := rmin_spec h01 h12 hsol 1
    by_contra hc; push Not at hc
    have hc' : vv x 2 + vv x 0 ≤ (rmin x n μ 1 : ℤ) := by exact_mod_cast hc
    have := rmin_le (isSol_add h01 h12 hk 1) (i := 1)
      (by show 0 ≤ k 1 + 1 * vv x 1; rw [h1]; omega)
    change (rmin x n μ 1 : ℤ) ≤ k 1 + 1 * vv x 1 at this; rw [h1] at this; omega
  · obtain ⟨k, hk, hki⟩ := rmin_spec h01 h12 hsol 2
    by_contra hc; push Not at hc
    have hc' : vv x 2 ≤ (rmin x n μ 2 : ℤ) := by exact_mod_cast hc
    have := rmin_le (isSol_add h01 h12 hk (-1)) (i := 2)
      (by show 0 ≤ k 2 + (-1) * vv x 2; omega)
    change (rmin x n μ 2 : ℤ) ≤ k 2 + (-1) * vv x 2 at this; omega

lemma sum_masses {ι : Type} [Fintype ι] {x : ι → ℝ} (hx : Function.Injective x) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.range x)ᶜ = 0) : ∑ i, masses F x i = 1 := by
  have h := congrArg (fun P : Measure ℝ => P Set.univ) (eq_law_masses hx F hF)
  simp only [measure_univ] at h
  rw [law_apply_real (w := masses F x) (fun i => ENNReal.toReal_nonneg) x
    MeasurableSet.univ] at h
  simp only [Set.indicator_univ, Pi.one_apply, mul_one] at h
  exact (ENNReal.ofReal_eq_one.1 h.symm)

lemma three_inj (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    Function.Injective (fun i => (x i : ℝ)) := by
  intro i j hij
  have hij' : x i = x j := by simpa using hij
  fin_cases i <;> fin_cases j <;> simp at hij' ⊢ <;> omega

/-- Proposition `lt:prop:three`, criterion: a distribution on three integers `x₀ < x₁ < x₂` is
`n`-completely mixable if and only if integer solutions exist and `n f_i ≥ r_i` for all `i`. -/
theorem three_cm_iff (h01 : x 0 < x 1) (h12 : x 1 < x 2) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.range (fun i => (x i : ℝ)))ᶜ = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    CompletelyMixable n F ↔ (∃ k, IsSol x n (∫ t, t ∂F) k) ∧
      ∀ i, (rmin x n (∫ t, t ∂F) i : ℝ) ≤ n * (F {(x i : ℝ)}).toReal := by
  have hinj := three_inj h01 h12
  rw [count_iff_fintype hinj F hF hn]
  have hμ := mean_eq_sum hinj F hF
  have hf1 := sum_masses hinj F hF
  set μ := ∫ t, t ∂F
  set f := masses F (fun i => (x i : ℝ)) with hfdef
  have hf0 : ∀ i, 0 ≤ f i := fun i => ENNReal.toReal_nonneg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change _ ↔ _ ∧ ∀ i, (rmin x n μ i : ℝ) ≤ n * f i
  obtain ⟨hg, ha, hb, h1, h0p, h2p, -⟩ := vv_spec h01 h12
  constructor
  · intro hmem
    have hne : (countVecs (fun i => (x i : ℝ)) n (n * μ)).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc, Set.image_empty, convexHull_empty] at hmem
      exact hmem
    obtain ⟨k, hk1, hk2⟩ := hne
    refine ⟨⟨fun i => k i, by show ∑ i, ((k i : ℕ) : ℤ) = n; exact_mod_cast hk1,
      by simpa using hk2⟩, fun i => ?_⟩
    let H : Set (Fin 3 → ℝ) := {y | (rmin x n μ i : ℝ) / n ≤ y i}
    have hH : Convex ℝ H := convex_halfSpace_ge ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _
    have hsub : (fun k : Fin 3 → ℕ => fun i => (k i : ℝ) / n) ''
        countVecs (fun i => (x i : ℝ)) n (n * μ) ⊆ H := by
      rintro _ ⟨k', ⟨hk1', hk2'⟩, rfl⟩
      simp only [H, Set.mem_ofPred_eq]
      apply div_le_div_of_nonneg_right _ hnR.le
      have : rmin x n μ i ≤ k' i :=
        Nat.sInf_le ⟨fun i => k' i, ⟨by show ∑ i, ((k' i : ℕ) : ℤ) = n; exact_mod_cast hk1',
          by simpa using hk2'⟩, rfl⟩
      exact_mod_cast this
    have := convexHull_min hsub hH hmem
    simp only [H, Set.mem_ofPred_eq] at this
    rw [div_le_iff₀ hnR] at this
    linarith
  · rintro ⟨⟨k, hk⟩, hbd⟩
    have hsol : ∃ k, IsSol x n μ k := ⟨k, hk⟩
    obtain ⟨t, ht⟩ := real_diff h01 h12 hk (y := fun i => n * f i)
      (by rw [← Finset.mul_sum, hf1, mul_one])
      (by simp_rw [mul_left_comm _ (n : ℝ), ← Finset.mul_sum]; rw [hμ];
          congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
    -- the witnesses of the r_i
    have hm : ∀ i, ∃ m : ℤ, (rmin x n μ i : ℤ) = k i + m * vv x i := by
      intro i
      obtain ⟨k', hk', hk'i⟩ := rmin_spec h01 h12 hsol i
      obtain ⟨m, hm⟩ := isSol_diff h01 h12 hk hk'
      exact ⟨m, by rw [← hk'i, hm i]⟩
    obtain ⟨m0, hm0⟩ := hm 0
    obtain ⟨m1, hm1⟩ := hm 1
    obtain ⟨m2, hm2⟩ := hm 2
    have hv1 : vv x 1 < 0 := by rw [h1]; omega
    have hb0 := hbd 0
    have hb1 := hbd 1
    have hb2 := hbd 2
    rw [ht 0] at hb0
    rw [ht 1] at hb1
    rw [ht 2] at hb2
    have hm0R : ((rmin x n μ 0 : ℤ) : ℝ) = k 0 + m0 * vv x 0 := by exact_mod_cast hm0
    have hm1R : ((rmin x n μ 1 : ℤ) : ℝ) = k 1 + m1 * vv x 1 := by exact_mod_cast hm1
    have hm2R : ((rmin x n μ 2 : ℤ) : ℝ) = k 2 + m2 * vv x 2 := by exact_mod_cast hm2
    push_cast at hm0R hm1R hm2R
    have hv0R : (0 : ℝ) < vv x 0 := by exact_mod_cast h0p
    have hv2R : (0 : ℝ) < vv x 2 := by exact_mod_cast h2p
    have hv1R : (vv x 1 : ℝ) < 0 := by exact_mod_cast hv1
    have ht0 : (m0 : ℝ) ≤ t := by
      by_contra hc; push Not at hc; nlinarith
    have ht2 : (m2 : ℝ) ≤ t := by
      by_contra hc; push Not at hc; nlinarith
    have ht1 : t ≤ (m1 : ℝ) := by
      by_contra hc; push Not at hc; nlinarith
    -- the points k + m v with m0, m2 ≤ m ≤ m1 are count vectors
    have hpt : ∀ m : ℤ, m0 ≤ m → m2 ≤ m → m ≤ m1 →
        (fun i => ((k i + m * vv x i : ℤ) : ℝ) / n) ∈ convexHull ℝ
          ((fun k : Fin 3 → ℕ => fun i => (k i : ℝ) / n) ''
            countVecs (fun i => (x i : ℝ)) n (n * μ)) := by
      intro m hm0' hm2' hm1'
      have hnn : ∀ i, 0 ≤ k i + m * vv x i := by
        have r0 : (0 : ℤ) ≤ rmin x n μ 0 := Int.natCast_nonneg _
        have r1 : (0 : ℤ) ≤ rmin x n μ 1 := Int.natCast_nonneg _
        have r2 : (0 : ℤ) ≤ rmin x n μ 2 := Int.natCast_nonneg _
        have e0 : 0 ≤ k 0 + m * vv x 0 := by nlinarith
        have e1 : 0 ≤ k 1 + m * vv x 1 := by nlinarith
        have e2 : 0 ≤ k 2 + m * vv x 2 := by nlinarith
        intro i; fin_cases i
        exacts [e0, e1, e2]
      have hs := isSol_add h01 h12 hk m
      apply subset_convexHull
      refine ⟨fun i => (k i + m * vv x i).toNat, ⟨?_, ?_⟩, ?_⟩
      · have := hs.1
        have h' : ((∑ i, (k i + m * vv x i).toNat : ℕ) : ℤ) = n := by
          push_cast; simp_rw [Int.toNat_of_nonneg (hnn _)]; exact this
        exact_mod_cast h'
      · have := hs.2
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h' : (((k i + m * vv x i).toNat : ℕ) : ℝ) = ((k i + m * vv x i : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (hnn i)]
        rw [h']
      · funext i
        simp only
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (hnn i)]
    have hfi : ∀ i, f i = ((k i : ℝ) + t * vv x i) / n := by
      intro i; rw [← ht i]; field_simp
    have hfl0 : m0 ≤ ⌊t⌋ := Int.le_floor.2 ht0
    have hfl2 : m2 ≤ ⌊t⌋ := Int.le_floor.2 ht2
    have hfl1 : ⌊t⌋ ≤ m1 := by
      have : (⌊t⌋ : ℝ) ≤ m1 := (Int.floor_le t).trans ht1
      exact_mod_cast this
    by_cases hfr : Int.fract t = 0
    · have htf : t = ⌊t⌋ := by
        have := Int.floor_add_fract t; rw [hfr, add_zero] at this; exact this.symm
      convert hpt ⌊t⌋ hfl0 hfl2 hfl1 using 1
      funext i
      conv_lhs => rw [hfi i, htf]
      push_cast; ring
    · have hlt : (⌊t⌋ : ℝ) < t := by
        rcases (Int.floor_le t).lt_or_eq with h | h
        · exact h
        · exact absurd (show Int.fract t = 0 by unfold Int.fract; linarith) hfr
      have hfl1' : ⌊t⌋ + 1 ≤ m1 := by
        have : (⌊t⌋ : ℝ) < m1 := lt_of_lt_of_le hlt ht1
        have : ⌊t⌋ < m1 := by exact_mod_cast this
        omega
      have hp := hpt ⌊t⌋ hfl0 hfl2 hfl1
      have hq := hpt (⌊t⌋ + 1) (by omega) (by omega) hfl1'
      have hφ0 := Int.fract_nonneg t
      have hφ1 := Int.fract_lt_one t
      have hcomb := (convex_convexHull ℝ _) hp hq (by linarith : 0 ≤ 1 - Int.fract t) hφ0
        (by ring)
      convert hcomb using 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hfi i, show Int.fract t = t - ⌊t⌋ from rfl]
      push_cast
      field_simp
      ring

lemma range_012 :
    Set.range (fun i : Fin 3 => (((![0, 1, 2] : Fin 3 → ℤ) i : ℤ) : ℝ)) = {0, 1, 2} := by
  ext v; simp [Fin.exists_fin_succ, eq_comm]

/-- Proposition `lt:prop:three`, the points `0, 1, 2`: a distribution on `{0,1,2}` is
`n`-completely mixable if and only if `M = nμ` is an integer and either `M` is even or
`f₁ ≥ 1/n`. -/
theorem three_012 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : F ({0, 1, 2} : Set ℝ)ᶜ = 0)
    {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n F ↔
      ∃ M : ℤ, (n : ℝ) * ∫ t, t ∂F = M ∧ (Even M ∨ (1 : ℝ) / n ≤ (F {1}).toReal) := by
  set x : Fin 3 → ℤ := ![0, 1, 2] with hxdef
  have h01 : x 0 < x 1 := by simp [x]
  have h12 : x 1 < x 2 := by simp [x]
  have hF' : F (Set.range (fun i => (x i : ℝ)))ᶜ = 0 := by rw [range_012]; exact hF
  rw [three_cm_iff h01 h12 F hF' hn]
  set μ := ∫ t, t ∂F
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : ((x 0 : ℤ) : ℝ) = 0 := by simp [x]
  have hx1 : ((x 1 : ℤ) : ℝ) = 1 := by simp [x]
  have hx2 : ((x 2 : ℤ) : ℝ) = 2 := by simp [x]
  have hsolM : ∀ k, IsSol x n μ k → (n : ℝ) * μ = ((k 1 + 2 * k 2 : ℤ) : ℝ) := by
    intro k hk
    have := hk.2
    simp only [Fin.sum_univ_three, hx0, hx1, hx2] at this
    push_cast; linarith
  have mkSol : ∀ M : ℤ, (n : ℝ) * μ = M → ∀ k0 k1 k2 : ℤ, k0 + k1 + k2 = n →
      k1 + 2 * k2 = M → IsSol x n μ ![k0, k1, k2] := by
    intro M hM k0 k1 k2 hs hk
    refine ⟨by simpa [Fin.sum_univ_three] using hs, ?_⟩
    simp only [Fin.sum_univ_three, hx0, hx1, hx2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [hM, ← hk]; push_cast; ring
  have rle : ∀ k, IsSol x n μ k → ∀ i, 0 ≤ k i → (rmin x n μ i : ℝ) ≤ k i := by
    intro k hk i hi
    exact_mod_cast rmin_le hk hi
  constructor
  · rintro ⟨⟨k, hk⟩, hb⟩
    refine ⟨k 1 + 2 * k 2, hsolM k hk, ?_⟩
    by_cases hev : Even (k 1 + 2 * k 2)
    · exact Or.inl hev
    · right
      obtain ⟨k', hk', hk'1⟩ := rmin_spec h01 h12 ⟨k, hk⟩ 1
      have hne : rmin x n μ 1 ≠ 0 := by
        intro h0
        rw [h0] at hk'1
        have e := (hsolM k hk).symm.trans (hsolM k' hk')
        have e' : k 1 + 2 * k 2 = k' 1 + 2 * k' 2 := by exact_mod_cast e
        apply hev
        rw [e', hk'1]
        exact ⟨k' 2, by ring⟩
      have h1 : (1 : ℝ) ≤ rmin x n μ 1 := by
        have : 1 ≤ rmin x n μ 1 := Nat.one_le_iff_ne_zero.2 hne
        exact_mod_cast this
      have := hb 1
      rw [hx1] at this
      rw [div_le_iff₀ hnR]
      linarith
  · rintro ⟨M, hM, hpar⟩
    refine ⟨⟨_, mkSol M hM 0 (2 * n - M) (M - n) (by ring) (by ring)⟩, fun i => ?_⟩
    have hf0 : ∀ v : ℝ, 0 ≤ (F {v}).toReal := fun v => ENNReal.toReal_nonneg
    fin_cases i
    · have := rle _ (mkSol M hM 0 (2 * n - M) (M - n) (by ring) (by ring)) 0 (by simp)
      simp at this
      show (rmin x n μ 0 : ℝ) ≤ n * (F {((x 0 : ℤ) : ℝ)}).toReal
      rw [this]; push_cast; exact mul_nonneg hnR.le (hf0 _)
    · show (rmin x n μ 1 : ℝ) ≤ n * (F {((x 1 : ℤ) : ℝ)}).toReal
      rw [hx1]
      rcases Int.even_or_odd M with ⟨r, hr⟩ | ⟨r, hr⟩
      · have := rle _ (mkSol M hM (n - r) 0 r (by ring) (by rw [hr]; ring)) 1 (by simp)
        simp at this
        rw [this]; push_cast; exact mul_nonneg hnR.le (hf0 _)
      · have hf1 : (1 : ℝ) / n ≤ (F {1}).toReal := by
          rcases hpar with ⟨r', hr'⟩ | hf1
          · exfalso; omega
          · exact hf1
        have := rle _ (mkSol M hM (n - 1 - r) 1 r (by ring) (by rw [hr]; ring)) 1 (by simp)
        simp at this
        have h1' : (rmin x n μ 1 : ℝ) ≤ 1 := by exact_mod_cast this
        rw [div_le_iff₀ hnR] at hf1
        linarith
    · have := rle _ (mkSol M hM (n - M) M 0 (by ring) (by ring)) 2 (by simp)
      simp at this
      show (rmin x n μ 2 : ℝ) ≤ n * (F {((x 2 : ℤ) : ℝ)}).toReal
      rw [this]; push_cast; exact mul_nonneg hnR.le (hf0 _)

lemma sum_fin2_bool (h : (Fin 2 → Bool) → ℝ) :
    ∑ ε, h ε = h ![true, true] + h ![true, false] + h ![false, true] + h ![false, false] := by
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp]
  simp [Fintype.sum_prod_type]
  ring

/-- Proposition `lt:prop:three`, the binomial distribution `B(2, p)`, `0 < p < 1`: it is
`n`-completely mixable if and only if `2np` is an integer and `2 ≤ 2np ≤ 2n - 2`. -/
theorem binom2_cm_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (binom 2 p) ↔
      (∃ m : ℤ, 2 * n * p = m) ∧ 2 ≤ 2 * n * p ∧ 2 * n * p ≤ 2 * n - 2 := by
  have hq : ∀ _ : Fin 2, 0 ≤ p ∧ p ≤ 1 := fun _ => ⟨hp0.le, hp1.le⟩
  have : IsProbabilityMeasure (binom 2 p) := pbLaw_isProb hq
  have hw0 := pbW_nonneg hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  -- carried by {0,1,2}
  have hF : binom 2 p ({0, 1, 2} : Set ℝ)ᶜ = 0 := by
    rw [binom, pbLaw, law_apply_real hw0 _ (by measurability)]
    simp only [sum_fin2_bool, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, ind]
    norm_num
  have hmean : ∫ t, t ∂(binom 2 p) = 2 * p := by
    rw [binom, pbLaw, integral_law hw0]
    simp only [sum_fin2_bool, Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, ind, bern]
    norm_num; ring
  have hf1 : (binom 2 p {1}).toReal = 2 * p * (1 - p) := by
    rw [binom, pbLaw, law_singleton hw0, ENNReal.toReal_ofReal (mass_nonneg hw0 _ _)]
    simp only [mass, sum_fin2_bool, Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, ind, bern]
    norm_num; ring
  rw [three_012 _ hF (by omega), hmean]
  constructor
  · rintro ⟨M, hM, hpar⟩
    have hM' : 2 * (n : ℝ) * p = M := by linarith
    refine ⟨⟨M, hM'⟩, ?_⟩
    have hMpos : (0 : ℝ) < M := by rw [← hM']; positivity
    have hMlt : (M : ℝ) < 2 * n := by rw [← hM']; nlinarith
    have hMpos' : 0 < M := by exact_mod_cast hMpos
    have hMlt' : M < 2 * n := by exact_mod_cast hMlt
    rcases hpar with ⟨r, hr⟩ | h1
    · have h2 : 2 ≤ M := by omega
      have h3 : M ≤ 2 * n - 2 := by omega
      rw [hM']
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩
    · rw [hf1] at h1
      have hp : p = M / (2 * n) := by field_simp; linarith
      rw [hp] at h1
      have hn0 : (0 : ℝ) < n := by linarith
      have key : 2 * (n : ℝ) ≤ M * (2 * n - M) := by
        rw [div_le_iff₀ hn0] at h1
        field_simp at h1
        nlinarith
      have h2 : 2 ≤ M := by
        by_contra hc
        have : M = 1 := by omega
        rw [this] at key; push_cast at key; linarith
      have h3 : M ≤ 2 * n - 2 := by
        by_contra hc
        have : M = 2 * n - 1 := by omega
        rw [this] at key; push_cast at key; nlinarith
      rw [hM']
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩
  · rintro ⟨⟨M, hM'⟩, h2, h3⟩
    refine ⟨M, by linarith, ?_⟩
    rcases Int.even_or_odd M with hev | hodd
    · exact Or.inl hev
    · right
      rw [hf1]
      have hn0 : (0 : ℝ) < n := by linarith
      have hp : p = M / (2 * n) := by field_simp; linarith
      rw [hM'] at h2 h3
      rw [hp, div_le_iff₀ hn0]
      field_simp
      nlinarith

end Three

end Mixes.LatticeBasic
