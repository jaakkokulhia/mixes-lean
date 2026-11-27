import Mixes.Homothetic
import Mixes.Joint
import Mixes.SlabsMix
import Mixes.Uniform

open MeasureTheory Finset
open scoped Classical

noncomputable section

namespace Mixes.NormAtom

section General

variable {E : Type*} [AddCommGroup E] {n : ℕ}

/-- `I₁ + ⋯ + Iₙ`: the set of the sums `x₁ + ⋯ + xₙ` with `xᵢ ∈ Iᵢ`. -/
def sumSet (I : Fin n → Set E) : Set E :=
  {y | ∃ x : Fin n → E, (∀ i, x i ∈ I i) ∧ ∑ i, x i = y}

/-- `J_j = s - ∑_{i ≠ j} I_i`: the points `s - ∑_{i ≠ j} xᵢ` with `xᵢ ∈ Iᵢ` for `i ≠ j`. -/
def peakJ (s : E) (I : Fin n → Set E) (j : Fin n) : Set E :=
  {y | ∃ x : Fin n → E, (∀ i, i ≠ j → x i ∈ I i) ∧ y = s - ∑ i ∈ univ.erase j, x i}

/-- The counting inequality behind Lemma `nc:lem:peak`: if `∑ xᵢ = s ∉ ∑ Iᵢ`, then the number
`A` of indices with `xᵢ ∈ Iᵢ` and the number `B` of indices with `x_j ∈ J_j \ I_j` satisfy
`A ≤ n - 2 + B`, written `A + 2 ≤ n + B`. -/
theorem count_peak (s : E) (I : Fin n → Set E) (hs : s ∉ sumSet I) (x : Fin n → E)
    (hx : ∑ i, x i = s) :
    (univ.filter fun i => x i ∈ I i).card + 2 ≤
      n + (univ.filter fun j => x j ∈ peakJ s I j \ I j).card := by
  classical
  set A := (univ.filter fun i => x i ∈ I i).card with hA
  set B := (univ.filter fun j => x j ∈ peakJ s I j \ I j).card
  have hAn : A ≤ n := by
    simpa using Finset.card_filter_le (univ : Finset (Fin n)) (fun i => x i ∈ I i)
  have hAne : A ≠ n := by
    intro h
    apply hs
    refine ⟨x, fun i => ?_, hx⟩
    have : (univ.filter fun i => x i ∈ I i) = univ := by
      apply Finset.eq_univ_of_card; simpa using h
    have hi : i ∈ (univ.filter fun i => x i ∈ I i) := by rw [this]; exact mem_univ i
    exact (Finset.mem_filter.1 hi).2
  by_contra hlt
  push Not at hlt
  have hB : B = 0 := by omega
  have hA1 : A = n - 1 := by omega
  have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => x i ∈ I i)
  rw [card_univ, Fintype.card_fin, ← hA] at hc
  have h1 : (univ.filter fun i => ¬ x i ∈ I i).card = 1 := by omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h1
  have hjI : x j ∉ I j := by
    have : j ∈ (univ.filter fun i => ¬ x i ∈ I i) := by rw [hj]; exact Finset.mem_singleton_self j
    exact (Finset.mem_filter.1 this).2
  have hother : ∀ i, i ≠ j → x i ∈ I i := by
    intro i hij
    by_contra hi
    have : i ∈ (univ.filter fun i => ¬ x i ∈ I i) := Finset.mem_filter.2 ⟨mem_univ i, hi⟩
    rw [hj, Finset.mem_singleton] at this
    exact hij this
  have hjJ : x j ∈ peakJ s I j := by
    refine ⟨x, hother, ?_⟩
    rw [← hx, ← Finset.add_sum_erase univ x (mem_univ j)]
    abel
  have : j ∈ (univ.filter fun j => x j ∈ peakJ s I j \ I j) :=
    Finset.mem_filter.2 ⟨mem_univ j, hjJ, hjI⟩
  have : 0 < B := Finset.card_pos.2 ⟨j, this⟩
  omega


/-- The pointwise form of the counting inequality, with indicator functions in `ℝ≥0∞`; `T` is any
set containing the event `∑ xᵢ ≠ s`. -/
theorem count_peak_indicator (s : E) (I : Fin n → Set E) (hs : s ∉ sumSet I) (hn : 2 ≤ n)
    (T : Set (Fin n → E)) (hT : {x | ∑ i, x i ≠ s} ⊆ T) (x : Fin n → E) :
    ∑ i, (I i).indicator (1 : E → ENNReal) (x i) ≤
      ((n - 2 : ℕ) : ENNReal) + ∑ j, (peakJ s I j \ I j).indicator (1 : E → ENNReal) (x j) +
        2 * T.indicator 1 x := by
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, Finset.sum_boole]
  by_cases hx : ∑ i, x i = s
  · have h := count_peak s I hs x hx
    have h' : ((univ.filter fun i => x i ∈ I i).card : ENNReal) ≤
        ((n - 2 : ℕ) : ENNReal) + ((univ.filter fun j => x j ∈ peakJ s I j \ I j).card : ENNReal) := by
      exact_mod_cast (by omega : (univ.filter fun i => x i ∈ I i).card ≤
        (n - 2) + (univ.filter fun j => x j ∈ peakJ s I j \ I j).card)
    exact h'.trans le_self_add
  · have hxT : x ∈ T := hT hx
    simp only [hxT, ite_true, mul_one]
    have h1 : (univ.filter fun i => x i ∈ I i).card ≤ n := by
      simpa using Finset.card_filter_le (univ : Finset (Fin n)) (fun i => x i ∈ I i)
    have h2 : ((univ.filter fun i => x i ∈ I i).card : ENNReal) ≤ ((n - 2 : ℕ) : ENNReal) + 2 := by
      exact_mod_cast (by omega : (univ.filter fun i => x i ∈ I i).card ≤ (n - 2) + 2)
    refine h2.trans ?_
    gcongr
    exact le_self_add

variable [MeasurableSpace E]

/-- **Lemma `nc:lem:peak`**, inequality (`nc:eq:peak`) in `ℝ≥0∞`, for an arbitrary measurable
additive group: if `P` is a probability measure on `n`-tuples with marginals `F i`, `n ≥ 2`, the
`Iᵢ` and `J_j` are measurable and `s ∉ I₁ + ⋯ + Iₙ`, then
`∑ᵢ Fᵢ(Iᵢ) ≤ (n - 2) + ∑ⱼ Fⱼ(Jⱼ \ Iⱼ) + 2 P(∑ xᵢ ≠ s)`. -/
theorem peak_ennreal (P : Measure (Fin n → E)) [IsProbabilityMeasure P] (F : Fin n → Measure E)
    (hm : ∀ i, P.map (fun x => x i) = F i) (hn : 2 ≤ n) (s : E) (I : Fin n → Set E)
    (hI : ∀ i, MeasurableSet (I i)) (hJ : ∀ j, MeasurableSet (peakJ s I j)) (hs : s ∉ sumSet I) :
    ∑ i, F i (I i) ≤ ((n - 2 : ℕ) : ENNReal) + ∑ j, F j (peakJ s I j \ I j) +
      2 * P {x | ∑ i, x i ≠ s} := by
  set S := {x : Fin n → E | ∑ i, x i ≠ s}
  have hT := measurableSet_toMeasurable P S
  have hcoord : ∀ (j : Fin n) (A : Set E), MeasurableSet A →
      ∫⁻ x, A.indicator (1 : E → ENNReal) (x j) ∂P = F j A := by
    intro j A hA
    rw [← hm j, ← lintegral_indicator_one hA,
      lintegral_map (measurable_one.indicator hA) (measurable_pi_apply j)]
  have hmeas : ∀ (j : Fin n) (A : Set E), MeasurableSet A →
      Measurable fun x : Fin n → E => A.indicator (1 : E → ENNReal) (x j) :=
    fun j A hA => (measurable_one.indicator hA).comp (measurable_pi_apply j)
  have key := lintegral_mono (μ := P) (count_peak_indicator s I hs hn (toMeasurable P S)
    (subset_toMeasurable P S))
  rw [lintegral_finsetSum _ fun i _ => hmeas i (I i) (hI i)] at key
  rw [lintegral_add_left (by
      exact (measurable_const.add (Finset.measurable_sum _ fun j _ =>
        hmeas j _ ((hJ j).diff (hI j))))), lintegral_add_left measurable_const,
    lintegral_finsetSum _ fun j _ => hmeas j _ ((hJ j).diff (hI j)),
    lintegral_const_mul _ (measurable_one.indicator hT), lintegral_indicator_one hT,
    measure_toMeasurable, lintegral_const, measure_univ, mul_one] at key
  simpa only [hcoord _ _ (hI _), hcoord _ _ ((hJ _).diff (hI _))] using key


/-- **Lemma `nc:lem:peak`**, inequality (`nc:eq:peak`) in real numbers:
`P(∑ xᵢ ≠ s) ≥ (∑ᵢ Fᵢ(Iᵢ) - ∑ⱼ Fⱼ(Jⱼ \ Iⱼ) - (n - 2)) / 2`. -/
theorem peak_real (P : Measure (Fin n → E)) [IsProbabilityMeasure P] (F : Fin n → Measure E)
    (hm : ∀ i, P.map (fun x => x i) = F i) (hn : 2 ≤ n) (s : E) (I : Fin n → Set E)
    (hI : ∀ i, MeasurableSet (I i)) (hJ : ∀ j, MeasurableSet (peakJ s I j)) (hs : s ∉ sumSet I) :
    (1 / 2 : ℝ) * (∑ i, (F i (I i)).toReal - ∑ j, (F j (peakJ s I j \ I j)).toReal - (n - 2)) ≤
      (P {x | ∑ i, x i ≠ s}).toReal := by
  have hF : ∀ i, IsProbabilityMeasure (F i) := fun i => by
    rw [← hm i]; exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply i).aemeasurable).2 inferInstance
  have key := peak_ennreal P F hm hn s I hI hJ hs
  have hfin : ((n - 2 : ℕ) : ENNReal) + ∑ j, F j (peakJ s I j \ I j) +
      2 * P {x | ∑ i, x i ≠ s} ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _,
      ENNReal.sum_ne_top.2 fun j _ => measure_ne_top _ _⟩,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)⟩
  have h := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_sum fun i _ => measure_ne_top _ _, ENNReal.toReal_add (ENNReal.add_ne_top.2
      ⟨ENNReal.natCast_ne_top _, ENNReal.sum_ne_top.2 fun j _ => measure_ne_top _ _⟩)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_add (ENNReal.natCast_ne_top _) (ENNReal.sum_ne_top.2 fun j _ => measure_ne_top _ _),
    ENNReal.toReal_sum fun j _ => measure_ne_top _ _, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, Nat.cast_sub hn] at h
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat] at h
  linarith

/-- **Lemma `nc:lem:peak`**, joint mixes: if `P` is a joint mix of `F₁, …, Fₙ` with sum `s`,
then `∑ᵢ Fᵢ(Iᵢ) ≤ n - 2 + ∑ⱼ Fⱼ(Jⱼ \ Iⱼ)`. -/
theorem peak_jointMix {F : Fin n → Measure E} {P : Measure (Fin n → E)} (hP : IsJointMix F P)
    {s : E} (hsum : ∀ᵐ x ∂P, ∑ i, x i = s) (hn : 2 ≤ n) (I : Fin n → Set E)
    (hI : ∀ i, MeasurableSet (I i)) (hJ : ∀ j, MeasurableSet (peakJ s I j)) (hs : s ∉ sumSet I) :
    ∑ i, F i (I i) ≤ ((n - 2 : ℕ) : ENNReal) + ∑ j, F j (peakJ s I j \ I j) := by
  have := hP.1
  have key := peak_ennreal P F hP.2.2 hn s I hI hJ hs
  have h0 : P {x | ∑ i, x i ≠ s} = 0 := by simpa using (ae_iff.1 hsum)
  rwa [h0, mul_zero, add_zero] at key

/-- The real form of `peak_jointMix`. -/
theorem peak_jointMix_real {F : Fin n → Measure E} {P : Measure (Fin n → E)} (hP : IsJointMix F P)
    {s : E} (hsum : ∀ᵐ x ∂P, ∑ i, x i = s) (hn : 2 ≤ n) (I : Fin n → Set E)
    (hI : ∀ i, MeasurableSet (I i)) (hJ : ∀ j, MeasurableSet (peakJ s I j)) (hs : s ∉ sumSet I) :
    ∑ i, (F i (I i)).toReal ≤ (n - 2 : ℝ) + ∑ j, (F j (peakJ s I j \ I j)).toReal := by
  have := hP.1
  have h := peak_real P F hP.2.2 hn s I hI hJ hs
  have h0 : P {x | ∑ i, x i ≠ s} = 0 := by simpa using (ae_iff.1 hsum)
  rw [h0, ENNReal.toReal_zero] at h
  linarith


omit [MeasurableSpace E] in
/-- `J_j` is the image of a product of compact sets, hence compact. -/
theorem isCompact_peakJ [TopologicalSpace E] [IsTopologicalAddGroup E] (s : E) (I : Fin n → Set E)
    (hI : ∀ i, IsCompact (I i)) (j : Fin n) : IsCompact (peakJ s I j) := by
  classical
  have hK : IsCompact (Set.pi Set.univ (Function.update I j {0})) := by
    refine isCompact_univ_pi fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hI i
  have heq : peakJ s I j = (fun x : Fin n → E => s - ∑ i ∈ univ.erase j, x i) ''
      Set.pi Set.univ (Function.update I j {0}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Function.update x j 0, fun i _ => ?_, ?_⟩
      · by_cases h : i = j
        · subst h; simp
        · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hx i h
      · simp only
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, fun i hij => ?_, rfl⟩
      have := hx i (Set.mem_univ i)
      rwa [Function.update_of_ne hij] at this
  rw [heq]
  exact hK.image (continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i))

/-- **Lemma `nc:lem:peak`** as stated in the paper, for compact sets in a Hausdorff topological
additive group with a Borel-type measurable structure (such as `ℝ^d`): every probability measure
`P` on `n`-tuples with marginals `Fᵢ` satisfies
`P(∑ xᵢ ≠ s) ≥ (∑ᵢ Fᵢ(Iᵢ) - ∑ⱼ Fⱼ(Jⱼ \ Iⱼ) - (n - 2)) / 2`. -/
theorem peak [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [OpensMeasurableSpace E]
    (P : Measure (Fin n → E)) [IsProbabilityMeasure P] (F : Fin n → Measure E)
    (hm : ∀ i, P.map (fun x => x i) = F i) (hn : 2 ≤ n) (s : E) (I : Fin n → Set E)
    (hI : ∀ i, IsCompact (I i)) (hs : s ∉ sumSet I) :
    (1 / 2 : ℝ) * (∑ i, (F i (I i)).toReal - ∑ j, (F j (peakJ s I j \ I j)).toReal - (n - 2)) ≤
      (P {x | ∑ i, x i ≠ s}).toReal :=
  peak_real P F hm hn s I (fun i => (hI i).measurableSet)
    (fun j => (isCompact_peakJ s I hI j).measurableSet) hs

/-- **Lemma `nc:lem:peak`**, first consequence, as in the paper: if `F₁, …, Fₙ` are jointly
mixable with sum `s` and the `Iᵢ` are compact with `s ∉ ∑ Iᵢ`, then
`∑ᵢ Fᵢ(Iᵢ) ≤ n - 2 + ∑ⱼ Fⱼ(Jⱼ \ Iⱼ)`. -/
theorem peak_jointlyMixable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [OpensMeasurableSpace E] {F : Fin n → Measure E} {P : Measure (Fin n → E)}
    (hP : IsJointMix F P) {s : E} (hsum : ∀ᵐ x ∂P, ∑ i, x i = s) (hn : 2 ≤ n)
    (I : Fin n → Set E) (hI : ∀ i, IsCompact (I i)) (hs : s ∉ sumSet I) :
    ∑ i, (F i (I i)).toReal ≤ (n - 2 : ℝ) + ∑ j, (F j (peakJ s I j \ I j)).toReal :=
  peak_jointMix_real hP hsum hn I (fun i => (hI i).measurableSet)
    (fun j => (isCompact_peakJ s I hI j).measurableSet) hs


omit [MeasurableSpace E] in
/-- For equal sets, `J_j = s - (n-1) I` for every `j`. -/
theorem peakJ_const {m : ℕ} (s : E) (I : Set E) (j : Fin (m + 1)) :
    peakJ s (fun _ => I) j = (fun y => s - y) '' sumSet (fun _ : Fin m => I) := by
  have hsum : ∀ x : Fin (m + 1) → E, ∑ i ∈ univ.erase j, x i = ∑ k : Fin m, x (j.succAbove k) := by
    intro x
    have h1 := Finset.add_sum_erase univ x (mem_univ j)
    rw [Fin.sum_univ_succAbove x j] at h1
    exact add_left_cancel h1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨∑ k : Fin m, x (j.succAbove k), ⟨fun k => x (j.succAbove k),
      fun k => hx _ (Fin.succAbove_ne j k), rfl⟩, by rw [hsum]⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Fin.insertNth j 0 z, fun i hij => ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
      rw [Fin.insertNth_apply_succAbove]; exact hz k
    · rw [hsum]; simp [Fin.insertNth_apply_succAbove]

end General

section CompleteMix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {n : ℕ}

/-- **Lemma `nc:lem:peak`**, last statement: if `F` is `n`-completely mixable with mean `μ`, and
`I` is a compact set for which `n μ` is not the sum of `n` points of `I`, then
`F(I) ≤ 1 - 2/n + F(J \ I)` with `J = n μ - (n-1) I`. -/
theorem peak_completelyMixable (hn : 2 ≤ n) {F : Measure E} (hF : CompletelyMixable n F)
    (hint : Integrable id F) {μ : E} (hμ : ∫ x, x ∂F = μ) {I : Set E} (hI : IsCompact I)
    (hs : (n • μ) ∉ sumSet (fun _ : Fin n => I)) :
    (F I).toReal ≤ 1 - 2 / n +
      (F ((fun y => n • μ - y) '' sumSet (fun _ : Fin (n - 1) => I) \ I)).toReal := by
  obtain ⟨P, hP⟩ := hF
  have hsum : ∀ᵐ x ∂P, ∑ i, x i = n • μ := by
    filter_upwards [Mixes.Homothetic.IsJointMix.ae_sum_eq hP fun _ => hint] with x hx
    rw [hx]; simp [hμ]
  have h := peak_jointlyMixable hP hsum hn (fun _ => I) (fun _ => hI) hs
  have hJ : ∀ j : Fin n, peakJ (n • μ) (fun _ => I) j =
      (fun y => n • μ - y) '' sumSet (fun _ : Fin (n - 1) => I) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    intro j
    rw [peakJ_const]
    rfl
  simp only [hJ, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine le_of_mul_le_mul_left ?_ hn0
  rw [mul_add, mul_sub, mul_div_cancel₀ _ hn0.ne', mul_one]
  linarith

end CompleteMix

/-- **Lemma `nc:lem:peak`** for an interval `I = [u, v]` of the line with `μ ∉ I`: an
`n`-completely mixable `F` with mean `μ` has `F([u, v]) ≤ 1 - 2/n + F(J \ [u, v])`, where
`J = [n μ - (n-1) v, n μ - (n-1) u]`. -/
theorem peak_interval {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF : CompletelyMixable n F)
    (hint : Integrable id F) {μ : ℝ} (hμ : ∫ x, x ∂F = μ) {u v : ℝ}
    (hμI : μ ∉ Set.Icc u v) :
    (F (Set.Icc u v)).toReal ≤ 1 - 2 / n +
      (F (Set.Icc (n * μ - (n - 1) * v) (n * μ - (n - 1) * u) \ Set.Icc u v)).toReal := by
  have hprob : IsProbabilityMeasure F := by
    obtain ⟨P, hP⟩ := hF
    have := hP.1
    have h := hP.2.2 ⟨0, by omega⟩
    simp only at h
    rw [← h]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  have hs : (n • μ) ∉ sumSet (fun _ : Fin n => Set.Icc u v) := by
    rintro ⟨x, hx, hxs⟩
    apply hμI
    have h1 : ∑ i : Fin n, u ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => (hx i).1
    have h2 : ∑ i, x i ≤ ∑ i : Fin n, v := Finset.sum_le_sum fun i _ => (hx i).2
    simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2 hxs
    rw [hxs] at h1 h2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact ⟨le_of_mul_le_mul_left h1 hn0, le_of_mul_le_mul_left h2 hn0⟩
  have h := peak_completelyMixable hn hF hint hμ isCompact_Icc hs
  refine h.trans ?_
  gcongr
  · exact measure_ne_top _ _
  · rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h2 : ∑ i, x i ≤ ∑ i : Fin (n - 1), v := Finset.sum_le_sum fun i _ => (hx i).2
      simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h2 ⊢
      linarith
    · have h1 : ∑ i : Fin (n - 1), u ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => (hx i).1
      simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h1 ⊢
      linarith


/-! ### Lemma `nc:lem:count` -/

/-- The counting inequality in the proof of Lemma `nc:lem:count`: if `x₁, …, xₙ ≤ b` have sum
`n μ`, `v < μ`, `1 ≤ r ≤ n - 1` and `(n - r + 1) v + (r - 1) b < n μ`, then the number `A` of
points in `[u, v]` and the number `B` of points in `[w, b]`, `w = (n μ - (n - r) v)/r`, satisfy
`A ≤ n - r - 1 + B`, written `A + r + 1 ≤ n + B`. -/
theorem count_le {n r : ℕ} {μ b u v : ℝ} (hv : v < μ) (hr1 : 1 ≤ r) (hrn : r ≤ n - 1)
    (hcond : ((n : ℝ) - r + 1) * v + ((r : ℝ) - 1) * b < n * μ) (x : Fin n → ℝ)
    (hxb : ∀ i, x i ≤ b) (hx : ∑ i, x i = n * μ) :
    (univ.filter fun i => x i ∈ Set.Icc u v).card + r + 1 ≤
      n + (univ.filter fun i => x i ∈ Set.Icc ((n * μ - (n - r) * v) / r) b).card := by
  classical
  set SA := univ.filter fun i => x i ∈ Set.Icc u v with hSA
  set SR := univ.filter fun i => ¬ x i ∈ Set.Icc u v with hSR
  set w := (n * μ - (n - r) * v) / r with hw
  set A := SA.card
  have hc : A + SR.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i => x i ∈ Set.Icc u v)
    rw [card_univ, Fintype.card_fin] at this
    exact this
  have hsplit : ∑ i ∈ SA, x i + ∑ i ∈ SR, x i = n * μ := by
    rw [Finset.sum_filter_add_sum_filter_not, hx]
  have hn1 : 1 ≤ n := by omega
  have hμb : μ ≤ b := by
    have : ∑ i, x i ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => hxb i
    simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hx] at this
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    exact le_of_mul_le_mul_left this hn0
  have hvb : v ≤ b := by linarith
  have hSAsum : ∑ i ∈ SA, x i ≤ A * v := by
    have := Finset.sum_le_sum (s := SA) (g := fun _ => v) fun i hi => (Finset.mem_filter.1 hi).2.2
    simpa using this
  have hSRsum : ∑ i ∈ SR, x i ≤ SR.card * b := by
    have := Finset.sum_le_sum (s := SR) (g := fun _ => b) fun i _ => hxb i
    simpa using this
  have hAle : A ≤ n - r := by
    by_contra hA
    push Not at hA
    have hA' : ((n : ℝ) - r + 1) ≤ A := by
      have : n - r + 1 ≤ A := by omega
      have h2 : ((n - r + 1 : ℕ) : ℝ) ≤ A := by exact_mod_cast this
      rwa [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one] at h2
    have hcR : (SR.card : ℝ) = n - A := by
      have : (A : ℝ) + SR.card = n := by exact_mod_cast hc
      linarith
    have : n * μ ≤ A * v + (n - A) * b := by rw [← hcR]; linarith
    have : A * v + (n - A) * b ≤ ((n : ℝ) - r + 1) * v + ((r : ℝ) - 1) * b := by nlinarith
    linarith
  by_contra hcon
  push Not at hcon
  have hAeq : A = n - r := by omega
  have hB : (univ.filter fun i => x i ∈ Set.Icc w b) = ∅ := by
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : 0 < (univ.filter fun i => x i ∈ Set.Icc w b).card := Finset.card_pos.2 ⟨i, hi⟩
    omega
  have hlt : ∀ i ∈ SR, x i < w := by
    intro i _
    by_contra h
    push Not at h
    have : i ∈ (univ.filter fun i => x i ∈ Set.Icc w b) :=
      Finset.mem_filter.2 ⟨mem_univ i, h, hxb i⟩
    rw [hB] at this
    exact Finset.notMem_empty i this
  have hSRcard : SR.card = r := by omega
  have hSRne : SR.Nonempty := Finset.card_pos.1 (by omega)
  have hSRlt : ∑ i ∈ SR, x i < ∑ _i ∈ SR, w := Finset.sum_lt_sum_of_nonempty hSRne hlt
  simp only [Finset.sum_const, hSRcard, nsmul_eq_mul] at hSRlt
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrw : (r : ℝ) * w = n * μ - (n - r) * v := by rw [hw]; field_simp
  have hAv : (A : ℝ) = n - r := by rw [hAeq, Nat.cast_sub (by omega)]
  rw [hAv] at hSAsum
  linarith

/-- Taking expectations of a counting inequality that holds almost surely under an `n`-complete
mix of `F`: from `#{i : xᵢ ∈ A} + k ≤ n + #{i : xᵢ ∈ B}` a.s. follows
`F(A) ≤ 1 - k/n + F(B)`. -/
theorem expect_count {n : ℕ} (hn : 1 ≤ n) {F : Measure ℝ} {P : Measure (Fin n → ℝ)}
    (hP : IsCompleteMix n F P) {A B : Set ℝ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hA : MeasurableSet A) (hB : MeasurableSet B) (k : ℕ) (hcount : ∀ᵐ x ∂P, (univ.filter fun i => x i ∈ A).card + k ≤
      n + (univ.filter fun i => x i ∈ B).card) :
    (F A).toReal ≤ 1 - k / n + (F B).toReal := by
  have hPprob := hP.1
  have hm : ∀ i, P.map (fun x => x i) = F := hP.2.2
  have hFprob : IsProbabilityMeasure F := by
    rw [← hm ⟨0, by omega⟩]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  have hcoord : ∀ (j : Fin n) (C : Set ℝ), MeasurableSet C →
      ∫⁻ x, C.indicator (1 : ℝ → ENNReal) (x j) ∂P = F C := by
    intro j C hC
    rw [← hm j, ← lintegral_indicator_one hC,
      lintegral_map (measurable_one.indicator hC) (measurable_pi_apply j)]
  have hmeas : ∀ (j : Fin n) (C : Set ℝ), MeasurableSet C →
      Measurable fun x : Fin n → ℝ => C.indicator (1 : ℝ → ENNReal) (x j) :=
    fun j C hC => (measurable_one.indicator hC).comp (measurable_pi_apply j)
  have hpt : ∀ᵐ x ∂P, ∑ i, A.indicator (1 : ℝ → ENNReal) (x i) + (k : ENNReal) ≤
      (n : ENNReal) + ∑ i, B.indicator (1 : ℝ → ENNReal) (x i) := by
    filter_upwards [hcount] with x hx
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole, Finset.sum_boole]
    exact_mod_cast hx
  have key := lintegral_mono_ae hpt
  rw [lintegral_add_right _ measurable_const, lintegral_finsetSum _ fun i _ => hmeas i A hA,
    lintegral_add_left measurable_const, lintegral_finsetSum _ fun i _ => hmeas i B hB,
    lintegral_const, lintegral_const, measure_univ, mul_one, mul_one] at key
  simp only [hcoord _ _ hA, hcoord _ _ hB, Finset.sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at key
  have hfin : (n : ENNReal) + n * F B ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)⟩
  have h := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _))
      (ENNReal.natCast_ne_top _), ENNReal.toReal_add (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  simp only [ENNReal.toReal_natCast] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_of_mul_le_mul_left ?_ hn0
  rw [mul_add, mul_sub, mul_div_cancel₀ _ hn0.ne', mul_one]
  linarith

/-- **Lemma `nc:lem:count`**: if `F` is `n`-completely mixable with mean `μ` and carried by
`(-∞, b]`, `u ≤ v < μ`, `1 ≤ r ≤ n - 1` and `(n - r + 1) v + (r - 1) b < n μ`, then
`F([u, v]) ≤ 1 - (r + 1)/n + F([w, b])` with `w = (n μ - (n - r) v)/r`. -/
theorem count_lemma {n r : ℕ} {F : Measure ℝ} (hF : CompletelyMixable n F)
    (hint : Integrable id F) {μ : ℝ} (hμ : ∫ x, x ∂F = μ) {b : ℝ} (hb : F (Set.Ioi b) = 0)
    {u v : ℝ} (huv : u ≤ v) (hv : v < μ) (hr1 : 1 ≤ r) (hrn : r ≤ n - 1)
    (hcond : ((n : ℝ) - r + 1) * v + ((r : ℝ) - 1) * b < n * μ) :
    (F (Set.Icc u v)).toReal ≤
      1 - (r + 1) / n + (F (Set.Icc ((n * μ - (n - r) * v) / r) b)).toReal := by
  obtain ⟨P, hP⟩ := hF
  have hn : 1 ≤ n := by omega
  have hsum : ∀ᵐ x ∂P, ∑ i, x i = n * μ := by
    filter_upwards [Mixes.Homothetic.IsJointMix.ae_sum_eq hP fun _ => hint] with x hx
    rw [hx]; simp [hμ]
  have hle : ∀ᵐ x ∂P, ∀ i, x i ≤ b := by
    rw [ae_all_iff]
    intro i
    have h1 : P {x | b < x i} = 0 := by
      have := hP.2.2 i
      simp only at this
      rw [← hb, ← this, Measure.map_apply (measurable_pi_apply i) measurableSet_Ioi]
      rfl
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx
    simpa using hx
  have h := expect_count hn hP (A := Set.Icc u v)
    (B := Set.Icc ((n * μ - (n - r) * v) / r) b) measurableSet_Icc measurableSet_Icc (r + 1) (by
    filter_upwards [hsum, hle] with x hx hxb
    have := count_le (u := u) hv hr1 hrn hcond x hxb hx
    omega)
  simpa using h

/-- **Lemma `nc:lem:count`**, reflected statement: if `F` is `n`-completely mixable with mean `μ`
and carried by `[a, ∞)`, `μ < u ≤ v`, `1 ≤ r ≤ n - 1` and `(n - r + 1) u + (r - 1) a > n μ`, then
`F([u, v]) ≤ 1 - (r + 1)/n + F([a, w])` with `w = (n μ - (n - r) u)/r`. -/
theorem count_lemma_reflect {n r : ℕ} {F : Measure ℝ} (hF : CompletelyMixable n F)
    (hint : Integrable id F) {μ : ℝ} (hμ : ∫ x, x ∂F = μ) {a : ℝ} (ha : F (Set.Iio a) = 0)
    {u v : ℝ} (huv : u ≤ v) (hu : μ < u) (hr1 : 1 ≤ r) (hrn : r ≤ n - 1)
    (hcond : n * μ < ((n : ℝ) - r + 1) * u + ((r : ℝ) - 1) * a) :
    (F (Set.Icc u v)).toReal ≤
      1 - (r + 1) / n + (F (Set.Icc a ((n * μ - (n - r) * u) / r))).toReal := by
  obtain ⟨P, hP⟩ := hF
  have hn : 1 ≤ n := by omega
  have hsum : ∀ᵐ x ∂P, ∑ i, x i = n * μ := by
    filter_upwards [Mixes.Homothetic.IsJointMix.ae_sum_eq hP fun _ => hint] with x hx
    rw [hx]; simp [hμ]
  have hle : ∀ᵐ x ∂P, ∀ i, a ≤ x i := by
    rw [ae_all_iff]
    intro i
    have h1 : P {x | x i < a} = 0 := by
      have := hP.2.2 i
      simp only at this
      rw [← ha, ← this, Measure.map_apply (measurable_pi_apply i) measurableSet_Iio]
      rfl
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx
    simpa using hx
  have h := expect_count hn hP (A := Set.Icc u v)
    (B := Set.Icc a ((n * μ - (n - r) * u) / r)) measurableSet_Icc measurableSet_Icc (r + 1) (by
    filter_upwards [hsum, hle] with x hx hxa
    have := count_le (n := n) (r := r) (μ := -μ) (b := -a) (u := -v) (v := -u) (by linarith)
      hr1 hrn (by linarith) (fun i => -x i) (fun i => by linarith [hxa i])
      (by rw [Finset.sum_neg_distrib, hx]; ring)
    have e1 : (univ.filter fun i => -x i ∈ Set.Icc (-v) (-u)) =
        univ.filter fun i => x i ∈ Set.Icc u v := by
      ext i; simp only [Finset.mem_filter, Set.mem_Icc]; constructor <;>
        rintro ⟨_, h1, h2⟩ <;> exact ⟨mem_univ i, by linarith, by linarith⟩
    have e2 : (univ.filter fun i => -x i ∈ Set.Icc ((n * -μ - (n - r) * -u) / r) (-a)) =
        univ.filter fun i => x i ∈ Set.Icc a ((n * μ - (n - r) * u) / r) := by
      ext i
      have : (n * -μ - (n - r) * -u) / r = -((n * μ - (n - r) * u) / r) := by ring
      simp only [Finset.mem_filter, Set.mem_Icc, this]
      constructor <;> rintro ⟨_, h1, h2⟩ <;> exact ⟨mem_univ i, by linarith, by linarith⟩
    rw [e1, e2] at this
    omega)
  simpa using h

/-! ### Proposition `nc:prop:atom`: the distribution and part (b) -/


/-- `F₀ = p δ_c + (1 - p) U[0, 1]`, the mixture of a point mass and a uniform distribution of
Proposition `nc:prop:atom`. -/
def atomUnif (p c : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac c + ENNReal.ofReal (1 - p) • unifI 0 1

lemma atomUnif_isProb {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (atomUnif p c) := by
  have := unifI_isProb 0 1
  constructor
  simp only [atomUnif, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- Integrals against `F₀`: `∫ g dF₀ = p g(c) + (1 - p) ∫₀¹ g` for continuous `g`. -/
lemma integral_atomUnif {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂(atomUnif p c) = p * g c + (1 - p) * ∫ x in (0 : ℝ)..1, g x := by
  have hU : Integrable g (unifI 0 1) := by
    rw [unifI01]
    exact (hg.continuousOn.integrableOn_compact isCompact_Icc)
  have hD : Integrable g (Measure.dirac c) := integrable_dirac enorm_lt_top
  rw [atomUnif, integral_add_measure (hD.smul_measure ENNReal.ofReal_ne_top)
      (hU.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, unifI01, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

/-- The mean of `F₀` is `p c + (1 - p)/2`. -/
lemma integral_id_atomUnif {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, x ∂(atomUnif p c) = p * c + (1 - p) / 2 := by
  rw [integral_atomUnif (g := fun x => x) hp0 hp1 continuous_id]
  simp [integral_id]
  ring


/-! ### Convex order, stop-loss order and the norm inequalities -/

/-- The convex order `L ≤cx L'` between distributions on the line: `∫ φ dL ≤ ∫ φ dL'` for every
convex `φ` for which both integrals exist. -/
def ConvexOrderLE (L L' : Measure ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Integrable φ L → Integrable φ L' →
    ∫ x, φ x ∂L ≤ ∫ x, φ x ∂L'

/-- The stop-loss order: `∫ (x - t)₊ dL ≤ ∫ (x - t)₊ dL'` for every `t`. -/
def StopLossLE (L L' : Measure ℝ) : Prop :=
  ∀ t : ℝ, ∫ x, max (x - t) 0 ∂L ≤ ∫ x, max (x - t) 0 ∂L'

/-- Relation (`nc:eq:cx`) for a distribution `F` with mean `μ` and `n` variables:
`X - μ ≤cx -(n - 1)(X - μ)` for `X ∼ F`. -/
def CxCond (n : ℕ) (F : Measure ℝ) (μ : ℝ) : Prop :=
  ConvexOrderLE (F.map fun x => x - μ) (F.map fun x => -((n : ℝ) - 1) * (x - μ))

/-- A law-determined (extended) norm on real random variables, written as a function `N` of the
law: it is absolutely homogeneous, satisfies the triangle inequality for every coupling, and
vanishes only at the point mass at `0`. -/
structure IsLawNorm (N : Measure ℝ → ENNReal) : Prop where
  map_mul : ∀ (L : Measure ℝ) (a : ℝ), N (L.map fun x => a * x) = ENNReal.ofReal |a| * N L
  triangle : ∀ P : Measure (ℝ × ℝ), IsProbabilityMeasure P →
    N (P.map fun z => z.1 + z.2) ≤ N (P.map Prod.fst) + N (P.map Prod.snd)
  eq_zero_iff : ∀ L : Measure ℝ, IsProbabilityMeasure L → (N L = 0 ↔ L = Measure.dirac 0)

/-- The norm inequalities (`nc:eq:norm`) for one law-determined norm `N`: for every `t`, with
`s = (n μ - t)/(n - 1)`, `‖(X - t)₊‖ ≤ (n - 1) ‖(X - s)₋‖` and `‖(X - t)₋‖ ≤ (n - 1) ‖(X - s)₊‖`. -/
def NormCond (N : Measure ℝ → ENNReal) (n : ℕ) (F : Measure ℝ) (μ : ℝ) : Prop :=
  ∀ t : ℝ,
    N (F.map fun x => max (x - t) 0) ≤
        ENNReal.ofReal ((n : ℝ) - 1) * N (F.map fun x => max ((n * μ - t) / (n - 1) - x) 0) ∧
      N (F.map fun x => max (t - x) 0) ≤
        ENNReal.ofReal ((n : ℝ) - 1) * N (F.map fun x => max (x - (n * μ - t) / (n - 1)) 0)

/-- The norm inequalities (`nc:eq:norm`) for all law-determined norms. -/
def NormIneqs (n : ℕ) (F : Measure ℝ) (μ : ℝ) : Prop :=
  ∀ N, IsLawNorm N → NormCond N n F μ

/-- The mean condition (`eq:meancond`) for a distribution on `[a, b]` with mean `μ`. -/
def MeanCond (n : ℕ) (a b μ : ℝ) : Prop :=
  a + (b - a) / n ≤ μ ∧ μ ≤ b - (b - a) / n

/-- Classical hypothesis (not in Mathlib; Shaked and Shanthikumar, *Stochastic Orders*,
Theorem 3.A.1): for distributions with bounded support and equal means, the stop-loss order
implies the convex order. -/
def H_stoploss_cx : Prop :=
  ∀ L L' : Measure ℝ, IsProbabilityMeasure L → IsProbabilityMeasure L' →
    (∃ R : ℝ, L (Set.Icc (-R) R)ᶜ = 0 ∧ L' (Set.Icc (-R) R)ᶜ = 0) →
    ∫ x, x ∂L = ∫ x, x ∂L' → StopLossLE L L' → ConvexOrderLE L L'

/-- The result of Shmalo cited in the paper (`shmalo26b`), in the direction used: for a
distribution with bounded support, relation (`nc:eq:cx`) implies the norm inequalities
(`nc:eq:norm`) for all law-determined norms. -/
def H_shmalo26b : Prop :=
  ∀ (n : ℕ) (F : Measure ℝ) (μ : ℝ), 2 ≤ n → IsProbabilityMeasure F →
    (∃ R : ℝ, F (Set.Icc (-R) R)ᶜ = 0) → Integrable id F → ∫ x, x ∂F = μ →
    CxCond n F μ → NormIneqs n F μ

/-! ### Proposition `nc:prop:atom` (b) -/

lemma integral_hinge_up {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∫ x in (0 : ℝ)..1, max (x - τ) 0 = (1 - τ) ^ 2 / 2 := by
  have hc : Continuous fun x : ℝ => max (x - τ) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := τ) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0 : ℝ)..τ, max (x - τ) 0 = ∫ x in (0 : ℝ)..τ, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le h0] at hx
    exact max_eq_right (by linarith [hx.2])
  have e2 : ∫ x in τ..1, max (x - τ) 0 = ∫ x in τ..1, (x - τ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le h1] at hx
    exact max_eq_left (by linarith [hx.1])
  rw [e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  ring

lemma integral_hinge_down {r a τ : ℝ} (ha : 0 < a) (hτ : τ ≤ r) (hra : r - τ ≤ a) :
    ∫ x in (0 : ℝ)..1, max (r - a * x - τ) 0 = (r - τ) ^ 2 / (2 * a) := by
  set z := (r - τ) / a with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) ha.le
  have hz1 : z ≤ 1 := (div_le_one ha).2 hra
  have hc : Continuous fun x : ℝ => max (r - a * x - τ) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := z) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have haz : a * z = r - τ := by rw [hz]; field_simp
  have e1 : ∫ x in (0 : ℝ)..z, max (r - a * x - τ) 0 = ∫ x in (0 : ℝ)..z, (r - τ - a * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hz0] at hx
    have : a * x ≤ a * z := mul_le_mul_of_nonneg_left hx.2 ha.le
    rw [max_eq_left (by linarith)]
    ring
  have e2 : ∫ x in z..1, max (r - a * x - τ) 0 = ∫ x in z..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hz1] at hx
    have : a * z ≤ a * x := mul_le_mul_of_nonneg_left hx.1 ha.le
    exact max_eq_right (by linarith)
  rw [e1, e2, intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.const_mul a), intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero, mul_zero, add_zero]
  rw [hz]
  field_simp
  ring

/-- **Proposition `nc:prop:atom` (b)**, stop-loss form: for `n ≥ 3`, `0 < p < 1`, `0 ≤ c < 1/2`
and `n μ ≥ √(n - 1)`, where `μ = p c + (1 - p)/2` is the mean of `F₀`, the laws of `X₀ - μ` and
of `-(n - 1)(X₀ - μ)` are in stop-loss order. -/
theorem atom_stopLoss {n : ℕ} (hn : 3 ≤ n) {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 ≤ c)
    (hc : c < 1 / 2) (hb : Real.sqrt ((n : ℝ) - 1) ≤ n * (p * c + (1 - p) / 2)) :
    StopLossLE ((atomUnif p c).map fun x => x - (p * c + (1 - p) / 2))
      ((atomUnif p c).map fun x => -((n : ℝ) - 1) * (x - (p * c + (1 - p) / 2))) := by
  intro t
  set μ := p * c + (1 - p) / 2 with hμ
  set r := (n : ℝ) * μ with hr
  set τ := t + μ with hτ
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  have e1 : ∀ x : ℝ, max (x - μ - t) 0 = max (x - τ) 0 := fun x => by rw [hτ]; ring_nf
  have e2 : ∀ x : ℝ, max (-((n : ℝ) - 1) * (x - μ) - t) 0 = max (r - ((n : ℝ) - 1) * x - τ) 0 :=
    fun x => by rw [hτ, hr]; ring_nf
  simp only [e1, e2]
  rw [integral_atomUnif hp0.le hp1.le (by fun_prop),
    integral_atomUnif hp0.le hp1.le (by fun_prop)]
  have hμc : c ≤ μ := by rw [hμ]; nlinarith
  have hμh : μ ≤ 1 / 2 := by rw [hμ]; nlinarith
  have hs1 : 1 ≤ Real.sqrt ((n : ℝ) - 1) := by
    have := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ (n : ℝ) - 1)
    simpa using this
  have hr1 : 1 ≤ r := le_trans hs1 hb
  have hrn : r ≤ (n : ℝ) - 1 := by rw [hr]; nlinarith
  have hy0 : c ≤ r - ((n : ℝ) - 1) * c := by rw [hr]; nlinarith
  have hq : 0 < 1 - p := by linarith
  have hcont : Continuous fun x : ℝ => max (r - ((n : ℝ) - 1) * x - τ) 0 := by fun_prop
  rcases le_or_gt τ 0 with hτ0 | hτ0
  · -- `τ ≤ 0`: both sides are at least `μ - τ`, the left side with equality
    have hL : ∫ x in (0 : ℝ)..1, max (x - τ) 0 = 1 / 2 - τ := by
      rw [intervalIntegral.integral_congr (g := fun x => x - τ) fun x hx => by
        rw [Set.uIcc_of_le zero_le_one] at hx; exact max_eq_left (by linarith [hx.1])]
      simp [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
        integral_id]
    have hR : ∫ x in (0 : ℝ)..1, (r - ((n : ℝ) - 1) * x - τ) ≤
        ∫ x in (0 : ℝ)..1, max (r - ((n : ℝ) - 1) * x - τ) 0 :=
      intervalIntegral.integral_mono_on zero_le_one (Continuous.intervalIntegrable (by fun_prop) _ _)
        (hcont.intervalIntegrable _ _) fun x _ => le_max_left _ _
    have hR' : ∫ x in (0 : ℝ)..1, (r - ((n : ℝ) - 1) * x - τ) = r - ((n : ℝ) - 1) / 2 - τ := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub
        (intervalIntegral.intervalIntegrable_id.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_id.const_mul _)]
      have hlin : ∫ x in (0 : ℝ)..1, ((n : ℝ) - 1) * x = ((n : ℝ) - 1) / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]; ring
      rw [hlin]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hL, max_eq_left (by linarith : (0 : ℝ) ≤ c - τ)]
    have : p * (r - ((n : ℝ) - 1) * c - τ) ≤ p * max (r - ((n : ℝ) - 1) * c - τ) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hp0.le
    have h2 := mul_le_mul_of_nonneg_left hR hq.le
    rw [hR'] at h2
    have : p * (c - τ) + (1 - p) * (1 / 2 - τ) =
        p * (r - ((n : ℝ) - 1) * c - τ) + (1 - p) * (r - ((n : ℝ) - 1) / 2 - τ) := by
      rw [hr, hμ]; ring
    linarith
  rcases le_or_gt 1 τ with hτ1 | hτ1
  · -- `τ ≥ 1`: the left side vanishes
    have hL : ∫ x in (0 : ℝ)..1, max (x - τ) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
        rw [Set.uIcc_of_le zero_le_one] at hx; exact max_eq_right (by linarith [hx.2])]
      simp
    rw [hL, max_eq_right (by linarith : c - τ ≤ 0)]
    have : 0 ≤ ∫ x in (0 : ℝ)..1, max (r - ((n : ℝ) - 1) * x - τ) 0 :=
      intervalIntegral.integral_nonneg zero_le_one fun x _ => le_max_right _ _
    have : 0 ≤ p * max (r - ((n : ℝ) - 1) * c - τ) 0 :=
      mul_nonneg hp0.le (le_max_right _ _)
    nlinarith
  · -- `0 < τ < 1`
    rw [integral_hinge_up hτ0.le hτ1.le, integral_hinge_down (by linarith) (by linarith)
      (by linarith)]
    have hatom : p * max (c - τ) 0 ≤ p * max (r - ((n : ℝ) - 1) * c - τ) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hp0.le
    have hsq : ((n : ℝ) - 1) * (1 - τ) ^ 2 ≤ (r - τ) ^ 2 := by
      have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)
      have hlin : Real.sqrt ((n : ℝ) - 1) * (1 - τ) ≤ r - τ := by nlinarith
      have h0 : 0 ≤ Real.sqrt ((n : ℝ) - 1) * (1 - τ) :=
        mul_nonneg (Real.sqrt_nonneg _) (by linarith)
      calc ((n : ℝ) - 1) * (1 - τ) ^ 2 = (Real.sqrt ((n : ℝ) - 1) * (1 - τ)) ^ 2 := by
            rw [mul_pow, hs]
        _ ≤ (r - τ) ^ 2 := pow_le_pow_left₀ h0 hlin 2
    have : (1 - τ) ^ 2 / 2 ≤ (r - τ) ^ 2 / (2 * ((n : ℝ) - 1)) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have := mul_le_mul_of_nonneg_left this hq.le
    linarith

/-- `F₀` is carried by `[0, 1]` when `c ∈ [0, 1]`. -/
lemma atomUnif_ae_mem {p c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ᵐ x ∂(atomUnif p c), x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  simp only [atomUnif, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Measure.dirac c {a | a ∉ Set.Icc (0 : ℝ) 1} = 0 := by
    show Measure.dirac c (Set.Icc (0 : ℝ) 1)ᶜ = 0
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
    simp [hc0, hc1]
  have h2 : unifI 0 1 {a | a ∉ Set.Icc (0 : ℝ) 1} = 0 := by
    show unifI 0 1 (Set.Icc (0 : ℝ) 1)ᶜ = 0
    rw [unifI01, Measure.restrict_apply measurableSet_Icc.compl]
    simp
  rw [h1, h2]; simp

/-- A continuous function is integrable against a finite measure carried by `[a, b]`. -/
lemma integrable_of_ae_Icc {F : Measure ℝ} [IsFiniteMeasure F] {a b : ℝ}
    (hF : ∀ᵐ x ∂F, x ∈ Set.Icc a b) {h : ℝ → ℝ} (hh : Continuous h) : Integrable h F := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hh.continuousOn
  exact Integrable.of_bound hh.aestronglyMeasurable C (by
    filter_upwards [hF] with x hx using hC x hx)

/-- Bounded support of the image of a measure carried by `[a, b]` under a continuous map. -/
lemma map_compl_Icc_eq_zero {F : Measure ℝ} {a b : ℝ} (hF : ∀ᵐ x ∂F, x ∈ Set.Icc a b)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ R : ℝ, (F.map f) (Set.Icc (-R) R)ᶜ = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨C, ?_⟩
  rw [Measure.map_apply hf.measurable measurableSet_Icc.compl]
  refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hF)
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx ⊢
  by_contra hxI
  simp only [Set.mem_setOf_eq, not_or, not_lt] at hxI
  have := hC x ⟨hxI.1, hxI.2⟩
  rw [Real.norm_eq_abs, abs_le] at this
  rcases hx with h | h <;> linarith [this.1, this.2]

/-- **Proposition `nc:prop:atom` (b)**: under the classical theorem `H_stoploss_cx`, for `n ≥ 3`,
`0 < p < 1`, `0 ≤ c < 1/2` and `n μ ≥ √(n - 1)`, relation (`nc:eq:cx`) holds for `F₀`:
`X₀ - μ ≤cx -(n - 1)(X₀ - μ)`. -/
theorem atom_cx (H : H_stoploss_cx) {n : ℕ} (hn : 3 ≤ n) {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc0 : 0 ≤ c) (hc : c < 1 / 2) (hb : Real.sqrt ((n : ℝ) - 1) ≤ n * (p * c + (1 - p) / 2)) :
    CxCond n (atomUnif p c) (p * c + (1 - p) / 2) := by
  have hprob := atomUnif_isProb (c := c) hp0.le hp1.le
  have hsupp := atomUnif_ae_mem (p := p) hc0 (by linarith)
  set μ := p * c + (1 - p) / 2 with hμ
  have hmean := integral_id_atomUnif (c := c) hp0.le hp1.le
  have hint : ∀ f : ℝ → ℝ, Continuous f → Integrable f (atomUnif p c) :=
    fun f hf => integrable_of_ae_Icc hsupp hf
  refine H _ _ ((Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 hprob)
    ((Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 hprob) ?_ ?_ (atom_stopLoss hn hp0 hp1 hc0 hc hb)
  · obtain ⟨R₁, h₁⟩ := map_compl_Icc_eq_zero hsupp (f := fun x => x - μ) (by fun_prop)
    obtain ⟨R₂, h₂⟩ := map_compl_Icc_eq_zero hsupp
      (f := fun x => -((n : ℝ) - 1) * (x - μ)) (by fun_prop)
    refine ⟨max R₁ R₂, measure_mono_null ?_ h₁, measure_mono_null ?_ h₂⟩ <;>
    · intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx ⊢
      rcases hx with h | h
      · left; linarith [le_max_left R₁ R₂, le_max_right R₁ R₂]
      · right; linarith [le_max_left R₁ R₂, le_max_right R₁ R₂]
  · rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      integral_const_mul, integral_sub (hint (fun x => x) continuous_id) (integrable_const _)]
    simp [hmean, ← hμ]

/-- Convex order under scaling: if `∫ g dF = 0` and `0 ≤ t ≤ t'`, `0 < t'`, then
`∫ φ(t g) dF ≤ ∫ φ(t' g) dF` for convex `φ` (both integrals existing). -/
lemma integral_convex_scale {F : Measure ℝ} [IsProbabilityMeasure F] {g : ℝ → ℝ}
    (hg : Integrable g F) (hg0 : ∫ x, g x ∂F = 0) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t')
    (ht' : 0 < t') {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hi : Integrable (fun x => φ (t * g x)) F) (hi' : Integrable (fun x => φ (t' * g x)) F) :
    ∫ x, φ (t * g x) ∂F ≤ ∫ x, φ (t' * g x) ∂F := by
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hJ : φ (∫ x, t' * g x ∂F) ≤ ∫ x, φ (t' * g x) ∂F :=
    hφ.map_integral_le hcont.continuousOn isClosed_univ (by simp) (hg.const_mul t') hi'
  rw [integral_const_mul, hg0, mul_zero] at hJ
  set lam := t / t'
  have hl0 : 0 ≤ lam := div_nonneg ht ht'.le
  have hl1 : lam ≤ 1 := (div_le_one ht').2 htt
  have hpt : ∀ x, φ (t * g x) ≤ lam * φ (t' * g x) + (1 - lam) * φ 0 := by
    intro x
    have := hφ.2 (Set.mem_univ (t' * g x)) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - lam)
      (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero] at this
    have e : lam * (t' * g x) = t * g x := by simp only [lam]; field_simp
    rwa [e] at this
  calc ∫ x, φ (t * g x) ∂F ≤ ∫ x, (lam * φ (t' * g x) + (1 - lam) * φ 0) ∂F :=
        integral_mono hi ((hi'.const_mul _).add (integrable_const _)) hpt
    _ = lam * ∫ x, φ (t' * g x) ∂F + (1 - lam) * φ 0 := by
        rw [integral_add (hi'.const_mul _) (integrable_const _), integral_const_mul]
        simp
    _ ≤ ∫ x, φ (t' * g x) ∂F := by nlinarith

/-- Relation (`nc:eq:cx`) for `n = 3` implies it for every `n ≥ 3`, for a distribution carried
by a bounded interval (proof of Corollary `nc:cor:least`). -/
theorem cxCond_of_three {F : Measure ℝ} [IsProbabilityMeasure F] {a b : ℝ}
    (hsupp : ∀ᵐ x ∂F, x ∈ Set.Icc a b) {μ : ℝ} (hμ : ∫ x, x ∂F = μ) (h3 : CxCond 3 F μ)
    {n : ℕ} (hn : 3 ≤ n) : CxCond n F μ := by
  intro φ hφ hi1 hi2
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hint : ∀ f : ℝ → ℝ, Continuous f → Integrable f F :=
    fun f hf => integrable_of_ae_Icc hsupp hf
  have hi3 : Integrable φ (F.map fun x => -(((3 : ℕ) : ℝ) - 1) * (x - μ)) := by
    rw [integrable_map_measure hcont.aestronglyMeasurable (by fun_prop)]
    exact hint _ (by fun_prop)
  have step1 := h3 φ hφ hi1 hi3
  refine step1.trans ?_
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [integral_map (by fun_prop) hcont.aestronglyMeasurable,
    integral_map (by fun_prop) hcont.aestronglyMeasurable]
  have hg0 : ∫ x, -(x - μ) ∂F = 0 := by
    rw [integral_neg, integral_sub (hint (fun x => x) continuous_id) (integrable_const _)]
    simp [hμ]
  have := integral_convex_scale (F := F) (g := fun x => -(x - μ)) (hint _ (by fun_prop)) hg0
    (t := 2) (t' := (n : ℝ) - 1) (by norm_num) (by linarith) (by linarith) hφ
    (hint _ (by fun_prop)) (hint _ (by fun_prop))
  convert this using 3 <;> push_cast <;> ring

/-! ### Two-step densities (Corollary 13 of the paper) -/

section Step
open Set


/-- The distribution with density `a` on `(α, m]` and `b` on `(m, β]`. -/
def stepM (α m β a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal a • volume.restrict (Ioc α m) + ENNReal.ofReal b • volume.restrict (Ioc m β)

open Set in
lemma lintegral_Ioc_sub_left {α l r : ℝ} (hl : α ≤ l) (hlr : l ≤ r) :
    ∫⁻ x in Ioc l r, ENNReal.ofReal (x - α) = ENNReal.ofReal (((r - α) ^ 2 - (l - α) ^ 2) / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Continuous.integrableOn_Icc (by fun_prop : Continuous fun x : ℝ => x - α)).mono_set
      Ioc_subset_Icc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
      simp only [Pi.zero_apply]; linarith [hx.1])]
  rw [← intervalIntegral.integral_of_le hlr, intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  congr 1; ring

lemma lintegral_Ioc_sub_right {β l r : ℝ} (hr : r ≤ β) (hlr : l ≤ r) :
    ∫⁻ x in Ioc l r, ENNReal.ofReal (β - x) = ENNReal.ofReal (((β - l) ^ 2 - (β - r) ^ 2) / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Continuous.integrableOn_Icc (by fun_prop : Continuous fun x : ℝ => β - x)).mono_set
      Ioc_subset_Icc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
      simp only [Pi.zero_apply]; linarith [hx.2])]
  rw [← intervalIntegral.integral_of_le hlr, intervalIntegral.integral_sub
    intervalIntegrable_const intervalIntegral.intervalIntegrable_id, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  congr 1; ring

lemma lintegral_stepM {α m β a b : ℝ} {g : ℝ → ENNReal} :
    ∫⁻ x, g x ∂(stepM α m β a b) =
      ENNReal.ofReal a * (∫⁻ x in Ioc α m, g x) + ENNReal.ofReal b * ∫⁻ x in Ioc m β, g x := by
  rw [stepM, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [smul_eq_mul]

/-- Two-step non-increasing densities: if `α ≤ m ≤ β`, `α < β`, `0 ≤ b ≤ a`, the total mass
`a (m - α) + b (β - m)` is `1`, the mean is `M` and `α + (β - α)/k ≤ M`, then `stepM α m β a b`
has a `k`-complete mix with sum `k M` (Corollary 13 of the paper). -/
theorem stepM_mix_anti {k : ℕ} (hk : 2 ≤ k) {α m β a b M : ℝ} (hαm : α ≤ m) (hmβ : m ≤ β)
    (hb0 : 0 ≤ b) (hba : b ≤ a) (hmass : a * (m - α) + b * (β - m) = 1)
    (hM : M = (a * (m ^ 2 - α ^ 2) + b * (β ^ 2 - m ^ 2)) / 2)
    (hcond : α + (β - α) / k ≤ M) :
    ∃ Q : Measure (Fin k → ℝ), IsCompleteMix k (stepM α m β a b) Q ∧
      ∀ᵐ x ∂Q, ∑ j, x j = k * M := by
  set f : ℝ → ℝ := fun x => if x < m then a else if x < β then b else 0 with hf
  have ha0 : 0 ≤ a := hb0.trans hba
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hαβ : α ≤ β := hαm.trans hmβ
  have hαM : α < M := by
    rcases eq_or_lt_of_le hαβ with h | h
    · exfalso; subst h
      have : m = α := le_antisymm hmβ hαm
      subst this; simp at hmass
    · have : 0 < (β - α) / k := div_pos (by linarith) hk0
      linarith
  have hmeas : Measurable fun x => ENNReal.ofReal (f x) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have hwd : (volume.restrict (Ioi α)).withDensity (fun x => ENNReal.ofReal (f x)) =
      stepM α m β a b := by
    have hae : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume.restrict (Ioi α)]
        (Ioo α m).indicator (fun _ => ENNReal.ofReal a) +
          (Ioo m β).indicator (fun _ => ENNReal.ofReal b) := by
      have hne : ∀ᵐ x ∂(volume.restrict (Ioi α)), x ≠ m :=
        ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton m))
      filter_upwards [hne, ae_restrict_mem measurableSet_Ioi] with x hxm hx
      simp only [hf, Pi.add_apply, Set.indicator_apply, Set.mem_Ioo]
      have hx' : α < x := hx
      by_cases h1 : x < m
      · simp [h1, hx', not_lt.2 h1.le]
      · have h1' : m < x := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hxm)
        by_cases h2 : x < β
        · simp [h1, h2, h1']
        · simp [h1, h2]
    rw [withDensity_congr_ae hae, withDensity_add_left (measurable_const.indicator measurableSet_Ioo),
      withDensity_indicator measurableSet_Ioo, withDensity_indicator measurableSet_Ioo,
      withDensity_const, withDensity_const, Measure.restrict_restrict measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, stepM]
    have e1 : Ioo α m ∩ Ioi α = Ioo α m := inter_eq_left.2 fun x hx => hx.1
    have e2 : Ioo m β ∩ Ioi α = Ioo m β := inter_eq_left.2 fun x hx => lt_of_le_of_lt hαm hx.1
    rw [e1, e2, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := m))]
  have hvol : ∀ {l r : ℝ}, l ≤ r → volume (Ioc l r) = ENNReal.ofReal (r - l) := fun _ => by
    simp [Real.volume_Ioc]
  have hA : AntitoneOn f (Ioi α) := by
    intro x hx y hy hxy
    simp only [hf]
    split_ifs <;> first | linarith | (exfalso; linarith) | skip
  have hRC : ∀ x, α < x → ContinuousWithinAt f (Ici x) x := by
    intro x _
    refine (continuousWithinAt_const (b := f x)).congr_of_eventuallyEq ?_ rfl
    by_cases h1 : x < m
    · filter_upwards [Ico_mem_nhdsGE h1] with y hy
      simp [hf, hy.2, h1]
    · by_cases h2 : x < β
      · filter_upwards [Ico_mem_nhdsGE h2] with y hy
        have : ¬ y < m := fun h => h1 (lt_of_le_of_lt hy.1 h)
        simp [hf, hy.2, h1, h2, this]
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : x ≤ y := hy
        have : ¬ y < m := fun h => h1 (lt_of_le_of_lt hy' h)
        have : ¬ y < β := fun h => h2 (lt_of_le_of_lt hy' h)
        simp [hf, h1, h2, *]
  have hZ : ∀ x, β ≤ x → f x = 0 := by
    intro x hx
    have : ¬ x < m := fun h => by linarith
    simp [hf, this, not_lt.2 hx]
  have h1 : ∫⁻ x in Ioi α, ENNReal.ofReal (f x) = 1 := by
    rw [← Measure.restrict_univ (μ := volume.restrict (Ioi α)), ← withDensity_apply _ MeasurableSet.univ,
      hwd]
    simp only [stepM, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul, hvol hαm, hvol hmβ]
    rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_add
      (mul_nonneg ha0 (by linarith)) (mul_nonneg hb0 (by linarith)), hmass, ENNReal.ofReal_one]
  have h2 : ∫⁻ x in Ioi α, ENNReal.ofReal (x - α) * ENNReal.ofReal (f x) = ENNReal.ofReal (M - α) := by
    have h1 : ∫⁻ x in Ioi α, ENNReal.ofReal (x - α) * ENNReal.ofReal (f x) =
        ∫⁻ x, ENNReal.ofReal (x - α) ∂((volume.restrict (Ioi α)).withDensity
          (fun x => ENNReal.ofReal (f x))) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hmeas (by fun_prop)]
      simp only [Pi.mul_apply, mul_comm]
    rw [h1, hwd, lintegral_stepM, lintegral_Ioc_sub_left le_rfl hαm,
      lintegral_Ioc_sub_left hαm hmβ, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
      ← ENNReal.ofReal_add (mul_nonneg ha0 (by nlinarith)) (mul_nonneg hb0 (by nlinarith))]
    congr 1
    rw [hM]
    have : α = α * (a * (m - α) + b * (β - m)) := by rw [hmass, mul_one]
    nlinarith
  obtain ⟨Q, hQ, hsum⟩ := Mixes.SlabsMix.cor13_nonincreasing (f := f) (α := α) (β := β) (μ := M)
    hk hA hRC hZ h1 h2 hαM hcond
  exact ⟨Q, hwd ▸ hQ, hsum⟩

/-- Two-step non-decreasing densities: if `α ≤ m < β`, `0 ≤ a ≤ b`, the total mass is `1`, the
mean is `M` and `M ≤ β - (β - α)/k`, then `stepM α m β a b` has a `k`-complete mix with sum
`k M` (Corollary 13 of the paper). -/
theorem stepM_mix_mono {k : ℕ} (hk : 2 ≤ k) {α m β a b M : ℝ} (hαm : α ≤ m) (hmβ : m < β)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hmass : a * (m - α) + b * (β - m) = 1)
    (hM : M = (a * (m ^ 2 - α ^ 2) + b * (β ^ 2 - m ^ 2)) / 2)
    (hcond : M ≤ β - (β - α) / k) :
    ∃ Q : Measure (Fin k → ℝ), IsCompleteMix k (stepM α m β a b) Q ∧
      ∀ᵐ x ∂Q, ∑ j, x j = k * M := by
  set f : ℝ → ℝ := fun x => if x ≤ α then 0 else if x ≤ m then a else b with hf
  have hb0 : 0 ≤ b := ha0.trans hab
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hMβ : M < β := by
    have : 0 < (β - α) / k := div_pos (by linarith) hk0
    linarith
  have hmeas : Measurable fun x => ENNReal.ofReal (f x) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Measurable.ite measurableSet_Iic measurable_const
      (Measurable.ite measurableSet_Iic measurable_const measurable_const)
  have hwd : (volume.restrict (Iio β)).withDensity (fun x => ENNReal.ofReal (f x)) =
      stepM α m β a b := by
    have hae : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume.restrict (Iio β)]
        (Ioc α m).indicator (fun _ => ENNReal.ofReal a) +
          (Ioo m β).indicator (fun _ => ENNReal.ofReal b) := by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
      have hx' : x < β := hx
      simp only [hf, Pi.add_apply, Set.indicator_apply, Set.mem_Ioo, Set.mem_Ioc]
      by_cases h1 : x ≤ α
      · have : ¬ m < x := fun h => by linarith
        simp [h1, not_lt.2 h1, this]
      · by_cases h2 : x ≤ m
        · simp [h1, h2, not_le.1 h1, not_lt.2 h2]
        · simp [h1, h2, not_le.1 h2, hx', not_le.1 h1]
    rw [withDensity_congr_ae hae, withDensity_add_left (measurable_const.indicator measurableSet_Ioc),
      withDensity_indicator measurableSet_Ioc, withDensity_indicator measurableSet_Ioo,
      withDensity_const, withDensity_const, Measure.restrict_restrict measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioo, stepM]
    have e1 : Ioc α m ∩ Iio β = Ioc α m := inter_eq_left.2 fun x hx => lt_of_le_of_lt hx.2 hmβ
    have e2 : Ioo m β ∩ Iio β = Ioo m β := inter_eq_left.2 fun x hx => hx.2
    rw [e1, e2, Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := m))]
  have hvol : ∀ {l r : ℝ}, l ≤ r → volume (Ioc l r) = ENNReal.ofReal (r - l) := fun _ => by
    simp [Real.volume_Ioc]
  have hMo : MonotoneOn f (Iio β) := by
    intro x hx y hy hxy
    simp only [hf]
    split_ifs <;> first | linarith | (exfalso; linarith) | skip
  have hLC : ∀ x, x < β → ContinuousWithinAt f (Iic x) x := by
    intro x _
    refine (continuousWithinAt_const (b := f x)).congr_of_eventuallyEq ?_ rfl
    by_cases h1 : x ≤ α
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : y ≤ x := hy
      simp [hf, h1, hy'.trans h1]
    · by_cases h2 : x ≤ m
      · filter_upwards [Ioc_mem_nhdsLE (not_le.1 h1)] with y hy
        simp [hf, h1, h2, not_le.2 hy.1, hy.2.trans h2]
      · filter_upwards [Ioc_mem_nhdsLE (not_le.1 h2)] with y hy
        have : ¬ y ≤ α := fun h => by linarith [hy.1]
        simp [hf, h1, h2, not_le.2 hy.1, this]
  have hZ : ∀ x, x ≤ α → f x = 0 := by
    intro x hx
    simp [hf, hx]
  have h1 : ∫⁻ x in Iio β, ENNReal.ofReal (f x) = 1 := by
    rw [← Measure.restrict_univ (μ := volume.restrict (Iio β)), ← withDensity_apply _ MeasurableSet.univ,
      hwd]
    simp only [stepM, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul, hvol hαm, hvol hmβ.le]
    rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_add
      (mul_nonneg ha0 (by linarith)) (mul_nonneg hb0 (by linarith)), hmass, ENNReal.ofReal_one]
  have h2 : ∫⁻ x in Iio β, ENNReal.ofReal (β - x) * ENNReal.ofReal (f x) =
      ENNReal.ofReal (β - M) := by
    have h1 : ∫⁻ x in Iio β, ENNReal.ofReal (β - x) * ENNReal.ofReal (f x) =
        ∫⁻ x, ENNReal.ofReal (β - x) ∂((volume.restrict (Iio β)).withDensity
          (fun x => ENNReal.ofReal (f x))) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hmeas (by fun_prop)]
      simp only [Pi.mul_apply, mul_comm]
    rw [h1, hwd, lintegral_stepM, lintegral_Ioc_sub_right hmβ.le hαm,
      lintegral_Ioc_sub_right le_rfl hmβ.le, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
      ← ENNReal.ofReal_add (mul_nonneg ha0 (by nlinarith)) (mul_nonneg hb0 (by nlinarith))]
    congr 1
    rw [hM]
    have : β = β * (a * (m - α) + b * (β - m)) := by rw [hmass, mul_one]
    nlinarith
  obtain ⟨Q, hQ, hsum⟩ := Mixes.SlabsMix.cor13_nondecreasing (f := f) (α := α) (β := β) (μ := M)
    hk hMo hLC hZ h1 h2 hMβ hcond
  exact ⟨Q, hwd ▸ hQ, hsum⟩

end Step

/-! ### Proposition `nc:prop:atom` (a): the assembly of the complete mix -/

section Assembly
open Set


/-- Put the point `c` in the first `j` coordinates and a tuple of length `n - j` in the others. -/
def embedAt (n j : ℕ) (c : ℝ) (x : Fin (n - j) → ℝ) : Fin n → ℝ :=
  fun i => if h : (i : ℕ) < j then c else x ⟨i - j, by omega⟩

lemma measurable_embedAt (n j : ℕ) (c : ℝ) : Measurable (embedAt n j c) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : (i : ℕ) < j
  · simp only [embedAt, h, dif_pos]; exact measurable_const
  · simp only [embedAt, h, dif_neg, not_false_eq_true]; exact measurable_pi_apply _

lemma sum_embedAt {n j : ℕ} (hj : j ≤ n) (c : ℝ) (x : Fin (n - j) → ℝ) :
    ∑ i, embedAt n j c x i = j * c + ∑ k, x k := by
  set g : ℕ → ℝ := fun i => if h0 : i < j then c else if h : i < n then x ⟨i - j, by omega⟩ else 0
  have h1 : ∑ i, embedAt n j c x i = ∑ i : Fin n, g i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [embedAt, g]
    by_cases h : (i : ℕ) < j
    · simp [h]
    · simp [h, i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range g n, ← Finset.sum_range_add_sum_Ico g hj,
    Finset.sum_Ico_eq_sum_range]
  have h2 : ∑ i ∈ Finset.range j, g i = j * c := by
    rw [Finset.sum_congr rfl fun i hi => (by simp [g, Finset.mem_range.1 hi] : g i = c)]
    simp
  set h' : ℕ → ℝ := fun k => if hk : k < n - j then x ⟨k, hk⟩ else 0
  have h3 : ∑ k ∈ Finset.range (n - j), g (j + k) = ∑ k : Fin (n - j), h' k := by
    rw [Fin.sum_univ_eq_sum_range h' (n - j)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    simp only [g, h']
    rw [dif_neg (by omega), dif_pos (by omega), dif_pos hk']
    congr 2; omega
  rw [h2, h3]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [h', k.isLt]

/-- `j` copies of the point mass at `c` together with an `(n - j)`-complete mix of `κ` with sum
`t` form a joint mix with sum `j c + t`. -/
theorem jointMix_embedAt {n j : ℕ} (hj : j ≤ n) (c : ℝ) {κ : Measure ℝ}
    {Q : Measure (Fin (n - j) → ℝ)} (hQ : IsCompleteMix (n - j) κ Q) {t : ℝ}
    (ht : ∀ᵐ x ∂Q, ∑ k, x k = t) :
    IsJointMix (fun i : Fin n => if (i : ℕ) < j then Measure.dirac c else κ)
        (Q.map (embedAt n j c)) ∧
      ∀ᵐ y ∂(Q.map (embedAt n j c)), ∑ i, y i = j * c + t := by
  have hQp := hQ.1
  have hm := measurable_embedAt n j c
  have hsum : ∀ᵐ y ∂(Q.map (embedAt n j c)), ∑ i, y i = j * c + t := by
    rw [ae_map_iff hm.aemeasurable (measurableSet_eq_fun
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const)]
    filter_upwards [ht] with x hx
    rw [sum_embedAt hj, hx]
  refine ⟨⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 hQp, ⟨_, hsum⟩, fun i => ?_⟩, hsum⟩
  rw [Measure.map_map (measurable_pi_apply i) hm]
  by_cases h : (i : ℕ) < j
  · simp only [h, if_true]
    have : (fun y => y i) ∘ embedAt n j c = fun _ => c := by
      funext x; simp [embedAt, h]
    rw [this, Measure.map_const, measure_univ, one_smul]
  · simp only [h, if_false]
    have : (fun y => y i) ∘ embedAt n j c = fun x => x ⟨i - j, by omega⟩ := by
      funext x; simp [embedAt, h]
    rw [this]
    exact hQ.2.2 _

/-- Assembly of the complete mix of Proposition `nc:prop:atom` (a): a random number `A = j i` of
the variables at `c`, chosen with probability `w i`, at uniformly random positions, and an
`(n - j i)`-complete mix of `κ i` with sum `s - j i c` for the others. -/
theorem completelyMixable_assemble {n : ℕ} {ι : Type*} [Fintype ι] (w : ι → ENNReal)
    (hw : ∑ i, w i = 1) (j : ι → ℕ) (hj : ∀ i, j i ≤ n) (c s : ℝ) (κ : ι → Measure ℝ)
    (Q : ∀ i, Measure (Fin (n - j i) → ℝ)) (hQ : ∀ i, IsCompleteMix (n - j i) (κ i) (Q i))
    (hs : ∀ i, ∀ᵐ x ∂(Q i), ∑ k, x k = s - j i * c) :
    CompletelyMixable n (∑ i, w i • ((n : ENNReal)⁻¹ •
      ((j i : ENNReal) • Measure.dirac c + ((n - j i : ℕ) : ENNReal) • κ i))) := by
  have hP := fun i => jointMix_embedAt (hj i) c (hQ i) (hs i)
  have := Mixes.lem_sym w hw (fun i k => if (k : ℕ) < j i then Measure.dirac c else κ i)
    (fun i => (Q i).map (embedAt n (j i) c)) s (fun i => (hP i).1)
    (fun i => by filter_upwards [(hP i).2] with y hy; rw [hy]; ring)
  have hsum : ∀ i, (∑ k : Fin n, if (k : ℕ) < j i then Measure.dirac c else κ i) =
      (j i : ENNReal) • Measure.dirac c + ((n - j i : ℕ) : ENNReal) • κ i := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Fin.card_filter_val_lt,
      min_eq_right (hj i)]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun k : Fin n => (k : ℕ) < j i)
    rw [Fin.card_filter_val_lt, min_eq_right (hj i), Finset.card_univ, Fintype.card_fin] at hc
    rw [show (Finset.univ.filter fun k : Fin n => ¬ (k : ℕ) < j i).card = n - j i by omega]
    simp only [← Nat.cast_smul_eq_nsmul ENNReal]
  simp only [hsum] at this
  exact ⟨_, this.1⟩



lemma unifI01_split {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    unifI 0 1 = volume.restrict (Ioc 0 m) + volume.restrict (Ioc m 1) := by
  rw [unifI01, ← Measure.restrict_congr_set Ioc_ae_eq_Icc, ← Ioc_union_Ioc_eq_Ioc hm0 hm1,
    Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]

/-- The identity (`nc:eq:mixture`) of the paper for two components: if the numbers of atoms
`j₀, j₁` are chosen with probabilities `1 - θ, θ` and the remaining variables follow the two-step
laws `stepM 0 m 1 aᵢ bᵢ`, the marginal is `F₀ = p δ_c + (1 - p) U[0, 1]`. -/
theorem atom_identity {n j0 j1 : ℕ} (hn : 1 ≤ n) (hj0 : j0 ≤ n) (hj1 : j1 ≤ n)
    {θ p c m a0 b0 a1 b1 : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (ha0 : 0 ≤ a0) (hb0 : 0 ≤ b0) (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1)
    (hp : (1 - θ) * j0 + θ * j1 = n * p)
    (hA : (1 - θ) * (n - j0) * a0 + θ * (n - j1) * a1 = n * (1 - p))
    (hB : (1 - θ) * (n - j0) * b0 + θ * (n - j1) * b1 = n * (1 - p)) :
    ENNReal.ofReal (1 - θ) • ((n : ENNReal)⁻¹ •
        ((j0 : ENNReal) • Measure.dirac c + ((n - j0 : ℕ) : ENNReal) • stepM 0 m 1 a0 b0)) +
      ENNReal.ofReal θ • ((n : ENNReal)⁻¹ •
        ((j1 : ENNReal) • Measure.dirac c + ((n - j1 : ℕ) : ENNReal) • stepM 0 m 1 a1 b1)) =
      atomUnif p c := by
  have key : ∀ (W0 W1 N J0 J1 K0 K1 A0 A1 B0 B1 P Q : NNReal),
      W0 * N * J0 + W1 * N * J1 = P → W0 * N * K0 * A0 + W1 * N * K1 * A1 = Q →
      W0 * N * K0 * B0 + W1 * N * K1 * B1 = Q → ∀ x y z : ENNReal,
      (W0 : ENNReal) * ((N : ENNReal) * ((J0 : ENNReal) * x + (K0 : ENNReal) *
        ((A0 : ENNReal) * y + (B0 : ENNReal) * z))) +
      (W1 : ENNReal) * ((N : ENNReal) * ((J1 : ENNReal) * x + (K1 : ENNReal) *
        ((A1 : ENNReal) * y + (B1 : ENNReal) * z))) = (P : ENNReal) * x + (Q : ENNReal) * (y + z) := by
    intro W0 W1 N J0 J1 K0 K1 A0 A1 B0 B1 P Q h1 h2 h3 x y z
    subst h1 h2
    rw [show ((W0 * N * K0 * A0 + W1 * N * K1 * A1 : NNReal) : ENNReal) * (y + z) =
      ((W0 * N * K0 * A0 + W1 * N * K1 * A1 : NNReal) : ENNReal) * y +
        ((W0 * N * K0 * B0 + W1 * N * K1 * B1 : NNReal) : ENNReal) * z by rw [h3, mul_add]]
    push_cast
    ring
  have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hN : (n : ENNReal)⁻¹ = (((n : NNReal)⁻¹ : NNReal) : ENNReal) := by
    rw [ENNReal.coe_inv hn0, ENNReal.coe_natCast]
  rw [atomUnif, unifI01_split hm0 hm1]
  ext A hA
  simp only [stepM, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hN, ← ENNReal.ofReal_natCast j0, ← ENNReal.ofReal_natCast j1,
    ← ENNReal.ofReal_natCast (n - j0), ← ENNReal.ofReal_natCast (n - j1), Nat.cast_sub hj0,
    Nat.cast_sub hj1]
  have hj0' : (0 : ℝ) ≤ n - j0 := by
    have : (j0 : ℝ) ≤ n := by exact_mod_cast hj0
    linarith
  have hj1' : (0 : ℝ) ≤ n - j1 := by
    have : (j1 : ℝ) ≤ n := by exact_mod_cast hj1
    linarith
  have hreal : ∀ r : ℝ, 0 ≤ r → ((Real.toNNReal r : NNReal) : ℝ) = r :=
    fun r hr => Real.coe_toNNReal r hr
  have hnr : ((n : NNReal) : ℝ) = n := rfl
  refine key _ _ _ _ _ _ _ _ _ _ _ (Real.toNNReal p) (Real.toNNReal (1 - p)) ?_ ?_ ?_ _ _ _
  · apply NNReal.eq
    push_cast
    rw [hreal (1 - θ) (by linarith), hreal θ hθ0, hreal p hp0, hreal _ (Nat.cast_nonneg j0),
      hreal _ (Nat.cast_nonneg j1)]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
    linarith
  · apply NNReal.eq
    push_cast
    rw [hreal (1 - θ) (by linarith), hreal θ hθ0, hreal a0 ha0, hreal a1 ha1,
      hreal (1 - p) (by linarith), hreal _ hj0', hreal _ hj1']
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
    linarith
  · apply NNReal.eq
    push_cast
    rw [hreal (1 - θ) (by linarith), hreal θ hθ0, hreal b0 hb0, hreal b1 hb1,
      hreal (1 - p) (by linarith), hreal _ hj0', hreal _ hj1']
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
    linarith

end Assembly

section Sufficiency
open Set

/-- `completelyMixable_assemble` for two components chosen with probabilities `1 - θ` and `θ`. -/
theorem completelyMixable_assemble2 {n j0 j1 : ℕ} (hj0 : j0 ≤ n) (hj1 : j1 ≤ n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (c s : ℝ) {κ0 κ1 : Measure ℝ}
    {Q0 : Measure (Fin (n - j0) → ℝ)} {Q1 : Measure (Fin (n - j1) → ℝ)}
    (hQ0 : IsCompleteMix (n - j0) κ0 Q0) (hQ1 : IsCompleteMix (n - j1) κ1 Q1)
    (hs0 : ∀ᵐ x ∂Q0, ∑ k, x k = s - j0 * c) (hs1 : ∀ᵐ x ∂Q1, ∑ k, x k = s - j1 * c) :
    CompletelyMixable n (ENNReal.ofReal (1 - θ) • ((n : ENNReal)⁻¹ •
        ((j0 : ENNReal) • Measure.dirac c + ((n - j0 : ℕ) : ENNReal) • κ0)) +
      ENNReal.ofReal θ • ((n : ENNReal)⁻¹ •
        ((j1 : ENNReal) • Measure.dirac c + ((n - j1 : ℕ) : ENNReal) • κ1))) := by
  have h := completelyMixable_assemble (n := n) (ι := Bool)
    (fun b => Bool.rec (ENNReal.ofReal (1 - θ)) (ENNReal.ofReal θ) b)
    (by rw [Fintype.sum_bool]; simp only
        rw [← ENNReal.ofReal_add hθ0 (by linarith)]; simp)
    (fun b => Bool.rec j0 j1 b) (fun b => by cases b <;> assumption) c s
    (fun b => Bool.rec κ0 κ1 b)
    (fun b => Bool.rec (motive := fun b => Measure (Fin (n - Bool.rec j0 j1 b) → ℝ)) Q0 Q1 b)
    (fun b => by cases b <;> assumption) (fun b => by cases b <;> assumption)
  rw [Fintype.sum_bool, add_comm] at h
  exact h

/-- `stepM (s - 1) 1 1 a 0 = stepM 0 (s - 1) 1 0 a`: the uniform law on `[s - 1, 1]`. -/
lemma stepM_shift (u a : ℝ) : stepM u 1 1 a 0 = stepM 0 u 1 0 a := by
  simp [stepM, add_comm]

lemma cond_left {a K M : ℝ} (ha : 0 < a) (hK : a ≤ K) (hM : 1 / a ≤ M) : 0 + (1 - 0) / K ≤ M := by
  have : 1 / K ≤ 1 / a := one_div_le_one_div_of_le ha hK
  simp only [zero_add, sub_zero]; linarith

lemma cond_right {a K M : ℝ} (ha : 0 < a) (hK : a ≤ K) (hM : M ≤ 1 - 1 / a) :
    M ≤ 1 - (1 - 0) / K := by
  have : 1 / K ≤ 1 / a := one_div_le_one_div_of_le ha hK
  simp only [sub_zero]; linarith

/-- Arithmetic of case A, first component. -/
lemma caseA_sum0 {n j0 θ β p c γ0 : ℝ} (hγ : (n - j0) * γ0 = -4 * β * θ) (hp : n * p = j0 + θ)
    (hc : c = 1 / 2 - β) :
    (n - j0) * (((1 - γ0) * ((1 / 2) ^ 2 - 0 ^ 2) + (1 + γ0) * (1 ^ 2 - (1 / 2) ^ 2)) / 2) =
      n * (p * c + (1 - p) / 2) - j0 * c := by
  subst hc; linear_combination (1 / 4) * hγ + β * hp

/-- Arithmetic of case A, second component. -/
lemma caseA_sum1 {n j0 θ β p c γ1 : ℝ} (hγ : (n - j0 - 1) * γ1 = 4 * β * (1 - θ))
    (hp : n * p = j0 + θ) (hc : c = 1 / 2 - β) :
    (n - j0 - 1) * (((1 - γ1) * ((1 / 2) ^ 2 - 0 ^ 2) + (1 + γ1) * (1 ^ 2 - (1 / 2) ^ 2)) / 2) =
      n * (p * c + (1 - p) / 2) - (j0 + 1) * c := by
  subst hc; linear_combination (1 / 4) * hγ + β * hp

lemma caseA_A {n j0 θ β p γ0 γ1 : ℝ} (hγ0 : (n - j0) * γ0 = -4 * β * θ)
    (hγ1 : (n - j0 - 1) * γ1 = 4 * β * (1 - θ)) (hp : n * p = j0 + θ) :
    (1 - θ) * (n - j0) * (1 - γ0) + θ * (n - (j0 + 1)) * (1 - γ1) = n * (1 - p) := by
  linear_combination (-(1 - θ)) * hγ0 + (-θ) * hγ1 + hp

lemma caseA_B {n j0 θ β p γ0 γ1 : ℝ} (hγ0 : (n - j0) * γ0 = -4 * β * θ)
    (hγ1 : (n - j0 - 1) * γ1 = 4 * β * (1 - θ)) (hp : n * p = j0 + θ) :
    (1 - θ) * (n - j0) * (1 + γ0) + θ * (n - (j0 + 1)) * (1 + γ1) = n * (1 - p) := by
  linear_combination (1 - θ) * hγ0 + θ * hγ1 + hp

lemma caseB_mass {θ s' a' d1 d2 : ℝ} (hθ : θ < 1) (ha : (2 - s') * a' = 1)
    (hd1 : 3 * (1 - θ) * d1 = 3 - θ) (hd2 : 3 * (1 - θ) * d2 = 3 - θ - 2 * θ * a') :
    d1 * (s' - 1 - 0) + d2 * (1 - (s' - 1)) = 1 := by
  have h : 3 * (1 - θ) ≠ 0 := by intro h; linarith
  apply mul_left_cancel₀ h
  linear_combination (s' - 1) * hd1 + (2 - s') * hd2 - 2 * θ * ha

lemma caseB_M0 {θ β s' a' d1 d2 : ℝ} (hθ : θ < 1) (hs' : s' = 1 + β * (1 - θ))
    (ha : (2 - s') * a' = 1) (hd1 : 3 * (1 - θ) * d1 = 3 - θ)
    (hd2 : 3 * (1 - θ) * d2 = 3 - θ - 2 * θ * a') :
    3 * ((d1 * ((s' - 1) ^ 2 - 0 ^ 2) + d2 * (1 ^ 2 - (s' - 1) ^ 2)) / 2) = 3 / 2 - θ * β := by
  have h : 2 * (1 - θ) ≠ 0 := by intro h; linarith
  apply mul_left_cancel₀ h
  subst hs'
  linear_combination (β * (1 - θ)) ^ 2 * hd1 + (1 - (β * (1 - θ)) ^ 2) * hd2 -
    2 * θ * (1 + β * (1 - θ)) * ha

lemma caseB_rhs0 {n θ β p c : ℝ} (hp : n * p = n - 3 + θ) (hc : c = 1 / 2 - β) :
    n * (p * c + (1 - p) / 2) - (n - 3) * c = 3 / 2 - θ * β := by
  subst hc; linear_combination (-β) * hp

lemma caseB_M1 {s' a' : ℝ} (ha : (2 - s') * a' = 1) :
    (a' * (1 ^ 2 - (s' - 1) ^ 2) + 0 * (1 ^ 2 - 1 ^ 2)) / 2 = s' / 2 := by
  linear_combination (s' / 2) * ha

lemma caseB_rhs1 {n θ β p c s' : ℝ} (hp : n * p = n - 3 + θ) (hc : c = 1 / 2 - β)
    (hs' : s' = 1 + β * (1 - θ)) :
    n * (p * c + (1 - p) / 2) - (n - 3 + 1) * c = s' := by
  subst hc hs'; linear_combination (-β) * hp

set_option maxHeartbeats 1000000 in
/-- **Proposition `nc:prop:atom` (a)**, sufficiency, with the explicit complete mix of the
paper: for `n ≥ 3`, `0 < p ≤ 1 - 2/n` and `0 ≤ c < 1/2`, `F₀` is `n`-completely mixable. -/
theorem atom_sufficiency {n : ℕ} (hn : 3 ≤ n) {p c : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 - 2 / n)
    (hc0 : 0 ≤ c) (hc : c < 1 / 2) : CompletelyMixable n (atomUnif p c) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnp : (n : ℝ) * p ≤ n - 2 := by
    have := mul_le_mul_of_nonneg_left hp hn0.le
    rwa [mul_sub, mul_one, mul_div_cancel₀ _ hn0.ne'] at this
  have hp1 : p < 1 := by
    have : 0 < 2 / (n : ℝ) := by positivity
    linarith
  obtain ⟨β, hcβ⟩ : ∃ β, c = 1 / 2 - β := ⟨1 / 2 - c, by ring⟩
  have hβ0 : 0 < β := by linarith
  have hβ1 : β ≤ 1 / 2 := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = (n : ℝ) * (p * c + (1 - p) / 2) := ⟨_, rfl⟩
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = ⌊(n : ℝ) * p⌋₊ := ⟨_, rfl⟩
  have hnp0 : 0 ≤ (n : ℝ) * p := by positivity
  have hj0le : (j0 : ℝ) ≤ n * p := hj0 ▸ Nat.floor_le hnp0
  have hj0lt : (n : ℝ) * p < j0 + 1 := hj0 ▸ Nat.lt_floor_add_one _
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = (n : ℝ) * p - j0 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hnpj : (n : ℝ) * p = j0 + θ := by rw [hθ]; ring
  rcases eq_or_lt_of_le hθ0 with hθz | hθpos
  · -- `n p` is an integer
    have hj0n : j0 + 2 ≤ n := by
      have : (j0 : ℝ) + 2 ≤ n := by linarith
      exact_mod_cast this
    have hk : 2 ≤ n - j0 := by omega
    have hkR : ((n - j0 : ℕ) : ℝ) = n - j0 := by rw [Nat.cast_sub (by omega)]
    have hkR2 : (2 : ℝ) ≤ ((n - j0 : ℕ) : ℝ) := by exact_mod_cast hk
    obtain ⟨Q, hQ, hsum⟩ := stepM_mix_anti (k := n - j0) (α := 0) (m := 1 / 2) (β := 1) (a := 1)
      (b := 1) (M := (1 * ((1 / 2) ^ 2 - 0 ^ 2) + 1 * (1 ^ 2 - (1 / 2) ^ 2)) / 2) hk (by norm_num)
      (by norm_num) (by norm_num) le_rfl (by norm_num) rfl
      (cond_left (a := 2) (by norm_num) hkR2 (by norm_num))
    have hsum' : ∀ᵐ x ∂Q, ∑ k, x k = s - j0 * c := by
      filter_upwards [hsum] with x hx
      rw [hx, hkR, hs]
      linear_combination (1 / 2 - c) * hnpj - (1 / 2 - c) * hθz.symm - (1 - 2 * c) * hθz
    have h := completelyMixable_assemble2 (n := n) (j0 := j0) (j1 := j0) (by omega) (by omega)
      (θ := 0) le_rfl zero_le_one c s hQ hQ hsum' hsum'
    rwa [atom_identity (by omega) (by omega) (by omega) le_rfl zero_le_one hp0.le hp1.le
      (by norm_num) (by norm_num) zero_le_one zero_le_one zero_le_one zero_le_one
      (by linarith) (by linear_combination hnpj - hθz) (by linear_combination hnpj - hθz)] at h
  · -- `n p` is not an integer
    have hj0n : j0 + 3 ≤ n := by
      have : (j0 : ℝ) + 2 < n := by linarith
      have : j0 + 2 < n := by exact_mod_cast this
      omega
    rcases Nat.lt_or_ge (j0 + 3) n with hA | hB
    · -- case A: `n - j0 - 1 ≥ 3`: two tilted two-step laws
      have hk0 : 4 ≤ n - j0 := by omega
      have hk1 : 3 ≤ n - (j0 + 1) := by omega
      have hk0R : ((n - j0 : ℕ) : ℝ) = n - j0 := by rw [Nat.cast_sub (by omega)]
      have hk1R : ((n - (j0 + 1) : ℕ) : ℝ) = n - j0 - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hd0 : (4 : ℝ) ≤ n - j0 := by
        have : ((4 : ℕ) : ℝ) ≤ ((n - j0 : ℕ) : ℝ) := by exact_mod_cast hk0
        rwa [hk0R] at this
      have hd1 : (3 : ℝ) ≤ n - j0 - 1 := by linarith
      obtain ⟨γ0, hγ0⟩ : ∃ γ, γ = -4 * β * θ / (n - j0) := ⟨_, rfl⟩
      obtain ⟨γ1, hγ1⟩ : ∃ γ, γ = 4 * β * (1 - θ) / (n - j0 - 1) := ⟨_, rfl⟩
      have eγ0 : ((n : ℝ) - j0) * γ0 = -4 * β * θ := by
        rw [hγ0]; field_simp
      have eγ1 : ((n : ℝ) - j0 - 1) * γ1 = 4 * β * (1 - θ) := by
        rw [hγ1]; have : (n : ℝ) - j0 - 1 ≠ 0 := by linarith
        field_simp
      have hγ0n : γ0 ≤ 0 := by nlinarith
      have hγ0l : -1 / 2 ≤ γ0 := by nlinarith
      have hγ1n : 0 ≤ γ1 := by nlinarith
      have hγ1u : γ1 ≤ 2 / 3 := by nlinarith
      obtain ⟨Q0, hQ0, hsum0⟩ := stepM_mix_anti (k := n - j0) (α := 0) (m := 1 / 2) (β := 1)
        (a := 1 - γ0) (b := 1 + γ0)
        (M := ((1 - γ0) * ((1 / 2) ^ 2 - 0 ^ 2) + (1 + γ0) * (1 ^ 2 - (1 / 2) ^ 2)) / 2)
        (by omega) (by norm_num) (by norm_num) (by linarith) (by linarith) (by ring) rfl
        (cond_left (a := 4) (by norm_num) (by rw [hk0R]; exact hd0) (by nlinarith))
      obtain ⟨Q1, hQ1, hsum1⟩ := stepM_mix_mono (k := n - (j0 + 1)) (α := 0) (m := 1 / 2)
        (β := 1) (a := 1 - γ1) (b := 1 + γ1)
        (M := ((1 - γ1) * ((1 / 2) ^ 2 - 0 ^ 2) + (1 + γ1) * (1 ^ 2 - (1 / 2) ^ 2)) / 2)
        (by omega) (by norm_num) (by norm_num) (by linarith) (by linarith) (by ring) rfl
        (cond_right (a := 3) (by norm_num) (by rw [hk1R]; exact hd1) (by nlinarith))
      have hsum0' : ∀ᵐ x ∂Q0, ∑ k, x k = s - j0 * c := by
        filter_upwards [hsum0] with x hx
        rw [hx, hk0R, hs]
        exact caseA_sum0 eγ0 hnpj hcβ
      have hsum1' : ∀ᵐ x ∂Q1, ∑ k, x k = s - ((j0 + 1 : ℕ) : ℝ) * c := by
        filter_upwards [hsum1] with x hx
        rw [hx, hk1R, hs]
        push_cast
        exact caseA_sum1 eγ1 hnpj hcβ
      have h := completelyMixable_assemble2 (n := n) (j0 := j0) (j1 := j0 + 1) (by omega)
        (by omega) hθ0 hθ1.le c s hQ0 hQ1 hsum0' hsum1'
      rwa [atom_identity (by omega) (by omega) (by omega) hθ0 hθ1.le hp0.le hp1.le
        (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith)
        (by push_cast; linarith) (by push_cast; exact caseA_A eγ0 eγ1 hnpj)
        (by push_cast; exact caseA_B eγ0 eγ1 hnpj)] at h
    · -- case B: `n - j0 - 1 = 2`
      have hjn : j0 + 3 = n := le_antisymm hj0n hB
      have hjR : (j0 : ℝ) = n - 3 := by
        have : ((j0 + 3 : ℕ) : ℝ) = n := by exact_mod_cast hjn
        push_cast at this; linarith
      have hnp3 : (n : ℝ) * p = n - 3 + θ := by rw [hnpj, hjR]
      obtain ⟨s', hs'⟩ : ∃ s', s' = 1 + β * (1 - θ) := ⟨_, rfl⟩
      have hs'1 : 1 ≤ s' := by rw [hs']; nlinarith
      have hs'2 : 2 - s' ≥ (1 + θ) / 2 := by rw [hs']; nlinarith
      have h2s : 0 < 2 - s' := by linarith
      have hθ1' : 0 < 1 - θ := by linarith
      obtain ⟨a', ha'⟩ : ∃ a', a' = 1 / (2 - s') := ⟨_, rfl⟩
      obtain ⟨d1, hd1⟩ : ∃ d, d = (3 - θ) / (3 * (1 - θ)) := ⟨_, rfl⟩
      obtain ⟨d2, hd2⟩ : ∃ d, d = (3 - θ - 2 * θ * a') / (3 * (1 - θ)) := ⟨_, rfl⟩
      have ea : (2 - s') * a' = 1 := by rw [ha']; field_simp
      have ed1 : 3 * (1 - θ) * d1 = 3 - θ := by rw [hd1]; field_simp
      have ed2 : 3 * (1 - θ) * d2 = 3 - θ - 2 * θ * a' := by rw [hd2]; field_simp
      have ha'0 : 0 < a' := by rw [ha']; positivity
      have h1 : a' * (1 + θ) ≤ 2 := by
        have := mul_le_mul_of_nonneg_left hs'2 ha'0.le
        linarith
      have hfrac : 2 * θ * a' ≤ 3 - θ := by
        have h2 := mul_le_mul_of_nonneg_left h1 hθ0
        by_contra hcon
        push Not at hcon
        have h3 := mul_lt_mul_of_pos_right hcon (by linarith : (0 : ℝ) < 1 + θ)
        have h4 : (3 - θ) * (1 + θ) < 4 * θ := by linarith
        have h5 := mul_le_mul_of_nonneg_left hθ1.le hθ0
        linarith
      have h3θ : (0 : ℝ) < 3 * (1 - θ) := by linarith
      have hd2n : 0 ≤ d2 := by
        have : 3 * (1 - θ) * 0 ≤ 3 * (1 - θ) * d2 := by rw [mul_zero, ed2]; linarith
        exact le_of_mul_le_mul_left this h3θ
      have hd21 : d2 ≤ d1 := by
        have h6 : 0 ≤ 2 * θ * a' := by positivity
        have : 3 * (1 - θ) * d2 ≤ 3 * (1 - θ) * d1 := by rw [ed1, ed2]; linarith
        exact le_of_mul_le_mul_left this h3θ
      have hk0 : n - j0 = 3 := by omega
      have hk1 : n - (j0 + 1) = 2 := by omega
      have hM0 := caseB_M0 hθ1 hs' ea ed1 ed2
      obtain ⟨Q0, hQ0, hsum0⟩ := stepM_mix_anti (k := n - j0) (α := 0) (m := s' - 1) (β := 1)
        (a := d1) (b := d2)
        (M := (d1 * ((s' - 1) ^ 2 - 0 ^ 2) + d2 * (1 ^ 2 - (s' - 1) ^ 2)) / 2)
        (by rw [hk0]; norm_num) (by linarith only [hs'1]) (by linarith only [h2s]) hd2n hd21
        (caseB_mass hθ1 ea ed1 ed2) rfl
        (cond_left (a := 3) (by norm_num) (by rw [hk0]; norm_num) (by
          have := mul_le_mul hθ1.le hβ1 hβ0.le zero_le_one
          linarith))
      obtain ⟨Q1, hQ1, hsum1⟩ := stepM_mix_anti (k := n - (j0 + 1)) (α := s' - 1) (m := 1)
        (β := 1) (a := a') (b := 0)
        (M := (a' * (1 ^ 2 - (s' - 1) ^ 2) + 0 * (1 ^ 2 - 1 ^ 2)) / 2)
        (by rw [hk1]) (by linarith only [h2s]) le_rfl le_rfl ha'0.le (by linear_combination ea) rfl
        (by rw [caseB_M1 ea, hk1]; push_cast; linarith only)
      rw [stepM_shift] at hQ1
      have hsum0' : ∀ᵐ x ∂Q0, ∑ k, x k = s - j0 * c := by
        filter_upwards [hsum0] with x hx
        rw [hx, hk0, hs, hjR, caseB_rhs0 hnp3 hcβ]
        push_cast
        exact hM0
      have hsum1' : ∀ᵐ x ∂Q1, ∑ k, x k = s - ((j0 + 1 : ℕ) : ℝ) * c := by
        filter_upwards [hsum1] with x hx
        rw [hx, hk1, hs, caseB_M1 ea]
        push_cast
        rw [hjR, caseB_rhs1 hnp3 hcβ hs']
        ring
      have h := completelyMixable_assemble2 (n := n) (j0 := j0) (j1 := j0 + 1) (by omega)
        (by omega) hθ0 hθ1.le c s hQ0 hQ1 hsum0' hsum1'
      rwa [atom_identity (by omega) (by omega) (by omega) hθ0 hθ1.le hp0.le hp1.le
        (by linarith) (by linarith) (by linarith) hd2n le_rfl ha'0.le
        (by push_cast; linarith) (by
          push_cast; rw [hjR]; linear_combination ed1 + hnp3) (by
          push_cast; rw [hjR]; linear_combination ed2 + hnp3)] at h
end Sufficiency

/-! ### Necessity and Corollary `nc:cor:least` -/

section Least
open Set

lemma unifI01_singleton (y : ℝ) : unifI 0 1 {y} = 0 := by
  rw [unifI01, Measure.restrict_apply (measurableSet_singleton y)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

lemma atomUnif_apply_of_not_mem {p c : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hc : c ∉ S)
    {y : ℝ} (hy : S ⊆ {y}) : atomUnif p c S = 0 := by
  simp only [atomUnif, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Measure.dirac_apply' _ hS, Set.indicator_of_notMem hc,
    measure_mono_null hy (unifI01_singleton y)]
  simp

lemma atomUnif_singleton (p c : ℝ) : atomUnif p c {c} = ENNReal.ofReal p := by
  simp only [atomUnif, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Measure.dirac_apply_of_mem (mem_singleton c), unifI01_singleton]
  simp

/-- Proposition `nc:prop:atom` (a), necessity, for every `n ≥ 2` and every position `c ≠ 1/2` of
the atom in `[0, 1]`: if `F₀` is `n`-completely mixable, then `p ≤ 1 - 2/n`. -/
theorem atom_necessity {n : ℕ} (hn : 2 ≤ n) {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hc : c ≠ 1 / 2) (hF : CompletelyMixable n (atomUnif p c)) :
    p ≤ 1 - 2 / n := by
  have hprob := atomUnif_isProb (c := c) hp0 hp1.le
  have hint : Integrable id (atomUnif p c) :=
    integrable_of_ae_Icc (atomUnif_ae_mem hc0 hc1) continuous_id
  have hmean := integral_id_atomUnif (c := c) hp0 hp1.le
  have hμc : p * c + (1 - p) / 2 ≠ c := by
    intro h
    apply hc
    have h2 : (1 - p) * (1 / 2 - c) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact absurd h1 (by linarith)
    · linarith
  have hμI : p * c + (1 - p) / 2 ∉ Set.Icc c c := by rw [Set.Icc_self]; exact hμc
  have h := peak_interval hn hF hint hmean hμI
  have h0 : atomUnif p c (Set.Icc (n * (p * c + (1 - p) / 2) - (n - 1) * c)
      (n * (p * c + (1 - p) / 2) - (n - 1) * c) \ Set.Icc c c) = 0 :=
    atomUnif_apply_of_not_mem (measurableSet_Icc.diff measurableSet_Icc)
      (fun h => h.2 ⟨le_rfl, le_rfl⟩) (by rw [Set.Icc_self]; exact diff_subset)
  rw [h0, Set.Icc_self, atomUnif_singleton, ENNReal.toReal_ofReal hp0] at h
  simpa using h

/-- One variable is `1`-completely mixable only for a point mass, which `F₀` is not. -/
lemma atom_not_cm_one {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ¬ CompletelyMixable 1 (atomUnif p c) := by
  rintro ⟨P, hP, ⟨s, hs⟩, hm⟩
  have hprob := atomUnif_isProb (c := c) hp0 hp1.le
  have h1 : atomUnif p c {s}ᶜ = 0 := by
    have hm0 : P.map (fun x => x 0) = atomUnif p c := hm 0
    rw [← hm0, Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton s).compl]
    rw [ae_iff] at hs
    refine measure_mono_null (fun x hx => ?_) hs
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    simpa [Fin.sum_univ_one] using hx
  have h2 : atomUnif p c {s} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton s)).1 h1
  by_cases hsc : s = c
  · subst hsc
    rw [atomUnif_singleton] at h2
    have := ENNReal.ofReal_lt_one.2 hp1
    rw [h2] at this
    exact lt_irrefl _ this
  · rw [atomUnif_apply_of_not_mem (measurableSet_singleton s)
      (fun h => hsc (mem_singleton_iff.1 h).symm) subset_rfl] at h2
    simp at h2

/-- The reflection `x ↦ 1 - x` maps `F₀ = p δ_c + (1 - p) U[0,1]` to `p δ_{1-c} + (1 - p) U[0,1]`. -/
lemma map_reflect_atomUnif (p c : ℝ) :
    (atomUnif p c).map (fun x => 1 + (-1) * x) = atomUnif p (1 - c) := by
  have hm : Measurable (fun x : ℝ => 1 + (-1) * x) := by fun_prop
  rw [atomUnif, Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
    Measure.map_smul _ hm.aemeasurable, Measure.map_dirac' hm,
    map_affine_unifI 1 (-1) (by norm_num)]
  norm_num [atomUnif]
  ring_nf

lemma cm_reflect {n : ℕ} {p c : ℝ} (h : CompletelyMixable n (atomUnif p c)) :
    CompletelyMixable n (atomUnif p (1 - c)) := by
  obtain ⟨Q, hQ⟩ := h
  have := Mixes.Homothetic.isCompleteMix_map_affine hQ 1 (-1)
  rw [map_reflect_atomUnif] at this
  exact ⟨_, this⟩

/-- **Proposition `nc:prop:atom` (a).** For `n ≥ 3`, `0 < p < 1` and `0 ≤ c < 1/2`, the
distribution `F₀ = p δ_c + (1 - p) U[0,1]` is `n`-completely mixable iff `p ≤ 1 - 2/n`. -/
theorem atom_completelyMixable_iff {n : ℕ} (hn : 3 ≤ n) {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc0 : 0 ≤ c) (hc : c < 1 / 2) :
    CompletelyMixable n (atomUnif p c) ↔ p ≤ 1 - 2 / n :=
  ⟨atom_necessity (by omega) hp0.le hp1 hc0 (by linarith) hc.ne,
    fun h => atom_sufficiency hn hp0 h hc0 hc⟩

/-- **Corollary `nc:cor:least`, first statement.** For `0 < p < 1` and `c ∈ [0, 1]`, `c ≠ 1/2`,
the distribution `p δ_c + (1 - p) U[0,1]` is `n`-completely mixable (`n ≥ 1`) exactly when
`n ≥ 2/(1 - p)`. -/
theorem cor_least_iff {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : c ≠ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (atomUnif p c) ↔ 2 / (1 - p) ≤ n := by
  have hq : 0 < 1 - p := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have key : 2 / (1 - p) ≤ n ↔ p ≤ 1 - 2 / n := by
    rw [div_le_iff₀ hq, show p ≤ 1 - 2 / n ↔ 2 / n ≤ 1 - p from
      ⟨fun h => by linarith, fun h => by linarith⟩, div_le_iff₀ hnr]
    constructor <;> intro h <;> linarith
  rw [key]
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
  · constructor
    · intro h; exact absurd h (atom_not_cm_one hp0.le hp1)
    · intro h; norm_num at h; linarith
  · constructor
    · exact atom_necessity le_rfl hp0.le hp1 hc0 hc1 hc
    · intro h; norm_num at h; linarith
  · constructor
    · exact atom_necessity (by omega) hp0.le hp1 hc0 hc1 hc
    · intro h
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · exact atom_sufficiency h3 hp0 h hc0 hlt
      · have := cm_reflect (atom_sufficiency h3 hp0 h (by linarith : (0 : ℝ) ≤ 1 - c)
          (by linarith : 1 - c < 1 / 2))
        rwa [sub_sub_cancel] at this

/-- **Corollary `nc:cor:least`, second statement, explicit form** (the parameters of the proof).
Let `n₀ ≥ 3`, `1 - 2/n₀ < p < 1`, `0 < β ≤ (3/2 - √2)/(3p)` and `c = 1/2 - β`, with mean
`μ = p c + (1 - p)/2`. Then `0 < c < 1/2`; relation (`nc:eq:cx`) holds for every `n ≥ 3` (given
the classical stop-loss/convex-order result); the norm inequalities (`nc:eq:norm`) hold for every
`n ≥ 3` (given also the cited result `shmalo26b`); the mean condition holds for every `n ≥ 3`;
and `F₀` is not `n`-completely mixable for `1 ≤ n ≤ n₀`. -/
theorem cor_least_explicit {n0 : ℕ} (hn0 : 3 ≤ n0) {p β c : ℝ} (hp : 1 - 2 / n0 < p)
    (hp1 : p < 1) (hβ0 : 0 < β) (hβ : β ≤ (3 / 2 - Real.sqrt 2) / (3 * p))
    (hc : c = 1 / 2 - β) :
    (0 < c ∧ c < 1 / 2) ∧
    (H_stoploss_cx → ∀ n, 3 ≤ n → CxCond n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (H_stoploss_cx → H_shmalo26b → ∀ n, 3 ≤ n →
      NormIneqs n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (∀ n : ℕ, 3 ≤ n → MeanCond n 0 1 (p * c + (1 - p) / 2)) ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ n0 → ¬ CompletelyMixable n (atomUnif p c) := by
  have hn0r : (3 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have h2n0 : 2 / (n0 : ℝ) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hp3 : 1 / 3 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : 1.4 < Real.sqrt 2 := by nlinarith
  have hβ' : β * (3 * p) ≤ 3 / 2 - Real.sqrt 2 := (le_div_iff₀ (by positivity)).1 hβ
  have hβ2 : β < 1 / 2 := by nlinarith [mul_pos hβ0 (by linarith : (0 : ℝ) < 3 * p - 1)]
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 / 2 := by rw [hc]; linarith
  have hμ : p * c + (1 - p) / 2 = 1 / 2 - p * β := by rw [hc]; ring
  have h3μ : Real.sqrt 2 ≤ 3 * (p * c + (1 - p) / 2) := by rw [hμ]; nlinarith
  have hprob := atomUnif_isProb (c := c) hp0.le hp1.le
  have hsupp := atomUnif_ae_mem (p := p) hc0.le (by linarith)
  have hmean := integral_id_atomUnif (c := c) hp0.le hp1.le
  have hint : Integrable id (atomUnif p c) := integrable_of_ae_Icc hsupp continuous_id
  have hcx : H_stoploss_cx → ∀ n, 3 ≤ n → CxCond n (atomUnif p c) (p * c + (1 - p) / 2) := by
    intro H n hn
    have hb : Real.sqrt (((3 : ℕ) : ℝ) - 1) ≤ ((3 : ℕ) : ℝ) * (p * c + (1 - p) / 2) := by
      rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num]
      exact h3μ
    exact cxCond_of_three hsupp hmean (atom_cx H le_rfl hp0 hp1 hc0.le hc1 hb) hn
  refine ⟨⟨hc0, hc1⟩, hcx, fun H H2 n hn => ?_, fun n hn => ?_, fun n hn1 hnn0 hF => ?_⟩
  · refine H2 n _ _ (by omega) hprob ⟨1, ?_⟩ hint hmean (hcx H n hn)
    exact measure_mono_null (show (Set.Icc (-1 : ℝ) 1)ᶜ ⊆ {x | x ∉ Set.Icc (0 : ℝ) 1} from
      fun x hx h => hx ⟨by linarith [h.1], h.2⟩) (ae_iff.1 hsupp)
  · have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have : 1 / (n : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hnr
    constructor
    · rw [hμ]; nlinarith
    · rw [hμ]; nlinarith [mul_pos hp0 hβ0]
  · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · exact atom_not_cm_one hp0.le hp1 hF
    · have h := atom_necessity h2 hp0.le hp1 hc0.le (by linarith) hc1.ne hF
      have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have : 2 / (n0 : ℝ) ≤ 2 / n :=
        div_le_div_of_nonneg_left (by norm_num) hnr (by exact_mod_cast hnn0)
      linarith

/-- **Corollary `nc:cor:least`, second statement.** For every `n₀` there are `p` and `c` such
that `F₀ = p δ_c + (1 - p) U[0,1]` satisfies (`nc:eq:cx`), the norm inequalities (`nc:eq:norm`)
and the mean condition for every `n ≥ 3` (the first two under the hypotheses named), while it is
not `n`-completely mixable for any `1 ≤ n ≤ n₀`. -/
theorem cor_least_exists (n0 : ℕ) : ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ c < 1 / 2 ∧
    (H_stoploss_cx → ∀ n, 3 ≤ n → CxCond n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (H_stoploss_cx → H_shmalo26b → ∀ n, 3 ≤ n →
      NormIneqs n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (∀ n : ℕ, 3 ≤ n → MeanCond n 0 1 (p * c + (1 - p) / 2)) ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ n0 → ¬ CompletelyMixable n (atomUnif p c) := by
  set m := max n0 3 with hm
  have hm3 : 3 ≤ m := le_max_right _ _
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hp : 1 - 2 / (m : ℝ) < 1 - 1 / m := by
    have : 1 / (m : ℝ) < 2 / m := div_lt_div_of_pos_right (by norm_num) (by linarith)
    linarith
  have hp1 : 1 - 1 / (m : ℝ) < 1 := by
    have : 0 < 1 / (m : ℝ) := by positivity
    linarith
  have hp0 : 0 < 1 - 1 / (m : ℝ) := by
    have : 1 / (m : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hmr
    linarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : Real.sqrt 2 < 1.42 := by nlinarith
  have hβ : (1 / 40 : ℝ) ≤ (3 / 2 - Real.sqrt 2) / (3 * (1 - 1 / (m : ℝ))) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  obtain ⟨hc, hcx, hnorm, hmean, hnot⟩ :=
    cor_least_explicit hm3 hp hp1 (by norm_num : (0 : ℝ) < 1 / 40) hβ rfl
  exact ⟨_, _, hp0, hp1, hc.1, hc.2, hcx, hnorm, hmean,
    fun n hn1 hn => hnot n hn1 (le_trans hn (le_max_left _ _))⟩
end Least

end Mixes.NormAtom
