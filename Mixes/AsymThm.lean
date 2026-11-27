import Mathlib
import Mixes.Symm
import Mixes.AsymWindow

/-!
# Couplings with a concentrated sum, and windows for distributions containing a uniform part

Section `as:sec:asym` of draft 14: Lemma `as:lem:conc`, Theorem `as:thm:window`,
Corollary `as:cor:interval`.

## Main results

* `lem_conc_a` (Lemma `as:lem:conc` (a)): distributions `T_j` on `ℝ` carried by intervals of
  length `ℓ` admit a coupling whose sum lies in an interval of length `ℓ`, hence within `ℓ` of
  `∑ m_{T_j}` (antitone quantile coupling and gluing, `conc_a_aux`, `exists_glue`).
* `lem_conc_b` (Lemma `as:lem:conc` (b)): the grid coupling `gridCoupling`
  (`Y_j = Q_T((σ(j) - 1 + W)/k)`) has marginals `T` and sum within `ℓ` of `k m_T`.
* `lem_conc_c` (Lemma `as:lem:conc` (c)): in `EuclideanSpace ℝ (Fin d)` (any `d`), for `T`
  supported in a set of diameter `≤ ℓ`, a coupling of `k` copies with `‖∑ Y_j - k m_T‖ ≤ 2 d ℓ`.
  Assumes `H_steinitz` (Steinitz lemma with the constant `d` of Grinberg–Sevastyanov 1980).
* `ThmWindow d` is a verbatim copy of `Mixes.AsymGeneral.H_thm_window d` (Theorem
  `as:thm:window`); `thm_window_d1_proved : ThmWindow 1` (no hypothesis) and
  `thm_window_proved (hS : H_steinitz) d : ThmWindow d`.
* `thm_window_one_proved`: Theorem `as:thm:window` for `d = 1` stated on `ℝ`.
* `cor_interval_proved`, `cor_interval_n_proved`, `cor_interval_density_proved`
  (Corollary `as:cor:interval`).

Proposition `as:prop:window` enters through verbatim copies `PropWindow`, `PropWindowReal` of
the statements of `Mixes.AsymWindow`, discharged by `Mixes.AsymWindow.propWindow(Real)`
(`propWindow_proved`, `propWindowReal_proved`). The theorems without the suffix `_proved` take
these statements as hypotheses.

## Copied definitions

`AggSetC n F` is definitionally `Mixes.AsymGeneral.AggSet n F` and
`Mixes.AsymWindow.InAgg (fun _ => F)`; `boxE`, `cdConst`, `SuppDiam`, `Rd` are copies of the
definitions of `Mixes.AsymGeneral`, and `boxW`, `InAgg`, `PropWindow`, `PropWindowReal` of those
of `Mixes.AsymWindow`. (`Mixes.AsymGeneral` has no compiled olean, so it is not imported; the
bridge `Mixes.AsymGeneral.H_thm_window d` is `thm_window_proved hS d` by `exact`.)
-/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section
set_option linter.unusedSectionVars false
namespace Mixes.AsymThm

section Agg
variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]

/-- The aggregation set `𝒜_n(F_1, …, F_n)`: the distributions of `X_1 + ⋯ + X_n` over all
random vectors (here: probability measures on tuples) with marginals `F_j`. -/
def AggSet {n : ℕ} (F : Fin n → Measure E) : Set (Measure E) :=
  {ν | ∃ P : Measure (Fin n → E), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = F j) ∧
    P.map (fun x => ∑ j, x j) = ν}

/-- `𝒜_n(F)`. -/
def AggSetC (n : ℕ) (F : Measure E) : Set (Measure E) := AggSet (fun _ : Fin n => F)

end Agg

section Symm
variable {E ι : Type*} [MeasurableSpace E] [Fintype ι] [DecidableEq ι]

lemma symmetrize_isProb {n : ℕ} (hι : Fintype.card ι = n) (Q : Measure (ι → E))
    [IsProbabilityMeasure Q] : IsProbabilityMeasure (Mixes.symmetrize n Q) := by
  have hmeas : ∀ σ : Fin n ≃ ι, Measurable (fun z : ι → E => fun k => z (σ k)) :=
    fun σ => Measurable.of_eval (fun k => measurable_pi_apply _)
  have hN : (Fintype.card (Fin n ≃ ι) : ℝ≥0∞) ≠ 0 := by
    have : Nonempty (Fin n ≃ ι) := ⟨(Fintype.equivFinOfCardEq hι).symm⟩
    exact_mod_cast Fintype.card_ne_zero
  constructor
  simp only [Mixes.symmetrize, smul_apply, sum_apply,
    smul_eq_mul, Measure.map_apply (hmeas _) MeasurableSet.univ, Set.preimage_univ, measure_univ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _)

lemma symmetrize_map_eval {n : ℕ} (hn : 0 < n) (hι : Fintype.card ι = n) (Q : Measure (ι → E))
    (k : Fin n) : (Mixes.symmetrize n Q).map (fun x => x k) =
      (n : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun z => z i) := by
  have hmeas : ∀ σ : Fin n ≃ ι, Measurable (fun z : ι → E => fun k => z (σ k)) :=
    fun σ => Measurable.of_eval (fun k => measurable_pi_apply _)
  have hN : (Fintype.card (Fin n ≃ ι) : ℝ≥0∞) ≠ 0 := by
    have : Nonempty (Fin n ≃ ι) := ⟨(Fintype.equivFinOfCardEq hι).symm⟩
    exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card (Fin n ≃ ι) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  ext t ht
  rw [Measure.map_apply (measurable_pi_apply k) ht]
  have hpre : ∀ σ : Fin n ≃ ι, (fun z : ι → E => fun k => z (σ k)) ⁻¹' ((fun x => x k) ⁻¹' t) =
      (fun z : ι → E => z (σ k)) ⁻¹' t := fun σ => rfl
  have hmap : ∀ i, Q.map (fun z : ι → E => z i) t = Q ((fun z : ι → E => z i) ⁻¹' t) :=
    fun i => Measure.map_apply (measurable_pi_apply i) ht
  simp only [Mixes.symmetrize, smul_apply, sum_apply,
    smul_eq_mul, Measure.map_apply (hmeas _) (measurable_pi_apply k ht), hpre, hmap]
  have hc := Mixes.nsmul_sum_equiv_apply (fun i => Q ((fun z : ι → E => z i) ⁻¹' t)) k
  simp only [nsmul_eq_mul] at hc
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  set X := ∑ σ : Fin n ≃ ι, Q ((fun z : ι → E => z (σ k)) ⁻¹' t)
  set S := ∑ i, Q ((fun z : ι → E => z i) ⁻¹' t)
  set N := (Fintype.card (Fin n ≃ ι) : ℝ≥0∞)
  calc N⁻¹ * X = N⁻¹ * ((n : ℝ≥0∞)⁻¹ * (n * X)) := by
        rw [← mul_assoc ((n : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel hn0 hnt, one_mul]
    _ = N⁻¹ * ((n : ℝ≥0∞)⁻¹ * (N * S)) := by rw [hc]
    _ = (n : ℝ≥0∞)⁻¹ * S := by
        rw [mul_left_comm ((n : ℝ≥0∞)⁻¹), ← mul_assoc, ENNReal.inv_mul_cancel hN hNt, one_mul]

lemma symmetrize_map_sum [AddCommMonoid E] [MeasurableAdd₂ E] {n : ℕ} (hι : Fintype.card ι = n)
    (Q : Measure (ι → E)) :
    (Mixes.symmetrize n Q).map (fun x => ∑ k, x k) = Q.map (fun z => ∑ i, z i) := by
  have hmeas : ∀ σ : Fin n ≃ ι, Measurable (fun z : ι → E => fun k => z (σ k)) :=
    fun σ => Measurable.of_eval (fun k => measurable_pi_apply _)
  have hN : (Fintype.card (Fin n ≃ ι) : ℝ≥0∞) ≠ 0 := by
    have : Nonempty (Fin n ≃ ι) := ⟨(Fintype.equivFinOfCardEq hι).symm⟩
    exact_mod_cast Fintype.card_ne_zero
  have hsum : Measurable (fun x : Fin n → E => ∑ k, x k) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hsum' : Measurable (fun x : ι → E => ∑ k, x k) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  ext t ht
  rw [Measure.map_apply hsum ht, Measure.map_apply hsum' ht]
  have hpre : ∀ σ : Fin n ≃ ι, (fun z : ι → E => fun k => z (σ k)) ⁻¹'
      ((fun x : Fin n → E => ∑ k, x k) ⁻¹' t) = (fun z : ι → E => ∑ i, z i) ⁻¹' t := by
    intro σ; ext z; simp [Equiv.sum_comp σ z]
  simp only [Mixes.symmetrize, smul_apply, sum_apply,
    smul_eq_mul, Measure.map_apply (hmeas _) (hsum ht), hpre, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _), one_mul]

end Symm

/-- The uniform distribution on `(0,1)`. -/
abbrev unif01 : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)

instance : IsProbabilityMeasure unif01 := ⟨by simp⟩

lemma unif01_Iic (t : ℝ) : unif01 (Iic t) = ENNReal.ofReal (min (max t 0) 1) := by
  rw [Measure.restrict_apply measurableSet_Iic]
  rcases le_or_gt t 0 with h | h
  · have : Iic t ∩ Ioo (0:ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]
      intro h1; linarith [h1.2.1, h1.1]
    rw [this]; simp [max_eq_right h]
  rcases lt_or_ge t 1 with h' | h'
  · have : Iic t ∩ Ioo (0:ℝ) 1 = Ioc 0 t := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Ioc, max_eq_left h.le, min_eq_left h'.le, sub_zero]
  · have : Iic t ∩ Ioo (0:ℝ) 1 = Ioo 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · rintro h2; exact ⟨by linarith [h2.2], h2⟩
    rw [this, Real.volume_Ioo, max_eq_left (by linarith), min_eq_right h']; simp

/-- `∑_{i<k} clamp(y - i) = clamp(y, 0, k)`. -/
lemma sum_clamp (y : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, min (max (y - i) 0) 1 = min (max y 0) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rcases le_or_gt y 0 with h | h
    · have h1 : max (y - k) 0 = 0 := max_eq_right (by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith)
      rw [max_eq_right h, h1]; simp; positivity
    rcases le_or_gt y k with h2 | h2
    · have h1 : max (y - k) 0 = 0 := max_eq_right (by linarith)
      rw [max_eq_left h.le, h1, min_eq_left h2, min_eq_left (by linarith)]; simp; linarith
    · rw [max_eq_left h.le, max_eq_left (by linarith : (0:ℝ) ≤ y - k), min_eq_right h2.le]
      rcases le_or_gt (y - k) 1 with h3 | h3
      · rw [min_eq_left h3, min_eq_left (by linarith)]; ring
      · rw [min_eq_right h3.le, min_eq_right (by linarith)]

/-- The grid: `(1/k) ∑_{i<k} law((i + W)/k) = U(0,1)`. -/
lemma unif01_grid {k : ℕ} (hk : 0 < k) :
    (k : ℝ≥0∞)⁻¹ • ∑ i : Fin k, unif01.map (fun w => ((i : ℝ) + w) / k) = unif01 := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hm : ∀ i : Fin k, Measurable (fun w : ℝ => ((i : ℝ) + w) / k) := fun i => by fun_prop
  refine (Measure.ext_of_Iic _ _ fun x => ?_).symm
  simp only [smul_apply, sum_apply, smul_eq_mul]
  have hpre : ∀ i : Fin k, (fun w : ℝ => ((i : ℝ) + w) / k) ⁻¹' Iic x = Iic (k * x - i) := by
    intro i; ext w; simp only [mem_preimage, mem_Iic, div_le_iff₀ hkpos]; constructor <;> intro h <;> linarith
  simp only [Measure.map_apply (hm _) measurableSet_Iic, hpre, unif01_Iic]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  have hs := sum_clamp (k * x) k
  rw [Finset.sum_range (fun i => min (max (k * x - i) 0) 1)] at hs
  rw [hs, eq_comm]
  have hc : min (max ((k:ℝ) * x) 0) k = k * min (max x 0) 1 := by
    rcases le_or_gt x 0 with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith)]; simp
    rcases le_or_gt x 1 with h' | h'
    · rw [max_eq_left h.le, max_eq_left (by positivity), min_eq_left h', min_eq_left (by nlinarith)]
    · rw [max_eq_left h.le, max_eq_left (by positivity), min_eq_right h'.le,
        min_eq_right (by nlinarith)]
      ring
  rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hk.ne') (ENNReal.natCast_ne_top _), one_mul]

/-- The quantile function of a distribution `μ` carried by `[a, b]`:
`Q(u) = inf {x ∈ [a, b] : u ≤ G(x)}` (with `b` added, so that it is defined for all `u`). -/
def qf (μ : Measure ℝ) (a b : ℝ) (u : ℝ) : ℝ := sInf (insert b {x | x ∈ Icc a b ∧ u ≤ cdf μ x})

section Quantile
variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}

lemma qf_set_bdd (u : ℝ) : BddBelow (insert b {x | x ∈ Icc a b ∧ u ≤ cdf μ x}) := by
  refine ⟨min a b, fun x hx => ?_⟩
  rcases hx with rfl | hx
  · exact min_le_right _ _
  · exact (min_le_left _ _).trans hx.1.1

lemma qf_le (u : ℝ) : qf μ a b u ≤ b := csInf_le (qf_set_bdd u) (mem_insert _ _)

lemma le_qf (hab : a ≤ b) (u : ℝ) : a ≤ qf μ a b u := by
  refine le_csInf ⟨b, mem_insert _ _⟩ fun x hx => ?_
  rcases hx with rfl | hx
  · exact hab
  · exact hx.1.1

lemma qf_mono : Monotone (qf μ a b) := by
  intro u u' huu
  refine csInf_le_csInf (qf_set_bdd u) ⟨b, mem_insert _ _⟩ ?_
  intro x hx
  rcases hx with rfl | hx
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨hx.1, huu.trans hx.2⟩

lemma measurable_qf : Measurable (qf μ a b) := qf_mono.measurable

lemma cdf_eq_one_of_le (hμ : μ (Icc a b)ᶜ = 0) {x : ℝ} (hx : b ≤ x) : cdf μ x = 1 := by
  have h1 : μ (Iic x) = 1 := by
    rw [← prob_compl_eq_zero_iff measurableSet_Iic]
    exact measure_mono_null (fun y hy => by
      simp only [mem_compl_iff, mem_Icc, not_and, not_le] at hy ⊢
      intro _; exact lt_of_le_of_lt hx (not_le.1 hy)) hμ
  rw [cdf_eq_real, measureReal_def, h1]; rfl

lemma cdf_eq_zero_of_lt (hμ : μ (Icc a b)ᶜ = 0) {x : ℝ} (hx : x < a) : cdf μ x = 0 := by
  have h1 : μ (Iic x) = 0 := measure_mono_null (fun y hy => by
      simp only [mem_Iic] at hy
      simp only [mem_compl_iff, mem_Icc, not_and, not_le]
      intro h; exact absurd h (not_le.2 (lt_of_le_of_lt hy hx))) hμ
  rw [cdf_eq_real, measureReal_def, h1]; rfl

lemma le_cdf_qf (hμ : μ (Icc a b)ᶜ = 0) {u : ℝ} (hu1 : u ≤ 1) : u ≤ cdf μ (qf μ a b u) := by
  set t := qf μ a b u
  have hy : ∀ y, t < y → u ≤ cdf μ y := by
    intro y hty
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt ⟨b, mem_insert _ _⟩ hty
    have : u ≤ cdf μ z := by
      rcases hz with rfl | hz
      · rw [cdf_eq_one_of_le hμ le_rfl]; exact hu1
      · exact hz.2
    exact this.trans (monotone_cdf μ hzy.le)
  have ht : Filter.Tendsto (cdf μ) (nhdsWithin t (Ioi t)) (nhds (cdf μ t)) :=
    ((cdf μ).right_continuous t).mono Ioi_subset_Ici_self
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun y hy' => hy y hy')

lemma qf_le_iff (hμ : μ (Icc a b)ᶜ = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (x : ℝ) : qf μ a b u ≤ x ↔ u ≤ cdf μ x := by
  constructor
  · intro h; exact (le_cdf_qf hμ hu1).trans (monotone_cdf μ h)
  · intro h
    rcases le_or_gt b x with hbx | hbx
    · exact (qf_le u).trans hbx
    rcases lt_or_ge x a with hxa | hxa
    · rw [cdf_eq_zero_of_lt hμ hxa] at h; linarith
    · exact csInf_le (qf_set_bdd u) (mem_insert_of_mem _ ⟨⟨hxa, hbx.le⟩, h⟩)

/-- Inverse transform sampling: `Q(U) ∼ μ` for `U` uniform on `(0,1)`. -/
theorem map_qf (hμ : μ (Icc a b)ᶜ = 0) : unif01.map (qf μ a b) = μ := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply measurable_qf measurableSet_Iic,
    Measure.restrict_apply (measurable_qf measurableSet_Iic)]
  have : qf μ a b ⁻¹' Iic x ∩ Ioo 0 1 = Iic (cdf μ x) ∩ Ioo 0 1 := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · rintro ⟨h, hu⟩; exact ⟨(qf_le_iff hμ hu.1 hu.2.le x).1 h, hu⟩
    · rintro ⟨h, hu⟩; exact ⟨(qf_le_iff hμ hu.1 hu.2.le x).2 h, hu⟩
  rw [this, ← Measure.restrict_apply measurableSet_Iic, unif01_Iic,
    max_eq_left (cdf_nonneg μ x), min_eq_left (cdf_le_one μ x), ofReal_cdf]

end Quantile

/-! ### Values in an interval, means -/

/-- A function on a set whose values differ pairwise by at most `ℓ` takes its values in an
interval of length `ℓ`. -/
lemma exists_Icc_of_osc {S : Set ℝ} (hS : S.Nonempty) {f : ℝ → ℝ} {ℓ : ℝ}
    (h : ∀ w ∈ S, ∀ w' ∈ S, f w - f w' ≤ ℓ) : ∃ c, ∀ w ∈ S, f w ∈ Icc c (c + ℓ) := by
  obtain ⟨w0, hw0⟩ := hS
  have hbdd : BddBelow (f '' S) := ⟨f w0 - ℓ, by
    rintro _ ⟨w, hw, rfl⟩; linarith [h w0 hw0 w hw]⟩
  refine ⟨sInf (f '' S), fun w hw => ⟨csInf_le hbdd ⟨w, hw, rfl⟩, ?_⟩⟩
  have : f w - ℓ ≤ sInf (f '' S) := by
    refine le_csInf ⟨f w0, w0, hw0, rfl⟩ ?_
    rintro _ ⟨w', hw', rfl⟩; linarith [h w hw w' hw']
  linarith

lemma integrable_of_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (hμ : μ (Icc a b)ᶜ = 0) : Integrable id μ := by
  refine Integrable.mono' (integrable_const (max |a| |b|)) aestronglyMeasurable_id ?_
  have : ∀ᵐ x ∂μ, x ∈ Icc a b := by
    rw [ae_iff]; exact hμ
  filter_upwards [this] with x hx
  simp only [id, Real.norm_eq_abs]
  exact abs_le_max_abs_abs hx.1 hx.2

/-- If the coordinates have integrable marginals and the sum lies in `[c, c + ℓ]` almost surely,
then it lies within `ℓ` of the sum of the means. -/
lemma abs_sum_sub_mean_le {k : ℕ} (P : Measure (Fin k → ℝ)) [IsProbabilityMeasure P]
    (T : Fin k → Measure ℝ) (hPT : ∀ j, P.map (fun y => y j) = T j)
    (hint : ∀ j, Integrable id (T j)) {c ℓ : ℝ} (hc : ∀ᵐ y ∂P, ∑ j, y j ∈ Icc c (c + ℓ)) :
    ∀ᵐ y ∂P, |∑ j, y j - ∑ j, ∫ x, x ∂(T j)| ≤ ℓ := by
  have hint' : ∀ j, Integrable (fun y : Fin k → ℝ => y j) P := by
    intro j
    have := hint j
    rw [← hPT j] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply j).aemeasurable).1 this
  have hmean : ∫ y, ∑ j, y j ∂P = ∑ j, ∫ x, x ∂(T j) := by
    rw [integral_finsetSum _ fun j _ => hint' j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hPT j, integral_map (measurable_pi_apply j).aemeasurable
      (aestronglyMeasurable_id (μ := P.map (fun y => y j)))]
  have hsi : Integrable (fun y : Fin k → ℝ => ∑ j, y j) P := integrable_finsetSum _ fun j _ => hint' j
  have h1 : c ≤ ∫ y, ∑ j, y j ∂P := by
    have := integral_mono_ae (integrable_const c) hsi (by filter_upwards [hc] with y hy; exact hy.1)
    simpa using this
  have h2 : ∫ y, ∑ j, y j ∂P ≤ c + ℓ := by
    have := integral_mono_ae hsi (integrable_const (c + ℓ)) (by filter_upwards [hc] with y hy; exact hy.2)
    simpa using this
  rw [hmean] at h1 h2
  filter_upwards [hc] with y hy
  rw [abs_le]; constructor <;> linarith [hy.1, hy.2]

/-! ### Lemma `as:lem:conc` (b): the grid coupling -/

/-- The grid: `w ↦ (Q_T((i + w)/k))_{i<k}`. -/
def gridMap (μ : Measure ℝ) (a b : ℝ) (k : ℕ) (w : ℝ) : Fin k → ℝ :=
  fun i => qf μ a b (((i : ℕ) + w) / k)

/-- The coupling of Lemma `as:lem:conc` (b): `Y_j = Q_T((σ(j) - 1 + W)/k)` with `W` uniform on
`(0,1)` and `σ` an independent uniformly random permutation (`Mixes.symmetrize`). -/
def gridCoupling (μ : Measure ℝ) (a b : ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  Mixes.symmetrize k (unif01.map (gridMap μ a b k))

lemma measurable_gridMap (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) (k : ℕ) : Measurable (gridMap μ a b k) :=
  measurable_pi_iff.2 fun i => measurable_qf.comp (by fun_prop)

/-- Telescoping: the oscillation of `w ↦ ∑_i q((i + w)/k)` is at most the range of `q`. -/
lemma grid_osc {q : ℝ → ℝ} (hq : Monotone q) {a b : ℝ} (hqa : ∀ u, a ≤ q u) (hqb : ∀ u, q u ≤ b)
    {k : ℕ} (hk : 0 < k) {w w' : ℝ} (hw1 : w' ≤ w + 1) :
    ∑ i : Fin k, q (((i : ℕ) + w') / k) - ∑ i : Fin k, q (((i : ℕ) + w) / k) ≤ b - a := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_eq_sum_range (fun i => q ((i + w') / k) - q ((i + w) / k))]
  have key : ∀ j : ℕ, ∑ i ∈ Finset.range (j + 1), (q ((i + w') / k) - q ((i + w) / k)) ≤
      q ((j + w') / k) - q (w / k) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have : q ((j + w') / k) ≤ q (((j + 1 : ℕ) + w) / k) := by
        apply hq; push_cast; apply div_le_div_of_nonneg_right _ hkpos.le; linarith
      push_cast at this ⊢; linarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  linarith [key j, hqa (w / ↑(j + 1)), hqb ((j + w') / ↑(j + 1))]

section GridB
variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}

lemma gridCoupling_isProb (k : ℕ) : IsProbabilityMeasure (gridCoupling μ a b k) :=
  symmetrize_isProb (by simp) _

lemma gridCoupling_map_eval (hμ : μ (Icc a b)ᶜ = 0) {k : ℕ} (hk : 0 < k) (j : Fin k) :
    (gridCoupling μ a b k).map (fun y => y j) = μ := by
  rw [gridCoupling, symmetrize_map_eval hk (by simp)]
  have h1 : ∀ i : Fin k, (unif01.map (gridMap μ a b k)).map (fun z => z i) =
      (unif01.map (fun w => ((i : ℕ) + w) / (k : ℝ))).map (qf μ a b) := by
    intro i
    rw [Measure.map_map (measurable_pi_apply i) (measurable_gridMap μ a b k),
      Measure.map_map measurable_qf (by fun_prop)]
    rfl
  simp only [h1]
  rw [← Measure.map_finset_sum' measurable_qf.aemeasurable,
    ← Measure.map_smul _ measurable_qf.aemeasurable, unif01_grid hk, map_qf hμ]

lemma gridCoupling_sum (hab : a ≤ b) {k : ℕ} (hk : 0 < k) :
    ∃ c, ∀ᵐ y ∂(gridCoupling μ a b k), ∑ j, y j ∈ Icc c (c + (b - a)) := by
  set s : ℝ → ℝ := fun w => ∑ i : Fin k, qf μ a b (((i : ℕ) + w) / k)
  obtain ⟨c, hc⟩ := exists_Icc_of_osc (S := Ioo (0:ℝ) 1) ⟨1/2, by norm_num, by norm_num⟩ (f := s)
    (ℓ := b - a) (by
      intro w hw w' hw'
      rcases le_total w' w with h | h
      · exact grid_osc (qf_mono (μ := μ)) (le_qf (μ := μ) hab) (qf_le (μ := μ) (a := a)) hk
          (by linarith [hw.2, hw'.1])
      · have h0 : 0 ≤ s w' - s w := by
          simp only [s]; rw [← Finset.sum_sub_distrib]
          exact Finset.sum_nonneg fun i _ => sub_nonneg.2 (qf_mono (by
            apply div_le_div_of_nonneg_right _ (by positivity); linarith))
        linarith)
  refine ⟨c, ?_⟩
  have hsum : Measurable (fun y : Fin k → ℝ => ∑ j, y j) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hmS : MeasurableSet (Icc c (c + (b - a))) := measurableSet_Icc
  refine (ae_map_iff hsum.aemeasurable hmS).1 ?_
  rw [gridCoupling, symmetrize_map_sum (by simp), Measure.map_map hsum (measurable_gridMap μ a b k)]
  refine (ae_map_iff (hsum.comp (measurable_gridMap μ a b k)).aemeasurable hmS).2 ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun w hw => hc w hw

end GridB

section Glue
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ]

/-- Gluing: two probability measures whose images under `f` and `g` agree are the marginals of
a measure on the product on which `f x = g y` almost surely. -/
theorem exists_glue (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : α → γ} {g : β → γ} (hf : Measurable f) (hg : Measurable g)
    (h : μ.map f = ν.map g) :
    ∃ Γ : Measure (α × β), IsProbabilityMeasure Γ ∧ Γ.map Prod.fst = μ ∧ Γ.map Prod.snd = ν ∧
      ∀ᵐ p ∂Γ, f p.1 = g p.2 := by
  set ρ : Measure (γ × α) := μ.map (fun a => (f a, a))
  set ρ' : Measure (γ × β) := ν.map (fun b => (g b, b))
  have hmρ : Measurable (fun a => (f a, a)) := hf.prodMk measurable_id
  have hmρ' : Measurable (fun b => (g b, b)) := hg.prodMk measurable_id
  have hfst : ρ.fst = ρ'.fst := by
    rw [Measure.fst, Measure.fst, Measure.map_map measurable_fst hmρ,
      Measure.map_map measurable_fst hmρ']
    exact h
  set σ := ρ.fst
  set κ := ρ.condKernel
  set κ' := ρ'.condKernel
  set Γ0 : Measure (γ × (α × β)) := σ ⊗ₘ (κ ×ₖ κ')
  have hm1 : Measurable (fun p : γ × (α × β) => (p.2.1, p.2.2)) := by fun_prop
  refine ⟨Γ0.map (fun p => (p.2.1, p.2.2)), inferInstance, ?_, ?_, ?_⟩
  · have e1 : Γ0.map (Prod.map id Prod.fst) = ρ := by
      rw [← Measure.compProd_map measurable_fst]
      have : (κ ×ₖ κ').map Prod.fst = κ := by
        rw [← Kernel.fst_eq]; exact Kernel.fst_prod _ _
      rw [this]; exact ρ.disintegrate ρ.condKernel
    rw [Measure.map_map measurable_fst hm1]
    have : (Prod.fst ∘ fun p : γ × (α × β) => (p.2.1, p.2.2)) = Prod.snd ∘ Prod.map id Prod.fst := by
      funext p; rfl
    rw [this, ← Measure.map_map measurable_snd (measurable_id.prodMap measurable_fst), e1,
      Measure.map_map measurable_snd hmρ]
    exact Measure.map_id
  · have e1 : Γ0.map (Prod.map id Prod.snd) = ρ' := by
      rw [← Measure.compProd_map measurable_snd]
      have : (κ ×ₖ κ').map Prod.snd = κ' := by
        rw [← Kernel.snd_eq]; exact Kernel.snd_prod _ _
      rw [this, hfst]; exact ρ'.disintegrate ρ'.condKernel
    rw [Measure.map_map measurable_snd hm1]
    have : (Prod.snd ∘ fun p : γ × (α × β) => (p.2.1, p.2.2)) = Prod.snd ∘ Prod.map id Prod.snd := by
      funext p; rfl
    rw [this, ← Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd), e1,
      Measure.map_map measurable_snd hmρ']
    exact Measure.map_id
  · rw [ae_map_iff hm1.aemeasurable]
    swap
    · exact measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd)
    -- ρ is carried by the graph of f
    have hρ : ∀ᵐ x ∂(σ ⊗ₘ κ), x.1 = f x.2 := by
      rw [ρ.disintegrate ρ.condKernel]
      exact (ae_map_iff hmρ.aemeasurable (measurableSet_eq_fun measurable_fst
        (hf.comp measurable_snd))).2 (Filter.Eventually.of_forall fun a => rfl)
    have hρ' : ∀ᵐ x ∂(σ ⊗ₘ κ'), x.1 = g x.2 := by
      rw [hfst, ρ'.disintegrate ρ'.condKernel]
      exact (ae_map_iff hmρ'.aemeasurable (measurableSet_eq_fun measurable_fst
        (hg.comp measurable_snd))).2 (Filter.Eventually.of_forall fun a => rfl)
    have hs1 : MeasurableSet {x : γ × α | x.1 = f x.2} :=
      measurableSet_eq_fun measurable_fst (hf.comp measurable_snd)
    have hs2 : MeasurableSet {x : γ × β | x.1 = g x.2} :=
      measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)
    have hs3 : MeasurableSet {p : γ × (α × β) | f p.2.1 = g p.2.2} :=
      measurableSet_eq_fun (hf.comp (measurable_fst.comp measurable_snd))
        (hg.comp (measurable_snd.comp measurable_snd))
    replace hρ := (Measure.ae_compProd_iff hs1).1 hρ
    replace hρ' := (Measure.ae_compProd_iff hs2).1 hρ'
    refine (Measure.ae_compProd_iff hs3).2 ?_
    filter_upwards [hρ, hρ'] with c h1 h2
    rw [Kernel.prod_apply]
    have e1 := (Measure.quasiMeasurePreserving_fst (μ := κ c) (ν := κ' c)).ae h1
    have e2 := (Measure.quasiMeasurePreserving_snd (μ := κ c) (ν := κ' c)).ae h2
    filter_upwards [e1, e2] with x hx1 hx2
    exact hx1.symm.trans hx2

end Glue

/-! ### Lemma `as:lem:conc` (a): sequential antitone couplings -/

lemma unif01_map_one_sub : unif01.map (fun v => 1 - v) = unif01 := by
  have hmp : MeasurePreserving (fun v : ℝ => 1 - v) volume volume := Measure.measurePreserving_sub_left volume 1
  have hpre : (fun v : ℝ => 1 - v) ⁻¹' Ioo 0 1 = Ioo 0 1 := by
    ext v; simp only [mem_preimage, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have := hmp.restrict_preimage (s := Ioo (0:ℝ) 1) measurableSet_Ioo
  rw [hpre] at this
  exact this.map_eq

/-- The antitone coupling of two distributions carried by intervals of length at most `ℓ`:
`(Q_σ(V), Q_τ(1 - V))`; its sum takes values in an interval of length at most `ℓ`. -/
lemma antitone_coupling {σ τ : Measure ℝ} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    {a₁ b₁ a₂ b₂ ℓ : ℝ} (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂) (h₁ : b₁ - a₁ ≤ ℓ) (h₂ : b₂ - a₂ ≤ ℓ)
    (hσ : σ (Icc a₁ b₁)ᶜ = 0) (hτ : τ (Icc a₂ b₂)ᶜ = 0) :
    ∃ γ : Measure (ℝ × ℝ), IsProbabilityMeasure γ ∧ γ.map Prod.fst = σ ∧ γ.map Prod.snd = τ ∧
      ∃ c, ∀ᵐ p ∂γ, p.1 + p.2 ∈ Icc c (c + ℓ) := by
  set q₁ := qf σ a₁ b₁
  set q₂ := qf τ a₂ b₂
  have hm : Measurable (fun v : ℝ => (q₁ v, q₂ (1 - v))) :=
    measurable_qf.prodMk (measurable_qf.comp (by fun_prop))
  refine ⟨unif01.map (fun v => (q₁ v, q₂ (1 - v))), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]; exact map_qf hσ
  · rw [Measure.map_map measurable_snd hm]
    have : (Prod.snd ∘ fun v : ℝ => (q₁ v, q₂ (1 - v))) = q₂ ∘ (fun v => 1 - v) := rfl
    rw [this, ← Measure.map_map measurable_qf (by fun_prop), unif01_map_one_sub]; exact map_qf hτ
  · obtain ⟨c, hc⟩ := exists_Icc_of_osc (S := Ioo (0:ℝ) 1) ⟨1/2, by norm_num, by norm_num⟩
      (f := fun v => q₁ v + q₂ (1 - v)) (ℓ := ℓ) (by
        intro v _ v' _
        rcases le_total v' v with h | h
        · have e1 : q₁ v - q₁ v' ≤ b₁ - a₁ := by
            linarith [qf_le (μ := σ) (a := a₁) (b := b₁) v, le_qf (μ := σ) hab₁ v']
          have e2 : q₂ (1 - v) ≤ q₂ (1 - v') := qf_mono (by linarith)
          linarith
        · have e1 : q₂ (1 - v) - q₂ (1 - v') ≤ b₂ - a₂ := by
            linarith [qf_le (μ := τ) (a := a₂) (b := b₂) (1 - v), le_qf (μ := τ) hab₂ (1 - v')]
          have e2 : q₁ v ≤ q₁ v' := qf_mono h
          linarith)
    refine ⟨c, ?_⟩
    have hmS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ Icc c (c + ℓ)} :=
      (measurable_fst.add measurable_snd) measurableSet_Icc
    refine (ae_map_iff hm.aemeasurable hmS).2 ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun v hv => hc v hv

lemma measurable_snoc {k : ℕ} :
    Measurable (fun p : (Fin k → ℝ) × (ℝ × ℝ) => (Fin.snoc p.1 p.2.2 : Fin (k + 1) → ℝ)) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.lastCases with
  | last =>
    have : (fun p : (Fin k → ℝ) × (ℝ × ℝ) => (Fin.snoc p.1 p.2.2 : Fin (k + 1) → ℝ) (Fin.last k))
        = fun p => p.2.2 := by funext p; simp
    rw [this]; fun_prop
  | cast i =>
    have : (fun p : (Fin k → ℝ) × (ℝ × ℝ) => (Fin.snoc p.1 p.2.2 : Fin (k + 1) → ℝ) i.castSucc)
        = fun p => p.1 i := by funext p; simp
    rw [this]; exact (measurable_pi_apply i).comp measurable_fst

lemma conc_a_aux (ℓ : ℝ) : ∀ k : ℕ, ∀ T : Fin (k + 1) → Measure ℝ, (∀ j, IsProbabilityMeasure (T j)) →
    (∀ j, ∃ a, T j (Icc a (a + ℓ))ᶜ = 0) →
    ∃ P : Measure (Fin (k + 1) → ℝ), IsProbabilityMeasure P ∧ (∀ j, P.map (fun y => y j) = T j) ∧
      ∃ c, ∀ᵐ y ∂P, ∑ j, y j ∈ Icc c (c + ℓ) := by
  intro k
  induction k with
  | zero =>
    intro T hT hsupp
    obtain ⟨a, ha⟩ := hsupp 0
    have hm : Measurable (fun x : ℝ => (fun _ : Fin 1 => x)) := measurable_pi_iff.2 fun _ => measurable_id
    refine ⟨(T 0).map (fun x => fun _ => x), inferInstance, fun j => ?_, a, ?_⟩
    · obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
      rw [Measure.map_map (measurable_pi_apply _) hm]; exact Measure.map_id
    · have hsum : Measurable (fun y : Fin 1 → ℝ => ∑ j, y j) :=
        Finset.measurable_sum _ fun i _ => measurable_pi_apply i
      refine (ae_map_iff hm.aemeasurable (hsum measurableSet_Icc)).2 ?_
      have : ∀ᵐ x ∂(T 0), x ∈ Icc a (a + ℓ) := by rw [ae_iff]; exact ha
      filter_upwards [this] with x hx; simpa using hx
  | succ k ih =>
    intro T hT hsupp
    obtain ⟨Pk, hPkp, hPkm, c, hc⟩ := ih (fun j => T (Fin.castSucc j)) (fun j => hT _)
      (fun j => hsupp _)
    obtain ⟨a, ha⟩ := hsupp (Fin.last _)
    have hsum : Measurable (fun y : Fin (k + 1) → ℝ => ∑ j, y j) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    set σ := Pk.map (fun y => ∑ j, y j)
    have hσ : σ (Icc c (c + ℓ))ᶜ = 0 := by
      rw [Measure.map_apply hsum measurableSet_Icc.compl]
      rw [ae_iff] at hc; exact hc
    have hℓ : 0 ≤ ℓ := by
      by_contra hneg
      have : Icc a (a + ℓ) = ∅ := Icc_eq_empty (by linarith)
      rw [this, compl_empty] at ha
      have := hT (Fin.last (k+1))
      simp at ha
    have := hT (Fin.last (k + 1))
    obtain ⟨γ, hγp, hγ1, hγ2, c', hc'⟩ := antitone_coupling (σ := σ) (τ := T (Fin.last _))
      (by linarith) (by linarith) (by linarith) (by linarith) hσ ha
    obtain ⟨Γ, hΓp, hΓ1, hΓ2, hΓs⟩ := exists_glue Pk γ hsum measurable_fst hγ1.symm
    refine ⟨Γ.map (fun p => Fin.snoc p.1 p.2.2), inferInstance, fun j => ?_, c', ?_⟩
    · rw [Measure.map_map (measurable_pi_apply j) measurable_snoc]
      induction j using Fin.lastCases with
      | last =>
        have : ((fun y : Fin (k + 2) → ℝ => y (Fin.last (k + 1))) ∘
            fun p : (Fin (k + 1) → ℝ) × (ℝ × ℝ) => (Fin.snoc p.1 p.2.2 : Fin (k + 2) → ℝ)) =
            Prod.snd ∘ Prod.snd := by funext p; simp
        rw [this, ← Measure.map_map measurable_snd measurable_snd, hΓ2, hγ2]
      | cast i =>
        have : ((fun y : Fin (k + 2) → ℝ => y (Fin.castSucc i)) ∘
            fun p : (Fin (k + 1) → ℝ) × (ℝ × ℝ) => (Fin.snoc p.1 p.2.2 : Fin (k + 2) → ℝ)) =
            (fun y : Fin (k + 1) → ℝ => y i) ∘ Prod.fst := by funext p; simp
        rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_fst, hΓ1, hPkm]
    · have hsum2 : Measurable (fun y : Fin (k + 2) → ℝ => ∑ j, y j) :=
        Finset.measurable_sum _ fun i _ => measurable_pi_apply i
      refine (ae_map_iff measurable_snoc.aemeasurable (hsum2 measurableSet_Icc)).2 ?_
      have h2 : ∀ᵐ p ∂Γ, p.2.1 + p.2.2 ∈ Icc c' (c' + ℓ) := by
        have hmS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ Icc c' (c' + ℓ)} :=
          (measurable_fst.add measurable_snd) measurableSet_Icc
        rw [← hΓ2] at hc'
        exact (ae_map_iff measurable_snd.aemeasurable hmS).1 hc'
      filter_upwards [hΓs, h2] with p hp1 hp2
      show ∑ j, (Fin.snoc p.1 p.2.2 : Fin (k + 2) → ℝ) j ∈ Icc c' (c' + ℓ)
      rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hp1]; exact hp2

section Core
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The common core of the proof of Theorem `as:thm:window`: if `n F = m U + k T`, the variables
`Y_1, …, Y_k ∼ T` are coupled by `PY`, `Z ∼ ν` is independent of them, and the distribution of
`Z - ∑ Y_j` lies in `𝒜_m(U)`, then `ν ∈ 𝒜_n(F)`. -/
theorem core {m k n : ℕ} (hn : n = m + k) (hn0 : 0 < n) (F U T : Measure E)
    [IsProbabilityMeasure U] [IsProbabilityMeasure T]
    (hdec : (n : ℝ≥0∞) • F = (m : ℝ≥0∞) • U + (k : ℝ≥0∞) • T)
    (PY : Measure (Fin k → E)) [IsProbabilityMeasure PY] (hPY : ∀ j, PY.map (fun y => y j) = T)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hwin : (PY.prod ν).map (fun p => p.2 - ∑ j, p.1 j) ∈ AggSetC m U) :
    ν ∈ AggSetC n F := by
  obtain ⟨PV, hPVp, hPVm, hPVs⟩ := hwin
  have hsumV : Measurable (fun x : Fin m → E => ∑ j, x j) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hg : Measurable (fun p : (Fin k → E) × E => p.2 - ∑ j, p.1 j) :=
    measurable_snd.sub (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst)
  obtain ⟨Γ, hΓp, hΓ1, hΓ2, hΓs⟩ := exists_glue PV (PY.prod ν) hsumV hg hPVs
  set e : (Fin m → E) × ((Fin k → E) × E) → (Fin m ⊕ Fin k → E) := fun p => Sum.elim p.1 p.2.1
  have he : Measurable e := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr j => exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  set R := Γ.map e
  have hcard : Fintype.card (Fin m ⊕ Fin k) = n := by simp [hn]
  have : IsProbabilityMeasure R := inferInstance
  refine ⟨Mixes.symmetrize n R, symmetrize_isProb hcard R, fun j => ?_, ?_⟩
  · rw [symmetrize_map_eval hn0 hcard, Fintype.sum_sum_type]
    have h1 : ∀ i : Fin m, R.map (fun z => z (Sum.inl i)) = U := by
      intro i
      rw [Measure.map_map (measurable_pi_apply _) he]
      have : ((fun z : Fin m ⊕ Fin k → E => z (Sum.inl i)) ∘ e) =
          (fun x : Fin m → E => x i) ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_fst, hΓ1, hPVm]
    have h2 : ∀ i : Fin k, R.map (fun z => z (Sum.inr i)) = T := by
      intro i
      rw [Measure.map_map (measurable_pi_apply _) he]
      have : ((fun z : Fin m ⊕ Fin k → E => z (Sum.inr i)) ∘ e) =
          (fun y : Fin k → E => y i) ∘ Prod.fst ∘ Prod.snd := rfl
      rw [this, ← Measure.map_map (measurable_pi_apply i) (measurable_fst.comp measurable_snd),
        ← Measure.map_map measurable_fst measurable_snd, hΓ2, Measure.map_fst_prod, measure_univ,
        one_smul, hPY]
    simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]
    rw [← hdec, smul_smul, ENNReal.inv_mul_cancel (by exact_mod_cast hn0.ne')
      (ENNReal.natCast_ne_top _), one_smul]
  · rw [symmetrize_map_sum hcard]
    have hsumR : Measurable (fun z : Fin m ⊕ Fin k → E => ∑ i, z i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    rw [Measure.map_map hsumR he]
    have hae : (fun z : Fin m ⊕ Fin k → E => ∑ i, z i) ∘ e =ᵐ[Γ] (fun p => p.2.2) := by
      filter_upwards [hΓs] with p hp
      simp only [Function.comp_apply, e, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      rw [hp]; abel
    rw [Measure.map_congr hae]
    have : (fun p : (Fin m → E) × ((Fin k → E) × E) => p.2.2) = Prod.snd ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map measurable_snd measurable_snd, hΓ2, Measure.map_snd_prod,
      measure_univ, one_smul]

end Core

/-! ### Proposition `as:prop:window` (hypothesis, in the form of `Mixes.AsymWindow`) -/

/-- `ν ∈ 𝒜_n(F 0, …, F (n-1))` (verbatim copy of `Mixes.AsymWindow.InAgg`). -/
def InAgg {E : Type*} [MeasurableSpace E] [AddCommMonoid E] {n : ℕ} (F : Fin n → Measure E)
    (ν : Measure E) : Prop :=
  ∃ P : Measure (Fin n → E), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = F j) ∧
    P.map (fun x => ∑ j, x j) = ν

/-- The box `c + ∏ᵢ [-Hᵢ, Hᵢ]` in `Fin d → ℝ` (verbatim copy of `Mixes.AsymWindow.box`). -/
def boxW {d : ℕ} (c H : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Icc (c i - H i) (c i + H i)

/-- **Proposition `as:prop:window`** (`mᵢ ≥ 4`; hypothesis, proved by another agent; verbatim copy
of `Mixes.AsymWindow.PropWindow`). -/
def PropWindow : Prop :=
  ∀ (d : ℕ) (c H : Fin d → ℝ) (mi : Fin d → ℕ) (ν : Measure (Fin d → ℝ)),
    (∀ i, 0 < H i) → (∀ i, 4 ≤ mi i) → IsProbabilityMeasure ν →
    (∀ᵐ x ∂ν, ∀ i, |x i - (∑ k, mi k : ℕ) * c i| ≤ mi i * H i / 2) →
    ∫ x, x ∂ν = ((∑ k, mi k : ℕ) : ℝ) • c →
    InAgg (fun _ : Fin (∑ k, mi k) => unifSet (boxW c H)) ν

/-- **Proposition `as:prop:window`, `d = 1`**, on `ℝ` (verbatim copy of
`Mixes.AsymWindow.PropWindowReal`). -/
def PropWindowReal : Prop :=
  ∀ (m : ℕ) (c H : ℝ) (ν : Measure ℝ), 0 < H → 4 ≤ m → IsProbabilityMeasure ν →
    (∀ᵐ x ∂ν, |x - m * c| ≤ m * H / 2) → ∫ x, x ∂ν = m * c →
    InAgg (fun _ : Fin m => unifI (c - H) (c + H)) ν

/-- The one-dimensional form of Proposition `as:prop:window` with `m ≥ 4`. -/
lemma prop_window_one (hP : PropWindowReal) {m : ℕ} (hm : 4 ≤ m) {c H : ℝ} (hH : 0 < H)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ x, x ∂ν = m * c)
    (hsupp : ν (Icc (m * c - m * H / 2) (m * c + m * H / 2))ᶜ = 0) :
    ν ∈ AggSetC m (unifI (c - H) (c + H)) := by
  refine hP m c H ν hH hm inferInstance ?_ hmean
  have : ∀ᵐ x ∂ν, x ∈ Icc (m * c - m * H / 2) (m * c + m * H / 2) := by rw [ae_iff]; exact hsupp
  filter_upwards [this] with x hx
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-! ### Auxiliary facts for Theorem `as:thm:window` -/

lemma integral_unifI {c H : ℝ} (hH : 0 < H) : ∫ x, x ∂(unifI (c - H) (c + H)) = c := by
  rw [unifI, if_pos (by linarith), integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_id]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
  field_simp
  ring_nf
  field_simp

lemma exists_Icc_of_diam {A : Set ℝ} (hA : Bornology.IsBounded A) (hne : A.Nonempty) {R : ℝ}
    (hd : Metric.diam A ≤ R) : ∃ a, A ⊆ Icc a (a + R) := by
  have hbdd : BddBelow A := hA.bddBelow
  refine ⟨sInf A, fun x hx => ⟨csInf_le hbdd hx, ?_⟩⟩
  have : x - R ≤ sInf A := by
    refine le_csInf hne fun y hy => ?_
    have := (Metric.dist_le_diam_of_mem hA hx hy).trans hd
    rw [Real.dist_eq] at this
    linarith [le_abs_self (x - y)]
  linarith

lemma integral_sum_coords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {k : ℕ} (P : Measure (Fin k → E))
    (T : Measure E) (hPT : ∀ j, P.map (fun y => y j) = T) (hint : Integrable id T) :
    Integrable (fun y : Fin k → E => ∑ j, y j) P ∧ ∫ y, ∑ j, y j ∂P = k • ∫ x, x ∂T := by
  have hint' : ∀ j, Integrable (fun y : Fin k → E => y j) P := by
    intro j
    have := hint
    rw [← hPT j] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply j).aemeasurable).1 this
  refine ⟨integrable_finsetSum _ fun j _ => hint' j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hint' j]
  have : ∀ j, ∫ y, y j ∂P = ∫ x, x ∂T := by
    intro j
    rw [← hPT j, integral_map (measurable_pi_apply j).aemeasurable
      (aestronglyMeasurable_id (μ := P.map (fun y => y j)))]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma completelyMixable_of_dirac_mem {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableSingletonClass E] [MeasurableAdd₂ E] {n : ℕ} {F : Measure E} {s : E}
    (h : Measure.dirac s ∈ AggSetC n F) : Mixes.CompletelyMixable n F := by
  obtain ⟨P, hPp, hPm, hPs⟩ := h
  have hsum : Measurable (fun y : Fin n → E => ∑ j, y j) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  refine ⟨P, hPp, ⟨s, ?_⟩, hPm⟩
  have : ∀ᵐ x ∂(P.map (fun y => ∑ j, y j)), x = s := by rw [hPs, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  exact (ae_map_iff hsum.aemeasurable (measurableSet_singleton s)).1 this

lemma smul_le_smul_measure {α : Type*} [MeasurableSpace α] {μ ν : Measure α} (c : ℝ≥0∞)
    (h : μ ≤ ν) : c • μ ≤ c • ν := by
  intro s
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul_right (h s) c

/-- The decomposition `(11)`: `n F = m U + k T` with a probability measure `T` carried by the
support of `F`. -/
lemma decomposition {E : Type*} [MeasurableSpace E] {F U : Measure E} [IsProbabilityMeasure F]
    [IsProbabilityMeasure U] {q : ℝ} (hFq : ENNReal.ofReal q • U ≤ F) {n m k : ℕ}
    (hmq : (m : ℝ) ≤ q * n) (hnmk : n = m + k) (hk : 0 < k) :
    ∃ T : Measure E, IsProbabilityMeasure T ∧
      (n : ℝ≥0∞) • F = (m : ℝ≥0∞) • U + (k : ℝ≥0∞) • T ∧ T ≤ ((k : ℝ≥0∞)⁻¹ * n) • F := by
  have hle : (m : ℝ≥0∞) • U ≤ (n : ℝ≥0∞) • F := by
    have h1 : (m : ℝ≥0∞) ≤ n * ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc (m : ℝ≥0∞) • U ≤ (n * ENNReal.ofReal q) • U := by
          intro s; simp only [smul_apply, smul_eq_mul]; exact mul_le_mul_left h1 _
      _ = (n : ℝ≥0∞) • (ENNReal.ofReal q • U) := by rw [smul_smul]
      _ ≤ (n : ℝ≥0∞) • F := smul_le_smul_measure _ hFq
  set T' := (n : ℝ≥0∞) • F - (m : ℝ≥0∞) • U
  have : IsFiniteMeasure ((m : ℝ≥0∞) • U) := ⟨by
    simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.natCast_lt_top m⟩
  have hT' : T' + (m : ℝ≥0∞) • U = (n : ℝ≥0∞) • F := Measure.sub_add_cancel_of_le hle
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hT'u : T' Set.univ = k := by
    have := congrArg (fun μ : Measure E => μ Set.univ) hT'
    simp only [Measure.add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one] at this
    rw [hnmk] at this; push_cast at this
    exact (ENNReal.add_left_inj (ENNReal.natCast_ne_top m)).1 (by rw [this, add_comm])
  refine ⟨(k : ℝ≥0∞)⁻¹ • T', ⟨?_⟩, ?_, ?_⟩
  · rw [smul_apply, hT'u, smul_eq_mul, ENNReal.inv_mul_cancel hk0 hkt]
  · rw [smul_smul, ENNReal.mul_inv_cancel hk0 hkt, one_smul, add_comm, hT']
  · rw [← smul_smul]
    exact smul_le_smul_measure _ Measure.sub_le

/-! ### Theorem `as:thm:window` for `d = 1` -/

/-- Theorem `as:thm:window` on the line (`d = 1`, `c_1 = 1`, `m' = m`): if `F` has mean `μ`, is
supported in a set of diameter at most `R`, and `F ≥ q U[c - H, c + H]` with `0 < q ≤ 1`, and if
`m = ⌊q n⌋ ≥ 4` and `ρ = m H/2 - R ≥ 0`, then `𝒜_n(F)` contains every probability measure with
mean `n μ` supported in `[n μ - ρ, n μ + ρ]`. -/
theorem thm_window_one (hP : PropWindowReal) (F : Measure ℝ) [IsProbabilityMeasure F]
    {R q c H : ℝ} (hH : 0 < H) (hq0 : 0 < q) (hq1 : q ≤ 1) {A : Set ℝ}
    (hA : Bornology.IsBounded A) (hdiam : Metric.diam A ≤ R) (hFA : F Aᶜ = 0)
    (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) {n : ℕ} (hn : 1 ≤ n)
    (hm : 4 ≤ ⌊q * n⌋₊) (hρ : 0 ≤ ⌊q * n⌋₊ * H / 2 - R)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνmean : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hνsupp : ν (Icc (n * ∫ x, x ∂F - (⌊q * n⌋₊ * H / 2 - R))
      (n * ∫ x, x ∂F + (⌊q * n⌋₊ * H / 2 - R)))ᶜ = 0) :
    ν ∈ AggSetC n F := by
  set μ := ∫ x, x ∂F
  set m := ⌊q * n⌋₊
  set ρ := (m : ℝ) * H / 2 - R
  set U := unifI (c - H) (c + H)
  have : IsProbabilityMeasure U := Mixes.unifI_isProb _ _
  have hmq : (m : ℝ) ≤ q * n := Nat.floor_le (by positivity)
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := hmq.trans (by nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    exact_mod_cast this
  -- the support interval of `F`
  have hAne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hFA
    exact one_ne_zero hFA
  obtain ⟨a, haA⟩ := exists_Icc_of_diam hA hAne hdiam
  have hFI : F (Icc a (a + R))ᶜ = 0 := measure_mono_null (compl_subset_compl.2 haA) hFA
  have hR : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hAne; have := haA hx; linarith [this.1, this.2]
  have hUmean : ∫ x, x ∂U = c := integral_unifI hH
  rcases Nat.eq_zero_or_pos (n - m) with hk | hk
  · -- `k = 0`: `F = U`
    have hmn' : m = n := by omega
    have hq : q = 1 := by
      have : (n : ℝ) ≤ q * n := by
        calc (n : ℝ) = m := by rw [hmn']
          _ ≤ q * n := hmq
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      nlinarith
    rw [hq, ENNReal.ofReal_one, one_smul] at hFq
    have hFU : F = U := (Measure.eq_of_le_of_isProbabilityMeasure hFq).symm
    have hμc : μ = c := by simp only [μ, hFU, hUmean]
    rw [hFU]
    rw [← hmn'] at hνmean hνsupp ⊢
    refine prop_window_one hP hm hH ν (by rw [hνmean, hμc]) (measure_mono_null ?_ hνsupp)
    refine compl_subset_compl.2 (Icc_subset_Icc ?_ ?_) <;> rw [hμc] <;>
      linarith [show ρ = (m:ℝ) * H / 2 - R from rfl]
  · set k := n - m
    have hnmk : n = m + k := by omega
    obtain ⟨T, hTp, hdec, hTle⟩ := decomposition hFq hmq hnmk hk
    have hTI : T (Icc a (a + R))ᶜ = 0 := by
      have := hTle (Icc a (a + R))ᶜ
      rw [smul_apply, hFI, smul_eq_mul, mul_zero] at this
      exact le_antisymm this bot_le
    have hintF : Integrable id F := integrable_of_Icc hFI
    have hintT : Integrable id T := integrable_of_Icc hTI
    have hintU : Integrable id U := integrable_of_Icc (a := c - H) (b := c + H) (by
      simp only [U]
      rw [unifI, if_pos (by linarith), smul_apply,
        Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self, measure_empty,
        smul_zero])
    -- the mean identity `n μ = m c + k m_T`
    set mT := ∫ x, x ∂T
    have hmeans : (n : ℝ) * μ = m * c + k * mT := by
      have := congrArg (fun ρ : Measure ℝ => ∫ x, x ∂ρ) hdec
      rw [integral_add_measure (f := fun x : ℝ => x) (hintU.smul_measure (ENNReal.natCast_ne_top _))
        (hintT.smul_measure (ENNReal.natCast_ne_top _)), integral_smul_measure,
        integral_smul_measure, integral_smul_measure, hUmean] at this
      simpa using this
    -- the coupling of `Y_1, …, Y_k ∼ T`
    have hab : a ≤ a + R := by linarith
    set PY := gridCoupling T a (a + R) k
    haveI : IsProbabilityMeasure PY := gridCoupling_isProb k
    have hPYm : ∀ j, PY.map (fun y => y j) = T := gridCoupling_map_eval hTI hk
    obtain ⟨c0, hc0⟩ := gridCoupling_sum (μ := T) hab hk
    have hS := abs_sum_sub_mean_le PY (fun _ => T) hPYm (fun _ => hintT) hc0
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
    rw [add_sub_cancel_left] at hS
    -- the window applied to `Z - S`
    refine core hnmk (by omega) F U T hdec PY hPYm ν ?_
    have hg : Measurable (fun p : (Fin k → ℝ) × ℝ => p.2 - ∑ j, p.1 j) :=
      measurable_snd.sub (Finset.measurable_sum (f := fun i (p : (Fin k → ℝ) × ℝ) => p.1 i)
        Finset.univ fun i _ => (measurable_pi_apply i).comp measurable_fst)
    obtain ⟨hSint, hSmean⟩ := integral_sum_coords PY T hPYm hintT
    have hνint : Integrable id ν := integrable_of_Icc hνsupp
    refine prop_window_one hP hm hH _ ?_ ?_
    · rw [show (∫ x, x ∂((PY.prod ν).map _)) = ∫ x, id x ∂((PY.prod ν).map
          (fun p : (Fin k → ℝ) × ℝ => p.2 - ∑ j, p.1 j)) from rfl,
        integral_map hg.aemeasurable aestronglyMeasurable_id]
      simp only [id]
      rw [integral_sub (f := fun p : (Fin k → ℝ) × ℝ => p.2) (g := fun p => ∑ j, p.1 j)
        (hνint.comp_snd PY) (hSint.comp_fst ν), integral_fun_snd (fun x : ℝ => x),
        integral_fun_fst (fun y : Fin k → ℝ => ∑ j, y j)]
      simp only [probReal_univ, one_smul]
      rw [hSmean, hνmean, nsmul_eq_mul]
      change (n : ℝ) * μ - k * mT = m * c
      linarith
    · have hmS : MeasurableSet (Icc ((m : ℝ) * c - m * H / 2) (m * c + m * H / 2)) :=
        measurableSet_Icc
      rw [Measure.map_apply hg hmS.compl]
      have hZ : ∀ᵐ p ∂(PY.prod ν), p.2 ∈ Icc (n * μ - ρ) (n * μ + ρ) :=
        Measure.quasiMeasurePreserving_snd.ae (by rw [ae_iff]; exact hνsupp)
      have hY : ∀ᵐ p ∂(PY.prod ν), |∑ j, p.1 j - k * mT| ≤ R :=
        Measure.quasiMeasurePreserving_fst.ae hS
      have h : ∀ᵐ p ∂(PY.prod ν), p.2 - ∑ j, p.1 j ∈
          Icc ((m : ℝ) * c - m * H / 2) (m * c + m * H / 2) := by
        filter_upwards [hZ, hY] with p hp1 hp2
        rw [abs_le] at hp2
        have hρ' : ρ = (m : ℝ) * H / 2 - R := rfl
        constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
      rw [ae_iff] at h
      exact h

/-! ### Corollary `as:cor:interval` -/

/-- If `F ≥ q U[c - H, c + H]` and `F` is carried by an interval of length `R`, then `2H ≤ R`. -/
lemma two_H_le {F : Measure ℝ} [IsProbabilityMeasure F] {q c H a R : ℝ} (hH : 0 < H)
    (hq0 : 0 < q) (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F)
    (hF : F (Icc a (a + R))ᶜ = 0) : 2 * H ≤ R := by
  have h1 : unifI (c - H) (c + H) (Icc a (a + R))ᶜ = 0 := by
    have := hFq (Icc a (a + R))ᶜ
    rw [hF, smul_apply, smul_eq_mul] at this
    have h0 : ENNReal.ofReal q * unifI (c - H) (c + H) (Icc a (a + R))ᶜ = 0 :=
      le_antisymm this bot_le
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (by simpa using hq0)
    · exact h
  rw [unifI, if_pos (by linarith), smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Icc.compl] at h1
  have h2 : volume ((Icc a (a + R))ᶜ ∩ Icc (c - H) (c + H)) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (by simp)
    · exact h
  have h3 : volume (Icc (c - H) (c + H)) ≤ volume (Icc a (a + R)) := by
    calc volume (Icc (c - H) (c + H))
        ≤ volume (Icc a (a + R) ∪ ((Icc a (a + R))ᶜ ∩ Icc (c - H) (c + H))) := by
          refine measure_mono fun x hx => ?_
          by_cases h : x ∈ Icc a (a + R)
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
      _ ≤ volume (Icc a (a + R)) + 0 := by rw [← h2]; exact measure_union_le _ _
      _ = volume (Icc a (a + R)) := add_zero _
  rw [Real.volume_Icc, Real.volume_Icc] at h3
  have := (ENNReal.ofReal_le_ofReal_iff' ).1 h3
  rcases this with h | h
  · linarith
  · linarith

/-- Corollary `as:cor:interval`, main statement: `F` with mean `μ` on an interval of length `R`,
`F ≥ q U[c - H, c + H]`, `⌊q n⌋ ≥ 2R/H`: `F` is `n`-completely mixable and `𝒜_n(F)` contains
every distribution with mean `n μ` supported in `[n μ - ρ, n μ + ρ]`, `ρ = ⌊q n⌋ H/2 - R`. -/
theorem cor_interval (hP : PropWindowReal) (F : Measure ℝ) [IsProbabilityMeasure F]
    {R q c H a : ℝ} (hH : 0 < H) (hq0 : 0 < q) (hq1 : q ≤ 1) (hF : F (Icc a (a + R))ᶜ = 0)
    (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) {n : ℕ} (hn : 2 * R / H ≤ ⌊q * n⌋₊) :
    Mixes.CompletelyMixable n F ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ x, x ∂ν = n * ∫ x, x ∂F →
      ν (Icc (n * ∫ x, x ∂F - (⌊q * n⌋₊ * H / 2 - R))
        (n * ∫ x, x ∂F + (⌊q * n⌋₊ * H / 2 - R)))ᶜ = 0 → ν ∈ AggSetC n F := by
  have h2H := two_H_le hH hq0 hFq hF
  have h4 : (4 : ℝ) ≤ ⌊q * n⌋₊ := by
    refine le_trans ?_ hn
    rw [le_div_iff₀ hH]; linarith
  have hm : 4 ≤ ⌊q * n⌋₊ := by exact_mod_cast h4
  have hρ : 0 ≤ (⌊q * n⌋₊ : ℝ) * H / 2 - R := by
    rw [div_le_iff₀ hH] at hn; linarith
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    rw [this] at hm; simp at hm
  have hA : Bornology.IsBounded (Icc a (a + R)) := Metric.isBounded_Icc _ _
  have hdiam : Metric.diam (Icc a (a + R)) ≤ R := by
    rw [Real.diam_Icc (by linarith)]; linarith
  have hwin := fun ν (hν : IsProbabilityMeasure ν) hmean hsupp =>
    thm_window_one hP F hH hq0 hq1 hA hdiam hF hFq hn1 hm hρ ν hmean hsupp
  refine ⟨?_, hwin⟩
  refine completelyMixable_of_dirac_mem (s := n * ∫ x, x ∂F) (hwin _ inferInstance ?_ ?_)
  · simp
  · rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    simp only [Set.indicator, mem_compl_iff, mem_Icc, not_and, not_le]
    split_ifs with h
    · exfalso; exact absurd (h (by linarith)) (by simp; linarith)
    · rfl

/-- Corollary `as:cor:interval`: `F` is `n`-completely mixable for every `n ≥ ⌈2R/H⌉/q`. -/
theorem cor_interval_n (hP : PropWindowReal) (F : Measure ℝ) [IsProbabilityMeasure F]
    {R q c H a : ℝ} (hH : 0 < H) (hq0 : 0 < q) (hq1 : q ≤ 1) (hF : F (Icc a (a + R))ᶜ = 0)
    (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) {n : ℕ}
    (hn : (⌈2 * R / H⌉₊ : ℝ) / q ≤ n) : Mixes.CompletelyMixable n F := by
  refine (cor_interval hP F hH hq0 hq1 hF hFq ?_).1
  have h1 : (⌈2 * R / H⌉₊ : ℝ) ≤ q * n := by rw [div_le_iff₀ hq0] at hn; linarith
  have h2 : ⌈2 * R / H⌉₊ ≤ ⌊q * n⌋₊ := Nat.le_floor h1
  exact (Nat.le_ceil _).trans (by exact_mod_cast h2)

/-- Corollary `as:cor:interval`, last statement: a distribution carried by `[a, b]` whose density
is at least `δ` on the whole of `[a, b]` (here: `F ≥ δ · Lebesgue` on `[a, b]`) is `n`-completely
mixable for every `n ≥ 4/(δ (b - a))`. -/
theorem cor_interval_density (hP : PropWindowReal) (F : Measure ℝ) [IsProbabilityMeasure F]
    {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) (hF : F (Icc a b)ᶜ = 0)
    (hFδ : ENNReal.ofReal δ • volume.restrict (Icc a b) ≤ F) {n : ℕ}
    (hn : 4 / (δ * (b - a)) ≤ n) : Mixes.CompletelyMixable n F := by
  set q := δ * (b - a)
  have hq0 : 0 < q := mul_pos hδ (by linarith)
  have hU : ENNReal.ofReal q • unifI ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) =
      ENNReal.ofReal δ • volume.restrict (Icc a b) := by
    have e1 : (a + b) / 2 - (b - a) / 2 = a := by ring
    have e2 : (a + b) / 2 + (b - a) / 2 = b := by ring
    rw [e1, e2, unifI, if_pos hab, smul_smul, ENNReal.ofReal_mul hδ.le, mul_assoc,
      ENNReal.mul_inv_cancel (by simpa using hab) ENNReal.ofReal_ne_top, mul_one]
  have hq1 : q ≤ 1 := by
    have := hFδ univ
    rw [smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
      measure_univ, smul_eq_mul, ← ENNReal.ofReal_mul hδ.le] at this
    exact (ENNReal.ofReal_le_one).1 this
  have hF' : F (Icc a (a + (b - a)))ᶜ = 0 := by rwa [add_sub_cancel]
  refine cor_interval_n hP F (R := b - a) (c := (a + b) / 2) (H := (b - a) / 2) (by linarith)
    hq0 hq1 hF' (by rw [hU]; exact hFδ) ?_
  have : 2 * (b - a) / ((b - a) / 2) = 4 := by field_simp; ring
  rw [this]; simpa using hn

/-! ## Theorem `as:thm:window` in `ℝ^d` (in the form of `Mixes.AsymGeneral`) -/

/-- `ℝ^d` (as in `Mixes.AsymGeneral`). -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The box `c + ∏ᵢ [-Hᵢ, Hᵢ]` in `ℝ^d` (verbatim copy of `Mixes.AsymGeneral.box`). -/
def boxE {d : ℕ} (c : Rd d) (H : Fin d → ℝ) : Set (Rd d) := {x | ∀ i, |x i - c i| ≤ H i}

/-- `c₁ = 1`, `c_d = 2d` for `d ≥ 2` (copy of `Mixes.AsymGeneral.cdConst`). -/
def cdConst (d : ℕ) : ℝ := if d = 1 then 1 else 2 * d

/-- `F` is supported in a set of diameter at most `R` (copy of `Mixes.AsymGeneral.SuppDiam`). -/
def SuppDiam {d : ℕ} (F : Measure (Rd d)) (R : ℝ) : Prop :=
  ∃ S : Set (Rd d), F Sᶜ = 0 ∧ ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R

/-- **Theorem `as:thm:window`** (verbatim copy of the statement `Mixes.AsymGeneral.H_thm_window`,
with `AggSet n F` written `AggSetC n F`). -/
def ThmWindow (d : ℕ) : Prop :=
  ∀ (F : Measure (Rd d)) [IsProbabilityMeasure F] (R : ℝ) (c : Rd d) (H : Fin d → ℝ) (q : ℝ)
    (n : ℕ), SuppDiam F R → (∀ i, 0 < H i) → 0 < q → q ≤ 1 →
    ENNReal.ofReal q • unifSet (boxE c H) ≤ F →
    4 ≤ ⌊q * n⌋₊ / d →
    (∀ i, 0 ≤ ((⌊q * n⌋₊ / d : ℕ) : ℝ) * H i / 2 - cdConst d * R) →
    ∀ ν : Measure (Rd d), IsProbabilityMeasure ν → ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
      ν (boxE ((n : ℝ) • ∫ x, x ∂F)
        (fun i => ((⌊q * n⌋₊ / d : ℕ) : ℝ) * H i / 2 - cdConst d * R))ᶜ = 0 →
      ν ∈ AggSetC n F

section Rd
variable {d : ℕ}

lemma integrable_of_bdd {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] {μ : Measure E} [IsProbabilityMeasure μ]
    {S : Set E} (hS : Bornology.IsBounded S) (hμ : μ Sᶜ = 0) : Integrable id μ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hS
  refine Integrable.mono' (integrable_const C) aestronglyMeasurable_id ?_
  have : ∀ᵐ x ∂μ, x ∈ S := by rw [ae_iff]; exact hμ
  filter_upwards [this] with x hx using hC x hx

lemma boxE_eq (c : Rd d) (H : Fin d → ℝ) :
    boxE c H = WithLp.ofLp ⁻¹' boxW (WithLp.ofLp c) H := by
  ext x
  simp only [boxE, boxW, mem_setOf_eq, mem_preimage, mem_univ_pi, mem_Icc, abs_le]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> simp at * <;> linarith

lemma measurable_ofLp : Measurable (WithLp.ofLp : Rd d → (Fin d → ℝ)) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable

lemma measurable_toLp : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable

lemma measurableSet_boxW (c H : Fin d → ℝ) : MeasurableSet (boxW c H) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma measurableSet_boxE (c : Rd d) (H : Fin d → ℝ) : MeasurableSet (boxE c H) := by
  rw [boxE_eq]; exact measurable_ofLp (measurableSet_boxW _ _)

lemma boxE_bdd (c : Rd d) (H : Fin d → ℝ) : Bornology.IsBounded (boxE c H) := by
  refine isBounded_iff_forall_norm_le.2 ⟨‖c‖ + √(∑ i, H i ^ 2), fun x hx => ?_⟩
  have h1 : ‖x - c‖ ≤ √(∑ i, H i ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have := hx i
    simp only [PiLp.sub_apply]
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ _ := by linarith

lemma volume_boxW {c H : Fin d → ℝ} : volume (boxW c H) = ∏ i, ENNReal.ofReal (2 * H i) := by
  rw [boxW, volume_pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.volume_Icc]; ring_nf

lemma volume_boxE (c : Rd d) (H : Fin d → ℝ) :
    volume (boxE c H) = ∏ i, ENNReal.ofReal (2 * H i) := by
  rw [boxE_eq, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (measurableSet_boxW _ _).nullMeasurableSet, volume_boxW]

lemma unifSet_boxE_isProb (c : Rd d) {H : Fin d → ℝ} (hH : ∀ i, 0 < H i) :
    IsProbabilityMeasure (unifSet (boxE c H)) := by
  have h0 : volume (boxE c H) ≠ 0 := by
    rw [volume_boxE]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using hH i
  have ht : volume (boxE c H) ≠ ⊤ := by
    rw [volume_boxE]; exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 ht]

lemma unifSet_boxE_compl (c : Rd d) (H : Fin d → ℝ) : unifSet (boxE c H) (boxE c H)ᶜ = 0 := by
  rw [unifSet, smul_apply, Measure.restrict_apply (measurableSet_boxE _ _).compl, compl_inter_self,
    measure_empty, smul_zero]

lemma map_unifSet_boxW (c : Rd d) (H : Fin d → ℝ) :
    (unifSet (boxW (WithLp.ofLp c) H)).map (WithLp.toLp 2) = unifSet (boxE c H) := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) ⁻¹' boxE c H = boxW (WithLp.ofLp c) H := by
    rw [boxE_eq]; rfl
  rw [unifSet, unifSet, Measure.map_smul _ measurable_toLp.aemeasurable, ← hpre,
    hmp.measure_preimage (measurableSet_boxE _ _).nullMeasurableSet]
  congr 1
  exact (hmp.restrict_preimage (measurableSet_boxE c H)).map_eq

/-- The mean of `U(Q)` is the centre `c` (by the reflection `x ↦ 2c - x`). -/
lemma integral_unifSet_boxE (c : Rd d) {H : Fin d → ℝ} (hH : ∀ i, 0 < H i) :
    ∫ x, x ∂(unifSet (boxE c H)) = c := by
  haveI := unifSet_boxE_isProb c hH
  set U := unifSet (boxE c H)
  have hint : Integrable id U := integrable_of_bdd (boxE_bdd c H) (unifSet_boxE_compl c H)
  have href : MeasurePreserving (fun x : Rd d => (2 : ℝ) • c - x) volume volume :=
    (Measure.measurePreserving_sub_left volume _)
  have hpre : (fun x : Rd d => (2 : ℝ) • c - x) ⁻¹' boxE c H = boxE c H := by
    ext x; simp only [boxE, mem_preimage, mem_setOf_eq, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
    refine forall_congr' fun i => ?_
    rw [show 2 * c i - x i - c i = -(x i - c i) by ring, abs_neg]
  have hmap : U.map (fun x : Rd d => (2 : ℝ) • c - x) = U := by
    simp only [U, unifSet]
    rw [Measure.map_smul _ href.measurable.aemeasurable]
    congr 1
    have := href.restrict_preimage (measurableSet_boxE c H)
    rw [hpre] at this
    exact this.map_eq
  have h2 : ∫ x, x ∂U = ∫ x, ((2 : ℝ) • c - x) ∂U := by
    conv_lhs => rw [← hmap]
    rw [show (∫ x, x ∂(U.map _)) = ∫ x, id x ∂(U.map (fun x : Rd d => (2 : ℝ) • c - x)) from rfl,
      integral_map href.measurable.aemeasurable aestronglyMeasurable_id]
    rfl
  rw [integral_sub (f := fun _ => (2:ℝ) • c) (g := fun x => x) (integrable_const _) hint, integral_const, probReal_univ, one_smul] at h2
  have : (2 : ℝ) • ∫ x, x ∂U = (2 : ℝ) • c := by
    rw [two_smul ℝ (∫ x, x ∂U)]; nth_rewrite 2 [h2]; abel
  exact smul_right_injective _ two_ne_zero this

end Rd

section RdThm
variable {d : ℕ}

/-- Proposition `as:prop:window` transported from `Fin d → ℝ` to `ℝ^d = EuclideanSpace ℝ (Fin d)`. -/
lemma prop_window_E (hP : PropWindow) (c : Rd d) (H : Fin d → ℝ) (mi : Fin d → ℕ)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] (hH : ∀ i, 0 < H i) (hmi : ∀ i, 4 ≤ mi i)
    (hmean : ∫ x, x ∂ν = ((∑ k, mi k : ℕ) : ℝ) • c)
    (hsupp : ∀ᵐ x ∂ν, ∀ i, |x i - (∑ k, mi k : ℕ) * c i| ≤ mi i * H i / 2) :
    ν ∈ AggSetC (∑ k, mi k) (unifSet (boxE c H)) := by
  set L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  set ν' := ν.map (WithLp.ofLp : Rd d → (Fin d → ℝ))
  have hmean' : ∫ x, x ∂ν' = ((∑ k, mi k : ℕ) : ℝ) • WithLp.ofLp c := by
    rw [show (∫ x, x ∂ν') = ∫ x, id x ∂ν' from rfl,
      integral_map measurable_ofLp.aemeasurable aestronglyMeasurable_id]
    have := L.integral_comp_comm (fun x : Rd d => x) (μ := ν)
    simp only [L, PiLp.coe_continuousLinearEquiv] at this
    simp only [id]
    rw [this, hmean, WithLp.ofLp_smul]
  have hsupp' : ∀ᵐ x ∂ν', ∀ i, |x i - (∑ k, mi k : ℕ) * (WithLp.ofLp c) i| ≤ mi i * H i / 2 := by
    refine (ae_map_iff measurable_ofLp.aemeasurable ?_).2 hsupp
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun i => ?_
    exact measurableSet_le ((measurable_pi_apply i).sub_const _).abs measurable_const
  obtain ⟨P, hPp, hPm, hPs⟩ := hP d (WithLp.ofLp c) H mi ν' hH hmi inferInstance hsupp' hmean'
  have hmap : Measurable (fun x : Fin (∑ k, mi k) → (Fin d → ℝ) => fun j => WithLp.toLp 2 (x j)) :=
    measurable_pi_iff.2 fun j => measurable_toLp.comp (measurable_pi_apply j)
  refine ⟨P.map (fun x j => WithLp.toLp 2 (x j)), inferInstance, fun j => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply j) hmap]
    have : ((fun y : Fin (∑ k, mi k) → Rd d => y j) ∘
        fun x : Fin (∑ k, mi k) → (Fin d → ℝ) => fun j => WithLp.toLp 2 (x j))
        = WithLp.toLp 2 ∘ (fun x => x j) := rfl
    rw [this, ← Measure.map_map measurable_toLp (measurable_pi_apply j), hPm j]
    exact map_unifSet_boxW c H
  · have hsum : Measurable (fun y : Fin (∑ k, mi k) → Rd d => ∑ j, y j) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hsum' : Measurable (fun y : Fin (∑ k, mi k) → (Fin d → ℝ) => ∑ j, y j) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    rw [Measure.map_map hsum hmap]
    have : ((fun y : Fin (∑ k, mi k) → Rd d => ∑ j, y j) ∘
        fun x : Fin (∑ k, mi k) → (Fin d → ℝ) => fun j => WithLp.toLp 2 (x j)) =
        WithLp.toLp 2 ∘ (fun y => ∑ j, y j) := by
      funext x; simp only [Function.comp_apply, WithLp.toLp_sum]
    rw [this, ← Measure.map_map measurable_toLp hsum', hPs, Measure.map_map measurable_toLp
      measurable_ofLp]
    have : (WithLp.toLp 2 ∘ WithLp.ofLp : Rd d → Rd d) = id := by funext x; rfl
    rw [this, Measure.map_id]

lemma measurableSet_boxLike (C B : Fin d → ℝ) :
    MeasurableSet {x : Rd d | ∀ i, |x i - C i| ≤ B i} := by
  rw [show {x : Rd d | ∀ i, |x i - C i| ≤ B i} = ⋂ i, {x : Rd d | |x i - C i| ≤ B i} by
    ext; simp]
  exact MeasurableSet.iInter fun i => measurableSet_le
    (((measurable_pi_apply i).comp measurable_ofLp).sub_const _).abs measurable_const

/-- The coupling statement needed in the proof of Theorem `as:thm:window`: Lemma `as:lem:conc`
(b) for `d = 1`, (c) for `d ≥ 2`, in the coordinate form used there. -/
def CouplingBound (d : ℕ) : Prop :=
  ∀ (T : Measure (Rd d)) [IsProbabilityMeasure T] (R : ℝ) (k : ℕ), 0 < k → SuppDiam T R →
    ∃ P : Measure (Fin k → Rd d), IsProbabilityMeasure P ∧ (∀ j, P.map (fun y => y j) = T) ∧
      ∀ᵐ y ∂P, ∀ i, |(∑ j, y j - (k : ℝ) • ∫ x, x ∂T) i| ≤ cdConst d * R

lemma suppDiam_bdd {F : Measure (Rd d)} {R : ℝ} {S : Set (Rd d)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R) : Bornology.IsBounded S := by
  rcases S.eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · rw [h]; exact Bornology.isBounded_empty
  · exact (Metric.isBounded_closedBall (x := x0) (r := R)).subset fun y hy =>
      Metric.mem_closedBall.2 (by rw [dist_comm]; exact hS x0 hx0 y hy)

lemma cdConst_nonneg (d : ℕ) : 0 ≤ cdConst d := by
  unfold cdConst; split_ifs <;> positivity

/-- **Theorem `as:thm:window`** in `ℝ^d`, from Proposition `as:prop:window` and the coupling
lemma. -/
theorem thmWindow_of (hP : PropWindow) (hC : CouplingBound d) : ThmWindow d := by
  intro F _ R c H q n hSupp hH hq0 hq1 hFq hm4 hρ ν _ hνmean hνsupp
  set μ := ∫ x, x ∂F
  set m := ⌊q * n⌋₊
  set m' := m / d
  set U := unifSet (boxE c H)
  haveI hU : IsProbabilityMeasure U := unifSet_boxE_isProb c hH
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [m', h] at hm4
    · exact h
  have hmq : (m : ℝ) ≤ q * n := Nat.floor_le (by positivity)
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := hmq.trans (by nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    exact_mod_cast this
  have hdm : d * m' ≤ m := Nat.mul_div_le m d
  -- block sizes
  set i0 : Fin d := ⟨0, hd⟩
  set mi : Fin d → ℕ := fun i => m' + if i = i0 then m - d * m' else 0
  have hmi : ∀ i, m' ≤ mi i := fun i => Nat.le_add_right _ _
  have hmi4 : ∀ i, 4 ≤ mi i := fun i => hm4.trans (hmi i)
  have hsum : ∑ i, mi i = m := by
    simp only [mi, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [m'] at *
    omega
  obtain ⟨S, hFS, hSd⟩ := hSupp
  have hSb := suppDiam_bdd (F := F) hSd
  have hintF : Integrable id F := integrable_of_bdd hSb hFS
  have hUmean : ∫ x, x ∂U = c := integral_unifSet_boxE c hH
  have hintU : Integrable id U := integrable_of_bdd (boxE_bdd c H) (unifSet_boxE_compl c H)
  have hcR : 0 ≤ cdConst d * R := by
    have hSne : S.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, compl_empty, measure_univ] at hFS
      exact one_ne_zero hFS
    obtain ⟨x0, hx0⟩ := hSne
    have := hSd x0 hx0 x0 hx0
    rw [dist_self] at this
    exact mul_nonneg (cdConst_nonneg d) this
  have hνae : ∀ᵐ z ∂ν, ∀ i, |z i - ((n : ℝ) • μ) i| ≤ (m' : ℝ) * H i / 2 - cdConst d * R := by
    rw [ae_iff]; exact hνsupp
  have hwin : ∀ (lam : Measure (Rd d)), IsProbabilityMeasure lam → ∫ x, x ∂lam = (m : ℝ) • c →
      (∀ᵐ x ∂lam, ∀ i, |x i - m * c i| ≤ m' * H i / 2) → lam ∈ AggSetC m U := by
    intro lam _ hmean hae
    have h := prop_window_E hP c H mi lam hH hmi4 (by rw [hsum]; exact hmean) (by
      rw [hsum]
      filter_upwards [hae] with x hx i
      refine (hx i).trans ?_
      have : (m' : ℝ) ≤ mi i := by exact_mod_cast hmi i
      have := hH i
      nlinarith)
    rwa [hsum] at h
  rcases Nat.eq_zero_or_pos (n - m) with hk | hk
  · -- `k = 0`: `F = U`
    have hmn' : m = n := by omega
    have hq : q = 1 := by
      have : (n : ℝ) ≤ q * n := by
        calc (n : ℝ) = m := by rw [hmn']
          _ ≤ q * n := hmq
      have hn' : (0:ℝ) < n := by
        have h1 : m' ≤ m := Nat.div_le_self m d
        exact_mod_cast (show 0 < n by omega)
      nlinarith
    rw [hq, ENNReal.ofReal_one, one_smul] at hFq
    have hFU : F = U := (Measure.eq_of_le_of_isProbabilityMeasure hFq).symm
    have hμc : μ = c := by simp only [μ, hFU, hUmean]
    rw [hFU, ← hmn']
    refine hwin ν inferInstance (by rw [hνmean, hμc, hmn']) ?_
    filter_upwards [hνae] with z hz i
    have := hz i
    rw [hμc, ← hmn', PiLp.smul_apply, smul_eq_mul] at this
    linarith
  · set k := n - m
    have hnmk : n = m + k := by omega
    obtain ⟨T, hTp, hdec, hTle⟩ := decomposition hFq hmq hnmk hk
    have hTS : T Sᶜ = 0 := by
      have := hTle Sᶜ
      rw [smul_apply, hFS, smul_eq_mul, mul_zero] at this
      exact le_antisymm this bot_le
    have hintT : Integrable id T := integrable_of_bdd hSb hTS
    set mT := ∫ x, x ∂T
    have hmeans : (n : ℝ) • μ = (m : ℝ) • c + (k : ℝ) • mT := by
      have := congrArg (fun ρ : Measure (Rd d) => ∫ x, x ∂ρ) hdec
      rw [integral_add_measure (f := fun x : Rd d => x)
        (hintU.smul_measure (ENNReal.natCast_ne_top _))
        (hintT.smul_measure (ENNReal.natCast_ne_top _)), integral_smul_measure,
        integral_smul_measure, integral_smul_measure, hUmean] at this
      simpa using this
    obtain ⟨PY, hPYp, hPYm, hPYae⟩ := hC T R k hk ⟨S, hTS, hSd⟩
    refine core hnmk (by omega) F U T hdec PY hPYm ν ?_
    have hg : Measurable (fun p : (Fin k → Rd d) × Rd d => p.2 - ∑ j, p.1 j) :=
      measurable_snd.sub (Finset.measurable_sum (f := fun i (p : (Fin k → Rd d) × Rd d) => p.1 i)
        Finset.univ fun i _ => (measurable_pi_apply i).comp measurable_fst)
    obtain ⟨hSint, hSmean⟩ := integral_sum_coords PY T hPYm hintT
    have hνint : Integrable id ν := integrable_of_bdd (boxE_bdd _ _) hνsupp
    refine hwin _ inferInstance ?_ ?_
    · rw [show (∫ x, x ∂((PY.prod ν).map _)) = ∫ x, id x ∂((PY.prod ν).map
          (fun p : (Fin k → Rd d) × Rd d => p.2 - ∑ j, p.1 j)) from rfl,
        integral_map hg.aemeasurable aestronglyMeasurable_id]
      simp only [id]
      rw [integral_sub (f := fun p : (Fin k → Rd d) × Rd d => p.2) (g := fun p => ∑ j, p.1 j)
        (hνint.comp_snd PY) (hSint.comp_fst ν), integral_fun_snd (fun x : Rd d => x),
        integral_fun_fst (fun y : Fin k → Rd d => ∑ j, y j)]
      simp only [probReal_univ, one_smul]
      rw [hSmean, hνmean, hmeans, ← Nat.cast_smul_eq_nsmul ℝ]
      abel
    · refine (ae_map_iff hg.aemeasurable ?_).2 ?_
      · exact measurableSet_boxLike (fun i => m * c i) (fun i => m' * H i / 2)
      have hZ := Measure.quasiMeasurePreserving_snd (μ := PY) (ν := ν) |>.ae hνae
      have hY := Measure.quasiMeasurePreserving_fst (μ := PY) (ν := ν) |>.ae hPYae
      filter_upwards [hZ, hY] with p hp1 hp2 i
      have h1 := abs_le.1 (hp1 i)
      have h2 := abs_le.1 (hp2 i)
      have h3 := congrArg (fun v : Rd d => v i) hmeans
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h3
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1 h2 ⊢
      rw [abs_le]
      have hsumi : (∑ j, p.1 j) i = ∑ j, p.1 j i := by
        simp [WithLp.ofLp_sum]
      constructor <;> nlinarith

end RdThm

/-- The theorem of Grinberg and Sevastyanov (1980) on the lemma of Steinitz, for the Euclidean
norm on `ℝ^d` (a classical theorem that Mathlib lacks; explicit hypothesis): vectors of norm at
most `ℓ` with sum `0` can be ordered so that all partial sums have norm at most `d ℓ`. -/
def H_steinitz : Prop :=
  ∀ (d N : ℕ) (v : Fin N → EuclideanSpace ℝ (Fin d)) (ℓ : ℝ), (∀ i, ‖v i‖ ≤ ℓ) →
    ∑ i, v i = 0 → ∃ π : Equiv.Perm (Fin N), ∀ J : ℕ,
      ‖∑ i : Fin N, if (i : ℕ) < J then v (π i) else 0‖ ≤ d * ℓ

section Disc
variable {d M k : ℕ}

/-- A coupling of `k` labels with label distribution `p`, as a weight function. -/
def IsLabCoupling (p : Fin M → ℝ) (w : (Fin k → Fin M) → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ j c, ∑ t, (if t j = c then w t else 0) = p c

/-- Block sums of the Steinitz ordering: `∑_{j<k} v(π(j + k b)) = S_{k(b+1)} - S_{k b}`. -/
lemma block_sum {L : ℕ} {E : Type*} [AddCommGroup E] (f : Fin (L * k) → E) (b : Fin L) :
    ∑ j : Fin k, f (finProdFinEquiv (b, j)) =
      (∑ i : Fin (L * k), if (i : ℕ) < k * b + k then f i else 0) -
        ∑ i : Fin (L * k), if (i : ℕ) < k * b then f i else 0 := by
  rw [← Finset.sum_sub_distrib]
  rw [← Fintype.sum_equiv finProdFinEquiv (fun p => (if ((finProdFinEquiv p : Fin (L * k)) : ℕ) <
      k * b + k then f (finProdFinEquiv p) else 0) - if ((finProdFinEquiv p : Fin (L * k)) : ℕ) <
      k * b then f (finProdFinEquiv p) else 0) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [finProdFinEquiv_apply_val]
    have hj := j.isLt
    rw [if_pos (by nlinarith), if_neg (by nlinarith), sub_zero]
  · intro b' _ hb'
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [finProdFinEquiv_apply_val]
    have hj := j.isLt
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hb') with h | h
    · have : (b' : ℕ) + 1 ≤ b := h
      rw [if_pos (by nlinarith), if_pos (by nlinarith), sub_self]
    · have : (b : ℕ) + 1 ≤ b' := h
      rw [if_neg (by nlinarith), if_neg (by nlinarith), sub_self]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The coupling of Lemma `as:lem:conc` (c) for the uniform distribution on `kL` labelled points:
Steinitz ordering, a uniformly random block of `k` consecutive points, in uniformly random order. -/
lemma disc_coupling (hS : H_steinitz) {L : ℕ} (hk : 0 < k) (hL : 0 < L) (lab : Fin (L * k) → Fin M)
    (x : Fin M → EuclideanSpace ℝ (Fin d)) {ℓ : ℝ}
    (hx : ∀ i, ‖x (lab i) - ((L * k : ℕ) : ℝ)⁻¹ • ∑ i', x (lab i')‖ ≤ ℓ) :
    ∃ w : (Fin k → Fin M) → ℝ,
      IsLabCoupling (fun c => ((Finset.univ.filter (fun i => lab i = c)).card : ℝ) / (L * k)) w ∧
      ∀ t, 0 < w t → ‖∑ j, x (t j) - (k : ℝ) • (((L * k : ℕ) : ℝ)⁻¹ • ∑ i', x (lab i'))‖ ≤
        2 * d * ℓ := by
  have hN0 : (0 : ℝ) < ((L * k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hL hk
  set mbar := ((L * k : ℕ) : ℝ)⁻¹ • ∑ i', x (lab i') with hmbar
  have hN := hN0
  set v : Fin (L * k) → EuclideanSpace ℝ (Fin d) := fun i => x (lab i) - mbar
  have hv0 : ∑ i, v i = 0 := by
    simp only [v, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      mbar, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hN.ne', one_smul, sub_self]
  obtain ⟨π, hπ⟩ := hS d (L * k) v ℓ hx hv0
  set y : Fin (L * k) → Fin M := fun i => lab (π i)
  set f : Fin L → (Fin k ≃ Fin k) → Fin k → Fin M := fun b σ j => y (finProdFinEquiv (b, σ j))
  set K := (Fintype.card (Fin k ≃ Fin k) : ℝ)
  have hK : K = (k.factorial : ℝ) := by
    simp only [K, Fintype.card_equiv (Equiv.refl (Fin k)), Fintype.card_fin]
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast k.factorial_pos
  set w : (Fin k → Fin M) → ℝ := fun t =>
    ((L : ℝ) * K)⁻¹ * ∑ b, ∑ σ, if t = f b σ then (1 : ℝ) else 0
  refine ⟨w, ⟨fun t => ?_, fun j c => ?_⟩, fun t ht => ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun σ _ =>
      by split_ifs <;> norm_num)
  · -- marginals
    have e1 : ∀ t, (if t j = c then w t else 0) = ((L : ℝ) * K)⁻¹ *
        ∑ b, ∑ σ, if t = f b σ then (if f b σ j = c then (1 : ℝ) else 0) else 0 := by
      intro t
      simp only [w]
      split_ifs with h
      · congr 1; refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun σ _ => ?_
        split_ifs with h1 h2 <;> first | rfl | (subst h1; exact absurd h h2)
      · rw [eq_comm, mul_eq_zero]; right
        refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun σ _ => ?_
        split_ifs with h1 h2
        · subst h1; exact absurd h2 h
        · rfl
        · rfl
    simp only [e1, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have e3 : ∀ b, ∑ t : Fin k → Fin M, ∑ σ : Fin k ≃ Fin k,
        (if t = f b σ then (if f b σ j = c then (1 : ℝ) else 0) else 0) =
        ∑ σ : Fin k ≃ Fin k, (if f b σ j = c then (1 : ℝ) else 0) := by
      intro b
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => by simp
    simp only [e3]
    -- counting permutations
    have hcount : ∀ b, ∑ σ : Fin k ≃ Fin k, (if f b σ j = c then (1 : ℝ) else 0) =
        K / k * ∑ i : Fin k, (if y (finProdFinEquiv (b, i)) = c then (1 : ℝ) else 0) := by
      intro b
      have := Mixes.nsmul_sum_equiv_apply
        (fun i : Fin k => if y (finProdFinEquiv (b, i)) = c then (1 : ℝ) else 0) j
      simp only [nsmul_eq_mul] at this
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
      simpa [f, K, mul_comm] using this
    simp only [hcount, ← Finset.mul_sum]
    rw [← Fintype.sum_prod_type' (fun b i => if y (finProdFinEquiv (b, i)) = c then (1 : ℝ) else 0)]
    rw [Fintype.sum_equiv finProdFinEquiv (fun p => if y (finProdFinEquiv p) = c then (1 : ℝ) else 0)
      (fun i => if y i = c then (1 : ℝ) else 0) (fun _ => rfl)]
    simp only [y]
    rw [Equiv.sum_comp π (fun i => if lab i = c then (1 : ℝ) else 0), Finset.sum_boole]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
  · -- support
    obtain ⟨b, σ, rfl⟩ : ∃ b σ, t = f b σ := by
      by_contra hne
      push_neg at hne
      have : w t = 0 := by
        simp only [w]
        rw [mul_eq_zero]; right
        exact Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun σ _ => if_neg (hne b σ)
      linarith
    have e2 : ∑ j, x (f b σ j) - (k : ℝ) • mbar = ∑ i : Fin k, v (π (finProdFinEquiv (b, i))) := by
      rw [← Equiv.sum_comp σ (fun i => v (π (finProdFinEquiv (b, i))))]
      simp only [v, f, y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [e2, block_sum (fun i => v (π i)) b]
    have h1 := hπ (k * b + k)
    have h2 := hπ (k * b)
    calc _ ≤ ‖∑ i : Fin (L * k), if (i : ℕ) < k * b + k then v (π i) else 0‖ +
          ‖∑ i : Fin (L * k), if (i : ℕ) < k * b then v (π i) else 0‖ := norm_sub_le _ _
      _ ≤ d * ℓ + d * ℓ := add_le_add h1 h2
      _ = 2 * d * ℓ := by ring

end Disc


open Filter Topology

section Weighted
variable {d M k : ℕ}

/-- Labels with prescribed counts. -/
lemma exists_lab (n : Fin M → ℕ) :
    ∃ lab : Fin (∑ c, n c) → Fin M, ∀ c, ((Finset.univ.filter (fun i => lab i = c)).card : ℝ) = n c := by
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun c => ?_⟩
  rw [Finset.card_filter, Nat.cast_sum]
  rw [← Equiv.sum_comp finSigmaFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ c) h

/-- `∑_i x(lab i) = ∑_c #(lab⁻¹ c) • x c`. -/
lemma sum_lab {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (lab : Fin N → Fin M)
    (x : Fin M → E) :
    ∑ i, x (lab i) = ∑ c, ((Finset.univ.filter (fun i => lab i = c)).card : ℝ) • x c := by
  rw [← Finset.sum_fiberwise Finset.univ lab (fun i => x (lab i))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => x c) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
    Finset.sum_const, Nat.cast_smul_eq_nsmul]

/-- A convex combination of points at mutual distance at most `ℓ` is within `ℓ` of each point. -/
lemma norm_sub_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : Fin M → ℝ)
    (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (x : Fin M → E) {ℓ : ℝ}
    (hx : ∀ c c', ‖x c - x c'‖ ≤ ℓ) (c : Fin M) : ‖x c - ∑ c', p c' • x c'‖ ≤ ℓ := by
  have : x c - ∑ c', p c' • x c' = ∑ c', p c' • (x c - x c') := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp1, one_smul]
  rw [this]
  calc ‖∑ c', p c' • (x c - x c')‖ ≤ ∑ c', ‖p c' • (x c - x c')‖ := norm_sum_le _ _
    _ ≤ ∑ c', p c' * ℓ := Finset.sum_le_sum fun c' _ => by
        rw [norm_smul, Real.norm_of_nonneg (hp0 c')]
        exact mul_le_mul_of_nonneg_left (hx c c') (hp0 c')
    _ = ℓ := by rw [← Finset.sum_mul, hp1, one_mul]

/-- Lemma `as:lem:conc` (c) for finitely many weighted points (real weights): limit of the
Steinitz couplings for rational approximations of the weights. -/
lemma weighted_coupling (hS : H_steinitz) (hk : 0 < k) (hM : 0 < M) (p : Fin M → ℝ)
    (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (x : Fin M → EuclideanSpace ℝ (Fin d)) {ℓ : ℝ}
    (hx : ∀ c c', ‖x c - x c'‖ ≤ ℓ) :
    ∃ w : (Fin k → Fin M) → ℝ, IsLabCoupling p w ∧
      ∀ t, 0 < w t → ‖∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c‖ ≤ 2 * d * ℓ := by
  set c0 : Fin M := ⟨0, hM⟩
  set j0 : Fin k := ⟨0, hk⟩
  -- rational approximations
  set Lk : ℕ → ℕ := fun N => (N + 1) * k
  have hLk : ∀ N, (0 : ℝ) < Lk N := fun N => by simp only [Lk]; positivity
  set fl : ℕ → Fin M → ℕ := fun N c => ⌊p c * Lk N⌋₊
  have hfl : ∀ N, ∑ c ∈ Finset.univ.erase c0, fl N c ≤ Lk N := by
    intro N
    have : (∑ c ∈ Finset.univ.erase c0, (fl N c : ℝ)) ≤ Lk N := by
      calc (∑ c ∈ Finset.univ.erase c0, (fl N c : ℝ)) ≤ ∑ c ∈ Finset.univ.erase c0, p c * Lk N :=
            Finset.sum_le_sum fun c _ => Nat.floor_le (mul_nonneg (hp0 c) (hLk N).le)
        _ ≤ ∑ c, p c * Lk N := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun c _ _ => mul_nonneg (hp0 c) (hLk N).le
        _ = Lk N := by rw [← Finset.sum_mul, hp1, one_mul]
    exact_mod_cast this
  set n : ℕ → Fin M → ℕ := fun N c =>
    if c = c0 then Lk N - ∑ c ∈ Finset.univ.erase c0, fl N c else fl N c
  have hnsum : ∀ N, ∑ c, n N c = Lk N := by
    intro N
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
    simp only [n, if_pos rfl]
    rw [Finset.sum_congr rfl (g := fl N) (fun c hc => if_neg (Finset.ne_of_mem_erase hc))]
    exact Nat.sub_add_cancel (hfl N)
  set pN : ℕ → Fin M → ℝ := fun N c => (n N c : ℝ) / Lk N
  have hpN0 : ∀ N c, 0 ≤ pN N c := fun N c => by positivity
  have hpN1 : ∀ N, ∑ c, pN N c = 1 := by
    intro N
    simp only [pN, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (hLk N).ne']; exact_mod_cast hnsum N
  -- convergence of the weights
  have htend_ne : ∀ c, c ≠ c0 → Tendsto (fun N => pN N c) atTop (𝓝 (p c)) := by
    intro c hc
    have e : ∀ N, pN N c = (fl N c : ℝ) / Lk N := fun N => by simp only [pN, n, if_neg hc]
    simp only [e]
    have hup : ∀ N, (fl N c : ℝ) / Lk N ≤ p c := fun N => by
      rw [div_le_iff₀ (hLk N)]; exact Nat.floor_le (mul_nonneg (hp0 c) (hLk N).le)
    have hlo : ∀ N : ℕ, p c - 1 / ((N : ℝ) + 1) ≤ (fl N c : ℝ) / Lk N := fun N => by
      have h1 := Nat.lt_floor_add_one (p c * Lk N)
      change p c * (Lk N : ℝ) < (fl N c : ℝ) + 1 at h1
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [le_div_iff₀ (hLk N)]
      have : (Lk N : ℝ) = (N + 1) * k := by simp [Lk]
      rw [this] at h1 ⊢
      have hN1 : (0:ℝ) < N + 1 := by positivity
      rw [sub_mul, div_mul_eq_mul_div, one_mul, mul_div_assoc,
        show ((N:ℝ) + 1) * (k / ((N:ℝ) + 1)) = k by field_simp]
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlo hup
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds (x := p c)).sub this
  have htend : ∀ c, Tendsto (fun N => pN N c) atTop (𝓝 (p c)) := by
    intro c
    by_cases hc : c = c0
    · subst hc
      have e : ∀ N, pN N c0 = 1 - ∑ c ∈ Finset.univ.erase c0, pN N c := by
        intro N; rw [← hpN1 N, ← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]; ring
      have e2 : p c0 = 1 - ∑ c ∈ Finset.univ.erase c0, p c := by
        rw [← hp1, ← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]; ring
      simp only [e]; rw [e2]
      exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun c hc =>
        htend_ne c (Finset.ne_of_mem_erase hc))
    · exact htend_ne c hc
  -- Steinitz couplings for the approximations
  set mN : ℕ → EuclideanSpace ℝ (Fin d) := fun N => ∑ c, pN N c • x c
  have hdisc : ∀ N, ∃ w : (Fin k → Fin M) → ℝ, IsLabCoupling (pN N) w ∧
      ∀ t, 0 < w t → ‖∑ j, x (t j) - (k : ℝ) • mN N‖ ≤ 2 * d * ℓ := by
    intro N
    obtain ⟨lab, hlab⟩ := exists_lab (n N)
    have hcast : ∑ c, n N c = (N + 1) * k := hnsum N
    -- transport to `Fin ((N+1) * k)`
    set lab' : Fin ((N + 1) * k) → Fin M := fun i => lab (Fin.cast hcast.symm i)
    have hlab' : ∀ c, ((Finset.univ.filter (fun i => lab' i = c)).card : ℝ) = n N c := by
      intro c
      rw [← hlab c]
      congr 1
      rw [Finset.card_filter, Finset.card_filter]
      exact Fintype.sum_equiv (finCongr hcast.symm) _ _ (fun i => rfl)
    have hm : ((((N + 1) * k : ℕ) : ℝ))⁻¹ • ∑ i', x (lab' i') = mN N := by
      rw [sum_lab, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hlab', smul_smul]; simp only [pN, Lk]; congr 1; push_cast; ring
    obtain ⟨w, hw, hws⟩ := disc_coupling hS hk N.succ_pos lab' x (ℓ := ℓ) (by
      intro i; rw [hm]; exact norm_sub_convex _ (hpN0 N) (hpN1 N) x hx _)
    refine ⟨w, ⟨hw.1, fun j c => ?_⟩, fun t ht => ?_⟩
    · rw [hw.2 j c]; simp only [hlab', pN, Lk]; push_cast; ring
    · have := hws t ht; rwa [hm] at this
  choose wN hwN hwNs using hdisc
  -- compactness
  have hbound : ∀ N t, wN N t ∈ Icc (0 : ℝ) 1 := by
    intro N t
    refine ⟨(hwN N).1 t, ?_⟩
    have h1 := (hwN N).2 j0 (t j0)
    have h2 : wN N t ≤ ∑ t', (if t' j0 = t j0 then wN N t' else 0) := by
      have := Finset.single_le_sum (f := fun t' => if t' j0 = t j0 then wN N t' else 0)
        (fun t' _ => by split_ifs; exact (hwN N).1 t'; exact le_rfl) (Finset.mem_univ t)
      simpa using this
    have h3 : pN N (t j0) ≤ 1 := by
      rw [← hpN1 N]
      exact Finset.single_le_sum (fun c _ => hpN0 N c) (Finset.mem_univ _)
    linarith
  obtain ⟨w, -, φ, hφ, hlim⟩ := (isCompact_univ_pi (fun _ : Fin k → Fin M =>
    isCompact_Icc (a := (0:ℝ)) (b := 1))).tendsto_subseq (x := wN)
    (fun N => mem_univ_pi.2 (hbound N))
  have hlimt : ∀ t, Tendsto (fun N => wN (φ N) t) atTop (𝓝 (w t)) := fun t =>
    (continuous_apply t).continuousAt.tendsto.comp hlim
  have hmN : Tendsto (fun N => mN (φ N)) atTop (𝓝 (∑ c, p c • x c)) :=
    tendsto_finsetSum _ fun c _ => ((htend c).comp hφ.tendsto_atTop).smul_const _
  refine ⟨w, ⟨fun t => ge_of_tendsto' (hlimt t) fun N => (hwN (φ N)).1 t, fun j c => ?_⟩,
    fun t ht => ?_⟩
  · have h1 : Tendsto (fun N => ∑ t, (if t j = c then wN (φ N) t else 0)) atTop
        (𝓝 (∑ t, (if t j = c then w t else 0))) :=
      tendsto_finsetSum _ fun t _ => by
        split_ifs; exact hlimt t; exact tendsto_const_nhds
    have h2 : (fun N => ∑ t, (if t j = c then wN (φ N) t else 0)) = fun N => pN (φ N) c :=
      funext fun N => (hwN (φ N)).2 j c
    rw [h2] at h1
    exact tendsto_nhds_unique h1 ((htend c).comp hφ.tendsto_atTop)
  · have hev : ∀ᶠ N in atTop, 0 < wN (φ N) t := (hlimt t).eventually (lt_mem_nhds ht)
    have hcont : Tendsto (fun N => ‖∑ j, x (t j) - (k : ℝ) • mN (φ N)‖) atTop
        (𝓝 ‖∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c‖) :=
      (tendsto_const_nhds.sub (hmN.const_smul _)).norm
    exact le_of_tendsto hcont (hev.mono fun N hN => hwNs (φ N) t hN)

end Weighted

section Lift
variable {d k : ℕ}
open ProbabilityTheory

/-- A finite measurable partition of a nonempty compact set into cells of diameter at most `ε`. -/
lemma exists_partition {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hne : K.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (C : Fin M → Set (EuclideanSpace ℝ (Fin d))), 0 < M ∧ (∀ c, MeasurableSet (C c)) ∧
      (∀ c, C c ⊆ K) ∧ (∀ x ∈ K, ∃ c, x ∈ C c) ∧ (∀ c c', c ≠ c' → Disjoint (C c) (C c')) ∧
      ∀ c, ∀ x ∈ C c, ∀ y ∈ C c, dist x y ≤ ε := by
  obtain ⟨t, htK, htf, hcov⟩ := finite_cover_balls_of_compact hK (half_pos hε)
  set e := htf.toFinset.equivFin
  set M := htf.toFinset.card
  set z : Fin M → EuclideanSpace ℝ (Fin d) := fun c => (e.symm c : EuclideanSpace ℝ (Fin d))
  set C : Fin M → Set (EuclideanSpace ℝ (Fin d)) := fun c =>
    K ∩ Metric.ball (z c) (ε / 2) ∩ ⋂ c' ∈ Finset.univ.filter (fun c' => c' < c),
      (Metric.ball (z c') (ε / 2))ᶜ
  have hcov' : ∀ x ∈ K, ∃ c, x ∈ Metric.ball (z c) (ε / 2) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hx)
    exact ⟨e ⟨y, htf.mem_toFinset.2 hy⟩, by simpa [z] using hxy⟩
  refine ⟨M, C, ?_, fun c => ?_, fun c => fun x hx => hx.1.1, fun x hx => ?_, fun c c' hcc' => ?_,
    fun c x hx y hy => ?_⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨c, -⟩ := hcov' x hx
    exact Fin.pos_iff_nonempty.2 ⟨c⟩
  · exact (hK.isClosed.measurableSet.inter Metric.isOpen_ball.measurableSet).inter
      (Finset.measurableSet_biInter _ fun c' _ => Metric.isOpen_ball.measurableSet.compl)
  · classical
    set s := Finset.univ.filter (fun c => x ∈ Metric.ball (z c) (ε / 2))
    have hs : s.Nonempty := by
      obtain ⟨c, hc⟩ := hcov' x hx
      exact ⟨c, by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc⟩
    refine ⟨s.min' hs, ⟨hx, (Finset.mem_filter.1 (s.min'_mem hs)).2⟩, ?_⟩
    simp only [mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and, mem_compl_iff]
    intro c' hc' hin
    exact absurd (s.min'_le c' (by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hin)) (not_le.2 hc')
  · rw [Set.disjoint_left]
    intro x hx hx'
    rcases lt_or_gt_of_ne hcc' with h | h
    · have := hx'.2
      simp only [mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and, mem_compl_iff] at this
      exact this c h hx.1.2
    · have := hx.2
      simp only [mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and, mem_compl_iff] at this
      exact this c' h hx'.1.2
  · have h1 := Metric.mem_ball.1 hx.1.2
    have h2 := Metric.mem_ball.1 hy.1.2
    calc dist x y ≤ dist x (z c) + dist y (z c) := dist_triangle_right _ _ _
      _ ≤ ε := by linarith


/-- Lifting step of Lemma `as:lem:conc` (c): a coupling with exact marginals and error
`2 d ℓ + 2 k ε`. -/
lemma eps_coupling (hS : H_steinitz) (hk : 0 < k) (T : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure T] {K : Set (EuclideanSpace ℝ (Fin d))} (hKc : IsCompact K)
    (hKT : T Kᶜ = 0) {ℓ : ℝ} (hKd : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ ℓ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Measure (Fin k → EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P ∧
      (∀ j, P.map (fun y => y j) = T) ∧ P (Set.univ.pi fun _ => K)ᶜ = 0 ∧
      ∀ᵐ y ∂P, ‖∑ j, y j - (k : ℝ) • ∫ x, x ∂T‖ ≤ 2 * d * ℓ + 2 * k * ε := by
  classical
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hne : K.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hKT; exact one_ne_zero hKT
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨M, C, hM, hCm, hCK, hcov, hdisj, hCd⟩ := exists_partition hKc ⟨x0, hx0⟩ hε
  set p : Fin M → ℝ := fun c => (T (C c)).toReal with hp_def
  set x : Fin M → EuclideanSpace ℝ (Fin d) := fun c =>
    if h : (C c).Nonempty then h.some else x0 with hx_def
  have hxK : ∀ c, x c ∈ K := fun c => by
    simp only [x]; split_ifs with h
    · exact hCK c h.some_mem
    · exact hx0
  have hxC : ∀ c, (C c).Nonempty → x c ∈ C c := fun c h => by
    simp only [x, dif_pos h]; exact h.some_mem
  have hUK : (⋃ c, C c) = K := Set.Subset.antisymm (Set.iUnion_subset hCK)
    (fun y hy => Set.mem_iUnion.2 (hcov y hy))
  have hsplit : ∀ s, MeasurableSet s → ∑ c, T (C c ∩ s) = T s := by
    intro s hs
    have hU : T (⋃ c, C c ∩ s) = ∑ c, T (C c ∩ s) := by
      rw [measure_iUnion (fun c c' hcc' =>
        ((hdisj c c' hcc').mono Set.inter_subset_left Set.inter_subset_left))
        (fun c => (hCm c).inter hs), tsum_fintype]
    rw [← hU, ← Set.iUnion_inter, hUK, Set.inter_comm]
    exact measure_inter_conull hKT
  have hp0 : ∀ c, 0 ≤ p c := fun c => ENNReal.toReal_nonneg
  have hp1 : ∑ c, p c = 1 := by
    simp only [p]; rw [← ENNReal.toReal_sum (fun c _ => measure_ne_top _ _)]
    have := hsplit univ MeasurableSet.univ
    simp only [Set.inter_univ, measure_univ] at this
    rw [this]; rfl
  obtain ⟨w, ⟨hw0, hwm⟩, hwb⟩ := weighted_coupling hS hk hM p hp0 hp1 x (ℓ := ℓ)
    (fun c c' => by rw [← dist_eq_norm]; exact hKd _ (hxK c) _ (hxK c'))
  set q : Fin M → Measure (EuclideanSpace ℝ (Fin d)) := fun c =>
    if T (C c) = 0 then T else T[|C c] with hq_def
  have hq : ∀ c, IsProbabilityMeasure (q c) := fun c => by
    simp only [q]; split_ifs with h
    · infer_instance
    · exact cond_isProbabilityMeasure h
  have hqs : ∀ c s, MeasurableSet s → ENNReal.ofReal (p c) * q c s = T (C c ∩ s) := by
    intro c s hs
    simp only [p, ENNReal.ofReal_toReal (measure_ne_top _ _), q]
    split_ifs with h
    · rw [h, zero_mul]; exact (measure_mono_null Set.inter_subset_left h).symm
    · rw [mul_comm]; exact cond_mul_eq_inter (hCm c) s T
  set P : Measure (Fin k → EuclideanSpace ℝ (Fin d)) :=
    ∑ t, ENNReal.ofReal (w t) • Measure.pi (fun j => q (t j)) with hP_def
  have hPapp : ∀ A, P A = ∑ t, ENNReal.ofReal (w t) * Measure.pi (fun j => q (t j)) A := by
    intro A; simp only [P, _root_.sum_apply, smul_apply, smul_eq_mul]
  have hmarg : ∀ j, P.map (fun y => y j) = T := by
    intro j; ext s hs
    rw [Measure.map_apply (measurable_pi_apply j) hs, hPapp]
    have h1 : ∀ t : Fin k → Fin M,
        Measure.pi (fun j => q (t j)) ((fun y => y j) ⁻¹' s) = q (t j) s := fun t =>
      (measurePreserving_eval (fun j => q (t j)) j).measure_preimage hs.nullMeasurableSet
    simp_rw [h1]
    rw [← hsplit s hs, ← Finset.sum_fiberwise Finset.univ (fun t : Fin k → Fin M => t j)
      (fun t => ENNReal.ofReal (w t) * q (t j) s)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hqs c s hs, ← hwm j c, ← Finset.sum_filter,
      ENNReal.ofReal_sum_of_nonneg (fun t _ => hw0 t), Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.1 ht).2]
  have hPprob : IsProbabilityMeasure P := by
    constructor
    have := congrArg (fun μ : Measure _ => μ univ) (hmarg ⟨0, hk⟩)
    simp only [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, Set.preimage_univ,
      measure_univ] at this
    exact this
  -- good sets
  set G : (Fin k → Fin M) → Set (Fin k → EuclideanSpace ℝ (Fin d)) := fun t =>
    {y | ∀ j, y j ∈ C (t j)} with hG_def
  have hpw : ∀ t j, w t ≤ p (t j) := fun t j => by
    rw [← hwm j (t j)]
    have := Finset.single_le_sum (f := fun t' : Fin k → Fin M => if t' j = t j then w t' else 0)
      (fun t' _ => by split_ifs <;> simp [hw0 t']) (Finset.mem_univ t)
    simpa using this
  have hGnull : ∀ t, 0 < w t → Measure.pi (fun j => q (t j)) (G t)ᶜ = 0 := by
    intro t ht
    have hG : (G t)ᶜ = ⋃ j, (fun y : Fin k → EuclideanSpace ℝ (Fin d) => y j) ⁻¹' (C (t j))ᶜ := by
      ext y; simp [G]
    rw [hG]
    refine measure_iUnion_null fun j => ?_
    rw [(measurePreserving_eval (fun j => q (t j)) j).measure_preimage
      (hCm (t j)).compl.nullMeasurableSet]
    have hpos : T (C (t j)) ≠ 0 := by
      intro h0
      have := hpw t j
      simp only [p, h0, ENNReal.toReal_zero] at this
      linarith
    simp only [q, if_neg hpos]
    exact ae_iff.1 (ae_cond_mem (hCm (t j)))
  have hae : ∀ Q : (Fin k → EuclideanSpace ℝ (Fin d)) → Prop,
      (∀ t, 0 < w t → ∀ y ∈ G t, Q y) → ∀ᵐ y ∂P, Q y := by
    intro Q hQ
    rw [ae_iff, hPapp]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases (hw0 t).lt_or_eq with ht | ht
    · rw [measure_mono_null (fun y hy => ?_) (hGnull t ht), mul_zero]
      by_contra hyG
      exact hy (hQ t ht y (by simpa using hyG))
    · rw [← ht, ENNReal.ofReal_zero, zero_mul]
  -- mean
  have hTsum : T = ∑ c, T.restrict (C c) := by
    ext s hs
    rw [_root_.sum_apply, ← hsplit s hs]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Measure.restrict_apply hs, Set.inter_comm]
  have hint : Integrable id T := integrable_of_bdd hKc.isBounded hKT
  have hmean : ‖∑ c, p c • x c - ∫ y, y ∂T‖ ≤ ε := by
    have h1 : ∫ y, y ∂T = ∑ c, ∫ y, y ∂(T.restrict (C c)) := by
      conv_lhs => rw [hTsum]
      exact integral_finsetSum_measure fun c _ => hint.restrict
    have h2 : ∀ c, p c • x c = ∫ _y, x c ∂(T.restrict (C c)) := fun c => by
      rw [integral_const, measureReal_def, Measure.restrict_apply_univ]
    rw [h1, ← Finset.sum_sub_distrib]
    calc ‖∑ c, (p c • x c - ∫ y, y ∂(T.restrict (C c)))‖
        ≤ ∑ c, ‖p c • x c - ∫ y, y ∂(T.restrict (C c))‖ := norm_sum_le _ _
      _ ≤ ∑ c, ε * p c := Finset.sum_le_sum fun c _ => by
          rw [h2, ← integral_sub (f := fun _ => x c) (g := fun y => y) (integrable_const _) hint.restrict]
          have := norm_integral_le_of_norm_le_const (μ := T.restrict (C c))
            (f := fun y => x c - y) (C := ε) ?_
          · simpa [measureReal_def, Measure.restrict_apply_univ, p] using this
          · refine ae_restrict_of_forall_mem (hCm c) fun y hy => ?_
            rw [← dist_eq_norm]; exact hCd c _ (hxC c ⟨y, hy⟩) _ hy
      _ = ε := by rw [← Finset.mul_sum, hp1, mul_one]
  refine ⟨P, hPprob, hmarg, ?_, hae _ fun t ht y hy => ?_⟩
  · have := hae (fun y => y ∈ Set.univ.pi fun _ => K) fun t _ y hy =>
      fun j _ => hCK _ (hy j)
    exact ae_iff.1 this
  · have hdec : ∑ j, y j - (k : ℝ) • ∫ x, x ∂T = ∑ j, (y j - x (t j)) +
        (∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c) + (k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T) := by
      rw [Finset.sum_sub_distrib, smul_sub]; abel
    rw [hdec]
    have hA : ‖∑ j, (y j - x (t j))‖ ≤ k * ε := by
      calc ‖∑ j, (y j - x (t j))‖ ≤ ∑ j, ‖y j - x (t j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin k, ε := Finset.sum_le_sum fun j _ => by
            rw [← dist_eq_norm]; exact hCd _ _ (hy j) _ (hxC _ ⟨y j, hy j⟩)
        _ = k * ε := by simp
    have hB := hwb t ht
    have hC : ‖(k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T)‖ ≤ k * ε := by
      rw [norm_smul, Real.norm_natCast]
      exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg k)
    calc _ ≤ ‖∑ j, (y j - x (t j)) + (∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c)‖ +
          ‖(k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T)‖ := norm_add_le _ _
      _ ≤ ‖∑ j, (y j - x (t j))‖ + ‖∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c‖ +
          ‖(k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith

open scoped BoundedContinuousFunction

/-- **Lemma `as:lem:conc` (c)**: if `T` is supported on a set of diameter at most `ℓ`, there is a
coupling of `k` copies of `T` whose sum stays within norm distance `2 d ℓ` of `k` times the mean.
Proved from `H_steinitz` (Grinberg–Sevastyanov) by the Steinitz coupling of a fine partition and a
Prokhorov limit. -/
theorem lem_conc_c (hS : H_steinitz) (hk : 0 < k) (T : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure T] {ℓ : ℝ} (hT : SuppDiam T ℓ) :
    ∃ P : Measure (Fin k → EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P ∧
      (∀ j, P.map (fun y => y j) = T) ∧
      ∀ᵐ y ∂P, ‖∑ j, y j - (k : ℝ) • ∫ x, x ∂T‖ ≤ 2 * d * ℓ := by
  obtain ⟨S0, hS0T, hS0d⟩ := hT
  have hb : Bornology.IsBounded S0 := suppDiam_bdd (F := T) hS0d
  set K := closure S0 with hK_def
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hKT : T Kᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 subset_closure) hS0T
  have hne : S0.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hS0T; exact one_ne_zero hS0T
  have hℓ : 0 ≤ ℓ := by obtain ⟨x, hx⟩ := hne; simpa using hS0d x hx x hx
  have hKd : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ ℓ := by
    intro x hx y hy
    have hd : Metric.diam S0 ≤ ℓ := Metric.diam_le_of_forall_dist_le hℓ hS0d
    calc dist x y ≤ Metric.diam K := Metric.dist_le_diam_of_mem hb.closure hx hy
      _ = Metric.diam S0 := Metric.diam_closure S0
      _ ≤ ℓ := hd
  have hP := fun N : ℕ => eps_coupling hS hk T hKc hKT hKd (ε := 1 / ((N : ℝ) + 1))
    (by positivity)
  choose Ps hPprob hPmarg hPsupp hPbd using hP
  set μs : ℕ → ProbabilityMeasure (Fin k → EuclideanSpace ℝ (Fin d)) :=
    fun N => ⟨Ps N, hPprob N⟩ with hμs
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure (Fin k → EuclideanSpace ℝ (Fin d))) :
        Measure (Fin k → EuclideanSpace ℝ (Fin d))) | μ ∈ Set.range μs} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hKc, ?_⟩
    rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
    show Ps N _ ≤ ε
    rw [hPsupp N]; exact zero_le
  obtain ⟨μ, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    (fun N => subset_closure (Set.mem_range_self N))
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim
  refine ⟨μ, inferInstance, fun j => ?_, ?_⟩
  · refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    set g : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ :=
      f.compContinuous ⟨fun y => y j, continuous_apply j⟩
    have h1 : ∀ ν : Measure (Fin k → EuclideanSpace ℝ (Fin d)),
        ∫ x, f x ∂(ν.map fun y => y j) = ∫ y, g y ∂ν := fun ν => by
      rw [integral_map (measurable_pi_apply j).aemeasurable f.continuous.aestronglyMeasurable]; rfl
    rw [h1]
    have h2 := hlim g
    have h3 : (fun i => ∫ y, g y ∂((μs ∘ φ) i : Measure (Fin k → EuclideanSpace ℝ (Fin d)))) =
        fun _ => ∫ x, f x ∂T := by
      funext i
      show ∫ y, g y ∂(Ps (φ i)) = _
      rw [← h1, hPmarg]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  · set m := (k : ℝ) • ∫ x, x ∂T
    set gf : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ :=
      fun y => min 1 (max 0 (‖∑ j, y j - m‖ - 2 * d * ℓ)) with hgf
    have hgc : Continuous gf := by
      simp only [gf]; fun_prop
    have hg01 : ∀ y, 0 ≤ gf y ∧ gf y ≤ 1 := fun y =>
      ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    set g : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨gf, hgc⟩ 1 (fun a b => by
        show |gf a - gf b| ≤ 1
        have := hg01 a; have := hg01 b
        rw [abs_le]; constructor <;> linarith)
    have hgv : ∀ y, g y = gf y := fun y => rfl
    have hseq : ∀ N, ∫ y, g y ∂(Ps N) ≤ 2 * k * (1 / ((N : ℝ) + 1)) := by
      intro N
      have : ∀ᵐ y ∂(Ps N), g y ≤ 2 * k * (1 / ((N : ℝ) + 1)) := (hPbd N).mono fun y hy => by
        rw [hgv]; exact (min_le_right _ _).trans (max_le (by positivity) (by linarith))
      calc ∫ y, g y ∂(Ps N) ≤ ∫ _y, 2 * k * (1 / ((N : ℝ) + 1)) ∂(Ps N) :=
            integral_mono_ae (g.integrable _) (integrable_const _) this
        _ = _ := by simp
    have hpos : ∀ N, 0 ≤ ∫ y, g y ∂(Ps N) := fun N => integral_nonneg fun y => (hg01 y).1
    have hto : Tendsto (fun N => ∫ y, g y ∂(Ps N)) atTop (𝓝 0) := by
      refine squeeze_zero hpos hseq ?_
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (k : ℝ))
      rwa [mul_zero] at this
    have h2 := hlim g
    have h0 : ∫ y, g y ∂(μ : Measure (Fin k → EuclideanSpace ℝ (Fin d))) = 0 :=
      tendsto_nhds_unique h2 (hto.comp hφ.tendsto_atTop)
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => (hg01 y).1) (g.integrable _)).1 h0
    filter_upwards [hae] with y hy
    have hy' : gf y = 0 := hy
    have hmax : max 0 (‖∑ j, y j - m‖ - 2 * d * ℓ) = 0 := by
      rcases le_total 1 (max 0 (‖∑ j, y j - m‖ - 2 * d * ℓ)) with h | h
      · simp only [gf, min_eq_left h] at hy'; norm_num at hy'
      · simpa only [gf, min_eq_right h] using hy'
    have := le_max_right 0 (‖∑ j, y j - m‖ - 2 * d * ℓ)
    linarith

end Lift

section Final
variable {d : ℕ}

/-- The coupling bound for `d ≥ 2` (more generally `d ≠ 1`), from Lemma `as:lem:conc` (c). -/
theorem couplingBound_of_steinitz (hS : H_steinitz) (hd : d ≠ 1) : CouplingBound d := by
  intro T _ R k hk hT
  obtain ⟨P, hP, hPm, hPb⟩ := lem_conc_c hS hk T hT
  refine ⟨P, hP, hPm, hPb.mono fun y hy i => ?_⟩
  have h1 := PiLp.norm_apply_le (∑ j, y j - (k : ℝ) • ∫ x, x ∂T) i
  rw [Real.norm_eq_abs] at h1
  simp only [cdConst, if_neg hd]
  linarith

/-- The coupling bound for `d = 1`, from Lemma `as:lem:conc` (b) (the grid coupling), transported
from `ℝ` to `EuclideanSpace ℝ (Fin 1)`. -/
theorem couplingBound_one : CouplingBound 1 := by
  intro T _ R k hk hT
  obtain ⟨S0, hS0T, hS0d⟩ := hT
  set L : Rd 1 ≃L[ℝ] ℝ := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) with hL
  set eL : Rd 1 ≃ᵐ ℝ := L.toHomeomorph.toMeasurableEquiv with heL
  have hcoord : ∀ (v : Rd 1) (i : Fin 1), v i = L v := fun v i => by
    rw [Fin.fin_one_eq_zero i]; rfl
  have heLv : ∀ v, eL v = L v := fun v => rfl
  have heLs : ∀ r, L (eL.symm r) = r := fun r => L.apply_symm_apply r
  set T' : Measure ℝ := T.map eL with hT'
  have : IsProbabilityMeasure T' := inferInstance
  have hne : S0.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hS0T; exact one_ne_zero hS0T
  have hR : 0 ≤ R := by obtain ⟨x, hx⟩ := hne; simpa using hS0d x hx x hx
  have hLd : ∀ x ∈ S0, ∀ y ∈ S0, dist (L x) (L y) ≤ R := by
    intro x hx y hy
    have h1 := PiLp.norm_apply_le (x - y) 0
    rw [hcoord, map_sub, ← dist_eq_norm, ← dist_eq_norm] at h1
    exact h1.trans (hS0d x hx y hy)
  obtain ⟨a, ha⟩ := exists_Icc_of_diam (A := L '' S0)
    (Metric.isBounded_iff.2 ⟨R, by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact hLd x hx y hy⟩)
    (hne.image _) (Metric.diam_le_of_forall_dist_le hR (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact hLd x hx y hy))
  have hT'I : T' (Icc a (a + R))ᶜ = 0 := by
    rw [hT', eL.map_apply]
    exact measure_mono_null (show eL ⁻¹' (Icc a (a + R))ᶜ ⊆ S0ᶜ from
      fun x hx hxS => hx (ha ⟨x, hxS, rfl⟩)) hS0T
  have hint' : Integrable id T' := integrable_of_Icc hT'I
  set P' := gridCoupling T' a (a + R) k with hP'
  have : IsProbabilityMeasure P' := gridCoupling_isProb k
  have hP'm : ∀ j, P'.map (fun y => y j) = T' := gridCoupling_map_eval hT'I hk
  obtain ⟨c, hc⟩ := gridCoupling_sum (μ := T') (by linarith : a ≤ a + R) hk
  rw [add_sub_cancel_left] at hc
  have hb := abs_sum_sub_mean_le P' (fun _ => T') hP'm (fun _ => hint') hc
  set e : (Fin k → ℝ) ≃ᵐ (Fin k → Rd 1) := MeasurableEquiv.piCongrRight (fun _ => eL.symm)
    with he
  refine ⟨P'.map e, inferInstance, fun j => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply j) e.measurable]
    have : (fun y : Fin k → Rd 1 => y j) ∘ e = eL.symm ∘ (fun y => y j) := rfl
    rw [this, ← Measure.map_map eL.symm.measurable (measurable_pi_apply j), hP'm, hT',
      Measure.map_map eL.symm.measurable eL.measurable, eL.symm_comp_self, Measure.map_id]
  · have hmean : L (∫ x, x ∂T) = ∫ r, r ∂T' := by
      rw [← L.integral_comp_comm, hT', eL.measurableEmbedding.integral_map]
      rfl
    rw [ae_iff, e.map_apply]
    refine ae_iff.1 (hb.mono fun y hy i => ?_)
    rw [hcoord]
    have hc1 : cdConst 1 = 1 := by simp [cdConst]
    rw [hc1, one_mul]
    rw [map_sub, map_sum, map_smul, hmean]
    show |∑ j, L (eL.symm (y j)) - _| ≤ R
    simp only [heLs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      smul_eq_mul] at hy ⊢
    exact hy

/-- **Theorem `as:thm:window`** for `d = 1`, assuming Proposition `as:prop:window` (`PropWindow`). -/
theorem thm_window_d1 (hP : PropWindow) : ThmWindow 1 := thmWindow_of hP couplingBound_one

/-- **Theorem `as:thm:window`** for `d ≥ 2`, assuming Proposition `as:prop:window` and the
Steinitz lemma with the constant of Grinberg–Sevastyanov (`H_steinitz`). -/
theorem thm_window_ge2 (hP : PropWindow) (hS : H_steinitz) (hd : 2 ≤ d) : ThmWindow d :=
  thmWindow_of hP (couplingBound_of_steinitz hS (by omega))

/-- **Theorem `as:thm:window`** for every dimension. -/
theorem thm_window (hP : PropWindow) (hS : H_steinitz) (d : ℕ) : ThmWindow d := by
  rcases eq_or_ne d 1 with rfl | hd
  · exact thm_window_d1 hP
  · exact thmWindow_of hP (couplingBound_of_steinitz hS hd)

end Final

/-! ### Lemma `as:lem:conc` (a) and (b), packaged -/

/-- **Lemma `as:lem:conc` (a)**: distributions `T_j` on `ℝ`, each carried by an interval of length
`ℓ` (the intervals may differ), admit a coupling whose sum lies in an interval of length `ℓ`,
hence within `ℓ` of the sum of the means. -/
theorem lem_conc_a {k : ℕ} (hk : 0 < k) (T : Fin k → Measure ℝ) [∀ j, IsProbabilityMeasure (T j)]
    {ℓ : ℝ} (hT : ∀ j, ∃ a, T j (Icc a (a + ℓ))ᶜ = 0) :
    ∃ P : Measure (Fin k → ℝ), IsProbabilityMeasure P ∧ (∀ j, P.map (fun y => y j) = T j) ∧
      (∃ c, ∀ᵐ y ∂P, ∑ j, y j ∈ Icc c (c + ℓ)) ∧
      ∀ᵐ y ∂P, |∑ j, y j - ∑ j, ∫ x, x ∂(T j)| ≤ ℓ := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨P, hP, hPm, c, hc⟩ := conc_a_aux ℓ k' T inferInstance hT
  refine ⟨P, hP, hPm, ⟨c, hc⟩, ?_⟩
  exact abs_sum_sub_mean_le P T hPm (fun j => integrable_of_Icc (hT j).choose_spec) hc

/-- **Lemma `as:lem:conc` (b)**: for `T` carried by `[a, a + ℓ]`, the grid coupling
`Y_j = Q_T((σ(j) - 1 + W)/k)` (`gridCoupling`) has marginals `T` and a sum in an interval of
length `ℓ`, hence within `ℓ` of `k m_T`. -/
theorem lem_conc_b (T : Measure ℝ) [IsProbabilityMeasure T] {a ℓ : ℝ}
    (hT : T (Icc a (a + ℓ))ᶜ = 0) {k : ℕ} (hk : 0 < k) :
    (∀ j, (gridCoupling T a (a + ℓ) k).map (fun y => y j) = T) ∧
      (∃ c, ∀ᵐ y ∂(gridCoupling T a (a + ℓ) k), ∑ j, y j ∈ Icc c (c + ℓ)) ∧
      ∀ᵐ y ∂(gridCoupling T a (a + ℓ) k), |∑ j, y j - k * ∫ x, x ∂T| ≤ ℓ := by
  have hℓ : 0 ≤ ℓ := by
    by_contra h
    rw [Set.Icc_eq_empty (by linarith), Set.compl_empty, measure_univ] at hT
    exact one_ne_zero hT
  have : IsProbabilityMeasure (gridCoupling T a (a + ℓ) k) := gridCoupling_isProb k
  have hm := gridCoupling_map_eval hT hk
  obtain ⟨c, hc⟩ := gridCoupling_sum (μ := T) (by linarith : a ≤ a + ℓ) hk
  rw [add_sub_cancel_left] at hc
  refine ⟨hm, ⟨c, hc⟩, ?_⟩
  have := abs_sum_sub_mean_le _ (fun _ => T) hm (fun _ => integrable_of_Icc hT) hc
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

/-! ## Discharging Proposition `as:prop:window` with `Mixes.AsymWindow`

`PropWindow` and `PropWindowReal` above are verbatim copies of the statements in
`Mixes.AsymWindow`, where they are proved (`propWindow`, `propWindowReal`); the bridges are
definitional. -/

theorem propWindow_proved : PropWindow := Mixes.AsymWindow.propWindow

theorem propWindowReal_proved : PropWindowReal := Mixes.AsymWindow.propWindowReal

/-- **Theorem `as:thm:window`, `d = 1`**, on `EuclideanSpace ℝ (Fin 1)`, with no hypothesis. -/
theorem thm_window_d1_proved : ThmWindow 1 := thm_window_d1 propWindow_proved

/-- **Theorem `as:thm:window`** in every dimension, assuming only the Steinitz lemma with the
Grinberg–Sevastyanov constant (`H_steinitz`, used for `d ≥ 2`). This is the statement
`Mixes.AsymGeneral.H_thm_window d` (verbatim copy `ThmWindow d`). -/
theorem thm_window_proved (hS : H_steinitz) (d : ℕ) : ThmWindow d :=
  thm_window propWindow_proved hS d

/-- **Theorem `as:thm:window`, `d = 1`**, on `ℝ`, with no hypothesis. -/
theorem thm_window_one_proved (F : Measure ℝ) [IsProbabilityMeasure F]
    {R q c H : ℝ} (hH : 0 < H) (hq0 : 0 < q) (hq1 : q ≤ 1) {A : Set ℝ}
    (hA : Bornology.IsBounded A) (hdiam : Metric.diam A ≤ R) (hFA : F Aᶜ = 0)
    (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) {n : ℕ} (hn : 1 ≤ n)
    (hm : 4 ≤ ⌊q * n⌋₊) (hρ : 0 ≤ ⌊q * n⌋₊ * H / 2 - R)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνmean : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hνsupp : ν (Icc (n * ∫ x, x ∂F - (⌊q * n⌋₊ * H / 2 - R))
      (n * ∫ x, x ∂F + (⌊q * n⌋₊ * H / 2 - R)))ᶜ = 0) :
    ν ∈ AggSetC n F :=
  thm_window_one propWindowReal_proved F hH hq0 hq1 hA hdiam hFA hFq hn hm hρ ν hνmean hνsupp

/-- **Corollary `as:cor:interval`**, main statement, with no hypothesis. -/
theorem cor_interval_proved (F : Measure ℝ) [IsProbabilityMeasure F]
    {R q c H a : ℝ} (hH : 0 < H) (hq0 : 0 < q) (hq1 : q ≤ 1) (hF : F (Icc a (a + R))ᶜ = 0)
    (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) {n : ℕ} (hn : 2 * R / H ≤ ⌊q * n⌋₊) :
    Mixes.CompletelyMixable n F ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ x, x ∂ν = n * ∫ x, x ∂F →
      ν (Icc (n * ∫ x, x ∂F - (⌊q * n⌋₊ * H / 2 - R))
        (n * ∫ x, x ∂F + (⌊q * n⌋₊ * H / 2 - R)))ᶜ = 0 → ν ∈ AggSetC n F :=
  cor_interval propWindowReal_proved F hH hq0 hq1 hF hFq hn

/-- **Corollary `as:cor:interval`**: `n ≥ ⌈2R/H⌉/q`, with no hypothesis. -/
theorem cor_interval_n_proved (F : Measure ℝ) [IsProbabilityMeasure F]
    {R q c H a : ℝ} (hH : 0 < H) (hq0 : 0 < q) (hq1 : q ≤ 1) (hF : F (Icc a (a + R))ᶜ = 0)
    (hFq : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) {n : ℕ}
    (hn : (⌈2 * R / H⌉₊ : ℝ) / q ≤ n) : Mixes.CompletelyMixable n F :=
  cor_interval_n propWindowReal_proved F hH hq0 hq1 hF hFq hn

/-- **Corollary `as:cor:interval`**, last statement, with no hypothesis. -/
theorem cor_interval_density_proved (F : Measure ℝ) [IsProbabilityMeasure F]
    {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) (hF : F (Icc a b)ᶜ = 0)
    (hFδ : ENNReal.ofReal δ • volume.restrict (Icc a b) ≤ F) {n : ℕ}
    (hn : 4 / (δ * (b - a)) ≤ n) : Mixes.CompletelyMixable n F :=
  cor_interval_density propWindowReal_proved F hab hδ hF hFδ hn

end Mixes.AsymThm
