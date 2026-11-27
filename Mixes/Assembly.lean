import Mixes.Trapezoid
import Mixes.Uniform
import Mixes.Bodies
import Mixes.SlabsMix

/-!
# The probabilistic assembly of Theorem 40 (trapezoids)

Item M1d of the verification priorities: the assembly in the proof of Theorem 40
(`t:thm:trap` in `mixes/main.tex`). The normal form is
`T = {(x, y) : 0 ≤ x ≤ 1, g x ≤ y ≤ g x + h x}` with `h x = q + (1 - q) x`, `0 ≤ q ≤ 1`, and
`g x = a + b x`.

* `unifSet_trapSet_eq`: the disintegration of `U(T)`: the abscissa has the law `trapAbsc q`
  (density `h / ∫₀¹ h` on `[0, 1]`), and given it, the ordinate is uniform on the chord.
* `chordVec`, `measurable_chordVec`, `chordVec_spec`: Lemma 1 for the chords
  `[g(xⱼ), g(xⱼ) + h(xⱼ)]`, with the choices of the paper (a largest chord `k`, a minimising `s`)
  made measurably in the abscissae (the first admissible code, by `Nat.find`), under the planar
  Archimedes measure `archPlane` of `Mixes.Uniform`.
* `trapMix_isCompleteMix`: the assembly: for an `n`-complete mix `Q` of the abscissa, `n ≥ 3`,
  the law of `((Xᵢ, Yᵢ))ᵢ` (abscissae from `Q`, ordinates by `chordVec` with an independent `ξ`)
  is an `n`-complete mix of `U(T)`.
* `completelyMixable_trapezoid`: Theorem 40 for every trapezoid and triangle, by an affine map,
  from the `n`-complete mixability of the abscissa distributions.
* `completelyMixable_trapAbsc`: that mixability, from Corollary 13 (`SlabsMix.cor13_nondecreasing`,
  Theorem 12 after a reflection); `completelyMixable_trapezoid'`: Theorem 40 unconditionally.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Mixes

namespace Assembly

/-! ### The normal form and the disintegration of `U(T)` -/

/-- The trapezoid in normal form, `{(x, y) : 0 ≤ x ≤ 1, g x ≤ y ≤ g x + h x}`, `g x = a + b x`. -/
def trapSet (q a b : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ a + b * p.1 ≤ p.2 ∧ p.2 ≤ a + b * p.1 + trapH q p.1}

/-- The strip between the graphs of `g` and `g + h`. -/
def strip (q a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a + b * p.1 ≤ p.2 ∧ p.2 ≤ a + b * p.1 + trapH q p.1}

/-- The density `h / ∫₀¹ h = h / ((q + 1) / 2)` of the abscissa on `[0, 1]`. -/
def trapDens (q x : ℝ) : ℝ := trapH q x / ((q + 1) / 2)

/-- The law of the abscissa: density `h / ∫₀¹ h` on `[0, 1]`. -/
def trapAbsc (q : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 1)).withDensity fun x => ENNReal.ofReal (trapDens q x)

/-- The uniform distribution on the chord `[g x, g x + h x]` at abscissa `x`. -/
def chord (q a b x : ℝ) : Measure ℝ := unifI (a + b * x) (a + b * x + trapH q x)

lemma continuous_trapH (q : ℝ) : Continuous (trapH q) := by unfold trapH; fun_prop

lemma measurableSet_strip (q a b : ℝ) : MeasurableSet (strip q a b) := by
  have h1 : Measurable fun p : ℝ × ℝ => a + b * p.1 := by fun_prop
  have h2 : Measurable fun p : ℝ × ℝ => a + b * p.1 + trapH q p.1 := by unfold trapH; fun_prop
  exact (measurableSet_le h1 measurable_snd).inter (measurableSet_le measurable_snd h2)

lemma measurableSet_trapSet (q a b : ℝ) : MeasurableSet (trapSet q a b) := by
  have h0 : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have : trapSet q a b = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1} ∩ strip q a b := by
    ext p; simp [trapSet, strip, and_assoc]
  rw [this]; exact h0.inter (measurableSet_strip q a b)

lemma trapH_nonneg {q x : ℝ} (hq : 0 ≤ q) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ trapH q x := by
  unfold trapH; nlinarith [hx.1, hx.2]

lemma slice_strip (q a b t : ℝ) (A : Set (ℝ × ℝ)) :
    Prod.mk t ⁻¹' (A ∩ strip q a b) = Prod.mk t ⁻¹' A ∩ Icc (a + b * t) (a + b * t + trapH q t) :=
  by ext y; simp [strip]

lemma slice_trapSet (q a b t : ℝ) (A : Set (ℝ × ℝ)) :
    Prod.mk t ⁻¹' (A ∩ trapSet q a b) =
      if t ∈ Icc (0 : ℝ) 1 then Prod.mk t ⁻¹' (A ∩ strip q a b) else ∅ := by
  split_ifs with ht
  · ext y; simp [trapSet, strip, ht.1, ht.2]
  · ext y
    simp only [mem_preimage, mem_inter_iff, trapSet, mem_setOf_eq, mem_empty_iff_false,
      iff_false, not_and]
    simp only [mem_Icc, not_and_or, not_le] at ht
    intro _ h0 h1; rcases ht with h | h <;> linarith

/-- Fubini: `vol(A ∩ T) = ∫₀¹ vol({y : (x, y) ∈ A} ∩ [g x, g x + h x]) dx`. -/
lemma volume_inter_trapSet (q a b : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    volume (A ∩ trapSet q a b) =
      ∫⁻ t in Icc 0 1, volume (Prod.mk t ⁻¹' (A ∩ strip q a b)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (hA.inter (measurableSet_trapSet q a b)),
    ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun t => ?_
  rw [slice_trapSet]
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [if_pos ht, indicator_of_mem ht]
  · rw [if_neg ht, indicator_of_notMem ht, measure_empty]

/-- The set integral of `h` over `[0, 1]` is `(q + 1) / 2`. -/
lemma integral_trapH_Icc (q : ℝ) : ∫ x in Icc (0 : ℝ) 1, trapH q x = (q + 1) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  unfold trapH
  simp [intervalIntegral.integral_add, mul_comm]
  ring

lemma integrableOn_trapH (q : ℝ) : IntegrableOn (trapH q) (Icc 0 1) :=
  (continuous_trapH q).integrableOn_Icc

/-- `vol(T) = (q + 1) / 2`. -/
lemma volume_trapSet {q : ℝ} (hq : 0 ≤ q) (a b : ℝ) :
    volume (trapSet q a b) = ENNReal.ofReal ((q + 1) / 2) := by
  rw [← univ_inter (trapSet q a b), volume_inter_trapSet q a b MeasurableSet.univ,
    ← integral_trapH_Icc, ofReal_integral_eq_lintegral_ofReal (integrableOn_trapH q)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
        fun t ht => trapH_nonneg hq ht))]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [slice_strip, preimage_univ, univ_inter, Real.volume_Icc, add_sub_cancel_left]

lemma chord_apply {q a b t : ℝ} (ht : 0 < trapH q t) {B : Set ℝ} (hB : MeasurableSet B) :
    chord q a b t B =
      (ENNReal.ofReal (trapH q t))⁻¹ * volume (B ∩ Icc (a + b * t) (a + b * t + trapH q t)) := by
  unfold chord unifI
  rw [if_pos (by linarith), smul_apply, Measure.restrict_apply hB, smul_eq_mul,
    add_sub_cancel_left]

lemma measurable_trapDens (q : ℝ) : Measurable fun x => ENNReal.ofReal (trapDens q x) := by
  unfold trapDens trapH; fun_prop

/-- Almost every abscissa lies in `[0, 1]` and has a chord of positive length. -/
lemma ae_trapAbsc {q : ℝ} (hq : 0 ≤ q) :
    ∀ᵐ t ∂trapAbsc q, t ∈ Icc (0 : ℝ) 1 ∧ 0 < trapH q t := by
  unfold trapAbsc
  rw [ae_withDensity_iff (measurable_trapDens q)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht hne
  refine ⟨ht, ?_⟩
  have : 0 < trapDens q t := by
    by_contra h; exact hne (ENNReal.ofReal_eq_zero.2 (not_lt.1 h))
  unfold trapDens at this
  exact (div_pos_iff_of_pos_right (by linarith)).1 this

/-- **Disintegration of `U(T)`** (proof of Theorem 40): if `(X, Y)` is uniform on `T`, then `X`
has the density `h / ∫₀¹ h`, and given `X = x`, `Y` is uniform on the chord `[g x, g x + h x]`:
`U(T)(A) = ∫ U[g x, g x + h x]({y : (x, y) ∈ A}) dP_X(x)` for every measurable `A`. -/
theorem unifSet_trapSet_eq {q : ℝ} (hq : 0 ≤ q) (a b : ℝ) {A : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) :
    unifSet (trapSet q a b) A = ∫⁻ t, chord q a b t (Prod.mk t ⁻¹' A) ∂trapAbsc q := by
  have hc : 0 < (q + 1) / 2 := by linarith
  rw [trapAbsc, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
      (measurable_trapDens q).aemeasurable (Filter.Eventually.of_forall fun _ => by simp)]
  have key : ∀ t ∈ Icc (0 : ℝ) 1,
      ((fun x => ENNReal.ofReal (trapDens q x)) * fun t => chord q a b t (Prod.mk t ⁻¹' A)) t =
        ENNReal.ofReal ((q + 1) / 2)⁻¹ * volume (Prod.mk t ⁻¹' (A ∩ strip q a b)) := by
    intro t ht
    simp only [Pi.mul_apply]
    rcases (trapH_nonneg hq ht).lt_or_eq with hpos | hzero
    · rw [chord_apply hpos (measurable_prodMk_left hA), slice_strip, trapDens, div_eq_mul_inv,
        ENNReal.ofReal_mul hpos.le]
      have hu : ENNReal.ofReal (trapH q t) * (ENNReal.ofReal (trapH q t))⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by simpa using hpos) ENNReal.ofReal_ne_top
      calc _ = (ENNReal.ofReal (trapH q t) * (ENNReal.ofReal (trapH q t))⁻¹) *
            (ENNReal.ofReal ((q + 1) / 2)⁻¹ *
              volume (Prod.mk t ⁻¹' A ∩ Icc (a + b * t) (a + b * t + trapH q t))) := by ring
        _ = _ := by rw [hu, one_mul]
    · rw [slice_strip, ← hzero, add_zero, Icc_self, trapDens, ← hzero, zero_div,
        ENNReal.ofReal_zero, zero_mul]
      refine (mul_eq_zero.2 (Or.inr (measure_mono_null inter_subset_right ?_))).symm
      exact Real.volume_singleton
  rw [setLIntegral_congr_fun measurableSet_Icc key, lintegral_const_mul _
      (measurable_measure_prodMk_left (hA.inter (measurableSet_strip q a b))),
    ← volume_inter_trapSet q a b hA, unifSet, smul_apply, Measure.restrict_apply hA,
    smul_eq_mul, volume_trapSet hq, ENNReal.ofReal_inv_of_pos hc]

/-! ### Lemma 1 for the chords, with a measurable choice of `k` and `s` -/

section Choice

open scoped Classical

variable {n : ℕ}

/-- The lower ends `g(x_j)` of the chords. -/
def lo (a b : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => a + b * x j

/-- The upper ends `g(x_j) + h(x_j)` of the chords. -/
def hi (q a b : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => a + b * x j + trapH q (x j)

lemma hi_sub_lo (q a b : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    hi q a b x j - lo a b x j = trapH q (x j) := by
  simp [hi, lo]

/-- The indices other than `k`, in increasing order (the enumeration `j₁, …, j_{n-1}`). -/
def others (k : Fin n) : List (Fin n) := (List.finRange n).filter (· ≠ k)

lemma others_nodup (k : Fin n) : (others k).Nodup := (List.nodup_finRange n).filter _

lemma mem_others (k j : Fin n) : j ∈ others k ↔ j ≠ k := by simp [others]

lemma others_toFinset (k : Fin n) : (others k).toFinset = Finset.univ.erase k := by
  ext j; simp [mem_others]

lemma others_length (k : Fin n) : (others k).length = n - 1 := by
  rw [← List.toFinset_card_of_nodup (others_nodup k), others_toFinset,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]

/-- `G = {j₁, …, j_s}`. -/
def partG (k : Fin n) (s : ℕ) : Finset (Fin n) := ((others k).take s).toFinset

/-- `H = {j_{s+1}, …, j_{n-1}}`. -/
def partH (k : Fin n) (s : ℕ) : Finset (Fin n) := ((others k).drop s).toFinset

lemma take_sum (k : Fin n) (s : ℕ) (f : Fin n → ℝ) :
    (((others k).take s).map f).sum = ∑ j ∈ partG k s, f j :=
  (List.sum_toFinset _ ((others_nodup k).sublist (List.take_sublist _ _))).symm

/-- The conditions of Lemma 1 on the choice `(k, s)` for the lengths `lam`: `λ_k` is a largest
length, `s ≤ n - 1`, and `s` minimises `|2 (λ_{j₁} + ⋯ + λ_{j_s}) - ∑_{j ≠ k} λ_j|`. -/
def Valid (lam : Fin n → ℝ) (k : Fin n) (s : ℕ) : Prop :=
  (∀ j, lam j ≤ lam k) ∧ s ≤ n - 1 ∧
    ∀ s' : Fin n, |2 * ∑ j ∈ partG k s, lam j - ∑ j ∈ Finset.univ.erase k, lam j| ≤
      |2 * ∑ j ∈ partG k s', lam j - ∑ j ∈ Finset.univ.erase k, lam j|

/-- The choice `c ∈ ℕ` encodes `(k, s) = (c / (n + 1), c % (n + 1))`; codes `c` with
`c / (n + 1) ≥ n` are always admitted (they are never reached when a valid choice exists). -/
def CodeOK (lam : Fin n → ℝ) (c : ℕ) : Prop :=
  if h : c / (n + 1) < n then Valid lam ⟨c / (n + 1), h⟩ (c % (n + 1)) else True

lemma exists_codeOK (lam : Fin n → ℝ) : ∃ c, CodeOK lam c :=
  ⟨(n + 1) * n, by simp [CodeOK, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]⟩

/-- The first vector of the orthonormal pair of `ℝ²` used for the triangle of Lemma 1. -/
def e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
/-- The second vector of the orthonormal pair. -/
def e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- The triangle of Lemma 1 for lengths `lam` and choice `(k, s)`: `E_k = a e₁`,
`E_G = (x - a) e₁ + y e₂`, `E_H = -(x e₁ + y e₂)`, with `a = λ_k`, `S = ∑_G λ_j`, `T = ∑_H λ_j`,
`x = (a² + T² - S²) / (2a)`, `y = √(T² - x²)`. -/
def triEk (lam : Fin n → ℝ) (k : Fin n) : EuclideanSpace ℝ (Fin 2) := lam k • e₁

/-- `x = (a² + T² - S²) / (2a)`. -/
def triX (lam : Fin n → ℝ) (k : Fin n) (s : ℕ) : ℝ :=
  (lam k ^ 2 + (∑ j ∈ partH k s, lam j) ^ 2 - (∑ j ∈ partG k s, lam j) ^ 2) / (2 * lam k)

/-- `y = √(T² - x²)`. -/
def triY (lam : Fin n → ℝ) (k : Fin n) (s : ℕ) : ℝ :=
  √((∑ j ∈ partH k s, lam j) ^ 2 - triX lam k s ^ 2)

/-- `E_G`. -/
def triEG (lam : Fin n → ℝ) (k : Fin n) (s : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  (triX lam k s - lam k) • e₁ + triY lam k s • e₂

/-- `E_H`. -/
def triEH (lam : Fin n → ℝ) (k : Fin n) (s : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  -(triX lam k s • e₁ + triY lam k s • e₂)

/-- The vector of Lemma 1 for the chords `[g(x_j), g(x_j) + h(x_j)]` and the code `c`. -/
def chordVecCode (q a b : ℝ) (c : ℕ) (x : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    Fin n → ℝ :=
  if h : c / (n + 1) < n then
    archVec (lo a b x) (hi q a b x) ⟨c / (n + 1), h⟩ (partG ⟨c / (n + 1), h⟩ (c % (n + 1)))
      (partH ⟨c / (n + 1), h⟩ (c % (n + 1)))
      (triEk (fun j => trapH q (x j)) ⟨c / (n + 1), h⟩)
      (triEG (fun j => trapH q (x j)) ⟨c / (n + 1), h⟩ (c % (n + 1)))
      (triEH (fun j => trapH q (x j)) ⟨c / (n + 1), h⟩ (c % (n + 1))) ξ
  else 0

/-- The first admissible code for the chords at abscissae `x`. -/
def chordCode (q : ℝ) (x : Fin n → ℝ) : ℕ :=
  Nat.find (exists_codeOK (fun j => trapH q (x j)))

/-- The joint mix of Lemma 1 of the chords at abscissae `x`, as a function of `ξ`. -/
def chordVec (q a b : ℝ) (x : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) : Fin n → ℝ :=
  chordVecCode q a b (chordCode q x) x ξ

lemma measurable_lam (q : ℝ) (j : Fin n) : Measurable fun x : Fin n → ℝ => trapH q (x j) :=
  (continuous_trapH q).measurable.comp (measurable_pi_apply j)

lemma measurable_archVec {α : Type*} [MeasurableSpace α] {k : Fin n} {G H : Finset (Fin n)}
    {l r : α → Fin n → ℝ}
    (hl : ∀ i, Measurable fun z => l z i) (hr : ∀ i, Measurable fun z => r z i)
    {Ek EG EH ξ : α → EuclideanSpace ℝ (Fin 2)} (hEk : Measurable Ek) (hEG : Measurable EG)
    (hEH : Measurable EH) (hξ : Measurable ξ) :
    Measurable fun z => archVec (l z) (r z) k G H (Ek z) (EG z) (EH z) (ξ z) := by
  refine measurable_pi_iff.2 fun j => ?_
  have hm : Measurable fun z => (l z j + r z j) / 2 := ((hl j).add (hr j)).div_const _
  have hsum : ∀ F : Finset (Fin n), Measurable fun z => 2 * ∑ i ∈ F, (r z i - l z i) :=
    fun F => measurable_const.mul (Finset.measurable_sum _ fun i _ => (hr i).sub (hl i))
  unfold archVec
  by_cases h1 : j = k
  · simp only [if_pos h1]
    exact hm.add (measurable_const.mul (hEk.inner hξ))
  · by_cases h2 : j ∈ G
    · simp only [if_neg h1, if_pos h2]
      exact hm.add ((((hr j).sub (hl j)).div (hsum G)).mul (hEG.inner hξ))
    · simp only [if_neg h1, if_neg h2]
      exact hm.add ((((hr j).sub (hl j)).div (hsum H)).mul (hEH.inner hξ))

lemma measurable_valid (q : ℝ) (k : Fin n) (s : ℕ) :
    Measurable fun x : Fin n → ℝ => Valid (fun j => trapH q (x j)) k s := by
  unfold Valid
  refine Measurable.and (Measurable.forall fun j => ?_) (Measurable.and measurable_const
    (Measurable.forall fun s' => ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_le (measurable_lam q j) (measurable_lam q k))
  · refine measurableSet_setOfPred.1 (measurableSet_le ?_ ?_)
    · exact ((measurable_const.mul (Finset.measurable_sum _ fun j _ => measurable_lam q j)).sub
        (Finset.measurable_sum _ fun j _ => measurable_lam q j)).abs
    · exact ((measurable_const.mul (Finset.measurable_sum _ fun j _ => measurable_lam q j)).sub
        (Finset.measurable_sum _ fun j _ => measurable_lam q j)).abs

lemma measurableSet_codeOK (q : ℝ) (c : ℕ) :
    MeasurableSet {x : Fin n → ℝ | CodeOK (fun j => trapH q (x j)) c} := by
  unfold CodeOK
  by_cases h : c / (n + 1) < n
  · simp only [h, dite_true]; exact measurableSet_setOfPred.2 (measurable_valid q _ _)
  · simp [h]

lemma measurable_chordCode (q : ℝ) : Measurable (chordCode (n := n) q) := by
  unfold chordCode
  exact measurable_find (fun x => exists_codeOK _) (measurableSet_codeOK q)

lemma measurable_triX (q : ℝ) (k : Fin n) (s : ℕ) :
    Measurable fun x : Fin n → ℝ => triX (fun j => trapH q (x j)) k s := by
  unfold triX
  have hk := measurable_lam q k
  have hH := Finset.measurable_sum (partH k s) fun j _ => measurable_lam q j
  have hG := Finset.measurable_sum (partG k s) fun j _ => measurable_lam q j
  exact (((hk.pow_const 2).add (hH.pow_const 2)).sub (hG.pow_const 2)).div
    (measurable_const.mul hk)

lemma measurable_triY (q : ℝ) (k : Fin n) (s : ℕ) :
    Measurable fun x : Fin n → ℝ => triY (fun j => trapH q (x j)) k s := by
  unfold triY
  exact (((Finset.measurable_sum (partH k s) fun j _ => measurable_lam q j).pow_const 2).sub
    ((measurable_triX q k s).pow_const 2)).sqrt

lemma measurable_chordVecCode (q a b : ℝ) (c : ℕ) :
    Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) => chordVecCode q a b c z.1 z.2 := by
  unfold chordVecCode
  by_cases h : c / (n + 1) < n
  · simp only [h, dite_true]
    set k : Fin n := ⟨c / (n + 1), h⟩
    set s := c % (n + 1)
    have hEk : Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) =>
        triEk (fun j => trapH q (z.1 j)) k :=
      ((measurable_lam q k).comp measurable_fst).smul_const _
    have hEG : Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) =>
        triEG (fun j => trapH q (z.1 j)) k s :=
      ((((measurable_triX q k s).sub (measurable_lam q k)).comp measurable_fst).smul_const _).add
        (((measurable_triY q k s).comp measurable_fst).smul_const _)
    have hEH : Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) =>
        triEH (fun j => trapH q (z.1 j)) k s :=
      ((((measurable_triX q k s).comp measurable_fst).smul_const _).add
        (((measurable_triY q k s).comp measurable_fst).smul_const _)).neg
    exact measurable_archVec
      (fun i => (((measurable_pi_apply i).comp measurable_fst).const_mul _).const_add _)
      (fun i => ((((measurable_pi_apply i).comp measurable_fst).const_mul _).const_add _).add
        ((continuous_trapH q).measurable.comp ((measurable_pi_apply i).comp measurable_fst)))
      hEk hEG hEH measurable_snd
  · simp only [h, dite_false]; exact measurable_const

/-- The joint mix of Lemma 1 depends measurably on the abscissae and on `ξ`. -/
lemma measurable_chordVec (q a b : ℝ) :
    Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) => chordVec q a b z.1 z.2 := by
  have hF : Measurable fun w : ((Fin n → ℝ) × EuclideanSpace ℝ (Fin 2)) × ℕ =>
      chordVecCode q a b w.2 w.1.1 w.1.2 :=
    measurable_from_prod_countable_left fun c => measurable_chordVecCode q a b c
  exact hF.comp (measurable_id.prodMk ((measurable_chordCode q).comp measurable_fst))

/-- The hypotheses of Lemma 1 on the lengths: nonnegative, not all zero, polygon inequality. -/
def LemOneHyp (lam : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ (∃ j, 0 < lam j) ∧ ∀ j, 2 * lam j ≤ ∑ i, lam i

/-- Lemma 1 for the chords at abscissae `x`, for a valid choice `(k, s)`. -/
theorem arch_chords (q a b : ℝ) (x : Fin n → ℝ) (hx : LemOneHyp fun j => trapH q (x j))
    (k : Fin n) (s : ℕ) (hv : Valid (fun j => trapH q (x j)) k s) :
    let P := archPlane.map (archVec (lo a b x) (hi q a b x) k (partG k s) (partH k s)
      (triEk (fun j => trapH q (x j)) k) (triEG (fun j => trapH q (x j)) k s)
      (triEH (fun j => trapH q (x j)) k s))
    IsJointMix (fun j => chord q a b (x j)) P ∧
      ∀ᵐ y ∂P, ∑ j, y j = 1 / 2 * ∑ j, (lo a b x j + hi q a b x j) := by
  intro P
  obtain ⟨h0, ⟨j0, hj0⟩, hpoly⟩ := hx
  obtain ⟨hk, hs, hmin⟩ := hv
  set lam : Fin n → ℝ := fun j => trapH q (x j) with hlam
  have hsl : ∀ j, hi q a b x j - lo a b x j = lam j := hi_sub_lo q a b x
  have hlen : (others k).length = n - 1 := others_length k
  have hkpos : 0 < lam k := lt_of_lt_of_le hj0 (hk j0)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h => (h ▸ k).elim0)
  obtain ⟨h1, h2, -⟩ := lem_arch isArchimedesMeasure_archPlane orthonormal_single_two.1
    orthonormal_single_two.2.1 orthonormal_single_two.2.2 (lo a b x) (hi q a b x)
    (fun j => by rw [← sub_nonneg, hsl]; exact h0 j) ⟨j0, by rw [← sub_pos, hsl]; exact hj0⟩
    (fun j => by simp only [hsl]; exact hpoly j) k (fun j => by simp only [hsl]; exact hk j)
    (others k) (others_nodup k) (mem_others k) s (by rw [hlen]; exact hs)
    (fun s' hs' => by
      simp only [hsl, take_sum]
      have : s' < n := by rw [hlen] at hs'; omega
      exact hmin ⟨s', this⟩)
  simp only [hsl] at h1 h2
  change |∑ j ∈ partG k s, lam j - ∑ j ∈ partH k s, lam j| ≤ lam k at h1
  change lam k ≤ ∑ j ∈ partG k s, lam j + ∑ j ∈ partH k s, lam j at h2
  obtain ⟨hEk, hEG, hEH, hsum⟩ := triangle_of_orthonormal orthonormal_single_two.1
    orthonormal_single_two.2.1 orthonormal_single_two.2.2 hkpos
    (Finset.sum_nonneg fun j _ => h0 j) (Finset.sum_nonneg fun j _ => h0 j) h1 h2
  have hdisj := List.disjoint_take_drop (others_nodup k) (le_refl s)
  refine arch_of_partition isArchimedesMeasure_archPlane (lo a b x) (hi q a b x)
    (fun j => by rw [← sub_nonneg, hsl]; exact h0 j) k (partG k s) (partH k s) ?_ ?_ ?_ ?_
    _ _ _ (by rw [hsl]; exact hEk) (by simp only [hsl]; exact hEG) (by simp only [hsl]; exact hEH)
    hsum
  · intro h; exact (mem_others k k).1 (List.mem_of_mem_take (List.mem_toFinset.1 h)) rfl
  · intro h; exact (mem_others k k).1 (List.mem_of_mem_drop (List.mem_toFinset.1 h)) rfl
  · exact Finset.disjoint_left.2 fun j h1 h2 =>
      hdisj (List.mem_toFinset.1 h1) (List.mem_toFinset.1 h2)
  · intro j
    by_cases hj : j = k
    · exact Or.inl hj
    · right
      have : j ∈ (others k).take s ++ (others k).drop s := by
        rw [List.take_append_drop]; exact (mem_others k j).2 hj
      rcases List.mem_append.1 this with h | h
      · exact Or.inl (List.mem_toFinset.2 h)
      · exact Or.inr (List.mem_toFinset.2 h)

/-- **Lemma 1 for the chords, measurably chosen**: if the chord lengths `h(x_j)` satisfy the
hypotheses of Lemma 1, then the law of `chordVec q a b x` under the planar Archimedes measure is a
joint mix of the uniform distributions on the chords `[g(x_j), g(x_j) + h(x_j)]`, with sum
`∑ (g(x_j) + h(x_j)/2)`. -/
theorem chordVec_spec (q a b : ℝ) (x : Fin n → ℝ) (hx : LemOneHyp fun j => trapH q (x j)) :
    IsJointMix (fun j => chord q a b (x j)) (archPlane.map (chordVec q a b x)) ∧
      ∀ᵐ y ∂(archPlane.map (chordVec q a b x)),
        ∑ j, y j = 1 / 2 * ∑ j, (lo a b x j + hi q a b x j) := by
  set lam : Fin n → ℝ := fun j => trapH q (x j) with hlam
  obtain ⟨h0, ⟨j0, hj0⟩, hpoly⟩ := hx
  -- a valid code exists
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ lam ⟨j0, Finset.mem_univ _⟩
  obtain ⟨s, -, hs⟩ := Finset.exists_min_image Finset.univ
    (fun s' : Fin n => |2 * ∑ j ∈ partG k s', lam j - ∑ j ∈ Finset.univ.erase k, lam j|)
    ⟨j0, Finset.mem_univ _⟩
  have hn1 : (n + 1) * k + s < (n + 1) * n := by
    have := k.isLt; have := s.isLt
    calc (n + 1) * k + s < (n + 1) * k + (n + 1) := by omega
      _ = (n + 1) * (k + 1) := by ring
      _ ≤ (n + 1) * n := Nat.mul_le_mul_left _ (by omega)
  have hdiv : ((n + 1) * k + s) / (n + 1) = k := by
    rw [Nat.mul_add_div (Nat.succ_pos n), Nat.div_eq_of_lt (by have := s.isLt; omega),
      add_zero]
  have hmod : ((n + 1) * k + s) % (n + 1) = s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := s.isLt; omega)]
  have hok : CodeOK lam ((n + 1) * k + s) := by
    unfold CodeOK
    rw [dif_pos (by rw [hdiv]; exact k.isLt)]
    have hkk : (⟨((n + 1) * k + s) / (n + 1), by rw [hdiv]; exact k.isLt⟩ : Fin n) = k :=
      Fin.ext hdiv
    rw [hkk, hmod]
    exact ⟨fun j => hk j (Finset.mem_univ j), by have := s.isLt; omega,
      fun s' => hs s' (Finset.mem_univ s')⟩
  -- the first admissible code is a valid choice
  have hN : chordCode q x ≤ (n + 1) * k + s := Nat.find_min' _ hok
  have hlt : chordCode q x < n * (n + 1) := by rw [mul_comm n]; omega
  have hNlt : chordCode q x / (n + 1) < n := (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).2 hlt
  have hspec : CodeOK lam (chordCode q x) := Nat.find_spec (exists_codeOK lam)
  unfold CodeOK at hspec
  rw [dif_pos hNlt] at hspec
  have hvec : chordVec q a b x = archVec (lo a b x) (hi q a b x) ⟨_, hNlt⟩
      (partG ⟨_, hNlt⟩ (chordCode q x % (n + 1))) (partH ⟨_, hNlt⟩ (chordCode q x % (n + 1)))
      (triEk lam ⟨_, hNlt⟩) (triEG lam ⟨_, hNlt⟩ (chordCode q x % (n + 1)))
      (triEH lam ⟨_, hNlt⟩ (chordCode q x % (n + 1))) := by
    funext ξ; unfold chordVec chordVecCode; rw [dif_pos hNlt]
  rw [hvec]
  exact arch_chords q a b x ⟨h0, ⟨j0, hj0⟩, hpoly⟩ _ _ hspec

end Choice

/-! ### The mean of the abscissa -/

section Mean

/-- The mean of the abscissa is `c = (q + 2) / (3 (q + 1))`. -/
lemma integral_trapAbsc {q : ℝ} (hq : 0 ≤ q) :
    ∫ t, t ∂trapAbsc q = trapMean q := by
  rw [trapAbsc, integral_withDensity_eq_integral_toReal_smul (measurable_trapDens q)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hc : 0 < (q + 1) / 2 := by linarith
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun t => (2 / (q + 1)) *
      (q * t + (1 - q) * t ^ 2)) (fun t ht => by
        simp only [smul_eq_mul]
        rw [trapDens, ENNReal.toReal_ofReal (div_nonneg (trapH_nonneg hq ht) hc.le), trapH]
        field_simp),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
    integral_pow, trapMean]
  have h1 : q + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `t ↦ U[g t, g t + h t]({y : (t, y) ∈ A})` is almost everywhere measurable. -/
lemma aemeasurable_chord {q : ℝ} (hq : 0 ≤ q) (a b : ℝ) {A : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) :
    AEMeasurable (fun t => chord q a b t (Prod.mk t ⁻¹' A)) (trapAbsc q) := by
  refine ((((continuous_trapH q).measurable.ennreal_ofReal).inv).mul
    (measurable_measure_prodMk_left (ν := volume)
      (hA.inter (measurableSet_strip q a b)))).aemeasurable.congr ?_
  filter_upwards [ae_trapAbsc hq] with t ht
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [chord_apply ht.2 (measurable_prodMk_left hA), slice_strip]

end Mean

/-! ### The assembly -/

section Assemble

variable {n : ℕ}

/-- The assembled complete mix: draw the abscissae `x` from `Q` and, independently, `ξ` from the
planar Archimedes measure, and put `(Xᵢ, Yᵢ) = (xᵢ, chordVec q a b x ξ i)`. -/
def trapMix (q a b : ℝ) (Q : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ × ℝ) :=
  (Q.prod archPlane).map fun z i => (z.1 i, chordVec q a b z.1 z.2 i)

lemma measurable_trapMixMap (q a b : ℝ) :
    Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) =>
      fun i => (z.1 i, chordVec q a b z.1 z.2 i) :=
  measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp (measurable_chordVec q a b))

lemma measurable_chordVec_right (q a b : ℝ) (x : Fin n → ℝ) : Measurable (chordVec q a b x) := by
  have h : Measurable ((fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) => chordVec q a b z.1 z.2)
      ∘ Prod.mk x) := (measurable_chordVec q a b).comp measurable_prodMk_left
  exact h

instance : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1

/-- The sum of an `n`-complete mix of the abscissa is `n c`. -/
lemma sum_eq_of_isCompleteMix {q : ℝ} (hq0 : 0 ≤ q) (hn : 1 ≤ n)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCompleteMix n (trapAbsc q) Q) :
    ∀ᵐ x ∂Q, ∑ j, x j = n * trapMean q := by
  obtain ⟨hP, ⟨s, hs⟩, hm⟩ := hQ
  replace hm : ∀ j, Q.map (fun x => x j) = trapAbsc q := hm
  have hprob : IsProbabilityMeasure (trapAbsc q) := by
    rw [← hm ⟨0, hn⟩]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 hP
  have hint : Integrable (fun t : ℝ => t) (trapAbsc q) := by
    refine Integrable.of_bound measurable_id.aestronglyMeasurable 1 ?_
    filter_upwards [ae_trapAbsc hq0] with t ht
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1.1, ht.1.2]
  have hj : ∀ j, Integrable (fun x : Fin n → ℝ => x j) Q ∧ ∫ x, x j ∂Q = trapMean q := by
    intro j
    rw [← hm j] at hint
    refine ⟨(integrable_map_measure hint.aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).1 hint, ?_⟩
    rw [← integral_trapAbsc hq0, ← hm j]
    exact (integral_map (φ := fun x : Fin n → ℝ => x j) (measurable_pi_apply j).aemeasurable
      (f := fun t : ℝ => t) measurable_id.aestronglyMeasurable).symm
  have h1 : ∫ x, ∑ j, x j ∂Q = s := by
    rw [integral_congr_ae hs, integral_const, probReal_univ, one_smul]
  have h2 : ∫ x, ∑ j, x j ∂Q = n * trapMean q := by
    rw [integral_finsetSum _ fun j _ => (hj j).1]
    simp [(hj _).2]
  rw [h1] at h2
  filter_upwards [hs] with x hx
  rw [hx, h2]

/-- **Assembly of Theorem 40.** Let `0 ≤ q ≤ 1`, `n ≥ 3`, and let `Q` be an `n`-complete mix of
the abscissa distribution (density `h / ∫₀¹ h` on `[0, 1]`). Then `trapMix q a b Q`, obtained by
mixing the uniform distributions on the chords at the abscissae by Lemma 1 (with a measurable
choice of the partition), is an `n`-complete mix of the uniform distribution on the trapezoid `T`
in normal form. -/
theorem trapMix_isCompleteMix {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hn : 3 ≤ n) (a b : ℝ)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCompleteMix n (trapAbsc q) Q) :
    IsCompleteMix n (unifSet (trapSet q a b)) (trapMix q a b Q) := by
  have hsum := sum_eq_of_isCompleteMix hq0 (by omega) hQ
  obtain ⟨hP, -, hm⟩ := hQ
  replace hm : ∀ j, Q.map (fun x => x j) = trapAbsc q := hm
  -- almost every tuple of abscissae lies in `[0, 1]ⁿ` with positive chords
  have hgood : ∀ᵐ x ∂Q, ∀ j, x j ∈ Icc (0 : ℝ) 1 ∧ 0 < trapH q (x j) := by
    rw [ae_all_iff]; intro j
    have := ae_trapAbsc (q := q) hq0
    rw [← hm j] at this
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable this
  have hlem : ∀ᵐ x ∂Q, (∑ j, x j = n * trapMean q) ∧ LemOneHyp fun j => trapH q (x j) := by
    filter_upwards [hsum, hgood] with x hx hg
    exact ⟨hx, fun j => (hg j).2.le, ⟨⟨0, by omega⟩, (hg _).2⟩,
      trap_polygon hq0 hq1 hn x (fun j => (hg j).1) hx⟩
  have hF := measurable_trapMixMap (n := n) q a b
  set s0 : ℝ × ℝ := (n * trapMean q, n * (a + q / 2) + (b + (1 - q) / 2) * (n * trapMean q))
    with hs0
  refine ⟨(Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance, ⟨s0, ?_⟩,
    fun i => ?_⟩
  · -- the sum is constant
    have hS : MeasurableSet {z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) |
        ∑ j, (z.1 j, chordVec q a b z.1 z.2 j) = s0} := hF (measurableSet_sum_eq' s0)
    rw [trapMix, ae_map_iff hF.aemeasurable (measurableSet_sum_eq' s0)]
    refine (Measure.ae_prod_iff_ae_ae hS).2 ?_
    filter_upwards [hlem] with x hx
    have h2 := (chordVec_spec q a b x hx.2).2
    have hmeas := measurable_chordVec_right (n := n) q a b x
    filter_upwards [ae_of_ae_map hmeas.aemeasurable h2] with ξ hξ
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; exact hx.1
    · rw [Prod.snd_sum]
      simp only at hξ ⊢
      rw [hξ, Finset.mul_sum]
      have : ∀ j, 1 / 2 * (lo a b x j + hi q a b x j) = (a + q / 2) + (b + (1 - q) / 2) * x j :=
        fun j => by simp only [lo, hi, trapH]; ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hx.1, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs0]
      ring
  · -- every point is uniform on `T`
    ext A hA
    have hFi : Measurable fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) =>
        (z.1 i, chordVec q a b z.1 z.2 i) := (measurable_pi_apply i).comp hF
    show _ = unifSet (trapSet q a b) A
    have hcomp : ((fun f : Fin n → ℝ × ℝ => f i) ∘
        fun z : (Fin n → ℝ) × EuclideanSpace ℝ (Fin 2) =>
          fun i => (z.1 i, chordVec q a b z.1 z.2 i))
        = fun z => (z.1 i, chordVec q a b z.1 z.2 i) := rfl
    rw [trapMix, Measure.map_map (measurable_pi_apply i) hF, hcomp, Measure.map_apply hFi hA,
      Measure.prod_apply (hFi hA), unifSet_trapSet_eq hq0 a b hA, ← hm i,
      lintegral_map' (by rw [hm i]; exact aemeasurable_chord hq0 a b hA)
        (measurable_pi_apply i).aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hlem] with x hx
    have hmeas' := measurable_chordVec_right (n := n) q a b x
    have hmeas : Measurable fun ξ => chordVec (n := n) q a b x ξ i :=
      (measurable_pi_apply i).comp hmeas'
    have h1 : archPlane.map (fun ξ => chordVec q a b x ξ i) = chord q a b (x i) := by
      have := (chordVec_spec q a b x hx.2).1.2.2 i
      rw [Measure.map_map (measurable_pi_apply i) hmeas'] at this
      exact this
    rw [← h1, Measure.map_apply hmeas (measurable_prodMk_left hA)]
    rfl

/-- **Theorem 40 in normal form**, given the complete mix of the abscissa: if the abscissa
distribution is `n`-completely mixable (Theorem 12, or the theorem of Wang and Wang (2011) for
monotone densities), then `U(T)` is `n`-completely mixable, for every `n ≥ 3`. -/
theorem completelyMixable_trapSet {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hn : 3 ≤ n) (a b : ℝ)
    (habs : CompletelyMixable n (trapAbsc q)) :
    CompletelyMixable n (unifSet (trapSet q a b)) := by
  obtain ⟨Q, hQ⟩ := habs
  exact ⟨_, trapMix_isCompleteMix hq0 hq1 hn a b hQ⟩

end Assemble

/-! ### Reduction of every trapezoid and triangle to the normal form -/

section Affine

/-- The normal form with `g = 0` is the convex hull of its vertices `(0, 0)`, `(0, q)`, `(1, 0)`,
`(1, 1)`. -/
theorem trapSet_eq_convexHull {q : ℝ} (hq0 : 0 ≤ q) :
    trapSet q 0 0 = convexHull ℝ {((0 : ℝ), (0 : ℝ)), (0, q), (1, 0), (1, 1)} := by
  apply Subset.antisymm
  · rintro ⟨x, y⟩ ⟨hx0, hx1, hy0, hy1⟩
    simp only [zero_add, zero_mul] at hy0 hy1
    set K := convexHull ℝ {((0 : ℝ), (0 : ℝ)), (0, q), (1, 0), (1, 1)}
    have hK : Convex ℝ K := convex_convexHull ℝ _
    have hmem : ∀ p ∈ ({((0 : ℝ), (0 : ℝ)), (0, q), (1, 0), (1, 1)} : Set (ℝ × ℝ)), p ∈ K :=
      fun p hp => subset_convexHull ℝ _ hp
    rcases (trapH_nonneg hq0 ⟨hx0, hx1⟩).lt_or_eq with hpos | hzero
    · set t := y / trapH q x
      have ht0 : 0 ≤ t := div_nonneg hy0 hpos.le
      have ht1 : t ≤ 1 := (div_le_one hpos).2 hy1
      have hA : (1 - t) • ((0 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), q) ∈ K :=
        hK (hmem _ (by simp)) (hmem _ (by simp)) (by linarith) ht0 (by ring)
      have hB : (1 - t) • ((1 : ℝ), (0 : ℝ)) + t • ((1 : ℝ), (1 : ℝ)) ∈ K :=
        hK (hmem _ (by simp)) (hmem _ (by simp)) (by linarith) ht0 (by ring)
      have := hK hA hB (by linarith : (0 : ℝ) ≤ 1 - x) hx0 (by ring)
      convert this using 1
      have hty : t * trapH q x = y := div_mul_cancel₀ y hpos.ne'
      ext
      · simp
      · simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk, mul_zero, zero_add, mul_one]
        rw [← hty]; unfold trapH; ring
    · have hx : x = 0 := by unfold trapH at hzero; nlinarith
      subst hx
      have hy : y = 0 := by linarith [hzero ▸ hy1]
      subst hy
      exact hmem _ (by simp)
  · refine convexHull_min ?_ ?_
    · intro p hp
      simp only [mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [trapSet, trapH, hq0]
    · rintro ⟨x₁, y₁⟩ ⟨h1, h2, h3, h4⟩ ⟨x₂, y₂⟩ ⟨h5, h6, h7, h8⟩ s t hs ht hst
      simp only [trapSet, trapH, zero_add, zero_mul, Prod.smul_mk, Prod.mk_add_mk,
        smul_eq_mul, mem_setOf_eq] at *
      refine ⟨by positivity, by nlinarith, by positivity, by nlinarith⟩

/-- The linear part `(x, y) ↦ x u + y w`. -/
def linPair (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

lemma linPair_apply (u w p : ℝ × ℝ) : linPair u w p = p.1 • u + p.2 • w := rfl

lemma det_linPair_ne_zero {u w : ℝ × ℝ} (h : LinearIndependent ℝ ![u, w]) :
    LinearMap.det (linPair u w) ≠ 0 := by
  have hker : LinearMap.ker (linPair u w) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy⟩ := LinearIndependent.pair_iff.1 h x y hp
    simp [hx, hy]
  exact ((LinearMap.isUnit_iff_isUnit_det _).1
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)).ne_zero

/-- The affine map `(x, y) ↦ P + x u + y w`. -/
def affPair (u w P : ℝ × ℝ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun p := linPair u w p + P
  linear := linPair u w
  map_vadd' p v := by simp only [vadd_eq_add, map_add]; abel

variable {n : ℕ}

/-- **Theorem 40** (`t:thm:trap`), with the complete mix of the abscissa as a hypothesis. Every
trapezoid, i.e. a convex quadrilateral `conv {P, P + m v, R, R + M v}` with parallel sides
`[P, P + m v]` and `[R, R + M v]`, `0 < m ≤ M` (with `R - P` and `v` independent), and every
triangle (`m = 0`), has an `n`-completely mixable uniform distribution for every `n ≥ 3`,
provided that the abscissa distributions `trapAbsc q` (`0 ≤ q ≤ 1`) are `n`-completely mixable.
`completelyMixable_trapAbsc` discharges this hypothesis (Theorem 12 via Corollary 13), giving
`completelyMixable_trapezoid'`. -/
theorem completelyMixable_trapezoid (hn : 3 ≤ n)
    (habs : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → CompletelyMixable n (trapAbsc q))
    (P R v : ℝ × ℝ) (hind : LinearIndependent ℝ ![R - P, v]) {m M : ℝ} (hm : 0 ≤ m)
    (hmM : m ≤ M) (hM : 0 < M) :
    CompletelyMixable n (unifSet (convexHull ℝ {P, P + m • v, R, R + M • v})) := by
  set q := m / M
  have hq0 : 0 ≤ q := div_nonneg hm hM.le
  have hq1 : q ≤ 1 := (div_le_one hM).2 hmM
  obtain ⟨Q, hQ⟩ := completelyMixable_trapSet hq0 hq1 hn 0 0 (habs q hq0 hq1)
  have hind' : LinearIndependent ℝ ![R - P, M • v] := by
    rw [LinearIndependent.pair_iff] at hind ⊢
    intro s t hst
    obtain ⟨h1, h2⟩ := hind s (t * M) (by rw [mul_smul]; exact hst)
    exact ⟨h1, (mul_eq_zero.1 h2).resolve_right hM.ne'⟩
  set L := linPair (R - P) (M • v)
  have hmix := IsJointMix.map_add_hom hQ L.toAddMonoidHom
    L.continuous_of_finiteDimensional.measurable
    (fun _ => P)
  have himg : (fun x => L x + P) '' trapSet q 0 0 = convexHull ℝ {P, P + m • v, R, R + M • v} := by
    rw [trapSet_eq_convexHull hq0]
    have := (affPair (R - P) (M • v) P).image_convexHull
      {((0 : ℝ), (0 : ℝ)), (0, q), (1, 0), (1, 1)}
    refine this.trans ?_
    congr 1
    have hqM : q * M = m := div_mul_cancel₀ m hM.ne'
    simp only [image_insert_eq, image_singleton]
    change ({linPair (R - P) (M • v) (0, 0) + P, linPair (R - P) (M • v) (0, q) + P,
      linPair (R - P) (M • v) (1, 0) + P, linPair (R - P) (M • v) (1, 1) + P} : Set (ℝ × ℝ)) = _
    simp only [linPair_apply, zero_smul, one_smul, zero_add, smul_smul, hqM, zero_mul,
      one_mul, add_zero]
    have e1 : m • v + P = P + m • v := add_comm _ _
    have e2 : R - P + P = R := sub_add_cancel R P
    have e3 : R - P + M • v + P = R + M • v := by abel
    rw [e1, e2, e3]
  have hfun : (fun x : ℝ × ℝ => P + L.toAddMonoidHom x) = fun x => L x + P := by
    funext x; simp [add_comm]
  have hmap : (unifSet (trapSet q 0 0)).map (fun x => P + L.toAddMonoidHom x) =
      unifSet (convexHull ℝ {P, P + m • v, R, R + M • v}) := by
    rw [hfun, unifSet_map_affine _ (det_linPair_ne_zero hind'), himg]
  simp only [hmap] at hmix
  exact ⟨_, hmix⟩

end Affine

/-! ### The complete mix of the abscissa (Corollary 13) and the unconditional Theorem 40 -/

section Unconditional

/-- The density of the abscissa on `(-∞, 1)`: `h / ∫₀¹ h` on `(0, 1)`, and `0` on `(-∞, 0]`. -/
def absDens (q x : ℝ) : ℝ := if 0 < x then trapDens q x else 0

lemma trapDens_nonneg {q x : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hx : 0 ≤ x) : 0 ≤ trapDens q x := by
  unfold trapDens trapH
  exact div_nonneg (by nlinarith) (by linarith)

lemma measurable_absDens (q : ℝ) : Measurable fun x => ENNReal.ofReal (absDens q x) := by
  unfold absDens trapDens trapH
  exact (Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const).ennreal_ofReal

/-- The two descriptions of the abscissa law agree (they differ only at the endpoints). -/
lemma withDensity_absDens (q : ℝ) :
    (volume.restrict (Iio 1)).withDensity (fun x => ENNReal.ofReal (absDens q x)) =
      trapAbsc q := by
  ext A hA
  rw [trapAbsc, withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA,
    Measure.restrict_restrict hA]
  have h1 : (fun x => ENNReal.ofReal (absDens q x)) =
      (Ioi 0).indicator fun x => ENNReal.ofReal (trapDens q x) := by
    funext x; by_cases hx : 0 < x
    · simp [absDens, hx]
    · simp [absDens, hx]
  rw [h1, setLIntegral_indicator measurableSet_Ioi]
  have h2 : Ioi (0 : ℝ) ∩ (A ∩ Iio 1) = A ∩ Ioo 0 1 := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_Iio, mem_Ioo]; tauto
  rw [h2]
  exact setLIntegral_congr (ae_eq_set_inter Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc)

lemma trapAbsc_univ {q : ℝ} (hq : 0 ≤ q) : trapAbsc q univ = 1 := by
  have hc : 0 < (q + 1) / 2 := by linarith
  rw [trapAbsc, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [show (fun x => trapDens q x) = fun x => trapH q x / ((q + 1) / 2) from rfl,
      integral_div, integral_trapH_Icc, div_self hc.ne', ENNReal.ofReal_one]
  · exact (integrableOn_trapH q).div_const _
  · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht =>
      div_nonneg (trapH_nonneg hq ht) hc.le)

/-- **The complete mix of the abscissa** (Theorem 12 via Corollary 13): for `0 ≤ q ≤ 1` and
`n ≥ 3` the abscissa distribution `trapAbsc q` has an `n`-complete mix (with sum `n c`). -/
theorem completelyMixable_trapAbsc {n : ℕ} (hn : 3 ≤ n) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    CompletelyMixable n (trapAbsc q) := by
  have hc : 0 < (q + 1) / 2 := by linarith
  have hmono : MonotoneOn (absDens q) (Iio 1) := by
    intro x _ y _ hxy
    unfold absDens
    by_cases hx : 0 < x
    · have hy : 0 < y := lt_of_lt_of_le hx hxy
      simp only [hx, hy, if_true]
      unfold trapDens trapH
      exact div_le_div_of_nonneg_right (by nlinarith) hc.le
    · simp only [hx, if_false]
      split_ifs with hy
      · exact trapDens_nonneg hq0 hq1 hy.le
      · exact le_rfl
  have hlc : ∀ x, x < 1 → ContinuousWithinAt (absDens q) (Iic x) x := by
    intro x _
    by_cases hx : 0 < x
    · have hcont : ContinuousAt (trapDens q) x := by
        unfold trapDens trapH; fun_prop
      refine (hcont.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [absDens, mem_Ioi.1 hy]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun y hy => ?_) ?_
      · simp [absDens, not_lt.2 ((mem_Iic.1 hy).trans (not_lt.1 hx))]
      · simp [absDens, hx]
  have hα : ∀ x : ℝ, x ≤ 0 → absDens q x = 0 := fun x hx => by simp [absDens, not_lt.2 hx]
  have hM := withDensity_absDens q
  have hf1 : ∫⁻ x in Iio 1, ENNReal.ofReal (absDens q x) = 1 := by
    rw [← trapAbsc_univ hq0, ← hM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun t : ℝ => 1 - t) (trapAbsc q) := by
    have : IsFiniteMeasure (trapAbsc q) := ⟨by rw [trapAbsc_univ hq0]; exact ENNReal.one_lt_top⟩
    refine Integrable.of_bound (f := fun t : ℝ => 1 - t) (by fun_prop) 1 ?_
    filter_upwards [ae_trapAbsc hq0] with t ht
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1.1, ht.1.2]
  have hmean : ∫⁻ x in Iio 1, ENNReal.ofReal (1 - x) * ENNReal.ofReal (absDens q x) =
      ENNReal.ofReal (1 - trapMean q) := by
    have : IsProbabilityMeasure (trapAbsc q) := ⟨trapAbsc_univ hq0⟩
    have e : ∫⁻ x in Iio 1, ENNReal.ofReal (1 - x) * ENNReal.ofReal (absDens q x) =
        ∫⁻ x, ENNReal.ofReal (1 - x) ∂trapAbsc q := by
      rw [← hM, lintegral_withDensity_eq_lintegral_mul _ (measurable_absDens q)
        (by fun_prop)]
      refine lintegral_congr fun x => ?_
      simp only [Pi.mul_apply]; ring
    rw [e, ← ofReal_integral_eq_lintegral_ofReal hint, integral_sub (integrable_const _)
      ((integrable_const 1).sub hint |>.congr (Filter.Eventually.of_forall fun t => by simp)),
      integral_const, probReal_univ, one_smul, integral_trapAbsc hq0]
    filter_upwards [ae_trapAbsc hq0] with t ht
    simp only [Pi.zero_apply]; linarith [ht.1.2]
  have hcm := trapMean_mem hq0 hq1
  have hcond := (trap_meancond hq0 hq1 hn).2
  obtain ⟨Q, hQ, -⟩ := SlabsMix.cor13_nondecreasing (n := n) (f := absDens q) (α := 0) (β := 1)
    (μ := trapMean q) (by omega) hmono hlc hα hf1 hmean (by linarith [hcm.2])
    (by simpa using hcond)
  rw [hM] at hQ
  exact ⟨Q, hQ⟩

/-- **Theorem 40** (`t:thm:trap`), unconditional: the uniform distribution on every trapezoid
`conv {P, P + m v, R, R + M v}` (`0 < m ≤ M`, `R - P` and `v` linearly independent) and on every
triangle (`m = 0`) is `n`-completely mixable for every `n ≥ 3`. -/
theorem completelyMixable_trapezoid' {n : ℕ} (hn : 3 ≤ n) (P R v : ℝ × ℝ)
    (hind : LinearIndependent ℝ ![R - P, v]) {m M : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hM : 0 < M) :
    CompletelyMixable n (unifSet (convexHull ℝ {P, P + m • v, R, R + M • v})) :=
  completelyMixable_trapezoid hn (fun _ hq0 hq1 => completelyMixable_trapAbsc hn hq0 hq1)
    P R v hind hm hmM hM

end Unconditional

end Assembly

end Mixes
