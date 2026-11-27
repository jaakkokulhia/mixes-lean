import Mixes.Defs

/-!
# Monotone densities: the slab measure and the pairing of slabs (Lemmas 9, 10, Theorem 12)

Section "Monotone densities" of the paper (`m:sec:mono`).

## Representation

* A density `f` on `(0, ∞)` gives the measure `densMeas f`; it is a probability density when
  `∫⁻ x in Ioi 0, f x = 1`, and has mean `1` when `∫⁻ x in Ioi 0, x f x = 1`.
* The measure `ν` with `ν((x, ∞)) = f(x)` for `x > 0` is taken as data, with `ν((-∞, 0]) = 0`;
  `exists_nu` constructs it for non-increasing right-continuous `f`. Lemmas 9 and 10 and
  Theorem 12 only use this representation, not the monotonicity itself.
* Mixtures `∫ μ_t P(dt)` are `Measure.bind`, or (Lemma 10) identities tested on measurable sets.
* `g a b` is the two-step density of Section 5 (as in `Mixes.TwoStep`, redefined here
  so that this file does not depend on that one), `gMeas a b` its distribution.
* Theorem 12 takes as hypotheses the complete mixes provided elsewhere in the paper (Lemma 1,
  Lemma 3, Theorem 6): `Q₀` for `U[0, 2]`, and a measurable kernel `κ(a, b)` for `g_{a,b}`.
* The case `n = 2` of Theorem 12 needs no separate treatment here: `κ` is then never used,
  since `P`-almost every `(a, b)` has `2 < b ≤ B ≤ n`, which forces `P = 0`, i.e. `Δ = 0`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Mixes

namespace Slabs

/-- The distribution with density `f` on `(0, ∞)`. -/
def densMeas (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (f x))

/-- The slab measure `π(dℓ) = ℓ ν(dℓ)`. -/
def slab (ν : Measure ℝ) : Measure ℝ := ν.withDensity (fun ℓ => ENNReal.ofReal ℓ)

/-- The layer-cake identity behind Lemma 9 (Tonelli's theorem). -/
theorem layer_cake {f : ℝ → ℝ} {ν : Measure ℝ} [SFinite ν]
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ℓ, (∫⁻ x in Ioo 0 ℓ, g x) ∂ν = ∫⁻ x in Ioi 0, g x * ENNReal.ofReal (f x) := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} := by
    have h := (measurableSet_lt (measurable_const (a := (0 : ℝ))) measurable_snd).inter
      (measurableSet_lt (measurable_snd (α := ℝ) (β := ℝ)) measurable_fst)
    exact h
  set F : ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator (fun p => g p.2) with hFdef
  have hF : Measurable F := (hg.comp measurable_snd).indicator hS
  have h1 : ∀ ℓ, ∫⁻ x in Ioo 0 ℓ, g x = ∫⁻ x, F (ℓ, x) := by
    intro ℓ
    rw [← lintegral_indicator measurableSet_Ioo]
    rfl
  simp_rw [h1]
  rw [lintegral_lintegral_swap (f := fun ℓ x => F (ℓ, x)) hF.aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  congr 1; ext x
  by_cases hx : 0 < x
  · have : (fun ℓ => F (ℓ, x)) = (Ioi x).indicator (fun _ => g x) := by
      ext ℓ; simp [hFdef, Set.indicator, hx]
    rw [this, lintegral_indicator_const measurableSet_Ioi, hνf x hx,
      Set.indicator_of_mem (show x ∈ Ioi 0 from hx)]
  · have : (fun ℓ => F (ℓ, x)) = fun _ => 0 := by
      ext ℓ; simp [hFdef, hx]
    rw [this, lintegral_zero, Set.indicator_of_notMem (show x ∉ Ioi 0 from hx)]

/-- `ℓ ↦ U[0, ℓ]` is measurable, so the mixture `∫ U[0, ℓ] π(dℓ)` is a `Measure.bind`. -/
lemma measurable_unifI_zero : Measurable (fun ℓ : ℝ => unifI 0 ℓ) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hmono : Monotone (fun ℓ : ℝ => volume (s ∩ Icc 0 ℓ)) := fun a b hab =>
    measure_mono (inter_subset_inter_right _ (Icc_subset_Icc_right hab))
  have : (fun ℓ => unifI 0 ℓ s) = fun ℓ => if 0 < ℓ then
      (ENNReal.ofReal ℓ)⁻¹ * volume (s ∩ Icc 0 ℓ) else Measure.dirac (0 : ℝ) s := by
    ext ℓ; unfold unifI; split_ifs <;> simp [Measure.restrict_apply hs]
  rw [this]
  exact Measurable.ite measurableSet_Ioi
    ((ENNReal.measurable_ofReal.inv).mul hmono.measurable) measurable_const

/-- `ℓ U[0, ℓ](s) = |s ∩ (0, ℓ)|` for `ℓ > 0`. -/
lemma ofReal_mul_unifI {ℓ : ℝ} (hℓ : 0 < ℓ) {s : Set ℝ} (hs : MeasurableSet s) :
    ENNReal.ofReal ℓ * unifI 0 ℓ s = ∫⁻ x in Ioo 0 ℓ, s.indicator 1 x := by
  rw [lintegral_indicator_one hs, Measure.restrict_congr_set Ioo_ae_eq_Icc]
  unfold unifI
  rw [ite_eq_left hℓ, smul_apply, smul_eq_mul, sub_zero, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simpa using hℓ) ENNReal.ofReal_ne_top, one_mul]

lemma ae_pos_of_Iic {ν : Measure ℝ} (hν0 : ν (Iic 0) = 0) : ∀ᵐ ℓ ∂ν, 0 < ℓ := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext a; simp
  rw [this]; exact hν0

lemma lintegral_Ioo_ofReal {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫⁻ x in Ioo 0 ℓ, ENNReal.ofReal x = ENNReal.ofReal (ℓ ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ.le, integral_id]
    congr 1; ring
  · exact (continuous_id.integrableOn_Icc (a := 0) (b := ℓ)).mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun x hx => hx.1.le)

variable {f : ℝ → ℝ} {ν : Measure ℝ}

/-- The mixture identity of Lemma 9, tested on a measurable set. -/
lemma lintegral_slab_unifI [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ ℓ, unifI 0 ℓ s ∂(slab ν) = densMeas f s := by
  unfold slab
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ ENNReal.measurable_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have h1 : ∀ᵐ ℓ ∂ν, ((fun ℓ => ENNReal.ofReal ℓ) * fun ℓ => unifI 0 ℓ s) ℓ =
      ∫⁻ x in Ioo 0 ℓ, s.indicator 1 x :=
    (ae_pos_of_Iic hν0).mono fun ℓ hℓ => ofReal_mul_unifI hℓ hs
  rw [lintegral_congr_ae h1, layer_cake hνf (measurable_one.indicator hs), densMeas,
    withDensity_apply _ hs, ← lintegral_indicator hs]
  congr 1; ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The slab measure is a probability measure. -/
lemma slab_isProb [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x))
    (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1) : IsProbabilityMeasure (slab ν) := by
  constructor
  have h := lintegral_slab_unifI hν0 hνf MeasurableSet.univ
  simp_rw [fun ℓ => (unifI_isProb 0 ℓ).measure_univ, lintegral_one] at h
  rw [h, densMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hf1]

/-- The distribution with density `f` is the mixture `∫ U[0, ℓ] π(dℓ)`. -/
lemma densMeas_eq_bind [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) :
    densMeas f = (slab ν).bind (fun ℓ => unifI 0 ℓ) := by
  ext s hs
  rw [Measure.bind_apply hs measurable_unifI_zero.aemeasurable]
  exact (lintegral_slab_unifI hν0 hνf hs).symm

/-- `∫ ℓ π(dℓ)` is twice the mean of `f`. -/
lemma lintegral_slab_id [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) :
    ∫⁻ ℓ, ENNReal.ofReal ℓ ∂(slab ν) =
      2 * ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) := by
  unfold slab
  rw [lintegral_withDensity_eq_lintegral_mul _ ENNReal.measurable_ofReal
    ENNReal.measurable_ofReal]
  have h1 : ∀ᵐ ℓ ∂ν, ((fun ℓ => ENNReal.ofReal ℓ) * fun ℓ => ENNReal.ofReal ℓ) ℓ =
      2 * ∫⁻ x in Ioo 0 ℓ, ENNReal.ofReal x := by
    refine (ae_pos_of_Iic hν0).mono fun ℓ hℓ => ?_
    rw [lintegral_Ioo_ofReal hℓ, Pi.mul_apply, ← ENNReal.ofReal_mul hℓ.le,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [lintegral_congr_ae h1, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
    layer_cake hνf ENNReal.measurable_ofReal]

/-- The slab measure lives on `(0, B]`. -/
lemma slab_support (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {B : ℝ}
    (hB : ∀ x, B ≤ x → f x = 0) : slab ν (Ioc 0 B)ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  set c := max B 0
  have hsub : (Ioc 0 B)ᶜ ⊆ Iic 0 ∪ ⋃ k : ℕ, Ioi (c + 1 / (k + 1)) := by
    intro y hy
    simp only [mem_compl_iff, mem_Ioc, not_and, not_le] at hy
    by_cases hy0 : y ≤ 0
    · exact Or.inl hy0
    · right
      replace hy0 : 0 < y := lt_of_not_ge hy0
      have hyc : c < y := max_lt (hy hy0) hy0
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hyc)
      exact mem_iUnion.mpr ⟨k, by simp only [mem_Ioi]; linarith⟩
  refine measure_mono_null hsub (measure_union_null hν0 (measure_iUnion_null fun k => ?_))
  have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
  rw [hνf _ (by have := le_max_right B 0; linarith),
    hB _ (by have := le_max_left B 0; linarith), ENNReal.ofReal_zero]

/-- **Lemma 9** (`m:lem:slab`). Let `ν` be a measure on `(0, ∞)` with `ν((x, ∞)) = f(x)` for
`x > 0`, where `f` is a probability density on `(0, ∞)` vanishing on `[B, ∞)`. Then the slab
measure `π(dℓ) = ℓ ν(dℓ)` is a probability measure on `(0, B]`, the distribution with density `f`
is the mixture `∫ U[0, ℓ] π(dℓ)`, and `∫ ℓ π(dℓ)` is twice the mean of `f`. -/
theorem slab_lemma [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {B : ℝ}
    (hB : ∀ x, B ≤ x → f x = 0) (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1) :
    IsProbabilityMeasure (slab ν) ∧ slab ν (Ioc 0 B)ᶜ = 0 ∧
      densMeas f = (slab ν).bind (fun ℓ => unifI 0 ℓ) ∧
      ∫⁻ ℓ, ENNReal.ofReal ℓ ∂(slab ν) =
        2 * ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) :=
  ⟨slab_isProb hν0 hνf hf1, slab_support hν0 hνf hB, densMeas_eq_bind hν0 hνf,
    lintegral_slab_id hν0 hνf⟩

/-- The measure `ν` of the paper exists: for a non-increasing, right-continuous `f` on `(0, ∞)`
vanishing on `[B, ∞)` there is an s-finite measure `ν` on `(0, ∞)` with `ν((x, ∞)) = f(x)`.
(It is built as the image under `exp` of the Stieltjes measure of `t ↦ -f(eᵗ)`, which allows
`f` to be unbounded near `0`.) -/
theorem exists_nu {f : ℝ → ℝ} (hmono : AntitoneOn f (Ioi 0))
    (hrc : ∀ x, 0 < x → ContinuousWithinAt f (Ici x) x) {B : ℝ}
    (hB : ∀ x, B ≤ x → f x = 0) :
    ∃ ν : Measure ℝ, SFinite ν ∧ ν (Iic 0) = 0 ∧
      ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x) := by
  let G : StieltjesFunction ℝ :=
    { toFun := fun t => -f (Real.exp t)
      mono' := fun t u htu => neg_le_neg
        (hmono (Real.exp_pos t) (Real.exp_pos u) (Real.exp_le_exp.mpr htu))
      right_continuous' := fun t =>
        ((hrc _ (Real.exp_pos t)).comp Real.continuous_exp.continuousWithinAt
          (show MapsTo Real.exp (Ici t) (Ici (Real.exp t)) from
            fun u hu => Real.exp_le_exp.mpr hu)).neg }
  have hG : Filter.Tendsto G Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (Real.log (max B 1))] with t ht
    have h1 : max B 1 ≤ Real.exp t := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < max B 1)]; exact Real.exp_le_exp.mpr ht
    show (0 : ℝ) = -f (Real.exp t)
    rw [hB _ (le_trans (le_max_left _ _) h1), neg_zero]
  refine ⟨G.measure.map Real.exp, inferInstance, ?_, fun x hx => ?_⟩
  · rw [Measure.map_apply Real.measurable_exp measurableSet_Iic]
    have : Real.exp ⁻¹' Iic 0 = ∅ := by
      ext t; simp [(Real.exp_pos t).not_ge]
    rw [this, measure_empty]
  · rw [Measure.map_apply Real.measurable_exp measurableSet_Ioi]
    have : Real.exp ⁻¹' Ioi x = Ioi (Real.log x) := by
      ext t; simp [(Real.log_lt_iff_lt_exp hx).symm]
    rw [this, G.measure_Ioi hG]
    show ENNReal.ofReal (0 - -f (Real.exp (Real.log x))) = _
    rw [Real.exp_log hx, zero_sub, neg_neg]

/-! ### Lemma 10: the pairing of slabs -/

/-- `π₋`, the restriction of `π` to `(0, 2)`. -/
def piM (π : Measure ℝ) : Measure ℝ := π.restrict (Ioo 0 2)

/-- `π₊`, the restriction of `π` to `(2, ∞)`. -/
def piP (π : Measure ℝ) : Measure ℝ := π.restrict (Ioi 2)

/-- `Δ = ∫ (2 - ℓ) π₋(dℓ)`. -/
def Delta (π : Measure ℝ) : ℝ≥0∞ := ∫⁻ ℓ, ENNReal.ofReal (2 - ℓ) ∂(piM π)

/-- `U[0, ℓ]` restricted to `[0, ℓ]`, as a real density: `ℓ⁻¹` on `[0, ℓ]`. -/
def ud (ℓ : ℝ) : ℝ → ℝ := (Icc 0 ℓ).indicator (fun _ => ℓ⁻¹)

/-- `h₁ = (a + b - 2)/(a b)`. -/
def h1 (a b : ℝ) : ℝ := (a + b - 2) / (a * b)

/-- `h₂ = (2 - a)/(b (b - a))`. -/
def h2 (a b : ℝ) : ℝ := (2 - a) / (b * (b - a))

/-- The two-step density `g_{a,b}` of Section 5: `h₁` on `[0, a)`, `h₂` on `[a, b)`. -/
def g (a b : ℝ) : ℝ → ℝ := fun x => (Ico 0 a).indicator (fun _ => h1 a b) x +
  (Ico a b).indicator (fun _ => h2 a b) x

/-- The distribution with density `g_{a,b}`. -/
def gMeas (a b : ℝ) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (g a b x))

variable {π : Measure ℝ}

lemma Ioi_zero_eq_union : Ioi (0 : ℝ) = Ioo 0 2 ∪ ({2} ∪ Ioi 2) := by
  ext x
  simp only [mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]
  constructor
  · intro hx
    rcases lt_trichotomy x 2 with h | h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h) <;> [exact h.1; (subst h; norm_num); linarith]

/-- Splitting an integral against `π` at `2`. -/
lemma lintegral_split (hπ0 : π (Iic 0) = 0) (h : ℝ → ℝ≥0∞) :
    ∫⁻ ℓ, h ℓ ∂π = ∫⁻ ℓ, h ℓ ∂(piM π) + h 2 * π {2} + ∫⁻ ℓ, h ℓ ∂(piP π) := by
  have hI : π.restrict (Ioi 0) = π := Measure.restrict_eq_self_of_ae_mem (ae_pos_of_Iic hπ0)
  have hd1 : Disjoint (Ioo (0 : ℝ) 2) ({2} ∪ Ioi 2) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rcases hy with hy | hy
    · rw [mem_singleton_iff] at hy; linarith [hx.2]
    · linarith [hx.2, mem_Ioi.mp hy]
  have hd2 : Disjoint ({2} : Set ℝ) (Ioi 2) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rw [mem_singleton_iff] at hx; rw [hx, mem_Ioi] at hy; linarith
  conv_lhs => rw [← hI, Ioi_zero_eq_union]
  rw [Measure.restrict_union hd1 ((measurableSet_singleton 2).union measurableSet_Ioi),
    Measure.restrict_union hd2 measurableSet_Ioi, lintegral_add_measure, lintegral_add_measure,
    lintegral_singleton, add_assoc]
  rfl

/-- The first identity of Lemma 10, `Δ = ∫ (ℓ - 2) π₊(dℓ)`, and the bound `Δ ≤ 2`. -/
lemma delta_eq [IsProbabilityMeasure π] (hπ0 : π (Iic 0) = 0)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = 2) :
    Delta π = ∫⁻ ℓ, ENNReal.ofReal (ℓ - 2) ∂(piP π) ∧ Delta π ≤ 2 := by
  set A := ∫⁻ ℓ, ENNReal.ofReal ℓ ∂(piM π)
  set Dp := ∫⁻ ℓ, ENNReal.ofReal (ℓ - 2) ∂(piP π)
  have hA : A + Delta π = 2 * piM π univ := by
    rw [Delta, ← lintegral_add_left ENNReal.measurable_ofReal, ← lintegral_const, piM,
      setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => (2 : ℝ≥0∞))]
    intro x hx
    show ENNReal.ofReal x + ENNReal.ofReal (2 - x) = 2
    rw [← ENNReal.ofReal_add hx.1.le (by linarith [hx.2]), add_sub_cancel, ENNReal.ofReal_ofNat]
  have hB : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂(piP π) = 2 * piP π univ + Dp := by
    rw [← lintegral_const, ← lintegral_add_left measurable_const, piP,
      setLIntegral_congr_fun measurableSet_Ioi (g := fun x => 2 + ENNReal.ofReal (x - 2))]
    intro x hx
    show ENNReal.ofReal x = 2 + ENNReal.ofReal (x - 2)
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_add (by norm_num) (by linarith [mem_Ioi.mp hx]),
      add_sub_cancel]
  have h2 := lintegral_split hπ0 (fun ℓ => ENNReal.ofReal ℓ)
  have h1 := lintegral_split hπ0 (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, measure_univ, one_mul] at h1
  rw [hmean, hB, ENNReal.ofReal_ofNat] at h2
  set X := A + 2 * π {2} + 2 * piP π univ
  have hX1 : X + Dp = 2 := by rw [h2]; ring
  have hX2 : X + Delta π = 2 := by
    calc X + Delta π = (A + Delta π) + 2 * π {2} + 2 * piP π univ := by ring
      _ = 2 * (piM π univ + π {2} + piP π univ) := by rw [hA]; ring
      _ = 2 := by rw [← h1, mul_one]
  have hXt : X ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top (hX1 ▸ le_self_add)
  refine ⟨((ENNReal.add_right_inj hXt).mp (hX2.trans hX1.symm)), ?_⟩
  rw [← hX2]; exact le_add_self

lemma eq_zero_of_delta_eq_zero [IsProbabilityMeasure π] (hπ0 : π (Iic 0) = 0)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = 2) (hΔ : Delta π = 0) : piM π = 0 ∧ piP π = 0 := by
  obtain ⟨hDp, -⟩ := delta_eq hπ0 hmean
  have hm := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
    (measurable_const.sub measurable_id))).mp hΔ
  rw [hDp] at hΔ
  have hp := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
    (measurable_id.sub measurable_const))).mp hΔ
  constructor
  · have : ∀ᵐ ℓ ∂(piM π), False := by
      filter_upwards [hm, ae_restrict_mem measurableSet_Ioo] with ℓ h1 h2
      simp only [Function.comp_apply, Pi.zero_apply, Pi.sub_apply, id_eq,
        ENNReal.ofReal_eq_zero] at h1
      linarith [h2.2]
    rwa [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
  · have : ∀ᵐ ℓ ∂(piP π), False := by
      filter_upwards [hp, ae_restrict_mem measurableSet_Ioi] with ℓ h1 h2
      simp only [Function.comp_apply, Pi.zero_apply, Pi.sub_apply, id_eq,
        ENNReal.ofReal_eq_zero] at h1
      linarith [mem_Ioi.mp h2]
    rwa [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this

lemma measurable_ud (ℓ : ℝ) : Measurable (ud ℓ) := measurable_const.indicator measurableSet_Icc

lemma measurable_g (a b : ℝ) : Measurable (g a b) :=
  (measurable_const.indicator measurableSet_Ico).add (measurable_const.indicator measurableSet_Ico)

lemma ud_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) : 0 ≤ ud ℓ x :=
  Set.indicator_nonneg (fun _ _ => (inv_pos.mpr hℓ).le) x

lemma unifI_eq_lintegral {ℓ : ℝ} (hℓ : 0 < ℓ) {s : Set ℝ} (hs : MeasurableSet s) :
    unifI 0 ℓ s = ∫⁻ x in s, ENNReal.ofReal (ud ℓ x) := by
  have : (fun x => ENNReal.ofReal (ud ℓ x)) =
      (Icc 0 ℓ).indicator (fun _ => ENNReal.ofReal ℓ⁻¹) := by
    ext x; by_cases hx : x ∈ Icc 0 ℓ <;> simp [ud, hx]
  rw [this, lintegral_indicator_const measurableSet_Icc, Measure.restrict_apply measurableSet_Icc,
    ENNReal.ofReal_inv_of_pos hℓ, unifI, ite_eq_left hℓ, smul_apply, smul_eq_mul, sub_zero,
    Measure.restrict_apply hs, inter_comm]

/-- The real identity behind Lemma 10: `(b - a) g_{a,b} = (b - 2) 1_{[0,a]}/a + (2 - a) 1_{[0,b]}/b`
off the two points `a`, `b`. -/
lemma g_identity {a b x : ℝ} (ha : 0 < a) (ha2 : a < 2) (hb2 : 2 < b) (hxa : x ≠ a)
    (hxb : x ≠ b) : (b - a) * g a b x = (b - 2) * ud a x + (2 - a) * ud b x := by
  have hb : 0 < b := by linarith
  have hab : b - a ≠ 0 := by linarith
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  unfold g ud h1 h2
  simp only [Set.indicator, mem_Ico, mem_Icc]
  rcases hxa.lt_or_gt with h1 | h1 <;> rcases hxb.lt_or_gt with h2 | h2 <;>
  split_ifs <;> (try simp only [not_and_or, not_le, not_lt] at *) <;> casesm* _ ∨ _, _ ∧ _ <;>
  first | (exfalso; linarith) | (field_simp; ring)

/-- `(b - a) g_{a,b} = (b - 2) U[0,a] + (2 - a) U[0,b]` as measures, tested on sets. -/
lemma gMeas_identity {a b : ℝ} (ha : 0 < a) (ha2 : a < 2) (hb2 : 2 < b) {s : Set ℝ}
    (hs : MeasurableSet s) : ENNReal.ofReal (b - a) * gMeas a b s =
      ENNReal.ofReal (b - 2) * unifI 0 a s + ENNReal.ofReal (2 - a) * unifI 0 b s := by
  have hb : 0 < b := by linarith
  have hmg : Measurable fun x => ENNReal.ofReal (g a b x) :=
    ENNReal.measurable_ofReal.comp (measurable_g a b)
  have hma : Measurable fun x => ENNReal.ofReal (ud a x) :=
    ENNReal.measurable_ofReal.comp (measurable_ud a)
  have hmb : Measurable fun x => ENNReal.ofReal (ud b x) :=
    ENNReal.measurable_ofReal.comp (measurable_ud b)
  rw [gMeas, withDensity_apply _ hs, unifI_eq_lintegral ha hs, unifI_eq_lintegral hb hs,
    ← lintegral_const_mul _ hmg, ← lintegral_const_mul _ hma, ← lintegral_const_mul _ hmb,
    ← lintegral_add_left (hma.const_mul _)]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(Set.toFinite ({a, b} : Set ℝ)).countable.ae_notMem volume] with x hx
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add
      (mul_nonneg (by linarith) (ud_nonneg ha x)) (mul_nonneg (by linarith) (ud_nonneg hb x)),
    g_identity ha ha2 hb2 hx.1 hx.2]

lemma gMeas_isProb {a b : ℝ} (ha : 0 < a) (ha2 : a < 2) (hb2 : 2 < b) :
    IsProbabilityMeasure (gMeas a b) := by
  constructor
  have h := gMeas_identity ha ha2 hb2 MeasurableSet.univ
  rw [(unifI_isProb 0 a).measure_univ, (unifI_isProb 0 b).measure_univ, mul_one, mul_one,
    ← ENNReal.ofReal_add (by linarith) (by linarith), show b - 2 + (2 - a) = b - a by ring] at h
  have hne : ENNReal.ofReal (b - a) ≠ 0 := by simp; linarith
  calc gMeas a b univ = (ENNReal.ofReal (b - a))⁻¹ * (ENNReal.ofReal (b - a) * gMeas a b univ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ = 1 := by rw [h, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top]

/-- The pairing measure `P(dℓ₁, dℓ₂) = (ℓ₂ - ℓ₁)/Δ π₋(dℓ₁) π₊(dℓ₂)`. -/
def pairMeas (π : Measure ℝ) : Measure (ℝ × ℝ) :=
  ((piM π).prod (piP π)).withDensity (fun p => ENNReal.ofReal (p.2 - p.1) / Delta π)

instance [IsFiniteMeasure π] : IsFiniteMeasure (piM π) := by unfold piM; infer_instance
instance [IsFiniteMeasure π] : IsFiniteMeasure (piP π) := by unfold piP; infer_instance

lemma ae_prod_piM_piP [IsFiniteMeasure π] :
    ∀ᵐ p ∂((piM π).prod (piP π)), p ∈ Ioo (0 : ℝ) 2 ×ˢ Ioi 2 := by
  rw [piM, piP, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioi)

lemma ae_pairMeas [IsFiniteMeasure π] : ∀ᵐ p ∂(pairMeas π), p ∈ Ioo (0 : ℝ) 2 ×ˢ Ioi 2 :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_prod_piM_piP

lemma measurable_unifI_apply {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable fun ℓ => unifI 0 ℓ s := (Measure.measurable_coe hs).comp measurable_unifI_zero

lemma lintegral_pairMeas [IsProbabilityMeasure π] (hπ0 : π (Iic 0) = 0)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = 2) (hΔ : Delta π ≠ 0) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫⁻ p, gMeas p.1 p.2 s ∂(pairMeas π) =
      ∫⁻ ℓ, unifI 0 ℓ s ∂(piM π) + ∫⁻ ℓ, unifI 0 ℓ s ∂(piP π) := by
  obtain ⟨hDp, hΔ2⟩ := delta_eq hπ0 hmean
  have hΔt : Delta π ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hΔ2
  have hU := measurable_unifI_apply hs
  have hmd : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.2 - p.1) / Delta π :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.sub measurable_fst)).div_const _
  rw [pairMeas, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmd
    (ae_of_all _ fun _ => ENNReal.div_lt_top ENNReal.ofReal_ne_top hΔ)]
  have h1 : ∀ᵐ p ∂((piM π).prod (piP π)),
      ((fun p : ℝ × ℝ => ENNReal.ofReal (p.2 - p.1) / Delta π) *
        fun p : ℝ × ℝ => gMeas p.1 p.2 s) p =
      (Delta π)⁻¹ * (unifI 0 p.1 s * ENNReal.ofReal (p.2 - 2) +
        ENNReal.ofReal (2 - p.1) * unifI 0 p.2 s) := by
    filter_upwards [ae_prod_piM_piP] with p hp
    obtain ⟨⟨h0, h2⟩, h3⟩ := hp
    rw [Pi.mul_apply, div_eq_mul_inv, mul_comm _ (Delta π)⁻¹, mul_assoc,
      gMeas_identity h0 h2 (mem_Ioi.mp h3) hs, mul_comm (ENNReal.ofReal (p.2 - 2))]
  have hm1 : Measurable fun ℓ : ℝ => ENNReal.ofReal (2 - ℓ) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)
  have hm2 : Measurable fun ℓ : ℝ => ENNReal.ofReal (ℓ - 2) :=
    ENNReal.measurable_ofReal.comp (measurable_id.sub_const _)
  have hX : Measurable fun p : ℝ × ℝ => unifI 0 p.1 s * ENNReal.ofReal (p.2 - 2) :=
    (hU.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (measurable_snd.sub_const _))
  rw [lintegral_congr_ae h1, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hΔ),
    lintegral_add_left hX,
    lintegral_prod_mul (f := fun ℓ => unifI 0 ℓ s) (g := fun ℓ => ENNReal.ofReal (ℓ - 2))
      hU.aemeasurable hm2.aemeasurable,
    lintegral_prod_mul (f := fun ℓ => ENNReal.ofReal (2 - ℓ)) (g := fun ℓ => unifI 0 ℓ s)
      hm1.aemeasurable hU.aemeasurable, ← hDp, ← Delta]
  calc (Delta π)⁻¹ * ((∫⁻ ℓ, unifI 0 ℓ s ∂(piM π)) * Delta π +
        Delta π * ∫⁻ ℓ, unifI 0 ℓ s ∂(piP π))
      = ((Delta π)⁻¹ * Delta π) * (∫⁻ ℓ, unifI 0 ℓ s ∂(piM π) + ∫⁻ ℓ, unifI 0 ℓ s ∂(piP π)) := by
        ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hΔ hΔt, one_mul]

lemma bind_unifI_isProb [IsProbabilityMeasure π] :
    IsProbabilityMeasure (π.bind (fun ℓ => unifI 0 ℓ)) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ measurable_unifI_zero.aemeasurable]
  simp_rw [fun ℓ => (unifI_isProb 0 ℓ).measure_univ, lintegral_one, measure_univ]

/-- **Lemma 10** (`m:lem:pairs`), for a probability measure `π` on `(0, ∞)` with
`∫ ℓ π(dℓ) = 2` (the slab measure of a density with mean `1`, by Lemma 9). Write
`μ = ∫ U[0, ℓ] π(dℓ)`, `π₀ = π({2})`. Then `Δ = ∫ (ℓ - 2) π₊(dℓ)`; if `Δ = 0` then `μ = U[0,2]`;
if `Δ > 0` then `μ = π₀ U[0,2] + ∬ g_{ℓ₁,ℓ₂} P(dℓ₁, dℓ₂)` (tested on measurable sets) and
`P` has total mass `1 - π₀`. -/
theorem pairs_lemma [IsProbabilityMeasure π] (hπ0 : π (Iic 0) = 0)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = 2) :
    Delta π = ∫⁻ ℓ, ENNReal.ofReal (ℓ - 2) ∂(piP π) ∧
    (Delta π = 0 → π.bind (fun ℓ => unifI 0 ℓ) = unifI 0 2) ∧
    (Delta π ≠ 0 → (∀ s, MeasurableSet s → π.bind (fun ℓ => unifI 0 ℓ) s =
        π {2} * unifI 0 2 s + ∫⁻ p, gMeas p.1 p.2 s ∂(pairMeas π)) ∧
      pairMeas π univ = 1 - π {2}) := by
  have hmix : ∀ s, MeasurableSet s → π.bind (fun ℓ => unifI 0 ℓ) s =
      ∫⁻ ℓ, unifI 0 ℓ s ∂(piM π) + unifI 0 2 s * π {2} + ∫⁻ ℓ, unifI 0 ℓ s ∂(piP π) :=
    fun s hs => by
      rw [Measure.bind_apply hs measurable_unifI_zero.aemeasurable, lintegral_split hπ0]
  have h1 := lintegral_split hπ0 (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, measure_univ, one_mul] at h1
  refine ⟨(delta_eq hπ0 hmean).1, fun hΔ => ?_, fun hΔ => ?_⟩
  · obtain ⟨hm, hp⟩ := eq_zero_of_delta_eq_zero hπ0 hmean hΔ
    rw [hm, hp] at h1
    simp only [FunLike.coe_zero, Pi.zero_apply, zero_add, add_zero] at h1
    ext s hs
    rw [hmix s hs, hm, hp, ← h1]
    simp
  · have hP : ∀ s, MeasurableSet s → π.bind (fun ℓ => unifI 0 ℓ) s =
        π {2} * unifI 0 2 s + ∫⁻ p, gMeas p.1 p.2 s ∂(pairMeas π) := fun s hs => by
      rw [hmix s hs, lintegral_pairMeas hπ0 hmean hΔ hs]; ring
    refine ⟨hP, ?_⟩
    have hu := hP univ MeasurableSet.univ
    have := bind_unifI_isProb (π := π)
    have hg : ∀ᵐ p ∂(pairMeas π), gMeas p.1 p.2 univ = 1 := by
      filter_upwards [ae_pairMeas] with p hp
      exact (gMeas_isProb hp.1.1 hp.1.2 (mem_Ioi.mp hp.2)).measure_univ
    rw [lintegral_congr_ae hg, lintegral_one, measure_univ, (unifI_isProb 0 2).measure_univ,
      mul_one] at hu
    exact ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) (by rw [hu, add_comm])

lemma ae_pairMeas_le [IsFiniteMeasure π] {B : ℝ} (hπB : π (Ioc 0 B)ᶜ = 0) :
    ∀ᵐ p ∂(pairMeas π), p.2 ≤ B := by
  refine (withDensity_absolutelyContinuous _ _).ae_le (ae_iff.mpr ?_)
  have : {p : ℝ × ℝ | ¬ p.2 ≤ B} = univ ×ˢ Ioi B := by ext p; simp
  rw [this, Measure.prod_prod]
  have : piP π (Ioi B) = 0 := by
    refine measure_mono_null (show Ioi B ⊆ (Ioc 0 B)ᶜ from
      fun x hx h => (mem_Ioi.mp hx).not_ge h.2) ?_
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hπB) zero_le
  rw [this, mul_zero]

/-- **Lemma 10** for the slab measure of a density `f` with mean `1`, combined with Lemma 9. -/
theorem pairs_lemma_density [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {B : ℝ}
    (hB : ∀ x, B ≤ x → f x = 0) (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1)
    (hmean1 : ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) = 1) :
    Delta (slab ν) = ∫⁻ ℓ, ENNReal.ofReal (ℓ - 2) ∂(piP (slab ν)) ∧
    (Delta (slab ν) = 0 → densMeas f = unifI 0 2) ∧
    (Delta (slab ν) ≠ 0 → (∀ s, MeasurableSet s → densMeas f s =
        slab ν {2} * unifI 0 2 s + ∫⁻ p, gMeas p.1 p.2 s ∂(pairMeas (slab ν))) ∧
      pairMeas (slab ν) univ = 1 - slab ν {2}) := by
  obtain ⟨hprob, -, hbind, hmean⟩ := slab_lemma hν0 hνf hB hf1
  rw [hmean1, mul_one] at hmean
  have hπ0 : slab ν (Iic 0) = 0 := withDensity_absolutelyContinuous _ _ hν0
  rw [hbind]
  exact pairs_lemma hπ0 hmean

/-! ### Theorem 12: Algorithm 11 as a mixture of tuples -/

open ProbabilityTheory in
/-- The output distribution of Algorithm 11: with probability `π({2})` an `n`-complete mix `Q₀`
of `U[0, 2]`, and otherwise, for `(a, b)` drawn from the pairing measure `P`, the `n`-complete mix
`κ(a, b)` of `g_{a,b}` (Theorem 6 and Lemma 3). If `Δ = 0`, only `Q₀`. -/
def algMix {n : ℕ} (π : Measure ℝ) (Q₀ : Measure (Fin n → ℝ))
    (κ : Kernel (ℝ × ℝ) (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  if Delta π = 0 then Q₀ else π {2} • Q₀ + (pairMeas π).bind κ

lemma isProb_of_map {n : ℕ} (hn : 0 < n) {Q : Measure (Fin n → ℝ)} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (h : Q.map (fun x => x ⟨0, hn⟩) = μ) : IsProbabilityMeasure Q := by
  constructor
  have := congrArg (fun m : Measure ℝ => m univ) h
  rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, preimage_univ] at this
  rw [this]; exact measure_univ

lemma densMeas_isProb (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1) :
    IsProbabilityMeasure (densMeas f) := by
  constructor
  rw [densMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hf1]

open ProbabilityTheory in
/-- **Theorem 12** (`m:thm:mono`). Let `n ≥ 2` and let `f` be a probability density on `(0, ∞)`
with mean `1`, vanishing on `[B, ∞)` with `B ≤ n`, given through `ν` with `ν((x, ∞)) = f(x)`
(`exists_nu` constructs `ν` for non-increasing right-continuous `f`). Then the output of
Algorithm 11 is an `n`-complete mix of the distribution with density `f`, with sum `n`.

Hypotheses standing for results proved elsewhere in the paper (Lemma 1, Lemma 3, Theorem 6):
`Q₀` is an `n`-complete mix of `U[0, 2]` with sum `n`, and `κ` is a (measurable) kernel giving,
for `0 < a < 2 < b ≤ n`, an `n`-complete mix of `g_{a,b}` with sum `n`. -/
theorem mono_mix {n : ℕ} (hn : 2 ≤ n) [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {B : ℝ} (hBn : B ≤ n)
    (hB : ∀ x, B ≤ x → f x = 0) (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1)
    (hmean1 : ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) = 1)
    (Q₀ : Measure (Fin n → ℝ)) (hQ₀sum : ∀ᵐ x ∂Q₀, ∑ j, x j = (n : ℝ))
    (hQ₀ : ∀ j, Q₀.map (fun x => x j) = unifI 0 2)
    (κ : Kernel (ℝ × ℝ) (Fin n → ℝ))
    (hκsum : ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ n → ∀ᵐ x ∂(κ (a, b)), ∑ j, x j = (n : ℝ))
    (hκ : ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ n →
      ∀ j, (κ (a, b)).map (fun x => x j) = gMeas a b) :
    IsCompleteMix n (densMeas f) (algMix (slab ν) Q₀ κ) ∧
      ∀ᵐ x ∂(algMix (slab ν) Q₀ κ), ∑ j, x j = (n : ℝ) := by
  obtain ⟨-, hD0, hD1⟩ := pairs_lemma_density hν0 hνf hB hf1 hmean1
  obtain ⟨hprob, hsupp, -, -⟩ := slab_lemma hν0 hνf hB hf1
  have hn0 : 0 < n := by omega
  have := densMeas_isProb hf1
  suffices h : (∀ j, (algMix (slab ν) Q₀ κ).map (fun x => x j) = densMeas f) ∧
      ∀ᵐ x ∂(algMix (slab ν) Q₀ κ), ∑ j, x j = (n : ℝ) from
    ⟨⟨isProb_of_map hn0 (h.1 _), ⟨n, h.2⟩, h.1⟩, h.2⟩
  by_cases hΔ : Delta (slab ν) = 0
  · simp only [algMix, hΔ, ↓reduceIte]; rw [hD0 hΔ]; exact ⟨hQ₀, hQ₀sum⟩
  simp only [algMix, hΔ, ↓reduceIte]
  obtain ⟨hmix, -⟩ := hD1 hΔ
  have hgood : ∀ᵐ p ∂(pairMeas (slab ν)), 0 < p.1 ∧ p.1 < 2 ∧ 2 < p.2 ∧ p.2 ≤ (n : ℝ) := by
    filter_upwards [ae_pairMeas, ae_pairMeas_le hsupp] with p hp hpB
    exact ⟨hp.1.1, hp.1.2, hp.2, hpB.trans hBn⟩
  constructor
  · intro j; ext s hs
    have hjs : MeasurableSet ((fun x : Fin n → ℝ => x j) ⁻¹' s) := measurable_pi_apply j hs
    rw [Measure.map_apply (measurable_pi_apply j) hs, add_apply, smul_apply, smul_eq_mul,
      Measure.bind_apply hjs κ.measurable.aemeasurable,
      ← Measure.map_apply (measurable_pi_apply j) hs, hQ₀ j, hmix s hs]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with p hp
    have := hκ p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 j
    rw [← this, Measure.map_apply (measurable_pi_apply j) hs]
  · have hSm : MeasurableSet {x : Fin n → ℝ | ∑ j, x j = (n : ℝ)} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
        measurable_const
    rw [ae_add_measure_iff]
    refine ⟨Measure.ae_smul_measure hQ₀sum _, ae_iff.mpr ?_⟩
    rw [show {a : Fin n → ℝ | ¬ ∑ j, a j = (n : ℝ)} = {x | ∑ j, x j = (n : ℝ)}ᶜ from rfl,
      Measure.bind_apply hSm.compl κ.measurable.aemeasurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hgood] with p hp
    exact ae_iff.mp (hκsum p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)

open ProbabilityTheory in
/-- **Theorem 12** for a non-increasing, right-continuous density `f` on `(0, ∞)` (the setting of
the section): the measure `ν` is supplied by `exists_nu`. Same hypotheses `Q₀`, `κ` as in
`mono_mix`. -/
theorem mono_completelyMixable {n : ℕ} (hn : 2 ≤ n) (hmono : AntitoneOn f (Ioi 0))
    (hrc : ∀ x, 0 < x → ContinuousWithinAt f (Ici x) x) {B : ℝ} (hBn : B ≤ n)
    (hB : ∀ x, B ≤ x → f x = 0) (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1)
    (hmean1 : ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) = 1)
    (Q₀ : Measure (Fin n → ℝ)) (hQ₀sum : ∀ᵐ x ∂Q₀, ∑ j, x j = (n : ℝ))
    (hQ₀ : ∀ j, Q₀.map (fun x => x j) = unifI 0 2)
    (κ : Kernel (ℝ × ℝ) (Fin n → ℝ))
    (hκsum : ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ n → ∀ᵐ x ∂(κ (a, b)), ∑ j, x j = (n : ℝ))
    (hκ : ∀ a b : ℝ, 0 < a → a < 2 → 2 < b → b ≤ n →
      ∀ j, (κ (a, b)).map (fun x => x j) = gMeas a b) :
    ∃ Q : Measure (Fin n → ℝ), IsCompleteMix n (densMeas f) Q ∧ ∀ᵐ x ∂Q, ∑ j, x j = (n : ℝ) := by
  obtain ⟨ν, hνs, hν0, hνf⟩ := exists_nu hmono hrc hB
  exact ⟨_, mono_mix hn hν0 hνf hBn hB hf1 hmean1 Q₀ hQ₀sum hQ₀ κ hκsum hκ⟩

end Slabs

end Mixes
