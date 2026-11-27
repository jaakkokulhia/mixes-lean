import Mixes.Joint
import Mixes.Slabs

/-!
# Part II: slab measures, recognition, pairing and splitting (Lemmas 20–23)

Section "Slab measures and the pairing" (`j:sec:slabs`) and Section "Splitting the slab lengths"
(`j:sec:split`) of the paper.

* `slab_lemma`, `slab_lemma_exists`: Lemma 20 (`j:lem:slab`).
* `recog_pos`, `recog_zero`: Lemma 21 (`j:lem:recog`).
* `pairs_lemma`, `pairs_lemma_F`: Lemma 22 (`j:lem:pairs`).
* `split_lemma`: Lemma 23 (`j:lem:split`).

## Representation

* A distribution `F ∈ 𝒟(B)` (Definition 19) is given through its description in Definition 19:
  `F` is a probability measure on `[0, ∞)` whose restriction to `(0, ∞)` has the density `f`
  (`Slabs.densMeas f`), with `f` non-increasing and right-continuous on `(0, ∞)` and `f = 0` on
  `(B, ∞)` (structure `DClass`). The equivalence with a concave distribution function is not
  formalised here.
* The measure `ν` with `ν((x, ∞)) = f(x)` is taken as data in `slab_lemma` (it is automatically
  σ-finite, `sigmaFinite_nu`); `slab_lemma_exists` constructs it (`Slabs.exists_nu`).
* The slab measure is `slabMeas F ν = F({0}) δ₀ + ℓ ν(dℓ)`.
* `g^μ_{a,b}` is `gPiece μ a b` of `Mixes.Joint`; mixtures `∫ μ_t P(dt)` are
  `Measure.bind`. A piece `(a, b)` for the mean `μ` is `IsPiece μ a b`, and the distribution it
  stands for is `piece μ a b` (`U[0, 2μ]` when `a = b = 2μ`); `φ` is `phi a b`.
* Means are Bochner integrals `∫ x ∂F` in the statements of Lemmas 20 and 21; Lemma 22 for a
  general `π` takes `∫ ℓ π(dℓ) = 2μ` as a lower integral.
* Lemma 21 is split into `recog_pos` (`a > 0`: `G` has a density, constant on `(0, a)` and on
  `(a, b)`) and `recog_zero` (`a = 0`: `G = c₀ δ₀ + ` a measure with density constant on
  `(0, b)`).
* The procedure of Lemma 23 is `proc a b fuel v θ`, a recursion with a depth bound `fuel`;
  `proc_spec` shows that `fuel = n` never cuts the recursion short (every output has at most one
  inner coordinate). Outputs are a list (repetitions allowed), the mixture is the list sum.
* The right ends of the supports in Lemma 20 are compared through: for every `b ≥ 0`,
  `F((b, ∞)) = 0` iff `π((b, ∞)) = 0`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Mixes

namespace JointLemmas

/-! ### Uniform distributions: measurability and means -/

lemma unifI_zero_isProb (ℓ : ℝ) : IsProbabilityMeasure (unifI 0 ℓ) := unifI_isProb 0 ℓ

/-- `∫ x U[0, ℓ](dx) = ℓ / 2` for `ℓ ≥ 0`, as a lower integral. -/
lemma lintegral_unifI_id {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫⁻ x, ENNReal.ofReal x ∂(unifI 0 ℓ) = ENNReal.ofReal (ℓ / 2) := by
  rcases hℓ.lt_or_eq with hℓ | rfl
  · rw [unifI_of_lt hℓ, lintegral_smul_measure, smul_eq_mul, sub_zero,
      Measure.restrict_congr_set Ioo_ae_eq_Icc.symm, Slabs.lintegral_Ioo_ofReal hℓ,
      show ℓ ^ 2 / 2 = ℓ * (ℓ / 2) by ring, ENNReal.ofReal_mul hℓ.le, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using hℓ) ENNReal.ofReal_ne_top, one_mul]
  · rw [unifI_self, lintegral_dirac]; simp

lemma ae_nonneg_of_Iio {π : Measure ℝ} (hπ0 : π (Iio 0) = 0) : ∀ᵐ ℓ ∂π, 0 ≤ ℓ := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext a; simp
  rw [this]; exact hπ0

/-- The mean of a mixture `∫ U[0, ℓ] π(dℓ)` is half the mean of `π` (lower integrals). -/
lemma lintegral_bind_unifI {π : Measure ℝ} (hπ0 : π (Iio 0) = 0) :
    ∫⁻ x, ENNReal.ofReal x ∂(π.bind (fun ℓ => unifI 0 ℓ)) =
      (∫⁻ ℓ, ENNReal.ofReal ℓ ∂π) / 2 := by
  rw [Measure.lintegral_bind Slabs.measurable_unifI_zero.aemeasurable
    ENNReal.measurable_ofReal.aemeasurable, div_eq_mul_inv,
    ← lintegral_mul_const' _ _ (by simp)]
  refine lintegral_congr_ae ((ae_nonneg_of_Iio hπ0).mono fun ℓ hℓ => ?_)
  show _ = _
  simp only
  rw [lintegral_unifI_id hℓ, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat,
    div_eq_mul_inv]

/-- `π(Iio 0) = 0` and `π((b, ∞)) = 0` give `π` mass `0` outside `[0, b]`. -/
lemma compl_Icc_null {π : Measure ℝ} {b : ℝ} (h0 : π (Iio 0) = 0) (hb : π (Ioi b) = 0) :
    π (Icc 0 b)ᶜ = 0 := by
  have : (Icc 0 b)ᶜ = Iio 0 ∪ Ioi b := by
    ext x; simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [this]; exact measure_union_null h0 hb

/-- For `b ≥ 0` and `ℓ ≥ 0`: `U[0, ℓ]((b, ∞)) = 0` iff `ℓ ≤ b`. -/
lemma unifI_Ioi_eq_zero_iff {b ℓ : ℝ} (hb : 0 ≤ b) (hℓ : 0 ≤ ℓ) :
    unifI 0 ℓ (Ioi b) = 0 ↔ ℓ ≤ b := by
  rcases hℓ.lt_or_eq with hℓ | rfl
  · rw [unifI_of_lt hℓ, smul_apply, Measure.restrict_apply measurableSet_Ioi, smul_eq_mul,
      mul_eq_zero]
    simp only [ENNReal.inv_eq_zero, ENNReal.ofReal_ne_top, false_or]
    constructor
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      have : volume (Ioo b ℓ) ≤ volume (Ioi b ∩ Icc 0 ℓ) :=
        measure_mono fun x hx => ⟨hx.1, by linarith [hx.1], hx.2.le⟩
      rw [h, Real.volume_Ioo, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
      linarith
    · intro h
      have : Ioi b ∩ Icc 0 ℓ = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_empty_iff_false, iff_false]
        intro hx; linarith [hx.1, hx.2.2]
      rw [this, measure_empty]
  · simp only [unifI_self, Measure.dirac_apply' _ measurableSet_Ioi, hb]
    simp [Set.indicator, not_lt.mpr hb]

/-- For a mixture `F = ∫ U[0, ℓ] π(dℓ)` of a measure `π` on `[0, ∞)` and `b ≥ 0`:
`F((b, ∞)) = 0` iff `π((b, ∞)) = 0`. -/
lemma bind_Ioi_eq_zero_iff {π : Measure ℝ} (hπ0 : π (Iio 0) = 0) {b : ℝ} (hb : 0 ≤ b) :
    π.bind (fun ℓ => unifI 0 ℓ) (Ioi b) = 0 ↔ π (Ioi b) = 0 := by
  rw [Measure.bind_apply measurableSet_Ioi Slabs.measurable_unifI_zero.aemeasurable,
    lintegral_eq_zero_iff (Slabs.measurable_unifI_apply measurableSet_Ioi)]
  have hset : {x : ℝ | ¬ x ≤ b} = Ioi b := by ext x; simp
  constructor
  · intro h
    have : ∀ᵐ ℓ ∂π, ℓ ≤ b := by
      filter_upwards [h, ae_nonneg_of_Iio hπ0] with ℓ h1 h2
      exact (unifI_Ioi_eq_zero_iff hb h2).mp h1
    rwa [ae_iff, hset] at this
  · intro h
    have : ∀ᵐ ℓ ∂π, ℓ ≤ b := by rwa [ae_iff, hset]
    filter_upwards [this, ae_nonneg_of_Iio hπ0] with ℓ h1 h2
    exact (unifI_Ioi_eq_zero_iff hb h2).mpr h1

/-! ### Lemma 20: the slab measure -/

/-- The description of `F ∈ 𝒟(B)` in Definition 19 (`j:def:class`): `F` is a probability measure
on `[0, ∞)`, its restriction to `(0, ∞)` has the density `f`, and `f` is non-increasing and
right-continuous on `(0, ∞)` and vanishes on `(B, ∞)`; `B ≥ 0`. -/
structure DClass (B : ℝ) (F : Measure ℝ) (f : ℝ → ℝ) : Prop where
  nonneg : 0 ≤ B
  prob : IsProbabilityMeasure F
  neg : F (Iio 0) = 0
  dens : F.restrict (Ioi 0) = Slabs.densMeas f
  anti : AntitoneOn f (Ioi 0)
  rc : ∀ x, 0 < x → ContinuousWithinAt f (Ici x) x
  vanish : ∀ x, B < x → f x = 0

/-- The slab measure `π(dℓ) = F({0}) δ₀(dℓ) + ℓ ν(dℓ)`. -/
def slabMeas (F ν : Measure ℝ) : Measure ℝ := F {0} • Measure.dirac 0 + Slabs.slab ν

/-- A measure `ν` on `(0, ∞)` with finite tails `ν((x, ∞))` is σ-finite. -/
lemma sigmaFinite_nu {f : ℝ → ℝ} {ν : Measure ℝ} (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) : SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable (S := insert (Iic 0)
    (range fun k : ℕ => Ioi (1 / ((k : ℝ) + 1)))) ((countable_range _).insert _) ?_ ?_
  · rintro s (rfl | ⟨k, rfl⟩)
    · rw [hν0]; exact ENNReal.zero_lt_top
    · rw [hνf _ (by positivity)]; exact ENNReal.ofReal_lt_top
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ≤ 0
    · exact ⟨Iic 0, mem_insert _ _, hx⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_of_not_ge hx)
      exact ⟨_, mem_insert_of_mem _ ⟨k, rfl⟩, hk⟩

lemma decomp_F {F : Measure ℝ} (hF0 : F (Iio 0) = 0) :
    F = F {0} • Measure.dirac 0 + F.restrict (Ioi 0) := by
  have hae : ∀ᵐ x ∂F, x ∈ Ici (0 : ℝ) := ae_nonneg_of_Iio hF0
  have hd : Disjoint ({0} : Set ℝ) (Ioi 0) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rw [mem_singleton_iff] at hx; rw [hx, mem_Ioi] at hy; exact lt_irrefl _ hy
  conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hae, ← insert_Ioi,
    ← singleton_union, Measure.restrict_union hd measurableSet_Ioi,
    Measure.restrict_singleton]

lemma slab_support' {f : ℝ → ℝ} {ν : Measure ℝ} (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {B : ℝ}
    (hB : ∀ x, B < x → f x = 0) : Slabs.slab ν (Ioc 0 B)ᶜ = 0 := by
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

lemma slabMeas_Iio {F ν : Measure ℝ} (hν0 : ν (Iic 0) = 0) : slabMeas F ν (Iio 0) = 0 := by
  rw [slabMeas, add_apply, smul_apply, Measure.dirac_apply' _ measurableSet_Iio]
  have : Slabs.slab ν (Iio 0) = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_mono_null Iio_subset_Iic_self hν0)
  simp [this]

lemma bind_slabMeas {F ν : Measure ℝ} {f : ℝ → ℝ} (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) (hF0 : F (Iio 0) = 0)
    (hFf : F.restrict (Ioi 0) = Slabs.densMeas f) :
    F = (slabMeas F ν).bind (fun ℓ => unifI 0 ℓ) := by
  have := sigmaFinite_nu hν0 hνf
  ext s hs
  rw [Measure.bind_apply hs Slabs.measurable_unifI_zero.aemeasurable, slabMeas,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    Slabs.lintegral_slab_unifI hν0 hνf hs, unifI_self]
  conv_lhs => rw [decomp_F hF0, hFf]
  rfl

/-- **Lemma 20** (`j:lem:slab`). Let `F ∈ 𝒟(B)` (`B ≥ 0`): a probability measure on `[0, ∞)`
whose restriction to `(0, ∞)` has the density `f`, with `f = 0` on `(B, ∞)`; let `ν` be the
measure on `(0, ∞)` with `ν((x, ∞)) = f(x)` for `x > 0`, and let `π = F({0}) δ₀ + ℓ ν(dℓ)` be the
slab measure. Then `π` is a probability measure on `[0, B]`, `F = ∫ U[0, ℓ] π(dℓ)`, the mean of
`F` is `½ ∫ ℓ π(dℓ)`, and the right ends of the supports of `F` and of `π` coincide: for every
`b ≥ 0`, `F((b, ∞)) = 0` iff `π((b, ∞)) = 0`. (Monotonicity of `f` is not needed once `ν` is
given; it is used in `slab_lemma_exists` to construct `ν`.) -/
theorem slab_lemma {F : Measure ℝ} [IsProbabilityMeasure F] {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF0 : F (Iio 0) = 0) (hFf : F.restrict (Ioi 0) = Slabs.densMeas f)
    (hfB : ∀ x, B < x → f x = 0) {ν : Measure ℝ} (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) :
    IsProbabilityMeasure (slabMeas F ν) ∧ slabMeas F ν (Icc 0 B)ᶜ = 0 ∧
      F = (slabMeas F ν).bind (fun ℓ => unifI 0 ℓ) ∧
      ∫ x, x ∂F = (∫ ℓ, ℓ ∂(slabMeas F ν)) / 2 ∧
      ∀ b, 0 ≤ b → (F (Ioi b) = 0 ↔ slabMeas F ν (Ioi b) = 0) := by
  have hbind := bind_slabMeas hν0 hνf hF0 hFf
  have hπ0 := slabMeas_Iio (F := F) hν0
  have hprob : IsProbabilityMeasure (slabMeas F ν) := by
    constructor
    have h := congrArg (fun m : Measure ℝ => m univ) hbind
    rw [Measure.bind_apply MeasurableSet.univ Slabs.measurable_unifI_zero.aemeasurable] at h
    simp_rw [fun ℓ => (unifI_isProb 0 ℓ).measure_univ, lintegral_one, measure_univ] at h
    exact h.symm
  have hsupp : slabMeas F ν (Icc 0 B)ᶜ = 0 := by
    rw [slabMeas, add_apply, smul_apply,
      Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    have h1 : Slabs.slab ν (Icc 0 B)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr Ioc_subset_Icc_self)
        (slab_support' hν0 hνf hfB)
    have h2 : (0 : ℝ) ∉ (Icc 0 B)ᶜ := by simp [hB]
    simp [h1, h2]
  refine ⟨hprob, hsupp, hbind, ?_, fun b hb => ?_⟩
  · -- the means, via lower integrals of the nonnegative identity
    have hFB : F (Icc 0 B)ᶜ = 0 := by
      refine compl_Icc_null hF0 ?_
      have h := (bind_Ioi_eq_zero_iff hπ0 hB).mpr
        (measure_mono_null (show Ioi B ⊆ (Icc 0 B)ᶜ from
          fun x hx h => (not_le.mpr (mem_Ioi.mp hx)) h.2) hsupp)
      rwa [← hbind] at h
    have hmeanF : ∫ x, x ∂F = (∫⁻ x, ENNReal.ofReal x ∂F).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_nonneg_of_Iio hF0)
        measurable_id.aestronglyMeasurable
    have hmeanπ : ∫ ℓ, ℓ ∂(slabMeas F ν) = (∫⁻ ℓ, ENNReal.ofReal ℓ ∂(slabMeas F ν)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_nonneg_of_Iio hπ0)
        measurable_id.aestronglyMeasurable
    rw [hmeanF, hmeanπ]
    have h := lintegral_bind_unifI hπ0
    rw [← hbind] at h
    rw [h, ENNReal.toReal_div]
    rfl
  · have h := bind_Ioi_eq_zero_iff hπ0 hb
    rwa [← hbind] at h

/-- **Lemma 20** for `F ∈ 𝒟(B)` (structure `DClass`), with the measure `ν` constructed: there is
a measure `ν` on `(0, ∞)` with `ν((x, ∞)) = f(x)` for `x > 0`, and for it all statements of
`slab_lemma` hold. -/
theorem slab_lemma_exists {F : Measure ℝ} {f : ℝ → ℝ} {B : ℝ} (hD : DClass B F f) :
    ∃ ν : Measure ℝ, ν (Iic 0) = 0 ∧ (∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) ∧
      IsProbabilityMeasure (slabMeas F ν) ∧ slabMeas F ν (Icc 0 B)ᶜ = 0 ∧
      F = (slabMeas F ν).bind (fun ℓ => unifI 0 ℓ) ∧
      ∫ x, x ∂F = (∫ ℓ, ℓ ∂(slabMeas F ν)) / 2 ∧
      ∀ b, 0 ≤ b → (F (Ioi b) = 0 ↔ slabMeas F ν (Ioi b) = 0) := by
  have := hD.prob
  obtain ⟨ν, -, hν0, hνf⟩ := Slabs.exists_nu hD.anti hD.rc (B := B + 1) fun x hx =>
    hD.vanish x (by linarith)
  exact ⟨ν, hν0, hνf, slab_lemma hD.nonneg hD.neg hD.dens hD.vanish hν0 hνf⟩

/-! ### Lemma 21: recognising `g^μ_{a,b}` -/

/-- `∫ x U[a, b](dx) = (a + b)/2` for `0 ≤ a ≤ b`, as a lower integral. -/
lemma lintegral_unifI_id' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ x, ENNReal.ofReal x ∂(unifI a b) = ENNReal.ofReal ((a + b) / 2) := by
  rcases hab.lt_or_eq with hab | rfl
  · rw [unifI_of_lt hab, lintegral_smul_measure, smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, integral_id,
        show (b ^ 2 - a ^ 2) / 2 = (b - a) * ((a + b) / 2) by ring,
        ENNReal.ofReal_mul (by linarith), ← mul_assoc,
        ENNReal.inv_mul_cancel (by simpa using hab) ENNReal.ofReal_ne_top, one_mul]
    · exact continuous_id.integrableOn_Icc
    · exact (ae_restrict_iff' measurableSet_Icc).mpr
        (ae_of_all _ fun x hx => ha.trans hx.1)
  · rw [unifI_self, lintegral_dirac]; congr 1; ring

/-- `vol|(l, r) = (r - l) U[l, r]` for `l < r`. -/
lemma volume_restrict_Ioo {l r : ℝ} (h : l < r) :
    volume.restrict (Ioo l r) = ENNReal.ofReal (r - l) • unifI l r := by
  rw [unifI_of_lt h, smul_smul, ENNReal.mul_inv_cancel (by simpa using h) ENNReal.ofReal_ne_top,
    one_smul, Measure.restrict_congr_set Ioo_ae_eq_Icc]

/-- `U[0, b] = (a/b) U[0, a] + ((b - a)/b) U[a, b]` for `0 ≤ a < b`. -/
lemma unifI_split {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    unifI 0 b = ENNReal.ofReal (a / b) • unifI 0 a + ENNReal.ofReal ((b - a) / b) • unifI a b := by
  have hb : 0 < b := by linarith
  rcases ha.lt_or_eq with ha | rfl
  · rw [unifI_of_lt hb, unifI_of_lt ha, unifI_of_lt hab, smul_smul, smul_smul, sub_zero,
      sub_zero]
    have hU : volume.restrict (Icc (0 : ℝ) b) =
        volume.restrict (Icc 0 a) + volume.restrict (Icc a b) := by
      rw [← Measure.restrict_union_add_inter _ measurableSet_Icc,
        Icc_union_Icc_eq_Icc ha.le hab.le, Icc_inter_Icc_eq_singleton ha.le hab.le,
        Measure.restrict_eq_zero.mpr Real.volume_singleton, add_zero]
    rw [hU, smul_add]
    congr 2
    · rw [← ENNReal.ofReal_inv_of_pos ha, ← ENNReal.ofReal_inv_of_pos hb,
        ← ENNReal.ofReal_mul (div_nonneg ha.le hb.le)]
      congr 1; field_simp
    · rw [← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab), ← ENNReal.ofReal_inv_of_pos hb,
        ← ENNReal.ofReal_mul (div_nonneg (by linarith) hb.le)]
      congr 1; field_simp [(sub_pos.mpr hab).ne']
  · simp [unifI_self, div_self hb.ne']

/-- `g^μ_{a,b} = (1 - t) U[0, a] + t U[a, b]` with `t = (2μ - a)/b`. -/
lemma gPiece_eq_two {μ a b : ℝ} (ha : 0 ≤ a) (ha2 : a < 2 * μ) (hb : 2 * μ < b) :
    gPiece μ a b = ENNReal.ofReal (1 - (2 * μ - a) / b) • unifI 0 a +
      ENNReal.ofReal ((2 * μ - a) / b) • unifI a b := by
  have hb0 : 0 < b := by linarith
  have hba : 0 < b - a := by linarith
  rw [gPiece, unifI_split ha (by linarith : a < b), smul_add, smul_smul, smul_smul,
    ← add_assoc, ← add_smul, ← ENNReal.ofReal_mul (div_nonneg (by linarith) hba.le),
    ← ENNReal.ofReal_mul (div_nonneg (by linarith) hba.le),
    ← ENNReal.ofReal_add (div_nonneg (by linarith) hba.le)
      (mul_nonneg (div_nonneg (by linarith) hba.le) (div_nonneg ha hb0.le))]
  congr 3
  · field_simp; ring
  · field_simp

/-- The core of Lemma 21: a probability measure on `[0, b]` of the form
`α U[0, a] + β U[a, b]` with mean `μ` is `g^μ_{a,b}`. -/
lemma recog_core {G : Measure ℝ} [IsProbabilityMeasure G] {μ a b : ℝ} (ha : 0 ≤ a)
    (ha2 : a < 2 * μ) (hb : 2 * μ < b) (hsupp : G (Icc 0 b)ᶜ = 0) (hmean : ∫ x, x ∂G = μ)
    {α β : ℝ≥0∞} (hG : G = α • unifI 0 a + β • unifI a b) : G = gPiece μ a b := by
  have hab : a < b := by linarith
  have hb0 : 0 < b := by linarith
  have hmass : α + β = 1 := by
    have h := measure_univ (μ := G)
    rwa [hG, add_apply, smul_apply, smul_apply, (unifI_isProb 0 a).measure_univ,
      (unifI_isProb a b).measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h
  have hαt : α ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hmass ▸ le_self_add)
  have hβt : β ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hmass ▸ le_add_self)
  have hnn : ∀ᵐ x ∂G, 0 ≤ x := by
    have : ∀ᵐ x ∂G, x ∈ Icc 0 b := by rw [ae_iff]; exact hsupp
    exact this.mono fun x hx => hx.1
  have hlin : ∫⁻ x, ENNReal.ofReal x ∂G =
      ENNReal.ofReal (α.toReal * (a / 2) + β.toReal * ((a + b) / 2)) := by
    rw [hG, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_unifI_id ha, lintegral_unifI_id' ha hab.le, smul_eq_mul, smul_eq_mul,
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hαt, ENNReal.ofReal_toReal hβt]
  have hmean' : α.toReal * (a / 2) + β.toReal * ((a + b) / 2) = μ := by
    rw [← hmean, integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable,
      hlin, ENNReal.toReal_ofReal (by positivity)]
  have hmass' : α.toReal + β.toReal = 1 := by
    rw [← ENNReal.toReal_add hαt hβt, hmass, ENNReal.toReal_one]
  have hβ : β.toReal = (2 * μ - a) / b := by
    field_simp; linear_combination 2 * hmean' - a * hmass'
  have hα : α.toReal = 1 - (2 * μ - a) / b := by linarith
  rw [hG, gPiece_eq_two ha ha2 hb, ← hα, ← hβ, ENNReal.ofReal_toReal hαt,
    ENNReal.ofReal_toReal hβt]

lemma restrict_withDensity_const {h : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {l r : ℝ}
    (hc : ∀ x ∈ Ioo l r, h x = c) :
    (volume.withDensity h).restrict (Ioo l r) = c • volume.restrict (Ioo l r) := by
  rw [restrict_withDensity measurableSet_Ioo, ← withDensity_const]
  exact withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hc))

lemma Icc_ae_eq_Ioo_union {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Icc 0 b : Set ℝ) =ᵐ[volume] (Ioo 0 a ∪ Ioo a b : Set ℝ) := by
  have h1 : (Ioo 0 a ∪ Ioo a b : Set ℝ) = Ioo 0 b \ {a} := by
    ext x; simp only [mem_union, mem_Ioo, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact ⟨⟨h.1, by linarith [h.2]⟩, h.2.ne⟩
      · exact ⟨⟨by linarith [h.1], h.2⟩, h.1.ne'⟩
    · rintro ⟨h, hne⟩
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inl ⟨h.1, h'⟩
      · exact Or.inr ⟨h', h.2⟩
  rw [h1]
  exact Ioo_ae_eq_Icc.symm.trans (sdiff_null_ae_eq_self Real.volume_singleton).symm

/-- **Lemma 21** (`j:lem:recog`), case `a > 0`. Let `0 < a < 2μ < b`. A probability distribution
`G` on `[0, b]` with mean `μ` that has a density (with respect to Lebesgue measure) constant on
`(0, a)` and on `(a, b)` equals `g^μ_{a,b}`. -/
theorem recog_pos {G : Measure ℝ} [IsProbabilityMeasure G] {μ a b : ℝ} (ha : 0 < a)
    (ha2 : a < 2 * μ) (hb : 2 * μ < b) (hsupp : G (Icc 0 b)ᶜ = 0) (hmean : ∫ x, x ∂G = μ)
    {h : ℝ → ℝ≥0∞} (hG : G = volume.withDensity h) {c₁ c₂ : ℝ≥0∞}
    (h1 : ∀ x ∈ Ioo 0 a, h x = c₁) (h2 : ∀ x ∈ Ioo a b, h x = c₂) : G = gPiece μ a b := by
  have hab : a < b := by linarith
  refine recog_core ha.le ha2 hb hsupp hmean (α := c₁ * ENNReal.ofReal a)
    (β := c₂ * ENNReal.ofReal (b - a)) ?_
  have hac : G ≪ volume := hG ▸ withDensity_absolutelyContinuous _ _
  have hd : Disjoint (Ioo 0 a : Set ℝ) (Ioo a b) :=
    Set.disjoint_left.mpr fun x hx hy => lt_asymm hx.2 hy.1
  calc G = G.restrict (Icc 0 b) := (Measure.restrict_eq_self_of_ae_mem
          (by rw [ae_iff]; exact hsupp)).symm
    _ = G.restrict (Ioo 0 a ∪ Ioo a b) :=
          Measure.restrict_congr_set (hac.ae_le (Icc_ae_eq_Ioo_union ha hab))
    _ = _ := by
          rw [Measure.restrict_union hd measurableSet_Ioo, hG, restrict_withDensity_const h1,
            restrict_withDensity_const h2, volume_restrict_Ioo ha, volume_restrict_Ioo hab,
            smul_smul, smul_smul, sub_zero]

/-- **Lemma 21** (`j:lem:recog`), case `a = 0`. Let `0 < 2μ < b`. A probability distribution `G`
on `[0, b]` with mean `μ` that is the sum of a multiple of `δ₀` and a measure with a density
constant on `(0, b)` equals `g^μ_{0,b}`. -/
theorem recog_zero {G : Measure ℝ} [IsProbabilityMeasure G] {μ b : ℝ}
    (hμ : 0 < 2 * μ) (hb : 2 * μ < b) (hsupp : G (Icc 0 b)ᶜ = 0) (hmean : ∫ x, x ∂G = μ)
    {c₀ : ℝ≥0∞} {h : ℝ → ℝ≥0∞} (hG : G = c₀ • Measure.dirac 0 + volume.withDensity h)
    {c : ℝ≥0∞} (hc : ∀ x ∈ Ioo 0 b, h x = c) : G = gPiece μ 0 b := by
  have hb0 : 0 < b := by linarith
  refine recog_core le_rfl hμ hb hsupp hmean (α := c₀) (β := c * ENNReal.ofReal b) ?_
  have hW : volume.withDensity h (Icc 0 b)ᶜ = 0 := by
    refine le_antisymm (le_trans ?_ hsupp.le) zero_le
    rw [hG, add_apply]; exact le_add_self
  have hW' : volume.withDensity h = (c * ENNReal.ofReal b) • unifI 0 b := by
    calc volume.withDensity h = (volume.withDensity h).restrict (Icc 0 b) :=
          (Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hW)).symm
      _ = (volume.withDensity h).restrict (Ioo 0 b) :=
          Measure.restrict_congr_set ((withDensity_absolutelyContinuous _ _).ae_le
            Ioo_ae_eq_Icc.symm)
      _ = _ := by
          rw [restrict_withDensity_const hc, volume_restrict_Ioo hb0, smul_smul, sub_zero]
  rw [hG, hW', unifI_self]

/-! ### Lemma 22: the pairing of slabs -/

/-- `π₋`, the restriction of `π` to `[0, m)` (here `m = 2μ`). -/
def piMinus (m : ℝ) (π : Measure ℝ) : Measure ℝ := π.restrict (Ico 0 m)

/-- `π₊`, the restriction of `π` to `(m, ∞)`. -/
def piPlus (m : ℝ) (π : Measure ℝ) : Measure ℝ := π.restrict (Ioi m)

/-- `Δ = ∫ (m - ℓ) π₋(dℓ)`. -/
def Delta (m : ℝ) (π : Measure ℝ) : ℝ≥0∞ := ∫⁻ ℓ, ENNReal.ofReal (m - ℓ) ∂(piMinus m π)

/-- The pairing measure `P(dℓ₁, dℓ₂) = (ℓ₂ - ℓ₁)/Δ π₋(dℓ₁) π₊(dℓ₂)`. -/
def pairMeas (m : ℝ) (π : Measure ℝ) : Measure (ℝ × ℝ) :=
  ((piMinus m π).prod (piPlus m π)).withDensity
    (fun p => ENNReal.ofReal (p.2 - p.1) / Delta m π)

variable {π : Measure ℝ} {m : ℝ}

instance [IsFiniteMeasure π] : IsFiniteMeasure (piMinus m π) := by
  unfold piMinus; infer_instance
instance [IsFiniteMeasure π] : IsFiniteMeasure (piPlus m π) := by
  unfold piPlus; infer_instance

lemma Ici_zero_eq_union (hm : 0 < m) : Ici (0 : ℝ) = Ico 0 m ∪ ({m} ∪ Ioi m) := by
  ext x
  simp only [mem_Ici, mem_union, mem_Ico, mem_singleton_iff, mem_Ioi]
  constructor
  · intro hx
    rcases lt_trichotomy x m with h | h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact h.1
    · rw [h]; exact hm.le
    · linarith

/-- Splitting an integral against `π` at `m`. -/
lemma lintegral_split (hπ0 : π (Iio 0) = 0) (hm : 0 < m) (h : ℝ → ℝ≥0∞) :
    ∫⁻ ℓ, h ℓ ∂π = ∫⁻ ℓ, h ℓ ∂(piMinus m π) + h m * π {m} + ∫⁻ ℓ, h ℓ ∂(piPlus m π) := by
  have hI : π.restrict (Ici 0) = π :=
    Measure.restrict_eq_self_of_ae_mem (ae_nonneg_of_Iio hπ0)
  have hd1 : Disjoint (Ico (0 : ℝ) m) ({m} ∪ Ioi m) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rcases hy with hy | hy
    · rw [mem_singleton_iff] at hy; linarith [hx.2]
    · linarith [hx.2, mem_Ioi.mp hy]
  have hd2 : Disjoint ({m} : Set ℝ) (Ioi m) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rw [mem_singleton_iff] at hx; rw [hx, mem_Ioi] at hy; linarith
  conv_lhs => rw [← hI, Ici_zero_eq_union hm]
  rw [Measure.restrict_union hd1 ((measurableSet_singleton m).union measurableSet_Ioi),
    Measure.restrict_union hd2 measurableSet_Ioi, lintegral_add_measure, lintegral_add_measure,
    lintegral_singleton, add_assoc]
  rfl

/-- The first identity of Lemma 22, `Δ = ∫ (ℓ - m) π₊(dℓ)`, and the bound `Δ ≤ m`. -/
lemma delta_eq [IsProbabilityMeasure π] (hπ0 : π (Iio 0) = 0) (hm : 0 < m)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = ENNReal.ofReal m) :
    Delta m π = ∫⁻ ℓ, ENNReal.ofReal (ℓ - m) ∂(piPlus m π) ∧
      Delta m π ≤ ENNReal.ofReal m := by
  set M := ENNReal.ofReal m
  set A := ∫⁻ ℓ, ENNReal.ofReal ℓ ∂(piMinus m π)
  set Dp := ∫⁻ ℓ, ENNReal.ofReal (ℓ - m) ∂(piPlus m π)
  have hA : A + Delta m π = M * piMinus m π univ := by
    rw [Delta, ← lintegral_add_left ENNReal.measurable_ofReal, ← lintegral_const,
      piMinus, setLIntegral_congr_fun measurableSet_Ico (g := fun _ => M)]
    intro x hx
    show ENNReal.ofReal x + ENNReal.ofReal (m - x) = M
    rw [← ENNReal.ofReal_add hx.1 (by linarith [hx.2]), add_sub_cancel]
  have hB : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂(piPlus m π) = M * piPlus m π univ + Dp := by
    rw [← lintegral_const, ← lintegral_add_left measurable_const, piPlus,
      setLIntegral_congr_fun measurableSet_Ioi (g := fun x => M + ENNReal.ofReal (x - m))]
    intro x hx
    show ENNReal.ofReal x = M + ENNReal.ofReal (x - m)
    rw [← ENNReal.ofReal_add hm.le (by linarith [mem_Ioi.mp hx]), add_sub_cancel]
  have h2 := lintegral_split hπ0 hm (fun ℓ => ENNReal.ofReal ℓ)
  have h1 := lintegral_split hπ0 hm (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, measure_univ, one_mul] at h1
  rw [hmean, hB] at h2
  set X := A + M * π {m} + M * piPlus m π univ
  have hX1 : X + Dp = M := by rw [h2]; ring
  have hX2 : X + Delta m π = M := by
    calc X + Delta m π = (A + Delta m π) + M * π {m} + M * piPlus m π univ := by ring
      _ = M * (piMinus m π univ + π {m} + piPlus m π univ) := by rw [hA]; ring
      _ = M := by rw [← h1, mul_one]
  have hXt : X ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hX1 ▸ le_self_add)
  refine ⟨((ENNReal.add_right_inj hXt).mp (hX2.trans hX1.symm)), ?_⟩
  rw [← hX2]; exact le_add_self

lemma eq_zero_of_delta_eq_zero [IsProbabilityMeasure π] (hπ0 : π (Iio 0) = 0) (hm : 0 < m)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = ENNReal.ofReal m) (hΔ : Delta m π = 0) :
    piMinus m π = 0 ∧ piPlus m π = 0 := by
  obtain ⟨hDp, -⟩ := delta_eq hπ0 hm hmean
  have hmz := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
    (measurable_const.sub measurable_id))).mp hΔ
  rw [hDp] at hΔ
  have hp := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
    (measurable_id.sub measurable_const))).mp hΔ
  constructor
  · have : ∀ᵐ ℓ ∂(piMinus m π), False := by
      filter_upwards [hmz, ae_restrict_mem measurableSet_Ico] with ℓ h1 h2
      simp only [Function.comp_apply, Pi.zero_apply, Pi.sub_apply, id_eq,
        ENNReal.ofReal_eq_zero] at h1
      linarith [h2.2]
    rwa [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
  · have : ∀ᵐ ℓ ∂(piPlus m π), False := by
      filter_upwards [hp, ae_restrict_mem measurableSet_Ioi] with ℓ h1 h2
      simp only [Function.comp_apply, Pi.zero_apply, Pi.sub_apply, id_eq,
        ENNReal.ofReal_eq_zero] at h1
      linarith [mem_Ioi.mp h2]
    rwa [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this

/-- `(b - a) g^μ_{a,b} = (b - 2μ) U[0, a] + (2μ - a) U[0, b]`, tested on a set. -/
lemma gPiece_identity {μ a b : ℝ} (ha2 : a < 2 * μ) (hb : 2 * μ < b) (s : Set ℝ) :
    ENNReal.ofReal (b - a) * gPiece μ a b s =
      ENNReal.ofReal (b - 2 * μ) * unifI 0 a s + ENNReal.ofReal (2 * μ - a) * unifI 0 b s := by
  have hba : 0 < b - a := by linarith
  rw [gPiece, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, mul_add,
    ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hba.le, ← ENNReal.ofReal_mul hba.le,
    mul_div_cancel₀ _ hba.ne', mul_div_cancel₀ _ hba.ne']

lemma gPiece_isProb {μ a b : ℝ} (ha2 : a < 2 * μ) (hb : 2 * μ < b) :
    IsProbabilityMeasure (gPiece μ a b) := by
  have hba : 0 < b - a := by linarith
  constructor
  rw [gPiece, add_apply, smul_apply, smul_apply, (unifI_isProb 0 a).measure_univ,
    (unifI_isProb 0 b).measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add (div_nonneg (by linarith) hba.le) (div_nonneg (by linarith) hba.le),
    ← add_div, show b - 2 * μ + (2 * μ - a) = b - a by ring, div_self hba.ne',
    ENNReal.ofReal_one]

lemma measurable_gPiece_apply (μ : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable fun p : ℝ × ℝ => gPiece μ p.1 p.2 s := by
  simp only [gPiece, add_apply, smul_apply, smul_eq_mul]
  refine Measurable.add ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp ((measurable_snd.sub_const _).div
      (measurable_snd.sub measurable_fst))).mul
      ((Slabs.measurable_unifI_apply hs).comp measurable_fst)
  · exact (ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_fst).div
      (measurable_snd.sub measurable_fst))).mul
      ((Slabs.measurable_unifI_apply hs).comp measurable_snd)

lemma measurable_gPiece (μ : ℝ) : Measurable fun p : ℝ × ℝ => gPiece μ p.1 p.2 :=
  Measure.measurable_of_measurable_coe _ fun _ hs => measurable_gPiece_apply μ hs

lemma ae_prod_pm [IsFiniteMeasure π] :
    ∀ᵐ p ∂((piMinus m π).prod (piPlus m π)), p ∈ Ico (0 : ℝ) m ×ˢ Ioi m := by
  rw [piMinus, piPlus, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ico.prod measurableSet_Ioi)

lemma ae_pairMeas [IsFiniteMeasure π] : ∀ᵐ p ∂(pairMeas m π), p ∈ Ico (0 : ℝ) m ×ˢ Ioi m :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_prod_pm

lemma lintegral_pairMeas [IsProbabilityMeasure π] {μ : ℝ} (hπ0 : π (Iio 0) = 0)
    (hμ : 0 < μ) (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = ENNReal.ofReal (2 * μ))
    (hΔ : Delta (2 * μ) π ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ p, gPiece μ p.1 p.2 s ∂(pairMeas (2 * μ) π) =
      ∫⁻ ℓ, unifI 0 ℓ s ∂(piMinus (2 * μ) π) + ∫⁻ ℓ, unifI 0 ℓ s ∂(piPlus (2 * μ) π) := by
  obtain ⟨hDp, hΔ2⟩ := delta_eq hπ0 (by linarith) hmean
  set m := 2 * μ
  have hΔt : Delta m π ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΔ2
  have hU := Slabs.measurable_unifI_apply hs
  have hmd : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.2 - p.1) / Delta m π :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.sub measurable_fst)).div_const _
  rw [pairMeas, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmd
    (ae_of_all _ fun _ => ENNReal.div_lt_top ENNReal.ofReal_ne_top hΔ)]
  have h1 : ∀ᵐ p ∂((piMinus m π).prod (piPlus m π)),
      ((fun p : ℝ × ℝ => ENNReal.ofReal (p.2 - p.1) / Delta m π) *
        fun p : ℝ × ℝ => gPiece μ p.1 p.2 s) p =
      (Delta m π)⁻¹ * (unifI 0 p.1 s * ENNReal.ofReal (p.2 - m) +
        ENNReal.ofReal (m - p.1) * unifI 0 p.2 s) := by
    filter_upwards [ae_prod_pm] with p hp
    obtain ⟨⟨_, h2⟩, h3⟩ := hp
    rw [Pi.mul_apply, div_eq_mul_inv, mul_comm _ (Delta m π)⁻¹, mul_assoc,
      gPiece_identity h2 (mem_Ioi.mp h3) s, mul_comm (ENNReal.ofReal (p.2 - m))]
  have hm1 : Measurable fun ℓ : ℝ => ENNReal.ofReal (m - ℓ) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)
  have hm2 : Measurable fun ℓ : ℝ => ENNReal.ofReal (ℓ - m) :=
    ENNReal.measurable_ofReal.comp (measurable_id.sub_const _)
  have hX : Measurable fun p : ℝ × ℝ => unifI 0 p.1 s * ENNReal.ofReal (p.2 - m) :=
    (hU.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (measurable_snd.sub_const _))
  rw [lintegral_congr_ae h1, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hΔ),
    lintegral_add_left hX,
    lintegral_prod_mul (f := fun ℓ => unifI 0 ℓ s) (g := fun ℓ => ENNReal.ofReal (ℓ - m))
      hU.aemeasurable hm2.aemeasurable,
    lintegral_prod_mul (f := fun ℓ => ENNReal.ofReal (m - ℓ)) (g := fun ℓ => unifI 0 ℓ s)
      hm1.aemeasurable hU.aemeasurable, ← hDp, ← Delta]
  calc (Delta m π)⁻¹ * ((∫⁻ ℓ, unifI 0 ℓ s ∂(piMinus m π)) * Delta m π +
        Delta m π * ∫⁻ ℓ, unifI 0 ℓ s ∂(piPlus m π))
      = ((Delta m π)⁻¹ * Delta m π) *
          (∫⁻ ℓ, unifI 0 ℓ s ∂(piMinus m π) + ∫⁻ ℓ, unifI 0 ℓ s ∂(piPlus m π)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hΔ hΔt, one_mul]

lemma bind_unifI_isProb [IsProbabilityMeasure π] :
    IsProbabilityMeasure (π.bind (fun ℓ => unifI 0 ℓ)) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ Slabs.measurable_unifI_zero.aemeasurable]
  simp_rw [fun ℓ => (unifI_isProb 0 ℓ).measure_univ, lintegral_one, measure_univ]

/-- **Lemma 22** (`j:lem:pairs`), for a probability measure `π` on `[0, ∞)` with
`∫ ℓ π(dℓ) = 2μ`, `μ > 0` (the slab measure of `F ∈ 𝒟(B)` with mean `μ`, by Lemma 20; see
`pairs_lemma_F`). Write `F = ∫ U[0, ℓ] π(dℓ)`, `π₋ = π|[0, 2μ)`, `π₊ = π|(2μ, ∞)`,
`Δ = ∫ (2μ - ℓ) π₋(dℓ)`. Then `Δ = ∫ (ℓ - 2μ) π₊(dℓ)`; if `Δ = 0` then `π = δ_{2μ}` and
`F = U[0, 2μ]`; if `Δ > 0` then `F = π({2μ}) U[0, 2μ] + ∬ g^μ_{ℓ₁,ℓ₂} P(dℓ₁, dℓ₂)` with
`P(dℓ₁, dℓ₂) = (ℓ₂ - ℓ₁)/Δ π₋(dℓ₁) π₊(dℓ₂)`, and `P` has total mass `1 - π({2μ})`. -/
theorem pairs_lemma [IsProbabilityMeasure π] {μ : ℝ} (hμ : 0 < μ) (hπ0 : π (Iio 0) = 0)
    (hmean : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = ENNReal.ofReal (2 * μ)) :
    Delta (2 * μ) π = ∫⁻ ℓ, ENNReal.ofReal (ℓ - 2 * μ) ∂(piPlus (2 * μ) π) ∧
    (Delta (2 * μ) π = 0 → π = Measure.dirac (2 * μ) ∧
      π.bind (fun ℓ => unifI 0 ℓ) = unifI 0 (2 * μ)) ∧
    (Delta (2 * μ) π ≠ 0 → π.bind (fun ℓ => unifI 0 ℓ) =
        π {2 * μ} • unifI 0 (2 * μ) + (pairMeas (2 * μ) π).bind (fun p => gPiece μ p.1 p.2) ∧
      pairMeas (2 * μ) π univ = 1 - π {2 * μ}) := by
  have hm : 0 < 2 * μ := by linarith
  have hmix : ∀ s, MeasurableSet s → π.bind (fun ℓ => unifI 0 ℓ) s =
      ∫⁻ ℓ, unifI 0 ℓ s ∂(piMinus (2 * μ) π) + unifI 0 (2 * μ) s * π {2 * μ} +
        ∫⁻ ℓ, unifI 0 ℓ s ∂(piPlus (2 * μ) π) :=
    fun s hs => by
      rw [Measure.bind_apply hs Slabs.measurable_unifI_zero.aemeasurable,
        lintegral_split hπ0 hm]
  have h1 := lintegral_split hπ0 hm (π := π) (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, measure_univ, one_mul] at h1
  refine ⟨(delta_eq hπ0 hm hmean).1, fun hΔ => ?_, fun hΔ => ?_⟩
  · obtain ⟨hmz, hp⟩ := eq_zero_of_delta_eq_zero hπ0 hm hmean hΔ
    rw [hmz, hp] at h1
    simp only [FunLike.coe_zero, Pi.zero_apply, zero_add, add_zero] at h1
    have hπ : π = Measure.dirac (2 * μ) := by
      ext s hs
      have := lintegral_split hπ0 hm (π := π) (s.indicator 1)
      rw [lintegral_indicator_one hs, hmz, hp, ← h1] at this
      rw [this, Measure.dirac_apply' _ hs]
      simp
    refine ⟨hπ, ?_⟩
    rw [hπ, Measure.dirac_bind Slabs.measurable_unifI_zero]
  · have hP : ∀ s, MeasurableSet s → π.bind (fun ℓ => unifI 0 ℓ) s =
        π {2 * μ} * unifI 0 (2 * μ) s + ∫⁻ p, gPiece μ p.1 p.2 s ∂(pairMeas (2 * μ) π) :=
      fun s hs => by
        rw [hmix s hs, lintegral_pairMeas hπ0 hμ hmean hΔ hs]; ring
    have hbind : π.bind (fun ℓ => unifI 0 ℓ) =
        π {2 * μ} • unifI 0 (2 * μ) + (pairMeas (2 * μ) π).bind (fun p => gPiece μ p.1 p.2) := by
      ext s hs
      rw [hP s hs, add_apply, smul_apply, smul_eq_mul,
        Measure.bind_apply hs (measurable_gPiece μ).aemeasurable]
    refine ⟨hbind, ?_⟩
    have hu := hP univ MeasurableSet.univ
    have := bind_unifI_isProb (π := π)
    have hg : ∀ᵐ p ∂(pairMeas (2 * μ) π), gPiece μ p.1 p.2 univ = 1 := by
      filter_upwards [ae_pairMeas] with p hp
      exact (gPiece_isProb hp.1.2 (mem_Ioi.mp hp.2)).measure_univ
    rw [lintegral_congr_ae hg, lintegral_one, measure_univ, (unifI_isProb 0 _).measure_univ,
      mul_one] at hu
    exact ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) (by rw [hu, add_comm])

lemma ae_pairMeas_le [IsFiniteMeasure π] {B : ℝ} (hπB : π (Icc 0 B)ᶜ = 0) :
    ∀ᵐ p ∂(pairMeas m π), p.2 ≤ B := by
  refine (withDensity_absolutelyContinuous _ _).ae_le (ae_iff.mpr ?_)
  have : {p : ℝ × ℝ | ¬ p.2 ≤ B} = univ ×ˢ Ioi B := by ext p; simp
  rw [this, Measure.prod_prod]
  have : piPlus m π (Ioi B) = 0 := by
    refine measure_mono_null (show Ioi B ⊆ (Icc 0 B)ᶜ from
      fun x hx h => (mem_Ioi.mp hx).not_ge h.2) ?_
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hπB) zero_le
  rw [this, mul_zero]

/-- **Lemma 22** (`j:lem:pairs`) for `F ∈ 𝒟(B)` with mean `μ > 0` and slab measure
`π = slabMeas F ν` (hypotheses of `slab_lemma`). With `π₋`, `π₊`, `Δ` and `P` as in
`pairs_lemma`: `Δ = ∫ (ℓ - 2μ) π₊(dℓ)`; if `Δ = 0` then `F = U[0, 2μ]`; if `Δ > 0` then
`F = π({2μ}) U[0, 2μ] + ∬ g^μ_{ℓ₁,ℓ₂} P(dℓ₁, dℓ₂)`, `P` has total mass `1 - π({2μ})`, and
`P`-almost every `(ℓ₁, ℓ₂)` is a piece `0 ≤ ℓ₁ < 2μ < ℓ₂` with `ℓ₂ ≤ B` (the remark after the
lemma). -/
theorem pairs_lemma_F {F : Measure ℝ} [IsProbabilityMeasure F] {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF0 : F (Iio 0) = 0) (hFf : F.restrict (Ioi 0) = Slabs.densMeas f)
    (hfB : ∀ x, B < x → f x = 0) {ν : Measure ℝ} (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {μ : ℝ} (hμ : 0 < μ)
    (hmeanF : ∫ x, x ∂F = μ) :
    Delta (2 * μ) (slabMeas F ν) =
      ∫⁻ ℓ, ENNReal.ofReal (ℓ - 2 * μ) ∂(piPlus (2 * μ) (slabMeas F ν)) ∧
    (Delta (2 * μ) (slabMeas F ν) = 0 → F = unifI 0 (2 * μ)) ∧
    (Delta (2 * μ) (slabMeas F ν) ≠ 0 →
      F = slabMeas F ν {2 * μ} • unifI 0 (2 * μ) +
        (pairMeas (2 * μ) (slabMeas F ν)).bind (fun p => gPiece μ p.1 p.2) ∧
      pairMeas (2 * μ) (slabMeas F ν) univ = 1 - slabMeas F ν {2 * μ} ∧
      ∀ᵐ p ∂(pairMeas (2 * μ) (slabMeas F ν)), 0 ≤ p.1 ∧ p.1 < 2 * μ ∧ 2 * μ < p.2 ∧ p.2 ≤ B) := by
  obtain ⟨hprob, hsupp, hbind, hmean, -⟩ := slab_lemma hB hF0 hFf hfB hν0 hνf
  have hπ0 := slabMeas_Iio (F := F) hν0
  set π := slabMeas F ν with hπdef
  have hL : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π = ENNReal.ofReal (2 * μ) := by
    have hfin : ∫⁻ ℓ, ENNReal.ofReal ℓ ∂π ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal B ∂π) ?_ ?_
      · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
      · refine lintegral_mono_ae ?_
        have : ∀ᵐ ℓ ∂π, ℓ ∈ Icc 0 B := by rw [ae_iff]; exact hsupp
        exact this.mono fun ℓ hℓ => ENNReal.ofReal_le_ofReal hℓ.2
    have h2 : ∫ ℓ, ℓ ∂π = 2 * μ := by linarith
    rw [integral_eq_lintegral_of_nonneg_ae (ae_nonneg_of_Iio hπ0)
      measurable_id.aestronglyMeasurable] at h2
    rw [← h2]
    exact (ENNReal.ofReal_toReal hfin).symm
  obtain ⟨h1, h2, h3⟩ := pairs_lemma hμ hπ0 hL
  refine ⟨h1, fun hΔ => hbind.trans (h2 hΔ).2, fun hΔ => ?_⟩
  obtain ⟨h4, h5⟩ := h3 hΔ
  refine ⟨hbind.trans h4, h5, ?_⟩
  filter_upwards [ae_pairMeas, ae_pairMeas_le hsupp] with p hp hpB
  exact ⟨hp.1.1, hp.1.2, mem_Ioi.mp hp.2, hpB⟩

/-! ### Lemma 23: splitting the slab lengths -/

/-- `φ(x) = U[0, x]` for `x ∈ {a, b}` and `φ(x) = g^{x/2}_{a,b}` otherwise. -/
def phi (a b x : ℝ) : Measure ℝ := if x = a ∨ x = b then unifI 0 x else gPiece (x / 2) a b

/-- `(a, b)` is a piece for the mean `μ`: `0 ≤ a < 2μ < b`, or `a = b = 2μ`. -/
def IsPiece (μ a b : ℝ) : Prop := (0 ≤ a ∧ a < 2 * μ ∧ 2 * μ < b) ∨ (a = 2 * μ ∧ b = 2 * μ)

/-- The distribution a piece stands for: `g^μ_{a,b}`, or `U[0, 2μ]` if `a = b = 2μ`. -/
def piece (μ a b : ℝ) : Measure ℝ := if a = b then unifI 0 (2 * μ) else gPiece μ a b

lemma phi_two_mu {μ a b : ℝ} (h : IsPiece μ a b) : phi a b (2 * μ) = piece μ a b := by
  rcases h with ⟨_, h1, h2⟩ | ⟨rfl, rfl⟩
  · unfold phi piece
    split_ifs with h h' h'
    · rcases h with h | h <;> linarith
    · rcases h with h | h <;> linarith
    · linarith
    · congr 1; ring
  · simp [phi, piece]

/-- The affine formula (`j:eq:affine`) for `a < b` and `a ≤ x ≤ b`. -/
lemma phi_affine {a b x : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    phi a b x = ENNReal.ofReal ((b - x) / (b - a)) • unifI 0 a +
      ENNReal.ofReal ((x - a) / (b - a)) • unifI 0 b := by
  have hba : b - a ≠ 0 := by linarith
  unfold phi
  split_ifs with h
  · rcases h with rfl | rfl
    · simp [div_self hba]
    · simp [div_self hba]
  · rw [not_or] at h
    rw [gPiece, show 2 * (x / 2) = x by ring]

/-- Mixtures of the `φ(xᵢ)` with weights `θᵢ ≥ 0`, in the affine form. -/
lemma list_sum_phi {a b : ℝ} (hab : a < b) (L : List (ℝ × ℝ))
    (hL : ∀ p ∈ L, a ≤ p.1 ∧ p.1 ≤ b ∧ 0 ≤ p.2) :
    (L.map fun p => ENNReal.ofReal p.2 • phi a b p.1).sum =
      ENNReal.ofReal ((L.map fun p => p.2 * ((b - p.1) / (b - a))).sum) • unifI 0 a +
      ENNReal.ofReal ((L.map fun p => p.2 * ((p.1 - a) / (b - a))).sum) • unifI 0 b := by
  have hba : 0 < b - a := by linarith
  induction L with
  | nil => simp
  | cons q L ih =>
    have hq := hL q (by simp)
    have ih := ih fun p hp => hL p (by simp [hp])
    have hn1 : 0 ≤ (L.map fun p => p.2 * ((b - p.1) / (b - a))).sum :=
      List.sum_nonneg fun y hy => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        have := hL p (by simp [hp])
        exact mul_nonneg this.2.2 (div_nonneg (by linarith) hba.le)
    have hn2 : 0 ≤ (L.map fun p => p.2 * ((p.1 - a) / (b - a))).sum :=
      List.sum_nonneg fun y hy => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        have := hL p (by simp [hp])
        exact mul_nonneg this.2.2 (div_nonneg (by linarith) hba.le)
    have hq1 : 0 ≤ q.2 * ((b - q.1) / (b - a)) :=
      mul_nonneg hq.2.2 (div_nonneg (by linarith) hba.le)
    have hq2 : 0 ≤ q.2 * ((q.1 - a) / (b - a)) :=
      mul_nonneg hq.2.2 (div_nonneg (by linarith) hba.le)
    simp only [List.map_cons, List.sum_cons]
    rw [ih, phi_affine hab hq.1 hq.2.1, ENNReal.ofReal_add hq1 hn1, ENNReal.ofReal_add hq2 hn2,
      smul_add, smul_smul, smul_smul, ← ENNReal.ofReal_mul hq.2.2,
      ← ENNReal.ofReal_mul hq.2.2, add_smul, add_smul]
    abel

/-- A convex combination of the `φ(xᵢ)` is `φ` of the convex combination (affinity of `φ`, also
when `a = b`). -/
lemma list_sum_phi_eq {a b : ℝ} (hab : a ≤ b) (L : List (ℝ × ℝ))
    (hL : ∀ p ∈ L, a ≤ p.1 ∧ p.1 ≤ b ∧ 0 ≤ p.2) (h1 : (L.map Prod.snd).sum = 1) :
    (L.map fun p => ENNReal.ofReal p.2 • phi a b p.1).sum =
      phi a b (L.map fun p => p.2 * p.1).sum := by
  set c := (L.map fun p => p.2 * p.1).sum
  rcases hab.lt_or_eq with hab | rfl
  · have hba : 0 < b - a := by linarith
    have e1 : (L.map fun p => p.2 * ((b - p.1) / (b - a))).sum = (b - c) / (b - a) := by
      have : ∀ L : List (ℝ × ℝ), (L.map fun p => p.2 * ((b - p.1) / (b - a))).sum =
          (b * (L.map Prod.snd).sum - (L.map fun p => p.2 * p.1).sum) / (b - a) := by
        intro L; induction L with
        | nil => simp
        | cons q L ih => simp only [List.map_cons, List.sum_cons, ih]; field_simp; ring
      rw [this, h1, mul_one]
    have e2 : (L.map fun p => p.2 * ((p.1 - a) / (b - a))).sum = (c - a) / (b - a) := by
      have : ∀ L : List (ℝ × ℝ), (L.map fun p => p.2 * ((p.1 - a) / (b - a))).sum =
          ((L.map fun p => p.2 * p.1).sum - a * (L.map Prod.snd).sum) / (b - a) := by
        intro L; induction L with
        | nil => simp
        | cons q L ih => simp only [List.map_cons, List.sum_cons, ih]; field_simp; ring
      rw [this, h1, mul_one]
    have hn : ∀ L' : List (ℝ × ℝ), (∀ p ∈ L', a ≤ p.1 ∧ p.1 ≤ b ∧ 0 ≤ p.2) →
        0 ≤ (L'.map fun p => p.2 * ((b - p.1) / (b - a))).sum ∧
        0 ≤ (L'.map fun p => p.2 * ((p.1 - a) / (b - a))).sum := fun L' hL' =>
      ⟨List.sum_nonneg fun y hy => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact mul_nonneg (hL' p hp).2.2 (div_nonneg (by linarith [(hL' p hp).2.1]) hba.le),
       List.sum_nonneg fun y hy => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact mul_nonneg (hL' p hp).2.2 (div_nonneg (by linarith [(hL' p hp).1]) hba.le)⟩
    obtain ⟨hn1, hn2⟩ := hn L hL
    rw [e1] at hn1; rw [e2] at hn2
    have hcb : c ≤ b := by
      have := (div_nonneg_iff.mp hn1); rcases this with h | h <;> linarith [h.1, h.2]
    have hac : a ≤ c := by
      have := (div_nonneg_iff.mp hn2); rcases this with h | h <;> linarith [h.1, h.2]
    rw [list_sum_phi hab L hL, e1, e2, phi_affine hab hac hcb]
  · have hc : c = a := by
      have : ∀ L' : List (ℝ × ℝ), (∀ p ∈ L', a ≤ p.1 ∧ p.1 ≤ a ∧ 0 ≤ p.2) →
          (L'.map fun p => p.2 * p.1).sum = a * (L'.map Prod.snd).sum := by
        intro L' hL'; induction L' with
        | nil => simp
        | cons q L' ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih fun p hp => hL' p (by simp [hp]),
            show q.1 = a from le_antisymm (hL' q (by simp)).2.1 (hL' q (by simp)).1]
          ring
      rw [show c = _ from this L hL, h1, mul_one]
    have : ∀ L' : List (ℝ × ℝ), (∀ p ∈ L', a ≤ p.1 ∧ p.1 ≤ a ∧ 0 ≤ p.2) →
        (L'.map fun p => ENNReal.ofReal p.2 • phi a a p.1).sum =
          ENNReal.ofReal (L'.map Prod.snd).sum • phi a a a := by
      intro L' hL'; induction L' with
      | nil => simp
      | cons q L' ih =>
        have hq := hL' q (by simp)
        simp only [List.map_cons, List.sum_cons]
        rw [ih fun p hp => hL' p (by simp [hp]), show q.1 = a from le_antisymm hq.2.1 hq.1,
          ENNReal.ofReal_add hq.2.2 (List.sum_nonneg fun y hy => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
            exact (hL' p (by simp [hp])).2.2), add_smul]
    rw [this L hL, h1, ENNReal.ofReal_one, one_smul, hc]

section Procedure

variable {n : ℕ} (a b : Fin n → ℝ)

/-- The coordinates `j` with `a j < v j < b j`. -/
def inner (v : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter fun j => a j < v j ∧ v j < b j

lemma two_le_card_pos {S : Finset (Fin n)} (h : 2 ≤ S.card) : S.Nonempty :=
  Finset.card_pos.mp (by omega)

/-- The smallest element of a set with at least two elements. -/
def first (S : Finset (Fin n)) (h : 2 ≤ S.card) : Fin n := S.min' (two_le_card_pos h)

lemma first_mem {S : Finset (Fin n)} (h : 2 ≤ S.card) : first S h ∈ S := Finset.min'_mem _ _

lemma erase_nonempty {S : Finset (Fin n)} (h : 2 ≤ S.card) : (S.erase (first S h)).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (first_mem h)]; omega

/-- The second smallest element of a set with at least two elements. -/
def second (S : Finset (Fin n)) (h : 2 ≤ S.card) : Fin n := (S.erase (first S h)).min'
  (erase_nonempty h)

lemma second_mem {S : Finset (Fin n)} (h : 2 ≤ S.card) : second S h ∈ S :=
  Finset.mem_of_mem_erase (Finset.min'_mem _ _)

lemma first_lt_second {S : Finset (Fin n)} (h : 2 ≤ S.card) : first S h < second S h := by
  have h1 := Finset.min'_mem _ (erase_nonempty h)
  have hne : second S h ≠ first S h := Finset.ne_of_mem_erase h1
  exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_of_mem_erase h1)) hne.symm

/-- The direction `e_i - e_k`. -/
def dir (i k : Fin n) : Fin n → ℝ := Pi.single i 1 - Pi.single k 1

lemma dir_apply {i k : Fin n} (hik : i ≠ k) (j : Fin n) :
    dir i k j = if j = i then 1 else if j = k then -1 else 0 := by
  unfold dir
  by_cases h1 : j = i
  · subst h1; simp [hik]
  · by_cases h2 : j = k
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- The splitting procedure of Lemma 23, with a bound `fuel` on the depth (`fuel = n` suffices,
`proc_spec`). Given `v` and `θ`: if at most one coordinate is inside its interval, output
`(v, θ)`; otherwise, with `i < k` the two smallest such coordinates,
`t₊ = min (b_i - v_i) (v_k - a_k)`, `t₋ = min (v_i - a_i) (b_k - v_k)`, recurse on
`(v + t₊ (e_i - e_k), θ t₋/(t₊ + t₋))` and on `(v - t₋ (e_i - e_k), θ t₊/(t₊ + t₋))`. -/
def proc : ℕ → (Fin n → ℝ) → ℝ → List ((Fin n → ℝ) × ℝ)
  | 0, v, θ => [(v, θ)]
  | fuel + 1, v, θ =>
    if h : 2 ≤ (inner a b v).card then
      let i := first (inner a b v) h
      let k := second (inner a b v) h
      let tp := min (b i - v i) (v k - a k)
      let tm := min (v i - a i) (b k - v k)
      proc fuel (v + tp • dir i k) (θ * tm / (tp + tm)) ++
        proc fuel (v - tm • dir i k) (θ * tp / (tp + tm))
    else [(v, θ)]

/-- The box `∏ [a_j, b_j]`. -/
def InBox (v : Fin n → ℝ) : Prop := ∀ j, a j ≤ v j ∧ v j ≤ b j

variable {a b}

/-- One step: moving along `e_i - e_k` until coordinate `i` or `k` reaches an end of its
interval removes it from the inner coordinates; the point stays in the box. -/
lemma step_spec {v : Fin n → ℝ} (hv : InBox a b v) {i k : Fin n} (hik : i ≠ k)
    (hi : i ∈ inner a b v) (hk : k ∈ inner a b v) {t : ℝ} (ht : 0 < t)
    (ht' : t = b i - v i ∨ t = v k - a k) (hti : t ≤ b i - v i) (htk : t ≤ v k - a k) :
    InBox a b (v + t • dir i k) ∧ (inner a b (v + t • dir i k)).card < (inner a b v).card ∧
      ∑ j, (v + t • dir i k) j = ∑ j, v j := by
  simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
  have happ : ∀ j, (v + t • dir i k) j = v j + t * (if j = i then 1 else if j = k then -1
      else 0) := fun j => by simp [dir_apply hik j]
  refine ⟨fun j => ?_, ?_, ?_⟩
  · rw [happ]
    by_cases h1 : j = i
    · subst h1; simp; constructor <;> linarith
    · by_cases h2 : j = k
      · subst h2; simp [h1]; constructor <;> linarith
      · simp [h1, h2]; exact hv j
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · rcases ht' with h | h
      · refine ⟨i, ?_, ?_⟩
        · simp [inner, hi]
        · simp [inner, dir_apply hik, h]
      · refine ⟨k, ?_, ?_⟩
        · simp [inner, hk]
        · simp [inner, dir_apply hik, h, hik.symm]
    · intro j hj
      simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_cases h1 : j = i
      · subst h1; exact hi
      · by_cases h2 : j = k
        · subst h2; exact hk
        · rw [happ] at hj; simpa [h1, h2] using hj
  · have h0 : ∑ j, dir i k j = 0 := by simp [dir, Finset.sum_sub_distrib]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, h0, mul_zero, add_zero]

lemma dir_swap (i k : Fin n) : dir k i = -dir i k := by unfold dir; abel

/-- The invariants of the procedure: with enough fuel, every output lies in the box, has at most
one inner coordinate, a positive weight and the coordinate sum of the input; the weights add up
to `θ`, the weighted outputs to `θ v`, and there are at most `2^(c - 1)` outputs, where `c` is
the number of inner coordinates of the input. -/
lemma proc_spec : ∀ (fuel : ℕ) (v : Fin n → ℝ) (θ : ℝ), InBox a b v →
    (inner a b v).card ≤ fuel + 1 → 0 < θ →
    (∀ p ∈ proc a b fuel v θ, InBox a b p.1 ∧ (inner a b p.1).card ≤ 1 ∧ 0 < p.2 ∧
        ∑ j, p.1 j = ∑ j, v j) ∧
    ((proc a b fuel v θ).map Prod.snd).sum = θ ∧
    ((proc a b fuel v θ).map fun p => p.2 • p.1).sum = θ • v ∧
    (proc a b fuel v θ).length ≤ 2 ^ ((inner a b v).card - 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro v θ hv hc hθ
    simp only [proc]
    refine ⟨?_, by simp, by simp, by simp [Nat.one_le_two_pow]⟩
    intro p hp
    rw [List.mem_singleton] at hp; subst hp
    exact ⟨hv, by omega, hθ, rfl⟩
  | succ fuel ih =>
    intro v θ hv hc hθ
    by_cases h : 2 ≤ (inner a b v).card
    · simp only [proc, h, ↓reduceDIte]
      set i := first (inner a b v) h
      set k := second (inner a b v) h
      have hik : i ≠ k := (first_lt_second h).ne
      have hi : i ∈ inner a b v := first_mem h
      have hk : k ∈ inner a b v := second_mem h
      have hi' := hi; have hk' := hk
      simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and] at hi' hk'
      set tp := min (b i - v i) (v k - a k) with htpdef
      set tm := min (v i - a i) (b k - v k) with htmdef
      have htp : 0 < tp := lt_min (by linarith) (by linarith)
      have htm : 0 < tm := lt_min (by linarith) (by linarith)
      obtain ⟨hb1, hc1, hs1⟩ := step_spec hv hik hi hk htp (min_choice _ _) (min_le_left _ _)
        (min_le_right _ _)
      have hvm : v - tm • dir i k = v + tm • dir k i := by
        rw [dir_swap i k, smul_neg, sub_eq_add_neg]
      obtain ⟨hb2, hc2, hs2⟩ := step_spec hv hik.symm hk hi htm
        (by rcases min_choice (v i - a i) (b k - v k) with h' | h'
            · exact Or.inr h'
            · exact Or.inl h')
        (min_le_right _ _) (min_le_left _ _)
      rw [← hvm] at hb2 hc2 hs2
      have hθ1 : 0 < θ * tm / (tp + tm) := by positivity
      have hθ2 : 0 < θ * tp / (tp + tm) := by positivity
      obtain ⟨A1, B1, C1, D1⟩ := ih _ _ hb1 (by omega) hθ1
      obtain ⟨A2, B2, C2, D2⟩ := ih _ _ hb2 (by omega) hθ2
      refine ⟨fun p hp => ?_, ?_, ?_, ?_⟩
      · rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨x1, x2, x3, x4⟩ := A1 p hp; exact ⟨x1, x2, x3, x4.trans hs1⟩
        · obtain ⟨x1, x2, x3, x4⟩ := A2 p hp; exact ⟨x1, x2, x3, x4.trans hs2⟩
      · rw [List.map_append, List.sum_append, B1, B2]
        field_simp
        ring
      · rw [List.map_append, List.sum_append, C1, C2]
        ext j
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      · rw [List.length_append]
        set c := (inner a b v).card
        have e1 : 2 ^ ((inner a b (v + tp • dir i k)).card - 1) ≤ 2 ^ (c - 2) :=
          Nat.pow_le_pow_right two_pos (by omega)
        have e2 : 2 ^ ((inner a b (v - tm • dir i k)).card - 1) ≤ 2 ^ (c - 2) :=
          Nat.pow_le_pow_right two_pos (by omega)
        have e3 : 2 ^ (c - 1) = 2 * 2 ^ (c - 2) := by
          rw [show c - 1 = (c - 2) + 1 by omega, pow_succ]; ring
        omega
    · simp only [proc, h, ↓reduceDIte]
      refine ⟨?_, by simp, by simp, by simp [Nat.one_le_two_pow]⟩
      intro p hp
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨hv, show (inner a b v).card ≤ 1 by omega, hθ, rfl⟩

section ListSums

variable {β α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]

lemma list_sum_apply (L : List β) (g : β → Measure α) (s : Set α) :
    (L.map g).sum s = (L.map fun p => g p s).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [ih]

lemma map_list_sum (L : List β) (g : β → Measure α) {f : α → γ} (hf : Measurable f) :
    ((L.map g).sum).map f = (L.map fun p => (g p).map f).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [Measure.map_add _ _ hf, ih]

lemma ae_list_sum (L : List β) (g : β → Measure α) {P : α → Prop}
    (h : ∀ p ∈ L, ∀ᵐ x ∂g p, P x) : ∀ᵐ x ∂(L.map g).sum, P x := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ae_add_measure_iff.mpr ⟨h q (by simp), ih fun p hp => h p (by simp [hp])⟩

lemma list_sum_ofReal (L : List (β × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.2) :
    (L.map fun p => ENNReal.ofReal p.2).sum = ENNReal.ofReal (L.map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih fun p hp => hL p (by simp [hp]), ENNReal.ofReal_add (hL q (by simp))
      (List.sum_nonneg fun y hy => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact hL p (by simp [hp]))]

lemma list_sum_vec_apply {n : ℕ} (L : List ((Fin n → ℝ) × ℝ)) (j : Fin n) :
    (L.map fun p => p.2 • p.1).sum j = (L.map fun p => p.2 * p.1 j).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [ih]

end ListSums

/-- **Lemma 23** (`j:lem:split`). Let `(a_j, b_j)` be a piece for the mean `μ_j`
(`j = 1, …, n`) and `s = ∑ μ_j`. The procedure `proc`, started at `m = (2μ_1, …, 2μ_n)` with
weight `1` (and depth bound `n`), outputs at most `2^(n-1)` pairs `(v, θ_v)` with `θ_v > 0`,
`∑ θ_v = 1`, `∑ θ_v v = m` and `∑_j v_j = 2s`; every output lies in the box `∏ [a_j, b_j]` and has
at most one coordinate with `a_j < v_j < b_j`. If for every output `v` a joint mix `P v` of the
leaf `(φ_1(v_1), …, φ_n(v_n))` with sum `s` is given, then `∑ θ_v P v` is a joint mix of the
pieces with sum `s`. -/
theorem split_lemma {n : ℕ} {μ a b : Fin n → ℝ} (hp : ∀ j, IsPiece (μ j) (a j) (b j)) :
    (proc a b n (fun j => 2 * μ j) 1).length ≤ 2 ^ (n - 1) ∧
    (∀ p ∈ proc a b n (fun j => 2 * μ j) 1, 0 < p.2 ∧ ∑ j, p.1 j = 2 * ∑ j, μ j ∧
      InBox a b p.1 ∧ (inner a b p.1).card ≤ 1) ∧
    ((proc a b n (fun j => 2 * μ j) 1).map Prod.snd).sum = 1 ∧
    ((proc a b n (fun j => 2 * μ j) 1).map fun p => p.2 • p.1).sum = (fun j => 2 * μ j) ∧
    ∀ P : (Fin n → ℝ) → Measure (Fin n → ℝ),
      (∀ p ∈ proc a b n (fun j => 2 * μ j) 1,
        IsJointMix (fun j => phi (a j) (b j) (p.1 j)) (P p.1) ∧
          ∀ᵐ x ∂P p.1, ∑ j, x j = ∑ j, μ j) →
      IsJointMix (fun j => piece (μ j) (a j) (b j))
          ((proc a b n (fun j => 2 * μ j) 1).map fun p => ENNReal.ofReal p.2 • P p.1).sum ∧
        ∀ᵐ x ∂((proc a b n (fun j => 2 * μ j) 1).map fun p => ENNReal.ofReal p.2 • P p.1).sum,
          ∑ j, x j = ∑ j, μ j := by
  set m : Fin n → ℝ := fun j => 2 * μ j with hm
  set L := proc a b n m 1 with hL
  have hbox : InBox a b m := fun j => by
    rcases hp j with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact ⟨h2.le, h3.le⟩
    · exact ⟨h1.le, h2.ge⟩
  have hcard : (inner a b m).card ≤ n := (Finset.card_le_univ _).trans (by simp)
  obtain ⟨A, B, C, D⟩ := proc_spec n m 1 hbox (by omega) one_pos
  have hab : ∀ j, a j ≤ b j := fun j => (hbox j).1.trans (hbox j).2
  refine ⟨D.trans (Nat.pow_le_pow_right two_pos (by omega)), fun p hp => ?_, B, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := A p hp
    refine ⟨h3, ?_, h1, h2⟩
    rw [h4, hm, ← Finset.mul_sum]
  · rw [C, one_smul]
  · intro P hP
    have hsum : ∀ᵐ x ∂(L.map fun p => ENNReal.ofReal p.2 • P p.1).sum, ∑ j, x j = ∑ j, μ j :=
      ae_list_sum _ _ fun p hp => Measure.ae_smul_measure (hP p hp).2 _
    refine ⟨⟨⟨?_⟩, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
    · rw [list_sum_apply]
      have : ∀ p ∈ L, (ENNReal.ofReal p.2 • P p.1) univ = ENNReal.ofReal p.2 := fun p hp => by
        have := (hP p hp).1.1
        rw [smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [List.map_congr_left this, list_sum_ofReal L fun p hp => (A p hp).2.2.1.le, B,
        ENNReal.ofReal_one]
    · rw [map_list_sum _ _ (measurable_pi_apply j)]
      have e1 : ∀ p ∈ L, (ENNReal.ofReal p.2 • P p.1).map (fun x => x j) =
          ENNReal.ofReal p.2 • phi (a j) (b j) (p.1 j) := fun p hp => by
        rw [Measure.map_smul _ (measurable_pi_apply j).aemeasurable, (hP p hp).1.2.2 j]
      rw [List.map_congr_left e1]
      show _ = piece (μ j) (a j) (b j)
      rw [← phi_two_mu (hp j)]
      have e2 := list_sum_phi_eq (hab j) (L.map fun p => (p.1 j, p.2))
        (fun q hq => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          exact ⟨((A p hp).1 j).1, ((A p hp).1 j).2, (A p hp).2.2.1.le⟩)
        (by rw [List.map_map]; exact B)
      simp only [List.map_map, Function.comp_def] at e2
      rw [e2]
      congr 1
      rw [← list_sum_vec_apply, C, one_smul]

end Procedure

end JointLemmas

end Mixes
