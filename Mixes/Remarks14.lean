import Mixes.Sphere
import Mixes.TwoStep
import Mixes.Trapezoid

/-!
# Draft 14: Proposition `rm:prop:generic` and three new remarks

The paper.

## Proposition `rm:prop:generic` (a common principle, Open Problem 2)

`ξ` is a random vector of a finite-dimensional real inner product space `V` whose law `μ` is
invariant under all linear isometries (`Ball.IsRotInv`); its "first coordinate" is
`ζ = ⟪u₀, ξ⟫` for a fixed unit vector `u₀` (for `V = ℝ^{k}` and `u₀` the first unit vector this is
`ξ 0`, `inner_single_zero`). Random vectors are replaced by laws, as in `Defs.lean`.

* (a) `law_inner`: `c + E · ξ` has the law of `c + |E| ζ`. `prop_generic_a_mix`: for
  `∑ E_j = 0` the law of `(c_j + E_j · ξ)_j` is a joint mix of the laws of `c_j + |E_j| ζ`, with
  sum `∑ c_j` almost surely. `polygon_iff_two` (`dim V ≥ 2`): vectors of lengths `λ_j ≥ 0` with
  sum `0` exist iff `2 max λ_j ≤ ∑ λ_j`. `polygon_iff_one` (`dim V = 1`): iff the `λ_j` split
  into two groups with equal sums.
* (b) `prop_generic_b`: `(c, E)` random with law `ν`, independent of `ξ` (product measure),
  `∑ E_j = 0` and `∑ c_j = s` `ν`-a.s.: the law of `(c_j + E_j · ξ)_j` is a joint mix with sum `s`,
  and the `j`-th marginal is the law of `c + λ ζ` with `(c, λ) ∼ (c_j, |E_j|)` independent of `ζ`
  (the mixture of the laws of `c + λ ζ`).
* (c) `prop_generic_c`: every joint mix arises so, with `E = 0`.
  `jointlyMixable_iff_exists_cE`: joint mixability is equivalent to the existence of a law of
  `(c, E)` as in (b) with the given marginals.

## Remark after the opening of Section `sec:remarks` (on Lemma `lem:arch`)

* The law of `e · ξ` depends only on `|e|`: `law_inner`; vectors with sum `0` give a joint mix of
  scaled copies: `prop_generic_a_mix` with `c = 0`.
* `isArchimedesMeasure_of_rotInv`: a rotation-invariant probability whose projection on one unit
  vector is `U[-1, 1]` is an `IsArchimedesMeasure` (the hypothesis of `lem_arch`).
* `sphUnif_isRotInv`, `isArchimedesMeasure_sphUnif`: for `ξ` uniform on `S²` (`Ball.sphUnif`)
  this holds, granted the theorem of Archimedes `H_archimedes` (classical, not in Mathlib).

## Remark after Theorem `m:thm:two` (two-step construction, `TwoStep.lean`)

* `endpoints_tau`, `endpoints_rho`: the two tuples of `S_β` and of `S_D` have the same multiset
  of endpoints; `tau_exchange`, `rho_exchange`: they differ by the exchange of two pairs.
* `Sw_jump`, `jump_zero_iff`, `S_no_jump`: the jump of the marginal of
  `w₁ τ'_β + w₂ τ''_β` at `u_β` is `(w₂/(b-u_β) - w₁/u_β)/n`, which vanishes (with `w₁ + w₂ = 1`)
  exactly for `w₁ = u_β/b`, `w₂ = 1 - u_β/b`.
* Tight case `β = 1`, `b = n`: `tau1_tight`, `tau2_tight` (polygon inequality with equality);
  `collinear_of_tight`, `segment_of_tight` (a degenerate polygon is a segment, so the joint mixes
  of Lemma 1 run on segments); `tau1_segment`, `tau2_segment`: the segments start at
  `(0, …, 0, n)` and end at `(a, …, a, n-(n-1)a, a)`, respectively `(a, …, a, n-(n-1)a)`.

## Remark after Theorem `t:thm:trap` (trapezoids)

* `affine_totals`, `polygon_of_affine`: affine lengths and affine midpoints have constant totals,
  and the polygon inequality compares the longest chord with the mean chord.
* `chord_jointMix`: the fibre step of the construction for any chord lengths `ℓ` satisfying the
  polygon inequality and affine (collinear) midpoints: a joint mix of the uniform distributions on
  the chords with sum `n m(c)`.
* `fibre_mid_zero`, `affine_chord_centre`: for a set symmetric in a line and an affine bijection
  `A`, the chords of `A(K)` in the image direction are symmetric about centres that lie on a line.
* `trap_polygon_ae` (with `completeMix_sum_eq`): for trapezoids every complete mix of the abscissa
  satisfies the polygon inequality almost surely.
* `disc_chord`, `disc_polygon_fails`: the chord of the disc of diameter `1` has length
  `2 √(x(1-x))`, and the polygon inequality fails for `(0, 0.6, 0.9)`.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

namespace Mixes.Remarks14

open Ball (IsRotInv)
open TwoStep

/-! ## Proposition `rm:prop:generic` -/

section Generic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Proposition `rm:prop:generic` (a), the law.** For a rotation-invariant `μ` and a unit
vector `u₀`, `c + E · ξ` has the law of `c + |E| ζ`, `ζ = u₀ · ξ`. -/
lemma law_inner {μ : Measure V} (hμ : IsRotInv μ) {u0 : V} (hu0 : ‖u0‖ = 1) (c : ℝ) (E : V) :
    μ.map (fun ξ => c + ⟪E, ξ⟫_ℝ) = μ.map (fun ξ => c + ‖E‖ * ⟪u0, ξ⟫_ℝ) := by
  have h : ‖E‖ = ‖‖E‖ • u0‖ := by rw [norm_smul, hu0, norm_norm, mul_one]
  set R := Submodule.reflection (ℝ ∙ (E - ‖E‖ • u0))ᗮ
  have hR : R E = ‖E‖ • u0 := Submodule.reflection_sub h
  have hf : Measurable (fun η : V => c + ‖E‖ * ⟪u0, η⟫_ℝ) := by fun_prop
  have : (fun ξ => c + ⟪E, ξ⟫_ℝ) = (fun η : V => c + ‖E‖ * ⟪u0, η⟫_ℝ) ∘ R := by
    funext ξ
    simp only [Function.comp]
    rw [← LinearIsometryEquiv.inner_map_map R E ξ, hR, real_inner_smul_left]
  rw [this, ← Measure.map_map hf R.continuous.measurable]
  congr 1
  exact hμ R

omit [MeasurableSpace V] [BorelSpace V] in
/-- **(a), `k ≥ 2`.** Vectors `E_j` with lengths `λ_j ≥ 0` and sum `0` exist iff
`2 max λ_j ≤ ∑ λ_j` (a closed polygon in a plane). -/
lemma polygon_iff_two (hV : 2 ≤ Module.finrank ℝ V) {n : ℕ} (lam : Fin n → ℝ)
    (hnn : ∀ j, 0 ≤ lam j) :
    (∃ E : Fin n → V, (∀ j, ‖E j‖ = lam j) ∧ ∑ j, E j = 0) ↔
      ∀ i, 2 * lam i ≤ ∑ j, lam j := by
  constructor
  · rintro ⟨E, hE, hs⟩ i
    have h1 : E i = -∑ j ∈ Finset.univ.erase i, E j := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ (Finset.mem_univ i), hs]
    have h2 : lam i ≤ ∑ j ∈ Finset.univ.erase i, lam j := by
      rw [← hE i, h1, norm_neg]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => hE j
    have h3 := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i)
    linarith
  · intro hpoly
    by_cases hne : ∃ j, lam j ≠ 0
    swap
    · push Not at hne
      exact ⟨0, fun j => by simp [hne j], by simp⟩
    obtain ⟨j0, hj0⟩ := hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j0.2; omega⟩
    obtain ⟨hn1, hs1⟩ := Ball.polyVec_spec hnn ⟨j0, hj0⟩ hpoly
    let b := stdOrthonormalBasis ℝ V
    have h0 : 0 < Module.finrank ℝ V := by omega
    have h1 : 1 < Module.finrank ℝ V := by omega
    set u : V := b ⟨0, h0⟩
    set w : V := b ⟨1, h1⟩
    have hu : ‖u‖ = 1 := b.orthonormal.1 _
    have hw : ‖w‖ = 1 := b.orthonormal.1 _
    have huw : ⟪u, w⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
    refine ⟨fun j => (Ball.polyVec lam j).1 • u + (Ball.polyVec lam j).2 • w, fun j => ?_, ?_⟩
    · have := norm_sq_smul_add_smul hu hw huw (Ball.polyVec lam j).1 (Ball.polyVec lam j).2
      rw [hn1 j] at this
      exact (pow_left_inj₀ (norm_nonneg _) (hnn j) two_ne_zero).1 this
    · rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Prod.fst_sum,
        ← Prod.snd_sum, hs1]
      simp

omit [MeasurableSpace V] [BorelSpace V] in
/-- **(a), `k = 1`.** Vectors `E_j` with lengths `λ_j ≥ 0` and sum `0` exist iff the `λ_j` can be
divided into two groups with the same sum. -/
lemma polygon_iff_one (hV : Module.finrank ℝ V = 1) {n : ℕ} (lam : Fin n → ℝ)
    (hnn : ∀ j, 0 ≤ lam j) :
    (∃ E : Fin n → V, (∀ j, ‖E j‖ = lam j) ∧ ∑ j, E j = 0) ↔
      ∃ G : Finset (Fin n), ∑ j ∈ G, lam j = ∑ j ∈ Gᶜ, lam j := by
  classical
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
  set u0 : V := b 0
  have hu0 : ‖u0‖ = 1 := b.orthonormal.1 _
  have hrep : ∀ v : V, v = ⟪u0, v⟫_ℝ • u0 := by
    intro v
    conv_lhs => rw [← b.sum_repr' v]
    simp [u0]
  constructor
  · rintro ⟨E, hE, hs⟩
    let t : Fin n → ℝ := fun j => ⟪u0, E j⟫_ℝ
    have ht : ∀ j, |t j| = lam j := by
      intro j
      rw [← hE j]
      conv_rhs => rw [hrep (E j)]
      rw [norm_smul, hu0, mul_one, Real.norm_eq_abs]
    have hts : ∑ j, t j = 0 := by
      simp only [t]; rw [← inner_sum, hs, inner_zero_right]
    refine ⟨Finset.univ.filter (fun j => 0 ≤ t j), ?_⟩
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => 0 ≤ t j), lam j =
        ∑ j ∈ Finset.univ.filter (fun j => 0 ≤ t j), t j :=
      Finset.sum_congr rfl fun j hj => by
        rw [← ht j, abs_of_nonneg (Finset.mem_filter.1 hj).2]
    have h2 : ∑ j ∈ (Finset.univ.filter (fun j => 0 ≤ t j))ᶜ, lam j =
        -∑ j ∈ (Finset.univ.filter (fun j => 0 ≤ t j))ᶜ, t j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : t j < 0 := by simpa using hj
      rw [← ht j, abs_of_neg this]
    have h3 := Finset.sum_add_sum_compl (Finset.univ.filter (fun j => 0 ≤ t j)) t
    linarith
  · rintro ⟨G, hG⟩
    refine ⟨fun j => (if j ∈ G then lam j else -lam j) • u0, fun j => ?_, ?_⟩
    · rw [norm_smul, hu0, mul_one, Real.norm_eq_abs]
      split_ifs
      · exact abs_of_nonneg (hnn j)
      · rw [abs_neg]; exact abs_of_nonneg (hnn j)
    · rw [← Finset.sum_smul, ← Finset.sum_add_sum_compl G]
      have e1 : ∑ j ∈ G, (if j ∈ G then lam j else -lam j) = ∑ j ∈ G, lam j :=
        Finset.sum_congr rfl fun j hj => by simp [hj]
      have e2 : ∑ j ∈ Gᶜ, (if j ∈ G then lam j else -lam j) = -∑ j ∈ Gᶜ, lam j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_compl.1 hj]
      rw [e1, e2, hG]
      simp

variable {n : ℕ}

/-- **Proposition `rm:prop:generic` (a), the joint mix.** If `∑ E_j = 0`, the law of
`(c_j + E_j · ξ)_j` is a joint mix of the laws of `c_j + |E_j| ζ`, with sum `∑ c_j` a.s. -/
theorem prop_generic_a_mix {μ : Measure V} [IsProbabilityMeasure μ] (hμ : IsRotInv μ) {u0 : V}
    (hu0 : ‖u0‖ = 1) (c : Fin n → ℝ) (E : Fin n → V) (hE : ∑ j, E j = 0) :
    IsJointMix (fun j => (μ.map fun ξ => ⟪u0, ξ⟫_ℝ).map fun z => c j + ‖E j‖ * z)
        (μ.map fun ξ j => c j + ⟪E j, ξ⟫_ℝ) ∧
      ∀ᵐ x ∂(μ.map fun ξ j => c j + ⟪E j, ξ⟫_ℝ), ∑ j, x j = ∑ j, c j := by
  have hX := measurable_affine_inner c E
  have hsum : ∀ᵐ x ∂(μ.map fun ξ j => c j + ⟪E j, ξ⟫_ℝ), ∑ j, x j = ∑ j, c j := by
    rw [ae_map_iff hX.aemeasurable (measurableSet_sum_eq _)]
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Finset.sum_add_distrib, ← sum_inner, hE, inner_zero_left, add_zero]
  refine ⟨⟨inferInstance, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  dsimp only
  rw [Measure.map_map (measurable_pi_apply j) hX,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact law_inner hμ hu0 (c j) (E j)

/-- The random vector `X_j = c_j + E_j · ξ` as a function of `((c, E), ξ)`. -/
def genVec (p : (Fin n → ℝ) × (Fin n → V)) (ξ : V) : Fin n → ℝ := fun j => p.1 j + ⟪p.2 j, ξ⟫_ℝ

omit [FiniteDimensional ℝ V] in
lemma measurable_genVec_uncurry [SecondCountableTopology V] :
    Measurable (fun z : ((Fin n → ℝ) × (Fin n → V)) × V => genVec z.1 z.2) := by
  refine measurable_pi_iff.2 fun j => ?_
  have : Continuous (fun z : ((Fin n → ℝ) × (Fin n → V)) × V => z.1.1 j + ⟪z.1.2 j, z.2⟫_ℝ) := by
    fun_prop
  exact this.measurable

/-- **Proposition `rm:prop:generic` (b).** If `(c, E)` has law `ν`, is independent of `ξ`
(product measure) and `∑ E_j = 0`, `∑ c_j = s` `ν`-a.s., then the law of `(c_j + E_j · ξ)_j` is a
joint mix with sum `s`; its `j`-th marginal is the law of `c + λ ζ` with `(c, λ)` distributed as
`(c_j, |E_j|)` and independent of `ζ`. -/
theorem prop_generic_b {μ : Measure V} [IsProbabilityMeasure μ] (hμ : IsRotInv μ) {u0 : V}
    (hu0 : ‖u0‖ = 1) (ν : Measure ((Fin n → ℝ) × (Fin n → V))) [IsProbabilityMeasure ν] (s : ℝ)
    (hν : ∀ᵐ p ∂ν, ∑ j, p.2 j = 0 ∧ ∑ j, p.1 j = s) :
    IsJointMix (fun j => ((ν.map fun p => (p.1 j, ‖p.2 j‖)).prod
          (μ.map fun ξ => ⟪u0, ξ⟫_ℝ)).map fun q => q.1.1 + q.1.2 * q.2)
        ((ν.prod μ).map fun z => genVec z.1 z.2) ∧
      ∀ᵐ x ∂((ν.prod μ).map fun z => genVec z.1 z.2), ∑ j, x j = s := by
  have hX := measurable_genVec_uncurry (n := n) (V := V)
  have hsum : ∀ᵐ x ∂((ν.prod μ).map fun z => genVec z.1 z.2), ∑ j, x j = s := by
    rw [ae_map_iff hX.aemeasurable (measurableSet_sum_eq _)]
    have h1 : ∀ᵐ z ∂(ν.prod μ), ∑ j, z.1.2 j = 0 ∧ ∑ j, z.1.1 j = s := by
      have hfst : (ν.prod μ).map Prod.fst = ν := by simp
      rw [← hfst] at hν
      exact ae_of_ae_map measurable_fst.aemeasurable hν
    filter_upwards [h1] with z hz
    simp only [genVec]
    rw [Finset.sum_add_distrib, ← sum_inner, hz.1, inner_zero_left, add_zero, hz.2]
  refine ⟨⟨inferInstance, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  have hf : Measurable (fun z : ((Fin n → ℝ) × (Fin n → V)) × V => z.1.1 j + ⟪z.1.2 j, z.2⟫_ℝ) :=
    (measurable_pi_apply j).comp hX
  have hg : Measurable (fun z : ((Fin n → ℝ) × (Fin n → V)) × V =>
      z.1.1 j + ‖z.1.2 j‖ * ⟪u0, z.2⟫_ℝ) := by
    have : Continuous (fun z : ((Fin n → ℝ) × (Fin n → V)) × V =>
        z.1.1 j + ‖z.1.2 j‖ * ⟪u0, z.2⟫_ℝ) := by fun_prop
    exact this.measurable
  have hh : Measurable (fun p : (Fin n → ℝ) × (Fin n → V) => (p.1 j, ‖p.2 j‖)) := by
    have : Continuous (fun p : (Fin n → ℝ) × (Fin n → V) => (p.1 j, ‖p.2 j‖)) := by fun_prop
    exact this.measurable
  have hζ : Measurable (fun ξ : V => ⟪u0, ξ⟫_ℝ) := by fun_prop
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => q.1.1 + q.1.2 * q.2) := by fun_prop
  dsimp only
  rw [Measure.map_map (measurable_pi_apply j) hX, Measure.map_prod_map _ _ hh hζ,
    Measure.map_map hm (hh.prodMap hζ)]
  change (ν.prod μ).map (fun z => z.1.1 j + ⟪z.1.2 j, z.2⟫_ℝ) =
    (ν.prod μ).map (fun z => z.1.1 j + ‖z.1.2 j‖ * ⟪u0, z.2⟫_ℝ)
  ext A hA
  rw [Measure.map_apply hf hA, Measure.map_apply hg hA, Measure.prod_apply (hf hA),
    Measure.prod_apply (hg hA)]
  refine lintegral_congr fun p => ?_
  have e := congrArg (fun m : Measure ℝ => m A) (law_inner hμ hu0 (p.1 j) (p.2 j))
  rw [Measure.map_apply (by fun_prop) hA, Measure.map_apply (by fun_prop) hA] at e
  exact e

/-- **Proposition `rm:prop:generic` (c).** Every joint mix `P` is of the form (b), with `E = 0`:
`ν` is the law of `(X, 0)` for `X ∼ P`. -/
theorem prop_generic_c (μ : Measure V) [IsProbabilityMeasure μ] {F : Fin n → Measure ℝ}
    {P : Measure (Fin n → ℝ)} (hP : IsJointMix F P) :
    ∃ (ν : Measure ((Fin n → ℝ) × (Fin n → V))) (s : ℝ), IsProbabilityMeasure ν ∧
      (∀ᵐ p ∂ν, p.2 = 0 ∧ ∑ j, p.1 j = s) ∧ (ν.prod μ).map (fun z => genVec z.1 z.2) = P := by
  obtain ⟨hprob, ⟨s, hs⟩, -⟩ := hP
  let emb : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → V) := fun x => (x, 0)
  have hemb : Measurable emb := measurable_id.prodMk measurable_const
  refine ⟨P.map emb, s, inferInstance, ?_, ?_⟩
  · rw [ae_map_iff hemb.aemeasurable]
    · filter_upwards [hs] with x hx using ⟨rfl, hx⟩
    · exact (measurableSet_singleton _).preimage measurable_snd |>.inter
        (measurableSet_sum_eq s |>.preimage measurable_fst)
  · have hX := measurable_genVec_uncurry (n := n) (V := V)
    rw [show μ = μ.map id from Measure.map_id.symm, Measure.map_prod_map _ _ hemb measurable_id,
      Measure.map_map hX (hemb.prodMap measurable_id)]
    have : ((fun z : ((Fin n → ℝ) × (Fin n → V)) × V => genVec z.1 z.2) ∘ Prod.map emb id) =
        Prod.fst := by
      funext z; funext j; simp [genVec, emb]
    rw [this, Measure.map_fst_prod]
    simp

/-- By (b) and (c), joint mixability of `F` is equivalent to the existence of a law of `(c, E)`
as in (b) whose marginals of (b) are the `F_j`. -/
theorem jointlyMixable_iff_exists_cE (μ : Measure V) [IsProbabilityMeasure μ] (hμ : IsRotInv μ)
    {u0 : V} (hu0 : ‖u0‖ = 1) (F : Fin n → Measure ℝ) :
    JointlyMixable F ↔ ∃ (ν : Measure ((Fin n → ℝ) × (Fin n → V))) (s : ℝ),
      IsProbabilityMeasure ν ∧ (∀ᵐ p ∂ν, ∑ j, p.2 j = 0 ∧ ∑ j, p.1 j = s) ∧
      ∀ j, ((ν.map fun p => (p.1 j, ‖p.2 j‖)).prod
          (μ.map fun ξ => ⟪u0, ξ⟫_ℝ)).map (fun q => q.1.1 + q.1.2 * q.2) = F j := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨ν, s, hν, hνs, hνP⟩ := prop_generic_c (V := V) μ hP
    refine ⟨ν, s, hν, hνs.mono fun p hp => ⟨by simp [hp.1], hp.2⟩, fun j => ?_⟩
    have hb := (prop_generic_b hμ hu0 ν s (hνs.mono fun p hp => ⟨by simp [hp.1], hp.2⟩)).1.2.2 j
    dsimp only at hb
    rw [← hb, hνP]
    exact hP.2.2 j
  · rintro ⟨ν, s, hν, hνs, hF⟩
    have h := (prop_generic_b hμ hu0 ν s hνs).1
    rw [show (fun j => ((ν.map fun p => (p.1 j, ‖p.2 j‖)).prod
          (μ.map fun ξ => ⟪u0, ξ⟫_ℝ)).map (fun q => q.1.1 + q.1.2 * q.2)) = F from
      funext hF] at h
    exact ⟨_, h⟩

/-! ### Remark on Lemma `lem:arch` (spherically symmetric vectors) -/

/-- The uniform distribution on the sphere (`Ball.sphUnif`, the law of `Z/|Z|` for a standard
Gaussian `Z`) is rotation invariant. -/
lemma sphUnif_isRotInv : IsRotInv (Ball.sphUnif V) := by
  intro L
  unfold Ball.sphUnif
  rw [Measure.map_map L.continuous.measurable Ball.measurable_dir]
  have : (L ∘ Ball.dir) = Ball.dir ∘ L := by funext x; exact (Ball.dir_iso L x).symm
  rw [this, ← Measure.map_map Ball.measurable_dir L.continuous.measurable,
    Ball.stdGaussian_isRotInv L]

/-- A rotation-invariant probability whose one-dimensional projection on a unit vector is
`U[-1, 1]` has the property used in Lemma 1 (`lem:arch`): every projection `e · ξ` is
`U[-|e|, |e|]`. -/
theorem isArchimedesMeasure_of_rotInv {μ : Measure V} [IsProbabilityMeasure μ]
    (hμ : IsRotInv μ) {u0 : V} (hu0 : ‖u0‖ = 1)
    (hζ : μ.map (fun ξ => ⟪u0, ξ⟫_ℝ) = unifI (-1) 1) : IsArchimedesMeasure μ := by
  refine ⟨inferInstance, fun e => ?_⟩
  have h := law_inner hμ hu0 0 e
  simp only [zero_add] at h
  rw [h, show (fun ξ => ‖e‖ * ⟪u0, ξ⟫_ℝ) = (fun t => ‖e‖ * t) ∘ (fun ξ => ⟪u0, ξ⟫_ℝ) from rfl,
    ← Measure.map_map (measurable_const_mul _) (by fun_prop), hζ]
  rcases eq_or_lt_of_le (norm_nonneg e) with he | he
  · rw [← he]
    simp only [zero_mul, neg_zero]
    have := unifI_isProb (-1) 1
    rw [Measure.map_const, measure_univ, one_smul]
    simp [unifI]
  · rw [map_unifI_const_mul he]; congr 1 <;> ring

/-- The theorem of Archimedes (classical; not in Mathlib): the first coordinate of a uniform
random point of the sphere `S² ⊂ ℝ³` is uniform on `[-1, 1]`. -/
def H_archimedes : Prop :=
  (Ball.sphUnif (EuclideanSpace ℝ (Fin 3))).map (fun ξ => ξ 0) = unifI (-1) 1

lemma inner_single_zero {k : ℕ} (ξ : EuclideanSpace ℝ (Fin (k + 1))) :
    ⟪EuclideanSpace.single 0 1, ξ⟫_ℝ = ξ 0 := by
  simp [EuclideanSpace.inner_single_left]

/-- Remark on Lemma 1: granted the theorem of Archimedes, the uniform distribution on `S²` is an
Archimedes measure, so Lemma 1 (`lem_arch`) holds with `ξ` uniform on `S²`. -/
theorem isArchimedesMeasure_sphUnif (h : H_archimedes) :
    IsArchimedesMeasure (Ball.sphUnif (EuclideanSpace ℝ (Fin 3))) := by
  refine isArchimedesMeasure_of_rotInv sphUnif_isRotInv (u0 := EuclideanSpace.single 0 1)
    (by simp) ?_
  simp_rw [inner_single_zero]
  exact h

end Generic

/-! ## Remark after Theorem `m:thm:two` -/

/-- The multiset of endpoints of a tuple: each block `c · [l, r]` contributes `c` copies of
`l` and of `r`. -/
def endpoints (t : Tup) : Multiset ℝ := (t.map fun B => B.c • ({B.l, B.r} : Multiset ℝ)).sum

/-- The multiset of intervals `(l, r)` of a tuple. -/
def intervals (t : Tup) : Multiset (ℝ × ℝ) :=
  (t.map fun B => B.c • ({(B.l, B.r)} : Multiset (ℝ × ℝ))).sum

lemma pair_eq {α : Type*} (x y : α) : ({x, y} : Multiset α) = {x} + {y} := by
  rw [Multiset.insert_eq_cons, Multiset.singleton_add]

/-- `τ'_β` and `τ''_β` differ by the exchange of `{[a,b], [0,u_β]}` and `{[0,a], [u_β,b]}`. -/
theorem tau_exchange {n β : ℕ} (h : β + 1 ≤ n) (a b : ℝ) :
    ∃ C, intervals (tau1 n a b β) = C + {(a, b), (0, u n a b β)} ∧
      intervals (tau2 n a b β) = C + {(0, a), (u n a b β, b)} := by
  refine ⟨(n - 1 - β) • {((0 : ℝ), a)} + (β - 1) • {((0 : ℝ), b)}, ?_, ?_⟩
  · simp only [intervals, tau1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_smul, add_zero, pair_eq]
    abel
  · have hn : n - β = (n - 1 - β) + 1 := by omega
    simp only [intervals, tau2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_smul, add_zero, pair_eq, hn, add_smul]
    abel

/-- `ρ'` and `ρ''` differ by the exchange of `{[0,a], [x,b]}` and `{[0,x], [a,b]}`. -/
theorem rho_exchange {n : ℕ} (h : 3 ≤ n) (a b : ℝ) :
    ∃ C, intervals (rho1 n a b) = C + {(0, a), (u n a b 2 / 2, b)} ∧
      intervals (rho2 n a b) = C + {(0, u n a b 2 / 2), (a, b)} := by
  refine ⟨(n - 3) • {((0 : ℝ), a)} + {(u n a b 2 / 2, b)}, ?_, ?_⟩
  · have hn : n - 2 = (n - 3) + 1 := by omega
    simp only [intervals, rho1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_smul, add_zero, pair_eq, hn, add_smul, two_smul]
    abel
  · simp only [intervals, rho2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_smul, add_zero, pair_eq]
    abel

/-- In `S_β` the two tuples have the same multiset of endpoints. -/
theorem endpoints_tau {n β : ℕ} (h : β + 1 ≤ n) (a b : ℝ) :
    endpoints (tau1 n a b β) = endpoints (tau2 n a b β) := by
  have hn : n - β = (n - 1 - β) + 1 := by omega
  simp only [endpoints, tau1, tau2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero, pair_eq, hn, add_smul]
  abel

/-- In `S_D` the two tuples have the same multiset of endpoints. -/
theorem endpoints_rho {n : ℕ} (h : 3 ≤ n) (a b : ℝ) :
    endpoints (rho1 n a b) = endpoints (rho2 n a b) := by
  have hn : n - 2 = (n - 3) + 1 := by omega
  simp only [endpoints, rho1, rho2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_smul, add_zero, pair_eq, hn, add_smul, two_smul]
  abel

/-- `ud l r` takes the same value at `x₁ ≤ x₂` if neither end lies in `(x₁, x₂]`. -/
lemma ud_eq_of_no_end {l r x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂) (hl : ¬(x₁ < l ∧ l ≤ x₂))
    (hr : ¬(x₁ < r ∧ r ≤ x₂)) : ud l r x₂ = ud l r x₁ := by
  unfold ud
  by_cases h1 : l ≤ x₁ ∧ x₁ < r
  · have h2 : l ≤ x₂ ∧ x₂ < r := ⟨h1.1.trans h12, by
      by_contra h; exact hr ⟨h1.2, not_lt.1 h⟩⟩
    simp only [h1, h2, and_self, ite_true]
  · have h2 : ¬(l ≤ x₂ ∧ x₂ < r) := by
      rintro ⟨h2l, h2r⟩
      by_cases hx : l ≤ x₁
      · exact h1 ⟨hx, lt_of_le_of_lt h12 h2r⟩
      · exact hl ⟨lt_of_not_ge hx, h2l⟩
    simp only [h1, h2, ite_false]

/-- The mixture of `τ'_β` and `τ''_β` with arbitrary weights `w₁`, `w₂`. -/
def Sw (n : ℕ) (a b : ℝ) (β : ℕ) (w₁ w₂ : ℝ) : Mix := [(w₁, tau1 n a b β), (w₂, tau2 n a b β)]

lemma S_eq_Sw (n : ℕ) (a b : ℝ) (β : ℕ) :
    S n a b β = Sw n a b β (u n a b β / b) (1 - u n a b β / b) := rfl

/-- **The jump of the marginal at `u_β`.** For points `x₁ < u_β ≤ x₂` in `(0, b)` with no other
endpoint (`a`) in `(x₁, x₂]`, the density of `w₁ m_{τ'_β} + w₂ m_{τ''_β}` increases from `x₁` to
`x₂` by `(w₂/(b - u_β) - w₁/u_β)/n`: only `[0,u_β]` and `[u_β,b]` change. -/
theorem Sw_jump {n β : ℕ} {a b w₁ w₂ x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁u : x₁ < u n a b β)
    (hux₂ : u n a b β ≤ x₂) (hx₂ : x₂ < b) (ha : ¬(x₁ < a ∧ a ≤ x₂)) :
    (Sw n a b β w₁ w₂).dens n x₂ - (Sw n a b β w₁ w₂).dens n x₁ =
      (w₂ / (b - u n a b β) - w₁ / u n a b β) / n := by
  set U := u n a b β
  have h12 : x₁ ≤ x₂ := by linarith
  have h0 : ¬(x₁ < 0 ∧ (0 : ℝ) ≤ x₂) := fun h => by linarith [h.1]
  have hbb : ¬(x₁ < b ∧ b ≤ x₂) := fun h => by linarith [h.2]
  have e0a := ud_eq_of_no_end h12 h0 ha
  have e0b := ud_eq_of_no_end h12 h0 hbb
  have eab := ud_eq_of_no_end h12 ha hbb
  have e0u1 : ud 0 U x₁ = U⁻¹ := by simp [ud, hx₁.le, hx₁u]
  have e0u2 : ud 0 U x₂ = 0 := by simp [ud, not_lt.2 hux₂]
  have eub1 : ud U b x₁ = 0 := by simp [ud, not_le.2 hx₁u]
  have eub2 : ud U b x₂ = (b - U)⁻¹ := by simp [ud, hux₂, hx₂]
  simp only [Sw, Mix.dens, Tup.dens, tau1, tau2, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Nat.cast_one, one_mul]
  rw [e0a, e0b, eab, e0u1, e0u2, eub1, eub2]
  rw [div_sub_div_same]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The weights `u_β/b` and `1 - u_β/b` of `S_β` are the only weights with sum `1` for which
the jump at `u_β` vanishes. -/
theorem jump_zero_iff {U b w₁ w₂ : ℝ} (hU : 0 < U) (hUb : U < b) (hw : w₁ + w₂ = 1) :
    w₂ / (b - U) - w₁ / U = 0 ↔ w₁ = U / b ∧ w₂ = 1 - U / b := by
  have hb : 0 < b := hU.trans hUb
  have hbU : 0 < b - U := by linarith
  rw [sub_eq_zero, div_eq_div_iff hbU.ne' hU.ne']
  constructor
  · intro h
    have h1 : w₁ = U / b := by
      rw [eq_div_iff hb.ne']
      have : w₂ = 1 - w₁ := by linarith
      subst this; nlinarith
    exact ⟨h1, by rw [← h1]; linarith⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; field_simp

/-- In particular the density of `S_β` has no jump at `u_β`. -/
theorem S_no_jump {n β : ℕ} {a b x₁ x₂ : ℝ} (hu0 : 0 < u n a b β) (hub : u n a b β < b) (hx₁ : 0 < x₁) (hx₁u : x₁ < u n a b β)
    (hux₂ : u n a b β ≤ x₂) (hx₂ : x₂ < b) (ha : ¬(x₁ < a ∧ a ≤ x₂)) :
    (S n a b β).dens n x₂ = (S n a b β).dens n x₁ := by
  rw [S_eq_Sw, ← sub_eq_zero, Sw_jump hx₁ hx₁u hux₂ hx₂ ha,
    ((jump_zero_iff hu0 hub (by ring)).2 ⟨rfl, rfl⟩), zero_div]

/-! ### The tight case `β = 1`, `b = n` -/

lemma u_tight (n : ℕ) (a : ℝ) : u n a n 1 = n - (n - 1) * a := by unfold u; push_cast; ring

/-- For `b = n`, `τ'_1` meets the polygon inequality with equality at `[a, b]`. -/
theorem tau1_tight {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    Tup.lenSum (tau1 n a n 1) = 2 * ((n : ℝ) - a) := by
  simp only [Tup.lenSum, tau1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    u_tight]
  rw [cast_sub3 (by omega : 1 + 1 ≤ n)]
  push_cast
  ring

/-- For `b = n`, `τ''_1` meets the polygon inequality with equality at `[u_1, b]`, whose length
is `(n - 1) a`. -/
theorem tau2_tight {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    Tup.lenSum (tau2 n a n 1) = 2 * ((n : ℝ) - u n a n 1) ∧
      (n : ℝ) - u n a n 1 = (n - 1) * a := by
  refine ⟨?_, by rw [u_tight]; ring⟩
  simp only [Tup.lenSum, tau2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    u_tight]
  rw [cast_sub2 (by omega : 1 ≤ n)]
  push_cast
  ring

section Tight

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- **A degenerate closed polygon is a segment.** If vectors with sum `0` meet the polygon
inequality with equality at `k`, then they are all parallel: `E_j = |E_j| e` for `j ≠ k` and
`E_k = -|E_k| e` for a unit vector `e`. -/
theorem collinear_of_tight (E : Fin n → V) (hs : ∑ j, E j = 0) (k : Fin n)
    (ht : 2 * ‖E k‖ = ∑ j, ‖E j‖) (hk : 0 < ‖E k‖) :
    ∃ e : V, ‖e‖ = 1 ∧ E k = -(‖E k‖ • e) ∧ ∀ j, j ≠ k → E j = ‖E j‖ • e := by
  set L := ‖E k‖
  set w := -E k
  have hw : w = ∑ j ∈ Finset.univ.erase k, E j := by
    have := Finset.add_sum_erase Finset.univ E (Finset.mem_univ k)
    rw [hs] at this
    simp only [w]; rw [neg_eq_iff_add_eq_zero, add_comm]; rw [add_comm]; exact this
  have hwn : ‖w‖ = L := norm_neg _
  have hrest : ∑ j ∈ Finset.univ.erase k, ‖E j‖ = L := by
    have := Finset.add_sum_erase Finset.univ (fun j => ‖E j‖) (Finset.mem_univ k)
    linarith
  have hle : ∀ j ∈ Finset.univ.erase k, ⟪w, E j⟫_ℝ ≤ L * ‖E j‖ := fun j _ => by
    rw [← hwn]; exact real_inner_le_norm _ _
  have hsum : ∑ j ∈ Finset.univ.erase k, ⟪w, E j⟫_ℝ = ∑ j ∈ Finset.univ.erase k, L * ‖E j‖ := by
    rw [← inner_sum, ← hw, real_inner_self_eq_norm_sq, hwn, ← Finset.mul_sum, hrest]; ring
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  refine ⟨L⁻¹ • w, ?_, ?_, fun j hj => ?_⟩
  · rw [norm_smul, hwn, norm_inv, Real.norm_eq_abs, abs_of_pos hk, inv_mul_cancel₀ hk.ne']
  · rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul, neg_neg]
  · have h1 := heq j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
    rw [← hwn, inner_eq_norm_mul_iff_real, hwn] at h1
    rw [smul_smul, mul_comm, ← smul_smul, h1, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]

/-- **Tight tuples give segments.** If the lengths `r_j - l_j` meet the polygon inequality with
equality at `k` (`l_k < r_k`), then for every choice of vectors `v_j` of lengths
`(r_j - l_j)/2` with sum `0` (as in Lemma 1) the vector `X_j = (l_j + r_j)/2 + v_j · ξ` runs, as
`ξ` varies, on the segment from `P₀` to `P₁`, where `P₀` has the coordinates `l_j` (`j ≠ k`) and
`r_k`, and `P₁` the coordinates `r_j` (`j ≠ k`) and `l_k`: `X = P₀ + ((1 + e · ξ)/2) (P₁ - P₀)`. -/
theorem segment_of_tight (l r : Fin n → ℝ) (v : Fin n → V) (hv : ∀ j, ‖v j‖ = (r j - l j) / 2)
    (hs : ∑ j, v j = 0) (k : Fin n) (ht : 2 * (r k - l k) = ∑ j, (r j - l j)) (hk : l k < r k) :
    ∃ e : V, ‖e‖ = 1 ∧ ∀ ξ : V, ∀ j, (l j + r j) / 2 + ⟪v j, ξ⟫_ℝ =
      (if j = k then r j else l j) +
        (1 + ⟪e, ξ⟫_ℝ) / 2 * ((if j = k then l j else r j) - (if j = k then r j else l j)) := by
  have ht' : 2 * ‖v k‖ = ∑ j, ‖v j‖ := by
    simp only [hv, ← Finset.sum_div]; rw [← ht]; ring
  obtain ⟨e, he, hek, hej⟩ := collinear_of_tight v hs k ht' (by rw [hv]; linarith)
  refine ⟨e, he, fun ξ j => ?_⟩
  by_cases hj : j = k
  · subst hj
    rw [hek, inner_neg_left, real_inner_smul_left, hv]
    simp only [ite_true]; rw [real_inner_comm]; ring
  · rw [hej j hj, real_inner_smul_left, hv]
    simp only [hj, ite_false]; rw [real_inner_comm]; ring

/-- `τ''_1` for `b = n = m + 2`, indexed: `[0, a]` for `j < m + 1`, `[u_1, n]` at the last index. -/
def tau2L (m : ℕ) (a : ℝ) (j : Fin (m + 2)) : ℝ := if j = Fin.last _ then u (m + 2) a (m + 2) 1 else 0
/-- Right ends of the indexed `τ''_1`. -/
def tau2R (m : ℕ) (a : ℝ) (j : Fin (m + 2)) : ℝ := if j = Fin.last _ then ((m + 2 : ℕ) : ℝ) else a

/-- `τ'_1` for `b = n = m + 3`, indexed: `[0, a]` for `j < m + 1`, `[0, u_1]` at `m + 1` and
`[a, n]` at the last index. -/
def tau1L (m : ℕ) (a : ℝ) (j : Fin (m + 3)) : ℝ := if j = Fin.last _ then a else 0
/-- Right ends of the indexed `τ'_1`. -/
def tau1R (m : ℕ) (a : ℝ) (j : Fin (m + 3)) : ℝ :=
  if j = Fin.last _ then ((m + 3 : ℕ) : ℝ)
  else if j = (Fin.last (m + 1)).castSucc then u (m + 3) a (m + 3) 1 else a

/-- **The tight case, `τ''_1`.** For `b = n` every joint mix of Lemma 1 type for `τ''_1` runs on
the segment from `(0, …, 0, n)` to `(a, …, a, n - (n-1) a)`. -/
theorem tau2_segment (m : ℕ) {a : ℝ} (ha : 0 < a) (v : Fin (m + 2) → V)
    (hv : ∀ j, ‖v j‖ = (tau2R m a j - tau2L m a j) / 2) (hs : ∑ j, v j = 0) :
    ∃ e : V, ‖e‖ = 1 ∧ ∀ ξ : V, ∀ j, (tau2L m a j + tau2R m a j) / 2 + ⟪v j, ξ⟫_ℝ =
      (if j = Fin.last _ then ((m + 2 : ℕ) : ℝ) else 0) + (1 + ⟪e, ξ⟫_ℝ) / 2 *
        ((if j = Fin.last _ then u (m + 2) a (m + 2) 1 else a) -
          (if j = Fin.last _ then ((m + 2 : ℕ) : ℝ) else 0)) := by
  have hu := u_tight (m + 2) a
  push_cast at hu
  have ht : 2 * (tau2R m a (Fin.last _) - tau2L m a (Fin.last _)) =
      ∑ j, (tau2R m a j - tau2L m a j) := by
    rw [Fin.sum_univ_castSucc]
    simp only [tau2R, tau2L, ite_true, Fin.castSucc_ne_last, ite_false, sub_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hu]; push_cast; ring
  have hk : tau2L m a (Fin.last _) < tau2R m a (Fin.last _) := by
    simp only [tau2R, tau2L, ite_true]; rw [hu]; push_cast; nlinarith
  obtain ⟨e, he, h⟩ := segment_of_tight _ _ v hv hs _ ht hk
  refine ⟨e, he, fun ξ j => ?_⟩
  rw [h ξ j]
  by_cases hj : j = Fin.last _ <;> simp [hj, tau2L, tau2R]

/-- **The tight case, `τ'_1`.** For `b = n` every joint mix of Lemma 1 type for `τ'_1` runs on
the segment from `(0, …, 0, n)` to `(a, …, a, n - (n-1) a, a)`. -/
theorem tau1_segment (m : ℕ) {a : ℝ} (ha1 : a ≤ 1) (v : Fin (m + 3) → V)
    (hv : ∀ j, ‖v j‖ = (tau1R m a j - tau1L m a j) / 2) (hs : ∑ j, v j = 0) :
    ∃ e : V, ‖e‖ = 1 ∧ ∀ ξ : V, ∀ j, (tau1L m a j + tau1R m a j) / 2 + ⟪v j, ξ⟫_ℝ =
      (if j = Fin.last _ then ((m + 3 : ℕ) : ℝ) else 0) + (1 + ⟪e, ξ⟫_ℝ) / 2 *
        ((if j = Fin.last _ then a else if j = (Fin.last (m + 1)).castSucc then
            u (m + 3) a (m + 3) 1 else a) -
          (if j = Fin.last _ then ((m + 3 : ℕ) : ℝ) else 0)) := by
  have hu := u_tight (m + 3) a
  push_cast at hu
  have ht : 2 * (tau1R m a (Fin.last _) - tau1L m a (Fin.last _)) =
      ∑ j, (tau1R m a j - tau1L m a j) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [tau1R, tau1L, ite_true, Fin.castSucc_ne_last, ite_false, sub_zero,
      Fin.castSucc_inj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hu]; push_cast; ring
  have hk : tau1L m a (Fin.last _) < tau1R m a (Fin.last _) := by
    simp only [tau1R, tau1L, ite_true]; push_cast; linarith
  obtain ⟨e, he, h⟩ := segment_of_tight _ _ v hv hs _ ht hk
  refine ⟨e, he, fun ξ j => ?_⟩
  rw [h ξ j]
  by_cases hj : j = Fin.last _
  · simp [hj, tau1L, tau1R]
  · by_cases hj' : j = (Fin.last (m + 1)).castSucc
    · simp [hj', tau1L, tau1R]
    · simp [hj, hj', tau1L, tau1R]

end Tight

/-! ### Remark after Theorem `t:thm:trap` -/

/-- Affine chord lengths `ℓ(x) = p + q x` and affine midpoints `m(x) = α + β x` have constant
totals over every tuple of abscissae with sum `n c`. -/
theorem affine_totals {n : ℕ} (p q α β c : ℝ) (x : Fin n → ℝ) (hsum : ∑ i, x i = n * c) :
    ∑ i, (p + q * x i) = n * (p + q * c) ∧ ∑ i, (α + β * x i) = n * (α + β * c) :=
  ⟨sum_affine_eq p q c x hsum, sum_affine_eq α β c x hsum⟩

/-- With affine lengths the polygon inequality only compares the longest chord with the mean
chord: if `ℓ(x_i) ≤ M` for all `i` and `n ℓ(c) ≥ 2 M`, the polygon inequality holds. -/
theorem polygon_of_affine {n : ℕ} (p q c M : ℝ) (x : Fin n → ℝ) (hsum : ∑ i, x i = n * c)
    (hM : ∀ i, p + q * x i ≤ M) (h2 : 2 * M ≤ n * (p + q * c)) (i : Fin n) :
    2 * (p + q * x i) ≤ ∑ j, (p + q * x j) := by
  rw [sum_affine_eq p q c x hsum]; linarith [hM i]

/-! #### Bodies symmetric in a line, and their affine images -/

/-- The fibre `{t : (x, t) ∈ K}` of a set of the plane over the abscissa `x`. -/
def fibre (K : Set (ℝ × ℝ)) (x : ℝ) : Set ℝ := {t | (x, t) ∈ K}

/-- For a set symmetric in the first axis, every fibre is symmetric, and its midpoint
`(inf + sup)/2` is `0`. -/
theorem fibre_mid_zero {K : Set (ℝ × ℝ)} (hK : ∀ p ∈ K, (p.1, -p.2) ∈ K) (x : ℝ) :
    (∀ t, t ∈ fibre K x ↔ -t ∈ fibre K x) ∧ (sInf (fibre K x) + sSup (fibre K x)) / 2 = 0 := by
  have hsym : ∀ t, t ∈ fibre K x ↔ -t ∈ fibre K x := fun t =>
    ⟨fun h => hK _ h, fun h => by have := hK _ h; simpa [fibre] using this⟩
  refine ⟨hsym, ?_⟩
  have : -fibre K x = fibre K x := by ext t; rw [Set.mem_neg, ← hsym]
  have h := Real.sInf_neg (fibre K x)
  rw [this] at h
  rw [h]; ring

variable (A : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ))

/-- **Collinear chord midpoints.** Let `K` be symmetric in the first axis and `A` an affine
bijection of the plane, `d = A(0,1) - A(0,0)` the image direction of the vertical chords. Then
the chord of `A(K)` through the point `A(x, 0)` in direction `d` is `{A(x,0) + t d : t ∈ S_x}`
for the symmetric fibre `S_x`, so it is symmetric about `A(x, 0)`; and these centres lie on the
line `A(ℝ × {0})`. -/
theorem affine_chord_centre {K : Set (ℝ × ℝ)} (hK : ∀ p ∈ K, (p.1, -p.2) ∈ K) (x : ℝ) :
    let d := A.linear (0, 1)
    {q | q ∈ A '' K ∧ ∃ t : ℝ, q = A (x, 0) + t • d} = (fun t => A (x, 0) + t • d) '' fibre K x ∧
      (∀ t, t ∈ fibre K x ↔ -t ∈ fibre K x) ∧
      (∀ q ∈ A '' K, (∃ t : ℝ, q = A (x, 0) + t • d) →
        (2 : ℝ) • A (x, 0) - q ∈ A '' K) ∧
      A (x, 0) = A (0, 0) + x • A.linear (1, 0) := by
  intro d
  have hA : ∀ s t : ℝ, A (s, t) = A (0, 0) + s • A.linear (1, 0) + t • d := by
    intro s t
    have h1 := A.toAffineMap.linear_apply_vsub (s, t) (0, 0)
    have h2 : ((s, t) : ℝ × ℝ) -ᵥ (0, 0) = s • (1, 0) + t • (0, 1) := by
      ext <;> simp
    rw [h2, map_add, map_smul, map_smul] at h1
    simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.linear_toAffineMap, vsub_eq_sub] at h1
    simp only [d]
    rw [add_assoc]
    exact (eq_add_of_sub_eq' h1.symm)
  have hx0 : ∀ t : ℝ, A (x, t) = A (x, 0) + t • d := fun t => by rw [hA x t, hA x 0]; simp
  refine ⟨?_, (fibre_mid_zero hK x).1, ?_, by rw [hA x 0]; simp⟩
  · ext q
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, t, ht⟩
      rw [← hx0] at ht
      have hpt : p = (x, t) := A.injective ht
      exact ⟨t, show (x, t) ∈ K from hpt ▸ hp, by simp only; rw [← hx0, hpt]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨(x, t), ht, hx0 t⟩, t, rfl⟩
  · rintro q ⟨p, hp, rfl⟩ ⟨t, ht⟩
    rw [← hx0] at ht
    have hpt : p = (x, t) := A.injective ht
    subst hpt
    refine ⟨(x, -t), hK _ hp, ?_⟩
    show A (x, -t) = (2 : ℝ) • A (x, 0) - A (x, t)
    rw [hx0 (-t), hx0 t, two_smul, neg_smul]; abel

/-! #### Trapezoids: every complete mix has the polygon property -/

lemma ae_coord_mem {n : ℕ} {F : Measure ℝ} {P : Measure (Fin n → ℝ)} (hP : IsCompleteMix n F P)
    {S : Set ℝ} (hF : F Sᶜ = 0) : ∀ᵐ x ∂P, ∀ i, x i ∈ S := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ y ∂(P.map fun x => x i), y ∈ S := by
    rw [hP.2.2 i]; exact ae_iff.2 hF
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

/-- The constant sum of a complete mix of a distribution on `[0, 1]` is `n` times its mean. -/
theorem completeMix_sum_eq {n : ℕ} {F : Measure ℝ} {P : Measure (Fin n → ℝ)}
    (hP : IsCompleteMix n F P) (hF : F (Icc 0 1)ᶜ = 0) {s : ℝ} (hs : ∀ᵐ x ∂P, ∑ i, x i = s) :
    s = n * ∫ y, y ∂F := by
  have hprob := hP.1
  have hcoord : ∀ i, Integrable (fun x : Fin n → ℝ => x i) P := by
    intro i
    refine Integrable.of_bound (measurable_pi_apply i).aestronglyMeasurable 1 ?_
    filter_upwards [ae_coord_mem hP hF] with x hx
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hx i).1, (hx i).2]
  have h1 : ∫ x, ∑ i, x i ∂P = s := by
    rw [integral_congr_ae hs]; simp
  have h2 : ∫ x, ∑ i, x i ∂P = ∑ _i : Fin n, ∫ y, y ∂F := by
    rw [integral_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => hcoord i]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : P.map (fun x => x i) = F := hP.2.2 i
    rw [← hm, integral_map (measurable_pi_apply i).aemeasurable
      (aestronglyMeasurable_id (μ := P.map fun x => x i))]
  rw [← h1, h2]; simp

/-- **Trapezoids** (remark after Theorem `t:thm:trap`): for every `n`-complete mix (`n ≥ 3`) of a
distribution on `[0, 1]` with mean `c = trapMean q`, the chord lengths `h(X_i)` satisfy the
polygon inequality almost surely. -/
theorem trap_polygon_ae {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 3 ≤ n)
    {F : Measure ℝ} {P : Measure (Fin n → ℝ)} (hP : IsCompleteMix n F P)
    (hF : F (Icc 0 1)ᶜ = 0) (hmean : ∫ y, y ∂F = trapMean q) :
    ∀ᵐ x ∂P, ∀ i, 2 * trapH q (x i) ≤ ∑ j, trapH q (x j) := by
  obtain ⟨s, hs⟩ := hP.2.1
  have hsc := completeMix_sum_eq hP hF hs
  rw [hmean] at hsc
  filter_upwards [hs, ae_coord_mem hP hF] with x hx hx01 i
  exact trap_polygon hq0 hq1 hn x hx01 (hx.trans hsc) i

/-! #### The disc -/

/-- The chord length of the disc of diameter `1` centred at `(1/2, 0)`. -/
def discH (x : ℝ) : ℝ := 2 * √(x * (1 - x))

/-- The vertical chord of the disc of diameter `1` at abscissa `x ∈ [0, 1]` is
`[-√(x(1-x)), √(x(1-x))]`, of length `discH x`. -/
theorem disc_chord {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    {y : ℝ | (x - 1 / 2) ^ 2 + y ^ 2 ≤ 1 / 4} = Icc (-√(x * (1 - x))) √(x * (1 - x)) ∧
      √(x * (1 - x)) - -√(x * (1 - x)) = discH x := by
  refine ⟨?_, by unfold discH; ring⟩
  ext y
  have hnn : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  simp only [mem_ofPred_eq, mem_Icc]
  rw [← abs_le, ← Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt_iff hnn]
  constructor <;> intro h <;> nlinarith

/-- For the disc the polygon inequality fails for the abscissae `(0, 0.6, 0.9)`, whose sum is
`3 c` with `c = 1/2`. -/
theorem disc_polygon_fails :
    (0 : ℝ) + 0.6 + 0.9 = 3 * (1 / 2) ∧
      ¬ (2 * discH 0.6 ≤ discH 0 + discH 0.6 + discH 0.9) := by
  refine ⟨by norm_num, ?_⟩
  have h0 : discH 0 = 0 := by simp [discH]
  have h9 : discH 0.9 = 0.6 := by
    unfold discH
    rw [show (0.9 : ℝ) * (1 - 0.9) = 0.3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have h6 : 0.6 < discH 0.6 := by
    unfold discH
    have : (0.3 : ℝ) < √(0.6 * (1 - 0.6)) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  rw [h0, h9]
  linarith

/-- **The fibre step of the construction** (remark after Theorem `t:thm:trap`). Given abscissae
`x_i` with sum `n c`, chord lengths `ℓ(x_i) ≥ 0` with the polygon inequality (`ℓ` need not be
affine) and affine chord midpoints `m(x) = α + β x`, the uniform distributions on the chords
`[m(x_i) - ℓ(x_i)/2, m(x_i) + ℓ(x_i)/2]` have a joint mix (that of Lemma 1, under the planar
Archimedes measure) whose coordinates add up to `n m(c)`. -/
theorem chord_jointMix {n : ℕ} (ℓ : ℝ → ℝ) (α β c : ℝ) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = n * c) (hℓ : ∀ i, 0 ≤ ℓ (x i)) (hpoly : ∀ i, 2 * ℓ (x i) ≤ ∑ j, ℓ (x j)) :
    ∃ P : Measure (Fin n → ℝ),
      IsJointMix (fun i => unifI (α + β * x i - ℓ (x i) / 2) (α + β * x i + ℓ (x i) / 2)) P ∧
        ∀ᵐ y ∂P, ∑ i, y i = n * (α + β * c) := by
  have hdim : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  obtain ⟨E, hE, hs⟩ := (polygon_iff_two (V := EuclideanSpace ℝ (Fin 2)) hdim
    (fun i => ℓ (x i) / 2) (fun i => by have := hℓ i; positivity)).2 (fun i => by
      have := hpoly i; rw [← Finset.sum_div]; linarith)
  obtain ⟨h1, h2⟩ := isJointMix_map_inner isArchimedesMeasure_archPlane
    (fun i => α + β * x i) E hs
  refine ⟨(archPlane).map (fun ξ j => α + β * x j + ⟪E j, ξ⟫_ℝ), ?_, ?_⟩
  · simpa only [hE] using h1
  · rw [sum_affine_eq α β c x hsum] at h2; exact h2

end Mixes.Remarks14
