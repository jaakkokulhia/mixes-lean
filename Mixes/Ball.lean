import Mixes.Bodies
import Mixes.Polygon
import Mixes.Uniform

/-!
# Balls: Lemma 50, the sufficiency half of Theorem 51, Proposition 52

This file formalises the rest of the subsection on balls in Section 17 of the paper
(`b:lem:frame`, `b:thm:ball`, `b:prop:radial`).

* `polyVec`, `polyVec_spec`: a Borel choice of the polygon of Lemma 49 (`b:lem:polygon`): the
  partition `G = {j < k}`, `H = {j > k}` at the index `k` where the partial sums of `λ` cross
  half the total, then `PolygonL49.polygon_of_partition`.
* `scalingProperty_of_rot`: if a probability measure `μ` on `H` is invariant under the rotations
  `y ↦ a y + b J y` (`a² + b² = 1`) of a complex structure `J` and `π : H → E` is linear, then
  `μ.map π` has the scaling property with constant `2`; the joint mix is
  `X_i = t_i + π (v_{i1} Y + v_{i2} J Y)` with `Y ∼ μ` and the polygon `v` of Lemma 49.
* **Theorem 51, sufficiency**: `ball_scalingProperty j` (all `j`, including `j = 1`),
  `ball_scalingPropertySet`, `ball_jointlyMixable_iff` (with `ball_necessity` from
  `Bodies.lean`), `ball_completelyMixable`. Even `j = 2k`: `μ = U(B)` and `J` the complex
  structure of `ℝ^{2k} = ℂ^k`. Odd `j`: `μ = liftBall j` on `ℝ^{j+1}` with density
  `c / √(1 - ‖y‖²)`, which is rotation invariant and projects to `U(B_j)` (`liftBall_map`).
  No hypothesis is needed. `ball_scalingProperty (m' + 1)` is the hypothesis `hball` of
  `FrustumMix.circCone_sufficiency` / `circCone_completelyMixable_iff`, and
  `ball_completelyMixable d (n := 3)` is the hypothesis `hball` of `SymmCor.lean`.
* `SphereUniqueness E`: the cited fact that a rotation-invariant probability measure on the unit
  sphere is unique. It is a hypothesis of Lemma 50 and of the sufficiency in Proposition 52 only.
* `polar_of_unique`: from it, every rotation-invariant probability is the law of `R Θ` with `R`
  its radius and `Θ` uniform on the sphere, independent.
* **Lemma 50**: `lemma50` (Gaussian frame `g₁, g₂`; `ae_frame_good`: almost surely defined).
* **Proposition 52**: `prop52_necessity` (no hypothesis), `prop52_sufficiency` (the explicit
  joint mix `radialMix`, sum `0`), `prop52`, `completelyMixable_of_isRotInv`.

The construction in Theorem 51 differs from the paper's `t_i + R (v_{i1} g₁ + v_{i2} g₂)`: a
complex structure replaces the random frame, which avoids the uniqueness on the sphere.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Mixes

namespace Ball

/-! ### The source of randomness -/

/-- The first variable of the uniform sequence, as a point of `unitInterval`. -/
def firstI (ω : ℕ → ℝ) : unitInterval := projIcc 0 1 zero_le_one (ω 0)

lemma measurable_firstI : Measurable firstI :=
  continuous_projIcc.measurable.comp (measurable_pi_apply 0)

lemma unifI_zero_one : unifI 0 1 = volume.restrict (Icc (0 : ℝ) 1) := by
  simp [unifI]

lemma map_firstI : unifSeq.map firstI = (volume : Measure unitInterval) := by
  have h1 : unifSeq.map (fun ω => ω 0) = unifI 0 1 := by
    unfold unifSeq; exact Measure.infinitePi_map_eval _ 0
  have h2 : (volume : Measure unitInterval) =
      (volume.restrict (Icc (0 : ℝ) 1)).map (projIcc 0 1 zero_le_one) := by
    rw [← unitInterval.measurePreserving_subtypeVal.map_eq,
      Measure.map_map continuous_projIcc.measurable measurable_subtypeVal]
    have : (projIcc (0 : ℝ) 1 zero_le_one ∘ Subtype.val : unitInterval → unitInterval) = id := by
      funext x; exact projIcc_val zero_le_one x
    rw [this, Measure.map_id]
  rw [h2, ← unifI_zero_one, ← h1]
  exact (Measure.map_map continuous_projIcc.measurable (measurable_pi_apply 0)).symm

/-! ### A Borel choice of the polygon of Lemma 49 -/

section Polygon

open PolygonL49

variable {n : ℕ}

/-- The partial sums `Λ_i = ∑_{j ≤ i} λ_j`. -/
def psum (lam : Fin n → ℝ) (i : Fin n) : ℝ := ∑ j ∈ Finset.Iic i, lam j

/-- The partial sums `Λ'_i = ∑_{j < i} λ_j`. -/
def psum' (lam : Fin n → ℝ) (i : Fin n) : ℝ := ∑ j ∈ Finset.Iio i, lam j

/-- `k` is the split index: the partial sums cross half the total at `k`. -/
def IsSplit (lam : Fin n → ℝ) (k : Fin n) : Prop :=
  2 * psum' lam k < ∑ j, lam j ∧ ∑ j, lam j ≤ 2 * psum lam k

open Classical in
/-- The polygon of Lemma 49 for the partition `G = {j < k}`, `H = {j > k}` at the split index
`k`, as a Borel function of `λ`: the first two coordinates of the vectors `vecs`. (Off the
admissible set, a sum over all split indices, which is irrelevant.) -/
def polyVec (lam : Fin n → ℝ) (j : Fin n) : ℝ × ℝ :=
  ∑ k, if IsSplit lam k then
    (vecs lam k (Finset.Iio k) (Finset.Ioi k) j 0, vecs lam k (Finset.Iio k) (Finset.Ioi k) j 1)
    else 0

lemma measurable_psum (i : Fin n) : Measurable fun lam : Fin n → ℝ => psum lam i :=
  Finset.measurable_sum _ fun j _ => measurable_pi_apply j

lemma measurable_psum' (i : Fin n) : Measurable fun lam : Fin n → ℝ => psum' lam i :=
  Finset.measurable_sum _ fun j _ => measurable_pi_apply j

lemma measurableSet_isSplit (k : Fin n) : MeasurableSet {lam : Fin n → ℝ | IsSplit lam k} := by
  have hL : Measurable fun lam : Fin n → ℝ => ∑ j, lam j :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  exact (measurableSet_lt ((measurable_psum' k).const_mul 2) hL).inter
    (measurableSet_le hL ((measurable_psum k).const_mul 2))

lemma measurable_vecs (k : Fin n) (G H : Finset (Fin n)) (j : Fin n) (c : Fin 3) :
    Measurable fun lam : Fin n → ℝ => vecs lam k G H j c := by
  have hS : Measurable fun lam : Fin n → ℝ => ∑ i ∈ G, lam i :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  have hT : Measurable fun lam : Fin n → ℝ => ∑ i ∈ H, lam i :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  have hk : Measurable fun lam : Fin n → ℝ => lam k := measurable_pi_apply k
  have hj : Measurable fun lam : Fin n → ℝ => lam j := measurable_pi_apply j
  have hx : Measurable fun lam : Fin n → ℝ => xco (lam k) (∑ i ∈ G, lam i) (∑ i ∈ H, lam i) := by
    unfold xco; fun_prop
  have hy : Measurable fun lam : Fin n → ℝ => yco (lam k) (∑ i ∈ G, lam i) (∑ i ∈ H, lam i) := by
    unfold yco; exact (((hT.pow_const 2).sub (hx.pow_const 2))).sqrt
  unfold vecs
  split_ifs
  · fin_cases c <;> simp [Ek, hk]
  · fin_cases c <;> simp [EG] <;> fun_prop
  · fin_cases c <;> simp [EH] <;> fun_prop

lemma measurable_polyVec (j : Fin n) : Measurable fun lam : Fin n → ℝ => polyVec lam j := by
  classical
  unfold polyVec
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.ite (measurableSet_isSplit k) ?_ measurable_const
  exact (measurable_vecs _ _ _ _ _).prodMk (measurable_vecs _ _ _ _ _)

lemma iic_eq_insert (k : Fin n) : Finset.Iic k = insert k (Finset.Iio k) := by
  ext j; simp [le_iff_lt_or_eq, or_comm]

lemma psum_eq (lam : Fin n → ℝ) (k : Fin n) : psum lam k = psum' lam k + lam k := by
  unfold psum psum'
  rw [iic_eq_insert, Finset.sum_insert (by simp), add_comm]

lemma sum_eq_split (lam : Fin n → ℝ) (k : Fin n) :
    ∑ j, lam j = psum' lam k + lam k + ∑ j ∈ Finset.Ioi k, lam j := by
  rw [← psum_eq, psum, ← Finset.sum_union]
  · congr 1; ext j; simp [le_or_gt]
  · rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; exact absurd ha (not_le.2 hb)

lemma exists_isSplit {m : ℕ} (lam : Fin (m + 1) → ℝ) (hL : 0 < ∑ j, lam j) :
    ∃ k, IsSplit lam k := by
  classical
  set P := Finset.univ.filter fun i => ∑ j, lam j ≤ 2 * psum lam i
  have hlast : Fin.last m ∈ P := by
    have : psum lam (Fin.last m) = ∑ j, lam j := by
      unfold psum; congr 1; ext j; simp [Fin.le_last]
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, this]
    linarith
  have hne : P.Nonempty := ⟨_, hlast⟩
  set k := P.min' hne
  have hk : k ∈ P := P.min'_mem hne
  refine ⟨k, ?_, (Finset.mem_filter.1 hk).2⟩
  by_contra hcon
  push Not at hcon
  rcases (Finset.Iio k).eq_empty_or_nonempty with h0 | h0
  · simp [psum', h0] at hcon; linarith
  · set p := (Finset.Iio k).max' h0
    have hp : p < k := Finset.mem_Iio.1 ((Finset.Iio k).max'_mem h0)
    have hIio : Finset.Iio k = Finset.Iic p := by
      ext j; simp only [Finset.mem_Iio, Finset.mem_Iic]
      exact ⟨fun h => (Finset.Iio k).le_max' j (by simpa using h), fun h => lt_of_le_of_lt h hp⟩
    have hpP : p ∈ P := by
      have : psum lam p = psum' lam k := by unfold psum psum'; rw [hIio]
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, this]
      exact hcon
    exact absurd (P.min'_le p hpP) (not_le.2 hp)

lemma isSplit_unique {lam : Fin n → ℝ} (hnn : ∀ j, 0 ≤ lam j) {k k' : Fin n}
    (hk : IsSplit lam k) (hk' : IsSplit lam k') : k = k' := by
  have key : ∀ a b : Fin n, a < b → IsSplit lam a → IsSplit lam b → False := by
    intro a b hab ha hb
    have : psum lam a ≤ psum' lam b :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => by simp at hj ⊢; exact lt_of_le_of_lt hj hab) (fun j _ _ => hnn j)
    linarith [ha.2, hb.1]
  rcases lt_trichotomy k k' with h | h | h
  · exact (key _ _ h hk hk').elim
  · exact h
  · exact (key _ _ h hk' hk).elim

/-- The polygon at the split index: lengths `λ_j` and sum `0` (Lemma 49 for the partition
`{j < k}`, `{j > k}`). -/
lemma vecs_split {lam : Fin n → ℝ} (hnn : ∀ j, 0 ≤ lam j) (hpoly : ∀ i, 2 * lam i ≤ ∑ j, lam j)
    {k : Fin n} (hk : IsSplit lam k) :
    (∀ j, vecs lam k (Finset.Iio k) (Finset.Ioi k) j 0 ^ 2 +
      vecs lam k (Finset.Iio k) (Finset.Ioi k) j 1 ^ 2 = lam j ^ 2) ∧
    ∑ j, vecs lam k (Finset.Iio k) (Finset.Ioi k) j = 0 := by
  have hsum := sum_eq_split lam k
  have hpos : 0 < lam k := by have := psum_eq lam k; linarith [hk.1, hk.2]
  have hST : |∑ j ∈ Finset.Iio k, lam j - ∑ j ∈ Finset.Ioi k, lam j| ≤ lam k := by
    have h1 := hk.1; have h2 := hk.2
    rw [psum_eq] at h2
    unfold psum' at h1 h2 hsum
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h3, hlen, hs⟩ := polygon_of_partition lam hnn k hpos (hpoly k) _ _
    (by rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; exact absurd ha (not_lt.2 hb.le))
    (fun j => by
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]; exact ne_iff_lt_or_gt) hST
  refine ⟨fun j => ?_, hs⟩
  have hl := hlen j
  unfold len at hl
  have h0 : 0 ≤ ∑ i, vecs lam k (Finset.Iio k) (Finset.Ioi k) j i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have := Real.sq_sqrt h0
  rw [hl, Fin.sum_univ_three, h3 j] at this
  linarith

/-- **The polygon** (Lemma 49, Borel version): for `λ ≥ 0`, not all zero, with
`2 max λ ≤ ∑ λ`, the planar vectors `polyVec λ j` have lengths `λ_j` and sum `0`. -/
theorem polyVec_spec {m : ℕ} {lam : Fin (m + 1) → ℝ} (hnn : ∀ j, 0 ≤ lam j)
    (hne : ∃ j, lam j ≠ 0) (hpoly : ∀ i, 2 * lam i ≤ ∑ j, lam j) :
    (∀ j, (polyVec lam j).1 ^ 2 + (polyVec lam j).2 ^ 2 = lam j ^ 2) ∧
      ∑ j, polyVec lam j = 0 := by
  classical
  have hL : 0 < ∑ j, lam j := by
    obtain ⟨j, hj⟩ := hne
    exact lt_of_lt_of_le (lt_of_le_of_ne (hnn j) (Ne.symm hj))
      (Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j))
  obtain ⟨k, hk⟩ := exists_isSplit lam hL
  have hv : ∀ j, polyVec lam j =
      (vecs lam k (Finset.Iio k) (Finset.Ioi k) j 0,
        vecs lam k (Finset.Iio k) (Finset.Ioi k) j 1) := by
    intro j
    unfold polyVec
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b _ hb
      simp [show ¬ IsSplit lam b from fun h => hb (isSplit_unique hnn h hk)]
    · simp
  obtain ⟨h1, h2⟩ := vecs_split hnn hpoly hk
  refine ⟨fun j => by rw [hv]; exact h1 j, ?_⟩
  simp only [hv]
  ext
  · rw [Prod.fst_sum]; simpa using congrFun h2 0
  · rw [Prod.snd_sum]; simpa using congrFun h2 1

end Polygon

/-! ### Joint mixes from a planar rotation -/

section Rotation

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The construction: `X_i = t_i + π (a_i Y + b_i J Y)` with `(a_i, b_i) = polyVec λ i` and the
sample `Y = Y₀ ω₀` of `μ` taken from the first uniform variable. -/
def rotMix (Y₀ : unitInterval → H) (J : H →L[ℝ] H) (π : H →L[ℝ] E) {n : ℕ}
    (p : (Fin n → ℝ) × (Fin n → E)) (ω : ℕ → ℝ) : Fin n → E :=
  fun i => p.2 i + π ((polyVec p.1 i).1 • Y₀ (firstI ω) + (polyVec p.1 i).2 • J (Y₀ (firstI ω)))

lemma measurable_rotMix {Y₀ : unitInterval → H} (hY : Measurable Y₀) (J : H →L[ℝ] H)
    (π : H →L[ℝ] E) (n : ℕ) : Measurable (Function.uncurry (rotMix Y₀ J π (n := n))) := by
  have hYω : Measurable fun q : ((Fin n → ℝ) × (Fin n → E)) × (ℕ → ℝ) => Y₀ (firstI q.2) :=
    hY.comp (measurable_firstI.comp measurable_snd)
  refine measurable_pi_iff.2 fun i => ?_
  have hv : Measurable fun q : ((Fin n → ℝ) × (Fin n → E)) × (ℕ → ℝ) => polyVec q.1.1 i :=
    (measurable_polyVec i).comp (measurable_fst.comp measurable_fst)
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
    (π.measurable.comp ((hv.fst.smul hYω).add (hv.snd.smul (J.measurable.comp hYω))))

/-- **Joint mixes from a planar rotation.** Let `μ` be a probability measure on `H`, invariant
under the maps `y ↦ a y + b J y` with `a² + b² = 1` (the rotations of a complex structure `J`),
and let `π : H → E` be linear. Then `μ.map π` has the scaling property with constant `2`: the
law of `X_i = t_i + π (a_i Y + b_i J Y)`, with `Y ∼ μ` and the planar polygon `(a_i, b_i)` of
Lemma 49 for the lengths `λ_i`, is a joint mix of the `U(t_i + λ_i K)`. -/
theorem scalingProperty_of_rot (μ : Measure H) [IsProbabilityMeasure μ] (J : H →L[ℝ] H)
    (hrot : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → μ.map (fun y => a • y + b • J y) = μ)
    (π : H →L[ℝ] E) : ScalingProperty (μ.map π) 2 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Y₀, hY, hYmap⟩ := μ.exists_measurable_map_eq
  refine ⟨rotMix Y₀ J π, measurable_rotMix hY J π _, fun lam t hlam hne hm => ?_⟩
  obtain ⟨hlen, hsum⟩ := polyVec_spec hlam hne hm
  have hΦ : Measurable (rotMix Y₀ J π (lam, t)) :=
    (measurable_rotMix hY J π _).comp measurable_prodMk_left
  have hlaw : unifSeq.map (Y₀ ∘ firstI) = μ := by
    rw [← hYmap, ← map_firstI, Measure.map_map hY measurable_firstI]
  refine ⟨inferInstance, ⟨∑ i, t i, ?_⟩, fun i => ?_⟩
  · rw [ae_map_iff hΦ.aemeasurable (measurableSet_sum_eq' _)]
    refine Filter.Eventually.of_forall fun ω => ?_
    have h1 : ∑ i, (polyVec lam i).1 = 0 := by rw [← Prod.fst_sum, hsum]; rfl
    have h2 : ∑ i, (polyVec lam i).2 = 0 := by rw [← Prod.snd_sum, hsum]; rfl
    simp only [rotMix, Finset.sum_add_distrib, ← map_sum, ← Finset.sum_smul, h1, h2, zero_smul,
      add_zero, map_zero]
  · set a := (polyVec lam i).1
    set b := (polyVec lam i).2
    have hg : Measurable fun y : H => t i + π (a • y + b • J y) := by fun_prop
    have e1 : (unifSeq.map (rotMix Y₀ J π (lam, t))).map (fun x => x i) =
        μ.map (fun y => t i + π (a • y + b • J y)) := by
      rw [Measure.map_map (measurable_pi_apply i) hΦ, ← hlaw,
        Measure.map_map hg (hY.comp measurable_firstI)]
      rfl
    rw [e1]
    dsimp only
    rw [Measure.map_map (by fun_prop) π.measurable]
    rcases (hlam i).eq_or_lt with h0 | hpos
    · have hab : a = 0 ∧ b = 0 := by
        have := hlen i; rw [← h0] at this
        constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
      congr 1
      funext y
      simp [hab.1, hab.2, ← h0]
    · have hcd : (a / lam i) ^ 2 + (b / lam i) ^ 2 = 1 := by
        rw [div_pow, div_pow, ← add_div, hlen i, div_self (by positivity)]
      have hf : (fun y => t i + π (a • y + b • J y)) =
          ((fun x => t i + lam i • x) ∘ π) ∘ (fun y => (a / lam i) • y + (b / lam i) • J y) := by
        funext y
        simp only [Function.comp, map_add, map_smul, smul_add, smul_smul]
        congr 3 <;> field_simp
      rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), hrot _ _ hcd]

end Rotation

/-! ### Complex structures and rotation-invariant measures -/

section Invariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The rotation `y ↦ a y + b J y` (`a² + b² = 1`) of a complex structure `J` as a linear
isometry equivalence. -/
def rotIso (J : H →L[ℝ] H) (hJn : ∀ y, ‖J y‖ = ‖y‖) (hJo : ∀ y, ⟪y, J y⟫_ℝ = 0) (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) : H ≃ₗᵢ[ℝ] H :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := a • LinearMap.id + b • J.toLinearMap
      norm_map' := fun y => by
        have h : ‖a • y + b • J y‖ ^ 2 = ‖y‖ ^ 2 := by
          rw [norm_add_sq_real, inner_smul_left, inner_smul_right, hJo, norm_smul, norm_smul,
            hJn, Real.norm_eq_abs, Real.norm_eq_abs]
          simp only [RCLike.conj_to_real, mul_zero, mul_pow, sq_abs]
          linear_combination ‖y‖ ^ 2 * hab
        have := congrArg Real.sqrt h
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this }
    rfl

omit [MeasurableSpace H] [BorelSpace H] in
lemma rotIso_apply (J : H →L[ℝ] H) (hJn : ∀ y, ‖J y‖ = ‖y‖) (hJo : ∀ y, ⟪y, J y⟫_ℝ = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (y : H) :
    rotIso J hJn hJo a b hab y = a • y + b • J y := rfl

omit [BorelSpace H] in
/-- A measure invariant under all linear isometries is invariant under the rotations of a
complex structure. -/
lemma rot_invariant {μ : Measure H} (hμ : ∀ L : H ≃ₗᵢ[ℝ] H, μ.map L = μ) (J : H →L[ℝ] H)
    (hJn : ∀ y, ‖J y‖ = ‖y‖) (hJo : ∀ y, ⟪y, J y⟫_ℝ = 0) :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → μ.map (fun y => a • y + b • J y) = μ :=
  fun a b hab => hμ (rotIso J hJn hJo a b hab)

/-- The uniform distribution on the unit ball is invariant under linear isometries. -/
lemma unifSet_ball_map_iso (L : H ≃ₗᵢ[ℝ] H) :
    (unifSet (Metric.closedBall (0 : H) 1)).map L = unifSet (Metric.closedBall (0 : H) 1) := by
  have hK : L ⁻¹' Metric.closedBall (0 : H) 1 = Metric.closedBall 0 1 := by
    ext y; simp
  ext A hA
  rw [Measure.map_apply L.continuous.measurable hA]
  simp only [unifSet, smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply (L.continuous.measurable hA), Measure.restrict_apply hA]
  congr 1
  rw [show L ⁻¹' A ∩ Metric.closedBall 0 1 = L ⁻¹' (A ∩ Metric.closedBall 0 1) by
      rw [preimage_inter, hK],
    (LinearIsometryEquiv.measurePreserving L).measure_preimage
      (hA.inter Metric.isClosed_closedBall.measurableSet).nullMeasurableSet]

/-- A measure with a radial density is invariant under linear isometries. -/
lemma withDensity_radial_map_iso (g : ℝ → ℝ≥0∞) (hg : Measurable g) (L : H ≃ₗᵢ[ℝ] H) :
    (volume.withDensity fun y : H => g ‖y‖).map L = volume.withDensity fun y : H => g ‖y‖ := by
  have hm : Measurable fun y : H => g ‖y‖ := hg.comp measurable_norm
  ext A hA
  rw [Measure.map_apply L.continuous.measurable hA, withDensity_apply _
    (L.continuous.measurable hA), withDensity_apply _ hA, ← lintegral_indicator
    (L.continuous.measurable hA), ← lintegral_indicator hA,
    ← (LinearIsometryEquiv.measurePreserving L).lintegral_comp_emb
      L.toHomeomorph.measurableEmbedding (A.indicator fun y : H => g ‖y‖)]
  congr 1
  funext y
  by_cases h : L y ∈ A <;> simp [indicator, h]

end Invariance

/-! ### The complex structure on `ℝ^{2k}` -/

section Cplx

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The complex structure `(u, w) ↦ (-w, u)` transported along `e : ι ≃ κ ⊕ κ`. -/
def cplxFun (e : ι ≃ κ ⊕ κ) (y : ι → ℝ) : ι → ℝ :=
  fun m => Sum.elim (fun i => -y (e.symm (Sum.inr i))) (fun i => y (e.symm (Sum.inl i))) (e m)

/-- The complex structure as a continuous linear map of `EuclideanSpace ℝ ι`. -/
def cplx (e : ι ≃ κ ⊕ κ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (cplxFun e (WithLp.ofLp y))
      map_add' := fun y z => by
        ext m; simp only [cplxFun, PiLp.add_apply]
        rcases e m with i | i <;> simp; ring
      map_smul' := fun c y => by
        ext m; simp only [cplxFun, PiLp.smul_apply, RingHom.id_apply]
        rcases e m with i | i <;> simp }

omit [Fintype κ] in
lemma cplx_apply (e : ι ≃ κ ⊕ κ) (y : EuclideanSpace ℝ ι) (m : ι) :
    cplx e y m = Sum.elim (fun i => -y (e.symm (Sum.inr i))) (fun i => y (e.symm (Sum.inl i)))
      (e m) := rfl

lemma sum_equiv_sum (e : ι ≃ κ ⊕ κ) (f : ι → ℝ) :
    ∑ m, f m = ∑ i, (f (e.symm (Sum.inl i)) + f (e.symm (Sum.inr i))) := by
  rw [← e.symm.sum_comp, Fintype.sum_sum_type, Finset.sum_add_distrib]

lemma cplx_norm (e : ι ≃ κ ⊕ κ) (y : EuclideanSpace ℝ ι) : ‖cplx e y‖ = ‖y‖ := by
  have : ‖cplx e y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, sum_equiv_sum e,
      sum_equiv_sum e (fun m => ‖y m‖ ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [cplx_apply]; ring
  have := congrArg Real.sqrt this
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

lemma cplx_inner (e : ι ≃ κ ⊕ κ) (y : EuclideanSpace ℝ ι) : ⟪y, cplx e y⟫_ℝ = 0 := by
  rw [PiLp.inner_apply, sum_equiv_sum e]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [cplx_apply]; ring

end Cplx

/-! ### Even dimensions -/

/-- The closed unit ball of `ℝ^j`. -/
abbrev B (j : ℕ) : Set (EuclideanSpace ℝ (Fin j)) := Metric.closedBall 0 1

instance isProb_unifBall (j : ℕ) : IsProbabilityMeasure (unifSet (B j)) :=
  unifSet_isProb (Metric.measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne

/-- **Theorem 51 (sufficiency) in even dimension `2k`**: `U(B)` is invariant under the rotations
of a complex structure on `ℝ^{2k} = ℂ^k`. -/
theorem scalingProperty_ball_even (k : ℕ) : ScalingProperty (unifSet (B (2 * k))) 2 := by
  set e : Fin (2 * k) ≃ Fin k ⊕ Fin k := (finCongr (two_mul k)).trans finSumFinEquiv.symm
  have h := scalingProperty_of_rot (unifSet (B (2 * k))) (cplx e)
    (rot_invariant unifSet_ball_map_iso _ (cplx_norm e) (cplx_inner e))
    (ContinuousLinearMap.id ℝ _)
  simpa using h

/-! ### Odd dimensions: a lift to `ℝ^{j+1}` -/

section Lift

variable (j : ℕ)

/-- Dropping the last coordinate, `ℝ^{j+1} → ℝ^j`. -/
def dropLast : EuclideanSpace ℝ (Fin (j + 1)) →L[ℝ] EuclideanSpace ℝ (Fin j) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun i => y (Fin.castSucc i)
      map_add' := fun y z => by ext i; simp
      map_smul' := fun c y => by ext i; simp }

lemma dropLast_apply (y : EuclideanSpace ℝ (Fin (j + 1))) (i : Fin j) :
    dropLast j y i = y (Fin.castSucc i) := rfl

/-- `ℝ^{j+1} ≃ ℝ^j × ℝ`, measure preserving. -/
def splitEquiv : EuclideanSpace ℝ (Fin (j + 1)) ≃ᵐ EuclideanSpace ℝ (Fin j) × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin (j + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last j)).trans
      (MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin j → ℝ))
          (MeasurableEquiv.refl ℝ))))

lemma splitEquiv_apply (y : EuclideanSpace ℝ (Fin (j + 1))) :
    splitEquiv j y = (dropLast j y, y (Fin.last j)) := by
  simp [splitEquiv, MeasurableEquiv.piFinSuccAbove, dropLast]
  rfl

lemma measurePreserving_splitEquiv : MeasurePreserving (splitEquiv j) := by
  unfold splitEquiv
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans
    ((volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last j)).trans
      ((Measure.measurePreserving_swap (μ := volume) (ν := volume)).trans ?_))
  exact (PiLp.volume_preserving_toLp (Fin j)).prod (MeasurePreserving.id volume)

lemma norm_sq_split (y : EuclideanSpace ℝ (Fin (j + 1))) :
    ‖y‖ ^ 2 = ‖dropLast j y‖ ^ 2 + y (Fin.last j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [dropLast_apply]

end Lift

section LiftMeasure

open Real

variable (j : ℕ)

/-- The normalising constant `1 / (π vol(B_j))`. -/
def liftConst : ℝ := 1 / (π * (volume (B j)).toReal)

lemma volB_toReal_pos : 0 < (volume (B j)).toReal :=
  ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne

lemma liftConst_pos : 0 < liftConst j := by
  have := volB_toReal_pos j; unfold liftConst; positivity

/-- The radial profile `c / √(1 - r²)` of the lift (`0` for `r ≥ 1`). -/
def liftG (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (liftConst j * (1 / √(1 - r ^ 2)))

lemma measurable_liftG : Measurable (liftG j) := by unfold liftG; fun_prop

/-- **The lift**: the measure on `ℝ^{j+1}` with density `c / √(1 - ‖y‖²)` on the unit ball, the
law of the projection of a uniform point of `S^{j+1}` to `ℝ^{j+1}` (this identification is not
used). Its projection to `ℝ^j` is `U(B_j)` (`liftBall_map`). -/
def liftBall : Measure (EuclideanSpace ℝ (Fin (j + 1))) :=
  volume.withDensity fun y => liftG j ‖y‖

lemma lintegral_lift_fibre (x : EuclideanSpace ℝ (Fin j)) :
    ∫⁻ s : ℝ, ENNReal.ofReal (liftConst j * (1 / √(1 - ‖x‖ ^ 2 - s ^ 2))) =
      (Metric.ball (0 : EuclideanSpace ℝ (Fin j)) 1).indicator
        (fun _ => ENNReal.ofReal (liftConst j * π)) x := by
  have hc := liftConst_pos j
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin j)) 1
  · rw [indicator_of_mem hx]
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
    have hr : 0 < √(1 - ‖x‖ ^ 2) := Real.sqrt_pos.2 (by linarith)
    have hr2 : √(1 - ‖x‖ ^ 2) ^ 2 = 1 - ‖x‖ ^ 2 := Real.sq_sqrt (by linarith)
    have : ∀ s : ℝ, ENNReal.ofReal (liftConst j * (1 / √(1 - ‖x‖ ^ 2 - s ^ 2))) =
        ENNReal.ofReal (liftConst j) * ENNReal.ofReal (1 / √(√(1 - ‖x‖ ^ 2) ^ 2 - s ^ 2)) := by
      intro s; rw [hr2, ENNReal.ofReal_mul hc.le]
    simp_rw [this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inv_sqrt hr,
      ← ENNReal.ofReal_mul hc.le]
  · rw [indicator_of_notMem hx]
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hx
    have : ∀ s : ℝ, 1 - ‖x‖ ^ 2 - s ^ 2 ≤ 0 := fun s => by nlinarith [sq_nonneg s]
    simp [Real.sqrt_eq_zero'.2 (this _)]

lemma volume_inter_ball (A : Set (EuclideanSpace ℝ (Fin j))) :
    volume (A ∩ Metric.ball 0 1) = volume (A ∩ B j) := by
  refine le_antisymm (measure_mono (inter_subset_inter_right _ Metric.ball_subset_closedBall)) ?_
  calc volume (A ∩ B j) ≤ volume (A ∩ Metric.ball 0 1 ∪ Metric.sphere 0 1) := by
        refine measure_mono fun y hy => ?_
        rcases eq_or_lt_of_le (mem_closedBall_zero_iff.1 hy.2) with h | h
        · exact Or.inr (mem_sphere_zero_iff_norm.2 h)
        · exact Or.inl ⟨hy.1, mem_ball_zero_iff.2 h⟩
    _ ≤ volume (A ∩ Metric.ball 0 1) + volume (Metric.sphere (0 : EuclideanSpace ℝ (Fin j)) 1) :=
        measure_union_le _ _
    _ = volume (A ∩ Metric.ball 0 1) := by
        rw [Measure.addHaar_sphere_of_ne_zero _ _ one_ne_zero, add_zero]

/-- The projection of the lift to `ℝ^j` is the uniform distribution on the ball. -/
theorem liftBall_map : (liftBall j).map (dropLast j) = unifSet (B j) := by
  have hd := (dropLast j).measurable
  set F : EuclideanSpace ℝ (Fin j) × ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (liftConst j * (1 / √(1 - ‖z.1‖ ^ 2 - z.2 ^ 2))) with hF
  have hFm : Measurable F := by rw [hF]; fun_prop
  ext A hA
  rw [Measure.map_apply hd hA, liftBall, withDensity_apply _ (hd hA), ← lintegral_indicator (hd hA)]
  have hpt : ∀ y, (dropLast j ⁻¹' A).indicator (fun y => liftG j ‖y‖) y =
      (Prod.fst ⁻¹' A).indicator F (splitEquiv j y) := by
    intro y
    rw [splitEquiv_apply]
    by_cases h : dropLast j y ∈ A
    · rw [indicator_of_mem (show y ∈ dropLast j ⁻¹' A from h), indicator_of_mem
        (show (dropLast j y, y (Fin.last j)) ∈ Prod.fst ⁻¹' A from h), liftG, hF]
      simp only
      rw [norm_sq_split j y, sub_add_eq_sub_sub]
    · rw [indicator_of_notMem (show y ∉ dropLast j ⁻¹' A from h), indicator_of_notMem
        (show (dropLast j y, y (Fin.last j)) ∉ Prod.fst ⁻¹' A from h)]
  simp_rw [hpt]
  rw [(measurePreserving_splitEquiv j).lintegral_comp_emb (splitEquiv j).measurableEmbedding,
    Measure.volume_eq_prod, lintegral_prod _ ((hFm.indicator (measurable_fst hA)).aemeasurable)]
  have hin : ∀ x, ∫⁻ s, (Prod.fst ⁻¹' A).indicator F (x, s) =
      A.indicator ((Metric.ball 0 1).indicator fun _ => ENNReal.ofReal (liftConst j * π)) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, ← lintegral_lift_fibre]
      exact lintegral_congr fun s => indicator_of_mem (show (x, s) ∈ Prod.fst ⁻¹' A from hx) _
    · rw [indicator_of_notMem hx]
      exact (lintegral_congr fun s =>
        indicator_of_notMem (show (x, s) ∉ Prod.fst ⁻¹' A from hx) _).trans lintegral_zero
  simp_rw [hin]
  rw [lintegral_indicator hA, lintegral_indicator_const Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm, volume_inter_ball]
  simp only [unifSet, smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  congr 1
  have h1 := volB_toReal_pos j
  rw [liftConst, show 1 / (π * (volume (B j)).toReal) * π = ((volume (B j)).toReal)⁻¹ by
    field_simp, ENNReal.ofReal_inv_of_pos h1, ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]

instance isProb_liftBall : IsProbabilityMeasure (liftBall j) := by
  constructor
  have := congrArg (fun μ => μ univ) (liftBall_map j)
  rw [Measure.map_apply (dropLast j).measurable MeasurableSet.univ, preimage_univ] at this
  rw [this, measure_univ]

end LiftMeasure

/-- **Theorem 51 (sufficiency) in odd dimension `2k + 1`**: the lift to `ℝ^{2k+2} = ℂ^{k+1}` is
invariant under all linear isometries, and its projection is `U(B)`. -/
theorem scalingProperty_ball_odd (k : ℕ) : ScalingProperty (unifSet (B (2 * k + 1))) 2 := by
  set e : Fin (2 * k + 1 + 1) ≃ Fin (k + 1) ⊕ Fin (k + 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  have h := scalingProperty_of_rot (liftBall (2 * k + 1)) (cplx e)
    (rot_invariant (withDensity_radial_map_iso _ (measurable_liftG _)) _ (cplx_norm e)
      (cplx_inner e)) (dropLast (2 * k + 1))
  rwa [liftBall_map] at h

/-- **Theorem 51, sufficiency** (`b:thm:ball`): the closed unit ball of `ℝ^j` has the scaling
property with constant `2`, in every dimension `j`: for every `n ≥ 2` there is a Borel function
of `(λ, t)` and of a sequence of independent uniform variables whose law is a joint mix of the
`U(t_i + λ_i B)` whenever `λ ≥ 0`, not all zero, and `2 max λ ≤ ∑ λ`. -/
theorem ball_scalingProperty (j : ℕ) :
    ScalingProperty (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · exact scalingProperty_ball_even k
  · exact scalingProperty_ball_odd k

/-- Theorem 51 sufficiency in the paper's form (`ScalingPropertySet`, with `U(t + λ B)` the point
mass at `t` for `λ = 0`). -/
theorem ball_scalingPropertySet (j : ℕ) :
    ScalingPropertySet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1) 2 :=
  (scalingPropertySet_iff (Metric.measure_closedBall_pos _ _ one_pos).ne'
    measure_closedBall_lt_top.ne 2).2 (ball_scalingProperty j)

/-- **Theorem 51** (`b:thm:ball`): for `j ≥ 1`, `n ≥ 2` and `λ ≥ 0`, not all zero, the
distributions `U(t_1 + λ_1 B), …, U(t_n + λ_n B)` are jointly mixable if and only if
`2 max λ ≤ ∑ λ`. (Necessity: `ball_necessity`.) -/
theorem ball_jointlyMixable_iff {j n : ℕ} (hj : 1 ≤ j) (hn : 2 ≤ n)
    (t : Fin n → EuclideanSpace ℝ (Fin j)) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0) :
    JointlyMixable (fun i => unifScaled (Metric.closedBall 0 1) (t i) (lam i)) ↔
      ∀ k, 2 * lam k ≤ ∑ i, lam i := by
  refine ⟨fun h k => ball_necessity hj t lam hlam h k, fun h => ?_⟩
  obtain ⟨Φ, -, hΦ⟩ := ball_scalingPropertySet j n hn
  exact ⟨_, hΦ lam t hlam hne h⟩

/-- **`U(B)` is `n`-completely mixable for every `n ≥ 2`** (last claim of Theorem 51), in every
dimension. This discharges the hypothesis `hball` of `SymmCor.lean` (with `n = 3`). -/
theorem ball_completelyMixable (j : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) := by
  obtain ⟨Φ, -, hΦ⟩ := ball_scalingProperty j n hn
  have hpoly : ∀ k : Fin n, 2 * (fun _ : Fin n => (1 : ℝ)) k ≤
      ∑ i, (fun _ : Fin n => (1 : ℝ)) i := by
    intro k
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact_mod_cast hn
  have h := hΦ (fun _ => 1) (fun _ => 0) (fun _ => zero_le_one) ⟨⟨0, by omega⟩, one_ne_zero⟩
    hpoly
  refine ⟨unifSeq.map (Φ (fun _ => 1, fun _ => 0)), ?_⟩
  unfold IsCompleteMix
  convert h using 2 with i
  simp only [zero_add, one_smul]
  exact Measure.map_id.symm

/-! ### Rotation-invariant measures and the sphere (for Lemma 50 and Proposition 52) -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `P` is invariant under the orthogonal group. -/
def IsRotInv (P : Measure E) : Prop := ∀ L : E ≃ₗᵢ[ℝ] E, P.map L = P

variable (E) in
/-- **The cited fact** (taken as a hypothesis): two probability measures on the unit sphere that
are invariant under the orthogonal group are equal (the uniqueness of the uniform distribution on
`S^{j-1}`). Mathlib does not contain it. -/
def SphereUniqueness : Prop :=
  ∀ ν₁ ν₂ : Measure E, IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
    ν₁ (Metric.sphere 0 1)ᶜ = 0 → ν₂ (Metric.sphere 0 1)ᶜ = 0 → IsRotInv ν₁ → IsRotInv ν₂ →
    ν₁ = ν₂

/-- The direction `x / ‖x‖` (`0` at `0`). -/
def dir (x : E) : E := ‖x‖⁻¹ • x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_iso (L : E ≃ₗᵢ[ℝ] E) (x : E) : dir (L x) = L (dir x) := by
  simp [dir]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_dir {x : E} (hx : x ≠ 0) : ‖dir x‖ = 1 := by
  rw [dir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_smul_dir (x : E) : ‖x‖ • dir x = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [dir]
  · rw [dir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]

omit [FiniteDimensional ℝ E] in
lemma measurable_dir : Measurable (dir : E → E) := by
  unfold dir; fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_mem_sphere_iff (x : E) : dir x ∈ Metric.sphere (0 : E) 1 ↔ x ≠ 0 := by
  refine ⟨fun h hx => ?_, fun hx => mem_sphere_zero_iff_norm.2 (norm_dir hx)⟩
  rw [hx] at h; simp [dir] at h

omit [FiniteDimensional ℝ E] in
/-- Restriction to an invariant set keeps the invariance. -/
lemma IsRotInv.restrict {P : Measure E} (hP : IsRotInv P) {M : Set E} (hM : MeasurableSet M)
    (hML : ∀ L : E ≃ₗᵢ[ℝ] E, L ⁻¹' M = M) : IsRotInv (P.restrict M) := by
  intro L
  have h := Measure.restrict_map (μ := P) L.continuous.measurable hM
  rw [hP L, hML L] at h
  exact h.symm

/-- **Polar decomposition**, from the uniqueness on the sphere: a rotation-invariant probability
measure `P` is the law of `R Θ` with `R ∼ |X|`, `X ∼ P`, and `Θ ∼ σ` independent, for any
rotation-invariant probability measure `σ` on the sphere. -/
theorem polar_of_unique (hU : SphereUniqueness E) {σ : Measure E} [IsProbabilityMeasure σ]
    (hσs : σ (Metric.sphere 0 1)ᶜ = 0) (hσ : IsRotInv σ) {P : Measure E} [IsProbabilityMeasure P]
    (hP : IsRotInv P) : P = ((P.map norm).prod σ).map (fun z => z.1 • z.2) := by
  have hn : Measurable (norm : E → ℝ) := measurable_norm
  have hg : Measurable fun z : ℝ × E => z.1 • z.2 := by fun_prop
  have h0m : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton 0).compl
  set P' := P.restrict {0}ᶜ with hP'
  -- the joint law of `(‖X‖, X/‖X‖)` on `X ≠ 0` is a product
  have hprod : P'.map (fun x => (‖x‖, dir x)) = (P'.map norm).prod σ := by
    refine (Measure.prod_eq fun s t hs ht => ?_).symm
    rw [Measure.map_apply (hn.prodMk measurable_dir) (hs.prod ht), Measure.map_apply hn hs]
    have hpre : (fun x : E => (‖x‖, dir x)) ⁻¹' (s ×ˢ t) = norm ⁻¹' s ∩ dir ⁻¹' t := rfl
    rw [hpre]
    set c := P' (norm ⁻¹' s)
    rcases eq_or_ne c 0 with hc | hc
    · rw [hc, zero_mul]; exact measure_mono_null inter_subset_left hc
    have hct : c ≠ ⊤ := measure_ne_top _ _
    set N := norm ⁻¹' s ∩ ({0}ᶜ : Set E)
    have hN : MeasurableSet N := (hn hs).inter h0m
    set ν := c⁻¹ • (P.restrict N).map dir
    have hcN : c = P N := by simp only [c, hP', Measure.restrict_apply (hn hs), N]
    have hν1 : IsProbabilityMeasure ν := by
      constructor
      rw [smul_apply, Measure.map_apply measurable_dir MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, ← hcN, smul_eq_mul,
        ENNReal.inv_mul_cancel hc hct]
    have hνs : ν (Metric.sphere 0 1)ᶜ = 0 := by
      rw [smul_apply, Measure.map_apply measurable_dir
        Metric.isClosed_sphere.measurableSet.compl, Measure.restrict_apply
        (measurable_dir Metric.isClosed_sphere.measurableSet.compl)]
      have : dir ⁻¹' (Metric.sphere (0 : E) 1)ᶜ ∩ N = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_compl_iff, dir_mem_sphere_iff, N,
          mem_singleton_iff, not_not, mem_empty_iff_false, iff_false]
        tauto
      rw [this, measure_empty, smul_eq_mul, mul_zero]
    have hνinv : IsRotInv ν := by
      have hPN : IsRotInv (P.restrict N) := hP.restrict hN fun L => by ext x; simp [N]
      intro L
      simp only [ν]
      rw [Measure.map_smul, Measure.map_map L.continuous.measurable measurable_dir]
      have : (L ∘ dir : E → E) = dir ∘ L := by funext x; exact (dir_iso L x).symm
      rw [this, ← Measure.map_map measurable_dir L.continuous.measurable, hPN L]
      exact L.continuous.measurable.aemeasurable
    have := congrArg (fun μ => μ t) (hU ν σ hν1 inferInstance hνs hσs hνinv hσ)
    simp only [ν, smul_apply, smul_eq_mul, Measure.map_apply measurable_dir ht,
      Measure.restrict_apply (measurable_dir ht)] at this
    rw [← this, ← mul_assoc, ENNReal.mul_inv_cancel hc hct, one_mul, hP',
      Measure.restrict_apply ((hn hs).inter (measurable_dir ht))]
    congr 1; ext x; simp only [N, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff]; tauto
  -- `P = P' + P{0} δ₀`
  have hsplit : P = P' + P {0} • Measure.dirac 0 := by
    rw [hP', ← Measure.restrict_singleton, add_comm, Measure.restrict_add_restrict_compl
      (measurableSet_singleton 0)]
  have hP'id : (P'.map (fun x => (‖x‖, dir x))).map (fun z => z.1 • z.2) = P' := by
    rw [Measure.map_map hg (hn.prodMk measurable_dir)]
    have : ((fun z : ℝ × E => z.1 • z.2) ∘ fun x => (‖x‖, dir x)) = id := by
      funext x; exact norm_smul_dir x
    rw [this, Measure.map_id]
  conv_lhs => rw [hsplit]
  conv_rhs => rw [hsplit]
  rw [Measure.map_add _ _ hn, Measure.add_prod, Measure.map_add _ _ hg, ← hprod, hP'id,
    Measure.map_smul, Measure.map_dirac' hn, Measure.prod_smul_left, Measure.map_smul,
    Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
  congr 2
  have : ((fun z : ℝ × E => z.1 • z.2) ∘ Prod.mk ‖(0 : E)‖) = fun _ => 0 := by
    funext x; simp
  rw [this, Measure.map_const, measure_univ, one_smul]
  all_goals first | exact hg.aemeasurable | exact hn.aemeasurable

end Sphere

/-! ### Lemma 50: a Gaussian frame -/

section Frame

open ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `g₁ = Z₁ / |Z₁|`. -/
def frame1 (z : E × E) : E := dir z.1

/-- `Z₂' = Z₂ - (Z₂ · g₁) g₁`. -/
def perp (z : E × E) : E := z.2 - ⟪z.2, dir z.1⟫_ℝ • dir z.1

/-- `g₂ = Z₂' / |Z₂'|`. -/
def frame2 (z : E × E) : E := dir (perp z)

omit [FiniteDimensional ℝ E] in
lemma measurable_frame1 : Measurable (frame1 : E × E → E) := measurable_dir.comp measurable_fst

lemma measurable_perp : Measurable (perp : E × E → E) := by
  have h1 : Measurable fun z : E × E => dir z.1 := measurable_dir.comp measurable_fst
  unfold perp
  exact measurable_snd.sub ((measurable_snd.inner h1).smul h1)

lemma measurable_frame2 : Measurable (frame2 : E × E → E) := measurable_dir.comp measurable_perp

variable (E) in
/-- The pair of independent standard Gaussian vectors `(Z₁, Z₂)`. -/
abbrev gauss2 : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)

variable (E) in
/-- The law of `g₁ = Z₁ / |Z₁|`: the uniform distribution on the sphere (as the paper uses it;
its identification with the normalised surface measure is not needed). -/
def sphUnif : Measure E := (stdGaussian E).map dir

instance : IsProbabilityMeasure (sphUnif E) := by
  unfold sphUnif; infer_instance

/-- Hyperplanes are null for the standard Gaussian. -/
lemma stdGaussian_inner_null {u : E} (hu : u ≠ 0) :
    stdGaussian E {x | ⟪u, x⟫_ℝ = 0} = 0 := by
  set L : StrongDual ℝ E := innerSL ℝ u
  have hpre : {x | ⟪u, x⟫_ℝ = 0} = L ⁻¹' {0} := by ext x; simp [L]
  rw [hpre, ← Measure.map_apply L.continuous.measurable (measurableSet_singleton 0),
    IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  have hv : (‖L‖ ^ 2).toNNReal ≠ 0 := by
    simp [L, innerSL_apply_norm, hu]
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  exact measure_singleton 0

lemma stdGaussian_zero_null [Nontrivial E] : stdGaussian E {0} = 0 := by
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  exact measure_mono_null (fun x hx => by simp [mem_singleton_iff.1 hx]) (stdGaussian_inner_null hu)

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_orth (hE : 2 ≤ Module.finrank ℝ E) (x : E) : ∃ u : E, u ≠ 0 ∧ ⟪x, u⟫_ℝ = 0 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ x)
  have h2 : Module.finrank ℝ (ℝ ∙ x) ≤ 1 := le_trans (finrank_span_le_card {x}) (by simp)
  have h3 : (ℝ ∙ x)ᗮ ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at h1; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  exact ⟨u, hu0, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hu⟩

/-- The frame is almost surely defined: `Z₁ ≠ 0` and `Z₂' ≠ 0` (dimension `≥ 2`). -/
lemma ae_frame_good (hE : 2 ≤ Module.finrank ℝ E) :
    ∀ᵐ z ∂gauss2 E, z.1 ≠ 0 ∧ perp z ≠ 0 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hm : MeasurableSet {z : E × E | z.1 ≠ 0 ∧ perp z ≠ 0} :=
    ((measurableSet_singleton 0).compl.preimage measurable_fst).inter
      ((measurableSet_singleton 0).compl.preimage measurable_perp)
  rw [gauss2, Measure.ae_prod_iff_ae_ae hm]
  have h0 : ∀ᵐ x ∂stdGaussian E, x ≠ 0 := by
    rw [ae_iff]; simpa using stdGaussian_zero_null
  filter_upwards [h0] with x hx
  obtain ⟨u, hu, hxu⟩ := exists_orth hE x
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (stdGaussian_inner_null hu)
  simp only [mem_ofPred_eq, not_and_or, not_not] at hy
  rcases hy with hy | hy
  · exact absurd hy hx
  · simp only [mem_ofPred_eq]
    have : y = ⟪y, dir x⟫_ℝ • dir x := by
      have := hy; simp only [perp] at this; exact (sub_eq_zero.1 this)
    have hux : ⟪u, x⟫_ℝ = 0 := by rw [real_inner_comm]; exact hxu
    rw [this]; simp [dir, inner_smul_right, hux]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma frame_iso (L : E ≃ₗᵢ[ℝ] E) (z : E × E) :
    frame1 (Prod.map L L z) = L (frame1 z) ∧ frame2 (Prod.map L L z) = L (frame2 z) := by
  have hp : perp (Prod.map L L z) = L (perp z) := by
    simp [perp, dir_iso, map_sub, map_smul]
  exact ⟨dir_iso L z.1, by rw [frame2, hp, dir_iso]; rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_frame {z : E × E} (h1 : z.1 ≠ 0) (h2 : perp z ≠ 0) {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) : ‖a • frame1 z + b • frame2 z‖ = 1 := by
  have hn1 : ‖frame1 z‖ = 1 := norm_dir h1
  have hn2 : ‖frame2 z‖ = 1 := norm_dir h2
  have ho : ⟪frame1 z, frame2 z⟫_ℝ = 0 := by
    have : ⟪dir z.1, perp z⟫_ℝ = 0 := by
      rw [perp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_dir h1,
        real_inner_comm]; ring
    show ⟪dir z.1, ‖perp z‖⁻¹ • perp z⟫_ℝ = 0
    rw [inner_smul_right, this, mul_zero]
  have h : ‖a • frame1 z + b • frame2 z‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, inner_smul_left, inner_smul_right, ho, norm_smul, norm_smul, hn1, hn2,
      Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [RCLike.conj_to_real, mul_zero, mul_one, sq_abs]
    linarith
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at this

lemma stdGaussian_isRotInv : IsRotInv (stdGaussian E) := fun L => stdGaussian_map L

/-- **Lemma 50** (`b:lem:frame`), given the uniqueness of the rotation-invariant probability
measure on the sphere (`SphereUniqueness`, the cited fact): for `j ≥ 2` and `a² + b² = 1`, the
vector `a g₁ + b g₂` built from two independent standard Gaussian vectors has the law of
`g₁ = Z₁/|Z₁|`, the uniform distribution on the sphere. -/
theorem lemma50 (hU : SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E) {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) :
    (gauss2 E).map (fun z => a • frame1 z + b • frame2 z) = sphUnif E := by
  have hΘ : Measurable fun z : E × E => a • frame1 z + b • frame2 z :=
    (measurable_frame1.const_smul a).add (measurable_frame2.const_smul b)
  have hS : MeasurableSet (Metric.sphere (0 : E) 1)ᶜ := Metric.isClosed_sphere.measurableSet.compl
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  refine hU _ _ inferInstance inferInstance ?_ ?_ ?_ ?_
  · rw [Measure.map_apply hΘ hS]
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 (ae_frame_good hE))
    simp only [mem_ofPred_eq, not_and_or, not_not]
    by_contra hc
    push Not at hc
    exact hz (mem_sphere_zero_iff_norm.2 (norm_frame hc.1 hc.2 hab))
  · rw [sphUnif, Measure.map_apply measurable_dir hS]
    refine measure_mono_null (fun x hx => ?_) stdGaussian_zero_null
    by_contra hc
    exact hx ((dir_mem_sphere_iff x).2 hc)
  · intro L
    have hL : Measurable (Prod.map L L) := L.continuous.measurable.prodMap L.continuous.measurable
    rw [Measure.map_map L.continuous.measurable hΘ]
    have : (L ∘ fun z : E × E => a • frame1 z + b • frame2 z) =
        (fun z => a • frame1 z + b • frame2 z) ∘ Prod.map L L := by
      funext z; simp [(frame_iso L z).1, (frame_iso L z).2]
    rw [this, ← Measure.map_map hΘ hL, gauss2, ← Measure.map_prod_map _ _
      L.continuous.measurable L.continuous.measurable, stdGaussian_map]
  · intro L
    rw [sphUnif, Measure.map_map L.continuous.measurable measurable_dir]
    have : (L ∘ dir : E → E) = dir ∘ L := by funext x; exact (dir_iso L x).symm
    rw [this, ← Measure.map_map measurable_dir L.continuous.measurable, stdGaussian_map]

end Frame

/-! ### Proposition 52: rotation-invariant distributions -/

section Radial

open ProbabilityTheory

/-- The polygon of Lemma 49 also for `λ = 0` (all vectors `0`) and every `n`. -/
lemma polyVec_spec' {n : ℕ} {lam : Fin n → ℝ} (hnn : ∀ j, 0 ≤ lam j)
    (hpoly : ∀ i, 2 * lam i ≤ ∑ j, lam j) :
    (∀ j, (polyVec lam j).1 ^ 2 + (polyVec lam j).2 ^ 2 = lam j ^ 2) ∧
      ∑ j, polyVec lam j = 0 := by
  classical
  by_cases hne : ∃ j, lam j ≠ 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hne.choose.2; omega⟩
    exact polyVec_spec hnn hne hpoly
  · push Not at hne
    have h0 : ∀ j, polyVec lam j = 0 := by
      intro j
      unfold polyVec
      refine Finset.sum_eq_zero fun k _ => ?_
      refine ite_eq_right fun h => ?_
      have := h.1
      simp [psum', hne] at this
    simp [h0, hne]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Lemma 50 scaled: if `a² + b² = s²` with `s ≥ 0`, then `a g₁ + b g₂ ∼ s Θ`, `Θ ∼ sphUnif`. -/
lemma frame_law_scaled (hU : SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E) {a b s : ℝ}
    (hs : 0 ≤ s) (h : a ^ 2 + b ^ 2 = s ^ 2) :
    (gauss2 E).map (fun z => a • frame1 z + b • frame2 z) = (sphUnif E).map (fun θ => s • θ) := by
  rcases hs.eq_or_lt with rfl | hpos
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    subst ha hb
    simp only [zero_smul, add_zero]
    rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  · have hcd : (a / s) ^ 2 + (b / s) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, h, div_self (by positivity)]
    have hf : (fun z => a • frame1 z + b • frame2 z) =
        (fun θ : E => s • θ) ∘ (fun z => (a / s) • frame1 z + (b / s) • frame2 z) := by
      funext z
      simp only [Function.comp, smul_add, smul_smul]
      congr 2 <;> field_simp
    have hΘ : Measurable fun z : E × E => (a / s) • frame1 z + (b / s) • frame2 z :=
      (measurable_frame1.const_smul _).add (measurable_frame2.const_smul _)
    rw [hf, ← Measure.map_map (measurable_const_smul s) hΘ, lemma50 hU hE hcd]

/-- The construction of Proposition 52: `X_i = v_{i1} g₁ + v_{i2} g₂` with the polygon `v` of
Lemma 49 for the lengths `R_1, …, R_n`. -/
def radialMix (n : ℕ) (w : (Fin n → ℝ) × (E × E)) : Fin n → E :=
  fun i => (polyVec w.1 i).1 • frame1 w.2 + (polyVec w.1 i).2 • frame2 w.2

lemma measurable_radialMix (n : ℕ) : Measurable (radialMix (E := E) n) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hv : Measurable fun w : (Fin n → ℝ) × (E × E) => polyVec w.1 i :=
    (measurable_polyVec i).comp measurable_fst
  exact (hv.fst.smul (measurable_frame1.comp measurable_snd)).add
    (hv.snd.smul (measurable_frame2.comp measurable_snd))

/-- **Proposition 52** (`b:prop:radial`), sufficiency, given the uniqueness of the
rotation-invariant probability on the sphere (`SphereUniqueness`, the cited fact): let `j ≥ 2`,
let `P_1, …, P_n` be rotation-invariant probability measures, and let `Q` be a coupling of their
radial distributions with `2 max R ≤ ∑ R` almost surely. Then the law of
`X_i = v_{i1} g₁ + v_{i2} g₂` (polygon of Lemma 49 for the lengths `R`, Gaussian frame of
Lemma 50 independent of `R`) is a joint mix of the `P_i` with sum `0`. -/
theorem prop52_sufficiency (hU : SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E) {n : ℕ}
    (P : Fin n → Measure E) [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, IsRotInv (P i))
    (Q : Measure (Fin n → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ i, Q.map (fun r => r i) = (P i).map norm)
    (hpoly : ∀ᵐ r ∂Q, ∀ i, 2 * r i ≤ ∑ l, r l) :
    IsJointMix P ((Q.prod (gauss2 E)).map (radialMix n)) ∧
      ∀ᵐ x ∂((Q.prod (gauss2 E)).map (radialMix n)), ∑ i, x i = 0 := by
  have hF := measurable_radialMix (E := E) n
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hσs : sphUnif E (Metric.sphere 0 1)ᶜ = 0 := by
    rw [sphUnif, Measure.map_apply measurable_dir Metric.isClosed_sphere.measurableSet.compl]
    refine measure_mono_null (fun x hx => ?_) stdGaussian_zero_null
    by_contra hc
    exact hx ((dir_mem_sphere_iff x).2 hc)
  have hσ : IsRotInv (sphUnif E) := by
    intro L
    rw [sphUnif, Measure.map_map L.continuous.measurable measurable_dir]
    have : (L ∘ dir : E → E) = dir ∘ L := by funext x; exact (dir_iso L x).symm
    rw [this, ← Measure.map_map measurable_dir L.continuous.measurable, stdGaussian_map]
  have hnn : ∀ᵐ r ∂Q, ∀ i, 0 ≤ r i := by
    rw [ae_all_iff]
    intro i
    have h := congrArg (fun μ => μ (Iio 0)) (hQ i)
    rw [Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.map_apply measurable_norm measurableSet_Iio] at h
    have h0 : (norm : E → ℝ) ⁻¹' Iio 0 = ∅ := by ext x; simp [norm_nonneg]
    rw [h0, measure_empty] at h
    rw [ae_iff]
    convert h using 2
    ext r; simp
  have hgood : ∀ᵐ r ∂Q, (∀ j, (polyVec r j).1 ^ 2 + (polyVec r j).2 ^ 2 = r j ^ 2) ∧
      ∑ j, polyVec r j = 0 ∧ ∀ i, 0 ≤ r i := by
    filter_upwards [hnn, hpoly] with r h1 h2
    exact ⟨(polyVec_spec' h1 h2).1, (polyVec_spec' h1 h2).2, h1⟩
  have hsum : ∀ᵐ x ∂((Q.prod (gauss2 E)).map (radialMix n)), ∑ i, x i = 0 := by
    rw [ae_map_iff hF.aemeasurable (measurableSet_sum_eq' 0)]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with w hw
    have h1 : ∑ i, (polyVec w.1 i).1 = 0 := by rw [← Prod.fst_sum, hw.2.1]; rfl
    have h2 : ∑ i, (polyVec w.1 i).2 = 0 := by rw [← Prod.snd_sum, hw.2.1]; rfl
    simp only [radialMix, Finset.sum_add_distrib, ← Finset.sum_smul, h1, h2, zero_smul, add_zero]
  refine ⟨⟨inferInstance, ⟨0, hsum⟩, fun i => ?_⟩, hsum⟩
  have hg : Measurable fun z : ℝ × E => z.1 • z.2 := by fun_prop
  have hFi : Measurable fun w : (Fin n → ℝ) × (E × E) =>
      (polyVec w.1 i).1 • frame1 w.2 + (polyVec w.1 i).2 • frame2 w.2 :=
    (measurable_pi_apply i).comp hF
  rw [Measure.map_map (measurable_pi_apply i) hF, polar_of_unique hU hσs hσ (hP i), ← hQ i]
  ext A hA
  rw [Measure.map_apply ((measurable_pi_apply i).comp hF) hA, Measure.map_apply hg hA,
    Measure.prod_apply (((measurable_pi_apply i).comp hF) hA), Measure.prod_apply (hg hA),
    lintegral_map (measurable_measure_prodMk_left (hg hA)) (measurable_pi_apply i)]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with r hr
  have hl := frame_law_scaled hU hE (hr.2.2 i) (hr.1 i)
  have e1 := congrArg (fun μ => μ A) hl
  have hΘ : Measurable fun z : E × E => (polyVec r i).1 • frame1 z + (polyVec r i).2 • frame2 z :=
    (measurable_frame1.const_smul _).add (measurable_frame2.const_smul _)
  rw [Measure.map_apply hΘ hA, Measure.map_apply (measurable_const_smul _) hA] at e1
  exact e1

/-- A rotation-invariant distribution with a finite mean has mean `0`. -/
lemma integral_id_eq_zero {P : Measure E} (hP : IsRotInv P) : ∫ x, x ∂P = 0 := by
  have h := hP (LinearIsometryEquiv.neg ℝ)
  have e : ∫ x, x ∂P = -∫ x, x ∂P := by
    conv_lhs => rw [← h]
    rw [integral_map (f := fun x : E => x)
      (LinearIsometryEquiv.neg ℝ).continuous.measurable.aemeasurable
      continuous_id.aestronglyMeasurable]
    exact integral_neg fun x : E => x
  have : (2 : ℝ) • ∫ x, x ∂P = 0 := by rw [two_smul]; nth_rw 1 [e]; exact neg_add_cancel _
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- **Proposition 52**, necessity (no hypothesis needed): if rotation-invariant distributions
with finite means are jointly mixable, then the norms of a joint mix are a coupling `R` of the
radial distributions with `2 max R ≤ ∑ R` almost surely (and the joint mix has sum `0`). -/
theorem prop52_necessity {n : ℕ} (P : Fin n → Measure E) (hP : ∀ i, IsRotInv (P i))
    (hint : ∀ i, Integrable id (P i)) (h : JointlyMixable P) :
    ∃ Q : Measure (Fin n → ℝ), IsProbabilityMeasure Q ∧
      (∀ i, Q.map (fun r => r i) = (P i).map norm) ∧ ∀ᵐ r ∂Q, ∀ i, 2 * r i ≤ ∑ l, r l := by
  obtain ⟨M, hMp, ⟨s, hs⟩, hm⟩ := h
  have hcoord : ∀ i, Integrable (fun x : Fin n → E => x i) M := by
    intro i
    have := hint i
    rw [← hm i] at this
    exact this.comp_measurable (measurable_pi_apply i)
  have hs0 : s = 0 := by
    have e1 : ∫ x, ∑ i, x i ∂M = s := by
      rw [integral_congr_ae hs]; simp
    have e2 : ∫ x, ∑ i, x i ∂M = 0 := by
      rw [integral_finsetSum _ fun i _ => hcoord i]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := integral_map (μ := M) (φ := fun x : Fin n → E => x i) (f := (id : E → E))
        (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id
      rw [hm i] at this
      simp only [id] at this
      rw [← this]
      exact integral_id_eq_zero (hP i)
    rw [← e1, e2]
  have hnm : Measurable fun x : Fin n → E => fun i => ‖x i‖ :=
    measurable_pi_iff.2 fun i => measurable_norm.comp (measurable_pi_apply i)
  refine ⟨M.map fun x i => ‖x i‖, inferInstance, fun i => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hnm, ← hm i]
    exact (Measure.map_map measurable_norm (measurable_pi_apply i)).symm
  · have hset : MeasurableSet {r : Fin n → ℝ | ∀ i, 2 * r i ≤ ∑ l, r l} := by
      rw [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).const_mul 2) (Finset.measurable_sum _ fun l _ =>
          measurable_pi_apply l)
    rw [ae_map_iff hnm.aemeasurable hset]
    filter_upwards [hs] with x hx i
    rw [hs0] at hx
    have hxi : x i = -∑ l ∈ Finset.univ.erase i, x l := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ (Finset.mem_univ i), hx]
    have h1 : ‖x i‖ ≤ ∑ l ∈ Finset.univ.erase i, ‖x l‖ := by
      rw [hxi, norm_neg]; exact norm_sum_le _ _
    have h2 := Finset.add_sum_erase Finset.univ (fun l => ‖x l‖) (Finset.mem_univ i)
    show 2 * ‖x i‖ ≤ ∑ l, ‖x l‖
    linarith

/-- **Proposition 52** (`b:prop:radial`): for `j ≥ 2`, rotation-invariant distributions with
finite means are jointly mixable if and only if their radial distributions have a coupling
`R` with `2 max R ≤ ∑ R` almost surely. The sufficiency uses `SphereUniqueness`. -/
theorem prop52 (hU : SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E) {n : ℕ}
    (P : Fin n → Measure E) [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, IsRotInv (P i))
    (hint : ∀ i, Integrable id (P i)) :
    JointlyMixable P ↔ ∃ Q : Measure (Fin n → ℝ), IsProbabilityMeasure Q ∧
      (∀ i, Q.map (fun r => r i) = (P i).map norm) ∧ ∀ᵐ r ∂Q, ∀ i, 2 * r i ≤ ∑ l, r l := by
  refine ⟨prop52_necessity P hP hint, fun ⟨Q, hQ1, hQ, hpoly⟩ => ?_⟩
  exact ⟨_, (prop52_sufficiency hU hE P hP Q hQ hpoly).1⟩

/-- Last claim of Proposition 52: a rotation-invariant distribution on `ℝ^j`, `j ≥ 2`, is
`n`-completely mixable for every `n ≥ 2` (given `SphereUniqueness`; no finite mean needed). -/
theorem completelyMixable_of_isRotInv (hU : SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E)
    {P : Measure E} [IsProbabilityMeasure P] (hP : IsRotInv P) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n P := by
  have hc : Measurable fun s : ℝ => fun _ : Fin n => s := measurable_pi_iff.2 fun _ =>
    measurable_id
  set Q := (P.map norm).map fun s : ℝ => fun _ : Fin n => s
  have hQ : ∀ i, Q.map (fun r => r i) = P.map norm := by
    intro i
    rw [Measure.map_map (measurable_pi_apply i) hc]
    exact Measure.map_id
  have hpoly : ∀ᵐ r ∂Q, ∀ i, 2 * r i ≤ ∑ l, r l := by
    have hset : MeasurableSet {r : Fin n → ℝ | ∀ i, 2 * r i ≤ ∑ l, r l} := by
      rw [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).const_mul 2) (Finset.measurable_sum _ fun l _ =>
          measurable_pi_apply l)
    rw [ae_map_iff hc.aemeasurable hset]
    refine (ae_map_iff measurable_norm.aemeasurable (hc hset)).2
      (Filter.Eventually.of_forall fun x => ?_)
    intro i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [norm_nonneg x]
  exact ⟨_, (prop52_sufficiency hU hE (fun _ => P) (fun _ => hP) Q hQ hpoly).1⟩

end Radial

end Ball

end Mixes
