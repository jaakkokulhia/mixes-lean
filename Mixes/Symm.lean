import Mixes.Defs

/-!
# Orbits of an affine symmetry (Proposition 98, `st:prop:symm`)

Setting: `V` is a finite-dimensional real normed space (the paper's `ℝ^d`) with an additive Haar
measure `volume`; `A : V ≃ᵃ[ℝ] V` is an affine bijection with `A^[m] = id` whose linear part
`A.linear` (the paper's `A₀`) has no eigenvalue `1`.

## Linear algebra
* `sum_pow_eq_zero`: `∑_{i<m} A₀^i = 0` from `A₀^m = 1` and the injectivity of `A₀ - 1`.
* `linear_pow_eq_one`, `abs_det_linear_eq_one`: `A₀^m = 1` and `|det A₀| = 1`.
* `exists_unique_fixed`: `A` has exactly one fixed point `c`.
* `orbit_sum`: every orbit has the sum `∑_{i<m} A^i x = m • c`.

## The density (25)
* `symmDensity`: `p = n/(n-r) (1/|K| - r/(n|L|) 1_L)` on `K`, `0` off `K`.
* `symmDensity_nonneg_iff`: `p ≥ 0` iff `r|K| ≤ n|L|`; `symmDensity_eq_zero_of_boundary`: on the
  boundary `n|L| = r|K|`, `p` vanishes on `L`.
* `symmDensity_marginal`: `((n-r)/n) p + (r/n) 1_L/|L| = 1_K/|K|` pointwise.
* `symmDensity_accept`: the acceptance rule gives the density `p`.
* `symmDensity_comp`: `p ∘ A = p`.

## The measure statement
* `isCompleteMix_symmetrize`: a measure on tuples with a constant sum and average marginal `F`,
  composed with a uniformly random bijection of the indices, is a complete mix of `F`.
* `completelyMixable_mul`: first statement of Proposition 98 (multiples of `m`).
* `completelyMixable_add`: second statement (`n = j m + r`, `j ≥ 1`, `n|L| ≥ r|K|`).
* `completelyMixable_centralSymm`: the final statement (central symmetry, `r = 3`), including
  `n = 3`, where `|L| ≥ |K|` forces `U(L) = U(K)` (`unifSet_eq_of_volume_le`).
* `integral_eq_fixed`, `sum_eq_of_isCompleteMix`: the mean of `U(L)` is `c`, and the constant sum
  of an `r`-complete mix of `U(L)` is `r • c`, so the tuple has the sum `jmc + rc = nc`
  (`sum_eq_smul_fixed`).

Differences from the paper: `K` and `L` are only measurable with `0 < |L|`, `|K| < ∞` (convexity,
compactness and the centroid are not used; `c` is the fixed point of `A`); `|det A₀| = 1` is
derived from `A^m = id`; the `j` orbits use the same point `P` (as in the displayed tuple), and in
the first statement the `j` copies use the same `X` (any coupling of the copies works); the
acceptance rule is verified as an identity of densities, not as a sampling procedure.
-/

open MeasureTheory Finset
open scoped ENNReal

noncomputable section

namespace Mixes

/-! ### Linear algebra -/

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `A₀^m = 1` and `A₀ - 1` is injective, then `∑_{i<m} A₀^i = 0`. -/
theorem sum_pow_eq_zero (A₀ : Module.End R M) {m : ℕ} (hm : A₀ ^ m = 1)
    (h1 : ∀ v, A₀ v = v → v = 0) : ∑ i ∈ range m, A₀ ^ i = 0 := by
  ext v
  have h := congrArg (fun T : Module.End R M => T v) (mul_geom_sum A₀ m)
  simp only [hm, sub_self, mul_apply_eq_comp, LinearMap.zero_apply, LinearMap.sub_apply,
    one_apply_eq_self] at h
  simpa using h1 _ (sub_eq_zero.1 h)

end Algebra

section Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `A x = A₀ (x - y) + A y`. -/
lemma affine_apply_eq (A : V ≃ᵃ[ℝ] V) (x y : V) : A x = A.linear (x - y) + A y := by
  have := A.map_vadd y (x - y)
  simpa [vadd_eq_add] using this

/-- `A^i x - A^i y = A₀^i (x - y)`. -/
lemma iterate_sub (A : V ≃ᵃ[ℝ] V) (i : ℕ) (x y : V) :
    (⇑A)^[i] x - (⇑A)^[i] y = ((A.linear : V →ₗ[ℝ] V) ^ i) (x - y) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ',
      mul_apply_eq_comp, ← ih, affine_apply_eq A ((⇑A)^[i] x) ((⇑A)^[i] y)]
    simp

/-- `A^m = id` gives `A₀^m = 1`. -/
theorem linear_pow_eq_one (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm : (⇑A)^[m] = id) :
    (A.linear : V →ₗ[ℝ] V) ^ m = 1 := by
  ext v
  have := iterate_sub A m v 0
  rw [hm] at this
  simpa using this.symm

/-- If `A₀` has no eigenvalue `1`, `A` has exactly one fixed point (finite dimension). -/
theorem exists_unique_fixed [FiniteDimensional ℝ V] (A : V ≃ᵃ[ℝ] V)
    (h1 : ∀ v, A.linear v = v → v = 0) : ∃! c, A c = c := by
  set B : V →ₗ[ℝ] V := 1 - (A.linear : V →ₗ[ℝ] V)
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply h1
    have : v - A.linear v = 0 := by simpa [B] using hv
    exact (sub_eq_zero.1 this).symm
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 hinj (A 0)
  have hc0 : A c = c := by
    have h' := affine_apply_eq A c 0
    have hc'' : c - A.linear c = A 0 := by simpa [B] using hc
    rw [h', sub_zero, ← hc'']; abel
  refine ⟨c, hc0, fun c' hc' => ?_⟩
  have h := affine_apply_eq A c' c
  rw [hc', hc0] at h
  have : A.linear (c' - c) = c' - c := by rw [← sub_eq_iff_eq_add.2 h]
  exact sub_eq_zero.1 (h1 _ this)

/-- Every orbit has the sum `m • c`, `c` the fixed point. -/
theorem orbit_sum (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm : (⇑A)^[m] = id)
    (h1 : ∀ v, A.linear v = v → v = 0) {c : V} (hc : A c = c) (x : V) :
    ∑ i ∈ range m, (⇑A)^[i] x = m • c := by
  have hci : ∀ i, (⇑A)^[i] c = c := fun i => Function.iterate_fixed hc i
  have : ∀ i, (⇑A)^[i] x = c + ((A.linear : V →ₗ[ℝ] V) ^ i) (x - c) := by
    intro i; rw [← iterate_sub, hci]; abel
  simp_rw [this, sum_add_distrib, ← LinearMap.sum_apply,
    sum_pow_eq_zero _ (linear_pow_eq_one A hm) h1]
  simp

end Affine

/-! ### The density (25) -/

section Density

variable {α : Type*}

/-- The density (25): `p = n/(n-r) (1/κ - r/(n λ) 1_L)` on `K` and `0` off `K`, where `κ = |K|`
and `λ = |L|`. -/
def symmDensity (n r κ l : ℝ) (K L : Set α) (y : α) : ℝ :=
  K.indicator (fun y => n / (n - r) * (1 / κ - r / (n * l) * L.indicator 1 y)) y

variable {n r κ l : ℝ} {K L : Set α} {y : α}

lemma symmDensity_of_mem_L (hLK : L ⊆ K) (hy : y ∈ L) :
    symmDensity n r κ l K L y = n / (n - r) * (1 / κ - r / (n * l)) := by
  simp [symmDensity, hLK hy, hy]

lemma symmDensity_of_mem_diff (hy : y ∈ K) (hyL : y ∉ L) :
    symmDensity n r κ l K L y = n / (n - r) / κ := by
  simp [symmDensity, hy, hyL, div_eq_mul_inv]

lemma symmDensity_of_not_mem (hy : y ∉ K) : symmDensity n r κ l K L y = 0 := by
  simp [symmDensity, hy]

/-- `p ≥ 0` everywhere iff `r |K| ≤ n |L|` (for `0 ≤ r < n`, `|K|, |L| > 0`, `∅ ≠ L ⊆ K`). -/
theorem symmDensity_nonneg_iff (hr : 0 ≤ r) (hrn : r < n) (hκ : 0 < κ) (hl : 0 < l)
    (hLK : L ⊆ K) (hL : L.Nonempty) :
    (∀ y, 0 ≤ symmDensity n r κ l K L y) ↔ r * κ ≤ n * l := by
  have hn : 0 < n := by linarith
  have hc : 0 < n / (n - r) := div_pos hn (by linarith)
  have key : 0 ≤ 1 / κ - r / (n * l) ↔ r * κ ≤ n * l := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) hκ]; constructor <;> intro h <;> linarith
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hL
    have := h y
    rw [symmDensity_of_mem_L hLK hy] at this
    exact key.1 ((mul_nonneg_iff_of_pos_left hc).1 this)
  · intro h y
    by_cases hyK : y ∈ K
    · by_cases hyL : y ∈ L
      · rw [symmDensity_of_mem_L hLK hyL]; exact mul_nonneg hc.le (key.2 h)
      · rw [symmDensity_of_mem_diff hyK hyL]; positivity
    · rw [symmDensity_of_not_mem hyK]

/-- The boundary case `n |L| = r |K|`: `p` vanishes on `L`. -/
theorem symmDensity_eq_zero_of_boundary (hn : n ≠ 0) (hκ : κ ≠ 0) (hl : l ≠ 0)
    (hb : n * l = r * κ) (hLK : L ⊆ K) (hy : y ∈ L) : symmDensity n r κ l K L y = 0 := by
  rw [symmDensity_of_mem_L hLK hy]
  have : 1 / κ - r / (n * l) = 0 := by
    rw [sub_eq_zero, hb, div_eq_div_iff hκ (mul_ne_zero (by rintro rfl; simp at hb; tauto) hκ)]
    ring
  rw [this, mul_zero]

/-- The marginal identity, multiplied by `n`: `(n-r) p + r 1_L/|L| = n 1_K/|K|`. -/
theorem symmDensity_marginal' (hrn : n ≠ r) (hn : n ≠ 0) (hl : l ≠ 0) (hLK : L ⊆ K) (y : α) :
    (n - r) * symmDensity n r κ l K L y + r * L.indicator 1 y / l = n * K.indicator 1 y / κ := by
  have hnr : n - r ≠ 0 := sub_ne_zero.2 hrn
  by_cases hyK : y ∈ K
  · by_cases hyL : y ∈ L
    · rw [symmDensity_of_mem_L hLK hyL]; simp [hyK, hyL]; field_simp; ring
    · rw [symmDensity_of_mem_diff hyK hyL]; simp [hyK, hyL]; field_simp
  · have hyL : y ∉ L := fun h => hyK (hLK h)
    rw [symmDensity_of_not_mem hyK]; simp [hyK, hyL]

/-- The marginal identity `((n-r)/n) p + (r/n) 1_L/|L| = 1_K/|K|`. -/
theorem symmDensity_marginal (hrn : n ≠ r) (hn : n ≠ 0) (hl : l ≠ 0) (hLK : L ⊆ K) (y : α) :
    (n - r) / n * symmDensity n r κ l K L y + r / n * (L.indicator 1 y / l) =
      K.indicator 1 y / κ := by
  have := symmDensity_marginal' (κ := κ) hrn hn hl hLK y
  calc (n - r) / n * symmDensity n r κ l K L y + r / n * (L.indicator 1 y / l)
      = ((n - r) * symmDensity n r κ l K L y + r * L.indicator 1 y / l) / n := by ring
    _ = n * (K.indicator 1 y / κ) / n := by rw [this]; ring
    _ = K.indicator 1 y / κ := by field_simp

/-- The acceptance probability of the rule: `1` off `L`, `1 - r|K|/(n|L|)` on `L`. -/
def acceptProb (n r κ l : ℝ) (L : Set α) (y : α) : ℝ :=
  1 - r * κ / (n * l) * L.indicator 1 y

/-- The acceptance rule: a point of `U(K)` accepted with probability `acceptProb` has the density
`acceptProb · 1_K/|K|` divided by the total acceptance probability `1 - r/n`, which is `p`. -/
theorem symmDensity_accept (hrn : n ≠ r) (hn : n ≠ 0) (hκ : κ ≠ 0) (hl : l ≠ 0) (hLK : L ⊆ K)
    (y : α) :
    acceptProb n r κ l L y * K.indicator 1 y / κ / (1 - r / n) = symmDensity n r κ l K L y := by
  have hnr : n - r ≠ 0 := sub_ne_zero.2 hrn
  have h1 : 1 - r / n = (n - r) / n := by field_simp
  rw [h1]
  by_cases hyK : y ∈ K
  · by_cases hyL : y ∈ L
    · rw [symmDensity_of_mem_L hLK hyL]; simp [acceptProb, hyK, hyL]; field_simp
    · rw [symmDensity_of_mem_diff hyK hyL]; simp [acceptProb, hyK, hyL]; field_simp
  · rw [symmDensity_of_not_mem hyK]; simp [hyK]

/-- The total acceptance probability: with `|K| = |K \ L| + |L|`,
`(|K \ L| + |L| (1 - r|K|/(n|L|))) / |K| = 1 - r/n`. -/
theorem acceptProb_total {a : ℝ} (hn : n ≠ 0) (hκ : κ ≠ 0) (hl : l ≠ 0) (hK : κ = a + l) :
    (a + l * (1 - r * κ / (n * l))) / κ = 1 - r / n := by
  field_simp
  rw [hK]; ring

/-- `p ∘ A = p` when `A` maps `K` and `L` onto themselves (as preimages). -/
theorem symmDensity_comp (f : α → α) (hK : f ⁻¹' K = K) (hL : f ⁻¹' L = L) (y : α) :
    symmDensity n r κ l K L (f y) = symmDensity n r κ l K L y := by
  have hK' : f y ∈ K ↔ y ∈ K := by rw [← Set.mem_preimage, hK]
  have hL' : f y ∈ L ↔ y ∈ L := by rw [← Set.mem_preimage, hL]
  unfold symmDensity
  by_cases hy : y ∈ K
  · rw [Set.indicator_of_mem (hK'.2 hy), Set.indicator_of_mem hy]
    by_cases hyL : y ∈ L
    · rw [Set.indicator_of_mem (hL'.2 hyL), Set.indicator_of_mem hyL]; rfl
    · rw [Set.indicator_of_notMem (mt hL'.1 hyL), Set.indicator_of_notMem hyL]
  · rw [Set.indicator_of_notMem (mt hK'.1 hy), Set.indicator_of_notMem hy]

/-- For a bijection, `f '' K = K` gives `f ⁻¹' K = K`. -/
lemma preimage_eq_of_image_eq {f : α → α} (hf : Function.Injective f) (hK : f '' K = K) :
    f ⁻¹' K = K := by
  rw [← hK, Set.preimage_image_eq _ hf, hK]

end Density

/-! ### Symmetrisation by a uniformly random bijection of the indices -/

section Symmetrize

variable {E ι : Type*} [MeasurableSpace E] [Fintype ι] [DecidableEq ι]

/-- Counting: `n ∑_σ g (σ k) = #{σ} ∑_i g i`, the sum over the bijections `σ : Fin n ≃ ι`. -/
lemma nsmul_sum_equiv_apply {M : Type*} [AddCommMonoid M] {n : ℕ} (g : ι → M) (k : Fin n) :
    n • ∑ σ : Fin n ≃ ι, g (σ k) = Fintype.card (Fin n ≃ ι) • ∑ i, g i := by
  have hk : ∀ k', ∑ σ : Fin n ≃ ι, g (σ k) = ∑ σ : Fin n ≃ ι, g (σ k') := by
    intro k'
    let e : (Fin n ≃ ι) ≃ (Fin n ≃ ι) :=
      ⟨fun σ => (Equiv.swap k k').trans σ, fun σ => (Equiv.swap k k').trans σ,
        fun σ => by ext; simp, fun σ => by ext; simp⟩
    exact Fintype.sum_equiv e _ _ (fun σ => by simp [e])
  calc n • ∑ σ : Fin n ≃ ι, g (σ k) = ∑ k' : Fin n, ∑ σ : Fin n ≃ ι, g (σ k') := by
        rw [Finset.sum_congr rfl (fun k' _ => (hk k').symm), sum_const, card_univ,
          Fintype.card_fin]
    _ = ∑ σ : Fin n ≃ ι, ∑ k', g (σ k') := Finset.sum_comm
    _ = ∑ σ : Fin n ≃ ι, ∑ i, g i := by simp_rw [Equiv.sum_comp]
    _ = Fintype.card (Fin n ≃ ι) • ∑ i, g i := by rw [sum_const, card_univ]

/-- A measure `Q` on tuples indexed by `ι`, composed with a uniformly random bijection
`Fin n ≃ ι` (the paper's uniformly random permutation). -/
def symmetrize (n : ℕ) (Q : Measure (ι → E)) : Measure (Fin n → E) :=
  ((Fintype.card (Fin n ≃ ι) : ℝ≥0∞)⁻¹) • ∑ σ : Fin n ≃ ι, Q.map (fun z k => z (σ k))

lemma measurableSet_sum_eq_gen {κ : Type*} [Fintype κ] [AddCommMonoid E] [MeasurableAdd₂ E]
    [MeasurableSingletonClass E] (s : E) : MeasurableSet {z : κ → E | ∑ i, z i = s} :=
  (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) (measurableSet_singleton s)

/-- A probability measure on tuples with a constant sum whose average coordinate marginal is `F`
becomes, composed with a uniformly random bijection of the indices, an `n`-complete mix of `F`. -/
theorem isCompleteMix_symmetrize [AddCommMonoid E] [MeasurableAdd₂ E] [MeasurableSingletonClass E]
    {n : ℕ} (hn : 0 < n) (hι : Fintype.card ι = n) (Q : Measure (ι → E)) [IsProbabilityMeasure Q]
    {s : E} (hs : ∀ᵐ z ∂Q, ∑ i, z i = s) {F : Measure E}
    (hF : (n : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun z => z i) = F) : IsCompleteMix n F (symmetrize n Q) := by
  have hmeas : ∀ σ : Fin n ≃ ι, Measurable (fun z : ι → E => fun k => z (σ k)) :=
    fun σ => Measurable.of_eval (fun k => measurable_pi_apply _)
  have hN : (Fintype.card (Fin n ≃ ι) : ℝ≥0∞) ≠ 0 := by
    have : Nonempty (Fin n ≃ ι) := ⟨(Fintype.equivFinOfCardEq hι).symm⟩
    exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card (Fin n ≃ ι) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  refine ⟨⟨?_⟩, ⟨s, ?_⟩, fun k => ?_⟩
  · simp only [symmetrize, smul_apply, sum_apply, smul_eq_mul,
      Measure.map_apply (hmeas _) MeasurableSet.univ, Set.preimage_univ, measure_univ, sum_const,
      card_univ, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hN hNt
  · rw [ae_iff]
    have hS : MeasurableSet {z : Fin n → E | ¬ ∑ k, z k = s} := (measurableSet_sum_eq_gen s).compl
    have hpre : ∀ σ : Fin n ≃ ι,
        (fun z : ι → E => fun k => z (σ k)) ⁻¹' {z | ¬ ∑ k, z k = s} = {z | ¬ ∑ i, z i = s} := by
      intro σ; ext z; simp [Equiv.sum_comp σ z]
    simp only [symmetrize, smul_apply, sum_apply, smul_eq_mul,
      Measure.map_apply (hmeas _) hS, hpre, ae_iff.1 hs, sum_const_zero, mul_zero]
  · ext t ht
    rw [← hF, Measure.map_apply (measurable_pi_apply k) ht]
    have hpre : ∀ σ : Fin n ≃ ι, (fun z : ι → E => fun k => z (σ k)) ⁻¹' ((fun x => x k) ⁻¹' t) =
        (fun z : ι → E => z (σ k)) ⁻¹' t := fun σ => rfl
    have hmap : ∀ i, Q.map (fun z : ι → E => z i) t = Q ((fun z : ι → E => z i) ⁻¹' t) :=
      fun i => Measure.map_apply (measurable_pi_apply i) ht
    simp only [symmetrize, smul_apply, sum_apply, smul_eq_mul,
      Measure.map_apply (hmeas _) (measurable_pi_apply k ht), hpre, hmap]
    have hc := nsmul_sum_equiv_apply (fun i => Q ((fun z : ι → E => z i) ⁻¹' t)) k
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

end Symmetrize

/-! ### Volume, uniform distributions and the measure of `P` -/

section Volume

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

lemma affine_eq_comp (A : V ≃ᵃ[ℝ] V) : ⇑A = (· + A 0) ∘ (A.linear : V →ₗ[ℝ] V) := by
  funext x; simpa using affine_apply_eq A x 0

lemma measurable_affine (A : V ≃ᵃ[ℝ] V) : Measurable A := by
  rw [affine_eq_comp]
  exact (measurable_add_const _).comp (LinearMap.continuous_of_finiteDimensional _).measurable

/-- `|det A₀| = 1`, from `A^m = id` (the paper derives it from `A(K) = K`). -/
theorem abs_det_linear_eq_one (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm0 : m ≠ 0) (hm : (⇑A)^[m] = id) :
    |LinearMap.det (A.linear : V →ₗ[ℝ] V)| = 1 := by
  have h := congrArg LinearMap.det (linear_pow_eq_one A hm)
  rw [map_pow, map_one] at h
  rw [← pow_eq_one_iff_of_nonneg (abs_nonneg _) hm0, ← abs_pow, h, abs_one]

/-- `A` preserves volume. -/
theorem measurePreserving_affine (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm0 : m ≠ 0) (hm : (⇑A)^[m] = id) :
    MeasurePreserving A volume volume := by
  refine ⟨measurable_affine A, ?_⟩
  have hdet := abs_det_linear_eq_one A hm0 hm
  have hne : LinearMap.det (A.linear : V →ₗ[ℝ] V) ≠ 0 := by
    intro h; rw [h] at hdet; simp at hdet
  rw [affine_eq_comp, ← Measure.map_map (measurable_add_const _)
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, abs_inv, hdet, inv_one,
    ENNReal.ofReal_one, one_smul, Measure.IsAddRightInvariant.map_add_right_eq_self]

lemma map_iterate_eq {f : V → V} (hf : Measurable f) {ν : Measure V} (h : ν.map f = ν) (i : ℕ) :
    ν.map (f^[i]) = ν := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ, ← Measure.map_map (hf.iterate i) hf, h, ih]

lemma isProbabilityMeasure_unifSet {K : Set V} (h0 : volume K ≠ 0) (hfin : volume K ≠ ∞) :
    IsProbabilityMeasure (unifSet K) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 hfin

lemma map_unifSet (A : V ≃ᵃ[ℝ] V) (hA : MeasurePreserving A volume volume) {K : Set V}
    (hK : MeasurableSet K) (hpre : A ⁻¹' K = K) : (unifSet K).map A = unifSet K := by
  have h := (hA.restrict_preimage hK).map_eq
  rw [hpre] at h
  rw [unifSet, Measure.map_smul _ hA.measurable.aemeasurable, h]

lemma map_withDensity_eq (A : V ≃ᵃ[ℝ] V) (hA : MeasurePreserving A volume volume)
    {f : V → ℝ≥0∞} (hf : Measurable f) (hfA : ∀ y, f (A y) = f y) :
    (volume.withDensity f).map A = volume.withDensity f := by
  ext s hs
  rw [Measure.map_apply hA.measurable hs, withDensity_apply _ (hA.measurable hs),
    withDensity_apply _ hs, ← hA.setLIntegral_comp_preimage hs hf]
  simp only [hfA]

lemma unifSet_eq_withDensity {L : Set V} (hL : MeasurableSet L) (h0 : volume L ≠ 0)
    (hfin : volume L ≠ ∞) :
    unifSet L = volume.withDensity (fun y => ENNReal.ofReal (L.indicator 1 y / (volume L).toReal))
    := by
  have : (fun y => ENNReal.ofReal (L.indicator 1 y / (volume L).toReal)) =
      L.indicator (fun _ => (volume L)⁻¹) := by
    funext y
    by_cases hy : y ∈ L
    · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_div]
      rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 hfin), ENNReal.ofReal_toReal hfin]
    · simp [hy]
  rw [this, withDensity_indicator hL, withDensity_const]; rfl

/-- If `L ⊆ K` and `|L| ≥ |K|`, then `L = K` up to a null set and `U(L) = U(K)`. -/
theorem unifSet_eq_of_volume_le {K L : Set V} (hL : MeasurableSet L) (hLK : L ⊆ K)
    (hKfin : volume K ≠ ∞) (hle : volume K ≤ volume L) : unifSet L = unifSet K := by
  have hae : L =ᵐ[volume] K := ae_eq_of_subset_of_measure_ge hLK hle hL.nullMeasurableSet hKfin
  have hv : volume L = volume K := measure_congr hae
  rw [unifSet, unifSet, hv, Measure.restrict_congr_set hae]

lemma measurable_symmDensity {n r κ l : ℝ} {K L : Set V} (hK : MeasurableSet K)
    (hL : MeasurableSet L) : Measurable (symmDensity n r κ l K L) :=
  (measurable_const.mul (measurable_const.sub
    (measurable_const.mul (measurable_one.indicator hL)))).indicator hK

/-- The measure of `P`, with the density (25) for `|K|`, `|L|` the volumes. -/
def symmMeasure (n r : ℕ) (K L : Set V) : Measure V :=
  volume.withDensity fun y =>
    ENNReal.ofReal (symmDensity n r (volume K).toReal (volume L).toReal K L y)

/-- The marginal identity as measures: `(n - r) • μ_P + r • U(L) = n • U(K)`. -/
theorem symmMeasure_identity {K L : Set V} (hK : MeasurableSet K) (hL : MeasurableSet L)
    (hLK : L ⊆ K) (hL0 : volume L ≠ 0) (hKfin : volume K ≠ ∞) {n r : ℕ} (hrn : r < n)
    (hcond : (r : ℝ) * (volume K).toReal ≤ n * (volume L).toReal) :
    ((n - r : ℕ) : ℝ≥0∞) • symmMeasure n r K L + (r : ℝ≥0∞) • unifSet L =
      (n : ℝ≥0∞) • unifSet K := by
  have hLfin : volume L ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hLK)
  have hK0 : volume K ≠ 0 := fun h => hL0 (measure_mono_null hLK h)
  have hκ : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKfin
  have hl : 0 < (volume L).toReal := ENNReal.toReal_pos hL0 hLfin
  have hn : (n : ℝ) ≠ 0 := by have : 0 < n := by omega
                              positivity
  have hrn' : (n : ℝ) ≠ r := by exact_mod_cast hrn.ne'
  have hp := (symmDensity_nonneg_iff (n := n) (r := r) (Nat.cast_nonneg r)
    (by exact_mod_cast hrn) hκ hl hLK (nonempty_of_measure_ne_zero hL0)).2 hcond
  have hm : Measurable (((n - r : ℕ) : ℝ≥0∞) • fun y =>
      ENNReal.ofReal (symmDensity n r (volume K).toReal (volume L).toReal K L y)) :=
    (ENNReal.measurable_ofReal.comp (measurable_symmDensity hK hL)).const_smul _
  rw [unifSet_eq_withDensity hL hL0 hLfin, unifSet_eq_withDensity hK hK0 hKfin, symmMeasure,
    ← withDensity_smul' _ _ (ENNReal.natCast_ne_top _),
    ← withDensity_smul' _ _ (ENNReal.natCast_ne_top _),
    ← withDensity_smul' _ _ (ENNReal.natCast_ne_top _),
    ← withDensity_add_left hm]
  congr 1
  funext y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hind : 0 ≤ L.indicator (1 : V → ℝ) y / (volume L).toReal :=
    div_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) y) hl.le
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast r, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (hp y))
      (mul_nonneg (Nat.cast_nonneg _) hind)]
  congr 1
  have := symmDensity_marginal' (κ := (volume K).toReal) hrn' hn hl.ne' hLK y
  rw [Nat.cast_sub hrn.le]
  rw [mul_div_assoc, mul_div_assoc] at this
  exact this

lemma isProbabilityMeasure_symmMeasure {K L : Set V} (hK : MeasurableSet K)
    (hL : MeasurableSet L) (hLK : L ⊆ K) (hL0 : volume L ≠ 0) (hKfin : volume K ≠ ∞) {n r : ℕ}
    (hrn : r < n) (hcond : (r : ℝ) * (volume K).toReal ≤ n * (volume L).toReal) :
    IsProbabilityMeasure (symmMeasure n r K L) := by
  have hK0 : volume K ≠ 0 := fun h => hL0 (measure_mono_null hLK h)
  have hLfin : volume L ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hLK)
  have := isProbabilityMeasure_unifSet hK0 hKfin
  have := isProbabilityMeasure_unifSet hL0 hLfin
  have h := congrArg (fun μ : Measure V => μ Set.univ)
    (symmMeasure_identity hK hL hLK hL0 hKfin hrn hcond)
  simp only [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one] at h
  constructor
  have h' : ((n - r : ℕ) : ℝ≥0∞) * symmMeasure n r K L Set.univ + r = ((n - r : ℕ) : ℝ≥0∞) + r := by
    rw [h]; push_cast [Nat.cast_sub hrn.le]; rw [tsub_add_cancel_of_le (by exact_mod_cast hrn.le)]
  have h'' := (ENNReal.add_left_inj (ENNReal.natCast_ne_top r)).1 h'
  have hnr0 : ((n - r : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hrn).ne'
  calc symmMeasure n r K L Set.univ = ((n - r : ℕ) : ℝ≥0∞)⁻¹ *
        (((n - r : ℕ) : ℝ≥0∞) * symmMeasure n r K L Set.univ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hnr0 (ENNReal.natCast_ne_top _), one_mul]
    _ = 1 := by rw [h'', ENNReal.inv_mul_cancel hnr0 (ENNReal.natCast_ne_top _)]

end Volume

/-! ### Proposition 98 -/

section Main

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Proposition 98, first statement** (with Remark 81): if `A` is an affine bijection with
`A(K) = K`, `A^m = id` (`m ≥ 1`) and no eigenvalue `1` of its linear part, then `U(K)` is
`n`-completely mixable for every multiple `n = j m`, `j ≥ 1`. The mix is a uniformly random
permutation of `j` copies of the orbit `(X, AX, …, A^{m-1}X)`, `X ∼ U(K)`. -/
theorem completelyMixable_mul (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm0 : m ≠ 0) (hm : (⇑A)^[m] = id)
    (h1 : ∀ v, A.linear v = v → v = 0) {K : Set V} (hK : MeasurableSet K) (hAK : A '' K = K)
    (hK0 : volume K ≠ 0) (hKfin : volume K ≠ ∞) {j : ℕ} (hj : j ≠ 0) :
    CompletelyMixable (j * m) (unifSet K) := by
  obtain ⟨c, hc, -⟩ := exists_unique_fixed A h1
  have hA := measurePreserving_affine A hm0 hm
  have hU : (unifSet K).map A = unifSet K :=
    map_unifSet A hA hK (preimage_eq_of_image_eq A.injective hAK)
  have := isProbabilityMeasure_unifSet hK0 hKfin
  let T : V → (Fin j × Fin m → V) := fun y ai => (⇑A)^[ai.2] y
  have hT : Measurable T := Measurable.of_eval fun ai => (measurable_affine A).iterate _
  refine ⟨_, isCompleteMix_symmetrize (n := j * m) (Nat.pos_of_ne_zero (mul_ne_zero hj hm0))
    (by simp) ((unifSet K).map T) (s := j • m • c) ?_ ?_⟩
  · rw [ae_map_iff hT.aemeasurable (measurableSet_sum_eq_gen _)]
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [T, Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun i => (⇑A)^[i] y) m]
    simp [orbit_sum A hm h1 hc]
  · have hmarg : ∀ ai : Fin j × Fin m, ((unifSet K).map T).map (fun z => z ai) = unifSet K := by
      intro ai
      rw [Measure.map_map (measurable_pi_apply ai) hT]
      exact map_iterate_eq (measurable_affine A) hU ai.2
    simp only [hmarg, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, ENNReal.inv_mul_cancel
      (by exact_mod_cast mul_ne_zero hj hm0) (ENNReal.natCast_ne_top _), one_smul]

/-- **Proposition 98, second statement.** With `A`, `K` as above, let `L ⊆ K` be measurable with
`A(L) = L`, `0 < |L|`, and let `U(L)` be `r`-completely mixable. Then `U(K)` is `n`-completely
mixable for every `n = j m + r` with `j ≥ 1` and `n |L| ≥ r |K|`. The mix is a uniformly random
permutation of `(P, AP, …, A^{m-1}P, …, P, AP, …, A^{m-1}P, X₁, …, X_r)` with `j` orbits, where
`(X₁, …, X_r)` is an `r`-complete mix of `U(L)` and, independently, `P` has the density (25). -/
theorem completelyMixable_add (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm0 : m ≠ 0) (hm : (⇑A)^[m] = id)
    (h1 : ∀ v, A.linear v = v → v = 0) {K L : Set V} (hK : MeasurableSet K)
    (hL : MeasurableSet L) (hLK : L ⊆ K) (hAK : A '' K = K) (hAL : A '' L = L)
    (hL0 : volume L ≠ 0) (hKfin : volume K ≠ ∞) {r : ℕ} (hLmix : CompletelyMixable r (unifSet L))
    {j : ℕ} (hj : j ≠ 0)
    (hcond : (r : ℝ) * (volume K).toReal ≤ ((j * m + r : ℕ) : ℝ) * (volume L).toReal) :
    CompletelyMixable (j * m + r) (unifSet K) := by
  obtain ⟨c, hc, -⟩ := exists_unique_fixed A h1
  obtain ⟨R, hRprob, ⟨s, hs⟩, hRmarg⟩ := hLmix
  have hA := measurePreserving_affine A hm0 hm
  have hjm : 0 < j * m := Nat.pos_of_ne_zero (mul_ne_zero hj hm0)
  have hrn : r < j * m + r := by omega
  have hP := isProbabilityMeasure_symmMeasure hK hL hLK hL0 hKfin hrn hcond
  have hPA : (symmMeasure (j * m + r) r K L).map A = symmMeasure (j * m + r) r K L := by
    refine map_withDensity_eq A hA
      (ENNReal.measurable_ofReal.comp (measurable_symmDensity hK hL)) fun y => ?_
    rw [symmDensity_comp A (preimage_eq_of_image_eq A.injective hAK)
      (preimage_eq_of_image_eq A.injective hAL)]
  let T : V × (Fin r → V) → ((Fin j × Fin m) ⊕ Fin r → V) :=
    fun w => Sum.elim (fun ai => (⇑A)^[ai.2] w.1) w.2
  have hT : Measurable T := by
    refine Measurable.of_eval fun i => ?_
    cases i with
    | inl ai => exact ((measurable_affine A).iterate _).comp measurable_fst
    | inr t => exact (measurable_pi_apply t).comp measurable_snd
  set μP := symmMeasure (j * m + r) r K L
  refine ⟨_, isCompleteMix_symmetrize (n := j * m + r) (by omega) (by simp)
    ((μP.prod R).map T) (s := j • m • c + s) ?_ ?_⟩
  · rw [ae_map_iff hT.aemeasurable (measurableSet_sum_eq_gen _)]
    have hs' : ∀ᵐ w ∂(μP.prod R), ∑ t, w.2 t = s :=
      ae_of_ae_map (p := fun x : Fin r → V => ∑ t, x t = s)
        (measurable_snd.aemeasurable (μ := μP.prod R)) (by
        rw [Measure.map_snd_prod, measure_univ, one_smul]; exact hs)
    filter_upwards [hs'] with w hw
    simp only [T, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, hw]
    rw [Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun i => (⇑A)^[i] w.1) m]
    simp [orbit_sum A hm h1 hc]
  · have hl : ∀ ai : Fin j × Fin m, ((μP.prod R).map T).map (fun z => z (Sum.inl ai)) = μP := by
      intro ai
      rw [Measure.map_map (measurable_pi_apply _) hT]
      change (μP.prod R).map ((⇑A)^[ai.2] ∘ Prod.fst) = μP
      rw [← Measure.map_map ((measurable_affine A).iterate _) measurable_fst,
        Measure.map_fst_prod, measure_univ, one_smul]
      exact map_iterate_eq (measurable_affine A) hPA ai.2
    have hr : ∀ t : Fin r, ((μP.prod R).map T).map (fun z => z (Sum.inr t)) = unifSet L := by
      intro t
      rw [Measure.map_map (measurable_pi_apply _) hT]
      change (μP.prod R).map ((fun x : Fin r → V => x t) ∘ Prod.snd) = unifSet L
      rw [← Measure.map_map (measurable_pi_apply t) measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul]
      exact hRmarg t
    rw [Fintype.sum_sum_type]
    simp only [hl, hr, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin]
    have hid := symmMeasure_identity hK hL hLK hL0 hKfin hrn hcond
    rw [Nat.add_sub_cancel] at hid
    rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, ← Nat.cast_smul_eq_nsmul ℝ≥0∞ r, hid, smul_smul,
      ENNReal.inv_mul_cancel (by exact_mod_cast (show j * m + r ≠ 0 by omega))
        (ENNReal.natCast_ne_top _), one_smul]

/-- **Proposition 98, final statement** (central symmetry, `m = 2`, `A(x) = 2c - x`, `r = 3`): if
`K` and `L ⊆ K` are symmetric about `c` and `U(L)` is `3`-completely mixable, then `U(K)` is
`n`-completely mixable for every even `n ≥ 2` and every odd `n` with `3 |K| ≤ n |L|`. For `n = 3`
the condition gives `|L| ≥ |K|`, so `U(L) = U(K)` (`unifSet_eq_of_volume_le`). -/
theorem completelyMixable_centralSymm {K L : Set V} {c : V} (hK : MeasurableSet K)
    (hL : MeasurableSet L) (hLK : L ⊆ K) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hLs : AffineEquiv.pointReflection ℝ c '' L = L) (hL0 : volume L ≠ 0)
    (hKfin : volume K ≠ ∞) (h3 : CompletelyMixable 3 (unifSet L)) :
    (∀ n : ℕ, Even n → n ≠ 0 → CompletelyMixable n (unifSet K)) ∧
      (∀ n : ℕ, Odd n → (3 : ℝ) * (volume K).toReal ≤ n * (volume L).toReal →
        CompletelyMixable n (unifSet K)) := by
  set A := AffineEquiv.pointReflection ℝ c
  have hA2 : (⇑A)^[2] = id := by
    funext x
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact AffineEquiv.pointReflection_involutive ℝ c x
  have hlin : ∀ v, A.linear v = -v := by
    intro v
    have h := affine_apply_eq A v 0
    rw [sub_zero] at h
    have e1 : A v = c - v + c := by simp [A, Equiv.pointReflection_apply]
    have e0 : A 0 = c + c := by simp [A, Equiv.pointReflection_apply]
    rw [eq_sub_of_add_eq h.symm, e1, e0]; abel
  have h1 : ∀ v, A.linear v = v → v = 0 := by
    intro v hv
    rw [hlin] at hv
    have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rw 1 [← hv]; exact neg_add_cancel v
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have hK0 : volume K ≠ 0 := fun h => hL0 (measure_mono_null hLK h)
  have hLfin : volume L ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hLK)
  have hκ : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKfin
  have hle : (volume L).toReal ≤ (volume K).toReal :=
    ENNReal.toReal_mono hKfin (measure_mono hLK)
  refine ⟨fun n hn hn0 => ?_, fun n hn hcond => ?_⟩
  · obtain ⟨j, rfl⟩ := hn
    have : j + j = j * 2 := by ring
    rw [this]
    exact completelyMixable_mul A two_ne_zero hA2 h1 hK hKs hK0 hKfin (by omega)
  · obtain ⟨k, rfl⟩ := hn
    rcases Nat.lt_or_ge k 1 with hk | hk
    · exfalso
      have : k = 0 := by omega
      subst this
      norm_num at hcond
      linarith
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      have hle' : volume K ≤ volume L := by
        rw [← ENNReal.toReal_le_toReal hKfin hLfin]; norm_num at hcond; linarith
      rw [← unifSet_eq_of_volume_le hL hLK hKfin hle']
      exact h3
    · have he : 2 * k + 1 = (k - 1) * 2 + 3 := by omega
      rw [he] at hcond ⊢
      exact completelyMixable_add A two_ne_zero hA2 h1 hK hL hLK hKs hLs hL0 hKfin h3
        (by omega) hcond

/-- The mean of an `A`-invariant probability measure (such as `U(L)` with `A(L) = L`) is fixed
by `A`, so it is the fixed point `c`. -/
theorem integral_eq_fixed (A : V ≃ᵃ[ℝ] V) {ν : Measure V} [IsProbabilityMeasure ν]
    (hν : ν.map A = ν) (hint : Integrable id ν) : A (∫ x, x ∂ν) = ∫ x, x ∂ν := by
  let A₀ : V →L[ℝ] V := LinearMap.toContinuousLinearMap (A.linear : V →ₗ[ℝ] V)
  have hA : ∀ x, A x = A₀ x + A 0 := fun x => by simpa [A₀] using affine_apply_eq A x 0
  conv_rhs => rw [← hν]
  rw [integral_map (f := fun x => x) (measurable_affine A).aemeasurable
    aestronglyMeasurable_id]
  have hi1 : Integrable (fun x => A₀ x) ν := A₀.integrable_comp hint
  have hc : ∫ x, A₀ x ∂ν = A₀ (∫ x, x ∂ν) := A₀.integral_comp_comm hint
  rw [integral_congr_ae (ae_of_all _ hA), integral_add hi1 (integrable_const _), hc,
    integral_const, probReal_univ, one_smul, hA (∫ x, x ∂ν)]

/-- The constant sum of an `r`-complete mix of an integrable `F` is `r` times the mean of `F`; for
`F = U(L)` it is `r • c`, so the tuple of Proposition 98 has the sum `j m c + r c = n c`. -/
theorem sum_eq_of_isCompleteMix {r : ℕ} {F : Measure V} {R : Measure (Fin r → V)}
    (hR : IsCompleteMix r F R) (hint : Integrable id F) {s : V}
    (hs : ∀ᵐ x ∂R, ∑ t, x t = s) : s = r • ∫ x, x ∂F := by
  obtain ⟨hRp, -, hRm'⟩ := hR
  have hRm : ∀ t : Fin r, R.map (fun x => x t) = F := hRm'
  have hi : ∀ t : Fin r, Integrable (fun x : Fin r → V => x t) R := by
    intro t
    have := hint
    rw [← hRm t] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply t).aemeasurable).1 this
  have h1 : ∫ x, ∑ t, x t ∂R = s := by
    rw [integral_congr_ae hs, integral_const, probReal_univ, one_smul]
  have h2 : ∫ x, ∑ t, x t ∂R = ∑ t : Fin r, ∫ x, x ∂F := by
    rw [integral_finsetSum _ fun t _ => hi t]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hRm t, integral_map (φ := fun x : Fin r → V => x t) (f := fun x : V => x)
      (measurable_pi_apply t).aemeasurable aestronglyMeasurable_id]
  rw [← h1, h2, sum_const, card_univ, Fintype.card_fin]

/-- The mean of `U(L)` is the fixed point `c` of `A`, and the constant sum of an `r`-complete mix of
`U(L)` is `r • c`; with the `j` orbits the tuple of Proposition 98 has the sum
`j m c + r c = (j m + r) c`. (Integrability of `U(L)` holds for bounded `L`.) -/
theorem sum_eq_smul_fixed (A : V ≃ᵃ[ℝ] V) {m : ℕ} (hm0 : m ≠ 0) (hm : (⇑A)^[m] = id)
    (h1 : ∀ v, A.linear v = v → v = 0) {L : Set V} (hL : MeasurableSet L) (hAL : A '' L = L)
    (hL0 : volume L ≠ 0) (hLfin : volume L ≠ ∞) (hint : Integrable id (unifSet L)) {c : V}
    (hc : A c = c) {r : ℕ} {R : Measure (Fin r → V)} (hR : IsCompleteMix r (unifSet L) R) {s : V}
    (hs : ∀ᵐ x ∂R, ∑ t, x t = s) (j : ℕ) :
    ∫ x, x ∂(unifSet L) = c ∧ s = r • c ∧ j • m • c + s = (j * m + r) • c := by
  have := isProbabilityMeasure_unifSet hL0 hLfin
  have hU := map_unifSet A (measurePreserving_affine A hm0 hm) hL
    (preimage_eq_of_image_eq A.injective hAL)
  obtain ⟨c', _, huniq⟩ := exists_unique_fixed A h1
  have hmean : ∫ x, x ∂(unifSet L) = c :=
    (huniq _ (integral_eq_fixed A hU hint)).trans (huniq _ hc).symm
  have hsum : s = r • c := by rw [sum_eq_of_isCompleteMix hR hint hs, hmean]
  refine ⟨hmean, hsum, ?_⟩
  rw [hsum, add_nsmul, mul_nsmul']

end Main

end Mixes
