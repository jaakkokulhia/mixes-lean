import Mixes.Defs

/-!
# Joint mixes of uniform distributions (Lemma 1, Definition 2, Lemma 3)

This file formalises Section 3 of the paper (`lem:arch`, `def:tuple`, `lem:sym`).

* `abs_two_mul_take_sum_sub_le`: the balancing step of Lemma 1, `|S - T| ≤ λ_k`.
* `triangle_of_orthonormal`, `triangle_R3`: the triangle `E_k + E_G + E_H = 0` with the side lengths
  `λ_k`, `S`, `T`, in the explicit coordinates of the paper.
* `IsArchimedesMeasure`: the theorem of Archimedes, stated as a property of a probability measure
  `σ` on a real inner product space: every projection `ξ ↦ ⟪e, ξ⟫` is `U[-‖e‖, ‖e‖]`.
  Mathlib has no surface measure on `S²` with this property. Lemma 1 only uses projections onto
  vectors in one plane, so we construct a planar measure instead: `archPlane`, with density
  `1 / (2π √(1 - ‖x‖²))` on the unit disc of `ℝ²` (the law of the projection of a uniform point of
  `S²` to a plane; this identification is not formalised), and prove
  `isArchimedesMeasure_archPlane`.
* `isJointMix_map_inner`: the core of Lemma 1, for arbitrary vectors `v j` with `∑ v j = 0`.
* `lem_arch`: Lemma 1, for any Archimedes measure; `exists_lem_arch_admissible`: with the choices
  of the paper made, for an admissible tuple.
* `lem_sym`, `lem_sym_admissible`: Lemma 3.
* `exists_jointMix_admissible`, `completelyMixable_mixtureMarginal'`: Lemmas 1 and 3 without
  hypotheses, with `σ = archPlane`.
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Mixes

/-! ### (a) The balancing step -/

/-- A sequence that starts `≤ 0`, ends `≥ 0` and increases by at most `2M` per step takes a value
of absolute value `≤ M`. -/
lemma exists_abs_le_of_steps (f : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∀ N, f 0 ≤ 0 → 0 ≤ f N → (∀ i < N, f (i + 1) ≤ f i + 2 * M) → ∃ i ≤ N, |f i| ≤ M := by
  intro N
  induction N with
  | zero =>
    intro h0 h1 _
    exact ⟨0, le_rfl, abs_le.2 ⟨by linarith, by linarith⟩⟩
  | succ N ih =>
    intro h0 h1 hst
    by_cases hN : 0 ≤ f N
    · obtain ⟨i, hi, h⟩ := ih h0 hN (fun i hi => hst i (by omega))
      exact ⟨i, by omega, h⟩
    · push Not at hN
      have := hst N (by omega)
      by_cases h2 : f (N + 1) ≤ M
      · exact ⟨N + 1, le_rfl, abs_le.2 ⟨by linarith, h2⟩⟩
      · exact ⟨N, by omega, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- Some prefix of a list of numbers in `[0, M]` has twice its sum within `M` of the total. -/
lemma exists_take_balanced (a : List ℝ) {M : ℝ} (hM : 0 ≤ M) (h0 : ∀ x ∈ a, 0 ≤ x)
    (h1 : ∀ x ∈ a, x ≤ M) : ∃ s ≤ a.length, |2 * (a.take s).sum - a.sum| ≤ M := by
  have hsum : 0 ≤ a.sum := List.sum_nonneg h0
  obtain ⟨i, hi, h⟩ := exists_abs_le_of_steps (fun s => 2 * (a.take s).sum - a.sum) hM a.length
    (by simp [hsum]) (by simp [List.take_of_length_le le_rfl]; linarith)
    (by
      intro i hi
      simp only [List.sum_take_succ a i hi]
      have := h1 _ (List.getElem_mem hi)
      linarith)
  exact ⟨i, hi, h⟩

/-- The balancing step of Lemma 1: if `s` minimises `|2 (a₁ + ⋯ + a_s) - ∑ a|` and all `a_i` lie
in `[0, M]`, then the minimum is at most `M`. -/
theorem abs_two_mul_take_sum_sub_le (a : List ℝ) {M : ℝ} (hM : 0 ≤ M) (h0 : ∀ x ∈ a, 0 ≤ x)
    (h1 : ∀ x ∈ a, x ≤ M) (s : ℕ)
    (hs : ∀ s' ≤ a.length, |2 * (a.take s).sum - a.sum| ≤ |2 * (a.take s').sum - a.sum|) :
    |2 * (a.take s).sum - a.sum| ≤ M := by
  obtain ⟨i, hi, h⟩ := exists_take_balanced a hM h0 h1
  exact (hs i hi).trans h

/-! ### (b) The triangle -/

section Triangle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_sq_smul_add_smul {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (p q : ℝ) : ‖p • u + q • v‖ ^ 2 = p ^ 2 + q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    huv, hvu, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, hv]
  ring

/-- The triangle of Lemma 1 in a plane spanned by orthonormal `u, v`: if `|S - T| ≤ a ≤ S + T`
and `a > 0`, then `E_k = a u`, `E_G = (x - a) u + y v`, `E_H = -(x u + y v)` with
`x = (a² + T² - S²) / (2a)` and `y = √(T² - x²)` have norms `a`, `S`, `T` and sum `0`. -/
theorem triangle_of_orthonormal {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    {a S T : ℝ} (ha : 0 < a) (hS : 0 ≤ S) (hT : 0 ≤ T) (h1 : |S - T| ≤ a) (h2 : a ≤ S + T) :
    let x := (a ^ 2 + T ^ 2 - S ^ 2) / (2 * a)
    let y := √(T ^ 2 - x ^ 2)
    ‖a • u‖ = a ∧ ‖(x - a) • u + y • v‖ = S ∧ ‖-(x • u + y • v)‖ = T ∧
      a • u + ((x - a) • u + y • v) + -(x • u + y • v) = 0 := by
  intro x y
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  have hx : 2 * a * x = a ^ 2 + T ^ 2 - S ^ 2 := by
    simp only [x]; field_simp
  have hxT : x ^ 2 ≤ T ^ 2 := by
    have hnum : |a ^ 2 + T ^ 2 - S ^ 2| ≤ 2 * a * T := by
      rw [abs_le]; constructor <;> nlinarith
    have : |x| ≤ T := by
      have h2a : (0 : ℝ) < 2 * a := by positivity
      rw [← mul_le_mul_iff_of_pos_left h2a, ← abs_of_pos h2a, ← abs_mul, abs_of_pos h2a, hx]
      linarith
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  have hy : y ^ 2 = T ^ 2 - x ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  · rw [← pow_left_inj₀ (norm_nonneg _) hS two_ne_zero, norm_sq_smul_add_smul hu hv huv, hy]
    nlinarith
  · rw [norm_neg, ← pow_left_inj₀ (norm_nonneg _) hT two_ne_zero,
      norm_sq_smul_add_smul hu hv huv, hy]
    ring
  · rw [sub_smul]; abel

/-- The triangle of Lemma 1 in `ℝ³` with the explicit coordinates of the paper:
`E_k = (λ_k, 0, 0)`, `E_H = -(x, y, 0)`, `E_G = (x - λ_k, y, 0)`. -/
theorem triangle_R3 {a S T : ℝ} (ha : 0 < a) (hS : 0 ≤ S) (hT : 0 ≤ T) (h1 : |S - T| ≤ a)
    (h2 : a ≤ S + T) :
    let x := (a ^ 2 + T ^ 2 - S ^ 2) / (2 * a)
    let y := √(T ^ 2 - x ^ 2)
    let Ek : EuclideanSpace ℝ (Fin 3) := !₂[a, 0, 0]
    let EG : EuclideanSpace ℝ (Fin 3) := !₂[x - a, y, 0]
    let EH : EuclideanSpace ℝ (Fin 3) := -!₂[x, y, 0]
    ‖Ek‖ = a ∧ ‖EG‖ = S ∧ ‖EH‖ = T ∧ Ek + EG + EH = 0 := by
  intro x y Ek EG EH
  set u : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  set v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have huv : ⟪u, v⟫_ℝ = 0 := by simp [u, v, EuclideanSpace.inner_single_left]
  have hEk : Ek = a • u := by ext i; fin_cases i <;> simp [Ek, u]
  have hEG : EG = (x - a) • u + y • v := by ext i; fin_cases i <;> simp [EG, u, v]
  have hEH : EH = -(x • u + y • v) := by ext i; fin_cases i <;> simp [EH, u, v]
  rw [hEk, hEG, hEH]
  exact triangle_of_orthonormal hu hv huv ha hS hT h1 h2

end Triangle

/-! ### (c) The theorem of Archimedes, and the core of Lemma 1 -/

/-- Translating `U[a, b]` by `m` gives `U[m + a, m + b]` (also for point masses). -/
lemma map_unifI_const_add (a b m : ℝ) :
    (unifI a b).map (fun t => m + t) = unifI (m + a) (m + b) := by
  have hf : Measurable (fun t : ℝ => m + t) := measurable_const_add m
  unfold unifI
  split_ifs with h1 h2 h2
  · rw [Measure.map_smul, show m + b - (m + a) = b - a by ring]
    congr 1
    conv_rhs => rw [← (measurePreserving_add_left volume m).map_eq,
      Measure.restrict_map hf measurableSet_Icc, Set.preimage_const_add_Icc]
    simp
    exact hf.aemeasurable
  · exact absurd (by linarith) h2
  · exact absurd (by linarith) h1
  · rw [Measure.map_dirac' hf]

section Archimedes

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The theorem of Archimedes as a property of a measure: `σ` is a probability measure and for
every `e` the law of `ξ ↦ ⟪e, ξ⟫` under `σ` is `U[-‖e‖, ‖e‖]`. The uniform distribution on the
unit sphere `S² ⊂ ℝ³` has this property; Mathlib does not contain this fact. The general
theorems below take such a measure as a hypothesis; only vectors `e` in one plane are used, and
`isArchimedesMeasure_archPlane` provides such a measure on `ℝ²`. -/
def IsArchimedesMeasure (σ : Measure V) : Prop :=
  IsProbabilityMeasure σ ∧ ∀ e : V, σ.map (fun ξ => ⟪e, ξ⟫_ℝ) = unifI (-‖e‖) ‖e‖

variable {n : ℕ}

lemma measurable_affine_inner (m : Fin n → ℝ) (v : Fin n → V) :
    Measurable (fun ξ : V => fun j => m j + ⟪v j, ξ⟫_ℝ) :=
  measurable_pi_iff.2 fun _ =>
    (continuous_const.add (continuous_const.inner continuous_id)).measurable

lemma measurableSet_sum_eq (c : ℝ) : MeasurableSet {x : Fin n → ℝ | ∑ j, x j = c} :=
  measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const

/-- The core of Lemma 1: for an Archimedes measure `σ`, numbers `m j` and vectors `v j` with
`∑ v j = 0`, the law of `ξ ↦ (m j + ⟪v j, ξ⟫)_j` is a joint mix of the `U[m j - ‖v j‖, m j + ‖v j‖]`
whose coordinates add up to `∑ m j` almost surely. -/
theorem isJointMix_map_inner {σ : Measure V} (hσ : IsArchimedesMeasure σ) (m : Fin n → ℝ)
    (v : Fin n → V) (hv : ∑ j, v j = 0) :
    IsJointMix (fun j => unifI (m j - ‖v j‖) (m j + ‖v j‖))
        (σ.map fun ξ j => m j + ⟪v j, ξ⟫_ℝ) ∧
      ∀ᵐ x ∂(σ.map fun ξ j => m j + ⟪v j, ξ⟫_ℝ), ∑ j, x j = ∑ j, m j := by
  obtain ⟨hprob, hproj⟩ := hσ
  have hX := measurable_affine_inner m v
  have hsum : ∀ᵐ x ∂(σ.map fun ξ j => m j + ⟪v j, ξ⟫_ℝ), ∑ j, x j = ∑ j, m j := by
    rw [ae_map_iff hX.aemeasurable (measurableSet_sum_eq _)]
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Finset.sum_add_distrib, ← sum_inner, hv, inner_zero_left, add_zero]
  have := hprob
  refine ⟨⟨inferInstance, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  rw [Measure.map_map (measurable_pi_apply j) hX]
  have hin : Measurable (fun ξ : V => ⟪v j, ξ⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  have : ((fun x : Fin n → ℝ => x j) ∘ fun ξ j => m j + ⟪v j, ξ⟫_ℝ) =
      (fun t => m j + t) ∘ (fun ξ : V => ⟪v j, ξ⟫_ℝ) := rfl
  rw [this, ← Measure.map_map (measurable_const_add _) hin, hproj, map_unifI_const_add]
  simp only [sub_eq_add_neg]

end Archimedes

/-! ### (d) Lemma 1 -/

section Lemma1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {n : ℕ}

/-- The random vector of Lemma 1 as a function of `ξ`: `X_k = (l_k + r_k)/2 + E_k·ξ/2`,
`X_j = (l_j + r_j)/2 + λ_j/(2S) E_G·ξ` for `j ∈ G` and `X_j = (l_j + r_j)/2 + λ_j/(2T) E_H·ξ`
otherwise, where `λ_j = r_j - l_j`, `S = ∑_{j ∈ G} λ_j`, `T = ∑_{j ∈ H} λ_j`. A coefficient with
`S = 0` or `T = 0` is `0` by the convention `x / 0 = 0`, as in the paper. -/
def archVec (l r : Fin n → ℝ) (k : Fin n) (G H : Finset (Fin n)) (Ek EG EH : V) (ξ : V) :
    Fin n → ℝ := fun j =>
  if j = k then (l j + r j) / 2 + 1 / 2 * ⟪Ek, ξ⟫_ℝ
  else if j ∈ G then (l j + r j) / 2 + (r j - l j) / (2 * ∑ i ∈ G, (r i - l i)) * ⟪EG, ξ⟫_ℝ
  else (l j + r j) / 2 + (r j - l j) / (2 * ∑ i ∈ H, (r i - l i)) * ⟪EH, ξ⟫_ℝ

omit [MeasurableSpace V] [BorelSpace V] in
lemma norm_coef_smul {lam S : ℝ} {E : V} (hl : 0 ≤ lam) (hlS : lam ≤ S) (hE : ‖E‖ = S) :
    ‖(lam / (2 * S)) • E‖ = lam / 2 := by
  rw [norm_smul, hE, Real.norm_eq_abs]
  rcases eq_or_lt_of_le (hl.trans hlS) with hS | hS
  · subst hS; simp [le_antisymm hlS hl]
  · rw [abs_of_nonneg (by positivity)]; field_simp

omit [MeasurableSpace V] [BorelSpace V] in
lemma coef_sum_smul {S : ℝ} {E : V} (hE : ‖E‖ = S) : (S / (2 * S)) • E = (1 / 2 : ℝ) • E := by
  rcases eq_or_ne S 0 with hS | hS
  · rw [hS] at hE; simp [norm_eq_zero.1 hE]
  · congr 1; field_simp

/-- Lemma 1 for a given partition `{k} ∪ G ∪ H` of the indices and a given triangle: if
`‖E_k‖ = λ_k`, `‖E_G‖ = S`, `‖E_H‖ = T` and `E_k + E_G + E_H = 0`, then the law of `archVec` under
an Archimedes measure is a joint mix of the `U[l_j, r_j]` with sum `(1/2) ∑ (l_j + r_j)`. -/
theorem arch_of_partition {σ : Measure V} (hσ : IsArchimedesMeasure σ) (l r : Fin n → ℝ)
    (hle : ∀ j, l j ≤ r j) (k : Fin n) (G H : Finset (Fin n)) (hkG : k ∉ G) (hkH : k ∉ H)
    (hGH : Disjoint G H) (hcov : ∀ j, j = k ∨ j ∈ G ∨ j ∈ H) (Ek EG EH : V)
    (hEk : ‖Ek‖ = r k - l k) (hEG : ‖EG‖ = ∑ j ∈ G, (r j - l j))
    (hEH : ‖EH‖ = ∑ j ∈ H, (r j - l j)) (hsum : Ek + EG + EH = 0) :
    IsJointMix (fun j => unifI (l j) (r j)) (σ.map (archVec l r k G H Ek EG EH)) ∧
      ∀ᵐ x ∂(σ.map (archVec l r k G H Ek EG EH)), ∑ j, x j = 1 / 2 * ∑ j, (l j + r j) := by
  set S := ∑ j ∈ G, (r j - l j)
  set T := ∑ j ∈ H, (r j - l j)
  have hlam : ∀ j, 0 ≤ r j - l j := fun j => sub_nonneg.2 (hle j)
  let m : Fin n → ℝ := fun j => (l j + r j) / 2
  let v : Fin n → V := fun j =>
    if j = k then (1 / 2 : ℝ) • Ek
    else if j ∈ G then ((r j - l j) / (2 * S)) • EG else ((r j - l j) / (2 * T)) • EH
  have hX : archVec l r k G H Ek EG EH = fun ξ j => m j + ⟪v j, ξ⟫_ℝ := by
    funext ξ j
    simp only [archVec, m, v]
    split_ifs <;> rw [real_inner_smul_left]
  have hnorm : ∀ j, ‖v j‖ = (r j - l j) / 2 := by
    intro j
    simp only [v]
    split_ifs with h1 h2
    · subst h1
      rw [norm_smul, hEk, Real.norm_eq_abs, abs_of_pos (by norm_num)]; ring
    · exact norm_coef_smul (hlam j) (Finset.single_le_sum (fun i _ => hlam i) h2) hEG
    · have h3 : j ∈ H := ((hcov j).resolve_left h1).resolve_left h2
      exact norm_coef_smul (hlam j) (Finset.single_le_sum (fun i _ => hlam i) h3) hEH
  have hv : ∑ j, v j = 0 := by
    have huniv : (Finset.univ : Finset (Fin n)) = insert k (G ∪ H) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
      exact hcov j
    have hG : ∑ j ∈ G, v j = (1 / 2 : ℝ) • EG := by
      rw [← coef_sum_smul hEG, Finset.sum_div, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≠ k := fun h => hkG (h ▸ hj)
      simp [v, this, hj]
    have hH : ∑ j ∈ H, v j = (1 / 2 : ℝ) • EH := by
      rw [← coef_sum_smul hEH, Finset.sum_div, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≠ k := fun h => hkH (h ▸ hj)
      have hjG : j ∉ G := fun h => Finset.disjoint_left.1 hGH h hj
      simp [v, this, hjG]
    rw [huniv, Finset.sum_insert (by simp [hkG, hkH]), Finset.sum_union hGH, hG, hH]
    simp only [v, ite_true]
    rw [← smul_add, ← smul_add, ← add_assoc, hsum, smul_zero]
  obtain ⟨h1, h2⟩ := isJointMix_map_inner hσ m v hv
  have hF : (fun j => unifI (m j - ‖v j‖) (m j + ‖v j‖)) = fun j => unifI (l j) (r j) := by
    funext j; rw [hnorm j]; simp only [m]; congr 1 <;> ring
  have hm : ∑ j, m j = 1 / 2 * ∑ j, (l j + r j) := by
    simp only [m, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hX]
  exact ⟨hF ▸ h1, hm ▸ h2⟩

/-- **Lemma 1** (`lem:arch`). Let `l j ≤ r j`, not all lengths `λ_j = r j - l j` zero, with the
polygon inequality `2 λ_j ≤ ∑ λ_i`. Let `λ_k` be a largest length, let the list `L` enumerate the
other indices (`j₁, …, j_{n-1}`), and let `s ≤ n - 1` minimise
`|2 (λ_{j₁} + ⋯ + λ_{j_s}) - ∑_{j ≠ k} λ_j|`. With `G = {j₁, …, j_s}`, `H` the remaining indices,
`S = ∑_G λ_j` and `T = ∑_H λ_j`, we have `|S - T| ≤ λ_k ≤ S + T`, there are `E_k, E_G, E_H` (in
the plane of any orthonormal pair `u, v`) with norms `λ_k, S, T` and sum `0`, and for every
Archimedes measure `σ` the law of the vector `archVec` of the paper is a joint mix of the
`U[l_j, r_j]` whose coordinates add up to `(1/2) ∑ (l_j + r_j)`. -/
theorem lem_arch {σ : Measure V} (hσ : IsArchimedesMeasure σ) {u w : V} (hu : ‖u‖ = 1)
    (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0) (l r : Fin n → ℝ) (hle : ∀ j, l j ≤ r j)
    (hpos : ∃ j, l j < r j) (hpoly : ∀ j, 2 * (r j - l j) ≤ ∑ i, (r i - l i)) (k : Fin n)
    (hk : ∀ j, r j - l j ≤ r k - l k) (L : List (Fin n)) (hL : L.Nodup)
    (hLk : ∀ j, j ∈ L ↔ j ≠ k) (s : ℕ) (_hs : s ≤ L.length)
    (hmin : ∀ s' ≤ L.length,
      |2 * ((L.take s).map fun j => r j - l j).sum - ∑ j ∈ Finset.univ.erase k, (r j - l j)| ≤
        |2 * ((L.take s').map fun j => r j - l j).sum - ∑ j ∈ Finset.univ.erase k, (r j - l j)|) :
    let G := (L.take s).toFinset
    let H := (L.drop s).toFinset
    let S := ∑ j ∈ G, (r j - l j)
    let T := ∑ j ∈ H, (r j - l j)
    |S - T| ≤ r k - l k ∧ r k - l k ≤ S + T ∧
      ∃ Ek EG EH : V, ‖Ek‖ = r k - l k ∧ ‖EG‖ = S ∧ ‖EH‖ = T ∧ Ek + EG + EH = 0 ∧
        IsJointMix (fun j => unifI (l j) (r j)) (σ.map (archVec l r k G H Ek EG EH)) ∧
        ∀ᵐ x ∂(σ.map (archVec l r k G H Ek EG EH)), ∑ j, x j = 1 / 2 * ∑ j, (l j + r j) := by
  intro G H S T
  set lam : Fin n → ℝ := fun j => r j - l j with hlam_def
  have hlam : ∀ j, 0 ≤ lam j := fun j => sub_nonneg.2 (hle j)
  have hkpos : 0 < lam k := by
    obtain ⟨j, hj⟩ := hpos
    exact lt_of_lt_of_le (sub_pos.2 hj) (hk j)
  have hSl : S = ((L.take s).map lam).sum :=
    List.sum_toFinset _ (hL.sublist (List.take_sublist _ _))
  have hTl : T = ((L.drop s).map lam).sum :=
    List.sum_toFinset _ (hL.sublist (List.drop_sublist _ _))
  have hLfin : L.toFinset = Finset.univ.erase k := by
    ext j; simp [hLk]
  have hrest : ∑ j ∈ Finset.univ.erase k, lam j = S + T := by
    rw [← hLfin, List.sum_toFinset _ hL, hSl, hTl, ← List.sum_append, ← List.map_append,
      List.take_append_drop]
  -- the balancing step
  have hbal : |S - T| ≤ lam k := by
    have h := abs_two_mul_take_sum_sub_le (L.map lam) (hlam k)
      (fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact hlam j)
      (fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact hk j) s
      (by
        intro s' hs'
        rw [List.length_map] at hs'
        rw [← List.map_take, ← List.map_take, ← List.sum_toFinset _ hL, hLfin]
        exact hmin s' hs')
    rw [← List.map_take, ← hSl, ← List.sum_toFinset _ hL, hLfin, hrest] at h
    rwa [show 2 * S - (S + T) = S - T by ring] at h
  have htri : lam k ≤ S + T := by
    have := hpoly k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at this
    change 2 * lam k ≤ lam k + ∑ j ∈ Finset.univ.erase k, lam j at this
    linarith [hrest]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hlam j
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => hlam j
  obtain ⟨hEk, hEG, hEH, hsum⟩ := triangle_of_orthonormal hu hw huw hkpos hS0 hT0 hbal htri
  refine ⟨hbal, htri, _, _, _, hEk, hEG, hEH, hsum, ?_⟩
  have hdisj := List.disjoint_take_drop hL (le_refl s)
  refine arch_of_partition hσ l r hle k G H ?_ ?_ ?_ ?_ _ _ _ hEk hEG hEH hsum
  · intro h; exact (hLk k).1 (List.mem_of_mem_take (List.mem_toFinset.1 h)) rfl
  · intro h; exact (hLk k).1 (List.mem_of_mem_drop (List.mem_toFinset.1 h)) rfl
  · exact Finset.disjoint_left.2 fun j h1 h2 =>
      hdisj (List.mem_toFinset.1 h1) (List.mem_toFinset.1 h2)
  · intro j
    by_cases hj : j = k
    · exact Or.inl hj
    · right
      have : j ∈ L.take s ++ L.drop s := by rw [List.take_append_drop]; exact (hLk j).2 hj
      rcases List.mem_append.1 this with h | h
      · exact Or.inl (List.mem_toFinset.2 h)
      · exact Or.inr (List.mem_toFinset.2 h)

end Lemma1

/-! ### Lemma 3 -/

section Lemma3

open Equiv

variable {n : ℕ}

/-- Averaging over all permutations: `(1/n!) ∑_π f (π j) = (1/n) ∑_i f i`. -/
lemma perm_avg (f : Fin n → ℝ≥0∞) (j : Fin n) :
    (n.factorial : ℝ≥0∞)⁻¹ * ∑ π : Perm (Fin n), f (π j) = (n : ℝ≥0∞)⁻¹ * ∑ i, f i := by
  have hn : (n : ℝ≥0∞) ≠ 0 := by simpa using (Nat.pos_of_ne_zero fun h => (h ▸ j).elim0).ne'
  have hf : (n.factorial : ℝ≥0∞) ≠ 0 := by simpa using Nat.factorial_ne_zero n
  have key : ∀ j', ∑ π : Perm (Fin n), f (π j') = ∑ π : Perm (Fin n), f (π j) := fun j' =>
    Fintype.sum_equiv (Equiv.mulRight (swap j j')) _ _ fun π => by
      simp [Perm.mul_apply]
  have hcount : (n : ℝ≥0∞) * ∑ π : Perm (Fin n), f (π j) = n.factorial * ∑ i, f i := by
    calc (n : ℝ≥0∞) * ∑ π : Perm (Fin n), f (π j)
        = ∑ j' : Fin n, ∑ π : Perm (Fin n), f (π j') := by simp [key]
      _ = ∑ π : Perm (Fin n), ∑ j' : Fin n, f (π j') := Finset.sum_comm
      _ = ∑ π : Perm (Fin n), ∑ i, f i :=
          Finset.sum_congr rfl fun π _ => Equiv.sum_comp π f
      _ = n.factorial * ∑ i, f i := by simp [Fintype.card_perm]
  calc (n.factorial : ℝ≥0∞)⁻¹ * ∑ π : Perm (Fin n), f (π j)
      = (n.factorial : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞)⁻¹ * (n * ∑ π : Perm (Fin n), f (π j))) := by
        rw [← mul_assoc ((n : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top n),
          one_mul]
    _ = (n : ℝ≥0∞)⁻¹ * ∑ i, f i := by
        rw [hcount, mul_left_comm ((n : ℝ≥0∞)⁻¹), ← mul_assoc (n.factorial : ℝ≥0∞)⁻¹,
          ENNReal.inv_mul_cancel hf (ENNReal.natCast_ne_top _), one_mul]

/-- The law of `(X_{π(1)}, …, X_{π(n)})` with `π` uniformly random and independent of `X ∼ P`. -/
def permAvg (P : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞)⁻¹ • ∑ π : Perm (Fin n), P.map (fun x => x ∘ π)

/-- The law of the mixture: choose `i` with probability `w i`, then draw from `Q i`. -/
def mixture {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞) (Q : ι → Measure (Fin n → ℝ)) :
    Measure (Fin n → ℝ) :=
  ∑ i, w i • Q i

lemma measurable_comp_perm (π : Perm (Fin n)) : Measurable (fun x : Fin n → ℝ => x ∘ π) :=
  measurable_pi_iff.2 fun j => measurable_pi_apply (π j)

/-- **Lemma 3** (`lem:sym`), for arbitrary joint mixes: if `P i` is a joint mix of
`F i 0, …, F i (n-1)` whose coordinates add up to `c` almost surely, and the weights `w i` add up
to `1`, then choosing `i` with probability `w i` and permuting the coordinates of a draw from `P i`
by a uniformly random permutation gives an `n`-complete mix of `∑_i w i (1/n) ∑_j F i j`, with
sum `c`. -/
theorem lem_sym {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (F : ι → Fin n → Measure ℝ) (P : ι → Measure (Fin n → ℝ)) (c : ℝ)
    (hP : ∀ i, IsJointMix (F i) (P i)) (hc : ∀ i, ∀ᵐ x ∂(P i), ∑ j, x j = c) :
    IsCompleteMix n (∑ i, w i • ((n : ℝ≥0∞)⁻¹ • ∑ j, F i j)) (mixture w fun i => permAvg (P i)) ∧
      ∀ᵐ x ∂(mixture w fun i => permAvg (P i)), ∑ j, x j = c := by
  have hsumset := measurableSet_sum_eq (n := n) c
  -- the measure of the complement of the hyperplane vanishes
  have hnull : (mixture w fun i => permAvg (P i)) {x | ∑ j, x j = c}ᶜ = 0 := by
    simp only [mixture, permAvg, sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_eq_zero, mul_zero, mul_zero]
    intro π _
    rw [Measure.map_apply (measurable_comp_perm π) hsumset.compl]
    have h := (ae_iff.1 (hc i))
    refine le_antisymm (le_trans (measure_mono ?_) h.le) zero_le
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
    rwa [Function.comp_def, Equiv.sum_comp π (fun j => x j)] at hx
  have hae : ∀ᵐ x ∂(mixture w fun i => permAvg (P i)), ∑ j, x j = c := by
    rw [ae_iff]; simpa [Set.compl_def] using hnull
  refine ⟨⟨⟨?_⟩, ⟨c, hae⟩, fun j => ?_⟩, hae⟩
  · simp only [mixture, permAvg, sum_apply, smul_apply, smul_eq_mul]
    rw [← hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hP i).1
    simp only [Measure.map_apply (measurable_comp_perm _) MeasurableSet.univ, Set.preimage_univ,
      measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    rw [ENNReal.inv_mul_cancel (by simpa using Nat.factorial_ne_zero n)
      (ENNReal.natCast_ne_top _), mul_one]
  · ext A hA
    rw [Measure.map_apply (measurable_pi_apply j) hA]
    simp only [mixture, permAvg, sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hmap : ∀ π : Perm (Fin n), (P i).map (fun x => x ∘ π) ((fun x => x j) ⁻¹' A) =
        F i (π j) A := by
      intro π
      rw [Measure.map_apply (measurable_comp_perm π) (measurable_pi_apply j hA),
        ← (hP i).2.2 (π j), Measure.map_apply (measurable_pi_apply (π j)) hA]
      rfl
    simp only [hmap]
    exact perm_avg (fun i' => F i i' A) j

/-- The marginal of a mixture of admissible tuples (Definition 2): `∑_i w i m_{τ i}`. -/
def mixtureMarginal {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞) (τ : ι → Admissible n) : Measure ℝ :=
  ∑ i, w i • (τ i).marginal

/-- **Lemma 3** (`lem:sym`) for admissible tuples: if `P i` is a joint mix of the `U(I_j)` of
the tuple `τ i` with sum `n` (as given by Lemma 1, see `exists_lem_arch_admissible`), the mixture
with weights `w i`, followed by a uniformly random permutation, is an `n`-complete mix of the
marginal `∑ w i m_{τ i}`, with sum `n`. -/
theorem lem_sym_admissible {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (τ : ι → Admissible n) (P : ι → Measure (Fin n → ℝ))
    (hP : ∀ i, IsJointMix (fun j => unifI ((τ i).l j) ((τ i).r j)) (P i))
    (hc : ∀ i, ∀ᵐ x ∂(P i), ∑ j, x j = (n : ℝ)) :
    IsCompleteMix n (mixtureMarginal w τ) (mixture w fun i => permAvg (P i)) ∧
      ∀ᵐ x ∂(mixture w fun i => permAvg (P i)), ∑ j, x j = (n : ℝ) :=
  lem_sym w hw _ P n hP hc

end Lemma3

/-! ### Lemma 1 for admissible tuples, and the complete mix of Lemma 3 -/

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {n : ℕ}

/-- Lemma 1 for an admissible tuple, with the choices of the paper made (a largest length `λ_k`,
an enumeration of the other indices and a minimising `s`): the `U(I_j)` have a joint mix with
sum `n`, the law of the vector `archVec`. -/
theorem exists_lem_arch_admissible {σ : Measure V} (hσ : IsArchimedesMeasure σ) {u w : V}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0) (τ : Admissible n) :
    ∃ P : Measure (Fin n → ℝ), IsJointMix (fun j => unifI (τ.l j) (τ.r j)) P ∧
      ∀ᵐ x ∂P, ∑ j, x j = (n : ℝ) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    obtain ⟨j, -⟩ := τ.pos; exact ⟨j, Finset.mem_univ j⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => τ.r j - τ.l j) hne
  set L := (Finset.univ.erase k).toList
  have hL : L.Nodup := Finset.nodup_toList _
  have hLk : ∀ j, j ∈ L ↔ j ≠ k := fun j => by simp [L]
  let g : ℕ → ℝ := fun s' => |2 * ((L.take s').map fun j => τ.r j - τ.l j).sum -
    ∑ j ∈ Finset.univ.erase k, (τ.r j - τ.l j)|
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (Finset.range (L.length + 1)) g
    ⟨0, by simp⟩
  have hs' : s ≤ L.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  obtain ⟨-, -, Ek, EG, EH, -, -, -, -, hP, hsum⟩ := lem_arch hσ hu hw huw τ.l τ.r τ.le τ.pos
    τ.polygon k (fun j => hk j (Finset.mem_univ j)) L hL hLk s hs'
    (fun s' hs'' => hmin s' (Finset.mem_range.2 (Nat.lt_succ_of_le hs'')))
  refine ⟨_, hP, hsum.mono fun x hx => ?_⟩
  rw [hx, τ.mid]; ring

/-- Lemma 1 and Lemma 3 together: given an Archimedes measure on a real inner product space with
an orthonormal pair (e.g. the uniform distribution on `S² ⊂ ℝ³`), the marginal of every mixture
of admissible tuples is `n`-completely mixable, by a complete mix with sum `n`. -/
theorem completelyMixable_mixtureMarginal {σ : Measure V} (hσ : IsArchimedesMeasure σ) {u w : V}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0) {ι : Type*} [Fintype ι]
    (wt : ι → ℝ≥0∞) (hwt : ∑ i, wt i = 1) (τ : ι → Admissible n) :
    ∃ Q : Measure (Fin n → ℝ), IsCompleteMix n (mixtureMarginal wt τ) Q ∧
      ∀ᵐ x ∂Q, ∑ j, x j = (n : ℝ) := by
  choose P hP hc using fun i => exists_lem_arch_admissible hσ hu hw huw (τ i)
  exact ⟨_, lem_sym_admissible wt hwt τ P hP hc⟩

end Assembly

/-! ### A planar Archimedes measure

The projection of the uniform distribution on `S²` to a plane has the density
`1 / (2π √(1 - |x|²))` on the unit disc. We prove directly that every projection of this measure
to a line through `0` is uniform, so that the hypothesis `IsArchimedesMeasure` is satisfied in
`EuclideanSpace ℝ (Fin 2)`, which is all that Lemma 1 uses. -/

section Planar

open Real Set

lemma hasDerivAt_arcsin_div {c b : ℝ} (hc : 0 < c) (hb : b ∈ Ioo (-c) c) :
    HasDerivAt (fun t => arcsin (t / c)) (1 / √(c ^ 2 - b ^ 2)) b := by
  obtain ⟨h1, h2⟩ := hb
  have hb1 : b / c ≠ -1 := by
    intro h; rw [div_eq_iff hc.ne'] at h; linarith
  have hb2 : b / c ≠ 1 := by
    intro h; rw [div_eq_iff hc.ne'] at h; linarith
  have := (Real.hasDerivAt_arcsin hb1 hb2).comp b ((hasDerivAt_id b).div_const c)
  have hpos : 0 < 1 - (b / c) ^ 2 := by
    rw [sub_pos, div_pow, div_lt_one (by positivity)]; nlinarith
  have hsq : √(c ^ 2 - b ^ 2) = c * √(1 - (b / c) ^ 2) := by
    rw [show c ^ 2 - b ^ 2 = c ^ 2 * (1 - (b / c) ^ 2) by field_simp, Real.sqrt_mul (sq_nonneg c),
      Real.sqrt_sq hc.le]
  convert this using 1
  · rfl
  · rw [hsq]; field_simp

/-- `∫ 1/√(c² - b²) db = π` (the integrand is `0` for `|b| ≥ c` by the conventions of `√` and
division). -/
lemma lintegral_inv_sqrt {c : ℝ} (hc : 0 < c) :
    ∫⁻ b, ENNReal.ofReal (1 / √(c ^ 2 - b ^ 2)) = ENNReal.ofReal π := by
  have hsupp : Function.support (fun b : ℝ => ENNReal.ofReal (1 / √(c ^ 2 - b ^ 2))) ⊆
      Ioc (-c) c := by
    intro b hb
    by_contra h
    apply hb
    have : c ^ 2 - b ^ 2 ≤ 0 := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at h
      rcases h with h | h <;> nlinarith
    simp [Real.sqrt_eq_zero'.2 this]
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have hcont : ContinuousOn (fun t => arcsin (t / c)) (Icc (-c) c) :=
    (continuous_arcsin.comp (continuous_id.div_const c)).continuousOn
  have hderiv : ∀ b ∈ Ioo (-c) c,
      HasDerivAt (fun t => arcsin (t / c)) (1 / √(c ^ 2 - b ^ 2)) b :=
    fun b hb => hasDerivAt_arcsin_div hc hb
  have hnn : ∀ b ∈ Ioo (-c) c, 0 ≤ 1 / √(c ^ 2 - b ^ 2) := fun b _ => by positivity
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnn
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun b => by positivity)]
  rw [← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hderiv
      (by rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)])]
  congr 1
  rw [div_self hc.ne', neg_div, div_self hc.ne', arcsin_one, arcsin_neg, arcsin_one]; ring

/-- The density `1 / (2π √(1 - a² - b²))` of the projection of the uniform distribution on `S²`
to a plane, in coordinates; it is `0` off the open unit disc. -/
def discDens (a b : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * π) * (1 / √(1 - a ^ 2 - b ^ 2)))

lemma measurable_discDens : Measurable (fun p : ℝ × ℝ => discDens p.1 p.2) := by
  unfold discDens; fun_prop

lemma lintegral_discDens (a : ℝ) :
    ∫⁻ b, discDens a b = (Ioo (-1) 1).indicator (fun _ => ENNReal.ofReal (1 / 2)) a := by
  unfold discDens
  by_cases ha : a ∈ Ioo (-1) 1
  · rw [indicator_of_mem ha]
    obtain ⟨h1, h2⟩ := ha
    have hc : 0 < √(1 - a ^ 2) := Real.sqrt_pos.2 (by nlinarith)
    have hc2 : √(1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
    have : ∀ b, ENNReal.ofReal (1 / (2 * π) * (1 / √(1 - a ^ 2 - b ^ 2))) =
        ENNReal.ofReal (1 / (2 * π)) * ENNReal.ofReal (1 / √(√(1 - a ^ 2) ^ 2 - b ^ 2)) := by
      intro b
      rw [hc2, ENNReal.ofReal_mul (by positivity)]
    simp_rw [this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inv_sqrt hc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  · rw [indicator_of_notMem ha]
    have : ∀ b, 1 - a ^ 2 - b ^ 2 ≤ 0 := by
      intro b
      simp only [mem_Ioo, not_and_or, not_lt] at ha
      rcases ha with h | h <;> nlinarith
    simp [Real.sqrt_eq_zero'.2 (this _)]

lemma discDens_eq_norm (x : EuclideanSpace ℝ (Fin 2)) :
    discDens (x 0) (x 1) = ENNReal.ofReal (1 / (2 * π) * (1 / √(1 - ‖x‖ ^ 2))) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, discDens, sub_sub]

/-- The planar Archimedes measure: density `1 / (2π √(1 - ‖x‖²))` on the unit disc of `ℝ²`, the
law of the orthogonal projection of a uniform point of `S²` to a plane (this identification is not
used or formalised). -/
def archPlane : Measure (EuclideanSpace ℝ (Fin 2)) :=
  volume.withDensity fun x => discDens (x 0) (x 1)

/-- The coordinate map `EuclideanSpace ℝ (Fin 2) → ℝ × ℝ`. -/
def coordEquiv : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

lemma coordEquiv_apply (y : EuclideanSpace ℝ (Fin 2)) : coordEquiv y = (y 0, y 1) := rfl

lemma measurePreserving_coordEquiv : MeasurePreserving coordEquiv :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma archPlane_map_inner_unit {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1) :
    archPlane.map (fun x => ⟪u, x⟫_ℝ) = unifI (-1) 1 := by
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin 2) (by simp) (v := fun _ => u) (s := {0}) (by
      refine ⟨fun i => hu, fun i j hij => absurd (Subtype.ext ?_) hij⟩
      rw [i.2, j.2])
  have hb0 : b 0 = u := hb 0 rfl
  set R := b.repr.symm
  have hR : ∀ y, ⟪u, R y⟫_ℝ = y 0 := by
    intro y; rw [← hb0, ← OrthonormalBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  have hRn : ∀ y, discDens (R y 0) (R y 1) = discDens (y 0) (y 1) := by
    intro y; rw [discDens_eq_norm, discDens_eq_norm, LinearIsometryEquiv.norm_map]
  have hφ : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => ⟪u, x⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  ext A hA
  rw [Measure.map_apply hφ hA, archPlane, withDensity_apply _ (hφ hA),
    ← lintegral_indicator (hφ hA),
    ← (LinearIsometryEquiv.measurePreserving R).lintegral_comp_emb
      R.toHomeomorph.measurableEmbedding]
  have hfun : ∀ y, ((fun x : EuclideanSpace ℝ (Fin 2) => ⟪u, x⟫_ℝ) ⁻¹' A).indicator
      (fun x => discDens (x 0) (x 1)) (R y) =
      (Prod.fst ⁻¹' A).indicator (fun p : ℝ × ℝ => discDens p.1 p.2) (coordEquiv y) := by
    intro y
    by_cases h : y 0 ∈ A <;> simp [indicator, hR, coordEquiv_apply, hRn, h]
  simp_rw [hfun]
  rw [measurePreserving_coordEquiv.lintegral_comp_emb coordEquiv.measurableEmbedding,
    Measure.volume_eq_prod, lintegral_prod _
      ((measurable_discDens.indicator (measurable_fst hA)).aemeasurable)]
  have hin : ∀ a, ∫⁻ b, (Prod.fst ⁻¹' A).indicator (fun p : ℝ × ℝ => discDens p.1 p.2) (a, b) =
      A.indicator ((Ioo (-1) 1).indicator fun _ => ENNReal.ofReal (1 / 2)) a := by
    intro a
    by_cases ha : a ∈ A
    · rw [indicator_of_mem ha, ← lintegral_discDens]
      exact lintegral_congr fun b => indicator_of_mem (show (a, b) ∈ Prod.fst ⁻¹' A from ha) _
    · rw [indicator_of_notMem ha]
      exact (lintegral_congr fun b =>
        indicator_of_notMem (show (a, b) ∉ Prod.fst ⁻¹' A from ha) _).trans lintegral_zero
  simp_rw [hin]
  rw [lintegral_indicator hA, lintegral_indicator_const measurableSet_Ioo,
    Measure.restrict_apply measurableSet_Ioo]
  have hae : (Ioo (-1 : ℝ) 1 ∩ A : Set ℝ) =ᵐ[volume] (Icc (-1) 1 ∩ A : Set ℝ) :=
    Ioo_ae_eq_Icc.inter
      (Filter.eventuallyEqSet_iff.2 (Filter.Eventually.of_forall fun _ => Iff.rfl))
  unfold unifI
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by norm_num)), smul_apply, Measure.restrict_apply hA,
    smul_eq_mul, measure_congr hae, inter_comm (Icc _ _)]
  congr 1
  rw [show (1 : ℝ) - -1 = 2 by norm_num, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- Scaling `U[a, b]` by `c > 0` gives `U[c a, c b]`. -/
lemma map_unifI_const_mul {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (unifI a b).map (fun t => c * t) = unifI (c * a) (c * b) := by
  have hf : Measurable (fun t : ℝ => c * t) := measurable_const_mul c
  unfold unifI
  split_ifs with h1 h2 h2
  · rw [Measure.map_smul]
    have hpre : (fun t => c * t) ⁻¹' Icc (c * a) (c * b) = Icc a b := by
      rw [preimage_const_mul_Icc₀ _ _ hc]; congr 1 <;> field_simp
    have hmap : (volume.restrict (Icc a b)).map (fun t => c * t) =
        ENNReal.ofReal c⁻¹ • volume.restrict (Icc (c * a) (c * b)) := by
      rw [← hpre, ← Measure.restrict_map hf measurableSet_Icc, Real.map_volume_mul_left hc.ne',
        abs_of_pos (inv_pos.2 hc), Measure.restrict_smul]
    rw [hmap, smul_smul]
    congr 1
    rw [show c * b - c * a = c * (b - a) by ring, ENNReal.ofReal_mul hc.le,
      ENNReal.mul_inv (Or.inl (by simpa using hc)) (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.ofReal_inv_of_pos hc, mul_comm]
    exact hf.aemeasurable
  · exact absurd (by nlinarith) h2
  · exact absurd (lt_of_mul_lt_mul_left h2 hc.le) h1
  · rw [Measure.map_dirac' hf]

/-- The planar Archimedes measure satisfies the theorem of Archimedes. -/
theorem isArchimedesMeasure_archPlane : IsArchimedesMeasure archPlane := by
  have hunit : ∀ e : EuclideanSpace ℝ (Fin 2), e ≠ 0 →
      archPlane.map (fun x => ⟪e, x⟫_ℝ) = unifI (-‖e‖) ‖e‖ := by
    intro e he
    have hpos : 0 < ‖e‖ := norm_pos_iff.2 he
    set u := ‖e‖⁻¹ • e
    have hu : ‖u‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have heu : (fun x => ⟪e, x⟫_ℝ) = (fun t => ‖e‖ * t) ∘ fun x => ⟪u, x⟫_ℝ := by
      funext x
      simp only [Function.comp, u, real_inner_smul_left]
      field_simp
    have hin : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => ⟪u, x⟫_ℝ) :=
      (continuous_const.inner continuous_id).measurable
    rw [heu, ← Measure.map_map (measurable_const_mul _) hin, archPlane_map_inner_unit hu,
      map_unifI_const_mul hpos, mul_neg_one, mul_one]
  have hprob : IsProbabilityMeasure archPlane := by
    set e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    have h0 : e0 ≠ 0 := by simp [e0]
    have h1 := hunit e0 h0
    have : IsProbabilityMeasure (archPlane.map fun x => ⟪e0, x⟫_ℝ) := by
      rw [h1]; exact unifI_isProb _ _
    have hin : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => ⟪e0, x⟫_ℝ) :=
      (continuous_const.inner continuous_id).measurable
    exact Measure.isProbabilityMeasure_of_map hin.aemeasurable
  refine ⟨hprob, fun e => ?_⟩
  rcases eq_or_ne e 0 with rfl | he
  · simp only [inner_zero_left, norm_zero, neg_zero, Measure.map_const, measure_univ, one_smul]
    unfold unifI
    simp
  · exact hunit e he

end Planar

/-! ### Unconditional forms -/

section Unconditional

lemma orthonormal_single_two :
    ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 ∧
      ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 ∧
      ⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)), EuclideanSpace.single 1 1⟫_ℝ = 0 :=
  ⟨by simp, by simp, by simp [EuclideanSpace.inner_single_left]⟩

/-- Lemma 1 without hypotheses: the `U(I_j)` of an admissible tuple have a joint mix with sum `n`,
the law of the vector of Lemma 1 under the planar Archimedes measure `archPlane`. -/
theorem exists_jointMix_admissible {n : ℕ} (τ : Admissible n) :
    ∃ P : Measure (Fin n → ℝ), IsJointMix (fun j => unifI (τ.l j) (τ.r j)) P ∧
      ∀ᵐ x ∂P, ∑ j, x j = (n : ℝ) :=
  exists_lem_arch_admissible isArchimedesMeasure_archPlane orthonormal_single_two.1
    orthonormal_single_two.2.1 orthonormal_single_two.2.2 τ

/-- Lemmas 1 and 3 without hypotheses: the marginal `∑ w i m_{τ i}` of every finite mixture of
admissible tuples is `n`-completely mixable, by a complete mix with sum `n`. -/
theorem completelyMixable_mixtureMarginal' {n : ℕ} {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞)
    (hw : ∑ i, w i = 1) (τ : ι → Admissible n) :
    ∃ Q : Measure (Fin n → ℝ), IsCompleteMix n (mixtureMarginal w τ) Q ∧
      ∀ᵐ x ∂Q, ∑ j, x j = (n : ℝ) :=
  completelyMixable_mixtureMarginal isArchimedesMeasure_archPlane orthonormal_single_two.1
    orthonormal_single_two.2.1 orthonormal_single_two.2.2 w hw τ

end Unconditional

end Mixes
