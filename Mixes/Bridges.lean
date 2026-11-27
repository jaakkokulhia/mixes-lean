import Mixes.Peel
import Mixes.ScaledB
import Mixes.Theorem27
import Mixes.Ball
import Mixes.Large
import Mixes.Room
import Mixes.SymmCor
import Mixes.ClassK

/-!
# Bridges: committed results with their cited hypotheses discharged

This file removes hypotheses from results proved elsewhere by plugging in theorems that are now
proved.

* Theorem 67 (`o:thm:pconc`): `pconc` without the hypotheses of Theorems 34 and 35
  (`Peel.lean`), via `qcDensity_rpow` (`g ^ p` is strictly quasi-concave) and
  `peelingProps_of_sol`.
* Corollary 64 (`b:cor:monotone`): `cor_monotone_a`, `cor_monotone_b` with Corollary 30
  (`Theorem27.cor30`); `cor_monotone_b_of_scaling` for a base given by `ScalingProperty`.
* Lemma 89 (`st:lem:room`): `room` for `n ≥ d + 2` with the theorem of Minkowski and Radon
  (`Large.asymLE_cent`) in place of the hypothesis `AsymLE`; `asymLE_centroid`.
* Corollary 99 (`st:cor:symm`): `partA`, `ball_core`, `dodecahedron`, `icosahedron`, `cell24`,
  `cell600`, `cell120` with Theorem 51 (`Ball.ball_completelyMixable`).
* Theorem 73 (b) as a scaling property (measurable in `(λ, t)`): `scalingProperty_of_decomp`
  (Theorem 27 for the scaled pieces discharged by `pieceKernel`, measurable in `(λ, U)`),
  `exists_decomp` (Theorem 35 in the form of Theorem 73 (b)), `scalingProperty_of_qc`,
  `scalingProperty_rpow` (constant `p + 2` for a density `g ^ p`, `g` concave), `cor74a`.
* Section 20: `scalingProperty_levLaw` (the level laws `∝ ∏ r_j ^ k_j`, constant `∑ k_j + 2`),
  `scalingProperty_segment` (Theorem 51, `d = 1`, on `ℝ`), and the unconditional `thm75`,
  `cor77`, `thm79`, `thm79_completelyMixable`, `cor80a`, `cor80b`, and `cor74b` (Brunn's theorem
  remains a hypothesis).
* Corollary `j:cor:finite`: `procMix_segMix` (one tuple of pieces: at most `8 · 2^(n-1)`
  segments) and `pieceMix_segMix` (pieces with finitely many atoms: at most
  `(∏ k_j) · 8 · 2^(n-1)` segments).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Bridges

/-! ## Theorem 67 without hypotheses -/

section Pconc

open Peel

/-- A function that is concave on `[0, 1]` is strictly quasi-concave there (`q1`–`q3` of
`Peel.QCDensity`). -/
lemma qc_of_concave {g : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc 0 1) g) :
    (∀ x t y, 0 ≤ x → x ≤ t → t ≤ y → y ≤ 1 → min (g x) (g y) ≤ g t) ∧
    (∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 → g x < g y → g x < g t) ∧
    (∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 → g y < g x → g y < g t) := by
  have key : ∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 →
      (y - t) / (y - x) * g x + (t - x) / (y - x) * g y ≤ g t := by
    intro x t y hx hxt hty hy
    have hyx : 0 < y - x := by linarith
    have := hconc.2 (⟨hx, by linarith⟩ : x ∈ Icc (0:ℝ) 1) (⟨by linarith, hy⟩ : y ∈ Icc (0:ℝ) 1)
      (div_nonneg (by linarith : (0:ℝ) ≤ y - t) hyx.le)
      (div_nonneg (by linarith : (0:ℝ) ≤ t - x) hyx.le)
      (by field_simp; ring)
    simp only [smul_eq_mul] at this
    convert this using 2
    field_simp
    ring
  have hab : ∀ x t y : ℝ, x < y → (y - t) / (y - x) + (t - x) / (y - x) = 1 := by
    intro x t y hxy
    have : y - x ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro x t y hx hxt hty hy
    rcases hxt.lt_or_eq with hxt | rfl
    · rcases hty.lt_or_eq with hty | rfl
      · have := key x t y hx hxt hty hy
        have hyx : 0 < y - x := by linarith
        have e := hab x t y (hxt.trans hty)
        have h1 : 0 ≤ (y - t) / (y - x) := div_nonneg (by linarith) hyx.le
        have h2 : 0 ≤ (t - x) / (y - x) := div_nonneg (by linarith) hyx.le
        have i1 := mul_le_mul_of_nonneg_left (min_le_left (g x) (g y)) h1
        have i2 := mul_le_mul_of_nonneg_left (min_le_right (g x) (g y)) h2
        have e2 : (y - t) / (y - x) * min (g x) (g y) + (t - x) / (y - x) * min (g x) (g y)
            = min (g x) (g y) := by rw [← add_mul, e, one_mul]
        linarith
      · exact min_le_right _ _
    · exact min_le_left _ _
  · intro x t y hx hxt hty hy hlt
    have := key x t y hx hxt hty hy
    have hyx : 0 < y - x := by linarith
    have e := hab x t y (hxt.trans hty)
    have h2 : 0 < (t - x) / (y - x) := div_pos (by linarith) hyx
    have i2 := mul_lt_mul_of_pos_left hlt h2
    have e2 : (y - t) / (y - x) * g x + (t - x) / (y - x) * g x = g x := by
      rw [← add_mul, e, one_mul]
    linarith
  · intro x t y hx hxt hty hy hlt
    have := key x t y hx hxt hty hy
    have hyx : 0 < y - x := by linarith
    have e := hab x t y (hxt.trans hty)
    have h1 : 0 < (y - t) / (y - x) := div_pos (by linarith) hyx
    have i1 := mul_lt_mul_of_pos_left hlt h1
    have e2 : (y - t) / (y - x) * g y + (t - x) / (y - x) * g y = g y := by
      rw [← add_mul, e, one_mul]
    linarith

/-- A probability density `g ^ p` on `[0, 1]` with `g ≥ 0` concave and continuous there and
`p > 0` is strictly quasi-concave, so Theorems 34 and 35 (`Peel.lean`) apply to it. -/
theorem qcDensity_rpow {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (hdens : ∫ x in (0:ℝ)..1, g x ^ p = 1) : QCDensity fun x => g x ^ p := by
  obtain ⟨q1, q2, q3⟩ := qc_of_concave hg
  have hlt : ∀ x y, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 → (g x ^ p < g y ^ p ↔ g x < g y) :=
    fun x y hx hy => Real.rpow_lt_rpow_iff (hg0 x hx) (hg0 y hy) hp
  refine ⟨hgc.rpow_const fun x _ => Or.inr hp.le, fun x hx => Real.rpow_nonneg (hg0 x hx) _,
    hdens, ?_, ?_, ?_⟩
  · intro x t y hx hxt hty hy
    have hxI : x ∈ Icc (0:ℝ) 1 := ⟨hx, by linarith⟩
    have hyI : y ∈ Icc (0:ℝ) 1 := ⟨by linarith, hy⟩
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := q1 x t y hx hxt hty hy
    rcases le_total (g x) (g y) with h' | h'
    · rw [min_eq_left h'] at h
      exact min_le_of_left_le (Real.rpow_le_rpow (hg0 x hxI) h hp.le)
    · rw [min_eq_right h'] at h
      exact min_le_of_right_le (Real.rpow_le_rpow (hg0 y hyI) h hp.le)
  · intro x t y hx hxt hty hy h
    have hxI : x ∈ Icc (0:ℝ) 1 := ⟨hx, by linarith⟩
    have hyI : y ∈ Icc (0:ℝ) 1 := ⟨by linarith, hy⟩
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    exact (hlt x t hxI htI).2 (q2 x t y hx hxt hty hy ((hlt x y hxI hyI).1 h))
  · intro x t y hx hxt hty hy h
    have hxI : x ∈ Icc (0:ℝ) 1 := ⟨hx, by linarith⟩
    have hyI : y ∈ Icc (0:ℝ) 1 := ⟨by linarith, hy⟩
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    exact (hlt y t hyI htI).2 (q3 x t y hx hxt hty hy ((hlt y x hyI hxI).1 h))

/-- The conclusions of Theorem 34 (a), (b) in the form `Bipyramid.PeelingProps` used by
Theorem 67, for a strictly quasi-concave density and a solution `m` of the equation of
Theorem 34. -/
theorem peelingProps_of_sol {f : ℝ → ℝ} (hf : QCDensity f) {m : ℝ → ℝ} (hm : IsSol f m) :
    Bipyramid.PeelingProps f (mean f) (fun U => cutA f (m U) U) (fun U => cutB f (m U) U) := by
  obtain ⟨-, -, hAB, -, -, -, -⟩ := hf.sol_b hm
  intro U hU0 hUμ
  have ha := hf.sol_a hm ⟨hU0, hUμ⟩
  exact ⟨(cutA_mem01 hf.mem01 _ _).1, (hAB U ⟨hU0, hUμ⟩).2.1, (hAB U ⟨hU0, hUμ⟩).2.2.1,
    (cutB_mem01 hf.mem01 _ _).2, ha.2.2.2.2.2.1, ha.2.2.2.2.2.2⟩

/-- **Theorem 67** (`o:thm:pconc`), unconditionally. Let `p ≥ 1` and let `f = g ^ p` be a
probability density on `[0, 1]`, where `g ≥ 0` is concave and continuous on `[0, 1]`. Then `f`
is `n`-completely mixable for every integer `n ≥ p + 2`. (Theorems 34 and 35 are discharged by
`Peel.lean`, Theorem 36 by `ConcaveMix.lean`.) -/
theorem pconc {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (hdens : ∫ x in (0:ℝ)..1, g x ^ p = 1) :
    ∀ n : ℕ, p + 2 ≤ n → CompletelyMixable n (Bipyramid.densityOn01 fun x => g x ^ p) := by
  have hf := qcDensity_rpow (by linarith) hg hgc hg0 hdens
  obtain ⟨m, hm⟩ := hf.exists_unique_sol.1
  obtain ⟨-, -, -, hAc, hBc, -, -⟩ := hf.sol_b hm
  exact ConcaveMix.pconc' hp hg hgc hg0 (mean fun x => g x ^ p) hdens rfl _ _
    (peelingProps_of_sol hf hm) hAc hBc (hf.decomp_sets hm)

end Pconc

/-! ## Corollary 64 with Corollary 30 discharged -/

section Cor64

open Module Homothetic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]
  {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **Corollary 64 (a)** (`b:cor:monotone`), with Corollary 30 proved (`Theorem27.cor30`): the
hypothesis `hC` of `Homothetic.cor_monotone_a` is removed. The scaling property of the base `F`
(`hΦ`, `hmix`) is part of the statement, not a cited result. -/
theorem cor_monotone_a {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s)
    (hrc : ConcaveOn ℝ (Icc α β) r) (hmono : MonotoneOn r (Icc α β) ∨ AntitoneOn r (Icc α β))
    (c₀ c₁ : V) {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    {m : ℝ} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam)))
    (hn : 2 ≤ n)
    (hmean : α + (β - α) / n ≤ ∫ s, s ∂levelDist α β r (finrank ℝ V) ∧
      ∫ s, s ∂levelDist α β r (finrank ℝ V) ≤ β - (β - α) / n)
    (hmax : ∀ s ∈ Icc α β, m * r s ≤ n * chord α β r (∫ s, s ∂levelDist α β r (finrank ℝ V))) :
    CompletelyMixable n (unifSet (body α β r (fun s => c₀ + s • c₁) F)) :=
  Homothetic.cor_monotone_a hαβ hr hr0 hpos hrc hmono c₀ c₁ hF hFi hcen hk hΦ hmix hn hmean
    hmax (Theorem27.cor30 n)

/-- **Corollary 64 (b)** (`b:cor:monotone`), with Corollary 30 proved: `U(K)` is
`n`-completely mixable for every `n ≥ k + 1` (`k = finrank V + 1`), for a concave monotone
profile and a base with the scaling property with constant `m ≤ (k + 1)/2`. -/
theorem cor_monotone_b {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s)
    (hrc : ConcaveOn ℝ (Icc α β) r) (hmono : MonotoneOn r (Icc α β) ∨ AntitoneOn r (Icc α β))
    (c₀ c₁ : V) {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    {m : ℝ} (hm : m ≤ ((finrank ℝ V + 1 : ℕ) + 1 : ℝ) / 2) {ρ : Measure Ω}
    [IsProbabilityMeasure ρ]
    {Φ : (Fin n → ℝ) → Ω → (Fin n → V)} (hΦ : Measurable (Function.uncurry Φ))
    (hmix : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (∀ k, m * lam k ≤ ∑ i, lam i) →
      IsJointMix (fun i => (unifSet F).map (fun y => lam i • y)) (ρ.map (Φ lam)))
    (hn : finrank ℝ V + 1 + 1 ≤ n) :
    CompletelyMixable n (unifSet (body α β r (fun s => c₀ + s • c₁) F)) :=
  Homothetic.cor_monotone_b hαβ hr hr0 hpos hrc hmono c₀ c₁ hF hFi hcen hk hm hΦ hmix hn
    (Theorem27.cor30 n)

/-- **Corollary 64 (b)** for a base with the scaling property in the form `ScalingProperty`
(e.g. a ball, `Ball.ball_scalingProperty`): the joint mixes of the base are those of the
scaling property with all translations `0`. -/
theorem cor_monotone_b_of_scaling {α β : ℝ} (hαβ : α < β) {r : ℝ → ℝ} (hr : Continuous r)
    (hr0 : ∀ s ∈ Icc α β, 0 ≤ r s) (hpos : ∀ s ∈ Ioo α β, 0 < r s)
    (hrc : ConcaveOn ℝ (Icc α β) r) (hmono : MonotoneOn r (Icc α β) ∨ AntitoneOn r (Icc α β))
    (c₀ c₁ : V) {F : Set V} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) (hk : 1 ≤ finrank ℝ V)
    {m : ℝ} (hm : m ≤ ((finrank ℝ V + 1 : ℕ) + 1 : ℝ) / 2) (hsc : ScalingProperty (unifSet F) m)
    (hn : finrank ℝ V + 1 + 1 ≤ n) :
    CompletelyMixable n (unifSet (body α β r (fun s => c₀ + s • c₁) F)) := by
  obtain ⟨Φ, hΦ, hmix⟩ := hsc n (by omega)
  refine cor_monotone_b hαβ hr hr0 hpos hrc hmono c₀ c₁ hF hFi hcen hk hm
    (ρ := unifSeq) (Φ := fun lam ω => Φ (lam, 0) ω) ?_ (fun lam hlam hne hk => ?_) hn
  · exact hΦ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  · have := hmix lam 0 hlam hne hk
    simpa using this

end Cor64

/-! ## Lemma 89 with the theorem of Minkowski and Radon discharged -/

section Room

open Module Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The theorem of Minkowski and Radon (`Large.asymLE_cent`) in the form `Room.AsymLE` used by
Lemma 89, about the centroid `Room.centroid K` (the mean of `U(K)`). -/
theorem asymLE_centroid {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hpos : 0 < volume K) : Room.AsymLE K (Room.centroid K) (finrank ℝ E) := by
  have e : Room.centroid K = Large.cent K := (Large.cent_eq_integral_unifSet K).symm
  rw [e]
  exact Large.asymLE_cent hKc hKconv hpos

/-- `as(K) < n - 1` for `n ≥ d + 2` (`Room.asym_lt_of_dim`), with the hypothesis
`as(K) ≤ d` (Minkowski–Radon) proved. -/
theorem asym_lt_of_dim {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hpos : 0 < volume K) {n : ℕ} (hn : finrank ℝ E + 2 ≤ n) :
    Room.AsymLE K (Room.centroid K) (finrank ℝ E) ∧ (finrank ℝ E : ℝ) < n - 1 :=
  Room.asym_lt_of_dim (asymLE_centroid hKc hKconv hpos) hn

/-- **Lemma 89** (`st:lem:room`, room for partners) for `n ≥ d + 2`, `d = dim E ≥ 1`, without
the Minkowski–Radon hypothesis: let `K` be a compact convex set of positive volume containing
the ball `c + sB` about its centroid `c`. There are `ρ₀ > 0` and `α > 0` such that for
`0 < ρ ≤ ρ₀` and every `p ∈ K + ρ₀B`, the point `c - (p - c)/(n - 1)` lies in the interior of
`K_{2ρ}`, and the set of `(x₂, …, x_{n-1})` with all `xᵢ ∈ K_{2ρ}` and
`nc - p - x₂ - ⋯ - x_{n-1} ∈ K_{2ρ}` has measure at least `α` (any Haar measure `μ`). -/
theorem room {n : ℕ} (hd : 0 < finrank ℝ E) (hn : finrank ℝ E + 2 ≤ n) {K : Set E}
    (hKc : IsCompact K) (hKconv : Convex ℝ K) (hpos : 0 < volume K) {s : ℝ} (hs : 0 < s)
    (hball : closedBall (Room.centroid K) s ⊆ K) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ ρ₀ > 0, ∃ α : ENNReal, 0 < α ∧ ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ p : E,
      (∃ x ∈ K, dist p x ≤ ρ₀) →
      Room.centroid K - ((n : ℝ) - 1)⁻¹ • (p - Room.centroid K) ∈
        interior (Room.innerBody K (2 * ρ)) ∧
      α ≤ Measure.pi (fun _ : Fin (n - 2) => μ)
        {y | (∀ i, y i ∈ Room.innerBody K (2 * ρ)) ∧
          (n : ℝ) • Room.centroid K - p - ∑ i, y i ∈ Room.innerBody K (2 * ρ)} := by
  obtain ⟨hasym, hlt⟩ := asym_lt_of_dim hKc hKconv hpos hn
  exact Room.room (by omega) hKconv hKc.isClosed hs hball (by exact_mod_cast hd) hlt hasym μ

end Room

/-! ## Corollary 99 with Theorem 51 discharged -/

section SymmCor

open Metric SymmCor

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- **Corollary 99 (a)** in `ℝ^d` with Theorem 51 proved (`Ball.ball_completelyMixable`); the
hypothesis `hJB` (John's ellipsoid with Ball's volume-ratio theorem) remains. -/
theorem partA {d : ℕ} {K : Set (E d)} {c : E d} (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (hconv : Convex ℝ K) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hJB : ∃ (e : E d) (T : (E d) →ₗ[ℝ] (E d)), LinearMap.det T ≠ 0 ∧ ell e T ⊆ K ∧
      (volume K).toReal ≤ 2 ^ d / (volume (closedBall (0 : E d) 1)).toReal *
        (volume (ell e T)).toReal) :
    (∀ n : ℕ, Even n → n ≠ 0 → CompletelyMixable n (unifSet K)) ∧
      (∀ n : ℕ, Odd n → 3 * 2 ^ d / (volume (closedBall (0 : E d) 1)).toReal ≤ n →
        CompletelyMixable n (unifSet K)) :=
  SymmCor.partA hK hKfin hconv hKs hJB (Ball.ball_completelyMixable d (by norm_num))

/-- **The ball as the core** (Corollary 99 (c)), with Theorem 51 proved. -/
theorem ball_core {d : ℕ} {K : Set (E d)} {c : E d} {r : ℝ} (hr : 0 < r) (hK : MeasurableSet K)
    (hKfin : volume K ≠ ∞) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c r ⊆ K)
    (hvol : (volume K).toReal ≤ 5 / 3 * (volume (closedBall c r)).toReal) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.ball_core hr hK hKfin hKs hBK hvol (Ball.ball_completelyMixable d (by norm_num))

/-- **Corollary 99 (c), dodecahedron**, with Theorem 51 proved (its classical volume and
inradius remain hypotheses). -/
theorem dodecahedron {K : Set (E 3)} {c : E 3} {a : ℝ} (ha : 0 < a) (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c (a * √(250 + 110 * √5) / 20) ⊆ K)
    (hvolK : volume K = ENNReal.ofReal ((15 + 7 * √5) * a ^ 3 / 4)) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.dodecahedron ha hK hKs hBK hvolK (Ball.ball_completelyMixable 3 (by norm_num))

/-- **Corollary 99 (c), icosahedron**, with Theorem 51 proved. -/
theorem icosahedron {K : Set (E 3)} {c : E 3} {a : ℝ} (ha : 0 < a) (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c (a * (3 * √3 + √15) / 12) ⊆ K)
    (hvolK : volume K = ENNReal.ofReal (5 * (3 + √5) * a ^ 3 / 12)) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.icosahedron ha hK hKs hBK hvolK (Ball.ball_completelyMixable 3 (by norm_num))

/-- **Corollary 99 (c), `24`-cell**, with Theorem 51 proved. -/
theorem cell24 {K : Set (E 4)} {c : E 4} (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K) (hBK : closedBall c 1 ⊆ K)
    (hvolK : volume K = 8) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.cell24 hK hKs hBK hvolK (Ball.ball_completelyMixable 4 (by norm_num))

/-- **Corollary 99 (c), `600`-cell**, with Theorem 51 proved. -/
theorem cell600 {K : Set (E 4)} {c : E 4} (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c √((7 + 3 * √5) / 16) ⊆ K) (hKB : K ⊆ closedBall c 1) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.cell600 hK hKs hBK hKB (Ball.ball_completelyMixable 4 (by norm_num))

/-- **Corollary 99 (c), `120`-cell**, with Theorem 51 proved. -/
theorem cell120 {K : Set (E 4)} {c : E 4} (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c 1 ⊆ K) (hKB : K ⊆ closedBall c (1 / √((7 + 3 * √5) / 16))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.cell120 hK hKs hBK hKB (Ball.ball_completelyMixable 4 (by norm_num))

end SymmCor

/-! ## Theorem 73 (b) as a scaling property

`Theorem27.thm73b_of_thm27` gives, for each fixed `λ`, a kernel of Theorem 27 for the scaled
pieces. For the scaling property the joint mix must be a Borel function of `(λ, t)` and of a
sequence of independent uniform variables; the kernel below is measurable in `(λ, U)`. -/

section Scaling73

open ProbabilityTheory Scaled Theorem27 Bipyramid

variable {n : ℕ}

/-- The joint mix of Theorem 27 for the scaled pieces `λ_i P_{β(U)}`, as a function of `(λ, U)`
(the construction `procMix` of `Theorem27.lean`). -/
def pieceKer (n : ℕ) (β : ℝ → ℝ) (p : (Fin n → ℝ) × ℝ) : Measure (Fin n → ℝ) :=
  procMix (fun j => p.1 j * 1) (fun j => p.1 j * (pieceAB (β p.2)).1)
    (fun j => p.1 j * (pieceAB (β p.2)).2)

lemma measurable_pieceKer {β : ℝ → ℝ} (hβ : Measurable β) : Measurable (pieceKer n β) :=
  measurable_procMix (fun j => ((measurable_pi_apply j).comp measurable_fst).mul_const _)
    (fun j => ((measurable_pi_apply j).comp measurable_fst).mul
      (measurable_fst.comp (measurable_pieceAB.comp (hβ.comp measurable_snd))))
    (fun j => ((measurable_pi_apply j).comp measurable_fst).mul
      (measurable_snd.comp (measurable_pieceAB.comp (hβ.comp measurable_snd))))

open Classical in
/-- `pieceKer` where it is a probability measure, `δ₀` elsewhere. -/
def pieceKerM (n : ℕ) (β : ℝ → ℝ) (p : (Fin n → ℝ) × ℝ) : Measure (Fin n → ℝ) :=
  if pieceKer n β p univ = 1 then pieceKer n β p else Measure.dirac 0

lemma measurable_pieceKerM {β : ℝ → ℝ} (hβ : Measurable β) : Measurable (pieceKerM n β) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_pieceKer hβ)) measurable_const) (measurable_pieceKer hβ) measurable_const

/-- The Markov kernel `(λ, U) ↦ pieceKerM`. -/
def pieceKernel (n : ℕ) {β : ℝ → ℝ} (hβ : Measurable β) : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ) :=
  ⟨pieceKerM n β, measurable_pieceKerM hβ⟩

instance {β : ℝ → ℝ} (hβ : Measurable β) : IsMarkovKernel (pieceKernel n hβ) := ⟨fun p => by
  change IsProbabilityMeasure (pieceKerM n β p)
  unfold pieceKerM
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance⟩

/-- Theorem 27 for the scaled pieces: where `β(U) λ_i ≤ ∑ λ_j` (and `λ ≥ 0`, `∑ λ > 0`),
`pieceKernel` is a joint mix of the `λ_i P_{β(U)}` with sum `∑ λ_j`. -/
theorem pieceKernel_spec {β : ℝ → ℝ} (hβ : Measurable β) (hβ2 : ∀ U, 2 ≤ β U)
    {lam : Fin n → ℝ} (hlam : ∀ i, 0 ≤ lam i) (hpos : 0 < ∑ j, lam j) {U : ℝ}
    (hU : ∀ i, β U * lam i ≤ ∑ j, lam j) :
    IsJointMix (fun i => scaledPiece (β U) (lam i)) (pieceKernel n hβ (lam, U)) ∧
      ∀ᵐ v ∂(pieceKernel n hβ (lam, U)), ∑ i, v i = ∑ i, lam i := by
  have hspec := procMix_spec (μ := fun j => lam j * 1) (a := fun j => lam j * (pieceAB (β U)).1)
    (b := fun j => lam j * (pieceAB (β U)).2)
    (fun j => isPiece_scale (isPiece_pieceAB (hβ2 U)).1 (hlam j))
    (fun j => by simpa using hlam j)
    (fun j => by
      simp only [mul_one]
      nlinarith [hU j, mul_le_mul_of_nonneg_left (isPiece_pieceAB (hβ2 U)).2 (hlam j)])
    (by simpa using hpos)
  have h1 : pieceKer n β (lam, U) univ = 1 := hspec.1.1.measure_univ
  have hκU : pieceKernel n hβ (lam, U) = pieceKer n β (lam, U) := by
    change pieceKerM n β (lam, U) = _
    simp only [pieceKerM, h1, ↓reduceIte]
  have e : pieceKer n β (lam, U) = procMix (fun j => lam j * 1)
      (fun j => lam j * (pieceAB (β U)).1) (fun j => lam j * (pieceAB (β U)).2) := rfl
  rw [hκU, e]
  refine ⟨?_, hspec.2.mono fun x hx => by rw [hx]; simp⟩
  convert hspec.1 using 1
  funext i
  rw [scaledPiece_eq_piece (hβ2 U) (hlam i)]

lemma measurable_scaledTuple' {Y : Type*} [MeasurableSpace Y] {t lam v : Y → Fin n → ℝ}
    {l r : Y → ℝ} (μ : ℝ) (ht : Measurable t) (hlam : Measurable lam) (hv : Measurable v)
    (hl : Measurable l) (hr : Measurable r) :
    Measurable fun y => scaledTuple (t y) (lam y) μ (l y) (r y) (v y) := by
  classical
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [scaledTuple]
  have hti : Measurable fun y => t y i := (measurable_pi_apply i).comp ht
  have hli : Measurable fun y => lam y i := (measurable_pi_apply i).comp hlam
  have hvi : Measurable fun y => v y i := (measurable_pi_apply i).comp hv
  exact Measurable.ite (measurableSet_le hl hr) (by fun_prop) (by fun_prop)

/-- The construction of Theorem 73 (b) as a function of `(λ, t)`: draw the level `U ∼ ω`, the
joint mix `V` of the scaled pieces, and map it to the tuple `scaledTuple`. -/
def mix73 (ω : Measure ℝ) (μ : ℝ) (l r : ℝ → ℝ) {β : ℝ → ℝ} (hβ : Measurable β)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ω.bind fun U => (pieceKernel n hβ (x.1, U)).map (scaledTuple x.2 x.1 μ (l U) (r U))

lemma measurable_mix73 (ω : Measure ℝ) [SFinite ω] (μ : ℝ) {l r β : ℝ → ℝ} (hl : Measurable l)
    (hr : Measurable r) (hβ : Measurable β) : Measurable (mix73 (n := n) ω μ l r hβ) := by
  let κ' : Kernel (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) (Fin n → ℝ) :=
    (pieceKernel n hβ).comap (fun q => (q.1.1, q.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  let Ψ : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × (Fin n → ℝ) → Fin n → ℝ := fun z =>
    scaledTuple z.1.1.2 z.1.1.1 μ (l z.1.2) (r z.1.2) z.2
  have hΨ : Measurable Ψ :=
    measurable_scaledTuple' μ (measurable_snd.comp (measurable_fst.comp measurable_fst))
      (measurable_fst.comp (measurable_fst.comp measurable_fst)) measurable_snd
      (hl.comp (measurable_snd.comp measurable_fst)) (hr.comp (measurable_snd.comp measurable_fst))
  let G : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ → Measure (Fin n → ℝ) := fun q =>
    (pieceKernel n hβ (q.1.1, q.2)).map (scaledTuple q.1.2 q.1.1 μ (l q.2) (r q.2))
  have hK : ∀ s, MeasurableSet s → Measurable fun q => G q s := by
    intro s hs
    have e : ∀ q, G q s = κ' q (Prod.mk q ⁻¹' (Ψ ⁻¹' s)) := by
      intro q
      have hm : Measurable (scaledTuple q.1.2 q.1.1 μ (l q.2) (r q.2)) :=
        hΨ.comp (measurable_prodMk_left (x := q))
      exact Measure.map_apply hm hs
    simp only [e]
    exact Kernel.measurable_kernel_prodMk_left (hΨ hs)
  have hKm : Measurable G := Measure.measurable_of_measurable_coe _ hK
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have e : ∀ x, mix73 ω μ l r hβ x s = ∫⁻ U, G (x, U) s ∂ω := by
    intro x
    have hm2 : Measurable fun U => G (x, U) := hKm.comp (measurable_prodMk_left (x := x))
    exact Measure.bind_apply hs hm2.aemeasurable
  simp only [e]
  exact (hK s hs).lintegral_prod_right'

/-- **Theorem 73 (b)** (`g:thm:scaled`) as a scaling property. Let `F` be decomposed as in
Theorem 35, `F = ∫ (P_{β(U)} mapped by y ↦ pieceMap μ ℓ(U) r(U) y) dω(U)` (`hdecomp`), with
measurable `ℓ`, `r`, `β ≥ 2`, and `β ≤ c` `ω`-almost everywhere. Then `F` has the scaling
property with constant `c`: Theorem 27 for the scaled pieces (`pieceKernel_spec`) is
discharged, and the joint mix is a Borel function of `(λ, t)` and of independent uniform
variables. -/
theorem scalingProperty_of_decomp (F ω : Measure ℝ) [IsProbabilityMeasure ω] (μ : ℝ)
    {l r β : ℝ → ℝ} (hl : Measurable l) (hr : Measurable r) (hβm : Measurable β)
    (hβ2 : ∀ U, 2 ≤ β U)
    (hdecomp : ∀ A, MeasurableSet A →
      F A = ∫⁻ U, (pieceP (β U)).map (pieceMap μ (l U) (r U)) A ∂ω)
    {c : ℝ} (hβc : ∀ᵐ U ∂ω, β U ≤ c) : ScalingProperty F c := by
  intro n _
  obtain ⟨Ψ, hΨ, hrep⟩ := exists_unif_rep (n := n) (mix73 ω μ l r hβm)
    (measurable_mix73 ω μ hl hr hβm)
  refine ⟨Ψ, hΨ, fun lam t hlam hne hk => ?_⟩
  have hpos : 0 < ∑ j, lam j := by
    obtain ⟨i, hi⟩ := hne
    exact lt_of_lt_of_le ((hlam i).lt_of_ne (Ne.symm hi))
      (Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i))
  set κl : Kernel ℝ (Fin n → ℝ) := (pieceKernel n hβm).comap (fun U => (lam, U))
    measurable_prodMk_left
  have hT : ∀ U, (∀ i, β U * lam i ≤ ∑ j, lam j) →
      IsJointMix (fun i => scaledPiece (β U) (lam i)) (κl U) ∧
        ∀ᵐ v ∂(κl U), ∑ i, v i = ∑ i, lam i :=
    fun U hU => pieceKernel_spec hβm hβ2 hlam hpos hU
  have hβ : ∀ᵐ U ∂ω, ∀ i, β U * lam i ≤ ∑ j, lam j := by
    filter_upwards [hβc] with U hU i
    exact (mul_le_mul_of_nonneg_right hU (hlam i)).trans (hk i)
  have h := (thm73b F ω μ hl hr hdecomp t lam κl hT hβ).1
  have e : mix73 ω μ l r hβm (lam, t) =
      ω.bind fun U => (κl U).map (scaledTuple t lam μ (l U) (r U)) := rfl
  rw [hrep _ (e ▸ h.1), e]
  simpa only [smul_eq_mul] using h

end Scaling73

/-! ## Theorems 34, 35 and 73 (b): the scaling property of a quasi-concave density -/

section QCScaling

open ProbabilityTheory Scaled Bipyramid ConcaveMix Peel

/-- The decomposition of Theorem 35 in the form `hdecomp` of Theorem 73 (b): from peeling ends
`A < μ < B` on `[0, f(μ))`, continuous there, with `∫_0^{f(μ)} π_U dU = f` (`H35`), the level law
`ω = W(U) dU` and measurable `ℓ = μ - A`, `r = B - μ`, `β ≥ 2` with
`f = ∫ (P_β(U) mapped by pieceMap μ ℓ(U) r(U)) dω(U)`, `β(U) = beta μ (A U) (B U)` for
`ω`-almost every `U`, which lies in `[0, f(μ))`. (Extracted from the proof of
`ConcaveMix.thm36`.) -/
theorem exists_decomp {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ}
    (hAB : ∀ U ∈ Ico 0 (f μ), A U < μ ∧ μ < B U)
    (hAc : ContinuousOn A (Ico 0 (f μ))) (hBc : ContinuousOn B (Ico 0 (f μ)))
    (H35 : ∀ S, MeasurableSet S →
      ∫⁻ U in Ico 0 (f μ), piU μ (A U) (B U) S = densityOn01 f S)
    (hf : IsProbabilityMeasure (densityOn01 f)) :
    ∃ ω : Measure ℝ, IsProbabilityMeasure ω ∧ ∃ l r β : ℝ → ℝ, Measurable l ∧ Measurable r ∧
      Measurable β ∧ (∀ U, 2 ≤ β U) ∧
      (∀ S, MeasurableSet S →
        densityOn01 f S = ∫⁻ U, (pieceP (β U)).map (pieceMap μ (l U) (r U)) S ∂ω) ∧
      ∀ᵐ U ∂ω, U ∈ Ico 0 (f μ) ∧ β U = beta μ (A U) (B U) := by
  classical
  set I := Ico 0 (f μ) with hI
  set A' := Aext f μ A
  set B' := Bext f μ B
  have hA' : Measurable A' :=
    ContinuousOn.measurable_piecewise hAc continuousOn_const measurableSet_Ico
  have hB' : Measurable B' :=
    ContinuousOn.measurable_piecewise hBc continuousOn_const measurableSet_Ico
  have hAeq : ∀ U ∈ I, A' U = A U := fun U hU => Set.piecewise_eq_of_mem _ _ _ hU
  have hBeq : ∀ U ∈ I, B' U = B U := fun U hU => Set.piecewise_eq_of_mem _ _ _ hU
  have hAB' : ∀ U, A' U < μ ∧ μ < B' U := by
    intro U
    by_cases hU : U ∈ I
    · rw [hAeq U hU, hBeq U hU]; exact hAB U hU
    · have e1 : A' U = μ - 1 := by simp only [A', Aext]; exact Set.piecewise_eq_of_notMem _ _ _ hU
      have e2 : B' U = μ + 1 := by simp only [B', Bext]; exact Set.piecewise_eq_of_notMem _ _ _ hU
      rw [e1, e2]; constructor <;> linarith
  set β' := fun U => beta μ (A' U) (B' U) with hβ'def
  have hβm : Measurable β' := by
    simp only [hβ'def, Bipyramid.beta]
    exact ((measurable_const.sub hA').add (hB'.sub measurable_const)).div
      ((measurable_const.sub hA').min (hB'.sub measurable_const))
  have hβ2 : ∀ U, 2 ≤ β' U := fun U => two_le_beta (hAB' U).1 (hAB' U).2
  set ω := levelLaw f μ A B with hωdef
  have hWm : Measurable fun U => ENNReal.ofReal (Wf μ (A' U) (B' U)) := by
    unfold Wf
    exact (((measurable_const.sub hA').add (hB'.sub measurable_const)).pow_const 2 |>.div
      (measurable_const.mul ((measurable_const.sub hA').min (hB'.sub measurable_const)))
      ).ennreal_ofReal
  have hpi : ∀ U ∈ I, ∀ S, piU μ (A U) (B U) S = ENNReal.ofReal (Wf μ (A' U) (B' U)) *
      (pieceP (β' U)).map (pieceMap μ (μ - A' U) (B' U - μ)) S := by
    intro U hU S
    simp only [hβ'def]
    rw [hAeq U hU, hBeq U hU, piU_eq (hAB U hU).1 (hAB U hU).2]
    rfl
  have hint : ∀ S, MeasurableSet S →
      ∫⁻ U, (pieceP (β' U)).map (pieceMap μ (μ - A' U) (B' U - μ)) S ∂ω = densityOn01 f S := by
    intro S hS
    rw [hωdef, levelLaw, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hWm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← H35 S hS]
    exact setLIntegral_congr_fun measurableSet_Ico fun U hU => (hpi U hU S).symm
  have hωprob : IsProbabilityMeasure ω := by
    constructor
    have h1 := hint univ MeasurableSet.univ
    rw [measure_univ] at h1
    have h2 : ∀ U, (pieceP (β' U)).map (pieceMap μ (μ - A' U) (B' U - μ)) univ = 1 := by
      intro U
      rw [Measure.map_apply (by unfold pieceMap; split_ifs <;> fun_prop) MeasurableSet.univ,
        preimage_univ]
      exact (pieceP_isProb (hβ2 U)).measure_univ
    simpa [h2] using h1
  refine ⟨ω, hωprob, fun U => μ - A' U, fun U => B' U - μ, β', measurable_const.sub hA',
    hB'.sub measurable_const, hβm, hβ2, fun S hS => (hint S hS).symm, ?_⟩
  have hac : ω ≪ volume.restrict I := withDensity_absolutelyContinuous _ _
  refine hac ((ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ fun U hU => ⟨hU, ?_⟩))
  simp only [hβ'def, hAeq U hU, hBeq U hU]

/-- **Theorem 73 (b)** for a strictly quasi-concave density, as a scaling property, with
Theorems 27, 34 and 35 proved: if `f` is a strictly quasi-concave probability density on
`[0, 1]` (`Peel.QCDensity`) and `β(U) ≤ c` at every level of the peeling (for the ends given by
some solution `m` of the equation of Theorem 34), then the law with density `f` has the
scaling property with constant `c`. -/
theorem scalingProperty_of_qc {f : ℝ → ℝ} (hf : QCDensity f) {m : ℝ → ℝ} (hm : IsSol f m)
    {c : ℝ} (hβ : ∀ U ∈ Ico 0 (f (mean f)),
      beta (mean f) (cutA f (m U) U) (cutB f (m U) U) ≤ c) :
    ScalingProperty (densityOn01 f) c := by
  obtain ⟨-, -, hAB, hAc, hBc, -, -⟩ := hf.sol_b hm
  have hfp : IsProbabilityMeasure (densityOn01 f) :=
    isProb_densityOn01 hf.cont hf.nonneg hf.int_one
  obtain ⟨ω, hω, l, r, β, hl, hr, hβm, hβ2, hdec, hae⟩ := exists_decomp
    (fun U hU => ⟨(hAB U hU).2.1, (hAB U hU).2.2.1⟩) hAc hBc (hf.decomp_sets hm) hfp
  refine scalingProperty_of_decomp _ ω (mean f) hl hr hβm hβ2 hdec ?_
  filter_upwards [hae] with U hU
  rw [hU.2]
  exact hβ U hU.1

/-- **Theorem 73 (b) with Theorem 67**: for `p ≥ 1` and a probability density `g ^ p` on
`[0, 1]` with `g ≥ 0` concave and continuous on `[0, 1]`, the law has the scaling property with
constant `p + 2`. No hypothesis on the peeling or on Theorem 27 remains. -/
theorem scalingProperty_rpow {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (hdens : ∫ x in (0:ℝ)..1, g x ^ p = 1) :
    ScalingProperty (densityOn01 fun x => g x ^ p) (p + 2) := by
  have hf := qcDensity_rpow (by linarith) hg hgc hg0 hdens
  obtain ⟨m, hm⟩ := hf.exists_unique_sol.1
  refine scalingProperty_of_qc hf hm fun U hU => ?_
  obtain ⟨hA0, hAμ, hμB, hB1, hfU, hmean⟩ := peelingProps_of_sol hf hm U hU.1 hU.2
  have sub : Icc (cutA _ (m U) U) (cutB _ (m U) U) ⊆ Icc 0 1 := Icc_subset_Icc hA0 hB1
  have hμI : mean (fun x => g x ^ p) ∈ Ioo (cutA _ (m U) U) (cutB _ (m U) U) := ⟨hAμ, hμB⟩
  obtain ⟨h1, h2⟩ := beta_le hp hU.1 (hg.subset sub (convex_Icc _ _)) (hgc.mono sub)
    (fun x hx => hg0 x (sub hx)) hfU hμI hU.2 hmean
  exact beta_le_of (by linarith) hμI h1 h2

/-- **Corollary 74 (a)** (`g:cor:scaled`), sufficiency, unconditionally: for `p ≥ 1`, `X` with
density `g ^ p` on `[0, 1]` (`g ≥ 0` concave, continuous), `λ_i ≥ 0` not all zero with
`(p + 2) max λ_i ≤ ∑ λ_i` and any `t_i`, the laws of `t_i + λ_i X` are jointly mixable. (For
`λ = 0` the laws are point masses, jointly mixable trivially; the scaling property excludes it.) -/
theorem cor74a {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Icc 0 1) g) (hgc : ContinuousOn g (Icc 0 1))
    (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (hdens : ∫ x in (0:ℝ)..1, g x ^ p = 1)
    (t lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (hcond : ∀ k, (p + 2) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => (densityOn01 fun x => g x ^ p).map (fun x => t i + lam i * x) := by
  obtain ⟨Φ, -, hmix⟩ := scalingProperty_rpow hp hg hgc hg0 hdens n hn
  exact ⟨_, by simpa only [smul_eq_mul] using hmix lam t hlam hne hcond⟩

end QCScaling

/-! ## The level laws of Section 20 -/

section LevelLaw

open ScaledB Bipyramid Peel

/-- The level law `levLaw ρ` (density `ρ / ∫_0^1 ρ` on `[0, 1]`) as `densityOn01`. -/
lemma levLaw_eq_densityOn01 {ρ : ℝ → ℝ} (h0 : levNorm ρ ≠ 0) (htop : levNorm ρ ≠ ∞) :
    levLaw ρ = densityOn01 fun s => ρ s / (levNorm ρ).toReal := by
  have hZ : 0 < (levNorm ρ).toReal := ENNReal.toReal_pos h0 htop
  ext S hS
  simp only [levLaw, densityOn01, smul_apply, withDensity_apply _ hS, smul_eq_mul]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 h0)]
  refine lintegral_congr fun s => ?_
  rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.2 hZ.le), ENNReal.ofReal_inv_of_pos hZ,
    ENNReal.ofReal_toReal htop, mul_comm]

/-- `levNorm ρ = ∫_0^1 ρ` for `ρ ≥ 0` continuous on `[0, 1]`. -/
lemma levNorm_toReal {ρ : ℝ → ℝ} (hρc : ContinuousOn ρ (Icc 0 1))
    (hρ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ ρ s) : (levNorm ρ).toReal = ∫ s in (0:ℝ)..1, ρ s := by
  rw [levNorm, ← ofReal_integral_eq_lintegral_ofReal (hρc.integrableOn_compact isCompact_Icc)
    (ae_restrict_of_forall_mem measurableSet_Icc hρ0), ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Icc hρ0), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]

variable {J : ℕ}

/-- The normalised level density `∏_j r_j ^ k_j / Z` is the `p`-th power (`p = ∑ k_j ≥ 1`) of the
function `Z^{-1/p} ∏_j r_j ^ (k_j / p)`, which is concave (`Scaled.concaveOn_prod_rpow`),
continuous and nonnegative on `[0, 1]`. -/
lemma prodDens_root (k : Fin J → ℕ) (hk : 1 ≤ ∑ j, k j) {r : Fin J → ℝ → ℝ}
    (hr : ∀ j, ContinuousOn (r j) (Icc 0 1)) (hrc : ∀ j, ConcaveOn ℝ (Icc 0 1) (r j))
    (hr0 : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r j s) {Z : ℝ} (hZ : 0 < Z) :
    ∃ g : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) g ∧ ContinuousOn g (Icc 0 1) ∧
      (∀ s ∈ Icc (0:ℝ) 1, 0 ≤ g s) ∧
      ∀ s ∈ Icc (0:ℝ) 1, g s ^ (∑ j, (k j : ℝ)) = prodDens r k s / Z := by
  set p : ℝ := ∑ j, (k j : ℝ) with hpdef
  have hp1 : 1 ≤ p := by rw [hpdef]; exact_mod_cast hk
  have hp0 : 0 < p := by linarith
  set g : ℝ → ℝ := fun s => Z ^ (-1 / p) * ∏ j, r j s ^ ((k j : ℝ) / p) with hgdef
  have hw1 : ∑ j, (k j : ℝ) / p = 1 := by rw [← Finset.sum_div, ← hpdef, div_self hp0.ne']
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · have := Scaled.concaveOn_prod_rpow (convex_Icc 0 1) Finset.univ (fun j => (k j : ℝ) / p)
      (fun j _ => div_nonneg (Nat.cast_nonneg _) hp0.le) hw1 r (fun j _ => hrc j)
      (fun j _ s hs => hr0 j s hs)
    exact this.smul (Real.rpow_nonneg hZ.le _)
  · have : ContinuousOn (fun s => ∏ j, r j s ^ ((k j : ℝ) / p)) (Icc 0 1) :=
      continuousOn_finsetProd Finset.univ fun j _ =>
        (hr j).rpow_const fun x _ => Or.inr (div_nonneg (Nat.cast_nonneg _) hp0.le)
    exact continuousOn_const.mul this
  · exact fun s hs => mul_nonneg (Real.rpow_nonneg hZ.le _)
      (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hr0 j s hs) _)
  · intro s hs
    rw [hgdef, Real.mul_rpow (Real.rpow_nonneg hZ.le _)
      (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hr0 j s hs) _),
      ← Real.rpow_mul hZ.le, div_mul_cancel₀ _ hp0.ne',
      ← Real.finsetProd_rpow _ _ fun j _ => Real.rpow_nonneg (hr0 j s hs) _]
    rw [Finset.prod_congr rfl fun j _ => by
      rw [← Real.rpow_mul (hr0 j s hs), div_mul_cancel₀ _ hp0.ne', Real.rpow_natCast]]
    rw [Real.rpow_neg_one, prodDens, div_eq_mul_inv, mul_comm]

/-- **Theorem 73 (b) for the level laws of Theorem 75**, with Theorems 27, 34, 35 and the bound
of Theorem 67 proved: let `r_j ≥ 0` be continuous and concave on `[0, 1]`, `k_j` natural numbers
with `p = ∑ k_j ≥ 1`, and `∫_0^1 ∏ r_j ^ k_j > 0`. Then the level law with density proportional
to `∏_j r_j ^ k_j` has the scaling property with constant `p + 2`. -/
theorem scalingProperty_levLaw (k : Fin J → ℕ) (hk : 1 ≤ ∑ j, k j) {r : Fin J → ℝ → ℝ}
    (hr : ∀ j, Continuous (r j)) (hrc : ∀ j, ConcaveOn ℝ (Icc 0 1) (r j))
    (hr0 : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r j s) (hpos : levNorm (prodDens r k) ≠ 0) :
    ScalingProperty (levLaw (prodDens r k)) ((∑ j, (k j : ℝ)) + 2) := by
  have hρ : Continuous (prodDens r k) := continuous_finsetProd _ fun j _ => (hr j).pow _
  have htop := (levNorm_lt_top hρ).ne
  have hρ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ prodDens r k s := fun s hs =>
    Finset.prod_nonneg fun j _ => pow_nonneg (hr0 j s hs) _
  set Z := (levNorm (prodDens r k)).toReal with hZdef
  have hZ : 0 < Z := ENNReal.toReal_pos hpos htop
  obtain ⟨g, hg, hgc, hg0, hgp⟩ := prodDens_root k hk (fun j => (hr j).continuousOn) hrc hr0 hZ
  have hp1 : (1:ℝ) ≤ ∑ j, (k j : ℝ) := by exact_mod_cast hk
  have hdens : ∫ x in (0:ℝ)..1, g x ^ (∑ j, (k j : ℝ)) = 1 := by
    rw [intervalIntegral.integral_congr (g := fun s => prodDens r k s / Z) fun s hs => by
      rw [uIcc_of_le zero_le_one] at hs; exact hgp s hs, intervalIntegral.integral_div,
      hZdef, levNorm_toReal hρ.continuousOn hρ0, div_self]
    rw [← levNorm_toReal hρ.continuousOn hρ0]; exact hZ.ne'
  have e : levLaw (prodDens r k) = densityOn01 fun x => g x ^ (∑ j, (k j : ℝ)) := by
    rw [levLaw_eq_densityOn01 hpos htop, ← hZdef, densityOn01, densityOn01]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [hgp s hs]
  rw [e]
  exact Bridges.scalingProperty_rpow hp1 hg hgc hg0 hdens

/-- The hypothesis `Hlev` of `ScaledB.thm79` and `hlev` of `ScaledB.cor77` for the affine
profiles `r_j(s) = (1 - s) a_j + s b_j`, whenever `∑ k_j ≥ 1`. -/
theorem scalingProperty_levLaw_prof [NeZero J] (k : Fin J → ℕ) (hk : 1 ≤ ∑ j, k j) (a b : Fin J → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j) :
    ScalingProperty (levLaw (prodDens (Scaled.prof a b) k)) ((∑ j, (k j : ℝ)) + 2) := by
  have hr : ∀ j, Continuous (Scaled.prof a b j) := fun j => by unfold Scaled.prof; fun_prop
  refine scalingProperty_levLaw k hk hr (ScaledB.concaveOn_prof a b)
    (fun j s hs => Scaled.prof_nonneg ha hb j hs) ?_
  have hρ : Continuous (prodDens (Scaled.prof a b) k) :=
    continuous_finsetProd _ fun j _ => (hr j).pow _
  exact (levNorm_pos hρ fun s hs => Finset.prod_pos fun j _ =>
    pow_pos (Scaled.prof_pos ha hb hab j hs) _).ne'

end LevelLaw

/-! ## Section 20 without cited hypotheses -/

section ScaledBUncond

open Module ScaledB Bipyramid

/-- **Theorem 51 for the segment** (`d = 1`): `U[-1, 1]` has the scaling property with constant
`2` (the hypothesis `Hseg` of `ScaledB.cor80b`), from `ClassK.thm51Ball` transported to `ℝ`. -/
theorem scalingProperty_segment : ScalingProperty (unifSet (Icc (-1:ℝ) 1)) 2 := by
  have h := ClassK.transport (MeasurableEquiv.funUnique (Fin 1) ℝ)
    (volume_preserving_funUnique (Fin 1) ℝ) ⟨fun x y => rfl, fun c x => rfl⟩
    (ClassK.good_eBall 1) (ClassK.thm51Ball 1 le_rfl)
  have himg : (MeasurableEquiv.funUnique (Fin 1) ℝ) '' ClassK.eBall 1 = Icc (-1) 1 := by
    rw [MeasurableEquiv.image_eq_preimage_symm]
    ext y
    simp only [ClassK.eBall, mem_preimage, mem_ofPred_eq, Fin.sum_univ_one, mem_Icc]
    change (fun _ : Fin 1 => y) 0 ^ 2 ≤ 1 ↔ _
    simp only
    constructor
    · intro hy; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; nlinarith
  rw [himg] at h
  exact (scalingPropertySet_iff (by simp) (by simp) 2).1 h.2

section Thm75

variable {J : ℕ} [NeZero J] {V : Fin J → Type*} [∀ j, NormedAddCommGroup (V j)]
  [∀ j, NormedSpace ℝ (V j)] [∀ j, FiniteDimensional ℝ (V j)] [∀ j, MeasureSpace (V j)]
  [∀ j, BorelSpace (V j)] [∀ j, (volume : Measure (V j)).IsAddHaarMeasure]

/-- **Theorem 75** (`g:thm:prod`) without the hypothesis `hlev`: Theorem 73 (b) for the level law
is proved (`scalingProperty_levLaw`), with `β* ≤ ∑ k_j + 2` from Theorem 67. Hence the
condition `β* ≤ m_K` of `ScaledB.thm75` becomes `∑_j dim V_j + 2 ≤ m_K`; the case
`∑ dim V_j = 0` (all `F_j` points) is excluded. -/
theorem thm75 {F : (j : Fin J) → Set (V j)} (hF : ∀ j, IsCompact (F j))
    (hFi : ∀ j, (interior (F j)).Nonempty) (hcen : ∀ j, ∫ y, y ∂(unifSet (F j)) = 0)
    {m : Fin J → ℝ} (hm0 : ∀ j, 0 ≤ m j) (hmF : ∀ j, ScalingProperty (unifSet (F j)) (m j))
    {r : Fin J → ℝ → ℝ} (hr : ∀ j, Continuous (r j)) (hrc : ∀ j, ConcaveOn ℝ (Icc 0 1) (r j))
    (hr0 : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r j s) (hrpos : ∀ j, ∀ s ∈ Ioo (0:ℝ) 1, 0 < r j s)
    (c₀ c₁ : (j : Fin J) → V j) (hk : 1 ≤ ∑ j, finrank ℝ (V j)) {mK sbar : ℝ}
    (hsbar : sbar = ∫ s, s ∂(levLaw (prodDens r fun j => finrank ℝ (V j))))
    (hβ : (∑ j, (finrank ℝ (V j) : ℝ)) + 2 ≤ mK) {M : Fin J → ℝ}
    (hM : ∀ j, ∀ s ∈ Icc (0:ℝ) 1, r j s ≤ M j)
    (hl : ∀ j, 0 ≤ (1 - sbar) * r j 0 + sbar * r j 1)
    (hmK : ∀ j, m j * M j ≤ mK * ((1 - sbar) * r j 0 + sbar * r j 1)) :
    ScalingProperty (unifSet (bodyL (diagMap r) (fun s => c₀ + s • c₁) (univ.pi F))) mK := by
  have hρ : Continuous (prodDens r fun j => finrank ℝ (V j)) :=
    continuous_finsetProd _ fun j _ => (hr j).pow _
  have hpos : levNorm (prodDens r fun j => finrank ℝ (V j)) ≠ 0 :=
    (levNorm_pos hρ fun s hs => Finset.prod_pos fun j _ => pow_pos (hrpos j s hs) _).ne'
  exact ScaledB.thm75 hF hFi hcen hm0 hmF hr hrc hr0 hrpos c₀ c₁
    (scalingProperty_levLaw _ hk hr hrc hr0 hpos) hsbar hβ hM hl hmK

/-- **Corollary 77** (`g:cor:cayley`) without the hypothesis `hlev` (Theorem 73 (b) for the
level law, now proved), for `∑_j dim V_j ≥ 1`: the hull `conv((C₀ × {0}) ∪ (C₁ × {1}))` has
the scaling property with constant `d + 1`, `d = 1 + ∑ dim V_j`. -/
theorem cor77 {F : (j : Fin J) → Set (V j)} (hF : ∀ j, IsCompact (F j))
    (hFc : ∀ j, Convex ℝ (F j)) (hFi : ∀ j, (interior (F j)).Nonempty) {m : Fin J → ℝ}
    (hm0 : ∀ j, 0 ≤ m j) (hmk : ∀ j, m j ≤ finrank ℝ (V j) + 1)
    (hmF : ∀ j, ScalingProperty (unifSet (F j)) (m j)) {a b : Fin J → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j) (t : (j : Fin J) → V j)
    (hk : 1 ≤ ∑ j, finrank ℝ (V j)) :
    ScalingProperty (unifSet (hullC F a b t)) ((∑ j, (finrank ℝ (V j) : ℝ)) + 2) :=
  ScaledB.cor77 hF hFc hFi hm0 hmk hmF ha hb hab t
    (scalingProperty_levLaw_prof _ hk a b ha hb hab)

end Thm75

/-- **Theorem 79** (`g:thm:class`), unconditionally: every member of `𝒦⁺` of dimension `d` has
the scaling property with constant `d + 1` (and its uniform distribution is a probability
measure). The hypotheses `Hball` (Theorem 51, `Ball.ball_scalingProperty`) and `Hlev`
(Theorem 73 (b) with Theorem 67 for the level laws of the hulls, `scalingProperty_levLaw_prof`)
of `ScaledB.thm79` are discharged. -/
theorem thm79 {X : Sp} {μ : Measure X.carrier} {d : ℕ} (h : KPlus X μ d) :
    IsProbabilityMeasure μ ∧ ScalingProperty μ (d + 1) := by
  induction h with
  | point X => exact ⟨inferInstance, by simpa using scalingProperty_dirac X.carrier⟩
  | ball j hj =>
    refine ⟨isProbabilityMeasure_unifSet (Metric.measure_closedBall_pos _ _ one_pos).ne'
      (isCompact_closedBall _ _).measure_lt_top.ne,
      scalingProperty_mono (Ball.ball_scalingProperty j) ?_⟩
    have : (1:ℝ) ≤ j := by exact_mod_cast hj
    linarith
  | affine h M hM b ih =>
    obtain ⟨hP, hS⟩ := ih
    exact ⟨inferInstance, scalingProperty_map_affine hS M b⟩
  | @prod X Y μ ν d₁ d₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨hP₁, hS₁⟩ := ih₁
    obtain ⟨hP₂, hS₂⟩ := ih₂
    refine ⟨inferInstance, scalingProperty_mono (scalingProperty_prod hS₁ hS₂) ?_⟩
    push_cast
    exact max_le (by linarith [(Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂)])
      (by linarith [(Nat.cast_nonneg d₁ : (0:ℝ) ≤ d₁)])
  | @hull J _ X F hF hFc hFi hK hk a b ha hb hab t ih =>
    obtain ⟨h0, ht⟩ := volume_hullC hF hFc hFi ha hb hab t
    refine ⟨unifSet_isProb h0 ht, ?_⟩
    have hk1 : 1 ≤ ∑ j, finrank ℝ (X j).carrier :=
      (hk 0).trans (Finset.single_le_sum (f := fun j => finrank ℝ (X j).carrier)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin J)))
    have key := cor77 hF hFc hFi (m := fun j => (finrank ℝ (X j).carrier : ℝ) + 1)
      (fun j => by positivity) (fun j => le_rfl) (fun j => (ih j).2) ha hb hab t hk1
    convert key using 1
    push_cast
    ring

/-- **Theorem 79**, complete mixability, unconditionally: a member of `𝒦⁺` of dimension `d` has
an `n`-completely mixable uniform distribution for every `n ≥ max(2, d + 1)`. -/
theorem thm79_completelyMixable {X : Sp} {μ : Measure X.carrier} {d : ℕ} (h : KPlus X μ d)
    {n : ℕ} (hn : 2 ≤ n) (hdn : d + 1 ≤ n) : CompletelyMixable n μ :=
  completelyMixable_of_scalingProperty (thm79 h).2 hn (by exact_mod_cast hdn)

section Cor80

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

/-- **Corollary 80 (a)** (`g:cor:more`) without the hypothesis `hlev` (now proved), for
`dim W ≥ 1` (`d ≥ 2`): `K` has the scaling property with constant `d + 1`. -/
theorem cor80a {F : Set W} (hF : IsCompact F) (hFi : (interior F).Nonempty)
    (hcen : ∫ y, y ∂(unifSet F) = 0) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ (((finrank ℝ W + 1 : ℕ) : ℝ) + 1) / 2) (hmF : ScalingProperty (unifSet F) m)
    {r : ℝ → ℝ} (hr : Continuous r) (hrc : ConcaveOn ℝ (Icc 0 1) r)
    (hanti : AntitoneOn r (Icc 0 1)) (hr0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r s)
    (hrpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < r s) (c₀ c₁ : Fin 1 → W) (hW : 1 ≤ finrank ℝ W) :
    ScalingProperty (unifSet (bodyL (diagMap (V := fun _ : Fin 1 => W) fun _ => r)
      (fun s => c₀ + s • c₁) (univ.pi fun _ => F))) (((finrank ℝ W + 1 : ℕ) : ℝ) + 1) := by
  have hρ : Continuous (prodDens (fun _ : Fin 1 => r) fun _ => finrank ℝ W) :=
    continuous_finsetProd _ fun j _ => hr.pow _
  have hpos : levNorm (prodDens (fun _ : Fin 1 => r) fun _ => finrank ℝ W) ≠ 0 :=
    (levNorm_pos hρ fun s hs => Finset.prod_pos fun j _ => pow_pos (hrpos s hs) _).ne'
  have h := scalingProperty_levLaw (fun _ : Fin 1 => finrank ℝ W) (by simpa using hW)
    (fun _ => hr) (fun _ => hrc) (fun _ => hr0) hpos
  refine ScaledB.cor80a hF hFi hcen hm0 hm hmF hr hrc hanti hr0 hrpos c₀ c₁ ?_
  convert h using 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  push_cast
  ring

/-- **Corollary 80 (b)** (`g:cor:more`), unconditionally (Theorem 51 for the segment and
Theorem 73 (b) for the level law proved): for the planar body
`K = {(s, c(s) + r(s) y) : 0 ≤ s ≤ 1, -1 ≤ y ≤ 1}` with `r ≥ 0` continuous and concave, `> 0` on
`(0, 1)`, `c` affine and `ℓ(s̄) > 0`, `K` has the scaling property with constant
`max(3, 2 max r / ℓ(s̄))`, and `U(K)` is `n`-completely mixable for every such `n`. -/
theorem cor80b {r : ℝ → ℝ} (hr : Continuous r) (hrc : ConcaveOn ℝ (Icc 0 1) r)
    (hr0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ r s) (hrpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < r s)
    (c₀ c₁ : Fin 1 → ℝ) {M : ℝ} (hM : ∀ s ∈ Icc (0:ℝ) 1, r s ≤ M)
    (hl : 0 < (1 - ∫ s, s ∂levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)) * r 0 +
      (∫ s, s ∂levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)) * r 1) :
    let sbar := ∫ s, s ∂levLaw (prodDens (fun _ : Fin 1 => r) fun _ => 1)
    let K := bodyL (diagMap (V := fun _ : Fin 1 => ℝ) fun _ => r) (fun s => c₀ + s • c₁)
      (univ.pi fun _ => Icc (-1:ℝ) 1)
    ScalingProperty (unifSet K) (max 3 (2 * M / ((1 - sbar) * r 0 + sbar * r 1))) ∧
      ∀ n : ℕ, max 3 (2 * M / ((1 - sbar) * r 0 + sbar * r 1)) ≤ n →
        CompletelyMixable n (unifSet K) := by
  have hρ : Continuous (prodDens (fun _ : Fin 1 => r) fun _ => 1) :=
    continuous_finsetProd _ fun j _ => hr.pow _
  have hpos : levNorm (prodDens (fun _ : Fin 1 => r) fun _ => 1) ≠ 0 :=
    (levNorm_pos hρ fun s hs => Finset.prod_pos fun j _ => pow_pos (hrpos s hs) _).ne'
  have h := scalingProperty_levLaw (fun _ : Fin 1 => 1) (by simp)
    (fun _ => hr) (fun _ => hrc) (fun _ => hr0) hpos
  refine ScaledB.cor80b hr hrc hr0 hrpos c₀ c₁ scalingProperty_segment ?_ hM hl
  convert h using 1
  norm_num

end Cor80

/-- **Corollary 74 (b)** (`g:cor:scaled`) with only Brunn's theorem as a hypothesis: the
peeling (Theorems 34, 35) and Theorem 27 are discharged. `hBrunn`: the law of `u(X)`,
`X ∼ U(K)`, is the image under `y ↦ a + c y` (`c > 0`) of the law with density `g ^ (d - 1)` on
`[0, 1]`, `g ≥ 0` concave and continuous. Then for `λ ≥ 0`, not all zero, with
`(d + 1) max λ_i ≤ ∑ λ_i`, the laws of `u(X_i)`, `X_i ∼ U(t_i + λ_i K)`, are jointly mixable.
(Brunn's theorem, that the projection of a convex body has such a density, is not in Mathlib
and stays a hypothesis.) -/
theorem cor74b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [BorelSpace E] (K : Set E) (d : ℕ) (hd : 2 ≤ d) (u : E →L[ℝ] ℝ) {a c : ℝ} (hc : 0 < c)
    {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g) (hgc : ContinuousOn g (Icc 0 1))
    (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (hdens : ∫ x in (0:ℝ)..1, g x ^ ((d : ℝ) - 1) = 1)
    (hBrunn : (unifSet K).map u =
      (densityOn01 fun x => g x ^ ((d : ℝ) - 1)).map (fun y => a + c * y))
    {n : ℕ} (hn : 2 ≤ n) (t : Fin n → E) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hne : ∃ i, lam i ≠ 0) (hcond : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => ((unifSet K).map (fun x => t i + lam i • x)).map u := by
  have hp : (1:ℝ) ≤ (d : ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨i0, hi0⟩ := hne
  have hJ := cor74a hn hp hg hgc hg0 hdens (fun i => u (t i) + lam i * a) (fun i => c * lam i)
    (fun i => mul_nonneg hc.le (hlam i)) ⟨i0, mul_ne_zero hc.ne' hi0⟩ (fun k => by
      rw [← Finset.mul_sum]
      have := hcond k
      nlinarith)
  convert hJ using 2 with i
  rw [Measure.map_map u.measurable (by fun_prop)]
  have e : (u ∘ fun x => t i + lam i • x) = (fun z => u (t i) + lam i * z) ∘ u := by
    funext x; simp [map_add, map_smul]
  rw [e, ← Measure.map_map (by fun_prop) u.measurable, hBrunn,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y
  simp only [Function.comp]
  ring

end ScaledBUncond

/-! ## Corollary `j:cor:finite`: finite mixtures of segments -/

section Finite

open Theorem27 JointLemmas
open scoped NNReal

variable {n : ℕ}

lemma list_sum_map_eq {α M : Type*} [AddCommMonoid M] (L : List α) (f : α → M) :
    (L.map f).sum = ∑ i : Fin L.length, f (L.get i) := by
  conv_lhs => rw [← List.ofFn_get L]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- **Corollary `j:cor:finite`, one tuple of pieces**: for pieces `(a_j, b_j)` of the means
`μ_j`, the joint mix `procMix μ a b` of `Theorem27.lean` is a mixture of at most
`8 · 2^(n-1)` uniform distributions on segments: `N ≤ 2^(n-1)` outputs of the procedure of
Lemma 23, each with a leaf of `8` segments (`leafD`). Under the hypotheses of
`procMix_spec` the weights are nonnegative and add up to `1`. -/
theorem procMix_segMix {μ a b : Fin n → ℝ} (hp : ∀ j, IsPiece (μ j) (a j) (b j)) :
    ∃ N : ℕ, N ≤ 2 ^ (n - 1) ∧ ∃ w : Fin N × Fin 8 → ℝ, ∃ P Q : Fin N × Fin 8 → Fin n → ℝ,
      procMix μ a b = segMix w P Q ∧
      ((∀ j, 0 ≤ μ j) → (∀ j, b j ≤ ∑ j, μ j) → 0 < ∑ j, μ j →
        (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1) := by
  classical
  obtain ⟨hlen, hout, hsum1, -, -⟩ := split_lemma hp
  set L := proc a b n (fun j => 2 * μ j) 1 with hL
  refine ⟨L.length, hlen, fun ie => (L.get ie.1).2 * (leafD a b (L.get ie.1).1).1 ie.2,
    fun ie => (leafD a b (L.get ie.1).1).2.1 ie.2,
    fun ie => (leafD a b (L.get ie.1).1).2.2 ie.2, ?_, ?_⟩
  · rw [procMix, ← hL, list_sum_map_eq, segMix, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [leafM, SegD.mix, segMix, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [smul_smul, ← ENNReal.ofReal_mul (hout _ (List.get_mem L i)).1.le]
  · intro hμ hbs hs
    have ha : ∀ j, 0 ≤ a j := fun j => by
      rcases hp j with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · rw [h]; linarith [hμ j]
    have hg : ∀ i : Fin L.length, Good ((∑ j, (L.get i).1 j) / 2)
        (fun j => phi (a j) (b j) ((L.get i).1 j)) (leafD a b (L.get i).1) := by
      intro i
      obtain ⟨-, hsum, hbox, hone⟩ := hout _ (List.get_mem L i)
      have e : (∑ j, (L.get i).1 j) / 2 = ∑ j, μ j := by rw [hsum]; ring
      exact good_leafD hbox hone ha (fun j => e ▸ hbs j) (e ▸ hs)
    refine ⟨fun ie => mul_nonneg (hout _ (List.get_mem L ie.1)).1.le ((hg ie.1).1 ie.2), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, (hg _).2.1, mul_one]
    rw [← list_sum_map_eq L Prod.snd] at *
    exact hsum1

/-- The product of finitely supported measures: `∏_j ∑_i c_{ji} δ_{x_{ji}}` is
`∑_σ (∏_j c_{jσ(j)}) δ_{(x_{jσ(j)})_j}`. -/
lemma pi_finite_atoms {k : Fin n → ℕ} {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (c : (j : Fin n) → Fin (k j) → ℝ≥0)
    (x : (j : Fin n) → Fin (k j) → α) :
    Measure.pi (fun j => ∑ i, c j i • Measure.dirac (x j i)) =
      ∑ σ : (j : Fin n) → Fin (k j), (∏ j, c j (σ j)) • Measure.dirac fun j => x j (σ j) := by
  classical
  have hfin : ∀ j, IsFiniteMeasure (∑ i, c j i • Measure.dirac (x j i)) := fun j => by
    constructor
    simp only [sum_apply, Measure.coe_nnreal_smul_apply, measure_univ, mul_one]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.coe_lt_top
  refine Measure.pi_eq fun S hS => ?_
  have hm : MeasurableSet (univ.pi S) := MeasurableSet.univ_pi hS
  simp only [sum_apply, Measure.coe_nnreal_smul_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ (hS _)]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  push_cast
  rw [Finset.prod_mul_distrib]
  congr 1
  by_cases h : ∀ j, x j (σ j) ∈ S j
  · rw [indicator_of_mem (show (fun j => x j (σ j)) ∈ univ.pi S from fun j _ => h j)]
    simp [indicator_of_mem (h _)]
  · push Not at h
    obtain ⟨j0, hj0⟩ := h
    rw [indicator_of_notMem (show (fun j => x j (σ j)) ∉ univ.pi S from
      fun hh => hj0 (hh j0 (mem_univ _)))]
    rw [Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [indicator_of_notMem hj0])]

/-- **Corollary `j:cor:finite`** (`mixes/main.tex`), for the construction `pieceMix` of
`Theorem27.lean`: if the law `pd j` of the piece of coordinate `j` has `k_j` atoms and no other
mass, `pd j = ∑_i c_{ji} δ_{x_{ji}}`, all of them pieces for the mean `μ_j`, then the joint mix
`pieceMix μ pd` is a mixture of at most `(∏_j k_j) · 8 · 2^(n-1)` uniform distributions on
segments. (The paper counts atoms of the slab measure `π_j`, `k_j` atoms giving at most
`⌊k_j²/4⌋ + 1` pieces by Lemma 20; that step is inside the existence proof `exists_pieces`
and is not restated here.) -/
theorem pieceMix_segMix {μ : Fin n → ℝ} {k : Fin n → ℕ} (c : (j : Fin n) → Fin (k j) → ℝ≥0)
    (x : (j : Fin n) → Fin (k j) → ℝ × ℝ) (hx : ∀ j i, IsPiece (μ j) (x j i).1 (x j i).2) :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι ≤ (∏ j, k j) * (8 * 2 ^ (n - 1)) ∧
      ∃ w : ι → ℝ, ∃ P Q : ι → Fin n → ℝ,
        pieceMix μ (fun j => ∑ i, c j i • Measure.dirac (x j i)) = segMix w P Q ∧
        ((∀ j, 0 ≤ μ j) → (∀ j i, (x j i).2 ≤ ∑ j, μ j) → 0 < ∑ j, μ j → ∀ e, 0 ≤ w e) := by
  classical
  set T := (j : Fin n) → Fin (k j)
  have hF := measurable_procMix_pieces (n := n) μ
  have h := fun σ : T => procMix_segMix (μ := μ) (a := fun j => (x j (σ j)).1)
    (b := fun j => (x j (σ j)).2) fun j => hx j (σ j)
  choose N hN w P Q hPQ hw using h
  refine ⟨Σ σ : T, Fin (N σ) × Fin 8, inferInstance, ?_, fun e => (∏ j, (c j (e.1 j) : ℝ)) *
    w e.1 e.2, fun e => P e.1 e.2, fun e => Q e.1 e.2, ?_, fun hμ hb hs e =>
      mul_nonneg (Finset.prod_nonneg fun j _ => (c j (e.1 j)).2)
        ((hw e.1 hμ (fun j => hb j (e.1 j)) hs).1 e.2)⟩
  · rw [Fintype.card_sigma]
    calc ∑ σ : T, Fintype.card (Fin (N σ) × Fin 8) ≤ ∑ _σ : T, 2 ^ (n - 1) * 8 :=
          Finset.sum_le_sum fun σ _ => by
            simp only [Fintype.card_prod, Fintype.card_fin]
            exact Nat.mul_le_mul_right 8 (hN σ)
      _ = (∏ j, k j) * (8 * 2 ^ (n - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
          simp only [Fintype.card_fin, smul_eq_mul]
          ring
  · ext s hs
    rw [pieceMix, pi_finite_atoms, Measure.bind_apply hs hF.aemeasurable,
      lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure]
    rw [segMix, sum_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lintegral_dirac' _ (show Measurable fun a : Fin n → ℝ × ℝ =>
      procMix μ (fun j => (a j).1) (fun j => (a j).2) s from (Measure.measurable_coe hs).comp hF)]
    rw [hPQ σ, segMix, sum_apply, ENNReal.smul_def, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [smul_apply, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [← NNReal.coe_prod, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

end Finite

end Mixes.Bridges
