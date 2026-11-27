import Mixes.SlabsMix
import Mixes.Scaled
import Mixes.Bipyramid

/-!
# Complete mixes for concave and unimodal densities (Theorem 36, Corollary 39)

Section 14 of the paper (`c:sec:mix`).

## Construction

* `Kpiece n β`: the explicit `n`-complete mix of `P_β` of Proposition 32 and Lemmas 1 and 3,
  `w K1(τ₁) + (1 - w) K1(τ₂)`, with the tuples and weights of `pieces_mixture` and the kernel
  `SlabsMix.K1` of Lemmas 1 and 3. It is a measurable function of `β` (`measurable_Kpiece`), and
  `Kpiece_spec` says that it is a complete mix of `P_β` with sum `n` for `2 ≤ β ≤ n`.
* `piU μ a b`: the piece `π_U` of Theorem 35 with `A(U) = a`, `B(U) = b`, and `piU_eq`: the
  algebraic part of Theorem 35, `π_U = W(U) · (image of P_β(U) under the affine map)`.
* `mixQ n f μ A B`: the complete mix of Theorem 36, the mixture over `U ∼ W(U) dU` on
  `[0, f(μ))` of the images of `Kpiece n β(U)` under the affine map.

## Main results

* `thm36`: **Theorem 36**, with Theorem 34 (b) and Theorem 35 (`c:eq:decomp`) as hypotheses.
* `H36_of`: Theorem 36 in the form of the hypothesis `H36` of `Bipyramid.pconc` (Theorem 67), and
  `pconc'`: Theorem 67 with `H36` discharged (Theorems 34 and 35 remain hypotheses).
* `cor39`: **Corollary 39**, with Theorem 34 (a), (b) and Theorem 35 as hypotheses.

## Differences from the paper

* Theorems 34 and 35 are hypotheses (they are formalised elsewhere). Only what is used is
  assumed: from Theorem 34 (b), `A(U) < μ < B(U)` and the continuity of `A`, `B` on
  `[0, f(μ))` (for measurability); from Theorem 35, equation `(c:eq:decomp)` for indicators of
  measurable sets (equivalent to bounded measurable `φ`). The algebraic part of Theorem 35
  (`π_U = W(U) ·` image of `P_β(U)`) is proved here (`piU_eq`), and that `W` is a probability
  density is derived from `(c:eq:decomp)`.
* The properties of `f` (continuity, strict unimodality, mean `μ`) enter Theorem 36 only through
  these hypotheses; `thm36` itself only assumes that `f` is a probability density on `[0, 1]`.
* `A`, `B` are total functions; outside `[0, f(μ))` they are replaced by `μ ∓ 1` (`Aext`, `Bext`),
  which does not affect the construction. `Kp` is `Kpiece` guarded by `2 ≤ β ≤ n` (a point mass
  otherwise), so that it is a Markov kernel; the guard always holds on the support.
* The complete mix of `P_β` uses the kernel `SlabsMix.K1` (Lemma 1 with the planar Archimedes
  measure `archPlane` and the first admissible partition of a fixed enumeration; the uniform
  permutation of Lemma 3 as a finite average).
* Corollary 39: `f` is assumed concave and continuous on `[0, 1]` (the paper extends a density
  concave on `(0, 1)` by its limits); `β ≤ 3` is obtained from `Bipyramid.beta_le` with `p = 1`
  (the case `p = 1` of the argument of Theorem 67, which is Lemma 38). The transfer to other
  bounded intervals by an affine map is not restated (see `SlabsMix.isCompleteMix_affine`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Mixes

namespace ConcaveMix

open SlabsMix Scaled

/-! ### The complete mix of `P_β`, measurably in `β` -/

section Kpiece

variable {n : ℕ}

/-- Left ends of `τ'` of Proposition 32 (i), as a function of `β`. -/
def lI1 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - 1 - kI n β) (kI n β) 1 (0, 0) (0, β) (0, uI n β) (0, 0) j).1
/-- Right ends of `τ'` of Proposition 32 (i). -/
def rI1 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - 1 - kI n β) (kI n β) 1 (0, 0) (0, β) (0, uI n β) (0, 0) j).2
/-- Left ends of `τ''` of Proposition 32 (i). -/
def lI2 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - kI n β) (kI n β - 1) 1 (0, 0) (0, β) (uI n β, β) (0, 0) j).1
/-- Right ends of `τ''` of Proposition 32 (i). -/
def rI2 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - kI n β) (kI n β - 1) 1 (0, 0) (0, β) (uI n β, β) (0, 0) j).2
/-- Left ends of `ρ'` of Proposition 32 (ii). -/
def lII1 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - 2) 2 0 (0, 0) (n - β, β) (0, 0) (0, 0) j).1
/-- Right ends of `ρ'` of Proposition 32 (ii). -/
def rII1 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - 2) 2 0 (0, 0) (n - β, β) (0, 0) (0, 0) j).2
/-- Left ends of `ρ''` of Proposition 32 (ii). -/
def lII2 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - 3) 1 1 (0, 0) (0, β) (0, n - β) (n - β, β) j).1
/-- Right ends of `ρ''` of Proposition 32 (ii). -/
def rII2 (n : ℕ) (β : ℝ) : Fin n → ℝ := fun j =>
  (blk (n - 3) 1 1 (0, 0) (0, β) (0, n - β) (n - β, β) j).2

/-- The case distinction of Proposition 32: case (i) is `n ≥ 4` and `β ≤ 2n/3`. -/
def caseI (n : ℕ) (β : ℝ) : Prop := 4 ≤ n ∧ β ≤ 2 * n / 3

instance (n : ℕ) (β : ℝ) : Decidable (caseI n β) := by unfold caseI; infer_instance

/-- **Proposition 32 with Lemmas 1 and 3, explicitly**: the `n`-complete mix of `P_β` that mixes
the outputs `K1` of Lemmas 1 and 3 for the two tuples of Proposition 32. -/
def Kpiece (n : ℕ) (β : ℝ) : Measure (Fin n → ℝ) :=
  if caseI n β then
    ENNReal.ofReal (uI n β / β) • K1 n (lI1 n β, rI1 n β) +
      ENNReal.ofReal (1 - uI n β / β) • K1 n (lI2 n β, rI2 n β)
  else
    ENNReal.ofReal (1 - 2 * (n - β) / β) • K1 n (lII1 n β, rII1 n β) +
      ENNReal.ofReal (2 * (n - β) / β) • K1 n (lII2 n β, rII2 n β)

lemma measurable_kI (n : ℕ) : Measurable (kI n) := by
  have : kI n = (fun k : ℕ => min (n - 1) k) ∘ (fun β : ℝ => ⌊2 * (n : ℝ) / β⌋₊) := rfl
  rw [this]
  exact measurable_from_nat.comp (Measurable.nat_floor (by fun_prop))

lemma measurable_blk (a b c j : ℕ) {A B C D : ℝ → ℝ × ℝ} (hA : Measurable A)
    (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) :
    Measurable fun β => blk a b c (A β) (B β) (C β) (D β) j := by
  unfold blk
  by_cases h1 : j < a
  · simpa [h1] using hA
  by_cases h2 : j < a + b
  · simpa [h1, h2] using hB
  by_cases h3 : j < a + b + c
  · simpa [h1, h2, h3] using hC
  · simpa [h1, h2, h3] using hD

/-- A function of `β` and of `kI n β` that is measurable in `β` for each value of `kI n β`. -/
lemma measurable_of_kI {γ : Type*} [MeasurableSpace γ] (G : ℝ × ℕ → γ)
    (hG : ∀ k, Measurable fun β => G (β, k)) : Measurable fun β => G (β, kI n β) :=
  (measurable_from_prod_countable_left hG).comp (measurable_id.prodMk (measurable_kI n))

lemma measurable_ends (n : ℕ) :
    Measurable (fun β => (lI1 n β, rI1 n β)) ∧ Measurable (fun β => (lI2 n β, rI2 n β)) ∧
      Measurable (fun β => (lII1 n β, rII1 n β)) ∧
        Measurable (fun β => (lII2 n β, rII2 n β)) := by
  have hI1 : ∀ j : Fin n, Measurable fun β =>
      blk (n - 1 - kI n β) (kI n β) 1 (0, 0) (0, β) (0, uI n β) (0, 0) j := fun j =>
    measurable_of_kI (fun z : ℝ × ℕ =>
      blk (n - 1 - z.2) z.2 1 (0, 0) (0, z.1) (0, 2 * n - z.2 * z.1) (0, 0) j)
      fun k => by
        dsimp only
        exact measurable_blk _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hI2 : ∀ j : Fin n, Measurable fun β =>
      blk (n - kI n β) (kI n β - 1) 1 (0, 0) (0, β) (uI n β, β) (0, 0) j := fun j =>
    measurable_of_kI (fun z : ℝ × ℕ =>
      blk (n - z.2) (z.2 - 1) 1 (0, 0) (0, z.1) (2 * n - z.2 * z.1, z.1) (0, 0) j)
      fun k => by
        dsimp only
        exact measurable_blk _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hII1 : ∀ j : Fin n, Measurable fun β : ℝ =>
      blk (n - 2) 2 0 (0, 0) (n - β, β) (0, 0) (0, 0) j := fun j =>
    measurable_blk _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hII2 : ∀ j : Fin n, Measurable fun β : ℝ =>
      blk (n - 3) 1 1 (0, 0) (0, β) (0, n - β) (n - β, β) j := fun j =>
    measurable_blk _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Measurable.prodMk ?_ ?_ <;>
    refine measurable_pi_iff.2 fun j => ?_
  · exact (hI1 j).fst
  · exact (hI1 j).snd
  · exact (hI2 j).fst
  · exact (hI2 j).snd
  · exact (hII1 j).fst
  · exact (hII1 j).snd
  · exact (hII2 j).fst
  · exact (hII2 j).snd

/-- The complete mix `Kpiece n β` of `P_β` depends measurably on `β`. -/
theorem measurable_Kpiece (n : ℕ) : Measurable (Kpiece n) := by
  obtain ⟨h1, h2, h3, h4⟩ := measurable_ends n
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hc : MeasurableSet {β : ℝ | caseI n β} := by
    simp only [caseI, ofPred_and]
    exact (MeasurableSet.const _).inter (measurableSet_le measurable_id measurable_const)
  have hu : Measurable (uI n) := by
    have hk : Measurable fun β => (kI n β : ℝ) := measurable_from_nat.comp (measurable_kI n)
    show Measurable fun β => 2 * (n : ℝ) - (kI n β : ℝ) * β
    exact measurable_const.sub (hk.mul measurable_id)
  have e : (fun β => Kpiece n β s) = fun β => if caseI n β then
      (ENNReal.ofReal (uI n β / β) * K1 n (lI1 n β, rI1 n β) s +
        ENNReal.ofReal (1 - uI n β / β) * K1 n (lI2 n β, rI2 n β) s)
      else (ENNReal.ofReal (1 - 2 * (n - β) / β) * K1 n (lII1 n β, rII1 n β) s +
        ENNReal.ofReal (2 * (n - β) / β) * K1 n (lII2 n β, rII2 n β) s) := by
    funext β; unfold Kpiece; split_ifs <;> rfl
  rw [e]
  have hK := fun {g : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hg : Measurable g) =>
    (Kernel.measurable_coe (K1 n) hs).comp hg
  refine Measurable.ite hc ?_ ?_
  · exact ((hu.div measurable_id).ennreal_ofReal.mul (hK h1)).add
      ((measurable_const.sub (hu.div measurable_id)).ennreal_ofReal.mul (hK h2))
  · exact ((by fun_prop : Measurable fun β : ℝ => 1 - 2 * (n - β) / β).ennreal_ofReal.mul
      (hK h3)).add
      ((by fun_prop : Measurable fun β : ℝ => 2 * (n - β) / β).ennreal_ofReal.mul (hK h4))

/-- A mixture of two complete mixes with the same sum is a complete mix of the mixture. -/
lemma isCompleteMix_mix2 {m₁ m₂ : Measure ℝ} {Q₁ Q₂ : Measure (Fin n → ℝ)} {c w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (h₁ : IsCompleteMix n m₁ Q₁) (hs₁ : ∀ᵐ x ∂Q₁, ∑ j, x j = c)
    (h₂ : IsCompleteMix n m₂ Q₂) (hs₂ : ∀ᵐ x ∂Q₂, ∑ j, x j = c) :
    IsCompleteMix n (ENNReal.ofReal w • m₁ + ENNReal.ofReal (1 - w) • m₂)
        (ENNReal.ofReal w • Q₁ + ENNReal.ofReal (1 - w) • Q₂) ∧
      ∀ᵐ x ∂(ENNReal.ofReal w • Q₁ + ENNReal.ofReal (1 - w) • Q₂), ∑ j, x j = c := by
  obtain ⟨hp₁, -, hm₁⟩ := h₁
  obtain ⟨hp₂, -, hm₂⟩ := h₂
  have hs : ∀ᵐ x ∂(ENNReal.ofReal w • Q₁ + ENNReal.ofReal (1 - w) • Q₂), ∑ j, x j = c :=
    ae_add_measure_iff.2 ⟨Measure.ae_smul_measure hs₁ _, Measure.ae_smul_measure hs₂ _⟩
  refine ⟨⟨⟨?_⟩, ⟨c, hs⟩, fun j => ?_⟩, hs⟩
  · simp only [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hw0 (by linarith)]; simp
  · rw [Measure.map_add _ _ (measurable_pi_apply j),
      Measure.map_smul _ (measurable_pi_apply j).aemeasurable,
      Measure.map_smul _ (measurable_pi_apply j).aemeasurable, hm₁ j, hm₂ j]

/-- **Proposition 32 with Lemmas 1 and 3**: for `n ≥ 3` and `2 ≤ β ≤ n`, `Kpiece n β` is an
`n`-complete mix of `P_β` with sum `n`. -/
theorem Kpiece_spec (hn : 3 ≤ n) {β : ℝ} (hβ : 2 ≤ β) (hβn : β ≤ n) :
    IsCompleteMix n (pieceP β) (Kpiece n β) ∧ ∀ᵐ x ∂(Kpiece n β), ∑ j, x j = (n : ℝ) := by
  have hβ0 : 0 < β := by linarith
  unfold Kpiece
  split_ifs with h
  · obtain ⟨hn4, hβ3⟩ := h
    obtain ⟨-, -, hu0, huβ⟩ := caseI_facts hn4 hβ hβ3
    obtain ⟨h₁, hs₁⟩ := K1_spec (tauI1 hn4 hβ hβ3)
    obtain ⟨h₂, hs₂⟩ := K1_spec (tauI2 hn4 hβ hβ3)
    have := isCompleteMix_mix2 (div_nonneg hu0 hβ0.le) ((div_le_one hβ0).2 huβ) h₁ hs₁ h₂ hs₂
    rw [caseI_marginal hn4 hβ hβ3] at this
    exact this
  · have hcase : n = 3 ∨ 2 * n / 3 < β := by
      by_cases h4 : 4 ≤ n
      · exact Or.inr (lt_of_not_ge fun h' => h ⟨h4, h'⟩)
      · exact Or.inl (by omega)
    obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
    obtain ⟨h₁, hs₁⟩ := K1_spec (rhoII1 hn hβ hβn hcase)
    obtain ⟨h₂, hs₂⟩ := K1_spec (rhoII2 hn hβ hβn hcase)
    have hw1 : 0 ≤ 1 - 2 * ((n : ℝ) - β) / β := by rw [sub_nonneg, div_le_one hβ0]; exact hxβ
    have hw2 : 1 - 2 * ((n : ℝ) - β) / β ≤ 1 := by
      have : 0 ≤ 2 * ((n : ℝ) - β) / β := div_nonneg (by linarith) hβ0.le
      linarith
    have := isCompleteMix_mix2 hw1 hw2 h₁ hs₁ h₂ hs₂
    rw [sub_sub_cancel, caseII_marginal hn hβ hβn hcase] at this
    exact this

end Kpiece

/-! ### The pieces `π_U` of Theorem 35 -/

section Piece

open Bipyramid

/-- The total mass `W = (ℓ + r)² / (2 min(ℓ, r))` of the piece `π_U` of Theorem 35, with
`ℓ = μ - a`, `r = b - μ`. -/
def Wf (μ a b : ℝ) : ℝ := ((μ - a) + (b - μ)) ^ 2 / (2 * min (μ - a) (b - μ))

/-- The piece `π_U` of Theorem 35 with ends `a = A(U)`, `b = B(U)`:
`1_[a,b](x) dx + (r² - ℓ²)⁺/(2ℓ) δ_a + (ℓ² - r²)⁺/(2r) δ_b`, `ℓ = μ - a`, `r = b - μ`. -/
def piU (μ a b : ℝ) : Measure ℝ :=
  volume.restrict (Icc a b) +
    ENNReal.ofReal (max ((b - μ) ^ 2 - (μ - a) ^ 2) 0 / (2 * (μ - a))) • Measure.dirac a +
    ENNReal.ofReal (max ((μ - a) ^ 2 - (b - μ) ^ 2) 0 / (2 * (b - μ))) • Measure.dirac b

lemma two_le_beta {μ a b : ℝ} (ha : a < μ) (hb : μ < b) : 2 ≤ Bipyramid.beta μ a b := by
  unfold Bipyramid.beta
  have hm : 0 < min (μ - a) (b - μ) := lt_min (by linarith) (by linarith)
  rw [le_div_iff₀ hm]
  have := min_le_left (μ - a) (b - μ); have := min_le_right (μ - a) (b - μ)
  linarith

/-- Lebesgue measure on `φ⁻¹' T` pushed forward by an affine map `φ y = d + c y`, `c ≠ 0`. -/
lemma map_restrict_affine {d c : ℝ} (hc : c ≠ 0) {S T : Set ℝ} (hT : MeasurableSet T)
    (hST : S = (fun y => d + c * y) ⁻¹' T) :
    (volume.restrict S).map (fun y => d + c * y) = ENNReal.ofReal |c⁻¹| • volume.restrict T := by
  have hm : Measurable fun y : ℝ => d + c * y := (measurable_const_mul c).const_add d
  rw [hST, ← Measure.restrict_map hm hT, map_volume_affine hc, Measure.restrict_smul]

/-- The algebraic part of **Theorem 35**: for `a < μ < b`, `π_U = W · (image of P_β under the
affine map y ↦ μ - ℓ + ℓ y if ℓ ≤ r, y ↦ μ + r - r y otherwise)`, `β = (ℓ + r)/min(ℓ, r)`. -/
theorem piU_eq {μ a b : ℝ} (ha : a < μ) (hb : μ < b) :
    piU μ a b = ENNReal.ofReal (Wf μ a b) •
      (pieceP (Bipyramid.beta μ a b)).map (pieceMap μ (μ - a) (b - μ)) := by
  set l := μ - a with hl
  set r := b - μ with hr
  have hl0 : 0 < l := by linarith
  have hr0 : 0 < r := by linarith
  have hβ0 : 0 < Bipyramid.beta μ a b := by linarith [two_le_beta ha hb]
  rw [pieceP_eq hβ0]
  unfold pieceMap piU Wf
  rw [← hl, ← hr]
  have hW0 : 0 ≤ (l + r) ^ 2 / (2 * min l r) := by positivity
  by_cases h : l ≤ r
  · have hβ : Bipyramid.beta μ a b = (l + r) / l := by
      unfold Bipyramid.beta; rw [← hl, ← hr, min_eq_left h]
    simp only [h, ↓reduceIte]
    have hm : Measurable fun y : ℝ => μ - l + l * y := by fun_prop
    rw [Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
      Measure.map_smul _ hm.aemeasurable, Measure.map_dirac' hm,
      map_restrict_affine hl0.ne' measurableSet_Icc (T := Icc a b)]
    · have e1 : max (l ^ 2 - r ^ 2) 0 / (2 * r) = 0 := by
        rw [max_eq_right (by nlinarith)]; simp
      have e2 : ENNReal.ofReal ((l + r) ^ 2 / (2 * min l r)) *
          ENNReal.ofReal (1 - 2 / Bipyramid.beta μ a b) =
          ENNReal.ofReal (max (r ^ 2 - l ^ 2) 0 / (2 * l)) := by
        rw [← ENNReal.ofReal_mul hW0, max_eq_left (by nlinarith), hβ, min_eq_left h]
        congr 1; field_simp; ring
      have e3 : ENNReal.ofReal ((l + r) ^ 2 / (2 * min l r)) *
          ENNReal.ofReal (2 / Bipyramid.beta μ a b ^ 2) * ENNReal.ofReal |l⁻¹| = 1 := by
        rw [← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul (by positivity), hβ, min_eq_left h,
          abs_of_pos (inv_pos.2 hl0), ← ENNReal.ofReal_one]
        congr 1; field_simp
      rw [e1, ENNReal.ofReal_zero, zero_smul, add_zero, smul_add, smul_smul, smul_smul,
        smul_smul, e2, e3, one_smul, add_comm, show μ - l + l * 0 = a by simp [hl]]
    · ext y; simp only [mem_Icc, mem_preimage, hβ]
      rw [le_div_iff₀ hl0]
      constructor <;> intro hy <;> constructor <;> nlinarith [hy.1, hy.2]
  · push Not at h
    have hβ : Bipyramid.beta μ a b = (l + r) / r := by
      unfold Bipyramid.beta; rw [← hl, ← hr, min_eq_right h.le]
    simp only [not_le.2 h, ↓reduceIte]
    have ef : (fun y : ℝ => μ + r - r * y) = fun y => (μ + r) + (-r) * y := by
      funext y; ring
    rw [ef]
    have hm : Measurable fun y : ℝ => (μ + r) + (-r) * y := by fun_prop
    rw [Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
      Measure.map_smul _ hm.aemeasurable, Measure.map_dirac' hm,
      map_restrict_affine (neg_ne_zero.2 hr0.ne') measurableSet_Icc (T := Icc a b)]
    · have e1 : max (r ^ 2 - l ^ 2) 0 / (2 * l) = 0 := by
        rw [max_eq_right (by nlinarith)]; simp
      have e2 : ENNReal.ofReal ((l + r) ^ 2 / (2 * min l r)) *
          ENNReal.ofReal (1 - 2 / Bipyramid.beta μ a b) =
          ENNReal.ofReal (max (l ^ 2 - r ^ 2) 0 / (2 * r)) := by
        rw [← ENNReal.ofReal_mul hW0, max_eq_left (by nlinarith), hβ, min_eq_right h.le]
        congr 1; field_simp; ring
      have e3 : ENNReal.ofReal ((l + r) ^ 2 / (2 * min l r)) *
          ENNReal.ofReal (2 / Bipyramid.beta μ a b ^ 2) * ENNReal.ofReal |(-r)⁻¹| = 1 := by
        rw [← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul (by positivity), hβ,
          min_eq_right h.le, inv_neg, abs_neg, abs_of_pos (inv_pos.2 hr0), ← ENNReal.ofReal_one]
        congr 1; field_simp
      rw [e1, ENNReal.ofReal_zero, zero_smul, add_zero, smul_add, smul_smul, smul_smul,
        smul_smul, e2, e3, one_smul, add_comm, show μ + r + -r * 0 = b by simp [hr]]
    · ext y; simp only [mem_Icc, mem_preimage, hβ]
      rw [le_div_iff₀ hr0]
      constructor <;> intro hy <;> constructor <;> nlinarith [hy.1, hy.2]

end Piece

/-! ### Theorem 36 -/

section Thm36

open Bipyramid

variable {n : ℕ}

/-- `Kpiece n β` where it is a complete mix of `P_β` (`2 ≤ β ≤ n`), a point mass otherwise
(the construction only uses `2 ≤ β ≤ n`; the guard makes it a Markov kernel). -/
def Kp (n : ℕ) (β : ℝ) : Measure (Fin n → ℝ) :=
  if 2 ≤ β ∧ β ≤ n then Kpiece n β else Measure.dirac 0

lemma measurable_Kp (n : ℕ) : Measurable (Kp n) := by
  have hs : MeasurableSet {β : ℝ | 2 ≤ β ∧ β ≤ n} := by
    simp only [ofPred_and]
    exact (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)
  exact Measurable.piecewise hs (measurable_Kpiece n) measurable_const

/-- The Markov kernel `β ↦ Kp n β`. -/
def KpK (n : ℕ) : Kernel ℝ (Fin n → ℝ) := ⟨Kp n, measurable_Kp n⟩

lemma isMarkovKernel_KpK (hn : 3 ≤ n) : IsMarkovKernel (KpK n) := ⟨fun β => by
  change IsProbabilityMeasure (Kp n β)
  unfold Kp
  split_ifs with h
  · exact (Kpiece_spec hn h.1 h.2).1.1
  · infer_instance⟩

open Classical in
/-- `A(U)` on `[0, f(μ))`, extended by `μ - 1` (only the values on `[0, f(μ))` matter). -/
def Aext (f : ℝ → ℝ) (μ : ℝ) (A : ℝ → ℝ) : ℝ → ℝ := (Ico 0 (f μ)).piecewise A fun _ => μ - 1

open Classical in
/-- `B(U)` on `[0, f(μ))`, extended by `μ + 1`. -/
def Bext (f : ℝ → ℝ) (μ : ℝ) (B : ℝ → ℝ) : ℝ → ℝ := (Ico 0 (f μ)).piecewise B fun _ => μ + 1

/-- The law of the level `U`: density `W(U)` on `[0, f(μ))`. -/
def levelLaw (f : ℝ → ℝ) (μ : ℝ) (A B : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ico 0 (f μ))).withDensity
    fun U => ENNReal.ofReal (Wf μ (Aext f μ A U) (Bext f μ B U))

/-- The conditional law of `(X_1, …, X_n)` given the level `U` in Theorem 36: the complete mix
`Kpiece n β(U)` of `P_β(U)` mapped coordinatewise by `y ↦ μ - ℓ + ℓ y` (if `ℓ ≤ r`) or
`y ↦ μ + r - r y` (otherwise), `ℓ = μ - A(U)`, `r = B(U) - μ`. -/
def levelMix (n : ℕ) (f : ℝ → ℝ) (μ : ℝ) (A B : ℝ → ℝ) (U : ℝ) : Measure (Fin n → ℝ) :=
  (Kp n (beta μ (Aext f μ A U) (Bext f μ B U))).map
    fun y j => pieceMap μ (μ - Aext f μ A U) (Bext f μ B U - μ) (y j)

/-- The complete mix of Theorem 36: the law of `(X_1, …, X_n)`, `U ∼ W(U) dU` on `[0, f(μ))`. -/
def mixQ (n : ℕ) (f : ℝ → ℝ) (μ : ℝ) (A B : ℝ → ℝ) : Measure (Fin n → ℝ) :=
  (levelLaw f μ A B).bind (levelMix n f μ A B)

/-- **Theorem 36** (`c:thm:mix`). Let `n ≥ 3` and let `f` be a probability density on `[0, 1]`
with peeling ends `A(U)`, `B(U)` on `[0, f(μ))` (Theorem 34). Hypotheses taken from
Theorems 34 and 35 (proved elsewhere):

* `hAB`, `hAc`, `hBc` (Theorem 34 (b)): `A(U) < μ < B(U)`, and `A`, `B` are continuous on
  `[0, f(μ))`;
* `H35` (Theorem 35, equation `c:eq:decomp`, for indicator functions):
  `∫_0^{f(μ)} π_U(S) dU = ∫_S f` for every measurable `S`.

If `β(U) ≤ n` for `0 ≤ U < f(μ)`, then `mixQ n f μ A B` (draw `U` with density `W`, take the
complete mix `Kpiece` of `P_β(U)` and map it affinely) is an `n`-complete mix of the distribution
with density `f`, with sum `n μ`. -/
theorem thm36 (hn : 3 ≤ n) {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ}
    (hf : IsProbabilityMeasure (densityOn01 f))
    (hAB : ∀ U ∈ Ico 0 (f μ), A U < μ ∧ μ < B U)
    (hAc : ContinuousOn A (Ico 0 (f μ))) (hBc : ContinuousOn B (Ico 0 (f μ)))
    (H35 : ∀ S, MeasurableSet S →
      ∫⁻ U in Ico 0 (f μ), piU μ (A U) (B U) S = densityOn01 f S)
    (hβ : ∀ U, 0 ≤ U → U < f μ → beta μ (A U) (B U) ≤ n) :
    IsCompleteMix n (densityOn01 f) (mixQ n f μ A B) ∧
      ∀ᵐ x ∂(mixQ n f μ A B), ∑ j, x j = n * μ := by
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
  -- the measure `π_U` through `P_β(U)`
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
  have := isMarkovKernel_KpK hn
  set κ : Kernel ℝ (Fin n → ℝ) := (KpK n).comap β' hβm with hκ
  have hκU : ∀ U, κ U = Kp n (β' U) := fun U => rfl
  have hn0 : 0 < n := by omega
  have hT27 : ∀ U, (∀ i : Fin n, β' U * (1 : Fin n → ℝ) i ≤ ∑ j, (1 : Fin n → ℝ) j) →
      IsJointMix (fun i => scaledPiece (β' U) ((1 : Fin n → ℝ) i)) (κ U) ∧
        ∀ᵐ v ∂(κ U), ∑ i, v i = ∑ i, (1 : Fin n → ℝ) i := by
    intro U hU
    have hle : β' U ≤ n := by simpa using hU ⟨0, hn0⟩
    have e : ∀ i : Fin n, scaledPiece (β' U) ((1 : Fin n → ℝ) i) = pieceP (β' U) := fun i => by
      simp [scaledPiece]
    simp only [e, hκU, Kp, ite_eq_left (And.intro (hβ2 U) hle)]
    simpa [IsCompleteMix] using Kpiece_spec hn (hβ2 U) hle
  have hβae : ∀ᵐ U ∂ω, ∀ i : Fin n, β' U * (1 : Fin n → ℝ) i ≤ ∑ j, (1 : Fin n → ℝ) j := by
    have hac : ω ≪ volume.restrict I := withDensity_absolutelyContinuous _ _
    refine hac ((ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ fun U hU i => ?_))
    simp only [Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hβ'def, hAeq U hU, hBeq U hU]
    exact hβ U hU.1 hU.2
  obtain ⟨hmix, hsum⟩ := thm73b (densityOn01 f) ω μ (l := fun U => μ - A' U)
    (r := fun U => B' U - μ) (measurable_const.sub hA') (hB'.sub measurable_const) (β := β')
    (fun S hS => (hint S hS).symm) 0 1 κ
    hT27 hβae
  have eQ : (ω.bind fun U => (κ U).map (scaledTuple 0 1 μ (μ - A' U) (B' U - μ))) =
      mixQ n f μ A B := by
    rw [mixQ, hωdef]
    congr 1
    funext U
    rw [hκU, levelMix]
    congr 1
    funext v i
    simp only [scaledTuple, pieceMap, Pi.zero_apply, Pi.one_apply]
    split_ifs <;> ring
  rw [eQ] at hmix hsum
  refine ⟨?_, ?_⟩
  · simpa [IsCompleteMix] using hmix
  · filter_upwards [hsum] with x hx
    rw [hx]; simp [mul_comm]

/-- Theorem 36 in the form of the hypothesis `H36` of `Bipyramid.pconc` (Theorem 67). -/
theorem H36_of {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ} (hf : IsProbabilityMeasure (densityOn01 f))
    (hAB : ∀ U ∈ Ico 0 (f μ), A U < μ ∧ μ < B U)
    (hAc : ContinuousOn A (Ico 0 (f μ))) (hBc : ContinuousOn B (Ico 0 (f μ)))
    (H35 : ∀ S, MeasurableSet S →
      ∫⁻ U in Ico 0 (f μ), piU μ (A U) (B U) S = densityOn01 f S) :
    ∀ n : ℕ, 3 ≤ n → (∀ U, 0 ≤ U → U < f μ → beta μ (A U) (B U) ≤ n) →
      CompletelyMixable n (densityOn01 f) :=
  fun _ hn hβ => ⟨_, (thm36 hn hf hAB hAc hBc H35 hβ).1⟩

/-- A continuous nonnegative function on `[0, 1]` with integral `1` is a probability density. -/
lemma isProb_densityOn01 {f : ℝ → ℝ} (hfc : ContinuousOn f (Icc 0 1))
    (hf0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0:ℝ)..1, f x = 1) :
    IsProbabilityMeasure (densityOn01 f) := by
  constructor
  rw [densityOn01, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hfc.integrableOn_compact isCompact_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc hf0),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hf1,
    ENNReal.ofReal_one]

/-- **Theorem 67** (`o:thm:pconc`) with Theorem 36 proved (`H36_of`): only Theorems 34 and 35
remain as hypotheses. -/
theorem pconc' {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (μ : ℝ)
    (hdens : ∫ x in (0:ℝ)..1, g x ^ p = 1) (hμ : μ = ∫ x in (0:ℝ)..1, x * g x ^ p)
    (A B : ℝ → ℝ) (H34 : PeelingProps (fun x => g x ^ p) μ A B)
    (hAc : ContinuousOn A (Ico 0 (g μ ^ p))) (hBc : ContinuousOn B (Ico 0 (g μ ^ p)))
    (H35 : ∀ S, MeasurableSet S →
      ∫⁻ U in Ico 0 (g μ ^ p), piU μ (A U) (B U) S = densityOn01 (fun x => g x ^ p) S) :
    ∀ n : ℕ, p + 2 ≤ n → CompletelyMixable n (densityOn01 fun x => g x ^ p) := by
  have hf : IsProbabilityMeasure (densityOn01 fun x => g x ^ p) :=
    isProb_densityOn01 (hgc.rpow_const fun x _ => Or.inr (by linarith))
      (fun x hx => Real.rpow_nonneg (hg0 x hx) _) hdens
  refine pconc hp hg hgc hg0 μ hdens hμ A B H34 (H36_of hf ?_ hAc hBc H35)
  intro U hU
  obtain ⟨-, h1, h2, -⟩ := H34 U hU.1 hU.2
  exact ⟨h1, h2⟩

end Thm36

/-! ### Corollary 39 -/

section Cor39

open Bipyramid

variable {n : ℕ}

/-- **Corollary 39** (`c:cor:concave`). Let `f` be a concave probability density on `[0, 1]`
(continuous on `[0, 1]`), with mean `μ` and peeling ends `A`, `B`. With Theorem 34 (a), (b)
(`H34`, `hAc`, `hBc`) and Theorem 35 (`H35`) as hypotheses: `β(U) ≤ 3` for `0 ≤ U < f(μ)`, and
for every `n ≥ 3` the construction `mixQ` of Theorem 36 (Algorithm 37) is an `n`-complete mix
of `f` with sum `n μ`. -/
theorem cor39 {f : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc 0 1) f) (hfc : ContinuousOn f (Icc 0 1))
    (hf0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0:ℝ)..1, f x = 1) {μ : ℝ}
    {A B : ℝ → ℝ} (H34 : PeelingProps f μ A B)
    (hAc : ContinuousOn A (Ico 0 (f μ))) (hBc : ContinuousOn B (Ico 0 (f μ)))
    (H35 : ∀ S, MeasurableSet S →
      ∫⁻ U in Ico 0 (f μ), piU μ (A U) (B U) S = densityOn01 f S) :
    (∀ U, 0 ≤ U → U < f μ → beta μ (A U) (B U) ≤ 3) ∧
      ∀ n : ℕ, 3 ≤ n → IsCompleteMix n (densityOn01 f) (mixQ n f μ A B) ∧
        ∀ᵐ x ∂(mixQ n f μ A B), ∑ j, x j = n * μ := by
  have h3 : ∀ U, 0 ≤ U → U < f μ → beta μ (A U) (B U) ≤ 3 := by
    intro U hU hUμ
    obtain ⟨hA0, hAμ, hμB, hB1, hfU, hmean⟩ := H34 U hU hUμ
    have sub : Icc (A U) (B U) ⊆ Icc 0 1 := Icc_subset_Icc hA0 hB1
    have hμI : μ ∈ Ioo (A U) (B U) := ⟨hAμ, hμB⟩
    obtain ⟨h1, h2⟩ := beta_le (p := 1) le_rfl hU (hconc.subset sub (convex_Icc _ _))
      (hfc.mono sub) (fun x hx => hf0 x (sub hx)) (by simpa using hfU) hμI (by simpa using hUμ)
      (by simpa using hmean)
    have := beta_le_of one_pos hμI h1 h2
    norm_num at this
    exact this
  refine ⟨h3, fun n hn => thm36 hn (isProb_densityOn01 hfc hf0 hf1) ?_ hAc hBc H35 ?_⟩
  · intro U hU
    obtain ⟨-, h1, h2, -⟩ := H34 U hU.1 hU.2
    exact ⟨h1, h2⟩
  · intro U hU hUμ
    exact (h3 U hU hUμ).trans (by exact_mod_cast hn)

end Cor39

end ConcaveMix

end Mixes
