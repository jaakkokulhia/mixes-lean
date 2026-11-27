import Mathlib

/-!
# Complete and joint mixes: definitions

Following the paper (Section 1, Section 3 and Definition 2), and the brief's advice, mixes are
probability measures on tuples rather than random vectors.

* `IsJointMix F P`: `P` is a probability measure on `Fin n → E` whose coordinate marginals are the
  `F j` and which is concentrated on a hyperplane `x₁ + ⋯ + xₙ = s`.
* `IsCompleteMix n F P`: a joint mix of `n` copies of `F`.
* `JointlyMixable`, `CompletelyMixable`: such a measure exists.
* `unifI l r`: the uniform distribution on `[l, r]`, the point mass at `l` when `l = r`.
* `unifSet K`: the uniform distribution on a set `K` of finite positive volume.
* `Admissible`: the admissible tuples of Definition 2, with their marginal `Admissible.marginal`.
-/

open MeasureTheory

noncomputable section

namespace Mixes

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E] {n : ℕ}

/-- `P` is a joint mix of `F 0, …, F (n-1)`: a probability measure on `n`-tuples with the given
coordinate marginals whose coordinates add up to a constant almost surely. -/
def IsJointMix (F : Fin n → Measure E) (P : Measure (Fin n → E)) : Prop :=
  IsProbabilityMeasure P ∧ (∃ s : E, ∀ᵐ x ∂P, ∑ j, x j = s) ∧
    ∀ j, P.map (fun x => x j) = F j

/-- `P` is an `n`-complete mix of `F`. -/
def IsCompleteMix (n : ℕ) (F : Measure E) (P : Measure (Fin n → E)) : Prop :=
  IsJointMix (fun _ : Fin n => F) P

/-- `F 0, …, F (n-1)` are jointly mixable. -/
def JointlyMixable (F : Fin n → Measure E) : Prop := ∃ P, IsJointMix F P

/-- `F` is `n`-completely mixable. -/
def CompletelyMixable (n : ℕ) (F : Measure E) : Prop :=
  ∃ P : Measure (Fin n → E), IsCompleteMix n F P

/-- `U[l, r]`: the uniform distribution on `[l, r]` for `l < r`, and the point mass at `l`
otherwise (the paper uses it only for `l ≤ r`). -/
def unifI (l r : ℝ) : Measure ℝ :=
  if l < r then (ENNReal.ofReal (r - l))⁻¹ • volume.restrict (Set.Icc l r) else Measure.dirac l

/-- The uniform distribution on a set `K` (meaningful when `0 < volume K < ∞`). -/
def unifSet {d : Type*} [MeasureSpace d] (K : Set d) : Measure d :=
  (volume K)⁻¹ • volume.restrict K

/-- An admissible tuple (Definition 2): intervals `[l j, r j]`, not all of length `0`, satisfying
the polygon inequality `2 max |I_j| ≤ ∑ |I_j|`, with midpoints adding up to `n`. -/
structure Admissible (n : ℕ) where
  l : Fin n → ℝ
  r : Fin n → ℝ
  le : ∀ j, l j ≤ r j
  pos : ∃ j, l j < r j
  polygon : ∀ k, 2 * (r k - l k) ≤ ∑ j, (r j - l j)
  mid : ∑ j, (l j + r j) = 2 * n

/-- The marginal of an admissible tuple, `(1/n) ∑ U(I_j)`. -/
def Admissible.marginal (τ : Admissible n) : Measure ℝ :=
  ((n : ENNReal)⁻¹) • ∑ j, unifI (τ.l j) (τ.r j)

lemma unifI_isProb (l r : ℝ) : IsProbabilityMeasure (unifI l r) := by
  unfold unifI
  split_ifs with hlr
  · constructor
    rw [smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using hlr) ENNReal.ofReal_ne_top
  · infer_instance

end Mixes
