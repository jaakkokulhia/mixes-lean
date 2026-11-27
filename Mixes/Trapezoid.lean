import Mathlib

/-!
# The inequalities of Theorem 40 (trapezoids)

Item M1a of the verification priorities: the elementary inequalities in the proof of
Theorem 40 (`t:thm:trap` in `mixes/main.tex`). The trapezoid is
`{(x, y) : 0 ≤ x ≤ 1, g x ≤ y ≤ g x + h x}` with `h x = q + (1 - q) x`, `0 ≤ q ≤ 1`, and
`g` affine. The abscissa has density `h / ∫₀¹ h` on `[0, 1]`.

* `Mixes.trapMean_eq_integral`: the mean of the density `h / ∫ h` is
  `c = (q + 2) / (3 (q + 1))`, and it agrees with the first expression of the paper.
* `Mixes.trapMean_mem`: `c ∈ [1/2, 2/3]`.
* `Mixes.trap_meancond`: the mean condition (1) on `[0, 1]` for every `n ≥ 3`.
* `Mixes.trap_polygon`: the polygon inequality `2 h(xᵢ) ≤ ∑ⱼ h(xⱼ)`.
* `Mixes.trap_nh_eq_two_iff`: `n h(c) = 2` only for the triangle (`q = 0`) and `n = 3`.
* `Mixes.trap_const_sum`: `∑ᵢ (g(xᵢ) + h(xᵢ)/2) = n (g(c) + h(c)/2)` for affine `g`.
-/

namespace Mixes

open Finset intervalIntegral

/-- The chord length `h(x) = q + (1 - q) x` of the trapezoid. -/
def trapH (q x : ℝ) : ℝ := q + (1 - q) * x

/-- The mean `c = (q + 2) / (3 (q + 1))` of the abscissa. -/
noncomputable def trapMean (q : ℝ) : ℝ := (q + 2) / (3 * (q + 1))

/-- The first expression of the paper for the mean agrees with the closed form. -/
theorem trapMean_eq_paper {q : ℝ} (hq : 0 ≤ q) :
    (q / 2 + (1 - q) / 3) / (q + (1 - q) / 2) = trapMean q := by
  unfold trapMean
  have h1 : q + 1 ≠ 0 := by linarith
  have h2 : q + (1 - q) / 2 ≠ 0 := by linarith
  rw [div_eq_div_iff h2 (by positivity)]
  ring

/-- `∫₀¹ h = (q + 1) / 2`, which is positive. -/
theorem integral_trapH (q : ℝ) : ∫ x in (0 : ℝ)..1, trapH q x = (q + 1) / 2 := by
  unfold trapH
  simp [integral_add, mul_comm]
  ring

/-- `∫₀¹ x h(x) dx = (q + 2) / 6`. -/
theorem integral_mul_trapH (q : ℝ) :
    ∫ x in (0 : ℝ)..1, x * trapH q x = (q + 2) / 6 := by
  have : (fun x : ℝ => x * trapH q x) = fun x => q * x + (1 - q) * x ^ 2 := by
    funext x; unfold trapH; ring
  rw [this, integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_const_mul,
    integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

/-- The mean of the density `h / ∫₀¹ h` on `[0, 1]` is `c = (q + 2) / (3 (q + 1))`. -/
theorem trapMean_eq_integral {q : ℝ} (hq : 0 ≤ q) :
    (∫ x in (0 : ℝ)..1, x * trapH q x) / (∫ x in (0 : ℝ)..1, trapH q x) = trapMean q := by
  rw [integral_mul_trapH, integral_trapH, trapMean]
  have h1 : q + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The mean lies in `[1/2, 2/3]` for `0 ≤ q ≤ 1`. -/
theorem trapMean_mem {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 / 2 ≤ trapMean q ∧ trapMean q ≤ 2 / 3 := by
  unfold trapMean
  have h1 : 0 < 3 * (q + 1) := by linarith
  constructor
  · rw [le_div_iff₀ h1]; linarith
  · rw [div_le_iff₀ h1]; linarith

/-- The mean condition (1) for the abscissa, supported on `[0, 1]`, holds for every `n ≥ 3`:
`0 + (1 - 0)/n ≤ c ≤ 1 - (1 - 0)/n`. -/
theorem trap_meancond {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 3 ≤ n) :
    (0 : ℝ) + (1 - 0) / n ≤ trapMean q ∧ trapMean q ≤ 1 - (1 - 0) / n := by
  obtain ⟨hc1, hc2⟩ := trapMean_mem hq0 hq1
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (1 : ℝ) / n ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hn'
  constructor <;> simp only [zero_add, sub_zero] <;> linarith

/-- `h(c) = 2 (q² + q + 1) / (3 (q + 1))`. -/
theorem trapH_trapMean {q : ℝ} (hq : 0 ≤ q) :
    trapH q (trapMean q) = 2 * (q ^ 2 + q + 1) / (3 * (q + 1)) := by
  unfold trapH trapMean
  have h1 : q + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `h(c) ≥ 2/3`. -/
theorem two_thirds_le_trapH_trapMean {q : ℝ} (hq : 0 ≤ q) :
    2 / 3 ≤ trapH q (trapMean q) := by
  rw [trapH_trapMean hq, le_div_iff₀ (by linarith)]
  nlinarith

/-- For an affine function the sum over a tuple with sum `n c` is `n` times the value at `c`. -/
theorem sum_affine_eq {n : ℕ} (a b c : ℝ) (x : Fin n → ℝ) (hsum : ∑ i, x i = n * c) :
    ∑ i, (a + b * x i) = n * (a + b * c) := by
  rw [sum_add_distrib, ← mul_sum, hsum]
  simp
  ring

/-- The total chord length `∑ⱼ h(xⱼ) = n h(c)` is constant. -/
theorem sum_trapH {n : ℕ} (q : ℝ) (x : Fin n → ℝ) (hsum : ∑ i, x i = n * trapMean q) :
    ∑ i, trapH q (x i) = n * trapH q (trapMean q) :=
  sum_affine_eq q (1 - q) _ x hsum

/-- **Polygon inequality** (proof of Theorem 40). If `n ≥ 3`, `0 ≤ q ≤ 1`, and
`x₁, …, xₙ ∈ [0, 1]` have sum `n c`, then `2 h(xᵢ) ≤ ∑ⱼ h(xⱼ)` for every `i`. -/
theorem trap_polygon {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 3 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ i, x i = n * trapMean q)
    (i : Fin n) : 2 * trapH q (x i) ≤ ∑ j, trapH q (x j) := by
  rw [sum_trapH q x hsum]
  have hhc := two_thirds_le_trapH_trapMean hq0
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hxi : trapH q (x i) ≤ 1 := by
    unfold trapH
    nlinarith [(hx i).2, (hx i).1]
  nlinarith

/-- Equality case: `n h(c) = 2` (for `n ≥ 3`) exactly for the triangle `q = 0` and `n = 3`. -/
theorem trap_nh_eq_two_iff {q : ℝ} (hq0 : 0 ≤ q) {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) * trapH q (trapMean q) = 2 ↔ q = 0 ∧ n = 3 := by
  rw [trapH_trapMean hq0]
  have h1 : 0 < 3 * (q + 1) := by linarith
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · intro h
    rw [mul_div_assoc', div_eq_iff h1.ne'] at h
    -- n * 2 (q² + q + 1) = 6 (q + 1), with q² + q + 1 ≥ q + 1 and n ≥ 3
    have hq : q = 0 := by nlinarith
    subst hq
    refine ⟨rfl, ?_⟩
    have : (n : ℝ) = 3 := by linarith
    exact_mod_cast this
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- **Constant sum** (proof of Theorem 40). For every affine `g(x) = a + b x` and every tuple
with `∑ xᵢ = n c`, `∑ᵢ (g(xᵢ) + h(xᵢ)/2) = n (g(c) + h(c)/2)`. -/
theorem trap_const_sum {n : ℕ} (q a b : ℝ) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = n * trapMean q) :
    ∑ i, ((a + b * x i) + trapH q (x i) / 2)
      = n * ((a + b * trapMean q) + trapH q (trapMean q) / 2) := by
  have := sum_affine_eq (a + q / 2) (b + (1 - q) / 2) _ x hsum
  unfold trapH
  convert this using 2 <;> ring

end Mixes
