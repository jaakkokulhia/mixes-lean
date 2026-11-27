import Mathlib

/-!
# The algebra of frusta (Lemma 54)

Item M1f (algebraic part) of the verification priorities: Lemma 54 (`b:lem:akq` in
`mixes/main.tex`) on the constants
`μ_{k,q} = k/(k+1) · (1 - q^{k+1}) / (1 - q^k)` and
`a_{k,q} = (1 - q) / (1 - μ_{k,q}) = (k+1)(1 + q + ⋯ + q^{k-1}) / (1 + 2q + ⋯ + k q^{k-1})`,
for `k ≥ 1` and `0 ≤ q < 1`. We also prove the mean computation of Lemma 55: the level
density `k s^{k-1} / ((1 - q^k) λ^k)` on `[qλ, λ]` is a probability density with mean
`μ_{k,q} λ`.

Main results:
* `Mixes.akq_eq`: the two expressions for `a_{k,q}` agree.
* `Mixes.muKQ_ge`, `Mixes.muKQ_lt_one`: `k/(k+1) ≤ μ_{k,q} < 1`.
* `Mixes.akq_le`, `Mixes.akq_eq_iff`: `a_{k,q} ≤ k+1`, with equality iff `q = 0` or `k = 1`.
* `Mixes.two_lt_akq`: `a_{k,q} > 2` for `k ≥ 2`.
* `Mixes.frustum_density_integral`, `Mixes.frustum_density_mean`: Lemma 55's integrals.
-/

namespace Mixes

open Finset intervalIntegral

/-- `μ_{k,q} = k/(k+1) · (1 - q^{k+1}) / (1 - q^k)`. -/
noncomputable def muKQ (k : ℕ) (q : ℝ) : ℝ :=
  (k : ℝ) / (k + 1) * ((1 - q ^ (k + 1)) / (1 - q ^ k))

/-- First expression: `a_{k,q} = (1 - q) / (1 - μ_{k,q})`. -/
noncomputable def aKQ (k : ℕ) (q : ℝ) : ℝ := (1 - q) / (1 - muKQ k q)

/-- `1 + q + ⋯ + q^{k-1}`. -/
noncomputable def geomS (k : ℕ) (q : ℝ) : ℝ := ∑ j ∈ range k, q ^ j

/-- `1 + 2q + ⋯ + k q^{k-1}`. -/
noncomputable def weightS (k : ℕ) (q : ℝ) : ℝ := ∑ j ∈ range k, ((j : ℝ) + 1) * q ^ j

/-- Second expression: `(k+1)(1 + q + ⋯ + q^{k-1}) / (1 + 2q + ⋯ + k q^{k-1})`. -/
noncomputable def aKQ' (k : ℕ) (q : ℝ) : ℝ := (k + 1) * geomS k q / weightS k q

lemma one_sub_pow_eq (k : ℕ) (q : ℝ) : 1 - q ^ k = (1 - q) * geomS k q := by
  unfold geomS
  have := geom_sum_mul q k
  linarith [this, show (∑ i ∈ range k, q ^ i) * (q - 1) = -((1 - q) * ∑ i ∈ range k, q ^ i)
    by ring]

/-- `1 - (k+1) q^k + k q^{k+1} = (1 - q)² ∑_{j<k} (j+1) q^j`. -/
lemma key_identity (k : ℕ) (q : ℝ) :
    1 - (k + 1) * q ^ k + k * q ^ (k + 1) = (1 - q) ^ 2 * weightS k q := by
  induction k with
  | zero => simp [weightS]
  | succ k ih =>
    unfold weightS at *
    rw [sum_range_succ, mul_add, ← ih]
    push_cast
    ring

lemma geomS_pos {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : 0 ≤ q) : 0 < geomS k q := by
  unfold geomS
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, sum_range_succ']
  have : 0 ≤ ∑ i ∈ range m, q ^ (i + 1) := sum_nonneg fun i _ => by positivity
  simp; linarith

lemma weightS_sub_geomS (k : ℕ) (q : ℝ) :
    weightS k q - geomS k q = ∑ j ∈ range k, (j : ℝ) * q ^ j := by
  unfold weightS geomS
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

lemma geomS_le_weightS (k : ℕ) {q : ℝ} (hq : 0 ≤ q) : geomS k q ≤ weightS k q := by
  have := weightS_sub_geomS k q
  have : 0 ≤ ∑ j ∈ range k, (j : ℝ) * q ^ j := sum_nonneg fun j _ => by positivity
  linarith

lemma weightS_pos {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : 0 ≤ q) : 0 < weightS k q :=
  (geomS_pos hk hq).trans_le (geomS_le_weightS k hq)

/-- `1 - μ_{k,q} = (1 - q) ∑ (j+1) q^j / ((k+1) ∑ q^j)`. -/
lemma one_sub_muKQ {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 - muKQ k q = (1 - q) * weightS k q / ((k + 1) * geomS k q) := by
  have hS := geomS_pos hk hq0
  have h1q : 0 < 1 - q := by linarith
  have hd : 1 - q ^ k = (1 - q) * geomS k q := one_sub_pow_eq k q
  have hkey := key_identity k q
  unfold muKQ
  rw [hd]
  field_simp
  have : (k + 1 : ℝ) * ((1 - q) * geomS k q) - k * (1 - q ^ (k + 1))
      = (1 - q) ^ 2 * weightS k q := by rw [← hd, ← hkey]; ring
  linear_combination this

/-- Lemma 54: the two expressions for `a_{k,q}` agree. -/
theorem akq_eq {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    aKQ k q = aKQ' k q := by
  have hS := geomS_pos hk hq0
  have hP := weightS_pos hk hq0
  have h1q : 0 < 1 - q := by linarith
  unfold aKQ aKQ'
  rw [one_sub_muKQ hk hq0 hq1]
  field_simp

/-- Lemma 54: `μ_{k,q} < 1`. -/
theorem muKQ_lt_one {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    muKQ k q < 1 := by
  have h := one_sub_muKQ hk hq0 hq1
  have : 0 < (1 - q) * weightS k q / ((k + 1) * geomS k q) := by
    have := geomS_pos hk hq0; have := weightS_pos hk hq0
    have : 0 < 1 - q := by linarith
    positivity
  linarith

/-- Lemma 54: `k/(k+1) ≤ μ_{k,q}`. -/
theorem muKQ_ge {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (k : ℝ) / (k + 1) ≤ muKQ k q := by
  unfold muKQ
  have hpk : q ^ k < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  have hle : q ^ (k + 1) ≤ q ^ k := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have h1 : 1 ≤ (1 - q ^ (k + 1)) / (1 - q ^ k) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have : (0 : ℝ) ≤ k / (k + 1) := by positivity
  nlinarith

/-- Lemma 54: `a_{k,q} ≤ k + 1`. -/
theorem akq_le {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    aKQ k q ≤ k + 1 := by
  rw [akq_eq hk hq0 hq1, aKQ', div_le_iff₀ (weightS_pos hk hq0)]
  have := geomS_le_weightS k hq0
  have : (0 : ℝ) ≤ k + 1 := by positivity
  nlinarith

/-- Lemma 54: `a_{k,q} = k + 1` if and only if `q = 0` or `k = 1`. -/
theorem akq_eq_iff {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    aKQ k q = k + 1 ↔ q = 0 ∨ k = 1 := by
  have hP := weightS_pos hk hq0
  have hS := geomS_pos hk hq0
  have hd := weightS_sub_geomS k q
  rw [akq_eq hk hq0 hq1, aKQ', div_eq_iff hP.ne']
  constructor
  · intro h
    have hPS : weightS k q = geomS k q := by
      have : (0 : ℝ) < k + 1 := by positivity
      have := mul_left_cancel₀ this.ne' (h.symm.trans (by ring) : _ = (k + 1) * geomS k q)
      exact this
    by_cases hk1 : k = 1
    · exact Or.inr hk1
    · left
      have h1 : 1 ∈ range k := mem_range.mpr (by omega)
      have hle : ((1 : ℕ) : ℝ) * q ^ 1 ≤ ∑ j ∈ range k, (j : ℝ) * q ^ j :=
        single_le_sum (f := fun j : ℕ => (j : ℝ) * q ^ j)
          (fun j _ => by positivity) h1
      simp at hle
      linarith
  · rintro (rfl | rfl)
    · have : weightS k 0 = geomS k 0 := by
        have h0 : ∑ j ∈ range k, (j : ℝ) * (0 : ℝ) ^ j = 0 :=
          sum_eq_zero fun j _ => by rcases j with _ | j <;> simp
        linarith
      rw [this]
    · simp [weightS, geomS]

/-- The reflected sum: `2 ∑_{j<k} (k-1-2j) q^j = ∑_{j<k} (k-1-2j)(q^j - q^{k-1-j})`. -/
lemma reflect_sum (k : ℕ) (q : ℝ) :
    2 * ∑ j ∈ range k, ((k : ℝ) - 1 - 2 * j) * q ^ j
      = ∑ j ∈ range k, ((k : ℝ) - 1 - 2 * j) * (q ^ j - q ^ (k - 1 - j)) := by
  have hr : ∑ j ∈ range k, ((k : ℝ) - 1 - 2 * j) * q ^ j
      = ∑ j ∈ range k, -(((k : ℝ) - 1 - 2 * j) * q ^ (k - 1 - j)) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < k := mem_range.mp hj
    have : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this]
    ring
  rw [two_mul]
  nth_rewrite 2 [hr]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- `(k+1) ∑ q^j - 2 ∑ (j+1) q^j = ∑ (k-1-2j) q^j`. -/
lemma sum_diff (k : ℕ) (q : ℝ) :
    (k + 1) * geomS k q - 2 * weightS k q = ∑ j ∈ range k, ((k : ℝ) - 1 - 2 * j) * q ^ j := by
  unfold geomS weightS
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- Lemma 54: `a_{k,q} > 2` for `k ≥ 2`. -/
theorem two_lt_akq {k : ℕ} (hk : 2 ≤ k) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    2 < aKQ k q := by
  have hk1 : 1 ≤ k := by omega
  have hP := weightS_pos hk1 hq0
  rw [akq_eq hk1 hq0 hq1, aKQ', lt_div_iff₀ hP]
  suffices 0 < (k + 1) * geomS k q - 2 * weightS k q by linarith
  rw [sum_diff]
  suffices 0 < 2 * ∑ j ∈ range k, ((k : ℝ) - 1 - 2 * j) * q ^ j by linarith
  rw [reflect_sum]
  have hnn : ∀ j ∈ range k, 0 ≤ ((k : ℝ) - 1 - 2 * j) * (q ^ j - q ^ (k - 1 - j)) := by
    intro j hj
    have hj' : j < k := mem_range.mp hj
    rcases le_total j (k - 1 - j) with h | h
    · have h1 : 0 ≤ (k : ℝ) - 1 - 2 * j := by
        have : ((j + j : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at this
        linarith
      have h2 : 0 ≤ q ^ j - q ^ (k - 1 - j) := by
        have := pow_le_pow_of_le_one hq0 hq1.le h; linarith
      positivity
    · have h1 : (k : ℝ) - 1 - 2 * j ≤ 0 := by
        have : ((k - 1 : ℕ) : ℝ) ≤ ((j + j : ℕ) : ℝ) := by exact_mod_cast (by omega)
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at this
        linarith
      have h2 : q ^ j - q ^ (k - 1 - j) ≤ 0 := by
        have := pow_le_pow_of_le_one hq0 hq1.le h; linarith
      nlinarith
  have h0 : (0 : ℕ) ∈ range k := mem_range.mpr (by omega)
  have hpos : 0 < ((k : ℝ) - 1 - 2 * (0 : ℕ)) * (q ^ 0 - q ^ (k - 1 - 0)) := by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : q ^ (k - 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
    simp only [Nat.cast_zero, mul_zero, sub_zero, pow_zero, Nat.sub_zero]
    apply mul_pos <;> linarith
  exact hpos.trans_le (single_le_sum hnn h0)

/-! ### The level density of Lemma 55 -/

/-- The level density of Lemma 55 integrates to `1` on `[qλ, λ]`. -/
theorem frustum_density_integral {k : ℕ} (hk : 1 ≤ k) {q lam : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hlam : 0 < lam) :
    ∫ s in q * lam..lam, k * s ^ (k - 1) / ((1 - q ^ k) * lam ^ k) = 1 := by
  have hpk : q ^ k < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  have hden : (1 - q ^ k) * lam ^ k ≠ 0 := by
    have : 0 < 1 - q ^ k := by linarith
    positivity
  simp_rw [div_eq_mul_inv _ ((1 - q ^ k) * lam ^ k)]
  rw [integral_mul_const, integral_const_mul, integral_pow]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 1 + m - 1 + 1 = 1 + m by omega, mul_pow]
  field_simp
  rw [Nat.add_sub_cancel_left]
  push_cast
  ring

/-- Lemma 55: the level density has mean `μ_{k,q} λ`. -/
theorem frustum_density_mean {k : ℕ} (hk : 1 ≤ k) {q lam : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hlam : 0 < lam) :
    ∫ s in q * lam..lam, s * (k * s ^ (k - 1) / ((1 - q ^ k) * lam ^ k))
      = muKQ k q * lam := by
  have hpk : q ^ k < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  have h1 : 0 < 1 - q ^ k := by linarith
  have hden : (1 - q ^ k) * lam ^ k ≠ 0 := by positivity
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have : (fun s : ℝ =>
        s * ((1 + m : ℕ) * s ^ (1 + m - 1) / ((1 - q ^ (1 + m)) * lam ^ (1 + m))))
      = fun s => s ^ (1 + m) * (((1 + m : ℕ) : ℝ) / ((1 - q ^ (1 + m)) * lam ^ (1 + m))) := by
    funext s
    rw [show 1 + m - 1 = m by omega]
    ring
  rw [this, integral_mul_const, integral_pow, muKQ, mul_pow]
  field_simp
  ring

end Mixes
