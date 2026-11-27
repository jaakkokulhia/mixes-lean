import Mathlib

/-!
# The polygon with sides `λᵢ` (Lemma 49, `b:lem:polygon`)

Let `λ₁, …, λₙ ≥ 0`, not all zero, with `2 max λⱼ ≤ ∑ λⱼ`. Lemma 1 (`lem:arch`) chooses a largest
length `λₖ`, an order `j₁, …, j_{n-1}` of the other indices and `s` minimising
`|2(λ_{j₁} + ⋯ + λ_{jₛ}) - ∑_{j ≠ k} λⱼ|`, puts `G = {j₁, …, jₛ}`, `H` the rest, `S = ∑_G λⱼ`,
`T = ∑_H λⱼ`, and builds the triangle `E_k = (λₖ, 0, 0)`, `E_H = -(x, y, 0)`,
`E_G = (x - λₖ, y, 0)` with `x = (λₖ² + T² - S²)/(2λₖ)`, `y = (T² - x²)^{1/2}`.
Lemma 49 puts `vₖ = E_k`, `vⱼ = (λⱼ/S) E_G` on `G`, `vⱼ = (λⱼ/T) E_H` on `H` (read as `0` when
`S = 0` or `T = 0`; in Lean division by `0` gives `0`, which is exactly this reading), and
states that the `vⱼ` lie in `ℝ² × {0}`, have lengths `λⱼ` and sum `0`.

We reprove the pieces of Lemma 1 that are needed (the bound `|S - T| ≤ λₖ` for the minimising
`s`, and the triangle), independently of the formalisation of Lemma 1 itself.

Vectors of `ℝ³` are functions `Fin 3 → ℝ`, with the Euclidean length `len u = √(∑ uᵢ²)`.

Main results:
* `Mixes.PolygonL49.exists_near_zero`, `Mixes.PolygonL49.choice_bound`: `|S - T| ≤ λₖ`.
* `Mixes.PolygonL49.triangle`: the triangle `E_k, E_G, E_H`.
* `Mixes.PolygonL49.polygon_of_partition`: Lemma 49 for any partition with `|S - T| ≤ λₖ`.
* `Mixes.PolygonL49.lemma49`: Lemma 49 with the choice of Lemma 1.
-/

noncomputable section

namespace Mixes

namespace PolygonL49

open Finset

/-- The Euclidean length of a vector of `ℝ³`. -/
def len (u : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ i, u i ^ 2)

lemma len_smul (c : ℝ) (u : Fin 3 → ℝ) : len (c • u) = |c| * len u := by
  unfold len
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma eq_zero_of_len_eq_zero {u : Fin 3 → ℝ} (h : len u = 0) : u = 0 := by
  unfold len at h
  rw [Real.sqrt_eq_zero'] at h
  have h0 : ∑ i, u i ^ 2 = 0 := le_antisymm h (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h0
  funext i
  simpa using h0 i (Finset.mem_univ i)

/-! ### The choice of `s` in Lemma 1 -/

/-- A sequence that starts at most `0`, ends at least `0` and rises by at most `2d` per step
comes within `d` of `0`. -/
lemma exists_near_zero (p : ℕ → ℝ) {d : ℝ} (hd : 0 ≤ d) :
    ∀ m : ℕ, p 0 ≤ 0 → 0 ≤ p m → (∀ i < m, p (i + 1) ≤ p i + 2 * d) → ∃ i ≤ m, |p i| ≤ d := by
  intro m
  induction m with
  | zero =>
    intro h0 h1 _
    exact ⟨0, le_rfl, by rw [le_antisymm h0 h1, abs_zero]; exact hd⟩
  | succ m ih =>
    intro h0 h1 hstep
    by_cases hm : p (m + 1) ≤ d
    · exact ⟨m + 1, le_rfl, abs_le.2 ⟨by linarith, hm⟩⟩
    · have := hstep m (Nat.lt_succ_self m)
      by_cases hpm : 0 ≤ p m
      · obtain ⟨i, hi, hpi⟩ := ih h0 hpm (fun i hi => hstep i (by omega))
        exact ⟨i, by omega, hpi⟩
      · exact ⟨m, by omega, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- The choice of Lemma 1: if `l` lists the indices other than `k`, each at most `λₖ`, and `s`
minimises `|2 ∑_{take s} λ - ∑_l λ|`, then `|S - T| ≤ λₖ` for `S = ∑_{take s} λ` and
`T = ∑_{drop s} λ`. -/
theorem choice_bound {n : ℕ} (lam : Fin n → ℝ) (hnn : ∀ j, 0 ≤ lam j) (k : Fin n)
    (hk : ∀ j, lam j ≤ lam k) (l : List (Fin n)) (s : ℕ)
    (hmin : ∀ s' ≤ l.length, |2 * ((l.take s).map lam).sum - (l.map lam).sum| ≤
      |2 * ((l.take s').map lam).sum - (l.map lam).sum|) :
    |((l.take s).map lam).sum - ((l.drop s).map lam).sum| ≤ lam k := by
  set L := (l.map lam).sum
  have hL : 0 ≤ L := List.sum_nonneg (by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
    exact hnn j)
  have hsplit : ((l.take s).map lam).sum + ((l.drop s).map lam).sum = L := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  set p : ℕ → ℝ := fun i => 2 * ((l.take i).map lam).sum - L
  obtain ⟨i, hi, hpi⟩ := exists_near_zero p ((hnn k).trans (hk k)) l.length
    (by simp [p]; exact hL)
    (by simp only [p, List.take_length]; linarith)
    (by
      intro i hi
      simp only [p]
      rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hi)]
      simp only [List.getElem_map]
      linarith [hk l[i]])
  have := (hmin i hi).trans hpi
  calc |((l.take s).map lam).sum - ((l.drop s).map lam).sum|
      = |2 * ((l.take s).map lam).sum - L| := by congr 1; linarith
    _ ≤ lam k := this

/-! ### The triangle of Lemma 1 -/

/-- `x = (a² + T² - S²)/(2a)`. -/
def xco (a S T : ℝ) : ℝ := (a ^ 2 + T ^ 2 - S ^ 2) / (2 * a)

/-- `y = (T² - x²)^{1/2}`. -/
def yco (a S T : ℝ) : ℝ := Real.sqrt (T ^ 2 - xco a S T ^ 2)

/-- `E_k = (a, 0, 0)`. -/
def Ek (a : ℝ) : Fin 3 → ℝ := ![a, 0, 0]

/-- `E_G = (x - a, y, 0)`. -/
def EG (a S T : ℝ) : Fin 3 → ℝ := ![xco a S T - a, yco a S T, 0]

/-- `E_H = -(x, y, 0)`. -/
def EH (a S T : ℝ) : Fin 3 → ℝ := ![-xco a S T, -yco a S T, 0]

/-- The triangle of Lemma 1: for `a > 0`, `S, T ≥ 0` with `|S - T| ≤ a ≤ S + T`, the vectors
`E_k, E_G, E_H` have third coordinate `0`, lengths `a, S, T`, and sum `0`. -/
theorem triangle {a S T : ℝ} (ha : 0 < a) (hS : 0 ≤ S) (hT : 0 ≤ T) (h1 : |S - T| ≤ a)
    (h2 : a ≤ S + T) :
    Ek a 2 = 0 ∧ EG a S T 2 = 0 ∧ EH a S T 2 = 0 ∧
      len (Ek a) = a ∧ len (EG a S T) = S ∧ len (EH a S T) = T ∧
      Ek a + EG a S T + EH a S T = 0 := by
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  have hkey : T ^ 2 - xco a S T ^ 2 =
      ((S - a + T) * (S + a - T)) * ((a + T - S) * (a + T + S)) / (2 * a) ^ 2 := by
    unfold xco; field_simp; ring
  have hy : 0 ≤ T ^ 2 - xco a S T ^ 2 := by
    rw [hkey]
    refine div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) (mul_nonneg ?_ ?_)) (sq_nonneg _) <;>
      linarith
  have hy2 : yco a S T ^ 2 = T ^ 2 - xco a S T ^ 2 := Real.sq_sqrt hy
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [len, Ek, Fin.sum_univ_three, Real.sqrt_sq ha.le]
  · have : ∑ i, EG a S T i ^ 2 = S ^ 2 := by
      simp only [EG, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hy2]
      unfold xco; field_simp; ring
    rw [len, this, Real.sqrt_sq hS]
  · have : ∑ i, EH a S T i ^ 2 = T ^ 2 := by
      simp only [EH, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [neg_sq, neg_sq, hy2]; ring
    rw [len, this, Real.sqrt_sq hT]
  · funext i
    fin_cases i <;> simp [Ek, EG, EH]

/-! ### Lemma 49 -/

/-- The vectors of Lemma 49: `vₖ = E_k`, `vⱼ = (λⱼ/S) E_G` on `G`, `vⱼ = (λⱼ/T) E_H` otherwise. -/
def vecs {n : ℕ} (lam : Fin n → ℝ) (k : Fin n) (G H : Finset (Fin n)) (j : Fin n) :
    Fin 3 → ℝ :=
  let S := ∑ i ∈ G, lam i
  let T := ∑ i ∈ H, lam i
  if j = k then Ek (lam k)
  else if j ∈ G then (lam j / S) • EG (lam k) S T
  else (lam j / T) • EH (lam k) S T

/-- On a part with nonnegative entries and sum `P`, the scaled copies `(λⱼ/P) E` of a vector of
length `P` have lengths `λⱼ` and sum `E` (also when `P = 0`). -/
lemma part_facts {n : ℕ} (lam : Fin n → ℝ) (hnn : ∀ j, 0 ≤ lam j) (A : Finset (Fin n))
    (E : Fin 3 → ℝ) (hE : len E = ∑ i ∈ A, lam i) :
    (∀ j ∈ A, len ((lam j / ∑ i ∈ A, lam i) • E) = lam j) ∧
      ∑ j ∈ A, (lam j / ∑ i ∈ A, lam i) • E = E := by
  set P := ∑ i ∈ A, lam i
  by_cases hP : P = 0
  · have hz : ∀ j ∈ A, lam j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 hP
    have hE0 : E = 0 := eq_zero_of_len_eq_zero (hE.trans hP)
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hP, div_zero, zero_smul, hz j hj]; simp [len]
    · simp [hP, hE0]
  · refine ⟨fun j hj => ?_, ?_⟩
    · have hP0 : 0 < P := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hnn i) (Ne.symm hP)
      rw [len_smul, hE, abs_of_nonneg (div_nonneg (hnn j) hP0.le), div_mul_cancel₀ _ hP]
    · rw [← Finset.sum_smul, ← Finset.sum_div, div_self hP, one_smul]

/-- **Lemma 49** for a given partition: let `λ ≥ 0`, `λₖ > 0` with `2λₖ ≤ ∑ λⱼ`, and let `G, H`
partition the indices other than `k` with `|S - T| ≤ λₖ`. Then the vectors `vⱼ` lie in
`ℝ² × {0}`, have lengths `λⱼ`, and sum to `0`. -/
theorem polygon_of_partition {n : ℕ} (lam : Fin n → ℝ) (hnn : ∀ j, 0 ≤ lam j) (k : Fin n)
    (hpos : 0 < lam k) (hpoly : 2 * lam k ≤ ∑ j, lam j) (G H : Finset (Fin n))
    (hGH : Disjoint G H) (hcov : ∀ j, j ≠ k ↔ j ∈ G ∪ H)
    (hST : |∑ j ∈ G, lam j - ∑ j ∈ H, lam j| ≤ lam k) :
    (∀ j, vecs lam k G H j 2 = 0) ∧ (∀ j, len (vecs lam k G H j) = lam j) ∧
      ∑ j, vecs lam k G H j = 0 := by
  set S := ∑ j ∈ G, lam j with hSdef
  set T := ∑ j ∈ H, lam j with hTdef
  have hkGH : k ∉ G ∪ H := fun h => (hcov k).2 h rfl
  have huniv : (Finset.univ : Finset (Fin n)) = insert k (G ∪ H) := by
    ext j
    by_cases hj : j = k
    · simp [hj]
    · simp [hj, ← hcov j]
  have hsum : ∀ F : Fin n → ℝ, ∑ j, F j = F k + ∑ j ∈ G, F j + ∑ j ∈ H, F j := by
    intro F
    rw [huniv, Finset.sum_insert hkGH, Finset.sum_union hGH, add_assoc]
  have hSn : 0 ≤ S := Finset.sum_nonneg fun i _ => hnn i
  have hTn : 0 ≤ T := Finset.sum_nonneg fun i _ => hnn i
  have h2 : lam k ≤ S + T := by have := hsum lam; linarith
  obtain ⟨hk3, hG3, hH3, hlk, hlG, hlH, hsum0⟩ := triangle hpos hSn hTn hST h2
  obtain ⟨hGlen, hGsum⟩ := part_facts lam hnn G (EG (lam k) S T) hlG
  obtain ⟨hHlen, hHsum⟩ := part_facts lam hnn H (EH (lam k) S T) hlH
  have hGk : ∀ j ∈ G, j ≠ k := fun j hj => (hcov j).2 (Finset.mem_union_left _ hj)
  have hHk : ∀ j ∈ H, j ≠ k := fun j hj => (hcov j).2 (Finset.mem_union_right _ hj)
  have hHG : ∀ j ∈ H, j ∉ G := fun j hj hG => Finset.disjoint_left.1 hGH hG hj
  have vG : ∀ j ∈ G, vecs lam k G H j = (lam j / S) • EG (lam k) S T := fun j hj => by
    simp only [vecs, hGk j hj, hj, ite_false, ite_true]; rfl
  have vH : ∀ j ∈ H, vecs lam k G H j = (lam j / T) • EH (lam k) S T := fun j hj => by
    simp only [vecs, hHk j hj, hHG j hj, ite_false]; rfl
  have vk : vecs lam k G H k = Ek (lam k) := by simp [vecs]
  have hrest : ∀ j, j ≠ k → j ∈ G ∨ j ∈ H := fun j hj => Finset.mem_union.1 ((hcov j).1 hj)
  refine ⟨fun j => ?_, fun j => ?_, ?_⟩
  · by_cases hj : j = k
    · rw [hj, vk]; exact hk3
    · rcases hrest j hj with hG | hH
      · rw [vG j hG]; simp [hG3]
      · rw [vH j hH]; simp [hH3]
  · by_cases hj : j = k
    · rw [hj, vk]; exact hlk
    · rcases hrest j hj with hG | hH
      · rw [vG j hG]; exact hGlen j hG
      · rw [vH j hH]; exact hHlen j hH
  · have : ∀ F : Fin n → (Fin 3 → ℝ), ∑ j, F j = F k + ∑ j ∈ G, F j + ∑ j ∈ H, F j := by
      intro F
      rw [huniv, Finset.sum_insert hkGH, Finset.sum_union hGH, add_assoc]
    rw [this, vk, Finset.sum_congr rfl vG, Finset.sum_congr rfl vH, hGsum, hHsum, hsum0]

/-- **Lemma 49** (`b:lem:polygon`). Let `λ₁, …, λₙ ≥ 0`, not all zero, with
`2 max λⱼ ≤ ∑ λⱼ`. Let `λₖ` be a largest length, `l` a list of the other indices (each once),
and `s ≤ length l` minimising `|2(λ_{j₁} + ⋯ + λ_{jₛ}) - ∑_{j ≠ k} λⱼ|`; put `G = {j₁, …, jₛ}` and
`H` the rest, as in Lemma 1. Then the vectors `vₖ = E_k`, `vⱼ = (λⱼ/S) E_G` (`j ∈ G`),
`vⱼ = (λⱼ/T) E_H` (`j ∈ H`), with `0` when `S = 0` or `T = 0`, lie in `ℝ² × {0}`, have
lengths `λⱼ`, and sum to `0`. -/
theorem lemma49 {n : ℕ} (lam : Fin n → ℝ) (hnn : ∀ j, 0 ≤ lam j) (hne : ∃ j, lam j ≠ 0)
    (hpoly : ∀ i, 2 * lam i ≤ ∑ j, lam j) (k : Fin n) (hk : ∀ j, lam j ≤ lam k)
    (l : List (Fin n)) (hl : l.Nodup) (hmem : ∀ j, j ∈ l ↔ j ≠ k) (s : ℕ)
    (hmin : ∀ s' ≤ l.length, |2 * ((l.take s).map lam).sum - (l.map lam).sum| ≤
      |2 * ((l.take s').map lam).sum - (l.map lam).sum|) :
    let G := (l.take s).toFinset
    let H := (l.drop s).toFinset
    (∀ j, vecs lam k G H j 2 = 0) ∧ (∀ j, len (vecs lam k G H j) = lam j) ∧
      ∑ j, vecs lam k G H j = 0 := by
  intro G H
  obtain ⟨j0, hj0⟩ := hne
  have hpos : 0 < lam k := lt_of_lt_of_le (lt_of_le_of_ne (hnn j0) (Ne.symm hj0)) (hk j0)
  have hGs : ∑ j ∈ G, lam j = ((l.take s).map lam).sum :=
    List.sum_toFinset _ (hl.sublist (List.take_sublist s l))
  have hHs : ∑ j ∈ H, lam j = ((l.drop s).map lam).sum :=
    List.sum_toFinset _ (hl.sublist (List.drop_sublist s l))
  have hGH : Disjoint G H := by
    rw [Finset.disjoint_left]
    intro j hjG hjH
    exact List.disjoint_take_drop hl le_rfl (List.mem_toFinset.1 hjG) (List.mem_toFinset.1 hjH)
  have hcov : ∀ j, j ≠ k ↔ j ∈ G ∪ H := by
    intro j
    rw [← hmem j, Finset.mem_union, List.mem_toFinset, List.mem_toFinset, ← List.mem_append,
      List.take_append_drop]
  refine polygon_of_partition lam hnn k hpos (hpoly k) G H hGH hcov ?_
  rw [hGs, hHs]
  exact choice_bound lam hnn k hk l s hmin

end PolygonL49

end Mixes
