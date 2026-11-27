import Mixes.Defs

/-!
# Densities with two steps (Lemmas 4, 5, Theorem 6, Corollary 7)

Section "Densities with two steps" of the paper (`m:sec:two`).

## Representation

An admissible tuple is represented by a list of *blocks* `⟨c, l, r⟩`, meaning `c` copies of the
interval `[l, r]` (the paper's `c · I`). A mixture is a list of pairs `(w, τ)` of a weight and a
tuple. The density of `U[l, r]` (for `l < r`) is taken as `ud l r = (r - l)⁻¹ · 1_[l, r)`; the
half-open indicator makes all density identities hold at *every* point, not only almost
everywhere. The density `g a b` of the paper is `h₁` on `[0, a)`, `h₂` on `[a, b)` and `0`
elsewhere.

The algebraic statements are proved pointwise for these densities. The connection with the
measures of `Mixes.Defs` (`unifI`, `Admissible`, `Admissible.marginal`) is made at the
end of the file.

## Main results

* `split_ud`: Lemma 5. `recog`, `recog_measure`, `recog_mixture`: Lemma 4.
* `caseA`, `caseB`, `caseC`, `caseD`, `thm6_i`: Theorem 6 (i); `g_decomp`, `thm6_ii`: part (ii).
* `cor7`: Corollary 7.
* `thm6_measure`: the marginal `∑ wᵢ m_{τᵢ}` of at most three (two if `a ≤ 1`) `Admissible`
  tuples is the measure with density `g_{a,b}`; `completelyMixable_g`: granted Lemma 3 (stated
  as the hypothesis `Lemma3 n`), `g_{a,b}` is `n`-completely mixable.

## Differences from the paper

* In case (D) the condition `u₂ > (n-2) a` is not used: `S_D` also works in case (C).
* Lemma 5 is proved for `0 ≤ u ≤ b` (the paper: `0 < u < b`).
* Tuples of weight `0` stay in the lists; nothing is required of them.
-/

open MeasureTheory

noncomputable section

namespace Mixes

namespace TwoStep

/-! ### Densities -/

/-- The density of `U[l, r]`, `(r - l)⁻¹` on `[l, r)` (it is `0` everywhere if `r ≤ l`). -/
def ud (l r x : ℝ) : ℝ := if l ≤ x ∧ x < r then (r - l)⁻¹ else 0

/-- `h₁ = (a + b - 2)/(a b)`. -/
def h1 (a b : ℝ) : ℝ := (a + b - 2) / (a * b)

/-- `h₂ = (2 - a)/(b (b - a))`. -/
def h2 (a b : ℝ) : ℝ := (2 - a) / (b * (b - a))

/-- The two-step density `g_{a,b}`: `h₁` on `[0, a)`, `h₂` on `[a, b)`, `0` elsewhere. -/
def g (a b x : ℝ) : ℝ := if 0 ≤ x ∧ x < a then h1 a b else if a ≤ x ∧ x < b then h2 a b else 0

lemma ud_nonneg (l r x : ℝ) : 0 ≤ ud l r x := by
  unfold ud; split_ifs with h
  · exact inv_nonneg.mpr (by linarith [h.1, h.2])
  · rfl

lemma h1_sub_h2 {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : 0 < b) :
    h1 a b - h2 a b = (b - 2) / (a * (b - a)) := by
  unfold h1 h2
  have : b - a ≠ 0 := by linarith
  field_simp; ring

/-- Case analysis for pointwise identities between the step functions `ud`, `g`: split all the
`if`s, turn the negated conditions into disjunctions, split them, and close each case by `linarith`
(contradictory case) or by `field_simp; ring`. -/
macro "ud_tac" : tactic => `(tactic| (split_ifs <;>
  (try simp only [not_and_or, not_le, not_lt] at *) <;> casesm* _ ∨ _, _ ∧ _ <;>
  first | (exfalso; linarith) | (field_simp; ring) | ring))

/-- `g_{a,b} = h₁ a · ud 0 a + h₂ (b - a) · ud a b`. -/
lemma g_eq_ud {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : ℝ) :
    g a b x = h1 a b * a * ud 0 a x + h2 a b * (b - a) * ud a b x := by
  have hba : b - a ≠ 0 := by linarith
  have ha' : a ≠ 0 := ha.ne'
  unfold g ud; ud_tac

/-- **Lemma 5** (`m:lem:split`), for densities and pointwise: for `0 ≤ u ≤ b` with `0 < b`,
`(u/b) U[0,u] + (1 - u/b) U[u,b] = U[0,b]`. (The paper assumes `0 < u < b`; at `u = 0` and
`u = b` the term of weight `0` has density `0`, so the identity still holds.) -/
lemma split_ud {u b : ℝ} (hu0 : 0 ≤ u) (hub : u ≤ b) (hb : 0 < b) (x : ℝ) :
    u / b * ud 0 u x + (1 - u / b) * ud u b x = ud 0 b x := by
  unfold ud
  by_cases h1 : 0 ≤ x ∧ x < u
  · have hu : u ≠ 0 := by linarith [h1.1, h1.2]
    rw [ite_eq_left h1, ite_eq_right (by intro h; linarith [h.1, h1.2]),
      ite_eq_left ⟨h1.1, by linarith [h1.2]⟩]
    field_simp; ring
  · by_cases h2 : u ≤ x ∧ x < b
    · have hu : b - u ≠ 0 := by linarith [h2.1, h2.2]
      rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left ⟨by linarith [h2.1], h2.2⟩]
      field_simp; ring
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right]
      · ring
      · rintro ⟨hx0, hxb⟩
        rcases le_or_gt u x with h | h
        · exact h2 ⟨h, hxb⟩
        · exact h1 ⟨hx0, h⟩

/-! ### Tuples and mixtures -/

/-- A block `⟨c, l, r⟩`: `c` copies of the interval `[l, r]` (the paper's `c · [l, r]`). -/
structure Block where
  /-- the multiplicity -/
  c : ℕ
  /-- the left end -/
  l : ℝ
  /-- the right end -/
  r : ℝ

/-- A tuple of intervals, given by blocks. -/
abbrev Tup := List Block

namespace Tup

/-- The number of intervals. -/
def size (t : Tup) : ℕ := (t.map Block.c).sum

/-- The sum of the lengths. -/
def lenSum (t : Tup) : ℝ := (t.map fun B => (B.c : ℝ) * (B.r - B.l)).sum

/-- The sum of `l + r` over the intervals (twice the sum of the midpoints). -/
def midSum (t : Tup) : ℝ := (t.map fun B => (B.c : ℝ) * (B.l + B.r)).sum

/-- `∑ⱼ` (density of `U(Iⱼ)`), that is `n` times the density of the marginal `m_τ`. -/
def dens (t : Tup) (x : ℝ) : ℝ := (t.map fun B => (B.c : ℝ) * ud B.l B.r x).sum

/-- Definition 2 for block tuples: `n` intervals `[l, r]` with `l ≤ r`, not all of length `0`,
the polygon inequality, and midpoints adding up to `n`. -/
structure Adm (n : ℕ) (t : Tup) : Prop where
  size : t.size = n
  le : ∀ B ∈ t, B.l ≤ B.r
  pos : ∃ B ∈ t, 0 < B.c ∧ B.l < B.r
  polygon : ∀ B ∈ t, 0 < B.c → 2 * (B.r - B.l) ≤ t.lenSum
  mid : t.midSum = 2 * n

/-- All intervals are nondegenerate (`l < r`, no point masses) and lie in `[0, b]`. -/
def Inside (b : ℝ) (t : Tup) : Prop := ∀ B ∈ t, 0 ≤ B.l ∧ B.l < B.r ∧ B.r ≤ b

end Tup

/-- A mixture `∑ᵢ wᵢ τᵢ`, a list of pairs (weight, tuple). -/
abbrev Mix := List (ℝ × Tup)

/-- The density of the marginal `∑ᵢ wᵢ m_{τᵢ}` of a mixture of `n`-tuples. -/
def Mix.dens (n : ℕ) (M : Mix) (x : ℝ) : ℝ := (M.map fun p => p.1 * p.2.dens x).sum / n

/-- A well defined mixture: weights `≥ 0` with sum `1`, and the tuples of positive weight are
admissible `n`-tuples of intervals in `[0, b]`. -/
structure Mix.Good (n : ℕ) (b : ℝ) (M : Mix) : Prop where
  nonneg : ∀ p ∈ M, 0 ≤ p.1
  sum_one : (M.map Prod.fst).sum = 1
  adm : ∀ p ∈ M, 0 < p.1 → p.2.Adm n ∧ p.2.Inside b

/-! ### The mixtures `S_β` and `S_D` -/

/-- `u_β = 2n - na - β(b - a)`. -/
def u (n : ℕ) (a b : ℝ) (β : ℕ) : ℝ := 2 * n - n * a - β * (b - a)

/-- `τ'_β = ((n-1-β)·[0,a], (β-1)·[0,b], [a,b], [0,u_β])`. -/
def tau1 (n : ℕ) (a b : ℝ) (β : ℕ) : Tup :=
  [⟨n - 1 - β, 0, a⟩, ⟨β - 1, 0, b⟩, ⟨1, a, b⟩, ⟨1, 0, u n a b β⟩]

/-- `τ''_β = ((n-β)·[0,a], (β-1)·[0,b], [u_β,b])`. -/
def tau2 (n : ℕ) (a b : ℝ) (β : ℕ) : Tup :=
  [⟨n - β, 0, a⟩, ⟨β - 1, 0, b⟩, ⟨1, u n a b β, b⟩]

/-- `S_β`: `τ'_β` with weight `u_β/b` and `τ''_β` with weight `1 - u_β/b` (a tuple of weight
`0` is kept in the list; `Mix.Good` asks nothing of it). -/
def S (n : ℕ) (a b : ℝ) (β : ℕ) : Mix :=
  [(u n a b β / b, tau1 n a b β), (1 - u n a b β / b, tau2 n a b β)]

/-- `ρ' = ((n-2)·[0,a], 2·[x,b])` with `x = u₂/2`. -/
def rho1 (n : ℕ) (a b : ℝ) : Tup := [⟨n - 2, 0, a⟩, ⟨2, u n a b 2 / 2, b⟩]

/-- `ρ'' = ((n-3)·[0,a], [0,x], [a,b], [x,b])` with `x = u₂/2`. -/
def rho2 (n : ℕ) (a b : ℝ) : Tup :=
  [⟨n - 3, 0, a⟩, ⟨1, 0, u n a b 2 / 2⟩, ⟨1, a, b⟩, ⟨1, u n a b 2 / 2, b⟩]

/-- `S_D`: `ρ'` with weight `1 - u₂/b` and `ρ''` with weight `u₂/b`. -/
def SD (n : ℕ) (a b : ℝ) : Mix := [(1 - u n a b 2 / b, rho1 n a b), (u n a b 2 / b, rho2 n a b)]

lemma cast_sub3 {n β : ℕ} (h : β + 1 ≤ n) : ((n - 1 - β : ℕ) : ℝ) = n - 1 - β := by
  have : n - 1 - β + β + 1 = n := by omega
  have : ((n - 1 - β : ℕ) : ℝ) + β + 1 = n := by exact_mod_cast this
  linarith

lemma cast_sub2 {n β : ℕ} (h : β ≤ n) : ((n - β : ℕ) : ℝ) = n - β := by
  rw [Nat.cast_sub h]

/-- The marginal of `S_β`, in the normal form `((n-β-w) U[0,a] + β U[0,b] + w U[a,b]) / n`. -/
lemma S_dens_nf {n β : ℕ} {a b : ℝ} (h1 : 1 ≤ β) (h2 : β + 1 ≤ n) (hb : 0 < b)
    (hu0 : 0 ≤ u n a b β) (hub : u n a b β ≤ b) (x : ℝ) :
    (S n a b β).dens n x = ((n - β - u n a b β / b) * ud 0 a x + β * ud 0 b x
      + u n a b β / b * ud a b x) / n := by
  have hs := split_ud hu0 hub hb x
  simp only [Mix.dens, S, Tup.dens, tau1, tau2, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, cast_sub3 h2, cast_sub2 (by omega : β ≤ n), cast_sub2 h1]
  rw [← hs]; push_cast; ring

/-- The marginal of `S_D` has the same normal form as that of `S_2`. -/
lemma SD_dens_nf {n : ℕ} {a b : ℝ} (h3 : 3 ≤ n) (hb : 0 < b)
    (hu0 : 0 ≤ u n a b 2) (hub : u n a b 2 ≤ 2 * b) (x : ℝ) :
    (SD n a b).dens n x = ((n - 2 - u n a b 2 / b) * ud 0 a x + 2 * ud 0 b x
      + u n a b 2 / b * ud a b x) / n := by
  have hs := split_ud (u := u n a b 2 / 2) (by linarith) (by linarith) hb x
  simp only [Mix.dens, SD, Tup.dens, rho1, rho2, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, cast_sub2 (by omega : 2 ≤ n), cast_sub2 (by omega : 3 ≤ n)]
  rw [← hs]; push_cast; ring

/-- The normal form is `g_{a,b}` (this is where Lemma 4 is used in the paper; here the
coefficients are computed directly). -/
lemma nf_eq_g {n β : ℕ} {a b : ℝ} (hn : 0 < n) (ha : 0 < a) (hab : a < b) (x : ℝ) :
    ((n - β - u n a b β / b) * ud 0 a x + β * ud 0 b x + u n a b β / b * ud a b x) / n
      = g a b x := by
  have hb : 0 < b := by linarith
  have hd := split_ud ha.le hab.le hb x
  rw [g_eq_ud ha hab x, ← hd]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hba : b - a ≠ 0 := by linarith
  unfold h1 h2 u
  field_simp
  ring

/-- The marginal density of `S_β` is `g_{a,b}` whenever `1 ≤ β ≤ n - 1` and `0 ≤ u_β ≤ b`. -/
theorem S_dens {n β : ℕ} {a b : ℝ} (h1 : 1 ≤ β) (h2 : β + 1 ≤ n) (ha : 0 < a) (hab : a < b)
    (hu0 : 0 ≤ u n a b β) (hub : u n a b β ≤ b) (x : ℝ) : (S n a b β).dens n x = g a b x := by
  rw [S_dens_nf h1 h2 (by linarith) hu0 hub, nf_eq_g (by omega) ha hab]

/-- The marginal density of `S_D` is `g_{a,b}` whenever `0 ≤ u₂ ≤ 2b`. -/
theorem SD_dens {n : ℕ} {a b : ℝ} (h3 : 3 ≤ n) (ha : 0 < a) (hab : a < b)
    (hu0 : 0 ≤ u n a b 2) (hub : u n a b 2 ≤ 2 * b) (x : ℝ) : (SD n a b).dens n x = g a b x := by
  rw [SD_dens_nf h3 (by linarith) hu0 hub]
  exact_mod_cast nf_eq_g (β := 2) (by omega) ha hab x

/-! ### Admissibility -/

/-- Simp set to evaluate sums and quantifiers over explicit block lists. -/
macro "blk_simp" : tactic => `(tactic| simp only [Tup.size, Tup.lenSum, Tup.midSum, Tup.Inside,
  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.forall_mem_cons,
  List.not_mem_nil, false_implies, implies_true, and_true])

lemma tau1_good {n β : ℕ} {a b : ℝ} (h1 : 1 ≤ β) (h2 : β + 1 ≤ n) (ha : 0 < a) (hab : a < b)
    (hu0 : 0 ≤ u n a b β) (hub : u n a b β ≤ b) (hup : 0 < u n a b β)
    (hpa : β + 1 < n → 2 * a ≤ ((n : ℝ) - 1 - β) * a + (β - 1) * b + (b - a) + u n a b β)
    (hpb : 1 < β → 2 * b ≤ ((n : ℝ) - 1 - β) * a + (β - 1) * b + (b - a) + u n a b β)
    (hpab : 2 * (b - a) ≤ ((n : ℝ) - 1 - β) * a + (β - 1) * b + (b - a) + u n a b β)
    (hpu : 2 * u n a b β ≤ ((n : ℝ) - 1 - β) * a + (β - 1) * b + (b - a) + u n a b β) :
    (tau1 n a b β).Adm n ∧ (tau1 n a b β).Inside b := by
  unfold tau1
  refine ⟨⟨?_, ?_, ⟨⟨1, a, b⟩, by simp, Nat.one_pos, hab⟩, ?_, ?_⟩, ?_⟩ <;> blk_simp
  · omega
  · exact ⟨ha.le, by linarith, hab.le, hu0⟩
  · simp only [cast_sub3 h2, cast_sub2 h1, Nat.cast_one]
    refine ⟨fun h => ?_, fun h => ?_, fun _ => ?_, fun _ => ?_⟩
    · have := hpa (by omega); linarith
    · have := hpb (by omega); linarith
    · linarith
    · linarith
  · simp only [cast_sub3 h2, cast_sub2 h1, Nat.cast_one]; unfold u; ring
  · exact ⟨⟨le_rfl, ha, by linarith⟩, ⟨le_rfl, by linarith, le_rfl⟩, ⟨ha.le, hab, le_rfl⟩,
      ⟨le_rfl, hup, hub⟩⟩

lemma tau2_good {n β : ℕ} {a b : ℝ} (h1 : 1 ≤ β) (h2 : β + 1 ≤ n) (ha : 0 < a) (hab : a < b)
    (hu0 : 0 ≤ u n a b β) (hub : u n a b β ≤ b) (hub' : u n a b β < b)
    (hpa : 2 * a ≤ ((n : ℝ) - β) * a + (β - 1) * b + (b - u n a b β))
    (hpb : 1 < β → 2 * b ≤ ((n : ℝ) - β) * a + (β - 1) * b + (b - u n a b β))
    (hpu : 2 * (b - u n a b β) ≤ ((n : ℝ) - β) * a + (β - 1) * b + (b - u n a b β)) :
    (tau2 n a b β).Adm n ∧ (tau2 n a b β).Inside b := by
  unfold tau2
  refine ⟨⟨?_, ?_, ⟨⟨n - β, 0, a⟩, by simp, (show 0 < n - β by omega), ha⟩, ?_, ?_⟩, ?_⟩ <;>
    blk_simp
  · omega
  · exact ⟨ha.le, by linarith, hub⟩
  · simp only [cast_sub2 (by omega : β ≤ n), cast_sub2 h1, Nat.cast_one]
    refine ⟨fun _ => ?_, fun h => ?_, fun _ => ?_⟩
    · linarith
    · have := hpb (by omega); linarith
    · linarith
  · simp only [cast_sub2 (by omega : β ≤ n), cast_sub2 h1, Nat.cast_one]; unfold u; ring
  · exact ⟨⟨le_rfl, ha, by linarith⟩, ⟨le_rfl, by linarith, le_rfl⟩, ⟨hu0, hub', le_rfl⟩⟩

lemma S_good {n β : ℕ} {a b : ℝ} (hb : 0 < b) (hu0 : 0 ≤ u n a b β) (hub : u n a b β ≤ b)
    (H1 : 0 < u n a b β → (tau1 n a b β).Adm n ∧ (tau1 n a b β).Inside b)
    (H2 : u n a b β < b → (tau2 n a b β).Adm n ∧ (tau2 n a b β).Inside b) :
    (S n a b β).Good n b := by
  have hw0 : 0 ≤ u n a b β / b := div_nonneg hu0 hb.le
  have hw1 : u n a b β / b ≤ 1 := (div_le_one hb).mpr hub
  refine ⟨?_, ?_, ?_⟩
  · simp only [S, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hw0, by linarith⟩
  · simp [S]
  · simp only [S, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨fun h => H1 ?_, fun h => H2 ?_⟩
    · exact (div_pos_iff_of_pos_right hb).mp h
    · by_contra hc
      have : u n a b β / b = 1 := by rw [div_eq_one_iff_eq hb.ne']; linarith
      have h' : 0 < 1 - u n a b β / b := h
      linarith

/-! ### The four cases of Theorem 6 (i) -/

section cases

variable {n : ℕ} {a b : ℝ}

/-- Facts used in all cases: `u₁ > 0`, `u_{n-1} < b`, `a < b - a`. -/
lemma u_one_pos (hn : 3 ≤ n) (ha1 : a ≤ 1) (hbn : b ≤ n) : 0 < u n a b 1 := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : ((n : ℝ) - 1) * a ≤ (n : ℝ) - 1 := by nlinarith
  unfold u; push_cast; linarith

lemma u_sub_succ (β : ℕ) : u n a b (β + 1) = u n a b β - (b - a) := by
  unfold u; push_cast; ring

/-- **Case (A)**: `S₁` when `u₁ ≤ b`. -/
theorem caseA (hn : 3 ≤ n) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb2 : 2 < b) (hbn : b ≤ n)
    (hA : u n a b 1 ≤ b) : (S n a b 1).Good n b ∧ ∀ x, (S n a b 1).dens n x = g a b x := by
  have hu1 := u_one_pos hn ha1 hbn
  have hab : a < b := by linarith
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hna : 0 ≤ ((n : ℝ) - 3) * a := mul_nonneg (by linarith) ha0.le
  refine ⟨S_good (by linarith) hu1.le hA (fun _ => ?_) (fun hq => ?_), S_dens le_rfl (by omega)
    ha0 hab hu1.le hA⟩
  · refine tau1_good le_rfl (by omega) ha0 hab hu1.le hA hu1 (fun _ => ?_) (fun h => absurd h
      (lt_irrefl 1)) ?_ ?_ <;> unfold u at * <;> push_cast at * <;> nlinarith
  · refine tau2_good le_rfl (by omega) ha0 hab hu1.le hA hq ?_ (fun h => absurd h (lt_irrefl 1))
      ?_ <;> unfold u at * <;> push_cast at * <;> nlinarith

/-- **Case (B)**: `S_β` for any `3 ≤ β ≤ n - 1` with `0 ≤ u_β ≤ b`; the paper takes
`β = β*`, the largest `β ∈ {3, …, n-1}` with `u_β ≥ 0`. -/
theorem caseB_gen {β : ℕ} (h3 : 3 ≤ β) (hβn : β + 1 ≤ n) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hb2 : 2 < b) (hu0 : 0 ≤ u n a b β) (hub : u n a b β ≤ b) :
    (S n a b β).Good n b ∧ ∀ x, (S n a b β).dens n x = g a b x := by
  have hab : a < b := by linarith
  have hβ : (3 : ℝ) ≤ β := by exact_mod_cast h3
  have hnβ : (β : ℝ) + 1 ≤ n := by exact_mod_cast hβn
  have hna : 0 ≤ ((n : ℝ) - 1 - β) * a := mul_nonneg (by linarith) ha0.le
  have hnb : 2 * b ≤ ((β : ℝ) - 1) * b := by nlinarith
  refine ⟨S_good (by linarith) hu0 hub (fun hp => ?_) (fun hq => ?_), S_dens (by omega) hβn
    ha0 hab hu0 hub⟩
  · exact tau1_good (by omega) hβn ha0 hab hu0 hub hp (fun _ => by linarith) (fun _ => by linarith)
      (by linarith) (by linarith)
  · have hna' : 0 ≤ ((n : ℝ) - β) * a := mul_nonneg (by linarith) ha0.le
    exact tau2_good (by omega) hβn ha0 hab hu0 hub hq (by linarith) (fun _ => by linarith)
      (by linarith)

/-- `β*`: the largest `β ≤ n - 1` with `u_β ≥ 0`. -/
def betaStar (n : ℕ) (a b : ℝ) : ℕ := Nat.findGreatest (fun β => 0 ≤ u n a b β) (n - 1)

/-- **Case (B)** as in the paper: `S_{β*}` when `u₁ > b`, `n ≥ 4` and `u₃ ≥ 0`. -/
theorem caseB (hn : 4 ≤ n) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb2 : 2 < b) (h3 : 0 ≤ u n a b 3) :
    3 ≤ betaStar n a b ∧ betaStar n a b + 1 ≤ n ∧
      (S n a b (betaStar n a b)).Good n b ∧
      ∀ x, (S n a b (betaStar n a b)).dens n x = g a b x := by
  have hab : a < b := by linarith
  set β := betaStar n a b with hβ'
  have hβdef : β = Nat.findGreatest (fun β => 0 ≤ u n a b β) (n - 1) := rfl
  have hge : 3 ≤ β := Nat.le_findGreatest (by omega) h3
  have hle : β ≤ n - 1 := Nat.findGreatest_le _
  have hu0 : 0 ≤ u n a b β := Nat.findGreatest_spec (P := fun β => 0 ≤ u n a b β)
    (m := 3) (by omega) h3
  have hub : u n a b β < b := by
    rcases Nat.lt_or_ge β (n - 1) with h | h
    · have hnot : ¬ 0 ≤ u n a b (β + 1) := Nat.findGreatest_is_greatest (k := β + 1)
        (by rw [← hβdef]; omega) (by omega)
      rw [u_sub_succ] at hnot; linarith
    · have hβ : β = n - 1 := le_antisymm hle h
      have hn' : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
      rw [hβ]; unfold u; rw [hn']
      nlinarith
  exact ⟨hge, by omega, caseB_gen hge (by omega) ha0 ha1 hb2 hu0 hub.le⟩

/-- In cases (C) and (D): `a < u₂ < b`. -/
lemma u_two_bounds (hn : 3 ≤ n) (ha0 : 0 < a) (hb2 : 2 < b) (hbn : b ≤ n)
    (h1 : b < u n a b 1) (h3 : n = 3 ∨ u n a b 3 < 0) : a < u n a b 2 ∧ u n a b 2 < b := by
  have e2 : u n a b 2 = u n a b 1 - (b - a) := u_sub_succ 1
  have e3 : u n a b 3 = u n a b 2 - (b - a) := u_sub_succ 2
  refine ⟨by linarith, ?_⟩
  rcases h3 with rfl | h3
  · unfold u; push_cast; linarith
  · linarith

/-- **Case (C)**: `S₂` when `u₁ > b`, `n = 3` or `u₃ < 0`, and `u₂ ≤ (n-2) a`. -/
theorem caseC (hn : 3 ≤ n) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb2 : 2 < b) (hbn : b ≤ n)
    (h1 : b < u n a b 1) (h3 : n = 3 ∨ u n a b 3 < 0) (hC : u n a b 2 ≤ ((n : ℝ) - 2) * a) :
    (S n a b 2).Good n b ∧ ∀ x, (S n a b 2).dens n x = g a b x := by
  obtain ⟨hl, hr⟩ := u_two_bounds hn ha0 hb2 hbn h1 h3
  have hab : a < b := by linarith
  have h3' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hna : 0 ≤ ((n : ℝ) - 3) * a := mul_nonneg (by linarith) ha0.le
  refine ⟨S_good (by linarith) (by linarith) hr.le (fun _ => ?_) (fun _ => ?_),
    S_dens (by omega) (by omega) ha0 hab (by linarith) hr.le⟩
  · exact tau1_good (by omega) (by omega) ha0 hab (by linarith) hr.le (by linarith)
      (fun _ => by push_cast; linarith) (fun _ => by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith)
  · exact tau2_good (by omega) (by omega) ha0 hab (by linarith) hr.le hr
      (by push_cast; linarith) (fun _ => by push_cast; linarith) (by push_cast; linarith)

/-- **Case (D)**: `S_D` when `u₁ > b`, `n = 3` or `u₃ < 0`, and `u₂ > (n-2) a`.
The condition `u₂ > (n-2) a` of case (D) is not needed: `S_D` is well defined, with admissible
tuples and marginal `g_{a,b}`, in case (C) as well. -/
theorem caseD (hn : 3 ≤ n) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb2 : 2 < b) (hbn : b ≤ n)
    (h1 : b < u n a b 1) (h3 : n = 3 ∨ u n a b 3 < 0) :
    (SD n a b).Good n b ∧ ∀ x, (SD n a b).dens n x = g a b x := by
  obtain ⟨hl, hr⟩ := u_two_bounds hn ha0 hb2 hbn h1 h3
  have hab : a < b := by linarith
  have h3' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hna : 0 ≤ ((n : ℝ) - 3) * a := mul_nonneg (by linarith) ha0.le
  have hb0 : 0 < b := by linarith
  refine ⟨⟨?_, ?_, ?_⟩, SD_dens hn ha0 hab (by linarith) (by linarith)⟩
  · simp only [SD, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨?_, div_nonneg (by linarith) hb0.le⟩
    have := (div_le_one hb0).mpr hr.le; linarith
  · simp [SD]
  · simp only [SD, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨fun _ => ⟨⟨?_, ?_, ⟨⟨n - 2, 0, a⟩, by simp [rho1], (show 0 < n - 2 by omega), ha0⟩,
        ?_, ?_⟩, ?_⟩,
      fun _ => ⟨⟨?_, ?_, ⟨⟨1, a, b⟩, by simp [rho2], Nat.one_pos, hab⟩, ?_, ?_⟩, ?_⟩⟩ <;>
      simp only [rho1, rho2] <;> blk_simp <;>
      (try simp only [cast_sub2 (by omega : 2 ≤ n), cast_sub2 (by omega : 3 ≤ n)]) <;>
      (try push_cast)
    · omega
    · exact ⟨ha0.le, by linarith⟩
    · exact ⟨fun _ => by nlinarith, fun _ => by linarith⟩
    · unfold u; push_cast; ring
    · (repeat' apply And.intro) <;> linarith
    · omega
    · exact ⟨ha0.le, by linarith, hab.le, by linarith⟩
    · refine ⟨fun _ => by nlinarith, fun _ => by nlinarith, fun _ => by nlinarith,
        fun _ => by nlinarith⟩
    · unfold u; push_cast; ring
    · (repeat' apply And.intro) <;> linarith

end cases

/-! ### Theorem 6 -/

/-- The mixture of Theorem 6 (i), chosen by the cases (A) to (D). -/
def mixI (n : ℕ) (a b : ℝ) : Mix :=
  if u n a b 1 ≤ b then S n a b 1
  else if 4 ≤ n ∧ 0 ≤ u n a b 3 then S n a b (betaStar n a b)
  else if u n a b 2 ≤ ((n : ℝ) - 2) * a then S n a b 2 else SD n a b

/-- **Theorem 6 (i)** (`m:thm:two`). Let `n ≥ 3`, `0 < a ≤ 1` and `2 < b ≤ n`. The mixture
`mixI n a b` given by the cases (A) to (D) is well defined (weights `≥ 0` with sum `1`), its
tuples of positive weight are admissible with intervals in `[0, b]`, it has two tuples, and its
marginal density is `g_{a,b}` (at every point, with the density conventions above). -/
theorem thm6_i {n : ℕ} {a b : ℝ} (hn : 3 ≤ n) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb2 : 2 < b)
    (hbn : b ≤ n) :
    (mixI n a b).Good n b ∧ (∀ x, (mixI n a b).dens n x = g a b x) ∧ (mixI n a b).length = 2 := by
  unfold mixI
  split_ifs with hA hB hC
  · exact ⟨(caseA hn ha0 ha1 hb2 hbn hA).1, (caseA hn ha0 ha1 hb2 hbn hA).2, rfl⟩
  · obtain ⟨-, -, h1, h2⟩ := caseB hB.1 ha0 ha1 hb2 hB.2
    exact ⟨h1, h2, rfl⟩
  all_goals
    have h1 : b < u n a b 1 := lt_of_not_ge hA
    have h3 : n = 3 ∨ u n a b 3 < 0 := by
      rcases Nat.lt_or_ge n 4 with h | h
      · left; omega
      · right; exact lt_of_not_ge fun h' => hB ⟨h, h'⟩
  · exact ⟨(caseC hn ha0 ha1 hb2 hbn h1 h3 hC).1, (caseC hn ha0 ha1 hb2 hbn h1 h3 hC).2, rfl⟩
  · exact ⟨(caseD hn ha0 ha1 hb2 hbn h1 h3).1, (caseD hn ha0 ha1 hb2 hbn h1 h3).2, rfl⟩

/-- For `n = 3` only the cases (A) and (D) occur: case (C) is impossible. -/
lemma not_caseC_three {a b : ℝ} (h1 : b < u 3 a b 1) : ¬ u 3 a b 2 ≤ ((3 : ℕ) - 2 : ℝ) * a := by
  have : u 3 a b 2 = u 3 a b 1 - (b - a) := u_sub_succ 1
  intro h; norm_num at h; linarith

/-- `θ = 2(a-1)(b-2)/(a(b-a))`. -/
def theta (a b : ℝ) : ℝ := 2 * (a - 1) * (b - 2) / (a * (b - a))

/-- The decomposition of part (ii): `g_{a,b} = θ U[2-a, a] + (1-θ) g_{2-a,b}`, with `0 < θ < 1`. -/
theorem g_decomp {a b : ℝ} (ha1 : 1 < a) (ha2 : a < 2) (hb2 : 2 < b) :
    0 < theta a b ∧ theta a b < 1 ∧
      ∀ x, g a b x = theta a b * ud (2 - a) a x + (1 - theta a b) * g (2 - a) b x := by
  have ha0 : 0 < a := by linarith
  have hba : 0 < b - a := by linarith
  have hpos : 0 < a * (b - a) := mul_pos ha0 hba
  refine ⟨div_pos (by nlinarith) hpos, (div_lt_one hpos).mpr (by nlinarith), fun x => ?_⟩
  have k1 : a ≠ 0 := ha0.ne'
  have k2 : b - a ≠ 0 := hba.ne'
  have k3 : b ≠ 0 := by linarith
  have k4 : 2 - a ≠ 0 := by linarith
  have k5 : b - (2 - a) ≠ 0 := by linarith
  have k6 : a - (2 - a) ≠ 0 := by linarith
  unfold g ud h1 h2 theta
  ud_tac

/-- The mixture of Theorem 6 (ii): the tuple `n · [2-a, a]` with weight `θ`, and the mixture of
part (i) for `g_{2-a,b}` with weight `1 - θ`. -/
def mixII (n : ℕ) (a b : ℝ) : Mix :=
  (theta a b, [⟨n, 2 - a, a⟩]) :: (mixI n (2 - a) b).map fun p => ((1 - theta a b) * p.1, p.2)

/-- **Theorem 6 (ii)** (`m:thm:two`). Let `n ≥ 3`, `1 < a < 2` and `2 < b ≤ n`. Then
`0 < θ < 1`, `g_{a,b} = θ U[2-a,a] + (1-θ) g_{2-a,b}`, and the mixture `mixII n a b` (three
tuples) is well defined, its tuples of positive weight are admissible with intervals in
`[0, b]`, and its marginal density is `g_{a,b}`. -/
theorem thm6_ii {n : ℕ} {a b : ℝ} (hn : 3 ≤ n) (ha1 : 1 < a) (ha2 : a < 2) (hb2 : 2 < b)
    (hbn : b ≤ n) :
    0 < theta a b ∧ theta a b < 1 ∧
      (∀ x, g a b x = theta a b * ud (2 - a) a x + (1 - theta a b) * g (2 - a) b x) ∧
      (mixII n a b).Good n b ∧ (∀ x, (mixII n a b).dens n x = g a b x) ∧
      (mixII n a b).length = 3 := by
  obtain ⟨ht0, ht1, hg⟩ := g_decomp ha1 ha2 hb2
  obtain ⟨⟨hnn, hsum, hadm⟩, hd, hlen⟩ :=
    thm6_i (a := 2 - a) hn (by linarith) (by linarith) hb2 hbn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨ht0, ht1, hg, ⟨?_, ?_, ?_⟩, fun x => ?_, by simp [mixII, hlen]⟩
  · simp only [mixII, List.forall_mem_cons, List.mem_map]
    refine ⟨ht0.le, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact mul_nonneg (by linarith) (hnn p hp)
  · simp only [mixII, List.map_cons, List.sum_cons, List.map_map]
    have e : (Prod.fst ∘ fun p : ℝ × Tup => ((1 - theta a b) * p.1, p.2))
        = fun p => (1 - theta a b) * p.1 := rfl
    rw [e, List.sum_map_mul_left, hsum]; ring
  · simp only [mixII, List.forall_mem_cons, List.mem_map]
    refine ⟨fun _ => ⟨⟨?_, ?_, ⟨⟨n, 2 - a, a⟩, by simp, (show 0 < n by omega), by linarith⟩,
      ?_, ?_⟩, ?_⟩, ?_⟩
    · simp [Tup.size]
    · blk_simp; linarith
    · blk_simp; intro _; nlinarith
    · blk_simp; ring
    · blk_simp; exact ⟨by linarith, by linarith, by linarith⟩
    · rintro _ ⟨p, hp, rfl⟩ hw
      exact hadm p hp (pos_of_mul_pos_right hw (by linarith))
  · have hdx := hd x
    simp only [Mix.dens] at hdx ⊢
    simp only [mixII, List.map_cons, List.sum_cons, List.map_map, Function.comp_def, Tup.dens,
      List.map_nil, List.sum_nil] at hdx ⊢
    rw [hg x]
    have e : (List.map (fun p : ℝ × Tup => (1 - theta a b) * p.1 * (List.map (fun B : Block =>
        (B.c : ℝ) * ud B.l B.r x) p.2).sum) (mixI n (2 - a) b)).sum
        = (1 - theta a b) * (List.map (fun p : ℝ × Tup => p.1 * (List.map (fun B : Block =>
        (B.c : ℝ) * ud B.l B.r x) p.2).sum) (mixI n (2 - a) b)).sum := by
      rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro p _; ring
    rw [e, ← hdx]
    field_simp
    ring

/-! ### Lemma 4 and the mass and mean of `g` -/

/-- `g_{a,b}` has mass `1` and mean `1`: `h₁ a + h₂ (b-a) = 1` and
`h₁ a²/2 + h₂ (b²-a²)/2 = 1`. -/
lemma g_mass_mean {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    h1 a b * a + h2 a b * (b - a) = 1 ∧
      h1 a b * a ^ 2 / 2 + h2 a b * (b ^ 2 - a ^ 2) / 2 = 1 := by
  have h1 : a ≠ 0 := ha.ne'
  have h2 : b - a ≠ 0 := by linarith
  have h3 : b ≠ 0 := by linarith
  unfold TwoStep.h1 TwoStep.h2
  constructor <;> field_simp <;> ring

/-- **Lemma 4** (`m:lem:recog`), in terms of the two values of the density: a density on
`[0, b]` equal to `c₁` on `(0, a)` and to `c₂` on `(a, b)` with mass `1` and mean `1` has
`c₁ = h₁` and `c₂ = h₂`, that is, it is `g_{a,b}`. (The measure form is `recog_measure`
below; the second statement of Lemma 4, on mixtures of admissible tuples, is used through the
explicit computations `S_dens` and `SD_dens`.) -/
theorem recog {a b c₁ c₂ : ℝ} (ha : 0 < a) (hab : a < b)
    (hmass : c₁ * a + c₂ * (b - a) = 1) (hmean : c₁ * a ^ 2 / 2 + c₂ * (b ^ 2 - a ^ 2) / 2 = 1) :
    c₁ = h1 a b ∧ c₂ = h2 a b := by
  have h1 : a ≠ 0 := ha.ne'
  have h2 : b - a ≠ 0 := by linarith
  have h3 : b ≠ 0 := by linarith
  unfold TwoStep.h1 TwoStep.h2
  constructor
  · rw [eq_div_iff (mul_ne_zero h1 h3)]; linear_combination (b + a) * hmass - 2 * hmean
  · rw [eq_div_iff (mul_ne_zero h3 h2)]; linear_combination 2 * hmean - a * hmass

/-! ### Corollary 7 -/

/-- The mixtures of Corollary 7 (`n = 3`). For `b ≥ 3 - a`, with `u = 6 - 2a - b`:
`([0,a],[a,b],[0,u])` with weight `u/b` and `([0,a],[0,a],[u,b])` with weight `1 - u/b`. For
`b < 3 - a`, with `x = 3 - b - a/2`: `([0,a],[x,b],[x,b])` with weight `1 - 2x/b` and
`([0,x],[a,b],[x,b])` with weight `2x/b`. -/
def mixCor (a b : ℝ) : Mix :=
  if 3 - a ≤ b then
    [((6 - 2 * a - b) / b, [⟨1, 0, a⟩, ⟨1, a, b⟩, ⟨1, 0, 6 - 2 * a - b⟩]),
     (1 - (6 - 2 * a - b) / b, [⟨2, 0, a⟩, ⟨1, 6 - 2 * a - b, b⟩])]
  else
    [(1 - 2 * (3 - b - a / 2) / b, [⟨1, 0, a⟩, ⟨2, 3 - b - a / 2, b⟩]),
     (2 * (3 - b - a / 2) / b, [⟨1, 0, 3 - b - a / 2⟩, ⟨1, a, b⟩, ⟨1, 3 - b - a / 2, b⟩])]

/-- **Corollary 7** (`m:cor:three`). Let `0 < a ≤ 1` and `2 < b ≤ 3`. The mixture `mixCor a b`
is well defined, its tuples of positive weight are admissible `3`-tuples of intervals in
`[0, b]`, and its marginal density is `g_{a,b}`. By Lemma 3 it gives a `3`-complete mix of
`g_{a,b}` (see `completelyMixable_of_lemma3`). -/
theorem cor7 {a b : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hb2 : 2 < b) (hb3 : b ≤ 3) :
    (mixCor a b).Good 3 b ∧ ∀ x, (mixCor a b).dens 3 x = g a b x := by
  have hab : a < b := by linarith
  have hb0 : 0 < b := by linarith
  unfold mixCor
  split_ifs with hc
  · set v := 6 - 2 * a - b with hv
    have hvu : v = u 3 a b 1 := by rw [hv]; unfold u; push_cast; ring
    have hv0 : 0 < v := by linarith
    have hvb : v ≤ b := by linarith
    have hvb' : 0 < 1 - v / b → v < b := fun hw => by
      by_contra h
      have : v / b = 1 := by rw [div_eq_one_iff_eq hb0.ne']; linarith
      linarith
    refine ⟨⟨?_, ?_, ?_⟩, fun x => ?_⟩
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨div_nonneg hv0.le hb0.le, by linarith [(div_le_one hb0).mpr hvb]⟩
    · simp
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨fun _ => ⟨⟨?_, ?_, ⟨⟨1, a, b⟩, by simp, Nat.one_pos, hab⟩, ?_, ?_⟩, ?_⟩,
        fun hw => ⟨⟨?_, ?_, ⟨⟨2, 0, a⟩, by simp, by norm_num, ha0⟩, ?_, ?_⟩, ?_⟩⟩ <;> blk_simp <;>
        (repeat' apply And.intro) <;> (try intro _) <;> push_cast <;>
        first | linarith | linarith [hvb' hw]
    · have hs := split_ud hv0.le hvb hb0 x
      have := nf_eq_g (n := 3) (β := 1) (by norm_num) ha0 hab x
      rw [← hvu] at this
      rw [← this, ← hs]
      simp only [Mix.dens, Tup.dens, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      push_cast; ring
  · set y := 3 - b - a / 2 with hy
    have hyu : 2 * y = u 3 a b 2 := by rw [hy]; unfold u; push_cast; ring
    have hy0 : a / 2 < y := by linarith
    have hyb : 2 * y < b := by linarith
    refine ⟨⟨?_, ?_, ?_⟩, fun x => ?_⟩
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨by linarith [(div_le_one hb0).mpr hyb.le], div_nonneg (by linarith) hb0.le⟩
    · simp
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨fun _ => ⟨⟨?_, ?_, ⟨⟨1, 0, a⟩, by simp, Nat.one_pos, ha0⟩, ?_, ?_⟩, ?_⟩,
        fun hw => ⟨⟨?_, ?_, ⟨⟨1, a, b⟩, by simp, Nat.one_pos, hab⟩, ?_, ?_⟩, ?_⟩⟩ <;> blk_simp <;>
        (repeat' apply And.intro) <;> (try intro _) <;> push_cast <;> linarith
    · have hs := split_ud (u := y) (by linarith) (by linarith) hb0 x
      have := nf_eq_g (n := 3) (β := 2) (by norm_num) ha0 hab x
      rw [← hyu] at this
      rw [← this]
      simp only [Mix.dens, Tup.dens, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hs' : 2 * y / b * ud 0 y x + (2 - 2 * y / b) * ud y b x = 2 * ud 0 b x := by
        rw [← hs]; ring
      push_cast
      linear_combination (1 / 3 : ℝ) * hs'

/-! ### Measures

The density statements are now turned into statements about the measures of
`Mixes.Defs`: `unifI l r` has density `ud l r` (for `l < r`), a block tuple gives an
`Admissible` tuple whose `marginal` is `n⁻¹ ∑ c • unifI l r`, and the marginal of each mixture of
Theorem 6 is the measure with density `g_{a,b}`. -/

lemma ud_eq_indicator (l r : ℝ) : ud l r = Set.indicator (Set.Ico l r) (fun _ => (r - l)⁻¹) := by
  funext x; simp only [ud, Set.indicator, Set.mem_Ico]

lemma measurable_ud (l r : ℝ) : Measurable (ud l r) := by
  rw [ud_eq_indicator]; exact measurable_const.indicator measurableSet_Ico

/-- For `l < r`, `U[l, r]` is the measure with density `ud l r`. -/
lemma unifI_eq_withDensity {l r : ℝ} (h : l < r) :
    unifI l r = volume.withDensity (fun x => ENNReal.ofReal (ud l r x)) := by
  have e : (fun x => ENNReal.ofReal (ud l r x))
      = (Set.Ico l r).indicator (fun _ => ENNReal.ofReal (r - l)⁻¹) := by
    funext x; simp only [ud, Set.indicator, Set.mem_Ico]; split_ifs <;> simp
  rw [e, withDensity_indicator measurableSet_Ico, withDensity_const,
    Measure.restrict_congr_set Ico_ae_eq_Icc, unifI, ite_eq_left h,
    ENNReal.ofReal_inv_of_pos (by linarith)]

namespace Tup

/-- `∑ⱼ U(Iⱼ)`, that is `n` times the marginal `m_τ`. -/
def measure (t : Tup) : Measure ℝ := (t.map fun B => B.c • unifI B.l B.r).sum

lemma dens_cons (B : Block) (t : Tup) (x : ℝ) :
    dens (B :: t) x = B.c * ud B.l B.r x + dens t x := by
  simp [dens]

lemma dens_nonneg (t : Tup) (x : ℝ) : 0 ≤ t.dens x := by
  induction t with
  | nil => simp [Tup.dens]
  | cons B t ih =>
    rw [dens_cons]; exact add_nonneg (mul_nonneg (by positivity) (ud_nonneg _ _ _)) ih

lemma measurable_dens (t : Tup) : Measurable t.dens := by
  induction t with
  | nil =>
    have : dens [] = fun _ => 0 := by funext x; simp [Tup.dens]
    rw [this]; exact measurable_const
  | cons B t ih =>
    have : dens (B :: t) = fun x => B.c * ud B.l B.r x + dens t x := funext (dens_cons B t)
    rw [this]; exact (measurable_const.mul (measurable_ud _ _)).add ih

/-- A tuple of nondegenerate intervals: `∑ⱼ U(Iⱼ)` has density `dens`. -/
lemma measure_eq (t : Tup) (h : ∀ B ∈ t, B.l < B.r) :
    t.measure = volume.withDensity (fun x => ENNReal.ofReal (t.dens x)) := by
  induction t with
  | nil => simp [measure, dens]
  | cons B t ih =>
    have hB := h B List.mem_cons_self
    have ht := ih fun B' hB' => h B' (List.mem_cons_of_mem _ hB')
    have e : (fun x => ENNReal.ofReal (dens (B :: t) x))
        = (B.c : ENNReal) • (fun x => ENNReal.ofReal (ud B.l B.r x))
          + fun x => ENNReal.ofReal (dens t x) := by
      funext x
      rw [dens_cons, ENNReal.ofReal_add (mul_nonneg (by positivity) (ud_nonneg _ _ _))
        (dens_nonneg _ _), ENNReal.ofReal_mul (by positivity)]
      simp
    simp only [measure, List.map_cons, List.sum_cons] at ht ⊢
    rw [ht, e, withDensity_add_left ((measurable_ud _ _).ennreal_ofReal.const_smul _),
      withDensity_smul _ (measurable_ud _ _).ennreal_ofReal, unifI_eq_withDensity hB,
      Nat.cast_smul_eq_nsmul]

/-- The list of the `n` intervals of a block tuple. -/
def expand (t : Tup) : List (ℝ × ℝ) := t.flatMap fun B => List.replicate B.c (B.l, B.r)

lemma sum_expand {M : Type*} [AddCommMonoid M] (f : ℝ × ℝ → M) (t : Tup) :
    (t.expand.map f).sum = (t.map fun B => B.c • f (B.l, B.r)).sum := by
  induction t with
  | nil => simp [expand]
  | cons B t ih =>
    simp only [expand, List.flatMap_cons, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

lemma length_expand (t : Tup) : t.expand.length = t.size := by
  have := sum_expand (fun _ => (1 : ℕ)) t
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at this
  rw [this]; rfl

lemma sum_fin_expand {M : Type*} [AddCommMonoid M] {n : ℕ} (t : Tup) (h : t.expand.length = n)
    (f : ℝ × ℝ → M) : ∑ j : Fin n, f (t.expand.get (j.cast h.symm)) = (t.expand.map f).sum := by
  subst h
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get (by simp)
  intro i h1 h2
  simp

lemma mem_expand {t : Tup} {p : ℝ × ℝ} : p ∈ t.expand ↔ ∃ B ∈ t, 0 < B.c ∧ p = (B.l, B.r) := by
  simp only [expand, List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨B, hB, hc, rfl⟩; exact ⟨B, hB, Nat.pos_of_ne_zero hc, rfl⟩
  · rintro ⟨B, hB, hc, rfl⟩; exact ⟨B, hB, hc.ne', rfl⟩

/-- An admissible block tuple as an `Admissible` tuple of Definition 2 (`Mixes.Defs`). -/
def toAdmissible {n : ℕ} (t : Tup) (h : t.Adm n) : Admissible n where
  l j := (t.expand.get (j.cast (by rw [length_expand, h.size]))).1
  r j := (t.expand.get (j.cast (by rw [length_expand, h.size]))).2
  le j := by
    obtain ⟨B, hB, -, he⟩ := mem_expand.mp (List.get_mem _ _)
    rw [he]; exact h.le B hB
  pos := by
    obtain ⟨B, hB, hc, hlt⟩ := h.pos
    have hm : (B.l, B.r) ∈ t.expand := mem_expand.mpr ⟨B, hB, hc, rfl⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hm
    refine ⟨i.cast (by rw [length_expand, h.size]), ?_⟩
    simp only [Fin.cast_cast, Fin.cast_eq_self, hi]; exact hlt
  polygon k := by
    have hs := sum_fin_expand t (by rw [length_expand, h.size]) (fun p => p.2 - p.1)
    rw [hs, sum_expand]
    obtain ⟨B, hB, hc, he⟩ := mem_expand.mp (List.get_mem t.expand
      (k.cast (by rw [length_expand, h.size])))
    rw [he]
    simpa [lenSum, nsmul_eq_mul] using h.polygon B hB hc
  mid := by
    have hs := sum_fin_expand t (by rw [length_expand, h.size]) (fun p => p.1 + p.2)
    rw [hs, sum_expand, ← h.mid, midSum]
    congr 1; apply List.map_congr_left; intro B _; rw [nsmul_eq_mul]

/-- The marginal of `toAdmissible` is `n⁻¹ ∑ c • U[l, r]`. -/
lemma marginal_toAdmissible {n : ℕ} (t : Tup) (h : t.Adm n) :
    (t.toAdmissible h).marginal = (n : ENNReal)⁻¹ • t.measure := by
  unfold Admissible.marginal
  congr 1
  have hs := sum_fin_expand t (by rw [length_expand, h.size]) (fun p => unifI p.1 p.2)
  exact hs.trans (sum_expand _ t)

end Tup

/-- `∑ᵢ wᵢ ∑ⱼ U(I_{ij})`, that is `n` times the marginal of the mixture. -/
def Mix.measure0 (M : Mix) : Measure ℝ := (M.map fun p => ENNReal.ofReal p.1 • p.2.measure).sum

lemma Mix.measure0_eq (M : Mix) (hw : ∀ p ∈ M, 0 ≤ p.1)
    (hnd : ∀ p ∈ M, 0 < p.1 → ∀ B ∈ p.2, B.l < B.r) :
    M.measure0 = volume.withDensity
      (fun x => ENNReal.ofReal ((M.map fun p => p.1 * p.2.dens x).sum)) := by
  induction M with
  | nil => simp [Mix.measure0]
  | cons p M ih =>
    have ht := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      (fun q hq => hnd q (List.mem_cons_of_mem _ hq))
    have hp0 := hw p List.mem_cons_self
    have hrest : ∀ x, 0 ≤ (M.map fun p => p.1 * p.2.dens x).sum := fun x =>
      List.sum_nonneg (by
        simp only [List.mem_map]
        rintro _ ⟨q, hq, rfl⟩
        exact mul_nonneg (hw q (List.mem_cons_of_mem _ hq)) (Tup.dens_nonneg _ _))
    simp only [Mix.measure0, List.map_cons, List.sum_cons] at ht ⊢
    rw [ht]
    rcases hp0.lt_or_eq with hp | hp
    · have e : (fun x => ENNReal.ofReal (p.1 * p.2.dens x + (M.map fun p => p.1 * p.2.dens x).sum))
          = ENNReal.ofReal p.1 • (fun x => ENNReal.ofReal (p.2.dens x))
            + fun x => ENNReal.ofReal ((M.map fun p => p.1 * p.2.dens x).sum) := by
        funext x
        rw [ENNReal.ofReal_add (mul_nonneg hp0 (Tup.dens_nonneg _ _)) (hrest x),
          ENNReal.ofReal_mul hp0]
        simp
      rw [e, withDensity_add_left ((Tup.measurable_dens _).ennreal_ofReal.const_smul _),
        withDensity_smul _ (Tup.measurable_dens _).ennreal_ofReal,
        Tup.measure_eq _ (hnd p List.mem_cons_self hp)]
    · rw [← hp]; simp

/-- From a mixture of block tuples to a list of weighted `Admissible` tuples (the tuples of
weight `0` are dropped), with the same marginal. -/
lemma Mix.toAdmissibleList {n : ℕ} (M : Mix) (hw : ∀ p ∈ M, 0 ≤ p.1)
    (hadm : ∀ p ∈ M, 0 < p.1 → p.2.Adm n) :
    ∃ L : List (ENNReal × Admissible n), L.length ≤ M.length ∧
      (L.map Prod.fst).sum = ENNReal.ofReal (M.map Prod.fst).sum ∧
      (L.map fun q => q.1 • q.2.marginal).sum = (n : ENNReal)⁻¹ • M.measure0 := by
  induction M with
  | nil => exact ⟨[], by simp, by simp, by simp [Mix.measure0]⟩
  | cons p M ih =>
    obtain ⟨L, hlen, hsum, hmarg⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      (fun q hq => hadm q (List.mem_cons_of_mem _ hq))
    have hp0 := hw p List.mem_cons_self
    have hrest : 0 ≤ (M.map Prod.fst).sum := List.sum_nonneg (by
      simp only [List.mem_map]
      rintro _ ⟨q, hq, rfl⟩
      exact hw q (List.mem_cons_of_mem _ hq))
    rcases hp0.lt_or_eq with hp | hp
    · refine ⟨(ENNReal.ofReal p.1, p.2.toAdmissible (hadm p List.mem_cons_self hp)) :: L,
        by simp [hlen], ?_, ?_⟩
      · simp [hsum, ENNReal.ofReal_add hp0 hrest]
      · simp only [List.map_cons, List.sum_cons, hmarg, Tup.marginal_toAdmissible, Mix.measure0,
          smul_add]
        rw [smul_comm]
    · refine ⟨L, by simp; omega, ?_, ?_⟩
      · simp [hsum, ← hp]
      · simp [hmarg, Mix.measure0, ← hp]

lemma Mix.measurable_sum (M : Mix) : Measurable fun x => (M.map fun p => p.1 * p.2.dens x).sum := by
  induction M with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons p M ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (measurable_const.mul (Tup.measurable_dens _)).add ih

/-- A good mixture whose marginal density is `f` gives at most `M.length` weighted admissible
tuples (Definition 2) whose mixed marginal `∑ wᵢ m_{τᵢ}` is the measure with density `f`. -/
theorem Mix.Good.exists_admissible {n : ℕ} {b : ℝ} {M : Mix} (hn : 0 < n) (hM : M.Good n b)
    {f : ℝ → ℝ} (hf : ∀ x, M.dens n x = f x) :
    ∃ L : List (ENNReal × Admissible n), L.length ≤ M.length ∧ (L.map Prod.fst).sum = 1 ∧
      (L.map fun q => q.1 • q.2.marginal).sum =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨L, hlen, hsum, hmarg⟩ := M.toAdmissibleList hM.nonneg (fun p hp h => (hM.adm p hp h).1)
  refine ⟨L, hlen, by simp [hsum, hM.sum_one], ?_⟩
  rw [hmarg, Mix.measure0_eq M hM.nonneg (fun p hp h B hB => (((hM.adm p hp h).2) B hB).2.1)]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (fun x => ENNReal.ofReal (f x)) = (n : ENNReal)⁻¹ •
      fun x => ENNReal.ofReal ((M.map fun p => p.1 * p.2.dens x).sum) := by
    funext x
    rw [← hf x, Mix.dens, ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_natCast]
    simp [div_eq_mul_inv, mul_comm]
  rw [e, withDensity_smul _ (Mix.measurable_sum M).ennreal_ofReal]

/-- **Theorem 6, measure form.** Let `n ≥ 3` and `0 < a < 2 < b ≤ n`. There are at most three
admissible tuples (at most two if `a ≤ 1`) and weights with sum `1` such that the marginal of the
mixture, `∑ wᵢ m_{τᵢ}`, is the distribution with density `g_{a,b}`. -/
theorem thm6_measure {n : ℕ} {a b : ℝ} (hn : 3 ≤ n) (ha0 : 0 < a) (ha2 : a < 2) (hb2 : 2 < b)
    (hbn : b ≤ n) :
    ∃ L : List (ENNReal × Admissible n), L.length ≤ (if a ≤ 1 then 2 else 3) ∧
      (L.map Prod.fst).sum = 1 ∧
      (L.map fun q => q.1 • q.2.marginal).sum =
        volume.withDensity (fun x => ENNReal.ofReal (g a b x)) := by
  split_ifs with ha1
  · obtain ⟨hG, hd, hlen⟩ := thm6_i hn ha0 ha1 hb2 hbn
    obtain ⟨L, h1, h2, h3⟩ := hG.exists_admissible (by omega) hd
    exact ⟨L, hlen ▸ h1, h2, h3⟩
  · obtain ⟨-, -, -, hG, hd, hlen⟩ := thm6_ii hn (lt_of_not_ge ha1) ha2 hb2 hbn
    obtain ⟨L, h1, h2, h3⟩ := hG.exists_admissible (by omega) hd
    exact ⟨L, hlen ▸ h1, h2, h3⟩

/-! ### Lemma 4 in measure form -/

/-- The step function equal to `c₁` on `[0, a)`, to `c₂` on `[a, b)` and to `0` elsewhere
(`g a b` is `step a b (h1 a b) (h2 a b)`). -/
def step (a b c₁ c₂ x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < a then c₁ else if a ≤ x ∧ x < b then c₂ else 0

lemma g_eq_step (a b : ℝ) : g a b = step a b (h1 a b) (h2 a b) := rfl

lemma step_eq_ud {a b c₁ c₂ : ℝ} (ha : 0 < a) (hab : a < b) (x : ℝ) :
    step a b c₁ c₂ x = c₁ * a * ud 0 a x + c₂ * (b - a) * ud a b x := by
  have hba : b - a ≠ 0 := by linarith
  have ha' : a ≠ 0 := ha.ne'
  unfold step ud; ud_tac

lemma integral_id_unifI {l r : ℝ} (h : l < r) : ∫ x, x ∂(unifI l r) = (l + r) / 2 := by
  rw [unifI, ite_eq_left h, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le h.le, integral_id, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ r - l), smul_eq_mul]
  have : r - l ≠ 0 := by linarith
  field_simp; ring

lemma integrable_id_unifI {l r : ℝ} (h : l < r) : Integrable (fun x : ℝ => x) (unifI l r) := by
  rw [unifI, ite_eq_left h]
  exact (continuous_id.integrableOn_Icc).smul_measure (by simpa using h)

/-- **Lemma 4** (`m:lem:recog`), measure form: let `0 < a < b`. If the measure with density
`c₁` on `[0, a)`, `c₂` on `[a, b)` and `0` elsewhere (`c₁, c₂ ≥ 0`) is a probability measure with
mean `1`, then `c₁ = h₁` and `c₂ = h₂`, so its density is `g_{a,b}`. -/
theorem recog_measure {a b c₁ c₂ : ℝ} (ha : 0 < a) (hab : a < b) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hprob : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (step a b c₁ c₂ x)))
    (hmean : ∫ x, x ∂(volume.withDensity fun x => ENNReal.ofReal (step a b c₁ c₂ x)) = 1) :
    c₁ = h1 a b ∧ c₂ = h2 a b ∧ step a b c₁ c₂ = g a b := by
  have hp : 0 ≤ c₁ * a := mul_nonneg hc₁ ha.le
  have hq : 0 ≤ c₂ * (b - a) := mul_nonneg hc₂ (by linarith)
  have e : (volume.withDensity fun x => ENNReal.ofReal (step a b c₁ c₂ x))
      = ENNReal.ofReal (c₁ * a) • unifI 0 a + ENNReal.ofReal (c₂ * (b - a)) • unifI a b := by
    have ef : (fun x => ENNReal.ofReal (step a b c₁ c₂ x))
        = ENNReal.ofReal (c₁ * a) • (fun x => ENNReal.ofReal (ud 0 a x))
          + ENNReal.ofReal (c₂ * (b - a)) • (fun x => ENNReal.ofReal (ud a b x)) := by
      funext x
      rw [step_eq_ud ha hab, ENNReal.ofReal_add (mul_nonneg hp (ud_nonneg _ _ _))
        (mul_nonneg hq (ud_nonneg _ _ _)), ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hq]
      simp
    rw [ef, withDensity_add_left ((measurable_ud _ _).ennreal_ofReal.const_smul _),
      withDensity_smul _ (measurable_ud _ _).ennreal_ofReal,
      withDensity_smul _ (measurable_ud _ _).ennreal_ofReal, unifI_eq_withDensity ha,
      unifI_eq_withDensity hab]
  have := unifI_isProb 0 a
  have := unifI_isProb a b
  have hmass : c₁ * a + c₂ * (b - a) = 1 := by
    have h1 := hprob.measure_univ
    rw [e] at h1
    simp only [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one] at h1
    rw [← ENNReal.ofReal_add hp hq, ENNReal.ofReal_eq_one] at h1
    exact h1
  have hmean' : c₁ * a ^ 2 / 2 + c₂ * (b ^ 2 - a ^ 2) / 2 = 1 := by
    rw [e, integral_add_measure ((integrable_id_unifI ha).smul_measure (by simp))
      ((integrable_id_unifI hab).smul_measure (by simp)), integral_smul_measure,
      integral_smul_measure, integral_id_unifI ha, integral_id_unifI hab,
      ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, smul_eq_mul, smul_eq_mul] at hmean
    linear_combination hmean
  obtain ⟨h1, h2⟩ := recog ha hab hmass hmean'
  exact ⟨h1, h2, by rw [h1, h2]; rfl⟩

/-- The measure `∑ⱼ U(Iⱼ)` of a tuple of nondegenerate intervals integrates `x` and has first
moment `∑ⱼ (lⱼ + rⱼ)/2`. -/
lemma Tup.integral_measure (t : Tup) (h : ∀ B ∈ t, B.l < B.r) :
    Integrable (fun x : ℝ => x) (Tup.measure t) ∧ ∫ x, x ∂(Tup.measure t) = Tup.midSum t / 2 := by
  induction t with
  | nil => simp [Tup.measure, Tup.midSum]
  | cons B t ih =>
    have hB := h B List.mem_cons_self
    obtain ⟨hi, hint⟩ := ih fun B' hB' => h B' (List.mem_cons_of_mem _ hB')
    have hBi : Integrable (fun x : ℝ => x) ((B.c : ENNReal) • unifI B.l B.r) :=
      (integrable_id_unifI hB).smul_measure (by simp)
    simp only [Tup.measure, Tup.midSum, List.map_cons, List.sum_cons,
      ← Nat.cast_smul_eq_nsmul ENNReal]
      at hi hint ⊢
    refine ⟨hBi.add_measure hi, ?_⟩
    rw [integral_add_measure hBi hi, integral_smul_measure, integral_id_unifI hB, hint]
    simp only [ENNReal.toReal_natCast, smul_eq_mul]
    ring

/-- The marginal of a good mixture has mean `1` (the second statement of Lemma 4 uses this). -/
lemma Mix.Good.integral_marginal {n : ℕ} {b : ℝ} {M : Mix} (hn : 0 < n) (hM : M.Good n b) :
    Integrable (fun x : ℝ => x) ((n : ENNReal)⁻¹ • M.measure0) ∧
      ∫ x, x ∂((n : ENNReal)⁻¹ • M.measure0) = 1 := by
  have key : ∀ M : Mix, (∀ p ∈ M, 0 ≤ p.1) → (∀ p ∈ M, 0 < p.1 → p.2.Adm n ∧ p.2.Inside b) →
      Integrable (fun x : ℝ => x) (Mix.measure0 M) ∧
        ∫ x, x ∂(Mix.measure0 M) = n * (M.map Prod.fst).sum := by
    intro M hw hadm
    induction M with
    | nil => simp [Mix.measure0]
    | cons p M ih =>
      obtain ⟨hi, hint⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
        (fun q hq => hadm q (List.mem_cons_of_mem _ hq))
      have e : Mix.measure0 M = (M.map fun p => ENNReal.ofReal p.1 • p.2.measure).sum := rfl
      simp only [Mix.measure0, List.map_cons, List.sum_cons] at hi hint ⊢
      rw [← e] at hi hint ⊢
      have hp0 := hw p List.mem_cons_self
      rcases hp0.lt_or_eq with hp | hp
      · obtain ⟨hA, hI⟩ := hadm p List.mem_cons_self hp
        obtain ⟨hti, htint⟩ := p.2.integral_measure fun B hB => (hI B hB).2.1
        have hpi : Integrable (fun x : ℝ => x) (ENNReal.ofReal p.1 • p.2.measure) :=
          hti.smul_measure (by simp)
        refine ⟨hpi.add_measure hi, ?_⟩
        rw [integral_add_measure hpi hi, integral_smul_measure, htint, hint, hA.mid,
          ENNReal.toReal_ofReal hp0, smul_eq_mul]
        ring
      · rw [← hp]; simpa using ⟨hi, hint⟩
  obtain ⟨hi, hint⟩ := key M hM.nonneg hM.adm
  have hn' : (n : ℝ) ≠ 0 := by positivity
  refine ⟨hi.smul_measure (by simp; omega), ?_⟩
  rw [integral_smul_measure, hint, hM.sum_one, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]
  field_simp

/-- **Lemma 4** (`m:lem:recog`), second statement: if all intervals of a good mixture lie in
`[0, b]` and its marginal is the measure with density `c₁` on `[0, a)`, `c₂` on `[a, b)` and `0`
elsewhere, then the marginal is `g_{a,b}`. -/
theorem recog_mixture {n : ℕ} {a b c₁ c₂ : ℝ} {M : Mix} (hn : 0 < n) (hM : M.Good n b)
    (ha : 0 < a) (hab : a < b) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hm : (n : ENNReal)⁻¹ • M.measure0 =
      volume.withDensity fun x => ENNReal.ofReal (step a b c₁ c₂ x)) :
    step a b c₁ c₂ = g a b := by
  obtain ⟨-, hint⟩ := hM.integral_marginal hn
  obtain ⟨L, -, hsum, hmarg⟩ := M.toAdmissibleList hM.nonneg (fun p hp h => (hM.adm p hp h).1)
  have hprob : IsProbabilityMeasure ((n : ENNReal)⁻¹ • M.measure0) := by
    rw [← hmarg]
    constructor
    have : ∀ L : List (ENNReal × Admissible n),
        (L.map fun q => q.1 • q.2.marginal).sum Set.univ = (L.map Prod.fst).sum := by
      intro L
      induction L with
      | nil => simp
      | cons q L ih =>
        simp only [List.map_cons, List.sum_cons, add_apply, smul_apply, ih, smul_eq_mul]
        congr 1
        have : IsProbabilityMeasure q.2.marginal := by
          constructor
          simp only [Admissible.marginal, smul_apply, smul_eq_mul]
          have hu : ∀ l r, unifI l r Set.univ = 1 := fun l r => (unifI_isProb l r).measure_univ
          rw [sum_apply]
          simp only [hu, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
          exact ENNReal.inv_mul_cancel (by simp; omega) (by simp)
        simp
    rw [this, hsum, hM.sum_one, ENNReal.ofReal_one]
  rw [hm] at hprob hint
  exact (recog_measure ha hab hc₁ hc₂ hprob hint).2.2

/-- Lemma 3 (`lem:sym`, Section 3, not part of this file), stated for lists of weighted
admissible tuples: the marginal of every mixture of admissible tuples is `n`-completely
mixable. -/
def Lemma3 (n : ℕ) : Prop :=
  ∀ L : List (ENNReal × Admissible n), (L.map Prod.fst).sum = 1 →
    CompletelyMixable n (L.map fun q => q.1 • q.2.marginal).sum

/-- **Theorem 6, final sentence** (and Corollary 7 for `n = 3`): granted Lemma 3, the
distribution with density `g_{a,b}` is `n`-completely mixable for `n ≥ 3`, `0 < a < 2 < b ≤ n`. -/
theorem completelyMixable_g {n : ℕ} {a b : ℝ} (hL3 : Lemma3 n) (hn : 3 ≤ n) (ha0 : 0 < a)
    (ha2 : a < 2) (hb2 : 2 < b) (hbn : b ≤ n) :
    CompletelyMixable n (volume.withDensity (fun x => ENNReal.ofReal (g a b x))) := by
  obtain ⟨L, -, h1, h2⟩ := thm6_measure hn ha0 ha2 hb2 hbn
  exact h2 ▸ hL3 L h1

/-- Corollary 7 in measure form: granted Lemma 3, the two weighted tuples of `mixCor a b` give
a `3`-complete mix of `g_{a,b}`. -/
theorem completelyMixable_of_lemma3 {a b : ℝ} (hL3 : Lemma3 3) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hb2 : 2 < b) (hb3 : b ≤ 3) :
    ∃ L : List (ENNReal × Admissible 3), L.length ≤ 2 ∧ (L.map Prod.fst).sum = 1 ∧
      (L.map fun q => q.1 • q.2.marginal).sum =
        volume.withDensity (fun x => ENNReal.ofReal (g a b x)) ∧
      CompletelyMixable 3 (volume.withDensity (fun x => ENNReal.ofReal (g a b x))) := by
  obtain ⟨hG, hd⟩ := cor7 ha0 ha1 hb2 hb3
  obtain ⟨L, h1, h2, h3⟩ := hG.exists_admissible (by norm_num) hd
  have hlen : (mixCor a b).length = 2 := by unfold mixCor; split_ifs <;> rfl
  exact ⟨L, hlen ▸ h1, h2, h3, h3 ▸ hL3 L h2⟩

end TwoStep

end Mixes
