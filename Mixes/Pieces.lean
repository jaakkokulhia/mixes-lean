import Mixes.Defs

/-!
# Pieces with one atom (Proposition 32) and the middle-third lemma (Lemma 38)

* `pieceP β` is `P_β = (1 - 2/β) U[0,0] + (2/β) U[0,β]`, a measure built from `unifI`;
  `pieceP_eq` rewrites it as an atom `1 - 2/β` at `0` plus density `2/β²` on `[0, β]`.
* Tuples are built from blocks of equal intervals (`blk`, `blkAdm`). The explicit tuples of the
  paper are `tauI1`, `tauI2` (case (i)) and `rhoII1`, `rhoII2` (case (ii)); they are `Admissible`
  (Definition 2) for all parameters of their case, also when their weight is `0`.
* `caseI_marginal`, `caseII_marginal`: the marginal identity, as an equality of measures
  `ofReal w • marginal τ₁ + ofReal (1 - w) • marginal τ₂ = pieceP β`.
* `pieces_mixture`: Proposition 32 (the explicit mixture, intervals in `[0, β]`, weights in
  `[0, 1]`). The final sentence of the proposition (the complete mix via `lem:sym` and
  `lem:arch`) is not formalised here.
* `mean_mem_middle_third`: Lemma 38, with interval integrals over `[p, q]` and the hypothesis
  `0 < ∫ g` in place of "not identically zero". The proof differs from the paper's (which uses
  the measure `-h''`): concavity and `g(p) ≥ 0` give `g(p + λ(s - p)) ≥ λ g(s)`, hence
  `∫_p^x g ≥ λ² ∫_p^q g` for `λ = (x-p)/(q-p)`, and integration by parts gives the upper bound;
  the lower bound follows by the reflection `t ↦ p + q - t`.
-/

open MeasureTheory

noncomputable section

namespace Mixes

/-- The piece `P_β = (1 - 2/β) U[0,0] + (2/β) U[0,β]` of Section 12. -/
def pieceP (β : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - 2 / β) • unifI 0 0 + ENNReal.ofReal (2 / β) • unifI 0 β

/-- The identity `U[0,β] = (c/β) U[0,c] + (1 - c/β) U[c,β]` for `0 ≤ c ≤ β`, `0 < β`. -/
lemma unifI_split {β c : ℝ} (hβ : 0 < β) (hc0 : 0 ≤ c) (hcβ : c ≤ β) :
    unifI 0 β = ENNReal.ofReal (c / β) • unifI 0 c + ENNReal.ofReal (1 - c / β) • unifI c β := by
  rcases hc0.lt_or_eq with hc0 | rfl
  · rcases hcβ.lt_or_eq with hcβ | rfl
    · simp only [unifI, hβ, hc0, hcβ, ↓reduceIte, sub_zero, smul_smul]
      have hU : volume.restrict (Set.Icc (0 : ℝ) β) =
          volume.restrict (Set.Icc 0 c) + volume.restrict (Set.Icc c β) := by
        rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := c) (b := β)),
          ← Measure.restrict_union ((Set.Iic_disjoint_Ioi le_rfl).mono Set.Icc_subset_Iic_self
            Set.Ioc_subset_Ioi_self) measurableSet_Ioc,
          Set.Icc_union_Ioc_eq_Icc hc0.le hcβ.le]
      rw [hU, smul_add]
      congr 2
      · rw [ENNReal.ofReal_div_of_pos hβ, div_eq_mul_inv, mul_comm, ← mul_assoc,
          ENNReal.inv_mul_cancel (by simpa using hc0) ENNReal.ofReal_ne_top, one_mul]
      · have h1 : 1 - c / β = (β - c) / β := by field_simp
        rw [h1, ENNReal.ofReal_div_of_pos hβ, div_eq_mul_inv, mul_comm, ← mul_assoc,
          ENNReal.inv_mul_cancel (by simpa using hcβ) ENNReal.ofReal_ne_top, one_mul]
    · simp [hβ.ne']
  · simp

/-! ### Tuples made of blocks of equal intervals -/

/-- The `j`-th interval of the tuple made of `a` copies of `A`, then `b` copies of `B`, then `c`
copies of `C`, then copies of `D` (intervals are pairs `(left end, right end)`). -/
def blk (a b c : ℕ) (A B C D : ℝ × ℝ) (j : ℕ) : ℝ × ℝ :=
  if j < a then A else if j < a + b then B else if j < a + b + c then C else D

lemma blk_prop (P : ℝ × ℝ → Prop) {a b c : ℕ} {A B C D : ℝ × ℝ}
    (hA : P A) (hB : P B) (hC : P C) (hD : P D) (j : ℕ) : P (blk a b c A B C D j) := by
  unfold blk; split_ifs <;> assumption

lemma sum_blk {M : Type*} [AddCommMonoid M] (G : ℝ × ℝ → M) {n : ℕ} (a b c d : ℕ)
    (A B C D : ℝ × ℝ) (hn : n = a + b + c + d) :
    ∑ j : Fin n, G (blk a b c A B C D j) = a • G A + b • G B + c • G C + d • G D := by
  subst hn
  rw [Fin.sum_univ_eq_sum_range (fun j => G (blk a b c A B C D j)), Finset.sum_range_add,
    Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range a, G (blk a b c A B C D x) = ∑ _x ∈ Finset.range a, G A :=
    Finset.sum_congr rfl fun x hx => by
      simp only [Finset.mem_range] at hx; simp [blk, hx]
  have e2 : ∑ x ∈ Finset.range b, G (blk a b c A B C D (a + x)) =
      ∑ _x ∈ Finset.range b, G B :=
    Finset.sum_congr rfl fun x hx => by
      simp only [Finset.mem_range] at hx; simp [blk, hx]
  have e3 : ∑ x ∈ Finset.range c, G (blk a b c A B C D (a + b + x)) =
      ∑ _x ∈ Finset.range c, G C :=
    Finset.sum_congr rfl fun x hx => by
      simp only [Finset.mem_range] at hx; simp [blk, hx, add_assoc]
  have e4 : ∑ x ∈ Finset.range d, G (blk a b c A B C D (a + b + c + x)) =
      ∑ _x ∈ Finset.range d, G D :=
    Finset.sum_congr rfl fun x _ => by simp [blk, add_assoc]
  rw [e1, e2, e3, e4]
  simp

/-- The total length `a |A| + b |B| + c |C| + d |D|` of a block tuple. -/
def blkLen (a b c d : ℕ) (A B C D : ℝ × ℝ) : ℝ :=
  a * (A.2 - A.1) + b * (B.2 - B.1) + c * (C.2 - C.1) + d * (D.2 - D.1)

/-- A block tuple is admissible when every block interval is an interval, satisfies the polygon
inequality against the total length, the block `B` occurs and has positive length, and the
midpoints add up to `n`. -/
def blkAdm (n a b c d : ℕ) (A B C D : ℝ × ℝ) (hn : n = a + b + c + d)
    (hle : ∀ X ∈ [A, B, C, D], X.1 ≤ X.2)
    (hpoly : ∀ X ∈ [A, B, C, D], 2 * (X.2 - X.1) ≤ blkLen a b c d A B C D)
    (hb : 0 < b) (hB : B.1 < B.2)
    (hmid : a * (A.1 + A.2) + b * (B.1 + B.2) + c * (C.1 + C.2) + d * (D.1 + D.2) = 2 * n) :
    Admissible n where
  l j := (blk a b c A B C D j).1
  r j := (blk a b c A B C D j).2
  le j := blk_prop (fun X => X.1 ≤ X.2) (hle A (by simp)) (hle B (by simp)) (hle C (by simp))
    (hle D (by simp)) j
  pos := ⟨⟨a, by omega⟩, by simpa [blk, hb] using hB⟩
  polygon k := by
    have h := sum_blk (fun X => X.2 - X.1) a b c d A B C D hn
    simp only [nsmul_eq_mul] at h
    rw [h]
    exact blk_prop (fun X => 2 * (X.2 - X.1) ≤ blkLen a b c d A B C D) (hpoly A (by simp))
      (hpoly B (by simp)) (hpoly C (by simp)) (hpoly D (by simp)) k
  mid := by
    have h := sum_blk (fun X => X.1 + X.2) a b c d A B C D hn
    simp only [nsmul_eq_mul] at h
    rw [h, hmid]

lemma blkAdm_marginal {n a b c d : ℕ} {A B C D : ℝ × ℝ} {hn hle hpoly hb hB hmid} :
    (blkAdm n a b c d A B C D hn hle hpoly hb hB hmid).marginal = (n : ENNReal)⁻¹ •
      (a • unifI A.1 A.2 + b • unifI B.1 B.2 + c • unifI C.1 C.2 + d • unifI D.1 D.2) := by
  unfold Admissible.marginal
  rw [← sum_blk (fun X => unifI X.1 X.2) a b c d A B C D hn]
  rfl

lemma blkAdm_mem {n a b c d : ℕ} {A B C D : ℝ × ℝ} {hn hle hpoly hb hB hmid} {lo hi : ℝ}
    (h : ∀ X ∈ [A, B, C, D], lo ≤ X.1 ∧ X.2 ≤ hi) (j : Fin n) :
    lo ≤ (blkAdm n a b c d A B C D hn hle hpoly hb hB hmid).l j ∧
      (blkAdm n a b c d A B C D hn hle hpoly hb hB hmid).r j ≤ hi :=
  blk_prop (fun X => lo ≤ X.1 ∧ X.2 ≤ hi) (h A (by simp)) (h B (by simp)) (h C (by simp))
    (h D (by simp)) j

/-! ### Case (i) of Proposition 32 -/

/-- `k = min(n - 1, ⌊2n/β⌋)` of Proposition 32(i). -/
def kI (n : ℕ) (β : ℝ) : ℕ := min (n - 1) ⌊2 * n / β⌋₊

/-- `u = 2n - kβ` of Proposition 32(i). -/
def uI (n : ℕ) (β : ℝ) : ℝ := 2 * n - kI n β * β

lemma caseI_facts {n : ℕ} {β : ℝ} (hn : 4 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ 2 * n / 3) :
    3 ≤ kI n β ∧ kI n β ≤ n - 1 ∧ 0 ≤ uI n β ∧ uI n β ≤ β := by
  have hβ0 : 0 < β := by linarith
  have h3 : (3 : ℝ) ≤ 2 * n / β := by rw [le_div_iff₀ hβ0]; linarith
  have hfl3 : 3 ≤ ⌊2 * n / β⌋₊ := Nat.le_floor (by exact_mod_cast h3)
  have hk_le_fl : kI n β ≤ ⌊2 * n / β⌋₊ := min_le_right _ _
  have hkfl : (kI n β : ℝ) ≤ 2 * n / β :=
    (Nat.cast_le.mpr hk_le_fl).trans (Nat.floor_le (by positivity))
  refine ⟨le_min (by omega) hfl3, min_le_left _ _, ?_, ?_⟩
  · unfold uI; rw [le_div_iff₀ hβ0] at hkfl; linarith
  · unfold uI
    rcases min_choice (n - 1) ⌊2 * n / β⌋₊ with h | h
    · have hk : kI n β = n - 1 := h
      rw [hk, Nat.cast_sub (by omega)]; push_cast; nlinarith
    · have hk : kI n β = ⌊2 * n / β⌋₊ := h
      have := Nat.lt_floor_add_one (2 * n / β)
      rw [← hk, div_lt_iff₀ hβ0] at this
      linarith

/-- The tuple `τ' = ((n-1-k)·[0,0], k·[0,β], [0,u])` of Proposition 32(i). -/
def tauI1 {n : ℕ} {β : ℝ} (hn : 4 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ 2 * n / 3) : Admissible n :=
  blkAdm n (n - 1 - kI n β) (kI n β) 1 0 (0, 0) (0, β) (0, uI n β) (0, 0)
    (by have := caseI_facts hn hβ hβn; omega)
    (by
      obtain ⟨-, -, hu0, huβ⟩ := caseI_facts hn hβ hβn
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith)
    (by
      obtain ⟨hk, -, hu0, huβ⟩ := caseI_facts hn hβ hβn
      have hk' : (3 : ℝ) ≤ kI n β := by exact_mod_cast hk
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp [blkLen] <;> nlinarith)
    (by have := caseI_facts hn hβ hβn; omega) (by simp; linarith)
    (by simp [uI])

/-- The tuple `τ'' = ((n-k)·[0,0], (k-1)·[0,β], [u,β])` of Proposition 32(i). -/
def tauI2 {n : ℕ} {β : ℝ} (hn : 4 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ 2 * n / 3) : Admissible n :=
  blkAdm n (n - kI n β) (kI n β - 1) 1 0 (0, 0) (0, β) (uI n β, β) (0, 0)
    (by have := caseI_facts hn hβ hβn; omega)
    (by
      obtain ⟨-, -, hu0, huβ⟩ := caseI_facts hn hβ hβn
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith)
    (by
      obtain ⟨hk, -, hu0, huβ⟩ := caseI_facts hn hβ hβn
      have hk' : (3 : ℝ) ≤ kI n β := by exact_mod_cast hk
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp [blkLen, Nat.cast_sub (by omega : 1 ≤ kI n β)]
        <;> nlinarith)
    (by have := caseI_facts hn hβ hβn; omega) (by simp; linarith)
    (by
      obtain ⟨hk, -, -, -⟩ := caseI_facts hn hβ hβn
      simp [uI, Nat.cast_sub (by omega : 1 ≤ kI n β)]; ring)

theorem caseI_marginal {n : ℕ} {β : ℝ} (hn : 4 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ 2 * n / 3) :
    ENNReal.ofReal (uI n β / β) • (tauI1 hn hβ hβn).marginal +
      ENNReal.ofReal (1 - uI n β / β) • (tauI2 hn hβ hβn).marginal = pieceP β := by
  obtain ⟨hk, hkn, hu0, huβ⟩ := caseI_facts hn hβ hβn
  have hβ0 : 0 < β := by linarith
  simp only [tauI1, tauI2, blkAdm_marginal, pieceP]
  rw [unifI_split hβ0 hu0 huβ]
  have hn' : (n : ENNReal)⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  rw [hn']
  ext s hs
  simp only [add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
  have := unifI_isProb 0 0; have := unifI_isProb 0 (uI n β); have := unifI_isProb (uI n β) β
  have ha := measure_ne_top (unifI 0 0) s
  have hb := measure_ne_top (unifI 0 (uI n β)) s
  have hc := measure_ne_top (unifI (uI n β) β) s
  generalize (unifI 0 0) s = A at ha ⊢
  generalize (unifI 0 (uI n β)) s = B at hb ⊢
  generalize (unifI (uI n β) β) s = C at hc ⊢
  have hw0 : 0 ≤ uI n β / β := div_nonneg hu0 hβ0.le
  have hw1 : 0 ≤ 1 - uI n β / β := by rw [sub_nonneg, div_le_one hβ0]; exact huβ
  have h20 : 0 ≤ 1 - 2 / β := by rw [sub_nonneg, div_le_one hβ0]; exact hβ
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hw0, ENNReal.toReal_ofReal hw1, ENNReal.toReal_ofReal h20,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / β), ENNReal.toReal_natCast]
  rw [Nat.cast_sub (by omega : kI n β ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : kI n β ≤ n), Nat.cast_sub (by omega : 1 ≤ kI n β)]
  unfold uI
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring
/-! ### Case (ii) of Proposition 32 -/

lemma caseII_facts {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n)
    (hcase : n = 3 ∨ 2 * n / 3 < β) : 0 ≤ (n : ℝ) - β ∧ 2 * ((n : ℝ) - β) ≤ β := by
  refine ⟨by linarith, ?_⟩
  rcases hcase with rfl | h
  · push_cast; linarith
  · rw [div_lt_iff₀ (by norm_num)] at h; linarith

/-- The tuple `ρ' = ((n-2)·[0,0], 2·[x,β])`, `x = n - β`, of Proposition 32(ii). -/
def rhoII1 {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n)
    (hcase : n = 3 ∨ 2 * n / 3 < β) : Admissible n :=
  blkAdm n (n - 2) 2 0 0 (0, 0) (n - β, β) (0, 0) (0, 0) (by omega)
    (by
      obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp; linarith)
    (by
      obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp [blkLen] <;> linarith)
    (by norm_num) (by have := caseII_facts hn hβ hβn hcase; simp only; linarith)
    (by simp)

/-- The tuple `ρ'' = ((n-3)·[0,0], [0,β], [0,x], [x,β])`, `x = n - β`, of Proposition 32(ii)
(the order of the intervals differs from the paper, which does not matter). -/
def rhoII2 {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n)
    (hcase : n = 3 ∨ 2 * n / 3 < β) : Admissible n :=
  blkAdm n (n - 3) 1 1 1 (0, 0) (0, β) (0, n - β) (n - β, β) (by omega)
    (by
      obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith)
    (by
      obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp [blkLen] <;> linarith)
    (by norm_num) (by simp only; linarith)
    (by simp; ring)

theorem caseII_marginal {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n)
    (hcase : n = 3 ∨ 2 * n / 3 < β) :
    ENNReal.ofReal (1 - 2 * (n - β) / β) • (rhoII1 hn hβ hβn hcase).marginal +
      ENNReal.ofReal (2 * (n - β) / β) • (rhoII2 hn hβ hβn hcase).marginal = pieceP β := by
  obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
  have hβ0 : 0 < β := by linarith
  have hxβ' : (n : ℝ) - β ≤ β := by linarith
  simp only [rhoII1, rhoII2, blkAdm_marginal, pieceP]
  rw [unifI_split hβ0 hx0 hxβ']
  have hn' : (n : ENNReal)⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  rw [hn']
  ext s hs
  simp only [add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
  have := unifI_isProb 0 0; have := unifI_isProb 0 ((n : ℝ) - β)
  have := unifI_isProb ((n : ℝ) - β) β
  have ha := measure_ne_top (unifI 0 0) s
  have hb := measure_ne_top (unifI 0 ((n : ℝ) - β)) s
  have hc := measure_ne_top (unifI ((n : ℝ) - β) β) s
  generalize (unifI 0 0) s = A at ha ⊢
  generalize (unifI 0 ((n : ℝ) - β)) s = B at hb ⊢
  generalize (unifI ((n : ℝ) - β) β) s = C at hc ⊢
  have hw0 : 0 ≤ ((n : ℝ) - β) / β := div_nonneg hx0 hβ0.le
  have hw1 : 0 ≤ 1 - ((n : ℝ) - β) / β := by rw [sub_nonneg, div_le_one hβ0]; exact hxβ'
  have hv0 : 0 ≤ 2 * ((n : ℝ) - β) / β := div_nonneg (by linarith) hβ0.le
  have hv1 : 0 ≤ 1 - 2 * ((n : ℝ) - β) / β := by rw [sub_nonneg, div_le_one hβ0]; exact hxβ
  have h20 : 0 ≤ 1 - 2 / β := by rw [sub_nonneg, div_le_one hβ0]; exact hβ
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hw0, ENNReal.toReal_ofReal hw1, ENNReal.toReal_ofReal h20,
    ENNReal.toReal_ofReal hv0, ENNReal.toReal_ofReal hv1,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / β), ENNReal.toReal_natCast]
  rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n)]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Proposition 32 -/

/-- `P_β` has an atom of mass `1 - 2/β` at `0` and density `2/β²` on `[0, β]`. -/
lemma pieceP_eq {β : ℝ} (hβ : 0 < β) : pieceP β = ENNReal.ofReal (1 - 2 / β) • Measure.dirac 0 +
    ENNReal.ofReal (2 / β ^ 2) • volume.restrict (Set.Icc 0 β) := by
  simp only [pieceP, unifI, lt_irrefl, hβ, ↓reduceIte, sub_zero, smul_smul]
  congr 2
  rw [← ENNReal.ofReal_inv_of_pos hβ, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; field_simp

/-- `P_β` is a probability measure for `β ≥ 2`. -/
lemma pieceP_isProb {β : ℝ} (hβ : 2 ≤ β) : IsProbabilityMeasure (pieceP β) := by
  have := unifI_isProb 0 0; have := unifI_isProb 0 β
  have hβ0 : 0 < β := by linarith
  constructor
  simp only [pieceP, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by rw [sub_nonneg, div_le_one hβ0]; exact hβ) (by positivity)]
  simp

/-- **Proposition 32.** Let `n ≥ 3` and `2 ≤ β ≤ n`. Then `P_β` is the marginal of a mixture
`w τ₁ + (1 - w) τ₂` of two admissible tuples whose intervals lie in `[0, β]`, with `0 ≤ w ≤ 1`.
The tuples and the weight are the explicit ones of the paper: `tauI1`, `tauI2` and `u/β` in case
(i) (`n ≥ 4` and `β ≤ 2n/3`), and `rhoII1`, `rhoII2` and `1 - 2x/β` otherwise (case (ii)); see
`caseI_marginal` and `caseII_marginal`. -/
theorem pieces_mixture {n : ℕ} {β : ℝ} (hn : 3 ≤ n) (hβ : 2 ≤ β) (hβn : β ≤ n) :
    ∃ (τ₁ τ₂ : Admissible n) (w : ℝ), 0 ≤ w ∧ w ≤ 1 ∧
      (∀ j, 0 ≤ τ₁.l j ∧ τ₁.r j ≤ β) ∧ (∀ j, 0 ≤ τ₂.l j ∧ τ₂.r j ≤ β) ∧
      ENNReal.ofReal w • τ₁.marginal + ENNReal.ofReal (1 - w) • τ₂.marginal = pieceP β := by
  have hβ0 : 0 < β := by linarith
  by_cases h : 4 ≤ n ∧ β ≤ 2 * n / 3
  · obtain ⟨hn4, hβ3⟩ := h
    obtain ⟨-, -, hu0, huβ⟩ := caseI_facts hn4 hβ hβ3
    refine ⟨tauI1 hn4 hβ hβ3, tauI2 hn4 hβ hβ3, uI n β / β, div_nonneg hu0 hβ0.le,
      (div_le_one hβ0).mpr huβ, ?_, ?_, caseI_marginal hn4 hβ hβ3⟩
    · unfold tauI1
      refine blkAdm_mem ?_
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith
    · unfold tauI2
      refine blkAdm_mem ?_
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith
  · have hcase : n = 3 ∨ 2 * n / 3 < β := by
      by_cases h4 : 4 ≤ n
      · exact Or.inr (lt_of_not_ge fun h' => h ⟨h4, h'⟩)
      · exact Or.inl (by omega)
    obtain ⟨hx0, hxβ⟩ := caseII_facts hn hβ hβn hcase
    refine ⟨rhoII1 hn hβ hβn hcase, rhoII2 hn hβ hβn hcase, 1 - 2 * (n - β) / β,
      by rw [sub_nonneg, div_le_one hβ0]; exact hxβ,
      by have : 0 ≤ 2 * ((n : ℝ) - β) / β := div_nonneg (by linarith) hβ0.le
         linarith, ?_, ?_, ?_⟩
    · unfold rhoII1
      refine blkAdm_mem ?_
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith
    · unfold rhoII2
      refine blkAdm_mem ?_
      intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> simp <;> linarith
    · rw [sub_sub_cancel]; exact caseII_marginal hn hβ hβn hcase

/-! ### Lemma 38: the mean of a concave function lies in the middle third -/

section Third

variable {g : ℝ → ℝ} {p q : ℝ}

/-- Scaling step: for `p ≤ x ≤ q` and `λ = (x - p)/(q - p)`, `λ² ∫_p^q g ≤ ∫_p^x g`. -/
lemma third_scaling (hpq : p < q) (hg : ConcaveOn ℝ (Set.Icc p q) g)
    (h0 : ∀ t ∈ Set.Icc p q, 0 ≤ g t) (hint : IntervalIntegrable g volume p q)
    {x : ℝ} (hx : x ∈ Set.Icc p q) :
    ((x - p) / (q - p)) ^ 2 * ∫ t in p..q, g t ≤ ∫ t in p..x, g t := by
  set l := (x - p) / (q - p) with hl
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have hl0 : 0 ≤ l := div_nonneg (by linarith [hx.1]) hqp.le
  have hl1 : l ≤ 1 := (div_le_one hqp).mpr (by linarith [hx.2])
  rcases hl0.lt_or_eq with hl0 | hl0
  swap
  · rw [← hl0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    have hxp : x = p := by
      have : x - p = 0 := by
        have := hl0.symm; rw [hl, div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · linarith
      linarith
    rw [hxp, intervalIntegral.integral_same]
  set d := (1 - l) * p
  have hlq : l * q + d = x := by simp only [d, hl]; field_simp; ring
  have hlp : l * p + d = p := by ring
  -- change of variables
  have hcv : ∫ s in p..q, g (l * s + d) = l⁻¹ * ∫ t in p..x, g t := by
    rw [intervalIntegral.integral_comp_mul_add _ hl0.ne', hlq, hlp, smul_eq_mul]
  -- integrability of the composite
  have hint' : IntervalIntegrable (fun s => g (l * s + d)) volume p q := by
    have h1 : IntervalIntegrable g volume p x :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le hpq.le]
        exact Set.Icc_subset_Icc le_rfl hx.2)
    have h2 := (h1.comp_add_right d).comp_mul_left (c := l)
    have e1 : (p - d) / l = p := by
      rw [div_eq_iff hl0.ne']; simp only [d]; ring
    have e2 : (x - d) / l = q := by
      rw [div_eq_iff hl0.ne']; rw [← hlq]; ring
    rw [e1, e2] at h2
    exact h2
  -- pointwise concavity bound
  have hpt : ∀ s ∈ Set.Icc p q, l * g s ≤ g (l * s + d) := by
    intro s hs
    have := hg.2 hs (Set.left_mem_Icc.mpr hpq.le) hl0.le (by linarith : 0 ≤ 1 - l)
      (by ring)
    simp only [smul_eq_mul] at this
    have hgp := h0 p (Set.left_mem_Icc.mpr hpq.le)
    have : l * g s + (1 - l) * g p ≤ g (l * s + d) := by
      simpa [d, mul_comm, mul_left_comm, mul_assoc] using this
    nlinarith
  have hmono : ∫ s in p..q, l * g s ≤ ∫ s in p..q, g (l * s + d) :=
    intervalIntegral.integral_mono_on hpq.le (hint.const_mul l) hint' hpt
  rw [intervalIntegral.integral_const_mul, hcv] at hmono
  have := mul_le_mul_of_nonneg_left hmono hl0.le
  rw [← mul_assoc l l⁻¹, mul_inv_cancel₀ hl0.ne', one_mul] at this
  rw [sq, mul_assoc]; exact this

/-- Upper half of Lemma 38: `∫_p^q t g(t) dt ≤ (q - (q-p)/3) ∫_p^q g`. -/
lemma third_upper (hpq : p < q) (hg : ConcaveOn ℝ (Set.Icc p q) g)
    (h0 : ∀ t ∈ Set.Icc p q, 0 ≤ g t) (hint : IntervalIntegrable g volume p q) :
    ∫ t in p..q, t * g t ≤ (q - (q - p) / 3) * ∫ t in p..q, g t := by
  set G : ℝ → ℝ := fun x => ∫ t in p..x, g t with hG
  have hGc : ContinuousOn G (Set.uIcc p q) :=
    intervalIntegral.continuousOn_primitive_interval
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hpq.le).mp hint |>.mono_set
        (by rw [Set.uIcc_of_le hpq.le]))
  have hgc : ContinuousOn g (Set.Ioo p q) := by
    have := hg.continuousOn_interior; rwa [interior_Icc] at this
  have hderiv : ∀ x ∈ Set.Ioo (min p q) (max p q), HasDerivAt G (g x) x := by
    intro x hx
    rw [min_eq_left hpq.le, max_eq_right hpq.le] at hx
    refine intervalIntegral.integral_hasDerivAt_right
      (hint.mono_set ?_) (hgc.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (hgc.continuousAt (isOpen_Ioo.mem_nhds hx))
    rw [Set.uIcc_of_le hpq.le, Set.uIcc_of_le hx.1.le]
    exact Set.Icc_subset_Icc le_rfl hx.2.le
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t => t) (u' := fun _ => (1 : ℝ)) (v := G) (v' := g) continuousOn_id hGc
    (fun x _ => hasDerivAt_id x) hderiv intervalIntegrable_const hint
  simp only [one_mul, hG, intervalIntegral.integral_same, mul_zero, sub_zero] at hibp
  -- lower bound for `∫ G`
  have hGint : IntervalIntegrable G volume p q := hGc.intervalIntegrable
  have hlow : ∫ x in p..q, ((x - p) / (q - p)) ^ 2 * ∫ t in p..q, g t ≤ ∫ x in p..q, G x :=
    intervalIntegral.integral_mono_on hpq.le
      ((by fun_prop : Continuous fun x => ((x - p) / (q - p)) ^ 2 *
          ∫ t in p..q, g t).intervalIntegrable _ _)
      hGint (fun x hx => third_scaling hpq hg h0 hint hx)
  have hcomp : ∫ x in p..q, ((x - p) / (q - p)) ^ 2 * ∫ t in p..q, g t =
      (q - p) / 3 * ∫ t in p..q, g t := by
    rw [intervalIntegral.integral_mul_const]
    congr 1
    have hqp : q - p ≠ 0 := sub_ne_zero.mpr hpq.ne'
    simp_rw [div_pow]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) p, integral_pow]
    field_simp
    ring
  rw [hcomp] at hlow
  rw [hibp]
  linarith

/-- **Lemma 38.** If `g` is concave and nonnegative on `[p, q]` with `∫_p^q g > 0`, then its mean
`∫ t g(t) dt / ∫ g` lies in the middle third `[p + (q-p)/3, q - (q-p)/3]`. -/
theorem mean_mem_middle_third (hpq : p ≤ q) (hg : ConcaveOn ℝ (Set.Icc p q) g)
    (h0 : ∀ t ∈ Set.Icc p q, 0 ≤ g t) (hpos : 0 < ∫ t in p..q, g t) :
    p + (q - p) / 3 ≤ (∫ t in p..q, t * g t) / (∫ t in p..q, g t) ∧
      (∫ t in p..q, t * g t) / (∫ t in p..q, g t) ≤ q - (q - p) / 3 := by
  have hint : IntervalIntegrable g volume p q := by
    by_contra h
    rw [intervalIntegral.integral_undef h] at hpos
    exact lt_irrefl _ hpos
  have hpq' : p < q := by
    rcases hpq.lt_or_eq with h | rfl
    · exact h
    · simp at hpos
  constructor
  · -- reflection `t ↦ p + q - t`
    set g' : ℝ → ℝ := fun t => g (p + q - t)
    have hmap : ∀ t ∈ Set.Icc p q, p + q - t ∈ Set.Icc p q := fun t ht =>
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hg' : ConcaveOn ℝ (Set.Icc p q) g' := by
      refine ⟨convex_Icc p q, fun x hx y hy a b ha hb hab => ?_⟩
      have := hg.2 (hmap x hx) (hmap y hy) ha hb hab
      simp only [smul_eq_mul] at this ⊢
      have e : p + q - (a * x + b * y) = a * (p + q - x) + b * (p + q - y) := by
        linear_combination (-(p + q)) * hab
      simp only [g']; rw [e]; exact this
    have h0' : ∀ t ∈ Set.Icc p q, 0 ≤ g' t := fun t ht => h0 _ (hmap t ht)
    have hint' : IntervalIntegrable g' volume p q := by
      have := hint.comp_sub_left (p + q)
      simpa [g'] using this.symm
    have e1 : ∫ t in p..q, g' t = ∫ t in p..q, g t := by
      simp only [g']
      rw [intervalIntegral.integral_comp_sub_left (fun t => g t) (p + q)]
      congr 1 <;> ring
    have e2 : ∫ t in p..q, t * g' t = ∫ t in p..q, (p + q - t) * g t := by
      have := intervalIntegral.integral_comp_sub_left (fun t => (p + q - t) * g t) (p + q)
        (a := p) (b := q)
      simp only [sub_sub_cancel] at this
      rw [show p + q - q = p by ring, show p + q - p = q by ring] at this
      exact this
    have hup := third_upper hpq' hg' h0' hint'
    rw [e1, e2] at hup
    have hti : IntervalIntegrable (fun t => t * g t) volume p q :=
      hint.continuousOn_mul continuousOn_id
    have e3 : ∫ t in p..q, (p + q - t) * g t =
        (p + q) * (∫ t in p..q, g t) - ∫ t in p..q, t * g t := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hint.const_mul _) hti, intervalIntegral.integral_const_mul]
    rw [e3] at hup
    rw [le_div_iff₀ hpos]
    linarith
  · rw [div_le_iff₀ hpos]
    exact third_upper hpq' hg h0 hint

end Third

end Mixes
