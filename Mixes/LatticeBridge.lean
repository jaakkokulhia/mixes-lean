import Mixes.LatticeBasic
import Mixes.LatticeLarge

/-!
# Lattice distributions: bridge between `LatticeBasic` and `LatticeLarge`

`LatticeLarge` states Lemma `lt:lem:count`, the last statement of Theorem `lt:thm:pb` and
Proposition `lt:prop:three` as hypotheses `H_lt_lem_count`, `H_lt_thm_pb`, `H_lt_prop_three`.
`LatticeBasic` proves them (`count_iff_fintype`, `binom_completelyMixable`, `binom2_cm_iff`),
with its own definitions of the binomial distribution (a law of a sum of independent indicators)
and of the count vectors. This file shows that the definitions agree, discharges the three
hypotheses, and states the main theorems of `LatticeLarge` unconditionally (`*_uncond`).
-/

open MeasureTheory Finset

noncomputable section

namespace Mixes.LatticeBridge

open Mixes

/-! ### The two binomial distributions agree -/

/-- The binomial distribution of `LatticeBasic` (sum of `N` independent indicators with success
probability `p`) equals that of `LatticeLarge` (masses `C(N,x) p^x (1-p)^(N-x)` at `0, …, N`). -/
theorem binom_eq (N : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    LatticeBasic.binom N p = LatticeLarge.binom N p := by
  classical
  have hL : LatticeLarge.binom N p =
      LatticeBasic.law (LatticeLarge.binomMass N p) (LatticeLarge.binomVal N) := rfl
  rw [hL, LatticeBasic.binom, LatticeBasic.pbLaw]
  refine LatticeBasic.law_eq_of_expect
    (LatticeBasic.pbW_nonneg (fun _ => ⟨hp0, hp1⟩))
    (LatticeLarge.binomMass_nonneg hp0 hp1) fun g => ?_
  -- reindex the Boolean vectors by finite sets
  have hbij : Function.Bijective (fun s : Finset (Fin N) => fun i => decide (i ∈ s)) := by
    constructor
    · intro s t h
      ext i
      have := congrFun h i
      simpa using this
    · intro ε
      refine ⟨Finset.univ.filter (fun i => ε i = true), ?_⟩
      funext i
      cases h : ε i <;> simp [h]
  rw [← Fintype.sum_bijective _ hbij
    (fun s : Finset (Fin N) => (p ^ s.card * (1 - p) ^ (N - s.card)) * g (s.card : ℝ)) _
    (fun s => ?_)]
  · rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
      (fun m => (p ^ m * (1 - p) ^ (N - m)) * g (m : ℝ))]
    simp only [Finset.card_univ, Fintype.card_fin, LatticeLarge.binomMass, LatticeLarge.binomVal]
    rw [Fin.sum_univ_eq_sum_range
      (fun x => ((N.choose x : ℝ) * p ^ x * (1 - p) ^ (N - x)) * g (x : ℝ)) (N + 1)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul]; ring
  · congr 1
    · have : ∀ i, LatticeBasic.bern p (decide (i ∈ s)) = if i ∈ s then p else 1 - p := by
        intro i; by_cases h : i ∈ s <;> simp [LatticeBasic.bern, h]
      simp_rw [this]
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      congr 2
      · congr 1; ext i; simp
      · have : (Finset.univ.filter fun i : Fin N => i ∉ s) = sᶜ := by ext i; simp
        rw [this, Finset.card_compl, Fintype.card_fin]
    · congr 1
      simp [LatticeBasic.ind]

/-! ### The three hypotheses of `LatticeLarge` -/

/-- **Lemma `lt:lem:count`** in the form of `LatticeLarge`. -/
theorem lem_count : LatticeLarge.H_lt_lem_count := by
  intro ι _ val f hinj hf0 hf1 n hn
  classical
  have hF : LatticeLarge.discr val f = LatticeBasic.law f val := rfl
  have : IsProbabilityMeasure (LatticeLarge.discr val f) := LatticeBasic.law_isProb hf0 hf1 val
  have hcar : LatticeLarge.discr val f (Set.range val)ᶜ = 0 := by
    rw [hF, LatticeBasic.law_apply_real hf0 val (Set.finite_range val).measurableSet.compl]
    simp
  have hmass : LatticeBasic.masses (LatticeLarge.discr val f) val = f := by
    funext i
    rw [LatticeBasic.masses, hF, LatticeBasic.law_singleton hf0,
      ENNReal.toReal_ofReal (LatticeBasic.mass_nonneg hf0 _ _)]
    simp [LatticeBasic.mass, hinj.eq_iff]
  have hmean : ∫ t, t ∂(LatticeLarge.discr val f) = LatticeLarge.mean val f := by
    rw [LatticeBasic.mean_eq_sum hinj _ hcar, hmass, LatticeLarge.mean]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hset : ((fun k : ι → ℕ => fun i => (k i : ℝ) / n) ''
      LatticeBasic.countVecs val n (n * LatticeLarge.mean val f)) =
      ((fun y => (n : ℝ)⁻¹ • y) '' LatticeLarge.countVecs val n (n * LatticeLarge.mean val f)) := by
    ext y
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨LatticeLarge.natVec k, ⟨k, rfl, hk1, hk2⟩, by
        funext i; simp [LatticeLarge.natVec, div_eq_inv_mul]⟩
    · rintro ⟨_, ⟨k, rfl, hk1, hk2⟩, rfl⟩
      exact ⟨k, ⟨hk1, hk2⟩, by funext i; simp [LatticeLarge.natVec, div_eq_inv_mul]⟩
  rw [LatticeBasic.count_iff_fintype hinj _ hcar (by omega : 1 ≤ n), hmass, hmean, hset]
  rfl

/-- **Theorem `lt:thm:pb`, last statement** in the form of `LatticeLarge`. -/
theorem thm_pb : LatticeLarge.H_lt_thm_pb := by
  intro n j s K _hn hj hjs hsn hK
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  rw [← binom_eq _ (div_nonneg (Nat.cast_nonneg _) hs.le)
    ((div_le_one hs).2 (by exact_mod_cast hjs))]
  exact LatticeBasic.binom_completelyMixable hj hjs hsn hK

/-- **Proposition `lt:prop:three`** (for `B(2, p)`) in the form of `LatticeLarge`. -/
theorem prop_three : LatticeLarge.H_lt_prop_three := by
  intro n hn p hp0 hp1
  rw [← binom_eq 2 hp0.le hp1.le]
  exact LatticeBasic.binom2_cm_iff hp0 hp1 hn

/-! ### Unconditional versions of the main theorems of `LatticeLarge` -/

section Uncond

open Mixes.LatticeLarge

/-- **Theorem `lt:thm:large`(a)**: if `F` is `n`-completely mixable then `n f ∈ ℤ^S + Λ_ℝ`. -/
theorem large_a_uncond {ι : Type} [Fintype ι] (val f : ι → ℝ)
    (hinj : Function.Injective val) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) (n : ℕ)
    (hn : 2 ≤ n) (hmix : CompletelyMixable n (discr val f)) :
    IntPlusLamR val ((n : ℝ) • f) :=
  large_a lem_count val f hinj hf0 hf1 n hn hmix

/-- **Theorem `lt:thm:large`(b)**. -/
theorem large_b_uncond {ι : Type} [Fintype ι] (val f : ι → ℝ)
    (hinj : Function.Injective val) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) (n : ℕ)
    (hn : 2 ≤ n) {ρ : ℕ} (b : Fin ρ → ι → ℤ) (hb : ∀ j, b j ∈ lam val)
    (hspan : lamR val ≤ Submodule.span ℝ (Set.range fun j => intVec (b j)))
    (hint : IntPlusLamR val ((n : ℝ) • f)) (hbeta : ∀ i, ∑ j, |(b j i : ℝ)| ≤ n * f i) :
    CompletelyMixable n (discr val f) :=
  large_b lem_count val f hinj hf0 hf1 n hn b hb hspan hint hbeta

/-- **Theorem `lt:thm:large`**, the eventual characterisation for positive masses. -/
theorem large_eventually_uncond {ι : Type} [Fintype ι] (val f : ι → ℝ)
    (hinj : Function.Injective val) (hfpos : ∀ i, 0 < f i) (hf1 : ∑ i, f i = 1) :
    ∃ N : ℕ, ∀ n : ℕ, 2 ≤ n →
      (CompletelyMixable n (discr val f) → IntPlusLamR val ((n : ℝ) • f)) ∧
      (N ≤ n → IntPlusLamR val ((n : ℝ) • f) → CompletelyMixable n (discr val f)) :=
  large_eventually lem_count val f hinj hfpos hf1

/-- **Theorem `lt:thm:large`(c)**, two points. -/
theorem large_c_two_uncond (val f : Fin 2 → ℝ) (hinj : Function.Injective val)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) (n : ℕ) (hn : 2 ≤ n) :
    CompletelyMixable n (discr val f) ↔ ∀ i, ∃ m : ℤ, (n : ℝ) * f i = m :=
  large_c_two lem_count val f hinj hf0 hf1 n hn

/-- **Proposition `lt:prop:binomial`(a)**. -/
theorem binomial_a_uncond {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hmix : CompletelyMixable n (binom N p)) :
    (∃ m : ℤ, (n : ℝ) * N * p = m) ∧ 1 / (n : ℝ) ≤ p ∧ p ≤ 1 - 1 / (n : ℝ) :=
  binomial_a lem_count hN hn hp0 hp1 hmix

/-- **Proposition `lt:prop:binomial`(c)**, case `np ∈ ℤ`. -/
theorem binomial_c_int_uncond {n N : ℕ} (hn : 2 ≤ n) (hN : 1 ≤ N) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hint : ∃ m : ℤ, (n : ℝ) * p = m) :
    CompletelyMixable n (binom N p) :=
  binomial_c_int lem_count hn hN hp0 hp1 hint

/-- **Proposition `lt:prop:binomial`(c)**, case `N = 2`. -/
theorem binomial_c_two_uncond {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hint : ∃ m : ℤ, (n : ℝ) * 2 * p = m) (hlo : 1 / (n : ℝ) ≤ p)
    (hhi : p ≤ 1 - 1 / (n : ℝ)) : CompletelyMixable n (binom 2 p) :=
  binomial_c_two prop_three hn hp0 hp1 hint hlo hhi

/-- **Proposition `lt:prop:binomial`(c)**, case `p = j/s`, `s ≤ n`, `s ∣ N`. -/
theorem binomial_c_pb_uncond {n N j s : ℕ} (hn : 2 ≤ n) (hN : 1 ≤ N)
    (hs : s ≤ n) (hsN : s ∣ N) (hp0 : 0 < (j : ℝ) / s) (hp1 : (j : ℝ) / s < 1) :
    CompletelyMixable n (binom N ((j : ℝ) / s)) :=
  binomial_c_pb thm_pb hn hN hs hsN hp0 hp1

/-- **Proposition `lt:prop:binomial`(c)**, the computed case `n ≤ 10`. -/
theorem binomial_c_comp_uncond {n N a b : ℕ} (hn : 2 ≤ n) (hn10 : n ≤ 10)
    (hN : 1 ≤ N) (hb : 0 < b) (hab : Nat.Coprime a b) (hN0 : b / Nat.gcd b n ≤ 12)
    (hp0 : 0 < (a : ℝ) / b) (hp1 : (a : ℝ) / b < 1)
    (hint : ∃ m : ℤ, (n : ℝ) * N * ((a : ℝ) / b) = m) (hlo : 1 / (n : ℝ) ≤ (a : ℝ) / b)
    (hhi : (a : ℝ) / b ≤ 1 - 1 / (n : ℝ)) :
    CompletelyMixable n (binom N ((a : ℝ) / b)) :=
  binomial_c_comp lem_count hn hn10 hN hb hab hN0 hp0 hp1 hint hlo hhi

/-- **Proposition `lt:prop:binomial`(c)**, all cases. -/
theorem binomial_c_uncond {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hint : ∃ m : ℤ, (n : ℝ) * N * p = m) (hlo : 1 / (n : ℝ) ≤ p) (hhi : p ≤ 1 - 1 / (n : ℝ))
    (hcase : (∃ m : ℤ, (n : ℝ) * p = m) ∨ N = 2 ∨
      (∃ j s : ℕ, p = (j : ℝ) / s ∧ s ≤ n ∧ s ∣ N) ∨
      (n ≤ 10 ∧ ∃ a b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ p = (a : ℝ) / b ∧ b / Nat.gcd b n ≤ 12)) :
    CompletelyMixable n (binom N p) :=
  binomial_c lem_count prop_three thm_pb hN hn hp0 hp1 hint hlo hhi hcase

/-- Remark `lt:rem:necessary`: the distribution `FA` is not `3`-completely mixable. -/
theorem not_mixA_uncond : ¬ CompletelyMixable 3 FA := not_mixA lem_count

/-- Remark `lt:rem:necessary`: the distribution `FB` is not `3`-completely mixable. -/
theorem not_mixB_uncond : ¬ CompletelyMixable 3 FB := not_mixB lem_count

/-- Remark `lt:rem:necessary`: the distribution `FC` is not `3`-completely mixable. -/
theorem not_mixC_uncond : ¬ CompletelyMixable 3 FC := not_mixC lem_count

open Mixes.NormAtom in
/-- **Remark `lt:rem:necessary`**: `FC` satisfies the listed necessary conditions but is not
`3`-completely mixable. -/
theorem remark_necessary_uncond :
    CxCond 3 FC 4 ∧ (∀ I : Finset (Fin 7), PeakCond 3 FC 4 (I.image (ptVal 6) : Set ℝ)) ∧
      CountLemCond 3 FC 4 6 ∧ CountLemCondRefl 3 FC 4 0 ∧ TailCond3Both FC 4 ∧
      ¬ CompletelyMixable 3 FC :=
  remark_necessary lem_count

end Uncond

end Mixes.LatticeBridge
