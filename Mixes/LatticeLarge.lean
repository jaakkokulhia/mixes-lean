import Mathlib
import Mixes.Defs
import Mixes.NormAtom

/-!
# Lattice distributions: complete mixability for large `n`, binomial distributions

Draft 14, Section `lt:sec:lattice`: Theorem `lt:thm:large`, Proposition `lt:prop:binomial` and the
proved claims of Remark `lt:rem:necessary`.

A distribution on finitely many points is described by an index type `ι` (finite), injective
points `val : ι → ℝ` and masses `f : ι → ℝ`; the measure is `discr val f = ∑ᵢ fᵢ δ_{valᵢ}`.

Lemma `lt:lem:count` (proved by another agent) enters as the hypothesis `H_lt_lem_count`.
-/

open MeasureTheory Finset

noncomputable section

namespace Mixes.LatticeLarge

open Mixes

section Defs

variable {ι : Type*} [Fintype ι]

/-- The distribution with the masses `f i` at the points `val i`. -/
def discr (val f : ι → ℝ) : Measure ℝ := ∑ i, ENNReal.ofReal (f i) • Measure.dirac (val i)

/-- Its mean. -/
def mean (val f : ι → ℝ) : ℝ := ∑ i, val i * f i

/-- A natural vector as a real vector. -/
def natVec (k : ι → ℕ) : ι → ℝ := fun i => (k i : ℝ)

/-- An integer vector as a real vector. -/
def intVec (k : ι → ℤ) : ι → ℝ := fun i => (k i : ℝ)

/-- The set `𝒦_n` of count vectors with `∑ k = n` and `∑ val·k = m` (as real vectors). -/
def countVecs (val : ι → ℝ) (n : ℕ) (m : ℝ) : Set (ι → ℝ) :=
  {y | ∃ k : ι → ℕ, y = natVec k ∧ ∑ i, k i = n ∧ ∑ i, val i * (k i : ℝ) = m}

/-- The criterion of Lemma `lt:lem:count`: `f` is a convex combination of the vectors `k / n`,
`k ∈ 𝒦_n` (with `m = n μ`). -/
def CountCond (val f : ι → ℝ) (n : ℕ) : Prop :=
  f ∈ convexHull ℝ ((fun y => (n : ℝ)⁻¹ • y) '' countVecs val n (n * mean val f))

/-- The lattice `Λ` of integer vectors with `∑ k = 0` and `∑ val·k = 0`. -/
def lam (val : ι → ℝ) : Set (ι → ℤ) := {k | ∑ i, k i = 0 ∧ ∑ i, val i * (k i : ℝ) = 0}

/-- Its real span `Λ_ℝ`. -/
def lamR (val : ι → ℝ) : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (intVec '' lam val)

/-- `y ∈ ℤ^S + Λ_ℝ`. -/
def IntPlusLamR (val : ι → ℝ) (y : ι → ℝ) : Prop := ∃ k : ι → ℤ, y - intVec k ∈ lamR val

end Defs

/-- **Lemma `lt:lem:count`** (Theorem 3.2 of Puccetti, Wang and Wang 2012), as a hypothesis: a
distribution with masses `f ≥ 0` (sum `1`) at distinct points `val i` is `n`-completely mixable if
and only if `f` is a convex combination of the vectors `k / n`, `k ∈ 𝒦_n`. -/
def H_lt_lem_count : Prop :=
  ∀ (ι : Type) [Fintype ι] (val f : ι → ℝ), Function.Injective val → (∀ i, 0 ≤ f i) →
    ∑ i, f i = 1 → ∀ n : ℕ, 2 ≤ n → (CompletelyMixable n (discr val f) ↔ CountCond val f n)

section Lattice

variable {ι : Type*} [Fintype ι]

/-- Both sums vanish on `Λ_ℝ`. -/
lemma lamR_sums {val : ι → ℝ} {y : ι → ℝ} (hy : y ∈ lamR val) :
    ∑ i, y i = 0 ∧ ∑ i, val i * y i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, ⟨h1, h2⟩, rfl⟩ := hx
    refine ⟨?_, h2⟩
    simp only [intVec]; exact_mod_cast h1
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · simp [Finset.sum_add_distrib, hx.1, hy.1]
    · simp [mul_add, Finset.sum_add_distrib, hx.2, hy.2]
  | smul a x _ hx =>
    refine ⟨?_, ?_⟩
    · simp [← Finset.mul_sum, hx.1]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [show ∑ i, val i * (a * x i) = a * ∑ i, val i * x i by
        rw [Finset.mul_sum]; congr 1; ext i; ring, hx.2, mul_zero]

lemma intVec_mem_lamR {val : ι → ℝ} {k : ι → ℤ} (hk : k ∈ lam val) : intVec k ∈ lamR val :=
  Submodule.subset_span ⟨k, hk, rfl⟩

/-- **Theorem `lt:thm:large`(a).** If `F` is `n`-completely mixable, then `n f ∈ ℤ^S + Λ_ℝ`. -/
theorem large_a (hc : H_lt_lem_count) {ι : Type} [Fintype ι] (val f : ι → ℝ)
    (hinj : Function.Injective val) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) (n : ℕ)
    (hn : 2 ≤ n) (hmix : CompletelyMixable n (discr val f)) :
    IntPlusLamR val ((n : ℝ) • f) := by
  have hcc := (hc ι val f hinj hf0 hf1 n hn).1 hmix
  unfold CountCond at hcc
  obtain ⟨y0, hy0⟩ : (countVecs val n (n * mean val f)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.image_empty, convexHull_empty] at hcc
    exact hcc
  obtain ⟨k0, rfl, hk0s, hk0m⟩ := hy0
  refine ⟨fun i => (k0 i : ℤ), ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by have : (2:ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  let T : Set (ι → ℝ) := {y | (n : ℝ) • y - intVec (fun i => (k0 i : ℤ)) ∈ lamR val}
  have hT : Convex ℝ T := by
    intro y1 h1 y2 h2 a b ha hb hab
    have e : (n : ℝ) • (a • y1 + b • y2) - intVec (fun i => (k0 i : ℤ)) =
        a • ((n : ℝ) • y1 - intVec (fun i => (k0 i : ℤ))) +
          b • ((n : ℝ) • y2 - intVec (fun i => (k0 i : ℤ))) := by
      ext i
      simp only [intVec, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Int.cast_natCast]
      linear_combination (k0 i : ℝ) * hab
    show _ ∈ lamR val
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  have hsub : (fun y => (n : ℝ)⁻¹ • y) '' countVecs val n (n * mean val f) ⊆ T := by
    rintro _ ⟨_, ⟨k, rfl, hks, hkm⟩, rfl⟩
    show (n : ℝ) • (n : ℝ)⁻¹ • natVec k - intVec (fun i => (k0 i : ℤ)) ∈ lamR val
    rw [smul_smul, mul_inv_cancel₀ hn0, one_smul]
    have : natVec k - intVec (fun i => (k0 i : ℤ)) = intVec (fun i => (k i : ℤ) - k0 i) := by
      ext i; simp [natVec, intVec]
    rw [this]
    apply intVec_mem_lamR
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_sub_distrib, ← Nat.cast_sum, hks, hk0s, sub_self]
    · simp only [Int.cast_sub, Int.cast_natCast, mul_sub, Finset.sum_sub_distrib]
      rw [hkm, hk0m, sub_self]
  exact convexHull_min hsub hT hcc

/-- **Theorem `lt:thm:large`(b).** Let `b₁, …, b_ρ` be vectors of `Λ` whose real span contains
`Λ_ℝ` (for instance a basis of `Λ`), and `βₓ = ∑ⱼ |b_{j,x}|`. If `n f ∈ ℤ^S + Λ_ℝ` and
`n fₓ ≥ βₓ` for all `x`, then `F` is `n`-completely mixable. -/
theorem large_b (hc : H_lt_lem_count) {ι : Type} [Fintype ι] (val f : ι → ℝ)
    (hinj : Function.Injective val) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) (n : ℕ)
    (hn : 2 ≤ n) {ρ : ℕ} (b : Fin ρ → ι → ℤ) (hb : ∀ j, b j ∈ lam val)
    (hspan : lamR val ≤ Submodule.span ℝ (Set.range fun j => intVec (b j)))
    (hint : IntPlusLamR val ((n : ℝ) • f)) (hbeta : ∀ i, ∑ j, |(b j i : ℝ)| ≤ n * f i) :
    CompletelyMixable n (discr val f) := by
  apply (hc ι val f hinj hf0 hf1 n hn).2
  have hn0 : (n : ℝ) ≠ 0 := by have : (2:ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  obtain ⟨k0, hw⟩ := hint
  have hk0sums := lamR_sums hw
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan hw)
  have ht' : ∀ i, (n : ℝ) * f i = k0 i + ∑ j, t j * b j i := by
    intro i
    have := congrFun ht i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, intVec, Pi.sub_apply] at this
    linarith
  -- the affine map `c ↦ (k0 + ∑ c_j b_j) / n`
  let A : (Fin ρ → ℝ) → ι → ℝ := fun c i => (n : ℝ)⁻¹ * (k0 i + ∑ j, c j * b j i)
  let H := convexHull ℝ ((fun y => (n : ℝ)⁻¹ • y) '' countVecs val n (n * mean val f))
  let W : Set (Fin ρ → ℝ) := {c | A c ∈ H}
  have hW : Convex ℝ W := by
    intro c1 h1 c2 h2 a b' ha hb hab
    have e : A (a • c1 + b' • c2) = a • A c1 + b' • A c2 := by
      ext i
      have e1 : ∑ j, (a * c1 j + b' * c2 j) * (b j i : ℝ) =
          a * ∑ j, c1 j * b j i + b' * ∑ j, c2 j * b j i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1; ext j; ring
      simp only [A, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e1]
      linear_combination -(n : ℝ)⁻¹ * (k0 i : ℝ) * hab
    show A (a • c1 + b' • c2) ∈ H
    rw [e]
    exact convex_convexHull ℝ _ h1 h2 ha hb hab
  -- the vertices of the box around `t` lie in `W`
  let V : Set (Fin ρ → ℝ) := Set.pi Set.univ fun j => {(⌊t j⌋ : ℝ), (⌊t j⌋ : ℝ) + 1}
  have hV : V ⊆ W := by
    intro c hcV
    have hm : ∀ j, ∃ m : ℤ, c j = m ∧ |c j - t j| ≤ 1 := by
      intro j
      have hj := hcV j (Set.mem_univ j)
      have h1 := Int.floor_le (t j)
      have h2 := Int.lt_floor_add_one (t j)
      rcases hj with hj | hj
      · exact ⟨⌊t j⌋, hj, by rw [hj, abs_le]; constructor <;> linarith⟩
      · exact ⟨⌊t j⌋ + 1, by rw [hj]; push_cast; ring, by rw [hj, abs_le]; constructor <;> linarith⟩
    choose m hmc hmt using hm
    let d : ι → ℝ := ∑ j, (c j - t j) • intVec (b j)
    have hd : d ∈ lamR val :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (intVec_mem_lamR (hb j))
    have hdsums := lamR_sums hd
    have hdi : ∀ i, d i = ∑ j, (c j - t j) * b j i := by
      intro i; simp [d, intVec, Finset.sum_apply]
    let κz : ι → ℤ := fun i => k0 i + ∑ j, m j * b j i
    have hκ : ∀ i, (κz i : ℝ) = n * f i + d i := by
      intro i
      simp only [κz, Int.cast_add, Int.cast_sum, Int.cast_mul, hdi, ht' i]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1; congr 1; ext j; rw [hmc j]; ring
    have hκ0 : ∀ i, 0 ≤ κz i := by
      intro i
      have hle : |d i| ≤ ∑ j, |(b j i : ℝ)| := by
        rw [hdi]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hmt j)
      have : (0 : ℝ) ≤ κz i := by
        rw [hκ i]; have := neg_abs_le (d i); linarith [hbeta i]
      exact_mod_cast this
    let κ : ι → ℕ := fun i => (κz i).toNat
    have hκn : natVec κ = (n : ℝ) • f + d := by
      ext i
      simp only [natVec, κ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hκ i]; exact_mod_cast Int.toNat_of_nonneg (hκ0 i)
    show A c ∈ H
    apply subset_convexHull
    refine ⟨natVec κ, ⟨κ, rfl, ?_, ?_⟩, ?_⟩
    · have : (∑ i, (κ i : ℝ)) = n := by
        have := congrArg (fun y : ι → ℝ => ∑ i, y i) hκn
        simp only [natVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hf1, hdsums.1]; ring
      exact_mod_cast this
    · have := congrArg (fun y : ι → ℝ => ∑ i, val i * y i) hκn
      simp only [natVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, mean]
      simp only [mul_add, Finset.sum_add_distrib, hdsums.2, add_zero, Finset.mul_sum]
      congr 1; ext i; ring
    · ext i
      simp only [A, Pi.smul_apply, smul_eq_mul]
      rw [hκn]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdi, ht' i]
      congr 1
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1; congr 1; ext j; rw [hmc j]; ring
  have hbox : t ∈ convexHull ℝ V := by
    rw [convexHull_pi]
    intro j _
    show t j ∈ convexHull ℝ {_, _}
    rw [convexHull_pair, segment_eq_Icc (by linarith)]
    exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  have htW := convexHull_min hV hW hbox
  have hAt : A t = f := by
    ext i
    simp only [A]
    rw [← ht' i, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have : A t ∈ H := htW
  rwa [hAt] at this

/-- `Λ` as a `ℤ`-submodule of `ℤ^ι`. -/
def lamZ (val : ι → ℝ) : Submodule ℤ (ι → ℤ) where
  carrier := lam val
  add_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · simp [Finset.sum_add_distrib, ha.1, hb.1]
    · simp [mul_add, Finset.sum_add_distrib, ha.2, hb.2]
  zero_mem' := by simp [lam]
  smul_mem' := by
    intro c a ha
    refine ⟨?_, ?_⟩
    · simp [← Finset.mul_sum, ha.1]
    · simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      rw [show ∑ i, val i * ((c : ℝ) * a i) = c * ∑ i, val i * a i by
        rw [Finset.mul_sum]; congr 1; ext i; ring, ha.2, mul_zero]

/-- `Λ` has a basis (it is a subgroup of `ℤ^ι`), and a basis spans `Λ_ℝ`. -/
theorem exists_lam_basis (val : ι → ℝ) :
    ∃ (ρ : ℕ) (b : Fin ρ → ι → ℤ), (∀ j, b j ∈ lam val) ∧
      lamR val ≤ Submodule.span ℝ (Set.range fun j => intVec (b j)) := by
  obtain ⟨ρ, B⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) (lamZ val)
  refine ⟨ρ, fun j => (B j : ι → ℤ), fun j => (B j).2, ?_⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hsum := B.sum_repr ⟨k, hk⟩
  have hk' : k = ∑ j, B.repr ⟨k, hk⟩ j • (B j : ι → ℤ) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  have : intVec k = ∑ j, ((B.repr ⟨k, hk⟩ j : ℤ) : ℝ) • intVec (B j : ι → ℤ) := by
    conv_lhs => rw [hk']
    ext i
    simp [intVec, Finset.sum_apply]
  rw [SetLike.mem_coe, this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Theorem `lt:thm:large`(b), second statement.** If all masses are positive, `F` is
`n`-completely mixable for all sufficiently large `n` with `n f ∈ ℤ^S + Λ_ℝ`, and (by (a)) for no
other `n`. -/
theorem large_eventually (hc : H_lt_lem_count) {ι : Type} [Fintype ι] (val f : ι → ℝ)
    (hinj : Function.Injective val) (hfpos : ∀ i, 0 < f i) (hf1 : ∑ i, f i = 1) :
    ∃ N : ℕ, ∀ n : ℕ, 2 ≤ n →
      (CompletelyMixable n (discr val f) → IntPlusLamR val ((n : ℝ) • f)) ∧
      (N ≤ n → IntPlusLamR val ((n : ℝ) • f) → CompletelyMixable n (discr val f)) := by
  obtain ⟨ρ, b, hb, hspan⟩ := exists_lam_basis val
  let β : ι → ℝ := fun i => ∑ j, |(b j i : ℝ)|
  refine ⟨⌈∑ i, β i / f i⌉₊, fun n hn => ⟨large_a hc val f hinj (fun i => (hfpos i).le) hf1 n hn,
    fun hN hint => large_b hc val f hinj (fun i => (hfpos i).le) hf1 n hn b hb hspan hint ?_⟩⟩
  intro i
  have h1 : β i / f i ≤ ∑ i, β i / f i :=
    Finset.single_le_sum (f := fun i => β i / f i)
      (fun i _ => div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (hfpos i).le)
      (Finset.mem_univ i)
  have h2 : ∑ i, β i / f i ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h3 : β i / f i ≤ n := h1.trans h2
  rw [div_le_iff₀ (hfpos i)] at h3
  linarith

/-- **Theorem `lt:thm:large`(c), first statement.** If the points are integers `z i` whose
differences generate `ℤ` (their greatest common divisor is `1`), then `n f ∈ ℤ^S + Λ_ℝ` if and only
if `n μ` is an integer. (The paper assumes at least three points; two points with difference `1`
are covered as well.) -/
theorem large_c_int [DecidableEq ι] (z : ι → ℤ)
    (hgen : Ideal.span (Set.range fun p : ι × ι => z p.1 - z p.2) = ⊤) (f : ι → ℝ)
    (hf1 : ∑ i, f i = 1) (n : ℕ) :
    IntPlusLamR (fun i => (z i : ℝ)) ((n : ℝ) • f) ↔
      ∃ m : ℤ, (n : ℝ) * mean (fun i => (z i : ℝ)) f = m := by
  constructor
  · rintro ⟨k, hk⟩
    have h2 := (lamR_sums hk).2
    refine ⟨∑ i, z i * k i, ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intVec, mul_sub,
      Finset.sum_sub_distrib] at h2
    rw [mean, Finset.mul_sum]
    push_cast
    rw [← sub_eq_zero, ← h2]
    congr 1; congr 1; ext i; ring
  · rintro ⟨m, hm⟩
    have h1 : (1 : ℤ) ∈ Ideal.span (Set.range fun p : ι × ι => z p.1 - z p.2) := by
      rw [hgen]; exact Submodule.mem_top
    obtain ⟨c, hc1⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
    obtain ⟨i0⟩ : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hf1
      exact zero_ne_one hf1
    let u : ι → ℤ := fun i =>
      ∑ p, c p * ((if p.1 = i then 1 else 0) - (if p.2 = i then 1 else 0))
    have hu0 : ∑ i, u i = 0 := by
      simp only [u]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro p _
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp
    have key : ∀ p : ι × ι, ∑ i, z i * (c p * ((if p.1 = i then 1 else 0) -
        (if p.2 = i then 1 else 0))) = c p * (z p.1 - z p.2) := by
      intro p
      rw [show ∑ i, z i * (c p * ((if p.1 = i then 1 else 0) - (if p.2 = i then 1 else 0))) =
        c p * (∑ i, (if p.1 = i then z i else 0) - ∑ i, (if p.2 = i then z i else 0)) by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          congr 1; ext i; split_ifs <;> ring]
      simp
    have hu1 : ∑ i, z i * u i = 1 := by
      simp only [u, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [key]
      exact hc1
    let k : ι → ℤ := fun i => (m - n * z i0) * u i + (if i = i0 then (n : ℤ) else 0)
    refine ⟨k, ?_⟩
    set w : ι → ℝ := (n : ℝ) • f - intVec k with hw
    have hws : ∑ i, w i = 0 := by
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intVec, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hf1, k]
      push_cast
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have : ∑ i, ((u i : ℤ) : ℝ) = 0 := by exact_mod_cast hu0
      rw [this]; simp
    have hwz : ∑ i, (z i : ℝ) * w i = 0 := by
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intVec, mul_sub,
        Finset.sum_sub_distrib, k]
      have e1 : ∑ i, (z i : ℝ) * (n * f i) = n * mean (fun i => (z i : ℝ)) f := by
        rw [mean, Finset.mul_sum]; congr 1; ext i; ring
      have e2 : ∑ i, (z i : ℝ) * (((m - n * z i0) * u i + (if i = i0 then (n : ℤ) else 0) : ℤ) : ℝ)
          = ((∑ i, z i * ((m - n * z i0) * u i + (if i = i0 then (n : ℤ) else 0)) : ℤ) : ℝ) := by
        push_cast; rfl
      rw [e1, e2, hm]
      have : ∑ i, z i * ((m - n * z i0) * u i + (if i = i0 then (n : ℤ) else 0)) = m := by
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        rw [show ∑ i, z i * ((m - n * z i0) * u i) = (m - n * z i0) * ∑ i, z i * u i by
          rw [Finset.mul_sum]; congr 1; ext i; ring, hu1]
        ring
      rw [this, sub_self]
    let v : ι → ι → ℤ := fun i j =>
      (if j = i then 1 else 0) - (if j = i0 then 1 else 0) - (z i - z i0) * u j
    have hv : ∀ i, v i ∈ lam (fun i => (z i : ℝ)) := by
      intro i
      have s1 : ∑ j, v i j = 0 := by
        simp only [v, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          ← Finset.mul_sum, hu0]
        ring
      have s2 : ∑ j, z j * v i j = 0 := by
        simp only [v, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [show ∑ j, z j * ((z i - z i0) * u j) = (z i - z i0) * ∑ j, z j * u j by
          rw [Finset.mul_sum]; congr 1; ext j; ring, hu1]
        ring
      refine ⟨s1, ?_⟩
      show ∑ j, (z j : ℝ) * (v i j : ℝ) = 0
      exact_mod_cast s2
    have hdec : w = ∑ i, w i • intVec (v i) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, intVec, v]
      push_cast
      simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      have e3 : ∑ i, w i * (((z i : ℝ) - z i0) * u j) =
          (∑ i, (z i : ℝ) * w i - z i0 * ∑ i, w i) * u j := by
        rw [sub_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        congr 1; ext i; ring
      rw [e3, hwz, hws]
      split_ifs <;> simp [hws]
    rw [hdec]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (intVec_mem_lamR (hv i))

/-- On two points the lattice is trivial. -/
lemma lam_two {val : Fin 2 → ℝ} (hinj : Function.Injective val) {k : Fin 2 → ℤ}
    (hk : k ∈ lam val) : k = 0 := by
  obtain ⟨h1, h2⟩ := hk
  rw [Fin.sum_univ_two] at h1 h2
  have hne : val 0 - val 1 ≠ 0 := sub_ne_zero.2 (hinj.ne (by decide))
  have h1' : (k 1 : ℝ) = -k 0 := by
    have : ((k 0 + k 1 : ℤ) : ℝ) = 0 := by exact_mod_cast h1
    push_cast at this; linarith
  rw [h1'] at h2
  have : (val 0 - val 1) * (k 0 : ℝ) = 0 := by linarith
  have hk0 : (k 0 : ℝ) = 0 := (mul_eq_zero.1 this).resolve_left hne
  have hk1 : (k 1 : ℝ) = 0 := by rw [h1', hk0, neg_zero]
  ext i; fin_cases i
  · exact_mod_cast hk0
  · exact_mod_cast hk1

lemma lamR_two {val : Fin 2 → ℝ} (hinj : Function.Injective val) : lamR val = ⊥ := by
  rw [lamR, Submodule.span_eq_bot]
  rintro _ ⟨k, hk, rfl⟩
  rw [lam_two hinj hk]; ext i; simp [intVec]

/-- **Theorem `lt:thm:large`(c), second statement.** A distribution on two points is
`n`-completely mixable if and only if the numbers `n fₓ` are integers. -/
theorem large_c_two (hc : H_lt_lem_count) (val f : Fin 2 → ℝ) (hinj : Function.Injective val)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) (n : ℕ) (hn : 2 ≤ n) :
    CompletelyMixable n (discr val f) ↔ ∀ i, ∃ m : ℤ, (n : ℝ) * f i = m := by
  constructor
  · intro hmix i
    obtain ⟨k, hk⟩ := large_a hc val f hinj hf0 hf1 n hn hmix
    rw [lamR_two hinj, Submodule.mem_bot] at hk
    refine ⟨k i, ?_⟩
    have := congrFun hk i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intVec, Pi.zero_apply] at this
    linarith
  · intro hm
    choose m hm using hm
    refine large_b hc val f hinj hf0 hf1 n hn (ρ := 0) (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) (by rw [lamR_two hinj]; exact bot_le) ⟨m, ?_⟩ ?_
    · have : (n : ℝ) • f - intVec m = 0 := by
        ext i; simp [intVec, hm i]
      rw [this]; exact zero_mem _
    · intro i; simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact mul_nonneg (Nat.cast_nonneg _) (hf0 i)

end Lattice

section Binomial

/-! ## Binomial distributions -/

/-- The points `0, 1, …, N`. -/
def binomVal (N : ℕ) : Fin (N + 1) → ℝ := fun x => ((x : ℕ) : ℝ)

/-- The masses of `B(N, p)`. -/
def binomMass (N : ℕ) (p : ℝ) : Fin (N + 1) → ℝ :=
  fun x => (N.choose x : ℝ) * p ^ (x : ℕ) * (1 - p) ^ (N - x)

/-- The binomial distribution `B(N, p)`. -/
def binom (N : ℕ) (p : ℝ) : Measure ℝ := discr (binomVal N) (binomMass N p)

lemma binomVal_inj (N : ℕ) : Function.Injective (binomVal N) := by
  intro x y h
  simp only [binomVal, Nat.cast_inj] at h
  exact Fin.ext h

lemma binomMass_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin (N + 1)) :
    0 ≤ binomMass N p x := by
  unfold binomMass
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma binomMass_sum (N : ℕ) (p : ℝ) : ∑ x, binomMass N p x = 1 := by
  have := Fin.sum_univ_eq_sum_range (fun x => (N.choose x : ℝ) * p ^ x * (1 - p) ^ (N - x)) (N + 1)
  simp only [binomMass]
  rw [this]
  calc _ = (p + (1 - p)) ^ N := by rw [add_pow]; exact Finset.sum_congr rfl (fun x _ => by ring)
    _ = 1 := by ring

lemma binom_mean (N : ℕ) (p : ℝ) : mean (binomVal N) (binomMass N p) = N * p := by
  unfold mean
  have := Fin.sum_univ_eq_sum_range
    (fun x => (x : ℝ) * ((N.choose x : ℝ) * p ^ x * (1 - p) ^ (N - x))) (N + 1)
  simp only [binomVal, binomMass]
  rw [this]
  rcases N with _ | M
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have e : ∀ y ∈ Finset.range (M + 1),
        ((y + 1 : ℕ) : ℝ) * (((M + 1).choose (y + 1) : ℕ) * p ^ (y + 1) * (1 - p) ^ (M + 1 - (y + 1)))
          = ((M + 1 : ℕ) : ℝ) * p * ((M.choose y : ℝ) * p ^ y * (1 - p) ^ (M - y)) := by
      intro y _
      have hc : ((M + 1 : ℕ) : ℝ) * (M.choose y : ℝ) = ((M + 1).choose (y + 1) : ℝ) * ((y + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq M y
      rw [show M + 1 - (y + 1) = M - y by omega]
      linear_combination (p ^ (y + 1) * (1 - p) ^ (M - y)) * hc.symm
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    rw [show ∑ y ∈ Finset.range (M + 1), (M.choose y : ℝ) * p ^ y * (1 - p) ^ (M - y) = 1 by
      calc _ = (p + (1 - p)) ^ M := by
            rw [add_pow]; exact Finset.sum_congr rfl (fun x _ => by ring)
        _ = 1 := by ring]
    push_cast; ring

/-- If `f` is a convex combination of the vectors `k / n` and `f i > 0`, some count vector has
`k i ≥ 1`. -/
lemma exists_count_pos {ι : Type*} [Fintype ι] {val f : ι → ℝ} {n : ℕ} (h : CountCond val f n)
    {i : ι} (hi : 0 < f i) :
    ∃ k : ι → ℕ, ∑ j, k j = n ∧ ∑ j, val j * (k j : ℝ) = n * mean val f ∧ 1 ≤ k i := by
  by_contra hne
  push Not at hne
  have hsub : (fun y => (n : ℝ)⁻¹ • y) '' countVecs val n (n * mean val f) ⊆ {y | y i ≤ 0} := by
    rintro _ ⟨_, ⟨k, rfl, hks, hkm⟩, rfl⟩
    have : k i = 0 := by have := hne k hks hkm; omega
    simp [natVec, this]
  have hconv : Convex ℝ {y : ι → ℝ | y i ≤ 0} := by
    intro y1 h1 y2 h2 a b ha hb _
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    nlinarith
  have := convexHull_min hsub hconv h
  simp only [Set.mem_ofPred_eq] at this
  linarith

lemma countVecs_nonempty {ι : Type*} [Fintype ι] {val f : ι → ℝ} {n : ℕ} (h : CountCond val f n) :
    ∃ k : ι → ℕ, ∑ j, k j = n ∧ ∑ j, val j * (k j : ℝ) = n * mean val f := by
  by_contra hne
  push Not at hne
  have : countVecs val n (n * mean val f) = ∅ := by
    ext y; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨k, rfl, hk1, hk2⟩; exact hne k hk1 hk2
  unfold CountCond at h
  rw [this, Set.image_empty, convexHull_empty] at h
  exact h

/-- **Proposition `lt:prop:binomial`(a).** If `B(N, p)` is `n`-completely mixable, then `nNp` is an
integer and `1/n ≤ p ≤ 1 - 1/n`. -/
theorem binomial_a (hc : H_lt_lem_count) {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hmix : CompletelyMixable n (binom N p)) :
    (∃ m : ℤ, (n : ℝ) * N * p = m) ∧ 1 / (n : ℝ) ≤ p ∧ p ≤ 1 - 1 / (n : ℝ) := by
  have hcc := (hc (Fin (N + 1)) (binomVal N) (binomMass N p) (binomVal_inj N)
    (binomMass_nonneg hp0.le hp1.le) (binomMass_sum N p) n hn).1 hmix
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨k, h2, h3⟩ := countVecs_nonempty hcc
    rw [binom_mean] at h3
    refine ⟨∑ x : Fin (N + 1), ((x : ℕ) * k x : ℤ), ?_⟩
    rw [show (n : ℝ) * N * p = n * (N * p) by ring, ← h3]; push_cast; simp [binomVal]
  · -- a count vector with a value `N`
    have hpos : 0 < binomMass N p (Fin.last N) := by
      simp only [binomMass, Fin.val_last, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        pow_zero, mul_one]
      positivity
    obtain ⟨k, h2, h3, hk⟩ := exists_count_pos hcc hpos
    rw [binom_mean] at h3
    have hge : (N : ℝ) ≤ ∑ x, binomVal N x * (k x : ℝ) := by
      have := Finset.single_le_sum (f := fun x => binomVal N x * (k x : ℝ))
        (fun x _ => mul_nonneg (by simp [binomVal]) (Nat.cast_nonneg _)) (Finset.mem_univ (Fin.last N))
      refine le_trans ?_ this
      simp only [binomVal, Fin.val_last]
      have : (1 : ℝ) ≤ k (Fin.last N) := by exact_mod_cast hk
      nlinarith
    rw [h3] at hge
    rw [div_le_iff₀ hnpos]
    nlinarith
  · -- a count vector with a value `0`
    have hpos : 0 < binomMass N p 0 := by
      simp only [binomMass, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero,
        Nat.sub_zero]
      have : 0 < 1 - p := by linarith
      positivity
    obtain ⟨k, h2, h3, hk⟩ := exists_count_pos hcc hpos
    rw [binom_mean] at h3
    have hle : ∑ x, binomVal N x * (k x : ℝ) ≤ N * ((n : ℝ) - 1) := by
      have e : ∀ x ∈ Finset.univ, binomVal N x * (k x : ℝ) ≤
          N * (k x : ℝ) - (if x = 0 then (N : ℝ) * k x else 0) := by
        intro x _
        by_cases hx : x = 0
        · subst hx; simp [binomVal]
        · simp only [hx, ite_false, sub_zero, binomVal]
          have : ((x : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 x.2
          exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      refine (Finset.sum_le_sum e).trans ?_
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      have hs : (∑ x, (k x : ℝ)) = n := by exact_mod_cast h2
      rw [hs]
      have : (1 : ℝ) ≤ k 0 := by exact_mod_cast hk
      nlinarith
    rw [h3] at hle
    have : (n : ℝ) * p ≤ (n : ℝ) - 1 := by
      have := mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.2 hNpos))
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul] at this
      nlinarith
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hnpos]
    nlinarith

/-- The sum of independent complete mixes is a complete mix of the convolution. -/
theorem cm_add {n : ℕ} {μ ν : Measure ℝ} (h1 : CompletelyMixable n μ)
    (h2 : CompletelyMixable n ν) :
    CompletelyMixable n ((μ.prod ν).map (fun q => q.1 + q.2)) := by
  obtain ⟨P1, hP1, ⟨s1, hs1⟩, hm1⟩ := h1
  obtain ⟨P2, hP2, ⟨s2, hs2⟩, hm2⟩ := h2
  have := hP1; have := hP2
  refine ⟨(P1.prod P2).map (fun q => q.1 + q.2), ?_, ⟨s1 + s2, ?_⟩, ?_⟩
  · infer_instance
  · rw [ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := P1) (ν := P2)).ae hs1
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := P1) (ν := P2)).ae hs2
    filter_upwards [a1, a2] with q hq1 hq2
    simp only [Pi.add_apply, Finset.sum_add_distrib, hq1, hq2]
  · intro j
    rw [Measure.map_map (measurable_pi_apply j) (by fun_prop)]
    have e : (fun x : Fin n → ℝ => x j) ∘ (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2) =
        (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (fun x : Fin n → ℝ => x j) (fun x => x j) := by
      ext q; simp
    rw [e, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_prod_map _ _ (measurable_pi_apply j) (measurable_pi_apply j), hm1 j, hm2 j]

/-- The summand in `vandermonde_sum`. -/
def vT (N1 N2 : ℕ) (p : ℝ) (g : ℕ → ℝ) (ij : ℕ × ℕ) : ℝ :=
  ((N1.choose ij.1 : ℝ) * p ^ ij.1 * (1 - p) ^ (N1 - ij.1)) *
    ((N2.choose ij.2 : ℝ) * p ^ ij.2 * (1 - p) ^ (N2 - ij.2)) * g (ij.1 + ij.2)

/-- Vandermonde's identity in the form needed for `B(N₁, p) * B(N₂, p) = B(N₁ + N₂, p)`. -/
lemma vandermonde_sum (N1 N2 : ℕ) (p : ℝ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range (N1 + 1), ∑ j ∈ Finset.range (N2 + 1),
      ((N1.choose i : ℝ) * p ^ i * (1 - p) ^ (N1 - i)) *
        ((N2.choose j : ℝ) * p ^ j * (1 - p) ^ (N2 - j)) * g (i + j) =
    ∑ x ∈ Finset.range (N1 + N2 + 1),
      ((N1 + N2).choose x : ℝ) * p ^ x * (1 - p) ^ (N1 + N2 - x) * g x := by
  have hR : ∀ x, ((N1 + N2).choose x : ℝ) * p ^ x * (1 - p) ^ (N1 + N2 - x) * g x =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal x, vT N1 N2 p g ij := by
    intro x
    rw [Nat.add_choose_eq]; push_cast
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    simp only [vT]
    by_cases h1 : ij.1 ≤ N1
    · by_cases h2 : ij.2 ≤ N2
      · rw [← hij, show N1 + N2 - (ij.1 + ij.2) = (N1 - ij.1) + (N2 - ij.2) by omega, pow_add,
          pow_add]
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : N2 < ij.2)]; simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : N1 < ij.1)]; simp
  rw [Finset.sum_congr rfl fun x _ => hR x, ← Finset.sum_biUnion]
  · show ∑ i ∈ Finset.range (N1 + 1), ∑ j ∈ Finset.range (N2 + 1), vT N1 N2 p g (i, j) = _
    rw [← Finset.sum_product]
    apply Finset.sum_subset
    · intro ij hij
      simp only [Finset.mem_product, Finset.mem_range] at hij
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
      exact ⟨ij.1 + ij.2, by omega, rfl⟩
    · intro ij _ hn
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hn
      simp only [vT]
      rcases hn with h | h
      · rw [Nat.choose_eq_zero_of_lt (by omega : N1 < ij.1)]; simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : N2 < ij.2)]; simp
  · intro x _ y _ hxy
    exact Finset.disjoint_left.2 fun ij h1 h2 =>
      hxy ((Finset.HasAntidiagonal.mem_antidiagonal.1 h1).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.1 h2))

lemma indicator_one_ennreal (S : Set ℝ) (y : ℝ) :
    S.indicator (1 : ℝ → ENNReal) y = ENNReal.ofReal (S.indicator (1 : ℝ → ℝ) y) := by
  by_cases h : y ∈ S <;> simp [h]

lemma discr_isProb {ι : Type*} [Fintype ι] {val f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∑ i, f i = 1) : IsProbabilityMeasure (discr val f) := by
  constructor
  simp only [discr, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hf0 i), hf1, ENNReal.ofReal_one]

instance binom_isProb (N : ℕ) (p : ℝ) [Fact (0 ≤ p ∧ p ≤ 1)] : IsProbabilityMeasure (binom N p) :=
  discr_isProb (binomMass_nonneg (Fact.out : 0 ≤ p ∧ p ≤ 1).1 (Fact.out : 0 ≤ p ∧ p ≤ 1).2)
    (binomMass_sum N p)

/-- `B(N₁, p) * B(N₂, p) = B(N₁ + N₂, p)`. -/
theorem binom_conv (N1 N2 : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((binom N1 p).prod (binom N2 p)).map (fun q => q.1 + q.2) = binom (N1 + N2) p := by
  have : Fact (0 ≤ p ∧ p ≤ 1) := ⟨⟨hp0, hp1⟩⟩
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA, Measure.prod_apply (hA.preimage (by fun_prop))]
  simp only [binom, discr, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply, indicator_one_ennreal]
  have hm1 := binomMass_nonneg (N := N1) hp0 hp1
  have hm2 := binomMass_nonneg (N := N2) hp0 hp1
  have hm3 := binomMass_nonneg (N := N1 + N2) hp0 hp1
  have hind : ∀ y, 0 ≤ A.indicator (1 : ℝ → ℝ) y := fun y => Set.indicator_nonneg (by simp) y
  have hL : ∀ i : Fin (N1 + 1), ENNReal.ofReal (binomMass N1 p i) * ∑ j : Fin (N2 + 1),
      ENNReal.ofReal (binomMass N2 p j) * ENNReal.ofReal ((Prod.mk (binomVal N1 i) ⁻¹'
        (fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' A).indicator 1 (binomVal N2 j)) =
      ENNReal.ofReal (binomMass N1 p i * ∑ j : Fin (N2 + 1),
        binomMass N2 p j * A.indicator 1 (binomVal N1 i + binomVal N2 j)) := by
    intro i
    rw [ENNReal.ofReal_mul (hm1 i), ENNReal.ofReal_sum_of_nonneg
      (fun j _ => mul_nonneg (hm2 j) (hind _))]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul (hm2 j)]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hL i]
  simp_rw [← ENNReal.ofReal_mul (hm3 _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hm3 j) (hind _)),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hm1 i)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hm2 j) (hind _)))]
  congr 1
  have e1 := Fin.sum_univ_eq_sum_range (fun x =>
    ((N1 + N2).choose x : ℝ) * p ^ x * (1 - p) ^ (N1 + N2 - x) * A.indicator 1 (x : ℝ)) (N1 + N2 + 1)
  simp only [binomMass, binomVal]
  rw [e1, ← vandermonde_sum N1 N2 p (fun x => A.indicator 1 (x : ℝ))]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range (N2 + 1),
      ((N1.choose i : ℝ) * p ^ i * (1 - p) ^ (N1 - i)) *
        ((N2.choose j : ℝ) * p ^ j * (1 - p) ^ (N2 - j)) * A.indicator 1 (((i + j : ℕ)) : ℝ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun j =>
      ((N1.choose i : ℝ) * p ^ (i : ℕ) * (1 - p) ^ (N1 - i)) *
        ((N2.choose j : ℝ) * p ^ j * (1 - p) ^ (N2 - j)) * A.indicator 1 (((i + j : ℕ)) : ℝ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (((i : ℕ) + (j : ℕ) : ℕ) : ℝ) = ((i : ℕ) : ℝ) + ((j : ℕ) : ℝ) by push_cast; rfl]
  ring

/-- **Proposition `lt:prop:binomial`(b), first statement.** If `B(N₁, p)` and `B(N₂, p)` are
`n`-completely mixable, so is `B(N₁ + N₂, p)`. -/
theorem binomial_b_add {n N1 N2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h1 : CompletelyMixable n (binom N1 p)) (h2 : CompletelyMixable n (binom N2 p)) :
    CompletelyMixable n (binom (N1 + N2) p) := by
  rw [← binom_conv N1 N2 hp0 hp1]; exact cm_add h1 h2

theorem binom_mul {n N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : CompletelyMixable n (binom N p)) (K : ℕ) (hK : 1 ≤ K) :
    CompletelyMixable n (binom (N * K) p) := by
  induction K, hK using Nat.le_induction with
  | base => simpa using h
  | succ K _ ih => rw [Nat.mul_succ]; exact binomial_b_add hp0 hp1 ih h

/-- **Proposition `lt:prop:binomial`(b), second statement.** If `p = a/b` in lowest terms, the
numbers `N` for which `nNp` is an integer are the multiples of `N₀ = b / gcd(b, n)`. -/
theorem binomial_b_N0 (n a b : ℕ) (hb : 0 < b) (hab : Nat.Coprime a b) (N : ℕ) :
    (∃ m : ℤ, (n : ℝ) * N * ((a : ℝ) / b) = m) ↔ b / Nat.gcd b n ∣ N := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have step1 : (∃ m : ℤ, (n : ℝ) * N * ((a : ℝ) / b) = m) ↔ b ∣ n * N * a := by
    constructor
    · rintro ⟨m, hm⟩
      have : ((n * N * a : ℕ) : ℝ) = m * b := by
        push_cast; rw [← hm]; field_simp
      have hz : ((n * N * a : ℕ) : ℤ) = m * b := by exact_mod_cast this
      exact Int.natCast_dvd_natCast.1 ⟨m, by rw [hz]; ring⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have : ((n * N * a : ℕ) : ℝ) = b * t := by exact_mod_cast ht
      rw [show (n : ℝ) * N * (a / b) = ((n * N * a : ℕ) : ℝ) / b by push_cast; ring, this]
      field_simp; norm_cast
  rw [step1, (Nat.Coprime.symm hab).dvd_mul_right]
  set g := Nat.gcd b n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hb
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_left b n
  obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_right b n
  have hcop : Nat.Coprime b' n' := by
    have := Nat.coprime_div_gcd_div_gcd (m := b) (n := n) hg
    rwa [show b / g = b' by rw [hb', Nat.mul_div_cancel_left _ hg],
      show n / g = n' by rw [hn', Nat.mul_div_cancel_left _ hg]] at this
  rw [show b / g = b' by rw [hb', Nat.mul_div_cancel_left _ hg]]
  constructor
  · intro h
    rw [hb', hn', mul_assoc] at h
    exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg h)
  · intro h
    rw [hb', hn', mul_assoc]
    exact Nat.mul_dvd_mul_left g (Dvd.dvd.mul_left h n')

/-! ### Part (c) -/

/-- **Proposition `lt:prop:three`, last statement, for `B(2, p)`** (proved by another agent), as
a hypothesis: `B(2, p)`, `0 < p < 1`, is `n`-completely mixable iff `2np` is an integer and
`2 ≤ 2np ≤ 2n - 2`. -/
def H_lt_prop_three : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ p : ℝ, 0 < p → p < 1 →
    (CompletelyMixable n (binom 2 p) ↔
      (∃ M : ℤ, 2 * (n : ℝ) * p = M) ∧ 2 ≤ 2 * (n : ℝ) * p ∧ 2 * (n : ℝ) * p ≤ 2 * n - 2)

/-- **Theorem `lt:thm:pb`, last statement** (proved by another agent), as a hypothesis: the binomial
distribution `B(sK, j/s)` is `n`-completely mixable for all integers `1 ≤ j ≤ s ≤ n`, `K ≥ 1`. -/
def H_lt_thm_pb : Prop :=
  ∀ (n j s K : ℕ), 2 ≤ n → 1 ≤ j → j ≤ s → s ≤ n → 1 ≤ K →
    CompletelyMixable n (binom (s * K) ((j : ℝ) / s))

/-- **Proposition `lt:prop:binomial`(c), first case** (due to Wang and Wang 2011): `B(N, p)` is
`n`-completely mixable if `np` is an integer. -/
theorem binomial_c_int (hc : H_lt_lem_count) {n N : ℕ} (hn : 2 ≤ n) (hN : 1 ≤ N) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hint : ∃ m : ℤ, (n : ℝ) * p = m) :
    CompletelyMixable n (binom N p) := by
  obtain ⟨m, hm⟩ := hint
  have h1 : CompletelyMixable n (binom 1 p) := by
    refine (large_c_two hc (binomVal 1) (binomMass 1 p) (binomVal_inj 1)
      (binomMass_nonneg hp0 hp1) (binomMass_sum 1 p) n hn).2 ?_
    intro i
    fin_cases i
    · refine ⟨n - m, ?_⟩; simp [binomMass]; rw [← hm]; ring
    · exact ⟨m, by simp [binomMass, hm]⟩
  simpa using binom_mul hp0 hp1 h1 N hN

/-- **Proposition `lt:prop:binomial`(c), second case:** `N = 2`. -/
theorem binomial_c_two (h3 : H_lt_prop_three) {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hint : ∃ m : ℤ, (n : ℝ) * 2 * p = m) (hlo : 1 / (n : ℝ) ≤ p)
    (hhi : p ≤ 1 - 1 / (n : ℝ)) : CompletelyMixable n (binom 2 p) := by
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
  refine (h3 n hn p hp0 hp1).2 ⟨?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hint; exact ⟨m, by rw [← hm]; ring⟩
  · rw [div_le_iff₀ hnpos] at hlo; linarith
  · have : 1 / (n : ℝ) * n = 1 := by field_simp
    nlinarith

/-- **Proposition `lt:prop:binomial`(c), third case:** `p = j/s` with `s ≤ n` and `s ∣ N`. -/
theorem binomial_c_pb (hpb : H_lt_thm_pb) {n N j s : ℕ} (hn : 2 ≤ n) (hN : 1 ≤ N)
    (hs : s ≤ n) (hsN : s ∣ N) (hp0 : 0 < (j : ℝ) / s) (hp1 : (j : ℝ) / s < 1) :
    CompletelyMixable n (binom N ((j : ℝ) / s)) := by
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hp0
    · exact h
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hp0
    · exact h
  have hjs : j ≤ s := by
    rw [div_lt_one hsR] at hp1; exact_mod_cast hp1.le
  obtain ⟨K, rfl⟩ := hsN
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hN
    · exact h
  exact hpb n j s K hn hj1 hjs hs hK

/-! ### Certificates for part (c), fourth case

The certificates come from the data file `binomial_mixes.json` of the paper's programs (the stored complete mixes
of the program of the paper), restricted to `N = N₀`, with integer weights. Each is one natural
number: base-128 groups (low first), the number of count vectors, then for each the weight and the
`N + 1` coordinates. -/

/-- Reads a number written in base-128 groups (low group first; a group `≥ 128` continues). -/
def readNat : ℕ → ℕ → ℕ × ℕ
  | 0, X => (0, X)
  | fuel + 1, X =>
    if X % 256 < 128 then (X % 256, X / 256) else
      let r := readNat fuel (X / 256)
      (X % 256 - 128 + 128 * r.1, r.2)

def readList : ℕ → ℕ → List ℕ × ℕ
  | 0, X => ([], X)
  | m + 1, X =>
    let r := readNat 20 X
    let s := readList m r.2
    (r.1 :: s.1, s.2)

def readVecs (N : ℕ) : ℕ → ℕ → List (ℕ × List ℕ)
  | 0, _ => []
  | m + 1, X =>
    let c := readNat 20 X
    let k := readList (N + 1) c.2
    (c.1, k.1) :: readVecs N m k.2

/-- The weights `c` and count vectors `k` of a certificate. -/
def decodeCert (N X : ℕ) : List (ℕ × List ℕ) :=
  let m := readNat 20 X
  readVecs N m.1 m.2

/-- The binomial coefficient by factorials (fast in the kernel). -/
def chooseF (N x : ℕ) : ℕ := N.factorial / (x.factorial * (N - x).factorial)

/-- The check of a certificate for `B(N, M/(nN))` and `n`. -/
def checkCert (N n M : ℕ) (L : List (ℕ × List ℕ)) : Bool :=
  L.all (fun v => ((List.range (N + 1)).map fun x => v.2.getD x 0).sum == n &&
      ((List.range (N + 1)).map fun x => x * v.2.getD x 0).sum == M) &&
    decide (0 < (L.map Prod.fst).sum) &&
    (List.range (N + 1)).all fun x =>
      (n * N) ^ N * (L.map fun v => v.1 * v.2.getD x 0).sum ==
        n * (L.map Prod.fst).sum * chooseF N x * M ^ x * (n * N - M) ^ (N - x)

def hdN (e : ℕ × ℕ × ℕ) : ℕ := e.2.1 / Nat.gcd e.2.1 e.1
def hdM (e : ℕ × ℕ × ℕ) : ℕ := e.1 * hdN e * e.2.2 / e.2.1

/-- The triples `(n, b, a)` with `2 ≤ n ≤ 10`, `0 < a < b`, `gcd(a, b) = 1`, `N₀ ≤ 12`,
`b ≤ n a` and `b ≤ n (b - a)`. -/
def enumList : List (ℕ × ℕ × ℕ) :=
  (List.range' 2 9).flatMap fun n => (List.range' 1 120).flatMap fun b =>
    (List.range' 1 (b - 1)).filterMap fun a =>
      if Nat.gcd a b = 1 ∧ b / Nat.gcd b n ≤ 12 ∧ b ≤ n * a ∧ b ≤ n * (b - a) then
        some (n, b, a) else none

def checkAll : List (ℕ × ℕ × ℕ) → List ℕ → Bool
  | [], [] => true
  | e :: es, X :: Xs => checkCert (hdN e) e.1 (hdM e) (decodeCert (hdN e) X) && checkAll es Xs
  | _, _ => false

lemma checkAll_sound : ∀ (es : List (ℕ × ℕ × ℕ)) (Xs : List ℕ), checkAll es Xs = true →
    ∀ e ∈ es, ∃ X, checkCert (hdN e) e.1 (hdM e) (decodeCert (hdN e) X) = true
  | [], [], _ => by simp
  | e :: es, X :: Xs, h => by
    simp only [checkAll, Bool.and_eq_true] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨X, h.1⟩
    · exact checkAll_sound es Xs h.2 e' he'
  | [], _ :: _, h => by simp [checkAll] at h
  | _ :: _, [], h => by simp [checkAll] at h


lemma list_range_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m : ℕ) :
    ((List.range m).map g).sum = ∑ x : Fin m, g x := by
  rw [Fin.sum_univ_eq_sum_range g m]
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

lemma list_sum_fin {α M : Type*} [AddCommMonoid M] (L : List α) (g : α → M) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (fun i : Fin (L.length + 1) => g ((a :: L).get i))).symm

/-- **Soundness of the certificate check**: a certificate that passes `checkCert` proves the
criterion of Lemma `lt:lem:count` for `B(N, M/(nN))`. -/
theorem checkCert_sound {N n M : ℕ} {L : List (ℕ × List ℕ)} (hn : 0 < n) (hN : 0 < N)
    (hM : M ≤ n * N) (h : checkCert N n M L = true) :
    CountCond (binomVal N) (binomMass N ((M : ℝ) / (n * N))) n := by
  simp only [checkCert, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set D := (L.map Prod.fst).sum with hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast h2
  have hmean : (n : ℝ) * mean (binomVal N) (binomMass N ((M : ℝ) / (n * N))) = M := by
    rw [binom_mean]; field_simp
  unfold CountCond
  rw [hmean]
  let kv : ℕ × List ℕ → Fin (N + 1) → ℕ := fun v x => v.2.getD x 0
  have hmem : ∀ v ∈ L, natVec (kv v) ∈ countVecs (binomVal N) n M := by
    intro v hv
    obtain ⟨hs, hw⟩ := h1 v hv
    rw [list_range_sum] at hs hw
    refine ⟨kv v, rfl, hs, ?_⟩
    have : ((∑ x : Fin (N + 1), (x : ℕ) * v.2.getD x 0 : ℕ) : ℝ) = M := by exact_mod_cast hw
    rw [← this]; push_cast; rfl
  let w : Fin L.length → ℝ := fun i => ((L.get i).1 : ℝ) / D
  let z : Fin L.length → Fin (N + 1) → ℝ := fun i => (n : ℝ)⁻¹ • natVec (kv (L.get i))
  have hsum : ∑ i, w i • z i = binomMass N ((M : ℝ) / (n * N)) := by
    ext x
    have hx := h3 x x.2
    rw [list_sum_fin] at hx
    have hc : chooseF N x = N.choose x := (Nat.choose_eq_factorial_div_factorial
      (Nat.lt_succ_iff.1 x.2)).symm
    rw [hc] at hx
    have hxR : ((n * N) ^ N * ∑ i : Fin L.length, (L.get i).1 * (L.get i).2.getD x 0 : ℕ) =
        ((n * D * N.choose x * M ^ (x : ℕ) * (n * N - M) ^ (N - x) : ℕ) : ℝ) := by
      exact_mod_cast hx
    push_cast [Nat.cast_sub hM] at hxR
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, z, natVec, kv, binomMass]
    rw [div_pow, show 1 - (M : ℝ) / (n * N) = ((n : ℝ) * N - M) / (n * N) by field_simp, div_pow]
    have hpos : (0 : ℝ) < (n * N) ^ N := by positivity
    have e : ∑ i : Fin L.length, ((L.get i).1 : ℝ) / D * ((n : ℝ)⁻¹ * ((L.get i).2.getD x 0 : ℝ))
        = (∑ i : Fin L.length, ((L.get i).1 : ℝ) * ((L.get i).2.getD x 0 : ℝ)) / (D * n) := by
      rw [Finset.sum_div]; congr 1; ext i; field_simp
    rw [e]
    have hpow : ((n : ℝ) * N) ^ (x : ℕ) * ((n : ℝ) * N) ^ (N - x) = ((n : ℝ) * N) ^ N := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 x.2)]
    rw [show (N.choose x : ℝ) * ((M : ℝ) ^ (x : ℕ) / ((n : ℝ) * N) ^ (x : ℕ)) *
        (((n : ℝ) * N - M) ^ (N - x) / ((n : ℝ) * N) ^ (N - x)) =
        (N.choose x : ℝ) * (M : ℝ) ^ (x : ℕ) * ((n : ℝ) * N - M) ^ (N - x) /
          (((n : ℝ) * N) ^ (x : ℕ) * ((n : ℝ) * N) ^ (N - x)) by ring, hpow,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination hxR
  rw [← hsum]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => div_nonneg (Nat.cast_nonneg _) hDR.le) ?_
    (fun i _ => subset_convexHull ℝ _ ⟨_, hmem _ (List.get_mem L i), rfl⟩)
  rw [← Finset.sum_div, div_eq_one_iff_eq hDR.ne', hD]
  rw [list_sum_fin]; push_cast; rfl


/-- Certificate data, part 0. -/
def certData0 : List ℕ := [
  0x1010101,
  0x300010101010302,
  0x1020101,
  0x2010101,
  0x30000019500000101010010f00001000002005700010001000104f90100000001016005,
  0x3000000019500010101000010f00002000001005701000100010004f90101000000016005,
  0x30000000cc8bd000000010101000003ffea00000002000001000eceab00000100000200000ef9d000010000000101000191d5000100000100000102ccdf010000000001000133a107,
  0x3000000000cc8bd000001010100000003ffea00000200000100000ef9d000010000020000000eceab00010100000001000191d5010000010000010002ccdf010001000000000133a107,
  0x300000001fffec00000000001010100002af3c000000000020000010002aefec900000001000002000002b7bb980000010000000101002790fc00000100000100000136a7980001000000000100011082a80100000000000001010199e308,
  0x3000000000001fffec00000010101000000002af3c000000200000100000002b7bb9800010000020000000002aefec90001010000000100002790fc01000001000001000036a7980100010000000001001082a80101000000000000010199e308,
  0x1020076000200013d010001014003,
  0x2010076010002003d010100014003,
  0x30000000001d78fc7daba00000000000002000001000002affaae8ca200000000000100000200000002d4968fcbe0000000000001000100010000019b8c8c8e0000000000020000000000010783f6f4890000000001000001000001000182fb89c8c40000000001000100000000010e8f94b7bc00000001000000000002000029b9e4808000000100000000000001010007f2d0808000010000000000000001000173c08080010000000000000000000101068080800b,
  0x3000000000001faf7c7db8000000000000200000100000001f6dfcdc9ee00000000010000020000000001ecb8f3d0800000000001010000000100006bb3ca89b80000000002000000000001000ee49ef1d400000001000000010100000001859aa3c2fc00000001000100000000010016b18ff6ac00000100000000010001000027958987840000010000010000000000010486fe9080000100000000000001010000079a81999601000000000000000002000045ecd9970b,
  0x300000000000003e7d0dd9dc300000000020000010000000003d8dc97869100000001000002000000000003e6a38be8f1000000010100000001000000029ef8ffb0e10000010000000101000000000289ffe3d3af0000010001000000000100002bdcf7e4d1000100000000010001000000108feba1ef0001000000010000000100002adb96c9b70001000001000000000001000eb482b2ac000100010000000000000001018bd9b2ae010000000000000101000000088dfca0800b,
  0x30000000000000003ffe8fe89af00000002000001000000000003f489c8c3850000010000020000000000000480a2ffdbf70000010100000001000000000299bba4d4e900010000000101000000000001d2e8cabcfb0001000100000000010000003fa4e8d48d00020000000000000000010001e780808001000000000100010000000008d997ab9701000000010000000100000013cedfabf30100000100000000000100000fe5a080800101000000000000000000010c8080800b,
  0x2010015e300010002000dbc00010100010df0010000010104f104,
  0x102000015e300020001000dbc01000101000df0010100000104f104,
  0x102000004d9c500000200010003eeb100010001010004f1cf0001010000017cd90100000100010183a705,
  0x201000004d9c500010002000003eeb100010100010004f1cf0100000101007cd90100010000010183a705,
  0x102000001b297ba0000000200010001acf7b00000010001010001e8dead00000101000001219f8a0001000001000143da8e0100000000010107979106,
  0x20100000001b297ba0001000200000001acf7b00001010001000001e8dead01000001010000219f8a0100010000010043da8e0101000000000107979106,
  0x201000044a1bedf000000010002000047ca80a300000001010001004ecddfdd00000100000101001ac4919b00000100010000011cf5eee500010000000002000bb0808001000000000001010180808007,
  0x1020000006288b9aa000000020001000022ed8d980000010001010000309bd3e4000001010000010036aec9b6000002000000000109a5b3c3000100000002000024dbdac0010000000001010004e2ad8007,
  0x2010000005da68caa000001000200000022ed8d98000001010001000034fe80e4000002000000010024dbdac000010000010100003b90f6b6010000000002000004c386c3010000010000000104e2ad8007,
  0x1020000000044a1bedf000002000100000047ca80a300010001010000004ecddfdd00010100000100001ac4919b00020000000001000bb0808001000001000100001cf5eee501010000000000010180808007,
  0x2010000002e8dcbddfb0000000100020000000eb397a0e900000001010001000010eabbd1d000000002000000010013e2e8ded70000010000010100001c98af8bbb0000010100000000010384fca0a100010000000002000007c6b1eeb8010000000000010100669bb6e108,
  0x102000000002e8dcbddfb0000000200010000000dccfbea8800000100010100000010eabbd1d00000010100000100001cfecac29c00000200000000010007c6b1eeb800010000000200000014c98495b8010000000001010000029ee0e9c0010000010000000001669bb6e108,
  0x10200000018e39eb1d5ee0000000000020001000006bdf7f9c5cc0000000001000101000009bae195bcc4000000000101000001000ea9c0ebbeda0000000002000000000103b686a2b591000000010000000200000c81b2f0da80000001000000000101000383ca91d4800001000000000000020038ffcdf2800100000000000000010103dceb948009,
  0x20100000018dfdbd0d8f300000000010002000000068fa5e4d9a10000000001010001000006e6d7dece9a000000000200000001000cb0808080800000000100000101000010dab9f8a7bb0000000101000000000101849ce4d8c500000100000000020000059d84fdd8800001000000000100000172feedcd900100000000000001000108e4addaab09,
  0x102000000000bf8ddfab3d40000000002000100000012bfa682bffa0000000100010100000013c7a5ed8dc80000000101000001000002e2ebe4f1980000000200000000010005839e98ea80000001000001000100000cf1b1ab9fd00001000000000101000002b1f6adc4be000100000100000000014cfbfa9c800100000000000002000027c0cfa3ad09,
  0x2010000000015eb9cfdf2e600000001000200000000069af0d1bcaa0000000101000100000009d4e6e9ceb6000000020000000100000ca4b5b183d000000100000101000000128693bdd5a60000020000000000000127c0cfa3ad000100000000020000000284abf189c20001000001000000010002fef2a7e0be010000000000010100004cfbfa9c8009,
  0x10200000000000cafdbd0d8f30000000200010000000012bfa5e4d9a1000001000101000000001396d7dece9a0000010100000100000004aab9f8a7bb00000200000000010000059d84fdd880000100000100010000000cb0808080800100000000010100000001849ce4d8c50100000100000000010072feedcd900100010000000000000108e4addaab09,
  0x20100000000000ce1ebc0fbee0000010002000000000012bfaaea9fcc0000010100010000000015bc948696c40001000001010000000002a88dfae4da000100010000010000000c81b2f0da80000101000000000100000383ca91d4800002000000000000010038ffcdf2800100000000020000000003b686a2b5910101000000000000000103dceb948009,
  0x2010000000ef2b4abfca7f40000000000010002000000038fe8a18880ef0000000000010100010000038cfe8fc2b5ba00000000000200000001000888a6fbb3959100000000010000010100000ac3dfb3dffad100000000010100000000013fa5fdbbd0f1000000010000000002000003d2e7e5f7e6f8000001000000000100000165acb6fcc4d500010000000000000100010d84fbec8bea010000000000000000010160cff6e1d90a,
  0x102000000000efbf590cde6c8000000000002000100000002e5d3c6beec9e000000000100010100000002c991da8fd4c0000000000101000001000009d39cfdffcfc8000000000200000000010003c0d6d3e4a3a2000000010000000200000008b2bcd5eca9e200000001010000000000010298e3bb95f6000001000000000101000002b4e08499b8ed000100000000010000000134bbe9a4f9e201000000000000010000010481c886cbc90a,
  0x20100000000000efbf590cde6c8000000010002000000000002e3bae383d6a8000000010100010000000002c991da8fd4c0000000020000000100000008b4d5b9a7bfd8000001000001010000000009d5b5e1bae5be000001010000000001000002b2c7a0dea2f7000100000000020000000003c0d6d3e4a3a201000000000100000100000298e3bb95f6010000000100000000010034bbe9a4f9e201000001000000000000010481c886cbc90a,
  0x10200000000000006ea8db0c992e300000002000100000000000b988f9cbb968000000100010100000000000b95a58af5cacb000001010000010000000002bbb8b8ace5c0000002000000000100000003d2e7e5f7e6f800010000010001000000000888a6fbb3959101000000000101000000003fa5fdbbd0f1010000010000000001000065acb6fcc4d501000100000000000001000d84fbec8bea010100000000000000000160cff6e1d90a,
  0x1020000000004b496a9f899baac00000000000002000100000007bdd4dd8aa096cd000000000001000101000000078bc8c9989190f300000000000101000001000010d9bafbc7d8ba00000000000200000000010002c686d1a0968ec400000000010000010001000005c3949cfdddfab50000000001010000000000012e94a791aaa9cb00000001000000000101000001f4e9fcc4f2d8c00000010000000000000200003585f2b9cc86b000010000000000000001010006f2d7eba9f1bc0100000000000000000100013494a8d5d6b50b,
  0x2010000000009f08eb49bfaaaf400000000000100020000000001f897868ff2d0eb00000000000101000100000068928aebb9f4ad00000000000200000001000005b7de9fa88693bf00000000010000010100000006b08c8ca5e3ed9600000000010100000000010001d6d7b0a0c1d8ea00000001000000000200000002fbe1a3e480ae8000000100000000000101000043dad5a6aed9d500000100000001000000000119c8ba9ceecaab0001000000000000000200000ddfb9c3ec888001000000000000000100000175ede792f0800b,
  0x102000000000009f7a3e8b6dffcd80000000000020001000000007f87c7d7cdf4a40000000001000101000000007496f099c086d00000000001010000010000000784a2aebce6ddb000000000020000000001000002ccf395d4ecce80000000010000000200000000068887debcdbe19e00000002000000000000000107e5b8e1d28fb100000100000000010100000001abd7c3b2e2c2d00000010000010000000001004cd6bccd9dbdb00001000000000001000100002ee08080808080010000000000000100000100048080808080800b,
  0x201000000000003e79c89fa849bba00000000010002000000000007b9efa694a9d5c200000000010100010000000007809eced69be7ee0000000100000101000000001adad0808afc92000000010001000001000000069087debcdbe19e00000001010000000001000001a7d7c3b2e2c2d00000000200000000000001002ee0808080808000000100000000020000000002fbd395d4ecce8000010000000001000001000050d6bccd9dbdb001000000000000000200000003e5b8e1d28fb1010000000001000000000001048080808080800b,
  0x10200000000000003f4d5bfcdc5bde000000000020001000000000007aff5a5b7f8e4aa00000001000101000000000006fe89a7bdf09bec0000000101000001000000005ee5b2e0ef8fac00000002000000000100000002fbe1a3e480ae8000000100000100010000000005fac386e7a1fd940000020000000000000001000ddfb9c3ec888000010000000001010000000078beb2f691c4ea0001000001000000000100005da38fc39da48000010100000000000000000175ede792f0800100000000000002000000001abea88481baab0b,
  0x20100000000000008b0d4f1c2af85ec0000000100020000000000000197a6a6c1cbec9d000000010100010000000000038f8a81cdfbc5b300000002000000010000000005f1a8c48f88a48000000100000101000000000008b2e3b9b1b0b88f0001000000000200000000004aab89b381d99f00010000010000000100000001c6d5d5b3c8aef50001000100000000000100003585f2b9cc86b000010100000000000000010006f2d7eba9f1bc0100000000010000010000002e94a791aaa9cb0100010000000000000000013494a8d5d6b50b,
  0x1020000000007a6ea928ca9eb8aed0000000000000002000100000001859ce7c5c687a0b80000000000000100010100000043c6eaf5fe8cc5ab0000000000000101000001000004c1a390aafef0aaab000000000000020000000001000287ff92bbd5db9b930000000000010000000200000004b89988b8a6d3d7c80000000001000000000101000001c8dcaad18dd3e9af0000000100000000000002000014fbbb8afbedd29a000000010000000001000000011dbad3aae697ab9a0000010000000000000100000108c6b2a795d0fdf20001000000000000000001000170bbe7d8deaaa40100000000000000000000010105a68890d9e3b10c,
  0x201000000000002bdbe8efafdf382d30000000000010002000000000005aeb3c3edd8a5e3f80000000000010100010000000004e3c2e5faa893a6a7000000000002000000010000000191daa5c7b6e0e40000000001000100000100000004e9b1a1da85a98eef000000000101000000000100007da7a696f4a0adb0000000000200000000000001001caaced8bc85c9a00000000100000000020000000002bdefe3b3d3afefb40000010000000001000001000051b29ab3caeb90a10000010000010000000000000103f79ff8cc9bd4b1000100000000000100000001000df0d98df6a3b3a4010000000000000000010100000184bcc4fbf485c10c,
  0x102000000000000039ce182bcbf81c6980000000000020001000000000005aeb3c3edd8a5e3f800000000010001010000000000048792d5ecb7acb1d20000000002000000000100000002b9f8c3bb87949b83000000010000000200000000000f82b3b3bdda94880000000100000100010000000004879bcae4f3f2fcba0000000101000000000001000055a9baac9786e4d20000010000000001010000000001c1eda481c4dc8fee000001000100000000000001000df0d98df6a3b3a4000100000000000002000000002996eba1b6b4f783000100000100000000000000010184bcc4fbf485c10100000000000000010100000003f79ff8cc9bd4b10c,
  0x2010000000000000005fbc8bae682aeccd80000000100020000000000000052e6d98fe482a384000000010100010000000000000294e9c7eea1b1accc0000000200000001000000000004b89988b8a6d3d7c80000010000010100000000000006abaffeeaeeceba9c000100000000020000000000002aa7acdfcc99dfca0001000001000000010000000001a2dba4ff91ebc0a30001000100000000000100000032b68eb5e284fdb40001010000000000000001000008c6b2a795d0fdf201000000000100000100000000268185d1fbe8a98c0100010000000000000000010070bbe7d8deaaa40101000000000000000000000105a68890d9e3b10c,
  0x2020101,
  0x10201160002000201010001020403,
  0x1020100160200020001020100010403,
  0x1030101,
  0x3010101,
  0x4000008b50000020002000b940000020100010c00020000000203e0010000000300018005,
  0x400000004d500020002000004d400020100010007c001000102000006cc010101000001018005,
  0x40000079187000000000200020002f2fc000000000201000112bbb40000000100010200118bc00000010000000300048d80000100000000020146800100000000000102048007,
  0x40000000ee28000000002000200001081fb0000000300000001048080000002000000020009fbe0000100000003000004dbe60001000100000200228a010000000002010044ac07,
  0x40000000004d59b000002010001000013f7c0000003000000010002bb80000100010200000013f7a8000200010000000144ac010000000300000001bd90020000000000020001a1b807,
  0x40000000000079187000200020000000002f2fc0002010001000000118bc00003000000010000048d80010001020000000012bbb4010200000000010046800201000000000001048007,
  0x301070101020902,
  0x10300070201010902,
  0x4000000002fc0f1b7000000000200020000004cf3e0800000000200000002000028d7aadc000001000000030000000291b880000002000000000002000cffa48000010000000100020000029deaa40001000100000000020015aac80002000000000000000201ceb5ca0100000100000000010140808009,
  0x40000000000018ee2d4a50000000200020000000071e1dc800000000300000001000054b08080000002000000020000007aa680940000020001000000010005d9beec000100000003000000004dbbd8800002000000000100010001bfffd80100010000010000000101c080800200000000000000020004eba0de09,
  0x3000149810000010003005d94000002000002058d000100010002169301000000010201f305,
  0x3000100005d940100030000004981020000020000058d020001000100169302010000000101f305,
  0x4000000028b95afddc0000000000000000200020000029d81f8feff00000000000000030000000149c5c88bc800000000000002000000020001dba2c0808000000000000100000003000077e6baa0d60000000000010001000002002cd3b5dfaa0000000001000000010100012c86ae808000000001000000000002000108a198d0800000010000000000010000020184938a8000010000000000000000020109f4d0e00100000000000000000001022b9fec0b,
  0x400000000028394f9cc800000000000000200020000006c99d8e8f500000000000003000000010001b992a28bb00000000000010200000000011affb9e4dc00000000000200000002000001deeed48dd200000000010000000300000001bdf1c7fdb200000000010001000002000003c6e082ce00000001000000000201000037a2b080800000010000000000010200000ac3c08080000100000001000000000002019a808080010000000000000100000101088080800b,
  0x4000000000001faf7c7db8000000000000200020000000039fd8fa7db00000000000300000001000001cebde7d080000000000102000000000100308cf1f29800000000020000000200000001dbd7f0bde000000000020100000000000104ebe0b69a00000001000000030000000001cef1d297fa0000010000000002010000003987ecbfca000001010000000001000001489d89e600010000000000010200000009cdaca1c80100000001000000000002005d90f6f40b,
  0x400000000000003f1c8f6ad9300000000020002000000000004fe8cb1b999000000000300000001000000129a8e81f20000000200000002000000006ef4c0b4d8000000020000010001000000038cd9d0c1ce0000010001000002000000000382fce49ca80000010100010000000001001198e4a3b400010000020000000000000101baa1ede800020000000000000002000030ea82e98c01000100000000000002000008e686e0a40200000000000000000002000180fa8fee0b,
  0x400000000000000028396f9cc8000000002000200000000000076d798e8f500000003000000010000000001b3b287fdb200000102000000000100000037a2b0808000000200000002000000000001def2d48dd20000020000010001000000000e86a082ce00010000000300000000000001adbce28bb00001000200000000000100000ac3c080800100000000020100000000001c91b9e4dc010100000001000000000100019a808080020000000001000000000001088080800b,
  0x40000000000000000028bb6b4c08000000200020000000000000001efcbb4f89500000300000001000000000001a4b9f0808000020000000200000000000001dba2c0808000020001000000010000000022f5f5918a00020100000000000100000008a198d0800003000000000000000100000184938a8001000000030000000000000076db87aff20100010100000001000000000990b8eef602000100000000000000010009f4d0e00201000000000000000000012b9fec0b,
  0x10300590002010101da010002017d03,
  0x30100590101020001da010200017d03,
  0x300010008f0e380000000010003000009c5af94000000020000020002ead1b10000010001000200548c940000020000000002029ab29f00010000000102007894ee010000000100000209c4da07,
  0x3000100000004f6db8700010003000000000490aac6000200000200000001aba6fa00020001000100006690c101010001000001003c8ab702000000000200006f93f4020000010000000104e2ad07,
  0x1030012c000000201013dd300010002012afc010000010204f104,
  0x301003d810002000101309e01000003000fde0100010101038304,
  0x10300003e82000300000110df01010002002f9d0200000101028204,
  0x301000012c001010200003dd301020001002afc020100000104f104,
  0x30001003ef7cdd2cc0000000000010003000019c1a587b20000000000020000020002c7b0faa100000000000200010001279395eeb90000000001000002010029f2baf0f6000000010000000102000adefed8840000010000000000030001e2d2e2f40001000000000001000215e5bfd501000000000000000102779ae509,
  0x3000100007980abf6dc000000000100030000007bf99994bf0000000002000002000034dce7a3fa00000002000000000200318091e4fc0000010000000102000008ba87dc9b0000010001000000020001a7ae94e30000020000000000000208bdefdd9d0001000000000003000004a0a3b2c60100000001000000000226bdfd8e09,
  0x30001000000007bf99994bf000001000300000000007980abf6dc00000200000200000000048393bc8c000002010000000100000893c9df8d0000030000000000010004a0a3b2c6000101000001010000006280a3c9f8000200000001000100000180f097d50002000100000000000126bdfd8e0200000000000002000008e4addaab09,
  0x30001000000000040eaa0b5c0000100030000000000003ef7cdd2cc0001020000010000000002c9bfc2e80002000002000000000016868991d3000201000000010000000adefed8840003000000000001000001e2d2e2f40102000000000000010015e5bfd50200000000020000000013d4bdd78702010000000000000001779ae509,
  0x3010014cb8d00000200010111d8ab00010000030006cdbd00010001010102f5e40100000100020183a705,
  0x103000056cebd000003000001119da60001010002004d86f901000001020003afc10101000000020b85e305,
  0x301000014dde70002000101000ed4d500020100000103cda90100000300000692fa01010000020003d7a105,
  0x10300000014cb8d00030000010005ca9601010002000011d8ab01010100010003f98b0102000000010183a705,
  0x30001000011fcea83dba8ff00000000000001000300000015fea3ceaab4e2000000000000020000020000098efeb184cef100000000000200000000020005bf99fca8f9a800000000000200000001000103f28797c0fc8a00000000010000010001010006a0ebb7f1a3cc0000000100000000000300000cf5efcb8cdd00000001000000010000020001adf8c3ed99b90000010000000000000201001d88d1fac4c200010000000000010000000202dba19ff5aa0100000000000000000003000edddcf2ae0b,
  0x3000100000013e5b6d0ebc89900000000000100030000000014cc80dcc58ccc0000000000020000020000000a9eb0af8f9dce00000000000300000000000110c2e1d8bbac0000000002000000000200000aa080bcfcd99a000000020000000000000200038bb0f5e4d9890000000200000000000100013ae2f7f7d9c000000100000000000300000001b085fd81f8ed00000100000001000002000021c88e9eeda10001000000000100010000011d82f7db97fe01000000000001000000020001e9e7a7e0b20b,
  0x300010000000000299881b98a999800000001000300000000000027e8e58d8698c900000002000002000000000014a0d2da9793b700000003000000000001000002fc99fe8b99bf00000200000000020000000014c080f9f9b2b4000002000001000000010000278298b6b2dd00020000000000000200000005dec5e3bae2c80002000000000100000001003a85efb6affc0100000000000300000000001f9bdc8996a601000100000000000200000001ade1f7fe82ca01010000000001000000000103d3cecfc0e40b,
  0x3000100000000000009f6f283d5b3b00000010003000000000000000a9cbe8eaea6e700000200000200000000000004b1d5efc1bc9200000201000000010000000001dcc3a6b7949800020000000002000000000003ca9af09df7ab00020000000100010000000001b3f2b5c1bdce00030000000000000000000107aeeeb9970100000200000000010000005db799dc938b010001000000020000000000018eb5d9d783ae0101000001000000000100000ec4a8fda2a101010001000000000000010001add0cffad50b,
  0x3010008f4afd0000000020001010884c58600000100000300039e99ea0000010001010101dd89a50001000001000268d18a0100000000010207979106,
  0x30100001bf1cbac0000020001010018a9a5db0001000003000007a8a9da0001010000020004b9adef0002000000010101eb86b50101000000000202c4b0fb06,
  0x10300000008f1d0ca0000030000010002d29ceb0001010002000007f3d2fc0002000001010001f282bf010000020001004eace7020000000001016c90a906,
  0x1030000000008f4afd00003000001000002b5c8e0010100020000000884c5860101010001000002c5daaf0102000000010068d18a0201000000000107979106,
  0x10300000a9495e895000000000300000101e2c18fae000000010100020009a7b3df970000010000010200749bdc9f000001010000000202b6d98eab000100000000030043b490ea010000000000020104c7edf207,
  0x30100000cfbd089c8000000020001010006d395c2aa000000020100000104caffa0d3000001000003000005a18b92f6000001010000020005d58fc3cf000100000002010002adc9c2ad01000000000102001bf09ac907,
  0x103000000049a989dea000000030000010001e49b94c5000001010002000001defbf2a6000001020000000151bcb6ef0000020000010100028a86d1f6000100000102000001f1d5c3e101000000000300001df5eee507,
  0x3010000001cd59b87f400000200010100001e8fa19f990001000003000000059cd2ea8c000200000001010008fcbbfeab010000010002000007e298a101000001010001007a81ffbd020000000000010101b3c398de07,
  0x1030000000017a6f6e9ae0000030000010000078dbaddb5000101000200000016cabfbaa4000200010000010002999aa8c4010100000002000005c6b8eedf010100000100010001ddb5c68701010001000000012ebb81cf07]

/-- The triples `(n, b, a)` of part 0. -/
def enumC0 : List (ℕ × ℕ × ℕ) := [(2, 2, 1), (3, 2, 1), (3, 3, 1), (3, 3, 2), (3, 5, 2), (3, 5, 3), (3, 7, 3), (3, 7, 4), (3, 8, 3), (3, 8, 5), (3, 9, 4), (3, 9, 5), (3, 11, 4), (3, 11, 5), (3, 11, 6), (3, 11, 7), (3, 12, 5), (3, 12, 7), (3, 15, 7), (3, 15, 8), (3, 18, 7), (3, 18, 11), (3, 21, 8), (3, 21, 10), (3, 21, 11), (3, 21, 13), (3, 24, 11), (3, 24, 13), (3, 27, 10), (3, 27, 11), (3, 27, 13), (3, 27, 14), (3, 27, 16), (3, 27, 17), (3, 30, 11), (3, 30, 13), (3, 30, 17), (3, 30, 19), (3, 33, 13), (3, 33, 14), (3, 33, 16), (3, 33, 17), (3, 33, 19), (3, 33, 20), (3, 36, 13), (3, 36, 17), (3, 36, 19), (3, 36, 23), (4, 2, 1), (4, 3, 1), (4, 3, 2), (4, 4, 1), (4, 4, 3), (4, 5, 2), (4, 5, 3), (4, 7, 2), (4, 7, 3), (4, 7, 4), (4, 7, 5), (4, 8, 3), (4, 8, 5), (4, 9, 4), (4, 9, 5), (4, 10, 3), (4, 10, 7), (4, 11, 3), (4, 11, 4), (4, 11, 5), (4, 11, 6), (4, 11, 7), (4, 11, 8), (4, 12, 5), (4, 12, 7), (4, 14, 5), (4, 14, 9), (4, 16, 5), (4, 16, 7), (4, 16, 9), (4, 16, 11), (4, 18, 5), (4, 18, 7), (4, 18, 11), (4, 18, 13), (4, 20, 7), (4, 20, 9), (4, 20, 11), (4, 20, 13), (4, 22, 7), (4, 22, 9), (4, 22, 13), (4, 22, 15), (4, 24, 7), (4, 24, 11), (4, 24, 13), (4, 24, 17), (4, 28, 9), (4, 28, 11), (4, 28, 13), (4, 28, 15), (4, 28, 17)]

theorem certs_ok0 : checkAll enumC0 certData0 = true := by decide +kernel

/-- Certificate data, part 1. -/
def certData1 : List ℕ := [
  0x301000000000a9495e895000200010100000009a7b3df970002010000010000749bdc9f000300000000010043b490ea010000030000000001e2c18fae010200000000000104c7edf2020000000101000002b6d98eab07,
  0x10300000cce8acfa0d30000000000030000010292fdc9b7ca0000000001010002000bc4aeafdeef00000001000001020001a0dfd58ef700000001010000000203b6e2fea7a900000100000000030075a68ae0f00001000000000002010d8ecbf7e0010000000000000102528dba8408,
  0x30100000790b794caac00000000020001010004b1ab95c3a800000000020100000102fda9bcf9f500000001000003000004cf9cbcf08000000001010000020002d69d83dad800000100000100020001f4bce399d400010000000100010124cba2efe801000000000100000202b2d2a4a308,
  0x10300000005f49f81d18900000000030000010068d7a7938f0000000101000200000699e686cda40000000200010000010181dfabf5000001010000000200028adeebe28200000200000000010130b195f09b0001000001000100014787f78ff00100000001000001010689f8c0c208,
  0x30100000016b0fdaefc9b0000000200010100001883858dda9c00000100000300000005adebd0928300000200000001010007ed9280f88600010000010002000001e1f0d08fdf00010100000000020032ec9b8fd100020000000000010101cff2b3c8880100000100000002004cb0d3b88808,
  0x1030000000008ac81be9cd000000003000001000001de98cbafe4000001010002000000098fbb84e4ac00000200010000010023b1abdcb50000020100000000011cd29fa58300010001010000010044b1bcbfad0001010000000200000393faf6e3b80101000000000002004dfaf3ab8308,
  0x301000000001ac3bfa1cdf50000020001010000001bf186e582bd00000300000000010063bff987f300010000030000000004cea9a1e1ac00020000000101000009bcbef7ddcb0100010100000000011bacdea2a901010000000002000065c1a9c6f602000000000001010001dca3deffc508,
  0x103000000000002fa81899d9800000300000100000031ac8fc79800010100020000000002f187e4a69400010200000001000051bef6b39c00020000010100000004b2c4fade000300000000000001669bb6e10100020000000001000c998bcff80101000000020000000180daa0c0e908,
  0x30100000000000cce8acfa0d30002000101000000000bc4aeafdeef00020100000100000001a0dfd58ef700030000000001000075a68ae0f00100000300000000000292fdc9b7ca0102000000000001000d8ecbf7e002000000010100000003b6e2fea7a9020100000000000001528dba8408,
  0x3010000069981bcb6eebb00000000000200010100068ac5d99991fa000000000100000300006b859edfacf00000000002000000010102a4c3b6faabd70000000100000002010001cb81ebe8eebc0000010000000001020016b6ff8990ee000001000001000000020fed98f5b79600010000000001000002049b82d1e1c3010000000000000100021aad898f8109,
  0x10300000004d78edf81c1e10000000000030000010003b0a5afaf8bf1000000000101000200007eacf1ccd8e20000000002000001010002eee1e086a0a700000000020001000001018dcbe8f084f10000000100000102000003aedc88dc89c40000010000000003000068aafcc680dc000100000000010100010edf8ee8c08d0100000000000100010176c1edea8709,
  0x103000000000f8af0abf2a4b70000000003000001000003dc92f680e3b700000001010002000000109586d3faad940000000200010000010001f6e1baa281a30000010100000002000005a3b3be9ee28600000200000000010100029b8ecc84b38d000100000000030000007fbc9390b4a8000200000000000001014b90ebf0b798010000000001000200001bce98ecc98809,
  0x3010000000001f995db909cd50000000200010100000001ab85c3839be80000000300000000010022dbddae94ab00000100000300000000568e9fae92ab0000010100000200000070f1d3d3acc10001000001000200000003fbb3a0eed90001010000000002000047d4db81fee00100000002000000000103b9e38dc9910100000100000002000005f8aab0bde209,
  0x30100000000000283adf0aec1d80000020001010000000001f8fbcffbb8930000030000000001000022e3d497aaf40001000003000000000037a1d8d1c1ed000200000001010000005d89b9c79f8c010000010002000000001184a481ba9c0100020000000000000127c0cfa3ad01010000000002000000199ffa8187b00200000000010000010004f584f895af09,
  0x103000000000000069ab592d28efc000003000001000000006d86afdf8cf200010100020000000000068891babe81b80001020000000100000001cb81ebe8eebc0002010000000001000011cec1d2efea00030000000000000100049b82d1e1c30101000000020000000002a3c2eebabbd6010200000000000000011aad898f810200000001000001000014d5d6abd89a09,
  0x301000004f0cda9b1b2aad3000000000000020001010004e8a091b1d484e600000000000100000300004df7808ec59eae000000000002000000010101f4f9afe6f9a2ef000000000100000002010001b3be8ee7c297c6000000010000000001020017f4a4c589ccbe00000001000001000000020effa9da98a5da000001000000000100000205c4a7a29ee09f00010000000000000100023bda8ed480a2010000000000000000010202a1efe4a58b0a,
  0x10300000003f8c3e6f8d7c19d0000000000000300000100029edbbfd9cd94ff000000000001010002000010e1eab987ec82000000000001020000000165e5d6e2b4baf500000000000200000101000385bee6b1e598e3000000000100000102000002efb9ac9d9cfde60000000100000000030000658cb28c8db298000001000001000000000212a0bae9a5fccf000100000000000002000101f9fef5d5dae201000000000000010000020c84d893e2db0a,
  0x10300000000068ccbbc9fd4d8d7000000000003000001000067a0c2d4d281e20000000001010002000000078f80b285e18a8c000000010002000000000125d6d78fc3a2c4000000010100000002000002f5ff8ba9f3fde7000001000001000002000011e7e2aad9e5ff000001010000000000020001859bf5a586d5f5000100000000010002000013d9c8a8c88bc30001000001000000000200058dd880fdc6d5010000000000000200010001ead8d39aed840a,
  0x30100000000049eb0f7b8d7eea0000000000200010100000050f8b7b695befe00000000020100000100006f94be86d2c3ec000000000300000000010066f8bac4f78f82000000010000030000000002c5f5a58bd7e3b8000000010100000200000002dfd7fe87a88be0000001000100000101000001e2f1d2839396da00010000010000000200002783ca96f5e8d200010100000000000100010381dc97ef889501010000000000000000020497a880d1899b0a,
  0x103000000000002ffe1c5aff3e0f2000000000300000100000048ced3b9e5a0e1000000010100020000000003b4f091cdf7bfa200000002010000000001001cf3988bb2e2cd000000030000000000000102e4f080b6869200000101000000020000006aa6adef8f85b0000002000000000101000056c793f8a3a3fd000100010000000101000040e5eedaed81ee000200000000000001010001f59c949beedf010000000001000200000007caf2e68bbcb20a,
  0x301000000000007c2eeeaf3ace0840000000200010100000000068684adb3fff1f80000000300000000010000019cce84c4dec283000001000003000000000002a4fe9b9380a9f1000002000000010100000003a0f59badf2f3f900010000010002000000003f9ebbcfb1baee0001000100000101000000028898f2a89abfef000200000001000000000102a5aee881c8a501000100000001000001001f8188b3f786de0101000000000000020000108ba4bfbd84b70a,
  0x30100000000000001d181eeee94aed8000002000101000000000001d2efb0a4a5c2d6000003000000000100000015ff8f83b388d100010000030000000000002493c3cfc7ac9c000200000001010000000058a7d4b0dcdae9000201000000000000010053aaa79cc8f600030000000000000000010481c886cbc901010000000002000000000b9df1d6ede3c102000000000001010000000bdaacaba6ddb70200000000010000010000068ae8f8b7a9c50a,
  0x1030000000000000004f2b9b6bce7a088000003000001000000000050d9cdd29990b6000101000200000000000004e582ddc4b596ad000102000000010000000001b3be8ee7c297c6000201000000000100000011b9bceacbefcc000300000000000001000005c4a7a29ee09f010100000002000000000001f3c889858fa9eb01020000000000000001003bda8ed480a2020000000100000100000015ba91b4d682cc020100000000000000000102a1efe4a58b0a,
  0x103000000038ef08ab7a6d9c3f500000000000000030000010002bbc9b1d5bb87b3f00000000000000101000200000ef5b49cbb90c3ec000000000000020000010100029fb4d699b0f2d6f50000000000000200010000016ee3d8a9b891b99600000000000100000102000002d49cb0c3fda395a600000000010000000003000065f4b980f2e5fb9600000001000000010000010115af908ac1ae93d100000100000000000002000102feaa94debc90c10001000000000000000101012088beecd5fcb7010000000000000000010002019cbcfa81839f0b,
  0x30100000002bddfe39a8994dcc000000000000002010000010002f1f6cb84bdafc98700000000000003000000000138cdedd6b1c5ca8700000000000100000300000002f2cea2d8e1fcd8f200000000000101000002000001c9b6c9d4f0acda8600000000010000010002000001d4c2aaedc7b4a1e200000001000000000102000036fb8b8ad6f0e9eb00000100000000000003000006a691efaccf95d90000010000010000000000020396e79ba8fdd4ea0001000000000100000000027dbd89f799cd9d01000000000000010000000205f39cc7819a8d0b,
  0x1030000000001aadb978b959efeea0000000000000300000100001dd2dea2f9ceb9d600000000000101000200000001bedcd9f7c1a3c6e90000000001010000000200005588ecebbbfaeee20000000002000000000101000fabf296eeb4c2a000000001000000000300000008b5a2f6d7c5f6e10000000101000000000002000c89f8a688c3cee800000002000000000000010109effdfab2eaf78300000100000100000000020008b98eab988fa48f000100000000010000000200018891f6a2a9dfc901000000000000000003000007e5b8e1d28fb10b,
  0x30100000000019fe586e295cdeda10000000000020001010000007fa4c990c2a8ce9400000000000300000000010010de8ce898e7bd8f00000000010000030000000039d5a5d38fe4d9ec00000000020000000101000049c0ff8fd4b08ff100000001000001000200000010dfa0a7a0ede4a70000000100010000010100003d84bcd8db83bac60000010000010000010001000b9df59381b7a2d3000002000000000000000101049e8cf8999bd5c900010000000000020000010002ffaea8ba87ccab0100000000000001010001001abea88481baab0b,
  0x103000000000007a9829cccf09ea28700000000000300000100000004d1dca8e5e4c19af7000000000200000101000000058dc6dcbeeccee9ab00000001000001020000000001a2c5e9bbc189e2d500000001010000010001000003d1cfcaf0ba9788f600000002000000010000010059c7bbf79ea9ebfb00000100000000030000000001f6a787b7ace6a5f20001000000000002010000001c8fffbbf598f2e400020000000000000000010108b6c7cfdcb58ced01000000000002000000000101dda6edfb9bdabd0100000100000000000002000280c7d2a4b782910b,
  0x301000000000002c08ee69efaabb7ef00000000020001010000000001a086a2e5a8c889d4000000000300000000010000528d82bd8ef7b7a6000000010000030000000000018dc6bab090ccfaed00000001010000020000000001b3a895ad9bb893920000010000010002000000002080d1cd93dcacff00000101000000000200000068a2b1edc0ddef83000002000000000100000100089cbb9fffcb94ce000002000000010000000001019fa4eadff0f49a0001000001000000020000001eceb6e4ced487a001010000000000000000020003b1a4e9f2c5cd8e0b,
  0x10300000000000006baedad81cdbc9ee600000000030000010000000057c69eccbb84cae20000000101000200000000000798ebe9f3b3a3eaf1000000010200000001000000019181e8e0f9a4c1b000000101000000020000000003d3f78ab7efea8ad20000020000000100000100002bc5c0f3f3849ec40000020001000000000000010184b7c89487a3d70001000002000000000001000efce7caa2a5fdd700010100000000000200000073d0afd9ef80e58b0002000000000000010100000cd088eb94908edb0101000000000000000200001596c0d8fe8aabed0b,
  0x30100000000000002e3f1e19bb2a4cbeb00000002010000010000000002a898b0fa92e7b79d00000003000000000100000078ddc5b4d19e9aed00000100000300000000000002c4aec4adbce6ea960000010100000200000000000289c2a3e782a196de0001000001000200000000000195a7eceecafbb3890001010000000002000000001ec3cbf0e2a0fbb300010100000100000001000019abab81c8adecad0100000001000101000000001787ddffa5cff9c001000100010000000000000117b0aaa4f6ae930200000000000001000001000398b5e2e6fd9edb0b,
  0x1030000000000000001a0bbd9b8eea5dafe00000003000001000000000025bbb8ffa5c58ade00000101000200000000000001b9acbbd1e993d9a10000020001000001000000001bc794e3f6c481e80000030000000000000100001be9d1fdee8bc000010002000000000100000012a983d8f2a5cdf90001010000000200000000004d91c6e1ecb9a6cc00010200000000000000010029e9d8d2b399df00020000010000000001000002f8bedc9ed6988101010000000000020000000015d2928afba6da8702000000010000000000000101fbdeed80b3af0b,
  0x301000000000000000182a0a7d689aebda500000200010100000000000001c6cb9ecbceeef600000201000001000000000071b49096d4b6b1e200000300000000010000000021fc9380a6a1feb20001000003000000000000006dcde4e3d0cd93e900010100000200000000000059b2d788e9de8fb8000102000000000001000000078fdad8eb8fb19b0002010000000000000100007fb8dc9fbedaeb0100000100020000000000002d85dbc2f2d3f4b80101010000000000000001000ad894f9c7a9bd0200010000000000000000013494a8d5d6b50b,
  0x1030000000380bfb1d8dec0a6e2a40000000000000000030000010002b19f9991cf93cca5b40000000000000002000001010002a1cdd0eccece88abf400000000000000020001000001689f85a5a4b995d9e80000000000000100000102000002c8a4b491eca3fdd0980000000000000200000000010106c3a4ede28f81b3fe000000000001000000000300006cd5e493938d96cdb800000000010000000100000101199d879fefeebeb1fd00000001000000000000020001049586bdaba0bb87ec000001000000000000000101013bb2e9c9f8a3eba6000100000000000000000100020481b880abaed1dc010000000000000000000001020ff298b28daa930c,
  0x1030000000003b0a4d389d8eea0e7e00000000000000003000001000003d2d0d7dce7c09fb2d800000000000001020000000100019da7f8ee8d83a5a4900000000000000200000101000004e08bbc9bddb9909fbe000000000001000001020000000585cdab9ceebeaa9e88000000000100000000030000001bf085db82c5c2c7cb0000000001000000020000010001c1b39ea1fc8cdfc3e00000000100000000020000000135f79593f4d4a3eaf40000010000000000010001010008efd7a6afd7aeae8a0001000000000000000003000014c6ac94fd8eedf3000100000000000001000100015cd7e0d5f098d691010000000000000000010002000596aed8ebc49bc50c,
  0x301000000000f9db0f8e4e2968698a40000000000000201000001000005d4a789f6acfba7a8c400000000000003000000000100049cbabecc8fb197d6d80000000000010000030000000006ec88c0e1b584a6a7cc000000000001010000020000000cebbb85e0bbedaba3910000000001000000020100000006ce8ca4bab9dac9c9f50000000001010000000002000002ada2fdd3a6e4cd95a50000000100000100000002000002b6aa849dfdacb789e7000001000000000000030000002886f0d4f3bac7d4cb000001010000000000000000021a88a7f3aea39c8e910001000001000000000000000207f093e3d8d7b4b4d8010000000001000000000000023785bf98ab839dae0c,
  0x301000000000007a5c2e8aff5acdb84e20000000000020100000100000003bbc7a7adc2aa89f89e0000000000030000000001000002c3bad0ecf79380dece0000000001000003000000000003fde1ced98dfd8bfb9d0000000001010000020000000005b193d99988d685f9e40000000100000002010000000001c3e281a482aaddedd50000000100020000000000000105e593d8aabce9fee700000001010000000002000000029087f195a2cbeec0a8000000020000000001000001003ff6aba69ccdcfc9ec0000010000000001020000000001a680ceaaacaea4f4ce000100000000000003000000001be2a88cd5cefac4ec010000000000000100020000000290bfd4ccc4e2ffa70c,
  0x10300000000000006e1b7948faabac0ebd00000000000030000010000000003d095cfbafd8588dbe40000000001020000000100000002fea2b1a0fdd1b3e3ae0000000002000001010000000006b6d9ed8f81c993dcfb0000000100000102000000000004ee98bbd799f6c0fe8f0000000200000000010100000001b88ddcbdbad0e3fcca0000010000000003000000000001a3db9f8fb0e29e8e950000010001000100000000010019d1e8b8898a97c5c500000200000000000001010000238bceffd0acbde0c4000101000000000000000200003ff6aba69ccdcfc9ec0100000100000000000002000001c494af91b3a48099020000000000000000000001010290bfd4ccc4e2ffa70c,
  0x10300000000000000019af4e9e6e2dad4ab820000000003000001000000000043c5edb4d6ede5b886000000010100020000000000005aa5a0c497f4c5afab0000000200000101000000000068c6a6f281afeaf8cd000002000000000101000000001db5fa8d86d096cf95000002000000010000010000001883cca5e7d7fce6a40000020000010000000001000004dcc1e0cbc6d9b4e20001000000000300000000000010afddfaf186edde8b0001000200000000000000000103f79ff8cc9bd4b1000101000000000002000000001699d3eacea7a681b80100000100000000020000000004acbee0d0b5ff89fd010001000000010000000001004881b4eaf3faccf40c,
  0x301000000000000000487c1ac839edec187cb0000000201000001000000000003e2e49befd7b791dbd00000000300000000010000000001dda3a3fcfed2a28bab00000100000300000000000000049bbcc2f0f3d59e86910000010100000200000000000001f5daec9786e49f9eeb0000010200000000000100000035f79593f4d4a3eaf4000002000000010100000000007584f9defc9a8aafbd00000300000000000000000100719e8ceaeda7c4840001000001000200000000000002e7d084e591d2f7b1bf000102000000000000000000010596aed8ebc49bc5010000000100010100000000002de495ce9aed8e92fb0100010000010000000001000008efd7a6afd7aeae8a0c,
  0x30100000000000000007ee3b989918acec8e80000020100000100000000000069d692d38281ef938e00000300000000010000000000249ccc86b184b299e8000100000300000000000000006981df9eb9ebdfe89d0001010000020000000000000058ceeb89a29a8cff960001020000000000010000000008b4ad8acffa94e5ff0002010000000000000100000001b1d7bf8eb5beada4010000010002000000000000002ad5b1d28492fd82de010100000000020000000000000486e0fe878a88bfe70101010000000000000001000013e6a398d2e1a3e20200010000000000000000010001ab92d5b98fc5f40201000000000000000000000105a68890d9e3b10c,
  0x10301030201020102,
  0x10301130002010203010100030503,
  0x50000130201020019030001010a03,
  0x1030101ac00000201021300010100033c01000001030504,
  0x50000005602010200006903000101003c03010000010504,
  0x1040101,
  0x2030101,
  0x3020101,
  0x4010101,
  0x500000effc400000000030001010ff782000000010100030005cef2000000020000020107efdf00000100000103000590a0000100000000040057c00100000000000301058007,
  0x50000000ea28000000003000101000fed9c000001010003000007e7ec000002000002010008c6e200020000000003004ed6000200000100000202c080010000000004000055b707,
  0x5000000001cd58b000003000101000012e9e000010100030000001ed1e000010200000200000fc0c0000300000000020001f2e3020000010000020004aac9020100000000000255b707,
  0x500000000007bc69100030001010000000192c1ea01010003000000005dc9f20103000000000001288002000100020000000c98cb020002000000010005bc80030000000002000014c18007,
  0x500000007e094e500000000030001010008f8c9a300000000030100000102a9b185000000020000020100088e9ad000000100000103000003fdd0a200000200000001010138d38700020000000000010231b1e601010000000000000308819408,
  0x500000000000ec588f300000300010100000008e1ebda00000301000001000009ddece000010100030000000013cdfbb200020001000200000007d8b9a102000000000300000002e2848c02010000000000020062e3cc0300000000000001011082a808,
  0x5000033f7a6b0000000000000030001013be3d88e00000000000101000300099495f60000000000020000020123e884d500000000010000010300178aadc00000000100000000040004b2de800000010000000000030144f4800001000000000000020204f68001000000000000000103148009,
  0x5000000000490dbe480000000000300010100000489a5aaa50000000101000300000004a6ff91910000000300000000020001a6cdcc8a000000030000000100011388e98b0000020000000003000001c1ae80800001000100000003000013f4cfb0000200000000010001011cdbd8a80200000000000000020103b8808009,
  0x5000000000070edc7d4000000030001010000005ba4e2800000000301000001000069bc80800000020000020100000001a0f7aee000010000010300000000339daddc0002000000000300000012bbcfe00100000000040000000002be91eb010100010000000002000ac680800102000000000000000278808009,
  0x1030100000000000002db98daeb0003000101000000000001d6fd81c2010100030000000000007ee293d10101020000010000000073b3e3c0020001000200000000005ebc8daf0200020000000100000015fdd6800201010000000001000002d8c4800300010000000000010018ce8003010000000000000001648009,
  0x3020b0101030902,
  0x203000b0301010902,
  0x500000019ef888beaeb0000000000000003000101002b9db6c7f2ce00000000000001010003000069fca8a89600000000000002000100020012fed284e9e900000000000003000000000209f3a9e5e78800000000000100000103000019d985c0808000000000010000000004000006f0ff98808000000001000000000003010001a597ecc08000000100000000000003000114d2fdc88000010000000001000000000301c69ccf8001000000000000000001020106e0fcf00b,
  0x50000000003d5fbe998800000000000000400000000013df8fbdcbd000000000001010003000000049ffe8c91f40000000000010200000200000580eae8ee8c00000000020000010000020001e7b6eace9c0000000002000001000100010aafc7b1e4000000010000000004000000018a95f880800000010000000000030100001aa8e08080000100000000000002020000028ea1e1d200020000000000000000000339af8f97010000000000000100020100148080800b,
  0x5000000000004bbb0c28ce000000000000300010100000003998294c00000000000030100000100000686a7e4cc8000000000000400000000010001b9eaea888000000000010300000000000114a2f6d080000000000200000201000000079bb2f9aff00000000100000103000000000184e784c9a000000002000000000300000002c2c8feaad400000100000000040000000001d88ca3f394000100000000000301000000248285fdee01000000000000020200000002dd9fbdf30b,
  0x500000000000002f8eee7c69d0000000003010000010000000484e7ebeb8e000000000400000000010000018c8bb898a50000000200000201000000000585a193ea8000000100000103000000000058958ccf800000010002010000000001001484cef4e100000200000000030000000001c3a884d5c000000300000000000001010003fcdfdf9300000300000000000100000101e8eaa9a20001000000000400000000007bf1f1b0800100000000000301000000000dc1f9e0800b,
  0x5000000000000000c9389d9c88000000003000101000000000011a3c287bd9a00000200000201000000000008cdfc96e6ab00000300000000020000000002929889dabc0001010000020001000000000786b698cb8800020000000003000000000050a9c09ee900020100000000000200000027e0d2ccce0100000300000000000000013c80808001010001000000000200000001a7c0a1b3b201020000000000000002000027bd90808003000000000000000000020004c1c080800b,
  0x500000000000000001fb49ea4dcdb00000300010100000000000023f6f58a82be0001010003000000000000001fbcaea8f8c60002000100020000000000000fd8d0dbf0b9000300000001000100000000019acdbe9cd001000201000000000100000001a597ecc0800101010000000200000000000cecc2e0808001020000010000000001000014d2fdc88002010000000000020000000002eb98ecf1d802010000010000000000010001c69ccf8003000000010000000000000106e0fcf00b,
  0x500000000005df2cbba95f90000000000000301000001000001dfa6dedbf9c4000000000000040000000001004587abb887d0000000000001030000000000010887a0e6c594000000000002000100020000000288b6d594a7870000000000030000000002000016e6e9aae3aa0000000001000001030000000001e59cc28b9cf80000000002000000000300000014c0cfb3c79a0000000100000000040000000055e4f083e5900000010000000100000300000012b185dc9ee80001000000000000030001000002b1cbc694d0010000000000000001030000001298a79cd40c,
  0x50000000000000001eda4c9b9a2a00000000003000101000000000001baecb0a6ca96000000000400000000010000004ce4faf2c5c40000000103000000000001000009b190caff9c0000000200000201000000000001fad3acd192a50000010003000000000000010002b1cbc694d00000010101000000020000000001878ef0b995d60000020000000003000000000035a0d8bb899b000002010000010000000000011298a79cd40000030000000000000101000008fff5919fcc000100000000040000000000004587abb887d0010000000000030100000000000887a0e6c5940c,
  0x40153000102020490010001034003,
  0x3010103880100040001df020001023c03,
  0x4000101df010103000388020100023c03,
  0x104000053020201000490030100014003,
  0x3010102f1b5000100040001e6cc00020001025ddc010001010238a304,
  0x4010001e5db0002000300019bf400030000023f90020000010233a104,
  0x104000001e5db0003000200019bf402000003003f90020100000233a104,
  0x400010040ae01010300000181b2010300000112e1020100020025bf04,
  0x104002895f7000000030002578ad30000010003015f97e00001000002020f83e001000000010379c005,
  0x3010101a09a8f0000010004006a88f200000200010230daeb00010001010227c8ce0100000100030389f505,
  0x400012d93db0000010103000ba69400000200020127c0f600010000040015a08001000000030102808005,
  0x4010001c6f2d7000002000300018eddeb00000300000238dc8e0002000001024089a00100000102010eb5a405,
  0x104000032d4ec0000030002001bb8ab00020000030018d8de00020100000206cad501000200000209ea9b05,
  0x30101003b83fc00000400000124e300010004000021c2890003000000020b97fd0101000003000f988005,
  0x400010021c2890001010300003b83fc0003000001010f988001000004000024e30200000003000b97fd05,
  0x401000065a9d800020003000040daf100030000020027c7a102000001020016ffc502010000000209ea9b05,
  0x10400000032d08000030002000020fdbc00040000000103cda90200000300000ffdd80201000002001082a805,
  0x30101000001c5f4a801000400000055aa9b01030000000106808002000102000024c1ec0300000002001ff08005,
  0x4000100006a88f201010300000001a09a8f02010002000030daeb02010100010027c8ce0300010000010389f505,
  0x102020000003fd0a50103000100001fd3b20201010100000ff8be03000100010007c1f00301000000013ce005,
  0x301011da5eade000000010004001494d7c40000000200010209e8e9e800000100010102098aeb9f00010000010003018dc8860100000000010307979106,
  0x104000070e4e7870000000300020046bfccad0000020000030031f8b2da0000020100000217fd9ac20002000000010211c1988c0100010000010203b0c1a406,
  0x400010033bc86b2000002000201001fb4fce70000030000010112b5a2d00001000004000022e2efa000020000000300568abe0200000000010202a6cdb906,
  0x40000010022e2efa00001000400000033bc86b2000102000200001fb4fce700030000000200568abe0101000003000012b5a2d00201000000000202a6cdb906,
  0x4010000002ef98fd20003000002000025e6f6f7000300010001000c8fd4b20100010300000025e58fc60102000100000101d8a0d20201000000020002d8e1ed06,
  0x400010000001494d7c4010103000000001da5eade0201000200000009e8e9e802010100010000098aeb9f03000100000100018dc8860301000000000107979106,
  0x4000124a5cf9c91000000000101030040d98eeff80000000002010002058cecca8400000001010001021fc4c6e080000001000000030105cdce8080000100000001000346f0808001000000000001030380808007,
  0x10300010faed0a9f800000000020101010e84caf8dc00000001000103000f84c5ebf80000010000000400038fdba794000100000000030120b797eb00010000000101020dd8a2eb010000000001000302a3f6f907,
  0x104000012ebfbc08000000000030002000bd2a29b98000000020000030009b1e7b3c8000000020100000203e7908eb800000200000001020389bfe0ec0001010000000003018df5b5e8010000000000040009a5b3c307,
  0x40000010cd7c686e7000000010004000011fe8ecd9a00000001020002000585e3fbae000001000101020037b0b6c8000001010000030009eeddc1b8000100000100030001e59ea0800100000000010300118b808007]

/-- The triples `(n, b, a)` of part 1. -/
def enumC1 : List (ℕ × ℕ × ℕ) := [(4, 28, 19), (4, 32, 9), (4, 32, 11), (4, 32, 13), (4, 32, 15), (4, 32, 17), (4, 32, 19), (4, 32, 21), (4, 32, 23), (4, 36, 11), (4, 36, 13), (4, 36, 17), (4, 36, 19), (4, 36, 23), (4, 36, 25), (4, 40, 11), (4, 40, 13), (4, 40, 17), (4, 40, 19), (4, 40, 21), (4, 40, 23), (4, 40, 27), (4, 40, 29), (4, 44, 13), (4, 44, 15), (4, 44, 17), (4, 44, 19), (4, 44, 21), (4, 44, 23), (4, 44, 25), (4, 44, 27), (4, 44, 29), (4, 44, 31), (4, 48, 13), (4, 48, 17), (4, 48, 19), (4, 48, 23), (4, 48, 25), (4, 48, 29), (4, 48, 31), (4, 48, 35), (5, 2, 1), (5, 3, 1), (5, 3, 2), (5, 4, 1), (5, 4, 3), (5, 5, 1), (5, 5, 2), (5, 5, 3), (5, 5, 4), (5, 7, 2), (5, 7, 3), (5, 7, 4), (5, 7, 5), (5, 8, 3), (5, 8, 5), (5, 9, 2), (5, 9, 4), (5, 9, 5), (5, 9, 7), (5, 10, 3), (5, 10, 7), (5, 11, 3), (5, 11, 4), (5, 11, 5), (5, 11, 6), (5, 11, 7), (5, 11, 8), (5, 12, 5), (5, 12, 7), (5, 15, 4), (5, 15, 7), (5, 15, 8), (5, 15, 11), (5, 20, 7), (5, 20, 9), (5, 20, 11), (5, 20, 13), (5, 25, 6), (5, 25, 7), (5, 25, 8), (5, 25, 9), (5, 25, 11), (5, 25, 12), (5, 25, 13), (5, 25, 14), (5, 25, 16), (5, 25, 17), (5, 25, 18), (5, 25, 19), (5, 30, 7), (5, 30, 11), (5, 30, 13), (5, 30, 17), (5, 30, 19), (5, 30, 23), (5, 35, 8), (5, 35, 9), (5, 35, 11), (5, 35, 12)]

theorem certs_ok1 : checkAll enumC1 certData1 = true := by decide +kernel

/-- Certificate data, part 2. -/
def certData2 : List ℕ := [
  0x40001000f8ca280a500000001010300007bbab5c1000000020100020005e0e6ef9b00000003000001010987bdd49b00000100000400000e87bfe8e4000100000003010002e2b996ca01000000000300011df5eee507,
  0x10400000011b39598800000000300020000089f9d82b4000000040000000102ea9dccfb000002000003000009d2fed38800000201000002000594a1acf80002000000010200049480808002000000000002014080808007,
  0x4000001001e87baf0aa000001000400000021cfdda998000001020002000001eed79b930000030000000200069fcbab000003000001000104c7edf280000101000003000016d4b8c6fc01000001000300000387aa95e207,
  0x40001000021cfdda998000002000201000018d5eec490000003000100000102faeaff8c000100000400000012d6ff81c100010200000002000baa9ca3be0003000000000002069fcbab010001000003000004c7edf28007,
  0x40100000011b39598800000020003000000089f9d82b4000003000002000009d2fed38800020000010200000594a1acf800020100000002000494808080010000000400000002ea9dccfb01020000000000024080808007,
  0x301010000007bbab5c100000400000100000e87bfe8e400010004000000000f8ca280a5000103000000010002e2b996ca000200010200000005e0e6ef9b01000300000000011df5eee501010000030000000987bdd49b07,
  0x4000100000011fe8ecd9a00020002010000000ef4c1bce6000201010001000037b0b6c8000300010000010001e59ea0800003010000000001118b8080010000040000000007e097a68b010200000002000004f7aee0dc07,
  0x4010000000012ebfbc08000020003000000000bd2a29b98000300000200000008f4928c97020000010200000003ddeadaf5020100000002000003d0babbe00201000001000100018df5b5e8020100010000000109a5b3c307,
  0x30100010000000f84c5ebf80004000000010000038fdba79401000301000000000faed0a9f801010102000000000e84caf8dc010300000000010020b797eb02010100000001000dd8a2eb030001000000000102a3f6f907,
  0x40000010000000ac1c2a080010004000000000011cffbe1af010200020000000011dec7e68001030000000100005af6a1fc02010100000100000194a3de84030001000000010017d0808003010000000000010180808007,
  0x10300010af9efb19db20000000000020101010bc485c7fceb0000000001000103000cac88aa9e860000000100000004000186d1e7d5eb00000001000001020101e8abffba9d00000100000000030135a2e3cedc00010000000001000304b5cebab801000000000000010314c3aec108,
  0x10400003ad2d1a7dafb00000000000300020023fbd8c3efcd0000000002000003001fa4ce95a8ae0000000002010000020af48ce1e0de0000000200000001020ab082f0b0d800000101000000000304edd0a9daf000010000000100010243af95c5e00100000000000101020398eddb8408,
  0x40001000cec9188c7e200000000020002010001f1b0f8aa80000000000300000101089c90f2f1e10000000100000400000bf4ccf6f488000001000000030100308c9d98b900000100010000030002bef888f5a300010000000002020032bef2fab80100000000000103000384fca0a108,
  0x4000001001eb8b98594ba00000001000400000033aae9cdd6870000000102000200001dfaaad8e4a800000003000000020001a9f6e8cff7000000030000010001098ef6acf28400000200000002010014e7e386c1b800010000010003000008e5899ec9e001000000000103000067f999e48408,
  0x40100000019cfeecfde9d00000003000002000008c5cb85acb40000000300010001000ff7db8b84f000000102000100000153eed39d9200000200000102000010ca9690a69300010000000400000007fbf1d7c0d80100000000030100001bc8e2aaaa01010000010000000262fc82c29808,
  0x104000000004db9e8f18ca900000004000000010018b8cafcabf100000200000300000019819d828be10000020100000200002fa2c2ec8ef300000300000001010001e3fe91dcdf0001000100030000002ea9aa89ebed010000010002010000058fccf1c1e301010100000000000201bde797a2e308,
  0x400010000000180ec83e2a5d40000030000010100006886efa0c7980000030001000001000bf7ae8be1f00001000004000000007487ae9c869300020000000300000008ecb9a681cc01000100000300000056e6eeb6800200000000020001000a85a980d6c00201000000000000020181f7c09d8508,
  0x30101000000000dcad6cdee9c0000040000010000002aadb9a9baf60001000400000000002ffdeecee3c100020200000000010001c9fbcbe9e000030000000200000002d2bd998ad50003000001000100000bbc9198b6f00003010000000000010c93f1818401010000030000000020f0c3cbc78408,
  0x40100000000000ed4edf0e4b700020003000000000008fedcca8e9b00030000020000000007d7f4d29da300040000000000010010ebe5b1b8010300000000000001669bb6e102000001020000000002eea28bc58002010000000200000002cc80dc8c96030000000001010000019bb48ab6dc08,
  0x30100010000000017a587b8d0cb00040000000100000005ddfbcea09001000301000000000017a6e7fea6a501010102000000000015d581f48e9502000101010000000001b3899bebc10201010000000100006ac5c79db803000100000000010008eb9cf4f00301000000000000012986dd8208,
  0x104000017e5ba9e96af94000000000000030100011080e5e88884ec0000000000010101020017c1ecb9bc96e80000000000020001010110ea99e89ec3ec0000000001000100030012bfd5d685abe00000000100000101000203fed69f8dd9e00000010000000001020146e7b1bed6900001000000000000030105dd88dadbd6010000000000000002021aad898f8109,
  0x40001000ba1e4808080800000000000020002010031ebda978edc0000000000030000010108808080808080000000000100000400000b93d9e3808080000000010000000301002c81a7969db80000000100010000030002d6d4abd1e2c80000010000000002020043a999a3a0800001000000000001030006eb97c8caa00100000000000000040027c0cfa3ad09,
  0x401000022f19ef7f49ac8000000000002000300000fe8ebb8da8bfa000000000003000100011094cff4c9c5ba0000000002000001020015ac8ed5adb2e0000000010001000102000cc998edbfd8800000010000010000030001e8e8a4f7ccbe000002000000000000032ae6b5afb3e10001000100000000000323f9ce948a800100000000010000010201e6f3eed48009,
  0x1040000000bd189faa3a0800000000000030002000005cce995b5cbec0000000000040000000101b9d7aaa1b0bd0000000002000003000006acde81f1c5b80000000002010000020004a38bb5cebac80000000200000001020003f495908080800000020000000001000276a2808080800001000000000004000020d0808080800100000000000003010002808080808009,
  0x40000010012a9f8fba0bddf000000000100040000000fc1d8db92bfa600000000020001020000119fc0b38b9cad000000010001010200000986c69594a9840000000200000002010005cc8dc18ef1be0000020000000000030053e6d795bbcd0000020000000100000201fda1b28a98f3000200000000000001023394d3d89dfc0100000000000201000106f3c69b92a209,
  0x4010000000183b9b2ff9ca399000000000300000200001fd2fcb6f18de80000000003000100010061b7afeaa288800000000200000102000057eba88ad1d8eb0000010000000400000026fecc98b1a9fa000001010000000300000deb9cea89a1aa0001000000000301000004a8c4f5aebedc0001010000010000000206c3b5cce7e59c0100000002000000000270d9a1e8d2e409,
  0x4000001000028ca9ecfe1de9b000000010004000000002b9986c4bf9ea000000003000000020000049780e4a580e80000010100000300000026a4fdb0d7f3ec0000030000000000010101d1d7a288bedc0001000001000300000001ed90b9d0e1940001000200000000020005919498b2c9de0002000000000003000001d6878d99e6c701000001010000000200018cc5dba5b08009,
  0x4000100000020b2e4f3afb6d8000000030000010100001da4dededaa0b2000001000004000000001efebf8fdfb9f0000002000000030000000386fb92b0d3d9000003000000000002007e9dc389aeba0002000000000102000001c7b1e99db1e70002000000000200010003a8e89889df820002010000000000000234da929e828001000002000000000200019da1b9c6af8509,
  0x104000000000042c590999b8ea00000000400000001000018c2b8b797a1d2000002000003000000001ba78efcd6eec70000020100000200000028b4d9828f869200010001000300000000239aaeeacc9ddf0002000100000002000002ca8bb89cfba70003000000000000020002dafed0c5c8fe0100010000010200000006fbe29ddc8ece020100000000000000021c96a8ba94d909,
  0x4000100000000019183e9c1bc8794000003000001010000000183c7f7d885ce800000030100000000010001afb283b6abf4000100000400000000000185eba4a3c49480000200020000000000012cef88b0b6dd000300000000000200000bbc86a8c49b9e010001000003000000001092f6efd892a40200000100000002000005d2ee93c9ca820201000000000000020001f4ed9ea2acec09,
  0x40100000000000196da8fbaffebec000003000002000000002abf89d3af9eb00000030001000100000063bcddb5d6afb00001020001000001000015f3ac95d6afb0000200000102000000005fc1d0fe90e1d00100000004000000000021a1bbd0ded4f902000001000001010000028fc7eaa9d0d0020001000001000000011a80808080800300000000000000020001d4888080808009,
  0x1040000000000000bcdb5c1bab2d800000400000001000000049e8cf7fdefa2000103000000000100006a91dac7bc80000200000300000000000ac0afed868ae000020100000200000000018a8981c580d20003000000010100000006a3f19e86de000300010000000001000bfdefb1ae80000301000000000000014cfbfa9c80010002000002000000000681bfa2a5e29f09,
  0x30101000000000004a7b9a28ea6b0000004000001000000004e89f4b5808080000100040000000000004de2cdd7bcb6b40002020000000001000003c78a90acc2c8000300000100010000001582c1a38de2c8000301000000000001002feea4fc87e0000400000000000000010294c4aaf7bb0101000003000000000037cfbd9ea1a7d8030000000000010100001096a0ca9db809,
  0x40100000000000001c7adfed0a4d1000201010100000000001387b5adfddfc00003000100010000000016a9f7e2d09e01000103000000000000068cd48bafd68b0100030000010000000005fef2cfc9e9820101020000000100000001aa9cdfd9f3a00103000000000000010001f4adc8f3f20201000100000001000017cd90bfc7b00300010000000000000108e4addaab09,
  0x104000017cda5d8a3c39da900000000000000030100010fd28ed29b81cf9100000000000001010102001696d0fddd8d9de2000000000000020001010111dec4e09b82a1ca000000000001000100030013c1dfce92a5c2a4000000000100000101000204cb89f28bfacca600000001000000000102015ecfb6bef0cc8800000100000000000003010a8182898eafb7000100000000000000020250a5a9e3dd86010000000000000000010302a1efe4a58b0a,
  0x40001000b8ed5c0bbe6e1fe000000000000030000010107feaced8684f0a000000000000100000400000baebbd1d8eff5e400000000000200000003000ab2a4c6b9a0cc000000000100010000030003aff8daefd5f3a200000001000000000202000fe189d9f8cfa8000000010000000003000146fbae8d84aed000000100000000000103000bb6c7ad91aac500010000000000000004007298e594988a01000000000000000003010481c886cbc90a,
  0x400000100258bc8a08ea4beb900000000000100040000002785e4d1eb81949d000000000002000102000011c2f096e4ced8ff000000000003000001000108bbfd8dfbeab6c7000000000200000002010012fca78bd2a1c0ef000000000200000101000102b1a8e289ab99b500000001000001000300000cc9b480a8d0cfe0000001000000000103000002b6f49d93be8fb4000100000000000004000023cbe683fa97a8010000000000010100000201ead8d39aed840a,
  0x40100000003c98de9e7ecf28cd100000000000300010001000381a4e3ad96a1edac00000000000301000000013ecff4b99ecbdd88000000000200000102000002b580afd9bcb3ffab0000000100000004000000019ad18de8e5ebb69e00000001010000000300005f90a4c0fea1a082000001000001000003000034c0cbd9c190e0f4000002000000000000030002b9cdce9ee7c3e4000100000000010003000007abb88cf3aa87cc01010000000000000000033daba089a5878c0a,
  0x1040000000015c9e8afc9c2c4f100000000000400000001000ae5cc9da2bda9fb000000000200000300000010c6d2f2bd86e49100000000020100000200000689e7ddc6d8b5b10000000200000001020000099fa1ebb9cd839f00000003000000000000020a9784f0d9d5e600000100000100020100000495d79cfda0a3ea00000200000000010100013acfe4e8a6c5c0000200000000000100000234afe7f1d5a78a020000000000000000010203e5b9b385de990a,
  0x4000100000014c396a1b4cbc7d2000000000300000101000002cf90b0f6d094920000000003000100000100069dc9d7cbe6888400000000030100000000014ae58cf4f291d0000000010000040000000012d4fad8b0c89290000000010200000002000009e2c697cfe99192000000020000000300000008e6adddd4fe87000001000100000300000009909f80ffc2bdca000100000100000201000001dd9384f6fa9384020000000000000100000209b5d5e3f0e8d10a,
  0x40000010000000ae683b0afe482c89a00000001000400000000000afff1c0aadc90eed0000000030000010001000004b380baa9b6e0bcea000001010000030000000006e080d692dc9dbba2000002000001000200000002dfead7ead1c1958b000100000100030000000002f8c9b389f1d9d5fc00010200000000000002003e96e68eb9bdf1dd000300000000000000000205afcdf5fbabd699010001000001000002000033d0cecfd38aa99802000000000100000002007190e5bcacc4f50a,
  0x40100000000002b93d0df938589e2000000020003000000000005b5f6d38dc8e8a3000000030000020000000025e0dce59afd80e7000002000001020000000007c098baecc1b29d00000201000000020000000c8d8dbd9eb2f4e500000300000000010100000a95edcd9bdaddd4000100000004000000000014e2b8eae1d085e2010101000000000000020068dfcfe3aace9402000000000000030000000183add6bbaf9896020100000000000000000207caf2e68bbcb20a,
  0x10400000000000054daa2deefb8b081000000030002000000000006949ecb90bbd58700000004000000010000002db4cefbfaf6d5c000000200000300000000003fb0f0c9d382cb98000002010000020000000020baafeef4b2f2a2000100030000000000010001b5fae5a2a5d490000200000001020000000020aff3b2f3c2a7e6010000000103000000000006abe1aea0a9e78c01000003000000000000010b93c081d898c80101010000000000020000059bfddc9794acb40a,
  0x4000100000000006cd1dbb69ee3ac8800000201000200000000005ef6ace2ec9b88e400000300010000010000001cc285c6e984adb200010000040000000000006f87fff3e7f1e9ed000102000000020000000038b4a1f8fd80aae7000300000100000000000105c089f9d0c78c01000200010000000001006ae3b28beec5f80200000001000101000000099a96ba90edc1ee0200000100000100010000068f84e69ade869c02010000000000000200004aebf8cfee94800a,
  0x400000100000000005c9a81d6ae93b7e0000100040000000000000058f3c7d2948ddfdc00010300000001000000001bbeefaefc8dfa000202000000000100000004adff9ac2b7a9d1000300000100010000000019dca2c3d982c6a7010100000300000000000040a99d99bcb5f3a301010200000000000100005bb4bae98ad4a802010001000000000001000791c6a9a1c0d00201010000000000000001208cc0b4dcc803000000000001010000000187e4a3f5b0c5ef0a,
  0x4010000000000000003a6d4dce3869acd000201010100000000000039d3dabe9391e0f600030001000100000000003fbcf2f9b7ded40100010300000000000000129a9aedc0bcb0a301000300000100000000001382a2db98ede3d0010102000000010000000004cb89f28bfacca601030000000000000100000a8182898eafb702010001000000010000005ecfb6bef0cc88030001000000000000010050a5a9e3dd86030100000000000000000102a1efe4a58b0a,
  0x30101000f99d688c7ff8ad6c000000000000000020001020008d8cc80ed96c8d8d700000000000000020002000102e7a891c3c79585a900000000000001000003010006f6c7d0e9b9c2e5f600000000000002000001000201ca9590b3d893b58500000000000100010001000202e89fe496c79ac08000000000010000000101000247e7dbeafdce80800000000100000000010001020a82c8acd8fc808000000100000000000100000377a7bcdbd0808000010000000000000001000306d4aea0c0808001000000000000000000010315cff68080800b,
  0x400010005b2ceb2a59c9eb5b300000000000000010300000113a5fbeaeee7b088fa00000000000000020002010010a9b0f788eab9d5fb0000000000000100000400001288c9c48ea0c8af890000000000000100020002000888c8e2e0e6a796f7000000000001000100000300088bb3b0cd8596ab8000000000010000000100030001e4f593f1d7e4a4c000000001000000010000010223b6d9f7d8a0a49000000100000000000100010203d3eeeef1dee1980001000000000000000101021cfba48fc9c2fc01000000000000000001000368a8d1abacea0b,
  0x4010000198af086a081e1c2cc00000000000000020003000007e8c4becbc6cfe1c10000000000000003000100010e81b2909fa6d1a0ec0000000000000200000102001092e4e9f5cbd7b6c00000000000010001000102000aee9f929698d7f8fa00000000000200000001000214e596a6b186d2c300000000010000000003010002dd9cecfc84fccc800000000100000100000001023bcfed92878bf48000000100000000000001030006e4d5a2a8ad88800001000000000000010001023ba9b4f5d2b08001000000000000000000030101ebdbcea5e0800b,
  0x1040000000cc6a8b8b28dd6a88000000000000000030002000001c2959de0ba9c8fc400000000000000040000000104b3f9d2f8e380d7f7000000000000020000030000089ad3b5cefad5b6a800000000000002010000020003cfaea7c9d0eac9d800000000000200000001020004ed918fa18880808000000000010000010002010002ec84b48a808080800000000100000000000400004ad69eb0808080800000010000000000000301000a9b8e80808080800001000000000000000202006ba08080808080010000000000000000010300048080808080800b,
  0x4000001000183a0e7cac9accaa4da000000000000010004000000018fb9b7e4fa8dfefad50000000000000300000002000db68188e1c2dbceb900000000000101000003000001919a9ebb86dd8f8e8000000000000200000100020017fe8eb887d0d8980000000002000000000003000ac5bff1c69ee382ac0000000002000000010000020cfbecc0b1e7bdb59400000002000000000000010205a192acedb0c7a0d000000100000100000001000201c8e1c5c2a797bfd000010000000000010001010111fba0bf998895980100000000000000000202005dc1a993d9b8cc0b,
  0x4000100000bb4b9b4b193fdf0880000000000000300000101000aae9fb0a1c8e79ec00000000000010000040000000bd5d78798f3fae18e00000000000200000003000001dcfaf7eb96e9d0f90000000002000000000200010293bdeae0ecd0fc8700000001000000000202000001b493bda4eb99d800000001010000000000030079d1bcc8a6c6e1f200000002000000000001000214a3fce2dfbcb39b0000010000000000010300001ac3f796c6eedc8000010000000000000004000002cab58dfab8b8800100000000000000000301000ecebabe8390800b,
  0x40100000017b1a2db99dbcd80800000000000000300000200000188b1bbc4a6a39eff000000000000030001000100159ae1aa82e18080800000000000020000010200000dd3f5cea1c2e7b9d700000000010000000400000005de86b7f4cfe2cba1000000000101000000030000088291e4a9d9a7ecdf00000001000000000301000002bcf69cc5d3d388b70000000100010100000000020193948adcf9eafff3000001000000020000000002498bd2a9b1a891c800010100000000000000000308d08ac1a79affd801000001000000000000000334fcd08882f4d60b,
  0x104000000000bd8fcb9f0f387a2c000000000000004000000010001b7bac8c3a292f8ea00000000000103000000000170fd8489df9cb8ed0000000000020000030000000cb9aed5ef8ed58500000000000201000002000009acc1c7ef8ad3fca400000000000300000001010001deb0a98f8f9189ab0000000001000100030000000b82f2d1e0b8c5bca000000002000000000100020001d9edf7f5bdb7f3d400000100000000000400000059dab8f491e2a88c00020000000000000000010205c59aedc9b0cec30100000000000100010100014fd2b5aff8ba8d0b,
  0x40001000000219de0d6c6808080800000000000030000010100001fecc1fdcde08080800000000001000004000000002183aae7c08080808000000000020000000300000003ed87ecba98b1a1e400000000030000000000020001a384bbfbfdb4bee800000000030000000001000101c08080808080808000000002000000000200010007a2b0caeaefaf8080000001010000000000030000038bccd690e080808000000200000000000100020048bf93ecc8eccc8000020000000000000000030026edb1ec81afce900100000000000000040000000589f79eebe8b3d50b,
  0x4010000000016c4c6cfd884c1b0c5000000000003000002000000139c92f5f6b6cce79800000000020000010200000072d0df8dfafaeeb100000000020100000002000008cfc2a5cfa4d9cab80000000003000000000101000680df8ab1bdc2dc900000000003000000010000014abbb78ba1afd3aa0000000100000004000000000f82a5a2a3b080808000000100000100000300000003f089cf85808080800001000000000100030000003d80f0f2a6a2bdec00020000000000010000000207f3c0baeceee18a01000000000000010300000005b3fdc0808080800b,
  0x104000000000001b4d6a5b491ea8582ec0000000000040000000100001ee8accf86e682c8fb0000000001020001010000005dc8eaa2ed8cd9fba100000000030000000101000058f9d0d9f091cca0c500000000030000010000010010a7dafdb9ec8689e000000000030001000000000102a6ccf0b4fec38cd00000000100010003000000006794c8fdc3ddabd2e600000002000000010200000029dbf793e2cafda6cd00000100000100020100000037e1f093f3f9a1c08000020000000000010000020004fff9a49b95bbc0800200000000000000010001013494a8d5d6b580800b,
  0x400000100000055b9cad4a896a8f5a600000000010004000000000052acbfb2f3caf09d91000000000300000002000000189bf68ae3f3a8cdf300000001010000030000000050c6aadbc6a886c38400000002000100000101000019c6b4d2d7d5aae800000003000000000001010009e291a68ce480808000000003000000000100000173c4f7b0e1e1d3dc00000200000001000002000012a0b098f7e3a9cec00001000000000103000000000782edafe5d889bcfc0002000001000000000000020194b7f1878f96920100000100000000020100004effefd396d7b8980b,
  0x400010000000057dcd7bea9e6b08f9700000000030001000001000022829cddce8dabbc800000000100000400000000004cf1f2d5f4fa8398aa00000001020000000200000038e4dd86bbdfd6e68000000002000000030000000001a2f98cb4c58380eb0000010001000003000000002f8bb7fca299808080000200000000000100020000019fa1ea90dcd3f0c00002000000000002000000010f9bd991e2989af000020000000100000000020003c2cb8fe3f393f4d00100000000000103000000003689d0d1bbc0e2d80200000000010000000000021ff28ba0da9fced40b,
  0x40100000000000182fca1c1ffb19c908100000000030001000100000073fad0a2e7b3fab0c000000000030100000001000011eadaf5f7d8b6e8c000000000040000000000010007bff5f6a8e099a0800000000103000000000000014e9ebd80c1cfc080000000020000010200000000379fcbbcb79fb2a98f00000003000000000101000017fed998ffa2c2a7c00000010000000400000000001fa6dcd6f4fedcd98e0000010100000003000000003ac2e1a7e49afeb6820001000000000301000000001484e9b2f4b285c7a8010000000001000300000000028488f2e7ffda89bc0b,
  0x10400000000000016c4c6cfd884c1b0c50000000004000000010000000f82a5a2a3b0808080000000020000030000000000139c92f5f6b6cce79800000002010000020000000072d0df8dfafaeeb100000003000001000001000003f089cf85808080800000000300010000000001003d80f0f2a6a2bdec00000003010000000000000105b3fdc08080808000000200000001020000000008cfc2a5cfa4d9cab80001010000000003000000000680df8ab1bdc2dc900100000100000003000000004abbb78ba1afd3aa02000000010000000000020007f3c0baeceee18a0b,
  0x4000001000000005888f294808080808000000001000400000000000055c28793caa6dd99b900000003000000020000000007a9ecd5d0ecaceced00000101000003000000000054f6dacefa808080800000020000010002000000000cb595a296e58b9a9c00010002000000000200000017c0bd8fddfea8808000020001000000000002000003d0c8fbc1e1e6f5b2010001000000000300000000018ad1bbc2a785a5fa01000101000000000002000002809b81cbb5e5aace01010100000000000000020067ceafcad8fefb8002010000000000000000000206e2c9d3e58b9a9c0b,
  0x40100000000000021f0e389aee1d4b6dc00000003000002000000000022adfaf4e7fef2a187000000040000000000010000028d8faadcb5a6f8a400000200000200010000000017b7c5d381edc5aec00001000000040000000000000a8a81e6ddf4cac18800010003000000000000000101eef7a08fe9aea700010100010000020000000004e8c9918fde85c39000010200000000000200000004e89ab5aaa28289f8010000010000030000000000028a879ed180f3b6e602000000000100000200000025afb2b696a5d18402010000000000000000020010cfd0c8dc91ebc90b,
  0x1040000000000000037e3eca8a58f96c59c00000004000000010000000015de9ec1dd8691c19000000201000002000000000022dcf0d3e8c5c7f4880000030000000101000000000cd29e84eee0c8caf000000300000100000100000009899e99ded5e2b8c000000300010000000001000001cca5a88adda7eb9000000301000000000000010015c89aa3a283bf9c0000040000000000000000010184b7c89487a3d70001000100030000000000002bf687f8cec0a4838000020000000102000000000004c6b5d89c998dfec0010000000103000000000000099184c6e1fa8080800b,
  0x400000100000000000bd5d78798f3fae18e0000010004000000000000000bb4b9b4b193fdf08800000202000000000100000001b493bda4eb99d800000300000002000000000001dcfaf7eb96e9d0f90000030100000000000100001ac3f796c6eedc8000000400000000000000010002cab58dfab8b8800001010000030000000000000aae9fb0a1c8e79ec00001030000000000000000010ecebabe83908000030000000000010100000079d1bcc8a6c6e1f20100020000000002000000000293bdeae0ecd0fc8702000100000000000200000014a3fce2dfbcb39b0b,
  0x40001000000000000018ee5bdf2e0a5cfe6d50000030000010100000000006b9ef6f9858ae5c0ba00000300010000010000000026c3fcce9f8bebd6fa00010000040000000000000075aade9ce6e7c0b39200020000000300000000000017a7f5e8e2c2fc998b0002000100000200000000000fe3d297d190caddac0100030000000000000000015dc1a993d9b8cc02000000010001010000000008ace0f591e7cd82ee02000000010100000100000008f9c39498b9f781d003000000000000000101000001c8e1c5c2a797bfd003000000000000010000010011fba0bf998895980b,
  0x401000000000000000cc199f1b28dd6a88000000200030000000000000005f3cdc0efba9c8fc400000300000200000000000006e4cb9bc9fad5b6a80000040000000000010000004ad69eb0808080800002000001020000000000000585b6c1ced0eac9d800020100000002000000000004ed918fa1888080800002020000000000000001006ba0808080808001000000040000000000000001bdd290eee380d7f70101000200000000000100000a9b8e808080808002000100000000020000000001b6829a8580808080020001010000000000000001048080808080800b,
  0x10400000000000000000cc5bf9aeb95e6aba600000400000001000000000005c9a6bdd7afccfbaa000200000300000000000000069484c3f1a796a1d20002010000020000000000000896cd9af6ddc3b6a001000100030000000000000005a1f0c6e5f2bbce8e0100030000000000010000001de7f6c983c5fa8001020000000002000000000001a790ed86f2e9eb0200020000000000000001001dd4dabae9988003000000000000020000000057a79b9f819f938003000000000100000001000003b2aad19496c48003000001000000000000000175ede792f0800b,
  0x30101000000000000000187d488cfc8c3cb970000040000010000000000000481c3e0bcb3be93a900010200020000000000000009d2e6a7d495e8f7ec0001030000000100000000000485d9d8a6c2cb95c0000200020001000000000000098785b2fb8ff9cfd700020200000000010000000072bac9f8ebf292a001000003010000000000000009e6c399ead8d7c79101020001000000000100000011dbacfbec90928801020100000000000001000001e9f7b7b8efb0cc0201010000000000000001000ebdd287e4e1be0300010000000000000000013494a8d5d6b50b,
  0x40001000000000000000dd5dfc4f0dbfcf8940003000001010000000000000a8af1f1d0e9e9d08000030001000001000000000002e89fe496c79ac08000030100000000010000000017dbd8dde6fa94cc0004000000000000010000000a82c8acd8fc80800100000400000000000000000ae1edffc294b2f68301030000000000000001000077a7bcdbd0808002000000030000000000000057e7c69294a591a4020001010000000100000000308c838d96d3ebb403000100000000000000010006d4aea0c0808003010000000000000000000115cff68080800b,
  0x1010300000186b8eecebdfbe3f1eba400000000000000000103000001319ed4d6cbada3a3ee96000000000000000003000001010ba38ae7c2e9abb6fac6000000000000000100020002004096aaa1f3faa8edab840000000000000002000001010118b98eb7eaf7e9f0befa0000000000000100010000030024be9cb3c284d8e3dba40000000000010000000002020008d39cf4bdc8a7dcc0b80000000001000000010000010201bfb4a8c7f5d8c8ebe90000000100000000000001020117c3edfec6e09ca98c0000010000000000000100000301f9f5e598b1f6aefe000100000000000000000100030cc8e2d6b2c5aadc01000000000000000000000103258ab8f4f4b7d70c,
  0x40000010068e494d2d09b9ca6ad9e0000000000000001000400000070f2d591dcb3feadb7a3000000000000000300000002000cd288e8abc9fce9fba70000000000000101000003000072a781fce5eebfdbc3a80000000000020000000000030003cea0e9d4c5ecdea98400000000000200000001000002118dec95c3b7cb8ac79c0000000001000000000103000002bcaea3d2ac99c0c6d00000000001000100000000030007e2a2c7eeabeb81b5a80000000100000000000004000001e6a5add78de8a8d9a0000001000000010000000001021ba893b4a6ecc2df900001000000000000000101010101fba7c6ccf8b08ca00100000000000000000101000208a3e4a7dfa0ac880c,
  0x40100000002979e93c2e6aef386f49b0000000000000003000002000001ecb182ca9aa5b9f4e1910000000000000200000102000068ed94a4caa8e890d1eb000000000000020100000002007782f7bbe5dca69fdded0000000000010000000400000001a7aea8f6ba83b8bb8eec00000000000200000000020100059fb38db2dcd0dd909a000000000200000000000003000889a386e7eab9feaffc0000000002000000000100000211d7c0c0c89ec49a9dda0000000200000000000000010204c8ceabc8e1c3e4c3940000010100000000000000000301bce696868bf5a0e9e8000100000000000000000400000ff496a5b4aff4c9d0010000000000000000000301004ed0feebf4a997d40c,
  0x40001000000019db3ace3e9de96f7949800000000000003000001010000019899e997f0cfc4d7c5f000000000000100000400000000019ea0eca9f7c3c7e093cd0000000000020000000300000014d38ce3ec99c39693e0000000000003000000000002000681d2ccbdffdde6c4a50000000000030000000001000108c8a487f4ff93f1cbcc0000000002000000000200010025d3e7dbd68e84f8c8e200000001010000000000030000139b81bdd3f1c9b388b00000000200000000000100020003b9e3b5f99f8191aaa00000020000000000000000030002b7d5fbc99480d3f6ec0001000000000000000400000046b9e6bbf7f8ccebb00100000000000000000301000003d391da95bf85918c0c,
  0x40100000000006ef0bea6b186bbd4f4fa000000000003000002000000000691a2c6aa80f3a58487000000000003010000000100001c83e7c9a18d9dd6e4d000000000010200000101000000018ab6e8a7a7f9daed8fd40000000001030000000000000162b0c4858694ecf5890000000002000001020000000029fcde898d8c8fbbe5f50000000100000004000000000046dda4e9ead7dbf0cde80000000300000000000000020001f2ccd5f9e282e497be0000010100000000020001000010aeb79db1f1d18eb5920000020000000000020000010004eb97fda89e85c4bdc80001000000000100030000000004b6efb2a0d7adaad1e4010000000000000103000000002c98c1c195f9c78df90c,
  0x10400000000000004c5dfb7a7f98caa84b794000000000004000000010000000380c0bde4f4ccdeb0fba40000000002000003000000000003dbfaffe2adbfdfd580bb0000000102000000000200000022c4e695c1b18c8af5e60000000102000000010001000060e1f7fb86a89ffbffb400000002000000010200000000028ba8b9c587d289c4f9bf0000010001000001020000000001a7e1d1c0bfb9bdd5e2fa000002000001000000000200000cacf9c9c99de9f0f8bc000002010000000000000002000ae9d7b3de8eb5f6b9d80001000001000000030000000029ab98e2a1a9f0d88cfa0100010000000001000002000002f4f8badcf6d99fc4f6010100000100000000000000026c8383d8999af4f7b60c,
  0x40000010000000000019ea0eca9f7c3c7e093cd00000001000400000000000000019db3ace3e9de96f79498000000030000000200000000001d9bb0ebe198d787dfac0000000400000000000000010046b9e6bbf7f8ccebb0000001010000030000000000000195acb2bff4a593b1d7ac0000010300000000000000000103d391da95bf85918c0000020100000000020000000022c3afccb6bf90d8a9d0000100020000000002000000000495d4e694c8c58897de0002000000000003000000000008ef89a4baaa8f8cb2e9000200010000000000020000000d87a494e397e5eaeeb80003000000000000000002000002b7d5fbc99480d3f6ec0101000000000100020000000008c8a487f4ff93f1cbcc0c,
  0x104000000000000000001a099fed6d5b3dfa8dccd0000000400000001000000000051cfba9c92fd9d82b0c6000001030000000001000000001ef49188ecf197b790b400000200000300000000000000018bbeafa7cd93e9e08680000002010000020000000000000dfe93bdd1c1e3aed3bb00000300000001010000000000198bceee99c0e5ddd29a0000030100000000000001000071a3da83d3f9c6f2d80000040000000000000000010009c5da96b98392dfb00001000300000000000100000006aee88ea7e2caf2dcf0000200000001020000000000004eb8beb2d1d8f591eee0010000010100020000000000001dad9ac5d3a1ca87a4c0010002010000000000000000012f96ffa792cbf4cc0c,
  0x400010000000000000001bedac5f0ffdbe0a5dfc700000201000200000000000000019f82a4e58ec8b1e6dfe4000003000100000100000000001f8ef2a4fc9c8aec91840000030100000000010000000014bda1d781b08983f7f00000040000000000000100000003cccadbae9bd0d1b2c00001000004000000000000000001c9d6f8d2a79bffd0a6d30001020000000200000000000064e3f9849bacf2859def0003000100000000000000010003f6cf8d99f0e098c00101010000000002000000000019f0e0ebf1ecea9bd7fe0101010001000000000001000036d0a6e8cdd985bea00102000100000000000000000110c7c8cfbec0d8900200000000010200000000000015c0d3d3ed94a59ab9f10c,
  0x301010000000000000000018ab5ba80b8b893e2b493000200020001000000000000003b87b8adc9bdaef699c60003000001000100000000000024be9cb3c284d8e3dba40003000100000001000000000008d39cf4bdc8a7dcc0b80100000301000000000000000030b9a6becc8792d6b187010100000300000000000000000ad3a6c7dcf1c98fb7c5010101000002000000000000001b80c7b28096a6ec87d90101020000000000010000000001bfb4a8c7f5d8c8ebe90201010000000000000001000001f9f5e598b1f6aefe0300000001000000000100000017c3edfec6e09ca98c030001000000000000000001000cc8e2d6b2c5aadc03010000000000000000000001258ab8f4f4b7d70c,
  0x3030101,
  0x2040101,
  0x4020101,
  0x303050101040302,
  0x30300050401010302,
  0x60009d70000000300030a8000000200000403e0000100000203780100000001040605,
  0x10401001bdb00000301010114dd00010101030006ee0002000102010db901000100040004c005,
  0x6000000068e0003010101000ba000030200000101ae02000004000005c70201000200011205,
  0x60000000008b703000300000007c003010101000007c0030200000100780401000000010605,
  0x1050101,
  0x5010101,
  0x30003000db290000000000301010107fca0000000010004000112f9ee000000020000040003abd900000100000203000693c0000200000000000434c00100000000010301068007,
  0x30101010053e0d4000000040001000128b0eb00000100040001000185c182000002000004000025f2ef000100010004000034a9d8010000000104000002afa4020000000001020101cf9507,
  0x10401000000168a85000004000100010006fab6000101010300000002d300020100010200000ef9d000030001000002002199010001000400000005ccdf010201000000000233a107,
  0x600000000000791c800030200000100000693c000040000020000000a86e1010004000100000004dade010101030000000015acb0020200010000000106800300010001000100698007,
  0x401010fd200010104001587000201010205ce010101000305d904,
  0x4010100158701010400000fd2020101020005ce030001010105d904,
  0x4023b0001020301a8010001041003,
  0x2040036000400023d01010301018003,
  0x4020036010301010180020004003d03]

/-- The triples `(n, b, a)` of part 2. -/
def enumC2 : List (ℕ × ℕ × ℕ) := [(5, 35, 13), (5, 35, 16), (5, 35, 17), (5, 35, 18), (5, 35, 19), (5, 35, 22), (5, 35, 23), (5, 35, 24), (5, 35, 26), (5, 35, 27), (5, 40, 9), (5, 40, 11), (5, 40, 13), (5, 40, 17), (5, 40, 19), (5, 40, 21), (5, 40, 23), (5, 40, 27), (5, 40, 29), (5, 40, 31), (5, 45, 11), (5, 45, 13), (5, 45, 14), (5, 45, 16), (5, 45, 17), (5, 45, 19), (5, 45, 22), (5, 45, 23), (5, 45, 26), (5, 45, 28), (5, 45, 29), (5, 45, 31), (5, 45, 32), (5, 45, 34), (5, 50, 11), (5, 50, 13), (5, 50, 17), (5, 50, 19), (5, 50, 21), (5, 50, 23), (5, 50, 27), (5, 50, 29), (5, 50, 31), (5, 50, 33), (5, 50, 37), (5, 50, 39), (5, 55, 12), (5, 55, 13), (5, 55, 14), (5, 55, 16), (5, 55, 17), (5, 55, 18), (5, 55, 19), (5, 55, 21), (5, 55, 23), (5, 55, 24), (5, 55, 26), (5, 55, 27), (5, 55, 28), (5, 55, 29), (5, 55, 31), (5, 55, 32), (5, 55, 34), (5, 55, 36), (5, 55, 37), (5, 55, 38), (5, 55, 39), (5, 55, 41), (5, 55, 42), (5, 55, 43), (5, 60, 13), (5, 60, 17), (5, 60, 19), (5, 60, 23), (5, 60, 29), (5, 60, 31), (5, 60, 37), (5, 60, 41), (5, 60, 43), (5, 60, 47), (6, 2, 1), (6, 3, 1), (6, 3, 2), (6, 4, 1), (6, 4, 3), (6, 5, 1), (6, 5, 2), (6, 5, 3), (6, 5, 4), (6, 6, 1), (6, 6, 5), (6, 7, 2), (6, 7, 3), (6, 7, 4), (6, 7, 5), (6, 8, 3), (6, 8, 5), (6, 9, 2), (6, 9, 4), (6, 9, 5)]

theorem certs_ok2 : checkAll enumC2 certData2 = true := by decide +kernel

/-- Certificate data, part 3. -/
def certData3 : List ℕ := [
  0x20400003b0302010001a8040100011003,
  0x4010102d2cb0000010104000487f600000201010260f900010101000301c7ab010001000103118b05,
  0x4010100000487f601010400000002d2cb02010102000060f903000101010001c7ab030100010001118b05,
  0x104010012b5fc95f0e70000000000000000030101010ed3e391faad0000000000000002000102010fb7d3dcb0a000000000000001000100040006dde4f2d5a20000000000000200000100032f9595cbef000000000001010000000103029196d1d6800000000001000000010002022baea1a48000000001000000000001020204e8d984800000010000000000000101032dd798800001000000000000000100040283f08001000000000000000000010405a0800b,
  0x10401000047c1e3b0dba100000000000000040001000110f7b49cd0c700000000000002010001020036cbff87ffc600000000000003000100000202a1c78a92fc000000000001000100040000129ee8e2829a0000000000020001000002010d85b1fafef30000000001000000010400000befdbb38080000000010000010000010300029cf991c88000000100000000000004010023cf92998000010000000000010000040002d5f7e1f00100000000000000000301010bd48ace0b,
  0x3010101000001a7a291eda400000000000004010000000103f0989094f80000000000010004000100002390d48497b900000000000103000001010015ea92cda3d700000000000201000102000004c1e8e0f9af0000000001000100040000001b99f5d0808000000001000100000300010054a1d0d29200000002000000000102010003c7a4c7d6f700000100000000000500000001bdbf8080800002000000000001000000030aea808080020000000000000000010003488080800b,
  0x400010001000056edbbb49388000000000100040001000000018d96e9e5c8ef00000000030001000002000002acf8e5a5ac0000000003010000000101001dcf83a6f08000000001000100040000000048fcf4a9d4d700000001010100000300000031f2b2cd94890000010000000104000000001fdae5b3908800000100030000000000000201cee4a0b080000001010000010100020000018ee488ed9000010000010000010300000005dedcfa87c401000000000000040100000037d4cf88aa0b,
  0x4000100010000000be2ed88c59e0000000100040001000000000dfd8ba4e6c00000000201000102000000000297dbc9a8840000000300000101010000003184f9f7f200000003000002000001000003b098c7e6a800000003010001000000000105babefbe6000001000100040000000000018c819beb9e0000010200000200000001001fbe9edbdc000002000000020200000000059ca590d8c300010000000104000000000002f3d5d4908001000100000003000000010028c5eda0800b,
  0x10401000000000000098ea7a3968000000004000100010000000003c4d8e7cff300000102000201000000000001ef93fac9c300000300000101010000000003a1e4ccb08d0001010000030100000000000394e5f991b900010101000003000000000002e4fda8a6fd00030001000000000002000014ff83fdb10100010200000000020000007cadac808001020100000000000000020002c8c080800103000000000000000001012480808002010000000100000002000002d8ec82cf0b,
  0x10401000000000000000cd6ace0fbff00000400010001000000000004f1a4f1cff800020100010200000000000008ca82e5a69100030001000002000000000001b4db9798840003000200000000000100000698f2bc800004000001000000000001003bbbe4c001000100040000000000000003a0b8838aae01010100000300000000000001918891e6ca0101030000000000000000010283bf880102010000000002000000000184938a808003000100000000000200000018e3c9f0800b,
  0x30101010000000000000001aaaab1a6ef00040001000100000000000001afcec6e58000040100000001000000000027839dfa8001000400010000000000000002dba898abed01010103000000000000000002ac9e88fcc50103010000000001000000000698f2bc80010400000000000001000000588cdc8002010001020000000000000017b4fad4b203010100000000000001000006c3a88004000100000000000000010025908004010000000000000000000160800b,
  0x10302170201030102,
  0x20301170301020102,
  0x4010128ceb2c900000000010104003a8dced800000000020101021e8ac7d000000002000001031098e491000001000002000305a6aede00010000010000043dd5da010000000001000402b3c607,
  0x401010054e48aac00000001010400005ab782cb00000002010102001791e7fe00000003010000022885fdc300000200000103002dcff5e2000100010001030010f2f7bc020000000000010355eaaa07,
  0x401010000005283bfc5000101040000000001a18da0a2000202000101000079a1bcd4010101000300000042c18790020100000102000007e792a903000001000002000cd699cd03010000000000020180dfbf07,
  0x500000100000002df9584010104000000000011df98fd010300020000000013e5b3a3010400000001000001e28fca02010200010000000886d8b2020300000000010014c79e040001000000000166c207,
  0x302010a838a00000100050007f98f0000010201020afaf100020000000401dc80010000000302208005,
  0x40100010bacbb0001010301001796a900020100030005d68101000102020005c0a501010100020153c505,
  0x10301010003acbc0001040000010286ce00020004000001eeb100020200020004988a01000104000004808005,
  0x5000100000eb69e0102030000001fdf8503000102000008a0f103010001010006f080030101000001408005,
  0x40101069a828ffc000000000001010400099aa9effc00000000000201010204e087abc800000000020000010302dbbeb1db0000000100000200030180a6e5880000010000010000040ee6f7fc0001000000000100047cf8b801000000000000010403cda908,
  0x401010013c1eaf3980000000001010400000a91c583880000000003000101010ce5fefabf00000002000001030007c7bfc9b000000002010000010201c6daefc400000100000004010004928c82cc00020000000000010322b5fcec01000000010001010203f4d6f508,
  0x4010100000586c0c6fd00000001010400000060c185ea00000002010102000001919ac3b700000003010000020004bede969c00000003010001000101b8dea2c900000100010301000008f98cfafc00010001000103000001febbe2b801000001000004000018ded9c908,
  0x401010000000fcfa595a50000010104000000000f98fcb6ad00000400000001010005a6ca86c000000400000100000126cfcfd700010101000300000005b29ddfe000010101010101000012abd6a29f01000100010300000003d1a3e7d70101010001000100011bacf4c108,
  0x401010000000006ceafd7950001010400000000000d8980bfde00010400000001000003c6aeeff80002010102000000000de5a3ce8401010200000200000007e7cdc38802000001030000000002f4c28dff02010100010000000103ad93d20301000000000002001dc0c6b808,
  0x5000001000000002fabecb201010400000000000002d6e1de8b0103000200000000000391c59fec0104000000010000002ae2a1d802010200010000000001b8a8b4e002030000000001000004f7d2d404000100000000010029d2e80401000000000000010199e308,
  0x1030206cc0002010303010100047d03,
  0x1050001870003010203ee0100040102d703,
  0x10302000cb103000201200301000202c703,
  0x203010006cc0301020003040001017d03,
  0x40101000012eb8cf3b7f4000000000001010400000004909d88d09eb70000000000010400000001018fffb8abc2ee00000000000301000002004ed986adbde1000000000101010003000001a585d1979db8000000000101010101010004bea3c9c5bfd0000000010000020003000001e3bdf4c3f5a000000100000002000201002df7c9fef8f4000100000000010004000005bfc58393f8020000000000000000010312f8c0c9f20a,
  0x4010100000005c4939fbcaeb8000000000101040000000005bbaaf89df4f6000000000400000001010002a1e987e29ef4000000000400000100000126bfeca8f6bb00000001010102000001001995d79b938600000002010000010200000383c28f8ec3de00000100000004010000000e99bfd9dac9000001010000000400000002cdda8cc5d0b600020000000000010300001fd0a9ebc9dd01000000000002030000000596ba85fbe30a,
  0x401010000000001cfb4fe88eab7000000030001010100000001c6bac99499a000000200000103000000001cb0affcaed3000002000101000200000015cbe3f195f0000003000001000002000028f781b8b29e00000300000100010001000ef18c94c0e80000030001000001000001019befc595cc000100000004010000000048a2bc97db88000101000000040000000001eca5babfe001000000000400010000000987bf9194ac0a,
  0x40101000000000004d8b7a3c28fd1000001010400000000000002affff9f09ef8000003000101010000000003f6cccaf885ed00020000010300000000004799e6c38fe6000202000000010000010005bfc58393f8000300000100000200000071defaa1fad000030000010001000100002df7c9fef8f4000300010001000000000125f18193e4010100000004000000000052d6b6f787df01010100000003000000003de1eaf698e50a,
  0x2040016efc8ae000000000004000239cafdb1000000000101030101b2b5e380000000020000000414fee680000001000000030205f6d08000010000000100043bc080010000000000010402808007,
  0x402002eabe6a500000000020102010188dc808000000001000104002aded0ca00000001000300022adaefb600000100000201021082e480000100000000040101d5cfe0010000000000030209c4da07,
  0x1040000011dadadc4000000020200020075c1f0f8000000030002000103e080a300000100010400006ef48080000100000103010001d09d000100010101010116deafe301000001010100020280808007,
  0x4010001000eff8fbde7000001000500000009abedc6f0000002010003000003b4dd85a7000003010000010102c7f3d69d00010100010300000aeae9d4b9010001000004000001a4b2f8f2020100000000000308b39ac707,
  0x1030101000002c0cfb9b1000001040000010004a0cc9c00000300010200007ad5e7c300000400000100011cce8e80000100010400000001deb0c3bb00010102000101000184b5838902000100000003001bf09ac907,
  0x40100010000019ffd94ee000101030100000001bdc782aa00030000020100003deaeb9200030001010001002dc08080010000040100000032c2858501000200030000003d95b68f02010000020000010480808007,
  0x401000100000002d5e6808000050000000100000cafb281010103010000000004a7bee5de010400000000010006d6bf80020100030000000001b4e0b3b6020102000001000033dbddff03010100000000012692e807,
  0x50001000000000281a4affa010203000000000004a683c4ff030001020000000001909e9683030100010100000001a7f6b080030101000001000017dac080040001000000010001ee8080040100000000000108808007,
  0x401010001e0b9c3d799bd8e00000000000000010104000002b4d0b381ee8ca700000000000000030100000234ffb3e5def9810000000000000101010003006fc296f8fbebb80000000000000201000001026ed1d9f3b0c68200000000000100010001030061f0d9dff5d7ec00000000010000010000040014c88a9ffdead400000001000000000100040003838984da84b200000100000000000001040025f9add1ce9e000100000000000000010301029ddd84e6be01000000000000000002000307d1f1e0c20b,
  0x40101000002858eb3eb9a9e00000000000001010400000066e8a4ffaf85a300000000000001040000000123b3abaa879cce0000000000000201010200000bb3c5e19b9b8a00000000000003010000020006a6b0b1a7d28700000000000101010101010001a8f6d4e4f2c18400000000010000020003000038a7c6f6fbc0ac0000000100000100000400000d91e1cefad7c60000010000000001000400000285cde1cee8d200010000000000010003010018b5ab9f9ffa0100000000000000010301000184cbc4859e0b,
  0x4010100000001b8ea91b9b9dd8200000000000101040000000001a7bbae8ed0dec600000000000400000001010061f5bce0f1aef8000000000101010101010000029585e3dea9849000000000030000000200000110e8a7b2cbc5980000000100000103000100002e8187f5befd8e0000000101000000040000004badd1f7cb888c0000000101000101000101001bd3e8939ec6e000000100000100000400000022b1e7ecb0e0a600020000000000000101020002b0dee8fdbbeb0200000000000000010100021396fce1b48d0b,
  0x40101000000000001cd91f3d9df978e00000001010400000000000001f8ec82f392b9e800000003000101010000000002c8f98b91daba8d00000100030100000100000001ffbb95dbfcb98800000101010101010000000002f2d19489ebee9900010000030000020000000004c5a68d99d0a10001010000000400000000000192f5f381ab98df00020100000100000002000011c6dab5e094000300000100000000000200048ab4eae9afdc00030100000000000000000220f0c3cbc7840102000000000001000200001dabb6f098cde80b,
  0x4010100000000000036a183f7fea9b40000010104000000000000000182c799f5cd8f00000300010101000000000005d9e2f0cdcdc50000030002000001000000001c93e3bbbde09600000400000100000100000006c8f0e7bdabe30000040001000000000100000182e6f0e7b4a90001010101010100000000004ee1c7c1ebd2fd0001030001000000000001000c9ad5cfcffd00010301000000000000000142a5e282cf000200000103000000000000068089d0facfe601000000040100000000000011d9d5d583cea70b,
  0x40101000000000000000d85fef0beebf000010104000000000000000011e7e5cdecc7b600010400000001000000000006fef48fffa1da00030001010100000000000003bfc8d6ddf2e600040000010000010000000001bc80dddba3860004000100000000010000001bd2f798dbdf00040100000000000001000002dafa8efcb90101010003000000000000000d9ecda89f8e960102000100020000000000000a91c7bccfe6a601030100000000000000010014b4ae87a902020100000000000000000145ecd9970b,
  0x1030202e0f30001000203048900010100044693010000010404f104,
  0x105001882000003010201cf81000100040101b69c010001010312e104,
  0x103020001bcfc000104000101df95000300020101df8d010002030001e4e204,
  0x3010200049cd8000302000155f50100040100049ce401030000020180cf04,
  0x50100001882010400010001b69c020103000001cf81030101000112e104,
  0x20301000002e0f30302000100048904000101004693040100000104f104,
  0x4020009b8b098f6f30000000000000201020122d2f5b1d2800000000000010001040006e0ade4d9dc0000000000010003000210efb9c2fba40000000001000000050005af9da68dc000000001000000010202689089d3c0000001000000000101030a92989ba00001000000000001000449e1b08c0100000000000000010401eeb5ca09,
  0x401000102ca85e1ebb5fe0000000000020002020003a3ebbfbee0b70000000001000102020002878b869ee6900000000002000100010210b083cce8f8000000010000000400013fbaf5f69cee0000000100010000040005c8dea3df92000001000000010200020aadacd0d9800001000000000001040073fbf3ee980100000000000002010204c1a1d4d209,
  0x1040000010395f0eed9dcd6000000000003000102000398fbb1e9a8d10000000001000104000003d7ffade1edbe000000000200010003006cc299b789a10000000100000201020001c1b4da8080800000010000000004010022f3b0808080000100000000010103002ed7d6c90001000000010002000203d5f1a8a9b701000000000001000400168080808009,
  0x40100010005a9f6d4a4c7bc0000000002010003000005b4e6bf97b5900000000003000100020001a3aaf6e5a8990000000003000101000144af9b91c187000000010000040100000686e0e3bf8089000000030000000002010dffb5baf7fd0000020000010000020166f9d8d8a880000200000001000000030f91f2d8a4800100000001010001000201fda8f6d08009,
  0x5000100002497c6daabe9000000000300020001000884ede1d5fd000000000400000100010880808080800000000100010400000002e7c89dfaf00000000101010200010025ef96e7f5c3000000010200000300001ea3fbee8fcd0000010000000500000014f493f6e0800001000000010300010003cbfbb6b4c0010000000100000400002391b6e9ac09,
  0x401000100004f83e78e9f8f000000010301000001001c9ef3bbd1840000000200030001000046a5bed3c0f1000001000004010000000bcea1838a000001010001030000005a9affbac39a0000020000030000000104e7dfd1e0800001000001010300000011cd978896b8000201000000000003000394fddaf6dc0100000000040000010002bc84fa9ae809,
  0x104000001000017b1d9c9abed0000000202000200000007fa94d9b5c5000000030100010100004fd9b190d1930000010001040000000067ffa29ebae60000010004000000010017f792be83f00000010201010000000102bc84fa9ae80000020001000300000009bbb685c3a1000100010100030000002899f1c6d0800100000002000300000004e7dfd1e08009,
  0x401000100000005d7a192d8ca9f00000201000300000000058dc69dfbd2aa0000030100000101000002eb8addc79cc20000030101000000000104f8b9dae8980001000004010000000006ba8c8ccd89820002010000000300000020b9f9d9bbbf0200000001000300000010eeb998a9c10200010000000102000006d084c991df0300000000000100020020abd6e9d8c009,
  0x10400000100000001a3c6a9d69e9f000003010001010000001cd084b581e10000040000010001000030b9a29ac0800000040001000000010005ce8ad0a0cc0001000104000000000001ceeef9ecf6ed0001020000030000000053e5e4a8b4d9000202000001000000013bcdb2c0800100010100030000000035dac2cb92dc0201000100000000020060f7c6ffda09,
  0x4010001000000000487ffda9091fc0002010003000000000003aff2b9ccb1ec0002010200000100000001ca9a818080800002020100000001000013d0a5afad92000300010002000000006496bcdbf7820003010100000000010003ebd080808000040001000000000001178080808001000004010000000000039f92d9d5eabc0202000000000002000008b789a8a9b709,
  0x1030101000000000002d9a1bfd69cdc000300010200000000006d8f94cad1d2000301010000010000000cf8f3f3aeee0004000100000001000006f3c8b5e680000401000000000001004da7f7f490010001040000000000000195e3a694bf990102010000020000000062ceaf92e880010301000000000000010380ebe38c0300010000000200000010c4e28efcc909,
  0x40100010000000000439ae8acd4960101030100000000000066e7b6b9b782010201020000000000005797faa9ecbf0201020000010000000015bcf598b6800202010000000100000003a0c0a6ce800203000000000001000028c8e0ed80030001000200000000000dd29ab8fff50400010000000000010002a785c0b00401000000000000000107b9d6a809,
  0x1050004ece200000003010271dbee0000010004016edfc600010001010310ed930100000100040183a705,
  0x104000101a2e6a100000201030002d786000003000201018bbae500010002030001a9e4de01000001040013d4b605,
  0x301020022fb9600000302000156d4d100010004010039d1f30002000103002da29901000101030016d4dd05,
  0x10400010007f5c9f400020103000007f5b5f40102000102000188c69702000003010001c388d003000001000271a7d105,
  0x30102000002d78600030200010001a9e4de00040100000113d4b601000401000001a2e6a1010200030000018bbae505,
  0x1030200000076c8d001040001000038a88003000201000036b7c603010100010010ed930400010000010183a705,
  0x401000139d8fbe49585b0ab0000000000000001010301000187ba91b2cb8d98840000000000000002010003002da8d1dbd7fca7fe0000000000000200000102012aa7fa8796989cb000000000000100000101030003f4eda6b2e895fa00000000000200000001000309c1f9b5b7d2fc8300000000010000000100040004b4e1a0edf8ef800000000100000100000001034c839fc083fba000000100000000000001030106e9a8c983d1d00001000000000000010001032f8395d3f1d80100000000000000000101030193a9a0f7cc0b,
  0x104000001018dc7a2e4ecf4c1c1000000000000000300010200018ab7f5aac9a0ea95000000000000010001040000019df09b85a0faf5a00000000000000200010003002de6fdefa596c5b000000000000100000201020031fadbb6abf29bd60000000000020000000102010dbda08cf1a6f295000000000100000000040100129fe0f2fc80808000000001000100000000020202f5dca6f080808000000100000000000100040027eec58080808000010000000000010001000302c6c88080808001000000000000010000010309c0808080800b,
  0x40100010027f4adcb989089c00000000000000300010002000affba91aad9f9d80000000000000300010100010bd6f490f29b83bd0000000000010000040100001a9b8afee991c3bf0000000000010100010300000ff4da8d94a7bc980000000001000100000400000d8fe5accde4908000000002000000000001020101b6cb8288ba988000000100000000000104000023fbcd88b097d700000100000101000000000310facdc0c8c8a900010000000000010003000104cd87f08ac08001000000000100000000030117a49ddd80800b,
  0x4010001000002aa8383d5f4d8c4fa00000000000101030100000002aaba8fdbf4bc9bf70000000000010400000000010f9085e4d7b4f9f400000000000301000001010063c28f9e838e999a00000000010100020101000002c0a2dad7c789c99c0000000003000000010002003dfa96ae9894efcc000000010001000004000000019bb5d4eeeabbe6970000010000000100040000001ac8b68b9ec0cfb70000010100000001010100010989c4e7bacbd4e900020000000100000000000302a8c3c187898f9402000000000000000001020111c2e9d4e483e70b,
  0x104000001000002ef9f93f196cf87e7000000000003000200010000228586a0adb8f7e700000000000400000100010001bbecba9cb9bddce00000000000040001000000011796c383c1a385d0000000000100010400000000048bcfc8f1de9bb8e40000000003000000010200007e8d9483f69ba2b400000001000101000300000002cca58fa7c0a8a08000000100000100010300000037f2c2c9c2b097a40000020000000001000300000cee8dc0d3cfd4ae0001000000010000040000000c83c2abaec7808001000000000001000400000067908aa0c280800b,
  0x401000100000036efbbdd99cecbe400000000030001000200000016e7fdbcd0d09a8e0000000003000101000100000dbae487f6ac8fa200000000030100010000010007c88dd79ee1e0c00000000004000001000000015dc1a993d9b8cc00000001000004010000000027b7d49adceda2db00000001000200030000000001cac8ab9db1f8980000000300000001000200000b88c0fe81f5ccaf00000100010000040000000017a4a8808080808000010000000100040000000004b1808080808080010000000000010400000000308080808080800b,
  0x104000001000000018df1fabd87e5d5eb00000000030101000001000029d6c6918cc9aaa600000000040001000000010006b3f1dd86f99fca0000000100010400000000002bfbf585969ffeae00000001010101020000000002aea3d6a6808080800000000201000100020000000bc88e92fd90fd9a00000100010003000100000076e1c1fcfdf8afe10000030000000100000002000599a791bcc3b09b0002000100000000000300000de3c4f1f0a683d0010001010000000000030000028abab38bc1c3ce0102000000000000010000025c8080808080800b,
  0x4010001000000003ef2f089bf8784d8000000010301000001000000479a9edae088d08000000003000002010000000029858ddc969df5e900000003000200000001000011becaf4cdbee08000000004000001000000010002c9f2e4dca1c080000000040001000000000001168ccbabc580800000010000040100000000004fe5d48ab7e8f9e600000100020003000000000008f9d8fe848eb3d00000020100000003000000001de3c797eba0879500010001000004000000000028a0b1868ca8d3f001000000000203000000000004fbd7c0e0a2f8880b,
  0x3010001010000000002a0a8bd9dd0f4c4ac0000010001040000000000000288d4e78dbbb7f8bb00000100030002000000000001a883c2c9aecdf7e900000102010001000100000014b68dfcf7d682ce000100000400000000010000179aca8999a2e5800001010000010300000000000ff3bcd9c5e0899c0001020000000003000000000299a684c2e281f900020000020100000000000116e8f1e5bde79800030000000000010200000022d5aebbb2b595e9010000000400000000000100038296b6faa9d2a001000001010101000100000011adc3cab5d6ade00b,
  0x104000001000000000036f0b485afe799a70000030001020000000000003181ffbc96d4c6830001000104000000000000002aabbe8dc3f3afa700010201010000000100000004a3e18699aec88000010400000000000000000122f6accbc08000020001000300000000000009a6dcfb94f5c09d00030100000100000000010006f3cbe88fe08001010000010300000000000006b28eed91bfb1e101020000000003000000000002eaffbd88ccf0f301020000010000020000000009ebec81baab8c800200010001010000000100004fb1a7edb590800b,
  0x401000100000000000001d8cfb9b4a1b9e2ae00010400000000010000000018fca6a48880808000020100030000000000000001bf83898782eb80f20002010200000100000000004ef4f7acc0b29bd60003000100020000000000003eb1fcfeb1fb8ee901000004010000000000000001b8c891bcdcd0fdaa01020100010000000100000003ffb49aa08080800201000100000200000000000f95b888d1a6f29502010101000000000000010003bef0808080800202000100000000000000010d808080808003000001010000000001000036c6b6808080800b,
  0x104000001000000000000228b9692abaec8800003000102000000000000002092ceefbb8aacfd00040001000000010000000001ab9cf1f1aaeff701000104000000000000000021c7b380a8c499a50100040000000100000000000996d9d3dab8ec8001010300000000010000000036d6e887b8d68901020000030000000000000008dbc1b2e0be92820103000100000000010000001eb4bfe6b4e4c001040000000000000000010012e7d5bb93f002010200000000000001000002dda9ea81baa00400000100000000000000013af6f3c9b80b,
  0x301024dacd7e2000000010004014fdcfecc0000000200010303add8000001000101030eb8d5e70001000001000401b2bf820100000000010407979106,
  0x103020074c4f8820000000104000131aa82f7000000030002011a97c8850000010101020101819b858c000100010003011784f7a40100010000010301d8a0d206,
  0x10500000187a7a1b60000000400010126ea8bd3000001020003006dced6fb0000030000010223c0e2a10002000000030118b7aca20200000000010302a6cdb906,
  0x1040001000ba6968dfe0000040000010102a2c0a78d0001010004000009abe3c2fb000201000003004defd3910200000001030041e99bc20201000000000325e1f9a706,
  0x30102000003bcb0fef20000040100000111e1acec0001000401000003fee7eded000102010101000584eaa4d8020000010102003fbfdeae0201000001000230d5c3af06,
  0x501000000058c8cfaec00030002010000059282ba80010100040000000191a3e1db02010000030000018cf0e8f2020101000002007a94ddaa030100000000020bc1839d06,
  0x3020001000001e989f0840100040100000001c6bf8d910102000300000001c6a485f5010202000001002e89eec8010300000200000cd68d8a0301000001000103b0c1a406,
  0x10302000000004da9aa8a01040001000000298a80b30300020100000026d9d9c9030101000100000eb8d5e70400010000010001b2bf820401000000000107979106,
  0x1040001028ee1cc8ef2000000000201030002898ebb8f8e0000000200000301018acc948dae000001000001040006ecdf8ba900000200000001031aec9189d500010001000001030794c6abc501000000010001032ebb81cf07,
  0x1050000269fcff5a4000000000301020010fe8ecc8900000001030000021caec0d8c500000002000103001f9db599cd000001000101030018b6e8a3e9000100000102000203d39ce9b301000000010003011df5eee507,
  0x10400010001fa9d8ed6d300000004000001012282aedfd5000001010004000001dce4fdf28d000003000000020112fbf0f6ed00010002000003001c84e9f7bc000200010000010211b9fd91c002000000000003010387aa95e207,
  0x400010100069c959dfaec000000040100000155e5959ccd000001000401000008bb88c2edb30000030000020001019b9a9de4d8000100010103000002d0fdbff39a000102000000030001c791ddf3c101000001000400003fa2b2b6a107,
  0x50100000006f898def2a0000003000201000001e5cfc1a983000003010100010004b4aafdd7f4000004000100000142ccd0839c000101000400000003fbb3aef4ea000201000003000003dfe1da86dd02000000010300007eebbcc48607,
  0x4000101000001cd86e4ebbe000100040100000001f3c7eed0d3000300000102000020fea5f2cb010000040001000006d5a08680010100000400000031e0c7e6a401010200000002001fbcb28d9e01030000000000020387aa95e207,
  0x5010000000002bcf6d5e6b900020103000000000192eacb9ce1000301000200000001f2c4effa82000301010001000001c3b6c29ec8010300010000000101efaef6a8020000030100000001d4a7929edc03000001010001001d99e6cb9807]

/-- The triples `(n, b, a)` of part 3. -/
def enumC3 : List (ℕ × ℕ × ℕ) := [(6, 9, 7), (6, 10, 3), (6, 10, 7), (6, 11, 2), (6, 11, 3), (6, 11, 4), (6, 11, 5), (6, 11, 6), (6, 11, 7), (6, 11, 8), (6, 11, 9), (6, 12, 5), (6, 12, 7), (6, 14, 3), (6, 14, 5), (6, 14, 9), (6, 14, 11), (6, 15, 4), (6, 15, 7), (6, 15, 8), (6, 15, 11), (6, 16, 3), (6, 16, 5), (6, 16, 7), (6, 16, 9), (6, 16, 11), (6, 16, 13), (6, 18, 5), (6, 18, 7), (6, 18, 11), (6, 18, 13), (6, 20, 7), (6, 20, 9), (6, 20, 11), (6, 20, 13), (6, 21, 4), (6, 21, 5), (6, 21, 8), (6, 21, 10), (6, 21, 11), (6, 21, 13), (6, 21, 16), (6, 21, 17), (6, 22, 5), (6, 22, 7), (6, 22, 9), (6, 22, 13), (6, 22, 15), (6, 22, 17), (6, 24, 5), (6, 24, 7), (6, 24, 11), (6, 24, 13), (6, 24, 17), (6, 24, 19), (6, 27, 5), (6, 27, 7), (6, 27, 8), (6, 27, 10), (6, 27, 11), (6, 27, 13), (6, 27, 14), (6, 27, 16), (6, 27, 17), (6, 27, 19), (6, 27, 20), (6, 27, 22), (6, 30, 7), (6, 30, 11), (6, 30, 13), (6, 30, 17), (6, 30, 19), (6, 30, 23), (6, 33, 7), (6, 33, 8), (6, 33, 10), (6, 33, 13), (6, 33, 14), (6, 33, 16), (6, 33, 17), (6, 33, 19), (6, 33, 20), (6, 33, 23), (6, 33, 25), (6, 33, 26), (6, 36, 7), (6, 36, 11), (6, 36, 13), (6, 36, 17), (6, 36, 19), (6, 36, 23), (6, 36, 25), (6, 36, 29), (6, 42, 11), (6, 42, 13), (6, 42, 17), (6, 42, 19), (6, 42, 23), (6, 42, 25), (6, 42, 29)]

theorem certs_ok3 : checkAll enumC3 certData3 = true := by decide +kernel

/-- Certificate data, part 4. -/
def certData4 : List ℕ := [
  0x302000100000001dde0a095b000040100000100005386eae80100040100000000019ffbb6df81010200030000000001a0a3a1ca9d030100000002000017f289f0ba030100000100010005dd9ed68403010001000000012595ce8c07,
  0x104000101958bf3efe19f0000000000020103000196bde2c7f6d60000000000030100021ed2bcf3b700000000020000030153ed92e0a98900000002000000010313f8dfe58bec00000100000002010205f6f6b6a2d400010000000100010340bbbdb8e801000000000001010302b2d2a4a308,
  0x40001012e91e092a3ba0000000001000401003fa5a2cfbd8700000000030000010201abfae4be9700000001010000040013ffa698b5ba00000002000100000302fcecfea3c700000200000000010302b4b0bcbb8e00010000000100030141b9eaacf80100000000010002020384fca0a108,
  0x1040001000e95bcd0f1d400000000020103000048d9e1bfd1db00000000030100020033c988dcfcd600000001000400000131d2c4a3bc820000000200010102002993f18c9dcf00000100000104000025e78dbbdeb800010001000001030005f699da95f001000000000004010033fcccf28208,
  0x4000101002dbbb5fcd9b200000001000401000035b1f7c9b2e100000002000103000056e7fab6820000000300010001010ec7c889fda1000002000000030100108fc0e4888e00010000010004000005f6b8eac5be0002000000000103000786b4bcdd0100000000010400003fa2b2b6a108,
  0x1040001000006c0d1d59cc8f900000004000001010001e7dadddeb8c100000101000400000005b690809fc9fb00000300000002010028affc9fadbb00000300000101000134e98cc2948800010002000003000054bab6a9ea8400010100010101010001e8d2a180a4fc020000000002000101129decd9e48808,
  0x400010100000581cf82b9acb400000004010000010002c6d2988380b40000010004010000000887eb9eeb86d10000030000020001002ef8ada1b5a200010100000400000002f792cef2f3c70001020000000300000296c6f2daf7990200000000010300000a9caff98fbb03000000000000010216e5a7f09d8a08,
  0x10400010000002bbb819d91db00000301000200000001aa99c9b7ffb20001000400000100000180fc86a0c0f00001010004000000000185e883bbbb8f0003010000000002000c898ba6fdf001000001040000000035fc8da1eff701010001000300000003a3cea198cb0103000000000000027ec4e4ecc208,
  0x301020000000001f49ccfa58db000000401000001000001bd83c3aad89800010004010000000003d0e5a2efc88200010300000200000021cd9182d7fa0001040000000000010283ef80ba8a00020100020100000002a6a3dfc3b3d50100030001000001001dcf80c2edb00200010000030000006da6eab79fad08,
  0x1040001000000000de8b491e3919500040000010100000004b7eba2efa5d00101000400000000000a8d8695bdfc8e010301000000000001558b97879c0201000003000000002499d9abe7c10201010100000001000ea8d3a1eaa00300000100020000004fa8b0edfd8803010000000002000043bacd9cf78808,
  0x30200010000000002f6be8dddadfe00040100000100000031b98f87c3ee01000401000000000002a4919aaae6e701020003000000000002afa7f7ccd7b303000100010100000038f5c593d0d20301000001000100000fe7e6bbb1e003010001000000010001abf3f997c003010100000000000106b1dbb68808,
  0x104000139b0b2c0cab6920000000000000201030017cfa7c3bed8eb0000000000000300020112d8df8282b3bc000000000002000003011dbea0a7d1d0a7000000000100000104000fe38cefa094aa0000000100010000010302d8abefa0a39c0000010000000001020225e09ebde68c0001000000000001010302b584f6c7a30100000000000000020308e4addaab09,
  0x203010057b28dddc7bef80000000000000400010104c5f298c9f3a80000000000020001030006afedb3ffdac8000000000003000001021ba9f794919d8f000000000200000003010f83dcdf98c6c30000000100000100040006ada48b8dc094000001000000000104006ec280cefef40001000000010000010308e1aa98ff910100000000000000040127c0cfa3ad09,
  0x10400010079859addeaeede0000000000020103000067d899e784be8f000000000100040000017ce188efb7bac50000000001020001020001ef8e94b6bdeaef0000000002000003010008d4839c9081a10000000100000104000074e189e5bf84940000010000010003000116feed95fb8ed40001000000000004010002d283f28bc6810100000000000101030011a0efc3edd509,
  0x40001010010beaddba88eeaea0000000001000401000014d8ffb6b9a3d3940000000003010000000201badd9bee9bc2d00000000101000004000006cdbeafb5f881de0000000102000000030002bacc8c92f89e8b0000000300000000010201b2abefc0bbabcd0000020000000001030001c597ebe0a3edc8000200000000000101021ae1b48dfdc6d20200000000000000010301cecea8d597e209,
  0x1040001000008f08caef4c094830000000004000001010002f9fbb9a8dac9aa0000000101000400000007d2b9f7eda58f9d0000000201000003000048f5d6adb582cd00000003010000000002268df8eaf5bcfd0000010100010101010003f995dfa2a086a0000003000000000100021c82bf8ea9fbd8000100010000010300006da5b5e99584fa0100000001000103000009819ffbaed8fa09,
  0x400010100001598ecb688f9e4c3000000010004010000001ca5fab3cffac68b0000010001010300000001cae8aca6989ad4000001010100020001000caeb1b688e1d4800000010200000003000006fd939cb6e8a9f3000001030000000000020ad9a3e085d9b90001000100000301000001ffcff090bff7e40002000000000300000101a1fab2a3d7f5ae020000000100000002011be0dbacf4f6a009,
  0x40000010100000fe688f4fa9ac5ca000000040001000001000496a1a6898184e7000001000301010000001fc691878eddcaef0000010100040000000001f2d2e28b8791f80000030000010002000001e4b9b7b989cee1000100000104000000000b94c4b1ededbab50002010000000200000128d9df9ac289c30100010000010300000001bdb0a7ef9ecbef01000201000000000002059ea4ce92e0a009,
  0x400010100000001b7af82acdda4ec0000000401000001000001d6a1f390b9b7e0000001000401000000000395bdffeca3948c000003010000010001001aabbfd49f9ea60001010000040000000001a1fadbd780a6d8000102000000030000000198bdb1ecdafed7010000010004000000001fb583aae3a5ae0200010100000000000201d1d7a288bedc0201000000000100020006d9e491dcf7c909,
  0x10400010000000014cbcedcb2a4efeb0000040000010100000001afa1dbc3a5b79800000400010000010000038aafd7c0c7db900000040100000000010035c2e89bfb8da4000101000400000000000ec8f29ca0d6f7ee0002010000030000000004e0fad5e0aeade700030100000100000001039d9cd1aaafc40101010001000200000005f7f697a3beb5dc020000000103000000000ea5a9a7f4fdd409,
  0x40100000100000022e3ccb4f6d4f80001000401000000000060f2c68bfec7b1000102000300000000000ba2bbb2fd84bf0001030000020000000047d1d7db9eebba0001040000000000010001879b9484cf9a000300000200010000000bf6b7c0bc93900003010000010001000009999288e4b9880003010100000000000106f3c69b92a2010001010300000000003b8ce2b5adea8a09,
  0x1030200000000000057b28dddc7bef80003010002000000000006afedb3ffdac80004000100000100000006ada48b8dc094000401000000000100006ec280cefef40101000400000000000004c5f298c9f3a8010300000002000000000f83dcdf98c6c30104000000000000000127c0cfa3ad020100000300000000001ba9f794919d8f0301000001000000010008e1aa98ff9109,
  0x302000100000000002f99e4fd90a390000401000001000000001fc699dec0a8d40100040100000000000066fce0e6e7aae30102000300000000000048e79ee6e7c8c70103000002000000000023afce90db8f86020201000000000100004bc0bcfbcc980203000000000000010004ea89ed8ec60301000001000100000005b0d7dec0c6b80302000000000000000111c8dbb4d609,
  0x104000144edfdb892f0a6a90000000000000002010300198dcefd84bec5f8000000000000000300020118b9ded5e488ffc5000000000000020000030123f2a6b9eed5a9a8000000000001000001040014aed4cda5cbf2d4000000000100010000010303e7d280c3c6aea200000001000000000102023ec6fcdae1ebe8000001000000000001010305a2879dec93ed000100000000000000020321d096fbe8ce010000000000000000010460cff6e1d90a,
  0x203010002baf4898cd6e795bb00000000000000040001010df3c6f3ea88acaf000000000000020001030010909aa4eafced9b000000000000030000010267f9c29aa0a5cbb300000000000200000003013996e2b5b8d7b78e00000000010000010004001aadf3a2cfd8b5c600000001000000000104000495a1b29bb0ccf8000001000000010000010337a7f1e6f6b3c7000100000000000000040103b395e9a3b5da01000000000000000101030c84d893e2db0a,
  0x10400010002f9caec8eee9ba3ec000000000000040000010102c6faa3ebabdac9ac000000000001000203000005e5e7d2dfd8cdc3e700000000000300000002015faab6a083acffe700000000010000010400000188ac9383f89e9cf5000000000100020000030001caa2f3f6e3a7a5f100000001000001000202004cbfe4d3edc7b4f800000100000000000401000babd89ce6f8adb700010000000000010103007fc4f8a3c0be9a01000000000000010004000585b3e4e9ebeb0a,
  0x40001010001d9e59af0e0fad7ea00000000000100040100000192e5bdebb8ebebf300000000000300000102001ca9e2b1dfc0ebef00000000000300000200015dfbac9eefaa8cb000000000010000040001000187d683e3a1d5b1d800000000020000000301001facb1dfcd81c998000000010000010004000034c3d9abbbfaf3a000000100000000010400000990b9a485acb0f400020000000000000001033c94feb1c498dc010000000000000004010005c9e080ec8ca40a,
  0x104000100000d89d5fbc6ce8ea591000000000004000001010005d8e0e7c5cd93fad4000000000101000400000009b392a9f8e9cbed96000000000300000101000101f19ef7c2f7eeb2e700000001000001040000000285c3d0de9beac1a4000000010100010101010006a4cce5d8f59693e4000001000100000103000001ebcae5b6cfe881d5000002000000010001010106bc8afddadcdc8e000100000100000004000022aaa7abb6f6b3860100000000010000040000029194b7d0c7daad0a,
  0x301000200000001afdbcaf699b2f09c00000000040001000001001ae3c9b1e4b5c890000000010004000001000001bbafa8b9a7bfd7c50000000101000400000000019cbcac9992f5da8e000001000001040000000046ff95d292f2f7e0000001010001000300000037a1e1aefec083c000000101010000020100001bbaa7e9bbdb9d9400020001000000000102000bce81b4e49eb6f9000300000000000001000202f4dcd2cea5cb82020000000100000000030001bfa8b1938ffbd20a,
  0x400010100000001c0a2acfdbbb4f1d800000001000401000000007ded8781a7b39fc600000002010101000100000199db9eeacd8e98b4000001000004000100000062caca9b97c2ace100000101000004000000004fe3c99af2ae8aca000001020000000300000015eeead5ceec8f9100000201010000000002000decfdfec0f6b0b400020000000001030000001b9ee2d7b39194bc020000010000010000000201bfa8b1938ffbd2020001000000000000030001b5b4a1bb95cfb00a,
  0x40001010000000007b6c898c693beb68c000001000401000000000006c6c7f3f1bec3e88c000003010000010001000001898ef09bcdf7fcd0000004000000010000010012f8b981f29597e000000400000100000000010196dadcbe8d8a90000100000400010000000001b8f1c493c0cbb7d7000101000004000000000002dfcbf4c8fbc59dc6000102000000030000000079bcf2e6af96b5af000102000100000200000001bfcd9b9c97bde594020001000000000300000044aae1e5d8fed3c80a,
  0x104000100000000000299ffacd0a8fd84ef000003000201000000000006b9b38781949ed6000004000100000100000034c3d9abbbfaf3a000000401000000000100000990b9a485acb0f4000101000400000000000001bedcc6c6dfb2f2ee000103000000020000000003e7c8b799f5cbc0000104000000000000000105c9e080ec8ca400020100000300000000004b89ae81feb3e5d9000201020000000000010078a9fce388b1b801010100010002000000005fafeb9a83f6d6c40a,
  0x3010200000000000013eec0c9f3fbc4a000000401000001000000001ee4a3c5ab9dcbf200010004010000000000001b86bfa5dd83d982000103000002000000000019ab98f293fc8400010400000000000100000183fcb194ffa78500020100020100000000003dcdfbc884fae7bc00030101000000000001000bcc8af7cbd78e01000004000100000000001fb7a1bac2cdd590010003000100000100000006fa94e4dbb584e801010300000000000000013ad694e6dba10a,
  0x104000100000000000008b9a6ce81d29989fb0004000001010000000000039de68c9ba6eef8ec00040001000001000000000392ba9fb4b0f0b0010100040000000000000006bdd0adaffedda3c001040000000000000001000feee5eba5a5a4020003000000000100000013b8c6bfd58dbcb0020100000300000000000024f3bdfff486c0f5030001000001010000000077eeb58294ebdeec030100000100000001000002828fbde0a8c5f603010100000000000000013895f0dca1fe0a,
  0x302000100000000000064a1b3d79ac9c8ac000401000001000000000051bad2b596afcad0010004010000000000000001faba8cf9a0c78ef3010200030000000000000001ad8ac5c6fff3bc8f01030000020000000000005db8bffbedb0c18a020201000000000100000001fa9bf2eb87afa0020300000000000001000015889cf7b0cfb403010000010001000000000f9ec8828e99b98803020000000000000001000186c0dbefa2b804010000000000000000010382bfdb86e40a,
  0x400010108c5b6ccf1b5e4bba0800000000000000001000401000b9db4f1a4eae68bbef500000000000000030000010226f5c8c8afaecc809b00000000000001010000040004b4f385dad083afdcd000000000000100000100040007b2e6c1dae8ddebb000000000000101000001000301ade5a3cffebcdce3840000000001000001000100031fdfa6d8d4fefcbbfc00000001000000000101000303f2aa96f9c2a5808e00000100000000010000000428df9cb8d0a4eb8a00010000000000000001010301ffebd4b49ee4f201000000000000000001000405da9cb9afb9e60b,
  0x10400010001ad8581a3c6f884ee850000000000000004000001011fa5a6cbfbf4ddc59c0000000000000101000400000186eaccd7abcb93f98f0000000000000300000002012787b9c5c4c1a49cef0000000000010000010400002cdfe59d9b8ca1b1ec0000000000010002000003002ad7b2c9bbaac9f6f00000000002000000010000030aead4eea7b8e6beaa00000002000000000000010301f0c5c9ff80daf5f500000100000000010000040037d1b389acc9a38e00010000000000000003010103ee91d39984c7f60100000000000001000002020fcaf1c3a49ee20b,
  0x40001010006f6adc7d2908fa1939200000000000001000401000002fed58b8d9d99eeb2e70000000000000300000102000191a2fffcece0ddf4ab000000000000030001000101039bd6e1a4928be78db000000000000100000302000006be92d4a7f4cfb9c29800000000010000010004000052fccf9acf96fd90c00000000002000000000103004eaefe9fc6e8b8e8b400000001000000000104000030b9e6b9d084d3d58400000100000000000103010006c3da87e1f7c6a3fc00010000000000000004010043c8d2aa9de8e89c01000000000000000004000102bdebe0b091bc840b,
  0x104000100000ba6f2e1d4d2ebc4d7ca00000000000004000001010002cad3cfe1c2a996e9dc00000000000102000102000008d68dabbdfaf7d396c000000000000102010100000171e2b3b1c2c2f4fdd7000000000003000001000200048a8f8eaacbfb96f1c600000000010000010400000008a9e4e9bbb3bca48ed9000000020000000002000101018ec990f281b2faa1f600000100000000000401000032ebb8d0ac9493e4b4000100000000000003020000058599c4e1bdeafd9500010000010100000000000332f982f8b08a859f02000000000000000000010310f6b891bcdc81c60b,
  0x400010100001785a58bfc97de8586ad0000000000010004010000000688ea9ba9dafcc598f700000000000300000200010012b38badff99e1f0aee200000000010000040001000015c6e5ef99f3b0a4c7c800000000010001010300000006eac79bde9addd39be400000001000001010201000007f1ba92deabadf1828c0000000200010000010000023191cdafd0afeee9b500000100000200000002000101e192fce0e7f6a3e1b20002000000000000010100020ddda0cacb82c3def501000000000100000004000052e398f3c6e385ae0200000000000000000003013882dd92e0caedb80b,
  0x104000100000007f49ee889a9b2bea2b200000000000400000101000001eefce693b2f0ddc6d400000000010100040000000006a9b6c896abf3afe3eb000000000201000101010000038bf8f386baf3e2b69b00000000030000010100010038a5aef0e8a4e7a3d100000003000000000002010001b3da96dcba82e09eb7000001010000000004000000019b8fa9a9d3bffbbceb00000300000000000001000206e29cf0fd9e80bca700010100010000000000030006be8dd4bbcfa6cfc400020000000000000300000109fff0f999cfe688da010100010000000000000003028488f2e7ffda89bc0b,
  0x10500000000006296a1eadc8fb8b4cf9000000000000400010100000046a184cf83b8b3a0bd9c00000000010400000000000109c9c5cee4fce3ea9c0000000003010000000200000ee8a089beebb6cba5ab00000000040000000001010013f5988afdde9bfb88d50000000101000004000000005aede19297a3b7a0d3c30000000101010100010100002acbfd9dbf84c4f4a5d100000100010100000300000027b396fe9d91f2d6d28c00010000010001000300000004a7d5d0e1ebcee8b8f700030000000000000000010271f2fa97dc9ae9afc702000000000000000300000123fbdca8b1869fc7da0b,
  0x10400010000000001c8c2caabbcdac7b980a00000000004000001010000004dc8c7898df5a0afcab400000001010004000000000001c0d6c0abf8f2e4f9b89300000003000001000200000014ffe4c7bbb2d897a4e200000003010000000002000013ace8abdea7ed9f86950000010100010003000000004adbd491fba8c1d2a0cc00000103000000000000020005e8bc8a8ceaefb3e6aa00000300000000000201000018abffb48fc49b81a4ba00020000000100000300000011ab9ec4a79badd3d9c20100000100010100010100000293ddacf6b894c78b9a0300000000000000000100023bf8ef98d1dfdfa2960b,
  0x40001010000000004e6fee0b88de6ac91c40000000100040100000000000593aa988ca9d8f7c59f00000003000001020000000001e99ea99d9be6ce8eb200000004000000010000010010b7e9c288bbe2c4b10000010100000400000000000190c08bd7f2cbc2b3cf00000300000001010000010002c9bc8f86e3a682c70000030000010000000200003cd1af9b82a38beb8c00000300000100010000000101adb0ccc5aabc86a8000102000000000003000000019adcefd297bad395d800020000000001030000000007e4ed8590d4bfc5b001000100000001030000000013e0aea2b2dcce93e80b,
  0x104000100000000000affdee0d6e6c4fad5b00000010100040000000000000bbdb5d991e993c7dbf40000010201000101000000000ae08baae58288b3c4970000010201010000010000001ae4d2e99f95fc91a000000400000001000000000158f88fdc91c584fd000101010100000101000000029acee88f84b085f78b0001030000000000000200001c929fea99c9eecdfc00020000000103000000000002d5a4e09be6959092e60100030000000000000101000cc4b9c9d598c8fdcf01010002000000000002000010fde2d2998ecba9ba02010000000000000300000041b7beb3eab38aadb20b,
  0x40001010000000000529dc4f4cbb0e5a4a000000004010000010000000003aabcdacc91c4f8eeb00000000500000000010000007287a78eb4a8e1e7f800000100040100000000000004cbc6f0bc8cdf8bca8700000300000102000000000039dc919ca6928ea6af00010100000400000000000002c9e4d997f3fe9eb4d80001020000000300000000000289f8c9f3c988dfafec02000000000103000000000028a0948487e79ac1da0201000001000000000200000a95bec3a2b79dc7a4020101000000000000000200018b9da7f8afcacda403010000000000000000000206e2c9d3e58b9a9c0b,
  0x10400010000000000000bcaab99a8c0f3f0fad6000101000400000000000000088fbab7baa7a4faaf8500010200010200000000000004aecce69efdcf8cd5e500010300000002000000000003afd0baf5a1f3f3a9e900030000010002000000000079b7f8fbfa8d8c94e701020001000000020000000015a8d9e282adacf1f0030000000001000200000000018abeae84bbc2c7cf8003000001000000000200000020a6c4a6b5ade2b8d80300000100000100000001005a8bc38dd2b6b5d003000100000001000000000103a7e580c097a5b003010000000000000002000004ad91afebfaaeeda80b,
  0x401000001000000000001aeeeafcdacedd6d1b800010004010000000000000002c9da8b9dd0fe8cb8de00010300000200000000000001e5acbbccb792beeebe00010400000000000100000007c296a7fc82ebd7d400040001000000000000010007dca3a6b2898fec0004010000000000000000011f95e386c8bdc4010003000100000100000000069187f2cdfdb786c601010000040000000000000001afbaf2b9e28ed7a6810102000000030000000000000f8dd3e7d6d381969401030000000000020000000012cce5e3a7f2f1b9b10200010200000000000100006fa2e692d992c69c0b,
  0x10400010000000000000005d1e080d5a4d5e9c9c400040000010100000000000002939d90a3f1ec87ba9a01010004000000000000000004a3d7c8cedcabb9e5d101030100000000000100000001f9958bbce192c08701040000000000000001000014afce9ca892b5c502010000030000000000000014f3ed80b8e0a5d5a60202000001000001000000000fefd3acaabfbe9dfe03000001000200000000000001e1bfd4a4b0d0df9b0300010000010100000000005acc8588ecd2dda79a0301010000000000000001007ff5ea9a8fb2b904000100000000000000000102ed8e9cd7dcf30b,
  0x40001016cb2bea0b485d2d697aa000000000000000001000401000198d6c4a58f83ac8accd4000000000000000002000103000381d3cdfdaae1969a9500000000000000000300000102168fb6d8d695acd2cbab0000000000000002000000030127d685acf4d9b7d496d40000000000000100000100040014b2dfa8b98db88c979c0000000000010000000001040003ed8981e081f5c2baa80000000001000000000001030143f3b4ca9ed1c58adf0000000100000000000000040106d391b8d7ecfeaa840000010000000000000001010338a1bd9ec584b9820001000000000000000001000402a0c0b0f9f1fd940100000000000000000000010405a68890d9e3b10c,
  0x10400010013bdffd8c5f5c7c5b9d5fb0000000000000000040000010104a6c8e6e18ae3f8eaacb5000000000000000101000400000dddaeaae8ccf6bbe5c8fd00000000000000030000000201058bd4e7dffa8681e0e9e10000000000000100000104000006b0f6aad79897e69ec5a8000000000000010002000003000489e2ddc3f4caa6aeb9880000000000020000000001010201b1aadbecfdd9e5defd900000000002000000000000010322a0fdb0d8a4a0dfb8960000000100000000010000040009b4e1c5bee4bbd6fed0000001000000000000010200026fdbb78adae2cffda80001000000000000000002020106a3cdadd5a4d2ad900100000000000000000101000314d9bae3ae90ee940c,
  0x301020000059dae94efc98bb1ecfe82000000000000000300000102000195fbd0cfac9f9dd29fc300000000000000030001000101028aa7f7c9a39f87eae7d50000000000000100000400010003b8f390c0d39ab28289f20000000000000200000003010028daaabcb3de8e99e5cd000000000001000001000400007fb799f3b3b9e598dee20000000000020000000001030010c485c8df9fc0e49ef30000000001000000010003010023faee84b5a6ebc6d89b0000000100000000010002020005ddafa8d7f68b9de3d4000001000000000000000401004eefcc8da8fab987ca000100000000000001000004000592848ac3d495a4a40100000000000000000100040013d49fdafd8aa5f50c,
  0x1040001000004d4dfbcf9d8b7c5db83b4000000000000000400000101000693f5a3f4f0bbf5fbd2b70000000000000100040000010002fe87b399eac39f9eac910000000000000200000301000003969dbbb0ab83f1a9cd860000000000000300000101000101cfdb9ea79ff68eb7958a000000000001000001040000000581af88b6dabdfaddbddb0000000000010100010003000001b8c08781b0d990f3d5b50000000001000000010301000001f2a498b9a2d09f95c2d60000000100000100000004000032c5d4f5cccbf9ddcca800000100000000000101030000078f84b0f9e795cac8d4000100000000000001000400004de089f0a2f6d78dc8010000000000000000010400000385a48b91f4c4a3ca0c,
  0x1050000000022a8e5f2edb685cffbe5840000000000000004000101000017efc4f4c8e1f4bbeec0f6000000000000030100000002000bf792acf19388c1dbd6920000000000000301000001000104a6d481cfffb7f6c6e6f2000000000001010000040000001cc8a9b883b9e7aeaceee20000000000010200000003000006d798e69893ded4c8b2f10000000000030000000001020001ecfe99a5f794a4e0b8e700000000020000000001030000059fa5b8d6908e8eeec9b200000001010000000000040000039fd4cdf1faf5a9a6dfb00000010000010000000004000042aa8cb6f9defd87c5d800020000000000000000000301039ac5f6a3ccb28efcb8020000000000000000000001031299abccbcacf1d7d60c,
  0x104000100000003daebb5c890b5de978281a3000000000000040100000000010bb29bd7e692b7dccdaea30000000000010100040000000002edddd6b98c81f1f8e0b9ff0000000000030000000201000001a2d4e3ced08aa4eb96b9d10000000001000200010101000002badbffd4c9b487f7aabfd3000000000300000001000001010684fe9cb1c9dce7afb890000000010100000000040000000fafa48cb6ead1b1bbebed000000020000000100000300000fa69fbebf93c89b96d7f600000002010000000000000300158b9acaf1a7989ffee9ed0000010100010000000000030016b2d6a582dec8c9a5e4860002000000000000010000030001afe183cfdd9aafa08ade0100000100000001000000030013e0de96add9e4c8c8d30c,
  0x400010100000002ec8f9894a59fa8a8fe8e0000000000010004010000000003bdfccef1fcddfc8ffe9f0000000000030000010200000002feefd1abfc859ceedf0000000000040000000001010058e4b091f9dbf8feded00000000000040000000100000109e4c39ef0edc9c6b384000000000101000004000000007c89c79baadfebb3ca98000000000200010001010100000196e28986d0d887accfc400000001000101000101010000528bf7cce999fb84c6f4000000010100000100030000005be2939980e282b3ad9c0000010000010001010101000027b7f0abd9f4bccdf7880002000000000000000103000002dafcafa3d996cecaa8010000000000000004010000002bdcd790bbd0b0b4840c,
  0x104000100000000049af8ecc2f7cae181abd3f80000000000040000010100000001cfaecbbbe5bae88982cfdd0000000001010004000000000002808b8089cdc2a29298e2d2000000000300000002010000000181ccdab188b7eca8e7cf8c00000001010000030001000000028db79eebeaa39fd0f99bb700000001010100010100010000778b988e8799bdbcd4968b0000010100000000040000000029c1b2bc8e96d693c4b1f0000003000000000000000201001ba1b3a8898bddaaaaa3e00002000000010000000003000004ad9fc6d5cbf8edbdc2f70002000100000000000001020004b7c2a6fa84d6fbc8eaee00030000000000000000010002019af5ade0ffe4978993f2020000000000000200000001016afdd4e9e8e3ef85e1e40c,
  0x40100000100000010cad6e18b9292878ac9c50000000001000401000000000014989ab2a5d5ebdfa6e5dc000000000300000102000000006982a9d4e899e6b599be00000000030001000101000000049fcfa49fc1eeb7d4f9ab0000000003010000010001000005f4d3b8eed9c8e4ead6b800000000040000000100000100018291bfc7c7d9c98186b00000000101000004000000000004d880c1bcd3c5bcae92e5000000020001000003000000000c98c28fb982c2b6bdb4d300000100000100040000000000099c8c828dac8fcadf97c10000010300000000000000000211868f88e89a81faf70001000000000104000000000001e2ecd3af82c3c9c7c4b00200000000000001020000000109feffb3f394acc4c2ee0c,
  0x1040001000000000020c9e3c1bec3a4d3a8aea10000000004000100000100000020b2e4f392aac6b6b28596000000010102010001000000004deab086eefff494f2fce20000000104000000000000000108c58d829bd2d9ba94e40000000201000003000000000033f69dc0e7f1fbcfd9a1e50000010000010400000000000035c4fdf9b5ccbcc0c1a6d8000001000102000101000000001180b4fbc7df9d9bb4e08c0002000000000003010000000002aeccda8effa082cec4ca0002010000010000000000020043e2a59dfcb5b5acc1e80003000000000000010002000003ecfabca2a3eff5ce90a40100000000000401000000000001b288888ef5ecabc9b5e60100020000000000000300000042c988f58fc78396c5fe0c,
  0x4000101000000000014f0b881eeb1bfb88a809b000000010004010000000000000f93b79b91d4b18cdfd8a100000001040000000000010000019bede9d3f49ee4f5b0b80000000400000000010100000003dee6f9ced3ccfac3b19c000001010000040000000000000bcbec80c2f285ebadd2b50000010101010001010000000008d5b7e3b8b3a1a8c3ef98000001020000000300000000000683de888affbadba78b8f00000102000200000000000100138ea3d7fa9d9ba188b0000002010002000000000000010189be84d8fd96cf80dc00000300000100000002000000558e8ce396a2accce9fc0001000000040000010000000007d5dff3849cccc8e09ab00100000000040000000100000079a7b7e3bbb8c5a7ebdc0c,
  0x104000100000000000012c98be5fcdd88df8ccb00000003020000000100000000019febcbc8c8a4c0d1e7bc00000004000001010000000000019d88b6a8adc5bcb9b29e0000000401000000000100000025e4e495ffc4ecbdda900000010004000001000000000002c3de8380e294f0bddb82000001010004000000000000000382ce989cfc99d5fbabe900010000010400000000000000269cdbedceacd8b2a6bf0001010001000300000000000001e6cf8fb7e9c2998bd49d010000020200000000000001004ad2c486bcb7d496d00100000301000000000000000103a7c28df3d9ceed84010100000000040000000000002ee28795a18590a0c2ec010200010000000000000200000381f4f6eea1b49db7c40c,
  0x30200010000000000001edfc0e8c2ecb0dbe9c8b40000000401000001000000000005b4a0fb8dd386c9e999db0000010400000000000100000001838bccbfaadd93c9cc86000002000300000100000000000a85ebbbdbb7afe0b6e085000003000101000001000000000687a781b7a280e3debbe00000030101000000000001000016e3a7cfec96f8a1e8c00000040001000000000000010001f8e6d2e7a2fbe3c5800000040100000000000000000109ddd9f0b9a88dd8a00001010000040000000000000015f4f3c3a9c692b1f6bbc80001020000000300000000000006eddb99e0aed8e198efc4000200000300000000010000001ed3a9d2caafbee1f4fa010000000400000100000000000598d7949799ad94ca90a00c,
  0x1040001000000000000000bbe9fbcc0bf92f2f5cdab0000030100020000000000000013d7a090e29d89d2e6c70000040100000000010000000056a6eebde6aa829086f4000101000400000000000000000a9aa993c2ddc8c48fa6810001030000000200000000000004f2e2f9dec6b4de8d99a80001040000000000000001000001bda5b6d395bfbc9298000301000000000200000000002cdce2e0f896fbd4f3a1000301000001000000010000000de08b94eccece94a2b0000400000100000000000001000caba3b2ef96e6a3f0000400010000000000000000012f96ffa792cbf4cc0101000100030000000000000003eba3eef1aab6f9c6fcfd010102000000000200000000000193ef96bec3e0b2ecc8cf0c,
  0x40001010000000000000006abd0ae9de4aec8d8b7db0000040100000100000000000003eeb185e1fbe6c69fc7fc0001000401000000000000000009c9b4b7a9d4ee97b0efe10002030000000000000100000004dab0e2dfb29debbfa80003000002000100000000000001aefbbeabcacac086f79c0101000004000000000000000002d5c9d7e3c285ab9dafa40102000000030000000000000002dc97abcce8b1f2cec3e70103000000000002000000000058d5adf6beecf2efbec80201000200000000000001000037eddbc5adb1a7fed4020200000100000000000001000391e6d6ead2a996c8030100000000000002000000001190bed8ac9290afdc8b030100000100000000000000010aacddb1d788b78a0c,
  0x1040001000000000000000004e5dbe4e2b9b891c0cce5000300020100000000000000000c86ceb7f5ab84d8e8d40004000100000100000000000051cafda1e4b5e0b0dcf0000401000000000100000000000fb4a4878087d689e9a00101000400000000000000000003abc6d1e5d5c188aca8fe01030000000200000000000000019ed895b3d2e5ded0dad001030100000000000100000000028fcdd2a8fac694aafc010400000000000000010000001accc5e2dfb3f9a890020100000300000000000000005bbfaeb0d68093e0c7c10301010000000000000001000001e185f4fa9491e48804000100000000000000000100098281c3e7c7f4d0040100000000000000000000011598a0c2e78dc40c,
  0x10501050301030302,
  0x10501390003010325020001040e03,
  0x1050100390301030025040100020e03,
  0x105017d00000301035200020001042a01000101040704,
  0x1050100007d03010300005204010002002a04010100010704,
  0x1050116e90000000301030efb00000200010408e000010001010402980100000100050e05,
  0x105010001b8fc000004000201798d0002000104002ca400030001000322f80101000005001de005,
  0x10501000001b8fc0004010002002ca40005000001011de0010200040000798d03000100030022f805,
  0x1050100000016e90301030000000efb04010002000008e004010100010002980500010000010e05,
  0x1050101a5d1000000000301036ca70000000200010444ae0000010001010414c10001000001000501d2010000000001050706,
  0x105010000000001a5d1030103000000006ca70401000200000044ae0401010001000014c10500010000010001d2050100000000010706,
  0x1060101,
  0x2050101,
  0x3040101,
  0x4030101,
  0x5020101,
  0x6010101,
  0x1050100006e9fc5b70000000102000400004780d5e000000001040000000203fc8cda0000000202000003003defd4f7000001000300000300049cb4ba00000300000001010212bbbcc600010000010005000009ba8483010100000001000301628e9508,
  0x10501000000002df8f4cc00000400020100000020a9c4e600000500010000010004b0d0f800030000020200000019f2b0d600030000030001000003c791fe0004000000010200000186f1b60004000100000100012a868903000001000003000006c2bbc308,
  0x10501000280a3e28400000000000004010002038c899fff0000000000010005000101a7c59f8a0000000000020001040002f0b397bb000000000100010104000282c0e4800000000200000001000418cfa880000001000000020001030683e080000100000001000002033790800100000000000000050101e08009,
  0x1050100000061e496a8800000000005000001010026b2e2bb940000000202000003000027dbf6c0bd0000000301000002010014c997d292000001010000050000003db0d3f0a50000030001000001000201add1fd900001010100000003010006898e98ab0003000000000100010202dfa3a2c70300000000000000010336a0808009,
  0x105010000000079e8e496920000000500000101000043cdb8e1d30000000500010000010014899c8080000003000100030000002ef99d89be000003000101010100001e81fa8be8000101000005000000004bb1cfefce0003000000000301000002ded992c5010100010000040000000bc193afcf030100000000000000034c90808009,
  0x1050100000000000008b0fbd2bc00040100020000000000029df9c68c0004010100010000000004a5a9d4c00102000400000000000005cbfae6b9010302000000000100000ce7fc80010401000000000001007592800300010003000000000003c29fc9980400010000000200000034a8c5800400010100000000000103dc8009,
  0x20400010001e8dce7cfdb00000000000005000001011d85ab8ca600000000000102000400002bc4f3c7a000000000000300000300014984ba95f0000000000003000100030025d9aa8bf80000000002000000040100438ca19aa2000000010000010005000020eebfa4b0000001000000000105000005a485ccda00020000000000010000042098d2f2020000000000000000010401b0ccd90a,
  0x105010000000000004cf18bc3b1000005000001010000000036ee96c48700030001000300000000001eb5b5d3ae00030001010101000000004db8a3e400030100010100010000000e8ae4a1f000040000010100000100001bfdf29900040000020000000001001bcbfdf400040001000001000100000285dff7e901010000050000000000002c96e7f89602000300000100000000010197afba0a,
  0x105010031fac5e4e7bc0000000000000000040002012185a18687ef00000000000000020001040021f5a989b08800000000000000030001000306c5c9efacf00000000000000200010001030dcdc0a8d4a00000000000020000000100040383808984c00000000001000000010200037aeddea6800000000100000000010003020dd3a6f6800000010000000000000005010181b7848000010000000000000001020305e0a8800100000000000000010000050ef0800b,
  0x105010000518eb8beacea0000000000000005000001012eadefc3df9e00000000000003000100030020dfb986c3ee0000000000010100000500003a95ffedf4b600000000000300000000030101a0a1cc8fee00000000010001010001030011bbc2dec08000000001000100000100040019a4e2bfa50000000100010000010102010389efdf9cdb00000100000000020000040034b2c89bc000020000000000000000010401fbbfc1840100000000000000000500011192f0890b,
  0x1050100000055fdf7b8b9a200000000000004020000000119aeafa4c095000000000000050000010100648cce9ade820000000000030001000300006ceea4b3c5f200000000010000050000010040bebdcaeff20000000001010000050000005ec3aab0eeaa000000000300000001020001699ba8e0cc000000010000010005000000318ee694808000000100010000010004000009adbe9080800001000001000000010400000188edc08080010000000001000001040000078e8080800b,
  0x40100020000000f9ac7a8eba99300000000010004020000000004c4fd82b183ea00000000040000000102000005a6dd81c3de8200000001000005000001000004bdbdfeffd3fc0000000101000005000000000aaca1d98893da00000100000005000000010003abc8e1d7b2cc00000200000001000400000036f4d7fdc2c900010000000001050000000034bafd83e2e200010001010100000100010123edd281adb400010102000000000000000301bfd7f0de9202000001000001000000000303b3bbd3fdb20b,
  0x1050100000000000c95a3acf1e2000000000500000101000000099fb592b7fb00000004000000010200000001ccd6d89cbd00000004000100000002000001fc8ea9f1820000000400010000010001005484e3a5d600000004010000000100000106aef490b700000100000500000100000001848493a0a60000010100000500000000000980a9eab3c6000002010000000400000000028597b6c48a00010002000000040000000003b1cecce8800100000101000004000000002fa6ea90800b,
  0x5000001010000000025b2c3b8f1eac00000010005000100000000002a9fddd180939e000004000100000002000000058fa68a889680000004010000000001010000758ea2a782c200010100000500000000000022c2cecaf7cca200030001000001010001000001a4a2b488fdbe00040000000100000100000101d5ea80808001000200000004000000000004c19bc69df199010200020000000000000200108a8ca08080020001000001000300000000499897b2b2d60300000001000000030000000ffab781c5ea0b,
  0x105010000000000000001b5fbc4e3ccb20000050000010100000000000184fcea99c9df00030001000300000000000048d4b1b8919100030100010100010000000020be8c9fba9300040001000001000100000006f1ef8bedc601010000050000000000000069c9afdad78601030000000101010000000006a3ddfec8db01030001000000010100000030e992bd9201030001010000000000000126b7c69d02030000000000000100010008e7b2e1a80301010000000000000200003adbfd88e00b,
  0x30103000000000000000029d788de8be000040100020000000000000006fac5b798e600050001000001000000000004a2ada3ac8000050100000000010000000056dcc2c8800100050001000000000000001ed3a9cdbad301040100000000000100000009d1b288800105000000000000000100005baeb08003000100030000000000000005dcde91f1cb03010001000200000000000009cda5efc3800401000100000000000001000487e0800500000100000000000000010ac0800b,
  0x500000101000004de9ba2e9bbbb0000000000000500010000010002c0a0b7ebfcfb0000000000010005000100000004b4fd94e295b5000000000003010000020100000483ffb58f98850000000001000005000001000002ae8cd7fbc9e20000000001010000050000000007cbe29199f9d30000000002010000000400000032f3f3ed9fa80000000100000004000200000003c2b1cc93f2f400000100000000010500000000369bb1e9f6d9000001000101010000010001012aa68c9aab89000100000000000300030000000cc4acd0aca4010000000100000000050000005fbfcdf6b90c,
  0x500000101000000000389d5aee9b7e6dc0000000100050001000000000004c894e696edd2fa00000004000000020001000000018ab2abbe8bb9d60000010003000101010000000001c39292a6bec2e00000010100000500000000000003c2f7dbe4b2a8df0001000004000001000000010005f6dcc9999ad0000201000000000103000000001bb08ff0e4c8900003000000010000000300000018ef84f1d1f8be00030100000000000000030000108d9cd0fc990004000000000001000000000216caaff2a38a0101000000000104000000000004f590cc9384f5010200010000000000000300000f8ba4d2b8a1df0c]

/-- The triples `(n, b, a)` of part 4. -/
def enumC4 : List (ℕ × ℕ × ℕ) := [(6, 42, 31), (6, 48, 11), (6, 48, 13), (6, 48, 17), (6, 48, 19), (6, 48, 23), (6, 48, 25), (6, 48, 29), (6, 48, 31), (6, 48, 35), (6, 48, 37), (6, 54, 11), (6, 54, 13), (6, 54, 17), (6, 54, 19), (6, 54, 23), (6, 54, 25), (6, 54, 29), (6, 54, 31), (6, 54, 35), (6, 54, 37), (6, 54, 41), (6, 54, 43), (6, 60, 11), (6, 60, 13), (6, 60, 17), (6, 60, 19), (6, 60, 23), (6, 60, 29), (6, 60, 31), (6, 60, 37), (6, 60, 41), (6, 60, 43), (6, 60, 47), (6, 60, 49), (6, 66, 13), (6, 66, 17), (6, 66, 19), (6, 66, 23), (6, 66, 25), (6, 66, 29), (6, 66, 31), (6, 66, 35), (6, 66, 37), (6, 66, 41), (6, 66, 43), (6, 66, 47), (6, 66, 49), (6, 66, 53), (6, 72, 13), (6, 72, 17), (6, 72, 19), (6, 72, 23), (6, 72, 25), (6, 72, 29), (6, 72, 31), (6, 72, 35), (6, 72, 37), (6, 72, 41), (6, 72, 43), (6, 72, 47), (6, 72, 49), (6, 72, 53), (6, 72, 55), (6, 72, 59), (7, 2, 1), (7, 3, 1), (7, 3, 2), (7, 4, 1), (7, 4, 3), (7, 5, 1), (7, 5, 2), (7, 5, 3), (7, 5, 4), (7, 6, 1), (7, 6, 5), (7, 7, 1), (7, 7, 2), (7, 7, 3), (7, 7, 4), (7, 7, 5), (7, 7, 6), (7, 8, 3), (7, 8, 5), (7, 9, 2), (7, 9, 4), (7, 9, 5), (7, 9, 7), (7, 10, 3), (7, 10, 7), (7, 11, 2), (7, 11, 3), (7, 11, 4), (7, 11, 5), (7, 11, 6), (7, 11, 7), (7, 11, 8), (7, 11, 9), (7, 12, 5), (7, 12, 7)]

theorem certs_ok4 : checkAll enumC4 certData4 = true := by decide +kernel

/-- Certificate data, part 5. -/
def certData5 : List ℕ := [
  0x304130101050902,
  0x502030103031902,
  0x20500030303011902,
  0x40300130501010902,
  0x40303bb0001020406b0010001054003,
  0x1030309ae010002047b010100050203,
  0x1060005ec000400030d95010005010c8003,
  0x30400058601010500059d010301020ab303,
  0x102040006b70104000203f0030002020403,
  0x10500010f820202030019eb040001023f03,
  0x303010009ae040200017b050001010203,
  0x304000003bb0402010006b0050100014003,
  0x1030304cfa300010002043d9900010100051cd3010000010504f104,
  0x20500029ce80001030003028b82000200030252f5010000050133a104,
  0x501010782cb00010204000993c200030100030693fe010001050004bbf504,
  0x10500010aeaf5000300040005cbda000301020101c38f020000050003bea204,
  0x302020005cf9d010005010044a2010104000103bea20201000400018a9f04,
  0x50002001d83d0010105000021a981030001030006b6d8030101000206a0d704,
  0x10303000001fd94010401010002a4b403000301005997040001010133a104,
  0x30301000004cfa304020001003d9905000101001cd3050100000104f104,
  0x6010180aeb100000002020302869afc00000200000537b7f80001000100050bbc900100000001053ce005,
  0x1060002b1d7bf00000003020202d8d4eb00000201000401c2888000010100010443c08001000001010404808005,
  0x4010203d2d1e600000101040104ccf7b30000020101030197a6e5000100000501019c96c60100010001040ae7fb05,
  0x5010101e2c38100000102040001e5d9ed00000301000301ebb1b100010001050001d6bbf002000000010409ea9b05,
  0x104010111dedd8800000301010203efc38e00010100050009f088ce0101000101032dedb20200000002032db5a705,
  0x105000101c3f98400000300040018eeb100000301020176cddc0002000005005ff0a701000100050016d4dd05,
  0x50001010183f7d6000101040100019084fe0002000400011398ed00020101030062e4d401000005010040808005,
  0x501000102d9fee000010105000003ccbd9000020200030002b3b4dc0100010401006db8d00102000004000196c5a305,
  0x501010028d0dda20003000202001ac1f5b100040001000209bda0ee01000105000015f0b39602010000040001d6b5f505,
  0x104010100019084fe00010500000140808000030101020062e4d40100040002001398ed0101000500000183f7d605,
  0x1060000000dbef38a0004010101000db8a59400050001000136e39c0201000400000abd83ca04000000020101c2c0e305,
  0x50001010009f088ce01010401000011dedd8802010103000003efc38e0301010001012dedb20302000000022db5a705,
  0x40201000001e5d9ed00050100010001d6bbf001010500000001e2c38103000103000001ebb1b104010000000209ea9b05,
  0x502000000038fa99d02030002000001909fd7020400000001079ad203000301000002b989a20401000002003487c205,
  0x60100000002b1d7bf02020300000002d8d4eb04000102000001c2888004010001010043c08004010100000104808005,
  0x106000000000180aeb103020200000002869afc05000002000037b7f80500010001000bbc900501000000013ce005,
  0x5010106b6bef28a0000000200050002b2c4d8a80000000301000305a5fee3c40000010001050005c0baa5d90001000001040163feaed20100000000050105f4f29f06,
  0x6010001ffbaaeaf0000000400010201c3e7bdfa0000010101040001b194d8940000030000010337bdd09e000100010005003dceacec0200000000010402a6cdb906,
  0x40201002580a2e90000000501000104c689e7950000010105000004da8a89b7000003000103005388c5d80001020000040003fbe3f2ce0100000005010039c699e506,
  0x10401010013d1d8c2b60000010500000108d6b396af000003010102000cf7d9d5e20001010005000011d0f5baff0003000001020103bac7be870200000100040001f6e1fdb306,
  0x50001010010caa8dfa90001010401000014c1ede493000201010300000d8e918fdb0003020000000201f6e1fdb30100000501000008a9c4a2bd0102010000030003e7b6b1f906,
  0x50101000029f9a0e3ad000301000300001de2e29e82000400010002000fafb9e7d1000401000001010485f7e88d010001050000002881c0d0ae030001000003002787f08506,
  0x1060000000001ffbaaeaf0004010101000001b194d894000500010001003dceacec0201000400000001c3e7bdfa0301000003000037bdd09e0401000000000202a6cdb906,
  0x5000200000003b980cfd50005010001000004dcbbf7870101050000000006efd09f820300010300000004caafedf10302000001010063feaed20400010100000105f4f29f06,
  0x1060001e7a5c98af5000000000003020201fff8e3ecd900000000020100040197eac1ac80000000010100010449cee5c080000001000001010408cf948080000100000001000547e0808001000000000001050280808007,
  0x303017cc9e6bfac000000000101040102ad8fdc91d3000000000103000301aae0d099ad00000001000103026dbfe7b88000000100010001040ee49195800001000000010104018df4beb0010000000001000504c7edf207,
  0x101050002b9f3d58a87000000000103010201e3b182f4e7000000010003000376c3cce2de00000001010101032494a0aac2000001000101000417e690e4c000010000010001040284ad9980010000000001010409c4da8007,
  0x5010105f0a0e2c2a0000000000200050001a9e2bf85ee000000000301000305db94c48edc000000010001050005dd9f8889b800000100000006007fad929fa400010000000201030ca4f5b4b601000000000004024185e8d507,
  0x10401010b8ce9afc9c7000000000301010202dfeffcdae4000000010100050006e8cfb1a49a000000020100010304f1c885f3000001010001010301d5998bc0800001000001000302178696808001000000010100040188d8808007,
  0x6010010fbeee082a700000000040001020cf992b081b900000001010104000acaa3f7f7fc000000030000010304cf84c2beac000001000100050005a5cceddea0000200000000010428e4849dfc0100000000010401049ac9ca9a07,
  0x10600001fd0e1e2c6f3000000000401010119beb7a8a8b6000000020100040019a6a5c0fbf7000000030100000306c196e7a5fe000002000001030109d491aadb98000100010000050002ebc8eeb8f802000000000001040bbabfdbce07,
  0x500010103d4bfcd8ad2000000010104010002aca287c38300000001030003000381e4a3eda100000003000102010381bcdeeff400000100000501000497ff808080000100000005000156d08080800200000000010004038080808007,
  0x50100013edf8796a39d00000001010500004a95f3c4bd9a000000040000010249afaab7d9000001020000040040f5b2e6f281000200000001030104fdd793aae100020100000000046bc9949dff020000000100000438c7cc92d507,
  0x501010007b3a1c789e6000000040000020103d987acf6c3000001010004010006dec7ada982000001010103000153c7c7c7a200010000010401005ff1d8bac8000201000000010330a4f9a2bc01000001000301010ffbc0cf8007,
  0x10500000105dd9fede780000000030101020006bce6fccdcb0000010004000200039fe8e3a7e8000001010005000005b7c0c694ed000002010001030001d5efbf8dda000100000105000002cb9ee5ccd201000100010004001dfc8ab4d307,
  0x10500010003e28a98f5d9000000030102010046f2cff6ef0000000401000101028185c3cad4000002000005000002aeb6f69cf6000002010002020076d295f38a000100010103010001c1cca3808001000000010500001389b4808007,
  0x40101010007c6d78efcd9000000050001000104efbe94d6b000000100050100000af9abaecabb0000020100040000079897d7f4bf000003010000030003b5b4f7b2ed000100010301010009fda0e4a88001000100000500000194d6b8b08007,
  0x50001010003c6c2fa9ff4000001010401000007daf2e2b3ff000003010001020001a5caf7d889000101010004000060daccd18a000101010102010002c5fdb4bafa00030100000000033bebddca8001000100010400004c8da4a8ea07,
  0x501000100248ab9ddbbae00000202000300002f8f9597bfc600000400000102000cc6f78acdee000004010000000204988acf92af000100000600000029b2da978ee300030001000002010184f588a5df01010000010400000789c780808007,
  0x5010100000d8dced4cee6000003000202000003cc93e88ba3000004000100020006e88c908080000004000101000101ef9a808080000100010500000008fedcb9f8c4000201000004000002cf85c1b197010100010004000002bea9aeb5be07,
  0x1050000010002ad8dccf58200000301010200000292b4b4abb500010004000200001cdbf5a48a00010005000000012686d294b5000101000500000001d4bce5cdfd0002010001030000018aa5f0ffc2010000010500000059e1ccaf8007,
  0x6010000000288f4fa87f0000004010001010001efbe92e7c000010101040000000380bfc7dcf800010300000300005fcdaa9ef401000200020200002abbd4f0010200000004000058d8fdd2a9030100000000000309a5b3c38007,
  0x5000002000007afc9a2b4f6000100050100000009dcb2dde38100010201030000001cf7ecb9a9000103010100010003e3fed7c08000010400010000012fd7c28080000300000301000001da9af7e69401010001040000000582cde8fad207,
  0x5000101000005b7c0c694ed000005010000010002cb9ee5ccd20002000400010000039fe8e3a7e8000201010300000006bce6fccdcb000301000102000001d5efbf8dda00040001000100011dfc8ab4d3010000050100000005dd9fede78007,
  0x5010001000014cdc7dce897000101050000000023d7b589b1cd00020200030000001e93b982e5a0010300000003000006e8ee90ec83020001000400000006e2d1b2e5fc020101010000020003fcd4aae3a004000000010000022a98d8bec007,
  0x501010000001cfcb48afeda000105000000010004f98c948a8e00040000020100001e81b1f5cfa701000105000000001df1efe499ee010005000000000133fcccf282020100000400000001b9ac95b8d6040000000001020019eee980d907,
  0x10401010000000382f287c38300010500000100000497ff808080000300030100000001d4c4a3eda1000401000100010056d0808080010100050000000004ab8fcd8ad201020100030000000381bcdeeff40400010000000002038080808007,
  0x6010000000007ee89e3f298000401000101000005aedefba4b800040101000001001ba3d9a796000500010000000106aedca4d6010101040000000009ba9ab3e6c7010300000300000004fbefd0fbe8030101000000020024edcdad9b07,
  0x106000000000010fbeee082a700040101010000000acaa3f7f7fc000500010001000005a5cceddea00104010000000001049ac9ca9a02010004000000000cf992b081b9030100000300000004cf84c2beac040100000000020028e4849dfc07,
  0x50001010000000782bc80dc9a01010401000000000bb4d4feddc7020101030000000002ab8e85eae40203000100000100178696808002030100000000010188d88080030100010200000062c7e689f304000100000200006accc5e08007,
  0x500020000000002ab95c0e8b8000501000100000005dd9f8889b8010105000000000005f3ebbbe097030001030000000004d696e98e9b03010101000100007fad929fa404000101000001000ca4f5b4b604010001000000014185e8d507,
  0x501010000000004b1bbace1d8010204000000000005bcfd899ed3030100030000000002b9f0e3ab80040001000200000001a3ce93b2f804010000010100003bbfa9fba00401000100000100058af0fec0040101000000000117ebe18007,
  0x103030000000000018ffda982c9010401010000000077f595e19a030101020000000022aacad1b3030201000001000007b288cac0040001010100000036dff3dc80040101000000010046fa9f98040200000000000102a3f6f907,
  0x601000000000001e7a5c98af5020203000000000001fff8e3ecd904000102000000000197eac1ac80040100010100000049cee5c080040101000001000008cf948080050001000000010047e0808005010000000000010280808007,
  0x303017ee4d5c7d2ba00000000000101040102ccb48cd1a69500000000000103000301c0cc92fee3eb0000000001000103020182b9b782868c00000001000100010413fdf3ddba9000000100000001010401f4f3f79fb80001000000000100050db38ae6f00100000000000001052986dd8208,
  0x501016db584ec8fe200000000000201030135d39a8cfe9100000000000301000359d8c3d9dbca0000000001000105007aa7f7b88bc600000001000100030217f5cdb3ae8800000100000002010302f6998db1dc0001000000000102031a9198f4b8010000000000010104669bb6e108,
  0x10500010183a19bd2fc9a00000000000300040008bfb9fc8aa50000000000030102016b96e4d2d1fd000000000200010301639395f8f087000000010001000500308eb7c39d8800000100000001050007a2f6c49adc00010000010001000450b4e1dfb80100000000000201030384fca0a108,
  0x106000005d99ec1cdc9e30000000000040101010ce5d8eca4de980000000002010004000cd1809ca3e28100000000030001010201d19dfab4e2ee00000001000005000109aa98c69ddcf000000100010000050001dab9c895868800010000000100050016eae7f0ae900100000000020001030185d592828e08,
  0x501000103fef789a4e79f00000000010105000004f6ac8e99c0d90000000004000001020ddefb8c8ff700000001010102010101f0b3f8faa2b800000001020000040003bdf986d1f6f00000010001010004000195cbb9acc0cc00010000000200040012d0d4fcd1980100000001000005000181f7c09d8508,
  0x10401010004bfa8a6e1959b00000000010500000109eb8acaa7e88100000000030101020009aed4889ffcbe0000000101000500000bc9fa95a6f5f600000002000102020002c2c3e8c681b900000101000101030005dee4d8f3ac8800020000010000010335f3cf95e78802000000000001010303baf0e0fbe708,
  0x50001010002c1da96c6d8a900000000050100000101ccd4b3b8ea8500000002010103000002f4d1aac58dc500000003010001020002f88a8fb8eaf30000010000050100000590ee90eed3cc00010000000500010003ddf481affa0002000000000401003fc4bb9ab38f0100000100000500000bb2d3f88ec508,
  0x5010100006392c3c5c6a000000001050000000118e9a291de810000000400010002004fa282edc9b00000010001050000006e90e2eca3d800000201000004000027dcddc0839600000300010000030044e8c5d8c80001000200000400002c86eeffb3b801000001010004000004b8b7c9dfc108,
  0x60100000023bda99ccef1bd0000000400010200001bd98baad7f7d300000101010400000017d6e7e8dfc6000001040000000101048c90a2e79da40000030000010300000aa1da81d1d3e40000030100000102000d99edebe7a79e00010001000500000013eed3c0a89fe001000000010500000002a7f4e0a7ffa408,
  0x50000020000048697e6a8e9d0000000050001000100018be6f9ffc3b80000010005010000000598caa8cee7af0000040000000201000191ccc6c6e8d600010100010400000003f9f5daabe6f30100010000050000001df3fac5db02010000000100030016cab3b1c3ae0201010000000000030dd9c6ea92f708,
  0x501000100000282b1d9f1e0b58e00000101050000000002c9b582dcd8a9d70000030101010001006df2fde3e4d9f90000040000010200000184f9beffe89a8b00020001000400000001d7dcf6adaacee701000101000400000030cfabe982feb602010001000000030003d1a49998b9c50301000000000000030487cae6b4a6b508,
  0x10500000100000fb8bff7d8d1d40000020400000001000a81efdfdfd9b80000040001010100002190becbeaf7e60001000400020000002a9dab89999bf80001010005000000002d91dfeaec8cc00100000500000000016fd6e9e5f4f102000001000400000006c4efaff3f1ef03000000000103000049b586fdcdf608,
  0x50001010000002b878fd3dadec700010006000000000022aaf9eddfa5e300020101030000000008e6b0ebaec2c50004000001010100000fcab5f1a6e5a800040000020000010002a4cf899af8d000040001010000000112e49afc8de60200000104000000000ebef3ebb7bcc802010001000300000057b3a2a290eb08,
  0x5010100000000208fd2f7b1a2f000010500000001000004c2db9ce3acd800040000020100000022dff8d5ba8da00100010500000000001ffaaac7b4baa00100050000000001007ed7dbb5f4f00201000004000000005e8aa5ba8c8704000000000102000001db9fdaff9ef004010000000000000203b9e38dc99108,
  0x60100000000000cae9de1be9eb300040001020000000008d19aa2e095d100050000010001000001dab9c895868800050001000000010016eae7f0ae900101010400000000000c90f5ada2bd9701030100000200000004d4c9b8c5edb102010100030000000004a6b7a0e1eb8e0302000000010000010185d592828e08,
  0x106000000000000038e968dd8f9de00040101010000000001c6fdda92f4a40005000100010000000190aba6c9d79800050100000001000015e8e3ccd094010500000000000001098ef4e0e302010004000000000002b4bf9bc1a88d0301000003000000000184cceda2c3ba03010101000000010001f19ea59ea808,
  0x5010001000000007aa7f7b88bc600060000000100000017f5cdb3ae880101050000000000006e92cb8fbc990103010200000000001ebb92fcfcc0030001030000000000709384c6b0e40302010000000001001a9198f4b804000101000001000002f6998db1dc040101000000000001669bb6e108,
  0x1030300000000000002b5b8c89d8cd5010401010000000000028e93fdc9e1c60301010200000000004898afb0ee9f03020100000100000013fdf3ddba900400010101000000000182b9b782868c04010100000001000001f4f3f79fb80402000000000001000db38ae6f00501000000000000012986dd8208,
  0x40201789dd3939086800000000000000101050001ce8daff1b5b3d2000000000000020200035ff1b6d783c3c7000000000002000100043bf3e4e0e4ddb00000000001000101000416cdc0cb958dc00000000100000100010402ebfb9f98b280000001000000000101041db794e7b4800001000000000001000501b1d990fa800100000000000000010503dceb948009,
  0x501010292baefccf1ca91000000000000020103011be4a6b0d5af890000000000000301000302bcc597b696b5fa0000000000010001050002befa8ff19ce0800000000001000000060043bca5e997a8800000000100000000050109c1f89aa98480000001000000000102036eb5b99f93800001000000000001010405ebb8c8b5a80100000000000000020411c8dbb4d609,
  0x105000102fac6a6fecfb88b0000000000000301020101ded0d4eae99ac9000000000002000005000195b7d1d6fce1a0000000000002010002026aa29c9adfbaa0000000000100010005000184fbc3b0f2c1c000000001000001020003178686c7cfcac00000010000000100030202c8dc94b58fa00001000000000000050115aef9d2e884010000000000010001044f819ec6da09,
  0x50001011185dfb2ddd4f0a4000000000002000302000cedaffbb2edf1a30000000000030100010205b2ad97f2aba7b7000000000100000501000ebbaae4b7edd8eb0000000001010100040001c8f58fba92a7950000000100010001040003d1e18ec08080800000010000000003030043f9f8808080800001000000000100050005e4a080808080010000000000000105001c808080808009,
  0x501000102c6cce8bae0a5b80000000000020004010002d5e49eb3c6d0f5000000000002020003000db4a5fac794a3000000000004000001022eb0edeb8ec9a40000000002000002030001b690f5bbc9b3e00000000100010100040059dfc3948a99c0000001000000020004000e9bb9f8b9a2a00001000000000003030001a88d80d8e2bc0100000000000100050006f3c69b92a209,
  0x60001001daaa2acbde7c2cf0000000000040001010114edc3e1ece5e8dd000000000101000500001dd28499aeb3fcc500000000010201000300029ac4c5fbca91a60000000003000001020106cc8b88b9ca97a30000000200000100040007bce3809eefdf800000010000010003020002e290d9838ee1c000010000010000010400269db893fcc0ac0100000000010001040001eae4d18facbb09,
  0x60100000895f5e8c6e0b7880000000000040100010102de9bf29ca5df9b000000000101010400005888d3bafe94b50000000001030000030006a488dbd3b5e8f50000000003000002010103b1f9ab89dbf0f20000000100010005000005a8a6f09db18080000001000001000401000187cdf599ec8080000100000000030101010fe2aeafd480800100000000000005010068a7b8b0808009,
  0x10600000016919edefec5c1ed00000000000401010100038094b49bfa98b2000000000005000100010abbf19db2b0f6e2000000000201000400001086f49ff693f3e3000000000301000003000694c998818cf2be00000002010000010300088aaac1b1aeae800000010100000004010004e9e5a1ebd698800001000000010005000052eff6beeae4800100000000000105000004f8b9dae8988009]

/-- The triples `(n, b, a)` of part 5. -/
def enumC5 : List (ℕ × ℕ × ℕ) := [(7, 14, 3), (7, 14, 5), (7, 14, 9), (7, 14, 11), (7, 21, 4), (7, 21, 5), (7, 21, 8), (7, 21, 10), (7, 21, 11), (7, 21, 13), (7, 21, 16), (7, 21, 17), (7, 28, 5), (7, 28, 9), (7, 28, 11), (7, 28, 13), (7, 28, 15), (7, 28, 17), (7, 28, 19), (7, 28, 23), (7, 35, 6), (7, 35, 8), (7, 35, 9), (7, 35, 11), (7, 35, 12), (7, 35, 13), (7, 35, 16), (7, 35, 17), (7, 35, 18), (7, 35, 19), (7, 35, 22), (7, 35, 23), (7, 35, 24), (7, 35, 26), (7, 35, 27), (7, 35, 29), (7, 42, 11), (7, 42, 13), (7, 42, 17), (7, 42, 19), (7, 42, 23), (7, 42, 25), (7, 42, 29), (7, 42, 31), (7, 49, 8), (7, 49, 9), (7, 49, 10), (7, 49, 11), (7, 49, 12), (7, 49, 13), (7, 49, 15), (7, 49, 16), (7, 49, 17), (7, 49, 18), (7, 49, 19), (7, 49, 20), (7, 49, 22), (7, 49, 23), (7, 49, 24), (7, 49, 25), (7, 49, 26), (7, 49, 27), (7, 49, 29), (7, 49, 30), (7, 49, 31), (7, 49, 32), (7, 49, 33), (7, 49, 34), (7, 49, 36), (7, 49, 37), (7, 49, 38), (7, 49, 39), (7, 49, 40), (7, 49, 41), (7, 56, 9), (7, 56, 11), (7, 56, 13), (7, 56, 15), (7, 56, 17), (7, 56, 19), (7, 56, 23), (7, 56, 25), (7, 56, 27), (7, 56, 29), (7, 56, 31), (7, 56, 33), (7, 56, 37), (7, 56, 39), (7, 56, 41), (7, 56, 43), (7, 56, 45), (7, 56, 47), (7, 63, 10), (7, 63, 11), (7, 63, 13), (7, 63, 16), (7, 63, 17), (7, 63, 19), (7, 63, 20), (7, 63, 22)]

theorem certs_ok5 : checkAll enumC5 certData5 = true := by decide +kernel

/-- Certificate data, part 6. -/
def certData6 : List ℕ := [
  0x50100000102aecfd88ec898ae0000000001040000020025ad84e7c48080800000000002010103000025bfe6e69ee9a0910000000100000501000025d284ab9be989b40000000200000104000002bab081a28198bd0000000301000000000336a0e09da3bcc60000030000000001000303cce4b6f399e6800001000001000005000001c6dba7d6bdc398010000000001000500000cd984a881e68909,
  0x5010100000385f5bdf98a9be30000000001050000000102f7d49bb293f880000000000400000201000ac2c3bcdbb1808f000000010001050000000bf8a89bde919ecd0000000100040001010006ede1d8808f93f10000000201000004000047f9a984add1840000020000000104000002e8db88c99dcfd00001000000000501000076d3ecf6b3ecdc0100000100000005000008d69cc684c4fa09,
  0x60001000031a4a8cd93f484930000000004010000020017bb9c83b294f6ee0000000005000000010106a0f4e9f9d4e4a6000000010100050000003cbcc0f881badea000000003010000000300049690b6ee9ec1a0000001010100000400001fd294ae9ca784800001000002000004000001b6d7b081fca3c50003000000000001000301b0a3bee7d0e4e90100000100000104000037c6efbddba48009,
  0x10600000000078e9387f38efbfd000000000501000000013f85a6c892f5920000000104000001010004b5fa90b9e79cba0000000201000400000053eb99d684d88100000003010000030000019f9dd881c8f7a00000000400000002010045f4a4a18d9fc60000010101000301000007d3acdff7c0f5e00001000100000500000001d0eabdef90d5ac0300000000000001000306ccb6d4c2e0fa09,
  0x501000100006881e0d2e78bca920000000101050000000023a281f6dab7e4f9000000030101000200000cda8dbcaaccf9ad000000040001000101003aed80808080808000000101010103000000019dcfc2f2e3c1af80000003000001000300000ca8dbd6c3f99b80000100000005010000002acfebe7d5bbf3800100000000050001000002e9a1b0f7eef2940102000100000000000302a080808080808009,
  0x104010001000042fec6d38780c0000000030002020000000180fdbea1a4dfb1000000050000000100010681bfa2a5e29f000001000105000000006b82abe8d6a6c60000010004000101000063b4e7afb6979a000001010300010001001dd3efc2e0dc990001000200000400000023c782daed99f9000101010100010101001a98fda592e687010101000000000400000880808080808009,
  0x60100000000119dd3c98dfcdca7000000040001020000000be1ced1ccfbebc10000000500000100010003db93ede8acbc8e0000020101010101000016fa869fe6c2e1a0000003000101010001000197abcbe585c3f6000003010001010000013bafebf8d8e8ca0001000100050000000009b6b9dab3c58b980002000100000400000002dec8e1eecc94b40100000001050000000001f8bfdfd191c88009,
  0x500010100000008deae9da2aae1a0000002010103000000000196b5e0929687900000030100010200000001abe7d1cc85f8b0000003010101000001006ed785bef1f6800000040000010101000004f68395b4e18c8000010000050100000000098ec9adebbceebc01000000040200000000419eef89928ab9010100000005000000000189a4e0dbdfb2ea0101020100000000000204a988d5eef68009,
  0x50100010000000192ef81fbcedcd9ce0000010105000000000001a2a2c597f4beee8e0000040000010200000022f7c480f49aa1b100000400010001010000558dbe9cbd9897f00000040001010000010002de9abc9c8d95bc000004010001000000010182fcaf87f7ddff000200010004000000000181a992befcbbc6eb010001010004000000002186f9c6d5c4f3820301000000000000030003e0bfae86aba0aa09,
  0x1050000010000002f88c5b488befeb90000040001010100000072979eb9fed9a1d30001000400020000000001a180b78fafd9e1f2000101000500000000000185cefaa19891acaf0100000500000000010006a7d69d9186bab00100020101010001000019eefa889df880c2020101000000010200000981e9a9c894f1df0300000000010300000002cfc0b7dd829a870300010100000000000219e6beb8c5dbe909,
  0x601000000000050e685f689f7fab6000004010001010000006ee2c1ebf38cd6800000050000010001000001bbddefc1acb984000005010000000000011a89f7d897d48000010101040000000000799bfebfd38fffdc000400000100000200000bb3fae894af9cfa0102000000040000000030f6ceacc395abef0301000000000003000032fc9f92f9f5d80301000000010000020001dad991c9af8f8009,
  0x10600000000000001a4b3b7df939693d6000005000100010000006386e6da8396fff800010401000000000100028ce688fce4fffc000105000000000000010fa086d5f08080000300000301000000007fe5c0b3fbb9c0fc0004010000000002000009f4f4bfc48e80800100020004000000000033e7a0d5e6bfaea50101020000030000000040a9e0a2a9d09aac040000000000020001001aa691dabf808409,
  0x50001010000000032e1c9f9d8e1bee000010006000000000000309982aee5bd8e830003010001020000000008fbffd9b0edc3a50004000100000200000009fedcad93f5b2a00004010000000101000004c4e387e1a2b9c0000401000001000001003ed99ed3faa1ec00040100010000000001038186a8f09aeb0101010004000000000022af87de9bca8ce40201000100030000000005a9d1a0b0b2f9ce09,
  0x50101000000000014a984bdea8ea8920003000202000000000002bee880aaa9f8990004000100020000000009faf6b6a181eaa00004000101000100000004f49cd68cc7b2c00004000200000001000063c095cb90efe0000401010000000001000998db84edb1a40005000100000000000130a8ebbdffee010001050000000000000b8b989bf7f2ce820201000004000000000005f696e0bfbddcff09,
  0x105000001000000000ebbaae4b7edd8eb000203000200000000000cedaffbb2edf1a30003030000000001000043f9f8808080800004000101010000000001c8f58fba92a7950004010001000100000003d1e18ec08080800005000100000000010005e4a080808080000501000000000000011c8080808080010100050000000000001185dfb2ddd4f0a40201000103000000000005b2ad97f2aba7b709,
  0x1060000000000000017acd1caada68fd7000401010100000000000a8aeaceb5a085ec0005000100010000000009acd7deb886cdc00005010000000100000001cfb6bb84cc9ec001040100000000010000178ebdb7de89a00105000000000000010001c0a6c6e9a8a4020100040000000000001298c3d08ed6fc950301000003000000000008cff7cec39ecddc0302010000000000000105c78b92fcaa09,
  0x5010001000000000002befa8ff19ce0800006000000010000000043bca5e997a880010105000000000000000292d6bcfb99aef1010301020000000000001b91bea5de80e90105000000000100000009c1f89aa98480020400000000000100006eb5b99f93800300010300000000000002bcfcb292e5ffba0401010000000000010005ebb8c8b5a80402000000000000000111c8dbb4d609,
  0x102040000000000000001dfa4ab8beadfe90104000200000000000001c2e6cfcbeaecf2030002020000000000000491bf83f3b0be0302000100010000000016cdc0cb958dc0040001000200000000003bf3e4e0e4ddb00401000100000100000002ebfb9f98b280040101000000000100001db794e7b4800500010000000000010001b1d990fa800501000000000000000103dceb948009,
  0x5010101a5828eb6efe69bf200000000000000010204004d898ad6dbabace6000000000000000301000301d1d5d99c9ef892c6000000000000010001050001e6afe5d4d799fdc2000000000002000000010419e2d19db7a89cae00000000010000000005010880fff788c1a58200000001000000000102036d99dbdbdbc8b8000001000000000001010407d1a0dbeb81c5000100000000000001000528becad6b29a010000000000000000010560cff6e1d90a,
  0x105000103e9de95989af3a097000000000000000301020102e4c8f9acd7b3e2f5000000000000020000050002b6b0d093e3fcb490000000000000020100020221c581f6e8d9c0e8000000000001000101030101c881a4b7e49f8ad800000000010001010000042681def0b3cec284000000010000010001000404fa90edcdcfecb00000010000000000010302369e89aff3bafa000100000000000100010402dfebc286ece401000000000000010000050883908d97920a,
  0x50100013994d8ddcdbaec98fa0000000000000101050000108cfdf6cc9f97b8dd000000000000030001030030e4a891e9c68cd78b000000000001010004000114fd87e691ade7bf86000000000002000100040018e888c5c8d896a2a9000000000100000005010012efcd8be1b7e190a4000000010000000005000103bae09f91c1e298b000000200000000000001041ad0adac899ec195000100000000000201000303e5f1c4a2cbdda401000000000000000203010fcaf1c3a49ee20a,
  0x60001003ead9d8584faa7bda4000000000000040001010133b0c5c9c691d2dfba000000000001010005000016d6a6f4dc88efb6b2000000000002010001030025dbf3baf5dabbc8a000000000000300010001020890bdafaac8c1aeee00000000010000010500002683ead0c1cd8ce9b20000000100000100030200088ca585a7b687dff800000100000000000501000190e3a5b9a2ecb09d00010000000000000500010bfe9796ef8af6aa01000000000000000401013993f888d3fdf10a,
  0x5000101003fa0af839cb19299e4000000000003000102010039daa4aab29dadb8e80000000000040001000002029af1bdc8eca380b900000000010000050100003d9afdccd1edeaf8ac000000000200000104000003ca9fcba0c4a2b4e3000000000300000001030002bcbba7dcafd0c5b2000000030000000001000307889e848191dec5a0000001000001000005000003f1e7d7a88eefcfd400020000000001000001031b88d4f7f2a4aa94020000000000000001010301a9c68885eedbb20a,
  0x60100000002eda4fee1ea91e3c3c8000000000004010001010003efb3c8eeda8acab0ca000000000101010400000003ffe9e5c6edc4c180d000000000040000000101012bef90ffd6c9dfb194000000010200000004000002abb8bafbacc8a28a9b000000030000000100030020b5cad3d6b4ef8fd2000000030100000000000312c38ef5dde991a8ce00000100000001050000006e9daabec2ebc1aeda00010001000000010400000fb0df9dc7eba3f4d402000001000000000000043de7cda485a6e4a10a,
  0x10600000000548eeeeab2bc8780f900000000000500010001002d88ebebad8e9ce2e4000000000301000003000009a18eb683cde5a1ba000000000400000002010017b8f1dae7e1908fc4000000000401000000000204d8bfebeaa0f3eb90000000010101000301000066fa8b8b8794f8a1e000000100010000050000000bb9b792c682ab868a000002000001000004000005e4a481e1b7dec0d9000101000000010004000004a5b4f89787d2b0a8020000000000010101000213b78cfef8cfc7aa0a,
  0x101050000000006b4a2c9b3f5daa1b5000000000104010000010005b1d2aeb29ed898dc000000000105000000000156e1bdfef1d8dca6000000000400000102000005cc8b86f39e9cd4f700000001000400000200000485a89fe1d8d4e190000000020001000400000005da86bfe0b2e7b7b2000001000000050100000003f0bccdfcbe82f2db00000100010100040000007ddac7baa0b5f9d300010001000000050000006df3a8cefab7fedc010000000100000500000008de95f7eaf0e1860a,
  0x104010100000007dddea3abb2a0bcfc00000000010500000100001fd79ce6b7a1c384e1000000000400010101000005fdf8bda4c1dce49600000000050000000101000cbfecd496b5ccc8da000000000500000100000101b3b0a0daf9ccbbad00000002000004010000001bcdb5a7c7fca6bd8e000001000001050000000009fbfdc696bd86edc700000101010000040000000fa487e9838bddffc200010001000002030000000580caeeeac5e3c79a01000000000005010000003991878f84ebbcd50a,
  0x50001010000007ba0bab18cf2baabb200000001000600000000006891c7a89aa0d681b1000000040000010101000034c4909adbecc2edf1000000040000020000010010d7a49c8de8cbedac000001010300010000000101beb8ed87bae69fc6000002000001040000000027c3bfd0b3d4a18be2000003000000010300000012ac99c6eab1add09d00000301000000000300000ac5e48f8c8284b88f000200000000040100000014eab58ca5aed4f996010000010000050000000004d5f697d9ead49b960a,
  0x501010000000038e4dbba99f68184b1000000010500000001000021cdb69889e7e1ebed00000004000100020000002daf94d3b98a90ffc200000004000101000100000be1ccdacab4b0dceb00000005000000010001000881defb8bcc8ac9b0000000050000010000000151c4a289909cb4b800000100010500000000004eb282adf58ceee0da000002010000040000000032deddd1f3b9eb9dbf00020001000002020000001992ab83958f9bc8d802000000000004010000000394f1cbfae7f3aedc0a,
  0x601000000000008b4bdb1dfa6deeedd000000040100010100000008a0a1898caf95eac8000000050000010001000031c3bedca78fa69400000005000100000001003fb2b5a099bfd4ac000000050100000000000104bdf993b9aff2f6000003000001030000000006c5ddf180f5a6e0ee000004000001000002000001b0f2beffffe0d2cd000100010005000000000006c1dcc7d78f9dbcb000030000000100030000003bb1efdd99bb97d40100000300000102000000018f87e0e785f281e60a,
  0x1060000000000003caffcf8d0cdcf99b70000000500010001000000279bc583d2e5e790fa00000105000000000000010dc49094e28de5bd000002010004000000000031fab5aced9099ebe1000002030000010001000006beb1ceeee587b6a700000400000002010000000c83efd7d8f29ccb9e000201000001030000000021f4b7ccc4afaee2ce020000010000040000000002b6c499bbe0a3a897020101000000000003000001ee85aaf2dbd690a603000001000001000002006be0eddea098bfe10a,
  0x105000001000000004ba0bf86eae6ab94fb00000301010200000000003ca49eefe880f78a97000004000101010000000011b08faed4aea8a89d0001040001000000000001039eb9beaae3fbec00020000040100000000004a85dbc4cab6f0a38d010000010500000000000006accfcff59b9ab0010101000004000000000003e58589ecfbe6d1be0101030000000001000100429596ddfaf59ff8010201010000000002000002b09be791b3e0d49e02000101010000020000000cd8d791a8b8b2d9d40a,
  0x5000101000000000028add3d0a3a98af585000100060000000000000028cacdc7e9c9f7fda0000203000100000100000004f7f18fdcdca3f8f800030001020100000000003dfadcf6cad9b0c100040001000002000000000bcc8c9bd5c7f2dec9000400010100000001000058a3c8e4bdead5cd000401000100000000010007a7bcfb9b93938a000401010000000000000122ecf885a3cce101010100040000000000001e8297bb88baa3f28f01020100000300000000000ba4aeaff8a6ff96920a,
  0x5010100000000000002df81b1ceb5ebdfe300010401000100000000000ec4ccd3c793b1a6b4000300020200000000000005aba5d2defcde98b9000400010100010000000003f1aa9ce38f9fa59e00040002000000010000005b93e8a5bebdd0a800050000010000000100000afbb8a8de948be300050001000000000001006484c6c3addade010001050000000000000006e6cdb9d8b4cdf0fc0104000100000000000001039adb91cefee70201000004000000000000058c80bfa6cbafddc60a,
  0x106000000000000000010a881bfade48bfaac000401010100000000000006d0ddaae1d5a0c2f2000500010001000000000006ede0988de5e4c8b4000501000000010000000001ab87eaf9e8a1a992010500000000000001000001f487aa97c7c9a502010004000000000000000cdca1efccc99df8bc030100000300000000000006ada6a4f6f68f8e90040100000001000100000016a5cbed9da7a7d804010001000000000001000cafa3e99ee9c20401010000000000000001248e88bba8910a,
  0x40201000000000000004d898ad6dbabace6000501000100000000000001e6afe5d4d799fdc2010105000000000000000001a5828eb6efe69bf201050000000001000000000880fff788c1a582030001030000000000000001d1d5d99c9ef892c603020100000000010000006d99dbdbdbc8b8040100000002000000000019e2d19db7a89cae040101000000000001000007d1a0dbeb81c5050001000000000000010028becad6b29a050100000000000000000160cff6e1d90a,
  0x6000105c79cb1bb94d7ebccd000000000000000000300030104edc28cc49fbbeb9fc500000000000000010100050002a6a3b593a5dbcce8e200000000000000020100010302beb2e8cac8e4a19fcf00000000000001000001050001f0d2d7beeab9b1a0800000000000010000010101032cb6d38dc8e98f808000000000010000000000050105edf1d1fbc4dc8080000000010000000000010203459c9ba188a8808000000100000000000001010404a19f9bd1a080800001000000000000000100051490f4838080800100000000000000000001052b9fec8080800b,
  0x10500010be394bee8abbcb695dd00000000000000000301020108bbcb98d4b2bbdbf3db00000000000000020000050007bbcfd59bb4e7f4f0ee00000000000000020100020276e784ccd4f88b8f92000000000000010001010301058eaebdb080808080800000000000010001010000040184f5b8bbe08080808000000000010000010001000413a4bbf48cc080808000000001000000000001030201fada8ae5a2c0808000000100000000000100010410fce28898ab808000010000000000000001010458a2b190fec68001000000000000000001000501d0d1a2d6d9d40b,
  0x40101010d95fc98eaa6dfc8f28f00000000000000010005010007d6c180b9eaf2f88cf70000000000000003000101020392ad9e9ef683f0aff20000000000000100000500011ea980dff8abe3f7dd00000000000001010001040008b3eefaf193c0d0aca3000000000001000000040101028bd08fbaec9484b280000000000200000000000104178ff5c4f7f8f185c000000001000000000100040105cc8dfe8cc0abeee000000100000000010001000439e08c9df4d68f9000010000000000000101000402e5d7a6cdf3d3a801000000000000000100010407eefbb481cdbc0b,
  0x500010122b0f2a4d29f9dc085ed0000000000000001030003000895d79cdce1d9a5e0f50000000000000003000102011fd59df697948e98dfd90000000000000100000501002486a2fda195f2a1c9af000000000001000000040200088d80a3a1ccc0a1c9af00000000000101000000050001eaf5a7b3cadfdeb6d100000000010000000003030001eea69be3cc808080800000000100000000010005001fa0a59be08080808000000100000000000001050002dde0a4808080808000010000000000000001040112acc08080808080010000000000000000010302388080808080800b,
  0x50100011ce6bb9292a185da90e10000000000000002020003002dcfaeeed0b3dee3d0fe00000000000000040000010214fbd2f2f2eea6efc2d100000000000001000104010042dbcef589bbad9ba6cb0000000000010000000501000de7d5b8f8c48c8f9d9600000000000201000000000402fbdefdab98e7c699b500000000010000000200040003ffb9a1a6ea8df1e48000000001000000010000050048ba9fb19dfbc8d3c000000100000000000100050006ebf3a8f5a8e9dab000010000000000000100040131d199e4c1f1c1a401000000000000000001040101a3d2a882bcc3850b,
  0x501010008e6a3aceca4e0deb1b600000000000000040000020104c9def9c6da82f79cbb00000000000001010004010008c6abbbb3d5c4b8c28a0000000000000101010300010197f2c79bbb87f2cbaa0000000000000300000003015f8aa1d1b2f3d39b8400000000000200000002020101e9edc991debfcaabc000000000020000000100010332fb86f9d1d2fc87800000000100000000030001020fc68ae698f4b79a8000000100000001000100010301cab0e9eceba694800001000000000001000102020cacd18bb4fcd8800100000000000000000203012bebafba89b0800b,
  0x10401010031bcaac2ea8ba8fce000000000000000010500000102cada9ef492e29cbfde0000000000000003010102006ae780da99ebe1c0dd00000000000001010005000002ee90b79f8e8ba3f7b70000000000000300000102010db38ef2dbaaebfbd000000000000101010000040001c5fdcae49ea8c1a1c00000000001000001010103002ea9d79698dfeebde000000001000000010100040006e197e4c4f297dcd40000010100000000000002036a8785dbecfbbcf400010000000001000100010306f9b39186d9a6ee0100000000000100010000041abea88481baab0b,
  0x60100000db4db86f1b18b93acc500000000000000040001020012fc94ffb1b88998cf0000000000000004010001010db6a4aab6edc099f9f600000000000001010104000001a3dcbe9fb8b6d9edec0000000000000300000103000ac8deea87ef82b890dc0000000000010001000500000bc9b197b9bec795808000000000020000000001040001b9d1c6d0acb4c680800000000100000000010401004191b1bdf092b8808000000100000000000005010007cf9181ffd2a0808000010000000000010001040044b78baf918080800100000000000001000005000297b2e4dc8080800b,
  0x5000101007683f5cacf86dcfc9bb4000000000000020003020000109ae9e7e6f8fe91bba40000000000000301000102004fad91abf79f839a97f80000000000000400010000021dc5f0f18986e1e8a59800000000000100000501000001828af2fc8ec2bdb8bda90000000001000000050001000bd1e0bceed3cdf985e90000000001010000000500002893d2b8abf7d1e2f7d70000000100000100000500000b83e8bcc28dd3e5aef0000002000000000100000103649cadb0f8a3c9fb8400020000000000000100000408c4e4c9ede6cb85a20200000000000000000001042aa88cabd7e683ef0b,
  0x5010001005298b5f6a4aea8878fa50000000000000101050000002ec08d87eaf5bdf6eac3000000000000040000010200379ae7d587a4fbbfd88c000000000000040100000002148cd6a7abdbd9f9c9840000000000020001000400005087ffd7d0ad9780808000000000010000000501000033e5b7abf5f0b080808000000001000000000500010007cfcfa8dee1e3bbef83000000010000010001040000048db191c0e0dcc490fd00000100000001000005000001e2c8c2e0c48080808000010000000000010005000014c2bb96e0808080800100000000000000010500006c8fce80808080800b,
  0x5010100005693d48ad3fcb3f1c59100000000000003000202000013c4baf2c49bc6d9bec50000000000000400010002002ccc8bbda8988dbfdc8e0000000000000401000001011e93dfc1c3fad280808000000000000100010500000046dacbf6b380f2c2a6ab00000000000300000003010021828bccaae4ebbde6b70000000002000000010400001dc4f7eaa7d0f2d4a280000000020000000000040100078cf0bfdae0fe8383a000000100000100000005000002a3a7abb2b687c996b00001000000000100000500001c81a98c9de88eb5ec010000000000010000040100019cd9dedfa4ffde8d0b,
  0x60001000029c9a4b58fa7fdfdf5d000000000000004000101010011f2f291addd828197fc00000000000005000000010107abd2c7b59b9ba0abdc0000000000010100050000002d99f0d7f9dfdec0b8dc00000000000400000000020103ec9fb6accfd0f9f8df00000000010101000004000018c3f98fd9d6f1fccea800000000030000000001030002aeb1e9f9878dc1f2c8000000020001000000000400049b94f5cac3aed4878000000100010100000000040001b79fafbefcfaf8cc8000010000000000000500010012d7c3cb98a4d0c88002000000000000000000040137b5cb9b83e8a8800b,
  0x60100000015aaf0b9ccb9f7bbe2e400000000000004000102000011ecbfb3a18c8e839b92000000000003000001030000018ad1bdcceee99aec9a0000000000030100000102000df2c788bca8fbe1f8bb00000000000400000100000202b0f7a3ce97c89188800000000001000100050000000ac2ef92c7b3e0c4e29a00000000020001000004000005a1f2a6e9f1d5afbde300000001000000010500000005d7c7a0b0a69df6b9a800000200000000000004010041bdb9fa8dd796978a0001000000010000010400000e92b2b3fce7e992a601000000000100000005000058efedcdc9c2af9b0b,
  0x106000000000ec294edbfc5aad8bf9b0000000000000500010001000599dce5fbecc0a781e30000000000000501000000010283bf8880808080808000000000000201000400000008ab8ce7d09fc4d4f2a900000000000301000101010008a2e8fcc493bfd8fe9d00000000020001000202000006f7a3e0ebbeb1e7e3b000000001010000000401000001dedefcc897f0829da70000000101010000000400000486eccc94c5a5de9bf9000001000000010005000000019989aca594fdcee48000010001000000000104000012bfc3e09cd5ca86e0010000000001000100040000018284b9b3ffed84de0b,
  0x5010000010039bba1f99cdb99c498c700000000000104000002000001a69394bbe0d0ffc2e8a6000000000003020000010001069b91acb293c3f4cfa10000000000040000010101005093fbdacfaecba7d4cf00000000010000050100000001cbd5c881abced888fbed0000000001010100040000004895e8e5ebd4e7b599830000000100010001040000005482d6e398f7f0c6c5b80000000102000000000400000c9fdaf6d1aaa0c0c4c800000300000000000001010206e9f6e8b4f6cfa3f48000020000010000000000030101a7acc581fbbdbdac8002000000000000010000040009dafcaa99fdd088800b,
  0x5010001000001a1eea89dfc86d5caf2ce00000000000401000000020035e3c9f5e3dae8a299da0000000000050000000001014daed0d6baf3edb2f600000000010001040100000065adfaeff2ff80fccdc70000000001020000040000006ef2ecd6e79bbdfdbb970000000001030000000300004686d5d180e7ebc1e7f40000000100000005010000005b83b4db99e9ae80c09e00000003010000000000000303def3b5a092ecc68ebc00000100010000000500000017d7f0e6cbc9b8aeaebc0001000101000000010101010398d2c5bdb1b4d6b1d60100000000000100050000001984c6c4a29293bad90b,
  0x6000001000001fbd79680c0fd8cfeeab100000000000400000201000001b299fea0f99380cbc4dc00000000010100040100000002f89cedd4d2f5bdcbc2e00000000004000000000102002197a4ddd1c196aac78800000001010001000400000016f1d9eb8b8fb280d7aa000000020200000000010002088280a7b3fb9bc4e4eb0000000300000001000102002595d6e9eefe87d1f5800000010100000000050000002cbef9dab3f1bff9d5d0000001010001010001000101029f8db5cc8ec086aab000010000010000000500000006d2e4808080808080800100000000010000050000003780808080808080800b,
  0x6010000000002c5e3b3fbd2fd8fdb9ece00000000000500000100010027e9f59cb3faac8fb3af0000000001030001010100000398a1fff1eec7bcd9cee300000000030000010300000039e081e1e6f686c89783000000000400000001010100528cc191a0b49fea838500000001000100050000000001d58497c0a49eb3c4e2ec0000000300000001020000010ec18d86af8acbbda9b000000003000001000002010004a285c89eb9b5d4c0ac00000101000001000400000060b3adf4eaff8293c0800001000001000100040000000f9fabc9ec8184c18080010000000001010004000000018ca1fdddc694f280800b,
  0x10600000000002af897eacd8bb48cab9500000000000500010001000017ebd3d09687e5cc99e000000000040000000201000009d088f1c9f4e2d480b20000000004000001010001000a9eb0a2fdbdfa87ded00000000004000100010000010189bcba8382d4c7dd820000000101010003010000003aeeb281bfedb7868ff000000004000000000001020008d9eddfbaae88bc840000020000010000040000000394acccc7a296d7c49b0000030000000000010300000480a4cfe0b0c890a7ee000100010001000004000000039bf3c0c4a88b80808001000001000001000400000020f0c3cbc7848080800b,
  0x500010100000003ba83aedbd2b5d6d5fbf200000000020003020000000002dce5ff9db9b2ecc3ba820000000003000300000001004dde829fd2e0808080800000000004000100000200000180d6cac5dda19e83a2ff000000020000030002000000028de3c2918ee6e29e98eb00000100040000000000000203e8f8f0a18080808080000001010000000500000000018887a4bbff8acad4eeaa00000300000000010003000016c6cb9fcebf9291c8b000010000000005000001000022c1f3c888dc8dc4e0f20001010000010000040000006493efea8ad0b294c6010100000000000104000000039ee7cbd2a998e9a0880b,
  0x501000100000015e7f1d1e8b8d2c8d1f0000000000400000102000000048fdbd8e984c6ffa1ac00000000050000000001010003a8ffc2d4c6f5cc8e9200000000050000000100000127d3c6eabefb8697af0000000100010401000000000db4acbec9e5a7aab7d00000000102000004000000000ef69faa9eacb99db0fd00000003010000000102000004b2e9efc49babb6cf910000010001000301010000000ca4cefac6afc08cf1f00000010001000400000100000199d2dec7beca8fc29000010000010003010001000002d0b399f2f99cf3e8800100000001000300010100001de68d84c1d1d0b0800b,
  0x6000001000000269cc3aca4818b998da00000000004000002010000001d86e6ebf59280c1edd000000001010004010000000039eaba9b95f283dfc6a000000004000000000102000006fabad58e9fc2ddbecf00000101000100040000000001def1eacd85d0ebea8a00000201000000010300000001a9f19bc4babc95a6eb00000300000100000003000003eda2a0c6abc6fe9cf600000300000100010000020002bddb83908ef7df94800000040000000000010000021c929ac4a1c5fdd88000010100000000050000000006a2e2d39fdba59dfea20100000100000005000000004af3948285938bd6e70b,
  0x60001000000000cb5dae1bdffda9fa79c00000000040001010100000003c2a991a3c8d7bfcecd00000000050000010000010004adf190b39fc2809ae80000000005000100000000012ef4edf1d8bbf9cf870000000101000500000000002af38f89f585b285d9af0000000101030001010000003282bd81e685d2ad99f20000000104000000000200000be3e5d2b0c7abbbb0a000000100010201010100000016efbebad0bed7eea3c1000001010100000400000000089190baa4dde891dcbf00010100000001040000000008e5a6acdcb4808080800100010000000005000000006ecc8d99e0808080800b,
  0x60100000000000386d7b49793c3f1f1ee8f00000001030001010100000004a1aceacffff6bbb880800000000103010001000100001fededd589dfecd4eab00000000400000100000200001bc58cc8b7eec9d0c29d0000000400000100010001001dd6d3efcbaac980808000000004000100000100000102af9bfdc780ec80808000000100010005000000000001d39782e09aa997c1f8f00000010200000004000000007ee0dfa9bec2d0a3d19a0000030100000000000300001bad87cd8b9eebe3b0b20002000000000104000000002feac5f8fa868db8f3a401000001000100040000000009f3e6b3c6c39a87a0f60b,
  0x1060000000000002583f9b0a9a0f3bcf29b0000000005000100010000000bb3cff191f6d4d8e39e0000000005010000000100000c86b5decdaff0a2b88000000001050000000000000111c49fdbd8e2cea08000000002010004000000000019e3add4f4c0fa8f898900000003010000030000000019d7c99694c3ae83a19200000004000001000200000004e5fbab8cd780e8bbc200000200010101010100000018dcc98ce3d8c0e881de0001010000000401000000000cf597a8f28ce7adc6ec00030000010000010000020079fadccee088a4888001000000010005000000000001e891d0e5f1a9b7d5960b,
  0x104000101000000003cd08a8ce7dabda2c5ce00000004000100010100000002a3e08bc0d5e8b4e1ec00000005000000000101000009acb4d080808080808000000005000000010000010001aa94808080808080800000000500000100000000010b808080808080808000000100000600000000000031c797f0a0dea9c5bcd90000010103000001010000000ec5c4e5d2c0f1fcf19a00000102000004000000000025c6c093e2efd98ce28d00010000030101000100000007b6d9a6f3f6deaab1fe00030000000000030100000005eafb99b8f2c7a3fafc01010001000000040000000003d3e99abdcde4cffdce0b,
  0x5010100000000005ac2dccea1f8fe9ccb8800000001050000000100000001c5c2d5a5e2ebb2a5c8f800000004000002010000000002ab8cc697f6f1bbc5ffb800000100010500000000000002d2b3e1f18acb92fafeee00000300010000030000000004b0f3d1deefe99dc9800000040000000002000100002cafb8a1c3d3bea7fcf40000040000010001000000012ef2f28cbffaabd4db00000401000000000000020002fedfabb8cc83aed4b10001010001000400000000000184a1c08289b69c80b292000200010001000300000000188c98d1d79dd3d1b2f70101010000000004000000001c91da90a092c8fcb0800b,
  0x1050000010000000071bcfe9e96d3a6bac3b700000003010102000000000002d8addc9d98b791a4b30000000500000001010000002ef1f6f49cd1e5b6d8c90000000500000100000100000af1ee8e9da9dfd4e88000000005000100000000010001b1f8a2bfd4a7b990800000000501000000000000010aa9d1fca28dd6e08000000100050000000100000004a59bb586e5cfb1c3b700000200000401000000000060febfe0a0bf86a385ba0001000001050000000000001986b1bbf28edfb59ce700010101000004000000000035feeda0a4e8e789b0bd0100000100030200000000000ba0f8acf7d0d1e680f60b,
  0x60100000000000077ef96ddc3aacb88d3c400000103000101010000000001a78ba298b7bcc7d8808000000103010001000100000012f8a3bed3eca9be8a8f0000030000010300000000002598f89de29797b1afe4000004000000020000010000098edeb28587ef858ad70001000100050000000000003fabcec3f58ec7c998f80001000301000100000100000186b186b6eabcd8c7a9000101020100010000000100019d9bfff1f3d7b5b9b000020200000002000000000108d1a5e7f9fedee89f0003010000000000030000000ac1bea3e68ab7ceb1fb010100000100040000000000119dd8848080808080800b,
  0x1060000000000000003e5cdf1c2b4f9e694d100000103010002000000000005f0faa1d6b6c9bde29600000201000400000000000004de969fcf829580dfe500000401000000010001000012979ed8f5f1caddc8000300010000000300000000019896a7b792a693d5ba00040000000000010200000050ebbcbea0d8d4a2e800040000000100000002000005baf6b5e4c59fc89001000100000500000000000058faeefcc2a4cffdac0100010003000101000000002ba2a7bb9b9b91bee20101010002000100000001000392a7d2d4cffaf5ec01010101010001000000000113dffbf4e5d5ee860b,
  0x500010100000000002887afc0b2f5d6c8d2b00000010006000000000000002197dee98bc580948ff70000040000010101000000000faffe9aee9ab9ce88c900000400000200000100000006f884ab89e7b6a184800000040100000100000100000196f49886d7ece3a8800000050000000100000001000fb1bf98a387c9f0800000050000010000000000015ba3c795f79ce08000020000010400000000000006a6fb80efeba9e6b0f60003000000010300000000000680bed3fdf6f6b0d6ad00030100000000030000000003f9a3e79684ff9ea6bd010100000005000000000000099bc7deffb9c5d4fb9a0b,
  0x501000100000000001592e780c297edf4cfd700000101050000000000000007b1c7c997c88abdc2d70000040000020001000000000ce2fff6cfb4a3dfa0800000050000000100000100003efe90a6c9fadbf78000000500000100000000010006879a97b3b5d2d7e000010000060000000000000008b281cef0c99291a5e90001030000000300000000000597e3aba8b9de83bde300010400000000000200000001c4c1eb978acbd7928000010400000100000000000121f0e7c1c9ddacc800020001000400000000000006b694dbefc0eb9baef601010000010400000000000006c2c58adae6d08080800b,
  0x5010100000000000014debbdeffffa3dc9c9100000105000000010000000019f2dbd5faf8988080800000040001000200000000002883ffebe896cbc0808000000401000100000100000004c8a3add5ebe9c1a1cf00000500000100000001000071a4a1b0a2808080800000050001000000000001000aa19dcbb0808080800000050100000000000000013687e780808080800001000105000000000000002bcde5e087d2cfa2e0e300010005000000000100000001a69cefb9f5b6bedeb100020100000400000000000011c788d6ede4d0e387c4010100010004000000000000148cd6a7abdbd9f9c9840b,
  0x104010100000000000008b1d383a9bb87d29bfc0000010500000100000000000be0a3f1d0b89cddc4c600000400010101000000000002bb87a5a992c2c8e5fa000005000000010100000000069bc3c6b1a2d0cdccc000000500000100000100000001a9b5bfcabf8a8785d00000050001000000000100001886e786d088c4f9d80002000004010000000000000edafee4d8d2df8a89ae010000010500000000000000028e97b09e9dcc92ddb201010100000400000000000005a2c4a6ab82e493b9a30301010000000000000002007e87a0fdd8e8a4810400010000000000000001010a93eebdd7d0e7aa0b,
  0x106000000000000000008f7cc85e098f998f9d100000500010001000000000007dbcbbaa6a9da8e808000000501000000010000000072b6f7eed4a4c8f6f6000105000000000000010000058a8babffe1c080800002010004000000000000001d89fae597d68be2dc00030100000300000000000007aa9af0fe819c80c0800003010101000000010000002bb6a0fecae1d0808000040100000000020000000042c5c8be9e90dfc4c50004010001000000000001002dcfb29fb680808000050000010000000000000101baa1ede880808001010001040000000000000008f9c2f1cf9eaae6d1a40b,
  0x500010100000000000001dfe1d3cb98d3f98aa5000005010000010000000000148de0cc978a8ed0b3c000010203000100000000000018928df3a6edd0ecedf600020101030000000000000026b0a3dc80c889e3a1e80100000501000000000000000ecdbbdca8afb29292c40102010000030000000000000bea86a5c9e4bd96b2c50300020000010000000001005aaa98ddd788f99603000200010000000000000102d8aa88b492f6af03010000010000020000000002ad8ef6d0a0ef8e91b00400000100000000020000002bf7dacdbfe69a9aa20400010000000000010100000ae2dbcaaa88c597e40b,
  0x10105000000000000000007f8c8e392acd6e5ccf600010400010100000000000004fdca9ea1a5f483c9ca00010401000001000000000003d290e1b9d093eec38001000301010100000000000002cbf3fdcfdfd681d3ea010200000400000000000000058ef9f3b7d3e29dc2bb01030000000300000000000001bbe9c5a3d786c2ff8401040000000000020000000032fb86f9d1d2fc87800203000000010000000001000cacd18bb4fcd8800301010001000000000000012bebafba89b08003020000000000000200000007e385b38cba9bcd8004000001000001000001000001cab0e9eceba694800b,
  0x5010100000000000000068aa69ce7d59a8680eb00010500000001000000000006b483d3dbcc92be9f00040001000200000000000003a8ddcecbd39fbbc08000040001010001000000000001eaa393c68b85d7e1e100040100010000010000000030dae4d98481a9a88000040101000000000100000006f3a1bbc5f3b1cb8000050001000000000001000053b5d391a2aed1e000050100000000000000010004dd88c6c39d8ca801000105000000000000000003d2ed999da3bc89a6c40104010000000000000000010fcaf1c3a49ee2020100000400000000000000028e8785ccdc9ea99dad0b,
  0x1040101000000000000001ad7d6e5b0f3bcadede30004000101010000000000001493cfddd8999feadb8500040101000000010000000001cca0e0f9f88080808000050100000000000001000002abe4e880808080800100040100010000000000000ca8e9d482de9495a4fb01000500000001000000000008c29bd2a4b8c080808001010005000000000000000015c886f4a9acb886d0b90102010003000000000000000de5cda1ecc4abc2bd88010500000000000000000001308080808080800202010001000000010000001ae4e985c0808080800202020000000000000001000fdd8080808080800b,
  0x10500010000000000000020d29de096adcdf9addd0004000102000000000000000bcfa89fc9f5e2e4ebdc00050000010001000000000005dffcaac1e9b78c89c00005000100000001000000007f97c6bb93d8eddea0010101040000000000000000218cd3efda8895baca8101030100000200000000000003bc858b80bd8180f3e2010401000000000000010000019ee8a1d2a0ece9cc01050000000000000000010007d7d08a969e858e0203000001000000010000000fb1a6bae2b0f8d0c803010000010200000000000008b4fbeeff83a486fdde05000000010000000000000115d193af84b5850b,
  0x50000020000000000000004d4cae9b2808e9fb0ee000500010001000000000000058eaebdb0808080808000060000000000010000000013a4bbf48cc08080800100050100000000000000000d8df9c5b7ae8eabb5dd010201030000000000000000078793f48ba9c9e6d3db02020001020000000000000003e7be8eb08ff1e0cf9203020100000000000001000010fce28898ab80800400000101000100000000000184f5b8bbe08080808004000101000000000100000001fada8ae5a2c0808004010100000000000000010058a2b190fec68005000100000000000000000101d0d1a2d6d9d40b,
  0x5000101000000000000004ecbd484e6fc82fdc400050100000100000000000002e8fc839e9fd689f08001000600000000000000000007c88db597bdc998e8b301030003000000000000000009bcb585d3d9bb81c9d401050000000000010000000008e4eabaf9a78a8080020201000200000000000000059380fadbf5fd89ff9e02030001000001000000000042d1fcd4ad9dd6c08003020100000000000100000067eaa8f1ccbc808004010100000000000001000006b1eee9b9f080800500010000000000000001001e99ae84c0808005010000000000000000000140efe28080800b,
  0x601000ea5b78dbef584a7b4d192000000000000000000040001020ae7b1ffb0e2d486c8d8e30000000000000000010101040006a491c0becea4d59199e60000000000000000030000010305d1e2fbaff386dd8285fd0000000000000001000100050006e5f6b6becd96e499cb98000000000000020000000001045cf587f694c7fefdf6ba000000000001000000000104011d9584a58bacbec2e9d80000000001000000000000050103ab9986f9b4d1fcb0cd0000000100000000000100010422e1e4f686a4dbecdc0000010000000000000100000501f4b6b398eec5f996000100000000000000000100050891c5dc8ee9caac010000000000000000000001050ff298b28daa930c,
  0x50100010280f9abe2e6e5f1ef9f93800000000000000000010105000003c4b6a183c28af89cc085820000000000000000040000010201979b9083c193c18bedae860000000000000002000100040001f89e81f98bdbd49e9dfced000000000000010001010004000192fbbdedc090e3cdfed2a8000000000001000001000104000dcedddac0d98eacf291de0000000000020000000100000409969ddee5a1b4f5cacda9000000000100000001000005000588e5988f93bcecf1f0ea000000010000000000010005004994fba5949ed1bdb9f80000010000000000000001050005c8edbf80fbeb89ba8c0001000000000000000001040120f1b6bec8e0a5cd98010000000000000100000000055980d6ab9ffbd9d60c,
  0x1050000012cad9cd8acd2f2d6a1bfdd0000000000000000030101020033dcebbbbffae2a9ccb1e7000000000000000004000101010acbba80fddf95d28cb4f30000000000000002000102020038feefe4eeec9fc5c7b1ba0000000000000100000105000026c0b6f9c4c7d8a7c99ae20000000000020000000002010204efb4cab08c84baceace10000000001000000010101020101d1b8f3bcfa88e4ca84840000000001000100000001030112abcfa5cfdc87bbe6ce000000010000010001000000041dcbedc5bd80d0c6e3980000010000000001000002000302cc959cdec792be90fc0001000000000000010001020211d3d487969c98e4b8010000000001000000000000053785bf98ab839dae0c,
  0x50001010011bddddbd7a9e7a98bace00000000000000002000302000011e2b6819bc8f8d6a4e5f40000000000000003010001020002c7fca7adcfc3baa8e9dc0000000000000004000100000202e1dfb39f90fbc2c386a9000000000000020000010400000799d1f099a2e4c4a2b2e9000000000000030000010002010394a99dcab99ede818a8a0000000000010000000500010007dbdde68cfcdfb0d284a000000000020000000001000400749dcc99bdb8a9a289b60000000200000000000100020211a5b3f98ab8cdfdd8820000010100000000000000040104b4e0fefeb9f8c387c80001000001000000000000040126dbdd9b968c89f89001000001000000000000000203019bdb9e879581db840c,
  0x50101000063f5f08ae4c1b8b5e5cab10000000000000001050000000106989fc5e9bf93e8edb4d1000000000000000400010002005396818cb0d2befa91a69a000000000000000400010100010ea6c4dcdf85c2aed1c3a70000000000000100010500000065e38ff6eae8e9e2b3f1ba000000000000020100000400003bf3fdb8ff9585b29fe5930000000000020000010003010028fdd9ecb090a58defc3f000000000030000000000000103079e92f7eaecbacfa4c0cc00000001000001000000050000048b9fd5e491f1b1edc9b00000010000000001000005000042c1edcef38b94b89df800010000000000000100050000058ff5f3f7c1ad94d9f0010000000000000000010500001794cee1a9f3a7fb9c0c,
  0x1060000000073f2e0dba09c9dbde8c0b8000000000000000500010001005bc8ddbfddb6e98c96a4cf000000000000040000000201002a8acbe6e2ecb7cdc49aa10000000000000401000000000207d0bfa6eeedf1fcd0cdcc000000000001010001040000001be0adf785f787c78794c30000000000010101010102000001a89cb38ed8fe92bd93bddd0000000000030001000000030004c7d8b5d1ad85e4f0e3b400000000010001000005000000458c8aaffab693fb96819c00000002000000000003010001088ca3acd5999cbab294a80000010000000000010500000002c7ebc48fe491eca79288000200000000000000010004000fdbbce880addad59e880100000000010000010101010101b0e28684d7e69cb7e40c,
  0x5010001000002e7caf3c1f1edfaf9f68afa0000000000000101050000000004afdaec9ee8f09cc5d18fd70000000000000105000000000105bde98781f1fbb285b6910000000000000400000102000001c48fbe98f4b58cf1c3b7fe0000000000000401000000020001a6e4edd4c7d0d09de5db85000000000002000100040000000391f3ec85a6d4e8adea8db9000000000201000000000400006f9de0efa095e6d1e7d6aa000000000300000000020001013183c6e8fdf698e882cca200000001000100000005000000608bbedbe6b2e0e7c89dfc0000020000000000000104000008b78dcbf5c5b5d3fa928b0001000000000001000500000001e5c2abe7e9809bc2948c010000000100000000010400000b97fba5bba0e8b1a8830c,
  0x501000001000050c7f1e69aaec784a1b9e6000000000001040000020000000281e58580a1ccaec9f0d18f0000000000040000010101000001b0dbf0b4df87ebd8ce81c70000000001000005010000000002b0b4ba9addcda996b992f20000000003000000010300000002e1a08fe2e4c9a1a6d6b8000000010100000005000000000193b9adaeabd6c796a6e0ed0000000300000100000002000106d8d0d8b6dec1b1f0dec4000001000101010001000002001cc4e2afad8ee0d8c5eef50000020000000000020300000004b19ba0e98af7d3ccffe00001000000000100050000000002daaea8af93c090d6bafd000101010000000000010102000389b8dcc58ca0b6bbca930100000100000000010400000030c4a1d7c1d0c683d7840c,
  0x50000010001000005feb4d4c9efbaad98d29eba000000000100050000010000000e8aaeeb9bc9b4f394ada9e90000000001030000030000000005c1cfefacc8bcf68298efeb000000000400000002000001000b8cebbdacac80d8c3b1fc0000000101000004010000000009958ce4f0e1c0b4cc85cfd900000001010100020101000000059dcba0b7c7fa9ee29886b40000010000010004010000000004889def859abd9d9cc9938d000100000004000000000002003b9581c09ed3abfae495d7000101010000010001000001010cc6b9aca789edddfee2f30003000000000000000102010006ddfdf791efffa8bdcbe3000300000100000000000000031388e482e7f097b6c5af0100000100000000050000000007abb2b794d29794e6a3800c,
  0x50100000001000001cc98f7a599ddb3ca98d6970000000001040000010100000002fcf386c1e899b1a4b0efaf0000000003000003010000000002e9a4e5c68989e4bc9f81ce0000000100000500010000000005978b88f0f6b1c2988f9dad0000000101020001010100000002b193aaee8bb0d2c5fff78b0000010001000005000000000002a9d7a4d39796e5f8e2f7ac0001000001010101010001000002d3e2b3e4f68a9bc7a3da0002010001000000000000030006fadae2e0a9bf96bda7e0000300000000000000030001000debbef7c8d2f8f0ebb5ea0100000000030001010000010078b6f4cfc598e5f5ac850100000000030100010000000102eef9d9c6888d868ff9d6030000000000000000000301003694d8e4a8e1bfb086890c,
  0x2030002000000000001bfefc488f88bde8e91df960000000005000001000001000006b6a6a08fe6e8caabe1990000000005000100000000010002d1a1e680a588a0b7a49c00000000050100000000000001169087e9e3c8be85b8cf000000030001010001010000001decf0d2caa3f2f99a83ef000000030100000003000000000fc9d4c2fd9e909b8e9d90000000030100000101010000002ff697bac3afa0d4c6cfb3000000040000000101000100000be7fbfdb6ecfe89d8dacb000001000001050000000000007ce5b5ecdfad83b4b4e28e000100000300000003000000001ce998d9f3b6df91b9e4fc0100000000000501000000000002f0bff79cd5e484f0fff5010000010101010000010100001682fcb0fedbd3ded0ea0c,
  0x10401000100000000000187f5a6ecb4d3c4efe1cd8800000004000100020000000000448bc3dfef8addc7859cea0000000500000001000100000020a39097829380a2e4bcf00000000500000100000001000005d4f2d49c93a388c2b598000000050001000000000001004d8bc4baa990d7b4c1b0000001000105000000000000000190cff3b498daeaca91abf8000001010300010001000000007bbbdaaef1b9a2d9a1edb20000010400010000000000000103e0fbbeb58ff494bcac0000020100000400000000000048d2b7f695d0a0b180b8e10002000000010400000000000040a0c2a895e0e1c7b989980100000003010100010000000057e6fc9e85c0b4e6eca20200000100000004000000000008e7efb6b3b1f5a1d5dee50c,
  0x6010000000000000010f18ee5b4d283c4eaa6800000000500000100010000000009ccac8de2e3fbd4d4eaeb00000005000100000001000000029fedaffb9cabbaf1bec40000000501000000000001000018a6d7c391ef8eb1cbf40000020101010101000000000016bfccb78589ee88f2abac000100010005000000000000000cc7b9d3b183aeb882fef70001020000000400000000000007a382bebac184c5c681fc0001020101010000000000000118c6c0eba8d1e0b2b50003000000010003000000000013ebc5cd8eed9ecde5aa000400010000000000000002000297afc7aadbd7a195fa01000003000001020000000000038a91baf3c38ad4dbd7df01010001010101000000010000159dcae9dc8592b7b3860c,
  0x10105000000000000000034f79e8ebd87a48580eeda000001050000000001000000001187888897a49cbaf1bcea0000020300000200000000000058d499eaf0d383bd93eb940001000400010001000000000025a4b3a18cc29dd8e9aac50001020000040000000000000048ca9fa9b8cfc2a0ac95e4000200000400000100000000001b8eec9bbf8e9ccfa1adeb000400010000000000020000000188c6ba8ab4e1ce82aba7010000000501000000000000001f8a99fda4e7decba5b5db020102000000000000000200001a90ddacdaf6d5df9e86030000010100000000020000004581b5aad2a1e5c8dad5030101000000000000000002000281d7bba19e9fbab5cc04010000000000000000000002098cd5e69e96b8ebeb0c,
  0x20300020000000000000004aaa3c99bb395a2dabfa1d10000040100000200000000000002f4a2dacd96f4808dc1b5f900000501000000000000010000018d989fdfcebe90e1f2800001000500000001000000000001edc487e6c385afdeff9d9c0001050000000000000000000126f6e7c1e5a0b6e1800002000004010000000000000003fbb1a4f9819ff194afc1b60100000105000000000000000001a9f69baac0d0bfbafdd5880100040000000001010000000009b3b1dcdc92bcb5c1eae4010101000004000000000000001e9fe6bfeab080dad6d0ea0200030000000000010100000009e099938caccab084d4800301000000000100020000000013c2b98a8ec1a8b6fe908e0401000000000000000000020004ebbbd3b2e1c19f82800c,
  0x50001010000000000000001e7ae9ac7e3be83a891d2000005010000010000000000003d8be488ebb09e89f4dbd0000201010300000000000000004b95b0dac1a8e2fbb1ed860002020100020000000000000058d5ddc6bca79cdedf9baf01000005010000000000000000479bd38793cccaa6c9e6b6010005000000000000010000002ec0ac91dfeeda81c0b8010101000400000000000000001590d297aab08c9ac994e4010104000000000000000100000489fce482a6d3f3f68c0103010000000002000000000007d3d2fbc6dffed9abafd80201030000000000000000000156bfbedd8ce0c0b60400000100000000020000000001b2fcd984a7d8b0a993e5040001000000010000000001001bdef1e6d9e394d4d80c,
  0x501010000000000000000018ffdb2ab85dfc2878edcce000300020200000000000000002fa6bed7c0a7bcfcd5f4e30004000100020000000000000050e983ce8fdcada4d199e20005000001000000010000000001d39dfbf983aecd909ee40005000100000000000100000017e987b2e5ec9ac3d1b00005010000000000000001000001e88beaebbd93fd8ff8010001050000000000000000004bc8e1cdbacdaf83af98d20103010000000200000000000017f6aae893afb0faeaf8c80201000004000000000000000027bddbfef5acb782d5fbcb03010100000000020000000000059a818fea81c992e6b3f0030101010000000000000001000adac1af94daf1b9f0050000000001000000000000011cfd9f8b8db19a9c0c,
  0x106000000000000000000000ea5b6f2aad2f3a9aceeac0004010101000000000000000006a490ef81e7f1daf9f1b40005000100010000000000000006e5f6b6becd96e499cb98010401000000000100000000001d9584a58bacbec2e9d80105000000000000010000000003ab9986f9b4d1fcb0cd020100040000000000000000000ae7b2d0edc98780e081950301000003000000000000000005d1e396c49597db89e8e3040100000000020000000000005cf587f694c7fefdf6ba0401000100000000000100000022e1e4f686a4dbecdc0401010000000000000001000001f4b6b398eec5f996050001000000000000000001000891c5dc8ee9caac050100000000000000000000010ff298b28daa930c,
  0x4040101,
  0x80007000400040c010005020803,
  0x80000070205000108040004000c03,
  0x2060101]

/-- The triples `(n, b, a)` of part 6. -/
def enumC6 : List (ℕ × ℕ × ℕ) := [(7, 63, 23), (7, 63, 25), (7, 63, 26), (7, 63, 29), (7, 63, 31), (7, 63, 32), (7, 63, 34), (7, 63, 37), (7, 63, 38), (7, 63, 40), (7, 63, 41), (7, 63, 43), (7, 63, 44), (7, 63, 46), (7, 63, 47), (7, 63, 50), (7, 63, 52), (7, 63, 53), (7, 70, 11), (7, 70, 13), (7, 70, 17), (7, 70, 19), (7, 70, 23), (7, 70, 27), (7, 70, 29), (7, 70, 31), (7, 70, 33), (7, 70, 37), (7, 70, 39), (7, 70, 41), (7, 70, 43), (7, 70, 47), (7, 70, 51), (7, 70, 53), (7, 70, 57), (7, 70, 59), (7, 77, 12), (7, 77, 13), (7, 77, 15), (7, 77, 16), (7, 77, 17), (7, 77, 18), (7, 77, 19), (7, 77, 20), (7, 77, 23), (7, 77, 24), (7, 77, 25), (7, 77, 26), (7, 77, 27), (7, 77, 29), (7, 77, 30), (7, 77, 31), (7, 77, 32), (7, 77, 34), (7, 77, 36), (7, 77, 37), (7, 77, 38), (7, 77, 39), (7, 77, 40), (7, 77, 41), (7, 77, 43), (7, 77, 45), (7, 77, 46), (7, 77, 47), (7, 77, 48), (7, 77, 50), (7, 77, 51), (7, 77, 52), (7, 77, 53), (7, 77, 54), (7, 77, 57), (7, 77, 58), (7, 77, 59), (7, 77, 60), (7, 77, 61), (7, 77, 62), (7, 77, 64), (7, 77, 65), (7, 84, 13), (7, 84, 17), (7, 84, 19), (7, 84, 23), (7, 84, 25), (7, 84, 29), (7, 84, 31), (7, 84, 37), (7, 84, 41), (7, 84, 43), (7, 84, 47), (7, 84, 53), (7, 84, 55), (7, 84, 59), (7, 84, 61), (7, 84, 65), (7, 84, 67), (7, 84, 71), (8, 2, 1), (8, 3, 1), (8, 3, 2), (8, 4, 1)]

theorem certs_ok6 : checkAll enumC6 certData6 = true := by decide +kernel

/-- Certificate data, part 7. -/
def certData7 : List ℕ := [
  0x6020101,
  0x80003dd0000000400040a800000010005020a80000200000006500100000003040805,
  0x10601002d8000000500010212cb000201000500129b00030100010307ee010002000500088005,
  0x20500010003b2000304000001028000040200020003eb01000600010003f80102010400000ba005,
  0x80000000003dd0205000100000a800400040000000a80040300000001080600000002005005,
  0x4040b000102050f010001060103,
  0x40400000b050201000f060100010103,
  0x80005f99f000000000004000413f7c00000000001000502169380000000020000000601eca000000100000003042fa0000100000000020502d001000000000001060807,
  0x106010001f290c00000000005000102018294db000000020100050046a1eb00000003010001033db88e000001010001050055a88000010100000005010d90800100000001000600608007,
  0x2050001003ce59b00000005010001011183c2000001020104000076908000000300020003001b898000010000060000010ef0e50003000001000301088bd9010200000000050005abb807,
  0x1060100000006a78a9a00000500010200000480f5d9000201000500000003c9e4e900030002000300003bb1b20004010000000300018bc4c0000500000001000216b6b8030000000104000070808007,
  0x50001020000000ea382000501000101000018ce800005010100000100018dde010006000100000031b0fc01020104000000003c9ef80400020000000200018b9105000100000000020c8007,
  0x800000000000005f99f0205000100000000169380040004000000000013f7c004030000000100002fa0050200000000010002d0060000000200000001eca006010000000000010807,
  0x1070101,
  0x3050101,
  0x5030101,
  0x7010101,
  0x1060100049cb6b193000000000000050001020282cdb2a70000000000030001020202d8d6b08000000000010002000500028ec2818e000000010000010105001fada18e0000000101000000050118f5def20000010000000100060006f28080000100000000000106003f80800100000000000001050102808009,
  0x102020201000060ce89c1b7000000040100000003000382f1d0bc000001000006000001000aa4c88b9a0000030000000202010002bfa7fde2000004000000000102010580dffef00001000001010500000003b5a8f9f600010000040000010200018ad78cd80002000100000005000001c3dffcd9010000000400000003005680808009,
  0x501000101000017ddc080800000000600000100010072bcdfea0000010006000100000012f9d189b80000020201020000010001a7ccccdd0000030100010300000008c5f687ca0001010001050000000016bee4c9c0010001000006000000000183b0d2ca020002000100000003006cbcf193030100000100000000031280808009,
  0x106010000000000000788d2be800005000102000000000001b0a4a3d50005000200010000000002e6df9080000600010000000100000aab8080000601000000000001005ec0800105000000010100000054b4c0800105010000000000000103808002010005000000000000029a95d2a503010001030000000000038fbedaf209,
  0x5020143b900000102050013930000030101033ec30001000106002ca602000000020401f305,
  0x60100010017e1010205000000018ae801050100000105d902030003000067ae02040000020015ac05,
  0x10601000d9db5bcf2c000000000000000000500010206afd9b1e3ce00000000000000030000040107c8e8d5a88000000000000001000200050003e2a0cfb2dd00000000000003000000010401969d84a9e10000000000020001000000056888cff0800000000001000000010006002184e2c08000000001000001000100000503d5eec08000000100000000000200010422e7808000010000000000000000060101c680800100000000000100000000060480800b,
  0x50001020010b4fea89de70000000000000005000200012d8aefd6a2a000000000000001000600010043da9bb7b0cb00000000000003010001030012e4b2a3dcfd0000000000010100010500001cb6cbf9e8be0000000000030000000104000bf880ccdd96000000000100010000060000119abdfc808000000002000001000001010301cebde7d08000000100000000000106000033cfb9f48000020000000000010000000501f7e3e2e001000000000000000006010010f2b8980b,
  0x106010000001cc095a7b6a60000000000000501000101001cf5acba9c00000000000006000001000105c392eaf1a000000000000301000103000013efb4a9f5f000000000000401000000030007a881acc7cc00000000010002000500000014a9b5dba0e900000000030000000104000005a7f0cc9fdd0000000100000202010101000aaeb980808000000100000002010201010001fcd48080800001000000000102020101001cf080808001000000010000000204000001c08080800b,
  0x1020202010000000188e2fbb4b3ee0000000002010202000100002582aff3f3d900000001000006000001000007d4b58ea1b400000001000201030100000073a6a4d4e200000001010102020000010016c9b1f9e0e00000000200030000000300000de7f6f7b08500000100000202010101000007edaf80918c000001020000000005000000139495bea1b400010000000006000000000102c4aeea808000030000000000000103010053fba79fa002000001000000000005000015e9fbef980b,
  0x6010000000000010182fbe79b9000000001040000030000000001e9b18d95fc80000000020100050000000000018098ebfbe9c9000000030300000000010100018cbff2ccb600000004010000000300000012f18588d68800000004010001000002000015f499af84eb00000100000600000100000001eb8aa1a1b8e80000010005000000000200001287edb5a0da0000030000000400000001000cb4a2acccea00010001000006000000000045d887e3808001000000010006000000000007cd8cbe80800b,
  0x5000102000000000037bdf790d900000005010100000100000005979cc0808000000100050200000000000054fefcf7a20000010301020001000000000b899383bcb40000020102010200000000000bbdc898aab30000020202010000000100007eaa808080000100000600000100000000078890dcc3cc0001010101020200000000000aa6aabcc4f401000100000600000000000002cce9b5b8d00400000001000100000000023080808004000100000000000000030004e88080800b,
  0x106010000000000000022e2c7e1958000000500010200000000000007c7fbc4fb9f00000600000100010000000008a198d0808000000600010000000100000001c69ccf808000000601000000000001000018e3c9f080000106000000000000000001088dfca000020100050000000000000012f6feeda68f0003010001030000000000000dc3aefbbb960102020000000300000000000aa2ffdafa8002010201000001000000010001edef928003000000010400000000000004c8b6ecf6800b,
  0x10601000000000000000027d6a48bf7c000050001020000000000000016dae8acde97000600010000000100000000638ea7c0800006010000000000010000000b81cbc08001050000000101000000000004f0b3dfa08001050100000000000001000068b5808001060000000000000000010004d2808002010005000000000000000011b8eac1dbc703010001030000000000000008b0d2b1fec604010000000300000000000005d8bcab90800600000000010000000000010c80800b,
  0x4020264010105016b020200040903,
  0x7000103ac0202040005c30400020201a103,
  0x5020108bfa6fa000000000300030206ccbbe1000000010001060017f386000000020000040202cda89a00000100000105017187e500010000000006010aa3cf010000010000010533a107,
  0x60100010189e28be8000000030101030001e19addd000000100010600000195adfdde000003000002010219b4b2a100010001000500010191a4d300020000010005001180ccc1010200000000010403a8b1a507,
  0x6010001000039d9e6d1000301010300000032dab68100030102010100001cbd94a100030201010001000ffae2ce01000106000000002cd3c8a902010001040000000fbfb5f903010101000000025187fd07,
  0x601000100000018b2b99601020500000000004cb2cc9201060000000001005ff78c0203000300000000399fa9a3030301000000000103deb404010001020000000cff8db30402000000020000048fcf8207,
  0x305170101060902,
  0x503070103041902,
  0x7010f0203033102,
  0x205012f0401031102,
  0x30500070403011902,
  0x50300170601010902,
  0x601000101adb982d2b70000000000030003020001d9ece5b1cc0000000001000106000037c5efbfa0000000000300000103013fbcdcefec00000002000001000500209cfc888c00000100000000060100069ff6b8d60000010001000100050004affa98e2000100000100000105000182e0fdfe0200000000000001000502e5d0af09,
  0x60100010002f4e5e3e6fb000000000301010300005df3a5f9af0000000005000100000257ebc987ae0000000100010600000002a6c4d8d6e800000001010201030000348deff0d70000000102010102010004f9b09b9bf100000100010102030000028ba3d5b2b0000100000000060100002ac2e1f9bc010000000100020400000380ebe38c09,
  0x1040102000000000ada9dacc6b30000040002000200000001b9c2db84920000050001000002000001e0d0e6c9e50000050001000100010048a4d9dba600000600000000010001058e9dceee0001000106000000000002f4ddadd8b50002010101010200000004e3ada6c2d70100000007000000000001b7cd8eb1fb01010100000500000000738783cdbb09,
  0x6010001000000000aa5f8bba888000301010300000000000c8db7fc8f8e00050001000002000000028cc6df98e40005000101000000010008c1d2ef9a0100010600000000000007cd9edeb5a50201000104000000000001c5adc7eeea020200010003000000000282f696f7ac020202000000000200002ca295a8d40500010000000000000217a49ddd09,
  0x6020beedf0000000202041ac8d500000100030409c39c0001000100066bca01000000010603e605,
  0x7000111be960000030103011aa486000101020301189bfb0002000006000296f40100010006000389f505,
  0x4020200018afa00000501010127a8ec0001000700001bb4d50003000104000fb6a10101010104000eb5a405,
  0x70001001bb4d5000202040000018afa0004010003000fb6a10004010101010eb5a401010105000027a8ec05,
  0x4030001000aa09d0006000100010286ce01000700000007e0dd01030103000013fc9302010301010008e6a505,
  0x206000000000beedf0402020000001ac8d504030001000009c39c0600010001006bca06010000000103e605,
  0x5020141c7cad3f5e7a900000000000000000301010348d2b5a1b2cbb70000000000000001000106003ff2a9f0abc2ae000000000000000201000104039d84cba59c9900000000000002000001000507e793fea1d6f900000000000100000100030302bbc2f8dbbd9200000000010000010000010523caf5c6f9b600000001000000000100010502e7ccd389cb00000100000000000001010512f6c7dee90001000000000000000100064cc09fa5010000000000000000000106018cc7bf0b,
  0x60100016ed7fcf7d0fd8900000000000000020300030001afa1b1fecfcfce000000000000000400010201018eecf0b7c3f4af00000000000001000106000001e6ec89d382a9a40000000000000200020004004adfb896aae6be0000000000030000000002032596b0f4d6f1b000000000010000000006010017c08bdbb4b0e000000002000000010000000501dd97b9c5ddf80000010000010000000005012bafa1efc79000010000000000010000060002c6c5e0f59001000000000000000100060008ddcb92f00b,
  0x60100010036a6ae87b0ec9f0000000000000401000102001edadad2acdaa200000000000005000100000207e4d3f6ba9a920000000000010001060000000ce6ef8eb0ccae0000000000020100010400002a82afb9b8adee00000000000400000100010203f8e4f4efe0b100000000010001000402000025c584cfa7d5c800000001000000000601000008e196b4d1e58400000100000000000600010001aeb3ebdf9b8c0002000000000001000102020891e3dfdffe0200000000010000000000052c9996d78a0b,
  0x6010001000007c88baab9feacae00000000000500000101010005a0e9def6c3ace100000000010001060000000007e5e99083a0e4c00000000001040000010100015ec4e9dba4d0880000000003010000010300000180de9fc2c3bfe5000000010101000005000000069e88a1e6c693aa0000010000010102020100005cd4ce9fecdcc50000010001010100020101002f8ed9e884e697000002010000000000050000198bdd88f5c0fe0001000002000001000400001aa6d4bed1de9801000000010000000600000001d3f1d083ada80b,
  0x60100010000000002f4b2f48fecbff400000005000100000200000041d482b0dce6ce0000000500010001000100006795b7c592a0f20000000600000000010001000ea4b8f5f0e7820000000600000001000000017389ecc8b8ce000001000106000000000000039fc6faeb99ead700000102010004000000000004fcba8ff49b9aa300000102020100010100000002adbb88a9cfafd000020000010005000000000002f4b4c0a4e8ca0003000000010004000000000180b2bfc5f2a7d201000000000601000000000033ac8084ab88960b,
  0x105000101000000000003c59390fccab0e8000004000102010000000000029dcc81d0eefd8900010001060000000000000002d283ae9487b58000010201020100010000000001e8a0deb8898bc700010202010001010000000035cdb0fcc2d3d100040000000102010000000001f8bed68f86900004000000020100010000004393d6be9ddbf4000500000001000000020000059cc6dd82a7ee0005000100000000000002003eb2fcde8ac60200000100050000000000005ab5bc88f58b9d05000000000001000000000202d2ebd8c6a20b,
  0x6010001000000000000068aa69cc1dfac9c00010600000000010000000060f8b0a988898c000301010300000000000000079ea5b69596a9b0000401000102000000000000038ba5bdaebdd5e40005000101000000010000000ea0e1badfa6fe0006000001000000000001000ac2ffdfe39201000106000000000000000005ff9599eda1bebd020100010400000000000000019bb4badfb0a2ee0302000000000300000000000199e7eedf98bbc2030300000000010000000001248285fdee05000100000000000002000059b9bdee8ad90b,
  0x60100010000000000000004fcc8fcacf2ee0102050000000000000000000584c9aaba82ec03010103000000000000000005d4ccc1fce09d0401000102000000000000001c84eeb381b905000100000200000000000040dcc092e1f005010000000101000000000018a2d88784da05010000010000010000000002deb0b6d88e0501000100000000010000001bd4d594b705010100000000000001000001baacf3cd06000100000000000000010005f19ff90601000000000000000000010ae7fb0b,
  0x50301b2000103040b91010002057d03,
  0x7010ba7000301040d820200010502d703,
  0x501022ede0101060032a7030100040afb03,
  0x6010132a7020105002ede040001030afb03,
  0x10700000ba7040103000d820501000202d703,
  0x305000001b2040301000b91050200017d03,
  0x402020baa81f6be000000000100070006e4b9a0a7000000000300010402bfd8e68b000000010101010403fbd2e5940000010000020104429bbfa4000100000001020404e695a401000000000101051389b407,
  0x10007000001a5cdb4a300000001030103004ea5f1da000000010302010102b6f395b0000001000301020173aab7cb0000010200000500628ffdda000100000201040021da88b5010000000200050002a3f6f907,
  0x70001001ef4aebbe600000005000002011fcaf3caae00000101020301006d9e8ae1b200010001000600000ca3c9c489000300000001020201eb8daada000300010000000401f6a4c6b903000000000001045cf6839e07,
  0x5010101000892c9f4e5000000060001000103c1abf5f900000201030101000dcfbdd99f000100000601000004f79ac4b6000102000005000005fe938de400040000000100030d94f18b010000000600010001b3c398de07,
  0x1050101000004e982b5e6000001060000010001f9aaaae4000005000100020005d2a9bebe000005010000010101efaef6a800010101050000000794b99ac7000101030102000017ddd599910100010006000000058be3b6f807,
  0x5010101000002bca3d783000006000100010001c986ac9e000100070000000053fbb9d2000201030101000004e7ee8dab01000006010000000199d18c86010102020100000112cae786010200000500000001db8ea2d607,
  0x7000100000002d6b8ebad000400030001000001b387e982000401000300000001a2c5f2ff000500010100010043b490ea000500020000000104c7edf2010102030100000004dcce98ae010201030001000001f7ed81c807,
  0x70001000000000ccb9c8eff020204000000000018d4a9eef2040100030000000007f8b4e18304010200000100000184b6fec8040200000200000003fbd2e594050100010000010009ccaac806000001000000012692e807,
  0x5033bad000001030406d6a6000100020569bc010000010604f104,
  0x70109acfe00000301040b88e500020001050391fa010001010538a304,
  0x205010fa980000103000403f0a9000201010403ccf401010100050199e304,
  0x5010218efae00010106001be9c70003010004049483010200010407938804,
  0x6010138e58700020105003db68201030000041499bc020000050105cbbb04,
  0x10600012cc6cf00040003011e9cee01010204002cd4bd0300010103488604,
  0x107000012a7e500050002010efeba02010104000dc29d03010100030197c404,
  0x50102003db682010106000038e587010500000205cbbb04000003011499bc04,
  0x60101001be9c7020105000018efae0400010300049483040100020107938804,
  0x1050200000bdc8c010600010003ccf4040003010007bd9d05000101010199e304,
  0x10700000009acfe04010300000b88e505010002000391fa050101000138a304,
  0x3050000003bad040301000006d6a6050200010069bc060100000104f104,
  0x402020a86bb9aa4deda00000000000001000700069af3a3a3ead90000000000000300010401ff88e4e8dbad00000000000101010104048cf6d98bf2900000000001000101000554d59ae0f1b000000001000000010204098da5a4c8e00000010000000001010550c6b4d5a000010000000000010006039fdf83b80100000000000000010607b9d6a809,
  0x700017eadefe0d5c90000000000000301030149b9abf5f6e400000000000004010003529b9dca96af0000000000010102030102e99881e39dcc000000000100010006005797b9e7b3a4000000020000000100050781f1c395e40000010000000001050101b9e2c2eeb8000100000000000202030b9af4cb8a0100000000000001030326bdfd8e09,
  0x70001001c9b91b392f8f30000000000050000020106fae7bfe8bcbf000000000102010202002489b7dcfeaed9000000000102010300010e9ea9ffeba8820000000003010000030107a1b1d299aee7000000010001000600001592edf2f696a00000030000000000010401aa92ce9687a0000200000000020000041c89bca18a940100000000010103000202dfaea49db809,
  0x5010101004beeecb1fdfa0000000000060001000103a3aec490fdb80000000002010301010008ecf4b7a0c8e80000000100010402000005aeaaa7aff4bd0000000102010002020002c1a6cc86aaa9000001000101000500000189a3a8a687a600000101000101020200018cf9f994cffa0001000000020005000027a8a7c1aaf80100000001000006000002bc84fa9ae809,
  0x5010101000011ccea929e80e00000000006000100010001d193c7bcb2d7d20000000100070000000002a8ff96a6c792a90000000500010000000269f7e0b8bcb50000010201000202000002eccd87f28af3980000020001000500000020a8c4fcc5f4f8000100010100050000005985c0dce28ad60004000000000001000301df85ef9cc5880100000005000000000209c5e48bc4a18209,
  0x70001000000019bcd85f0b19b92000000050000020100000187d1c0d6d3e5ed0000010101050000000016c7d6f8c2acb400000300000203000000398fabb3d5feaf0000040000010003000016ff85d7a7cbb20000040100000001020019e28aa5a18bf50000050000000100000202c7f0c789a3cf0001000100060000000070a0f597debace010000000106000000000df8b0828e9eda09,
  0x70001000000000b9482978bc3940000020401000100000005a4b6dda8c0f70000040002020000000006a7a5a7e68fcb0001010105000000000002e3a988e5d2bb0001020202000001000004f281eba484a8000202000102010000000ef3f1d6fff8a10100010006000000000006b1a59285def70301000101000000000202e3c5c9be95040001000000000003001dbe9dd1809a09,
  0x5010101000000000382cdbae2a6ad000006000100010000000698b2fb8fdedb00000601000000010000019990dffaa0900001050100000000010010ec8ac7868c0003000104000000000007b18ff5d09edd0003010200010100000012eaffef9f91000302000003000000000693d2d2d4eebe0005010000000100000169b4a4bc84010000060100000000000ab4a2a0ebecac09,
  0x50101010000000000198fedd7dcfaa20006000100010000000008ec9f91d4cad20100070000000000000013cddbe7bbe9a70300010400000000000010e6acb3eef7cb0302000003000000000003e6f3ea97f8f60303010000000000000103f4a5dab60500000101000001000012ef80e59bd8050001000000020000005b98c3e99b94050100000001000001000191ddebd08209,
  0x7000100000000000005cee3edcce8f5020204000000000000000b9f82a8ed8cf20401000300000000000003e3b785ede0d90402000002000000000001dc90df95c0b004020100000001000000098da5a4c8e00501000001010000000054d59ae0f1b00600000100000001000050c6b4d5a006000100000000000100039fdf83b80601000000000000000107b9d6a809,
  0x70106eccba50000000301040899c8fe00000200010502d5fcd900010001010548c58f0100000100060389f505,
  0x2050108a4fc9200000100060102fea8f300000103000405bfb88f00010101000501ba9af10100010001050ae7fb05,
  0x40301018cc5870000010106001184a1a10000010400030efefff30002000101040384dcc30100000006013afda205]

/-- The triples `(n, b, a)` of part 7. -/
def enumC7 : List (ℕ × ℕ × ℕ) := [(8, 4, 3), (8, 5, 1), (8, 5, 2), (8, 5, 3), (8, 5, 4), (8, 6, 1), (8, 6, 5), (8, 7, 1), (8, 7, 2), (8, 7, 3), (8, 7, 4), (8, 7, 5), (8, 7, 6), (8, 8, 1), (8, 8, 3), (8, 8, 5), (8, 8, 7), (8, 9, 2), (8, 9, 4), (8, 9, 5), (8, 9, 7), (8, 10, 3), (8, 10, 7), (8, 11, 2), (8, 11, 3), (8, 11, 4), (8, 11, 5), (8, 11, 6), (8, 11, 7), (8, 11, 8), (8, 11, 9), (8, 12, 5), (8, 12, 7), (8, 14, 3), (8, 14, 5), (8, 14, 9), (8, 14, 11), (8, 16, 3), (8, 16, 5), (8, 16, 7), (8, 16, 9), (8, 16, 11), (8, 16, 13), (8, 18, 5), (8, 18, 7), (8, 18, 11), (8, 18, 13), (8, 20, 3), (8, 20, 7), (8, 20, 9), (8, 20, 11), (8, 20, 13), (8, 20, 17), (8, 22, 3), (8, 22, 5), (8, 22, 7), (8, 22, 9), (8, 22, 13), (8, 22, 15), (8, 22, 17), (8, 22, 19), (8, 24, 5), (8, 24, 7), (8, 24, 11), (8, 24, 13), (8, 24, 17), (8, 24, 19), (8, 28, 5), (8, 28, 9), (8, 28, 11), (8, 28, 13), (8, 28, 15), (8, 28, 17), (8, 28, 19), (8, 28, 23), (8, 32, 5), (8, 32, 7), (8, 32, 9), (8, 32, 11), (8, 32, 13), (8, 32, 15), (8, 32, 17), (8, 32, 19), (8, 32, 21), (8, 32, 23), (8, 32, 25), (8, 32, 27), (8, 36, 5), (8, 36, 7), (8, 36, 11), (8, 36, 13), (8, 36, 17), (8, 36, 19), (8, 36, 23), (8, 36, 25), (8, 36, 29), (8, 36, 31), (8, 40, 7), (8, 40, 9), (8, 40, 11)]

theorem certs_ok7 : checkAll enumC7 certData7 = true := by decide +kernel

/-- Certificate data, part 8. -/
def certData8 : List ℕ := [
  0x6010109bec7e300000201050005e792f200000400010304ddfcc900020000050103d6d5ee0100000106005ad2f405,
  0x50002011ac3e8d90001010402003380b7ff00040000010303eec9e901000006000107f58ce5010101000500029ee8da05,
  0x600010103d4f2dc00020103020006c397f901000007000001d6c9d00200010104000e98ad0200010202011dd3ae05,
  0x70000011ac0dcc800020301020060a4d8fb00050000010203969cb801010006000037edc0f402000301000201a4ad9105,
  0x2040101003380b7ff000500010101029ee8da01000600000107f58ce50102000500001ac3e8d903010000040003eec9e905,
  0x5010200000ac5e58e01010600000008d9ba890301000400000281aa810400010200015ad2f404010000030002b9e3f405,
  0x60101000007a990f90105010001000288d0e50106000000011dbed1030004010000089ab9e20500000102003e85ef05,
  0x1050200000008a4fc9201060001000002fea8f304000301000005bfb88f05000101010001ba9af10501000100010ae7fb05,
  0x1070000000006eccba50401030000000899c8fe05010002000002d5fcd905010100010048c58f0600010000010389f505,
  0x7000108e1a9a2d886b2c3a30000000000000000040100030897e18cd0fa9fa1af00000000000000010101050010f5839781fbb2b8fa00000000000002000000040246ada8c78287d5a200000000000002010000000501f080f7d9c2c9adaa00000000000100000001060078c1f7e6a0b497ec00000000010001000001000510a4cafffdbaf8ec00000001000000000000060101c598b294c28ef20000010000000000010100050cb7dea1cac1c20001000000000000000102043c9d95aaf9be0100000000000000010000060184cbc4859e0b,
  0x50101011593c2e98dd4ab98fa00000000000000010007000006b1c1f1b1dcd1a5ec00000000000000030100030116be81d097c7cee0e60000000000000100010402001be1cc8e8292a1dcfd0000000000000300010000043ed083a6eba6efc500000000000100010003020107ada8f7cea0e4c7a400000000010000000104000201b0dafeaf96c7d4c400000001000100000001020314e2f1a4afafe8c000000101000000000000010501f9a2cfb4b8bde60001000000000001000200040ce8f4dcd4e9ca01000000000000000200010426adf9c2e89a0b,
  0x6000100013ed0c5ed9e8af7f29c000000000000010007000000019abbc3e1e7f28ebac40000000000000302000003001ef1f9ff88f081efd7000000000000050000000102068b9cabf5b6b7e49700000000000101020003010001dfa2cfecce9b89fcf800000000010001010005000016cbdeb28da5c9a2aa0000000003000000000103010e86f4cbf09f93d8ba0000000200000100000005000781bba3b9b992b8ca00000100010001000000050001faf3d5cdffbaead40001000001000001000005001585c99fa8b5d48c01000000000001010001040066d88088d690ac0b,
  0x70001000001d6ccead0c8adbbc4f500000000000005000002010001bca3c091f4b1c19ff100000000000300010004000031e3c3aef7d699b8c60000000000040000000300013ae59ae0f6eed1bec700000000000400000100030035a68a96c9b4ce999f00000000010001000600000001d58faad39ee3d2fd980000000100000001060000001fe8a09c92daeaf9e300000002010000000101020107d9cbf0ccb5d48dd200000101000000010102020009eca9e88af8ead7cf0001000000000102020001010182b0bba8edcd9f910100000100000001010102010690dcd5e4a08fc10b,
  0x600010001000ad699f0dc80fd9fec00000000000006010000000106a2f9ccffe5d7afc00000000000010007000000003491d1dcb3e0acafaf00000000000500000001020005b4aafa9bedf780d90000000001010200030100005ee5b8eccc81b4fab600000000040000000003000101c2b4e4caa8d8c5ef00000001000102010101010019e7dc91a195cfd0c600000001000300000004000005f8f18fcaeed48ce500000100000102010002010006d588a88a8487bfeb00020000000000010005000032d1c6a282c991bc010100000000000001050000069385e585e691d50b,
  0x700010000002fcdeced9ccce6dfb100000000000600000001000103b1b69ed086afc9d60000000001020102020000000180d4c4c9f0cba5e6ec00000000020201000102000036bcabbc9fa7eddd8b00000001000100060000000008d6e2ecb0e58effdc00000001010101030000000101aae7f3a8e6acabbe00000002000001040000010028c8d28f90e5cfb4a200000100000201020002000016d0bda4e3d3f2d9f40000010002000102000002003b90a99b8fdcbaba00010000000000070000000003c1a0a3b484f3bab20300000000000000010100030aacabd1c8c8e4e60b,
  0x600010001000014d4ffc3cdecaae0df00000000010007000000000019f9b98afcbc8880a700000000030001040000000013b2e5e7f0b39ad6da00000001010201010200000036e6d8da9382e18ee100000001040000000003000003a2ccf3c6889f98b50000000400000001000300006aa0b2ba99a3f8c60000000500000000000002016de9a6cc9ca2c8d60000030000000003000101000786a48286af89cec200000400000100000000000350b2f3b7f28da800010001000000060000000003eee0a1ecfaa289aa0100000001000006000000002988bfc2dc8dfada0b,
  0x20401000100000027b7df9be2e0fa8ac30000000101030102000000001a9b8d8196e3e8e4fa000000010203000100010000149fc9f29dedf5dbe200000002010300010000010004e6d8c98b9fd4fffa00000002020001020100000022acbdea9bb5c681d70000010001000600000000001dcc8eccd29cc3aec000000300000000040100000006c9ba8ba3e192d6e800010002000101010101000004fbe78db69e85a5f600020000000002040000000002fb86cfaea9cbaeb401000001000202000101000057e1ffdcfd90bd940100010200000100010100013382e698db959caa0b,
  0x60001000100000015b1e7918fd6f4dad80000000100070000000000001afbe9ac8595ae9e990000000500000100010100004ac0e9a4dec6d79c0000000600000000000100010a91eda9c4c7aabb0000010201000202000000002796daafb3e999a3b7000002000100050000000000048cf2f1eaa6bcb49500000202010100000001010039edc3fafceccc820000040000000100030000001cfed18ddbe89abc00010102000101000100010058f399c3a087d0b900020001010002000101000006b6ffc5ddcdb195fc01000100000006000000000001cfc2fa81d3cbe0f90b,
  0x70001000000000006bcfafdd0c7839ffc0000000600000001000100003eaeee9baeb4fd950000000600000100000001001392c2d0e9efb8a20000010201020200000000000681e3fa9cb4909e940000010201030001000000000cf588c3c7fa84a1b50000020201010001010000000397e79df49c89a8b400000202010101000001000059d593ee83de8cf900010002010300000100000002bcca82c7cbabf8da000101020102000000000001018ca1fdddc694f200020100000005000000000003c8d999808ca5c9d501000002010102010000000001b1dfdb9b9384deb60b,
  0x600010001000000000ffeb3feb7da99b58000000006010000000100000008efefe587ae9be0ce000001000700000000000000119ba1cbf8d2bfa2d800000105010000000001000001c3ebc6b1e98999be00000205000000000000000179f7f8e698f0e200000302000003000000000006e9bff08d8599d1c5000005000000010200000000098ad899e9cfdc8f8900000501000000010000010014a198f7f4e6bc820001010102020100000000003ac3fef7a6e9bbeff401000101000500000000000009a6c4e4b8f3cbbb84010101010000040000000000019993ece0b5c5f5f20b,
  0x106000001000000000002f0f3c4dbdbe7f1c200000500000201000000000002a5efc999b1f4a8ed00000600000001000100000038fdd5c6d8fb89d800000600000100000001000007fbc5e1fbf5d6d800010102030100000000000006afd4ed8d9785eeb600010500000100000000010055c1a7ccbacbe800010500010000000000000103a1a2c5adb3a800030001000400000000000001bbedbf99d7fe94d800040100000001020000000020dd9cd2d692ad8b01000201030000010000000001cea6dedd85eb98fa010100010400010000000000019ae381a6e6c9bcfe0b,
  0x700010000000000000033d6cacbbdccd9dfc40004010101010000000000004fabb5d39dbff3bfbc00050001010001000000000003b4e18ed0f9c3b98c00060001000000000001000005a4cbd7c599a7de00060100000000000000010022e5f3d6f8c3920101010500000000000000004592ef84949ecbafb401030200010000010000000003dfd2b2b6f48bd39402020200000002000000000008bfa8d097d4cc9b9403000100040000000000000014c6e2fea6b4f7abf7030103000000000000000001688f80d9f6a20500010000000000020000001eeae493fea8fd8f0b,
  0x50101010000000000000009b7d7eddda5c3b29c00060100000001000000000039f3ee9cafee838001000700000000000000000004f19c86e8f9a9b5c70106000000000000010000006dc6b8a7ebebea0300010400000000000000000498d280f58ed79daf03030100000000000001000006f4a692d487fa0400010003000000000000002ae89be3cfc7c9a804010001000200000000000001b0f998c3ecc4bfba05010000000001010000000009868d9cb7bd98bc05010001000000000000010021baefb4a78606000001000000000000000149d4d0bbe60b,
  0x1050205c8e1ffa30000000003010402a2a4aaef00000001010204038994a99a0000010100000639dea4be0001000001000603f8d9f4010000000001060eaea206,
  0x501020785c4b6dc0000000101060009e1bda0950000000301000403b8e4cc8900000200010104029edce68e00020000000105228cb5d40100000001030303b0c1a406,
  0x6010103e78eb9d80000000201050004f6e9878a0000000400010360c9afd70000030000010401a6eac0fa000100020100044aae81940200000000010502a6cdb906,
  0x107000003d29be0e1000000050002010382c9c8d70000020101040001989bd5f10000030002010201c99185a30001010100050001f0acdcd3020100000000050bc19ee106,
  0x600010117c5beabca000001010600001cdb80929c0000030101020104c2f5e8d00001020001040015ddc7c3fb020000000105003eb59ebe020100000100045ecef79106,
  0x701000036d6a2a9d80000030104000029e0aee1fb000005000101011ba4baeafe000301000004001ecd9ea1f1010002010202003abe99c501010000060000108b97cdf906,
  0x10700000036d6a2a9d80000040103000029e0aee1fb00000600000101108b97cdf9000202010200013abe99c5000400000103001ecd9ea1f1010101000500001ba4baeafe06,
  0x60101000017e3e0a4910004000103000005d7a1e7cd0005000001020008839aa7b20005000002000101e0aac3ba010100060000000fbefff89403000001040000029cb991a206,
  0x2040101000027a89f92810005000101010005d3cefc910005010001000101acd2cdaf01000600000100098da9e1b50102000500000013c3def5fa020101020200000abdb6cd9006,
  0x5010200000009c8bb8dca0101060000000007e0e8b3d503010004000000029e8ca0e70401000003000002cdd581f4040101000002004aae81940501000000000204cd9af206,
  0x10402010000000fe5f787f9030004010000000186b3d6f90301030001000004bdb9cc9c0400010300000072d2a8a6040101010001004498eba80500010100000103b0c1a406,
  0x10700000000000289c595be0401030000000002bfebc0e20501000200000070dcd3b6050101000100001cef929f0600010000010001fcacfa0601000000000107979106,
  0x107000db3b0eddfdb00000000000401030aeaf697e7c300000000020101040aefb9f5c0c10000000200000105028ab9b1de8700000100000102043d9cfde7ee000100000001010503f49de8d601000000000100060dd7c9d607,
  0x5010220fc9df9fdca000000000101060028e7ade4a5b100000000030100040cb5fef9ffbd00000002010000050aefd1dd94f8000001000000060103989bb1c1f0000100000001030321a1c2ceb001000000010001050194d6b8b007,
  0x601011fa190fc8b9700000000030200031eebb0a0abaa000000010100060023e3ed849b89000000020101000401e2def8e098000001000001060006b581dcf39400010100000100055c81a5ffd5010000000000060103fcd3dbb507,
  0x701002bcb9ba6f3b700000000040101022799e980ecfd00000001020005001bd5c9e88baa0000000300010103139af5a187ca000001000101050012dcdaa6b088000100000100060002a4a3feb7e801000000000106000fa3aaa4e807,
  0x107000022b4ddbfa78500000000050002011df7bceaa5be00000002010104002cb3a8a9af000000030002010214fda596a2b0000001010100050017e188adbbfa000100010001050003b9eecee7f201000000010105001bc1fbc3f207,
  0x60001014adc95f5eaf700000001010600005ae5c2cdf79800000003010102010aecff9ab9a800000102000104004fc4a3ecf7eb000200000001050041d095e7e3000201000001000406f7ce91b4e4020001000000000545f6edd09707,
  0x701000056c2b9a181e50000000301040000309ea8dcf0a8000000050001010131efb7debee9000003010000040033ebe5d497d6000100020102020007c4f0bb93a60001010000060000259fdca9be85030000000001000401bea19ae68907,
  0x10700000006d09caaa9fe000000050100020001bcbdfbd09f00000006000001010399fc92e6fc000002010104000007d4ecc7a9c3000100020104000003a2fad0f698000103000000040002c5818cf7ba02010000000005002dbce287d207,
  0x60001010034b1d88989ed000001010600000035f9e69fbbac00000400000301000285cd90fcb100000500000002011188eefebaca00010101020300004de9ab9c8ca6010001010104000002e5bdb5eafe010003000001030007c7b6d68cc807,
  0x60101000017c1f99fd89e000003020101010022aadaccb2cd000004010101000102fa8addebe9000101000600000016a1f9abecfc000300000104000002ebe6da81eb0004000001010002679be2e2ca010200000005000007c3f4ddb7fb07,
  0x70100000013c5b293e2b2000004010200010016f8d39acced000102020102000033cfcff8a19500030000040001000287ebfedba9000302000000030075aaace2c4000400010100000201ccd1b9a2b101010000060000000eb4eed4cfae07,
  0x107000000000aa2e9bcc3fa000004010300000009c7fed59f80000006000001010002fcadf5e78500000600010000014c8da4a8ea000202010200010002fffeb9dfc5000400000103000007c9f1a4b0af020000010500000003dca695fda307,
  0x7000001000012d2d6bbdadf00010600000001004c97f4accc0004000103000000119ebfcce2ad01000600000000011dfc8ab4d3010100060000000010e2b0a0f98202010100040000000299d7cac2d604010000000003006ee3fda5fd07,
  0x20401010000004eea8c89f89b0005000101010000118892acf18d00060000010000012dedf8c6be010006000001000016c4a69ef2e9010200050000000027a18085a5fa010500000000020002f09c97819f02010102020000001bc9cfb5b69807,
  0x107000000000009df9eb5b1dc00050100020000000ad4e599b4a1000600010000010038f0cfb1c602010104000000000eb6f98fcfd5020301000002000002a1cad7b39a04010001000101001098b09cb4040101000001000103e8eac99a07,
  0x50102000000003ee0a1929ff2010106000000000031b8e2ca8f8103010004000000000ec3f2859ca1040100000300000012c0d0b7b2c804010100000200000581d7a8eaf0050100000000020040f9b1b4bc050100000001000105ce8ce2f807,
  0x601010000000011d0e1b989e9010304000000000014eff1bb9903000401000000000ec3fad6c7f304010100020000000489eed2f7ed040101010001000001998aa2c8da04010200000001000cbcc8fdb2040201000000000137e0b59207,
  0x70100000000000e96b3bdfb8503010400000000000aa6c286c090040101020000000008c6b284eec305000101010000000494f2e3bc8e05010001000100003d9cfde7ee050101000000010003f49de8d606000100000000010dd7c9d607,
  0x1070008b391d2aed89400000000000004010306e0a4dacf96c00000000000020101040780fa96c5ffac00000000020000010501b7bbf39491a90000000100000102043084c1c396d800000100000001010503f787d88ed400010000000001000617c2c2cfe80100000000000001063dca8bc308,
  0x5010204d0d4e0d7c0ca00000000000101060006d7c89890d18900000000000301000402bcdeb8b1abf500000000020001010401ebadafa3d5860000000200000001052789f9ae81c8000001000001000204088e91f8d2b80001000000010001053dc7e5abf001000000000001010501ccb6edc208,
  0x6010107d4c4dcf5e69800000000000201050009f2b5ac9ba49800000000000400010302a5aeefdfd08a0000000003000001040389cf9ec7f5e500000002000001010478b4a2fba0ac0000020000000001050faca7cbf8ea000100000000000601029e8f8bb5e8010000000100000105098ef4e0e308,
  0x701000eb5a3c4e9af8d0000000000040101020cb6deefe09e9d0000000001020005000b8583c3a7a5ca00000000030001010305ce8eeb8bcb9e00000002000000050103b4e992ecaad80000010000010006000185dca2c0c1a800020000000000010505ecc3988be801000000000003010339a4beca8608,
  0x10700001ff7bfa0c6e4d30000000000050002011bb092c1a4cced00000000020101040011d6dcedfcf4a70000000004000001030c90c2ccdbc5aa0000000200000105000c99d5fbdaf394000002000000020103029ab784d5f1b60001000001000006003aaff997cb9801000000000100060002d1e9f3e58d08,
  0x600010170fde4e4febdbe00000000010106000001bbe5bffce5c8e700000000030100040052befdfbd9de9300000000040100000312e286ebf1b5f200000003000000040139baeccaebcfa0000002000000010500129984c2aef0c80002000000000005010298fba1cdca900200000000000101040eea87e8dbde08,
  0x6010100588cf38ec8efab00000000030201010174f7c5a981f1ac0000000004000103000594ecfbddea8b0000000101000600005e96dedbaed1d80000010200000005002befc98d8e89c400000200000101040023a186a88686000200000000010500038cda8adcf2d001000000000006010030b7d395e1ac08,
  0x701000022f08bfeb5e39000000000040101020006d7cdb7e294ed00000000050001010119b5bea6e2878e0000000200010500003bd4dcb7ff9300000003010000040012c995f496f4bc000001010000060000169784d385ef8800010000010006000003c784e1948f900100000101000104001ff49e9d8f8e08,
  0x10700000010fe85d59ba0b600000000060000010103dbec92c6ada300000001030004000008df83e5b8eecb0000000203000003000bdcb2a8e3caab00000004000002010104e6c0afd3f3a400000200000105000006e192a0e0d1fe0001010000000600000383fab4c997c80100000100000600001f8b85849cc708,
  0x6000101003190f8efe488c200000000060100000102ad9ecea5e8af0000000101060000003e9486958df2ed0000000401000101010be9cf888df3ce0000010200010400003b97d9c2fd8dcb0001020001000004000be882d28ab8bc00030001000000010301f6f7e99ac6d401000101010000040001cdbfa6b89bf908,
  0x700000100018ef0cf90f1f8cc00000002010500000001e9b3a8cb8f89d900000005000100010106bdedb5eff4a4000001030000040000498e95dbd499940000020101010201007dc5f68afc90880000040000010100020cf1dd81a7fbee0002000100000500002cbd8db7eec2bc010000020101020001099ba4cea8a1f108,
  0x7010000003fcba4e9f9ab900000000301040000001dbee5d499faff0000000501000002001fa094cacb8cf900000006000000010109cbfab4d4fc9e00000301000004000032dbb48fc7e6ac000100020102020000118bf593bcdacc00010100000600000020b9e79fb48bc401000001000600000005e8d68094849e08,
  0x107000000003fcba4e9f9ab900000000401030000001dbee5d499faff00000006000001010020b9e79fb48bc400000006000100000105e8d68094849e000002020102000100118bf593bcdacc00000400000103000032dbb48fc7e6ac0002000001050000001fa094cacb8cf901010000000600000009cbfab4d4fc9e08,
  0x5010200000003e0a885f5b1f0ad000004000003010000018ed3a9eabfcf9a00000500000100020050dcf7dca5cfde00000500010000010112d3d8ace4bea4000100000700000000029ba3d6f9b39fa10001020101010200000291a9fb84ca9ebf0200000001050000000f96e8d9e7efe103000000000104000011efc5bf9f84f608,
  0x6010100000001e1df93e6aaceb5000003020101010000039dce82fad4f8ba000005010000010001088bd8d18bfdbe00010100060000000001db8ebdc681d4e400040000000103000001a09ccaaea3f000040000010100020029bd96bbdb80f701020000000500000060e5f9a8e5eed202020000010000030001f5a6d983d3b608,
  0x7010000000005a0d8d4dcebd5f400000500010101000004f79be4ceeaccb400000501000100010053f09992e189ec00030000030200000003d0a5d4c298fda801010000060000000001bce9dba1f088cd01010200000400000051b6f1cab2baca0400000001000003000ac9edc0e9df94040100000000000003038b9ed2a3b49908,
  0x10700000000001cc9a690c781b8000006000001010000189ca4a4d4eca800000600010000010004c9868f99eef0000201020201000000378bb3f587adcc00020103010001000004a5f3fcfbebd000050100000000000214c1caa580c901010100050000000015c08583c68a8402010100000400000005cbc0fbdbffc708,
  0x60001010000000bfcabb588fbb70000060100000100000a8ca5ba9b9c980001010600000000001b9ae58bc08df40001060000000000010b8181b9a7ca00030100040000000006eda095f7fc8300040100000300000009e5a6d89881b30005010000000002005a94bccfa5d80201000005000000000da4edd9838fe508,
  0x60101000000000199d9f9a2cb8cb300010600000001000024b28984dde1900004000103000000002ddaf4a280efdf0005000001020000005698a2f0a1b6f00101000600000000007aaf8a93ac9bf603000001040000000021a9f789d2aa8a0301020000000002000298fba1cdca900401010000000000020eea87e8dbde08,
  0x701000000000045f98d8997bbfb0005000101010000002ae8fd9e9aa0f5010200050000000000299d9df29dc1800105000001000000010589d5c1919902020001030000000027e2bea0998798020301000000020000049f919cd6b2de02030100000100010070a190b79ab80400010000030000000189ddc3c8fcc908,
  0x10700000000000020dcaaefa2d58b0005000201000000000fabd3aa9fa9fe0006000001010000000ee4f2a7808ea800060001000001000002a1dda08be2ec0105010000000000017c8f87cb8d0201010400000000001cd8ea96c49c920400000103000000000a8af692f28ef80501000000000002000cd5e6f499cc08,
  0x50102000000000009f2b5ac9ba49801010600000000000007d4c4dcf5e698010600000000000100029e8f8bb5e803010004000000000002a5aeefdfd08a0401000003000000000389cf9ec7f5e504010100000200000078b4a2fba0ac0501000000000200000faca7cbf8ea050100000100000001098ef4e0e308,
  0x60101000000000009b0daf9d29dc801050100010000000002d2a3fcc787d403000401000000000009c2fd9bebb8ce040101010001000000759dec8a84d80401020000000100000c959af4fbd405000001020000000001b7f288d1fbdf0501000100000001005cabd881e806000001000000000102b2d2a4a308,
  0x70100000000000008f8a6aeaba1db03010400000000000006b3929fb498a504010102000000000005b1bc82d0a2d705000101010000000002eef7e6a8a2d20501000100010000003084c1c396d805010100000001000003f787d88ed406000100000000010017c2c2cfe80601000000000000013dca8bc308,
  0x10106000ea9b38894e3e682000000000000010400030dacaac0e4ec8dc000000000000100010501029ffd939cf5a0ee000000000002010000050383b4d785aafcd20000000001000002020301bfd3c4b7b3aabe00000001000000000502178592dbff96cc0000010000000000040301e3f5e0ded4e4000100000000000101050aa39af5ca8f010000000000000100061aad898f8109,
  0x601011cf1eddd958cc8d10000000000000201050025e6c1f5e18cb1e20000000000000400010308e0d29fb7b098bd000000000003000001040c97d98291b7ade8000000000200000101040483ca94a6f3f398000000020000000001054bde87a99398f0000001000000000006010ea6ebb0afd1a00001000000010000010564ecfbcec7980100000000000100010502bc84fa9ae809,
  0x10700002db097c489feee8d0000000000000500020125e99ce8e798bbe70000000000020101040019abb3baaba0d3a30000000000040000010311d38f9fbcdeefa40000000002000001050012f3bbcc8fcdee830000000200000101000403f2c79eb6b5a3ee0000010000010000060001848af2b9d1cdd4000100000000010006000a9ab8c6e3fda3010000000000000106002cef88b0b6dd09,
  0x60001014a939a83ee8ee6b6000000000001010600000184d4c2f6a88ebcd50000000000030100040038dbcca38ae7bee3000000000200010104000cab91f7c4f096d20000000003000100010321f387cbd5eee3c0000000010002000005001fad98c9d4f2b8b80000010001000001050004e8cac0b9c6afa80001000000010001050037a19f919deda6010000000000010105000299df94c5cefa09,
  0x701000029dd8fa1a5c4a2b3000000000005000101012ad3e2aa8badd2ad0000000001000600000115b6ded5cffe93c9000000000102020102000195829ff4b7a1e3c80000000101000006000046b28a95e39696f90000010100000201020104fcbe9d8e9eba8b0000030000000001000402e2e9edcad4d1fb0001010000010001020201e3dc85dce7aab5010001000000010102020bf098d6fdc6db09,
  0x5000201000af09a80cc88edd80000000000060000010151c0f2a9d4c8c2870000000001010402000001fad49484c8d2eed7000000000400000103002dbe839c97bab3ba000000030000000203002cc498b1e6b2faec000001000002020102000df0bda79e80959c0000010100000006000015bcacffeca4eec80001000001000006000004d9dab29183c7ff0100000000010006000023c7f585c5e7c109,
  0x6010100006fb59caa95affaaa000000000106000000013af69eb795b9ced6000000000302010101000280faecdb9abdd3ea0000000101000600000001b7b0aca692d896f20000000300000104000031d4c0fcd38c9fc8000000040000000103000aec9389b8c4bea50000020100000004010043a7bdc5c2c9c7d40001000101000005000016d99c98f798e786020000000000000501006ced85f2cdbfdd09,
  0x701000000229b8ab0d09e82870000000005000101010065f3a0ca9ea8cab0000000010006000001005bd4c2e09392a4c80000000101050000000119bee4fe81e5d5ff0000000102020102000002d1c1c894b298c7fd00000101000006000000019cececf9bf8195d8000004000000000003010aa9e3bcf1dfe6df000300000000000203000cbe91aef7e5beb1010000000104000001010392e48ef9e2b69d09,
  0x600010100002ca6bbc1ada6a6f3000000020103020000004e94c4aef8e49787000001000007000000006097d9f1dcfdf8000001010104000001000bb9818aa2fac1bc000001020101010200002994d899cdbdf09f00000300000004010000079eab9dcbaab4f70000040000000200010165e6eac49dda92000101000004010001001791c0f99198ab98030100000000000000046bc382e6ffd89209,
  0x6010100000014a2e6a095a3ecd8000000010600000001000a8e84c1b6c6a18e0000010006000000000101a1a4c49abfc49b000001010006000000000385cea2bba6a39b000001030001020100002cedf388f7f892d10000030000010400000002dce7b9bccbd6ec0000040000010002010001f0bdbcc5c5e0c70001000001060000000011d894b6fc98a3b3010001000102020100000289f9baf08e9dad09,
  0x107000000000003e6bdfbcbb4c995000000060000010100000f9da2fcf8ababd8000000060001000001000693928dc8b089db0000020102020100000041e9f1ececdce6d6000100010500000100000af491ffa4c6c3d9000100020104000000000bddd7e5f298c1d70003000000020300000006b99ff1f7bdf7da000300000103000000014290b7f99fb8d50100000006000001000006b2e8e097d6e58309,
  0x600010100000022f185dbccf1afbe9f000001010600000000001fb8f3b4bee7f49f8c0000050000000201000013bfd792b2dbc7c0eb0001010102030000000037f7d4d5e49490abf50003010000000400000003e7bfd0dbe5beb9d90004000100000002010033dde08fb5b09fd9030100000000000400000180c186eee5ffc5c5040000000000010102000282aeb3f6a8bec0b3040001000000000000030e99bfd2f5d7d6cb09,
  0x701000000000001c5f6d2bde693ebc20000030104000000000063e39bc7c5868f86000005010000020000005decd5e8eca9a3a3000006000000010100003293caa1acef8da700000600000100000100079cc9aad8cda3d90003010000040000000001a2ebe99b9aeccbe3010100000600000000006f84eab3a196f6b60300000100030001000004959ad2f2c6d6950400000000020100000136d2b3ecb698e709,
  0x10700000000000003bab1cee4fea3e10000050002010000000009cdbededea59ce00000060001000001000003d4b4d9a78dc5e400010500000002000000098c9ee79fabefa600020102020100000000239adeb78099ec8e010000060001000000000da8e4f8c8b7f690010101000500000000000683ad9bc0edf6e70200010301000000010036fbde8994c3cf0200010400000000000102eef8dbceede109,
  0x6010100000000007baef7b9cda5c3fc000500000102000000002997a8e883ed96f4000501000000020000000ed0e9aaf4b5b3f80005010000010001000004bfbd80b5dba3d0000600000100000000010286faf9c9c1940101000600000000000053a4f99ff19396e5010300000400000000002c9fbdae90a4ab99030100010003000000000bee93bdb780ece00500000100000000020019e4ecb2daddd609,
  0x70100000000000063a0cbd992cba9990005000101010000000045dfa0f5a5e4aace0102000500000000000036efc1e493f9ce85020200010300000000003793dec185e7e3bc0301010200000000010013d0b1d6f1bfd70302000200000000000156a4add3a4a9040001000003000000007e9099d697dae00400010100000200000007bee1ce99f0a7b6050000010000000200007f80d0c1a294c209,
  0x10106000000000000000be9d1adbe92cdfd010400030000000000000dccceafcdfe8ffc01040200000100000000019ab9aa979584ee0203010002000000000006eae5d9bff4f7f10500000100020000000057dbefe3c9dfb80500010000010100000038e6c5beeeb2d40500010001000001000005aec8a291eebc0500010100000000010025e8eeadbad90501000100000000000176c1edea8709,
  0x6010100000000000005e4cdd3c6f2b3fd0103040000000000000008f1ff93b5fdd7e2030300010001000000007fe2adcfccf1d4030400000000000100000197f995e9e3980400010300000000000004c2c5faddeca1c70401010002000000000002e2a295e2c3de86040200010000010000000fae8cbdaa8f880600000100000000010006ece7a3dc8a0600010000000000000111c8dbb4d609,
  0x501022ee4bb9282f6e28596000000000000000101060039a6aeaba6c4efcbc7000000000000000301000412b7c7c2dfc3e5828b000000000000020100000512b5d084f7f4b8e688000000000001000000060107868691bcacc6daa0000000000100000101000577eb968df290e89000000001000000010001050af5addee89afcc0000001000000000001010553c4e992e09ca8000100000000000001000602fae7f387deb001000000000000000001060684ffb68dc80a,
  0x601012c8ef487e99c98ccc70000000000000002010500408e999aff94aaabee000000000000000400010305a3b182b6ec90b2930000000000000300000104148a85c7e791b5cbb000000000000100020100040e8398f38eaca1cea0000000000200000000010501919191caefc2b38800000001000000000006012097b9d58dc584c0000001000000000101000502abde9cf0c0fba800010000000000010001050cf6a1f7d8acb00100000000000000010105208cc0b4dcc80a,
  0x500020122e0ebf5b1b9a0ef85000000000000010104020032c892e2baa58ce185000000000000040000010305aeedc3ebe9f8dde7000000000001010003020122bfbb90dcd3eeaddc000000000200000001030203f0b9a2f2dbb090ff000000010000000103010201998cdd98d1caf6b8000001000000000004010209d6e8e7d3e5d6b3000001000000000100060005e897bd8ff1f488000100000000010100010476f4c0c1c9d3da0100000000000100000303039adb91cefee70a,
  0x600010157deace796949c849400000000000001010600000180e8eeff84addae5d200000000000004010000031ae8f89d95bad7d3e300000000000201000005003edefe96aadfeed9bb000000000003000002000304beff95ec82caead200000000010002000005002488eabcb6f2ddadc6000000010000000006000106b5ddcbe6ffdea0d800000100000001000105005ffdc782a9d6a4ef000100000000010000060006d2aef180e4d0f201000000000000010006001abea88481baab0a,
  0x70000010992a7e6e3c5ae8999ef000000000000040001030007c3979081f481e9caa2000000000001010006000009efb5d0d0c3aae1ffa4000000000102000000050003ccf1f9ebb78ae4deba000000000200000101040014e997c5beb2daf9b800000001020000000100044081bcbcdb8dd982aa0000000200000000010500198e8e88d6f481dfac000001010100000000000511cc9eeea5d6d5f5ae000200000000000100000555f3afbae3efafef010100000000000001000506abcdfbabcbbde60a]

/-- The triples `(n, b, a)` of part 8. -/
def enumC8 : List (ℕ × ℕ × ℕ) := [(8, 40, 13), (8, 40, 17), (8, 40, 19), (8, 40, 21), (8, 40, 23), (8, 40, 27), (8, 40, 29), (8, 40, 31), (8, 40, 33), (8, 44, 7), (8, 44, 9), (8, 44, 13), (8, 44, 15), (8, 44, 17), (8, 44, 19), (8, 44, 21), (8, 44, 23), (8, 44, 25), (8, 44, 27), (8, 44, 29), (8, 44, 31), (8, 44, 35), (8, 44, 37), (8, 48, 7), (8, 48, 11), (8, 48, 13), (8, 48, 17), (8, 48, 19), (8, 48, 23), (8, 48, 25), (8, 48, 29), (8, 48, 31), (8, 48, 35), (8, 48, 37), (8, 48, 41), (8, 56, 9), (8, 56, 11), (8, 56, 13), (8, 56, 15), (8, 56, 17), (8, 56, 19), (8, 56, 23), (8, 56, 25), (8, 56, 27), (8, 56, 29), (8, 56, 31), (8, 56, 33), (8, 56, 37), (8, 56, 39), (8, 56, 41), (8, 56, 43), (8, 56, 45), (8, 56, 47), (8, 64, 9), (8, 64, 11), (8, 64, 13), (8, 64, 15), (8, 64, 17), (8, 64, 19), (8, 64, 21), (8, 64, 23), (8, 64, 25), (8, 64, 27), (8, 64, 29), (8, 64, 31), (8, 64, 33), (8, 64, 35), (8, 64, 37), (8, 64, 39), (8, 64, 41), (8, 64, 43), (8, 64, 45), (8, 64, 47), (8, 64, 49), (8, 64, 51), (8, 64, 53), (8, 64, 55), (8, 72, 11), (8, 72, 13), (8, 72, 17), (8, 72, 19), (8, 72, 23), (8, 72, 25), (8, 72, 29), (8, 72, 31), (8, 72, 35), (8, 72, 37), (8, 72, 41), (8, 72, 43), (8, 72, 47), (8, 72, 49), (8, 72, 53), (8, 72, 55), (8, 72, 59), (8, 72, 61), (8, 80, 11), (8, 80, 13), (8, 80, 17), (8, 80, 19), (8, 80, 21)]

theorem certs_ok8 : checkAll enumC8 certData8 = true := by decide +kernel

/-- Certificate data, part 9. -/
def certData9 : List ℕ := [
  0x701000004deafd98edfcef5eb8d000000000000040101020003fa90b599b992bccabd000000000000050100000201e0a9f281f3fbcca8ba000000000003010000040002fa90f1a8ffb8f3dd86000000000101000006000004bc83a8a4ffd6908b8800000003000000000100042c8d9afed5d3b6f0d0000001000000000106000007f79faa95b8c5d19200000200000000010004010685d8c8c19284959a000100000100000101030101e5e4e48fccf5e394010000000001000102010209a2eab8a986ffde0a,
  0x60001010004ee8cadd3fedddeb8ae000000000001010600000006b4fbddb0f882f7cc8000000000000500000002010295d1e8e2db83b9f3f6000000000201000005000003f08aab8abbfdc2fedc00000000040000000003012d94a6c6b2e380bac700000001010101000103000c8be1fd9c9d95a4f600000002000000010500000181c6bd9495f285cdaf000001010001000100040041f2b89ea893ebdab9000100010001000001040007baebe6b9d6e391be010000010001000000050030d2a5abc1c2f09d0a,
  0x7000001000197ece4d4d6c194cbef000000000005000001020029aad1d4db909d9bdc000000000005000002000143ddf7d3aa9ab4b1b1000000000101010401000002e8cbf7f89dc899caae00000000040000000103001e87cc8cb7dfd2afb100000001000201020002001a82c5cba492db85e8000000020001000005000030aaaec5fdb6a3d8d9000001010000010005000021a8aab0ec82cadb9d0001000000020100020200049aecc4d1d8dd8cf601000001000000000600001ed1fbefc887a6d10a,
  0x5000101010017d49ddbaff98afcac00000000000600000001010e9fd7f1bcf6a8aba000000000010006000001002ab18dd8b6aab7ec9400000000010202010200003e849fe0d4d2a4c6b300000000040000000301000ad1b3a5e5f19ef5b100000001000103010200001799b5e5a3bee4ddc900000001010000060000002ef09becf6ebe2b59f000001000001020202000010d0808da69fd2eba9000100000000010600000002ab96aec8dbc38ade010000000000050000010112f6da98fcf4a7cd0a,
  0x102030101000009d0fdb6afdecaadf5ee00000000010500000002000198adc881f8e2d4a6c900000000050000000101014eeafb88bee2d0a3ec000000010101020200010001a2a594fef0f3e2f0e70000000300000002030000018ca0d3e6cc8b9287c1000000040000000001030001c7d1b6be8db488bb00000100030000000301000381a2eef8b7ae8bb2000001010000000600000001cec3d3a0dfa6bc8dca000100000100000600000020d8e9ca94f9e1aec802000000000000010500000192f580828cb8f7b60a,
  0x601010000000dc783ccb3d289d6af00000000010600000001000b94f2e3e1a7e59ab7000000000205000000000101e6aba5c0b0f8bf96000000000401000201000020a1e996fabeadeea800000003000001040000000eadddc4a5b9d3aef20000000301000100030000099dc3e98eb6c182d2000001000001060000000018aaf3dce2a488a8de000100010000050000010004a98ad6819e89eaad00010001010000050000002ac481ecc1e59eb7010000000000060100000033a089aca2defed60a,
  0x701000000001fc6b5efcde4a1bde4ed000000000501000002000013e693d0889b95bf89a1000000000600000001010009f5c49bcec192c9aed200000003010000040000001983a3f598f4e3938deb00000101000006000000001ce3f59ccaf2f39dd79f000004000001000000020132bdb0d89e8ea6ff94000100000500000000000215f8d69b83e7ffe2a3000101000100010400000006d892e2e6e78bb88ead00040000000000000003011f88fce4d899cdd1ae03000000000001000201011fe493e8f6c4dcbd840a,
  0x6000001010000219c9ada98999e9700000001000601000000000497f9abfe96f9dfb200000001030102010000000884cedd9ec0bfcb840000000500000001010100019882a9f0f69fe9f600000005000000020000010ebaf4ffe8a48fb10000010003010200010000028fb0efeefdf1a3f4000003000001000400000001a3c3fa92e7d9d8e000010100000006000000005fc48e8dfdc89fd8000201010000000004000041d1aea28dd8cc8f010002000000000500000017ebfae6c0fdd5d10a,
  0x20202010100000002edb1faa7de8bdac3f5000000020301010001000004f4d4adc795ceac9ca700000006000000000001010882b78dc5ff8ff4e6000001000007000000000002d7b09abc9cdbfbe9bd000001010201020100000009b5bfb5bcb2efa9afca00010001010202010000000296d5a9dac7f2fca4a3000300010100000000030021d0979893db8f8f8f010000000500000100000102a9c5b99cad85fe9d01020000000000050000000a9dd28e8284a5b4f903000000000000040001000ba7dedcfcdc8dabaf0a,
  0x20401010000000014c78d9ad0a9e4b7d2c8000000060000000101000002a1cafdc4cdf79a8ad1000003010000040000000003fed7a8fa8f9eb8fdc0000003020000000300000004e2efa5caaaaedfd7e500010100000600000000000883fdeb87b1a1d5adbf0001010005000000000001068fc5aae0c2afd2a0000104000000000003000005fdb9ceeb8aa1d08500020100000104000000000199f2b8fde6c6fac3fe01010100020100000101005797c49b8d9a83d1c003010000000000000400002981f38cde87f0e8a00a,
  0x107000000000000029fdffad2f7c5a9fd82000000060000010100000068fed592e4b9869f9a00000006000100000100006198cfb09ad6c6dfdc00000202010102000000000481d6a8babb98e2cdb900000400010100020000006cdb9df8a592e98af400010202010000010001000dd582df81dbfeab8800010202010001000000016ed3c0c39f94a2cc000200000105000000000001b489c4f782bdcda9c9000301000001000300000018c3f4b3f59ba29ef2010100000006000000000054949a9cecabbb95cc0a,
  0x1040101010000000002a081aee986cd98fbe9000001050100000001000007cfd7d1b7b3c5b89000000400010102000000002e9e9a96c7c4d9feb4000005000002000000010003b1dabdbed0e3f4c6000006000000000100000118d4daaafbc7b889000100000700000000000077b4ac9ae3bfedb9f0000201000005000000000058e2b5ccfeb0c0a59a000202000101010001000006c3c0b499c082e59101000201010200000100000cd58a88daaaceb8d4010004000000000300000029ed94d6bb939da4950a,
  0x60101000000000002b99797dae6aef287ae000003020101010000000003f6db82bea2dbc9eb84000005010000010001000025d3d6ff84d4bdc5fc000101000600000000000002aaebccc2bfd8b3a791000104010000010000010004a1cff1b39fa6aec800030100000300010000001ebba782fdd283e49300040000000103000000002c93a0afcfafbfb7f001020000000500000000000180d8d78094eaecde91010202000000000300000037c5f0b8ecbcc5a0ef02010300000000000000020df2f8b180b7d6f60a,
  0x1070000000000000008caf7b7eda3eaeb9500000600000101000000003bb2eaf4b3edd28ed2000006000100000100000013f9e4cbcba8e58298000106000000000000000101b2fbdde9dfc48300020102020100000000000192d3f6c2bab5e2d4e000020103010001000000001b90e9acbb92c895a4010000060001000000000033a3a4a38bd8dfc09a010101000500000000000025cdbbded28affa4f702000103010000000100000382b6e6b1a5aa9de7020001040000000000010022d3a1b18acad3820a,
  0x5010200000000000058f9b9dcf1a8b0c9f100040001010200000000000ea7a69a97acd7bd84000500000002010000000021a8bdaca8a4e0a496000500000101000100000006e3ad82c0ccf38598000500010001000001000073e2bdf2b1a8a6f7000501000001000000010009948ad7938b92a2000600000001000000000129dbf7b1bf8c9301000007000000000000002db7c5efdb9ac9b3f402010000050000000000000ce6adecdf98a4c8f8030100000004000000000002aaa7a59390c48dc50a,
  0x60101000000000000018b89d4a081ce9b9dca00010600000001000000003593e0a394a2aba1b8000500000102000000000051eeafaefeafc8f7ca010006000000000100000009bafcb9e8d0ba87e00101000600000000000000018dfcb7aec6b0a6b2df010300000400000000000051deb09788fceceec903010001000300000000000dd7efafc1a58afcf4050000010000000002000046c8ffd6df8face8050100000000000000020004f2cafbd894a0d405010000000000000100012784a085f4d5fc0a,
  0x204010100000000000062accedf8df2cedef800060000010000010000000286bab285d580b8e000060001000000000100001ac7b7ace1dfa49c01010401000100000000001a858fd981d3dad3ea01020005000000000000002ebab1f7cd8af7a29301020301000001000000000da68dc0e4ddee95d8010400010002000000000010c68fb48ecbdefda3010500010000000000010001cbeca5b9c7b488010501000000000000000105c089f9d0c78c030100000400000000000014c79cf5ce9b9ac0800a,
  0x50102000000000000000b90c48abedfa8e2c0010106000000000000000019b18cb8d4cbb18b82010401010100000000000034daaeccbedddcd5ee01040200000100000000000ca2e5e4dcc6ddb4bc03000203000000000000001ad69da0b1fea79792030103000000010000000001fdfdfee3839499ae03030001000000010000001c94c2babbecb3f805000101000000000100000286a2b9a2b8ebf305010001000000000001000ba7bdd8dda6ea06000001000000000000011c8af8ae90ff0a,
  0x60101000000000000002681d9b2afc4aca7ce01060000000100000000000695a5afa4e6fdeefc02010500000000000000002bacdaacf1abc6d5df030200030000000000000019ebd790e6ffcceb8e030301000000010000000068ede3ac93eedb8e0401010002000000000000108ef684a8f5f1d9a7040201000000000100000009c6d882fb97ccf80501010000000000010000498c9c80b498e3060001000000000000010002cbbaf4d6e2ca060100000000000000000105a4afbfabef0a,
  0x6010131adcd838e82ddf5f9fa00000000000000000300040141c8e28fceb994b0b38600000000000000020002010321f698aed7898085c8ee0000000000000100000106000dfbfde1ba9bc698bcbe00000000000100000000070024deadf7bba1b084f200000000000101000000020402cabae798ccc5a7f6a00000000001000001000100052dbb98c7bcd9c1dfda00000001000000000101000503f8aa9e8b9df8f2fb0000010000000000000004031d91e6b7a1cba09f0001000000000000000101050181a6aefcb1afc50100000000000000000100060284e5cbacb0890b,
  0x7010078ffd8cedefbb8cab5d5000000000000000004010102019fb1bac8f6d2c1eee0e800000000000000020001050062dba090c2848cd2aeab0000000000000003010000041bc999b99fb2b9b68fec00000000000002000000050128a5d680fce4edb2be9e00000000000100000100060010c7cbd6a8e1c7a182e4000000000200000000000105019bc686fafcf1e8bfda0000000100000000000301031ffb8dda92d380b79600000100000000000000060102989b9edcbaa4ecfe0001000000000000010100050bc1ffc195d7b7aa0100000000000001000000061bc4aff685cf920b,
  0x10700000286bbeed8b6e7b990fb8b00000000000000000500020101ea85ac8ba7d39ee8cdac00000000000000020101040029e6ffa9accfb7d8a2cd000000000000000400000103018b93d7e8b3a789ced6fe00000000000002000001050076b884e392f8d8c9e3b600000000000100010001050038dbde9db9dfd3f0ecf400000000010000010000060009d9cdb4d7b2efb8b1c40000000100000000010006000194d2a486ede0a2d8ee0000010000000000000106000beec3e3d9f1b9ba9600010000000000010000030348dbf8f08eb9999201000000000000000000060101cacdc3ead78ffa0b,
  0x600010104e18187abcdf6dc8ff69f000000000000000301000400059ebbf5d2b9bdd7b8d0cc00000000000000040100000351caacefc28ac2aaa5c400000000000001000007000005f0f68df9a8bbb4c9b6fc0000000000000201000005005c81a099a4deb3ffe2b000000000000300000000010455fff8acebc594c780ec00000000020000000002010319afd0abb49cc083b1e900000001000000000103020106fea58d8a96d2a1c1e6000001000000000100000600528ae9d9fd90e9dcce00010000000000010101000404c2d1c187d188b5da0100000001000000000001050ebe89f298e5f3c20b,
  0x700000153febe85cd9eb685f3cf00000000000000040001030001a8cd99bcf8c2bcacb09800000000000001000303010036c693f5f6abd19db4980000000000000200020201016b8cb694fae5e1f1e3c100000000000100000106000059c2c1b288d8dcbddfcd00000000000102000000050003a4a2f9f589c98683d300000000010001000102020114e3b6f8d3c7d6ddc0a000000001000000000006010003a0e3add3e488e8b8f00000010000000001010005002bc5cdaefb95f7e7b000010000000000000004030002ddb1f7eec0b5df9001000000000000010000060009faa6d5ff87a1d00b,
  0x70100000cd1fb95fdfcc2a4f6e9a90000000000000004010102000ad7d3b1a2f6cb91f5d5d100000000000000050100000204c598c0a7afc6e08f9cdb000000000000030100000400088dfdb1f1a0f4b0ebdcb50000000000010100000600000c92c1c69bfce4c2f18de100000000000300000100020220baf8d5b2ecc791cef5000000000300000000010004018b968597c998c0e8e38000000002000000000002030124f7c9a0acc485b1bbe000000100000000010102030008db9cb89aa18f8789c00001000000000001010202014ef6999fb2e4dad8c001000000000100010001000402c4fbcfb5f499eac00b,
  0x10700000007caafebf59bc5f8eef6d700000000000000060000010104fcbaf3cf81c1dda9b8cb00000000000004000001030004dcbce8dc8e83fdced1cd00000000000101010005000004c3abc9d181f5a0a9c1c80000000000030000000203005afcae87f590f6bdd1b800000000010100000006000002d1909498eac5dacdb4f40000000200000001000005001ac7bebbf590c6a382cb00000003000000000000010404cbd3d09bebadbf85c000000200000000000100040104b6a1ffe6a4d98c87ef00010000000000000106000059f18a909e9aaac6aa02000000000000000001010401cfc2fa81d3cbe0f90b,
  0x60100000138becb84ebfaaba2c9c700000000000001010600000005e0fbe199dff3db8ab200000000000003010102010056d8849ac3ccf6f6baca0000000000000400010200011085bec186e8b69ca9b000000000000101020102010002869f8e95fea297bbc4e000000000010000000601000052f4c6dda4a9b18b83e000000001000000000600010012acd6ffd4d0c0afc79000000100000000000600000102dac3b2a7e1f4c1e2d00001000000000101010201011ed6c5c0afd99b9cf00100000000000001000600005dda94df8d8a81ca0200000000000000010002032092e5a3d092b7b30b,
  0x70000010074cb9c8c80e3ba9fbbefa400000000000003020101010001ebfaf182a8d498fadfc0c600000000000101000600000001b59cb680bef6ac8a87ecfd00000000010200000005000077bae0bfdcadefc7eea4b600000000020101000000040002fad4dfe292b0bedbc6eb00000000040000000000010362cad9b88796d4c2c3b60000000101000001000500000cea9ee789e4d0dbde95d00000000201010000000000040cc8d3c4a2da8d9980ca8e000002000001010000000004038e8ccc84d780e8f399be0001000001020000000000044ea2cae9f69a98fba89402000000010000000000000501dfeafee8c18a8393920b,
  0x70100000018f4c9b2ad9c8bd396c3ab0000000000000501000002001291c9e3fe8699afe7bdeb0000000000000600000001010480d6b39dccef97a192e300000000000301000004000013b0d0b6fcab9abeae85a8000000000101000006000000199dcce4a9d7d2fe96b0b900000000040000000001010201b19e90a0b2a7958aabc000000001000002010103000008e7b5cbebf7a8d9b6b1a300000100010001000005000001ccb1b1d6f7d89c988ab700010000010000010005000003889adda6bda4bed0ba00030000000000000000010406b1e789e3cd8b8280c1010000000001000101030100018cd8d6a5bfef82fe910b,
  0x6000101000010b397adb5e498c5e385a800000000000200050100000014d5d1a0d3c5b4e7e8c9fe00000000000500000100020001c3e396ccef90b4e9fef500000000000500000101000101d988f0f5d891cbbac7f800000000020100000500000004bdfbbab980bcc0be9ec10000000003010000000400000381e6a5e9d8acb8ebf2ea000000000400000100000300038b8bdef7b4b1ae87c5ba00000003000000000104000002d0e1c6cf84bde086c2a0000001010000000006000000029d94d5cd9fd5a989d2f800010000010000000600000025d4ebf4bbddb0f2e4a801000000000100000600000002a1b59f92a5f0db99c80b,
  0x7000001000046b6b8bf96aceae4a1ca00000000000302010101000069b3f4bb93c5d885d1e300000000000500010001010020e8cfe3c1d9ce8997c1000000000005010000010001039d83c4c7fafbecaca400000000030000010400000063c9a2cdf7a5afb896fe0000000100000106000000005693878ea193bc9093eb00000004000000000100020103f7f699edbed1a488880000010000030001010101001a9a92f098b78af1a48f00010001000101010100010101b2adb9e5bbeab5abe300010002000000000104000002b4a9cefab88acec5f2010000010000000006000000208ccb97f2b6bf80990b,
  0x701000000003ec6dde6e0a9a5f5b5db9400000000000501000002000019b5cdf39882d599f497dc0000000000060000000101001bbeaab096bec5b5c9b8a400000000010500000001000101d083c1b2acc2c494a0d000000000030100000400000032ceaecc9ae49aa788ebcd0000000101000006000000003895efe9d2f3cbb4dfa28100000003000100000103000004d6db8998d8e0f6d7c6e80000010100010001040000000d9cb6e2fbf897b4fdda8b00000300000000010004000002fc9adde3abc2da9cdde30003000000000000010300010196a9d2acedb7dfc59e940300000000010000000000040af0a0a8e294b5d989e40b,
  0x107000000000007bbb8e38f88979ba58fc900000000000600000101000006bafa92cdf08af8cdb5860000000002010104000000002f9795c1ef9a919ec6bf00000000040000010300000005d5cce2a2d0e6acb5fea00000000005000000010101001ca6d3ed9fefcfeef7e4000000000501000000000002108abe9bcfbcabdaef840000000101020102000001000298aae186f0c4dbe0f98400000002010001020101000003eaf685e089a8aeffb1ce0000010100000006000000000485bf90acbdbadbc290880001000001000006000000005aa4cec88497ee9993d80100000000010006000000000794bdd89491deb3c1b80b,
  0x600010100000007a1c1e48d8788b6dcd9bd000000000400010102000000058db18ea4eef0ad8296e80000000005010000000002004e9bb1e9f39a9cc999d200000000060000000000010110b999b7959e84e7f59f0000000100000700000000000683b8c58ccdf1a49d82fa0000000201000005000000000396a282ef8bd7dec5f283000000020300000000030000019297cc8b82c897a5a4c100000300000000010400000020eeeabcd3b0a299fbbc000003000001000100030000018191a186b8efaa98e39200010100000000060000000072e9c7bbc1d2f0c2f4a501000001000000060000000009fce0fcb0afa3f294b90b,
  0x1060000000100001784fed5a4c7c8f191d800000000020301020000000016f3fc98b9b2fcefecd700000000060000000001010003c0a19acdc8e9a3b3f200000001010006000000000026bec6d3b0d1edb191870000000104000000030000004bb284f5dfe4c4d3e40000000201010102010000003290fbb29da794f280890000010002010102010000002eccf6c4ebd5d39b8f9a00000101000400000100010003bac09bb6b4b8d8f29800010000000500000101000009efdaf59fdbac9fc39400030001010000000000000319e5c1eef092e9dee60200000100000000050000003fe5cf9fd69f96c5bf0b,
  0x70100000000000492fb988092f3d1e2b4e20000000005010000020000005bb9bdb4d0e4e0bdf8ac00000000060000000101000002a59fc0ddbcb6cdbae6fc0000000006000001000001001da7b8fce2d69883e78200000003000102010100000003b2b0cae5d4918fffc98e00000101000006000000000001e88faedeb182859bb1bd00000101020000040000000003cd8c99c3bbaa9ea3c3cd0001000001000600000000000199858cc8fad5a19ec6ba00010300000000000300010015eda6df9fd9bbdfe4920100010002010001010000010487abbee0dfb19d98a4020000000101000004000000078ae78e91ffa6c783ec0b,
  0x6000001010000000a8dcacf99bcbac9eed5d200000002010202010000000006f6e1ff8eefda9cee9fd900000002010400000001000062bee2e29e94f5c5dfcb00000005000000010101000001dafcafadf18182c39f850000000500010000000101004a9b85818aa3cfc988b40000010100030201000000000fe09e958dddd0f9f0ddf800010000000600000100000001f4d482b1b3ddd0cea3f5000101000000060000000000029ab8d2dacf85dfc5b5880100000100000600000000002bbc9a9888deb1b6cdb301000101020001000001000105afa8a18b98d4eb958401030000000000000004000011a4fecabad6a1aaeaa50b,
  0x600010100000000019d9ad997a583bde3a0c6b700000004000003010000000050aade8fe1d5c2e2bceb8f00000005010000000002000010c393dca181c4e9eec98e0000010000070000000000000195e693e2c7d786c4f89e8800000104000000010200000047c08d90af95bcc6a380a600000105000000000000020002a0b897a4c0c38db2fefa0000030100000004000000000aa4b599c2d183dadad9d800010100010005000000000048c0dfadaab7fdf2c8cad401020000000000050000000008e7b4a9f39eedd9d9e7ac04000000000000000003010041b39486e593f6f9c7c00400000001000000000000030e8fb189cba199ef94ec0b,
  0x700000100000000028cdde3ee94e0e0f9c8ae0000000203010200000000000de0bdeedbb7ceac858eec000000060000000100000100198df2cdd2bea0ccc2f000000006000001000000000101c0f8ea8c99a0bce6b000000101000600000000000006c9d0bbc1e5bd9f8b9e8d0000010203000001010000000296d49ce2d583b4bcc2c200000201010102010000000007f3a2a981b5db97b69eac00010102000200010001000001be8de3de958e9bb18cd0000201010000000400000000018a88d2848fb285b4ecb900030001000100000300000001c2fef1b398ace2ab9a9a02000001010000040000000048add0a79db0c3e8eda80b,
  0x107000000000000000ef9938a89daeefdef9de200000006000001010000000008c0ea8ad5cb82c9fecfbf00000006000100000100000005cddaa0f0fdae8f9cc3a600000006010000000001000001828e8ef8e4c9bdf2bace0000030101010101000000000c8ebcd5bdbff5bcb8ddd500000400000103000000000008fc8ee2b1cffe8190faa80002000001050000000000000984dfd3ff9cb98c8dd2cd00030000010004000000000001b1cdd5edb8b5d8e780ae01010000000600000000000004a4dbe4bae2e5fbb1f1f40200030100000000000000022ce48ae4bd898494a104010000000000000000030004dbead7cef9c48ee3de0b,
  0x6010000010000000002f28ecdb1eaa7d8cb9bc000000101060000000000000004f8fca7e78ffaa09594ec0000010500000200000000000585fce4f8b8b8d9b591a10000010600000000000100001e8ec180f7d5ecb7fbac00000303010000000000010002faf5bbfc92b5ceeaa400000500000002010000000002f9df82dcc7dfcbbc85c800000501000000000200000032d0d6bd83cdce86dd9d00000600000001000000000110f79fbce2d2eecef400020100000500000000000006a1abcfbc88e0ced5f8bc00020101020001000100000052c4b88bd398bbf8d5a201000000060100000000000002c6f9d9ef98e494e3d9ac0b,
  0x60101000000000000088ac6d18cb2a2889fdbac00000500010100000100000001b9e4b0ecc8ef8be1c092000005010001000000010000159fa9bed6b494f2f6b000000600000100000000010002b6cc9fdbe2f7a3d4ae0000060001000000000000010cbfddb4f4abaad1e600010201020101000000000014df9affbeceba8dcae88c00010202010100010000000006c7bc8c90bfe380ffd5fc00030000010400000000000046ae86e5af9d91adc5d3000500000100000000020000038ad0b7ae8dcbb3c08d01000001060000000000000002f4e7bf848082e1e9df8202000100000500000000000001c3dea4abe6b0e7a8a5940b,
  0x7010000000000000007b3b082e0f1acd4ec93e900000401010200000000000006a599fba3b1a9f591b0d30000060000000101000000000381a4e09cb0cfd5a1cee00000060000010000010000004cb988f7b4a89883cfd00000060001000000000100000a8ea991e9e694e4db9000000601000000000000010066dcd4dbd9b0b0d0b000020400010000000000000103daaba996889aeff000030100000400000000000003adddbdb081e2b694d0f000040001000003000000000002b7c99593abadcb97c9e401010000060000000000000005ddebb2aea3f9baf589a601010201000102000000000013d2d095db92bf8bddea0b,
  0x10700000000000000001c82aba3e6a5d2e1ece9b000000600000101000000000015d0bccefed6f792f3e0b300000600010000010000000003aada8cac8a989cc8b00004000001030000000000000feafeb2af8da8e6a09feb00040100010001010000000002eba3d9ebe089da8fecb5000500010000000101000000018c85b0b5a8ecd4b69d9c00050001010000000000000104e88aaec8eefbd1f400050100000000010001000010c2a39ff1e48f9adfac0101010005000000000000001896bfe084a297f2f2dae40103010100010000000001000195d08ac3c2f9cbf7e404000100000000030000000059bab7a5cb94f3c7c0c90b,
  0x60100000100000000004ef988c8e9befdfafdc00001050000020000000000003089f5ca9f88b2c39c990001050100000001000000001689d2b098e49493aca200030100040000000000000001b0e389a6c88194daac9500030400000000000000010002f39d87adb4b98d8900050000010002000000000009ea8982fa88dcfac1fd00050001000100000100000003bae9c8c182a9aefcb70005010000010000000100002ea1fa99f2efa7a5eb0006000001000000000000010ac9f98baeffdbdd01000007000000000000000075e5eeddbbdc85cca2da0101020200020000000000006ba7af8ef9ccc7fe9e910b,
  0x6010100000000000000089df29685d9e1a7d48fec0005000001020000000000000582bce1cdd1e4dcddf5e000050100000002000000000001abc6859388dfec8b9acb00060100000000000000000113eede83818be0a001000600000000010000000045cbf7c4f0f5e0a082c001010006000000000000000006c18699e8cefba0d1f0be020101000400000000000000039998dda894ec89f8ecfd0203000200000000000001000699c7c6f897b3e3a004010000000003000000000003c9f4c1ecdeabf3c18e04010100000000000200000004e59d8cd08fc3b0cab005010000000000000002000038a4d78e93fcf4b0f00b,
  0x70100000000000000000286bbe3c0b7f3dea5d9d700040101020000000000000029e896ad9de9c280a5cb00050100000200000000000076b884e392f8d8c9e3b600050100010001000000000038db95c1c0efc5b7d3e200060000010000010000000009d9cdb4d7b2efb8b1c40006000100000000010000000194d2a486ede0a2d8ee0006010000000000000100000beec3e3d9f1b9ba9601020005000000000000000001ea85908faab1fbdcb9ea01060000000000000000000101cacdc3ead78ffa030100000400000000000000018b93b0d4b7928bd7a28805010000000001000000010048dbf8f08eb999920b,
  0x10700000000000000000001f3d7d6949193fcccb3e500050100020000000000000073e4b995b5c4de84ddfb01030004000000000000000002a492f08dd7e8e89afcc201060000000000000001000003e0aed99ebfacf1d80301010003000000000000003bf7f7d7e6f2f98eebb204010000010200000000000044eea9f5f6af98fadffc0401010000000200000000000e98e5b7d9e5f3f7dde804010200000000000000010013deecefdc83ccc804020000000100000100000036e5a9e3d6e9dc95b8050100000000000200000000028ad3c2e58cf9fca4880600000001000000000000012f99e4b889d0e80b,
  0x50102000000000000000011bcebaee5efa2bedbfd0101060000000000000000002bd4f6b2adadb6f19afb0104010101000000000000005fbde3f1f1bafdb8b8b20104020000010000000000001795e8e5daaba9da93ea0300020300000000000000003093b2c4edeab583d090030103000000010000000000048289d0e3a4c2fb92e60303000100000001000000003fd2ef97a1e3dc85fe05000101000000000100000005c287f6f690a9a0f905010001000000000001000028e5dc9a95b693c506000001000000000000010001b582c1e1abc2c706000100000000000000000102ed8e9cd7dcf30b,
  0x6010101e983d4b0acd1bbd492ac9300000000000000000004000103019c81d0d9f6d983a995e39300000000000000000101000600018da3f0e5edd3dbd792cfb4000000000000000003000001042ae7ebd684a6dbe5f197960000000000000001000001060043cbd2ffeaf2edf0a8b490000000000000020000000001050696bb8f82d9b3b5e9fecc0000000000010000000000060101d49eedabd7d6a4f6ac900000000001000000000001030314e3b3fab8fbf5acdef60000000100000000000100010501b990908889ffccfbe80000010000000000000001010508d9b7acbe9483e2d4000100000000000000000100061fdaccfccacc8c880100000000000000000000010634fcd1a781e1ea0c,
  0x107000003fca4fda5da87ef9ef391a20000000000000000000500020103c8c9f3bfb1939bd099f9ab000000000000000002010104003ddd82c6acb09ae0c9b1af0000000000000000040000010302978df49c9abcc6c3f99c800000000000000002000001050001ede5e4b98fc1c0a7f9b9fb0000000000000100010001050077b38de1c5f78febeb93d8000000000001000001000006001682f986988191fbe8db900000000002000000000000010501bdc8abedfc83aaede9e30000000100000000000001060024a1a3f7c1a7da8e95a80000010000000000000003010302abd0a0c0d3b4fbddb4000100000000000000000006010bdcc69ab28da293c8010000000000000100000000061af4a68195c98f9a0c,
  0x600010102d8bafc9dabee8b88cd96a50000000000000000010106000002e68bedb9acdea09ec1dc9d0000000000000000030100040001f8808c94a3fdb89ad2d7e8000000000000000004000101025bafe0f0dff3b9fbee83e20000000000000003000000040101c3bf84a98e99a490ffc4d00000000000000100000006010001a8eae6d286b8df9aa8a9e80000000000020000010000010411ed9ef2b8aa89abb2a4a10000000002000000000100000502e0b9ec878cd7b3eef3b50000000200000000000000010526d3c6b3b1ccd18688cc0000010000000000010001030205dcbfa4c497d2e8a5ec0001000000010000000000010520eeb885bd8798bcf80100000000010000000000000656bfbedd8ce0c0b60c,
  0x701000008d6a3cdefb0a9d080d8a7ee000000000000000004000301000be6d8c2b8e8c490ceaeaef40000000000000003000102010107b19ef8b5dca4a59dbea8800000000000000200000005010001a581ea8b9eeebea5ecdae9000000000000020001010004005caec9c2a7f7b183fc95de000000000000030001000001036dfe83dae890f2d98eb6c80000000000010101000000050002b8c2d0cec7efc2b1ea8fd0000000000200000000000105001eaebe82efffc1e7a3c0ad0000000200000000000000050104a7c3aa92a9e2c0b5e3a40000010001000000000000050168a1b5c792e29d81b3840001000000000000010100050005fcbfa99bd8ffa2d5e8010000000000010000000005011489a1aff69adc9e820c,
  0x1070000000baee280eaca91b1a4e699f00000000000000000060000010108869088c9f19bd0efe4c4cc0000000000000004000001030009e3a3b185c4aad8ebd19e8800000000000002000001050000088485d19495f1e6b7fdd1980000000000010000020005000004d883ed9aaca1b684aa8dae000000000002000001000203000aa1a0cda1b4b3d6aa8db90000000002000000010000050010ed8adba3c6b3a1defecf0000000003000000000000010422a4d9edf7faf3faffb69a0000000100000000010006000015afc8cac9baa6eb959fd00000010000000000000106000002a0fbf9ba9ebfcc9cb1a800020000000000000000010104099fff91a2c9bf8aa0880100000000000000000006010045bdeca3fdd9f7f1d40c,
  0x7000001002db4e3cd9b84c1d484ec8cb9000000000000000301020200006b8cc9858c8a9397f0e3c1980000000000000200000501000022e8a0f782b699b6f3eb9c84000000000000040000010002010ecca6eba186baddb9d8c8d6000000000001010002020100010bfabcdca5b6c5c5c99fa7b40000000000010200000005000003cc9df0afa2b7f49eeea78e000000000003000000010103000f89fcdda3dec1ea9aaef0da0000000001000100010202010010b8eaef9fcf85d8baeff88e000000010000000101020201000394f4c0da9296dfc7b38588000002000000010000000003021aa4fe8b99e9cca8d2f192000100000000010000000600000491d0e798b1a2e1e09ea80200000000000000010000010409c6d0e9e0b4cdda81e90c,
  0x7010000001ea8bdd0b1cce192b6bedf9e0000000000000005000101010021b9d8a885f5a5f5b2fcb1dc000000000000040000000301001194a0cdd6d1af9ac3d783ff0000000000010001030102000006d4a0e9d5a3ad9bbedcf9b60000000000010100000600000018dcfac8d1c4a5c1c892a99c0000000000010400000000000301d08dc6ca94e193e8c4cc860000000000040000000001010201f9fb99f6c9feb898aaa7b50000000002000001000005000004e5d9e9d48aab8fe18ac7be0000000101000000010005000002ca92f284d8ede9f7d9a0d0000001000000000201010200012f9ea2e9ea8786a5e6e1e800010000000000010201020001048ca5b2968affa5bca5900100000000010000000006000014eb95c2ecb5a788e5f40c,
  0x601000001000dec9c90f8dfe5b5eceef8990000000000000401000003000006b1d4aea6d5cbadff9d8196000000000000050000010002000aa19da2dac4e8cadec380d90000000000000501000000000202e0fea19bf0cf83b8bbebcd0000000000010102010201000057cb92a38bfe8d8d9d9effc5000000000100000006010000001f97ab95b5ef9a98cf86a9b10000000100000101020200010003ce8fa19dd1b7e8a0dca1fd0000000101000000000600000071c3c1ca86f4958a9bc0950000000200010000000005000001ebc8b2fe8585dca194f3cb0000020000000001000005000050d8dab3a7cba0a3b786f60001010000000000010005000012e682df81e29fe696cfc8010000000000000100060000007385b0a1918ebaf5c59a0c,
  0x700000100000df28487a1f1b2b485dfebb30000000000000301020200000007bcd5a7f98ad2dedf888bc6000000000001010006000000000fa0a392c59ea1b3fafcfab30000000000010300010201000014b0a6f9bfe9cba0b0acb6960000000000010301000200010002e698a5dcdcdeb7db988afb000000000101000201020100000cf2b5e598f680e9c9c4ef820000000004000000000001030001e0b7c7dfd19efeaa94cdb70000000004000001000000000351b0d3c191c18bd3baa6960000000100010002010200010006a5e298e1a58f918da584c8000002000000000000050100004be5fde2fc80f0e5e796820001000001000000000600000011a4bc9ebad3b78df993e80100000000010000000600000073cfe6eaebb4ccbdbcc20c,
  0x6000100000100228ebad687e08bd7e5add0800000000000010104020000000001acfad48bb09caaaaabc0c8ee000000000001050000000200002ba6c797ababfea49decc8bf00000000010300000004000000408b9fc3f7f4cc91eee990eb00000000030000000203000000138efe9ef89ea5e5b5c4fafc0000000004000100000000030042deedc9da97f7ce83ea8f0000000005000000000000010201cdcded9ecca1938d97f0cb000000010100010102010100004197a5dbb3a0a8f7929ea798000001000001000006000000000dcfcbf1a894b9abcbc7f78c000100000000010006000000000182cfdb97e3b8f29fd3e398000101000000000300010100017aa2dbd6fbedcd89debfe0010000000001000005000100000fdaf1fa8a97f5cac2f6f60c,
  0x60001010000005af9b78ea0a7ac8ec3e5a9f2000000000004010000030000000ee5b8c0c6a786e2adb2a2cf0000000000050100000000020009e68deaa3a38096e6a9d2ab00000000000600000000000101028fc691a9e78aafeb859cc60000000001000007000000000057fc98c4f38aff94a0b0e0a50000000001040000000102000030dce18ebe9bc9a880f097920000000100010102020100000003b4d0d699deeae49b90c8b10000000101010000040100000047e0a2e1daaee191818b90d70000010000010100050000000011b6f295a898f6ffd2b387a10001000000010001050000000001ead0d6e7bae3e6cdbb9ba5000101000001000000050000006ee6a7b1d398e9b987af830300000000000001000000020207e4bae5ccbac7a787a2c60c,
  0x701000000000007b7f0f1b7919dafb3c398b10000000000050100000200000035c4cde3e4b980d2a59d880000000000060000000101000005f6deb19da5f7979f90bdda00000000000600000100000100018fe9a4e88bd2e0c0e9cfe4000000000006000100000000010cbfb1dcc7e980d5c2af8d000000000301000004000000000285d986fcd7a5ffe49dc1f0000000000400010000030000000295e9d6b1d2f2bffa9c8fed00000001010000060000000000098acea68c889ca59ca6edb10000000101010200020100000005d6cdf88ec3b3d4a8b9d1a300000100010101000400000000049fd180edc3dea8fdcaa1da000100000101000104000000005ee7b5cab7c190f18be1e40100000001010000050000000007ca81829feee4b2eafa8d0c,
  0x1070000000000000c85c6c28fc5c2b6ddb3b5e9000000000006000001010000000b80a886c6fbc0d08c8480b40000000004000001030000000008ea9ff0a8f49bbcf2b09ac2000000000500000001010100000286a2e9ccdcc99de4dfe6920000000101020102000001000001f388ef8affb4edf6b8aedc000000020002010200000001007ee98bea9bdab9bf96b1ac0000000201000102010100000006d8c6f98af2be96e2f0b1b60000010100000006000000000007f6f7cdbebb86bed6c2f78e000100000100000600000000000feddaa1f9f7c4edbdc3ad000100020000010201000000010a91c5c296d6d7e0a1ada70003000001000000000004000037bbb1cc9aa0b7d4b983c80100000000010006000000000010dbb8c4fad5cdae9ecca70c,
  0x60101000000000016bddbababccbad8c1d083da000000000500000102000000001095e2bf88fdc1bfa6a5d7ab0000000101000600000000000016ecb09c95919694ae82dce5000000010202010100010000001687b4bced9789e4a98b87f8000001000006000000000001006a90f2baf58abbbca0aa900000010200000005000000000006a2d3a8f2c4bdb9dbd7eaf30000010300000000040000000007ebe5c682bcf4e591dbaaaf000004000000000001030000002affc6c2fed399dea0959a000004000001000000000300000197ce82cdf0cdfae5acc7a40000050000000000000100000203cb9eb7dd8edf98d6ea8a0001010000010005000000000006daedcb9ca887afd5a1c29001000300000000010000030000589bd0b4a2eff1e5e3f8940c,
  0x7010000000000000384f3fac5ebdfa88ebea5d4fb0000000005000101010000000003b29289b7f3c0ceaef6ead5e200000003000003020000000000028595e9dca1a79df28cb5f3db0000000500000000010200000044c1f1afabf09ce7afe8d893000001010101020101000000000290e7c6b38585bf97b6e0bde30000040000000100000300000026d5a2a385c1b788abafc7ce000004010000000000000300001393c083feed9fc5e3f6d8f00000050000000000000100020003f2b3de8ec9ead9a5d588900001000001000600000000000043d4edcffecbb7e8c5dab98b000101010000000500000000004efcacb3fcfcb2c0d0f3c2a5020000000000010500000000000886e184d4f0dceff9e7d59c0202000100000000000000000314d285eb92879192bfd2b80c,
  0x6010000010000000003c6e2fad8aff8ebfca785b80000000101060000000000000070c9c1eac4fea2cdcab7b20000000401000003000000000002a5c9e1ace3a9bcc7baf4b20000000501000000000200000045d196d7b5e3a49f9694f8000000050100000001000100001a99e2e4cabcada7f7b5b80000000600000000010000010002feb3bfddf1fcf183c7b00000000600000001000000000113fdfee7e6a8d98985dc00000201000005000000000000039ae99ddaeef899ffdea5e00000030100000004000000000059f3cfb0af80ea84cfbccd0001000000060100000000000002bdc6c2fbc29399f8c1bfb00100000000060001000000000022abe193faacb9bbe7f1ba0200010100000000040000000003f6ddfb87aee6a4e2a4910c,
  0x6010100000000000066e591c6b1b9bdbec8cfcbed0000010100060000000000000035fecbe9c8f7d887edaba19e00000103000102010000000000018bb5ffb7f7d2e9edebd393e00000010301010001010000000004d0b0a0c6ee9de6b08896ce000004000001010002000000000485c4c89d9ef9a5c28badab0000050000010000000002000001ab93b188c68dd6b2d89e960000050001000000000001010027ef9bea91cdf8b88ddec80001030000000004000000000070edb4f996bcccf1c5ebb1000105000000000000000000027a80b3cb8b9bfcb8fdfd0004000000000001030000000012b7d7b1c2cfd5b3b8a5e7960100040000000000000300000005e48a889fb3d483829f89b80101010001000004000000000005f5a6e7a8b29cd1d8f4e4c20c,
  0x107000000000000000011bdae90d09ec2adbfa3bce30000000600010000010000000002b09afee2ce96a79efdfabe0000010500000002000000000009e1b7bf9a83cfaf998d9da00000010600000000000000010002b9dbcfaacbe9c5d198a80000040000010300000000000001dea0eba696c0bf9ad2ecf70000050000000101010000000004f3e28dacd88b8abdabfa90000005000101000000000000010cbbf6ec9980b5e6eb920000050100000000000200000062e383d8bea0edede3cfc40001010100050000000000000012bac5e0ebeb9dfaf5eecce1000101020100030000000000000cf184ead8cd958a93aabcf5000105000000000000000200000e90f6be8ba2d18cadfad20100010101020200000000000005bfb5bfbf88b184b1efed920c,
  0x1050000020000000000000beaa0d5b189e6978dada1c7000002020103000000000000002486c1de9ca1ecbd9fa6ebd0000005000000020100000000000193ddf0c0d7a1ebf792b2900000060000000100000000010001b0c5cd8890b6a0cadfb8000100000700000000000000000fb1bf9993c4a6c2ccd7d4880001020201000100010000000005bdcea58ac581f2e8fad2da0003010100000003000000000005af8189ff89b2b6eb8be9ee0100010202000101000000000002f882e8feaae4d3ccb7a090010002020100010000010000000186fc95c8dbb29fed9181d80102000100000400000000000004e595efa285c5fee4c488c00302000000000001000002000008e1d4d988cdeee2f0fb86040001010000000000000000020397c5cdf5bc99f3aba30c,
  0x1060001000000000000000cb9bdedd6a8b1b1cbc29eeb0000060000000101000000000003ccb988a0d6bdc58fbff483000102010301000000000000001cdfbbf185b9c8fab79185cd000105000000010001000000000a8cb197cdf2e6c099c6cb0004000100000300000000000005a681e384e491e7f9f8fbb30100020103000100000000000001a39ef9de97e9f3e1b7dc940200010100040000000000000002b1b8cfca92bbeeafc9f6a40400000100000002010000000001a3ffaffea2eee2fee5fa9a050000000000000100020000000deeeeaaa4fefc9fb7d8aa0500000000000001010001000002f6fca2969eb78c86adda050000000000010001000001001880dfa3d6d78eaff7e4050000000000010100000000015a94e9baf0ea84db8d0c,
  0x10700000000000000000010bcd7c0bfaee68885fe9eaf000006000100000100000000000391c1ba89a5cdbcbcb1c0e20001030004000000000000000012aff6f9a1f6b6f4e1d5d38e0001060000000000000001000001c785cefc9898ced48ffc0004010000010200000000000008c8b3e3feb2e9ee9d8e84880005000001000002000000000061c7cd80c3a0e6fa8cc5e70005000100000100000100000010b9e9e6dd9fbdf5fbefb8000501000000000002000000003adf96a793f3f2d59cb1b1000501000001000000000001000bb3bedaa99ea1c298980005010001000000000000000126a8f9f2e1d5f5f3be010102010003000000000000000ce5f7998fe985f18588bdb0020000010500000000000000000393949ec294bdb7aeb38a870c,
  0x60101000000000000000004cf8d8baedfe6d9a2db83d8000400010300000000000000000383f5d4b4c2e8d9b9e9c6a2000501000000020000000000003fc38b9bb383bc97a081b9000600000100000000010000005bae9ae298929cd494a80006000100000000000001000006e1d6b6e7edb3a9e6f40006010000000000000000010026eb9fa9b0f19cf6c80101000600000000000000000002ebeaf4f9e0f2a6bdfbf19f01050000000000020000000000158cf28ea9c0cc9ab8b7cb0202010000030000000000000001e784d6c7edefaad9f3e8b0040100000000030000000000001894cfc0bdce9cb58697a20401010000000000020000000003a0c4ae9fd4e7a68388b306000000000000010000000001669cbebfbdcf91fa0c,
  0x7010000000000000000000487f1e79ba3b2eebc91eab8000401010200000000000000000194d6b6beada2eed6cbd0f70005010000020000000000000001b28b87e09ca5ced7c681b50006000000010100000000000077b38de1c5f78febeb93d80006010000000000000100000024a1a3f7c1a7da8e95a80102000500000000000000000003b4ef878fef8da4ccacfae503010000040000000000000000028efedbfa91c1a582ed87f6030202000000000000000001000bdcc69ab28da293c8040101000000000200000000000b81bcc38c80c8fdf4adc80402000000010000000001000002abd0a0c0d3b4fbddb40501000000000000020000000001bdc8abedfc83aaede9e3060000000001000000000000011af4a68195c98f9a0c,
  0x6000101000000000000000001d3fbcfbd919985a685bb9f0006010000010000000000000065b1bcbfe0aca4e8bcce980101060000000000000000000002ddcaa991bdc6b5fbd3bb800106000000000001000000000002beaea481c3c1b7b1c2980301000400000000000000000001e9f9dfd0aefcaba8e2aec3040100000300000000000000004099ea8aa29bcb8d86cc86040200010000000001000000001f958df7d5b9f0838eb1040201000000000000010000000295d8988c8effb3b9dc0501000000000200000000000009a1d8d6c4868d90defdf2050101000000000000000100000d869382dd9e85d3fe060001000000000000000001002fc7f3baeff2928c060100000000000000000000014fbaf9fac2d2df0c,
  0x10701070401040502,
  0x3060101,
  0x6030101,
  0x1070105d5000004010403cc000201010502a901010100063604,
  0x10701000005cc040104000003d5050101020002c406010000021b04,
  0x1070141cb0000000401042adc00000201010521c5000200000106049c0100010001063605,
  0x401040001f2d40000050101022fe000010007000101e5dc00040000020321fd01010100060038a005,
  0x10701000002d1fd000500030100029488020101050000418f0202010300014cc00400010004004ab605,
  0x1070100000020e104010400000015a505010102000010f00502010000011b060100000200028e05,
  0x306030101070102,
  0x60300030701010102,
  0x1070140afdc000000000004010429c4c7000000000201010525abd10000000200000106069dac0000010000010205019fbc000100000100000708ee01000000000100071b07,
  0x500030103eaadf0000000010007000104819efc0000000201010500018fdd98000000040000020333899900000200000106007bd1b00001000100010600219cc0010001000000060101f38007,
  0x107010000039bb7fa000000050003010003b6c9a2000002020102020006b49baf0000040001020002308ad9000100000700000102abeace0001010100060000018cd4fe010100000007000034ee8407,
  0x5000301000001f7d0b600000601000002000185f09f00000700000001011589d6000100070001000003d8afac0002020102020000028bf4af00050001000002010cc7fe010101000600000001fc808007,
  0x500030100000001b4dac900060100000200003bfe9000060100010001000fffc000070000010000017580010007000100000001e9e4d302010105000000007fe8f50202010202000000229eaa07,
  0x10701000000000040c8e9040104000000000029f6e1050101020000000024e0aa0601000002000000069dac0601000100010000019fbc060101000000010008ee07000100000000011b07,
  0x107010a8cd4b200000000000004010406c0badc0000000000020101050686b1d2000000000200000106018abe910000000100000102051fd3d800000100000100000702a1b40001000000000100070be80100000000000001071b08,
  0x2060001007baaa3f40000000006000101011fd4c28900000002020102020077b5b28400000005000001000309e9ba900000010000070000011395f59400000101010006000045def5f000010100000007000012b2d3f80300000000000101043aeef308,
  0x107010000000031a3e0fd00000501010200000028d5ecfc0000060002000001000ac1c2a000000700000100000164f4fc0002020102020000003d918eb60005000001000300000ed6d9b901000007000001000011a4e0e50101010006000000001dd3b29708,
  0x107010000000000000a91c7b804010400000000000006caa0e805010102000000000005f7d8c0060100000200000000018abe910601000100010000001fd3d806010100000001000002a1b40700010000000001000be80701000000000000011b08,
  0x1080101,
  0x2070101,
  0x4050101,
  0x5040101,
  0x7020101,
  0x8010101]

/-- The triples `(n, b, a)` of part 9. -/
def enumC9 : List (ℕ × ℕ × ℕ) := [(8, 80, 23), (8, 80, 27), (8, 80, 29), (8, 80, 31), (8, 80, 33), (8, 80, 37), (8, 80, 39), (8, 80, 41), (8, 80, 43), (8, 80, 47), (8, 80, 49), (8, 80, 51), (8, 80, 53), (8, 80, 57), (8, 80, 59), (8, 80, 61), (8, 80, 63), (8, 80, 67), (8, 80, 69), (8, 88, 13), (8, 88, 15), (8, 88, 17), (8, 88, 19), (8, 88, 21), (8, 88, 23), (8, 88, 25), (8, 88, 27), (8, 88, 29), (8, 88, 31), (8, 88, 35), (8, 88, 37), (8, 88, 39), (8, 88, 41), (8, 88, 43), (8, 88, 45), (8, 88, 47), (8, 88, 49), (8, 88, 51), (8, 88, 53), (8, 88, 57), (8, 88, 59), (8, 88, 61), (8, 88, 63), (8, 88, 65), (8, 88, 67), (8, 88, 69), (8, 88, 71), (8, 88, 73), (8, 88, 75), (8, 96, 13), (8, 96, 17), (8, 96, 19), (8, 96, 23), (8, 96, 25), (8, 96, 29), (8, 96, 31), (8, 96, 35), (8, 96, 37), (8, 96, 41), (8, 96, 43), (8, 96, 47), (8, 96, 49), (8, 96, 53), (8, 96, 55), (8, 96, 59), (8, 96, 61), (8, 96, 65), (8, 96, 67), (8, 96, 71), (8, 96, 73), (8, 96, 77), (8, 96, 79), (8, 96, 83), (9, 2, 1), (9, 3, 1), (9, 3, 2), (9, 4, 1), (9, 4, 3), (9, 5, 1), (9, 5, 2), (9, 5, 3), (9, 5, 4), (9, 6, 1), (9, 6, 5), (9, 7, 1), (9, 7, 2), (9, 7, 3), (9, 7, 4), (9, 7, 5), (9, 7, 6), (9, 8, 1), (9, 8, 3), (9, 8, 5), (9, 8, 7), (9, 9, 1), (9, 9, 2), (9, 9, 4), (9, 9, 5), (9, 9, 7), (9, 9, 8)]

theorem certs_ok9 : checkAll enumC9 certData9 = true := by decide +kernel

/-- Certificate data, part 10. -/
def certData10 : List ℕ := [
  0x50003010003e38bbbf0a8000000000001000700010003c68ee3bebd000000000005000001000350dc9dc5a900000000010300000104007a89acb7da000000000200000106000029dbf1dbd1000000000400000001010320afebd6eb00000001010000000700006cd397e0e0000001000001000007000011bb8ad6b400020000000100000004026ab7aee40100000000000001070000098fdbe40a,
  0x5010102000000000014cdc89ee100000502010000010000001e978ddaf00001000602000000000000199e94e6e000010302020001000000004abaffbcfb00020201020200000000000197f6c4809b010000070000010000000030e3adebb9020000010600000000000013be9b9cfb02030002000000000002001dc8a2aa030300000100000000000201a297b5040101000000000003000001cef9f0a60a,
  0x10701002aa7a6f0bfdb00000000000000000501010226dc89c4d5f50000000000000002010105001fedb9d1edac0000000000000004000100040cbdf8cbb29a00000000000002000001060012c2e0c6bbc0000000000002000100010005048eebd4af8000000000010000010000070001a79ffeb48000000001000000000100070012cad7b48000000100000000000001070001b099b88000010000000001000000030407eab08001000000010000000000000714a0800b,
  0x10701000046f0ea8bbdeb00000000000000060100000219e69c9c90ee0000000000000202010202000183868fa080800000000000020000010600000a8df28ba8f500000000000300010000050008b0829489fe00000000000400000001010306d3dec9c4870000000001010000000700001aa9e6bf808000000002000000010101020202bbf5cdf4800000010000000001000700004efdb3bd8000010000000000000107000005f69aa1b00200000000000001000001050cf6a2830b,
  0x4010400000002ade295c0d300000000000006010000020005d3face91810000000000000700000001010fc4ecfccec20000000000020201020200007cfb88abc080000000000100000700000100389d89b1ebec0000000002000201010201000980d992a3b800000001000004000004000001aff2f2b2dc0000000101000000070000001be2ddb5cda400000100000002020201010005c6cca08080000100000000010007000000519b808080010000000000020102020100049c8080800b,
  0x60002000001000fd781dff08000000000000700000100000101daf99ae08000000000010007000100000022bbb4a0eaf100000000020201020200000006f1c890ade70000000002020103000100002693bd9e989c000000020000010600000000048fabc694820000000200020101020100001b978a86cfe4000001000002000600000000078ac9b688d90000010003000000050000000af5e5e083a50001000100000006010000000384fcc0cfa40100010001000000060000001dbbedcfda0b,
  0x7000000010100006ef0aecdedb000000000070000010000010010f998f4b59000000000070001000000000101bad0b6a3ba00000001000700010000000001e589f596c2ea00000002020102020000000002a4e3b48e96e900000102010102000200000045ace0d090a600000200000106000000000029baccbec0f5000002010200000202000000518cf4deb2f800010100000007000000000063a78b89f08002000000010101020200000001fbf1888ec203000000000102000002010002a6a6a4ebd40b,
  0x7000000010100000001d1b0aaf7f39200000007000001000001000015a680b6fc8400000007000100000000010004fc93c0808000000202010202000000000007c89bd6b9a1fe00000501000100000002000001d0dad6bbc700010000070000010000000003d0c1e2b29cee0001010100060000000000004dff8fa9a8f50001020101020002000000003ebb8df9f88000020201000200000101000012f6f4ec8cee000202010101000100000001218680808001010000000700000000000079dbaafae7850b,
  0x2050200000000000000039fa9bbb7e90000050300000000010000006fc08cb88000000601000002000000000001c5bea6dbc300000700000001010000000004d2d5ed80800000070001000000000100000df881c7800000070100000000000001000185e6c29000020101050000000000000004dbeea08080000202010202000000000000179091e0808001000007000001000000000009cebaedc8fa01000600010000000000000104c7edf202000001060000000000000001f8e0a5a4ca0b,
  0x50101020000000000000016f2e6e6f3a900060100000200000000000021fab18197e000070000010000010000000002b2cffd8a800007000100000000010000002288f5ca8000070100000000000001000002c383fc800100070001000000000000005eb5e7b293da0103000500000000000000005dccd0d28df301060000000002000000000007c5f085abc004000100040000000000000012f5ebabf79d0600000100010000000001000eadd8800700000000000001000000012590800b,
  0x7010130eb000202050016ae000401010321df0101010600278804,
  0x60003000494000700000204f1010107000010b402030004000ac704,
  0x60301fedb00000002020502a2bc00000101010669d000010000020608900100000001072005,
  0x5020210d7920000010107000e97b900000301010406b2ed00020100010503b880010002000105408005,
  0x60101011a9ae800020104020029e9c401000008000003859102000104000201f2cc02010001050004a3d005,
  0x800000103859100020401020029e9c400050100010204a3d00101010600001a9ae802000401000201f2cc05,
  0x7010100000eceb90202050000000e8d92040101030000058ded04010201010006f080050100020001408005,
  0x3060000000001fedb05020200000002a2bc06010101000069d006020000010008900701000000012005,
  0x5040b0103051902,
  0x702170203043102,
  0x305013b0501030d02,
  0x405000b0503011902,
  0x5020201e488c3b600000000010107000288baffeb00000000030101044f96f487000000010102010401a7f6b080000001000200010515ecc080000101000000010601ee8080010000000101000608808007,
  0x7010102c5c0f0ef000000000400030202b2d6eb920000000200000700018af7c2ed00000003000101040bc2b2e20000010100010402488cc280000200000100000603e0d3b801000000000106012af59507,
  0x800000101c5f1d68d000000040101030017e4bed000000005010001021f99c7c0000001020103020003f38a808000010001000700004afd85bc00010001020302001bb2fac4020000000103010204c0808007,
  0x60101010005b0a4e5c5000000070001000102c59d8ba9000003010104000004c2ced8a8000004010100030002a7e3eca90001000008000000069789d99e000102010103010003ee8086a2010002000105000001a6f2a78007,
  0x80000010005b9dbe4b10000040101030000049aca99ad0000050100020001018aa49980000101010600000003ccb7c994000103010102010002ef87dc8f000300000303000002a7e3eca90100010007000000028dbcd69707,
  0x6010101000001b8ebb1c8000007000100010005e3b08080000007010000000141808080000102050100000018b2d9ebd80004010002020000079feaec8601020100050000000683f2c8c403000200000400000386fe9dcb07,
  0x700000200000001a6fb85000700010001000018849680000701000000010002c0b7d0010107000000000057e1a8b101040103000000002cffdcdc01060100000000010ea78702030102010000007dc8a9f607,
  0x701010000000001ffb7e0eb0202050000000000029a93fdb6040101030000000001808d918705010001020000004889f880050101000101000017dac080050101010000010001ee8080060100000100000108808007,
  0x7010103bdfca6de93000000000004010103039482f9a8f7000000000101010600048dc58eb3dc00000001000100070035dcdfcad800000001020001000562a7bd9db80000010000000107001480c794b800010000000001060101c0c2f8f001000000000000070106aacfe208,
  0x60003001ce5a9e7bb00000000020301020101a7abf3d68900000001000008000056f6a58ca600000001000500010207a48cdcbf00000002010001050059ccaf8400000101010000060018e9d8ff8400010000020000060002f5ecad88010000010000010600139efec708,
  0x7010100002eabd9f2c90000000401010300002da0c2b6d30000020001050100000f9ed5ec86000002020101010200299288aaf000000202020100000201f0edc8a40001000100070000001c998cffac00020200000102000201809d9d9a0100020002010100020398eddb8408,
  0x204000102000039a6e386d10000020400020001001dc0e7ad9e0000040001030100000aa7e7a1ce0000050000030000010398eddb840001000008000000003592e0d18100010004000400000010a4def7990002020002010002002cb086a10101010000060000000c93f1818408,
  0x800000100000003b2dff8cec4000300060000000000018fefd1cfa300050100010200000003d8dcc4dd0006000001010100007c90bcfb940006000002000001000ecd9de1a8000600010100000001609af8e301020103020000000006c49f85c59702010005000100000024d2de838608,
  0x601010100000000048dc58eb3dc00070001000100000035dcdfcad80007010000000100001480c794b801010700000000000003bdfca6de9301060100000000010001c0c2f8f001070000000000000106aacfe2030101040000000000039482f9a8f705000100020100000062a7bd9db808,
  0x40507fb0001020608d0010001074003,
  0x504039c000103050cf2010002067d03,
  0x70206e00003010507d40100040402d703,
  0x80106fb00040005069001010304048003,
  0x206010ba50005000401f20202000503f403,
  0x4030261b80100080025db0301000512d003,
  0x503011dd50105000308da020105011dfd03,
  0x10305001dd5010501021dfd0300050108da03,
  0x8000125db0203040061b80500010312d003,
  0x10602000ba50400050001f20500020203f403,
  0x108000006fb04030101048005000400069003,
  0x207000006e00404000102d70501030007d403,
  0x4050000039c050301000cf2060200017d03,
  0x504000007fb0602010008d0070100014003,
  0x601010111e3d2bdb0acf800000000000001010700000fb99a99f0c7aa00000000000004010100030f83d4c1fac3f300000000000101020104002aec87d3c0e1d8000000000003010001000416c5eaff9ea500000000010000000701000b80c49f83a8de000000010000000007000101f4fb968bdac800000100000001010202021bfaca969aab000100000001000001050101f283e3e986010000000001000001040207aeeeb9970a,
  0x8000001000fc485a199c6d1000000000005000200020061dd8fc598caba000000000101030202000003daa3e8cef1a688000000000202010101020031bd97d894d8b000000002000000060001000dbd91f78cb5e30000000200010202000002249fb085becfea00000002000200010202002aafdfbaddc59a0000010000000107000000299686aacbf2c4000100010001000202020005a682a7f4e788020000010000000000060013d09e8fec8a0a,
  0x7000100010015ccbbecf697af000000000204000102000047de91f490f8ad000000010000080000000035a493dec6b0d7000000020003010200000167c5eefbb4cb00000002020001020101001efdd7fbe9f9cf00000002020200010000020384a3a4c4d292000001000200010500000020bc9da7e4dda30000010100020102020000039eebdeb689f90001000002000006000000069381abaaa2be01000100000000070000003c97b8e2edc70a,
  0x80000010000001791ab87bf9dff000000040101030000000014f2a88ffdf49e000002020101010200000014e3dda78fc88b000002020101020001000013a680a1cbc6e8000002020102010000010003a3decaa7ce900000020202010100000001208cc0b4dcc8000100010007000000000014e6c3f497e2dc000100020201020100000002ccc5f4ddcfab000102000100050000000004d2abb5ace889010000000107000000000003d5b1a6b5da880a,
  0x60101010000000015f7c790d1dd8c000000070001000100000062bbf2c0a2dba8000000070100000001000005d8e5c4e5c988000004000201020000000028a5a692bbead800000401010200000100000fd7ca87bcf4ef000005000102000000010002e0868fe6bfae000100000800000000000052fce1fba2ffc3000103000102020000000061c7fefdcfe29d010101000006000000000025afebf8f9a6ce050000010000000000000306e5cfacefa10a,
  0x107000000010000000004dbd48da5ff9600040102010100000000000df1ebe7cc98d3000502010000000000010067dd869ade010007000000000100000068fdf797a6e801010106000000000000000af7bbd1bda5a101010400030000000000000af79a93e0d3e70101050000020000000000019fdfe18e9cd801050001000100000100000bfdd6d2d4b70201020102010000000000028ee4f7d3b2e7020401000001000000000103948ae1d30a,
  0x10107000793a68dcfe781d100000000000000000104010308d1a183f2aff1ba0000000000000000030101047f98bce6f49ba700000000000000020001020402c2c2bdc490e4800000000000000200000002053ffdf6e0c1f08000000000000100010001000611d3a5969b808000000000010000000001030401decbc5d480800000000100000000010001060facf7c880800000010000000000000101065aabe0808000010000000000000001000702bf808080010000000000000000000107048080800b,
  0x70101608af4a5cef8ff810000000000000000040101034bf9b7e1a9f990ab00000000000000010101060046a5a188e984f9ce0000000000000003010000051da6aff9cfe6c58600000000000001000100070027c68c9ef0b080800000000000010000000107000787f985c1e4808000000000010000000001060173a6a5f6e180800000000100000000000007010aa5da9f96b0800000010000000000000202044eb7d4928c8000010000000000000001030402e6c7c9e58001000000000000010000000705e987b7a00b,
  0x601010101afbffddaad8298a50000000000000001010700006b84ecbba7febcc60000000000000004000201020187b3d6b8fb9fb5b300000000000001010201040002b89cfaa395fcc7ee00000000000100000007010051b7d3eda48dedc10000000000010300000000051089c4dc8cee8dff00000000010000000007000112e09dabd3a1d7e000000002000001000000000601a1c6f2f888b5f40000010000000200000100051cffccb6afbaf400010000000001000003000401c7edbc84c39601000000000001000000050204f28fabfca30b,
  0x7010100018687fcb4888b83af0000000000000004000302006aa2b0e0c7d7aea700000000000000050100010218dcdf94b0a184b700000000000002010201020101c1d6f9bbe99a80800000000000010001000700006bcae7a88392f0d100000000000300000001040105a5ecc3c684afe50000000002000001000006000e95a4bea780808000000002000000000001060002a29089fc8080800000010000010001010002033df2aec080808000010000000000010003040003fb84808080800100000000000100000106000ee0808080800b,
  0x1050002010006b2e4cf9f87a2f8aa000000000000050001000201029b8299a6e0f59cd700000000000100000800000004b8db97ebf9a0c7aa0000000000020101010202006ee9ff8dfbedfc940000000001010002010202005390f983def1b99d0000000001010100000600000288e6c9ba85c9f8e300000001000002000006000019c7e3acbf80edf600000003000100000000000511c0e3849dd5a9ae0000010001000000000700000ba8e3f7ace9c4800001000000010000000700007dfdc7cc9fb88002000001000000000000000602bed7f6f0f8800b,
  0x700010001000b8f96d8c89be88400000000000007010000000115e9fbef988080800000000000020203010100000289ea909fbec7d49c0000000001000204020000004f9fa0e2a5b4a4b60000000002010101020200005ce8afb082b88cb60000000002020100020002002c8fc09aaee699af00000002000002010201010037e1faccff8892f800000100000200000600000017f6848bf2c3ac9a0000020000000102020002003caee3c6c7e993000100010000000007000000039de196a7d1989001000000000002000600000018b9c38894c0ec0b,
  0x701010000005bfe9bc09cbbf09e00000000000600000200000109a7f489b4c1c18f00000000000600010000020010a8c4cde9cfe0a8000000000202010101020000709ca6cb86fff7de00000000020202000101010004f2a7bb83f6f0d20000000003010000050000002adbf5b2ecb9a9e000000001000100070000000054e3fee283bef68a00000001000202010201000030dd9ae890d19ff600000100000202010200010020e5acbad1a5d48000010000000201020200010004eac79cecfee88001000000000102020200010029b7cda1d1b0800b,
  0x20301020100000001fadae9d2d4a2fd9000000000020400020001000006cfdae0a4c1f0dac4000000000600000001010100019ae6eef5c4f5a1bc00000001000008000000000005faac92e1d6b8bfb000000002010101020200000004cb9bdec4c58ae39b000001000103000202000000049380cb8aefbfe19100000101010000060000000072a0f0f590c09eef0001000001020102020000005485e9bff18ea4d50001000100040001000002001d8edec799bbb3d20100010000000007000000002388878ac9d8a70101010100000001020000020aa4f7f8f5b6a7d90b,
  0x80000010000005092a5b0c3e1d1940000000005010002000100000ec3baf98ea0f8fa0000000005010101000001000bf1c080808080800000000104000101020000004188e9f7de8f97b600000002030100010002000019dcb0c3b8efc3c300000003000003030000000028bcfec4e4df828a00000100010007000000000042bbd8f0fa9ffafd0000010200010005000000000cb5b6e388e2baa300010101000000060000000014f2fc8cc1eaa6e0000102020001000000000102448080808080800200000000000106000000000184bcc4fbf485c10b,
  0x20400010200000000018e87c1d2f39fa0e2000000020400020001000000038cd4c5d4e8c1a4890000000700000000000001017bb0f9fde1a08000000100000800000000000002aaaadfa4a9d1d09d00000102010005000000000017f8d4fdd1cbdcdf00000201010102020000000001bf8aa6ecd5faaab400000202020001000002000030e9b19098a9ec8000010002010102020000000001cbefb2dc8bcd9eed0005000000000001000003000496b594b1eae08301000100010006000000000019f6d2a8b9e5a99402000002000101010100010073a5e5efeeeff70b,
  0x8000001000000000390e8c4b7fb84cef200000006000001010100000001d6b4b3deecaea0d50000000600000200000100002ae881ebb9949bf20000010101060000000000002ca39bdc8daa84000002020101010200000000018e89d1a5b4b3aeec00000202020001010100000041e7dcc1d6b4c2e100000301000005000000000002b594a190c5b1b2bc00010001000700000000000003aacbb8d2de80808001000201010200000100010008a88ec1b3f2d4fc0200010001020100010100001993c4e6aca3f9ce02000200010200000000010142ea848de2dbf40b,
  0x8000001000000000014f880ecfed5bde40000040101030000000000000df7ea9abfcfab9b00000501000102000000000008fe85e1feeed2c300010101060000000000000005d09086928dcdae0002010201020100000000001398f79a88efb0960002020101020001000000001285dbadaaf9d68000020300010200000100000003efe4aaed91ca8000020300020100000001000048e2c4c4a6848001000100070000000000000012c1f6cd9082988d02010300000100000100010006a9faea8eb8800202010001010100000000012081e8eff0800b,
  0x700010001000000000073c6c8c3e6a080800000070100000001000000000daf95cf8cd0f3c800020104020000000000000001d6ff98c59a8abce00100000800000000000000002dfde7c0be8f01000700000000000000010003d8d48080808001020102010200000000000001b4c6a1a9f7e28080010202020100000001000000049cf4e0d880808001020203000000000001000039d9a0c08080800201000105000000000000000f9291bce8f2f4c004010100000000030000000004acc1af88baaee806000100000000000000000206f0808080800b,
  0x2040102000000000000001deb99bbc7bdcfb90002050001010000000000006386bfb7939ae6ce00050002000200000000000007ffcdd3afc996990006000100000200000000000fbea7a5a0cff6a00007000001000000000001003fbdf0b7d38a00070001000000000000000101c6f1a687ed01010106000000000000000054a0b5c7b79fe1ac01050100000000020000000002f8cde198f5c3ea02050000000000000200000033a8cbd4e989cc020500000000000100010000099afd95e4f4cc0301000005000000000000001da694f7cfb5efbe0b,
  0x6010101000000000000000a9ebffbe0d1dd940007000100010000000000000696f9f4e9c7c080000701000000010000000000018bd182e1b490c00101070000000000000000000ea1c98ce1fec2b00301010400000000000000000d99a6f1aeced8db04010100030000000000000004e9debcd2d6e1b9050102000000000000000100388397c3e40502000001000000000100000ca0d992e9f00601000000000002000000000980fefba3ca8006010000000001000100000001cdf28cefbfc007000000010000000000000174b594d10b,
  0x70101000000000000000003b79c91d6c4cbba01040400000000000000000001dbdbcb87a8ecdd04000400010000000000000002c2c2bdc490e48004010103000000000000000001fdd6ebd4cfdd820502000100000001000000006fa5e2ea808005020100000000000100000007d6bbe480800600010000020000000000001ffefbb0a0f88006000100010001000000000008e9d2cb8dc0800601010000000000000100002d95f08080070001000000000000000100019fc08080070100000000000000000001028080800b,
  0x50401cded000001030508e6960001000206798c010000010704f104,
  0x7020bc0a400000301050ef8f5000100040407a4c4010001010638a304,
  0x4030204dfc600010008000792e30001040004098cf5010000070101e4e204,
  0x50301398ee000020007001995f4000302000404c59301030000050fd89904,
  0x107000104bc8900040103017f8d00050100036aa90102010500058cc104,
  0x10800003297f1000402030039d3e6010500000306dcd3020201030138a5d604,
  0x700020002b08200070100010c99f7010305000025fa9703020103001b99f004,
  0x8000100039a85010503000002afe3020501000172b1040004010004f5e704,
  0x2070000000bc0a4040400010007a4c405010300000ef8f5060101000138a304,
  0x40500000001cded050301000008e6960602000100798c070100000104f104,
  0x7020cc0f99a0000000301050ccd9cf200000200010603c5ba8400010001010653c3fa0100000002060389f505,
  0x801039ba2b500000004000503839aa000000101030403abe88000020000000717908001000001010602808005,
  0x5010319afd1b90000010106011ff0dc9300000300020406bf81e70002000003040493d9e301000000060244e7bd05,
  0x5030104b2c48400000105000305a5f3bc00000300040205a9f2cd00010001070004adeac002000100000616d4dd05,
  0x60201049796d700000201060010f69c00000401000402af86d200010100070002ebb7b001000001070020e9e005,
  0x10601010ef1b28000000500010302c480810001020006000aa9a1fd000301000104018bca8103000000010540808005,
  0x107000114bcdeab00000501000306abf3a50001020105001bc2f7d000020101040102fbc9bc03000001000501ada9a205,
  0x10800003cdcb6fd0000040203000595f7b600000600010232fed1a000030001050030bc9fcc0200010006000ad094db05,
  0x10402020001ba929c9500030004020002df8dfb0005000100031ed8b7a60100010700003d9acfcc0103000005000cc1faf405,
  0x1050102003de3aea80004000203003ddda50005000101020d8f88990101000700001fafb5d303010000040165f9ee05,
  0x80100003cdcb6fd0003020400000595f7b600050100030030bc9fcc0006000100020ad094db02010006000032fed1a005,
  0x5010201001bc2f7d001000701000014bcdeab01040101020002fbc9bc03000105000006abf3a505000100000301ada9a205,
  0x6000201000aa9a1fd0101060100000ef1b28003010005000002c48081040100010300018bca8105010000000340808005,
  0x60102000010f69c00070001010002ebb7b000070100000120e9e0010206000000049796d704000104000002af86d205,
  0x103050000001e94aafd01050200010015e594c00204000300001f95fc9e0300050100000de1aba605010100000271a7d105,
  0x1060101000004fc8a9903010500000003afe7f00403000002004bfac505000103000061ddec05010101000109ea9b05,
  0x1080000000004869cb50500040000000298a0a005010201000003abe88006010100000102808007000000020017908005,
  0x207000000000cc0f99a0501030000000ccd9cf206010002000003c5ba8406010100010053c3fa0602000000010389f505]

/-- The triples `(n, b, a)` of part 10. -/
def enumC10 : List (ℕ × ℕ × ℕ) := [(9, 10, 3), (9, 10, 7), (9, 11, 2), (9, 11, 3), (9, 11, 4), (9, 11, 5), (9, 11, 6), (9, 11, 7), (9, 11, 8), (9, 11, 9), (9, 12, 5), (9, 12, 7), (9, 15, 2), (9, 15, 4), (9, 15, 7), (9, 15, 8), (9, 15, 11), (9, 15, 13), (9, 18, 5), (9, 18, 7), (9, 18, 11), (9, 18, 13), (9, 21, 4), (9, 21, 5), (9, 21, 8), (9, 21, 10), (9, 21, 11), (9, 21, 13), (9, 21, 16), (9, 21, 17), (9, 24, 5), (9, 24, 7), (9, 24, 11), (9, 24, 13), (9, 24, 17), (9, 24, 19), (9, 27, 4), (9, 27, 5), (9, 27, 7), (9, 27, 8), (9, 27, 10), (9, 27, 11), (9, 27, 13), (9, 27, 14), (9, 27, 16), (9, 27, 17), (9, 27, 19), (9, 27, 20), (9, 27, 22), (9, 27, 23), (9, 30, 7), (9, 30, 11), (9, 30, 13), (9, 30, 17), (9, 30, 19), (9, 30, 23), (9, 33, 4), (9, 33, 5), (9, 33, 7), (9, 33, 8), (9, 33, 10), (9, 33, 13), (9, 33, 14), (9, 33, 16), (9, 33, 17), (9, 33, 19), (9, 33, 20), (9, 33, 23), (9, 33, 25), (9, 33, 26), (9, 33, 28), (9, 33, 29), (9, 36, 5), (9, 36, 7), (9, 36, 11), (9, 36, 13), (9, 36, 17), (9, 36, 19), (9, 36, 23), (9, 36, 25), (9, 36, 29), (9, 36, 31), (9, 45, 7), (9, 45, 8), (9, 45, 11), (9, 45, 13), (9, 45, 14), (9, 45, 16), (9, 45, 17), (9, 45, 19), (9, 45, 22), (9, 45, 23), (9, 45, 26), (9, 45, 28), (9, 45, 29), (9, 45, 31), (9, 45, 32), (9, 45, 34), (9, 45, 37), (9, 45, 38)]

theorem certs_ok10 : checkAll enumC10 certData10 = true := by decide +kernel

/-- Certificate data, part 11. -/
def certData11 : List ℕ := [
  0x1050319f7d2adfb000000000301050992dbcfe30000000200010604dbae87ca000001010000070197df90bc0001000001000709858fd8010000000001071cdcc406,
  0x501030481e3c0b80000000101060103858d87a60000000300020401ceb68bf70000010000070101c1d0b7a70002000000010609f4859b010000010100066c90a906,
  0x10500032291fcceb00000000200070011cdb888af000001000107000ffc90b4f20000010300000502e7d7c497000200010000060198b7f5c901000000010502108e9e8f06,
  0x8010002a4ddf795b00000000501000301f5b387f7f1000002010006000292debdecfd000100020006002eb4edf393000300000100050fcebaa8b90101000000060107ddead59606,
  0x108000069ceaa8680000000060001025bf9e0ca840000030001050038edaee0900001020000060030c3e7f8a1000300000200040398ede3910300000000010501e0aac3ba06,
  0x70100010189aac3d7d3000004010004007e87e1e7bc0000040101020101c3d399d70001010007000078e688ceea000300010005001695f0e9a6010000010700001794dec48a06,
  0x1060101001e8f9ee6de0000010700000130a9b4b4d4000003010500004bd6ba95d7000202010004003aafed89850003000005000102d295d6eb0101000007000014f5c6dac706,
  0x6010002001be8abcef1000007000001010af4fdf7cc0001010601000014abe3dbbd0003010005000020e4e6a1bd0004000102020004dad5f49d010000070100001acbcdceac06,
  0x70001010001b5f8e0d2a1000300040200000186be8f829a000401010200011cd6d0bbf40005000100030010d3e8f79d0100010700000075a5998ff10103000005000036d0f782c306,
  0x80100000041a7b9eda40003020400000075868feb000500020200003ed2fce895000501020000010393e693820104010100020011b7c1fda60300000501000023a3bdd3b406,
  0x1080000000003a694d9d8000601000101000196a6e4be000700000100010bc19ee10103010400000002dabb8081010500000300000188b184c80301000401000001f6eebf8006,
  0x103050000000049e7b88db00106010000010004a6e6b6d4020400030000002ea7e5fded02050100000001209cbc9e0402000102000012e3e7f989060000010002001dbccfe806,
  0x106010100000015a197828f010700000100000acbb38391030105000000001c8e90e3da040200030000000ba5e6e3ea0502000100000105f4f29f0601000000020045aca4bd06,
  0x207000000000004a299ab800501030000000004adb6a2b00601000200000001a9e7b3fa0601010001000025f7e48f0602000000010002a1a3f60701000000000107979106,
  0x80103ebd88ea5d7000000000004000503dba6ef89b0000000000101030404e2efb08c8000000002000000072cb6d2d080000001000001010607e0ca808000010000000002063090808001000000000001070180808007,
  0x1080023dd8dc6f1b000000000000402032eeca7f4d4ef000000000300010517ccaf89efc8000000020001000606e9c1b1a0f8000001000100020501c5e3aac6a000010000000102050cb894b1c001000000010000072af5958007,
  0x5010304b3c2fc9f9d00000000010106010497a298ddfc000000000301000501f3db8d99a70000000100000701028cb5a597c000000200000001061184aef4f8000100000101000602b3beb4cc010000000100010609a5b3c307,
  0x601021694baa09182000000000102060003daa89cdc84000000000400010410c7ae928ceb00000001000107001296a4ebd7bf000001000001060102eb8ad3d2d400010000000007011fbbe6e9a601000001000100060195cda9f907,
  0x106010137bfb5b5a6dd00000000050001031d87dccce1a3000000020001060019e4e580b3d200000003010001040198d382b2f400000101000007000e9489808080000100000100070001cdd080808001000000000107000a8080808007,
  0x8010025efd0b8d7c200000000050100031dcf89c0c58a000000020100060019e78abe8db500000002010202020fcce89acb930000010002000600119dcf939cbe00020100000000060190e2ccf08a01000000010007000fa4d2ecea07,
  0x108000001bf83dbaef68000000000060001024eddabb9abf9000000020200050001d9ae86b8e38700000200010006000198e8a880850000030100000005289cb188f6f2000300000000010505f3dc888498020000000100020445f6edd09707,
  0x600020149bcdbf7e1b000000001000800004a9f9aa9d3c400000004000004011c9eaea3a383000002000201020210b1cb9bb1d000000201000006000e84abe592b0000100020000060009c3feb9a08001000100000106005187fd808007,
  0x1040202000398cbefafbe99000000050001000357c3f781b1b6000001000107000001b0f8ad8dc6ef0000010300000500398ee6b7d0f30000020003010102328acfef8c8f00020001000006001ea789bef080010001010000060004d2d9e1c08007,
  0x70100016ec7d2b4dbdd00000004010004004bdbebfeb08c000000040101020116fa99cba4a3000001010007000071adcac8808000000300010005000fe5aac8a9c600020100000006000fc09ba29dae010100010000060002e393a9bec407,
  0x106010100098e8bb6f8bd00000001070000014ccba8ea8d8000000003010500005093a9b3dafb00000202010004004fc7ece3aeb4000100020201030004aeeac3eaa20001010000070000278dbab4ada40100000201020300048afae7d7ef07,
  0x107000100048cc4a8d7ee000000060000020105f1b2f1caaa000001000700000107f6ecac98970000010202030100279ed5ec91a300010300000005006ca4e8efa20002000001050100058dccd1ffef02010000000006004ae6d4fcc007,
  0x5010300000493dcb4fad8d8000000070000010101ecb398b4c6ac000001000800000005f39bc99986a9000003010005000002b8bdc5948cc0000102020001030003eab7e6dcceb2000201000006000001a2d6f1d8fce1030001000000030221919b9b8fea07,
  0x7000101000191b7dfabbb86000004000104000034b9fab49bcc000005000100030027bae09c96fe0000060000000102158080808080000100010700000001a6f5ffdc9ba900010201010400004c8ae8aa8e97010002010005000021d0d7c5b99607,
  0x70100010006e697a7b4b8000000080000000102b3bd8e8d9d0000030103020000099384b99f9800000301040001000ac7cbc6e0e8000300010005000006d4dff697f0010000010700000002a4bfc58fa002010000000600002de09db8b007,
  0x8000100000182aeffa3e3f4000004010202000001c3d0bab3f5b1000005010100020020f3c5ede8ec00020001060000007a83f6bd88b300020201010201006f8edaf0f00005000000010201158afa85cff20201010001020200208cfae4c58007,
  0x600010200000192dcd0c48fa6000100070100000001919acbdccdd00005000100000300158f9df3add0000600000000010203cfe2f59dc001020000060000004995b388c4af020003010001020002cd93d4ba88030100000005000002b6bc82b09c07,
  0x601000200000be8ceb2e1bc00000700000101000babc6eda1fc00000700010000010188b6a696f6000101060100000006c1de8699db000301000500000011abd9baa5df000400010202000008af93c886c2010000070100000013fdb1cde28007,
  0x70001010000558297f68080000400010400000039bdd5e993da00050001000300000a8e83eca88a00060000000102000cd5abd99dbc0006000000020001028aaebf8ef30100010700000000538bf78290da01020101040000001185b9fdefa607,
  0x105010200000044c5c385b9a80005000101020000129dd0bd97df0006000001000200028df4a7a69500060000010100015cf6839e8001010007000000001ef886cab1ed030000020400000001c9eca0a0e7040100000003010005a0b2ad86d607,
  0x800010000000d9daf8ebbfa000500010300000008beb78faec200060000010200000ccbdd8efc80010006000200000013db88a4dda0010007000000010003f6acc4e08001020006000000001f8baec2e9d5050100000001000210d89dc08007,
  0x20501010000000198dbb1a99b9500060001000200001ee1d8fad998000600010100010006c0b7d3d4a8000601000100000145f6edd097020100060000000038e0c3b1e6f8040000010400000013b6cfe4d7db050100000000030064b0e890d407,
  0x501020100000010e4e1c7afce00060100010100000b829decedf8010007010000000017ef8ce1cddb01040101020000000aa1c9f9e38f01050101000000010995fec1a6020400010100010001addcdca08c03000105000000000d87ffb292c807,
  0x600020100000042aabb999af6000700000101000027d1e6808080000700010000010004bfe080808000070100000000011c80808080010106010000000001a2c3bdc7afa303010005000000003689def29efd03020100030000001daede87ccae07,
  0x7010001000000529fc784a5e801070000000001000190dff2cae2020204010000000001a584d8fa86de040100040000000025c4c9ac8a89050100000300000039e58a8acf050200000100000105b096f493060000010002000006c38bd9fe8e07,
  0x10601010000000017c0b0ffc18501070000010000000ed6f584a4c0030105000000000022d4e8d7c2ee04020003000000000fa0a89899cd050200010000010010e8b4f09405020100000000014185e8d50601000000020000779ec8b2c807,
  0x801000000000023a9ac879cf803020400000000002cbf81cae5df050100030000000013c3f5c2929805010101010000000dd382e2c1f0050102000001000001c5e3aac6a006010001000001000cb894b1c006010100000000012af5958007,
  0x1080000000000000c9ecaa9a3d504020300000000000bbbd6c6d9c005010201000000000c9e86a0c4800601000101000000028ac7efe080060101000001000017a1de808007000100000001000190b0808007010000000000010380808007,
  0x5010331b0888299c3d30000000000010106011ed0e9f6d3fbb200000000000300020417988f81d0c58200000000010000070116caf5fba9b1ea00000002000000010601d0c3a1d3fddc00000100000001030425cd96edc98400010000000001020501f7fe97848801000000000001010605cbbfffa708,
  0x5030171bfbfc3a8cfd30000000000030004024498dea4b1e3a000000000010100060119a5e3addba2f300000000020101000516b5a4a1b6e1b500000002000100000606a7eba3b6f7b400000100010100000601b1ffe2f6b4ac0001000001000100060b9aaa96f9d801000000010000010627c0cfa3ad08,
  0x10700016fa7e38dd2b8a400000000000501000322d78483dbc4a100000000010201050001bbe3ca9de6a99900000000030002010316c7a5a2b8bcf700000003000001000515878885b1c6b800000200000000050204f0e1eed0dcc60001000000010203026eacc689cd9801000000000100060104a1dca7ad9508,
  0x10800000289f3a698a4a5ed00000000000600010201feb2fed28aa3bc0000000003000105000291908ee1f4c0c800000000040100000406dffbdef2b3d30000000200010202026494fae891ccf80000010100000106002bdffae5b2adb000010000010001060004bdcaaae8c2e001000000010000070019d9fcbe85b408,
  0x701000152b1ece0d2de870000000004010004003e808a8fefe0ad0000000101000700002fa4cd8b96f99100000001030002020126c1b8a28cd28900000003000100050016e9b5b29fd7a2000001000001070000249aaae29ffbc000020000000100060002b6e0f4a6dbc001000000000007010024bbd9b3c89008,
  0x10601010002fac4f481bfea00000000010700000120bdffddcbbe8600000000050001030015d4eac8a0de8e0000000200010600000aede5ae8d9db500000002020100040011c992a7c2a2cf00000101000007000014ccf4b2f4fca80001000001000700000390dfc093aad00100000000010700001ad2cdbabd8608,
  0x60002010003fbb183aca1d1fc00000001000800000003d3d0a0faa2ba8100000004010001030001c883f8f18a8600000005000001020101e4c6dee1cfa9960000020002010202000183fcbbc2baaecb00000201000006000001a98ed0f6d199a900020000000106000035908cbf95e4dd01010000000007000009e48ab6da949608,
  0x1040202000023bfeae6c2a886000000020401000200019db29e92a7ac00000004000104000005abdfec809bff00000006000000010203d0e4aa8e818200000201010201020012cdeedf8fcfb600010000000800000007cb8caaf5aac600020000020102020027dcf2d1a1cd01000101000006000063a588c6f88408,
  0x8010000002baeb7d3f6c2ca0000000600010002002dc982a4ede68f0000000601000001010eb08a8cfda7d2000002010202020000018bcb9b84d2d99300010001040102000028c096f7aabaa90001000200060000002295e6baefffc700020001020200020001d1b3d1efb680010001000007000000099bd881c1e6d208,
  0x1080000000001aff5b4fa9de5c000000006000102000001bea684e984aa800000020104000200000dc5ecc2d5b49900000202030001010001c7989ddbd2b69000010200000600000001e3a0e6948aaca800030100000005000010f5da9181aff80200020100000200020be3b0bae9b4f703000000000105000004b2c78ec0f58008,
  0x10600010100002cc7a8d293a6b60000030005010000006bd4afe8efa1b200000600000100020024f7bbc8ebadf000000600000101000106fdcdccfeb8a400010004020200000001fa93d0aa94c89500010202020002000001919990af82f7cb01000001070000000017e0d4e6f8f3f201000300000500000029cdb98f839eb208,
  0x8000100000003d3d0a0faa2ba8100000600000102000001a98ed0f6d199a900000601000000020035908cbf95e4dd00000700000000010109e48ab6da949600010200060000000003fbb183aca1d1fc0002020102000200000183fcbbc2baaecb00030100010400000001c883f8f18a8601020100000500000001e4c6dee1cfa99608,
  0x70000010100006ad3c7c4f6bed900000701000000000101a4a888a8cde50001010601000000000188c0e5bdc9f6c500020202020100000002c0a59b8ce0e8b101010006000001000014b1b0f585bff30200010301020000000fdac6b3d6a8c302000203000100010013a7a2a0f79c9802010000060000000036f9fe86e38ffe08,
  0x1040202000000000290e8dfd0bbe6de00020401000200000001ddacf091a1d4e10004000104000000000ccca0a2bcd4c90005000003000100005a90eddddda4f80006000001000101000dfaed9cdece9000060000010100000168ebd1849fae01000107000000000001a7d1cad4bfbf8c0300000105000000003bfdfacbe69eb608,
  0x2050101000000001bb7f3a4b3d0a68000060000020100000006fee4e890c8e5eb00070000010000000101aac3d9f49ef90201000600000000000be48497c1febad304000001040000000019c3d5bac2dada05000000010300000001f1c381b2e7b49f0500010100000002000eeedf9aabfafc05010000000003000060e0c3a09e90d408,
  0x10800000000000004efcff8c9afb3000600010200000000029d82a1ae93c600060002000100000003818193878a880006010100000100003bc096dd82dc00070001000000010005a0ccbdb4b800070100000000000119fea6b98102020201020000000003edbf8fc2fdfd03000105000000000003e3aaa9fdc4ed08,
  0x7010001000000001680e8adc9b0b801030500000000000014bd99cde2dbc701060100000100000002efa2a48a9fd202050100000001000036e2b290def00400020300000000001ad59aefe6a6b405010100000200000040f7a09fbca705020000010000010003b9aac291e00600010100000000010c93f1818408,
  0x106010100000000001f91a58bc6d48201070000010000000016a5a8e4bbe8e603010500000000000031aad8b5e5a6f70402000300000000001782d0cfffd29205020100000000010001f7fe97848806010000000200000001d0c3a1d3fddc06010000010001000025cd96edc98406010100000000000105cbbfffa708,
  0x2060118ce8efa8eeef4eb000000000000010007010fb7928edafe9fe20000000000000103010429e0a1c7e2d0bafe00000000000200000205059a91eea7b48b900000000001010000010601dab482cbefc0c00000000100000100010614c0fd9ec7e28000000100000000010106019eb9c380bc800001000000000001000705ca91d7ba80010000000000000001070b96c1bc8009,
  0x10008001da4cedbd7e3bcdd000000000000010400043faac0fdbad6d183000000000001000007011683f1bfd9daba800000000001000000060202cf9bbfb0f090b8000000000100010101056bf4c1be91a4c8000000010000000201052eb68ca481af8000000100000000000404039097a5b6f9c0000100000000010000070fdcabfe85d8010000000000000100072391b6e9ac09,
  0x60102719099d2d1b7e7f90000000000000400010458f589968498dfc000000000000100010700669eb7e79be2d08000000000010000010601129d98d5c689f8de0000000002000100000654a887c88b85d10000000100000000070102beedfde2eafe80000001000000010003041a9080adbcf7c000010000000000010304019fe9b6f0c7cc0100000000000100010603b2c6e884ef09,
  0x602010bcbc1afb49783df0000000000000202040124a29fa79a80cb910000000000030001000507decef79ebae7c00000000001000001070001db808ec4fca2c40000000002000100010501c58f8cf7cfc79e000000020000000100062ba0aab1dfce800000010001000001000607dfcabacab8800001000000000002020433e6a3c4ec80010000000000010100060199f7f4b88009,
  0x10601017e9ed5eb97beaed3000000000000050001033ef69986c0ecb1ad000000000002000106002caaa2e0cae7b88e000000000003010001040d9bb0f89bf5dacc0000000001010000070029f2a6f0f68080800000000100000100070006efff94c0808080000001000000000107005ceae8808080800001000000000001060105dba0808080800100000001000001000614808080808009,
  0x2050101058aa08080808080800000000000020100060002cfa7b0f9e2ccaebc0000000000040000010417d0a4d5c5d9e8e2000000000100040000045ddfb7b694eb99870000000003000000020427eba0cfa4fcd39b0000000100010000070025e288f6a48080800000010000000100070004a6a7a6cde880800002000000000000010612a2e7848ada8001000000010001000006018a86fc9eeda809,
  0x108000001d2bec0b4dcbbb8e70000000000000600010201c8b5a2cbd295f9820000000000030001050001d39cabd29ffec7a8000000000004010000040ddeeecca999a99f0000000002000102020254dada9387ac80c0000000010100000106002bbff082ef81ebc00000010000010001060005dba1f185929de00001000000010000070038838eab9de4ac0100000000000100070001f496decdb3ae09,
  0x6000201038f95bee596e9c2d10000000000010008000003a99eaf8f80b7cd98000000000004010001030180e9eca9e383a29a0000000002010000060001d59af8b495dac8800000000100010201020228d9a6f8da9f9a800000000100020000060034c194d893fbe680000001000000030102020d8cb4dfa5fc8080000100000001000106000189b4cafadc8080010000000001000007000580dffef0808009,
  0x700010162f68b99e2949ec00000000000040001040018d3bcbaa786ed800000000000050001000326aaafbdb8cdb4be00000000010001070000018799efdfbdf0c5bb000000000102010104003cbdb1bac9f78dc50000000100020100050030d2b7fde6bb84800000010000020001050007e38387b2e3a880000100000001020102025ce0e9f4bb94800200000000000100010501f5f9ffe1b48009,
  0x701000101afc2ecd1a6a8d2de000000000004010004007cc388deb4afa5b6000000000101000700003ce18eeea1c8a9eb0000000001030002020165bebea2bad2e7ff000000000300000204003c84b6edaedbbb92000000010000010700005ac0eac8848693a00000020000000100060007d8b6ba91fff2980001000000000007010001c39884f48fb6d20100000000000007000108ccea92ecc9a309,
  0x800010004c3b9af848989bfa10000000000060000010201c8c2f591cff2a3ab0000000001020006000001aca6faeef6bc84da0000000001040000040003839ecbb6ece7a2d6000000000400010002026d9e85dffb91de940000000101000007000003a69ebfb2d3dce0800000010000010007000050e4c3d1edb48480000300000000000001050380d8cea4a1aed001000000000102020201399fbcb4d193f209,
  0x801000009babbfecf8fad9d00000000000500020200019195dcf3e9be00000000000600010002089791e7bab281f70000000002010006000003acf480d4e6c4940000000002010202020013b780c4d5d3a9ac000000010002020202000faba19595c4ec8000000100010000070000038de093cac1e880000100000001000700002f80f282febc8002000000000000010600019e82bd8db48009,
  0x10800000001e488a6ae91ebd1ad0000000000060001020001b882f0d3b1a6a9ca0000000003010102020001e9bbba8497d8aefa0000000004010002000228f1fcf89ceeae9d0000000200010006000048d591d9b0cfe5e2000000020101010200022ee091adf5ef9a9e0000010100000106000048dba1b5b3c880800001000100000007000009cda1b2c39880800100000002000102020148949acaa0808009,
  0x70000010101a5d7c6f398f2a9a50000000001000800000048e0b4ededbbc4d00000000002020202010005a7eff297b7baf8c50000000100010600010043b7f4fbcdacd9b4000000030000000501000198e3fbbb988284e20000010000000602000075b4b192a4b69d9a000001010100030100020aecffa79280cea60003000000000101000405fafeadaaf8a5b401000000000104020001018deb97999ba4bf09,
  0x1040202000056e6fed4899cccfe8c000000000106000002007597d193d8c59cf0000000000600000001020783a9b9fcd4d1d8ea000000020200010202002d858b81c3b1ea9ff40000000500000000010315b1c1f9ba87f098000001000000080000001485fecbecf992bdb00001020000010100020202878a80fe9bd096f00003000000000100040132879fd8d3fbec840102000000000000060021829abdadb6c8a109,
  0x70100010003ded193fbc5f1c8000000000008000000010ebba5aef284b8f5000000000202040100004ace96a18cf9cef00000000200010402000002cdff90829f83940000000201010300020008cb93d3b5b597b8000000020201000202001d96c7e4c8abe5b4000002010000000600000d989a80808080800003000000000002040001b7e08080808080010000010100000600002880808080808009,
  0x80001000002e9bff387b9a389bd0000000006000001020001a79e99f9ddb497dd0000000006000002000155bde8a5b9bcb8e50000000201000501000003bcb8a4aaf6accdb0000001020101000202003182e9e4bf8cd3a8000002000100040101007c8491f681a0aedc0000020100010005000008d4b1ade5ded7d0000200010000000600001cece0bd92f38d800100010100000006000004d1d1969ea2ec8009,
  0x2060000010002a1bacac98eceb1d80000000006010000010119dde08d95eed585000000010202030100000a89d8eba4c7d88db2000000020201020101000381eda6b6bcd4c3bb000001000007000000013beba181d1d8fecb00000300000100050000018d93e0adbd88ccb30001020000010102020056fbf1f2edcc94f400020001010100020002158d8ae997aa9a98010002000000000600000af5e7a4bafbf9ea09,
  0x1080000000005eaa4859dbbcbc0b00000000006000200010001afbba09ce7cdef9a00000000070000010001018786fedcf5908080000000020201030100000ca4aca2be8491d8fc0000010202010001020003a7a9f59fded788b30000020001010401000003a3bbfa9fdad0c5d60000030100000005000013f7bcf4d7f6b7a2000201000001000500007bc7c9bec785c5fb010200000000000600001cb2d1a4d1c2bbe709,
  0x7000001010001f0fceef4f3f9f5820000000007000100000126b1f0f5b2e9b5990000000100080000000002c998aef392a988e70000000301000500000002ccebdef7c6e0f1c100000200020102020000019de19bfbfbb6a4950000020200010004000064f6eb869d87a893000002020100010102000399f890ecedc6980002010000010202010039f9e1b5e7a6ff80010100000000070000000ccfaa8fb1a2c48009,
  0x7010000010008d8bbaeeacbb6f4000000020204000100001db3b48d8ae4a2a100000006000000010200598088d681e9e30000010300000500000004e28888a3a08eb40000020001050000010010ded6a0e3e396000002010005000000010194f091bebea9d20000020102000202000004f0b89ad38debfe0001020000000600000008cbdaaa9080808001000101000006000000779ae58080808009,
  0x204010101000006af9da8e487f3ca0000000500000301000037b98bd481d1af0000000600000002010019e38efeb0808080000001000402020000005493979ea7f79a9a000001010007000000001389a8e7918dde8a000002020002010200000895d6edee8099ee000100020102020100001ed1cec3a698c8f00100000202010200000102e5d0af80808080020000010000050100002cc082ddddbebb09,
  0x80001000000039bd3a2979dacffc0000000050001030000001491cccf80c2ec910000000600000102000001c0cbf0b6ecf091f900000006000002000100018ebeb6bef1ca90d50000030100020201000002879b82b1b7f88ce3000003020001020000010c90c3c3e4eca1aa0001010000070000000002cff8b3f985c7cbc9000500000000000101027da8acd2e08fab010001020000050000002aeda1e2a6efdc9009,
  0x8010000000002da87ef98e792e28e0000000501000300000002858e88c0daa7b8da000000060100000101000191e3c6b7cedbfdc4000000070000000100010dcfb8d7a687f9a70000020102020200000002c8e0a6c3b4869af90000020400000003000061bbb882d3be9ec70001010001060000000001f8d2deb7d1ccf3800001020100020201000001f1d1d1aff9af8d800100010000070000000040e4918a9d90808009,
  0x108000000000003bca6f7d7bc9093bd0000000600010200000003f7e68288c1d1dabe0000030001050000000016f2e2fbadc2f394000004010002000200000296cca2d2abbfcc800000050000020100000108faf5c8cad281c00000050001010000020034ff9a88daae97c00001020002020200000002da8ad88795f2fce2000200010006000000000185c0bfc1efad81cf0101000001060000000068ebd1849fae808009,
  0x10008000000000002adeeacede0888bd90000010500010200000003a19382aad3bf8fda0000020301020001000061c5accdbdd997f00000060000000100020019bfaec7f2f7ca800002010000060000000001a7cea49e85c7b9fd0002020001020002000043b29ad1e8d492e20101000100060000000015e9da97a4ba9dae0200020001000202000018e7cce0a4fa8da6020002010101000000020286a6ec87b68c8009,
  0x10402020000000005b2f2e6d0eaf2c1b0000006000000010200006aa3cac088fc8cd00000060000000200010028bde080808080800000060000010100000102f88080808080800001000107000000000020c4f9e8bf9cc8f00002000301010200000074b5cafd88f8c3d00002010102020001000023b386ffee87e6e00002020001020200000001e7b9f0baf2c9b688010000000800000000000187fa92b8e39096ff09,
  0x10501020000000007d188b4d9a8c4b80000020401010100000001e795efb8b1d2e9930000050000030100000049fee4faad8cad000006000001000200000e8b969dd186bfee000101000700000000005ddb83fc8782d3df000106000000000000022a8abaf088afd90002020101020000010009c5dd8ca0eef99c0004000000040001000021b3e1eac2bad4c40201000000060000000018a4cff7a6a7bc8009,
  0x800010000000003968792d3e99cc6bc0000050001030000000002bca4bdb287ababcc000006010000000200004ac8feb39fd2bec00000060100000100010014e5cad0e09ad8e80000070000000100000101a4f6d6c184f7ea0002000106000000000021c3c09eb5888ef90002020102000200000001dc8d8aaa8e98a5ff0003010002020100000001a1da83d1dbad87b00101000007000000000001f6f3efbcf9a0808009,
  0x801000000000005fdb7d386fce5cae9000103010202000000000b88b8b5c3c0faf69b0001050100000002000073b781f4b3b5809500050000000103000000028ca4ebdebcd2d8c20006000000000100020011a4d5daf8f880800100020006000000000003b18f95a184e48ee90100040100010200000001a6ff90b3e2bdfb9d020200010101000200000eb895ef8a92ffeb020200020100000100010283e2acbec0808009,
  0x60100010100000002e48b959e93cbbdf20001000701000000000005e98ad4b8e7a5e8970001040101020000000007939fa6ecaf8b85eb0005000100000300000055e5ead7f497f3e20100040201000000010010dae8c487faaa800102000006000000000003f58999c8deedb4e50201030001000100000170abe1b8c3fc80030101000001030000001bebe1a9a3e1def8030102000000000300002f90c7d3d4e6948009,
  0x60002010000000051d2b8c284ebfcb50000070000010100000001d38f9fd9a9eeb0800000070001000001000028b2a1e8f6da82800001000800000000000002a1ddfe86a8d29d960004000004010000000001c1dca7869fbab8e20100060000010000010004c184f5b6b285f80201000006000000000065ddf3a38de1b0ad020102020001000000011ccfde9aa8c9f90202000100040000000036c4cecddcdd82de09,
  0x70001010000000002f0c7f5bcb9bdb9c400040001040000000000018ae6ed92d390b09c000500010003000000004b95a39dcf94e2b2000600000001020000005ac0eac8848693a0000600010000000200000dedd4efaff0adde000600010001000000011199d4a5d992c6000601000000000101000386b089e89eeda40100010700000000000002e1b8a3d5f7d0eaed0102010104000000000001c8dbcbe5efff9d9309,
  0x7010001000000000395b3d5a3868190b1000401000400000000004a81d0becfd8cb800004010102010000000001b5d28eab91b5e8cf00050001020001000000018fe185bbd5ffd0800005010002000001000017a9899698a9f880000601000000010001000296a2bdddb1bc800101000700000000000002a9d786b8cee6fbc0020300020100000000010bc3dbfec8b880030001000500000000007493cf8d858799ba09,
  0x1070000010000000007f2a0e29fd3ae8a0002040201000000000002f3c7a0e184f2ab000600000102000000000feb9691ddcd88fb0006000002000100000008d5e7e3e6c48080000700000001000001000ce492f0d08080000700000100000000013bcdb2c08080010006000200000000002ab9cd91e0e79aad01020006000000000000288498929dbad0c7010600000000000200004dfcbffbe8808009,
  0x205010100000000000181e3c5c5a8a1c7f600050002020000000000138bb29b929bf3d5000700000001000100000299a0dcdacbf7e00007000001000000010015c68fae95a6cc000700010000000000015df586ecc4fe0101050002000000000020e8eaeda781b08a0105000002000100000010ddbee3c89e9fc00201000600000000000044f2bbb4b9b383fb020400000003000000001ac8a19182aa80a009,
  0x5010201000000000003aabfea998cfcfa9c000701000000000001001bb49ac690878001000701000000000000028ae9f0f1e9dde3b5010501000100010000001ca9c6d8db80808001060000010000010000039cddbcfaae80800106010000000000000167c59d9791fe030001050000000000004ea6aef8e5d4eeb70500000003010000000030858ff5df9caccc0500010000030000000025a6ee98eaf6c6bc09,
  0x6000201000000000016958fb0a5b3dc870007000001010000000014f99db8bb8080800007000100000100000003b7f5caa0808080000701000000000100002eb5b4808080800101060100000000000042e89a92fcd2bc800106010000000000010002edd0808080800301000500000000000014b0c6eb8ddcaad3040100010300000000000dffb0f6efe1b6d3060100000000010000010a808080808009,
  0x7000101000000000002e7a0e1d491cab5a80102060000000000000003a7fcd0f8a1f1b6af0400010400000000000001fcc0bac18185838e05000100030000000000088cefdace9ddfc8060000000102000000002cecadb4b89184a006000001010000010000018fa8a1bbe18c800600010000000200000006a0969098a8e3800601000000010000010007bea491b9ce8006010000010000000001169feaaa8c8009,
  0x7010001000000000009a5d6c3c8abf0800106010000010000000001d3c981a182e5c2010700000000010000001cfeaeabf2ba80020106000000000000000aa3a9faf4fa95f704010004000000000000088d93d1f0a6a0800501010000020000000006dfc3f794c7ff050102000000000001000ec3e28a9de40502010000000000000127c0cfa3ad0601000000010001000002b080849196c009]

/-- The triples `(n, b, a)` of part 11. -/
def enumC11 : List (ℕ × ℕ × ℕ) := [(9, 54, 7), (9, 54, 11), (9, 54, 13), (9, 54, 17), (9, 54, 19), (9, 54, 23), (9, 54, 25), (9, 54, 29), (9, 54, 31), (9, 54, 35), (9, 54, 37), (9, 54, 41), (9, 54, 43), (9, 54, 47), (9, 63, 8), (9, 63, 10), (9, 63, 11), (9, 63, 13), (9, 63, 16), (9, 63, 17), (9, 63, 19), (9, 63, 20), (9, 63, 22), (9, 63, 23), (9, 63, 25), (9, 63, 26), (9, 63, 29), (9, 63, 31), (9, 63, 32), (9, 63, 34), (9, 63, 37), (9, 63, 38), (9, 63, 40), (9, 63, 41), (9, 63, 43), (9, 63, 44), (9, 63, 46), (9, 63, 47), (9, 63, 50), (9, 63, 52), (9, 63, 53), (9, 63, 55), (9, 72, 11), (9, 72, 13), (9, 72, 17), (9, 72, 19), (9, 72, 23), (9, 72, 25), (9, 72, 29), (9, 72, 31), (9, 72, 35), (9, 72, 37), (9, 72, 41), (9, 72, 43), (9, 72, 47), (9, 72, 49), (9, 72, 53), (9, 72, 55), (9, 72, 59), (9, 72, 61), (9, 81, 10), (9, 81, 11), (9, 81, 13), (9, 81, 14), (9, 81, 16), (9, 81, 17), (9, 81, 19), (9, 81, 20), (9, 81, 22), (9, 81, 23), (9, 81, 25), (9, 81, 26), (9, 81, 28), (9, 81, 29), (9, 81, 31), (9, 81, 32), (9, 81, 34), (9, 81, 35), (9, 81, 37), (9, 81, 38), (9, 81, 40), (9, 81, 41), (9, 81, 43), (9, 81, 44), (9, 81, 46), (9, 81, 47), (9, 81, 49), (9, 81, 50), (9, 81, 52), (9, 81, 53), (9, 81, 55), (9, 81, 56), (9, 81, 58), (9, 81, 59), (9, 81, 61), (9, 81, 62), (9, 81, 64), (9, 81, 65), (9, 81, 67), (9, 81, 68)]

theorem certs_ok11 : checkAll enumC11 certData11 = true := by decide +kernel

/-- Certificate data, part 12. -/
def certData12 : List ℕ := [
  0x8000100000000000002e2d5c3daf3d9db0107000001000000000005c0fcaff6b6cec0020304000000000000000dc6a38af5fbb1c60500010300000000000006eaeba7d3dfb897050003000001000000006ee4809be0ada0050201000000000100006485e9addeb0060001010000010000000bcdc38980abe00601010000000000010003f78affc1b60700010000000000000108e4addaab09,
  0x107000100000000000006a7b6bfadefd6eb0204030000000000000025ceeeb194f7e780050100030000000000000acdb29ac5c1ccc70600010002000000000003bc8bf49aa2dce0060100000101000000000191cdacb2caab80060100010000010000000dd5fe94afec800601010000000001000069d18280a8800700010000000000010003dc8be4fc800701000000000000000107b9d6a88009,
  0x5010314cea8cda99dfafae400000000000000010106010bc890e29beb82989a00000000000000030002040aaae6a0c1b8a0daaa00000000000001000007010a95f48ff08dc5eed000000000000200000001066ef5b6c1a799f8d6000000000100010000010619dee1b8defca6a20000000100000000010205028693a9e3f4cc9800000100000000000101060dd88cc1af99ed0001000000000000010007369bb28bc5b2010000000000000000010760cff6e1d90a,
  0x6010202efbad2fd85f88aae97000000000000000400010402a5accafdc4b9a0f693000000000000010001070002dafbd7ebd3e8dbaba800000000000100000106012afb93b5f9b9ddd8dc00000000000200000101050dd5a2cc98b387e4ea000000000100000000070109f1f4aebdf4b4e3a800000001000000010003047a90b9d6f9f2c8e0000001000000000001030407dddbe0dcf4e1a400010000000000000102052590f6c1f59e880100000000000001000007509fa183e7b40a,
  0x20501013a95b097a1d4bcabfa00000000000002010006001e95c19b92adf3add0000000000000040000010402aae988ca9ad09e8b000000000001000400000408c8d3ff87d1aff6ae00000000000300000002040480ee8df0eda9ebae000000000100010000070003ffb3e1f4a3f2f3a400000002000000000101052283b8eeb7ff90b8000002000000000000010602fcadc1e0c0e6bd000100000000010100010527aefeb6e695f4010000000000000000070175aca9cdb6c20a,
  0x108000005edbfa9b9bfd0fad1c5000000000000000600010205c6b9f0f0ebe5d896f8000000000000030001050005de93e5e5ea92bc9df800000000000004010000044a9f97a6f09695a7df000000000002000102020202bbd08abbf4a1cde0c4000000000101000001060001b596b0c5fbcacbc8e800000001000001000106001bda9bc1c796ffb9e0000001000000010000070002e3efb0dc8cf38ce400010000000000010007001594eca1c2d5e2a8010000000000000001070048bee08afd9fd40a,
  0x701000105d5a2cefef2ea92edd8000000000000040100040003819c9987f0ded0999f000000000000050001010201db98f79088e7d894c3000000000001010007000005eacfcee1ad938489cb00000000000300010005000192e9daaacdd8cbd6a5000000000201000000060001c7faa8e2acc6c6b7de0000000200000001000600279cd191f6dcfea1a800000100000101000006000a8cd08ed2d0a69ec6000100000001000100060062cdee81d187affc010000000001000001060003b1a4e9f2c5cd8e0a,
  0x60002010009f5a8cbeff29ef7f082000000000001000800000009d7f0beeca0ac94ab80000000000005000001020105b390c6e8ecbcb0f690000000000200020102020005b9fa959f9092d8b28d000000000201000006000001fe81b6f9ce8ee6bcce0000000002020001020002508f9ee3b2b5d8fcdb00000002000000010600000298b0c18485ddc3f6e8000001000001010006000063fca7fcdca2f68fce00010000000002000600000ac7f1c98ca887e8bc010000000001000007000040a2c8c1b6aec4c60a,
  0x104020200003da5d8e98fd2858c8eeb000000000006000000010204b68995f4f7e38b80f0000000000202000102020022a3e586f0d9bbfe8ed800000001000000080000000ddd8e81deadd5dd96ce000000020001000006000016ffaadaceb880b3d900000102000001010002020394dd8cc7b38a9acb84000002000000000106000007dbc7aac0b9e39fe60001010100000001010202169faae68cbad7c8b8000102000000000000060026afbde189cd82a0f8020000000001000000060001cbead596e8c7838c0a,
  0x108000000000782eaec96d6df9693b7000000000006000200010004c2b09cccd2d782bdab00000000030101020200007bbce8b3ac8889b1e1000000000401000201000101b3cd83db99fbb4d7ba000000000500000101020001dfdde49591e786e28000000001010201020200000b88a9d6cae58684aba2000000010200000600000001fed1b5aee6d497918a000002000100010202010001e3fdd4b19fc9aad2d9000100010000000700000046dea29de2cf8dc084010000000100000700000004f88bc8ccd793c4fa0a,
  0x800000001000bfae7bdc1fdf5908eb600000000040100040000000f86b88f9ed1db93ce92000000010100070000000012df849fe7fbf988d4e400000002010201010200000df7ada3f4cee583f3d0000001000202010102000008decfc9dfe480cae8cb00000200000200050000001a82ce97af9a96bca900000300000002020101006d97d5bd80c6edb4a4000003000001010201000101c3fff2fcb8f9b7a3910001000200000006000000038a85cad4e6f191b1da010001000001020202000020fca4e7dfede3b5810a,
  0x8000100000009f89aadc6c290ea99a2000000000600000102000072f2d6ecba999f95d7000000000600000200010004c0c2c0d2a1b7e89290000000000600010100000135ae89fad68c9ab0de00000002010005010000000bdfe88d9ffd99a5c9c50000000202010200020000059288edb5bccbf1878b000002000200020102000003de80d3f690e29cc08600010200000000060000000287da97c38cf7a6949000020000010103000002000c85f798add8afbab502010000010000010201010de5f6ca98a1f18efe0a,
  0x601000200000003f8a6e0c7b4f9acccd7000000000700010000010001d1e6f7fecea8a5d98000000000070100000000011398f8bad9b4daccc0000000040001020200000006afa5a0fdd5eecf8db00000010000070100000000048dffd3a18fa8c983b800000101020202000100000887f8e8fc9387d796c0000003000000050100000006fbafb8ebfae8e586000101000102020200000001b4ebebb099bfcef9b6000200000001060000000063f6d9fea28e9cf7c501010000000007000000002edbea8ec1d29390c00a,
  0x10402020000000008f0adca988ac9b8f5fe0000000500010003000000029a8aed8ca8cdf9cdcc000000060000000102000001da89db9cc5d79bbcea000002000301010200000003c8a0cdb891cab2a3c6000002010102020001000001dead8c92e0a3edc5b700000202010102000000010a9fb1e285f5ffe5e700000202020100000002003d9cacc0c2cdcce9db000100000008000000000002cadcccaecfefeaf4f3000102000000060000000001b2f0c29bc688e2b5c301000101000202020000003cf3d6acba98dbd4d70a,
  0x801000000000003caa29be1cb9a97a6ab00000006000100020000000482a9feecefbbdab7a1000000070000000100010037ad85e2bedb89f8ea00000201020202000000000bdba5bbf4c5e595cbf000010002000600000000005fc1d694efad8ff9ee0002000102020002000000018babf3dc9491cfb7820002000201010200010000028edb9e9388d6dd97cc000201020100000102000031bf97f8abdfd4ecf00100010000070000000000018dcf9fd7dde6868f8002010201000000000001020280a0aeddaddaf9ae0a,
  0x70100010000000001b39cbfd6b098dba8f900000500010200010000005bd7fd8798b2fde285000005010002000001000026f7e4f59389b1b1c900010100070000000000005aa299f5bab6b3fcae000102020102010000000003def987e0f6e9f199a1000201020102000100000069f68bafec989784f30100000107000000000000018087c8f4f3b4a69f9a01000300000500000000000eb883faa096e4fef8040100010000000000030001c1fc9bb0c6cbec9e05010000000000000000030a98c4a19283c6c70a,
  0x80001000000000007b0ddc0d0e8e3a3d4be00000700000000010100004f8681ebc5fdeca494000007000000010000010008acf7c8d790e5b7e8000007000001000000000132e8dd878a9eebe4000102000600000000000006e3e696d0819497bed7000104000004000000000004f9d9958e978e95bb9b00020201020002000000000691b89beef2e1d7c2fe02000101030002000000001ab9f18380dcacaa92020002010200000200000001b695f9f8cb9bb3d4e602010001000500000000007ffba8cfe6898bc7fa0a,
  0x7000101000000000005eacfcee1ad938489cb000400010400000000000003819c9987f0ded0999f00050001000300000000000192e9daaacdd8cbd6a5000600000001020000000001c7faa8e2acc6c6b7de00060000010100000100000a8cd08ed2d0a69ec60006000100000002000000279cd191f6dcfea1a8000600010001000000010062cdee81d187affc000601000001000000000103b1a4e9f2c5cd8e010001070000000000000005d5a2cefef2ea92edd8020101000500000000000001db98f79088e7d894c30a,
  0x8010000000000000005edbfa9b9bfd0fad1c5000501000300000000000005de93e5e5ea92bc9df8000601000001010000000001b596b0c5fbcacbc8e800060100010000010000001bda9bc1c796ffb9e0000700000100000001000002e3efb0dc8cf38ce400070001000000000001001594eca1c2d5e2a8000701000000000000000148bee08afd9fd4020100060000000000000005c6b9f0f0ebe5d896f8020202010002000000000002bbd08abbf4a1cde0c404000001040000000000004a9f97a6f09695a7df0a,
  0x108000000000000000003afd892a2c7d0fee3a2000600010200000000000001b293f6bee2a2ecc9ce0006000200010000000000028bd1fe9bd4ace098fe000700000100010000000033f8a0f8e7d2d5dad4030001050000000000000002c7a8a9f0e3a2abf28604010000040000000000000189afc2b9a5e596d289050001020000000000010003ffe2ebc8b09ce4050101000000000200000003baace39bd7f4d5d805020000000100000000010bf5c09ceec4da060100000000000002000026d0cfd6e6cab4990a,
  0x701000100000000000002dafbd7ebd3e8dbaba801060100000100000000002bac87ea80de89af84010700000000010000000009f1f4aebdf4b4e3a8020106000000000000000002efa2a2879ff6b1eac5040100040000000000000002a5acc1d9a6e8e3ced1040301000000000001000007dddbe0dcf4e1a405010100000200000000000dbce8b294e0f1f9d605010101000000010000007a90b9d6f9f2c8e006010001000000000001002590f6c1f59e880700000100000000000001509fa183e7b40a,
  0x1060101000000000000000bc890e29beb82989a01070000010000000000000a95f48ff08dc5eed0030105000000000000000014cea8cda99dfafae404020003000000000000000aaae6a0c1b8a0daaa0502010000000001000000028693a9e3f4cc9806010000000200000000006ef5b6c1a799f8d6060100000100010000000019dee1b8defca6a206010100000000000100000dd88cc1af99ed0700010000000000000100369bb28bc5b2070100000000000000000160cff6e1d90a,
  0x503010586f580fcc8f8fac4fbdf00000000000000000200070001e59d94b7d198bfdbd8c90000000000000001000107007894d788ce94ea8caba200000000000000010300000502d4b8cca2fc8e9cee8dbe00000000000002000100000630f49089978eeafa83c00000000000010000000105020ee4cca6bfc5fccec8c000000000010000010001000601ccace7d58ddcabada00000000100000000010100060fb8fbf6e6fee5c19800000100000000000100010663ced6edb0888bdc0001000000000000000101060381be94c998d3da01000000000000000001000705a68890d9e3b10b,
  0x602010bdfa6b994edc7a7e2c0e9000000000000000004010004078fc1afbbefa7cef1e8e60000000000000001010007000a96c2938e95b3938af8e00000000000000003000100052eccd2b4ecc7faa6dde000000000000002010000000601bbfbc7d5f1e5bfd587a00000000000020000000100061efae091949fe3aacfc000000000010000000001050207a4b4deb1f8b5bede800000000100000000010003044ce4dc8d92f9eeca80000001000000000100000106049bceec928ddbf48000010000000000000001020511e3a397e4df98800100000000000000010000072288dee8bab0800b,
  0x8000101838596b1f5b48ab4f5800000000000000000050001030182cbcac0e9b2c3a88b9d0000000000000002000106005d8086cbe6f5a2f0808000000000000001010000070044c1c8bbdee1bc8080800000000000010000010007000192a2e6e896c7f98fde0000000000020000010001050686a5a9acc1fc83b89100000000020000000000020574d7dd97d48080808000000001000001000001010516bf96cbc08080808000000100000000000000070101b980f880808080800001000000000001000002050791808080808080010000000000010000000007108080808080800b,
  0x8010002e5a8b5e899e29ddabeb600000000000000000501000302b689e9c492a7979ddf910000000000000002010006000399db9eeed6d2d4fdbf8000000000000003000000020448c5f0fbbbaaa5f4ecaf00000000000100000101060008eec78281bbf6e0f1cb000000000002010000000006149981eac9fdf2e5a7f300000000010000000100070007a6ccc1b287c3b5c1e000000002000000000000010630b8a1868dd4a394fc00000100000100000001000606d8f98fb4f0cbcff400010000000000000000070123c48af8c1edf48201000000000100000000000755dbf0b287a99b0b,
  0x10800000187e1eef6acfbe8d18fa800000000000000000402030004a78191fea9beb8c1ed00000000000000010500000337e5fecde392f5d7c1bd00000000000000020201030101d8929bb7dfd885bf9cb600000000000002000101040151a49e8ac3d98880808000000000000100000201050026ce81beccfaa780808000000000010000000102050006c6b0a0aae2bb98808000000001000000010001050163c7aa9ed6f29da08000000100000000010000060107f0ecb4c7f985c2800001000000000000010104022ff5e587a0f9c5b00100000000000001010001050184b7c89487a3d70b,
  0x601000202bf81b6c7dde49aaae5e900000000000000010106010003f2d3e4ba808d95fddbb100000000000000030100050001c0dbac81c3f9fb9aa7d90000000000000004000102023ca283d8accdc8ddafb10000000000000300000005010198a4fcf696fbf795c0800000000000020000000106003b97e7a586c0ebf380800000000002000100000001050ad9f99be1d9a28c808000000002000000010000000601adb2b6d38cd48880800000020000000000000100060ed190ecc1dea0808000010000000000000100070001bdd7ca96ee80808001000001000000000000010604aee5c9b88080800b,
  0x701000106a7aff485e6b3e6a6d1c000000000000000020204010004cc82f5a3afdb8ee8bd8f00000000000000050001010203efdfc295d9b980b7e0cc00000000000002000104020008a091e9b6b9f2cfe4f0c900000000000100010104020002a5bfdff985bfc3e9decd00000000000100030000050002d9dfb1a3e6e6d383c1b30000000002000000010006003bd0a6cb8aea9be9fc8c00000001010000000001060012e6b1ced0b7e4e59ce0000001010000000000000601028dfe89b98d90a6eaa000010000010000000000060110abd690cbf4c3838801000000000001000000070039c5f2889b9f9eee0b,
  0x800010004fbe58c9e94e8f5b39c9500000000000000040102020075d5edfae5add5d3e3a300000000000000050002010104b0c896ede484e3e3a69b00000000000003000004020004cd84fed69ebf98979e8000000000000200010102020102aabfc8fac4cace9d939d0000000001000001000700000185fffbd6ede7828bd8f80000000001000003000202010a8894818f9bbce7a6c800000001000000000107000018aaf1ad90e5ce8ae3b000000100000000000106010002dee3a0979cdeda80e800010000000000000007010017d9ddece7ffbdb7b40100000000010000000106005d969cd4aae0dac60b,
  0x80100001ca3f3b4fbadbfc4ae99800000000000000006000002011b88c39adc94c9fcfbdb950000000000000201020202002ef5df8eb598b1def4a9b20000000000000500000001030990b3d5b6d79af7e1d80000000000010002000600000ebbe3cf8ba0b8c191a6b80000000000020100010202010df8d9a9acfc81e3eabca40000000001000100000700000ae394f8e8b2e7fa9cc28000000003000000000001000551ef8ff895dc8bacae800000010000000001030200021d94a59ec3ad89a6cc800001000000000000050001020289eea88699d3e3988001000000000000000007010008cded9b91f1bfd0800b,
  0x108000000089afa94d2b29abe9e8bb800000000000000060002000105dadbb593c7dacfed8fc30000000000000301010202000887b98791f191acd1f5f4000000000001010201020200098ebad0b2ee97e0edd8e100000000000202000101010276ecd9efa2f181c6afb40000000001000300000202017894e3b699bb9dbcb7c90000000001010000010600000395d08dafde84ce8bc8b70000000100010000000700006ab7ddfcadd7fa9080800000010001000000020202010dfef4f5a787adc08080000100000000000100070000018da0d49ff6be80808001000000000000000107000005889bf7a7e88080800b,
  0x700000101268fe0a9dab2929d9b84ab00000000000001020402000001b3dd99b3aae0f2c48493e60000000000010201010202000195b9f1b28298bcec88d6da0000000000020001030200010dd2c18acea9e2acab94e800000000010100010202020015cdd6c8bea5f4c898f7960000000002000001030100020eb8c6fdbfb2e8bb9781a8000000010100000000070000089a94d689c9b7cabfe6fa00000003000000000000050101a8bcd19fc1d0afa8d1cd00000300000000000001000547d1c5c2e5d1f68afdac00010000000001000302010111e7a4d4fef7bcb88fe601000001000000010002020255ebf7f2e9f3bdd0870b,
  0x7000101006cee90e897dea9ab85d800000000000000070100000101fcbadbe69efee0c687d20000000000000400010400002087d783f1e7eceba2fe00000000000100010700000001a1aafaedb1a2faa4899100000000000102010202010007a9aec7cdd09190e4f9d10000000001000201020102000186fdc3b2cea5ced2ffbc0000000002000100000600006fb4b9fbdca6fee796a200000001000000000701000051c7accea5aba592f2c00000010000000201010201010cb2afc890fbf4da8b900001000000000101000600000190d1f1efbcfefc95ac01000000000200000102010205ffa4dc8896aff6cf0b,
  0x70100010001cfd48df391ad91a09ce800000000000000080000000144b3c5b984fed69291e700000000000005000102000132e2c2e9e2c4808de3ac000000000001010007000000028d90b393a28dcbe1dbb400000000000104000002020001d19ca9c3a6e484f6acfc0000000000030001000500001292e0ce9efce58da7f00000000002010000000600006fbae9a9dd80808080800000000200000001000600001acfc58bf0808080808000000100000101000006000008bcfeb880808080808000010000000100010006000067d28080808080808001000000010000000007000004c0808080808080800b,
  0x8000100001ea2b7fd9791f7c3d583fc00000000000004010202000016bfd9ddd08c838ba88fc00000000000000600000102000cb4eebbecbbecc8f685a000000000000400000103010005cbb6add8f98abefeb3f40000000000050000000102010adfda98d1a0fe8e9ffed100000000010100000700000019cea28498eeeaeca8ee9b0000000003000000010500000488ee89d3f1c0d481abf700000001000003000202010009f78499c68591abc6da800000020000000001000600006ef3de9684b59ef2ae80000100000100010000060000179a97d299abea8dd880010000010000000001060000018d9ed4e9e0b6e890800b,
  0x107000100001fcccfbcbbe492f7d28300000000000006000101000106c1dafda5ec93bcaad200000000000201000600000009a0b5f9b6f8fbbaa1bb0000000000020200040001001faee199ebf2ffad97c900000000010004000004000009bda7b685e2eface7810000000002010001020201000e99c081b0b98598d7940000000101020001000200025f92c1ad89f6a1ead700000003000000000005010002c7dee4e3d3fbba91a300000101000100000006000001f6b4a18c84cfa9a0800001000100000100000600001af9dbcfa8c0d6c1c001000000000200000006000001abc0dea7a4d5e0db0b,
  0x70000010001078cddafcb9aa4bed9d8a40000000000010105020000001ff4bb93fbd5ea90f1b39a0000000000020203000101001eac9694f8acf5e39397eb0000000001010201020200003782d787c3a785ec81d783000000000201010102000200058885b1a383b480a2daf70000000100010100060000000a90a792a2cda1f392c3d600000002000001030001020005a597c9cd8b91dfb1e9c1000001000100000007000000048fa4b7d09c87ce87d78c00030000000000000001050003d7efb4b0c6cce98a9b00030000010000000000000511a5a7fff9a6fdff80a30300000000000000000102030191d6d59dd68b80b28f0b,
  0x7000001010030f792e8f7c9a4d0909a8800000000000100080000000033c78ddfe4d99bf6dff2fe00000000000301000500000006f4a2f79fa4ccdeefdec800000000000600000000020102c89cc3ab94c8d5a087a90000000001020101020200004f98e6abe9e4ccf08df4d400000000020100000600000014ecb3a0ad8cfb80e2ecd600000002000102000200000203dfeef7e5e9b09fb1dab600000003000000010201020007b984e2e0b091c1818ddc00000101000000000700000007e8e6c0c1cac588b5b4800001000000010001060000007cd8a7f7b193f7e8b8800100000000010000070000000787eeb688f1d6dbb0800b,
  0x7010000010016cc94d892e29ed685e18d00000000000400010400000018e5bed5c4f5cdf883a9df00000000000600000100010103d6e7c98bd1e293d79fb000000000020002020201000024cfbecf93feee8de2dbe200000001000100060001000014d3ada097a5e188fae8eb00000001010101010202000006b7fab79ea1e5f785979500000100000000070100000013fff1ffeaeeb0c893e600000100000301000004000005c6eeb7eed2b1b4cd89cc0001000000000007000100004ff291bfb4c3f2caced90001020001000000000005001aadc093effc8db5b1a702000000010100000000050003a38c978a80808080800b,
  0x8000000010008bbaf87e4b7e8caf1d89400000000000401000400000044f3e5c2ccd49fe8988100000000000402000102000009abe5ddd19acecd8b83f000000000000500010200010003dbbb8697aa8af2c797ec00000000000600000101000101c8bc98c0958db7a6a08000000000020101020201000016e5cc89ddf381b1d190a00000000100000107000000000aedd2f9a0e7978fc5dce000000002000002000500000002d0b2c2b2fefeee97cdb800000200000001000600000001f0e3f682b5c39ed39d8f00010000000000070100000044dac092a9a8909d90ac01000100000000000700000004b594fce1e0a2dfe1fa0b,
  0x10700000100000285a6f0a9b4a1f9e2bcd300000000000500020101000038c1d8b4d8c1e5c993a500000000000700000000010114a0efdd9fa08080808000000000020201000400000002bfcfa2dcfe80caec95d6000000000202010200020000018af4eceeb4f4abc4c1f0000000010100000700000000018781e8f89fe9e0e190f40000000200010200030100003b84abfab9fbbac099c60000000200020102000002004bb5e990f0f68080808000000100000100070000000067b1a4f2a5dc80cf87c00001000000000107000000000ff0a0d1c6dabcb883b8010000000002010201020000018deeaaa1e8e7c5c9b10b,
  0x108000000000002a7d19db2c4e4cff0db9f00000000000700000100010038ed80affa98edd4e6fa000000000007000100000001108a91eca2fcc7faedd000000000020201030100000005b9eff2a5cac296aeccfa0000000102020002000200004dcc91909ab687a390f400000001020200020100010060d4b3d4f5c1bef7d6a600000002000102020200000001e29581ffa3e1affae0c70000000202010000020200007094c381c68ebcf4fbec00000200000201010102000064b7b2e2c1d1dda7e0800001010000020100020200002af3b9d9f6ecc8f7808001000101000000000600000003b1a4e9f2c5cd8e80800b,
  0x501030000000003c6d2bf92be8796e7fbd60000000000070001000001000496e4a8d6b6d98d80808000000000000701000000000135e4f9f8ad8ed48080800000000001000800000000000dc9c389eba3e2bbd19ee700000000030100050000000005dce0bbd4ee86e8e7b9b60000000102020001030000000fd2fee8b1c493b5d5de8e00000002010200020002000006a5b0fd82eeb1e384d0db00000102000001020300000001a9d28ab595d483b894de000002000002010200020000039382f7c0b786aaabafa500010100000000070000000001d7a5b7d1d0e0b9f3d4f802000000000001020400000008ec95b5cbdae4ebc9ef0b,
  0x70001010000006bdeabdfb7a8d6bbf6f20000000000070100000100000fddb1e2ebd7e7b98de08000000000040001040000000009f6e4e0e2c2e8d3dcd399000000000601000000000101268ef4b9e2f9829180800000000202000102020000001490bf80e9eba5ba99ed9c00000100000008000000000009bffe9cbbf9888ce4bb8400000200000201020200000001c8ddbbdbcda7baaa95fd0001000002010102020000000180cbccfb87d9b0abe9ae00010002020100000000030053c8a8d7d3e283d3f3a000010100000100060000000063f486fbea87829fb39a0101010101000000000004001ec2d98bc1e8cdad99c80b,
  0x800000001000001b4a6a4f6c5aff7b4bda000000000020204010000000001cfa9a9b5c4b0fa96cccf0000000006000001000200000d86a8f4f1c9bacdfc8b0000000006000100000101003481aa8d8bcb898597fc000000000700000000000101058b8eeccafc8cf299cc00000002000104020000000001e8fbcce5c3eefafd99c100000002020100020200000001f3eeb4c4aaf19be4e4f000000100020102020100000002aed4c8d5cdbe8781d4e200000202000100000202000010b9eec8eb9ef6cafdcf000200000000040102000000229ef1c99de5baf0908001000000000007010000000006ad93b4a5e9c0adc0800b,
  0x800010000000044ff83ccb99bab98c79c870000000006000001020000001ca4ba8ea79dbff4fde1910000000006000002000100002fd3a192c2b0e4efd6eaa00000000007000000010000015acc91d7aaadc38493ce0000000400010002020000002bc093f58fea8cdfc29dac0000010100000700000000004cb9b4e3f5fec48ec2cffc0000020101000102020000000291ed83a0bbabaef0a5e400010002010001020200000004e6b59a8d82b190ae8ab800010200000000060000000005eaa6eecdee9c9db7f19000020100010100020000020004a7a3ddfdd0dbe9cd829c0101000001000006000000000293bba6e4bcaff48080800b,
  0x801000000000001f0cfe4c2ea82e4eb92a000000000040201020000000001b4e9b6a19b95b5a28dc000000000060001000200000019c7f5f1f4abbcc0f4fb0000000204000100000200004d9e8da2e1fae19ab48000000004000003000200000011c2de9a83b8dcecd0e50000000600000000010002000db48a848d91f6e598800000000600000100000000020187b3c18be5e08cb0800000010002000600000000004df9cb9eabf4a69fbddc00000102010002020100000002d2b4e5c3b3af9ee58a9c0001000102000202010000005ff8f0c385e8bbefe6a40100000001000700000000000a86ab93d5edecfce4c20b,
  0x7000100000100000dc3cfaa87e9ebccacd2a00000000100080000000000001ededead80f8f3f2db8fea00000002020202010000000001a4d2c69ce4dd8bcad2b88b00000300020001010200000027fba9e1c8ffb89789aa9b00000300020001020001000009d8e2ddadcaee8efae6e000000300020200000100000121e0abd8cbe0d1afc6bd00010200020100000201000001b093dc91f6c6e68688c0000200000001060000000000029abd83d096b8ccb8ffa70002000002010102010000000d94ca93b7f49db9d7c88d00020200000102000000020001f1e1d9d9e984c6ecb4ac01010000000007000000000004e8f4e1f4e6a0808080800b,
  0x1040202000000000025a0a080c997d2eaace79e00000002050000010100000011afa8d8b5e2fce0bea09200000006000100000002000002efef848fd7af8ed1c7d100000007000000000001000108ad9da6ecea83bc8cac00000202000102020000000022b88ecdfec5c0e581a3b700000202010101000200000005abc7e3ff94e8b08bdaae0001000000080000000000000fa18af8db909dcff6a4a4000200020001020002000000019bde82db89e9c0c79ef900020102000101000000020040ff8fd9fdc8c6d9e9b400020200000102000002000057d4f6eac1e4ed8a95c101010000010006000000000002fba2a7b7d4f3ade7c0800b,
  0x701000100000000198bf6ea9b9dd3c28df08c00000004010004000000000016d8aefaf79dcbb1c4f2ec00000006010000000002000002a5fd9ab5f8e9e08080800000000700000000000101005c9d9ef0a5f48080808000000007000000000100000105d7cca0faa08080808000000101000700000000000013ed97b8c4bcc386e1b3da0000030001020200010000000a879ed395ecf2b7bfa0b40000030100010202000000000a9dcc8097a9ee9f94ebee0002000201000102010000000bf3f695eeb4ccace49c8c0100000000080000000000000287faf887af99b3979d87030000010001000004000000309f888beff6ccf790f00b,
  0x2040201000000000001f0e2d7edc7c9c1cec7a4ad00000202010102010000000001aaef8ea4abffbcae9ae8b00001010000070000000000002ce2ec85cfaae79bd981a300010202000100020100000029c2ddf6fae7b388cea788000201000200020200000000119780b3acc8aae7e5c1e000020101010101000200000002d8efa6ef82d18588c3cb00020201000101000002000008bfddbdb0faa0df8af6fd01010002010101000200000013e599cfa8fe808ab9cdeb010203000000000000000300638eb3b7c1aa8d97f88002000200010100000201000001d3889f899fd9aec28e8603010200000000000000000305ceba9dece7beaeb0800b,
  0x8010000000000000fc9f18a82f1c7c0bf83ba00000006000101000100000011c887fba9f4db8db9aec000000201020202000000000034cfaf86ddfbd4c58accb30000020202010002000000000c888e9fedd2b78df1c9f60001000200060000000000000887d98ca2faa7d1e9afcd00020001040000000200000015ccda9094bba4c68fec00020002010101020000000011f7a69b8edf9deeb0859a01000001060000000000010036b3a2d5e684a7fcc6ca01000100000700000000000002dd89b696c5d29882b7ae02000001040000000002000001e3f2bae0c098fdf8bcb60401000100000000000000037df6a6fba3aeb29ea70b,
  0x1080000000000000043f78afcb7bc8ffcb4e09300000007000001000100000024d1eab6f5edf99f98d6ca00000202010301000000000001b3edd89e85cec2fdcab0e600010201020002010000000019ef8789c49b8788889ef800020001020202000000000068ecdbbcd896e9f8f3e70002010101020002000000003988bdc0d1d6b7bbfbf0c400020102010002000001000006fd9db7fbd0dfc5c4808000020201010002000000010061d99c8fc2eab9cdb8800005000000000100030000004687b0d6e8f480f7e39200050001000100000000000202b6edaaf79abbb7a4f80201000001000500000000000ec08080808080808080800b,
  0x7000001010000000002b8d0b2ab83bef8a6eae9aa00000302010200000100000058b7c4c1cb8980b590feea00000400010202000000000002b79696b1cfd5fd8dafdab500010000070100000000000002b18bf58ad2ade6ddf898da00020200010200020000000018d7e788daeefeb4f0bdab0003000000050100000000002dcfb7d2a6a5c2d0899bec00050000000100000300000002b7d49dd1e481def294b200060000000000000002010001dfdcd6d9e9df88dd90800006000000000000010100010ad1df9fa6eec092e08001010001000600000000000051def7f6dbdddaf5fdfbf605000000000000010003000004b093a48f8de586f0f8800b,
  0x7000101000000000009eeefb3a996d490cbf0b800000500020000020000000002a3d783b2f8f1e7f2f5d000000600010000010001000022b1f4d3d088f9e5beb000010201020201000000000016c8d98bc789a691fe85a0000102020102000100000000069aafa2e8b0d497a2d2f800010202020100000100000002d59bd9d58884bcf2df9800060000000000000102000007e8f7aa97fbc38da0e800060000000000010001010005a7b6808080808080800006000000000100000100011dc08080808080808001000000080000000000000005b4f5b1a8f6e1a1e687a90200020100000301000000002c94def2fbbf9f9283b80b,
  0x40200010200000000003683f7aff6adf2c19bd08000000501000200000100000002c2abc7d1eb90c3a9b4f6000006010000000100010000019c81cf9b8aa6f1e6c0e00000070000000001000001000fd0d4bcde96d0e89500010005000300000000000028acabcafd87a9de92e48600010100070000000000000016aad4d9e7afcd868da8ca0002010201020001000000001cbbcee3b0d9d5f2c68d8100020202010000010100000005c0a9b59ea790b5f9928a01000001070000000000000019efb3c2eecab0e3a4b7f601050000010000000000000225ddb2b4b3ba80bdb505010000000000000000030004d9daeca8f78fdf82910b,
  0x800010000000000000eadd7e58792eec0c0f6c400000600000200010000000004f5dd9085a5f5cebddaae00000700000000010100000001c7c2c1fbf382b18fa6b80000070000000100000100001bc6dfd4e295d4e6d7cc00000700000100000000010002a49bd6b18c84bbdad20001020006000000000000000e918af08ea7f6be8b94dc0002020102000200000000000ac1e8f2c184d2c8eda8ec01020100000500000000000006d9ddb787d1eff4c9eae401020201000001020000000042fcefcde3d2cad08add0102020200000100000000010b80daedf3a987f3a502000201000202000000000001eaacabb7bba1bce0e3cd0b,
  0x8010000000000000008e3c49dcb96d2fec5fdc80000060001000200000000000acef3d2e0dfa8c2db879a00000700000001000100000001a2899dd1dcebdfe4808000000700000100000001000002a79aaeeec6b3aca79a00000700010000000000010001d78bf4d3c2fbc0808000020102020200000000000018f894f0d2daf9b3c084ee01000202020200000000000003fa8db5afc9fcadb1ffc501010001060000000000000004cadd829cc5d4b9c38eb40201030000000003000000000291fda8faf5a9faa6808002020002010100000000000107db87cfee8a80808002020101000002000001000012ffeef88feacf83d8e60b,
  0x1080000000000000000168596de86b3a893dc94d50000060001020000000000000acca687c1e7b3c19fcfc800000700000100010000000006f1adf9f2b798e3a898800000070001000000010000000ae5f5d48ead9093bfc600000701000000000001000012d190fdc5c6bafb908000030101020200000000000017f99abde6c3e39eb7bdb80003020101000200000000000dc49ae799c291d6f0fa8001000601000000000000000105c092a584cecbc0800200010006000000000000000db0fb93a1d795f9c6f9eb03000300000200000000010001a9f397a989c9fea08005000100000000000300000030dc8a8cd3e9d4d6bdbe0b,
  0x501030000000000000057f9d6f0d88ecdb7b68d00000700000101000000000079e4dddaf4eaceedb0ea0000070001000001000000002deba7f3a1fafcdee2e000000701000000000100000007df8ce5d0fdb5f7e5b80003010202000100000000004495b4979d82cdcfc9d600040001020200000000000001cde3ebdda1a8d7d7abb701000007010000000000000001bce5e98cb3e9b38aab810100070000000000000000011dd2dac9b0c1d6ff0300000005010000000000001cbdd186a7e1c9e5fdc604020001000000000000020003e2d1ebbf8bc6eed105000100000100000002000037e78883d8f7e5cbe20b,
  0x700010100000000000005d3f4b3eea9df9197aba10001070000000000010000000e92beb0a4c8fcb1c8c000040001040000000000000002c9afbae3a2acaeeb89d400050001000300000000000001b1ffe5bf8ea8d69daae600060000000102000000000001a9bcfeff9eaf8da4ae800006000001000101000000005dbcfaebd0a583f9d48000060001000100000001000001b6d1c2d0858ee5c7f00006010000010000000001000b86faa1e887a5e7dc00070000000100000000000126f6e7c1e5a0b6e101000107000000000000000005d3a986ba98e5d697dbfa02010100050000000000000001f7c4d5bf958af1f492830b,
  0x80001000000000000000acbd4d8f5bbb8fa82edf2000401020200000000000000048992ac9cccaac1e9f4a500060001000101000000000003acd7e7bacfaa81ade18a00060100000100010000000043e687cc8bd6a3c7c29401040001020100000000000009c18cd8ccec8dc3e39ce20106000000010000000100006ba8a69be288c0808002000106000000000000000008f899b1cba59cad93d7f702030201000000000000010005b7c18ffebe8080800501000002000000000000011080f4b7f880808006000000000001020000000005ac8dffe0b1c0c89ef606000000010000000200000004fbebc8eaf585c880800b,
  0x80100000000000000000493978be9b0cb9bb39fc400050100030000000000000004a5fb9bdec2fab9a781c2000601000001010000000000019ab885fab3e99c808080000700000100000001000000038e9da8fadbc8f580800007000100000000000100001fc3b1d29fe496888000070100000000000000010001bfd7949d83e695c002010006000000000000000003f9ef81a7ead6db9ae4eb0201020202000000000000000197abe58eb8eec5cafddd02020201000200000000000001f7f4f5acf4efd28080800401020000000002000000000d8cdeb7e6b4cea1b8d20601000000000001000000010491dea0d09d8edc0b,
  0x1080000000000000000000d9788dad1d49a92e3f6870006000102000000000000000d9599a0d89be6cbe0b18000070000010001000000000001e98b9192e8aff7a7c68c00070001000000010000000022c28cccb2baed9ff1800300010500000000000000000bf4b6a4bcfdeab7e492a004010000040000000000000043c5abcc87dbb0e5e7fd04010300000000000000010001a7fc8596e5f0a4b804020000000300000000000002f6e2a0d4b7dbf3dfa4800402000200000000000100001fd382b1cbb79485b006010000000000000200000001e4fea7eea9a5d4e39007000000000001000000000103959b87d5ae9ff40b,
  0x50103000000000000000009ebfcb7e38ec8b1a9bce80007010000000001000000000f85a7c1c6aa8080808001000800000000000000000007f9e5dce0d9fea7daedd30107000000000000000100000bf6a7de808080808002040000030000000000000005bbb6f1b5eb8184e8808003010005000000000000000002c285a08aefdeb5f2c8a805010000000300000000000001bcf281b3d49c8580808005010001000002000000000036cfa3bd9cfda880808005010001010000000100000001b9c99aaef0808080800601000000010000000001003aeca0808080808007000000000100000000000101848080808080800b,
  0x70001010000000000000007bbb882d88ac7fcaff1e000070100000100000000000002f7aaaacfd6b885bbc4c00102060000000000000000000af5de8db98094e8c0d5c901070000000000010000000007a4b4deb1f8b5bede8004000104000000000000000007e6b78ce0b5a793849d8605000100030000000000000001e0facea8ba93c6aadec0050102000000000000010000049bceec928ddbf48005020100000000000000010011e3a397e4df98800600010000000200000000001efae091949fe3aacfc00601000000010000010000004ce4dc8d92f9eeca800700000100000000000000012288dee8bab0800b,
  0x70002000000000000000002a3fdebb1c8a3ade2818d00070100010000000000000002f9e8d0abb9b8c59fe9db0107000000000100000000000ff6978bf5d599f293800300050100000000000000000589eaf1c89fccfca695a304020200000000010000000001dc88efd1e7b29affc005000003010000000000000077f7f2a4ada3afc3faa506000001000200000000000034d5d69dca8ffd83b58006000101000000000100000010d185bb82cdbc8b900601000100000000000100006ba3bfffd1a6a0a8070000010000000000000100039f91db89f3959c07000100000000000000000105da9cb9afb9e60b,
  0x601020697f6c7be9894e5ac87fdf10000000000000000000400010405858891ecb1baf694819cc300000000000000000100010700069ab9f0a6f9d1c9b3e2f7b60000000000000001000001060128bbd79186f18fa8f9a1c40000000000000002000001010542dec39c9adbd88bbbf086000000000000010000000007011be2c5ddd8f393c8ecfed80000000000010000000001040303a0f6a3d0a692bbae8ad00000000001000000000001030423d49ca7daebd7cd9a96000000010000000000010001060295cbc3c4ecf9c090c8000001000000000000010000070bb2d4e9f39cfca6b40001000000000000000001000724a5b1c68eb8a0a80100000000000000000000010734fcd1a781e1ea0c,
  0x8010047e7d3ffacf69c8a9999dcd3000000000000000000050100033ec7faf0bbb0f799abe48b880000000000000000020100060051b1befcb39aab8edbd6a9c40000000000000003000000020410d49e82edfcebb98bb5c1a20000000000000100000101060001f8d0d3ae9687b1a5cabdc40000000000000200010000010504bcffb69cb0e1fba2dbc7960000000000010000000100070001dfa8abf7dfedf4c191da90000000000200000000000001060d84dda592c2baf7bfaebf0000000100000001000100000602958d92e9f4ebf7db81a8000001000000000000000007010fc3eab4ad9db38292e40001000000000100000000000743c2b391c2ccb4c088010000000000000100000000070186c5be85ebedcc820c,
  0x10800002fb5e780f3a2f6f0b19cdfa00000000000000000000600010226a4ceaa8383fff8ecacd5fc000000000000000003000105001d9eebc2d1e1cab0b7969eae000000000000000004000101030e99c1d3e997fac9e49f96d20000000000000002000100060017c7a9a5e98ae1e0d38fd9fb00000000000003000000000105048cca92ce8ba2fedb86a2b800000000000100010000000700029ffca6e6f68e9bf7928fba00000000020000000001000006139b8aa8b1f396ebd9c2a50000000100000000000100070003d2d296d7e2dc9cdfcdf8000001000000000000000107001df1b59d9accfa89c9cc000100000000000001010001050194bdf9a4feb4cbd7980100000000010000000000000702d28fbb839acad8f60c,
  0x701000155a9abdec3b1cec7e3e3aab8000000000000000004010004004c9bb9f78bf6d3ba8b86f1f3000000000000000101000700005fb180aa968a86bcfbdeff880000000000000003000100050005adc2e5e78abcf3aab1d4e80000000000000004000100000412c8dfca999cbdb0eff5c7ab000000000000020001000105001dadf9f796ddfbe6dcd4e0a80000000000020000000100060006e7cbe9a6cf82a0b786c4b0000000000200000000010004020193b3b4d0f190b0e3d4efaa0000000100000001000100060023ba85d0ee99d8c492b3f00000010000000000010100060002f0b0f994d8c2fc98fe980001000000000001000000070011dbc1eb8ed69beab8840101000000000000000000000734a7d38cb487c9caac0c,
  0x10700000101f1eeeafedfdd99dddb94dc90000000000000000005000103007ac8d2fff39a97d3aa8ef3a40000000000000002020100040001c2b5cbd780fc83f9bdb7e1850000000000000002020102000206fcf7a199ffe5acc3cac3cb0000000000000101000007000001dad39581b8abb19badf8b280000000000001000001000700001696e4f6d3d3acd5a28d92ea000000000003000001000000050bb6a2d9c3c1c5c5849898b2000000000100000000010700000ad09ef1b0d5eec397b7ecc0000000020000000100000100055b84c7e582a69fc3ccf9a000000200000000010000000006089d89acece78ed0fe87c00001000000000000000007000173abe4b1bedfc4ba8e800100000100000000010000000602f2c9ec959eb4ffb3c00c,
  0x7000001012ab6e7f78fd6d0bf89c9c4a9000000000000000102040200000199e4b4be8ddeddced0f797f4000000000000010201010202000198a0f0a9d9eef89284a48cbe0000000000000200010301020001fcd280ddb4a7c6f59cfaeb0000000000000200010302000112d081abb29bbab2edbab7f200000000000200000004010101199dabf392acdc93f4b8f5970000000001000000010500020002efae96cdefb0e8fbfcc6c0000000000101000000000700000ba6a3cdab90b2b2d797b1c20000000100000100000007000002a7f2d9b2f1b0e2eca1bfd80000010000000200000101020220cb81b5dcecf3f0b0b49c00020000000000000001000402018b98e5c1c6d3d9e2d7bc0200000000000000000100020404a183d2ceb9b0c2abff0c,
  0x7000101001f85d886e8c7d3eab9a9eb880000000000000004000104000016dfccbc87adb7d4cd8896bd000000000000000600000001024e8895cf84afedd0a186fb00000000000002000401000002028bf186bfdfafb2dfffa1da000000000000020200010202001af0d7c3bafaeac6d28fe1e8000000000001000000080000001899b88ca7e8f4cdcebcd6f000000000010002000101020002068bb1d2f1f59a8289c89a820000000100000000000700010051a0ab92a888959d9bcdfd0000000100000002000006000038f78fb8df8187f8dfdda50000030000000000000000010505ced4b1bea487ccd3caf400010001000000000002020102019de8c2bdb79c8edbe6b80100000100000000000201020205a5dcc6bf9c9deea6be0c,
  0x8010000000d9ef3acafa284bbea8eebcf000000000000000600000201000bd7a4bdcbb2d2b7cf94e5a90000000000000201020202000009c797919b9ecce9cf9f8fa300000000000102010002020100109cebb6e2aaefc4959a9e8b0000000000020002020100000202c8c7f0acf3ced191e5e8cd0000000000030000000204000066e1d1ecdfbaa7c8a2a3f9000000000100000105000002006fa6a0fac2efd5e687b6ea0000000001000100000700000006a0aae89a91acdfe0dfffd40000000100000001000700000001c2a1a0939adbb1e5b2d6e8000001000000000001070000001bf8c18f84dc86a4c0a3a40001000000000100020202000102b7e39fb885bcd29fb6c8010000000000000000070100000cbabbece19ef5a18e820c,
  0x108000000000d8092e49cb1cde58ddae1830000000000000006000102000028bae08cf2c0d09cb79b840000000000000007000001000103d8cae79ddea5caa9dffce200000000000005000001010200079d8b958ab1fae5e88dfcf8000000000001010201020200001ad8e8d7ebe19da6b0cb83a500000000010001010006000000059edbd3cda59eb79e8ed4830000000001010002010200020003e9eee4c6afd6f78fd6a8eb0000000002000100010202010020f1909bf3bee6f08ff0b60000000100000002000600000002a6dad5eed3f9b1b98888a8000001000100000200010202002e89bebaf8f7b2babfe8e40001000000000001000700000004aee4fcf384f5eef6bd880100000000000102000102020018a290ebe0e8a381ebc20c,
  0x80000000100319bf1a2e9e8dcbec084ede70000000000000600000002010002e6e793c1bff2dbaaae9e83000000000001020004020000006ad0b98e98a7d0bbf5c0f5b80000000000020201000202000025d1ed96cbd292d0f795f3b40000000002000001040002000004a99fb0939696bebaf4c590000000000200010101020200001ebbb587fdb9d3fbdb95cfee000000020000000005000101003ae7ea9bafd68f93e2e1fa0000000200000001020202000001efe984efe3e49b91b088ee000000020000010200010200010790afe7c0a2a7ce9799c4c00000010000000101040002000003bcd1d18abfd794c5c4d1c80001000000000100050002000031bca8d0db92c787f4c490030000000000000000000201036bd1e3d3d9b5a986b1ac0c,
  0x7000000000101079d85bcd9f9beddb8e981c0000000000001000700000001002dbcd7c4abe4e0cbb39ff8f600000000000102000600000000408ea4acb7f992dcc9bacbf6000000000002020100040000003d83e1cab0e795dedbf3b9ab000000000100020201030000002f87928cf486b89cc0ddc990000000000101010202000200005494f7be89bb83a3c2988db0000000010000020201020100002582d8ef9385c389f7a986f20000000100010201020000020001c7d1e2ecd4eaee99a5a78e00000100000000010700000000068dd48dc696cae6ac89edd200000200000002010000020200639ab084a29a84fac9ded70001000000000201020102000075f0fa83dec685a2a096800100000000000000070100000006bfe9ec97e0df929199c00c,
  0x70001000001000599f79facb4b79dc6a8add800000000000100080000000000068edcebfcf1e0efdaf5ccde000000000002020202010000001bd1a7bcc6dd8fd6b1ceee84000000000201000202020000000adcc4d7c5c0c988a9fda9cd0000000002010200020002000008ce99cea1dab6a4bad4e2db000000020000000501000000014db2e0b38ac1c4d491a5c00000000200000201010201000005ddb8b8b983b39683d7818c0000000201000101020000020006b9d6beeaceeab0e38cec0000020000000101020201000001c4f9c5b7ac80acadb5f0c40001000001000000070000000014b5bee695a19392d18ba00001000200000100020001020022e1d8a3e7b6d99dfaa4f00200000000010101000101000201e2e0d3d2a0c681f4b7920c,
  0x70100000100001d99b0e7b2f6f082bda088f7000000000003020004000000003ba7ecdbdce5c5baf291f1a00000000000040200000300000012d69efeade39be7c8c5f8ce000000000201020002020000005ad3affde996e89da995ddd20000000002020101010002000005acdad3fcf9df94cf9ece97000000000202020001000101001580baa0ba85d4de9ca3c9ec000000010000000800000000004dc7f3ec8deae58db2efa3bf0000000200020001020002000002acc8b697a5f4d3ccb7baaf00000002010200010000020001028de1a384fa84e6cff383a30000010000020200020101000015dbbc9fa0acf3d3d2d68bf60001000000020200010201000003a3da948d95c9a3dab1d7cc010000030000000000000500001d8687c4f1e1e8cf8ed2f30c,
  0x801000000000013d2cf8dfdaebdaaf7e9f1880000000000060001000200000001e2ffeca7a9e18de898859800000000000700000001000100049cadbefacaacf0f2a7e0a0000000000007000001000000012edda5b8f1f3b0b3dfcec8000000000202010103000000002deba5acdc8bbc8d8fbe94f5000000000202020100020000000dc0fdacad8ffde1c6f69ee90000000200020101010200000011f8e7a4dce38fcaffc5ea91000000020002020100000200000adb95bcadccb59b8482c0db000001000100000700000000000fd694d6dd9ba9d4d5c18efc000002000002010100020100003dd0b0bae68cbba7aff9ca0001000000010007000000000002f58ba28aa3be9dd8d3d2a0010000010002010100010200001dfaf2a09f958c8ab5a1c80c,
  0x600010200000000079bfd9fefd4ec858ad7fbbd000000000203010200000100000aeab2f89ddbfecffdc1dd8e0000000002040001000200000006ffeede90e199bbc2bbff930000000100030202000100000011fefc9f83cbbfe3aff4abe4000000010200020202000000001fe9d6d4ccebfeb2fab0f6a40000010000000700000100000007f6d8c28082b08bc1f0998e0000010001010202020000000007ce8ef5dc84cdfed4d0aaf60001000000000700000001000056c5aaedf2dd8d82d2f8a60001000001000106000000000029a1b7b4e1dbf0d2fde2ba000200000101010200000002007bdcb4dce4f6d383feab940100000000030202000000000114e78fabdce0b6ceac8cd20200000200000100000101020005e9a3c6e3ebb3dcc9afd00c,
  0x80000000100000007f5eeb6809096f8ee9e85ba000000000600000100020000006bfcead6cfc9efb597f5d40000000007000000000001010035f6ecb596e5d4d6d9aadc0000000007000000000100000103ddded2c0d69cbae5a3d7000000010100070000000000000991e0e68894f684a8bd9dfb000000020201000202000000000af4f68a8becffadebffe4ef0000000202010102000001000001b8fefaa08383ddc193ada60000010002010202010000000008a5898994fbc1f2b2d6bbbd000002000201000200020000005ce8d6cadaf1939cdfefd60001010001000006000000000002bcfda1a1f6bcc0a2bd8dae000201000100010002010100000e9de49cccd1b180a7d5a70100000104000000000003000022d4dcbac7bac4fb9ff8c70c,
  0x80001000000000002c299a3c28cb2fbe8c1f184fe000000000600000200010000007e9de887f5d0fab199d1bae20000000007000000000101000045babbac97ba9d83d1dba3bc0000000007000001000000000152d5f3e9fec498d98ee2c80000000202010200020000000002bccba19fb1ffc4ac8084e2f80000000301000104000000000001d98dfdbaf48392badcf4a6eb0000010100000700000000000055a5f1c7d694ffb19abbb9ed000001020201000001020000003790c5b0fd83bad6ad8cd2ed0000020001010202010000000001daebcabacee6a8c1faf882db000100000100070000000000000188b5dbb7b291b5afc2debaa0020000000201020000000002000583e3e2c9d9abc5e1c4dc900200000200000101000201000002acc1fbffa0c8bcf5f78ad40c,
  0x7000001010000000004f793f9cbea84f283c38ab60000000007000100000100000006d0e3aa8bf9c3f2d2edbbf40000000007010000000001000001a8b9c2ebc3d1e7a5db85b20000000301000500000000000001f8a695e0a0ebeaf3b1ccc500000004000102020000000000109dfee2ca80eec6e299ecb9000001000007010000000000000281f2e3ec91f7c98b90d4900000020002010202000000000008c9bcfbf798a48ebab4c1d0000002010102010002000000000898abb0b79295a3bacdc68c0000020102010200000000010014a1b4fcd2a084f3f1c3e400000201020201000000000001018efc98cc8ad0ad8efab10001000000060200000000000009ee9394d5e78f88cdb3db8401000000000700000100000000019efef8b7baf0e487e286a10c,
  0x104020200000000000014e69dbfd2c0fe8dffec98d3000000020401010001000000001c86f394fe9db493b1e58e820000000205000100000100000006ce9b8bea8cca95c6b094950000020200010202000000000026848de588c292a9d4d2aba3000100000008000000000000000ed0c6af9ba988eca9d2e0f10002000003010002010000000027efb5ed8fedddcea4c8b10002000100000600000000000054ba9a99e384afcca0cd890002000103000002000001000001d49ba9cddeb2a9e780e18e0002020001000100020100000002b5dfde8cb89991e7cbd3970005000100000000000000030007efb5819a91bfd5cfd0d40100010100020202000000000003b4a0bcc6c396e6e0e6d2da0105000000000000000000000333afe18290bfa291cbf50c,
  0x8010000000000000034a7f1d2c3d9f89198e7fdb30000000500020200000000000025d3e880ced4cdff95cecffc000000060002000000010000000f84a2ecf0d1a7d1f4cb9fd80000000700000100000001000002aceb90a6c2e5f6d0e4bb9c000000070001000000000001001cc0c882abaf989885caf80000020100060000000000000030a28ec3f3bbe888cafbc6a600000202020002010000000000018dd1af98f8b1e5b68c81b2b8000101000302020000000000001c98f59babd3d7d98f95ddd4000200020101010200000000001ce9beb8d8b4f294a9f3d8dc0002000202010000020000000020ba8b9e89d28ff9f4ab8be101000100000700000000000000188bd1a78af19485cfe6958c0501000000000000000000000334e8b3dbbc908ffcbcea0c,
  0x108000000000000000003cfb3f1c1ccd3e1dcc3f7e40000000700000100010000000006a680afc7f9c7f58f83a2e40000000701000000000001000027b998959da088efe2a2e00000020202010200000000000025d6c1bfaad3baacf9ad85ee000002020202000100000000000ddffde9c3d390fdbad788d60000020203010000010000000003e1819289f5e7de828edeec0002000100060000000000000005c89fab8ee9ff9ca4cda7cb0002000104000002000000000009f3bdb2c5c096b098bfa99500050001000000000003000000598fedfac19ea9d39ff5c00006000000000000000200010003b893d283e9ce8ad9c5c00006000000010000000000000208e5c0eaf1e8d2e2d5980101000001060000000000000007a39294d0e8b18680daf4b00c,
  0x40200010200000000000004d28c9cdfffdd809aeb8cff000005010002000001000000007bfef08f89958df8fbb5e2000100050003000000000000000184f2a084f2fcad98eccbff0001000600010001000000000003f3cb8eafdb9f98f3f181d00001000700000000000100000016bf8ff08a8489d58789880001010007000000000000000005aba8fd88fbd9f5d09a8aae000202010002020000000000000180a0f69eca95cbb7dcd0cb0100000700000000000001000002dbdec19e91b9adacc9b40201000000060000000000000001b4f39daaea8ffcb9bb8cc70201000201000200010000000001c1b3dda1f0d0c3b9f9e20202000201000000010000010019ba92fdc2db9fa3b9e8020201010100000001000000016da7d9e99588f9828a0c,
  0x800010000000000000028b6e3e491e6fda5a89ec5cd00000600000102000000000000049eb9848dc1ba98e6e0feb100000601000000020000000000099becfba0b1afc9ef85b5d30000070000000001010000000005becaacbdeecee5e7dae08a0000070000000100000100000072d0978ce5ca9fafda9eb8000007000001000000000100000ccfe683c1f9e0e484f58c0000070100000000000000000103a6a38eb5ee97e0aff60001020006000000000000000028df88bba6a7b5a59889adae000106000001000000000001006bec809e8480a2facad8000202010200020000000000001cf4b68fff87f78d99a5edab0102010000050000000000000018e4b8fd91f38dd2a1b3e79e0200020100020200000000000004b6849deb9db1bfa983969c0c,
  0x7000001010000000000000f80e98d94abe08de5cd80d30000070001000001000000000004c4d0bceab6bfe488a996a0000100080000000000000000001391b29c8ee3afeae4f8bc8a0001070000000000000001000001a99f9be3e2ede3efd8880003010005000000000000000002fca0fbe7a2b69eb7f0b7b9000401000103000000000000000bd584a6c6c79e91d8ddcbef000501000000030000000000006dade58ffbd896bcefd1a3000601000000000001010000000ed0fbcd83acb6af8fdfd00006010000000100000000010009a2b088c697d6d2b190000700000000010000000000011de3d2fd91a6c5d5a4020100000600000000000000000c8ee8a39b8acc9880ba9fa8050100000000000003000000001fc7aeb499c8abef81fb840c,
  0x106000002000000000000003b9780bee3c6b2d3fba0b6f50003020004000000000000000057b5c9c2c1daf9fcbfb9e7f70006000000010200000000000009d6fec2968cf995dfd7c3b00006000100000002000000000005c5b7e1cf87e18bc1d2dbb0000700000001000000000001000eb5d3adc1c399d0d7a401000107000000000000000000519f8cc38caac6b6f3fef5d00202020101000000000001000002abeca78af1dd9ad5e9d80301010000040000000000000005cdb4b2c7abf8a88cfddb9a0301020000000300000000000009bd9abc9fabacf8cfe1e3d00500010000010000020000000077fd98fdafb78180dfefba050001010000000000020000000eb6f0b79dfbc99edaebb8070000000000000000000001012ac9f99bfadfbbf28c0c,
  0x80100000000000000000066d8de8b94fad3ae8cdec4dd0006000002010000000000000060b7a9dba394fb8fc6e1dfa00006000101000100000000000001cfc8a9ada2fbb7c7abc1ac0006010001000001000000000004b2c6969cb48fef8fb89e98000700000100000001000000004b87c985febf82f593a9d8000701000000000000000100003ab0f3f1cee0dfcba1d0020100060000000000000000004d8fb692a2b48891cda0e0e40400000104000000000000000014db9e83a7d9efbb9afac09f0501000000000300000000000007bbc98dd1f1c7edf8acb0bc0600000100010000000000010002a287f2f1f6f8ccb3a00601000000000000000200000003c7e58d9d9680e3c2cc90070000000000000100000000010594c1f6a484a6e0a80c,
  0x108000000000000000000001daeac84ae85a9cb9293daa7000600010200000000000000000da09ac4e184a8bbb091aa8c0006000200010000000000000013ffc688d8a6c9a2f0e4ceec0007000100000001000000000059a9deaff392aecda0d7a0000701000000000001000000000ab6fdeac281fbf9998bcc01070000000000000000010000069b90fbabd8c7cdd4a80300010500000000000000000014cdf1d9bdffdbf1b6f09a94040100000400000000000000000a8cd8ef8fe1cafeb0f893fd040200010000020000000000000296bef0c482de8bfdbaf5a8060001000000010000010000006eebd4aaaedeaff19a90070000000000010000000001001b80faedb49ec899d00700000000010000000000000135e8cc82ab929eb40c,
  0x701000100000000000000000dd3e5ddbc8bcd87f1f3a0aa0106010000010000000000000073e9da84a8a6aaeadb9484010700000000010000000000003d8bffe7dd96f7ed89b0a8020106000000000000000000000de2ab9de9c1cfec9a9ad3850304010000000001000000000007959de7fdbaa8cfb297b0040100040000000000000000000ae9d1f391c6fbfef79e9bc3050200010000000001000000004eb9a4d7aea08dc3b9ca0502010000000000000100000004e2d9ae97bcbec0a4b8060000010002000000000000000185b6ad8ed4ccca848ede9607000001000000000000010000198987b5e3f2f7ee8c070001000000000000000001004febed80d2fbe0d80701000000000000000000000174c5b2efb78ab60c,
  0x5050101,
  0xa0005000500050c010007020a03,
  0xa000005020700010a050005000c03,
  0x505030103060502]

/-- The triples `(n, b, a)` of part 12. -/
def enumC12 : List (ℕ × ℕ × ℕ) := [(9, 81, 70), (9, 81, 71), (9, 90, 11), (9, 90, 13), (9, 90, 17), (9, 90, 19), (9, 90, 23), (9, 90, 29), (9, 90, 31), (9, 90, 37), (9, 90, 41), (9, 90, 43), (9, 90, 47), (9, 90, 49), (9, 90, 53), (9, 90, 59), (9, 90, 61), (9, 90, 67), (9, 90, 71), (9, 90, 73), (9, 90, 77), (9, 90, 79), (9, 99, 13), (9, 99, 14), (9, 99, 16), (9, 99, 17), (9, 99, 19), (9, 99, 20), (9, 99, 23), (9, 99, 25), (9, 99, 26), (9, 99, 28), (9, 99, 29), (9, 99, 31), (9, 99, 32), (9, 99, 34), (9, 99, 35), (9, 99, 37), (9, 99, 38), (9, 99, 40), (9, 99, 41), (9, 99, 43), (9, 99, 46), (9, 99, 47), (9, 99, 49), (9, 99, 50), (9, 99, 52), (9, 99, 53), (9, 99, 56), (9, 99, 58), (9, 99, 59), (9, 99, 61), (9, 99, 62), (9, 99, 64), (9, 99, 65), (9, 99, 67), (9, 99, 68), (9, 99, 70), (9, 99, 71), (9, 99, 73), (9, 99, 74), (9, 99, 76), (9, 99, 79), (9, 99, 80), (9, 99, 82), (9, 99, 83), (9, 99, 85), (9, 99, 86), (9, 108, 13), (9, 108, 17), (9, 108, 19), (9, 108, 23), (9, 108, 25), (9, 108, 29), (9, 108, 31), (9, 108, 35), (9, 108, 37), (9, 108, 41), (9, 108, 43), (9, 108, 47), (9, 108, 49), (9, 108, 53), (9, 108, 55), (9, 108, 59), (9, 108, 61), (9, 108, 65), (9, 108, 67), (9, 108, 71), (9, 108, 73), (9, 108, 77), (9, 108, 79), (9, 108, 83), (9, 108, 85), (9, 108, 89), (9, 108, 91), (9, 108, 95), (10, 2, 1), (10, 3, 1), (10, 3, 2), (10, 4, 1)]

theorem certs_ok12 : checkAll enumC12 certData12 = true := by decide +kernel

/-- Certificate data, part 13. -/
def certData13 : List ℕ := [
  0x50500030603010502,
  0x2080101,
  0x4060101,
  0x6040101,
  0x8020101,
  0x5051c000103064b010002070503,
  0x50500001c060301004b070200010503,
  0x5000535e8cb00000000010007024da1d3000000000103010505e5cd00000001000104040cbad8000001010000010701b198000100000001020609ec01000000000101071e07,
  0x10801000382ba96000000000601000302a28391000000030001060002d5e680000001000300060040ba8200000200020102035ae8ff00010000020106001ef880010100000000070101f08007,
  0x10801000001f3f5d5000000060100030053acfc000000070001000250808000000300010600000180badc00000401000104002fe8e3000101020103020001c7ab80010001010007000015ade007,
  0x108010000000288eabb00000601000300006fa0c4000007000100020063d5c0000203010300000115ade000030001060000006f9e84000401000104000073f2cd020001000700000050808007,
  0x502020001000001ae8600060201000000011e8000070001000200000ed9dd010008000100000023e69701030203010000005cb08901060100000002000286c0030001060000000004a3a207,
  0x2070001000000001bd7e0030600000100000016a2050005000000000013f6ec060200000200000001fed3060201000000010003a406030000000000010a07010000010100003b8807,
  0x50503b100000103060bbe0001000207018c01000001080504,
  0x7010227f3000201070014b9000401010410d6010100080012fe04,
  0x701020014b9000800010112fe020107000027f3040101040010d604,
  0x50500000003b106030100000bbe0702000100018c08010000010504,
  0x1080140fb9f8400000000000000040204499289eb00000000000003000106228ea0800000000000020000020609ec80800000000001000101000702bb8080000000010000010001071aa0800000010000000001010701b4800001000000000001000805d0010000000000000001080a09,
  0x108010029baa985af0000000000000601000324d3c28cea0000000000030001060024b7b3e29c000000000102000301030589aae4d6000000000200010007000ee38cddd50000000200000201000503a686c0800000010000020001030367ae80800001000000020001020407b18080010000000000010008001e808009,
  0x108010000000be0ccc598000000000601000300000fb08ebf000000000700010002000ef789bb94000000030001060000000c9bf1e1c90000000400020004000005b285c28d000001010103020200001dc281ad8f0000010203010001000201e5e6d2f10001000003010302000006a1c880800200000002010201000223d0808009,
  0x1080100000000448389fddf000000070000020100001abff8bda40000000800000001000101dc8080800000020301030000010013ab808080000003000106000000000595b183880000040100010400000005b8ad89d10000050100000103000016e982c0f4000101020103020000005c99dc8f80010001010007000000000ce790ace009,
  0x502010200000000000be0badabd0006000300010000000005d7cb81ba000602010000000100001d88f880010008000100000000000ac9a7aac6010501010002000000000283b28be30205010001000000000108b880030001060000000000000889ead593060001000000030000004f919c80060002000000000002000184f28009,
  0x108010000000000000040fb9f8404020400000000000000499289eb06010003000000000000228ea0800602000002000000000009ec80800700010100010000000002bb8080070100010000010000001aa0800701010000000001000001b4800800010000000000010005d0080100000000000000010a09,
  0x1090101,
  0x3070101,
  0x7030101,
  0x9010101,
  0x402040010bfeabeb4870000000000000000060100031bc4b5f38dee00000000000000010008000123c2b4d3abdc00000000000000030001060018eedddca2cc00000000000002000100070010ecbaa9b7c000000000000300000001000602c59af9ce800000000002000100000001064db796ee80000000010000000100000800119abdfc8000000100000000000100080001a380888000010000000000000001080007a0908001000100000000000000000812e0800b,
  0x60100030001cee0c49ec8b3000000000000000700010002039db7c8add400000000000003000106000001e4d1a9cba9c400000000000100000800000101a2e18aeaecfe00000000000200020102030035c2f7bac9c10000000002000100010302011ff0b5f7cfb400000001020000000100050104a0e5e6b0cc00000002000000000007000104d2eaa6b7da00000100000001000008000001d8e7a6b48000010000000000020103030010a1acbdc001000000000000000108000046fa9f980b,
  0x1000800010000278e80ea96dd0000000000020203010101004f8786e598ba0000000000020301010300000186b4a4f681b900000000010003030101010001abf5c9c384f400000000010200000700000067f19bc0fb8c00000001000000080000000121c7ba828d9600000001000003000501000021f58190f4a000000002000101010102020001f4dbbabfa500000201000000010103010107c0cfb080800002000000000200020102016de4c0808002000000000001010201010205da8080800b,
  0x60002020000000a97e6ebbcd100000000000700020000000102fab6d1808000000000020103030100000042f7deaad5970000000002030201000200002f84d3b3c6e10000000002030201010001001695cba3f78800000001000008000001000012ecbfeed2be0000000200020102030000002ba1d8e491d70000020000010103030000000eac9581bcbe00000202000001020000030001a7ffe5aae400010001000000080000000005a0a69aadb002000101000100000000050019bbd0c1dc0b,
  0x1080100000000000196dc8deba5e600000000070000020100000007d695c08b9700000000080000010000000101a9959ffdda00000003010103020000000001eccce2a5cc9900000003030100020000010011b8fef2fba400000101030102000200000001a8d6fc98f9b400000200030101020001000060ae9c9cc39100000201020100020200000006e9f785b49500010000030103020000000049b2a585aef200020000030100020101000008a7dd95a0c702000000010201020200000004f4baddb0800b,
  0x70001000200000000098afecad9bf000000080000010000000100188880808000000008000100000000000101a08080800000010303010200000000000acbefd089b000000301010302000000000015deb9a9c49000000303010100000200000002829cb2e6e00001000008000001000000000c86e98acd820002000100070000000000005be5f3a9c700020003010102000100000004ccf6dab2c000020103010100000002000069a380808001010000010700000000000004cda583deb00b,
  0x700000201000000000010e9ae87f7dc0000080000000100010000000888b58690800000080100000000000000012a9e8cbc0001000800010000000000006cb4d98ba3ba00010301050000000000000042e7bbc0b0f10002030102010100000000006dc29080c5830002030103000001000000002b829af6808001000700000001000000010009d6f2ede00200020005000100000000001a8ef8aec5c1020003010300000000010000018186d0e28002010200000500000000000023ab95c7a1cf0b,
  0x402040000000000000000088299d4d8b000070001000200000000000005dbdcd1cfc000070001010001000000000002c59af9ce8000080000010000000100000005de94d48000080001000000000001000036aad88000080100000000000000010002b5b0800100080001000000000000000ccbdf8ee8b402040000040000000000000005abee84d5c30300010600000000000000000787cef8d3b806000100010000020000000019e7dcfa8008000000000000000001000106a0800b,
  0x80001010ae7ca940000030104020013e3929e0002000105020004acace50002000106000102f1e6f6000202010102020180ce87020100000106000185c1ec06,
  0x10700000200109bf4930002040103000030e5eaaf000600000103000293d1ba0006010000010202e5d0af010100080000001fc9f9dc02010201030100059fe5f906,
  0x7010212b78ffa00000000030006010d9494bf00000001020103030d97c3da000000020000070102b3e480000001000001080002f8efa600020000010000071190d9010000000000080101aaee07,
  0x800010105eae2f08800000003010402000af0e7d7f6000002000106000103d8c186bd00000301000006000184bf81b700020002010002031edabbd600020100000106005dc486e5010101000000070015b5e89307,
  0x204010300000002e2edccec0002050100020000769c8bb30007000000010101059bc99c010100080000000001adfb83d0020005010000020001f1a6b602030101000102001caecf860400010100040000159ae7b907,
  0x80001010000007df9d1f6000801000001000076a3e80201070000000000018299abbd040101040000000053f78ba3050102000002000008f3fee2050201000001010001efe9de060001020000000109ac8207,
  0x40602db0001020702b8010001081003,
  0x80202bb0004000601e801010305018003,
  0x602020d8d020106010d91040100051103,
  0x7020117c60301050117d4040200042103,
  0x208000002bb0503010101800600040001e803,
  0x604000002db0702010002b8080100011003,
  0x7010228ec82f3a30000000000040101041ac18dd4e3000000000101000800289ec484f800000002000002010502add9cd80000000020100000106018bd7cd840000010101000000077392b3a800010000000201000607cbe1d00100000000020001061c848608,
  0x80001011dd69aabe100000000040101040009f3a6e1ab0000000005010002020b8eee9de00000000101000800001587fbc0f600000002020001050011d5da98e90000010000010800000ce8e2949c00010000020101050001d58b8af80100000002010006000c8ddca108,
  0x701020000029ea693d3f1000000040101040000028cb2ebddbd00000101000800000002a992d89aac00000102030101020002dde9c5f1d800010200010202020005b980c5a000020200000201010240f99293d500040000000001050006c684ecaf01010100000007000011b2cafdaa08,
  0x7010200000073ddbcb4eb00000008010000010063b3acb9f000000501000202000001cea9a98ae700010100080000000001bed99deab50003000101050000004b9dedd3d902010000010600000014ecfed9ad02010003010100000204eabfbfa103010000010005000006f7a4afe208,
  0x800010100000054ffd8de97000401010400000000019eb69fdf00040102020100000035eb89bbe9000501010200000100048cc2d6800006000101000200000fe3b3f1c00006000102000000011de6d9a00101000800000000003feff091e20202000105000000001ff99a93df08,
  0x80001010000000060f5a0e28000080100000100000017b1deb69002010700000000000076e1d6f18b04010104000000000055c8cfc28405010100030000000009f6a38fa406010100000002000001acb1c6f30701000000000002000bb1d2b8070100000000010001548c9208,
  0x80001016ccab4c9f5a40000000000030104020001c5d7e6b08c90000000000200010502006cdee2a4ebf2000000000202010200030eefc1bedcef00000000030100000600088ec2e0c7a20000000200020100020322a3a8d680b10000020000010000070005deeaaed68c00010001000100000700018da892e996010000000200010003030684ffdaf609,
  0x8000101001f98b4db8fbe000000000501000202000bd8aa9c868e000000000501000300010db0f1d0cfc10000000101000800000023b2a6d6dd9f000000040000000501000980caaee2eb0000020001010006000001f4e2eb93df0000020002000103020006c4a1ba9ecc00010101000000070000039ecafb80a9010001000100000700001da89ae69509,
  0x800010100000003b186e3a2cc000000080100000100000ecef9d5e0d0000001080000000000011585f2b5d4000004010104000000000beeb6ce96a90000040103000200000003b899eeabef0000050100020200000007f4c5fef9d60000050101020000010002a9d3add2a4000201010302010000001bc1ccfcc9fa0100000108000000000009cde1fee78409,
  0x80100000100000023d5b2d2a5a4000303010201000000007ddb818582f50100070001000001000003e8dd89999401000800000000000001038be7f9ad0101000800000000000037baa4f4b8a20103030100010000010048ae80b19d020301020000000200000183f3f0cd800300010301020000000006b4eb9de1ea0301000006000000000010d5cba9a6fd09,
  0x3071f0101080902,
  0x7031f0203053102,
  0x107024f0401052902,
  0x207014f0501042902,
  0x40501470601030902,
  0x703001f0801010902,
  0x70102028e9ab594f18aa500000000000000000201070001ecd7b78ddfdcf800000000000000010201030302edb0d599c4cdb800000000000000020000070107b9d8858ff9d60000000000000200000103042a8487c69c89e300000000000200000001010606d1be89f6a4ce00000000010000000000080101bfcebdf497d40000000100000000010102050f90a6c9968a00000100000000010000020665f4c79c8e000100000000010000000008039bf7bc9601000000000000010000000805f4eda20b,
  0x800010107afa3a8d59ef5f400000000000001010008000004e4bfb1c4cbf7d30000000000000102020104000ee8b8f8d6c3aca800000000000001050000000403f29e8c9cd0ed9b00000000000100000108000006f5cab085858cfc00000000010000020101050001ba8687b3d481f80000000100000002010006001485f1bededff000000002000001010000000603d48bc898d7de00000100000000000008000102d7abc1bde8b4000100000000010002000402149992f4c9f4010000000001000000010601458fc8a08c0b,
  0x80001010025a5f4f7a1c88400000000000000080100000108f4d9e5f5e8e0fc000000000000040101040000048ad7add8d191f40000000000010100080000000d8ed9d9b1da90d500000000000105000000040002ce91bf87e39acf0000000000020102010301000d92a0ddedb5d6f00000000001000202010301000e96b3b4ced2d29800000001000002020102020003a7ae90c5c6bdec00000100000101010103020041edc9d7cf9dc40001000000000000080001000692e1aaa7e99401000000000001020103020021b0acbb8c9c0b,
  0x9000000000104968f80c8cbf30000000000010700000200000db1abdac2f786b500000000000700000001010101b3fee3c1f2e0dd0000000001010008000000000cf0e2f187a3cede00000000020200010500000006d5fc84e4aa8cf800000000020202000201010005a793b0a08cb0b5000000020002000005010000058c90f9aee7cd9c00000002000201010200020001a3f6dde59ba1fa00000200000101000500010001bca9948ebbdeca0002000000010100040002001a89d1c6f6c69a02000000000003010002000201d287e8dbccf60b,
  0x7010200000000000192a4a6e2b5ebea00000000090000000001000007e6f691d2a6cedc000000010800000000000100018aa7fec0c8a6bc0000010202030002000000001ea9bca8b7eaeabd00000103010103010000000022e7fee7a2d3cef000000201030200000200000010f4aad0f2a8fff2000003000201020200000000018eb1def2caf4c70001000102030300000000001dc4f0e8c6b5b7e200010301020100000000000203d8a7c79b8fda01000000000900000000000003efe884b3c8c2a402020100000100020000000254e7cec1c7b80b,
  0x8010000010000000001f4aee5e5e8e5e000000303010201000000000004d6eebbc7e1b5ca00000701000000000002000008c28481b389ab00000800000000000100000108d0f5b780fa00010100080000000000000003b5a892b98cdaae00010303010100000000010001cbbcbdd9dfce00020103000202000000000001f080dafa9dbcbd00020301000200020000000070b889fce3c3f200020301020000000200000036db83cea3d6fc01000301010202000000000001a4b6bdf0f9cd840102000100060000000000000182cad5edc2cc860b,
  0x80001010000000000001ac28acfb4f9b2bd00040101040000000000000011cdd9f4e081ddd800060000010300000000000007d5ced2b3dcb9810007010000000100000001002ac2b5a4cae00008000000000100000000010191c2b9e5a001010008000000000000000016c1b4bb86bc818f03010000060000000000000037fc8fc4d7abeb03020001020002000000000006c28db5f194aad003020201000000000200000019fcfcfa93a2a003030100000001020000000001c3ebb6f9df96a003030101000000000101000005d2e989edf6e00b,
  0x70102000000000000000042fa869aa7ffa40008010000010000000000002483bda9f3bf9e010800000000000100000000528face8d3a402010700000000000000000073e0aa9f93abcf03030102010000000000000001a2fdc09cdbf0fa0401010400000000000000000da9a9a7dabcfb0404010000000000000100002bd6c38c8606010002000000000100000006bdebfae4f207000001000002000000000002ec88a8e9c6c608000000000100000000010001b0c5beae08000000010000000000000102c4aeea0b,
  0x800010129f5c0988afda0cb0000000000000000060000010309d0a8d897eaae8200000000000000010100080000168ebaa6bc83bb80000000000000000102010303005fe4aa9fc5e8eeb000000000000002000002030102128cc8d9ac89aaa40000000000010000020102030102fdbae783f4f7f00000000000020000010101020302cbe6fbcaefc9e00000000001000000000008010001abf1b7f587f7e200000001000000000000080001148da29e94b1f80000020000000000010000010665c9e2effb9e0001000000000000010102030209dc9894c1d8020000000000000000000001070dd29db5bf0c,
  0x80001010053e0c8f5c7ce9981fb0000000000000006000101000211cad6f1c9c08cfe860000000000000101000800000027e9a3fa92ed94f2f20000000000000202000203010062d29eb2be8fcfaaa10000000000010002010302010049f0fffea0dcc4abc00000000000020002000104000103b8cde3d980a8b7d4000000000200000001030300010aeccccbcf88d4c5c8000000010000000000080100000299c1eacb8bf5f9b40000000100020100000100030201e2dfb7e7eed583cc000001000000000000080001003ee4be9cf1839ec00001000000000000000800000104d9d4dfa0b5d180020000000100000000010000060aa9a683b0cdd00c,
  0x800010100000001aba898d0929acbac0000000000030104020000000002c68bb2add6a481d1000000000203010002000200001f93f486c4d7d5830000000002030100030000000105e5d0f2a298d9cc0000000003000103010200000001c2aba2a282dfc9ae000000020003000101010200006590be8daab8d5c20000000201000001060000000001f99788a9e2dfd0000000020201000003000002001db59ad7e8d681f80000020001000100030300000023fcd1fba99e928c000100000003010002030000000188a5998fb6909600010002000000000600010000099ccf93bee2b38e0101000000000000080000000063f3d1f9c9aecc0c,
  0x304000102000000001fabc8eab09def88dd0000000100050103000000000010aeb1ab98e5e9febf000000010100080000000000001abc89fdc4fbba91e30000000300030102000000010001c1a7dfafd5aab6800000000302000102000200000007ede3f2eab6a7e9ab000001000301010300010000001981e8e0b3f991e4ab000001010004010003000000000cc5ec99eebe8abbcf000002020100000300000200006ad6eecafee4c9b60001000300000103010001000008b39b8b87c1d18bc001000002000000070000000000438bddacd6899d83020002000002000000010200010eb4d2d2a4e1bca90202010000000000000102020005c4abe482ddf9ba0c,
  0x70102000000000000001edcc0be94f8d1b4c7000005010002020000000000001ce1a7b28c83daa9d50001010008000000000000000018eacfd98dd396c4db0002040001010000020000000044dfe0f5a19ce4b20002050000010001000000010001c4a387d4aabcb0000300020102020000000000000799e1f5f1f488f7f30003020001020002000000000006b99ad5cebaae8e840003030100000002000100000001a5e09bcc8dcbbd940103020101000000000100000106de88b5dbe7dc0201000001060000000000000002c8cf8f9ff6ad8ba4020200030100000000000200000a9eea93939bd39c020201010000010201000000000680c0e08cbfcfb3800c,
  0x80100000100000000000005e8838ae197ef87a8000303010201000000000000001686a7f6acc795fdea010100080000000000000000000982e8add6ab8aa0d60103030100010000010000000026868e85ca8bc1ae0203010200000002000000000073d5918bebbccbe8020301020100000000000100002cfbff8dc8c7a4020301030000000000000001000293b481efefe80300020102020000000000000001a9d1eb82dcbae0880301000006000000000000000002c490aafff9f6d9850301010301000000000100000004b9cd9fabecb1c803010201000102000000000000018ce2c6b2ea90eaa8070100000000000000000000020382c4c1c0f90c,
  0x6043495c900000002020631fcaa0000010101070ff9f0000100010008018b9c01000000010803e605,
  0x80225e2d50000000400062d9c9000000100050422ba8000020000000801d280010000000306108005,
  0x5020304f3e8a5000001000900039dea8b00000301010501b0c79700020100010652d4d00100020001060ab8c005,
  0x102070001c3c7d700000105010303f69a860000040002040180bdfd00010001080001edb3d4020001000106099ddf05,
  0x10601022bd89b000002020600319caf00000500010403869b00020101030315a08002000101010502808005,
  0x20502010a9ee59200010302010302a68ee1000201000700039b8ee30100020007005ce5ab01010004010324fa9905,
  0x502030003e5fdc000010009000004b5ec9500020301030107bebde601000303020102e2c89a02010001060013a88f05,
  0x10207000042acd800010501030003b68acd00030301010201cbfac50004000204005b8fa30100010800000291b08005,
  0x80100010480bbcc00030301030006bad9b100050002020140d4b401010107000005f5e8cd01040000050067ab8105,
  0x900010003d4da9300030205000003fff7a501030103020004f69ca60200020600001deaf80203010101020193b99505,
  0x30601000031dde80007010001011ceac801000900000061cca901040104000001baf99f02030201020071dd9c05,
  0x70101010002d480800008000100012080800105010300000b9bd602010601000003c59e87040100050000759ccb05,
  0x70201000001c3c7d700080100010001edb3d403010501000003f69a860402000400000180bdfd060100010002099ddf05,
  0x900010000039dea8b03020500000004f3e8a505010103000001b0c79706010001020052d4d00601000200010ab8c005,
  0x208000000003783d50600040000001bfb9006010201000022ba80070101000001108008000000020001d28005,
  0x406000000003495c906020200000031fcaa0701010100000ff9f0080001000100018b9c08010000000103e605,
  0x70309ce0003010608e70100040502d703,
  0x207015d89010400052dbe03010006098d03,
  0x60103368d0101080042fb020301041acc03,
  0x7030039e4010700021ea3040005013bcd03,
  0x10702005d89050004012dbe06000103098d03,
  0x307000009ce0504000102d70601030008e703,
  0x8021599a59f9700000000000400060a95f09b9800000000010201060fb4eda38000000002000000087fa3fa80000001000001010713dad08000010000000100086cc080010000000000010802808007]

/-- The triples `(n, b, a)` of part 13. -/
def enumC13 : List (ℕ × ℕ × ℕ) := [(10, 4, 3), (10, 5, 1), (10, 5, 2), (10, 5, 3), (10, 5, 4), (10, 6, 1), (10, 6, 5), (10, 7, 1), (10, 7, 2), (10, 7, 3), (10, 7, 4), (10, 7, 5), (10, 7, 6), (10, 8, 1), (10, 8, 3), (10, 8, 5), (10, 8, 7), (10, 9, 1), (10, 9, 2), (10, 9, 4), (10, 9, 5), (10, 9, 7), (10, 9, 8), (10, 10, 1), (10, 10, 3), (10, 10, 7), (10, 10, 9), (10, 11, 2), (10, 11, 3), (10, 11, 4), (10, 11, 5), (10, 11, 6), (10, 11, 7), (10, 11, 8), (10, 11, 9), (10, 12, 5), (10, 12, 7), (10, 14, 3), (10, 14, 5), (10, 14, 9), (10, 14, 11), (10, 15, 2), (10, 15, 4), (10, 15, 7), (10, 15, 8), (10, 15, 11), (10, 15, 13), (10, 16, 3), (10, 16, 5), (10, 16, 7), (10, 16, 9), (10, 16, 11), (10, 16, 13), (10, 18, 5), (10, 18, 7), (10, 18, 11), (10, 18, 13), (10, 20, 3), (10, 20, 7), (10, 20, 9), (10, 20, 11), (10, 20, 13), (10, 20, 17), (10, 22, 3), (10, 22, 5), (10, 22, 7), (10, 22, 9), (10, 22, 13), (10, 22, 15), (10, 22, 17), (10, 22, 19), (10, 24, 5), (10, 24, 7), (10, 24, 11), (10, 24, 13), (10, 24, 17), (10, 24, 19), (10, 25, 3), (10, 25, 4), (10, 25, 6), (10, 25, 7), (10, 25, 8), (10, 25, 9), (10, 25, 11), (10, 25, 12), (10, 25, 13), (10, 25, 14), (10, 25, 16), (10, 25, 17), (10, 25, 18), (10, 25, 19), (10, 25, 21), (10, 25, 22), (10, 30, 7), (10, 30, 11), (10, 30, 13), (10, 30, 17), (10, 30, 19), (10, 30, 23), (10, 35, 4)]

theorem certs_ok13 : checkAll enumC13 certData13 = true := by decide +kernel

/-- Certificate data, part 14. -/
def certData14 : List ℕ := [
  0x30601018eada2dfb5000000000104010407c5a286e100000000030101053ff192a3a5000000020002000614b6abccf00000010000030105058eece1c000010001000100072d94df80010000010000010701aaee8007,
  0x7020153bfda8eaf00000000030301030193bd98d3b700000001010107005fa78fc5db000000030001020418a5dc93b700000100010008001df3a08080000100000001080002fa80808002000000000002060880808007,
  0x9000101cd9b88c6be00000001020106000197b0a5c3e8000000010301030202b090effdca0000010002010501578ed786d900000102000103030ce892dea7000200000001040305e1f7aae0010000000102040248fddea007,
  0x700010201dfa7bfe7c1000000010009000004b8f0af8dcf000000020301030104f8b8b7d9f4000001000400050001e1f791acc600000201010103027ee9a4abc5000101010000070056bdc6e5b0010000020000070005d4e5b2ea07,
  0x701010103acd7aaa9e6000000020106010004e5a3eee6ef0000000401000500018daaeaf8c1000000050100010325f9b1a086000002000203020102f2dbf5e08000010003000006000180f9828080020000000100070004e78c808007,
  0x801000144c2ed95e5000000030105010073d087b48500000103010202012afdfd8e9b0000020001060100038bfb99ba000003000200050027b097dac1000200000104030010ced787bc020001000000070001b3c398de07,
  0x70100010101c8b6f993ef000001000900000003dac6a9e19e000002030103010007919be1d9fa000200020104010002a7ada8aa8900020201000202012dbad7d5f702000101010202011b95aabd800300010000000600099cb9828007,
  0x7010101002385a7d5d0000000080001000104c1cb94da00000301030300002ade9d98df00010001080000001296b3b09600010301010202001bdba39fd800020001040300000b85e9c2c3020001000500000204caffa0d307,
  0x90000000121c6b7e0ac000003030103000001ecd38682970001010107000000529c88938e00020102030002007cd0b786aa00030101010300010a988f8a01000005010300001b98b0e5c7010001000800000016fe8880b907,
  0x9000100000bb8e6e0ddd100000601000102000695e0808080000007000001010101d880808080000103010302000007aa98c9ed8c00020100070000000afeb8dbe3c400040001000500007a99d1c89b030001000006000001efe0d3a59807,
  0x7010101000007c5d6cbdcb0000008000100010004bffcf4d8a0000008010000000130cfc4849000040100050000000686ccfce296000500010202000007d3a0c7a38801000108000000000bd7c1c6e8a703000100060000000191e0dcd7f307,
  0x1060102000000069690f9feef000500010400000010b5cd80c1000600010003000001e1d3e3c080000700000001020040bcc18080000700010000000204e78c8080010101070000000003dfdcc8b9e603010001050000000190c0f9908607,
  0x9000100000001a7a0c28ff000030205000000000ce8eeb88800050201000200006cedda80c0000700010000020010d0e1a798010301030200000002b89be0b48801040103000000010296e289da0200020600000000638bdee18f07,
  0x601020100000001eebab4dccf010009000000000001cda498a2a2020301030100000001d8fdd188ff020501000100000148fddea0030201030001000057aece87f703030100020100000cc89bdd89030401000000020005e1f7aae007,
  0x60202000000003febfdf8c1000800010001000012d8848080000801000000010001eca0808001070100000000010a808080020106010000000059affe8dd5030301010200000034c7cba08004010005000000000da5c3ded507,
  0x106030000000000018eada2dfb5040104010000000007c5a286e105010103000000003ff192a3a50501030000010000058eece1c0060002000200000014b6abccf007000100010001002d94df80070100000100000101aaee8007,
  0x20800000000000015998a8f9706000400000000000b95afa59806010201000000000db6a5af80070100010100000001fec7f480070101000001000013dad08007020000000001006cc080080100000000000102808007,
  0x70312e084000003010613b2c5000100040508a594010001010738a304,
  0x90105dcbd000003030404b1a70001030006058efb010100020633a104,
  0x1090027e1ac000005010420bb89000301000612ecb8020001010602d79304,
  0x601030186bec70001010800018cc4d4000400010528f2ee03000001060c99f704,
  0x801017fffa100040103025fe3f0010200070054a8b8040000010504b4b704,
  0x10702004db2f30006000103278ab8020101060027a4bf02010400033e9604,
  0x109000041ddae00060003013ecfc903000401020cb7f903010006001f8b9004,
  0x700020154a8b801010800007fffa102030104005fe3f0050100000404b4b704,
  0x8010100018cc4d403010600000186bec7050100040028f2ee06010000030c99f704,
  0x901000023869e0401050000259697050200030012ecb8060101000202d79304,
  0x1090000003cb7030600010005c29c0403030000099e8c060102000133a104,
  0x30700000012e084050400010008a594060103000013b2c5070101000138a304,
  0x102070067d1db80b4e2a8000000000000010501037883cbd480af8c0000000000000400020420ec9cfaf7bed30000000000030000020520d9eaeeaa97800000000001000001070112899cded3f8c000000001000000000801029c8aa28aa7c00000010000000003010516b6daa2bfe00001000000000002020501849a86d28c0100000000000002010602daade5fe09,
  0x1060102378bbffb80b8800000000000000500010410a9ebafe583d70000000000010101070022e0a3b39aeb9a000000000002010201040f95bff088cab3000000000100010008000e89d1d3e08080000000010000000108000283d984808080000001000000000107011888a08080800001000000010001020501a6c080808001000000000000030105048080808009,
  0x7000102018bcea2f3e8db93000000000001000900001bb288a890b0ae0000000000020104030001bce5c9dca0cdf5000000000102000303016699c296a4d3d4000000000200010303012fc5dba4d9c4e6000000010000010503002ac797f6bce8800000030000000000010601fbe1affba480000100000001010203023d8bb29cfcc00100000001000101030302998bb6cae009,
  0x80100010b8c878189d1d5ea0000000000020304010027e997d1a69df1a70000000001050000010307f8ef91c58db18a000000000200010601000a819d86f88fe9e3000000010201000006000d9aae99cda9bdd80000000400000000020430d4eac3b5d0ca0000020000010101030201a3ac908cd7eaa80002000000000100070010d5a1b8f4fe800100010000000100070001c0cb82bcabb009,
  0x1080000016acda4d0a7a6df000000000003040102002ad9cdaec890850000000000060001020149dfc5b4c5dcc30000000002010007000062c7ab97cdf8840000000002010301030066b9ddefc7ffbc0000000200010103030040a1dcaaa2ea800000010001000008000018f0939ce088800001000000010008000002e7c08dc8e48001000000000001080000128586d2c88009,
  0x7000200010383abdfd1afb4000000000100090000000ebee1a1cda0ac00000000020301030100239ff58d99afea0000000200010303010001f7c9d3a9fca90000000200030101030007abd1eee5b88f0000000500000001000402c5b0b2ad84d0000002000001020302000393e880808080000101000000010700000182c0808080800100010000000008000008808080808009,
  0x80001000101d8e69be69fc3db0000000003030101020005caaeb5ca8ab4c90000000004010005000002b6cb84a5f1b1df0000000100010800000001decbcbc4feaef3000000010301010300010199cea8b0c0bca50000000200030103010004cf93a3c9e998b4000001000000090000000395c3db908bd580000200000000020600001ee3b6ac8a83cc010000000101030301000493c19ea9feba09,
  0x90001000004d5ed978497b5b0000000000600010201004d9ec6b8c9dca70000000007000001010101b49ee9d9a5a8800000000201000700000001fff9f3dffcb5ab0000000202010203000006c8cdd3b387f6a40000010103010100030070d28abcd6c5a20000020001000600010002b0dfbfd99b99df000100000301030002000183f6e7fab9dff4010000000301020102000adb93b0e3ef9609,
  0x801000000010590c3e4e282b8000000030301010200003db89bebb7b0a80000000303010200010031ade6e185afd40000010001080000000006e892d6a5d897000001030001050000000bedc3d5b8efbf0000020003010301000041fc83c8f9a3d00000020301010100000226d6e99decc5000100000009000000002494b1fbc0a4800100000000080100000003ebf3ffc2e88009,
  0x8010001000019a4d2b096cffd000000000900000001006292e38689f480000000010800000000010ab796a3a38880000000050100030100006e969ea984a6ed000001030103000200005ea2f1888aacb40000020101030300000001d19485cbdaa6b6000100010008000000002fc5dde9d2a4b6000200010103010200002b9ba5d882dc97010000000108000000000fc7fd83d0d3ea09,
  0x700010200000003a4e7f6dfc4f6eb0000000800010000000105dcc49be89a8a0000040101030000010046bddcae90e9cc0000050001020002000001b29a8987c489e70001000008010000000002f984cb95b08bab000102010006000000001fe3abaae9ea8e0001030001030200000001c38e8bbeac96f5000202010003000200000ed8faba8bd3e9020000010007000000003092e0cf8aec8009,
  0x10601020000000001b5e890a7a897d30000070000000102000008b896e6c2aeb4000007000001000101000ab298fff68b980000070001000001000159de90e0edba000101010700000000002ec4ffbc83d2ee0002010401000002000009c899eceba7e8000203000102020000007fabeca4e4b6e60100010008000000000033ed9eca9dc885010202000102000200000ad7bcdcc2b7fb09,
  0x3040102000000000ad5d6a6b6d8d9f60002010007000000000004ecadfbc0d49cf50002030101010200000003aa86ffc7a5da8f0003000301020100000053fef292c481c8010200040100000200000199b08c80808080010300030100000002001593f0808080800103010300000000000201a680808080800200000500010200000001b4ccfa8fb8a58d0300010000060000000003c1989891b6fc09,
  0x80000010001000010cae29395b08000000800010000000100559a8abdf19d000008010000000000010c83af8cb08000010009000000000000489dc7fbcbe8c80002030103010000000001c9a8b5b8cccbe00102030100010200000006f582d096f1e80200030201000200000019c7fcdac9b0c30300020100030100000013c396b9d0ccc703000301000101000100019abba99da6e309,
  0x70101010000000002e2b5ef8584baf00000080001000100000004f4ab96c9808080000008010000000100006db2f989a480800004010005000000000002a490ac8cc3d9fa0005000102020000000007d6e680f5bde2c80100010800000000000007decfb2efc39ca901060100000000000002208cc0b4dcc80300010006000000000001d8fc86d6dcf5850600010000000000030003da87b7a89c8009,
  0x3040102000000000001a79295ac9db5cf010008000000010000000de0e2eae38e95010303010002000000002eddeb9ef3b7be01030500000000000001019e8eb6da860201000700000000000044d9bcd6c2a0e20301020101020000000008e195e39ccbe20501000100000300000003acd991f4fde306010000000000030000018dcee2fdaca00700000000000100020011979a90938209,
  0x6020200000000000023ebfd97fda0e70008000100010000000011cc8688d880800008010000000100000002c4cfa5808080010701000000000100001e8aa8808080020106010000000000003fd8e1afe3b0b30206010000000000010001d0908080800303010102000000000028d7ee848bc080040100050000000000000bb9a5d5defcb306000201000000000001058080808009,
  0x7020100000000000067d1db80b4e2a80107010000010000000012899cded3f8c001080000000001000000029c8aa28aa7c0030105010000000000007883cbd480af8c0402000400000000000020ec9cfaf7bed30501030000000001000016b6daa2bfe00502000003000000000020d9eaeeaa97800502020000000000010001849a86d28c0601020000000000000102daade5fe09,
  0x70310c4ed8d00000003010612aaa9e70000010004050989a2a20001000101075ec2e50100000002070389f505,
  0x90105b1bcc50000000303040383ea8400000103000605ebfa9a0001000005044ebec401010000000803cda905,
  0x1090005aa8ae300000005010405d1acac000003000205039bf08a000200010106529b9c01010001000709ea9b05,
  0x6010303e3ecfdef00000101080004869fe58c00000400010501abcee78700030000010646c5f3fc02000001010607b7e6c205,
  0x801013ce586890000040103021eebb790000102000700259e87c60001030102031bcd839601010000080007b9a2fb05,
  0x108000148fbb3b30001020205000180e7f9c40001050000041c81bf9500020103020203baf1d1010003010302148998f305,
  0x10900003c93d1d900000600030136f3df8800030100060012f8eefd00040001030216e2cad5030000000601079280bd05,
  0x700020104e7ca9d00020105020007e3c58d00030202010236c3ff0100000900005ac6d7020100030301019792d005,
  0x80101000c8c82af00000900000118c6dfb80004010302003aa4b586020001070000159888fa040000010500038bc59905,
  0x901000028ef85bd00040105000003aeabb700060001030023ede6d80201010600001faac1a002030102000207e58c9405,
  0x10900000023d082e400060003010016e5ffea00070001010109b9849801030400020016b488ab0301000600001cf7d5ef05,
  0x700020100259e87c600080000010107b9a2fb0101080000003ce586890203010400001eebb7900302010301001bcd839605,
  0x80101000002838ff2c603010600000001f2c5e7bd05010004000053f9b9f306010000030020e5d7e806010001010107b7e6c205,
  0x901000000308ab6af04010500000029b9ae8d06000103000012bdd2c00601000201000af2859807010000000227a8ec05,
  0x1090000000005e5e69d04030300000002cfc0ac06000301000005ebfa9a0601020001004ebec408000000010103cda905,
  0x3070000000010c4ed8d0504000100000989a2a206010300000012aaa9e70701010001005ec2e50702000000010389f505,
  0x502037687bfd799fbeed1fa00000000000000000101070131a9c494d0bcc0fb8d000000000000000003010105479ccaf2c1a59fced100000000000000010000080140b48982fd92d6948000000000000002000001000704ec8de8a285c19c8000000000000101000000010701ad86eabf8abbf0800000000001000000000201060f91b1fee6b5e08000000001000000000001020676cee8b5a5a08000000100000000000001010704ebdabbd2c0800001000000000000000100080f96cbd3808001000000000000000000010815cff680800b,
  0x105010302cee795f8f2a38fffdc00000000000000000400020478d789aeab908e809100000000000000010001080001f5a6bbd3dacdd1efa00000000000000100000107010382c1dd8abca7ba9400000000000002000100010617c0ba8de9a7d382f600000000000100000000080106c5be96d2aaf0808000000000010100000000010761b0f3dff3908080000000010000010000000107078cf38dd4b2c0800000010000000000000201062c97afe39bac8000010000000000010000000801a4f9b2ae90e00100000000000000010000080297f4e4fcea0b,
  0x702010cad82cdcf96ecbaad96000000000000000005000104088ff4848aeea9a7b2fb0000000000000001010107000ab4ef9dc1fff2d9c99900000000000000030001020402a8fcf2e086aad9e7cd00000000000003000000010601b0d295f4d4b18880800000000000010000000108005a92ebdeff9ec0808000000000020000000001000705bdeea18ad280808000000001000000000000080177bbcf94f080808000000100000100000000010706e3ce83808080800001000000000000000104041dc4c8808080800100000000000100000000083ac0808080800b,
  0x90001068c98d1b492d39e9be800000000000000000501010305bafab6e8d0ebff81910000000000000002010007000794d493fff18fb9a48000000000000002000101030301e99b81a7e6c594d7ab0000000000010000010107001ae0eecfafeb9c9bac00000000000201000000010623dfcc9db4e4c585aa0000000001000000010008000dddc1fd989dea9bd400000001000000000001080001abf79fdb8bf7eaa00000010000000000000107010b9ba0d6d1bcd7d00001000000000000000008013894e0f1b0c8b80100000001000000000000087feebfdedbac0b,
  0x701010108db95becfe28184ef8000000000000000040100050002e6d19c89c0d1c0a3ca000000000000000500010202068fd481ddd6d2b889f800000000000001000108000009aef3c0c9d194f6819100000000000003000100060001c488eef582a79daaa500000000000201000000070002a4d9e9b2a9edc480800000000002000000010007003aaca2cef687b0808000000001000001010000070010a495c8d0c9c0808000000100000001000100070001c1f092d4f28080800001000000000100000107000ae98b94e88080800100000000000100000008002391efe08080800b,
  0x80100011ef9c5dca5e4ede4fc0000000000000002030401004db8c88bf490d3abf00000000000000005020000032394e19ecb8bdbb6a00000000000000201010303005bbc808884d886b5800000000000020000010403001ca7f3ea8dd28e96c000000000020000000104010201bbb4ceb7b8aa81e000000000020000000200060004e5e2ca889e9da18d0000000200000000010007006fffa69d9da6d4d60000010100000000000107001880a98baf94d3c400010100000000000000070101cadefced82d4e401000000010000000000080005da9cb9afb9e60b,
  0x900010020f3e5a5f9a4a2e3d90000000000000103020103002982f59999bd9c8a8700000000000001030301000203e5e5c7d5c49d98eb00000000000002010007000025a284cfc1ca9eb1ea0000000000000500000003020694cf879dc8a6c6f200000000000100030201020137f78fb9eee5fa96800000000001000100000800000dd290a0ec98eefc8000000001000000010008000002aa8fa1daa3bbc48000000100000000030101020221f7aaabc9e1a88000010000000000000107010002a8cf88cc9bf080010000000000000000080100099aca87bce0800b,
  0x7000200010dd3a6a9c4daddccf8930000000000000203010301000189fcae97879db8a4eeed00000000000100000801000026ceeae1e4d4d19382fe0000000000050000000002030bf8bd96a292cbd2bde400000000010001000600020017dad79d91b9b5d7dbf90000000001020001000303000caaa8cee5a2caa8a48700000001000000000800000105ecfac8b9b4cefa99b400000102000000000000070062d38e9db5d8c2f3a60000020000000101010002030fb09acba593dec6ad00030000000000000000020503c582c0808080808001000000000000010501000232d88080808080800b,
  0x80001000111adb3daafabb7d2fa9000000000000003010303000047c4e4adcb8a8bd4a0d00000000000020003020102003595f6b4e8fbfed0fbdc00000000010002000500020007a882de858dd0d0efe600000000020000010303010008c6f49480e7aff580ab00000000020002000300010204efc7dda0eeadaaf1a200000001000000000801000002d1d5dad2f0c299be8600000002000000010301030002c09fbda28482d5fb8d00000200000100010003000348f7b7e0cb9e84cec800020000000000010102030106c3a3a6facdbbd99c03000000000000000000010616d2e8fbe2d4dab40b,
  0x90000000160edade6d5c19699d8b10000000000000303010300000393cccdf58ac2e7bfe1e20000000000050000000104000188fee5bf8695e7bed28600000000010001000800000001d9c7a2caabe2c1bfe18c0000000102000001010203000cd985ffdfa0c4d8d5ba00000002000002010100030104b2cff1a2b0e3ded9a70000000200010000000700000e99aba4cda6eff5bfe200000102000000010102000303d6a3cef488ffa1ea9a00000200000000020102030002fa96c8c8abd9efeef300010002000000010100030277acc3bba2fdad908002000000000000000007000102d1e7d9ffea9ef0800b,
  0x3040102000006ecbac7ba91f8ddb6bb00000000000007000100000201dda38880f18fdcc0d50000000000020102030200000eb3caeaa8b1a8bec2e6000000000002030101010200048fbaecc884e1939d9a00000000010000060200010005b5ed92f3e78be5b2ce00000000020002000302010004989df7cf92f4fad9d200000002000001010301020001ebf0919d9db5ffbd8000000100000001000800000048b4e8d4abc5bd8da40000010002000003010000030acaabd082aedab59c00010000000000010800000008e1aad6a9e9b5d7b00200000001000001010002031af3a4d489bd9fd60b,
  0x1000900000000068f83fbadbf9bb6c5830000000000020301030100000c989dddeb8fd29fa69500000000000600000003000111c1d4dd9eb081bcae00000000020003010103000003bb81b3a78dd480d6fe00000000020103000101020004dcd0c5efae8eb0f9c500000002000100000601000001e9e7f197ffb1ae99fa000000050000000000010004208b8fc6eadc9097860000020001000000050100012b8dedc79e94c287ba00000201000001010002030017f6fcd3f0d2b6a1f800020001000000000007000008b2f2da899bd781c601000200000000010003030078daf4f2d4c887da0b,
  0x9000000010026b8ada7b7d6f9d0cbae00000000000700000001020003b8b5bdb0d6899eabb20000000001030103000200000fc587ef8ce4a8caad8e0000000002010103030000002784f2cbbfa18cd6b9990000000002030100010300002bfc8ceee397fc8b81a900000000060000010000000301ff808080808080808000000001000201030300000044a78af5dbb186d1a2920000000202000003000102007bc5eef3beb9f9aef700000100000001080000000010e9f2e1abf381add08000010000000100070001000002b5cfd998daf7b2c7c0010000000000000801000000149dc98cf1c9fdecd60b,
  0x900010000001feaabb598d6fb9888db00000000010301030200000036ffbbd98f8a9bcfca960000000003000104020000000787998ec1c4f9e990af00000000030201010003000010dfe1b48fbf9caae3da00000000030301000001020009f8c2b0e5908f93f3ae0000000200020003020100001f8bdf93fb9eb080808000000100010000080000000004a8f5faa1d5ecb8ffc500000400000000000202020002b9b694a6c89ffce9e200000500000000000100000431bed2e1adb790ded70002000000000007000000010199b6e39bc8808080800201000001000000020101020b98cee9c0808080800b,
  0x800000100010001d5e486b7e2938feee200000000010009000000000006d0f78abbaee193d9f000000000020301030100000009cda0b9f0c1c9f6d1ad0000000007000000000101012185e0849bb5d2e5a00000000102030002000200000681b88eb2bee693f1dc000000030001010203000000049ec9f5b6ee90c6a48d000002000101000303000000029aa9a39ca9809292c800010100010001030300000067b2efb78af6ea8cd600010202000000010000040019aaa4cabdd7baa2f000020201000000010000020201a0ddeac0a2cae09d0100010000000008000000000ad995abc8fcafa0800b,
  0x80001000100001cecd1adf8ceb6d8abe70000000003030101020000007ead8faeb1dad8dfcda3000000020300010200020000169cbb9089eff9d483a600000003000100060000000033d681bd90afedd5c0df000000030300010000010200058bdd94c1f993b7bfb70000010000000900000000003bc198f0c6a5a7dc89fa00000203000100000200000273829596ccdaebb1f500020001000102000202000002b5ed85d8e4d3ad8b9b00020200000100010002020004bbb98bacc2c996fbf00005000000000000010001031aadab8aa0e389b2010001020000000006000000019acda080a3f28fbafc0b,
  0x900000001000001b3f99ea7fe80a286d4000000000303010300000000019ec485c89992babdb7000000000701000000000101059fbef58380e79dcc00000001030103000200000002acabbbfa93f5e9f39600000002010103030000000003a987db83f7d0fcb8e9000002000101030102000000019989e0bced90d9d7c800000200030001020002000027cfaf918ca1b98da000000201030000010100020007b7bea297f88d9b980002000001020300000002000ff9ee9387bea8b5aa00020000030001000202000019c79baeeeead7cad602000000020100030000020003f4f2d6b09c8080800b,
  0x900010000000008e0bed4f0c6ceb1d7a9000000000800000000010001119bdab6a3e2ffa08000000001030103020000000019b3b0fcd5b987a5a4e600000003010103010001000005b4958ca6e7cec2bab700000201010102000300000006eff9dcfbbabcff83d200000201020100020002000072acee80eba8929ef700000203000100000300010001a0f69e82c6e983c9940002000003010000030100000184b4a38cb98bd68e950002010001000102030000007087a9f9d0feb08bd80003020000000001000202001993e38bdac0f793b60200020000000100030200001cced2d0f8d194c5ad0b,
  0x100090000000000000ff1abefe4bdadfdba00000002040100030000000018c18fa4feccf3e0f000000002050001000200000007e89693bf9fb99bd10000010004010301000000000488bdace5d1a4ddb000000100070000000002000001c1d5b6f0e6ad8bd90000020203000100000002004ce7f1e88080808000000203000102000002000002aeb4989499d2f4a7000003010001030002000000079a8f8ee490c6e4af0001010100000700000000000bfc8a97a2fb85b8a001000100010007000000000001af90f2c1f69aaafc01010100020300000000000205b3fdc0808080800b,
  0x800010001000000799aca9dd983df82f00000000303010102000000000582f1b7f09cd2f580dc00000100010800000000000002d195cccfa4fba69ca30000010301010300010000005bf886b4b3fae49d8c00000202010103000001000070cfcfc687d7f580800000020301000300000000010187b3c18be5e08cb00000050001000000040000003b9dddba92d7f7988100000600010000000000030002b8a99ce2ddd2898c000201000000070000000000019e908080808080808002000002010003000100010008efa3e1addaf580dc0200010001000302010000000b90dc9ed2a58affa40b,
  0x90001000000000007e4febdd0dcac83f89a000000080000000001000100158feeb1dfe1abafb80000010301030200000000000da49195a18fd7baa7be000002030101010200000000058fa5aacfd5f397daee00000303000101000200000002e89ac1e0eda3c9b38b00020101000301020000000005aaa6ed9ad684cbb08d0003000301000000010200004adc8b8da3ffe28bc80003000301000100000100010197e98ddfb1cee0e401000100000800000000000001d593d4c0afc19589b80201000200010002020000000288fce6a7aaeffbe60202000101000001010200000a989acac59f90dfbe0b,
  0x70001020000000000019a9e8b91a18eaea2ff0000000800010000000100000ed7bdd795f4888ce000000301020301000000000001c982f7f69898f2cbd4000003030101000200000000019e9296c4dcd8b884800001000008010000000000000197b3def79f8ad3d7dc00020100060000000000010001c6b1f1de85ecf8e800020101010302000000000001a4dfbdb8e2a1fcc79700030101010200000200000053a08385b6a393ee01010100000700000000000001e4debede81acf1a20200010005000000020000002985d6c0c8c4e6cbf502010003010100000100000109c2b2b1b8c2fbba0b,
  0x8000100010000000001f6b4bed2c4bec5c590000003030101020000000000069fb0c9b8e6a6fcd0800000040100050000000000000bd08488dbdaa6b0c600000700000001000200000047c9f898ecc2daf080000007000000010100010000179bb8a3de80f0c08000000700000100010000010002a18ebc9b91b180800000070000010100000000010ce4d396a2de808000010001080000000000000003dfd3cae49dc59680bb000103010300000200000000019ea99d9b918db3edb800030001000600000000000001eac4f5ffb393fef3c7020100000007000000000000018aa2c3f0e388a38ad80b,
  0x206010000000100000006d7dcfeb180fe9bab0000030301030000000000000ae1e5cada89acb2c7d100000800000000010000000109b086a5bce6c0fa00020102030002000000000007b099dd92a48898c8c0000201040100000200000000019efebaccd990a6a3b20003000401000001010000005f898e8de2f9e0caf301000100080000000000000002988ec49cb2f996bfc202000005000100020000000056ed8fd883e18fc7930200030201000000000200000a889cc8dee68c8dcc02010300010000010200000010cea0cef1dcb8afc903010200010100000000020073a1c5eaebbf87fa0b,
  0x9000100000000000049b8bc8d99fb9fc8f900000600020002000000000001fbedbcc699b2c4cfa300000800000000010001000006c5aefc808080808000000800000001000000010044dac0808080808000000800000100000000000102c8808080808080000100080000000100000000698db2c3f9cbe0ba920001010700000000010000002feb9fbae08080808000020102030200000000000005e2dcfae69a8eb2fda70100020007000000000000005df6dda5f7a4ddb3d30100030300010200000000000191e591fcfdddbbb0dd01000303000200010000000079c887eebab49fc5ee0b,
  0x70001020000000000005082bca9d5dffceebe000008000001000100000000269993f5c8c5d0a88000000800010000000100000006c2ddf7fce3a6d8800000080100000000000100005f81a9e0b4f6f08000010401040000000000000014c2a6d3caa1f7ece70003030101000200000000004ea6e2b7b4dbc4d280000401000302000000000000018299aca2b2d2b6a4c2010000080100000000000000019fe3e5b3f399becaea01000700010000000000010006bec3e4ef81a08001000701000000000000000119e482c890c0800201000106000000000000001b80f1e9ea8b9debe90b,
  0x80001000100000000002699e587abd7b7a987000008010000000100000000299186c9b6e382c7c00003020104000000000000001db393d3efeb9bcaec00030301010200000000000002acc592befd8f82e5800003030102000100000000000193ecb8d6c09fcab3f901000108000000000000000001c7b5e4ede7b3dac08601000700010000000100000006aeea94c0ede6bef00100070100000000000100005488f5f6b883bba8010303010100000000000100059a93bee69b84a40201010105000000000000007dddedd4d4f8b0c9d902020301010000000000000112dfa6cee587860b,
  0x8010001000000000000098998d3fbd5fc81c19100050001040000000000000002a8d6fc89d1e6a7a3ca00060001000300000000000001e4b4ddb6c6ca9aeaa500060100010002000000000002a4d9e9b2a9edc4808000070000000200010000000074d8c59dec8ee0808000070000010100000100000010a495c8d0c9c0808000070001000100000001000001c1f092d4f28080800007010000010000000001000ae98b94e88080800008000000010000000000012391efe080808001010107000000000000000008ed8fb5cac1b4c4ef800202010005000000000000000686d786a0a6f8d889f80b,
  0x70001020000000000000002d8a18f908a8298d98200080000010001000000000028da8a9fd3d5d5ad80000801000000000001000000479da4f4af80a2f001000900000000000000000002c2a0fd8fc1fbc089e001080000000000000000010017a299c1a0f5e403010105000000000000000002a8a3f2dc8ba4bb819a0303010100020000000000006882d389e485cbf38003030102000000010000000005d3bbf6e4a8e3a8fe04020000040000000000000007c9b898a09ff1bf9f07000100000000010001000004d2cdc4e79ed09808000000000000010000000134fcb480ebaa0b,
  0x70101010000000000000002bdb2a9a4fec0d298b300080001000100000000000001c7a2aeab9993a0808000080100000001000000000021f5f8d2c98680808001020700000000000000000004cbaef5f780bdfa89d90108000000000000010000002cf6d8ecc08080800401000500000000000000000383ff979adac9d78ea905000200030000000000000001acfbfcc8d9e085f7ef0602000001000000000001000b8de0808080800700010000000002000000000287f9a9fdb880808007000100000100000001000002c6a3f4808080800800000000010000000000011680808080800b,
  0x80100010000000000000001f5a6bbd3dacdd1efa0010701000001000000000000029cb9f4fab4848a9401080000000001000000000007a6ef8ab29e80808003010501000000000000000002cefa9de1e2daf8ebdc04020004000000000000000078928e8c9bff8dcc9106010001000200000000000017f784bbb895fdfaf606010002000000010000000061b0f3dff3908080060101010000000001000000078cf38dd4b2c0800700010100000000000100002c97afe39bac8008000000010000000000010001a4f9b2ae90e00800000100000000000000010297f4e4fcea0b,
  0x1070101000000000000000031a9c494d0bcc0fb8d01080000010000000000000040b48982fd92d694800302050000000000000000007687bfd799fbeed1fa050101030000000000000000479ccaf2c1a59fced10601020000000001000000000f91b1fee6b5e08006020100000000000100000076cee8b5a5a08007000100000200000000000004ec8de8a285c19c8007010000000101000000000001ad86eabf8abbf08007010100000000000001000004ebdabbd2c0800800010000000000000001000f96cbd3808008010000000000000000000115cff680800b,
  0x1050430b9a9cfbb000000000301060cd0dbfe930000000200010706edc0c8ca0000010100000801c0fae1dc000100000100080a98ebc8010000000001081cdcc406,
  0x1090053f8ae9891000000000501044189e7e683000000030100062ed5bbcdf0000002000101060bdfc4d484000200000001070187bbdc8c010001000001070a91c3ec06,
  0x6010331f4ddb6d00000000101080063a6cafd88000000020301043fecfebdc40000020002010518d6ecac990001000201000605bafda4bc02000000000107108e9e8f06,
  0x80101019ab4aaabc40000000301060044ad83c3cb0000000501000479bbb083b70000020001070078e880d2c200020000000701138dbc9ddc0100000100080002c2a2dd9c06,
  0x9010001808f8eabfc0000000500040101ecbb9ef0990000020004030101f4ea9499ac0001000302010349ee8ee8c60002000100060104f9a6d491010100000008000781aa8de806]

/-- The triples `(n, b, a)` of part 14. -/
def enumC14 : List (ℕ × ℕ × ℕ) := [(10, 35, 6), (10, 35, 8), (10, 35, 9), (10, 35, 11), (10, 35, 12), (10, 35, 13), (10, 35, 16), (10, 35, 17), (10, 35, 18), (10, 35, 19), (10, 35, 22), (10, 35, 23), (10, 35, 24), (10, 35, 26), (10, 35, 27), (10, 35, 29), (10, 35, 31), (10, 40, 7), (10, 40, 9), (10, 40, 11), (10, 40, 13), (10, 40, 17), (10, 40, 19), (10, 40, 21), (10, 40, 23), (10, 40, 27), (10, 40, 29), (10, 40, 31), (10, 40, 33), (10, 45, 7), (10, 45, 8), (10, 45, 11), (10, 45, 13), (10, 45, 14), (10, 45, 16), (10, 45, 17), (10, 45, 19), (10, 45, 22), (10, 45, 23), (10, 45, 26), (10, 45, 28), (10, 45, 29), (10, 45, 31), (10, 45, 32), (10, 45, 34), (10, 45, 37), (10, 45, 38), (10, 50, 7), (10, 50, 9), (10, 50, 11), (10, 50, 13), (10, 50, 17), (10, 50, 19), (10, 50, 21), (10, 50, 23), (10, 50, 27), (10, 50, 29), (10, 50, 31), (10, 50, 33), (10, 50, 37), (10, 50, 39), (10, 50, 41), (10, 50, 43), (10, 55, 6), (10, 55, 7), (10, 55, 8), (10, 55, 9), (10, 55, 12), (10, 55, 13), (10, 55, 14), (10, 55, 16), (10, 55, 17), (10, 55, 18), (10, 55, 19), (10, 55, 21), (10, 55, 23), (10, 55, 24), (10, 55, 26), (10, 55, 27), (10, 55, 28), (10, 55, 29), (10, 55, 31), (10, 55, 32), (10, 55, 34), (10, 55, 36), (10, 55, 37), (10, 55, 38), (10, 55, 39), (10, 55, 41), (10, 55, 42), (10, 55, 43), (10, 55, 46), (10, 55, 47), (10, 55, 48), (10, 55, 49), (10, 60, 7), (10, 60, 11), (10, 60, 13), (10, 60, 17), (10, 60, 19)]

theorem certs_ok14 : checkAll enumC14 certData14 = true := by decide +kernel

/-- Certificate data, part 15. -/
def certData15 : List ℕ := [
  0x700020105cd92cc96830000030202010201a2e5fa99d50000040001050003f889a0cb810001000009000004eb8dda98c1020000010302021adfa5efcd0301000000000603d6e38d9906,
  0x901000003edb48a85d10000050102020002f1b79fb8ea000105000200020181eef8be820002020103020004a594d182910101010007000001a5a7b7dfdf040100000000050dc28a91d306,
  0x60102000168a4f6aa000100080100000d84c7aab8000105000202000e9b95cfb20001060001000201e7bed6840003000205000001cae1e3a70201000007000003a798f6c106,
  0x900000100029bbe988fc00004010302000002c4a2a081ed0006000101020001fd828ae6000601010000020ef1f3d0ab0102000700000001d4ebc082f003010100050000658cd1f0d206,
  0x1090000000045bcccc79c0006000301000034bcd2adf60008000000010102e6f79f900103040002000047d8f8bffd0106000100020010e092b6c80301000600000040f2b8f59906,
  0x7000201000023eaf7c69f000800000101000f81b8bbf60101080000000042daff9ce6020301040000001cc893f6f2030201030100002c89f587e8030301020000017ecdd2ab06,
  0x8010100000063a6cafd880301060000000031f4ddb6d0040103020000003fecfebdc40501020002000018d6ecac990600010200010005bafda4bc07010000000002108e9e8f06,
  0x901000000001586c7a3e5040105000000001099fe9be0060001030000000bd5aef3bc0601010002000002d6829dfe0700010001010043ddee860701000001000102c4b0fb06,
  0x3070000000000068d95ccc20504000100000003e6fefcdc060103000000000789dcfca807010100010000309ed8b70702000000010002c69af20801000000000107979106,
  0x9014881ded6d18f000000000004010547f995ecc195000000000201010622c2e4ccbf9c00000001010100070c91b0d18ef800000100010001070189c1c9f4a8000100000001010706e1d3afd80100000000010008129fb7c807,
  0x1090001c9aa9781d1a1000000000005010401d5c1dad484db0000000003000205529fd3a7c4f8000000010200010649c1befef8d80000020000000107048ea5cae4f4000100000100020641b58fe6f8010000000100010701df81d4c807,
  0x6010311b4b6baaed60000000001010800138da8c09eba00000000040001050784cb8ef6b1000000030000010603cbe1e3ffb200000200000101065e91e2d9ec00020000000001070796abb4d701000100000001073bebddca07,
  0x8010102f0a08ebeb0d3000000000401030203d8a5ef91dbb200000002000107007edada8f84b600000004000001053bb1c48292dd00000101000008007580ddb7eef0000200000100020506a0d2a3cbc8010000000001080049aff48ab007,
  0x9010002abfb8c9990e9000000010300060002b8b0eae9daf8000000010401010301eeb1aeebe290000000040001010408d7cad4af8300000201000103034edcd7f7e5cc000100020001030313c6dab8c3880100000100000800018599a086b807,
  0x601030001c9dd93968ddf00000000070100027adfa2f8c089000000030201030103f5b7e6b1bca6000001000009000002c5fcd1f48bd700010200000007003acceac0be91000200000101060006ec99a2bfc501000001010303010586f0f4db8507,
  0x900000102e5fcd68eb087000000030106000068f1fd8b9a8e00000006000101020fbefeb081fd000001030102030005a6d6a7f4838e000002020103000226f2bcb18ec8000101000008000001c89edf9eae97010000010008000011fb8d9c9ec107,
  0x90100000a9debd784eea3000000070000010204d3b1e9eba9d700000103000600000da0e8d8fb8487000003000301030008f3e1e48eec8d000100030201030007c382c2eda2fc000201010201000343ede3c6bac801010000000800007bc093fcafae07,
  0x1090000006bf8b0cbe0c8000000070100000223f983cbb58f000002030102020001b9e4d794b1fb000003010006000010ef89c4878800000400010302000e9bf4cdcaf6000200010106000038a0f690be8201010001000700000eb4eed4cfae07,
  0x70002010001dcdcbbaaa7f3000000080000010167c483a2d7b0000003020103010005e69bd1a0fdfc000100000900000003a6cc90f19a9400020002010500004cfeeefad58600020003010202002ad9c6e48bd60400000100000104158b82fcc5f107,
  0x2040301000010d3f4d6feb880000200050100020001fffccfeaa4e0000201050000000225cbe8b7bcd1000203000103010006d6b586fc849201000104010300005e82b9e9e9d6010100000800000001d4cbadb4c3ec020201010000020238d6b3f5a8fb07,
  0x90100000001d7f0e197c190000006000103000021de93888e90000006010100020070c1eca0fc8400000700010001011ce9dda99edc000201010600000001b9e4d794b1fb000203010004000001d69cc0afc7e7020000010700000047f28796ea9e07,
  0x109000000000bd7c4c391f9000005010400000045eab5f3c400000701000002007ca3da82e500000800000001010180c2e1e5aa00020301020200001589acd3d9c1000203010300010006feebd5a39a020001010600000005d5c289c4d907,
  0x104020300000004a5c8ecc296bd000105020002000001a681d985a2d2000302020102000001bce984eac79f000600010000030038989bbdf3b2000700000000010207f59581ccae01000009000000000190a8918ba1c802010003030100000185c3cf82e4aa07,
  0x205010200000001c1cbec80a683000700000002010016d6fcc7ff90000700000101000101caf8e0ecf001020007000000005fadaecec28a020005010002000021ffb2f785df0201020203000000189e88a1e7a302030002010200000c86b3aab6f107,
  0x109000000000002abfb8c9990e90006000301000000019af7bafa8fe00007000101010000019db9afefcb980008000001000001018599a086b8030101040100000002bd8e86e3c7dc030301000200010013c6dab8c388040101000400000008d7cad4af8307,
  0x70100020000000282e6b2d8fcae000801000000000149aff48ab0010108000000000002defac990d89b020301040000000003d8a5ef91dbb2050100000400000016cbef8b92bd050200000003000027809f92cfd0060001010000020006a0d2a3cbc807,
  0x1070002000000000292d3f9eceabb020305000000000003f0ded1a99bf003050000020000002c8ac8f7a7e706000003010000007facd9818bea07000001000200000dcba4d1e7a40700010000010100029efdc8bb98070100000001000109aceacfc807,
  0x901000000000046ca8bce8dd704010500000000001dbebcf2cd95050102020000000041dbc280ffa4050103000100000018c0bfd4fdc806020100000000014aab9c98070100000002000001a4c3d6a5e8080000000001010015e785a2a807,
  0x1090000000000004881ded6d18f050104000000000047f995ecc195060101020000000022c2e4ccbf9c07000101010000000c91b0d18ef807010001000100000189c1c9f4a8070101000000010006e1d3afd80800010000000001129fb7c807,
  0x10702379fe6fbe187a20000000000000401051da0e49682f39c000000000002010106198c9d838dfb8200000000020000010703fdbfe6f5cce900000001000001020667aaef81edd800000100000100000806c6a9a589d40001000000000100081eaea7bae80100000000000001083dca8bc308,
  0x109006eec81c69cc0e10000000000000501042baaf19c8fefeb0000000000020201056a83a48fa1ef9c00000000010003010529e9ef91b6bed000000002000000010702d8f4e5c5c2a000000100010000010736fe9ba8e1e000010000000001020602c0cab1c7c001000000000100000806b1dbb68808,
  0x60103029dcae3d0adaef600000000000101080002bbc1a58abbd7cb00000000000400010577b4918be096da000000000300000106408fd3a0e9e9aa0000000200000101060eece0f3bff88800000200000000010701b9b387f59aa600010001000000010714c794e6c1d80100000000010100073fe8b1a5b508,
  0x801014dc689b3bb99b000000000000301060054fffdacc1ee0000000000050100044fa2cbbdd590a200000000020001070049a5c589ffceb50000000100010107001fd2b8d2aaf3f800000100000100080004a2bebff7c8c40001000000010007012a918193fac801000000000001070101b5f48d8f8708,
  0x108000117c4e4f499b6d9cf0000000000050004010a9b9cb78bd4f38500000000020200050116d0f2d4898ede8c000000020000010700039b9f88aaa7a4d000000003010000000601b3e681c6a19dc800000201000001000673c0e696b1fbf80002000100000000070aa8a8d8f381c001000101000000000766e7f1f895d008,
  0x109000004c1b7f28b9083de00000000000600030104d09edca3cde5a70000000004000103025387bbf9e5f0d700000001020001060001dcf780bb82a1ab00000001030001020302a4c1928292f7940000010002000007005d91a7f884c0dc00010001000001070009bcab8eb097f801000001000000080035f893f2b59108,
  0x70002011ddce7eac6b1e5cc00000000040001050017b9f4a1f89e94c100000000050100000403879faed4efc28a0000000100000900001aa1cdda9fb782de0000010200010102030488cbacf487a0f9000002000001030202018badbb84eda8f100010101000001030368ecb6c0cfe4b801000100000001070005a4f493c592e908,
  0x90000017daef1c48ea69f000000000500020300018ac5b9cb82beb600000002000107000008dc9de2bb90d00000000202010300020f96c4868cd8860000000400000105002be6ace492e2ce0000010100000800004c9b96e29a92b40001000001000800000b8bf2888adaa80100000000010800005ab5b9efe3ab08,
  0x7000001025ce8a5adf68ad300000001020303010006e5f9bfac83b3ee0000000201030300013bf8e0b5a4d08800000005000000040114f5f0a78eccd000000100000700020071c8f2f2eeabc400000201010003020153bac5aab0cc8200010100010103030036b4a1e38adbf002000000010200030201f7c0c9a9d1b108,
  0x109000000058085f7adeaaaa200000000070001010103c5b0aaeaa5d4bc0000000400010302000289f0fc92d688c500000101020006000003d28fcd9be68df200000103000102030002dbedafa7b1b39e0001000005000004003cd5b3a3cace820002000000010700002b9de5ee8fe18f0100000003010302000bd1ac80a888bc08,
  0x60103000011feb3efc3dbee0000000008000001010181f7fef6adf898000000030201030100039df1bfd5d0c4c000000100000900000001d6dbcff5e98ed500000200030102020029cfc1c083d9bc0000030000010600002dfdccef86d3f10002000002010302002bdcc0c29ffba001000000030301020007d6aeddaab09808,
  0x90000010006a2d8aedcbddc9a00000003010600000008d3d697e1988cf100000005010004000001c18affeddfc9c400000007000000020101ff90ba93d5c8e000000203010002020001ddd2a99fc6f69300000300010303000006b2dcd08a9ff89e00030000010006000001e0ea95f4c081f002010000000007000026aaf0a2ce94b008,
  0x1080001000002cdb78cf8dbe5ba0000000700000200013a8cc5a1e090a000000201010600000001cf97ca98d5facc00000203010102010002c1c3af97e1e2e10001000301030200000185af9cb99f88c3000101020005000100658ed681f5838f0002010000050200002ec1a5abe0e99702000001000501010013bc9cce97b89008,
  0x6010102000001e2d3e6e6edb2dc00000100080100000002c3d8fed1d089b200000203010300010001c4d2f9b7ab9ef70000020500000102000cb7f3a2f7e6fb00010005000201010056c1c0c7a3b98300010201010302000002bcd4a8849bf4dd01000200000700000026d0a8d3c8d89001020102000001010213bc9cce97b89008,
  0x6010300000004ecfba2869faecd00000302010301000012fcd8fcd3abc5c600010000090000000009b487f6b7fae8f400010006010000020004acf2ab888b8ca800010106000000000236f48c8aebd0cd00020200010302000003ccb182c2b58bfd0100000501000300000389d2e7c3bf9ab802030100000000000402bfb9d5cf9fcf08,
  0x20403010000002da2b4ab86cacc00000304010101000001c1daccc5f28dd200000700000101000103eb97aed5988c00020102020300000079f7d2bbe19dad00020203010000020013ed8cea869bda0002030002010200000a99fcb6bdbcb90101000008000000003cf9d8cd83b8a0020003000201000200028193b789e1f608,
  0x901000000005b82a1bbced49fb5000007000001020000368ecde7faaf918e000202010302000000019cb7eefcf1e2dfa50100050101000002000ba6e78bbea8f5900101010007000000001de78cfbf8c8c4aa01020301010000000272b59baddfa8ce03010000000600000004ddafcbbcbb9dac04010000000005000003aeffd1a48df0e408,
  0x1090000000000089298eafa87cec200000601010200000003eab8fcaca1f3d700000701000100010001b9d0b6ff9d84e00000080000010000010d98eda985c1f40002020105000000000cac8ccfc8cec6a100030301000102000002ddd1e9aafeb9ba01040000000500000002c0c6e8f382e0fc02000301010201000003bba5f2cae496bc08,
  0x70100020000000197c88ab1e2a7a100000800010000010028ab9ee39ba5c000000801000000000102c8e5a3f3c6a80002030104000000000591aabbd4b9d38c00050100000400000057e193dcf2ffc80006000100000300001488f9abf4ebfb01000009000000000002dda9a4fcece9b901020301000201000001d8f6c3ed80c4ef08,
  0x9000001000000358dac8b81e787a4000501000400000000269d8cea82e5dfcc00070000010002000006ebe09baddadcc800070000010100010001c9f6dfbeeaa0a001020007000000000039d2d8c8e5cea2b904000001050000000009dfd1c2ac928c8a040300000100000002058beb8e89d99e05000001000400000003a4c2f9ef8494c708,
  0x90100000000000282dcf290b2d69500050102020000000001b2bed3b3e3b3d60103000600000000000190ade7a59ddfc001050002000200000075bde2a2be949802040001020001000029e8b6c0abe8e802050100000000020002909490a4f8a8030301000200000001189be9caf0d60400010104000000006085fab9f2b0d708,
  0x6010102000000003781fad0d69bdc00080001000000000102fbceaec5c60100080100000000004eea81ffde85d401040005000000000036aae3cca0ea9b02040101000200000015bc8096a3cdd802050100000002000003abfbeaa582d4030500000000000200268b82c89ee80500000104000000000fc98d91ebbfdb08,
  0x70002010000000038bbd4d1df92e200080000010100000031dcfdcac3b698000801000000000100429add9faea80101080000000000000187ffe48ce9e9e2010701000000000001029deda6f38b0203010400000000002e838ddbcc8cb50302010301000000007c949995b7d28803030102000001000006dae29ba9cdb408,
  0x80101000000000069f0a09cb388e00301060000000000005ff3bc94d09be605010004000000000026b1ddfce1db9006010000030000000015afe9ffac82c107000001000200000004f9cafbead2d80701000000000200003de6ada788e207010000000100010006ed86f7c0c807010000010000000115a2e5e1e708,
  0x9010000000000006ee591e2e7b4c50401050000000000002b96a1f1f0cb9705010202000000000069e7e581cdbeac0501030001000000002aa0edacdfa0b006020001000001000036fe9ba8e1e006020100000000010002c0cab1c7c007010000000200000002d8f4e5c5c2a008000001000000000106b1dbb68808,
  0x2070100000000000037c29ff68cabea0501040000000000001db280d398c5c0060101020000000000198c9d838dfb8207010000020000000003c9eaafb4d5fd08000000010100000067aaef81edd808000001000001000006c6a9a589d40800010000000001001eaea7bae80801000000000000013dca8bc308,
  0x1090001c5fc9d91cce58789000000000000000501044990b3a7c3b7bffb0000000000000202010501c18e9fa998feeed4000000000001000301054fcff8c8e2d597b00000000002000000010705ceedd9978696a8000000010001000001070185badb8ba6b4e00000010000000001020607fbb3bfd0fee00001000000000100000823be92e9a6b80100000000000001000846a2edd2d809,
  0x6010355aaddd1fbdbd7ea0000000000000101080001bef78ad299a6c590000000000000020301047b91ddd6a7cef7af000000000002000201053cc7ede8f395c4c50000000001000201000614b9c1abdddfb08a000000020000000001070193a791fcfbb2ae0000010000000101010615a8c9afa5c8cc000100000000010100077395b0fac2d3010000000000010001070294c4aaf7bb09,
  0x8010101efbed184d8b2bed7000000000000040103024a99998782b4fcf10000000000010200070058a6f5b0b6a4a3b00000000000010301020301eedb8be0b8c5cf800000000001010000080063a2f2d0c69bc9ca000000010000020103030fb4e1a4bbffcdbc0000010000000001080001c4f1f4ee98c18c000100000000000107010bbb9e84d4dbbb0100000000000000080125fbc295a4bb09,
  0x108000102de8eadbbc7afa4a30000000000000500040101c2e0c6e9cc92f39500000000000201010600449d86ad90d7b2ec0000000000020201030202ccd7fe98a88587c40000000002000001070070d59cd19e8debd0000000010001010104022899ccf5f6a7e5c00000020000000002010502a788f5c0ee98e00002000000000001010613dee5cde6f5f8010000000000000108000196a1d7e0eeb009,
  0x700020114e5cdf6f883e8c79d000000000004000105001094a7c791ab83d1b40000000000050001010302a2a0bfa8f0fce2b5000000000100000900001292b7e6e4aab4ceba0000000004000100000501fdfec194f290fc8f0000000300000001030301fbba9485fc85d9d1000002000000000107003899df9fb5ca81aa0001000100000001070009d2dfd0edbfaaa1010000000001020102032f8cacf3b48b9509,
  0x901000003e5dae0dcca96e7c40000000000070000010201caaef1bdf3a6c4d00000000002020103020007b9898adcdcde8fc70000000100030103020001e3be96feffc1e48b0000000300010102000305f7c2cddcebf2d50000000400000100020333bcffcff583e8b1000001010000000800007b91f7fb91f1ded8000100020000010300030ed1ac94b3fb94960100000101000103000362fab3f3e9aea609,
  0x10900000004e9e18bbcf7ae83bf0000000000070001010103fbe9a9f799ef90bb0000000004000103020047cad795d5d08c850000000101020006000002d6f58ab0fcc69eab0000000103000102030004aacef7c8ffc1c2d1000001000200000700000186cdaebde8a5be98000003000001000006000dd3b5ca89ebe5fb000101000000000800001ac692ecc1e8c2f30100000000030102030001c6b1a7ebdea9ff09,
  0x90000010036dbf384f09cbbf5af000000000501000400002cd0d9eda69ff5e0fe000000000601000003001485efc786d9a6c8cb00000000070000010002078dd6f4ce889980c80000000200010700000007b3a68985eec8baa0000000040000010500001ce0bde4a5b7ecc9f00000010100000800000037b5fd9baea594e9800002000001010301010104eb86b2fef4938390010000000001080000006084dff6dabcb0a009,
  0x1090000000002cba0a598daa9e6d500000000050104000000248fb3addc87bab700000002030103000100048ae6c4cbafb6cd980000000302010300000145b699e189e291980000000400010302000058bc9a82f1c4ef980000010103010103000002c5bb95ecabb3afc80000020002010302000001c48d8efca9ce98cc00020001000103030000448ad995c6d385c0010100000000080000000dfac1d1edebf3d809,
  0x8000001010002a98ae3fedf99a0a7000000000800010000015185d3b1f9cab5e8000000030201030100000bddaf9a87a4fda9f10000000303010101010007929d87fe90c7b5b70000010000090000000008b1bdfae9a9bf9bfd0000020003010202000005b5869ba290e8a7a40001010002000600000002dceab5e7c793b29c000200000201030200000196c4dbd58b80cfb50200010001020101000221849cd98dfbb9d709,
  0x20501020000001985cdaac9f1aca0fd0000000700000101000166d5e3c8ed90ffb1000002000501000200000482e8c585d2f18d800000020300010301000008ff85edd4c8d7cd840000020301010101010007f1feb5dbc6b38be500010003020101020000029cf2d9b9efb08f88000101000008000000000c819ee9e7c3a298a2010000050000000400002fd9b0d094d4c790030100000000000600003ca79a94c791e1af09,
  0x9010000000013ceafd8d5edc2aae80000000700000200010034bc8890b5b490b600000008000000000101688cb49d98ca8eeb000001030006000000000289e5bcdca9a0ade50000020301020002000014e297f3c898c6e3e3000003010102030000001298f58bfde2fd8cec000100030103020000001ebb9cdfc7bcb1f5830100010301020000020003e1c78aa8c49bfbbd02000002010102020000128ecaf38aa7fd8309,
  0x601030000000001aaed988791aed3bb0000030301000300000001a0ede486eefd93f60000040001050000000021adc3a6a3e7c280000006000100000300001edba588a896cd91000007000000000200010289f9baf08e9dad000100000900000000007ee49aede2b8ffde000203000102000101001ae4cae997beaea5000302000100020200000f99a0e08cf2f4d10102000000070000000034e0c1ebd4dbabbd09,
  0x901000000000004e9e18bbcf7ae83bf0000060002010100000002bbce9f9ce8eed2b50000070000020001000001bcbaacbebde5cd81000203010004000000002ca3ec81c1f8c08f0003020100030100000004abafcff0d1b0cbd40003020103000000000101c6b1a7ebdea9ff000303010001010001001ac692ecc1e8c2f3000400000500000100000dd3b5ca89ebe5fb0101010007000000000003fbe9a9f799ef90bb09,
  0x109000000000000559bb99486d1b9ffab000007000101010000003a9ccef1f9a2d297b4000008000000010100001481a8a5ce8dd7b1c0000301010401000000007ef0a0aefad58d8eb800030301020000000001108aa59e82dca9b00200010106000000000008f4e9a0adc8b19c970202010000050000000018fa98d4fcc398dea40300010103000200000009fec7d49985deada60302000102000000020001989ae4ede99ab89809,
  0x3040101010000000015fa9192b6c8a395ee00070000010002000000018cfffefcd38f97d9000800000000010000012c9db497e59db4010105000300000000000fd6b682e1ef92d5b4010200070000000000001086e794c683f8bee50107000000000000020004c3e5d5e9fa8fb20203000201020000000001a2c392b5c0cace950300040100000200000001d9ca97ece3fd81b5050200000000000300002397f4b2eb80d9f009,
  0x6010102000000000004b2dcccd7f8a9f9d80006010200010000000002c094b0f1d49ebeb6000701000002000000002c90a3bab4b9ebee0100080100000000000004f7cad986ee91a5e5010602000000000000010290ad8787c8870107000001000000010047c7d0aa858bc30205000101000001000008add0a9fb8fb9dc040000050100000000000387e8a2c7a69eeafb0401030000000200000024b799daef9c87fe09,
  0x6020101000000000018e582c4cda7a2fe000701010001000000001286ac8ed2caeabc010108000000000000001fb1c0df93e19ad7010502000200000000001aadf7e6c6f2d6ef02060001000000000100028ae2c6d59ca20206010000000000000106f3c69b92a20400010500000000000023bfd4abddd080e40600010100000200000001b3abe0b3fffbb40700000100000002000011f38acfeafaa409,
  0x8010100000000000002fdedf3e1c7f99e9c0301060000000000000002a5e6f7b7b4b2baff0501010201000000000001f29fb7a3ccd692940600010200010000000028f382d7bbbee0940601000200000100000004858a94ad978cda060101010000000100002ad192decb91980601020000000000010001e6aae1f585a60602010000000000000104a988d5eef607010000000002000000248999e3ab9eaf09,
  0x9010000000000000001c5ebc5e69bb0a0bd0401050000000000000048deada5af998c970501020200000000000001c0cbc1fbd3abd4a40501030001000000000050d5b3a3edfbcc90060200010000010000000185badb8ba6b4e00602010000000001000007fbb3bfd0fee00701000000020000000005ceedd9978696a80800000100000000010023be92e9a6b80800010000000000000146a2edd2d809,
  0x109002dabec9b9cf3d0a79f0000000000000000050104309ecfe3aa9196cee0000000000000000300020520d68ff6dedbd38d8000000000000002000101060acd9496c9ffdae0e9000000000002000000010701c9a4d2deb280e6fa000000000100000001030529bba9bf88eeb6e2000000010000000100010702f6eaf295cac9a8000001000000000001010711afdee8f4c4bd00010000000000000100083d89e5e68efe010000000000000000010860cff6e1d90a,
  0x6010302dcece2c482acb2b6d3000000000000000101080002cb92898b92d0c3dad30000000000000004000105019ee1d4e5889399f88100000000000003000001065487ae8eca9fa7daa200000000000100000008012da6ecd9f6b4f0e38c000000000200000000010702e98586ca98d08c8700000001000001000100073dd3f19397e0a3d8000001000000000002010603ba9bede1f0fdcb00010000000000010001070ed7c8bbe7fb8201000000000000010000081c8af8ae90ff0a,
  0x8010103d9dfa4ebf0f1ad86e50000000000000004010302018888ba88d3bcdfa2ab0000000000000102000700019c93c79becf1cf8f8e000000000000010301020303f889b1c8b48fbedd8c000000000001010000080001d793d3f7e3bfdfdabc000000000100000201030324dcc5cb98b7ee93a6000000010000000001080004a69394bd82e5bab800000100000000000107012aa0d9d5d3a6a087000100000000000000080101f696f78682b6ca01000000000000000105030585b3e4e9ebeb0a,
  0x901005ff194a9e79a98fd80000000000000000600010367ffffb7d6a2a9b4cc00000000000002010106000183b8a9a0bbd7b48ee300000000000002010400031ca2f9e9a6f5e3f6ec000000000002000004010324b7fbfaa9afff9dab000000000101000000080011dab0b9bd83ad90c6000000010000010000080002afe4978786c5daf800000100000000010008001adcaf88a9bbbbc7000100000000000102030301b2a59c8086fb9a01000000000000000401040497a880d1899b0a,
  0x109000014dbccaefc979bc48e9400000000000000060101020edeb485c58881ebb5eb00000000000003010006001492fd8dc2e4d4d0cf82000000000000050000010401d8e4ca8cce9ac0a39400000000000200020103020baaaa9585e38f91a8d400000000020001000103030290bcd8d1cee4cfd9fa000000010100000101030361cd92b0abc0d9d7d0000002000000000001030404eed78bf6e9e7a78d000200000000000100000724e499c69ae2ffce010000000000000100080001faa7cca8fac8f20a,
  0x700020101988baea8bab7938a8ad000000000000004000105000183fc91868d8b849ba981000000000000050100000408aebee2dcc8ea81cdde0000000000010000090000018785f8e3f3d182a99c95000000000004000100000510e6ddfacf92ccc2f7a4000000000300000001030310f5fd92ebc28ce6a59c000000030000000001000602f2968fed9ce5add59800000100000200000103037cb29ed6e488a5ca91000100000100000101030308a0f1ccc0a2c4cf9601000000000100000008001fc8f0bfe18ed7bd0a,
  0x90000010e95bfa3ad82ebe18eeb000000000000030204010034a58cc5defacdbc99e500000000000103030001020dd796d5f7edd2ffa5ec0000000000020002050100128ec890bb948ef995e100000000010300000006000ddaa7d6e492e7cafc8600000000020001010302010796b4dcd1cbb791e0ed000000030000000000060101fcffb9ff81d7bad1800000030000000001000006208cdbffaffe97f5e0000101000000000100070008d3c0b3dbd7e7d6a0010001000000000001070028fb98dac4d3a1f00a,
  0x901000027fcf890f3fff89cd5ca000000000001040101030042e1daaa96e48dda9de100000000000500010001030beefba9faafd3d880bc00000000010101000700001bc1b1e5eee485f6b7f20000000002000300020102069beb9dbdb2f48985de000000000201000103030009fda0e8c4dc82f7e100000001010000000800000ba38fdad998bbe0c7a4000002010100000000000677d7f8839fe6d8f49c000100000000020103030015dd8ae2df8eb7e6d0010000000000000108000071cbfd97adbdb4d80a,
  0x10900000014ac90ea9abcffefa39200000000000007000101010bebeec089eecf9584c5000000000002020203010059a7acf9d0b396d687f4000000000200010303000101c590c993bbe3cddeb2000000000200020201030014b0948dcfcba5f9b5f4000000000500000000010404c6b7c88bd8bfe7f68c00000002000001020301010791d2ba83f59aeaeadb000001010000000008000002f29e88babcf0f8a19a000100000100000008000024fbb085eba49bd5fc010000000000010107000001d4c8eb8ed3b7e4920a,
  0x8000001010ebdb7d18decf1d18ac200000000000203010400007df59fa192e0affe99ab000000000003030100030037a6bbd2e3b38cf6cebe00000000010000090000004b82b4e79c9b9c84eca800000000020102000302002e83cff0c8d2afadd29c00000002000002010302000390cbadb3a2e9ffc1a4000000020100010201010217dc9689c1f7edefa484000002000000010104020004fae3989de2a6d6ceb5000200000002000100020345bd958fade4b29e9e030000000000000001010502a481ebbed1cffd960a,
  0x9000001000d83e2bdf4bdd9889282000000000005000301010018b6ce86e6e981e9c0000000000103010203000014c89493ebdcb4a6a9d2000000000105000002020001d19cadadc8fcaade8e00000000020201030002000b958dc69fd180cfa1f500000001010101030300000cc3b9dab8a98bc199f2000000020002010300000203a7dd9beb83a1dbc59f0000010000010008000000049be49fb5b9dce89aa6000100000000010800000046b9aaa0a1a2bb99e401000000000201030102000491cbb5f491d5c7ce0a,
  0x3050100010015a986faae92ac82d593000000000202020103000020f3f581fdc7f99895d6000000010003020103000002d3c9a7adbf8dabc795000000010101000700000011d982c3f8eeefcdbd91000000020000050002010001c6ffc99bdc8abdf7b600000002000301010003000187d6ddf290f2e6b6d0000000020100040100000203828af4cb97bd99bebf000002000001030100030003e584cca58be9dca4f3000200000000030102020044f4e1c98efc91a7c2020000000000020103020004b3f9d2f8e380d7f70a,
  0x7000101010002c5ebecbc88f2b7d7f5d6000000000301020300010024a3acc4b989eaa5848500000000030201010300000686bcdb97ac9693fdc789000000010001050300000007e6fbb2fcdab7f798dbd7000000010301000300020001acafaef4a9b896c29cc200000200000104000102003fb4cdeeecfca0c1c0ce00000500000000000001041c928886e7bf8ad497c6000101000000000800000026928efbf8c096fac0cc000200000100040000010204c3f8d3e39fad9db28c020000010000020101010201d1f7c69cc692bcfc970a,
  0x8000001010001f392fcc2c7fea4eec791000000000302010301000003908ddebb8088c2e8ee9c0000000100000900000000028e8cc4e2dadebdf098cb00000002020001030200006abfb2b5e7d599bbc5e0000001000500000100020105dac9ce9cecabc0c5dc00000101020001020300005f9cf1d3c3988be186c1000001020000000700000052ebfbe4d19fe6e6f49a0001010004000000000202128e8eee95a9ac85bbd2000201000200000000050008cb90a1aabddf8ae9a7020000000300000100020201aaadad88f9c3e486f80a,
  0x9000001000018d2a4f1b9af8faaa9b600000000030106000000002187e588f0afb99dd2eb00000000070000010002000a8baff6b3bcb1a0a2c800000000070100000000020191cfe0b598c1bc81dc0000000203010002020000129a9498a4f796f1f49100000003000103030000001ab8e1f991c29282bcda000002010000050002000002829ebac2b6c481f3900000030000010006000000068ddecb83f792ffc3b8000102000001010302000007dbe39bb9d4e0e28990010002000000000700000057cc96fb9b8a83eef80a,
  0x901000000002cbce7b4ead8b5c68fef000000000401050000000033d7eb8a8ce6aef98fa1000000000800000000010102e4ebe0c0afc3a9eb9800000003010102030000004785d4d389b781f8cb8800000004000103000200000786fec8dddb96bb80f4000002000301000202000024cc8fd2e8f3dc9dc8f4000002010300010001020007def4d6b691e295ffa8000101000000080000000002b5ecefe2fdfbc0e180000200000301000102010008c1e8affa8790e1e4e8010000020100030102000001ef97dedfbad38d9bd80a,
  0x109000000000066bfa4c688f7ea94cd8d000000000800000001010015f0c5a29cbbe9b0c984000000020301020200000010adeb87b99f93ab978900000002030103000100000199c7ccbc99def08e839c00000003020103000001000faef6eefaf29bb4d8e6000002020100000500000059c9a99beeb3bfa2a5ce00010002030001020000010396bdafb3c3edf99bf400010100010007000000002bbbb8d69fad97bce7d8010100000000080000000004f989ebd6bcd4a6edf402000200010002000001021b8b91e0fcbccddfd60a,
  0x60103000000000282df85d2b9bb86b9a30000000303010003000000029cd2fce28b908089ca000000040001050000000058a3d4c18792d4c4f4000000070000000001020029949192b3c4848b86000001000009000000000001fdfdd298ac88be9ce9000002000301030001000001ddbca493f285e8caaa00010003010102000200004dc4e2bccfa6d7cc810001010200010203000000018685b0a6e9d18dcfe6000101030101010000000203d396a59190b5bfa5010001010000070000000018a2d088eee09faafa0a,
  0x900000100000067e8e2bbfdbbe2ecd0d900000004010302000000006296d3ce92a7f291e2e0000001050000020200000050dbabafebc7c68be0c4000002030102000002000002a4aaf8d3faa098e4e500000300010303000000002df9e5eaa584bfabe092000101000008000000000043cbf2becf9b9393ccc9000102010101030001000034c6dcba90aba988e88a000103020100000001020006d6e2d495f5cf92b6d2020002000101000202000007f7dce5f4fbe8ba8ee8020101010002000100000240bde4d598af88acff0a,
  0x90100000000000e9b95bacbd3eab8f7ea00000103020202000000002682bfecedd68bb9b18d00000302010101020000000fb9bdfa96c7f3abb48000010003020201010000001387d5adf598f2e9f6800001020100030300000000058b91d3ca86b6a195e2000103010003000002000006c199c0c499d295edf000020201010200000002003fc2b3a9ddcdcfdd87010100000008000000000004dab190d1a3ed9ae2ff01010100050000000002003cd6e2e1d6e9c6db81020201000200000000010208f8be86b8af908eb00a,
  0x1000801000000000029d7d1fadbebf7e5c49600000105000202000000003fbed68b93a4a8ecf7c6000007000000000100020079f5fbb2cbdbcfeda600020002010302000000000587eea9fd91bc999fe9000202000103000200000017b1d3b39cbd80fef9f5000203000101010002000004afb9e4bf8ab0aba586010003000102020100000005e6e5f5c3808ad6a9e8010003020100000102000002aad898d1a88adab9e3010100010007000000000002bcef85f6d59ded8f9a010203000100000100000207e5e188f39bbca5b50a,
  0x6010300000000001f868ec1ec96b79384c000000008000100000100000beaf085cbd7d787c5d6000000080100000000010001c5dad9d6b48a80fe8400000401010202000000003efc92c188e0cfc8cfd50001000009000000000000248a80dde0ecfbeefa820002000301020200000000118bd5fdb89c978aa5f90002020101020002000000129fc99ca9a7f0af95f401020000000700000000000197e4b4f29c978ae2d4020000030102000200000008cfcdaed28ab692b1e4050001000001000000000303efb68581a5969dea0a,
  0x20403010000000000108497cf99e3df8bdbc200000700000101000100003a8f85d5bbd6d28e9e000008000000000001010012feb7889686e280a8000102000700000000000002d3fda78ef5d0cca9ae000107000000000001000177dacbeedfbcceac00020102020300000000000bc795e5dbb8d89ce9dc000201030200020000000004be95acdfe6e1f4adc6000203020001000200000003d5cfa6c1a7b692a8f0010003020101020000000008a9acb3b6dbeab590f701020300010100000200002fdc8793bed7decd950a,
  0x90100000000000001b2f7bccceeb585c486db000007000001020000000050e3ffaacca3bcb7e2e6000007010000000200000029d09ef0c5cc80d79fd0000202010302000000000002ffd4b8dd9de8aed99d9701000601000000000200000781d8d791a593cbf5aa010101000700000000000027a9c9e3c3cddbaef6d003010000000600000000000381a1b3e1afef9fd8ca030200010200000000020059cffbc180cf85dcdc040100000000050000000020c5dfb9c891f7e0a4cc060100000000000000000302d7cdb49496d393ec0a,
  0x105000202000000000011aa85a3c1badda9ece2000203010300010000000014ff92a4c080b79cebba00020303010000000100005faa8dcdfb9a8aae81000302010300000100000004f1ad94eab4e3a6f8b300050000010400000000000290e9a9f4dfcb95a2cc00070000000000020100005e94b4d2c4919b8800070000000100010000012dcb8fdb87a6fb85000700000100000000020004ae85f9dad5809ffb010000080001000000000012bef4c29ba3b2df83cb020100000700000000000001c2b399fad7b1fba5910a]

/-- The triples `(n, b, a)` of part 15. -/
def enumC15 : List (ℕ × ℕ × ℕ) := [(10, 60, 23), (10, 60, 29), (10, 60, 31), (10, 60, 37), (10, 60, 41), (10, 60, 43), (10, 60, 47), (10, 60, 49), (10, 60, 53), (10, 70, 9), (10, 70, 11), (10, 70, 13), (10, 70, 17), (10, 70, 19), (10, 70, 23), (10, 70, 27), (10, 70, 29), (10, 70, 31), (10, 70, 33), (10, 70, 37), (10, 70, 39), (10, 70, 41), (10, 70, 43), (10, 70, 47), (10, 70, 51), (10, 70, 53), (10, 70, 57), (10, 70, 59), (10, 70, 61), (10, 80, 9), (10, 80, 11), (10, 80, 13), (10, 80, 17), (10, 80, 19), (10, 80, 21), (10, 80, 23), (10, 80, 27), (10, 80, 29), (10, 80, 31), (10, 80, 33), (10, 80, 37), (10, 80, 39), (10, 80, 41), (10, 80, 43), (10, 80, 47), (10, 80, 49), (10, 80, 51), (10, 80, 53), (10, 80, 57), (10, 80, 59), (10, 80, 61), (10, 80, 63), (10, 80, 67), (10, 80, 69), (10, 80, 71), (10, 90, 11), (10, 90, 13), (10, 90, 17), (10, 90, 19), (10, 90, 23), (10, 90, 29), (10, 90, 31), (10, 90, 37), (10, 90, 41), (10, 90, 43), (10, 90, 47), (10, 90, 49), (10, 90, 53), (10, 90, 59), (10, 90, 61), (10, 90, 67), (10, 90, 71), (10, 90, 73), (10, 90, 77), (10, 90, 79), (10, 100, 11), (10, 100, 13), (10, 100, 17), (10, 100, 19), (10, 100, 21), (10, 100, 23), (10, 100, 27), (10, 100, 29), (10, 100, 31), (10, 100, 33), (10, 100, 37), (10, 100, 39), (10, 100, 41), (10, 100, 43), (10, 100, 47), (10, 100, 49), (10, 100, 51), (10, 100, 53), (10, 100, 57), (10, 100, 59), (10, 100, 61), (10, 100, 63), (10, 100, 67), (10, 100, 69), (10, 100, 71)]

theorem certs_ok15 : checkAll enumC15 certData15 = true := by decide +kernel

/-- Certificate data, part 16. -/
def certData16 : List ℕ := [
  0x8010000000001000009b38bd6d3fdbdfaa20001050004000000000000038efbfeade9d6e2f082000303010101010000000002c0d1c3dc8ac9f9eed4000303010200000100000043b0d99db6d2aec0da00050100000400000000000180b689cc999dd0f2ab010000090000000000000002d993b8f8edb7dfac92020003010202000000000066fdc8b9ce83e8b2c403000001060000000000000eb882f4bbcfe08dda040103000000000000000201ea898d97d1b79d050200000000000100020031b8cbb9e7acd0b60a,
  0x900000100000000001bc4fef9febcbdbfe18b0005000400000100000000019feedb94cec9bc898c000501000400000000000022c3ba888fdad7b9c4b4000601000003000000000007a3e3c5c3b6f8b2dfdb00070100000000020000000186cdeebefeead6b6a0000800000001000000000107d3cdd993d581e8020001070000000000000023b9af8a9fd8bd9fced4020301020000020000000005c4d995caf4d4cbcce205020000000100000200000f89fbfb80bf88b7c4070000000001000000020001808de2be8bf8e6d80a,
  0x901000000000000000a808ed8acc6b5acf9e4000700000102000000000004e7a5a48a9ac4bdd3980007000002000100000000018ea6e5c5d6bea7dcf6000800000000010100000029b48fc6f7a78af2e001030006000000000000000990baa7afa0b3d78ac103010400000002000000002cb8e3a8c1e8cff1f1040100000500000000000004cfc9e0fbbe85e790e40502000100000000020000028895b7be868ce5f606010100000000000002000fcdb5c0d8f7c9c40701000000000000000002358ca3cad0a6de0a,
  0x109000000000000000068a38991aca085aaee00070100000200000000002da5949787f1d5e5ce000800000100000100000002afe4978786c5daf8000801000000000000010001b2a59c8086fb9a010302040000000000000036e4c89398a9e199b4010700000000020000000008ed989cdec1d6c8a301070100000000000000010497a880d1899b0203010202000000000000019fdba389e2cd9885cf030100060000000000000028e9c2bcf8f2dbedaa03030102000000000100001adcaf88a9bbbbc70a,
  0x7000201000000000000019c93c79becf1cf8f8e000800000101000000000001d793d3f7e3bfdfdabc000801000000000100000004a69394bd82e5bab8010108000000000000000003d9dfa4ebf0f1ad86e501070100000000000100002aa0d9d5d3a6a087010800000000000000010001f696f78682b6ca0203010400000000000000018888ba88d3bcdfa2ab030201030100000000000003f889b1c8b48fbedd8c030301020000010000000024dcc5cb98b7ee93a603050100000000000000010585b3e4e9ebeb0a,
  0x801010000000000000002cbc6f3bb86b7e2e7d501080000000100000000002ce998e8e39d90bfb4030106000000000000000002dcefafdef5b5e6faba0501000400000000000000019ed4bdeefda8ac93c10601000003000000000000549ae1ab81b1a291d106020100000000000001000ed7c8bbe7fb82070100000000020000000002e98586ca98d08c8707010000000100010000003dd3f19397e0a3d8070100000100000001000003ba9bede1f0fdcb08000001000000000000011c8af8ae90ff0a,
  0x90100000000000000006b97be86c8d9c1b0af04010500000000000000004ffdb9f6c5b08cbbcf060001030000000000000041ac9fedbdb7a69a800601010002000000000000159aa8ad93ffb5c1d2060102000000010000000052f6d2fe91dcedc407010000000200000000000392c9a5bce481cdf4070100010000000100000005edd5e4ab9592d0070101000000000001000022dfbdd1e988fa08000100000000000001007a93cbcc9dfc080100000000000000000101c19fedc3b20a,
  0x601030c899b94d386b298a9c8b10000000000000000010108000babbafbcacabebbbbdabe00000000000000000400010505cba08792c9e3b0c39aaf0000000000000003000001060380b0c4a5b1edff82dab000000000000001000000080101d8f192f8c9d0f293b5b40000000000020000000001070ec4a49ec1d1a5fffdd200000000010000010001000702e495a1f789dca5d9bc00000001000000000002010617eef9d99192dca1860000010000000000010001070188bcedfec8c4abda00010000000000000100000803d49eb2d18fa5aa01000000000000000001000805da9cb9afb9e60b,
  0x8010132d4f8af80aa97e7a1f3e70000000000000000050002032da8f184d1c8c9e9d8c2c00000000000000002000107000ec9a3b0e5f8f3bb8fbec400000000000000040000010508b29bc7a2d9c3928bdc9b00000000000001010000080015c8edc1c8faadb8f1eec400000000000100000100080003f8d6af91c59690e0f0ac00000000010000000001080041f2c0eab2f1f4c0c6d80000000200000000000001070381b9aa8381e1f187ae0000010000000000000008012efcb7cb93839b8ac400010000000001000000020601dbe7cdcfb688fcc401000000000100000000000803d3c6cde2bf9afc0b,
  0x9010002cdcdbfa48e82a6d0b5930000000000000000040105003fb8c2b4d198ae80befb00000000000000000600010301b79aebc19482b592dc8800000000000000020201030203ddc1fb87a4c785feb9e0000000000000020000010700018ceec4a1f091a98ca6f40000000000020000000007011db4cefab4f9e2cd8f9400000000010000010000080008e2f195ec83aef29db80000000200000000000101063ab890c5e2e4fdf4a60000010000000000000108000894a497f0d7919fb40001000100000000000001072bcddfe6cdac85c401000001000000000000000869f9a09085e9ac0b,
  0x109000011c3b1e7efbab3aefacde00000000000000000060101020ed9f0a1e4baf989ffc2e100000000000000040001030209f9858dede2baccb8f3a50000000000000101020006000af6ddf396d6bb8bc5dfce00000000000001030001020303f7b596bad897e2a99f9c00000000000101000100070004efdcbd92a2c29c938aec000000000100010000010700698fcb838a90f4f6a2f40000000100000100000008000cb3babc869da98fb2920000010000000001010103037cedcb98f89ec7d7ae00010000000000000100080005f297fca4ded1cfbe0100000000000000000108001096deebdebbe6d20b,
  0x700020102ebcbbaef82a9b0bb938d8100000000000000040001050001d7cdf9a4df99f9f581e1d6000000000000000500010103398ddc8cbbb39e99f4c3e400000000000001000009000002d1e296f7b091d1b1f780e600000000000002020100020358eed6f187b59c94dcfca9000000000002000100000700439297fcf1c0f688d6be8a00000000030000000001000608ca84d7e4dff7fdd5ffb000000002000100000000010601d9dbb4dbd9d2a2ecd1c400000100000100000101030326afbfdd949ba09197d80001000000000100000008000283d88ed1b395dad3f8010000000000000100000800069eeff39f98aa95e80b,
  0x90000010bc1f6d597d086bedcb78f0000000000000003010600000dd88be1e6ccd7c5acf6fd0000000000000006000003010784a8b6a7f4a0f4a8cfc90000000000000300010303000dbb9ca9c0bee382a8baf400000000000200010103020105b59acad8efd8c8acb9c700000000020100000000070001c3b0b0eb8be8db96b1ca0000000100000000010800000dce9bc895a686a3e68900000001000200000000070031f985a4d8fabcb291b100000200000000000002050103b988dca1dea5c5b7870002000000000000000301041cd98b9fbfc0b883a301000000000100000100070001d99fd384deb0bac20b,
  0x50200030001b48af4f78bd894bcf2a70000000000000007000001020188c9e5f4e9ffcde9f1e70000000000000100080000010ab6b5dc8fdea19be8cdf40000000000000201010600000986d2a2819ecbb7a09bb400000000000005000000040102baa2d1c5cbc386a3e6b00000000000010003010302000ecdfdf5fce398dfc3dbdc00000000010000030102030003de9bbb88b7959d95eac400000001000000040000050054effc8efaf8998ef2a40000010000000002010303000a9bd9abefbedf90c3a60001000100000001000007005dd1ceff91919ef29601000000000000010104030003868dac9bffc78e9a0b,
  0x10900000007b2f1f3c0ab9094dec4b600000000000000070001010106d8ce8d9fe2f88feb9bae00000000000003010006000002809f9a9dccb8b5edc5d600000000000103000102030008cafdbbfbb9e6c5bce5dc0000000000020002010302001694cf89f4e394fbd9830000000000020200010300023aa3f8f3c89aaaf3a7c300000000010100010007000002f1e995d6f3ba92f2fe840000000101000000000800005aa2deff85808ad4c1840000010000010000000800000be7b0ce97f0acccf8ec00010000000001010103030076ced5ed919f85dbbc010000000000000100080000049dced085e2cf80f40b,
  0x900000100238bbeceab82a49bcbada8000000000001030102030000509fb1bf818c9683a89eeb0000000000050000010004007398c3f2d1e0af98e2ca00000000000600000000010304eebbb5b0f9d6f89bc79c00000000010003010300020012a8a0af9394b69de1b2a5000000000101000008000000139fa69a81f089d28dadd900000000020200000103020008acd0b3a2cd89b981d0c900000003000000000301020104c5d1d6ff89b9c6db84b400000100000000010800000002a9acd8b4e9f5b2dae1d80002000100000000010006000f898d9fe4b3dbbc818c01000000000000000801000001b1e3a0b5c8c1bfb2a80b,
  0x90100000001abb2b287bedcc598f8a3c300000000000007000001020058b1a7a1e4ddfc9a8687ba0000000000020300030101006fac9bd1c399c59ac580f100000000010201000303000001e3968daa93d4a6c4b4f7aa0000000002000201030100011395e3d1d684ecdc82c4a90000000100000200070000000197b1a6c3ddbffc82a39c00000001020000010301020002de97f4dd8df49483e4e400000002000001020300010123a0b7f98290d4a185fcd10000010000010000080000000dd0a3d8fbfcf5f5e6b9f600010000000001000800000001bfd08084fbd984a4edbe01000000000000010800000009c8ea9a92a783befcba0b,
  0x8000000010110f192affcd99aaaa6f0b60000000000020203010200000384a6e3bab98ffff2fcf5d60000000000020203020001004be1bfb2b2c5daeaccb9ae000000000100030203010000018de0e893edaac988fb90a600000000020003020001020035add0af85c4bd8295c88800000000020100000700000059b6e6e192cd969e9fa5ac00000001020000040100000262acad8acaadff87cfd60000000200000103020002003fe2edab8ba1a0d2a7cab40000020000000005010000020cdac4dbc3f2df8efcc4d90001000001000006000000020382ccb7f1dbbacca3c4d20200000000000201010002020ab8c4d0c884c4ab8fb70b,
  0x800000101000eacfbbef6acc187d0abcc890000000000030201030100000c89d693d9c1d8c69bb4ae8f000000000004010103000100079de7f9b798c896f4a0f9fe0000000001000009000000000ed2f3fafbdca295d0f7c8990000000002020001030200000ea7a3a8ccc1c995a0e0c18f00000002000101010203000004dee880ca9fd2bda98ca6c70000000202000001030000027ec7b3e28de4ea85d7cfde00000101000001000700000002eeeee4ef8ae1accb82c9bb00000400010000000000000501b7aac7e29694ff9f93ff0002010100010000000000051982efa0a8fe99c6f9ddac0301000000000000000000067f86c4f8d3b4ddedb9b70b,
  0x9000001000005f8a3f0d0b18bb09995b50000000001030102030000000f9cc1c9e4a9c68192d78300000000020201030002000002daf7fe9a99d293a7b3e100000000020301020000020001c5a68ac083baf980bea20000000100030103000200000af0a2bfe7d7d0eccbe900000001010000080000000001a888a2e6a1bf81e283ab0000000200030102000000022f8bf0949ff8dfd086b900000002010001030102000004df92bedcd8fd95a9a3d100000200010100030001020001b9b4bb9087bff6afb9af00010000000001080000000037aa88da9086f1abe9a601000001000300010002020003e0a88efd9af0ccd5d20b,
  0x9010000000001f5f4e681d6dafaddafa0d30000000000070000020001007b868084e3bf93e4e6a2a200000000000800000000010111c5d5b4d8ffd1cdcafccc00000000030201000301000002f0a0d58cb18592949fbcb00000000101010007000000006cd393e18ee0c3dad987fe00000002000201010400000025b2c392988af2eaaab48e00000002000301010003000054e5ae91cfb2aad09f8dac000000020200010300000200079bccc3d781d0898ffef30000010100000008000000000186af85cfd6b8b798b496a400010000010000080000000015cb9081bc86c691e2cea401000000000100080000000001c9e3ccfdf38fffb1f79c0b,
  0x10900000000003ec3fbcddae0deca86ab9a0000000000080000010000011b9dc7b6d4eddd8e88e00000000002030103000100000ce1a8b6ecf1eab88c9fd20000000003020103000001001e8ef5a29ae3bafee6afdc00000000030300010201000054e0afe7bd97a785ecc7c800000002000201030200000050b2a687b0deabb3dbc99300000101030001020000000201bd8c84d2c8e3b2e7b5ca00000200000201030002000010a9d8f28ae5f2b385dac900000200010001030300000002acb6b0ad9fe3d39cfcda000101000000000800000000088ed681dd92d0f0b1e0bc01000001000000080000000051cfc4c9b1fdd6de9ed40b,
  0x801000000000101f8aca090f6e9e3e08fc70000000002030104000000005fab90d5c9cdcdf2a984b300000001000009000000000030aede84b0878ec1969f990000000102030100020100003bd5e6d697bcd8bfaf95f100000001020301010100010013ec8cbb96d888c1efebb90000000202000005010000000a8396eaaed9a39bd193f400000100020301000102000007bf96a4c6c3e4a284f0ae00000102000200030002000007f6feb4a4efc58c85cadb0000030100000000060000000dabae91c38da2fca6e3bc00030000000001000600000003b7f194cbf08be1c498c70100000200010004000200006fc6abe792d0939ca8c30b,
  0x90000010000000ad1efc3dcac8efd87c0fb00000000030500010001000025bae18ffdc7fb86ac94910000000008000000000001012febba8dbea3f6cfb4c300000002010202030000000012fdde9db2aab0968bdd8800000002030101000300000024ded5e5d7acfcf6f3839c00000101000008000000000003dff486f196a6ebdeb8e50000010101010303000000003797cff7ebfce6c280f8af00000101030201000000020003a5f4a8a08da3bca687a30000010203010100000000020de284e382e9fdac9ed60001000001000800000000000db4a48ca7c5f0ffc4d2fd01000000000108000000000001a7e6c692add8e2c4b4830b,
  0x90100000000004df0af8bd28cd2dbe484f100000000070000020001000013cfa8d1c384b1fadffb8e00000000070002000000000159c2cb9ae8af8094e3d800000000080000000001010008f39892b4ce9ef380f28800000002030102000200000047ff98c7e7c386b7dbbff2000001020100030300000000718eab93ed8882c7c3e2aa0000020003000201020000000ee9c6d09beed8adf791ff00010000020007000000000006e3d89e8d84c98b838fac00020000020101020200000001d2d7adb8df8483f9ade50002000003000201000200000bbdbae2d3c6e390dc98a902000000010003030100000001dea9e68986ceacece0cc0b,
  0x10900000000000072b7ac879bd3b4c0f3b5d600000000080000000101000052efc4b8c3bcaac1d7d3a000000000080000010000010006acd5e08ba5ca85f1b68400000003010202020000000001e7908ab9e3afd5cbf3f2890000010301000300020000004ac6b686dcedf3c48fadee0000020103000002020000001bd189b1bbc2a8e4d59dcb00000300010003030000000057c49495efcec2e7869ce00001000000080000010000001b869bfba4c090ce8aaae200010000030006000000000046d3e4ebfb91a5b7c3dfe20200000103000001020000017f95f39ad29ec2a6ffec05000000000000000001040001e899ba9cfacc95e1fcb40b,
  0x8000001010000002be5d4eda5f6c0eea893a3f90000000401010202000000002fd5c1f7b5d9af9bdb9dd9e800000007000000000102000005f2cfe6a7f6b2e8b0b2ebda00000100000900000000000027c3a595e0d8c9e7b29db5e20000020200010302000000000cd1c0b896bba5e9f0aea1ea00010200000007000000000019a6f8f7c5e68da5e28ed6da00020103000000000202000001bafa8898dfacee8cb3d6f80002020200000001010002007ed0eba7f29283b28b9aef01010201020000000000020113efcff0bbaf8881b9c48e02010002000000000500000001cf9adee1f489f996f4baa4040001000000000000050000108fe890c6a2f4f2f7a8860b,
  0x9000001000000005c93ba8bc79af6a4ef8be700000007000000020100000057c0f4f1c8d9a7daecaba400000008000000000001010002d0def8afb2a6abe9a4ab00000008000000000100000113d2e9d5fab6abc5dad90000010301020300000000001cf3d8a0f6b0a4a78fc2f5000003000103030000000000018ed987a5e1b2f7af84e9b600010001010700000000000044deffe7e0b9d591d1c9d10002000102010301000000000b9bf99ffed08088b1c2da0003000001020300010000000892c7a695c885ffadeb9800030002010002000002000008f7adc2afe6a8f1899992010000030101030100000000149688ddf298a4ccde94f10b,
  0x901000000000000039593ca8a80f4affa92dac60000010302020200000000000abdfb9ac8ab8db0abc7a7b700000302010101020000000004beb5fce4e698b1a486d78a000200020201010200000000018daaf094c2e1fe88b4d8a200020102000300000200000001dfd4d787b59dbed8d5d1a800020102000300010001000051a7cfc8a884e4fa9af2ac0003010000000600000000001bb98cbcdbddf8f0f4acdb010100000008000000000000019fecf2dbcdf2b8c4afe0ee0200000006000000010100000291e0fe85ea86f8fe929a02010301000000000001000224c9d8ff91c5a3a791bd02020100020000000001020005a58cbab1cafc9a89c9e30b,
  0x1090000000000000001d6f8d98ab7a9af80eedfeb00000007010100000001000016a19adcc8bbac9bb0bdec0000000800000001010000007b9397cabdb1ccee90f4a400000008000100000000010002bd89f39683f6e3979d9c0000000801000000000000010fead9968a83e6bbffd4000002030103000100000000399eb197b2efc19de7fbb60000030301000102000000007687c2fda2fcc0d8f8cbec00000700000000010002000012c0c28084ced6c4acd00001020101030200000000000480b0ffea84c9d682f4d3d60002000301020002000000000fefc2bef8decfdbeda9a30200000001070000000000002d83b59ae6b4e4dcb680aa0b,
  0x104020300000000000006f8cc82c18fa9b7b3a8c200000302020102000000000008c7d8f3ea8ee5fab898910000030400010002000000000683d2ccb4d8dec3e2809000000800000000000000010127c0dcc4e5b99ca7d000010000090000000000000006cbff95dcb4e4bed79ca2000201020003020000000000088bdbc08cb9abcd98f6df0002030002010000020000001797eecbf2a48693e2c00102000302000000000200002184fbccfdc5f7b4e0980102030001010000000002000398f7f59ecac5f888f002000004010100000200000001acaf859af1ade2d8ada802000100000700000000000051d0d5b0d4edaec88bdc0b,
  0x9010000000000000008d2d785cfcbba9ed0ccb2e50000070000010200000000000693e8ade286fa8581b3a9b3000202010302000000000000138594e9bc9e9aefc9fdb6ac0003030100000201000000003be6e487eadda796ebccac01010100070000000000000001b6caa7bed9b394b1afb4f101020500000000000100000105de9289bfe9968bdd9e0201010202000002000000000299f5d7a5aa82e7f8e498c00201020201000000020000003d9496e7c7f1f2d1dd9aec0301020100010000000200000880a898fed7b29d92f39904010000000005000000000069f9e1c0f2f79ce6c083ee06010000000000000000030035cbf0babcfac3b594ce0b,
  0x601020001000000000001dd98fc9ae68d9bcbe7fc0002030102020000000000000590df80d9eecafcc58ce60002030301000000010000001cc4c4c9fe838e8fa1be00020401010002000000000001c988c09cddbdc29085fc00030002050000000000000033ab95d184d394acecb7000302010300000100000000019fb3e982e7dcb4b1f8ec00030301020000000001000003b3f38ecfea9fdaebe2000304010100000000000001018284b9b3ffed84de0005000202000000000001001f9b9aaab0b0b4fbb201000008000100000000000003abc4bbf0ff9794e9e7f80201000007000000000000006ac58bd28084fff0bad70b,
  0x80000010100000000000ed2f1b4db96dafeb8c89400000800010000010000000002ecccbbf4d0cec2bbb8a60003010302010000000000000ea7f9dcf19e94dfd7d2ff00030301000300000000000007bdca84a59bae8e9ec9d70100000900000000000000000dc3c6f0bbddd0998cd0d20103000006000000000000000dc8b9b8a688d7cecb9d980103030101000000000000010294bfc6e38fb284d40203010100000201000000000184dd9dbef0b0b1a0baa203030002000000000002000004b1ae818883d2d8aee604010300000000000000020024c2ebb3dcbadec9fe0600000100000000030000001afba98ba391d6bbddac0b,
  0x90000010000000000000388d3d98381c6d892dc85da00050100040000000000000003d3e1e7f6b48bf3d9aa8fbf0007000000020100000000000195a4e0b3e5d2c2c7b684a200080000000100000000010002e3b5f1a8f386b1e2ce00080000010000000000000108c5aff79c85d1caaa02000107000000000000000003ff99d9d8e38cf4a6d58ced02030103000000000001000034c28beaacbd94d4a2860302000102020000000000000793b1c6edcfa8a4e6f7b003020101010002000000000012cfa09ba591819da9a8d505010100010000000200000002a9fcc8d8cfebdc95e2c90600010000000003000000000bdee99081e0cbe78f988c0b,
  0x901000000000000000002a5e08bd783d3d5ada8d5b3000700000102000000000000018decccc4c6ede0c4aeacf30007010000000200000000002380f0d985ba8399ecd5ad0007010000010001000000000be891b798cce9b9a5a7ac00080001000000000000010054e0d8e890bdd194f200080100000000000000000101e8dae7fa89f9e1fe010300060000000000000000028cb3a5fdcea4b6a6f8aec30303010000020100000000000a9fd18fcb9eb9eab69a03030101000100000100000001b2b2faa4d9cd94b682be0401000005000000000000000197be9393aaa4aeeae2eaf5070000010000000000020000078280bfa4cd8d83c8810b,
  0x1090000000000000000000f8699b5d9febfc58ca9d900060101020000000000000010e6b7b6c08ba3bce3a7ef000800000100000100000000309feeb89292c1f4a1f40008010000000000000100002cefc783abdf9eecde0301000600000000000000000dd4a1a9a790a9dfa696b90303010001020000000000000686dff7baa8dfa283d5fe0303010200000000010000000582e9b5ffbed6e8ffa20500000104000000000000002ca1d9a5b4d9e9c995b10601000000000300000000006bebcc9697bebef08cf407010000000000000100010001efebcef4a9b29eb608000000000000000100000104c6daf0d8a083b20b,
  0x7000201000000000000001ea3e4c79fe6abb8a5fbac0008000001010000000000001780f4e889c6e3d6a48fc0000800010000010000000000049aa8f6c5f4b9ded6a2c001010800000000000000000033bed9f7f7c4e6d3ec9de7010800000000000000010000328da1d8d8c7d8cfc0040001050000000000000000249da5d7b0d7d6fcad8d880501000004000000000000000993d9a184bffecda4efc50601010000000002000000002392b3d2ac9acf99f2c007000100000100000000010001eabba890b9d6afc0070100000000000002000000039b92bdf292f9bceea008000000000001000000000103f2dcb0e987d8c00b,
  0x8010100000000000000000badec8cccd7d9a4e4c5c001080000000100000000000001d68cfdd6d2c795eddbf80301060000000000000000000c89abb8f6e3b5a5d1dec305010004000000000000000005cad48581a1fca8aa8ac506010000030000000000000003819fa6b2e6c0ecf0c2c20602010000000000000100000188bcedfec8c4abda0701000000000200000000000ec4a49ec1d1a5fffdd207010000000100010000000002e495a1f789dca5d9bc07010000010000000100000017eef9d99192dca18608000001000000000000010003d49eb2d18fa5aa08000100000000000000000105da9cb9afb9e60b,
  0x503020ebce7f9fe81e1eec882a0b30000000000000000000200070107fbee8692eac4c28dd5abaf0000000000000000010300000604a2addc809ce889adb0e8810000000000000000020000050301f19ac6a1a8b792b9cf98fd0000000000000002000100000754abf9c2ebe5bbf3b891fa000000000000010100000100071cacb387ee96cbabd8fd8c0000000000010001000000010702f9edddfab196dbaed8c8000000000100000000010100071cd8d0edaaa893e68b9b0000000100000000000100010701c6a8a0beaec88685d400000100000000000001000008079d9c9c8eb0a9afca0001000000000000000001000814b88b87e9929aa4010000000000000000000001081abea8d3c0f0f50c,
  0x801013dc794c189fbc3b4bdbb9fce0000000000000000000500020336f7fba1ffd6eca09484bfe8000000000000000002000107000fd99488b3bf8edbd1b3cadc000000000000000004000001050ba3f1b786bd8098e0c0e7ed000000000000000101000008001bbaafaeafd4d6eb97cac7960000000000000100000100080005a4dca6b7b1c59ebceae0f0000000000001000000000108005fde9ae085d88bccb99db00000000002000000000000010704f885c9bad9dfd5a1dae1000000010000000000000008015cdd8786a1f0be9beef80000010000000001000000020604cbd8bacbfefdee9efc0001000000000100000000000811d1b2f3bdc5989ad8010000000000000100000000081f8698958599a59e0c,
  0x9010036c2ae92e4b0ebc185b09ea90000000000000000000600010331cc94e4ced2b299ccb4f9ba000000000000000002010106003cf48ad48bc8bac48ac3c9ba0000000000000000040100000501c4deeeedadf7a1ae9d86b00000000000000002010001030316fac196a2a9b79bc4bfb1d40000000000000300000000010603adf4a3d3a1befffcf3bc9e0000000000010000010000080001cffdb6ddcd8299cdf7f7d70000000001000000000201030318b9ffb6bacbb3a2e3dbbf000000010000000000000108000285d8e78fdef0939f8184000001000000010000000003050ee2b4fbb896a68be1c20001000000000000000000080140d4a6e4c5b6f09494010000000001000000000000080181df9e8bd390e0d10c,
  0x701000209ccc38387c1e7dde498baa4d30000000000000000040001050008e8e8d690caf9cf8fd697bfd20000000000000001000009000007b6d9cfa79bd0d288db9fdece000000000000000202010002031ef89ebab1f3e69ddfb495d50000000000000102000000070002f681dfeff78cdfe5cbbac2d60000000000000200010101020338c3d5b8989ef8b3bdf98be90000000000030000000001000620ffd68ff9d183b1beaa9ed00000000002000000010100000607aaf2dde2efe4bbb4eeeacd0000000100000000000302010301c5f1e29ab4cbdbec87c398000001000000000100000008000e89e7b9a6ca80cc9696cc000100000000000001000008004c92b4a1dcfea09bc8b20101000000000000000000000801c4bbceb68581d4adc60c,
  0x901000002d3dafdecc2f1b695a8ebc2f70000000000000000070000010201a7bbfadcc69de4bffbb6c6f20000000000000002020103020005bfeef8b6aeaeb1c5eab6f8c00000000000000200020103000244eeca9ce1a9e682bd98888b0000000000000300010001050043a085c597e5feb5a9ae84cc0000000000010100000008000063ccb89590d2d48e8cab85fa000000000001020000010203012cea9c80eca1f4e3dfb3ca86000000000200000100010103020eb1868cb1b9d6b0ceaadf80000000010000000001000800000489c2a38a8cf38eeed388800000010000000000000108000031ee80a196cec2e9f984800002000000000000000002030301b8f2a9cff7e584ddd4800100000000000000000008010009e980aaf6d3f3ade2800c,
  0x10900000002d7dfa7a0aca9f5e0f79485eb0000000000000000070001010102aed6d89fb491dcdbbbedded60000000000000004000103020002b39c918fd982e8b6c2899ccb00000000000000050001010102199c8da9f6a0fed0d8fdded70000000000000201010102030001e3b5b6ec8acaeed7c985a6930000000000010100010007000001bfa19ef7fd84b1b39f88eb8a0000000000020001000103030001e6919591e88a8aa1f5e1a300000000020000010001030102159aebd89184f1d1e58d9a970000000100000100000008000006c8c6b596afedbef094dac80000010000000001010103030057eacc83d0f883a1caaea40001000000000000010008000005c7ff87f8eafbf296bee80100000000000000000108000014d5a797a497bef0cbf20c,
  0x90000010058eae38bd6caa9d9eb9de3b60000000000000007000000020131b0a9aebfbceaac8ccc9fab000000000000010203010300003192ae9ddefff59cdef4949e0000000000000202020003010001a3ab88dad48ca4d1d5a391950000000000000202030100000202b688f59eaf9599e39acc950000000000010100000800000060ac96b4c4a082ca96f490ba000000000002000200010500002afae7e8ca88cfce85c4f8e70000000001000001000800000032e482b48bdaeae28ad083a3000000020000000101020200020583f4cb899baacfa4c2efda0000030000000000000101020339b4abdaa29aa8b0cca4be0003000000000000000001020404d3cc838e90b7b6c6b2ac03000000000000000000000106169087e9e3c8be85b8cf0c,
  0x102040300000002ee84b9e6fd8ad8f7a09d90ce0000000000000303000102010001a5c3c6ecedcddbc3c8d0d4ff0000000000020001030300010013bbdaded9b1fda49af399910000000000020002020103000001c3d59cd1b4e5e4beafbba19c0000000000020300010101000207eec0ddff84cdf5c1b8afeb000000000200020000030102003a8ca4f090bc8194b59ce0990000000005000000000000010405d8f3f4de9086d98791d1e00000000200000001040000020110af89b0979bfafabbede6ce0000020000000000020301020002ccc0aea1ace999a6d2ddee00010000000001000500010200169ea8a3baf9cea2848eca0001000200000000020001020228c1e595adc5ebd7b597ce0100000000000000070000010102dbb0d388a6b1f38393ce0c,
  0x8000001010023c8ace0b1b0d7b2fb8f97e1fd000000000000030301000300001f9f979d83b9a698e5e994b6e200000000000007000000000102049eada0acf5ac8696f8fbe3bc000000000001000009000000002bfea0f2ba83a599baf7cbfe900000000000020200000501000026b89ade82f0c7f99bf2a6e3e8000000000100020100060000000880c7e380bdd0f8c98dfaacb60000000002000200000401010010e9a1a2cac988eba593abdfd500000002000000000107000000059e8babae8ce3f189f5afccd8000001000000030101010003006e92e2ce83e5b3b1f2c4b5e00000020001000001010002020139988cd39f95879b9ff0f3bc000200000100000001020003010bb380b2e698aeb4ccf3f1b80200000000000000010400030043f2edeea899b7aee6aeb60c,
  0x90000010000749199c4bbcec9d59886d9e6000000000000070000010002000fceccdaeb8ad0b6d88586fd0000000000010301020300000040f4f69dd08bab9cabfd82ea00000000000203000201020000018486979fa3f5d995e8a794a3000000000003000105000001002fbbe582d98fb480caefdac60000000000030301000100000205e1ffd5b78ff4f79482c2aa0000000002000100040300000065a4d0cbd3ffc39588c5f1900000000100000201030300000031b896e895f08dcde2c3c9f80000010100020001000200030008ecf8f5c1ce9fbdc1a3d3b000010200010000000100010202019aacb3d6a9ba89a1ffa2c40002000100000001000201030002d6f7a4dc85d799fae7c8010100000000000000080000000986fc9da4b4c9b4b6d2dc0c,
  0x20103020200000033ebeec996d5f791afc3eca900000000000203010200020000449fc284b2ffadfc82b9f1940000000000020302010100000104a5bee6edc2f0a4d1dfc6800000000001000008000000010019f6a38af4b7efa7e688d197000000000100030005010000000de0ededdfe1b4c091effb9400000000010202010003000100028ecff492b2c9e098b09a85000000000200010202030000001ff4c7cddef6a2efc489b4a7000000010000030102030000001cf786b4e09fb0e2b9ec9dda000000010100000008000000000581a3dfa3ca9db7a0f3ebc60000020000010001030100020003c1ddb696b1fbb1adae97a80002000000000001050000020038b7a8dccfd8df82f3f79002000000010100010000020102039fb6bccebfec9ceeaa940c,
  0x800000101000001e4f2eebfc0cda1abbea7d0ef0000000000000801000000000103e3dff2aeccadaadabba5830000000000030103020100000004838db4f5c5a5f3d7ef8bcde9000000000100000900000000005bdeecaf8ac3a0d9bc97bfcd0000000002010102030001000002a6f586d48488f1bdac94ebff000000000202010002030000004ab3aef89e84e3b3d0e8bbb3000000020100010003030000000195abb5c88ccce682d6df87c50000000202000003000002000103a69be1dccbdda39ad4f08d00000005000000000100000400078ec79eabbaecb0b4e8ad8c000002000000010500000002002992d2949adeb2c1df84c9f00002000100010101000001020105f5bdd4dad7c885fdd8aee00200000000000005000001020031f7beb5decde9bc83b7f80c,
  0x901000000000005fdc5c2abb09ec099f7b9aa95000000000008000000000101000198bfa1a0a7eca3cd9db0d6f0000000000008000000010000010d91df9ff289efc5b1dbf0ac0000000003010102030000000007ba8ccae68db7e5ecddd8cb900000000003030100000201000001f6ee9dc59594b1a494f5aeca0000000100030103020000000007fd979cdf90c1998f9e9296d2000000020102000102020000000389c4a0dffc94bcbfc1f3b0a00000000202000103000002000001a6c1d4d08686d0bcda97a28f0000010001020103000200000004eda982b1969dcdfcfdc785d8000100000100000800000000001eb6bdb1e4b9bbd48df8dcf00002000000030100000202000027b5cffbc6bd9ec4cdd9e8800100000000010008000000000008e7a1f6c3f2c3a1b3b5e1ac0c,
  0x1090000000000000f9186e9f88381eb9db5c9fb000000000008000001000001000285e1f5bca6fb89a3abce9800000000000800010000000001158ccec584c58382d69cee000000000303010001020000000aa0f9f4bbdaa292eaded2c0000000000303010100010100000bd0c1b4f8c5d8868da6d19c0000000102010103020000000007e693f18dfdcada90cfadea000000020003010004000000000fc8898cdfe2d6eaac89bc9f0000000200030102000200000003fbdee3e5bdc0c1a4e7b28e000000030100010005000000004eebffeebeb9b3ff92d5c2000001000200000700000000000caa8fceb29380fca3b6ac840001010000000008000000000002edaadbfe80fffdd791d798010000010000000800000000001fbcfef1aeddbbe9a8b2ae0c,
  0x9000001000000000ad39dbbd5c6e2c8f5e1f9adf50000000003020401000000000025db838eb19eb7cf9dd190d283000000030101010301000000001ce78bfeabf6eabfe29a998dcf00000003030100010000020000018494e4ffd3fd99d09dc8bbd20000020100000600000001000001df90a0eaf6cce4abceddf380000003000201000002020000000a93f28c97e9c6ecb684a6f4c2000200010000050000020000007296fac6a8889ab6b2dc98ff0002000202000000020001010064b3f8aa82cdd398d8e888900002000301010000000100000203a7cd8fb2c6ede7a1bfa59a000201000000000700000000007996bbe0addeb1a693be88dc000301000000000006000000005685de88d0bccce2e8bb93c602020000000001010002020000378fe5a1a7c9c8999992ecda0c,
  0x800000001010000000de8a6c3f9b8d4c0a5a89aa9810000000102040300000000000013cef2fbbcb193ba94f8d9d3c1000000030102020200000000002199b2fce2c9a3efb0a8d394870000010301000300020000000003aab6dfc3f3809ab5a7f4e580000003000100030300000000000da9c3d08d99b2e7a696acf38e000003010300000001000200002fa8eb99c0f6b6e388f9e4b1000101000006000002000000000be5f08bbba5fb95e1cbf9a0870002000001030300000001000001c4afdff39498e987ef9fbcd3020000010004000002000100004fa0f1fa90cbdffc8380c3f60200020000030000010000020017b391ce9aac8fccf782cfae0200020000030000010001000102d8c1b6aef3868091a5ee8b0301000100000000000500000006cec6b0e7c1b8a4a8dbd4ef0c,
  0x70100020000000000019f95a4c8ffc7d9ac86b1c6c40000000108000000000000000112a791b5d1fafe93dde4ba0000000302010301000000000001f1f684e495f1d384eafdb9b4000000030400010002000000005d8c87ed828787e9b6be8fd70000010000090000000000000001cddfd197b4e5aa9df8e895a2000002000301030001000000003fb8c485bafae3c4bf89a8a2000002010400010000020000003af8f78ae1ddbbd5d1f598b4000002030001000301000000000199d1bcbdb681b6839ea69ac40002000100000700000000000065ef978ca1ffc882fdbaeb9301000101000007000000000000088adfbcf9ebb480d6dfd7ce0102020100000001000002010002d59888dfcc84cac49ae6880201000200000200010002000008dc8fb58feec2de83f2f2d20c,
  0x304010101000000000006808a96eba0b89dc992b8ceee0000000800000000000101000012ca99c8d7d48ddef49af3980000000800000000010000010001f1bc9698a8a39fc6a4a3f00000020004010300000000000002b8d9e28586adebcfb2a0d49400000302000102020000000000028089aab8fcffbd889fc4fcb90000030201010100020000000020a7af97d084b7b9abf0a5ca0001010000080000000000000001a6e2a891ae81c5fcf680de9600010103000103000100000000018da89b9baec1d48bf6d6efce0002010002030000020000000077c183fcd2a7a5f3aefe87b1000201020003000000020000002e94d0b28db0dbd8b9c3e9cc0003010300010000000000000205cf97c1c4c4fcf6ac9a86010000010008000000000000005fb7f984ae93ccd5e9eccb8c0c,
  0x90100000000000000058fcee78cbde1ddbefea0ce9a000000080000000001010000007ad589fea7a1eae9ceccf8a80000000800000100000000010001ccb8bdebb6d2e2dcf0edf70000000800010000000000000109fcfec6fe87dbbea383ca0000020301020002000000000003df83c38e9c9891f4a7f495ec00000302000104000000000000059b92bc868fcdefb094e486dc0000030301000100020000000001ccc8b5dd96c6eed1d8c5e3970000030301000200000001000012bdf2ce8d80f4b9d596f1e1000100030103020000000000000382f3eeeab2b7e8c6c5f19fec0002000201030002000000000002d4dbe1d88d9a89c8a7c4f7dc0101000000080000000000000001caf1fd839b86f4839fbeaba4060000000000000000000301001a9dfeb2fa94d7a0d593d10c,
  0x8000001010000000000029dfdb9bbded4e9a3e2d5daf700000008000100000100000000028ff6c6d980e2a2f8c9b4e48e0000030201030100000000000007cfece7f6b99b8a88fbf6b6de0001000009000000000000000004be9bfb9cfee8eab6fdef85a30001030201000102000000000001a4fea9a288e9a0838c8a91a90002010300030000000100000010a493dcc1fcd698fbb2a9a40002020001030200000000000004aaabb5ad9282b7bbb1cf91940201000401000000000002000003cd8fe3978ecf9f96ecfff20201020201000000000000020025affbb5f1bde6beb5b5b40300000301000100000200000012e5fb8afbda9c9c8a80c5d204000100000000050000000000488185a7fd868acbc3fe939b0601000000000000000000000376bd9dc2e7defde3ab860c,
  0x901000000000000000001e4f883e8c3888992b6e4a6800000060001030000000000000079bb84fdf9d9feb1acf8be960000070000020001000000000056f6ca91b383bfb9d4fb9cfa000008000000000101000000001898a1faddbdd28098aac89600000800000100000000010000328b88b98a9881ee8ffad400000800010000000000000100039681caacc9d8d0fcfac8000008010000000000000000010be4bdbdf8899586838a00020301020002000000000000019bae949ef3b491f1bab0f10003030100020000000100000003dfa99b938dc4e4b1939ba8000500000102020000000000000199aa84f381f5b5eade9ef7d60101010007000000000000000001a2bae18ee7e9bcdb9482a7c0020003010002020000000000001fc685b4fc9aa3e2c5fbd3850c,
  0x10900000000000000000007aab2f5e98387a2eed1fab1ae0000080000000101000000000001fec5cc8dbdccd6a9d2f8ca8b000203010202000000000000000fc7c2b4898d8cf7fdd4a49e84000600010100000002000000001bb9f2c0b795cb9e8bf2b6c7000601000000000300000000002d9eb2efccd081f9b3deaba40007010000000000000002000045e9a5eebaf5bb8aeedeed01020301000003000000000000039480c1ddaf85c48ac1eea185010303010000000001010000000bb4d48f9fe590b590f3d1f402010000070000000000000000049f809283aef1ffaff1ae95a0020203010000010000000000011bc0cbb89da9fecbd6fd020301010000010101000000000ea0a683a2efe1fcfe8cf79102030101010001000000000100088bd8b394e280fbc0cfc40c,
  0x9000001000000000000001cf7c4c895efe0f99aed93980005000400000100000000000001fac3beceeadc94d5e6f4e60005010004000000000000000027c1d9bbcda2a3abfee6b7fa0007010000000002000000000001b7e4c6f7c6d68ec9a7ccb3000800000001000000000100003daea997c0deab81f8ec0008000001000000000000010002cbf5f28bbec6ebf7e2010302020002000000000000000fc1cbcbff86f7fbc49ffbb60200010700000000000000000022cdce93e8ea95d0f9a3ccc40203010200000200000000000007a8abc284b9f0cef8e58ac1030301010000000101000000003ff9c69895f0d3a6efb08a0600010100000000000200000003afa7f4fac784c4cecbec0800000000000000000000010106d8b5e5a7b3c9b4d60c,
  0x109000000000000000000004895dea8a0888c9ba7f7b597000700020000010000000000000ddeefe9bfdff19ea7a2ccec000701000002000000000000001fa6fdacdc92f0d0c3b792d700080000010000010000000000029bcdf996f4d4ba98e9aeeb0008000100000000010000000008f3e4eea5cfca8392a6a1010800000000000000000001005895ef898d9ca4ca840203010202000000000000000066f38f938bcde3b992b3d7b4030100060000000000000000002b808590f1ddb6f8b1b5c088060100010001000000000100001491eb9186e49cd5edda070000010000000002000000000c9c98e89591b890a9b1890701000000000000000200000001b2b6ddcadde3dec9c0da0800000000000001000000000101b0f69db2e5dcd59d0c,
  0x7000201000000000000000004a097f4d386ecc7caa4a98c0008000001010000000000000003d4cacab9c78385e181b494000800010000010000000000005a9dafe5a09aa69996e2a0000801000000000100000000000ce1f2c080e18a8a98d9a00101080000000000000000000007e286dae4bbeaece88786a7030500010000000000010000000caec59ab7dbe694e4900400010500000000000000000005cff3aab7a5d7eef2d4a8a80501000004000000000000000001beb593a2ddea918ed488c7070001000001000000000100004eadf6dfbbccc1f3880701000000000000020000000054a2f098f2aef1e2ae9e0800000000000100000000010002acfea0bbb3f294d0080000000001000000000000010491f293efd096840c,
  0x107000200000000000000000001ccaac79ecec1cff79484cc0107010001000000000000000001a6ebb8c2f591b8e3d4edfc0108000000010000000000000016e79acce0a6f0df84a29c0400050100000000000000000002d2ab97e6b4a28591bee6ca0700000002010000000000000010cced82e0eccff1bdcae40700000101000100000000000005d5d781c99e8f88decc9c070100000001000100000000004bc992e5a3b7df89aba80701000001000000010000000005dec3afbbd4eaae829f0701000100000000000100000027d4ecf2efdb9ae7c40800000100000000000001000001b985d2b689d589c208000100000000000000000100048b9be7fbb6ebd40801000000000000000000000105a68890d9e3b10c]

/-- The triples `(n, b, a)` of part 16. -/
def enumC16 : List (ℕ × ℕ × ℕ) := [(10, 100, 73), (10, 100, 77), (10, 100, 79), (10, 100, 81), (10, 100, 83), (10, 100, 87), (10, 100, 89), (10, 110, 13), (10, 110, 17), (10, 110, 19), (10, 110, 21), (10, 110, 23), (10, 110, 27), (10, 110, 29), (10, 110, 31), (10, 110, 37), (10, 110, 39), (10, 110, 41), (10, 110, 43), (10, 110, 47), (10, 110, 49), (10, 110, 51), (10, 110, 53), (10, 110, 57), (10, 110, 59), (10, 110, 61), (10, 110, 63), (10, 110, 67), (10, 110, 69), (10, 110, 71), (10, 110, 73), (10, 110, 79), (10, 110, 81), (10, 110, 83), (10, 110, 87), (10, 110, 89), (10, 110, 91), (10, 110, 93), (10, 110, 97), (10, 120, 13), (10, 120, 17), (10, 120, 19), (10, 120, 23), (10, 120, 29), (10, 120, 31), (10, 120, 37), (10, 120, 41), (10, 120, 43), (10, 120, 47), (10, 120, 49), (10, 120, 53), (10, 120, 59), (10, 120, 61), (10, 120, 67), (10, 120, 71), (10, 120, 73), (10, 120, 77), (10, 120, 79), (10, 120, 83), (10, 120, 89), (10, 120, 91), (10, 120, 97), (10, 120, 101), (10, 120, 103), (10, 120, 107)]

theorem certs_ok16 : checkAll enumC16 certData16 = true := by decide +kernel

theorem enumList_eq : enumList = enumC0 ++ enumC1 ++ enumC2 ++ enumC3 ++ enumC4 ++ enumC5 ++ enumC6 ++ enumC7 ++ enumC8 ++ enumC9 ++ enumC10 ++ enumC11 ++ enumC12 ++ enumC13 ++ enumC14 ++ enumC15 ++ enumC16 := by
  decide +kernel

/-- Every triple of `enumList` has a certificate that passes the check. -/
theorem certs_exist : ∀ e ∈ enumList, ∃ X, checkCert (hdN e) e.1 (hdM e) (decodeCert (hdN e) X) = true := by
  intro e he
  rw [enumList_eq] at he
  simp only [List.mem_append, or_assoc] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact checkAll_sound _ _ certs_ok0 e h
  · exact checkAll_sound _ _ certs_ok1 e h
  · exact checkAll_sound _ _ certs_ok2 e h
  · exact checkAll_sound _ _ certs_ok3 e h
  · exact checkAll_sound _ _ certs_ok4 e h
  · exact checkAll_sound _ _ certs_ok5 e h
  · exact checkAll_sound _ _ certs_ok6 e h
  · exact checkAll_sound _ _ certs_ok7 e h
  · exact checkAll_sound _ _ certs_ok8 e h
  · exact checkAll_sound _ _ certs_ok9 e h
  · exact checkAll_sound _ _ certs_ok10 e h
  · exact checkAll_sound _ _ certs_ok11 e h
  · exact checkAll_sound _ _ certs_ok12 e h
  · exact checkAll_sound _ _ certs_ok13 e h
  · exact checkAll_sound _ _ certs_ok14 e h
  · exact checkAll_sound _ _ certs_ok15 e h
  · exact checkAll_sound _ _ certs_ok16 e h

/-- **Proposition `lt:prop:binomial`(c), fourth case (the computation):** if `n ≤ 10` and
`N₀ = b / gcd(b, n) ≤ 12`, where `p = a/b` in lowest terms, then under the conditions of (a)
`B(N, p)` is `n`-completely mixable. The certificates (weights of a convex combination of count
vectors, Lemma `lt:lem:count`) for `B(N₀, p)` are checked by the kernel (`certs_ok`), and part (b)
extends them from `N₀` to its multiples. -/
theorem binomial_c_comp (hc : H_lt_lem_count) {n N a b : ℕ} (hn : 2 ≤ n) (hn10 : n ≤ 10)
    (hN : 1 ≤ N) (hb : 0 < b) (hab : Nat.Coprime a b) (hN0 : b / Nat.gcd b n ≤ 12)
    (hp0 : 0 < (a : ℝ) / b) (hp1 : (a : ℝ) / b < 1)
    (hint : ∃ m : ℤ, (n : ℝ) * N * ((a : ℝ) / b) = m) (hlo : 1 / (n : ℝ) ≤ (a : ℝ) / b)
    (hhi : (a : ℝ) / b ≤ 1 - 1 / (n : ℝ)) :
    CompletelyMixable n (binom N ((a : ℝ) / b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at hp0
    · exact h
  have hab' : a < b := by rw [div_lt_one hbR] at hp1; exact_mod_cast hp1
  have hlo' : b ≤ n * a := by
    rw [div_le_div_iff₀ hnR hbR] at hlo
    exact_mod_cast (by linarith : (b : ℝ) ≤ n * a)
  have hhi' : b ≤ n * (b - a) := by
    have h1 : (a : ℝ) * n ≤ (n - 1) * b := by
      rw [div_le_iff₀ hbR] at hhi
      have : (1 - 1 / (n : ℝ)) * b * n = (n - 1) * b := by field_simp
      nlinarith
    have : (b : ℝ) ≤ n * ((b : ℝ) - a) := by nlinarith
    have hcast : ((n * (b - a) : ℕ) : ℝ) = n * ((b : ℝ) - a) := by
      rw [Nat.cast_mul, Nat.cast_sub hab'.le]
    exact_mod_cast (hcast ▸ this)
  set g := Nat.gcd b n with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hb
  have hgb : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_left b n)
  have hgn : g ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right b n)
  have hb120 : b ≤ 120 := by
    calc b = g * (b / g) := hgb.symm
      _ ≤ 10 * 12 := Nat.mul_le_mul (by omega) hN0
  have hmem : (n, b, a) ∈ enumList := by
    simp only [enumList, List.mem_flatMap, List.mem_range'_1, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq]
    refine ⟨n, ⟨by omega, by omega⟩, b, ⟨by omega, by omega⟩, a, ⟨by omega, by omega⟩,
      ⟨hab, hN0, hlo', hhi'⟩, rfl⟩
  obtain ⟨X, hX⟩ := certs_exist _ hmem
  set N0 := b / g with hN0def
  have hN0e : hdN (n, b, a) = N0 := rfl
  set M0 := n * N0 * a / b with hM0def
  have hM0e : hdM (n, b, a) = M0 := rfl
  rw [hN0e, hM0e] at hX
  simp only at hX
  have hN0pos : 0 < N0 := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_left b n)) hgpos
  -- `b ∣ n N₀`
  obtain ⟨n', hn'⟩ := Nat.gcd_dvd_right b n
  have hbdvd : n * N0 = n' * b := by rw [← hgb, hn', ← hg]; ring
  have hM0b : M0 * b = n * N0 * a := by
    rw [hM0def, hbdvd, mul_assoc, mul_comm b a, ← mul_assoc, Nat.mul_div_cancel _ hb]
  have hM0le : M0 ≤ n * N0 := by
    have : M0 * b ≤ n * N0 * b := by rw [hM0b]; exact Nat.mul_le_mul_left _ hab'.le
    exact Nat.le_of_mul_le_mul_right this hb
  have hcc := checkCert_sound (by omega) hN0pos hM0le hX
  have hp : (M0 : ℝ) / (n * N0) = (a : ℝ) / b := by
    have : ((M0 * b : ℕ) : ℝ) = ((n * N0 * a : ℕ) : ℝ) := by rw [hM0b]
    push_cast at this
    have hN0R : (0 : ℝ) < N0 := by exact_mod_cast hN0pos
    field_simp
    linarith
  rw [hp] at hcc
  have h0 : CompletelyMixable n (binom N0 ((a : ℝ) / b)) :=
    (hc (Fin (N0 + 1)) (binomVal N0) (binomMass N0 _) (binomVal_inj N0)
      (binomMass_nonneg hp0.le hp1.le) (binomMass_sum N0 _) n hn).2 hcc
  obtain ⟨K, hK⟩ := (binomial_b_N0 n a b hb hab N).1 hint
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hK; omega
    · exact h
  rw [hK]
  exact binom_mul hp0.le hp1.le h0 K hK1

/-- **Proposition `lt:prop:binomial`(c).** Under the conditions of (a), `B(N, p)` is
`n`-completely mixable if `np` is an integer; if `N = 2`; if `p = j/s` with `s ≤ n` and `s ∣ N`;
and if `n ≤ 10` and `N₀ ≤ 12` (`p = a/b` in lowest terms, `N₀ = b / gcd(b, n)`). -/
theorem binomial_c (hc : H_lt_lem_count) (h3 : H_lt_prop_three) (hpb : H_lt_thm_pb)
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hint : ∃ m : ℤ, (n : ℝ) * N * p = m) (hlo : 1 / (n : ℝ) ≤ p) (hhi : p ≤ 1 - 1 / (n : ℝ))
    (hcase : (∃ m : ℤ, (n : ℝ) * p = m) ∨ N = 2 ∨
      (∃ j s : ℕ, p = (j : ℝ) / s ∧ s ≤ n ∧ s ∣ N) ∨
      (n ≤ 10 ∧ ∃ a b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ p = (a : ℝ) / b ∧ b / Nat.gcd b n ≤ 12)) :
    CompletelyMixable n (binom N p) := by
  rcases hcase with h | rfl | ⟨j, s, rfl, hs, hsN⟩ | ⟨hn10, a, b, hb, hab, rfl, hN0⟩
  · exact binomial_c_int hc hn hN hp0.le hp1.le h
  · exact binomial_c_two h3 hn hp0 hp1 hint hlo hhi
  · exact binomial_c_pb hpb hn hN hs hsN hp0 hp1
  · exact binomial_c_comp hc hn hn10 hN hb hab hN0 hp0 hp1 hint hlo hhi

end Binomial

/-! ## Remark `lt:rem:necessary` -/

section Remark

open Mixes.NormAtom

/-- The points `0, 1, …, N`. -/
def ptVal (N : ℕ) : Fin (N + 1) → ℝ := fun i => ((i : ℕ) : ℝ)

lemma ptVal_inj (N : ℕ) : Function.Injective (ptVal N) := by
  intro x y h; simp only [ptVal, Nat.cast_inj] at h; exact Fin.ext h

lemma discr_apply_toReal {ι : Type*} [Fintype ι] (val f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (A : Set ℝ) [DecidablePred (· ∈ A)] :
    ((discr val f) A).toReal = ∑ i, if val i ∈ A then f i else 0 := by
  simp only [discr, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (by by_cases h : val i ∈ A <;> simp [h]))]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : val i ∈ A <;> simp [h, ENNReal.toReal_ofReal (hf0 i)]

lemma discr_map {ι : Type*} [Fintype ι] (val f : ι → ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    (discr val f).map g = discr (fun i => g (val i)) f := by
  ext A hA
  rw [Measure.map_apply hg hA]
  simp only [discr, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply]
  rfl

lemma integral_discr {ι : Type*} [Fintype ι] (val f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (φ : ℝ → ℝ) : ∫ x, φ x ∂(discr val f) = ∑ i, f i * φ (val i) := by
  unfold discr
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hf0 i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Relation (`nc:eq:cx`) for a distribution on finitely many points, from a martingale coupling
`π` of `X - μ` and `-(n-1)(X - μ)`: `π i j ≥ 0` with row and column sums `f`, and the rows having
the barycentres `f i (val i - μ)`. -/
theorem cx_of_coupling {ι : Type*} [Fintype ι] (val f : ι → ℝ) (hf : ∀ i, 0 < f i) (n : ℕ)
    (μ : ℝ) (π : ι → ι → ℝ) (hπ0 : ∀ i j, 0 ≤ π i j) (hrow : ∀ i, ∑ j, π i j = f i)
    (hcol : ∀ j, ∑ i, π i j = f j)
    (hbar : ∀ i, ∑ j, π i j * (-((n : ℝ) - 1) * (val j - μ)) = f i * (val i - μ)) :
    CxCond n (discr val f) μ := by
  intro φ hφ _ _
  rw [discr_map _ _ (by fun_prop), discr_map _ _ (by fun_prop),
    integral_discr _ _ (fun i => (hf i).le), integral_discr _ _ (fun i => (hf i).le)]
  have key : ∀ i, f i * φ (val i - μ) ≤ ∑ j, π i j * φ (-((n : ℝ) - 1) * (val j - μ)) := by
    intro i
    have hfi := hf i
    have hw : ∑ j, π i j / f i = 1 := by rw [← Finset.sum_div, hrow i, div_self hfi.ne']
    have hp : val i - μ = ∑ j, (π i j / f i) • (-((n : ℝ) - 1) * (val j - μ)) := by
      simp only [smul_eq_mul]
      rw [show ∑ j, π i j / f i * (-((n : ℝ) - 1) * (val j - μ)) =
        (∑ j, π i j * (-((n : ℝ) - 1) * (val j - μ))) / f i by
          rw [Finset.sum_div]; congr 1; ext j; ring, hbar i]
      field_simp
    have hj := hφ.map_sum_le (t := Finset.univ) (w := fun j => π i j / f i)
      (p := fun j => -((n : ℝ) - 1) * (val j - μ)) (fun j _ => div_nonneg (hπ0 i j) hfi.le) hw
      (fun j _ => Set.mem_univ _)
    rw [← hp] at hj
    simp only [smul_eq_mul] at hj
    have := mul_le_mul_of_nonneg_left hj hfi.le
    rw [Finset.mul_sum] at this
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    field_simp
  refine (Finset.sum_le_sum fun i _ => key i).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, hcol j]

/-- Not completely mixable, from a linear function that is nonnegative on all count vectors and
negative on `f` (a certificate of the dual linear programme). -/
theorem not_countCond_of_linear {ι : Type*} [Fintype ι] {val f : ι → ℝ} {n : ℕ} (y : ι → ℝ)
    (hy : ∀ k : ι → ℕ, ∑ i, k i = n → ∑ i, val i * (k i : ℝ) = n * mean val f →
      0 ≤ ∑ i, y i * (k i : ℝ))
    (hf : ∑ i, y i * f i < 0) : ¬ CountCond val f n := by
  intro h
  have hsub : (fun z => (n : ℝ)⁻¹ • z) '' countVecs val n (n * mean val f) ⊆
      {z | 0 ≤ ∑ i, y i * z i} := by
    rintro _ ⟨_, ⟨k, rfl, hks, hkm⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, natVec]
    rw [show ∑ i, y i * ((n : ℝ)⁻¹ * (k i : ℝ)) = (n : ℝ)⁻¹ * ∑ i, y i * (k i : ℝ) by
      rw [Finset.mul_sum]; congr 1; ext i; ring]
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (hy k hks hkm)
  have hconv : Convex ℝ {z : ι → ℝ | 0 ≤ ∑ i, y i * z i} := by
    intro z1 h1 z2 h2 a b ha hb _
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [show ∑ i, y i * (a * z1 i + b * z2 i) = a * ∑ i, y i * z1 i + b * ∑ i, y i * z2 i by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext i; ring]
    positivity
  have := convexHull_min hsub hconv h
  simp only [Set.mem_ofPred_eq] at this
  linarith

/-- The condition of Lemma `nc:lem:peak` (last statement) for one set `I`: if `nμ` is not a sum
of `n` points of `I`, then `F(I) ≤ 1 - 2/n + F(J \ I)`, `J = nμ - (n-1)I`. -/
def PeakCond (n : ℕ) (F : Measure ℝ) (μ : ℝ) (I : Set ℝ) : Prop :=
  (n : ℝ) * μ ∉ sumSet (fun _ : Fin n => I) →
    (F I).toReal ≤ 1 - 2 / n +
      (F (((fun y => (n : ℝ) * μ - y) '' sumSet (fun _ : Fin (n - 1) => I)) \ I)).toReal

/-- The conditions of Lemma `nc:lem:count` for a distribution carried by `(-∞, b]`: for
`u ≤ v < μ` and `1 ≤ r ≤ n - 1` with `(n-r+1)v + (r-1)b < nμ`,
`F([u,v]) ≤ 1 - (r+1)/n + F([w,b])`, `w = (nμ - (n-r)v)/r`. -/
def CountLemCond (n : ℕ) (F : Measure ℝ) (μ b : ℝ) : Prop :=
  ∀ u v : ℝ, ∀ r : ℕ, u ≤ v → v < μ → 1 ≤ r → r ≤ n - 1 →
    ((n : ℝ) - r + 1) * v + ((r : ℝ) - 1) * b < n * μ →
    (F (Set.Icc u v)).toReal ≤ 1 - ((r : ℝ) + 1) / n +
      (F (Set.Icc (((n : ℝ) * μ - ((n : ℝ) - r) * v) / r) b)).toReal

/-- The reflected conditions, for a distribution carried by `[a, ∞)`: the conditions for the
image under `x ↦ -x`. -/
def CountLemCondRefl (n : ℕ) (F : Measure ℝ) (μ a : ℝ) : Prop :=
  CountLemCond n (F.map fun x => -x) (-μ) (-a)

/-- The condition of Lemma `nc:lem:peak` for a distribution with masses `m i / Den` at the points
`0, …, N`, `nμ = S`, and the set `I`, in natural numbers (decidable). -/
def PeakNat (N n S Den : ℕ) (m : Fin (N + 1) → ℕ) (I : Finset (Fin (N + 1))) : Prop :=
  (¬ ∃ t : Fin n → Fin (N + 1), (∀ j, t j ∈ I) ∧ ∑ j, (t j : ℕ) = S) →
    n * ∑ i ∈ I, m i ≤ (n - 2) * Den + n * ∑ i ∈ Finset.univ.filter (fun i => i ∉ I ∧
      ∃ t : Fin (n - 1) → Fin (N + 1), (∀ j, t j ∈ I) ∧ (i : ℕ) + ∑ j, (t j : ℕ) = S), m i

instance (N n S Den : ℕ) (m : Fin (N + 1) → ℕ) (I : Finset (Fin (N + 1))) :
    Decidable (PeakNat N n S Den m I) := by unfold PeakNat; infer_instance

theorem peakCond_of_nat {N n S Den : ℕ} (m : Fin (N + 1) → ℕ) (hn : 2 ≤ n) (hDen : 0 < Den)
    (μ : ℝ) (hS : (n : ℝ) * μ = S) (I : Finset (Fin (N + 1))) (h : PeakNat N n S Den m I) :
    PeakCond n (discr (ptVal N) (fun i => (m i : ℝ) / Den)) μ (I.image (ptVal N) : Set ℝ) := by
  classical
  intro hns
  have hnot : ¬ ∃ t : Fin n → Fin (N + 1), (∀ j, t j ∈ I) ∧ ∑ j, (t j : ℕ) = S := by
    rintro ⟨t, ht, hsum⟩
    apply hns
    refine ⟨fun j => ptVal N (t j), fun j => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (ht j)), ?_⟩
    rw [hS]; simp only [ptVal]; exact_mod_cast hsum
  have hineq := h hnot
  have hf0 : ∀ i, 0 ≤ (m i : ℝ) / Den := fun i => by positivity
  rw [discr_apply_toReal _ _ hf0, discr_apply_toReal _ _ hf0]
  have hI : ∀ i, ptVal N i ∈ (I.image (ptVal N) : Set ℝ) ↔ i ∈ I := by
    intro i
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, (ptVal_inj N).eq_iff,
      exists_eq_right]
  have hJ : ∀ i, ptVal N i ∈ ((fun y => (n : ℝ) * μ - y) ''
      sumSet (fun _ : Fin (n - 1) => (I.image (ptVal N) : Set ℝ))) ↔
      ∃ t : Fin (n - 1) → Fin (N + 1), (∀ j, t j ∈ I) ∧ (i : ℕ) + ∑ j, (t j : ℕ) = S := by
    intro i
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, hy⟩
      have : ∀ j, ∃ t, t ∈ I ∧ ptVal N t = x j := fun j => by
        simpa only [Finset.coe_image, Set.mem_image, Finset.mem_coe] using hx j
      choose t ht hxt using this
      refine ⟨t, ht, ?_⟩
      have e : ((i : ℕ) : ℝ) + ∑ j, ((t j : ℕ) : ℝ) = S := by
        rw [← hS]
        have : ∑ j, ((t j : ℕ) : ℝ) = ∑ j, x j := Finset.sum_congr rfl fun j _ => hxt j
        rw [this]; simp only [ptVal] at hy; linarith
      exact_mod_cast e
    · rintro ⟨t, ht, hsum⟩
      refine ⟨∑ j, ptVal N (t j), ⟨fun j => ptVal N (t j),
        fun j => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (ht j)), rfl⟩, ?_⟩
      show (n : ℝ) * μ - _ = _
      rw [hS]
      have e : ((i : ℕ) : ℝ) + ∑ j, ((t j : ℕ) : ℝ) = S := by exact_mod_cast hsum
      simp only [ptVal]; linarith
  have s1 : (∑ i, if ptVal N i ∈ (I.image (ptVal N) : Set ℝ) then (m i : ℝ) / Den else 0) =
      (∑ i ∈ I, (m i : ℝ)) / Den := by
    simp_rw [hI]
    rw [← Finset.sum_filter, Finset.sum_div]
    congr 1; ext i; simp
  have s2 : (∑ i, if ptVal N i ∈ (((fun y => (n : ℝ) * μ - y) ''
      sumSet (fun _ : Fin (n - 1) => (I.image (ptVal N) : Set ℝ))) \ (I.image (ptVal N) : Set ℝ))
        then (m i : ℝ) / Den else 0) =
      (∑ i ∈ Finset.univ.filter (fun i => i ∉ I ∧ ∃ t : Fin (n - 1) → Fin (N + 1),
        (∀ j, t j ∈ I) ∧ (i : ℕ) + ∑ j, (t j : ℕ) = S), (m i : ℝ)) / Den := by
    rw [Finset.sum_div, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.mem_sdiff, hI, hJ]
    by_cases hiI : i ∈ I <;> simp [hiI, and_comm]
  rw [s1, s2]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hDR : (0 : ℝ) < Den := by exact_mod_cast hDen
  have hc : (n : ℝ) * ∑ i ∈ I, (m i : ℝ) ≤ ((n : ℝ) - 2) * Den + n * ∑ i ∈ Finset.univ.filter
      (fun i => i ∉ I ∧ ∃ t : Fin (n - 1) → Fin (N + 1), (∀ j, t j ∈ I) ∧
        (i : ℕ) + ∑ j, (t j : ℕ) = S), (m i : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hineq
    push_cast [Nat.cast_sub hn] at this
    exact this
  rw [div_le_iff₀ hDR]
  have : (1 - 2 / (n : ℝ) + (∑ i ∈ Finset.univ.filter (fun i => i ∉ I ∧
      ∃ t : Fin (n - 1) → Fin (N + 1), (∀ j, t j ∈ I) ∧ (i : ℕ) + ∑ j, (t j : ℕ) = S),
        (m i : ℝ)) / Den) * Den * n = ((n : ℝ) - 2) * Den + n * ∑ i ∈ Finset.univ.filter
      (fun i => i ∉ I ∧ ∃ t : Fin (n - 1) → Fin (N + 1), (∀ j, t j ∈ I) ∧
        (i : ℕ) + ∑ j, (t j : ℕ) = S), (m i : ℝ) := by
    field_simp
  have hn0 : (0 : ℝ) < n := by linarith
  nlinarith

/-- The tail inequalities of Komisarski and Labuschagne (2024, Corollary 2) for three variables
with the law `F` and the sum `t = 3μ`, in the form used by the program of the paper:
`P(X > t - a₁ - a₂) ≤ P(X < a₁) + P(X < a₂)` for all `a₁, a₂`, and
`P(X > a₁) + P(X > a₂) + P(X > a₃) ≥ 1` whenever `a₁ + a₂ + a₃ < t`. -/
def TailCond3 (F : Measure ℝ) (μ : ℝ) : Prop :=
  (∀ a b : ℝ, (F (Set.Ioi (3 * μ - a - b))).toReal ≤ (F (Set.Iio a)).toReal + (F (Set.Iio b)).toReal) ∧
  (∀ a b c : ℝ, a + b + c < 3 * μ →
    1 ≤ (F (Set.Ioi a)).toReal + (F (Set.Ioi b)).toReal + (F (Set.Ioi c)).toReal)

/-- The tail inequalities and their reflections (the inequalities for `-X`). -/
def TailCond3Both (F : Measure ℝ) (μ : ℝ) : Prop :=
  TailCond3 F μ ∧ TailCond3 (F.map fun x => -x) (-μ)

lemma map_add_apply_Ioi (G : Measure ℝ) (d y : ℝ) :
    (G.map fun x => x + d) (Set.Ioi y) = G (Set.Ioi (y - d)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 1; ext x; simp [sub_lt_iff_lt_add]

lemma map_add_apply_Iio (G : Measure ℝ) (d y : ℝ) :
    (G.map fun x => x + d) (Set.Iio y) = G (Set.Iio (y - d)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  congr 1; ext x; simp [lt_sub_iff_add_lt]

lemma map_add_apply_Icc (G : Measure ℝ) (d u v : ℝ) :
    (G.map fun x => x + d) (Set.Icc u v) = G (Set.Icc (u - d) (v - d)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
  congr 1; ext x; simp [le_sub_iff_add_le, sub_le_iff_le_add]

/-- The tail inequalities are invariant under translation. -/
lemma tailCond3_shift {G : Measure ℝ} {μ : ℝ} (d : ℝ) (h : TailCond3 G μ) :
    TailCond3 (G.map fun x => x + d) (μ + d) := by
  refine ⟨fun a b => ?_, fun a b c habc => ?_⟩
  · simp only [map_add_apply_Ioi, map_add_apply_Iio]
    have := h.1 (a - d) (b - d)
    rwa [show 3 * μ - (a - d) - (b - d) = 3 * (μ + d) - a - b - d by ring] at this
  · simp only [map_add_apply_Ioi]
    exact h.2 (a - d) (b - d) (c - d) (by linarith)

/-- The conditions of Lemma `nc:lem:count` are invariant under translation. -/
lemma countLemCond_shift {n : ℕ} {G : Measure ℝ} {μ b : ℝ} (d : ℝ) (h : CountLemCond n G μ b) :
    CountLemCond n (G.map fun x => x + d) (μ + d) (b + d) := by
  intro u v r huv hvμ hr1 hrn hc
  simp only [map_add_apply_Icc]
  have hr : (0 : ℝ) < r := by exact_mod_cast hr1
  have := h (u - d) (v - d) r (by linarith) (by linarith) hr1 hrn (by nlinarith)
  rw [show ((n : ℝ) * (μ + d) - ((n : ℝ) - r) * v) / r - d =
    ((n : ℝ) * μ - ((n : ℝ) - r) * (v - d)) / r by field_simp; ring,
    show b + d - d = b by ring]
  exact this

/-- The first tail inequality in natural numbers, for masses `m i / Den` at `0, …, N` and
`3μ = S`, with integer thresholds in `[0, N]`. -/
def TailNat1 (N S : ℕ) (m : Fin (N + 1) → ℕ) : Prop :=
  ∀ c0 c1 : Fin (N + 1),
    ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => (S : ℤ) - c0 - c1 < (i : ℕ)), m i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => (i : ℕ) < c0), m i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => (i : ℕ) < c1), m i

/-- The second tail inequality in natural numbers. -/
def TailNat2 (N S Den : ℕ) (m : Fin (N + 1) → ℕ) : Prop :=
  ∀ c0 c1 c2 : Fin (N + 1), (c0 : ℕ) + c1 + c2 < S →
    Den ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => (c0 : ℕ) < i), m i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => (c1 : ℕ) < i), m i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => (c2 : ℕ) < i), m i

instance (N S : ℕ) (m : Fin (N + 1) → ℕ) : Decidable (TailNat1 N S m) := by
  unfold TailNat1; infer_instance
instance (N S Den : ℕ) (m : Fin (N + 1) → ℕ) : Decidable (TailNat2 N S Den m) := by
  unfold TailNat2; infer_instance

lemma ptMass_apply {N Den : ℕ} (m : Fin (N + 1) → ℕ) (A : Set ℝ) [DecidablePred (· ∈ A)] :
    ((discr (ptVal N) (fun i => (m i : ℝ) / Den)) A).toReal =
      (∑ i ∈ Finset.univ.filter (fun i => ptVal N i ∈ A), (m i : ℝ)) / Den := by
  rw [discr_apply_toReal _ _ (fun i => by positivity), Finset.sum_div, Finset.sum_filter]

theorem tailCond3_of_nat {N S Den : ℕ} (m : Fin (N + 1) → ℕ) (hDen : 0 < Den)
    (hsum : ∑ i, m i = Den) (μ : ℝ) (hS : 3 * μ = S) (h1 : TailNat1 N S m)
    (h2 : TailNat2 N S Den m) : TailCond3 (discr (ptVal N) (fun i => (m i : ℝ) / Den)) μ := by
  classical
  have hDR : (0 : ℝ) < Den := by exact_mod_cast hDen
  have htot : ∀ A : Set ℝ, ∀ [DecidablePred (· ∈ A)],
      (∑ i ∈ Finset.univ.filter (fun i => ptVal N i ∈ A), (m i : ℝ)) ≤ Den := by
    intro A _
    calc _ ≤ ∑ i, (m i : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => Nat.cast_nonneg _)
      _ = Den := by exact_mod_cast hsum
  have hnn : ∀ A : Set ℝ, ∀ [DecidablePred (· ∈ A)],
      0 ≤ (∑ i ∈ Finset.univ.filter (fun i => ptVal N i ∈ A), (m i : ℝ)) :=
    fun A _ => Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hall : ∀ A : Set ℝ, ∀ [DecidablePred (· ∈ A)], (∀ i, ptVal N i ∈ A) →
      (∑ i ∈ Finset.univ.filter (fun i => ptVal N i ∈ A), (m i : ℝ)) = Den := by
    intro A _ hA
    rw [Finset.filter_true_of_mem (fun i _ => hA i)]; exact_mod_cast hsum
  have hN : ∀ i : Fin (N + 1), ((i : ℕ) : ℝ) ≤ N := fun i => by
    exact_mod_cast Nat.lt_succ_iff.1 i.2
  refine ⟨fun a b => ?_, fun a b c habc => ?_⟩
  · simp only [ptMass_apply]
    rw [← add_div, div_le_div_iff_of_pos_right hDR]
    by_cases ha : (N : ℝ) < a
    · have := hall (Set.Iio a) (fun i => show ptVal N i < a from (hN i).trans_lt ha)
      linarith [htot (Set.Ioi (3 * μ - a - b)), hnn (Set.Iio b)]
    by_cases hb : (N : ℝ) < b
    · have := hall (Set.Iio b) (fun i => show ptVal N i < b from (hN i).trans_lt hb)
      linarith [htot (Set.Ioi (3 * μ - a - b)), hnn (Set.Iio a)]
    push Not at ha hb
    have hc0 : ⌈a⌉₊ < N + 1 := by
      have := Nat.ceil_le.2 ha
      omega
    have hc1 : ⌈b⌉₊ < N + 1 := by
      have := Nat.ceil_le.2 hb
      omega
    have key := h1 ⟨_, hc0⟩ ⟨_, hc1⟩
    simp only [Fin.val_mk] at key
    have keyR := (Nat.cast_le (α := ℝ)).2 key
    push_cast at keyR
    refine le_trans ?_ (le_trans keyR (le_of_eq ?_))
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioi, ptVal] at hi ⊢
        have e1 := Nat.le_ceil a
        have e2 := Nat.le_ceil b
        have : ((S : ℤ) - (⌈a⌉₊ : ℕ) - (⌈b⌉₊ : ℕ) : ℝ) < ((i : ℕ) : ℝ) := by
          push_cast; rw [← hS]; linarith
        exact_mod_cast this
      · intro i _ _; exact Nat.cast_nonneg _
    · congr 1 <;> refine Finset.sum_congr ?_ fun _ _ => rfl <;> ext i <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio, ptVal, Nat.lt_ceil]
  · simp only [ptMass_apply]
    rw [← add_div, ← add_div, le_div_iff₀ hDR, one_mul]
    -- a threshold below `0` gives the probability `1`
    have hneg : ∀ y : ℝ, y < 0 →
        (∑ i ∈ Finset.univ.filter (fun i => ptVal N i ∈ Set.Ioi y), (m i : ℝ)) = Den :=
      fun y hy => hall _ fun i => show y < ptVal N i from hy.trans_le (Nat.cast_nonneg _)
    by_cases ha : a < 0
    · rw [hneg a ha]; linarith [hnn (Set.Ioi b), hnn (Set.Ioi c)]
    by_cases hb : b < 0
    · rw [hneg b hb]; linarith [hnn (Set.Ioi a), hnn (Set.Ioi c)]
    by_cases hc : c < 0
    · rw [hneg c hc]; linarith [hnn (Set.Ioi a), hnn (Set.Ioi b)]
    push Not at ha hb hc
    -- clamp the thresholds to `min ⌊y⌋₊ N`
    have hcl : ∀ y : ℝ, 0 ≤ y → (∑ i ∈ Finset.univ.filter (fun i => ptVal N i ∈ Set.Ioi y),
        (m i : ℝ)) = ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => min ⌊y⌋₊ N < (i : ℕ)),
          (m i : ℝ) := by
      intro y hy
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioi, ptVal]
      rw [← Nat.floor_lt hy]
      have := Nat.lt_succ_iff.1 i.2
      constructor
      · intro h; exact lt_of_le_of_lt (min_le_left _ _) h
      · intro h
        rcases le_total ⌊y⌋₊ N with h' | h'
        · rwa [min_eq_left h'] at h
        · rw [min_eq_right h'] at h; omega
    rw [hcl a ha, hcl b hb, hcl c hc]
    have hlt : min ⌊a⌋₊ N + min ⌊b⌋₊ N + min ⌊c⌋₊ N < S := by
      have e : ((min ⌊a⌋₊ N + min ⌊b⌋₊ N + min ⌊c⌋₊ N : ℕ) : ℝ) < S := by
        push_cast
        have := Nat.floor_le ha; have := Nat.floor_le hb; have := Nat.floor_le hc
        have := min_le_left (⌊a⌋₊ : ℝ) N; have := min_le_left (⌊b⌋₊ : ℝ) N
        have := min_le_left (⌊c⌋₊ : ℝ) N
        rw [← hS]; linarith
      exact_mod_cast e
    have key := h2 ⟨_, Nat.lt_succ_of_le (min_le_right _ _)⟩
      ⟨_, Nat.lt_succ_of_le (min_le_right _ _)⟩ ⟨_, Nat.lt_succ_of_le (min_le_right _ _)⟩ hlt
    simp only [Fin.val_mk] at key
    have keyR := (Nat.cast_le (α := ℝ)).2 key
    push_cast at keyR
    exact keyR

/-- The mirror image: `-X` is `(N - X) - N`. -/
lemma discr_neg_eq (N : ℕ) (f : Fin (N + 1) → ℝ) :
    (discr (ptVal N) f).map (fun x => -x) =
      (discr (ptVal N) (fun i => f (Fin.rev i))).map (fun x => x + -(N : ℝ)) := by
  rw [discr_map _ _ (by fun_prop), discr_map _ _ (by fun_prop)]
  unfold discr
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.rev_rev, ptVal, Fin.val_rev]
  congr 2
  have := Nat.lt_succ_iff.1 i.2
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The conditions of Lemma `nc:lem:count` for a distribution on `0, …, N` follow from the
conditions for the integer intervals `[0, v]`. -/
theorem countLem_of_nat {N n : ℕ} (f : Fin (N + 1) → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hn : 2 ≤ n)
    (μ : ℝ)
    (h : ∀ v : ℕ, (v : ℝ) < μ → ∀ r : ℕ, 1 ≤ r → r ≤ n - 1 →
      ((n : ℝ) - r + 1) * v + ((r : ℝ) - 1) * N < n * μ →
      (∑ i : Fin (N + 1), if (i : ℕ) ≤ v then f i else 0) ≤ 1 - ((r : ℝ) + 1) / n +
        ∑ i : Fin (N + 1), if ((n : ℝ) * μ - ((n : ℝ) - r) * v) / r ≤ ((i : ℕ) : ℝ) then f i else 0) :
    CountLemCond n (discr (ptVal N) f) μ N := by
  classical
  intro u v r huv hvμ hr1 hrn hc
  rw [discr_apply_toReal _ _ hf0, discr_apply_toReal _ _ hf0]
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrn' : (r : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : r + 1 ≤ n)
  have hnR : (0 : ℝ) < n := by linarith
  have hR0 : 0 ≤ 1 - ((r : ℝ) + 1) / n := by
    rw [sub_nonneg, div_le_one hnR]; exact hrn'
  have hS0 : 0 ≤ ∑ i, if ptVal N i ∈ Set.Icc (((n : ℝ) * μ - ((n : ℝ) - r) * v) / r) (N : ℝ)
      then f i else 0 := Finset.sum_nonneg fun i _ => by split_ifs; exacts [hf0 i, le_refl _]
  by_cases hv0 : v < 0
  · have : (∑ i, if ptVal N i ∈ Set.Icc u v then f i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      intro hi; have := hi.2; have : (0 : ℝ) ≤ ptVal N i := Nat.cast_nonneg _; linarith
    rw [this]; linarith
  push Not at hv0
  set v' := ⌊v⌋₊ with hv'
  have hv'v : (v' : ℝ) ≤ v := Nat.floor_le hv0
  have hc' : ((n : ℝ) - r + 1) * v' + ((r : ℝ) - 1) * N < n * μ := by
    have : ((n : ℝ) - r + 1) * v' ≤ ((n : ℝ) - r + 1) * v :=
      mul_le_mul_of_nonneg_left hv'v (by linarith)
    linarith
  have key := h v' (by linarith) r hr1 hrn hc'
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (key.trans (add_le_add le_rfl
    (Finset.sum_le_sum fun i _ => ?_)))
  · by_cases hi : ptVal N i ∈ Set.Icc u v
    · rw [if_pos hi, if_pos (Nat.le_floor hi.2)]
    · rw [if_neg hi]; split_ifs; exacts [hf0 i, le_refl _]
  · by_cases hi : ((n : ℝ) * μ - ((n : ℝ) - r) * v') / r ≤ ((i : ℕ) : ℝ)
    · rw [if_pos hi, if_pos]
      refine ⟨le_trans ?_ hi, show ((i : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.lt_succ_iff.1 i.2⟩
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : ((n : ℝ) - r) * v' ≤ ((n : ℝ) - r) * v :=
        mul_le_mul_of_nonneg_left hv'v (by linarith)
      linarith
    · rw [if_neg hi]; split_ifs; exacts [hf0 i, le_refl _]

/-! ### The three distributions of the remark -/

/-- Masses `27·f` of the log-concave distribution on `0, 1, 2, 3`. -/
def mA : Fin 4 → ℕ := ![1, 18, 6, 2]
/-- Masses `48·f` of the second distribution, on `0, …, 6`. -/
def mB : Fin 7 → ℕ := ![1, 18, 11, 7, 6, 3, 2]
/-- Masses `39·f` of the third distribution, on `0, …, 6`. -/
def mC : Fin 7 → ℕ := ![1, 3, 3, 4, 9, 15, 4]

def fA : Fin 4 → ℝ := fun i => (mA i : ℝ) / (27 : ℕ)
def fB : Fin 7 → ℝ := fun i => (mB i : ℝ) / (48 : ℕ)
def fC : Fin 7 → ℝ := fun i => (mC i : ℝ) / (39 : ℕ)

/-- The distribution with masses `(1, 18, 6, 2)/27` on `0, 1, 2, 3`. -/
def FA : Measure ℝ := discr (ptVal 3) fA
/-- The distribution with masses `(1, 18, 11, 7, 6, 3, 2)/48` on `0, …, 6`. -/
def FB : Measure ℝ := discr (ptVal 6) fB
/-- The distribution with masses `(1, 3, 3, 4, 9, 15, 4)/39` on `0, …, 6`. -/
def FC : Measure ℝ := discr (ptVal 6) fC

lemma fA_pos (i : Fin 4) : 0 < fA i := by fin_cases i <;> simp [fA, mA] <;> norm_num
lemma fB_pos (i : Fin 7) : 0 < fB i := by fin_cases i <;> simp [fB, mB] <;> norm_num
lemma fC_pos (i : Fin 7) : 0 < fC i := by fin_cases i <;> simp [fC, mC] <;> norm_num
lemma fA_sum : ∑ i, fA i = 1 := by simp [fA, mA, Fin.sum_univ_succ]; norm_num
lemma fB_sum : ∑ i, fB i = 1 := by simp [fB, mB, Fin.sum_univ_succ]; norm_num
lemma fC_sum : ∑ i, fC i = 1 := by simp [fC, mC, Fin.sum_univ_succ]; norm_num
lemma meanA : mean (ptVal 3) fA = 4 / 3 := by
  simp [mean, ptVal, fA, mA, Fin.sum_univ_succ]; norm_num
lemma meanB : mean (ptVal 6) fB = 7 / 3 := by
  simp [mean, ptVal, fB, mB, Fin.sum_univ_succ]; norm_num
lemma meanC : mean (ptVal 6) fC = 4 := by
  simp [mean, ptVal, fC, mC, Fin.sum_univ_succ]; norm_num

/-- The first distribution is log-concave, and the second and third are unimodal (with modes `1`
and `5`). -/
theorem shapes : (mA 1 ^ 2 ≥ mA 0 * mA 2 ∧ mA 2 ^ 2 ≥ mA 1 * mA 3) ∧
    (∀ i j : Fin 7, i ≤ j → j ≤ 1 → mB i ≤ mB j) ∧ (∀ i j : Fin 7, 1 ≤ i → i ≤ j → mB j ≤ mB i) ∧
    (∀ i j : Fin 7, i ≤ j → j ≤ 5 → mC i ≤ mC j) ∧ (∀ i j : Fin 7, 5 ≤ i → i ≤ j → mC j ≤ mC i) := by
  decide

/-- **The log-concave distribution** `(1, 18, 6, 2)/27` on `0, 1, 2, 3`, `n = 3`, `3μ = 4`:
relation (`nc:eq:cx`) holds. -/
theorem cxA : CxCond 3 FA (4 / 3) := by
  refine cx_of_coupling (ptVal 3) fA fA_pos 3 (4 / 3)
    (fun i j => ((![![0, 1, 0, 1], ![0, 21, 12, 3], ![0, 12, 0, 0], ![2, 2, 0, 0]] :
      Fin 4 → Fin 4 → ℕ) i j : ℝ) / 54) (fun i j => by positivity) ?_ ?_ ?_ <;>
  intro i <;> fin_cases i <;> simp [Fin.sum_univ_succ, fA, mA, ptVal] <;> norm_num

/-- It violates the condition of Lemma `nc:lem:peak` for `I = {1}`. -/
theorem not_peakA : ¬ PeakCond 3 FA (4 / 3) {1} := by
  classical
  have hsum : ∀ m : ℕ, sumSet (fun _ : Fin m => ({1} : Set ℝ)) = {(m : ℝ)} := by
    intro m; ext y
    simp only [sumSet, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; simp [hx]
    · rintro rfl; exact ⟨fun _ => 1, fun _ => rfl, by simp⟩
  intro h
  have h' := h (by rw [hsum]; norm_num)
  rw [hsum] at h'
  simp only [Set.image_singleton] at h'
  rw [FA, discr_apply_toReal _ _ (fun i => (fA_pos i).le),
    discr_apply_toReal _ _ (fun i => (fA_pos i).le)] at h'
  simp [Fin.sum_univ_succ, fA, mA, ptVal] at h'
  norm_num at h'

/-- It is not `3`-completely mixable (under Lemma `lt:lem:count`): every count vector has
`k₃ ≤ k₀`, while `f₃ > f₀`. -/
theorem not_mixA (hc : H_lt_lem_count) : ¬ CompletelyMixable 3 FA := by
  rw [FA, hc (Fin 4) (ptVal 3) fA (ptVal_inj 3) (fun i => (fA_pos i).le) fA_sum 3 (by norm_num)]
  refine not_countCond_of_linear ![1, 0, 0, -1] ?_ ?_
  · intro k hk hm
    rw [meanA] at hm
    rw [Fin.sum_univ_four] at hk hm ⊢
    simp [ptVal] at hm
    have e2 : k 1 + 2 * k 2 + 3 * k 3 = 4 := by
      have : ((k 1 + 2 * k 2 + 3 * k 3 : ℕ) : ℝ) = 4 := by
        push_cast; norm_num at hm; linarith
      exact_mod_cast this
    have h : k 3 ≤ k 0 := by
      have : k 0 ≤ 3 := by omega
      have : k 3 ≤ 3 := by omega
      interval_cases (k 0) <;> interval_cases (k 3) <;> omega
    have h' : ((k 3 : ℕ) : ℝ) ≤ ((k 0 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    simp; linarith
  · simp [Fin.sum_univ_succ, fA, mA]; norm_num

/-- Masses of the mirror images `6 - X`. -/
def mBr : Fin 7 → ℕ := ![2, 3, 6, 7, 11, 18, 1]
def mCr : Fin 7 → ℕ := ![4, 15, 9, 4, 3, 3, 1]

lemma fB_rev : (fun i => fB (Fin.rev i)) = fun i => (mBr i : ℝ) / (48 : ℕ) := by
  funext i; fin_cases i <;> rfl
lemma fC_rev : (fun i => fC (Fin.rev i)) = fun i => (mCr i : ℝ) / (39 : ℕ) := by
  funext i; fin_cases i <;> rfl

theorem cxB : CxCond 3 FB (7 / 3) := by
  refine cx_of_coupling (ptVal 6) fB fB_pos 3 (7 / 3)
    (fun i j => ((![![0, 1, 0, 0, 0, 0, 1], ![0, 16, 0, 0, 11, 6, 3], ![0, 5, 2, 14, 1, 0, 0],
      ![0, 0, 14, 0, 0, 0, 0], ![0, 6, 6, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0],
      ![2, 2, 0, 0, 0, 0, 0]] : Fin 7 → Fin 7 → ℕ) i j : ℝ) / 96) (fun i j => by positivity)
    ?_ ?_ ?_ <;>
  intro i <;> fin_cases i <;> simp [Fin.sum_univ_succ, fB, mB, ptVal] <;> norm_num

theorem cxC : CxCond 3 FC 4 := by
  refine cx_of_coupling (ptVal 6) fC fC_pos 3 4
    (fun i j => ((![![0, 0, 0, 0, 0, 0, 40], ![0, 12, 0, 0, 0, 0, 108],
      ![0, 3, 0, 0, 0, 105, 12], ![4, 15, 0, 0, 0, 141, 0], ![0, 90, 0, 0, 0, 270, 0],
      ![36, 0, 120, 0, 360, 84, 0], ![0, 0, 0, 160, 0, 0, 0]] : Fin 7 → Fin 7 → ℕ) i j : ℝ) / 1560)
    (fun i j => by positivity) ?_ ?_ ?_ <;>
  intro i <;> fin_cases i <;> simp [Fin.sum_univ_succ, fC, mC, ptVal] <;> norm_num

theorem peakNatB : ∀ I : Finset (Fin 7), PeakNat 6 3 7 48 mB I := by decide +kernel
theorem peakNatC : ∀ I : Finset (Fin 7), PeakNat 6 3 12 39 mC I := by decide +kernel

/-- The second distribution satisfies the condition of Lemma `nc:lem:peak` for every subset `I` of
its support. -/
theorem peakB (I : Finset (Fin 7)) : PeakCond 3 FB (7 / 3) (I.image (ptVal 6) : Set ℝ) :=
  peakCond_of_nat mB (by norm_num) (by norm_num) _ (by norm_num) I (peakNatB I)

/-- So does the third. -/
theorem peakC (I : Finset (Fin 7)) : PeakCond 3 FC 4 (I.image (ptVal 6) : Set ℝ) :=
  peakCond_of_nat mC (by norm_num) (by norm_num) _ (by norm_num) I (peakNatC I)

theorem tailB : TailCond3Both FB (7 / 3) := by
  refine ⟨tailCond3_of_nat (S := 7) (Den := 48) mB (by norm_num) (by decide) _ (by norm_num) (by decide +kernel)
    (by decide +kernel), ?_⟩
  rw [FB, discr_neg_eq, fB_rev]
  have h := tailCond3_shift (-((6 : ℕ) : ℝ)) (tailCond3_of_nat (S := 11) (Den := 48) mBr (by norm_num) (by decide)
    (11 / 3) (by norm_num) (by decide +kernel) (by decide +kernel))
  convert h using 1; norm_num

theorem tailC : TailCond3Both FC 4 := by
  refine ⟨tailCond3_of_nat (S := 12) (Den := 39) mC (by norm_num) (by decide) _ (by norm_num) (by decide +kernel)
    (by decide +kernel), ?_⟩
  rw [FC, discr_neg_eq, fC_rev]
  have h := tailCond3_shift (-((6 : ℕ) : ℝ)) (tailCond3_of_nat (S := 6) (Den := 39) mCr (by norm_num) (by decide)
    2 (by norm_num) (by decide +kernel) (by decide +kernel))
  convert h using 1; norm_num

/-- The second distribution violates the reflected condition of Lemma `nc:lem:count` with `r = 2`
for the point `6`. -/
theorem not_countReflB : ¬ CountLemCondRefl 3 FB (7 / 3) 0 := by
  classical
  intro h
  have h' := h (-6) (-6) 2 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [FB, discr_map _ _ (by fun_prop), discr_apply_toReal _ _ (fun i => (fB_pos i).le),
    discr_apply_toReal _ _ (fun i => (fB_pos i).le)] at h'
  simp [Fin.sum_univ_succ, fB, mB, ptVal] at h'
  norm_num at h'

/-- The third distribution satisfies the conditions of Lemma `nc:lem:count` and the reflected
ones. -/
theorem countC : CountLemCond 3 FC 4 6 ∧ CountLemCondRefl 3 FC 4 0 := by
  constructor
  · have e : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [e, FC]
    apply countLem_of_nat fC (fun i => (fC_pos i).le) (by norm_num) 4
    intro v hv r hr1 hr2 hc
    have hv' : v < 4 := by exact_mod_cast hv
    interval_cases v <;> interval_cases r <;> simp [Fin.sum_univ_succ, fC, mC] at hc ⊢ <;>
      (try norm_num at hc) <;> (try norm_num)
  · unfold CountLemCondRefl
    rw [FC, discr_neg_eq, fC_rev]
    have h0 : CountLemCond 3 (discr (ptVal 6) (fun i => (mCr i : ℝ) / (39 : ℕ))) 2
        ((6 : ℕ) : ℝ) := by
      apply countLem_of_nat _ (fun i => by positivity) (by norm_num) 2
      intro v hv r hr1 hr2 hc
      have hv' : v < 2 := by exact_mod_cast hv
      interval_cases v <;> interval_cases r <;> simp [Fin.sum_univ_succ, mCr] at hc ⊢ <;>
        (try norm_num at hc) <;> (try norm_num)
    have h := countLemCond_shift (-((6 : ℕ) : ℝ)) h0
    convert h using 1 <;> norm_num

/-- Every count vector of the second distribution (`n = 3`, sum `7`) has `k₀ ≥ k₆`, while
`f₆ > f₀`; so it is not `3`-completely mixable (under Lemma `lt:lem:count`). -/
theorem not_mixB (hc : H_lt_lem_count) : ¬ CompletelyMixable 3 FB := by
  rw [FB, hc (Fin 7) (ptVal 6) fB (ptVal_inj 6) (fun i => (fB_pos i).le) fB_sum 3 (by norm_num)]
  refine not_countCond_of_linear ![1, 0, 0, 0, 0, 0, -1] ?_ ?_
  · intro k hk hm
    rw [meanB] at hm
    rw [Fin.sum_univ_seven] at hk hm ⊢
    simp [ptVal] at hm
    have e2 : k 1 + 2 * k 2 + 3 * k 3 + 4 * k 4 + 5 * k 5 + 6 * k 6 = 7 := by
      have : ((k 1 + 2 * k 2 + 3 * k 3 + 4 * k 4 + 5 * k 5 + 6 * k 6 : ℕ) : ℝ) = 7 := by
        push_cast; norm_num at hm; linarith
      exact_mod_cast this
    have h : k 6 ≤ k 0 := by
      have : k 0 ≤ 3 := by omega
      have : k 6 ≤ 3 := by omega
      interval_cases (k 0) <;> interval_cases (k 6) <;> omega
    have h' : ((k 6 : ℕ) : ℝ) ≤ ((k 0 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    simp; linarith
  · simp [Fin.sum_univ_succ, fB, mB]; norm_num

/-- **The third distribution is not `3`-completely mixable** (under Lemma `lt:lem:count`): every
count vector (sum `12`) has `k₆ ≥ 2k₀ + k₁`, while `f₆ < 2f₀ + f₁`. -/
theorem not_mixC (hc : H_lt_lem_count) : ¬ CompletelyMixable 3 FC := by
  rw [FC, hc (Fin 7) (ptVal 6) fC (ptVal_inj 6) (fun i => (fC_pos i).le) fC_sum 3 (by norm_num)]
  refine not_countCond_of_linear ![-2, -1, 0, 0, 0, 0, 1] ?_ ?_
  · intro k hk hm
    rw [meanC] at hm
    rw [Fin.sum_univ_seven] at hk hm ⊢
    simp [ptVal] at hm
    have e2 : k 1 + 2 * k 2 + 3 * k 3 + 4 * k 4 + 5 * k 5 + 6 * k 6 = 12 := by
      have : ((k 1 + 2 * k 2 + 3 * k 3 + 4 * k 4 + 5 * k 5 + 6 * k 6 : ℕ) : ℝ) = 12 := by
        push_cast; norm_num at hm; linarith
      exact_mod_cast this
    have h : 2 * k 0 + k 1 ≤ k 6 := by
      have : k 0 ≤ 3 := by omega
      have : k 1 ≤ 3 := by omega
      have : k 6 ≤ 3 := by omega
      interval_cases (k 0) <;> interval_cases (k 1) <;> interval_cases (k 6) <;> omega
    have h' : ((2 * k 0 + k 1 : ℕ) : ℝ) ≤ ((k 6 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    simp; linarith
  · simp [Fin.sum_univ_succ, fC, mC]; norm_num

/-- **Remark `lt:rem:necessary`**, summary: the third distribution satisfies relation
(`nc:eq:cx`), the condition of Lemma `nc:lem:peak` for every subset of its support, the
conditions of Lemma `nc:lem:count` and their reflections, and the tail inequalities and their
reflections, and it is not `3`-completely mixable. -/
theorem remark_necessary (hc : H_lt_lem_count) :
    CxCond 3 FC 4 ∧ (∀ I : Finset (Fin 7), PeakCond 3 FC 4 (I.image (ptVal 6) : Set ℝ)) ∧
      CountLemCond 3 FC 4 6 ∧ CountLemCondRefl 3 FC 4 0 ∧ TailCond3Both FC 4 ∧
      ¬ CompletelyMixable 3 FC :=
  ⟨cxC, peakC, countC.1, countC.2, tailC, not_mixC hc⟩

end Remark

end Mixes.LatticeLarge
