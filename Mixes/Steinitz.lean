import Mixes.AsymThm

/-!
# The Steinitz lemma with the constant of Grinberg and Sevastyanov (1980)

* `steinitz_normed`: in any finite-dimensional real normed space `E`, vectors `v_1, …, v_N` with
  `‖v_i‖ ≤ ℓ` (`ℓ ≥ 0`) and sum `0` admit an ordering whose partial sums all have norm
  `≤ (dim E) ℓ`. Proof: induction on `N` with weights `λ ∈ [0,1]^N`, `∑ λ = N - dim E`,
  `∑ λ_i v_i = 0`; the vertex step moves along a kernel direction of `δ ↦ (∑ δ, ∑ δ_i v_i)` on
  the fractional coordinates (`exists_kernel`, `move`, `exists_zero`, `reduce`).
* `steinitz_nonneg : H_steinitz_nonneg` (Euclidean `ℝ^d`, constant `d`), `steinitz_pos`.
* **Finding** `not_H_steinitz : ¬ AsymThm.H_steinitz`: the hypothesis of `AsymThm` omits `0 ≤ ℓ`
  and fails for `N = 0`, `ℓ < 0`, `d ≥ 1`. Hence the chain of `AsymThm` from `H_steinitz` is
  rerun here (primed copies) from `H_steinitz_nonneg`, giving unconditionally
  `lem_conc_c_uncond` (Lemma `as:lem:conc` (c)), `couplingBound_all`, and
  `thm_window_all : ∀ d, AsymThm.ThmWindow d` (Theorem `as:thm:window`).
-/

namespace Mixes.Steinitz


section Core
open Finset Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fractional coordinates of a weight vector. -/
noncomputable def frac (μ : ι → ℝ) : Finset ι := univ.filter (fun i => 0 < μ i ∧ μ i < 1)

lemma card_frac_ge (μ : ι → ℝ) (d : ℕ) (hpos : ∀ i, 0 < μ i) (hle : ∀ i, μ i ≤ 1)
    (hsum : ∑ i, μ i = (Fintype.card ι : ℝ) - d - 1) : d + 2 ≤ (frac μ).card := by
  have h1 : ∑ i, (1 - μ i) = (d : ℝ) + 1 := by
    rw [Finset.sum_sub_distrib, hsum]; simp; ring
  have h2 : ∑ i, (1 - μ i) = ∑ i ∈ frac μ, (1 - μ i) := by
    symm; apply Finset.sum_subset (subset_univ _)
    intro i _ hi
    simp only [frac, mem_filter, mem_univ, true_and, not_and, not_lt] at hi
    have := hi (hpos i); linarith [hle i]
  rcases (frac μ).eq_empty_or_nonempty with he | hne
  · rw [h2, he, sum_empty] at h1
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  · have h3 : ∑ i ∈ frac μ, (1 - μ i) < ∑ i ∈ frac μ, (1:ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hne
      intro i hi; simp only [frac, mem_filter] at hi; linarith [hi.2.1]
    rw [sum_const, nsmul_eq_mul, mul_one] at h3
    have h4 : ((d + 1 : ℕ) : ℝ) < (frac μ).card := by push_cast; linarith
    have : d + 1 < (frac μ).card := by exact_mod_cast h4
    omega

lemma exists_kernel (v : ι → E) (F : Finset ι) (hF : finrank ℝ E + 2 ≤ F.card) :
    ∃ δ : ι → ℝ, δ ≠ 0 ∧ (∀ i, i ∉ F → δ i = 0) ∧ ∑ i, δ i = 0 ∧ ∑ i, δ i • v i = 0 := by
  let ext : (F → ℝ) → ι → ℝ := fun δ i => if h : i ∈ F then δ ⟨i, h⟩ else 0
  let T : (F → ℝ) →ₗ[ℝ] ℝ × E :=
    { toFun := fun δ => (∑ i, ext δ i, ∑ i, ext δ i • v i)
      map_add' := by
        intro a b
        simp only [ext, Prod.mk_add_mk, ← sum_add_distrib, ← add_smul]
        congr 1 <;> refine sum_congr rfl fun i _ => ?_ <;> split_ifs <;> simp
      map_smul' := by
        intro c a
        simp only [ext, RingHom.id_apply, Prod.smul_mk, smul_sum, smul_smul]
        congr 1 <;> refine sum_congr rfl fun i _ => ?_ <;> split_ifs <;> simp }
  have hlt : finrank ℝ (ℝ × E) < finrank ℝ (F → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]; omega
  obtain ⟨δ, hδT, hδ0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hlt)
  rw [LinearMap.mem_ker] at hδT
  have hT1 := congrArg Prod.fst hδT
  have hT2 := congrArg Prod.snd hδT
  refine ⟨ext δ, ?_, ?_, hT1, hT2⟩
  · intro h
    apply hδ0
    funext x
    have := congrFun h x.1
    simpa [ext, x.2] using this
  · intro i hi; simp [ext, hi]


lemma move (v : ι → E) (μ : ι → ℝ) (h01 : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (δ : ι → ℝ) (hδ : δ ≠ 0)
    (hδF : ∀ i, i ∉ frac μ → δ i = 0) (hs : ∑ i, δ i = 0) (hv : ∑ i, δ i • v i = 0) :
    ∃ μ' : ι → ℝ, (∀ i, 0 ≤ μ' i ∧ μ' i ≤ 1) ∧ ∑ i, μ' i = ∑ i, μ i ∧
      ∑ i, μ' i • v i = ∑ i, μ i • v i ∧ (frac μ').card < (frac μ).card := by
  classical
  have hF : ∀ i, δ i ≠ 0 → 0 < μ i ∧ μ i < 1 := by
    intro i hi
    by_contra h
    exact hi (hδF i (by simpa [frac] using h))
  set S := (frac μ).filter (fun i => δ i ≠ 0) with hS
  obtain ⟨i1, hi1⟩ := Function.ne_iff.1 hδ
  have hne : S.Nonempty := ⟨i1, by
    simp only [hS, frac, mem_filter, mem_univ, true_and]; exact ⟨hF i1 hi1, hi1⟩⟩
  set r : ι → ℝ := fun i => if 0 < δ i then (1 - μ i) / δ i else μ i / (-δ i) with hr
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image r hne
  have hmemS : ∀ i, δ i ≠ 0 → i ∈ S := by
    intro i hi; simp only [hS, frac, mem_filter, mem_univ, true_and]; exact ⟨hF i hi, hi⟩
  have hδi0 : δ i0 ≠ 0 := (mem_filter.1 hi0S).2
  set t := r i0 with ht
  have hrd : ∀ i, δ i ≠ 0 → r i * δ i = if 0 < δ i then 1 - μ i else - μ i := by
    intro i hi
    simp only [hr]
    split_ifs with h
    · field_simp
    · field_simp
  have hbd : ∀ i, 0 ≤ μ i + t * δ i ∧ μ i + t * δ i ≤ 1 := by
    intro i
    by_cases hi : δ i = 0
    · simp [hi, h01 i]
    have htr : t ≤ r i := hmin i (hmemS i hi)
    have h1 := hrd i hi
    have hFi := hF i hi
    have ht0 : 0 ≤ t := by
      have := hrd i0 hδi0
      have hF0 := hF i0 hδi0
      simp only [ht, hr]
      split_ifs with h
      · exact div_nonneg (by linarith) h.le
      · exact div_nonneg hF0.1.le (by push Not at h; exact neg_nonneg.2 h)
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · rw [if_neg (by linarith)] at h1
      constructor
      · nlinarith
      · nlinarith
    · rw [if_pos hpos] at h1
      constructor
      · nlinarith
      · nlinarith
  refine ⟨fun i => μ i + t * δ i, hbd, ?_, ?_, ?_⟩
  · simp [sum_add_distrib, ← mul_sum, hs]
  · simp [add_smul, sum_add_distrib, mul_smul, ← smul_sum, hv]
  · apply lt_of_le_of_lt (card_le_card (t := (frac μ).erase i0) ?_)
    · exact card_erase_lt_of_mem (mem_filter.1 hi0S).1
    intro i hi
    simp only [frac, mem_filter, mem_univ, true_and] at hi
    rw [mem_erase]
    by_cases hδi : δ i = 0
    · rw [hδi, mul_zero, add_zero] at hi
      refine ⟨?_, by simpa [frac] using hi⟩
      intro h; rw [h] at hδi; exact hδi0 hδi
    · refine ⟨?_, by simpa [frac] using hF i hδi⟩
      intro h
      rw [h] at hi
      have h1 := hrd i0 hδi0
      split_ifs at h1 <;> rw [← ht] at h1 <;> rcases hi with ⟨h2, h3⟩ <;> linarith

lemma exists_zero (v : ι → E) (n : ℕ) : ∀ μ : ι → ℝ, (∀ i, 0 ≤ μ i ∧ μ i ≤ 1) →
    ∑ i, μ i = (Fintype.card ι : ℝ) - finrank ℝ E - 1 → ∑ i, μ i • v i = 0 →
    (frac μ).card ≤ n → ∃ μ' : ι → ℝ, (∀ i, 0 ≤ μ' i ∧ μ' i ≤ 1) ∧
      ∑ i, μ' i = (Fintype.card ι : ℝ) - finrank ℝ E - 1 ∧ ∑ i, μ' i • v i = 0 ∧
      ∃ j, μ' j = 0 := by
  induction n with
  | zero =>
    intro μ h01 hs hv hc
    by_cases hz : ∃ j, μ j = 0
    · exact ⟨μ, h01, hs, hv, hz⟩
    push Not at hz
    have := card_frac_ge μ (finrank ℝ E) (fun i => lt_of_le_of_ne (h01 i).1 (hz i).symm)
      (fun i => (h01 i).2) hs
    omega
  | succ n ih =>
    intro μ h01 hs hv hc
    by_cases hz : ∃ j, μ j = 0
    · exact ⟨μ, h01, hs, hv, hz⟩
    push Not at hz
    have hcard := card_frac_ge μ (finrank ℝ E) (fun i => lt_of_le_of_ne (h01 i).1 (hz i).symm)
      (fun i => (h01 i).2) hs
    obtain ⟨δ, hδ, hδF, hδs, hδv⟩ := exists_kernel v (frac μ) hcard
    obtain ⟨μ', h01', hs', hv', hc'⟩ := move v μ h01 δ hδ hδF hδs hδv
    exact ih μ' h01' (hs'.trans hs) (hv'.trans hv) (by omega)

lemma reduce (v : ι → E) (lam : ι → ℝ) (h01 : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1)
    (hs : ∑ i, lam i = (Fintype.card ι : ℝ) - finrank ℝ E) (hv : ∑ i, lam i • v i = 0)
    (hk : finrank ℝ E + 1 ≤ Fintype.card ι) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i ∧ μ i ≤ 1) ∧
      ∑ i, μ i = (Fintype.card ι : ℝ) - finrank ℝ E - 1 ∧ ∑ i, μ i • v i = 0 ∧
      ∃ j, μ j = 0 := by
  have hk' : (1 : ℝ) ≤ (Fintype.card ι : ℝ) - finrank ℝ E := by
    have : ((finrank ℝ E + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    push_cast at this; linarith
  set c := ((Fintype.card ι : ℝ) - finrank ℝ E - 1) / ((Fintype.card ι : ℝ) - finrank ℝ E)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hc1 : c ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  refine exists_zero v (frac (fun i => c * lam i)).card (fun i => c * lam i) ?_ ?_ ?_ le_rfl
  · intro i; constructor
    · exact mul_nonneg hc0 (h01 i).1
    · calc c * lam i ≤ 1 * 1 := mul_le_mul hc1 (h01 i).2 (h01 i).1 zero_le_one
        _ = 1 := one_mul 1
  · rw [← mul_sum, hs]; simp only [c]; field_simp
  · simp [mul_smul, ← smul_sum, hv]

end Core

section Main
open Finset Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The induction hypothesis of the Grinberg–Sevastyanov argument: either `N ≤ dim E`, or there
are weights in `[0,1]` with sum `N - dim E` and weighted sum `0`. -/
def WeightHyp (N : ℕ) (v : Fin N → E) : Prop :=
  N ≤ finrank ℝ E ∨ ∃ lam : Fin N → ℝ, (∀ i, 0 ≤ lam i ∧ lam i ≤ 1) ∧
    ∑ i, lam i = (N : ℝ) - finrank ℝ E ∧ ∑ i, lam i • v i = 0

lemma step_data {N : ℕ} (v : Fin (N + 1) → E) {ℓ : ℝ} (hv : ∀ i, ‖v i‖ ≤ ℓ)
    (h : WeightHyp (N + 1) v) :
    ∃ j : Fin (N + 1), WeightHyp N (fun i => v (j.succAbove i)) ∧
      ‖∑ i, v i‖ ≤ finrank ℝ E * ℓ := by
  have hℓ : 0 ≤ ℓ := le_trans (norm_nonneg _) (hv 0)
  by_cases hk : N + 1 ≤ finrank ℝ E
  · refine ⟨Fin.last N, Or.inl (by omega), ?_⟩
    have hk' : ((N + 1 : ℕ) : ℝ) ≤ finrank ℝ E := by exact_mod_cast hk
    calc ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (N + 1), ℓ := sum_le_sum fun i _ => hv i
      _ = ((N + 1 : ℕ) : ℝ) * ℓ := by simp
      _ ≤ finrank ℝ E * ℓ := mul_le_mul_of_nonneg_right hk' hℓ
  · obtain ⟨lam, h01, hs, hlv⟩ := h.resolve_left hk
    have hk' : finrank ℝ E + 1 ≤ Fintype.card (Fin (N + 1)) := by simp; omega
    obtain ⟨μ, hμ01, hμs, hμv, j, hj⟩ := reduce v lam h01 (by simpa using hs) hlv hk'
    refine ⟨j, Or.inr ⟨fun i => μ (j.succAbove i), fun i => hμ01 _, ?_, ?_⟩, ?_⟩
    · have := Fin.sum_univ_succAbove μ j
      rw [hj, zero_add] at this
      rw [← this, hμs]; simp; ring
    · have := Fin.sum_univ_succAbove (fun i => μ i • v i) j
      simp only [hj, zero_smul, zero_add] at this
      rw [← this, hμv]
    · have heq : ∑ i, v i = ∑ i, (1 - lam i) • v i := by
        simp [sub_smul, sum_sub_distrib, hlv]
      rw [heq]
      calc ‖∑ i, (1 - lam i) • v i‖ ≤ ∑ i, ‖(1 - lam i) • v i‖ := norm_sum_le _ _
        _ ≤ ∑ i, (1 - lam i) * ℓ := by
            refine sum_le_sum fun i _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (by linarith [(h01 i).2])]
            exact mul_le_mul_of_nonneg_left (hv i) (by linarith [(h01 i).2])
        _ = finrank ℝ E * ℓ := by rw [← sum_mul, sum_sub_distrib, hs]; simp

lemma perm_extend {N : ℕ} (v : Fin (N + 1) → E) (j : Fin (N + 1)) (π' : Equiv.Perm (Fin N)) :
    ∃ π : Equiv.Perm (Fin (N + 1)), ∀ J : ℕ,
      (∑ i : Fin (N + 1), if (i : ℕ) < J then v (π i) else 0) =
        (∑ i : Fin N, if (i : ℕ) < J then v (j.succAbove (π' i)) else 0) +
          if N < J then v j else 0 := by
  refine ⟨finSuccEquivLast.trans ((Equiv.optionCongr π').trans (finSuccEquiv' j).symm),
    fun J => ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp

lemma gen {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : ∀ (N : ℕ) (v : Fin N → E), (∀ i, ‖v i‖ ≤ ℓ) →
    WeightHyp N v → ∃ π : Equiv.Perm (Fin N), ∀ J : ℕ,
      ‖∑ i : Fin N, if (i : ℕ) < J then v (π i) else 0‖ ≤ finrank ℝ E * ℓ := by
  intro N
  induction N with
  | zero => intro v _ _; exact ⟨1, fun J => by simp; positivity⟩
  | succ N ih =>
    intro v hv h
    obtain ⟨j, hj, hfull⟩ := step_data v hv h
    obtain ⟨π', hπ'⟩ := ih _ (fun i => hv _) hj
    obtain ⟨π, hπ⟩ := perm_extend v j π'
    refine ⟨π, fun J => ?_⟩
    by_cases hJ : N < J
    · have : (∑ i : Fin (N + 1), if (i : ℕ) < J then v (π i) else 0) = ∑ i, v i := by
        rw [← Equiv.sum_comp π v]
        exact sum_congr rfl fun i _ => if_pos (by omega)
      rw [this]; exact hfull
    · rw [hπ J, if_neg hJ, add_zero]; exact hπ' J

/-- **Steinitz lemma with the constant of Grinberg–Sevastyanov (1980)**, in any finite-dimensional
real normed space `E`: vectors of norm at most `ℓ` (with `ℓ ≥ 0`) and sum `0` can be ordered so
that every partial sum has norm at most `(dim E) ℓ`. -/
theorem steinitz_normed {N : ℕ} (v : Fin N → E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hv : ∀ i, ‖v i‖ ≤ ℓ)
    (h0 : ∑ i, v i = 0) : ∃ π : Equiv.Perm (Fin N), ∀ J : ℕ,
      ‖∑ i : Fin N, if (i : ℕ) < J then v (π i) else 0‖ ≤ finrank ℝ E * ℓ := by
  refine gen hℓ N v hv ?_
  by_cases hk : N ≤ finrank ℝ E
  · exact Or.inl hk
  right
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (finrank ℝ E : ℝ) ≤ N := by exact_mod_cast (show finrank ℝ E ≤ N by omega)
  refine ⟨fun _ => ((N : ℝ) - finrank ℝ E) / N, fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact div_nonneg (by linarith) hN.le
  · rw [div_le_one hN]; linarith [(Nat.cast_nonneg (finrank ℝ E) : (0:ℝ) ≤ _)]
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · rw [← smul_sum, h0, smul_zero]

end Main

/-! ### The statement `AsymThm.H_steinitz` and its corrected form -/

/-- **Finding**: `AsymThm.H_steinitz` is false as stated, because it allows `ℓ < 0`: for `N = 0`
the hypotheses on the vectors are empty, while the conclusion asks `‖0‖ ≤ d ℓ < 0`. -/
theorem not_H_steinitz : ¬ Mixes.AsymThm.H_steinitz := by
  intro h
  obtain ⟨π, hπ⟩ := h 1 0 (fun i => i.elim0) (-1) (fun i => i.elim0) (by simp)
  have := hπ 0
  norm_num at this

/-- `AsymThm.H_steinitz` with the missing hypothesis `0 ≤ ℓ` (automatic when `N ≥ 1`). -/
def H_steinitz_nonneg : Prop :=
  ∀ (d N : ℕ) (v : Fin N → EuclideanSpace ℝ (Fin d)) (ℓ : ℝ), 0 ≤ ℓ → (∀ i, ‖v i‖ ≤ ℓ) →
    ∑ i, v i = 0 → ∃ π : Equiv.Perm (Fin N), ∀ J : ℕ,
      ‖∑ i : Fin N, if (i : ℕ) < J then v (π i) else 0‖ ≤ d * ℓ

/-- **Steinitz lemma, Grinberg–Sevastyanov constant**, Euclidean `ℝ^d`, with `0 ≤ ℓ`. -/
theorem steinitz_nonneg : H_steinitz_nonneg := by
  intro d N v ℓ hℓ hv h0
  have := steinitz_normed v hℓ hv h0
  simpa [finrank_euclideanSpace_fin] using this

/-- `AsymThm.H_steinitz` holds for `N ≥ 1` (the only case where it can hold for all `ℓ`). -/
theorem steinitz_pos (d N : ℕ) (hN : 0 < N) (v : Fin N → EuclideanSpace ℝ (Fin d)) (ℓ : ℝ)
    (hv : ∀ i, ‖v i‖ ≤ ℓ) (h0 : ∑ i, v i = 0) : ∃ π : Equiv.Perm (Fin N), ∀ J : ℕ,
      ‖∑ i : Fin N, if (i : ℕ) < J then v (π i) else 0‖ ≤ d * ℓ :=
  steinitz_nonneg d N v ℓ (le_trans (norm_nonneg _) (hv ⟨0, hN⟩)) hv h0

/-! ### The chain of `AsymThm` from `H_steinitz` to `ThmWindow`, rerun from `H_steinitz_nonneg`

Verbatim copies of `AsymThm.disc_coupling`, `weighted_coupling`, `eps_coupling`, `lem_conc_c`,
`couplingBound_of_steinitz`, `thm_window` (primed names), with `H_steinitz` replaced by
`H_steinitz_nonneg`; the only change of proof is the argument `0 ≤ ℓ` in `disc_coupling'`. -/

open MeasureTheory ProbabilityTheory Set Mixes.AsymThm
open scoped ENNReal

noncomputable section
set_option linter.unusedSectionVars false

section Disc
variable {d M k : ℕ}

/-- The coupling of Lemma `as:lem:conc` (c) for the uniform distribution on `kL` labelled points:
Steinitz ordering, a uniformly random block of `k` consecutive points, in uniformly random order. -/
lemma disc_coupling' (hS : H_steinitz_nonneg) {L : ℕ} (hk : 0 < k) (hL : 0 < L) (lab : Fin (L * k) → Fin M)
    (x : Fin M → EuclideanSpace ℝ (Fin d)) {ℓ : ℝ}
    (hx : ∀ i, ‖x (lab i) - ((L * k : ℕ) : ℝ)⁻¹ • ∑ i', x (lab i')‖ ≤ ℓ) :
    ∃ w : (Fin k → Fin M) → ℝ,
      IsLabCoupling (fun c => ((Finset.univ.filter (fun i => lab i = c)).card : ℝ) / (L * k)) w ∧
      ∀ t, 0 < w t → ‖∑ j, x (t j) - (k : ℝ) • (((L * k : ℕ) : ℝ)⁻¹ • ∑ i', x (lab i'))‖ ≤
        2 * d * ℓ := by
  have hN0 : (0 : ℝ) < ((L * k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hL hk
  set mbar := ((L * k : ℕ) : ℝ)⁻¹ • ∑ i', x (lab i') with hmbar
  have hN := hN0
  set v : Fin (L * k) → EuclideanSpace ℝ (Fin d) := fun i => x (lab i) - mbar
  have hv0 : ∑ i, v i = 0 := by
    simp only [v, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      mbar, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hN.ne', one_smul, sub_self]
  obtain ⟨π, hπ⟩ := hS d (L * k) v ℓ
    (le_trans (norm_nonneg _) (hx ⟨0, Nat.mul_pos hL hk⟩)) hx hv0
  set y : Fin (L * k) → Fin M := fun i => lab (π i)
  set f : Fin L → (Fin k ≃ Fin k) → Fin k → Fin M := fun b σ j => y (finProdFinEquiv (b, σ j))
  set K := (Fintype.card (Fin k ≃ Fin k) : ℝ)
  have hK : K = (k.factorial : ℝ) := by
    simp only [K, Fintype.card_equiv (Equiv.refl (Fin k)), Fintype.card_fin]
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast k.factorial_pos
  set w : (Fin k → Fin M) → ℝ := fun t =>
    ((L : ℝ) * K)⁻¹ * ∑ b, ∑ σ, if t = f b σ then (1 : ℝ) else 0
  refine ⟨w, ⟨fun t => ?_, fun j c => ?_⟩, fun t ht => ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun σ _ =>
      by split_ifs <;> norm_num)
  · -- marginals
    have e1 : ∀ t, (if t j = c then w t else 0) = ((L : ℝ) * K)⁻¹ *
        ∑ b, ∑ σ, if t = f b σ then (if f b σ j = c then (1 : ℝ) else 0) else 0 := by
      intro t
      simp only [w]
      split_ifs with h
      · congr 1; refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun σ _ => ?_
        split_ifs with h1 h2 <;> first | rfl | (subst h1; exact absurd h h2)
      · rw [eq_comm, mul_eq_zero]; right
        refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun σ _ => ?_
        split_ifs with h1 h2
        · subst h1; exact absurd h2 h
        · rfl
        · rfl
    simp only [e1, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have e3 : ∀ b, ∑ t : Fin k → Fin M, ∑ σ : Fin k ≃ Fin k,
        (if t = f b σ then (if f b σ j = c then (1 : ℝ) else 0) else 0) =
        ∑ σ : Fin k ≃ Fin k, (if f b σ j = c then (1 : ℝ) else 0) := by
      intro b
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => by simp
    simp only [e3]
    -- counting permutations
    have hcount : ∀ b, ∑ σ : Fin k ≃ Fin k, (if f b σ j = c then (1 : ℝ) else 0) =
        K / k * ∑ i : Fin k, (if y (finProdFinEquiv (b, i)) = c then (1 : ℝ) else 0) := by
      intro b
      have := Mixes.nsmul_sum_equiv_apply
        (fun i : Fin k => if y (finProdFinEquiv (b, i)) = c then (1 : ℝ) else 0) j
      simp only [nsmul_eq_mul] at this
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
      simpa [f, K, mul_comm] using this
    simp only [hcount, ← Finset.mul_sum]
    rw [← Fintype.sum_prod_type' (fun b i => if y (finProdFinEquiv (b, i)) = c then (1 : ℝ) else 0)]
    rw [Fintype.sum_equiv finProdFinEquiv (fun p => if y (finProdFinEquiv p) = c then (1 : ℝ) else 0)
      (fun i => if y i = c then (1 : ℝ) else 0) (fun _ => rfl)]
    simp only [y]
    rw [Equiv.sum_comp π (fun i => if lab i = c then (1 : ℝ) else 0), Finset.sum_boole]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
  · -- support
    obtain ⟨b, σ, rfl⟩ : ∃ b σ, t = f b σ := by
      by_contra hne
      push_neg at hne
      have : w t = 0 := by
        simp only [w]
        rw [mul_eq_zero]; right
        exact Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun σ _ => if_neg (hne b σ)
      linarith
    have e2 : ∑ j, x (f b σ j) - (k : ℝ) • mbar = ∑ i : Fin k, v (π (finProdFinEquiv (b, i))) := by
      rw [← Equiv.sum_comp σ (fun i => v (π (finProdFinEquiv (b, i))))]
      simp only [v, f, y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [e2, block_sum (fun i => v (π i)) b]
    have h1 := hπ (k * b + k)
    have h2 := hπ (k * b)
    calc _ ≤ ‖∑ i : Fin (L * k), if (i : ℕ) < k * b + k then v (π i) else 0‖ +
          ‖∑ i : Fin (L * k), if (i : ℕ) < k * b then v (π i) else 0‖ := norm_sub_le _ _
      _ ≤ d * ℓ + d * ℓ := add_le_add h1 h2
      _ = 2 * d * ℓ := by ring

end Disc

open Filter Topology

section Weighted
variable {d M k : ℕ}

/-- Lemma `as:lem:conc` (c) for finitely many weighted points (real weights): limit of the
Steinitz couplings for rational approximations of the weights. -/
lemma weighted_coupling' (hS : H_steinitz_nonneg) (hk : 0 < k) (hM : 0 < M) (p : Fin M → ℝ)
    (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (x : Fin M → EuclideanSpace ℝ (Fin d)) {ℓ : ℝ}
    (hx : ∀ c c', ‖x c - x c'‖ ≤ ℓ) :
    ∃ w : (Fin k → Fin M) → ℝ, IsLabCoupling p w ∧
      ∀ t, 0 < w t → ‖∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c‖ ≤ 2 * d * ℓ := by
  set c0 : Fin M := ⟨0, hM⟩
  set j0 : Fin k := ⟨0, hk⟩
  -- rational approximations
  set Lk : ℕ → ℕ := fun N => (N + 1) * k
  have hLk : ∀ N, (0 : ℝ) < Lk N := fun N => by simp only [Lk]; positivity
  set fl : ℕ → Fin M → ℕ := fun N c => ⌊p c * Lk N⌋₊
  have hfl : ∀ N, ∑ c ∈ Finset.univ.erase c0, fl N c ≤ Lk N := by
    intro N
    have : (∑ c ∈ Finset.univ.erase c0, (fl N c : ℝ)) ≤ Lk N := by
      calc (∑ c ∈ Finset.univ.erase c0, (fl N c : ℝ)) ≤ ∑ c ∈ Finset.univ.erase c0, p c * Lk N :=
            Finset.sum_le_sum fun c _ => Nat.floor_le (mul_nonneg (hp0 c) (hLk N).le)
        _ ≤ ∑ c, p c * Lk N := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun c _ _ => mul_nonneg (hp0 c) (hLk N).le
        _ = Lk N := by rw [← Finset.sum_mul, hp1, one_mul]
    exact_mod_cast this
  set n : ℕ → Fin M → ℕ := fun N c =>
    if c = c0 then Lk N - ∑ c ∈ Finset.univ.erase c0, fl N c else fl N c
  have hnsum : ∀ N, ∑ c, n N c = Lk N := by
    intro N
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
    simp only [n, if_pos rfl]
    rw [Finset.sum_congr rfl (g := fl N) (fun c hc => if_neg (Finset.ne_of_mem_erase hc))]
    exact Nat.sub_add_cancel (hfl N)
  set pN : ℕ → Fin M → ℝ := fun N c => (n N c : ℝ) / Lk N
  have hpN0 : ∀ N c, 0 ≤ pN N c := fun N c => by positivity
  have hpN1 : ∀ N, ∑ c, pN N c = 1 := by
    intro N
    simp only [pN, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (hLk N).ne']; exact_mod_cast hnsum N
  -- convergence of the weights
  have htend_ne : ∀ c, c ≠ c0 → Tendsto (fun N => pN N c) atTop (𝓝 (p c)) := by
    intro c hc
    have e : ∀ N, pN N c = (fl N c : ℝ) / Lk N := fun N => by simp only [pN, n, if_neg hc]
    simp only [e]
    have hup : ∀ N, (fl N c : ℝ) / Lk N ≤ p c := fun N => by
      rw [div_le_iff₀ (hLk N)]; exact Nat.floor_le (mul_nonneg (hp0 c) (hLk N).le)
    have hlo : ∀ N : ℕ, p c - 1 / ((N : ℝ) + 1) ≤ (fl N c : ℝ) / Lk N := fun N => by
      have h1 := Nat.lt_floor_add_one (p c * Lk N)
      change p c * (Lk N : ℝ) < (fl N c : ℝ) + 1 at h1
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [le_div_iff₀ (hLk N)]
      have : (Lk N : ℝ) = (N + 1) * k := by simp [Lk]
      rw [this] at h1 ⊢
      have hN1 : (0:ℝ) < N + 1 := by positivity
      rw [sub_mul, div_mul_eq_mul_div, one_mul, mul_div_assoc,
        show ((N:ℝ) + 1) * (k / ((N:ℝ) + 1)) = k by field_simp]
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlo hup
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds (x := p c)).sub this
  have htend : ∀ c, Tendsto (fun N => pN N c) atTop (𝓝 (p c)) := by
    intro c
    by_cases hc : c = c0
    · subst hc
      have e : ∀ N, pN N c0 = 1 - ∑ c ∈ Finset.univ.erase c0, pN N c := by
        intro N; rw [← hpN1 N, ← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]; ring
      have e2 : p c0 = 1 - ∑ c ∈ Finset.univ.erase c0, p c := by
        rw [← hp1, ← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]; ring
      simp only [e]; rw [e2]
      exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun c hc =>
        htend_ne c (Finset.ne_of_mem_erase hc))
    · exact htend_ne c hc
  -- Steinitz couplings for the approximations
  set mN : ℕ → EuclideanSpace ℝ (Fin d) := fun N => ∑ c, pN N c • x c
  have hdisc : ∀ N, ∃ w : (Fin k → Fin M) → ℝ, IsLabCoupling (pN N) w ∧
      ∀ t, 0 < w t → ‖∑ j, x (t j) - (k : ℝ) • mN N‖ ≤ 2 * d * ℓ := by
    intro N
    obtain ⟨lab, hlab⟩ := exists_lab (n N)
    have hcast : ∑ c, n N c = (N + 1) * k := hnsum N
    -- transport to `Fin ((N+1) * k)`
    set lab' : Fin ((N + 1) * k) → Fin M := fun i => lab (Fin.cast hcast.symm i)
    have hlab' : ∀ c, ((Finset.univ.filter (fun i => lab' i = c)).card : ℝ) = n N c := by
      intro c
      rw [← hlab c]
      congr 1
      rw [Finset.card_filter, Finset.card_filter]
      exact Fintype.sum_equiv (finCongr hcast.symm) _ _ (fun i => rfl)
    have hm : ((((N + 1) * k : ℕ) : ℝ))⁻¹ • ∑ i', x (lab' i') = mN N := by
      rw [sum_lab, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hlab', smul_smul]; simp only [pN, Lk]; congr 1; push_cast; ring
    obtain ⟨w, hw, hws⟩ := disc_coupling' hS hk N.succ_pos lab' x (ℓ := ℓ) (by
      intro i; rw [hm]; exact norm_sub_convex _ (hpN0 N) (hpN1 N) x hx _)
    refine ⟨w, ⟨hw.1, fun j c => ?_⟩, fun t ht => ?_⟩
    · rw [hw.2 j c]; simp only [hlab', pN, Lk]; push_cast; ring
    · have := hws t ht; rwa [hm] at this
  choose wN hwN hwNs using hdisc
  -- compactness
  have hbound : ∀ N t, wN N t ∈ Icc (0 : ℝ) 1 := by
    intro N t
    refine ⟨(hwN N).1 t, ?_⟩
    have h1 := (hwN N).2 j0 (t j0)
    have h2 : wN N t ≤ ∑ t', (if t' j0 = t j0 then wN N t' else 0) := by
      have := Finset.single_le_sum (f := fun t' => if t' j0 = t j0 then wN N t' else 0)
        (fun t' _ => by split_ifs; exact (hwN N).1 t'; exact le_rfl) (Finset.mem_univ t)
      simpa using this
    have h3 : pN N (t j0) ≤ 1 := by
      rw [← hpN1 N]
      exact Finset.single_le_sum (fun c _ => hpN0 N c) (Finset.mem_univ _)
    linarith
  obtain ⟨w, -, φ, hφ, hlim⟩ := (isCompact_univ_pi (fun _ : Fin k → Fin M =>
    isCompact_Icc (a := (0:ℝ)) (b := 1))).tendsto_subseq (x := wN)
    (fun N => mem_univ_pi.2 (hbound N))
  have hlimt : ∀ t, Tendsto (fun N => wN (φ N) t) atTop (𝓝 (w t)) := fun t =>
    (continuous_apply t).continuousAt.tendsto.comp hlim
  have hmN : Tendsto (fun N => mN (φ N)) atTop (𝓝 (∑ c, p c • x c)) :=
    tendsto_finsetSum _ fun c _ => ((htend c).comp hφ.tendsto_atTop).smul_const _
  refine ⟨w, ⟨fun t => ge_of_tendsto' (hlimt t) fun N => (hwN (φ N)).1 t, fun j c => ?_⟩,
    fun t ht => ?_⟩
  · have h1 : Tendsto (fun N => ∑ t, (if t j = c then wN (φ N) t else 0)) atTop
        (𝓝 (∑ t, (if t j = c then w t else 0))) :=
      tendsto_finsetSum _ fun t _ => by
        split_ifs; exact hlimt t; exact tendsto_const_nhds
    have h2 : (fun N => ∑ t, (if t j = c then wN (φ N) t else 0)) = fun N => pN (φ N) c :=
      funext fun N => (hwN (φ N)).2 j c
    rw [h2] at h1
    exact tendsto_nhds_unique h1 ((htend c).comp hφ.tendsto_atTop)
  · have hev : ∀ᶠ N in atTop, 0 < wN (φ N) t := (hlimt t).eventually (lt_mem_nhds ht)
    have hcont : Tendsto (fun N => ‖∑ j, x (t j) - (k : ℝ) • mN (φ N)‖) atTop
        (𝓝 ‖∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c‖) :=
      (tendsto_const_nhds.sub (hmN.const_smul _)).norm
    exact le_of_tendsto hcont (hev.mono fun N hN => hwNs (φ N) t hN)

end Weighted

section Lift
variable {d k : ℕ}
open ProbabilityTheory

/-- Lifting step of Lemma `as:lem:conc` (c): a coupling with exact marginals and error
`2 d ℓ + 2 k ε`. -/
lemma eps_coupling' (hS : H_steinitz_nonneg) (hk : 0 < k) (T : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure T] {K : Set (EuclideanSpace ℝ (Fin d))} (hKc : IsCompact K)
    (hKT : T Kᶜ = 0) {ℓ : ℝ} (hKd : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ ℓ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Measure (Fin k → EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P ∧
      (∀ j, P.map (fun y => y j) = T) ∧ P (Set.univ.pi fun _ => K)ᶜ = 0 ∧
      ∀ᵐ y ∂P, ‖∑ j, y j - (k : ℝ) • ∫ x, x ∂T‖ ≤ 2 * d * ℓ + 2 * k * ε := by
  classical
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hne : K.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hKT; exact one_ne_zero hKT
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨M, C, hM, hCm, hCK, hcov, hdisj, hCd⟩ := exists_partition hKc ⟨x0, hx0⟩ hε
  set p : Fin M → ℝ := fun c => (T (C c)).toReal with hp_def
  set x : Fin M → EuclideanSpace ℝ (Fin d) := fun c =>
    if h : (C c).Nonempty then h.some else x0 with hx_def
  have hxK : ∀ c, x c ∈ K := fun c => by
    simp only [x]; split_ifs with h
    · exact hCK c h.some_mem
    · exact hx0
  have hxC : ∀ c, (C c).Nonempty → x c ∈ C c := fun c h => by
    simp only [x, dif_pos h]; exact h.some_mem
  have hUK : (⋃ c, C c) = K := Set.Subset.antisymm (Set.iUnion_subset hCK)
    (fun y hy => Set.mem_iUnion.2 (hcov y hy))
  have hsplit : ∀ s, MeasurableSet s → ∑ c, T (C c ∩ s) = T s := by
    intro s hs
    have hU : T (⋃ c, C c ∩ s) = ∑ c, T (C c ∩ s) := by
      rw [measure_iUnion (fun c c' hcc' =>
        ((hdisj c c' hcc').mono Set.inter_subset_left Set.inter_subset_left))
        (fun c => (hCm c).inter hs), tsum_fintype]
    rw [← hU, ← Set.iUnion_inter, hUK, Set.inter_comm]
    exact measure_inter_conull hKT
  have hp0 : ∀ c, 0 ≤ p c := fun c => ENNReal.toReal_nonneg
  have hp1 : ∑ c, p c = 1 := by
    simp only [p]; rw [← ENNReal.toReal_sum (fun c _ => measure_ne_top _ _)]
    have := hsplit univ MeasurableSet.univ
    simp only [Set.inter_univ, measure_univ] at this
    rw [this]; rfl
  obtain ⟨w, ⟨hw0, hwm⟩, hwb⟩ := weighted_coupling' hS hk hM p hp0 hp1 x (ℓ := ℓ)
    (fun c c' => by rw [← dist_eq_norm]; exact hKd _ (hxK c) _ (hxK c'))
  set q : Fin M → Measure (EuclideanSpace ℝ (Fin d)) := fun c =>
    if T (C c) = 0 then T else T[|C c] with hq_def
  have hq : ∀ c, IsProbabilityMeasure (q c) := fun c => by
    simp only [q]; split_ifs with h
    · infer_instance
    · exact cond_isProbabilityMeasure h
  have hqs : ∀ c s, MeasurableSet s → ENNReal.ofReal (p c) * q c s = T (C c ∩ s) := by
    intro c s hs
    simp only [p, ENNReal.ofReal_toReal (measure_ne_top _ _), q]
    split_ifs with h
    · rw [h, zero_mul]; exact (measure_mono_null Set.inter_subset_left h).symm
    · rw [mul_comm]; exact cond_mul_eq_inter (hCm c) s T
  set P : Measure (Fin k → EuclideanSpace ℝ (Fin d)) :=
    ∑ t, ENNReal.ofReal (w t) • Measure.pi (fun j => q (t j)) with hP_def
  have hPapp : ∀ A, P A = ∑ t, ENNReal.ofReal (w t) * Measure.pi (fun j => q (t j)) A := by
    intro A; simp only [P, _root_.sum_apply, smul_apply, smul_eq_mul]
  have hmarg : ∀ j, P.map (fun y => y j) = T := by
    intro j; ext s hs
    rw [Measure.map_apply (measurable_pi_apply j) hs, hPapp]
    have h1 : ∀ t : Fin k → Fin M,
        Measure.pi (fun j => q (t j)) ((fun y => y j) ⁻¹' s) = q (t j) s := fun t =>
      (measurePreserving_eval (fun j => q (t j)) j).measure_preimage hs.nullMeasurableSet
    simp_rw [h1]
    rw [← hsplit s hs, ← Finset.sum_fiberwise Finset.univ (fun t : Fin k → Fin M => t j)
      (fun t => ENNReal.ofReal (w t) * q (t j) s)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hqs c s hs, ← hwm j c, ← Finset.sum_filter,
      ENNReal.ofReal_sum_of_nonneg (fun t _ => hw0 t), Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.1 ht).2]
  have hPprob : IsProbabilityMeasure P := by
    constructor
    have := congrArg (fun μ : Measure _ => μ univ) (hmarg ⟨0, hk⟩)
    simp only [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, Set.preimage_univ,
      measure_univ] at this
    exact this
  -- good sets
  set G : (Fin k → Fin M) → Set (Fin k → EuclideanSpace ℝ (Fin d)) := fun t =>
    {y | ∀ j, y j ∈ C (t j)} with hG_def
  have hpw : ∀ t j, w t ≤ p (t j) := fun t j => by
    rw [← hwm j (t j)]
    have := Finset.single_le_sum (f := fun t' : Fin k → Fin M => if t' j = t j then w t' else 0)
      (fun t' _ => by split_ifs <;> simp [hw0 t']) (Finset.mem_univ t)
    simpa using this
  have hGnull : ∀ t, 0 < w t → Measure.pi (fun j => q (t j)) (G t)ᶜ = 0 := by
    intro t ht
    have hG : (G t)ᶜ = ⋃ j, (fun y : Fin k → EuclideanSpace ℝ (Fin d) => y j) ⁻¹' (C (t j))ᶜ := by
      ext y; simp [G]
    rw [hG]
    refine measure_iUnion_null fun j => ?_
    rw [(measurePreserving_eval (fun j => q (t j)) j).measure_preimage
      (hCm (t j)).compl.nullMeasurableSet]
    have hpos : T (C (t j)) ≠ 0 := by
      intro h0
      have := hpw t j
      simp only [p, h0, ENNReal.toReal_zero] at this
      linarith
    simp only [q, if_neg hpos]
    exact ae_iff.1 (ae_cond_mem (hCm (t j)))
  have hae : ∀ Q : (Fin k → EuclideanSpace ℝ (Fin d)) → Prop,
      (∀ t, 0 < w t → ∀ y ∈ G t, Q y) → ∀ᵐ y ∂P, Q y := by
    intro Q hQ
    rw [ae_iff, hPapp]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases (hw0 t).lt_or_eq with ht | ht
    · rw [measure_mono_null (fun y hy => ?_) (hGnull t ht), mul_zero]
      by_contra hyG
      exact hy (hQ t ht y (by simpa using hyG))
    · rw [← ht, ENNReal.ofReal_zero, zero_mul]
  -- mean
  have hTsum : T = ∑ c, T.restrict (C c) := by
    ext s hs
    rw [_root_.sum_apply, ← hsplit s hs]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Measure.restrict_apply hs, Set.inter_comm]
  have hint : Integrable id T := integrable_of_bdd hKc.isBounded hKT
  have hmean : ‖∑ c, p c • x c - ∫ y, y ∂T‖ ≤ ε := by
    have h1 : ∫ y, y ∂T = ∑ c, ∫ y, y ∂(T.restrict (C c)) := by
      conv_lhs => rw [hTsum]
      exact integral_finsetSum_measure fun c _ => hint.restrict
    have h2 : ∀ c, p c • x c = ∫ _y, x c ∂(T.restrict (C c)) := fun c => by
      rw [integral_const, measureReal_def, Measure.restrict_apply_univ]
    rw [h1, ← Finset.sum_sub_distrib]
    calc ‖∑ c, (p c • x c - ∫ y, y ∂(T.restrict (C c)))‖
        ≤ ∑ c, ‖p c • x c - ∫ y, y ∂(T.restrict (C c))‖ := norm_sum_le _ _
      _ ≤ ∑ c, ε * p c := Finset.sum_le_sum fun c _ => by
          rw [h2, ← integral_sub (f := fun _ => x c) (g := fun y => y) (integrable_const _) hint.restrict]
          have := norm_integral_le_of_norm_le_const (μ := T.restrict (C c))
            (f := fun y => x c - y) (C := ε) ?_
          · simpa [measureReal_def, Measure.restrict_apply_univ, p] using this
          · refine ae_restrict_of_forall_mem (hCm c) fun y hy => ?_
            rw [← dist_eq_norm]; exact hCd c _ (hxC c ⟨y, hy⟩) _ hy
      _ = ε := by rw [← Finset.mul_sum, hp1, mul_one]
  refine ⟨P, hPprob, hmarg, ?_, hae _ fun t ht y hy => ?_⟩
  · have := hae (fun y => y ∈ Set.univ.pi fun _ => K) fun t _ y hy =>
      fun j _ => hCK _ (hy j)
    exact ae_iff.1 this
  · have hdec : ∑ j, y j - (k : ℝ) • ∫ x, x ∂T = ∑ j, (y j - x (t j)) +
        (∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c) + (k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T) := by
      rw [Finset.sum_sub_distrib, smul_sub]; abel
    rw [hdec]
    have hA : ‖∑ j, (y j - x (t j))‖ ≤ k * ε := by
      calc ‖∑ j, (y j - x (t j))‖ ≤ ∑ j, ‖y j - x (t j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin k, ε := Finset.sum_le_sum fun j _ => by
            rw [← dist_eq_norm]; exact hCd _ _ (hy j) _ (hxC _ ⟨y j, hy j⟩)
        _ = k * ε := by simp
    have hB := hwb t ht
    have hC : ‖(k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T)‖ ≤ k * ε := by
      rw [norm_smul, Real.norm_natCast]
      exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg k)
    calc _ ≤ ‖∑ j, (y j - x (t j)) + (∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c)‖ +
          ‖(k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T)‖ := norm_add_le _ _
      _ ≤ ‖∑ j, (y j - x (t j))‖ + ‖∑ j, x (t j) - (k : ℝ) • ∑ c, p c • x c‖ +
          ‖(k : ℝ) • (∑ c, p c • x c - ∫ x, x ∂T)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith

open scoped BoundedContinuousFunction

/-- **Lemma `as:lem:conc` (c)**: if `T` is supported on a set of diameter at most `ℓ`, there is a
coupling of `k` copies of `T` whose sum stays within norm distance `2 d ℓ` of `k` times the mean.
Proved from `H_steinitz_nonneg` (Grinberg–Sevastyanov) by the Steinitz coupling of a fine partition and a
Prokhorov limit. -/
theorem lem_conc_c' (hS : H_steinitz_nonneg) (hk : 0 < k) (T : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure T] {ℓ : ℝ} (hT : SuppDiam T ℓ) :
    ∃ P : Measure (Fin k → EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P ∧
      (∀ j, P.map (fun y => y j) = T) ∧
      ∀ᵐ y ∂P, ‖∑ j, y j - (k : ℝ) • ∫ x, x ∂T‖ ≤ 2 * d * ℓ := by
  obtain ⟨S0, hS0T, hS0d⟩ := hT
  have hb : Bornology.IsBounded S0 := suppDiam_bdd (F := T) hS0d
  set K := closure S0 with hK_def
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hKT : T Kᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 subset_closure) hS0T
  have hne : S0.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hS0T; exact one_ne_zero hS0T
  have hℓ : 0 ≤ ℓ := by obtain ⟨x, hx⟩ := hne; simpa using hS0d x hx x hx
  have hKd : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ ℓ := by
    intro x hx y hy
    have hd : Metric.diam S0 ≤ ℓ := Metric.diam_le_of_forall_dist_le hℓ hS0d
    calc dist x y ≤ Metric.diam K := Metric.dist_le_diam_of_mem hb.closure hx hy
      _ = Metric.diam S0 := Metric.diam_closure S0
      _ ≤ ℓ := hd
  have hP := fun N : ℕ => eps_coupling' hS hk T hKc hKT hKd (ε := 1 / ((N : ℝ) + 1))
    (by positivity)
  choose Ps hPprob hPmarg hPsupp hPbd using hP
  set μs : ℕ → ProbabilityMeasure (Fin k → EuclideanSpace ℝ (Fin d)) :=
    fun N => ⟨Ps N, hPprob N⟩ with hμs
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure (Fin k → EuclideanSpace ℝ (Fin d))) :
        Measure (Fin k → EuclideanSpace ℝ (Fin d))) | μ ∈ Set.range μs} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hKc, ?_⟩
    rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
    show Ps N _ ≤ ε
    rw [hPsupp N]; exact zero_le
  obtain ⟨μ, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    (fun N => subset_closure (Set.mem_range_self N))
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim
  refine ⟨μ, inferInstance, fun j => ?_, ?_⟩
  · refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    set g : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ :=
      f.compContinuous ⟨fun y => y j, continuous_apply j⟩
    have h1 : ∀ ν : Measure (Fin k → EuclideanSpace ℝ (Fin d)),
        ∫ x, f x ∂(ν.map fun y => y j) = ∫ y, g y ∂ν := fun ν => by
      rw [integral_map (measurable_pi_apply j).aemeasurable f.continuous.aestronglyMeasurable]; rfl
    rw [h1]
    have h2 := hlim g
    have h3 : (fun i => ∫ y, g y ∂((μs ∘ φ) i : Measure (Fin k → EuclideanSpace ℝ (Fin d)))) =
        fun _ => ∫ x, f x ∂T := by
      funext i
      show ∫ y, g y ∂(Ps (φ i)) = _
      rw [← h1, hPmarg]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  · set m := (k : ℝ) • ∫ x, x ∂T
    set gf : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ :=
      fun y => min 1 (max 0 (‖∑ j, y j - m‖ - 2 * d * ℓ)) with hgf
    have hgc : Continuous gf := by
      simp only [gf]; fun_prop
    have hg01 : ∀ y, 0 ≤ gf y ∧ gf y ≤ 1 := fun y =>
      ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    set g : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨gf, hgc⟩ 1 (fun a b => by
        show |gf a - gf b| ≤ 1
        have := hg01 a; have := hg01 b
        rw [abs_le]; constructor <;> linarith)
    have hgv : ∀ y, g y = gf y := fun y => rfl
    have hseq : ∀ N, ∫ y, g y ∂(Ps N) ≤ 2 * k * (1 / ((N : ℝ) + 1)) := by
      intro N
      have : ∀ᵐ y ∂(Ps N), g y ≤ 2 * k * (1 / ((N : ℝ) + 1)) := (hPbd N).mono fun y hy => by
        rw [hgv]; exact (min_le_right _ _).trans (max_le (by positivity) (by linarith))
      calc ∫ y, g y ∂(Ps N) ≤ ∫ _y, 2 * k * (1 / ((N : ℝ) + 1)) ∂(Ps N) :=
            integral_mono_ae (g.integrable _) (integrable_const _) this
        _ = _ := by simp
    have hpos : ∀ N, 0 ≤ ∫ y, g y ∂(Ps N) := fun N => integral_nonneg fun y => (hg01 y).1
    have hto : Tendsto (fun N => ∫ y, g y ∂(Ps N)) atTop (𝓝 0) := by
      refine squeeze_zero hpos hseq ?_
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (k : ℝ))
      rwa [mul_zero] at this
    have h2 := hlim g
    have h0 : ∫ y, g y ∂(μ : Measure (Fin k → EuclideanSpace ℝ (Fin d))) = 0 :=
      tendsto_nhds_unique h2 (hto.comp hφ.tendsto_atTop)
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => (hg01 y).1) (g.integrable _)).1 h0
    filter_upwards [hae] with y hy
    have hy' : gf y = 0 := hy
    have hmax : max 0 (‖∑ j, y j - m‖ - 2 * d * ℓ) = 0 := by
      rcases le_total 1 (max 0 (‖∑ j, y j - m‖ - 2 * d * ℓ)) with h | h
      · simp only [gf, min_eq_left h] at hy'; norm_num at hy'
      · simpa only [gf, min_eq_right h] using hy'
    have := le_max_right 0 (‖∑ j, y j - m‖ - 2 * d * ℓ)
    linarith

end Lift

section Final
variable {d : ℕ}

/-- The coupling bound for `d ≥ 2` (more generally `d ≠ 1`), from Lemma `as:lem:conc` (c). -/
theorem couplingBound_of_steinitz' (hS : H_steinitz_nonneg) (hd : d ≠ 1) : CouplingBound d := by
  intro T _ R k hk hT
  obtain ⟨P, hP, hPm, hPb⟩ := lem_conc_c' hS hk T hT
  refine ⟨P, hP, hPm, hPb.mono fun y hy i => ?_⟩
  have h1 := PiLp.norm_apply_le (∑ j, y j - (k : ℝ) • ∫ x, x ∂T) i
  rw [Real.norm_eq_abs] at h1
  simp only [cdConst, if_neg hd]
  linarith



/-- **Theorem `as:thm:window`** for every dimension. -/
theorem thm_window' (hP : PropWindow) (hS : H_steinitz_nonneg) (d : ℕ) : ThmWindow d := by
  rcases eq_or_ne d 1 with rfl | hd
  · exact thm_window_d1 hP
  · exact thmWindow_of hP (couplingBound_of_steinitz' hS hd)

end Final

/-! ### Unconditional results -/

/-- **Lemma `as:lem:conc` (c)**, unconditional. -/
theorem lem_conc_c_uncond {d k : ℕ} (hk : 0 < k) (T : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure T] {ℓ : ℝ} (hT : SuppDiam T ℓ) :
    ∃ P : Measure (Fin k → EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P ∧
      (∀ j, P.map (fun y => y j) = T) ∧
      ∀ᵐ y ∂P, ‖∑ j, y j - (k : ℝ) • ∫ x, x ∂T‖ ≤ 2 * d * ℓ :=
  lem_conc_c' steinitz_nonneg hk T hT

/-- The coupling bound `AsymThm.CouplingBound d` in every dimension, unconditional. -/
theorem couplingBound_all (d : ℕ) : CouplingBound d := by
  rcases eq_or_ne d 1 with rfl | hd
  · exact couplingBound_one
  · exact couplingBound_of_steinitz' steinitz_nonneg hd

/-- **Theorem `as:thm:window`** in every dimension, unconditional
(`= Mixes.AsymGeneral.H_thm_window d`, verbatim copy `AsymThm.ThmWindow d`). -/
theorem thm_window_all (d : ℕ) : ThmWindow d :=
  thm_window' propWindow_proved steinitz_nonneg d

end

end Mixes.Steinitz
