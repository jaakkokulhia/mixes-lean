import Mixes.NormAtom

/-!
# Stop-loss order and convex order

For probability measures carried by a bounded interval `[-R, R]` with equal means, the stop-loss
order implies the convex order (Shaked and Shanthikumar, *Stochastic Orders*, Theorem 3.A.1).
This discharges the classical hypothesis `NormAtom.H_stoploss_cx`.

Proof: given a convex `φ` and `ε > 0`, take a uniform grid `t₀ < ⋯ < t_N` of `[-R, R]` fine
enough that `φ` varies by less than `ε` on each cell, and the chord interpolant
`g(x) = φ(t₀) + s₀ (x - t₀) + ∑_{i < N-1} (s_{i+1} - s_i) (x - t_{i+1})₊`, `s_i` the slope of
`φ` on `[t_i, t_{i+1}]`. Convexity gives `s_i ≤ s_{i+1}` and `φ ≤ g ≤ φ + ε` on `[-R, R]`; the
affine part of `g` has equal integrals (equal means) and the hinge part is ordered by the
stop-loss order. Hence `∫ φ dL ≤ ∫ g dL ≤ ∫ g dL' ≤ ∫ φ dL' + ε`.
-/

open MeasureTheory Finset

noncomputable section

namespace Mixes.StopLoss

open NormAtom

section Grid

variable (φ : ℝ → ℝ) (R : ℝ) (N : ℕ)

/-- The mesh `2R/N` of the grid. -/
def hh : ℝ := 2 * R / N

/-- The grid point `t_k = -R + k (2R/N)`. -/
def tt (k : ℕ) : ℝ := -R + hh R N * k

/-- The slope of `φ` on the cell `[t_k, t_{k+1}]`. -/
def ss (k : ℕ) : ℝ := (φ (tt R N (k + 1)) - φ (tt R N k)) / hh R N

/-- The chord interpolant of `φ` on the grid, written as an affine function plus hinges. -/
def gg (x : ℝ) : ℝ :=
  φ (tt R N 0) + ss φ R N 0 * (x - tt R N 0) +
    ∑ i ∈ range (N - 1), (ss φ R N (i + 1) - ss φ R N i) * max (x - tt R N (i + 1)) 0

variable {R N}

lemma tt_succ (k : ℕ) : tt R N (k + 1) = tt R N k + hh R N := by
  simp only [tt]; push_cast; ring

lemma hh_pos (hR : 0 < R) (hN : 0 < N) : 0 < hh R N := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  unfold hh; positivity

lemma tt_le (hR : 0 < R) (hN : 0 < N) {a b : ℕ} (hab : a ≤ b) : tt R N a ≤ tt R N b := by
  unfold tt
  have := mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ b by exact_mod_cast hab) (hh_pos hR hN).le
  linarith

lemma tt_N (hN : 0 < N) : tt R N N = R := by
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold tt hh; field_simp; ring

lemma tt_mem (hR : 0 < R) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) : tt R N k ∈ Set.Icc (-R) R := by
  refine ⟨?_, ?_⟩
  · have := tt_le hR hN (Nat.zero_le k); simpa [tt] using this
  · have := tt_le hR hN hk; rwa [tt_N hN] at this

lemma ss_mul (hR : 0 < R) (hN : 0 < N) (k : ℕ) :
    ss φ R N k * hh R N = φ (tt R N (k + 1)) - φ (tt R N k) := by
  unfold ss; exact div_mul_cancel₀ _ (hh_pos hR hN).ne'

lemma G_eq (hR : 0 < R) (hN : 0 < N) (x : ℝ) (k : ℕ) :
    φ (tt R N 0) + ss φ R N 0 * (x - tt R N 0) +
        ∑ i ∈ range k, (ss φ R N (i + 1) - ss φ R N i) * (x - tt R N (i + 1)) =
      φ (tt R N k) + ss φ R N k * (x - tt R N k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← add_assoc, ih]
    linear_combination ss_mul φ hR hN k + ss φ R N k * tt_succ (R := R) (N := N) k

lemma gg_eq_on (hR : 0 < R) (hN : 0 < N) {k : ℕ} (hk : k < N) {x : ℝ} (hx1 : tt R N k ≤ x)
    (hx2 : x ≤ tt R N (k + 1)) : gg φ R N x = φ (tt R N k) + ss φ R N k * (x - tt R N k) := by
  rw [gg, ← sum_range_add_sum_Ico _ (show k ≤ N - 1 by omega)]
  have h1 : ∑ i ∈ range k, (ss φ R N (i + 1) - ss φ R N i) * max (x - tt R N (i + 1)) 0 =
      ∑ i ∈ range k, (ss φ R N (i + 1) - ss φ R N i) * (x - tt R N (i + 1)) := by
    refine sum_congr rfl fun i hi => ?_
    have := tt_le hR hN (show i + 1 ≤ k by simp at hi; omega)
    rw [max_eq_left (by linarith)]
  have h2 : ∑ i ∈ Ico k (N - 1), (ss φ R N (i + 1) - ss φ R N i) * max (x - tt R N (i + 1)) 0 =
      0 := by
    refine sum_eq_zero fun i hi => ?_
    have := tt_le hR hN (show k + 1 ≤ i + 1 by simp at hi; omega)
    rw [max_eq_right (by linarith), mul_zero]
  rw [h1, h2, add_zero]
  exact G_eq φ hR hN x k

lemma exists_cell (hR : 0 < R) (hN : 0 < N) {x : ℝ} (hx : x ∈ Set.Icc (-R) R) :
    ∃ k < N, tt R N k ≤ x ∧ x ≤ tt R N (k + 1) := by
  have hh0 := hh_pos hR hN
  have hq : 0 ≤ (x + R) / hh R N := div_nonneg (by linarith [hx.1]) hh0.le
  set m := ⌊(x + R) / hh R N⌋₊ with hm
  have hfl : (m : ℝ) ≤ (x + R) / hh R N := Nat.floor_le hq
  have hfl' : (m : ℝ) * hh R N ≤ x + R := (le_div_iff₀ hh0).1 hfl
  by_cases hmN : m < N
  · refine ⟨m, hmN, ?_, ?_⟩
    · unfold tt; linarith
    · have hlt : (x + R) / hh R N < m + 1 := Nat.lt_floor_add_one _
      have := (div_lt_iff₀ hh0).1 hlt
      unfold tt; push_cast; linarith
  · refine ⟨N - 1, by omega, ?_, ?_⟩
    · have hc : ((N - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : N - 1 ≤ m)
      have := mul_le_mul_of_nonneg_left hc hh0.le
      unfold tt; linarith
    · rw [Nat.sub_add_cancel hN, tt_N hN]; exact hx.2

lemma ss_mono (hφ : ConvexOn ℝ Set.univ φ) (hR : 0 < R) (hN : 0 < N) (i : ℕ) :
    ss φ R N i ≤ ss φ R N (i + 1) := by
  have h0 := hh_pos hR hN
  have h := hφ.slope_mono_adjacent (x := tt R N i) (y := tt R N (i + 1)) (z := tt R N (i + 1 + 1))
    (Set.mem_univ _) (Set.mem_univ _) (by rw [tt_succ]; linarith) (by rw [tt_succ (k := i + 1)]; linarith)
  have e1 : tt R N (i + 1) - tt R N i = hh R N := by rw [tt_succ]; ring
  have e2 : tt R N (i + 1 + 1) - tt R N (i + 1) = hh R N := by rw [tt_succ (k := i + 1)]; ring
  rw [e1, e2] at h
  exact h

/-- On `[-R, R]` the interpolant lies above `φ` and at most `ε` above it, when `φ` varies by
at most `ε` over distances at most the mesh. -/
lemma gg_bounds (hφ : ConvexOn ℝ Set.univ φ) (hR : 0 < R) (hN : 0 < N) {ε : ℝ}
    (hε : ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R, |x - y| ≤ hh R N → |φ x - φ y| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc (-R) R) : φ x ≤ gg φ R N x ∧ gg φ R N x ≤ φ x + ε := by
  have h0 := hh_pos hR hN
  obtain ⟨k, hk, hx1, hx2⟩ := exists_cell hR hN hx
  have hts := tt_succ (R := R) (N := N) k
  set a := (tt R N (k + 1) - x) / hh R N with ha
  set b := (x - tt R N k) / hh R N with hb
  have ha0 : 0 ≤ a := div_nonneg (by linarith) h0.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith) h0.le
  have hbh : b * hh R N = x - tt R N k := div_mul_cancel₀ _ h0.ne'
  have hah : a * hh R N = tt R N (k + 1) - x := div_mul_cancel₀ _ h0.ne'
  have hab : a + b = 1 := by
    have : (a + b) * hh R N = 1 * hh R N := by rw [add_mul, hah, hbh, hts]; ring
    exact mul_right_cancel₀ h0.ne' this
  have hxab : a * tt R N k + b * tt R N (k + 1) = x := by
    have : (a * tt R N k + b * tt R N (k + 1)) * hh R N = x * hh R N := by
      have e : (a * tt R N k + b * tt R N (k + 1)) * hh R N =
          (a * hh R N) * tt R N k + (b * hh R N) * tt R N (k + 1) := by ring
      rw [e, hah, hbh, hts]; ring
    exact mul_right_cancel₀ h0.ne' this
  have hg : gg φ R N x = a * φ (tt R N k) + b * φ (tt R N (k + 1)) := by
    rw [gg_eq_on φ hR hN hk hx1 hx2]
    have hs := ss_mul φ hR hN k
    have ha' : a = 1 - b := by linarith
    linear_combination b * hs - ss φ R N k * hbh - φ (tt R N k) * ha'
  have hmk := tt_mem hR hN hk.le
  have hmk1 := tt_mem hR hN (show k + 1 ≤ N by omega)
  have e1 := hε _ hmk x hx (by rw [abs_le]; constructor <;> linarith)
  have e2 := hε _ hmk1 x hx (by rw [abs_le]; constructor <;> linarith)
  rw [abs_le] at e1 e2
  refine ⟨?_, ?_⟩
  · have := hφ.2 (Set.mem_univ (tt R N k)) (Set.mem_univ (tt R N (k + 1))) ha0 hb0 hab
    simp only [smul_eq_mul] at this
    rw [hxab] at this
    rw [hg]; exact this
  · rw [hg]
    have h1 := mul_le_mul_of_nonneg_left e1.2 ha0
    have h2 := mul_le_mul_of_nonneg_left e2.2 hb0
    have : φ x + ε = a * (φ x + ε) + b * (φ x + ε) := by rw [← add_mul, hab, one_mul]
    linarith

lemma cont_aff (a b c : ℝ) : Continuous fun x : ℝ => a + b * (x - c) :=
  continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))

lemma cont_hinge (c : ℝ) : Continuous fun x : ℝ => max (x - c) 0 :=
  (continuous_id.sub continuous_const).max continuous_const

lemma cont_hsum (s : Finset ℕ) (c t : ℕ → ℝ) :
    Continuous fun x : ℝ => ∑ i ∈ s, c i * max (x - t i) 0 :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (cont_hinge _)

lemma gg_continuous : Continuous (gg φ R N) := by
  unfold gg
  exact (cont_aff _ _ _).add (cont_hsum _ _ _)

lemma integral_gg {L : Measure ℝ} [IsProbabilityMeasure L]
    (hI : ∀ f : ℝ → ℝ, Continuous f → Integrable f L) :
    ∫ x, gg φ R N x ∂L = φ (tt R N 0) + ss φ R N 0 * (∫ x, x ∂L - tt R N 0) +
      ∑ i ∈ range (N - 1), (ss φ R N (i + 1) - ss φ R N i) * ∫ x, max (x - tt R N (i + 1)) 0 ∂L := by
  unfold gg
  have hA : ∫ x, φ (tt R N 0) + ss φ R N 0 * (x - tt R N 0) ∂L =
      φ (tt R N 0) + ss φ R N 0 * (∫ x, x ∂L - tt R N 0) := by
    rw [integral_add (integrable_const _)
        (hI (fun x => ss φ R N 0 * (x - tt R N 0))
          (continuous_const.mul (continuous_id.sub continuous_const))),
      integral_const, integral_const_mul,
      integral_sub (f := fun x => x) (g := fun _ => tt R N 0) (hI _ continuous_id)
        (integrable_const _), integral_const]
    simp
  rw [integral_add (hI _ (cont_aff _ _ _)) (hI _ (cont_hsum _ _ _)), hA,
    integral_finsetSum (f := fun i x => (ss φ R N (i + 1) - ss φ R N i) * max (x - tt R N (i + 1)) 0)
      _ fun i _ => hI _ (continuous_const.mul (cont_hinge _))]
  congr 1
  exact sum_congr rfl fun i _ => integral_const_mul _ _

end Grid

/-- **Stop-loss order implies convex order** (Shaked and Shanthikumar, *Stochastic Orders*,
Theorem 3.A.1) for probability measures carried by a bounded interval with equal means. This
proves the classical hypothesis `NormAtom.H_stoploss_cx`. -/
theorem stoploss_cx : H_stoploss_cx := by
  intro L L' hL hL' ⟨R0, h1, h2⟩ hmean hSL φ hφ hiL hiL'
  set R := |R0| + 1 with hRdef
  have hR : 0 < R := by positivity
  have hsub : (Set.Icc (-R) R)ᶜ ⊆ (Set.Icc (-R0) R0)ᶜ := by
    refine Set.compl_subset_compl.2 fun x hx => ⟨?_, ?_⟩
    · have := le_abs_self R0; linarith [hx.1]
    · have := le_abs_self R0; linarith [hx.2]
  have hs : ∀ᵐ x ∂L, x ∈ Set.Icc (-R) R := mem_ae_iff.2 (measure_mono_null hsub h1)
  have hs' : ∀ᵐ x ∂L', x ∈ Set.Icc (-R) R := mem_ae_iff.2 (measure_mono_null hsub h2)
  have hI : ∀ f : ℝ → ℝ, Continuous f → Integrable f L := fun f hf => integrable_of_ae_Icc hs hf
  have hI' : ∀ f : ℝ → ℝ, Continuous f → Integrable f L' :=
    fun f hf => integrable_of_ae_Icc hs' hf
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / δ)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hhδ : hh R N < δ := by
    unfold hh
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hεg : ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R, |x - y| ≤ hh R N →
      |φ x - φ y| ≤ ε := fun x hx y hy hxy =>
    (hU x hx y hy (by rw [Real.dist_eq]; linarith)).le
  have hB := fun x (hx : x ∈ Set.Icc (-R) R) => gg_bounds φ hφ hR hN0 hεg hx
  have hgc := gg_continuous φ (R := R) (N := N)
  have step1 : ∫ x, φ x ∂L ≤ ∫ x, gg φ R N x ∂L :=
    integral_mono_ae hiL (hI _ hgc) (by filter_upwards [hs] with x hx using (hB x hx).1)
  have step3 : ∫ x, gg φ R N x ∂L' ≤ ∫ x, φ x ∂L' + ε := by
    have : ∫ x, gg φ R N x ∂L' ≤ ∫ x, (φ x + ε) ∂L' := integral_mono_ae (hI' _ hgc) (hiL'.add (integrable_const ε) : Integrable (fun x => φ x + ε) L')
      (by filter_upwards [hs'] with x hx using (hB x hx).2)
    rw [integral_add hiL' (integrable_const _), integral_const] at this
    simpa using this
  have step2 : ∫ x, gg φ R N x ∂L ≤ ∫ x, gg φ R N x ∂L' := by
    rw [integral_gg φ hI, integral_gg φ hI', hmean]
    exact add_le_add_right (sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hSL _) (sub_nonneg.2 (ss_mono φ hφ hR hN0 i))) _
  linarith

/-! ### Unconditional versions of results of `NormAtom` -/

/-- **Proposition `nc:prop:atom` (b)**, unconditionally: for `n ≥ 3`, `0 < p < 1`, `0 ≤ c < 1/2`
and `n μ ≥ √(n - 1)`, relation (`nc:eq:cx`) holds for `F₀ = p δ_c + (1 - p) U[0,1]`. -/
theorem atom_cx_uncond {n : ℕ} (hn : 3 ≤ n) {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc0 : 0 ≤ c) (hc : c < 1 / 2) (hb : Real.sqrt ((n : ℝ) - 1) ≤ n * (p * c + (1 - p) / 2)) :
    CxCond n (atomUnif p c) (p * c + (1 - p) / 2) :=
  atom_cx stoploss_cx hn hp0 hp1 hc0 hc hb

/-- **Corollary `nc:cor:least`, second statement, explicit form**, with relation (`nc:eq:cx`)
unconditional; the norm inequalities still use the cited result `H_shmalo26b`. -/
theorem cor_least_explicit_uncond {n0 : ℕ} (hn0 : 3 ≤ n0) {p β c : ℝ} (hp : 1 - 2 / n0 < p)
    (hp1 : p < 1) (hβ0 : 0 < β) (hβ : β ≤ (3 / 2 - Real.sqrt 2) / (3 * p))
    (hc : c = 1 / 2 - β) :
    (0 < c ∧ c < 1 / 2) ∧
    (∀ n, 3 ≤ n → CxCond n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (H_shmalo26b → ∀ n, 3 ≤ n → NormIneqs n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (∀ n : ℕ, 3 ≤ n → MeanCond n 0 1 (p * c + (1 - p) / 2)) ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ n0 → ¬ CompletelyMixable n (atomUnif p c) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cor_least_explicit hn0 hp hp1 hβ0 hβ hc
  exact ⟨h1, h2 stoploss_cx, h3 stoploss_cx, h4, h5⟩

/-- **Corollary `nc:cor:least`, second statement**, with relation (`nc:eq:cx`) unconditional:
for every `n₀` there are `p` and `c` such that `F₀` satisfies (`nc:eq:cx`), the norm
inequalities (given the cited result `H_shmalo26b`) and the mean condition for every `n ≥ 3`,
while it is not `n`-completely mixable for any `1 ≤ n ≤ n₀`. -/
theorem cor_least_exists_uncond (n0 : ℕ) : ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ c < 1 / 2 ∧
    (∀ n, 3 ≤ n → CxCond n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (H_shmalo26b → ∀ n, 3 ≤ n → NormIneqs n (atomUnif p c) (p * c + (1 - p) / 2)) ∧
    (∀ n : ℕ, 3 ≤ n → MeanCond n 0 1 (p * c + (1 - p) / 2)) ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ n0 → ¬ CompletelyMixable n (atomUnif p c) := by
  obtain ⟨p, c, hp0, hp1, hc0, hc1, h2, h3, h4, h5⟩ := cor_least_exists n0
  exact ⟨p, c, hp0, hp1, hc0, hc1, h2 stoploss_cx, h3 stoploss_cx, h4, h5⟩

end Mixes.StopLoss
