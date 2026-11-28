import Mixes.AsymGeneral
import Mixes.AsymBridge

/-!
# Theorem `as:thm:general` with the sharp rate `κ < qH/(4d)`

The proof of Theorem `as:thm:general` ends with: the theorem follows with
any `κ < qH/(4d)` and `N` large enough, where `F ∗ F ≥ q U(Q')` for a cube `Q'` of half-side
`H`. `AsymGeneral.thm_general` proves the theorem with the fixed choice `κ = qH/(8d)`. This file
proves the sharper statement.

* `thm_general_rate_of`: given `F ∗ F ≥ q U(c + [-H, H]^d)` (with `H, q > 0`), for every
  `0 < κ < qH/(4d)` there is `N` such that for `n ≥ N` the aggregation set `𝒜_n(F)` contains
  every probability measure with mean `nμ` supported in `nμ + [-κn, κn]^d`.
* `thm_general_rate`: under the hypotheses of `AsymBridge.thm_general_b`, there are `c`, `H > 0`
  and `q ∈ (0, 1]` with `F ∗ F ≥ q U(c + [-H, H]^d)` such that the conclusion holds for every
  `0 < κ < qH/(4d)`.
* `cor_order_rate_of`, `cor_order_rate`: Corollary `as:cor:order` with the same rate.

No hypothesis: Theorem `as:thm:window` enters through `AsymBridge.h_thm_window`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric Pointwise

noncomputable section

namespace Mixes.AsymRate

open Mixes.AsymGeneral

variable {d : ℕ}

/-- The mass inequality `q ≤ 1` from `q U(Q) ≤ G` for a probability measure `G`. -/
lemma q_le_one (hd : 0 < d) {G : Measure (Rd d)} [IsProbabilityMeasure G] {c0 : Rd d} {H q : ℝ}
    (hH : 0 < H) (hunif : ENNReal.ofReal q • unifSet (box c0 (fun _ => H)) ≤ G) : q ≤ 1 := by
  have hV0 : volume (box c0 (fun _ => H)) ≠ 0 := (vol_box_pos hH).ne'
  have hVt : volume (box c0 (fun _ => H)) ≠ ⊤ := (vol_box_lt_top hd hH.le).ne
  have h1 := hunif (box c0 (fun _ => H))
  rw [smul_apply, unifSet, smul_apply,
    Measure.restrict_apply (measurableSet_box _ _), Set.inter_self, smul_eq_mul, smul_eq_mul,
    ENNReal.inv_mul_cancel hV0 hVt, mul_one] at h1
  have h2 := ENNReal.ofReal_le_one.1 (h1.trans prob_le_one)
  exact h2

/-- **Theorem `as:thm:general` with the rate `κ < qH/(4d)`**, explicit form. Let `F` be a
probability measure on `ℝ^d`, `d ≥ 1`, with bounded support and mean `μ`, and suppose
`F ∗ F ≥ q U(c + [-H, H]^d)` with `H > 0` and `q > 0`. Then for every `κ` with
`0 < κ < qH/(4d)` there is `N` such that for every `n ≥ N` the aggregation set `𝒜_n(F)`
contains every probability measure with mean `nμ` supported in `nμ + [-κn, κn]^d`. -/
theorem thm_general_rate_of (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (c0 : Rd d) {H q : ℝ} (hH : 0 < H) (hq : 0 < q)
    (hunif : ENNReal.ofReal q • unifSet (box c0 (fun _ => H)) ≤ conv F)
    (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ < q * H / (4 * d)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
      ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
      ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 → ν ∈ AggSet n F := by
  have hW := AsymBridge.h_thm_window d
  have hq1 : q ≤ 1 := q_le_one hd hH hunif
  obtain ⟨S, hSb, hS⟩ := hb
  set K := closure S
  have hKc : IsCompact K := hSb.isCompact_closure
  have hK : F Kᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 subset_closure) hS
  set R := Metric.diam K
  have hR0 : 0 ≤ R := Metric.diam_nonneg
  have hR : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R := fun x hx y hy =>
    Metric.dist_le_diam_of_mem hKc.isBounded hx hy
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ K, ‖x‖ ≤ M := hKc.isBounded.exists_norm_le
  have hint : Integrable (fun x => x) F := integrable_of_null_compl hK hM
  set μ := ∫ x, x ∂F with hμ
  have hadd : Measurable (fun p : Rd d × Rd d => p.1 + p.2) := by fun_prop
  have hmeanC : ∫ x, x ∂(conv F) = (2 : ℝ) • μ := by
    rw [conv, integral_map (f := fun x : Rd d => x) hadd.aemeasurable (by fun_prop),
      integral_add (hint.comp_fst F) (hint.comp_snd F), integral_fun_fst (fun x : Rd d => x),
      integral_fun_snd (fun x : Rd d => x)]
    simp [two_smul, μ]
  have hKK : (F.prod F) (K ×ˢ K)ᶜ = 0 := by
    rw [Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hK, zero_mul]
    · rw [Measure.prod_prod, hK, mul_zero]
  have hsuppC : SuppDiam (conv F) (2 * R) := by
    refine ⟨K + K, ?_, ?_⟩
    · have hcl : IsClosed (K + K) := (hKc.add hKc).isClosed
      rw [conv, Measure.map_apply hadd hcl.measurableSet.compl]
      exact measure_mono_null (fun p (hp : p ∈ (fun p : Rd d × Rd d => p.1 + p.2) ⁻¹' (K + K)ᶜ) =>
        show p ∈ (K ×ˢ K)ᶜ from fun hpK => hp (Set.add_mem_add hpK.1 hpK.2)) hKK
    · rintro x ⟨a, ha, b, hb, rfl⟩ y ⟨a', ha', b', hb', rfl⟩
      calc dist (a + b) (a' + b') ≤ dist a a' + dist b b' := dist_add_add_le _ _ _ _
        _ ≤ R + R := add_le_add (hR a ha a' ha') (hR b hb b' hb')
        _ = 2 * R := by ring
  set cc := cdConst d
  have hcc : 0 ≤ cc := by simp only [cc, cdConst]; split_ifs <;> positivity
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set ε := q * H / (4 * d) - κ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set st := κ + H + R + 2 * cc * R with hst
  set X := 6 * d / q + st / (2 * ε) with hX
  refine ⟨2 * ⌈X⌉₊ + 2, fun n hn ν hν hmean hsupp => ?_⟩
  set n' := n / 2 with hn'def
  have hn'X : X ≤ n' := by
    have h1 : ⌈X⌉₊ ≤ n' := by omega
    exact (Nat.le_ceil X).trans (by exact_mod_cast h1)
  have hn2 : n = 2 * n' ∨ n = 2 * n' + 1 := by omega
  have hnle : (n : ℝ) ≤ 2 * n' + 1 := by rcases hn2 with h | h <;> rw [h] <;> push_cast <;> linarith
  set m' := ⌊q * (n' : ℝ)⌋₊ / d with hm'
  have hm'r : q * n' / d - 2 ≤ (m' : ℝ) := floor_div_ge hd (by positivity)
  have hXst : st / (2 * ε) ≤ n' := le_trans (by
    rw [hX]; have : 0 ≤ 6 * (d : ℝ) / q := by positivity
    linarith) hn'X
  have hX6 : 6 * (d : ℝ) / q ≤ n' := le_trans (by
    rw [hX]; have : 0 ≤ st / (2 * ε) := by positivity
    linarith) hn'X
  have hm'4 : 4 ≤ m' := by
    have : (6 : ℝ) ≤ q * n' / d := by
      rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ hq] at hX6; linarith
    have : (4 : ℝ) ≤ m' := by linarith
    exact_mod_cast this
  have hst' : st ≤ 2 * ε * n' := by
    rw [div_le_iff₀ (by positivity)] at hXst; linarith
  have hρ : κ * n + R ≤ m' * H / 2 - cc * (2 * R) := by
    have h1 : κ * n ≤ κ * (2 * n' + 1) := mul_le_mul_of_nonneg_left hnle hκ0.le
    have h2 : (q * n' / d - 2) * H / 2 ≤ m' * H / 2 := by
      have := mul_le_mul_of_nonneg_right hm'r hH.le; linarith
    have h3 : κ * (2 * n' + 1) = 2 * (q * H / (4 * d)) * n' - 2 * ε * n' + κ := by
      rw [hε]; ring
    have h4 : (q * n' / d - 2) * H / 2 = 2 * (q * H / (4 * d)) * n' - H := by
      field_simp; ring
    rw [hst] at hst'
    linarith
  have hρ0 : 0 ≤ (m' : ℝ) * H / 2 - cc * (2 * R) := by
    have : 0 ≤ κ * n := by positivity
    linarith
  have hwin : ∀ ν0 : Measure (Rd d), IsProbabilityMeasure ν0 →
      ∫ x, x ∂ν0 = ((2 * n' : ℕ) : ℝ) • μ →
      ν0 (box (((2 * n' : ℕ) : ℝ) • μ) (fun _ => m' * H / 2 - cc * (2 * R)))ᶜ = 0 →
      ν0 ∈ AggSet (2 * n') F := by
    intro ν0 h0 hm0 hs0
    apply aggSet_conv_subset
    refine hW (conv F) (2 * R) c0 (fun _ => H) q n' hsuppC (fun _ => hH) hq hq1 hunif hm'4
      (fun _ => hρ0) ν0 h0 ?_ ?_
    · rw [hm0, hmeanC, smul_smul]; push_cast; ring_nf
    · rw [hmeanC, smul_smul]
      convert hs0 using 4
      push_cast; ring_nf
  rcases hn2 with h | h
  · rw [h] at hmean hsupp ⊢
    refine hwin ν hν hmean (measure_mono_null (Set.compl_subset_compl.2 (box_mono fun _ => ?_))
      hsupp)
    rw [← h]; linarith
  · rw [h]
    have hνprob := hν
    apply aggSet_succ_of_sub
    set B' := box ((n : ℝ) • μ) (fun _ => κ * n)
    have hintν : Integrable (fun x => x) ν := by
      refine integrable_of_null_compl hsupp (M := ‖(n : ℝ) • μ‖ + d * (κ * n)) fun x hx => ?_
      have := box_subset_closedBall hd _ (by positivity) hx
      rw [mem_closedBall, dist_eq_norm] at this
      calc ‖x‖ = ‖(x - (n : ℝ) • μ) + (n : ℝ) • μ‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - (n : ℝ) • μ‖ + ‖(n : ℝ) • μ‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hsub : Measurable (fun p : Rd d × Rd d => p.1 - p.2) := by fun_prop
    apply hwin _ inferInstance
    · rw [integral_map (f := fun x : Rd d => x) hsub.aemeasurable (by fun_prop),
        integral_sub (hintν.comp_fst F) (hint.comp_snd ν), integral_fun_fst (fun x : Rd d => x),
        integral_fun_snd (fun x : Rd d => x), hmean]
      simp only [probReal_univ, one_smul]
      rw [← hμ, h]; push_cast
      rw [add_smul, one_smul, add_sub_cancel_right]
    · have hbm : MeasurableSet (box (((2 * n' : ℕ) : ℝ) • μ)
          (fun _ => (m' : ℝ) * H / 2 - cc * (2 * R)))ᶜ := (measurableSet_box _ _).compl
      rw [Measure.map_apply hsub hbm]
      have hBK : (ν.prod F) (B' ×ˢ K)ᶜ = 0 := by
        rw [Set.compl_prod_eq_union]
        refine measure_union_null ?_ ?_
        · rw [Measure.prod_prod, hsupp, zero_mul]
        · rw [Measure.prod_prod, hK, mul_zero]
      refine measure_mono_null (fun p (hp : p ∈ (fun p : Rd d × Rd d => p.1 - p.2) ⁻¹'
        (box (((2 * n' : ℕ) : ℝ) • μ) (fun _ => (m' : ℝ) * H / 2 - cc * (2 * R)))ᶜ) =>
        show p ∈ (B' ×ˢ K)ᶜ from fun hpK => hp ?_) hBK
      intro i
      have h1 := hpK.1 i
      have h2 : |p.2 i - μ i| ≤ R := by
        have := PiLp.norm_apply_le (p.2 - μ) i
        rw [Real.norm_eq_abs] at this
        exact le_trans (by simpa using this) (norm_sub_mean_le hK hR hint hpK.2)
      have h3 : (p.1 - p.2) i - (((2 * n' : ℕ) : ℝ) • μ) i =
          (p.1 i - ((n : ℝ) • μ) i) - (p.2 i - μ i) := by
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, h]; push_cast; ring
      rw [h3]
      calc |(p.1 i - ((n : ℝ) • μ) i) - (p.2 i - μ i)|
          ≤ |p.1 i - ((n : ℝ) • μ) i| + |p.2 i - μ i| := abs_sub _ _
        _ ≤ κ * n + R := add_le_add h1 h2
        _ ≤ _ := hρ

/-- **Theorem `as:thm:general` with the rate `κ < qH/(4d)`** (no hypothesis). Let `F` be a
probability measure on `ℝ^d`, `d ≥ 1`, with bounded support, mean `μ`, and a nonzero absolutely
continuous part. Then there are `c`, `H > 0` and `q ∈ (0, 1]` with `F ∗ F ≥ q U(c + [-H, H]^d)`
such that for every `κ` with `0 < κ < qH/(4d)` there is `N` such that for every `n ≥ N` the
aggregation set `𝒜_n(F)` contains every probability measure with mean `nμ` supported in
`nμ + [-κn, κn]^d`. -/
theorem thm_general_rate (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ (c0 : Rd d) (H q : ℝ), 0 < H ∧ 0 < q ∧ q ≤ 1 ∧
      ENNReal.ofReal q • unifSet (box c0 (fun _ => H)) ≤ conv F ∧
      ∀ κ : ℝ, 0 < κ → κ < q * H / (4 * d) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
          ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
          ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 → ν ∈ AggSet n F := by
  obtain ⟨c0, H, hH, q, hq, hq1, hunif⟩ := conv_ge_unif hd F hac
  exact ⟨c0, H, q, hH, hq, hq1, hunif, fun κ hκ0 hκ =>
    thm_general_rate_of hd F hb c0 hH hq hunif κ hκ0 hκ⟩

/-- **Corollary `as:cor:order` with the rate `κ < qH/(4d)`**, explicit form. Under the
hypotheses of `thm_general_rate_of`, for every `0 < κ < qH/(4d)` there is `N` such that for
`n ≥ N` the point mass at `nμ` is the smallest element of `𝒜_n(F)` in convex order, and a
probability measure supported in `nμ + [-κn, κn]^d` belongs to `𝒜_n(F)` if and only if its mean
is `nμ`. -/
theorem cor_order_rate_of (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (c0 : Rd d) {H q : ℝ} (hH : 0 < H) (hq : 0 < q)
    (hunif : ENNReal.ofReal q • unifSet (box c0 (fun _ => H)) ≤ conv F)
    (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ < q * H / (4 * d)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Measure.dirac ((n : ℝ) • ∫ x, x ∂F) ∈ AggSet n F ∧
        ∀ ν ∈ AggSet n F, CxLe (Measure.dirac ((n : ℝ) • ∫ x, x ∂F)) ν) ∧
      ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
        ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 →
        (ν ∈ AggSet n F ↔ ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F) := by
  obtain ⟨S, hSb, hS⟩ := hb
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ S, ‖x‖ ≤ M := hSb.exists_norm_le
  have hint : Integrable (fun x => x) F := integrable_of_null_compl hS hM
  obtain ⟨N, hN⟩ := thm_general_rate_of hd F ⟨S, hSb, hS⟩ c0 hH hq hunif κ hκ0 hκ
  refine ⟨N, fun n hn => ⟨⟨?_, fun ν hν => ?_⟩, fun ν hνp hsupp => ⟨fun h =>
    (aggSet_mean hint h).2.2, fun h => hN n hn ν hνp h hsupp⟩⟩⟩
  · refine hN n hn _ inferInstance (by rw [integral_dirac]) ?_
    rw [Measure.dirac_apply' _ (measurableSet_box _ _).compl, Set.indicator_of_notMem]
    simp only [Set.mem_compl_iff, not_not]
    intro i
    simp only [sub_self, abs_zero]
    positivity
  · obtain ⟨hνp, hνi, hνm⟩ := aggSet_mean hint hν
    rw [← hνm]
    exact dirac_cxLe hνi

/-- **Corollary `as:cor:order` with the rate `κ < qH/(4d)`** (no hypothesis), for `F` as in
`thm_general_rate`. -/
theorem cor_order_rate (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ (c0 : Rd d) (H q : ℝ), 0 < H ∧ 0 < q ∧ q ≤ 1 ∧
      ENNReal.ofReal q • unifSet (box c0 (fun _ => H)) ≤ conv F ∧
      ∀ κ : ℝ, 0 < κ → κ < q * H / (4 * d) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (Measure.dirac ((n : ℝ) • ∫ x, x ∂F) ∈ AggSet n F ∧
            ∀ ν ∈ AggSet n F, CxLe (Measure.dirac ((n : ℝ) • ∫ x, x ∂F)) ν) ∧
          ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
            ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 →
            (ν ∈ AggSet n F ↔ ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F) := by
  obtain ⟨c0, H, hH, q, hq, hq1, hunif⟩ := conv_ge_unif hd F hac
  exact ⟨c0, H, q, hH, hq, hq1, hunif, fun κ hκ0 hκ =>
    cor_order_rate_of hd F hb c0 hH hq hunif κ hκ0 hκ⟩

end Mixes.AsymRate
