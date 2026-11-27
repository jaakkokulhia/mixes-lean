import Mixes.AsymThm
import Mixes.AsymWindow
import Mixes.AsymGeneral
import Mixes.AsymHetero
import Mixes.AsymThree
import Mixes.NormUnimodal
import Mixes.StopLoss
import Mixes.ConvSq
import Mixes.Steinitz
import Mixes.TwoStepBorel

/-!
# Bridges for Section `as:sec:asym` and Section `nc:sec:norm` (draft 14)

Discharges the cross-agent hypotheses of `AsymGeneral`, `AsymHetero`, `AsymThree` and
`NormUnimodal` with the results proved in `AsymThm`, `AsymWindow`, `Steinitz`, `StopLoss`, `ConvSq`, and
restates the main theorems without them (suffix `_b`). Remaining hypotheses: `Large.JohnThm`
(John's theorem, only in `cor_body_b`) and `NormAtom.H_shmalo26b` (cited, only in the norm
inequality results). `H_twoStepBorel` is discharged by `TwoStepBorel.twoStepBorel`, `H_convSq` by
`ConvSq.convSq`, `H_stoploss_cx` by `StopLoss.stoploss_cx`, `H_thm_window` by
`Steinitz.thm_window_all`; no `_b` theorem uses the false `AsymThm.H_steinitz` or
`AsymThree.H_conc_a`.

* `AsymGeneral`: `h_thm_window` (`H_thm_window d`, every `d`, from `Steinitz.thm_window_all`), `h_thm_window_one`
  (`H_thm_window 1`, no hypothesis); `thm_general_b`, `thm_general_mix_b`, `cor_order_b`,
  `cor_body_b` (no hypothesis except `JohnThm` for `cor_body_b`); the `d = 1` versions
  `thm_general_one_b`, `thm_general_mix_one_b`, `cor_order_one_b` are kept (now redundant).
* `AsymHetero`: `h_lem_conc_a`, `h_prop_window`; `thm_hetero_b`, `thm_hetero_strong_b`,
  `thm_hetero_jointlyMixable_b`, `cor_hetero_b`, `cor_hetero_jointlyMixable_b`, `cor_hetero_n_b`.
* `AsymThree`: `h_window_line`. **Finding**: `AsymThree.H_conc_a` is false (`not_H_conc_a`: for
  `k = 0` and `ℓ < 0` its conclusion requires `|0| ≤ ℓ`), so the theorems of `AsymThree` that
  take it are vacuous. `H_conc_a_fix` adds `0 ≤ ℓ` and is proved (`h_conc_a_fix`, from
  `AsymThm.lem_conc_a`); the engine and the theorems using it are re-proved here with it (proofs
  copied from `AsymThree`, `_fix`). Statement change: `prop_complete_b` and
  `prop_complete_dirac_b` assume `0 ≤ ℓ` (without it `prop_complete` is false for `K = r = 0`,
  `ℓ < 0`, where the window `[-ρ, ρ]`, `ρ = -ℓ > 0`, is not `{0}`). Main theorems: `prop_complete_b`, `prop_complete_dirac_b`,
  `four_uniform_jointlyMixable_b`, `cor_repeat_b` (no hypothesis left), `cor_three_b`,
  `cor_three_mixable_b`, `cor_three_a_b`, `cor_three_b_b`, `cor_three_c_b`, `prop_three_b`,
  `rem_three_b` (no hypothesis).
* `NormUnimodal`: `h_as_cor_three_a`, `h_as_cor_three_b` (no hypothesis);
  `cxCond_of_SL_b`, `normIneqs_of_SL_b`, `cx_F1_F2_b`, `thm_unimodal_norm_b`, `cor_alln_norm_b`
  (`H_stoploss_cx` discharged by `StopLoss.stoploss_cx`), `cor_alln_mixable_b`,
  `threshold_unimodal_b`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Mixes.AsymBridge

/-! ## `AsymGeneral` -/

section General

open Mixes.AsymGeneral

/-- Theorem `as:thm:window` in `ℝ^d`, every `d`, no hypothesis (`Steinitz.thm_window_all`). -/
theorem h_thm_window (d : ℕ) : H_thm_window d :=
  Steinitz.thm_window_all d

/-- Theorem `as:thm:window` for `d = 1`, no hypothesis. -/
theorem h_thm_window_one : H_thm_window 1 := AsymThm.thm_window_d1_proved

variable {d : ℕ}

/-- **Theorem `as:thm:general`** (no hypothesis). -/
theorem thm_general_b (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, N ≤ n → ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
      ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
      ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 → ν ∈ AggSet n F :=
  thm_general hd (h_thm_window d) F hb hac

/-- **Theorem `as:thm:general`**, `d = 1`, no hypothesis. -/
theorem thm_general_one_b (F : Measure (Rd 1))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd 1), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, N ≤ n → ∀ ν : Measure (Rd 1), IsProbabilityMeasure ν →
      ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
      ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 → ν ∈ AggSet n F :=
  thm_general one_pos h_thm_window_one F hb hac

/-- **Theorem `as:thm:general`**, complete mixability (no hypothesis). -/
theorem thm_general_mix_b (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) : ∃ N : ℕ, ∀ n, N ≤ n → CompletelyMixable n F :=
  thm_general_mix hd (h_thm_window d) F hb hac

/-- **Theorem `as:thm:general`**, complete mixability, `d = 1`, no hypothesis. -/
theorem thm_general_mix_one_b (F : Measure (Rd 1))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd 1), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) : ∃ N : ℕ, ∀ n, N ≤ n → CompletelyMixable n F :=
  thm_general_mix one_pos h_thm_window_one F hb hac

/-- **Corollary `as:cor:order`** (no hypothesis). -/
theorem cor_order_b (hd : 0 < d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, N ≤ n →
      (Measure.dirac ((n : ℝ) • ∫ x, x ∂F) ∈ AggSet n F ∧
        ∀ ν ∈ AggSet n F, CxLe (Measure.dirac ((n : ℝ) • ∫ x, x ∂F)) ν) ∧
      ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
        ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 →
        (ν ∈ AggSet n F ↔ ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F) :=
  cor_order hd (h_thm_window d) F hb hac

/-- **Corollary `as:cor:order`**, `d = 1`, no hypothesis. -/
theorem cor_order_one_b (F : Measure (Rd 1))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd 1), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, N ≤ n →
      (Measure.dirac ((n : ℝ) • ∫ x, x ∂F) ∈ AggSet n F ∧
        ∀ ν ∈ AggSet n F, CxLe (Measure.dirac ((n : ℝ) • ∫ x, x ∂F)) ν) ∧
      ∀ ν : Measure (Rd 1), IsProbabilityMeasure ν →
        ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 →
        (ν ∈ AggSet n F ↔ ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F) :=
  cor_order one_pos h_thm_window_one F hb hac

/-- **Corollary `as:cor:body`**, given John's theorem only. -/
theorem cor_body_b (hd : 2 ≤ d) (hJ : Large.JohnThm (Rd d)) :
    ∀ K : Set (Rd d), IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∀ n, Nstar d ≤ n → CompletelyMixable n (unifSet K) :=
  cor_body hd hJ (h_thm_window d)

end General

/-! ## `AsymHetero` -/

section Hetero

open Mixes.AsymHetero

/-- Lemma `as:lem:conc`(a) in the form of `AsymHetero.H_lem_conc_a`. -/
theorem h_lem_conc_a : H_lem_conc_a := by
  intro k ℓ T hℓ hT hc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨Measure.dirac (fun _ => 0), inferInstance, fun j => j.elim0, 0, ?_⟩
    refine Filter.Eventually.of_forall fun x => ?_
    simp [hℓ]
  · have := hT
    obtain ⟨P, hP, hm, hα, -⟩ := AsymThm.lem_conc_a hk T hc
    exact ⟨P, hP, hm, hα⟩

/-- Proposition `as:prop:window` (`d = 1`, `m ≥ 4`) in the form of `AsymHetero.H_prop_window`. -/
theorem h_prop_window : H_prop_window := by
  intro m c H ν hm hH hν hsupp hmean
  refine AsymWindow.propWindowReal m c H ν hH hm hν ?_ hmean
  have : ∀ᵐ x ∂ν, x ∈ Icc (m * c - m * H / 2) (m * c + m * H / 2) := by
    rw [ae_iff]; exact hsupp
  filter_upwards [this] with x hx
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- **Theorem `as:thm:hetero`**, strong form, no hypothesis. -/
theorem thm_hetero_strong_b {b m1 m2 n r : ℕ}
    (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ ρ : ℝ} (hH : 0 < H)
    (h1 : (m1 - 1 : ℝ) * H ≥ 4 * (ℓ - H)) (hρ : ρ + ℓ ≤ m2 * H / 2) (hn : n = b * (m1 + m2))
    (F : Fin (n + r) → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0) (c : Fin n → ℝ)
    (hU : ∀ j : Fin n, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (Fin.castAdd r j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc ((∑ i, ∫ x, x ∂(F i)) - ρ) ((∑ i, ∫ x, x ∂(F i)) + ρ))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = ∑ i, ∫ x, x ∂(F i)) : ν ∈ AggSet F :=
  thm_hetero_strong h_lem_conc_a h_prop_window hb hm1 hm2 hH h1 hρ hn F hF hFc c hU ν hνc hνm

/-- **Theorem `as:thm:hetero`** (the paper's statement), no hypothesis. -/
theorem thm_hetero_b {b m1 m2 n r : ℕ}
    (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ ρ : ℝ} (hH : 0 < H) (hℓ : 0 < ℓ)
    (h1 : (m1 - 1 : ℝ) * H ≥ 4 * (ℓ - H)) (hρ : ρ = m2 * H / 2 - ℓ - H) (hρ0 : 0 ≤ ρ)
    (hn : n = b * (m1 + m2))
    (F : Fin (n + r) → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0) (c : Fin n → ℝ)
    (hU : ∀ j : Fin n, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (Fin.castAdd r j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc ((∑ i, ∫ x, x ∂(F i)) - ρ) ((∑ i, ∫ x, x ∂(F i)) + ρ))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = ∑ i, ∫ x, x ∂(F i)) : ν ∈ AggSet F :=
  thm_hetero h_lem_conc_a h_prop_window hb hm1 hm2 hH hℓ h1 hρ hρ0 hn F hF hFc c hU ν hνc hνm

/-- **Theorem `as:thm:hetero`**, joint mixability, no hypothesis. -/
theorem thm_hetero_jointlyMixable_b
    {b m1 m2 n r : ℕ} (hb : 2 ≤ b) (hm1 : 2 ≤ m1) (hm2 : 4 ≤ m2) {H ℓ : ℝ} (hH : 0 < H)
    (h1 : (m1 - 1 : ℝ) * H ≥ 4 * (ℓ - H)) (hρ0 : 0 ≤ m2 * H / 2 - ℓ - H)
    (hn : n = b * (m1 + m2))
    (F : Fin (n + r) → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, ∃ α, F i (Icc α (α + ℓ))ᶜ = 0) (c : Fin n → ℝ)
    (hU : ∀ j : Fin n, (b : ℝ≥0∞)⁻¹ • unifI (c j - H) (c j + H) ≤ F (Fin.castAdd r j)) :
    JointlyMixable F :=
  thm_hetero_jointlyMixable h_lem_conc_a h_prop_window hb hm1 hm2 hH h1 hρ0 hn F hF hFc c hU

/-- **Corollary `as:cor:hetero`**, no hypothesis. -/
theorem cor_hetero_b {n r : ℕ} {u v q : ℝ}
    (huv : u < v) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, F i (Icc u v)ᶜ = 0) (hFq : ∀ i, ENNReal.ofReal q • unifI u v ≤ F i)
    (G : Fin r → Measure ℝ) (hG : ∀ j, IsProbabilityMeasure (G j))
    (hGc : ∀ j, ∃ α, G j (Icc α (α + (v - u)))ᶜ = 0)
    (hm : 11 ≤ n / ⌈1 / q⌉₊) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνc : ν (Icc ((∑ i, ∫ x, x ∂(F i)) + (∑ j, ∫ x, x ∂(G j)) -
        (((n / ⌈1 / q⌉₊ : ℕ) : ℝ) - 11) * (v - u) / 4)
      ((∑ i, ∫ x, x ∂(F i)) + (∑ j, ∫ x, x ∂(G j)) +
        (((n / ⌈1 / q⌉₊ : ℕ) : ℝ) - 11) * (v - u) / 4))ᶜ = 0)
    (hνm : ∫ x, x ∂ν = (∑ i, ∫ x, x ∂(F i)) + ∑ j, ∫ x, x ∂(G j)) :
    ν ∈ AggSet (Sum.elim F G) :=
  cor_hetero h_lem_conc_a h_prop_window huv hq0 hq1 F hF hFc hFq G hG hGc hm ν hνc hνm

/-- **Corollary `as:cor:hetero`**, joint mixability, no hypothesis. -/
theorem cor_hetero_jointlyMixable_b {n r : ℕ}
    {u v q : ℝ} (huv : u < v) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, F i (Icc u v)ᶜ = 0) (hFq : ∀ i, ENNReal.ofReal q • unifI u v ≤ F i)
    (G : Fin r → Measure ℝ) (hG : ∀ j, IsProbabilityMeasure (G j))
    (hGc : ∀ j, ∃ α, G j (Icc α (α + (v - u)))ᶜ = 0)
    (hm : 11 ≤ n / ⌈1 / q⌉₊) : JointlyMixable (Fin.append F G) :=
  cor_hetero_jointlyMixable h_lem_conc_a h_prop_window huv hq0 hq1 F hF hFc hFq G hG hGc hm

/-- **Corollary `as:cor:hetero`**, last sentence, no hypothesis. -/
theorem cor_hetero_n_b {n : ℕ} {u v q : ℝ}
    (huv : u < v) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, IsProbabilityMeasure (F i))
    (hFc : ∀ i, F i (Icc u v)ᶜ = 0) (hFq : ∀ i, ENNReal.ofReal q • unifI u v ≤ F i)
    (hn : 11 * ⌈1 / q⌉₊ ≤ n) : JointlyMixable F :=
  cor_hetero_n h_lem_conc_a h_prop_window huv hq0 hq1 F hF hFc hFq hn

end Hetero

/-! ## `AsymThree` -/

section Three

open Mixes.AsymThree

/-- Proposition `as:prop:window` (`d = 1`, `m ≥ 4`) in the form of `AsymThree.H_window_line`. -/
theorem h_window_line : H_window_line := by
  intro m c H ν hm hH hν hmean hsupp
  exact h_prop_window m c H ν hm hH hν hsupp hmean

/-- **Finding**: `AsymThree.H_conc_a` is false (`k = 0`, `ℓ = -1`: the empty family satisfies
the premises, but the conclusion requires `|0 - 0| ≤ -1` almost surely). -/
theorem not_H_conc_a : ¬ H_conc_a := by
  intro h
  obtain ⟨P, hP, -, α, hα⟩ := h 0 (-1) Fin.elim0 (fun j => j.elim0) (fun j => j.elim0)
  have : ∀ᵐ x ∂P, False := by
    filter_upwards [hα] with x hx
    simp at hx
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
  exact IsProbabilityMeasure.ne_zero P this

/-- `AsymThree.H_conc_a` with the missing condition `0 ≤ ℓ` (Lemma `as:lem:conc`(a)). -/
def H_conc_a_fix : Prop :=
  ∀ (k : ℕ) (ℓ : ℝ) (T : Fin k → Measure ℝ), 0 ≤ ℓ → (∀ j, IsProbabilityMeasure (T j)) →
    (∀ j, ∃ a, T j (Icc a (a + ℓ))ᶜ = 0) →
    ∃ P : Measure (Fin k → ℝ), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = T j) ∧
      ∃ α : ℝ, ∀ᵐ x ∂P, ∑ j, x j ∈ Icc α (α + ℓ) ∧ |∑ j, x j - ∑ j, ∫ y, y ∂(T j)| ≤ ℓ

theorem h_conc_a_fix : H_conc_a_fix := by
  intro k ℓ T hℓ hT hc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨Measure.dirac (fun _ => 0), inferInstance, fun j => j.elim0, 0, ?_⟩
    refine Filter.Eventually.of_forall fun x => ?_
    simp [hℓ]
  · have := hT
    obtain ⟨P, hP, hm, ⟨α, hα⟩, hdev⟩ := AsymThm.lem_conc_a hk T hc
    exact ⟨P, hP, hm, α, by filter_upwards [hα, hdev] with x h1 h2 using ⟨h1, h2⟩⟩


/-! ### Re-proofs with `H_conc_a_fix` (copied from `AsymThree`) -/

lemma conc_fintype_fix (hC : H_conc_a_fix) {ι : Type*} [Fintype ι] (T : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (T i)] {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hT : ∀ i, ∃ a, T i (Icc a (a + ℓ))ᶜ = 0) :
    ∃ P : Measure (ι → ℝ), IsProbabilityMeasure P ∧ (∀ i, P.map (fun x => x i) = T i) ∧
      ∃ α : ℝ, ∀ᵐ x ∂P, ∑ i, x i ∈ Icc α (α + ℓ) := by
  let e := Fintype.equivFin ι
  obtain ⟨P, hP, hm, α, hα⟩ := hC (Fintype.card ι) ℓ (fun j => T (e.symm j)) hℓ
    (fun j => inferInstance) (fun j => hT _)
  have hme : Measurable (fun (x : Fin (Fintype.card ι) → ℝ) (i : ι) => x (e i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  refine ⟨P.map (fun x i => x (e i)), inferInstance, fun i => ?_, α, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hme]
    have := hm (e i)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · rw [ae_map_iff hme.aemeasurable (measurable_sum_coord measurableSet_Icc)]
    filter_upwards [hα] with x hx
    rw [Equiv.sum_comp e (fun j => x j)]
    exact hx.1

theorem engine_fix (hC : H_conc_a_fix) {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hNpos : ∀ k, 0 < N k)
    (s ρ : ℝ) (hs : s = ∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = s)
    (hν : ν (Icc (s - ρ) (s + ρ))ᶜ = 0)
    (hBlock : ∀ (lam : Measure ℝ) (β : ℝ), IsProbabilityMeasure lam →
      ∫ x, x ∂lam = ∑ k, (⌊q k * N k⌋₊ : ℝ) * c k →
      ∑ k, (⌊q k * N k⌋₊ : ℝ) * c k ∈ Icc (β - ℓ) β → lam (Icc (β - ρ - ℓ) (β + ρ))ᶜ = 0 →
      lam ∈ aggSet (fun p : Σ k, Fin ⌊q k * N k⌋₊ => unifI (c p.1 - H p.1) (c p.1 + H p.1))) :
    ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) := by
  classical
  set m : Fin K → ℕ := fun k => ⌊q k * N k⌋₊ with hmdef
  have hmle : ∀ k, (m k : ℝ) ≤ q k * N k := fun k =>
    Nat.floor_le (mul_nonneg (hq0 k).le (Nat.cast_nonneg _))
  have hmN : ∀ k, m k ≤ N k := fun k => by
    have h1 : q k * N k ≤ N k := by
      have := hq1 k; have : (0 : ℝ) ≤ N k := Nat.cast_nonneg _; nlinarith
    have : (m k : ℝ) ≤ N k := (hmle k).trans h1
    exact_mod_cast this
  set n : Fin K → ℕ := fun k => N k - m k with hndef
  set U : Fin K → Measure ℝ := fun k => unifI (c k - H k) (c k + H k) with hUdef
  have hUp : ∀ k, IsProbabilityMeasure (U k) := fun k => unifI_isProb _ _
  choose T hTp hTs hTd using fun k => decomp (hGU k) (hmle k) (hmN k) (hNpos k)
  choose aG haG using hGℓ
  have hTℓ : ∀ k, T k (Icc (aG k) (aG k + ℓ))ᶜ = 0 := fun k => hTs k _ (haG k)
  have hUmean : ∀ k, ∫ x, x ∂(U k) = c k := fun k => by
    rw [hUdef]; dsimp only
    rw [integral_unifI (by linarith [hH k])]; ring
  have hTint : ∀ k, Integrable (fun x => x) (T k) := fun k => integrable_id_of_null (hTℓ k)
  have hGmean : ∀ k, (N k : ℝ) * ∫ x, x ∂(G k) = m k * c k + n k * ∫ x, x ∂(T k) := fun k => by
    rw [integral_decomp (hTd k) (integrable_unifI _ _ (by linarith [hH k])) (hTint k), hUmean k]
  -- the coupling of the `T_k` and the `F_j`
  set TF : (Σ k, Fin (n k)) ⊕ Fin r → Measure ℝ := Sum.elim (fun p => T p.1) F with hTFdef
  have hTFp : ∀ i, IsProbabilityMeasure (TF i) := by
    rintro (p | j)
    · simp only [hTFdef, Sum.elim_inl]; exact hTp p.1
    · simp only [hTFdef, Sum.elim_inr]; infer_instance
  have hTFℓ : ∀ i, ∃ a, TF i (Icc a (a + ℓ))ᶜ = 0 := by
    rintro (p | j)
    · exact ⟨_, hTℓ p.1⟩
    · exact hFℓ j
  obtain ⟨PY, hPY, hmY, α, hα⟩ := conc_fintype_fix hC TF hℓ hTFℓ
  set E := ∑ i, ∫ x, x ∂(TF i) with hEdef
  have hEsum : E = ∑ k, (n k : ℝ) * ∫ x, x ∂(T k) + ∑ j, ∫ x, x ∂(F j) := by
    simp [hEdef, hTFdef, Fintype.sum_sum_type, Fintype.sum_sigma, Finset.sum_const]
  have hint_coord : ∀ i, Integrable (fun x : _ → ℝ => x i) PY := fun i => by
    obtain ⟨a, ha⟩ := hTFℓ i
    exact integrable_coord_of_map i (hmY i) ha
  have hESY : ∫ x, ∑ i, x i ∂PY = E := by
    rw [integral_finsetSum _ (fun i _ => hint_coord i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_id_map (measurable_pi_apply i), hmY i]
  have hEmem : E ∈ Icc α (α + ℓ) := hESY ▸
    integral_mem_Icc_of_ae measurable_sum_coord.aestronglyMeasurable hα
  -- the product with the target
  set μ := PY.prod ν with hμdef
  have hμ1 : μ.map Prod.fst = PY := by simp [hμdef]
  have hμ2 : μ.map Prod.snd = ν := by simp [hμdef]
  set C := ∑ k, (m k : ℝ) * c k with hCdef
  have hsC : s = C + E := by
    rw [hs, hEsum, hCdef, ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hGmean k
  have h1 : ∀ᵐ ω ∂μ, ∑ i, ω.1 i ∈ Icc α (α + ℓ) :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hμ1]; exact hα)
  have h2 : ∀ᵐ ω ∂μ, ω.2 ∈ Icc (s - ρ) (s + ρ) :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hμ2]; exact ae_mem_of_null hν)
  have hDm : Measurable (fun ω : ((Σ k, Fin (n k)) ⊕ Fin r → ℝ) × ℝ => ω.2 - ∑ i, ω.1 i) :=
    measurable_snd.sub (measurable_sum_coord.comp measurable_fst)
  have hD : μ.map (fun ω => ω.2 - ∑ i, ω.1 i) ∈ aggSet (fun p : Σ k, Fin (m k) => U p.1) := by
    apply hBlock _ (s - α) inferInstance
    rotate_left
    · constructor <;> linarith [hEmem.1, hEmem.2]
    · apply map_null_of_ae hDm measurableSet_Icc
      filter_upwards [h1, h2] with ω h1 h2
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have hi1 : Integrable (fun ω : ((Σ k, Fin (n k)) ⊕ Fin r → ℝ) × ℝ => ω.2) μ :=
        integrable_of_ae_Icc measurable_snd.aestronglyMeasurable h2
      have hi2 : Integrable (fun ω : ((Σ k, Fin (n k)) ⊕ Fin r → ℝ) × ℝ => ∑ i, ω.1 i) μ :=
        integrable_of_ae_Icc (measurable_sum_coord.comp measurable_fst).aestronglyMeasurable h1
      rw [integral_id_map hDm, integral_sub hi1 hi2]
      have e1 : ∫ ω, ω.2 ∂μ = s := by
        rw [← hνm, ← hμ2, integral_id_map measurable_snd]
      have e2 : ∫ ω, ∑ i, ω.1 i ∂μ = E := by
        rw [← hESY, ← hμ1, integral_map measurable_fst.aemeasurable
          measurable_sum_coord.aestronglyMeasurable]
      rw [e1, e2, hsC]; ring
  have hν' : ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (m k) => U p.1) TF) := by
    have := absorb μ (Y := Prod.fst) (Z := Prod.snd) (A := TF) measurable_fst measurable_snd
      (fun i => by
        rw [← hmY i, ← hμ1, Measure.map_map (measurable_pi_apply i) measurable_fst]; rfl)
      hD
    rwa [hμ2] at this
  -- regrouping into blocks and random order
  have hNmn : ∀ k, m k + n k = N k := fun k => by have := hmN k; simp only [hndef]; omega
  haveI : ∀ k, NeZero (N k) := fun k => ⟨(hNpos k).ne'⟩
  set A : (Σ k, Fin (N k)) → Measure ℝ := fun p => if (p.2 : ℕ) < m p.1 then U p.1 else T p.1
    with hAdef
  let e : (Σ k, Fin (m k)) ⊕ ((Σ k, Fin (n k)) ⊕ Fin r) ≃ (Σ k, Fin (N k)) ⊕ Fin r :=
    (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr
      ((Equiv.sigmaSumDistrib (fun k => Fin (m k)) (fun k => Fin (n k))).symm.trans
        (Equiv.sigmaCongrRight (fun k => finSumFinEquiv.trans (finCongr (hNmn k)))))
      (Equiv.refl _))
  have hfam : ∀ x, Sum.elim A F (e x) = Sum.elim (fun p : Σ k, Fin (m k) => U p.1) TF x := by
    rintro (⟨k, i⟩ | ⟨k, i⟩ | j)
    · simp [e, hAdef, Equiv.sigmaSumDistrib, Sigma.map]
    · simp [e, hAdef, hTFdef, Equiv.sigmaSumDistrib, Sigma.map]
    · simp [e, hTFdef]
  have h3 := aggSet_shuffle N A F (aggSet_reindex' e hfam hν')
  refine aggSet_congr ?_ h3
  funext x
  cases x with
  | inr j => rfl
  | inl p =>
    obtain ⟨k, i⟩ := p
    show (N k : ℝ≥0∞)⁻¹ • ∑ i, A ⟨k, i⟩ = G k
    have hsum : ∑ i, A ⟨k, i⟩ = (m k : ℝ≥0∞) • U k + (n k : ℝ≥0∞) • T k :=
      sum_ite_block (U k) (T k) (hNmn k)
    rw [hsum, ← hTd k, smul_smul, ENNReal.inv_mul_cancel (by exact_mod_cast (hNpos k).ne')
      (ENNReal.natCast_ne_top _), one_smul]



/-- **Proposition `as:prop:complete`.** `N_k` copies of `G_k ≥ q_k U[c_k - H_k, c_k + H_k]`
(`k < K`) and further distributions `F_1, …, F_r`, all carried by intervals of length at most
`ℓ`: if `m_k = ⌊q_k N_k⌋ ≥ 4` and `ρ = ∑ m_k H_k / 2 - ℓ ≥ 0`, the aggregation set contains every
distribution with mean `s` (the sum of all means) carried by `[s - ρ, s + ρ]`.
(The hypothesis `ρ ≥ 0` is not needed for this part: it follows from the existence of `ν`.) -/
theorem prop_complete_fix (hW : H_window_line) (hC : H_conc_a_fix) {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hm4 : ∀ k, 4 ≤ ⌊q k * N k⌋₊)
    (s ρ : ℝ) (hs : s = ∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j))
    (hρ : ρ = ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 - ℓ) (_hρ0 : 0 ≤ ρ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = s)
    (hν : ν (Icc (s - ρ) (s + ρ))ᶜ = 0) :
    ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) := by
  have hNpos : ∀ k, 0 < N k := fun k => by
    by_contra h
    have h0 : N k = 0 := by omega
    have := hm4 k
    rw [h0] at this
    simp at this
  refine engine_fix hC G F ℓ hℓ hGℓ hFℓ c H q hH hq0 hq1 hGU N hNpos s ρ hs ν hνm hν ?_
  intro lam β hlam hmean hC' hsupp
  have hWin := win_sigma K (fun k => Fin ⌊q k * N k⌋₊) (fun k _ => unifI (c k - H k) (c k + H k))
    (fun k => ⌊q k * N k⌋₊ * c k) (fun k => ⌊q k * N k⌋₊ * H k / 2)
    (fun k => by have := hH k; positivity) (fun k => win_of_window hW (hm4 k) _ _ (hH k))
  apply hWin lam hlam _ hmean
  refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hsupp
  intro x hx
  have hW : ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 = ρ + ℓ := by rw [hρ]; ring
  rw [hW]
  constructor <;> linarith [hx.1, hx.2, hC'.1, hC'.2]

/-- Proposition `as:prop:complete`, "in particular they are jointly mixable": the point mass at
the sum of the means lies in the aggregation set. -/
theorem prop_complete_dirac_fix (hW : H_window_line) (hC : H_conc_a_fix) {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hm4 : ∀ k, 4 ≤ ⌊q k * N k⌋₊)
    (hρ0 : 0 ≤ ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 - ℓ) :
    Measure.dirac (∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) := by
  refine prop_complete_fix hW hC G F ℓ hℓ hGℓ hFℓ c H q hH hq0 hq1 hGU N hm4 _ _ rfl rfl hρ0 _
    (by simp) ?_
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_not]
  constructor <;> linarith

/-- Proposition `as:prop:complete`, "for instance": four uniform distributions on `[0, 1]`
together with any finite family of distributions on intervals of length at most `1` are jointly
mixable. -/
theorem four_uniform_jointlyMixable_fix (hW : H_window_line) (hC : H_conc_a_fix) {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 4 => unifI 0 1) F) := by
  have hU : unifI (1 / 2 - 1 / 2) (1 / 2 + 1 / 2) = unifI 0 1 := by norm_num
  have := unifI_isProb 0 1
  have h := prop_complete_dirac_fix hW hC (fun _ : Fin 1 => unifI 0 1) F 1 zero_le_one
    (fun _ => ⟨0, by simpa using unifI_null zero_le_one⟩) hF (fun _ => 1 / 2) (fun _ => 1 / 2)
    (fun _ => 1) (fun _ => by norm_num) (fun _ => one_pos) (fun _ => le_rfl)
    (fun _ => by rw [hU]; simp) (fun _ => 4) (fun _ => by norm_num) (by norm_num)
  convert h using 2
  simp [integral_unifI01]
  norm_num


/-- **Corollary `as:cor:three`** (main statement). Let `F` have mean `μ`, be carried by an
interval of length `R`, and satisfy `F ≥ q U[c - H, c + H]`; let `m = ⌊q n⌋ ≥ 3` and `L ≥ R`.
Then `𝒜_n(F)` contains every distribution with mean `n μ` carried by
`[n μ - (L - R)/2, n μ + (L - R)/2]`. -/
theorem cor_three_fix (h3 : PropThree) (hC : H_conc_a_fix) (F : Measure ℝ) [IsProbabilityMeasure F]
    (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H) (hq0 : 0 < q)
    (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hν : ν (Icc (n * ∫ x, x ∂F - (lenThree ⌊q * n⌋₊ H - R) / 2)
      (n * ∫ x, x ∂F + (lenThree ⌊q * n⌋₊ H - R) / 2))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin n => F) := by
  have hn : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hm3; simp at hm3
  have hR0 : 0 ≤ R := by
    obtain ⟨a, ha⟩ := hR
    by_contra h
    push Not at h
    rw [Set.Icc_eq_empty (by linarith), Set.compl_empty, measure_univ] at ha
    exact one_ne_zero ha
  have : ∀ j : Fin 0, IsProbabilityMeasure ((Fin.elim0 : Fin 0 → Measure ℝ) j) := fun j => j.elim0
  have h := engine_fix hC (fun _ : Fin 1 => F) (Fin.elim0 : Fin 0 → Measure ℝ) R hR0 (fun _ => hR)
    (fun j => j.elim0) (fun _ => c) (fun _ => H) (fun _ => q) (fun _ => hH) (fun _ => hq0)
    (fun _ => hq1) (fun _ => hFU) (fun _ => n) (fun _ => hn) (n * ∫ x, x ∂F)
    ((lenThree ⌊q * n⌋₊ H - R) / 2) (by simp) ν hνm hν
    (fun lam β hlam hmean hC' hsupp => block_of_three h3 hm3 c H R _ hH (by ring)
      (by linarith) lam β hlam hmean hC' hsupp)
  refine aggSet_reindex' ((Equiv.sumEmpty _ _).trans (Equiv.uniqueSigma _)) ?_ h
  rintro (p | j)
  · rfl
  · exact j.elim0

/-- Corollary `as:cor:three`: `F` is `n`-completely mixable. -/
theorem cor_three_mixable_fix (h3 : PropThree) (hC : H_conc_a_fix) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H) : CompletelyMixable n F := by
  refine jointlyMixable_of_dirac (cor_three_fix h3 hC F R hR c H q hH hq0 hq1 hFU n hm3 hLR
    (Measure.dirac (n * ∫ x, x ∂F)) (by simp) ?_)
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_not]
  constructor <;> linarith

/-- Corollary `as:cor:three` (a): `F` is `n`-completely mixable as soon as
`⌊q n⌋ ≥ max(4, R/H)`. -/
theorem cor_three_a_fix (h3 : PropThree) (hC : H_conc_a_fix) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (h4 : 4 ≤ ⌊q * n⌋₊) (hRH : R / H ≤ ⌊q * n⌋₊) : CompletelyMixable n F := by
  refine cor_three_mixable_fix h3 hC F R hR c H q hH hq0 hq1 hFU n (by omega) ?_
  unfold lenThree
  rw [if_pos h4]
  rwa [div_le_iff₀ hH] at hRH

/-- Corollary `as:cor:three` (b), the theorem of Puccetti, Wang and Wang with an explicit
complete mix: a distribution on `[a, b]` with `F ≥ (3/n) U[a, b]` is `n`-completely mixable.
(Such an `F` forces `n ≥ 3`; this is assumed.) -/
theorem cor_three_b_fix (h3 : PropThree) (hC : H_conc_a_fix) (F : Measure ℝ) [IsProbabilityMeasure F]
    {a b : ℝ} (hab : a < b) (hF : F (Icc a b)ᶜ = 0) (n : ℕ) (hn : 3 ≤ n)
    (hFU : ENNReal.ofReal (3 / n) • unifI a b ≤ F) : CompletelyMixable n F := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hq : (3 / n : ℝ) * n = 3 := by field_simp
  have hU : unifI ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) = unifI a b := by
    congr 1 <;> ring
  refine cor_three_mixable_fix h3 hC F (b - a) ⟨a, by rwa [add_sub_cancel]⟩ ((a + b) / 2)
    ((b - a) / 2) (3 / n) (by linarith) (by positivity) (by rw [div_le_one (by positivity)]; exact hnr)
    (by rw [hU]; exact hFU) n (by rw [hq]; simp) ?_
  rw [hq]
  simp only [lenThree]
  norm_num
  linarith

/-- Corollary `as:cor:three` (c): three uniform distributions on `[0, 1]` together with any
finite family of distributions on intervals of length at most `1` are jointly mixable. -/
theorem cor_three_c_fix (h3 : PropThree) (hC : H_conc_a_fix) {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 3 => unifI 0 1) F) := by
  have hU : unifI (1 / 2 - 1 / 2) (1 / 2 + 1 / 2) = unifI 0 1 := by norm_num
  have := unifI_isProb 0 1
  have h3eq : ⌊(1 : ℝ) * (3 : ℕ)⌋₊ = 3 := by norm_num
  have h := engine_fix hC (fun _ : Fin 1 => unifI 0 1) F 1 zero_le_one
    (fun _ => ⟨0, by simpa using unifI_null zero_le_one⟩) hF (fun _ => 1 / 2) (fun _ => 1 / 2)
    (fun _ => 1) (fun _ => by norm_num) (fun _ => one_pos) (fun _ => le_rfl)
    (fun _ => by rw [hU]; simp) (fun _ => 3) (fun _ => by norm_num)
    (3 / 2 + ∑ j, ∫ x, x ∂(F j)) 0 (by simp [integral_unifI01]; norm_num)
    (Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j))) (by simp) (by
      rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
      simp)
    (fun lam β hlam hmean hC' hsupp => by
      have hm' : 3 ≤ ⌊(1 : ℝ) * ((3 : ℕ) : ℝ)⌋₊ := by rw [h3eq]
      exact block_of_three h3 hm' (1 / 2) (1 / 2) 1 0 (by norm_num)
        (by rw [h3eq]; simp [lenThree]) le_rfl lam β hlam hmean hC' hsupp)
  exact h


/-- **Corollary `as:cor:repeat`**: for `G` on a bounded interval with nonzero absolutely
continuous part and `L > 0` there are `N₀` and `κ > 0` such that for `N ≥ N₀` and every finite
family `F` of distributions on intervals of length at most `L`, the aggregation set of `N` copies
of `G` together with `F` contains every distribution with mean `s` carried by
`[s - κ N, s + κ N]`, where `s` is the sum of the means. -/
theorem cor_repeat_fix (hW : H_window_line) (hC : H_conc_a_fix) (hCS : H_convSq)
    (G : Measure ℝ) [IsProbabilityMeasure G] {a0 R : ℝ} (hG : G (Icc a0 (a0 + R))ᶜ = 0)
    (hac : volume.withDensity (G.rnDeriv volume) ≠ 0) {L : ℝ} (_hL : 0 < L) :
    ∃ N0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, N0 ≤ N → ∀ (r : ℕ) (F : Fin r → Measure ℝ)
      [∀ j, IsProbabilityMeasure (F j)], (∀ j, ∃ a, F j (Icc a (a + L))ᶜ = 0) →
      ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        ∫ x, x ∂ν = N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) →
        ν (Icc (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) - κ * N)
          (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) + κ * N))ᶜ = 0 →
        ν ∈ aggSet (Sum.elim (fun _ : Fin N => G) F) := by
  have hR : 0 ≤ R := by
    by_contra h
    push Not at h
    have : Icc a0 (a0 + R) = ∅ := Icc_eq_empty (by linarith)
    rw [this, compl_empty, measure_univ] at hG
    exact one_ne_zero hG
  obtain ⟨c, H, q0, hH, hq0, hGU0⟩ := hCS G inferInstance ⟨a0, a0 + R, hG⟩ hac
  set q := min q0 1 with hqdef
  have hq : 0 < q := lt_min hq0 one_pos
  have hq1 : q ≤ 1 := min_le_right _ _
  have hGU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ G ∗ G := by
    refine le_trans (Measure.le_iff'.mpr fun s => ?_) hGU0
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left _ _)) _
  set ℓ := max (2 * R) L with hℓ
  have hℓR : 2 * R ≤ ℓ := le_max_left _ _
  have hℓL : L ≤ ℓ := le_max_right _ _
  have hqH : 0 < q * H := mul_pos hq hH
  refine ⟨⌈2 + 8 / q + 8 * ℓ / (q * H)⌉₊ + 1, q * H / 8, by positivity, ?_⟩
  intro N hN r F hF hFL ν hν hνm hνs
  set N' := N / 2 with hN'
  set e := N % 2 with he
  have hNe : N = 2 * N' + e := (Nat.div_add_mod N 2).symm
  have he1 : e ≤ 1 := by omega
  set F' : Fin (e + r) → Measure ℝ := Fin.append (fun _ : Fin e => G) F with hF'def
  have hF'G : ∀ a : Fin e, F' (finSumFinEquiv (Sum.inl a)) = G := fun a => by
    simp [hF'def]
  have hF'F : ∀ b : Fin r, F' (finSumFinEquiv (Sum.inr b)) = F b := fun b => by
    simp [hF'def]
  haveI hF'P : ∀ j, IsProbabilityMeasure (F' j) := fun j => by
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    rcases k with a | b
    · rw [hF'G]; infer_instance
    · rw [hF'F]; infer_instance
  have hFℓ' : ∀ j, ∃ a, F' j (Icc a (a + ℓ))ᶜ = 0 := fun j => by
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    rcases k with a | b
    · rw [hF'G]
      exact ⟨a0, measure_mono_null (compl_subset_compl.mpr
        (Icc_subset_Icc le_rfl (by linarith))) hG⟩
    · rw [hF'F]
      obtain ⟨a, ha⟩ := hFL b
      exact ⟨a, measure_mono_null (compl_subset_compl.mpr
        (Icc_subset_Icc le_rfl (by linarith))) ha⟩
  have hGG : ∃ a, (G ∗ G) (Icc a (a + ℓ))ᶜ = 0 := by
    refine ⟨2 * a0, measure_mono_null (compl_subset_compl.mpr ?_) (conv_null G hG)⟩
    exact Icc_subset_Icc le_rfl (by linarith)
  -- arithmetic
  have hNr : (N : ℝ) = 2 * N' + e := by exact_mod_cast hNe
  have he1r : (e : ℝ) ≤ 1 := by exact_mod_cast he1
  have he0r : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hN0 : 2 + 8 / q + 8 * ℓ / (q * H) < N := by
    have h1 := Nat.le_ceil (2 + 8 / q + 8 * ℓ / (q * H))
    have h2 : ((⌈2 + 8 / q + 8 * ℓ / (q * H)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hN1 : 2 * (q * H) + 8 * H + 8 * ℓ < q * H * N := by
    have := mul_lt_mul_of_pos_left hN0 hqH
    have e2 : q * H * (2 + 8 / q + 8 * ℓ / (q * H)) = 2 * (q * H) + 8 * H + 8 * ℓ := by
      field_simp
    linarith
  have hN2 : 8 < q * ((N : ℝ) - 2) := by
    have h8 : 8 / q < (N : ℝ) - 2 := by
      have : 0 ≤ 8 * ℓ / (q * H) := by positivity
      linarith
    rw [div_lt_iff₀ hq] at h8
    linarith
  set m := ⌊q * N'⌋₊ with hm
  have hfl : q * N' < m + 1 := Nat.lt_floor_add_one _
  have hqN : q * ((N : ℝ) - 1) / 2 ≤ q * N' := by
    rw [hNr]; nlinarith
  have hm4 : 4 ≤ m := by
    have : (3 : ℝ) < m := by nlinarith
    have : 3 < m := by exact_mod_cast this
    omega
  have hmH : (q * ((N : ℝ) - 1) / 2 - 1) * H ≤ m * H := by
    apply mul_le_mul_of_nonneg_right _ hH.le
    linarith
  set s := (N : ℝ) * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) with hsdef
  set ρ := ∑ _k : Fin 1, (m : ℝ) * H / 2 - ℓ with hρdef
  have hρ' : ρ = m * H / 2 - ℓ := by rw [hρdef, Fin.sum_univ_one]
  have hκρ : q * H / 8 * N ≤ ρ := by rw [hρ']; nlinarith
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hκρ
  have hs : s = ∑ _k : Fin 1, (N' : ℝ) * ∫ x, x ∂(G ∗ G) + ∑ j, ∫ x, x ∂(F' j) := by
    rw [Fin.sum_univ_one, integral_conv G hG, Fin.sum_univ_add, hsdef]
    have h1 : ∀ a : Fin e, ∫ x, x ∂(F' (Fin.castAdd r a)) = ∫ x, x ∂G := fun a => by
      have := hF'G a; simp only [finSumFinEquiv_apply_left] at this; rw [this]
    have h2 : ∀ b : Fin r, ∫ x, x ∂(F' (Fin.natAdd e b)) = ∫ x, x ∂(F b) := fun b => by
      have := hF'F b; simp only [finSumFinEquiv_apply_right] at this; rw [this]
    simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hNr]; ring
  have hν' : ν (Icc (s - ρ) (s + ρ))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (Icc_subset_Icc (by linarith) (by linarith))) hνs
  have h0 := prop_complete_fix hW hC (K := 1) (fun _ => G ∗ G) F' ℓ hℓ0 (fun _ => hGG) hFℓ'
    (fun _ => c) (fun _ => H) (fun _ => q) (fun _ => hH) (fun _ => hq) (fun _ => hq1)
    (fun _ => hGU) (fun _ => N') (fun _ => hm4) s ρ hs hρdef hρ0 ν hνm hν'
  have h1 := aggSet_const_block (β := Fin N') (by simp) (G ∗ G) F' h0
  have h2 : ν ∈ aggSet (Sum.elim (fun _ : Fin N' => G ∗ G) (Sum.elim (fun _ : Fin e => G) F)) := by
    refine aggSet_reindex' (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm) ?_ h1
    rintro (a | j)
    · rfl
    · obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
      rcases k with a | b
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply, Sum.elim_inr]
        rw [hF'G]; rfl
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply, Sum.elim_inr]
        rw [hF'F]
  have h3 := split_pairs G N' _ ν h2
  have h4 := aggSet_assoc h3
  rw [sum_elim_const] at h4
  exact aggSet_const_block (by simp; omega) G F h4

/-! ### Corollary `as:cor:three` and Remark `as:rem:three` with Proposition `as:prop:three` -/

/-- **Proposition `as:prop:complete`**, no hypothesis (the length `ℓ` is assumed `≥ 0`). -/
theorem prop_complete_b {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hm4 : ∀ k, 4 ≤ ⌊q k * N k⌋₊)
    (s ρ : ℝ) (hs : s = ∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j))
    (hρ : ρ = ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 - ℓ) (hρ0 : 0 ≤ ρ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = s)
    (hν : ν (Icc (s - ρ) (s + ρ))ᶜ = 0) :
    ν ∈ aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) :=
  prop_complete_fix h_window_line h_conc_a_fix G F ℓ hℓ hGℓ hFℓ c H q hH hq0 hq1 hGU N hm4 s ρ
    hs hρ hρ0 ν hνm hν

/-- **Proposition `as:prop:complete`**, joint mixability, no hypothesis (`ℓ ≥ 0`). -/
theorem prop_complete_dirac_b {K r : ℕ}
    (G : Fin K → Measure ℝ) [∀ k, IsProbabilityMeasure (G k)]
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)] (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hGℓ : ∀ k, ∃ a, G k (Icc a (a + ℓ))ᶜ = 0) (hFℓ : ∀ j, ∃ a, F j (Icc a (a + ℓ))ᶜ = 0)
    (c H q : Fin K → ℝ) (hH : ∀ k, 0 < H k) (hq0 : ∀ k, 0 < q k) (hq1 : ∀ k, q k ≤ 1)
    (hGU : ∀ k, ENNReal.ofReal (q k) • unifI (c k - H k) (c k + H k) ≤ G k)
    (N : Fin K → ℕ) (hm4 : ∀ k, 4 ≤ ⌊q k * N k⌋₊)
    (hρ0 : 0 ≤ ∑ k, (⌊q k * N k⌋₊ : ℝ) * H k / 2 - ℓ) :
    Measure.dirac (∑ k, (N k : ℝ) * ∫ x, x ∂(G k) + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun p : Σ k, Fin (N k) => G p.1) F) :=
  prop_complete_dirac_fix h_window_line h_conc_a_fix G F ℓ hℓ hGℓ hFℓ c H q hH hq0 hq1 hGU N
    hm4 hρ0

/-- **Proposition `as:prop:complete`**, "for instance", no hypothesis. -/
theorem four_uniform_jointlyMixable_b {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 4 => unifI 0 1) F) :=
  four_uniform_jointlyMixable_fix h_window_line h_conc_a_fix F hF

/-- **Corollary `as:cor:repeat`**, no hypothesis (`H_convSq` from `ConvSq.convSq`). -/
theorem cor_repeat_b
    (G : Measure ℝ) [IsProbabilityMeasure G] {a0 R : ℝ} (hG : G (Icc a0 (a0 + R))ᶜ = 0)
    (hac : volume.withDensity (G.rnDeriv volume) ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ N0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, N0 ≤ N → ∀ (r : ℕ) (F : Fin r → Measure ℝ)
      [∀ j, IsProbabilityMeasure (F j)], (∀ j, ∃ a, F j (Icc a (a + L))ᶜ = 0) →
      ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        ∫ x, x ∂ν = N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) →
        ν (Icc (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) - κ * N)
          (N * ∫ x, x ∂G + ∑ j, ∫ x, x ∂(F j) + κ * N))ᶜ = 0 →
        ν ∈ aggSet (Sum.elim (fun _ : Fin N => G) F) :=
  cor_repeat_fix h_window_line h_conc_a_fix ConvSq.convSq G hG hac hL

/-- **Proposition `as:prop:three`**, no hypothesis. -/
theorem prop_three_b : PropThree := prop_three TwoStepBorel.twoStepBorel

/-- **Corollary `as:cor:three`** (main statement), no hypothesis. -/
theorem cor_three_b (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hν : ν (Icc (n * ∫ x, x ∂F - (lenThree ⌊q * n⌋₊ H - R) / 2)
      (n * ∫ x, x ∂F + (lenThree ⌊q * n⌋₊ H - R) / 2))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin n => F) :=
  cor_three_fix prop_three_b h_conc_a_fix F R hR c H q hH hq0 hq1 hFU n hm3 hLR ν hνm hν

/-- **Corollary `as:cor:three`**: complete mixability, no hypothesis. -/
theorem cor_three_mixable_b (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H) : CompletelyMixable n F :=
  cor_three_mixable_fix prop_three_b h_conc_a_fix F R hR c H q hH hq0 hq1 hFU n hm3 hLR

/-- **Corollary `as:cor:three`** (a), no hypothesis. -/
theorem cor_three_a_b (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (h4 : 4 ≤ ⌊q * n⌋₊) (hRH : R / H ≤ ⌊q * n⌋₊) : CompletelyMixable n F :=
  cor_three_a_fix prop_three_b h_conc_a_fix F R hR c H q hH hq0 hq1 hFU n h4 hRH

/-- **Corollary `as:cor:three`** (b), no hypothesis. -/
theorem cor_three_b_b (F : Measure ℝ)
    [IsProbabilityMeasure F] {a b : ℝ} (hab : a < b) (hF : F (Icc a b)ᶜ = 0) (n : ℕ) (hn : 3 ≤ n)
    (hFU : ENNReal.ofReal (3 / n) • unifI a b ≤ F) : CompletelyMixable n F :=
  cor_three_b_fix prop_three_b h_conc_a_fix F hab hF n hn hFU

/-- **Corollary `as:cor:three`** (c), no hypothesis. -/
theorem cor_three_c_b {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 3 => unifI 0 1) F) :=
  cor_three_c_fix prop_three_b h_conc_a_fix F hF

/-- **Remark `as:rem:three`**, no hypothesis. -/
theorem rem_three_b (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ x, x ∂ν = 3 / 2)
    (hsupp : (∃ a : ℝ, a ≤ 3 / 2 ∧ 3 / 2 ≤ a + 1 ∧ ν (Icc a (a + 1))ᶜ = 0) ∨
      ν (Icc 1 (5 / 2))ᶜ = 0 ∨ ν (Icc (1 / 2) 2)ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin 3 => unifI 0 1) :=
  rem_three TwoStepBorel.twoStepBorel ν hmean hsupp

end Three

/-! ## `NormUnimodal` -/

section Norm

open Mixes.NormUnimodal

/-- `NormUnimodal.H_as_cor_three_a`, no hypothesis (`TwoStepBorel.twoStepBorel`). -/
theorem h_as_cor_three_a : H_as_cor_three_a :=
  fun F hF R hR c H q hH hq0 hq1 hFU n h4 hRH =>
    haveI := hF
    cor_three_a_b F R hR c H q hH hq0 hq1 hFU n h4 hRH

/-- `NormUnimodal.H_as_cor_three_b`, no hypothesis (`TwoStepBorel.twoStepBorel`). -/
theorem h_as_cor_three_b : H_as_cor_three_b :=
  fun F hF _ _ hab hFs n hn hFU =>
    haveI := hF
    cor_three_b_b F hab hFs n hn hFU

theorem cxCond_of_SL_b {n : ℕ} {F : Measure ℝ} [IsProbabilityMeasure F]
    {a b : ℝ} (hF : ∀ᵐ x ∂F, x ∈ Icc a b) (h : CxCondSL n F) : NormAtom.CxCond n F (mean F) :=
  cxCond_of_SL StopLoss.stoploss_cx hF h

theorem normIneqs_of_SL_b (H2 : NormAtom.H_shmalo26b) {n : ℕ}
    (hn : 2 ≤ n) {F : Measure ℝ} [IsProbabilityMeasure F] {a b : ℝ} (hF : ∀ᵐ x ∂F, x ∈ Icc a b)
    (h : CxCondSL n F) : NormAtom.NormIneqs n F (mean F) :=
  normIneqs_of_SL StopLoss.stoploss_cx H2 hn hF h

variable {n n₀ : ℕ} {p β η : ℝ} {w : ℝ → ℝ}

/-- Relation (nc:eq:cx) for all convex functions, for `f₁` and `f₂`, no hypothesis. -/
theorem cx_F1_F2_b (h : CxParams n p β η) (hw : IsBump w) :
    NormAtom.CxCond n (F1 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) ∧
      NormAtom.CxCond n (F2 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) :=
  cx_F1_F2 StopLoss.stoploss_cx h hw

/-- The inequalities (nc:eq:norm) for `f₁` and `f₂`, under the cited `H_shmalo26b` only. -/
theorem thm_unimodal_norm_b (H2 : NormAtom.H_shmalo26b)
    (h : CxParams n p β η) (hw : IsBump w) :
    NormAtom.NormIneqs n (F1 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) ∧
      NormAtom.NormIneqs n (F2 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) :=
  thm_unimodal_norm StopLoss.stoploss_cx H2 h hw

/-- Corollary `nc:cor:alln`, norm inequalities for every `n ≥ 3`, under `H_shmalo26b` only. -/
theorem cor_alln_norm_b (H2 : NormAtom.H_shmalo26b)
    (h : CorParams n₀ p β η) (hw : IsBump w) (n : ℕ) (hn : 3 ≤ n) :
    NormAtom.NormIneqs n (F1 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) ∧
      NormAtom.NormIneqs n (F2 p (1 / 2 - β) η (wLaw w)) (p * (1 / 2 - β) + (1 - p) / 2) :=
  cor_alln_norm StopLoss.stoploss_cx H2 h hw n hn

/-- Corollary `nc:cor:alln`: `f₁` is `n`-completely mixable for `n ≥ 3/q`, with no
hypothesis. -/
theorem cor_alln_mixable_b (h : CorParams n₀ p β η)
    (hw : IsBump w) (n : ℕ) (hn : 3 / (1 - p) ≤ n) :
    CompletelyMixable n (F1 p (1 / 2 - β) η (wLaw w)) :=
  cor_alln_mixable (h_as_cor_three_b) h hw n hn

/-- Remark `nc:rem:classes`, the explicit threshold for unimodal densities, with no
hypothesis. -/
theorem threshold_unimodal_b {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {a b m : ℝ}
    (hF : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)))
    (hsupp : (volume.withDensity fun x => ENNReal.ofReal (f x)) (Icc a b)ᶜ = 0)
    (hmono : MonotoneOn f (Iic m)) (hanti : AntitoneOn f (Ici m)) {x y : ℝ} (hxy : x < y)
    (n : ℕ) (h4 : 4 ≤ ⌊(y - x) * min (f x) (f y) * n⌋₊)
    (hR : 2 * (b - a) / (y - x) ≤ ⌊(y - x) * min (f x) (f y) * n⌋₊) :
    CompletelyMixable n (volume.withDensity fun x => ENNReal.ofReal (f x)) :=
  threshold_unimodal (h_as_cor_three_a) hfm hf0 hF hsupp hmono hanti hxy n h4 hR

end Norm

end Mixes.AsymBridge
