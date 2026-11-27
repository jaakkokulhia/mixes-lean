import Mixes.Sphere
import Mixes.Homothetic
import Mixes.Cone
import Mixes.ProjLemmas

/-!
# Projections onto proper subspaces: Theorem `pj:thm:main`, Corollary `pj:cor:confine`

Section `pj:sec:proj` of the paper. The three lemmas of the section are proved in
`ProjLemmas.lean`; here they enter as the hypotheses `H_example` (Lemma `pj:lem:example`),
`H_gadget_a`, `H_gadget_b` (Lemma `pj:lem:gadget`), stated with the objects of `ProjLemmas.lean`
(Lemma `pj:lem:three` is used only inside the proof of Lemma `pj:lem:example`).

* `exists_P0`: the distribution `P₀` (gadget of `G₁, G₂, G₃, δ₀, …, δ₀`, `ρ₀ = 13/10`): compact
  support, mean `0`, images under maps with a nonzero kernel `n`-completely mixable, `P₀` not.
* `Nd`: the rotation-invariant smooth bump law `N_δ` (density `η_δ(x) ∝ φ(1 - |x|²/δ²)`, `φ` the
  smooth transition function); `n`-completely mixable by Proposition `b:prop:radial`
  (`Ball.completelyMixable_of_isRotInv`, `Sphere.sphereUniqueness`).
* `Pd P₀ δ = P₀ * N_δ`, with density `fd P₀ δ` (`Pd_eq_withDensity`), `C^∞` (`fd_contDiff`, by
  `ContDiff.parametric_integral`) and of compact support.
* `Pd_tendsto`: `P_{1/(k+1)} → P₀` weakly; `exists_weak_limit`: Prokhorov
  (`isCompact_closure_of_isTightMeasureSet`); `Pd_not_cm`: some `P_δ` is not completely mixable.
* **Theorem `pj:thm:main`**: `pj_thm_main` (`C^∞` density of compact support; images under all
  linear maps with a nonzero kernel into any second countable real normed space), and
  `pj_thm_main_proj` (orthogonal projections onto all proper subspaces).
* **Theorem `pj:thm:main`, last sentence**: `pj_thm_main_analytic`: `P_δ = P₀ * N(0, δ² I)`
  (`PG`, Gaussian `Gs`), with an everywhere positive (`fG_pos`) real-analytic (`fG_analytic`)
  density; analyticity from `laplace_analytic` (an explicit power series with infinite radius for
  `x ↦ ∫ exp⟪y, x⟫ w(y) dμ(y)`, `μ` compactly supported); tightness (`Gs_tail`, `PG_compl_le`)
  replaces the compact support in the limit argument (`exists_weak_limit_tight`, `PG_not_cm`).
* Unconditional versions (`*_uncond`): the hypotheses discharged by `ProjLemmas.lean`.
* **Corollary `pj:cor:confine`**: for any `P` with compact support and mean `0` as in the
  theorem: `cor_confine_subspace` (gluing along a conditional distribution, `glue_all`),
  `cor_confine_line`, `cor_no_zero_sum`, `cor_min` (minimum attained and positive); combined for
  the distribution of the theorem in `pj_cor_confine`.
* **Remark `pj:rem:positive`**: `rem_product` (products of completely mixable distributions on
  `ℝ`). The other claims of the remark are citations.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal ContDiff BoundedContinuousFunction

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.ProjMain

open Mixes.ProjLemmas

/-- `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ## The lemmas of the section, as hypotheses

The objects (`exG`, `exQ`, `exQf`, `gadP`, ...) are those of `ProjLemmas.lean`; the hypotheses
are the statements proved there (`ex_*`, `gadget_a`, `gadget_b`), with the target spaces `F` of
the linear maps taken in `Type`. -/

/-- **Lemma `pj:lem:example`** (`ProjLemmas.ex_Qf_nonneg`, `ex_Qf_le`, `ex_isProb_Q`,
`ex_Q_compl`, `ex_isProb`, `ex_support`, `ex_mean` (part (i)), `ex_not_jointlyMixable` (part (ii)),
`ex_map_jointlyMixable` (part (iii))). -/
def H_example : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ w : E d, ‖w‖ = 3 / 10 →
    ((∀ x, 0 ≤ exQf d w x) ∧ (∀ x, exQf d w x ≤ 3 / exVol d) ∧
      IsProbabilityMeasure (exQ d w) ∧ exQ d w (closedBall 0 (13 / 10))ᶜ = 0 ∧
      (∀ i, IsProbabilityMeasure (exG d w i)) ∧ (∀ i, exG d w i (closedBall 0 (13 / 10))ᶜ = 0) ∧
      ∀ i, ∫ x, x ∂(exG d w i) = 0) ∧
    ¬ JointlyMixable (exG d w) ∧
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
      [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
      JointlyMixable fun i => (exG d w i).map L

/-- **Lemma `pj:lem:gadget` (a)** (`ProjLemmas.gadget_a`, on `ℝ^d`). -/
def H_gadget_a : Prop :=
  ∀ (d n : ℕ), 2 ≤ n → ∀ (G : Fin n → Measure (E d)), (∀ i, IsProbabilityMeasure (G i)) →
    ∀ (lam : ℝ) (e : E d) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F),
      (JointlyMixable fun i => (G i).map L) → CompletelyMixable n ((gadP G lam e).map L)

/-- **Lemma `pj:lem:gadget` (b)** (`ProjLemmas.gadget_b`, on `ℝ^d`). -/
def H_gadget_b : Prop :=
  ∀ (d n : ℕ), 2 ≤ n → ∀ (G : Fin n → Measure (E d)), (∀ i, IsProbabilityMeasure (G i)) →
    ∀ (ρ₀ lam : ℝ) (e : E d), (∀ i, G i (closedBall 0 ρ₀)ᶜ = 0) →
      (∀ i, ∫ x, x ∂(G i) = 0) → ‖e‖ = 1 → n * ρ₀ < lam →
      CompletelyMixable n (gadP G lam e) → JointlyMixable G

/-! ## Padding with point masses at `0` -/

section Pad

variable {F : Type*} [MeasurableSpace F] [AddCommGroup F] [MeasurableSingletonClass F]
  [MeasurableAdd₂ F]

lemma measurable_append_zero (m : ℕ) :
    Measurable fun x : Fin 3 → F => (Fin.append x (fun _ : Fin m => (0 : F)) : Fin (3 + m) → F) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [Fin.append_left]; exact measurable_pi_apply j
  · simp only [Fin.append_right]; exact measurable_const

/-- Point masses at `0` do not affect joint mixability (one direction). -/
theorem jm_pad {m : ℕ} {G : Fin 3 → Measure F} (h : JointlyMixable G) :
    JointlyMixable (Fin.append G (fun _ : Fin m => Measure.dirac (0 : F))) := by
  obtain ⟨P, hP, ⟨s, hs⟩, hm⟩ := h
  refine ⟨P.map fun x => Fin.append x (fun _ : Fin m => (0 : F)), inferInstance, ⟨s, ?_⟩,
    fun i => ?_⟩
  · rw [ae_map_iff (measurable_append_zero m).aemeasurable (Mixes.measurableSet_sum_eq' s)]
    filter_upwards [hs] with x hx
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, hx]
  · rw [Measure.map_map (measurable_pi_apply i) (measurable_append_zero m)]
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · rw [Fin.append_left, ← hm j]
      congr 1
      funext x; simp [Fin.append_left]
    · simp only [Fin.append_right]
      have : ((fun x : Fin (3 + m) → F => x (Fin.natAdd 3 k)) ∘
          fun x : Fin 3 → F => Fin.append x (fun _ : Fin m => (0 : F))) = fun _ => 0 := by
        funext x; simp [Fin.append_right]
      rw [this, Measure.map_const, measure_univ, one_smul]

/-- Point masses at `0` do not affect joint mixability (other direction). -/
theorem jm_unpad {m : ℕ} {G : Fin 3 → Measure F}
    (h : JointlyMixable (Fin.append G (fun _ : Fin m => Measure.dirac (0 : F)))) :
    JointlyMixable G := by
  obtain ⟨P, hP, ⟨s, hs⟩, hm⟩ := h
  have hmeas : Measurable fun x : Fin (3 + m) → F => fun j : Fin 3 => x (Fin.castAdd m j) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hz : ∀ k : Fin m, ∀ᵐ x ∂P, x (Fin.natAdd 3 k) = 0 := by
    intro k
    have h1 := hm (Fin.natAdd 3 k)
    simp only [Fin.append_right] at h1
    have h2 : ∀ᵐ y ∂(Measure.dirac (0 : F)), y = 0 := by rw [ae_dirac_eq]; exact rfl
    rw [← h1] at h2
    exact (ae_map_iff (measurable_pi_apply _).aemeasurable (measurableSet_singleton 0)).1 h2
  refine ⟨P.map fun x j => x (Fin.castAdd m j), inferInstance, ⟨s, ?_⟩, fun j => ?_⟩
  · rw [ae_map_iff hmeas.aemeasurable (Mixes.measurableSet_sum_eq' s)]
    filter_upwards [hs, ae_all_iff.2 hz] with x hx hx0
    rw [Fin.sum_univ_add] at hx
    simpa [hx0] using hx
  · rw [Measure.map_map (measurable_pi_apply j) hmeas, ← Fin.append_left G
      (fun _ : Fin m => Measure.dirac (0 : F)) j, ← hm]
    rfl

end Pad

/-! ## Measures carried by balls -/

section Carried

variable {d : ℕ}

lemma ae_of_carried {μ : Measure (E d)} {R : ℝ} (h : μ (closedBall 0 R)ᶜ = 0) :
    ∀ᵐ x ∂μ, ‖x‖ ≤ R := by
  rw [ae_iff]
  convert h using 2
  ext x; simp

lemma carried_of_ae {μ : Measure (E d)} {R : ℝ} (h : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    μ (closedBall 0 R)ᶜ = 0 := by
  rw [ae_iff] at h
  convert h using 2
  ext x; simp

lemma integrable_id_of_carried {μ : Measure (E d)} [IsFiniteMeasure μ] {R : ℝ}
    (h : μ (closedBall 0 R)ᶜ = 0) : Integrable id μ :=
  Integrable.of_bound aestronglyMeasurable_id R (ae_of_carried h)

lemma tr_isProb (v : E d) (G : Measure (E d)) [IsProbabilityMeasure G] :
    IsProbabilityMeasure (tr v G) := by
  unfold tr; infer_instance

lemma tr_carried {v : E d} {G : Measure (E d)} {ρ : ℝ} (h : G (closedBall 0 ρ)ᶜ = 0) :
    tr v G (closedBall 0 (ρ + ‖v‖))ᶜ = 0 := by
  refine carried_of_ae ?_
  unfold tr
  rw [ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))]
  filter_upwards [ae_of_carried h] with x hx
  exact (norm_add_le x v).trans (by linarith)

lemma integral_tr {v : E d} {G : Measure (E d)} [IsProbabilityMeasure G]
    (hi : Integrable id G) : ∫ x, x ∂(tr v G) = ∫ x, x ∂G + v := by
  unfold tr
  rw [integral_map (f := fun x => x) (by fun_prop) aestronglyMeasurable_id,
    integral_add (f := fun x => x) hi (integrable_const v)]
  simp

lemma sum_gadA {n : ℕ} (hn : 1 ≤ n) : ∑ i, gadA n i = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin m, gadA (m + 1) i.castSucc = (2 * (m + 1 : ℕ) + 1 : ℤ) ^ i.val := by
    intro i; simp [gadA, i.isLt]
  have h2 : gadA (m + 1) (Fin.last m) =
      -∑ k ∈ Finset.range m, (2 * (m + 1 : ℕ) + 1 : ℤ) ^ k := by
    simp [gadA]
  rw [h2, Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range
    (fun k => (2 * (m + 1 : ℕ) + 1 : ℤ) ^ k) m]
  ring

lemma gadgetP_isProb {n : ℕ} (hn : 1 ≤ n) (G : Fin n → Measure (E d))
    [hG : ∀ i, IsProbabilityMeasure (G i)] (e : E d) (lam : ℝ) :
    IsProbabilityMeasure (gadP G lam e) := by
  constructor
  have : ∀ i, (tr (gadV n lam e i) (G i)) univ = 1 := fun i =>
    (tr_isProb _ (G i)).measure_univ
  rw [gadP, smul_apply, sum_apply]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp; omega) (by simp)

lemma gadgetP_carried {n : ℕ} (G : Fin n → Measure (E d)) {ρ : ℝ}
    (hc : ∀ i, G i (closedBall 0 ρ)ᶜ = 0) (e : E d) (lam : ℝ) :
    gadP G lam e (closedBall 0 (ρ + ∑ i, ‖gadV n lam e i‖))ᶜ = 0 := by
  rw [gadP, smul_apply, sum_apply]
  have : ∀ i, (tr (gadV n lam e i) (G i))
      (closedBall 0 (ρ + ∑ i, ‖gadV n lam e i‖))ᶜ = 0 := by
    intro i
    refine measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall ?_))
      (tr_carried (hc i))
    have := Finset.single_le_sum (f := fun i => ‖gadV n lam e i‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  simp [this]

lemma gadgetP_mean {n : ℕ} (hn : 1 ≤ n) (G : Fin n → Measure (E d))
    [hG : ∀ i, IsProbabilityMeasure (G i)] {ρ : ℝ} (hc : ∀ i, G i (closedBall 0 ρ)ᶜ = 0)
    (hm : ∀ i, ∫ x, x ∂(G i) = 0) (e : E d) (lam : ℝ) :
    ∫ x, x ∂(gadP G lam e) = 0 := by
  have hi : ∀ i, Integrable id (G i) := fun i => integrable_id_of_carried (hc i)
  have hti : ∀ i, Integrable (fun x : E d => x) (tr (gadV n lam e i) (G i)) := by
    intro i
    have := tr_isProb (gadV n lam e i) (G i)
    exact integrable_id_of_carried (tr_carried (hc i))
  rw [gadP, integral_smul_measure, integral_finsetSum_measure (fun i _ => hti i)]
  simp only [integral_tr (hi _), hm, zero_add]
  simp only [gadV]
  rw [← Finset.sum_smul, ← Finset.mul_sum, ← Int.cast_sum, sum_gadA hn]
  simp

end Carried

/-! ## The unsmoothed distribution `P₀` -/

section P0

variable {d : ℕ}

lemma exists_unit (hd : 1 ≤ d) : ∃ e : E d, ‖e‖ = 1 := by
  have : Nontrivial (E d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  exact exists_norm_eq (E d) zero_le_one

/-- The padded family `(G₁, G₂, G₃, δ₀, …, δ₀)`. -/
def padG (d m : ℕ) (w : E d) : Fin (3 + m) → Measure (E d) :=
  Fin.append (exG d w) (fun _ => Measure.dirac 0)

/-- The distribution `P₀` of the proof of Theorem `pj:thm:main`: the gadget of
`(G₁, G₂, G₃, δ₀, …, δ₀)` with `ρ₀ = 13/10`; its properties. -/
theorem exists_P0 (hex : H_example) (hga : H_gadget_a) (hgb : H_gadget_b) (hd : 2 ≤ d)
    (m : ℕ) :
    ∃ P₀ : Measure (E d), IsProbabilityMeasure P₀ ∧ (∃ R, P₀ (closedBall 0 R)ᶜ = 0) ∧
      ∫ x, x ∂P₀ = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
        [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable (3 + m) (P₀.map L)) ∧ ¬ CompletelyMixable (3 + m) P₀ := by
  obtain ⟨e, he⟩ := exists_unit (d := d) (by omega)
  set w : E d := (3 / 10 : ℝ) • e with hw
  have hwn : ‖w‖ = 3 / 10 := by rw [hw, norm_smul, he]; norm_num
  obtain ⟨⟨-, -, -, -, hP, hS, hmean⟩, hnot, himg⟩ := hex d hd w hwn
  set G := padG d m w with hG
  have hprob : ∀ i, IsProbabilityMeasure (G i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · rw [hG, padG, Fin.append_left]; exact hP j
    · rw [hG, padG, Fin.append_right]; infer_instance
  have hcar : ∀ i, G i (closedBall 0 (13 / 10))ᶜ = 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · rw [hG, padG, Fin.append_left]; exact hS j
    · rw [hG, padG, Fin.append_right]
      simp [Measure.dirac_apply' _ measurableSet_closedBall.compl]
      norm_num
  have hmeanG : ∀ i, ∫ x, x ∂(G i) = 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · rw [hG, padG, Fin.append_left]; exact hmean j
    · rw [hG, padG, Fin.append_right]; simp
  set lam : ℝ := ((3 + m : ℕ) : ℝ) * (13 / 10) + 1
  refine ⟨gadP G lam e, gadgetP_isProb (by omega) G e lam, ⟨_, gadgetP_carried G hcar e lam⟩,
    gadgetP_mean (by omega) G hcar hmeanG e lam, fun F _ _ _ _ _ L hL => ?_, fun h => ?_⟩
  · refine hga d (3 + m) (by omega) G hprob lam e F L ?_
    have h1 := jm_pad (m := m) (himg F L hL)
    convert h1 using 2 with i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp only [hG, padG, Fin.append_left]
    · simp only [hG, padG, Fin.append_right]
      rw [Measure.map_dirac' (L.continuous_of_finiteDimensional.measurable), map_zero]
  · exact hnot (jm_unpad (hgb d (3 + m) (by omega) G hprob (13 / 10) lam e hcar hmeanG he
      (by simp [lam]) h))

end P0

/-! ## The smoothing kernel -/

section Bump

variable {d : ℕ}

/-- `x ↦ φ(1 - |x|²/δ²)`, `φ` the smooth transition function: a rotation-invariant smooth bump
supported by the closed ball of radius `δ`. -/
def bump (δ : ℝ) (x : E d) : ℝ := Real.smoothTransition (1 - ‖x‖ ^ 2 / δ ^ 2)

lemma bump_contDiff (δ : ℝ) : ContDiff ℝ ∞ (bump (d := d) δ) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

lemma bump_continuous (δ : ℝ) : Continuous (bump (d := d) δ) := (bump_contDiff δ).continuous

lemma bump_nonneg (δ : ℝ) (x : E d) : 0 ≤ bump δ x := Real.smoothTransition.nonneg _

lemma bump_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : E d} (hx : δ ≤ ‖x‖) : bump δ x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 1 ≤ ‖x‖ ^ 2 / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

lemma bump_zero (δ : ℝ) : bump δ (0 : E d) = 1 :=
  Real.smoothTransition.one_of_one_le (by simp)

lemma bump_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (bump (d := d) δ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 δ) fun x hx =>
    bump_eq_zero hδ (by simp at hx; linarith)

/-- The normalising constant. -/
def bumpZ (d : ℕ) (δ : ℝ) : ℝ := ∫ x : E d, bump δ x

lemma bumpZ_pos {δ : ℝ} (hδ : 0 < δ) : 0 < bumpZ d δ :=
  Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 0) (bump_continuous δ)
    (bump_hasCompactSupport hδ) (bump_nonneg δ) (by rw [bump_zero]; norm_num)

/-- The probability density `η_δ`. -/
def eta (δ : ℝ) (x : E d) : ℝ := bump δ x / bumpZ d δ

lemma eta_contDiff (δ : ℝ) : ContDiff ℝ ∞ (eta (d := d) δ) := (bump_contDiff δ).div_const _

lemma eta_continuous (δ : ℝ) : Continuous (eta (d := d) δ) := (eta_contDiff δ).continuous

lemma eta_nonneg {δ : ℝ} (hδ : 0 < δ) (x : E d) : 0 ≤ eta δ x :=
  div_nonneg (bump_nonneg δ x) (bumpZ_pos hδ).le

lemma eta_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : E d} (hx : δ ≤ ‖x‖) : eta δ x = 0 := by
  simp [eta, bump_eq_zero hδ hx]

lemma eta_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (eta (d := d) δ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 δ) fun x hx =>
    eta_eq_zero hδ (by simp at hx; linarith)

lemma eta_integrable {δ : ℝ} (hδ : 0 < δ) : Integrable (eta (d := d) δ) :=
  (eta_continuous δ).integrable_of_hasCompactSupport (eta_hasCompactSupport hδ)

lemma eta_integral {δ : ℝ} (hδ : 0 < δ) : ∫ x : E d, eta δ x = 1 := by
  simp only [eta]
  rw [integral_div]
  exact div_self (bumpZ_pos hδ).ne'

lemma eta_bdd (δ : ℝ) : ∃ C, ∀ x : E d, |eta δ x| ≤ C := by
  by_cases hδ : 0 < δ
  · obtain ⟨C, hC⟩ := (eta_continuous (d := d) δ).bounded_above_of_compact_support
      (eta_hasCompactSupport hδ)
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  · refine ⟨|1 / bumpZ d δ|, fun x => ?_⟩
    simp only [eta, div_eq_mul_inv, abs_mul, one_mul]
    have h1 : |bump δ x| ≤ 1 := by
      rw [abs_of_nonneg (bump_nonneg δ x)]; exact Real.smoothTransition.le_one _
    have := abs_nonneg (bumpZ d δ)⁻¹
    nlinarith [abs_nonneg (bump δ x)]

/-- The distribution `N_δ` with density `η_δ`. -/
def Nd (d : ℕ) (δ : ℝ) : Measure (E d) := volume.withDensity fun x => ENNReal.ofReal (eta δ x)

lemma Nd_isProb {δ : ℝ} (hδ : 0 < δ) : IsProbabilityMeasure (Nd d δ) := by
  constructor
  rw [Nd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (eta_integrable hδ)
      (Eventually.of_forall (eta_nonneg hδ)), eta_integral hδ, ENNReal.ofReal_one]

lemma Nd_carried {δ : ℝ} (hδ : 0 < δ) : Nd d δ (closedBall 0 δ)ᶜ = 0 := by
  rw [Nd, withDensity_apply _ measurableSet_closedBall.compl,
    setLIntegral_congr_fun measurableSet_closedBall.compl (g := fun _ => 0) (fun x hx => by
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hx
      simp [eta_eq_zero hδ hx.le])]
  simp

lemma Nd_isRotInv (δ : ℝ) : Mixes.Ball.IsRotInv (Nd d δ) := by
  intro L
  have hg : Measurable fun r : ℝ =>
      ENNReal.ofReal (Real.smoothTransition (1 - r ^ 2 / δ ^ 2) / bumpZ d δ) :=
    ENNReal.measurable_ofReal.comp
      ((Real.smoothTransition.continuous.comp (by fun_prop)).measurable.div_const _)
  exact Mixes.Ball.withDensity_radial_map_iso _ hg L

lemma Nd_mean (δ : ℝ) : ∫ x, x ∂(Nd d δ) = 0 := Mixes.Ball.integral_id_eq_zero (Nd_isRotInv δ)

lemma Nd_cm (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (Nd d δ) := by
  have := Nd_isProb (d := d) hδ
  exact Mixes.Ball.completelyMixable_of_isRotInv Mixes.Sphere.sphereUniqueness
    (by simp; omega) (Nd_isRotInv δ) hn

end Bump

/-! ## The smoothed distributions `P_δ = P₀ * η_δ` -/

section Smooth

variable {d : ℕ} (P₀ : Measure (E d)) [IsProbabilityMeasure P₀]

/-- `P_δ = P₀ * N_δ`, the law of `X + Y` with `X ∼ P₀` and `Y ∼ N_δ` independent. -/
def Pd (δ : ℝ) : Measure (E d) := (P₀.prod (Nd d δ)).map fun p => p.1 + p.2

/-- The density of `P_δ`, `x ↦ ∫ η_δ(x - y) dP₀(y)`. -/
def fd (δ : ℝ) (x : E d) : ℝ := ∫ y, eta δ (x - y) ∂P₀

variable {P₀}

lemma Pd_isProb {δ : ℝ} (hδ : 0 < δ) : IsProbabilityMeasure (Pd P₀ δ) := by
  have := Nd_isProb (d := d) hδ
  unfold Pd; infer_instance

lemma ae_prod_carried {δ R : ℝ} (hδ : 0 < δ) (hR : P₀ (closedBall 0 R)ᶜ = 0) :
    ∀ᵐ p ∂(P₀.prod (Nd d δ)), ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ δ := by
  have := Nd_isProb (d := d) hδ
  have h1 : ∀ᵐ p ∂(P₀.prod (Nd d δ)), ‖p.1‖ ≤ R :=
    Measure.quasiMeasurePreserving_fst.ae (ae_of_carried hR)
  have h2 : ∀ᵐ p ∂(P₀.prod (Nd d δ)), ‖p.2‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (ae_of_carried (Nd_carried hδ))
  filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩

lemma Pd_carried {δ R : ℝ} (hδ : 0 < δ) (hR : P₀ (closedBall 0 R)ᶜ = 0) :
    Pd P₀ δ (closedBall 0 (R + δ))ᶜ = 0 := by
  refine carried_of_ae ?_
  unfold Pd
  rw [ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))]
  filter_upwards [ae_prod_carried hδ hR] with p hp
  exact (norm_add_le _ _).trans (by linarith [hp.1, hp.2])

lemma Pd_mean {δ R : ℝ} (hδ : 0 < δ) (hR : P₀ (closedBall 0 R)ᶜ = 0)
    (hmean : ∫ x, x ∂P₀ = 0) : ∫ x, x ∂(Pd P₀ δ) = 0 := by
  have := Nd_isProb (d := d) hδ
  have hi1 : Integrable (fun p : E d × E d => p.1) (P₀.prod (Nd d δ)) :=
    (integrable_id_of_carried hR).comp_fst _
  have hi2 : Integrable (fun p : E d × E d => p.2) (P₀.prod (Nd d δ)) :=
    (integrable_id_of_carried (Nd_carried hδ)).comp_snd _
  unfold Pd
  rw [integral_map (f := fun x => x) (by fun_prop) aestronglyMeasurable_id,
    integral_add hi1 hi2, integral_fun_fst (fun x : E d => x),
    integral_fun_snd (fun x : E d => x), hmean, Nd_mean]
  simp

lemma Pd_map_cm (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : E d →ₗ[ℝ] F) (h0 : CompletelyMixable n (P₀.map L)) :
    CompletelyMixable n ((Pd P₀ δ).map L) := by
  have := Nd_isProb (d := d) hδ
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  obtain ⟨π₀, h₀⟩ := h0
  obtain ⟨πN, hN⟩ := Nd_cm hd hδ hn
  have hN' := Mixes.IsJointMix.map_affine hN L.toAddMonoidHom hL (fun _ => 0)
  have hP := (Mixes.IsJointMix.prod h₀ hN').map_add_hom
    (AddMonoidHom.coprod (AddMonoidHom.id F) (AddMonoidHom.id F))
    (by
      have e : ⇑(AddMonoidHom.coprod (AddMonoidHom.id F) (AddMonoidHom.id F)) =
          fun p : F × F => p.1 + p.2 := by funext p; simp
      rw [e]; exact measurable_fst.add measurable_snd)
    (fun _ => 0)
  have heq : ((P₀.map L).prod ((Nd d δ).map fun x => 0 + L.toAddMonoidHom x)).map
      (fun x => 0 + (AddMonoidHom.coprod (AddMonoidHom.id F) (AddMonoidHom.id F)) x) =
      (Pd P₀ δ).map L := by
    simp only [zero_add, AddMonoidHom.coprod_apply, AddMonoidHom.id_apply,
      LinearMap.toAddMonoidHom_coe]
    rw [Measure.map_prod_map _ _ hL hL, Measure.map_map (by fun_prop) (by fun_prop), Pd,
      Measure.map_map hL (by fun_prop)]
    congr 1
    funext p
    simp
  rw [heq] at hP
  exact ⟨_, hP⟩

lemma fd_eq_zero {δ R : ℝ} (hδ : 0 < δ) (hR : P₀ (closedBall 0 R)ᶜ = 0) {x : E d}
    (hx : R + δ < ‖x‖) : fd P₀ δ x = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_of_carried hR] with y hy
  refine eta_eq_zero hδ ?_
  have := norm_sub_norm_le x y
  linarith

lemma fd_hasCompactSupport {δ R : ℝ} (hδ : 0 < δ) (hR : P₀ (closedBall 0 R)ᶜ = 0) :
    HasCompactSupport (fd P₀ δ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (R + δ)) fun x hx =>
    fd_eq_zero hδ hR (by simpa using hx)

lemma fd_nonneg {δ : ℝ} (hδ : 0 < δ) (x : E d) : 0 ≤ fd P₀ δ x :=
  integral_nonneg fun _ => eta_nonneg hδ _

lemma fd_contDiff {δ R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0) : ContDiff ℝ ∞ (fd P₀ δ) := by
  have hres : P₀.restrict (closedBall 0 R) = P₀ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    filter_upwards [ae_of_carried hR] with y hy using by simpa using hy
  have := ContDiff.parametric_integral (μ := P₀) (f := fun x y : E d => eta δ (x - y))
    (isCompact_closedBall 0 R) subset_rfl (measure_ne_top _ _) (n := ⊤)
    ((eta_contDiff δ).comp (contDiff_fst.sub contDiff_snd))
  show ContDiff ℝ ∞ (fun x => ∫ y, eta δ (x - y) ∂P₀)
  simpa [hres] using this

lemma fd_integrable {δ : ℝ} (z : E d) : Integrable (fun y => eta δ (z - y)) P₀ := by
  obtain ⟨C, hC⟩ := eta_bdd (d := d) δ
  exact Integrable.of_bound ((eta_continuous δ).comp (continuous_const.sub continuous_id)
    ).aestronglyMeasurable C (Eventually.of_forall fun y => by simpa using hC (z - y))

/-- `P_δ` has the density `f_δ`. -/
lemma Pd_eq_withDensity {δ : ℝ} (hδ : 0 < δ) :
    Pd P₀ δ = volume.withDensity fun x => ENNReal.ofReal (fd P₀ δ x) := by
  have := Nd_isProb (d := d) hδ
  have hcont : Continuous fun q : E d × E d => eta δ (q.1 - q.2) :=
    (eta_continuous δ).comp (continuous_fst.sub continuous_snd)
  ext A hA
  rw [Pd, Measure.map_apply (by fun_prop) hA, Measure.prod_apply (measurable_add hA),
    withDensity_apply _ hA]
  have h1 : ∀ x : E d, Nd d δ (Prod.mk x ⁻¹' ((fun p : E d × E d => p.1 + p.2) ⁻¹' A)) =
      ∫⁻ z in A, ENNReal.ofReal (eta δ (z - x)) := by
    intro x
    rw [show Prod.mk x ⁻¹' ((fun p : E d × E d => p.1 + p.2) ⁻¹' A) = (fun y => x + y) ⁻¹' A
      from rfl, Nd, withDensity_apply _ (measurable_const_add x hA), ← lintegral_indicator
      (measurable_const_add x hA), ← lintegral_indicator hA]
    rw [← lintegral_add_left_eq_self (μ := volume)
      (A.indicator fun z => ENNReal.ofReal (eta δ (z - x))) x]
    congr 1
    funext y
    by_cases hy : x + y ∈ A
    · simp [indicator, hy]
    · simp [indicator, hy]
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun z => ?_
    rw [fd, ofReal_integral_eq_lintegral_ofReal (fd_integrable z)
      (Eventually.of_forall fun y => eta_nonneg hδ _)]
  · exact (ENNReal.measurable_ofReal.comp
      ((eta_continuous δ).measurable.comp (measurable_snd.sub measurable_fst))).aemeasurable

/-- `δ_k = 1/(k+1)`. -/
def dk (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma dk_pos (k : ℕ) : 0 < dk k := by unfold dk; positivity

lemma dk_le_one (k : ℕ) : dk k ≤ 1 := by
  unfold dk; rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]

lemma dk_anti {k l : ℕ} (h : k ≤ l) : dk l ≤ dk k := by
  unfold dk
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

/-- `P_{δ_k} → P₀` weakly. -/
lemma Pd_tendsto (g : E d →ᵇ ℝ) :
    Tendsto (fun k => ∫ z, g z ∂(Pd P₀ (dk k))) atTop (𝓝 (∫ z, g z ∂P₀)) := by
  have hF : ∀ k, ∫ z, g z ∂(Pd P₀ (dk k)) = ∫ x, ∫ y, g (x + y) ∂(Nd d (dk k)) ∂P₀ := by
    intro k
    have := Nd_isProb (d := d) (dk_pos k)
    rw [Pd, integral_map (by fun_prop) g.continuous.aestronglyMeasurable]
    exact integral_prod (fun p : E d × E d => g (p.1 + p.2))
      (Integrable.of_bound (g.continuous.comp (by fun_prop)).aestronglyMeasurable ‖g‖
        (Eventually.of_forall fun p => g.norm_coe_le_norm _))
  simp_rw [hF]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun k => ?_)
    (integrable_const _) (fun k => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · have := Nd_isProb (d := d) (dk_pos k)
    exact (StronglyMeasurable.integral_prod_right (f := fun x y : E d => g (x + y))
      (g.continuous.comp continuous_add).stronglyMeasurable).aestronglyMeasurable
  · have := Nd_isProb (d := d) (dk_pos k)
    have := norm_integral_le_of_norm_le_const (μ := Nd d (dk k)) (f := fun y => g (x + y))
      (C := ‖g‖) (Eventually.of_forall fun y => g.norm_coe_le_norm _)
    simpa using this
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨ρ, hρ, hgρ⟩ := Metric.continuous_iff.1 g.continuous x (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have := Nd_isProb (d := d) (dk_pos k)
    have hint : Integrable (fun y => g (x + y)) (Nd d (dk k)) :=
      Integrable.of_bound (g.continuous.comp (by fun_prop)).aestronglyMeasurable ‖g‖
        (Eventually.of_forall fun y => g.norm_coe_le_norm _)
    have heq : ∫ y, g (x + y) ∂(Nd d (dk k)) - g x = ∫ y, (g (x + y) - g x) ∂(Nd d (dk k)) := by
      rw [integral_sub hint (integrable_const _)]; simp
    rw [Real.dist_eq, heq]
    have hb := norm_integral_le_of_norm_le_const (μ := Nd d (dk k))
      (f := fun y => g (x + y) - g x) (C := ε / 2) (by
        filter_upwards [ae_of_carried (Nd_carried (dk_pos k))] with y hy
        have h1 : dist (x + y) x < ρ := by
          rw [dist_eq_norm, add_sub_cancel_left]
          exact lt_of_le_of_lt hy (lt_of_le_of_lt (dk_anti hk) hN)
        have := hgρ (x + y) h1
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]; exact this.le)
    simp only [probReal_univ, mul_one] at hb
    rw [← Real.norm_eq_abs]
    linarith

end Smooth

/-! ## Weak compactness (Prokhorov) -/

section Prokhorov

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [BorelSpace X]
  [FirstCountableTopology (ProbabilityMeasure X)]

/-- A sequence of probability measures carried by one compact set has a weakly convergent
subsequence (Prokhorov's theorem, `isCompact_closure_of_isTightMeasureSet`). -/
lemma exists_weak_limit (μ : ℕ → Measure X) [hμ : ∀ k, IsProbabilityMeasure (μ k)] {K : Set X}
    (hK : IsCompact K) (hμK : ∀ k, μ k Kᶜ = 0) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ g : X →ᵇ ℝ, Tendsto (fun k => ∫ x, g x ∂(μ (φ k))) atTop (𝓝 (∫ x, g x ∂π)) := by
  let ν : ℕ → ProbabilityMeasure X := fun k => ⟨μ k, hμ k⟩
  have hT : IsTightMeasureSet {x | ∃ m ∈ range ν, (m : Measure X) = x} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε _
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨m, ⟨k, rfl⟩, rfl⟩
    simp [ν, hμK]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (x := ν) (fun k => subset_closure ⟨k, rfl⟩)
  refine ⟨a, inferInstance, φ, hφ, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim
  exact hlim

/-- Prokhorov's theorem for a tight sequence: a weakly convergent subsequence. -/
lemma exists_weak_limit_tight (μ : ℕ → Measure X) [hμ : ∀ k, IsProbabilityMeasure (μ k)]
    (hT : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ k, μ k Kᶜ ≤ ε) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ g : X →ᵇ ℝ, Tendsto (fun k => ∫ x, g x ∂(μ (φ k))) atTop (𝓝 (∫ x, g x ∂π)) := by
  let ν : ℕ → ProbabilityMeasure X := fun k => ⟨μ k, hμ k⟩
  have hT' : IsTightMeasureSet {x | ∃ m ∈ range ν, (m : Measure X) = x} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKε⟩ := hT ε hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨m, ⟨k, rfl⟩, rfl⟩
    exact hKε k
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT').tendsto_subseq
    (x := ν) (fun k => subset_closure ⟨k, rfl⟩)
  refine ⟨a, inferInstance, φ, hφ, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim
  exact hlim

end Prokhorov

/-! ## `P_δ` is not completely mixable for some `δ` -/

section NotCM

variable {d n : ℕ} {P₀ : Measure (E d)} [IsProbabilityMeasure P₀]

/-- If `P_{δ_k}` were `n`-completely mixable for every `k`, a weak limit point of the complete
mixes would be an `n`-complete mix of `P₀`. -/
theorem Pd_not_cm {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0) (hmean : ∫ x, x ∂P₀ = 0)
    (hnot : ¬ CompletelyMixable n P₀) : ∃ k, ¬ CompletelyMixable n (Pd P₀ (dk k)) := by
  by_contra hall
  push Not at hall
  choose π hπ using hall
  have hprob : ∀ k, IsProbabilityMeasure (π k) := fun k => (hπ k).1
  have hPk : ∀ k, IsProbabilityMeasure (Pd P₀ (dk k)) := fun k => Pd_isProb (dk_pos k)
  have hcar : ∀ k, Pd P₀ (dk k) (closedBall 0 (R + 1))ᶜ = 0 := fun k =>
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall
      (by linarith [dk_le_one k]))) (Pd_carried (dk_pos k) hR)
  have hsum : ∀ k, ∀ᵐ x ∂(π k), ∑ j, x j = 0 := by
    intro k
    have := Mixes.Homothetic.IsJointMix.ae_sum_eq (hπ k) (fun _ => integrable_id_of_carried (hcar k))
    simpa [Pd_mean (dk_pos k) hR hmean] using this
  set K : Set (Fin n → E d) := univ.pi fun _ => closedBall 0 (R + 1)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hπK : ∀ k, π k Kᶜ = 0 := by
    intro k
    have hsub : Kᶜ ⊆ ⋃ j, (fun x : Fin n → E d => x j) ⁻¹' (closedBall 0 (R + 1))ᶜ := by
      intro x hx
      simp only [K, mem_compl_iff, mem_univ_pi, not_forall] at hx
      obtain ⟨j, hj⟩ := hx
      exact mem_iUnion.2 ⟨j, hj⟩
    refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
    rw [← Measure.map_apply (measurable_pi_apply j) measurableSet_closedBall.compl,
      (hπ k).2.2 j]
    exact hcar k
  obtain ⟨π', hπ', φ, hφ, hlim⟩ := exists_weak_limit π hK hπK
  -- the marginals of the limit
  have hmarg : ∀ j, π'.map (fun x => x j) = P₀ := by
    intro j
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    let gj : (Fin n → E d) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => g (x j)) (g.continuous.comp (continuous_apply j)) ‖g‖
      (fun x => g.norm_coe_le_norm _)
    have h1 := hlim gj
    have h2 : (fun k => ∫ x, gj x ∂(π (φ k))) = fun k => ∫ z, g z ∂(Pd P₀ (dk (φ k))) := by
      funext k
      have hm : (π (φ k)).map (fun x => x j) = Pd P₀ (dk (φ k)) := (hπ (φ k)).2.2 j
      rw [← hm, integral_map (measurable_pi_apply j).aemeasurable
        g.continuous.aestronglyMeasurable]
      rfl
    rw [h2] at h1
    rw [integral_map (measurable_pi_apply j).aemeasurable g.continuous.aestronglyMeasurable]
    exact tendsto_nhds_unique h1 ((Pd_tendsto g).comp hφ.tendsto_atTop)
  -- the sum of the limit
  let h : (Fin n → E d) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min 1 ‖∑ j, x j‖) (by fun_prop) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (norm_nonneg _))]
      exact min_le_left _ _)
  have hh0 : ∫ x, h x ∂π' = 0 := by
    refine tendsto_nhds_unique (hlim h) ?_
    have : ∀ k, ∫ x, h x ∂(π (φ k)) = 0 := fun k => integral_eq_zero_of_ae (by
      filter_upwards [hsum (φ k)] with x hx
      simp [h, hx])
    simp only [this]
    exact tendsto_const_nhds
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => le_min zero_le_one (norm_nonneg _))
    (h.integrable π')).1 hh0
  refine hnot ⟨π', hπ', ⟨0, ?_⟩, hmarg⟩
  filter_upwards [hae] with x hx
  have hx' : min 1 ‖∑ j, x j‖ = 0 := hx
  rcases min_eq_iff.1 hx' with h1 | h1
  · exact absurd h1.1 one_ne_zero
  · exact norm_eq_zero.1 h1.1

/-- The smoothing step of the proof of Theorem `pj:thm:main`: from `P₀` (compact support, mean
`0`, completely mixable images under the maps with a nonzero kernel, not completely mixable) to a
distribution with the same properties and a `C^∞` density of compact support. -/
theorem smoothing (hd : 2 ≤ d) (hn : 2 ≤ n) {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0)
    (hmean : ∫ x, x ∂P₀ = 0)
    (himg : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
      [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
      CompletelyMixable n (P₀.map L))
    (hnot : ¬ CompletelyMixable n P₀) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
        [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable n (P.map L)) ∧
      ¬ CompletelyMixable n P := by
  obtain ⟨k, hk⟩ := Pd_not_cm hR hmean hnot
  have hδ := dk_pos k
  exact ⟨fd P₀ (dk k), Pd P₀ (dk k), Pd_eq_withDensity hδ, fd_contDiff hR,
    fd_hasCompactSupport hδ hR, fd_nonneg hδ, Pd_isProb hδ, Pd_mean hδ hR hmean,
    fun F _ _ _ _ _ L hL => Pd_map_cm hd hδ hn L (himg F L hL), hk⟩

end NotCM

/-! ## Theorem `pj:thm:main` -/

/-- **Theorem `pj:thm:main`** (the `C^∞` part), given Lemmas `pj:lem:example` and
`pj:lem:gadget`: for `d ≥ 2` and `n ≥ 3` there is a probability distribution `P` on `ℝ^d` with
mean `0` and a `C^∞` density `f` of compact support such that the image of `P` under every
linear map with a nonzero kernel is `n`-completely mixable, while `P` is not. -/
theorem pj_thm_main (hex : H_example) (hga : H_gadget_a) (hgb : H_gadget_b) {d n : ℕ}
    (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
        [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable n (P.map L)) ∧
      ¬ CompletelyMixable n P := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m := ⟨n - 3, by omega⟩
  obtain ⟨P₀, hP₀, ⟨R, hR⟩, hmean, himg, hnot⟩ := exists_P0 hex hga hgb hd m
  exact smoothing hd (by omega) hR hmean himg hnot

/-- **Theorem `pj:thm:main`, "in particular"**: the orthogonal projections of `P` onto all proper
subspaces `K` of `ℝ^d` (as maps `ℝ^d → ℝ^d`) are `n`-completely mixable. -/
theorem pj_thm_main_proj (hex : H_example) (hga : H_gadget_a) (hgb : H_gadget_b) {d n : ℕ}
    (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ K : Submodule ℝ (E d), K ≠ ⊤ → CompletelyMixable n (P.map K.starProjection)) ∧
      ¬ CompletelyMixable n P := by
  obtain ⟨f, P, h1, h2, h3, h4, h5, h6, himg, h8⟩ := pj_thm_main hex hga hgb hd hn
  refine ⟨f, P, h1, h2, h3, h4, h5, h6, fun K hK => ?_, h8⟩
  have := himg (E d) (K.starProjection : E d →ₗ[ℝ] E d) (by
    have e : LinearMap.ker (K.starProjection : E d →ₗ[ℝ] E d) = Kᗮ := K.ker_starProjection
    rw [e]
    exact fun h => hK (Submodule.orthogonal_eq_bot_iff.1 h))
  exact this

/-! ## Corollary `pj:cor:confine`: gluing along conditional distributions -/

section Glue

open ProbabilityTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma compProd_comap_map (ρ : Measure α) [IsFiniteMeasure ρ] (κ : Kernel β γ) [IsMarkovKernel κ]
    {f : α → β} (hf : Measurable f) :
    (ρ ⊗ₘ κ.comap f hf).map (fun q => (f q.1, q.2)) = (ρ.map f) ⊗ₘ κ := by
  ext s hs
  have hg : Measurable fun q : α × γ => (f q.1, q.2) := (hf.comp measurable_fst).prodMk
    measurable_snd
  rw [Measure.map_apply hg hs, Measure.compProd_apply (hg hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

variable {d n : ℕ}

/-- The gluing invariant: the first coordinate block has law `πW`, and for `j ∈ S` the pair
`(y_j, x_j)` has law `J`. -/
def GlueInv (πW : Measure (Fin n → E d)) (J : Measure (E d × E d)) (S : Finset (Fin n))
    (ρ : Measure ((Fin n → E d) × (Fin n → E d))) : Prop :=
  IsProbabilityMeasure ρ ∧ ρ.map Prod.fst = πW ∧
    ∀ j ∈ S, ρ.map (fun p => (p.1 j, p.2 j)) = J

lemma glue_step {πW : Measure (Fin n → E d)} {J : Measure (E d × E d)} [IsFiniteMeasure J]
    (hJ : ∀ k, πW.map (fun y => y k) = J.fst) {S : Finset (Fin n)} {k : Fin n} (hk : k ∉ S)
    {ρ : Measure ((Fin n → E d) × (Fin n → E d))} (h : GlueInv πW J S ρ) :
    ∃ ρ', GlueInv πW J (insert k S) ρ' := by
  obtain ⟨hρ, hfst, hS⟩ := h
  set κ := J.condKernel
  have hf : Measurable fun p : (Fin n → E d) × (Fin n → E d) => p.1 k :=
    (measurable_pi_apply k).comp measurable_fst
  set κ' := κ.comap (fun p : (Fin n → E d) × (Fin n → E d) => p.1 k) hf
  have hup : Measurable fun q : ((Fin n → E d) × (Fin n → E d)) × E d =>
      (q.1.1, Function.update q.1.2 k q.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_pi_iff.2 fun i => by
        by_cases hi : i = k
        · subst hi; simpa using measurable_snd
        · simp only [Function.update_of_ne hi]
          exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  refine ⟨(ρ ⊗ₘ κ').map fun q => (q.1.1, Function.update q.1.2 k q.2), inferInstance, ?_,
    fun j hj => ?_⟩
  · rw [Measure.map_map measurable_fst hup]
    have : (Prod.fst ∘ fun q : ((Fin n → E d) × (Fin n → E d)) × E d =>
        (q.1.1, Function.update q.1.2 k q.2)) = Prod.fst ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_fst measurable_fst]
    rw [show (ρ ⊗ₘ κ').map Prod.fst = (ρ ⊗ₘ κ').fst from rfl, Measure.fst_compProd, hfst]
  · have hpj : ∀ j : Fin n, Measurable fun p : (Fin n → E d) × (Fin n → E d) => (p.1 j, p.2 j) :=
      fun j => ((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    rw [Measure.map_map (hpj j) hup]
    rcases Finset.mem_insert.1 hj with rfl | hjS
    · have : ((fun p : (Fin n → E d) × (Fin n → E d) => (p.1 j, p.2 j)) ∘
          fun q : ((Fin n → E d) × (Fin n → E d)) × E d =>
            (q.1.1, Function.update q.1.2 j q.2)) = fun q => (q.1.1 j, q.2) := by
        funext q; simp
      rw [this, compProd_comap_map ρ κ hf]
      have h1 : ρ.map (fun p : (Fin n → E d) × (Fin n → E d) => p.1 j) = J.fst := by
        rw [← hJ j, ← hfst, Measure.map_map (measurable_pi_apply j) measurable_fst]
        rfl
      rw [h1]
      exact J.disintegrate J.condKernel
    · have hne : j ≠ k := fun h => hk (h ▸ hjS)
      have : ((fun p : (Fin n → E d) × (Fin n → E d) => (p.1 j, p.2 j)) ∘
          fun q : ((Fin n → E d) × (Fin n → E d)) × E d =>
            (q.1.1, Function.update q.1.2 k q.2)) =
          (fun p : (Fin n → E d) × (Fin n → E d) => (p.1 j, p.2 j)) ∘ Prod.fst := by
        funext q; simp [Function.update_of_ne hne]
      rw [this, ← Measure.map_map (hpj j) measurable_fst,
        show (ρ ⊗ₘ κ').map Prod.fst = (ρ ⊗ₘ κ').fst from rfl, Measure.fst_compProd]
      exact hS j hjS

lemma glue_all {πW : Measure (Fin n → E d)} [IsProbabilityMeasure πW] {J : Measure (E d × E d)}
    [IsFiniteMeasure J] (hJ : ∀ k, πW.map (fun y => y k) = J.fst) :
    ∃ ρ, GlueInv πW J Finset.univ ρ := by
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · refine ⟨πW.prod (Measure.dirac 0), inferInstance, ?_, by simp⟩
    rw [Measure.map_fst_prod]; simp
  · intro k S hk ⟨ρ, hρ⟩
    exact glue_step hJ hk hρ

end Glue

/-! ## Corollary `pj:cor:confine` -/

section Confine

variable {d n : ℕ}

/-- `π` is the law of random vectors `X_1, …, X_n` with distribution `P` each. -/
def IsCoupling (n : ℕ) (P : Measure (E d)) (π : Measure (Fin n → E d)) : Prop :=
  IsProbabilityMeasure π ∧ ∀ j, π.map (fun x => x j) = P

/-- **Corollary `pj:cor:confine`, first claim**: if `P` has compact support and mean `0` and its
images under the linear maps with a nonzero kernel are `n`-completely mixable, then for every
subspace `V ≠ {0}` there are `X_1, …, X_n ∼ P` whose sum lies in `V` almost surely. -/
theorem cor_confine_subspace {P : Measure (E d)} [IsProbabilityMeasure P] {R : ℝ}
    (hR : P (closedBall 0 R)ᶜ = 0) (hmean : ∫ x, x ∂P = 0)
    (himg : ∀ L : E d →ₗ[ℝ] E d, LinearMap.ker L ≠ ⊥ → CompletelyMixable n (P.map L))
    {V : Submodule ℝ (E d)} (hV : V ≠ ⊥) :
    ∃ π, IsCoupling n P π ∧ ∀ᵐ x ∂π, ∑ j, x j ∈ V := by
  set Lc : E d →L[ℝ] E d := Vᗮ.starProjection with hLc
  have hker : LinearMap.ker (Lc : E d →ₗ[ℝ] E d) = V := by
    have e : LinearMap.ker (Lc : E d →ₗ[ℝ] E d) = Vᗮᗮ := Vᗮ.ker_starProjection
    rw [e, Submodule.orthogonal_orthogonal]
  have hLm : Measurable Lc := Lc.continuous.measurable
  obtain ⟨πW, hW⟩ := himg Lc (by rw [hker]; exact hV)
  have hWp : IsProbabilityMeasure πW := hW.1
  have hint : Integrable id P := integrable_id_of_carried hR
  have hintL : Integrable id (P.map Lc) :=
    (integrable_map_measure aestronglyMeasurable_id hLm.aemeasurable).2 (Lc.integrable_comp hint)
  have hmeanL : ∫ y, y ∂(P.map Lc) = 0 := by
    rw [integral_map (f := fun y => y) hLm.aemeasurable aestronglyMeasurable_id,
      Lc.integral_comp_comm (φ := fun x => x) hint, hmean, map_zero]
  have hsum : ∀ᵐ y ∂πW, ∑ j, y j = 0 := by
    have := Mixes.Homothetic.IsJointMix.ae_sum_eq hW (fun _ => hintL)
    simpa [hmeanL] using this
  have hpair : Measurable fun x : E d => (Lc x, x) := hLm.prodMk measurable_id
  set J : Measure (E d × E d) := P.map fun x => (Lc x, x)
  have hJfst : J.fst = P.map Lc := by
    rw [Measure.fst, Measure.map_map measurable_fst hpair]; rfl
  obtain ⟨ρ, hρ, hfst, hpairs⟩ := glue_all (πW := πW) (J := J) (fun k => by
    rw [hJfst]; exact hW.2.2 k)
  have hpj : ∀ j : Fin n, Measurable fun p : (Fin n → E d) × (Fin n → E d) => (p.1 j, p.2 j) :=
    fun j => ((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)
  refine ⟨ρ.map Prod.snd, ⟨inferInstance, fun j => ?_⟩, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply j) measurable_snd]
    have : ((fun x : Fin n → E d => x j) ∘ Prod.snd) =
        Prod.snd ∘ fun p : (Fin n → E d) × (Fin n → E d) => (p.1 j, p.2 j) := rfl
    rw [this, ← Measure.map_map measurable_snd (hpj j), hpairs j (Finset.mem_univ j),
      Measure.map_map measurable_snd hpair]
    exact Measure.map_id
  · have hgraph : ∀ j, ∀ᵐ p ∂ρ, Lc (p.2 j) = p.1 j := by
      intro j
      have hmeasG : MeasurableSet {q : E d × E d | Lc q.2 = q.1} :=
        measurableSet_eq_fun (hLm.comp measurable_snd) measurable_fst
      have hJg : ∀ᵐ q ∂J, Lc q.2 = q.1 :=
        (ae_map_iff hpair.aemeasurable hmeasG).2 (Eventually.of_forall fun x => rfl)
      rw [← hpairs j (Finset.mem_univ j)] at hJg
      exact (ae_map_iff (hpj j).aemeasurable hmeasG).1 hJg
    have hsum' : ∀ᵐ p ∂ρ, ∑ j, p.1 j = 0 := by
      rw [← hfst] at hsum
      exact (ae_map_iff measurable_fst.aemeasurable (Mixes.measurableSet_sum_eq' 0)).1 hsum
    have hVm : MeasurableSet {x : Fin n → E d | ∑ j, x j ∈ V} :=
      (V.isClosed_of_finiteDimensional.measurableSet).preimage
        (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
    rw [ae_map_iff measurable_snd.aemeasurable hVm]
    filter_upwards [ae_all_iff.2 hgraph, hsum'] with p hp hp'
    rw [← hker, LinearMap.mem_ker]
    simp only [ContinuousLinearMap.coe_coe, map_sum, hp, hp']

/-- **Corollary `pj:cor:confine`, second claim**: if `P` is not `n`-completely mixable, no
`X_1, …, X_n ∼ P` have the sum `0`. -/
theorem cor_no_zero_sum {P : Measure (E d)} (hnot : ¬ CompletelyMixable n P)
    {π : Measure (Fin n → E d)} (hπ : IsCoupling n P π) : ¬ ∀ᵐ x ∂π, ∑ j, x j = 0 :=
  fun h => hnot ⟨π, hπ.1, ⟨0, h⟩, hπ.2⟩

lemma coupling_compl {P : Measure (E d)} {R : ℝ} (hR : P (closedBall 0 R)ᶜ = 0)
    {π : Measure (Fin n → E d)} (hπ : IsCoupling n P π) :
    π (univ.pi fun _ => closedBall (0 : E d) R)ᶜ = 0 := by
  have hsub : (univ.pi fun _ => closedBall (0 : E d) R)ᶜ ⊆
      ⋃ j, (fun x : Fin n → E d => x j) ⁻¹' (closedBall 0 R)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_univ_pi, not_forall] at hx
    obtain ⟨j, hj⟩ := hx
    exact mem_iUnion.2 ⟨j, hj⟩
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  rw [← Measure.map_apply (measurable_pi_apply j) measurableSet_closedBall.compl, hπ.2 j]
  exact hR

/-- **Corollary `pj:cor:confine`, third claim**: for `P` with compact support that is not
`n`-completely mixable, the minimum of `E|X_1 + ⋯ + X_n|²` over all `X_1, …, X_n ∼ P` is attained
and positive. -/
theorem cor_min {P : Measure (E d)} [IsProbabilityMeasure P] {R : ℝ}
    (hR : P (closedBall 0 R)ᶜ = 0) (hnot : ¬ CompletelyMixable n P) :
    ∃ π₀, IsCoupling n P π₀ ∧
      (∀ π, IsCoupling n P π → ∫ x, ‖∑ j, x j‖ ^ 2 ∂π₀ ≤ ∫ x, ‖∑ j, x j‖ ^ 2 ∂π) ∧
      0 < ∫ x, ‖∑ j, x j‖ ^ 2 ∂π₀ := by
  set C : ℝ := ((n : ℝ) * |R|) ^ 2 + 1 with hC
  have hC0 : 0 < C := by positivity
  set K : Set (Fin n → E d) := univ.pi fun _ => closedBall (0 : E d) R
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let q : (Fin n → E d) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (‖∑ j, x j‖ ^ 2) C) (by fun_prop) C
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) hC0.le)]
      exact min_le_right _ _)
  have hq : ∀ π, IsCoupling n P π → ∫ x, ‖∑ j, x j‖ ^ 2 ∂π = ∫ x, q x ∂π := by
    intro π hπ
    refine integral_congr_ae ?_
    have hKae : ∀ᵐ x ∂π, x ∈ K := by
      rw [ae_iff]; exact coupling_compl hR hπ
    filter_upwards [hKae] with x hx
    have hb : ‖∑ j, x j‖ ≤ n * |R| := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ j ∈ Finset.univ, ‖x j‖ ≤ |R| := fun j _ => by
        have := hx j (mem_univ j)
        simp only [mem_closedBall, dist_zero_right] at this
        exact this.trans (le_abs_self R)
      simpa using Finset.sum_le_sum this
    have : ‖∑ j, x j‖ ^ 2 ≤ C := by
      rw [hC]; nlinarith [norm_nonneg (∑ j, x j)]
    simp [q, min_eq_left this]
  have hqnn : ∀ π : Measure (Fin n → E d), 0 ≤ ∫ x, q x ∂π := fun π =>
    integral_nonneg fun x => le_min (sq_nonneg _) hC0.le
  set T : Set ℝ := {t | ∃ π, IsCoupling n P π ∧ ∫ x, q x ∂π = t}
  have hdiag : IsCoupling n P (P.map fun x => fun _ : Fin n => x) := by
    have hm : Measurable fun x : E d => fun _ : Fin n => x :=
      measurable_pi_iff.2 fun _ => measurable_id
    refine ⟨inferInstance, fun j => ?_⟩
    rw [Measure.map_map (measurable_pi_apply j) hm]
    exact Measure.map_id
  have hTne : T.Nonempty := ⟨_, _, hdiag, rfl⟩
  have hTbdd : BddBelow T := ⟨0, by rintro _ ⟨π, -, rfl⟩; exact hqnn π⟩
  set m := sInf T
  have hseq : ∀ k : ℕ, ∃ π, IsCoupling n P π ∧ ∫ x, q x ∂π < m + 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨t, ⟨π, hπ, rfl⟩, ht⟩ := exists_lt_of_csInf_lt hTne
      (lt_add_of_pos_right m (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    exact ⟨π, hπ, ht⟩
  choose π hπ hπlt using hseq
  have hprob : ∀ k, IsProbabilityMeasure (π k) := fun k => (hπ k).1
  obtain ⟨π', hπ', φ, hφ, hlim⟩ := exists_weak_limit π hK fun k => coupling_compl hR (hπ k)
  have hmarg : ∀ j, π'.map (fun x => x j) = P := by
    intro j
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    let gj : (Fin n → E d) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => g (x j)) (g.continuous.comp (continuous_apply j)) ‖g‖
      (fun x => g.norm_coe_le_norm _)
    have h1 := hlim gj
    have h2 : (fun k => ∫ x, gj x ∂(π (φ k))) = fun _ => ∫ z, g z ∂P := by
      funext k
      rw [← (hπ (φ k)).2 j, integral_map (measurable_pi_apply j).aemeasurable
        g.continuous.aestronglyMeasurable]
      rfl
    rw [h2] at h1
    rw [integral_map (measurable_pi_apply j).aemeasurable g.continuous.aestronglyMeasurable]
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hcoup : IsCoupling n P π' := ⟨hπ', hmarg⟩
  have hqm : ∫ x, q x ∂π' = m := by
    refine tendsto_nhds_unique (hlim q) ?_
    have hup : Tendsto (fun k => m + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 m) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => csInf_le hTbdd ⟨π (φ k), hπ (φ k), rfl⟩) (fun k => (hπlt (φ k)).le)
  refine ⟨π', hcoup, fun π₁ h₁ => ?_, ?_⟩
  · rw [hq π' hcoup, hq π₁ h₁, hqm]
    exact csInf_le hTbdd ⟨π₁, h₁, rfl⟩
  · rw [hq π' hcoup]
    refine lt_of_le_of_ne (hqnn π') fun h0 => ?_
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => le_min (sq_nonneg _) hC0.le)
      (q.integrable π')).1 h0.symm
    refine cor_no_zero_sum hnot hcoup ?_
    filter_upwards [hae] with x hx
    have hx' : min (‖∑ j, x j‖ ^ 2) C = 0 := hx
    rcases min_eq_iff.1 hx' with h1 | h1
    · exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1.1)
    · exact absurd h1.1 hC0.ne'

/-- The confinement to a line through the origin. -/
theorem cor_confine_line {P : Measure (E d)} [IsProbabilityMeasure P] {R : ℝ}
    (hR : P (closedBall 0 R)ᶜ = 0) (hmean : ∫ x, x ∂P = 0)
    (himg : ∀ L : E d →ₗ[ℝ] E d, LinearMap.ker L ≠ ⊥ → CompletelyMixable n (P.map L))
    {v : E d} (hv : v ≠ 0) :
    ∃ π, IsCoupling n P π ∧ ∀ᵐ x ∂π, ∃ t : ℝ, ∑ j, x j = t • v := by
  obtain ⟨π, hπ, h⟩ := cor_confine_subspace hR hmean himg
    (V := ℝ ∙ v) (by simpa [Submodule.span_singleton_eq_bot] using hv)
  refine ⟨π, hπ, ?_⟩
  filter_upwards [h] with x hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hx
  exact ⟨t, ht.symm⟩

lemma carried_of_hasCompactSupport {f : E d → ℝ} (hf : HasCompactSupport f) :
    ∃ R, (volume.withDensity fun x => ENNReal.ofReal (f x)) (closedBall 0 R)ᶜ = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, ?_⟩
  rw [withDensity_apply _ measurableSet_closedBall.compl,
    setLIntegral_congr_fun measurableSet_closedBall.compl (g := fun _ => 0) (fun x hx => by
      have : x ∉ tsupport f := fun h => hx (hR h)
      simp [image_eq_zero_of_notMem_tsupport this])]
  simp

/-- **Corollary `pj:cor:confine`** for the distribution of Theorem `pj:thm:main` (given its
lemmas): the sum of suitable `X_1, …, X_n ∼ P` can be confined to any subspace `V ≠ {0}`, no
`X_1, …, X_n ∼ P` have the sum `0`, and the minimum of `E|X_1 + ⋯ + X_n|²` is attained and
positive. -/
theorem pj_cor_confine (hex : H_example) (hga : H_gadget_a) (hgb : H_gadget_b) (hd : 2 ≤ d)
    (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ V : Submodule ℝ (E d), V ≠ ⊥ → ∃ π, IsCoupling n P π ∧ ∀ᵐ x ∂π, ∑ j, x j ∈ V) ∧
      (∀ π, IsCoupling n P π → ¬ ∀ᵐ x ∂π, ∑ j, x j = 0) ∧
      ∃ π₀, IsCoupling n P π₀ ∧
        (∀ π, IsCoupling n P π → ∫ x, ‖∑ j, x j‖ ^ 2 ∂π₀ ≤ ∫ x, ‖∑ j, x j‖ ^ 2 ∂π) ∧
        0 < ∫ x, ‖∑ j, x j‖ ^ 2 ∂π₀ := by
  obtain ⟨f, P, hP, hf, hfc, -, hprob, hmean, himg, hnot⟩ := pj_thm_main hex hga hgb hd hn
  obtain ⟨R, hR⟩ := carried_of_hasCompactSupport hfc
  rw [← hP] at hR
  exact ⟨f, P, hP, hf, hfc, hprob, hmean,
    fun V hV => cor_confine_subspace hR hmean (fun L hL => himg (E d) L hL) hV,
    fun π hπ => cor_no_zero_sum hnot hπ, cor_min hR hnot⟩

end Confine

/-! ## Remark `pj:rem:positive`: products -/

/-- **Remark `pj:rem:positive`, the product claim**: a product of `n`-completely mixable
distributions on `ℝ` is `n`-completely mixable (independent complete mixes of the coordinates
form one of the product). -/
theorem rem_product {d n : ℕ} (F : Fin d → Measure ℝ) [∀ k, IsProbabilityMeasure (F k)]
    (hF : ∀ k, CompletelyMixable n (F k)) : CompletelyMixable n (Measure.pi F) := by
  choose π hπ using hF
  have hprob : ∀ k, IsProbabilityMeasure (π k) := fun k => (hπ k).1
  choose s hs using fun k => (hπ k).2.1
  have hT : Measurable fun z : Fin d → Fin n → ℝ => fun j k => z k j :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k =>
      (measurable_pi_apply j).comp (measurable_pi_apply k)
  refine ⟨(Measure.pi π).map fun z j k => z k j, inferInstance, ⟨s, ?_⟩, fun j => ?_⟩
  · have hm : MeasurableSet {y : Fin n → Fin d → ℝ | ∑ j, y j = s} :=
      Mixes.measurableSet_sum_eq' s
    rw [ae_map_iff hT.aemeasurable hm]
    have hk : ∀ k, ∀ᵐ z ∂(Measure.pi π), ∑ j, z k j = s k := fun k =>
      (measurePreserving_eval π k).quasiMeasurePreserving.ae (hs k)
    filter_upwards [ae_all_iff.2 hk] with z hz
    funext k
    simp [Finset.sum_apply, hz k]
  · rw [Measure.map_map (measurable_pi_apply j) hT]
    have e : ((fun y : Fin n → Fin d → ℝ => y j) ∘ fun z : Fin d → Fin n → ℝ => fun j k => z k j)
        = fun z k => (fun x : Fin n → ℝ => x j) (z k) := rfl
    rw [e, Measure.pi_map_pi (fun k => (measurable_pi_apply j).aemeasurable)]
    congr 1
    funext k
    exact (hπ k).2.2 j

/-! ## Analyticity of Laplace transforms of compactly supported measures -/

section Laplace

open scoped Nat InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V]

/-- The integrand of the `k`-th coefficient. -/
def lapQ (k : ℕ) (y : V) : ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
    (fun _ => innerSL ℝ y)

lemma lapQ_continuous (k : ℕ) : Continuous (lapQ (V := V) k) := by
  have : (lapQ (V := V) k) = fun y =>
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMapLRight
        (fun _ => innerSL ℝ y) := by
    funext y; rfl
  rw [this]
  exact (ContinuousMultilinearMap.coe_continuous _).comp
    (continuous_pi fun _ => (innerSL ℝ (E := V)).continuous)

lemma lapQ_apply (k : ℕ) (y x : V) : lapQ k y (fun _ => x) = ⟪y, x⟫_ℝ ^ k := by
  simp [lapQ, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

lemma lapQ_norm (k : ℕ) (y : V) : ‖lapQ k y‖ ≤ ‖y‖ ^ k := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.norm_mkPiAlgebra, one_mul]
  simp [innerSL_apply_norm]

/-- **Analyticity of a Laplace transform**: for a finite measure `μ` carried by a ball and a
bounded weight `w`, `x ↦ ∫ exp⟪y, x⟫ w(y) dμ(y)` is real analytic on all of `V`. -/
theorem laplace_analytic (μ : Measure V) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) {w : V → ℝ} (hw : Measurable w) {C : ℝ}
    (hC : ∀ y, |w y| ≤ C) :
    AnalyticOnNhd ℝ (fun x => ∫ y, Real.exp ⟪y, x⟫_ℝ * w y ∂μ) univ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set R' := |R|
  have hR' : ∀ᵐ y ∂μ, ‖y‖ ≤ R' := by
    filter_upwards [hR] with y hy using hy.trans (le_abs_self R)
  set M := μ.real univ
  have hM : 0 ≤ M := measureReal_nonneg
  have hint : ∀ k, Integrable (fun y => (w y / k !) • lapQ (V := V) k y) μ := by
    intro k
    refine Integrable.of_bound ((hw.div_const _).aestronglyMeasurable.smul (lapQ_continuous k).aestronglyMeasurable)
      (C / k ! * R' ^ k) ?_
    filter_upwards [hR'] with y hy
    rw [norm_smul, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact mul_le_mul (div_le_div_of_nonneg_right (hC y) (by positivity))
      ((lapQ_norm k y).trans (pow_le_pow_left₀ (norm_nonneg _) hy k)) (norm_nonneg _)
      (by positivity)
  let p : FormalMultilinearSeries ℝ V ℝ := fun k => ∫ y, (w y / k !) • lapQ k y ∂μ
  have hpnorm : ∀ k, ‖p k‖ ≤ C / k ! * R' ^ k * M := by
    intro k
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hR'] with y hy
    rw [norm_smul, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact mul_le_mul (div_le_div_of_nonneg_right (hC y) (by positivity))
      ((lapQ_norm k y).trans (pow_le_pow_left₀ (norm_nonneg _) hy k)) (norm_nonneg _)
      (by positivity)
  have hpapply : ∀ k (x : V), p k (fun _ => x) = ∫ y, w y / k ! * ⟪y, x⟫_ℝ ^ k ∂μ := by
    intro k x
    have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => V) ℝ (fun _ => x)).integral_comp_comm
      (hint k)
    simp only [ContinuousMultilinearMap.apply_apply] at this
    rw [show p k (fun _ => x) = _ from this.symm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [lapQ_apply]
  have hrad : p.radius = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    refine p.le_radius_of_bound (C * M * Real.exp (R' * r)) fun k => ?_
    calc ‖p k‖ * (r : ℝ) ^ k ≤ C / k ! * R' ^ k * M * (r : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (hpnorm k) (by positivity)
      _ = C * M * ((R' * r) ^ k / k !) := by rw [mul_pow]; ring
      _ ≤ C * M * Real.exp (R' * r) :=
          mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) k)
            (by positivity)
  have hps : HasFPowerSeriesOnBall (fun x => ∫ y, Real.exp ⟪y, x⟫_ℝ * w y ∂μ) p 0 ⊤ := by
    refine ⟨hrad.ge, ENNReal.zero_lt_top, fun {x} _ => ?_⟩
    simp only [hpapply, zero_add]
    refine hasSum_integral_of_dominated_convergence (fun k _ => C * (R' * ‖x‖) ^ k / k !)
      (fun k => ((hw.div_const _).aestronglyMeasurable.mul (by fun_prop : Continuous fun y : V =>
        ⟪y, x⟫_ℝ ^ k).aestronglyMeasurable)) (fun k => ?_)
      (Eventually.of_forall fun _ => by
        simpa [mul_div_assoc] using (Real.summable_pow_div_factorial (R' * ‖x‖)).mul_left C)
      (integrable_const _) (Eventually.of_forall fun y => ?_)
    · filter_upwards [hR'] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_div, Nat.abs_cast, abs_pow]
      have h1 : |⟪y, x⟫_ℝ| ≤ R' * ‖x‖ :=
        (abs_real_inner_le_norm y x).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
      have h2 : |⟪y, x⟫_ℝ| ^ k ≤ (R' * ‖x‖) ^ k := pow_le_pow_left₀ (abs_nonneg _) h1 k
      calc |w y| / k ! * |⟪y, x⟫_ℝ| ^ k ≤ C / k ! * (R' * ‖x‖) ^ k :=
            mul_le_mul (div_le_div_of_nonneg_right (hC y) (by positivity)) h2 (by positivity)
              (by positivity)
        _ = C * (R' * ‖x‖) ^ k / k ! := by ring
    · have := (NormedSpace.expSeries_div_hasSum_exp (⟪y, x⟫_ℝ)).mul_left (w y)
      rw [← Real.exp_eq_exp_ℝ] at this
      convert this using 1
      · funext k; ring
      · ring
  intro x _
  exact hps.analyticAt_of_mem (by simp)

end Laplace

/-! ## The Gaussian kernel -/

section Gauss

variable {d : ℕ}

/-- `exp(-|x|²/2)`. -/
def gauss (x : E d) : ℝ := Real.exp (-(1 / 2) * ‖x‖ ^ 2)

lemma gauss_continuous : Continuous (gauss (d := d)) := by unfold gauss; fun_prop

lemma gauss_pos (x : E d) : 0 < gauss x := Real.exp_pos _

lemma gauss_le_one (x : E d) : gauss x ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg x])

lemma gauss_integral : ∫ x : E d, gauss x = (Real.pi / (1 / 2)) ^ (d / 2 : ℝ) := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E d) (b := 1 / 2) (by norm_num)
  simpa [gauss, finrank_euclideanSpace] using this

/-- The normalising constant `(2π)^{d/2}`. -/
def gZ (d : ℕ) : ℝ := ∫ x : E d, gauss x

lemma gZ_pos : 0 < gZ d := by
  rw [gZ, gauss_integral]; positivity

lemma gauss_integrable : Integrable (gauss (d := d)) :=
  Integrable.of_integral_ne_zero (gZ_pos (d := d)).ne'

/-- The standard Gaussian density `γ`. -/
def gam (x : E d) : ℝ := gauss x / gZ d

@[fun_prop] lemma gam_continuous : Continuous (gam (d := d)) := gauss_continuous.div_const _

@[fun_prop] lemma gam_measurable : Measurable (gam (d := d)) := gam_continuous.measurable

lemma gam_pos (x : E d) : 0 < gam x := div_pos (gauss_pos x) gZ_pos

lemma gam_le (x : E d) : gam x ≤ 1 / gZ d :=
  div_le_div_of_nonneg_right (gauss_le_one x) gZ_pos.le

lemma gam_integrable : Integrable (gam (d := d)) := gauss_integrable.div_const _

lemma gam_integral : ∫ x : E d, gam x = 1 := by
  simp only [gam]; rw [integral_div]; exact div_self gZ_pos.ne'

/-- The standard Gaussian distribution on `ℝ^d`, as a measure with density. -/
def Gs (d : ℕ) : Measure (E d) := volume.withDensity fun x => ENNReal.ofReal (gam x)

instance Gs_isProb : IsProbabilityMeasure (Gs d) := by
  constructor
  rw [Gs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal gam_integrable
      (Eventually.of_forall fun x => (gam_pos x).le), gam_integral, ENNReal.ofReal_one]

lemma Gs_isRotInv : Mixes.Ball.IsRotInv (Gs d) := by
  intro L
  have hg : Measurable fun r : ℝ => ENNReal.ofReal (Real.exp (-(1 / 2) * r ^ 2) / gZ d) :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun r : ℝ =>
      Real.exp (-(1 / 2) * r ^ 2)).div_const _)
  exact Mixes.Ball.withDensity_radial_map_iso _ hg L

lemma Gs_mean : ∫ x, x ∂(Gs d) = 0 := Mixes.Ball.integral_id_eq_zero Gs_isRotInv

lemma Gs_cm (hd : 2 ≤ d) {n : ℕ} (hn : 2 ≤ n) : CompletelyMixable n (Gs d) :=
  Mixes.Ball.completelyMixable_of_isRotInv Mixes.Sphere.sphereUniqueness
    (by simp; omega) Gs_isRotInv hn

lemma norm_mul_gauss_le (x : E d) :
    ‖x‖ * gauss x ≤ 3 * Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by
  set t := ‖x‖
  have h1 : t ≤ 3 * Real.exp ((1 / 4) * t ^ 2) := by
    have := Real.add_one_le_exp ((1 / 4) * t ^ 2)
    nlinarith [sq_nonneg (t - 2)]
  have h2 : Real.exp ((1 / 4) * t ^ 2) * gauss x = Real.exp (-(1 / 4) * t ^ 2) := by
    rw [gauss, ← Real.exp_add]; congr 1; simp only [t]; ring
  calc t * gauss x ≤ 3 * Real.exp ((1 / 4) * t ^ 2) * gauss x :=
        mul_le_mul_of_nonneg_right h1 (gauss_pos x).le
    _ = 3 * Real.exp (-(1 / 4) * t ^ 2) := by rw [mul_assoc, h2]

lemma Gs_integrable_id : Integrable id (Gs d) := by
  have hf : Measurable fun x : E d => ENNReal.ofReal (gam x) :=
    ENNReal.measurable_ofReal.comp gam_continuous.measurable
  rw [Gs, integrable_withDensity_iff_integrable_smul' hf
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hi : Integrable (fun x : E d => 3 * Real.exp (-(1 / 4) * ‖x‖ ^ 2) / gZ d) := by
    have : ∫ x : E d, Real.exp (-(1 / 4) * ‖x‖ ^ 2) ≠ 0 := by
      rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num)]; positivity
    exact ((Integrable.of_integral_ne_zero this).const_mul 3).div_const _
  refine hi.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [ENNReal.toReal_ofReal (gam_pos x).le, norm_smul, Real.norm_eq_abs,
    abs_of_pos (gam_pos x), id, gam, div_mul_eq_mul_div, mul_comm]
  exact div_le_div_of_nonneg_right (norm_mul_gauss_le x) gZ_pos.le

lemma Gs_tail {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ r : ℕ, Gs d (closedBall 0 r)ᶜ ≤ ε := by
  have hanti : Antitone fun k : ℕ => (closedBall (0 : E d) k)ᶜ := fun a b hab =>
    compl_subset_compl.2 (closedBall_subset_closedBall (by exact_mod_cast hab))
  have hempty : (⋂ k : ℕ, (closedBall (0 : E d) k)ᶜ) = ∅ := by
    ext x
    simp only [mem_iInter, mem_compl_iff, mem_closedBall, dist_zero_right, not_le,
      mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    exact ⟨k, hk⟩
  have ht := tendsto_measure_iInter_atTop (μ := Gs d)
    (fun k => measurableSet_closedBall.compl.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at ht
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop_zero.1 ht) ε hε
  exact ⟨k, hk k le_rfl⟩

end Gauss

/-! ## Gaussian smoothing: `P_δ = P₀ * N(0, δ² I)` -/

section GaussSmooth

variable {d : ℕ} {P₀ : Measure (E d)} [IsProbabilityMeasure P₀]

variable (P₀) in
/-- `P_δ`, the law of `X + δ Y` with `X ∼ P₀` and `Y` standard Gaussian, independent. -/
def PG (δ : ℝ) : Measure (E d) := (P₀.prod (Gs d)).map fun p => p.1 + δ • p.2

/-- The Gaussian kernel `η_δ(u) = δ^{-d} γ(u/δ)`. -/
def kG (d : ℕ) (δ : ℝ) (u : E d) : ℝ := |δ ^ d|⁻¹ * gam (δ⁻¹ • u)

variable (P₀) in
/-- The density of `P_δ`, `x ↦ ∫ η_δ(x - y) dP₀(y)`. -/
def fG (δ : ℝ) (x : E d) : ℝ := ∫ y, kG d δ (x - y) ∂P₀

lemma kG_continuous (δ : ℝ) : Continuous (kG d δ) := by
  unfold kG; exact continuous_const.mul (gam_continuous.comp (continuous_const_smul _))

lemma kG_pos {δ : ℝ} (hδ : δ ≠ 0) (u : E d) : 0 < kG d δ u :=
  mul_pos (inv_pos.2 (abs_pos.2 (pow_ne_zero _ hδ))) (gam_pos _)

lemma kG_le (δ : ℝ) (u : E d) : kG d δ u ≤ |δ ^ d|⁻¹ * (1 / gZ d) :=
  mul_le_mul_of_nonneg_left (gam_le _) (by positivity)

lemma kG_integrable (δ : ℝ) (z : E d) : Integrable (fun y => kG d δ (z - y)) P₀ := by
  refine Integrable.of_bound ((kG_continuous δ).comp (continuous_const.sub continuous_id)
    ).aestronglyMeasurable (|δ ^ d|⁻¹ * (1 / gZ d)) (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ kG d δ (z - y) := mul_nonneg (by positivity) (gam_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact kG_le δ _

lemma Gs_preimage {δ : ℝ} (hδ : δ ≠ 0) (x : E d) {A : Set (E d)} (hA : MeasurableSet A) :
    Gs d ((fun y => x + δ • y) ⁻¹' A) = ∫⁻ w in A, ENNReal.ofReal (kG d δ (w - x)) := by
  have hpre : MeasurableSet ((fun y : E d => x + δ • y) ⁻¹' A) :=
    hA.preimage (by fun_prop)
  set ψ : E d → ℝ≥0∞ := A.indicator fun w => ENNReal.ofReal (gam (δ⁻¹ • (w - x)))
  have hψ : Measurable ψ := (Measurable.indicator (by fun_prop) hA)
  have key : ∀ y, ((fun y : E d => x + δ • y) ⁻¹' A).indicator
      (fun y => ENNReal.ofReal (gam y)) y = ψ (x + δ • y) := by
    intro y
    by_cases h : x + δ • y ∈ A
    · simp [ψ, indicator, h, smul_smul, inv_mul_cancel₀ hδ]
    · simp [ψ, indicator, h]
  rw [Gs, withDensity_apply _ hpre, ← lintegral_indicator hpre]
  simp_rw [key]
  rw [show (∫⁻ y, ψ (x + δ • y)) = ∫⁻ z, ψ (x + z) ∂(volume.map (δ • ·)) from
    (lintegral_map (hψ.comp (measurable_const_add x)) (measurable_const_smul δ)).symm,
    Measure.map_addHaar_smul volume hδ, lintegral_smul_measure,
    lintegral_add_left_eq_self ψ x, lintegral_indicator hA, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul, ← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_congr fun w => ?_
  rw [kG, ENNReal.ofReal_mul (by positivity), abs_inv]

lemma PG_eq_withDensity {δ : ℝ} (hδ : δ ≠ 0) :
    PG P₀ δ = volume.withDensity fun x => ENNReal.ofReal (fG P₀ δ x) := by
  ext A hA
  have hm : Measurable fun p : E d × E d => p.1 + δ • p.2 := by fun_prop
  rw [PG, Measure.map_apply hm hA, Measure.prod_apply (hm hA), withDensity_apply _ hA]
  have h1 : ∀ x : E d, Gs d (Prod.mk x ⁻¹' ((fun p : E d × E d => p.1 + δ • p.2) ⁻¹' A)) =
      ∫⁻ w in A, ENNReal.ofReal (kG d δ (w - x)) := fun x => Gs_preimage hδ x hA
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun z => ?_
    rw [fG, ofReal_integral_eq_lintegral_ofReal (kG_integrable δ z)
      (Eventually.of_forall fun y => (kG_pos hδ _).le)]
  · exact (ENNReal.measurable_ofReal.comp
      ((kG_continuous δ).measurable.comp (measurable_snd.sub measurable_fst))).aemeasurable

lemma fG_pos {δ : ℝ} (hδ : δ ≠ 0) (x : E d) : 0 < fG P₀ δ x := by
  rw [fG, integral_pos_iff_support_of_nonneg (fun y => (kG_pos hδ _).le) (kG_integrable δ x)]
  have : Function.support (fun y => kG d δ (x - y)) = univ :=
    eq_univ_of_forall fun y => (kG_pos hδ _).ne'
  rw [this, measure_univ]; exact one_pos

lemma analyticAt_norm_sq (x : E d) : AnalyticAt ℝ (fun v : E d => ‖v‖ ^ 2) x := by
  have h := (innerSL ℝ (E := E d)).analyticAt_bilinear (x, x)
  have h2 : AnalyticAt ℝ (fun v : E d => (v, v)) x := analyticAt_id.prod analyticAt_id
  have := AnalyticAt.comp (g := fun p : E d × E d => innerSL ℝ p.1 p.2)
    (f := fun v : E d => (v, v)) h h2
  convert this using 1
  funext v
  simp

lemma analyticAt_smul_const (c : ℝ) (x : E d) : AnalyticAt ℝ (fun v : E d => c • v) x := by
  have := (c • ContinuousLinearMap.id ℝ (E d)).analyticAt x
  convert this using 1
  funext v; simp

lemma gauss_split (a : ℝ) (x y : E d) :
    Real.exp (-(1 / 2) * ‖a • (x - y)‖ ^ 2) =
      Real.exp (-(1 / 2) * ‖a • x‖ ^ 2) *
        (Real.exp (inner ℝ y ((a * a) • x)) * Real.exp (-(1 / 2) * ‖a • y‖ ^ 2)) := by
  rw [← Real.exp_add, ← Real.exp_add, smul_sub, norm_sub_sq_real]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm x y]
  congr 1; ring

/-- The density of `P_δ` is real analytic. -/
lemma fG_analytic {δ : ℝ} {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0) :
    AnalyticOnNhd ℝ (fG P₀ δ) univ := by
  set H : E d → ℝ := fun z => ∫ y, Real.exp (inner ℝ y z) *
    Real.exp (-(1 / 2) * ‖δ⁻¹ • y‖ ^ 2) ∂P₀
  have hH : AnalyticOnNhd ℝ H univ := by
    refine laplace_analytic P₀ (ae_of_carried hR) (by fun_prop) (C := 1) fun y => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg (δ⁻¹ • y)])
  have hfun : fG P₀ δ = fun x => (|δ ^ d|⁻¹ / gZ d * Real.exp (-(1 / 2) * ‖δ⁻¹ • x‖ ^ 2)) *
      H ((δ⁻¹ * δ⁻¹) • x) := by
    funext x
    simp only [fG, kG, gam, gauss, H]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [gauss_split]; ring
  rw [hfun]
  intro x _
  refine AnalyticAt.mul (analyticAt_const.mul (analyticAt_rexp.comp
    (analyticAt_const.mul ((analyticAt_norm_sq _).comp (analyticAt_smul_const _ x)))))
    ((hH _ (mem_univ _)).comp (analyticAt_smul_const _ x))

lemma PG_isProb (δ : ℝ) : IsProbabilityMeasure (PG P₀ δ) := by unfold PG; infer_instance

lemma PG_integrable {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0) (δ : ℝ) :
    Integrable id (PG P₀ δ) := by
  have hm : Measurable fun p : E d × E d => p.1 + δ • p.2 := by fun_prop
  rw [PG, integrable_map_measure aestronglyMeasurable_id hm.aemeasurable]
  exact ((integrable_id_of_carried hR).comp_fst _).add
    ((Gs_integrable_id.comp_snd _).smul δ)

lemma PG_mean {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0) (hmean : ∫ x, x ∂P₀ = 0) (δ : ℝ) :
    ∫ x, x ∂(PG P₀ δ) = 0 := by
  have hi1 : Integrable (fun p : E d × E d => p.1) (P₀.prod (Gs d)) :=
    (integrable_id_of_carried hR).comp_fst _
  have hi2 : Integrable (fun p : E d × E d => δ • p.2) (P₀.prod (Gs d)) :=
    (Gs_integrable_id.comp_snd _).smul δ
  unfold PG
  rw [integral_map (f := fun x => x) (by fun_prop) aestronglyMeasurable_id,
    integral_add hi1 hi2, integral_fun_fst (fun x : E d => x),
    integral_fun_snd (fun x : E d => δ • x), integral_smul, hmean, Gs_mean]
  simp

lemma PG_map_cm (hd : 2 ≤ d) (δ : ℝ) {n : ℕ} (hn : 2 ≤ n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : E d →ₗ[ℝ] F) (h0 : CompletelyMixable n (P₀.map L)) :
    CompletelyMixable n ((PG P₀ δ).map L) := by
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  set φ : E d →ₗ[ℝ] F := L.comp (δ • LinearMap.id)
  have hφ : Measurable φ := φ.continuous_of_finiteDimensional.measurable
  obtain ⟨π₀, h₀⟩ := h0
  obtain ⟨πN, hN⟩ := Gs_cm (d := d) hd hn
  have hN' := Mixes.IsJointMix.map_affine hN φ.toAddMonoidHom hφ (fun _ => 0)
  have hP := (Mixes.IsJointMix.prod h₀ hN').map_add_hom
    (AddMonoidHom.coprod (AddMonoidHom.id F) (AddMonoidHom.id F))
    (by
      have e : ⇑(AddMonoidHom.coprod (AddMonoidHom.id F) (AddMonoidHom.id F)) =
          fun p : F × F => p.1 + p.2 := by funext p; simp
      rw [e]; exact measurable_fst.add measurable_snd)
    (fun _ => 0)
  have heq : ((P₀.map L).prod ((Gs d).map fun x => 0 + φ.toAddMonoidHom x)).map
      (fun x => 0 + (AddMonoidHom.coprod (AddMonoidHom.id F) (AddMonoidHom.id F)) x) =
      (PG P₀ δ).map L := by
    simp only [zero_add, AddMonoidHom.coprod_apply, AddMonoidHom.id_apply,
      LinearMap.toAddMonoidHom_coe]
    rw [Measure.map_prod_map _ _ hL hφ, Measure.map_map (by fun_prop) (by fun_prop), PG,
      Measure.map_map hL (by fun_prop)]
    congr 1
    funext p
    simp [φ]
  rw [heq] at hP
  exact ⟨_, hP⟩

lemma dk_tendsto : Tendsto dk atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

lemma PG_tendsto (g : E d →ᵇ ℝ) :
    Tendsto (fun k => ∫ z, g z ∂(PG P₀ (dk k))) atTop (𝓝 (∫ z, g z ∂P₀)) := by
  have hF : ∀ k, ∫ z, g z ∂(PG P₀ (dk k)) = ∫ p, g (p.1 + dk k • p.2) ∂(P₀.prod (Gs d)) := by
    intro k
    rw [PG, integral_map (by fun_prop) g.continuous.aestronglyMeasurable]
  have hlim : ∫ z, g z ∂P₀ = ∫ p, g p.1 ∂(P₀.prod (Gs d)) := by
    rw [integral_fun_fst (fun x : E d => g x)]; simp
  simp_rw [hF]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun k => ?_)
    (integrable_const _) (fun k => Eventually.of_forall fun p => g.norm_coe_le_norm _)
    (Eventually.of_forall fun p => ?_)
  · exact (g.continuous.comp (by fun_prop)).aestronglyMeasurable
  · have : Tendsto (fun k => p.1 + dk k • p.2) atTop (𝓝 (p.1 + (0 : ℝ) • p.2)) :=
      tendsto_const_nhds.add (dk_tendsto.smul_const p.2)
    rw [zero_smul, add_zero] at this
    exact (g.continuous.tendsto _).comp this

lemma PG_compl_le {δ R r : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hR : P₀ (closedBall 0 R)ᶜ = 0) :
    PG P₀ δ (closedBall 0 (R + r))ᶜ ≤ Gs d (closedBall 0 r)ᶜ := by
  have hm : Measurable fun p : E d × E d => p.1 + δ • p.2 := by fun_prop
  rw [PG, Measure.map_apply hm measurableSet_closedBall.compl]
  have hsub : (fun p : E d × E d => p.1 + δ • p.2) ⁻¹' (closedBall 0 (R + r))ᶜ ⊆
      (closedBall 0 R)ᶜ ×ˢ univ ∪ univ ×ˢ (closedBall 0 r)ᶜ := by
    intro p hp
    simp only [mem_preimage, mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hp
    by_contra hc
    simp only [mem_union, mem_prod, mem_compl_iff, mem_closedBall, dist_zero_right, not_le,
      mem_univ, and_true, true_and, not_or, not_lt] at hc
    have : ‖p.1 + δ • p.2‖ ≤ R + r := by
      calc ‖p.1 + δ • p.2‖ ≤ ‖p.1‖ + ‖δ • p.2‖ := norm_add_le _ _
        _ = ‖p.1‖ + δ * ‖p.2‖ := by rw [norm_smul, Real.norm_of_nonneg hδ0]
        _ ≤ R + 1 * r := by gcongr; exact hc.1; exact hc.2
        _ = R + r := by ring
    linarith
  calc (P₀.prod (Gs d)) ((fun p : E d × E d => p.1 + δ • p.2) ⁻¹' (closedBall 0 (R + r))ᶜ)
      ≤ (P₀.prod (Gs d)) ((closedBall 0 R)ᶜ ×ˢ univ ∪ univ ×ˢ (closedBall 0 r)ᶜ) :=
        measure_mono hsub
    _ ≤ (P₀.prod (Gs d)) ((closedBall 0 R)ᶜ ×ˢ univ) +
        (P₀.prod (Gs d)) (univ ×ˢ (closedBall 0 r)ᶜ) := measure_union_le _ _
    _ = Gs d (closedBall 0 r)ᶜ := by
        rw [Measure.prod_prod, Measure.prod_prod, hR]; simp

end GaussSmooth

/-! ## The analytic variant of Theorem `pj:thm:main` -/

section AnalyticMain

variable {d n : ℕ} {P₀ : Measure (E d)} [IsProbabilityMeasure P₀]

/-- Some Gaussian smoothing `P_{δ_k}` of `P₀` is not `n`-completely mixable (tightness replaces
the compact support of the bump case). -/
theorem PG_not_cm {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0)
    (hmean : ∫ x, x ∂P₀ = 0) (hnot : ¬ CompletelyMixable n P₀) :
    ∃ k, ¬ CompletelyMixable n (PG P₀ (dk k)) := by
  by_contra hall
  push Not at hall
  choose π hπ using hall
  have hprob : ∀ k, IsProbabilityMeasure (π k) := fun k => (hπ k).1
  have hPk : ∀ k, IsProbabilityMeasure (PG P₀ (dk k)) := fun k => PG_isProb _
  have hsum : ∀ k, ∀ᵐ x ∂(π k), ∑ j, x j = 0 := by
    intro k
    have := Mixes.Homothetic.IsJointMix.ae_sum_eq (hπ k) (fun _ => PG_integrable hR _)
    simpa [PG_mean hR hmean] using this
  have htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set (Fin n → E d), IsCompact K ∧
      ∀ k, π k Kᶜ ≤ ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := Gs_tail (d := d) (ε := ε / n)
      (ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top n))
    refine ⟨univ.pi fun _ => closedBall 0 (R + r),
      isCompact_univ_pi fun _ => isCompact_closedBall _ _, fun k => ?_⟩
    have hsub : (univ.pi fun _ => closedBall (0 : E d) (R + r))ᶜ ⊆
        ⋃ j, (fun x : Fin n → E d => x j) ⁻¹' (closedBall 0 (R + r))ᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_univ_pi, not_forall] at hx
      obtain ⟨j, hj⟩ := hx
      exact mem_iUnion.2 ⟨j, hj⟩
    have hj : ∀ j, π k ((fun x : Fin n → E d => x j) ⁻¹' (closedBall 0 (R + r))ᶜ) ≤ ε / n := by
      intro j
      rw [← Measure.map_apply (measurable_pi_apply j) measurableSet_closedBall.compl,
        (hπ k).2.2 j]
      exact (PG_compl_le (dk_pos k).le (dk_le_one k) hR).trans hr
    calc π k (univ.pi fun _ => closedBall (0 : E d) (R + r))ᶜ
        ≤ π k (⋃ j, (fun x : Fin n → E d => x j) ⁻¹' (closedBall 0 (R + r))ᶜ) :=
          measure_mono hsub
      _ ≤ ∑ j, π k ((fun x : Fin n → E d => x j) ⁻¹' (closedBall 0 (R + r))ᶜ) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin n, ε / n := Finset.sum_le_sum fun j _ => hj j
      _ = n * (ε / n) := by simp
      _ ≤ ε := ENNReal.mul_div_le
  obtain ⟨π', hπ', φ, hφ, hlim⟩ := exists_weak_limit_tight π htight
  have hmarg : ∀ j, π'.map (fun x => x j) = P₀ := by
    intro j
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    let gj : (Fin n → E d) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => g (x j)) (g.continuous.comp (continuous_apply j)) ‖g‖
      (fun x => g.norm_coe_le_norm _)
    have h1 := hlim gj
    have h2 : (fun k => ∫ x, gj x ∂(π (φ k))) = fun k => ∫ z, g z ∂(PG P₀ (dk (φ k))) := by
      funext k
      have hm : (π (φ k)).map (fun x => x j) = PG P₀ (dk (φ k)) := (hπ (φ k)).2.2 j
      rw [← hm, integral_map (measurable_pi_apply j).aemeasurable
        g.continuous.aestronglyMeasurable]
      rfl
    rw [h2] at h1
    rw [integral_map (measurable_pi_apply j).aemeasurable g.continuous.aestronglyMeasurable]
    exact tendsto_nhds_unique h1 ((PG_tendsto g).comp hφ.tendsto_atTop)
  let h : (Fin n → E d) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min 1 ‖∑ j, x j‖) (by fun_prop) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (norm_nonneg _))]
      exact min_le_left _ _)
  have hh0 : ∫ x, h x ∂π' = 0 := by
    refine tendsto_nhds_unique (hlim h) ?_
    have : ∀ k, ∫ x, h x ∂(π (φ k)) = 0 := fun k => integral_eq_zero_of_ae (by
      filter_upwards [hsum (φ k)] with x hx
      simp [h, hx])
    simp only [this]
    exact tendsto_const_nhds
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => le_min zero_le_one (norm_nonneg _))
    (h.integrable π')).1 hh0
  refine hnot ⟨π', hπ', ⟨0, ?_⟩, hmarg⟩
  filter_upwards [hae] with x hx
  have hx' : min 1 ‖∑ j, x j‖ = 0 := hx
  rcases min_eq_iff.1 hx' with h1 | h1
  · exact absurd h1.1 one_ne_zero
  · exact norm_eq_zero.1 h1.1

/-- The Gaussian smoothing step: a distribution with the properties of `P₀` and an everywhere
positive real-analytic density. -/
theorem smoothing_analytic (hd : 2 ≤ d) (hn : 2 ≤ n) {R : ℝ} (hR : P₀ (closedBall 0 R)ᶜ = 0)
    (hmean : ∫ x, x ∂P₀ = 0)
    (himg : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
      [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
      CompletelyMixable n (P₀.map L))
    (hnot : ¬ CompletelyMixable n P₀) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      AnalyticOnNhd ℝ f univ ∧ ContDiff ℝ ∞ f ∧ (∀ x, 0 < f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
        [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable n (P.map L)) ∧
      ¬ CompletelyMixable n P := by
  obtain ⟨k, hk⟩ := PG_not_cm hR hmean hnot
  have hδ : dk k ≠ 0 := (dk_pos k).ne'
  have han := fG_analytic (P₀ := P₀) (δ := dk k) hR
  exact ⟨fG P₀ (dk k), PG P₀ (dk k), PG_eq_withDensity hδ, han, han.contDiff, fG_pos hδ,
    PG_isProb _, PG_mean hR hmean _,
    fun F _ _ _ _ _ L hL => PG_map_cm hd _ hn L (himg F L hL), hk⟩

end AnalyticMain

/-- **Theorem `pj:thm:main`, last sentence** (given Lemmas `pj:lem:example` and `pj:lem:gadget`):
for `d ≥ 2` and `n ≥ 3` there is a distribution `P` on `ℝ^d` with mean `0` and an everywhere
positive real-analytic density `f` such that the image of `P` under every linear map with a
nonzero kernel is `n`-completely mixable, while `P` is not. -/
theorem pj_thm_main_analytic (hex : H_example) (hga : H_gadget_a) (hgb : H_gadget_b) {d n : ℕ}
    (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      AnalyticOnNhd ℝ f univ ∧ ContDiff ℝ ∞ f ∧ (∀ x, 0 < f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
        [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable n (P.map L)) ∧
      ¬ CompletelyMixable n P := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m := ⟨n - 3, by omega⟩
  obtain ⟨P₀, hP₀, ⟨R, hR⟩, hmean, himg, hnot⟩ := exists_P0 hex hga hgb hd m
  exact smoothing_analytic hd (by omega) hR hmean himg hnot

/-! ## Unconditional versions (the lemmas from `ProjLemmas.lean`) -/

theorem H_example_holds : H_example := fun _ hd _ hw =>
  ⟨⟨ex_Qf_nonneg hd hw, ex_Qf_le hd hw, ex_isProb_Q hd hw, ex_Q_compl hd hw, ex_isProb hd hw,
    ex_support hd hw, ex_mean hd hw⟩, ex_not_jointlyMixable hd hw,
    fun _ _ _ _ _ _ L hL => ex_map_jointlyMixable hd hw L hL⟩

theorem H_gadget_a_holds : H_gadget_a := fun _ _ hn G _ lam e _ _ _ _ _ _ L h =>
  gadget_a hn G lam e L h

theorem H_gadget_b_holds : H_gadget_b := fun _ _ hn G _ _ _ _ hs hm he hl h =>
  gadget_b hn G hs hm he hl h

/-- **Theorem `pj:thm:main`** (`C^∞` part), unconditional. -/
theorem pj_thm_main_uncond {d n : ℕ} (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
        [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable n (P.map L)) ∧
      ¬ CompletelyMixable n P :=
  pj_thm_main H_example_holds H_gadget_a_holds H_gadget_b_holds hd hn

/-- **Theorem `pj:thm:main`** (analytic part), unconditional. -/
theorem pj_thm_main_analytic_uncond {d n : ℕ} (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      AnalyticOnNhd ℝ f univ ∧ ContDiff ℝ ∞ f ∧ (∀ x, 0 < f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
        [BorelSpace F] [SecondCountableTopology F] (L : E d →ₗ[ℝ] F), LinearMap.ker L ≠ ⊥ →
        CompletelyMixable n (P.map L)) ∧
      ¬ CompletelyMixable n P :=
  pj_thm_main_analytic H_example_holds H_gadget_a_holds H_gadget_b_holds hd hn

/-- **Theorem `pj:thm:main`, "in particular"**, unconditional. -/
theorem pj_thm_main_proj_uncond {d n : ℕ} (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
      IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ K : Submodule ℝ (E d), K ≠ ⊤ → CompletelyMixable n (P.map K.starProjection)) ∧
      ¬ CompletelyMixable n P :=
  pj_thm_main_proj H_example_holds H_gadget_a_holds H_gadget_b_holds hd hn

/-- **Corollary `pj:cor:confine`**, unconditional. -/
theorem pj_cor_confine_uncond {d n : ℕ} (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ (f : E d → ℝ) (P : Measure (E d)),
      P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ IsProbabilityMeasure P ∧ ∫ x, x ∂P = 0 ∧
      (∀ V : Submodule ℝ (E d), V ≠ ⊥ → ∃ π, IsCoupling n P π ∧ ∀ᵐ x ∂π, ∑ j, x j ∈ V) ∧
      (∀ π, IsCoupling n P π → ¬ ∀ᵐ x ∂π, ∑ j, x j = 0) ∧
      ∃ π₀, IsCoupling n P π₀ ∧
        (∀ π, IsCoupling n P π → ∫ x, ‖∑ j, x j‖ ^ 2 ∂π₀ ≤ ∫ x, ‖∑ j, x j‖ ^ 2 ∂π) ∧
        0 < ∫ x, ‖∑ j, x j‖ ^ 2 ∂π₀ :=
  pj_cor_confine H_example_holds H_gadget_a_holds H_gadget_b_holds hd hn

end Mixes.ProjMain

