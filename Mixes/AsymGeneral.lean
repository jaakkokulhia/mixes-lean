import Mixes.Defs
import Mixes.Large

/-!
# All large `n` without convexity (Section `as:sec:asym`)

Theorem `as:thm:general`, Corollary `as:cor:body` and Corollary `as:cor:order` of draft 14.

* `AggSet n F`: the aggregation set `𝒜_n(F)`, the laws of `X₁ + ⋯ + Xₙ` over all couplings with
  `Xᵢ ∼ F`.
* `H_thm_window d`: Theorem `as:thm:window` in `ℝ^d`, used as an explicit hypothesis (it is proved
  by another agent).
* `glue`: the gluing lemma (a regular conditional distribution, `Measure.condKernel`).
* `aggSet_conv_subset`: `𝒜_{n'}(F ∗ F) ⊆ 𝒜_{2n'}(F)`; `aggSet_succ_of_sub`: the odd step.
* `conv_ge_unif`: if `F` is not singular, `F ∗ F ≥ q U(Q')` for a cube `Q'` (density points).
* `thm_general`, `thm_general_mix`: Theorem `as:thm:general`.
* `cor_order`: Corollary `as:cor:order`.
* `cor_body`: Corollary `as:cor:body`, given John's theorem (`Large.JohnThm`); `Nstar_two`,
  `Nstar_three`: `N*₂ = 579`, `N*₃ = 27548`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric Pointwise

noncomputable section

namespace Mixes.AsymGeneral

/-! ### Definitions -/

/-- Euclidean space `ℝ^d`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The aggregation set `𝒜_n(F)`: the laws of `X₁ + ⋯ + Xₙ` over all random vectors with
`Xⱼ ∼ F`, as probability measures on `n`-tuples. -/
def AggSet {E : Type*} [MeasurableSpace E] [AddCommMonoid E] (n : ℕ) (F : Measure E) :
    Set (Measure E) :=
  {ν | ∃ P : Measure (Fin n → E), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = F) ∧
    P.map (fun x => ∑ j, x j) = ν}

/-- The box `c + ∏ᵢ [-Hᵢ, Hᵢ]`. -/
def box {d : ℕ} (c : Rd d) (H : Fin d → ℝ) : Set (Rd d) := {x | ∀ i, |x i - c i| ≤ H i}

/-- The constant `c_d`: `c₁ = 1` and `c_d = 2d` for `d ≥ 2`. -/
def cdConst (d : ℕ) : ℝ := if d = 1 then 1 else 2 * d

/-- `F` is supported in a set of diameter at most `R`. -/
def SuppDiam {d : ℕ} (F : Measure (Rd d)) (R : ℝ) : Prop :=
  ∃ S : Set (Rd d), F Sᶜ = 0 ∧ ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R

/-- The convolution square `F ∗ F`, the law of `X + X'` for independent `X, X' ∼ F`. -/
def conv {d : ℕ} (F : Measure (Rd d)) : Measure (Rd d) := (F.prod F).map (fun p => p.1 + p.2)

instance conv_isProb {d : ℕ} (F : Measure (Rd d)) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (conv F) := by
  unfold conv; infer_instance

/-- **Theorem `as:thm:window`** (explicit hypothesis; proved by another agent). Let `F` be a
distribution on `ℝ^d` with mean `μ`, supported in a set of diameter at most `R`, with
`F ≥ q U(Q)` for a box `Q = c + ∏ [-Hᵢ, Hᵢ]` and `q ∈ (0, 1]`. Let `n ≥ 1`, `m = ⌊qn⌋`,
`m' = ⌊m/d⌋`, and suppose `m' ≥ 4` and `ρᵢ = m'Hᵢ/2 - c_d R ≥ 0`. Then `𝒜_n(F)` contains every
probability measure with mean `nμ` supported in `nμ + ∏ [-ρᵢ, ρᵢ]`. -/
def H_thm_window (d : ℕ) : Prop :=
  ∀ (F : Measure (Rd d)) [IsProbabilityMeasure F] (R : ℝ) (c : Rd d) (H : Fin d → ℝ) (q : ℝ)
    (n : ℕ), SuppDiam F R → (∀ i, 0 < H i) → 0 < q → q ≤ 1 →
    ENNReal.ofReal q • unifSet (box c H) ≤ F →
    4 ≤ ⌊q * n⌋₊ / d →
    (∀ i, 0 ≤ ((⌊q * n⌋₊ / d : ℕ) : ℝ) * H i / 2 - cdConst d * R) →
    ∀ ν : Measure (Rd d), IsProbabilityMeasure ν → ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
      ν (box ((n : ℝ) • ∫ x, x ∂F)
        (fun i => ((⌊q * n⌋₊ / d : ℕ) : ℝ) * H i / 2 - cdConst d * R))ᶜ = 0 →
      ν ∈ AggSet n F

/-! ### The gluing lemma -/

section Glue

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_comap_map {π : Measure (Y × Z)} [IsFiniteMeasure π] (κ : Kernel Y X)
    [IsMarkovKernel κ] :
    (π ⊗ₘ (κ.comap Prod.fst measurable_fst)).map (fun p => (p.1.1, p.2)) =
      (π.map Prod.fst) ⊗ₘ κ := by
  ext s hs
  have hg : Measurable (fun p : (Y × Z) × X => (p.1.1, p.2)) := by fun_prop
  rw [Measure.map_apply hg hs, Measure.compProd_apply (hg hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_fst]
  rfl

/-- **The gluing lemma** (a regular conditional distribution): a probability measure `μ` on a
standard Borel space `X` and a probability measure `π` on `Y × Z` whose first marginal is the
image of `μ` under `f` glue to a probability measure `σ` on `X × Z` with first marginal `μ` and
with `(f × id)_* σ = π`. -/
theorem glue [StandardBorelSpace X] [Nonempty X] [MeasurableEq Y]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → Y} (hf : Measurable f)
    (π : Measure (Y × Z)) [IsProbabilityMeasure π] (hπ : π.map Prod.fst = μ.map f) :
    ∃ σ : Measure (X × Z), IsProbabilityMeasure σ ∧ σ.map Prod.fst = μ ∧
      σ.map (fun p => (f p.1, p.2)) = π := by
  set ρ : Measure (Y × X) := μ.map (fun x => (f x, x)) with hρ
  have hfx : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have : IsProbabilityMeasure ρ := inferInstance
  set κ := ρ.condKernel
  have hdis : ρ.fst ⊗ₘ κ = ρ := Measure.disintegrate ρ ρ.condKernel
  have hρfst : ρ.fst = μ.map f := by
    rw [Measure.fst, hρ, Measure.map_map measurable_fst hfx]; rfl
  set σ' := π ⊗ₘ (κ.comap Prod.fst measurable_fst)
  have hL : σ'.map (fun p => (p.1.1, p.2)) = ρ := by
    rw [compProd_comap_map, hπ, ← hρfst, hdis]
  have hg1 : Measurable (fun p : (Y × Z) × X => (p.1.1, p.2)) := by fun_prop
  have hdiag : MeasurableSet {q : Y × X | f q.2 = q.1} :=
    measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst
  have hae : ∀ᵐ p ∂σ', f p.2 = p.1.1 := by
    have h1 : ∀ᵐ q ∂ρ, f q.2 = q.1 := by
      rw [hρ, ae_map_iff hfx.aemeasurable hdiag]
      exact Filter.Eventually.of_forall fun x => rfl
    rw [← hL, ae_map_iff hg1.aemeasurable hdiag] at h1
    exact h1
  refine ⟨σ'.map (fun p => (p.2, p.1.2)), inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (by fun_prop)]
    have : (Prod.fst ∘ fun p : (Y × Z) × X => (p.2, p.1.2)) =
        Prod.snd ∘ (fun p : (Y × Z) × X => (p.1.1, p.2)) := rfl
    rw [this, ← Measure.map_map measurable_snd hg1, hL, hρ, Measure.map_map measurable_snd hfx]
    exact Measure.map_id
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : σ'.map (fun p => p.1) = π := by
      simp only [σ']; exact Measure.fst_compProd π _
    rw [← this]
    apply Measure.map_congr
    filter_upwards [hae] with p hp
    simp [hp]

end Glue

/-! ### `𝒜_{n'}(F ∗ F) ⊆ 𝒜_{2n'}(F)` and the odd step -/

section Refine

variable {d : ℕ}

/-- The state of the coordinate-by-coordinate refinement: the coordinates `j < k` are pairs with
law `F ⊗ F`, the others are `(w, 0)` with `w ∼ F ∗ F`, and the total sum has law `ν`. -/
def RefState (n' : ℕ) (F ν : Measure (Rd d)) (k : ℕ) (P : Measure (Fin n' → Rd d × Rd d)) :
    Prop :=
  IsProbabilityMeasure P ∧ (∀ j : Fin n', j.val < k → P.map (fun x => x j) = F.prod F) ∧
    (∀ j : Fin n', k ≤ j.val → P.map (fun x => x j) = (conv F).map (fun w => (w, (0 : Rd d)))) ∧
    P.map (fun x => ∑ j, ((x j).1 + (x j).2)) = ν

lemma refState_zero {n' : ℕ} {F ν : Measure (Rd d)} (h : ν ∈ AggSet n' (conv F)) :
    ∃ P, RefState n' F ν 0 P := by
  obtain ⟨P, hP, hm, hs⟩ := h
  have hmeas : Measurable (fun (x : Fin n' → Rd d) (j : Fin n') => (x j, (0 : Rd d))) := by
    fun_prop
  refine ⟨P.map (fun x j => (x j, (0 : Rd d))), inferInstance, fun j hj => absurd hj (by omega),
    fun j _ => ?_, ?_⟩
  · rw [Measure.map_map (by fun_prop) hmeas, ← hm j,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · rw [Measure.map_map (by fun_prop) hmeas, ← hs]
    congr 1
    funext x
    simp

lemma sum_update_comp {n' : ℕ} {α : Type*} (g : α → Rd d) (x : Fin n' → α) (k : Fin n') (a : α)
    (hk : g a = g (x k)) : ∑ j, g (Function.update x k a j) = ∑ j, g (x j) := by
  have h1 : ∀ j, g (Function.update x k a j) =
      Function.update (fun j => g (x j)) k (g a) j := fun j => by
    by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [h1, Finset.sum_update_of_mem (Finset.mem_univ k), hk]
  rw [Finset.sdiff_singleton_eq_erase]
  exact Finset.add_sum_erase _ (fun j => g (x j)) (Finset.mem_univ k)

lemma refState_succ {n' : ℕ} {F ν : Measure (Rd d)} [IsProbabilityMeasure F] {k : ℕ}
    (hk : k < n') {P : Measure (Fin n' → Rd d × Rd d)} (h : RefState n' F ν k P) :
    ∃ P', RefState n' F ν (k + 1) P' := by
  obtain ⟨hP, hlt, hge, hsum⟩ := h
  set kk : Fin n' := ⟨k, hk⟩
  set f : Rd d × Rd d → Rd d × Rd d := fun p => (p.1 + p.2, 0) with hfdef
  have hf : Measurable f := by fun_prop
  set π : Measure ((Rd d × Rd d) × (Fin n' → Rd d × Rd d)) := P.map (fun x => (x kk, x))
  have hπm : Measurable (fun x : Fin n' → Rd d × Rd d => (x kk, x)) := by fun_prop
  have hπ : π.map Prod.fst = (F.prod F).map f := by
    rw [Measure.map_map measurable_fst hπm]
    change P.map (fun x => x kk) = _
    rw [hge kk le_rfl, conv, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := glue (F.prod F) hf π hπ
  have hh : Measurable (fun p : (Rd d × Rd d) × (Fin n' → Rd d × Rd d) => (f p.1, p.2)) := by
    fun_prop
  have hσs : σ.map Prod.snd = P := by
    have : (Prod.snd : (Rd d × Rd d) × (Fin n' → Rd d × Rd d) → _) =
        Prod.snd ∘ (fun p => (f p.1, p.2)) := rfl
    rw [this, ← Measure.map_map measurable_snd hh, hσ2, Measure.map_map measurable_snd hπm]
    exact Measure.map_id
  have hset : MeasurableSet {q : (Rd d × Rd d) × (Fin n' → Rd d × Rd d) | q.1 = q.2 kk} :=
    measurableSet_eq_fun measurable_fst (by fun_prop)
  have hae : ∀ᵐ p ∂σ, f p.1 = p.2 kk := by
    have h1 : ∀ᵐ q ∂π, q.1 = q.2 kk := by
      rw [ae_map_iff hπm.aemeasurable hset]
      exact Filter.Eventually.of_forall fun x => rfl
    rw [← hσ2, ae_map_iff hh.aemeasurable hset] at h1
    exact h1
  have hU : Measurable (fun p : (Rd d × Rd d) × (Fin n' → Rd d × Rd d) =>
      Function.update p.2 kk p.1) := by fun_prop
  have hmarg : ∀ j : Fin n', j ≠ kk → (σ.map (fun p => Function.update p.2 kk p.1)).map
      (fun x => x j) = P.map (fun x => x j) := by
    intro j hj
    rw [Measure.map_map (by fun_prop) hU, ← hσs, Measure.map_map (by fun_prop) measurable_snd]
    congr 1
    funext p
    simp [Function.update_of_ne hj]
  refine ⟨σ.map (fun p => Function.update p.2 kk p.1), inferInstance, fun j hj => ?_,
    fun j hj => ?_, ?_⟩
  · by_cases hjk : j = kk
    · subst hjk
      rw [Measure.map_map (by fun_prop) hU, ← hσ1]
      congr 1
      funext p
      simp
    · have : j.val < k := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact h
        · exact absurd (Fin.ext h) hjk
      rw [hmarg j hjk, hlt j this]
  · have hjk : j ≠ kk := fun h => by rw [h] at hj; exact Nat.not_succ_le_self k hj
    rw [hmarg j hjk, hge j (by omega)]
  · rw [Measure.map_map (by fun_prop) hU, ← hsum, ← hσs,
      Measure.map_map (by fun_prop) measurable_snd]
    apply Measure.map_congr
    filter_upwards [hae] with p hp
    simp only [Function.comp]
    apply sum_update_comp (fun e : Rd d × Rd d => e.1 + e.2)
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    simp only [hfdef] at h1 h2
    simp [← h1, ← h2]

lemma aggSet_of_refState {n' : ℕ} {F ν : Measure (Rd d)} [IsProbabilityMeasure F]
    {P : Measure (Fin n' → Rd d × Rd d)} (h : RefState n' F ν n' P) :
    ν ∈ AggSet (2 * n') F := by
  obtain ⟨hP, hlt, -, hsum⟩ := h
  set flat : (Fin n' → Rd d × Rd d) → (Fin (2 * n') → Rd d) := fun x l =>
    if (finProdFinEquiv.symm l).1 = 0 then (x (finProdFinEquiv.symm l).2).1
    else (x (finProdFinEquiv.symm l).2).2 with hflat
  have hmc : ∀ l, Measurable (fun x : Fin n' → Rd d × Rd d => flat x l) := by
    intro l
    simp only [hflat]
    split_ifs <;> fun_prop
  have hm : Measurable flat := measurable_pi_iff.mpr hmc
  refine ⟨P.map flat, inferInstance, fun l => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply l) hm]
    have hj := hlt (finProdFinEquiv.symm l).2 (finProdFinEquiv.symm l).2.isLt
    by_cases h0 : (finProdFinEquiv.symm l).1 = 0
    · have : (fun x => x l) ∘ flat = Prod.fst ∘ (fun x => x (finProdFinEquiv.symm l).2) := by
        funext x; simp only [hflat, Function.comp, h0, ↓reduceIte]
      rw [this, ← Measure.map_map measurable_fst (measurable_pi_apply _), hj,
        Measure.map_fst_prod]
      simp
    · have : (fun x => x l) ∘ flat = Prod.snd ∘ (fun x => x (finProdFinEquiv.symm l).2) := by
        funext x; simp only [hflat, Function.comp, h0, ↓reduceIte]
      rw [this, ← Measure.map_map measurable_snd (measurable_pi_apply _), hj,
        Measure.map_snd_prod]
      simp
  · rw [Measure.map_map (by fun_prop) hm, ← hsum]
    congr 1
    funext x
    simp only [Function.comp, hflat]
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, Fin.sum_univ_two,
      Finset.sum_add_distrib]
    simp

/-- `𝒜_{n'}(F ∗ F) ⊆ 𝒜_{2n'}(F)`: each variable with law `F ∗ F` is replaced by a pair with law
`F ⊗ F` and the same sum, drawn from a regular conditional distribution. -/
theorem aggSet_conv_subset {n' : ℕ} {F ν : Measure (Rd d)} [IsProbabilityMeasure F]
    (h : ν ∈ AggSet n' (conv F)) : ν ∈ AggSet (2 * n') F := by
  have : ∀ k ≤ n', ∃ P, RefState n' F ν k P := by
    intro k hk
    induction k with
    | zero => exact refState_zero h
    | succ k ih =>
      obtain ⟨P, hP⟩ := ih (by omega)
      exact refState_succ (by omega) hP
  obtain ⟨P, hP⟩ := this n' le_rfl
  exact aggSet_of_refState hP

/-- The odd step: if the law of `Z - X₀` (`Z ∼ ν'`, `X₀ ∼ F` independent) lies in `𝒜_m(F)`, then
`ν' ∈ 𝒜_{m+1}(F)`. -/
theorem aggSet_succ_of_sub {m : ℕ} {F ν' : Measure (Rd d)} [IsProbabilityMeasure F]
    [IsProbabilityMeasure ν'] (h : (ν'.prod F).map (fun p => p.1 - p.2) ∈ AggSet m F) :
    ν' ∈ AggSet (m + 1) F := by
  obtain ⟨P, hP, hm, hs⟩ := h
  set π : Measure (Rd d × Rd d) := (ν'.prod F).map (fun p => (p.1 - p.2, p.2))
  have hπm : Measurable (fun p : Rd d × Rd d => (p.1 - p.2, p.2)) := by fun_prop
  have hπ : π.map Prod.fst = P.map (fun x => ∑ j, x j) := by
    rw [hs, Measure.map_map measurable_fst hπm]; rfl
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := glue P (by fun_prop) π hπ
  have hc : Measurable (fun p : (Fin m → Rd d) × Rd d => (Fin.cons p.2 p.1 : Fin (m + 1) → Rd d)) :=
    by fun_prop
  have hh : Measurable (fun p : (Fin m → Rd d) × Rd d => (∑ j, p.1 j, p.2)) := by fun_prop
  refine ⟨σ.map (fun p => (Fin.cons p.2 p.1 : Fin (m + 1) → Rd d)), inferInstance,
    fun j => ?_, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply j) hc]
    refine Fin.cases ?_ (fun i => ?_) j
    · have : (fun x : Fin (m + 1) → Rd d => x 0) ∘
          (fun p : (Fin m → Rd d) × Rd d => (Fin.cons p.2 p.1 : Fin (m + 1) → Rd d)) =
          Prod.snd ∘ (fun p : (Fin m → Rd d) × Rd d => (∑ j, p.1 j, p.2)) := by
        funext p; simp
      rw [this, ← Measure.map_map measurable_snd hh, hσ2, Measure.map_map measurable_snd hπm]
      have : (Prod.snd ∘ fun p : Rd d × Rd d => (p.1 - p.2, p.2)) = Prod.snd := rfl
      rw [this, Measure.map_snd_prod]; simp
    · have : (fun x : Fin (m + 1) → Rd d => x i.succ) ∘
          (fun p : (Fin m → Rd d) × Rd d => (Fin.cons p.2 p.1 : Fin (m + 1) → Rd d)) =
          (fun x => x i) ∘ Prod.fst := by
        funext p; simp
      rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_fst, hσ1, hm i]
  · rw [Measure.map_map (by fun_prop) hc]
    have : (fun x : Fin (m + 1) → Rd d => ∑ j, x j) ∘
        (fun p : (Fin m → Rd d) × Rd d => (Fin.cons p.2 p.1 : Fin (m + 1) → Rd d)) =
        (fun q : Rd d × Rd d => q.2 + q.1) ∘
          (fun p : (Fin m → Rd d) × Rd d => (∑ j, p.1 j, p.2)) := by
      funext p; simp [Fin.sum_univ_succ]
    rw [this, ← Measure.map_map (by fun_prop) hh, hσ2, Measure.map_map (by fun_prop) hπm]
    have : ((fun q : Rd d × Rd d => q.2 + q.1) ∘ fun p : Rd d × Rd d => (p.1 - p.2, p.2)) =
        Prod.fst := by
      funext p; simp
    rw [this, Measure.map_fst_prod]; simp

end Refine

/-! ### Boxes, and a uniform part of `F ∗ F` -/

section ConvUnif

variable {d : ℕ}

lemma isClosed_box (c : Rd d) (H : Fin d → ℝ) : IsClosed (box c H) := by
  have : box c H = ⋂ i, {x : Rd d | |x i - c i| ≤ H i} := by ext x; simp [box]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma measurableSet_box (c : Rd d) (H : Fin d → ℝ) : MeasurableSet (box c H) :=
  (isClosed_box c H).measurableSet

lemma closedBall_subset_box (c : Rd d) (H : ℝ) : closedBall c H ⊆ box c (fun _ => H) := by
  intro x hx i
  have := PiLp.dist_apply_le x c i
  rw [Real.dist_eq] at this
  exact this.trans hx

lemma box_subset_closedBall (hd : 0 < d) (c : Rd d) {H : ℝ} (hH : 0 ≤ H) :
    box c (fun _ => H) ⊆ closedBall c (d * H) := by
  intro x hx
  rw [mem_closedBall, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ i, dist (x i) (c i) ^ 2 ≤ ∑ _i : Fin d, H ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = d * H ^ 2 := by simp
    _ ≤ (d * H) ^ 2 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [sq_nonneg H]

lemma vol_box_pos {c : Rd d} {H : ℝ} (hH : 0 < H) : 0 < volume (box c (fun _ => H)) :=
  (measure_closedBall_pos volume c hH).trans_le (measure_mono (closedBall_subset_box c H))

lemma vol_box_lt_top (hd : 0 < d) {c : Rd d} {H : ℝ} (hH : 0 ≤ H) :
    volume (box c (fun _ => H)) < ⊤ :=
  (measure_mono (box_subset_closedBall hd c hH)).trans_lt measure_closedBall_lt_top

lemma conv_lower {F : Measure (Rd d)} [IsProbabilityMeasure F] {A : Set (Rd d)}
    (hA : MeasurableSet A) {c : ENNReal} (hcF : c • volume.restrict A ≤ F) {Q' : Set (Rd d)}
    {ε : ℝ} (hε : ∀ y ∈ Q', ENNReal.ofReal ε ≤ volume {b | b ∈ A ∧ y - b ∈ A})
    {T : Set (Rd d)} (hT : MeasurableSet T) (hTQ : T ⊆ Q') :
    c * c * ENNReal.ofReal ε * volume T ≤ conv F T := by
  have hadd : Measurable (fun p : Rd d × Rd d => p.1 + p.2) := by fun_prop
  have hU : MeasurableSet ((fun p : Rd d × Rd d => p.1 + p.2) ⁻¹' T) := hadd hT
  rw [conv, Measure.map_apply hadd hT]
  have hle : (c • volume.restrict A).prod (c • volume.restrict A) ≤ F.prod F :=
    Measure.prod_mono hcF hcF
  refine le_trans ?_ (hle _)
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict, smul_apply,
    smul_apply, Measure.restrict_apply hU, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  set W : Set (Rd d × Rd d) := {p | p.1 ∈ A ∧ p.2 - p.1 ∈ A ∧ p.2 ∈ T}
  have hW : MeasurableSet W :=
    (hA.preimage measurable_fst).inter ((hA.preimage (by fun_prop)).inter (hT.preimage measurable_snd))
  have hpre : (fun p : Rd d × Rd d => p.1 + p.2) ⁻¹' T ∩ A ×ˢ A =
      (fun z : Rd d × Rd d => (z.1, z.1 + z.2)) ⁻¹' W := by
    ext ⟨a, b⟩; simp [W]; tauto
  rw [hpre, (measurePreserving_prod_add volume volume).measure_preimage hW.nullMeasurableSet,
    Measure.prod_apply_symm hW, mul_assoc]
  gcongr
  rw [← lintegral_indicator_const hT]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ T
  · rw [Set.indicator_of_mem hy]
    refine (hε y (hTQ hy)).trans (measure_mono fun b hb => ?_)
    exact ⟨hb.1, hb.2, hy⟩
  · rw [Set.indicator_of_notMem hy]; exact zero_le
lemma exists_lower_set (F : Measure (Rd d)) [IsFiniteMeasure F] (hac : ¬ F ⟂ₘ volume) :
    ∃ s : Set (Rd d), MeasurableSet s ∧ 0 < volume s ∧ ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧
      c • volume.restrict s ≤ F := by
  set f := F.rnDeriv volume
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hwd : volume.withDensity f ≠ 0 := by
    intro h0
    apply hac
    have := Measure.haveLebesgueDecomposition_add F volume
    rw [h0, add_zero] at this
    rw [this]
    exact Measure.mutuallySingular_singularPart _ _
  have hpos : volume {x | f x ≠ 0} ≠ 0 := by
    intro h
    apply hwd
    rw [withDensity_eq_zero_iff hf.aemeasurable]
    exact (measure_eq_zero_iff_ae_notMem.1 h).mono fun x hx => by simpa using hx
  have hU : {x | f x ≠ 0} ⊆ ⋃ k : ℕ, {x | ((k : ENNReal) + 1)⁻¹ ≤ f x} := by
    intro x hx
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    show ((k : ENNReal) + 1)⁻¹ ≤ f x
    refine le_trans ?_ hk.le
    exact ENNReal.inv_le_inv.2 le_self_add
  obtain ⟨k, hk⟩ : ∃ k : ℕ, volume {x | ((k : ENNReal) + 1)⁻¹ ≤ f x} ≠ 0 := by
    by_contra h
    push Not at h
    exact hpos (measure_mono_null hU (measure_iUnion_null h))
  refine ⟨_, measurableSet_le measurable_const hf, pos_iff_ne_zero.2 hk, ((k : ENNReal) + 1)⁻¹,
    by simp, by simp, ?_⟩
  refine Measure.le_iff.2 fun t ht => ?_
  rw [smul_apply, Measure.restrict_apply ht, smul_eq_mul]
  calc ((k : ENNReal) + 1)⁻¹ * volume (t ∩ {x | ((k : ENNReal) + 1)⁻¹ ≤ f x})
      = ∫⁻ _ in t ∩ {x | ((k : ENNReal) + 1)⁻¹ ≤ f x}, ((k : ENNReal) + 1)⁻¹ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in t ∩ {x | ((k : ENNReal) + 1)⁻¹ ≤ f x}, f x :=
        setLIntegral_mono hf fun x hx => hx.2
    _ ≤ ∫⁻ x in t, f x := lintegral_mono_set Set.inter_subset_left
    _ = volume.withDensity f t := (withDensity_apply _ ht).symm
    _ ≤ F t := by
        conv_rhs => rw [Measure.haveLebesgueDecomposition_add F volume]
        exact le_add_self
lemma vol_closedBall_eq (x : Rd d) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = r ^ d * volume.real (ball (0 : Rd d) 1) := by
  rw [measureReal_def, Measure.addHaar_closedBall volume x hr, finrank_euclideanSpace,
    Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

lemma density_lower (s : Set (Rd d)) (hs : MeasurableSet s) (hpos : 0 < volume s) :
    ∃ A ⊆ s, MeasurableSet A ∧ volume A < ⊤ ∧ ∃ y0 : Rd d, ∃ r > 0, ∃ ε : ℝ, 0 < ε ∧
      ∀ y, dist y y0 ≤ r → ENNReal.ofReal ε ≤ volume {b | b ∈ A ∧ y - b ∈ A} := by
  have hne : volume.restrict s ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hpos.ne'
  have := ae_neBot.2 hne
  obtain ⟨a, ha⟩ := (Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Rd d)) s).exists
  set η : ℝ := (3 / 4 : ℝ) ^ d / 4 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by
    have : (3 / 4 : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [hη]; linarith
  have hlt : ENNReal.ofReal (1 - η) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  obtain ⟨r, hr1, hr0⟩ := ((ha.eventually (Ioi_mem_nhds hlt)).and self_mem_nhdsWithin).exists
  have hr0 : 0 < r := hr0
  have hr1 : ENNReal.ofReal (1 - η) < volume (s ∩ closedBall a r) / volume (closedBall a r) := hr1
  set B := closedBall a r
  set A := s ∩ B
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hAm : MeasurableSet A := hs.inter hBm
  have hBfin : volume B < ⊤ := measure_closedBall_lt_top
  have hBpos : 0 < volume B := measure_closedBall_pos volume a hr0
  have hAfin : volume A < ⊤ := (measure_mono Set.inter_subset_right).trans_lt hBfin
  have hB0 : 0 < volume.real B := ENNReal.toReal_pos hBpos.ne' hBfin.ne
  -- `vol(A) > (1 - η) vol(B)`
  have hA : (1 - η) * volume.real B < volume.real A := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hBpos.ne') (Or.inl hBfin.ne)] at hr1
    have := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin.ne)
      hAfin.ne).2 hr1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hBA : volume.real (B \ A) < η * volume.real B := by
    rw [measureReal_sdiff Set.inter_subset_right hAm hBfin.ne]
    linarith
  refine ⟨A, Set.inter_subset_left, hAm, hAfin, (2 : ℝ) • a, r / 2, by positivity,
    2 * η * volume.real B, by positivity, fun y hy => ?_⟩
  set T := {b | b ∈ A ∧ y - b ∈ A}
  have hTm : MeasurableSet T := hAm.inter (hAm.preimage (by fun_prop))
  have hTfin : volume T < ⊤ := (measure_mono (show T ⊆ A from fun b hb => hb.1)).trans_lt hAfin
  set C := closedBall ((1 / 2 : ℝ) • y) (3 * r / 4)
  have hya : ‖(1 / 2 : ℝ) • y - a‖ ≤ r / 4 := by
    have : (1 / 2 : ℝ) • y - a = (1 / 2 : ℝ) • (y - (2 : ℝ) • a) := by
      rw [smul_sub, smul_smul]; norm_num
    rw [this, norm_smul, ← dist_eq_norm]
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this]; linarith
  set P := (fun b => y - b) ⁻¹' (B \ A)
  have hCsub : C ⊆ T ∪ (B \ A) ∪ P := by
    intro b hb
    rw [mem_closedBall, dist_eq_norm] at hb
    have hb1 : b ∈ B := by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖b - a‖ = ‖(b - (1 / 2 : ℝ) • y) + ((1 / 2 : ℝ) • y - a)‖ := by congr 1; abel
        _ ≤ ‖b - (1 / 2 : ℝ) • y‖ + ‖(1 / 2 : ℝ) • y - a‖ := norm_add_le _ _
        _ ≤ r := by linarith
    have hb2 : y - b ∈ B := by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖y - b - a‖ = ‖((1 / 2 : ℝ) • y - b) + ((1 / 2 : ℝ) • y - a)‖ := by
            congr 1; module
        _ ≤ ‖(1 / 2 : ℝ) • y - b‖ + ‖(1 / 2 : ℝ) • y - a‖ := norm_add_le _ _
        _ ≤ r := by rw [norm_sub_rev] at hb; linarith
    by_cases h1 : b ∈ A
    · by_cases h2 : y - b ∈ A
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr ⟨hb2, h2⟩
    · exact Or.inl (Or.inr ⟨hb1, h1⟩)
  have hPm : volume.real P = volume.real (B \ A) := by
    simp only [measureReal_def, P]
    rw [(Measure.measurePreserving_sub_left volume y).measure_preimage
      (hBm.diff hAm).nullMeasurableSet]
  have hPfin : volume P < ⊤ := by
    simp only [P]
    rw [(Measure.measurePreserving_sub_left volume y).measure_preimage
      (hBm.diff hAm).nullMeasurableSet]
    exact (measure_mono Set.sdiff_subset).trans_lt hBfin
  have hBAfin : volume (B \ A) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hBfin
  have hC : volume.real C ≤ volume.real T + volume.real (B \ A) + volume.real P := by
    have h1 : volume C ≤ volume T + volume (B \ A) + volume P :=
      (measure_mono hCsub).trans ((measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _))
    have h2 := ENNReal.toReal_mono (by finiteness) h1
    rwa [ENNReal.toReal_add (by finiteness) hPfin.ne, ENNReal.toReal_add hTfin.ne hBAfin.ne] at h2
  have hCvol : volume.real C = (3 / 4 : ℝ) ^ d * volume.real B := by
    rw [vol_closedBall_eq _ (by positivity), vol_closedBall_eq _ hr0.le]
    rw [show 3 * r / 4 = (3 / 4) * r by ring, mul_pow]; ring
  have hT : 2 * η * volume.real B ≤ volume.real T := by
    have : (3 / 4 : ℝ) ^ d = 4 * η := by rw [hη]; ring
    rw [this] at hCvol
    linarith
  calc ENNReal.ofReal (2 * η * volume.real B) ≤ ENNReal.ofReal (volume.real T) :=
        ENNReal.ofReal_le_ofReal hT
    _ = volume T := ENNReal.ofReal_toReal hTfin.ne

theorem conv_ge_unif (hd : 0 < d) (F : Measure (Rd d)) [IsProbabilityMeasure F]
    (hac : ¬ F ⟂ₘ volume) :
    ∃ (c0 : Rd d) (H : ℝ), 0 < H ∧ ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      ENNReal.ofReal q • unifSet (box c0 (fun _ => H)) ≤ conv F := by
  obtain ⟨s, hs, hspos, c, hc0, hctop, hcF⟩ := exists_lower_set F hac
  obtain ⟨A, hAs, hAm, -, y0, r, hr, ε, hε, hεy⟩ := density_lower s hs hspos
  have hcA : c • volume.restrict A ≤ F := by
    refine le_trans (Measure.le_iff.2 fun t ht => ?_) hcF
    rw [smul_apply, smul_apply, Measure.restrict_apply ht, Measure.restrict_apply ht]
    gcongr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set H : ℝ := r / d with hH
  have hH0 : 0 < H := by positivity
  set Q' := box y0 (fun _ => H)
  have hQ'ball : Q' ⊆ closedBall y0 r := by
    refine (box_subset_closedBall hd y0 hH0.le).trans (closedBall_subset_closedBall ?_)
    rw [hH]; field_simp; rfl
  have hεQ : ∀ y ∈ Q', ENNReal.ofReal ε ≤ volume {b | b ∈ A ∧ y - b ∈ A} :=
    fun y hy => hεy y (hQ'ball hy)
  set V := volume Q'
  have hV0 : V ≠ 0 := (vol_box_pos hH0).ne'
  have hVt : V ≠ ⊤ := (vol_box_lt_top hd hH0.le).ne
  set K := c * c * ENNReal.ofReal ε * V with hK
  have hKt : K ≠ ⊤ := by finiteness
  have hK0 : K ≠ 0 := by
    simp only [hK, ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨hc0.ne', hc0.ne'⟩, by simpa using hε⟩, hV0⟩
  have key : ENNReal.ofReal K.toReal • unifSet Q' ≤ conv F := by
    refine Measure.le_iff.2 fun T hT => ?_
    rw [smul_apply, unifSet, smul_apply, Measure.restrict_apply hT, smul_eq_mul, smul_eq_mul,
      ENNReal.ofReal_toReal hKt]
    calc K * (V⁻¹ * volume (T ∩ Q')) = c * c * ENNReal.ofReal ε * volume (T ∩ Q') := by
          rw [hK, mul_assoc _ V, ← mul_assoc V, ENNReal.mul_inv_cancel hV0 hVt, one_mul]
      _ ≤ conv F (T ∩ Q') := conv_lower hAm hcA hεQ (hT.inter (measurableSet_box _ _))
          Set.inter_subset_right
      _ ≤ conv F T := measure_mono Set.inter_subset_left
  refine ⟨y0, H, hH0, K.toReal, ENNReal.toReal_pos hK0 hKt, ?_, key⟩
  have h1 := key Q'
  rw [smul_apply, unifSet, smul_apply, Measure.restrict_apply (measurableSet_box _ _),
    Set.inter_self, smul_eq_mul, smul_eq_mul, ENNReal.inv_mul_cancel hV0 hVt, mul_one] at h1
  exact ENNReal.ofReal_le_one.1 (h1.trans prob_le_one)

end ConvUnif

/-! ### Theorem `as:thm:general` -/

section General

variable {d : ℕ}

lemma box_mono {c : Rd d} {H H' : Fin d → ℝ} (h : ∀ i, H i ≤ H' i) : box c H ⊆ box c H' :=
  fun _ hx i => (hx i).trans (h i)

lemma integrable_of_null_compl {ν : Measure (Rd d)} [IsFiniteMeasure ν] {K : Set (Rd d)} {M : ℝ}
    (hK : ν Kᶜ = 0) (hM : ∀ x ∈ K, ‖x‖ ≤ M) : Integrable (fun x => x) ν :=
  Integrable.of_bound aestronglyMeasurable_id M (by
    rw [ae_iff]
    exact measure_mono_null (fun x (hx : x ∈ {a | ¬‖a‖ ≤ M}) => show x ∈ Kᶜ from
      fun hxK => hx (hM x hxK)) hK)

lemma norm_sub_mean_le {F : Measure (Rd d)} [IsProbabilityMeasure F] {K : Set (Rd d)}
    (hK : F Kᶜ = 0) {R : ℝ} (hR : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R)
    (hint : Integrable (fun x => x) F) {x : Rd d} (hx : x ∈ K) : ‖x - ∫ y, y ∂F‖ ≤ R := by
  have h1 : x - ∫ y, y ∂F = ∫ y, (x - y) ∂F := by
    rw [integral_sub (integrable_const x) hint, integral_const]; simp
  rw [h1]
  have := norm_integral_le_of_norm_le_const (μ := F) (f := fun y => x - y) (C := R) (by
    rw [ae_iff]
    refine measure_mono_null (fun y (hy : y ∈ {a | ¬‖x - a‖ ≤ R}) => show y ∈ Kᶜ from
      fun hyK => hy (by rw [← dist_eq_norm]; exact hR x hx y hyK)) hK)
  simpa using this

lemma floor_div_ge (hd : 0 < d) {x : ℝ} (_hx : 0 ≤ x) : x / d - 2 ≤ ((⌊x⌋₊ / d : ℕ) : ℝ) := by
  set m := ⌊x⌋₊
  have h1 : x < m + 1 := Nat.lt_floor_add_one x
  have h2 : m < d * (m / d) + d := by
    have := Nat.div_add_mod m d; have := Nat.mod_lt m hd; omega
  have h2' : (m : ℝ) < d * ((m / d : ℕ) : ℝ) + d := by exact_mod_cast h2
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have : x / d ≤ ((m / d : ℕ) : ℝ) + 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **Theorem `as:thm:general`**, given Theorem `as:thm:window` (`H_thm_window`). Let `F` be a
probability measure on `ℝ^d`, `d ≥ 1`, with bounded support, mean `μ`, and a nonzero absolutely
continuous part (`F` is not singular with respect to Lebesgue measure). Then there are `N` and
`κ > 0` such that for every `n ≥ N` the aggregation set `𝒜_n(F)` contains every probability
measure with mean `nμ` that is supported in `nμ + [-κn, κn]^d`. -/
theorem thm_general (hd : 0 < d) (hW : H_thm_window d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, N ≤ n → ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
      ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F →
      ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 → ν ∈ AggSet n F := by
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
  obtain ⟨c0, H, hH, q, hq, hq1, hunif⟩ := conv_ge_unif hd F hac
  set cc := cdConst d
  have hcc : 0 ≤ cc := by simp only [cc, cdConst]; split_ifs <;> positivity
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set κ := q * H / (8 * d) with hκ
  set st := q * H / (8 * d) + H + R + 2 * cc * R with hst
  set X := 6 * d / q + st * (4 * d / (q * H)) with hX
  refine ⟨2 * ⌈X⌉₊ + 2, κ, by positivity, fun n hn ν hν hmean hsupp => ?_⟩
  set n' := n / 2 with hn'def
  have hn'X : X ≤ n' := by
    have h1 : ⌈X⌉₊ ≤ n' := by omega
    exact (Nat.le_ceil X).trans (by exact_mod_cast h1)
  have hn2 : n = 2 * n' ∨ n = 2 * n' + 1 := by omega
  have hnle : (n : ℝ) ≤ 2 * n' + 1 := by rcases hn2 with h | h <;> rw [h] <;> push_cast <;> linarith
  set m' := ⌊q * (n' : ℝ)⌋₊ / d with hm'
  have hm'r : q * n' / d - 2 ≤ (m' : ℝ) := floor_div_ge hd (by positivity)
  have hXst : st * (4 * d / (q * H)) ≤ n' := le_trans (by
    rw [hX]; have : 0 ≤ 6 * (d : ℝ) / q := by positivity
    linarith) hn'X
  have hX6 : 6 * (d : ℝ) / q ≤ n' := le_trans (by
    rw [hX]; have : 0 ≤ st * (4 * (d : ℝ) / (q * H)) := by positivity
    linarith) hn'X
  have hm'4 : 4 ≤ m' := by
    have : (6 : ℝ) ≤ q * n' / d := by
      rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ hq] at hX6; linarith
    have : (4 : ℝ) ≤ m' := by linarith
    exact_mod_cast this
  have hst' : st ≤ q * H * n' / (4 * d) := by
    rw [le_div_iff₀ (by positivity)]
    have := hXst
    rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
    linarith
  have hρ : κ * n + R ≤ m' * H / 2 - cc * (2 * R) := by
    have h1 : κ * n ≤ κ * (2 * n' + 1) := mul_le_mul_of_nonneg_left hnle (by positivity)
    have h2 : (q * n' / d - 2) * H / 2 ≤ m' * H / 2 := by
      have := mul_le_mul_of_nonneg_right hm'r hH.le; linarith
    have h3 : κ * (2 * n' + 1) = q * H * n' / (4 * d) + q * H / (8 * d) := by
      rw [hκ]; field_simp; ring
    have h4 : (q * n' / d - 2) * H / 2 = 2 * (q * H * n' / (4 * d)) - H := by
      field_simp; ring
    rw [hst] at hst'
    nlinarith
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

/-- The last statement of Theorem `as:thm:general`: `F` is `n`-completely mixable for every
`n ≥ N`. -/
theorem completelyMixable_of_dirac_mem {n : ℕ} {F : Measure (Rd d)} {s : Rd d}
    (h : Measure.dirac s ∈ AggSet n F) : CompletelyMixable n F := by
  obtain ⟨P, hP, hm, hs⟩ := h
  refine ⟨P, ⟨hP, ⟨s, ?_⟩, hm⟩⟩
  have hmeas : Measurable (fun x : Fin n → Rd d => ∑ j, x j) := by fun_prop
  have : ∀ᵐ y ∂(P.map (fun x : Fin n → Rd d => ∑ j, x j)), y = s := by
    rw [hs, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  exact ae_of_ae_map hmeas.aemeasurable this

theorem thm_general_mix (hd : 0 < d) (hW : H_thm_window d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) : ∃ N : ℕ, ∀ n, N ≤ n → CompletelyMixable n F := by
  obtain ⟨N, κ, hκ, hN⟩ := thm_general hd hW F hb hac
  refine ⟨N, fun n hn => completelyMixable_of_dirac_mem (hN n hn (Measure.dirac ((n : ℝ) • ∫ x, x ∂F)) inferInstance ?_ ?_)⟩
  · rw [integral_dirac]
  · rw [Measure.dirac_apply' _ (measurableSet_box _ _).compl, Set.indicator_of_notMem]
    simp only [Set.mem_compl_iff, not_not]
    intro i
    simp only [sub_self, abs_zero]
    positivity

end General

/-! ### Corollary `as:cor:order` -/

section Order

variable {d : ℕ}

/-- The convex order `ν₁ ≤_cx ν₂`: `∫ f dν₁ ≤ ∫ f dν₂` for every convex `f` integrable under
both. -/
def CxLe (ν₁ ν₂ : Measure (Rd d)) : Prop :=
  ∀ f : Rd d → ℝ, ConvexOn ℝ Set.univ f → Integrable f ν₁ → Integrable f ν₂ →
    ∫ x, f x ∂ν₁ ≤ ∫ x, f x ∂ν₂

/-- Every element of `𝒜_n(F)` is a probability measure with integrable identity and mean
`n m_F`. -/
lemma aggSet_mean {n : ℕ} {F : Measure (Rd d)} (hint : Integrable (fun x => x) F)
    {ν : Measure (Rd d)} (h : ν ∈ AggSet n F) :
    IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧
      ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F := by
  obtain ⟨P, hP, hm, rfl⟩ := h
  have hmeas : Measurable (fun x : Fin n → Rd d => ∑ j, x j) := by fun_prop
  have hcoord : ∀ j : Fin n, Integrable (fun x : Fin n → Rd d => x j) P := fun j => by
    have : Integrable (fun y : Rd d => y) (P.map (fun x => x j)) := by rw [hm j]; exact hint
    exact (integrable_map_measure (g := fun y : Rd d => y) (by fun_prop)
      (by fun_prop : Measurable (fun x : Fin n → Rd d => x j)).aemeasurable).1 this
  have hsum : Integrable (fun x : Fin n → Rd d => ∑ j, x j) P :=
    integrable_finsetSum _ fun j _ => hcoord j
  refine ⟨inferInstance, (integrable_map_measure (by fun_prop) hmeas.aemeasurable).2 hsum, ?_⟩
  rw [integral_map (f := fun x : Rd d => x) hmeas.aemeasurable (by fun_prop),
    integral_finsetSum _ fun j _ => hcoord j]
  have : ∀ j : Fin n, ∫ x, x j ∂P = ∫ y, y ∂F := fun j => by
    rw [← hm j, integral_map (f := fun y : Rd d => y)
      (by fun_prop : Measurable (fun x : Fin n → Rd d => x j)).aemeasurable (by fun_prop)]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℝ n _).symm

/-- The point mass at the mean is below every probability measure with that mean in convex
order (Jensen's inequality). -/
lemma dirac_cxLe {ν : Measure (Rd d)} [IsProbabilityMeasure ν]
    (hint : Integrable (fun x => x) ν) : CxLe (Measure.dirac (∫ x, x ∂ν)) ν := by
  intro f hf _ hfi
  rw [integral_dirac]
  have hc : ContinuousOn f Set.univ := by
    have := hf.continuousOn_interior; rwa [interior_univ] at this
  exact hf.map_integral_le hc isClosed_univ (Filter.Eventually.of_forall fun _ => trivial) hint hfi

/-- **Corollary `as:cor:order`**, given Theorem `as:thm:window`. For `F` as in Theorem
`as:thm:general` there are `N` and `κ > 0` (those of the theorem) such that for `n ≥ N` the
aggregation set `𝒜_n(F)` has a smallest element in convex order, the point mass at `nμ`, and a
probability measure supported in `nμ + [-κn, κn]^d` belongs to `𝒜_n(F)` if and only if its mean
is `nμ`. -/
theorem cor_order (hd : 0 < d) (hW : H_thm_window d) (F : Measure (Rd d))
    [IsProbabilityMeasure F] (hb : ∃ S : Set (Rd d), Bornology.IsBounded S ∧ F Sᶜ = 0)
    (hac : ¬ F ⟂ₘ volume) :
    ∃ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, N ≤ n →
      (Measure.dirac ((n : ℝ) • ∫ x, x ∂F) ∈ AggSet n F ∧
        ∀ ν ∈ AggSet n F, CxLe (Measure.dirac ((n : ℝ) • ∫ x, x ∂F)) ν) ∧
      ∀ ν : Measure (Rd d), IsProbabilityMeasure ν →
        ν (box ((n : ℝ) • ∫ x, x ∂F) (fun _ => κ * n))ᶜ = 0 →
        (ν ∈ AggSet n F ↔ ∫ x, x ∂ν = (n : ℝ) • ∫ x, x ∂F) := by
  obtain ⟨S, hSb, hS⟩ := hb
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ S, ‖x‖ ≤ M := hSb.exists_norm_le
  have hint : Integrable (fun x => x) F := integrable_of_null_compl hS hM
  obtain ⟨N, κ, hκ, hN⟩ := thm_general hd hW F ⟨S, hSb, hS⟩ hac
  refine ⟨N, κ, hκ, fun n hn => ⟨⟨?_, fun ν hν => ?_⟩, fun ν hνp hsupp => ⟨fun h =>
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

end Order

/-! ### Corollary `as:cor:body` -/

section Body

open Real

variable {d : ℕ}

/-- `ω_d`, the volume of the unit ball of `ℝ^d`. -/
def omega (d : ℕ) : ℝ := volume.real (closedBall (0 : Rd d) 1)
/-- `q_d = 2^d / (d^{3d/2} ω_d)`. -/
def qd (d : ℕ) : ℝ := 2 ^ d / (Real.sqrt d ^ (3 * d) * omega d)
/-- `N*_d = ⌈d ⌈8 d^{5/2}⌉ / q_d⌉`. -/
def Nstar (d : ℕ) : ℕ := ⌈(d * ⌈8 * Real.sqrt d ^ 5⌉₊ : ℝ) / qd d⌉₊

lemma omega_eq (d : ℕ) [NeZero d] : omega d = √π ^ d / Gamma (d / 2 + 1) := by
  rw [omega, measureReal_def, EuclideanSpace.volume_closedBall (Fin d)]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal]
  exact div_nonneg (by positivity) (Gamma_nonneg_of_nonneg (by positivity))

lemma omega_two : omega 2 = π := by
  rw [omega_eq]
  norm_num [Gamma_two]
  exact Real.sq_sqrt pi_pos.le

lemma omega_three : omega 3 = 4 * π / 3 := by
  rw [omega_eq]
  have h1 : ((3 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 := by norm_num
  rw [h1, Gamma_add_one (by norm_num), Gamma_add_one (by norm_num), Gamma_one_half_eq]
  have hp : 0 < √π := Real.sqrt_pos.2 pi_pos
  have : √π ^ 2 = π := Real.sq_sqrt pi_pos.le
  field_simp
  rw [this]; ring

/-- `N*₂ = 579` (the paper's `\\AsNtwo`). -/
theorem Nstar_two : Nstar 2 = 579 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1.4142 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hq : qd 2 = 1 / (2 * π) := by
    rw [qd, omega_two]
    have : Real.sqrt ((2 : ℕ) : ℝ) ^ (3 * 2) = 8 := by
      rw [show (3 * 2 : ℕ) = 2 * 3 by rfl, pow_mul, Nat.cast_ofNat, h2]; norm_num
    rw [this]; field_simp; norm_num
  have hC : ⌈8 * Real.sqrt ((2 : ℕ) : ℝ) ^ 5⌉₊ = 46 := by
    rw [Nat.ceil_eq_iff (by norm_num), Nat.cast_ofNat,
      show Real.sqrt 2 ^ 5 = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 by ring, h2]
    constructor <;> norm_num <;> linarith
  rw [Nstar, hC, hq, Nat.ceil_eq_iff (by norm_num)]
  have := pi_gt_d6
  have := pi_lt_d6
  constructor <;> norm_num <;> field_simp <;> nlinarith

/-- `N*₃ = 27548` (the paper's `\\AsNthree`). -/
theorem Nstar_three : Nstar 3 = 27548 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : (1.7320508 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 3 < 1.7320509 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hq : qd 3 = 2 / (27 * Real.sqrt 3 * π) := by
    rw [qd, omega_three]
    have : Real.sqrt ((3 : ℕ) : ℝ) ^ (3 * 3) = 81 * Real.sqrt 3 := by
      rw [Nat.cast_ofNat, show Real.sqrt 3 ^ (3 * 3) = (Real.sqrt 3 ^ 2) ^ 4 * Real.sqrt 3 by ring,
        h3]; norm_num
    rw [this]
    have : 0 < Real.sqrt 3 := by positivity
    field_simp; norm_num
  have hC : ⌈8 * Real.sqrt ((3 : ℕ) : ℝ) ^ 5⌉₊ = 125 := by
    rw [Nat.ceil_eq_iff (by norm_num), Nat.cast_ofNat,
      show Real.sqrt 3 ^ 5 = (Real.sqrt 3 ^ 2) ^ 2 * Real.sqrt 3 by ring, h3]
    constructor <;> norm_num <;> linarith
  rw [Nstar, hC, hq, Nat.ceil_eq_iff (by norm_num)]
  have := pi_gt_d6
  have := pi_lt_d6
  have h0 : 0 < Real.sqrt 3 := by positivity
  have hprod1 : (1.7320508 : ℝ) * 3.141592 < Real.sqrt 3 * π := by nlinarith
  have hprod2 : Real.sqrt 3 * π < 1.7320509 * 3.141593 := by nlinarith
  constructor <;> norm_num <;> field_simp <;> nlinarith

lemma vol_cube (d : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    volume (box (0 : Rd d) (fun _ => h)) = ENNReal.ofReal ((2 * h) ^ d) := by
  have hpre : box (0 : Rd d) (fun _ => h) =
      (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (Set.univ.pi fun _ => Set.Icc (-h) h) := by
    ext x
    simp only [box, abs_le, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]; simp
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by linarith)]
  ring_nf

lemma cube_subset_ball (hd : 0 < d) :
    box (0 : Rd d) (fun _ => (Real.sqrt d)⁻¹) ⊆ closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_one.mpr ?_
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, ((Real.sqrt d)⁻¹) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs]
        have := hx i
        simp only [PiLp.zero_apply, sub_zero] at this
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, inv_pow,
          Real.sq_sqrt (by positivity), nsmul_eq_mul]
        field_simp

lemma qd_identity (hd : 0 < d) :
    qd d * (d : ℝ) ^ d * omega d = (2 / Real.sqrt d) ^ d := by
  have hom : 0 < omega d := ENNReal.toReal_pos
    (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have h3 : Real.sqrt d ^ (3 * d) = (d : ℝ) ^ d * Real.sqrt d ^ d := by
    rw [show 3 * d = 2 * d + d by ring, pow_add, pow_mul, Real.sq_sqrt (by positivity)]
  rw [qd, h3, div_pow]
  field_simp

/-- **Corollary `as:cor:body`**, given John's theorem (`Large.JohnThm`) and Theorem
`as:thm:window` (`H_thm_window`): for `d ≥ 2` the uniform distribution on every convex body in
`ℝ^d` is `n`-completely mixable for every `n ≥ N*_d`, where `q_d = 2^d / (d^{3d/2} ω_d)` and
`N*_d = ⌈d ⌈8 d^{5/2}⌉ / q_d⌉`. -/
theorem cor_body (hd : 2 ≤ d) (hJ : Large.JohnThm (Rd d)) (hW : H_thm_window d) :
    ∀ K : Set (Rd d), IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∀ n, Nstar d ≤ n → CompletelyMixable n (unifSet K) := by
  intro K hKc hKconv hKi n hn
  have hd0 : 0 < d := by omega
  obtain ⟨L, t, hB, hD⟩ := hJ K hKc hKconv hKi
  rw [finrank_euclideanSpace, Fintype.card_fin] at hD
  set K' := Large.affE L t '' K
  suffices h : CompletelyMixable n (unifSet K') by
    obtain ⟨P, hP⟩ := h
    exact ⟨_, by simpa [K', Large.unifSet_map_affE] using
      Large.isCompleteMix_affE hP L.symm (-L.symm t)⟩
  have hK'c : IsCompact K' :=
    hKc.image (show Continuous (Large.affE L t) from L.continuous.add continuous_const)
  have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by positivity)
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 hdR
  set Q := box (0 : Rd d) (fun _ => (Real.sqrt d)⁻¹)
  have hQm : MeasurableSet Q := measurableSet_box _ _
  have hQK : Q ⊆ K' := (cube_subset_ball hd0).trans hB
  have hvB : 0 < volume (closedBall (0 : Rd d) 1) := measure_closedBall_pos volume 0 one_pos
  have hvK0 : volume K' ≠ 0 := (hvB.trans_le (measure_mono hB)).ne'
  have hvKt : volume K' ≠ ⊤ := hK'c.measure_lt_top.ne
  have hvQ : volume Q = ENNReal.ofReal ((2 * (Real.sqrt d)⁻¹) ^ d) := vol_cube d (by positivity)
  have hvQ0 : volume Q ≠ 0 := by
    rw [hvQ]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hvQt : volume Q ≠ ⊤ := by rw [hvQ]; exact ENNReal.ofReal_ne_top
  -- `|K'| ≤ d^d ω_d`
  have hvK : volume.real K' ≤ (d : ℝ) ^ d * omega d := by
    have h1 : volume.real K' ≤ volume.real (closedBall (0 : Rd d) d) :=
      measureReal_mono hD measure_closedBall_lt_top.ne
    rw [Measure.addHaar_real_closedBall' volume 0 (by positivity), finrank_euclideanSpace,
      Fintype.card_fin] at h1
    exact h1
  have hvKr : 0 < volume.real K' := ENNReal.toReal_pos hvK0 hvKt
  have hvQr : volume.real Q = (2 / Real.sqrt d) ^ d := by
    rw [measureReal_def, hvQ, ENNReal.toReal_ofReal (by positivity), div_eq_mul_inv]
  have hqle : qd d * volume.real K' ≤ volume.real Q := by
    rw [hvQr, ← qd_identity hd0, mul_assoc]
    have hq0 : 0 ≤ qd d := by
      have hom : 0 < omega d := ENNReal.toReal_pos hvB.ne' measure_closedBall_lt_top.ne
      unfold qd; positivity
    exact mul_le_mul_of_nonneg_left hvK hq0
  have hq : 0 < qd d := by
    have hom : 0 < omega d := ENNReal.toReal_pos hvB.ne' measure_closedBall_lt_top.ne
    unfold qd; positivity
  have hQK' : volume.real Q ≤ volume.real K' := measureReal_mono hQK hvKt
  have hq1 : qd d ≤ 1 := by
    have : qd d * volume.real K' ≤ 1 * volume.real K' := by linarith
    exact le_of_mul_le_mul_right this hvKr
  -- `U(K') ≥ q_d U(Q)`
  have hle : ENNReal.ofReal (qd d) • unifSet Q ≤ unifSet K' := by
    have hq' : ENNReal.ofReal (qd d) ≤ volume Q / volume K' := by
      rw [← ENNReal.ofReal_toReal hvQt, ← ENNReal.ofReal_toReal hvKt,
        ← ENNReal.ofReal_div_of_pos (show 0 < (volume K').toReal from hvKr)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ (show 0 < (volume K').toReal from hvKr)]; exact hqle
    refine Measure.le_iff.2 fun T hT => ?_
    rw [smul_apply, unifSet, unifSet, smul_apply, smul_apply, Measure.restrict_apply hT,
      Measure.restrict_apply hT, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    calc ENNReal.ofReal (qd d) * ((volume Q)⁻¹ * volume (T ∩ Q))
        ≤ volume Q / volume K' * ((volume Q)⁻¹ * volume (T ∩ K')) := by
          gcongr
      _ = (volume K')⁻¹ * volume (T ∩ K') := by
          rw [ENNReal.div_eq_inv_mul, mul_assoc, ← mul_assoc (volume Q),
            ENNReal.mul_inv_cancel hvQ0 hvQt, one_mul]
  have hprob : IsProbabilityMeasure (unifSet K') := by
    constructor
    rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel hvK0 hvKt]
  have hsupp : SuppDiam (unifSet K') (2 * d) := by
    refine ⟨K', ?_, fun x hx y hy => ?_⟩
    · rw [unifSet, smul_apply, Measure.restrict_apply hK'm.compl, Set.compl_inter_self,
        measure_empty, smul_zero]
    · have h1 := hD hx; have h2 := hD hy
      rw [mem_closedBall, dist_zero_right] at h1 h2
      calc dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
        _ ≤ 2 * d := by linarith
  -- the counting
  set C := ⌈8 * Real.sqrt d ^ 5⌉₊
  have hC : 8 * Real.sqrt d ^ 5 ≤ C := Nat.le_ceil _
  have hdCm : d * C ≤ ⌊qd d * n⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((d * C : ℕ) : ℝ) / qd d ≤ n := by
      have := (Nat.ceil_le.1 hn)
      simpa using this
    rw [div_le_iff₀ hq] at h1
    linarith
  have hm' : C ≤ ⌊qd d * n⌋₊ / d := by
    rw [Nat.le_div_iff_mul_le hd0, mul_comm]; exact hdCm
  have hm'r : (C : ℝ) ≤ ((⌊qd d * n⌋₊ / d : ℕ) : ℝ) := by exact_mod_cast hm'
  have hs5 : 1 ≤ Real.sqrt d ^ 5 := one_le_pow₀ hs1
  have hm'4 : 4 ≤ ⌊qd d * n⌋₊ / d := by
    have : (4 : ℝ) ≤ ((⌊qd d * n⌋₊ / d : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hcd : cdConst d = 2 * d := by simp [cdConst, show d ≠ 1 by omega]
  have hρ : 0 ≤ ((⌊qd d * n⌋₊ / d : ℕ) : ℝ) * (Real.sqrt d)⁻¹ / 2 - cdConst d * (2 * d) := by
    rw [hcd]
    have h4 : Real.sqrt d ^ 5 = (d : ℝ) ^ 2 * Real.sqrt d := by
      rw [show Real.sqrt d ^ 5 = (Real.sqrt d ^ 2) ^ 2 * Real.sqrt d by ring,
        Real.sq_sqrt (by positivity)]
    have : 8 * (d : ℝ) ^ 2 * Real.sqrt d ≤ ((⌊qd d * n⌋₊ / d : ℕ) : ℝ) := by
      calc 8 * (d : ℝ) ^ 2 * Real.sqrt d = 8 * Real.sqrt d ^ 5 := by rw [h4]; ring
        _ ≤ (C : ℝ) := hC
        _ ≤ _ := hm'r
    rw [sub_nonneg, div_eq_mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by norm_num), ← div_eq_mul_inv,
      le_div_iff₀ hs]
    nlinarith
  refine completelyMixable_of_dirac_mem (s := (n : ℝ) • ∫ x, x ∂(unifSet K'))
    (hW (unifSet K') (2 * d) 0 (fun _ => (Real.sqrt d)⁻¹) (qd d) n hsupp
      (fun _ => inv_pos.2 hs) hq hq1 hle hm'4 (fun _ => hρ) _ inferInstance
      (by rw [integral_dirac]) ?_)
  rw [Measure.dirac_apply' _ (measurableSet_box _ _).compl, Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, not_not]
  intro i
  simp only [sub_self, abs_zero]
  exact hρ

end Body

end Mixes.AsymGeneral
