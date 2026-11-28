import Mixes.PolyB
import Mixes.Proj

/-!
# The Prékopa–Leindler and Brunn–Minkowski inequalities

Mathlib has neither inequality. This file proves them and discharges the two cited hypotheses
`Mixes.PolyB.PLHyp` and `Mixes.Proj.BrunnSections m` of the project.

* One dimension: `bm1` (Brunn–Minkowski `|C| ≥ a|A| + b|B|` for nonempty measurable `A, B` and any
  `C ⊇ aA + bB`, via compact sets and inner regularity), `pl1` (Prékopa–Leindler on `ℝ` for
  lower Lebesgue integrals: layer cake, normalisation `sup f = sup g = 1`, truncation).
* `PLProp μ`: the Prékopa–Leindler property of a measure; it passes to products
  (`plProp_prod`, Fubini–Tonelli), along measure-preserving maps compatible with convex
  combinations (`plProp_of_equiv`), hence to `X^n` (`plProp_pi`) and to `ℂ` (`plProp_complex`).
* `prekopa_leindler` (on `Fin n → ℝ`), `prekopa_leindler_complex` (on `Fin m → ℂ`).
* `bm_mul_of_plProp`: multiplicative Brunn–Minkowski `μ(C) ≥ μ(A)^(1-t) μ(B)^t`;
  `brunn_minkowski`: the additive form `|C|^(1/m) ≥ (1-t)|A|^(1/m) + t|B|^(1/m)` in `ℝ^m`, `m ≥ 1`.
* (A) `cp_anti`, `plHyp : Mixes.PolyB.PLHyp`.
* (B) `brunnSections : ∀ m, Mixes.Proj.BrunnSections m` (for `m = 0` the exponent `(0:ℝ)⁻¹` is
  `0` and the statement is concavity of the constant `1`).
* Unconditional versions: `cor68_pl`, `thm95_pointwise_pl`, `thm95_pl`, `cm_of_cond22_pl`,
  `cor96d_poly_pl`, `cor96d_poly_iff_pl`.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

namespace Mixes.PrekopaLeindler

/-- Volume of an affine image `x ↦ a x + c` of a set of reals, `a > 0`. -/
lemma volume_affine_image {a : ℝ} (ha : 0 < a) (c : ℝ) (K : Set ℝ) :
    volume ((fun x => a * x + c) '' K) = ENNReal.ofReal a * volume K := by
  have : (fun x => a * x + c) '' K = c +ᵥ (a • K) := by
    ext z; simp only [mem_image, Set.mem_vadd_set, Set.mem_smul_set, smul_eq_mul, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨a * x, ⟨x, hx, rfl⟩, by ring⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, by ring⟩
  rw [this, measure_vadd, Measure.addHaar_smul]
  simp [abs_of_pos ha]

/-- **One-dimensional Brunn–Minkowski, compact sets.** -/
lemma bm1_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {K L : Set ℝ} (hK : IsCompact K)
    (hL : IsCompact L) (hK0 : K.Nonempty) (hL0 : L.Nonempty) {C : Set ℝ}
    (hC : ∀ x ∈ K, ∀ y ∈ L, a * x + b * y ∈ C) :
    ENNReal.ofReal a * volume K + ENNReal.ofReal b * volume L ≤ volume C := by
  set M := sSup K
  set m := sInf L
  have hM : M ∈ K := hK.sSup_mem hK0
  have hm : m ∈ L := hL.sInf_mem hL0
  set P := (fun x => a * x + b * m) '' K
  set Q := (fun y => b * y + a * M) '' L
  have hPv : volume P = ENNReal.ofReal a * volume K := volume_affine_image ha _ _
  have hQv : volume Q = ENNReal.ofReal b * volume L := volume_affine_image hb _ _
  set c := a * M + b * m
  have hPc : P \ {c} ⊆ Iio c := by
    rintro _ ⟨⟨x, hx, rfl⟩, hne⟩
    have : x ≤ M := le_csSup hK.bddAbove hx
    have : a * x + b * m ≤ c := by simp only [c]; nlinarith
    exact lt_of_le_of_ne this hne
  have hQc : Q ⊆ Ici c := by
    rintro _ ⟨y, hy, rfl⟩
    have : m ≤ y := csInf_le hL.bddBelow hy
    show c ≤ b * y + a * M
    simp only [c]; nlinarith
  have hdisj : Disjoint (P \ {c}) Q := by
    rw [Set.disjoint_left]; intro z hz hz'
    exact lt_irrefl _ ((show z < c from hPc hz).trans_le (show c ≤ z from hQc hz'))
  have hQm : MeasurableSet Q := (hL.image (by fun_prop)).isClosed.measurableSet
  have hsub : P \ {c} ∪ Q ⊆ C := by
    rintro _ (⟨⟨x, hx, rfl⟩, -⟩ | ⟨y, hy, rfl⟩)
    · exact hC x hx m hm
    · show b * y + a * M ∈ C; rw [add_comm]; exact hC M hM y hy
  calc ENNReal.ofReal a * volume K + ENNReal.ofReal b * volume L
      = volume (P \ {c}) + volume Q := by
        rw [measure_sdiff_null (measure_singleton c), hPv, hQv]
    _ = volume (P \ {c} ∪ Q) := (measure_union hdisj hQm).symm
    _ ≤ volume C := measure_mono hsub

/-- **One-dimensional Brunn–Minkowski, measurable sets.** For nonempty measurable `A, B ⊆ ℝ`
and any `C` containing `a A + b B`, `|C| ≥ a |A| + b |B|`. -/
lemma bm1 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hA0 : A.Nonempty) (hB0 : B.Nonempty) {C : Set ℝ}
    (hC : ∀ x ∈ A, ∀ y ∈ B, a * x + b * y ∈ C) :
    ENNReal.ofReal a * volume A + ENNReal.ofReal b * volume B ≤ volume C := by
  obtain ⟨x0, hx0⟩ := hA0
  obtain ⟨y0, hy0⟩ := hB0
  have e : ∀ {S : Set ℝ}, MeasurableSet S →
      volume S = ⨆ K : {K : Set ℝ // K ⊆ S ∧ IsCompact K}, volume (K : Set ℝ) := by
    intro S hS
    rw [hS.measure_eq_iSup_isCompact]
    apply le_antisymm
    · exact iSup₂_le fun K hK => iSup_le fun hc => le_iSup_of_le ⟨K, hK, hc⟩ le_rfl
    · exact iSup_le fun K => le_iSup₂_of_le K.1 K.2.1 (le_iSup_of_le K.2.2 le_rfl)
  have : ∀ S : Set ℝ, Nonempty {K : Set ℝ // K ⊆ S ∧ IsCompact K} :=
    fun S => ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  rw [e hA, e hB]
  simp only [ENNReal.mul_iSup]
  refine ENNReal.iSup_add_iSup_le fun ⟨K, hKA, hK⟩ ⟨L, hLB, hL⟩ => ?_
  dsimp only
  calc ENNReal.ofReal a * volume K + ENNReal.ofReal b * volume L
      ≤ ENNReal.ofReal a * volume (insert x0 K) + ENNReal.ofReal b * volume (insert y0 L) := by
        gcongr <;> exact subset_insert _ _
    _ ≤ volume C := bm1_compact ha hb (hK.insert x0) (hL.insert y0) (insert_nonempty _ _)
        (insert_nonempty _ _) fun x hx y hy =>
          hC x (insert_subset hx0 hKA hx) y (insert_subset hy0 hLB hy)


/-! ### One-dimensional Prékopa–Leindler -/

/-- Layer cake for a measurable function with values in `[0, 1]`. -/
lemma layer_le_one {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (h1 : ∀ x, φ x ≤ 1) :
    ∫⁻ x, φ x = ∫⁻ s in Ioo 0 1, volume {x | ENNReal.ofReal s < φ x} := by
  have hfin : ∀ x, φ x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (h1 x)
  have e1 : ∫⁻ x, φ x = ∫⁻ x, ENNReal.ofReal (φ x).toReal := by
    congr 1; funext x; rw [ENNReal.ofReal_toReal (hfin x)]
  rw [e1, lintegral_eq_lintegral_meas_lt volume (ae_of_all _ fun x => ENNReal.toReal_nonneg)
    hφ.ennreal_toReal.aemeasurable]
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one, lintegral_union measurableSet_Ici
    (Set.disjoint_left.2 fun (x : ℝ) (hx : x ∈ Ioo 0 1) (hx' : x ∈ Ici 1) =>
      lt_irrefl _ (hx.2.trans_le hx'))]
  have e2 : ∫⁻ s in Ici (1 : ℝ), volume {x | s < (φ x).toReal} = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici (g := fun _ => 0) ?_, lintegral_zero]
    intro s hs
    have : {x | s < (φ x).toReal} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (ENNReal.toReal_le_of_le_ofReal (by linarith [mem_Ici.1 hs])
      ((h1 x).trans (by rw [ENNReal.one_le_ofReal]; exact hs)))
    simp only [this, measure_empty]
  rw [e2, add_zero]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  congr 1; ext x
  simp only [mem_ofPred_eq]
  exact (ENNReal.ofReal_lt_iff_lt_toReal hs.1.le (hfin x)).symm

/-- Layer cake, lower bound for any measurable function. -/
lemma layer_ge {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ s in Ioo 0 1, volume {x | ENNReal.ofReal s < ψ x} ≤ ∫⁻ x, ψ x := by
  calc ∫⁻ s in Ioo 0 1, volume {x | ENNReal.ofReal s < ψ x}
      = ∫⁻ s in Ioo 0 1, volume {x | ENNReal.ofReal s < min (ψ x) 1} := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
        congr 1; ext x
        simp only [mem_ofPred_eq, lt_min_iff, iff_self_and]
        intro _; rw [ENNReal.ofReal_lt_one]; exact hs.2
    _ = ∫⁻ x, min (ψ x) 1 := (layer_le_one (hψ.min measurable_const) fun x => min_le_right _ _).symm
    _ ≤ ∫⁻ x, ψ x := lintegral_mono fun x => min_le_left _ _

/-- `s^(1-t) s^t = s`. -/
lemma rpow_split (s : ℝ≥0∞) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s ^ (1 - t) * s ^ t = s := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) ht0, sub_add_cancel, ENNReal.rpow_one]

/-- One-dimensional Prékopa–Leindler, normalised form (`f, g ≤ 1` with supremum `1`). -/
lemma pl1_norm {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ s < 1, ∃ x, s < f x) (hgs : ∀ s < 1, ∃ x, s < g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    ENNReal.ofReal (1 - t) * (∫⁻ x, f x) + ENNReal.ofReal t * (∫⁻ x, g x) ≤ ∫⁻ x, h x := by
  obtain ⟨ht0, ht1⟩ := ht
  rw [layer_le_one hf hf1, layer_le_one hg hg1,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (le_lintegral_add _ _).trans ((setLIntegral_mono' measurableSet_Ioo fun s hs => ?_).trans
    (layer_ge hh))
  have hs1 : ENNReal.ofReal s < 1 := by rw [ENNReal.ofReal_lt_one]; exact hs.2
  obtain ⟨x0, hx0⟩ := hfs _ hs1
  obtain ⟨y0, hy0⟩ := hgs _ hs1
  refine bm1 (by linarith) ht0 (measurableSet_lt measurable_const hf)
    (measurableSet_lt measurable_const hg) ⟨x0, hx0⟩ ⟨y0, hy0⟩ fun x hx y hy => ?_
  simp only [mem_ofPred_eq] at hx hy ⊢
  calc ENNReal.ofReal s = ENNReal.ofReal s ^ (1 - t) * ENNReal.ofReal s ^ t :=
        (rpow_split _ ht0.le ht1.le).symm
    _ < f x ^ (1 - t) * g y ^ t :=
        ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx (by linarith)) (ENNReal.rpow_lt_rpow hy ht0)
    _ ≤ h ((1 - t) * x + t * y) := hfgh x y

/-- Algebra for the normalisation. -/
lemma norm_alg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (X Y F G : ℝ≥0∞) (hF : F ≠ 0) (hF' : F ≠ ⊤) :
    (X * F⁻¹) ^ (1 - t) * (Y * G⁻¹) ^ t = X ^ (1 - t) * Y ^ t * (F ^ (1 - t) * G ^ t)⁻¹ := by
  have h1 : (0 : ℝ) ≤ 1 - t := by linarith
  have a1 : F ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hF) hF').ne'
  have a2 : F ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg h1 hF'
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1, ENNReal.mul_rpow_of_nonneg _ _ ht0, ENNReal.inv_rpow,
    ENNReal.inv_rpow, ENNReal.mul_inv (Or.inl a1) (Or.inl a2)]
  ring

/-- One-dimensional Prékopa–Leindler when `sup f`, `sup g` are positive and finite. -/
lemma pl1_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hF0 : (⨆ x, f x) ≠ 0) (hF1 : (⨆ x, f x) ≠ ⊤)
    (hG0 : (⨆ x, g x) ≠ 0) (hG1 : (⨆ x, g x) ≠ ⊤)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  obtain ⟨ht0, ht1⟩ := ht
  set F := ⨆ x, f x
  set G := ⨆ x, g x
  set c := F ^ (1 - t) * G ^ t
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hF0) hF1).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hG0) hG1).ne'
  have hc1 : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hF1)
    (ENNReal.rpow_ne_top_of_nonneg ht0.le hG1)
  -- normalised functions
  have nle : ∀ {φ : ℝ → ℝ≥0∞}, (⨆ x, φ x) ≠ 0 → (⨆ x, φ x) ≠ ⊤ →
      (∀ x, φ x * (⨆ x, φ x)⁻¹ ≤ 1) ∧ ∀ s < 1, ∃ x, s < φ x * (⨆ x, φ x)⁻¹ := by
    intro φ h0 h1
    refine ⟨fun x => ?_, fun s hs => ?_⟩
    · calc φ x * (⨆ x, φ x)⁻¹ ≤ (⨆ x, φ x) * (⨆ x, φ x)⁻¹ := by gcongr; exact le_iSup φ x
        _ = 1 := ENNReal.mul_inv_cancel h0 h1
    · have : s * (⨆ x, φ x) < ⨆ x, φ x := by
        calc s * (⨆ x, φ x) < 1 * (⨆ x, φ x) := ENNReal.mul_lt_mul_left h0 h1 hs
          _ = _ := one_mul _
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 this
      refine ⟨x, ?_⟩
      calc s = s * (⨆ x, φ x) * (⨆ x, φ x)⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel h0 h1, mul_one]
        _ < φ x * (⨆ x, φ x)⁻¹ :=
            ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0) hx
  obtain ⟨hf1, hfs⟩ := nle hF0 hF1
  obtain ⟨hg1, hgs⟩ := nle hG0 hG1
  have key := pl1_norm ⟨ht0, ht1⟩ (hf.mul_const F⁻¹) (hg.mul_const G⁻¹) (hh.mul_const c⁻¹)
    hf1 hg1 hfs hgs fun x y => by
      rw [norm_alg ht0.le ht1.le _ _ _ _ hF0 hF1]
      exact mul_le_mul' (hfgh x y) le_rfl
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hF0),
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hG0),
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0)] at key
  have amgm := ENNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal (1 - t)) (Real.toNNReal t)
    ((∫⁻ x, f x) * F⁻¹) ((∫⁻ x, g x) * G⁻¹) (by
      rw [← Real.toNNReal_add (by linarith) ht0.le]; simp)
  rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ ht0.le,
    norm_alg ht0.le ht1.le _ _ _ _ hF0 hF1] at amgm
  have := amgm.trans key
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hc1) (ENNReal.inv_ne_top.2 hc0)).1 this


/-- If `sup f = 0` then `∫ f = 0`. -/
lemma lintegral_eq_zero_of_iSup {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (h : (⨆ x, f x) = 0) : ∫⁻ x, f x ∂μ = 0 := by
  have : ∀ x, f x = 0 := fun x => le_antisymm ((le_iSup f x).trans h.le) bot_le
  simp [this]

/-- Passing to the limit along monotone sequences in the product of powers. -/
lemma rpow_mul_rpow_iSup_le {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) {c : ℝ≥0∞} (h : ∀ n, a n ^ p * b n ^ q ≤ c) :
    (⨆ n, a n) ^ p * (⨆ n, b n) ^ q ≤ c := by
  rw [ENNReal.iSup_rpow_of_pos hp, ENNReal.iSup_rpow_of_pos hq, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun k => ?_
  calc a n ^ p * b k ^ q ≤ a (max n k) ^ p * b (max n k) ^ q := by
        gcongr
        · exact ha (le_max_left _ _)
        · exact hb (le_max_right _ _)
    _ ≤ c := h _

/-- **Prékopa–Leindler inequality on `ℝ`** (lower Lebesgue integrals, no integrability or
boundedness assumptions). For `0 < t < 1` and measurable `f, g, h : ℝ → [0, ∞]` with
`h((1-t)x + t y) ≥ f(x)^(1-t) g(y)^t`, `∫ h ≥ (∫ f)^(1-t) (∫ g)^t`. -/
theorem pl1 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  obtain ⟨ht0, ht1⟩ := ht
  have h1t : 0 < 1 - t := by linarith
  by_cases hF0 : (⨆ x, f x) = 0
  · rw [lintegral_eq_zero_of_iSup hF0, ENNReal.zero_rpow_of_pos h1t, zero_mul]; exact bot_le
  by_cases hG0 : (⨆ x, g x) = 0
  · rw [lintegral_eq_zero_of_iSup hG0, ENNReal.zero_rpow_of_pos ht0, mul_zero]; exact bot_le
  -- truncations `min f (n+1)`
  set T : ℕ → ℝ≥0∞ := fun n => (n : ℝ≥0∞) + 1
  have hT : Monotone T := fun n k hnk => by simp only [T]; gcongr
  have hTsup : (⨆ n, T n) = ⊤ := by
    simp only [T]; rw [← ENNReal.iSup_add, ENNReal.iSup_natCast, top_add]
  have hT0 : ∀ n, T n ≠ 0 := fun n => by simp [T]
  have hT1 : ∀ n, T n ≠ ⊤ := fun n => by simp [T]
  have trunc : ∀ {φ : ℝ → ℝ≥0∞}, Measurable φ → (⨆ x, φ x) ≠ 0 →
      (∀ n, (⨆ x, min (φ x) (T n)) ≠ 0 ∧ (⨆ x, min (φ x) (T n)) ≠ ⊤) ∧
      Monotone (fun n => ∫⁻ x, min (φ x) (T n)) ∧
      (⨆ n, ∫⁻ x, min (φ x) (T n)) = ∫⁻ x, φ x := by
    intro φ hφ h0
    refine ⟨fun n => ?_, fun n k hnk => lintegral_mono fun x => min_le_min le_rfl (hT hnk), ?_⟩
    · rw [← iSup_inf_eq]
      refine ⟨?_, ne_top_of_le_ne_top (hT1 n) inf_le_right⟩
      exact (lt_inf_iff.2 ⟨pos_iff_ne_zero.2 h0, pos_iff_ne_zero.2 (hT0 n)⟩).ne'
    · rw [← lintegral_iSup (fun n => hφ.min measurable_const)
        (fun n k hnk x => min_le_min le_rfl (hT hnk))]
      congr 1; funext x
      rw [← inf_iSup_eq, hTsup, inf_top_eq]
  obtain ⟨hf1, hfm, hfs⟩ := trunc hf hF0
  obtain ⟨hg1, hgm, hgs⟩ := trunc hg hG0
  rw [← hfs, ← hgs]
  refine rpow_mul_rpow_iSup_le hfm hgm h1t ht0 fun n => ?_
  refine pl1_pos ⟨ht0, ht1⟩ (hf.min measurable_const) (hg.min measurable_const) hh
    (hf1 n).1 (hf1 n).2 (hg1 n).1 (hg1 n).2 fun x y => ?_
  calc min (f x) (T n) ^ (1 - t) * min (g y) (T n) ^ t ≤ f x ^ (1 - t) * g y ^ t := by
        gcongr <;> exact min_le_left _ _
    _ ≤ _ := hfgh x y


/-! ### The Prékopa–Leindler property and its stability -/

/-- The **Prékopa–Leindler property** of a measure `μ` on a real vector space. -/
def PLProp {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] (μ : Measure E) :
    Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1, ∀ f g h : E → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ

lemma plProp_real : PLProp (volume : Measure ℝ) :=
  fun _ ht _ _ _ hf hg hh H => pl1 ht hf hg hh (by simpa only [smul_eq_mul] using H)

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
  [AddCommGroup F] [Module ℝ F] [MeasurableSpace F]

/-- Prékopa–Leindler passes to products (Fubini–Tonelli). -/
lemma plProp_prod {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν] (hμ : PLProp μ)
    (hν : PLProp ν) : PLProp (μ.prod ν) := by
  intro t ht f g h hf hg hh H
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hh.aemeasurable]
  refine hμ t ht _ _ _ hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' fun s u => ?_
  refine hν t ht _ _ _ (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
    (hh.comp measurable_prodMk_left) fun x y => ?_
  have := H (s, x) (u, y)
  simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

/-- Prékopa–Leindler passes along measure-preserving maps compatible with convex combinations. -/
lemma plProp_of_equiv {μ : Measure E} {ν : Measure F} (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν)
    (hlin : ∀ (t : ℝ) (u v : F), e.symm ((1 - t) • u + t • v) = (1 - t) • e.symm u + t • e.symm v)
    (hν : PLProp ν) : PLProp μ := by
  intro t ht f g h hf hg hh H
  have I : ∀ φ : E → ℝ≥0∞, ∫⁻ y, φ (e.symm y) ∂ν = ∫⁻ x, φ x ∂μ := fun φ => by
    rw [← he.lintegral_comp_emb e.measurableEmbedding]; simp
  have key := hν t ht (fun y => f (e.symm y)) (fun y => g (e.symm y)) (fun y => h (e.symm y))
    (hf.comp e.symm.measurable) (hg.comp e.symm.measurable) (hh.comp e.symm.measurable)
    fun u v => by rw [hlin]; exact H _ _
  rwa [I f, I g, I h] at key

/-- Prékopa–Leindler for `X^n` from Prékopa–Leindler for `X`. -/
lemma plProp_pi {X : Type*} [MeasureSpace X] [SigmaFinite (volume : Measure X)] [AddCommGroup X]
    [Module ℝ X] (hX : PLProp (volume : Measure X)) :
    ∀ n : ℕ, PLProp (volume : Measure (Fin n → X)) := by
  intro n
  induction n with
  | zero =>
    intro t ht f g h hf hg hh H
    have hv : (volume : Measure (Fin 0 → X)) = Measure.dirac (fun i => Fin.elim0 i) :=
      Measure.pi_of_empty _ _
    rw [hv, lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hh]
    have := H (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rwa [Subsingleton.elim ((1 - t) • (fun i => Fin.elim0 i) + t • fun i => Fin.elim0 i)
      (fun i : Fin 0 => (Fin.elim0 i : X))] at this
  | succ n ih =>
    refine plProp_of_equiv (MeasurableEquiv.piFinSuccAbove (fun _ => X) 0)
      (volume_preserving_piFinSuccAbove (fun _ => X) 0) ?_ (plProp_prod hX ih)
    intro t u v
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Prékopa–Leindler on `ℂ`. -/
lemma plProp_complex : PLProp (volume : Measure ℂ) := by
  refine plProp_of_equiv Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod
    ?_ (plProp_prod plProp_real plProp_real)
  intro t u v
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

/-- **Prékopa–Leindler inequality in `ℝⁿ`.** -/
theorem prekopa_leindler (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {f g h : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x :=
  plProp_pi plProp_real n t ht f g h hf hg hh hfgh

/-- **Prékopa–Leindler inequality in `ℂᵐ`.** -/
theorem prekopa_leindler_complex (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {f g h : (Fin m → ℂ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x :=
  plProp_pi plProp_complex m t ht f g h hf hg hh hfgh

/-- **Brunn–Minkowski, multiplicative form**, for any measure with the Prékopa–Leindler
property: if `(1-t)A + tB ⊆ C` then `μ(C) ≥ μ(A)^(1-t) μ(B)^t`. -/
theorem bm_mul_of_plProp {μ : Measure E} (hμ : PLProp μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {A B C : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1 - t) • a + t • b ∈ C) :
    μ A ^ (1 - t) * μ B ^ t ≤ μ C := by
  have h1t : 0 < 1 - t := by linarith [ht.2]
  have := hμ t ht (A.indicator 1) (B.indicator 1) (C.indicator 1)
    (measurable_one.indicator hA) (measurable_one.indicator hB) (measurable_one.indicator hC)
    fun x y => by
      by_cases hx : x ∈ A
      · by_cases hy : y ∈ B
        · simp [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem (hABC x hx y hy)]
        · simp [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos ht.1]
      · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos h1t]
  simpa [lintegral_indicator_one hA, lintegral_indicator_one hB, lintegral_indicator_one hC]
    using this


/-! ### Consequence (A): the radial profiles of the convolution powers `λ_{m+1}` -/

open Mixes.PolyB in
/-- `cp m` is non-increasing along `[0, ∞)`: for `0 ≤ r ≤ s`, `λ_{m+1}(s) ≤ λ_{m+1}(r)`. Writing
`r = (1-t) s + t (-s)`, the set `S_r` of the definition of `cp` contains `(1-t) S_s + t S_{-s}`,
and `|S_{-s}| = |S_s|`, so Brunn–Minkowski (multiplicative form) gives `|S_r| ≥ |S_s|`. -/
theorem cp_anti (m : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : cp m (s : ℂ) ≤ cp m (r : ℂ) := by
  rcases hrs.eq_or_lt with rfl | hrs'
  · exact le_rfl
  have hs : 0 < s := hr.trans_lt hrs'
  set t := (s - r) / (2 * s) with htdef
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hrt : r = (1 - t) * s + t * (-s) := by rw [htdef]; field_simp; ring
  have key := bm_mul_of_plProp (plProp_pi plProp_complex m) ⟨ht0, ht1⟩
    (measurableSet_cpSet m (s : ℂ)) (measurableSet_cpSet m ((-s : ℝ) : ℂ))
    (measurableSet_cpSet m (r : ℂ)) (fun y hy z hz => by
      simp only [mem_ofPred_eq] at hy hz ⊢
      have hc := convex_closedBall (0 : ℂ) 1
      have h1t : (0 : ℝ) ≤ 1 - t := by linarith
      have hsum : 1 - t + t = 1 := by ring
      refine ⟨fun i => ?_, ?_⟩
      · exact hc (hy.1 i) (hz.1 i) h1t ht0.le hsum
      · have := hc hy.2 hz.2 h1t ht0.le hsum
        have e : (r : ℂ) - ∑ i, ((1 - t) • y + t • z) i =
            (1 - t) • ((s : ℂ) - ∑ i, y i) + t • (((-s : ℝ) : ℂ) - ∑ i, z i) := by
          simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Complex.real_smul,
            ← Finset.mul_sum, hrt]
          push_cast
          ring
        rw [e]; exact this)
  have hneg : cp m ((-s : ℝ) : ℂ) = cp m (s : ℂ) := by
    rw [Complex.ofReal_neg, cp_neg]
  change cp m (s : ℂ) ^ (1 - t) * cp m ((-s : ℝ) : ℂ) ^ t ≤ cp m (r : ℂ) at key
  rwa [hneg, rpow_split _ ht0.le ht1.le] at key

/-- **The hypothesis `PLHyp` of `PolyB` holds**: the radial profiles `r ↦ λ_{m+1}(r)` are
non-increasing on `[0, ∞)`. -/
theorem plHyp : Mixes.PolyB.PLHyp := by
  intro m r hr s hs hrs
  exact ENNReal.toReal_mono (Mixes.PolyB.cp_ne_top m _) (cp_anti m hr hrs)

/-! ### Brunn–Minkowski in `ℝᵐ`, additive form, and consequence (B) -/

lemma volume_smul_toReal {m : ℕ} (r : ℝ) (S : Set (Fin m → ℝ)) :
    (volume (r • S)).toReal = |r| ^ m * (volume S).toReal := by
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    Module.finrank_fin_fun, abs_pow]

/-- A translate of `t • B` inside `C`: `|C| ≥ t^m |B|`. -/
lemma volume_le_of_translate {m : ℕ} {t : ℝ} (ht : 0 < t) {B C : Set (Fin m → ℝ)} (v : Fin m → ℝ)
    (hC : volume C ≠ ⊤) (hBC : ∀ b ∈ B, v + t • b ∈ C) :
    t ^ m * (volume B).toReal ≤ (volume C).toReal := by
  have hsub : v +ᵥ (t • B) ⊆ C := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact hBC b hb
  have := ENNReal.toReal_mono hC (measure_mono hsub)
  rwa [measure_vadd, volume_smul_toReal, abs_of_pos ht] at this

/-- **Brunn–Minkowski inequality in `ℝᵐ`** (`m ≥ 1`, additive form). For nonempty measurable
`A, B` of finite measure and measurable `C ⊇ (1-t)A + tB` of finite measure,
`|C|^(1/m) ≥ (1-t)|A|^(1/m) + t|B|^(1/m)`. -/
theorem brunn_minkowski {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {A B C : Set (Fin m → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hA0 : A.Nonempty) (hB0 : B.Nonempty) (hAf : volume A ≠ ⊤)
    (hBf : volume B ≠ ⊤) (hCf : volume C ≠ ⊤)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1 - t) • a + t • b ∈ C) :
    (1 - t) * (volume A).toReal ^ (m : ℝ)⁻¹ + t * (volume B).toReal ^ (m : ℝ)⁻¹ ≤
      (volume C).toReal ^ (m : ℝ)⁻¹ := by
  obtain ⟨ht0, ht1⟩ := ht
  have h1t : 0 < 1 - t := by linarith
  have hm0 : m ≠ 0 := by omega
  have hk : (0 : ℝ) < (m : ℝ)⁻¹ := by positivity
  set a := (volume A).toReal
  set b := (volume B).toReal
  set c := (volume C).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  -- the degenerate cases
  have deg : ∀ {τ : ℝ} {B' : Set (Fin m → ℝ)}, 0 < τ → ∀ v : Fin m → ℝ,
      (∀ b ∈ B', v + τ • b ∈ C) → τ * (volume B').toReal ^ (m : ℝ)⁻¹ ≤ c ^ (m : ℝ)⁻¹ := by
    intro τ B' hτ v hv
    have h1 := volume_le_of_translate hτ v hCf hv
    calc τ * (volume B').toReal ^ (m : ℝ)⁻¹
        = (τ ^ m * (volume B').toReal) ^ (m : ℝ)⁻¹ := by
          rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg,
            Real.pow_rpow_inv_natCast hτ.le hm0]
      _ ≤ c ^ (m : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) h1 hk.le
  obtain ⟨a0, ha0⟩ := hA0
  obtain ⟨b0, hb0⟩ := hB0
  rcases ha.eq_or_lt with ha' | ha'
  · rw [← ha', Real.zero_rpow hk.ne', mul_zero, zero_add]
    exact deg ht0 ((1 - t) • a0) fun b hb => hABC a0 ha0 b hb
  rcases hb.eq_or_lt with hb' | hb'
  · rw [← hb', Real.zero_rpow hk.ne', mul_zero, add_zero]
    exact deg h1t (t • b0) fun a ha => by rw [add_comm]; exact hABC a ha b0 hb0
  -- the main case
  set p := a ^ (m : ℝ)⁻¹
  set q := b ^ (m : ℝ)⁻¹
  have hp : 0 < p := Real.rpow_pos_of_pos ha' _
  have hq : 0 < q := Real.rpow_pos_of_pos hb' _
  have hpm : p ^ m = a := Real.rpow_inv_natCast_pow ha hm0
  have hqm : q ^ m = b := Real.rpow_inv_natCast_pow hb hm0
  set D := (1 - t) * p + t * q
  have hD : 0 < D := by positivity
  set σ := t * q / D
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ < 1 := (div_lt_one hD).2 (by simp only [D]; nlinarith)
  have h1σ : 1 - σ = (1 - t) * p / D := by simp only [σ]; field_simp; ring
  have key := bm_mul_of_plProp (plProp_pi plProp_real m) ⟨hσ0, hσ1⟩
    (hA.const_smul_of_ne_zero (inv_ne_zero hp.ne')) (hB.const_smul_of_ne_zero (inv_ne_zero hq.ne'))
    (hC.const_smul_of_ne_zero (inv_ne_zero hD.ne')) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      refine ⟨(1 - t) • x + t • y, hABC x hx y hy, ?_⟩
      simp only [smul_add, smul_smul, h1σ]
      congr 2
      · field_simp
      · simp only [σ]; field_simp)
  have e1 : ∀ {r : ℝ} {S : Set (Fin m → ℝ)}, 0 < r → volume S ≠ ⊤ → r ^ m = (volume S).toReal →
      volume (r⁻¹ • S) = 1 := by
    intro r S hr hS hrS
    rw [Measure.addHaar_smul, Module.finrank_fin_fun, ← ENNReal.ofReal_toReal hS, ← hrS,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity), inv_pow,
      inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
  rw [e1 hp hAf hpm, e1 hq hBf hqm, ENNReal.one_rpow, ENNReal.one_rpow, one_mul,
    Measure.addHaar_smul, Module.finrank_fin_fun, ← ENNReal.ofReal_toReal hCf,
    ← ENNReal.ofReal_mul (abs_nonneg _), ENNReal.one_le_ofReal, abs_of_pos (by positivity),
    inv_pow] at key
  have hDm : D ^ m ≤ c := by
    have := mul_le_mul_of_nonneg_left key (pow_pos hD m).le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ (pow_pos hD m).ne', one_mul] at this
  calc (1 - t) * p + t * q = D := rfl
    _ = (D ^ m) ^ (m : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hD.le hm0).symm
    _ ≤ c ^ (m : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) hDm hk.le

/-- **Brunn's theorem: the hypothesis `BrunnSections m` of `Proj` holds for every `m`.** For
`m = 0` the exponent is `(0 : ℝ)⁻¹ = 0` and the function is the constant `1`. -/
theorem brunnSections (m : ℕ) : Mixes.Proj.BrunnSections m := by
  intro C hC hconv
  have hfst : Convex ℝ (Prod.fst '' C) := by
    simpa using hconv.linear_image (LinearMap.fst ℝ ℝ (Fin m → ℝ))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using concaveOn_const (1 : ℝ) hfst
  refine ⟨hfst, ?_⟩
  rintro s ⟨⟨s', x0⟩, hx0, rfl⟩ u ⟨⟨u', y0⟩, hy0, rfl⟩ a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  obtain rfl : a = 1 - b := by linarith
  have hmeas : ∀ w : ℝ, MeasurableSet (Prod.mk w ⁻¹' C) := fun w =>
    hC.isClosed.measurableSet.preimage measurable_prodMk_left
  have hfin : ∀ w : ℝ, volume (Prod.mk w ⁻¹' C) ≠ ⊤ := fun w =>
    ne_top_of_le_ne_top (hC.image continuous_snd).measure_lt_top.ne
      (measure_mono fun y hy => ⟨(w, y), hy, rfl⟩)
  have := brunn_minkowski hm ⟨hb', by linarith⟩ (hmeas s') (hmeas u') (hmeas ((1 - b) • s' + b • u'))
    ⟨x0, hx0⟩ ⟨y0, hy0⟩ (hfin _) (hfin _) (hfin _) fun x hx y hy => by
      have := hconv hx hy ha hb hab
      simpa only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk] using this
  simpa only [smul_eq_mul] using this


/-! ### Unconditional versions of the results that took `BrunnSections` or `PLHyp` -/

section Unconditional

open Module Mixes.PolyB

/-- **Corollary 68** (`o:cor:proj`), first statement, without the Brunn hypothesis: for a convex
body `K` in a real space of dimension `d ≥ 2`, `X ∼ U(K)` and a nonzero linear functional `u`,
the law of `u(X)` is `n`-completely mixable for every `n ≥ d + 1`. -/
theorem cor68_pl {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {d : ℕ} (hd : 2 ≤ d)
    (hV : finrank ℝ V = d) {K : Set V} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (u : V →L[ℝ] ℝ) (hu : u ≠ 0) :
    ∀ n : ℕ, d + 1 ≤ n → Mixes.CompletelyMixable n ((Mixes.unifSet K).map u) :=
  Mixes.Proj.cor68 hd hV (brunnSections _) hKc hKconv hKi u hu

/-- **Theorem 95, pointwise form (22)**, without the Prékopa–Leindler hypothesis. -/
theorem thm95_pointwise_pl (m k : ℕ) (hk : 3 ≤ k)
    (haR : 0 < aF m (Mixes.Poly.secR k : ℂ)) (ha1 : (m + 2) * hF m 0 / k < aF m 1) :
    ∃ φ : ℂ → ℝ, Measurable φ ∧
      (∀ q ∈ disc, |φ q| ≤ (m + 3) * Mixes.Poly.W (m + 3) k (hF m 0)
        (aF m (Mixes.Poly.secR k : ℂ)) (Mixes.Poly.Ssum (m + 3) k) /
          (aF m 1 - (m + 2) * hF m 0 / k)) ∧
      (∀ᵐ p ∂(volume : Measure ℂ), p ∈ disc → Gop m φ p = -(nu m k p - nus m k p)) ∧
      ∀ t : ℝ, (∀ q ∈ disc, |φ q| ≤ t) →
        (∀ q ∈ disc, nus m k q + t * aF m q ≤ 1 / Mixes.Poly.area k) →
        Mixes.CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) :=
  thm95_pointwise plHyp m k hk haR ha1

/-- **Theorem 95 (`st:thm:poly`), condition (21)**, without the Prékopa–Leindler hypothesis. -/
theorem thm95_pl (m k : ℕ) (hk : 3 ≤ k) (haR : 0 < aF m (Mixes.Poly.secR k : ℂ))
    {N : ℝ} (hN : ∀ q ∈ disc, nu m k q ≤ N)
    (h21 : Mixes.Poly.Cond21 (m + 3) k (aF m 1) (aF m (Mixes.Poly.secR k : ℂ)) (hF m 0) (aF m 0)
      (Mixes.Poly.Ssum (m + 3) k) N) :
    Mixes.CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) :=
  thm95 plHyp m k hk haR hN h21

/-- `cm_of_cond22` without the Prékopa–Leindler hypothesis. -/
theorem cm_of_cond22_pl {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Mixes.Poly.secR k : ℂ))
    (ha1 : (m + 2) * hF m 0 / k < aF m 1) (h22 : Cond22 m k) :
    Mixes.CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) :=
  cm_of_cond22 plHyp hk haR ha1 h22

/-- **Corollary 96 (d), `n ≥ 3`**, without the Prékopa–Leindler hypothesis (the other hypotheses
of `cor96d_poly` remain). -/
theorem cor96d_poly_pl
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Mixes.Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Mixes.Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Mixes.Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Mixes.Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Mixes.Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Mixes.Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Mixes.Poly.secR 7 : ℂ) ∧ Cond22 2 7)
    (htri : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → Mixes.CompletelyMixable n (Mixes.unifSet (poly 3)))
    (hsq : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → Mixes.CompletelyMixable n (Mixes.unifSet (poly 4)))
    (hhex : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → Mixes.CompletelyMixable n (Mixes.unifSet (poly 6))) :
    ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, 3 ≤ n → Mixes.CompletelyMixable n (Mixes.unifSet (poly k)) :=
  cor96d_poly plHyp ha41 ha49 ha48 ha51 ha59 hc4u hcap h53 h54 h74 h75 htri hsq hhex

/-- **Corollary 96 (d), complete**, without the Prékopa–Leindler hypothesis: under the other
hypotheses of `cor96d_poly`, for `k ≥ 3` and `n ≥ 2`, `U(P_k)` is `n`-completely mixable exactly
when `n ≥ 3` or `k` is even. -/
theorem cor96d_poly_iff_pl
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Mixes.Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Mixes.Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Mixes.Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Mixes.Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Mixes.Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Mixes.Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Mixes.Poly.secR 7 : ℂ) ∧ Cond22 2 7)
    (htri : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → Mixes.CompletelyMixable n (Mixes.unifSet (poly 3)))
    (hsq : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → Mixes.CompletelyMixable n (Mixes.unifSet (poly 4)))
    (hhex : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → Mixes.CompletelyMixable n (Mixes.unifSet (poly 6)))
    {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) :
    Mixes.CompletelyMixable n (Mixes.unifSet (poly k)) ↔ 3 ≤ n ∨ Even k :=
  cor96d_poly_iff plHyp ha41 ha49 ha48 ha51 ha59 hc4u hcap h53 h54 h74 h75 htri hsq hhex hk hn

end Unconditional

end Mixes.PrekopaLeindler
