import Mixes.Thm113
import Mixes.LLT
import Mixes.Markov

/-!
# Theorem 113 (`jl:thm:main`): joint mixes of densities for large `n`

Proof of `Large.Thm113 E` and `Large.Thm113Sym E` for a finite-dimensional real inner product
space `E` with any additive Haar measure `volume`, given one cited result stated as an explicit
hypothesis: the Tychonoff (Schauder–Tychonoff) fixed point theorem in the locally convex space
`ℝ^ι` (`TychonoffFP`).

Lemma 112 (`Thm113.llt_delta`) and the `L¹` modulus (`LLT.l1_modulus`) are proved for the
canonical volume `vol0`; they are transferred to `volume = c • vol0` (Haar uniqueness).

Differences from the paper's proof:
* no projection `P_j` onto affine functions: the unknown is `ψ = (ψ_j)` with `ψ_j = 0` off
  `K_j`, `|ψ_j| ≤ 1` and `Lip(ψ_j) ≤ 1` on `K_j`, and the tilt `v` of Lemma 111(b) is
  recomputed from `ψ`; `Φ(ψ)_j(p) = -(log f_{-j}(s - p) - log f_{-j}(s - m_j))`;
* the fixed point theorem is applied in `ℝ^{Fin n × E}` with the product topology, where the set
  of such `ψ` is compact by Tychonoff's theorem (no Arzelà–Ascoli needed);
* the Lipschitz estimate uses the `L¹` modulus of one factor and the ratio bound of Lemma 112 for
  the convolution of the others (no comparison constant `C₁`).
-/

open MeasureTheory Real RealInnerProductSpace Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Thm113B

universe u

/-- **Tychonoff's fixed point theorem** in `ℝ^ι` (product topology, a locally convex Hausdorff
space): a continuous self-map of a nonempty compact convex set has a fixed point. Stated as an
explicit hypothesis (Mathlib lacks Schauder–Tychonoff). -/
def TychonoffFP : Prop :=
  ∀ (ι : Type u) (C : Set (ι → ℝ)), IsCompact C → Convex ℝ C → C.Nonempty →
    ∀ f : (ι → ℝ) → (ι → ℝ), ContinuousOn f C → Set.MapsTo f C C → ∃ x ∈ C, f x = x

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

section Haar

variable (E) in
/-- The canonical volume of `E`. -/
def vol0 : Measure E := @volume E measureSpaceOfInnerProductSpace

instance : (vol0 E).IsAddHaarMeasure := by unfold vol0; infer_instance

variable (E) in
/-- The scale `c` with `volume = c • vol0`. -/
def cH : ℝ := ((volume : Measure E).addHaarScalarFactor (vol0 E) : ℝ)

lemma cH_pos : 0 < cH E := by
  unfold cH
  exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma volume_eq : (volume : Measure E) = ENNReal.ofReal (cH E) • vol0 E := by
  have h := Measure.isAddLeftInvariant_eq_smul (volume : Measure E) (vol0 E)
  rw [cH, ENNReal.ofReal_coe_nnreal]
  exact h

lemma integral_eq (f : E → ℝ) : ∫ x, f x = cH E * ∫ x, f x ∂(vol0 E) := by
  conv_lhs => rw [volume_eq]
  rw [integral_smul_measure, ENNReal.toReal_ofReal cH_pos.le, smul_eq_mul]

lemma integral_eq' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) :
    ∫ x, f x = cH E • ∫ x, f x ∂(vol0 E) := by
  conv_lhs => rw [volume_eq]
  rw [integral_smul_measure, ENNReal.toReal_ofReal cH_pos.le]

lemma real_eq (K : Set E) : volume.real K = cH E * (vol0 E).real K := by
  rw [measureReal_def, measureReal_def, volume_eq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal cH_pos.le]

lemma integrable_iff {f : E → ℝ} : Integrable f ↔ Integrable f (vol0 E) := by
  rw [volume_eq]
  exact integrable_smul_measure (by simpa using cH_pos (E := E)) ENNReal.ofReal_ne_top

/-- The convolution with respect to `volume`. -/
def cv (f g : E → ℝ) (x : E) : ℝ := ∫ t, f t * g (x - t)

/-- The convolution `h_0 * ⋯ * h_m` with respect to `volume`. -/
def cvF : (m : ℕ) → (Fin (m + 1) → E → ℝ) → E → ℝ
  | 0, hs => hs 0
  | m + 1, hs => cv (hs 0) (cvF m (Fin.tail hs))

lemma conv_vol0 (f g : E → ℝ) (x : E) :
    Thm113.conv f g x = ∫ t, f t * g (x - t) ∂(vol0 E) := rfl

lemma cv_eq (f g : E → ℝ) (x : E) : cv f g x = cH E * Thm113.conv f g x := by
  rw [cv, integral_eq, conv_vol0]

lemma convF_smul (c : ℝ) : ∀ (m : ℕ) (hs : Fin (m + 1) → E → ℝ) (y : E),
    Thm113.convF m (fun k z => c * hs k z) y = c ^ (m + 1) * Thm113.convF m hs y
  | 0, hs, y => by simp [Thm113.convF]
  | m + 1, hs, y => by
    show Thm113.conv _ (Thm113.convF m (Fin.tail fun k z => c * hs k z)) y =
      c ^ (m + 2) * Thm113.conv (hs 0) (Thm113.convF m (Fin.tail hs)) y
    have e : Thm113.convF m (Fin.tail fun k z => c * hs k z) =
        fun z => c ^ (m + 1) * Thm113.convF m (Fin.tail hs) z := by
      funext z; exact convF_smul c m (Fin.tail hs) z
    rw [e, conv_vol0, conv_vol0, ← integral_const_mul]
    congr 1; funext t; ring

lemma cvF_eq : ∀ (m : ℕ) (hs : Fin (m + 1) → E → ℝ) (y : E),
    cvF m hs y = cH E ^ m * Thm113.convF m hs y
  | 0, hs, y => by simp [cvF, Thm113.convF]
  | m + 1, hs, y => by
    show cv (hs 0) (cvF m (Fin.tail hs)) y =
      cH E ^ (m + 1) * Thm113.conv (hs 0) (Thm113.convF m (Fin.tail hs)) y
    have e : cvF m (Fin.tail hs) = fun z => cH E ^ m * Thm113.convF m (Fin.tail hs) z := by
      funext z; exact cvF_eq m (Fin.tail hs) z
    rw [cv_eq, e, conv_vol0, conv_vol0, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext t; ring

/-- `cvF hs = convF (c • hs) / c`. -/
lemma cvF_eq' (m : ℕ) (hs : Fin (m + 1) → E → ℝ) (y : E) :
    cvF m hs y = Thm113.convF m (fun k z => cH E * hs k z) y / cH E := by
  rw [cvF_eq, convF_smul, eq_div_iff cH_pos.ne', pow_succ]; ring

lemma meanD_eq (h : E → ℝ) : Large.meanD h = ∫ y, (cH E * h y) • y ∂(vol0 E) := by
  rw [Large.meanD, integral_eq']
  rw [← integral_smul]
  congr 1; funext y; rw [smul_smul]

/-- The class `𝓗(A, r, R)` of Lemma 112 with respect to `volume`. -/
structure GH (A r R : ℝ) (K : Set E) (h : E → ℝ) : Prop where
  compact : IsCompact K
  convex : Convex ℝ K
  ball : ∃ b, Metric.closedBall b r ⊆ K
  diam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R
  meas : Measurable h
  zero : ∀ y ∉ K, h y = 0
  int : ∫ y, h y = 1
  low : ∀ y ∈ K, exp (-A) ≤ volume.real K * h y
  up : ∀ y ∈ K, volume.real K * h y ≤ exp A

lemma GH.toInH {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) :
    @Thm113.InH E _ _ _ _ _ A r R K (fun y => cH E * h y) := by
  have hc := cH_pos (E := E)
  refine ⟨hH.compact, hH.convex, hH.ball, hH.diam, hH.meas.const_mul _, fun y hy => by
    simp [hH.zero y hy], ?_, fun y hy => ?_, fun y hy => ?_⟩
  · show ∫ y, cH E * h y ∂(vol0 E) = 1
    rw [integral_const_mul, ← integral_eq, hH.int]
  · show exp (-A) ≤ (vol0 E).real K * (cH E * h y)
    have := hH.low y hy; rw [real_eq] at this; linarith
  · show (vol0 E).real K * (cH E * h y) ≤ exp A
    have := hH.up y hy; rw [real_eq] at this; linarith

/-- **Lemma 112, second part, for `volume`.** -/
theorem llt_delta_g {A r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (ρ : ℝ) :
    ∃ (N : ℕ) (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) ∧ ∀ m ≥ N, ∀ (Ks : Fin (m + 2) → Set E)
      (hs : Fin (m + 2) → E → ℝ), (∀ k, GH A r R (Ks k) (hs k)) → ∀ y y' : E,
      ‖y - ∑ k, Large.meanD (hs k)‖ ≤ ρ → ‖y' - ∑ k, Large.meanD (hs k)‖ ≤ ρ →
      0 < cvF (m + 1) hs y' ∧ |cvF (m + 1) hs y / cvF (m + 1) hs y' - 1| ≤ δ m := by
  obtain ⟨N, δ, hδ, H⟩ := @Thm113.llt_delta E _ _ _ _ _ A r R hr hrR ρ
  refine ⟨N, δ, hδ, fun m hm Ks hs hH y y' hy hy' => ?_⟩
  have hc := cH_pos (E := E)
  have hmu : ∑ k, Large.meanD (hs k) = Thm113.muF (fun k z => cH E * hs k z) := by
    exact Finset.sum_congr rfl fun k _ => meanD_eq _
  rw [hmu] at hy hy'
  obtain ⟨h1, h2⟩ := H m hm Ks _ (fun k => (hH k).toInH) y y' hy hy'
  rw [cvF_eq' _ _ y, cvF_eq' _ _ y', div_div_div_cancel_right₀ hc.ne']
  exact ⟨div_pos h1 hc, h2⟩

/-- The `L¹` modulus (`LLT.l1_modulus`) for `volume`, for a convex body containing a closed ball
of radius `ρ` about any point, in any dimension. -/
theorem l1_modulus_g {K : Set E} (hKm : MeasurableSet K) (hK : Convex ℝ K) {ρ : ℝ}
    (hρ : 0 < ρ) {b : E} (hball : Metric.closedBall b ρ ⊆ K) (hfin : volume K ≠ ⊤)
    {h : E → ℝ} {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hhK : ∀ x, x ∉ K → h x = 0) (hgG : ∀ x ∈ K, |h x| ≤ G)
    (hgL : ∀ x ∈ K, ∀ x' ∈ K, |h x - h x'| ≤ L * ‖x - x'‖) (y y' : E) :
    ∫ z, |h (y - z) - h (y' - z)| ≤
      (L * volume.real K + 2 * G * Module.finrank ℝ E * volume.real K / ρ) * ‖y - y'‖ := by
  by_cases hd : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff (R := ℝ).1 hd
    rw [Subsingleton.elim y y']
    simp
  have hc := cH_pos (E := E)
  set K' : Set E := (fun x => b + x) ⁻¹' K
  have hK'm : MeasurableSet K' := (measurable_const_add b) hKm
  have hvol : volume K' = volume K := measure_preimage_add _ _ _
  have hvol0 : (vol0 E) K' = (vol0 E) K := measure_preimage_add _ _ _
  have hK' : Convex ℝ K' := hK.translate_preimage_right b
  have hball' : Metric.closedBall (0 : E) ρ ⊆ K' := fun x hx => hball (by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
  have hfin0 : (vol0 E) K' ≠ ⊤ := by
    intro h0
    apply hfin
    rw [← hvol, volume_eq, FunLike.coe_smul, Pi.smul_apply, h0, smul_eq_mul,
      ENNReal.mul_top (by simpa using hc)]
  have H := @LLT.l1_modulus E _ _ _ _ _ K' hK'm hK' ρ hρ hball' hfin0 (by omega)
    (fun x => h (b + x)) G L hG hL (fun x hx => hhK _ hx) (fun x hx => hgG _ hx)
    (fun x hx x' hx' => by
      have := hgL _ hx _ hx'
      rwa [show b + x - (b + x') = x - x' by abel] at this) (y - b) (y' - b)
  have e1 : ∫ z, |h (y - z) - h (y' - z)| =
      cH E * ∫ z, |h (b + (y - b - z)) - h (b + (y' - b - z))| ∂(vol0 E) := by
    rw [integral_eq]; congr 2; funext z
    rw [show b + (y - b - z) = y - z by abel, show b + (y' - b - z) = y' - z by abel]
  have e2 : volume.real K = cH E * (vol0 E).real K' := by
    rw [real_eq, measureReal_def, measureReal_def, hvol0]
  rw [e1, e2, show y - b - (y' - b) = y - y' by abel] at *
  calc cH E * ∫ z, |h (b + (y - b - z)) - h (b + (y' - b - z))| ∂(vol0 E)
      ≤ cH E * ((L * (vol0 E).real K' + 2 * G * Module.finrank ℝ E * (vol0 E).real K' / ρ) *
          ‖y - y'‖) := mul_le_mul_of_nonneg_left H hc.le
    _ = _ := by ring

/-- Bounded probability densities with respect to `volume`. -/
structure PDg (M : ℝ) (h : E → ℝ) : Prop where
  int : Integrable h
  meas : Measurable h
  nonneg : ∀ y, 0 ≤ h y
  le : ∀ y, h y ≤ M
  one : ∫ y, h y = 1

lemma PDg.toPD {M : ℝ} {h : E → ℝ} (hP : PDg M h) :
    @Thm113.PD E _ _ _ _ _ (cH E * M) (fun y => cH E * h y) := by
  have hc := cH_pos (E := E)
  refine ⟨(integrable_iff.1 hP.int).const_mul _, hP.meas.const_mul _,
    fun y => mul_nonneg hc.le (hP.nonneg y), fun y => mul_le_mul_of_nonneg_left (hP.le y) hc.le,
    ?_⟩
  show ∫ y, cH E * h y ∂(vol0 E) = 1
  rw [integral_const_mul, ← integral_eq, hP.one]

lemma cvF_props {M : ℝ} (m : ℕ) (hs : Fin (m + 1) → E → ℝ) (hP : ∀ k, PDg M (hs k)) :
    Integrable (cvF m hs) ∧ (∀ y, 0 ≤ cvF m hs y) ∧ (∀ y, cvF m hs y ≤ M) ∧
      ∫ y, cvF m hs y = 1 := by
  have hc := cH_pos (E := E)
  obtain ⟨i1, n1, l1, o1⟩ := @Thm113.pd_convF E _ _ _ _ _ _ m _ fun k => (hP k).toPD
  have e : cvF m hs = fun y => Thm113.convF m (fun k z => cH E * hs k z) y / cH E := by
    funext y; exact cvF_eq' m hs y
  rw [e]
  refine ⟨integrable_iff.2 (i1.div_const _), fun y => div_nonneg (n1 y) hc.le,
    fun y => by rw [div_le_iff₀ hc, mul_comm]; exact l1 y, ?_⟩
  have o1' : ∫ y, Thm113.convF m (fun k z => cH E * hs k z) y ∂(vol0 E) = 1 := o1
  rw [integral_eq, integral_div, o1']; field_simp

lemma measurable_cvF {M : ℝ} (m : ℕ) (hs : Fin (m + 1) → E → ℝ) (hP : ∀ k, PDg M (hs k)) :
    Measurable (cvF m hs) := by
  cases m with
  | zero => exact (hP 0).meas
  | succ m =>
    have e : cvF (m + 1) hs = fun y => Thm113.convF (m + 1) (fun k z => cH E * hs k z) y /
        cH E := by
      funext y; exact cvF_eq' _ hs y
    rw [e]
    exact ((@Thm113.continuous_convF E _ _ _ _ _ _ m _ fun k => (hP k).toPD).measurable).div_const _

lemma continuous_cvF {M : ℝ} (m : ℕ) (hs : Fin (m + 2) → E → ℝ) (hP : ∀ k, PDg M (hs k)) :
    Continuous (cvF (m + 1) hs) := by
  have e : cvF (m + 1) hs = fun y => Thm113.convF (m + 1) (fun k z => cH E * hs k z) y /
      cH E := by
    funext y; exact cvF_eq' _ hs y
  rw [e]
  exact (@Thm113.continuous_convF E _ _ _ _ _ _ m _ fun k => (hP k).toPD).div_const _

/-- `cvF` does not depend on the order of the factors (two or more factors). -/
lemma cvF_perm {M : ℝ} (m : ℕ) (hs : Fin (m + 2) → E → ℝ) (hP : ∀ k, PDg M (hs k))
    (σ : Equiv.Perm (Fin (m + 2))) (y : E) :
    cvF (m + 1) (fun k => hs (σ k)) y = cvF (m + 1) hs y := by
  rw [cvF_eq', cvF_eq']
  congr 1
  have h1 := @Thm113.convF_inversion E _ _ _ _ _ _ m _ (fun k => (hP (σ k)).toPD) y
  have h2 := @Thm113.convF_inversion E _ _ _ _ _ _ m _ (fun k => (hP k).toPD) y
  have : (Thm113.convF (m + 1) (fun k z => cH E * hs (σ k) z) y : ℂ) =
      (Thm113.convF (m + 1) (fun k z => cH E * hs k z) y : ℂ) := by
    rw [h1, h2]
    congr 1; funext ξ; congr 1
    exact Equiv.prod_comp σ (fun k => Thm113.ft (fun z => cH E * hs k z) ξ)
  exact_mod_cast this

end Haar

section Marginal

lemma lintegral_fin_succ' (k : ℕ) (F : (Fin (k + 1) → E) → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ x0 : E, ∫⁻ x' : Fin k → E, F (Fin.cons x0 x' : Fin (k + 1) → E) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => E) 0).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ => E) 0).symm p))
      (hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
  congr 1; funext x0; congr 1; funext x'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

lemma measurable_cons (k : ℕ) :
    Measurable fun p : E × (Fin k → E) => (Fin.cons p.1 p.2 : Fin (k + 1) → E) := by
  have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) 0).symm.measurable
  convert this using 1
  funext p
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

lemma measurable_prodF {k : ℕ} {f : Fin (k + 1) → E → ℝ} (hm : ∀ i, Measurable (f i)) (y : E) :
    Measurable fun x : Fin k → E =>
      ENNReal.ofReal (∏ l, f (Fin.castSucc l) (x l)) *
        ENNReal.ofReal (f (Fin.last k) (y - ∑ i, x i)) :=
  (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
    (hm _).comp (measurable_pi_apply i))).mul (ENNReal.measurable_ofReal.comp
      ((hm _).comp (measurable_const.sub (Finset.measurable_sum _
        fun i _ => measurable_pi_apply i))))

/-- `∫_{E^k} ∏_{l<k} f_l(x_l) f_k(y - ∑ x_l) dx = (f_0 * ⋯ * f_k)(y)`. -/
lemma lintegral_prod_eq_cvF {M : ℝ} : ∀ (k : ℕ) (f : Fin (k + 1) → E → ℝ),
    (∀ i, PDg M (f i)) → ∀ y : E,
    ∫⁻ x : Fin k → E, ENNReal.ofReal (∏ l, f (Fin.castSucc l) (x l)) *
      ENNReal.ofReal (f (Fin.last k) (y - ∑ i, x i)) = ENNReal.ofReal (cvF k f y)
  | 0, f, hP, y => by
    rw [show (volume : Measure (Fin 0 → E)) = Measure.dirac (fun i => Fin.elim0 i) from
      Measure.pi_of_empty _ _, lintegral_dirac]
    simp [cvF]
  | k + 1, f, hP, y => by
    rw [lintegral_fin_succ' k _ (measurable_prodF (fun i => (hP i).meas) y)]
    have e : ∀ (x0 : E) (x' : Fin k → E),
        ENNReal.ofReal (∏ l, f (Fin.castSucc l) ((Fin.cons x0 x' : Fin (k + 1) → E) l)) *
          ENNReal.ofReal (f (Fin.last (k + 1)) (y - ∑ i, (Fin.cons x0 x' : Fin (k + 1) → E) i))
        = ENNReal.ofReal (f 0 x0) * (ENNReal.ofReal (∏ l, Fin.tail f (Fin.castSucc l) (x' l)) *
          ENNReal.ofReal (Fin.tail f (Fin.last k) ((y - x0) - ∑ i, x' i))) := fun x0 x' => by
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ, Fin.tail, Fin.castSucc_zero, Fin.succ_last]
      rw [ENNReal.ofReal_mul ((hP 0).nonneg x0), sub_sub, mul_assoc]
      simp only [Fin.succ_castSucc]
    simp_rw [e]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have IH := fun z => lintegral_prod_eq_cvF k (Fin.tail f) (fun i => hP i.succ) z
    simp_rw [IH]
    obtain ⟨i1, n1, l1, o1⟩ := cvF_props k (Fin.tail f) fun i => hP i.succ
    have hi : Integrable fun t => f 0 t * cvF k (Fin.tail f) (y - t) :=
      (hP 0).int.mul_bdd ((measurable_cvF k _ fun i => hP i.succ).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable (c := M)
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (n1 _)]
          exact l1 _)
    simp_rw [← ENNReal.ofReal_mul ((hP 0).nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t =>
      mul_nonneg ((hP 0).nonneg t) (n1 _))]
    rfl

variable {m : ℕ}

lemma prod_embedT (h : Fin (m + 1) → E → ℝ) (s : E) (y : Fin m → E) :
    ∏ j, h j (Large.embedT m s y j) =
      (∏ l, h (Fin.castSucc l) (y l)) * h (Fin.last m) (s - ∑ i, y i) := by
  rw [Fin.prod_univ_castSucc]
  simp [Large.embedT]

lemma measurable_prod_ofReal {n : ℕ} {h : Fin n → E → ℝ} (hm : ∀ i, Measurable (h i)) :
    Measurable fun x : Fin n → E => ENNReal.ofReal (∏ j, h j (x j)) :=
  ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
    (hm i).comp (measurable_pi_apply i))

/-- The normalising constant: `∫ ∏ h_j(x_j) dλ(x) = f(s)`. -/
lemma lintegral_lebT {M : ℝ} (h : Fin (m + 1) → E → ℝ) (hP : ∀ i, PDg M (h i)) (s : E) :
    ∫⁻ x, ENNReal.ofReal (∏ j, h j (x j)) ∂(Large.lebT m s) = ENNReal.ofReal (cvF m h s) := by
  rw [Large.lebT, lintegral_map (measurable_prod_ofReal fun i => (hP i).meas)
    (Large.measurable_embedT m s)]
  simp_rw [prod_embedT]
  simp_rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hP _).nonneg _)]
  exact lintegral_prod_eq_cvF m h hP s

lemma integral_lebT {M : ℝ} (h : Fin (m + 1) → E → ℝ) (hP : ∀ i, PDg M (h i)) (s : E) :
    ∫ x, ∏ j, h j (x j) ∂(Large.lebT m s) = cvF m h s := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
    Finset.prod_nonneg fun i _ => (hP i).nonneg _)
    (Finset.measurable_prod _ fun i _ => (hP i).meas.comp (measurable_pi_apply i)
      ).aestronglyMeasurable, lintegral_lebT h hP s,
    ENNReal.toReal_ofReal ((cvF_props m h hP).2.1 s)]

lemma finRotate_castSucc' (k : ℕ) (l : Fin (k + 1)) :
    finRotate (k + 2) (Fin.castSucc l) = l.succ :=
  Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last l).ne]; simp)

lemma lintegral_insertNth (k : ℕ) (i : Fin (k + 1)) (F : (Fin (k + 1) → E) → ENNReal)
    (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ z : E, ∫⁻ x' : Fin k → E, F (Fin.insertNth i z x') := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => E) i).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ => E) i).symm p))
      (hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
  rfl

/-- The marginal integrals of the conditioned product on `𝒯` (formula `jl:eq:marg`, before
normalisation): `∫_𝒯 1_A(x_j) ∏ h_i(x_i) dλ = ∫_A h_j(z) f_{-j}(s - z) dz`. -/
lemma lintegral_marg {M : ℝ} (k : ℕ) (h : Fin (k + 3) → E → ℝ) (hP : ∀ i, PDg M (h i)) (s : E)
    (j : Fin (k + 3)) {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator 1 (x j) * ENNReal.ofReal (∏ i, h i (x i)) ∂(Large.lebT (k + 2) s) =
      ∫⁻ z, A.indicator 1 z * ENNReal.ofReal
        (h j z * cvF (k + 1) (fun i => h (j.succAbove i)) (s - z)) := by
  have hm := fun i => (hP i).meas
  have hind : Measurable fun x : Fin (k + 3) → E => A.indicator (1 : E → ENNReal) (x j) :=
    (measurable_one.indicator hA).comp (measurable_pi_apply j)
  rw [Large.lebT, lintegral_map (f := fun x => A.indicator (1 : E → ENNReal) (x j) *
    ENNReal.ofReal (∏ i, h i (x i))) (hind.mul (measurable_prod_ofReal hm))
    (Large.measurable_embedT _ s)]
  simp_rw [prod_embedT]
  have hsum : Measurable fun y : Fin (k + 2) → E => ∑ i, y i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  refine Fin.lastCases ?_ (fun i => ?_) j
  · -- the last coordinate
    simp only [Large.embedT, Fin.snoc_last]
    have hF : Measurable fun y : Fin (k + 2) → E => A.indicator (1 : E → ENNReal) (s - ∑ i, y i) *
        ENNReal.ofReal ((∏ l, h (Fin.castSucc l) (y l)) * h (Fin.last (k + 2)) (s - ∑ i, y i)) :=
      ((measurable_one.indicator hA).comp (measurable_const.sub hsum)).mul
        (ENNReal.measurable_ofReal.comp ((Finset.measurable_prod _ fun i _ =>
          (hm _).comp (measurable_pi_apply i)).mul ((hm _).comp (measurable_const.sub hsum))))
    refine (lintegral_fin_succ' (k + 1) _ hF).trans ?_
    rw [lintegral_lintegral_swap (by exact (hF.comp (measurable_cons _)).aemeasurable)]
    set f' : Fin (k + 2) → E → ℝ := fun l => h (Fin.castSucc (finRotate (k + 2) l)) with hf'
    have hf'P : ∀ l, PDg M (f' l) := fun l => hP _
    have e1 : ∀ x' : Fin (k + 1) → E, ∫⁻ z, A.indicator (1 : E → ENNReal)
          (s - ∑ i, (Fin.cons z x' : Fin (k + 2) → E) i) * ENNReal.ofReal
          ((∏ l, h (Fin.castSucc l) ((Fin.cons z x' : Fin (k + 2) → E) l)) *
            h (Fin.last (k + 2)) (s - ∑ i, (Fin.cons z x' : Fin (k + 2) → E) i)) =
        ∫⁻ w, A.indicator 1 w * ENNReal.ofReal (h (Fin.last (k + 2)) w) *
          (ENNReal.ofReal (∏ l, f' (Fin.castSucc l) (x' l)) *
            ENNReal.ofReal (f' (Fin.last (k + 1)) ((s - w) - ∑ i, x' i))) := by
      intro x'
      rw [← lintegral_sub_left_eq_self _ (s - ∑ i, x' i)]
      congr 1; funext w
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      set c := ∑ i, x' i
      simp only [hf', finRotate_castSucc', finRotate_last, Fin.castSucc_zero]
      have e : s - (s - c - w + c) = w := by abel
      rw [e, show s - c - w = s - w - c by abel]
      rw [ENNReal.ofReal_mul (mul_nonneg ((hP _).nonneg _)
          (Finset.prod_nonneg fun i _ => (hP _).nonneg _)),
        ENNReal.ofReal_mul ((hP _).nonneg _)]
      ring
    simp_rw [e1]
    rw [lintegral_lintegral_swap]
    · congr 1; funext w
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by
          by_cases hw : w ∈ A <;> simp [hw]) ENNReal.ofReal_ne_top),
        lintegral_prod_eq_cvF (k + 1) f' hf'P (s - w), mul_assoc,
        ← ENNReal.ofReal_mul ((hP _).nonneg w)]
      congr 3
      have := cvF_perm k (fun l => h (Fin.castSucc l)) (fun l => hP _) (finRotate (k + 2)) (s - w)
      rw [hf', this, Fin.succAbove_last]
    · refine Measurable.aemeasurable ?_
      refine (((measurable_one.indicator hA).comp measurable_snd).mul
        (ENNReal.measurable_ofReal.comp ((hm _).comp measurable_snd))).mul ?_
      refine (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
        (hm _).comp ((measurable_pi_apply _).comp measurable_fst))).mul
        (ENNReal.measurable_ofReal.comp ((hm _).comp ((measurable_const.sub measurable_snd).sub
          (Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).comp measurable_fst))))
  · -- the coordinate `i < k + 2`
    simp only [Large.embedT, Fin.snoc_castSucc]
    have hF : Measurable fun y : Fin (k + 2) → E => A.indicator (1 : E → ENNReal) (y i) *
        ENNReal.ofReal ((∏ l, h (Fin.castSucc l) (y l)) * h (Fin.last (k + 2)) (s - ∑ i, y i)) :=
      ((measurable_one.indicator hA).comp (measurable_pi_apply i)).mul
        (ENNReal.measurable_ofReal.comp ((Finset.measurable_prod _ fun i _ =>
          (hm _).comp (measurable_pi_apply i)).mul ((hm _).comp (measurable_const.sub hsum))))
    refine (lintegral_insertNth (k + 1) i _ hF).trans ?_
    congr 1; funext z
    set f : Fin (k + 2) → E → ℝ := fun l => h ((Fin.castSucc i).succAbove l) with hf
    have e : ∀ x' : Fin (k + 1) → E, A.indicator (1 : E → ENNReal)
          (Fin.insertNth (α := fun _ => E) i z x' i) * ENNReal.ofReal
          ((∏ l, h (Fin.castSucc l) (Fin.insertNth (α := fun _ => E) i z x' l)) *
            h (Fin.last (k + 2)) (s - ∑ l, Fin.insertNth (α := fun _ => E) i z x' l)) =
        A.indicator 1 z * ENNReal.ofReal (h (Fin.castSucc i) z) *
          (ENNReal.ofReal (∏ l, f (Fin.castSucc l) (x' l)) *
            ENNReal.ofReal (f (Fin.last (k + 1)) ((s - z) - ∑ l, x' l))) := by
      intro x'
      rw [Fin.prod_univ_succAbove _ i, Fin.sum_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hf,
        Fin.castSucc_succAbove_castSucc]
      have hl : (Fin.castSucc i).succAbove (Fin.last (k + 1)) = Fin.last (k + 2) := by
        rw [Fin.succAbove_castSucc_of_le _ _ (Fin.le_last _), Fin.succ_last]
      rw [hl, ENNReal.ofReal_mul (mul_nonneg ((hP _).nonneg _)
          (Finset.prod_nonneg fun i _ => (hP _).nonneg _)),
        ENNReal.ofReal_mul ((hP _).nonneg _), sub_sub]
      ring
    simp_rw [e]
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by
        by_cases hw : z ∈ A <;> simp [hw]) ENNReal.ofReal_ne_top),
      lintegral_prod_eq_cvF (k + 1) f (fun l => hP _) (s - z), mul_assoc,
      ← ENNReal.ofReal_mul ((hP _).nonneg z)]

lemma setLIntegral_preimage_eq' {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → E)
    {A : Set E} (hS : MeasurableSet (φ ⁻¹' A)) (F : α → ENNReal) :
    ∫⁻ x in φ ⁻¹' A, F x ∂μ = ∫⁻ x, A.indicator 1 (φ x) * F x ∂μ := by
  rw [← lintegral_indicator hS]
  congr 1; funext x
  by_cases hx : φ x ∈ A
  · simp [hx]
  · simp [hx]

lemma setLIntegral_ind {A : Set E} (hA : MeasurableSet A) (F : E → ENNReal) :
    ∫⁻ x in A, F x = ∫⁻ x, A.indicator 1 x * F x :=
  setLIntegral_preimage_eq' volume id hA F

lemma condProdJ_eq {M : ℝ} (h : Fin (m + 1) → E → ℝ) (hP : ∀ i, PDg M (h i)) (s : E)
    (x : Fin (m + 1) → E) :
    Large.condProdJ (Large.lebT m s) h x = (∏ i, h i (x i)) / cvF m h s := by
  rw [Large.condProdJ, integral_lebT h hP s]

/-- The conditioned product is a probability measure. -/
lemma condMeas_prob {M : ℝ} (h : Fin (m + 1) → E → ℝ) (hP : ∀ i, PDg M (h i)) (s : E)
    (hZ : 0 < cvF m h s) : IsProbabilityMeasure (Large.condMeas (Large.lebT m s) h) := by
  constructor
  rw [Large.condMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [condProdJ_eq h hP s, ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv]
  rw [lintegral_mul_const _ (measurable_prod_ofReal fun i => (hP i).meas), lintegral_lebT h hP s,
    ENNReal.mul_inv_cancel (by simpa using hZ) ENNReal.ofReal_ne_top]

/-- **The marginal formula** (`jl:eq:marg`): the `j`-th marginal of the conditioned product on
`𝒯` has the density `p ↦ h_j(p) f_{-j}(s - p) / f(s)`. -/
lemma condMeas_marg {M : ℝ} (k : ℕ) (h : Fin (k + 3) → E → ℝ) (hP : ∀ i, PDg M (h i)) (s : E)
    (hZ : 0 < cvF (k + 2) h s) (j : Fin (k + 3)) :
    (Large.condMeas (Large.lebT (k + 2) s) h).map (fun x => x j) = volume.withDensity
      (fun z => ENNReal.ofReal (h j z * cvF (k + 1) (fun i => h (j.succAbove i)) (s - z) /
        cvF (k + 2) h s)) := by
  ext A hA
  have hS : MeasurableSet ((fun x : Fin (k + 3) → E => x j) ⁻¹' A) := measurable_pi_apply j hA
  rw [Measure.map_apply (measurable_pi_apply j) hA, Large.condMeas, withDensity_apply _ hS,
    withDensity_apply _ hA, setLIntegral_preimage_eq' _ _ hS, setLIntegral_ind hA]
  simp_rw [condProdJ_eq h hP s, ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, ← mul_assoc]
  have hcv := measurable_cvF (k + 1) (fun i => h (j.succAbove i)) (fun i => hP _)
  have hne : (ENNReal.ofReal (cvF (k + 2) h s))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simpa using hZ)
  rw [lintegral_mul_const' _ _ hne, lintegral_mul_const' _ _ hne, lintegral_marg k h hP s j hA]

end Marginal

section Compare

/-- Multiplicative comparison of convolutions. -/
lemma cvF_le_mul {M a : ℝ} (ha : 0 ≤ a) : ∀ (k : ℕ) (h h' : Fin (k + 1) → E → ℝ),
    (∀ i, PDg M (h i)) → (∀ i, PDg M (h' i)) → (∀ i y, h i y ≤ a * h' i y) →
    ∀ y, cvF k h y ≤ a ^ (k + 1) * cvF k h' y
  | 0, h, h', _, _, hle, y => by simpa [cvF] using hle 0 y
  | k + 1, h, h', hP, hP', hle, y => by
    show cv (h 0) (cvF k (Fin.tail h)) y ≤ a ^ (k + 2) * cv (h' 0) (cvF k (Fin.tail h')) y
    have IH := cvF_le_mul ha k (Fin.tail h) (Fin.tail h') (fun i => hP _) (fun i => hP' _)
      (fun i => hle _)
    obtain ⟨_, n1, _, _⟩ := cvF_props k (Fin.tail h) fun i => hP i.succ
    obtain ⟨_, n1', l1', _⟩ := cvF_props k (Fin.tail h') fun i => hP' i.succ
    rw [cv, cv, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg ((hP 0).nonneg t)
      (n1 _)) ?_ (Eventually.of_forall fun t => ?_)
    · refine Integrable.const_mul ?_ _
      exact (hP' 0).int.mul_bdd ((measurable_cvF k _ fun i => hP' i.succ).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable (c := M)
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (n1' _)]; exact l1' _)
    · dsimp only
      calc h 0 t * cvF k (Fin.tail h) (y - t) ≤ (a * h' 0 t) * (a ^ (k + 1) *
            cvF k (Fin.tail h') (y - t)) :=
            mul_le_mul (hle 0 t) (IH _) (n1 _) (mul_nonneg ha ((hP' 0).nonneg t))
        _ = _ := by ring

/-- Multiplicative comparison of tilts: `|u - u'| ≤ η` where `g ≠ 0` gives
`tiltD g u ≤ e^{2η} tiltD g u'`. -/
lemma tiltD_le {g u u' : E → ℝ} {η : ℝ} (hg0 : ∀ y, 0 ≤ g y)
    (hi : Integrable fun y => g y * exp (u y)) (hi' : Integrable fun y => g y * exp (u' y))
    (hpos : 0 < ∫ y, g y * exp (u' y)) (hη : ∀ y, g y ≠ 0 → |u y - u' y| ≤ η) (y : E) :
    Large.tiltD g u y ≤ exp (2 * η) * Large.tiltD g u' y := by
  have hnum : ∀ y, g y * exp (u y) ≤ exp η * (g y * exp (u' y)) := fun y => by
    by_cases hy : g y = 0
    · simp [hy]
    · have := (abs_le.1 (hη y hy)).2
      rw [← mul_assoc, mul_comm (exp η), mul_assoc, ← exp_add]
      exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) (hg0 y)
  have hden : ∀ y, exp (-η) * (g y * exp (u' y)) ≤ g y * exp (u y) := fun y => by
    by_cases hy : g y = 0
    · simp [hy]
    · have := (abs_le.1 (hη y hy)).1
      rw [← mul_assoc, mul_comm (exp (-η)), mul_assoc, ← exp_add]
      exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) (hg0 y)
  have hI : exp (-η) * ∫ y, g y * exp (u' y) ≤ ∫ y, g y * exp (u y) := by
    rw [← integral_const_mul]; exact integral_mono (hi'.const_mul _) hi hden
  have hIpos : 0 < ∫ y, g y * exp (u y) := lt_of_lt_of_le (by positivity) hI
  rw [Large.tiltD, Large.tiltD, div_le_iff₀ hIpos]
  set I' := ∫ y, g y * exp (u' y)
  set q := g y * exp (u' y) / I'
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (hg0 y) (exp_pos _).le) hpos.le
  have hX : g y * exp (u' y) = q * I' := by simp only [q]; field_simp
  have h2 : exp (2 * η) = exp η * exp η := by rw [← exp_add]; ring_nf
  have h3 : exp η * exp (-η) = 1 := by rw [← exp_add]; simp
  calc g y * exp (u y) ≤ exp η * (g y * exp (u' y)) := hnum y
    _ = (exp (2 * η) * q) * (exp (-η) * I') := by
        rw [hX, h2]; linear_combination (-(exp η * q * I')) * h3
    _ ≤ (exp (2 * η) * q) * ∫ y, g y * exp (u y) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

lemma abs_sub_le_of_ratio {a b η : ℝ} (hb : 0 ≤ b) (h1 : a ≤ exp (2 * η) * b)
    (h2 : b ≤ exp (2 * η) * a) : |a - b| ≤ (exp (2 * η) - 1) * b := by
  have hη : 0 ≤ exp (2 * η) - 1 ∨ b = 0 := by
    by_cases hb0 : b = 0
    · right; exact hb0
    · left
      have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have ha : 0 ≤ a := by
        by_contra hc; push Not at hc
        have := mul_neg_of_pos_of_neg (exp_pos (2 * η)) hc; linarith
      by_contra hc; push Not at hc
      have : exp (2 * η) < 1 := by linarith
      have h3 : exp (2 * η) * a ≤ a := mul_le_of_le_one_left ha this.le
      have h4 : exp (2 * η) * b < b := mul_lt_of_lt_one_left hb' this
      linarith
  rcases hη with hη | hb0
  · rw [abs_le]
    constructor
    · -- b - a ≤ (e - 1) b: from b ≤ e a, i.e. a ≥ b / e
      have he : 0 < exp (2 * η) := exp_pos _
      have : b / exp (2 * η) ≤ a := by rw [div_le_iff₀ he, mul_comm]; exact h2
      have h5 : b - b / exp (2 * η) ≤ (exp (2 * η) - 1) * b := by
        have : b - b / exp (2 * η) = (1 - exp (-(2 * η))) * b := by
          rw [exp_neg]; field_simp
        rw [this]
        refine mul_le_mul_of_nonneg_right ?_ hb
        have := add_one_le_exp (2 * η)
        have := add_one_le_exp (-(2 * η))
        nlinarith [exp_pos (2 * η), exp_pos (-(2 * η)), mul_self_nonneg (exp (2 * η) - 1),
          show exp (2 * η) * exp (-(2 * η)) = 1 by rw [← exp_add]; simp]
      linarith
    · linarith
  · subst hb0
    have : a ≤ 0 := by simpa using h1
    have : 0 ≤ a := by
      have := h2; nlinarith [exp_pos (2 * η)]
    have ha : a = 0 := by linarith
    simp [ha]

/-- Difference of means of two densities with comparable values. -/
lemma meanD_sub_le {h h' : E → ℝ} {K : Set E} {B c : ℝ} (hm : Measurable h)
    (hm' : Measurable h') (hi : Integrable h) (hi' : Integrable h') (h1 : ∫ y, h' y = 1)
    (hz : ∀ y ∉ K, h y = 0) (hz' : ∀ y ∉ K, h' y = 0) (hB : ∀ y ∈ K, ‖y‖ ≤ B)
    (hc : ∀ y, |h y - h' y| ≤ c * h' y) :
    ‖Large.meanD h - Large.meanD h'‖ ≤ c * B := by
  have hb : ∀ {f : E → ℝ}, Measurable f → Integrable f → (∀ y ∉ K, f y = 0) →
      Integrable fun y => f y • y := fun {f} hfm hfi hfz => by
    refine Integrable.mono' (hfi.norm.mul_const B) (hfm.smul measurable_id).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul]
    by_cases hy : y ∈ K
    · exact mul_le_mul_of_nonneg_left (hB y hy) (norm_nonneg _)
    · simp [hfz y hy]
  rw [Large.meanD, Large.meanD, ← integral_sub (hb hm hi hz) (hb hm' hi' hz')]
  calc ‖∫ y, (h y • y - h' y • y)‖ ≤ ∫ y, c * B * h' y := by
        refine norm_integral_le_of_norm_le ((hi'.const_mul _)) (Eventually.of_forall fun y => ?_)
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        by_cases hy : y ∈ K
        · calc |h y - h' y| * ‖y‖ ≤ (c * h' y) * B :=
                mul_le_mul (hc y) (hB y hy) (norm_nonneg _)
                  ((abs_nonneg _).trans (hc y))
            _ = _ := by ring
        · simp [hz y hy, hz' y hy]
    _ = c * B := by rw [integral_const_mul, h1, mul_one]

end Compare

section Key

/-- **The key estimate** (Lipschitz bound of Theorem 113): for `f = a * T` with `a` a density
whose support lies within `R` of its mean `μa` and has the `L¹` modulus `D`, and `T` with
`|T(t)/T(z0) - 1| ≤ δ ≤ 1/2` on the ball of radius `2R` about `z0`:
`f ≥ (1 - δ) T(z0)` and `|log f(y) - log f(y')| ≤ 2 D δ |y - y'|` on the ball of radius `R`
about `μa + z0`. -/
lemma key_log {a T : E → ℝ} {R D δ MT : ℝ} {z0 μa : E} (ha0 : ∀ y, 0 ≤ a y)
    (hai : Integrable a) (ha1 : ∫ y, a y = 1) (hKa : ∀ y, a y ≠ 0 → ‖y - μa‖ ≤ R)
    (hD : ∀ y y', ∫ t, |a (y - t) - a (y' - t)| ≤ D * ‖y - y'‖)
    (hTm : Measurable T) (hT0 : ∀ t, 0 ≤ T t) (hTb : ∀ t, T t ≤ MT) (hTz : 0 < T z0)
    (hδ : ∀ t, ‖t - z0‖ ≤ 2 * R → |T t / T z0 - 1| ≤ δ) (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (hD0 : 0 ≤ D) :
    (∀ y, ‖y - μa - z0‖ ≤ R → (1 - δ) * T z0 ≤ cv a T y) ∧
    ∀ y y', ‖y - μa - z0‖ ≤ R → ‖y' - μa - z0‖ ≤ R →
      |log (cv a T y) - log (cv a T y')| ≤ 2 * D * δ * ‖y - y'‖ := by
  have hcv : ∀ y, cv a T y = ∫ t, a (y - t) * T t := fun y => by
    rw [cv, ← integral_sub_left_eq_self _ volume y]
    congr 1; funext t; rw [sub_sub_cancel]
  have hTd : ∀ y t, ‖y - μa - z0‖ ≤ R → a (y - t) ≠ 0 → |T t - T z0| ≤ δ * T z0 := by
    intro y t hy ha
    have h1 := hKa _ ha
    have : ‖t - z0‖ ≤ 2 * R := by
      have e : t - z0 = (y - μa - z0) - (y - t - μa) := by abel
      rw [e]; linarith [norm_sub_le (y - μa - z0) (y - t - μa)]
    have h2 := hδ t this
    rw [div_sub_one hTz.ne', abs_div, abs_of_pos hTz, div_le_iff₀ hTz] at h2
    exact h2
  have hTi : ∀ y, Integrable fun t => a (y - t) * T t := fun y =>
    (hai.comp_sub_left y).mul_bdd hTm.aestronglyMeasurable (c := MT)
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hT0 t)]; exact hTb t)
  have ha1' : ∀ y, ∫ t, a (y - t) = 1 := fun y => by
    rw [integral_sub_left_eq_self a volume y, ha1]
  have hlow : ∀ y, ‖y - μa - z0‖ ≤ R → (1 - δ) * T z0 ≤ cv a T y := by
    intro y hy
    rw [hcv]
    calc (1 - δ) * T z0 = ∫ t, a (y - t) * ((1 - δ) * T z0) := by
          rw [integral_mul_const, ha1' y, one_mul]
      _ ≤ _ := by
          refine integral_mono ((hai.comp_sub_left y).mul_const _) (hTi y) fun t => ?_
          dsimp only
          by_cases ht : a (y - t) = 0
          · simp [ht]
          · have := hTd y t hy ht
            exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 this).1]) (ha0 _)
  refine ⟨hlow, fun y y' hy hy' => ?_⟩
  have hδ1 : 1 / 2 ≤ 1 - δ := by linarith
  have hf : 0 < (1 - δ) * T z0 := mul_pos (by linarith) hTz
  have hfy := hlow y hy
  have hfy' := hlow y' hy'
  have hdiff : |cv a T y - cv a T y'| ≤ D * ‖y - y'‖ * (δ * T z0) := by
    rw [hcv, hcv, ← integral_sub (hTi y) (hTi y')]
    have e : ∀ t, a (y - t) * T t - a (y' - t) * T t =
        (a (y - t) - a (y' - t)) * (T t - T z0) + (a (y - t) - a (y' - t)) * T z0 := fun t => by
      ring
    have hi1 : Integrable fun t => (a (y - t) - a (y' - t)) * T z0 :=
      ((hai.comp_sub_left y).sub (hai.comp_sub_left y')).mul_const _
    have hi2 : Integrable fun t => (a (y - t) - a (y' - t)) * (T t - T z0) := by
      have := ((hTi y).sub (hTi y')).sub hi1
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.sub_apply]; ring
    simp_rw [e]
    rw [integral_add hi2 hi1, integral_mul_const,
      integral_sub (hai.comp_sub_left y) (hai.comp_sub_left y'), ha1', ha1', sub_self, zero_mul,
      add_zero, ← Real.norm_eq_abs]
    calc ‖∫ t, (a (y - t) - a (y' - t)) * (T t - T z0)‖
        ≤ ∫ t, |a (y - t) - a (y' - t)| * (δ * T z0) := by
          refine norm_integral_le_of_norm_le
            (((hai.comp_sub_left y).sub (hai.comp_sub_left y')).abs.mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [Real.norm_eq_abs, abs_mul]
          by_cases h12 : a (y - t) = 0 ∧ a (y' - t) = 0
          · simp [h12.1, h12.2]
          · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            by_cases h1 : a (y - t) = 0
            · exact hTd y' t hy' (fun h2 => h12 ⟨h1, h2⟩)
            · exact hTd y t hy h1
      _ = (∫ t, |a (y - t) - a (y' - t)|) * (δ * T z0) := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hD y y') (by positivity)
  have hmin : (1 - δ) * T z0 ≤ min (cv a T y) (cv a T y') := le_min hfy hfy'
  calc |log (cv a T y) - log (cv a T y')|
      ≤ |cv a T y - cv a T y'| / min (cv a T y) (cv a T y') :=
        LLT.abs_log_sub_log_le (hf.trans_le hfy) (hf.trans_le hfy')
    _ ≤ D * ‖y - y'‖ * (δ * T z0) / ((1 - δ) * T z0) :=
        div_le_div₀ (by positivity) hdiff hf hmin
    _ ≤ 2 * D * δ * ‖y - y'‖ := by
        rw [div_le_iff₀ hf]
        have : 0 ≤ D * ‖y - y'‖ * δ * T z0 := by positivity
        nlinarith

end Key

section Tilt

variable {A L r R : ℝ} {K : Set E} {g : E → ℝ}

lemma tiltD_add_const (g u : E → ℝ) (a : ℝ) :
    Large.tiltD g (fun y => u y + a) = Large.tiltD g u := by
  funext y
  simp only [Large.tiltD, exp_add]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  by_cases h : ∫ z, g z * exp (u z) = 0
  · simp [h]
  · field_simp

lemma GH.integrable {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) : Integrable h :=
  Integrable.of_integral_ne_zero (by rw [hH.int]; exact one_ne_zero)

lemma GH.volPos {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) (hr : 0 < r) :
    0 < volume.real K := by
  have := (hH.toInH).volPos hr.le
  rw [real_eq]; exact mul_pos cH_pos this

lemma GH.nonneg {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) (hr : 0 < r) (y : E) :
    0 ≤ h y := by
  have := (hH.toInH).nonneg hr.le y
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using this) cH_pos

lemma vball_pos {r : ℝ} (hr : 0 < r) : 0 < volume.real (Metric.closedBall (0 : E) r) :=
  ENNReal.toReal_pos (Metric.measure_closedBall_pos volume 0 hr).ne'
    measure_closedBall_lt_top.ne

lemma GH.vol_ge {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) :
    volume.real (Metric.closedBall (0 : E) r) ≤ volume.real K := by
  obtain ⟨b, hb⟩ := hH.ball
  rw [measureReal_def, measureReal_def, ← Measure.addHaar_closedBall_center volume b]
  exact ENNReal.toReal_mono hH.compact.measure_lt_top.ne (measure_mono hb)

lemma GH.le {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) (hr : 0 < r) (y : E) :
    h y ≤ exp A / volume.real (Metric.closedBall (0 : E) r) := by
  have hv := vball_pos (E := E) hr
  by_cases hy : y ∈ K
  · rw [le_div_iff₀ hv]
    calc h y * volume.real (Metric.closedBall (0 : E) r) ≤ h y * volume.real K :=
          mul_le_mul_of_nonneg_left hH.vol_ge (hH.nonneg hr y)
      _ ≤ exp A := by rw [mul_comm]; exact hH.up y hy
  · rw [hH.zero y hy]; positivity

lemma GH.pdg {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) (hr : 0 < r) :
    PDg (exp A / volume.real (Metric.closedBall (0 : E) r)) h :=
  ⟨hH.integrable, hH.meas, hH.nonneg hr, hH.le hr, hH.int⟩

lemma GH.norm_sub_mean_le {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h)
    (hr : 0 < r) {y : E} (hy : y ∈ K) : ‖y - Large.meanD h‖ ≤ R := by
  rw [meanD_eq]
  exact (hH.toInH).norm_sub_mean_le hr.le hy

lemma GH.mono {A A' r R : ℝ} {K : Set E} {h : E → ℝ} (hH : GH A r R K h) (hA : A ≤ A') :
    GH A' r R K h :=
  ⟨hH.compact, hH.convex, hH.ball, hH.diam, hH.meas, hH.zero, hH.int,
    fun y hy => (exp_le_exp.2 (by linarith)).trans (hH.low y hy),
    fun y hy => (hH.up y hy).trans (exp_le_exp.2 hA)⟩

lemma ig_integrable_mul_exp (hG : Large.InG A L r R K g) {u : E → ℝ} (hu : Measurable u)
    {c : ℝ} (hc : ∀ y ∈ K, |u y| ≤ c) : Integrable fun y => g y * exp (u y) := by
  refine Integrable.mono' (hG.integrable.mul_const (exp c))
    (hG.meas.mul (continuous_exp.measurable.comp hu)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ K
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hG.gpos hy), abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (abs_le.1 (hc y hy)).2) (hG.gpos hy).le
  · simp [hG.zero y hy]

lemma ig_Z_bounds (hG : Large.InG A L r R K g) {u : E → ℝ} (hu : Measurable u)
    {c : ℝ} (hc : ∀ y ∈ K, |u y| ≤ c) :
    exp (-c) ≤ ∫ y, g y * exp (u y) ∧ ∫ y, g y * exp (u y) ≤ exp c := by
  have hi := ig_integrable_mul_exp hG hu hc
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    by_cases hy : y ∈ K
    · exact (hG.gpos hy).le
    · rw [hG.zero y hy]
  constructor
  · calc exp (-c) = ∫ y, g y * exp (-c) := by rw [integral_mul_const, hG.int, one_mul]
      _ ≤ _ := integral_mono (hG.integrable.mul_const _) hi fun y => by
          by_cases hy : y ∈ K
          · exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by
              linarith [(abs_le.1 (hc y hy)).1])) (hg0 y)
          · simp [hG.zero y hy]
  · calc ∫ y, g y * exp (u y) ≤ ∫ y, g y * exp c := integral_mono hi
          (hG.integrable.mul_const _) fun y => by
          by_cases hy : y ∈ K
          · exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (abs_le.1 (hc y hy)).2) (hg0 y)
          · simp [hG.zero y hy]
      _ = exp c := by rw [integral_mul_const, hG.int, one_mul]

/-- A tilt `g e^u / ∫ g e^u` with `|u| ≤ c` on `K` lies in `𝓗(A + 2c, r, R)`. -/
lemma ig_tilt_GH (hG : Large.InG A L r R K g) {u : E → ℝ} (hu : Measurable u)
    {c : ℝ} (hc : ∀ y ∈ K, |u y| ≤ c) : GH (A + 2 * c) r R K (Large.tiltD g u) := by
  obtain ⟨hZ1, hZ2⟩ := ig_Z_bounds hG hu hc
  have hZ : 0 < ∫ y, g y * exp (u y) := (exp_pos _).trans_le hZ1
  refine ⟨hG.compact, hG.convex, hG.ball, hG.diam,
    (hG.meas.mul (continuous_exp.measurable.comp hu)).div_const _,
    fun y hy => by simp [Large.tiltD, hG.zero y hy], ?_, fun y hy => ?_, fun y hy => ?_⟩
  · simp only [Large.tiltD]; rw [integral_div, div_self hZ.ne']
  · have h1 := hG.low y hy
    have h2 : -c ≤ u y := (abs_le.1 (hc y hy)).1
    rw [Large.tiltD, ← mul_div_assoc, le_div_iff₀ hZ, ← mul_assoc]
    calc exp (-(A + 2 * c)) * ∫ y, g y * exp (u y) ≤ exp (-(A + 2 * c)) * exp c :=
          mul_le_mul_of_nonneg_left hZ2 (exp_pos _).le
      _ = exp (-A) * exp (-c) := by rw [← exp_add, ← exp_add]; ring_nf
      _ ≤ volume.real K * g y * exp (u y) :=
          mul_le_mul h1 (exp_le_exp.2 h2) (exp_pos _).le (by
            exact mul_nonneg measureReal_nonneg (hG.gpos hy).le)
  · have h1 := hG.up y hy
    have h2 : u y ≤ c := (abs_le.1 (hc y hy)).2
    rw [Large.tiltD, ← mul_div_assoc, div_le_iff₀ hZ, ← mul_assoc]
    calc volume.real K * g y * exp (u y) ≤ exp A * exp c :=
          mul_le_mul h1 (exp_le_exp.2 h2) (exp_pos _).le (exp_pos _).le
      _ = exp (A + 2 * c) * exp (-c) := by rw [← exp_add, ← exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ1 (exp_pos _).le

lemma abs_sub_le_max_mul_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| ≤ max a b * |log a - log b| := by
  wlog hab : b ≤ a generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    rwa [abs_sub_comm, max_comm, abs_sub_comm (log b)] at this
  rw [max_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab),
    abs_of_nonneg (sub_nonneg.2 (log_le_log hb hab))]
  have := log_le_sub_one_of_pos (div_pos hb ha)
  rw [log_div hb.ne' ha.ne'] at this
  have e : a * (b / a - 1) = b - a := by field_simp
  nlinarith

/-- Lipschitz bound for a tilt on `K`. -/
lemma ig_tilt_lip (hG : Large.InG A L r R K g) {u : E → ℝ} (hu : Measurable u)
    {c Lu : ℝ} (hc : ∀ y ∈ K, |u y| ≤ c) (hLu : ∀ x ∈ K, ∀ y ∈ K, |u x - u y| ≤ Lu * dist x y)
    (_hr : 0 < r) (x : E) (hx : x ∈ K) (y : E) (hy : y ∈ K) :
    |Large.tiltD g u x - Large.tiltD g u y| ≤
      exp (A + 2 * c) / volume.real K * (L + Lu) * ‖x - y‖ := by
  have hH := ig_tilt_GH hG hu hc
  have hv := hG.volPos
  obtain ⟨hZ1, -⟩ := ig_Z_bounds hG hu hc
  have hZ : 0 < ∫ y, g y * exp (u y) := (exp_pos _).trans_le hZ1
  have hpos : ∀ z ∈ K, 0 < Large.tiltD g u z := fun z hz =>
    div_pos (mul_pos (hG.gpos hz) (exp_pos _)) hZ
  have hup : ∀ z ∈ K, Large.tiltD g u z ≤ exp (A + 2 * c) / volume.real K := fun z hz => by
    rw [le_div_iff₀' hv]; exact hH.up z hz
  have hlog : |log (Large.tiltD g u x) - log (Large.tiltD g u y)| ≤ (L + Lu) * ‖x - y‖ := by
    simp only [Large.tiltD]
    rw [log_div (mul_pos (hG.gpos hx) (exp_pos _)).ne' hZ.ne',
      log_div (mul_pos (hG.gpos hy) (exp_pos _)).ne' hZ.ne',
      log_mul (hG.gpos hx).ne' (exp_pos _).ne', log_mul (hG.gpos hy).ne' (exp_pos _).ne',
      log_exp, log_exp]
    have h1 := hG.lip x hx y hy
    have h2 := hLu x hx y hy
    rw [dist_eq_norm] at h1 h2
    calc _ = |(log (g x) - log (g y)) + (u x - u y)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  calc _ ≤ max (Large.tiltD g u x) (Large.tiltD g u y) *
        |log (Large.tiltD g u x) - log (Large.tiltD g u y)| :=
        abs_sub_le_max_mul_log (hpos x hx) (hpos y hy)
    _ ≤ exp (A + 2 * c) / volume.real K * ((L + Lu) * ‖x - y‖) :=
        mul_le_mul (max_le (hup x hx) (hup y hy)) hlog (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The `L¹` modulus of a tilt. -/
lemma ig_tilt_l1 (hG : Large.InG A L r R K g) {u : E → ℝ} (hu : Measurable u)
    {c Lu : ℝ} (hc : ∀ y ∈ K, |u y| ≤ c) (hLu : ∀ x ∈ K, ∀ y ∈ K, |u x - u y| ≤ Lu * dist x y)
    (hr : 0 < r) (hL : 0 ≤ L) (hLu0 : 0 ≤ Lu) (y y' : E) :
    ∫ z, |Large.tiltD g u (y - z) - Large.tiltD g u (y' - z)| ≤
      exp (A + 2 * c) * (L + Lu + 2 * Module.finrank ℝ E / r) * ‖y - y'‖ := by
  have hH := ig_tilt_GH hG hu hc
  have hv := hG.volPos
  obtain ⟨b, hb⟩ := hG.ball
  have H := l1_modulus_g hG.compact.isClosed.measurableSet hG.convex hr hb
    hG.compact.measure_lt_top.ne (G := exp (A + 2 * c) / volume.real K)
    (L := exp (A + 2 * c) / volume.real K * (L + Lu)) (by positivity) (by positivity)
    hH.zero (fun x hx => by
      rw [abs_of_nonneg (hH.nonneg hr x), le_div_iff₀' hv]; exact hH.up x hx)
    (ig_tilt_lip hG hu hc hLu hr) y y'
  refine H.trans (le_of_eq ?_)
  field_simp

end Tilt

section Setup

open Classical

variable {A L r R : ℝ} {k : ℕ}

variable (E) in
/-- `r_A = 2 e^{-A} r / (d + 1)` of Lemma 111(a). -/
def rA (A r : ℝ) : ℝ := 2 * exp (-A) * r / (Module.finrank ℝ E + 1)

variable (E) in
/-- The bound `V` of Lemma 111(b) for `A' = A + 2`. -/
def VB (A r R : ℝ) : ℝ := Large.constV' (E := E) R (rA E A r) (A + 2)

variable (E) in
/-- `A₂ = A + 2 (1 + V R)`. -/
def A2 (A r R : ℝ) : ℝ := A + 2 * (1 + VB E A r R * R)

/-- The set `𝒟` of corrections. -/
def Dset (K : Fin (k + 4) → Set E) : Set (Fin (k + 4) × E → ℝ) :=
  {ψ | (∀ j y, y ∉ K j → ψ (j, y) = 0) ∧ (∀ j y, |ψ (j, y)| ≤ 1) ∧
    ∀ j, ∀ x ∈ K j, ∀ y ∈ K j, |ψ (j, x) - ψ (j, y)| ≤ dist x y}

/-- The exponent `ψ_j + ⟪v, · - m_j⟫`. -/
def uF (g : Fin (k + 4) → E → ℝ) (ψ : Fin (k + 4) × E → ℝ) (v : E) (j : Fin (k + 4)) (y : E) :
    ℝ := ψ (j, y) + ⟪v, y - Large.meanD (g j)⟫

/-- The densities `h_j = g_j e^{ψ_j + ⟪v, ·⟫} / ∫ ⋯`. -/
def hTv (g : Fin (k + 4) → E → ℝ) (ψ : Fin (k + 4) × E → ℝ) (v : E) (j : Fin (k + 4)) : E → ℝ :=
  Large.tiltD (g j) (uF g ψ v j)

/-- The sum of the means of the `h_j`. -/
def Gm (g : Fin (k + 4) → E → ℝ) (ψ : Fin (k + 4) × E → ℝ) (v : E) : E :=
  ∑ j, Large.meanD (hTv g ψ v j)

/-- `s = ∑ m_{g_j}`. -/
def sD (g : Fin (k + 4) → E → ℝ) : E := ∑ j, Large.meanD (g j)

/-- The tilt `v` of Lemma 111(b). -/
def vT (g : Fin (k + 4) → E → ℝ) (ψ : Fin (k + 4) × E → ℝ) : E :=
  if h : ∃ v, Gm g ψ v = sD g then h.choose else 0

/-- `f_{-j}`: the convolution of the `h_i`, `i ≠ j`. -/
def fJ (g : Fin (k + 4) → E → ℝ) (ψ : Fin (k + 4) × E → ℝ) (j : Fin (k + 4)) : E → ℝ :=
  cvF (k + 2) (fun i => hTv g ψ (vT g ψ) (j.succAbove i))

/-- The map `Φ`. -/
def Phi (K : Fin (k + 4) → Set E) (g : Fin (k + 4) → E → ℝ) (ψ : Fin (k + 4) × E → ℝ) :
    Fin (k + 4) × E → ℝ := fun q =>
  if q.2 ∈ K q.1 then -(log (fJ g ψ q.1 (sD g - q.2)) -
    log (fJ g ψ q.1 (sD g - Large.meanD (g q.1)))) else 0

variable {K : Fin (k + 4) → Set E} {g : Fin (k + 4) → E → ℝ}

lemma Dset_meas {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (hK : ∀ j, IsClosed (K j))
    (j : Fin (k + 4)) : Measurable fun y => ψ (j, y) := by
  have hL : LipschitzOnWith 1 (fun y => ψ (j, y)) (K j) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [Real.dist_eq]; simpa using hψ.2.2 j x hx y hy
  obtain ⟨f, hf, hEq⟩ := hL.extend_real
  have e : (fun y => ψ (j, y)) = (K j).indicator f := by
    funext y
    by_cases hy : y ∈ K j
    · rw [Set.indicator_of_mem hy]; exact hEq hy
    · rw [Set.indicator_of_notMem hy]; exact hψ.1 j y hy
  rw [e]
  exact hf.continuous.measurable.indicator (hK j).measurableSet

lemma meanD_mem (hG : ∀ j, Large.InG A L r R (K j) (g j)) (j : Fin (k + 4)) :
    Large.meanD (g j) = ∫ y in K j, g j y • y := by
  rw [Large.meanD, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
    simp [(hG j).zero y hy]]

lemma ball_mean (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r) (j : Fin (k + 4)) :
    Metric.closedBall (Large.meanD (g j)) (rA E A r) ⊆ K j := by
  obtain ⟨b, hb⟩ := (hG j).ball
  rw [meanD_mem hG j, rA]
  refine Large.lemma111a (hG j).compact (hG j).convex hr hb (hG j).meas (hG j).low (hG j).up ?_
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => (hG j).zero y hy, (hG j).int]

lemma rA_pos (hr : 0 < r) : 0 < rA E A r := by unfold rA; positivity

lemma mean_mem (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r) (j : Fin (k + 4)) :
    Large.meanD (g j) ∈ K j :=
  ball_mean hG hr j (Metric.mem_closedBall_self (rA_pos hr).le)

lemma uF_bound (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r)
    {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) {v : E} {V : ℝ} (hv : ‖v‖ ≤ V)
    (j : Fin (k + 4)) (y : E) (hy : y ∈ K j) : |uF g ψ v j y| ≤ 1 + V * R := by
  have h1 := hψ.2.1 j y
  have h2 : |⟪v, y - Large.meanD (g j)⟫| ≤ V * R := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul hv ?_ (norm_nonneg _)
      ((norm_nonneg _).trans hv))
    rw [← dist_eq_norm]; exact (hG j).diam y hy _ (mean_mem hG hr j)
  exact (abs_add_le _ _).trans (by linarith)

lemma uF_lip {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) {v : E} {V : ℝ} (hv : ‖v‖ ≤ V)
    (j : Fin (k + 4)) :
    ∀ x ∈ K j, ∀ y ∈ K j, |uF g ψ v j x - uF g ψ v j y| ≤ (1 + V) * dist x y := by
  intro x hx y hy
  have h1 := hψ.2.2 j x hx y hy
  have h2 : |⟪v, x - Large.meanD (g j)⟫ - ⟪v, y - Large.meanD (g j)⟫| ≤ V * dist x y := by
    rw [← inner_sub_right, show x - Large.meanD (g j) - (y - Large.meanD (g j)) = x - y by abel,
      dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  calc _ = |(ψ (j, x) - ψ (j, y)) + (⟪v, x - Large.meanD (g j)⟫ - ⟪v, y - Large.meanD (g j)⟫)| := by
        unfold uF; ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

lemma uF_meas (hK : ∀ j, IsClosed (K j)) {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (v : E)
    (j : Fin (k + 4)) : Measurable (uF g ψ v j) :=
  (Dset_meas hψ hK j).add ((continuous_const.inner (continuous_id.sub continuous_const)).measurable)

lemma hTv_GH (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r)
    {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) {v : E} {V : ℝ} (hv : ‖v‖ ≤ V)
    (j : Fin (k + 4)) : GH (A + 2 * (1 + V * R)) r R (K j) (hTv g ψ v j) :=
  ig_tilt_GH (hG j) (uF_meas (fun j => (hG j).compact.isClosed) hψ v j)
    (uF_bound hG hr hψ hv j)

lemma tiltDens_tiltD (hG : ∀ j, Large.InG A L r R (K j) (g j)) (_hr : 0 < r)
    {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (v : E) (j : Fin (k + 4)) :
    Large.tiltDens (K j) (Large.tiltD (g j) fun y => ψ (j, y)) v = hTv g ψ v j := by
  have hK : ∀ j, IsClosed (K j) := fun j => (hG j).compact.isClosed
  have hψm := Dset_meas hψ hK j
  obtain ⟨hZ1, -⟩ := ig_Z_bounds (hG j) hψm (c := 1) (fun y _ => hψ.2.1 j y)
  have hZ : 0 < ∫ y, g j y * exp (ψ (j, y)) := (exp_pos _).trans_le hZ1
  have e1 : hTv g ψ v j = Large.tiltD (g j) fun y => ψ (j, y) + ⟪v, y⟫ := by
    rw [hTv, ← tiltD_add_const _ _ (⟪v, Large.meanD (g j)⟫)]
    congr 1; funext y; simp only [uF, inner_sub_right]; ring
  rw [e1]
  funext y
  simp only [Large.tiltDens, Large.tiltD]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [(hG j).zero z hz])]
  simp_rw [div_mul_eq_mul_div, exp_add, ← mul_assoc]
  rw [integral_div, div_div_div_cancel_right₀ hZ.ne']

lemma Gm_eq (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r)
    {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (v : E) :
    ∑ j, ∫ y in K j, Large.tiltDens (K j) (Large.tiltD (g j) fun y => ψ (j, y)) v y • y =
      Gm g ψ v := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tiltDens_tiltD hG hr hψ v j, Large.meanD,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [hTv, Large.tiltD, (hG j).zero y hy]]

lemma vT_spec (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hr : 0 < r)
    {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) :
    Gm g ψ (vT g ψ) = sD g ∧ ‖vT g ψ‖ ≤ VB E A r R ∧ ∀ w, Gm g ψ w = sD g → w = vT g ψ := by
  have hK : ∀ j, IsClosed (K j) := fun j => (hG j).compact.isClosed
  have hGH := fun j => ig_tilt_GH (hG j) (Dset_meas hψ hK j) (c := 1)
    (fun y _ => hψ.2.1 j y)
  have H := Large.lemma111b (n := k + 4) (by omega) K (fun j => (hK j).measurableSet)
    (fun j => Large.meanD (g j)) (rA_pos hr) (ball_mean hG hr)
    (fun j x hx y hy => by rw [← dist_eq_norm]; exact (hG j).diam x hx y hy)
    (A' := A + 2) (by linarith) (fun j => Large.tiltD (g j) fun y => ψ (j, y))
    (fun j => (hGH j).meas) (fun j y hy => by
      have := (hGH j).low y hy; rw [measureReal_def] at this; simpa using this)
    (fun j y hy => by
      have := (hGH j).up y hy; rw [measureReal_def] at this; simpa using this) (fun j => by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => (hGH j).zero y hy,
        (hGH j).int])
  simp_rw [Gm_eq hG hr hψ] at H
  obtain ⟨⟨v0, hv0, hu⟩, hb⟩ := H
  have hex : ∃ v, Gm g ψ v = sD g := ⟨v0, hv0⟩
  have hvT : vT g ψ = hex.choose := by rw [vT, dif_pos hex]
  have hs := hex.choose_spec
  rw [← hvT] at hs
  refine ⟨hs, (hb _ hs).1, fun w hw => (hu w hw).trans (hu _ hs).symm⟩

variable (E) in
/-- The `L¹`-modulus constant `D = e^{A₂} (L + 1 + V + 2d/r)`. -/
def DC (A L r R : ℝ) : ℝ :=
  exp (A2 E A r R) * (L + (1 + VB E A r R) + 2 * Module.finrank ℝ E / r)

lemma VB_nonneg (hA : 0 ≤ A) (hr : 0 < r) (hrR : r ≤ R) : 0 ≤ VB E A r R := by
  have hρ := rA_pos (E := E) (A := A) hr
  have h1 : rA E A r ≤ 2 * r := by
    unfold rA
    rw [div_le_iff₀ (by positivity)]
    have : exp (-A) ≤ 1 := exp_le_one_iff.2 (by linarith)
    have : (1 : ℝ) ≤ Module.finrank ℝ E + 1 := by
      have := (Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _); linarith
    nlinarith
  have hv1 := vball_pos (E := E) (r := rA E A r / 4) (by positivity)
  have h2 : volume.real (Metric.ball (0 : E) (rA E A r / 4)) ≤
      volume.real (Metric.closedBall (0 : E) R) :=
    ENNReal.toReal_mono measure_closedBall_lt_top.ne
      (measure_mono (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by linarith))))
  have h3 : 0 < volume.real (Metric.ball (0 : E) (rA E A r / 4)) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by positivity)).ne'
      measure_ball_lt_top.ne
  unfold VB Large.constV'
  have : 0 ≤ log ((volume (Metric.closedBall (0 : E) R)).toReal /
      (volume (Metric.ball (0 : E) (rA E A r / 4))).toReal) :=
    log_nonneg ((one_le_div h3).2 h2)
  positivity

lemma DC_nonneg (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r) (hrR : r ≤ R) : 0 ≤ DC E A L r R := by
  have := VB_nonneg (E := E) hA hr hrR
  unfold DC; positivity

/-- The ratio bound of Lemma 112 for the class `𝓗(A₂, r, R)` with radius `2R`. -/
def LLTprop (A r R : ℝ) (N : ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ m ≥ N, ∀ (Ks : Fin (m + 2) → Set E) (hs : Fin (m + 2) → E → ℝ),
    (∀ k, GH A r R (Ks k) (hs k)) → ∀ y y' : E,
    ‖y - ∑ k, Large.meanD (hs k)‖ ≤ 2 * R → ‖y' - ∑ k, Large.meanD (hs k)‖ ≤ 2 * R →
    0 < cvF (m + 1) hs y' ∧ |cvF (m + 1) hs y / cvF (m + 1) hs y' - 1| ≤ δ m

/-- **Estimates for `f_{-j}`** on `s - K_j`: a positive lower bound, and the Lipschitz bound
`|log f_{-j}(s - p) - log f_{-j}(s - p')| ≤ 2 D δ |p - p'|`. -/
lemma fJ_est (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r)
    (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ} (hδ : LLTprop (E := E) (A2 E A r R) r R N δ)
    (hk : N ≤ k) (hδ2 : δ k ≤ 1 / 2) {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K)
    (j : Fin (k + 4)) :
    (∃ c > 0, ∀ p ∈ K j, c ≤ fJ g ψ j (sD g - p)) ∧
    ∀ p ∈ K j, ∀ p' ∈ K j, |log (fJ g ψ j (sD g - p)) - log (fJ g ψ j (sD g - p'))| ≤
      2 * DC E A L r R * δ k * ‖p - p'‖ := by
  obtain ⟨hGm, hvV, -⟩ := vT_spec hG hA hr hψ
  set v := vT g ψ
  have hV0 := VB_nonneg (E := E) hA hr hrR
  have hGH : ∀ i, GH (A2 E A r R) r R (K i) (hTv g ψ v i) := fun i => hTv_GH hG hr hψ hvV i
  set H : Fin (k + 3) → E → ℝ := fun i => hTv g ψ v (j.succAbove i)
  set M := exp (A2 E A r R) / volume.real (Metric.closedBall (0 : E) r)
  have hPD : ∀ i, PDg M (hTv g ψ v i) := fun i => (hGH i).pdg hr
  set T := cvF (k + 1) (Fin.tail H)
  set z0 := ∑ i, Large.meanD (Fin.tail H i)
  have hT := hδ k hk (fun i => K (j.succAbove i.succ)) (Fin.tail H) (fun i => hGH _)
  have hR0 : 0 ≤ R := hr.le.trans hrR
  have hzz : ‖z0 - ∑ i, Large.meanD (Fin.tail H i)‖ ≤ 2 * R := by
    show ‖z0 - z0‖ ≤ 2 * R
    rw [sub_self, norm_zero]; linarith
  obtain ⟨hTz, -⟩ := hT z0 z0 hzz hzz
  have hδ0 : 0 ≤ δ k := (abs_nonneg _).trans (hT z0 z0 hzz hzz).2
  obtain ⟨-, hT0, hTb, -⟩ := cvF_props (k + 1) (Fin.tail H) fun i => hPD _
  have hD := ig_tilt_l1 (hG (j.succAbove 0)) (uF_meas (fun j => (hG j).compact.isClosed) hψ v _)
    (uF_bound hG hr hψ hvV _) (uF_lip hψ hvV _) hr hL (by linarith)
  have key := key_log (a := H 0) (T := T) (R := R) (D := DC E A L r R) (δ := δ k) (MT := M)
    (z0 := z0) (μa := Large.meanD (H 0)) ((hGH _).nonneg hr) (hGH _).integrable (hGH _).int
    (fun y hy => (hGH _).norm_sub_mean_le hr (by
      by_contra hc; exact hy ((hGH _).zero y hc)))
    (fun y y' => hD y y')
    (measurable_cvF _ _ fun i => hPD _) hT0 hTb hTz
    (fun t ht => (hT t z0 ht hzz).2) hδ0 hδ2
    (DC_nonneg hA hL hr hrR)
  have hfJ : fJ g ψ j = cv (H 0) T := rfl
  have hloc : ∀ p ∈ K j, ‖sD g - p - Large.meanD (H 0) - z0‖ ≤ R := by
    intro p hp
    have e : sD g = Large.meanD (hTv g ψ v j) + (Large.meanD (H 0) + z0) := by
      rw [← hGm, Gm, Fin.sum_univ_succAbove _ j, Fin.sum_univ_succ]
      rfl
    rw [e, show Large.meanD (hTv g ψ v j) + (Large.meanD (H 0) + z0) - p - Large.meanD (H 0) - z0
      = -(p - Large.meanD (hTv g ψ v j)) by abel, norm_neg]
    exact (hGH j).norm_sub_mean_le hr hp
  refine ⟨⟨(1 - δ k) * T z0, mul_pos (by linarith) hTz, fun p hp => ?_⟩, fun p hp p' hp' => ?_⟩
  · rw [hfJ]; exact key.1 _ (hloc p hp)
  · rw [hfJ]
    have := key.2 _ _ (hloc p hp) (hloc p' hp')
    rwa [show sD g - p - (sD g - p') = -(p - p') by abel, norm_neg] at this

/-- Bounds for `Φ(ψ)`: `|Φ(ψ)_j| ≤ 2DδR` and `Lip(Φ(ψ)_j) ≤ 2Dδ` on `K_j`. -/
lemma Phi_est (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r)
    (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ} (hδ : LLTprop (E := E) (A2 E A r R) r R N δ)
    (hk : N ≤ k) (hδ0 : 0 ≤ δ k) (hδ2 : δ k ≤ 1 / 2) {ψ : Fin (k + 4) × E → ℝ}
    (hψ : ψ ∈ Dset K) (j : Fin (k + 4)) :
    (∀ p ∈ K j, |Phi K g ψ (j, p)| ≤ 2 * DC E A L r R * δ k * R) ∧
    ∀ x ∈ K j, ∀ y ∈ K j, |Phi K g ψ (j, x) - Phi K g ψ (j, y)| ≤
      2 * DC E A L r R * δ k * dist x y := by
  have H := (fJ_est hG hA hL hr hrR hδ hk hδ2 hψ j).2
  have hm := mean_mem hG hr j
  have hc : 0 ≤ 2 * DC E A L r R * δ k := by
    have := DC_nonneg (E := E) hA hL hr hrR
    positivity
  constructor
  · intro p hp
    simp only [Phi, if_pos hp, abs_neg]
    refine (H p hp _ hm).trans (mul_le_mul_of_nonneg_left ?_ hc)
    rw [← dist_eq_norm]; exact (hG j).diam p hp _ hm
  · intro x hx y hy
    simp only [Phi, if_pos hx, if_pos hy]
    have := H y hy x hx
    rw [← dist_eq_norm, dist_comm] at this
    calc _ = |log (fJ g ψ j (sD g - y)) - log (fJ g ψ j (sD g - x))| := by ring_nf
      _ ≤ _ := this

lemma Phi_maps (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 < r)
    (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ} (hδ : LLTprop (E := E) (A2 E A r R) r R N δ)
    (hk : N ≤ k) (hδ0 : 0 ≤ δ k) (hδ2 : δ k ≤ 1 / 2)
    (hδ3 : 2 * DC E A L r R * δ k * (R + 1) ≤ 1) :
    Set.MapsTo (Phi K g) (Dset K) (Dset K) := by
  intro ψ hψ
  have hR0 : 0 ≤ R := hr.le.trans hrR
  have hc : 0 ≤ 2 * DC E A L r R * δ k := by
    have := DC_nonneg (E := E) hA hL hr hrR; positivity
  refine ⟨fun j y hy => by simp [Phi, hy], fun j y => ?_, fun j x hx y hy => ?_⟩
  · by_cases hy : y ∈ K j
    · refine ((Phi_est hG hA hL hr hrR hδ hk hδ0 hδ2 hψ j).1 y hy).trans ?_
      nlinarith
    · simp [Phi, hy]
  · refine ((Phi_est hG hA hL hr hrR hδ hk hδ0 hδ2 hψ j).2 x hx y hy).trans ?_
    have : 2 * DC E A L r R * δ k ≤ 1 := by nlinarith
    calc _ ≤ 1 * dist x y := mul_le_mul_of_nonneg_right this dist_nonneg
      _ = _ := one_mul _

lemma hTv_le (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r)
    {ψ ψ' : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (hψ' : ψ' ∈ Dset K) {v v' : E} {V η1 : ℝ}
    (hv : ‖v‖ ≤ V) (hv' : ‖v'‖ ≤ V) (hc : ∀ j, ∀ y ∈ K j, |ψ (j, y) - ψ' (j, y)| ≤ η1)
    (j : Fin (k + 4)) (y : E) :
    hTv g ψ v j y ≤ exp (2 * (η1 + ‖v - v'‖ * R)) * hTv g ψ' v' j y := by
  have hK : ∀ j, IsClosed (K j) := fun j => (hG j).compact.isClosed
  have hg0 : ∀ y, 0 ≤ g j y := fun y => by
    by_cases hy : y ∈ K j
    · exact ((hG j).gpos hy).le
    · rw [(hG j).zero y hy]
  obtain ⟨hZ1, -⟩ := ig_Z_bounds (hG j) (uF_meas hK hψ' v' j) (uF_bound hG hr hψ' hv' j)
  refine tiltD_le hg0 (ig_integrable_mul_exp (hG j) (uF_meas hK hψ v j) (uF_bound hG hr hψ hv j))
    (ig_integrable_mul_exp (hG j) (uF_meas hK hψ' v' j) (uF_bound hG hr hψ' hv' j))
    ((exp_pos _).trans_le hZ1) (fun y hy => ?_) y
  have hyK : y ∈ K j := by by_contra hc'; exact hy ((hG j).zero y hc')
  have h1 := hc j y hyK
  have h2 : |⟪v - v', y - Large.meanD (g j)⟫| ≤ ‖v - v'‖ * R := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [← dist_eq_norm]; exact (hG j).diam y hyK _ (mean_mem hG hr j)
  calc |uF g ψ v j y - uF g ψ' v' j y|
      = |(ψ (j, y) - ψ' (j, y)) + ⟪v - v', y - Large.meanD (g j)⟫| := by
        simp only [uF, inner_sub_left]; ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

lemma abs_log_le_of_ratio {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : a ≤ exp c * b)
    (h2 : b ≤ exp c * a) : |log a - log b| ≤ c := by
  rw [abs_le]
  have e1 := log_le_log ha h1
  have e2 := log_le_log hb h2
  rw [log_mul (exp_pos _).ne' hb.ne', log_exp] at e1
  rw [log_mul (exp_pos _).ne' ha.ne', log_exp] at e2
  constructor <;> linarith

/-- Comparison of the `f_{-j}` for nearby `ψ` and tilts. -/
lemma fJ_cmp (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hr : 0 < r)
    {ψ ψ' : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (hψ' : ψ' ∈ Dset K) {η1 : ℝ}
    (hc : ∀ j, ∀ y ∈ K j, |ψ (j, y) - ψ' (j, y)| ≤ η1) (j : Fin (k + 4)) (y : E) :
    fJ g ψ j y ≤ exp (2 * (η1 + ‖vT g ψ - vT g ψ'‖ * R)) ^ (k + 3) * fJ g ψ' j y := by
  obtain ⟨-, hv, -⟩ := vT_spec hG hA hr hψ
  obtain ⟨-, hv', -⟩ := vT_spec hG hA hr hψ'
  exact cvF_le_mul (exp_pos _).le (k + 2) _ _ (fun i => (hTv_GH hG hr hψ hv _).pdg hr)
    (fun i => (hTv_GH hG hr hψ' hv' _).pdg hr)
    (fun i y => hTv_le hG hr hψ hψ' hv hv' hc _ y) y

/-- Modulus of continuity of `G(ψ, v) = ∑ m_{h_j}`. -/
lemma Gm_cmp (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hr : 0 < r) {B : ℝ}
    (hB : ∀ j, ∀ y ∈ K j, ‖y‖ ≤ B)
    {ψ ψ' : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (hψ' : ψ' ∈ Dset K) {v v' : E} {V η1 : ℝ}
    (hv : ‖v‖ ≤ V) (hv' : ‖v'‖ ≤ V) (hc : ∀ j, ∀ y ∈ K j, |ψ (j, y) - ψ' (j, y)| ≤ η1) :
    ‖Gm g ψ v - Gm g ψ' v'‖ ≤
      (k + 4) * ((exp (2 * (η1 + ‖v - v'‖ * R)) - 1) * B) := by
  have hc' : ∀ j, ∀ y ∈ K j, |ψ' (j, y) - ψ (j, y)| ≤ η1 := fun j y hy => by
    rw [abs_sub_comm]; exact hc j y hy
  have hj : ∀ j, ‖Large.meanD (hTv g ψ v j) - Large.meanD (hTv g ψ' v' j)‖ ≤
      (exp (2 * (η1 + ‖v - v'‖ * R)) - 1) * B := by
    intro j
    have h1 := hTv_GH hG hr hψ hv j
    have h2 := hTv_GH hG hr hψ' hv' j
    refine meanD_sub_le h1.meas h2.meas h1.integrable h2.integrable h2.int h1.zero h2.zero (hB j)
      (fun y => abs_sub_le_of_ratio (h2.nonneg hr y) (hTv_le hG hr hψ hψ' hv hv' hc j y) ?_)
    have := hTv_le hG hr hψ' hψ hv' hv hc' j y
    rwa [norm_sub_rev] at this
  rw [Gm, Gm, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
  simp

section Topology

lemma eventually_close (hG : ∀ j, Large.InG A L r R (K j) (g j))
    {ψ0 : Fin (k + 4) × E → ℝ} (h0 : ψ0 ∈ Dset K) {η1 : ℝ} (hη : 0 < η1) :
    ∀ᶠ ψ in 𝓝[Dset K] ψ0, ∀ j, ∀ y ∈ K j, |ψ (j, y) - ψ0 (j, y)| ≤ η1 := by
  have he : 0 < η1 / 3 := by positivity
  choose t ht htf htc using fun j => (hG j).compact.finite_cover_balls he
  have hev : ∀ᶠ ψ in 𝓝 ψ0, ∀ j, ∀ x ∈ t j, dist (ψ (j, x)) (ψ0 (j, x)) < η1 / 3 := by
    rw [eventually_all]
    intro j
    rw [eventually_all_finite (htf j)]
    intro x _
    exact Metric.tendsto_nhds.1 ((continuous_apply (j, x)).tendsto ψ0) _ he
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev, self_mem_nhdsWithin]
    with ψ hψ hψD j y hy
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (htc j hy)
  have hxK := ht j hx
  rw [Metric.mem_ball] at hyx
  have h1 := hψD.2.2 j y hy x hxK
  have h2 := h0.2.2 j x hxK y hy
  have h3 := hψ j x hx
  rw [Real.dist_eq] at h3
  rw [dist_comm] at h2
  calc |ψ (j, y) - ψ0 (j, y)| ≤ |ψ (j, y) - ψ (j, x)| + |ψ (j, x) - ψ0 (j, x)| +
        |ψ0 (j, x) - ψ0 (j, y)| := by
        have := abs_sub_le (ψ (j, y)) (ψ (j, x)) (ψ0 (j, y))
        have := abs_sub_le (ψ (j, x)) (ψ0 (j, x)) (ψ0 (j, y))
        linarith
    _ ≤ η1 := by linarith

lemma tendsto_vT (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hr : 0 < r)
    {ψ0 : Fin (k + 4) × E → ℝ} (h0 : ψ0 ∈ Dset K) :
    Tendsto (vT g) (𝓝[Dset K] ψ0) (𝓝 (vT g ψ0)) := by
  obtain ⟨B, hB⟩ := (isCompact_iUnion fun j => (hG j).compact).isBounded.subset_closedBall 0
  have hB' : ∀ j, ∀ y ∈ K j, ‖y‖ ≤ B := fun j y hy => by
    have := hB (Set.mem_iUnion.2 ⟨j, hy⟩); simpa using this
  set V := VB E A r R
  refine (isCompact_closedBall (0 : E) V).tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ψ hψ
    simpa using (vT_spec hG hA hr hψ).2.1
  intro w hw hcl
  rw [mem_closedBall_zero_iff] at hw
  refine (vT_spec hG hA hr h0).2.2 w (eq_of_forall_dist_le fun ε hε => ?_)
  -- choose `η` with `(k + 4) (e^{2η(1+R)} - 1) B ≤ ε`
  have hcont : Continuous fun η : ℝ => ((k : ℝ) + 4) * ((exp (2 * (η + η * R)) - 1) * B) := by
    fun_prop
  have h00 : ((k : ℝ) + 4) * ((exp (2 * ((0 : ℝ) + 0 * R)) - 1) * B) = 0 := by simp
  obtain ⟨ρ, hρ, hρε⟩ := Metric.continuous_iff.1 hcont 0 ε hε
  set η := ρ / 2
  have hη : 0 < η := by positivity
  have hηε : ((k : ℝ) + 4) * ((exp (2 * (η + η * R)) - 1) * B) < ε := by
    have := hρε η (by rw [Real.dist_eq, sub_zero, abs_of_pos hη]; simp only [η]; linarith)
    rw [h00, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hfr := (mapClusterPt_iff_frequently.1 hcl) _ (Metric.closedBall_mem_nhds w hη)
  obtain ⟨ψ, hψw, hψc, hψD⟩ := (hfr.and_eventually ((eventually_close hG h0 hη).and
    self_mem_nhdsWithin)).exists
  obtain ⟨hGψ, hvψ, -⟩ := vT_spec hG hA hr hψD
  have hc : ∀ j, ∀ y ∈ K j, |ψ0 (j, y) - ψ (j, y)| ≤ η := fun j y hy => by
    rw [abs_sub_comm]; exact hψc j y hy
  have := Gm_cmp hG hr hB' h0 hψD hw hvψ hc
  rw [hGψ, ← dist_eq_norm] at this
  refine this.trans (le_trans ?_ hηε.le)
  have hR0 : 0 ≤ R := by
    obtain ⟨b, hb⟩ := (hG 0).ball
    have := (hG 0).diam b (hb (Metric.mem_closedBall_self hr.le)) b
      (hb (Metric.mem_closedBall_self hr.le))
    simpa using this
  have hwv : ‖w - vT g ψ‖ ≤ η := by
    rw [← dist_eq_norm, dist_comm]; exact hψw
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0 _ (mean_mem hG hr 0))
  gcongr

lemma logfJ_cont (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hr : 0 < r) (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ}
    (hδ : LLTprop (E := E) (A2 E A r R) r R N δ) (hk : N ≤ k) (hδ2 : δ k ≤ 1 / 2)
    {ψ0 : Fin (k + 4) × E → ℝ} (h0 : ψ0 ∈ Dset K) (j : Fin (k + 4)) {q : E} (hq : q ∈ K j) :
    ContinuousWithinAt (fun ψ => log (fJ g ψ j (sD g - q))) (Dset K) ψ0 := by
  have hR0 : 0 ≤ R := hr.le.trans hrR
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set η1 := ε / (8 * ((k : ℝ) + 3))
  set η2 := ε / (8 * ((k : ℝ) + 3) * (R + 1))
  have hη1 : 0 < η1 := by positivity
  have hη2 : 0 < η2 := by positivity
  filter_upwards [eventually_close hG h0 hη1, self_mem_nhdsWithin,
    Metric.tendsto_nhds.1 (tendsto_vT hG hA hr h0) η2 hη2] with ψ hc hψ hv
  rw [dist_eq_norm] at hv
  obtain ⟨c1, hc1, hl1⟩ := (fJ_est hG hA hL hr hrR hδ hk hδ2 hψ j).1
  obtain ⟨c0, hc0, hl0⟩ := (fJ_est hG hA hL hr hrR hδ hk hδ2 h0 j).1
  have hc' : ∀ j, ∀ y ∈ K j, |ψ0 (j, y) - ψ (j, y)| ≤ η1 := fun j y hy => by
    rw [abs_sub_comm]; exact hc j y hy
  set c := ((k : ℝ) + 3) * (2 * (η1 + ‖vT g ψ - vT g ψ0‖ * R))
  have hexp : exp (2 * (η1 + ‖vT g ψ - vT g ψ0‖ * R)) ^ (k + 3) = exp c := by
    rw [← exp_natCast_mul]; push_cast; rfl
  have hexp' : exp (2 * (η1 + ‖vT g ψ0 - vT g ψ‖ * R)) ^ (k + 3) = exp c := by
    rw [norm_sub_rev, hexp]
  have h1 := fJ_cmp hG hA hr hψ h0 hc j (sD g - q)
  have h2 := fJ_cmp hG hA hr h0 hψ hc' j (sD g - q)
  rw [hexp] at h1
  rw [hexp'] at h2
  rw [Real.dist_eq]
  refine (abs_log_le_of_ratio (hc1.trans_le (hl1 q hq)) (hc0.trans_le (hl0 q hq)) h1 h2).trans_lt ?_
  have : ‖vT g ψ - vT g ψ0‖ * R ≤ η2 * R := mul_le_mul_of_nonneg_right hv.le hR0
  have e1 : ((k : ℝ) + 3) * (2 * η1) = ε / 4 := by
    simp only [η1]; field_simp; ring
  have e2 : ((k : ℝ) + 3) * (2 * (η2 * R)) ≤ ε / 4 := by
    simp only [η2]
    rw [show ((k : ℝ) + 3) * (2 * (ε / (8 * ((k : ℝ) + 3) * (R + 1)) * R)) =
      ε / 4 * (R / (R + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  have hk3 : (0 : ℝ) ≤ (k : ℝ) + 3 := by positivity
  calc c = ((k : ℝ) + 3) * (2 * η1) + ((k : ℝ) + 3) * (2 * (‖vT g ψ - vT g ψ0‖ * R)) := by ring
    _ ≤ ε / 4 + ((k : ℝ) + 3) * (2 * (η2 * R)) := by
        rw [e1]; gcongr
    _ < ε := by linarith

lemma Phi_cont (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hr : 0 < r) (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ}
    (hδ : LLTprop (E := E) (A2 E A r R) r R N δ) (hk : N ≤ k) (hδ2 : δ k ≤ 1 / 2) :
    ContinuousOn (Phi K g) (Dset K) := by
  intro ψ0 h0
  rw [continuousWithinAt_pi]
  rintro ⟨j, p⟩
  by_cases hp : p ∈ K j
  · have e : (fun ψ => Phi K g ψ (j, p)) = fun ψ => -(log (fJ g ψ j (sD g - p)) -
        log (fJ g ψ j (sD g - Large.meanD (g j)))) := by
      funext ψ; simp [Phi, hp]
    rw [e]
    exact ((logfJ_cont hG hA hL hr hrR hδ hk hδ2 h0 j hp).sub
      (logfJ_cont hG hA hL hr hrR hδ hk hδ2 h0 j (mean_mem hG hr j))).neg
  · have e : (fun ψ => Phi K g ψ (j, p)) = fun _ => 0 := by
      funext ψ; simp [Phi, hp]
    rw [e]; exact continuousWithinAt_const

lemma Dset_compact : IsCompact (Dset K) := by
  have hsub : Dset K ⊆ Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1 := fun ψ hψ q _ => by
    exact abs_le.1 (hψ.2.1 q.1 q.2)
  refine (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset ?_ hsub
  have e : Dset K = (⋂ j, ⋂ y, ⋂ (_ : y ∉ K j), {ψ : Fin (k + 4) × E → ℝ | ψ (j, y) = 0}) ∩
      ((⋂ j, ⋂ y, {ψ : Fin (k + 4) × E → ℝ | |ψ (j, y)| ≤ 1}) ∩
      ⋂ j, ⋂ x ∈ K j, ⋂ y ∈ K j,
        {ψ : Fin (k + 4) × E → ℝ | |ψ (j, x) - ψ (j, y)| ≤ dist x y}) := by
    ext ψ; simp [Dset]
  rw [e]
  have hc : ∀ q : Fin (k + 4) × E, Continuous fun ψ : Fin (k + 4) × E → ℝ => ψ q :=
    fun q => continuous_apply q
  refine (isClosed_iInter fun j => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_eq (hc _) continuous_const).inter ((isClosed_iInter fun j => isClosed_iInter
      fun y => isClosed_le (hc _).abs continuous_const).inter (isClosed_iInter fun j =>
      isClosed_biInter fun x _ => isClosed_biInter fun y _ =>
        isClosed_le ((hc _).sub (hc _)).abs continuous_const))

lemma Dset_convex : Convex ℝ (Dset K) := by
  intro ψ hψ ψ' hψ' a b ha hb hab
  refine ⟨fun j y hy => by simp [hψ.1 j y hy, hψ'.1 j y hy], fun j y => ?_,
    fun j x hx y hy => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * ψ (j, y) + b * ψ' (j, y)| ≤ a * |ψ (j, y)| + b * |ψ' (j, y)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr; exacts [hψ.2.1 j y, hψ'.2.1 j y]
      _ = 1 := by rw [mul_one, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * ψ (j, x) + b * ψ' (j, x) - (a * ψ (j, y) + b * ψ' (j, y))|
        = |a * (ψ (j, x) - ψ (j, y)) + b * (ψ' (j, x) - ψ' (j, y))| := by ring_nf
      _ ≤ a * |ψ (j, x) - ψ (j, y)| + b * |ψ' (j, x) - ψ' (j, y)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * dist x y + b * dist x y := by
          gcongr; exacts [hψ.2.2 j x hx y hy, hψ'.2.2 j x hx y hy]
      _ = dist x y := by rw [← add_mul, hab, one_mul]

lemma zero_mem_Dset : (0 : Fin (k + 4) × E → ℝ) ∈ Dset K :=
  ⟨fun _ _ _ => rfl, fun _ _ => by simp, fun _ _ _ _ _ => by simp⟩

end Topology

section Fixed

lemma wd_restrict {K0 : Set E} (hK : MeasurableSet K0) {F : E → ENNReal}
    (hF : ∀ z ∉ K0, F z = 0) : volume.withDensity F = (volume.restrict K0).withDensity F := by
  rw [← withDensity_indicator hK]
  congr 1; funext z
  by_cases hz : z ∈ K0
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz, hF z hz]

lemma InG.toGH {K0 : Set E} {g0 : E → ℝ} (hG : Large.InG A L r R K0 g0) : GH A r R K0 g0 :=
  ⟨hG.compact, hG.convex, hG.ball, hG.diam, hG.meas, hG.zero, hG.int, hG.low, hG.up⟩

/-- A probability measure with density `a g e^{⟪v,·⟫}` is the tilt `(g)_v` on `K`. -/
lemma marg_tilt {K0 : Set E} {g0 : E → ℝ} (hG : Large.InG A L r R K0 g0) {B : ℝ}
    (hB : ∀ y ∈ K0, ‖y‖ ≤ B) (v : E) {a : ℝ}
    (hprob : IsProbabilityMeasure
      (volume.withDensity fun z => ENNReal.ofReal (a * (g0 z * exp ⟪v, z⟫)))) :
    volume.withDensity (fun z => ENNReal.ofReal (a * (g0 z * exp ⟪v, z⟫))) =
      (volume.restrict K0).withDensity fun z =>
        ENNReal.ofReal (Large.tiltDens K0 g0 v z) := by
  have hKm : MeasurableSet K0 := hG.compact.isClosed.measurableSet
  have hu : Measurable fun z : E => ⟪v, z⟫ := (continuous_const.inner continuous_id).measurable
  have hc : ∀ y ∈ K0, |⟪v, y⟫| ≤ ‖v‖ * B := fun y hy =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hB y hy) (norm_nonneg _))
  have hi := ig_integrable_mul_exp hG hu hc
  obtain ⟨hW1, -⟩ := ig_Z_bounds hG hu hc
  set W := ∫ z, g0 z * exp ⟪v, z⟫
  have hW : 0 < W := (exp_pos _).trans_le hW1
  have hg0 : ∀ y, 0 ≤ g0 y := fun y => by
    by_cases hy : y ∈ K0
    · exact (hG.gpos hy).le
    · rw [hG.zero y hy]
  have hmass := hprob.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  have ha : 0 ≤ a := by
    by_contra hneg; push Not at hneg
    have : ∀ z, ENNReal.ofReal (a * (g0 z * exp ⟪v, z⟫)) = 0 := fun z =>
      ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonpos_of_nonneg hneg.le
        (mul_nonneg (hg0 z) (exp_pos _).le))
    simp [this] at hmass
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul a) (Eventually.of_forall fun z =>
    mul_nonneg ha (mul_nonneg (hg0 z) (exp_pos _).le)), integral_const_mul] at hmass
  have haW : a * W = 1 := by
    have := (ENNReal.ofReal_eq_one).1 hmass
    exact this
  rw [wd_restrict hKm (fun z hz => by simp [hG.zero z hz])]
  congr 1; funext z
  congr 1
  rw [Large.tiltDens, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
    simp [hG.zero y hy]]
  change a * (g0 z * exp ⟪v, z⟫) = g0 z * exp ⟪v, z⟫ / W
  rw [eq_div_iff hW.ne']
  linear_combination (g0 z * exp ⟪v, z⟫) * haW

/-- **A fixed point of `Φ` gives the joint mix** (and the tilt `v` vanishes). -/
lemma fixed_mix (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hr : 0 < r) (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ}
    (hδ : LLTprop (E := E) (A2 E A r R) r R N δ) (hk : N ≤ k) (hδ2 : δ k ≤ 1 / 2)
    {ψ : Fin (k + 4) × E → ℝ} (hψ : ψ ∈ Dset K) (hfix : Phi K g ψ = ψ) :
    vT g ψ = 0 ∧
    IsJointMix (fun j => Large.densMeas (g j))
      (Large.condMeas (Large.lebT (k + 3) (sD g)) fun j => hTv g ψ 0 j) ∧
    0 < cvF (k + 3) (fun j => hTv g ψ 0 j) (sD g) := by
  have hK : ∀ j, IsClosed (K j) := fun j => (hG j).compact.isClosed
  have hKm : ∀ j, MeasurableSet (K j) := fun j => (hK j).measurableSet
  obtain ⟨B, hB⟩ := (isCompact_iUnion fun j => (hG j).compact).isBounded.subset_closedBall 0
  have hB' : ∀ j, ∀ y ∈ K j, ‖y‖ ≤ B := fun j y hy => by
    have := hB (Set.mem_iUnion.2 ⟨j, hy⟩); simpa using this
  obtain ⟨hGm, hvV, -⟩ := vT_spec hG hA hr hψ
  set v := vT g ψ with hvdef
  set h : Fin (k + 4) → E → ℝ := fun j => hTv g ψ v j with hhdef
  have hGH : ∀ j, GH (A2 E A r R) r R (K j) (h j) := fun j => hTv_GH hG hr hψ hvV j
  set M := exp (A2 E A r R) / volume.real (Metric.closedBall (0 : E) r)
  have hPD : ∀ j, PDg M (h j) := fun j => (hGH j).pdg hr
  set s := sD g
  set Z := cvF (k + 3) h s
  -- positivity of the normaliser
  have hZ : 0 < Z := by
    obtain ⟨c, hc, hlow⟩ := (fJ_est hG hA hL hr hrR hδ hk hδ2 hψ 0).1
    have hf0 : fJ g ψ 0 = cvF (k + 2) (Fin.tail h) := by
      unfold fJ; congr 1
    obtain ⟨-, n1, l1, -⟩ := cvF_props (k + 2) (Fin.tail h) fun i => hPD _
    have hZe : Z = ∫ t, h 0 t * cvF (k + 2) (Fin.tail h) (s - t) := rfl
    rw [hZe]
    calc (0 : ℝ) < c := hc
      _ = ∫ t, h 0 t * c := by rw [integral_mul_const, (hGH 0).int, one_mul]
      _ ≤ _ := by
        refine integral_mono ((hGH 0).integrable.mul_const _) ?_ fun t => ?_
        · exact (hGH 0).integrable.mul_bdd ((measurable_cvF _ _ fun i => hPD _).comp
            (measurable_const.sub measurable_id)).aestronglyMeasurable (c := M)
            (Eventually.of_forall fun t => by
              rw [Real.norm_eq_abs, abs_of_nonneg (n1 _)]; exact l1 _)
        · by_cases ht : t ∈ K 0
          · rw [← hf0]
            exact mul_le_mul_of_nonneg_left (hlow t ht) ((hGH 0).nonneg hr t)
          · simp [(hGH 0).zero t ht]
  have hprob := condMeas_prob h hPD s hZ
  set β := Large.condMeas (Large.lebT (k + 3) s) h with hβdef
  -- the marginals are tilts of the `g_j`
  have hmarg : ∀ j, β.map (fun x => x j) = (volume.restrict (K j)).withDensity fun z =>
      ENNReal.ofReal (Large.tiltDens (K j) (g j) v z) := by
    intro j
    obtain ⟨c0, hc0, hl0⟩ := (fJ_est hG hA hL hr hrR hδ hk hδ2 hψ j).1
    set m := Large.meanD (g j)
    set Z' := ∫ y, g j y * exp (uF g ψ v j y)
    set a := fJ g ψ j (s - m) * exp (-⟪v, m⟫) / Z' / Z
    have hpt : ∀ z, h j z * cvF (k + 1 + 1) (fun i => h (j.succAbove i)) (s - z) / Z =
        a * (g j z * exp ⟪v, z⟫) := by
      intro z
      by_cases hz : z ∈ K j
      · have hfz := hc0.trans_le (hl0 z hz)
        have hfm := hc0.trans_le (hl0 m (mean_mem hG hr j))
        have hfx := congr_fun hfix (j, z)
        simp only [Phi, hz, if_true] at hfx
        have hfe : fJ g ψ j (s - z) = fJ g ψ j (s - m) * exp (-ψ (j, z)) := by
          have : log (fJ g ψ j (s - z)) = log (fJ g ψ j (s - m)) + -ψ (j, z) := by linarith
          rw [← exp_log hfz, this, exp_add, exp_log hfm]
        obtain ⟨hZ'1, -⟩ := ig_Z_bounds (hG j) (uF_meas hK hψ v j) (uF_bound hG hr hψ hvV j)
        have hZ' : 0 < Z' := (exp_pos _).trans_le hZ'1
        have hh : h j z = g j z * (exp (ψ (j, z)) * exp ⟪v, z⟫ * exp (-⟪v, m⟫)) / Z' := by
          show Large.tiltD (g j) (uF g ψ v j) z = _
          rw [Large.tiltD]; congr 1
          rw [uF, inner_sub_right, sub_eq_add_neg, exp_add, exp_add]; ring
        change h j z * fJ g ψ j (s - z) / Z = _
        rw [hh, hfe]
        simp only [a]
        rw [exp_neg (ψ (j, z))]
        field_simp
      · have hg : g j z = 0 := (hG j).zero z hz
        show Large.tiltD (g j) (uF g ψ v j) z * _ / Z = _
        simp [Large.tiltD, hg]
    have hm1 : β.map (fun x => x j) =
        volume.withDensity fun z => ENNReal.ofReal (a * (g j z * exp ⟪v, z⟫)) := by
      refine (condMeas_marg (k + 1) h hPD s hZ j).trans ?_
      congr 1; funext z; rw [← hpt z]
    rw [hm1]
    have hp : IsProbabilityMeasure
        (volume.withDensity fun z => ENNReal.ofReal (a * (g j z * exp ⟪v, z⟫))) := by
      rw [← hm1]; infer_instance
    exact marg_tilt (hG j) (hB' j) v hp
  -- `v = 0` by Lemma 111(c)
  have hsum : ∀ᵐ x ∂β, ∑ j, x j = s :=
    Large.ae_condMeas (Large.ae_sum_lebT (k + 3) s)
  have hsupp : ∀ᵐ x ∂β, ∀ j, x j ∈ K j := by
    rw [hβdef, Large.condMeas, ae_withDensity_iff' (by
      refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
      show Measurable fun x : Fin (k + 4) → E => (∏ i, h i (x i)) / _
      exact (Finset.measurable_prod _ fun i _ => (hPD i).meas.comp
        (measurable_pi_apply i)).div_const _)]
    refine Eventually.of_forall fun x hx j => ?_
    by_contra hxj
    apply hx
    simp only [Large.condProdJ]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) ((hGH j).zero _ hxj), zero_div,
      ENNReal.ofReal_zero]
  have hgle : ∀ j, ∀ y ∈ K j, g j y ≤ exp A / volume.real (Metric.closedBall (0 : E) r) :=
    fun j y _ => (InG.toGH (hG j)).le hr y
  have hint : ∀ j, ∫ y in K j, g j y = 1 := fun j => by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => (hG j).zero y hy, (hG j).int]
  have hv0 : v = 0 := Large.lemma111c (n := k + 4) (by omega) K hKm hB' g (fun j => (hG j).meas)
    (fun j y hy => ((hG j).gpos hy).le) hgle hint (fun j => ∫ y in K j, g j y • y)
    (fun j => rfl) β (by
      filter_upwards [hsum] with x hx
      rw [hx]; exact Finset.sum_congr rfl fun j _ => meanD_mem hG j)
    hsupp v hmarg
  refine ⟨hv0, ?_, ?_⟩
  · rw [← hv0]
    refine ⟨hprob, ⟨s, hsum⟩, fun j => ?_⟩
    show _ = volume.withDensity fun y => ENNReal.ofReal (g j y)
    rw [hmarg j, hv0, wd_restrict (hKm j) (fun z hz => by
      simp [(hG j).zero z hz])]
    congr 1; funext z
    simp [Large.tiltDens, hint j]
  · rw [← hv0]; exact hZ

/-- **Theorem 113 for `n = k + 4`**, with the fixed point taken in a closed convex `Φ`-invariant
set `C ∋ 0` (all of `ℝ^{Fin n × E}` for Theorem 113; the equal-coordinate subset for the
symmetric form). -/
lemma main_k (hS : TychonoffFP.{u}) (hG : ∀ j, Large.InG A L r R (K j) (g j)) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hr : 0 < r) (hrR : r ≤ R) {N : ℕ} {δ : ℕ → ℝ}
    (hδ : LLTprop (E := E) (A2 E A r R) r R N δ) (hk : N ≤ k) (hδ0 : 0 ≤ δ k)
    (hδ2 : δ k ≤ 1 / 2) (hδ3 : 2 * DC E A L r R * δ k * (R + 1) ≤ 1)
    (C : Set (Fin (k + 4) × E → ℝ)) (hC : IsClosed C) (hCc : Convex ℝ C) (hC0 : 0 ∈ C)
    (hCinv : ∀ ψ ∈ Dset K ∩ C, Phi K g ψ ∈ C) :
    ∃ ψ ∈ C, ∃ φ : Fin (k + 4) → E → ℝ,
      (φ = fun j y => ψ (j, y) - ∫ z, ψ (j, z) * g j z) ∧
      (∀ j, ∫ y in K j, φ j y * g j y = 0) ∧
      (∀ j, Large.SupLipLE (K j) (φ j) (2 * DC E A L r R * δ k * (2 * R + 1))) ∧
      IsJointMix (fun j => Large.densMeas (g j))
        (Large.condMeas (Large.lebT (k + 3) (∑ j, Large.meanD (g j)))
          fun j => Large.tiltD (g j) (φ j)) ∧
      ∃ c > 0, ∀ x : Fin (k + 4) → E, (∀ j, x j ∈ K j) →
        c ≤ Large.condProdJ (Large.lebT (k + 3) (∑ j, Large.meanD (g j)))
          (fun j => Large.tiltD (g j) (φ j)) x := by
  obtain ⟨ψ, ⟨hψ, hψC⟩, hfix⟩ := hS (Fin (k + 4) × E) (Dset K ∩ C)
    (Dset_compact.inter_right hC) (Dset_convex.inter hCc) ⟨0, zero_mem_Dset, hC0⟩ (Phi K g)
    ((Phi_cont hG hA hL hr hrR hδ hk hδ2).mono Set.inter_subset_left)
    (fun ψ hψ => ⟨Phi_maps hG hA hL hr hrR hδ hk hδ0 hδ2 hδ3 hψ.1, hCinv ψ hψ⟩)
  obtain ⟨hv0, hmix, hZ⟩ := fixed_mix hG hA hL hr hrR hδ hk hδ2 hψ hfix
  have hK : ∀ j, IsClosed (K j) := fun j => (hG j).compact.isClosed
  set φ : Fin (k + 4) → E → ℝ := fun j y => ψ (j, y) - ∫ z, ψ (j, z) * g j z with hφ
  have hR0 : 0 ≤ R := hr.le.trans hrR
  have hD := DC_nonneg (E := E) hA hL hr hrR
  set b := 2 * DC E A L r R * δ k
  have hb : 0 ≤ b := by positivity
  have hest := fun j => Phi_est hG hA hL hr hrR hδ hk hδ0 hδ2 hψ j
  have hψb : ∀ j, ∀ y ∈ K j, |ψ (j, y)| ≤ b * R := fun j y hy => by
    rw [← hfix]; exact (hest j).1 y hy
  have hint : ∀ j, Integrable fun z => ψ (j, z) * g j z := fun j =>
    ((hG j).integrable.bdd_mul (Dset_meas hψ hK j).aestronglyMeasurable (c := 1)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hψ.2.1 j z))
  have hcb : ∀ j, |∫ z, ψ (j, z) * g j z| ≤ b * R := fun j => by
    rw [← Real.norm_eq_abs]
    calc ‖∫ z, ψ (j, z) * g j z‖ ≤ ∫ z, b * R * g j z := by
          refine norm_integral_le_of_norm_le ((hG j).integrable.const_mul _)
            (Eventually.of_forall fun z => ?_)
          by_cases hz : z ∈ K j
          · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ((hG j).gpos hz)]
            exact mul_le_mul_of_nonneg_right (hψb j z hz) ((hG j).gpos hz).le
          · simp [(hG j).zero z hz]
      _ = b * R := by rw [integral_const_mul, (hG j).int, mul_one]
  have htilt : (fun j => Large.tiltD (g j) (φ j)) = fun j => hTv g ψ 0 j := by
    funext j
    rw [hTv, show uF g ψ 0 j = fun y => ψ (j, y) by funext y; simp [uF]]
    exact tiltD_add_const _ _ _
  refine ⟨ψ, hψC, φ, rfl, fun j => ?_, fun j => ?_, ?_, ?_⟩
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [(hG j).zero y hy]]
    simp only [hφ, sub_mul]
    rw [integral_sub (hint j) ((hG j).integrable.const_mul _), integral_const_mul, (hG j).int]
    ring
  · refine ⟨2 * (b * R), b, by positivity, hb, fun y hy => ?_,
     fun x hx y hy => ?_, by ring_nf; linarith⟩
    · simp only [hφ]
      exact (abs_sub _ _).trans (by linarith [hψb j y hy, hcb j])
    · simp only [hφ, sub_sub_sub_cancel_right]
      rw [← hfix]; exact (hest j).2 x hx y hy
  · rw [htilt]; exact hmix
  · obtain ⟨-, hvV, -⟩ := vT_spec hG hA hr hψ
    have hGH : ∀ j, GH (A2 E A r R) r R (K j) (hTv g ψ 0 j) := fun j =>
      hTv_GH hG hr hψ (by simpa using VB_nonneg (E := E) hA hr hrR) j
    set Z := cvF (k + 3) (fun j => hTv g ψ 0 j) (∑ j, Large.meanD (g j))
    have hvp := fun j => (hGH j).volPos hr
    refine ⟨(∏ j, exp (-A2 E A r R) / volume.real (K j)) / Z,
      div_pos (Finset.prod_pos fun j _ => div_pos (exp_pos _) (hvp j)) hZ, fun x hx => ?_⟩
    rw [htilt, condProdJ_eq _ (fun j => (hGH j).pdg hr)]
    refine div_le_div_of_nonneg_right ?_ hZ.le
    refine Finset.prod_le_prod₀ (fun j _ => div_nonneg (exp_pos _).le (hvp j).le) fun j _ => ?_
    rw [div_le_iff₀' (hvp j)]
    exact (hGH j).low _ (hx j)

end Fixed

end Setup

section Main

/-- The constants `N` and `ε_n` of Theorem 113. -/
lemma constants {A L r R : ℝ} (_hA : 0 ≤ A) (_hL : 0 ≤ L) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ (N0 : ℕ) (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) ∧
      LLTprop (E := E) (A2 E A r R) r R N0 δ ∧ ∀ k ≥ N0, 0 ≤ δ k ∧ δ k ≤ 1 / 2 ∧
        2 * DC E A L r R * δ k * (R + 1) ≤ 1 := by
  obtain ⟨Nδ, δ, hδt, Hδ⟩ := llt_delta_g (E := E) (A := A2 E A r R) hr hrR (2 * R)
  have ht : Tendsto (fun k => |δ k|) atTop (𝓝 0) := by simpa using hδt.abs
  have ht2 : Tendsto (fun k => 2 * DC E A L r R * |δ k| * (R + 1)) atTop (𝓝 0) := by
    simpa using (ht.const_mul (2 * DC E A L r R)).mul_const (R + 1)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((ht.eventually (Iic_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 2))).and (ht2.eventually (Iic_mem_nhds one_pos)))
  refine ⟨max Nδ N1, fun k => |δ k|, ht, fun m hm Ks hs hH y y' hy hy' => ?_,
    fun k hk => ⟨abs_nonneg _, (hN1 k (le_of_max_le_right hk)).1,
      (hN1 k (le_of_max_le_right hk)).2⟩⟩
  obtain ⟨h1, h2⟩ := Hδ m (le_of_max_le_left hm) Ks hs hH y y' hy hy'
  exact ⟨h1, h2.trans (le_abs_self _)⟩

/-- **Theorem 113** (`jl:thm:main`), given Tychonoff's fixed point theorem (`TychonoffFP`).
For `A, L ≥ 0` and `0 < r ≤ R` there are `N` and `ε_n → 0` such that for `n ≥ N` and
`(K_j, g_j) ∈ 𝒢_d(A, L, r, R)` there are `φ_j` with `∫ φ_j g_j = 0` and
`sup |φ_j| + Lip(φ_j) ≤ ε_n` on `K_j` for which the conditioned product of the
`g_j e^{φ_j} / ∫ g_j e^{φ_j}` on `𝒯(K_1, …, K_n; ∑ m_{g_j})` is a joint mix of `g_1, …, g_n`
whose density is bounded below by a positive constant on `𝒯`. -/
theorem thm113 (hS : TychonoffFP.{u}) : Large.Thm113 E := by
  intro A L r R hA hL hr hrR
  obtain ⟨N0, δ, hδt, hδ, hN0⟩ := constants (E := E) hA hL hr hrR
  refine ⟨N0 + 4, fun n => 2 * DC E A L r R * δ (n - 4) * (2 * R + 1), ?_, ?_⟩
  · have := ((hδt.comp (tendsto_sub_atTop_nat 4)).const_mul (2 * DC E A L r R)).mul_const
      (2 * R + 1)
    simpa using this
  intro m hm K g hG
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hk : N0 ≤ k := by omega
  obtain ⟨hδ0, hδ2, hδ3⟩ := hN0 k hk
  obtain ⟨ψ, -, φ, -, h1, h2, h3, c, hc, h4⟩ := main_k (k := k) (K := K) (g := g) hS hG hA hL hr
    hrR hδ hk hδ0 hδ2 hδ3 Set.univ isClosed_univ convex_univ (Set.mem_univ _)
    (fun _ _ => Set.mem_univ _)
  have e : k + 3 + 1 - 4 = k := by omega
  refine ⟨φ, h1, fun j => ?_, h3, c, hc, fun x hx _ => h4 x hx⟩
  show Large.SupLipLE (K j) (φ j) (2 * DC E A L r R * δ (k + 3 + 1 - 4) * (2 * R + 1))
  rw [e]; exact h2 j

/-- **Theorem 113 for equal data, with equal corrections** (`Large.Thm113Sym`), given
`TychonoffFP`: the map `Φ` preserves the set of corrections with equal coordinates. -/
theorem thm113Sym (hS : TychonoffFP.{u}) : Large.Thm113Sym E := by
  intro A L r R hA hL hr hrR
  obtain ⟨N0, δ, hδt, hδ, hN0⟩ := constants (E := E) hA hL hr hrR
  refine ⟨N0 + 4, fun n => 2 * DC E A L r R * δ (n - 4) * (2 * R + 1), ?_, ?_⟩
  · have := ((hδt.comp (tendsto_sub_atTop_nat 4)).const_mul (2 * DC E A L r R)).mul_const
      (2 * R + 1)
    simpa using this
  intro m hm K g hG
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hk : N0 ≤ k := by omega
  obtain ⟨hδ0, hδ2, hδ3⟩ := hN0 k hk
  set C : Set (Fin (k + 4) × E → ℝ) := {ψ | ∀ j y, ψ (j, y) = ψ (0, y)} with hCdef
  have hC : IsClosed C := by
    have e : C = ⋂ j : Fin (k + 4), ⋂ y : E, {ψ : Fin (k + 4) × E → ℝ | ψ (j, y) = ψ (0, y)} := by
      ext ψ; simp [hCdef]
    rw [e]
    exact isClosed_iInter fun j => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) (continuous_apply _)
  have hCc : Convex ℝ C := by
    intro ψ hψ ψ' hψ' a b _ _ _ j y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hψ j y, hψ' j y]
  have hinv : ∀ ψ ∈ Dset (fun _ : Fin (k + 4) => K) ∩ C,
      Phi (fun _ => K) (fun _ => g) ψ ∈ C := by
    rintro ψ ⟨-, hψC⟩ j y
    have hh : ∀ v i, hTv (fun _ => g) ψ v i = hTv (fun _ => g) ψ v 0 := fun v i => by
      have : uF (fun _ => g) ψ v i = uF (fun _ => g) ψ v 0 := by
        funext z; simp only [uF, hψC i z]
      simp only [hTv, this]
    have hf : fJ (fun _ => g) ψ j = fJ (fun _ => g) ψ 0 := by
      simp only [fJ, hh]
    simp only [Phi, hf]
  obtain ⟨ψ, hψC, φ, hφ, h1, h2, h3, -⟩ := main_k (k := k) (K := fun _ => K)
    (g := fun _ => g) hS (fun _ => hG) hA hL hr hrR hδ hk hδ0 hδ2 hδ3 C hC hCc (fun _ _ => rfl)
    hinv
  have hφ0 : ∀ j, φ j = φ 0 := fun j => by
    rw [hφ]; funext y; simp only [hψC j]
  have e : k + 3 + 1 - 4 = k := by omega
  refine ⟨φ 0, h1 0, by
    show Large.SupLipLE K (φ 0) (2 * DC E A L r R * δ (k + 3 + 1 - 4) * (2 * R + 1))
    rw [e]; exact h2 0, ?_⟩
  have hfam : (fun j => Large.tiltD g (φ j)) = fun _ => Large.tiltD g (φ 0) := by
    funext j; rw [hφ0 j]
  have hs : ∑ _j : Fin (k + 4), Large.meanD g = ((k + 3 + 1 : ℕ) : ℝ) • Large.meanD g := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  rw [hfam, hs] at h3
  exact h3

end Main

section Corollaries

open Mixes.Large

/-- **Corollary 114** (`jl:cor:density`) without the hypothesis `Thm113Sym` (John's theorem
`JohnThm` remains an explicit hypothesis). -/
theorem cor114' (hS : TychonoffFP.{u}) (hJ : JohnThm E) (hd : 0 < Module.finrank ℝ E) {A Λ : ℝ}
    (hA : 0 ≤ A) (hΛ : 0 ≤ Λ) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ (K : Set E) (g : E → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
      Measurable g → (∀ y ∉ K, g y = 0) → ∫ y, g y = 1 →
      (∀ y ∈ K, exp (-A) ≤ volume.real K * g y) → (∀ y ∈ K, volume.real K * g y ≤ exp A) →
      (∀ x ∈ K, ∀ y ∈ K, |log (g x) - log (g y)| ≤ Λ / Metric.diam K * dist x y) →
      ∀ m : ℕ, N ≤ m + 1 → ∃ φ : E → ℝ, (∀ y ∈ K, |φ y| ≤ ε (m + 1)) ∧
        IsCompleteMix (m + 1) (densMeas g)
          (condMeas (lebT m (((m + 1 : ℕ) : ℝ) • meanD g)) fun _ => tiltD g φ) :=
  cor114 hJ (thm113Sym hS) hd hA hΛ

/-- **Corollary 115** (`jl:cor:weights`) without the hypothesis `Thm113`. -/
theorem cor115' (hS : TychonoffFP.{u}) {A Lg r R κ : ℝ} (hA : 0 ≤ A) (hLg : 0 ≤ Lg) (hr : 0 < r)
    (hrR : r ≤ R) (hκ : 1 ≤ κ) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ (K : Fin (m + 1) → Set E) (g : Fin (m + 1) → E → ℝ),
      (∀ j, InG A Lg r R (K j) (g j)) → ∀ M : Fin (m + 1) → E ≃L[ℝ] E,
      (∀ j, ‖(M j : E →L[ℝ] E)‖ ≤ κ) → (∀ j, ‖((M j).symm : E →L[ℝ] E)‖ ≤ κ) →
      ∃ φ : Fin (m + 1) → E → ℝ, (∀ j, ∀ y ∈ K j, |φ j y| ≤ ε (m + 1)) ∧
        IsProbabilityMeasure (condMeas ((lebT m (∑ j, M j (meanD (g j)))).map
          (MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0))
          fun j => tiltD (g j) (φ j)) ∧
        (∀ j, (condMeas ((lebT m (∑ j, M j (meanD (g j)))).map
          (MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0))
          fun j => tiltD (g j) (φ j)).map (fun x => x j) = densMeas (g j)) ∧
        ∀ᵐ x ∂(condMeas ((lebT m (∑ j, M j (meanD (g j)))).map
          (MeasurableEquiv.piCongrRight fun j => affE (M j).symm 0))
          fun j => tiltD (g j) (φ j)), ∑ j, M j (x j) = ∑ j, M j (meanD (g j)) :=
  cor115 (thm113 hS) hA hLg hr hrR hκ

/-- **Theorem 121(a)** (`mk:thm:large`) without the hypothesis `Thm113`. -/
theorem thm121_a' (hS : TychonoffFP.{u}) {A Lg r R κ : ℝ} (hA : 0 ≤ A) (hLg : 0 ≤ Lg) (hr : 0 < r)
    (hrR : r ≤ R) (hκ : 1 ≤ κ) :
    ∃ N : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ (Q : Fin (m + 1) → Set E) (q : Fin (m + 1) → E → ℝ),
      (∀ j, InG A Lg r R (Q j) (q j)) →
      ∀ (K : Fin (m + 1) → Set E), (∀ j, MeasurableSet (K j)) → ∀ (a : Fin (m + 1) → E → E)
        (M : Fin (m + 1) → E → E ≃L[ℝ] E) (Γ : E →L[ℝ] E) (c : Fin (m + 1) → E) (s : E),
      (∀ j y, ‖(M j y : E →L[ℝ] E)‖ ≤ κ) → (∀ j y, ‖((M j y).symm : E →L[ℝ] E)‖ ≤ κ) →
      (∀ j, ∀ y ∈ K j, ∀ v ∈ Q j, a j y + M j y v ∈ K j) →
      (∀ j, ∀ y ∈ K j, a j y + M j y (meanD (q j)) = Γ y + c j) → Γ s + ∑ j, c j = s →
      ∀ x ∈ tset K s, ∃ φ : Fin (m + 1) → E → ℝ, (∀ j, ∀ v ∈ Q j, |φ j v| ≤ ε (m + 1)) ∧
        IsJointMix (fun j => affLaw (q j) (a j (x j)) (M j (x j)))
          ((condMeas ((lebT m (∑ j, M j (x j) (meanD (q j)))).map
            (MeasurableEquiv.piCongrRight fun j => affE (M j (x j)).symm 0))
            fun j => tiltD (q j) (φ j)).map fun v j => a j (x j) + M j (x j) (v j)) ∧
        ((condMeas ((lebT m (∑ j, M j (x j) (meanD (q j)))).map
            (MeasurableEquiv.piCongrRight fun j => affE (M j (x j)).symm 0))
            fun j => tiltD (q j) (φ j)).map fun v j => a j (x j) + M j (x j) (v j))
          (tset K s)ᶜ = 0 :=
  Mixes.thm121_a (thm113 hS) hA hLg hr hrR hκ

end Corollaries

end Mixes.Thm113B
