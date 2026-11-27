import Mixes.Robust
open MeasureTheory Set Metric RealInnerProductSpace Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
noncomputable section
namespace Mixes.RobustB
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma qmp_of_le {μ : Measure Y} {ρ : Measure X} {g : X → Y} (hg : Measurable g) {M : ℝ≥0}
    (hle : ρ.map g ≤ (M : ℝ≥0∞) • μ) : QuasiMeasurePreserving g ρ μ := by
  refine ⟨hg.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  refine le_antisymm ((hle s).trans ?_) zero_le
  simp [h0]

lemma eLpNorm_comp_le {μ : Measure Y} {ρ : Measure X} {g : X → Y} (hg : Measurable g) {M : ℝ≥0}
    (hle : ρ.map g ≤ (M : ℝ≥0∞) • μ) {f : Y → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f (g x)) 2 ρ ≤ (M : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm f 2 μ := by
  have hq := qmp_of_le hg hle
  have hf' : AEStronglyMeasurable f (ρ.map g) := hf.mono_ac hq.absolutelyContinuous
  rw [show (fun x => f (g x)) = f ∘ g from rfl, ← eLpNorm_map_measure hf' hg.aemeasurable]
  refine (eLpNorm_mono_measure f hle).trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) f _ hf]
  simp

lemma memLp_comp {μ : Measure Y} {ρ : Measure X} {g : X → Y} (hg : Measurable g) {M : ℝ≥0}
    (hle : ρ.map g ≤ (M : ℝ≥0∞) • μ) (f : Lp ℝ 2 μ) : MemLp (fun x => f (g x)) 2 ρ := by
  refine lt_of_le_of_lt (eLpNorm_comp_le hg hle (Lp.aestronglyMeasurable f)) ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
    (Lp.eLpNorm_lt_top f)

def compLin (μ : Measure Y) (ρ : Measure X) (g : X → Y) (hg : Measurable g) (M : ℝ≥0)
    (hle : ρ.map g ≤ (M : ℝ≥0∞) • μ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ρ where
  toFun f := (memLp_comp hg hle f).toLp _
  map_add' f f' := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have := (qmp_of_le hg hle).ae_eq_comp (Lp.coeFn_add f f')
    filter_upwards [this] with x hx
    simpa using hx
  map_smul' a f := by
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have := (qmp_of_le hg hle).ae_eq_comp (Lp.coeFn_smul a f)
    filter_upwards [this] with x hx
    simpa using hx

def compOp (μ : Measure Y) (ρ : Measure X) (g : X → Y) (hg : Measurable g) (M : ℝ≥0)
    (hle : ρ.map g ≤ (M : ℝ≥0∞) • μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ρ :=
  (compLin μ ρ g hg M hle).mkContinuous ((M : ℝ) ^ (1 / 2 : ℝ)) fun f => by
    change ‖(memLp_comp hg hle f).toLp _‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def]
    have h := eLpNorm_comp_le hg hle (Lp.aestronglyMeasurable f)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top).ne
      (Lp.eLpNorm_ne_top f)) h
    rw [ENNReal.toReal_mul] at h2
    convert h2 using 2
    rw [← ENNReal.toReal_rpow]; simp

lemma compOp_ae {μ : Measure Y} {ρ : Measure X} {g : X → Y} (hg : Measurable g) {M : ℝ≥0}
    (hle : ρ.map g ≤ (M : ℝ≥0∞) • μ) (f : Lp ℝ 2 μ) :
    compOp μ ρ g hg M hle f =ᵐ[ρ] fun x => f (g x) :=
  MemLp.coeFn_toLp (memLp_comp hg hle f)

def intFun (μ : Measure Y) (ν : Measure Y) [IsFiniteMeasure ν] (C : ℝ≥0)
    (hν : ν ≤ (C : ℝ≥0∞) • μ) : StrongDual ℝ (Lp ℝ 2 μ) :=
  (innerSL ℝ (MemLp.toLp (fun _ : Y => (1 : ℝ)) (memLp_const 1) : Lp ℝ 2 ν)).comp
    (compOp μ ν id measurable_id C (by simpa using hν))

lemma intFun_apply (μ : Measure Y) (ν : Measure Y) [IsFiniteMeasure ν] (C : ℝ≥0)
    (hν : ν ≤ (C : ℝ≥0∞) • μ) (ψ : Lp ℝ 2 μ) : intFun μ ν C hν ψ = ∫ y, ψ y ∂ν := by
  simp only [intFun, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1:ℝ)) (μ := ν) (p := 2),
    compOp_ae measurable_id (M := C) (by simpa using hν) ψ] with y h1 h2
  rw [h1, h2]; simp

/-- **Cited hypothesis** (Hilbert–Schmidt): on a finite measure space, an integral operator on
`L²(μ)` with a bounded measurable kernel `k` on `V × V` is compact. -/
def HSCompact (V : Type*) [MeasurableSpace V] : Prop :=
  ∀ (μ : Measure V), IsFiniteMeasure μ → ∀ (k : V × V → ℝ), Measurable k →
    ∀ M : ℝ, (∀ z, 0 ≤ k z ∧ k z ≤ M) → ∀ T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      (∀ f g : Lp ℝ 2 μ, ⟪T f, g⟫ = ∫ z, k z * (f z.1 * g z.2) ∂(μ.prod μ)) →
      IsCompactOperator T

lemma compact_of_pair {V : Type*} [MeasurableSpace V] (hHS : HSCompact V) (μ : Measure V)
    [IsFiniteMeasure μ] {π : Measure (V × V)} [IsFiniteMeasure π] {M' : ℝ≥0}
    (hπ : π ≤ (M' : ℝ≥0∞) • μ.prod μ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f g : Lp ℝ 2 μ, ⟪T f, g⟫ = ∫ z, f z.1 * g z.2 ∂π) : IsCompactOperator T := by
  set ν := μ.prod μ with hν
  have hac : π ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs h0 => by
    refine le_antisymm ((hπ s).trans ?_) zero_le
    simp [h0]
  set r := π.rnDeriv ν with hr
  have hrle : r ≤ᵐ[ν] fun _ => (M' : ℝ≥0∞) := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
      fun s hs _ => ?_
    refine (Measure.setLIntegral_rnDeriv_le s).trans ((hπ s).trans ?_)
    rw [setLIntegral_const]; simp
  have hrlt : ∀ᵐ z ∂ν, r z < ∞ := hrle.mono fun z hz => lt_of_le_of_lt hz ENNReal.coe_lt_top
  refine hHS μ inferInstance (fun z => min (r z).toReal M')
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const) M'
    (fun z => ⟨le_min ENNReal.toReal_nonneg M'.2, min_le_right _ _⟩) T fun f g => ?_
  rw [hT, ← Measure.withDensity_rnDeriv_eq π ν hac,
    integral_withDensity_eq_integral_toReal_smul₀ (Measure.measurable_rnDeriv _ _).aemeasurable
      hrlt]
  refine integral_congr_ae ?_
  filter_upwards [hrle] with z hz
  rw [smul_eq_mul, ← hr]
  congr 1
  rw [min_eq_left]
  exact ENNReal.toReal_le_of_le_ofReal M'.2 (by simpa using hz)

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {n : ℕ}
  (μ : Measure V) [IsFiniteMeasure μ] (lam : Measure (Fin n → V)) [IsFiniteMeasure lam]
  (M : ℝ≥0) (hM : ∀ i, lam.map (fun x => x i) ≤ (M : ℝ≥0∞) • μ)

def Sop (i : Fin n) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 lam :=
  compOp μ lam (fun x => x i) (measurable_pi_apply i) M (hM i)

def Sav : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 lam := (n : ℝ)⁻¹ • ∑ i, Sop μ lam M hM i

def Gop : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.adjoint (Sav μ lam M hM)).comp (Sav μ lam M hM)

lemma real_inner_eq (a b : ℝ) : ⟪a, b⟫ = a * b := by
  simp [mul_comm]

lemma Sop_ae (i : Fin n) (φ : Lp ℝ 2 μ) : Sop μ lam M hM i φ =ᵐ[lam] fun x => φ (x i) :=
  compOp_ae _ _ φ

include hM in
lemma qmp_i (i : Fin n) : QuasiMeasurePreserving (fun x : Fin n → V => x i) lam μ :=
  qmp_of_le (measurable_pi_apply i) (hM i)

include hM in
lemma comp_ae (i : Fin n) {f g : V → ℝ} (h : f =ᵐ[μ] g) :
    (fun x : Fin n → V => f (x i)) =ᵐ[lam] fun x => g (x i) :=
  (qmp_i μ lam M hM i).ae_eq_comp h

lemma sum_Sop_ae (s : Finset (Fin n)) (φ : Lp ℝ 2 μ) :
    (∑ i ∈ s, Sop μ lam M hM i φ : Lp ℝ 2 lam) =ᵐ[lam] fun x => ∑ i ∈ s, φ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 lam] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (Sop μ lam M hM a φ) (∑ i ∈ s, Sop μ lam M hM i φ),
      Sop_ae μ lam M hM a φ, ih] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert ha]

lemma Sav_ae (φ : Lp ℝ 2 μ) :
    Sav μ lam M hM φ =ᵐ[lam] fun x => (n : ℝ)⁻¹ * ∑ i, φ (x i) := by
  have h1 : Sav μ lam M hM φ = (n : ℝ)⁻¹ • ∑ i, Sop μ lam M hM i φ := by
    simp [Sav]
  rw [h1]
  filter_upwards [Lp.coeFn_smul (n : ℝ)⁻¹ (∑ i, Sop μ lam M hM i φ),
    sum_Sop_ae μ lam M hM Finset.univ φ] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

lemma inner_Gop_Sav (φ ψ : Lp ℝ 2 μ) :
    ⟪Gop μ lam M hM φ, ψ⟫ = ⟪Sav μ lam M hM φ, Sav μ lam M hM ψ⟫ := by
  rw [Gop, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

lemma inner_Gop (φ ψ : Lp ℝ 2 μ) :
    ⟪Gop μ lam M hM φ, ψ⟫ =
      ∫ x, ((n : ℝ)⁻¹ * ∑ i, φ (x i)) * ((n : ℝ)⁻¹ * ∑ i, ψ (x i)) ∂lam := by
  rw [inner_Gop_Sav, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Sav_ae μ lam M hM φ, Sav_ae μ lam M hM ψ] with x h1 h2
  rw [real_inner_eq, h1, h2]

lemma inner_Sop_Sop (i j : Fin n) (f g : Lp ℝ 2 μ) :
    ⟪Sop μ lam M hM j f, Sop μ lam M hM i g⟫ = ∫ x, f (x j) * g (x i) ∂lam := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Sop_ae μ lam M hM j f, Sop_ae μ lam M hM i g] with x h1 h2
  rw [real_inner_eq, h1, h2]

/-- `Sᵢ* Sⱼ`. -/
def Top (i j : Fin n) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.adjoint (Sop μ lam M hM i)).comp (Sop μ lam M hM j)

lemma inner_Top (i j : Fin n) (f g : Lp ℝ 2 μ) :
    ⟪Top μ lam M hM i j f, g⟫ = ⟪Sop μ lam M hM j f, Sop μ lam M hM i g⟫ := by
  rw [Top, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

def Mop : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := ((n : ℝ)⁻¹ ^ 2) • ∑ i, Top μ lam M hM i i

def Cop : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ((n : ℝ)⁻¹ ^ 2) • ∑ i, ∑ j, if i = j then 0 else Top μ lam M hM i j

lemma inner_Sav (φ ψ : Lp ℝ 2 μ) :
    ⟪Sav μ lam M hM φ, Sav μ lam M hM ψ⟫ = (n : ℝ)⁻¹ ^ 2 *
      ∑ i, ∑ j, ⟪Sop μ lam M hM j φ, Sop μ lam M hM i ψ⟫ := by
  simp only [Sav, smul_apply, sum_apply,
    real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  simp only [← Finset.mul_sum]
  rw [← mul_assoc, sq]

lemma Gop_eq : Gop μ lam M hM = Mop μ lam M hM + Cop μ lam M hM := by
  refine ContinuousLinearMap.ext fun φ => ext_inner_right ℝ fun ψ => ?_
  rw [inner_Gop_Sav, inner_Sav, add_apply, inner_add_left]
  simp only [Mop, Cop, smul_apply, sum_apply,
    real_inner_smul_left, sum_inner]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_Top]
  have : ∀ j, ⟪Sop μ lam M hM j φ, Sop μ lam M hM i ψ⟫ =
      (if i = j then ⟪Sop μ lam M hM j φ, Sop μ lam M hM i ψ⟫ else 0) +
      ⟪(if i = j then 0 else Top μ lam M hM i j) φ, ψ⟫ := fun j => by
    split_ifs with h
    · subst h; simp
    · simp [inner_Top]
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

lemma ac_of_le_smul {Z : Type*} [MeasurableSpace Z] {π ν : Measure Z} {M' : ℝ≥0}
    (h : π ≤ (M' : ℝ≥0∞) • ν) : π ≪ ν :=
  Measure.AbsolutelyContinuous.mk fun s _ h0 => by
    refine le_antisymm ((h s).trans ?_) zero_le
    simp [h0]

lemma inner_Top_pair (i j : Fin n) {M' : ℝ≥0}
    (hπ : lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ) (f g : Lp ℝ 2 μ) :
    ⟪Top μ lam M hM i j f, g⟫ = ∫ z, f z.1 * g z.2 ∂(lam.map fun x => (x j, x i)) := by
  rw [inner_Top, inner_Sop_Sop, integral_map]
  · exact ((measurable_pi_apply j).prodMk (measurable_pi_apply i)).aemeasurable
  · exact ((Lp.aestronglyMeasurable f).comp_fst.mul
      (Lp.aestronglyMeasurable g).comp_snd).mono_ac (ac_of_le_smul hπ)

lemma isCompactOperator_finsum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} (s : Finset ι) (T : ι → E →L[ℝ] F)
    (h : ∀ i ∈ s, IsCompactOperator (T i)) : IsCompactOperator ⇑(∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero (M₁ := E) (M₂ := F))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Cop_compact (hHS : HSCompact V) {M' : ℝ≥0}
    (hpair : ∀ i j, i ≠ j → lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ) :
    IsCompactOperator (Cop μ lam M hM) := by
  rw [Cop, show ∀ (c : ℝ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), ⇑(c • T) = c • ⇑T from fun _ _ => rfl]
  refine IsCompactOperator.smul (isCompactOperator_finsum _ _ fun i _ =>
    isCompactOperator_finsum _ _ fun j _ => ?_) _
  split_ifs with h
  · simpa using (isCompactOperator_zero (M₁ := Lp ℝ 2 μ) (M₂ := Lp ℝ 2 μ))
  · exact compact_of_pair hHS μ (hpair i j h) _ (inner_Top_pair μ lam M hM i j (hpair i j h))

lemma Gop_pos (x : Lp ℝ 2 μ) : 0 ≤ ⟪Gop μ lam M hM x, x⟫ := by
  rw [inner_Gop_Sav]; exact real_inner_self_nonneg

lemma Gop_sym (x y : Lp ℝ 2 μ) : ⟪Gop μ lam M hM x, y⟫ = ⟪x, Gop μ lam M hM y⟫ := by
  rw [inner_Gop_Sav, ← real_inner_comm x, inner_Gop_Sav, real_inner_comm]

lemma Sop_sq_ge {α : ℝ≥0} (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    (x : Lp ℝ 2 μ) :
    (α : ℝ) * ⟪x, x⟫ ≤ ⟪Sop μ lam M hM i0 x, Sop μ lam M hM i0 x⟫ := by
  have hmeas : AEMeasurable (fun y : Fin n → V => y i0) lam := (measurable_pi_apply i0).aemeasurable
  have hac : lam.map (fun y => y i0) ≪ μ := ac_of_le_smul (hM i0)
  have haes : AEStronglyMeasurable (fun z => x z * x z) (lam.map fun y => y i0) :=
    ((Lp.aestronglyMeasurable x).mul (Lp.aestronglyMeasurable x)).mono_ac hac
  rw [inner_Sop_Sop, ← integral_map hmeas haes, L2.inner_def]
  have hint : Integrable (fun z => x z * x z) (lam.map fun y => y i0) := by
    rw [integrable_map_measure haes hmeas]
    have := L2.integrable_inner (𝕜 := ℝ) (Sop μ lam M hM i0 x) (Sop μ lam M hM i0 x)
    refine this.congr ?_
    filter_upwards [Sop_ae μ lam M hM i0 x] with y hy
    simp only [Function.comp_apply, real_inner_eq, hy]
  have h1 := integral_mono_measure hlow
    (Filter.Eventually.of_forall fun z => mul_self_nonneg (x z)) hint
  rw [integral_smul_measure] at h1
  simp only [real_inner_eq]
  simpa using h1

/-- The multiplication part `M = n⁻² ∑ Sᵢ* Sᵢ` is bounded below. -/
lemma Mop_ge {α : ℝ≥0} (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    (x : Lp ℝ 2 μ) : (n : ℝ)⁻¹ ^ 2 * α * ‖x‖ ^ 2 ≤ ⟪Mop μ lam M hM x, x⟫ := by
  have h1 : ⟪Mop μ lam M hM x, x⟫ =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ⟪Sop μ lam M hM i x, Sop μ lam M hM i x⟫ := by
    simp only [Mop, smul_apply, sum_apply, real_inner_smul_left, sum_inner, inner_Top]
  rw [h1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (Finset.single_le_sum (f := fun i =>
    ⟪Sop μ lam M hM i x, Sop μ lam M hM i x⟫) (fun i _ => real_inner_self_nonneg)
    (Finset.mem_univ i0))
  have := Sop_sq_ge μ lam M hM i0 hlow x
  rwa [real_inner_self_eq_norm_sq] at this

lemma Mop_norm_ge {α : ℝ≥0} (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    (x : Lp ℝ 2 μ) : (n : ℝ)⁻¹ ^ 2 * α * ‖x‖ ≤ ‖Mop μ lam M hM x‖ := by
  have h1 := Mop_ge μ lam M hM i0 hlow x
  have h2 : ⟪Mop μ lam M hM x, x⟫ ≤ ‖Mop μ lam M hM x‖ * ‖x‖ := real_inner_le_norm _ _
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h]; simp
  · nlinarith

lemma l1_le (ψ : Lp ℝ 2 μ) : ∫ y, |ψ y| ∂μ ≤ Real.sqrt (μ.real univ) * ‖ψ‖ := by
  have aes := Lp.aestronglyMeasurable ψ
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) aes
  have e1 : ∫ y, |ψ y| ∂μ = (eLpNorm ψ 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_eNorm aes, ← integral_norm_eq_lintegral_eNorm aes]
    rfl
  have h' : eLpNorm ψ 1 μ ≤ eLpNorm ψ 2 μ * μ univ ^ (1 / 2 : ℝ) := by
    convert h using 3; norm_num
  rw [e1]
  calc (eLpNorm ψ 1 μ).toReal ≤ (eLpNorm ψ 2 μ * μ univ ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top ψ)
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ))) h'
    _ = Real.sqrt (μ.real univ) * ‖ψ‖ := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def, Real.sqrt_eq_rpow,
          measureReal_def, mul_comm]

lemma linfty_upper {M' : ℝ≥0}
    (hpair : ∀ i j, i ≠ j → lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ)
    {α : ℝ≥0} (hα : 0 < α) (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    (φ : Lp ℝ 2 μ) {H : ℝ} (hH : 0 ≤ H)
    (hh : ∀ ψ : Lp ℝ 2 μ, ⟪Gop μ lam M hM φ, ψ⟫ ≤ H * ∫ y, |ψ y| ∂μ) :
    ∀ᵐ y ∂μ, φ y ≤ (n : ℝ) ^ 2 * (H + M' * ∫ y, |φ y| ∂μ) / α := by
  set φ' := (Lp.aestronglyMeasurable φ).mk φ with hφ'def
  have hφ'm : Measurable φ' := (Lp.aestronglyMeasurable φ).stronglyMeasurable_mk.measurable
  have hφφ' : (φ : V → ℝ) =ᵐ[μ] φ' := (Lp.aestronglyMeasurable φ).ae_eq_mk
  set L := ∫ y, |φ y| ∂μ with hLdef
  have hL : 0 ≤ L := integral_nonneg fun _ => abs_nonneg _
  have hαr : (0 : ℝ) < α := hα
  set B := (n : ℝ) ^ 2 * (H + M' * L) / α with hBdef
  have hB : 0 ≤ B := by positivity
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i0)
  have hint : ∀ j, Integrable (fun x : Fin n → V => φ' (x j)) lam := fun j => by
    have := (Lp.memLp (Sop μ lam M hM j φ)).integrable one_le_two
    refine this.congr ?_
    filter_upwards [Sop_ae μ lam M hM j φ, comp_ae μ lam M hM j hφφ'] with x h1 h2
    rw [h1]; exact h2
  have hintφ' : Integrable φ' μ := ((Lp.memLp φ).integrable one_le_two).congr hφφ'
  have hLφ' : ∫ y, |φ' y| ∂μ = L := by
    refine integral_congr_ae ?_
    filter_upwards [hφφ'] with y hy
    rw [hy]
  have hkey : ∀ t, B < t → μ {y | t < φ' y} = 0 := by
    intro t ht
    have ht0 : 0 ≤ t := hB.trans ht.le
    set A := {y | t < φ' y} with hAdef
    have hA : MeasurableSet A := measurableSet_lt measurable_const hφ'm
    set ψ : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) with hψdef
    have hψ : (ψ : V → ℝ) =ᵐ[μ] A.indicator 1 := indicatorConstLp_coeFn
    have hψabs : ∫ y, |ψ y| ∂μ = μ.real A := by
      rw [← integral_indicator_one hA]
      refine integral_congr_ae ?_
      filter_upwards [hψ] with y hy
      rw [hy]
      by_cases hy : y ∈ A <;> simp [Set.indicator, hy]
    have hpre : ∀ i, MeasurableSet ((fun x : Fin n → V => x i) ⁻¹' A) := fun i =>
      hA.preimage (measurable_pi_apply i)
    set I : Fin n → Fin n → ℝ := fun i j =>
      ∫ x, ((fun x : Fin n → V => x i) ⁻¹' A).indicator (fun x => φ' (x j)) x ∂lam with hIdef
    have hI : ∀ i j, ⟪Sop μ lam M hM j φ, Sop μ lam M hM i ψ⟫ = I i j := by
      intro i j
      rw [inner_Sop_Sop]
      refine integral_congr_ae ?_
      filter_upwards [comp_ae μ lam M hM j hφφ', comp_ae μ lam M hM i hψ] with x h1 h2
      rw [h1, h2]
      by_cases hx : x i ∈ A <;> simp [Set.indicator, hx]
    have hdiag : ∀ i, t * lam.real ((fun x : Fin n → V => x i) ⁻¹' A) ≤ I i i := by
      intro i
      rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const t (hpre i)]
      refine integral_mono ((integrable_const t).indicator (hpre i)) ((hint i).indicator (hpre i))
        fun x => ?_
      by_cases hx : x i ∈ A
      · simp only [Set.indicator, Set.mem_preimage, hx, ite_true]
        exact hx.le
      · simp [Set.indicator, hx]
    have hlowA : (α : ℝ) * μ.real A ≤ lam.real ((fun x : Fin n → V => x i0) ⁻¹' A) := by
      have h1 := hlow A
      rw [Measure.map_apply (measurable_pi_apply i0) hA, smul_apply, smul_eq_mul] at h1
      have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
      rw [ENNReal.toReal_mul] at h2
      simpa [measureReal_def] using h2
    have hoff : ∀ i j, i ≠ j → -(M' * L * μ.real A) ≤ I i j := by
      intro i j hij
      refine neg_le_of_abs_le (abs_integral_le_integral_abs.trans ?_)
      have hpm : Measurable fun x : Fin n → V => (x j, x i) :=
        (measurable_pi_apply j).prodMk (measurable_pi_apply i)
      have hGm : Measurable fun z : V × V => |φ' z.1| * A.indicator 1 z.2 :=
        (hφ'm.comp measurable_fst).abs.mul ((measurable_const.indicator hA).comp measurable_snd)
      have e1 : ∫ x, |((fun x : Fin n → V => x i) ⁻¹' A).indicator (fun x => φ' (x j)) x| ∂lam =
          ∫ z, |φ' z.1| * A.indicator 1 z.2 ∂(lam.map fun x => (x j, x i)) := by
        rw [integral_map hpm.aemeasurable hGm.aestronglyMeasurable]
        congr 1
        ext x
        by_cases hx : x i ∈ A <;> simp [Set.indicator, hx]
      rw [e1]
      have hG : Integrable (fun z : V × V => |φ' z.1| * A.indicator 1 z.2) (μ.prod μ) :=
        hintφ'.abs.mul_prod ((integrable_const (1 : ℝ)).indicator hA)
      refine (integral_mono_measure (hpair i j hij) (Filter.Eventually.of_forall fun z =>
        mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (hG.smul_measure ENNReal.coe_ne_top)).trans (le_of_eq ?_)
      rw [integral_smul_measure, integral_prod_mul (fun y => |φ' y|) (A.indicator 1),
        integral_indicator_one hA, hLφ']
      simp [mul_assoc]
    have hlow2 : ∀ i j, (if i = i0 then (if j = i0 then t * α * μ.real A else 0) else 0)
        - M' * L * μ.real A ≤ I i j := by
      intro i j
      have hMLA : 0 ≤ (M' : ℝ) * L * μ.real A := by positivity
      by_cases hij : i = j
      · subst hij
        have h1 := hdiag i
        have h2 : 0 ≤ t * lam.real ((fun x : Fin n → V => x i) ⁻¹' A) := by positivity
        by_cases hi : i = i0
        · subst hi
          simp only [ite_true]
          have : t * α * μ.real A ≤ t * lam.real ((fun x : Fin n → V => x i) ⁻¹' A) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlowA ht0
          linarith
        · simp only [hi, ite_false]; linarith
      · have h1 := hoff i j hij
        have : (if i = i0 then (if j = i0 then t * α * μ.real A else 0) else 0) = 0 := by
          by_cases hi : i = i0
          · have hj : j ≠ i0 := fun h => hij (hi.trans h.symm)
            simp [hi, hj]
          · simp [hi]
        rw [this]; linarith
    have hsum : t * α * μ.real A - (n : ℝ) * n * (M' * L * μ.real A) ≤ ∑ i, ∑ j, I i j := by
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hlow2 i j)
      simp [Finset.sum_sub_distrib]
      ring
    have hinner : ⟪Gop μ lam M hM φ, ψ⟫ = (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, I i j := by
      rw [inner_Gop_Sav, inner_Sav]
      simp only [hI]
    have hle := hh ψ
    rw [hinner, hψabs] at hle
    have hμA0 : 0 ≤ μ.real A := measureReal_nonneg
    have h3 : t * α * μ.real A - (n : ℝ) * n * (M' * L * μ.real A) ≤ n ^ 2 * (H * μ.real A) := by
      have h4 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
      have e : (n : ℝ) ^ 2 * (n : ℝ)⁻¹ ^ 2 = 1 := by field_simp
      rw [← mul_assoc, e, one_mul] at h4
      linarith
    have htB : (n : ℝ) ^ 2 * (H + M' * L) < t * α := by
      have := (div_lt_iff₀ hαr).1 ht
      linarith
    have hreal : μ.real A ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have : (n : ℝ) ^ 2 * (H + M' * L) * μ.real A < t * α * μ.real A :=
        mul_lt_mul_of_pos_right htB hcon
      nlinarith
    have : μ.real A = 0 := le_antisymm hreal hμA0
    rwa [measureReal_eq_zero_iff (measure_ne_top μ A)] at this
  have hnull : μ {y | B < φ' y} = 0 := by
    refine measure_mono_null (t := ⋃ k : ℕ, {y | B + 1 / ((k : ℝ) + 1) < φ' y}) ?_
      (measure_iUnion_null fun k => hkey _ (by
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith))
    intro y hy
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (show B < φ' y from hy))
    exact mem_iUnion.2 ⟨k, show B + 1 / ((k : ℝ) + 1) < φ' y by linarith⟩
  have hae : ∀ᵐ y ∂μ, φ' y ≤ B := by
    rw [ae_iff]
    simpa [not_le] using hnull
  filter_upwards [hae, hφφ'] with y h1 h2
  rw [h2]; exact h1

lemma linfty_abs {M' : ℝ≥0}
    (hpair : ∀ i j, i ≠ j → lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ)
    {α : ℝ≥0} (hα : 0 < α) (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    (φ : Lp ℝ 2 μ) {H : ℝ} (hH : 0 ≤ H)
    (hh : ∀ ψ : Lp ℝ 2 μ, |⟪Gop μ lam M hM φ, ψ⟫| ≤ H * ∫ y, |ψ y| ∂μ) :
    ∀ᵐ y ∂μ, |φ y| ≤ (n : ℝ) ^ 2 * (H + M' * ∫ y, |φ y| ∂μ) / α := by
  have h1 := linfty_upper μ lam M hM hpair hα i0 hlow φ hH fun ψ => (le_abs_self _).trans (hh ψ)
  have h2 := linfty_upper μ lam M hM hpair hα i0 hlow (-φ) hH fun ψ => by
    rw [map_neg, inner_neg_left]
    exact (neg_le_abs _).trans (hh ψ)
  have hL : ∫ y, |(-φ : Lp ℝ 2 μ) y| ∂μ = ∫ y, |φ y| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg φ] with y hy
    rw [hy, Pi.neg_apply, abs_neg]
  rw [hL] at h2
  filter_upwards [h1, h2, Lp.coeFn_neg φ] with y hy1 hy2 hy3
  rw [hy3, Pi.neg_apply] at hy2
  exact abs_le.2 ⟨by linarith, hy1⟩

lemma memLp_ell (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V) (f : StrongDual ℝ V) :
    MemLp (fun y => f (y - c)) 2 μ := by
  obtain ⟨R, hR⟩ := hbdd
  refine MemLp.of_bound
    (f.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (‖f‖ * (R + ‖c‖)) (hR.mono fun y hy => ?_)
  calc ‖f (y - c)‖ ≤ ‖f‖ * ‖y - c‖ := f.le_opNorm _
    _ ≤ ‖f‖ * (R + ‖c‖) := mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith))
        (norm_nonneg _)

/-- `f ↦ f(· - c)`, the linear functions about `c`, in `L²(μ)`. -/
def ellL (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V) : (StrongDual ℝ V) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_ell μ hbdd c f).toLp _
  map_add' f f' := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' a f := by
    rw [← MemLp.toLp_const_smul]
    rfl

lemma ellL_ae (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V) (f : StrongDual ℝ V) :
    ellL μ hbdd c f =ᵐ[μ] fun y => f (y - c) :=
  MemLp.coeFn_toLp (memLp_ell μ hbdd c f)

/-- The subspace of linear functions about `c`. -/
def Vlin (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V) : Submodule ℝ (Lp ℝ 2 μ) :=
  LinearMap.range (ellL μ hbdd c)

lemma Sav_ell (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V)
    (hsum : ∀ᵐ x ∂lam, ∑ i, x i = (n : ℝ) • c) (f : StrongDual ℝ V) :
    Sav μ lam M hM (ellL μ hbdd c f) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hall : ∀ᵐ x ∂lam, ∀ i, (ellL μ hbdd c f) (x i) = f (x i - c) :=
    ae_all_iff.2 fun i => comp_ae μ lam M hM i (ellL_ae μ hbdd c f)
  filter_upwards [Sav_ae μ lam M hM (ellL μ hbdd c f), hall, hsum] with x h1 h2 h3
  rw [h1, Pi.zero_apply]
  simp only [h2]
  rw [← map_sum, Finset.sum_sub_distrib, h3]
  simp

lemma Gop_mem_orth (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V)
    (hsum : ∀ᵐ x ∂lam, ∑ i, x i = (n : ℝ) • c) (x : Lp ℝ 2 μ) :
    Gop μ lam M hM x ∈ (Vlin μ hbdd c)ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro u ⟨f, rfl⟩
  rw [real_inner_comm, inner_Gop_Sav, Sav_ell μ lam M hM hbdd c hsum f, inner_zero_right]

lemma Gop_ker (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V)
    (hsum : ∀ᵐ x ∂lam, ∑ i, x i = (n : ℝ) • c)
    {α : ℝ≥0} (hα : 0 < α) (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    {M' : ℝ≥0} (hpair : ∀ i j, i ≠ j →
      lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ)
    (hker : ∀ φ : V → ℝ, Measurable φ → (∃ C, ∀ y, |φ y| ≤ C) →
      (∀ᵐ x ∂lam, ∑ i, φ (x i) = 0) →
      ∃ (a : ℝ) (f : StrongDual ℝ V), ∀ᵐ y ∂μ, φ y = a + f y)
    (x : Lp ℝ 2 μ) (hx : x ∈ (Vlin μ hbdd c)ᗮ) (hGx : Gop μ lam M hM x = 0) : x = 0 := by
  rcases eq_or_ne μ 0 with hμ0 | hμ0
  · rw [Lp.eq_zero_iff_ae_eq_zero]
    exact measure_mono_null (subset_univ _) (by simp [hμ0])
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i0)
  have hSx : Sav μ lam M hM x = 0 := by
    have := inner_Gop_Sav μ lam M hM x x
    rw [hGx, inner_zero_left] at this
    exact inner_self_eq_zero.1 this.symm
  have hsumx : ∀ᵐ y ∂lam, ∑ i, x (y i) = 0 := by
    filter_upwards [Sav_ae μ lam M hM x, Lp.coeFn_zero ℝ 2 lam, hSx ▸ Sav_ae μ lam M hM x]
      with y h1 h2 h3
    have h4 : (Sav μ lam M hM x : (Fin n → V) → ℝ) y = 0 := by
      rw [hSx]; simpa using h2
    rw [h1] at h4
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (inv_ne_zero hn.ne')
    · exact h
  set B := (n : ℝ) ^ 2 * (0 + M' * ∫ y, |x y| ∂μ) / α with hB
  have hαr : (0 : ℝ) < α := hα
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∫ y, |x y| ∂μ := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hbd := linfty_abs μ lam M hM hpair hα i0 hlow x le_rfl fun ψ => by
    rw [hGx, inner_zero_left]; simp
  set x' := (Lp.aestronglyMeasurable x).mk x
  have hx'm : Measurable x' := (Lp.aestronglyMeasurable x).stronglyMeasurable_mk.measurable
  have hxx' : (x : V → ℝ) =ᵐ[μ] x' := (Lp.aestronglyMeasurable x).ae_eq_mk
  set φ : V → ℝ := fun y => max (-B) (min B (x' y)) with hφ
  have hφm : Measurable φ := measurable_const.max (measurable_const.min hx'm)
  have hφb : ∀ y, |φ y| ≤ B := fun y =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hxφ : (x : V → ℝ) =ᵐ[μ] φ := by
    filter_upwards [hbd, hxx'] with y h1 h2
    have h1' : |x y| ≤ B := h1
    show x y = max (-B) (min B (x' y))
    rw [← h2, min_eq_right (abs_le.1 h1').2, max_eq_right (abs_le.1 h1').1]
  have hsumφ : ∀ᵐ y ∂lam, ∑ i, φ (y i) = 0 := by
    have hall : ∀ᵐ y ∂lam, ∀ i, x (y i) = φ (y i) :=
      ae_all_iff.2 fun i => comp_ae μ lam M hM i hxφ
    filter_upwards [hall, hsumx] with y h1 h2
    simp only [← h1]; exact h2
  obtain ⟨a, f, haf⟩ := hker φ hφm ⟨B, hφb⟩ hsumφ
  have hlam : lam ≠ 0 := by
    intro h0
    have h1 := hlow univ
    rw [h0, Measure.map_zero] at h1
    simp only [smul_apply, smul_eq_mul, FunLike.coe_zero, Pi.zero_apply,
      nonpos_iff_eq_zero, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact (ne_of_gt hα) (by exact_mod_cast h)
    · exact hμ0 (Measure.measure_univ_eq_zero.1 h)
  have hac : ∀ᵐ y ∂lam, ∀ i, φ (y i) = a + f (y i) :=
    ae_all_iff.2 fun i => comp_ae μ lam M hM i haf
  have : Filter.NeBot (ae lam) := ae_neBot.2 hlam
  obtain ⟨y, hy1, hy2, hy3⟩ := (hsumφ.and (hac.and hsum)).exists
  have ha : a = -f c := by
    simp only [hy2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← map_sum, hy3, map_smul, nsmul_eq_mul, smul_eq_mul] at hy1
    have : (n : ℝ) * (a + f c) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hn.ne'
    · linarith
  have hxe : x = ellL μ hbdd c f := by
    refine Lp.ext ?_
    filter_upwards [hxφ, haf, ellL_ae μ hbdd c f] with y h1 h2 h3
    rw [h1, h2, h3, ha, map_sub]; ring
  have hxin : x ∈ Vlin μ hbdd c := hxe ▸ ⟨f, rfl⟩
  exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hxin hx)

/-- **The linear correction of Theorem 91, abstractly.** Let `λ` be a finite measure on
`n`-tuples with sum `n c`, whose coordinates have bounded densities with respect to `μ`, whose
coordinate `i₀` has density at least `α > 0`, and whose pairs of distinct coordinates have bounded
densities with respect to `μ ⊗ μ`, and suppose that `∑ φ(xᵢ) = 0` `λ`-a.e. forces a bounded `φ`
to be affine `μ`-a.e. Then (given the cited compactness `HSCompact`) there is `C` such that every
`h ⊥` linear functions with `|⟪h, ψ⟫| ≤ H ∫ |ψ| dμ` is `Gφ` for some `φ` with `|φ| ≤ C H` a.e. -/
theorem abstract_main (hHS : HSCompact V) (hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R) (c : V)
    (hsum : ∀ᵐ x ∂lam, ∑ i, x i = (n : ℝ) • c)
    {α : ℝ≥0} (hα : 0 < α) (i0 : Fin n) (hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x i0))
    {M' : ℝ≥0} (hpair : ∀ i j, i ≠ j →
      lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ)
    (hker : ∀ φ : V → ℝ, Measurable φ → (∃ C, ∀ y, |φ y| ≤ C) →
      (∀ᵐ x ∂lam, ∑ i, φ (x i) = 0) →
      ∃ (a : ℝ) (f : StrongDual ℝ V), ∀ᵐ y ∂μ, φ y = a + f y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Lp ℝ 2 μ) (H : ℝ), 0 ≤ H →
      (∀ ψ : Lp ℝ 2 μ, |⟪h, ψ⟫| ≤ H * ∫ y, |ψ y| ∂μ) → h ∈ (Vlin μ hbdd c)ᗮ →
      ∃ φ : Lp ℝ 2 μ, Gop μ lam M hM φ = h ∧ ∀ᵐ y ∂μ, |φ y| ≤ C * H := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i0)
  have hαr : (0 : ℝ) < α := hα
  obtain ⟨γ, hγ, hgap⟩ := Mixes.Robust.spectral_gap (Gop μ lam M hM) (Cop μ lam M hM)
    (Gop_pos μ lam M hM) (Gop_sym μ lam M hM) (m := (n : ℝ)⁻¹ ^ 2 * α) (by positivity)
    (fun x => by
      rw [Gop_eq, add_apply, add_sub_cancel_right]
      exact Mop_norm_ge μ lam M hM i0 hlow x)
    (Cop_compact μ lam M hM hHS hpair) (Vlin μ hbdd c)
    (Gop_ker μ lam M hM hbdd c hsum hα i0 hlow hpair hker)
  set U := μ.real univ with hU
  have hU0 : 0 ≤ U := measureReal_nonneg
  refine ⟨(n : ℝ) ^ 2 * (1 + M' * (U * γ⁻¹)) / α, by positivity, fun h H hH hh horth => ?_⟩
  obtain ⟨φ, -, hGφ, hφn⟩ := Mixes.Robust.solve_of_gap (Gop μ lam M hM) (Vlin μ hbdd c)
    (Gop_mem_orth μ lam M hM hbdd c hsum) hγ hgap horth
  refine ⟨φ, hGφ, ?_⟩
  have hsq : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU0
  have hs0 : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hhn : ‖h‖ ≤ H * Real.sqrt U := by
    have h1 : ‖h‖ ^ 2 ≤ H * (Real.sqrt U * ‖h‖) := by
      rw [← real_inner_self_eq_norm_sq]
      exact (le_abs_self _).trans ((hh h).trans
        (mul_le_mul_of_nonneg_left (l1_le μ h) hH))
    rcases (norm_nonneg h).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  have hL : ∫ y, |φ y| ∂μ ≤ U * γ⁻¹ * H := by
    calc ∫ y, |φ y| ∂μ ≤ Real.sqrt U * ‖φ‖ := l1_le μ φ
      _ ≤ Real.sqrt U * (γ⁻¹ * (H * Real.sqrt U)) :=
          mul_le_mul_of_nonneg_left (hφn.trans (mul_le_mul_of_nonneg_left hhn
            (inv_nonneg.2 hγ.le))) hs0
      _ = U * γ⁻¹ * H := by
          rw [show Real.sqrt U * (γ⁻¹ * (H * Real.sqrt U)) =
            (Real.sqrt U * Real.sqrt U) * γ⁻¹ * H by ring, hsq]
  have hbd := linfty_abs μ lam M hM hpair hα i0 hlow φ hH fun ψ => by rw [hGφ]; exact hh ψ
  filter_upwards [hbd] with y hy
  refine hy.trans ?_
  have hM'L : (M' : ℝ) * ∫ y, |φ y| ∂μ ≤ M' * (U * γ⁻¹ * H) :=
    mul_le_mul_of_nonneg_left hL M'.2
  calc (n : ℝ) ^ 2 * (H + M' * ∫ y, |φ y| ∂μ) / α ≤ (n : ℝ) ^ 2 * (H + M' * (U * γ⁻¹ * H)) / α := by
        gcongr
    _ = (n : ℝ) ^ 2 * (1 + M' * (U * γ⁻¹)) / α * H := by ring

end Abstract

open Room

section Geom

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The partner point `q(p) = c - (p - c)/(n - 1)`, `n = k + 3`. -/
def qpt (k : ℕ) (c p : V) : V := c - ((k + 2 : ℕ) : ℝ)⁻¹ • (p - c)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma mem_innerBody_iff {K : Set V} {ρ : ℝ} {x : V} :
    x ∈ innerBody K ρ ↔ ∀ v : V, ‖v‖ ≤ ρ → x + v ∈ K := by
  constructor
  · intro h v hv
    exact h (by rw [mem_closedBall, dist_eq_norm]; simpa using hv)
  · intro h y hy
    have := h (y - x) (by rwa [mem_closedBall, dist_eq_norm] at hy)
    simpa using this

lemma innerBody_eq_iInter (K : Set V) (ρ : ℝ) :
    innerBody K ρ = ⋂ v ∈ closedBall (0 : V) ρ, (fun x => x + v) ⁻¹' K := by
  ext x
  simp only [mem_iInter, mem_preimage, mem_closedBall, dist_zero_right, mem_innerBody_iff]

lemma isClosed_innerBody {K : Set V} (hK : IsClosed K) (ρ : ℝ) : IsClosed (innerBody K ρ) := by
  rw [innerBody_eq_iInter]
  exact isClosed_biInter fun v _ => hK.preimage (continuous_id.add continuous_const)

lemma convex_innerBody {K : Set V} (hK : Convex ℝ K) (ρ : ℝ) : Convex ℝ (innerBody K ρ) := by
  rw [innerBody_eq_iInter]
  exact convex_iInter₂ fun v _ => by simpa [add_comm] using hK.translate_preimage_right v

lemma innerBody_subset {K : Set V} {ρ : ℝ} (hρ : 0 ≤ ρ) : innerBody K ρ ⊆ K := fun x hx => by
  simpa using (mem_innerBody_iff.1 hx) 0 (by simpa using hρ)

/-- If `d_H(K, K₀) < ε ≤ ρ` with `K` closed and convex, then `(K₀)_ρ ⊂ K` (support functions). -/
lemma innerBody_subset_of_hausdorff {K K0 : Set V} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hfin : hausdorffEDist K K0 ≠ ⊤) {ε ρ : ℝ} (hd : hausdorffDist K K0 < ε) (hερ : ε ≤ ρ) :
    innerBody K0 ρ ⊆ K := by
  intro x hx
  by_contra hxK
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed hKc hKcl hxK
  obtain ⟨v, hv, hvmax⟩ := (isCompact_closedBall (0 : V) 1).exists_isMaxOn
    (nonempty_closedBall.2 zero_le_one) (continuous_neg.comp f.continuous).continuousOn
  set m := -f v
  have hbound : ∀ w : V, f w ≤ m * ‖w‖ := by
    intro w
    rcases eq_or_ne w 0 with h | h
    · simp [h]
    have hn : 0 < ‖w‖ := norm_pos_iff.2 h
    have h1 : ‖-(‖w‖⁻¹ • w)‖ ≤ 1 := by
      rw [norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h2 : -f (-(‖w‖⁻¹ • w)) ≤ -f v := hvmax (by rwa [mem_closedBall, dist_zero_right])
    have : ‖w‖⁻¹ * f w ≤ m := by simpa [m] using h2
    rwa [inv_mul_le_iff₀ hn, mul_comm] at this
  have hρ : 0 ≤ ρ := le_trans (le_trans hausdorffDist_nonneg hd.le) hερ
  have hy : x + ρ • v ∈ K0 := mem_innerBody_iff.1 hx _ (by
    rw [norm_smul, Real.norm_of_nonneg hρ]
    have : ‖v‖ ≤ 1 := by simpa using hv
    nlinarith)
  obtain ⟨b, hb, hdb⟩ := exists_dist_lt_of_hausdorffDist_lt' hy hd hfin
  have hm0 : 0 ≤ m := by
    have := hvmax (show (0 : V) ∈ closedBall 0 1 by simp)
    simpa [m] using this
  have h1 := hbound (b - (x + ρ • v))
  rw [map_sub, map_add, map_smul, smul_eq_mul, ← dist_eq_norm] at h1
  have h2 : m * dist b (x + ρ • v) ≤ m * ε := mul_le_mul_of_nonneg_left hdb.le hm0
  have h3 := hfb b hb
  have : f v = -m := by simp [m]
  rw [this] at h1
  nlinarith

/-- A point of `K` is within `ε` of `K₀` if `d_H(K, K₀) < ε`. -/
lemma subset_cthickening_of_hausdorff {K K0 : Set V} (hfin : hausdorffEDist K K0 ≠ ⊤)
    {ε : ℝ} (hd : hausdorffDist K K0 < ε) : K ⊆ cthickening ε K0 := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hd hfin
  exact mem_cthickening_of_dist_le x y ε K0 hy hxy.le

/-- **Partners near the centre.** Let `K₀` be closed and convex with `c + sB ⊂ K₀` and
`as(K₀) ≤ a < n - 1` about `c` (`n = k + 3`), `θ = a/(n-1)`. For `p` within `δ` of `K₀`,
`q(p) + ((1 - θ)s - δ/(n-1)) B ⊂ K₀`. -/
lemma partner_ball {k : ℕ} {K0 : Set V} (hKc : Convex ℝ K0) (hKcl : IsClosed K0) {c : V}
    {s a : ℝ} (hball : closedBall c s ⊆ K0) (ha : 0 < a) (han : a < ((k + 2 : ℕ) : ℝ))
    (hasym : AsymLE K0 c a) {p x : V} (hx : x ∈ K0) {δ : ℝ} (hpx : dist p x ≤ δ) :
    closedBall (qpt k c p) ((1 - a / ((k + 2 : ℕ) : ℝ)) * s - δ / ((k + 2 : ℕ) : ℝ)) ⊆ K0 := by
  set N : ℝ := ((k + 2 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  set θ := a / N
  have hθ0 : 0 < θ := div_pos ha hN
  have hθ1 : θ < 1 := (div_lt_one hN).2 han
  have hy := reflect_mem_of_asymLE hKc hKcl ha hasym hx
  set y := c - a⁻¹ • (x - c)
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  set e := p - x
  set u := w - qpt k c p
  have hq : qpt k c p = θ • y + (1 - θ) • c - N⁻¹ • e := by
    have hθy : θ • y = θ • c - N⁻¹ • (x - c) := by
      simp only [y, θ, smul_sub, smul_smul]
      rw [show a / N * a⁻¹ = N⁻¹ by field_simp]
    rw [hθy, show qpt k c p = c - N⁻¹ • (p - c) from rfl]
    simp only [e]
    module
  set z := c + (1 - θ)⁻¹ • (u - N⁻¹ • e)
  have hz : z ∈ K0 := by
    apply hball
    rw [mem_closedBall, dist_eq_norm, show z - c = (1 - θ)⁻¹ • (u - N⁻¹ • e) by simp [z],
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by linarith)),
      inv_mul_le_iff₀ (by linarith)]
    have he : ‖e‖ ≤ δ := by rw [← dist_eq_norm]; exact hpx
    calc ‖u - N⁻¹ • e‖ ≤ ‖u‖ + ‖N⁻¹ • e‖ := norm_sub_le _ _
      _ ≤ ((1 - θ) * s - δ / N) + N⁻¹ * δ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN.le)]
          exact add_le_add hw (mul_le_mul_of_nonneg_left he (inv_nonneg.2 hN.le))
      _ = (1 - θ) * s := by rw [div_eq_mul_inv]; ring
  have hw' : w = θ • y + (1 - θ) • z := by
    have h1 : (1 - θ) • (1 - θ)⁻¹ • (u - N⁻¹ • e) = u - N⁻¹ • e := by
      rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
    simp only [z, smul_add, h1]
    have : w = qpt k c p + u := by simp [u]
    rw [this, hq]; abel
  rw [hw']
  exact hKc hy hz hθ0.le (by linarith) (by ring)

lemma closedBall_sub_innerBody {K : Set V} {q : V} {R ρ : ℝ} (h : closedBall q R ⊆ K) :
    closedBall q (R - ρ) ⊆ innerBody K ρ := by
  intro y hy z hz
  apply h
  rw [mem_closedBall] at hy hz ⊢
  linarith [dist_triangle z y q]

/-- The centre `c` of a body with finite asymmetry about `c` is an interior point. -/
lemma mem_interior_of_asym {K : Set V} (hKc : Convex ℝ K) (hi : (interior K).Nonempty) {c : V}
    {a : ℝ} (ha : 0 ≤ a) (hasym : AsymLE K c a) : c ∈ interior K := by
  by_contra hc
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (hKc.interior) isOpen_interior hc
  -- `f < f c` on the interior, hence `f ≤ f c` on `K`
  have hK : ∀ y ∈ K, f y ≤ f c := by
    intro y hy
    have hcl : y ∈ closure (interior K) := by
      rw [hKc.closure_interior_eq_closure_of_nonempty_interior hi]; exact subset_closure hy
    exact (isClosed_le f.continuous continuous_const).closure_subset_iff.2
      (fun z hz => (hf z hz).le) hcl
  obtain ⟨x, hx⟩ := hi
  obtain ⟨y, hy, hxy⟩ := hasym (-f) x (interior_subset hx)
  have h1 := hf x hx
  have h2 := hK y hy
  simp only [neg_apply] at hxy
  nlinarith

end Geom

section GeomMeas

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- `|(K₀)_δ| → |K₀|` as `δ → 0+`, for a compact convex `K₀`. -/
lemma vol_innerBody_close {K0 : Set V} (hKc : Convex ℝ K0) (hK : IsCompact K0) {η : ℝ≥0∞}
    (hη : 0 < η) : ∃ δ > 0, volume K0 ≤ volume (innerBody K0 δ) + η := by
  set s : ℕ → Set V := fun j => innerBody K0 (1 / ((j : ℝ) + 1))
  have hmono : Monotone s := by
    intro i j hij x hx y hy
    apply hx
    rw [mem_closedBall] at hy ⊢
    refine hy.trans ?_
    gcongr
  have hU : interior K0 ⊆ ⋃ j, s j := by
    intro x hx
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hr
    refine mem_iUnion.2 ⟨j, fun y hy => interior_subset (hb ?_)⟩
    rw [mem_ball]; rw [mem_closedBall] at hy; linarith
  have hvol : volume K0 ≤ volume (⋃ j, s j) := by
    calc volume K0 ≤ volume (interior K0 ∪ frontier K0) := by
          refine measure_mono fun x hx => ?_
          by_cases h : x ∈ interior K0
          · exact Or.inl h
          · exact Or.inr ⟨subset_closure hx, h⟩
      _ ≤ volume (interior K0) + volume (frontier K0) := measure_union_le _ _
      _ = volume (interior K0) := by rw [hKc.addHaar_frontier volume, add_zero]
      _ ≤ _ := measure_mono hU
  have ht := tendsto_measure_iUnion_atTop (μ := volume) hmono
  have hfin : volume (⋃ j, s j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono ?_)
    exact iUnion_subset fun j => innerBody_subset (by positivity)
  have key : ∃ j, volume (⋃ j, s j) ≤ volume (s j) + η := by
    rcases eq_or_ne (volume (⋃ j, s j)) 0 with h0 | h0
    · exact ⟨0, by rw [h0]; exact bot_le⟩
    have hlt : volume (⋃ j, s j) - η < volume (⋃ j, s j) := ENNReal.sub_lt_self hfin h0 hη.ne'
    obtain ⟨j, hj⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
    exact ⟨j, tsub_le_iff_right.1 hj.le⟩
  obtain ⟨j, hj⟩ := key
  exact ⟨1 / ((j : ℝ) + 1), by positivity, hvol.trans hj⟩

/-- `|K₀ + δB| → |K₀|` as `δ → 0`. -/
lemma vol_cthickening_close {K0 : Set V} (hK : IsCompact K0) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, volume (cthickening δ K0) ≤ volume K0 + η := by
  have ht := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure V)) hK
  have hlt : volume K0 < volume K0 + η := ENNReal.lt_add_right hK.measure_lt_top.ne hη.ne'
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (gt_mem_nhds hlt))
  have hd : dist (δ / 2) (0 : ℝ) < δ := by
    rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]; linarith
  exact ⟨δ / 2, by positivity, (h hd).le⟩

end GeomMeas

section Tuples

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- Replacing coordinate `i` of `y` by `v - ∑ y` preserves Lebesgue measure. -/
lemma mp_reflect (j : ℕ) (i : Fin (j + 1)) (v : V) :
    MeasurePreserving (fun y : Fin (j + 1) → V => Function.update y i (v - ∑ l, y l))
      (Measure.pi fun _ => (volume : Measure V)) (Measure.pi fun _ => (volume : Measure V)) := by
  set ν := Measure.pi fun _ : Fin j => (volume : Measure V)
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => (volume : Measure V)) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => V) i
  have hΨ : MeasurePreserving (fun q : (Fin j → V) × V => (q.1, v - q.2 - ∑ l, q.1 l))
      (ν.prod volume) (ν.prod volume) := by
    refine (MeasurePreserving.id ν).skew_product (g := fun r a => v - a - ∑ l, r l) ?_
      (Filter.Eventually.of_forall fun r => ?_)
    · exact ((measurable_const.sub measurable_snd).sub
        ((Finset.measurable_sum _ fun l _ => measurable_pi_apply l).comp measurable_fst))
    · have h1 := (Measure.measurePreserving_sub_left (volume : Measure V) v).map_eq
      have h2 := (measurePreserving_sub_right (volume : Measure V) (∑ l, r l)).map_eq
      have hm1 : Measurable fun a : V => v - a := measurable_const.sub measurable_id
      have hm2 : Measurable fun a : V => a - ∑ l, r l := measurable_id.sub measurable_const
      rw [show (fun a : V => v - a - ∑ l, r l) = (fun a => a - ∑ l, r l) ∘ (fun a => v - a)
        from rfl, ← Measure.map_map hm2 hm1, h1, h2]
  have hΦ : MeasurePreserving (fun p : V × (Fin j → V) => (v - p.1 - ∑ l, p.2 l, p.2))
      ((volume : Measure V).prod ν) ((volume : Measure V).prod ν) :=
    (Measure.measurePreserving_swap.comp hΨ).comp Measure.measurePreserving_swap
  have hcomp := (he.symm e).comp (hΦ.comp he)
  convert hcomp using 1
  funext y
  simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    MeasurableEquiv.piFinSuccAbove_apply]
  ext l
  refine Fin.succAboveCases i ?_ (fun l' => ?_) l
  · simp [Fin.insertNthEquiv, Fin.sum_univ_succAbove _ i]; abel
  · simp [Fin.insertNthEquiv, Fin.succAbove_ne, Fin.removeNth]

/-- The tuple of `update y i (N c - ∑ y)` is the tuple of `y` with coordinates `i` and `last`
exchanged. -/
lemma embed_update {m : ℕ} (c : V) (y : Fin m → V) (i : Fin m) :
    embed c (Function.update y i (((m + 1 : ℕ) : ℝ) • c - ∑ l, y l)) =
      embed c y ∘ Equiv.swap i.castSucc (Fin.last m) := by
  ext l
  simp only [Function.comp_apply]
  refine Fin.lastCases ?_ (fun l' => ?_) l
  · rw [Equiv.swap_apply_right, embed_last, embed_castSucc]
    rw [Finset.sum_update_of_mem (Finset.mem_univ _),
      Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ y (Finset.mem_univ i)]
    abel
  · rcases eq_or_ne l' i with h | h
    · subst h
      rw [Equiv.swap_apply_left, embed_castSucc, embed_last, Function.update_self]
    · have h1 : l'.castSucc ≠ i.castSucc := fun h' => h (Fin.castSucc_injective _ h')
      have h2 : l'.castSucc ≠ Fin.last m := Fin.castSucc_ne_last l'
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, embed_castSucc, embed_castSucc,
        Function.update_of_ne h]

lemma mem_tuples_perm {n : ℕ} {K : Set V} {c : V} (σ : Equiv.Perm (Fin n)) (x : Fin n → V) :
    x ∘ σ ∈ tuples n K c ↔ x ∈ tuples n K c := by
  have := congrArg (fun S => x ∈ S) (tuples_perm (n := n) K c σ)
  simp only [mem_preimage, mem_compl_iff, eq_iff_iff, not_iff_not] at this
  exact this

lemma measurable_perm' {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (fun x : Fin n → V => x ∘ σ) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- Invariance of `λ` under exchanging a free coordinate with the last one. -/
lemma lebTuples_swap_last {j : ℕ} {K : Set V} (hK : MeasurableSet K) (c : V) (i : Fin (j + 1)) :
    (lebTuples volume (j + 1) K c).map (fun x => x ∘ Equiv.swap i.castSucc (Fin.last (j + 1))) =
      lebTuples volume (j + 1) K c := by
  set σ := Equiv.swap i.castSucc (Fin.last (j + 1))
  set R := fun y : Fin (j + 1) → V => Function.update y i (((j + 1 + 1 : ℕ) : ℝ) • c - ∑ l, y l)
  have hR := mp_reflect j i (((j + 1 + 1 : ℕ) : ℝ) • c)
  set T' := embed (m := j + 1) c ⁻¹' tuples (j + 1 + 1) K c
  have hT'm : MeasurableSet T' := measurable_embed c (measurableSet_tuples hK c)
  have hcomm : (fun x => x ∘ σ) ∘ embed (m := j + 1) c = embed c ∘ R := by
    funext y; exact (embed_update c y i).symm
  have hpre : R ⁻¹' T' = T' := by
    ext y
    show embed c (R y) ∈ tuples _ K c ↔ embed c y ∈ tuples _ K c
    rw [show embed c (R y) = embed c y ∘ σ from embed_update c y i, mem_tuples_perm]
  have hres := hR.restrict_preimage hT'm
  rw [hpre] at hres
  rw [lebTuples, Measure.map_map (measurable_perm' σ) (measurable_embed c), hcomm,
    ← Measure.map_map (measurable_embed c) hR.measurable, hres.map_eq]

/-- `λ` on `𝒯_n(K)` is invariant under all permutations of the coordinates. -/
theorem lebTuples_perm {j : ℕ} {K : Set V} (hK : MeasurableSet K) (c : V) :
    PermInvariant (lebTuples volume (j + 1) K c) := by
  set lam := lebTuples volume (j + 1) K c
  let Sg : Subgroup (Equiv.Perm (Fin (j + 2))) :=
    { carrier := {σ | lam.map (fun x => x ∘ σ) = lam}
      mul_mem' := by
        intro a b ha hb
        simp only [mem_ofPred_eq] at ha hb ⊢
        have : (fun x : Fin (j + 2) → V => x ∘ ⇑(a * b)) =
            (fun x => x ∘ b) ∘ (fun x => x ∘ a) := by
          funext x; rfl
        rw [this, ← Measure.map_map (measurable_perm' b) (measurable_perm' a), ha, hb]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [Measure.map_map (measurable_perm' _) (measurable_perm' a)]
        have : (fun x : Fin (j + 2) → V => x ∘ ⇑a⁻¹) ∘ (fun x => x ∘ a) = id := by
          funext x; ext l; simp
        rw [this, Measure.map_id] }
  have hlast : ∀ i : Fin (j + 1), Equiv.swap i.castSucc (Fin.last (j + 1)) ∈ Sg :=
    fun i => lebTuples_swap_last hK c i
  have hswap : ∀ a b : Fin (j + 2), Equiv.swap a b ∈ Sg := by
    intro a b
    rcases eq_or_ne a b with hab | hab
    · subst hab; rw [Equiv.swap_self]; exact Sg.one_mem
    have key : ∀ a b : Fin (j + 2), b = Fin.last (j + 1) → Equiv.swap a b ∈ Sg := by
      intro a b hb
      subst hb
      rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
      · exact hlast i
      · rw [Equiv.swap_self]; exact Sg.one_mem
    by_cases hb : b = Fin.last (j + 1)
    · exact key a b hb
    by_cases ha : a = Fin.last (j + 1)
    · rw [Equiv.swap_comm]; exact key b a ha
    have : Equiv.swap a b = Equiv.swap a (Fin.last (j + 1)) * Equiv.swap b (Fin.last (j + 1)) *
        Equiv.swap a (Fin.last (j + 1)) := by
      rw [Equiv.swap_comm a (Fin.last (j + 1)),
        Equiv.swap_mul_swap_mul_swap (x := b) (y := Fin.last (j + 1)) (z := a) hb (Ne.symm hab)]
    rw [this]
    exact Sg.mul_mem (Sg.mul_mem (key _ _ rfl) (key _ _ rfl)) (key _ _ rfl)
  intro σ
  have : σ ∈ Sg := by
    have htop := Equiv.Perm.closure_isSwap (α := Fin (j + 2))
    have hle : Subgroup.closure {σ : Equiv.Perm (Fin (j + 2)) | σ.IsSwap} ≤ Sg := by
      rw [Subgroup.closure_le]
      rintro τ ⟨a, b, -, rfl⟩
      exact hswap a b
    rw [htop] at hle
    exact hle (Subgroup.mem_top σ)
  exact this

lemma map_perm_coord {j : ℕ} {K : Set V} (hK : MeasurableSet K) (c : V)
    (σ : Equiv.Perm (Fin (j + 2)))
    {Z : Type*} [MeasurableSpace Z] {F : (Fin (j + 2) → V) → Z} (hF : Measurable F) :
    (lebTuples volume (j + 1) K c).map (fun x => F (x ∘ σ)) =
      (lebTuples volume (j + 1) K c).map F := by
  have h := lebTuples_perm hK c σ
  rw [show (fun x : Fin (j + 2) → V => F (x ∘ σ)) = F ∘ (fun x => x ∘ σ) from rfl,
    ← Measure.map_map hF (measurable_perm' σ), h]

/-- The first coordinate of `λ` has density at most `|K|^{n-2}` on `K`. -/
lemma coord0_le {k : ℕ} {K : Set V} (_hK : MeasurableSet K) (c : V) {A : Set V}
    (hA : MeasurableSet A) :
    lebTuples volume (k + 1) K c ((fun x => x 0) ⁻¹' A) ≤ volume (A ∩ K) * volume K ^ k := by
  rw [lebTuples_apply volume K c (measurable_pi_apply 0 hA)]
  set P : Set (Fin (k + 1) → V) :=
    Set.pi univ (Function.update (fun _ => K) 0 (A ∩ K)) with hP
  have hsub : embed c ⁻¹' ((fun x => x 0) ⁻¹' A) ∩ embed c ⁻¹' tuples (k + 1 + 1) K c ⊆ P := by
    rintro y ⟨hy1, hy2⟩
    rw [mem_embed_preimage_tuples] at hy2
    simp only [mem_preimage] at hy1
    rw [show (0 : Fin (k + 1 + 1)) = (0 : Fin (k + 1)).castSucc from rfl, embed_castSucc] at hy1
    intro l _
    rcases eq_or_ne l 0 with h | h
    · subst h; simp; exact ⟨hy1, hy2.1 _⟩
    · simp [h]; exact hy2.1 _
  calc _ ≤ Measure.pi (fun _ : Fin (k + 1) => (volume : Measure V)) P := measure_mono hsub
    _ = volume (A ∩ K) * volume K ^ k := by
        rw [hP, Measure.pi_pi]
        have h : ∀ l, volume (Function.update (fun _ => K) (0 : Fin (k + 1)) (A ∩ K) l) =
            Function.update (fun _ => volume K) 0 (volume (A ∩ K)) l := fun l => by
          rcases eq_or_ne l 0 with h | h
          · subst h; simp
          · simp [h]
        simp_rw [h]
        rw [Finset.prod_update_of_mem (Finset.mem_univ 0)]
        simp [Finset.prod_const, Finset.card_sdiff]

/-- Every coordinate of `λ` on `𝒯_n(K)` has density at most `|K|^{n-2}` on `K`. -/
lemma coord_le {k : ℕ} {K : Set V} (hK : MeasurableSet K) (c : V) (i : Fin (k + 2)) :
    (lebTuples volume (k + 1) K c).map (fun x => x i) ≤
      (volume K ^ k) • (volume : Measure V).restrict K := by
  have h := map_perm_coord hK c (Equiv.swap 0 i) (F := fun x => x 0) (measurable_pi_apply 0)
  simp only [Function.comp_apply, Equiv.swap_apply_left] at h
  rw [h, Measure.le_iff]
  intro A hA
  rw [Measure.map_apply (measurable_pi_apply 0) hA, smul_apply, Measure.restrict_apply hA,
    smul_eq_mul, mul_comm]
  exact coord0_le hK c hA

/-- `(w, (a, b)) ↦ (a, b, w)` preserves Lebesgue measure. -/
lemma mp_cons2 (k : ℕ) :
    MeasurePreserving (fun t : (Fin k → V) × (V × V) =>
      (Fin.cons t.2.1 (Fin.cons t.2.2 t.1 : Fin (k + 1) → V) : Fin (k + 2) → V))
      ((Measure.pi fun _ : Fin k => (volume : Measure V)).prod
        ((volume : Measure V).prod volume))
      (Measure.pi fun _ : Fin (k + 2) => (volume : Measure V)) := by
  have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 2) => (volume : Measure V)) 0
  have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure V)) 0
  have h1 := e1.symm
  have h2 := (MeasurePreserving.id (volume : Measure V)).prod e2.symm
  have h3 := measurePreserving_prodAssoc (volume : Measure V) (volume : Measure V)
    (Measure.pi fun _ : Fin k => (volume : Measure V))
  have h4 := Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin k => (volume : Measure V))
    (ν := (volume : Measure V).prod (volume : Measure V))
  have := h1.comp (h2.comp (h3.comp h4))
  convert this using 1
  funext t
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      MeasurableEquiv.prodAssoc]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      MeasurableEquiv.prodAssoc]
    · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      MeasurableEquiv.prodAssoc]

/-- The pair of the first two coordinates of `λ` has density at most `|K|^{n-3}` on `K × K`. -/
lemma pair01_le {k : ℕ} {K : Set V} (hK : MeasurableSet K) (c : V) :
    (lebTuples volume (k + 2) K c).map (fun x => (x 0, x 1)) ≤
      (volume K ^ k) • ((volume : Measure V).restrict K).prod
        ((volume : Measure V).restrict K) := by
  have hpm : Measurable (fun x : Fin (k + 3) → V => (x 0, x 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  rw [Measure.le_iff]
  intro S hS
  rw [Measure.map_apply hpm hS, lebTuples_apply volume K c (hpm hS), smul_apply,
    Measure.prod_restrict, Measure.restrict_apply hS, smul_eq_mul]
  have hmp := mp_cons2 (V := V) k
  have hQ : MeasurableSet (embed c ⁻¹' ((fun x : Fin (k + 3) → V => (x 0, x 1)) ⁻¹' S) ∩
      embed c ⁻¹' tuples (k + 2 + 1) K c) :=
    (measurable_embed c (hpm hS)).inter (measurable_embed c (measurableSet_tuples hK c))
  rw [← hmp.measure_preimage hQ.nullMeasurableSet]
  refine (measure_mono (t := (Set.pi univ fun _ => K) ×ˢ (S ∩ K ×ˢ K)) ?_).trans ?_
  · rintro ⟨w, a, b⟩ ⟨hy1, hy2⟩
    simp only [mem_preimage] at hy1
    replace hy2 := mem_embed_preimage_tuples.1 (show _ ∈ embed c ⁻¹' _ from hy2)
    have e0 : embed c (Fin.cons a (Fin.cons b w : Fin (k + 1) → V) : Fin (k + 2) → V) 0 = a :=
      embed_castSucc c _ 0
    have e1 : embed c (Fin.cons a (Fin.cons b w : Fin (k + 1) → V) : Fin (k + 2) → V) 1 = b :=
      embed_castSucc c _ 1
    rw [e0, e1] at hy1
    refine ⟨fun l _ => ?_, hy1, ?_, ?_⟩
    · simpa using hy2.1 l.succ.succ
    · simpa using hy2.1 0
    · simpa using hy2.1 1
  · rw [Measure.prod_prod, Measure.pi_pi]
    simp [Finset.prod_const]

/-- Any pair of distinct coordinates of `λ` has density at most `|K|^{n-3}` on `K × K`. -/
lemma pair_le {k : ℕ} {K : Set V} (hK : MeasurableSet K) (c : V) (i j : Fin (k + 3))
    (hij : i ≠ j) :
    (lebTuples volume (k + 2) K c).map (fun x => (x j, x i)) ≤
      (volume K ^ k) • ((volume : Measure V).restrict K).prod
        ((volume : Measure V).restrict K) := by
  set i' := Equiv.swap 0 j i
  have hi'0 : i' ≠ 0 := by
    intro h
    apply hij
    have := congrArg (Equiv.swap 0 j) h
    simpa [i'] using this
  set σ := Equiv.swap 0 j * Equiv.swap 1 i'
  have hσ0 : σ 0 = j := by
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hi'0), Equiv.swap_apply_left]
  have hσ1 : σ 1 = i := by
    simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, i', Equiv.swap_apply_self]
  have h := map_perm_coord hK c σ (F := fun x => (x 0, x 1))
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  simp only [Function.comp_apply, hσ0, hσ1] at h
  rw [h]
  exact pair01_le hK c


lemma sum_partners (k : ℕ) (c p : V) (z : Fin (k + 1) → V) :
    (((k + 2 + 1 : ℕ) : ℝ) • c - (p + ∑ l, z l)) - qpt k c p = -∑ l, (z l - qpt k c p) := by
  have hk : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq : ((k + 2 : ℕ) : ℝ) • qpt k c p = ((k + 2 : ℕ) : ℝ) • c - (p - c) := by
    rw [qpt, smul_sub, smul_smul, mul_inv_cancel₀ hk, one_smul]
  set q := qpt k c p
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (((k + 2 + 1 : ℕ) : ℝ)) • c = ((k + 2 : ℕ) : ℝ) • c + c := by
    rw [show ((k + 2 + 1 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) + 1 by push_cast; ring, add_smul,
      one_smul]
  have h3 : (k + 1) • q = ((k + 2 : ℕ) : ℝ) • q - q := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, show ((k + 1 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) - 1 by
      push_cast; ring, sub_smul, one_smul]
  rw [h3, hq, h2]
  abel

/-- **Room on `D`**: if every `p ∈ D` has `q(p) + (n-2) r B ⊂ D`, then the first coordinate of
`λ` on `𝒯_n(D)` has density at least `|rB|^{n-2}` on `D`. -/
lemma coord0_ge {k : ℕ} {D : Set V} (hD : MeasurableSet D) (c : V) {r : ℝ} (hr : 0 < r)
    (hball : ∀ p ∈ D, closedBall (qpt k c p) ((k + 1 : ℕ) * r) ⊆ D) :
    (volume (closedBall (0 : V) r) ^ (k + 1)) • (volume : Measure V).restrict D ≤
      (lebTuples volume (k + 2) D c).map (fun x => x 0) := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.map_apply (measurable_pi_apply 0) hA, lebTuples_apply volume D c
    (measurable_pi_apply 0 hA), smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 2) => (volume : Measure V)) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => V) 0
  set Q := embed c ⁻¹' ((fun x : Fin (k + 3) → V => x 0) ⁻¹' A) ∩
      embed c ⁻¹' tuples (k + 2 + 1) D c
  have hQ : MeasurableSet Q := (measurable_embed c (measurable_pi_apply 0 hA)).inter
      (measurable_embed c (measurableSet_tuples hD c))
  rw [← (he.symm e).measure_preimage hQ.nullMeasurableSet]
  set W : Set (V × (Fin (k + 1) → V)) :=
    {t | t.1 ∈ A ∩ D ∧ ∀ l, t.2 l ∈ closedBall (qpt k c t.1) r}
  have hWm : MeasurableSet W := by
    show MeasurableSet ({t : V × (Fin (k + 1) → V) | t.1 ∈ A ∩ D} ∩
      {t | ∀ l, t.2 l ∈ closedBall (qpt k c t.1) r})
    refine (measurable_fst (hA.inter hD)).inter ?_
    have : {t : V × (Fin (k + 1) → V) | ∀ l, t.2 l ∈ closedBall (qpt k c t.1) r} =
        ⋂ l, {t | dist (t.2 l) (qpt k c t.1) ≤ r} := by ext t; simp
    rw [this]
    refine MeasurableSet.iInter fun l => measurableSet_le ?_ measurable_const
    exact ((measurable_pi_apply l).comp measurable_snd).dist
      (measurable_const.sub (measurable_const.smul (measurable_fst.sub measurable_const)))
  have hsub : W ⊆ e.symm ⁻¹' Q := by
    rintro ⟨p, z⟩ ⟨⟨hpA, hpD⟩, hz⟩
    have hy : e.symm (p, z) = (Fin.cons p z : Fin (k + 2) → V) := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hzD : ∀ l, z l ∈ D := fun l => hball p hpD (closedBall_subset_closedBall
      (by have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
          nlinarith) (hz l))
    simp only [mem_preimage, Q, hy, mem_inter_iff]
    refine ⟨?_, ?_⟩
    · rw [show (0 : Fin (k + 2 + 1)) = (0 : Fin (k + 2)).castSucc from rfl, embed_castSucc]
      simpa using hpA
    · refine mem_embed_preimage_tuples.2 ⟨fun l => ?_, ?_⟩
      · refine Fin.cases ?_ (fun l' => ?_) l
        · simpa using hpD
        · simpa using hzD l'
      · apply hball p hpD
        rw [mem_closedBall, dist_eq_norm, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [sum_partners, norm_neg]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun l _ => (mem_closedBall_iff_norm.1 (hz l))).trans ?_
        simp
  refine le_trans ?_ (measure_mono hsub)
  rw [Measure.prod_apply hWm]
  have hsec : ∀ p, (Measure.pi fun _ : Fin (k + 1) => (volume : Measure V))
      (Prod.mk p ⁻¹' W) =
        (A ∩ D).indicator (fun _ => volume (closedBall (0 : V) r) ^ (k + 1)) p := by
    intro p
    by_cases hp : p ∈ A ∩ D
    · rw [indicator_of_mem hp]
      have : Prod.mk p ⁻¹' W = Set.pi univ fun _ => closedBall (qpt k c p) r := by
        ext z; simp [W, hp.1, hp.2]
      rw [this, Measure.pi_pi]
      simp [Measure.addHaar_closedBall_center, Finset.prod_const]
    · rw [indicator_of_notMem hp]
      have : Prod.mk p ⁻¹' W = ∅ := by
        ext z; simp only [W, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hp h.1
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const (hA.inter hD), mul_comm]

end Tuples

section Partners

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The uniform distribution of `k + 1` independent points of `rB`. -/
def boxM (k : ℕ) (r : ℝ) : Measure (Fin (k + 1) → V) :=
  (volume (closedBall (0 : V) r) ^ (k + 1))⁻¹ •
    (Measure.pi fun _ => (volume : Measure V)).restrict (Set.pi univ fun _ => closedBall (0 : V) r)

/-- The offsets `(w₁, …, w_{k+1}, -∑ w)` of the partners, summing to `0`. -/
def offs {k : ℕ} (w : Fin (k + 1) → V) : Fin (k + 2) → V :=
  Fin.snoc (α := fun _ => V) w (-∑ l, w l)

/-- A point `p` and its partners `q(p) + offsets`. -/
def partF (k : ℕ) (c : V) (t : V × (Fin (k + 1) → V)) : Fin (k + 3) → V :=
  Fin.cons t.1 (fun i => qpt k c t.1 + offs t.2 i)

/-- The distribution of `p ∼ g` with its partners. -/
def gam (k : ℕ) (c : V) (r : ℝ) (g : Measure V) : Measure (Fin (k + 3) → V) :=
  (g.prod (boxM k r)).map (partF k c)

lemma measurable_offs {k : ℕ} (i : Fin (k + 2)) :
    Measurable (fun w : Fin (k + 1) → V => offs w i) := by
  refine Fin.lastCases ?_ (fun l => ?_) i
  · simp only [offs, Fin.snoc_last]
    exact (Finset.measurable_sum _ fun l _ => measurable_pi_apply l).neg
  · simp only [offs, Fin.snoc_castSucc]
    exact measurable_pi_apply l

lemma measurable_qpt (k : ℕ) (c : V) : Measurable (qpt k c) :=
  measurable_const.sub (measurable_const.smul (measurable_id.sub measurable_const))

lemma measurable_partF (k : ℕ) (c : V) : Measurable (partF k c) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [partF] using measurable_fst
  · simp only [partF, Fin.cons_succ]
    exact ((measurable_qpt k c).comp measurable_fst).add ((measurable_offs j).comp measurable_snd)

lemma vol_ball_pos {r : ℝ} (hr : 0 < r) : 0 < volume (closedBall (0 : V) r) :=
  measure_closedBall_pos _ _ hr

lemma vol_ball_ne_top (r : ℝ) : volume (closedBall (0 : V) r) ≠ ⊤ :=
  (isCompact_closedBall _ _).measure_lt_top.ne

lemma boxM_univ (k : ℕ) {r : ℝ} (hr : 0 < r) : boxM (V := V) k r univ = 1 := by
  rw [boxM, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.pi_pi,
    smul_eq_mul]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ (vol_ball_pos hr).ne')
    (ENNReal.pow_ne_top (vol_ball_ne_top r))

lemma boxM_finite (k : ℕ) {r : ℝ} (hr : 0 < r) : IsFiniteMeasure (boxM (V := V) k r) :=
  ⟨by rw [boxM_univ k hr]; exact ENNReal.one_lt_top⟩

lemma pi_update (k : ℕ) (l : Fin (k + 1)) (B A : Set V) :
    Measure.pi (fun _ : Fin (k + 1) => (volume : Measure V))
      (Set.pi univ (Function.update (fun _ => B) l A)) = volume A * volume B ^ k := by
  rw [Measure.pi_pi]
  have h : ∀ j, volume (Function.update (fun _ => B) l A j) =
      Function.update (fun _ => volume B) l (volume A) j := fun j => by
    rcases eq_or_ne j l with h | h
    · subst h; simp
    · simp [h]
  simp_rw [h]
  rw [Finset.prod_update_of_mem (Finset.mem_univ l)]
  simp [Finset.prod_const, Finset.card_sdiff]

/-- Each offset has density at most `|rB|⁻¹` under `boxM`. -/
lemma boxM_offs_le (k : ℕ) {r : ℝ} (hr : 0 < r) (i : Fin (k + 2)) {A : Set V}
    (hA : MeasurableSet A) :
    boxM k r {w : Fin (k + 1) → V | offs w i ∈ A} ≤
      (volume (closedBall (0 : V) r))⁻¹ * volume A := by
  set B := closedBall (0 : V) r
  have hB0 := (vol_ball_pos (V := V) hr).ne'
  have hBt := vol_ball_ne_top (V := V) r
  have hSm : MeasurableSet {w : Fin (k + 1) → V | offs w i ∈ A} := measurable_offs i hA
  rw [boxM, smul_apply, Measure.restrict_apply hSm, smul_eq_mul]
  have hmain : Measure.pi (fun _ : Fin (k + 1) => (volume : Measure V))
      ({w | offs w i ∈ A} ∩ Set.pi univ fun _ => B) ≤ volume A * volume B ^ k := by
    refine Fin.lastCases ?_ (fun l => ?_) i
    · have hR := mp_reflect k (0 : Fin (k + 1)) (0 : V)
      set P := Set.pi univ (Function.update (fun _ => B) (0 : Fin (k + 1)) A)
      have hP : MeasurableSet P := MeasurableSet.univ_pi fun j => by
        rcases eq_or_ne j 0 with h | h
        · subst h; simpa using hA
        · simpa [h] using measurableSet_closedBall
      calc _ ≤ Measure.pi (fun _ : Fin (k + 1) => (volume : Measure V))
            ((fun y : Fin (k + 1) → V => Function.update y 0 (0 - ∑ l, y l)) ⁻¹' P) := by
            refine measure_mono fun w ⟨h1, h2⟩ j _ => ?_
            rcases eq_or_ne j 0 with h | h
            · subst h; simpa [offs] using h1
            · simpa [h] using h2 j (mem_univ _)
        _ = volume A * volume B ^ k := by
            rw [hR.measure_preimage hP.nullMeasurableSet, pi_update]
    · calc _ ≤ Measure.pi (fun _ : Fin (k + 1) => (volume : Measure V))
            (Set.pi univ (Function.update (fun _ => B) l A)) := by
            refine measure_mono fun w ⟨h1, h2⟩ j _ => ?_
            rcases eq_or_ne j l with h | h
            · subst h; simpa [offs] using h1
            · simpa [h] using h2 j (mem_univ _)
        _ = volume A * volume B ^ k := pi_update k l B A
  calc (volume B ^ (k + 1))⁻¹ * Measure.pi (fun _ => volume) _
      ≤ (volume B ^ (k + 1))⁻¹ * (volume A * volume B ^ k) := by gcongr
    _ = (volume B)⁻¹ * volume A := by
        rw [pow_succ, ENNReal.mul_inv (Or.inr hBt) (Or.inr hB0),
          show (volume B ^ k)⁻¹ * (volume B)⁻¹ * (volume A * volume B ^ k) =
            (volume B)⁻¹ * volume A * ((volume B ^ k)⁻¹ * volume B ^ k) by ring,
          ENNReal.inv_mul_cancel (pow_ne_zero _ hB0) (ENNReal.pow_ne_top hBt), mul_one]

lemma norm_offs_le {k : ℕ} {r : ℝ} {w : Fin (k + 1) → V} (hw : ∀ l, ‖w l‖ ≤ r) (hr : 0 ≤ r)
    (i : Fin (k + 2)) : ‖offs w i‖ ≤ ((k + 1 : ℕ) : ℝ) * r := by
  refine Fin.lastCases ?_ (fun l => ?_) i
  · simp only [offs, Fin.snoc_last, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun l _ => hw l).trans ?_
    simp
  · simp only [offs, Fin.snoc_castSucc]
    refine (hw l).trans ?_
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith

lemma sum_offs {k : ℕ} (w : Fin (k + 1) → V) : ∑ i, offs w i = 0 := by
  rw [Fin.sum_univ_castSucc]; simp [offs]

lemma box_ae {k : ℕ} {r : ℝ} :
    ∀ᵐ w ∂(boxM (V := V) k r), ∀ l, ‖w l‖ ≤ r := by
  exact Measure.ae_smul_measure (ae_restrict_of_forall_mem
    (MeasurableSet.univ_pi fun _ => measurableSet_closedBall)
    fun w hw l => by simpa using hw l (mem_univ _)) _

lemma qpt_sum (k : ℕ) (c p : V) :
    p + ((k + 2 : ℕ) : ℝ) • qpt k c p = ((k + 3 : ℕ) : ℝ) • c := by
  have hk : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [qpt, smul_sub, smul_smul, mul_inv_cancel₀ hk, one_smul,
    show ((k + 3 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) + 1 by push_cast; ring, add_smul, one_smul]
  abel

lemma gam_map0 (k : ℕ) (c : V) {r : ℝ} (hr : 0 < r) (g : Measure V) [SFinite g] :
    (gam k c r g).map (fun x => x 0) = g := by
  have := boxM_finite (V := V) k hr
  rw [gam, Measure.map_map (measurable_pi_apply 0) (measurable_partF k c)]
  have : (fun x : Fin (k + 3) → V => x 0) ∘ partF k c = Prod.fst := by
    funext t; simp [partF]
  rw [this, Measure.map_fst_prod, boxM_univ k hr, one_smul]

instance gam_finite (k : ℕ) (c : V) {r : ℝ} [Fact (0 < r)] (g : Measure V) [IsFiniteMeasure g] :
    IsFiniteMeasure (gam k c r g) := by
  have := boxM_finite (V := V) k (Fact.out : 0 < r)
  unfold gam; infer_instance

/-- The partners of `gam` have densities at most `g(V) / |rB|` and lie in `D`. -/
lemma gam_succ_le (k : ℕ) (c : V) {r : ℝ} (hr : 0 < r) (g : Measure V) [IsFiniteMeasure g]
    {D : Set V} (hD : MeasurableSet D)
    (hgD : ∀ᵐ p ∂g, closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ D) (i : Fin (k + 2)) :
    (gam k c r g).map (fun x => x i.succ) ≤
      (g univ * (volume (closedBall (0 : V) r))⁻¹) • (volume : Measure V).restrict D := by
  have := boxM_finite (V := V) k hr
  rw [Measure.le_iff]
  intro A hA
  have hmi : Measurable (fun t : V × (Fin (k + 1) → V) => qpt k c t.1 + offs t.2 i) :=
    ((measurable_qpt k c).comp measurable_fst).add ((measurable_offs i).comp measurable_snd)
  rw [Measure.map_apply (measurable_pi_apply i.succ) hA, gam,
    Measure.map_apply (measurable_partF k c) (measurable_pi_apply i.succ hA), smul_apply,
    Measure.restrict_apply hA, smul_eq_mul]
  have hpre : partF k c ⁻¹' ((fun x => x i.succ) ⁻¹' A) =
      {t | qpt k c t.1 + offs t.2 i ∈ A} := by
    ext t; simp [partF]
  rw [hpre]
  have hae : ∀ᵐ t ∂(g.prod (boxM k r)), qpt k c t.1 + offs t.2 i ∈ D := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := g) (ν := boxM (V := V) k r)).ae hgD
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := g) (ν := boxM (V := V) k r)).ae
      (box_ae (V := V) (k := k) (r := r))
    filter_upwards [h1, h2] with t ht1 ht2
    apply ht1
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact norm_offs_le ht2 hr.le i
  have hmono : (g.prod (boxM k r)) {t | qpt k c t.1 + offs t.2 i ∈ A} ≤
      (g.prod (boxM k r)) {t | qpt k c t.1 + offs t.2 i ∈ A ∩ D} := by
    refine measure_mono_ae ?_
    filter_upwards [hae] with t ht h
    exact ⟨h, ht⟩
  refine hmono.trans ?_
  rw [Measure.prod_apply (show MeasurableSet
    {t : V × (Fin (k + 1) → V) | qpt k c t.1 + offs t.2 i ∈ A ∩ D} from hmi (hA.inter hD))]
  calc ∫⁻ p, boxM k r (Prod.mk p ⁻¹' {t | qpt k c t.1 + offs t.2 i ∈ A ∩ D}) ∂g
      ≤ ∫⁻ _, (volume (closedBall (0 : V) r))⁻¹ * volume (A ∩ D) ∂g := by
        refine lintegral_mono fun p => ?_
        have : Prod.mk p ⁻¹' {t : V × (Fin (k + 1) → V) | qpt k c t.1 + offs t.2 i ∈ A ∩ D} =
            {w | offs w i ∈ (fun v => qpt k c p + v) ⁻¹' (A ∩ D)} := by ext w; simp
        rw [this]
        refine (boxM_offs_le k hr i ((measurable_const_add _) (hA.inter hD))).trans ?_
        rw [measure_preimage_add]
    _ = g univ * ((volume (closedBall (0 : V) r))⁻¹ * volume (A ∩ D)) := by
        rw [lintegral_const, mul_comm]
    _ = _ := by rw [mul_assoc, inter_comm]

/-- `gam` lives on `𝒯_n(K)` when `g` lives on `K` and the partners of points of `K` stay in `K`. -/
lemma gam_null (k : ℕ) (c : V) {r : ℝ} (hr : 0 < r) (g : Measure V) [IsFiniteMeasure g]
    {K : Set V} (hK : MeasurableSet K) (hgK : g Kᶜ = 0)
    (hP : ∀ p ∈ K, closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ K) :
    gam k c r g (tuples (k + 3) K c)ᶜ = 0 := by
  have := boxM_finite (V := V) k hr
  rw [gam, Measure.map_apply (measurable_partF k c) (measurableSet_tuples hK c).compl]
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := g) (ν := boxM (V := V) k r)).ae
    (show ∀ᵐ p ∂g, p ∈ K from ae_iff.2 hgK)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := g) (ν := boxM (V := V) k r)).ae
    (box_ae (V := V) (k := k) (r := r))
  have : ∀ᵐ t ∂(g.prod (boxM k r)), partF k c t ∈ tuples (k + 3) K c := by
    filter_upwards [h1, h2] with t ht1 ht2
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa [partF] using ht1
      · simp only [partF, Fin.cons_succ]
        apply hP _ ht1
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        exact norm_offs_le ht2 hr.le j
    · rw [Fin.sum_univ_succ]
      simp only [partF, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib, sum_offs,
        add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      exact qpt_sum k c t.1
  exact ae_iff.1 this

end Partners

section Corr

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {n : ℕ}
  (μ : Measure V) [IsFiniteMeasure μ] (lam : Measure (Fin n → V)) [IsFiniteMeasure lam]
  (M : ℝ≥0) (hM : ∀ i, lam.map (fun x => x i) ≤ (M : ℝ≥0∞) • μ)

include hM

lemma integrable_comp (φ : Lp ℝ 2 μ) (i : Fin n) : Integrable (fun x => φ (x i)) lam := by
  have h := ((Lp.memLp (Sop μ lam M hM i φ)).integrable (by norm_num))
  exact h.congr (Sop_ae μ lam M hM i φ)

/-- **The marginal of the correction.** If `Gφ` pairs with indicators like `c₀ μ - ν` and
`|φ| ≤ Hb ≤ σ`, then the marginal of `λ` with density `σ + (1/n) ∑ φ(xᵢ)` plus `ν` is
`σ λ̄ + c₀ μ`. -/
lemma marginal_corr (hn : 0 < n) (φ : Lp ℝ 2 μ) {Hb σr : ℝ} (hφb : ∀ᵐ y ∂μ, |φ y| ≤ Hb)
    (hσ : Hb ≤ σr) (hσ0 : 0 ≤ σr) (ν : Measure V) [IsFiniteMeasure ν] {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hrep : ∀ A (hA : MeasurableSet A), ⟪Gop μ lam M hM φ,
      indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)⟫ = c0 * μ.real A - ν.real A)
    {A : Set V} (hA : MeasurableSet A) :
    marginal (lam.withDensity fun x => ENNReal.ofReal (σr + (n : ℝ)⁻¹ * ∑ i, φ (x i))) A +
      ν A = ENNReal.ofReal σr * marginal lam A + ENNReal.ofReal c0 * μ A := by
  set Ψ : (Fin n → V) → ℝ := fun x => (n : ℝ)⁻¹ * ∑ i, φ (x i) with hΨ
  set F : (Fin n → V) → ℝ := fun x => σr + Ψ x with hF
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hΨint : Integrable Ψ lam :=
    (integrable_finsetSum _ fun i _ => integrable_comp μ lam M hM φ i).const_mul _
  have hFint : Integrable F lam := (integrable_const σr).add hΨint
  have hΨb : ∀ᵐ x ∂lam, |Ψ x| ≤ Hb := by
    have hall : ∀ᵐ x ∂lam, ∀ i, |φ (x i)| ≤ Hb :=
      ae_all_iff.2 fun i => (qmp_i μ lam M hM i).ae hφb
    filter_upwards [hall] with x hx
    rw [hΨ, abs_mul, abs_inv, abs_of_pos hnr]
    calc (n : ℝ)⁻¹ * |∑ i, φ (x i)| ≤ (n : ℝ)⁻¹ * ∑ i, |φ (x i)| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, Hb := by gcongr with i; exact hx i
      _ = Hb := by simp; field_simp
  have hF0 : ∀ᵐ x ∂lam, 0 ≤ F x := by
    filter_upwards [hΨb] with x hx
    have := neg_abs_le (Ψ x)
    simp only [hF]; linarith
  -- each term of the marginal
  have hterm : ∀ i, (lam.withDensity fun x => ENNReal.ofReal (F x)) ((fun x => x i) ⁻¹' A) =
      ENNReal.ofReal (∫ x, (A.indicator 1 (x i)) * F x ∂lam) := by
    intro i
    have hm : MeasurableSet ((fun x : Fin n → V => x i) ⁻¹' A) := measurable_pi_apply i hA
    rw [withDensity_apply _ hm]
    have hind : ∀ x, (A.indicator 1 (x i) : ℝ) * F x =
        ((fun x : Fin n → V => x i) ⁻¹' A).indicator F x := by
      intro x
      by_cases h : x i ∈ A
      · simp [indicator_of_mem h, indicator_of_mem (show x ∈ (fun x => x i) ⁻¹' A from h)]
      · simp [indicator_of_notMem h,
          indicator_of_notMem (show x ∉ (fun x : Fin n → V => x i) ⁻¹' A from h)]
    simp_rw [hind]
    rw [integral_indicator hm, ofReal_integral_eq_lintegral_ofReal hFint.integrableOn
      (ae_restrict_of_ae hF0)]
  -- the real identity
  have hreal : (n : ℝ)⁻¹ * ∑ i, ∫ x, (A.indicator 1 (x i)) * F x ∂lam =
      σr * (marginal lam A).toReal + (c0 * μ.real A - ν.real A) := by
    have h1 : ∀ i, ∫ x, (A.indicator 1 (x i)) * F x ∂lam =
        σr * lam.real ((fun x => x i) ⁻¹' A) + ∫ x, (A.indicator 1 (x i)) * Ψ x ∂lam := by
      intro i
      have hb : Integrable (fun x : Fin n → V => (A.indicator 1 (x i) : ℝ) * Ψ x) lam := by
        refine hΨint.bdd_mul (c := 1) ?_ ?_
        · exact ((measurable_const.indicator hA).comp (measurable_pi_apply i)).aestronglyMeasurable
        · exact Eventually.of_forall fun x => by
            by_cases h : x i ∈ A <;> simp [h]
      have hc : Integrable (fun x : Fin n → V => (A.indicator 1 (x i) : ℝ) * σr) lam := by
        refine (integrable_const σr).bdd_mul (c := 1) ?_ ?_
        · exact ((measurable_const.indicator hA).comp (measurable_pi_apply i)).aestronglyMeasurable
        · exact Eventually.of_forall fun x => by
            by_cases h : x i ∈ A <;> simp [h]
      simp only [hF, mul_add]
      rw [integral_add hc hb]
      congr 1
      have : (fun x : Fin n → V => (A.indicator 1 (x i) : ℝ) * σr) =
          ((fun x : Fin n → V => x i) ⁻¹' A).indicator (fun _ => σr) := by
        funext x; by_cases h : x i ∈ A
        · simp [indicator_of_mem h, indicator_of_mem (show x ∈ (fun x => x i) ⁻¹' A from h)]
        · simp [indicator_of_notMem h,
            indicator_of_notMem (show x ∉ (fun x : Fin n → V => x i) ⁻¹' A from h)]
      rw [this, integral_indicator_const _ (measurable_pi_apply i hA), smul_eq_mul, mul_comm]
    simp_rw [h1]
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    · rw [marginal_apply _ hA, ENNReal.toReal_mul, ENNReal.toReal_sum
        (fun i _ => measure_ne_top _ _), ← Finset.mul_sum, ENNReal.toReal_inv]
      simp [measureReal_def]; ring
    · rw [← hrep A hA, inner_Gop]
      have hψ : ∀ᵐ x ∂lam, ∀ i, (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) : V → ℝ)
          (x i) = A.indicator 1 (x i) :=
        ae_all_iff.2 fun i => comp_ae μ lam M hM i indicatorConstLp_coeFn
      rw [integral_congr_ae (g := fun x => (n : ℝ)⁻¹ * ∑ i, (A.indicator 1 (x i) * Ψ x)) ?_]
      · rw [integral_const_mul, integral_finsetSum]
        intro i _
        refine hΨint.bdd_mul (c := 1) ?_ ?_
        · exact ((measurable_const.indicator hA).comp
            (measurable_pi_apply i)).aestronglyMeasurable
        · exact Eventually.of_forall fun x => by
            by_cases h : x i ∈ A <;> simp [h]
      · filter_upwards [hψ] with x hx
        simp only [hx, hΨ, ← Finset.sum_mul]
        ring
  set X := (n : ℝ)⁻¹ * ∑ i, ∫ x, (A.indicator 1 (x i)) * F x ∂lam with hX
  have hX0 : 0 ≤ X := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => integral_nonneg_of_ae ?_)
    filter_upwards [hF0] with x hx
    exact mul_nonneg (by by_cases h : x i ∈ A <;> simp [h]) hx
  have hW : marginal (lam.withDensity fun x => ENNReal.ofReal (F x)) A = ENNReal.ofReal X := by
    rw [marginal_apply _ hA]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg_of_ae (by
      filter_upwards [hF0] with x hx
      exact mul_nonneg (by by_cases h : x i ∈ A <;> simp [h]) hx),
      hX, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hnr,
      ENNReal.ofReal_natCast]
  change marginal (lam.withDensity fun x => ENNReal.ofReal (F x)) A + ν A = _
  rw [hW, ← ofReal_measureReal (μ := ν) (s := A) (measure_ne_top ν A),
    ← ENNReal.ofReal_add hX0 measureReal_nonneg, hreal]
  have hm : marginal lam A ≠ ⊤ := by
    rw [marginal_apply _ hA]
    exact ENNReal.mul_ne_top (by simpa using hn.ne') (ENNReal.sum_ne_top.2
      fun i _ => measure_ne_top _ _)
  rw [show σr * (marginal lam A).toReal + (c0 * μ.real A - ν.real A) + ν.real A =
    σr * (marginal lam A).toReal + c0 * μ.real A by ring,
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hσ0,
    ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hm, ofReal_measureReal (measure_ne_top μ A)]

end Corr

section Lin

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

lemma integrable_of_bdd {X : Type*} [MeasurableSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hFm : Measurable F) {C : ℝ} (hC : ∀ y, |F y| ≤ C) : Integrable F P :=
  Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall fun y => by
    simpa [Real.norm_eq_abs] using hC y)

/-- The marginal of a measure on `𝒯_n(K)` has mean `c`: `∫ F dβ̄ = 0` for `F = f(· - c)` on `K`. -/
lemma integral_marginal_lin {n : ℕ} (P : Measure (Fin n → V)) [IsFiniteMeasure P] {K : Set V}
    {c : V} (hP : P (tuples n K c)ᶜ = 0) (f : StrongDual ℝ V) {F : V → ℝ} (hFm : Measurable F)
    {C : ℝ} (hFb : ∀ y, |F y| ≤ C) (hFK : ∀ y ∈ K, F y = f (y - c)) :
    ∫ y, F y ∂(marginal P) = 0 := by
  have hint : ∀ i, Integrable F (P.map fun x => x i) := fun i => by
    have : IsFiniteMeasure (P.map fun x : Fin n → V => x i) := Measure.isFiniteMeasure_map _ _
    exact integrable_of_bdd hFm hFb
  rw [marginal, integral_smul_measure, integral_finsetSum_measure fun i _ => hint i]
  have h2 : ∀ i, ∫ y, F y ∂(P.map fun x => x i) = ∫ x, F (x i) ∂P := fun i =>
    integral_map (measurable_pi_apply i).aemeasurable hFm.aestronglyMeasurable
  simp_rw [h2]
  rw [← integral_finsetSum _ fun i _ => (integrable_of_bdd (hFm.comp (measurable_pi_apply i))
    (fun x => hFb (x i)) : Integrable (fun x : Fin n → V => F (x i)) P)]
  have h3 : ∫ x, ∑ i, F (x i) ∂P = 0 := by
    rw [← integral_zero (Fin n → V) ℝ (μ := P)]
    refine integral_congr_ae ?_
    have : ∀ᵐ x ∂P, x ∈ tuples n K c := ae_iff.2 hP
    filter_upwards [this] with x hx
    rw [Finset.sum_congr rfl fun i _ => hFK _ (hx.1 i), ← map_sum, Finset.sum_sub_distrib,
      hx.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, map_zero]
  rw [h3, smul_zero]

/-- `U(K)` has mean `c = centroid K`. -/
lemma integral_unif_lin {K : Set V} (hK : IsCompact K) (hpos : 0 < volume K) {c : V}
    (hc : centroid K = c) (f : StrongDual ℝ V) {F : V → ℝ} (hFK : ∀ y ∈ K, F y = f (y - c)) :
    ∫ y, F y ∂(unifSet K) = 0 := by
  have := Room.unifSet_isProb hK hpos
  have hae : ∀ᵐ y ∂(unifSet K), y ∈ K := by
    rw [unifSet]
    exact Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  rw [integral_congr_ae (g := fun y => f y - f c) (by
    filter_upwards [hae] with y hy; rw [hFK y hy, map_sub])]
  have hi := unifSet_integrable hK hpos
  have hf : Integrable (fun a => f a) (unifSet K) := f.integrable_comp hi
  have h3 : ∫ a, f a ∂(unifSet K) = f (centroid K) := by
    have := f.integral_comp_comm hi; simpa [centroid] using this
  rw [integral_sub hf (integrable_const _), integral_const, h3, hc]
  simp

end Lin

/-- **The kernel step of Theorem 91, as a hypothesis on the space**: on a compact convex `D` with
room for partners (`q(a) ∈ int D` for `a ∈ int D`), a bounded measurable `φ` with
`∑ φ(xᵢ) = 0` for `λ`-almost every tuple of `𝒯_n(D)` (`n = k + 3`) is affine a.e. on `D`. -/
def KernelHyp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasureSpace V] : Prop :=
  ∀ (k : ℕ) (D : Set V) (c : V), Convex ℝ D → IsCompact D →
    (∀ a ∈ interior D, qpt k c a ∈ interior D) → ∀ φ : V → ℝ, Measurable φ →
      (∃ C, ∀ y, |φ y| ≤ C) → (∀ᵐ x ∂(lebTuples volume (k + 2) D c), ∑ i, φ (x i) = 0) →
      ∃ (a : ℝ) (f : StrongDual ℝ V), ∀ᵐ y ∂(volume.restrict D), φ y = a + f y

/-- The kernel step holds in every finite-dimensional inner product space
(`Robust.kernelAffine_of_room`). -/
theorem kernelHyp_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] : KernelHyp E := by
  intro k D c hDc hD hroom φ hφm ⟨C, hC⟩ hsum
  obtain ⟨a, v, h⟩ := Mixes.Robust.kernelAffine_of_room hDc hD.measurableSet hroom φ hφm
    ⟨C, fun y _ => hC y⟩ hsum
  exact ⟨a, innerSL ℝ v, by simpa [innerSL_apply_apply] using h⟩


section Construct

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

lemma marginal_gam (k : ℕ) (c : V) {r : ℝ} (hr : 0 < r) (g : Measure V) [IsFiniteMeasure g] :
    marginal (((k + 3 : ℕ) : ℝ≥0∞) • gam k c r g) =
      g + ∑ i : Fin (k + 2), (gam k c r g).map (fun x => x i.succ) := by
  rw [marginal_smul, marginal, smul_smul, ENNReal.mul_inv_cancel (by positivity) (by simp),
    one_smul, Fin.sum_univ_succ, gam_map0 k c hr]

/-- **The construction in the proof of Theorem 91.** Given the restriction `β₁` (on `𝒯_n(K)`,
`β₁ ≥ σ λ` with `λ` the Lebesgue measure on `𝒯_n(D)`, `D ⊂ K`), the remainder `g` with
`g + β̄₁ + c₀ 1_D = U(K)`, partners in `D` for every point of `K`, the solution operator of the
linear correction (`hC`, from `abstract_main`) and the smallness condition `C H ≤ σ`, `U(K)` is
`n`-completely mixable (`n = k + 3`). -/
theorem construct {k : ℕ} {c : V} {D K : Set V} (hDm : MeasurableSet D) (hDK : D ⊆ K)
    (hK : IsCompact K) (hKpos : 0 < volume K) (hcK : centroid K = c) {r : ℝ} (hr : 0 < r)
    (hP : ∀ p ∈ K, closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ D)
    [IsFiniteMeasure ((volume : Measure V).restrict D)]
    [IsFiniteMeasure (lebTuples volume (k + 2) D c)]
    (M : ℝ≥0) (hM : ∀ i, (lebTuples volume (k + 2) D c).map (fun x => x i) ≤
      (M : ℝ≥0∞) • (volume : Measure V).restrict D)
    (hbdd : ∃ R, ∀ᵐ y ∂((volume : Measure V).restrict D), ‖y‖ ≤ R) {C : ℝ}
    (hC : ∀ (h : Lp ℝ 2 ((volume : Measure V).restrict D)) (H : ℝ), 0 ≤ H →
      (∀ ψ : Lp ℝ 2 ((volume : Measure V).restrict D),
        |⟪h, ψ⟫| ≤ H * ∫ y, |ψ y| ∂((volume : Measure V).restrict D)) →
      h ∈ (Vlin ((volume : Measure V).restrict D) hbdd c)ᗮ →
      ∃ φ, Gop ((volume : Measure V).restrict D) (lebTuples volume (k + 2) D c) M hM φ = h ∧
        ∀ᵐ y ∂((volume : Measure V).restrict D), |φ y| ≤ C * H)
    (β₁ : Measure (Fin (k + 3) → V)) [IsFiniteMeasure β₁]
    (hβ₁ : β₁ (tuples (k + 3) K c)ᶜ = 0) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hsl : ENNReal.ofReal σ • lebTuples volume (k + 2) D c ≤ β₁)
    {c0 : ℝ} (hc0 : 0 ≤ c0) (g : Measure V) [IsFiniteMeasure g]
    (hg : g + (marginal β₁ + ENNReal.ofReal c0 • (volume : Measure V).restrict D) = unifSet K)
    (hsmall : C * (c0 + (k + 2 : ℝ) * ((g univ).toReal *
      ((volume (closedBall (0 : V) r))⁻¹).toReal)) ≤ σ) :
    CompletelyMixable (k + 3) (unifSet K) := by
  set μ := (volume : Measure V).restrict D with hμ
  set lam := lebTuples volume (k + 2) D c with hlam
  have hKm := hK.measurableSet
  have hprob := Room.unifSet_isProb hK hKpos
  -- `g` lives on `K`
  have hgK : g Kᶜ = 0 := by
    have h1 : g Kᶜ ≤ unifSet K Kᶜ := by
      rw [← hg]; exact le_self_add
    exact le_antisymm (h1.trans (unifSet_compl hKm).le) bot_le
  -- the partners
  have hFr : Fact (0 < r) := ⟨hr⟩
  set γ := gam k c r g with hγ
  set ν := ∑ i : Fin (k + 2), γ.map (fun x => x i.succ) with hν
  set vB := volume (closedBall (0 : V) r)
  have hvB0 : vB ≠ 0 := (vol_ball_pos hr).ne'
  set a : ℝ≥0∞ := g univ * vB⁻¹ with ha
  have hat : a ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top g univ) (ENNReal.inv_ne_top.2 hvB0)
  set Cν : ℝ≥0 := ((k + 2 : ℕ) : ℝ≥0) * a.toNNReal with hCν
  have hgD : ∀ᵐ p ∂g, closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ D := by
    have : ∀ᵐ p ∂g, p ∈ K := ae_iff.2 hgK
    filter_upwards [this] with p hp using hP p hp
  have hνle : ν ≤ (Cν : ℝ≥0∞) • μ := by
    calc ν ≤ ∑ _i : Fin (k + 2), a • μ :=
          Finset.sum_le_sum fun i _ => gam_succ_le k c hr g hDm hgD i
      _ = (Cν : ℝ≥0∞) • μ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
            smul_smul, hCν]
          congr 1
          rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hat]; simp
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨lt_of_le_of_lt (hνle univ) ?_⟩
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  -- the defect `h` as an element of `L²(D)`
  have h1μ : μ ≤ ((1 : ℝ≥0) : ℝ≥0∞) • μ := by simp
  set H2 := Lp ℝ 2 μ
  set hvec : H2 := (InnerProductSpace.toDual ℝ H2).symm
    (c0 • intFun μ μ 1 h1μ - intFun μ ν Cν hνle) with hhvec
  have hinner : ∀ ψ : H2, ⟪hvec, ψ⟫ = c0 * ∫ y, ψ y ∂μ - ∫ y, ψ y ∂ν := by
    intro ψ
    rw [hhvec, InnerProductSpace.toDual_symm_apply]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [intFun_apply μ μ 1 h1μ ψ, intFun_apply μ ν Cν hνle ψ]
  have hνμ : ν ≪ μ := ac_of_le_smul hνle
  -- the bound `|⟪h, ψ⟫| ≤ (c₀ + Cν) ∫ |ψ| dμ`
  have hbound : ∀ ψ : H2, |⟪hvec, ψ⟫| ≤ (c0 + Cν) * ∫ y, |ψ y| ∂μ := by
    intro ψ
    have hi : Integrable (fun y => |(ψ : V → ℝ) y|) μ :=
      ((Lp.memLp ψ).integrable (by norm_num)).abs
    have hi' : Integrable (fun y => |(ψ : V → ℝ) y|) ((Cν : ℝ≥0∞) • μ) := hi.smul_measure
      ENNReal.coe_ne_top
    have h1 : ∫ y, |ψ y| ∂ν ≤ Cν * ∫ y, |ψ y| ∂μ := by
      refine (integral_mono_measure hνle (Eventually.of_forall fun y => abs_nonneg _) hi').trans
        (le_of_eq ?_)
      rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
    rw [hinner]
    calc |c0 * ∫ y, ψ y ∂μ - ∫ y, ψ y ∂ν| ≤ |c0 * ∫ y, ψ y ∂μ| + |∫ y, ψ y ∂ν| := abs_sub _ _
      _ ≤ c0 * ∫ y, |ψ y| ∂μ + ∫ y, |ψ y| ∂ν := by
          rw [abs_mul, abs_of_nonneg hc0]
          exact add_le_add (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hc0)
            abs_integral_le_integral_abs
      _ ≤ c0 * ∫ y, |ψ y| ∂μ + Cν * ∫ y, |ψ y| ∂μ := by linarith
      _ = (c0 + Cν) * ∫ y, |ψ y| ∂μ := by ring
  -- the defect is orthogonal to the linear functions
  have hmβ : IsFiniteMeasure (marginal β₁) :=
    ⟨by rw [marginal_univ (by omega)]; exact measure_lt_top _ _⟩
  have hc0μ : IsFiniteMeasure (ENNReal.ofReal c0 • μ) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hnγ : IsFiniteMeasure (((k + 3 : ℕ) : ℝ≥0∞) • γ) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (measure_lt_top _ _)
  have hγnull : (((k + 3 : ℕ) : ℝ≥0∞) • γ) (tuples (k + 3) K c)ᶜ = 0 := by
    rw [smul_apply, gam_null k c hr g hKm hgK (fun p hp => (hP p hp).trans hDK), smul_zero]
  have horth : hvec ∈ (Vlin μ hbdd c)ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro u ⟨f, rfl⟩
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    set F : V → ℝ := K.indicator fun y => f (y - c) with hF
    have hFm : Measurable F :=
      (f.continuous.measurable.comp (measurable_id.sub measurable_const)).indicator hKm
    have hFb : ∀ y, |F y| ≤ ‖f‖ * (|R| + ‖c‖) := by
      intro y
      by_cases hy : y ∈ K
      · rw [hF, indicator_of_mem hy, ← Real.norm_eq_abs]
        refine (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_sub_le _ _).trans (by linarith [hR y hy, le_abs_self R])
      · rw [hF, indicator_of_notMem hy, abs_zero]; positivity
    have hFK : ∀ y ∈ K, F y = f (y - c) := fun y hy => by rw [hF, indicator_of_mem hy]
    have hFae : (ellL μ hbdd c f : V → ℝ) =ᵐ[μ] F := by
      filter_upwards [ellL_ae μ hbdd c f, ae_restrict_mem hDm] with y h1 h2
      rw [h1, hFK y (hDK h2)]
    have hi1 : ∫ y, (ellL μ hbdd c f : V → ℝ) y ∂μ = ∫ y, F y ∂μ := integral_congr_ae hFae
    have hi2 : ∫ y, (ellL μ hbdd c f : V → ℝ) y ∂ν = ∫ y, F y ∂ν :=
      integral_congr_ae (hνμ.ae_eq hFae)
    -- the two mean identities
    have e1 : ∫ y, F y ∂g + c0 * ∫ y, F y ∂μ = 0 := by
      have := integral_unif_lin hK hKpos hcK f hFK
      rw [← hg, integral_add_measure (integrable_of_bdd hFm hFb)
        (integrable_of_bdd hFm hFb), integral_add_measure (integrable_of_bdd hFm hFb)
        (integrable_of_bdd hFm hFb), integral_marginal_lin β₁ hβ₁ f hFm hFb hFK,
        integral_smul_measure, ENNReal.toReal_ofReal hc0, smul_eq_mul] at this
      linarith
    have e2 : ∫ y, F y ∂g + ∫ y, F y ∂ν = 0 := by
      have := integral_marginal_lin _ hγnull f hFm hFb hFK
      rw [marginal_gam k c hr g, integral_add_measure (integrable_of_bdd hFm hFb)
        (integrable_of_bdd hFm hFb)] at this
      exact this
    rw [real_inner_comm, hinner, hi1, hi2]
    linarith
  -- solve `Gφ = h`
  obtain ⟨φ, hGφ, hφb⟩ := hC hvec (c0 + Cν) (by positivity) hbound horth
  have hrep : ∀ A (hA : MeasurableSet A), ⟪Gop μ lam M hM φ,
      indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)⟫ = c0 * μ.real A - ν.real A := by
    intro A hA
    rw [hGφ, hinner, integral_indicatorConstLp, smul_eq_mul, mul_one]
    congr 1
    rw [integral_congr_ae (hνμ.ae_eq indicatorConstLp_coeFn)]
    exact integral_indicator_one hA
  have hCν : (Cν : ℝ) = (k + 2 : ℝ) * ((g univ).toReal * (vB⁻¹).toReal) := by
    rw [hCν, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, ha, ENNReal.toReal_mul]
    push_cast; ring
  have hσ : C * (c0 + Cν) ≤ σ := by rw [hCν]; exact hsmall
  set W := lam.withDensity fun x =>
    ENNReal.ofReal (σ + ((k + 2 + 1 : ℕ) : ℝ)⁻¹ * ∑ i, φ (x i)) with hWdef
  have hW : ∀ A, MeasurableSet A → marginal W A + ν A =
      ENNReal.ofReal σ * marginal lam A + ENNReal.ofReal c0 * μ A := fun A hA =>
    marginal_corr μ lam M hM (by omega) φ hφb hσ hσ0 ν hc0 hrep hA
  -- the complete mix before symmetrisation
  set β' : Measure (Fin (k + 3) → V) :=
    (β₁ - ENNReal.ofReal σ • lam) + (((k + 3 : ℕ) : ℝ≥0∞) • γ + W) with hβ'
  have hσfin : IsFiniteMeasure (ENNReal.ofReal σ • lam) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hX : marginal (β₁ - ENNReal.ofReal σ • lam) + ENNReal.ofReal σ • marginal lam =
      marginal β₁ := by
    rw [← marginal_smul, ← marginal_add, Measure.sub_add_cancel_of_le hsl]
  have hmarg : marginal β' = unifSet K := by
    ext A hA
    have e := hW A hA
    have eX := congrArg (fun m : Measure V => m A) hX
    simp only [add_apply, smul_apply, smul_eq_mul] at eX
    have eg := congrArg (fun m : Measure V => m A) hg
    simp only [add_apply, smul_apply, smul_eq_mul] at eg
    have hνA : ν A ≠ ⊤ := measure_ne_top ν A
    refine (ENNReal.add_left_inj hνA).1 ?_
    rw [hβ', marginal_add, marginal_add, marginal_gam k c hr g]
    simp only [add_apply]
    rw [← eg, ← eX]
    calc marginal (β₁ - ENNReal.ofReal σ • lam) A + (g A + ν A + marginal W A) + ν A
        = marginal (β₁ - ENNReal.ofReal σ • lam) A + g A + ν A + (marginal W A + ν A) := by
          ring
      _ = _ := by rw [e]; ring
  have hnull : β' (tuples (k + 3) K c)ᶜ = 0 := by
    have hT : (tuples (k + 3) K c)ᶜ ⊆ (tuples (k + 2 + 1) D c)ᶜ := by
      intro x hx hxD
      exact hx ⟨fun i => hDK (hxD.1 i), hxD.2⟩
    have hlam0 : lam (tuples (k + 3) K c)ᶜ = 0 :=
      measure_mono_null hT (lebTuples_null volume hDm c)
    rw [hβ', add_apply, add_apply, hγnull,
      withDensity_absolutelyContinuous lam _ hlam0]
    simp only [add_zero]
    exact measure_mono_null_ae (Eventually.of_forall fun _ => id) <|
      le_antisymm ((Measure.sub_le (μ := β₁) (ν := ENNReal.ofReal σ • lam) _).trans hβ₁.le)
        bot_le
  -- symmetrise
  have hn0 : 0 < k + 3 := by omega
  refine (completelyMixable_unif_iff hn0 hK hKpos).2 ⟨symmetrise β', ?_, ?_,
    permInvariant_symmetrise β', ?_⟩
  · constructor
    rw [← marginal_univ hn0, marginal_symmetrise, hmarg, measure_univ]
  · rw [hcK]
    exact symmetrise_null β' (measurableSet_tuples hKm c).compl (tuples_perm K c) hnull
  · rw [marginal_symmetrise, hmarg]

end Construct


/-- The elementary estimates for the scaling `s = min(1, |K₀|/|K|)` and `c₀ = 1/|K| - s/|K₀|`. -/
lemma scale_est {v0 vK η : ℝ} (hv0 : 0 < v0) (hη : 0 < η) (hη4 : η ≤ v0 / 4)
    (h1 : vK ≤ v0 + η) (h2 : v0 ≤ vK + η) :
    0 < vK ∧ 0 ≤ 1 / vK - min 1 (v0 / vK) / v0 ∧ 1 / vK - min 1 (v0 / vK) / v0 ≤ 2 * η / v0 ^ 2 ∧
      1 - min 1 (v0 / vK) ≤ η / v0 ∧ 1 / 2 ≤ min 1 (v0 / vK) ∧ min 1 (v0 / vK) ≤ 1 := by
  have hvK : 0 < vK := by linarith
  refine ⟨hvK, ?_, ?_, ?_, ?_, min_le_left _ _⟩
  · rcases le_total 1 (v0 / vK) with h | h
    · rw [min_eq_left h]
      rw [le_div_iff₀ hvK] at h
      rw [sub_nonneg, div_le_div_iff₀ hv0 hvK]; linarith
    · rw [min_eq_right h, div_div, mul_comm, ← div_div, div_self hv0.ne', sub_self]
  · rcases le_total 1 (v0 / vK) with h | h
    · rw [min_eq_left h]
      rw [show 1 / vK - 1 / v0 = (v0 - vK) / (vK * v0) by field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : v0 - vK ≤ η := by linarith
      have hvK' : v0 / 2 ≤ vK := by linarith
      have e1 : (v0 - vK) * v0 ≤ η * (2 * vK) := mul_le_mul this (by linarith) hv0.le hη.le
      nlinarith [mul_le_mul_of_nonneg_right e1 hv0.le]
    · rw [min_eq_right h, div_div, mul_comm, ← div_div, div_self hv0.ne', sub_self]
      positivity
  · rcases le_total 1 (v0 / vK) with h | h
    · rw [min_eq_left h, sub_self]; positivity
    · rw [min_eq_right h]
      rw [div_le_one hvK] at h
      rw [show 1 - v0 / vK = (vK - v0) / vK by field_simp, div_le_div_iff₀ hvK hv0]
      nlinarith
  · rcases le_total 1 (v0 / vK) with h | h
    · rw [min_eq_left h]; norm_num
    · rw [min_eq_right h, le_div_iff₀ hvK]; linarith


section Main

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

open Room

omit [(volume : Measure V).IsAddHaarMeasure] in
lemma lebTuples_le_of_subset {m : ℕ} {D K : Set V} (hDK : D ⊆ K) (c : V)
    {S : Set (Fin (m + 1) → V)} (hS : MeasurableSet S) :
    lebTuples volume m D c S ≤ lebTuples volume m K c S := by
  rw [lebTuples_apply _ _ _ hS, lebTuples_apply _ _ _ hS]
  refine measure_mono (inter_subset_inter_right _ (preimage_mono ?_))
  exact fun x hx => ⟨fun i => hDK (hx.1 i), hx.2⟩

omit [(volume : Measure V).IsAddHaarMeasure] in
/-- The rescaled robust mix still dominates `σ λ` on the inner body. -/
lemma lam_le_beta {k : ℕ} {K0 K : Set V} {c : V} {ρ : ℝ} (hKm : MeasurableSet K)
    (hDm : MeasurableSet (innerBody K0 ρ)) (hDK : innerBody K0 ρ ⊆ K)
    (hDK0 : innerBody K0 ρ ⊆ K0) {b : ℝ≥0∞} (hbt : b ≠ ⊤)
    {β₀ : Measure (Fin (k + 2 + 1) → V)}
    (hβ₀l : b • (lebTuples volume (k + 2) K0 c).restrict
      (Mixes.Robust.tuplesRho (k + 2 + 1) K0 c ρ) ≤ β₀)
    {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (s * b.toReal) • lebTuples volume (k + 2) (innerBody K0 ρ) c ≤
      ENNReal.ofReal s • β₀.restrict (tuples (k + 2 + 1) K c) := by
  set D := innerBody K0 ρ
  set T := tuples (k + 2 + 1) K c
  have hT : MeasurableSet T := measurableSet_tuples hKm c
  have hTD : MeasurableSet (tuples (k + 2 + 1) D c) := measurableSet_tuples hDm c
  rw [Measure.le_iff]
  intro S hS
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, Measure.restrict_apply hS,
    ENNReal.ofReal_mul hs, ENNReal.ofReal_toReal hbt, mul_assoc]
  gcongr
  have h1 : lebTuples volume (k + 2) D c S = lebTuples volume (k + 2) D c
      (S ∩ tuples (k + 2 + 1) D c) := (measure_inter_conull (lebTuples_null volume hDm c)).symm
  have hsub : S ∩ tuples (k + 2 + 1) D c ⊆ (S ∩ T) ∩ Mixes.Robust.tuplesRho (k + 2 + 1) K0 c ρ := by
    rintro x ⟨hxS, hx⟩
    refine ⟨⟨hxS, fun i => hDK (hx.1 i), hx.2⟩, ⟨fun i => hDK0 (hx.1 i), hx.2⟩,
      0, fun i _ => hx.1 i⟩
  calc b * lebTuples volume (k + 2) D c S
      ≤ b * lebTuples volume (k + 2) K0 c (S ∩ tuples (k + 2 + 1) D c) := by
        rw [h1]; exact mul_le_mul_right (lebTuples_le_of_subset hDK0 c (hS.inter hTD)) _
    _ ≤ b * (lebTuples volume (k + 2) K0 c).restrict
          (Mixes.Robust.tuplesRho (k + 2 + 1) K0 c ρ) (S ∩ T) := by
        exact mul_le_mul_right ((measure_mono hsub).trans (Measure.le_restrict_apply _ _)) _
    _ ≤ β₀ (S ∩ T) := hβ₀l _

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
lemma marginal_restrict_le {n : ℕ} {K : Set V} (hKm : MeasurableSet K) (c : V)
    (β : Measure (Fin n → V)) {A : Set V} (hA : MeasurableSet A) :
    marginal (β.restrict (tuples n K c)) A ≤ marginal β (A ∩ K) := by
  rw [marginal_apply _ hA, marginal_apply _ (hA.inter hKm)]
  refine mul_le_mul_right (Finset.sum_le_sum fun (i : Fin n) _ => ?_) _
  rw [Measure.restrict_apply (measurable_pi_apply i hA)]
  exact measure_mono fun x hx => ⟨hx.1, hx.2.1 i⟩

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
lemma sum_map_eq_marginal {n : ℕ} (hn : 0 < n) (β : Measure (Fin n → V)) {B : Set V}
    (hB : MeasurableSet B) : ∑ i, β ((fun x => x i) ⁻¹' B) = (n : ℝ≥0∞) * marginal β B := by
  rw [marginal_apply _ hB, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top _), one_mul]

omit [FiniteDimensional ℝ V] [(volume : Measure V).IsAddHaarMeasure] in
/-- Mass of a mix of `K₀` leaving `K`: at most `n` times the uniform mass of `K₀ \ K`. -/
lemma compl_tuples_le {n : ℕ} (hn : 0 < n) {K0 K : Set V} (hK0m : MeasurableSet K0)
    (hKm : MeasurableSet K) (c : V) (β : Measure (Fin n → V))
    (hβn : β (tuples n K0 c)ᶜ = 0) :
    β (tuples n K c)ᶜ ≤ (n : ℝ≥0∞) * marginal β (K0 \ K) := by
  have hsub : (tuples n K c)ᶜ ⊆ (tuples n K0 c)ᶜ ∪ ⋃ i, (fun x => x i) ⁻¹' (K0 \ K) := by
    intro x hx
    by_cases h0 : x ∈ tuples n K0 c
    · right
      obtain ⟨i, hi⟩ := not_forall.1 fun h => hx ⟨h, h0.2⟩
      exact mem_iUnion.2 ⟨i, h0.1 i, hi⟩
    · exact Or.inl h0
  calc β (tuples n K c)ᶜ ≤ β ((tuples n K0 c)ᶜ ∪ ⋃ i, (fun x => x i) ⁻¹' (K0 \ K)) :=
        measure_mono hsub
    _ ≤ β (tuples n K0 c)ᶜ + β (⋃ i, (fun x => x i) ⁻¹' (K0 \ K)) := measure_union_le _ _
    _ ≤ 0 + ∑ i, β ((fun x => x i) ⁻¹' (K0 \ K)) := by
        rw [hβn]; gcongr; exact measure_iUnion_fintype_le _ _
    _ = _ := by rw [zero_add, sum_map_eq_marginal hn β (hK0m.diff hKm)]

/-- The rescaled restricted mix plus `c₀` times Lebesgue measure on `D` lies below `U(K)`. -/
lemma le_unif {n : ℕ} {K0 K D : Set V} (hKm : MeasurableSet K) (hDK : D ⊆ K) (c : V)
    (β : Measure (Fin n → V)) (hβm : marginal β = unifSet K0) {s c0 : ℝ}
    (hcoef : ENNReal.ofReal s * (volume K0)⁻¹ + ENNReal.ofReal c0 = (volume K)⁻¹) :
    marginal (ENNReal.ofReal s • β.restrict (tuples n K c)) +
      ENNReal.ofReal c0 • (volume : Measure V).restrict D ≤ unifSet K := by
  rw [Measure.le_iff]
  intro A hA
  rw [add_apply, marginal_smul, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, unifSet,
    smul_apply, smul_eq_mul, Measure.restrict_apply hA, Measure.restrict_apply hA, ← hcoef]
  have h1 : marginal (β.restrict (tuples n K c)) A ≤ (volume K0)⁻¹ * volume (A ∩ K) := by
    refine (marginal_restrict_le hKm c β hA).trans ?_
    rw [hβm, unifSet, smul_apply, smul_eq_mul, Measure.restrict_apply (hA.inter hKm)]
    exact mul_le_mul_right (measure_mono inter_subset_left) _
  have h2 : volume (A ∩ D) ≤ volume (A ∩ K) := measure_mono (inter_subset_inter_right _ hDK)
  calc ENNReal.ofReal s * marginal (β.restrict (tuples n K c)) A +
        ENNReal.ofReal c0 * volume (A ∩ D)
      ≤ ENNReal.ofReal s * ((volume K0)⁻¹ * volume (A ∩ K)) +
        ENNReal.ofReal c0 * volume (A ∩ K) := by gcongr
    _ = _ := by ring

/-- **Theorem 91, centred form.** Let `n = k + 3`, `K₀` a convex body with centroid `c`,
`as(K₀) ≤ a < n - 1` about `c`, and `U(K₀)` robustly `n`-completely mixable. Given the cited
compactness `HSCompact` and the kernel step `KernelHyp`, there is `ε > 0` such that `U(K)` is
`n`-completely mixable for every convex body `K` with centroid `c` and `d_H(K, K₀) < ε`. -/
theorem thm91_centred (hHS : HSCompact V) (hKer : KernelHyp V) {k : ℕ} {K0 : Set V}
    (hK0c : Convex ℝ K0) (hK0 : IsCompact K0) (hK0i : (interior K0).Nonempty) {a : ℝ}
    (ha : 0 < a) (han : a < ((k + 2 : ℕ) : ℝ)) (hasym : AsymLE K0 (centroid K0) a)
    (hrob : Mixes.Robust.RobustlyCM (k + 2) K0) :
    ∃ ε > 0, ∀ K : Set V, Convex ℝ K → IsCompact K → (interior K).Nonempty →
      centroid K = centroid K0 → hausdorffDist K K0 < ε →
      CompletelyMixable (k + 3) (unifSet K) := by
  set c := centroid K0 with hc
  -- a ball about the centroid
  have hcint := mem_interior_of_asym hK0c hK0i ha.le hasym
  obtain ⟨s0, hs0, hbs⟩ := Metric.isOpen_iff.1 isOpen_interior c hcint
  set s := s0 / 2 with hs
  have hs : 0 < s := by positivity
  have hball : closedBall c s ⊆ K0 := fun y hy =>
    interior_subset (hbs (lt_of_le_of_lt (mem_closedBall.1 hy) (by linarith)))
  -- the radii
  set N : ℝ := ((k + 2 : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by have := k.cast_nonneg (α := ℝ); rw [hN]; push_cast; linarith
  have hθ1 : a / N < 1 := (div_lt_one (by linarith)).2 han
  set R0 := (1 - a / N) * s with hR0
  have hR0 : 0 < R0 := mul_pos (by linarith) hs
  set ρ := R0 / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  set r := ρ / ((k + 1 : ℕ) : ℝ) with hr
  have hr0 : 0 < r := by positivity
  have hkr : ((k + 1 : ℕ) : ℝ) * r = ρ := by rw [hr]; field_simp
  set D := innerBody K0 ρ with hD
  have hDcl : IsClosed D := isClosed_innerBody hK0.isClosed ρ
  have hDK0 : D ⊆ K0 := innerBody_subset hρ0.le
  have hDcpt : IsCompact D := hK0.of_isClosed_subset hDcl hDK0
  have hDm : MeasurableSet D := hDcl.measurableSet
  have hDconv : Convex ℝ D := convex_innerBody hK0c ρ
  have hPb : ∀ p, (∃ x ∈ K0, dist p x ≤ ρ) →
      closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ D := by
    rintro p ⟨x, hx, hpx⟩
    have h1 := partner_ball hK0c hK0.isClosed hball ha han hasym hx hpx
    have h2 := closedBall_sub_innerBody (ρ := ρ) h1
    refine (closedBall_subset_closedBall ?_).trans h2
    rw [hkr]
    have : ρ / N ≤ ρ := div_le_self hρ0.le hN1
    linarith
  have hPD : ∀ p ∈ D, closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ D :=
    fun p hp => hPb p ⟨p, hDK0 hp, by simp [hρ0.le]⟩
  have hroom : ∀ a' ∈ interior D, qpt k c a' ∈ interior D := by
    intro a' ha'
    refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (ball_mem_nhds _ hρ0) ?_)
    exact ball_subset_closedBall.trans (hkr ▸ hPD a' (interior_subset ha'))
  -- the operator on `L²(D)`
  set μ := (volume : Measure V).restrict D with hμ
  have hμfin : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hDcpt.measure_lt_top.ne
  set lam := lebTuples volume (k + 2) D c with hlam
  have hlamfin : IsFiniteMeasure lam := lebTuples_finite volume hDcpt c
  have hvD : volume D ≠ ⊤ := hDcpt.measure_lt_top.ne
  set M : ℝ≥0 := (volume D ^ (k + 1)).toNNReal
  have hM : ∀ i, lam.map (fun x => x i) ≤ (M : ℝ≥0∞) • μ := fun i => by
    rw [ENNReal.coe_toNNReal (ENNReal.pow_ne_top hvD)]; exact coord_le hDm c i
  set M' : ℝ≥0 := (volume D ^ k).toNNReal
  have hpair : ∀ i j, i ≠ j → lam.map (fun x => (x j, x i)) ≤ (M' : ℝ≥0∞) • μ.prod μ :=
    fun i j hij => by
      rw [ENNReal.coe_toNNReal (ENNReal.pow_ne_top hvD)]; exact pair_le hDm c i j hij
  set vB := volume (closedBall (0 : V) r) with hvB
  have hvB0 : vB ≠ 0 := (vol_ball_pos hr0).ne'
  have hvBt : vB ≠ ⊤ := vol_ball_ne_top r
  set α : ℝ≥0 := (vB ^ (k + 1)).toNNReal
  have hα : 0 < α := ENNReal.toNNReal_pos (pow_ne_zero _ hvB0) (ENNReal.pow_ne_top hvBt)
  have hlow : (α : ℝ≥0∞) • μ ≤ lam.map (fun x => x 0) := by
    rw [ENNReal.coe_toNNReal (ENNReal.pow_ne_top hvBt)]; exact coord0_ge hDm c hr0 hPD
  have hsum : ∀ᵐ x ∂lam, ∑ i, x i = ((k + 2 + 1 : ℕ) : ℝ) • c := by
    have : ∀ᵐ x ∂lam, x ∈ tuples (k + 2 + 1) D c := ae_iff.2 (lebTuples_null volume hDm c)
    filter_upwards [this] with x hx using hx.2
  obtain ⟨R, hR⟩ := hK0.isBounded.exists_norm_le
  have hbdd : ∃ R, ∀ᵐ y ∂μ, ‖y‖ ≤ R :=
    ⟨R, ae_restrict_of_forall_mem hDm fun y hy => hR y (hDK0 hy)⟩
  obtain ⟨C, hC0, hC⟩ := abstract_main μ lam M hM hHS hbdd c hsum hα 0 hlow hpair
    (hKer k D c hDconv hDcpt hroom)
  -- the robust complete mix of `K₀`
  obtain ⟨b, hb, hbt, β₀, hβ₀p, hβ₀n, hβ₀perm, hβ₀m, hβ₀l⟩ := hrob ρ hρ0
  set bR := b.toReal with hbR
  have hbR : 0 < bR := ENNReal.toReal_pos hb.ne' hbt
  -- the smallness parameter
  have hK0pos : 0 < volume K0 := Measure.measure_pos_of_nonempty_interior _ hK0i
  set v0 := (volume K0).toReal with hv0
  have hv0 : 0 < v0 := ENNReal.toReal_pos hK0pos.ne' hK0.measure_lt_top.ne
  set vBr := vB.toReal with hvBr
  have hvBr : 0 < vBr := ENNReal.toReal_pos hvB0 hvBt
  set Ht := bR / (2 * (C + 1)) with hHt
  have hHt : 0 < Ht := by positivity
  set L := 2 / v0 ^ 2 + (k + 2 : ℝ) * ((k + 4) / (v0 * vBr)) with hL
  have hL0 : 0 ≤ L := by positivity
  set η := min (v0 / 4) (Ht / (L + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηL : η * L ≤ Ht := by
    have h1 : η ≤ Ht / (L + 1) := min_le_right _ _
    calc η * L ≤ Ht / (L + 1) * L := mul_le_mul_of_nonneg_right h1 hL0
      _ ≤ Ht := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
  obtain ⟨δ1, hδ1, hvol1⟩ := vol_innerBody_close hK0c hK0 (η := ENNReal.ofReal η)
    (ENNReal.ofReal_pos.2 hη0)
  obtain ⟨δ2, hδ2, hvol2⟩ := vol_cthickening_close hK0 (η := ENNReal.ofReal η)
    (ENNReal.ofReal_pos.2 hη0)
  refine ⟨min ρ (min δ1 δ2), lt_min hρ0 (lt_min hδ1 hδ2), fun K hKc hK hKi hcK hd => ?_⟩
  -- geometry of `K`
  have hKm := hK.measurableSet
  have hKne : K.Nonempty := hKi.mono interior_subset
  have hK0ne : K0.Nonempty := hK0i.mono interior_subset
  have hfin : hausdorffEDist K K0 ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded hKne hK0ne hK.isBounded hK0.isBounded
  have hDK : D ⊆ K := innerBody_subset_of_hausdorff hKc hK.isClosed hfin hd (min_le_left _ _)
  have hI1K : innerBody K0 δ1 ⊆ K := innerBody_subset_of_hausdorff hKc hK.isClosed hfin hd
    ((min_le_right _ _).trans (min_le_left _ _))
  have hKth : K ⊆ cthickening δ2 K0 := (subset_cthickening_of_hausdorff hfin hd).trans
    (cthickening_mono ((min_le_right _ _).trans (min_le_right _ _)) K0)
  have hP : ∀ p ∈ K, closedBall (qpt k c p) (((k + 1 : ℕ) : ℝ) * r) ⊆ D := by
    intro p hp
    obtain ⟨x, hx, hpx⟩ := exists_dist_lt_of_hausdorffDist_lt hp hd hfin
    exact hPb p ⟨x, hx, hpx.le.trans (min_le_left _ _)⟩
  have hKpos : 0 < volume K := Measure.measure_pos_of_nonempty_interior _ hKi
  -- volumes
  set vK := (volume K).toReal with hvK
  have hKt : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hK0t : volume K0 ≠ ⊤ := hK0.measure_lt_top.ne
  have hv1 : vK ≤ v0 + η := by
    have h := (measure_mono hKth).trans hvol2
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hK0t, ENNReal.ofReal_ne_top⟩) h
    rwa [ENNReal.toReal_add hK0t ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη0.le] at this
  have hI1t : volume (innerBody K0 δ1) ≠ ⊤ :=
    ne_top_of_le_ne_top hK0t (measure_mono (innerBody_subset hδ1.le))
  have hv2 : v0 ≤ vK + η := by
    have h : volume K0 ≤ volume K + ENNReal.ofReal η :=
      hvol1.trans (by gcongr)
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hKt, ENNReal.ofReal_ne_top⟩) h
    rwa [ENNReal.toReal_add hKt ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη0.le] at this
  have hdiff : volume (K0 \ K) ≤ ENNReal.ofReal η := by
    refine (measure_mono (sdiff_subset_sdiff_right hI1K)).trans ?_
    exact (measure_sdiff_le_iff_le_add (isClosed_innerBody hK0.isClosed δ1).nullMeasurableSet
      (innerBody_subset hδ1.le) hI1t).2 hvol1
  set sc := min 1 (v0 / vK) with hsc
  set c0 := 1 / vK - sc / v0 with hc0d
  obtain ⟨hvK0, hc00, hc0η, hsη, hs2, hs1⟩ :=
    scale_est hv0 hη0 (min_le_left _ _) hv1 hv2
  have hsc0 : 0 ≤ sc := by linarith
  -- the rescaled restricted mix
  set T := tuples (k + 2 + 1) K c with hT
  have hTm : MeasurableSet T := measurableSet_tuples hKm c
  set β₁ : Measure (Fin (k + 3) → V) := ENNReal.ofReal sc • β₀.restrict T with hβ₁d
  have hβ₁fin : IsFiniteMeasure β₁ := by
    constructor
    rw [hβ₁d, smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hβ₁ : β₁ (tuples (k + 3) K c)ᶜ = 0 := by
    rw [hβ₁d, smul_apply, Measure.restrict_apply hTm.compl, compl_inter_self, measure_empty,
      smul_zero]
  set σ := sc * bR with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hsl : ENNReal.ofReal σ • lam ≤ β₁ := lam_le_beta hKm hDm hDK hDK0 hbt hβ₀l hsc0
  -- the uniform remainder
  have hvKe : volume K = ENNReal.ofReal vK := (ENNReal.ofReal_toReal hKt).symm
  have hv0e : volume K0 = ENNReal.ofReal v0 := (ENNReal.ofReal_toReal hK0t).symm
  have hcoef : ENNReal.ofReal sc * (volume K0)⁻¹ + ENNReal.ofReal c0 = (volume K)⁻¹ := by
    rw [hv0e, hvKe, ← ENNReal.ofReal_inv_of_pos hv0, ← ENNReal.ofReal_inv_of_pos hvK0,
      ← ENNReal.ofReal_mul hsc0, ← ENNReal.ofReal_add (by positivity) hc00]
    congr 1; rw [hsc]; field_simp; ring
  have hle : marginal β₁ + ENNReal.ofReal c0 • μ ≤ unifSet K :=
    le_unif (n := k + 2 + 1) hKm hDK c β₀ hβ₀m hcoef
  have hUK := Room.unifSet_isProb hK hKpos
  have hXfin : IsFiniteMeasure (marginal β₁ + ENNReal.ofReal c0 • μ) :=
    isFiniteMeasure_of_le (unifSet K) hle
  set g := unifSet K - (marginal β₁ + ENNReal.ofReal c0 • μ) with hgd
  have hgfin : IsFiniteMeasure g := isFiniteMeasure_of_le (unifSet K) Measure.sub_le
  have hg : g + (marginal β₁ + ENNReal.ofReal c0 • μ) = unifSet K :=
    Measure.sub_add_cancel_of_le hle
  -- the mass of `g`
  have hβ₀T : β₀ T ≤ 1 := prob_le_one
  have hgu1 : g univ ≤ 1 - ENNReal.ofReal sc * β₀ T := by
    rw [hgd, Measure.sub_apply MeasurableSet.univ hle, measure_univ]
    refine tsub_le_tsub_left ?_ _
    calc ENNReal.ofReal sc * β₀ T = marginal β₁ univ := by
          rw [marginal_univ (by omega), hβ₁d, smul_apply, Measure.restrict_apply_univ,
            smul_eq_mul]
      _ ≤ _ := by rw [add_apply]; exact le_self_add
  have hsT1 : ENNReal.ofReal sc * β₀ T ≤ 1 :=
    mul_le_one' (ENNReal.ofReal_le_one.2 hs1) hβ₀T
  have hgu2 : (g univ).toReal ≤ 1 - sc * (β₀ T).toReal := by
    have := ENNReal.toReal_mono (by simp) hgu1
    rwa [ENNReal.toReal_sub_of_le hsT1 ENNReal.one_ne_top, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hsc0, ENNReal.toReal_one] at this
  have hTc : (β₀ T).toReal + (β₀ Tᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hTm, measure_univ, ENNReal.toReal_one]
  have hTc1 : β₀ Tᶜ ≤ ((k + 2 + 1 : ℕ) : ℝ≥0∞) * ((volume K0)⁻¹ * ENNReal.ofReal η) := by
    refine (compl_tuples_le (by omega) hK0.measurableSet hKm c β₀ hβ₀n).trans ?_
    rw [hβ₀m, unifSet, smul_apply, smul_eq_mul,
      Measure.restrict_apply (hK0.measurableSet.diff hKm)]
    gcongr
    exact (measure_mono inter_subset_left).trans hdiff
  have hTc2 : (β₀ Tᶜ).toReal ≤ (k + 3) * (η / v0) := by
    have hne : ((k + 2 + 1 : ℕ) : ℝ≥0∞) * ((volume K0)⁻¹ * ENNReal.ofReal η) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hK0pos.ne') ENNReal.ofReal_ne_top)
    have := ENNReal.toReal_mono hne hTc1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hη0.le,
      ENNReal.toReal_natCast] at this
    convert this using 1
    push_cast; ring
  have hG0 : 0 ≤ (g univ).toReal := ENNReal.toReal_nonneg
  have hgu : (g univ).toReal ≤ (k + 4) * η / v0 := by
    have ht0 : 0 ≤ (β₀ Tᶜ).toReal := ENNReal.toReal_nonneg
    have e1 : (g univ).toReal ≤ (1 - sc) + (β₀ Tᶜ).toReal := by nlinarith
    calc (g univ).toReal ≤ η / v0 + (k + 3) * (η / v0) := by linarith
      _ = (k + 4) * η / v0 := by ring
  -- the smallness condition
  have hX : c0 + (k + 2 : ℝ) * ((g univ).toReal * ((vB)⁻¹).toReal) ≤ Ht := by
    rw [ENNReal.toReal_inv]
    have h1 : (g univ).toReal * vBr⁻¹ ≤ (k + 4) * η / v0 * vBr⁻¹ :=
      mul_le_mul_of_nonneg_right hgu (by positivity)
    calc c0 + (k + 2 : ℝ) * ((g univ).toReal * vBr⁻¹)
        ≤ 2 * η / v0 ^ 2 + (k + 2 : ℝ) * ((k + 4) * η / v0 * vBr⁻¹) := by gcongr
      _ = η * L := by rw [hL]; field_simp
      _ ≤ Ht := hηL
  have hCH : C * Ht ≤ bR / 2 := by
    have e : C * Ht = bR / 2 * (C / (C + 1)) := by
      rw [show Ht = bR / (2 * (C + 1)) from rfl]; field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).2 (by linarith))
  have hsmall : C * (c0 + (k + 2 : ℝ) * ((g univ).toReal *
      ((volume (closedBall (0 : V) r))⁻¹).toReal)) ≤ σ := by
    calc _ ≤ C * Ht := mul_le_mul_of_nonneg_left hX hC0
      _ ≤ bR / 2 := hCH
      _ ≤ σ := by
          have := mul_le_mul_of_nonneg_right hs2 hbR.le
          rw [hσ]; linarith
  exact construct hDm hDK hK hKpos hcK hr0 hP M hM hbdd hC β₁ hβ₁ hσ0 hsl hc00 g hg hsmall

end Main


section Translate

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

open Room

lemma unifSet_translate (p : V) (K : Set V) :
    unifSet ((fun x => x + p) '' K) = (unifSet K).map (fun x => x + p) := by
  ext S hS
  rw [Measure.map_apply (measurable_add_const p) hS, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply (measurable_add_const p hS), Measure.restrict_apply hS,
    ← image_preimage_inter, image_add_right, image_add_right, measure_preimage_add_right,
    measure_preimage_add_right]

lemma centroid_translate {K : Set V} (hK : IsCompact K) (hpos : 0 < volume K) (p : V) :
    centroid ((fun x => x + p) '' K) = centroid K + p := by
  have := Room.unifSet_isProb hK hpos
  have e := integral_map (μ := unifSet K) (measurable_add_const p).aemeasurable
    (f := id) aestronglyMeasurable_id
  simp only [id] at e
  rw [centroid, unifSet_translate, e,
    integral_add (f := fun x : V => x) (unifSet_integrable hK hpos) (integrable_const p),
    integral_const, probReal_univ, one_smul]
  rfl

/-- **Theorem 91** for `n = k + 3` (`Thm91Stmt V (k + 2)`), given the cited compactness
`HSCompact V` and the kernel step `KernelHyp V`: translating `K` so that its centroid is that of
`K₀` reduces it to `thm91_centred`. -/
theorem thm91 (hHS : HSCompact V) (hKer : KernelHyp V) (k : ℕ) :
    Mixes.Robust.Thm91Stmt V (k + 2) := by
  intro K0 hK0c hK0 hK0i ⟨a, ha, han, hasym⟩ hrob
  obtain ⟨ε, hε, H⟩ := thm91_centred hHS hKer hK0c hK0 hK0i ha han hasym hrob
  refine ⟨ε, hε, fun K hKc hK hKi hd => ?_⟩
  have hKpos : 0 < volume K := Measure.measure_pos_of_nonempty_interior _ hKi
  set c0 := centroid K0
  set p := c0 - centroid K
  set T : V ≃ᵃ[ℝ] V := AffineEquiv.constVAdd ℝ V p
  have hT : ⇑T = fun x => x + p := funext fun x => by simp [T, add_comm]
  apply Mixes.Robust.completelyMixable_of_affine_image T
  rw [hT]
  have hK'c : Convex ℝ ((fun x => x + p) '' K) := by
    rw [← hT]; exact hKc.affine_image T.toAffineMap
  have hK'k : IsCompact ((fun x => x + p) '' K) := hK.image (continuous_id.add continuous_const)
  have hK'i : (interior ((fun x => x + p) '' K)).Nonempty := by
    have := (Homeomorph.addRight p).image_interior K
    simp only [Homeomorph.coe_addRight] at this
    rw [← this]; exact hKi.image _
  have hc' : centroid ((fun x => x + p) '' K) = c0 := by
    rw [centroid_translate hK hKpos]; simp [p]
  refine H _ hK'c hK'k hK'i hc' ?_
  have hiso : Isometry (fun x : V => x + c0) := (IsometryEquiv.addRight c0).isometry
  have e1 : (fun x => x + c0) '' ((fun x => x - centroid K) '' K) = (fun x => x + p) '' K := by
    rw [image_image]; congr 1; funext x; simp only [p]; abel
  have e2 : (fun x => x + c0) '' ((fun x => x - c0) '' K0) = K0 := by
    rw [image_image]; simp
  rw [← e1, ← e2, hausdorffDist_image hiso]
  exact hd

end Translate


section Transport

open Room

/-- The kernel step transfers along a volume-preserving linear isomorphism. -/
theorem kernelHyp_transport {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W] [SigmaFinite (volume : Measure W)]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasureSpace V]
    [BorelSpace V]
    [SigmaFinite (volume : Measure V)]
    (e : W ≃L[ℝ] V) (he : MeasurePreserving e volume volume) (h : KernelHyp W) :
    KernelHyp V := by
  intro k D c hDc hD hroom φ hφm ⟨C, hC⟩ hsum
  have hem : Measurable e := e.continuous.measurable
  set D' := e ⁻¹' D with hD'
  set c' := e.symm c with hc'
  have hqpt : ∀ a, e (qpt k c' a) = qpt k c (e a) := by
    intro a; simp [qpt, c', map_sub, map_smul]
  have hD'c : Convex ℝ D' := hDc.linear_preimage (e : W →ₗ[ℝ] V)
  have hD'k : IsCompact D' := e.toHomeomorph.isCompact_preimage.2 hD
  have hint : interior D' = e ⁻¹' interior D := (e.toHomeomorph.preimage_interior D).symm
  have hroom' : ∀ a ∈ interior D', qpt k c' a ∈ interior D' := by
    intro a ha
    rw [hint] at ha ⊢
    show e (qpt k c' a) ∈ interior D
    rw [hqpt]; exact hroom _ ha
  set E : (Fin (k + 2) → W) → (Fin (k + 2) → V) := fun x i => e (x i) with hEd
  have hE : MeasurePreserving E (Measure.pi fun _ => volume) (Measure.pi fun _ => volume) :=
    measurePreserving_pi _ _ fun _ => he
  have hemb : ∀ y, embed c (E y) = fun i => e (embed c' y i) := by
    intro y; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [embed_last, embed_last, map_sub, map_smul, map_sum, hc',
        ContinuousLinearEquiv.apply_symm_apply]
    · rw [embed_castSucc, embed_castSucc]
  have hφe : Measurable (φ ∘ e) := hφm.comp hem
  have hsumm : ∀ (ψ : V → ℝ), Measurable ψ →
      MeasurableSet {x : Fin (k + 2 + 1) → V | ∑ i, ψ (x i) = 0} :=
    fun ψ hψ => measurableSet_eq_fun
      (Finset.measurable_sum _ fun i _ => hψ.comp (measurable_pi_apply i)) measurable_const
  have hsumW : MeasurableSet {x : Fin (k + 2 + 1) → W | ∑ i, (φ ∘ e) (x i) = 0} :=
    measurableSet_eq_fun
      (Finset.measurable_sum _ fun i _ => hφe.comp (measurable_pi_apply i)) measurable_const
  have hsum' : ∀ᵐ x ∂(lebTuples volume (k + 2) D' c'), ∑ i, (φ ∘ e) (x i) = 0 := by
    rw [lebTuples] at hsum ⊢
    have h1 := (ae_map_iff (measurable_embed c).aemeasurable (hsumm φ hφm)).1 hsum
    rw [ae_restrict_iff' (measurable_embed c (measurableSet_tuples hD.measurableSet c))] at h1
    have h2 := hE.quasiMeasurePreserving.ae h1
    refine (ae_map_iff (measurable_embed c').aemeasurable hsumW).2 ?_
    rw [ae_restrict_iff' (measurable_embed c' (measurableSet_tuples
      (hD.measurableSet.preimage hem) c'))]
    filter_upwards [h2] with y hy hyT
    have hT : embed c (E y) ∈ tuples (k + 2 + 1) D c := by
      rw [hemb]
      refine ⟨fun i => hyT.1 i, ?_⟩
      rw [← map_sum, hyT.2, map_smul, hc', ContinuousLinearEquiv.apply_symm_apply]
    have := hy hT
    rw [hemb] at this
    simpa using this
  obtain ⟨a, f', hf'⟩ := h k D' c' hD'c hD'k hroom' (φ ∘ e) hφe ⟨C, fun y => hC _⟩ hsum'
  refine ⟨a, f'.comp (e.symm : V →L[ℝ] W), ?_⟩
  have hres : MeasurePreserving e (volume.restrict D') (volume.restrict D) :=
    he.restrict_preimage hD.measurableSet
  have hmeas : MeasurableSet {y | φ y = a + (f'.comp (e.symm : V →L[ℝ] W)) y} :=
    measurableSet_eq_fun hφm (measurable_const.add
      (f'.comp (e.symm : V →L[ℝ] W)).continuous.measurable)
  rw [← hres.map_eq]
  refine (ae_map_iff hem.aemeasurable hmeas).2 (hf'.mono fun y hy => ?_)
  simpa using hy

/-- The kernel step in the plane `ℝ × ℝ`, transported from the Euclidean plane. -/
theorem kernelHyp_prod : KernelHyp (ℝ × ℝ) := by
  set e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  exact kernelHyp_transport e he kernelHyp_inner

end Transport

section Cor93

open Room

/-- **Corollary 93 (a)** without Theorem 91 as a hypothesis, only the cited compactness
`HSCompact (ℝ × ℝ)`: for a convex body `K₀ ⊂ ℝ²` other than a triangle that is mapped onto itself
by an affine map `A ≠ id` with `A³ = id`, there is `ε > 0` such that `U(K)` is `3`-completely
mixable for every convex body `K` with `δ(K, K₀) < 1 + ε`. -/
theorem cor93a (hHS : HSCompact (ℝ × ℝ)) {K0 : Set (ℝ × ℝ)} (hK0c : Convex ℝ K0)
    (hK0 : IsCompact K0) (hK0i : (interior K0).Nonempty) (hT : ¬ IsTriangle K0)
    (A : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) (hm : (⇑A)^[3] = id) (hA : ∃ x, A x ≠ x)
    (hAK : A '' K0 = K0) :
    ∃ ε > 0, ∀ K : Set (ℝ × ℝ), Convex ℝ K → IsCompact K → Mixes.Robust.BMClose K K0 ε →
      CompletelyMixable 3 (unifSet K) :=
  Mixes.Robust.cor93a (thm91 hHS kernelHyp_prod 0) hK0c hK0 hK0i hT A hm hA hAK

/-- **Corollary 93 (b)** without Theorem 91 as a hypothesis, only the cited compactness
`HSCompact ℂ`: there is `ε > 0` such that `U(K)` is `n`-completely mixable for every `n ≥ 3` and
every convex body `K ⊂ ℂ` with `δ(K, B) < 1 + ε`, `B` the unit disc. -/
theorem cor93b (hHS : HSCompact ℂ) :
    ∃ ε > 0, ∀ K : Set ℂ, Convex ℝ K → IsCompact K → Mixes.Robust.BMClose K (closedBall 0 1) ε →
      ∀ n, 3 ≤ n → CompletelyMixable n (unifSet K) :=
  Mixes.Robust.cor93b fun m hm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    exact thm91 hHS kernelHyp_inner k

/-- **Corollary 93 (c)** without Theorem 91 as a hypothesis, only the cited compactness
`HSCompact E`: in every finite-dimensional inner product space of dimension `d ≥ 2` there is
`ε > 0` such that `U(K)` is `n`-completely mixable for every `n ≥ 3` and every convex body `K`
with `δ(K, B) < 1 + ε`, `B` the unit ball. -/
theorem cor93c {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (hHS : HSCompact E) (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ ε > 0, ∀ K : Set E, Convex ℝ K → IsCompact K → Mixes.Robust.BMClose K (closedBall 0 1) ε →
      ∀ n, 3 ≤ n → CompletelyMixable n (unifSet K) :=
  Mixes.Robust.cor93c' hE fun m hm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    exact thm91 hHS kernelHyp_inner k

end Cor93

end Mixes.RobustB
