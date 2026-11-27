import Mixes.Large

/-!
# Lemma 112 and Theorem 113 (Section 23): local limit theorem for different densities

Work in progress.
-/

open MeasureTheory Real RealInnerProductSpace FourierTransform Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Thm113

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Taylor

/-- `|e^{-iθ} - (1 - iθ - θ²/2)| ≤ |θ|³` for `|θ| ≤ 1`. -/
lemma norm_cexp_taylor {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp (-(θ : ℂ) * Complex.I) - (1 - (θ : ℂ) * Complex.I - (θ : ℂ) ^ 2 / 2)‖ ≤
      |θ| ^ 3 := by
  have hx : ‖-(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.exp_bound (x := -(θ : ℂ) * Complex.I) (by rw [hx]; exact hθ) (n := 3)
    (by norm_num)
  rw [hx] at h
  have hs : ∑ m ∈ Finset.range 3, (-(θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      1 - (θ : ℂ) * Complex.I - (θ : ℂ) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hs] at h
  refine h.trans ?_
  have : (0 : ℝ) ≤ |θ| ^ 3 := by positivity
  norm_num at h ⊢
  nlinarith

lemma norm_taylor_poly_le {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖1 - (θ : ℂ) * Complex.I - (θ : ℂ) ^ 2 / 2‖ ≤ 3 := by
  have h1 : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hθ
  have h2 : ‖(θ : ℂ) ^ 2 / 2‖ ≤ 1 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have : |θ| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hθ
    have h2 : ‖(2:ℂ)‖ = 2 := by simp
    rw [h2]
    linarith
  have := norm_sub_le (1 - (θ : ℂ) * Complex.I) ((θ : ℂ) ^ 2 / 2)
  have := norm_sub_le (1 : ℂ) ((θ : ℂ) * Complex.I)
  have h0 : ‖(1:ℂ)‖ = 1 := norm_one
  linarith

end Taylor

section ClassH

/-- The class `𝓗` of Lemma 112: `h` is a measurable probability density vanishing outside a
convex body `K` (compact, convex) that contains a closed ball of radius `r` and has diameter at
most `R`, with `e^{-A} ≤ |K| h ≤ e^A` on `K`. -/
structure InH (A r R : ℝ) (K : Set E) (h : E → ℝ) : Prop where
  compact : IsCompact K
  convex : Convex ℝ K
  ball : ∃ b, Metric.closedBall b r ⊆ K
  diam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R
  meas : Measurable h
  zero : ∀ y ∉ K, h y = 0
  int : ∫ y, h y = 1
  low : ∀ y ∈ K, exp (-A) ≤ volume.real K * h y
  up : ∀ y ∈ K, volume.real K * h y ≤ exp A

variable {A r R : ℝ} {K : Set E} {h : E → ℝ}

lemma InH.volPos (hH : InH A r R K h) (hr : 0 ≤ r) : 0 < volume.real K := by
  obtain ⟨b, hb⟩ := hH.ball
  have hbK : b ∈ K := hb (Metric.mem_closedBall_self hr)
  have h1 := hH.low b hbK
  have hK0 : 0 ≤ volume.real K := measureReal_nonneg
  rcases hK0.lt_or_eq with h2 | h2
  · exact h2
  · rw [← h2, zero_mul] at h1; exact absurd h1 (not_le.2 (exp_pos _))

lemma InH.nonneg (hH : InH A r R K h) (hr : 0 ≤ r) (y : E) : 0 ≤ h y := by
  by_cases hy : y ∈ K
  · have h1 := hH.low y hy
    have h2 := hH.volPos hr
    by_contra hneg
    replace hneg := not_le.1 hneg
    have : volume.real K * h y < 0 := mul_neg_of_pos_of_neg h2 hneg
    linarith [exp_pos (-A)]
  · rw [hH.zero y hy]

/-- The bound `h ≤ e^A / |K|`. -/
lemma InH.le_max (hH : InH A r R K h) (hr : 0 ≤ r) (y : E) :
    h y ≤ exp A / volume.real K := by
  have h2 := hH.volPos hr
  by_cases hy : y ∈ K
  · rw [le_div_iff₀ h2, mul_comm]; exact hH.up y hy
  · rw [hH.zero y hy]; positivity

lemma InH.subset_ball (hH : InH A r R K h) (hr : 0 ≤ r) :
    ∃ b, Metric.closedBall b r ⊆ K ∧ K ⊆ Metric.closedBall b R := by
  obtain ⟨b, hb⟩ := hH.ball
  have hbK : b ∈ K := hb (Metric.mem_closedBall_self hr)
  exact ⟨b, hb, fun y hy => by
    rw [Metric.mem_closedBall]; exact hH.diam y hy b hbK⟩

lemma InH.integrable (hH : InH A r R K h) (_hr : 0 ≤ r) : Integrable h := by
  by_contra hni
  have := integral_undef hni
  rw [hH.int] at this
  exact one_ne_zero this

/-- Integrability of `h • g` for `g` bounded on `K`. -/
lemma InH.integrable_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hH : InH A r R K h) (hr : 0 ≤ r) {g : E → F} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hb : ∀ y ∈ K, ‖g y‖ ≤ C) : Integrable fun y => h y • g y := by
  refine Integrable.mono' ((hH.integrable hr).mul_const C)
    ((hH.meas.aestronglyMeasurable).smul hg) (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ K
  · rw [norm_smul, Real.norm_of_nonneg (hH.nonneg hr y), mul_comm]
    exact mul_le_mul_of_nonneg_right (hb y hy) (hH.nonneg hr y) |>.trans_eq (mul_comm _ _)
  · simp [hH.zero y hy]

/-- The mean `m_h = ∫ y h(y) dy` lies within `R` of every point of `K`. -/
lemma InH.norm_sub_mean_le (hH : InH A r R K h) (hr : 0 ≤ r) {y : E} (hy : y ∈ K) :
    ‖y - Large.meanD h‖ ≤ R := by
  obtain ⟨b, -, hKb⟩ := hH.subset_ball hr
  have hint : Integrable fun z => h z • z :=
    hH.integrable_smul hr continuous_id.aestronglyMeasurable (C := ‖b‖ + R) fun z hz => by
      have := hKb hz; rw [Metric.mem_closedBall, dist_eq_norm] at this
      calc ‖z‖ = ‖(z - b) + b‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - b‖ + ‖b‖ := norm_add_le _ _
        _ ≤ ‖b‖ + R := by linarith
  have hy' : y - Large.meanD h = ∫ z, h z • (y - z) := by
    rw [Large.meanD]
    simp_rw [smul_sub]
    rw [integral_sub ((hH.integrable hr).smul_const y) hint, integral_smul_const, hH.int,
      one_smul]
  rw [hy']
  calc ‖∫ z, h z • (y - z)‖ ≤ ∫ z, h z * R := by
        refine norm_integral_le_of_norm_le ((hH.integrable hr).mul_const R)
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ K
        · rw [norm_smul, Real.norm_of_nonneg (hH.nonneg hr z), ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left (hH.diam y hy z hz) (hH.nonneg hr z)
        · simp [hH.zero z hz]
    _ = R := by rw [integral_mul_const, hH.int, one_mul]

lemma InH.integrable_id (hH : InH A r R K h) (hr : 0 ≤ r) : Integrable fun y => h y • y := by
  obtain ⟨b, -, hKb⟩ := hH.subset_ball hr
  exact hH.integrable_smul hr continuous_id.aestronglyMeasurable (C := ‖b‖ + R) fun z hz => by
    have := hKb hz; rw [Metric.mem_closedBall, dist_eq_norm] at this
    calc ‖z‖ = ‖(z - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - b‖ + ‖b‖ := norm_add_le _ _
      _ ≤ ‖b‖ + R := by linarith

lemma InH.integral_smul_sub_mean (hH : InH A r R K h) (hr : 0 ≤ r) :
    ∫ y, h y • (y - Large.meanD h) = 0 := by
  simp_rw [smul_sub]
  rw [integral_sub (hH.integrable_id hr) ((hH.integrable hr).smul_const _), integral_smul_const,
    hH.int, one_smul, Large.meanD, sub_self]

lemma InH.integral_inner_sub_mean (hH : InH A r R K h) (hr : 0 ≤ r) (ξ : E) :
    ∫ y, h y * ⟪y - Large.meanD h, ξ⟫ = 0 := by
  have h1 : (fun y => h y * ⟪y - Large.meanD h, ξ⟫) =
      fun y => ⟪ξ, h y • (y - Large.meanD h)⟫ := by
    funext y; rw [inner_smul_right, real_inner_comm]
  have hint : Integrable fun y => h y • (y - Large.meanD h) :=
    ((hH.integrable_id hr).sub ((hH.integrable hr).smul_const (Large.meanD h))).congr
      (Eventually.of_forall fun y => by simp [smul_sub])
  rw [h1, integral_inner hint, hH.integral_smul_sub_mean hr, inner_zero_right]

lemma InH.abs_inner_le (hH : InH A r R K h) (hr : 0 ≤ r) {y : E} (hy : y ∈ K) (ξ : E) :
    |⟪y - Large.meanD h, ξ⟫| ≤ R * ‖ξ‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hH.norm_sub_mean_le hr hy) (norm_nonneg _))

end ClassH

section CharFun

/-- The centred characteristic function `c_h(ξ) = ∫ h(y) e^{-2πi⟨y - m_h, ξ⟩} dy`. -/
def cf (h : E → ℝ) (ξ : E) : ℂ :=
  ∫ y, (h y : ℂ) * Complex.exp (-((2 * π * ⟪y - Large.meanD h, ξ⟫ : ℝ) : ℂ) * Complex.I)

/-- The variance form `Σ_h(ξ) = ∫ h(y) ⟨y - m_h, ξ⟩² dy`. -/
def varF (h : E → ℝ) (ξ : E) : ℝ := ∫ y, h y * ⟪y - Large.meanD h, ξ⟫ ^ 2

variable {A r R : ℝ} {K : Set E} {h : E → ℝ}

lemma InH.integrable_sq (hH : InH A r R K h) (hr : 0 ≤ r) (ξ : E) :
    Integrable fun y => h y * ⟪y - Large.meanD h, ξ⟫ ^ 2 :=
  hH.integrable_smul hr (g := fun y => ⟪y - Large.meanD h, ξ⟫ ^ 2)
    ((by fun_prop : Continuous fun y => ⟪y - Large.meanD h, ξ⟫ ^ 2).aestronglyMeasurable)
    (C := (R * ‖ξ‖) ^ 2) (fun y hy => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hH.abs_inner_le hr hy ξ) 2)

lemma InH.varF_le (hH : InH A r R K h) (hr : 0 ≤ r) (ξ : E) :
    varF h ξ ≤ R ^ 2 * ‖ξ‖ ^ 2 := by
  calc varF h ξ ≤ ∫ y, h y * (R * ‖ξ‖) ^ 2 := by
        refine integral_mono (hH.integrable_sq hr ξ) ((hH.integrable hr).mul_const _) fun y => ?_
        by_cases hy : y ∈ K
        · refine mul_le_mul_of_nonneg_left ?_ (hH.nonneg hr y)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hH.abs_inner_le hr hy ξ) 2
        · simp [hH.zero y hy]
    _ = R ^ 2 * ‖ξ‖ ^ 2 := by rw [integral_mul_const, hH.int]; ring

lemma InH.varF_nonneg (hH : InH A r R K h) (hr : 0 ≤ r) (ξ : E) : 0 ≤ varF h ξ :=
  integral_nonneg fun y => mul_nonneg (hH.nonneg hr y) (sq_nonneg _)

/-- **Taylor bound**: `|c_h(ξ) - (1 - 2π² Σ_h(ξ))| ≤ (2πR|ξ|)³` for `2πR|ξ| ≤ 1`. -/
lemma InH.cf_taylor (hH : InH A r R K h) (hr : 0 ≤ r) {ξ : E} (hξ : 2 * π * R * ‖ξ‖ ≤ 1) :
    ‖cf h ξ - (1 - (2 * π ^ 2 * varF h ξ : ℝ))‖ ≤ (2 * π * R * ‖ξ‖) ^ 3 := by
  obtain ⟨θ, hθ⟩ : ∃ θ : E → ℝ, θ = fun y => 2 * π * ⟪y - Large.meanD h, ξ⟫ := ⟨_, rfl⟩
  have hθK : ∀ y ∈ K, |θ y| ≤ 2 * π * R * ‖ξ‖ := fun y hy => by
    simp only [hθ, abs_mul, abs_of_pos two_pi_pos]
    calc 2 * π * |⟪y - Large.meanD h, ξ⟫| ≤ 2 * π * (R * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left (hH.abs_inner_le hr hy ξ) two_pi_pos.le
      _ = _ := by ring
  have hθc : Continuous θ := by rw [hθ]; fun_prop
  obtain ⟨T, hTd⟩ : ∃ T : E → ℂ, T = fun y => 1 - (θ y : ℂ) * Complex.I - (θ y : ℂ) ^ 2 / 2 :=
    ⟨_, rfl⟩
  have hT : Continuous T := by rw [hTd]; fun_prop
  obtain ⟨X, hXd⟩ : ∃ X : E → ℂ, X = fun y => Complex.exp (-(θ y : ℂ) * Complex.I) := ⟨_, rfl⟩
  have hX : Continuous X := by rw [hXd]; fun_prop
  -- integrability
  have iX : Integrable fun y => h y • X y :=
    hH.integrable_smul hr (g := X) hX.aestronglyMeasurable (C := 1) fun y _ => by
      simp [hXd, Complex.norm_exp]
  have iT : Integrable fun y => h y • T y :=
    hH.integrable_smul hr (g := T) hT.aestronglyMeasurable (C := 3) fun y hy => by
      rw [hTd]; exact norm_taylor_poly_le ((hθK y hy).trans hξ)
  -- the integral of `h T`
  have hIT : ∫ y, h y • T y = 1 - ((2 * π ^ 2 * varF h ξ : ℝ) : ℂ) := by
    have hT' : (fun y => h y • T y) =
        fun y => ((h y - 2 * π ^ 2 * (h y * ⟪y - Large.meanD h, ξ⟫ ^ 2) : ℝ) : ℂ)
        - ((2 * π * (h y * ⟪y - Large.meanD h, ξ⟫) : ℝ) : ℂ) * Complex.I := by
      funext y; simp only [hTd, hθ, Complex.real_smul]; push_cast; ring
    rw [hT', integral_sub, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub (hH.integrable hr) ((hH.integrable_sq hr ξ).const_mul _), integral_const_mul,
      integral_const_mul, hH.integral_inner_sub_mean hr, hH.int, varF]
    · simp
    · exact ((hH.integrable hr).sub ((hH.integrable_sq hr ξ).const_mul _)).ofReal
    · refine (Integrable.ofReal ?_).mul_const _
      exact (hH.integrable_smul hr (g := fun y => ⟪y - Large.meanD h, ξ⟫)
        ((by fun_prop : Continuous fun y => ⟪y - Large.meanD h, ξ⟫).aestronglyMeasurable)
        (C := R * ‖ξ‖) (fun y hy => by
          rw [Real.norm_eq_abs]; exact hH.abs_inner_le hr hy ξ)).const_mul _
  have hcf : cf h ξ = ∫ y, h y • X y := by
    simp only [cf, hXd, hθ, Complex.real_smul]
  rw [hcf, ← hIT, ← integral_sub iX iT]
  calc ‖∫ y, (h y • X y - h y • T y)‖ ≤ ∫ y, h y * (2 * π * R * ‖ξ‖) ^ 3 := by
        refine norm_integral_le_of_norm_le ((hH.integrable hr).mul_const _)
          (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ K
        · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hH.nonneg hr y)]
          refine mul_le_mul_of_nonneg_left ?_ (hH.nonneg hr y)
          have h1 := hθK y hy
          rw [hXd, hTd]
          refine (norm_cexp_taylor (h1.trans hξ)).trans ?_
          exact pow_le_pow_left₀ (abs_nonneg _) h1 3
        · simp [hH.zero y hy]
    _ = (2 * π * R * ‖ξ‖) ^ 3 := by rw [integral_mul_const, hH.int, one_mul]

/-- The volume of a closed ball of radius `ρ` (any centre). -/
def vB (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ρ : ℝ) : ℝ :=
  volume.real (Metric.closedBall (0 : E) ρ)

lemma vB_center (x : E) (ρ : ℝ) : volume.real (Metric.closedBall x ρ) = vB E ρ :=
  Measure.addHaar_real_closedBall_center volume x ρ

lemma vB_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < vB E ρ := by
  rw [vB, measureReal_def]
  exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume 0 hρ).ne'
    measure_closedBall_lt_top.ne

lemma InH.vol_le (hH : InH A r R K h) (hr : 0 ≤ r) : volume.real K ≤ vB E R := by
  obtain ⟨b, -, hKb⟩ := hH.subset_ball hr
  rw [← vB_center b]
  exact measureReal_mono hKb measure_closedBall_lt_top.ne

lemma InH.vol_ge (hH : InH A r R K h) : vB E r ≤ volume.real K := by
  obtain ⟨b, hb⟩ := hH.ball
  rw [← vB_center b]
  exact measureReal_mono hb hH.compact.measure_lt_top.ne

/-- The constant `σ` of the covariance bound (Lemma 112), with our elementary argument:
`σ = e^{-A} (r/4)² |B_{r/4}| / |B_R|` (the paper has `e^{-A} (r/R)^d r² / (d+2)`). -/
def sig (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (A r R : ℝ) : ℝ :=
  exp (-A) * (r / 4) ^ 2 * vB E (r / 4) / vB E R

lemma sig_pos {A r R : ℝ} (hr : 0 < r) (hR : 0 < R) : 0 < sig E A r R := by
  unfold sig
  have := vB_pos (E := E) (by positivity : 0 < r / 4)
  have := vB_pos (E := E) hR
  positivity

/-- **Covariance bound** (Lemma 112): `σ |ξ|² ≤ Σ_h(ξ)`. -/
lemma InH.varF_ge (hH : InH A r R K h) (hr : 0 < r) (ξ : E) :
    sig E A r R * ‖ξ‖ ^ 2 ≤ varF h ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hH.varF_nonneg hr.le]
  obtain ⟨b, hb, hKb⟩ := hH.subset_ball hr.le
  have hR : 0 < R := by
    have hbK : b ∈ K := hb (Metric.mem_closedBall_self hr.le)
    have hy : b + r • ‖ξ‖⁻¹ • ξ ∈ K := hb (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul,
        norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ), mul_one,
        Real.norm_of_nonneg hr.le])
    have := hH.diam _ hy b hbK
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ), mul_one, Real.norm_of_nonneg hr.le] at this
    linarith
  set m := Large.meanD h
  set t := ⟪b - m, ξ⟫
  obtain ⟨s, hs2, hst⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ 0 ≤ s * t := by
    rcases le_total 0 t with ht | ht
    · exact ⟨1, by norm_num, by linarith⟩
    · exact ⟨-1, by norm_num, by linarith⟩
  have hs : |s| = 1 := by
    have : |s| ^ 2 = 1 := by rw [sq_abs, hs2]
    nlinarith [abs_nonneg s]
  have hnξ : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set e : E := ‖ξ‖⁻¹ • ξ
  have hen : ‖e‖ = 1 := by
    simp only [e, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnξ.ne']
  have heξ : ⟪e, ξ⟫ = ‖ξ‖ := by
    simp only [e, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]; field_simp
  set c : E := b + (s * (r / 2)) • e
  have hcB : Metric.closedBall c (r / 4) ⊆ K := by
    intro y hy
    apply hb
    rw [Metric.mem_closedBall] at hy ⊢
    calc dist y b ≤ dist y c + dist c b := dist_triangle _ _ _
      _ ≤ r / 4 + r / 2 := by
        gcongr
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hen, mul_one, Real.norm_eq_abs,
          abs_mul, hs, one_mul, abs_of_pos (by positivity : 0 < r / 2)]
      _ ≤ r := by linarith
  have hsq : ∀ y ∈ Metric.closedBall c (r / 4), (r / 4) ^ 2 * ‖ξ‖ ^ 2 ≤ ⟪y - m, ξ⟫ ^ 2 := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 : ⟪y - m, ξ⟫ = ⟪y - c, ξ⟫ + s * (r / 2) * ‖ξ‖ + t := by
      have : y - m = (y - c) + (s * (r / 2)) • e + (b - m) := by simp only [c]; abel
      rw [this, inner_add_left, inner_add_left, inner_smul_left, heξ]
      simp [t]
    have h2 : |⟪y - c, ξ⟫| ≤ r / 4 * ‖ξ‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hy hnξ.le)
    have h3 : r / 4 * ‖ξ‖ ≤ s * ⟪y - m, ξ⟫ := by
      rw [h1, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← sq, hs2, one_mul]
      have : -(r / 4 * ‖ξ‖) ≤ s * ⟪y - c, ξ⟫ := by
        have := neg_abs_le (s * ⟪y - c, ξ⟫)
        rw [abs_mul, hs, one_mul] at this
        linarith
      linarith
    have h4 : (s * ⟪y - m, ξ⟫) ^ 2 = ⟪y - m, ξ⟫ ^ 2 := by rw [mul_pow, hs2, one_mul]
    rw [← h4, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h3 2
  have hKpos := hH.volPos hr.le
  have hlow : ∀ y ∈ Metric.closedBall c (r / 4),
      exp (-A) / vB E R * ((r / 4) ^ 2 * ‖ξ‖ ^ 2) ≤ h y * ⟪y - m, ξ⟫ ^ 2 := by
    intro y hy
    have hyK := hcB hy
    have h1 : exp (-A) / vB E R ≤ h y := by
      rw [div_le_iff₀ (vB_pos hR)]
      calc exp (-A) ≤ volume.real K * h y := hH.low y hyK
        _ ≤ vB E R * h y := mul_le_mul_of_nonneg_right (hH.vol_le hr.le) (hH.nonneg hr.le y)
        _ = h y * vB E R := mul_comm _ _
    exact mul_le_mul h1 (hsq y hy) (by positivity) (hH.nonneg hr.le y)
  calc sig E A r R * ‖ξ‖ ^ 2
      = exp (-A) / vB E R * ((r / 4) ^ 2 * ‖ξ‖ ^ 2) *
          volume.real (Metric.closedBall c (r / 4)) := by
        rw [vB_center, sig]; field_simp
    _ ≤ ∫ y in Metric.closedBall c (r / 4), h y * ⟪y - m, ξ⟫ ^ 2 :=
        setIntegral_ge_of_const_le_real measurableSet_closedBall measure_closedBall_lt_top.ne
          hlow (hH.integrable_sq hr.le ξ).integrableOn
    _ ≤ varF h ξ :=
        setIntegral_le_integral (hH.integrable_sq hr.le ξ)
          (Eventually.of_forall fun y => mul_nonneg (hH.nonneg hr.le y) (sq_nonneg _))

end CharFun

section Gap

/-- The character `e^{-2πi⟨y, ξ⟩}`. -/
def ex (y ξ : E) : ℂ := Complex.exp (-((2 * π * ⟪y, ξ⟫ : ℝ) : ℂ) * Complex.I)

lemma norm_ex (y ξ : E) : ‖ex y ξ‖ = 1 := by
  rw [ex, Complex.norm_exp]; simp

lemma continuous_ex : Continuous fun p : E × E => ex p.1 p.2 := by
  unfold ex; fun_prop

lemma ex_zero_left (ξ : E) : ex 0 ξ = 1 := by simp [ex]

lemma eq_one_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) (hre : 1 ≤ z.re) : z = 1 := by
  have h1 : z.re ≤ 1 := hz ▸ Complex.re_le_norm z
  have hre1 : z.re = 1 := le_antisymm h1 hre
  have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h3 := Complex.normSq_apply z
    have h4 := Complex.sq_norm z
    rw [hz] at h4
    nlinarith
  have him : z.im = 0 := by nlinarith
  exact Complex.ext hre1 him

/-- `|∫_{B_r} e^{-2πi⟨y, ξ⟩} dy| < |B_r|` for `ξ ≠ 0`. -/
lemma norm_ballInt_lt {r : ℝ} (hr : 0 < r) {ξ : E} (hξ : ξ ≠ 0) :
    ‖∫ y in Metric.closedBall (0 : E) r, ex y ξ‖ < vB E r := by
  set B := Metric.closedBall (0 : E) r
  set F := ∫ y in B, ex y ξ
  have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hexc : Continuous fun y => ex y ξ := by unfold ex; fun_prop
  have iex : IntegrableOn (fun y => ex y ξ) B :=
    hexc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  rcases eq_or_ne F 0 with hF | hF
  · rw [hF, norm_zero]; exact vB_pos hr
  set w : ℂ := starRingEnd ℂ F / (‖F‖ : ℂ)
  have hFn : (‖F‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hF)
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self (norm_ne_zero_iff.2 hF)
  have hwF : w * F = ‖F‖ := by
    simp only [w]
    rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hFn]; ring
  set g : E → ℝ := fun y => 1 - (w * ex y ξ).re
  have hgc : Continuous g := by
    simp only [g]; fun_prop
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    simp only [g, sub_nonneg]
    calc (w * ex y ξ).re ≤ ‖w * ex y ξ‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, hw, norm_ex, one_mul]
  have hnorm : ∀ y, ‖w * ex y ξ‖ = 1 := fun y => by rw [norm_mul, hw, norm_ex, one_mul]
  -- a point of the open ball where `g > 0`
  have hnξ : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨y0, hy0, hgy0⟩ : ∃ y0 ∈ Metric.ball (0 : E) r, 0 < g y0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ y ∈ Metric.ball (0 : E) r, w * ex y ξ = 1 := fun y hy =>
      eq_one_of_norm_one (hnorm y) (by have := hcon y hy; simp only [g] at this; linarith)
    have hw1 : w = 1 := by
      have := hz 0 (Metric.mem_ball_self hr); rwa [ex_zero_left, mul_one] at this
    set s : ℝ := min (r / (2 * ‖ξ‖)) (1 / (2 * ‖ξ‖ ^ 2))
    have hs0 : 0 < s := by positivity
    have hs1 : s * ‖ξ‖ < r := by
      have : s ≤ r / (2 * ‖ξ‖) := min_le_left _ _
      calc s * ‖ξ‖ ≤ r / (2 * ‖ξ‖) * ‖ξ‖ := mul_le_mul_of_nonneg_right this hnξ.le
        _ = r / 2 := by field_simp
        _ < r := by linarith
    have hs2 : s * ‖ξ‖ ^ 2 < 1 := by
      have : s ≤ 1 / (2 * ‖ξ‖ ^ 2) := min_le_right _ _
      calc s * ‖ξ‖ ^ 2 ≤ 1 / (2 * ‖ξ‖ ^ 2) * ‖ξ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 1 / 2 := by field_simp
        _ < 1 := by norm_num
    have hy1 : s • ξ ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs0.le]; exact hs1
    have h1 := hz _ hy1
    rw [hw1, one_mul, ex, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have h2 : (-(2 * π * (s * ‖ξ‖ ^ 2)) : ℝ) = (n : ℝ) * (2 * π) := by
      have := congrArg Complex.im hn
      simp only [inner_smul_left, real_inner_self_eq_norm_sq, conj_trivial] at this
      simp at this
      rw [show ((‖ξ‖ : ℂ) ^ 2).re = ‖ξ‖ ^ 2 by norm_cast] at this
      exact this
    have h3 : -(s * ‖ξ‖ ^ 2) = (n : ℝ) := by
      have hπ : (2 * π) ≠ 0 := by positivity
      field_simp at h2; nlinarith [pi_pos]
    have h4 : (n : ℝ) < 0 := by have : 0 < s * ‖ξ‖ ^ 2 := by positivity
                                linarith
    have h5 : (-1 : ℝ) < n := by linarith
    have h6 : n < 0 := by exact_mod_cast h4
    have h7 : -1 < n := by exact_mod_cast h5
    omega
  -- `g ≥ g y0 / 2` on a small ball around `y0`
  obtain ⟨δ, hδ, hδg⟩ : ∃ δ > 0, ∀ y ∈ Metric.closedBall y0 δ, g y0 / 2 ≤ g y ∧ y ∈ B := by
    have hU : ∀ᶠ y in 𝓝 y0, g y0 / 2 < g y ∧ y ∈ Metric.ball (0 : E) r :=
      (hgc.continuousAt.eventually (lt_mem_nhds (by linarith))).and
        (Metric.isOpen_ball.mem_nhds hy0)
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    have := hεU (Metric.closedBall_subset_ball (by linarith) hy)
    exact ⟨this.1.le, Metric.ball_subset_closedBall this.2⟩
  have igB : IntegrableOn g B := hgc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hpos : 0 < ∫ y in B, g y := by
    have hsub : Metric.closedBall y0 δ ⊆ B := fun y hy => (hδg y hy).2
    calc (0 : ℝ) < g y0 / 2 * volume.real (Metric.closedBall y0 δ) := by
          have := vB_pos (E := E) hδ; rw [vB_center]; positivity
      _ ≤ ∫ y in Metric.closedBall y0 δ, g y :=
          setIntegral_ge_of_const_le_real measurableSet_closedBall measure_closedBall_lt_top.ne
            (fun y hy => (hδg y hy).1) (igB.mono_set hsub)
      _ ≤ ∫ y in B, g y :=
          setIntegral_mono_set igB (Eventually.of_forall hg0) (Eventually.of_forall hsub)
  have hint : ∫ y in B, g y = vB E r - ‖F‖ := by
    have h1 : ∫ y in B, g y = (∫ y in B, (1 : ℝ)) - ∫ y in B, (w * ex y ξ).re := by
      rw [← integral_sub (integrableOn_const hBfin)]
      exact (iex.const_mul w).re
    have h2 : ∫ y in B, (w * ex y ξ).re = ‖F‖ := by
      have h3 := integral_re (iex.const_mul w)
      simp only [RCLike.re_to_complex] at h3
      rw [h3, integral_const_mul, hwF, Complex.ofReal_re]
    rw [h1, h2, setIntegral_const, smul_eq_mul, mul_one, vB]
  linarith

lemma ex_add (y z ξ : E) : ex (y + z) ξ = ex y ξ * ex z ξ := by
  simp only [ex, inner_add_left, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `∫_{B_r} e^{-2πi⟨y, ξ⟩} dy`. -/
def ballInt (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (r : ℝ) (ξ : E) : ℂ :=
  ∫ y in Metric.closedBall (0 : E) r, ex y ξ

lemma continuous_ballInt (r : ℝ) : Continuous (ballInt E r) := by
  have : Continuous (Function.uncurry fun (ξ y : E) => ex y ξ) := by
    simp only [Function.uncurry_def]; unfold ex; fun_prop
  exact continuous_parametric_integral_of_continuous this (isCompact_closedBall 0 r)

lemma tendsto_ballInt (r : ℝ) : Tendsto (ballInt E r) (cocompact E) (𝓝 0) := by
  have h := tendsto_integral_exp_inner_smul_cocompact
    ((Metric.closedBall (0 : E) r).indicator fun _ => (1 : ℂ))
  refine h.congr fun ξ => ?_
  rw [ballInt, ← integral_indicator measurableSet_closedBall]
  congr 1; funext y
  by_cases hy : y ∈ Metric.closedBall (0 : E) r
  · simp only [Set.indicator_of_mem hy, Circle.smul_def, Real.fourierChar_apply, ex, smul_eq_mul,
      mul_one]
    congr 1; push_cast; ring
  · simp [Set.indicator_of_notMem hy]

/-- **Fourier gap for the ball**: for `r, r₀ > 0` there is `q < 1` with
`|∫_{B_r} e^{-2πi⟨y, ξ⟩} dy| ≤ q |B_r|` for `|ξ| ≥ r₀`. -/
lemma ballInt_gap {r r₀ : ℝ} (hr : 0 < r) (hr₀ : 0 < r₀) :
    ∃ q < 1, ∀ ξ : E, r₀ ≤ ‖ξ‖ → ‖ballInt E r ξ‖ ≤ q * vB E r := by
  have hV := vB_pos (E := E) hr
  have hev : ∀ᶠ ξ in cocompact E, ‖ballInt E r ξ‖ < vB E r / 2 :=
    (tendsto_ballInt r).norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))
  obtain ⟨t, ht, htc⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨M, hM⟩ := ht.isBounded.subset_closedBall 0
  have hout : ∀ ξ : E, M < ‖ξ‖ → ‖ballInt E r ξ‖ ≤ 1 / 2 * vB E r := fun ξ hξ => by
    have : ξ ∈ tᶜ := fun hξt => by
      have := hM hξt; rw [Metric.mem_closedBall, dist_zero_right] at this; linarith
    have := htc this; simp only [Set.mem_ofPred_eq] at this; linarith
  set S := Metric.closedBall (0 : E) M ∩ {ξ | r₀ ≤ ‖ξ‖}
  have hSc : IsCompact S :=
    (isCompact_closedBall 0 M).inter_right (isClosed_le continuous_const continuous_norm)
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1 / 2, by norm_num, fun ξ hξ => hout ξ ?_⟩
    by_contra hcon
    have : ξ ∈ S := ⟨by rw [Metric.mem_closedBall, dist_zero_right]; linarith, hξ⟩
    rw [hS] at this; exact this
  obtain ⟨ξ1, hξ1S, hmax⟩ :=
    hSc.exists_isMaxOn hS (continuous_ballInt r).norm.continuousOn
  have hξ1 : ξ1 ≠ 0 := fun h0 => by
    have := hξ1S.2; simp only [Set.mem_ofPred_eq, h0, norm_zero] at this; linarith
  have hlt := norm_ballInt_lt (E := E) hr hξ1
  refine ⟨max (1 / 2) (‖ballInt E r ξ1‖ / vB E r), max_lt (by norm_num)
    ((div_lt_one hV).2 hlt), fun ξ hξ => ?_⟩
  rcases le_or_gt ‖ξ‖ M with hξM | hξM
  · have hξS : ξ ∈ S := ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hξM, hξ⟩
    calc ‖ballInt E r ξ‖ ≤ ‖ballInt E r ξ1‖ := hmax hξS
      _ = ‖ballInt E r ξ1‖ / vB E r * vB E r := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hV.le
  · exact (hout ξ hξM).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hV.le)

lemma setIntegral_ball_ex (b : E) (r : ℝ) (ξ : E) :
    ∫ y in Metric.closedBall b r, ex y ξ = ex b ξ * ballInt E r ξ := by
  rw [ballInt, ← integral_const_mul, ← integral_indicator measurableSet_closedBall,
    ← integral_indicator measurableSet_closedBall]
  rw [← integral_add_left_eq_self _ b]
  congr 1; funext z
  by_cases hz : z ∈ Metric.closedBall (0 : E) r
  · have hz' : b + z ∈ Metric.closedBall b r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz, ex_add]
  · have hz' : b + z ∉ Metric.closedBall b r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]

end Gap

section FT

/-- The Fourier transform `ĥ(ξ) = ∫ h(y) e^{-2πi⟨y, ξ⟩} dy` of a real function. -/
def ft (h : E → ℝ) (ξ : E) : ℂ := ∫ y, (h y : ℂ) * ex y ξ

lemma ft_eq_fourier (h : E → ℝ) (ξ : E) : ft h ξ = 𝓕 (fun y => (h y : ℂ)) ξ := by
  rw [ft, Real.fourier_eq]
  congr 1; funext y
  rw [Circle.smul_def, Real.fourierChar_apply, ex, smul_eq_mul, mul_comm]
  congr 2; push_cast; ring

variable {A r R : ℝ} {K : Set E} {h : E → ℝ}

lemma norm_cf_eq (h : E → ℝ) (ξ : E) : ‖cf h ξ‖ = ‖ft h ξ‖ := by
  have : cf h ξ = ex (-Large.meanD h) ξ * ft h ξ := by
    rw [cf, ft, ← integral_const_mul]
    congr 1; funext y
    rw [show -((2 * π * ⟪y - Large.meanD h, ξ⟫ : ℝ) : ℂ) * Complex.I
      = -((2 * π * ⟪y + -Large.meanD h, ξ⟫ : ℝ) : ℂ) * Complex.I by rw [sub_eq_add_neg],
      ← ex, ex_add]
    ring
  rw [this, norm_mul, norm_ex, one_mul]

lemma norm_ft_le_one (hH : InH A r R K h) (hr : 0 ≤ r) (ξ : E) : ‖ft h ξ‖ ≤ 1 := by
  calc ‖ft h ξ‖ ≤ ∫ y, h y := by
        refine norm_integral_le_of_norm_le (hH.integrable hr) (Eventually.of_forall fun y => ?_)
        rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_of_nonneg (hH.nonneg hr y)]
    _ = 1 := hH.int

/-- The mixing weight `α = e^{-A} |B_r| / |B_R|` of the ball component. -/
def alph (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (A r R : ℝ) : ℝ :=
  exp (-A) * vB E r / vB E R

/-- **Fourier bound from the ball component**: `|ĥ(ξ)| ≤ 1 - α + α |û_{B_r}(ξ)|`. -/
lemma InH.norm_ft_le (hH : InH A r R K h) (hr : 0 < r) (ξ : E) :
    ‖ft h ξ‖ ≤ 1 - alph E A r R + alph E A r R * (‖ballInt E r ξ‖ / vB E r) := by
  obtain ⟨b, hb, hKb⟩ := hH.subset_ball hr.le
  have hR : 0 < vB E R := lt_of_lt_of_le (hH.volPos hr.le) (hH.vol_le hr.le)
  have hVr := vB_pos (E := E) hr
  obtain ⟨a, had⟩ : ∃ a, a = exp (-A) / vB E R := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [had]; positivity
  obtain ⟨B, hBd⟩ : ∃ B, B = Metric.closedBall b r := ⟨_, rfl⟩
  have hBm : MeasurableSet B := hBd ▸ measurableSet_closedBall
  have hBf : volume B ≠ ⊤ := hBd ▸ measure_closedBall_lt_top.ne
  rw [← hBd] at hb
  obtain ⟨k, hkd⟩ : ∃ k : E → ℝ, k = fun y => h y - B.indicator (fun _ => a) y := ⟨_, rfl⟩
  have hk0 : ∀ y, 0 ≤ k y := fun y => by
    simp only [hkd]
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, sub_nonneg]
      have h1 := hH.low y (hb hy)
      rw [had, div_le_iff₀ hR]
      calc exp (-A) ≤ volume.real K * h y := h1
        _ ≤ vB E R * h y := mul_le_mul_of_nonneg_right (hH.vol_le hr.le) (hH.nonneg hr.le y)
        _ = h y * vB E R := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, sub_zero]; exact hH.nonneg hr.le y
  have iI : Integrable (B.indicator fun _ => a) :=
    (integrableOn_const hBf).integrable_indicator hBm
  have ik : Integrable k := hkd ▸ (hH.integrable hr.le).sub iI
  have hIk : ∫ y, k y = 1 - alph E A r R := by
    rw [hkd, integral_sub (hH.integrable hr.le) iI, hH.int, integral_indicator hBm,
      setIntegral_const, smul_eq_mul, hBd, vB_center, alph, had]
    ring
  have iex : Integrable fun y => ((k y : ℝ) : ℂ) * ex y ξ := by
    have i1 : Integrable fun y => ((k y : ℝ) : ℂ) := ik.ofReal (𝕜 := ℂ)
    refine Integrable.mono' i1.norm ?_
      (Eventually.of_forall fun y => by rw [norm_mul, norm_ex, mul_one])
    have : Continuous fun y => ex y ξ := by unfold ex; fun_prop
    exact i1.aestronglyMeasurable.mul this.aestronglyMeasurable
  have iB : Integrable fun y => ((B.indicator (fun _ => a) y : ℝ) : ℂ) * ex y ξ := by
    have i1 : Integrable fun y => ((B.indicator (fun _ => a) y : ℝ) : ℂ) := iI.ofReal (𝕜 := ℂ)
    refine Integrable.mono' i1.norm ?_
      (Eventually.of_forall fun y => by rw [norm_mul, norm_ex, mul_one])
    have : Continuous fun y => ex y ξ := by unfold ex; fun_prop
    exact i1.aestronglyMeasurable.mul this.aestronglyMeasurable
  have hsplit : ft h ξ = (∫ y, ((k y : ℝ) : ℂ) * ex y ξ) + a * (ex b ξ * ballInt E r ξ) := by
    rw [← setIntegral_ball_ex, ← hBd, ← integral_const_mul, ← integral_indicator hBm,
      ← integral_add iex]
    · rw [ft]; congr 1; funext y
      simp only [hkd]
      by_cases hy : y ∈ B
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; push_cast; ring
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; push_cast; ring
    · refine (iB.congr (Eventually.of_forall fun y => ?_))
      dsimp only
      by_cases hy : y ∈ B
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp
  rw [hsplit]
  calc ‖(∫ y, ((k y : ℝ) : ℂ) * ex y ξ) + a * (ex b ξ * ballInt E r ξ)‖
      ≤ ‖∫ y, ((k y : ℝ) : ℂ) * ex y ξ‖ + ‖a * (ex b ξ * ballInt E r ξ)‖ := norm_add_le _ _
    _ ≤ (∫ y, k y) + a * ‖ballInt E r ξ‖ := by
        gcongr
        · refine norm_integral_le_of_norm_le ik (Eventually.of_forall fun y => ?_)
          rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_of_nonneg (hk0 y)]
        · rw [norm_mul, norm_mul, norm_ex, one_mul, Complex.norm_real,
            Real.norm_of_nonneg ha0]
    _ = 1 - alph E A r R + alph E A r R * (‖ballInt E r ξ‖ / vB E r) := by
        rw [hIk, alph, had]; field_simp

lemma continuous_ex_left (ξ : E) : Continuous fun y : E => ex y ξ := by unfold ex; fun_prop

lemma continuous_ex_right (y : E) : Continuous fun ξ : E => ex y ξ := by unfold ex; fun_prop

lemma ex_neg (y ξ : E) : ex (-y) ξ = starRingEnd ℂ (ex y ξ) := by
  simp only [ex, inner_neg_left, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1; push_cast; ring

/-- `ĥ` is continuous for an integrable `h`. -/
lemma continuous_ft {h : E → ℝ} (hi : Integrable h) : Continuous (ft h) := by
  refine continuous_of_dominated (bound := fun y => ‖h y‖) (fun ξ => ?_) (fun ξ => ?_) hi.norm
    (Eventually.of_forall fun y => ?_)
  · exact (hi.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
      (continuous_ex_left ξ).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by rw [norm_mul, norm_ex, mul_one, Complex.norm_real]
  · exact continuous_const.mul (continuous_ex_right y)

lemma integrable_ft_mul {h : E → ℝ} (hi : Integrable h) (ξ : E) :
    Integrable fun y => (h y : ℂ) * ex y ξ := by
  refine Integrable.mono' (hi.ofReal (𝕜 := ℂ)).norm ?_
    (Eventually.of_forall fun y => by rw [norm_mul, norm_ex, mul_one]; rfl)
  exact (hi.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul (continuous_ex_left ξ).aestronglyMeasurable

end FT

section Gauss

/-- The Gaussian weight `e^{-ε|ξ|²}`. -/
def gw (ε : ℝ) (ξ : E) : ℝ := exp (-ε * ‖ξ‖ ^ 2)

/-- Its Fourier transform `(π/ε)^{d/2} e^{-π²|z|²/ε}`. -/
def gK (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ε : ℝ) (z : E) : ℝ :=
  (π / ε) ^ ((Module.finrank ℝ E : ℝ) / 2) * exp (-π ^ 2 * ‖z‖ ^ 2 / ε)

lemma integrable_gw {ε : ℝ} (hε : 0 < ε) : Integrable (gw (E := E) ε) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (ε : ℂ))
    (by simpa using hε) 0 0).norm
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp, gw]
  congr 1; simp [← Complex.ofReal_pow]

lemma continuous_gw (ε : ℝ) : Continuous (gw (E := E) ε) := by unfold gw; fun_prop

lemma gw_pos (ε : ℝ) (ξ : E) : 0 < gw ε ξ := exp_pos _

lemma gw_le_one {ε : ℝ} (hε : 0 ≤ ε) (ξ : E) : gw ε ξ ≤ 1 := by
  rw [gw, exp_le_one_iff]; nlinarith [sq_nonneg ‖ξ‖]

lemma gK_nonneg {ε : ℝ} (hε : 0 < ε) (z : E) : 0 ≤ gK E ε z := by
  unfold gK; positivity

lemma gK_le {ε : ℝ} (hε : 0 < ε) (z : E) :
    gK E ε z ≤ (π / ε) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  unfold gK
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [exp_le_one_iff]
  have : 0 ≤ π ^ 2 * ‖z‖ ^ 2 / ε := by positivity
  linarith [show -π ^ 2 * ‖z‖ ^ 2 / ε = -(π ^ 2 * ‖z‖ ^ 2 / ε) by ring]

lemma continuous_gK (ε : ℝ) : Continuous (gK E ε) := by unfold gK; fun_prop

/-- The Fourier transform of the Gaussian weight. -/
lemma gauss_ft {ε : ℝ} (hε : 0 < ε) (z : E) :
    ∫ ξ, (gw ε ξ : ℂ) * ex z ξ = (gK E ε z : ℂ) := by
  have h := fourier_gaussian_innerProductSpace (V := E) (b := (ε : ℂ)) (by simpa using hε) z
  rw [Real.fourier_eq] at h
  have hL : (∫ ξ, (gw ε ξ : ℂ) * ex z ξ) =
      ∫ v, 𝐞 (-⟪v, z⟫) • Complex.exp (-(ε : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    congr 1; funext v
    rw [Circle.smul_def, Real.fourierChar_apply, gw, ex, smul_eq_mul, mul_comm,
      Complex.ofReal_exp, real_inner_comm]
    congr 2
    · push_cast; ring
    · push_cast; ring
  rw [hL, h, gK, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
  push_cast
  ring_nf

lemma integral_gK {ε : ℝ} (hε : 0 < ε) : ∫ z, gK E ε z = 1 := by
  have hb : 0 < π ^ 2 / ε := by positivity
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  have h2 : (fun z : E => gK E ε z) =
      fun z => (π / ε) ^ ((Module.finrank ℝ E : ℝ) / 2) * exp (-(π ^ 2 / ε) * ‖z‖ ^ 2) := by
    funext z; rw [gK]; congr 2; ring
  rw [h2, integral_const_mul, h, ← mul_rpow (by positivity) (by positivity)]
  rw [show π / ε * (π / (π ^ 2 / ε)) = 1 by field_simp]
  exact one_rpow _

lemma integrable_gK {ε : ℝ} (hε : 0 < ε) : Integrable (gK E ε) := by
  by_contra hni
  have := integral_undef hni
  rw [integral_gK hε] at this
  exact one_ne_zero this

end Gauss

section L2

lemma conj_ft (h : E → ℝ) (ξ : E) : starRingEnd ℂ (ft h ξ) = ∫ y, (h y : ℂ) * ex (-y) ξ := by
  rw [ft, ← integral_conj]
  congr 1; funext y
  rw [map_mul, Complex.conj_ofReal, ex_neg]

lemma kernel_eq {h : E → ℝ} (hi : Integrable h) (hm : Measurable h) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ∫ ξ, (gw ε ξ : ℂ) * ex x ξ * starRingEnd ℂ (ft h ξ) =
      ((∫ y, h y * gK E ε (x - y) : ℝ) : ℂ) := by
  have hmC : Measurable fun y => (h y : ℂ) := Complex.measurable_ofReal.comp hm
  have e1 : (fun ξ => (gw ε ξ : ℂ) * ex x ξ * starRingEnd ℂ (ft h ξ)) =
      fun ξ => ∫ y, (gw ε ξ : ℂ) * ex x ξ * ((h y : ℂ) * ex (-y) ξ) := by
    funext ξ; rw [conj_ft, integral_const_mul]
  rw [e1, integral_integral_swap]
  · have h2 : ∀ y, ∫ ξ, (gw ε ξ : ℂ) * ex x ξ * ((h y : ℂ) * ex (-y) ξ) =
        (h y : ℂ) * (gK E ε (x - y) : ℂ) := fun y => by
      rw [← gauss_ft hε, ← integral_const_mul]
      congr 1; funext ξ
      rw [sub_eq_add_neg, ex_add]; ring
    rw [integral_congr_ae (Eventually.of_forall h2), ← integral_complex_ofReal]
    congr 1; funext y; push_cast; rfl
  · have hc : Continuous fun p : E × E => (gw ε p.1 : ℂ) * ex x p.1 * ex (-p.2) p.1 := by
      unfold gw ex; fun_prop
    have e2 : (Function.uncurry fun ξ y => (gw ε ξ : ℂ) * ex x ξ * ((h y : ℂ) * ex (-y) ξ)) =
        fun p : E × E => ((gw ε p.1 : ℂ) * ex x p.1 * ex (-p.2) p.1) * (h p.2 : ℂ) := by
      funext ⟨a, b⟩; simp only [Function.uncurry_apply_pair]; ring
    rw [e2]
    refine Integrable.mono' ((integrable_gw (E := E) hε).mul_prod hi.norm)
      (hc.aestronglyMeasurable.mul (hmC.comp measurable_snd).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    show ‖(gw ε p.1 : ℂ) * ex x p.1 * ex (-p.2) p.1 * (h p.2 : ℂ)‖ ≤ gw ε p.1 * ‖h p.2‖
    rw [norm_mul, norm_mul, norm_mul, norm_ex, norm_ex, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (gw_pos ε p.1).le, mul_one, mul_one]

lemma l2_identity {h : E → ℝ} (hi : Integrable h) (hm : Measurable h) {ε : ℝ} (hε : 0 < ε) :
    ∫ ξ, gw ε ξ * ‖ft h ξ‖ ^ 2 = ∫ x, h x * ∫ y, h y * gK E ε (x - y) := by
  have hFc := continuous_ft hi
  have hmC : Measurable fun y => (h y : ℂ) := Complex.measurable_ofReal.comp hm
  obtain ⟨I1, hI1⟩ : ∃ I1, I1 = ∫ y, ‖h y‖ := ⟨_, rfl⟩
  have hF1 : ∀ ξ, ‖ft h ξ‖ ≤ I1 := fun ξ => hI1 ▸
    norm_integral_le_of_norm_le hi.norm (Eventually.of_forall fun y => by
      rw [norm_mul, norm_ex, mul_one, Complex.norm_real])
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have h1 : (fun ξ => ((gw ε ξ * ‖ft h ξ‖ ^ 2 : ℝ) : ℂ)) =
      fun ξ => ∫ x, (gw ε ξ : ℂ) * ((h x : ℂ) * ex x ξ) * starRingEnd ℂ (ft h ξ) := by
    funext ξ
    rw [integral_mul_const, integral_const_mul, ← ft, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [h1, integral_integral_swap]
  · congr 1; funext x
    have h2 : ∫ ξ, (gw ε ξ : ℂ) * ((h x : ℂ) * ex x ξ) * starRingEnd ℂ (ft h ξ) =
        (h x : ℂ) * ∫ ξ, (gw ε ξ : ℂ) * ex x ξ * starRingEnd ℂ (ft h ξ) := by
      rw [← integral_const_mul]; congr 1; funext ξ; ring
    rw [h2, kernel_eq hi hm hε]; push_cast; rfl
  · have hc : Continuous fun p : E × E =>
        (gw ε p.1 : ℂ) * ex p.2 p.1 * starRingEnd ℂ (ft h p.1) := by
      have h3 : Continuous fun p : E × E => ft h p.1 := hFc.comp continuous_fst
      unfold gw ex; fun_prop
    have e2 : (Function.uncurry fun ξ x =>
        (gw ε ξ : ℂ) * ((h x : ℂ) * ex x ξ) * starRingEnd ℂ (ft h ξ)) =
        fun p : E × E => ((gw ε p.1 : ℂ) * ex p.2 p.1 * starRingEnd ℂ (ft h p.1)) *
          (h p.2 : ℂ) := by
      funext ⟨a, b⟩; simp only [Function.uncurry_apply_pair]; ring
    rw [e2]
    refine Integrable.mono' ((integrable_gw (E := E) hε).mul_prod (hi.norm.mul_const I1))
      (hc.aestronglyMeasurable.mul (hmC.comp measurable_snd).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    show ‖(gw ε p.1 : ℂ) * ex p.2 p.1 * starRingEnd ℂ (ft h p.1) * (h p.2 : ℂ)‖ ≤
      gw ε p.1 * (‖h p.2‖ * I1)
    rw [norm_mul, norm_mul, norm_mul, norm_ex, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (gw_pos ε p.1).le, mul_one, Complex.norm_conj]
    calc gw ε p.1 * ‖ft h p.1‖ * ‖h p.2‖ ≤ gw ε p.1 * I1 * ‖h p.2‖ := by
          gcongr
          · exact (gw_pos ε p.1).le
          · exact hF1 p.1
      _ = gw ε p.1 * (‖h p.2‖ * I1) := by ring

/-- **Regularised Plancherel bound**: `∫ e^{-ε|ξ|²} |ĥ(ξ)|² dξ ≤ M ∫ h` for `0 ≤ h ≤ M`. -/
lemma l2_reg {h : E → ℝ} (hi : Integrable h) (hm : Measurable h) (h0 : ∀ y, 0 ≤ h y) {M : ℝ}
    (hM : ∀ y, h y ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∫ ξ, gw ε ξ * ‖ft h ξ‖ ^ 2 ≤ M * ∫ y, h y := by
  rw [l2_identity hi hm hε]
  have hΦ : ∀ x, 0 ≤ ∫ y, h y * gK E ε (x - y) ∧ ∫ y, h y * gK E ε (x - y) ≤ M := fun x => by
    refine ⟨integral_nonneg fun y => mul_nonneg (h0 y) (gK_nonneg hε _), ?_⟩
    calc ∫ y, h y * gK E ε (x - y) ≤ ∫ y, M * gK E ε (x - y) :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (h0 y)
            (gK_nonneg hε _)) (((integrable_gK hε).comp_sub_left x).const_mul M)
            (Eventually.of_forall fun y => mul_le_mul_of_nonneg_right (hM y) (gK_nonneg hε _))
      _ = M := by
          rw [integral_const_mul, integral_sub_left_eq_self (gK E ε) volume x, integral_gK hε,
            mul_one]
  calc ∫ x, h x * ∫ y, h y * gK E ε (x - y) ≤ ∫ x, h x * M :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg (h0 x) (hΦ x).1)
          (hi.mul_const M) (Eventually.of_forall fun x =>
            mul_le_mul_of_nonneg_left (hΦ x).2 (h0 x))
    _ = M * ∫ y, h y := by rw [integral_mul_const, mul_comm]

/-- **Plancherel bound** (by Fatou's lemma from `l2_reg`): `|ĥ|²` is integrable and
`∫ |ĥ|² ≤ M ∫ h` for `0 ≤ h ≤ M`. -/
lemma l2_bound {h : E → ℝ} (hi : Integrable h) (hm : Measurable h) (h0 : ∀ y, 0 ≤ h y) {M : ℝ}
    (hM : ∀ y, h y ≤ M) :
    Integrable (fun ξ => ‖ft h ξ‖ ^ 2) ∧ ∫ ξ, ‖ft h ξ‖ ^ 2 ≤ M * ∫ y, h y := by
  have hFc := continuous_ft hi
  have hc : Continuous fun ξ => ‖ft h ξ‖ ^ 2 := hFc.norm.pow 2
  obtain ⟨I1, hI1⟩ : ∃ I1, I1 = ∫ y, ‖h y‖ := ⟨_, rfl⟩
  have hF1 : ∀ ξ, ‖ft h ξ‖ ≤ I1 := fun ξ => hI1 ▸
    norm_integral_le_of_norm_le hi.norm (Eventually.of_forall fun y => by
      rw [norm_mul, norm_ex, mul_one, Complex.norm_real])
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have iε : ∀ n, Integrable fun ξ => gw (ε n) ξ * ‖ft h ξ‖ ^ 2 := fun n =>
    (integrable_gw (E := E) (hε n)).mul_bdd hc.aestronglyMeasurable
      (c := I1 ^ 2) (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hF1 ξ) 2)
  have hlim : ∀ ξ : E, Tendsto (fun n => ENNReal.ofReal (gw (ε n) ξ * ‖ft h ξ‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖ft h ξ‖ ^ 2))) := fun ξ => by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have h1 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n => gw (ε n) ξ) atTop (𝓝 1) := by
      have : Continuous fun t : ℝ => exp (-t * ‖ξ‖ ^ 2) := by fun_prop
      have h3 := (this.tendsto 0).comp h1
      simp only [neg_zero, zero_mul, exp_zero] at h3
      exact h3
    simpa using h2.mul_const (‖ft h ξ‖ ^ 2)
  have hlin : ∫⁻ ξ, ENNReal.ofReal (‖ft h ξ‖ ^ 2) ≤ ENNReal.ofReal (M * ∫ y, h y) := by
    calc ∫⁻ ξ, ENNReal.ofReal (‖ft h ξ‖ ^ 2)
        = ∫⁻ ξ, liminf (fun n => ENNReal.ofReal (gw (ε n) ξ * ‖ft h ξ‖ ^ 2)) atTop := by
          congr 1; funext ξ; exact (hlim ξ).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (gw (ε n) ξ * ‖ft h ξ‖ ^ 2)) atTop :=
          lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
            ((continuous_gw (E := E) (ε n)).mul hc).measurable
      _ ≤ ENNReal.ofReal (M * ∫ y, h y) := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (iε n)
            (Eventually.of_forall fun ξ => mul_nonneg (gw_pos _ ξ).le (sq_nonneg _))]
          exact ENNReal.ofReal_le_ofReal (l2_reg hi hm h0 hM (hε n))
  have h0' : 0 ≤ᵐ[volume] fun ξ => ‖ft h ξ‖ ^ 2 := Eventually.of_forall fun ξ => sq_nonneg _
  have hint : Integrable (fun ξ => ‖ft h ξ‖ ^ 2) :=
    ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0').2
      (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0' hc.aestronglyMeasurable]
  have hMi : 0 ≤ M * ∫ y, h y := by
    rw [← integral_const_mul]; exact integral_nonneg fun y => by
      have := h0 y; have := hM y; show 0 ≤ M * h y; nlinarith
  exact ENNReal.toReal_le_of_le_ofReal hMi hlin

end L2

end Mixes.Thm113

namespace Mixes.Thm113

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Conv

/-- The convolution `(f * g)(x) = ∫ f(t) g(x - t) dt`. -/
def conv (f g : E → ℝ) (x : E) : ℝ := ∫ t, f t * g (x - t)

lemma conv_eq_convolution (f g : E → ℝ) :
    conv f g = convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x; rw [convolution_mul]; rfl

lemma conv_comm (f g : E → ℝ) : conv f g = conv g f := by
  funext x
  rw [conv, conv, ← integral_sub_left_eq_self _ volume x]
  congr 1; funext t; rw [sub_sub_cancel, mul_comm]

lemma integrable_conv {f g : E → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (conv f g) := by
  rw [conv_eq_convolution]; exact hf.integrable_convolution _ hg

lemma integral_conv {f g : E → ℝ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, conv f g x = (∫ x, f x) * ∫ x, g x := by
  rw [conv_eq_convolution, integral_convolution _ hf hg]; rfl

lemma conv_nonneg {f g : E → ℝ} (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (x : E) :
    0 ≤ conv f g x :=
  integral_nonneg fun t => mul_nonneg (hf t) (hg _)

lemma conv_le {f g : E → ℝ} (hf : Integrable f) (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    {M : ℝ} (hM : ∀ y, g y ≤ M) (x : E) : conv f g x ≤ M * ∫ y, f y := by
  rw [conv, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg (hf0 t) (hg0 _))
    (hf.const_mul M) (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM _) (hf0 t)

lemma ft_conv {f g : E → ℝ} (hf : Integrable f) (hg : Integrable g) (ξ : E) :
    ft (conv f g) ξ = ft f ξ * ft g ξ := by
  have h1 : (fun x => ((conv f g x : ℝ) : ℂ)) =
      convolution (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) (ContinuousLinearMap.mul ℂ ℂ)
        volume := by
    funext x
    rw [convolution_mul, conv, ← integral_complex_ofReal]
    congr 1; funext t; push_cast; rfl
  rw [ft_eq_fourier, ft_eq_fourier, ft_eq_fourier, h1]
  exact Real.fourier_mul_convolution_eq (hf.ofReal (𝕜 := ℂ)) (hg.ofReal (𝕜 := ℂ)) ξ

/-- Continuity of `g * f` for `g` bounded and integrable and `f` integrable. -/
lemma continuous_conv {f g : E → ℝ} (hf : Integrable f) (hg : Integrable g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) : Continuous (conv g f) := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨c, hcs, hfc, hcc, hci⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le (ε := ε / 2 / (M + 1)) (by positivity)
  refine ⟨conv g c, ?_, fun x => hεu ?_⟩
  · rw [conv_eq_convolution]
    exact hcs.continuous_convolution_right _ hg.locallyIntegrable hcc
  · rw [Real.dist_eq, conv, conv, ← integral_sub]
    · calc |∫ t, (g t * f (x - t) - g t * c (x - t))|
          ≤ ∫ t, M * ‖f (x - t) - c (x - t)‖ := by
            rw [← Real.norm_eq_abs]
            refine norm_integral_le_of_norm_le
              (((hf.sub hci).norm.comp_sub_left x).const_mul M) (Eventually.of_forall fun t => ?_)
            rw [← mul_sub, norm_mul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)
        _ = M * ∫ t, ‖f t - c t‖ := by
            rw [integral_const_mul,
              integral_sub_left_eq_self (fun t => ‖f t - c t‖) volume x]
        _ ≤ M * (ε / 2 / (M + 1)) := mul_le_mul_of_nonneg_left hfc hM0
        _ < ε := by
            rw [mul_div_assoc']
            rw [div_lt_iff₀ (by linarith)]
            nlinarith
    · exact (hf.comp_sub_left x).bdd_mul hg.aestronglyMeasurable
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hM t) |>.congr
        (Eventually.of_forall fun t => rfl)
    · exact (hci.comp_sub_left x).bdd_mul hg.aestronglyMeasurable
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hM t)

/-- The convolution `h_0 * h_1 * ⋯ * h_m` of a family. -/
def convF : (m : ℕ) → (Fin (m + 1) → E → ℝ) → E → ℝ
  | 0, hs => hs 0
  | m + 1, hs => conv (hs 0) (convF m (Fin.tail hs))

/-- Probability densities bounded by `M`. -/
structure PD (M : ℝ) (h : E → ℝ) : Prop where
  int : Integrable h
  meas : Measurable h
  nonneg : ∀ y, 0 ≤ h y
  le : ∀ y, h y ≤ M
  one : ∫ y, h y = 1

lemma InH.pd {A r R : ℝ} {K : Set E} {h : E → ℝ} (hH : InH A r R K h) (hr : 0 ≤ r) :
    PD (exp A / volume.real K) h :=
  ⟨hH.integrable hr, hH.meas, hH.nonneg hr, hH.le_max hr, hH.int⟩

lemma PD.mono {M M' : ℝ} {h : E → ℝ} (hP : PD M h) (hMM : M ≤ M') : PD M' h :=
  ⟨hP.int, hP.meas, hP.nonneg, fun y => (hP.le y).trans hMM, hP.one⟩

lemma PD.norm_ft_le {M : ℝ} {h : E → ℝ} (hP : PD M h) (ξ : E) : ‖ft h ξ‖ ≤ 1 := by
  calc ‖ft h ξ‖ ≤ ∫ y, h y := by
        refine norm_integral_le_of_norm_le hP.int (Eventually.of_forall fun y => ?_)
        rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_of_nonneg (hP.nonneg y)]
    _ = 1 := hP.one

lemma pd_convF {M : ℝ} : ∀ (m : ℕ) (hs : Fin (m + 1) → E → ℝ), (∀ k, PD M (hs k)) →
    Integrable (convF m hs) ∧ (∀ y, 0 ≤ convF m hs y) ∧ (∀ y, convF m hs y ≤ M) ∧
      ∫ y, convF m hs y = 1
  | 0, hs, hP => ⟨(hP 0).int, (hP 0).nonneg, (hP 0).le, (hP 0).one⟩
  | m + 1, hs, hP => by
    obtain ⟨i1, n1, l1, o1⟩ := pd_convF m (Fin.tail hs) fun k => hP k.succ
    refine ⟨integrable_conv (hP 0).int i1, conv_nonneg (hP 0).nonneg n1, fun y => ?_, ?_⟩
    · have := conv_le (hP 0).int (hP 0).nonneg n1 l1 y
      rw [(hP 0).one, mul_one] at this; exact this
    · show ∫ y, conv (hs 0) (convF m (Fin.tail hs)) y = 1
      rw [integral_conv (hP 0).int i1, (hP 0).one, o1, one_mul]

lemma integrable_convF : ∀ (m : ℕ) (hs : Fin (m + 1) → E → ℝ), (∀ k, Integrable (hs k)) →
    Integrable (convF m hs)
  | 0, _, hi => hi 0
  | m + 1, hs, hi => integrable_conv (hi 0) (integrable_convF m (Fin.tail hs) fun k => hi k.succ)

lemma ft_convF : ∀ (m : ℕ) (hs : Fin (m + 1) → E → ℝ), (∀ k, Integrable (hs k)) →
    ∀ ξ, ft (convF m hs) ξ = ∏ k, ft (hs k) ξ
  | 0, hs, _, ξ => by simp [convF]
  | m + 1, hs, hi, ξ => by
    show ft (conv (hs 0) (convF m (Fin.tail hs))) ξ = _
    rw [ft_conv (hi 0) (integrable_convF m (Fin.tail hs) fun k => hi k.succ),
      ft_convF m (Fin.tail hs) (fun k => hi k.succ),
      Fin.prod_univ_succ (fun k => ft (hs k) ξ)]
    rfl

lemma continuous_convF {M : ℝ} (m : ℕ) (hs : Fin (m + 2) → E → ℝ) (hP : ∀ k, PD M (hs k)) :
    Continuous (convF (m + 1) hs) := by
  show Continuous (conv (hs 0) (convF m (Fin.tail hs)))
  refine continuous_conv (integrable_convF m _ fun k => (hP k.succ).int) (hP 0).int
    (M := M) fun y => ?_
  rw [abs_of_nonneg ((hP 0).nonneg y)]; exact (hP 0).le y

/-- `‖∏ ĥ_k‖ ≤ (‖ĥ_0‖² + ‖ĥ_1‖²)/2` for two or more probability densities. -/
lemma norm_prod_ft_le {M : ℝ} (m : ℕ) (hs : Fin (m + 2) → E → ℝ) (hP : ∀ k, PD M (hs k))
    (ξ : E) : ‖∏ k, ft (hs k) ξ‖ ≤ (‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, norm_mul, norm_mul]
  have h1 : ‖∏ i : Fin m, ft (hs i.succ.succ) ξ‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => (hP _).norm_ft_le ξ
  have h2 : ‖ft (hs 0) ξ‖ * ‖ft (hs 1) ξ‖ ≤ (‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖ft (hs 0) ξ‖ - ‖ft (hs 1) ξ‖)]
  calc ‖ft (hs 0) ξ‖ * (‖ft (hs (Fin.succ 0)) ξ‖ * ‖∏ i : Fin m, ft (hs i.succ.succ) ξ‖)
      ≤ ‖ft (hs 0) ξ‖ * (‖ft (hs 1) ξ‖ * 1) := by
        gcongr
        exact le_of_eq rfl
    _ ≤ _ := by rw [mul_one]; exact h2

lemma integrable_prod_ft {M : ℝ} (m : ℕ) (hs : Fin (m + 2) → E → ℝ) (hP : ∀ k, PD M (hs k)) :
    Integrable fun ξ => ∏ k, ft (hs k) ξ := by
  have i0 := (l2_bound (hP 0).int (hP 0).meas (hP 0).nonneg (hP 0).le).1
  have i1 := (l2_bound (hP 1).int (hP 1).meas (hP 1).nonneg (hP 1).le).1
  refine Integrable.mono' ((i0.add i1).div_const 2) ?_
    (Eventually.of_forall fun ξ => norm_prod_ft_le m hs hP ξ)
  exact (continuous_finsetProd _ fun k _ => continuous_ft (hP k).int).aestronglyMeasurable

/-- **Fourier inversion** for the convolution of two or more bounded probability densities:
`f(y) = ∫ e^{2πi⟨ξ, y⟩} ∏ ĥ_k(ξ) dξ`. -/
lemma convF_inversion {M : ℝ} (m : ℕ) (hs : Fin (m + 2) → E → ℝ) (hP : ∀ k, PD M (hs k))
    (y : E) : (convF (m + 1) hs y : ℂ) = ∫ ξ, ex (-y) ξ * ∏ k, ft (hs k) ξ := by
  have hc := continuous_convF m hs hP
  have hi := integrable_convF (m + 1) hs fun k => (hP k).int
  have hF : 𝓕 (fun x => (convF (m + 1) hs x : ℂ)) = fun ξ => ∏ k, ft (hs k) ξ := by
    funext ξ; rw [← ft_eq_fourier, ft_convF _ _ (fun k => (hP k).int)]
  have hFi : Integrable (𝓕 (fun x => (convF (m + 1) hs x : ℂ))) := by
    rw [hF]; exact integrable_prod_ft m hs hP
  have hinv := MeasureTheory.Integrable.fourierInv_fourier_eq (v := y) (hi.ofReal (𝕜 := ℂ)) hFi
    (Complex.continuous_ofReal.comp hc).continuousAt
  have hinv' : 𝓕⁻ (𝓕 fun x => (convF (m + 1) hs x : ℂ)) y = (convF (m + 1) hs y : ℂ) := hinv
  rw [← hinv', hF, Real.fourierInv_eq]
  congr 1; funext ξ
  rw [Circle.smul_def, Real.fourierChar_apply, ex, smul_eq_mul, inner_neg_left, real_inner_comm]
  congr 2; push_cast; ring

end Conv

section Pointwise

/-- Telescoping: `‖∏ a - ∏ b‖ ≤ (∑ ‖a k - b k‖) β^{n-1}` when all factors have norm `≤ β`. -/
lemma norm_prod_sub_prod_le : ∀ (n : ℕ) (a b : Fin (n + 1) → ℂ) {β : ℝ}, 0 ≤ β →
    (∀ k, ‖a k‖ ≤ β) → (∀ k, ‖b k‖ ≤ β) →
    ‖∏ k, a k - ∏ k, b k‖ ≤ (∑ k, ‖a k - b k‖) * β ^ n
  | 0, a, b, β, _, _, _ => by simp
  | n + 1, a, b, β, hβ, ha, hb => by
    rw [Fin.prod_univ_succ a, Fin.prod_univ_succ b, Fin.sum_univ_succ]
    have ih := norm_prod_sub_prod_le n (fun k => a k.succ) (fun k => b k.succ) hβ
      (fun k => ha _) (fun k => hb _)
    have hpa : ‖∏ k : Fin (n + 1), a k.succ‖ ≤ β ^ (n + 1) := by
      rw [norm_prod]
      calc ∏ k : Fin (n + 1), ‖a k.succ‖ ≤ ∏ _k : Fin (n + 1), β :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ha _
        _ = β ^ (n + 1) := by simp
    have h1 : a 0 * ∏ k : Fin (n + 1), a k.succ - b 0 * ∏ k : Fin (n + 1), b k.succ =
        (a 0 - b 0) * ∏ k : Fin (n + 1), a k.succ +
          b 0 * (∏ k : Fin (n + 1), a k.succ - ∏ k : Fin (n + 1), b k.succ) := by ring
    rw [h1]
    calc ‖(a 0 - b 0) * ∏ k : Fin (n + 1), a k.succ +
          b 0 * (∏ k : Fin (n + 1), a k.succ - ∏ k : Fin (n + 1), b k.succ)‖
        ≤ ‖a 0 - b 0‖ * β ^ (n + 1) +
            β * ((∑ k : Fin (n + 1), ‖a k.succ - b k.succ‖) * β ^ n) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hpa (norm_nonneg _)
          · rw [norm_mul]; exact mul_le_mul (hb 0) ih (norm_nonneg _) hβ
      _ = (‖a 0 - b 0‖ + ∑ k : Fin (n + 1), ‖a k.succ - b k.succ‖) * β ^ (n + 1) := by ring

lemma ex_zero_right (y : E) : ex y 0 = 1 := by simp [ex]

lemma ex_sum {ι : Type*} (s : Finset ι) (y : ι → E) (ξ : E) :
    ex (∑ k ∈ s, y k) ξ = ∏ k ∈ s, ex (y k) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ex_add, ih]

lemma ft_eq_ex_mul_cf (h : E → ℝ) (ξ : E) : ft h ξ = ex (Large.meanD h) ξ * cf h ξ := by
  have : cf h ξ = ex (-Large.meanD h) ξ * ft h ξ := by
    rw [cf, ft, ← integral_const_mul]
    congr 1; funext y
    rw [show -((2 * π * ⟪y - Large.meanD h, ξ⟫ : ℝ) : ℂ) * Complex.I
      = -((2 * π * ⟪y + -Large.meanD h, ξ⟫ : ℝ) : ℂ) * Complex.I by rw [sub_eq_add_neg],
      ← ex, ex_add]
    ring
  rw [this, ← mul_assoc, ← ex_add, add_neg_cancel, ex_zero_left, one_mul]

lemma varF_smul (h : E → ℝ) (c : ℝ) (ξ : E) : varF h (c • ξ) = c ^ 2 * varF h ξ := by
  rw [varF, varF, ← integral_const_mul]
  congr 1; funext y
  rw [inner_smul_right]; ring

lemma ex_smul_right (y ξ : E) (c : ℝ) : ex y (c • ξ) = ex (c • y) ξ := by
  rw [ex, ex, inner_smul_right, inner_smul_left]; simp

variable {A r R : ℝ} {K : Set E} {h : E → ℝ}

/-- The radius `r₀` of the inner region. -/
def rad0 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (A r R : ℝ) : ℝ :=
  min (1 / (2 * π * R)) (π ^ 2 * sig E A r R / (2 * π * R) ^ 3)

lemma rad0_pos (hr : 0 < r) (hR : 0 < R) : 0 < rad0 E A r R := by
  have := sig_pos (E := E) (A := A) hr hR
  unfold rad0; positivity

lemma inner_facts (_hr : 0 < r) (hR : 0 < R) {ξ : E} (hξ : ‖ξ‖ ≤ rad0 E A r R) :
    2 * π * R * ‖ξ‖ ≤ 1 ∧ (2 * π * R * ‖ξ‖) ^ 3 ≤ π ^ 2 * sig E A r R * ‖ξ‖ ^ 2 ∧
      2 * π ^ 2 * R ^ 2 * ‖ξ‖ ^ 2 ≤ 1 / 2 := by
  have h1 : ‖ξ‖ ≤ 1 / (2 * π * R) := hξ.trans (min_le_left _ _)
  have h2 : ‖ξ‖ ≤ π ^ 2 * sig E A r R / (2 * π * R) ^ 3 := hξ.trans (min_le_right _ _)
  have hc : 0 < 2 * π * R := by positivity
  have hn := norm_nonneg ξ
  have e1 : 2 * π * R * ‖ξ‖ ≤ 1 := by
    rw [le_div_iff₀ hc] at h1; linarith
  refine ⟨e1, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at h2
    calc (2 * π * R * ‖ξ‖) ^ 3 = ‖ξ‖ * (2 * π * R) ^ 3 * ‖ξ‖ ^ 2 := by ring
      _ ≤ π ^ 2 * sig E A r R * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
  · have : (2 * π * R * ‖ξ‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) e1
    nlinarith

/-- Inner region, modulus: `|c_h(ξ)| ≤ e^{-π² σ |ξ|²}`. -/
lemma InH.norm_cf_le_inner (hH : InH A r R K h) (hr : 0 < r) (hR : 0 < R) {ξ : E}
    (hξ : ‖ξ‖ ≤ rad0 E A r R) : ‖cf h ξ‖ ≤ exp (-(π ^ 2 * sig E A r R) * ‖ξ‖ ^ 2) := by
  obtain ⟨e1, e2, e3⟩ := inner_facts (A := A) hr hR hξ
  have hT := hH.cf_taylor hr.le e1
  have hv1 := hH.varF_ge hr ξ
  have hv2 := hH.varF_le hr.le ξ
  set x := 2 * π ^ 2 * varF h ξ
  have hx1 : x ≤ 1 := by
    have : x ≤ 2 * π ^ 2 * (R ^ 2 * ‖ξ‖ ^ 2) := mul_le_mul_of_nonneg_left hv2 (by positivity)
    nlinarith
  have hx2 : 2 * π ^ 2 * (sig E A r R * ‖ξ‖ ^ 2) ≤ x :=
    mul_le_mul_of_nonneg_left hv1 (by positivity)
  have hn1 : ‖(1 : ℂ) - (x : ℂ)‖ = 1 - x := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  calc ‖cf h ξ‖ ≤ ‖cf h ξ - (1 - (x : ℂ))‖ + ‖(1 : ℂ) - (x : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ π ^ 2 * sig E A r R * ‖ξ‖ ^ 2 + (1 - x) := by rw [hn1]; linarith
    _ ≤ -(π ^ 2 * sig E A r R) * ‖ξ‖ ^ 2 + 1 := by nlinarith
    _ ≤ exp (-(π ^ 2 * sig E A r R) * ‖ξ‖ ^ 2) := add_one_le_exp _

/-- Inner region, difference: `|c_h(ξ) - e^{-2π² Σ_h(ξ)}| ≤ (2πR)³|ξ|³ + (2π²R²)²|ξ|⁴`. -/
lemma InH.norm_cf_sub_le_inner (hH : InH A r R K h) (hr : 0 < r) (hR : 0 < R) {ξ : E}
    (hξ : ‖ξ‖ ≤ rad0 E A r R) :
    ‖cf h ξ - (exp (-(2 * π ^ 2 * varF h ξ)) : ℂ)‖ ≤
      (2 * π * R) ^ 3 * ‖ξ‖ ^ 3 + (2 * π ^ 2 * R ^ 2) ^ 2 * ‖ξ‖ ^ 4 := by
  obtain ⟨e1, e2, e3⟩ := inner_facts (A := A) hr hR hξ
  have hT := hH.cf_taylor hr.le e1
  have hv0 := hH.varF_nonneg hr.le ξ
  have hv2 := hH.varF_le hr.le ξ
  set x := 2 * π ^ 2 * varF h ξ
  have hx0 : 0 ≤ x := by positivity
  have hxR : x ≤ 2 * π ^ 2 * R ^ 2 * ‖ξ‖ ^ 2 := by
    have : x ≤ 2 * π ^ 2 * (R ^ 2 * ‖ξ‖ ^ 2) := mul_le_mul_of_nonneg_left hv2 (by positivity)
    linarith
  have hx1 : |-x| ≤ 1 := by rw [abs_neg, abs_of_nonneg hx0]; linarith
  have hE := Real.abs_exp_sub_one_sub_id_le hx1
  have hn : ‖((1 - x : ℝ) : ℂ) - (exp (-x) : ℂ)‖ ≤ x ^ 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have : exp (-x) - (1 - x) = exp (-x) - 1 - -x := by ring
    rw [this]; simpa using hE
  calc ‖cf h ξ - (exp (-x) : ℂ)‖
      ≤ ‖cf h ξ - (1 - (x : ℂ))‖ + ‖((1 - x : ℝ) : ℂ) - (exp (-x) : ℂ)‖ := by
        refine (norm_sub_le_norm_sub_add_norm_sub _ ((1 - x : ℝ) : ℂ) _).trans_eq ?_
        push_cast; rfl
    _ ≤ (2 * π * R * ‖ξ‖) ^ 3 + x ^ 2 := add_le_add hT hn
    _ ≤ (2 * π * R) ^ 3 * ‖ξ‖ ^ 3 + (2 * π ^ 2 * R ^ 2) ^ 2 * ‖ξ‖ ^ 4 := by
        have : x ^ 2 ≤ (2 * π ^ 2 * R ^ 2 * ‖ξ‖ ^ 2) ^ 2 := pow_le_pow_left₀ hx0 hxR 2
        nlinarith

end Pointwise

section GaussMoments

/-- `I_k(b) = ∫ |ξ|^k e^{-b|ξ|²} dξ`. -/
def gI (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (k : ℕ) (b : ℝ) : ℝ :=
  ∫ ξ : E, ‖ξ‖ ^ k * exp (-b * ‖ξ‖ ^ 2)

lemma pow_le_one_add_pow_two_mul (t : ℝ) (ht : 0 ≤ t) (k : ℕ) : t ^ k ≤ 1 + t ^ (2 * k) := by
  rcases le_total t 1 with h | h
  · have := pow_le_one₀ ht h (n := k); have : 0 ≤ t ^ (2 * k) := by positivity
    linarith
  · have : t ^ k ≤ t ^ (2 * k) := pow_le_pow_right₀ h (by omega)
    linarith

lemma integrable_rexp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable fun ξ : E => exp (-b * ‖ξ‖ ^ 2) := integrable_gw (E := E) hb

lemma integrable_pow_gauss (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun ξ : E => ‖ξ‖ ^ k * exp (-b * ‖ξ‖ ^ 2) := by
  have hb2 : 0 < b / 2 := by positivity
  have hfact : ∀ t : ℝ, 0 ≤ t → t ^ (2 * k) ≤ k.factorial * (2 / b) ^ k * exp (b / 2 * t ^ 2) :=
    fun t ht => by
      have h1 := Real.pow_div_factorial_le_exp (x := b / 2 * t ^ 2) (by positivity) k
      have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
      rw [div_le_iff₀ hf] at h1
      calc t ^ (2 * k) = (2 / b) ^ k * (b / 2 * t ^ 2) ^ k := by
            rw [mul_pow, ← mul_assoc, ← mul_pow, show 2 / b * (b / 2) = 1 by field_simp, one_pow,
              one_mul, ← pow_mul, mul_comm 2 k]
        _ ≤ (2 / b) ^ k * (exp (b / 2 * t ^ 2) * k.factorial) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = k.factorial * (2 / b) ^ k * exp (b / 2 * t ^ 2) := by ring
  refine Integrable.mono' ((integrable_rexp_neg_mul_sq_norm (E := E) hb).add
    ((integrable_rexp_neg_mul_sq_norm (E := E) hb2).const_mul (k.factorial * (2 / b) ^ k)))
    (by fun_prop) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := pow_le_one_add_pow_two_mul ‖ξ‖ (norm_nonneg _) k
  have h2 := hfact ‖ξ‖ (norm_nonneg _)
  have he : exp (-b * ‖ξ‖ ^ 2) = exp (-(b / 2) * ‖ξ‖ ^ 2) * exp (-(b / 2) * ‖ξ‖ ^ 2) := by
    rw [← exp_add]; ring_nf
  have he2 : exp (b / 2 * ‖ξ‖ ^ 2) * exp (-(b / 2) * ‖ξ‖ ^ 2) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  calc ‖ξ‖ ^ k * exp (-b * ‖ξ‖ ^ 2) ≤ (1 + ‖ξ‖ ^ (2 * k)) * exp (-b * ‖ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp (-b * ‖ξ‖ ^ 2) + ‖ξ‖ ^ (2 * k) * exp (-(b / 2) * ‖ξ‖ ^ 2) *
          exp (-(b / 2) * ‖ξ‖ ^ 2) := by rw [he]; ring
    _ ≤ exp (-b * ‖ξ‖ ^ 2) + k.factorial * (2 / b) ^ k * exp (b / 2 * ‖ξ‖ ^ 2) *
          exp (-(b / 2) * ‖ξ‖ ^ 2) * exp (-(b / 2) * ‖ξ‖ ^ 2) := by
        gcongr
    _ = exp (-b * ‖ξ‖ ^ 2) + k.factorial * (2 / b) ^ k * exp (-(b / 2) * ‖ξ‖ ^ 2) := by
        rw [show (k.factorial : ℝ) * (2 / b) ^ k * exp (b / 2 * ‖ξ‖ ^ 2) *
          exp (-(b / 2) * ‖ξ‖ ^ 2) * exp (-(b / 2) * ‖ξ‖ ^ 2) = k.factorial * (2 / b) ^ k *
          (exp (b / 2 * ‖ξ‖ ^ 2) * exp (-(b / 2) * ‖ξ‖ ^ 2)) * exp (-(b / 2) * ‖ξ‖ ^ 2) by ring,
          he2, mul_one]

/-- Scaling: `I_k(b) = b^{-(d+k)/2} I_k(1)`. -/
lemma gI_scale (k : ℕ) {b : ℝ} (hb : 0 < b) :
    gI E k b = b ^ (-((Module.finrank ℝ E : ℝ) + k) / 2) * gI E k 1 := by
  set c := b ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 < c := by positivity
  have hcb : b * c ^ 2 = 1 := by
    rw [hc, ← rpow_natCast, ← rpow_mul hb.le]; norm_num
    rw [rpow_neg_one, mul_inv_cancel₀ hb.ne']
  have h1 := Measure.integral_comp_smul (volume : Measure E)
    (fun ξ : E => ‖ξ‖ ^ k * exp (-b * ‖ξ‖ ^ 2)) c
  have h2 : (fun η : E => ‖c • η‖ ^ k * exp (-b * ‖c • η‖ ^ 2)) =
      fun η => c ^ k * (‖η‖ ^ k * exp (-1 * ‖η‖ ^ 2)) := by
    funext η
    rw [norm_smul, Real.norm_of_nonneg hc0.le, mul_pow, mul_pow, ← mul_assoc (-b), mul_comm (-b),
      ← mul_assoc, show c ^ 2 * -b = -(b * c ^ 2) by ring, hcb]
  rw [h2, integral_const_mul, abs_of_pos (by positivity), smul_eq_mul] at h1
  rw [gI, gI]
  have hd : (0 : ℝ) < c ^ Module.finrank ℝ E := by positivity
  have h3 : ∫ ξ : E, ‖ξ‖ ^ k * exp (-b * ‖ξ‖ ^ 2) =
      c ^ Module.finrank ℝ E * c ^ k * ∫ η : E, ‖η‖ ^ k * exp (-1 * ‖η‖ ^ 2) := by
    rw [mul_assoc, h1, ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  rw [h3, ← pow_add, hc, ← rpow_natCast, ← rpow_mul hb.le]
  congr 2
  push_cast; ring

lemma gI_nonneg (k : ℕ) (b : ℝ) : 0 ≤ gI E k b :=
  integral_nonneg fun ξ => by positivity

end GaussMoments

section ErrorBound

variable {A r R : ℝ}

/-- **Uniform Fourier gap** for the class `𝓗` (Lemma 112): there is `q ∈ [1/2, 1)` with
`|ĥ(ξ)| ≤ q` for `|ξ| ≥ r₀` and every `h ∈ 𝓗`. No selection theorem is needed: the bound comes
from the uniform density on a ball of radius `r` inside `K`. -/
lemma exists_gap (hr : 0 < r) (hrR : r ≤ R) :
    ∃ q : ℝ, 1 / 2 ≤ q ∧ q < 1 ∧ ∀ (K : Set E) (h : E → ℝ), InH A r R K h →
      ∀ ξ : E, rad0 E A r R ≤ ‖ξ‖ → ‖ft h ξ‖ ≤ q := by
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨qB, hqB, hgap⟩ := ballInt_gap (E := E) hr (rad0_pos (E := E) (A := A) hr hR)
  have hα : 0 < alph E A r R := by
    unfold alph; have := vB_pos (E := E) hr; have := vB_pos (E := E) hR; positivity
  have hVr := vB_pos (E := E) hr
  refine ⟨max (1 / 2) (1 - alph E A r R + alph E A r R * qB), le_max_left _ _,
    max_lt (by norm_num) (by nlinarith), fun K h hH ξ hξ => ?_⟩
  refine (hH.norm_ft_le hr ξ).trans (le_trans ?_ (le_max_right _ _))
  have : ‖ballInt E r ξ‖ / vB E r ≤ qB := by rw [div_le_iff₀ hVr]; exact hgap ξ hξ
  nlinarith

/-- **Pointwise three-region bound** for `n = m + 2` factors. -/
lemma err_pointwise (hr : 0 < r) (hrR : r ≤ R) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ (K : Set E) (h : E → ℝ), InH A r R K h → ∀ ξ : E, rad0 E A r R ≤ ‖ξ‖ → ‖ft h ξ‖ ≤ q)
    (m : ℕ) (Ks : Fin (m + 2) → Set E) (hs : Fin (m + 2) → E → ℝ)
    (hH : ∀ k, InH A r R (Ks k) (hs k)) (ξ : E) :
    ‖∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
      ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * (‖ξ‖ ^ 3 *
          exp (-(π ^ 2 * sig E A r R * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2)) +
        (2 * π ^ 2 * R ^ 2) ^ 2 * (‖ξ‖ ^ 4 *
          exp (-(π ^ 2 * sig E A r R * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2))) +
      q ^ m * ((‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2) +
      exp (-(π ^ 2 * sig E A r R * rad0 E A r R ^ 2 * ((m : ℝ) + 2))) *
        exp (-(π ^ 2 * sig E A r R * ((m : ℝ) + 2)) * ‖ξ‖ ^ 2) := by
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨σ, hσd⟩ : ∃ σ, σ = sig E A r R := ⟨_, rfl⟩
  obtain ⟨r0, hr0d⟩ : ∃ r0, r0 = rad0 E A r R := ⟨_, rfl⟩
  rw [← hσd, ← hr0d]
  have hσ : 0 < σ := hσd ▸ sig_pos hr hR
  set a := π ^ 2 * σ with ha
  have ha0 : 0 < a := by positivity
  have hT1 : 0 ≤ ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * (‖ξ‖ ^ 3 *
      exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2)) + (2 * π ^ 2 * R ^ 2) ^ 2 * (‖ξ‖ ^ 4 *
      exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2))) := by positivity
  have hT2 : 0 ≤ q ^ m * ((‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2) := by positivity
  have hT3 : 0 ≤ exp (-(a * r0 ^ 2 * ((m : ℝ) + 2))) * exp (-(a * ((m : ℝ) + 2)) * ‖ξ‖ ^ 2) := by
    positivity
  have hek : ∀ k, ‖(exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤ exp (-(2 * a) * ‖ξ‖ ^ 2) := by
    intro k
    rw [Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, exp_le_exp]
    have := (hH k).varF_ge hr ξ
    rw [← hσd] at this
    nlinarith [pi_pos]
  rcases le_or_gt ‖ξ‖ r0 with hξ | hξ
  · -- inner region
    have hξ' : ‖ξ‖ ≤ rad0 E A r R := hr0d ▸ hξ
    have hβ : ∀ k, ‖cf (hs k) ξ‖ ≤ exp (-a * ‖ξ‖ ^ 2) := fun k => by
      have := (hH k).norm_cf_le_inner hr hR hξ'
      rw [← hσd] at this; simpa [ha] using this
    have hβ' : ∀ k, ‖(exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤ exp (-a * ‖ξ‖ ^ 2) :=
      fun k => (hek k).trans (exp_le_exp.2 (by nlinarith [sq_nonneg ‖ξ‖]))
    have htel := norm_prod_sub_prod_le (m + 1) (fun k => cf (hs k) ξ)
      (fun k => (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)) (exp_pos _).le hβ hβ'
    have hsum : ∑ k, ‖cf (hs k) ξ - (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
        ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * ‖ξ‖ ^ 3 + (2 * π ^ 2 * R ^ 2) ^ 2 * ‖ξ‖ ^ 4) := by
      calc ∑ k, ‖cf (hs k) ξ - (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖
          ≤ ∑ _k : Fin (m + 2), ((2 * π * R) ^ 3 * ‖ξ‖ ^ 3 + (2 * π ^ 2 * R ^ 2) ^ 2 * ‖ξ‖ ^ 4) :=
            Finset.sum_le_sum fun k _ => (hH k).norm_cf_sub_le_inner hr hR hξ'
        _ = _ := by simp; ring
    have hpow : exp (-a * ‖ξ‖ ^ 2) ^ (m + 1) = exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2) := by
      rw [← Real.exp_natCast_mul]; congr 1; push_cast; ring
    rw [hpow] at htel
    have : ‖∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
        ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * (‖ξ‖ ^ 3 * exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2)) +
        (2 * π ^ 2 * R ^ 2) ^ 2 * (‖ξ‖ ^ 4 * exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2))) := by
      refine htel.trans ?_
      calc (∑ k, ‖cf (hs k) ξ - (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖) *
            exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2)
          ≤ ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * ‖ξ‖ ^ 3 + (2 * π ^ 2 * R ^ 2) ^ 2 * ‖ξ‖ ^ 4) *
            exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hsum (exp_pos _).le
        _ = _ := by ring
    linarith
  · -- outer region
    have hξ' : rad0 E A r R ≤ ‖ξ‖ := hr0d ▸ hξ.le
    have h1 : ‖∏ k, cf (hs k) ξ‖ ≤ q ^ m * ((‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2) := by
      rw [norm_prod]
      simp_rw [norm_cf_eq]
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      have hrest : ∏ i : Fin m, ‖ft (hs i.succ.succ) ξ‖ ≤ q ^ m := by
        calc ∏ i : Fin m, ‖ft (hs i.succ.succ) ξ‖ ≤ ∏ _i : Fin m, q :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hq _ _ (hH _) ξ hξ'
          _ = q ^ m := by simp
      have h2 : ‖ft (hs 0) ξ‖ * ‖ft (hs 1) ξ‖ ≤ (‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖ft (hs 0) ξ‖ - ‖ft (hs 1) ξ‖)]
      calc ‖ft (hs 0) ξ‖ * (‖ft (hs (Fin.succ 0)) ξ‖ * ∏ i : Fin m, ‖ft (hs i.succ.succ) ξ‖)
          = (‖ft (hs 0) ξ‖ * ‖ft (hs 1) ξ‖) * ∏ i : Fin m, ‖ft (hs i.succ.succ) ξ‖ := by
            rw [mul_assoc]; rfl
        _ ≤ ((‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2) * q ^ m :=
            mul_le_mul h2 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
        _ = _ := mul_comm _ _
    have h3 : ‖∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
        exp (-(a * r0 ^ 2 * ((m : ℝ) + 2))) * exp (-(a * ((m : ℝ) + 2)) * ‖ξ‖ ^ 2) := by
      rw [norm_prod]
      have hr00 : 0 ≤ r0 := by rw [hr0d]; exact (rad0_pos (E := E) (A := A) hr hR).le
      have hsq : r0 ^ 2 ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ hr00 hξ.le 2
      have hγ : ∀ k, ‖(exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
          exp (-(a * r0 ^ 2) - a * ‖ξ‖ ^ 2) := fun k =>
        (hek k).trans (exp_le_exp.2 (by nlinarith))
      calc ∏ k, ‖(exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖
          ≤ ∏ _k : Fin (m + 2), exp (-(a * r0 ^ 2) - a * ‖ξ‖ ^ 2) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hγ k
        _ = exp (-(a * r0 ^ 2) - a * ‖ξ‖ ^ 2) ^ (m + 2) := by simp
        _ = _ := by
            rw [← Real.exp_natCast_mul, ← exp_add]; congr 1; push_cast; ring
    calc ‖∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖
        ≤ ‖∏ k, cf (hs k) ξ‖ + ‖∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith

/-- **Integrated three-region bound** (Lemma 112): with `a = π²σ`, `n = m + 2` factors,
`∫ |∏ c_k - ∏ e^{-2π²Σ_k}| ≤ n((2πR)³ I₃(a(n-1)) + (2π²R²)² I₄(a(n-1))) + q^{n-2} M
+ e^{-a r₀² n} I₀(an)`, where `M = e^A/|B_r|` bounds `∫|ĥ|²`. -/
lemma err_integral (hr : 0 < r) (hrR : r ≤ R) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ (K : Set E) (h : E → ℝ), InH A r R K h → ∀ ξ : E, rad0 E A r R ≤ ‖ξ‖ → ‖ft h ξ‖ ≤ q)
    (m : ℕ) (Ks : Fin (m + 2) → Set E) (hs : Fin (m + 2) → E → ℝ)
    (hH : ∀ k, InH A r R (Ks k) (hs k)) :
    ∫ ξ, ‖∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
      ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * gI E 3 (π ^ 2 * sig E A r R * ((m : ℝ) + 1)) +
        (2 * π ^ 2 * R ^ 2) ^ 2 * gI E 4 (π ^ 2 * sig E A r R * ((m : ℝ) + 1))) +
      q ^ m * (exp A / vB E r) +
      exp (-(π ^ 2 * sig E A r R * rad0 E A r R ^ 2 * ((m : ℝ) + 2))) *
        gI E 0 (π ^ 2 * sig E A r R * ((m : ℝ) + 2)) := by
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨a, had⟩ : ∃ a, a = π ^ 2 * sig E A r R := ⟨_, rfl⟩
  obtain ⟨r0, hr0d⟩ : ∃ r0, r0 = rad0 E A r R := ⟨_, rfl⟩
  rw [← had, ← hr0d]
  have ha0 : 0 < a := by have := sig_pos (E := E) (A := A) hr hR; rw [had]; positivity
  have hb1 : 0 < a * ((m : ℝ) + 1) := by positivity
  have hb2 : 0 < a * ((m : ℝ) + 2) := by positivity
  have hPD : ∀ k, PD (exp A / vB E r) (hs k) := fun k =>
    ((hH k).pd hr.le).mono (div_le_div_of_nonneg_left (exp_pos _).le (vB_pos hr) (hH k).vol_ge)
  have hL2 : ∀ k, Integrable (fun ξ => ‖ft (hs k) ξ‖ ^ 2) ∧
      ∫ ξ, ‖ft (hs k) ξ‖ ^ 2 ≤ exp A / vB E r := fun k => by
    have := l2_bound (hPD k).int (hPD k).meas (hPD k).nonneg (hPD k).le
    rwa [(hPD k).one, mul_one] at this
  have i3 := integrable_pow_gauss (E := E) 3 hb1
  have i4 := integrable_pow_gauss (E := E) 4 hb1
  have i0 := integrable_rexp_neg_mul_sq_norm (E := E) hb2
  obtain ⟨T1, hT1d⟩ : ∃ T1 : E → ℝ, T1 = fun ξ => ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * (‖ξ‖ ^ 3 *
      exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2)) + (2 * π ^ 2 * R ^ 2) ^ 2 * (‖ξ‖ ^ 4 *
      exp (-(a * ((m : ℝ) + 1)) * ‖ξ‖ ^ 2))) := ⟨_, rfl⟩
  obtain ⟨T2, hT2d⟩ : ∃ T2 : E → ℝ,
      T2 = fun ξ => q ^ m * ((‖ft (hs 0) ξ‖ ^ 2 + ‖ft (hs 1) ξ‖ ^ 2) / 2) := ⟨_, rfl⟩
  obtain ⟨T3, hT3d⟩ : ∃ T3 : E → ℝ, T3 = fun ξ => exp (-(a * r0 ^ 2 * ((m : ℝ) + 2))) *
      exp (-(a * ((m : ℝ) + 2)) * ‖ξ‖ ^ 2) := ⟨_, rfl⟩
  have iT1 : Integrable T1 := hT1d ▸ ((i3.const_mul _).add (i4.const_mul _)).const_mul _
  have iT2 : Integrable T2 := hT2d ▸ (((hL2 0).1.add (hL2 1).1).div_const 2).const_mul _
  have iT3 : Integrable T3 := hT3d ▸ i0.const_mul _
  have hpt : ∀ ξ, ‖∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖ ≤
      T1 ξ + T2 ξ + T3 ξ := fun ξ => by
    have := err_pointwise hr hrR hq0 hq m Ks hs hH ξ
    rw [← had, ← hr0d] at this
    rw [hT1d, hT2d, hT3d]; exact this
  have e1 : ∫ ξ, T1 ξ = ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * gI E 3 (a * ((m : ℝ) + 1)) +
      (2 * π ^ 2 * R ^ 2) ^ 2 * gI E 4 (a * ((m : ℝ) + 1))) := by
    rw [hT1d, integral_const_mul, integral_add (i3.const_mul _) (i4.const_mul _),
      integral_const_mul, integral_const_mul, gI, gI]
  have e2 : ∫ ξ, T2 ξ ≤ q ^ m * (exp A / vB E r) := by
    rw [hT2d, integral_const_mul, integral_div, integral_add (hL2 0).1 (hL2 1).1]
    have h1 := (hL2 0).2
    have h2 := (hL2 1).2
    have hqm : 0 ≤ q ^ m := by positivity
    have : ((∫ ξ, ‖ft (hs 0) ξ‖ ^ 2) + ∫ ξ, ‖ft (hs 1) ξ‖ ^ 2) / 2 ≤ exp A / vB E r := by
      linarith
    exact mul_le_mul_of_nonneg_left this hqm
  have e3 : ∫ ξ, T3 ξ = exp (-(a * r0 ^ 2 * ((m : ℝ) + 2))) * gI E 0 (a * ((m : ℝ) + 2)) := by
    rw [hT3d, integral_const_mul, gI]
    simp only [pow_zero, one_mul]
  calc ∫ ξ, ‖∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)‖
      ≤ ∫ ξ, (T1 ξ + T2 ξ + T3 ξ) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => norm_nonneg _)
          ((iT1.add iT2).add iT3) (Eventually.of_forall hpt)
    _ = (∫ ξ, T1 ξ) + (∫ ξ, T2 ξ) + ∫ ξ, T3 ξ := by
        have h1 := integral_add (iT1.add iT2) iT3
        have h2 := integral_add iT1 iT2
        simp only [Pi.add_apply] at h1 h2
        rw [h1, h2]
    _ ≤ _ := by rw [e1, e3]; linarith

end ErrorBound

section RealBounds

lemma rpow_bound {x a p k : ℝ} (hx : 1 ≤ x) (ha : 0 < a) (hp : 0 ≤ p) :
    (x + 1) ^ p * (x + 1) * (a * x) ^ (-(2 * p + k) / 2) ≤
      2 ^ (p + 1) * a ^ (-(2 * p + k) / 2) * x ^ ((2 - k) / 2) := by
  have hx0 : 0 < x := by linarith
  rw [← rpow_add_one (by linarith : x + 1 ≠ 0), mul_rpow ha.le hx0.le]
  have h1 : (x + 1) ^ (p + 1) ≤ (2 * x) ^ (p + 1) :=
    rpow_le_rpow (by linarith) (by linarith) (by linarith)
  rw [mul_rpow (by norm_num) hx0.le] at h1
  have h2 : x ^ (p + 1) * x ^ (-(2 * p + k) / 2) = x ^ ((2 - k) / 2) := by
    rw [← rpow_add hx0]; congr 1; ring
  calc (x + 1) ^ (p + 1) * (a ^ (-(2 * p + k) / 2) * x ^ (-(2 * p + k) / 2))
      ≤ 2 ^ (p + 1) * x ^ (p + 1) * (a ^ (-(2 * p + k) / 2) * x ^ (-(2 * p + k) / 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 ^ (p + 1) * a ^ (-(2 * p + k) / 2) * (x ^ (p + 1) * x ^ (-(2 * p + k) / 2)) := by ring
    _ = _ := by rw [h2]

lemma rpow_cancel {x a p : ℝ} (hx : 0 < x) (ha : 0 < a) :
    x ^ p * (a * x) ^ (-p) = a ^ (-p) := by
  rw [mul_rpow ha.le hx.le, rpow_neg hx.le, rpow_neg ha.le]
  have : x ^ p ≠ 0 := (rpow_pos_of_pos hx p).ne'
  field_simp

lemma tendsto_natCast_add_rpow_neg {c y : ℝ} (hy : 0 < y) :
    Tendsto (fun m : ℕ => ((m : ℝ) + c) ^ (-y)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop hy).comp h1

lemma tendsto_pow_mul_geom {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (d : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 2) ^ d * q ^ m) atTop (𝓝 0) := by
  rcases hq0.lt_or_eq with hq0 | hq0
  · have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one d
      (by rw [abs_of_pos hq0]; exact hq)).comp (tendsto_add_atTop_nat 2)
    have h2 := h.div_const (q ^ 2)
    rw [zero_div] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp, Nat.cast_add, Nat.cast_ofNat]
    rw [pow_add]; field_simp
  · rw [← hq0]
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨1, fun m hm => ?_⟩)
    show (0 : ℝ) = ((m : ℝ) + 2) ^ d * 0 ^ m
    rw [zero_pow (by omega), mul_zero]

lemma tendsto_exp_neg_linear {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => exp (-(c * ((m : ℝ) + 2)))) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  refine tendsto_neg_atTop_atBot.comp ?_
  exact (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop).const_mul_atTop hc

end RealBounds

section Gaussian

/-- `φ_W(x) = ∫ e^{2πi⟨η, x⟩} e^{-2π² W(η)} dη`: the centred normal density whose covariance
has quadratic form `W`, written as the Fourier integral of its characteristic function. -/
def phiV (W : E → ℝ) (x : E) : ℂ := ∫ η, ex (-x) η * (exp (-(2 * π ^ 2 * W η)) : ℂ)

/-- `Q(ξ) = ∑ Σ_{h_k}(ξ)`, the quadratic form of `V = ∑ Σ_{h_k}`. -/
def Qf {n : ℕ} (hs : Fin n → E → ℝ) (ξ : E) : ℝ := ∑ k, varF (hs k) ξ

/-- `μ = ∑ m_{h_k}`. -/
def muF {n : ℕ} (hs : Fin n → E → ℝ) : E := ∑ k, Large.meanD (hs k)

lemma measurable_varF {h : E → ℝ} (hm : Measurable h) : Measurable (varF h) := by
  have : StronglyMeasurable (Function.uncurry fun (ξ y : E) => h y * ⟪y - Large.meanD h, ξ⟫ ^ 2) :=
    by
      refine Measurable.stronglyMeasurable ?_
      simp only [Function.uncurry_def]
      exact (hm.comp measurable_snd).mul (by fun_prop)
  exact this.integral_prod_right.measurable

lemma measurable_Qf {n : ℕ} {hs : Fin n → E → ℝ} (hm : ∀ k, Measurable (hs k)) :
    Measurable (Qf hs) := by
  unfold Qf
  exact Finset.measurable_sum _ fun k _ => measurable_varF (hm k)

lemma prod_ft_eq {n : ℕ} (hs : Fin n → E → ℝ) (ξ : E) :
    ∏ k, ft (hs k) ξ = ex (muF hs) ξ * ∏ k, cf (hs k) ξ := by
  simp_rw [ft_eq_ex_mul_cf, Finset.prod_mul_distrib, muF, ex_sum]

lemma prod_exp_eq {n : ℕ} (hs : Fin n → E → ℝ) (ξ : E) :
    ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ) = (exp (-(2 * π ^ 2 * Qf hs ξ)) : ℂ) := by
  rw [← Complex.ofReal_prod, ← Real.exp_sum, Qf, Finset.mul_sum, Finset.sum_neg_distrib]

variable {A r R : ℝ}

lemma Qf_ge (hr : 0 < r) {n : ℕ} {Ks : Fin n → Set E} {hs : Fin n → E → ℝ}
    (hH : ∀ k, InH A r R (Ks k) (hs k)) (ξ : E) : n * sig E A r R * ‖ξ‖ ^ 2 ≤ Qf hs ξ := by
  calc (n : ℝ) * sig E A r R * ‖ξ‖ ^ 2 = ∑ _k : Fin n, sig E A r R * ‖ξ‖ ^ 2 := by
        simp; ring
    _ ≤ Qf hs ξ := Finset.sum_le_sum fun k _ => (hH k).varF_ge hr ξ

lemma Qf_le (hr : 0 < r) {n : ℕ} {Ks : Fin n → Set E} {hs : Fin n → E → ℝ}
    (hH : ∀ k, InH A r R (Ks k) (hs k)) (ξ : E) : Qf hs ξ ≤ n * R ^ 2 * ‖ξ‖ ^ 2 := by
  calc Qf hs ξ ≤ ∑ _k : Fin n, R ^ 2 * ‖ξ‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => (hH k).varF_le hr.le ξ
    _ = n * R ^ 2 * ‖ξ‖ ^ 2 := by simp; ring

lemma integrable_gaussQ (hr : 0 < r) (hrR : r ≤ R) {n : ℕ} (hn : 0 < n) {Ks : Fin n → Set E}
    {hs : Fin n → E → ℝ} (hH : ∀ k, InH A r R (Ks k) (hs k)) (z : E) :
    Integrable fun ξ => ex z ξ * (exp (-(2 * π ^ 2 * Qf hs ξ)) : ℂ) := by
  have hR : 0 < R := hr.trans_le hrR
  have hσ := sig_pos (E := E) (A := A) hr hR
  have hb : 0 < 2 * π ^ 2 * (n * sig E A r R) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine Integrable.mono' (integrable_rexp_neg_mul_sq_norm (E := E) hb) ?_
    (Eventually.of_forall fun ξ => ?_)
  · have hQ := measurable_Qf (hs := hs) fun k => (hH k).meas
    exact (continuous_ex_right z).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (hQ.const_mul _).neg)).aestronglyMeasurable
  · rw [norm_mul, norm_ex, one_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le,
      exp_le_exp]
    have := Qf_ge hr hH ξ
    nlinarith [pi_pos]

/-- The Gaussian `G(z) = ∫ e^{2πi⟨ξ, z⟩} e^{-2π² Q(ξ)} dξ`. -/
def gaussG {n : ℕ} (hs : Fin n → E → ℝ) (z : E) : ℂ :=
  ∫ ξ, ex (-z) ξ * (exp (-(2 * π ^ 2 * Qf hs ξ)) : ℂ)

/-- Scaling: `φ_{V/n}(x) = n^{d/2} G(√n x)`. -/
lemma phiV_eq {n : ℕ} (hn : 0 < n) (hs : Fin n → E → ℝ) (x : E) :
    phiV (fun η => Qf hs η / n) x =
      ((n : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) * gaussG hs (Real.sqrt n • x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set c := Real.sqrt n
  have hc : 0 < c := Real.sqrt_pos.2 hn'
  have hc2 : c ^ 2 = n := Real.sq_sqrt hn'.le
  have h1 := Measure.integral_comp_smul (volume : Measure E)
    (fun η : E => ex (-x) η * (exp (-(2 * π ^ 2 * (Qf hs η / n))) : ℂ)) c
  have h2 : (fun ξ : E => ex (-x) (c • ξ) * (exp (-(2 * π ^ 2 * (Qf hs (c • ξ) / n))) : ℂ)) =
      fun ξ => ex (-(c • x)) ξ * (exp (-(2 * π ^ 2 * Qf hs ξ)) : ℂ) := by
    funext ξ
    have hQ : Qf hs (c • ξ) / n = Qf hs ξ := by
      rw [Qf, Qf, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [varF_smul, hc2]; field_simp
    rw [ex_smul_right, smul_neg, hQ]
  rw [h2] at h1
  rw [phiV, gaussG]
  have hd : (0 : ℝ) < c ^ Module.finrank ℝ E := by positivity
  rw [abs_of_pos (inv_pos.2 hd)] at h1
  have h3 : ∫ η, ex (-x) η * (exp (-(2 * π ^ 2 * (Qf hs η / n))) : ℂ) =
      (c ^ Module.finrank ℝ E : ℝ) • ∫ ξ, ex (-(c • x)) ξ * (exp (-(2 * π ^ 2 * Qf hs ξ)) : ℂ) := by
    rw [h1, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  rw [h3, Complex.real_smul]
  congr 2
  rw [show (n : ℝ) = c ^ 2 from hc2.symm, ← rpow_natCast c 2, ← rpow_mul hc.le, ← rpow_natCast]
  congr 1; push_cast; ring

end Gaussian

section LLT

variable {A r R : ℝ}

/-- The error bound of `err_integral`, for `m + 2` factors and the gap constant `q`. -/
def errB (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (A r R q : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 2) * ((2 * π * R) ^ 3 * gI E 3 (π ^ 2 * sig E A r R * ((m : ℝ) + 1)) +
      (2 * π ^ 2 * R ^ 2) ^ 2 * gI E 4 (π ^ 2 * sig E A r R * ((m : ℝ) + 1))) +
    q ^ m * (exp A / vB E r) +
    exp (-(π ^ 2 * sig E A r R * rad0 E A r R ^ 2 * ((m : ℝ) + 2))) *
      gI E 0 (π ^ 2 * sig E A r R * ((m : ℝ) + 2))

/-- Pointwise comparison of the convolution `f = h_1 * ⋯ * h_{m+2}` with the Gaussian `G` of
the same covariance: `|f(μ + z) - G(z)| ≤ errB m` for all `z`. -/
lemma llt_point (hr : 0 < r) (hrR : r ≤ R) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ (K : Set E) (h : E → ℝ), InH A r R K h → ∀ ξ : E, rad0 E A r R ≤ ‖ξ‖ → ‖ft h ξ‖ ≤ q)
    (m : ℕ) (Ks : Fin (m + 2) → Set E) (hs : Fin (m + 2) → E → ℝ)
    (hH : ∀ k, InH A r R (Ks k) (hs k)) (z : E) :
    ‖(convF (m + 1) hs (muF hs + z) : ℂ) - gaussG hs z‖ ≤ errB E A r R q m := by
  have hP : ∀ k, PD (⨆ j, exp A / volume.real (Ks j)) (hs k) := fun k =>
    ((hH k).pd hr.le).mono (le_ciSup (f := fun j => exp A / volume.real (Ks j))
      (Set.finite_range _).bddAbove k)
  have hI := integrable_prod_ft m hs hP
  have I1 : Integrable fun ξ => ex (-(muF hs + z)) ξ * ∏ k, ft (hs k) ξ :=
    Integrable.mono' hI.norm ((continuous_ex_right _).aestronglyMeasurable.mul
      hI.aestronglyMeasurable)
      (Eventually.of_forall fun ξ => by rw [norm_mul, norm_ex, one_mul])
  have I2 := integrable_gaussQ hr hrR (n := m + 2) (by omega) hH (-z)
  rw [convF_inversion m hs hP, gaussG, ← integral_sub I1 I2]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_
    (err_integral hr hrR hq0 hq m Ks hs hH))
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have h1 : ex (-muF hs) ξ * ex (muF hs) ξ = 1 := by
    rw [← ex_add, neg_add_cancel, ex_zero_left]
  have h2 : ex (-(muF hs + z)) ξ * ∏ k, ft (hs k) ξ -
      ex (-z) ξ * (exp (-(2 * π ^ 2 * Qf hs ξ)) : ℂ) =
      ex (-z) ξ * (∏ k, cf (hs k) ξ - ∏ k, (exp (-(2 * π ^ 2 * varF (hs k) ξ)) : ℂ)) := by
    rw [prod_ft_eq, prod_exp_eq, neg_add, ex_add]
    linear_combination (ex (-z) ξ * ∏ k, cf (hs k) ξ) * h1
  simp only [h2, norm_mul, norm_ex, one_mul]

lemma tendsto_gI_term {a : ℝ} (ha : 0 < a) (k : ℕ) (hk : 2 < k) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      (((m : ℝ) + 2) * gI E k (a * ((m : ℝ) + 1)))) atTop (𝓝 0) := by
  set p : ℝ := (Module.finrank ℝ E : ℝ) / 2 with hp
  have hb : ∀ m : ℕ, ((m : ℝ) + 2) ^ p * (((m : ℝ) + 2) * gI E k (a * ((m : ℝ) + 1))) ≤
      gI E k 1 * (2 ^ (p + 1) * a ^ (-(2 * p + k) / 2)) *
        ((m : ℝ) + 1) ^ (-(((k : ℝ) - 2) / 2)) := by
    intro m
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hx : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have h := rpow_bound (k := (k : ℝ)) hx ha (by positivity : 0 ≤ p)
    rw [gI_scale k (by positivity)]
    have e : (-((Module.finrank ℝ E : ℝ) + k) / 2) = -(2 * p + k) / 2 := by rw [hp]; ring
    have e2 : (m : ℝ) + 1 + 1 = (m : ℝ) + 2 := by ring
    have e3 : -(((k : ℝ) - 2) / 2) = ((2 : ℝ) - k) / 2 := by ring
    rw [e2] at h; rw [e, e3]
    calc _ = gI E k 1 * (((m : ℝ) + 2) ^ p * ((m : ℝ) + 2) *
          (a * ((m : ℝ) + 1)) ^ (-(2 * p + k) / 2)) := by ring
      _ ≤ gI E k 1 * (2 ^ (p + 1) * a ^ (-(2 * p + k) / 2) * ((m : ℝ) + 1) ^ (((2 : ℝ) - k) / 2)) :=
          mul_le_mul_of_nonneg_left h (gI_nonneg _ _)
      _ = _ := by ring
  refine squeeze_zero (fun m => mul_nonneg (by positivity)
    (mul_nonneg (by positivity) (gI_nonneg _ _))) hb ?_
  have hk' : (2 : ℝ) < k := by exact_mod_cast hk
  have := (tendsto_natCast_add_rpow_neg (c := 1) (y := ((k : ℝ) - 2) / 2)
    (by linarith)).const_mul (gI E k 1 * (2 ^ (p + 1) * a ^ (-(2 * p + k) / 2)))
  simpa using this

lemma tendsto_gI0_term {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      (exp (-(c * ((m : ℝ) + 2))) * gI E 0 (a * ((m : ℝ) + 2)))) atTop (𝓝 0) := by
  set p : ℝ := (Module.finrank ℝ E : ℝ) / 2 with hp
  have hb : ∀ m : ℕ, ((m : ℝ) + 2) ^ p * (exp (-(c * ((m : ℝ) + 2))) *
      gI E 0 (a * ((m : ℝ) + 2))) = gI E 0 1 * a ^ (-p) * exp (-(c * ((m : ℝ) + 2))) := by
    intro m
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    rw [gI_scale 0 (by positivity)]
    have e : (-((Module.finrank ℝ E : ℝ) + ((0 : ℕ) : ℝ)) / 2) = -p := by
      rw [hp]; push_cast; ring
    rw [e]
    have h := rpow_cancel (p := p) hm ha
    linear_combination (gI E 0 1 * exp (-(c * ((m : ℝ) + 2)))) * h
  simp_rw [hb]
  simpa using (tendsto_exp_neg_linear hc).const_mul (gI E 0 1 * a ^ (-p))

lemma tendsto_geom_term {q C : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (hC : 0 ≤ C) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * (q ^ m * C))
      atTop (𝓝 0) := by
  have hb : ∀ m : ℕ, ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * (q ^ m * C) ≤
      C * (((m : ℝ) + 2) ^ Module.finrank ℝ E * q ^ m) := by
    intro m
    have hm : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
    have h1 : ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) ≤
        ((m : ℝ) + 2) ^ Module.finrank ℝ E := by
      rw [← rpow_natCast]
      exact rpow_le_rpow_of_exponent_le hm (by
        have : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
        linarith)
    calc _ = C * (((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * q ^ m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h1 (pow_nonneg hq0 _)) hC
  refine squeeze_zero (fun m => mul_nonneg (by positivity)
    (mul_nonneg (pow_nonneg hq0 _) hC)) hb ?_
  simpa using (tendsto_pow_mul_geom hq0 hq (Module.finrank ℝ E)).const_mul C

/-- The sequence `ε_m = (m+2)^{d/2} errB m` of Lemma 112 (for `m + 2` factors). -/
def epsS (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (A r R q : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * errB E A r R q m

lemma tendsto_epsS (hr : 0 < r) (hrR : r ≤ R) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Tendsto (epsS E A r R q) atTop (𝓝 0) := by
  have hR : 0 < R := hr.trans_le hrR
  have hσ := sig_pos (E := E) (A := A) hr hR
  have hr0 := rad0_pos (E := E) (A := A) hr hR
  have ha : 0 < π ^ 2 * sig E A r R := by positivity
  have hc : 0 < π ^ 2 * sig E A r R * rad0 E A r R ^ 2 := by positivity
  have hC : 0 ≤ exp A / vB E r := (div_pos (exp_pos _) (vB_pos hr)).le
  have h := (((tendsto_gI_term (E := E) ha 3 (by norm_num)).const_mul ((2 * π * R) ^ 3)).add
    ((tendsto_gI_term (E := E) ha 4 (by norm_num)).const_mul ((2 * π ^ 2 * R ^ 2) ^ 2))).add
    ((tendsto_geom_term (E := E) hq0 hq hC).add (tendsto_gI0_term (E := E) ha hc))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun m => ?_
  simp only [epsS, errB]
  ring

/-- **Lemma 112, first part** (uniform local limit theorem, with `n = m + 2` factors).
There is a sequence `ε_m → 0`, depending only on `E`, `A`, `r`, `R`, such that for all
densities `h_1, …, h_n` in `𝓗(A, r, R)` and all `x`,
`|n^{d/2} f(μ + √n x) - φ_{V/n}(x)| ≤ ε_m`, where `f = h_1 * ⋯ * h_n`, `μ = ∑ m_{h_k}`,
`V = ∑ Σ_{h_k}`, and `φ_{V/n}` is the centred normal density of covariance `V/n`, written as
the Fourier integral `phiV`. -/
theorem llt_eps (hr : 0 < r) (hrR : r ≤ R) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ (m : ℕ) (Ks : Fin (m + 2) → Set E)
      (hs : Fin (m + 2) → E → ℝ), (∀ k, InH A r R (Ks k) (hs k)) → ∀ x : E,
      ‖((((m + 2 : ℕ) : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) *
          convF (m + 1) hs (muF hs + Real.sqrt ((m + 2 : ℕ) : ℝ) • x) -
        phiV (fun η => Qf hs η / ((m + 2 : ℕ) : ℝ)) x‖ ≤ ε m := by
  obtain ⟨q, hq1, hq, hgap⟩ := exists_gap (E := E) (A := A) hr hrR
  have hq0 : 0 ≤ q := by linarith
  refine ⟨epsS E A r R q, tendsto_epsS hr hrR hq0 hq, fun m Ks hs hH x => ?_⟩
  rw [phiV_eq (by omega), ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), epsS]
  push_cast
  exact mul_le_mul_of_nonneg_left (llt_point hr hrR hq0 hgap m Ks hs hH _) (by positivity)

lemma norm_ex_sub_one_le (y ξ : E) : ‖ex y ξ - 1‖ ≤ 2 * π * (‖y‖ * ‖ξ‖) := by
  have e : ex y ξ = Complex.exp (Complex.I * ((-(2 * π * ⟪y, ξ⟫) : ℝ) : ℂ)) := by
    rw [ex]; congr 1; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm y ξ) (by positivity)

lemma integrable_expQ (hr : 0 < r) (hrR : r ≤ R) {n : ℕ} (hn : 0 < n) {Ks : Fin n → Set E}
    {hs : Fin n → E → ℝ} (hH : ∀ k, InH A r R (Ks k) (hs k)) :
    Integrable fun ξ => exp (-(2 * π ^ 2 * Qf hs ξ)) := by
  have hR : 0 < R := hr.trans_le hrR
  have hσ := sig_pos (E := E) (A := A) hr hR
  have hb : 0 < 2 * π ^ 2 * (n * sig E A r R) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine Integrable.mono' (integrable_rexp_neg_mul_sq_norm (E := E) hb) ?_
    (Eventually.of_forall fun ξ => ?_)
  · have hQ := measurable_Qf (hs := hs) fun k => (hH k).meas
    exact (Real.measurable_exp.comp (hQ.const_mul _).neg).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_exp]
    have := Qf_ge hr hH ξ
    nlinarith [pi_pos]

lemma gaussG_zero {n : ℕ} (hs : Fin n → E → ℝ) :
    gaussG hs 0 = ((∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ)) : ℝ) : ℂ) := by
  rw [gaussG, ← integral_complex_ofReal]
  congr 1; funext ξ
  rw [neg_zero, ex_zero_left, one_mul]

/-- `|G(z) - G(0)| ≤ 2π |z| I_1(2π² n σ)`. -/
lemma gaussG_sub (hr : 0 < r) (hrR : r ≤ R) {n : ℕ} (hn : 0 < n) {Ks : Fin n → Set E}
    {hs : Fin n → E → ℝ} (hH : ∀ k, InH A r R (Ks k) (hs k)) (z : E) :
    ‖gaussG hs z - gaussG hs 0‖ ≤
      2 * π * ‖z‖ * gI E 1 (2 * π ^ 2 * (n * sig E A r R)) := by
  have hR : 0 < R := hr.trans_le hrR
  have hσ := sig_pos (E := E) (A := A) hr hR
  have hb : 0 < 2 * π ^ 2 * (n * sig E A r R) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [gaussG, gaussG, ← integral_sub (integrable_gaussQ hr hrR hn hH (-z))
    (integrable_gaussQ hr hrR hn hH (-0)), gI, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_pow_gauss 1 hb).const_mul (2 * π * ‖z‖))
    (Eventually.of_forall fun ξ => ?_)
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, neg_zero,
    ex_zero_left]
  have h1 := norm_ex_sub_one_le (-z) ξ
  rw [norm_neg] at h1
  have h2 : exp (-(2 * π ^ 2 * Qf hs ξ)) ≤ exp (-(2 * π ^ 2 * (n * sig E A r R)) * ‖ξ‖ ^ 2) := by
    rw [exp_le_exp]
    have := Qf_ge hr hH ξ
    nlinarith [pi_pos]
  calc _ ≤ 2 * π * (‖z‖ * ‖ξ‖) * exp (-(2 * π ^ 2 * (n * sig E A r R)) * ‖ξ‖ ^ 2) :=
        mul_le_mul h1 h2 (exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Lower bound `n^{d/2} G(0) ≥ (2π²R²)^{-d/2} I_0(1)`. -/
lemma gauss0_ge (hr : 0 < r) (hrR : r ≤ R) {n : ℕ} (hn : 0 < n) {Ks : Fin n → Set E}
    {hs : Fin n → E → ℝ} (hH : ∀ k, InH A r R (Ks k) (hs k)) :
    (2 * π ^ 2 * R ^ 2) ^ (-((Module.finrank ℝ E : ℝ) / 2)) * gI E 0 1 ≤
      (n : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) * ∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ)) := by
  have hR : 0 < R := hr.trans_le hrR
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < 2 * π ^ 2 * R ^ 2 := by positivity
  have hb : 0 < 2 * π ^ 2 * R ^ 2 * n := by positivity
  have h1 : gI E 0 (2 * π ^ 2 * R ^ 2 * n) ≤ ∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ)) := by
    rw [gI]
    refine integral_mono (by simpa using integrable_rexp_neg_mul_sq_norm (E := E) hb)
      (integrable_expQ hr hrR hn hH) fun ξ => ?_
    simp only [pow_zero, one_mul]
    rw [exp_le_exp]
    have := Qf_le hr hH ξ
    nlinarith [pi_pos]
  rw [gI_scale 0 hb] at h1
  have e : -((Module.finrank ℝ E : ℝ) + ((0 : ℕ) : ℝ)) / 2 = -((Module.finrank ℝ E : ℝ) / 2) := by
    push_cast; ring
  rw [e] at h1
  have h2 := rpow_cancel (p := (Module.finrank ℝ E : ℝ) / 2) hn' hc
  calc _ = (n : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        ((2 * π ^ 2 * R ^ 2 * n) ^ (-((Module.finrank ℝ E : ℝ) / 2)) * gI E 0 1) := by
        rw [← h2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

lemma gI0_pos : 0 < gI E 0 1 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1) one_pos
  rw [gI]
  simp only [pow_zero, one_mul]
  rw [show (fun ξ : E => exp (-1 * ‖ξ‖ ^ 2)) = fun ξ : E => exp (-(1 : ℝ) * ‖ξ‖ ^ 2) from rfl, h]
  positivity

lemma tendsto_gI1_term {b : ℝ} (hb : 0 < b) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      gI E 1 (b * ((m : ℝ) + 2))) atTop (𝓝 0) := by
  have h : ∀ m : ℕ, ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      gI E 1 (b * ((m : ℝ) + 2)) = gI E 1 1 * b ^ (-((Module.finrank ℝ E : ℝ) + ((1 : ℕ) : ℝ)) / 2)
        * ((m : ℝ) + 2) ^ (-(1 / 2 : ℝ)) := by
    intro m
    have hx : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    rw [gI_scale 1 (by positivity), mul_rpow hb.le hx.le]
    have e : ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        ((m : ℝ) + 2) ^ (-((Module.finrank ℝ E : ℝ) + ((1 : ℕ) : ℝ)) / 2) =
        ((m : ℝ) + 2) ^ (-(1 / 2 : ℝ)) := by
      rw [← rpow_add hx]; congr 1; push_cast; ring
    linear_combination (gI E 1 1 * b ^ (-((Module.finrank ℝ E : ℝ) + ((1 : ℕ) : ℝ)) / 2)) * e
  simp_rw [h]
  simpa using (tendsto_natCast_add_rpow_neg (c := 2) (y := 1 / 2) (by norm_num)).const_mul
    (gI E 1 1 * b ^ (-((Module.finrank ℝ E : ℝ) + ((1 : ℕ) : ℝ)) / 2))

/-- Near the mean: `|n^{d/2} f(μ + z) - n^{d/2} G(0)| ≤ ε_m + 2π|z| n^{d/2} I_1(2π²σ n)`. -/
lemma llt_near (hr : 0 < r) (hrR : r ≤ R) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ (K : Set E) (h : E → ℝ), InH A r R K h → ∀ ξ : E, rad0 E A r R ≤ ‖ξ‖ → ‖ft h ξ‖ ≤ q)
    (m : ℕ) (Ks : Fin (m + 2) → Set E) (hs : Fin (m + 2) → E → ℝ)
    (hH : ∀ k, InH A r R (Ks k) (hs k)) (z : E) :
    |((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * convF (m + 1) hs (muF hs + z) -
        ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * ∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ))| ≤
      epsS E A r R q m + 2 * π * ‖z‖ * (((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        gI E 1 (2 * π ^ 2 * sig E A r R * ((m : ℝ) + 2))) := by
  have h1 := llt_point hr hrR hq0 hq m Ks hs hH z
  have h2 := gaussG_sub hr hrR (n := m + 2) (by omega) hH z
  rw [gaussG_zero] at h2
  have h3 : |convF (m + 1) hs (muF hs + z) - ∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ))| ≤
      errB E A r R q m + 2 * π * ‖z‖ * gI E 1 (2 * π ^ 2 * sig E A r R * ((m : ℝ) + 2)) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub]
    have e : 2 * π ^ 2 * sig E A r R * ((m : ℝ) + 2) =
        2 * π ^ 2 * (((m + 2 : ℕ) : ℝ) * sig E A r R) := by push_cast; ring
    rw [e]
    calc _ = ‖((convF (m + 1) hs (muF hs + z) : ℂ) - gaussG hs z) +
          (gaussG hs z - ((∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ)) : ℝ) : ℂ))‖ := by ring_nf
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity), epsS]
  calc _ ≤ ((m : ℝ) + 2) ^ ((Module.finrank ℝ E : ℝ) / 2) * (errB E A r R q m +
        2 * π * ‖z‖ * gI E 1 (2 * π ^ 2 * sig E A r R * ((m : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- **Lemma 112, second part.** For every `ρ` there are `N` and `δ_m → 0`, depending only
on `E`, `A`, `r`, `R`, `ρ`, such that for `m ≥ N`, densities `h_1, …, h_{m+2}` in `𝓗` and
`|y - μ|, |y' - μ| ≤ ρ`: `f(y') > 0` and `|f(y)/f(y') - 1| ≤ δ_m`. -/
theorem llt_delta (hr : 0 < r) (hrR : r ≤ R) (ρ : ℝ) :
    ∃ (N : ℕ) (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) ∧ ∀ m ≥ N, ∀ (Ks : Fin (m + 2) → Set E)
      (hs : Fin (m + 2) → E → ℝ), (∀ k, InH A r R (Ks k) (hs k)) → ∀ y y' : E,
      ‖y - muF hs‖ ≤ ρ → ‖y' - muF hs‖ ≤ ρ →
      0 < convF (m + 1) hs y' ∧
        |convF (m + 1) hs y / convF (m + 1) hs y' - 1| ≤ δ m := by
  obtain ⟨q, hq1, hq, hgap⟩ := exists_gap (E := E) (A := A) hr hrR
  have hq0 : 0 ≤ q := by linarith
  have hR : 0 < R := hr.trans_le hrR
  have hσ := sig_pos (E := E) (A := A) hr hR
  set p : ℝ := (Module.finrank ℝ E : ℝ) / 2 with hp
  set c0 : ℝ := (2 * π ^ 2 * R ^ 2) ^ (-p) * gI E 0 1 with hc0
  have hc0p : 0 < c0 := mul_pos (by positivity) gI0_pos
  set η : ℕ → ℝ := fun m => epsS E A r R q m + 2 * π * ρ * (((m : ℝ) + 2) ^ p *
    gI E 1 (2 * π ^ 2 * sig E A r R * ((m : ℝ) + 2))) with hη
  have hηt : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_epsS (E := E) (A := A) hr hrR hq0 hq).add
      ((tendsto_gI1_term (E := E) (b := 2 * π ^ 2 * sig E A r R) (by positivity)).const_mul
        (2 * π * ρ))
    simpa using this
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hηt.eventually (gt_mem_nhds (half_pos hc0p)))
  refine ⟨N, fun m => 4 * η m / c0, by simpa using (hηt.const_mul 4).div_const c0,
    fun m hm Ks hs hH y y' hy hy' => ?_⟩
  have hηm : η m < c0 / 2 := hN m hm
  have hgI1 : 0 ≤ ((m : ℝ) + 2) ^ p * gI E 1 (2 * π ^ 2 * sig E A r R * ((m : ℝ) + 2)) :=
    mul_nonneg (by positivity) (gI_nonneg _ _)
  have key : ∀ w : E, ‖w - muF hs‖ ≤ ρ →
      |((m : ℝ) + 2) ^ p * convF (m + 1) hs w -
        ((m : ℝ) + 2) ^ p * ∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ))| ≤ η m := by
    intro w hw
    have h := llt_near hr hrR hq0 hgap m Ks hs hH (w - muF hs)
    rw [add_sub_cancel] at h
    refine h.trans ?_
    simp only [hη]
    have := mul_le_mul_of_nonneg_right hw hgI1
    nlinarith [pi_pos]
  have hlow : c0 ≤ ((m : ℝ) + 2) ^ p * ∫ ξ, exp (-(2 * π ^ 2 * Qf hs ξ)) := by
    have := gauss0_ge hr hrR (n := m + 2) (by omega) hH
    push_cast at this
    simpa [hc0, hp] using this
  have k1 := abs_le.1 (key y hy)
  have k2 := abs_le.1 (key y' hy')
  have hpos : 0 < ((m : ℝ) + 2) ^ p := by positivity
  set F := ((m : ℝ) + 2) ^ p * convF (m + 1) hs y with hF
  set F' := ((m : ℝ) + 2) ^ p * convF (m + 1) hs y' with hF'
  have hF'pos : c0 / 2 ≤ F' := by linarith
  have hf' : 0 < convF (m + 1) hs y' := by
    by_contra hc
    have : F' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le (not_lt.1 hc)
    linarith
  refine ⟨hf', ?_⟩
  have hratio : convF (m + 1) hs y / convF (m + 1) hs y' = F / F' := by
    rw [hF, hF', mul_div_mul_left _ _ hpos.ne']
  have hF'0 : 0 < F' := by linarith
  rw [hratio, div_sub_one hF'0.ne', abs_div, abs_of_pos hF'0, div_le_iff₀ hF'0]
  have hd : |F - F'| ≤ 2 * η m := by rw [abs_le]; constructor <;> linarith
  have h2 : 2 * η m ≤ 4 * η m / c0 * F' := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0p]
    have : 0 ≤ η m := by linarith [abs_nonneg (F - F'), hd]
    nlinarith
  linarith

/-- The densities of `𝒢_d(A, L, r, R)` (with the canonical volume of `E`) lie in `𝓗(A, r, R)`. -/
lemma InH.of_InG {L : ℝ} {K : Set E} {g : E → ℝ} (hG : Large.InG A L r R K g) :
    InH A r R K g :=
  ⟨hG.compact, hG.convex, hG.ball, hG.diam, hG.meas, hG.zero, hG.int, hG.low, hG.up⟩

end LLT

end Mixes.Thm113
