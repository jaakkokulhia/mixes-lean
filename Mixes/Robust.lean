import Mixes.Large
import Mixes.Room
import Mixes.SymmCor
import Mixes.ScaledB
import Mixes.Ball
import Mixes.Sphere

/-!
# Robust complete mixability and stability (Definition 90, Theorem 91, Corollary 93)

Item M1k of `mixes/LEAN_VERIFICATION_PRIORITIES.md` (`st:def:robust`, `st:thm:open`,
`st:cor:open` in `mixes/main.tex`).

**The kernel argument** (used in Theorem 91 and in Proposition 106):
* `smooth_rep`, `pexider_local`: the almost-everywhere Pexider equation
  `f a + g b = k (a + b)` on a product of balls forces `f` to be affine (smoothing by a bump
  convolution, then the derivative is constant);
* `glue_affine`: locally affine almost everywhere on a connected open set gives one affine
  function;
* `kernelAffine_of_room`, `kernelAffine_of_asym`: `Large.KernelAffine λ K` for the Lebesgue
  measure `λ = lebTuples` on `𝒯_n(K)`, `n ≥ 3`, under room in the interior, resp.
  `as(K) < n - 1` (Lemma 89);
* `prop106_unique_of_asym`: Proposition 106 (uniqueness of `h`) without the hypothesis
  `KernelAffine`.

**Theorem 91, functional-analytic core** (abstract Hilbert space `H`): `spectral_gap` (spectral
gap of `G₀ = M + C`, `M` bounded below, `C` compact, by a norm argument instead of weak limits),
`solve_of_gap` (Lax–Milgram on `Vᗮ`), `linear_correction` (stability under a perturbation of
size `γ₀/2` and `‖φ‖ ≤ 2γ₀⁻¹‖h‖`). The identification of the paper's operator `G` on `L²(K̃)` as a
multiplication plus a Hilbert–Schmidt (compact) operator, the measures `β₁`, `β₂`, `η_φ`, the
`L^∞` bound and the Hausdorff estimates of the proof are **not** formalised; Theorem 91 itself
enters Corollary 93 as the hypothesis `Thm91Stmt`.

**Definition 90 and Corollary 93**: `tuplesRho`, `RobustlyCM` (Definition 90), `robust_of_symm`
(Lemma 92 gives robustness), `Thm91Stmt` (the statement of Theorem 91), `BMClose` (Banach–Mazur
closeness), `stable_of_thm91` (the reduction from the Banach–Mazur distance to the Hausdorff
distance after centring), `cor93a` (planar bodies with an affine symmetry of order `3`, in
`ℝ × ℝ`), `cor93b` (the disc, in `ℂ`), `ball_robust` and `cor93c` (the ball in every dimension
`≥ 2`, with Proposition 52 and the cited `Ball.SphereUniqueness`).
-/

open MeasureTheory Set Metric RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes.Robust

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-! ## The functional equation: smoothing and the local Pexider equation -/

section Pexider

/-- Smoothing: if `f a + g b = k (a + b)` for almost every `a` near `a₀` and almost every `b` near
`b₀`, then `f` agrees almost everywhere near `a₀` with a `C¹` function (the convolution of `k`
with a smooth bump, minus a constant). -/
lemma smooth_rep {f g k : E → ℝ} (hg : LocallyIntegrable g volume)
    (hk : LocallyIntegrable k volume) {a0 b0 : E} {r : ℝ} (hr : 0 < r)
    (H : ∀ᵐ a, a ∈ ball a0 r → ∀ᵐ b, b ∈ ball b0 r → f a + g b = k (a + b)) :
    ∃ F : E → ℝ, ContDiff ℝ 1 F ∧ ∀ᵐ a, a ∈ ball a0 r → f a = F a := by
  let ψ : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set w := ψ.normed (volume : Measure E) with hw
  set Cg := ∫ b, w (b - b0) * g b with hCg
  refine ⟨fun a => (convolution w k (ContinuousLinearMap.lsmul ℝ ℝ) volume) (a + b0) - Cg, ?_, ?_⟩
  · exact ((ψ.hasCompactSupport_normed.contDiff_convolution_left _ ψ.contDiff_normed hk).comp
      (contDiff_id.add contDiff_const)).sub contDiff_const
  filter_upwards [H] with a ha hab
  have hb := ha hab
  have hconv : (convolution w k (ContinuousLinearMap.lsmul ℝ ℝ) volume) (a + b0) =
      ∫ b, w (b - b0) * k (a + b) := by
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← integral_sub_left_eq_self (fun b => w (b - b0) * k (a + b)) volume b0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [show b0 - t - b0 = -t by abel, hw, ψ.normed_neg, show a + (b0 - t) = a + b0 - t by abel]
  have hsupp : ∀ b, b ∉ ball b0 r → w (b - b0) = 0 := fun b hb' => by
    rw [← Function.notMem_support, ψ.support_normed_eq]
    intro hm
    apply hb'
    rw [mem_ball, dist_eq_norm]
    rw [mem_ball, dist_zero_right] at hm
    have : ψ.rOut = r / 2 := rfl
    linarith
  have hwi : Integrable (fun b => w (b - b0)) volume :=
    (ψ.integrable_normed).comp_sub_right b0
  have hcs : HasCompactSupport (fun b => w (b - b0)) :=
    ψ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subRight b0)
  have hwg : Integrable (fun b => w (b - b0) * g b) volume := by
    have := hg.integrable_smul_left_of_hasCompactSupport
      ((ψ.contDiff_normed (n := 0)).continuous.comp (continuous_id.sub continuous_const)) hcs
    simpa [smul_eq_mul] using this
  have h1 : ∫ b, w (b - b0) * k (a + b) = ∫ b, (w (b - b0) * f a + w (b - b0) * g b) := by
    refine integral_congr_ae ?_
    filter_upwards [hb] with b hb'
    by_cases hbm : b ∈ ball b0 r
    · rw [← hb' hbm]; ring
    · rw [hsupp b hbm]; ring
  have h2 : ∫ b, w (b - b0) = 1 := by
    rw [integral_sub_right_eq_self (fun b => w b) b0]
    exact ψ.integral_normed
  show f a = _ - Cg
  rw [hconv, h1, integral_add (hwi.mul_const _) hwg, integral_mul_const, h2, ← hCg]
  ring

/-- **The local Pexider equation.** If `f a + g b = k (a + b)` for almost every `(a, b)` in
`ball a₀ r × ball b₀ r`, with `f`, `g`, `k` locally integrable, then `f` is almost everywhere on
`ball a₀ (r/2)` equal to an affine function. Proof: by `smooth_rep`, `f` and `g` agree with `C¹`
functions `F`, `G`; then `F (a + h) + G (b - h) = F a + G b` everywhere, so the derivative of `F`
is constant. -/
theorem pexider_local {f g k : E → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (hk : LocallyIntegrable k volume) {a0 b0 : E} {r : ℝ}
    (hr : 0 < r)
    (H : ∀ᵐ p ∂(volume : Measure E).prod volume, p.1 ∈ ball a0 r → p.2 ∈ ball b0 r →
      f p.1 + g p.2 = k (p.1 + p.2)) :
    ∃ (c : ℝ) (v : E), ∀ᵐ x, x ∈ ball a0 (r / 2) → f x = c + ⟪v, x⟫ := by
  have H1 : ∀ᵐ a, a ∈ ball a0 r → ∀ᵐ b, b ∈ ball b0 r → f a + g b = k (a + b) := by
    filter_upwards [Measure.ae_ae_of_ae_prod H] with a ha h1
    filter_upwards [ha] with b hb h2 using hb h1 h2
  have H2 : ∀ᵐ b, b ∈ ball b0 r → ∀ᵐ a, a ∈ ball a0 r → g b + f a = k (b + a) := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure E))
      (ν := (volume : Measure E))).quasiMeasurePreserving.ae H
    filter_upwards [Measure.ae_ae_of_ae_prod this] with b hb h1
    filter_upwards [hb] with a ha h2
    simp only [Prod.fst_swap, Prod.snd_swap] at ha
    rw [add_comm, add_comm b]; exact ha h2 h1
  obtain ⟨F, hFc, hF⟩ := smooth_rep hg hk hr H1
  obtain ⟨G, hGc, hG⟩ := smooth_rep hf hk hr H2
  have HP : ∀ᵐ p ∂(volume : Measure E).prod volume, p.1 ∈ ball a0 r → p.2 ∈ ball b0 r →
      F p.1 + G p.2 = k (p.1 + p.2) := by
    filter_upwards [H, Measure.quasiMeasurePreserving_fst.ae hF,
      Measure.quasiMeasurePreserving_snd.ae hG] with p hp h1 h2 ha hb
    rw [← h1 ha, ← h2 hb]; exact hp ha hb
  have hball : ∀ {x y : E} {h : E}, x ∈ ball y (r / 2) → ‖h‖ < r / 2 →
      x + h ∈ ball y r ∧ x - h ∈ ball y r ∧ x ∈ ball y r := by
    intro x y h hx hh
    rw [mem_ball, dist_eq_norm] at hx
    refine ⟨?_, ?_, ?_⟩ <;> rw [mem_ball, dist_eq_norm]
    · calc ‖x + h - y‖ = ‖(x - y) + h‖ := by abel_nf
        _ ≤ ‖x - y‖ + ‖h‖ := norm_add_le _ _
        _ < r := by linarith
    · calc ‖x - h - y‖ = ‖(x - y) - h‖ := by abel_nf
        _ ≤ ‖x - y‖ + ‖h‖ := norm_sub_le _ _
        _ < r := by linarith
    · linarith
  have hshift : ∀ h : E, ‖h‖ < r / 2 → ∀ a ∈ ball a0 (r / 2), ∀ b ∈ ball b0 (r / 2),
      F (a + h) + G (b - h) = F a + G b := by
    intro h hh
    have hmp : MeasurePreserving (Prod.map (· + h) (· - h)) ((volume : Measure E).prod volume)
        (volume.prod volume) :=
      (measurePreserving_add_right volume h).prod (measurePreserving_sub_right volume h)
    have HP' := hmp.quasiMeasurePreserving.ae HP
    have hae : (fun p : E × E => F (p.1 + h) + G (p.2 - h)) =ᵐ[((volume : Measure E).prod
        volume).restrict (ball a0 (r / 2) ×ˢ ball b0 (r / 2))] (fun p => F p.1 + G p.2) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_ball.prod measurableSet_ball)]
      filter_upwards [HP, HP'] with p h1 h2 hp
      simp only [Prod.map_fst, Prod.map_snd] at h2
      rw [h1 (hball hp.1 hh).2.2 (hball hp.2 hh).2.2, h2 (hball hp.1 hh).1 (hball hp.2 hh).2.1]
      congr 1; abel
    have hcont : Continuous F := hFc.continuous
    have hcontG : Continuous G := hGc.continuous
    have := Measure.eqOn_open_of_ae_eq hae (isOpen_ball.prod isOpen_ball)
      ((hcont.comp (continuous_fst.add continuous_const)).add
        (hcontG.comp (continuous_snd.sub continuous_const))).continuousOn
      ((hcont.comp continuous_fst).add (hcontG.comp continuous_snd)).continuousOn
    intro a ha b hb
    exact this (show (a, b) ∈ ball a0 (r / 2) ×ˢ ball b0 (r / 2) from ⟨ha, hb⟩)
  have hFd : Differentiable ℝ F := hFc.differentiable one_ne_zero
  have hb0 : b0 ∈ ball b0 (r / 2) := mem_ball_self (by linarith)
  have ha0 : a0 ∈ ball a0 (r / 2) := mem_ball_self (by linarith)
  -- the derivative of `F` is constant on `ball a₀ (r/2)`
  have hder : ∀ x ∈ ball a0 (r / 2), fderiv ℝ F x = fderiv ℝ F a0 := by
    intro x hx
    set h := x - a0 with hh
    have hhn : ‖h‖ < r / 2 := by rw [hh, ← dist_eq_norm]; exact hx
    have hD : (fun y => F (y + h) - F y) =ᶠ[nhds a0] fun _ => G b0 - G (b0 - h) := by
      filter_upwards [isOpen_ball.mem_nhds ha0] with y hy
      have := hshift h hhn y hy b0 hb0
      linarith
    have h0 := hD.fderiv_eq (𝕜 := ℝ)
    have hd1 : DifferentiableAt ℝ (fun y => F (y + h)) a0 :=
      (hFd (a0 + h)).comp a0 (differentiableAt_id.add_const h)
    rw [fderiv_const_apply, fderiv_fun_sub hd1 (hFd a0), fderiv_comp_add_right] at h0
    have : a0 + h = x := by rw [hh]; abel
    rw [this] at h0
    exact sub_eq_zero.1 h0
  set L0 := fderiv ℝ F a0
  have hconst : ∀ x ∈ ball a0 (r / 2), F x - L0 x = F a0 - L0 a0 := by
    intro x hx
    refine IsOpen.is_const_of_fderiv_eq_zero (f := fun y => F y - L0 y) isOpen_ball
      (convex_ball _ _).isPreconnected ((hFd.sub L0.differentiable).differentiableOn)
      (fun y hy => ?_) hx ha0
    simp only [Pi.zero_apply]
    rw [fderiv_fun_sub (hFd y) L0.differentiableAt, ContinuousLinearMap.fderiv, hder y hy,
      sub_self]
  refine ⟨F a0 - L0 a0, (InnerProductSpace.toDual ℝ E).symm L0, ?_⟩
  filter_upwards [hF] with x hx hxb
  rw [hx (ball_subset_ball (by linarith) hxb), InnerProductSpace.toDual_symm_apply]
  have := hconst x hxb
  linarith

/-- Two affine functions that agree on a nonempty open set are equal. -/
lemma affine_eq_of_open {U : Set E} (hU : IsOpen U) {y : E} (hy : y ∈ U) {c c' : ℝ} {v v' : E}
    (h : ∀ x ∈ U, c + ⟪v, x⟫ = c' + ⟪v', x⟫) : c = c' ∧ v = v' := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
  set w := v - v'
  set t := ε / (2 * (‖w‖ + 1))
  have ht : 0 < t := div_pos hε (by positivity)
  have hmem : y + t • w ∈ U := by
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have h1 : t * ‖w‖ ≤ t * (‖w‖ + 1) := by nlinarith [norm_nonneg w]
    have h2 : t * (‖w‖ + 1) = ε / 2 := by
      simp only [t]; field_simp
    linarith
  have e1 := h y hy
  have e2 := h _ hmem
  simp only [inner_add_right, inner_smul_right] at e2
  have hw : t * ⟪w, w⟫ = 0 := by
    simp only [w, inner_sub_left]; linarith
  have hw0 : w = 0 := by
    have := (mul_eq_zero.1 hw).resolve_left ht.ne'
    exact inner_self_eq_zero.1 this
  have hv : v = v' := sub_eq_zero.1 hw0
  subst hv
  exact ⟨by linarith, rfl⟩

/-- **Gluing.** A function that is, near every point of a connected open set `D`, almost
everywhere equal to an affine function, is almost everywhere on `D` equal to one affine
function. -/
theorem glue_affine {D : Set E} (hD : IsOpen D) (hDc : IsPreconnected D) {f : E → ℝ}
    (hloc : ∀ x ∈ D, ∃ r > 0, ∃ (c : ℝ) (v : E), ∀ᵐ y, y ∈ ball x r → f y = c + ⟪v, y⟫) :
    ∃ (c : ℝ) (v : E), ∀ᵐ y ∂(volume.restrict D), f y = c + ⟪v, y⟫ := by
  rcases D.eq_empty_or_nonempty with hDe | ⟨x0, hx0⟩
  · exact ⟨0, 0, by simp [hDe]⟩
  have hloc' : ∀ x, ∃ r : ℝ, 0 < r ∧ ∃ cv : ℝ × E, x ∈ D →
      ball x r ⊆ D ∧ ∀ᵐ y, y ∈ ball x r → f y = cv.1 + ⟪cv.2, y⟫ := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨r, hr, c, v, hcv⟩ := hloc x hx
      obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD x hx
      refine ⟨min r ε, lt_min hr hε, (c, v), fun _ => ⟨(ball_subset_ball (min_le_right _ _)).trans
        hεD, ?_⟩⟩
      filter_upwards [hcv] with y hy hy' using hy (ball_subset_ball (min_le_left _ _) hy')
    · exact ⟨1, one_pos, (0, 0), fun h => absurd h hx⟩
  choose R hR P hP using hloc'
  -- `P` is locally constant on `D`
  have hloc_eq : ∀ x ∈ D, ∀ y ∈ D, y ∈ ball x (R x) → P y = P x := by
    intro x hx y hy hyx
    set W := ball x (R x) ∩ ball y (R y)
    have hW : IsOpen W := isOpen_ball.inter isOpen_ball
    have hyW : y ∈ W := ⟨hyx, mem_ball_self (hR y)⟩
    have hae : (fun z => (P y).1 + ⟪(P y).2, z⟫) =ᵐ[volume.restrict W]
        fun z => (P x).1 + ⟪(P x).2, z⟫ := by
      rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)]
      filter_upwards [(hP x hx).2, (hP y hy).2] with z h1 h2 hz
      rw [← h1 hz.1, ← h2 hz.2]
    have hcont : ∀ q : ℝ × E, Continuous fun z : E => q.1 + ⟪q.2, z⟫ := fun q =>
      continuous_const.add (continuous_const.inner continuous_id)
    have heq := Measure.eqOn_open_of_ae_eq hae hW (hcont _).continuousOn (hcont _).continuousOn
    obtain ⟨h1, h2⟩ := affine_eq_of_open hW hyW heq
    exact Prod.ext h1 h2
  have hpc : PreconnectedSpace D := Subtype.preconnectedSpace hDc
  have hlc : IsLocallyConstant fun x : D => P x := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : (Subtype.val : D → E) ⁻¹' ball x.1 (R x.1) ∈ nhds x :=
      (isOpen_ball.preimage continuous_subtypeVal).mem_nhds (mem_ball_self (hR x.1))
    filter_upwards [this] with y hy using hloc_eq x.1 x.2 y.1 y.2 hy
  have hconst : ∀ x ∈ D, P x = P x0 := fun x hx =>
    hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x0, hx0⟩
  refine ⟨(P x0).1, (P x0).2, ?_⟩
  obtain ⟨T, hTD, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (R x)) (s := D)
    (fun x _ => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hR x)))
  refine ae_restrict_of_ae_restrict_of_subset hcover ?_
  rw [ae_restrict_biUnion_iff _ hTc]
  intro x hxT
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [(hP x (hTD hxT)).2] with y hy hyb
  rw [hy hyb, hconst x (hTD hxT)]

end Pexider

/-! ## The kernel argument (Theorem 91, used in Proposition 106) -/

section Kernel

open Room

/-- A measurable function bounded by `C` is locally integrable. -/
lemma locallyIntegrable_of_bdd {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    LocallyIntegrable f volume := fun x =>
  ⟨ball x 1, ball_mem_nhds x one_pos, Measure.integrableOn_of_bounded
    measure_ball_lt_top.ne hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)⟩

/-- The coordinates `(w, (a, b)) ↦ (a, b, w₁, …, w_k)` preserve Lebesgue measure. -/
lemma measurePreserving_cons2 (k : ℕ) :
    MeasurePreserving (fun t : (Fin k → E) × (E × E) =>
      (Fin.cons t.2.1 (Fin.cons t.2.2 t.1 : Fin (k + 1) → E) : Fin (k + 2) → E))
      ((Measure.pi fun _ : Fin k => (volume : Measure E)).prod
        ((volume : Measure E).prod volume))
      (Measure.pi fun _ : Fin (k + 2) => (volume : Measure E)) := by
  have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 2) => (volume : Measure E)) 0
  have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure E)) 0
  have h1 := e1.symm
  have h2 := (MeasurePreserving.id (volume : Measure E)).prod e2.symm
  have h3 := measurePreserving_prodAssoc (volume : Measure E) (volume : Measure E)
    (Measure.pi fun _ : Fin k => (volume : Measure E))
  have h4 := Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin k => (volume : Measure E))
    (ν := (volume : Measure E).prod (volume : Measure E))
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

/-- **The kernel argument.** Let `n = k + 3 ≥ 3`, `K` convex and measurable, and suppose every
interior point `a` of `K` has room for partners: `c - (a - c)/(n - 1)` is again an interior point
(this follows from `as(K) < n - 1` by Lemma 89, see `kernelAffine_of_asym`). If `φ` is measurable
and bounded on `K` and `∑ᵢ φ(xᵢ) = 0` for `λ`-almost every tuple of `𝒯_n(K)` (sum `n c`), then `φ`
is almost everywhere on `K` equal to an affine function. This is `Large.KernelAffine λ K` for the
Lebesgue measure `λ = lebTuples` on `𝒯_n(K)`.

The proof follows the paper's smoothing of the functional equation, but replaces the contraction
`x ↦ -x/(n-1)` by a local argument: near a tuple `(a, q, …, q)` with `q = c - (a - c)/(n-1)`,
fixing almost every choice of `x₃, …, x_{n-1}` leaves a Pexider equation
`φ(x₁) + φ(x₂) = k(x₁ + x₂)`, so `φ` is affine near `a` (`pexider_local`); the local affine
functions glue on the connected interior (`glue_affine`), and the boundary of `K` is null. -/
theorem kernelAffine_of_room {k : ℕ} {K : Set E} (hKc : Convex ℝ K) (hKm : MeasurableSet K)
    {c : E} (hroom : ∀ a ∈ interior K, c - ((k + 2 : ℕ) : ℝ)⁻¹ • (a - c) ∈ interior K) :
    Large.KernelAffine (lebTuples (volume : Measure E) (k + 2) K c) K := by
  intro φ hφm ⟨C, hC⟩ hsum
  set ϕ := K.indicator φ with hϕ
  have hϕm : Measurable ϕ := hφm.indicator hKm
  have hϕb : ∀ y, |ϕ y| ≤ max C 0 := fun y => by
    by_cases hy : y ∈ K
    · rw [hϕ, indicator_of_mem hy]; exact (hC y hy).trans (le_max_left _ _)
    · rw [hϕ, indicator_of_notMem hy, abs_zero]; exact le_max_right _ _
  have hϕK : ∀ y ∈ K, φ y = ϕ y := fun y hy => by rw [hϕ, indicator_of_mem hy]
  -- the hypothesis in the coordinates `y ∈ E^{k+2}`
  set T' := embed (m := k + 2) c ⁻¹' tuples (k + 2 + 1) K c with hT'
  have hT'm : MeasurableSet T' := measurable_embed c (measurableSet_tuples hKm c)
  have hy : ∀ᵐ y ∂(Measure.pi fun _ : Fin (k + 2) => (volume : Measure E)), y ∈ T' →
      ∑ i, φ (embed c y i) = 0 := by
    have := ae_of_ae_map (measurable_embed c).aemeasurable hsum
    exact (ae_restrict_iff'₀ hT'm.nullMeasurableSet).1 this
  have hpull := (measurePreserving_cons2 (E := E) k).quasiMeasurePreserving.ae hy
  have hpull2 := Measure.ae_ae_of_ae_prod hpull
  -- local affinity at every interior point
  have hloc : ∀ a0 ∈ interior K, ∃ r > 0, ∃ (c' : ℝ) (v : E),
      ∀ᵐ y, y ∈ ball a0 r → ϕ y = c' + ⟪v, y⟫ := by
    intro a0 ha0
    set q := c - ((k + 2 : ℕ) : ℝ)⁻¹ • (a0 - c) with hq
    have hqK := hroom a0 ha0
    obtain ⟨ε1, hε1, hb1⟩ := Metric.isOpen_iff.1 isOpen_interior a0 ha0
    obtain ⟨ε2, hε2, hb2⟩ := Metric.isOpen_iff.1 isOpen_interior q hqK
    have hk3 : (0 : ℝ) < k + 3 := by positivity
    set r := min ε1 (ε2 / (k + 3)) with hr
    have hr0 : 0 < r := lt_min hε1 (div_pos hε2 hk3)
    have hra : ball a0 r ⊆ K := fun y hy =>
      interior_subset (hb1 (ball_subset_ball (min_le_left _ _) hy))
    have hrq : ∀ y, dist y q < (k + 3) * r → y ∈ K := fun y hy => by
      refine interior_subset (hb2 ?_)
      rw [mem_ball]
      calc dist y q < (k + 3) * r := hy
        _ ≤ (k + 3) * (ε2 / (k + 3)) := by gcongr; exact min_le_right _ _
        _ = ε2 := by field_simp
    have hqa : ((k + 2 : ℕ) : ℝ) • q = ((k + 2 + 1 : ℕ) : ℝ) • c - a0 := by
      rw [hq, smul_sub, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      push_cast; module
    -- a good choice of the remaining coordinates
    set box := Set.pi univ fun _ : Fin k => ball q r
    have hbox : (Measure.pi fun _ : Fin k => (volume : Measure E)) box ≠ 0 := by
      rw [Measure.pi_pi]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => (measure_ball_pos _ _ hr0).ne'
    obtain ⟨w, hwbox, hw⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbox
      (ae_restrict_of_ae hpull2)
    set σ : E := ((k + 2 + 1 : ℕ) : ℝ) • c - ∑ j, w j
    set S : ℝ := ∑ j, ϕ (w j)
    set kk : E → ℝ := fun z => -S - ϕ (σ - z)
    have hkk : LocallyIntegrable kk volume := by
      refine locallyIntegrable_of_bdd (C := |S| + max C 0) ?_ fun z => ?_
      · exact measurable_const.sub (hϕm.comp (measurable_const.sub measurable_id))
      · calc |kk z| ≤ |S| + |ϕ (σ - z)| := by
              simp only [kk]; rw [show -S - ϕ (σ - z) = -(S + ϕ (σ - z)) by ring, abs_neg]
              exact abs_add_le _ _
          _ ≤ |S| + max C 0 := by gcongr; exact hϕb _
    have hϕli := locallyIntegrable_of_bdd hϕm hϕb
    have H : ∀ᵐ p ∂(volume : Measure E).prod volume, p.1 ∈ ball a0 r → p.2 ∈ ball q r →
        ϕ p.1 + ϕ p.2 = kk (p.1 + p.2) := by
      filter_upwards [hw] with p hp ha hb
      set y : Fin (k + 2) → E := Fin.cons p.1 (Fin.cons p.2 w : Fin (k + 1) → E)
      have hsumy : ∑ i, y i = p.1 + p.2 + ∑ j, w j := by
        simp [y, Fin.sum_univ_succ, add_assoc]
      have hyK : ∀ i, y i ∈ K := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [y] using hra ha
        · refine Fin.cases ?_ (fun l => ?_) j
          · simp only [y, Fin.cons_succ, Fin.cons_zero]
            exact hrq _ (by
              have : dist p.2 q < r := hb
              nlinarith [dist_nonneg (x := p.2) (y := q)])
          · simp only [y, Fin.cons_succ]
            exact hrq _ (by
              have : dist (w l) q < r := hwbox l (mem_univ _)
              nlinarith [dist_nonneg (x := w l) (y := q)])
      have hlast : ((k + 2 + 1 : ℕ) : ℝ) • c - ∑ i, y i ∈ K := by
        apply hrq
        rw [hsumy, dist_eq_norm]
        have hid : ((k + 2 + 1 : ℕ) : ℝ) • c - (p.1 + p.2 + ∑ j, w j) - q =
            (a0 - p.1) + (q - p.2) + ∑ j, (q - w j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            ← Nat.cast_smul_eq_nsmul ℝ]
          have : ((k + 2 + 1 : ℕ) : ℝ) • c = ((k + 2 : ℕ) : ℝ) • q + a0 := by rw [hqa]; abel
          rw [this]; push_cast; module
        rw [hid]
        have h1 : ‖a0 - p.1‖ < r := by rw [← dist_eq_norm, dist_comm]; exact ha
        have h2 : ‖q - p.2‖ < r := by rw [← dist_eq_norm, dist_comm]; exact hb
        have h3 : ‖∑ j, (q - w j)‖ ≤ k * r := by
          calc ‖∑ j, (q - w j)‖ ≤ ∑ j : Fin k, ‖q - w j‖ := norm_sum_le _ _
            _ ≤ ∑ _j : Fin k, r := Finset.sum_le_sum fun j _ => by
                rw [← dist_eq_norm, dist_comm]; exact (hwbox j (mem_univ _)).le
            _ = k * r := by simp
        calc ‖a0 - p.1 + (q - p.2) + ∑ j, (q - w j)‖
            ≤ ‖a0 - p.1‖ + ‖q - p.2‖ + ‖∑ j, (q - w j)‖ := norm_add₃_le
          _ < (k + 3) * r := by nlinarith
      have hmem : y ∈ T' := mem_embed_preimage_tuples.2 ⟨hyK, hlast⟩
      have h0 := hp hmem
      rw [Fin.sum_univ_castSucc] at h0
      simp only [embed_castSucc, embed_last] at h0
      rw [hϕK _ hlast, Finset.sum_congr rfl fun i _ => hϕK _ (hyK i)] at h0
      have hs : ∑ i, ϕ (y i) = ϕ p.1 + ϕ p.2 + S := by
        simp [y, Fin.sum_univ_succ, S, add_assoc]
      rw [hs, hsumy] at h0
      simp only [kk, σ]
      rw [show ((k + 2 + 1 : ℕ) : ℝ) • c - ∑ j, w j - (p.1 + p.2) =
        ((k + 2 + 1 : ℕ) : ℝ) • c - (p.1 + p.2 + ∑ j, w j) by abel]
      linarith
    obtain ⟨c', v, hcv⟩ := pexider_local hϕli hϕli hkk hr0 H
    exact ⟨r / 2, by linarith, c', v, hcv⟩
  have hint : IsOpen (interior K) := isOpen_interior
  obtain ⟨c', v, hcv⟩ := glue_affine hint (hKc.interior).isPreconnected hloc
  refine ⟨c', v, ?_⟩
  have hfr : (volume : Measure E) (frontier K) = 0 := hKc.addHaar_frontier volume
  have h1 : ∀ᵐ y, y ∉ frontier K := measure_eq_zero_iff_ae_notMem.1 hfr
  have h2 := (ae_restrict_iff' hint.measurableSet).1 hcv
  rw [ae_restrict_iff' hKm]
  filter_upwards [h1, h2] with y hy1 hy2 hyK
  have hyi : y ∈ interior K := by
    by_contra hni
    exact hy1 ⟨subset_closure hyK, hni⟩
  rw [hϕK y hyK, hy2 hyi]

/-- Room for partners in the interior from Lemma 89: if `K` is closed and convex, contains a ball
about `c` and has asymmetry `as(K) ≤ a < n - 1` about `c` (`n = k + 3`), then
`c - (p - c)/(n - 1)` is an interior point of `K` for every `p ∈ K`. -/
lemma interiorRoom_of_asym {k : ℕ} {K : Set E} (hKc : Convex ℝ K) (hKcl : IsClosed K) {c : E}
    {s a : ℝ} (hs : 0 < s) (hball : closedBall c s ⊆ K) (ha : 0 < a) (han : a < (k + 3 : ℕ) - 1)
    (hasym : AsymLE K c a) :
    ∀ p ∈ K, c - ((k + 2 : ℕ) : ℝ)⁻¹ • (p - c) ∈ interior K := by
  obtain ⟨ρ₀, hρ₀, α, -, hroom⟩ := room (n := k + 3) (by omega) hKc hKcl hs hball ha han hasym
    (volume : Measure E)
  intro p hp
  have h := (hroom ρ₀ hρ₀ le_rfl p ⟨p, hp, by simp [hρ₀.le]⟩).1
  have hsub : innerBody K (2 * ρ₀) ⊆ K := fun x hx => hx (mem_closedBall_self (by linarith))
  have hcast : ((k + 3 : ℕ) : ℝ) - 1 = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at h
  exact interior_mono hsub h

/-- **The kernel property under `as(K) < n - 1`** (Theorem 91's kernel argument with Lemma 89),
for `n = k + 3` and the Lebesgue measure `λ` on `𝒯_n(K)`. -/
theorem kernelAffine_of_asym {k : ℕ} {K : Set E} (hKc : Convex ℝ K) (hKcl : IsClosed K) {c : E}
    {s a : ℝ} (hs : 0 < s) (hball : closedBall c s ⊆ K) (ha : 0 < a) (han : a < (k + 3 : ℕ) - 1)
    (hasym : AsymLE K c a) :
    Large.KernelAffine (lebTuples (volume : Measure E) (k + 2) K c) K :=
  kernelAffine_of_room hKc hKcl.measurableSet fun p hp =>
    interiorRoom_of_asym hKc hKcl hs hball ha han hasym p (interior_subset hp)

/-- **Proposition 106, uniqueness of `h`, unconditionally** (the hypothesis `KernelAffine` of
`Large.prop106_unique` discharged by `kernelAffine_of_asym`). Let `n = k + 3`, `K` compact and
convex, containing a ball about `c`, with `as(K) ≤ a < n - 1` about `c`, and `λ` the Lebesgue
measure on `𝒯_n(K)` (tuples with sum `n c`). If the conditioned products of `h` and `h'` (both
measurable, between `a₀ > 0` and `b₀` on `K`) are `n`-complete mixes of `U(K)`, then
`h' = h e^{c' + ⟪v, ·⟫}` almost everywhere on `K`. -/
theorem prop106_unique_of_asym {k : ℕ} {K : Set E} (hKc : Convex ℝ K) (hKcpt : IsCompact K)
    {c : E} {s a : ℝ} (hs : 0 < s) (hball : closedBall c s ⊆ K) (ha : 0 < a)
    (han : a < (k + 3 : ℕ) - 1) (hasym : AsymLE K c a) {h h' : E → ℝ} (hm : Measurable h)
    (hm' : Measurable h') {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hlo : ∀ y ∈ K, a₀ ≤ h y)
    (hhi : ∀ y ∈ K, h y ≤ b₀) (hlo' : ∀ y ∈ K, a₀ ≤ h' y) (hhi' : ∀ y ∈ K, h' y ≤ b₀)
    (hmix : IsCompleteMix (k + 3) (unifSet K)
      ((lebTuples (volume : Measure E) (k + 2) K c).withDensity
        fun x => ENNReal.ofReal (Large.condProd (lebTuples volume (k + 2) K c) h x)))
    (hmix' : IsCompleteMix (k + 3) (unifSet K)
      ((lebTuples (volume : Measure E) (k + 2) K c).withDensity
        fun x => ENNReal.ofReal (Large.condProd (lebTuples volume (k + 2) K c) h' x))) :
    ∃ (c' : ℝ) (v : E), ∀ᵐ y ∂(volume.restrict K), h' y = h y * Real.exp (c' + ⟪v, y⟫) := by
  have := lebTuples_finite (volume : Measure E) (m := k + 2) hKcpt c
  have hlamK : ∀ᵐ x ∂(lebTuples (volume : Measure E) (k + 2) K c), ∀ i, x i ∈ K := by
    have h0 := lebTuples_null (volume : Measure E) (m := k + 2) hKcpt.measurableSet c
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
    simp only [mem_compl_iff, not_not] at hx
    exact hx.1
  exact Large.prop106_unique _ (by omega) hKcpt.measurableSet hm hm' ha₀ hlo hhi hlo' hhi' hlamK
    hmix hmix' (kernelAffine_of_asym hKc hKcpt.isClosed hs hball ha han hasym)

end Kernel

/-! ## The spectral gap of Theorem 91 in an abstract Hilbert space -/

section Gap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Cauchy–Schwarz for a nonnegative symmetric operator: `⟪Gx, y⟫² ≤ ⟪Gx, x⟫ ⟪Gy, y⟫`. -/
lemma sq_inner_le_of_nonneg (G : H →L[ℝ] H) (hpos : ∀ x, 0 ≤ ⟪G x, x⟫)
    (hsym : ∀ x y, ⟪G x, y⟫ = ⟪x, G y⟫) (x y : H) :
    ⟪G x, y⟫ ^ 2 ≤ ⟪G x, x⟫ * ⟪G y, y⟫ := by
  have h : ∀ t : ℝ, 0 ≤ ⟪G y, y⟫ * (t * t) + 2 * ⟪G x, y⟫ * t + ⟪G x, x⟫ := by
    intro t
    have := hpos (x + t • y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at this
    have hs : ⟪G y, x⟫ = ⟪G x, y⟫ := by rw [hsym, real_inner_comm]
    rw [hs] at this
    nlinarith
  have := discrim_le_zero h
  simp only [discrim] at this
  nlinarith

/-- For a nonnegative symmetric operator, `‖Gx‖² ≤ ‖G‖ ⟪Gx, x⟫`. -/
lemma norm_sq_le_of_nonneg (G : H →L[ℝ] H) (hpos : ∀ x, 0 ≤ ⟪G x, x⟫)
    (hsym : ∀ x y, ⟪G x, y⟫ = ⟪x, G y⟫) (x : H) : ‖G x‖ ^ 2 ≤ ‖G‖ * ⟪G x, x⟫ := by
  have h1 := sq_inner_le_of_nonneg G hpos hsym x (G x)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : ⟪G (G x), G x⟫ ≤ ‖G‖ * ‖G x‖ ^ 2 := by
    calc ⟪G (G x), G x⟫ ≤ ‖G (G x)‖ * ‖G x‖ := real_inner_le_norm _ _
      _ ≤ ‖G‖ * ‖G x‖ * ‖G x‖ := by gcongr; exact G.le_opNorm _
      _ = ‖G‖ * ‖G x‖ ^ 2 := by ring
  have h0 := hpos x
  rcases (norm_nonneg (G x)).eq_or_lt with h | h
  · rw [← h]; simp; exact mul_nonneg (norm_nonneg _) h0
  · have hp : 0 < ‖G x‖ ^ 2 := by positivity
    have : (‖G x‖ ^ 2) ^ 2 ≤ (‖G‖ * ⟪G x, x⟫) * ‖G x‖ ^ 2 := by
      calc (‖G x‖ ^ 2) ^ 2 ≤ ⟪G x, x⟫ * ⟪G (G x), G x⟫ := h1
        _ ≤ ⟪G x, x⟫ * (‖G‖ * ‖G x‖ ^ 2) := by gcongr
        _ = (‖G‖ * ⟪G x, x⟫) * ‖G x‖ ^ 2 := by ring
    nlinarith

/-- **The spectral gap by compactness** (proof of Theorem 91). Let `G` be a bounded, symmetric,
nonnegative operator on a Hilbert space `H` that is the sum of an operator bounded below,
`m ‖x‖ ≤ ‖(G - C) x‖` (in the paper the multiplication by `a₀/n ≥ α/n`), and a compact operator
`C`. If `G` has no kernel on the orthogonal complement `Vᗮ` of a subspace `V` (the linear
functions), then `⟪Gx, x⟫ ≥ γ ‖x‖²` on `Vᗮ` for some `γ > 0`. The paper's argument with weak
limits is replaced by a norm argument: `⟪Gxⱼ, xⱼ⟫ → 0` forces `Gxⱼ → 0`; a subsequence of
`Cxⱼ` converges, hence so does `(G - C)xⱼ`, hence `xⱼ`. -/
theorem spectral_gap (G C : H →L[ℝ] H) (hpos : ∀ x, 0 ≤ ⟪G x, x⟫)
    (hsym : ∀ x y, ⟪G x, y⟫ = ⟪x, G y⟫) {m : ℝ} (hm : 0 < m)
    (hM : ∀ x, m * ‖x‖ ≤ ‖G x - C x‖) (hC : IsCompactOperator C) (V : Submodule ℝ H)
    (hker : ∀ x ∈ Vᗮ, G x = 0 → x = 0) :
    ∃ γ > 0, ∀ x ∈ Vᗮ, γ * ‖x‖ ^ 2 ≤ ⟪G x, x⟫ := by
  by_contra hcon
  push Not at hcon
  have hj : ∀ j : ℕ, ∃ x ∈ Vᗮ, ⟪G x, x⟫ < (1 / ((j : ℝ) + 1)) * ‖x‖ ^ 2 := fun j =>
    hcon _ (by positivity)
  choose x hxV hx using hj
  have hx0 : ∀ j, x j ≠ 0 := fun j h => by
    have := hx j; rw [h] at this; simp at this
  set u : ℕ → H := fun j => ‖x j‖⁻¹ • x j with hu
  have hun : ∀ j, ‖u j‖ = 1 := fun j => by
    rw [hu]; simp only; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2
      (hx0 j))]
  have huV : ∀ j, u j ∈ Vᗮ := fun j => Submodule.smul_mem _ _ (hxV j)
  have huG : ∀ j, ⟪G (u j), u j⟫ < 1 / ((j : ℝ) + 1) := fun j => by
    have hpos' : 0 < ‖x j‖ := norm_pos_iff.2 (hx0 j)
    have : ⟪G (u j), u j⟫ = (‖x j‖ ^ 2)⁻¹ * ⟪G (x j), x j⟫ := by
      rw [hu]; simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp
    rw [this, inv_mul_lt_iff₀ (by positivity)]
    linarith [hx j]
  -- `G uⱼ → 0`
  have hGu : Filter.Tendsto (fun j => G (u j)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun j => ‖G (u j)‖ ^ 2) Filter.atTop (nhds 0) := by
      have hlim : Filter.Tendsto (fun j : ℕ => ‖G‖ * (1 / ((j : ℝ) + 1))) Filter.atTop
          (nhds 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖G‖
      refine squeeze_zero (fun j => by positivity) (fun j => ?_) hlim
      calc ‖G (u j)‖ ^ 2 ≤ ‖G‖ * ⟪G (u j), u j⟫ := norm_sq_le_of_nonneg G hpos hsym _
        _ ≤ ‖G‖ * (1 / ((j : ℝ) + 1)) := by gcongr; exact (huG j).le
    have : Filter.Tendsto (fun j => ‖G (u j)‖) Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hsq
      simp only [Function.comp_def, Real.sqrt_zero] at h
      refine h.congr fun j => ?_
      rw [Real.sqrt_sq (norm_nonneg _)]
    exact tendsto_zero_iff_norm_tendsto_zero.2 this
  -- a convergent subsequence of `C uⱼ`
  obtain ⟨Kc, hKc, hsub⟩ := hC.image_subset_compact_of_bounded (f := (C : H →ₗ[ℝ] H))
    (S := closedBall (0 : H) 1) isBounded_closedBall
  have hCu : ∀ j, C (u j) ∈ Kc := fun j =>
    hsub ⟨u j, by rw [mem_closedBall, dist_zero_right, hun], rfl⟩
  obtain ⟨z, -, ψ, hψ, hz⟩ := hKc.tendsto_subseq hCu
  set w := fun j => u (ψ j) with hw
  have hMw : Filter.Tendsto (fun j => G (w j) - C (w j)) Filter.atTop (nhds (0 - z)) :=
    (hGu.comp hψ.tendsto_atTop).sub hz
  have hcw : CauchySeq w := by
    have hc := hMw.cauchySeq
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc (m * ε) (mul_pos hm hε)
    refine ⟨N, fun a ha b hb => ?_⟩
    have h1 := hN a ha b hb
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hM (w a - w b)
    rw [map_sub, map_sub] at h2
    have : G (w a) - G (w b) - (C (w a) - C (w b)) =
        G (w a) - C (w a) - (G (w b) - C (w b)) := by abel
    rw [this] at h2
    have h3 : m * ‖w a - w b‖ < m * ε := lt_of_le_of_lt h2 h1
    exact lt_of_mul_lt_mul_left h3 hm.le
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcw
  have hvn : ‖v‖ = 1 := by
    have := (continuous_norm.tendsto v).comp hv
    simp only [Function.comp_def, hw, hun] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have hvV : v ∈ Vᗮ := V.isClosed_orthogonal.mem_of_tendsto hv
    (Filter.Eventually.of_forall fun j => huV _)
  have hGv : G v = 0 :=
    tendsto_nhds_unique ((G.continuous.tendsto v).comp hv) (hGu.comp hψ.tendsto_atTop)
  have := hker v hvV hGv
  rw [this, norm_zero] at hvn
  exact zero_ne_one hvn

/-- **Inverting `G` on `Vᗮ`** (proof of Theorem 91). If `G` maps into `Vᗮ` and
`⟪Gx, x⟫ ≥ γ ‖x‖²` on `Vᗮ`, then for every `h ∈ Vᗮ` there is `φ ∈ Vᗮ` with `Gφ = h` and
`‖φ‖ ≤ γ⁻¹ ‖h‖` (Lax–Milgram on the Hilbert space `Vᗮ`). -/
theorem solve_of_gap (G : H →L[ℝ] H) (V : Submodule ℝ H) (hrange : ∀ x, G x ∈ Vᗮ) {γ : ℝ}
    (hγ : 0 < γ) (hgap : ∀ x ∈ Vᗮ, γ * ‖x‖ ^ 2 ≤ ⟪G x, x⟫) {h : H} (hh : h ∈ Vᗮ) :
    ∃ φ ∈ Vᗮ, G φ = h ∧ ‖φ‖ ≤ γ⁻¹ * ‖h‖ := by
  set W := Vᗮ
  let Gw : W →L[ℝ] W := (G.comp W.subtypeL).codRestrict W (fun x => hrange x)
  let B : W →L[ℝ] W →L[ℝ] ℝ := (innerSL ℝ (E := W)).comp Gw
  have hB : ∀ u v : W, B u v = ⟪G u, v⟫ := fun u v => rfl
  have hcoer : IsCoercive B := ⟨γ, hγ, fun u => by
    rw [hB, mul_assoc, ← sq]
    exact hgap u u.2⟩
  have hsharp : InnerProductSpace.continuousLinearMapOfBilin B = Gw := by
    ext1 u
    refine ext_inner_right ℝ fun v => ?_
    rw [InnerProductSpace.continuousLinearMapOfBilin_apply, hB]
    rfl
  have hrt := hcoer.range_eq_top
  rw [hsharp] at hrt
  obtain ⟨φ, hφ⟩ : (⟨h, hh⟩ : W) ∈ (Gw : W →ₗ[ℝ] W).range := by
    rw [hrt]; trivial
  have hGφ : G φ = h := congrArg Subtype.val hφ
  refine ⟨φ, φ.2, hGφ, ?_⟩
  have h1 := hgap φ φ.2
  rw [hGφ] at h1
  have h2 : ⟪h, (φ : H)⟫ ≤ ‖h‖ * ‖(φ : H)‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (φ : H)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · rw [le_inv_mul_iff₀ hγ]
    nlinarith

/-- **The linear correction of Theorem 91, abstractly.** Let `G₀ = M + C` be bounded, symmetric,
nonnegative, with `M` bounded below and `C` compact, and without kernel on `Vᗮ`. There is
`γ₀ > 0` such that every operator `G` mapping into `Vᗮ` with
`⟪G₀x, x⟫ - ⟪Gx, x⟫ ≤ (γ₀/2) ‖x‖²` on `Vᗮ` (the perturbation from `K₀` to `K`) is invertible on
`Vᗮ`: every `h ∈ Vᗮ` is `Gφ` for some `φ ∈ Vᗮ` with `‖φ‖ ≤ 2γ₀⁻¹ ‖h‖`. -/
theorem linear_correction (G0 C : H →L[ℝ] H) (hpos : ∀ x, 0 ≤ ⟪G0 x, x⟫)
    (hsym : ∀ x y, ⟪G0 x, y⟫ = ⟪x, G0 y⟫) {m : ℝ} (hm : 0 < m)
    (hM : ∀ x, m * ‖x‖ ≤ ‖G0 x - C x‖) (hC : IsCompactOperator C) (V : Submodule ℝ H)
    (hker : ∀ x ∈ Vᗮ, G0 x = 0 → x = 0) :
    ∃ γ0 > 0, ∀ G : H →L[ℝ] H, (∀ x, G x ∈ Vᗮ) →
      (∀ x ∈ Vᗮ, ⟪G0 x, x⟫ - ⟪G x, x⟫ ≤ γ0 / 2 * ‖x‖ ^ 2) →
      ∀ h ∈ Vᗮ, ∃ φ ∈ Vᗮ, G φ = h ∧ ‖φ‖ ≤ 2 * γ0⁻¹ * ‖h‖ := by
  obtain ⟨γ0, hγ0, hgap⟩ := spectral_gap G0 C hpos hsym hm hM hC V hker
  refine ⟨γ0, hγ0, fun G hrange hpert h hh => ?_⟩
  have hgap' : ∀ x ∈ Vᗮ, γ0 / 2 * ‖x‖ ^ 2 ≤ ⟪G x, x⟫ := fun x hx => by
    have := hgap x hx; have := hpert x hx; linarith
  obtain ⟨φ, hφV, hGφ, hφ⟩ := solve_of_gap G V hrange (by positivity) hgap' hh
  refine ⟨φ, hφV, hGφ, ?_⟩
  calc ‖φ‖ ≤ (γ0 / 2)⁻¹ * ‖h‖ := hφ
    _ = 2 * γ0⁻¹ * ‖h‖ := by field_simp

end Gap

/-! ## Definition 90 and the statement of Theorem 91 -/

section Robust

open Room

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- `𝒯^ρ_n(K)`: the tuples of `𝒯_n(K)` (sum `n c`) with at least `n - 1` coordinates in
`K_ρ = {x : x + ρB ⊂ K}`. -/
def tuplesRho (n : ℕ) (K : Set V) (c : V) (ρ : ℝ) : Set (Fin n → V) :=
  tuples n K c ∩ {x | ∃ j, ∀ i, i ≠ j → x i ∈ innerBody K ρ}

/-- **Definition 90** (`st:def:robust`), for `n = m + 1`: `U(K)` is robustly `n`-completely
mixable if for every `ρ > 0` there are `b > 0` and a permutation-invariant probability measure
`β` on `𝒯_n(K)` (sum `n c`, `c` the centroid) with `β̄ = U(K)` and `β ≥ b λ` on `𝒯^ρ_n(K)`, where
`λ` is the Lebesgue measure on `𝒯_n(K)` (`lebTuples`, through the first `n - 1` coordinates).
"`β ≥ b λ` on `𝒮`" is written `b • λ|_𝒮 ≤ β`. -/
def RobustlyCM (m : ℕ) (K : Set V) : Prop :=
  ∀ ρ > 0, ∃ b : ENNReal, 0 < b ∧ b ≠ ⊤ ∧ ∃ β : Measure (Fin (m + 1) → V),
    IsProbabilityMeasure β ∧ β (tuples (m + 1) K (centroid K))ᶜ = 0 ∧ PermInvariant β ∧
    marginal β = unifSet K ∧
    b • (lebTuples volume m K (centroid K)).restrict (tuplesRho (m + 1) K (centroid K) ρ) ≤ β

/-- A robust complete mix is a complete mix (Lemma 88). -/
lemma RobustlyCM.completelyMixable {m : ℕ} {K : Set V} (hK : IsCompact K)
    (hpos : 0 < volume K) (h : RobustlyCM m K) : CompletelyMixable (m + 1) (unifSet K) := by
  obtain ⟨b, -, -, β, h1, h2, h3, h4, -⟩ := h 1 one_pos
  exact (completelyMixable_unif_iff (Nat.succ_pos m) hK hpos).2 ⟨β, h1, h2, h3, h4⟩

/-- **Lemma 92 gives robustness**: a linear `L` with `L^n = I` (`n = k + 2`), no eigenvalue `1`,
mapping `K` onto itself, makes `U(K)` robustly `n`-completely mixable (`β ≥ b λ` even on all of
`𝒯_n(K)`, `Room.symm_robust`). -/
theorem robust_of_symm {k : ℕ} (L : V →L[ℝ] V) (hLn : L ^ (k + 2) = 1)
    (hfix : ∀ x, L x = x → x = 0) {K : Set V} (hK : IsCompact K) (hpos : 0 < volume K)
    (hLK : L ⁻¹' K = K) : RobustlyCM (k + 1) K := by
  intro ρ _
  obtain ⟨-, b, hb, hbt, β, h1, h2, h3, h4, h5⟩ := symm_robust L hLn hfix hK hpos hLK
  refine ⟨b, hb, hbt, β, h1, h2, h3, h4, le_trans ?_ h5⟩
  rw [Measure.le_iff]
  intro S hS
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  gcongr
  exact Measure.restrict_le_self

variable (V) in
/-- **The statement of Theorem 91** (`st:thm:open`) for `n = m + 1`, as a proposition: for every
convex body `K₀` with `as(K₀) < n - 1` (about its centroid) whose uniform distribution is robustly
`n`-completely mixable there is `ε > 0` such that `U(K)` is `n`-completely mixable for every convex
body `K` whose translate by its centroid has Hausdorff distance less than `ε` from that of `K₀`. -/
def Thm91Stmt (m : ℕ) : Prop :=
  ∀ K0 : Set V, Convex ℝ K0 → IsCompact K0 → (interior K0).Nonempty →
    (∃ a : ℝ, 0 < a ∧ a < (m : ℝ) ∧ AsymLE K0 (centroid K0) a) → RobustlyCM m K0 →
    ∃ ε > 0, ∀ K : Set V, Convex ℝ K → IsCompact K → (interior K).Nonempty →
      Metric.hausdorffDist ((fun x => x - centroid K) '' K) ((fun x => x - centroid K0) '' K0)
        < ε → CompletelyMixable (m + 1) (unifSet K)

/-- Banach–Mazur closeness `δ(K, K₀) < 1 + ε`: `K₀ ⊂ T(K) ⊂ z + t(K₀ - z)` for an affine
bijection `T`, a point `z` and some `1 ≤ t < 1 + ε`. -/
def BMClose (K K0 : Set V) (ε : ℝ) : Prop :=
  ∃ (T : V ≃ᵃ[ℝ] V) (z : V) (t : ℝ), 1 ≤ t ∧ t < 1 + ε ∧ K0 ⊆ T '' K ∧
    T '' K ⊆ AffineMap.homothety z t '' K0

/-- The centre of a homothety with ratio `t > 1` that maps a closed nonempty set onto a superset
of itself lies in the set. -/
lemma center_mem {K0 : Set V} (hcl : IsClosed K0) (hne : K0.Nonempty) {z : V} {t : ℝ}
    (ht : 1 < t) (hsub : K0 ⊆ AffineMap.homothety z t '' K0) : z ∈ K0 := by
  obtain ⟨x0, hx0⟩ := hne
  have ht0 : 0 < t := by linarith
  have hg : ∀ x ∈ K0, z + t⁻¹ • (x - z) ∈ K0 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hsub hx
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] at hyx
    have : z + t⁻¹ • (x - z) = y := by
      rw [← hyx, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]; abel
    rw [this]; exact hy
  have hit : ∀ j : ℕ, z + (t⁻¹) ^ j • (x0 - z) ∈ K0 := by
    intro j
    induction j with
    | zero => simpa using hx0
    | succ j ih =>
      have := hg _ ih
      rw [add_sub_cancel_left, smul_smul, ← pow_succ'] at this
      exact this
  have hlim : Filter.Tendsto (fun j : ℕ => z + (t⁻¹) ^ j • (x0 - z)) Filter.atTop (nhds z) := by
    have h1 : Filter.Tendsto (fun j : ℕ => (t⁻¹) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 ht0.le) (inv_lt_one_of_one_lt₀ ht)
    have := (tendsto_const_nhds (x := z)).add (h1.smul_const (x0 - z))
    simpa using this
  exact hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall hit)

/-- The centroid of `B ⊇ A` is close to that of `A` when `B \ A` is small:
`‖c_B - c_A‖ ≤ R |B \ A| / |B|` if `‖x - c_A‖ ≤ R` on `B`. -/
lemma centroid_sub_le {A B : Set V} (hA : IsCompact A) (hB : IsCompact B) (hAB : A ⊆ B)
    (hApos : 0 < volume A) {R : ℝ} (hR : ∀ x ∈ B, ‖x - centroid A‖ ≤ R) :
    ‖centroid B - centroid A‖ ≤ R * ((volume.real B - volume.real A) / volume.real B) := by
  have hBpos : 0 < volume B := hApos.trans_le (measure_mono hAB)
  have hBr : 0 < volume.real B :=
    ENNReal.toReal_pos hBpos.ne' hB.measure_lt_top.ne
  set cA := centroid A
  have hcent : ∀ {C : Set V}, IsCompact C → 0 < volume C →
      centroid C = (volume.real C)⁻¹ • ∫ x in C, x := by
    intro C hC hCpos
    rw [centroid, unifSet, integral_smul_measure, ENNReal.toReal_inv]
    rfl
  have hAr : 0 < volume.real A := ENNReal.toReal_pos hApos.ne' hA.measure_lt_top.ne
  have hint : ∀ {C : Set V}, IsCompact C → IntegrableOn (fun x : V => x - cA) C volume :=
    fun hC => (continuous_id.sub continuous_const).continuousOn.integrableOn_compact hC
  have hintA : ∫ x in A, (x - cA) = 0 := by
    have hiA : IntegrableOn (fun x : V => x) A volume :=
      continuous_id.continuousOn.integrableOn_compact hA
    rw [integral_sub hiA
      (integrableOn_const hA.measure_lt_top.ne), setIntegral_const]
    have h1 : (volume.real A) • centroid A = ∫ x in A, x := by
      rw [hcent hA hApos, smul_smul, mul_inv_cancel₀ hAr.ne', one_smul]
    rw [← h1, sub_self]
  have hsplit : ∫ x in B, (x - cA) = ∫ x in B \ A, (x - cA) := by
    rw [← union_sdiff_cancel hAB, setIntegral_union disjoint_sdiff_right
      (hB.measurableSet.diff hA.measurableSet) (hint hA)
      ((hint hB).mono_set (union_sdiff_cancel hAB ▸ sdiff_subset)), hintA, zero_add,
      union_sdiff_cancel hAB]
  have hcB : centroid B - cA = (volume.real B)⁻¹ • ∫ x in B, (x - cA) := by
    have hiB : IntegrableOn (fun x : V => x) B volume :=
      continuous_id.continuousOn.integrableOn_compact hB
    rw [integral_sub hiB
      (integrableOn_const hB.measure_lt_top.ne), setIntegral_const, smul_sub, smul_smul,
      inv_mul_cancel₀ hBr.ne', one_smul, hcent hB hBpos]
  have hbound : ‖∫ x in B \ A, (x - cA)‖ ≤ R * volume.real (B \ A) :=
    norm_setIntegral_le_of_norm_le_const ((measure_mono sdiff_subset).trans_lt
      hB.measure_lt_top) fun x hx => hR x hx.1
  rw [hcB, hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hBr),
    measureReal_sdiff hAB hA.measurableSet hB.measure_lt_top.ne] at *
  rw [inv_mul_le_iff₀ hBr]
  calc ‖∫ x in B \ A, (x - cA)‖ ≤ R * (volume.real B - volume.real A) := hbound
    _ = volume.real B * (R * ((volume.real B - volume.real A) / volume.real B)) := by
      field_simp

/-- Complete mixability of `U(T(K))` for an affine bijection `T` gives that of `U(K)`. -/
lemma completelyMixable_of_affine_image {n : ℕ} {K : Set V} (T : V ≃ᵃ[ℝ] V)
    (h : CompletelyMixable n (unifSet (T '' K))) : CompletelyMixable n (unifSet K) := by
  have := SymmCor.completelyMixable_image_affine h
    (LinearEquiv.isUnit_det' T.symm.linear).ne_zero (T.symm 0)
  convert this using 3
  ext x
  constructor
  · intro hx
    refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
    have h1 := AffineMap.linear_apply_vsub T.symm.toAffineMap (T x) 0
    simp only [vsub_eq_sub, sub_zero] at h1
    change T.symm.linear (T x) + T.symm 0 = x
    rw [show T.symm.linear (T x) = T.symm.toAffineMap.linear (T x) from rfl, h1]
    simp
  · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
    have h1 := AffineMap.linear_apply_vsub T.symm.toAffineMap (T x') 0
    simp only [vsub_eq_sub, sub_zero] at h1
    change T.symm.linear (T x') + T.symm 0 ∈ K
    rw [show T.symm.linear (T x') = T.symm.toAffineMap.linear (T x') from rfl, h1]
    simpa using hx'

/-- **The reduction in Corollary 93.** Given Theorem 91 (`Thm91Stmt`) for `n = m + 1`, a convex
body `K₀` with `as(K₀) < n - 1` whose uniform distribution is robustly `n`-completely mixable has
an `ε > 0` such that `U(K)` is `n`-completely mixable for every convex body `K` with Banach–Mazur
distance `δ(K, K₀) < 1 + ε`: from `K₀ ⊂ T(K) ⊂ z + t(K₀ - z)` the Hausdorff distance of `T(K)`
from `K₀` and the distance of the centroids are at most a constant times `t - 1`, resp.
`t^d - 1`; complete mixability is invariant under affine bijections. -/
theorem stable_of_thm91 {m : ℕ} (h91 : Thm91Stmt V m) {K0 : Set V} (hK0c : Convex ℝ K0)
    (hK0 : IsCompact K0) (hK0i : (interior K0).Nonempty)
    (hasym : ∃ a : ℝ, 0 < a ∧ a < (m : ℝ) ∧ AsymLE K0 (centroid K0) a) (hrob : RobustlyCM m K0) :
    ∃ ε > 0, ∀ K : Set V, Convex ℝ K → IsCompact K → BMClose K K0 ε →
      CompletelyMixable (m + 1) (unifSet K) := by
  obtain ⟨ε1, hε1, h1⟩ := h91 K0 hK0c hK0 hK0i hasym hrob
  obtain ⟨M, hM⟩ := hK0.isBounded.exists_norm_le
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hMK : ∀ x ∈ K0, ‖x‖ ≤ M' := fun x hx => (hM x hx).trans (le_max_left _ _)
  set d := Module.finrank ℝ V
  set g : ℝ → ℝ := fun t => (t - 1) * (2 * M') + 4 * M' * (t ^ d - 1) with hg
  have hgc : ContinuousAt g 1 := by fun_prop
  have hg1 : g 1 = 0 := by simp [g]
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hgc ε1 hε1
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  rintro K hKc hK ⟨T, z, t, ht1, ht, hsub1, hsub2⟩
  have htδ : t - 1 < δ := by have := min_le_left δ 1; linarith
  have ht2 : t ≤ 2 := by have := min_le_right δ 1; linarith
  have hgt : g t < ε1 := by
    have := hδg (show dist t 1 < δ by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; exact htδ)
    rw [hg1, Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  set K' := T '' K with hK'
  have hK'c : Convex ℝ K' := hKc.affine_image T.toAffineMap
  have hK'k : IsCompact K' := hK.image T.continuous_of_finiteDimensional
  have hK'i : (interior K').Nonempty := hK0i.mono (interior_mono hsub1)
  apply completelyMixable_of_affine_image T
  refine h1 K' hK'c hK'k hK'i (lt_of_le_of_lt ?_ hgt)
  -- the estimates
  have hK0pos : 0 < volume K0 := by
    obtain ⟨x, hx⟩ := hK0i
    exact (isOpen_interior.measure_pos volume ⟨x, hx⟩).trans_le (measure_mono interior_subset)
  set c0 := centroid K0
  have hc0 : ‖c0‖ ≤ M' := by
    have := Room.unifSet_isProb hK0 hK0pos
    have hb : ∀ᵐ x ∂(unifSet K0), ‖x‖ ≤ M' := by
      have : unifSet K0 ≪ volume.restrict K0 := by
        rw [unifSet]; exact Measure.smul_absolutelyContinuous
      exact this.ae_le ((ae_restrict_iff' hK0.measurableSet).2
        (Filter.Eventually.of_forall hMK))
    have := norm_integral_le_of_norm_le_const hb
    simpa [c0, centroid] using this
  -- the defect of the homothety
  have hzt : ∀ y ∈ K0, (t - 1) * ‖y - z‖ ≤ (t - 1) * (2 * M') := by
    intro y hy
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [← h]; simp
    · have hz := center_mem hK0.isClosed ⟨_, hy⟩ h (hsub1.trans hsub2)
      have h0 : 0 ≤ t - 1 := by linarith
      refine mul_le_mul_of_nonneg_left ?_ h0
      · calc ‖y - z‖ ≤ ‖y‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ M' + M' := add_le_add (hMK y hy) (hMK z hz)
          _ = 2 * M' := by ring
  have hhom : ∀ y : V, AffineMap.homothety z t y - y = (t - 1) • (y - z) := by
    intro y; rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module
  -- centroid estimate
  have hvol : volume.real K' ≤ t ^ d * volume.real K0 := by
    have h := measure_mono (μ := (volume : Measure V)) hsub2
    rw [Measure.addHaar_image_homothety] at h
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      hK0.measure_lt_top.ne) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_nonneg (pow_nonneg (by linarith) _)] at h'
    exact h'
  have hK'pos : 0 < volume.real K' := by
    have := measure_mono (μ := (volume : Measure V)) hsub1
    exact ENNReal.toReal_pos (hK0pos.trans_le this).ne' hK'k.measure_lt_top.ne
  have hvol0 : volume.real K0 ≤ volume.real K' :=
    ENNReal.toReal_mono hK'k.measure_lt_top.ne (measure_mono hsub1)
  have htd : 1 ≤ t ^ d := one_le_pow₀ ht1
  have hratio : (volume.real K' - volume.real K0) / volume.real K' ≤ t ^ d - 1 := by
    rw [div_le_iff₀ hK'pos]
    nlinarith
  have hR : ∀ x ∈ K', ‖x - c0‖ ≤ 4 * M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hsub2 hx
    have := hzt y hy
    calc ‖AffineMap.homothety z t y - c0‖
        = ‖(AffineMap.homothety z t y - y) + (y - c0)‖ := by abel_nf
      _ ≤ ‖AffineMap.homothety z t y - y‖ + ‖y - c0‖ := norm_add_le _ _
      _ ≤ (t - 1) * (2 * M') + (‖y‖ + ‖c0‖) := by
          gcongr
          · rw [hhom, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; exact this
          · exact norm_sub_le _ _
      _ ≤ 1 * (2 * M') + (M' + M') := by
          gcongr
          · linarith
          · exact hMK y hy
      _ = 4 * M' := by ring
  have hcent := centroid_sub_le hK0 hK'k hsub1 hK0pos hR
  have hcent' : ‖centroid K' - c0‖ ≤ 4 * M' * (t ^ d - 1) :=
    hcent.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
  have hg0 : 0 ≤ g t := by
    simp only [g]
    have : 0 ≤ t ^ d - 1 := by linarith
    have : 0 ≤ t - 1 := by linarith
    positivity
  refine Metric.hausdorffDist_le_of_mem_dist hg0 ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hsub2 hx
    refine ⟨y - c0, ⟨y, hy, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    calc ‖AffineMap.homothety z t y - centroid K' - (y - c0)‖
        = ‖(AffineMap.homothety z t y - y) - (centroid K' - c0)‖ := by abel_nf
      _ ≤ ‖AffineMap.homothety z t y - y‖ + ‖centroid K' - c0‖ := norm_sub_le _ _
      _ ≤ (t - 1) * (2 * M') + 4 * M' * (t ^ d - 1) := by
          gcongr
          rw [hhom, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          exact hzt y hy
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y - centroid K', ⟨y, hsub1 hy, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    calc ‖y - c0 - (y - centroid K')‖ = ‖centroid K' - c0‖ := by abel_nf
      _ ≤ 4 * M' * (t ^ d - 1) := hcent'
      _ ≤ g t := by
          simp only [g]
          have : 0 ≤ t - 1 := by linarith
          nlinarith

end Robust

/-! ## Corollary 93 -/

section Cor93

open Room

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

lemma bmClose_mono {K K0 : Set V} {ε ε' : ℝ} (h : BMClose K K0 ε) (hε : ε ≤ ε') :
    BMClose K K0 ε' := by
  obtain ⟨T, z, t, h1, h2, h3, h4⟩ := h
  exact ⟨T, z, t, h1, by linarith, h3, h4⟩

/-- The semigroup step (Remark 81): complete mixability for `n = 3, 4, 5` gives every `n ≥ 3`. -/
lemma completelyMixable_of_345 {μ : Measure V} (h3 : CompletelyMixable 3 μ)
    (h4 : CompletelyMixable 4 μ) (h5 : CompletelyMixable 5 μ) :
    ∀ n, 3 ≤ n → CompletelyMixable n μ := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with h | h | h | h
    · subst h; exact h3
    · subst h; exact h4
    · subst h; exact h5
    · have := ScaledB.completelyMixable_add_add (ih (n - 3) (by omega) (by omega)) h3
      rwa [show n - 3 + 3 = n by omega] at this

/-- The closed unit ball has asymmetry `1` about `0`. -/
lemma asymLE_ball : AsymLE (closedBall (0 : V) 1) 0 1 := by
  intro u x hx
  refine ⟨-x, by simpa using hx, ?_⟩
  simp

/-- The closed unit ball is a convex body. -/
lemma ball_body : Convex ℝ (closedBall (0 : V) 1) ∧ IsCompact (closedBall (0 : V) 1) ∧
    (interior (closedBall (0 : V) 1)).Nonempty :=
  ⟨convex_closedBall _ _, isCompact_closedBall _ _,
    ⟨0, interior_mono ball_subset_closedBall (by rw [isOpen_ball.interior_eq]; simp)⟩⟩

end Cor93

section Disc

open Room

/-- Multiplication by a primitive `n`-th root of unity on `ℂ` (the rotation by `2π/n`). -/
def rotC (n : ℕ) : ℂ →L[ℝ] ℂ :=
  (LinearMap.mulLeft ℝ (Complex.exp (2 * Real.pi * Complex.I / n))).toContinuousLinearMap

lemma rotC_pow_apply (n j : ℕ) (x : ℂ) :
    (rotC n ^ j) x = Complex.exp (2 * Real.pi * Complex.I / n) ^ j * x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    change (rotC n ^ j) (rotC n x) = _
    rw [ih]
    simp [rotC, pow_succ, mul_assoc]

/-- The rotation of the disc by `2π/n` gives Lemma 92 for the disc and `n = k + 2 ≥ 2`. -/
lemma disc_robust (k : ℕ) :
    centroid (closedBall (0 : ℂ) 1) = 0 ∧ RobustlyCM (k + 1) (closedBall (0 : ℂ) 1) := by
  set n := k + 2
  have hn : n ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp n hn
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hLn : rotC n ^ n = 1 := by
    ext1 x
    rw [rotC_pow_apply, hprim.pow_eq_one, one_mul]; rfl
  have hfix : ∀ x, rotC n x = x → x = 0 := by
    intro x hx
    have h1 : ζ ≠ 1 := hprim.ne_one (by omega)
    have : (ζ - 1) * x = 0 := by
      have hx' : ζ * x = x := hx
      rw [sub_mul, hx', one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hnorm : ‖ζ‖ = 1 := hprim.norm'_eq_one hn
  have hLK : rotC n ⁻¹' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_zero_right]
    change ‖ζ * x‖ ≤ 1 ↔ ‖x‖ ≤ 1
    rw [norm_mul, hnorm, one_mul]
  have hpos : 0 < volume (closedBall (0 : ℂ) 1) := measure_closedBall_pos _ _ one_pos
  have hk : n = k + 2 := rfl
  rw [hk] at hLn
  exact ⟨(symm_robust (rotC n) hLn hfix (isCompact_closedBall _ _) hpos hLK).1,
    robust_of_symm (rotC n) hLn hfix (isCompact_closedBall _ _) hpos hLK⟩

/-- **Corollary 93 (b)**, given Theorem 91 (`Thm91Stmt ℂ m` for `m = 2, 3, 4`, i.e. `n = 3, 4, 5`):
there is `ε > 0` such that `U(K)` is `n`-completely mixable for every `n ≥ 3` and every convex
body `K` of the plane `ℂ` with `δ(K, B) < 1 + ε`, `B` the unit disc. -/
theorem cor93b (h91 : ∀ m, 2 ≤ m → Thm91Stmt ℂ m) :
    ∃ ε > 0, ∀ K : Set ℂ, Convex ℝ K → IsCompact K → BMClose K (closedBall 0 1) ε →
      ∀ n, 3 ≤ n → CompletelyMixable n (unifSet K) := by
  obtain ⟨hBc, hBk, hBi⟩ := ball_body (V := ℂ)
  have hst : ∀ k : ℕ, ∃ ε > 0, ∀ K : Set ℂ, Convex ℝ K → IsCompact K →
      BMClose K (closedBall 0 1) ε → CompletelyMixable (k + 3) (unifSet K) := by
    intro k
    obtain ⟨hc, hrob⟩ := disc_robust (k + 1)
    exact stable_of_thm91 (h91 (k + 2) (by omega)) hBc hBk hBi
      ⟨1, one_pos, by push_cast; linarith, by rw [hc]; exact asymLE_ball⟩ hrob
  obtain ⟨ε3, h3, H3⟩ := hst 0
  obtain ⟨ε4, h4, H4⟩ := hst 1
  obtain ⟨ε5, h5, H5⟩ := hst 2
  refine ⟨min ε3 (min ε4 ε5), lt_min h3 (lt_min h4 h5), fun K hKc hK hBM => ?_⟩
  exact completelyMixable_of_345
    (H3 K hKc hK (bmClose_mono hBM (min_le_left _ _)))
    (H4 K hKc hK (bmClose_mono hBM ((min_le_right _ _).trans (min_le_left _ _))))
    (H5 K hKc hK (bmClose_mono hBM ((min_le_right _ _).trans (min_le_right _ _))))

end Disc

section Plane

open Room

/-- **In the plane `ℝ × ℝ`, an affine bijection `A ≠ id` with `A³ = id` has a linear part
without the eigenvalue `1`** (the argument of `SymmCor.no_eigen_one_plane`, with the standard
basis of `ℝ × ℝ`). -/
theorem no_eigen_one_prod (A : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) (hm : (⇑A)^[3] = id)
    (hA : ∃ x, A x ≠ x) : ∀ v, A.linear v = v → v = 0 := by
  intro v hv
  by_contra hv0
  set A₀ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := (A.linear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
  set bs := Module.Basis.finTwoProd ℝ
  set M := LinearMap.toMatrixAlgEquiv bs A₀
  have hM3 : M ^ 3 = 1 := by
    rw [← map_pow, Mixes.linear_pow_eq_one A hm, map_one]
  have hdet : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨bs.repr v, fun h => hv0 (bs.repr.injective (by
      rw [map_zero]; exact DFunLike.coe_injective h)), ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, show M = LinearMap.toMatrix bs bs A₀ by
      ext i j; simp [M, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply],
      LinearMap.toMatrix_mulVec_repr]
    rw [show A₀ v = v from hv, sub_self]
  have hM := SymmCor.matrix_two_eq_one hM3 hdet
  have hA₀ : A₀ = 1 := (LinearMap.toMatrixAlgEquiv bs).injective (by rw [map_one]; exact hM)
  have hx : ∀ x, A x = x + A 0 := fun x => by
    rw [SymmCor.affine_lin A x]; change A₀ x + A 0 = _; rw [hA₀]; rfl
  have h0 : A 0 = 0 := by
    have := congrFun hm 0
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at this
    rw [hx (A 0), hx (A 0 + A 0)] at this
    have h3 : (3 : ℝ) • A 0 = 0 := by
      rw [show (3 : ℝ) • A 0 = A 0 + A 0 + A 0 by module]; exact this
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  obtain ⟨x, hx'⟩ := hA
  exact hx' (by rw [hx, h0, add_zero])

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- Banach–Mazur closeness is invariant under translating `K₀`. -/
lemma bmClose_translate {K K0 : Set V} {ε : ℝ} (p : V) (h : BMClose K K0 ε) :
    BMClose K ((fun x => x + p) ⁻¹' K0) ε := by
  obtain ⟨T, z, t, h1, h2, h3, h4⟩ := h
  refine ⟨T.trans (AffineEquiv.constVAdd ℝ V (-p)), z - p, t, h1, h2, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := h3 hx
    refine ⟨y, hy, ?_⟩
    simp only [AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add, hyx]
    abel
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hwy⟩ := h4 ⟨y, hy, rfl⟩
    refine ⟨w - p, by simpa using hw, ?_⟩
    simp only [AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add, ← hwy,
      AffineMap.homothety_apply, vsub_eq_sub]
    module

end Plane

section PlaneA

open Room

lemma pow_toContinuousLinearMap (f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (j : ℕ) (x : ℝ × ℝ) :
    (LinearMap.toContinuousLinearMap f ^ j) x = (f ^ j) x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    change (LinearMap.toContinuousLinearMap f ^ j) (f x) = (f ^ j) (f x)
    exact ih _

/-- **Corollary 93 (a)**, given Theorem 91 for `n = 3` in the plane (`Thm91Stmt (ℝ × ℝ) 2`): let
`K₀ ⊂ ℝ²` be a convex body other than a triangle that is mapped onto itself by an affine map
`A ≠ id` with `A³ = id`. There is `ε > 0` such that `U(K)` is `3`-completely mixable for every
convex body `K ⊂ ℝ²` with `δ(K, K₀) < 1 + ε`. (Lemma 92 gives the robustness, Lemma 89 with the
planar asymmetry `as(K₀) < 2` the room.) -/
theorem cor93a (h91 : Thm91Stmt (ℝ × ℝ) 2) {K0 : Set (ℝ × ℝ)} (hK0c : Convex ℝ K0)
    (hK0 : IsCompact K0) (hK0i : (interior K0).Nonempty) (hT : ¬ IsTriangle K0)
    (A : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) (hm : (⇑A)^[3] = id) (hA : ∃ x, A x ≠ x)
    (hAK : A '' K0 = K0) :
    ∃ ε > 0, ∀ K : Set (ℝ × ℝ), Convex ℝ K → IsCompact K → BMClose K K0 ε →
      CompletelyMixable 3 (unifSet K) := by
  have h1 := no_eigen_one_prod A hm hA
  obtain ⟨p, hp, -⟩ := Mixes.exists_unique_fixed A h1
  set K0' := (fun x => x + p) ⁻¹' K0 with hK0'
  set L := LinearMap.toContinuousLinearMap (A.linear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
  have hL3 : L ^ (1 + 2) = 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [pow_toContinuousLinearMap, Mixes.linear_pow_eq_one A hm]; rfl
  have hfix : ∀ x, L x = x → x = 0 := h1
  have hAin : ∀ y, A y ∈ K0 ↔ y ∈ K0 := by
    intro y
    constructor
    · intro hy
      rw [← hAK] at hy
      obtain ⟨y', hy', he⟩ := hy
      rwa [← A.injective he]
    · intro hy; rw [← hAK]; exact ⟨y, hy, rfl⟩
  have hAp : ∀ x, A (x + p) = L x + p := by
    intro x
    rw [SymmCor.affine_lin A (x + p), map_add, add_assoc, ← SymmCor.affine_lin A p, hp]; rfl
  have hLK : L ⁻¹' K0' = K0' := by
    ext x
    simp only [mem_preimage, hK0']
    rw [← hAp, hAin]
  have hfun : (fun x : ℝ × ℝ => x + p) = fun x => p + x := funext fun x => add_comm x p
  have hK'c : Convex ℝ K0' := by
    rw [hK0', hfun]; exact hK0c.translate_preimage_right p
  have hK'k : IsCompact K0' := (Homeomorph.addRight p).isCompact_preimage.2 hK0
  have hK'i : (interior K0').Nonempty := by
    obtain ⟨x, hx⟩ := hK0i
    refine ⟨x - p, ?_⟩
    change x - p ∈ interior ((Homeomorph.addRight p) ⁻¹' K0)
    rw [← (Homeomorph.addRight p).preimage_interior]
    simpa using hx
  have hvol : 0 < volume K0' := by
    obtain ⟨x, hx⟩ := hK'i
    exact (isOpen_interior.measure_pos volume ⟨x, hx⟩).trans_le (measure_mono interior_subset)
  have hT' : ¬ IsTriangle K0' := by
    rintro ⟨a, b, c, habc⟩
    apply hT
    refine ⟨a + p, b + p, c + p, ?_⟩
    have himg : K0 = (fun x => x + p) '' K0' := by
      rw [hK0', image_preimage_eq _ (fun y => ⟨y - p, by simp⟩)]
    have := (AffineEquiv.constVAdd ℝ (ℝ × ℝ) p).toAffineMap.image_convexHull
      ({a, b, c} : Set (ℝ × ℝ))
    simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add,
      image_insert_eq, image_singleton] at this
    rw [himg, habc, hfun, this, add_comm p a, add_comm p b, add_comm p c]
  obtain ⟨a, ha, ha2, hasym⟩ := (planar_asym hK'c hK'k hvol).2 hT'
  have hrob := robust_of_symm L hL3 hfix hK'k hvol hLK
  have hasym' : ∃ a' : ℝ, 0 < a' ∧ a' < ((2 : ℕ) : ℝ) ∧ AsymLE K0' (centroid K0') a' :=
    ⟨a, ha, by push_cast; exact ha2, hasym⟩
  obtain ⟨ε, hε, H⟩ := stable_of_thm91 (m := 2) h91 hK'c hK'k hK'i hasym' hrob
  exact ⟨ε, hε, fun K hKc hK hBM => H K hKc hK (bmClose_translate p hBM)⟩

end PlaneA

/-! ## Corollary 93 (c): the ball in every dimension -/

section BallRobust

open Room

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The construction of Lemma 92 with an arbitrary mixer: if `λ` is a finite permutation-invariant
measure on `𝒯_n(K)` with `λ̄ ≤ M F`, and the measure `ν` with `ν + b λ̄ = F` (`b = 1/(2(M+1))`)
is the common marginal of some measure `γ` on `𝒯_n(K)`, then `β = b λ + Sym γ` is a
permutation-invariant probability on `𝒯_n(K)` with `β̄ = F` and `β ≥ b λ`. -/
theorem robust_core {n : ℕ} (hn : 0 < n) {K : Set V} (hK : MeasurableSet K) (F : Measure V)
    [IsProbabilityMeasure F] (lam : Measure (Fin n → V)) [IsFiniteMeasure lam]
    (hlamP : PermInvariant lam) (hlamT : lam (tuples n K 0)ᶜ = 0) {M : ENNReal} (hM : M ≠ ⊤)
    (hmar : marginal lam ≤ M • F)
    (hmix : ∀ ν : Measure V, ν + (2 * (M + 1))⁻¹ • marginal lam = F →
      ∃ γ : Measure (Fin n → V), γ (tuples n K 0)ᶜ = 0 ∧ ∀ j, γ.map (fun x => x j) = ν) :
    ∃ b : ENNReal, 0 < b ∧ b ≠ ⊤ ∧ ∃ β : Measure (Fin n → V), IsProbabilityMeasure β ∧
      β (tuples n K 0)ᶜ = 0 ∧ PermInvariant β ∧ marginal β = F ∧ b • lam ≤ β := by
  set b : ENNReal := (2 * (M + 1))⁻¹ with hb
  have h2M : 2 * (M + 1) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (by simpa using hM)
  have h2M0 : 2 * (M + 1) ≠ 0 := by simp
  have hbpos : 0 < b := ENNReal.inv_pos.2 h2M
  have hbtop : b ≠ ⊤ := ENNReal.inv_ne_top.2 h2M0
  have hbM : b * M ≤ 1 := by
    calc b * M ≤ b * (2 * (M + 1)) := by
          gcongr
          calc M ≤ M + 1 := le_self_add
            _ ≤ 2 * (M + 1) := by
              calc M + 1 = 1 * (M + 1) := (one_mul _).symm
                _ ≤ 2 * (M + 1) := by gcongr; norm_num
      _ = 1 := ENNReal.inv_mul_cancel h2M0 h2M
  set X := b • marginal lam with hX
  have hXF : X ≤ F := by
    refine Measure.le_iff'.2 fun S => ?_
    calc X S = b * marginal lam S := by rw [hX, smul_apply, smul_eq_mul]
      _ ≤ b * (M * F S) := by
          gcongr
          have := Measure.le_iff'.1 hmar S
          rwa [smul_apply, smul_eq_mul] at this
      _ = (b * M) * F S := (mul_assoc _ _ _).symm
      _ ≤ 1 * F S := by gcongr
      _ = F S := one_mul _
  have hXfin : IsFiniteMeasure X := isFiniteMeasure_of_le F hXF
  set ν := F - X with hν
  have hνX : ν + X = F := Measure.sub_add_cancel_of_le hXF
  obtain ⟨γ, hγT, hγmar⟩ := hmix ν hνX
  set β := b • lam + symmetrise γ with hβ
  have hβP : PermInvariant β :=
    permInvariant_add (permInvariant_smul b hlamP) (permInvariant_symmetrise γ)
  have hβmar : marginal β = F := by
    rw [hβ, marginal_add, marginal_smul,
      marginal_eq_of_permInvariant (permInvariant_symmetrise γ) ⟨0, hn⟩,
      map_eval_symmetrise γ hγmar, ← hX, add_comm, hνX]
  refine ⟨b, hbpos, hbtop, β, ⟨?_⟩, ?_, hβP, hβmar, Measure.le_add_right le_rfl⟩
  · rw [← marginal_univ hn, hβmar, measure_univ]
  · rw [hβ, add_apply, smul_apply, hlamT, smul_zero, zero_add]
    exact symmetrise_null γ (measurableSet_tuples hK 0).compl (tuples_perm K 0) hγT

end BallRobust

section BallC

open Room

/-- A linear isometry preserves every additive Haar measure (it preserves the unit ball). -/
lemma map_isometry_eq (L : E ≃ₗᵢ[ℝ] E) : (volume : Measure E).map L = volume := by
  have hdet : LinearMap.det (L.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hd := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure E)) hdet
  have hB : (L.toLinearEquiv : E →ₗ[ℝ] E) ⁻¹' closedBall 0 1 = closedBall 0 1 := by
    ext x; simp
  have hcoe : ⇑(L.toLinearEquiv : E →ₗ[ℝ] E) = ⇑L := rfl
  have h1 := congrArg (fun μ : Measure E => μ (closedBall 0 1)) hd
  simp only [smul_apply, smul_eq_mul] at h1
  rw [Measure.map_apply (L.toLinearEquiv : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable
    measurableSet_closedBall, hB] at h1
  have hB0 : (volume : Measure E) (closedBall 0 1) ≠ 0 := (measure_closedBall_pos _ _ one_pos).ne'
  have hBt : (volume : Measure E) (closedBall 0 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hc : ENNReal.ofReal |(LinearMap.det (L.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| = 1 :=
    ((ENNReal.mul_left_inj hB0 hBt).1 (by rw [one_mul]; exact h1.symm))
  rw [← hcoe, hd, hc, one_smul]

/-- **Corollary 93 (c), first step: the ball is robustly `n`-completely mixable** for `n = k + 2`
(in `E` of dimension `≥ 2`), given the cited uniqueness of the rotation-invariant distribution on
the sphere (`Ball.SphereUniqueness`, used by Proposition 52): `ν = U(B) - b λ̄` is invariant under
the orthogonal group, hence `n`-completely mixable by Proposition 52, with sum `0`. -/
theorem ball_robust (hU : Ball.SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E) (k : ℕ) :
    centroid (closedBall (0 : E) 1) = 0 ∧ RobustlyCM (k + 1) (closedBall (0 : E) 1) := by
  set B := closedBall (0 : E) 1 with hBdef
  have hBk : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hpos : 0 < volume B := measure_closedBall_pos _ _ one_pos
  have hpre : ∀ L : E ≃ₗᵢ[ℝ] E, (L : E →L[ℝ] E) ⁻¹' B = B := fun L => by
    ext x; simp [hBdef]
  have hvolL : ∀ L : E ≃ₗᵢ[ℝ] E, (volume : Measure E).map (L : E →L[ℝ] E) = volume :=
    fun L => map_isometry_eq L
  -- the centroid is `0`, by the symmetry `x ↦ -x`
  have hc : centroid B = 0 := by
    set N := LinearIsometryEquiv.neg ℝ (E := E)
    have hU' := unifSet_map (N : E →L[ℝ] E) (hvolL N) hBm (hpre N)
    exact centroid_eq_zero (N : E →L[ℝ] E) (fun x hx => by
      have : -x = x := hx
      have h2 : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← this]; simp
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero) hBk hpos hU'
  refine ⟨hc, ?_⟩
  intro ρ _
  rw [hc]
  have := Room.unifSet_isProb hBk hpos
  set lam0 := lebTuples (volume : Measure E) (k + 1) B 0 with hlam0
  have := lebTuples_finite (volume : Measure E) (m := k + 1) hBk 0
  set N : ENNReal := (Fintype.card (Equiv.Perm (Fin (k + 2))) : ENNReal) with hN
  set lam := symmetrise lam0 with hlam
  have hlamfin : IsFiniteMeasure lam := by
    constructor
    rw [hlam, symmetrise_apply _ MeasurableSet.univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by
      rw [pos_iff_ne_zero]; exact card_perm_ne_zero))
      (ENNReal.sum_lt_top.2 fun σ _ => measure_lt_top _ _)
  have hlamL : ∀ L : E ≃ₗᵢ[ℝ] E, lam.map (fun x => ⇑(L : E →L[ℝ] E) ∘ x) = lam := fun L => by
    rw [hlam, symmetrise_diag, hlam0, lebTuples_diag volume hBm (L : E →L[ℝ] E) (hvolL L)
      (hpre L)]
  have hlamT : lam (tuples (k + 2) B 0)ᶜ = 0 :=
    symmetrise_null _ (measurableSet_tuples hBm 0).compl (tuples_perm B 0)
      (lebTuples_null _ hBm 0)
  have hmar : marginal lam ≤ (volume B ^ (k + 1)) • unifSet B := by
    rw [hlam, marginal_symmetrise]
    exact lebTuples_marginal_le volume hBk hpos
  have hUL : ∀ L : E ≃ₗᵢ[ℝ] E, (unifSet B).map (L : E →L[ℝ] E) = unifSet B := fun L =>
    unifSet_map (L : E →L[ℝ] E) (hvolL L) hBm (hpre L)
  obtain ⟨b, hb, hbt, β, h1, h2, h3, h4, h5⟩ := robust_core (n := k + 2) (by omega) hBm
    (unifSet B) lam (permInvariant_symmetrise lam0) hlamT
    (ENNReal.pow_ne_top hBk.measure_lt_top.ne) hmar (by
      intro ν hνX
      set X := (2 * (volume B ^ (k + 1) + 1))⁻¹ • marginal lam with hX
      have hXL : ∀ L : E ≃ₗᵢ[ℝ] E, X.map (L : E →L[ℝ] E) = X := fun L => by
        rw [hX, Measure.map_smul, marginal_map_diag, hlamL L]
        exact (L : E →L[ℝ] E).continuous.measurable.aemeasurable
      have hXF : X ≤ unifSet B := by rw [← hνX]; exact Measure.le_add_left le_rfl
      have hXfin : IsFiniteMeasure X := isFiniteMeasure_of_le _ hXF
      have hνF : ν ≤ unifSet B := by rw [← hνX]; exact Measure.le_add_right le_rfl
      have hνfin : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hνF
      have hνL : ∀ L : E ≃ₗᵢ[ℝ] E, ν.map L = ν := by
        intro L
        have hLm : Measurable (L : E →L[ℝ] E) := (L : E →L[ℝ] E).continuous.measurable
        have h := congrArg (fun μ : Measure E => μ.map (L : E →L[ℝ] E)) hνX
        rw [Measure.map_add _ _ hLm, hXL, hUL, ← hνX] at h
        ext S hS
        have hS' := congrArg (fun μ : Measure E => μ S) h
        simp only [add_apply] at hS'
        exact (ENNReal.add_left_inj (measure_ne_top X S)).1 hS'
      have hνB : ν Bᶜ = 0 := le_antisymm ((Measure.le_iff'.1 hνF _).trans
        (unifSet_compl hBm).le) zero_le
      by_cases hν0 : ν univ = 0
      · refine ⟨0, by simp, fun j => ?_⟩
        rw [Measure.map_zero, (Measure.measure_univ_eq_zero.1 hν0)]
      set P := (ν univ)⁻¹ • ν with hP
      have hνt : ν univ ≠ ⊤ := measure_ne_top _ _
      have hPprob : IsProbabilityMeasure P := ⟨by
        rw [hP, smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hν0 hνt]⟩
      have hPL : Ball.IsRotInv P := fun L => by
        rw [hP, Measure.map_smul, hνL]
        exact L.continuous.measurable.aemeasurable
      have hPB : P Bᶜ = 0 := by rw [hP, smul_apply, hνB, smul_zero]
      obtain ⟨Q, hQp, ⟨s, hs⟩, hQm⟩ :=
        Ball.completelyMixable_of_isRotInv hU hE hPL (n := k + 2) (by omega)
      replace hQm : ∀ j, Q.map (fun x => x j) = P := hQm
      -- the mean of `P` is `0`
      have hPint : Integrable (fun x : E => x) P := by
        refine (integrable_const (1 : ℝ)).mono' aestronglyMeasurable_id ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPB] with x hx
        simp only [mem_compl_iff, not_not] at hx
        simpa [hBdef] using hx
      have hmean : ∫ x, x ∂P = 0 := by
        set Ng := LinearIsometryEquiv.neg ℝ (E := E)
        have h := hPL Ng
        have e : ∫ x, x ∂(P.map Ng) = ∫ x, Ng x ∂P :=
          integral_map Ng.continuous.measurable.aemeasurable aestronglyMeasurable_id
        rw [h] at e
        have e2 : ∫ x, Ng x ∂P = -∫ x, x ∂P := by
          simp only [Ng, LinearIsometryEquiv.coe_neg]
          exact integral_neg _
        rw [e2] at e
        have : (2 : ℝ) • ∫ x, x ∂P = 0 := by rw [two_smul]; nth_rewrite 1 [e]; simp
        exact (smul_eq_zero.1 this).resolve_left two_ne_zero
      have hQint : ∀ j, Integrable (fun x : Fin (k + 2) → E => x j) Q := fun j => by
        have := hPint
        rw [← hQm j] at this
        exact (integrable_map_measure aestronglyMeasurable_id
          (measurable_pi_apply j).aemeasurable).1 this
      have hs0 : s = 0 := by
        have e1 : ∫ x, ∑ j, x j ∂Q = s := by
          rw [integral_congr_ae hs, integral_const, probReal_univ, one_smul]
        rw [integral_finsetSum _ fun j _ => hQint j] at e1
        have e2 : ∀ j, ∫ x, x j ∂Q = 0 := fun j => by
          have := integral_map (μ := Q) (φ := fun x : Fin (k + 2) → E => x j)
            (measurable_pi_apply j).aemeasurable (f := fun y : E => y) aestronglyMeasurable_id
          rw [hQm j] at this
          rw [← this]; exact hmean
        simp only [e2, Finset.sum_const_zero] at e1
        exact e1.symm
      refine ⟨ν univ • Q, ?_, fun j => ?_⟩
      · rw [smul_apply, smul_eq_mul]
        have hcoord : ∀ j, ∀ᵐ x ∂Q, x j ∈ B := fun j => by
          have h := hQm j ▸ hPB
          rw [Measure.map_apply (measurable_pi_apply j) hBm.compl] at h
          exact measure_eq_zero_iff_ae_notMem.1 h |>.mono fun x hx => by
            simpa using hx
        have hall : ∀ᵐ x ∂Q, x ∈ tuples (k + 2) B 0 := by
          filter_upwards [ae_all_iff.2 hcoord, hs] with x hx hxs
          exact ⟨hx, by rw [hxs, hs0, smul_zero]⟩
        rw [show Q (tuples (k + 2) B 0)ᶜ = 0 from ae_iff.1 hall, mul_zero]
      · rw [Measure.map_smul, hQm j, hP, smul_smul, ENNReal.mul_inv_cancel hν0 hνt, one_smul]
        exact (measurable_pi_apply j).aemeasurable)
  refine ⟨b * N⁻¹, ENNReal.mul_pos hb.ne' (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)),
    ENNReal.mul_ne_top hbt (ENNReal.inv_ne_top.2 card_perm_ne_zero), β, h1, h2, h3, h4, ?_⟩
  refine le_trans ?_ h5
  rw [Measure.le_iff]
  intro S hS
  have h6 := Measure.le_iff.1 (le_symmetrise lam0) S hS
  rw [smul_apply, smul_eq_mul] at h6
  have h7 : (lam0.restrict (tuplesRho (k + 1 + 1) B 0 ρ)) S ≤ lam0 S :=
    Measure.restrict_apply_le _ _
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  exact mul_le_mul_right ((mul_le_mul_right h7 _).trans h6) b

/-- **Corollary 93 (c)**, given Theorem 91 (`Thm91Stmt E m` for `m = 2, 3, 4`) and the cited
uniqueness of the rotation-invariant distribution on the sphere (for Proposition 52): in every
dimension `d ≥ 2` there is `ε > 0` such that `U(K)` is `n`-completely mixable for every `n ≥ 3` and
every convex body `K ⊂ E` with `δ(K, B) < 1 + ε`, `B` the unit ball. -/
theorem cor93c (hU : Ball.SphereUniqueness E) (hE : 2 ≤ Module.finrank ℝ E)
    (h91 : ∀ m, 2 ≤ m → Thm91Stmt E m) :
    ∃ ε > 0, ∀ K : Set E, Convex ℝ K → IsCompact K → BMClose K (closedBall 0 1) ε →
      ∀ n, 3 ≤ n → CompletelyMixable n (unifSet K) := by
  obtain ⟨hBc, hBk, hBi⟩ := ball_body (V := E)
  have hst : ∀ k : ℕ, ∃ ε > 0, ∀ K : Set E, Convex ℝ K → IsCompact K →
      BMClose K (closedBall 0 1) ε → CompletelyMixable (k + 3) (unifSet K) := by
    intro k
    obtain ⟨hc, hrob⟩ := ball_robust hU hE (k + 1)
    exact stable_of_thm91 (h91 (k + 2) (by omega)) hBc hBk hBi
      ⟨1, one_pos, by push_cast; linarith, by rw [hc]; exact asymLE_ball⟩ hrob
  obtain ⟨ε3, h3, H3⟩ := hst 0
  obtain ⟨ε4, h4, H4⟩ := hst 1
  obtain ⟨ε5, h5, H5⟩ := hst 2
  refine ⟨min ε3 (min ε4 ε5), lt_min h3 (lt_min h4 h5), fun K hKc hK hBM => ?_⟩
  exact completelyMixable_of_345
    (H3 K hKc hK (bmClose_mono hBM (min_le_left _ _)))
    (H4 K hKc hK (bmClose_mono hBM ((min_le_right _ _).trans (min_le_left _ _))))
    (H5 K hKc hK (bmClose_mono hBM ((min_le_right _ _).trans (min_le_right _ _))))

/-- **Corollary 93 (c)** with the uniqueness on the sphere proved (`Sphere.sphereUniqueness`);
Theorem 91 remains the hypothesis `Thm91Stmt`. -/
theorem cor93c' (hE : 2 ≤ Module.finrank ℝ E) (h91 : ∀ m, 2 ≤ m → Thm91Stmt E m) :
    ∃ ε > 0, ∀ K : Set E, Convex ℝ K → IsCompact K → BMClose K (closedBall 0 1) ε →
      ∀ n, 3 ≤ n → CompletelyMixable n (unifSet K) :=
  cor93c Sphere.sphereUniqueness hE h91

/-- The ball is robustly completely mixable, with the uniqueness on the sphere proved. -/
theorem ball_robust' (hE : 2 ≤ Module.finrank ℝ E) (k : ℕ) :
    centroid (closedBall (0 : E) 1) = 0 ∧ RobustlyCM (k + 1) (closedBall (0 : E) 1) :=
  ball_robust Sphere.sphereUniqueness hE k

end BallC

end Mixes.Robust
