import Mathlib
import Mixes.Decomp
import Mixes.ConcaveMix

/-!
# Peeling a strictly unimodal density (Lemma 33 and Theorem 34)

Section "Peeling a unimodal density" of the paper (`c:lem:L`, `c:thm:peel`), with bridges to
Theorem 35 (`c:thm:decomp`, `Decomp.decomp`) and Corollary 39 (`c:cor:concave`,
`ConcaveMix.cor39`), which are thereby stated without hypotheses on the peeling.

Main results (section `Main`, for `UnimodalDensity f`): `lemma33_*`, `thm34_exists_unique`,
`thm34_C1`, `thm34_a`, `thm34_b`, `thm34_c_left`, `thm34_c_right`, `thm34_d`, `thm35`; and
`cor39`, `cor39_completelyMixable` for concave densities.

Differences from the paper:
* The proofs work with `Hyp f` (`f` continuous on `ℝ`, strictly quasi-concave on `[0, 1]`) and
  are transferred to a density continuous on `[0, 1]` through `ext01 f`; `QCDensity` (strict
  quasi-concavity on `[0, 1]`) covers both strictly unimodal (`UnimodalDensity.qc`) and concave
  (`QCDensity.of_concave`) densities.
* `A(m, U)` and `B(m, U)` are defined by `sInf`/`sSup`; the paper's case definition is
  `Hyp.cutA_of_lam_le`, `Hyp.cutA_of_lt_lam`. `Φ(m, U) = 0` for `m < 0` as in the paper.
* A solution is a function with `m(0) = m₀` and one-sided derivative `-Φ(m(U), U)` on
  `[0, f(μ))`; uniqueness is equality on `[0, f(μ))`.
* Existence is proved without Peano's theorem: Picard–Lindelöf for a mollified right-hand side,
  and a one-sided limit argument that uses only the monotonicity of `Φ` in `m`.
* "Continuously differentiable" for `L` is given as the two partial derivatives plus a uniform
  first-order expansion (`lemma33_differentiable`); for `m`, as continuity of `Φ(m(U), U)`.
* Part (c) is an identity of measures on `(0, f(μ))` (the open interval, which is what Theorem 35
  uses), for any Stieltjes function equal to `A` (resp. `-B`) up to a constant on `[0, f(μ))`.
-/

open Set MeasureTheory Filter Topology intervalIntegral
open scoped Interval

noncomputable section

namespace Mixes.Peel

/-! ## Definitions -/

section Defs

variable (f : ℝ → ℝ)

/-- The mean `μ = ∫₀¹ t f(t) dt`. -/
def mean : ℝ := ∫ t in (0:ℝ)..1, t * f t

/-- The level set `{x ∈ [0,1] : f x ≥ U}`. -/
def lev (U : ℝ) : Set ℝ := {x | x ∈ Icc (0:ℝ) 1 ∧ U ≤ f x}

/-- The left end `a(U)` of the level set. -/
def levA (U : ℝ) : ℝ := sInf (lev f U)

/-- The right end `b(U)` of the level set. -/
def levB (U : ℝ) : ℝ := sSup (lev f U)

/-- `L(x,U) = ∫_x^μ (μ - t) (f t - U)⁺ dt`. -/
def Lf (x U : ℝ) : ℝ := ∫ t in x..mean f, (mean f - t) * max (f t - U) 0

/-- `R(y,U) = ∫_μ^y (t - μ) (f t - U)⁺ dt`. -/
def Rf (y U : ℝ) : ℝ := ∫ t in mean f..y, (t - mean f) * max (f t - U) 0

/-- `λ(U) = L(0,U)`. -/
def lam (U : ℝ) : ℝ := Lf f 0 U

/-- `ρ(U) = R(1,U)`. -/
def rho (U : ℝ) : ℝ := Rf f 1 U

/-- `m₀ = ∫₀¹ (t - μ)⁺ f(t) dt`. -/
def m0 : ℝ := ∫ t in (0:ℝ)..1, max (t - mean f) 0 * f t

/-- `A(m,U)`: the least `x ∈ [a(U), μ]` with `L(x,U) ≤ m` (the paper's case definition is
`cutA_of_lam_le` and `cutA_of_lt_lam`). -/
def cutA (m U : ℝ) : ℝ := sInf {x | x ∈ Icc (levA f U) (mean f) ∧ Lf f x U ≤ m}

/-- `B(m,U)`: the largest `y ∈ [μ, b(U)]` with `R(y,U) ≤ m`. -/
def cutB (m U : ℝ) : ℝ := sSup {y | y ∈ Icc (mean f) (levB f U) ∧ Rf f y U ≤ m}

/-- `Φ(m,U) = ½ max(ℓ(m,U), r(m,U))²`, and `0` for `m < 0`. -/
def Phi (m U : ℝ) : ℝ :=
  if m < 0 then 0 else max (mean f - cutA f m U) (cutB f m U - mean f) ^ 2 / 2

/-- `m` solves the initial value problem `m' = -Φ(m,U)`, `m(0) = m₀` on `[0, f(μ))`
(one-sided derivative at `0`). -/
def IsSol (m : ℝ → ℝ) : Prop :=
  m 0 = m0 f ∧ ∀ U ∈ Ico 0 (f (mean f)), HasDerivWithinAt m (-Phi f (m U) U) (Ici 0) U

end Defs

/-! ## Working hypotheses

`Hyp f`: `f` continuous on `ℝ`, a probability density on `[0,1]`, and strictly quasi-concave on
`[0,1]` in the form `q1`–`q3`, which is what strict unimodality gives. -/

/-- Internal hypotheses. -/
structure Hyp (f : ℝ → ℝ) : Prop where
  cont : Continuous f
  nonneg : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x
  int_one : ∫ x in (0:ℝ)..1, f x = 1
  q1 : ∀ x t y, 0 ≤ x → x ≤ t → t ≤ y → y ≤ 1 → min (f x) (f y) ≤ f t
  q2 : ∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 → f x < f y → f x < f t
  q3 : ∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 → f y < f x → f y < f t

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma intervalIntegrable_mul (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun t => g t * f t) volume a b :=
  (hg.mul h.cont).intervalIntegrable a b

lemma pos : ∀ x ∈ Ioo (0:ℝ) 1, 0 < f x := by
  intro x hx
  by_contra hneg
  push Not at hneg
  have hx0 : f x = 0 := le_antisymm hneg (h.nonneg x (Ioo_subset_Icc_self hx))
  have hz : ∃ z ∈ Icc (0:ℝ) 1, 0 < f z := by
    by_contra hz
    push Not at hz
    have : ∫ t in (0:ℝ)..1, f t ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) (f := fun t => - f t)
        (zero_le_one) (fun t ht => neg_nonneg.2 (hz t ht))
      rw [intervalIntegral.integral_neg] at this
      linarith
    rw [h.int_one] at this
    norm_num at this
  obtain ⟨z, hz, hfz⟩ := hz
  rcases lt_trichotomy z x with hzx | rfl | hxz
  · set y := (x + 1) / 2
    have hxy : x < y := by simp only [y]; linarith [hx.2]
    have hy1 : y ≤ 1 := by simp only [y]; linarith [hx.2]
    have h1 := h.q1 z x y hz.1 hzx.le hxy.le hy1
    have hy0 : 0 ≤ f y := h.nonneg y ⟨by linarith [hx.1], hy1⟩
    have hfy : f y = 0 := by
      rcases min_le_iff.1 h1 with h' | h'
      · linarith
      · linarith
    have := h.q3 z x y hz.1 hzx hxy hy1 (by linarith)
    linarith
  · linarith
  · set y := x / 2
    have hyx : y < x := by simp only [y]; linarith [hx.1]
    have hy0 : 0 ≤ y := by simp only [y]; linarith [hx.1]
    have h1 := h.q1 y x z hy0 hyx.le hxz.le hz.2
    have hfy0 : 0 ≤ f y := h.nonneg y ⟨hy0, by linarith [hx.2]⟩
    have hfy : f y = 0 := by
      rcases min_le_iff.1 h1 with h' | h'
      · linarith
      · linarith
    have := h.q2 y x z hy0 hyx hxz hz.2 (by linarith)
    linarith

lemma mean_pos : 0 < mean f := by
  unfold mean
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact h.intervalIntegrable_mul id continuous_id 0 1
  · intro x hx
    exact mul_pos hx.1 (h.pos x hx)
  · norm_num

lemma one_sub_mean : 1 - mean f = ∫ t in (0:ℝ)..1, (1 - t) * f t := by
  have i1 := h.cont.intervalIntegrable (μ := volume) 0 1
  have i2 : IntervalIntegrable (fun t => t * f t) volume 0 1 :=
    h.intervalIntegrable_mul (fun t => t) continuous_id 0 1
  have e2 : ∫ t in (0:ℝ)..1, (1 - t) * f t
      = (∫ t in (0:ℝ)..1, f t) - ∫ t in (0:ℝ)..1, t * f t := by
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1
    ext t
    ring
  rw [e2, h.int_one]
  rfl

lemma mean_lt_one : mean f < 1 := by
  have e := h.one_sub_mean
  have : 0 < ∫ t in (0:ℝ)..1, (1 - t) * f t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact h.intervalIntegrable_mul (fun t => 1 - t) (by fun_prop) 0 1
    · intro x hx
      exact mul_pos (by linarith [hx.2]) (h.pos x hx)
    · norm_num
  linarith

lemma mean_mem : mean f ∈ Ioo (0:ℝ) 1 := ⟨h.mean_pos, h.mean_lt_one⟩

lemma f_mean_pos : 0 < f (mean f) := h.pos _ h.mean_mem

/-- `∫₀¹ (t - μ) f t = 0`. -/
lemma integral_sub_mean : ∫ t in (0:ℝ)..1, (t - mean f) * f t = 0 := by
  have e : (fun t => (t - mean f) * f t) = fun t => t * f t - mean f * f t := by
    ext t; ring
  have i2 : IntervalIntegrable (fun t => t * f t) volume 0 1 :=
    h.intervalIntegrable_mul (fun t => t) continuous_id 0 1
  rw [e, intervalIntegral.integral_sub i2 ((h.cont.intervalIntegrable 0 1).const_mul _),
    intervalIntegral.integral_const_mul, h.int_one]
  simp [mean]

end Hyp

/-! ## Two elementary facts -/

/-- A derivative bound `|F V - F U - D (V - U)| ≤ k V |V - U|` with `k V → 0` gives `F' = D`. -/
lemma hasDerivAt_of_bound {F : ℝ → ℝ} {D U : ℝ} {k : ℝ → ℝ} (hk : Tendsto k (𝓝 U) (𝓝 0))
    (hb : ∀ᶠ V in 𝓝 U, |F V - F U - D * (V - U)| ≤ k V * |V - U|) : HasDerivAt F D U := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hb, hk.eventually (gt_mem_nhds hc)] with V hV hkV
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, mul_comm (V - U) D]
  exact hV.trans (mul_le_mul_of_nonneg_right hkV.le (abs_nonneg _))

/-- The second elementary fact of the paper: if `g a ≥ 0` and `g' ≥ 0` wherever `g < 0`, then
`g ≥ 0`. -/
lemma nonneg_of_deriv {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioo a b, g x < 0 → 0 ≤ g' x)
    (ha : 0 ≤ g a) : 0 ≤ g b := by
  by_contra hb
  push Not at hb
  set S := {x | x ∈ Icc a b ∧ 0 ≤ g x}
  have hS : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hab⟩, ha⟩
  have hSbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c := sSup S
  have hcS : c ∈ S := hS.csSup_mem hSne hSbdd
  have hcb : c < b := by
    rcases hcS.1.2.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [h'] at hcS; linarith [hcS.2]
  have hneg : ∀ x ∈ Ioc c b, g x < 0 := by
    intro x hx
    by_contra hx'
    push Not at hx'
    have : x ≤ c := le_csSup hSbdd ⟨⟨by linarith [hcS.1.1, hx.1], hx.2⟩, hx'⟩
    linarith [hx.1]
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope g g' hcb
    (hc.mono (Icc_subset_Icc hcS.1.1 le_rfl))
    (fun x hx => hd x ⟨by linarith [hcS.1.1, hx.1], hx.2⟩)
  have h1 : 0 ≤ g' ξ := hpos ξ ⟨by linarith [hcS.1.1, hξ.1], hξ.2⟩ (hneg ξ ⟨hξ.1, hξ.2.le⟩)
  rw [hξd] at h1
  have h2 : 0 ≤ g b - g c := by
    have := div_nonneg_iff.1 h1
    rcases this with ⟨h3, _⟩ | ⟨_, h4⟩
    · exact h3
    · linarith
  linarith [hcS.2]

/-! ## Level sets -/

lemma lev_bddBelow (f : ℝ → ℝ) (U : ℝ) : BddBelow (lev f U) := ⟨0, fun _ hx => hx.1.1⟩

lemma lev_bddAbove (f : ℝ → ℝ) (U : ℝ) : BddAbove (lev f U) := ⟨1, fun _ hx => hx.1.2⟩

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma mean_mem_lev {U : ℝ} (hU : U ≤ f (mean f)) : mean f ∈ lev f U :=
  ⟨⟨h.mean_pos.le, h.mean_lt_one.le⟩, hU⟩

lemma lev_closed (U : ℝ) : IsClosed (lev f U) :=
  isClosed_Icc.inter (isClosed_le continuous_const h.cont)

lemma levA_mem {U : ℝ} (hU : U ≤ f (mean f)) : levA f U ∈ lev f U :=
  (h.lev_closed U).csInf_mem ⟨_, h.mean_mem_lev hU⟩ (lev_bddBelow f U)

lemma levA_nonneg {U : ℝ} (hU : U ≤ f (mean f)) : 0 ≤ levA f U := (h.levA_mem hU).1.1

lemma levA_le_mean {U : ℝ} (hU : U ≤ f (mean f)) : levA f U ≤ mean f :=
  csInf_le (lev_bddBelow f U) (h.mean_mem_lev hU)

lemma le_f_levA {U : ℝ} (hU : U ≤ f (mean f)) : U ≤ f (levA f U) := (h.levA_mem hU).2

lemma f_lt_of_lt_levA {U x : ℝ} (hU : U ≤ f (mean f)) (hx0 : 0 ≤ x) (hx : x < levA f U) :
    f x < U := by
  by_contra hc
  push Not at hc
  have : levA f U ≤ x := csInf_le (lev_bddBelow f U)
    ⟨⟨hx0, by linarith [h.levA_le_mean hU, h.mean_lt_one]⟩, hc⟩
  linarith

lemma lt_f_of_levA_lt {U x : ℝ} (hU : U < f (mean f)) (hx : levA f U < x)
    (hxm : x ≤ mean f) : U < f x := by
  rcases hxm.lt_or_eq with hxm | rfl
  · have ha0 := h.levA_nonneg hU.le
    have hfa := h.le_f_levA hU.le
    rcases hfa.lt_or_eq with hfa | hfa
    · have := h.q1 _ x _ ha0 hx.le hxm.le h.mean_lt_one.le
      exact lt_of_lt_of_le (lt_min hfa hU) this
    · rw [hfa] at hU ⊢
      exact h.q2 _ x _ ha0 hx hxm h.mean_lt_one.le hU
  · exact hU

lemma levA_lt_mean {U : ℝ} (hU : U < f (mean f)) : levA f U < mean f := by
  have hev : ∀ᶠ x in 𝓝 (mean f), U < f x ∧ 0 < x :=
    (continuousAt_const.eventually_lt h.cont.continuousAt hU).and (lt_mem_nhds h.mean_pos)
  obtain ⟨x, hx, hfx, hx0⟩ := hev.exists_lt
  calc levA f U ≤ x := csInf_le (lev_bddBelow f U)
        ⟨⟨hx0.le, by linarith [h.mean_lt_one]⟩, hfx.le⟩
    _ < mean f := hx

lemma f_levA_eq {U : ℝ} (hU : U ≤ f (mean f)) (hpos : 0 < levA f U) : f (levA f U) = U := by
  by_contra hne
  have hlt : U < f (levA f U) := lt_of_le_of_ne (h.le_f_levA hU) (Ne.symm hne)
  have hev : ∀ᶠ x in 𝓝 (levA f U), U < f x ∧ 0 < x :=
    (continuousAt_const.eventually_lt h.cont.continuousAt hlt).and (lt_mem_nhds hpos)
  obtain ⟨x, hx, hfx, hx0⟩ := hev.exists_lt
  have : levA f U ≤ x := csInf_le (lev_bddBelow f U)
    ⟨⟨hx0.le, by linarith [h.levA_le_mean hU, h.mean_lt_one]⟩, hfx.le⟩
  linarith

lemma levA_eq_zero {U : ℝ} (hU : U ≤ f 0) (hU' : U ≤ f (mean f)) : levA f U = 0 :=
  le_antisymm (csInf_le (lev_bddBelow f U) ⟨⟨le_rfl, zero_le_one⟩, hU⟩) (h.levA_nonneg hU')

lemma levA_mono {U U' : ℝ} (hUU' : U ≤ U') (hU' : U' ≤ f (mean f)) : levA f U ≤ levA f U' :=
  csInf_le_csInf (lev_bddBelow f U) ⟨_, h.mean_mem_lev hU'⟩
    (fun _ hx => ⟨hx.1, le_trans hUU' hx.2⟩)

lemma levA_continuousAt {U : ℝ} (hU : U < f (mean f)) : ContinuousAt (levA f) U := by
  rw [ContinuousAt, tendsto_order]
  have hlt := h.levA_lt_mean hU
  constructor
  · intro b hb
    have hev : ∀ᶠ U' in 𝓝 U, U' < f (mean f) := gt_mem_nhds hU
    by_cases hb0 : b < 0
    · filter_upwards [hev] with U' hU'
      exact lt_of_lt_of_le hb0 (h.levA_nonneg hU'.le)
    · push Not at hb0
      set x2 := (b + levA f U) / 2
      have hx2b : b < x2 := by simp only [x2]; linarith
      have hx2a : x2 < levA f U := by simp only [x2]; linarith
      have hfx2 : f x2 < U := h.f_lt_of_lt_levA hU.le (by linarith) hx2a
      filter_upwards [hev, lt_mem_nhds hfx2] with U' hU' hfU'
      refine lt_of_lt_of_le hx2b (le_csInf ⟨_, h.mean_mem_lev hU'.le⟩ ?_)
      intro y hy
      by_contra hyx
      push Not at hyx
      have h1 := h.q1 y x2 (mean f) hy.1.1 hyx.le (by linarith) h.mean_lt_one.le
      have h2 : U' ≤ min (f y) (f (mean f)) := le_min hy.2 hU'.le
      linarith
  · intro b hb
    set x1 := (levA f U + min b (mean f)) / 2
    have hm : levA f U < min b (mean f) := lt_min hb hlt
    have hx1a : levA f U < x1 := by simp only [x1]; linarith
    have hx1b : x1 < min b (mean f) := by simp only [x1]; linarith
    have hx1m : x1 ≤ mean f := le_trans hx1b.le (min_le_right _ _)
    have hfx1 : U < f x1 := h.lt_f_of_levA_lt hU hx1a hx1m
    have ha0 := h.levA_nonneg hU.le
    filter_upwards [gt_mem_nhds hfx1] with U' hU'
    calc levA f U' ≤ x1 := csInf_le (lev_bddBelow f U')
          ⟨⟨by linarith, by linarith [h.mean_lt_one]⟩, hU'.le⟩
      _ < b := lt_of_lt_of_le hx1b (min_le_left _ _)

end Hyp

/-! ## The function `L` (Lemma 33) -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma Lf_integrand_cont (U : ℝ) :
    Continuous fun t => (mean f - t) * max (f t - U) 0 := by
  have := h.cont
  fun_prop

lemma Lf_integrand_cont2 :
    Continuous fun q : (ℝ × ℝ) × ℝ => (mean f - q.2) * max (f q.2 - q.1.2) 0 := by
  have := h.cont
  fun_prop

/-- `L` is continuous (on all of `ℝ²`, hence on `[0,μ] × [0,f(μ)]`). -/
lemma Lf_continuous : Continuous fun p : ℝ × ℝ => Lf f p.1 p.2 := by
  have := continuous_parametric_intervalIntegral_of_continuous (a₀ := mean f) (μ := volume)
    (f := fun (p : ℝ × ℝ) (t : ℝ) => (mean f - t) * max (f t - p.2) 0)
    h.Lf_integrand_cont2 continuous_fst
  convert this.neg using 1
  ext p
  simp only [Lf, Pi.neg_apply]
  rw [integral_symm]

/-- `∂ₓ L(x,U) = -(μ - x) (f x - U)⁺`. -/
lemma Lf_hasDerivAt_x (x U : ℝ) :
    HasDerivAt (fun x => Lf f x U) (-((mean f - x) * max (f x - U) 0)) x :=
  integral_hasDerivAt_left ((h.Lf_integrand_cont U).intervalIntegrable _ _)
    ((h.Lf_integrand_cont U).stronglyMeasurableAtFilter _ _)
    (h.Lf_integrand_cont U).continuousAt

lemma Lf_anti {U x x' : ℝ} (hxx' : x ≤ x') (hx' : x' ≤ mean f) : Lf f x' U ≤ Lf f x U := by
  have i := h.Lf_integrand_cont U
  simp only [Lf]
  rw [← integral_add_adjacent_intervals (a := x) (b := x') (i.intervalIntegrable _ _)
    (i.intervalIntegrable _ _)]
  have : 0 ≤ ∫ t in x..x', (mean f - t) * max (f t - U) 0 :=
    intervalIntegral.integral_nonneg hxx' (fun t ht =>
      mul_nonneg (by linarith [ht.2]) (le_max_right _ _))
  linarith

omit h in
lemma Lf_mean (U : ℝ) : Lf f (mean f) U = 0 := integral_same

/-- The explicit form `L(x,U) = ∫_{max(x,a(U))}^μ (μ - t)(f t - U) dt`. -/
lemma Lf_eq_Q {x U : ℝ} (hU : U < f (mean f)) (hx0 : 0 ≤ x) (hxm : x ≤ mean f) :
    Lf f x U = ∫ t in max x (levA f U)..mean f, (mean f - t) * (f t - U) := by
  set y := max x (levA f U) with hy
  have hxy : x ≤ y := le_max_left _ _
  have hym : y ≤ mean f := max_le hxm (h.levA_le_mean hU.le)
  have i := h.Lf_integrand_cont U
  simp only [Lf]
  rw [← integral_add_adjacent_intervals (b := y) (i.intervalIntegrable _ _)
    (i.intervalIntegrable _ _)]
  have hz : ∫ t in x..y, (mean f - t) * max (f t - U) 0 = 0 := by
    rcases eq_or_lt_of_le hxy with hxy' | hxy'
    · rw [hxy', integral_same]
    · have hyA : y = levA f U := by
        rcases le_total x (levA f U) with h' | h'
        · exact max_eq_right h'
        · exfalso; rw [hy, max_eq_left h'] at hxy'; exact lt_irrefl _ hxy'
      have hfa : f (levA f U) = U := h.f_levA_eq hU.le (by rw [← hyA]; linarith)
      rw [integral_congr (g := fun _ => (0:ℝ))]
      · simp
      intro t ht
      rw [uIcc_of_le hxy] at ht
      simp only
      rcases ht.2.lt_or_eq with htl | hte
      · have := h.f_lt_of_lt_levA hU.le (by linarith [ht.1]) (hyA ▸ htl)
        rw [max_eq_right (by linarith)]
        ring
      · rw [hte, hyA, hfa]
        simp
  rw [hz, zero_add]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le hym] at ht
  simp only
  rw [max_eq_left]
  rcases ((le_max_right x (levA f U)).trans ht.1).lt_or_eq with hlt | heq
  · linarith [h.lt_f_of_levA_lt hU hlt ht.2]
  · rw [← heq]
    linarith [h.le_f_levA hU.le]

omit h in
lemma int_mean_sub (y : ℝ) : ∫ t in y..mean f, (mean f - t) = (mean f - y) ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  ring

lemma Q_sub_U (y U U' : ℝ) :
    (∫ t in y..mean f, (mean f - t) * (f t - U')) - ∫ t in y..mean f, (mean f - t) * (f t - U)
      = -((U' - U) * ((mean f - y) ^ 2 / 2)) := by
  have hc : ∀ V, Continuous fun t => (mean f - t) * (f t - V) := by
    intro V; have := h.cont; fun_prop
  rw [← intervalIntegral.integral_sub ((hc U').intervalIntegrable _ _)
    ((hc U).intervalIntegrable _ _), ← int_mean_sub (f := f) y,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg]
  congr 1
  ext t
  ring

lemma Q_sub_y (y y' U : ℝ) :
    (∫ t in y..mean f, (mean f - t) * (f t - U)) - ∫ t in y'..mean f, (mean f - t) * (f t - U)
      = ∫ t in y..y', (mean f - t) * (f t - U) := by
  have hc : Continuous fun t => (mean f - t) * (f t - U) := by have := h.cont; fun_prop
  rw [← integral_add_adjacent_intervals (b := y') (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  ring

/-- `|f t - U'| ≤ |U' - U|` between `max(x,a(U))` and `max(x,a(U'))`. -/
lemma level_bound {x U U' t : ℝ} (hx0 : 0 ≤ x) (hU : U < f (mean f)) (hU' : U' < f (mean f))
    (ht : t ∈ Ι (max x (levA f U)) (max x (levA f U'))) : |f t - U'| ≤ |U' - U| := by
  have hm : max x (levA f U) ≤ mean f ∨ True := Or.inr trivial
  clear hm
  rcases le_total U U' with hle | hle
  · have hmono := h.levA_mono hle hU'.le
    have hyy : max x (levA f U) ≤ max x (levA f U') := max_le_max le_rfl hmono
    rw [uIoc_of_le hyy] at ht
    have hy'A : max x (levA f U') = levA f U' := by
      rcases le_total x (levA f U') with h' | h'
      · exact max_eq_right h'
      · exfalso
        rw [max_eq_left h'] at ht
        linarith [ht.1, ht.2, le_max_left x (levA f U)]
    have htm : t ≤ mean f := by linarith [ht.2, h.levA_le_mean hU'.le]
    have hlow : U < f t := h.lt_f_of_levA_lt hU (lt_of_le_of_lt (le_max_right _ _) ht.1) htm
    have hup : f t ≤ U' := by
      rw [hy'A] at ht
      rcases ht.2.lt_or_eq with hlt | heq
      · exact (h.f_lt_of_lt_levA hU'.le (by linarith [ht.1, le_max_left x (levA f U)]) hlt).le
      · rw [heq, h.f_levA_eq hU'.le (by linarith [ht.1, le_max_left x (levA f U)])]
    rw [abs_le, abs_of_nonneg (by linarith)]
    constructor <;> linarith
  · have hmono := h.levA_mono hle hU.le
    have hyy : max x (levA f U') ≤ max x (levA f U) := max_le_max le_rfl hmono
    rw [uIoc_comm, uIoc_of_le hyy] at ht
    have hyA : max x (levA f U) = levA f U := by
      rcases le_total x (levA f U) with h' | h'
      · exact max_eq_right h'
      · exfalso
        rw [max_eq_left h'] at ht
        linarith [ht.1, ht.2, le_max_left x (levA f U')]
    have htm : t ≤ mean f := by linarith [ht.2, h.levA_le_mean hU.le]
    have hlow : U' < f t := h.lt_f_of_levA_lt hU' (lt_of_le_of_lt (le_max_right _ _) ht.1) htm
    have hup : f t ≤ U := by
      rw [hyA] at ht
      rcases ht.2.lt_or_eq with hlt | heq
      · exact (h.f_lt_of_lt_levA hU.le (by linarith [ht.1, le_max_left x (levA f U')]) hlt).le
      · rw [heq, h.f_levA_eq hU.le (by linarith [ht.1, le_max_left x (levA f U')])]
    rw [abs_le, abs_of_nonpos (by linarith)]
    constructor <;> linarith

/-- `∂_U L(x,U) = -½ (μ - max(x, a(U)))²` for `0 ≤ x ≤ μ` and `U < f(μ)`. -/
lemma Lf_hasDerivAt_U {x U : ℝ} (hx0 : 0 ≤ x) (hxm : x ≤ mean f) (hU : U < f (mean f)) :
    HasDerivAt (fun U => Lf f x U) (-((mean f - max x (levA f U)) ^ 2 / 2)) U := by
  set k : ℝ → ℝ := fun V => mean f * |max x (levA f V) - max x (levA f U)|
  have hk : Tendsto k (𝓝 U) (𝓝 0) := by
    have hc : ContinuousAt (fun V => max x (levA f V)) U :=
      continuousAt_const.max (h.levA_continuousAt hU)
    have : Tendsto (fun V => mean f * |max x (levA f V) - max x (levA f U)|) (𝓝 U)
        (𝓝 (mean f * |max x (levA f U) - max x (levA f U)|)) :=
      tendsto_const_nhds.mul ((hc.sub continuousAt_const).abs)
    simpa using this
  apply hasDerivAt_of_bound hk
  filter_upwards [gt_mem_nhds hU] with V hV
  rw [h.Lf_eq_Q hV hx0 hxm, h.Lf_eq_Q hU hx0 hxm]
  set y := max x (levA f U)
  set y' := max x (levA f V)
  have e1 := h.Q_sub_U y U V
  have e2 := h.Q_sub_y y y' V
  have hint : |∫ t in y..y', (mean f - t) * (f t - V)| ≤ mean f * |V - U| * |y' - y| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := y')
      (C := mean f * |V - U|) (f := fun t => (mean f - t) * (f t - V)) ?_
    · simpa [Real.norm_eq_abs] using this
    intro t ht
    have hy0 : 0 ≤ min y y' := le_min (le_trans hx0 (le_max_left _ _))
      (le_trans hx0 (le_max_left _ _))
    have hym : max y y' ≤ mean f := max_le (max_le hxm (h.levA_le_mean hU.le))
      (max_le hxm (h.levA_le_mean hV.le))
    have ht0 : 0 ≤ t := le_trans hy0 ht.1.le
    have htm : t ≤ mean f := le_trans ht.2 hym
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul _ (h.level_bound hx0 hU hV ht) (abs_nonneg _) h.mean_pos.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  have : (∫ t in y'..mean f, (mean f - t) * (f t - V)) - (∫ t in y..mean f,
      (mean f - t) * (f t - U)) - -((mean f - y) ^ 2 / 2) * (V - U)
      = -∫ t in y..y', (mean f - t) * (f t - V) := by linarith
  rw [this, abs_neg]
  calc _ ≤ mean f * |V - U| * |y' - y| := hint
    _ = k V * |V - U| := by simp only [k]; ring

/-- `L(·,U)` equals `λ(U)` on `[0, a(U)]`. -/
lemma Lf_eq_lam {x U : ℝ} (hU : U < f (mean f)) (hx0 : 0 ≤ x) (hxa : x ≤ levA f U) :
    Lf f x U = lam f U := by
  have ha := h.levA_le_mean hU.le
  rw [lam, h.Lf_eq_Q hU hx0 (hxa.trans ha), h.Lf_eq_Q hU le_rfl h.mean_pos.le,
    max_eq_right hxa, max_eq_right (h.levA_nonneg hU.le)]

/-- `L(·,U)` is strictly decreasing on `[a(U), μ]`. -/
lemma Lf_strictAnti {U : ℝ} (hU : U < f (mean f)) :
    StrictAntiOn (fun x => Lf f x U) (Icc (levA f U) (mean f)) := by
  intro x hx x' hx' hxx'
  have ha0 := h.levA_nonneg hU.le
  simp only
  rw [h.Lf_eq_Q hU (ha0.trans hx.1) hx.2, h.Lf_eq_Q hU (ha0.trans hx'.1) hx'.2,
    max_eq_left hx.1, max_eq_left hx'.1]
  have e := h.Q_sub_y x x' U
  have : 0 < ∫ t in x..x', (mean f - t) * (f t - U) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · have hc : Continuous fun t => (mean f - t) * (f t - U) := by have := h.cont; fun_prop
      exact hc.intervalIntegrable _ _
    · intro t ht
      exact mul_pos (by linarith [ht.2, hx'.2])
        (by linarith [h.lt_f_of_levA_lt hU (lt_of_le_of_lt hx.1 ht.1) (by linarith [ht.2, hx'.2])])
    · exact hxx'
  linarith

lemma lam_pos {U : ℝ} (hU : U < f (mean f)) : 0 < lam f U := by
  have ha := h.levA_lt_mean hU
  rw [← h.Lf_eq_lam hU (h.levA_nonneg hU.le) le_rfl, ← Lf_mean (f := f) U]
  exact h.Lf_strictAnti hU ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩ ha

lemma lam_hasDerivAt {U : ℝ} (hU : U < f (mean f)) :
    HasDerivAt (lam f) (-((mean f - levA f U) ^ 2 / 2)) U := by
  have := h.Lf_hasDerivAt_U le_rfl h.mean_pos.le hU
  rwa [max_eq_right (h.levA_nonneg hU.le)] at this

end Hyp

/-! ## The function `A(m,U)` -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma Lf_cont_x (U : ℝ) : Continuous fun x => Lf f x U :=
  h.Lf_continuous.comp₂ continuous_id continuous_const

lemma Lf_cont_U (x : ℝ) : Continuous fun U => Lf f x U :=
  h.Lf_continuous.comp₂ continuous_const continuous_id

lemma cutA_set_closed (m U : ℝ) :
    IsClosed {x | x ∈ Icc (levA f U) (mean f) ∧ Lf f x U ≤ m} :=
  isClosed_Icc.inter (isClosed_le (h.Lf_cont_x U) continuous_const)

omit h in
lemma cutA_set_bdd (m U : ℝ) :
    BddBelow {x | x ∈ Icc (levA f U) (mean f) ∧ Lf f x U ≤ m} := ⟨levA f U, fun _ hx => hx.1.1⟩

lemma mean_mem_cutA_set {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    mean f ∈ {x | x ∈ Icc (levA f U) (mean f) ∧ Lf f x U ≤ m} :=
  ⟨⟨h.levA_le_mean hU.le, le_rfl⟩, by rw [Lf_mean]; exact hm⟩

lemma cutA_mem {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    cutA f m U ∈ {x | x ∈ Icc (levA f U) (mean f) ∧ Lf f x U ≤ m} :=
  (h.cutA_set_closed m U).csInf_mem ⟨_, h.mean_mem_cutA_set hm hU⟩ (cutA_set_bdd m U)

lemma levA_le_cutA {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) : levA f U ≤ cutA f m U :=
  (h.cutA_mem hm hU).1.1

lemma cutA_le_mean {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) : cutA f m U ≤ mean f :=
  (h.cutA_mem hm hU).1.2

lemma cutA_nonneg {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) : 0 ≤ cutA f m U :=
  (h.levA_nonneg hU.le).trans (h.levA_le_cutA hm hU)

omit h in
lemma cutA_le_of {m U x : ℝ} (hx : x ∈ Icc (levA f U) (mean f)) (hLx : Lf f x U ≤ m) :
    cutA f m U ≤ x :=
  csInf_le (cutA_set_bdd m U) ⟨hx, hLx⟩

lemma Lf_cutA_of_levA_lt {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f))
    (hlt : levA f U < cutA f m U) : Lf f (cutA f m U) U = m := by
  have hc := h.cutA_mem hm hU
  refine le_antisymm hc.2 ?_
  by_contra hlt'
  push Not at hlt'
  have hev : ∀ᶠ x in 𝓝 (cutA f m U), Lf f x U < m ∧ levA f U < x :=
    (((h.Lf_cont_x U).continuousAt).eventually_lt continuousAt_const hlt').and (lt_mem_nhds hlt)
  obtain ⟨x, hxc, hx1, hx2⟩ := hev.exists_lt
  have := cutA_le_of ⟨hx2.le, by linarith [hc.1.2]⟩ hx1.le
  linarith

/-- `L(A(m,U),U) = min(m, λ(U))`. -/
lemma Lf_cutA {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    Lf f (cutA f m U) U = min m (lam f U) := by
  have hc := h.cutA_mem hm hU
  have ha0 := h.levA_nonneg hU.le
  have ham := h.levA_le_mean hU.le
  rcases hc.1.1.lt_or_eq with hlt | heq
  · have heq' := h.Lf_cutA_of_levA_lt hm hU hlt
    have : m < lam f U := by
      rw [← heq', ← h.Lf_eq_lam hU ha0 le_rfl]
      exact h.Lf_strictAnti hU ⟨le_rfl, ham⟩ hc.1 hlt
    rw [heq', min_eq_left this.le]
  · have h2 := hc.2
    rw [← heq, h.Lf_eq_lam hU ha0 le_rfl] at h2 ⊢
    rw [min_eq_right h2]

/-- Paper's definition, first case: `A(m,U) = a(U)` if `m ≥ λ(U)`. -/
lemma cutA_of_lam_le {m U : ℝ} (hU : U < f (mean f)) (hlam : lam f U ≤ m) :
    cutA f m U = levA f U := by
  have hm : 0 ≤ m := (h.lam_pos hU).le.trans hlam
  refine le_antisymm (cutA_le_of ⟨le_rfl, h.levA_le_mean hU.le⟩ ?_) (h.levA_le_cutA hm hU)
  rw [h.Lf_eq_lam hU (h.levA_nonneg hU.le) le_rfl]
  exact hlam

/-- Paper's definition, second case: for `0 ≤ m < λ(U)`, `A(m,U)` is the unique
`x ∈ (a(U), μ]` with `L(x,U) = m`. -/
lemma cutA_of_lt_lam {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) (hlt : m < lam f U) :
    cutA f m U ∈ Ioc (levA f U) (mean f) ∧ Lf f (cutA f m U) U = m ∧
      ∀ x ∈ Ioc (levA f U) (mean f), Lf f x U = m → x = cutA f m U := by
  have hc := h.cutA_mem hm hU
  have hL := h.Lf_cutA hm hU
  rw [min_eq_left hlt.le] at hL
  have hgt : levA f U < cutA f m U := by
    rcases hc.1.1.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [← h', h.Lf_eq_lam hU (h.levA_nonneg hU.le) le_rfl] at hL
      linarith
  refine ⟨⟨hgt, hc.1.2⟩, hL, fun x hx hLx => ?_⟩
  exact (h.Lf_strictAnti hU).injOn ⟨hx.1.le, hx.2⟩ hc.1 (hLx.trans hL.symm)

lemma cutA_zero {U : ℝ} (hU : U < f (mean f)) : cutA f 0 U = mean f := by
  have hc := h.cutA_mem le_rfl hU
  have hL := h.Lf_cutA le_rfl hU
  rw [min_eq_left (h.lam_pos hU).le] at hL
  exact (h.Lf_strictAnti hU).injOn hc.1 ⟨h.levA_le_mean hU.le, le_rfl⟩
    (hL.trans (Lf_mean (f := f) U).symm)

lemma cutA_lt_mean {m U : ℝ} (hm : 0 < m) (hU : U < f (mean f)) : cutA f m U < mean f := by
  rcases (h.cutA_le_mean hm.le hU).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have hL := h.Lf_cutA hm.le hU
    rw [h', Lf_mean] at hL
    have := lt_min hm (h.lam_pos hU)
    linarith

lemma cutA_anti {m m' U : ℝ} (hm : 0 ≤ m) (hmm' : m ≤ m') (hU : U < f (mean f)) :
    cutA f m' U ≤ cutA f m U :=
  csInf_le_csInf (cutA_set_bdd m' U) ⟨_, h.mean_mem_cutA_set hm hU⟩
    (fun _ hx => ⟨hx.1, hx.2.trans hmm'⟩)

/-- `A` is continuous on `[0,∞) × (-∞, f(μ))`. -/
lemma cutA_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => cutA f p.1 p.2) (Ici 0 ×ˢ Iio (f (mean f))) := by
  rintro ⟨m, U⟩ ⟨hm, hU⟩
  simp only [mem_Ici, mem_Iio] at hm hU
  have hca : ContinuousAt (fun p : ℝ × ℝ => levA f p.2) (m, U) :=
    ContinuousAt.comp (g := levA f) (f := Prod.snd) (h.levA_continuousAt hU)
      continuous_snd.continuousAt
  rw [ContinuousWithinAt, tendsto_order]
  have hS : ∀ᶠ p in 𝓝[Ici 0 ×ˢ Iio (f (mean f))] (m, U),
      0 ≤ p.1 ∧ p.2 < f (mean f) :=
    eventually_nhdsWithin_of_forall (fun p hp => ⟨hp.1, hp.2⟩)
  have hc := h.cutA_mem hm hU
  set c := cutA f m U
  constructor
  · intro b hb
    rcases hc.1.1.lt_or_eq with hlt | heq
    · set x2 := max ((b + c) / 2) ((levA f U + c) / 2)
      have hx2c : x2 < c := max_lt (by linarith) (by linarith)
      have hbx2 : b < x2 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hax2 : levA f U ≤ x2 := le_trans (by linarith) (le_max_right _ _)
      have hLc := h.Lf_cutA_of_levA_lt hm hU hlt
      have hL2 : m < Lf f x2 U := by
        rw [← hLc]
        exact h.Lf_strictAnti hU ⟨hax2, hx2c.le.trans hc.1.2⟩ hc.1 hx2c
      have hcont : ContinuousAt (fun p : ℝ × ℝ => Lf f x2 p.2 - p.1) (m, U) :=
        ((h.Lf_continuous.comp (continuous_const.prodMk continuous_snd)).sub
          continuous_fst).continuousAt
      have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (m, U), 0 < Lf f x2 p.2 - p.1 :=
        hcont.eventually (lt_mem_nhds (by simp only; linarith))
      filter_upwards [hS, nhdsWithin_le_nhds hev] with p hp hp2
      refine lt_of_lt_of_le hbx2 (le_csInf ⟨_, h.mean_mem_cutA_set hp.1 hp.2⟩ ?_)
      intro y hy
      by_contra hyx
      push Not at hyx
      have := h.Lf_anti (U := p.2) hyx.le (hx2c.le.trans hc.1.2)
      linarith [hy.2]
    · have hb' : b < levA f U := by rw [heq]; exact hb
      have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (m, U), b < levA f p.2 := hca.eventually (lt_mem_nhds hb')
      filter_upwards [hS, nhdsWithin_le_nhds hev] with p hp hp2
      exact lt_of_lt_of_le hp2 (h.levA_le_cutA hp.1 hp.2)
  · intro b hb
    by_cases hbm : mean f < b
    · filter_upwards [hS] with p hp
      exact lt_of_le_of_lt (h.cutA_le_mean hp.1 hp.2) hbm
    · push Not at hbm
      set x1 := (c + b) / 2
      have hcx1 : c < x1 := by simp only [x1]; linarith
      have hx1b : x1 < b := by simp only [x1]; linarith
      have hL1 : Lf f x1 U < m := by
        have := h.Lf_strictAnti hU hc.1 ⟨hc.1.1.trans hcx1.le, by linarith⟩ hcx1
        have h2 := h.Lf_cutA hm hU
        simp only at this
        linarith [min_le_left m (lam f U)]
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 - Lf f x1 p.2) (m, U) :=
        (continuous_fst.sub (h.Lf_continuous.comp
          (continuous_const.prodMk continuous_snd))).continuousAt
      have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (m, U), 0 < p.1 - Lf f x1 p.2 :=
        hcont.eventually (lt_mem_nhds (by simp only; linarith))
      have hev2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (m, U), levA f p.2 < x1 :=
        hca.eventually (gt_mem_nhds (lt_of_le_of_lt hc.1.1 hcx1))
      filter_upwards [hS, nhdsWithin_le_nhds hev, nhdsWithin_le_nhds hev2] with p hp hp2 hp3
      exact lt_of_le_of_lt (cutA_le_of ⟨hp3.le, by linarith⟩ (by linarith)) hx1b

end Hyp

/-! ## Reflection `x ↦ 1 - x`

The right-hand objects `R`, `b`, `B` of `f` are the left-hand objects of `x ↦ f(1 - x)`. -/

/-- The reflected function `x ↦ f(1 - x)`. -/
def refl (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (1 - x)

lemma refl_refl (f : ℝ → ℝ) : refl (refl f) = f := by
  funext x; simp [refl]

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma refl_hyp : Hyp (refl f) where
  cont := h.cont.comp (continuous_const.sub continuous_id)
  nonneg x hx := h.nonneg (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  int_one := by
    simp only [refl]
    rw [intervalIntegral.integral_comp_sub_left (fun x => f x)]
    simpa using h.int_one
  q1 x t y hx hxt hty hy := by
    simp only [refl]
    rw [min_comm]
    exact h.q1 (1 - y) (1 - t) (1 - x) (by linarith) (by linarith) (by linarith) (by linarith)
  q2 x t y hx hxt hty hy hlt := by
    simp only [refl] at hlt ⊢
    exact h.q3 (1 - y) (1 - t) (1 - x) (by linarith) (by linarith) (by linarith) (by linarith) hlt
  q3 x t y hx hxt hty hy hlt := by
    simp only [refl] at hlt ⊢
    exact h.q2 (1 - y) (1 - t) (1 - x) (by linarith) (by linarith) (by linarith) (by linarith) hlt

lemma mean_refl : mean (refl f) = 1 - mean f := by
  have e : (fun t => t * refl f t) = fun t => (fun s => (1 - s) * f s) (1 - t) := by
    funext t; simp [refl]
  unfold mean
  rw [e, intervalIntegral.integral_comp_sub_left (fun s => (1 - s) * f s)]
  norm_num
  exact h.one_sub_mean.symm

lemma f_refl_mean : refl f (mean (refl f)) = f (mean f) := by
  simp [refl, h.mean_refl]

lemma Lf_refl (x U : ℝ) : Lf (refl f) x U = Rf f (1 - x) U := by
  have e : (fun t => (mean (refl f) - t) * max (refl f t - U) 0)
      = fun t => (fun s => (s - mean f) * max (f s - U) 0) (1 - t) := by
    funext t; simp only [refl, h.mean_refl]; ring_nf
  unfold Lf
  rw [e, intervalIntegral.integral_comp_sub_left (fun s => (s - mean f) * max (f s - U) 0),
    h.mean_refl, sub_sub_cancel]
  rfl

lemma Rf_refl (y U : ℝ) : Rf (refl f) y U = Lf f (1 - y) U := by
  have := h.refl_hyp.Lf_refl (1 - y) U
  rw [refl_refl, sub_sub_cancel] at this
  exact this.symm

omit h in
lemma lev_refl (U : ℝ) : lev (refl f) U = (fun x => 1 - x) '' lev f U := by
  ext x
  constructor
  · rintro ⟨⟨h0, h1⟩, hU⟩
    exact ⟨1 - x, ⟨⟨by linarith, by linarith⟩, hU⟩, by ring⟩
  · rintro ⟨y, ⟨⟨h0, h1⟩, hU⟩, rfl⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp only [refl, sub_sub_cancel]
    exact hU

lemma levA_refl {U : ℝ} (hU : U ≤ f (mean f)) : levA (refl f) U = 1 - levB f U := by
  rw [levA, lev_refl, levB]
  exact (Antitone.map_csSup_of_continuousAt (f := fun x : ℝ => 1 - x)
    (continuous_const.sub continuous_id).continuousAt (fun a b hab => by simp only; linarith)
    ⟨_, h.mean_mem_lev hU⟩ (lev_bddAbove f U)).symm

lemma levB_refl {U : ℝ} (hU : U ≤ f (mean f)) : levB (refl f) U = 1 - levA f U := by
  have := h.refl_hyp.levA_refl (U := U) (by rw [h.f_refl_mean]; exact hU)
  rw [refl_refl] at this
  linarith

lemma mean_le_levB {U : ℝ} (hU : U ≤ f (mean f)) : mean f ≤ levB f U :=
  le_csSup (lev_bddAbove f U) (h.mean_mem_lev hU)

lemma cutA_refl {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    cutA (refl f) m U = 1 - cutB f m U := by
  have hset : {x | x ∈ Icc (levA (refl f) U) (mean (refl f)) ∧ Lf (refl f) x U ≤ m}
      = (fun x => 1 - x) '' {y | y ∈ Icc (mean f) (levB f U) ∧ Rf f y U ≤ m} := by
    ext x
    simp only [mem_image, mem_Icc, h.levA_refl hU.le, h.mean_refl, h.Lf_refl]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨1 - x, ⟨⟨by linarith, by linarith⟩, h3⟩, by ring⟩
    · rintro ⟨y, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rwa [sub_sub_cancel]
  have hne : ({y | y ∈ Icc (mean f) (levB f U) ∧ Rf f y U ≤ m} : Set ℝ).Nonempty :=
    ⟨mean f, ⟨le_rfl, h.mean_le_levB hU.le⟩, by simp [Rf, hm]⟩
  have hbdd : BddAbove ({y | y ∈ Icc (mean f) (levB f U) ∧ Rf f y U ≤ m} : Set ℝ) :=
    ⟨levB f U, fun _ hy => hy.1.2⟩
  rw [cutA, hset, cutB]
  exact (Antitone.map_csSup_of_continuousAt (f := fun x : ℝ => 1 - x)
    (continuous_const.sub continuous_id).continuousAt (fun a b hab => by simp only; linarith)
    hne hbdd).symm

lemma cutB_eq {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    cutB f m U = 1 - cutA (refl f) m U := by
  rw [h.cutA_refl hm hU]; ring

lemma cutB_refl {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    cutB (refl f) m U = 1 - cutA f m U := by
  have := h.refl_hyp.cutB_eq hm (U := U) (by rw [h.f_refl_mean]; exact hU)
  rwa [refl_refl] at this

lemma Phi_refl {U : ℝ} (hU : U < f (mean f)) (m : ℝ) : Phi (refl f) m U = Phi f m U := by
  unfold Phi
  split_ifs with hm
  · rfl
  · push Not at hm
    rw [h.mean_refl, h.cutA_refl hm hU, h.cutB_refl hm hU]
    have e1 : 1 - mean f - (1 - cutB f m U) = cutB f m U - mean f := by ring
    have e2 : 1 - cutA f m U - (1 - mean f) = mean f - cutA f m U := by ring
    rw [e1, e2, max_comm]

lemma lam_refl (U : ℝ) : lam (refl f) U = rho f U := by
  rw [lam, h.Lf_refl, sub_zero]; rfl

lemma rho_refl (U : ℝ) : rho (refl f) U = lam f U := by
  rw [rho, h.Rf_refl, sub_self]; rfl

lemma rho_zero : rho f 0 = ∫ t in mean f..1, (t - mean f) * f t := by
  unfold rho Rf
  apply integral_congr
  intro t ht
  rw [uIcc_of_le h.mean_lt_one.le] at ht
  simp only [sub_zero]
  rw [max_eq_left (h.nonneg t ⟨h.mean_pos.le.trans ht.1, ht.2⟩)]

lemma lam_zero : lam f 0 = ∫ t in (0:ℝ)..mean f, (mean f - t) * f t := by
  unfold lam Lf
  apply integral_congr
  intro t ht
  rw [uIcc_of_le h.mean_pos.le] at ht
  simp only [sub_zero]
  rw [max_eq_left (h.nonneg t ⟨ht.1, ht.2.trans h.mean_lt_one.le⟩)]

lemma m0_eq_rho : m0 f = rho f 0 := by
  have hc : Continuous fun t => max (t - mean f) 0 * f t := by have := h.cont; fun_prop
  unfold m0
  rw [← integral_add_adjacent_intervals (b := mean f) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h.rho_zero]
  have z : ∫ t in (0:ℝ)..mean f, max (t - mean f) 0 * f t = 0 := by
    rw [integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro t ht
    rw [uIcc_of_le h.mean_pos.le] at ht
    simp only
    rw [max_eq_right (by linarith [ht.2])]
    ring
  rw [z, zero_add]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le h.mean_lt_one.le] at ht
  simp only
  rw [max_eq_left (by linarith [ht.1])]

lemma lam_zero_eq_rho_zero : lam f 0 = rho f 0 := by
  have hc : Continuous fun t => (t - mean f) * f t := by have := h.cont; fun_prop
  have := h.integral_sub_mean
  rw [← integral_add_adjacent_intervals (b := mean f) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)] at this
  rw [h.lam_zero, h.rho_zero]
  have e : ∫ t in (0:ℝ)..mean f, (mean f - t) * f t
      = -∫ t in (0:ℝ)..mean f, (t - mean f) * f t := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext t
    ring
  linarith

lemma m0_eq_lam : m0 f = lam f 0 := by rw [h.m0_eq_rho, h.lam_zero_eq_rho_zero]

lemma m0_refl : m0 (refl f) = m0 f := by
  rw [h.refl_hyp.m0_eq_rho, h.rho_refl, h.m0_eq_lam]

lemma isSol_refl {m : ℝ → ℝ} : IsSol (refl f) m ↔ IsSol f m := by
  unfold IsSol
  rw [h.m0_refl, h.f_refl_mean]
  constructor
  · rintro ⟨h0, hd⟩
    refine ⟨h0, fun U hU => ?_⟩
    have := hd U hU
    rwa [h.Phi_refl hU.2] at this
  · rintro ⟨h0, hd⟩
    refine ⟨h0, fun U hU => ?_⟩
    rw [h.Phi_refl hU.2]
    exact hd U hU

end Hyp

/-! ## The function `B(m,U)` and the field `Φ` -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma cutB_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => cutB f p.1 p.2) (Ici 0 ×ˢ Iio (f (mean f))) := by
  have := h.refl_hyp.cutA_continuousOn
  rw [h.f_refl_mean] at this
  exact (continuousOn_const.sub this).congr (fun p hp => h.cutB_eq hp.1 hp.2)

lemma cutB_zero {U : ℝ} (hU : U < f (mean f)) : cutB f 0 U = mean f := by
  rw [h.cutB_eq le_rfl hU, h.refl_hyp.cutA_zero (by rw [h.f_refl_mean]; exact hU), h.mean_refl]
  ring

lemma mean_le_cutB {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) : mean f ≤ cutB f m U := by
  have := h.refl_hyp.cutA_le_mean hm (U := U) (by rw [h.f_refl_mean]; exact hU)
  rw [h.mean_refl] at this
  rw [h.cutB_eq hm hU]
  linarith

lemma cutB_le_levB {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) : cutB f m U ≤ levB f U := by
  have := h.refl_hyp.levA_le_cutA hm (U := U) (by rw [h.f_refl_mean]; exact hU)
  rw [h.levA_refl hU.le] at this
  rw [h.cutB_eq hm hU]
  linarith

lemma levB_le_one {U : ℝ} (hU : U ≤ f (mean f)) : levB f U ≤ 1 :=
  csSup_le ⟨_, h.mean_mem_lev hU⟩ (fun _ hx => hx.1.2)

lemma mean_lt_cutB {m U : ℝ} (hm : 0 < m) (hU : U < f (mean f)) : mean f < cutB f m U := by
  have := h.refl_hyp.cutA_lt_mean hm (U := U) (by rw [h.f_refl_mean]; exact hU)
  rw [h.mean_refl] at this
  rw [h.cutB_eq hm.le hU]
  linarith

lemma cutB_mono {m m' U : ℝ} (hm : 0 ≤ m) (hmm' : m ≤ m') (hU : U < f (mean f)) :
    cutB f m U ≤ cutB f m' U := by
  have := h.refl_hyp.cutA_anti hm hmm' (U := U) (by rw [h.f_refl_mean]; exact hU)
  rw [h.cutB_eq hm hU, h.cutB_eq (hm.trans hmm') hU]
  linarith

/-- `Φ` through `max m 0`. -/
lemma Phi_eq {U : ℝ} (hU : U < f (mean f)) (m : ℝ) :
    Phi f m U = max (mean f - cutA f (max m 0) U) (cutB f (max m 0) U - mean f) ^ 2 / 2 := by
  unfold Phi
  split_ifs with hm
  · rw [max_eq_right hm.le, h.cutA_zero hU, h.cutB_zero hU]
    simp
  · push Not at hm
    rw [max_eq_left hm]

/-- `Φ` is continuous on `ℝ × (-∞, f(μ))`. -/
lemma Phi_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => Phi f p.1 p.2) (univ ×ˢ Iio (f (mean f))) := by
  set g : ℝ × ℝ → ℝ × ℝ := fun p => (max p.1 0, p.2) with hg_def
  have hg : Continuous g := by fun_prop
  have hmaps : MapsTo g (univ ×ˢ Iio (f (mean f))) (Ici 0 ×ˢ Iio (f (mean f))) :=
    fun p hp => ⟨mem_Ici.2 (le_max_right _ _), hp.2⟩
  have hA : ContinuousOn ((fun p : ℝ × ℝ => cutA f p.1 p.2) ∘ g)
      (univ ×ˢ Iio (f (mean f))) := h.cutA_continuousOn.comp hg.continuousOn hmaps
  have hB : ContinuousOn ((fun p : ℝ × ℝ => cutB f p.1 p.2) ∘ g)
      (univ ×ˢ Iio (f (mean f))) := h.cutB_continuousOn.comp hg.continuousOn hmaps
  have hC : ContinuousOn (fun p => max (mean f - ((fun p : ℝ × ℝ => cutA f p.1 p.2) ∘ g) p)
      (((fun p : ℝ × ℝ => cutB f p.1 p.2) ∘ g) p - mean f) ^ 2 / 2)
      (univ ×ˢ Iio (f (mean f))) :=
    ((ContinuousOn.sup (continuousOn_const.sub hA) (hB.sub continuousOn_const)).pow 2).div_const 2
  refine hC.congr (fun p hp => ?_)
  rw [h.Phi_eq hp.2 p.1]
  rfl

omit h in
lemma Phi_of_neg {m U : ℝ} (hm : m < 0) : Phi f m U = 0 := by
  unfold Phi
  split_ifs
  rfl

omit h in
lemma Phi_of_nonneg {m U : ℝ} (hm : 0 ≤ m) :
    Phi f m U = max (mean f - cutA f m U) (cutB f m U - mean f) ^ 2 / 2 := by
  unfold Phi
  split_ifs with h'
  · linarith
  · rfl

omit h in
lemma Phi_nonneg (m U : ℝ) : 0 ≤ Phi f m U := by
  unfold Phi
  split_ifs
  · exact le_rfl
  · positivity

lemma Phi_le {m U : ℝ} (hU : U < f (mean f)) : Phi f m U ≤ 1 / 2 := by
  unfold Phi
  split_ifs with hm
  · norm_num
  · push Not at hm
    have h1 : 0 ≤ mean f - cutA f m U := by linarith [h.cutA_le_mean hm hU]
    have h2 : mean f - cutA f m U ≤ 1 := by linarith [h.cutA_nonneg hm hU, h.mean_lt_one]
    have h3 : 0 ≤ cutB f m U - mean f := by linarith [h.mean_le_cutB hm hU]
    have h4 : cutB f m U - mean f ≤ 1 := by
      linarith [h.cutB_le_levB hm hU, h.levB_le_one hU.le, h.mean_pos]
    have h5 : max (mean f - cutA f m U) (cutB f m U - mean f) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ max (mean f - cutA f m U) (cutB f m U - mean f) := le_max_of_le_left h1
      nlinarith [max_le h2 h4]
    linarith

lemma Phi_mono {U : ℝ} (hU : U < f (mean f)) : Monotone fun m => Phi f m U := by
  intro m m' hmm'
  simp only
  by_cases hm : m < 0
  · rw [Phi_of_neg hm]
    exact Phi_nonneg m' U
  · push Not at hm
    rw [Phi_of_nonneg hm, Phi_of_nonneg (hm.trans hmm')]
    have h1 : 0 ≤ mean f - cutA f m U := by linarith [h.cutA_le_mean hm hU]
    have hle : max (mean f - cutA f m U) (cutB f m U - mean f)
        ≤ max (mean f - cutA f m' U) (cutB f m' U - mean f) :=
      max_le_max (by linarith [h.cutA_anti hm hmm' hU]) (by linarith [h.cutB_mono hm hmm' hU])
    have h0 : 0 ≤ max (mean f - cutA f m U) (cutB f m U - mean f) := le_max_of_le_left h1
    have := pow_le_pow_left₀ h0 hle 2
    linarith

lemma Phi_ge_left {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    (mean f - cutA f m U) ^ 2 / 2 ≤ Phi f m U := by
  rw [Phi_of_nonneg hm]
  have h1 : 0 ≤ mean f - cutA f m U := by linarith [h.cutA_le_mean hm hU]
  have := pow_le_pow_left₀ h1 (le_max_left _ (cutB f m U - mean f)) 2
  linarith

lemma Phi_ge_right {m U : ℝ} (hm : 0 ≤ m) (hU : U < f (mean f)) :
    (cutB f m U - mean f) ^ 2 / 2 ≤ Phi f m U := by
  rw [Phi_of_nonneg hm]
  have h1 : 0 ≤ cutB f m U - mean f := by linarith [h.mean_le_cutB hm hU]
  have := pow_le_pow_left₀ h1 (le_max_right (mean f - cutA f m U) _) 2
  linarith

end Hyp

/-! ## Existence and uniqueness for a scalar ODE `m' = -F(m,U)` with `F` non-decreasing in `m`

Mathlib has the Picard–Lindelöf theorem but not Peano's theorem. Monotonicity in `m` makes
the problem dissipative: we regularise `F` in `m` by averaging (which keeps monotonicity and
makes it Lipschitz), solve by Picard–Lindelöf, and pass to the limit with the one-sided
estimate `d/dU (m_j - m_k) ≤ η` where `m_j > m_k`. -/

section ODE

lemma mono_mul_nonneg {g : ℝ → ℝ} (hg : Monotone g) (a b : ℝ) : 0 ≤ (a - b) * (g a - g b) := by
  rcases le_total a b with hab | hab
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hg hab])
  · exact mul_nonneg (by linarith) (by linarith [hg hab])

/-- Uniqueness, from monotonicity of `F` in `m`. -/
lemma ode_unique {F : ℝ → ℝ → ℝ} {T : ℝ} (hmono : ∀ U ∈ Ico 0 T, Monotone fun m => F m U)
    {m₁ m₂ : ℝ → ℝ} (h0 : m₁ 0 = m₂ 0)
    (h₁ : ∀ U ∈ Ico 0 T, HasDerivWithinAt m₁ (-F (m₁ U) U) (Ici 0) U)
    (h₂ : ∀ U ∈ Ico 0 T, HasDerivWithinAt m₂ (-F (m₂ U) U) (Ici 0) U) :
    EqOn m₁ m₂ (Ico 0 T) := by
  intro U hU
  have hc : ∀ m : ℝ → ℝ, (∀ U ∈ Ico 0 T, HasDerivWithinAt m (-F (m U) U) (Ici 0) U) →
      ContinuousOn m (Icc 0 U) := by
    intro m hm x hx
    exact ((hm x ⟨hx.1, lt_of_le_of_lt hx.2 hU.2⟩).continuousWithinAt).mono Icc_subset_Ici_self
  have hcont : ContinuousOn (fun x => -(m₁ x - m₂ x) ^ 2) (Icc 0 U) := by
    have := ((hc m₁ h₁).sub (hc m₂ h₂)).pow 2
    exact this.neg
  have hder : ∀ x ∈ Ioo 0 U, HasDerivAt (fun x => -(m₁ x - m₂ x) ^ 2)
      (2 * ((m₁ x - m₂ x) * (F (m₁ x) x - F (m₂ x) x))) x := by
    intro x hx
    have hx' : x ∈ Ico 0 T := ⟨hx.1.le, lt_trans hx.2 hU.2⟩
    have d1 := (h₁ x hx').hasDerivAt (Ici_mem_nhds hx.1)
    have d2 := (h₂ x hx').hasDerivAt (Ici_mem_nhds hx.1)
    have := ((d1.sub d2).pow 2).neg
    convert this using 1
    norm_num
    ring
  have hsign : ∀ x ∈ Ioo 0 U, -(m₁ x - m₂ x) ^ 2 < 0 →
      0 ≤ 2 * ((m₁ x - m₂ x) * (F (m₁ x) x - F (m₂ x) x)) := by
    intro x hx _
    have := mono_mul_nonneg (hmono x ⟨hx.1.le, lt_trans hx.2 hU.2⟩) (m₁ x) (m₂ x)
    linarith
  have key := nonneg_of_deriv hU.1 hcont hder hsign (by simp [h0])
  have h3 : (m₁ U - m₂ U) ^ 2 = 0 := by nlinarith [sq_nonneg (m₁ U - m₂ U)]
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- Existence on `[0, T₁]` for `T₁ < T`. -/
lemma ode_exists_Icc {F : ℝ → ℝ → ℝ} {T T₁ C : ℝ} (hT₁ : 0 ≤ T₁) (hT₁T : T₁ < T) (hC : 0 ≤ C)
    (hb : ∀ m, ∀ U ∈ Ico 0 T, |F m U| ≤ C) (hmono : ∀ U ∈ Ico 0 T, Monotone fun m => F m U)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Ico 0 T)) (x₀ : ℝ) :
    ∃ m : ℝ → ℝ, m 0 = x₀ ∧ ∀ U ∈ Ico 0 T₁, HasDerivWithinAt m (-F (m U) U) (Ici 0) U := by
  -- clamping the time variable
  set cl : ℝ → ℝ := fun U => max 0 (min U T₁) with hcl
  have hclc : Continuous cl := by fun_prop
  have hcl_mem : ∀ U, cl U ∈ Icc 0 T₁ :=
    fun U => ⟨le_max_left _ _, max_le hT₁ (min_le_right _ _)⟩
  have hcl_T : ∀ U, cl U ∈ Ico 0 T :=
    fun U => ⟨(hcl_mem U).1, lt_of_le_of_lt (hcl_mem U).2 hT₁T⟩
  have hcl_eq : ∀ U ∈ Icc 0 T₁, cl U = U := fun U hU => by
    simp only [hcl, min_eq_left hU.2, max_eq_right hU.1]
  set G : ℝ → ℝ → ℝ := fun m U => F m (cl U) with hG
  have hGc : Continuous fun p : ℝ × ℝ => G p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => (p.1, cl p.2) := by fun_prop
    exact hcont.comp_continuous h1 (fun p => ⟨mem_univ _, hcl_T p.2⟩)
  have hGb : ∀ m U, |G m U| ≤ C := fun m U => hb m (cl U) (hcl_T U)
  have hGm : ∀ U, Monotone fun m => G m U := fun U => hmono (cl U) (hcl_T U)
  have hGF : ∀ m, ∀ U ∈ Icc 0 T₁, G m U = F m U := fun m U hU => by
    simp only [hG, hcl_eq U hU]
  -- uniform continuity on a compact set
  set K : Set (ℝ × ℝ) := Icc (x₀ - C * T₁ - 1) (x₀ + C * T₁ + 1) ×ˢ Icc 0 T₁
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous hGc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  have hδ : ∀ k : ℕ, ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      dist (G p.1 p.2) (G q.1 q.2) < 1 / ((k : ℝ) + 1) := fun k => huc _ (by positivity)
  choose δ hδpos hδ using hδ
  set ε : ℕ → ℝ := fun k => min 1 (δ k / 2) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => lt_min one_pos (by linarith [hδpos k])
  have hε1 : ∀ k, ε k ≤ 1 := fun k => min_le_left _ _
  have hεδ : ∀ k, ε k < δ k := fun k => lt_of_le_of_lt (min_le_right _ _) (by linarith [hδpos k])
  -- the regularised fields
  set Fk : ℕ → ℝ → ℝ → ℝ := fun k m U => ∫ s in (0:ℝ)..1, G (m + ε k * s) U with hFk
  have hFkc : ∀ k, Continuous fun p : ℝ × ℝ => Fk k p.1 p.2 := by
    intro k
    have h1 : Continuous (Function.uncurry fun (p : ℝ × ℝ) (s : ℝ) => G (p.1 + ε k * s) p.2) :=
      hGc.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => (q.1.1 + ε k * q.2, q.1.2))
    exact continuous_parametric_intervalIntegral_of_continuous' h1 0 1
  have hFkb : ∀ k m U, |Fk k m U| ≤ C := by
    intro k m U
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := C)
      (f := fun s => G (m + ε k * s) U) (fun s _ => by rw [Real.norm_eq_abs]; exact hGb _ _)
    simpa using this
  have hGi : ∀ U a b, IntervalIntegrable (fun y => G y U) volume a b := fun U a b =>
    (hGc.comp₂ continuous_id continuous_const).intervalIntegrable a b
  have hGint : ∀ U a b, |∫ y in a..b, G y U| ≤ C * |b - a| := by
    intro U a b
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C)
      (f := fun y => G y U) (fun s _ => by rw [Real.norm_eq_abs]; exact hGb _ _)
    simpa using this
  have hFklip : ∀ k U m m', |Fk k m U - Fk k m' U| ≤ 2 * C / ε k * |m - m'| := by
    intro k U m m'
    have hrep : ∀ x, Fk k x U = (ε k)⁻¹ * ∫ y in x..x + ε k, G y U := by
      intro x
      simp only [hFk]
      rw [intervalIntegral.integral_comp_add_mul (fun y => G y U) (hεpos k).ne' x]
      simp [smul_eq_mul]
    rw [hrep, hrep, ← mul_sub, intervalIntegral.integral_interval_sub_interval_comm (hGi U _ _)
      (hGi U _ _) (hGi U _ _), abs_mul, abs_inv, abs_of_pos (hεpos k)]
    have h1 := hGint U m m'
    have h2 := hGint U (m + ε k) (m' + ε k)
    have e : m' + ε k - (m + ε k) = m' - m := by ring
    rw [e] at h2
    have h3 : |(∫ y in m..m', G y U) - ∫ y in m + ε k..m' + ε k, G y U| ≤ 2 * C * |m - m'| := by
      rw [abs_sub_comm m' m] at h1 h2
      calc _ ≤ |∫ y in m..m', G y U| + |∫ y in m + ε k..m' + ε k, G y U| := abs_sub _ _
        _ ≤ _ := by linarith
    calc (ε k)⁻¹ * |(∫ y in m..m', G y U) - ∫ y in m + ε k..m' + ε k, G y U|
        ≤ (ε k)⁻¹ * (2 * C * |m - m'|) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 (hεpos k).le)
      _ = 2 * C / ε k * |m - m'| := by field_simp
  have hFkapp : ∀ k m U, m ∈ Icc (x₀ - C * T₁) (x₀ + C * T₁) → U ∈ Icc 0 T₁ →
      |Fk k m U - G m U| ≤ 1 / ((k : ℝ) + 1) := by
    intro k m U hm hU
    have e : Fk k m U - G m U = ∫ s in (0:ℝ)..1, (G (m + ε k * s) U - G m U) := by
      rw [intervalIntegral.integral_sub
        ((hGc.comp₂ (by fun_prop) continuous_const).intervalIntegrable _ _)
        intervalIntegrable_const]
      simp [hFk]
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := 1 / ((k : ℝ) + 1)) (f := fun s => G (m + ε k * s) U - G m U) ?_
    · simpa using this
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    have hp : ((m + ε k * s, U) : ℝ × ℝ) ∈ K := by
      refine ⟨⟨?_, ?_⟩, hU⟩
      · nlinarith [hm.1, hεpos k, hs.1]
      · nlinarith [hm.2, hε1 k, hs.2, hs.1, hεpos k]
    have hq : ((m, U) : ℝ × ℝ) ∈ K := ⟨⟨by linarith [hm.1], by linarith [hm.2]⟩, hU⟩
    have hd : dist ((m + ε k * s, U) : ℝ × ℝ) (m, U) < δ k := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      have : |m + ε k * s - m| ≤ ε k := by
        rw [show m + ε k * s - m = ε k * s by ring, abs_of_nonneg (by nlinarith [hεpos k, hs.1])]
        nlinarith [hεpos k, hs.2]
      exact max_lt (by linarith [hεδ k]) (hδpos k)
    have := hδ k _ hp _ hq hd
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  -- Picard–Lindelöf for the regularised fields
  have hPL : ∀ k, ∃ α : ℝ → ℝ, α 0 = x₀ ∧
      ∀ t ∈ Icc 0 T₁, HasDerivWithinAt α (-Fk k (α t) t) (Icc 0 T₁) t := by
    intro k
    have hP : IsPicardLindelof (fun t x => -Fk k x t) (tmin := 0) (tmax := T₁)
        ⟨0, le_rfl, hT₁⟩ x₀ ⟨C * T₁, by positivity⟩ 0 ⟨C, hC⟩
        ⟨2 * C / ε k, by have := hεpos k; positivity⟩ :=
      { lipschitzOnWith := fun t _ => LipschitzOnWith.of_dist_le_mul fun x _ y _ => by
          simp only [Real.dist_eq]
          rw [show -Fk k x t - -Fk k y t = -(Fk k x t - Fk k y t) by ring, abs_neg]
          exact hFklip k t x y
        continuousOn := fun x _ => ((hFkc k).comp₂ continuous_const continuous_id).neg.continuousOn
        norm_le := fun t _ x _ => by
          simp only [Real.norm_eq_abs, abs_neg]
          exact hFkb k x t
        mul_max_le := by
          simp only [NNReal.coe_zero, sub_zero]
          rw [max_eq_left (by linarith)]
          exact le_rfl }
    obtain ⟨α, h0, hd⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, h0, hd⟩
  choose α hα0 hαd using hPL
  have hαc : ∀ k, ContinuousOn (α k) (Icc 0 T₁) := fun k t ht => (hαd k t ht).continuousWithinAt
  have hαlip : ∀ k t t', t ∈ Icc 0 T₁ → t' ∈ Icc 0 T₁ → |α k t - α k t'| ≤ C * |t - t'| := by
    intro k t t' ht ht'
    have := (convex_Icc (0:ℝ) T₁).norm_image_sub_le_of_norm_hasDerivWithin_le (hαd k)
      (fun x _ => by rw [Real.norm_eq_abs, abs_neg]; exact hFkb k _ _) ht' ht
    simpa [Real.norm_eq_abs] using this
  have hαr : ∀ k t, t ∈ Icc 0 T₁ → α k t ∈ Icc (x₀ - C * T₁) (x₀ + C * T₁) := by
    intro k t ht
    have := hαlip k t 0 ht ⟨le_rfl, hT₁⟩
    rw [hα0, sub_zero, abs_of_nonneg ht.1] at this
    have h2 : C * t ≤ C * T₁ := mul_le_mul_of_nonneg_left ht.2 hC
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hαd' : ∀ k, ∀ t ∈ Ioo 0 T₁, HasDerivAt (α k) (-Fk k (α k t) t) t := fun k t ht =>
    (hαd k t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- the one-sided estimate
  have hcauchy : ∀ j k, ∀ t ∈ Icc 0 T₁,
      α j t - α k t ≤ (1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)) * t := by
    intro j k t ht
    set η := 1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)
    have key := nonneg_of_deriv (g := fun s => η * s - (α j s - α k s))
      (g' := fun s => η - (-Fk j (α j s) s - -Fk k (α k s) s)) ht.1
      ((continuousOn_const.mul continuousOn_id).sub
        (((hαc j).mono (Icc_subset_Icc le_rfl ht.2)).sub
          ((hαc k).mono (Icc_subset_Icc le_rfl ht.2))))
      ?_ ?_ (by simp [hα0])
    · have key' : 0 ≤ η * t - (α j t - α k t) := key
      linarith
    · intro s hs
      have hs' : s ∈ Ioo 0 T₁ := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
      have h2 := ((hasDerivAt_id s).const_mul η).sub ((hαd' j s hs').sub (hαd' k s hs'))
      have h3 : HasDerivAt (fun s => η * s - (α j s - α k s))
          (η * 1 - (-Fk j (α j s) s - -Fk k (α k s) s)) s := h2
      convert h3 using 1
      ring
    · intro s hs hneg
      have hneg' : η * s - (α j s - α k s) < 0 := hneg
      show 0 ≤ η - (-Fk j (α j s) s - -Fk k (α k s) s)
      have hs' : s ∈ Icc 0 T₁ := ⟨hs.1.le, (lt_of_lt_of_le hs.2 ht.2).le⟩
      have hη : 0 ≤ η * s := mul_nonneg (by positivity) hs.1.le
      have hgt : α k s ≤ α j s := by linarith
      have hmon := hGm s hgt
      simp only at hmon
      have a1 := abs_le.1 (hFkapp j (α j s) s (hαr j s hs') hs')
      have a2 := abs_le.1 (hFkapp k (α k s) s (hαr k s hs') hs')
      simp only [η]
      linarith [a1.1, a2.2]
  -- the limit
  have hcs : ∀ t ∈ Icc 0 T₁, CauchySeq fun k => α k t := by
    intro t ht
    rw [Metric.cauchySeq_iff']
    intro e he
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * T₁ / e)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hcauchy n N t ht
    have h2 := hcauchy N n t ht
    have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hn
    have hb2 : (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) * t ≤ 2 / ((N : ℝ) + 1) * T₁ := by
      have : 1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1) ≤ 2 / ((N : ℝ) + 1) := by
        rw [show (2:ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) by ring]
        linarith
      exact mul_le_mul this ht.2 ht.1 (by positivity)
    have hlt : 2 / ((N : ℝ) + 1) * T₁ < e := by
      have hN1 : 2 * T₁ / e < (N : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ he] at hN1
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith
    rw [abs_lt]
    constructor
    · have := add_comm (1 / ((n : ℝ) + 1)) (1 / ((N : ℝ) + 1))
      linarith
    · linarith
  set mlim : ℝ → ℝ := fun t => limUnder atTop fun k => α k t with hmlim
  have htend : ∀ t ∈ Icc 0 T₁, Tendsto (fun k => α k t) atTop (𝓝 (mlim t)) :=
    fun t ht => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcs t ht))
  have hmlip : ∀ t ∈ Icc 0 T₁, ∀ t' ∈ Icc 0 T₁, |mlim t - mlim t'| ≤ C * |t - t'| :=
    fun t ht t' ht' => le_of_tendsto' ((htend t ht).sub (htend t' ht')).abs
      (fun k => hαlip k t t' ht ht')
  have hmc : ContinuousOn mlim (Icc 0 T₁) := by
    have : LipschitzOnWith ⟨C, hC⟩ mlim (Icc 0 T₁) :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
        simp only [Real.dist_eq]; exact hmlip x hx y hy
    exact this.continuousOn
  -- integral equations
  have hcomp : ∀ k, ContinuousOn (fun τ => -Fk k (α k τ) τ) (Icc 0 T₁) := fun k =>
    ((hFkc k).comp_continuousOn ((hαc k).prodMk continuousOn_id)).neg
  have hαint : ∀ k, ∀ t ∈ Icc 0 T₁, α k t = x₀ + ∫ τ in (0:ℝ)..t, -Fk k (α k τ) τ := by
    intro k t ht
    have := integral_eq_sub_of_hasDeriv_right_of_le ht.1
      ((hαc k).mono (Icc_subset_Icc le_rfl ht.2))
      (fun x hx => (hαd' k x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩).hasDerivWithinAt)
      (((hcomp k).mono
        (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)).intervalIntegrable)
    rw [this, hα0]
    ring
  have hlim : ∀ t ∈ Icc 0 T₁, Tendsto (fun k => ∫ τ in (0:ℝ)..t, -Fk k (α k τ) τ) atTop
      (𝓝 (∫ τ in (0:ℝ)..t, -G (mlim τ) τ)) := by
    intro t ht
    have hsub : uIoc 0 t ⊆ Icc 0 T₁ := by
      rw [uIoc_of_le ht.1]; exact fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall fun k =>
        ((hcomp k).mono hsub).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun k => ae_of_all _ fun τ _ => by
        rw [Real.norm_eq_abs, abs_neg]; exact hFkb k _ _
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun τ hτ => ?_
      have hτ' := hsub hτ
      have h1 : Tendsto (fun k => Fk k (α k τ) τ - G (α k τ) τ) atTop (𝓝 0) := by
        apply squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
        rw [Real.norm_eq_abs]
        exact hFkapp k _ _ (hαr k τ hτ') hτ'
      have h2 : Tendsto (fun k => G (α k τ) τ) atTop (𝓝 (G (mlim τ) τ)) :=
        (hGc.tendsto (mlim τ, τ)).comp ((htend τ hτ').prodMk_nhds tendsto_const_nhds)
      have := (h1.add h2).neg
      simp only [zero_add, sub_add_cancel] at this
      exact this
  have hmeq : ∀ t ∈ Icc 0 T₁, mlim t = x₀ + ∫ τ in (0:ℝ)..t, -G (mlim τ) τ := by
    intro t ht
    refine tendsto_nhds_unique (htend t ht) ?_
    have := (tendsto_const_nhds (x := x₀)).add (hlim t ht)
    exact this.congr' (Eventually.of_forall fun k => (hαint k t ht).symm)
  -- the solution
  set hh : ℝ → ℝ := fun τ => -G (mlim (cl τ)) τ with hhh
  have hhc : Continuous hh := by
    have h1 : Continuous (mlim ∘ cl) := hmc.comp_continuous hclc hcl_mem
    exact (hGc.comp₂ h1 continuous_id).neg
  set sol : ℝ → ℝ := fun t => x₀ + ∫ τ in (0:ℝ)..t, hh τ with hsol
  have hsol_eq : ∀ t ∈ Icc 0 T₁, sol t = mlim t := by
    intro t ht
    rw [hmeq t ht]
    show x₀ + ∫ τ in (0:ℝ)..t, hh τ = _
    congr 1
    apply integral_congr
    intro τ hτ
    rw [uIcc_of_le ht.1] at hτ
    simp only [hhh, hcl_eq τ ⟨hτ.1, hτ.2.trans ht.2⟩]
  refine ⟨sol, by simp [hsol], fun t ht => ?_⟩
  have hd := ((hhc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x₀).hasDerivWithinAt
    (s := Ici 0)
  have ht' : t ∈ Icc 0 T₁ := ⟨ht.1, ht.2.le⟩
  convert hd using 1
  simp only [hhh, hcl_eq t ht', hsol_eq t ht', hGF _ t ht']

/-- Existence on `[0, T)`. -/
lemma ode_exists {F : ℝ → ℝ → ℝ} {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (hb : ∀ m, ∀ U ∈ Ico 0 T, |F m U| ≤ C) (hmono : ∀ U ∈ Ico 0 T, Monotone fun m => F m U)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Ico 0 T)) (x₀ : ℝ) :
    ∃ m : ℝ → ℝ, m 0 = x₀ ∧ ∀ U ∈ Ico 0 T, HasDerivWithinAt m (-F (m U) U) (Ici 0) U := by
  have hloc : ∀ T₁ : ℝ, ∃ m : ℝ → ℝ, 0 ≤ T₁ → T₁ < T →
      (m 0 = x₀ ∧ ∀ U ∈ Ico 0 T₁, HasDerivWithinAt m (-F (m U) U) (Ici 0) U) := by
    intro T₁
    by_cases h : 0 ≤ T₁ ∧ T₁ < T
    · obtain ⟨m, hm⟩ := ode_exists_Icc h.1 h.2 hC hb hmono hcont x₀
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨fun _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose s hs using hloc
  set T1 : ℝ → ℝ := fun U => (max U 0 + T) / 2 with hT1
  have hT1a : ∀ U, U < T → U < T1 U ∧ T1 U < T ∧ 0 ≤ T1 U := by
    intro U hU
    simp only [hT1]
    refine ⟨?_, ?_, ?_⟩
    · linarith [le_max_left U 0]
    · rcases le_total U 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    · linarith [le_max_right U 0]
  refine ⟨fun U => s (T1 U) U, (hs (T1 0) (hT1a 0 hT).2.2 (hT1a 0 hT).2.1).1, fun U hU => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT1a U hU.2
  have hsU := hs (T1 U) h3 h2
  have heq : (fun V => s (T1 V) V) =ᶠ[𝓝[Ici 0] U] s (T1 U) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds h1)] with V hV0 hVlt
    obtain ⟨k1, k2, k3⟩ := hT1a V (hVlt.trans h2)
    have hsV := hs (T1 V) k3 k2
    have hV : V ∈ Ico 0 (min (T1 V) (T1 U)) := ⟨hV0, lt_min k1 hVlt⟩
    refine ode_unique (T := min (T1 V) (T1 U))
      (fun W hW => hmono W ⟨hW.1, lt_of_lt_of_le hW.2 ((min_le_left _ _).trans k2.le)⟩)
      (hsV.1.trans hsU.1.symm)
      (fun W hW => hsV.2 W ⟨hW.1, lt_of_lt_of_le hW.2 (min_le_left _ _)⟩)
      (fun W hW => hsU.2 W ⟨hW.1, lt_of_lt_of_le hW.2 (min_le_right _ _)⟩) hV
  exact (hsU.2 U ⟨hU.1, h1⟩).congr_of_eventuallyEq heq rfl

end ODE

/-! ## Theorem 34: existence, uniqueness, part (a) -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma sol_exists : ∃ m, IsSol f m :=
  ode_exists (T := f (mean f)) (C := 1 / 2) h.f_mean_pos (by norm_num)
    (fun m U hU => by rw [abs_of_nonneg (Phi_nonneg m U)]; exact h.Phi_le hU.2)
    (fun U hU => h.Phi_mono hU.2)
    (h.Phi_continuousOn.mono (prod_mono subset_rfl Ico_subset_Iio_self)) (m0 f)

lemma sol_unique {m₁ m₂ : ℝ → ℝ} (h₁ : IsSol f m₁) (h₂ : IsSol f m₂) :
    EqOn m₁ m₂ (Ico 0 (f (mean f))) :=
  ode_unique (fun _ hU => h.Phi_mono hU.2) (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

variable {m : ℝ → ℝ}

omit h in
lemma sol_contOn (hm : IsSol f m) {a b : ℝ} (ha : 0 ≤ a) (hb : b < f (mean f)) :
    ContinuousOn m (Icc a b) := fun x hx =>
  ((hm.2 x ⟨ha.trans hx.1, lt_of_le_of_lt hx.2 hb⟩).continuousWithinAt).mono
    (fun _ hy => (ha.trans hy.1 : (0:ℝ) ≤ _))

omit h in
lemma sol_contOn_Ico (hm : IsSol f m) : ContinuousOn m (Ico 0 (f (mean f))) := fun x hx =>
  ((hm.2 x hx).continuousWithinAt).mono (fun _ hy => hy.1)

omit h in
lemma sol_deriv (hm : IsSol f m) {x : ℝ} (hx0 : 0 < x) (hx : x < f (mean f)) :
    HasDerivAt m (-Phi f (m x) x) x :=
  (hm.2 x ⟨hx0.le, hx⟩).hasDerivAt (Ici_mem_nhds hx0)

lemma lam_contOn {b : ℝ} (hb : b < f (mean f)) : ContinuousOn (lam f) (Iic b) := fun _ hx =>
  (h.lam_hasDerivAt (lt_of_le_of_lt hx hb)).continuousAt.continuousWithinAt

/-- Theorem 34(a): `m ≤ λ`. -/
lemma sol_le_lam (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) : m U ≤ lam f U := by
  have hc : ContinuousOn (fun x => lam f x - m x) (Icc 0 U) :=
    ((h.lam_contOn hU.2).mono (fun _ hx => (mem_Icc.1 hx).2)).sub (sol_contOn hm le_rfl hU.2)
  have hd : ∀ x ∈ Ioo 0 U, HasDerivAt (fun x => lam f x - m x)
      (-((mean f - levA f x) ^ 2 / 2) - -Phi f (m x) x) x := fun x hx =>
    (h.lam_hasDerivAt (lt_trans hx.2 hU.2)).sub (sol_deriv hm hx.1 (lt_trans hx.2 hU.2))
  have hs : ∀ x ∈ Ioo 0 U, lam f x - m x < 0 →
      0 ≤ -((mean f - levA f x) ^ 2 / 2) - -Phi f (m x) x := by
    intro x hx hneg
    have hx' : x < f (mean f) := lt_trans hx.2 hU.2
    have hlt : lam f x < m x := by linarith
    have hm0 : 0 ≤ m x := ((h.lam_pos hx').le.trans hlt.le)
    have := h.Phi_ge_left hm0 hx'
    rw [h.cutA_of_lam_le hx' hlt.le] at this
    linarith
  have h0 : 0 ≤ lam f 0 - m 0 := by rw [hm.1, h.m0_eq_lam, sub_self]
  have key := nonneg_of_deriv hU.1 hc hd hs h0
  linarith

/-- Theorem 34(a): `m ≤ ρ`. -/
lemma sol_le_rho (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) : m U ≤ rho f U := by
  rw [← h.lam_refl]
  exact h.refl_hyp.sol_le_lam (h.isSol_refl.2 hm) ⟨hU.1, by rw [h.f_refl_mean]; exact hU.2⟩

lemma sol_nonneg (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) : 0 ≤ m U := by
  have key := nonneg_of_deriv (g := m) (g' := fun x => -Phi f (m x) x) hU.1
    (sol_contOn hm le_rfl hU.2) (fun x hx => sol_deriv hm hx.1 (lt_trans hx.2 hU.2))
    (fun x _ hneg => by rw [Phi_of_neg hneg]; simp)
    (by rw [hm.1, h.m0_eq_lam]; exact (h.lam_pos h.f_mean_pos).le)
  exact key

/-- A quadratic lower bound for `L` near `μ`. -/
lemma Lf_lower {U₁ : ℝ} (hU₁ : U₁ < f (mean f)) : ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ d ≤ mean f ∧
    ∀ U ≤ U₁, ∀ x ∈ Icc (mean f - d) (mean f), c * (mean f - x) ^ 2 ≤ Lf f x U := by
  set c' := (f (mean f) - U₁) / 2 with hc'
  have hc'pos : 0 < c' := by simp only [hc']; linarith
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 h.cont.continuousAt c' hc'pos
  refine ⟨min (δ / 2) (mean f), c' / 2, lt_min (by linarith) h.mean_pos, by linarith,
    min_le_right _ _, fun U hU x hx => ?_⟩
  have hxm := hx.2
  have hle : ∫ t in x..mean f, (mean f - t) * c' ≤ Lf f x U := by
    apply intervalIntegral.integral_mono_on hxm
    · exact (by fun_prop : Continuous fun t => (mean f - t) * c').intervalIntegrable _ _
    · exact (h.Lf_integrand_cont U).intervalIntegrable _ _
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (by linarith [ht.2])
    have hd : dist t (mean f) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]
      linarith [hx.1, ht.1, min_le_left (δ / 2) (mean f)]
    have := hδf hd
    rw [Real.dist_eq, abs_lt] at this
    exact le_max_of_le_left (by linarith [this.1])
  have e : ∫ t in x..mean f, (mean f - t) * c' = c' * ((mean f - x) ^ 2 / 2) := by
    rw [intervalIntegral.integral_mul_const, int_mean_sub]
    ring
  rw [e] at hle
  linarith

lemma cutA_quad {U₁ : ℝ} (hU₁ : U₁ < f (mean f)) : ∃ c m₁ : ℝ, 0 < c ∧ 0 < m₁ ∧
    ∀ m U, 0 ≤ m → m < m₁ → U ≤ U₁ → c * (mean f - cutA f m U) ^ 2 ≤ m := by
  obtain ⟨d, c, hd, hc, hdm, hL⟩ := h.Lf_lower hU₁
  refine ⟨c, c * d ^ 2, hc, by positivity, fun m U hm hm1 hU => ?_⟩
  have hU' : U < f (mean f) := lt_of_le_of_lt hU hU₁
  have hmem := h.cutA_mem hm hU'
  have hLx : Lf f (cutA f m U) U ≤ m := hmem.2
  have hx : mean f - d ≤ cutA f m U := by
    by_contra hlt
    push Not at hlt
    have h1 := h.Lf_anti (U := U) hlt.le (by linarith)
    have h2 := hL U hU (mean f - d) ⟨le_rfl, by linarith⟩
    rw [show mean f - (mean f - d) = d by ring] at h2
    linarith
  exact (hL U hU _ ⟨hx, hmem.1.2⟩).trans hLx

lemma Phi_le_lin {U₁ : ℝ} (hU₁ : U₁ < f (mean f)) : ∃ K m₁ : ℝ, 0 < K ∧ 0 < m₁ ∧
    ∀ m U, 0 ≤ m → m < m₁ → U ≤ U₁ → Phi f m U ≤ K * m := by
  obtain ⟨c, m₁, hc, hm₁, hq⟩ := h.cutA_quad hU₁
  obtain ⟨c', m₁', hc', hm₁', hq'⟩ := h.refl_hyp.cutA_quad (U₁ := U₁)
    (by rw [h.f_refl_mean]; exact hU₁)
  refine ⟨(1 / c + 1 / c') / 2, min m₁ m₁', by positivity, lt_min hm₁ hm₁',
    fun m U hm hmm hU => ?_⟩
  have hU' : U < f (mean f) := lt_of_le_of_lt hU hU₁
  have h1 := hq m U hm (lt_of_lt_of_le hmm (min_le_left _ _)) hU
  have h2 := hq' m U hm (lt_of_lt_of_le hmm (min_le_right _ _)) hU
  rw [h.mean_refl, h.cutA_refl hm hU', show 1 - mean f - (1 - cutB f m U) = cutB f m U - mean f
    by ring] at h2
  rw [Phi_of_nonneg hm]
  have ha : (mean f - cutA f m U) ^ 2 ≤ m / c := by rw [le_div_iff₀ hc]; linarith
  have hb : (cutB f m U - mean f) ^ 2 ≤ m / c' := by rw [le_div_iff₀ hc']; linarith
  have hmax : max (mean f - cutA f m U) (cutB f m U - mean f) ^ 2
      ≤ (mean f - cutA f m U) ^ 2 + (cutB f m U - mean f) ^ 2 := by
    rcases le_total (mean f - cutA f m U) (cutB f m U - mean f) with h' | h'
    · rw [max_eq_right h']; nlinarith
    · rw [max_eq_left h']; nlinarith
  have e : (1 / c + 1 / c') / 2 * m = (m / c + m / c') / 2 := by ring
  rw [e]
  linarith

/-- Theorem 34(a): `m > 0`. -/
lemma sol_pos (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) : 0 < m U := by
  obtain ⟨K, m₁, hK, hm₁, hPhi⟩ := h.Phi_le_lin hU.2
  have hm0 : 0 < m0 f := by rw [h.m0_eq_lam]; exact h.lam_pos h.f_mean_pos
  set c0 := min (m0 f) m₁ / 2 with hc0
  have hc0pos : 0 < c0 := by simp only [hc0]; have := lt_min hm0 hm₁; linarith
  have hc0m : c0 < m₁ := by simp only [hc0]; linarith [min_le_right (m0 f) m₁]
  have hc : ContinuousOn (fun x => m x - c0 * Real.exp (-(K * x))) (Icc 0 U) :=
    (sol_contOn hm le_rfl hU.2).sub (by fun_prop)
  have hd : ∀ x ∈ Ioo 0 U, HasDerivAt (fun x => m x - c0 * Real.exp (-(K * x)))
      (-Phi f (m x) x - c0 * (Real.exp (-(K * x)) * -(K * 1))) x := fun x hx =>
    (sol_deriv hm hx.1 (lt_trans hx.2 hU.2)).sub
      ((((hasDerivAt_id x).const_mul K).neg.exp).const_mul c0)
  have hs : ∀ x ∈ Ioo 0 U, m x - c0 * Real.exp (-(K * x)) < 0 →
      0 ≤ -Phi f (m x) x - c0 * (Real.exp (-(K * x)) * -(K * 1)) := by
    intro x hx hneg
    have hx' : x ∈ Ico 0 (f (mean f)) := ⟨hx.1.le, lt_trans hx.2 hU.2⟩
    have he : Real.exp (-(K * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hx.1])
    have hmx := h.sol_nonneg hm hx'
    have hlt : m x < m₁ := by nlinarith [Real.exp_pos (-(K * x))]
    have := hPhi (m x) x hmx hlt hx.2.le
    nlinarith [Real.exp_pos (-(K * x))]
  have h0 : 0 ≤ m 0 - c0 * Real.exp (-(K * 0)) := by
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    rw [hm.1]
    simp only [hc0]
    linarith [min_le_left (m0 f) m₁]
  have key := nonneg_of_deriv hU.1 hc hd hs h0
  nlinarith [Real.exp_pos (-(K * U))]

end Hyp

/-! ## Theorem 34: rest of part (a), part (b) -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f) {m : ℝ → ℝ}
include h

lemma Lf_cutA_sol (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    Lf f (cutA f (m U) U) U = m U := by
  rw [h.Lf_cutA (h.sol_nonneg hm hU) hU.2, min_eq_left (h.sol_le_lam hm hU)]

lemma hU_refl {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    U ∈ Ico 0 (refl f (mean (refl f))) := by rw [h.f_refl_mean]; exact hU

lemma Rf_cutB_sol (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    Rf f (cutB f (m U) U) U = m U := by
  have := h.refl_hyp.Lf_cutA_sol (h.isSol_refl.2 hm) (h.hU_refl hU)
  rw [h.Lf_refl, ← h.cutB_eq (h.sol_nonneg hm hU) hU.2] at this
  exact this

lemma le_f_of_levA_le {U t : ℝ} (hU : U < f (mean f)) (ht : levA f U ≤ t) (htm : t ≤ mean f) :
    U ≤ f t := by
  rcases ht.lt_or_eq with hlt | heq
  · exact (h.lt_f_of_levA_lt hU hlt htm).le
  · rw [← heq]; exact h.le_f_levA hU.le

lemma le_f_sol (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    ∀ t ∈ Icc (cutA f (m U) U) (cutB f (m U) U), U ≤ f t := by
  intro t ht
  have hm0 := h.sol_nonneg hm hU
  rcases le_total t (mean f) with htm | htm
  · exact h.le_f_of_levA_le hU.2 ((h.levA_le_cutA hm0 hU.2).trans ht.1) htm
  · have hl := h.refl_hyp
    have hU' : U < refl f (mean (refl f)) := (h.hU_refl hU).2
    have h1 := hl.levA_le_cutA hm0 hU'
    rw [h.cutA_refl hm0 hU.2] at h1
    have := hl.le_f_of_levA_le hU' (t := 1 - t) (by linarith [ht.2])
      (by rw [h.mean_refl]; linarith)
    simpa [refl] using this

/-- Theorem 34(a): `f - U` on `[A(U), B(U)]` has mean `μ`. -/
lemma mean_sol (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    ∫ t in cutA f (m U) U..cutB f (m U) U, (t - mean f) * (f t - U) = 0 := by
  have hm0 := h.sol_nonneg hm hU
  have hc : Continuous fun t => (t - mean f) * (f t - U) := by have := h.cont; fun_prop
  have hA := h.cutA_le_mean hm0 hU.2
  have hB := h.mean_le_cutB hm0 hU.2
  have hle := h.le_f_sol hm hU
  rw [← integral_add_adjacent_intervals (b := mean f) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in cutA f (m U) U..mean f, (t - mean f) * (f t - U)
      = -Lf f (cutA f (m U) U) U := by
    rw [Lf, ← intervalIntegral.integral_neg]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hA] at ht
    simp only
    rw [max_eq_left (by linarith [hle t ⟨ht.1, ht.2.trans hB⟩])]
    ring
  have e2 : ∫ t in mean f..cutB f (m U) U, (t - mean f) * (f t - U)
      = Rf f (cutB f (m U) U) U := by
    rw [Rf]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hB] at ht
    simp only
    rw [max_eq_left (by linarith [hle t ⟨hA.trans ht.1, ht.2⟩])]
  rw [e1, e2, h.Lf_cutA_sol hm hU, h.Rf_cutB_sol hm hU]
  ring

lemma cutA_sol_zero (hm : IsSol f m) : cutA f (m 0) 0 = 0 := by
  rw [hm.1, h.m0_eq_lam, h.cutA_of_lam_le h.f_mean_pos le_rfl]
  exact h.levA_eq_zero (h.nonneg 0 ⟨le_rfl, zero_le_one⟩) h.f_mean_pos.le

lemma cutB_sol_zero (hm : IsSol f m) : cutB f (m 0) 0 = 1 := by
  rw [h.cutB_eq (h.sol_nonneg hm ⟨le_rfl, h.f_mean_pos⟩) h.f_mean_pos,
    h.refl_hyp.cutA_sol_zero (h.isSol_refl.2 hm)]
  ring

lemma cutA_sol_contOn (hm : IsSol f m) :
    ContinuousOn (fun U => cutA f (m U) U) (Ico 0 (f (mean f))) := by
  have hp : ContinuousOn (fun U => (m U, U)) (Ico 0 (f (mean f))) :=
    (sol_contOn_Ico hm).prodMk continuousOn_id
  have : ContinuousOn ((fun p : ℝ × ℝ => cutA f p.1 p.2) ∘ (fun U => (m U, U)))
      (Ico 0 (f (mean f))) :=
    ContinuousOn.comp (g := fun p : ℝ × ℝ => cutA f p.1 p.2) h.cutA_continuousOn hp
      (fun U hU => ⟨h.sol_nonneg hm hU, hU.2⟩)
  exact this

lemma cutB_sol_contOn (hm : IsSol f m) :
    ContinuousOn (fun U => cutB f (m U) U) (Ico 0 (f (mean f))) := by
  have hp : ContinuousOn (fun U => (m U, U)) (Ico 0 (f (mean f))) :=
    (sol_contOn_Ico hm).prodMk continuousOn_id
  have : ContinuousOn ((fun p : ℝ × ℝ => cutB f p.1 p.2) ∘ (fun U => (m U, U)))
      (Ico 0 (f (mean f))) :=
    ContinuousOn.comp (g := fun p : ℝ × ℝ => cutB f p.1 p.2) h.cutB_continuousOn hp
      (fun U hU => ⟨h.sol_nonneg hm hU, hU.2⟩)
  exact this

lemma cutA_sol_mono (hm : IsSol f m) : MonotoneOn (fun U => cutA f (m U) U)
    (Ico 0 (f (mean f))) := by
  intro U₁ hU₁ U₂ hU₂ h12
  simp only
  set x₁ := cutA f (m U₁) U₁ with hx₁
  have hm1 := h.sol_nonneg hm hU₁
  have hx0 : 0 ≤ x₁ := h.cutA_nonneg hm1 hU₁.2
  have hxm : x₁ ≤ mean f := h.cutA_le_mean hm1 hU₁.2
  have hc : ContinuousOn (fun U => Lf f x₁ U - m U) (Icc U₁ U₂) :=
    (h.Lf_continuous.comp₂ continuous_const continuous_id).continuousOn.sub
      (sol_contOn hm hU₁.1 hU₂.2)
  have hd : ∀ x ∈ Ioo U₁ U₂, HasDerivAt (fun U => Lf f x₁ U - m U)
      (-((mean f - max x₁ (levA f x)) ^ 2 / 2) - -Phi f (m x) x) x := fun x hx =>
    (h.Lf_hasDerivAt_U hx0 hxm (lt_trans hx.2 hU₂.2)).sub
      (sol_deriv hm (lt_of_le_of_lt hU₁.1 hx.1) (lt_trans hx.2 hU₂.2))
  have hs : ∀ x ∈ Ioo U₁ U₂, Lf f x₁ x - m x < 0 →
      0 ≤ -((mean f - max x₁ (levA f x)) ^ 2 / 2) - -Phi f (m x) x := by
    intro x hx hneg
    have hx' : x ∈ Ico 0 (f (mean f)) := ⟨hU₁.1.trans hx.1.le, lt_trans hx.2 hU₂.2⟩
    have hmx := h.sol_nonneg hm hx'
    have hLA := h.Lf_cutA_sol hm hx'
    have hlt : cutA f (m x) x < x₁ := by
      by_contra hle
      push Not at hle
      have := h.Lf_anti (U := x) hle (h.cutA_le_mean hmx hx'.2)
      linarith
    have hmax : max x₁ (levA f x) = x₁ :=
      max_eq_left ((h.levA_le_cutA hmx hx'.2).trans hlt.le)
    rw [hmax]
    have hP := h.Phi_ge_left hmx hx'.2
    have : (mean f - x₁) ^ 2 ≤ (mean f - cutA f (m x) x) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith
  have h0 : 0 ≤ Lf f x₁ U₁ - m U₁ := by rw [hx₁, h.Lf_cutA_sol hm hU₁, sub_self]
  have key := nonneg_of_deriv h12 hc hd hs h0
  by_contra hlt
  push Not at hlt
  have hm2 := h.sol_nonneg hm hU₂
  have := h.Lf_strictAnti hU₂.2 ⟨h.levA_le_cutA hm2 hU₂.2, h.cutA_le_mean hm2 hU₂.2⟩
    ⟨(h.levA_le_cutA hm2 hU₂.2).trans hlt.le, hxm⟩ hlt
  simp only at this
  rw [h.Lf_cutA_sol hm hU₂] at this
  linarith

lemma cutB_sol_anti (hm : IsSol f m) : AntitoneOn (fun U => cutB f (m U) U)
    (Ico 0 (f (mean f))) := by
  intro U₁ hU₁ U₂ hU₂ h12
  have := h.refl_hyp.cutA_sol_mono (h.isSol_refl.2 hm) (h.hU_refl hU₁) (h.hU_refl hU₂) h12
  simp only at this ⊢
  rw [h.cutA_refl (h.sol_nonneg hm hU₁) hU₁.2, h.cutA_refl (h.sol_nonneg hm hU₂) hU₂.2] at this
  linarith

end Hyp

/-! ## Tools for part (c) -/

/-- Local-to-global: if `|Ψ y - Ψ x| ≤ ε |F y - F x|` near every point, for every `ε > 0`, with
`F` monotone, then `Ψ` is constant. -/
lemma eq_of_local {Ψ F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hF : MonotoneOn F (Icc a b))
    (hloc : ∀ x ∈ Icc a b, ∀ ε > 0, ∀ᶠ y in 𝓝 x, y ∈ Icc a b → |Ψ y - Ψ x| ≤ ε * |F y - F x|) :
    Ψ b = Ψ a := by
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbound : ∀ ε > 0, |Ψ b - Ψ a| ≤ ε * (F b - F a) := by
    intro ε hε
    set S := {x | x ∈ Icc a b ∧ |Ψ x - Ψ a| ≤ ε * (F x - F a)}
    have hSne : S.Nonempty := ⟨a, ha, by simp⟩
    have hSbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
    set c := sSup S
    have hac : a ≤ c := le_csSup hSbdd ⟨ha, by simp⟩
    have hcb : c ≤ b := csSup_le hSne (fun x hx => hx.1.2)
    have hc : c ∈ Icc a b := ⟨hac, hcb⟩
    obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (hloc c hc ε hε)
    have hcS : c ∈ S := by
      refine ⟨hc, ?_⟩
      rcases hac.lt_or_eq with hlt | heq
      · obtain ⟨y, hyS, hy⟩ := exists_lt_of_lt_csSup hSne
          (show max a (c - δ / 2) < c from max_lt hlt (by linarith))
        have hyc : y ≤ c := le_csSup hSbdd hyS
        have hyd : dist y c < δ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith)]
          linarith [le_max_right a (c - δ / 2)]
        have h1 := hδP hyd hyS.1
        have hFF : |F y - F c| = F c - F y := by
          rw [abs_of_nonpos (by linarith [hF hyS.1 hc hyc])]; ring
        rw [hFF, abs_sub_comm] at h1
        calc |Ψ c - Ψ a| ≤ |Ψ c - Ψ y| + |Ψ y - Ψ a| := abs_sub_le _ _ _
          _ ≤ ε * (F c - F y) + ε * (F y - F a) := add_le_add h1 hyS.2
          _ = ε * (F c - F a) := by ring
      · rw [← heq]; simp
    have hcb' : c = b := by
      by_contra hne
      have hlt : c < b := lt_of_le_of_ne hcb hne
      set y := min b (c + δ / 2)
      have hcy : c < y := lt_min hlt (by linarith)
      have hy : y ∈ Icc a b := ⟨by linarith, min_le_left _ _⟩
      have hyd : dist y c < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith [min_le_right b (c + δ / 2)]
      have h1 := hδP hyd hy
      have hFF : |F y - F c| = F y - F c := abs_of_nonneg (by linarith [hF hc hy hcy.le])
      rw [hFF] at h1
      have hyS : y ∈ S := ⟨hy, by
        calc |Ψ y - Ψ a| ≤ |Ψ y - Ψ c| + |Ψ c - Ψ a| := abs_sub_le _ _ _
          _ ≤ ε * (F y - F c) + ε * (F c - F a) := add_le_add h1 hcS.2
          _ = ε * (F y - F a) := by ring⟩
      have := le_csSup hSbdd hyS
      linarith
    rw [← hcb']
    exact hcS.2
  have hD : 0 ≤ F b - F a := by linarith [hF ha hb hab]
  have h0 : |Ψ b - Ψ a| = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (abs_nonneg _)
    have := hbound (e / (F b - F a + 1)) (by positivity)
    have h2 : e / (F b - F a + 1) * (F b - F a) ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have := abs_eq_zero.1 h0
  linarith

lemma len_eq (ν : Measure ℝ) (F : ℝ → ℝ) (hν : ∀ a b, ν (Ioc a b) = ENNReal.ofReal (F b - F a))
    (x y : ℝ) : ν.real (Ioc x y) - ν.real (Ioc y x) = F y - F x := by
  simp only [measureReal_def, hν, ENNReal.toReal_ofReal']
  rcases le_total (F x) (F y) with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

lemma integral_approx {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {g : ℝ → ℝ} {x y ε : ℝ}
    (hg : ContinuousOn g (uIcc x y)) (hε : ∀ s ∈ uIcc x y, |g s - g x| ≤ ε) :
    |(∫ s in x..y, g s ∂ν) - (ν.real (Ioc x y) - ν.real (Ioc y x)) * g x|
      ≤ ε * |ν.real (Ioc x y) - ν.real (Ioc y x)| := by
  have hi : IntervalIntegrable g ν x y := hg.intervalIntegrable
  have e : (∫ s in x..y, g s ∂ν) - (ν.real (Ioc x y) - ν.real (Ioc y x)) * g x
      = ∫ s in x..y, (g s - g x) ∂ν := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const', smul_eq_mul]
  rw [e]
  rcases le_total x y with hxy | hxy
  · have h0 : ν.real (Ioc y x) = 0 := by rw [Ioc_eq_empty (not_lt.2 hxy)]; simp
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := ν) (g := fun _ => ε) hxy
      (ae_of_all _ fun t ht => by
        rw [Real.norm_eq_abs]; exact hε t (by rw [uIcc_of_le hxy]; exact Ioc_subset_Icc_self ht))
      intervalIntegrable_const
    rw [Real.norm_eq_abs, intervalIntegral.integral_const', smul_eq_mul, h0] at this
    rw [h0, sub_zero, abs_of_nonneg measureReal_nonneg]
    linarith
  · have h0 : ν.real (Ioc x y) = 0 := by rw [Ioc_eq_empty (not_lt.2 hxy)]; simp
    rw [intervalIntegral.integral_symm, abs_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := ν) (g := fun _ => ε) hxy
      (ae_of_all _ fun t ht => by
        rw [Real.norm_eq_abs]; exact hε t (by rw [uIcc_of_ge hxy]; exact Ioc_subset_Icc_self ht))
      intervalIntegrable_const
    rw [Real.norm_eq_abs, intervalIntegral.integral_const', smul_eq_mul, h0] at this
    rw [h0, zero_sub, abs_neg, abs_of_nonneg measureReal_nonneg]
    linarith

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

/-- `L` is differentiable at `(x₀, U₀)` (the C¹ statement of Lemma 33 in the form used). -/
lemma Lf_local {x₀ U₀ : ℝ} (hx0 : 0 ≤ x₀) (hxm : x₀ ≤ mean f) (hU : U₀ < f (mean f))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, U₀),
      |Lf f p.1 p.2 - Lf f x₀ U₀ - (-((mean f - x₀) * max (f x₀ - U₀) 0)) * (p.1 - x₀)
        - (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2)) * (p.2 - U₀)|
        ≤ ε * (|p.1 - x₀| + |p.2 - U₀|) := by
  set H : ℝ × ℝ → ℝ := fun q => (mean f - q.1) * max (f q.1 - q.2) 0 with hH
  have hHc : Continuous H := by have := h.cont; fun_prop
  obtain ⟨δ, hδ, hδH⟩ := Metric.continuousAt_iff.1 hHc.continuousAt ε hε
  have hder := h.Lf_hasDerivAt_U hx0 hxm hU
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hder
  have hder' := hder hε
  have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, U₀), ‖Lf f x₀ p.2 - Lf f x₀ U₀ - (p.2 - U₀) •
      (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2))‖ ≤ ε * ‖p.2 - U₀‖ :=
    Filter.Tendsto.eventually (f := Prod.snd) (continuous_snd.tendsto (x₀, U₀))
      (p := fun U => ‖Lf f x₀ U - Lf f x₀ U₀ - (U - U₀) •
        (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2))‖ ≤ ε * ‖U - U₀‖) hder'
  filter_upwards [Metric.ball_mem_nhds (x₀, U₀) hδ, h2] with p hp hp2
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul] at hp2
  have hi : ∀ a b, IntervalIntegrable (fun t => (mean f - t) * max (f t - p.2) 0) volume a b :=
    fun a b => (h.Lf_integrand_cont p.2).intervalIntegrable a b
  have e1 : Lf f p.1 p.2 - Lf f x₀ p.2 = -∫ t in x₀..p.1, (mean f - t) * max (f t - p.2) 0 := by
    simp only [Lf]
    rw [← integral_add_adjacent_intervals (a := x₀) (b := p.1) (hi _ _) (hi _ _)]
    ring
  have hb : |(∫ t in x₀..p.1, (mean f - t) * max (f t - p.2) 0) - (p.1 - x₀) * H (x₀, U₀)|
      ≤ ε * |p.1 - x₀| := by
    have e : (∫ t in x₀..p.1, (mean f - t) * max (f t - p.2) 0) - (p.1 - x₀) * H (x₀, U₀)
        = ∫ t in x₀..p.1, (H (t, p.2) - H (x₀, U₀)) := by
      rw [intervalIntegral.integral_sub (hi _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀) (b := p.1) (C := ε)
      (f := fun t => H (t, p.2) - H (x₀, U₀)) ?_
    · rw [Real.norm_eq_abs] at this
      linarith
    intro t ht
    have ht' : |t - x₀| ≤ |p.1 - x₀| := by
      rcases le_total x₀ p.1 with h' | h'
      · rw [uIoc_of_le h'] at ht
        rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]
        linarith [ht.2]
      · rw [uIoc_comm, uIoc_of_le h'] at ht
        rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]
        linarith [ht.1]
    have hd : dist (t, p.2) (x₀, U₀) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨lt_of_le_of_lt ht' hp.1, hp.2⟩
    have := hδH hd
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  have hH0 : H (x₀, U₀) = (mean f - x₀) * max (f x₀ - U₀) 0 := rfl
  rw [hH0] at hb
  have e2 : Lf f p.1 p.2 - Lf f x₀ U₀ - (-((mean f - x₀) * max (f x₀ - U₀) 0)) * (p.1 - x₀)
      - (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2)) * (p.2 - U₀)
      = -((∫ t in x₀..p.1, (mean f - t) * max (f t - p.2) 0)
          - (p.1 - x₀) * ((mean f - x₀) * max (f x₀ - U₀) 0))
        + (Lf f x₀ p.2 - Lf f x₀ U₀ - (p.2 - U₀) * (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2))) := by
    linarith [e1]
  rw [e2]
  calc _ ≤ |(∫ t in x₀..p.1, (mean f - t) * max (f t - p.2) 0)
          - (p.1 - x₀) * ((mean f - x₀) * max (f x₀ - U₀) 0)|
        + |Lf f x₀ p.2 - Lf f x₀ U₀ - (p.2 - U₀) * (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2))| := by
        rw [← abs_neg ((∫ t in x₀..p.1, (mean f - t) * max (f t - p.2) 0)
          - (p.1 - x₀) * ((mean f - x₀) * max (f x₀ - U₀) 0))]
        exact abs_add_le _ _
    _ ≤ ε * |p.1 - x₀| + ε * |p.2 - U₀| := add_le_add hb hp2
    _ = _ := by ring

end Hyp

/-- The atom at the left end, `(r² - ℓ²)⁺/(2ℓ)` with `ℓ = μ - a`, `r = b - μ`. -/
def wLeft (μ a b : ℝ) : ℝ := max ((b - μ) ^ 2 - (μ - a) ^ 2) 0 / (2 * (μ - a))

/-- The atom at the right end, `(ℓ² - r²)⁺/(2r)`. -/
def wRight (μ a b : ℝ) : ℝ := max ((μ - a) ^ 2 - (b - μ) ^ 2) 0 / (2 * (b - μ))

lemma abs_sub_le_of_mem_uIcc {s x y : ℝ} (hs : s ∈ uIcc x y) : |s - x| ≤ |y - x| := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hs
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
    linarith [hs.2]
  · rw [uIcc_of_ge h] at hs
    rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]
    linarith [hs.1]

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f) {m : ℝ → ℝ}
include h

/-- Theorem 34(c), left end, integrated form on `[U₁, U₂] ⊆ [0, f(μ))`, for any Stieltjes
function equal to `A(U)` up to a constant on `[0, f(μ))`. -/
lemma c_core (hm : IsSol f m) (SA : StieltjesFunction ℝ) (κ : ℝ)
    (hSA : ∀ U ∈ Ico 0 (f (mean f)), SA U = cutA f (m U) U + κ) {U₁ U₂ : ℝ} (h0 : 0 ≤ U₁)
    (h12 : U₁ ≤ U₂) (h2 : U₂ < f (mean f)) :
    ∫ s in U₁..U₂, (f (cutA f (m s) s) - s) ∂SA.measure
      = ∫ s in U₁..U₂, wLeft (mean f) (cutA f (m s) s) (cutB f (m s) s) := by
  set Ap := fun U => cutA f (m U) U with hAp
  set Bp := fun U => cutB f (m U) U with hBp
  set g := fun U => f (Ap U) - U with hg
  set w := fun U => wLeft (mean f) (Ap U) (Bp U) with hw
  have hI : Icc U₁ U₂ ⊆ Ico 0 (f (mean f)) :=
    fun U hU => ⟨h0.trans hU.1, lt_of_le_of_lt hU.2 h2⟩
  have hApc : ContinuousOn Ap (Icc U₁ U₂) := (h.cutA_sol_contOn hm).mono hI
  have hBpc : ContinuousOn Bp (Icc U₁ U₂) := (h.cutB_sol_contOn hm).mono hI
  have hgc : ContinuousOn g (Icc U₁ U₂) := (h.cont.comp_continuousOn hApc).sub continuousOn_id
  have hℓ : ∀ U ∈ Icc U₁ U₂, 0 < mean f - Ap U := fun U hU =>
    sub_pos.2 (h.cutA_lt_mean (h.sol_pos hm (hI hU)) (hI hU).2)
  have hr : ∀ U ∈ Icc U₁ U₂, 0 ≤ Bp U - mean f := fun U hU =>
    sub_nonneg.2 (h.mean_le_cutB (h.sol_nonneg hm (hI hU)) (hI hU).2)
  have hwc : ContinuousOn w (Icc U₁ U₂) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ContinuousOn.sup (((hBpc.sub continuousOn_const).pow 2).sub
        ((continuousOn_const.sub hApc).pow 2)) continuousOn_const
    · exact continuousOn_const.mul (continuousOn_const.sub hApc)
    · intro U hU; exact (mul_pos two_pos (hℓ U hU)).ne'
  have hsub : ∀ a ∈ Icc U₁ U₂, ∀ b ∈ Icc U₁ U₂, uIcc a b ⊆ Icc U₁ U₂ :=
    fun a ha b hb => uIcc_subset_Icc ha hb
  have hig : ∀ a ∈ Icc U₁ U₂, ∀ b ∈ Icc U₁ U₂, IntervalIntegrable g SA.measure a b :=
    fun a ha b hb => (hgc.mono (hsub a ha b hb)).intervalIntegrable
  have hiw : ∀ a ∈ Icc U₁ U₂, ∀ b ∈ Icc U₁ U₂, IntervalIntegrable w volume a b :=
    fun a ha b hb => (hwc.mono (hsub a ha b hb)).intervalIntegrable
  have hlenA : ∀ x ∈ Icc U₁ U₂, ∀ y ∈ Icc U₁ U₂,
      SA.measure.real (Ioc x y) - SA.measure.real (Ioc y x) = Ap y - Ap x := by
    intro x hx y hy
    rw [len_eq SA.measure SA (fun a b => SA.measure_Ioc a b), hSA y (hI hy), hSA x (hI hx)]
    ring
  have hlenV : ∀ x y : ℝ, volume.real (Ioc x y) - volume.real (Ioc y x) = y - x := fun x y =>
    len_eq volume id (fun a b => Real.volume_Ioc) x y
  have hU₁ : U₁ ∈ Icc U₁ U₂ := ⟨le_rfl, h12⟩
  set Ψ := fun U => (∫ s in U₁..U, g s ∂SA.measure) - ∫ s in U₁..U, w s with hΨ
  have hFm : MonotoneOn (fun U => Ap U + U) (Icc U₁ U₂) :=
    ((h.cutA_sol_mono hm).mono hI).add monotoneOn_id
  have key := eq_of_local (Ψ := Ψ) h12 hFm ?_
  · simp only [hΨ, integral_same, sub_self] at key
    linarith
  intro x hx ε hε
  have hxI := hI hx
  have hmx := h.sol_nonneg hm hxI
  have hℓx := hℓ x hx
  obtain ⟨δg, hδg, hg'⟩ := Metric.continuousWithinAt_iff.1 (hgc x hx) (ε / 2) (by linarith)
  obtain ⟨δw, hδw, hw'⟩ := Metric.continuousWithinAt_iff.1 (hwc x hx) (ε / 2) (by linarith)
  set ε' := ε * (mean f - Ap x) / 4 with hε'def
  have hε' : 0 < ε' := by positivity
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ Icc U₁ U₂ →
      |m y - m x - (y - x) * (-Phi f (m x) x)| ≤ ε' * |y - x| := by
    have hd := hm.2 x hxI
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hd
    have h' := hd hε'
    rw [eventually_nhdsWithin_iff] at h'
    filter_upwards [h'] with y hy hyI
    have := hy (h0.trans hyI.1 : (0:ℝ) ≤ y)
    simpa [Real.norm_eq_abs, smul_eq_mul] using this
  have h4 : ∀ᶠ y in 𝓝 x, y ∈ Icc U₁ U₂ →
      |Lf f (Ap y) y - Lf f (Ap x) x - (-((mean f - Ap x) * max (f (Ap x) - x) 0)) * (Ap y - Ap x)
        - (-((mean f - max (Ap x) (levA f x)) ^ 2 / 2)) * (y - x)|
        ≤ ε' * (|Ap y - Ap x| + |y - x|) := by
    have hL := h.Lf_local (h.cutA_nonneg hmx hxI.2) (h.cutA_le_mean hmx hxI.2) hxI.2 hε'
    have ht : Tendsto (fun y => (Ap y, y)) (𝓝[Icc U₁ U₂] x) (𝓝 (Ap x, x)) :=
      (ContinuousWithinAt.prodMk (hApc x hx) continuousWithinAt_id).tendsto
    have h' := ht.eventually hL
    rw [eventually_nhdsWithin_iff] at h'
    exact h'
  filter_upwards [Metric.ball_mem_nhds x (lt_min hδg hδw), h3, h4] with y hy hy3 hy4 hyI
  have hyI' := hI hyI
  rw [Metric.mem_ball, lt_min_iff] at hy
  have hΨd : Ψ y - Ψ x = (∫ s in x..y, g s ∂SA.measure) - ∫ s in x..y, w s := by
    simp only [hΨ]
    rw [← integral_interval_sub_left (hig U₁ hU₁ y hyI) (hig U₁ hU₁ x hx),
      ← integral_interval_sub_left (hiw U₁ hU₁ y hyI) (hiw U₁ hU₁ x hx)]
    ring
  have hE1 : |(∫ s in x..y, g s ∂SA.measure) - (Ap y - Ap x) * g x| ≤ ε / 2 * |Ap y - Ap x| := by
    have := integral_approx (ν := SA.measure) (hgc.mono (hsub x hx y hyI)) (ε := ε / 2)
      (fun s hs => by
        have hs' := hsub x hx y hyI hs
        have hds : dist s x < δg := by
          rw [Real.dist_eq]; exact lt_of_le_of_lt (abs_sub_le_of_mem_uIcc hs) (by
            rw [← Real.dist_eq]; exact hy.1)
        have := hg' hs' hds
        rw [Real.dist_eq] at this
        exact this.le)
    rwa [hlenA x hx y hyI] at this
  have hE2 : |(∫ s in x..y, w s) - (y - x) * w x| ≤ ε / 2 * |y - x| := by
    have := integral_approx (ν := volume) (hwc.mono (hsub x hx y hyI)) (ε := ε / 2)
      (fun s hs => by
        have hs' := hsub x hx y hyI hs
        have hds : dist s x < δw := by
          rw [Real.dist_eq]; exact lt_of_le_of_lt (abs_sub_le_of_mem_uIcc hs) (by
            rw [← Real.dist_eq]; exact hy.2)
        have := hw' hs' hds
        rw [Real.dist_eq] at this
        exact this.le)
    rwa [hlenV x y] at this
  have hLy := h.Lf_cutA_sol hm hyI'
  have hLx := h.Lf_cutA_sol hm hxI
  have hgx : 0 ≤ f (Ap x) - x := by
    have := h.le_f_sol hm hxI (Ap x)
      ⟨le_rfl, (h.cutA_le_mean hmx hxI.2).trans (h.mean_le_cutB hmx hxI.2)⟩
    linarith
  have hmax1 : max (f (Ap x) - x) 0 = g x := max_eq_left hgx
  have hmax2 : max (Ap x) (levA f x) = Ap x := max_eq_left (h.levA_le_cutA hmx hxI.2)
  have hPhi : Phi f (m x) x = max (mean f - Ap x) (Bp x - mean f) ^ 2 / 2 := Phi_of_nonneg hmx
  have hrx := hr x hx
  have hℓw : (mean f - Ap x) * w x
      = (max (mean f - Ap x) (Bp x - mean f) ^ 2 - (mean f - Ap x) ^ 2) / 2 := by
    simp only [hw, wLeft]
    rcases le_total (mean f - Ap x) (Bp x - mean f) with hlr | hlr
    · rw [max_eq_right hlr, max_eq_left (by nlinarith)]
      field_simp
    · rw [max_eq_left hlr, max_eq_right (by nlinarith)]
      simp
  have hy4' := hy4 hyI
  have hy3' := hy3 hyI
  have hLy' : Lf f (Ap y) y = m y := hLy
  have hLx' : Lf f (Ap x) x = m x := hLx
  rw [hLy', hLx', hmax1, hmax2] at hy4'
  rw [hPhi] at hy3'
  set dA := Ap y - Ap x with hdA
  set dU := y - x with hdU
  set ℓ := mean f - Ap x with hℓdef
  set M := max ℓ (Bp x - mean f) with hM
  have hD : ℓ * (dA * g x - dU * w x)
      = (m y - m x - (-(ℓ * g x)) * dA - (-(ℓ ^ 2 / 2)) * dU)
        - (m y - m x - dU * (-(M ^ 2 / 2))) := by
    linear_combination (-dU) * hℓw
  have hX : ℓ * |dA * g x - dU * w x| ≤ ℓ * (ε / 2 * (|dA| + |dU|)) := by
    rw [← abs_of_pos hℓx, ← abs_mul, hD, abs_of_pos hℓx]
    calc _ ≤ |m y - m x - (-(ℓ * g x)) * dA - (-(ℓ ^ 2 / 2)) * dU|
          + |m y - m x - dU * (-(M ^ 2 / 2))| := abs_sub _ _
      _ ≤ ε' * (|dA| + |dU|) + ε' * |dU| := add_le_add hy4' hy3'
      _ ≤ ℓ * (ε / 2 * (|dA| + |dU|)) := by
        simp only [hε'def]
        nlinarith [abs_nonneg dA, abs_nonneg dU]
  have hX' := le_of_mul_le_mul_left hX hℓx
  have hsame : |(Ap y + y) - (Ap x + x)| = |dA| + |dU| := by
    have he : (Ap y + y) - (Ap x + x) = dA + dU := by simp only [hdA, hdU]; ring
    rw [he]
    rcases le_total x y with hxy | hxy
    · have : Ap x ≤ Ap y := (h.cutA_sol_mono hm) hxI hyI' hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    · have : Ap y ≤ Ap x := (h.cutA_sol_mono hm) hyI' hxI hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
  rw [hΨd, hsame]
  calc _ ≤ |(∫ s in x..y, g s ∂SA.measure) - dA * g x| + |dA * g x - dU * w x|
        + |dU * w x - ∫ s in x..y, w s| := by
        have := abs_sub_le (∫ s in x..y, g s ∂SA.measure) (dA * g x) (∫ s in x..y, w s)
        have := abs_sub_le (dA * g x) (dU * w x) (∫ s in x..y, w s)
        linarith
    _ ≤ ε / 2 * |dA| + ε / 2 * (|dA| + |dU|) + ε / 2 * |dU| := by
        rw [abs_sub_comm (dU * w x)]
        linarith
    _ = ε * (|dA| + |dU|) := by ring

end Hyp

/-- Two measures with densities on `(0, T)` agree if they agree on every `(a, b]` with
`0 < a`, `b < T`. -/
lemma withDensity_eq_of_Ioc {ν₁ ν₂ : Measure ℝ} {G₁ G₂ : ℝ → ENNReal} {T : ℝ} (hT : 0 < T)
    (h : ∀ a b, 0 < a → b < T → ∫⁻ x in Ioc a b, G₁ x ∂ν₁ = ∫⁻ x in Ioc a b, G₂ x ∂ν₂)
    (hfin : ∀ a b, 0 < a → b < T → ∫⁻ x in Ioc a b, G₁ x ∂ν₁ ≠ ⊤) :
    (ν₁.restrict (Ioo 0 T)).withDensity G₁ = (ν₂.restrict (Ioo 0 T)).withDensity G₂ := by
  rw [← restrict_withDensity measurableSet_Ioo, ← restrict_withDensity measurableSet_Ioo]
  have hU : Ioo 0 T = ⋃ k : ℕ, Ioc (T / ((k : ℝ) + 2)) (T - T / ((k : ℝ) + 2)) := by
    ext x
    simp only [mem_Ioo, mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨hx0, hxT⟩
      obtain ⟨k, hk⟩ := exists_nat_gt (T / min x (T - x))
      have hmin : 0 < min x (T - x) := lt_min hx0 (by linarith)
      have hk2 : T / ((k : ℝ) + 2) < min x (T - x) := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hmin] at hk
        nlinarith
      exact ⟨k, lt_of_lt_of_le hk2 (min_le_left _ _),
        by linarith [min_le_right x (T - x)]⟩
    · rintro ⟨k, h1, h2⟩
      have : 0 < T / ((k : ℝ) + 2) := by positivity
      exact ⟨by linarith, by linarith⟩
  rw [hU, Measure.restrict_iUnion_congr]
  intro k
  set a := T / ((k : ℝ) + 2)
  set b := T - T / ((k : ℝ) + 2)
  have ha : 0 < a := by positivity
  have hb : b < T := by simp only [b]; linarith
  have : IsFiniteMeasure ((ν₁.withDensity G₁).restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, withDensity_apply _ measurableSet_Ioc]
        exact lt_top_iff_ne_top.2 (hfin a b ha hb)⟩
  refine Measure.ext_of_Ioc _ _ (fun c d _ => ?_)
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc, withDensity_apply _ measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc]
  exact h _ _ (lt_max_of_lt_right ha) (lt_of_le_of_lt (min_le_right _ _) hb)

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f) {m : ℝ → ℝ}
include h

lemma gA_contOn (hm : IsSol f m) :
    ContinuousOn (fun U => f (cutA f (m U) U) - U) (Ico 0 (f (mean f))) :=
  (h.cont.comp_continuousOn (h.cutA_sol_contOn hm)).sub continuousOn_id

lemma gA_nonneg (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    0 ≤ f (cutA f (m U) U) - U := by
  have hm0 := h.sol_nonneg hm hU
  have := h.le_f_sol hm hU (cutA f (m U) U)
    ⟨le_rfl, (h.cutA_le_mean hm0 hU.2).trans (h.mean_le_cutB hm0 hU.2)⟩
  linarith

lemma wLeft_contOn (hm : IsSol f m) :
    ContinuousOn (fun U => wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U))
      (Ico 0 (f (mean f))) := by
  have hA := h.cutA_sol_contOn hm
  have hB := h.cutB_sol_contOn hm
  refine ContinuousOn.div ?_ ?_ ?_
  · exact ContinuousOn.sup (((hB.sub continuousOn_const).pow 2).sub
      ((continuousOn_const.sub hA).pow 2)) continuousOn_const
  · exact continuousOn_const.mul (continuousOn_const.sub hA)
  · intro U hU
    exact (mul_pos two_pos (sub_pos.2 (h.cutA_lt_mean (h.sol_pos hm hU) hU.2))).ne'

lemma wLeft_nonneg (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    0 ≤ wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U) :=
  div_nonneg (le_max_right _ _)
    (mul_nonneg zero_le_two (sub_nonneg.2 (h.cutA_le_mean (h.sol_nonneg hm hU) hU.2)))

/-- **Theorem 34(c), left end**, as an equality of measures on `(0, f(μ))`:
`(f(A(U)) - U) dA(U) = (r² - ℓ²)⁺/(2ℓ) dU`, for any Stieltjes function `SA` equal to `A` up to a
constant on `[0, f(μ))`. -/
theorem peel_c_left (hm : IsSol f m) (SA : StieltjesFunction ℝ) (κ : ℝ)
    (hSA : ∀ U ∈ Ico 0 (f (mean f)), SA U = cutA f (m U) U + κ) :
    (SA.measure.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (f (cutA f (m U) U) - U)) =
      (volume.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U))) := by
  have hI : ∀ a b, 0 < a → b < f (mean f) → Icc a b ⊆ Ico 0 (f (mean f)) :=
    fun a b ha hb U hU => ⟨ha.le.trans hU.1, lt_of_le_of_lt hU.2 hb⟩
  have hg : ∀ a b, 0 < a → a ≤ b → b < f (mean f) →
      IntegrableOn (fun U => f (cutA f (m U) U) - U) (Ioc a b) SA.measure := fun a b ha hab hb =>
    (((h.gA_contOn hm).mono (hI a b ha hb)).mono (uIcc_of_le hab ▸ subset_rfl)
      |>.intervalIntegrable (μ := SA.measure)).1
  have hw : ∀ a b, 0 < a → a ≤ b → b < f (mean f) →
      IntegrableOn (fun U => wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U)) (Ioc a b) := by
    intro a b ha hab hb
    exact (((h.wLeft_contOn hm).mono (hI a b ha hb)).mono (uIcc_of_le hab ▸ subset_rfl)
      |>.intervalIntegrable (μ := volume)).1
  have hgn : ∀ a b, 0 < a → b < f (mean f) →
      0 ≤ᵐ[SA.measure.restrict (Ioc a b)] fun U => f (cutA f (m U) U) - U := fun a b ha hb =>
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun U hU =>
      h.gA_nonneg hm ⟨ha.le.trans hU.1.le, lt_of_le_of_lt hU.2 hb⟩)
  have hwn : ∀ a b, 0 < a → b < f (mean f) →
      0 ≤ᵐ[volume.restrict (Ioc a b)]
        fun U => wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U) := fun a b ha hb =>
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun U hU =>
      h.wLeft_nonneg hm ⟨ha.le.trans hU.1.le, lt_of_le_of_lt hU.2 hb⟩)
  apply withDensity_eq_of_Ioc h.f_mean_pos
  · intro a b ha hb
    rcases le_or_gt a b with hab | hab
    · rw [← ofReal_integral_eq_lintegral_ofReal (hg a b ha hab hb) (hgn a b ha hb),
        ← ofReal_integral_eq_lintegral_ofReal (hw a b ha hab hb) (hwn a b ha hb),
        ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab,
        h.c_core hm SA κ hSA ha.le hab hb]
    · rw [Ioc_eq_empty (not_lt.2 hab.le)]
      simp
  · intro a b ha hb
    rcases le_or_gt a b with hab | hab
    · rw [← ofReal_integral_eq_lintegral_ofReal (hg a b ha hab hb) (hgn a b ha hb)]
      exact ENNReal.ofReal_ne_top
    · rw [Ioc_eq_empty (not_lt.2 hab.le)]
      simp

/-- **Theorem 34(c), right end**: `(f(B(U)) - U) d(-B)(U) = (ℓ² - r²)⁺/(2r) dU` on
`(0, f(μ))`, for any Stieltjes function `SB` equal to `-B` up to a constant on `[0, f(μ))`. -/
theorem peel_c_right (hm : IsSol f m) (SB : StieltjesFunction ℝ) (κ : ℝ)
    (hSB : ∀ U ∈ Ico 0 (f (mean f)), SB U = -cutB f (m U) U + κ) :
    (SB.measure.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (f (cutB f (m U) U) - U)) =
      (volume.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (wRight (mean f) (cutA f (m U) U) (cutB f (m U) U))) := by
  have hl := h.refl_hyp
  have hml := h.isSol_refl.2 hm
  have key := hl.peel_c_left hml SB (κ - 1) (fun U hU => by
    rw [h.f_refl_mean] at hU
    rw [hSB U hU, h.cutB_eq (h.sol_nonneg hm hU) hU.2]
    ring)
  rw [h.f_refl_mean] at key
  have hae : ∀ G₁ G₂ : ℝ → ℝ, (∀ U ∈ Ioo 0 (f (mean f)), G₁ U = G₂ U) → ∀ ν : Measure ℝ,
      (ν.restrict (Ioo 0 (f (mean f)))).withDensity (fun U => ENNReal.ofReal (G₁ U)) =
        (ν.restrict (Ioo 0 (f (mean f)))).withDensity (fun U => ENNReal.ofReal (G₂ U)) := by
    intro G₁ G₂ hG ν
    apply withDensity_congr_ae
    exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun U hU => by simp only [hG U hU])
  rw [hae _ (fun U => f (cutB f (m U) U) - U) (fun U hU => by
      have hU' : U ∈ Ico 0 (f (mean f)) := ⟨hU.1.le, hU.2⟩
      simp only [refl]
      rw [h.cutA_refl (h.sol_nonneg hm hU') hU'.2, sub_sub_cancel]) SB.measure,
    hae _ (fun U => wRight (mean f) (cutA f (m U) U) (cutB f (m U) U)) (fun U hU => by
      have hU' : U ∈ Ico 0 (f (mean f)) := ⟨hU.1.le, hU.2⟩
      have hm0 := h.sol_nonneg hm hU'
      simp only [wLeft, wRight]
      rw [h.cutA_refl hm0 hU'.2, h.cutB_refl hm0 hU'.2, h.mean_refl]
      congr 1
      · congr 1; ring
      · ring) volume] at key
  exact key

end Hyp

/-! ## Theorem 34(d) -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f) {m : ℝ → ℝ}
include h

lemma int_bounds (hm : IsSol f m) {M : ℝ} (hM : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ M) {U : ℝ}
    (hU : U ∈ Ico 0 (f (mean f))) :
    0 ≤ ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U) ∧
      ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U)
        ≤ (M - U) * (cutB f (m U) U - cutA f (m U) U) := by
  have hm0 := h.sol_nonneg hm hU
  have hAB : cutA f (m U) U ≤ cutB f (m U) U :=
    (h.cutA_le_mean hm0 hU.2).trans (h.mean_le_cutB hm0 hU.2)
  have hle := h.le_f_sol hm hU
  have hA0 := h.cutA_nonneg hm0 hU.2
  have hB1 : cutB f (m U) U ≤ 1 := (h.cutB_le_levB hm0 hU.2).trans (h.levB_le_one hU.2.le)
  have hc : Continuous fun t => f t - U := h.cont.sub continuous_const
  constructor
  · exact intervalIntegral.integral_nonneg hAB (fun t ht => by linarith [hle t ht])
  · have := intervalIntegral.integral_mono_on hAB (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable (μ := volume) _ _) (g := fun _ => M - U)
      (fun t ht => by linarith [hM t ⟨hA0.trans ht.1, ht.2.trans hB1⟩])
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith

lemma d_flat (hm : IsSol f m) (hflat : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ f (mean f)) :
    Tendsto (fun U => ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U))
      (𝓝[<] (f (mean f))) (𝓝 0) := by
  have hev : ∀ᶠ U in 𝓝[<] (f (mean f)), U ∈ Ico 0 (f (mean f)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds h.f_mean_pos)] with U hU hU0
    exact ⟨hU0.le, hU⟩
  have hlim : Tendsto (fun U => f (mean f) - U) (𝓝[<] (f (mean f))) (𝓝 0) := by
    have : Tendsto (fun U => f (mean f) - U) (𝓝 (f (mean f))) (𝓝 (f (mean f) - f (mean f))) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [hev] with U hU
    exact (h.int_bounds hm hflat hU).1
  · filter_upwards [hev] with U hU
    have hb := (h.int_bounds hm hflat hU).2
    have hm0 := h.sol_nonneg hm hU
    have hA0 := h.cutA_nonneg hm0 hU.2
    have hB1 : cutB f (m U) U ≤ 1 :=
      (h.cutB_le_levB hm0 hU.2).trans (h.levB_le_one hU.2.le)
    have hAB : cutA f (m U) U ≤ cutB f (m U) U :=
      (h.cutA_le_mean hm0 hU.2).trans (h.mean_le_cutB hm0 hU.2)
    have : (f (mean f) - U) * (cutB f (m U) U - cutA f (m U) U) ≤ f (mean f) - U := by
      have h1 : 0 ≤ f (mean f) - U := by linarith [hU.2]
      nlinarith
    linarith

lemma Rf_mono {U y y' : ℝ} (hy : mean f ≤ y) (hyy' : y ≤ y') : Rf f y U ≤ Rf f y' U := by
  rw [← sub_sub_cancel 1 y, ← sub_sub_cancel 1 y', ← h.Lf_refl, ← h.Lf_refl]
  exact h.refl_hyp.Lf_anti (by linarith) (by rw [h.mean_refl]; linarith)

lemma d_right (hm : IsSol f m) {z : ℝ} (hz : mean f < z) (hz1 : z ≤ 1)
    (hfz : f (mean f) < f z) :
    Tendsto (fun U => ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U))
      (𝓝[<] (f (mean f))) (𝓝 0) := by
  obtain ⟨zM, hzM, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
    h.cont.continuousOn
  set M := f zM
  have hM : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ M := fun t ht => hmax ht
  have hev : ∀ᶠ U in 𝓝[<] (f (mean f)), U ∈ Ico 0 (f (mean f)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds h.f_mean_pos)] with U hU hU0
    exact ⟨hU0.le, hU⟩
  -- left of `μ`, `f < f(μ)`
  have hleft : ∀ x, 0 ≤ x → x < mean f → f x < f (mean f) := by
    intro x hx0 hx
    have h1 := h.q1 x (mean f) z hx0 hx.le hz.le hz1
    have hle : f x ≤ f (mean f) := by
      rcases min_le_iff.1 h1 with h' | h'
      · exact h'
      · linarith
    rcases hle.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (h.q2 x (mean f) z hx0 hx hz hz1 (by rw [h']; exact hfz)) (by rw [h']; simp)
  -- `A(U) → μ`
  have hA : Tendsto (fun U => cutA f (m U) U) (𝓝[<] (f (mean f))) (𝓝 (mean f)) := by
    rw [tendsto_order]
    constructor
    · intro x' hx'
      by_cases hx0 : x' < 0
      · filter_upwards [hev] with U hU
        exact lt_of_lt_of_le hx0 (h.cutA_nonneg (h.sol_nonneg hm hU) hU.2)
      push Not at hx0
      set x := (x' + mean f) / 2
      have hxx : x' < x := by simp only [x]; linarith
      have hxm : x < mean f := by simp only [x]; linarith
      have hfx := hleft x (by linarith) hxm
      filter_upwards [hev, nhdsWithin_le_nhds (lt_mem_nhds hfx)] with U hU hUx
      have hm0 := h.sol_nonneg hm hU
      refine lt_of_lt_of_le hxx (le_trans ?_ (h.levA_le_cutA hm0 hU.2))
      refine le_csInf ⟨_, h.mean_mem_lev hU.2.le⟩ (fun y hy => ?_)
      by_contra hyx
      push Not at hyx
      have h1 := h.q1 y x (mean f) hy.1.1 hyx.le hxm.le h.mean_lt_one.le
      have h2 : f y ≤ f x := by
        rcases min_le_iff.1 h1 with h' | h'
        · exact h'
        · linarith
      linarith [hy.2]
    · intro x' hx'
      filter_upwards [hev] with U hU
      exact lt_of_le_of_lt (h.cutA_le_mean (h.sol_nonneg hm hU) hU.2) hx'
  -- `B(U) → μ`
  have hB : Tendsto (fun U => cutB f (m U) U) (𝓝[<] (f (mean f))) (𝓝 (mean f)) := by
    rw [tendsto_order]
    constructor
    · intro x' hx'
      filter_upwards [hev] with U hU
      exact lt_of_lt_of_le hx' (h.mean_le_cutB (h.sol_nonneg hm hU) hU.2)
    · intro b hb
      set y := min ((mean f + b) / 2) z
      have hyμ : mean f < y := lt_min (by linarith) hz
      have hyb : y < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hyz : y ≤ z := min_le_right _ _
      have hc : 0 < Rf f y (f (mean f)) := by
        apply intervalIntegral.intervalIntegral_pos_of_pos_on
        · exact (by have := h.cont; fun_prop :
            Continuous fun t => (t - mean f) * max (f t - f (mean f)) 0).intervalIntegrable _ _
        · intro t ht
          have := h.q2 (mean f) t z h.mean_pos.le ht.1 (lt_of_lt_of_le ht.2 hyz) hz1 hfz
          exact mul_pos (by linarith [ht.1]) (lt_max_of_lt_left (by linarith))
        · exact hyμ
      have hlam0 : lam f (f (mean f)) = 0 := by
        unfold lam Lf
        rw [integral_congr (g := fun _ => (0:ℝ))]
        · simp
        intro t ht
        rw [uIcc_of_le h.mean_pos.le] at ht
        simp only
        rcases ht.2.lt_or_eq with h' | h'
        · rw [max_eq_right (by linarith [hleft t ht.1 h'])]; ring
        · rw [h']; simp
      have hRc : Continuous fun U => Rf f y U := by
        have e : (fun U => Rf f y U) = fun U => Lf (refl f) (1 - y) U := by
          funext U; rw [h.Lf_refl, sub_sub_cancel]
        rw [e]; exact h.refl_hyp.Lf_cont_U _
      have hlc : Continuous fun U => lam f U := h.Lf_cont_U 0
      have e1 : ∀ᶠ U in 𝓝 (f (mean f)), Rf f y (f (mean f)) / 2 < Rf f y U :=
        hRc.continuousAt.eventually (lt_mem_nhds (by linarith))
      have e2 : ∀ᶠ U in 𝓝 (f (mean f)), lam f U < Rf f y (f (mean f)) / 2 :=
        hlc.continuousAt.eventually (gt_mem_nhds (by show lam f _ < _; rw [hlam0]; linarith))
      filter_upwards [hev, nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2] with U hU h1 h2
      by_contra hBU
      push Not at hBU
      have h3 := h.Rf_mono (U := U) hyμ.le (hyb.le.trans hBU)
      rw [h.Rf_cutB_sol hm hU] at h3
      have h4 := h.sol_le_lam hm hU
      linarith
  have hlim : Tendsto (fun U => (M - U) * (cutB f (m U) U - cutA f (m U) U))
      (𝓝[<] (f (mean f))) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := M)).sub (tendsto_id.mono_left nhdsWithin_le_nhds)).mul
      (hB.sub hA)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (by filter_upwards [hev] with U hU; exact (h.int_bounds hm hM hU).1)
    (by filter_upwards [hev] with U hU; exact (h.int_bounds hm hM hU).2)

/-- **Theorem 34(d)**: `∫_{A(U)}^{B(U)} (f - U) → 0` as `U → f(μ)`. -/
theorem peel_d (hm : IsSol f m) :
    Tendsto (fun U => ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U))
      (𝓝[<] (f (mean f))) (𝓝 0) := by
  by_cases hex : ∃ z ∈ Icc (0:ℝ) 1, f (mean f) < f z
  · obtain ⟨z, hz, hfz⟩ := hex
    rcases lt_trichotomy z (mean f) with hlt | heq | hgt
    · -- reflect
      have hl := h.refl_hyp
      have key := hl.d_right (h.isSol_refl.2 hm) (z := 1 - z)
        (by rw [h.mean_refl]; linarith) (by linarith [hz.1])
        (by simp only [refl, sub_sub_cancel]; rw [h.mean_refl, sub_sub_cancel]; exact hfz)
      rw [h.f_refl_mean] at key
      refine key.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (lt_mem_nhds h.f_mean_pos)] with U hU hU0
      have hU' : U ∈ Ico 0 (f (mean f)) := ⟨hU0.le, hU⟩
      have hm0 := h.sol_nonneg hm hU'
      rw [h.cutA_refl hm0 hU'.2, h.cutB_refl hm0 hU'.2]
      simp only [refl]
      rw [intervalIntegral.integral_comp_sub_left (fun s => f s - U)]
      simp only [sub_sub_cancel]
    · rw [heq] at hfz; exact absurd hfz (lt_irrefl _)
    · exact h.d_right hm hgt hz.2 hfz
  · push Not at hex
    exact h.d_flat hm hex

end Hyp

/-! ## Lemma 33 for `R` -/

namespace Hyp

variable {f : ℝ → ℝ} (h : Hyp f)
include h

lemma Rf_hasDerivAt_U {y U : ℝ} (hy : mean f ≤ y) (hy1 : y ≤ 1) (hU : U < f (mean f)) :
    HasDerivAt (fun U => Rf f y U) (-((min y (levB f U) - mean f) ^ 2 / 2)) U := by
  have := h.refl_hyp.Lf_hasDerivAt_U (x := 1 - y) (by linarith)
    (by rw [h.mean_refl]; linarith) (by rw [h.f_refl_mean]; exact hU)
  have e : (fun U => Lf (refl f) (1 - y) U) = fun U => Rf f y U := by
    funext U; rw [h.Lf_refl, sub_sub_cancel]
  rw [e, h.levA_refl hU.le, h.mean_refl, max_sub_sub_left] at this
  convert this using 2
  ring

lemma Rf_eq_rho {y U : ℝ} (hU : U < f (mean f)) (hby : levB f U ≤ y) (hy1 : y ≤ 1) :
    Rf f y U = rho f U := by
  have := h.refl_hyp.Lf_eq_lam (x := 1 - y) (U := U) (by rw [h.f_refl_mean]; exact hU)
    (by linarith) (by rw [h.levA_refl hU.le]; linarith)
  rw [h.Lf_refl, sub_sub_cancel, h.lam_refl] at this
  exact this

lemma Rf_strictMono {U : ℝ} (hU : U < f (mean f)) :
    StrictMonoOn (fun y => Rf f y U) (Icc (mean f) (levB f U)) := by
  intro y hy y' hy' hyy'
  have := h.refl_hyp.Lf_strictAnti (U := U) (by rw [h.f_refl_mean]; exact hU)
    (a := 1 - y') (b := 1 - y)
    (by rw [h.levA_refl hU.le, h.mean_refl]; exact ⟨by linarith [hy'.2], by linarith [hy'.1]⟩)
    (by rw [h.levA_refl hU.le, h.mean_refl]; exact ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    (by linarith)
  simp only [h.Lf_refl, sub_sub_cancel] at this
  exact this

end Hyp

lemma Rf_mean (f : ℝ → ℝ) (U : ℝ) : Rf f (mean f) U = 0 := integral_same

/-! ## Functions agreeing on `[0, 1]` -/

section Congr

variable {f g : ℝ → ℝ} (hfg : EqOn f g (Icc 0 1))
include hfg

lemma mean_congr : mean f = mean g := by
  unfold mean
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  simp only [hfg ht]

lemma lev_congr (U : ℝ) : lev f U = lev g U := by
  ext x
  simp only [lev, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h'⟩; exact ⟨hx, by rwa [← hfg hx]⟩
  · rintro ⟨hx, h'⟩; exact ⟨hx, by rwa [hfg hx]⟩

lemma levA_congr (U : ℝ) : levA f U = levA g U := by unfold levA; rw [lev_congr hfg]

lemma levB_congr (U : ℝ) : levB f U = levB g U := by unfold levB; rw [lev_congr hfg]

variable (hμ : mean f ∈ Icc (0:ℝ) 1)
include hμ

lemma Lf_congr {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (U : ℝ) : Lf f x U = Lf g x U := by
  unfold Lf
  rw [← mean_congr hfg]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  simp only [hfg (uIcc_subset_Icc hx hμ ht)]

lemma Rf_congr {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) (U : ℝ) : Rf f y U = Rf g y U := by
  unfold Rf
  rw [← mean_congr hfg]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  simp only [hfg (uIcc_subset_Icc hμ hy ht)]

lemma lam_congr (U : ℝ) : lam f U = lam g U :=
  Lf_congr hfg hμ ⟨le_rfl, zero_le_one⟩ U

lemma rho_congr (U : ℝ) : rho f U = rho g U :=
  Rf_congr hfg hμ ⟨zero_le_one, le_rfl⟩ U

omit hμ in
lemma m0_congr : m0 f = m0 g := by
  unfold m0
  rw [← mean_congr hfg]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  simp only [hfg ht]

lemma cutA_congr (m U : ℝ) : cutA f m U = cutA g m U := by
  unfold cutA
  rw [← levA_congr hfg, ← mean_congr hfg]
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  have h0 : 0 ≤ levA f U := Real.sInf_nonneg (fun x hx => hx.1.1)
  constructor
  · rintro ⟨hx, h'⟩
    exact ⟨hx, by rwa [← Lf_congr hfg hμ ⟨h0.trans hx.1, hx.2.trans hμ.2⟩]⟩
  · rintro ⟨hx, h'⟩
    exact ⟨hx, by rwa [Lf_congr hfg hμ ⟨h0.trans hx.1, hx.2.trans hμ.2⟩]⟩

lemma cutB_congr (m U : ℝ) : cutB f m U = cutB g m U := by
  unfold cutB
  rw [← levB_congr hfg, ← mean_congr hfg]
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  have h1 : levB f U ≤ 1 := Real.sSup_le (fun x hx => hx.1.2) zero_le_one
  constructor
  · rintro ⟨hx, h'⟩
    exact ⟨hx, by rwa [← Rf_congr hfg hμ ⟨hμ.1.trans hx.1, hx.2.trans h1⟩]⟩
  · rintro ⟨hx, h'⟩
    exact ⟨hx, by rwa [Rf_congr hfg hμ ⟨hμ.1.trans hx.1, hx.2.trans h1⟩]⟩

lemma Phi_congr : Phi f = Phi g := by
  funext m U
  unfold Phi
  rw [cutA_congr hfg hμ, cutB_congr hfg hμ, mean_congr hfg]

lemma isSol_congr (m : ℝ → ℝ) : IsSol f m ↔ IsSol g m := by
  have e : f (mean f) = g (mean g) := by rw [hfg hμ, mean_congr hfg]
  unfold IsSol
  rw [m0_congr hfg, Phi_congr hfg hμ, e]

end Congr

/-! ## Hypotheses on `[0, 1]` only -/

/-- `f` is a **strictly unimodal probability density on `[0, 1]`**, continuous on `[0, 1]`
(the standing hypothesis of the section): there are `0 ≤ c₁ ≤ c₂ ≤ 1` with `f` strictly
increasing on `[0, c₁]`, constant on `[c₁, c₂]` and strictly decreasing on `[c₂, 1]`. -/
structure UnimodalDensity (f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Icc 0 1)
  nonneg : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x
  int_one : ∫ x in (0:ℝ)..1, f x = 1
  unimodal : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ c₁ ≤ c₂ ∧ c₂ ≤ 1 ∧ StrictMonoOn f (Icc 0 c₁) ∧
    (∀ x ∈ Icc c₁ c₂, f x = f c₁) ∧ StrictAntiOn f (Icc c₂ 1)

/-- A probability density on `[0, 1]`, continuous on `[0, 1]` and strictly quasi-concave there
(`q1`–`q3`); implied by strict unimodality and by concavity. -/
structure QCDensity (f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Icc 0 1)
  nonneg : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x
  int_one : ∫ x in (0:ℝ)..1, f x = 1
  q1 : ∀ x t y, 0 ≤ x → x ≤ t → t ≤ y → y ≤ 1 → min (f x) (f y) ≤ f t
  q2 : ∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 → f x < f y → f x < f t
  q3 : ∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 → f y < f x → f y < f t

lemma UnimodalDensity.qc {f : ℝ → ℝ} (hf : UnimodalDensity f) : QCDensity f := by
  obtain ⟨c₁, c₂, h0, h12, h1, hinc, hconst, hdec⟩ := hf.unimodal
  have hmax : ∀ s ∈ Icc (0:ℝ) 1, f s ≤ f c₁ := by
    intro s hs
    rcases le_total s c₁ with h' | h'
    · exact hinc.monotoneOn ⟨hs.1, h'⟩ ⟨h0, le_rfl⟩ h'
    rcases le_total s c₂ with h'' | h''
    · exact (hconst s ⟨h', h''⟩).le
    · rw [← hconst c₂ ⟨h12, le_rfl⟩]
      exact hdec.antitoneOn ⟨le_rfl, h1⟩ ⟨h'', hs.2⟩ h''
  refine ⟨hf.cont, hf.nonneg, hf.int_one, ?_, ?_, ?_⟩
  · intro x t y hx hxt hty hy
    rcases le_total t c₁ with h' | h'
    · exact min_le_of_left_le (hinc.monotoneOn ⟨hx, hxt.trans h'⟩ ⟨hx.trans hxt, h'⟩ hxt)
    rcases le_total c₂ t with h'' | h''
    · exact min_le_of_right_le
        (hdec.antitoneOn ⟨h'', (hty.trans hy)⟩ ⟨h''.trans hty, hy⟩ hty)
    · rw [hconst t ⟨h', h''⟩]
      exact min_le_of_left_le (hmax x ⟨hx, by linarith⟩)
  · intro x t y hx hxt hty hy hlt
    rcases le_total t c₁ with h' | h'
    · exact hinc ⟨hx, by linarith⟩ ⟨by linarith, h'⟩ hxt
    rcases le_total t c₂ with h'' | h''
    · rw [hconst t ⟨h', h''⟩]
      exact lt_of_lt_of_le hlt (hmax y ⟨by linarith, hy⟩)
    · exact hlt.trans (hdec ⟨h'', by linarith⟩ ⟨by linarith, hy⟩ hty)
  · intro x t y hx hxt hty hy hlt
    rcases le_total c₂ t with h' | h'
    · exact hdec ⟨h', by linarith⟩ ⟨by linarith, hy⟩ hty
    rcases le_total c₁ t with h'' | h''
    · rw [hconst t ⟨h'', h'⟩]
      exact lt_of_lt_of_le hlt (hmax x ⟨hx, by linarith⟩)
    · exact hlt.trans (hinc ⟨hx, by linarith⟩ ⟨by linarith, h''⟩ hxt)

/-- A continuous concave probability density on `[0, 1]` is strictly quasi-concave. -/
lemma QCDensity.of_concave {f : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc 0 1) f)
    (hfc : ContinuousOn f (Icc 0 1)) (hf0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0:ℝ)..1, f x = 1) : QCDensity f := by
  -- `t = a x + b y` with `a = (y - t)/(y - x)`, `b = (t - x)/(y - x)`
  have key : ∀ x t y, 0 ≤ x → x < t → t < y → y ≤ 1 →
      (y - t) / (y - x) * f x + (t - x) / (y - x) * f y ≤ f t := by
    intro x t y hx hxt hty hy
    have hyx : 0 < y - x := by linarith
    have := hconc.2 (⟨hx, by linarith⟩ : x ∈ Icc (0:ℝ) 1) (⟨by linarith, hy⟩ : y ∈ Icc (0:ℝ) 1)
      (div_nonneg (by linarith : (0:ℝ) ≤ y - t) hyx.le)
      (div_nonneg (by linarith : (0:ℝ) ≤ t - x) hyx.le)
      (by field_simp; ring)
    simp only [smul_eq_mul] at this
    convert this using 2
    field_simp
    ring
  have hab : ∀ x t y : ℝ, x < y → (y - t) / (y - x) + (t - x) / (y - x) = 1 := by
    intro x t y hxy
    have : y - x ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨hfc, hf0, hf1, ?_, ?_, ?_⟩
  · intro x t y hx hxt hty hy
    rcases hxt.lt_or_eq with hxt | rfl
    · rcases hty.lt_or_eq with hty | rfl
      · have := key x t y hx hxt hty hy
        have hyx : 0 < y - x := by linarith
        have e := hab x t y (hxt.trans hty)
        have h1 : 0 ≤ (y - t) / (y - x) := div_nonneg (by linarith) hyx.le
        have h2 : 0 ≤ (t - x) / (y - x) := div_nonneg (by linarith) hyx.le
        have i1 := mul_le_mul_of_nonneg_left (min_le_left (f x) (f y)) h1
        have i2 := mul_le_mul_of_nonneg_left (min_le_right (f x) (f y)) h2
        have e2 : (y - t) / (y - x) * min (f x) (f y) + (t - x) / (y - x) * min (f x) (f y)
            = min (f x) (f y) := by rw [← add_mul, e, one_mul]
        linarith
      · exact min_le_right _ _
    · exact min_le_left _ _
  · intro x t y hx hxt hty hy hlt
    have := key x t y hx hxt hty hy
    have hyx : 0 < y - x := by linarith
    have e := hab x t y (hxt.trans hty)
    have h2 : 0 < (t - x) / (y - x) := div_pos (by linarith) hyx
    have i2 := mul_lt_mul_of_pos_left hlt h2
    have e2 : (y - t) / (y - x) * f x + (t - x) / (y - x) * f x = f x := by
      rw [← add_mul, e, one_mul]
    linarith
  · intro x t y hx hxt hty hy hlt
    have := key x t y hx hxt hty hy
    have hyx : 0 < y - x := by linarith
    have e := hab x t y (hxt.trans hty)
    have h1 : 0 < (y - t) / (y - x) := div_pos (by linarith) hyx
    have i1 := mul_lt_mul_of_pos_left hlt h1
    have e2 : (y - t) / (y - x) * f y + (t - x) / (y - x) * f y = f y := by
      rw [← add_mul, e, one_mul]
    linarith

/-- The extension `x ↦ f (max 0 (min 1 x))` of a function on `[0, 1]` to `ℝ`. -/
def ext01 (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (max 0 (min 1 x))

lemma ext01_eqOn (f : ℝ → ℝ) : EqOn f (ext01 f) (Icc 0 1) := fun x hx => by
  simp only [ext01, min_eq_right hx.2, max_eq_right hx.1]

lemma QCDensity.hyp {f : ℝ → ℝ} (hf : QCDensity f) : Hyp (ext01 f) := by
  have e := ext01_eqOn f
  refine ⟨?_, fun x hx => by rw [← e hx]; exact hf.nonneg x hx, ?_, ?_, ?_, ?_⟩
  · have : Continuous fun x : ℝ => max 0 (min 1 x) := by fun_prop
    exact hf.cont.comp_continuous this (fun x => ⟨le_max_left _ _,
      max_le zero_le_one (min_le_left _ _)⟩)
  · refine (intervalIntegral.integral_congr (g := f) (fun t ht => ?_)).trans hf.int_one
    rw [uIcc_of_le zero_le_one] at ht
    exact (e ht).symm
  · intro x t y hx hxt hty hy
    rw [← e (show x ∈ Icc (0:ℝ) 1 from ⟨hx, by linarith⟩),
      ← e (show t ∈ Icc (0:ℝ) 1 from ⟨by linarith, by linarith⟩),
      ← e (show y ∈ Icc (0:ℝ) 1 from ⟨by linarith, hy⟩)]
    exact hf.q1 x t y hx hxt hty hy
  · intro x t y hx hxt hty hy
    rw [← e (show x ∈ Icc (0:ℝ) 1 from ⟨hx, by linarith⟩),
      ← e (show t ∈ Icc (0:ℝ) 1 from ⟨by linarith, by linarith⟩),
      ← e (show y ∈ Icc (0:ℝ) 1 from ⟨by linarith, hy⟩)]
    exact hf.q2 x t y hx hxt hty hy
  · intro x t y hx hxt hty hy
    rw [← e (show x ∈ Icc (0:ℝ) 1 from ⟨hx, by linarith⟩),
      ← e (show t ∈ Icc (0:ℝ) 1 from ⟨by linarith, by linarith⟩),
      ← e (show y ∈ Icc (0:ℝ) 1 from ⟨by linarith, hy⟩)]
    exact hf.q3 x t y hx hxt hty hy

lemma cutA_mem01 {f : ℝ → ℝ} (hμ : mean f ∈ Icc (0:ℝ) 1) (m U : ℝ) :
    cutA f m U ∈ Icc (0:ℝ) 1 := by
  unfold cutA
  set S := {x | x ∈ Icc (levA f U) (mean f) ∧ Lf f x U ≤ m}
  have h0 : 0 ≤ levA f U := Real.sInf_nonneg (fun x hx => hx.1.1)
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Real.sInf_empty]; exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨x, hx⟩ := hS
    exact ⟨le_csInf ⟨x, hx⟩ (fun y (hy : y ∈ S) => h0.trans hy.1.1),
      (csInf_le ⟨0, fun y (hy : y ∈ S) => h0.trans hy.1.1⟩ hx).trans (hx.1.2.trans hμ.2)⟩

lemma cutB_mem01 {f : ℝ → ℝ} (hμ : mean f ∈ Icc (0:ℝ) 1) (m U : ℝ) :
    cutB f m U ∈ Icc (0:ℝ) 1 := by
  unfold cutB
  set S := {y | y ∈ Icc (mean f) (levB f U) ∧ Rf f y U ≤ m}
  have h1 : levB f U ≤ 1 := Real.sSup_le (fun x hx => hx.1.2) zero_le_one
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Real.sSup_empty]; exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨x, hx⟩ := hS
    exact ⟨hμ.1.trans (hx.1.1.trans (le_csSup ⟨1, fun y (hy : y ∈ S) => hy.1.2.trans h1⟩ hx)),
      csSup_le ⟨x, hx⟩ (fun y (hy : y ∈ S) => hy.1.2.trans h1)⟩

namespace QCDensity

variable {f : ℝ → ℝ} (hf : QCDensity f)
include hf

set_option linter.unusedSectionVars false in
lemma mean_eq : mean (ext01 f) = mean f := (mean_congr (ext01_eqOn f)).symm

lemma mean_mem : mean f ∈ Ioo (0:ℝ) 1 := by rw [← hf.mean_eq]; exact hf.hyp.mean_mem

lemma mem01 : mean f ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hf.mean_mem

lemma fmean_eq : ext01 f (mean (ext01 f)) = f (mean f) := by
  rw [hf.mean_eq]; exact (ext01_eqOn f hf.mem01).symm

lemma f_mean_pos : 0 < f (mean f) := by rw [← hf.fmean_eq]; exact hf.hyp.f_mean_pos

lemma isSol_iff (m : ℝ → ℝ) : IsSol f m ↔ IsSol (ext01 f) m :=
  isSol_congr (ext01_eqOn f) hf.mem01 m

lemma cutA_eq (m U : ℝ) : cutA (ext01 f) m U = cutA f m U :=
  (cutA_congr (ext01_eqOn f) hf.mem01 m U).symm

lemma cutB_eq (m U : ℝ) : cutB (ext01 f) m U = cutB f m U :=
  (cutB_congr (ext01_eqOn f) hf.mem01 m U).symm

set_option linter.unusedSectionVars false in
lemma levA_eq (U : ℝ) : levA (ext01 f) U = levA f U := (levA_congr (ext01_eqOn f) U).symm

set_option linter.unusedSectionVars false in
lemma levB_eq (U : ℝ) : levB (ext01 f) U = levB f U := (levB_congr (ext01_eqOn f) U).symm

lemma lam_eq (U : ℝ) : lam (ext01 f) U = lam f U := (lam_congr (ext01_eqOn f) hf.mem01 U).symm

lemma rho_eq (U : ℝ) : rho (ext01 f) U = rho f U := (rho_congr (ext01_eqOn f) hf.mem01 U).symm

lemma Lf_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (U : ℝ) : Lf (ext01 f) x U = Lf f x U :=
  (Lf_congr (ext01_eqOn f) hf.mem01 hx U).symm

lemma Rf_eq {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) (U : ℝ) : Rf (ext01 f) y U = Rf f y U :=
  (Rf_congr (ext01_eqOn f) hf.mem01 hy U).symm

set_option linter.unusedSectionVars false in
lemma f_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : ext01 f x = f x := (ext01_eqOn f hx).symm

lemma hU_eq {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) : U ∈ Ico 0 (ext01 f (mean (ext01 f))) := by
  rw [hf.fmean_eq]; exact hU

/-! ### Lemma 33 -/

theorem L_continuousOn : ContinuousOn (fun p : ℝ × ℝ => Lf f p.1 p.2) (Icc 0 1 ×ˢ univ) :=
  hf.hyp.Lf_continuous.continuousOn.congr (fun p hp => (hf.Lf_eq hp.1 p.2).symm)

theorem L_hasDerivWithinAt_x {x U : ℝ} (hx : x ∈ Icc 0 (mean f)) :
    HasDerivWithinAt (fun x => Lf f x U) (-((mean f - x) * max (f x - U) 0))
      (Icc 0 (mean f)) x := by
  have hx1 : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.trans hf.mem01.2⟩
  have := (hf.hyp.Lf_hasDerivAt_x x U).hasDerivWithinAt (s := Icc 0 (mean f))
  rw [hf.mean_eq, hf.f_eq hx1] at this
  exact this.congr (fun y hy => (hf.Lf_eq ⟨hy.1, hy.2.trans hf.mem01.2⟩ U).symm)
    (hf.Lf_eq hx1 U).symm

theorem L_hasDerivAt_U {x U : ℝ} (hx0 : 0 ≤ x) (hxm : x ≤ mean f) (hU : U < f (mean f)) :
    HasDerivAt (fun U => Lf f x U) (-((mean f - max x (levA f U)) ^ 2 / 2)) U := by
  have hx1 : x ∈ Icc (0:ℝ) 1 := ⟨hx0, hxm.trans hf.mem01.2⟩
  have := hf.hyp.Lf_hasDerivAt_U hx0 (by rw [hf.mean_eq]; exact hxm)
    (by rw [hf.fmean_eq]; exact hU)
  have e : (fun U => Lf (ext01 f) x U) = fun U => Lf f x U := funext (hf.Lf_eq hx1)
  rw [e, hf.mean_eq, hf.levA_eq] at this
  exact this

theorem L_local {x₀ U₀ : ℝ} (hx0 : 0 ≤ x₀) (hxm : x₀ ≤ mean f) (hU : U₀ < f (mean f))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ p : ℝ × ℝ in 𝓝[Icc 0 1 ×ˢ univ] (x₀, U₀),
      |Lf f p.1 p.2 - Lf f x₀ U₀ - (-((mean f - x₀) * max (f x₀ - U₀) 0)) * (p.1 - x₀)
        - (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2)) * (p.2 - U₀)|
        ≤ ε * (|p.1 - x₀| + |p.2 - U₀|) := by
  have hx1 : x₀ ∈ Icc (0:ℝ) 1 := ⟨hx0, hxm.trans hf.mem01.2⟩
  have := hf.hyp.Lf_local hx0 (by rw [hf.mean_eq]; exact hxm)
    (by rw [hf.fmean_eq]; exact hU) hε
  rw [hf.mean_eq, hf.levA_eq, hf.f_eq hx1, hf.Lf_eq hx1] at this
  filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with p hp hmem
  rw [← hf.Lf_eq hmem.1]
  exact hp

theorem L_shape {U : ℝ} (hU : U < f (mean f)) :
    (∀ x ∈ Icc 0 (levA f U), Lf f x U = lam f U) ∧
      StrictAntiOn (fun x => Lf f x U) (Icc (levA f U) (mean f)) ∧ Lf f (mean f) U = 0 := by
  have hU' : U < ext01 f (mean (ext01 f)) := by rw [hf.fmean_eq]; exact hU
  have ha : levA f U ≤ mean f := by
    rw [← hf.levA_eq, ← hf.mean_eq]; exact hf.hyp.levA_le_mean hU'.le
  refine ⟨fun x hx => ?_, fun a ha' b hb hab => ?_, integral_same⟩
  · have hx1 : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.trans (ha.trans hf.mem01.2)⟩
    rw [← hf.Lf_eq hx1, ← hf.lam_eq]
    exact hf.hyp.Lf_eq_lam hU' hx.1 (by rw [hf.levA_eq]; exact hx.2)
  · have h0 : 0 ≤ levA f U := Real.sInf_nonneg (fun x hx => hx.1.1)
    have := hf.hyp.Lf_strictAnti hU'
    rw [hf.levA_eq, hf.mean_eq] at this
    have := this ha' hb hab
    simp only at this ⊢
    rwa [hf.Lf_eq ⟨h0.trans ha'.1, ha'.2.trans hf.mem01.2⟩,
      hf.Lf_eq ⟨h0.trans hb.1, hb.2.trans hf.mem01.2⟩] at this

theorem R_hasDerivAt_U {y U : ℝ} (hy : mean f ≤ y) (hy1 : y ≤ 1) (hU : U < f (mean f)) :
    HasDerivAt (fun U => Rf f y U) (-((min y (levB f U) - mean f) ^ 2 / 2)) U := by
  have hy01 : y ∈ Icc (0:ℝ) 1 := ⟨hf.mem01.1.trans hy, hy1⟩
  have := hf.hyp.Rf_hasDerivAt_U (by rw [hf.mean_eq]; exact hy) hy1
    (by rw [hf.fmean_eq]; exact hU)
  have e : (fun U => Rf (ext01 f) y U) = fun U => Rf f y U := funext (hf.Rf_eq hy01)
  rw [e, hf.mean_eq, hf.levB_eq] at this
  exact this

theorem R_shape {U : ℝ} (hU : U < f (mean f)) :
    (∀ y ∈ Icc (levB f U) 1, Rf f y U = rho f U) ∧
      StrictMonoOn (fun y => Rf f y U) (Icc (mean f) (levB f U)) ∧ Rf f (mean f) U = 0 := by
  have hU' : U < ext01 f (mean (ext01 f)) := by rw [hf.fmean_eq]; exact hU
  have hb : mean f ≤ levB f U := by
    rw [← hf.levB_eq, ← hf.mean_eq]; exact hf.hyp.mean_le_levB hU'.le
  refine ⟨fun y hy => ?_, fun a ha' b hb' hab => ?_, integral_same⟩
  · have hy1 : y ∈ Icc (0:ℝ) 1 := ⟨hf.mem01.1.trans (hb.trans hy.1), hy.2⟩
    rw [← hf.Rf_eq hy1, ← hf.rho_eq]
    exact hf.hyp.Rf_eq_rho hU' (by rw [hf.levB_eq]; exact hy.1) hy.2
  · have h1 : levB f U ≤ 1 := Real.sSup_le (fun x hx => hx.1.2) zero_le_one
    have := hf.hyp.Rf_strictMono hU'
    rw [hf.levB_eq, hf.mean_eq] at this
    have := this ha' hb' hab
    simp only at this ⊢
    rwa [hf.Rf_eq ⟨hf.mem01.1.trans ha'.1, ha'.2.trans h1⟩,
      hf.Rf_eq ⟨hf.mem01.1.trans hb'.1, hb'.2.trans h1⟩] at this

/-! ### Theorem 34 -/

theorem exists_unique_sol : (∃ m, IsSol f m) ∧
    ∀ m₁ m₂, IsSol f m₁ → IsSol f m₂ → EqOn m₁ m₂ (Ico 0 (f (mean f))) := by
  refine ⟨?_, fun m₁ m₂ h₁ h₂ => ?_⟩
  · obtain ⟨m, hm⟩ := hf.hyp.sol_exists
    exact ⟨m, (hf.isSol_iff m).2 hm⟩
  · have := hf.hyp.sol_unique ((hf.isSol_iff _).1 h₁) ((hf.isSol_iff _).1 h₂)
    rwa [hf.fmean_eq] at this

variable {m : ℝ → ℝ}

theorem sol_C1 (hm : IsSol f m) :
    ContinuousOn (fun U => Phi f (m U) U) (Ico 0 (f (mean f))) := by
  have hm' := (hf.isSol_iff m).1 hm
  have hp : ContinuousOn (fun U => (m U, U)) (Ico 0 (f (mean f))) := by
    have := (Hyp.sol_contOn_Ico hm').prodMk continuousOn_id
    rwa [hf.fmean_eq] at this
  have hP := hf.hyp.Phi_continuousOn
  rw [hf.fmean_eq] at hP
  have : ContinuousOn ((fun p : ℝ × ℝ => Phi (ext01 f) p.1 p.2) ∘ (fun U => (m U, U)))
      (Ico 0 (f (mean f))) :=
    ContinuousOn.comp (g := fun p : ℝ × ℝ => Phi (ext01 f) p.1 p.2) hP hp
      (fun U hU => ⟨trivial, hU.2⟩)
  rw [← Phi_congr (ext01_eqOn f) hf.mem01] at this
  exact this

theorem sol_a (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    0 < m U ∧ m U ≤ lam f U ∧ m U ≤ rho f U ∧
      Lf f (cutA f (m U) U) U = m U ∧ Rf f (cutB f (m U) U) U = m U ∧
      (∀ t ∈ Icc (cutA f (m U) U) (cutB f (m U) U), U ≤ f t) ∧
      ∫ t in cutA f (m U) U..cutB f (m U) U, (t - mean f) * (f t - U) = 0 := by
  have hm' := (hf.isSol_iff m).1 hm
  have hU' := hf.hU_eq hU
  have hA := cutA_mem01 hf.mem01 (m U) U
  have hB := cutB_mem01 hf.mem01 (m U) U
  refine ⟨hf.hyp.sol_pos hm' hU', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hf.lam_eq]; exact hf.hyp.sol_le_lam hm' hU'
  · rw [← hf.rho_eq]; exact hf.hyp.sol_le_rho hm' hU'
  · rw [← hf.Lf_eq hA, ← hf.cutA_eq]; exact hf.hyp.Lf_cutA_sol hm' hU'
  · rw [← hf.Rf_eq hB, ← hf.cutB_eq]; exact hf.hyp.Rf_cutB_sol hm' hU'
  · intro t ht
    have := hf.hyp.le_f_sol hm' hU' t (by rw [hf.cutA_eq, hf.cutB_eq]; exact ht)
    rwa [hf.f_eq ⟨hA.1.trans ht.1, ht.2.trans hB.2⟩] at this
  · have := hf.hyp.mean_sol hm' hU'
    rw [hf.cutA_eq, hf.cutB_eq, hf.mean_eq] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    simp only [hf.f_eq (uIcc_subset_Icc hA hB ht)]

theorem sol_b (hm : IsSol f m) :
    cutA f (m 0) 0 = 0 ∧ cutB f (m 0) 0 = 1 ∧
      (∀ U ∈ Ico 0 (f (mean f)), levA f U ≤ cutA f (m U) U ∧ cutA f (m U) U < mean f ∧
        mean f < cutB f (m U) U ∧ cutB f (m U) U ≤ levB f U) ∧
      ContinuousOn (fun U => cutA f (m U) U) (Ico 0 (f (mean f))) ∧
      ContinuousOn (fun U => cutB f (m U) U) (Ico 0 (f (mean f))) ∧
      MonotoneOn (fun U => cutA f (m U) U) (Ico 0 (f (mean f))) ∧
      AntitoneOn (fun U => cutB f (m U) U) (Ico 0 (f (mean f))) := by
  have hm' := (hf.isSol_iff m).1 hm
  have eA : (fun U => cutA (ext01 f) (m U) U) = fun U => cutA f (m U) U :=
    funext fun U => hf.cutA_eq _ _
  have eB : (fun U => cutB (ext01 f) (m U) U) = fun U => cutB f (m U) U :=
    funext fun U => hf.cutB_eq _ _
  have h1 := hf.hyp.cutA_sol_contOn hm'
  have h2 := hf.hyp.cutB_sol_contOn hm'
  have h3 := hf.hyp.cutA_sol_mono hm'
  have h4 := hf.hyp.cutB_sol_anti hm'
  rw [eA, hf.fmean_eq] at h1 h3
  rw [eB, hf.fmean_eq] at h2 h4
  refine ⟨?_, ?_, fun U hU => ?_, h1, h2, h3, h4⟩
  · rw [← hf.cutA_eq]; exact hf.hyp.cutA_sol_zero hm'
  · rw [← hf.cutB_eq]; exact hf.hyp.cutB_sol_zero hm'
  · have hU' := hf.hU_eq hU
    have hp := hf.hyp.sol_pos hm' hU'
    have := hf.hyp.levA_le_cutA hp.le hU'.2
    have := hf.hyp.cutA_lt_mean hp hU'.2
    have := hf.hyp.mean_lt_cutB hp hU'.2
    have := hf.hyp.cutB_le_levB hp.le hU'.2
    simp only [hf.cutA_eq, hf.cutB_eq, hf.levA_eq, hf.levB_eq, hf.mean_eq] at *
    exact ⟨by assumption, by assumption, by assumption, by assumption⟩

theorem sol_c_left (hm : IsSol f m) (SA : StieltjesFunction ℝ) (κ : ℝ)
    (hSA : ∀ U ∈ Ico 0 (f (mean f)), SA U = cutA f (m U) U + κ) :
    (SA.measure.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (f (cutA f (m U) U) - U)) =
      (volume.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U))) := by
  have hm' := (hf.isSol_iff m).1 hm
  have := hf.hyp.peel_c_left hm' SA κ (fun U hU => by
    rw [hf.cutA_eq]; exact hSA U (by rw [hf.fmean_eq] at hU; exact hU))
  simp only [hf.cutA_eq, hf.cutB_eq, hf.mean_eq, hf.f_eq hf.mem01,
    hf.f_eq (cutA_mem01 hf.mem01 _ _)] at this
  exact this

theorem sol_c_right (hm : IsSol f m) (SB : StieltjesFunction ℝ) (κ : ℝ)
    (hSB : ∀ U ∈ Ico 0 (f (mean f)), SB U = -cutB f (m U) U + κ) :
    (SB.measure.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (f (cutB f (m U) U) - U)) =
      (volume.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (wRight (mean f) (cutA f (m U) U) (cutB f (m U) U))) := by
  have hm' := (hf.isSol_iff m).1 hm
  have := hf.hyp.peel_c_right hm' SB κ (fun U hU => by
    rw [hf.cutB_eq]; exact hSB U (by rw [hf.fmean_eq] at hU; exact hU))
  simp only [hf.cutA_eq, hf.cutB_eq, hf.mean_eq, hf.f_eq hf.mem01,
    hf.f_eq (cutB_mem01 hf.mem01 _ _)] at this
  exact this

theorem sol_d (hm : IsSol f m) :
    Tendsto (fun U => ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U))
      (𝓝[<] (f (mean f))) (𝓝 0) := by
  have := hf.hyp.peel_d ((hf.isSol_iff m).1 hm)
  simp only [hf.cutA_eq, hf.cutB_eq, hf.fmean_eq] at this
  refine this.congr (fun U => intervalIntegral.integral_congr (fun t ht => ?_))
  simp only [hf.f_eq (uIcc_subset_Icc (cutA_mem01 hf.mem01 _ _) (cutB_mem01 hf.mem01 _ _) ht)]

end QCDensity

/-! ## Bridge to Theorem 35 and Corollary 39 -/

/-- A function that is continuous and non-decreasing on `[0, c)` and bounded there agrees on
`[0, c)` with a Stieltjes function. -/
lemma exists_stieltjes {g : ℝ → ℝ} {c M : ℝ} (hmono : MonotoneOn g (Ico 0 c))
    (hcont : ContinuousOn g (Ico 0 c)) (hM : ∀ U ∈ Ico 0 c, g U ≤ M) (hc : 0 < c) :
    ∃ S : StieltjesFunction ℝ, EqOn S g (Ico 0 c) := by
  classical
  set G : ℝ → ℝ := fun U => if U < 0 then g 0 else if U < c then g U else M with hG
  have h0 : (0:ℝ) ∈ Ico 0 c := ⟨le_rfl, hc⟩
  have hmG : Monotone G := by
    intro x y hxy
    simp only [hG]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> first
      | exact le_rfl
      | exact hmono h0 ⟨by linarith, by linarith⟩ (by linarith)
      | exact hM 0 h0
      | exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hxy
      | exact hM x ⟨by linarith, by linarith⟩
      | (exfalso; linarith)
  have hrc : ∀ x, ContinuousWithinAt G (Ici x) x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · refine (continuousAt_const (y := g 0)).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hx)] with y hy
        simp only [hG, hy, ↓reduceIte]
      · simp only [hG, hx, ↓reduceIte]
    rcases lt_or_ge x c with hxc | hxc
    · have hx' : x ∈ Ico 0 c := ⟨hx, hxc⟩
      have h1 : ContinuousWithinAt g (Ico x c) x :=
        (hcont x hx').mono (Ico_subset_Ico_left hx)
      have h2 : Ico x c ∈ 𝓝[≥] x := Ico_mem_nhdsGE hxc
      have h3 : ContinuousWithinAt g (Ici x) x := by
        rwa [← continuousWithinAt_inter' h2, inter_eq_right.2 Ico_subset_Ici_self]
      refine h3.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [h2] with y hy
        simp only [hG, (not_lt.2 (hx.trans hy.1)), hy.2, ↓reduceIte]
      · simp only [hG, (not_lt.2 hx), hxc, ↓reduceIte]
    · refine (continuousAt_const (y := M)).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y (hy : x ≤ y)
        simp only [hG, (not_lt.2 (hx.trans hy)), (not_lt.2 (hxc.trans hy)), ↓reduceIte]
      · simp only [hG, (not_lt.2 hx), (not_lt.2 hxc), ↓reduceIte]
  refine ⟨⟨G, hmG, hrc⟩, fun U hU => ?_⟩
  show G U = g U
  simp only [hG, (not_lt.2 hU.1), hU.2, ↓reduceIte]

namespace QCDensity

variable {f : ℝ → ℝ} (hf : QCDensity f) {m : ℝ → ℝ}
include hf

/-- The conclusions of Theorem 34 in the form `Decomp.Peel34` used for Theorem 35, for the
extension `ext01 f` of `f` (equal to `f` on `[0, 1]`). -/
theorem peel34 (hm : IsSol f m) : ∃ SA SB : StieltjesFunction ℝ,
    Decomp.Peel34 (ext01 f) (mean f) (fun U => cutA f (m U) U) (fun U => cutB f (m U) U)
      SA SB := by
  obtain ⟨hA0, hB0, hAB, hAc, hBc, hAm, hBa⟩ := hf.sol_b hm
  have hc : ext01 f (mean f) = f (mean f) := hf.f_eq hf.mem01
  obtain ⟨SA, hSA⟩ := exists_stieltjes hAm hAc (M := mean f)
    (fun U hU => (hAB U hU).2.1.le) hf.f_mean_pos
  obtain ⟨SB, hSB⟩ := exists_stieltjes (g := fun U => -cutB f (m U) U) (M := -mean f)
    (fun x hx y hy hxy => neg_le_neg (hBa hx hy hxy)) hBc.neg
    (fun U hU => neg_le_neg (hAB U hU).2.2.1.le) hf.f_mean_pos
  have eA : ∀ U, ext01 f (cutA f (m U) U) = f (cutA f (m U) U) := fun U =>
    hf.f_eq (cutA_mem01 hf.mem01 _ _)
  have eB : ∀ U, ext01 f (cutB f (m U) U) = f (cutB f (m U) U) := fun U =>
    hf.f_eq (cutB_mem01 hf.mem01 _ _)
  refine ⟨SA, SB, ⟨hf.hyp.cont, by rw [hc]; exact hf.f_mean_pos, hA0, hB0,
    fun U hU => (hAB U (by rwa [hc] at hU)).2.1, fun U hU => (hAB U (by rwa [hc] at hU)).2.2.1,
    by rw [hc]; exact hAc, by rw [hc]; exact hBc, by rw [hc]; exact hSA,
    by rw [hc]; exact hSB, ?_, ?_, ?_, ?_⟩⟩
  · intro U hU t ht
    rw [hc] at hU
    rw [hf.f_eq ⟨(cutA_mem01 hf.mem01 _ _).1.trans ht.1,
      ht.2.trans (cutB_mem01 hf.mem01 _ _).2⟩]
    exact (hf.sol_a hm hU).2.2.2.2.2.1 t ht
  · simp only [hc, eA]
    exact hf.sol_c_left hm SA 0 (fun U hU => by rw [add_zero]; exact hSA hU)
  · simp only [hc, eB]
    exact hf.sol_c_right hm SB 0 (fun U hU => by rw [add_zero]; exact hSB hU)
  · rw [hc]
    refine (hf.sol_d hm).congr (fun U => intervalIntegral.integral_congr (fun t ht => ?_))
    simp only [hf.f_eq (uIcc_subset_Icc (cutA_mem01 hf.mem01 _ _)
      (cutB_mem01 hf.mem01 _ _) ht)]

/-- **Theorem 35** (`c:thm:decomp`) for a strictly quasi-concave density, without hypotheses
on the peeling: `∫_0^{f(μ)} π_U dU = f(x) dx` on `[0, 1]`. -/
theorem decomp (hm : IsSol f m) :
    (volume.restrict (Ioo 0 (f (mean f)))).bind
        (fun U => Decomp.piU (mean f) (cutA f (m U) U) (cutB f (m U) U)) =
      (volume.restrict (Icc 0 1)).withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨SA, SB, h⟩ := hf.peel34 hm
  have := Decomp.decomp h
  rw [hf.f_eq hf.mem01] at this
  rw [this]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [hf.f_eq hx]

/-- Theorem 35 tested against measurable sets, in the form used by Corollary 39. -/
theorem decomp_sets (hm : IsSol f m) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ U in Ico 0 (f (mean f)), ConcaveMix.piU (mean f) (cutA f (m U) U) (cutB f (m U) U) S =
      Bipyramid.densityOn01 f S := by
  obtain ⟨SA, SB, h⟩ := hf.peel34 hm
  have := Decomp.decomp_lintegral h (φ := S.indicator 1) (measurable_one.indicator hS)
  rw [hf.f_eq hf.mem01] at this
  rw [← setLIntegral_congr Ioo_ae_eq_Ico]
  have e1 : ∀ U, ConcaveMix.piU (mean f) (cutA f (m U) U) (cutB f (m U) U) S =
      ∫⁻ x, S.indicator 1 x ∂(Decomp.piU (mean f) (cutA f (m U) U) (cutB f (m U) U)) :=
    fun U => (lintegral_indicator_one hS).symm
  simp only [e1, this]
  rw [Bipyramid.densityOn01, withDensity_apply _ hS, ← lintegral_indicator hS]
  refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  rw [hf.f_eq hx]
  by_cases hxS : x ∈ S <;> simp [hxS]

end QCDensity

/-! ## Main results for a strictly unimodal density -/

section Main

variable {f : ℝ → ℝ} (hf : UnimodalDensity f) {m : ℝ → ℝ}
include hf

/-- **Lemma 33**, continuity: `L` is continuous on `[0, 1] × ℝ` (in particular on
`[0, μ] × [0, f(μ)]`). -/
theorem lemma33_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => Lf f p.1 p.2) (Icc 0 1 ×ˢ univ) :=
  hf.qc.L_continuousOn

/-- **Lemma 33**, `∂ₓ L(x, U) = -(μ - x)(f(x) - U)⁺` on `[0, μ]`. -/
theorem lemma33_deriv_x {x U : ℝ} (hx : x ∈ Icc 0 (mean f)) :
    HasDerivWithinAt (fun x => Lf f x U) (-((mean f - x) * max (f x - U) 0))
      (Icc 0 (mean f)) x :=
  hf.qc.L_hasDerivWithinAt_x hx

/-- **Lemma 33**, `∂_U L(x, U) = -½ (μ - max(x, a(U)))²` for `0 ≤ x ≤ μ`, `U < f(μ)`. -/
theorem lemma33_deriv_U {x U : ℝ} (hx0 : 0 ≤ x) (hxm : x ≤ mean f) (hU : U < f (mean f)) :
    HasDerivAt (fun U => Lf f x U) (-((mean f - max x (levA f U)) ^ 2 / 2)) U :=
  hf.qc.L_hasDerivAt_U hx0 hxm hU

/-- **Lemma 33**, continuous differentiability: `L` is differentiable at every point of
`[0, μ] × (-∞, f(μ))` relative to `[0, 1] × ℝ`, with the partial derivatives above (both of
which are continuous, the second since `a` is continuous). -/
theorem lemma33_differentiable {x₀ U₀ : ℝ} (hx0 : 0 ≤ x₀) (hxm : x₀ ≤ mean f)
    (hU : U₀ < f (mean f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Icc 0 1 ×ˢ univ] (x₀, U₀),
      |Lf f p.1 p.2 - Lf f x₀ U₀ - (-((mean f - x₀) * max (f x₀ - U₀) 0)) * (p.1 - x₀)
        - (-((mean f - max x₀ (levA f U₀)) ^ 2 / 2)) * (p.2 - U₀)|
        ≤ ε * (|p.1 - x₀| + |p.2 - U₀|) :=
  hf.qc.L_local hx0 hxm hU hε

/-- **Lemma 33**, shape: for `U < f(μ)`, `L(·, U) = λ(U)` on `[0, a(U)]`, `L(·, U)` is strictly
decreasing on `[a(U), μ]`, and `L(μ, U) = 0`. -/
theorem lemma33_shape {U : ℝ} (hU : U < f (mean f)) :
    (∀ x ∈ Icc 0 (levA f U), Lf f x U = lam f U) ∧
      StrictAntiOn (fun x => Lf f x U) (Icc (levA f U) (mean f)) ∧ Lf f (mean f) U = 0 :=
  hf.qc.L_shape hU

/-- **Lemma 33** for `R`: `∂_U R(y, U) = -½ (min(y, b(U)) - μ)²` for `μ ≤ y ≤ 1`, `U < f(μ)`. -/
theorem lemma33_R_deriv_U {y U : ℝ} (hy : mean f ≤ y) (hy1 : y ≤ 1) (hU : U < f (mean f)) :
    HasDerivAt (fun U => Rf f y U) (-((min y (levB f U) - mean f) ^ 2 / 2)) U :=
  hf.qc.R_hasDerivAt_U hy hy1 hU

/-- **Lemma 33** for `R`, shape: `R(·, U)` is strictly increasing on `[μ, b(U)]`, equal to
`ρ(U)` on `[b(U), 1]`, and `R(μ, U) = 0`. -/
theorem lemma33_R_shape {U : ℝ} (hU : U < f (mean f)) :
    (∀ y ∈ Icc (levB f U) 1, Rf f y U = rho f U) ∧
      StrictMonoOn (fun y => Rf f y U) (Icc (mean f) (levB f U)) ∧ Rf f (mean f) U = 0 :=
  hf.qc.R_shape hU

/-- **Theorem 34**, existence and uniqueness: the initial value problem `m' = -Φ(m, U)`,
`m(0) = m₀` has a solution on `[0, f(μ))`, and any two solutions agree there. -/
theorem thm34_exists_unique : (∃ m, IsSol f m) ∧
    ∀ m₁ m₂, IsSol f m₁ → IsSol f m₂ → EqOn m₁ m₂ (Ico 0 (f (mean f))) :=
  hf.qc.exists_unique_sol

/-- **Theorem 34**, `m` is continuously differentiable: its derivative `-Φ(m(U), U)` is
continuous on `[0, f(μ))`. -/
theorem thm34_C1 (hm : IsSol f m) :
    ContinuousOn (fun U => Phi f (m U) U) (Ico 0 (f (mean f))) :=
  hf.qc.sol_C1 hm

/-- **Theorem 34(a)**: `0 < m(U) ≤ min(λ(U), ρ(U))`, `L(A(U), U) = R(B(U), U) = m(U)`, `f ≥ U`
on `[A(U), B(U)]`, and `f - U` has mean `μ` there. -/
theorem thm34_a (hm : IsSol f m) {U : ℝ} (hU : U ∈ Ico 0 (f (mean f))) :
    0 < m U ∧ m U ≤ lam f U ∧ m U ≤ rho f U ∧
      Lf f (cutA f (m U) U) U = m U ∧ Rf f (cutB f (m U) U) U = m U ∧
      (∀ t ∈ Icc (cutA f (m U) U) (cutB f (m U) U), U ≤ f t) ∧
      ∫ t in cutA f (m U) U..cutB f (m U) U, (t - mean f) * (f t - U) = 0 :=
  hf.qc.sol_a hm hU

/-- **Theorem 34(b)**: `A(0) = 0`, `B(0) = 1`, `a(U) ≤ A(U) < μ < B(U) ≤ b(U)`, and `A` is
continuous and non-decreasing, `B` continuous and non-increasing on `[0, f(μ))`. -/
theorem thm34_b (hm : IsSol f m) :
    cutA f (m 0) 0 = 0 ∧ cutB f (m 0) 0 = 1 ∧
      (∀ U ∈ Ico 0 (f (mean f)), levA f U ≤ cutA f (m U) U ∧ cutA f (m U) U < mean f ∧
        mean f < cutB f (m U) U ∧ cutB f (m U) U ≤ levB f U) ∧
      ContinuousOn (fun U => cutA f (m U) U) (Ico 0 (f (mean f))) ∧
      ContinuousOn (fun U => cutB f (m U) U) (Ico 0 (f (mean f))) ∧
      MonotoneOn (fun U => cutA f (m U) U) (Ico 0 (f (mean f))) ∧
      AntitoneOn (fun U => cutB f (m U) U) (Ico 0 (f (mean f))) :=
  hf.qc.sol_b hm

/-- **Theorem 34(c)**, left end: `(f(A(U)) - U) dA(U) = (r² - ℓ²)⁺/(2ℓ) dU` as measures on
`(0, f(μ))`, where `dA` is the Stieltjes measure of any Stieltjes function equal to `A` plus a
constant on `[0, f(μ))`. -/
theorem thm34_c_left (hm : IsSol f m) (SA : StieltjesFunction ℝ) (κ : ℝ)
    (hSA : ∀ U ∈ Ico 0 (f (mean f)), SA U = cutA f (m U) U + κ) :
    (SA.measure.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (f (cutA f (m U) U) - U)) =
      (volume.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (wLeft (mean f) (cutA f (m U) U) (cutB f (m U) U))) :=
  hf.qc.sol_c_left hm SA κ hSA

/-- **Theorem 34(c)**, right end: `(f(B(U)) - U) d(-B)(U) = (ℓ² - r²)⁺/(2r) dU` on
`(0, f(μ))`. -/
theorem thm34_c_right (hm : IsSol f m) (SB : StieltjesFunction ℝ) (κ : ℝ)
    (hSB : ∀ U ∈ Ico 0 (f (mean f)), SB U = -cutB f (m U) U + κ) :
    (SB.measure.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (f (cutB f (m U) U) - U)) =
      (volume.restrict (Ioo 0 (f (mean f)))).withDensity
        (fun U => ENNReal.ofReal (wRight (mean f) (cutA f (m U) U) (cutB f (m U) U))) :=
  hf.qc.sol_c_right hm SB κ hSB

/-- **Theorem 34(d)**: `∫_{A(U)}^{B(U)} (f(t) - U) dt → 0` as `U → f(μ)`. -/
theorem thm34_d (hm : IsSol f m) :
    Tendsto (fun U => ∫ t in cutA f (m U) U..cutB f (m U) U, (f t - U))
      (𝓝[<] (f (mean f))) (𝓝 0) :=
  hf.qc.sol_d hm

/-- **Theorem 35** (`c:thm:decomp`), unconditionally: with `A`, `B` from the solution `m` of
Theorem 34, `∫_0^{f(μ)} π_U dU = f(x) dx` on `[0, 1]`. -/
theorem thm35 (hm : IsSol f m) :
    (volume.restrict (Ioo 0 (f (mean f)))).bind
        (fun U => Decomp.piU (mean f) (cutA f (m U) U) (cutB f (m U) U)) =
      (volume.restrict (Icc 0 1)).withDensity (fun x => ENNReal.ofReal (f x)) :=
  hf.qc.decomp hm

end Main

/-- **Corollary 39** (`c:cor:concave`), unconditionally. Let `f` be a probability density on
`[0, 1]` that is concave and continuous on `[0, 1]`, with mean `μ`, and let `A`, `B` be the ends
given by the solution `m` of Theorem 34. Then `β(U) ≤ 3` for `0 ≤ U < f(μ)`, and for every
`n ≥ 3` the construction `mixQ` of Theorem 36 is an `n`-complete mix of `f` with sum `n μ`. -/
theorem cor39 {f : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc 0 1) f) (hfc : ContinuousOn f (Icc 0 1))
    (hf0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0:ℝ)..1, f x = 1) {m : ℝ → ℝ}
    (hm : IsSol f m) :
    (∀ U, 0 ≤ U → U < f (mean f) →
        Bipyramid.beta (mean f) (cutA f (m U) U) (cutB f (m U) U) ≤ 3) ∧
      ∀ n : ℕ, 3 ≤ n →
        IsCompleteMix n (Bipyramid.densityOn01 f)
          (ConcaveMix.mixQ n f (mean f) (fun U => cutA f (m U) U) (fun U => cutB f (m U) U)) ∧
        ∀ᵐ x ∂(ConcaveMix.mixQ n f (mean f) (fun U => cutA f (m U) U)
          (fun U => cutB f (m U) U)), ∑ j, x j = n * mean f := by
  have hf := QCDensity.of_concave hconc hfc hf0 hf1
  obtain ⟨-, -, hAB, hAc, hBc, -, -⟩ := hf.sol_b hm
  refine ConcaveMix.cor39 hconc hfc hf0 hf1 ?_ hAc hBc (hf.decomp_sets hm)
  intro U hU0 hUμ
  have ha := hf.sol_a hm ⟨hU0, hUμ⟩
  exact ⟨(cutA_mem01 hf.mem01 _ _).1, (hAB U ⟨hU0, hUμ⟩).2.1, (hAB U ⟨hU0, hUμ⟩).2.2.1,
    (cutB_mem01 hf.mem01 _ _).2, ha.2.2.2.2.2.1, ha.2.2.2.2.2.2⟩

/-- **Corollary 39**, short form: a probability density on `[0, 1]` that is concave and
continuous on `[0, 1]` is `n`-completely mixable for every `n ≥ 3`. -/
theorem cor39_completelyMixable {f : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc 0 1) f)
    (hfc : ContinuousOn f (Icc 0 1)) (hf0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0:ℝ)..1, f x = 1) (n : ℕ) (hn : 3 ≤ n) :
    CompletelyMixable n (Bipyramid.densityOn01 f) := by
  obtain ⟨m, hm⟩ := (QCDensity.of_concave hconc hfc hf0 hf1).exists_unique_sol.1
  exact ⟨_, ((cor39 hconc hfc hf0 hf1 hm).2 n hn).1⟩

end Mixes.Peel
