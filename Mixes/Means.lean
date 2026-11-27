import Mathlib

/-!
# Means of densities with a concave root (Lemmas 63, 66 and 76)

* `chebyshev_pairwise`, `chebyshev_monotoneOn`: Chebyshev's integral covariance inequality
  (Mathlib only has the finite-sum version), proved through the double integral.
* `brunn_mean` (Lemma 63, `b:lem:brunn`) and its real-exponent form `brunn_mean_rpow`.
* `root_monotoneOn`, `root_concaveOn`, `root_comp_concaveOn`, `root_mean` (Lemma 66,
  `o:lem:root`).
* `weighted_mean` (Lemma 76, `g:lem:mean`) and its equality case `weighted_mean_eq`.

The mean of a density proportional to `f` on `[a, b]` is `meanOn a b f`.
-/

open Set MeasureTheory intervalIntegral

noncomputable section

namespace Mixes

/-- The mean `∫ x f / ∫ f` of the density proportional to `f` on `[a, b]`. -/
def meanOn (a b : ℝ) (f : ℝ → ℝ) : ℝ := (∫ x in a..b, x * f x) / ∫ x in a..b, f x

/-! ## Chebyshev's integral covariance inequality -/

/-- Pairwise form of Chebyshev's covariance inequality: if
`(u x - u y) (A x B y - A y B x) ≥ 0` on `[a, b]²`, then `∫A ∫uB ≤ ∫uA ∫B`. -/
theorem chebyshev_pairwise {a b : ℝ} (hab : a ≤ b) {u A B : ℝ → ℝ}
    (hA : IntervalIntegrable A volume a b) (hB : IntervalIntegrable B volume a b)
    (huA : IntervalIntegrable (fun x => u x * A x) volume a b)
    (huB : IntervalIntegrable (fun x => u x * B x) volume a b)
    (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, 0 ≤ (u x - u y) * (A x * B y - A y * B x)) :
    (∫ x in a..b, A x) * (∫ x in a..b, u x * B x) ≤
      (∫ x in a..b, u x * A x) * (∫ x in a..b, B x) := by
  have key : ∀ x, (∫ y in a..b, (u x - u y) * (A x * B y - A y * B x)) =
      u x * A x * (∫ y in a..b, B y) - u x * B x * (∫ y in a..b, A y)
        - A x * (∫ y in a..b, u y * B y) + B x * (∫ y in a..b, u y * A y) := by
    intro x
    have e : (fun y => (u x - u y) * (A x * B y - A y * B x)) = fun y =>
        (u x * A x) * B y - (u x * B x) * A y - A x * (u y * B y) + B x * (u y * A y) := by
      funext y; ring
    rw [e, integral_add (((hB.const_mul _).sub (hA.const_mul _)).sub (huB.const_mul _))
      (huA.const_mul _), integral_sub ((hB.const_mul _).sub (hA.const_mul _)) (huB.const_mul _),
      integral_sub (hB.const_mul _) (hA.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have h1 : 0 ≤ ∫ x in a..b, (u x * A x * (∫ y in a..b, B y) - u x * B x * (∫ y in a..b, A y)
        - A x * (∫ y in a..b, u y * B y) + B x * (∫ y in a..b, u y * A y)) := by
    refine integral_nonneg hab fun x hx => ?_
    rw [← key x]
    exact integral_nonneg hab fun y hy => h x hx y hy
  rw [integral_add (((huA.mul_const _).sub (huB.mul_const _)).sub (hA.mul_const _))
      (hB.mul_const _), integral_sub ((huA.mul_const _).sub (huB.mul_const _)) (hA.mul_const _),
      integral_sub (huA.mul_const _) (huB.mul_const _), intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const] at h1
  linarith

/-- Chebyshev's covariance inequality for a weight `w ≥ 0` and two non-decreasing functions
`f, h` on `[a, b]`: `∫ w f · ∫ w h ≤ ∫ w · ∫ w f h`. -/
theorem chebyshev_monotoneOn {a b : ℝ} (hab : a ≤ b) {w f h : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, 0 ≤ w x) (hf : MonotoneOn f (Icc a b)) (hh : MonotoneOn h (Icc a b))
    (i1 : IntervalIntegrable w volume a b)
    (i2 : IntervalIntegrable (fun x => w x * f x) volume a b)
    (i3 : IntervalIntegrable (fun x => w x * h x) volume a b)
    (i4 : IntervalIntegrable (fun x => w x * f x * h x) volume a b) :
    (∫ x in a..b, w x * f x) * (∫ x in a..b, w x * h x) ≤
      (∫ x in a..b, w x) * (∫ x in a..b, w x * f x * h x) := by
  have e1 : (fun x => f x * w x) = fun x => w x * f x := funext fun x => by ring
  have e2 : (fun x => f x * (w x * h x)) = fun x => w x * f x * h x := funext fun x => by ring
  have := chebyshev_pairwise hab (u := f) (A := fun x => w x * h x) (B := w) i3 i1
    (by rw [e2]; exact i4) (by rw [e1]; exact i2) (by
      intro x hx y hy
      have hfh : 0 ≤ (f x - f y) * (h x - h y) := by
        rcases le_total x y with hxy | hxy
        · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hf hx hy hxy))
            (sub_nonpos.2 (hh hx hy hxy))
        · exact mul_nonneg (sub_nonneg.2 (hf hy hx hxy)) (sub_nonneg.2 (hh hy hx hxy))
      have e : (f x - f y) * (w x * h x * w y - w y * h y * w x) =
          w x * w y * ((f x - f y) * (h x - h y)) := by ring
      rw [e]; exact mul_nonneg (mul_nonneg (hw x hx) (hw y hy)) hfh)
  simp only [e1, e2] at this
  linarith

/-- A sign condition for `chebyshev_pairwise` with `u = id`, from the case `y ≤ x`. -/
private lemma pair_nonneg {S : Set ℝ} {F H : ℝ → ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, y ≤ x → F y * H x ≤ F x * H y) :
    ∀ x ∈ S, ∀ y ∈ S, 0 ≤ (x - y) * (F x * H y - F y * H x) := by
  intro x hx y hy
  rcases le_total y x with hyx | hxy
  · exact mul_nonneg (sub_nonneg.2 hyx) (sub_nonneg.2 (h x hx y hy hyx))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hxy) (sub_nonpos.2 (h y hy x hx hxy))

/-! ## Concave functions on `[0, 1]` -/

section Concave

variable {g : ℝ → ℝ}

private lemma concave_bound (hg : ConcaveOn ℝ (Icc 0 1) g) (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : g x ≤ 2 * g (1 / 2) := by
  have hx' : 1 - x ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have := hg.2 hx hx' (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  have e : 1 / 2 * x + 1 / 2 * (1 - x) = (1 / 2 : ℝ) := by ring
  rw [e] at this
  linarith [h0 _ hx']

/-- `g(s)/s` is non-increasing, in multiplied form. -/
lemma concave_ratio_left (hg : ConcaveOn ℝ (Icc 0 1) g) (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) (hyx : y ≤ x) :
    y * g x ≤ x * g y := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · have : y = 0 := le_antisymm (h ▸ hyx) hy.1
    subst this; rw [← h]
  · have h0m : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hθ : y / x ≤ 1 := (div_le_one h).2 hyx
    have := hg.2 hx h0m (div_nonneg hy.1 h.le) (sub_nonneg.2 hθ) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero] at this
    rw [div_mul_cancel₀ y h.ne'] at this
    have h1 : 0 ≤ (1 - y / x) * g 0 := mul_nonneg (sub_nonneg.2 hθ) (h0 0 h0m)
    have h2 : y / x * g x ≤ g y := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ h] at h2
    linarith

/-- `g(s)/(1 - s)` is non-decreasing, in multiplied form. -/
lemma concave_ratio_right (hg : ConcaveOn ℝ (Icc 0 1) g) (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) (hyx : y ≤ x) :
    (1 - x) * g y ≤ (1 - y) * g x := by
  rcases eq_or_lt_of_le hy.2 with h | h
  · have : x = 1 := le_antisymm hx.2 (h ▸ hyx)
    subst this; rw [h]
  · have h1m : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hpos : 0 < 1 - y := by linarith
    have hθ : (1 - x) / (1 - y) ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hθ0 : 0 ≤ (1 - x) / (1 - y) := div_nonneg (by linarith [hx.2]) hpos.le
    have := hg.2 hy h1m hθ0 (sub_nonneg.2 hθ) (by ring)
    simp only [smul_eq_mul, mul_one] at this
    have e : (1 - x) / (1 - y) * y + (1 - (1 - x) / (1 - y)) = x := by
      field_simp; ring
    rw [e] at this
    have h1 : 0 ≤ (1 - (1 - x) / (1 - y)) * g 1 := mul_nonneg (sub_nonneg.2 hθ) (h0 1 h1m)
    have h2 : (1 - x) / (1 - y) * g y ≤ g x := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at h2
    linarith

/-- A concave `g ≥ 0` on `[0, 1]` that does not vanish identically is positive on `(0, 1)`. -/
lemma concave_pos (hg : ConcaveOn ℝ (Icc 0 1) g) (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (hne : ∃ x ∈ Icc (0:ℝ) 1, g x ≠ 0) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : 0 < g x := by
  obtain ⟨x0, hx0, hgx0⟩ := hne
  have hpos0 : 0 < g x0 := lt_of_le_of_ne (h0 x0 hx0) (Ne.symm hgx0)
  have hxI : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
  rcases le_total x x0 with hxx | hxx
  · have hx0p : 0 < x0 := lt_of_lt_of_le hx.1 hxx
    have := concave_ratio_left hg h0 hx0 hxI hxx
    have : 0 < x0 * g x := lt_of_lt_of_le (mul_pos hx.1 hpos0) this
    exact pos_of_mul_pos_right this hx0p.le
  · have hx01 : x0 < 1 := lt_of_le_of_lt hxx hx.2
    have := concave_ratio_right hg h0 hxI hx0 hxx
    have : 0 < (1 - x0) * g x :=
      lt_of_lt_of_le (mul_pos (by linarith [hx.2]) hpos0) this
    exact pos_of_mul_pos_right this (by linarith)

/-- `g ^ γ` is interval integrable on `[0, 1]` for a concave `g ≥ 0` and `γ ≥ 0`. -/
lemma concave_rpow_intervalIntegrable {γ : ℝ} (hγ : 0 ≤ γ) (hg : ConcaveOn ℝ (Icc 0 1) g)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) :
    IntervalIntegrable (fun s => g s ^ γ) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  have hc : ContinuousOn g (Ioo 0 1) := by
    have := hg.continuousOn_interior
    rwa [interior_Icc] at this
  have hc' : ContinuousOn (fun s => g s ^ γ) (Ioo 0 1) :=
    (Real.continuous_rpow_const hγ).comp_continuousOn hc
  refine ⟨hc'.aestronglyMeasurable measurableSet_Ioo,
    HasFiniteIntegral.restrict_of_bounded (C := (2 * g (1 / 2)) ^ γ) measure_Ioo_lt_top ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hxI : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h0 x hxI) _)]
  exact Real.rpow_le_rpow (h0 x hxI) (concave_bound hg h0 hxI) hγ

end Concave

/-! ## Elementary integrals on `[0, 1]` -/

section Integrals

variable {γ : ℝ}

private lemma cont_rpow (hγ : 0 ≤ γ) : Continuous fun s : ℝ => s ^ γ :=
  Real.continuous_rpow_const hγ

private lemma cont_one_sub_rpow (hγ : 0 ≤ γ) (c : ℝ) : Continuous fun s : ℝ => (1 - c * s) ^ γ :=
  (continuous_const.sub (continuous_const.mul continuous_id)).rpow_const fun _ => Or.inr hγ

private lemma integral_rpow01 (hγ : 0 ≤ γ) : ∫ s in (0:ℝ)..1, s ^ γ = 1 / (γ + 1) := by
  rw [integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow (by linarith : γ + 1 ≠ 0)]

private lemma integral_mul_rpow01 (hγ : 0 ≤ γ) : ∫ s in (0:ℝ)..1, s * s ^ γ = 1 / (γ + 2) := by
  have : ∫ s in (0:ℝ)..1, s * s ^ γ = ∫ s in (0:ℝ)..1, s ^ (γ + 1) := by
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    simp only [Real.rpow_add_one' hs.1 (by linarith : γ + 1 ≠ 0)]; ring
  rw [this, integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow (by linarith : γ + 1 + 1 ≠ 0)]; ring

private lemma integral_one_sub_rpow01 (hγ : 0 ≤ γ) :
    ∫ s in (0:ℝ)..1, (1 - s) ^ γ = 1 / (γ + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ γ) 1]
  simpa using integral_rpow01 hγ

private lemma integral_mul_one_sub_rpow01 (hγ : 0 ≤ γ) :
    ∫ s in (0:ℝ)..1, s * (1 - s) ^ γ = 1 / ((γ + 1) * (γ + 2)) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x => (1 - x) * x ^ γ) (1:ℝ)
    (a := 0) (b := 1)
  simp only [sub_sub_cancel, sub_zero, sub_self] at h
  rw [h]
  have e : ∫ x in (0:ℝ)..1, (1 - x) * x ^ γ =
      (∫ x in (0:ℝ)..1, x ^ γ) - ∫ x in (0:ℝ)..1, x * x ^ γ := by
    have i1 : IntervalIntegrable (fun x : ℝ => x ^ γ) volume 0 1 :=
      (cont_rpow hγ).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x : ℝ => x * x ^ γ) volume 0 1 :=
      (continuous_id.mul (cont_rpow hγ)).intervalIntegrable _ _
    rw [← integral_sub i1 i2]
    congr 1; funext x; ring
  rw [e, integral_rpow01 hγ, integral_mul_rpow01 hγ]
  have : γ + 1 ≠ 0 := by linarith
  have : γ + 2 ≠ 0 := by linarith
  field_simp; ring

end Integrals

/-! ## Lemma 63 -/

section Brunn

variable {g : ℝ → ℝ}

/-- Lemma 63 in multiplied form, for a real exponent `γ ≥ 0`:
`∫ g^γ / (γ+2) ≤ ∫ s g^γ ≤ (γ+1)/(γ+2) ∫ g^γ` for concave `g ≥ 0` on `[0, 1]`. -/
theorem brunn_mean_core {γ : ℝ} (hγ : 0 ≤ γ) (hg : ConcaveOn ℝ (Icc 0 1) g)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) :
    1 / (γ + 2) * (∫ s in (0:ℝ)..1, g s ^ γ) ≤ ∫ s in (0:ℝ)..1, s * g s ^ γ ∧
      ∫ s in (0:ℝ)..1, s * g s ^ γ ≤ (γ + 1) / (γ + 2) * ∫ s in (0:ℝ)..1, g s ^ γ := by
  have hG := concave_rpow_intervalIntegrable hγ hg h0
  have hsG : IntervalIntegrable (fun s => s * g s ^ γ) volume 0 1 :=
    hG.continuousOn_mul continuousOn_id
  have c1 : Continuous fun s : ℝ => (1 - s) ^ γ := by simpa using cont_one_sub_rpow hγ 1
  have hγ1 : 0 < γ + 1 := by linarith
  have hγ2 : 0 < γ + 2 := by linarith
  constructor
  · have := chebyshev_pairwise zero_le_one (u := fun s => s) (A := fun s => g s ^ γ)
      (B := fun s => (1 - s) ^ γ) hG (c1.intervalIntegrable _ _) hsG
      ((continuous_id.mul c1).intervalIntegrable _ _)
      (pair_nonneg (S := Icc 0 1) fun x hx y hy hyx => by
        rw [← Real.mul_rpow (h0 y hy) (by linarith [hx.2]),
          ← Real.mul_rpow (h0 x hx) (by linarith [hy.2])]
        refine Real.rpow_le_rpow (mul_nonneg (h0 y hy) (by linarith [hx.2])) ?_ hγ
        have := concave_ratio_right hg h0 hx hy hyx
        linarith)
    rw [integral_mul_one_sub_rpow01 hγ, integral_one_sub_rpow01 hγ] at this
    have e : 1 / (γ + 2) * (∫ s in (0:ℝ)..1, g s ^ γ) =
        (γ + 1) * ((∫ s in (0:ℝ)..1, g s ^ γ) * (1 / ((γ + 1) * (γ + 2)))) := by
      field_simp
    rw [e]
    have e2 : ∫ s in (0:ℝ)..1, s * g s ^ γ =
        (γ + 1) * ((∫ s in (0:ℝ)..1, s * g s ^ γ) * (1 / (γ + 1))) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left this hγ1.le
  · have := chebyshev_pairwise zero_le_one (u := fun s => s) (A := fun s => s ^ γ)
      (B := fun s => g s ^ γ) ((cont_rpow hγ).intervalIntegrable _ _) hG
      ((continuous_id.mul (cont_rpow hγ)).intervalIntegrable _ _) hsG
      (pair_nonneg (S := Icc 0 1) fun x hx y hy hyx => by
        rw [← Real.mul_rpow hy.1 (h0 x hx), ← Real.mul_rpow hx.1 (h0 y hy)]
        exact Real.rpow_le_rpow (mul_nonneg hy.1 (h0 x hx))
          (concave_ratio_left hg h0 hx hy hyx) hγ)
    rw [integral_rpow01 hγ, integral_mul_rpow01 hγ] at this
    have e : (γ + 1) / (γ + 2) * (∫ s in (0:ℝ)..1, g s ^ γ) =
        (γ + 1) * (1 / (γ + 2) * (∫ s in (0:ℝ)..1, g s ^ γ)) := by
      field_simp
    rw [e]
    have e2 : ∫ s in (0:ℝ)..1, s * g s ^ γ =
        (γ + 1) * (1 / (γ + 1) * (∫ s in (0:ℝ)..1, s * g s ^ γ)) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left this hγ1.le

lemma concave_rpow_integral_pos {γ : ℝ} (hγ : 0 ≤ γ) (hg : ConcaveOn ℝ (Icc 0 1) g)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (hne : ∃ x ∈ Icc (0:ℝ) 1, g x ≠ 0) :
    0 < ∫ s in (0:ℝ)..1, g s ^ γ :=
  intervalIntegral_pos_of_pos_on (concave_rpow_intervalIntegrable hγ hg h0)
    (fun _ hx => Real.rpow_pos_of_pos (concave_pos hg h0 hne hx) γ) zero_lt_one

/-- Lemma 63 for a real exponent `γ ≥ 0` (the form used in Lemma 66, there with `γ > 0`): the
density proportional to `g ^ γ` on `[0, 1]`, `g ≥ 0` concave and not identically zero, has its
mean in `[1/(γ+2), (γ+1)/(γ+2)]`. -/
theorem brunn_mean_rpow {γ : ℝ} (hγ : 0 ≤ γ) (hg : ConcaveOn ℝ (Icc 0 1) g)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (hne : ∃ x ∈ Icc (0:ℝ) 1, g x ≠ 0) :
    meanOn 0 1 (fun s => g s ^ γ) ∈ Icc (1 / (γ + 2)) ((γ + 1) / (γ + 2)) := by
  have hpos := concave_rpow_integral_pos hγ hg h0 hne
  obtain ⟨h1, h2⟩ := brunn_mean_core hγ hg h0
  unfold meanOn
  exact ⟨(le_div_iff₀ hpos).2 h1, (div_le_iff₀ hpos).2 h2⟩

/-- **Lemma 63** (`b:lem:brunn`). Let `d ≥ 2` and let `g ≥ 0` be concave on `[0, 1]` and not
identically zero. Then the density proportional to `g ^ (d - 1)` on `[0, 1]` has its mean in
`[1/(d+1), d/(d+1)]`. -/
theorem brunn_mean {d : ℕ} (hd : 2 ≤ d) (hg : ConcaveOn ℝ (Icc 0 1) g)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (hne : ∃ x ∈ Icc (0:ℝ) 1, g x ≠ 0) :
    meanOn 0 1 (fun s => g s ^ (d - 1)) ∈ Icc (1 / (d + 1 : ℝ)) (d / (d + 1)) := by
  have := brunn_mean_rpow (Nat.cast_nonneg (d - 1)) hg h0 hne
  simp only [Real.rpow_natCast] at this
  have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc] at this
  convert this using 3 <;> ring

end Brunn

/-! ## Lemma 66 -/

section Root

variable {p U : ℝ}

private lemma root_mem {t : ℝ} (hp : 1 ≤ p) (hU : 0 ≤ U) (ht : t ∈ Ici (U ^ (1 / p))) :
    0 ≤ t ∧ U ≤ t ^ p := by
  have hc : 0 ≤ U ^ (1 / p) := Real.rpow_nonneg hU _
  refine ⟨le_trans hc ht, ?_⟩
  have := Real.rpow_le_rpow hc ht (by linarith : (0:ℝ) ≤ p)
  rwa [← Real.rpow_mul hU, one_div_mul_cancel (by linarith : p ≠ 0), Real.rpow_one] at this

lemma root_hasDerivAt {t : ℝ} (hp : 1 ≤ p) (hU : 0 ≤ U) (ht : U ^ (1 / p) < t) :
    HasDerivAt (fun t => (t ^ p - U) ^ (1 / p)) ((t ^ p / (t ^ p - U)) ^ ((p - 1) / p)) t := by
  have hp0 : 0 < p := by linarith
  have hc : 0 ≤ U ^ (1 / p) := Real.rpow_nonneg hU _
  have ht0 : 0 < t := lt_of_le_of_lt hc ht
  have hUt : U < t ^ p := by
    have := Real.rpow_lt_rpow hc ht hp0
    rwa [← Real.rpow_mul hU, one_div_mul_cancel hp0.ne', Real.rpow_one] at this
  have hv : 0 < t ^ p - U := sub_pos.2 hUt
  have h1 := ((Real.hasDerivAt_rpow_const (p := p) (Or.inl ht0.ne')).sub_const U).rpow_const
    (p := 1 / p) (Or.inl hv.ne')
  convert h1 using 1
  rw [Real.div_rpow (Real.rpow_nonneg ht0.le _) hv.le, ← Real.rpow_mul ht0.le]
  have e1 : p * ((p - 1) / p) = p - 1 := by field_simp
  have e2 : (1 / p - 1) = -((p - 1) / p) := by field_simp; ring
  rw [e1, e2, Real.rpow_neg hv.le]
  field_simp

/-- **Lemma 66** (`o:lem:root`), monotonicity: `φ_U(t) = (t^p - U)^(1/p)` is non-decreasing on
`[U^(1/p), ∞)` for `p ≥ 1`, `U ≥ 0`. -/
theorem root_monotoneOn (hp : 1 ≤ p) (hU : 0 ≤ U) :
    MonotoneOn (fun t => (t ^ p - U) ^ (1 / p)) (Ici (U ^ (1 / p))) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hxU⟩ := root_mem hp hU hx
  exact Real.rpow_le_rpow (sub_nonneg.2 hxU)
    (sub_le_sub_right (Real.rpow_le_rpow hx0 hxy (by linarith)) U) (by positivity)

/-- **Lemma 66** (`o:lem:root`), concavity: `φ_U(t) = (t^p - U)^(1/p)` is concave on
`[U^(1/p), ∞)` for `p ≥ 1`, `U ≥ 0`. -/
theorem root_concaveOn (hp : 1 ≤ p) (hU : 0 ≤ U) :
    ConcaveOn ℝ (Ici (U ^ (1 / p))) (fun t => (t ^ p - U) ^ (1 / p)) := by
  have hp0 : 0 < p := by linarith
  have hcont : Continuous fun t : ℝ => (t ^ p - U) ^ (1 / p) :=
    ((Real.continuous_rpow_const hp0.le).sub continuous_const).rpow_const
      fun _ => Or.inr (by positivity)
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici _) hcont.continuousOn ?_ ?_
  · rw [interior_Ici]
    exact fun t ht => (root_hasDerivAt hp hU ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(root_hasDerivAt hp hU hx).deriv, (root_hasDerivAt hp hU hy).deriv]
    have hc : 0 ≤ U ^ (1 / p) := Real.rpow_nonneg hU _
    have hUx : U < x ^ p := by
      have := Real.rpow_lt_rpow hc hx hp0
      rwa [← Real.rpow_mul hU, one_div_mul_cancel hp0.ne', Real.rpow_one] at this
    have hx0 : 0 < x := lt_of_le_of_lt hc hx
    have hxy' : x ^ p ≤ y ^ p := Real.rpow_le_rpow hx0.le hxy hp0.le
    have hUy : U < y ^ p := lt_of_lt_of_le hUx hxy'
    refine Real.rpow_le_rpow (div_nonneg (by linarith) (by linarith)) ?_
      (div_nonneg (by linarith) hp0.le)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- **Lemma 66** (`o:lem:root`), composition: if `g ≥ 0` is concave on a convex set `J` and
`g ^ p ≥ U` on `J`, then `(g ^ p - U) ^ (1/p)` is concave on `J`. -/
theorem root_comp_concaveOn (hp : 1 ≤ p) (hU : 0 ≤ U) {J : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ J g) (h0 : ∀ x ∈ J, 0 ≤ g x) (hgU : ∀ x ∈ J, U ≤ g x ^ p) :
    ConcaveOn ℝ J (fun x => (g x ^ p - U) ^ (1 / p)) := by
  have hp0 : 0 < p := by linarith
  have mem : ∀ x ∈ J, g x ∈ Ici (U ^ (1 / p)) := fun x hx => by
    have := Real.rpow_le_rpow hU (hgU x hx) (by positivity : (0:ℝ) ≤ 1 / p)
    rw [one_div, Real.rpow_rpow_inv (h0 x hx) hp0.ne', ← one_div] at this
    exact this
  refine ⟨hg.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hφ := (root_concaveOn hp hU).2 (mem x hx) (mem y hy) ha hb hab
  have hcomb : a • g x + b • g y ∈ Ici (U ^ (1 / p)) :=
    (convex_Ici _) (mem x hx) (mem y hy) ha hb hab
  have hmono := root_monotoneOn hp hU hcomb (mem _ (hg.1 hx hy ha hb hab)) (hg.2 hx hy ha hb hab)
  exact le_trans hφ hmono

/-- **Lemma 66** (`o:lem:root`), last part: for a real `γ ≥ 0` (the paper: `γ > 0`) and a concave
`h ≥ 0` on `[a, b]`, `a < b`, not identically zero, the density proportional to `h ^ γ` on
`[a, b]` has its mean in `[a + (b-a)/(γ+2), b - (b-a)/(γ+2)]`. -/
theorem root_mean {γ a b : ℝ} (hγ : 0 ≤ γ) (hab : a < b) {h : ℝ → ℝ}
    (hh : ConcaveOn ℝ (Icc a b) h) (h0 : ∀ x ∈ Icc a b, 0 ≤ h x)
    (hne : ∃ x ∈ Icc a b, h x ≠ 0) :
    meanOn a b (fun x => h x ^ γ) ∈
      Icc (a + (b - a) / (γ + 2)) (b - (b - a) / (γ + 2)) := by
  have hL : 0 < b - a := sub_pos.2 hab
  set g : ℝ → ℝ := fun s => h ((b - a) * s + a) with hgdef
  have memI : ∀ s ∈ Icc (0:ℝ) 1, (b - a) * s + a ∈ Icc a b := fun s hs =>
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hg : ConcaveOn ℝ (Icc 0 1) g := by
    refine ⟨convex_Icc 0 1, fun x hx y hy p q hp hq hpq => ?_⟩
    have := hh.2 (memI x hx) (memI y hy) hp hq hpq
    simp only [smul_eq_mul] at this ⊢
    have e : p * ((b - a) * x + a) + q * ((b - a) * y + a) = (b - a) * (p * x + q * y) + a := by
      linear_combination a * hpq
    rw [e] at this
    exact this
  have hg0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ g s := fun s hs => h0 _ (memI s hs)
  have hgne : ∃ s ∈ Icc (0:ℝ) 1, g s ≠ 0 := by
    obtain ⟨x0, hx0, hhx0⟩ := hne
    refine ⟨(x0 - a) / (b - a), ⟨div_nonneg (by linarith [hx0.1]) hL.le,
      (div_le_one hL).2 (by linarith [hx0.2])⟩, ?_⟩
    simp only [hgdef]
    rwa [mul_div_cancel₀ _ hL.ne', sub_add_cancel]
  obtain ⟨hm1, hm2⟩ := brunn_mean_rpow hγ hg hg0 hgne
  unfold meanOn at hm1 hm2 ⊢
  have hG := concave_rpow_intervalIntegrable hγ hg hg0
  have hpos := concave_rpow_integral_pos hγ hg hg0 hgne
  -- change of variables `x = (b - a) s + a`
  have c0 := intervalIntegral.integral_comp_mul_add (fun x => h x ^ γ) hL.ne' a
    (a := 0) (b := 1)
  have c1 := intervalIntegral.integral_comp_mul_add (fun x => x * h x ^ γ) hL.ne' a
    (a := 0) (b := 1)
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at c0 c1
  have I0 : ∫ x in a..b, h x ^ γ = (b - a) * ∫ s in (0:ℝ)..1, g s ^ γ := by
    rw [c0]; field_simp
  have I1 : ∫ x in a..b, x * h x ^ γ =
      (b - a) * ((b - a) * (∫ s in (0:ℝ)..1, s * g s ^ γ) + a * ∫ s in (0:ℝ)..1, g s ^ γ) := by
    have e : ∫ s in (0:ℝ)..1, ((b - a) * s + a) * h ((b - a) * s + a) ^ γ =
        (b - a) * (∫ s in (0:ℝ)..1, s * g s ^ γ) + a * ∫ s in (0:ℝ)..1, g s ^ γ := by
      have hsG : IntervalIntegrable (fun s => s * g s ^ γ) volume 0 1 :=
        hG.continuousOn_mul continuousOn_id
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← integral_add (hsG.const_mul _) (hG.const_mul _)]
      congr 1; funext s; simp only [hgdef]; ring
    rw [← e, c1]; field_simp
  rw [I0, I1]
  set G0 := ∫ s in (0:ℝ)..1, g s ^ γ
  set G1 := ∫ s in (0:ℝ)..1, s * g s ^ γ
  have hγ2 : 0 < γ + 2 := by linarith
  have e : (b - a) * ((b - a) * G1 + a * G0) / ((b - a) * G0) = a + (b - a) * (G1 / G0) := by
    field_simp; ring
  rw [e]
  constructor
  · have := mul_le_mul_of_nonneg_left hm1 hL.le
    have e' : (b - a) / (γ + 2) = (b - a) * (1 / (γ + 2)) := by ring
    linarith
  · have := mul_le_mul_of_nonneg_left hm2 hL.le
    have e' : b - (b - a) / (γ + 2) = a + (b - a) * ((γ + 1) / (γ + 2)) := by
      field_simp; ring
    linarith

end Root

/-! ## Lemma 76 -/

section WeightedMean

variable {k γ : ℝ}

private lemma cont_beta (hk : 0 ≤ k) (hγ : 0 ≤ γ) : Continuous fun u : ℝ => (1 - u) ^ k * u ^ γ :=
  ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hk).mul (cont_rpow hγ)

/-- The mean of a Beta distribution, by integration by parts:
`(k+γ+2) ∫₀¹ (1-u) (1-u)^k u^γ = (k+1) ∫₀¹ (1-u)^k u^γ`. -/
lemma beta_mean (hk : 0 ≤ k) (hγ : 0 ≤ γ) :
    (k + γ + 2) * ∫ u in (0:ℝ)..1, (1 - u) * ((1 - u) ^ k * u ^ γ) =
      (k + 1) * ∫ u in (0:ℝ)..1, (1 - u) ^ k * u ^ γ := by
  have cb := cont_beta hk hγ
  have i0 : IntervalIntegrable (fun u : ℝ => (1 - u) ^ k * u ^ γ) volume 0 1 :=
    cb.intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun u : ℝ => (1 - u) * ((1 - u) ^ k * u ^ γ)) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul cb).intervalIntegrable _ _
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun u : ℝ => (1 - u) ^ (k + 1) * u ^ (γ + 1))
      ((k + γ + 2) * ((1 - x) * ((1 - x) ^ k * x ^ γ)) - (k + 1) * ((1 - x) ^ k * x ^ γ)) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h1 := ((hasDerivAt_id' x).const_sub 1).rpow_const (p := k + 1) (Or.inr (by linarith))
    have h2 := Real.hasDerivAt_rpow_const (x := x) (p := γ + 1) (Or.inr (by linarith))
    convert h1.mul h2 using 1
    simp only [add_sub_cancel_right]
    rw [Real.rpow_add_one' (by linarith [hx.2] : (0:ℝ) ≤ 1 - x) (by linarith),
      Real.rpow_add_one' hx.1 (by linarith)]
    ring
  have := integral_eq_sub_of_hasDerivAt hd ((i1.const_mul _).sub (i0.const_mul _))
  rw [integral_sub (i1.const_mul _) (i0.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at this
  simp only [sub_self, sub_zero, Real.zero_rpow (by linarith : k + 1 ≠ 0),
    Real.zero_rpow (by linarith : γ + 1 ≠ 0), zero_mul, mul_zero, Real.one_rpow] at this
  linarith

/-- Truncation raises the mean of `1 - V`: if `ρ ≥ 0` is continuous on `[0, 1]`, positive on
`(0, 1)`, and `∫₀¹ (1-u) ρ = r ∫₀¹ ρ`, then `r ∫₀ᶜ ρ ≤ ∫₀ᶜ (1-u) ρ` for `0 ≤ c ≤ 1`. -/
lemma trunc_mean {ρ : ℝ → ℝ} {r c : ℝ} (cb : Continuous ρ) (ρ0 : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ ρ u)
    (ρpos : ∀ u ∈ Ioo (0:ℝ) 1, 0 < ρ u)
    (hr : ∫ u in (0:ℝ)..1, (1 - u) * ρ u = r * ∫ u in (0:ℝ)..1, ρ u)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    r * ∫ u in (0:ℝ)..c, ρ u ≤ ∫ u in (0:ℝ)..c, (1 - u) * ρ u := by
  have cb1 : Continuous fun u => (1 - u) * ρ u := (continuous_const.sub continuous_id).mul cb
  have hsum : (∫ u in (0:ℝ)..c, ρ u) + (∫ u in c..1, ρ u) = ∫ u in (0:ℝ)..1, ρ u :=
    integral_add_adjacent_intervals (cb.intervalIntegrable _ _) (cb.intervalIntegrable _ _)
  have hsum1 : (∫ u in (0:ℝ)..c, (1 - u) * ρ u) + (∫ u in c..1, (1 - u) * ρ u) =
      ∫ u in (0:ℝ)..1, (1 - u) * ρ u :=
    integral_add_adjacent_intervals (cb1.intervalIntegrable _ _) (cb1.intervalIntegrable _ _)
  have hpos : 0 < ∫ u in (0:ℝ)..1, ρ u :=
    intervalIntegral_pos_of_pos_on (cb.intervalIntegrable _ _) ρpos zero_lt_one
  have hP : 0 ≤ ∫ u in (0:ℝ)..c, ρ u :=
    integral_nonneg hc0 fun u hu => ρ0 u ⟨hu.1, hu.2.trans hc1⟩
  have hQ : 0 ≤ ∫ u in c..1, ρ u := integral_nonneg hc1 fun u hu => ρ0 u ⟨hc0.trans hu.1, hu.2⟩
  have hP1 : (1 - c) * (∫ u in (0:ℝ)..c, ρ u) ≤ ∫ u in (0:ℝ)..c, (1 - u) * ρ u := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on hc0 ((cb.intervalIntegrable _ _).const_mul _)
      (cb1.intervalIntegrable _ _)
      fun u hu => mul_le_mul_of_nonneg_right (by linarith [hu.2]) (ρ0 u ⟨hu.1, hu.2.trans hc1⟩)
  have hQ1 : (∫ u in c..1, (1 - u) * ρ u) ≤ (1 - c) * ∫ u in c..1, ρ u := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on hc1 (cb1.intervalIntegrable _ _)
      ((cb.intervalIntegrable _ _).const_mul _)
      fun u hu => mul_le_mul_of_nonneg_right (by linarith [hu.1]) (ρ0 u ⟨hc0.trans hu.1, hu.2⟩)
  set P := ∫ u in (0:ℝ)..c, ρ u
  set Q := ∫ u in c..1, ρ u
  set P1 := ∫ u in (0:ℝ)..c, (1 - u) * ρ u
  set Q1 := ∫ u in c..1, (1 - u) * ρ u
  rw [← hsum, ← hsum1] at hr
  rw [← hsum] at hpos
  have h1 : P * Q1 ≤ P1 * Q := by
    have a1 := mul_le_mul_of_nonneg_left hQ1 hP
    have a2 := mul_le_mul_of_nonneg_right hP1 hQ
    nlinarith
  have h2 : r * P * (P + Q) ≤ P1 * (P + Q) := by
    have : r * P * (P + Q) = P * (P1 + Q1) := by rw [hr]; ring
    rw [this]; nlinarith
  exact le_of_mul_le_mul_right h2 hpos

variable {g : ℝ → ℝ} {c : ℝ}

/-- Lemma 76 in multiplied form: `(k+1)/(k+γ+2) ∫ w^k g^γ ≤ ∫ w · w^k g^γ`, `w(s) = 1 - c s`. -/
theorem weighted_mean_core (hk : 0 ≤ k) (hγ : 0 ≤ γ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hg : ConcaveOn ℝ (Icc 0 1) g) (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) :
    (k + 1) / (k + γ + 2) * (∫ s in (0:ℝ)..1, (1 - c * s) ^ k * g s ^ γ) ≤
      ∫ s in (0:ℝ)..1, (1 - c * s) * ((1 - c * s) ^ k * g s ^ γ) := by
  set r := (k + 1) / (k + γ + 2) with hr
  have hkγ : 0 < k + γ + 2 := by linarith
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hkγ]; linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hkγ.le
  have cw := cont_one_sub_rpow hk c
  have cw1 : Continuous fun s : ℝ => 1 - c * s := continuous_const.sub (continuous_const.mul
    continuous_id)
  have hG := concave_rpow_intervalIntegrable hγ hg h0
  have w0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ 1 - c * s := fun s hs => by nlinarith [hs.1, hs.2]
  have wpos : ∀ s ∈ Ioo (0:ℝ) 1, 0 < 1 - c * s := fun s hs => by nlinarith [hs.1, hs.2]
  -- integrability
  have iA : IntervalIntegrable (fun s => (1 - c * s) ^ k * g s ^ γ) volume 0 1 :=
    hG.continuousOn_mul cw.continuousOn
  have isA : IntervalIntegrable (fun s => s * ((1 - c * s) ^ k * g s ^ γ)) volume 0 1 := by
    have := hG.continuousOn_mul (continuous_id.mul cw).continuousOn
    convert this using 1; funext s; simp only [Pi.mul_apply, id]; ring
  have cB : Continuous fun s : ℝ => (1 - c * s) ^ k * s ^ γ := cw.mul (cont_rpow hγ)
  have iB : IntervalIntegrable (fun s : ℝ => (1 - c * s) ^ k * s ^ γ) volume 0 1 :=
    cB.intervalIntegrable _ _
  have isB : IntervalIntegrable (fun s : ℝ => s * ((1 - c * s) ^ k * s ^ γ)) volume 0 1 :=
    (continuous_id.mul cB).intervalIntegrable _ _
  -- Step 1: Chebyshev with the non-increasing `(g(s)/s)^γ`
  have step1 := chebyshev_pairwise zero_le_one (u := fun s => s)
    (A := fun s => (1 - c * s) ^ k * s ^ γ) (B := fun s => (1 - c * s) ^ k * g s ^ γ)
    iB iA isB isA (pair_nonneg (S := Icc 0 1) fun x hx y hy hyx => by
      have hρx := Real.rpow_nonneg (w0 x hx) k
      have hρy := Real.rpow_nonneg (w0 y hy) k
      have key : y ^ γ * g x ^ γ ≤ x ^ γ * g y ^ γ := by
        rw [← Real.mul_rpow hy.1 (h0 x hx), ← Real.mul_rpow hx.1 (h0 y hy)]
        exact Real.rpow_le_rpow (mul_nonneg hy.1 (h0 x hx))
          (concave_ratio_left hg h0 hx hy hyx) hγ
      calc (1 - c * y) ^ k * y ^ γ * ((1 - c * x) ^ k * g x ^ γ)
          = ((1 - c * x) ^ k * (1 - c * y) ^ k) * (y ^ γ * g x ^ γ) := by ring
        _ ≤ ((1 - c * x) ^ k * (1 - c * y) ^ k) * (x ^ γ * g y ^ γ) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hρx hρy)
        _ = (1 - c * x) ^ k * x ^ γ * ((1 - c * y) ^ k * g y ^ γ) := by ring)
  -- Step 2: the same inequality for `g(s) = s`, through the Beta distribution
  have step2 : r * (∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ) ≤
      ∫ s in (0:ℝ)..1, (1 - c * s) * ((1 - c * s) ^ k * s ^ γ) := by
    rcases eq_or_lt_of_le hc0 with h | h
    · subst h
      simp only [zero_mul, sub_zero, one_mul]
      have : 0 ≤ ∫ s in (0:ℝ)..1, (1:ℝ) ^ k * s ^ γ :=
        integral_nonneg zero_le_one fun s hs => mul_nonneg (by simp) (Real.rpow_nonneg hs.1 _)
      nlinarith
    · have hT := trunc_mean (r := r) (c := c) (cont_beta hk hγ)
        (fun u hu => mul_nonneg (Real.rpow_nonneg (by linarith [hu.2]) _)
          (Real.rpow_nonneg hu.1 _))
        (fun u hu => mul_pos (Real.rpow_pos_of_pos (by linarith [hu.2]) _)
          (Real.rpow_pos_of_pos hu.1 _))
        (by rw [hr, div_mul_eq_mul_div, eq_div_iff hkγ.ne', mul_comm]; exact beta_mean hk hγ)
        hc0 hc1
      have s0 := intervalIntegral.integral_comp_mul_left
        (fun u => (1 - u) ^ k * u ^ γ) h.ne' (a := 0) (b := 1)
      have s1 := intervalIntegral.integral_comp_mul_left
        (fun u => (1 - u) * ((1 - u) ^ k * u ^ γ)) h.ne' (a := 0) (b := 1)
      simp only [mul_zero, mul_one, smul_eq_mul] at s0 s1
      have e0 : ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * (c * s) ^ γ =
          c ^ γ * ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ := by
        rw [← intervalIntegral.integral_const_mul]
        refine integral_congr fun s hs => ?_
        rw [uIcc_of_le zero_le_one] at hs
        simp only [Real.mul_rpow hc0 hs.1]; ring
      have e1 : ∫ s in (0:ℝ)..1, (1 - c * s) * ((1 - c * s) ^ k * (c * s) ^ γ) =
          c ^ γ * ∫ s in (0:ℝ)..1, (1 - c * s) * ((1 - c * s) ^ k * s ^ γ) := by
        rw [← intervalIntegral.integral_const_mul]
        refine integral_congr fun s hs => ?_
        rw [uIcc_of_le zero_le_one] at hs
        simp only [Real.mul_rpow hc0 hs.1]; ring
      rw [e0] at s0
      rw [e1] at s1
      have hcγ : 0 < c ^ γ := Real.rpow_pos_of_pos h γ
      have key : c ^ γ * (r * ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ) ≤
          c ^ γ * ∫ s in (0:ℝ)..1, (1 - c * s) * ((1 - c * s) ^ k * s ^ γ) := by
        have := mul_le_mul_of_nonneg_left hT (inv_nonneg.2 h.le)
        rw [← s1] at this
        calc c ^ γ * (r * ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ)
            = r * (c ^ γ * ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ) := by ring
          _ = c⁻¹ * (r * ∫ u in (0:ℝ)..c, (1 - u) ^ k * u ^ γ) := by rw [s0]; ring
          _ ≤ _ := this
      exact le_of_mul_le_mul_left key hcγ
  -- combination
  have hBpos : 0 < ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ :=
    intervalIntegral_pos_of_pos_on iB (fun s hs => mul_pos (Real.rpow_pos_of_pos (wpos s hs) _)
      (Real.rpow_pos_of_pos hs.1 _)) zero_lt_one
  have hA0 : 0 ≤ ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * g s ^ γ :=
    integral_nonneg zero_le_one fun s hs => mul_nonneg (Real.rpow_nonneg (w0 s hs) _)
      (Real.rpow_nonneg (h0 s hs) _)
  have lin : ∀ (F : ℝ → ℝ), IntervalIntegrable F volume 0 1 →
      IntervalIntegrable (fun s => s * F s) volume 0 1 →
      ∫ s in (0:ℝ)..1, (1 - c * s) * F s =
        (∫ s in (0:ℝ)..1, F s) - c * ∫ s in (0:ℝ)..1, s * F s := by
    intro F i1 i2
    rw [← intervalIntegral.integral_const_mul, ← integral_sub i1 (i2.const_mul c)]
    congr 1; funext s; ring
  rw [lin _ iB isB] at step2
  rw [lin _ iA isA]
  set A0 := ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * g s ^ γ
  set A1 := ∫ s in (0:ℝ)..1, s * ((1 - c * s) ^ k * g s ^ γ)
  set B0 := ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * s ^ γ
  set B1 := ∫ s in (0:ℝ)..1, s * ((1 - c * s) ^ k * s ^ γ)
  -- step1 : B0 * A1 ≤ B1 * A0, step2 : r * B0 ≤ B0 - c * B1
  have a1 := mul_le_mul_of_nonneg_left step1 hc0
  have a2 := mul_le_mul_of_nonneg_left step2 hA0
  have : B0 * (r * A0) ≤ B0 * (A0 - c * A1) := by nlinarith
  exact le_of_mul_le_mul_left this hBpos

/-- **Lemma 76** (`g:lem:mean`). Let `k, γ ≥ 0` be real, `w(s) = 1 - c s` with `0 ≤ c ≤ 1`, and
let `g ≥ 0` be concave on `[0, 1]` and not identically zero. Then the mean `s̄` of the density
proportional to `w^k g^γ` on `[0, 1]` satisfies `w(s̄) ≥ (k+1)/(k+γ+2)`. -/
theorem weighted_mean (hk : 0 ≤ k) (hγ : 0 ≤ γ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hg : ConcaveOn ℝ (Icc 0 1) g) (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (hne : ∃ x ∈ Icc (0:ℝ) 1, g x ≠ 0) :
    (k + 1) / (k + γ + 2) ≤ 1 - c * meanOn 0 1 (fun s => (1 - c * s) ^ k * g s ^ γ) := by
  have core := weighted_mean_core hk hγ hc0 hc1 hg h0
  have hG := concave_rpow_intervalIntegrable hγ hg h0
  have cw := cont_one_sub_rpow hk c
  have iA : IntervalIntegrable (fun s => (1 - c * s) ^ k * g s ^ γ) volume 0 1 :=
    hG.continuousOn_mul cw.continuousOn
  have isA : IntervalIntegrable (fun s => s * ((1 - c * s) ^ k * g s ^ γ)) volume 0 1 := by
    have := hG.continuousOn_mul (continuous_id.mul cw).continuousOn
    convert this using 1; funext s; simp only [Pi.mul_apply, id]; ring
  have hApos : 0 < ∫ s in (0:ℝ)..1, (1 - c * s) ^ k * g s ^ γ :=
    intervalIntegral_pos_of_pos_on iA (fun s hs => mul_pos
      (Real.rpow_pos_of_pos (by nlinarith [hs.1, hs.2]) _)
      (Real.rpow_pos_of_pos (concave_pos hg h0 hne hs) _)) zero_lt_one
  have e : ∫ s in (0:ℝ)..1, (1 - c * s) * ((1 - c * s) ^ k * g s ^ γ) =
      (∫ s in (0:ℝ)..1, (1 - c * s) ^ k * g s ^ γ) -
        c * ∫ s in (0:ℝ)..1, s * ((1 - c * s) ^ k * g s ^ γ) := by
    rw [← intervalIntegral.integral_const_mul, ← integral_sub iA (isA.const_mul c)]
    congr 1; funext s; ring
  rw [e] at core
  unfold meanOn
  rw [mul_div_assoc', le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hApos]
  nlinarith

/-- The equality case of Lemma 76: for `c = 1` and `g(s) = s`, `w(s̄) = (k+1)/(k+γ+2)`. -/
theorem weighted_mean_eq (hk : 0 ≤ k) (hγ : 0 ≤ γ) :
    1 - 1 * meanOn 0 1 (fun s => (1 - 1 * s) ^ k * s ^ γ) = (k + 1) / (k + γ + 2) := by
  simp only [one_mul]
  have cb := cont_beta hk hγ
  have hb := beta_mean hk hγ
  have i0 : IntervalIntegrable (fun u : ℝ => (1 - u) ^ k * u ^ γ) volume 0 1 :=
    cb.intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun u : ℝ => u * ((1 - u) ^ k * u ^ γ)) volume 0 1 :=
    (continuous_id.mul cb).intervalIntegrable _ _
  have e : ∫ u in (0:ℝ)..1, (1 - u) * ((1 - u) ^ k * u ^ γ) =
      (∫ u in (0:ℝ)..1, (1 - u) ^ k * u ^ γ) - ∫ u in (0:ℝ)..1, u * ((1 - u) ^ k * u ^ γ) := by
    rw [← integral_sub i0 i1]; congr 1; funext u; ring
  have hpos : 0 < ∫ u in (0:ℝ)..1, (1 - u) ^ k * u ^ γ :=
    intervalIntegral_pos_of_pos_on i0 (fun u hu => mul_pos
      (Real.rpow_pos_of_pos (by linarith [hu.2]) _) (Real.rpow_pos_of_pos hu.1 _)) zero_lt_one
  rw [e] at hb
  unfold meanOn
  have hkγ : 0 < k + γ + 2 := by linarith
  set I0 := ∫ u in (0:ℝ)..1, (1 - u) ^ k * u ^ γ
  set I1 := ∫ u in (0:ℝ)..1, u * ((1 - u) ^ k * u ^ γ)
  rw [eq_div_iff hkγ.ne']
  field_simp
  linarith

end WeightedMean

end Mixes
