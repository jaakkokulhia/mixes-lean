import Mixes.Poly

/-!
# Regular polygons, concrete (Theorem 95, Corollary 96)

Item M1k, second part: Theorem 95 (`st:thm:poly`) and Corollary 96 (d) (`st:cor:poly`) of
`mixes/main.tex` for the concrete regular `k`-gon `poly k ⊆ ℂ` (inradius `1`, centre `0`).

* Objects: `disc`, `nrm`, `poly`, `cp m = λ_{m+1}` (convolution powers of `1_B`), the Lebesgue
  measure `lamG` on tuples with its one- and two-point densities (`lamG_map_zero`,
  `lamG_map_pair`, `permInvariant_lamG`), and for `n = m + 3`: `aF m = a_n`, `hF m = λ_{n-2}`,
  `corner`, `nu`, `nus`, `proj` (angular Fourier components), `Top`, `Gop`.
* Geometry: `volume_poly` (`|P_k| = k tan(π/k)`), `mem_ang_iff`, `arc_integral`,
  `centroid_poly`, `completelyMixable_two_iff_even` (`n = 2` iff `k` even).
* Constants: `cp_one_eq` (`a₃ = lens`), `cp_one_zero` (`c₂ = π`), `cp_two_zero`
  (`c₃ = π² - (3/4)√3π`).
* Fourier: `fourier_ae` (a.e. inversion for summable coefficients), `norm_Top_le`,
  `norm_proj_nu_le`, `proj_nu_eq_zero`, `mode_solve` (Neumann series for `G_κ`), `exists_phi`
  (`φ = -∑ G_κ⁻¹ ν_κ`, `Gφ = -ν_o`).
* Assembly: `thm95_of_phi`; Theorem 95: `thm95_pointwise` (condition (22)), `thm95`
  (condition (21)); Corollary 96 (d): `cor96d_poly`, `cor96d_poly_iff`.
* Cited hypothesis: `PLHyp` (Prékopa–Leindler: the radial profiles of `λ_m` are
  non-increasing).
-/

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Mixes

namespace PolyB

/-- The closed unit disc `B`. -/
def disc : Set ℂ := Metric.closedBall 0 1

/-- The unit normal of the `j`-th side of the regular `k`-gon, `e^{2πij/k}`. -/
def nrm (k j : ℕ) : ℂ := Complex.exp (((2 * π * j / k : ℝ) : ℂ) * Complex.I)

/-- The regular `k`-gon `P_k` with inradius `1` and centre `0`, with side normals `nrm k j`. -/
def poly (k : ℕ) : Set ℂ := {z | ∀ j < k, (z * (starRingEnd ℂ) (nrm k j)).re ≤ 1}

/-- `cp m x = λ_{m+1}(x)`, the `(m+1)`-fold convolution power of `1_B` at `x`: the measure of
the `y ∈ B^m` with `x - ∑ yᵢ ∈ B`. -/
def cp (m : ℕ) (x : ℂ) : ℝ≥0∞ :=
  volume {y : Fin m → ℂ | (∀ i, y i ∈ disc) ∧ x - ∑ i, y i ∈ disc}

section GeomA


variable {k : ℕ}

/-- `e^{2πim/k}` for an integer `m`. -/
def ee (k : ℕ) (m : ℤ) : ℂ := Complex.exp (((2 * π * m / k : ℝ) : ℂ) * Complex.I)

lemma nrm_eq_ee (k j : ℕ) : nrm k j = ee k j := by simp [nrm, ee]

lemma ee_add (k : ℕ) (a b : ℤ) : ee k (a + b) = ee k a * ee k b := by
  simp only [ee, ← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_mul_k (hk : 0 < k) (q : ℤ) : ee k (k * q) = 1 := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [ee, ← Complex.exp_int_mul_two_pi_mul_I q]; congr 1; push_cast; field_simp

lemma ee_emod (hk : 0 < k) (m : ℤ) : ee k (m % k) = ee k m := by
  conv_rhs => rw [← Int.emod_add_mul_ediv m k, ee_add, ee_mul_k hk, mul_one]

lemma conj_ee (k : ℕ) (m : ℤ) : (starRingEnd ℂ) (ee k m) = ee k (-m) := by
  rw [ee, ee, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma norm_ee (k : ℕ) (m : ℤ) : ‖ee k m‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma norm_nrm {j : ℕ} : ‖nrm k j‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma re_mul_conj_ee (z : ℂ) (k : ℕ) (m : ℤ) :
    (z * (starRingEnd ℂ) (ee k m)).re =
      z.re * cos (2 * π * m / k) + z.im * sin (2 * π * m / k) := by
  rw [Complex.mul_re, ee, Complex.conj_re, Complex.conj_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]; ring

lemma mem_poly_iff (hk : 0 < k) (z : ℂ) :
    z ∈ poly k ↔ ∀ m : ℤ, (z * (starRingEnd ℂ) (ee k m)).re ≤ 1 := by
  constructor
  · intro h m
    have h0 : 0 ≤ m % k := Int.emod_nonneg _ (by exact_mod_cast hk.ne')
    have h1 : m % k < k := Int.emod_lt_of_pos _ (by exact_mod_cast hk)
    have := h (m % k).toNat (by omega)
    rwa [nrm_eq_ee, Int.toNat_of_nonneg h0, ee_emod hk] at this
  · intro h j _; rw [nrm_eq_ee]; exact h j

/-- Rotating by a side normal preserves the polygon. -/
lemma mul_nrm_mem_poly (hk : 0 < k) (j : ℕ) (z : ℂ) :
    nrm k j * z ∈ poly k ↔ z ∈ poly k := by
  rw [mem_poly_iff hk, mem_poly_iff hk, nrm_eq_ee]
  have key : ∀ m : ℤ, ee k j * z * (starRingEnd ℂ) (ee k m) =
      z * (starRingEnd ℂ) (ee k (m - j)) := by
    intro m
    rw [conj_ee, conj_ee, show -(m - (j : ℤ)) = -m + j by ring, ee_add]; ring
  simp only [key]
  constructor
  · intro h m; simpa using h (m + j)
  · intro h m; exact h _

lemma isClosed_poly (k : ℕ) : IsClosed (poly k) := by
  have : poly k =
      ⋂ j ∈ {j | j < k}, {z : ℂ | (z * (starRingEnd ℂ) (nrm k j)).re ≤ 1} := by
    ext z; simp [poly]
  rw [this]
  exact isClosed_biInter fun j _ =>
    isClosed_le (Complex.continuous_re.comp (continuous_id.mul continuous_const))
      continuous_const

lemma measurableSet_poly (k : ℕ) : MeasurableSet (poly k) := (isClosed_poly k).measurableSet

lemma convex_poly (k : ℕ) : Convex ℝ (poly k) := by
  intro x hx y hy a b ha hb hab j hj
  have h1 := hx j hj; have h2 := hy j hj
  have : ((a • x + b • y) * (starRingEnd ℂ) (nrm k j)).re =
      a * (x * (starRingEnd ℂ) (nrm k j)).re + b * (y * (starRingEnd ℂ) (nrm k j)).re := by
    simp [add_mul, Complex.mul_re]; ring
  rw [this]; nlinarith

lemma disc_subset_poly (k : ℕ) : disc ⊆ poly k := by
  intro z hz j _
  have hz' : ‖z‖ ≤ 1 := by simpa [disc] using hz
  calc (z * (starRingEnd ℂ) (nrm k j)).re ≤ ‖z * (starRingEnd ℂ) (nrm k j)‖ :=
        Complex.re_le_norm _
    _ = ‖z‖ := by rw [norm_mul, Complex.norm_conj, norm_nrm, mul_one]
    _ ≤ 1 := hz'
lemma cos_pi_div_pos (hk : 3 ≤ k) : 0 < cos (π / k) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  apply cos_pos_of_mem_Ioo; constructor
  · have : 0 < π / k := by positivity
    linarith [pi_pos]
  · rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]

/-- The polygon lies in the closed disc of radius `secR k = 1 / cos (π / k)`. -/
lemma poly_subset_closedBall (hk : 3 ≤ k) :
    poly k ⊆ Metric.closedBall 0 (Mixes.Poly.secR k) := by
  intro z hz
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [mem_poly_iff hk0] at hz
  rw [Metric.mem_closedBall, dist_zero_right, Mixes.Poly.secR, le_div_iff₀ (cos_pi_div_pos hk)]
  set t := z.arg * k / (2 * π)
  set m := round t
  have hm := hz m
  have hround : |t - m| ≤ 1 / 2 := abs_sub_round t
  set x := z.arg - 2 * π * m / k with hx
  have hxeq : x = 2 * π / k * (t - m) := by
    simp only [hx, t]; field_simp
  have hxabs : |x| ≤ π / k := by
    rw [hxeq, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / k)]
    calc 2 * π / k * |t - m| ≤ 2 * π / k * (1 / 2) := by gcongr
      _ = π / k := by ring
  have hre : (z * (starRingEnd ℂ) (ee k m)).re = ‖z‖ * cos x := by
    rw [re_mul_conj_ee]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
    rw [hx, cos_sub]; ring
  have hcos : cos (π / k) ≤ cos x := by
    rw [← cos_abs x]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) _ hxabs
    calc π / k ≤ π / 1 := by gcongr; linarith
      _ = π := div_one π
  rw [hre] at hm
  nlinarith [norm_nonneg z]

lemma isCompact_poly (hk : 3 ≤ k) : IsCompact (poly k) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_poly k)
    (Metric.isBounded_closedBall.subset (poly_subset_closedBall hk))

lemma volume_poly_pos (k : ℕ) : 0 < volume (poly k) :=
  lt_of_lt_of_le (Metric.measure_closedBall_pos _ _ one_pos) (measure_mono (disc_subset_poly k))

lemma volume_poly_ne_top (hk : 3 ≤ k) : volume (poly k) ≠ ⊤ :=
  (isCompact_poly hk).measure_lt_top.ne

/-- `U(P_k)` is a probability measure. -/
lemma unifSet_poly_isProb (hk : 3 ≤ k) : IsProbabilityMeasure (Mixes.unifSet (poly k)) :=
  Room.unifSet_isProb (isCompact_poly hk) (volume_poly_pos k)

/-! ## Rotations -/

/-- Multiplication by `u` as a continuous `ℝ`-linear map. -/
def rot (u : ℂ) : ℂ →L[ℝ] ℂ := (LinearMap.mulLeft ℝ u).toContinuousLinearMap

@[simp] lemma rot_apply (u z : ℂ) : rot u z = u * z := rfl

lemma rot_pow_apply (u : ℂ) (n : ℕ) (z : ℂ) : (rot u ^ n) z = u ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']; show rot u ((rot u ^ n) z) = _
    rw [ih, rot_apply]; ring

lemma nrm_pow {n : ℕ} (j : ℕ) : nrm n 1 ^ j = nrm n j := by
  rw [nrm, nrm, ← Complex.exp_natCast_mul]; congr 1; push_cast; ring

lemma nrm_self {n : ℕ} (hn : 0 < n) : nrm n n = 1 := by
  rw [nrm_eq_ee, show ((n : ℕ) : ℤ) = n * 1 by ring, ee_mul_k hn]

lemma rot_pow_eq_one {n : ℕ} (hn : 0 < n) : rot (nrm n 1) ^ n = 1 := by
  ext1 z; rw [rot_pow_apply, nrm_pow, nrm_self hn, one_mul]; rfl

lemma nrm_one_ne_one {n : ℕ} (hn : 2 ≤ n) : nrm n 1 ≠ 1 := by
  intro h
  rw [nrm, Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 2 * π * ((1 : ℕ) : ℝ) / n = m * (2 * π) := by
    have := congrArg Complex.im hm
    simpa using this
  have hpos : 0 < 2 * π * ((1 : ℕ) : ℝ) / n := by positivity
  have hlt : 2 * π * ((1 : ℕ) : ℝ) / n < 2 * π := by
    rw [div_lt_iff₀ (by positivity)]; push_cast; nlinarith [pi_pos]
  rw [h2] at hpos hlt
  have h0 : (0 : ℝ) < m := by nlinarith [pi_pos]
  have h1 : (m : ℝ) < 1 := by nlinarith [pi_pos]
  have : (0 : ℤ) < m := by exact_mod_cast h0
  have : m < (1 : ℤ) := by exact_mod_cast h1
  omega

lemma rot_fix {n : ℕ} (hn : 2 ≤ n) : ∀ x, rot (nrm n 1) x = x → x = 0 := by
  intro x hx
  rw [rot_apply] at hx
  have : (nrm n 1 - 1) * x = 0 := by rw [sub_mul, hx]; ring
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) (nrm_one_ne_one hn)
  · exact h

lemma measurePreserving_rot {u : ℂ} (hu : ‖u‖ = 1) :
    MeasurePreserving (rot u) volume volume := by
  have hu' : u ∈ Submonoid.unitSphere ℂ := by simp [Submonoid.unitSphere, hu]
  have := (rotation (⟨u, hu'⟩ : Circle)).measurePreserving
  convert this using 1
  funext z; rw [rot_apply]; exact (rotation_apply (⟨u, hu'⟩ : Circle) z).symm

lemma mul_mem_disc_iff {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) : u * z ∈ disc ↔ z ∈ disc := by
  simp [disc, hu]

/-- The centroid of the regular polygon is `0`. -/
lemma centroid_poly (hk : 3 ≤ k) : Room.centroid (poly k) = 0 := by
  have hk0 : 0 < k := by omega
  refine Room.centroid_eq_zero (rot (nrm k 1)) (rot_fix (by omega)) (isCompact_poly hk)
    (volume_poly_pos k) (Room.unifSet_map _ (measurePreserving_rot norm_nrm).map_eq
      (measurableSet_poly k) ?_)
  ext z; exact mul_nrm_mem_poly hk0 1 z

lemma nrm_half {k : ℕ} (hk : Even k) (hk0 : 0 < k) : nrm k (k / 2) = -1 := by
  obtain ⟨r, rfl⟩ := hk
  have hr0 : r ≠ 0 := by omega
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  rw [nrm, show (r + r) / 2 = r by omega]
  rw [show ((2 * π * (r : ℕ) / ((r + r : ℕ) : ℝ) : ℝ) : ℂ) = π by
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
    push_cast; rw [show ((r : ℂ) + r) = 2 * r by ring]; field_simp]
  exact Complex.exp_pi_mul_I

/-- For even `k` the polygon is point symmetric. -/
lemma neg_mem_poly {k : ℕ} (hk : Even k) (z : ℂ) : -z ∈ poly k ↔ z ∈ poly k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [poly]
  rw [show -z = nrm k (k / 2) * z by rw [nrm_half hk hk0]; ring]
  exact mul_nrm_mem_poly hk0 _ z

/-- For odd `k`, every side normal makes an angle at least `π/k` with `-1`. -/
lemma neg_cos_le_of_odd {k : ℕ} (hk : Odd k) {j : ℕ} (hj : j < k) :
    -cos (2 * π * j / k) ≤ cos (π / k) := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  set d : ℤ := (k : ℤ) - 2 * j with hd
  have hd1 : 1 ≤ |d| := by
    obtain ⟨r, rfl⟩ := hk
    have : d ≠ 0 := by omega
    exact Int.one_le_abs this
  have hd2 : |d| ≤ k := by rw [abs_le]; constructor <;> omega
  have hdR1 : (1 : ℝ) ≤ |(d : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hd1
  have hdR2 : |(d : ℝ)| ≤ k := by rw [← Int.cast_abs]; exact_mod_cast hd2
  have hy : -cos (2 * π * j / k) = cos (π * |(d : ℝ)| / k) := by
    rw [← cos_pi_sub, ← cos_abs (π - _)]
    congr 1
    have : π - 2 * π * j / k = π * d / k := by
      rw [hd]; push_cast; field_simp
    rw [this, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hkR]
  rw [hy]
  apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · rw [div_le_iff₀ hkR]; nlinarith [mul_le_mul_of_nonneg_left hdR2 pi_pos.le]
  · apply div_le_div_of_nonneg_right _ hkR.le; nlinarith [pi_pos]

/-- **Corollary 96 (d), `n = 2`.** `U(P_k)` is `2`-completely mixable iff `k` is even. -/
theorem completelyMixable_two_iff_even {k : ℕ} (hk : 3 ≤ k) :
    CompletelyMixable 2 (Mixes.unifSet (poly k)) ↔ Even k := by
  have := unifSet_poly_isProb hk
  rw [Mixes.completelyMixable_two_iff]
  constructor
  · rintro ⟨c, hc⟩
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hk0' : 0 < k := by omega
    set F := Mixes.unifSet (poly k) with hF
    have hint : Integrable (fun x : ℂ => x) F :=
      Room.unifSet_integrable (isCompact_poly hk) (volume_poly_pos k)
    have hcen : ∫ x, x ∂F = 0 := centroid_poly hk
    have hmeas : Measurable (fun x : ℂ => c - x) := measurable_const_sub c
    have h1 : ∫ x, x ∂(F.map (fun x => c - x)) = c := by
      rw [show (∫ x, x ∂(F.map (fun x => c - x))) = ∫ x, (c - x) ∂F from
        integral_map hmeas.aemeasurable aestronglyMeasurable_id,
        integral_sub (integrable_const c) hint]
      simp [hcen]
    have hc0 : c = 0 := by rw [← h1, hc, hcen]
    subst hc0
    -- an open set `U ⊆ P` with `-U` disjoint from `P`
    set U : Set ℂ := {z | (∀ j < k, (z * (starRingEnd ℂ) (nrm k j)).re < 1) ∧ z.re < -1}
      with hU
    have hUo : IsOpen U := by
      have : U = (⋂ j ∈ {j | j < k}, {z : ℂ | (z * (starRingEnd ℂ) (nrm k j)).re < 1}) ∩
          {z : ℂ | z.re < -1} := by ext z; simp [hU]
      rw [this]
      exact ((Set.finite_lt_nat k).isOpen_biInter fun j _ =>
        isOpen_lt (Complex.continuous_re.comp (continuous_id.mul continuous_const))
          continuous_const).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hc0 := cos_pi_div_pos hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hc1 : cos (π / k) < 1 := by
      rw [← cos_zero]
      apply cos_lt_cos_of_nonneg_of_le_pi le_rfl
      · rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
      · positivity
    set s : ℝ := (1 + 1 / cos (π / k)) / 2 with hs
    have hs1 : 1 < s := by
      have : 1 < 1 / cos (π / k) := by rw [lt_div_iff₀ hc0]; linarith
      rw [hs]; linarith
    have hsc : s * cos (π / k) < 1 := by
      rw [hs, add_div, add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, one_div_mul_cancel hc0.ne']
      linarith
    have hx0 : (-(s : ℂ)) ∈ U := by
      refine ⟨fun j hj => ?_, by simp; linarith⟩
      rw [nrm_eq_ee, re_mul_conj_ee]
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
        zero_mul, add_zero, Int.cast_natCast]
      have := neg_cos_le_of_odd hodd hj
      nlinarith
    have hUpos : 0 < volume U := hUo.measure_pos volume ⟨_, hx0⟩
    have hUP : U ⊆ poly k := fun z hz j hj => (hz.1 j hj).le
    have hdisj : (fun x : ℂ => 0 - x) ⁻¹' U ∩ poly k = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hw hwP
      have h0 := hwP 0 hk0'
      simp [nrm] at h0
      have := hw.2
      simp at this
      linarith
    have hFU : F U ≠ 0 := by
      rw [hF, Mixes.unifSet, smul_apply, Measure.restrict_apply hUo.measurableSet,
        Set.inter_eq_left.2 hUP, smul_eq_mul]
      exact mul_ne_zero (ENNReal.inv_ne_zero.2 (volume_poly_ne_top hk)) hUpos.ne'
    apply hFU
    rw [← hc, Measure.map_apply hmeas hUo.measurableSet, hF, Mixes.unifSet, smul_apply,
      Measure.restrict_apply (hmeas hUo.measurableSet), hdisj]
    simp
  · intro he
    refine ⟨0, ?_⟩
    have : (fun x : ℂ => 0 - x) = rot (-1) := by funext x; simp
    rw [this]
    exact Room.unifSet_map _ (measurePreserving_rot (by simp)).map_eq (measurableSet_poly k)
      (by ext z; simp [neg_mem_poly he])

end GeomA

section AreaB

/-- The angular section of `P_k` at radius `ρ`: the `θ` with `ρ e^{iθ} ∈ P_k`. -/
def ang (k : ℕ) (ρ : ℝ) : Set ℝ := {θ | ∀ j : ℤ, ρ * cos (θ - 2 * π * j / k) ≤ 1}

lemma re_polar_nrm (k j : ℕ) (ρ θ : ℝ) :
    ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) (nrm k j)).re =
      ρ * cos (θ - 2 * π * j / k) := by
  rw [nrm, ← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
  have : (θ : ℂ) * Complex.I + (starRingEnd ℂ) (((2 * π * j / k : ℝ) : ℂ) * Complex.I) =
      ((θ - 2 * π * j / k : ℝ) : ℂ) * Complex.I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Polar membership.** `ρ e^{iθ} ∈ P_k` iff `ρ cos(θ - 2πj/k) ≤ 1` for all `j ∈ ℤ`. -/
lemma mem_poly_polar {k : ℕ} (hk : 0 < k) (ρ θ : ℝ) :
    (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ poly k ↔ θ ∈ ang k ρ := by
  simp only [poly, ang, Set.mem_ofPred_eq, re_polar_nrm]
  constructor
  · intro h j
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hr0 : 0 ≤ j % k := Int.emod_nonneg _ hk'
    have hrk : j % k < k := Int.emod_lt_of_pos _ (by exact_mod_cast hk)
    have h1 := h (j % k).toNat (by omega)
    have hc : ((j % k).toNat : ℝ) = ((j % k : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
    rw [hc] at h1
    have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have : θ - 2 * π * j / k = θ - 2 * π * ((j % k : ℤ) : ℝ) / k - ((j / k : ℤ) : ℝ) * (2 * π) := by
      have hj := Int.emod_add_mul_ediv j k
      have : (j : ℝ) = ((j % k : ℤ) : ℝ) + k * ((j / k : ℤ) : ℝ) := by exact_mod_cast hj.symm
      rw [this]; field_simp; ring
    rw [this, cos_sub_int_mul_two_pi]; exact h1
  · intro h j _
    exact_mod_cast h j

/-- `ang k ρ` is invariant under rotation by multiples of `2π/k`. -/
lemma ang_shift (k : ℕ) (ρ : ℝ) (m : ℤ) (θ : ℝ) :
    θ + m * (2 * π / k) ∈ ang k ρ ↔ θ ∈ ang k ρ := by
  simp only [ang, Set.mem_ofPred_eq]
  constructor
  · intro h j
    have := h (j + m); push_cast at this
    convert this using 3; ring
  · intro h j
    have := h (j - m); push_cast at this
    convert this using 3; ring

lemma isClosed_ang (k : ℕ) (ρ : ℝ) : IsClosed (ang k ρ) := by
  have : ang k ρ = ⋂ j : ℤ, {θ | ρ * cos (θ - 2 * π * j / k) ≤ 1} := by
    ext; simp [ang]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma cos_le_cos_mid {c x : ℝ} (hc0 : 0 ≤ c) (h1 : c ≤ x) (h2 : x ≤ 2 * π - c) :
    cos x ≤ cos c := by
  by_cases hx : x ≤ π
  · exact cos_le_cos_of_nonneg_of_le_pi hc0 hx h1
  · rw [← cos_two_pi_sub x]
    exact cos_le_cos_of_nonneg_of_le_pi hc0 (by linarith) (by linarith)

lemma le_of_cos_le_cos {c x : ℝ} (hx0 : 0 ≤ x) (hcπ : c ≤ π) (h : cos x ≤ cos c) :
    c ≤ x := by
  by_contra hlt; push Not at hlt
  have := cos_lt_cos_of_nonneg_of_le_pi hx0 hcπ hlt; linarith

/-- **The window `[0, 2π/k]`.** For `0 ≤ θ ≤ 2π/k`, `θ ∈ ang k ρ` iff
`arccos(1/ρ) ≤ θ ≤ 2π/k - arccos(1/ρ)`: an interval of half-width `π/k - arccos(1/ρ)`
centred at the vertex angle `π/k`. -/
lemma mem_ang_window {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 2 * π / k) :
    θ ∈ ang k ρ ↔ θ ∈ Icc (arccos (1 / ρ)) (2 * π / k - arccos (1 / ρ)) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hu : 2 * π / k ≤ π := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hku : (k : ℝ) * (2 * π / k) = 2 * π := by field_simp
  rcases le_total ρ 1 with hρ1 | hρ1
  · have hc : arccos (1 / ρ) = 0 := arccos_eq_zero.2 (by rw [le_div_iff₀ hρ]; linarith)
    rw [hc]
    simp only [ang, Set.mem_ofPred_eq, sub_zero, Set.mem_Icc]
    refine ⟨fun _ => ⟨h0, h1⟩, fun _ j => ?_⟩
    nlinarith [cos_le_one (θ - 2 * π * j / k)]
  set c := arccos (1 / ρ) with hcdef
  have hcc : cos c = 1 / ρ := cos_arccos (by
    have : 0 < 1 / ρ := by positivity
    linarith) (by rw [div_le_iff₀ hρ]; linarith)
  have hc0 : 0 ≤ c := arccos_nonneg _
  have hcπ : c ≤ π := arccos_le_pi _
  have key : ∀ x, ρ * cos x ≤ 1 ↔ cos x ≤ cos c := fun x => by
    rw [hcc, le_div_iff₀ hρ, mul_comm]
  simp only [ang, Set.mem_ofPred_eq, key, Set.mem_Icc]
  constructor
  · intro h
    have e0 := h 0
    have e1 := h 1
    simp only [Int.cast_zero, mul_zero, zero_div, sub_zero, Int.cast_one, mul_one] at e0 e1
    rw [← cos_neg, neg_sub] at e1
    exact ⟨le_of_cos_le_cos h0 hcπ e0, by
      have := le_of_cos_le_cos (x := 2 * π / k - θ) (by linarith) hcπ e1; linarith⟩
  · rintro ⟨hc1, hc2⟩ j
    set u := 2 * π / k with hudef
    have hj : 2 * π * j / k = j * u := by rw [hudef]; ring
    rw [hj]
    have hr0 : 0 ≤ j % k := Int.emod_nonneg _ (by exact_mod_cast (by omega : k ≠ 0))
    have hrk : j % k < k := Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < k))
    have hjd := Int.emod_add_mul_ediv j k
    set r := j % k
    set q := j / k
    have hjr : (j : ℝ) = r + k * q := by exact_mod_cast hjd.symm
    have hu0 : 0 ≤ u := by positivity
    have e : θ - j * u = (θ - r * u) - q * (2 * π) := by rw [hjr, ← hku]; ring
    rw [e, cos_sub_int_mul_two_pi]
    rcases eq_or_lt_of_le hr0 with hr | hr
    · rw [← hr]; simp only [Int.cast_zero, zero_mul, sub_zero]
      exact cos_le_cos_mid hc0 hc1 (by linarith)
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hrk' : (r : ℝ) ≤ k - 1 := by
        have : r ≤ k - 1 := by omega
        exact_mod_cast this
      rw [← cos_add_two_pi]
      apply cos_le_cos_mid hc0
      · nlinarith
      · nlinarith

/-- **The angular section as a union of arcs.** For `ρ > 0`, `ρ e^{iθ} ∈ P_k` iff `θ` lies within
`w = π/k - arccos(1/ρ)` of a vertex angle `π/k + 2πj/k` (`j ∈ ℤ`; the arcs for `j < k` are
disjoint mod `2π` since `w ≤ π/k`). -/
lemma mem_ang_iff {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    θ ∈ ang k ρ ↔ ∃ j : ℤ, |θ - (π / k + 2 * π * j / k)| ≤ π / k - arccos (1 / ρ) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 : 0 < 2 * π / k := by positivity
  have hc0 : 0 ≤ arccos (1 / ρ) := arccos_nonneg _
  constructor
  · intro h
    set m := ⌊θ / (2 * π / k)⌋
    have hm1 : (m : ℝ) ≤ θ / (2 * π / k) := Int.floor_le _
    have hm2 : θ / (2 * π / k) < m + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hu0] at hm1
    rw [div_lt_iff₀ hu0] at hm2
    have h' : θ - m * (2 * π / k) ∈ ang k ρ := by
      rw [← ang_shift k ρ m, sub_add_cancel]; exact h
    rw [mem_ang_window hk hρ (by linarith) (by linarith)] at h'
    refine ⟨m, abs_le.2 ⟨?_, ?_⟩⟩
    · have := h'.1
      have e : 2 * π * m / k = m * (2 * π / k) := by ring
      have e2 : π / k = (2 * π / k) / 2 := by ring
      rw [e, e2]; linarith
    · have := h'.2
      have e : 2 * π * m / k = m * (2 * π / k) := by ring
      have e2 : π / k = (2 * π / k) / 2 := by ring
      rw [e, e2]; linarith
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := abs_le.1 hj
    have e : 2 * π * j / k = j * (2 * π / k) := by ring
    have e2 : π / k = (2 * π / k) / 2 := by ring
    rw [e, e2] at h1 h2
    have h' : θ - j * (2 * π / k) ∈ ang k ρ := by
      rw [mem_ang_window hk hρ (by linarith) (by linarith)]
      constructor <;> linarith
    have := (ang_shift k ρ j (θ - j * (2 * π / k))).2 h'
    rwa [sub_add_cancel] at this

/-- Beyond the circumradius `secR k` the angular section is empty. -/
lemma ang_eq_empty {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : Poly.secR k < ρ) : ang k ρ = ∅ := by
  have hc := Poly.cos_pi_div_pos hk
  have hR := Poly.one_le_secR hk
  have hρ0 : 0 < ρ := by linarith
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hlt : π / k < arccos (1 / ρ) := by
    have h1 : 1 / ρ < cos (π / k) := by
      rw [Poly.secR, div_lt_iff₀ hc] at hρ
      rw [div_lt_iff₀ hρ0]; linarith
    have h0 : 0 ≤ π / k := by positivity
    have hpi : π / k ≤ π := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
    rw [← arccos_cos h0 hpi]
    have : 0 < 1 / ρ := by positivity
    exact arccos_lt_arccos (by linarith) h1 (cos_le_one _)
  ext θ
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_ang_iff hk hρ0]
  rintro ⟨j, hj⟩
  have := abs_nonneg (θ - (π / k + 2 * π * j / k))
  linarith

open Complex in
/-- **Fourier coefficient of the angular section, reduced to one window.** -/
lemma integral_ang {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) (κ : ℤ) :
    ∫ θ in Ioo (-π) π, (ang k ρ).indicator (fun θ : ℝ => cexp (-(I * κ) * θ)) θ =
      (∑ m ∈ Finset.range k, cexp (-(I * κ) * ((m : ℝ) * (2 * π / k) : ℝ))) *
        ∫ θ in Ioc 0 (2 * π / k) ∩ Icc (arccos (1 / ρ)) (2 * π / k - arccos (1 / ρ)),
          cexp (-(I * κ) * θ) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set u := 2 * π / k with hudef
  have hu0 : 0 < u := by positivity
  have hku : (k : ℝ) * u = 2 * π := by rw [hudef]; field_simp
  set g : ℝ → ℂ := fun θ => cexp (-(I * κ) * θ) with hg
  set G := (ang k ρ).indicator g with hG
  have hgc : Continuous g := by fun_prop
  have hGi : ∀ a b, IntervalIntegrable G volume a b := fun a b =>
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 (hgc.intervalIntegrable a b)).indicator
      (isClosed_ang k ρ).measurableSet)
  have hshift : ∀ (m : ℤ) θ, G (θ + m * u) = cexp (-(I * κ) * ((m : ℝ) * u : ℝ)) * G θ := by
    intro m θ
    by_cases h : θ ∈ ang k ρ
    · have h' : θ + m * u ∈ ang k ρ := (ang_shift k ρ m θ).2 h
      simp only [hG, Set.indicator_of_mem h, Set.indicator_of_mem h', hg, ← Complex.exp_add]
      congr 1; push_cast; ring
    · have h' : θ + m * u ∉ ang k ρ := fun h' => h ((ang_shift k ρ m θ).1 h')
      simp [hG, Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hper : Function.Periodic G (2 * π) := by
    intro θ
    have := hshift k θ
    have e : cexp (-(I * κ) * (((k : ℤ) : ℝ) * u : ℝ)) = 1 := by
      have : -(I * κ) * ((((k : ℤ) : ℝ) * u : ℝ) : ℂ) = ((-κ : ℤ) : ℂ) * (2 * π * I) := by
        have hku' : (k : ℂ) * (u : ℂ) = 2 * π := by exact_mod_cast hku
        push_cast
        linear_combination (-(I * κ)) * hku'
      rw [this, exp_int_mul_two_pi_mul_I]
    rw [e, one_mul] at this
    rw [← this]; congr 1; push_cast; rw [hku]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  have hp := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hp
  rw [hp]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun m : ℕ => (m : ℝ) * u) (n := k) (μ := volume) (fun m _ => hGi _ _)
  simp only [Nat.cast_zero, zero_mul, hku] at hsum
  rw [← hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : ∫ x in (0 : ℝ)..u, G (x + (m : ℤ) * u) =
      ∫ x in ((m : ℕ) : ℝ) * u..((m + 1 : ℕ) : ℝ) * u, G x := by
    rw [intervalIntegral.integral_comp_add_right]; congr 1 <;> push_cast <;> ring
  rw [← h1]
  simp_rw [hshift m]
  rw [intervalIntegral.integral_const_mul, Int.cast_natCast]
  refine congrArg (fun z : ℂ => cexp (-(I * κ) * ((m : ℝ) * u : ℝ)) * z) ?_
  rw [intervalIntegral.integral_of_le hu0.le, ← setIntegral_indicator measurableSet_Icc]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
  by_cases h : θ ∈ ang k ρ
  · have h' := (mem_ang_window hk hρ hθ.1.le hθ.2).1 h
    rw [hG, Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : θ ∉ Icc (arccos (1 / ρ)) (2 * π / k - arccos (1 / ρ)) :=
      fun h' => h ((mem_ang_window hk hρ hθ.1.le hθ.2).2 h')
    rw [hG, Set.indicator_of_notMem h, Set.indicator_of_notMem h']

lemma window_ae {u c d : ℝ} (hc0 : 0 ≤ c) (hdu : d ≤ u) :
    (Ioc 0 u ∩ Icc c d : Set ℝ) =ᵐ[volume] Icc c d := by
  have h := (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := u) (μ := volume)).inter
    (Filter.EventuallyEqSet.rfl (s := Icc c d))
  rwa [Set.inter_eq_right.2 (Icc_subset_Icc hc0 (by linarith : d ≤ u))] at h

open Complex in
lemma norm_integral_window_le (k : ℕ) (ρ : ℝ) {κ : ℤ} (hκ : κ ≠ 0) :
    ‖∫ θ in Ioc 0 (2 * π / k) ∩ Icc (arccos (1 / ρ)) (2 * π / k - arccos (1 / ρ)),
        cexp (-(I * κ) * θ)‖ ≤ 2 / |(κ : ℝ)| := by
  set c := arccos (1 / ρ)
  have hc0 : 0 ≤ c := arccos_nonneg _
  have hκr : (κ : ℝ) ≠ 0 := by exact_mod_cast hκ
  rcases le_or_gt c (2 * π / k - c) with hcd | hcd
  · rw [setIntegral_congr_set (window_ae hc0 (by linarith)), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hcd]
    have e1 : c = π / k - (π / k - c) := by ring
    have e2 : 2 * π / k - c = π / k + (π / k - c) := by ring
    rw [e2]; nth_rewrite 1 [e1]
    have := Poly.integral_arc hκr (π / k) (π / k - c)
    push_cast at this ⊢
    rw [this, norm_mul]
    have hn : ‖cexp (-(I * κ) * (π / k : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [hn, one_mul, norm_div, norm_mul]
    have : ‖((κ : ℤ) : ℂ)‖ = |(κ : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [this]
    gcongr
    have e3 : (κ : ℂ) * ((π : ℂ) / k - c) = (((κ : ℝ) * (π / k - c) : ℝ) : ℂ) := by push_cast; ring
    rw [e3, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
    have := abs_sin_le_one ((κ : ℝ) * (π / k - c))
    norm_num
    linarith
  · rw [Set.Icc_eq_empty (not_le.2 hcd), Set.inter_empty]
    simp only [Measure.restrict_empty, integral_zero_measure, norm_zero]
    positivity

open Complex in
/-- `∑_{m<k} e^{-iκ·2πm/k} = [k ∣ κ]·k`. -/
lemma sum_window_exp (k : ℕ) (hk : 0 < k) (κ : ℤ) :
    ∑ m ∈ Finset.range k, cexp (-(I * κ) * ((m : ℝ) * (2 * π / k) : ℝ)) =
      if (k : ℤ) ∣ κ then (k : ℂ) else 0 := by
  have h := Poly.sum_exp_root k hk (-κ)
  simp only [dvd_neg] at h
  rw [← h]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1; push_cast; ring

open Complex in
/-- **Fourier coefficients of the angular section of `P_k`.** At a radius `ρ ≥ 1`, the
`κ`-th coefficient (`κ ≠ 0`) of the indicator of `{θ : ρe^{iθ} ∈ P_k}` vanishes unless `k ∣ κ`,
and is at most `2k/|κ|` in absolute value. -/
theorem arc_integral {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : 1 ≤ ρ) {κ : ℤ} (hκ : κ ≠ 0) :
    ‖∫ θ in Ioo (-π) π, (poly k).indicator (fun _ => (1 : ℂ))
        ((ρ : ℂ) * cexp ((θ : ℂ) * I)) * cexp (-(I * κ) * θ)‖ ≤ 2 * k / |(κ : ℝ)| ∧
    (¬ (k : ℤ) ∣ κ → ∫ θ in Ioo (-π) π, (poly k).indicator (fun _ => (1 : ℂ))
        ((ρ : ℂ) * cexp ((θ : ℂ) * I)) * cexp (-(I * κ) * θ) = 0) := by
  have hk0 : 0 < k := by omega
  have hρ0 : 0 < ρ := by linarith
  have hfun : (fun θ : ℝ => (poly k).indicator (fun _ => (1 : ℂ))
      ((ρ : ℂ) * cexp ((θ : ℂ) * I)) * cexp (-(I * κ) * θ)) =
      (ang k ρ).indicator (fun θ : ℝ => cexp (-(I * κ) * θ)) := by
    funext θ
    by_cases h : θ ∈ ang k ρ
    · have h' := (mem_poly_polar hk0 ρ θ).2 h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h', one_mul]
    · have h' : (ρ : ℂ) * cexp ((θ : ℂ) * I) ∉ poly k := fun h' =>
        h ((mem_poly_polar hk0 ρ θ).1 h')
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', zero_mul]
  rw [hfun, integral_ang hk hρ0, sum_window_exp k hk0]
  refine ⟨?_, fun h => by simp [h]⟩
  rw [norm_mul]
  have h1 : ‖(if (k : ℤ) ∣ κ then (k : ℂ) else 0)‖ ≤ k := by split_ifs <;> simp
  calc _ ≤ (k : ℝ) * (2 / |(κ : ℝ)|) :=
        mul_le_mul h1 (norm_integral_window_le k ρ hκ) (norm_nonneg _) (by positivity)
    _ = 2 * k / |(κ : ℝ)| := by ring

lemma volume_window (k : ℕ) (ρ : ℝ) :
    volume (Ioc 0 (2 * π / k) ∩ Icc (arccos (1 / ρ)) (2 * π / k - arccos (1 / ρ))) =
      ENNReal.ofReal (2 * (π / k - arccos (1 / ρ))) := by
  set c := arccos (1 / ρ)
  have hc0 : 0 ≤ c := arccos_nonneg _
  rcases le_or_gt c (2 * π / k - c) with hcd | hcd
  · rw [measure_congr (window_ae hc0 (by linarith)), Real.volume_Icc]
    congr 1; ring
  · rw [Set.Icc_eq_empty (not_le.2 hcd), Set.inter_empty, measure_empty, eq_comm,
      ENNReal.ofReal_eq_zero]
    have : 2 * π / k = 2 * (π / k) := by ring
    linarith

open Complex in
/-- **Length of the angular section.** For `ρ > 0` the set of `θ ∈ (-π, π)` with
`ρ e^{iθ} ∈ P_k` has measure `2k · max(π/k - arccos(1/ρ), 0)`. -/
lemma volume_ang {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ang k ρ ∩ Ioo (-π) π) =
      ENNReal.ofReal (k * (2 * (π / k - arccos (1 / ρ)))) := by
  have hk0 : 0 < k := by omega
  have h := integral_ang hk hρ 0
  simp only [Int.cast_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [setIntegral_indicator (isClosed_ang k ρ).measurableSet, setIntegral_const,
    setIntegral_const, measureReal_def, measureReal_def, volume_window] at h
  have hfin : volume (Ioo (-π) π ∩ ang k ρ) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left (by simp)
  rw [Set.inter_comm, ← ENNReal.ofReal_toReal hfin]
  have h2 : ((volume (Ioo (-π) π ∩ ang k ρ)).toReal : ℂ) =
      ((k * (ENNReal.ofReal (2 * (π / k - arccos (1 / ρ)))).toReal : ℝ) : ℂ) := by
    simpa using h
  rw [Complex.ofReal_inj] at h2
  rw [h2]
  rcases le_total 0 (2 * (π / k - arccos (1 / ρ))) with hx | hx
  · rw [ENNReal.toReal_ofReal hx]
  · rw [ENNReal.ofReal_of_nonpos hx, ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero,
      eq_comm, ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hx

lemma hasDerivAt_G_B (a : ℝ) {ρ : ℝ} (hρ : 1 < ρ) :
    HasDerivAt (fun r : ℝ => a * r ^ 2 / 2 - r ^ 2 / 2 * arccos (1 / r) + √(r ^ 2 - 1) / 2)
      (ρ * (a - arccos (1 / ρ))) ρ := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : 1 / ρ ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hρ0.ne']; linarith
  have h2 : 1 / ρ ≠ -1 := by
    have : 0 < 1 / ρ := by positivity
    linarith
  have hinv : HasDerivAt (fun r : ℝ => 1 / r) (-(1 / ρ ^ 2)) ρ := by
    have := hasDerivAt_inv hρ0.ne'
    simpa [one_div] using this
  have hac := (Real.hasDerivAt_arccos h2 h1).comp ρ hinv
  have hs0 : ρ ^ 2 - 1 ≠ 0 := by nlinarith
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2 - 1) (2 * ρ) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).sub_const 1
  have hsqrt := hsq.sqrt hs0
  have hall := ((((hasDerivAt_pow 2 ρ).const_mul a).div_const 2).sub
    (((hasDerivAt_pow 2 ρ).div_const 2).mul hac)).add (hsqrt.div_const 2)
  convert hall using 1
  · funext r; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
  have hpos : 0 < ρ ^ 2 - 1 := by nlinarith
  have hs1 : √(1 - (1 / ρ) ^ 2) = √(ρ ^ 2 - 1) / ρ := by
    rw [show 1 - (1 / ρ) ^ 2 = (ρ ^ 2 - 1) / ρ ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hρ0.le]
  have hs : 0 < √(ρ ^ 2 - 1) := Real.sqrt_pos.2 hpos
  simp only [Function.comp_apply]
  rw [hs1]
  field_simp
  ring

/-- `∫₁^R ρ (π/k - arccos(1/ρ)) dρ = (tan(π/k) - π/k)/2` for `R = sec(π/k)`. -/
lemma integral_one_secR {k : ℕ} (hk : 3 ≤ k) :
    ∫ ρ in (1 : ℝ)..Poly.secR k, ρ * (π / k - arccos (1 / ρ)) = (tan (π / k) - π / k) / 2 := by
  have hR := Poly.one_le_secR hk
  have hc := Poly.cos_pi_div_pos hk
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set G := fun r : ℝ => π / k * r ^ 2 / 2 - r ^ 2 / 2 * arccos (1 / r) + √(r ^ 2 - 1) / 2
  have hcont : ContinuousOn G (Icc 1 (Poly.secR k)) := by
    have : ContinuousOn (fun r : ℝ => arccos (1 / r)) (Icc 1 (Poly.secR k)) :=
      Real.continuous_arccos.comp_continuousOn
        (continuousOn_const.div continuousOn_id fun x hx => (by linarith [hx.1] : (0 : ℝ) < x).ne')
    exact ((continuousOn_const.mul (continuousOn_id.pow 2)).div_const 2).sub
      (((continuousOn_id.pow 2).div_const 2).mul this) |>.add
      ((((continuousOn_id.pow 2).sub continuousOn_const).sqrt).div_const 2)
  have hint : IntervalIntegrable (fun ρ : ℝ => ρ * (π / k - arccos (1 / ρ))) volume 1
      (Poly.secR k) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hR]
    exact continuousOn_id.mul (continuousOn_const.sub
      (Real.continuous_arccos.comp_continuousOn
        (continuousOn_const.div continuousOn_id fun x hx =>
          (by linarith [hx.1] : (0 : ℝ) < x).ne')))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hcont
    (fun x hx => hasDerivAt_G_B _ hx.1) hint]
  have h0 : 0 ≤ π / k := by positivity
  have hpi : π / k ≤ π := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hacR : arccos (1 / Poly.secR k) = π / k := by
    rw [Poly.secR, one_div_one_div, arccos_cos h0 hpi]
  have hsR : √(Poly.secR k ^ 2 - 1) = tan (π / k) := by
    rw [Poly.secR_sq_sub_one hk, Real.sqrt_sq (Poly.tan_pos_of_three hk).le]
  simp only [G, hacR, hsR, div_one, arccos_one, one_pow, sub_self, Real.sqrt_zero]
  ring

lemma arccos_le_of_le_secR {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ Poly.secR k) :
    arccos (1 / ρ) ≤ π / k := by
  have hc := Poly.cos_pi_div_pos hk
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 : 0 ≤ π / k := by positivity
  have hpi : π / k ≤ π := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  have h1 : cos (π / k) ≤ 1 / ρ := by
    rw [Poly.secR, le_div_iff₀ hc] at hρ
    rw [le_div_iff₀ hρ0]; linarith
  calc arccos (1 / ρ) ≤ arccos (cos (π / k)) := arccos_le_arccos h1
    _ = π / k := arccos_cos h0 hpi

lemma lt_arccos_of_secR_lt {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : Poly.secR k < ρ) :
    π / k < arccos (1 / ρ) := by
  have hc := Poly.cos_pi_div_pos hk
  have hR := Poly.one_le_secR hk
  have hρ0 : 0 < ρ := by linarith
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 1 / ρ < cos (π / k) := by
    rw [Poly.secR, div_lt_iff₀ hc] at hρ
    rw [div_lt_iff₀ hρ0]; linarith
  have h0 : 0 ≤ π / k := by positivity
  have hpi : π / k ≤ π := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  rw [← arccos_cos h0 hpi]
  have : 0 < 1 / ρ := by positivity
  exact arccos_lt_arccos (by linarith) h1 (cos_le_one _)

/-- The radial integral `∫₀^∞ ρ · |{θ : ρe^{iθ} ∈ P_k}| dρ = k tan(π/k)`. -/
lemma lintegral_radial {k : ℕ} (hk : 3 ≤ k) :
    ∫⁻ ρ in Ioi 0, ENNReal.ofReal (ρ * (k * (2 * (π / k - arccos (1 / ρ))))) =
      ENNReal.ofReal (Poly.area k) := by
  have hR := Poly.one_le_secR hk
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set R := Poly.secR k
  set h : ℝ → ℝ := fun ρ => ρ * (k * (2 * (π / k - arccos (1 / ρ)))) with hh
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ R),
    lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
  have hout : ∫⁻ ρ in Ioi R, ENNReal.ofReal (h ρ) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun ρ hρ => ?_,
      lintegral_zero]
    have := lt_arccos_of_secR_lt hk hρ
    have hρ0 : 0 < ρ := by have := hρ.out; linarith
    rw [ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hρ0.le (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by linarith))
  rw [hout, add_zero]
  have hcont1 : ContinuousOn h (Icc 1 R) :=
    continuousOn_id.mul (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.sub
      (Real.continuous_arccos.comp_continuousOn
        (continuousOn_const.div continuousOn_id fun x hx =>
          (by linarith [hx.1] : (0 : ℝ) < x).ne')))))
  have heq0 : EqOn h (fun ρ => ρ * (k * (2 * (π / k)))) (Icc 0 1) := by
    intro ρ hρ
    rcases eq_or_lt_of_le hρ.1 with h0 | h0
    · simp [hh, ← h0]
    · have : arccos (1 / ρ) = 0 := arccos_eq_zero.2 (by rw [le_div_iff₀ h0]; linarith [hρ.2])
      simp only [hh, this, sub_zero]
  have hi1 : IntegrableOn h (Ioc 0 1) :=
    ((continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (heq0.symm.mono Ioc_subset_Icc_self) measurableSet_Ioc
  have hi2 : IntegrableOn h (Ioc 1 R) :=
    (hcont1.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint : IntegrableOn h (Ioc 0 R) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hR]; exact hi1.union hi2
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] h := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun ρ hρ => ?_)
    have := arccos_le_of_le_secR hk hρ.1 hρ.2
    simp only [Pi.zero_apply, hh]
    have : 0 ≤ π / k - arccos (1 / ρ) := by linarith
    exact mul_nonneg hρ.1.le (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hi1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).2 hi2)]
  rw [intervalIntegral.integral_congr (g := fun ρ => ρ * (k * (2 * (π / k))))
    (by rw [Set.uIcc_of_le zero_le_one]; exact heq0)]
  rw [intervalIntegral.integral_congr (a := 1) (b := R) (f := h)
    (g := fun ρ => (2 * k) * (ρ * (π / k - arccos (1 / ρ)))) (fun ρ _ => by simp only [hh]; ring)]
  rw [intervalIntegral.integral_const_mul, integral_one_secR hk,
    intervalIntegral.integral_mul_const,
    integral_id, Poly.area]
  field_simp
  ring

lemma isClosed_poly_B (k : ℕ) : IsClosed (poly k) := by
  have : poly k = ⋂ j ∈ Finset.range k, {z : ℂ | (z * (starRingEnd ℂ) (nrm k j)).re ≤ 1} := by
    ext z; simp [poly]
  rw [this]
  exact isClosed_biInter fun j _ => isClosed_le (by fun_prop) continuous_const

/-- **Area of the regular `k`-gon.** `|P_k| = k tan(π/k)`. -/
theorem volume_poly {k : ℕ} (hk : 3 ≤ k) :
    volume (poly k) = ENNReal.ofReal (Poly.area k) := by
  have hk0 : 0 < k := by omega
  have hmeas : MeasurableSet (poly k) := (isClosed_poly_B k).measurableSet
  have hsymm : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  have hpt : ∀ p : ℝ × ℝ, (poly k).indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) =
      (ang k p.1).indicator 1 p.2 := by
    intro p
    have e : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    rw [e]
    by_cases h : p.2 ∈ ang k p.1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_poly_polar hk0 _ _).2 h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
        (fun h' => h ((mem_poly_polar hk0 _ _).1 h'))]
  have hf : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • (poly k).indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) := by
    refine (ENNReal.measurable_ofReal.comp measurable_fst).smul
      ((measurable_one.indicator hmeas).comp ?_)
    rw [hsymm]; fun_prop
  rw [← lintegral_indicator_one hmeas, ← Complex.lintegral_comp_polarCoord_symm,
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ hf.aemeasurable, ← lintegral_radial hk]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  simp only [hpt, smul_eq_mul]
  rw [lintegral_const_mul _ (measurable_one.indicator (isClosed_ang k ρ).measurableSet),
    lintegral_indicator_one (isClosed_ang k ρ).measurableSet,
    Measure.restrict_apply (isClosed_ang k ρ).measurableSet, volume_ang hk hρ,
    ← ENNReal.ofReal_mul (le_of_lt hρ)]

end AreaB

section CpC
lemma measurableSet_cpSet (m : ℕ) (x : ℂ) :
    MeasurableSet {y : Fin m → ℂ | (∀ i, y i ∈ disc) ∧ x - ∑ i, y i ∈ disc} := by
  apply IsClosed.measurableSet
  simp only [disc, Metric.mem_closedBall, dist_zero_right, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- `cp m` is measurable. -/
lemma measurable_cp (m : ℕ) : Measurable (cp m) := by
  have hS : MeasurableSet
      {p : ℂ × (Fin m → ℂ) | (∀ i, p.2 i ∈ disc) ∧ p.1 - ∑ i, p.2 i ∈ disc} := by
    apply IsClosed.measurableSet
    simp only [disc, Metric.mem_closedBall, dist_zero_right, ofPred_and, ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)
  exact measurable_measure_prodMk_left hS

/-- `cp m x ≤ |B|^m`. -/
lemma cp_le (m : ℕ) (x : ℂ) : cp m x ≤ volume disc ^ m := by
  calc cp m x ≤ volume (Set.univ.pi fun _ : Fin m => disc) :=
        measure_mono fun y hy => fun i _ => hy.1 i
    _ = volume disc ^ m := by
        rw [volume_pi, Measure.pi_pi]; simp

lemma volume_disc : volume disc = ENNReal.ofReal π := by
  simp [disc, Complex.volume_closedBall, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- `cp m x` is finite. -/
lemma cp_ne_top (m : ℕ) (x : ℂ) : cp m x ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [volume_disc]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (cp_le m x)

/-- Rotation invariance of `cp`. -/
lemma cp_rot (m : ℕ) {u : ℂ} (hu : ‖u‖ = 1) (x : ℂ) : cp m (u * x) = cp m x := by
  let U : Circle := ⟨u, mem_sphere_zero_iff_norm.2 hu⟩
  have hR : MeasurePreserving (fun y : Fin m → ℂ => fun i => u * y i) := by
    have := (rotation U).measurePreserving
    exact volume_preserving_pi fun _ => this
  unfold cp
  rw [← hR.measure_preimage (measurableSet_cpSet m (u * x)).nullMeasurableSet]
  congr 1
  ext y
  simp only [disc, Metric.mem_closedBall, dist_zero_right, mem_preimage, mem_ofPred_eq,
    norm_mul, hu, one_mul, ← Finset.mul_sum, ← mul_sub]

/-- `cp m` is even. -/
lemma cp_neg (m : ℕ) (x : ℂ) : cp m (-x) = cp m x := by
  simpa using cp_rot m (u := -1) (by simp) x

/-- `cp m` is radial. -/
lemma cp_radial (m : ℕ) (x : ℂ) : cp m x = cp m (‖x‖ : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : (‖x‖ : ℂ) ≠ 0 := by simpa using hx
  have hu : ‖(starRingEnd ℂ) (x / ‖x‖)‖ = 1 := by
    rw [Complex.norm_conj, norm_div]; simp [hx]
  rw [← cp_rot m hu x]
  congr 1
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  field_simp
  push_cast; ring

/-- `λ₁ = 1_B`. -/
lemma cp_zero_eq (x : ℂ) : cp 0 x = disc.indicator 1 x := by
  unfold cp
  by_cases hx : x ∈ disc
  · simp [hx, volume_pi]
  · simp [hx]

/-- `λ₁(0) = 1`. -/
lemma cp_zero_zero : cp 0 0 = 1 := by
  rw [cp_zero_eq]; simp [disc]

/-- The recursion `λ_{m+2}(x) = ∫_B λ_{m+1}(x - y) dy` (Fubini). -/
lemma cp_succ (m : ℕ) (x : ℂ) : cp (m + 1) x = ∫⁻ y in disc, cp m (x - y) := by
  have hP := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℂ)) 0
  set T : Set (ℂ × (Fin m → ℂ)) :=
    {p | p.1 ∈ disc ∧ (∀ i, p.2 i ∈ disc) ∧ x - (p.1 + ∑ i, p.2 i) ∈ disc} with hTdef
  have hT : MeasurableSet T := by
    apply IsClosed.measurableSet
    simp only [hTdef, disc, Metric.mem_closedBall, dist_zero_right, ofPred_and, ofPred_forall]
    exact (isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const))
  have hS : {y : Fin (m + 1) → ℂ | (∀ i, y i ∈ disc) ∧ x - ∑ i, y i ∈ disc} =
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0 ⁻¹' T := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, hTdef, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply, Fin.forall_fin_succ, Fin.sum_univ_succ,
      and_assoc]
    rfl
  unfold cp
  rw [hS, volume_pi, hP.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT,
    ← lintegral_indicator (s := disc) measurableSet_closedBall, ← volume_pi]
  refine lintegral_congr fun a => ?_
  by_cases ha : a ∈ disc
  · rw [indicator_of_mem ha]
    congr 1
    ext z
    simp [hTdef, ha, sub_add_eq_sub_sub]
  · rw [indicator_of_notMem ha]
    simp [hTdef, ha]

/-- `λ₂(x)` as the area of `B ∩ (x - B)`. -/
lemma cp_one_eq_vol (x : ℂ) : cp 1 x = volume {z : ℂ | ‖z‖ ≤ 1 ∧ ‖x - z‖ ≤ 1} := by
  have hP := volume_preserving_funUnique (Fin 1) ℂ
  have hT : MeasurableSet {z : ℂ | ‖z‖ ≤ 1 ∧ ‖x - z‖ ≤ 1} := by
    apply IsClosed.measurableSet
    simp only [ofPred_and]
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)
  unfold cp
  rw [← hP.measure_preimage hT.nullMeasurableSet]
  congr 1
  ext y
  simp [disc, Fin.forall_fin_one]

lemma volume_sq_le (c : ℝ) : volume {b : ℝ | b ^ 2 ≤ c} = ENNReal.ofReal (2 * √c) := by
  rcases lt_or_ge c 0 with hc | hc
  · have : {b : ℝ | b ^ 2 ≤ c} = ∅ := by
      ext b; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      nlinarith [sq_nonneg b]
    rw [this, Real.sqrt_eq_zero'.2 hc.le]; simp
  · have : {b : ℝ | b ^ 2 ≤ c} = Icc (-√c) (√c) := by
      ext b; simp [Real.sq_le hc]
    rw [this, Real.volume_Icc]; ring_nf

lemma hasDerivAt_G_C {t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    HasDerivAt (fun t => t * √(1 - t ^ 2) + arcsin t) (2 * √(1 - t ^ 2)) t := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 hpos
  have h := ((hasDerivAt_id' t).mul (((hasDerivAt_pow 2 t).const_sub 1).sqrt
    hpos.ne')).add (Real.hasDerivAt_arcsin (by linarith) (by linarith))
  convert h using 1
  have hsq : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hpos.le
  field_simp
  rw [hsq]; push_cast; ring

lemma integral_two_sqrt {a b : ℝ} (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ 1) :
    ∫ t in a..b, 2 * √(1 - t ^ 2) =
      (b * √(1 - b ^ 2) + arcsin b) - (a * √(1 - a ^ 2) + arcsin a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact (by fun_prop : Continuous fun t : ℝ => t * √(1 - t ^ 2)).continuousOn.add
      Real.continuous_arcsin.continuousOn
  · intro t ht
    exact hasDerivAt_G_C (by linarith [ht.1]) (by linarith [ht.2])
  · exact (by fun_prop : Continuous fun t : ℝ => 2 * √(1 - t ^ 2)).intervalIntegrable _ _

lemma integral_lensFun {d : ℝ} (h0 : 0 ≤ d) (h2 : d ≤ 2) :
    ∫ a, 2 * √(min (1 - a ^ 2) (1 - (a - d) ^ 2)) = Mixes.Poly.lens d := by
  set f : ℝ → ℝ := fun a => 2 * √(min (1 - a ^ 2) (1 - (a - d) ^ 2)) with hf
  have hfc : Continuous f := by fun_prop
  have h1 : ∫ a, f a = ∫ a in (d - 1)..1, f a := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at ha
    simp only [hf, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    apply Real.sqrt_eq_zero'.2
    rcases ha with ha | ha
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans (by nlinarith)
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (b := d / 2)
    (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
  have e1 : ∫ a in (d - 1)..(d / 2), f a = ∫ a in (d - 1)..(d / 2), 2 * √(1 - (a - d) ^ 2) := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [uIcc_of_le (by linarith)] at ha
    simp only [hf]
    rw [min_eq_right (by nlinarith [ha.2])]
  have e2 : ∫ a in (d / 2)..1, f a = ∫ a in (d / 2)..1, 2 * √(1 - a ^ 2) := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [uIcc_of_le (by linarith)] at ha
    simp only [hf]
    rw [min_eq_left (by nlinarith [ha.1])]
  rw [e1, e2, intervalIntegral.integral_comp_sub_right (fun t => 2 * √(1 - t ^ 2)) d,
    integral_two_sqrt (by linarith) (by linarith) (by linarith),
    integral_two_sqrt (by linarith) (by linarith) le_rfl]
  have hs : √(4 - d ^ 2) = 2 * √(1 - (d / 2) ^ 2) := by
    rw [show 4 - d ^ 2 = 2 ^ 2 * (1 - (d / 2) ^ 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  simp only [Mixes.Poly.lens, hs, arccos_eq_pi_div_two_sub_arcsin, show d - 1 - d = -1 by ring,
    show d / 2 - d = -(d / 2) by ring, arcsin_neg, arcsin_one, neg_sq]
  norm_num
  ring

/-- Area of the lens `B ∩ (d + B)`, `0 ≤ d ≤ 2`. -/
lemma volume_lens {d : ℝ} (h0 : 0 ≤ d) (h2 : d ≤ 2) :
    volume {z : ℂ | ‖z‖ ≤ 1 ∧ ‖(d : ℂ) - z‖ ≤ 1} = ENNReal.ofReal (Mixes.Poly.lens d) := by
  set T : Set (ℝ × ℝ) := {p | p.2 ^ 2 ≤ min (1 - p.1 ^ 2) (1 - (p.1 - d) ^ 2)} with hTdef
  have hT : MeasurableSet T := (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hS : {z : ℂ | ‖z‖ ≤ 1 ∧ ‖(d : ℂ) - z‖ ≤ 1} = Complex.measurableEquivRealProd ⁻¹' T := by
    ext z
    have e1 : ‖z‖ ≤ 1 ↔ ‖z‖ ^ 2 ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).symm
    have e2 : ‖(d : ℂ) - z‖ ≤ 1 ↔ ‖(d : ℂ) - z‖ ^ 2 ≤ 1 :=
      (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).symm
    simp only [mem_ofPred_eq, mem_preimage, hTdef, Complex.measurableEquivRealProd_apply,
      le_min_iff,
      e1, e2, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  rw [hS, Complex.volume_preserving_equiv_real_prod.measure_preimage hT.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hT]
  simp only [hTdef, preimage_ofPred_eq, volume_sq_le]
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_lensFun h0 h2]
  · refine (by fun_prop : Continuous fun a : ℝ =>
      2 * √(min (1 - a ^ 2) (1 - (a - d) ^ 2))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun a ha => ?_
    simp only [mem_Icc, not_and_or, not_le] at ha
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact Real.sqrt_eq_zero'.2 ((min_le_left _ _).trans (by rcases ha with ha | ha <;> nlinarith))
  · exact Filter.Eventually.of_forall fun a => by positivity

/-- `λ₂(x) = lens ‖x‖` for `‖x‖ ≤ 2`. -/
lemma cp_one_eq {x : ℂ} (hx : ‖x‖ ≤ 2) : cp 1 x = ENNReal.ofReal (Mixes.Poly.lens ‖x‖) := by
  rw [cp_radial, cp_one_eq_vol, volume_lens (norm_nonneg _) hx]

/-- `λ₂(x) = 0` for `‖x‖ > 2`. -/
lemma cp_one_eq_zero {x : ℂ} (hx : 2 < ‖x‖) : cp 1 x = 0 := by
  rw [cp_one_eq_vol]
  rw [show {z : ℂ | ‖z‖ ≤ 1 ∧ ‖x - z‖ ≤ 1} = ∅ from ?_, measure_empty]
  ext z
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro hz
  have := norm_sub_norm_le x z
  linarith

/-- `λ₂(0) = π`. -/
lemma cp_one_zero : cp 1 0 = ENNReal.ofReal π := by
  have h : Mixes.Poly.lens 0 = π := by simp [Mixes.Poly.lens]; ring
  rw [cp_one_eq (by simp), norm_zero, h]

lemma lens_nonneg {d : ℝ} (h0 : 0 ≤ d) (h2 : d ≤ 2) : 0 ≤ Mixes.Poly.lens d := by
  rw [← integral_lensFun h0 h2]
  exact integral_nonneg fun a => by positivity

lemma hasDerivAt_H {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    HasDerivAt (fun r => (r ^ 2 - 1) * arccos (r / 2) - √(4 - r ^ 2) * (r ^ 3 + 2 * r) / 8)
      (r * Mixes.Poly.lens r) r := by
  have hpos : 0 < 4 - r ^ 2 := by nlinarith
  have hq : √(1 - (r / 2) ^ 2) = √(4 - r ^ 2) / 2 := by
    rw [show 4 - r ^ 2 = 2 ^ 2 * (1 - (r / 2) ^ 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]; ring
  have hs : 0 < √(4 - r ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : √(4 - r ^ 2) ^ 2 = 4 - r ^ 2 := Real.sq_sqrt hpos.le
  have hA := (Real.hasDerivAt_arccos (x := r / 2) (by linarith) (by linarith)).comp r
    ((hasDerivAt_id' r).div_const 2)
  have h := (((hasDerivAt_pow 2 r).sub_const 1).mul hA).sub
    (((((hasDerivAt_pow 2 r).const_sub 4).sqrt hpos.ne').mul
      ((hasDerivAt_pow 3 r).add ((hasDerivAt_id' r).const_mul 2))).div_const 8)
  convert h using 1
  · funext x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Function.comp_apply]
  simp only [Function.comp_apply, Pi.add_apply]
  rw [hq, Mixes.Poly.lens]
  field_simp
  push_cast; ring_nf; rw [hsq]; ring

lemma integral_r_lens : ∫ r in (0 : ℝ)..1, r * Mixes.Poly.lens r = π / 2 - 3 * √3 / 8 := by
  have hc : Continuous fun r : ℝ => r * Mixes.Poly.lens r := by
    unfold Mixes.Poly.lens; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (f := fun r => (r ^ 2 - 1) * arccos (r / 2) - √(4 - r ^ 2) * (r ^ 3 + 2 * r) / 8)
    (by fun_prop) (fun r hr => hasDerivAt_H hr.1 hr.2) (hc.intervalIntegrable _ _)]
  norm_num
  ring

/-- `λ₃(0) = π² - (3/4)√3 π`. -/
lemma cp_two_zero : cp 2 0 = ENNReal.ofReal (π ^ 2 - 3 / 4 * √3 * π) := by
  set g : ℝ → ℝ≥0∞ := (Iic (1 : ℝ)).indicator fun r => ENNReal.ofReal (r * Mixes.Poly.lens r)
    with hgdef
  have hlc : Continuous Mixes.Poly.lens := by unfold Mixes.Poly.lens; fun_prop
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun r : ℝ =>
      r * Mixes.Poly.lens r).measurable).indicator measurableSet_Iic
  have step1 : cp 2 0 = ∫⁻ y, disc.indicator (fun y => ENNReal.ofReal (Mixes.Poly.lens ‖y‖)) y := by
    rw [cp_succ, lintegral_indicator (s := disc) measurableSet_closedBall]
    refine setLIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
    have hy' : ‖y‖ ≤ 1 := by simpa [disc] using hy
    rw [zero_sub, cp_neg, cp_one_eq (by linarith)]
  have step2 : ∫⁻ y, disc.indicator (fun y => ENNReal.ofReal (Mixes.Poly.lens ‖y‖)) y =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g p.1 := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have h0 : 0 < p.1 := hp.1
    by_cases h1 : p.1 ≤ 1
    · simp [hgdef, disc, h1, abs_of_pos h0, ENNReal.ofReal_mul h0.le]
    · simp [hgdef, disc, h1, abs_of_pos h0]
  have step3 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g p.1 =
      (∫⁻ r in Ioi (0 : ℝ), g r) * ENNReal.ofReal (2 * π) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod (fun p : ℝ × ℝ => g p.1) (hg.comp measurable_fst).aemeasurable]
    simp only [setLIntegral_const, Real.volume_Ioo]
    rw [lintegral_mul_const _ hg]
    congr 2; ring
  have step4 : ∫⁻ r in Ioi (0 : ℝ), g r = ENNReal.ofReal (π / 2 - 3 * √3 / 8) := by
    rw [hgdef, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi, ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le
      zero_le_one, integral_r_lens]
    · exact (by fun_prop : Continuous fun r : ℝ => r * Mixes.Poly.lens r).integrableOn_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      exact mul_nonneg hr.1.le (lens_nonneg hr.1.le (by linarith [hr.2]))
  rw [step1, step2, step3, step4, ← ENNReal.ofReal_mul]
  · congr 1; ring
  · have : √3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith [pi_gt_three]

end CpC

section LamD

/-! ## The Lebesgue measure on tuples with sum `0` -/

/-- Tuples `x` with `x 0 ∈ K0`, the other coordinates in the disc, and sum `0`. -/
def tupSet (m : ℕ) (K0 : Set ℂ) : Set (Fin (m + 3) → ℂ) :=
  {x | x 0 ∈ K0 ∧ (∀ i, i ≠ 0 → x i ∈ disc) ∧ ∑ i, x i = 0}

/-- `y ↦ (-∑ y, y)`. -/
def consNeg (m : ℕ) (y : Fin (m + 2) → ℂ) : Fin (m + 3) → ℂ :=
  Fin.cons (α := fun _ => ℂ) (-∑ i, y i) y

/-- The Lebesgue measure on the tuples of `tupSet m K0`, through the last `m + 2` coordinates. -/
def lamG (m : ℕ) (K0 : Set ℂ) : Measure (Fin (m + 3) → ℂ) :=
  ((volume : Measure (Fin (m + 2) → ℂ)).restrict
    {y | (∀ i, y i ∈ disc) ∧ -∑ i, y i ∈ K0}).map (consNeg m)

lemma measurableSet_disc : MeasurableSet disc := Metric.isClosed_closedBall.measurableSet

lemma measurable_sumC {k : ℕ} : Measurable (fun y : Fin k → ℂ => ∑ i, y i) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

lemma measurableSet_allDisc {k : ℕ} : MeasurableSet {y : Fin k → ℂ | ∀ i, y i ∈ disc} := by
  rw [ofPred_forall]; exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_disc

lemma measurable_consNeg (m : ℕ) : Measurable (consNeg m) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [consNeg, Fin.cons_zero]; exact measurable_sumC.neg
  · simpa [consNeg] using measurable_pi_apply j

/-- The set on which `lamG` lives (in the `y` coordinates). -/
def ySet (m : ℕ) (K0 : Set ℂ) : Set (Fin (m + 2) → ℂ) := {y | (∀ i, y i ∈ disc) ∧ -∑ i, y i ∈ K0}

lemma measurableSet_ySet (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) :
    MeasurableSet (ySet m K0) :=
  measurableSet_allDisc.inter (measurable_sumC.neg hK0)

/-- `cp m` is measurable (a section of a measurable set). -/
lemma measurable_cp_D (m : ℕ) : Measurable (cp m) := by
  have hs : MeasurableSet {q : ℂ × (Fin m → ℂ) | (∀ i, q.2 i ∈ disc) ∧ q.1 - ∑ i, q.2 i ∈ disc} :=
    (measurable_snd measurableSet_allDisc).inter
      ((measurable_fst.sub (measurable_sumC.comp measurable_snd)) measurableSet_disc)
  exact measurable_measure_prodMk_left hs

@[simp] lemma consNeg_zero (m : ℕ) (y : Fin (m + 2) → ℂ) : consNeg m y 0 = -∑ i, y i := rfl

@[simp] lemma consNeg_succ (m : ℕ) (y : Fin (m + 2) → ℂ) (i : Fin (m + 2)) :
    consNeg m y i.succ = y i := rfl

lemma sum_consNeg (m : ℕ) (y : Fin (m + 2) → ℂ) : ∑ i, consNeg m y i = 0 := by
  rw [Fin.sum_univ_succ]; simp

lemma lamG_apply (m : ℕ) {K0 : Set ℂ} {S : Set (Fin (m + 3) → ℂ)} (hS : MeasurableSet S) :
    lamG m K0 S = volume (consNeg m ⁻¹' S ∩ ySet m K0) := by
  rw [lamG, Measure.map_apply (measurable_consNeg m) hS,
    Measure.restrict_apply (measurable_consNeg m hS)]; rfl

lemma measurableSet_tupSet (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) :
    MeasurableSet (tupSet m K0) := by
  change MeasurableSet ({x : Fin (m + 3) → ℂ | x 0 ∈ K0} ∩
    ({x | ∀ i, i ≠ 0 → x i ∈ disc} ∩ {x | ∑ i, x i = 0}))
  have h0 : Measurable fun x : Fin (m + 3) → ℂ => x 0 := measurable_pi_apply 0
  refine (h0 hK0).inter (MeasurableSet.inter ?_ ?_)
  · rw [ofPred_forall]; refine MeasurableSet.iInter fun i => ?_
    rw [ofPred_forall]; exact MeasurableSet.iInter fun _ => measurable_pi_apply i measurableSet_disc
  · exact measurable_sumC (measurableSet_singleton 0)

/-- `lamG m K0` is concentrated on `tupSet m K0`. -/
lemma lamG_tupSet (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) :
    lamG m K0 (tupSet m K0)ᶜ = 0 := by
  rw [lamG_apply m (measurableSet_tupSet m hK0).compl]
  convert measure_empty (μ := (volume : Measure (Fin (m + 2) → ℂ)))
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
  rintro ⟨hc, h1, h2⟩
  refine hc ⟨h2, fun i hi => ?_, sum_consNeg m y⟩
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
  exact h1 j

/-- `lamG m K0` is concentrated on `𝒯_{m+3}(K)` for `K0, B ⊆ K`. -/
lemma lamG_tuples (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) {K : Set ℂ} (h0 : K0 ⊆ K)
    (hB : disc ⊆ K) (_hK : MeasurableSet K) : lamG m K0 (Room.tuples (m + 3) K 0)ᶜ = 0 := by
  refine measure_mono_null (compl_subset_compl.2 fun x hx => ⟨fun i => ?_, ?_⟩)
    (lamG_tupSet m hK0)
  · by_cases hi : i = 0
    · subst hi; exact h0 hx.1
    · exact hB (hx.2.1 i hi)
  · rw [hx.2.2, smul_zero]

instance (m : ℕ) (K0 : Set ℂ) : IsFiniteMeasure (lamG m K0) := by
  have : IsFiniteMeasure ((volume : Measure (Fin (m + 2) → ℂ)).restrict
      {y | (∀ i, y i ∈ disc) ∧ -∑ i, y i ∈ K0}) := by
    refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top ?_ (measure_mono (t := Set.univ.pi
      fun _ => disc) fun y hy i _ => hy.1 i))
    rw [volume_pi_pi]
    exact ENNReal.prod_ne_top fun i _ =>
      (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  rw [lamG]; infer_instance

lemma isFiniteMeasure_lamG (m : ℕ) (K0 : Set ℂ) : IsFiniteMeasure (lamG m K0) := inferInstance

/-! ## Symmetries -/

/-- `y ↦ y ∘ τ` as a measurable equivalence. -/
def permME {k : ℕ} (τ : Equiv.Perm (Fin k)) : (Fin k → ℂ) ≃ᵐ (Fin k → ℂ) where
  toFun y := y ∘ τ
  invFun y := y ∘ τ.symm
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  measurable_toFun := Room.measurable_perm τ
  measurable_invFun := Room.measurable_perm τ.symm

lemma permME_apply {k : ℕ} (τ : Equiv.Perm (Fin k)) (y : Fin k → ℂ) : permME τ y = y ∘ τ := rfl

lemma mp_permME {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    MeasurePreserving (permME τ) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin k => ℂ) τ.symm using 1
  ext y i
  simp [permME_apply, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

lemma reflect0_reflect0 {k : ℕ} (y : Fin (k + 1) → ℂ) : Room.reflect0 (Room.reflect0 y) = y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Room.reflect0, Fin.sum_univ_succ (f := y), Fin.tail]
  · simp [Room.reflect0, Fin.tail]

lemma measurable_reflect0 {k : ℕ} : Measurable (Room.reflect0 (E := ℂ) (m := k)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Room.reflect0, Fin.cons_zero]; exact measurable_sumC.neg
  · simp only [Room.reflect0, Fin.cons_succ, Fin.tail]; exact measurable_pi_apply _

/-- `reflect0` as a measurable equivalence (an involution). -/
def reflME (k : ℕ) : (Fin (k + 1) → ℂ) ≃ᵐ (Fin (k + 1) → ℂ) where
  toFun := Room.reflect0
  invFun := Room.reflect0
  left_inv := reflect0_reflect0
  right_inv := reflect0_reflect0
  measurable_toFun := measurable_reflect0
  measurable_invFun := measurable_reflect0

lemma mp_reflME (k : ℕ) : MeasurePreserving (reflME k) volume volume :=
  Room.measurePreserving_reflect0 (volume : Measure ℂ)

lemma lamG_map_of (m : ℕ) (K0 : Set ℂ) (e : (Fin (m + 2) → ℂ) ≃ᵐ (Fin (m + 2) → ℂ))
    (he : MeasurePreserving e volume volume) (hS : e ⁻¹' ySet m K0 = ySet m K0)
    {g : (Fin (m + 3) → ℂ) → Fin (m + 3) → ℂ} (hg : Measurable g)
    (hc : ∀ y, g (consNeg m y) = consNeg m (e y)) : (lamG m K0).map g = lamG m K0 := by
  rw [lamG, Measure.map_map hg (measurable_consNeg m)]
  have : g ∘ consNeg m = consNeg m ∘ e := funext hc
  rw [this, ← Measure.map_map (measurable_consNeg m) e.measurable]
  congr 1
  have := (he.restrict_preimage_emb e.measurableEmbedding (ySet m K0)).map_eq
  rw [hS] at this; exact this

/-- The permutation of `Fin (k + 1)` induced by a permutation of `Fin (k + 2)` fixing `0`. -/
def predPerm {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) (hσ : σ 0 = 0) : Equiv.Perm (Fin (k + 1)) where
  toFun i := (σ i.succ).pred (by
    intro h; rw [← hσ] at h; exact Fin.succ_ne_zero i (σ.injective h))
  invFun i := (σ.symm i.succ).pred (by
    intro h; rw [Equiv.symm_apply_eq, hσ] at h; exact Fin.succ_ne_zero i h)
  left_inv i := by simp
  right_inv i := by simp

lemma succ_predPerm {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) (hσ : σ 0 = 0) (i : Fin (k + 1)) :
    (predPerm σ hσ i).succ = σ i.succ := by simp [predPerm]

/-- Permutations of the coordinates fixing `0` preserve `lamG`. -/
lemma lamG_perm_fix (m : ℕ) (K0 : Set ℂ) (σ : Equiv.Perm (Fin (m + 3))) (hσ : σ 0 = 0) :
    (lamG m K0).map (fun x => x ∘ σ) = lamG m K0 := by
  refine lamG_map_of m K0 (permME (predPerm σ hσ)) (mp_permME _) ?_ (Room.measurable_perm σ) ?_
  · ext y
    simp only [mem_preimage, ySet, mem_ofPred_eq, permME_apply, Function.comp_apply,
      Equiv.sum_comp (predPerm σ hσ) y]
    rw [(predPerm σ hσ).forall_congr_right (q := fun i => y i ∈ disc)]
  · intro y
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hσ, permME_apply, Equiv.sum_comp (predPerm σ hσ) y]
    · simp only [Function.comp_apply, ← succ_predPerm σ hσ, consNeg_succ, permME_apply]

lemma sum_reflect0 {k : ℕ} (y : Fin (k + 1) → ℂ) : ∑ i, Room.reflect0 y i = -y 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Room.reflect0, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  rw [Fin.sum_univ_succ (f := y)]; ring

lemma lamG_swap01 (m : ℕ) :
    (lamG m disc).map (fun x => x ∘ Equiv.swap 0 1) = lamG m disc := by
  refine lamG_map_of m disc (reflME _) (mp_reflME _) ?_ (Room.measurable_perm _) ?_
  · ext y
    simp only [mem_preimage, ySet, mem_ofPred_eq]
    change ((∀ i, Room.reflect0 y i ∈ disc) ∧ -∑ i, Room.reflect0 y i ∈ disc) ↔ _
    rw [sum_reflect0, neg_neg, Fin.forall_fin_succ, Fin.forall_fin_succ (P := fun i => y i ∈ disc)]
    simp only [Room.reflect0, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    tauto
  · intro y
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change consNeg m y 1 = -∑ i, Room.reflect0 y i
      rw [sum_reflect0, neg_neg]; rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · change consNeg m y _ = consNeg m (Room.reflect0 y) _
        simp [Room.reflect0]; rfl
      · have : Equiv.swap (0 : Fin (m + 3)) 1 k.succ.succ = k.succ.succ :=
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by
            intro h; exact Fin.succ_ne_zero k (Fin.succ_injective _ h))
        change consNeg m y _ = consNeg m (Room.reflect0 y) _
        rw [this, consNeg_succ, consNeg_succ]; rfl

/-- `lamG m disc` is invariant under all permutations of the coordinates. -/
lemma permInvariant_lamG (m : ℕ) : Room.PermInvariant (lamG m disc) := by
  set G : Set (Equiv.Perm (Fin (m + 3))) :=
    {σ | (lamG m disc).map (fun x => x ∘ σ) = lamG m disc} with hG
  have hmul : ∀ σ ∈ G, ∀ τ ∈ G, σ * τ ∈ G := by
    intro σ hσ τ hτ
    simp only [hG, mem_ofPred_eq] at hσ hτ ⊢
    conv_rhs => rw [← hτ, ← hσ]
    rw [Measure.map_map (Room.measurable_perm τ) (Room.measurable_perm σ)]
    rfl
  have hfix : ∀ σ : Equiv.Perm (Fin (m + 3)), σ 0 = 0 → σ ∈ G :=
    fun σ hσ => lamG_perm_fix m disc σ hσ
  have h01 : Equiv.swap (0 : Fin (m + 3)) 1 ∈ G := lamG_swap01 m
  have hswap : ∀ j : Fin (m + 3), Equiv.swap 0 j ∈ G := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0; rw [Equiv.swap_self]; exact hfix _ rfl
    by_cases hj1 : j = 1
    · subst hj1; exact h01
    have h : Equiv.swap (0 : Fin (m + 3)) j =
        Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j := by
      have := Equiv.swap_apply_apply (Equiv.swap (1 : Fin (m + 3)) j) 0 1
      rwa [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hj0),
        Equiv.swap_inv] at this
    have hf : Equiv.swap (1 : Fin (m + 3)) j ∈ G :=
      hfix _ (Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hj0))
    rw [h]; exact hmul _ (hmul _ hf _ h01) _ hf
  intro σ
  set a := σ.symm 0
  have hρ : (σ * Equiv.swap 0 a) 0 = 0 := by simp [a]
  have : σ = σ * Equiv.swap 0 a * Equiv.swap 0 a := by simp [mul_assoc]
  show σ ∈ G
  rw [this]; exact hmul _ (hfix _ hρ) _ (hswap a)

/-! ## One- and two-point densities -/

/-- The slice `{z ∈ B^k | c - ∑ z ∈ B}`, of volume `cp k c`. -/
def Tc (k : ℕ) (c : ℂ) : Set (Fin k → ℂ) := {z | (∀ i, z i ∈ disc) ∧ c - ∑ i, z i ∈ disc}

lemma measurableSet_Tc (k : ℕ) (c : ℂ) : MeasurableSet (Tc k c) :=
  measurableSet_allDisc.inter ((measurable_const.sub measurable_sumC) measurableSet_disc)

lemma volume_Tc (k : ℕ) (c : ℂ) : volume (Tc k c) = cp k c := rfl

lemma measurable_cons_right {k : ℕ} (a : ℂ) :
    Measurable (fun z : Fin k → ℂ => (Fin.cons a z : Fin (k + 1) → ℂ)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply j

lemma lintegral_cons {k : ℕ} {f : (Fin (k + 1) → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ a, ∫⁻ z, f (Fin.cons a z) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure ℂ)) 0).symm
  rw [volume_pi, ← h.lintegral_comp hf]
  refine (lintegral_prod _ (hf.comp h.measurable).aemeasurable).trans ?_
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero']
  rfl

lemma indicator_one_iff {α β γ : Type*} {u : Set α} {s : Set β} {t : Set γ} {x : α} {a : β}
    {b : γ} (h : x ∈ u ↔ a ∈ s ∧ b ∈ t) :
    u.indicator (1 : α → ℝ≥0∞) x = s.indicator 1 a * t.indicator 1 b := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;> simp [ha, hb, h]

lemma lintegral_ind_mul {k : ℕ} (c : ℝ≥0∞) (d : ℂ) :
    ∫⁻ z : Fin k → ℂ, c * (Tc k d).indicator 1 z = c * cp k d := by
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_Tc k d)),
    lintegral_indicator_one (measurableSet_Tc k d), volume_Tc]

lemma sum_cons' {k : ℕ} (a : ℂ) (z : Fin k → ℂ) :
    ∑ i, (Fin.cons a z : Fin (k + 1) → ℂ) i = a + ∑ i, z i := Fin.sum_cons a z

lemma mem_zero_iff (m : ℕ) (K0 A : Set ℂ) (a : ℂ) (z : Fin (m + 1) → ℂ) :
    Room.reflect0 (Fin.cons a z : Fin (m + 2) → ℂ) ∈
      consNeg m ⁻¹' ((fun x => x 0) ⁻¹' A) ∩ ySet m K0 ↔ a ∈ K0 ∩ A ∧ z ∈ Tc (m + 1) (-a) := by
  have hs := sum_reflect0 (Fin.cons a z : Fin (m + 2) → ℂ)
  simp only [Fin.cons_zero] at hs
  simp only [mem_inter_iff, mem_preimage, consNeg_zero, hs, neg_neg, ySet, mem_ofPred_eq, Tc,
    Fin.forall_fin_succ]
  simp only [Room.reflect0, Fin.cons_zero, Fin.cons_succ, Fin.tail, sum_cons', neg_add']
  tauto

/-- The one-point density of `lamG`: `x 0` has density `1_{K0}(p) cp (m+1) (-p)`. -/
lemma lamG_map_zero (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) :
    (lamG m K0).map (fun x => x 0) =
      volume.withDensity (fun p => K0.indicator 1 p * cp (m + 1) (-p)) := by
  ext A hA
  have hA0 : MeasurableSet ((fun x : Fin (m + 3) → ℂ => x 0) ⁻¹' A) := measurable_pi_apply 0 hA
  have hT := (measurable_consNeg m hA0).inter (measurableSet_ySet m hK0)
  rw [Measure.map_apply (measurable_pi_apply 0) hA, lamG_apply m hA0,
    ← (mp_reflME (m + 1)).measure_preimage hT.nullMeasurableSet,
    ← lintegral_indicator_one ((reflME (m + 1)).measurable hT),
    lintegral_cons (measurable_one.indicator ((reflME (m + 1)).measurable hT)),
    withDensity_apply _ hA, ← lintegral_indicator hA]
  refine lintegral_congr fun a => ?_
  have : ∀ z, (reflME (m + 1) ⁻¹' (consNeg m ⁻¹' ((fun x => x 0) ⁻¹' A) ∩ ySet m K0)).indicator
      1 (Fin.cons a z) = (K0 ∩ A).indicator 1 a * (Tc (m + 1) (-a)).indicator 1 z :=
    fun z => indicator_one_iff (mem_zero_iff m K0 A a z)
  simp only [this, lintegral_ind_mul]
  by_cases ha : a ∈ A <;> by_cases hb : a ∈ K0 <;> simp [ha, hb]

lemma mem_pair_iff (m : ℕ) (K0 : Set ℂ) (A : Set (ℂ × ℂ)) (p q : ℂ) (w : Fin m → ℂ) :
    permME (Equiv.swap 0 1) (reflME (m + 1) (Fin.cons p (Fin.cons q w))) ∈
      consNeg m ⁻¹' ((fun x => (x 0, x 1)) ⁻¹' A) ∩ ySet m K0 ↔
        (p, q) ∈ A ∩ K0 ×ˢ disc ∧ w ∈ Tc m (-p - q) := by
  set v : Fin (m + 2) → ℂ := Fin.cons p (Fin.cons q w)
  set r := Room.reflect0 v with hr
  have h1 : reflME (m + 1) v = r := rfl
  have hsum : ∑ i, (r ∘ Equiv.swap 0 1) i = -p := by
    exact (Equiv.sum_comp (Equiv.swap 0 1) r).trans (by rw [hr, sum_reflect0]; rfl)
  have h0 : consNeg m (r ∘ Equiv.swap 0 1) 0 = p := by rw [consNeg_zero, hsum, neg_neg]
  have h01 : consNeg m (r ∘ Equiv.swap 0 1) 1 = q := by
    change r (Equiv.swap 0 1 0) = q
    rw [Equiv.swap_apply_left]; rfl
  have hall : (∀ i, (r ∘ Equiv.swap 0 1) i ∈ disc) ↔ ∀ i, r i ∈ disc :=
    (Equiv.swap 0 1).forall_congr_right (q := fun i => r i ∈ disc)
  have hv : ∑ i, v i = p + (q + ∑ i, w i) := by simp only [v, sum_cons']
  rw [mem_inter_iff, mem_preimage, mem_preimage, permME_apply, h1, h0, h01]
  change _ ∧ ((∀ i, (r ∘ Equiv.swap 0 1) i ∈ disc) ∧ -∑ i, (r ∘ Equiv.swap 0 1) i ∈ K0) ↔ _
  rw [hall, hsum, neg_neg, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp only [hr, Room.reflect0, Fin.cons_zero, Fin.cons_succ, Fin.tail, v] at hv ⊢
  rw [hv]
  simp only [mem_inter_iff, mem_prod, Tc, mem_ofPred_eq]
  have : -(p + (q + ∑ i, w i)) = -p - q - ∑ i, w i := by ring
  rw [this]
  tauto

/-- The two-point density for the coordinates `0, 1`. -/
lemma lamG_map_pair01 (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) :
    (lamG m K0).map (fun x => (x 0, x 1)) = (volume.prod volume).withDensity
      (Function.uncurry fun p q => K0.indicator 1 p * disc.indicator 1 q * cp m (-p - q)) := by
  have hF : Measurable (fun x : Fin (m + 3) → ℂ => (x 0, x 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  ext A hA
  have hA0 := hF hA
  have hT := (measurable_consNeg m hA0).inter (measurableSet_ySet m hK0)
  set ψ : (Fin (m + 2) → ℂ) → Fin (m + 2) → ℂ := permME (Equiv.swap 0 1) ∘ reflME (m + 1)
    with hψdef
  have hψ : MeasurePreserving ψ volume volume := (mp_permME _).comp (mp_reflME _)
  have hψT : MeasurableSet (ψ ⁻¹' (consNeg m ⁻¹' ((fun x => (x 0, x 1)) ⁻¹' A) ∩ ySet m K0)) :=
    hψ.measurable hT
  have hFd : Measurable (Function.uncurry fun p q : ℂ =>
      K0.indicator (1 : ℂ → ℝ≥0∞) p * disc.indicator 1 q * cp m (-p - q)) :=
    (((measurable_one.indicator hK0).comp measurable_fst).mul
      ((measurable_one.indicator measurableSet_disc).comp measurable_snd)).mul
      ((measurable_cp_D m).comp (measurable_fst.neg.sub measurable_snd))
  rw [Measure.map_apply hF hA, lamG_apply m hA0, ← hψ.measure_preimage hT.nullMeasurableSet,
    ← lintegral_indicator_one hψT, lintegral_cons (measurable_one.indicator hψT),
    withDensity_apply _ hA, ← lintegral_indicator hA,
    lintegral_prod _ (hFd.indicator hA).aemeasurable]
  refine lintegral_congr fun p => ?_
  refine (lintegral_cons ((measurable_one.indicator hψT).comp (measurable_cons_right p))).trans ?_
  refine lintegral_congr fun q => ?_
  have : ∀ w, (ψ ⁻¹' (consNeg m ⁻¹' ((fun x => (x 0, x 1)) ⁻¹' A) ∩ ySet m K0)).indicator 1
      (Fin.cons p (Fin.cons q w) : Fin (m + 2) → ℂ) =
      (A ∩ K0 ×ˢ disc).indicator 1 (p, q) * (Tc m (-p - q)).indicator 1 w :=
    fun w => indicator_one_iff (mem_pair_iff m K0 A p q w)
  simp only [Function.comp_apply, this, lintegral_ind_mul]
  by_cases ha : (p, q) ∈ A <;> by_cases hb : p ∈ K0 <;> by_cases hc : q ∈ disc <;>
    simp [ha, hb, hc]

/-- The two-point density of `lamG`: `(x 0, x j)`, `j ≠ 0`, has density
`1_{K0}(p) 1_B(q) cp m (-p - q)`. -/
lemma lamG_map_pair (m : ℕ) {K0 : Set ℂ} (hK0 : MeasurableSet K0) (j : Fin (m + 3))
    (hj : j ≠ 0) : (lamG m K0).map (fun x => (x 0, x j)) = (volume.prod volume).withDensity
      (Function.uncurry fun p q => K0.indicator 1 p * disc.indicator 1 q * cp m (-p - q)) := by
  have hσ : Equiv.swap (1 : Fin (m + 3)) j 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hj)
  rw [← lamG_map_pair01 m hK0]
  conv_lhs => rw [← lamG_perm_fix m K0 _ hσ]
  rw [Measure.map_map ((measurable_pi_apply 0).prodMk (measurable_pi_apply j))
      (Room.measurable_perm _)]
  congr 1
  funext x
  simp [hσ]

end LamD

section FourE

/-- Fourier coefficient on [0, 2π]. -/
def fc (f : ℝ → ℂ) (κ : ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ * Complex.exp (-((κ : ℂ) * θ * Complex.I))

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

lemma fourier_two_pi (n : ℤ) (x : ℝ) :
    fourier (T := 2 * π) n (x : AddCircle (2 * π)) = Complex.exp ((n : ℂ) * x * Complex.I) := by
  rw [fourier_coe_apply]; congr 1; push_cast; field_simp

/-- The Fourier coefficient of the lift of a periodic function. -/
lemma fourierCoeff_lift {f : ℝ → ℂ} {g : AddCircle (2 * π) → ℂ}
    (hg : ∀ x : ℝ, g x = f x) (n : ℤ) : fourierCoeff g n = fc f n := by
  rw [fourierCoeff_eq_intervalIntegral g n 0, fc, zero_add, Complex.real_smul]
  congr 1
  · push_cast; ring
  · apply intervalIntegral.integral_congr; intro x _
    simp only [smul_eq_mul, hg, fourier_two_pi]; push_cast; rw [mul_comm]; ring_nf

/-- Two bounded measurable functions on the circle with equal Fourier coefficients agree a.e. -/
lemma ae_eq_of_fourierCoeff_eq {g F : AddCircle (2 * π) → ℂ}
    (hg : AEStronglyMeasurable g AddCircle.haarAddCircle)
    (hF : AEStronglyMeasurable F AddCircle.haarAddCircle)
    {M : ℝ} (hgM : ∀ x, ‖g x‖ ≤ M) (hFM : ∀ x, ‖F x‖ ≤ M)
    (h : fourierCoeff g = fourierCoeff F) : g =ᵐ[AddCircle.haarAddCircle] F := by
  have mg : MemLp g 2 AddCircle.haarAddCircle :=
    MemLp.of_bound hg M (Filter.Eventually.of_forall hgM)
  have mF : MemLp F 2 AddCircle.haarAddCircle :=
    MemLp.of_bound hF M (Filter.Eventually.of_forall hFM)
  have key : mg.toLp g = mF.toLp F := by
    apply (fourierBasis (T := 2 * π)).repr.injective
    ext i
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_congr_ae (MemLp.coeFn_toLp mg),
      fourierCoeff_congr_ae (MemLp.coeFn_toLp mF), h]
  exact (MemLp.toLp_eq_toLp_iff mg mF).mp key

/-- Fourier inversion a.e. for bounded measurable `2π`-periodic functions with absolutely
summable Fourier coefficients. -/
theorem fourier_ae {f : ℝ → ℂ} (hf : Measurable f) (hper : Function.Periodic f (2 * π))
    {M : ℝ} (hM : ∀ θ, ‖f θ‖ ≤ M) (hs : Summable fun κ : ℤ => ‖fc f κ‖) :
    ∀ᵐ θ ∂(volume : Measure ℝ),
      f θ = ∑' κ : ℤ, fc f κ * Complex.exp ((κ : ℂ) * θ * Complex.I) := by
  let g : AddCircle (2 * π) → ℂ := fun x => f (AddCircle.equivIoc (2 * π) 0 x)
  have gmeas : Measurable g :=
    hf.comp (measurable_subtypeVal.comp (AddCircle.measurableEquivIoc (2 * π) 0).measurable)
  have gcoe : ∀ x : ℝ, g x = f x := by
    intro x
    simp only [g, AddCircle.equivIoc, QuotientAddGroup.equivIocMod_coe]
    rw [toIocMod, hper.sub_zsmul_eq]
  let F : AddCircle (2 * π) → ℂ := fun x => ∑' i, fourier i x • fc f i
  have hFn : ∀ i x, ‖fourier (T := 2 * π) i x • fc f i‖ ≤ ‖fc f i‖ := by
    intro i x; rw [norm_smul]
    have : ‖fourier (T := 2 * π) i x‖ = 1 := by simp [fourier_apply]
    rw [this, one_mul]
  have Fcont : Continuous F :=
    continuous_tsum (fun i => by fun_prop) hs hFn
  have FM : ∀ x, ‖F x‖ ≤ ∑' i, ‖fc f i‖ := fun x =>
    (norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ => norm_nonneg _) (hFn · x))).trans
      (hs.of_nonneg_of_le (fun _ => norm_nonneg _) (hFn · x) |>.tsum_le_tsum (hFn · x) hs)
  have gM : ∀ x, ‖g x‖ ≤ M := fun x => hM _
  have hcoef : fourierCoeff g = fourierCoeff F := by
    rw [fourierCoeff_tsum_fourier_smul hs]; ext n; exact fourierCoeff_lift gcoe n
  have hae := ae_eq_of_fourierCoeff_eq gmeas.aestronglyMeasurable
    Fcont.aestronglyMeasurable (M := max M (∑' i, ‖fc f i‖))
    (fun x => (gM x).trans (le_max_left _ _)) (fun x => (FM x).trans (le_max_right _ _)) hcoef
  have hvol : ∀ᵐ x ∂(volume : Measure (AddCircle (2 * π))), g x = F x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; exact Measure.ae_smul_measure hae _
  have hunion : (⋃ k : ℤ, Ioc (0 + k • (2 * π)) (0 + (k + 1) • (2 * π))) = univ :=
    iUnion_Ioc_add_zsmul (by positivity) 0
  rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← hunion, ae_restrict_iUnion_iff]
  intro k
  have hk : (0 + (k + 1) • (2 * π)) = (0 + k • (2 * π)) + 2 * π := by
    rw [add_zsmul, one_zsmul]; ring
  rw [hk]
  filter_upwards [(AddCircle.measurePreserving_mk (2 * π)
    (0 + k • (2 * π))).quasiMeasurePreserving.ae hvol] with θ hθ
  rw [← gcoe, hθ]
  show ∑' i, fourier i (θ : AddCircle (2 * π)) • fc f i = _
  exact tsum_congr fun i => by rw [smul_eq_mul, fourier_two_pi, mul_comm]

/-- Shifting a periodic function multiplies its Fourier coefficients by `exp (i κ α)`. -/
lemma fc_shift {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (α : ℝ) (κ : ℤ) :
    fc (fun θ => f (θ + α)) κ = Complex.exp ((κ : ℂ) * α * Complex.I) * fc f κ := by
  have hp : Function.Periodic (fun u : ℝ => f u * Complex.exp (-((κ : ℂ) * u * Complex.I)))
      (2 * π) := by
    intro u
    simp only [hper u]
    congr 1
    rw [show -((κ : ℂ) * ((u + 2 * π : ℝ) : ℂ) * Complex.I) =
      -((κ : ℂ) * u * Complex.I) + (-κ : ℤ) * (2 * π * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h1 : ∫ θ in (0 : ℝ)..2 * π, f (θ + α) * Complex.exp (-((κ : ℂ) * θ * Complex.I)) =
      Complex.exp ((κ : ℂ) * α * Complex.I) *
        ∫ u in α..α + 2 * π, f u * Complex.exp (-((κ : ℂ) * u * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * π)
      (fun u => Complex.exp ((κ : ℂ) * α * Complex.I) *
        (f u * Complex.exp (-((κ : ℂ) * u * Complex.I)))) α
    rw [zero_add, add_comm (2 * π)] at this
    rw [← this]
    apply intervalIntegral.integral_congr; intro θ _
    simp only
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [fc, fc, h1, hp.intervalIntegral_add_eq α 0, zero_add]; ring

end FourE

/-! ## Theorem 95: the objects of the proof (`n = m + 3`) -/

section Defs95

/-- `a_n(|p|) = λ_{n-1}(p)` for `n = m + 3`. -/
def aF (m : ℕ) (p : ℂ) : ℝ := (cp (m + 1) p).toReal

/-- `λ_{n-2}(x)` for `n = m + 3`; `g(p, q) = 1_B(q) hF m (-p - q)`. -/
def hF (m : ℕ) (x : ℂ) : ℝ := (cp m x).toReal

/-- The corners `C = P_k \ B`. -/
def corner (k : ℕ) : Set ℂ := poly k \ disc

/-- The partner density `ν(q) = (n-1)/|P_k| ∫_C g(p, q)/a_n(|p|) dp` (without the factor
`1_B(q)`), `n = m + 3`. -/
def nu (m k : ℕ) (q : ℂ) : ℝ :=
  ((m + 2 : ℝ) / Poly.area k) * ∫ p in corner k, hF m (-p - q) / aF m p

/-- Its average over the rotations by `2π/n`, `n = m + 3` (equation (23)). -/
def nus (m k : ℕ) (q : ℂ) : ℝ := Poly.avgRot (m + 3) (fun z => nrm (m + 3) 1 * z) (nu m k) q

/-- The `κ`-th angular Fourier component `Π_κ f(q) = (1/2π) ∫ f(e^{iθ} q) e^{-iκθ} dθ`. -/
def proj (κ : ℤ) (f : ℂ → ℂ) (q : ℂ) : ℂ :=
  fc (fun θ => f (Complex.exp ((θ : ℂ) * Complex.I) * q)) κ

/-- `ψ` is a `κ`-mode: `ψ(e^{iα} q) = e^{iκα} ψ(q)`. -/
def IsMode (κ : ℤ) (ψ : ℂ → ℂ) : Prop :=
  ∀ (α : ℝ) (q : ℂ), ψ (Complex.exp ((α : ℂ) * Complex.I) * q) =
    Complex.exp ((κ : ℂ) * α * Complex.I) * ψ q

/-- The integral operator `Tψ(p) = ∫_B λ_{n-2}(-p-q) ψ(q) dq`. -/
def Top (m : ℕ) (ψ : ℂ → ℂ) (p : ℂ) : ℂ := ∫ q in disc, (hF m (-p - q) : ℂ) * ψ q

/-- The operator `G` of the proof on real functions: the marginal density of
`η_φ = (1/n) ∑ φ(xᵢ) λ`, `n = m + 3`. -/
def Gop (m : ℕ) (φ : ℂ → ℝ) (p : ℂ) : ℝ :=
  ((m + 3 : ℕ) : ℝ)⁻¹ * (aF m p * φ p + (m + 2 : ℝ) * ∫ q in disc, hF m (-p - q) * φ q)

/-- **Prékopa–Leindler (cited, stated once as a hypothesis).** The radial profiles of the
convolution powers `λ_{m+1}` of the indicator of the disc are non-increasing on `[0, ∞)`
(each `λ_{m+1}` is log-concave and radial). -/
def PLHyp : Prop := ∀ m : ℕ, AntitoneOn (fun r : ℝ => (cp m (r : ℂ)).toReal) (Ici 0)

end Defs95

section P1

lemma p1_exp_norm (α : ℝ) : ‖Complex.exp ((α : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I α

lemma p1_exp_mul (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `Π_κ f` is a `κ`-mode. -/
lemma isMode_proj (κ : ℤ) (f : ℂ → ℂ) : IsMode κ (proj κ f) := by
  intro α q
  have hper : Function.Periodic
      (fun θ : ℝ => f (Complex.exp ((θ : ℂ) * Complex.I) * q)) (2 * π) := by
    intro θ
    simp only
    congr 2
    rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [proj, proj, ← fc_shift hper α κ]
  congr 1; funext θ
  rw [← mul_assoc, p1_exp_mul]

/-- `Π_κ f` is measurable. -/
lemma measurable_proj (κ : ℤ) {f : ℂ → ℂ} (hf : Measurable f) : Measurable (proj κ f) := by
  have h : StronglyMeasurable (Function.uncurry fun (q : ℂ) (θ : ℝ) =>
      f (Complex.exp ((θ : ℂ) * Complex.I) * q) * Complex.exp (-((κ : ℂ) * θ * Complex.I))) := by
    apply Measurable.stronglyMeasurable
    show Measurable fun x : ℂ × ℝ =>
      f (Complex.exp ((x.2 : ℂ) * Complex.I) * x.1) * Complex.exp (-((κ : ℂ) * x.2 * Complex.I))
    exact (hf.comp (Continuous.measurable (by fun_prop))).mul
      (Continuous.measurable (by fun_prop))
  have h2 := h.integral_prod_right (ν := volume.restrict (Ioc 0 (2 * π)))
  unfold proj fc
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  exact measurable_const.mul h2.measurable

lemma p1_norm_fc_le {F : ℝ → ℂ} {M : ℝ} (hM : ∀ θ, ‖F θ‖ ≤ M) (κ : ℤ) : ‖fc F κ‖ ≤ M := by
  unfold fc
  rw [norm_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (f := fun θ => F θ * Complex.exp (-((κ : ℂ) * θ * Complex.I))) (C := M) (fun θ _ => by
      rw [norm_mul, show -((κ : ℂ) * θ * Complex.I) = ((-(κ * θ) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]; exact hM θ)
  have h2 : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h2]
  rw [sub_zero, abs_of_pos (by positivity)] at h
  calc (2 * π)⁻¹ * ‖_‖ ≤ (2 * π)⁻¹ * (M * (2 * π)) := by gcongr
    _ = M := by field_simp

/-- `‖Π_κ f‖ ≤ sup ‖f‖`. -/
lemma norm_proj_le (κ : ℤ) {f : ℂ → ℂ} {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (q : ℂ) :
    ‖proj κ f q‖ ≤ M :=
  p1_norm_fc_le (fun _ => hM _) κ

/-- `‖Π_κ f(q)‖ ≤ sup_B ‖f‖` for `q ∈ B`. -/
lemma norm_proj_le_disc (κ : ℤ) {f : ℂ → ℂ} {M : ℝ} (hM : ∀ z ∈ disc, ‖f z‖ ≤ M) {q : ℂ}
    (hq : q ∈ disc) : ‖proj κ f q‖ ≤ M :=
  p1_norm_fc_le (fun θ => hM _ ((mul_mem_disc_iff (p1_exp_norm θ) q).2 hq)) κ

lemma p1_setIntegral_rot {u : ℂ} (hu : ‖u‖ = 1) (F : ℂ → ℂ) :
    ∫ q in disc, F (u * q) = ∫ q in disc, F q := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hemb : MeasurableEmbedding (rot u) := by
    convert (Homeomorph.mulLeft₀ u hu0).measurableEmbedding using 1
    funext z; simp
  have := (measurePreserving_rot hu).setIntegral_preimage_emb hemb F disc
  have hpre : (rot u) ⁻¹' disc = disc := by ext z; simp [mul_mem_disc_iff hu]
  rw [hpre] at this
  simpa using this

/-- `T` maps `κ`-modes to `κ`-modes. -/
lemma isMode_Top (m : ℕ) {κ : ℤ} {ψ : ℂ → ℂ} (hψ : IsMode κ ψ) : IsMode κ (Top m ψ) := by
  intro α p
  have hu : ‖Complex.exp ((α : ℂ) * Complex.I)‖ = 1 := p1_exp_norm α
  unfold Top
  rw [← p1_setIntegral_rot hu
    (fun q => (hF m (-(Complex.exp ((α : ℂ) * Complex.I) * p) - q) : ℂ) * ψ q),
    ← integral_const_mul]
  congr 1; funext q
  rw [hψ α q, show -(Complex.exp ((α : ℂ) * Complex.I) * p) - Complex.exp ((α : ℂ) * Complex.I) * q
    = Complex.exp ((α : ℂ) * Complex.I) * (-p - q) by ring]
  simp only [hF, cp_rot m hu]; ring

lemma p1_measurable_hF (m : ℕ) : Measurable (hF m) := (measurable_cp m).ennreal_toReal

/-- `Tψ` is measurable. -/
lemma measurable_Top (m : ℕ) {ψ : ℂ → ℂ} (hψ : Measurable ψ) : Measurable (Top m ψ) := by
  have h : StronglyMeasurable (Function.uncurry fun (p q : ℂ) => (hF m (-p - q) : ℂ) * ψ q) := by
    apply Measurable.stronglyMeasurable
    exact (Complex.measurable_ofReal.comp ((p1_measurable_hF m).comp
      (Continuous.measurable (by fun_prop)))).mul (hψ.comp measurable_snd)
  exact (h.integral_prod_right (ν := volume.restrict disc)).measurable


lemma p1_hF_radial (m : ℕ) (x : ℂ) : hF m x = hF m (‖x‖ : ℂ) := by
  simp only [hF]; rw [cp_radial]

lemma p1_hF_nonneg (m : ℕ) (x : ℂ) : 0 ≤ hF m x := ENNReal.toReal_nonneg

lemma p1_hF_le (hPL : PLHyp) (m : ℕ) (x : ℂ) : hF m x ≤ hF m 0 := by
  rw [p1_hF_radial]
  have := hPL m (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (norm_nonneg x)) (norm_nonneg x)
  simpa [hF] using this

lemma p1_normSq (r s t : ℝ) :
    ‖(r : ℂ) - s * Complex.exp ((t : ℂ) * Complex.I)‖ ^ 2 = r ^ 2 + s ^ 2 - 2 * r * s * cos t := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (s ^ 2) * sin_sq_add_cos_sq t

lemma p1_g_anti (hPL : PLHyp) (m : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    AntitoneOn (fun t : ℝ => hF m ((r : ℂ) - s * Complex.exp ((t : ℂ) * Complex.I))) (Icc 0 π) := by
  intro a ha b hb hab
  simp only
  rw [p1_hF_radial m (_ - _ * Complex.exp ((b : ℂ) * _)),
    p1_hF_radial m (_ - _ * Complex.exp ((a : ℂ) * _))]
  apply hPL m (Set.mem_Ici.2 (norm_nonneg _)) (Set.mem_Ici.2 (norm_nonneg _))
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, p1_normSq, p1_normSq]
  have := cos_le_cos_of_nonneg_of_le_pi ha.1 hb.2 hab
  nlinarith [mul_nonneg hr hs]

lemma p1_g_even (m : ℕ) (r s t : ℝ) :
    hF m ((r : ℂ) - s * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) =
      hF m ((r : ℂ) - s * Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [p1_hF_radial, p1_hF_radial m (_ - _ * Complex.exp ((t : ℂ) * _))]
  have h := p1_normSq r s (-t)
  rw [cos_neg, ← p1_normSq r s t] at h
  rw [(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h]

lemma p1_ii {f : ℝ → ℂ} (hf : Measurable f) {K : ℝ} (hK : ∀ x, ‖f x‖ ≤ K) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := K)).mono_fun' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)

lemma p1_cos_sum (κ : ℤ) (x : ℝ) :
    Complex.exp ((κ : ℂ) * ((-x : ℝ) : ℂ) * Complex.I) + Complex.exp ((κ : ℂ) * x * Complex.I) =
      ((2 * cos (κ * x) : ℝ) : ℂ) := by
  rw [show (κ : ℂ) * ((-x : ℝ) : ℂ) * Complex.I = ((-(κ * x) : ℝ) : ℂ) * Complex.I by
    push_cast; ring,
    show (κ : ℂ) * (x : ℂ) * Complex.I = ((κ * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_neg, sin_neg]
  push_cast; ring

/-- The angular integral of a `PL`-profile against a `κ`-mode. -/
lemma p1_angular (hPL : PLHyp) (m : ℕ) {κ : ℤ} (hκ : κ ≠ 0) {r s : ℝ} (hr : 0 ≤ r)
    (hs : 0 ≤ s) (δ : ℝ) :
    ‖∫ α in (0 : ℝ)..2 * π, Complex.exp ((κ : ℂ) * α * Complex.I) *
      (hF m ((r : ℂ) - s * Complex.exp (((α + δ : ℝ) : ℂ) * Complex.I)) : ℂ)‖ ≤
      2 * hF m 0 / |(κ : ℝ)| := by
  set g : ℝ → ℝ := fun t => hF m ((r : ℂ) - s * Complex.exp ((t : ℂ) * Complex.I)) with hg
  set G : ℝ → ℂ := fun t => Complex.exp ((κ : ℂ) * t * Complex.I) * (g t : ℂ) with hG
  have gm : Measurable g := (p1_measurable_hF m).comp (Continuous.measurable (by fun_prop))
  have Gm : Measurable G :=
    (Continuous.measurable (by fun_prop)).mul (Complex.measurable_ofReal.comp gm)
  have GK : ∀ t, ‖G t‖ ≤ hF m 0 := by
    intro t
    rw [hG, norm_mul, show (κ : ℂ) * t * Complex.I = ((κ * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg
      (p1_hF_nonneg _ _)]
    exact p1_hF_le hPL m _
  have Gper : Function.Periodic G (2 * π) := by
    intro t
    simp only [hG, hg]
    rw [show (((t + 2 * π : ℝ) : ℂ)) * Complex.I = (t : ℂ) * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
      show (κ : ℂ) * ((t + 2 * π : ℝ) : ℂ) * Complex.I = (κ : ℂ) * t * Complex.I +
        (κ : ℤ) * (2 * π * Complex.I) by push_cast; ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h1 : ∀ α : ℝ, Complex.exp ((κ : ℂ) * α * Complex.I) *
      (hF m ((r : ℂ) - s * Complex.exp (((α + δ : ℝ) : ℂ) * Complex.I)) : ℂ) =
      Complex.exp (-((κ : ℂ) * δ * Complex.I)) * G (α + δ) := by
    intro α
    simp only [hG, hg]
    rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, norm_mul,
    show -((κ : ℂ) * δ * Complex.I) = ((-(κ * δ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul,
    intervalIntegral.integral_comp_add_right G δ, zero_add, add_comm (2 * π) δ,
    Gper.intervalIntegral_add_eq δ (-π), show -π + 2 * π = π by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (p1_ii Gm GK _ _)
      (p1_ii Gm GK _ _)]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := π) G
  rw [neg_zero] at hneg
  rw [← hneg, ← intervalIntegral.integral_add
    (p1_ii (f := fun x => G (-x)) (Gm.comp measurable_neg) (fun x => GK (-x)) _ _)
    (p1_ii Gm GK _ _)]
  have h2 : ∀ x : ℝ, G (-x) + G x = ((2 * (g x * cos (κ * x)) : ℝ) : ℂ) := by
    intro x
    simp only [hG, hg]
    rw [p1_g_even, ← add_mul, p1_cos_sum]; push_cast; ring
  simp_rw [h2]
  rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs,
    intervalIntegral.integral_const_mul, abs_mul, abs_two, mul_div_assoc]
  gcongr
  exact Poly.abs_integral_antitone_mul_cos_le gm pi_pos.le (by exact_mod_cast hκ)
    (p1_g_anti hPL m hr hs) (fun _ _ => p1_hF_nonneg _ _) (fun _ _ => p1_hF_le hPL m _)

lemma p1_hF_eq (m : ℕ) (p q : ℂ) (α : ℝ) :
    hF m (-p - Complex.exp ((α : ℂ) * Complex.I) * q) =
      hF m ((‖p‖ : ℂ) - (‖q‖ : ℝ) *
        Complex.exp (((α + (Complex.arg q - Complex.arg p + π)) : ℝ) * Complex.I)) := by
  have hp := Complex.norm_mul_exp_arg_mul_I p
  have hq := Complex.norm_mul_exp_arg_mul_I q
  have key : Complex.exp ((Complex.arg p : ℂ) * Complex.I) *
      Complex.exp (((α + (Complex.arg q - Complex.arg p + π)) : ℝ) * Complex.I) =
      -(Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((Complex.arg q : ℂ) * Complex.I)) := by
    rw [show -(Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((Complex.arg q : ℂ) * Complex.I))
      = Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((Complex.arg q : ℂ) * Complex.I) *
        Complex.exp (π * Complex.I) by rw [Complex.exp_pi_mul_I]; ring,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have e : -p - Complex.exp ((α : ℂ) * Complex.I) * q =
      -(Complex.exp ((Complex.arg p : ℂ) * Complex.I) * ((‖p‖ : ℂ) - (‖q‖ : ℝ) *
        Complex.exp (((α + (Complex.arg q - Complex.arg p + π)) : ℝ) * Complex.I))) := by
    linear_combination hp + Complex.exp ((α : ℂ) * Complex.I) * hq - (‖q‖ : ℂ) * key
  rw [e]; simp only [hF]; rw [cp_neg, cp_rot m (p1_exp_norm _)]

/-- **Theorem 95, the bound on `T` on `κ`-modes.** Under `PLHyp`, for a bounded measurable
`κ`-mode `ψ` (`κ ≠ 0`), `‖Tψ(p)‖ ≤ λ_{n-2}(0) sup_B ‖ψ‖ / |κ|`. -/
theorem norm_Top_le (hPL : PLHyp) (m : ℕ) {κ : ℤ} (hκ : κ ≠ 0) {ψ : ℂ → ℂ} (hψ : IsMode κ ψ)
    (hψm : Measurable ψ) {M : ℝ} (hM : ∀ q ∈ disc, ‖ψ q‖ ≤ M) (p : ℂ) :
    ‖Top m ψ p‖ ≤ hF m 0 * M / |(κ : ℝ)| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [disc]))
  set ψ' : ℂ → ℂ := disc.indicator ψ with hψ'
  have hψ'b : ∀ q, ‖ψ' q‖ ≤ M := by
    intro q; by_cases hq : q ∈ disc
    · simp [hψ', hq, hM q hq]
    · simp [hψ', hq, hM0]
  have hψ'm : Measurable ψ' := hψm.indicator measurableSet_disc
  have hc0 : 0 ≤ hF m 0 := p1_hF_nonneg m 0
  have hrot : ∀ α : ℝ, Top m ψ p = Complex.exp ((κ : ℂ) * α * Complex.I) *
      ∫ q in disc, (hF m (-p - Complex.exp ((α : ℂ) * Complex.I) * q) : ℂ) * ψ' q := by
    intro α
    have hu := p1_exp_norm α
    unfold Top
    rw [← p1_setIntegral_rot hu (fun q => (hF m (-p - q) : ℂ) * ψ q), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_disc (fun q hq => ?_)
    simp only [hψ', Set.indicator_of_mem hq, hψ α q]; ring
  have : IsFiniteMeasure (volume.restrict disc) :=
    isFiniteMeasure_restrict.2 (by rw [volume_disc]; exact ENNReal.ofReal_ne_top)
  have hint : Integrable (Function.uncurry fun (α : ℝ) (q : ℂ) =>
      Complex.exp ((κ : ℂ) * α * Complex.I) *
        ((hF m (-p - Complex.exp ((α : ℂ) * Complex.I) * q) : ℂ) * ψ' q))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict disc)) := by
    refine Integrable.of_bound ?_ (hF m 0 * M) (Filter.Eventually.of_forall fun x => ?_)
    · apply Measurable.aestronglyMeasurable
      show Measurable fun x : ℝ × ℂ => Complex.exp ((κ : ℂ) * x.1 * Complex.I) *
        ((hF m (-p - Complex.exp ((x.1 : ℂ) * Complex.I) * x.2) : ℂ) * ψ' x.2)
      exact (Continuous.measurable (by fun_prop)).mul ((Complex.measurable_ofReal.comp
        ((p1_measurable_hF m).comp (Continuous.measurable (by fun_prop)))).mul
          (hψ'm.comp measurable_snd))
    · simp only [Function.uncurry]
      rw [norm_mul, norm_mul, show (κ : ℂ) * x.1 * Complex.I = ((κ * x.1 : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (p1_hF_nonneg _ _)]
      exact mul_le_mul (p1_hF_le hPL m _) (hψ'b _) (norm_nonneg _) hc0
  have hJ : ∀ q, ‖∫ α in Ioc 0 (2 * π), Complex.exp ((κ : ℂ) * α * Complex.I) *
      (hF m (-p - Complex.exp ((α : ℂ) * Complex.I) * q) : ℂ)‖ ≤ 2 * hF m 0 / |(κ : ℝ)| := by
    intro q
    rw [← intervalIntegral.integral_of_le (by positivity)]
    simp_rw [p1_hF_eq m p q]
    exact p1_angular hPL m hκ (norm_nonneg p) (norm_nonneg q) _
  have key : ((2 * π : ℝ) : ℂ) * Top m ψ p = ∫ q in disc,
      (∫ α in Ioc 0 (2 * π), Complex.exp ((κ : ℂ) * α * Complex.I) *
        (hF m (-p - Complex.exp ((α : ℂ) * Complex.I) * q) : ℂ)) * ψ' q := by
    calc ((2 * π : ℝ) : ℂ) * Top m ψ p = ∫ α in Ioc 0 (2 * π), Top m ψ p := by
          rw [← intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_const,
            sub_zero, Complex.real_smul]
      _ = ∫ α in Ioc 0 (2 * π), ∫ q in disc, Complex.exp ((κ : ℂ) * α * Complex.I) *
            ((hF m (-p - Complex.exp ((α : ℂ) * Complex.I) * q) : ℂ) * ψ' q) := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun α _ => ?_)
          rw [hrot α, ← integral_const_mul]
      _ = _ := integral_integral_swap hint
      _ = _ := by
          congr 1; funext q; rw [← integral_mul_const]; congr 1; funext α; ring
  have hb : ‖((2 * π : ℝ) : ℂ) * Top m ψ p‖ ≤
      2 * hF m 0 / |(κ : ℝ)| * M * volume.real disc := by
    rw [key]
    exact norm_setIntegral_le_of_norm_le_const
      (by rw [volume_disc]; exact ENNReal.ofReal_lt_top) (fun q _ => by
        rw [norm_mul]
        exact mul_le_mul (hJ q) (hψ'b q) (norm_nonneg _)
          (div_nonneg (mul_nonneg zero_le_two hc0) (abs_nonneg _)))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), measureReal_def,
    volume_disc, ENNReal.toReal_ofReal pi_pos.le] at hb
  have : ‖Top m ψ p‖ * (2 * π) ≤ (hF m 0 * M / |(κ : ℝ)|) * (2 * π) := by
    calc ‖Top m ψ p‖ * (2 * π) = 2 * π * ‖Top m ψ p‖ := by ring
      _ ≤ 2 * hF m 0 / |(κ : ℝ)| * M * π := hb
      _ = _ := by ring
  exact le_of_mul_le_mul_right this (by positivity)

end P1

section P2

open Complex in
/-- `a_n` is maximal at `0`. -/
lemma aF_le (hPL : PLHyp) {m : ℕ} (p : ℂ) : aF m p ≤ aF m 0 := by
  unfold aF; rw [cp_radial]
  have := hPL (m + 1) (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.2 le_rfl) (show ‖p‖ ∈ Ici (0 : ℝ) from
    norm_nonneg p) (norm_nonneg p)
  simpa using this

lemma hF_nonneg (m : ℕ) (x : ℂ) : 0 ≤ hF m x := ENNReal.toReal_nonneg

lemma aF_nonneg (m : ℕ) (x : ℂ) : 0 ≤ aF m x := ENNReal.toReal_nonneg

/-- `λ_{n-2}` is maximal at `0`. -/
lemma hF_le (hPL : PLHyp) {m : ℕ} (x : ℂ) : hF m x ≤ hF m 0 := by
  unfold hF; rw [cp_radial]
  have := hPL m (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.2 le_rfl) (show ‖x‖ ∈ Ici (0 : ℝ) from
    norm_nonneg x) (norm_nonneg x)
  simpa using this

lemma p2_aF_anti (hPL : PLHyp) {m : ℕ} {p : ℂ} {r : ℝ} (hr : ‖p‖ ≤ r) :
    aF m (r : ℂ) ≤ aF m p := by
  unfold aF; rw [cp_radial (m + 1) p]
  exact hPL (m + 1) (show ‖p‖ ∈ Ici (0 : ℝ) from norm_nonneg p)
    (show r ∈ Ici (0 : ℝ) from (norm_nonneg p).trans hr) hr

/-- On `P_k`, `a_n ≥ a_n(R)`. -/
lemma aF_ge (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) {p : ℂ} (hp : p ∈ poly k) :
    aF m (Poly.secR k : ℂ) ≤ aF m p :=
  p2_aF_anti hPL (by simpa using poly_subset_closedBall hk hp)

/-- On the disc, `a_n ≥ a_n(1)`. -/
lemma aF_ge_one (hPL : PLHyp) {m : ℕ} {p : ℂ} (hp : p ∈ disc) : aF m 1 ≤ aF m p := by
  have := p2_aF_anti (m := m) hPL (p := p) (r := 1) (by simpa [disc] using hp)
  simpa using this

lemma measurable_hF (m : ℕ) : Measurable (hF m) := (measurable_cp m).ennreal_toReal

lemma measurable_aF (m : ℕ) : Measurable (aF m) := (measurable_cp (m + 1)).ennreal_toReal

lemma measurableSet_corner (k : ℕ) : MeasurableSet (corner k) :=
  (measurableSet_poly k).diff measurableSet_disc

/-- `ν` is measurable. -/
lemma measurable_nu (m k : ℕ) : Measurable (nu m k) := by
  unfold nu
  refine Measurable.const_mul ?_ _
  have h : StronglyMeasurable (Function.uncurry fun (q p : ℂ) => hF m (-p - q) / aF m p) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((measurable_hF m).comp ((measurable_snd.neg).sub measurable_fst)).div
      ((measurable_aF m).comp measurable_snd)
  exact (h.integral_prod_right' (ν := volume.restrict (corner k))).measurable

lemma p2_integrand_nonneg (m : ℕ) (p q : ℂ) : 0 ≤ hF m (-p - q) / aF m p :=
  div_nonneg (hF_nonneg _ _) (aF_nonneg _ _)

lemma p2_area_pos {k : ℕ} (hk : 3 ≤ k) : 0 < Poly.area k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ht := Poly.tan_pos_of_three hk
  simp only [Poly.area]; positivity

/-- `ν ≥ 0`. -/
lemma nu_nonneg (m : ℕ) {k : ℕ} (hk : 3 ≤ k) (q : ℂ) : 0 ≤ nu m k q := by
  unfold nu
  have := p2_area_pos hk
  exact mul_nonneg (by positivity) (setIntegral_nonneg (measurableSet_corner k)
    fun p _ => p2_integrand_nonneg m p q)

lemma p2_volume_corner {k : ℕ} (hk : 3 ≤ k) :
    volume (corner k) = ENNReal.ofReal (Poly.area k - π) := by
  unfold corner
  rw [measure_sdiff (disc_subset_poly k) measurableSet_disc.nullMeasurableSet
    (by rw [volume_disc]; exact ENNReal.ofReal_ne_top), volume_poly hk, volume_disc,
    ENNReal.ofReal_sub _ pi_pos.le]

lemma p2_volume_corner_ne_top {k : ℕ} (hk : 3 ≤ k) : volume (corner k) ≠ ⊤ := by
  rw [p2_volume_corner hk]; exact ENNReal.ofReal_ne_top

lemma p2_area_ge_pi {k : ℕ} (hk : 3 ≤ k) : π ≤ Poly.area k := by
  have h := measure_mono (μ := volume) (disc_subset_poly k)
  rw [volume_disc, volume_poly hk] at h
  exact (ENNReal.ofReal_le_ofReal_iff (p2_area_pos hk).le).1 h

lemma p2_integrableOn (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k)
    (haR : 0 < aF m (Poly.secR k : ℂ)) (q : ℂ) :
    IntegrableOn (fun p => hF m (-p - q) / aF m p) (corner k) := by
  refine Measure.integrableOn_of_bounded (M := hF m 0 / aF m (Poly.secR k : ℂ))
    (p2_volume_corner_ne_top hk) ?_ ?_
  · exact (((measurable_hF m).comp (measurable_neg.sub_const q)).div
      (measurable_aF m)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_corner k)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (p2_integrand_nonneg m p q)]
    exact div_le_div₀ (hF_nonneg _ _) (hF_le hPL _) haR (aF_ge hPL hk hp.1)

/-- **`ν ≤ N`.** -/
lemma nu_le_Nb (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ))
    (q : ℂ) : nu m k q ≤ Mixes.Poly.Nb (m + 3) k (hF m 0) (aF m (Poly.secR k : ℂ)) := by
  have h := Poly.nu_le_N (measurableSet_corner k) (p2_volume_corner_ne_top hk)
    (p2_integrableOn hPL hk haR q) (c := hF m 0) haR (p2_area_pos hk)
    (fun p hp => div_le_div₀ (hF_nonneg _ _) (hF_le hPL _) haR (aF_ge hPL hk hp.1))
    (m := (m + 2 : ℝ)) (by positivity)
    (by rw [Measure.real, p2_volume_corner hk,
      ENNReal.toReal_ofReal (sub_nonneg.2 (p2_area_ge_pi hk))])
  unfold nu; rw [Poly.Nb]; push_cast
  convert h using 2; ring

lemma p2_hF_rot {m : ℕ} {u : ℂ} (hu : ‖u‖ = 1) (x : ℂ) : hF m (u * x) = hF m x := by
  unfold hF; rw [cp_rot m hu]

lemma p2_aF_rot {m : ℕ} {u : ℂ} (hu : ‖u‖ = 1) (x : ℂ) : aF m (u * x) = aF m x := by
  unfold aF; rw [cp_rot (m + 1) hu]

/-- `ν` is invariant under the rotation by `2π/k`. -/
lemma nu_rot (m : ℕ) {k : ℕ} (hk : 0 < k) (q : ℂ) : nu m k (nrm k 1 * q) = nu m k q := by
  have hu : ‖nrm k 1‖ = 1 := norm_nrm
  have hu0 : nrm k 1 ≠ 0 := by rw [← norm_ne_zero_iff, hu]; exact one_ne_zero
  have hmp : MeasurePreserving (fun z : ℂ => nrm k 1 * z) volume volume :=
    measurePreserving_rot hu
  have hemb : MeasurableEmbedding (fun z : ℂ => nrm k 1 * z) :=
    (Homeomorph.mulLeft₀ (nrm k 1) hu0).measurableEmbedding
  have hpre : (fun z : ℂ => nrm k 1 * z) ⁻¹' corner k = corner k := by
    ext z; simp only [corner, mem_preimage, mem_sdiff, mul_nrm_mem_poly hk, mul_mem_disc_iff hu]
  unfold nu; congr 1
  rw [← hmp.setIntegral_preimage_emb hemb, hpre]
  refine setIntegral_congr_fun (measurableSet_corner k) fun p _ => ?_
  rw [p2_aF_rot hu, show -(nrm k 1 * p) - nrm k 1 * q = nrm k 1 * (-p - q) by ring,
    p2_hF_rot hu]

lemma p2_secR_le_two {k : ℕ} (hk : 3 ≤ k) : Poly.secR k ≤ 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc := Poly.cos_pi_div_pos hk
  have h1 : π / k ≤ π / 3 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) hk'
  have h2 : cos (π / 3) ≤ cos (π / k) :=
    cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) h1
  rw [cos_pi_div_three] at h2
  rw [Poly.secR, div_le_iff₀ hc]; linarith

lemma p2_aF_zero_secR {k : ℕ} (hk : 3 ≤ k) :
    aF 0 (Poly.secR k : ℂ) = Poly.lens (Poly.secR k) := by
  have hR : 0 ≤ Poly.secR k := le_trans zero_le_one (Poly.one_le_secR hk)
  have hn : ‖(Poly.secR k : ℂ)‖ = Poly.secR k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  unfold aF
  rw [cp_one_eq (by rw [hn]; exact p2_secR_le_two hk), hn, ENNReal.toReal_ofReal]
  exact lens_nonneg hR (p2_secR_le_two hk)

/-- **Cap bound for `n = 3`.** If every unit disc centred in `B` meets the corners in area at
most `cap`, then `ν ≤ 2·cap/(|P_k| ℓ(R))` on `B`. -/
lemma nu_le_cap (hPL : PLHyp) {k : ℕ} (hk : 3 ≤ k) (hlR : 0 < Poly.lens (Poly.secR k))
    {cap : ℝ} (hcap0 : 0 ≤ cap)
    (hcap : ∀ c ∈ disc, volume (corner k ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal cap)
    {q : ℂ} (hq : q ∈ disc) :
    nu 0 k q ≤ 2 * cap / (Poly.area k * Poly.lens (Poly.secR k)) := by
  have haR : 0 < aF 0 (Poly.secR k : ℂ) := by rw [p2_aF_zero_secR hk]; exact hlR
  have hA := p2_area_pos hk
  have haR' := p2_aF_zero_secR hk
  set aR := aF 0 (Poly.secR k : ℂ)
  have hmq : -q ∈ disc := by simpa [disc] using hq
  have hb : MeasurableSet (Metric.closedBall (-q) (1 : ℝ)) := measurableSet_closedBall
  have hpt : ∀ p ∈ corner k, hF 0 (-p - q) / aF 0 p ≤
      (Metric.closedBall (-q) 1).indicator (fun _ => 1 / aR) p := by
    intro p hp
    have hge := aF_ge hPL (m := 0) hk hp.1
    by_cases hpb : p ∈ Metric.closedBall (-q) 1
    · rw [indicator_of_mem hpb]
      have : hF 0 (-p - q) ≤ 1 := by
        unfold hF; rw [cp_zero_eq]
        by_cases h : -p - q ∈ disc <;> simp [h]
      exact div_le_div₀ zero_le_one this haR hge
    · rw [indicator_of_notMem hpb]
      have : -p - q ∉ disc := by
        intro h; apply hpb
        simp only [disc, Metric.mem_closedBall, dist_zero_right] at h
        rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add, ← norm_neg]
        convert h using 2; ring
      unfold hF; rw [cp_zero_eq]; simp [this]
  have hvol : volume (corner k ∩ Metric.closedBall (-q) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (p2_volume_corner_ne_top hk) (measure_mono inter_subset_left)
  have hint : ∫ p in corner k, hF 0 (-p - q) / aF 0 p ≤ cap / aR := by
    calc ∫ p in corner k, hF 0 (-p - q) / aF 0 p
        ≤ ∫ p in corner k, (Metric.closedBall (-q) 1).indicator (fun _ => 1 / aR) p :=
          setIntegral_mono_on (p2_integrableOn hPL hk haR q)
            ((integrableOn_const (p2_volume_corner_ne_top hk)).indicator hb)
            (measurableSet_corner k) hpt
      _ = volume.real (corner k ∩ Metric.closedBall (-q) 1) * (1 / aR) := by
          rw [setIntegral_indicator hb, setIntegral_const, smul_eq_mul]
      _ ≤ cap * (1 / aR) := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal hcap0 (hcap _ hmq)
      _ = cap / aR := by ring
  unfold nu
  rw [show (2 : ℝ) * cap / (Poly.area k * Poly.lens (Poly.secR k)) =
    ((0 : ℕ) + 2 : ℝ) / Poly.area k * (cap / aR) by rw [haR']; push_cast; ring]
  gcongr

lemma p2_exp_periodic (θ : ℝ) :
    Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [show (((θ + 2 * π : ℝ) : ℂ) * Complex.I) = (θ : ℂ) * Complex.I + 2 * π * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Only the modes `k ∣ κ` occur in `ν`.** -/
lemma proj_nu_eq_zero (m : ℕ) {k : ℕ} (hk : 3 ≤ k) {κ : ℤ} (hκ : ¬ (k : ℤ) ∣ κ) (q : ℂ) :
    proj κ (fun z => (nu m k z : ℂ)) q = 0 := by
  have hk0 : 0 < k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  set F : ℝ → ℂ := fun θ => (nu m k (Complex.exp ((θ : ℂ) * Complex.I) * q) : ℂ) with hFdef
  have hper : Function.Periodic F (2 * π) := fun θ => by simp only [hFdef, p2_exp_periodic]
  set α : ℝ := 2 * π * (1 : ℕ) / k
  have hshift : (fun θ => F (θ + α)) = F := by
    funext θ
    simp only [hFdef]
    rw [show Complex.exp (((θ + α : ℝ) : ℂ) * Complex.I) * q =
      nrm k 1 * (Complex.exp ((θ : ℂ) * Complex.I) * q) by
        rw [nrm, ← mul_assoc, ← Complex.exp_add]; congr 2; simp only [α]; push_cast; ring,
      nu_rot m hk0]
  have h := fc_shift hper α κ
  rw [hshift] at h
  have hne : Complex.exp ((κ : ℂ) * α * Complex.I) ≠ 1 := by
    intro he
    rw [Complex.exp_eq_one_iff] at he
    obtain ⟨n, hn⟩ := he
    apply hκ
    refine ⟨n, ?_⟩
    have h2 : (((κ : ℝ) * (1 / k) : ℝ) : ℂ) * (2 * π * Complex.I) =
        ((n : ℝ) : ℂ) * (2 * π * Complex.I) := by
      rw [Complex.ofReal_intCast, ← hn]; simp only [α]; push_cast; ring
    have hpi : (2 * π * Complex.I) ≠ 0 := by simp [pi_ne_zero, Complex.I_ne_zero]
    have h4 : (κ : ℝ) * (1 / k) = n := by exact_mod_cast mul_right_cancel₀ hpi h2
    have h5 : (κ : ℝ) = (k : ℝ) * n := by field_simp at h4; linarith
    exact_mod_cast h5
  unfold proj
  have : (1 - Complex.exp ((κ : ℂ) * α * Complex.I)) * fc F κ = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1).symm hne
  · exact h1

open Complex in
/-- The angular profile `θ ↦ λ_{n-2}(ρ - s e^{iθ})`. -/
def p2g (m : ℕ) (ρ s θ : ℝ) : ℝ := hF m ((ρ : ℂ) - s * cexp ((θ : ℂ) * I))

lemma p2_hF_norm {m : ℕ} {x y : ℂ} (h : ‖x‖ = ‖y‖) : hF m x = hF m y := by
  unfold hF; rw [cp_radial m x, cp_radial m y, h]

lemma p2_hF_mono (hPL : PLHyp) {m : ℕ} {x y : ℂ} (h : ‖x‖ ≤ ‖y‖) : hF m y ≤ hF m x := by
  unfold hF; rw [cp_radial m x, cp_radial m y]
  exact hPL m (show ‖x‖ ∈ Ici (0 : ℝ) from norm_nonneg x)
    (show ‖y‖ ∈ Ici (0 : ℝ) from norm_nonneg y) h

open Complex in
lemma p2_normSq (ρ s θ : ℝ) :
    ‖(ρ : ℂ) - s * cexp ((θ : ℂ) * I)‖ ^ 2 = ρ ^ 2 + s ^ 2 - 2 * ρ * s * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, re_ofReal_mul, im_ofReal_mul,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination s ^ 2 * this

lemma p2g_even (m : ℕ) (ρ s θ : ℝ) : p2g m ρ s (-θ) = p2g m ρ s θ := by
  unfold p2g; apply p2_hF_norm
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), p2_normSq, p2_normSq, Real.cos_neg]

lemma p2g_anti (hPL : PLHyp) (m : ℕ) {ρ s : ℝ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s) :
    AntitoneOn (p2g m ρ s) (Icc 0 π) := by
  intro a ha b hb hab
  unfold p2g; apply p2_hF_mono hPL
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), p2_normSq, p2_normSq]
  have := Real.cos_le_cos_of_nonneg_of_le_pi ha.1 hb.2 hab
  nlinarith [mul_nonneg hρ hs]

lemma p2g_meas (m : ℕ) (ρ s : ℝ) : Measurable (p2g m ρ s) :=
  (measurable_hF m).comp (by fun_prop)

lemma p2_ii {F : ℝ → ℂ} (hF : Measurable F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) (a b : ℝ) :
    IntervalIntegrable F volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const
    hF.aestronglyMeasurable (Filter.Eventually.of_forall hM)

open Complex in
/-- **Fourier coefficients of the angular profile of `λ_{n-2}`.** -/
lemma p2_fc_bound (hPL : PLHyp) (m : ℕ) {ρ s : ℝ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s) {κ : ℤ}
    (hκ : κ ≠ 0) :
    ‖fc (fun θ => (p2g m ρ s θ : ℂ)) κ‖ ≤ (2 * π)⁻¹ * (2 * hF m 0 / |(κ : ℝ)|) := by
  set g := p2g m ρ s
  set c := hF m 0
  set G : ℝ → ℂ := fun θ => (g θ : ℂ) * cexp (-((κ : ℂ) * θ * I)) with hGdef
  have hgle : ∀ θ, g θ ≤ c := fun θ => hF_le hPL _
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => hF_nonneg _ _
  have hGm : Measurable G := by
    refine (Complex.measurable_ofReal.comp (p2g_meas m ρ s)).mul ?_; fun_prop
  have hGb : ∀ θ, ‖G θ‖ ≤ c := by
    intro θ
    rw [hGdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 θ),
      show -((κ : ℂ) * θ * I) = ((-(κ * θ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hgle θ
  have hGi : ∀ a b, IntervalIntegrable G volume a b := p2_ii hGm hGb
  have hGni : ∀ a b, IntervalIntegrable (fun θ => G (-θ)) volume a b :=
    p2_ii (hGm.comp measurable_neg) (fun θ => hGb _)
  have hper : Function.Periodic G (2 * π) := by
    intro θ
    simp only [hGdef]
    have : g (θ + 2 * π) = g θ := by
      simp only [g, p2g]; rw [p2_exp_periodic]
    rw [this]
    congr 1
    rw [show -((κ : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) =
      -((κ : ℂ) * θ * I) + (-κ : ℤ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h1 : ∫ θ in (0 : ℝ)..2 * π, G θ = ∫ θ in (-π)..π, G θ := by
    have := hper.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at this
    exact this
  have h2 : ∫ θ in (-π)..π, G θ = ∫ θ in (0 : ℝ)..π, (G (-θ) + G θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hGi (-π) 0) (hGi 0 π),
      intervalIntegral.integral_add (hGni 0 π) (hGi 0 π), intervalIntegral.integral_comp_neg,
      neg_zero]
  have h3 : ∀ θ : ℝ, G (-θ) + G θ = ((2 * (g θ * Real.cos (κ * θ)) : ℝ) : ℂ) := by
    intro θ
    simp only [hGdef]
    rw [show g (-θ) = g θ from p2g_even m ρ s θ]
    push_cast
    rw [Complex.cos]
    rw [show -((κ : ℂ) * -(θ : ℂ) * I) = (κ : ℂ) * θ * I by ring,
      show -((κ : ℂ) * (θ : ℂ) * I) = -((κ : ℂ) * θ) * I by ring]
    ring
  rw [fc, h1, h2]
  simp_rw [h3]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hb := Poly.abs_integral_antitone_mul_cos_le (p2g_meas m ρ s) (L := π) (C := c)
    (κ := κ) pi_pos.le (by exact_mod_cast hκ) (p2g_anti hPL m hρ hs)
    (fun ψ _ => hg0 ψ) (fun ψ _ => hgle ψ)
  have h2pi : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2pi, abs_two]
  gcongr
  calc 2 * |∫ ψ in (0 : ℝ)..π, g ψ * Real.cos (κ * ψ)| ≤ 2 * (c / |(κ : ℝ)|) := by gcongr
    _ = 2 * c / |(κ : ℝ)| := by ring

open Complex in
lemma p2_polar_symm (y : ℝ × ℝ) : Complex.polarCoord.symm y = y.1 * cexp (y.2 * I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]

open Complex in
lemma p2_norm_polar (ρ β : ℝ) : ‖(ρ : ℂ) * cexp (β * I)‖ = |ρ| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The polar measure on `(0, R] × (-π, π)`. -/
def p2nu (k : ℕ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc 0 (Poly.secR k))).prod (volume.restrict (Ioo (-π) π))

open Complex in
/-- The integrand of `ν` in polar coordinates. -/
def p2int (m k : ℕ) (x : ℂ) (y : ℝ × ℝ) : ℝ :=
  y.1 * ((corner k).indicator (fun _ => (1 : ℝ)) (y.1 * cexp (y.2 * I)) *
    (hF m (-(y.1 * cexp (y.2 * I)) - x) / aF m (y.1 * cexp (y.2 * I))))

instance p2nu_finite (k : ℕ) : IsFiniteMeasure (p2nu k) := by unfold p2nu; infer_instance

open Complex in
/-- `ν` in polar coordinates. -/
lemma p2_nu_polar (m : ℕ) {k : ℕ} (hk : 3 ≤ k) (x : ℂ) :
    nu m k x = ((m + 2 : ℝ) / Poly.area k) * ∫ y, p2int m k x y ∂(p2nu k) := by
  unfold nu; congr 1
  rw [p2nu, Measure.prod_restrict, ← Measure.volume_eq_prod,
    ← integral_indicator (measurableSet_corner k), ← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo)
    (prod_mono Ioc_subset_Ioi_self subset_rfl)]
  · refine setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo) fun y _ => ?_
    rw [p2_polar_symm, smul_eq_mul, p2int]
    congr 1
    by_cases h : (y.1 : ℂ) * cexp (y.2 * I) ∈ corner k
    · rw [indicator_of_mem h, indicator_of_mem h, one_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  · intro y hy
    have h1 : 0 < y.1 := hy.1.1
    have h2 : Poly.secR k < y.1 := by
      by_contra hc
      exact hy.2 ⟨⟨h1, not_lt.1 hc⟩, hy.1.2⟩
    have : Complex.polarCoord.symm y ∉ corner k := by
      intro hc
      have := poly_subset_closedBall hk hc.1
      rw [Metric.mem_closedBall, dist_zero_right, p2_polar_symm, p2_norm_polar,
        abs_of_pos h1] at this
      linarith
    rw [indicator_of_notMem this, smul_zero]

open Complex in
lemma p2_theta (m : ℕ) {κ : ℤ} (q : ℂ) (ρ β : ℝ) :
    ∫ θ in Ioc 0 (2 * π), (hF m (-(ρ * cexp (β * I)) - cexp (θ * I) * q) : ℂ) *
        cexp (-((κ : ℂ) * θ * I)) =
      2 * π * (cexp ((κ : ℂ) * (Complex.arg q - β + π : ℝ) * I) *
        fc (fun θ => (p2g m ρ ‖q‖ θ : ℂ)) κ) := by
  have hper : Function.Periodic (fun θ => (p2g m ρ ‖q‖ θ : ℂ)) (2 * π) := by
    intro θ; simp only [p2g, p2_exp_periodic]
  rw [← fc_shift hper, fc, ← intervalIntegral.integral_of_le (by positivity)]
  rw [← mul_assoc, mul_inv_cancel₀ (by simp [pi_ne_zero]), one_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  congr 2
  unfold p2g; apply p2_hF_norm
  set γ := Complex.arg q
  have hq : q = ‖q‖ * cexp (γ * I) := (Complex.norm_mul_exp_arg_mul_I q).symm
  set sq := ‖q‖
  have e : cexp (((θ + (γ - β + π) : ℝ) : ℂ) * I) =
      -(cexp (θ * I) * cexp (γ * I)) / cexp (β * I) := by
    rw [show ((θ + (γ - β + π) : ℝ) : ℂ) * I = θ * I + γ * I - β * I + π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_sub, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hne : cexp (β * I) ≠ 0 := Complex.exp_ne_zero _
  rw [e, show -(ρ * cexp (β * I)) - cexp (θ * I) * q =
      (-cexp (β * I)) * ((ρ : ℂ) - sq * (-(cexp (θ * I) * cexp (γ * I)) / cexp (β * I))) by
    rw [hq]; field_simp; ring]
  rw [norm_mul, norm_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

open Complex in
lemma p2_beta {k : ℕ} (hk : 3 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) {κ : ℤ} (hκ : κ ≠ 0) :
    ‖∫ β in Ioo (-π) π, (((corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) : ℝ) : ℂ)
        * cexp (-(I * κ) * β)‖ ≤ (Ioi 1).indicator (fun _ => 2 * k / |(κ : ℝ)|) ρ ∧
    (¬ (k : ℤ) ∣ κ → ∫ β in Ioo (-π) π,
      (((corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) : ℝ) : ℂ) *
        cexp (-(I * κ) * β) = 0) := by
  rcases le_or_gt ρ 1 with h1 | h1
  · have h0 : ∀ β : ℝ, (((corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) : ℝ) : ℂ)
        * cexp (-(I * κ) * β) = 0 := by
      intro β
      have : (ρ : ℂ) * cexp (β * I) ∉ corner k := by
        intro hc; apply hc.2
        simp only [disc, Metric.mem_closedBall, dist_zero_right, p2_norm_polar,
          abs_of_pos hρ]
        exact h1
      rw [indicator_of_notMem this]; simp
    simp only [h0, integral_zero, norm_zero]
    exact ⟨indicator_nonneg (fun _ _ => by positivity) _, by simp⟩
  · have heq : ∀ β : ℝ, (((corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) : ℝ) : ℂ)
        = (poly k).indicator (fun _ => (1 : ℂ)) ((ρ : ℂ) * cexp ((β : ℂ) * I)) := by
      intro β
      have hnd : (ρ : ℂ) * cexp (β * I) ∉ disc := by
        simp only [disc, Metric.mem_closedBall, dist_zero_right, p2_norm_polar,
          abs_of_pos hρ, not_le]
        exact h1
      by_cases hp : (ρ : ℂ) * cexp (β * I) ∈ poly k
      · rw [indicator_of_mem (show _ ∈ corner k from ⟨hp, hnd⟩), indicator_of_mem hp,
          ofReal_one]
      · rw [indicator_of_notMem (show _ ∉ corner k from fun h => hp h.1), indicator_of_notMem hp,
          ofReal_zero]
    simp_rw [heq]
    have := arc_integral hk h1.le hκ
    rw [indicator_of_mem (show ρ ∈ Ioi 1 from h1)]
    exact this

open Complex in
lemma p2_aF_polar {m : ℕ} (ρ β : ℝ) :
    aF m ((ρ : ℂ) * cexp (β * I)) = aF m ρ := by
  unfold aF; rw [cp_radial _ ((ρ : ℂ) * _), cp_radial _ (ρ : ℂ), p2_norm_polar,
    Complex.norm_real, Real.norm_eq_abs]

open Complex in
lemma p2int_bound (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ))
    (x : ℂ) (y : ℝ × ℝ) :
    ‖p2int m k x y‖ ≤ Poly.secR k * (hF m 0 / aF m (Poly.secR k : ℂ)) := by
  have hR : 0 ≤ Poly.secR k := le_trans zero_le_one (Poly.one_le_secR hk)
  unfold p2int
  by_cases h : (y.1 : ℂ) * cexp (y.2 * I) ∈ corner k
  · rw [indicator_of_mem h, one_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (p2_integrand_nonneg m _ _)]
    have h1 := poly_subset_closedBall hk h.1
    rw [Metric.mem_closedBall, dist_zero_right, p2_norm_polar] at h1
    exact mul_le_mul h1 (div_le_div₀ (hF_nonneg _ _) (hF_le hPL _) haR (aF_ge hPL hk h.1))
      (p2_integrand_nonneg m _ _) hR
  · rw [indicator_of_notMem h, zero_mul, mul_zero, norm_zero]
    exact mul_nonneg hR (div_nonneg (hF_nonneg _ _) haR.le)

open Complex in
/-- **Angular Fourier coefficients of `ν`** (Theorem 95): for `κ ≠ 0`,
`|Π_κ ν(q)| ≤ (n-1) k c (R² - 1)/(π |P_k| a_n(R) κ²)`. -/
theorem norm_proj_nu_le (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k)
    (haR : 0 < aF m (Poly.secR k : ℂ)) {κ : ℤ} (hκ : κ ≠ 0) (q : ℂ) (_hq : q ∈ disc) :
    ‖proj κ (fun z => (nu m k z : ℂ)) q‖ ≤
      (m + 2) * k * hF m 0 * (Poly.secR k ^ 2 - 1) /
        (π * Poly.area k * aF m (Poly.secR k : ℂ) * (κ : ℝ) ^ 2) := by
  set R := Poly.secR k with hRdef
  set aR := aF m (R : ℂ)
  set c := hF m 0
  set A := Poly.area k
  have hR1 : 1 ≤ R := Poly.one_le_secR hk
  have hA := p2_area_pos hk
  have hκr : (κ : ℝ) ≠ 0 := by exact_mod_cast hκ
  have hc0 : 0 ≤ c := hF_nonneg _ _
  set μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  set Φ : ℝ → ℝ × ℝ → ℂ := fun θ y =>
    (p2int m k (cexp (θ * I) * q) y : ℂ) * cexp (-((κ : ℂ) * θ * I)) with hΦdef
  -- integrability of `Φ`
  have hΦm : Measurable (Function.uncurry Φ) := by
    have hP : Measurable fun z : ℝ × (ℝ × ℝ) => (z.2.1 : ℂ) * cexp (z.2.2 * I) := by fun_prop
    refine (Complex.measurable_ofReal.comp ?_).mul (by fun_prop)
    refine (measurable_snd.fst).mul (((measurable_const.indicator (measurableSet_corner k)).comp
      hP).mul (((measurable_hF m).comp ?_).div ((measurable_aF m).comp hP)))
    exact hP.neg.sub (by fun_prop)
  have hΦb : ∀ z : ℝ × (ℝ × ℝ), ‖Function.uncurry Φ z‖ ≤ R * (c / aR) := by
    intro z
    simp only [Function.uncurry, hΦdef, norm_mul, Complex.norm_real]
    rw [show -((κ : ℂ) * z.1 * I) = ((-(κ * z.1) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact p2int_bound hPL hk haR _ _
  have hΦi : Integrable (Function.uncurry Φ) (μ.prod (p2nu k)) := by
    exact Integrable.of_bound hΦm.aestronglyMeasurable _ (Filter.Eventually.of_forall hΦb)
  -- step A: `proj` as a double integral
  have hA1 : proj κ (fun z => (nu m k z : ℂ)) q =
      (2 * π : ℂ)⁻¹ * (((m + 2 : ℝ) / A : ℝ) : ℂ) * ∫ θ, ∫ y, Φ θ y ∂(p2nu k) ∂μ := by
    have e : ∀ θ : ℝ, (nu m k (cexp (θ * I) * q) : ℂ) * cexp (-((κ : ℂ) * θ * I)) =
        (((m + 2 : ℝ) / A : ℝ) : ℂ) * ∫ y, Φ θ y ∂(p2nu k) := by
      intro θ
      simp only [hΦdef]
      rw [integral_mul_const, integral_complex_ofReal, p2_nu_polar m hk]
      push_cast; ring
    unfold proj fc
    rw [intervalIntegral.integral_of_le (by positivity)]
    simp_rw [e]
    rw [integral_const_mul]; ring
  -- step B, C: swap and split
  have hint := hΦi.integral_prod_right
  have hBC : ∫ θ, ∫ y, Φ θ y ∂(p2nu k) ∂μ =
      ∫ ρ in Ioc 0 R, ∫ β in Ioo (-π) π, ∫ θ, Φ θ (ρ, β) ∂μ := by
    rw [integral_integral_swap hΦi]
    exact integral_prod _ hint
  -- step D: the slices
  set fcρ : ℝ → ℂ := fun ρ => fc (fun θ => (p2g m ρ ‖q‖ θ : ℂ)) κ
  set K : ℝ → ℂ := fun ρ => ((ρ / aF m ρ : ℝ) : ℂ) *
    (2 * π * (cexp ((κ : ℂ) * (Complex.arg q + π : ℝ) * I) * fcρ ρ))
  set Jβ : ℝ → ℂ := fun ρ => ∫ β in Ioo (-π) π,
    (((corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) : ℝ) : ℂ) *
      cexp (-(I * κ) * β)
  have hD : ∀ ρ ∈ Ioc 0 R, ∫ β in Ioo (-π) π, ∫ θ, Φ θ (ρ, β) ∂μ = K ρ * Jβ ρ := by
    intro ρ hρ
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    simp only [hΦdef, p2int]
    have e1 : ∀ θ : ℝ, ((ρ * ((corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) *
        (hF m (-(ρ * cexp (β * I)) - cexp (θ * I) * q) / aF m (ρ * cexp (β * I)))) : ℝ) : ℂ) *
        cexp (-((κ : ℂ) * θ * I)) =
        ((ρ * (corner k).indicator (fun _ => (1 : ℝ)) (ρ * cexp (β * I)) /
          aF m (ρ * cexp (β * I)) : ℝ) : ℂ) *
        ((hF m (-(ρ * cexp (β * I)) - cexp (θ * I) * q) : ℂ) * cexp (-((κ : ℂ) * θ * I))) := by
      intro θ; push_cast; ring
    simp_rw [e1]
    rw [integral_const_mul, p2_theta, p2_aF_polar]
    simp only [K, fcρ]
    have e2 : cexp ((κ : ℂ) * (Complex.arg q - β + π : ℝ) * I) =
        cexp ((κ : ℂ) * (Complex.arg q + π : ℝ) * I) * cexp (-(I * κ) * β) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e2]; push_cast; ring
  -- step E: the bound
  set bnd : ℝ → ℝ := (Ioi 1).indicator
    (fun ρ => ρ / aF m ρ * (2 * c / |(κ : ℝ)|) * (2 * k / |(κ : ℝ)|))
  have haρ : ∀ ρ ∈ Ioc 0 R, aR ≤ aF m ρ := fun ρ hρ => p2_aF_anti hPL (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ.1]; exact hρ.2)
  have hE : ∀ ρ ∈ Ioc 0 R, ‖K ρ * Jβ ρ‖ ≤ bnd ρ := by
    intro ρ hρ
    have ha := lt_of_lt_of_le haR (haρ ρ hρ)
    have hfc := p2_fc_bound hPL m hρ.1.le (norm_nonneg q) hκ
    have hJ := (p2_beta hk hρ.1 hκ).1
    have hK : ‖K ρ‖ ≤ ρ / aF m ρ * (2 * c / |(κ : ℝ)|) := by
      simp only [K, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hρ.1.le ha.le)]
      rw [show (κ : ℂ) * ((Complex.arg q + π : ℝ) : ℂ) * I =
        ((κ * (Complex.arg q + π) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_two, abs_of_pos pi_pos]
      calc ρ / aF m ρ * (2 * π * ‖fcρ ρ‖)
          ≤ ρ / aF m ρ * (2 * π * ((2 * π)⁻¹ * (2 * c / |(κ : ℝ)|))) :=
            mul_le_mul_of_nonneg_left (by gcongr) (div_nonneg hρ.1.le ha.le)
        _ = ρ / aF m ρ * (2 * c / |(κ : ℝ)|) := by field_simp
    rw [norm_mul]
    simp only [bnd, Jβ] at hJ ⊢
    by_cases h1 : ρ ∈ Ioi 1
    · rw [indicator_of_mem h1] at hJ ⊢
      exact mul_le_mul hK hJ (norm_nonneg _)
        (mul_nonneg (div_nonneg hρ.1.le ha.le) (div_nonneg (by linarith) (abs_nonneg _)))
    · rw [indicator_of_notMem h1] at hJ ⊢
      have : ‖Jβ ρ‖ = 0 := le_antisymm hJ (norm_nonneg _)
      simp only [Jβ] at this
      rw [this, mul_zero]
  have hbi : IntegrableOn bnd (Ioc 0 R) := by
    refine Measure.integrableOn_of_bounded (M := R / aR * (2 * c / |(κ : ℝ)|) *
      (2 * k / |(κ : ℝ)|)) measure_Ioc_lt_top.ne ?_ ?_
    · exact (Measurable.indicator (by
        have := (measurable_aF m).comp Complex.measurable_ofReal
        fun_prop) measurableSet_Ioi).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
      have ha := lt_of_lt_of_le haR (haρ ρ hρ)
      simp only [bnd]
      by_cases h1 : ρ ∈ Ioi 1
      have hb0 : 0 ≤ 2 * c / |(κ : ℝ)| := div_nonneg (by linarith) (abs_nonneg _)
      have hb1 : 0 ≤ 2 * (k : ℝ) / |(κ : ℝ)| := div_nonneg (by positivity) (abs_nonneg _)
      · rw [indicator_of_mem h1, Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg (div_nonneg hρ.1.le ha.le) hb0) hb1)]
        have := div_le_div₀ (by linarith) hρ.2 haR (haρ ρ hρ)
        gcongr
      · rw [indicator_of_notMem h1, norm_zero]; positivity
  have hF' : ∫ ρ in Ioc 0 R, bnd ρ =
      (∫ ρ in (1 : ℝ)..R, ρ / aF m ρ) * (2 * c / |(κ : ℝ)|) * (2 * k / |(κ : ℝ)|) := by
    simp only [bnd]
    rw [setIntegral_indicator measurableSet_Ioi,
      show Ioc 0 R ∩ Ioi 1 = Ioc 1 R by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩,
      integral_mul_const, integral_mul_const, intervalIntegral.integral_of_le hR1]
  have hI : ‖∫ ρ in Ioc 0 R, ∫ β in Ioo (-π) π, ∫ θ, Φ θ (ρ, β) ∂μ‖ ≤
      ∫ ρ in Ioc 0 R, bnd ρ := by
    refine norm_integral_le_of_norm_le hbi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    rw [hD ρ hρ]; exact hE ρ hρ
  have hcb := Poly.coeff_bound (n := m + 3) (by omega) hk (a := fun ρ => aF m ρ) hc0 haR
    (fun ρ hρ => haρ ρ ⟨by linarith [hρ.1], hρ.2⟩) hκr
  have hn1 : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hn2 : ‖((((m + 2 : ℝ) / A : ℝ)) : ℂ)‖ = (m + 2) / A := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hA1, hBC, norm_mul, norm_mul, hn1, hn2]
  calc (2 * π)⁻¹ * ((m + 2) / A) * ‖∫ ρ in Ioc 0 R, ∫ β in Ioo (-π) π, ∫ θ, Φ θ (ρ, β) ∂μ‖
      ≤ (2 * π)⁻¹ * ((m + 2) / A) * ∫ ρ in Ioc 0 R, bnd ρ := by gcongr
    _ = (((m + 3 : ℕ) : ℝ) - 1) / A * (∫ ρ in (1 : ℝ)..R, ρ / aF m ρ) * (1 / (2 * π)) *
        (2 * c / |(κ : ℝ)|) * (2 * k / |(κ : ℝ)|) := by rw [hF']; push_cast; ring
    _ ≤ _ := hcb
    _ = _ := by push_cast; ring

end P2

section P4

open Room

/-- The a.e. form of `completelyMixable_of_densities`, with an `ℝ≥0∞`-valued marginal density. -/
lemma p4_cm_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {n : ℕ}
    (hn : 0 < n) (Q : E →L[ℝ] E) (hQn : Q ^ n = 1)
    (hfix : ∀ x, Q x = x → x = 0) (hQvol : MeasurePreserving Q volume volume) {K B : Set E}
    (hK : IsCompact K) (hpos : 0 < volume K) (hc : centroid K = 0) (hB : MeasurableSet B)
    (hBK : B ⊆ K) (hQB : ∀ x ∈ B, Q x ∈ B)
    (β₁ : Measure (Fin n → E)) (hβP : PermInvariant β₁) (hβT : β₁ (tuples n K 0)ᶜ = 0)
    {f₁ : E → ℝ≥0∞} {dR : E → ℝ} (hdR : Measurable dR)
    (hmar : marginal β₁ = volume.withDensity f₁)
    (hdRB : ∀ q, q ∉ B → dR q = 0) (hdRQ : ∀ q, dR (Q q) = dR q)
    (hid : ∀ᵐ q ∂volume, f₁ q + ENNReal.ofReal (dR q) =
      ENNReal.ofReal (K.indicator 1 q / (volume K).toReal)) :
    CompletelyMixable n (unifSet K) := by
  set ρ := volume.withDensity fun q => ENNReal.ofReal (dR q) with hρ
  have hfR : Measurable fun q => ENNReal.ofReal (dR q) := ENNReal.measurable_ofReal.comp hdR
  refine Poly.completelyMixable_of_rest hn Q hQn hfix hK hpos hc hBK hQB β₁ hβP hβT ρ ?_ ?_ ?_
  · rw [hρ, withDensity_apply _ hB.compl]
    apply setLIntegral_eq_zero hB.compl
    · intro q hq; simp [hdRB q hq]
  · ext S hS
    rw [Measure.map_apply hQvol.measurable hS, hρ, withDensity_apply _ (hQvol.measurable hS),
      withDensity_apply _ hS, ← hQvol.setLIntegral_comp_preimage hS hfR]
    simp only [hdRQ]
  · rw [hmar, hρ, ← withDensity_add_right _ hfR,
      Mixes.unifSet_eq_withDensity hK.measurableSet hpos.ne' hK.measure_lt_top.ne]
    exact withDensity_congr_ae hid

/-- A measure with a permutation-symmetric density w.r.t. a permutation-invariant measure is
permutation-invariant. -/
lemma p4_permInvariant_withDensity {n : ℕ} {lam : Measure (Fin n → ℂ)} (hP : PermInvariant lam)
    {f : (Fin n → ℂ) → ℝ≥0∞} (hf : Measurable f) (hfσ : ∀ (σ : Equiv.Perm (Fin n)) x,
      f (x ∘ σ) = f x) : PermInvariant (lam.withDensity f) := by
  intro σ
  ext S hS
  rw [Measure.map_apply (measurable_perm σ) hS, withDensity_apply _ (measurable_perm σ hS),
    withDensity_apply _ hS]
  conv_rhs => rw [← hP σ]
  rw [setLIntegral_map hS hf (measurable_perm σ)]
  simp only [hfσ]

lemma p4_measurable_aF (m : ℕ) : Measurable (aF m) :=
  (measurable_cp (m + 1)).ennreal_toReal

lemma p4_measurable_hF (m : ℕ) : Measurable (hF m) :=
  (measurable_cp m).ennreal_toReal

lemma p4_ofReal_aF (m : ℕ) (p : ℂ) : ENNReal.ofReal (aF m p) = cp (m + 1) p :=
  ENNReal.ofReal_toReal (cp_ne_top _ _)

lemma p4_ofReal_hF (m : ℕ) (p : ℂ) : ENNReal.ofReal (hF m p) = cp m p :=
  ENNReal.ofReal_toReal (cp_ne_top _ _)

lemma p4_hF_nonneg (m : ℕ) (p : ℂ) : 0 ≤ hF m p := ENNReal.toReal_nonneg

lemma p4_hF_le (m : ℕ) (p : ℂ) : hF m p ≤ (volume disc ^ m).toReal :=
  ENNReal.toReal_mono (by rw [volume_disc]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (cp_le m p)

lemma p4_aF_le {k : ℕ} (hk : 3 ≤ k) (hPL : PLHyp) (m : ℕ) {p : ℂ} (hp : p ∈ poly k) :
    aF m (Poly.secR k : ℂ) ≤ aF m p := by
  have hb := poly_subset_closedBall hk hp
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have h := hPL (m + 1) (mem_Ici.2 (norm_nonneg p)) (mem_Ici.2 ((norm_nonneg p).trans hb)) hb
  simp only [aF]
  rwa [cp_radial (m + 1) p]

/-- `∫_B λ_{n-2}(-p-q) dq = a_n(p)`. -/
lemma p4_integral_hF (m : ℕ) (p : ℂ) : ∫ q in disc, hF m (-p - q) = aF m p := by
  simp only [hF, aF]
  rw [integral_toReal, ← cp_succ, cp_neg]
  · exact ((measurable_cp m).comp (measurable_const.sub measurable_id)).aemeasurable
  · exact Filter.Eventually.of_forall fun q => (cp_ne_top _ _).lt_top


lemma p4_area_pos {k : ℕ} (hk : 3 ≤ k) : 0 < Poly.area k :=
  mul_pos (by exact_mod_cast (show 0 < k by omega)) (Poly.tan_pos_of_three hk)

lemma p4_vol_poly_toReal {k : ℕ} (hk : 3 ≤ k) : (volume (poly k)).toReal = Poly.area k := by
  rw [volume_poly hk, ENNReal.toReal_ofReal (p4_area_pos hk).le]

lemma p4_intOn {S : Set ℂ} (hS : MeasurableSet S) (hSf : volume S ≠ ⊤) {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x ∈ S, |f x| ≤ M) : IntegrableOn f S volume := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  exact Integrable.of_bound hf.aestronglyMeasurable M
    ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x hx))

lemma p4_lint_ind {S : Set ℂ} (hS : MeasurableSet S) {f : ℂ → ℝ} (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hfi : IntegrableOn f S volume) :
    ∫⁻ x, S.indicator 1 x * ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in S, f x) := by
  have : (fun x => S.indicator 1 x * ENNReal.ofReal (f x)) =
      S.indicator (fun x => ENNReal.ofReal (f x)) := by
    ext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [this, lintegral_indicator hS, ofReal_integral_eq_lintegral_ofReal hfi
    ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hf0))]

lemma p4_volume_disc_ne_top : volume disc ≠ ⊤ := by
  rw [volume_disc]; exact ENNReal.ofReal_ne_top

lemma p4_measurable_hF_sub (m : ℕ) (p : ℂ) : Measurable fun q => hF m (-p - q) :=
  (p4_measurable_hF m).comp (measurable_const.sub measurable_id)

lemma p4_eta_int (m : ℕ) {t : ℝ} {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφt : ∀ q ∈ disc, |φ q| ≤ t) (p : ℂ) :
    IntegrableOn (fun q => hF m (-p - q) * φ q) disc volume ∧
      IntegrableOn (fun q => hF m (-p - q)) disc volume := by
  refine ⟨p4_intOn measurableSet_disc p4_volume_disc_ne_top
    ((p4_measurable_hF_sub m p).mul hφm) (M := (volume disc ^ m).toReal * t) fun q hq => ?_,
    p4_intOn measurableSet_disc p4_volume_disc_ne_top (p4_measurable_hF_sub m p)
      (M := (volume disc ^ m).toReal) fun q _ => ?_⟩
  · rw [abs_mul, abs_of_nonneg (p4_hF_nonneg m _)]
    exact mul_le_mul (p4_hF_le m _) (hφt q hq) (abs_nonneg _) ENNReal.toReal_nonneg
  · rw [abs_of_nonneg (p4_hF_nonneg m _)]; exact p4_hF_le m _

lemma p4_eta_val (m : ℕ) {t : ℝ} {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφt : ∀ q ∈ disc, |φ q| ≤ t) (p : ℂ) :
    ((m + 3 : ℕ) : ℝ)⁻¹ * (aF m p * (t + φ p) +
      (m + 2 : ℝ) * ∫ q in disc, hF m (-p - q) * (t + φ q)) = t * aF m p + Gop m φ p := by
  obtain ⟨h1, h2⟩ := p4_eta_int m hφm hφt p
  have : ∫ q in disc, hF m (-p - q) * (t + φ q) =
      t * aF m p + ∫ q in disc, hF m (-p - q) * φ q := by
    simp_rw [mul_add]
    rw [integral_add (h2.mul_const t) h1, integral_mul_const, p4_integral_hF]; ring
  rw [this, Gop]; push_cast; field_simp; ring

lemma p4_eta_nonneg (m : ℕ) {t : ℝ} {φ : ℂ → ℝ}
    (hφt : ∀ q ∈ disc, |φ q| ≤ t) {p : ℂ} (hp : p ∈ disc) :
    0 ≤ ((m + 3 : ℕ) : ℝ)⁻¹ * (aF m p * (t + φ p) +
      (m + 2 : ℝ) * ∫ q in disc, hF m (-p - q) * (t + φ q)) := by
  have ht : ∀ q ∈ disc, 0 ≤ t + φ q := fun q hq => by linarith [neg_abs_le (φ q), hφt q hq]
  have hI : 0 ≤ ∫ q in disc, hF m (-p - q) * (t + φ q) :=
    setIntegral_nonneg measurableSet_disc fun q hq => mul_nonneg (p4_hF_nonneg m _) (ht q hq)
  have ha : 0 ≤ aF m p := ENNReal.toReal_nonneg
  have := ht p hp
  positivity

lemma p4_feta (m : ℕ) {t : ℝ} {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφt : ∀ q ∈ disc, |φ q| ≤ t) {p : ℂ} (hp : p ∈ disc) :
    ((m + 3 : ℕ) : ℝ≥0∞)⁻¹ * (disc.indicator 1 p * cp (m + 1) (-p) * ENNReal.ofReal (t + φ p) +
      ((m + 3 - 1 : ℕ) : ℝ≥0∞) * ∫⁻ q, disc.indicator 1 p * disc.indicator 1 q *
        cp m (-p - q) * ENNReal.ofReal (t + φ q)) =
    ENNReal.ofReal (((m + 3 : ℕ) : ℝ)⁻¹ * (aF m p * (t + φ p) +
      (m + 2 : ℝ) * ∫ q in disc, hF m (-p - q) * (t + φ q))) := by
  have ht : ∀ q ∈ disc, 0 ≤ t + φ q := fun q hq => by linarith [neg_abs_le (φ q), hφt q hq]
  obtain ⟨h1, h2⟩ := p4_eta_int m hφm hφt p
  have hint : IntegrableOn (fun q => hF m (-p - q) * (t + φ q)) disc volume := by
    simp_rw [mul_add]; exact (h2.mul_const t).add h1
  have hI0 : 0 ≤ ∫ q in disc, hF m (-p - q) * (t + φ q) :=
    setIntegral_nonneg measurableSet_disc fun q hq => mul_nonneg (p4_hF_nonneg m _) (ht q hq)
  have hI : ∫⁻ q, disc.indicator 1 p * disc.indicator 1 q * cp m (-p - q) *
      ENNReal.ofReal (t + φ q) = ENNReal.ofReal (∫ q in disc, hF m (-p - q) * (t + φ q)) := by
    rw [← p4_lint_ind measurableSet_disc
      (fun q hq => mul_nonneg (p4_hF_nonneg m _) (ht q hq)) hint]
    congr 1; ext q
    by_cases hq : q ∈ disc
    · simp [hp, hq, ← p4_ofReal_hF, ENNReal.ofReal_mul (p4_hF_nonneg m _)]
    · simp [hq]
  have ha : 0 ≤ aF m p := ENNReal.toReal_nonneg
  rw [hI, show (m + 3 - 1 : ℕ) = m + 2 by omega, indicator_of_mem hp, Pi.one_apply, one_mul,
    cp_neg, ← p4_ofReal_aF, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_natCast (m + 2),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (mul_nonneg ha (ht p hp))
      (by positivity), ← ENNReal.ofReal_natCast (m + 3),
    ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  push_cast; ring_nf


lemma p4_measurableSet_corner (k : ℕ) : MeasurableSet (corner k) :=
  (measurableSet_poly k).diff measurableSet_disc

lemma p4_volume_corner_ne_top {k : ℕ} (hk : 3 ≤ k) : volume (corner k) ≠ ⊤ :=
  ((measure_mono sdiff_subset).trans_lt (isCompact_poly hk).measure_lt_top).ne

lemma p4_aF_pos {k : ℕ} (hk : 3 ≤ k) (hPL : PLHyp) {m : ℕ}
    (haR : 0 < aF m (Poly.secR k : ℂ)) {p : ℂ} (hp : p ∈ poly k) : 0 < aF m p :=
  haR.trans_le (p4_aF_le hk hPL m hp)

lemma p4_nu_nonneg (m k : ℕ) (hk : 3 ≤ k) (hPL : PLHyp) (haR : 0 < aF m (Poly.secR k : ℂ))
    (q : ℂ) : 0 ≤ nu m k q := by
  have hA := p4_area_pos hk
  have hI : 0 ≤ ∫ p in corner k, hF m (-p - q) / aF m p :=
    setIntegral_nonneg (p4_measurableSet_corner k) fun p hp =>
      div_nonneg (p4_hF_nonneg m _) (p4_aF_pos hk hPL haR hp.1).le
  unfold nu; positivity

lemma p4_measurable_nu (m k : ℕ) : Measurable (nu m k) := by
  have hf : Measurable (Function.uncurry fun q p : ℂ => hF m (-p - q) / aF m p) :=
    ((p4_measurable_hF m).comp (measurable_snd.neg.sub measurable_fst)).div
      ((p4_measurable_aF m).comp measurable_snd)
  exact measurable_const.mul
    (hf.stronglyMeasurable.integral_prod_right (ν := volume.restrict (corner k))).measurable

lemma p4_measurable_nus (m k : ℕ) : Measurable (nus m k) := by
  have h : nus m k = fun q => ((m + 3 : ℕ) : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (m + 3), nu m k ((fun z => nrm (m + 3) 1 * z)^[i] q) := rfl
  rw [h]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact (p4_measurable_nu m k).comp ((continuous_const.mul continuous_id).measurable.iterate i)

lemma p4_fC_disc (m k : ℕ) (hk : 3 ≤ k) (hPL : PLHyp) (haR : 0 < aF m (Poly.secR k : ℂ))
    {q : ℂ} (hq : q ∈ disc) :
    (corner k).indicator 1 q * cp (m + 1) (-q) * ENNReal.ofReal ((aF m q)⁻¹ / Poly.area k) +
      ((m + 3 - 1 : ℕ) : ℝ≥0∞) * ∫⁻ p, (corner k).indicator 1 p * disc.indicator 1 q *
        cp m (-p - q) * ENNReal.ofReal ((aF m p)⁻¹ / Poly.area k) =
    ENNReal.ofReal (nu m k q) := by
  have hA := p4_area_pos hk
  have hqC : q ∉ corner k := fun h => h.2 hq
  have hC := p4_measurableSet_corner k
  have h0 : ∀ p ∈ corner k, 0 ≤ hF m (-p - q) * ((aF m p)⁻¹ / Poly.area k) := fun p hp =>
    mul_nonneg (p4_hF_nonneg m _) (div_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hA.le)
  have hint : IntegrableOn (fun p => hF m (-p - q) * ((aF m p)⁻¹ / Poly.area k))
      (corner k) volume := by
    refine p4_intOn hC (p4_volume_corner_ne_top hk)
      (((p4_measurable_hF m).comp (measurable_id.neg.sub measurable_const)).mul
        (((p4_measurable_aF m).inv).div_const _))
      (M := (volume disc ^ m).toReal * ((aF m (Poly.secR k : ℂ))⁻¹ / Poly.area k))
      fun p hp => ?_
    rw [abs_of_nonneg (h0 p hp)]
    exact mul_le_mul (p4_hF_le m _) (div_le_div_of_nonneg_right
      (inv_anti₀ haR (p4_aF_le hk hPL m hp.1)) hA.le)
      (div_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hA.le) ENNReal.toReal_nonneg
  have hI : ∫⁻ p, (corner k).indicator 1 p * disc.indicator 1 q * cp m (-p - q) *
      ENNReal.ofReal ((aF m p)⁻¹ / Poly.area k) =
      ENNReal.ofReal (∫ p in corner k, hF m (-p - q) * ((aF m p)⁻¹ / Poly.area k)) := by
    rw [← p4_lint_ind hC h0 hint]
    congr 1; ext p
    by_cases hp : p ∈ corner k
    · simp [hp, hq, ← p4_ofReal_hF, ENNReal.ofReal_mul (p4_hF_nonneg m _)]
    · simp [hp]
  have hI0 : 0 ≤ ∫ p in corner k, hF m (-p - q) * ((aF m p)⁻¹ / Poly.area k) :=
    setIntegral_nonneg hC h0
  have hfun : (fun p => hF m (-p - q) * ((aF m p)⁻¹ / Poly.area k)) =
      fun p => hF m (-p - q) / aF m p / Poly.area k := by ext p; ring
  rw [hI, indicator_of_notMem hqC, zero_mul, zero_mul, zero_add,
    show (m + 3 - 1 : ℕ) = m + 2 by omega, ← ENNReal.ofReal_natCast (m + 2),
    ← ENNReal.ofReal_mul (by positivity), hfun, integral_div, nu]
  congr 1; push_cast; ring

lemma p4_fC_corner (m k : ℕ) (hk : 3 ≤ k) (hPL : PLHyp) (haR : 0 < aF m (Poly.secR k : ℂ))
    {q : ℂ} (hq : q ∈ corner k) :
    (corner k).indicator 1 q * cp (m + 1) (-q) * ENNReal.ofReal ((aF m q)⁻¹ / Poly.area k) +
      ((m + 3 - 1 : ℕ) : ℝ≥0∞) * ∫⁻ p, (corner k).indicator 1 p * disc.indicator 1 q *
        cp m (-p - q) * ENNReal.ofReal ((aF m p)⁻¹ / Poly.area k) =
    ENNReal.ofReal (1 / Poly.area k) := by
  have ha := p4_aF_pos hk hPL haR hq.1
  simp only [indicator_of_mem hq, indicator_of_notMem hq.2, Pi.one_apply, one_mul, mul_zero,
    zero_mul, lintegral_zero, add_zero, ← p4_ofReal_aF]
  rw [show aF m (-q) = aF m q by simp only [aF, cp_neg], ← ENNReal.ofReal_mul ha.le]
  congr 1; field_simp

lemma p4_fC_out (m k : ℕ) {q : ℂ} (hq : q ∉ poly k) :
    (corner k).indicator 1 q * cp (m + 1) (-q) * ENNReal.ofReal ((aF m q)⁻¹ / Poly.area k) +
      ((m + 3 - 1 : ℕ) : ℝ≥0∞) * ∫⁻ p, (corner k).indicator 1 p * disc.indicator 1 q *
        cp m (-p - q) * ENNReal.ofReal ((aF m p)⁻¹ / Poly.area k) = 0 := by
  have h1 : q ∉ corner k := fun h => hq h.1
  have h2 : q ∉ disc := fun h => hq (disc_subset_poly k h)
  simp [indicator_of_notMem h1, indicator_of_notMem h2]


lemma p4_iter_rot {n : ℕ} (hn : 0 < n) : (fun z : ℂ => nrm n 1 * z)^[n] = id := by
  rw [mul_left_iterate, nrm_pow, nrm_self hn]
  funext z; simp

/-- **Theorem 95 (measure-theoretic assembly).** Given the corrector `φ` with `|φ| ≤ t` on the
disc `B`, `Gφ = -(ν - ν_s)` a.e. on `B`, and condition (22), the uniform distribution on the
regular `k`-gon `P_k` is `(m+3)`-completely mixable. -/
theorem thm95_of_phi (hPL : PLHyp) (m k : ℕ) (hk : 3 ≤ k)
    (haR : 0 < aF m (Poly.secR k : ℂ)) {t : ℝ} {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφt : ∀ q ∈ disc, |φ q| ≤ t)
    (hG : ∀ᵐ p ∂(volume : Measure ℂ), p ∈ disc → Gop m φ p = -(nu m k p - nus m k p))
    (h22 : ∀ q ∈ disc, nus m k q + t * aF m q ≤ 1 / Poly.area k) :
    CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) := by
  have hn2 : 2 ≤ m + 3 := by omega
  have hA := p4_area_pos hk
  have hCm := p4_measurableSet_corner k
  have hPm := measurableSet_poly k
  have hDm := measurableSet_disc
  have hDP := disc_subset_poly k
  have hu1 : ‖nrm (m + 3) 1‖ = 1 := norm_nrm
  set w : ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal ((aF m p)⁻¹ / Poly.area k) with hw
  have hwm : Measurable w :=
    ENNReal.measurable_ofReal.comp (((p4_measurable_aF m).inv).div_const _)
  set ψ : ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (t + φ q) with hψ
  have hψm : Measurable ψ := ENNReal.measurable_ofReal.comp (measurable_const.add hφm)
  have hgm : ∀ K0 : Set ℂ, MeasurableSet K0 → Measurable (Function.uncurry fun p q : ℂ =>
      K0.indicator (1 : ℂ → ℝ≥0∞) p * disc.indicator 1 q * cp m (-p - q)) := fun K0 hK0 =>
    (((measurable_one.indicator hK0).comp measurable_fst).mul
      ((measurable_one.indicator hDm).comp measurable_snd)).mul
      ((measurable_cp m).comp (measurable_fst.neg.sub measurable_snd))
  have hAm : ∀ K0 : Set ℂ, MeasurableSet K0 →
      Measurable fun p : ℂ => K0.indicator (1 : ℂ → ℝ≥0∞) p * cp (m + 1) (-p) := fun K0 hK0 =>
    (measurable_one.indicator hK0).mul ((measurable_cp _).comp measurable_neg)
  set βC := ((m + 3 : ℕ) : ℝ≥0∞) • symmetrise ((lamG m (corner k)).withDensity fun x => w (x 0))
    with hβC
  set βη := (lamG m disc).withDensity fun x => ((m + 3 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, ψ (x i)
    with hβη
  have hmC := Poly.corner_marginal (lamC := lamG m (corner k)) (i0 := 0) (hAm _ hCm)
    (hgm _ hCm) (lamG_map_zero m hCm) (fun j hj => lamG_map_pair m hCm j hj) hwm
  have hmη := Poly.marginal_withDensity_sum hn2 (permInvariant_lamG m) (i0 := 0) (i1 := 1)
    (by simp) (hAm _ hDm) (hgm _ hDm) (lamG_map_zero m hDm) (lamG_map_pair m hDm 1 (by simp))
    hψm
  set fC := fun q => (corner k).indicator 1 q * cp (m + 1) (-q) * w q +
      ((m + 3 - 1 : ℕ) : ℝ≥0∞) * ∫⁻ p, (corner k).indicator 1 p * disc.indicator 1 q *
        cp m (-p - q) * w p with hfC
  set fη := fun p => ((m + 3 : ℕ) : ℝ≥0∞)⁻¹ * (disc.indicator 1 p * cp (m + 1) (-p) * ψ p +
      ((m + 3 - 1 : ℕ) : ℝ≥0∞) * ∫⁻ q, disc.indicator 1 p * disc.indicator 1 q *
        cp m (-p - q) * ψ q) with hfη
  have hfηm : Measurable fη :=
    measurable_const.mul (((hAm _ hDm).mul hψm).add (measurable_const.mul
      (Measurable.lintegral_prod_right' ((hgm _ hDm).mul (hψm.comp measurable_snd)))))
  have hmar : marginal (βC + βη) = volume.withDensity (fC + fη) := by
    rw [marginal_add, withDensity_add_right _ hfηm, hmC, hmη]
  set dR : ℂ → ℝ := disc.indicator fun q => 1 / Poly.area k - t * aF m q - nus m k q with hdR
  have hdRm : Measurable dR :=
    ((measurable_const.sub (measurable_const.mul (p4_measurable_aF m))).sub
      (p4_measurable_nus m k)).indicator hDm
  have hmemQ : ∀ q, nrm (m + 3) 1 * q ∈ disc ↔ q ∈ disc := fun q => by
    simp only [disc, Metric.mem_closedBall, dist_zero_right, norm_mul, hu1, one_mul]
  refine p4_cm_ae (n := m + 3) (by omega) (rot (nrm (m + 3) 1)) (rot_pow_eq_one (by omega))
    (rot_fix hn2) (measurePreserving_rot hu1) (isCompact_poly hk) (volume_poly_pos k)
    (centroid_poly hk) hDm hDP (fun x hx => (hmemQ x).2 hx) (βC + βη) ?_ ?_ hdRm hmar ?_ ?_ ?_
  · exact permInvariant_add (permInvariant_smul _ (permInvariant_symmetrise _))
      (p4_permInvariant_withDensity (permInvariant_lamG m)
        (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
          hψm.comp (measurable_pi_apply i)))
        fun σ x => by simp only [Function.comp_apply]; rw [Equiv.sum_comp σ (fun i => ψ (x i))])
  · rw [add_apply, hβC, hβη, smul_apply,
      symmetrise_null _ (measurableSet_tuples hPm 0).compl (tuples_perm (poly k) 0)
        (withDensity_absolutelyContinuous _ _ (lamG_tuples m hCm sdiff_subset hDP hPm)),
      withDensity_absolutelyContinuous _ _ (lamG_tuples m hDm hDP hDP hPm)]
    simp
  · intro q hq; simp [hdR, hq]
  · intro q
    rw [rot_apply, hdR]
    by_cases hq : q ∈ disc
    · rw [indicator_of_mem ((hmemQ q).2 hq), indicator_of_mem hq]
      simp only [aF, cp_rot (m + 1) hu1]
      rw [show nus m k (nrm (m + 3) 1 * q) = nus m k q from
        Poly.avgRot_comp (m + 3) (p4_iter_rot (by omega)) _ q]
    · rw [indicator_of_notMem (mt (hmemQ q).1 hq), indicator_of_notMem hq]
  · filter_upwards [hG] with q hGq
    rw [p4_vol_poly_toReal hk, Pi.add_apply]
    by_cases hqD : q ∈ disc
    · have h1 := p4_nu_nonneg m k hk hPL haR q
      have h2 : 0 ≤ t * aF m q + Gop m φ q := by
        rw [← p4_eta_val m hφm hφt]; exact p4_eta_nonneg m hφt hqD
      have h3 : 0 ≤ 1 / Poly.area k - t * aF m q - nus m k q := by linarith [h22 q hqD]
      rw [hfC, hfη]
      simp only
      rw [p4_fC_disc m k hk hPL haR hqD, p4_feta m hφm hφt hqD, p4_eta_val m hφm hφt,
        hdR, indicator_of_mem hqD, indicator_of_mem (hDP hqD), Pi.one_apply,
        ← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3]
      congr 1; rw [hGq hqD]; ring
    · by_cases hqP : q ∈ poly k
      · have hqC : q ∈ corner k := ⟨hqP, hqD⟩
        rw [hfC, hfη]
        simp only
        rw [p4_fC_corner m k hk hPL haR hqC, hdR, indicator_of_notMem hqD,
          indicator_of_mem hqP]
        simp [hqD]
      · rw [hfC, hfη]
        simp only
        rw [p4_fC_out m k hqP, hdR, indicator_of_notMem hqD, indicator_of_notMem hqP]
        simp [hqD]

end P4

section P3a

/-- Disc-indicator of a `κ`-mode is a `κ`-mode. -/
lemma p3a_isMode_ind {κ : ℤ} {f : ℂ → ℂ} (hf : IsMode κ f) : IsMode κ (disc.indicator f) := by
  intro α q
  by_cases hq : q ∈ disc
  · rw [indicator_of_mem ((mul_mem_disc_iff (p1_exp_norm α) q).2 hq), indicator_of_mem hq, hf]
  · rw [indicator_of_notMem (mt (mul_mem_disc_iff (p1_exp_norm α) q).1 hq),
      indicator_of_notMem hq, mul_zero]

/-- The Neumann step operator. -/
def p3aK (m : ℕ) (ψ : ℂ → ℂ) : ℂ → ℂ :=
  disc.indicator fun p => -((m + 2 : ℂ) * Top m ψ p) / (aF m p : ℂ)

/-- Good functions: measurable `κ`-modes vanishing off the disc, bounded by `B`. -/
def p3aGood (κ : ℤ) (B : ℝ) (ψ : ℂ → ℂ) : Prop :=
  IsMode κ ψ ∧ Measurable ψ ∧ (∀ q, q ∉ disc → ψ q = 0) ∧ ∀ q, ‖ψ q‖ ≤ B

lemma p3a_good_K (hPL : PLHyp) (m : ℕ) {k : ℕ} (hk : 0 < k) {κ : ℤ}
    (hκ : (k : ℝ) ≤ |(κ : ℝ)|) (ha : 0 < aF m 1) {B : ℝ} {ψ : ℂ → ℂ}
    (hψ : p3aGood κ B ψ) :
    p3aGood κ ((m + 2) * hF m 0 / (k * aF m 1) * B) (p3aK m ψ) := by
  obtain ⟨hmo, hme, hz, hb⟩ := hψ
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hκ0 : κ ≠ 0 := by
    rintro rfl; simp at hκ; linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  refine ⟨p3a_isMode_ind ?_, ?_, ?_, ?_⟩
  · intro α p
    have hu := p1_exp_norm α
    beta_reduce
    rw [isMode_Top m hmo α p, p2_aF_rot hu]
    ring
  · exact Measurable.indicator (((measurable_Top m hme).const_mul _).neg.div
      (Complex.measurable_ofReal.comp (measurable_aF m))) measurableSet_disc
  · intro q hq; simp [p3aK, hq]
  · intro q
    by_cases hq : q ∈ disc
    · have hT := norm_Top_le hPL m hκ0 hmo hme (fun q _ => hb q) q
      have hap := aF_ge_one hPL (m := m) hq
      have hap0 : 0 < aF m q := ha.trans_le hap
      have hc0 := hF_nonneg m 0
      simp only [p3aK, indicator_of_mem hq, norm_div, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hap0.le]
      have h2 : ‖(m + 2 : ℂ)‖ = m + 2 := by
        rw [show (m + 2 : ℂ) = ((m + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h2, div_le_iff₀ hap0]
      have hT' : ‖Top m ψ q‖ ≤ hF m 0 * B / k :=
        hT.trans (div_le_div_of_nonneg_left (by positivity) hkr hκ)
      calc (m + 2 : ℝ) * ‖Top m ψ q‖ ≤ (m + 2) * (hF m 0 * B / k) := by gcongr
        _ = (m + 2) * hF m 0 / (k * aF m 1) * B * aF m 1 := by field_simp
        _ ≤ _ := by gcongr
    · simp only [p3aK, indicator_of_notMem hq, norm_zero]
      have := hF_nonneg m 0
      positivity

/-- **Theorem 95, a correction on each frequency.** Neumann-series inversion of `G` on
`κ`-modes, `|κ| ≥ k`. -/
theorem mode_solve (hPL : PLHyp) (m : ℕ) {k : ℕ} (hk : 0 < k) {κ : ℤ}
    (hκ : (k : ℝ) ≤ |(κ : ℝ)|) (ha1 : (m + 2) * hF m 0 / k < aF m 1)
    {h : ℂ → ℂ} (hh : IsMode κ h) (hhm : Measurable h) {M : ℝ}
    (hM : ∀ q ∈ disc, ‖h q‖ ≤ M) :
    ∃ ψ : ℂ → ℂ, IsMode κ ψ ∧ Measurable ψ ∧ (∀ q, q ∉ disc → ψ q = 0) ∧
      (∀ q ∈ disc, ‖ψ q‖ ≤ (m + 3) * M / (aF m 1 - (m + 2) * hF m 0 / k)) ∧
      ∀ p ∈ disc, (aF m p : ℂ) * ψ p + (m + 2) * Top m ψ p = (m + 3) * h p := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hc0 := hF_nonneg m 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [disc]))
  have ha : 0 < aF m 1 := lt_of_le_of_lt (by positivity) ha1
  set θ : ℝ := (m + 2) * hF m 0 / (k * aF m 1) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one (by positivity)]
    have := (div_lt_iff₀ hkr).1 ha1
    linarith
  set M₀ : ℝ := (m + 3) * M / aF m 1
  set h₀ : ℂ → ℂ := disc.indicator fun p => (m + 3 : ℂ) * h p / (aF m p : ℂ) with hh₀
  have hg0 : p3aGood κ M₀ h₀ := by
    refine ⟨p3a_isMode_ind ?_, ?_, ?_, ?_⟩
    · intro α p
      beta_reduce
      rw [hh α p, p2_aF_rot (p1_exp_norm α)]
      ring
    · exact Measurable.indicator ((hhm.const_mul _).div
        (Complex.measurable_ofReal.comp (measurable_aF m))) measurableSet_disc
    · intro q hq; simp [hh₀, hq]
    · intro q
      by_cases hq : q ∈ disc
      · have hap := aF_ge_one hPL (m := m) hq
        have hap0 : 0 < aF m q := ha.trans_le hap
        simp only [hh₀, indicator_of_mem hq, norm_div, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hap0.le]
        have h3 : ‖(m + 3 : ℂ)‖ = m + 3 := by
          rw [show (m + 3 : ℂ) = ((m + 3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        rw [h3]
        calc (m + 3 : ℝ) * ‖h q‖ / aF m q ≤ (m + 3) * M / aF m q := by
              gcongr; exact hM q hq
          _ ≤ M₀ := div_le_div_of_nonneg_left (by positivity) ha hap
      · simp only [hh₀, indicator_of_notMem hq, norm_zero]; positivity
  set φ : ℕ → ℂ → ℂ := fun j => (p3aK m)^[j] h₀ with hφ
  have hgood : ∀ j, p3aGood κ (θ ^ j * M₀) (φ j) := by
    intro j
    induction j with
    | zero => simpa [hφ] using hg0
    | succ j ih =>
      have := p3a_good_K hPL m hk hκ ha ih
      show p3aGood κ _ ((p3aK m)^[j + 1] h₀)
      rw [Function.iterate_succ_apply']
      convert this using 1; rw [hθ]; ring
  have hsum : ∀ q, Summable fun j => φ j q := fun q =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_right M₀)
      fun j => (hgood j).2.2.2 q
  set ψ : ℂ → ℂ := fun q => ∑' j, φ j q with hψ
  have hψb : ∀ q, ‖ψ q‖ ≤ M₀ / (1 - θ) := by
    intro q
    have := tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one hθ0 hθ1).mul_right M₀) fun j => (hgood j).2.2.2 q
    simpa [div_eq_inv_mul, mul_comm] using this
  have hψm : Measurable ψ := by
    refine measurable_of_tendsto_metrizable (f := fun n q => ∑ j ∈ Finset.range n, φ j q)
      (fun n => Finset.measurable_sum _ fun j _ => (hgood j).2.1) ?_
    exact tendsto_pi_nhds.2 fun q => (hsum q).hasSum.tendsto_sum_nat
  have hfin : IsFiniteMeasure (volume.restrict disc) :=
    isFiniteMeasure_restrict.2 p4_volume_disc_ne_top
  have hTop : ∀ p, Top m ψ p = ∑' j, Top m (φ j) p := by
    intro p
    have hint : ∀ j, Integrable (fun q => (hF m (-p - q) : ℂ) * φ j q) (volume.restrict disc) :=
      fun j => Integrable.of_bound ((Complex.measurable_ofReal.comp
        ((measurable_hF m).comp (Continuous.measurable (by fun_prop)))).mul
          (hgood j).2.1).aestronglyMeasurable (hF m 0 * (θ ^ j * M₀))
          (Filter.Eventually.of_forall fun q => by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hF_nonneg _ _)]
            exact mul_le_mul (hF_le hPL _) ((hgood j).2.2.2 q) (norm_nonneg _) hc0)
    have hs : Summable fun j => ∫ q in disc, ‖(hF m (-p - q) : ℂ) * φ j q‖ := by
      refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun q => norm_nonneg _)
        (fun j => ?_) (((summable_geometric_of_lt_one hθ0 hθ1).mul_right
          (M₀ * hF m 0 * volume.real disc)))
      have := norm_setIntegral_le_of_norm_le_const (s := disc) (μ := volume)
        (f := fun q => ‖(hF m (-p - q) : ℂ) * φ j q‖) (C := hF m 0 * (θ ^ j * M₀))
        p4_volume_disc_ne_top.lt_top (fun q _ => by
          rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hF_nonneg _ _)]
          exact mul_le_mul (hF_le hPL _) ((hgood j).2.2.2 q) (norm_nonneg _) hc0)
      rw [Real.norm_of_nonneg (integral_nonneg fun q => norm_nonneg _)] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    unfold Top
    rw [integral_tsum_of_summable_integral_norm hint hs]
    congr 1; funext q
    rw [hψ, tsum_mul_left]
  refine ⟨ψ, ?_, hψm, ?_, ?_, ?_⟩
  · intro α q
    simp only [hψ]
    rw [← tsum_mul_left]
    congr 1; funext j
    exact (hgood j).1 α q
  · intro q hq
    simp only [hψ]
    rw [tsum_congr fun j => (hgood j).2.2.1 q hq, tsum_zero]
  · intro q _
    refine (hψb q).trans (le_of_eq ?_)
    have : aF m 1 - (m + 2) * hF m 0 / k = aF m 1 * (1 - θ) := by
      rw [hθ]; field_simp
    rw [this, show M₀ = (m + 3) * M / aF m 1 from rfl, div_div]
  · intro p hp
    have hap0 : 0 < aF m p := ha.trans_le (aF_ge_one hPL hp)
    have hap : (aF m p : ℂ) ≠ 0 := by exact_mod_cast hap0.ne'
    have hdec : ψ p = h₀ p + ∑' j, p3aK m (φ j) p := by
      simp only [hψ]
      rw [(hsum p).tsum_eq_zero_add]
      congr 1
      refine tsum_congr fun j => ?_
      simp only [hφ, Function.iterate_succ_apply']
    have hK : ∑' j, p3aK m (φ j) p = -((m + 2 : ℂ) * Top m ψ p) / (aF m p : ℂ) := by
      simp only [p3aK, indicator_of_mem hp]
      rw [tsum_div_const, tsum_neg, tsum_mul_left, hTop p]
    rw [hK] at hdec
    simp only [hh₀, indicator_of_mem hp] at hdec
    rw [hdec]
    field_simp
    ring

end P3a

section P3b

open Filter Topology

/-- A pointwise `tsum` (summable everywhere) of measurable functions is measurable. -/
lemma p3b_measurable_tsum {f : ℤ → ℂ → ℂ} (hf : ∀ κ, Measurable (f κ))
    (hs : ∀ p, Summable fun κ => f κ p) : Measurable fun p => ∑' κ, f κ p := by
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ))
    (f := fun s p => ∑ κ ∈ s, f κ p) (fun s => Finset.measurable_sum s (fun κ _ => hf κ)) ?_
  rw [tendsto_pi_nhds]; intro p; exact (hs p).hasSum

/-- A measurable set meeting almost no point of each circle orbit is null. -/
lemma p3b_null_of_rot {N : Set ℂ} (hN : MeasurableSet N)
    (h : ∀ q, ∀ᵐ (θ : ℝ), Complex.exp ((θ : ℂ) * Complex.I) * q ∉ N) :
    volume N = 0 := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  set g : ℝ → ℂ → ℝ≥0∞ := fun θ q =>
    N.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.exp ((θ : ℂ) * Complex.I) * q) with hg
  have hmeas : Measurable (Function.uncurry g) :=
    (measurable_const.indicator hN).comp (Continuous.measurable (by fun_prop))
  have h1 : ∫⁻ θ, ∫⁻ q, g θ q ∂volume ∂μ = ∫⁻ _θ, volume N ∂μ := by
    apply lintegral_congr; intro θ
    have := (measurePreserving_rot (p1_exp_norm θ)).lintegral_comp
      (f := N.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hN)
    simp only [rot_apply] at this
    rw [hg]; simp only; rw [this, lintegral_indicator_const hN, one_mul]
  have h2 : ∫⁻ θ, ∫⁻ q, g θ q ∂volume ∂μ = 0 := by
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have : ∀ q, ∫⁻ θ, g θ q ∂μ = 0 := by
      intro q
      rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
      filter_upwards [ae_restrict_of_ae (h q)] with θ hθ
      simp [hg, hθ]
    simp [this]
  rw [h2, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc] at h1
  rcases mul_eq_zero.1 h1.symm with h | h
  · exact h
  · exfalso; rw [ENNReal.ofReal_eq_zero] at h; linarith [pi_pos]

/-- The coefficient bound on the frequencies `κ` with `k ∣ κ`, `n ∤ κ` (else `0`). -/
def p3bB (m k : ℕ) (c aR : ℝ) (κ : ℤ) : ℝ :=
  if (k : ℤ) ∣ κ ∧ ¬ ((m + 3 : ℕ) : ℤ) ∣ κ then
    (m + 2) * k * c * (Poly.secR k ^ 2 - 1) / (π * Poly.area k * aR * (κ : ℝ) ^ 2) else 0

/-- The bounds `p3bB` sum to `W`. -/
lemma p3b_hasSum (m k : ℕ) (hk : 3 ≤ k) (c aR : ℝ) (haR : aR ≠ 0) :
    HasSum (p3bB m k c aR) (Poly.W (m + 3) k c aR (Poly.Ssum (m + 3) k)) := by
  have hk0 : 0 < k := by omega
  set b := p3bB m k c aR with hb
  have hneg : ∀ κ, b (-κ) = b κ := by
    intro κ; simp only [hb, p3bB, dvd_neg, Int.cast_neg, neg_sq]
  have hrange : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ => j * k) → 2 * b n = 0 := by
    intro n hn
    have : ¬ (k : ℤ) ∣ (n : ℤ) := by
      intro hd
      obtain ⟨j, rfl⟩ := Int.natCast_dvd_natCast.mp hd
      exact hn ⟨j, mul_comm _ _⟩
    simp [hb, p3bB, this]
  have hcomp : ∀ j : ℕ, 2 * b ((j * k : ℕ) : ℤ) = (if ¬ (m + 3) ∣ j * k then
      2 * (((m + 3 : ℕ) - 1) * c * tan (π / k) / (π * k ^ 2 * aR) * (1 / (j : ℝ) ^ 2))
      else 0) := by
    intro j
    by_cases hd : (m + 3) ∣ j * k
    · have : ((m + 3 : ℕ) : ℤ) ∣ ((j * k : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hd
      simp only [hb, p3bB, this, hd, not_true_eq_false, and_false, ite_false, mul_zero]
    · have hj : j ≠ 0 := by rintro rfl; simp at hd
      have hkd : (k : ℤ) ∣ ((j * k : ℕ) : ℤ) := ⟨j, by push_cast; ring⟩
      have hmd : ¬ ((m + 3 : ℕ) : ℤ) ∣ ((j * k : ℕ) : ℤ) := by
        rwa [Int.natCast_dvd_natCast]
      simp only [hb, p3bB, hkd, hmd, hd, not_false_eq_true, and_self, ite_true]
      rw [← Poly.coeff_bound_eq (n := m + 3) hk c aR haR hj]; push_cast; ring
  have hinj : Function.Injective (fun j : ℕ => j * k) :=
    fun a b h => Nat.eq_of_mul_eq_mul_right hk0 h
  have hF : HasSum (fun n : ℕ => 2 * b n) (Poly.W (m + 3) k c aR (Poly.Ssum (m + 3) k)) := by
    rw [← hinj.hasSum_iff hrange]
    convert Poly.hasSum_W (m + 3) k c aR using 1
    funext j; exact hcomp j
  have h1 : HasSum (fun n : ℕ => b n) (Poly.W (m + 3) k c aR (Poly.Ssum (m + 3) k) / 2) := by
    convert hF.div_const 2 using 1; funext n; ring
  have h2 : HasSum (fun n : ℕ => b (-n)) (Poly.W (m + 3) k c aR (Poly.Ssum (m + 3) k) / 2) := by
    simpa [hneg] using h1
  have h0 : b 0 = 0 := by simp [hb, p3bB]
  convert h1.of_nat_of_neg h2 using 1; rw [h0]; ring

/-- For `q ∈ B` the angular Fourier coefficients of `ν` at `q` are absolutely summable. -/
lemma p3b_summable (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ))
    {q : ℂ} (hq : q ∈ disc) :
    Summable fun κ : ℤ => proj κ (fun z => (nu m k z : ℂ)) q := by
  set C := (m + 2) * k * hF m 0 * (Poly.secR k ^ 2 - 1) /
    (π * Poly.area k * aF m (Poly.secR k : ℂ)) with hC
  set Nb := Mixes.Poly.Nb (m + 3) k (hF m 0) (aF m (Poly.secR k : ℂ))
  have hs : Summable fun κ : ℤ => C * (1 / (κ : ℝ) ^ 2) + (if κ = 0 then Nb else 0) :=
    ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left C).add
      (hasSum_ite_eq (0 : ℤ) Nb).summable
  refine hs.of_norm_bounded (fun κ => ?_)
  by_cases h0 : κ = 0
  · subst h0
    have := norm_proj_le 0 (f := fun z => (nu m k z : ℂ)) (M := Nb) (fun z => by
      rw [Complex.norm_real, Real.norm_of_nonneg (nu_nonneg m hk z)]
      exact nu_le_Nb hPL hk haR z) q
    simpa using this
  · rw [ite_eq_right h0, add_zero]
    refine (norm_proj_nu_le hPL hk haR h0 q hq).trans_eq ?_
    rw [hC]; ring

/-- Fourier inversion of `ν` on almost every circle, transferred to almost every point (and
its rotations by `2πi/(m+3)`). -/
lemma p3b_good (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ)) :
    ∀ᵐ p ∂(volume : Measure ℂ), ∀ i : ℕ, p ∈ disc →
      (nu m k (nrm (m + 3) i * p) : ℂ) =
        ∑' κ : ℤ, proj κ (fun z => (nu m k z : ℂ)) (nrm (m + 3) i * p) := by
  set νc : ℂ → ℂ := fun z => (nu m k z : ℂ) with hνc
  have hνm : Measurable νc := Complex.measurable_ofReal.comp (measurable_nu m k)
  set Nb := Mixes.Poly.Nb (m + 3) k (hF m 0) (aF m (Poly.secR k : ℂ))
  have hνb : ∀ z, ‖νc z‖ ≤ Nb := fun z => by
    simp only [hνc, Complex.norm_real, Real.norm_of_nonneg (nu_nonneg m hk z)]
    exact nu_le_Nb hPL hk haR z
  set S : ℂ → ℂ := fun p => ∑' κ : ℤ, disc.indicator (proj κ νc) p with hS
  have hSm : Measurable S := p3b_measurable_tsum
    (fun κ => (measurable_proj κ hνm).indicator measurableSet_disc) (fun p => by
      by_cases hp : p ∈ disc
      · simpa [indicator_of_mem hp] using p3b_summable hPL hk haR hp
      · simp [indicator_of_notMem hp])
  set N := {p | p ∈ disc ∧ νc p ≠ S p} with hN
  have hNm : MeasurableSet N := measurableSet_disc.inter (measurableSet_eq_fun hνm hSm).compl
  have hN0 : volume N = 0 := by
    apply p3b_null_of_rot hNm
    intro q
    by_cases hq : q ∈ disc
    · have hf := fourier_ae (f := fun θ : ℝ => νc (Complex.exp ((θ : ℂ) * Complex.I) * q))
        (hνm.comp (Continuous.measurable (by fun_prop))) (fun θ => by simp only [p2_exp_periodic])
        (M := Nb) (fun θ => hνb _) (p3b_summable hPL hk haR hq).norm
      filter_upwards [hf] with θ hθ
      rintro ⟨-, hne⟩
      apply hne
      have hmem : Complex.exp ((θ : ℂ) * Complex.I) * q ∈ disc :=
        (mul_mem_disc_iff (p1_exp_norm θ) q).2 hq
      simp only [hS, indicator_of_mem hmem]
      rw [hθ]
      refine tsum_congr fun κ => ?_
      rw [isMode_proj κ νc θ q, mul_comm]; rfl
    · exact Eventually.of_forall fun θ h => hq ((mul_mem_disc_iff (p1_exp_norm θ) q).1 h.1)
  have hall : ∀ i : ℕ, ∀ᵐ p ∂(volume : Measure ℂ), nrm (m + 3) i * p ∉ N := by
    intro i
    have h := (measurePreserving_rot (norm_nrm (k := m + 3) (j := i))).measure_preimage
      hNm.nullMeasurableSet
    rw [hN0] at h
    exact measure_eq_zero_iff_ae_notMem.mp h
  filter_upwards [ae_all_iff.2 hall] with p hp i hpd
  have hmem : nrm (m + 3) i * p ∈ disc := (mul_mem_disc_iff norm_nrm p).2 hpd
  by_contra hne
  exact hp i ⟨hmem, by simpa [hS, indicator_of_mem hmem] using hne⟩

lemma p3b_norm_exp (κ : ℤ) (α : ℝ) : ‖Complex.exp ((κ : ℂ) * α * Complex.I)‖ = 1 := by
  rw [show (κ : ℂ) * α * Complex.I = ((κ * α : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **`ν - ν_s` is the sum of the modes `κ ∈ M`**, a.e. on the disc. -/
lemma p3b_fourier (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ)) :
    ∀ᵐ p ∂(volume : Measure ℂ), p ∈ disc →
      ((nu m k p - nus m k p : ℝ) : ℂ) = ∑' κ : ℤ,
        (if (k : ℤ) ∣ κ ∧ ¬ ((m + 3 : ℕ) : ℤ) ∣ κ then
          proj κ (fun z => (nu m k z : ℂ)) p else 0) := by
  filter_upwards [p3b_good hPL hk haR] with p hp hpd
  set νc : ℂ → ℂ := fun z => (nu m k z : ℂ) with hνc
  have hs := p3b_summable hPL hk haR hpd
  have hn : 0 < m + 3 := by omega
  have hrot : ∀ i : ℕ, (nu m k (nrm (m + 3) i * p) : ℂ) = ∑' κ : ℤ,
      Complex.exp ((κ : ℂ) * ((2 * π * i / (m + 3 : ℕ) : ℝ) : ℂ) * Complex.I) *
        proj κ νc p := by
    intro i; rw [hp i hpd]; refine tsum_congr fun κ => ?_
    rw [nrm, isMode_proj]
  have hrs : ∀ i : ℕ, Summable fun κ : ℤ =>
      Complex.exp ((κ : ℂ) * ((2 * π * i / (m + 3 : ℕ) : ℝ) : ℂ) * Complex.I) *
        proj κ νc p :=
    fun i => hs.norm.of_norm_bounded (fun κ => by rw [norm_mul, p3b_norm_exp, one_mul])
  have h0 : (nu m k p : ℂ) = ∑' κ, proj κ νc p := by simpa [nrm] using hp 0 hpd
  have hsym : (nus m k p : ℂ) = ∑' κ : ℤ,
      (if ((m + 3 : ℕ) : ℤ) ∣ κ then proj κ νc p else 0) := by
    unfold nus Poly.avgRot
    simp only [mul_left_iterate, nrm_pow]
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    simp only [hrot]
    rw [← Summable.tsum_finsetSum (fun i _ => hrs i), ← tsum_mul_left]
    refine tsum_congr fun κ => ?_
    rw [← Finset.sum_mul]
    have he : ∑ i ∈ Finset.range (m + 3),
        Complex.exp ((κ : ℂ) * ((2 * π * i / (m + 3 : ℕ) : ℝ) : ℂ) * Complex.I) =
        ∑ j ∈ Finset.range (m + 3),
          Complex.exp (2 * π * Complex.I * κ * j / ((m + 3 : ℕ) : ℂ)) :=
      Finset.sum_congr rfl fun i _ => by congr 1; push_cast; ring
    rw [he, Poly.sum_exp_root (m + 3) hn κ]
    have hn' : ((m + 3 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    split_ifs
    · rw [Complex.ofReal_inv, Complex.ofReal_natCast]; field_simp
    · simp
  have hsi : Summable fun κ : ℤ => (if ((m + 3 : ℕ) : ℤ) ∣ κ then proj κ νc p else 0) :=
    hs.norm.of_norm_bounded (fun κ => by split_ifs <;> first | exact le_rfl | simp)
  rw [Complex.ofReal_sub, h0, hsym, ← Summable.tsum_sub hs hsi]
  refine tsum_congr fun κ => ?_
  by_cases hkd : (k : ℤ) ∣ κ
  · by_cases hnd : ((m : ℤ) + 3) ∣ κ <;> simp [hkd, hnd, hνc]
  · rw [proj_nu_eq_zero m hk hkd p]; simp [hkd]

/-- **The correction `φ` of Theorem 95** (equation (st:eq:phi)), given the per-frequency
inversion `hsolve` of `G_κ`. -/
theorem exists_phi (hPL : PLHyp) (m k : ℕ) (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ))
    (ha1 : (m + 2) * hF m 0 / k < aF m 1)
    (hsolve : ∀ {κ : ℤ}, ((k : ℝ) ≤ |(κ : ℝ)|) → ∀ {h : ℂ → ℂ}, IsMode κ h →
      Measurable h → ∀ {M : ℝ}, (∀ q ∈ disc, ‖h q‖ ≤ M) →
      ∃ ψ : ℂ → ℂ, IsMode κ ψ ∧ Measurable ψ ∧ (∀ q, q ∉ disc → ψ q = 0) ∧
        (∀ q ∈ disc, ‖ψ q‖ ≤ (m + 3) * M / (aF m 1 - (m + 2) * hF m 0 / k)) ∧
        ∀ p ∈ disc, (aF m p : ℂ) * ψ p + (m + 2) * Top m ψ p = (m + 3) * h p) :
    ∃ φ : ℂ → ℝ, Measurable φ ∧
      (∀ q ∈ disc, |φ q| ≤ (m + 3) * Poly.W (m + 3) k (hF m 0) (aF m (Poly.secR k : ℂ))
        (Poly.Ssum (m + 3) k) / (aF m 1 - (m + 2) * hF m 0 / k)) ∧
      ∀ᵐ p ∂(volume : Measure ℂ), p ∈ disc → Gop m φ p = -(nu m k p - nus m k p) := by
  set D := aF m 1 - (m + 2) * hF m 0 / k with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  set c := hF m 0 with hc
  set aR := aF m (Poly.secR k : ℂ) with haRdef
  set W := Poly.W (m + 3) k c aR (Poly.Ssum (m + 3) k) with hW
  set νc : ℂ → ℂ := fun z => (nu m k z : ℂ) with hνc
  have hνm : Measurable νc := Complex.measurable_ofReal.comp (measurable_nu m k)
  set b := p3bB m k c aR with hb
  have hbW : HasSum b W := p3b_hasSum m k hk c aR haR.ne'
  have hbs : Summable b := hbW.summable
  set hk' : ℤ → ℂ → ℂ := fun κ =>
    if (k : ℤ) ∣ κ ∧ ¬ ((m + 3 : ℕ) : ℤ) ∣ κ then proj κ νc else 0 with hhk
  have hex : ∀ κ : ℤ, ∃ ψ : ℂ → ℂ, IsMode κ ψ ∧ Measurable ψ ∧
      (∀ q, q ∉ disc → ψ q = 0) ∧
      (∀ q ∈ disc, ‖ψ q‖ ≤ (m + 3) * b κ / D) ∧
      ∀ p ∈ disc, (aF m p : ℂ) * ψ p + (m + 2) * Top m ψ p = (m + 3) * hk' κ p := by
    intro κ
    by_cases hM : (k : ℤ) ∣ κ ∧ ¬ ((m + 3 : ℕ) : ℤ) ∣ κ
    · have hκ0 : κ ≠ 0 := by rintro rfl; exact hM.2 (dvd_zero _)
      have hkκ : (k : ℝ) ≤ |(κ : ℝ)| := by
        obtain ⟨j, rfl⟩ := hM.1
        have hj : j ≠ 0 := by rintro rfl; simp at hκ0
        rw [Int.cast_mul, abs_mul, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg k)]
        have : (1 : ℝ) ≤ |(j : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      obtain ⟨ψ, h1, h2, h3, h4, h5⟩ :=
        hsolve hkκ (isMode_proj κ νc) (measurable_proj κ hνm)
        (M := b κ) (fun q hq => by
          simp only [hb, p3bB, ite_eq_left hM]; exact norm_proj_nu_le hPL hk haR hκ0 q hq)
      exact ⟨ψ, h1, h2, h3, h4, fun p hp => by simp only [hhk, ite_eq_left hM]; exact h5 p hp⟩
    · refine ⟨0, fun α q => by simp, measurable_const, fun _ _ => rfl, fun q _ => ?_,
        fun p _ => ?_⟩
      · rw [hb, p3bB, ite_eq_right hM]; simp
      · simp only [hhk, ite_eq_right hM]; simp [Top]
  choose ψ hψmode hψmeas hψout hψbd hψeq using hex
  have hbD : HasSum (fun κ => (m + 3) * b κ / D) ((m + 3) * W / D) :=
    (hbW.mul_left _).div_const D
  have hψsum : ∀ q, Summable fun κ => ψ κ q := by
    intro q
    by_cases hq : q ∈ disc
    · exact hbD.summable.of_norm_bounded (fun κ => hψbd κ q hq)
    · simp [hψout _ q hq]
  set Ψ : ℂ → ℂ := fun q => ∑' κ, ψ κ q with hΨ
  have hΨm : Measurable Ψ := p3b_measurable_tsum hψmeas hψsum
  have hΨb : ∀ q ∈ disc, ‖Ψ q‖ ≤ (m + 3) * W / D := fun q hq =>
    tsum_of_norm_bounded hbD (fun κ => hψbd κ q hq)
  refine ⟨fun q => -(Ψ q).re, (Complex.measurable_re.comp hΨm).neg, ?_, ?_⟩
  · intro q hq
    rw [abs_neg]
    exact (Complex.abs_re_le_norm _).trans (hΨb q hq)
  have : IsFiniteMeasure (volume.restrict disc) :=
    isFiniteMeasure_restrict.2 p4_volume_disc_ne_top
  have hc0 : 0 ≤ c := hF_nonneg _ _
  have hG : ∀ p ∈ disc, Gop m (fun q => -(Ψ q).re) p = -(∑' κ, hk' κ p).re := by
    intro p hp
    have hmeasF : ∀ g : ℂ → ℂ, Measurable g →
        Measurable fun q => (hF m (-p - q) : ℂ) * g q := fun g hg =>
      (Complex.measurable_ofReal.comp ((measurable_hF m).comp
        (measurable_const.sub measurable_id))).mul hg
    have hFb : ∀ (g : ℂ → ℂ) (C : ℝ), (∀ q ∈ disc, ‖g q‖ ≤ C) →
        ∀ᵐ q ∂(volume.restrict disc), ‖(hF m (-p - q) : ℂ) * g q‖ ≤ c * C := by
      intro g C hg
      filter_upwards [ae_restrict_mem measurableSet_disc] with q hq
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hF_nonneg _ _)]
      exact mul_le_mul (hF_le hPL _) (hg q hq) (norm_nonneg _) hc0
    have hFint : ∀ κ, Integrable (fun q => (hF m (-p - q) : ℂ) * ψ κ q)
        (volume.restrict disc) := fun κ =>
      Integrable.of_bound (hmeasF _ (hψmeas κ)).aestronglyMeasurable _ (hFb _ _ (hψbd κ))
    have hnI : ∀ κ, ∫ q in disc, ‖(hF m (-p - q) : ℂ) * ψ κ q‖ ≤
        c * ((m + 3) * b κ / D) * (volume.restrict disc).real univ := by
      intro κ
      refine (le_abs_self _).trans ?_
      have := norm_integral_le_of_norm_le_const (μ := volume.restrict disc)
        (f := fun q => ‖(hF m (-p - q) : ℂ) * ψ κ q‖) (C := c * ((m + 3) * b κ / D))
        (by filter_upwards [hFb _ _ (hψbd κ)] with q hq; rwa [norm_norm])
      rwa [Real.norm_eq_abs] at this
    have hsumI : Summable fun κ => ∫ q in disc, ‖(hF m (-p - q) : ℂ) * ψ κ q‖ :=
      ((hbD.summable.mul_left c).mul_right _).of_nonneg_of_le
        (fun κ => integral_nonneg fun _ => norm_nonneg _) hnI
    have hTop : Top m Ψ p = ∑' κ, Top m (ψ κ) p := by
      simp only [Top, hΨ, ← tsum_mul_left]
      exact (integral_tsum_of_summable_integral_norm hFint hsumI).symm
    have hTs : Summable fun κ => Top m (ψ κ) p :=
      hsumI.of_norm_bounded (fun κ => norm_integral_le_integral_norm _)
    have hsumC : (aF m p : ℂ) * Ψ p + (m + 2) * Top m Ψ p = (m + 3) * ∑' κ, hk' κ p := by
      rw [hTop, hΨ]
      simp only
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
        ← Summable.tsum_add ((hψsum p).mul_left _) (hTs.mul_left _)]
      exact tsum_congr fun κ => hψeq κ p hp
    have hΨint : Integrable (fun q => (hF m (-p - q) : ℂ) * Ψ q) (volume.restrict disc) :=
      Integrable.of_bound (hmeasF _ hΨm).aestronglyMeasurable _ (hFb _ _ hΨb)
    have hre : ∫ q in disc, hF m (-p - q) * -(Ψ q).re = -(Top m Ψ p).re := by
      have hi := integral_re hΨint
      simp only [RCLike.re_to_complex] at hi
      rw [Top, ← hi, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp
    have hre2 := congrArg Complex.re hsumC
    simp only [Complex.add_re, Complex.mul_re] at hre2
    simp at hre2
    unfold Gop
    simp only
    rw [hre]
    have hm3 : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show aF m p * -(Ψ p).re + (m + 2 : ℝ) * -(Top m Ψ p).re =
      -(((m + 3 : ℕ) : ℝ) * (∑' κ, hk' κ p).re) by push_cast; linarith]
    field_simp
  filter_upwards [p3b_fourier hPL hk haR] with p hp hpd
  rw [hG p hpd]
  have := congrArg Complex.re (hp hpd)
  rw [Complex.ofReal_re] at this
  rw [this]
  congr 2
  refine tsum_congr fun κ => ?_
  simp only [hhk]
  split_ifs <;> rfl

end P3b

/-! ## Theorem 95 and Corollary 96 for the concrete regular polygons -/

section Final

lemma iter_mem_disc (n i : ℕ) {q : ℂ} (hq : q ∈ disc) :
    (fun z => nrm n 1 * z)^[i] q ∈ disc := by
  induction i with
  | zero => simpa using hq
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (mul_mem_disc_iff norm_nrm _).2 ih

/-- **Theorem 95, pointwise form (22).** Let `n = m + 3`, `k ≥ 3`, `a_n(R) > 0` and
`a_n(1) > (n-1)c_{n-2}/k`. Then the correction `φ` of the proof exists: it is measurable,
bounded on `B` by `nW/(a_n(1) - (n-1)c_{n-2}/k)`, and `Gφ = -ν_o = -(ν - ν_s)` a.e. on `B`; and
for every `t ≥ sup_B |φ|` satisfying (22), `ν_s + t a_n ≤ 1/|P_k|` on `B`, `U(P_k)` is
`n`-completely mixable. -/
theorem thm95_pointwise (hPL : PLHyp) (m k : ℕ) (hk : 3 ≤ k)
    (haR : 0 < aF m (Poly.secR k : ℂ)) (ha1 : (m + 2) * hF m 0 / k < aF m 1) :
    ∃ φ : ℂ → ℝ, Measurable φ ∧
      (∀ q ∈ disc, |φ q| ≤ (m + 3) * Poly.W (m + 3) k (hF m 0) (aF m (Poly.secR k : ℂ))
        (Poly.Ssum (m + 3) k) / (aF m 1 - (m + 2) * hF m 0 / k)) ∧
      (∀ᵐ p ∂(volume : Measure ℂ), p ∈ disc → Gop m φ p = -(nu m k p - nus m k p)) ∧
      ∀ t : ℝ, (∀ q ∈ disc, |φ q| ≤ t) →
        (∀ q ∈ disc, nus m k q + t * aF m q ≤ 1 / Poly.area k) →
        CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) := by
  obtain ⟨φ, h1, h2, h3⟩ := exists_phi hPL m k hk haR ha1
    (fun {_} hκ {_} hh hhm {_} hM => mode_solve hPL m (by omega) hκ ha1 hh hhm hM)
  exact ⟨φ, h1, h2, h3, fun t ht h22 => thm95_of_phi hPL m k hk haR h1 ht h3 h22⟩

/-- **Theorem 95 (`st:thm:poly`), condition (21).** Let `n = m + 3`, `k ≥ 3`, `a_n(R) > 0`,
and let `N` bound `ν` on `B` (for instance `N = Nb`, `nu_le_Nb`, or for `n = 3` the second
form, `nu_le_cap`). If condition (21) holds (`Cond21`, which includes
`a_n(1) > (n-1)c_{n-2}/k`), with `a_n = aF m`, `c_{n-2} = hF m 0`, `c_{n-1} = aF m 0`, then
`U(P_k)` is `n`-completely mixable. -/
theorem thm95 (hPL : PLHyp) (m k : ℕ) (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ))
    {N : ℝ} (hN : ∀ q ∈ disc, nu m k q ≤ N)
    (h21 : Poly.Cond21 (m + 3) k (aF m 1) (aF m (Poly.secR k : ℂ)) (hF m 0) (aF m 0)
      (Poly.Ssum (m + 3) k) N) :
    CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) := by
  have hcast : ((m + 3 : ℕ) : ℝ) - 1 = (m : ℝ) + 2 := by push_cast; ring
  have ha1 : (m + 2) * hF m 0 / k < aF m 1 := by
    have := h21.1; rwa [hcast] at this
  obtain ⟨φ, -, hφb, -, hfin⟩ := thm95_pointwise hPL m k hk haR ha1
  have hc0 : 0 ≤ (m + 2) * hF m 0 / k := by
    have := hF_nonneg m 0; positivity
  have hc1 : 0 < aF m 0 := lt_of_lt_of_le (lt_of_le_of_lt hc0 ha1) (aF_le hPL 1)
  have hνs : ∀ q ∈ disc, nus m k q ≤ N := fun q hq =>
    Poly.avgRot_le _ (by omega) q fun i => hN _ (iter_mem_disc _ i hq)
  have hφ' : ∀ q ∈ disc, |φ q| ≤ ((m + 3 : ℕ) : ℝ) * Poly.W (m + 3) k (hF m 0)
      (aF m (Poly.secR k : ℂ)) (Poly.Ssum (m + 3) k) /
        (aF m 1 - (((m + 3 : ℕ) : ℝ) - 1) * hF m 0 / k) := fun q hq => by
    rw [hcast]; push_cast; exact hφb q hq
  obtain ⟨h1, h2⟩ := Poly.pointwise_of_cond21 h21 hc1 hνs (fun q _ => aF_le hPL q) hφ'
  exact hfin _ h1 h2

/-- Condition (22) for every correction `φ` of the proof of Theorem 95 (the form in which
Corollary 96 (c) checks it numerically, Table 15). -/
def Cond22 (m k : ℕ) : Prop :=
  ∀ φ : ℂ → ℝ, Measurable φ →
    (∀ᵐ p ∂(volume : Measure ℂ), p ∈ disc → Gop m φ p = -(nu m k p - nus m k p)) →
    ∃ t : ℝ, (∀ q ∈ disc, |φ q| ≤ t) ∧ ∀ q ∈ disc, nus m k q + t * aF m q ≤ 1 / Poly.area k

lemma cm_of_cond22 (hPL : PLHyp) {m k : ℕ} (hk : 3 ≤ k) (haR : 0 < aF m (Poly.secR k : ℂ))
    (ha1 : (m + 2) * hF m 0 / k < aF m 1) (h22 : Cond22 m k) :
    CompletelyMixable (m + 3) (Mixes.unifSet (poly k)) := by
  obtain ⟨φ, hm, -, hG, hfin⟩ := thm95_pointwise hPL m k hk haR ha1
  obtain ⟨t, ht, h⟩ := h22 φ hm hG
  exact hfin t ht h

/-- Remark 81: the rotation of order `k` gives a `k`-complete mix of `U(P_k)`. -/
theorem cm_self {k : ℕ} (hk : 3 ≤ k) : CompletelyMixable k (Mixes.unifSet (poly k)) := by
  have hk0 : 0 < k := by omega
  have hLK : (rot (nrm k 1)) ⁻¹' poly k = poly k := by
    ext z; simp [rot_apply, mul_nrm_mem_poly hk0]
  refine Poly.completelyMixable_of_rest hk0 (rot (nrm k 1)) (rot_pow_eq_one hk0)
    (rot_fix (by omega)) (isCompact_poly hk) (volume_poly_pos k) (centroid_poly hk)
    subset_rfl (fun x hx => by simpa [rot_apply, mul_nrm_mem_poly hk0] using hx) 0
    (fun σ => Measure.map_zero _) (by simp) (Mixes.unifSet (poly k))
    (Room.unifSet_compl (measurableSet_poly k))
    (Room.unifSet_map _ (measurePreserving_rot norm_nrm).map_eq (measurableSet_poly k) hLK) ?_
  ext S hS
  simp [Room.marginal]

lemma aF_zero_eq_lens {r : ℝ} (h0 : 0 ≤ r) (h2 : r ≤ 2) : aF 0 (r : ℂ) = Poly.lens r := by
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg h0]
  unfold aF
  rw [cp_one_eq (by rw [hn]; exact h2), hn, ENNReal.toReal_ofReal (lens_nonneg h0 h2)]

lemma c3_eq : (π ^ 2 - 3 / 4 * √3 * π) = (cp 2 0).toReal := by
  rw [cp_two_zero, ENNReal.toReal_ofReal Poly.c3_pos.le]

/-- **Corollary 96 (d), `n ≥ 3`.** Every regular polygon `P_k`, `k ≥ 3`, is `n`-completely
mixable for every `n ≥ 3`. Hypotheses: Prékopa–Leindler (`hPL`); the floating-point bounds of
Section 25 on `a₄ = aF 1`, `a₅ = aF 2` and `c₄ = aF 2 0`; the corner-area bound for `k = 7`;
the four cases of (c) (`(k, n) = (5,3), (5,4), (7,4), (7,5)`: `a_n(R) > 0` and condition (22),
Table 15); and the triangle (Corollary 44), the square and the hexagon (Lemma 50 with
Remark 81), which are proved elsewhere for other coordinates. The pentagon with `n = 5` uses its
rotation (`cm_self`), the octagon with `n = 5` uses `5 = 2 + 3` and its central symmetry. -/
theorem cor96d_poly (hPL : PLHyp)
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Poly.secR 7 : ℂ) ∧ Cond22 2 7)
    (htri : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (Mixes.unifSet (poly 3)))
    (hsq : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (Mixes.unifSet (poly 4)))
    (hhex : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (Mixes.unifSet (poly 6))) :
    ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, 3 ≤ n → CompletelyMixable n (Mixes.unifSet (poly k)) := by
  have hpi := pi_gt_three
  have hpi' := pi_lt_d2
  have hc3 := Poly.c3_le
  -- values of the constants
  have hF00 : hF 0 0 = 1 := by simp [hF, cp_zero_zero]
  have aF00 : aF 0 0 = π := by
    simp only [aF, zero_add, cp_one_zero, ENNReal.toReal_ofReal pi_pos.le]
  have hF10 : hF 1 0 = π := by simp only [hF, cp_one_zero, ENNReal.toReal_ofReal pi_pos.le]
  have aF10 : aF 1 0 = π ^ 2 - 3 / 4 * √3 * π := by rw [c3_eq]; rfl
  have hF20 : hF 2 0 = π ^ 2 - 3 / 4 * √3 * π := by rw [c3_eq]; rfl
  have aF01 : aF 0 1 = Poly.lens 1 := by
    have := aF_zero_eq_lens (r := 1) zero_le_one one_le_two; simpa using this
  have hR2 : ∀ k, 3 ≤ k → Poly.secR k ≤ 2 := fun k hk => p2_secR_le_two hk
  have hR0 : ∀ k, 3 ≤ k → 0 ≤ Poly.secR k := fun k hk =>
    le_trans zero_le_one (Poly.one_le_secR hk)
  have aF0R : ∀ k, 3 ≤ k → aF 0 (Poly.secR k : ℂ) = Poly.lens (Poly.secR k) := fun k hk =>
    aF_zero_eq_lens (hR0 k hk) (hR2 k hk)
  have hanti : ∀ m, AntitoneOn (fun ρ : ℝ => aF m (ρ : ℂ)) (Icc 1 2) := fun m =>
    (hPL (m + 1)).mono fun x hx => le_trans zero_le_one hx.1
  have hR9 : ∀ m k, 9 ≤ k → aF m (Poly.secR 9 : ℂ) ≤ aF m (Poly.secR k : ℂ) := by
    intro m k hk
    obtain ⟨h1, h2, -⟩ := Poly.trig_ge_nine hk
    refine p2_aF_anti hPL ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact h2
  -- n = 3 for k ≥ 7
  have h3 : ∀ k, 7 ≤ k → CompletelyMixable 3 (Mixes.unifSet (poly k)) := by
    intro k hk
    rcases (show k = 7 ∨ 8 ≤ k by omega) with h | h
    · subst h
      obtain ⟨h1, h2, -⟩ := Poly.trig_seven
      have hl := Poly.lens_ge_seven h1 h2
      have hR : 0 < aF 0 (Poly.secR 7 : ℂ) := by rw [aF0R 7 (by norm_num)]; linarith
      refine thm95 hPL 0 7 (by norm_num) hR
        (fun q hq => nu_le_cap hPL (by norm_num) (by linarith) (by norm_num) hcap hq) ?_
      have := Poly.cor96a_seven (Poly.Ssum_nonneg 3 7) (Poly.Ssum_le 3 7) (le_refl 0.1279)
      rw [aF01, aF0R 7 (by norm_num), hF00, aF00]; exact this
    · obtain ⟨h1, h2, -⟩ := Poly.trig_ge_eight h
      have hl := Poly.lens_ge_eight h1 h2
      have hR : 0 < aF 0 (Poly.secR k : ℂ) := by rw [aF0R k (by omega)]; linarith
      refine thm95 hPL 0 k (by omega) hR (fun q _ => nu_le_Nb hPL (by omega) hR q) ?_
      have := Poly.cor96a_ge_eight h (Poly.Ssum_nonneg 3 k) (Poly.Ssum_le 3 k)
      rw [aF01, aF0R k (by omega), hF00, aF00]; exact this
  -- n = 4 for k ≥ 8
  have h4 : ∀ k, 8 ≤ k → CompletelyMixable 4 (Mixes.unifSet (poly k)) := by
    intro k hk
    rcases (show k = 8 ∨ 9 ≤ k by omega) with h | h
    · subst h
      have hR : 0 < aF 1 (Poly.secR 8 : ℂ) := by linarith
      refine thm95 hPL 1 8 (by norm_num) hR (fun q _ => nu_le_Nb hPL (by norm_num) hR q) ?_
      have := Poly.cor96b_four_eight ha41 ha48
      rw [hF10, aF10]; exact this
    · have hR : 0 < aF 1 (Poly.secR k : ℂ) := by linarith [hR9 1 k h]
      refine thm95 hPL 1 k (by omega) hR (fun q _ => nu_le_Nb hPL (by omega) hR q) ?_
      have := Poly.cor96b_four (hanti 1) (by simpa using ha41) ha49 h
      simp only [Complex.ofReal_one] at this
      rw [hF10, aF10]; exact this
  -- n = 5 for k ≥ 9
  have h5 : ∀ k, 9 ≤ k → CompletelyMixable 5 (Mixes.unifSet (poly k)) := by
    intro k hk
    have hR : 0 < aF 2 (Poly.secR k : ℂ) := by linarith [hR9 2 k hk]
    refine thm95 hPL 2 k (by omega) hR (fun q _ => nu_le_Nb hPL (by omega) hR q) ?_
    have hc4 : 0 < aF 2 0 := by linarith [aF_le hPL (m := 2) 1]
    have := Poly.cor96b_five (hanti 2) (by simpa using ha51) ha59 hc4 hc4u hk
    simp only [Complex.ofReal_one] at this
    rw [hF20]; exact this
  intro k hk
  apply Poly.all_of_three_four_five
  · rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ 7 ≤ k by omega) with h | h | h | h | h
    · subst h; exact htri 3 (Or.inl rfl)
    · subst h; exact hsq 3 (Or.inl rfl)
    · subst h
      refine cm_of_cond22 hPL (by norm_num) h53.1 ?_ h53.2
      rw [hF00, aF01]; have := Poly.lens_one_gt; push_cast; linarith
    · subst h; exact hhex 3 (Or.inl rfl)
    · exact h3 k h
  · rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ 8 ≤ k by omega)
      with h | h | h | h | h | h
    · subst h; exact htri 4 (Or.inr (Or.inl rfl))
    · subst h; exact hsq 4 (Or.inr (Or.inl rfl))
    · subst h
      refine cm_of_cond22 hPL (by norm_num) h54.1 ?_ h54.2
      rw [hF10]; push_cast; linarith
    · subst h; exact hhex 4 (Or.inr (Or.inl rfl))
    · subst h
      refine cm_of_cond22 hPL (by norm_num) h74.1 ?_ h74.2
      rw [hF10]; push_cast; linarith
    · exact h4 k h
  · rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k by omega)
      with h | h | h | h | h | h | h
    · subst h; exact htri 5 (Or.inr (Or.inr rfl))
    · subst h; exact hsq 5 (Or.inr (Or.inr rfl))
    · subst h; exact cm_self (le_refl _ |>.trans' (by norm_num))
    · subst h; exact hhex 5 (Or.inr (Or.inr rfl))
    · subst h
      refine cm_of_cond22 hPL (by norm_num) h75.1 ?_ h75.2
      rw [hF20]; push_cast; linarith
    · subst h
      have h2 : CompletelyMixable 2 (Mixes.unifSet (poly 8)) :=
        (completelyMixable_two_iff_even (by norm_num)).2 (by decide)
      exact ScaledB.completelyMixable_add_add h2 (h3 8 (by norm_num))
    · exact h5 k h

/-- **Corollary 96 (d), complete.** Under the hypotheses of `cor96d_poly`, for `k ≥ 3` and
`n ≥ 2`, `U(P_k)` is `n`-completely mixable exactly when `n ≥ 3` or `k` is even. -/
theorem cor96d_poly_iff (hPL : PLHyp)
    (ha41 : 3.398 ≤ aF 1 1) (ha49 : 3.143 ≤ aF 1 (Poly.secR 9 : ℂ))
    (ha48 : 3.071 ≤ aF 1 (Poly.secR 8 : ℂ))
    (ha51 : 9.242 ≤ aF 2 1) (ha59 : 8.724 ≤ aF 2 (Poly.secR 9 : ℂ)) (hc4u : aF 2 0 ≤ 14.252)
    (hcap : ∀ c ∈ disc, volume (corner 7 ∩ Metric.closedBall c 1) ≤ ENNReal.ofReal 0.1279)
    (h53 : 0 < aF 0 (Poly.secR 5 : ℂ) ∧ Cond22 0 5)
    (h54 : 0 < aF 1 (Poly.secR 5 : ℂ) ∧ Cond22 1 5)
    (h74 : 0 < aF 1 (Poly.secR 7 : ℂ) ∧ Cond22 1 7)
    (h75 : 0 < aF 2 (Poly.secR 7 : ℂ) ∧ Cond22 2 7)
    (htri : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (Mixes.unifSet (poly 3)))
    (hsq : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (Mixes.unifSet (poly 4)))
    (hhex : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (Mixes.unifSet (poly 6)))
    {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) :
    CompletelyMixable n (Mixes.unifSet (poly k)) ↔ 3 ≤ n ∨ Even k := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with h | h
  · subst h; rw [completelyMixable_two_iff_even hk]; simp
  · exact ⟨fun _ => Or.inl h, fun _ => cor96d_poly hPL ha41 ha49 ha48 ha51 ha59 hc4u hcap h53
      h54 h74 h75 htri hsq hhex k hk n h⟩

end Final

end PolyB

end Mixes
