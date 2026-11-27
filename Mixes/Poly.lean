import Mixes.Room
import Mixes.ScaledB
import Mixes.Cone
import Mixes.Symm

/-!
# Regular polygons (Theorem 95, Corollary 96)

Item M1k of `mixes/LEAN_VERIFICATION_PRIORITIES.md`: Theorem 95 (`st:thm:poly`) and
Corollary 96 (`st:cor:poly`) of `mixes/main.tex`.

* Numerics, exact (bounds on `π`, `√2`, `√3`, Taylor bounds for `sin`, `cos`, concavity of
  `cos` for `arccos`): `lens_one_gt`, `lens_ge_of_le`, `trig_ge_eight`, `trig_seven`,
  `trig_ge_nine`, `c3_le`.
* Quantities: `area`, `secR`, `W`, `Nb`, `Ssum` (`0 ≤ S ≤ π²/6`, `S = 0` if `n ∣ k`), `Cond21`
  (condition (21)).
* Corollary 96 (a): `cor96a_ge_eight` (all `k ≥ 8`, proved), `cor96a_seven` (`k = 7`, with the
  corner-area bound `0.1279` as a hypothesis); (b): `cond21_of_bounds` (monotonicity in `k`),
  `cor96b_four`, `cor96b_four_eight`, `cor96b_five` (Riemann-sum bounds as hypotheses);
  (d): `all_of_three_four_five` (Remark 81), `cor96d` (bookkeeping, with Theorem 95 as `hthm`).
* Theorem 95, analytic steps: `sum_exp_root`, `avg_rot_exp` (symmetric part), `integral_arc`,
  `integral_arcs` (the `k` arcs), `abs_integral_antitone_mul_cos_le` (Fourier coefficients of
  a monotone function, by the layer-cake formula and Fubini), `coeff_bound`, `coeff_bound_eq`,
  `hasSum_W` (the sum `W`), `integral_T_bound`, `neumann` (the Neumann series for `G_κ`).
* Theorem 95, densities: `nu_le_N`, `avgRot`, `avgRot_comp`, `avgRot_le`,
  `pointwise_of_cond21` ((21) ⇒ (22)), `marginal_identity`, `correction_nonneg`,
  `rest_nonneg`.
* Theorem 95, measures: `marginal_withDensity_sum` (the operator `G`), `corner_marginal` (the
  marginal of the corner partners), `marginal_symmetrise`, `completelyMixable_of_rest` and
  `completelyMixable_of_densities` (the complete mix via orbits of `Q` and Lemma 88).
-/

open MeasureTheory Set Real

noncomputable section

namespace Mixes

namespace Poly

/-! ## The lens function and its numerical bounds -/

/-- The area of the intersection of two unit discs at distance `d`. -/
def lens (d : ℝ) : ℝ := 2 * arccos (d / 2) - d / 2 * √(4 - d ^ 2)

lemma lens_one : lens 1 = 2 * π / 3 - √3 / 2 := by
  have h : arccos (1 / 2) = π / 3 := by
    rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]
  simp only [lens, h]
  norm_num
  ring

/-- `arccos` lies above its chord between `1/2` and `√2/2` (concavity of `cos`). -/
lemma arccos_ge_chord {u : ℝ} (h1 : 1 / 2 ≤ u) (h2 : u ≤ √2 / 2) :
    π / 3 - (u - 1 / 2) * (π / 12) / ((√2 - 1) / 2) ≤ arccos u := by
  have hs2 : (1.4142 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hd : 0 < (√2 - 1) / 2 := by linarith
  set s := (u - 1 / 2) / ((√2 - 1) / 2) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hd]; linarith
  set θ := s * (π / 4) + (1 - s) * (π / 3) with hθ
  have hθeq : π / 3 - (u - 1 / 2) * (π / 12) / ((√2 - 1) / 2) = θ := by
    rw [hθ, hs]; field_simp; ring
  have hpi := pi_pos
  have hcos : u ≤ cos θ := by
    have hc := strictConcaveOn_cos_Icc.concaveOn.2
      (show π / 4 ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith, by linarith⟩)
      (show π / 3 ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith, by linarith⟩)
      hs0 (by linarith : 0 ≤ 1 - s) (by ring)
    simp only [smul_eq_mul, cos_pi_div_four, cos_pi_div_three] at hc
    have hne : √2 - 1 ≠ 0 := by linarith
    have hu : u = s * (√2 / 2) + (1 - s) * (1 / 2) := by
      rw [hs]; field_simp; ring
    rw [hu]; exact hc
  rw [hθeq]
  calc θ = arccos (cos θ) := (arccos_cos (by nlinarith) (by nlinarith)).symm
    _ ≤ arccos u := arccos_le_arccos hcos

lemma sqrt_two_gt : (1.41421 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt_two_lt : √2 < (1.41422 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt_three_lt : √3 < (1.7320509 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `lens 1 = 2π/3 - √3/2 > 1.22836`. -/
lemma lens_one_gt : (1.22836 : ℝ) < lens 1 := by
  rw [lens_one]; linarith [pi_gt_d6, sqrt_three_lt]

/-- A lower bound for `lens` on `[1, d₀]`, `d₀ ≤ √2`: `arccos` is antitone and above its
chord, and `d ↦ d²(4 - d²)` is increasing for `d² ≤ 2`. -/
lemma lens_ge_of_le {d d₀ : ℝ} (h1 : 1 ≤ d) (hd : d ≤ d₀) (hd₀ : d₀ ≤ √2) :
    2 * (π / 3 - (d₀ / 2 - 1 / 2) * (π / 12) / ((√2 - 1) / 2))
      - √(d₀ ^ 2 * (4 - d₀ ^ 2)) / 2 ≤ lens d := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : arccos (d₀ / 2) ≤ arccos (d / 2) := arccos_le_arccos (by linarith)
  have hc := arccos_ge_chord (u := d₀ / 2) (by linarith) (by linarith)
  have hd0 : 0 ≤ d := by linarith
  have hsq : d / 2 * √(4 - d ^ 2) = √(d ^ 2 * (4 - d ^ 2)) / 2 := by
    rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd0]; ring
  have hmono : √(d ^ 2 * (4 - d ^ 2)) ≤ √(d₀ ^ 2 * (4 - d₀ ^ 2)) := by
    apply Real.sqrt_le_sqrt
    have h2 : d ^ 2 ≤ d₀ ^ 2 := by nlinarith
    have h3 : d₀ ^ 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg 2]
    nlinarith
  simp only [lens]
  rw [hsq]
  linarith

/-- `lens d ≥ 1.0798` for `1 ≤ d ≤ 1.0825`. -/
lemma lens_ge_eight {d : ℝ} (h1 : 1 ≤ d) (hd : d ≤ 1.0825) : (1.0798 : ℝ) ≤ lens d := by
  have h := lens_ge_of_le h1 hd (by linarith [sqrt_two_gt])
  have ht : √((1.0825 : ℝ) ^ 2 * (4 - 1.0825 ^ 2)) ≤ 1.820466 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hq : (1.0825 / 2 - 1 / 2) * (π / 12) / ((√2 - 1) / 2) ≤
      (1.0825 / 2 - 1 / 2) * (π / 12) / ((1.41421 - 1) / 2) := by
    apply div_le_div_of_nonneg_left _ (by norm_num) (by linarith [sqrt_two_gt])
    nlinarith [pi_pos]
  generalize ((1.0825 : ℝ) / 2 - 1 / 2) * (π / 12) / ((√2 - 1) / 2) = A at h hq
  generalize √((1.0825 : ℝ) ^ 2 * (4 - 1.0825 ^ 2)) = B at h ht
  have hπ := pi_gt_d6
  norm_num at hq h ⊢
  linarith

/-- `lens d ≥ 1.0276` for `1 ≤ d ≤ 1.1125`. -/
lemma lens_ge_seven {d : ℝ} (h1 : 1 ≤ d) (hd : d ≤ 1.1125) : (1.0276 : ℝ) ≤ lens d := by
  have h := lens_ge_of_le h1 hd (by linarith [sqrt_two_gt])
  have ht : √((1.1125 : ℝ) ^ 2 * (4 - 1.1125 ^ 2)) ≤ 1.849010 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hq : (1.1125 / 2 - 1 / 2) * (π / 12) / ((√2 - 1) / 2) ≤
      (1.1125 / 2 - 1 / 2) * (π / 12) / ((1.41421 - 1) / 2) := by
    apply div_le_div_of_nonneg_left _ (by norm_num) (by linarith [sqrt_two_gt])
    nlinarith [pi_pos]
  generalize ((1.1125 : ℝ) / 2 - 1 / 2) * (π / 12) / ((√2 - 1) / 2) = A at h hq
  generalize √((1.1125 : ℝ) ^ 2 * (4 - 1.1125 ^ 2)) = B at h ht
  have hπ := pi_gt_d6
  norm_num at hq h ⊢
  linarith

/-! ## The quantities of Theorem 95 -/

/-- `|P_k| = k tan(π/k)`, the area of the regular `k`-gon with inradius `1`. -/
def area (k : ℕ) : ℝ := k * tan (π / k)

/-- `R = sec(π/k)`, the circumradius of `P_k`. -/
def secR (k : ℕ) : ℝ := 1 / cos (π / k)

/-- The constant `W` of Theorem 95, with `c = c_{n-2}`, `a = a_n(R)` and `S` the sum
`∑_{j ≥ 1, n ∤ jk} 1/j²`. -/
def W (n k : ℕ) (c a S : ℝ) : ℝ := 2 * (n - 1) * c * tan (π / k) / (π * k ^ 2 * a) * S

/-- The constant `N` of Theorem 95, with `c = c_{n-2}` and `a = a_n(R)`. -/
def Nb (n k : ℕ) (c a : ℝ) : ℝ := (n - 1) * c * (area k - π) / (area k * a)

/-- Condition (21) (`st:eq:poly`) together with `a_n(1) > (n-1)c_{n-2}/k`, for given values
`a1 = a_n(1)`, `aR = a_n(R)`, `c2 = c_{n-2}`, `c1 = c_{n-1}`, the sum `S` and a bound `N`. -/
def Cond21 (n k : ℕ) (a1 aR c2 c1 S N : ℝ) : Prop :=
  (n - 1) * c2 / k < a1 ∧ n * W n k c2 aR S / (a1 - (n - 1) * c2 / k) ≤ (1 / area k - N) / c1

/-- Trigonometric bounds for `k ≥ 8`: `1 ≤ sec(π/k) ≤ 1.0825` and
`π/k ≤ tan(π/k) ≤ 1.0825 π/k`. -/
lemma trig_ge_eight {k : ℕ} (hk : 8 ≤ k) :
    1 ≤ secR k ∧ secR k ≤ 1.0825 ∧ π / k ≤ tan (π / k) ∧ tan (π / k) ≤ 1.0825 * (π / k) := by
  have hk' : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := pi_pos
  have hx0 : 0 < π / k := by positivity
  have hx8 : π / k ≤ π / 8 := div_le_div_of_nonneg_left hpi.le (by norm_num) hk'
  have hc8 : (0.92379 : ℝ) ≤ cos (π / 8) := by
    rw [cos_pi_div_eight, le_div_iff₀ (by norm_num), Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sqrt_two_gt]
  have hcx : cos (π / 8) ≤ cos (π / k) :=
    cos_le_cos_of_nonneg_of_le_pi hx0.le (by linarith) hx8
  have hc0 : 0 < cos (π / k) := by linarith
  have hc1 : cos (π / k) ≤ 1 := cos_le_one _
  have hsec : 1 / cos (π / k) ≤ 1.0825 := by
    rw [div_le_iff₀ hc0]; nlinarith
  refine ⟨by rw [secR, le_div_iff₀ hc0]; linarith, hsec, le_tan hx0.le (by linarith), ?_⟩
  rw [tan_eq_sin_div_cos, div_le_iff₀ hc0]
  have hs := sin_le hx0.le
  have : 1 ≤ 1.0825 * cos (π / k) := by rw [div_le_iff₀ hc0] at hsec; linarith
  nlinarith

/-- **Corollary 96 (a), `k ≥ 8`.** For `n = 3` (`c₁ = 1`, `c₂ = π`, `a₃ = lens`), condition (21)
holds for every `k ≥ 8` and every value `0 ≤ S ≤ π²/6` of the sum over `j`. -/
theorem cor96a_ge_eight {k : ℕ} (hk : 8 ≤ k) {S : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ π ^ 2 / 6) :
    Cond21 3 k (lens 1) (lens (secR k)) 1 π S (Nb 3 k 1 (lens (secR k))) := by
  obtain ⟨hR1, hR2, ht1, ht2⟩ := trig_ge_eight hk
  have hk' : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hpi := pi_pos
  have hl1 := lens_one_gt
  have hl := lens_ge_eight hR1 hR2
  set ℓ := lens (secR k)
  set t := tan (π / k)
  have h2k : (3 - 1 : ℝ) * 1 / k ≤ 1 / 4 := by
    rw [div_le_iff₀ hkpos]; linarith
  refine ⟨by linarith, ?_⟩
  -- the left side
  have hW : W 3 k 1 ℓ S ≤ 4 * 1.0825 * π ^ 2 / (6 * 512 * 1.0798) := by
    simp only [W]
    have hk3 : (512 : ℝ) ≤ k ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hk' 3; norm_num at this; linarith
    calc 2 * ((3 : ℕ) - 1 : ℝ) * 1 * t / (π * k ^ 2 * ℓ) * S
        = 4 * t * S / (π * k ^ 2 * ℓ) := by push_cast; ring
      _ ≤ 4 * (1.0825 * (π / k)) * (π ^ 2 / 6) / (π * k ^ 2 * 1.0798) := by
          gcongr
      _ = 4 * 1.0825 * π ^ 2 / (6 * k ^ 3 * 1.0798) := by field_simp
      _ ≤ 4 * 1.0825 * π ^ 2 / (6 * 512 * 1.0798) := by gcongr
  set D := lens 1 - ((3 : ℕ) - 1) * 1 / k with hD
  have hL : (3 : ℕ) * W 3 k 1 ℓ S / D ≤ 0.0396 := by
    have hden : (0.97836 : ℝ) ≤ D := by rw [hD]; push_cast at h2k ⊢; linarith
    rw [div_le_iff₀ (by linarith)]
    have hW0 : 0 ≤ W 3 k 1 ℓ S := by
      simp only [W]; push_cast
      have : 0 ≤ t := by linarith [div_pos hpi hkpos]
      positivity
    have hpi2 : π ^ 2 ≤ 9.8697 := by nlinarith [pi_lt_d6]
    have h3W : 3 * W 3 k 1 ℓ S ≤ 3 * (4 * 1.0825 * 9.8697 / (6 * 512 * 1.0798)) := by
      have : 4 * 1.0825 * π ^ 2 / (6 * 512 * 1.0798) ≤ 4 * 1.0825 * 9.8697 / (6 * 512 * 1.0798) :=
        by gcongr
      linarith
    push_cast
    norm_num at h3W hden ⊢
    linarith
  -- the right side
  have hR : (0.0486 : ℝ) ≤ (1 / area k - Nb 3 k 1 ℓ) / π := by
    have hX1 : π ≤ area k := by
      simp only [area]
      calc π = k * (π / k) := by field_simp
        _ ≤ k * t := by gcongr
    have hX2 : area k ≤ 1.0825 * π := by
      simp only [area]
      calc (k : ℝ) * t ≤ k * (1.0825 * (π / k)) := by gcongr
        _ = 1.0825 * π := by field_simp
    have hX0 : 0 < area k := by linarith
    have heq : (1 / area k - Nb 3 k 1 ℓ) / π = (1 - 2 * (area k - π) / ℓ) / (area k * π) := by
      simp only [Nb]; push_cast; field_simp; ring
    rw [heq, le_div_iff₀ (by positivity)]
    have hq : 2 * (area k - π) / ℓ ≤ 2 * (0.0825 * π) / 1.0798 := by
      gcongr
      · linarith
    have hpi2 : π * π ≤ 9.8697 := by nlinarith [pi_lt_d6]
    have hXpi : area k * π ≤ 1.0825 * 9.8697 := by nlinarith
    have hq' : (0.5199 : ℝ) ≤ 1 - 2 * (area k - π) / ℓ := by
      have : 2 * (0.0825 * π) / 1.0798 ≤ (0.4801 : ℝ) := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith [pi_lt_d6]
      linarith
    nlinarith
  linarith

/-- Trigonometric bounds for `k = 7`: `1 ≤ sec(π/7) ≤ 1.1125` and
`π/7 ≤ tan(π/7) ≤ 0.4826` (from `cos x ≥ 1 - x²/2` and `sin x ≤ x - x³/6 + x⁵/100`). -/
lemma trig_seven :
    1 ≤ secR 7 ∧ secR 7 ≤ 1.1125 ∧ π / 7 ≤ tan (π / 7) ∧ tan (π / 7) ≤ 0.4826 := by
  have hpi := pi_pos
  have hx0 : 0 < π / (7 : ℕ) := by positivity
  set x := π / (7 : ℕ) with hx
  have hxl : 0.448798 ≤ x := by rw [hx]; push_cast; linarith [pi_gt_d6]
  have hxu : x ≤ 0.4488 := by rw [hx]; push_cast; linarith [pi_lt_d6]
  have hc : 0.89928 ≤ cos x := by
    have := one_sub_sq_div_two_le_cos (x := x)
    have h2 : x ^ 2 ≤ 0.4488 ^ 2 := by gcongr
    norm_num at h2 ⊢; linarith
  have hc0 : 0 < cos x := by linarith
  have hsin : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
    have h := sin_bound (x := x) (by rw [abs_of_pos hx0]; linarith)
    rw [abs_of_pos hx0] at h
    linarith [le_abs_self (sin x - (x - x ^ 3 / 6))]
  have hsin' : sin x ≤ 0.43392 := by
    have h3 : 0.448798 ^ 3 ≤ x ^ 3 := by gcongr
    have h5 : x ^ 5 ≤ 0.4488 ^ 5 := by gcongr
    norm_num at h3 h5 ⊢; linarith
  have h7 : (π / 7 : ℝ) = x := by rw [hx]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [secR, le_div_iff₀ hc0]; linarith [cos_le_one x]
  · rw [secR, div_le_iff₀ hc0]; linarith
  · rw [h7]; exact le_tan hx0.le (by linarith)
  · rw [h7, tan_eq_sin_div_cos, div_le_iff₀ hc0]; nlinarith

/-- **Corollary 96 (a), `k = 7`.** For `n = 3` and the heptagon, condition (21) holds with the
second form `N = 2 cap / (|P₇| lens(R))` of `N`, for every bound `cap ≤ 0.1279` of the area of
the corners in a unit disc with centre in `B` (computed in Section 25, a hypothesis here). -/
theorem cor96a_seven {S : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ π ^ 2 / 6) {cap : ℝ}
    (hc : cap ≤ 0.1279) :
    Cond21 3 7 (lens 1) (lens (secR 7)) 1 π S (2 * cap / (area 7 * lens (secR 7))) := by
  obtain ⟨hR1, hR2, ht1, ht2⟩ := trig_seven
  have hpi := pi_pos
  have hl1 := lens_one_gt
  have hl := lens_ge_seven hR1 hR2
  set ℓ := lens (secR 7)
  set t := tan (π / (7 : ℕ))
  have ht : t = tan (π / 7) := by simp [t]
  rw [← ht] at ht1 ht2
  have h2k : ((3 : ℕ) - 1 : ℝ) * 1 / (7 : ℕ) = 2 / 7 := by norm_num
  refine ⟨by rw [h2k]; linarith, ?_⟩
  rw [h2k]
  have hW : W 3 7 1 ℓ S ≤ 4 * 0.4826 * π / (6 * 49 * 1.0276) := by
    simp only [W]
    calc 2 * ((3 : ℕ) - 1 : ℝ) * 1 * t / (π * (7 : ℕ) ^ 2 * ℓ) * S
        = 4 * t * S / (π * 49 * ℓ) := by push_cast; ring
      _ ≤ 4 * 0.4826 * (π ^ 2 / 6) / (π * 49 * 1.0276) := by
          gcongr
      _ = 4 * 0.4826 * π / (6 * 49 * 1.0276) := by field_simp
  have hL : (3 : ℕ) * W 3 7 1 ℓ S / (lens 1 - 2 / 7) ≤ 0.0639 := by
    rw [div_le_iff₀ (by linarith)]
    have h3W : 3 * W 3 7 1 ℓ S ≤ 3 * (4 * 0.4826 * 3.141593 / (6 * 49 * 1.0276)) := by
      have : 4 * 0.4826 * π / (6 * 49 * 1.0276) ≤ 4 * 0.4826 * 3.141593 / (6 * 49 * 1.0276) := by
        gcongr; exact pi_lt_d6.le
      linarith
    push_cast
    norm_num at h3W ⊢
    linarith
  have hR : (0.0689 : ℝ) ≤ (1 / area 7 - 2 * cap / (area 7 * ℓ)) / π := by
    have hA : area 7 = 7 * t := by simp [area, t]
    have hX1 : π ≤ area 7 := by rw [hA]; linarith
    have hX2 : area 7 ≤ 3.3782 := by rw [hA]; linarith
    have hX0 : 0 < area 7 := by linarith
    have hinv : (0.296 : ℝ) ≤ 1 / area 7 := by
      rw [le_div_iff₀ hX0]; nlinarith
    have hN : 2 * cap / (area 7 * ℓ) ≤ 0.079237 := by
      rw [div_le_iff₀ (by positivity)]
      have : 3.141592 * 1.0276 ≤ area 7 * ℓ := by
        have := pi_gt_d6; nlinarith
      nlinarith
    rw [le_div_iff₀ hpi]
    nlinarith [pi_lt_d6]
  linarith

/-! ## The sum over `j` -/

/-- The sum `∑_{j ≥ 1, n ∤ jk} 1/j²` of Theorem 95 (the term `j = 0` is excluded since
`n ∣ 0`). -/
def Ssum (n k : ℕ) : ℝ := ∑' j : ℕ, if ¬ n ∣ j * k then 1 / (j : ℝ) ^ 2 else 0

lemma summable_Ssum (n k : ℕ) :
    Summable fun j : ℕ => if ¬ n ∣ j * k then 1 / (j : ℝ) ^ 2 else 0 := by
  refine hasSum_zeta_two.summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
  · split_ifs <;> positivity
  · split_ifs <;> simp [one_div]

lemma Ssum_nonneg (n k : ℕ) : 0 ≤ Ssum n k :=
  tsum_nonneg fun j => by split_ifs <;> positivity

lemma Ssum_le (n k : ℕ) : Ssum n k ≤ π ^ 2 / 6 := by
  rw [← hasSum_zeta_two.tsum_eq]
  refine (summable_Ssum n k).tsum_le_tsum (fun j => ?_) hasSum_zeta_two.summable
  split_ifs <;> simp [one_div]

/-- If `n ∣ k`, then `n` divides every `jk` and the sum is `0` (so `W = 0`). -/
lemma Ssum_eq_zero_of_dvd {n k : ℕ} (h : n ∣ k) : Ssum n k = 0 := by
  have : ∀ j : ℕ, (if ¬ n ∣ j * k then 1 / (j : ℝ) ^ 2 else 0) = 0 := fun j => by
    simp [h.mul_left j]
  rw [Ssum, tsum_congr this, tsum_zero]

/-! ## Corollary 96 (b): a generic reduction to one numerical inequality -/

/-- Condition (21) from bounds: if `a_n(R) ≥ aR0`, `a_n(1) ≥ a10`, `c_{n-2} ≤ c2u`,
`c_{n-1} ≤ c1u`, `π/k ≤ tan(π/k) ≤ τπ/k`, `k ≥ k0`, and the numerical inequality `hnum`
between the resulting bounds of the two sides holds, then (21) holds. This is the
monotonicity in `k` of Corollary 96 (a), (b): the left side decreases and the right side
increases as `k` grows. -/
lemma cond21_of_bounds {n k : ℕ} {a1 aR c2 c1 S a10 aR0 c2u c1u τ k0 : ℝ} (hn : 2 ≤ n)
    (hk0 : 0 < k0) (hk : k0 ≤ k) (haR : aR0 ≤ aR) (haR0 : 0 < aR0) (ha1 : a10 ≤ a1)
    (hc2 : c2 ≤ c2u) (hc2p : 0 ≤ c2) (hc1 : c1 ≤ c1u) (hc1p : 0 < c1)
    (hS0 : 0 ≤ S) (hS : S ≤ π ^ 2 / 6) (ht1 : π / k ≤ tan (π / k))
    (ht2 : tan (π / k) ≤ τ * (π / k))
    (hD0 : 0 < a10 - (n - 1) * c2u / k0) (hq : (n - 1) * c2u * (τ - 1) * π / aR0 ≤ 1)
    (hnum : n * (2 * (n - 1) * c2u * τ * π ^ 2 / (6 * k0 ^ 3 * aR0)) /
        (a10 - (n - 1) * c2u / k0) ≤ (1 - (n - 1) * c2u * (τ - 1) * π / aR0) / (τ * π * c1u)) :
    Cond21 n k a1 aR c2 c1 S (Nb n k c2 aR) := by
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le hk0 hk
  have hpi := pi_pos
  have hn1 : (1 : ℝ) ≤ n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set t := tan (π / k) with ht
  have hx0 : 0 < π / k := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le hx0 ht1
  have hτ : 1 ≤ τ := by
    by_contra h
    push Not at h
    have : τ * (π / k) < π / k := by nlinarith
    linarith
  have hc2u : 0 ≤ c2u := le_trans hc2p hc2
  have hD : a10 - (n - 1) * c2u / k0 ≤ a1 - (n - 1) * c2 / k := by
    have : (n - 1) * c2 / k ≤ (n - 1) * c2u / k0 := by
      apply div_le_div₀ (by positivity) (by gcongr) hk0 hk
    linarith
  refine ⟨by linarith, ?_⟩
  have hW : W n k c2 aR S ≤ 2 * (n - 1) * c2u * τ * π ^ 2 / (6 * k0 ^ 3 * aR0) := by
    simp only [W]
    have haRp : 0 < aR := lt_of_lt_of_le haR0 haR
    calc 2 * (n - 1) * c2 * t / (π * k ^ 2 * aR) * S
        ≤ 2 * (n - 1) * c2u * (τ * (π / k)) / (π * k ^ 2 * aR0) * (π ^ 2 / 6) := by
          gcongr
      _ = 2 * (n - 1) * c2u * τ * π ^ 2 / (6 * k ^ 3 * aR0) := by field_simp
      _ ≤ 2 * (n - 1) * c2u * τ * π ^ 2 / (6 * k0 ^ 3 * aR0) := by gcongr
  have hW0 : 0 ≤ W n k c2 aR S := by
    simp only [W]
    have haRp : 0 < aR := lt_of_lt_of_le haR0 haR
    have : (0 : ℝ) ≤ n - 1 := by linarith
    positivity
  have hL : n * W n k c2 aR S / (a1 - (n - 1) * c2 / k) ≤
      n * (2 * (n - 1) * c2u * τ * π ^ 2 / (6 * k0 ^ 3 * aR0)) / (a10 - (n - 1) * c2u / k0) := by
    apply div_le_div₀ (by positivity) (by gcongr) hD0 hD
  have hX1 : π ≤ area k := by
    simp only [area]
    calc π = k * (π / k) := by field_simp
      _ ≤ k * t := by gcongr
  have hX2 : area k ≤ τ * π := by
    simp only [area]
    calc (k : ℝ) * t ≤ k * (τ * (π / k)) := by gcongr
      _ = τ * π := by field_simp
  have hX0 : 0 < area k := by linarith
  have hR : (1 - (n - 1) * c2u * (τ - 1) * π / aR0) / (τ * π * c1u) ≤
      (1 / area k - Nb n k c2 aR) / c1 := by
    have haRp : 0 < aR := lt_of_lt_of_le haR0 haR
    have heq : (1 / area k - Nb n k c2 aR) / c1 =
        (1 - (n - 1) * c2 * (area k - π) / aR) / (area k * c1) := by
      simp only [Nb]; field_simp
    rw [heq]
    have hqq : (n - 1) * c2 * (area k - π) / aR ≤ (n - 1) * c2u * (τ - 1) * π / aR0 := by
      have h1 : area k - π ≤ (τ - 1) * π := by linarith
      calc (n - 1) * c2 * (area k - π) / aR ≤ (n - 1) * c2u * ((τ - 1) * π) / aR0 := by
            gcongr
        _ = (n - 1) * c2u * (τ - 1) * π / aR0 := by ring
    apply div_le_div₀ (by linarith) (by linarith) (by positivity)
    calc area k * c1 ≤ (τ * π) * c1u := by gcongr
      _ = τ * π * c1u := by ring
  linarith

/-- Trigonometric bounds for `k ≥ 9`: `1 ≤ sec(π/k) ≤ sec(π/9) ≤ 1.065` and
`π/k ≤ tan(π/k) ≤ 1.0435 π/k`. -/
lemma trig_ge_nine {k : ℕ} (hk : 9 ≤ k) :
    1 ≤ secR k ∧ secR k ≤ secR 9 ∧ secR 9 ≤ 1.065 ∧ π / k ≤ tan (π / k) ∧
      tan (π / k) ≤ 1.0435 * (π / k) := by
  have hk' : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := pi_pos
  have hx0 : 0 < π / k := by positivity
  have hx9 : π / k ≤ π / 9 := div_le_div_of_nonneg_left hpi.le (by norm_num) hk'
  have h9 : π / 9 ≤ 0.349066 := by linarith [pi_lt_d6]
  have hc9 : 0.939 ≤ cos (π / 9) := by
    have := one_sub_sq_div_two_le_cos (x := π / 9)
    have h2 : (π / 9) ^ 2 ≤ 0.349066 ^ 2 := by gcongr
    norm_num at h2 ⊢; linarith
  have hcx : cos (π / 9) ≤ cos (π / k) :=
    cos_le_cos_of_nonneg_of_le_pi hx0.le (by linarith) hx9
  have hc0 : 0 < cos (π / k) := by linarith
  have h99 : (π / (9 : ℕ) : ℝ) = π / 9 := by norm_num
  refine ⟨?_, ?_, ?_, le_tan hx0.le (by linarith), ?_⟩
  · rw [secR, le_div_iff₀ hc0]; linarith [cos_le_one (π / k)]
  · rw [secR, secR, h99]
    exact one_div_le_one_div_of_le (by linarith) hcx
  · rw [secR, h99, div_le_iff₀ (by linarith)]; linarith
  · set x := π / k
    have hx2 : x ^ 2 ≤ 0.12185 := by
      have : x ^ 2 ≤ 0.349066 ^ 2 := by gcongr; linarith
      norm_num at this ⊢; linarith
    have hsin : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
      have h := sin_bound (x := x) (by rw [abs_of_pos hx0]; linarith)
      rw [abs_of_pos hx0] at h
      linarith [le_abs_self (sin x - (x - x ^ 3 / 6))]
    have hcos := one_sub_sq_div_two_le_cos (x := x)
    have hkey : x - x ^ 3 / 6 + x ^ 5 / 100 ≤ 1.0435 * x * (1 - x ^ 2 / 2) := by
      have hx4 : x ^ 4 ≤ 0.12185 ^ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg x) hx2 2
        rw [← pow_mul] at this; simpa using this
      have : (1.0435 / 2 - 1 / 6) * x ^ 2 + x ^ 4 / 100 ≤ 0.0435 := by nlinarith
      nlinarith
    rw [tan_eq_sin_div_cos, div_le_iff₀ hc0]
    have : 1.0435 * x * (1 - x ^ 2 / 2) ≤ 1.0435 * x * cos x := by gcongr
    linarith

/-- `c₃ = π² - (3/4)√3 π ≤ 5.7886`. -/
lemma c3_le : π ^ 2 - 3 / 4 * √3 * π ≤ 5.7886 := by
  have h3 : (1.7320508 : ℝ) ≤ √3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  nlinarith [pi_gt_d6, pi_lt_d6]

lemma c3_pos : 0 < π ^ 2 - 3 / 4 * √3 * π := by
  nlinarith [pi_gt_d6, pi_lt_d6, sqrt_three_lt]

/-- **Corollary 96 (b), `n = 4`, `k ≥ 9`.** Let `a = a₄` be non-increasing on `[1, 2]` (from
the log-concavity of `λ₃`, Prékopa–Leindler, a hypothesis) with `a₄(1) ≥ 3.398` and
`a₄(sec π/9) ≥ 3.143` (Riemann sums in Section 25, hypotheses). With `c₂ = π` and
`c₃ = π² - (3/4)√3 π`, condition (21) holds for `n = 4` and every `k ≥ 9`. -/
theorem cor96b_four {a : ℝ → ℝ} (ha : AntitoneOn a (Icc 1 2)) (ha1 : 3.398 ≤ a 1)
    (ha9 : 3.143 ≤ a (secR 9)) {k : ℕ} (hk : 9 ≤ k) :
    Cond21 4 k (a 1) (a (secR k)) π (π ^ 2 - 3 / 4 * √3 * π) (Ssum 4 k)
      (Nb 4 k π (a (secR k))) := by
  obtain ⟨hR1, hR2, hR9, ht1, ht2⟩ := trig_ge_nine hk
  have hpi := pi_pos
  have haR : a (secR 9) ≤ a (secR k) :=
    ha ⟨hR1, by linarith⟩ ⟨by linarith, by linarith⟩ hR2
  have hpl := pi_gt_d6
  have hpu := pi_lt_d6
  apply cond21_of_bounds (a10 := 3.398) (aR0 := 3.143) (c2u := π) (c1u := 5.7886)
    (τ := 1.0435) (k0 := 9) (by norm_num) (by norm_num) (by exact_mod_cast hk)
    (by linarith) (by norm_num) ha1 le_rfl hpi.le c3_le c3_pos (Ssum_nonneg _ _) (Ssum_le _ _)
    ht1 ht2
  · push_cast; linarith
  · push_cast
    rw [div_le_one (by norm_num)]; nlinarith
  · push_cast
    have hL : 4 * (2 * (4 - 1) * π * 1.0435 * π ^ 2 / (6 * 9 ^ 3 * 3.143)) /
        (3.398 - (4 - 1) * π / 9) ≤ (0.0241 : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      have : π ^ 3 ≤ 31.0063 := by
        have := pow_le_pow_left₀ hpi.le hpu.le 3; norm_num at this; linarith
      have e : 4 * (2 * (4 - 1) * π * 1.0435 * π ^ 2 / (6 * 9 ^ 3 * 3.143)) =
          (24 * 1.0435 / (6 * 729 * 3.143)) * π ^ 3 := by ring
      rw [e]; linarith
    have hR : (0.031 : ℝ) ≤ (1 - (4 - 1) * π * (1.0435 - 1) * π / 3.143) /
        (1.0435 * π * 5.7886) := by
      rw [le_div_iff₀ (by positivity)]
      have hp2 : π ^ 2 ≤ 9.8697 := by nlinarith
      have e : (4 - 1) * π * (1.0435 - 1) * π / 3.143 = (3 * 0.0435 / 3.143) * π ^ 2 := by ring
      rw [e]; linarith
    linarith

/-- **Corollary 96 (b), `n = 4`, `k = 8`.** Here `4 ∣ 8j` for every `j`, so `W = 0`, and (21)
reads `1/|P₈| ≥ N`; it holds with `a₄(sec π/8) ≥ 3.071` (a hypothesis). -/
theorem cor96b_four_eight {a1 aR : ℝ} (ha1 : 3.398 ≤ a1) (haR : 3.071 ≤ aR) :
    Cond21 4 8 a1 aR π (π ^ 2 - 3 / 4 * √3 * π) (Ssum 4 8) (Nb 4 8 π aR) := by
  obtain ⟨hR1, hR2, ht1, ht2⟩ := trig_ge_eight (le_refl 8)
  have hpi := pi_pos
  have hpu := pi_lt_d6
  have hS : Ssum 4 8 = 0 := Ssum_eq_zero_of_dvd (by norm_num)
  have h8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
  refine ⟨by push_cast; linarith, ?_⟩
  have hW : W 4 8 π aR 0 = 0 := by simp [W]
  rw [hS, hW, mul_zero, zero_div]
  apply div_nonneg _ c3_pos.le
  have hX1 : π ≤ area 8 := by
    simp only [area]; rw [h8] at ht1 ⊢
    calc π = 8 * (π / 8) := by ring
      _ ≤ 8 * tan (π / 8) := by gcongr
  have hX2 : area 8 ≤ 1.0825 * π := by
    simp only [area]; rw [h8] at ht2 ⊢
    calc 8 * tan (π / 8) ≤ 8 * (1.0825 * (π / 8)) := by gcongr
      _ = 1.0825 * π := by ring
  have hX0 : 0 < area 8 := by linarith
  simp only [Nb]
  rw [sub_nonneg, div_le_div_iff₀ (by positivity) hX0]
  push_cast
  have : 3 * π * (area 8 - π) ≤ aR := by nlinarith
  nlinarith

/-- **Corollary 96 (b), `n = 5`, `k ≥ 9`.** With `a = a₅` non-increasing on `[1, 2]`
(Prékopa–Leindler, a hypothesis), `a₅(1) ≥ 9.242`, `a₅(sec π/9) ≥ 8.724`, `c₃ = π² - (3/4)√3 π`
and `0 < c₄ ≤ 14.252` (Section 25, hypotheses), condition (21) holds for `n = 5` and every
`k ≥ 9`. -/
theorem cor96b_five {a : ℝ → ℝ} (ha : AntitoneOn a (Icc 1 2)) (ha1 : 9.242 ≤ a 1)
    (ha9 : 8.724 ≤ a (secR 9)) {c4 : ℝ} (hc4 : 0 < c4) (hc4u : c4 ≤ 14.252) {k : ℕ}
    (hk : 9 ≤ k) :
    Cond21 5 k (a 1) (a (secR k)) (π ^ 2 - 3 / 4 * √3 * π) c4 (Ssum 5 k)
      (Nb 5 k (π ^ 2 - 3 / 4 * √3 * π) (a (secR k))) := by
  obtain ⟨hR1, hR2, hR9, ht1, ht2⟩ := trig_ge_nine hk
  have hpi := pi_pos
  have haR : a (secR 9) ≤ a (secR k) :=
    ha ⟨hR1, by linarith⟩ ⟨by linarith, by linarith⟩ hR2
  have hpl := pi_gt_d6
  have hpu := pi_lt_d6
  apply cond21_of_bounds (a10 := 9.242) (aR0 := 8.724) (c2u := 5.7886) (c1u := 14.252)
    (τ := 1.0435) (k0 := 9) (by norm_num) (by norm_num) (by exact_mod_cast hk)
    (by linarith) (by norm_num) ha1 c3_le c3_pos.le hc4u hc4 (Ssum_nonneg _ _) (Ssum_le _ _)
    ht1 ht2
  · push_cast; norm_num
  · push_cast
    rw [div_le_one (by norm_num)]; nlinarith
  · push_cast
    have hL : 5 * (2 * (5 - 1) * 5.7886 * 1.0435 * π ^ 2 / (6 * 9 ^ 3 * 8.724)) /
        (9.242 - (5 - 1) * 5.7886 / 9) ≤ (0.00938 : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]
      have hp2 : π ^ 2 ≤ 9.8697 := by nlinarith
      have e : 5 * (2 * (5 - 1) * 5.7886 * 1.0435 * π ^ 2 / (6 * 9 ^ 3 * 8.724)) =
          (40 * 5.7886 * 1.0435 / (6 * 729 * 8.724)) * π ^ 2 := by ring
      rw [e]; linarith
    have hR : (0.0136 : ℝ) ≤ (1 - (5 - 1) * 5.7886 * (1.0435 - 1) * π / 8.724) /
        (1.0435 * π * 14.252) := by
      rw [le_div_iff₀ (by positivity)]
      have e : (5 - 1) * 5.7886 * (1.0435 - 1) * π / 8.724 = (4 * 5.7886 * 0.0435 / 8.724) * π := by
        ring
      have e2 : (0.0136 : ℝ) * (1.0435 * π * 14.252) = (0.0136 * 1.0435 * 14.252) * π := by ring
      rw [e, e2]; norm_num; linarith
    linarith

/-! ## Theorem 95: the assembly of the complete mix -/

section Assembly

open Room

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {n : ℕ}

/-- **Theorem 95, last step ("the complete mix").** Let `Q` be linear with `Qⁿ = I` and no
eigenvalue `1` (the rotation by `2π/n`), `K` compact of positive volume with centroid `0`,
and `B ⊆ K` measurable and mapped into itself by `Q`. If `β₁` is a permutation-invariant
measure on `𝒯_n(K)` (here `β_C + tλ + η_φ`) and the rest `ρ = U(K) - β̄₁` (here `ν_R dx`) is a
`Q`-invariant measure on `B`, then `U(K)` is `n`-completely mixable: the rest is mixed by the
orbits `(X, QX, …, Q^{n-1}X)` (Remark 81), and Lemma 88 completes the proof. -/
theorem completelyMixable_of_rest (hn : 0 < n) (Q : E →L[ℝ] E) (hQn : Q ^ n = 1)
    (hfix : ∀ x, Q x = x → x = 0) {K B : Set E} (hK : IsCompact K) (hpos : 0 < volume K)
    (hc : centroid K = 0) (hBK : B ⊆ K) (hQB : ∀ x ∈ B, Q x ∈ B)
    (β₁ : Measure (Fin n → E)) (hβP : PermInvariant β₁) (hβT : β₁ (tuples n K 0)ᶜ = 0)
    (ρ : Measure E) (hρB : ρ Bᶜ = 0) (hρQ : ρ.map Q = ρ)
    (hsum : marginal β₁ + ρ = unifSet K) : CompletelyMixable n (unifSet K) := by
  have := Room.unifSet_isProb hK hpos
  rw [completelyMixable_unif_iff hn hK hpos, hc]
  have hQm : Measurable Q := Q.continuous.measurable
  set γ := ρ.map (orbit (n := n) Q) with hγ
  have hpowQ : ∀ i : ℕ, ρ.map ⇑(Q ^ i) = ρ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : ⇑(Q ^ (i + 1)) = ⇑(Q ^ i) ∘ ⇑Q := by
        rw [pow_succ]; rfl
      rw [this, ← Measure.map_map (Q ^ i).continuous.measurable hQm, hρQ, ih]
  have hγmar : ∀ j : Fin n, γ.map (fun x => x j) = ρ := fun j => by
    rw [hγ, Measure.map_map (measurable_pi_apply j) (measurable_orbit Q)]
    exact hpowQ j
  have hpowB : ∀ i : ℕ, ∀ x ∈ B, (Q ^ i) x ∈ B := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro x hx; rw [pow_succ]; exact ih _ (hQB x hx)
  have hγT : γ (tuples n K 0)ᶜ = 0 := by
    rw [hγ, Measure.map_apply (measurable_orbit Q)
      (measurableSet_tuples hK.measurableSet 0).compl]
    refine measure_mono_null ?_ hρB
    intro x hx
    by_contra hxB
    apply hx
    refine ⟨fun i => hBK (hpowB i x (not_not.1 hxB)), ?_⟩
    rw [smul_zero]
    exact orbit_sum_zero Q hQn hfix x
  set β := β₁ + symmetrise γ with hβ
  have hβP' : PermInvariant β := permInvariant_add hβP (permInvariant_symmetrise γ)
  have hβmar : marginal β = unifSet K := by
    rw [hβ, marginal_add, marginal_eq_of_permInvariant (permInvariant_symmetrise γ) ⟨0, hn⟩,
      map_eval_symmetrise γ hγmar, hsum]
  refine ⟨β, ⟨?_⟩, ?_, hβP', hβmar⟩
  · rw [← marginal_univ hn, hβmar, measure_univ]
  · rw [hβ, add_apply, hβT, zero_add]
    exact symmetrise_null γ (measurableSet_tuples hK.measurableSet 0).compl (tuples_perm K 0) hγT

/-- **Theorem 95 (assembly from densities).** In the setting of `completelyMixable_of_rest`,
let `β₁ = β_C + tλ + η_φ` be permutation-invariant on `𝒯_n(K)` with marginal density `d₁`
(`= |P_k|⁻¹ 1_C + ν + t a_n - ν_o`, by `corner_marginal` and `marginal_withDensity_sum`), and let
`d_R` (`= ν_R`) be a nonnegative `Q`-invariant density on `B` with `d₁ + d_R = |K|⁻¹ 1_K`
(`marginal_identity`). If `Q` preserves the volume, `U(K)` is `n`-completely mixable. -/
theorem completelyMixable_of_densities (hn : 0 < n) (Q : E →L[ℝ] E) (hQn : Q ^ n = 1)
    (hfix : ∀ x, Q x = x → x = 0) (hQvol : MeasurePreserving Q volume volume) {K B : Set E}
    (hK : IsCompact K) (hpos : 0 < volume K) (hc : centroid K = 0) (hB : MeasurableSet B)
    (hBK : B ⊆ K) (hQB : ∀ x ∈ B, Q x ∈ B)
    (β₁ : Measure (Fin n → E)) (hβP : PermInvariant β₁) (hβT : β₁ (tuples n K 0)ᶜ = 0)
    {d₁ dR : E → ℝ} (hd₁ : Measurable d₁) (hdR : Measurable dR)
    (hmar : marginal β₁ = volume.withDensity fun q => ENNReal.ofReal (d₁ q))
    (hd₁0 : ∀ q, 0 ≤ d₁ q) (hdR0 : ∀ q, 0 ≤ dR q) (hdRB : ∀ q, q ∉ B → dR q = 0)
    (hdRQ : ∀ q, dR (Q q) = dR q)
    (hid : ∀ q, d₁ q + dR q = K.indicator 1 q / (volume K).toReal) :
    CompletelyMixable n (unifSet K) := by
  set ρ := volume.withDensity fun q => ENNReal.ofReal (dR q) with hρ
  have hfR : Measurable fun q => ENNReal.ofReal (dR q) := ENNReal.measurable_ofReal.comp hdR
  refine completelyMixable_of_rest hn Q hQn hfix hK hpos hc hBK hQB β₁ hβP hβT ρ ?_ ?_ ?_
  · rw [hρ, withDensity_apply _ hB.compl]
    apply setLIntegral_eq_zero hB.compl
    · intro q hq; simp [hdRB q hq]
  · ext S hS
    rw [Measure.map_apply hQvol.measurable hS, hρ, withDensity_apply _ (hQvol.measurable hS),
      withDensity_apply _ hS, ← hQvol.setLIntegral_comp_preimage hS hfR]
    simp only [hdRQ]
  · rw [hmar, hρ, ← withDensity_add_left (f := fun q => ENNReal.ofReal (d₁ q))
      (ENNReal.measurable_ofReal.comp hd₁),
      Mixes.unifSet_eq_withDensity hK.measurableSet hpos.ne' hK.measure_lt_top.ne]
    congr 1
    ext q
    rw [Pi.add_apply, ← ENNReal.ofReal_add (hd₁0 q) (hdR0 q), hid]

end Assembly

/-! ## Theorem 95: Fourier coefficients on the circle -/

section Fourier

open Complex in
/-- The filter of the roots of unity: `∑_{j<m} e^{2πiκj/m}` is `m` if `m ∣ κ` and `0`
otherwise. -/
lemma sum_exp_root (m : ℕ) (hm : 0 < m) (κ : ℤ) :
    ∑ j ∈ Finset.range m, exp (2 * π * I * κ * j / m) = if (m : ℤ) ∣ κ then (m : ℂ) else 0 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  set z := exp (2 * π * I * κ / m) with hz
  have hterm : ∀ j : ℕ, exp (2 * π * I * κ * j / m) = z ^ j := fun j => by
    rw [hz, ← Complex.exp_natCast_mul]; congr 1; ring
  simp only [hterm]
  have hzm : z ^ m = 1 := by
    rw [hz, ← Complex.exp_natCast_mul]
    have : (m : ℂ) * (2 * π * I * κ / m) = κ * (2 * π * I) := by field_simp
    rw [this, exp_int_mul_two_pi_mul_I]
  split_ifs with h
  · obtain ⟨l, rfl⟩ := h
    have : z = 1 := by
      rw [hz]
      have : 2 * π * I * ((m * l : ℤ) : ℂ) / m = l * (2 * π * I) := by push_cast; field_simp
      rw [this, exp_int_mul_two_pi_mul_I]
    simp [this]
  · have hz1 : z ≠ 1 := by
      intro h1
      obtain ⟨l, hl⟩ := exp_eq_one_iff.1 h1
      apply h
      refine ⟨l, ?_⟩
      have hpi : (2 * π * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, I_ne_zero]
      have : (κ : ℂ) = m * l := by
        have := hl
        field_simp at this
        linear_combination this
      exact_mod_cast this
    rw [geom_sum_eq hz1, hzm, sub_self, zero_div]

open Complex in
/-- **The symmetric part (`ν_s`).** Averaging `e^{iκθ}` over the rotations by `2π/n` keeps the
frequencies `κ` with `n ∣ κ` and removes the others:
`(1/n) ∑_{i<n} e^{iκ(θ + 2πi/n)} = [n ∣ κ] e^{iκθ}`. -/
lemma avg_rot_exp (n : ℕ) (hn : 0 < n) (κ : ℤ) (θ : ℝ) :
    (n : ℂ)⁻¹ * ∑ i ∈ Finset.range n, exp (I * κ * (θ + 2 * π * i / n)) =
      if (n : ℤ) ∣ κ then exp (I * κ * θ) else 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : ∀ i : ℕ, exp (I * κ * ((θ : ℂ) + 2 * π * i / n)) =
      exp (I * κ * θ) * exp (2 * π * I * κ * i / n) := fun i => by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [this, ← Finset.mul_sum, sum_exp_root n hn κ]
  split_ifs
  · field_simp
  · simp

open Complex in
/-- The integral of `e^{-iκφ}` over an arc of half-width `w` centred at `c`:
`e^{-iκc} · 2 sin(κw)/κ`. -/
lemma integral_arc {κ : ℝ} (hκ : κ ≠ 0) (c w : ℝ) :
    ∫ φ in (c - w)..(c + w), exp (-(I * κ) * φ) =
      exp (-(I * κ) * c) * (2 * (Real.sin (κ * w) : ℂ) / κ) := by
  have hc : -(I * κ) ≠ 0 := by simp [I_ne_zero, hκ]
  rw [integral_exp_mul_complex hc]
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  rw [ofReal_sin, Complex.sin]
  push_cast
  have e1 : exp (-(I * κ) * (c + w)) = exp (-(I * κ) * c) * exp (-(κ * w) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : exp (-(I * κ) * (c - w)) = exp (-(I * κ) * c) * exp ((κ * w) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2]
  field_simp
  ring_nf
  rw [I_sq]
  ring

open Complex in
/-- **The `k` arcs of the corners.** At a radius `ρ ∈ (1, R)` the corners of `P_k` meet the
circle in `k` arcs of a common half-width `w` centred at the directions `2πj/k` of the
vertices. The integral of `e^{-iκφ}` over them is `[k ∣ κ] · k · 2 sin(κw)/κ`; so it vanishes
unless `k ∣ κ`, and its absolute value is at most `2k/|κ|`. -/
lemma integral_arcs (k : ℕ) (hk : 0 < k) {κ : ℤ} (hκ : κ ≠ 0) (w : ℝ) :
    ∑ j ∈ Finset.range k, ∫ φ in (2 * π * j / k - w)..(2 * π * j / k + w),
        exp (-(I * κ) * φ) =
      (if (k : ℤ) ∣ κ then (k : ℂ) else 0) * (2 * (Real.sin (κ * w) : ℂ) / κ) ∧
    ‖∑ j ∈ Finset.range k, ∫ φ in (2 * π * j / k - w)..(2 * π * j / k + w),
        exp (-(I * κ) * φ)‖ ≤ 2 * k / |(κ : ℝ)| := by
  have hκr : (κ : ℝ) ≠ 0 := by exact_mod_cast hκ
  have hsum : ∑ j ∈ Finset.range k, ∫ φ in (2 * π * j / k - w)..(2 * π * j / k + w),
        exp (-(I * κ) * φ) =
      (if (k : ℤ) ∣ κ then (k : ℂ) else 0) * (2 * (Real.sin (κ * w) : ℂ) / κ) := by
    have h1 : ∀ j : ℕ, ∫ φ in (2 * π * j / k - w)..(2 * π * j / k + w),
        exp (-(I * κ) * φ) =
        exp (2 * π * I * ((-κ : ℤ) : ℂ) * j / k) * (2 * (Real.sin (κ * w) : ℂ) / κ) := by
      intro j
      have := integral_arc hκr (2 * π * j / k) w
      push_cast at this ⊢
      rw [this]
      congr 2
      ring
    simp only [h1, ← Finset.sum_mul, sum_exp_root k hk, dvd_neg]
  refine ⟨hsum, ?_⟩
  rw [hsum, norm_mul]
  have hs : ‖(2 * (Real.sin (κ * w) : ℂ) / κ)‖ ≤ 2 / |(κ : ℝ)| := by
    rw [norm_div, norm_mul]
    have : ‖((κ : ℤ) : ℂ)‖ = |(κ : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [this]
    gcongr
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := abs_sin_le_one ((κ : ℝ) * w)
    norm_num
    linarith
  have hk' : ‖(if (k : ℤ) ∣ κ then (k : ℂ) else 0)‖ ≤ k := by
    split_ifs <;> simp
  calc _ ≤ (k : ℝ) * (2 / |(κ : ℝ)|) := by gcongr
    _ = 2 * k / |(κ : ℝ)| := by ring

/-- The integral of `cos(κψ)` over an initial segment of `(0, L]`: if `A ∩ (0, L]` is an initial
segment (here a superlevel set `{s < g}` of a function `g` non-increasing on `[0, L]`), the
integral is `sin(κb)/κ` for its supremum `b`, so at most `1/|κ|` in absolute value. -/
lemma abs_setIntegral_superlevel_cos_le {g : ℝ → ℝ} (hgm : Measurable g) {L : ℝ}
    (hg : AntitoneOn g (Icc 0 L)) (s : ℝ) {κ : ℝ} (hκ : κ ≠ 0) :
    |∫ ψ in Ioc 0 L, {ψ | s < g ψ}.indicator (fun ψ => cos (κ * ψ)) ψ| ≤ 1 / |κ| := by
  have hA : MeasurableSet {ψ | s < g ψ} := measurableSet_lt measurable_const hgm
  rw [setIntegral_indicator hA]
  set X := Ioc 0 L ∩ {ψ | s < g ψ} with hX
  by_cases hne : X.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have hbdd : BddAbove X := ⟨L, fun ψ hψ => hψ.1.2⟩
  set b := sSup X with hb
  obtain ⟨ψ₀, hψ₀⟩ := hne
  have hb0 : 0 ≤ b := le_trans hψ₀.1.1.le (le_csSup hbdd hψ₀)
  have hsub : X ⊆ Ioc 0 b := fun ψ hψ => ⟨hψ.1.1, le_csSup hbdd hψ⟩
  have hdiff : ∀ ψ ∈ Ioc 0 b \ X, ψ = b := by
    rintro ψ ⟨⟨hψ0, hψb⟩, hψX⟩
    by_contra hne'
    have hlt : ψ < b := lt_of_le_of_ne hψb hne'
    obtain ⟨ψ', hψ'X, hψψ'⟩ := exists_lt_of_lt_csSup ⟨ψ₀, hψ₀⟩ hlt
    apply hψX
    refine ⟨⟨hψ0, hψψ'.le.trans hψ'X.1.2⟩, ?_⟩
    have : g ψ' ≤ g ψ := hg ⟨hψ0.le, hψψ'.le.trans hψ'X.1.2⟩
      ⟨(hψ0.trans hψψ').le, hψ'X.1.2⟩ hψψ'.le
    exact lt_of_lt_of_le hψ'X.2 this
  have hae : ∀ᵐ ψ ∂(volume : Measure ℝ), ψ ∈ Ioc 0 b \ X → cos (κ * ψ) = 0 := by
    have : ∀ᵐ ψ ∂(volume : Measure ℝ), ψ ≠ b := by
      rw [ae_iff]; simp
    filter_upwards [this] with ψ hψ h
    exact absurd (hdiff ψ h) hψ
  rw [← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet hsub hae,
    ← intervalIntegral.integral_of_le hb0, intervalIntegral.integral_comp_mul_left
      (fun x => cos x) hκ, integral_cos, mul_zero, sin_zero, sub_zero, smul_eq_mul, abs_mul,
    abs_inv, one_div]
  calc |κ|⁻¹ * |sin (κ * b)| ≤ |κ|⁻¹ * 1 := by gcongr; exact abs_sin_le_one _
    _ = |κ|⁻¹ := mul_one _

/-- The layer-cake formula `x = ∫₀^C 1[s < x] ds` for `0 ≤ x ≤ C`. -/
lemma layer_cake {x C : ℝ} (h0 : 0 ≤ x) (hC : x ≤ C) :
    ∫ s in Ioc 0 C, (Iio x).indicator (fun _ => (1 : ℝ)) s = x := by
  rw [setIntegral_indicator measurableSet_Iio, setIntegral_const, smul_eq_mul, mul_one]
  have : Ioc 0 C ∩ Iio x = Ioo 0 x := by
    ext s; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
  rw [this, Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal h0]

/-- **Fourier coefficients of a monotone function** (the bound `2c_{n-2}/|κ|` for `g(p, ·)`).
If `g` is non-increasing on `[0, L]` with values in `[0, C]`, then
`|∫₀^L g(ψ) cos(κψ) dψ| ≤ C/|κ|`: by the layer-cake formula and Fubini's theorem the integral
is an average over `s ∈ (0, C)` of integrals of `cos(κψ)` over initial segments. For an even
function on the circle, non-increasing on `[0, π]`, this gives the bound `2C/|κ|` for its
Fourier coefficient. -/
theorem abs_integral_antitone_mul_cos_le {g : ℝ → ℝ} (hgm : Measurable g) {L C κ : ℝ}
    (hL : 0 ≤ L) (hκ : κ ≠ 0) (hg : AntitoneOn g (Icc 0 L)) (hg0 : ∀ ψ ∈ Icc 0 L, 0 ≤ g ψ)
    (hgC : ∀ ψ ∈ Icc 0 L, g ψ ≤ C) :
    |∫ ψ in (0 : ℝ)..L, g ψ * cos (κ * ψ)| ≤ C / |κ| := by
  rw [intervalIntegral.integral_of_le hL]
  have hC : 0 ≤ C := by
    have := hg0 0 ⟨le_rfl, hL⟩; have := hgC 0 ⟨le_rfl, hL⟩; linarith
  set F : ℝ → ℝ → ℝ := fun ψ s => {ψ | s < g ψ}.indicator (fun ψ => cos (κ * ψ)) ψ with hF
  have hlayer : ∀ ψ ∈ Ioc 0 L, g ψ * cos (κ * ψ) = ∫ s in Ioc 0 C, F ψ s := by
    intro ψ hψ
    have hψ' : ψ ∈ Icc 0 L := Ioc_subset_Icc_self hψ
    rw [← layer_cake (hg0 ψ hψ') (hgC ψ hψ'), ← integral_mul_const]
    congr 1; ext s
    simp only [hF, indicator, mem_Iio, mem_ofPred_eq]
    split_ifs <;> simp
  rw [setIntegral_congr_fun measurableSet_Ioc hlayer]
  have hmeas : Measurable (Function.uncurry F) := by
    have hset : MeasurableSet {z : ℝ × ℝ | z.2 < g z.1} :=
      measurableSet_lt measurable_snd (hgm.comp measurable_fst)
    have : Function.uncurry F = {z : ℝ × ℝ | z.2 < g z.1}.indicator
        (fun z => cos (κ * z.1)) := by
      ext ⟨a, b⟩; simp [hF, indicator]
    rw [this]
    exact (continuous_cos.comp (continuous_const.mul continuous_fst)).measurable.indicator hset
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioc 0 C))) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, hF, indicator]
    split_ifs
    · rw [Real.norm_eq_abs]; exact abs_cos_le_one _
    · simp
  rw [integral_integral_swap hint]
  have hb : ∀ s ∈ Ioc 0 C, ‖∫ ψ in Ioc 0 L, F ψ s‖ ≤ 1 / |κ| := fun s _ => by
    rw [Real.norm_eq_abs]; exact abs_setIntegral_superlevel_cos_le hgm hg s hκ
  have := norm_setIntegral_le_of_norm_le_const
    (measure_Ioc_lt_top (μ := (volume : Measure ℝ))) hb
  rw [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hC] at this
  calc _ ≤ 1 / |κ| * C := this
    _ = C / |κ| := by ring

end Fourier

/-! ## Theorem 95: the Neumann series for `G_κ` -/

/-- **The Neumann series.** In a complete normed ring (for `G_κ`: the bounded operators on
bounded functions on `[0, 1]`), let `a` be invertible with `‖a⁻¹‖ ≤ 1/α` (multiplication by
`a_n ≥ a_n(1) = α`) and `‖s‖ ≤ σ < α` (for `s = (n-1)T_κ`, `σ = (n-1)c_{n-2}/k`). Then `a + s`
is invertible with `‖(a + s)⁻¹‖ ≤ 1/(α - σ)`; so `G_κ = (a + s)/n` has an inverse of norm at
most `n/(α - σ) = n/(a_n(1) - (n-1)c_{n-2}/k)`. -/
theorem neumann {R : Type*} [NormedRing R] [CompleteSpace R] (h1 : ‖(1 : R)‖ ≤ 1) (a : Rˣ)
    (s : R) {α σ : ℝ} (hα : 0 < α) (ha : ‖((a⁻¹ : Rˣ) : R)‖ ≤ 1 / α) (hs : ‖s‖ ≤ σ)
    (hσ : σ < α) :
    ∃ b : R, (a + s) * b = 1 ∧ b * (a + s) = 1 ∧ ‖b‖ ≤ 1 / (α - σ) := by
  set u : R := ((a⁻¹ : Rˣ) : R) * s with hu
  have hσ0 : 0 ≤ σ := le_trans (norm_nonneg _) hs
  have hu1 : ‖u‖ ≤ σ / α := by
    calc ‖u‖ ≤ ‖((a⁻¹ : Rˣ) : R)‖ * ‖s‖ := norm_mul_le _ _
      _ ≤ 1 / α * σ := by gcongr
      _ = σ / α := by ring
  have hσα : σ / α < 1 := by rw [div_lt_one hα]; exact hσ
  have hu' : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  set v := ∑' i : ℕ, (-u) ^ i with hv
  have hv1 : v * (1 + u) = 1 := by
    have := geom_series_mul_neg (-u) hu'; rwa [sub_neg_eq_add] at this
  have hv2 : (1 + u) * v = 1 := by
    have := mul_neg_geom_series (-u) hu'; rwa [sub_neg_eq_add] at this
  have hfac : (a : R) + s = a * (1 + u) := by
    rw [hu, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨v * ((a⁻¹ : Rˣ) : R), ?_, ?_, ?_⟩
  · rw [hfac, mul_assoc, ← mul_assoc (1 + u), hv2, one_mul, Units.mul_inv]
  · rw [hfac, mul_assoc, ← mul_assoc ((a⁻¹ : Rˣ) : R), Units.inv_mul, one_mul, hv1]
  · have hvn : ‖v‖ ≤ (1 - σ / α)⁻¹ := by
      have := tsum_geometric_le_of_norm_lt_one (-u) hu'
      rw [norm_neg] at this
      have h2 : (1 - ‖u‖)⁻¹ ≤ (1 - σ / α)⁻¹ := by
        gcongr
      linarith
    calc ‖v * ((a⁻¹ : Rˣ) : R)‖ ≤ ‖v‖ * ‖((a⁻¹ : Rˣ) : R)‖ := norm_mul_le _ _
      _ ≤ (1 - σ / α)⁻¹ * (1 / α) := by gcongr
      _ = 1 / (α - σ) := by
          have : α - σ ≠ 0 := by linarith
          field_simp


/-! ## Theorem 95: the bounds on the coefficients of `ν` and the sum `W` -/

lemma tan_pos_of_three {k : ℕ} (hk : 3 ≤ k) : 0 < tan (π / k) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  apply tan_pos_of_pos_of_lt_pi_div_two (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [pi_pos]

lemma cos_pi_div_pos {k : ℕ} (hk : 3 ≤ k) : 0 < cos (π / k) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  apply cos_pos_of_mem_Ioo ⟨_, _⟩
  · have : 0 < π / k := by positivity
    linarith [pi_pos]
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]

lemma one_le_secR {k : ℕ} (hk : 3 ≤ k) : 1 ≤ secR k := by
  rw [secR, le_div_iff₀ (cos_pi_div_pos hk)]; linarith [cos_le_one (π / k)]

/-- `R² - 1 = tan²(π/k)` for `R = sec(π/k)`. -/
lemma secR_sq_sub_one {k : ℕ} (hk : 3 ≤ k) : secR k ^ 2 - 1 = tan (π / k) ^ 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : cos (π / k) ≠ 0 := by
    apply (cos_pos_of_mem_Ioo ⟨_, _⟩).ne'
    · have : 0 < π / k := by positivity
      linarith [pi_pos]
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]
  rw [secR, tan_eq_sin_div_cos]
  field_simp
  linarith [sin_sq_add_cos_sq (π / k)]

/-- `∫₁^R ρ/a(ρ) dρ ≤ (R² - 1)/(2 a(R))` when `a ≥ a(R) > 0` on `[1, R]`. -/
lemma integral_rho_div_le {a : ℝ → ℝ} {R aR : ℝ} (hR : 1 ≤ R) (haR : 0 < aR)
    (ha : ∀ ρ ∈ Icc 1 R, aR ≤ a ρ) :
    ∫ ρ in (1 : ℝ)..R, ρ / a ρ ≤ (R ^ 2 - 1) / (2 * aR) := by
  by_cases hi : IntervalIntegrable (fun ρ => ρ / a ρ) volume 1 R
  · have h1 : ∫ ρ in (1 : ℝ)..R, ρ / a ρ ≤ ∫ ρ in (1 : ℝ)..R, ρ / aR := by
      apply intervalIntegral.integral_mono_on hR hi
      · exact (continuous_id.div_const _).intervalIntegrable _ _
      · intro ρ hρ
        have : 0 < a ρ := lt_of_lt_of_le haR (ha ρ hρ)
        have h0 : 0 ≤ ρ := by linarith [hρ.1]
        gcongr
        exact ha ρ hρ
    have h2 : ∫ ρ in (1 : ℝ)..R, ρ / aR = (R ^ 2 - 1) / (2 * aR) := by
      rw [intervalIntegral.integral_div, integral_id]; field_simp
    linarith
  · rw [intervalIntegral.integral_undef hi]
    have : 0 ≤ R ^ 2 - 1 := by nlinarith
    positivity

/-- **The bound on `ν_κ`.** Inserting the bounds `2c_{n-2}/|κ|` (variation of `g`) and `2k/|κ|`
(the `k` arcs) into `ν_κ(r) = (1/2π) ∫ ν(re^{iθ}) e^{-iκθ} dθ`:
`(n-1)/|P_k| ∫₁^R ρ/a_n(ρ) · (1/2π)(2c/|κ|)(2k/|κ|) dρ ≤ (n-1) k c (R² - 1)/(π |P_k| a_n(R) κ²)`. -/
lemma coeff_bound {n k : ℕ} (hn : 1 ≤ n) (hk : 3 ≤ k) {a : ℝ → ℝ} {c aR κ : ℝ} (hc : 0 ≤ c)
    (haR : 0 < aR) (ha : ∀ ρ ∈ Icc 1 (secR k), aR ≤ a ρ) (hκ : κ ≠ 0) :
    (n - 1) / area k * (∫ ρ in (1 : ℝ)..secR k, ρ / a ρ) * (1 / (2 * π)) * (2 * c / |κ|) *
        (2 * k / |κ|) ≤
      (n - 1) * k * c * (secR k ^ 2 - 1) / (π * area k * aR * κ ^ 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ht := tan_pos_of_three hk
  have hA : 0 < area k := by simp only [area]; positivity
  have hR : 1 ≤ secR k := one_le_secR hk
  have hint := integral_rho_div_le hR haR ha
  have hn1 : (0 : ℝ) ≤ n - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hκ2 : |κ| ^ 2 = κ ^ 2 := sq_abs κ
  have hκp : 0 < |κ| := abs_pos.2 hκ
  calc (n - 1) / area k * (∫ ρ in (1 : ℝ)..secR k, ρ / a ρ) * (1 / (2 * π)) * (2 * c / |κ|) *
        (2 * k / |κ|)
      ≤ (n - 1) / area k * ((secR k ^ 2 - 1) / (2 * aR)) * (1 / (2 * π)) * (2 * c / |κ|) *
        (2 * k / |κ|) := by gcongr
    _ = (n - 1) * k * c * (secR k ^ 2 - 1) / (π * area k * aR * κ ^ 2) := by
        rw [← hκ2]; field_simp

/-- With `R² - 1 = tan²(π/k)` and `|P_k| = k tan(π/k)`, the bound at `κ = jk` is
`(n-1) c tan(π/k)/(π k² a_n(R) j²)`. -/
lemma coeff_bound_eq {n k j : ℕ} (hk : 3 ≤ k) (c aR : ℝ) (haR : aR ≠ 0) (hj : j ≠ 0) :
    (n - 1) * k * c * (secR k ^ 2 - 1) / (π * area k * aR * ((j : ℝ) * k) ^ 2) =
      (n - 1) * c * tan (π / k) / (π * k ^ 2 * aR) * (1 / (j : ℝ) ^ 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ht := (tan_pos_of_three hk).ne'
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  rw [secR_sq_sub_one hk, area]
  have : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The sum `W`.** Summing the bound of `coeff_bound_eq` over the set `M` of the frequencies
`κ = ±jk` with `n ∤ jk` (two signs for each `j`) gives exactly `W`. -/
lemma hasSum_W (n k : ℕ) (c aR : ℝ) :
    HasSum (fun j : ℕ => if ¬ n ∣ j * k then
        2 * ((n - 1) * c * tan (π / k) / (π * k ^ 2 * aR) * (1 / (j : ℝ) ^ 2)) else 0)
      (W n k c aR (Ssum n k)) := by
  have h := ((summable_Ssum n k).hasSum).mul_left (2 * ((n - 1) * c * tan (π / k) /
    (π * k ^ 2 * aR)))
  rw [W, Ssum]
  convert h using 1
  · ext j; split_ifs <;> ring
  · ring

/-- **The bound on `T_κ`:** `∫₀¹ M s (2c/|κ|) ds = M c/|κ|`, so `|T_κ f| ≤ c ‖f‖_∞/|κ|`. -/
lemma integral_T_bound (M c κ : ℝ) :
    ∫ s in (0 : ℝ)..1, M * s * (2 * c / |κ|) = M * c / |κ| := by
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
  ring

/-! ## Theorem 95: the partner density, its symmetric part, and (21) ⇒ (22) -/

section Pointwise

variable {E : Type*}

/-- **The bound `ν ≤ N`.** If `f = g(·, q)/a_n(|·|) ≤ c/a_n(R)` on the corners `C` (from
`g ≤ c_{n-2}` and `a_n ≥ a_n(R) > 0`), and `C` has area `|P_k| - π`, then
`ν(q) = (n-1)/|P_k| ∫_C f ≤ N = (n-1) c (|P_k| - π)/(|P_k| a_n(R))`. -/
lemma nu_le_N [MeasureSpace E] {C : Set E} (hC : MeasurableSet C) (hCfin : volume C ≠ ⊤)
    {f : E → ℝ} (hfi : IntegrableOn f C) {c aR A : ℝ} (haR : 0 < aR) (hA : 0 < A)
    (hf : ∀ p ∈ C, f p ≤ c / aR) {m : ℝ} (hm : 0 ≤ m) (hvol : volume.real C = A - π) :
    m / A * ∫ p in C, f p ≤ m * c * (A - π) / (A * aR) := by
  have h : ∫ p in C, f p ≤ c / aR * volume.real C := by
    calc ∫ p in C, f p ≤ ∫ _ in C, c / aR :=
          setIntegral_mono_on hfi (integrableOn_const hCfin) hC hf
      _ = c / aR * volume.real C := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  calc m / A * ∫ p in C, f p ≤ m / A * (c / aR * volume.real C) := by gcongr
    _ = m * c * (A - π) / (A * aR) := by rw [hvol]; field_simp

/-- The average `ν_s = (1/n) ∑_{i<n} ν ∘ Qⁱ` over the rotations by `2π/n` (equation (23)). -/
def avgRot (n : ℕ) (Q : E → E) (ν : E → ℝ) (q : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ν (Q^[i] q)

/-- `ν_s` is invariant under `Q` when `Qⁿ = I`. -/
lemma avgRot_comp (n : ℕ) {Q : E → E} (hQ : Q^[n] = id) (ν : E → ℝ) (q : E) :
    avgRot n Q ν (Q q) = avgRot n Q ν q := by
  simp only [avgRot]
  congr 1
  have h : ∀ i, Q^[i] (Q q) = Q^[i + 1] q := fun i => by
    rw [Function.iterate_succ_apply]
  simp only [h]
  have h1 := Finset.sum_range_succ' (fun i => ν (Q^[i] q)) n
  have h2 := Finset.sum_range_succ (fun i => ν (Q^[i] q)) n
  have h3 : Q^[n] q = q := by rw [hQ]; rfl
  simp only [h3, Function.iterate_zero, id_eq] at h1 h2
  linarith

/-- `ν_s ≤ N` when `ν ≤ N` on the `Q`-orbit. -/
lemma avgRot_le (n : ℕ) (hn : 0 < n) {Q : E → E} {ν : E → ℝ} {N : ℝ} (q : E)
    (h : ∀ i, ν (Q^[i] q) ≤ N) : avgRot n Q ν q ≤ N := by
  simp only [avgRot]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_mul_le_iff₀ hn']
  calc ∑ i ∈ Finset.range n, ν (Q^[i] q) ≤ ∑ _i ∈ Finset.range n, N :=
        Finset.sum_le_sum fun i _ => h i
    _ = n * N := by simp

/-- **(21) implies (22).** Let (21) hold, `c_{n-1} > 0`, and on `B` let `ν_s ≤ N`,
`a_n ≤ c_{n-1}` and `|φ| ≤ nW/(a_n(1) - (n-1)c_{n-2}/k)` (the Neumann bound). Then
`t = (1/|P_k| - N)/c_{n-1}` satisfies `|φ| ≤ t` and `ν_s + t a_n ≤ 1/|P_k|` on `B`. -/
theorem pointwise_of_cond21 {n k : ℕ} {a1 aR c2 c1 S N : ℝ}
    (h : Cond21 n k a1 aR c2 c1 S N) (hc1 : 0 < c1) {B : Set E} {νs a φ : E → ℝ}
    (hν : ∀ q ∈ B, νs q ≤ N) (ha : ∀ q ∈ B, a q ≤ c1)
    (hφ : ∀ q ∈ B, |φ q| ≤ n * W n k c2 aR S / (a1 - (n - 1) * c2 / k)) :
    (∀ q ∈ B, |φ q| ≤ (1 / area k - N) / c1) ∧
      ∀ q ∈ B, νs q + (1 / area k - N) / c1 * a q ≤ 1 / area k := by
  obtain ⟨_, h2⟩ := h
  refine ⟨fun q hq => (hφ q hq).trans h2, fun q hq => ?_⟩
  have ht : 0 ≤ (1 / area k - N) / c1 := le_trans (abs_nonneg _) ((hφ q hq).trans h2)
  have h1 : (1 / area k - N) / c1 * a q ≤ (1 / area k - N) / c1 * c1 :=
    mul_le_mul_of_nonneg_left (ha q hq) ht
  rw [div_mul_cancel₀ _ hc1.ne'] at h1
  linarith [hν q hq]

/-- **The three components and the marginal identity (pointwise).** On `P_k = B ∪ C` with
`B ∩ C = ∅`: the corner density `|P_k|⁻¹ 1_C + ν`, the correction `t a_n - ν_o` with
`ν_o = ν - ν_s` (the marginal of `tλ + η_φ`, since `Gφ = -ν_o`), and the rest
`ν_R = (|P_k|⁻¹ - t a_n) 1_B - ν_s` add up to `|P_k|⁻¹ 1_{P_k}`. -/
lemma marginal_identity (P B C : Set E) (hPBC : P = B ∪ C) (hBC : Disjoint B C) (A t : ℝ)
    (ν νs a : E → ℝ) (q : E) :
    (C.indicator (fun _ => A⁻¹) q + ν q) + (t * a q - (ν q - νs q)) +
        (B.indicator (fun _ => A⁻¹) q - t * a q - νs q) = P.indicator (fun _ => A⁻¹) q := by
  rw [hPBC, indicator_union_of_disjoint hBC]
  ring

/-- **Nonnegativity of the correction.** If `|φ| ≤ t` on `B`, the density
`(1/n) ∑ᵢ (t + φ(xᵢ))` of `tλ + η_φ` with respect to `λ` is nonnegative on `𝒯_n(B)`. -/
lemma correction_nonneg {n : ℕ} {B : Set E} {φ : E → ℝ} {t : ℝ} (hφ : ∀ q ∈ B, |φ q| ≤ t)
    (x : Fin n → E) (hx : ∀ i, x i ∈ B) : 0 ≤ (n : ℝ)⁻¹ * ∑ i, (t + φ (x i)) := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => by linarith [neg_abs_le (φ (x i)), hφ (x i) (hx i)]

/-- **Nonnegativity of the rest.** Condition (22) is exactly `ν_R ≥ 0` on `B`. -/
lemma rest_nonneg {A t : ℝ} {νs a : E → ℝ} {q : E} (h : νs q + t * a q ≤ 1 / A) :
    0 ≤ 1 / A - t * a q - νs q := by linarith

end Pointwise

/-! ## Corollary 96 (d): bookkeeping -/

section Bookkeeping

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [MeasurableSingletonClass E]
  [MeasurableAdd₂ E]

/-- **Remark 81**: `n = 3, 4, 5` generate every `n ≥ 3` under addition, so `3`-, `4`- and
`5`-complete mixability give `n`-complete mixability for every `n ≥ 3`. -/
theorem all_of_three_four_five {μ : Measure E} (h3 : CompletelyMixable 3 μ)
    (h4 : CompletelyMixable 4 μ) (h5 : CompletelyMixable 5 μ) :
    ∀ n : ℕ, 3 ≤ n → CompletelyMixable n μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with h | h | h | h
    · rw [h]; exact h3
    · rw [h]; exact h4
    · rw [h]; exact h5
    · have := ScaledB.completelyMixable_add_add (ih (n - 3) (by omega) (by omega)) h3
      rwa [show n - 3 + 3 = n by omega] at this

end Bookkeeping

section Bookkeeping2

variable {E : Type*} [MeasureSpace E] [AddCommGroup E] [MeasurableSingletonClass E]
  [MeasurableAdd₂ E] [MeasurableSub E]

/-- **Corollary 96 (d), `n ≥ 3`.** Let `P k` be the regular `k`-gon and `a n`, `c m` the
functions `a_n` and the constants `c_m` of Theorem 95 (with `a 3 = lens`, `c 1 = 1`, `c 2 = π`,
`c 3 = π² - (3/4)√3 π`, and the floating-point bounds of Section 25 on `a 4`, `a 5`, `c 4`).
Hypotheses: Theorem 95 in the form `hthm` (condition (21), with either form of `N` for `n = 3`,
gives complete mixability); the triangle (Corollary 44), the square and the hexagon (Lemma 50
with Remark 81) for `n = 3, 4, 5`; the rotation of order `5` of the pentagon (Remark 81); and the
four cases of (c), whose condition (22) is only checked numerically; and the central symmetry
of `U(P₈)` (`hsym8`), which (d) does not mention but needs: (21) fails for `(k, n) = (8, 5)`
(Table 14), and `5 = 2 + 3` with `2`-complete mixability from the central symmetry. Then `U(P_k)` is
`n`-completely mixable for every `k ≥ 3` and every `n ≥ 3`. The cases `k ≥ 7` use (a) and (b),
proved above. -/
theorem cor96d (P : ℕ → Set E) (a : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (ha3 : a 3 = lens) (hc1 : c 1 = 1) (hc2 : c 2 = π) (hc3 : c 3 = π ^ 2 - 3 / 4 * √3 * π)
    (ha4 : AntitoneOn (a 4) (Icc 1 2)) (ha41 : 3.398 ≤ a 4 1) (ha49 : 3.143 ≤ a 4 (secR 9))
    (ha48 : 3.071 ≤ a 4 (secR 8))
    (ha5 : AntitoneOn (a 5) (Icc 1 2)) (ha51 : 9.242 ≤ a 5 1) (ha59 : 8.724 ≤ a 5 (secR 9))
    (hc4 : 0 < c 4) (hc4u : c 4 ≤ 14.252)
    (cap : ℝ) (hcap : cap ≤ 0.1279)
    (hthm : ∀ n k : ℕ, 3 ≤ n → 3 ≤ k → ∀ N : ℝ,
      (N = Nb n k (c (n - 2)) (a n (secR k)) ∨
        (n = 3 ∧ k = 7 ∧ N = 2 * cap / (area k * lens (secR k)))) →
      Cond21 n k (a n 1) (a n (secR k)) (c (n - 2)) (c (n - 1)) (Ssum n k) N →
      CompletelyMixable n (unifSet (P k)))
    (htri : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (unifSet (P 3)))
    (hsq : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (unifSet (P 4)))
    (hhex : ∀ n, n = 3 ∨ n = 4 ∨ n = 5 → CompletelyMixable n (unifSet (P 6)))
    (hpent5 : CompletelyMixable 5 (unifSet (P 5)))
    (hc53 : CompletelyMixable 3 (unifSet (P 5))) (hc54 : CompletelyMixable 4 (unifSet (P 5)))
    (hc74 : CompletelyMixable 4 (unifSet (P 7))) (hc75 : CompletelyMixable 5 (unifSet (P 7)))
    [IsProbabilityMeasure (unifSet (P 8))]
    (hsym8 : (unifSet (P 8)).map (fun x => 0 - x) = unifSet (P 8)) :
    ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, 3 ≤ n → CompletelyMixable n (unifSet (P k)) := by
  intro k hk
  apply all_of_three_four_five
  -- the three generators
  · rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ 8 ≤ k by omega)
      with h | h | h | h | h | h
    · subst h; exact htri 3 (Or.inl rfl)
    · subst h; exact hsq 3 (Or.inl rfl)
    · subst h; exact hc53
    · subst h; exact hhex 3 (Or.inl rfl)
    · subst h
      refine hthm 3 7 le_rfl (by norm_num) _ (Or.inr ⟨rfl, rfl, rfl⟩) ?_
      have := cor96a_seven (Ssum_nonneg 3 7) (Ssum_le 3 7) hcap
      simpa [ha3, hc1, hc2] using this
    · refine hthm 3 k le_rfl hk _ (Or.inl rfl) ?_
      have := cor96a_ge_eight h (Ssum_nonneg 3 k) (Ssum_le 3 k)
      simpa [ha3, hc1, hc2] using this
  · rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k by omega)
      with h | h | h | h | h | h | h
    · subst h; exact htri 4 (Or.inr (Or.inl rfl))
    · subst h; exact hsq 4 (Or.inr (Or.inl rfl))
    · subst h; exact hc54
    · subst h; exact hhex 4 (Or.inr (Or.inl rfl))
    · subst h; exact hc74
    · subst h
      refine hthm 4 8 (by norm_num) (by norm_num) _ (Or.inl rfl) ?_
      have := cor96b_four_eight ha41 ha48
      simpa [hc2, hc3] using this
    · refine hthm 4 k (by norm_num) (by omega) _ (Or.inl rfl) ?_
      have := cor96b_four ha4 ha41 ha49 h
      simpa [hc2, hc3] using this
  · rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k by omega)
      with h | h | h | h | h | h | h
    · subst h; exact htri 5 (Or.inr (Or.inr rfl))
    · subst h; exact hsq 5 (Or.inr (Or.inr rfl))
    · subst h; exact hpent5
    · subst h; exact hhex 5 (Or.inr (Or.inr rfl))
    · subst h; exact hc75
    · subst h
      have h2 : CompletelyMixable 2 (unifSet (P 8)) :=
        (completelyMixable_two_iff (unifSet (P 8))).2 ⟨0, hsym8⟩
      have h3 : CompletelyMixable 3 (unifSet (P 8)) :=
        hthm 3 8 le_rfl (by norm_num) _ (Or.inl rfl) (by
          have := cor96a_ge_eight (le_refl 8) (Ssum_nonneg 3 8) (Ssum_le 3 8)
          simpa [ha3, hc1, hc2] using this)
      exact ScaledB.completelyMixable_add_add h2 h3
    · refine hthm 5 k (by norm_num) (by omega) _ (Or.inl rfl) ?_
      have := cor96b_five ha5 ha51 ha59 hc4 hc4u h
      simpa [hc3] using this

end Bookkeeping2

/-! ## Theorem 95: the marginal of `(1/n) ∑ᵢ ψ(xᵢ) λ` (the operator `G`) -/

section GFormula

open Room

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma exists_perm_pair {i0 i1 i j : Fin n} (h01 : i0 ≠ i1) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin n), σ i0 = i ∧ σ i1 = j := by
  refine ⟨(Equiv.swap i1 (Equiv.swap i0 i j)).trans (Equiv.swap i0 i), ?_, ?_⟩
  · have hne : i0 ≠ Equiv.swap i0 i j := by
      intro h
      have := congrArg (Equiv.swap i0 i) h
      rw [Equiv.swap_apply_left, Equiv.swap_apply_self] at this
      exact hij this
    simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h01 hne, Equiv.swap_apply_left]
  · simp [Equiv.trans_apply]

/-- In a permutation-invariant measure, all pairs of distinct coordinates have the same law. -/
lemma map_pair_eq {lam : Measure (Fin n → E)} (hP : PermInvariant lam) {i0 i1 i j : Fin n}
    (h01 : i0 ≠ i1) (hij : i ≠ j) :
    lam.map (fun x => (x i, x j)) = lam.map (fun x => (x i0, x i1)) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_pair h01 hij
  have hm : Measurable fun x : Fin n → E => (x i0, x i1) :=
    (measurable_pi_apply i0).prodMk (measurable_pi_apply i1)
  conv_rhs => rw [← hP σ]
  rw [Measure.map_map hm (measurable_perm σ)]
  congr 1
  funext x
  simp [hσ0, hσ1]

end GFormula

section GFormula2

open Room

variable {E : Type*} [MeasureSpace E] [SFinite (volume : Measure E)] {n : ℕ}

/-- **The operator `G` (marginal of the correction).** Let `λ` be a permutation-invariant
measure on `n`-tuples (`n ≥ 2`) whose coordinate `i0` has the density `A` (for the Lebesgue
measure on `𝒯_n(B)`: `A = a_n(|·|) 1_B`) and whose pair of coordinates `(i0, i1)` has the
density `g` (there `g(p, q) = 1_B(p) 1_B(q) λ_{n-2}(-p-q)`). Then for `ψ ≥ 0` the measure with
density `(1/n) ∑ᵢ ψ(xᵢ)` with respect to `λ` has the marginal density
`(1/n) (A(p) ψ(p) + (n-1) ∫ g(p, q) ψ(q) dq)`. With `ψ = t + φ` and `∫ g(p, q) dq = A(p)` this is
`t A + Gφ`. -/
theorem marginal_withDensity_sum (hn : 2 ≤ n) {lam : Measure (Fin n → E)}
    (hP : PermInvariant lam) {i0 i1 : Fin n} (h01 : i0 ≠ i1) {A : E → ENNReal}
    (hA : Measurable A) {g : E → E → ENNReal} (hg : Measurable (Function.uncurry g))
    (h1 : lam.map (fun x => x i0) = volume.withDensity A)
    (h2 : lam.map (fun x => (x i0, x i1)) =
      (volume.prod volume).withDensity (Function.uncurry g))
    {ψ : E → ENNReal} (hψ : Measurable ψ) :
    marginal (lam.withDensity fun x => (n : ENNReal)⁻¹ * ∑ i, ψ (x i)) =
      volume.withDensity fun p =>
        (n : ENNReal)⁻¹ * (A p * ψ p + ((n - 1 : ℕ) : ENNReal) * ∫⁻ q, g p q * ψ q) := by
  ext S hS
  set D := ∫⁻ p in S, A p * ψ p with hD
  set O := ∫⁻ p in S, ∫⁻ q, g p q * ψ q with hO
  have hS1 : Measurable (S.indicator (1 : E → ENNReal)) := measurable_one.indicator hS
  -- the diagonal terms
  have hdiag : ∀ j : Fin n, ∫⁻ x, S.indicator 1 (x j) * ψ (x j) ∂lam = D := fun j => by
    have hm : Measurable fun x : Fin n → E => x j := measurable_pi_apply j
    rw [show (∫⁻ x, S.indicator 1 (x j) * ψ (x j) ∂lam) =
        ∫⁻ p, S.indicator 1 p * ψ p ∂(lam.map fun x => x j) from
        (lintegral_map (f := fun p => S.indicator 1 p * ψ p) (hS1.mul hψ) hm).symm,
      map_eval_eq_of_permInvariant hP j i0, h1,
      lintegral_withDensity_eq_lintegral_mul _ hA (g := fun p => S.indicator 1 p * ψ p)
        (hS1.mul hψ), hD,
      ← lintegral_indicator hS]
    congr 1; ext p
    simp only [Pi.mul_apply, indicator]
    split_ifs <;> simp
  -- the off-diagonal terms
  have hoff : ∀ j i : Fin n, j ≠ i → ∫⁻ x, S.indicator 1 (x j) * ψ (x i) ∂lam = O := by
    intro j i hji
    have hm : Measurable fun x : Fin n → E => (x j, x i) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply i)
    have hF : Measurable fun z : E × E => S.indicator 1 z.1 * ψ z.2 :=
      (hS1.comp measurable_fst).mul (hψ.comp measurable_snd)
    rw [show (∫⁻ x, S.indicator 1 (x j) * ψ (x i) ∂lam) =
        ∫⁻ z, S.indicator 1 z.1 * ψ z.2 ∂(lam.map fun x => (x j, x i)) from
        (lintegral_map hF hm).symm, map_pair_eq hP h01 hji, h2,
      lintegral_withDensity_eq_lintegral_mul _ hg hF, lintegral_prod _ (hg.mul hF).aemeasurable,
      hO, ← lintegral_indicator hS]
    congr 1; ext p
    simp only [Pi.mul_apply, Function.uncurry, indicator]
    split_ifs <;> simp
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcoord : ∀ j : Fin n,
      (lam.withDensity fun x => (n : ENNReal)⁻¹ * ∑ i, ψ (x i)) ((fun x => x j) ⁻¹' S) =
        (n : ENNReal)⁻¹ * (D + ((n - 1 : ℕ) : ENNReal) * O) := fun j => by
    have hpre : MeasurableSet ((fun x : Fin n → E => x j) ⁻¹' S) := measurable_pi_apply j hS
    rw [withDensity_apply _ hpre, ← lintegral_indicator hpre]
    have : (((fun x : Fin n → E => x j) ⁻¹' S).indicator
        fun x => (n : ENNReal)⁻¹ * ∑ i, ψ (x i)) =
        fun x => (n : ENNReal)⁻¹ * ∑ i, S.indicator 1 (x j) * ψ (x i) := by
      ext x
      by_cases hx : x j ∈ S <;> simp [indicator, hx]
    have hmeas : ∀ i, Measurable fun x : Fin n → E => S.indicator 1 (x j) * ψ (x i) :=
      fun i => (hS1.comp (measurable_pi_apply j)).mul (hψ.comp (measurable_pi_apply i))
    rw [this]
    beta_reduce
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hn0),
      lintegral_finsetSum _ fun i _ => hmeas i]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hdiag j,
      Finset.sum_congr rfl fun i hi => hoff j i (Finset.ne_of_mem_erase hi).symm]
    simp [Finset.card_erase_of_mem]
  rw [marginal_apply _ hS]
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top _), one_mul,
    withDensity_apply _ hS, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hn0),
    lintegral_add_left (f := fun a => A a * ψ a) (hA.mul hψ),
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]

omit [SFinite (volume : Measure E)] in
lemma marginal_smul' (b : ENNReal) (β : Measure (Fin n → E)) :
    marginal (b • β) = b • marginal β := by
  ext S hS
  simp only [marginal_apply _ hS, smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

omit [SFinite (volume : Measure E)] in
/-- Symmetrisation does not change the marginal. -/
lemma marginal_symmetrise (P : Measure (Fin n → E)) : marginal (symmetrise P) = marginal P := by
  ext S hS
  rw [marginal_apply _ hS, marginal_apply _ hS]
  congr 1
  simp only [fun j => symmetrise_apply P (measurable_pi_apply j hS)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have : ∀ σ : Equiv.Perm (Fin n), ∑ j, P ((fun x => x ∘ σ) ⁻¹' ((fun x => x j) ⁻¹' S)) =
      ∑ j, P ((fun x => x j) ⁻¹' S) := fun σ =>
    Equiv.sum_comp σ (fun j => P ((fun x => x j) ⁻¹' S))
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel card_perm_ne_zero (ENNReal.natCast_ne_top _), one_mul]

/-- **The marginal of the corner partners.** Let `λ_C` be a measure on `n`-tuples whose
coordinate `i0` (the corner point `p`) has the density `A_C` (for the Lebesgue measure on the
tuples with `p ∈ C` and the others in `B`: `A_C = 1_C a_n(|·|)`), and every pair `(x_{i0}, x_j)`,
`j ≠ i0`, the density `g_C` (there `g_C(p, q) = 1_C(p) g(p, q)`). Weighting by `w(p)` (there
`w = 1/(|P_k| a_n(|p|))`, so that `p` has the density `|P_k|⁻¹ 1_C` and the other coordinates are
uniform on `L_p`) gives `γ`, and `β_C = n Sym γ` has the marginal density
`A_C w + (n-1) ∫ g_C(p, ·) w(p) dp`, that is `|P_k|⁻¹ 1_C + ν`. -/
theorem corner_marginal {lamC : Measure (Fin n → E)} {i0 : Fin n} {AC : E → ENNReal}
    (hA : Measurable AC) {gC : E → E → ENNReal} (hg : Measurable (Function.uncurry gC))
    (h1 : lamC.map (fun x => x i0) = volume.withDensity AC)
    (h2 : ∀ j, j ≠ i0 → lamC.map (fun x => (x i0, x j)) =
      (volume.prod volume).withDensity (Function.uncurry gC))
    {w : E → ENNReal} (hw : Measurable w) :
    marginal ((n : ENNReal) • symmetrise (lamC.withDensity fun x => w (x i0))) =
      volume.withDensity fun q => AC q * w q + ((n - 1 : ℕ) : ENNReal) * ∫⁻ p, gC p q * w p := by
  have hn : 0 < n := Fin.pos i0
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  rw [marginal_smul', marginal_symmetrise]
  ext S hS
  rw [smul_apply, marginal_apply _ hS, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top _), one_mul]
  have hS1 : Measurable (S.indicator (1 : E → ENNReal)) := measurable_one.indicator hS
  set D := ∫⁻ q in S, AC q * w q
  set O := ∫⁻ q in S, ∫⁻ p, gC p q * w p
  have hcoord : ∀ j, (lamC.withDensity fun x => w (x i0)) ((fun x => x j) ⁻¹' S) =
      if j = i0 then D else O := by
    intro j
    have hpre : MeasurableSet ((fun x : Fin n → E => x j) ⁻¹' S) := measurable_pi_apply j hS
    rw [withDensity_apply _ hpre, ← lintegral_indicator hpre]
    have hind : (((fun x : Fin n → E => x j) ⁻¹' S).indicator fun x => w (x i0)) =
        fun x => S.indicator 1 (x j) * w (x i0) := by
      ext x; by_cases hx : x j ∈ S <;> simp [indicator, hx]
    rw [hind]
    split_ifs with hj
    · subst hj
      rw [show (∫⁻ x, S.indicator 1 (x j) * w (x j) ∂lamC) =
          ∫⁻ p, S.indicator 1 p * w p ∂(lamC.map fun x => x j) from
          (lintegral_map (f := fun p => S.indicator 1 p * w p) (hS1.mul hw)
            (measurable_pi_apply j)).symm, h1,
        lintegral_withDensity_eq_lintegral_mul _ hA (g := fun p => S.indicator 1 p * w p)
          (hS1.mul hw)]
      show _ = ∫⁻ q in S, AC q * w q
      rw [← lintegral_indicator hS]
      congr 1; ext p
      simp only [Pi.mul_apply, indicator]
      split_ifs <;> simp
    · have hm : Measurable fun x : Fin n → E => (x i0, x j) :=
        (measurable_pi_apply i0).prodMk (measurable_pi_apply j)
      have hF : Measurable fun z : E × E => S.indicator 1 z.2 * w z.1 :=
        (hS1.comp measurable_snd).mul (hw.comp measurable_fst)
      rw [show (∫⁻ x, S.indicator 1 (x j) * w (x i0) ∂lamC) =
          ∫⁻ z, S.indicator 1 z.2 * w z.1 ∂(lamC.map fun x => (x i0, x j)) from
          (lintegral_map hF hm).symm, h2 j hj,
        lintegral_withDensity_eq_lintegral_mul _ hg hF,
        lintegral_prod _ (hg.mul hF).aemeasurable,
        lintegral_lintegral_swap ((hg.mul hF).aemeasurable)]
      show _ = ∫⁻ q in S, ∫⁻ p, gC p q * w p
      rw [← lintegral_indicator hS]
      congr 1; ext q
      simp only [Pi.mul_apply, Function.uncurry, indicator]
      split_ifs
      · congr 1; ext p; simp
      · simp
  simp only [hcoord]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), ite_eq_left rfl,
    Finset.sum_congr rfl fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj)]
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [withDensity_apply _ hS, lintegral_add_left (f := fun q => AC q * w q) (hA.mul hw),
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]

end GFormula2

end Poly

end Mixes
