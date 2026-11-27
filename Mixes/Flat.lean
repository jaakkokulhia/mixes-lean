import Mixes.ScaledC
import Mixes.Bridges

/-!
# Corollary 84 (f): regular `2m`-gons sliced perpendicular to two opposite sides

Corollary 84 (f) (`g:cor:flat`, Table `g:tab:polygons`) of the mixes paper: for `k = 2` and `K` a
regular `2m`-gon with inradius `1` and `2m ≤ 18`, sliced perpendicular to two opposite sides,
conditions (P_h) and (F_h) of Theorem 83 hold at the tabulated `h`, so `U(K)` is `n`-completely
mixable for every `n ≥ 2`.

* `prof m`: the half-width `r(z) = min_{1 ≤ j ≤ m/2} (1 - |z| cos(jπ/m)) / sin(jπ/m)` of the
  regular `2m`-gon with inradius `1` and two sides on `z = ±1`; `bodyK (prof m) [-1, 1]` is that
  polygon (`bodyK_prof`).
* `flat_mixable`: Theorem 83 with `k = 2`, `F = [-1, 1]` for this profile.
* Exact verification of (P_h) and (F_h) at the tabulated `h` for `2m = 6, …, 18`, from
  alternating-series bounds of `cos`, `sin`, the series of `log` and `π` to six decimals.
-/

open Set MeasureTheory intervalIntegral Real
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes

namespace Flat

/-! ## The profile of the regular `2m`-gon -/

/-- Indices `1 ≤ j ≤ max 1 (m/2)` of the sides that meet the upper half of the slice. -/
def idx (m : ℕ) : Finset ℕ := Finset.Icc 1 (max 1 (m / 2))

lemma idx_nonempty (m : ℕ) : (idx m).Nonempty := ⟨1, by simp [idx]⟩

/-- The half-width of the strip of side `j`: `(1 - |z| cos(jπ/m)) / sin(jπ/m)`. -/
def term (m j : ℕ) (z : ℝ) : ℝ := (1 - |z| * cos (j * π / m)) / sin (j * π / m)

/-- The half-width of the regular `2m`-gon with inradius `1` and two sides on `z = ±1`. -/
def prof (m : ℕ) (z : ℝ) : ℝ := (idx m).inf' (idx_nonempty m) fun j => term m j z

lemma angle_mem {m j : ℕ} (hm : 2 ≤ m) (hj : j ∈ idx m) :
    0 < (j:ℝ) * π / m ∧ (j:ℝ) * π / m ≤ π / 2 := by
  simp only [idx, Finset.mem_Icc] at hj
  have h1 : max 1 (m / 2) = m / 2 := max_eq_right (by omega)
  rw [h1] at hj
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj.1
  have hj2 : (2 * j : ℝ) ≤ m := by exact_mod_cast (by omega : 2 * j ≤ m)
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hm0 two_pos]
  nlinarith [pi_pos]

lemma sin_pos_of_idx {m j : ℕ} (hm : 2 ≤ m) (hj : j ∈ idx m) : 0 < sin (j * π / m) := by
  obtain ⟨h1, h2⟩ := angle_mem hm hj
  exact sin_pos_of_pos_of_lt_pi h1 (by linarith [pi_pos])

lemma cos_nonneg_of_idx {m j : ℕ} (hm : 2 ≤ m) (hj : j ∈ idx m) : 0 ≤ cos (j * π / m) := by
  obtain ⟨h1, h2⟩ := angle_mem hm hj
  exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h2⟩

lemma cos_le_one' (m j : ℕ) : cos (j * π / m) ≤ 1 := cos_le_one _

lemma prof_neg (m : ℕ) (z : ℝ) : prof m (-z) = prof m z := by
  simp [prof, term, abs_neg]

lemma continuous_term {m j : ℕ} : Continuous (term m j) := by
  unfold term; fun_prop

lemma continuous_prof (m : ℕ) : Continuous (prof m) := by
  have := Continuous.finset_inf'_apply (idx_nonempty m) (f := fun j z => term m j z)
    (fun _ _ => continuous_term)
  exact this

lemma term_nonneg {m j : ℕ} (hm : 2 ≤ m) (hj : j ∈ idx m) {z : ℝ} (hz : |z| ≤ 1) :
    0 ≤ term m j z := by
  have hs := sin_pos_of_idx hm hj
  have hc := cos_nonneg_of_idx hm hj
  have hc1 := cos_le_one' m j
  unfold term
  apply div_nonneg _ hs.le
  nlinarith [abs_nonneg z]

lemma term_pos {m j : ℕ} (hm : 2 ≤ m) (hj : j ∈ idx m) {z : ℝ} (hz : |z| < 1) :
    0 < term m j z := by
  have hs := sin_pos_of_idx hm hj
  have hc := cos_nonneg_of_idx hm hj
  have hc1 := cos_le_one' m j
  unfold term
  apply div_pos _ hs
  nlinarith [abs_nonneg z]

lemma le_prof_iff {m : ℕ} {z L : ℝ} : L ≤ prof m z ↔ ∀ j ∈ idx m, L ≤ term m j z :=
  Finset.le_inf'_iff _ _

lemma prof_le_term {m j : ℕ} (hj : j ∈ idx m) (z : ℝ) : prof m z ≤ term m j z :=
  Finset.inf'_le _ hj

lemma prof_nonneg {m : ℕ} (hm : 2 ≤ m) {z : ℝ} (hz : z ∈ Icc (-1:ℝ) 1) : 0 ≤ prof m z :=
  le_prof_iff.2 fun _ hj => term_nonneg hm hj (abs_le.2 hz)

lemma prof_pos {m : ℕ} (hm : 2 ≤ m) {z : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) : 0 < prof m z := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (idx_nonempty m) fun j => term m j z
  rw [prof, hjeq]
  exact term_pos hm hj (abs_lt.2 hz)

lemma concaveOn_term {m j : ℕ} (hm : 2 ≤ m) (hj : j ∈ idx m) : ConcaveOn ℝ univ (term m j) := by
  have hs := sin_pos_of_idx hm hj
  have hc := cos_nonneg_of_idx hm hj
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [term, smul_eq_mul]
  have habs : |a * x + b * y| ≤ a * |x| + b * |y| := by
    calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = a * |x| + b * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  apply div_le_div_of_nonneg_right _ hs.le
  have : a * (1 - |x| * cos (j * π / m)) + b * (1 - |y| * cos (j * π / m)) =
      1 - (a * |x| + b * |y|) * cos (j * π / m) := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [this]
  nlinarith

lemma concaveOn_prof {m : ℕ} (hm : 2 ≤ m) : ConcaveOn ℝ univ (prof m) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_prof_iff.2 fun j hj => ?_
  have := (concaveOn_term hm hj).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at this
  refine le_trans ?_ this
  gcongr
  · exact prof_le_term hj x
  · exact prof_le_term hj y

/-! ## The profile describes the regular `2m`-gon -/

/-- The regular `2m`-gon with inradius `1`, centre `0` and two sides on `z = ±1`, as the
intersection of the `2m` half-planes `z cos(kπ/m) + y sin(kπ/m) ≤ 1`, `0 ≤ k < 2m`; points are
`(z, y)`, the level `z` first. -/
def regPoly (m : ℕ) : Set (ℝ × ℝ) :=
  {p | ∀ k : ℕ, k < 2 * m → p.1 * cos (k * π / m) + p.2 * sin (k * π / m) ≤ 1}

lemma mem_smul_Icc {r y : ℝ} (hr : 0 ≤ r) : y ∈ r • Icc (-1:ℝ) 1 ↔ |y| ≤ r := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [smul_eq_mul, abs_mul, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr (abs_le.2 hx)
  · intro hy
    rcases eq_or_lt_of_le hr with h0 | hpos
    · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [← h0] at hy ⊢
      simp only [smul_eq_mul, mul_zero]
      exact (abs_nonpos_iff.1 hy).symm
    · refine ⟨y / r, ⟨?_, ?_⟩, by rw [smul_eq_mul]; field_simp⟩
      · rw [le_div_iff₀ hpos]; linarith [neg_abs_le y]
      · rw [div_le_iff₀ hpos]; linarith [le_abs_self y]

/-- The reflections of the angle `jπ/m`. -/
lemma cs_refl {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    (cos (((m - j : ℕ) : ℝ) * π / m) = -cos (j * π / m) ∧
      sin (((m - j : ℕ) : ℝ) * π / m) = sin (j * π / m)) ∧
    (cos (((m + j : ℕ) : ℝ) * π / m) = -cos (j * π / m) ∧
      sin (((m + j : ℕ) : ℝ) * π / m) = -sin (j * π / m)) ∧
    (cos (((2 * m - j : ℕ) : ℝ) * π / m) = cos (j * π / m) ∧
      sin (((2 * m - j : ℕ) : ℝ) * π / m) = -sin (j * π / m)) := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e1 : ((m - j : ℕ) : ℝ) * π / m = π - j * π / m := by
    rw [Nat.cast_sub hj]; field_simp
  have e2 : ((m + j : ℕ) : ℝ) * π / m = j * π / m + π := by
    push_cast; field_simp; ring
  have e3 : ((2 * m - j : ℕ) : ℝ) * π / m = -(j * π / m) + 2 * π := by
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring
  rw [e1, e2, e3, cos_pi_sub, sin_pi_sub, cos_add_pi, sin_add_pi, cos_add_two_pi,
    sin_add_two_pi, cos_neg, sin_neg]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

lemma abs_le_prof_iff {m : ℕ} (hm : 2 ≤ m) {z y : ℝ} :
    |y| ≤ prof m z ↔ ∀ j ∈ idx m, |z| * cos (j * π / m) + |y| * sin (j * π / m) ≤ 1 := by
  rw [le_prof_iff]
  refine forall₂_congr fun j hj => ?_
  have hs := sin_pos_of_idx hm hj
  rw [term, le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- `bodyK (prof m) [-1, 1] = {(z, y) : |z| ≤ 1, |y| ≤ prof m z}` is the regular `2m`-gon
`regPoly m` with inradius `1` and two sides on `z = ±1`. -/
theorem bodyK_prof {m : ℕ} (hm : 2 ≤ m) :
    ScaledC.bodyK (prof m) (Icc (-1:ℝ) 1) = regPoly m := by
  have hm0 : 0 < m := by omega
  ext ⟨z, y⟩
  simp only [ScaledC.bodyK, regPoly, mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hy⟩
    rw [mem_smul_Icc (prof_nonneg hm (abs_le.1 hz)), abs_le_prof_iff hm] at hy
    intro k hk
    -- fold `k` to an index `j ≤ m/2`
    have key : ∀ j : ℕ, j ≤ m / 2 → ∀ c s : ℝ, (c = cos (j * π / m) ∨ c = -cos (j * π / m)) →
        (s = sin (j * π / m) ∨ s = -sin (j * π / m)) → z * c + y * s ≤ 1 := by
      intro j hj c s hc hs
      have hzc : z * c ≤ |z| * |c| := by rw [← abs_mul]; exact le_abs_self _
      have hys : y * s ≤ |y| * |s| := by rw [← abs_mul]; exact le_abs_self _
      have hcj : |c| = |cos (j * π / m)| := by rcases hc with rfl | rfl <;> simp
      have hsj : |s| = |sin (j * π / m)| := by rcases hs with rfl | rfl <;> simp
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simp only [CharP.cast_eq_zero, zero_mul, zero_div, cos_zero, sin_zero, abs_one,
          abs_zero] at hcj hsj
        rw [hcj] at hzc; rw [hsj] at hys
        linarith
      · have hji : j ∈ idx m := by
          simp only [idx, Finset.mem_Icc]; exact ⟨hj1, by omega⟩
        rw [abs_of_nonneg (cos_nonneg_of_idx hm hji)] at hcj
        rw [abs_of_nonneg (sin_pos_of_idx hm hji).le] at hsj
        rw [hcj] at hzc; rw [hsj] at hys
        linarith [hy j hji]
    rcases (show k ≤ m / 2 ∨ (m / 2 < k ∧ k ≤ m) ∨ (m < k ∧ k ≤ m + m / 2) ∨
        (m + m / 2 < k) by omega) with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · exact key k h1 _ _ (Or.inl rfl) (Or.inl rfl)
    · obtain ⟨⟨hc, hs⟩, -⟩ := cs_refl (j := m - k) hm0 (by omega)
      rw [show m - (m - k) = k by omega] at hc hs
      exact key (m - k) (by omega) _ _ (Or.inr hc) (Or.inl hs)
    · obtain ⟨-, ⟨hc, hs⟩, -⟩ := cs_refl (j := k - m) hm0 (by omega)
      rw [show m + (k - m) = k by omega] at hc hs
      exact key (k - m) (by omega) _ _ (Or.inr hc) (Or.inr hs)
    · obtain ⟨-, -, ⟨hc, hs⟩⟩ := cs_refl (j := 2 * m - k) hm0 (by omega)
      rw [show 2 * m - (2 * m - k) = k by omega] at hc hs
      exact key (2 * m - k) (by omega) _ _ (Or.inl hc) (Or.inr hs)
  · intro H
    have hz1 : z ≤ 1 := by have := H 0 (by omega); simpa using this
    have hz2 : -z ≤ 1 := by
      have := H m (by omega)
      have e : (m:ℝ) * π / m = π := by field_simp
      rw [e, cos_pi, sin_pi] at this; linarith
    have hz : |z| ≤ 1 := abs_le.2 ⟨by linarith, hz1⟩
    refine ⟨hz, ?_⟩
    rw [mem_smul_Icc (prof_nonneg hm (abs_le.1 hz)), abs_le_prof_iff hm]
    intro j hj
    have hjm : j ≤ m := by simp only [idx, Finset.mem_Icc] at hj; omega
    have hj1 : 1 ≤ j := by simp only [idx, Finset.mem_Icc] at hj; omega
    have hjm2 : j < m := by
      simp only [idx, Finset.mem_Icc] at hj
      have : max 1 (m / 2) = m / 2 := max_eq_right (by omega)
      omega
    obtain ⟨⟨c1, s1⟩, ⟨c2, s2⟩, ⟨c3, s3⟩⟩ := cs_refl hm0 hjm
    rcases le_total 0 z with hz0 | hz0 <;> rcases le_total 0 y with hy0 | hy0
    · have := H j (by omega)
      rw [abs_of_nonneg hz0, abs_of_nonneg hy0]; exact this
    · have := H (2 * m - j) (by omega)
      rw [c3, s3] at this
      rw [abs_of_nonneg hz0, abs_of_nonpos hy0]; linarith
    · have := H (m - j) (by omega)
      rw [c1, s1] at this
      rw [abs_of_nonpos hz0, abs_of_nonneg hy0]; linarith
    · have := H (m + j) (by omega)
      rw [c2, s2] at this
      rw [abs_of_nonpos hz0, abs_of_nonpos hy0]; linarith

/-! ## Theorem 83 for the regular `2m`-gon -/

/-- **Theorem 83** (`g:thm:bipyr`) with `k = 2` and `F = [-1, 1]` for the profile `prof m` of the
regular `2m`-gon: if (P_h) and (F_h) hold for some `h ∈ [1/2, 1)`, the uniform distribution on
`K = {(z, y) : |z| ≤ 1, |y| ≤ prof m z}` is `n`-completely mixable for every `n ≥ 2`. -/
theorem flat_mixable {m : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 1 / 2 ≤ h) (hh1 : h < 1)
    (hP : Scaled.CondP (prof m) h 2) (hF : Scaled.CondF (prof m) h) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (ScaledC.bodyK (prof m) (Icc (-1:ℝ) 1))) := by
  have hk : Module.finrank ℝ ℝ + 1 = 2 := by simp
  refine ScaledC.thm83 (V := ℝ) isCompact_Icc ?_ ScaledB.integral_unifSet_Icc (by simp)
    (continuous_prof m).continuousOn (fun z _ => prof_neg m z)
    ((concaveOn_prof hm).subset (subset_univ _) (convex_Icc _ _))
    (fun z hz => prof_nonneg hm hz) (fun z hz => prof_pos hm hz)
    Bridges.scalingProperty_segment hh hh1 (hk ▸ hP) hF hn
  rw [interior_Icc]; exact ⟨0, by norm_num⟩

/-! ## Interval bounds for `cos` and `sin` -/

/-- Partial sum of the cosine series. -/
def cosS (N : ℕ) (y : ℝ) : ℝ := ∑ i ∈ Finset.range N, (-1) ^ i * (y ^ (2 * i) / (2 * i).factorial)

/-- Partial sum of the sine series. -/
def sinS (N : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, (-1) ^ i * (y ^ (2 * i + 1) / (2 * i + 1).factorial)

lemma cos_terms_anti {y : ℝ} (h2 : y ^ 2 ≤ 2) :
    Antitone fun i : ℕ => y ^ (2 * i) / ((2 * i).factorial : ℝ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hf : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf, show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
  have hF : (0:ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
  have hy : 0 ≤ y ^ (2 * n) := by rw [pow_mul]; positivity
  have hn : (0:ℝ) ≤ n := n.cast_nonneg
  rw [div_le_div_iff₀ (by positivity) hF]
  have : y ^ 2 * (2 * n).factorial ≤ (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    apply mul_le_mul_of_nonneg_right _ hF.le; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hy]

lemma sin_terms_anti {y : ℝ} (h0 : 0 ≤ y) (h2 : y ^ 2 ≤ 6) :
    Antitone fun i : ℕ => y ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hf : ((2 * (n + 1) + 1).factorial : ℝ) =
      (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, pow_add]
  have hF : (0:ℝ) < (2 * n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hy : 0 ≤ y ^ (2 * n + 1) := by positivity
  have hn : (0:ℝ) ≤ n := n.cast_nonneg
  rw [div_le_div_iff₀ (by positivity) hF]
  have : y ^ 2 * (2 * n + 1).factorial ≤ (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
    apply mul_le_mul_of_nonneg_right _ hF.le; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hy]

lemma cos_tendsto (y : ℝ) : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n,
    (-1) ^ i * (y ^ (2 * i) / ((2 * i).factorial : ℝ))) Filter.atTop (nhds (cos y)) := by
  have := (Real.hasSum_cos y).tendsto_sum_nat
  simpa only [mul_div_assoc] using this

lemma sin_tendsto (y : ℝ) : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n,
    (-1) ^ i * (y ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) Filter.atTop (nhds (sin y)) := by
  have := (Real.hasSum_sin y).tendsto_sum_nat
  simpa only [mul_div_assoc] using this

lemma cosS_le {y : ℝ} (h2 : y ^ 2 ≤ 2) (k : ℕ) : cosS (2 * k) y ≤ cos y :=
  (cos_terms_anti h2).alternating_series_le_tendsto (cos_tendsto y) k

lemma le_cosS {y : ℝ} (h2 : y ^ 2 ≤ 2) (k : ℕ) : cos y ≤ cosS (2 * k + 1) y :=
  (cos_terms_anti h2).tendsto_le_alternating_series (cos_tendsto y) k

lemma sinS_le {y : ℝ} (h0 : 0 ≤ y) (h2 : y ^ 2 ≤ 6) (k : ℕ) : sinS (2 * k) y ≤ sin y :=
  (sin_terms_anti h0 h2).alternating_series_le_tendsto (sin_tendsto y) k

lemma le_sinS {y : ℝ} (h0 : 0 ≤ y) (h2 : y ^ 2 ≤ 6) (k : ℕ) : sin y ≤ sinS (2 * k + 1) y :=
  (sin_terms_anti h0 h2).tendsto_le_alternating_series (sin_tendsto y) k

/-- Interval bounds for `cos (jπ/m)` and `sin (jπ/m)`. -/
structure TB (m j : ℕ) (cl cu sl su : ℝ) : Prop where
  cl : cl ≤ cos (j * π / m)
  cu : cos (j * π / m) ≤ cu
  sl : sl ≤ sin (j * π / m)
  su : sin (j * π / m) ≤ su

/-- Bounds from the series, for `0 ≤ ylo ≤ jπ/m ≤ yhi`, `yhi² ≤ 2`. -/
lemma tb_of (m j : ℕ) {ylo yhi : ℝ} (h0 : 0 ≤ ylo) (hlo : ylo ≤ j * π / m)
    (hhi : j * π / m ≤ yhi) (h2 : yhi ^ 2 ≤ 2) :
    TB m j (cosS 8 yhi) (cosS 7 ylo) (sinS 8 ylo) (sinS 7 yhi) := by
  have hpi : yhi < π := by nlinarith [pi_gt_three]
  have hlo2 : ylo ^ 2 ≤ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (cosS_le h2 4).trans (cos_le_cos_of_nonneg_of_le_pi (h0.trans hlo) hpi.le hhi)
  · exact (cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) hlo).trans (le_cosS hlo2 3)
  · refine (sinS_le h0 (by linarith) 4).trans (sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [pi_pos]) ?_ hlo)
    nlinarith [pi_gt_three]
  · refine (sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) ?_ hhi).trans
      (le_sinS (by linarith) (by linarith) 3)
    nlinarith [pi_gt_three]

/-- Exact values for the side `j = m/2` (`cos (π/2) = 0`, `sin (π/2) = 1`). -/
lemma tb_half (m j : ℕ) (hm : 0 < m) (hj : 2 * j = m) : TB m j 0 0 1 1 := by
  have : (j:ℝ) * π / m = π / 2 := by
    have hm' : (m:ℝ) = 2 * j := by exact_mod_cast hj.symm
    have hj0 : (j:ℝ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    rw [hm']; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [this]

lemma TB.term_ge {m j : ℕ} {cl cu sl su : ℝ} (H : TB m j cl cu sl su) {z : ℝ} (hz : 0 ≤ z)
    (hsl : 0 < sl) (hn : 0 ≤ 1 - z * cu) : (1 - z * cu) / su ≤ term m j z := by
  have hs : 0 < sin (j * π / m) := hsl.trans_le H.sl
  unfold term
  rw [abs_of_nonneg hz]
  calc (1 - z * cu) / su ≤ (1 - z * cu) / sin (j * π / m) :=
        div_le_div_of_nonneg_left hn hs H.su
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [H.cu]) hs.le

lemma TB.term_le {m j : ℕ} {cl cu sl su : ℝ} (H : TB m j cl cu sl su) {z : ℝ} (hz : 0 ≤ z)
    (hsl : 0 < sl) (hn : 0 ≤ 1 - z * cl) : term m j z ≤ (1 - z * cl) / sl := by
  have hs : 0 < sin (j * π / m) := hsl.trans_le H.sl
  unfold term
  rw [abs_of_nonneg hz]
  calc (1 - z * cos (j * π / m)) / sin (j * π / m) ≤ (1 - z * cl) / sin (j * π / m) :=
        div_le_div_of_nonneg_right (by nlinarith [H.cl]) hs.le
    _ ≤ _ := div_le_div_of_nonneg_left hn hsl H.sl

/-- An affine upper bound of the profile from one side. -/
lemma prof_le_aff {m j : ℕ} {cl cu sl su : ℝ} (H : TB m j cl cu sl su) (hj : j ∈ idx m)
    (hsl : 0 < sl) (hcl : 0 ≤ cl) (hcl1 : cl ≤ 1) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    prof m z ≤ 1 / sl + (-cl / sl) * z := by
  refine (prof_le_term hj z).trans ((H.term_le hz hsl (by nlinarith)).trans_eq ?_)
  ring

/-! ## (F_h) on a subinterval -/

/-- (F_h) on `[a, b]`: if `r ≤ α + β c` on `[a, b]`, `r` is concave on `[0, 1]`, and
`α + β c ≤ r(h) + r(h + c)` at `c = a` and `c = b`, then `r(c) ≤ r(h) + r(h + c)` on `[a, b]`. -/
lemma F_piece {r : ℝ → ℝ} (hconc : ConcaveOn ℝ (Icc 0 1) r) {h a b α β : ℝ} (hh : 0 ≤ h)
    (ha : 0 ≤ a) (hab : a < b) (hb : h + b ≤ 1) (hu : ∀ c ∈ Icc a b, r c ≤ α + β * c)
    (hA : α + β * a ≤ r h + r (h + a)) (hB : α + β * b ≤ r h + r (h + b)) :
    ∀ c ∈ Icc a b, r c ≤ r h + r (h + c) := by
  intro c hc
  set t := (c - a) / (b - a)
  have hba : 0 < b - a := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hc.1]) hba.le
  have ht1 : t ≤ 1 := by rw [div_le_one hba]; linarith [hc.2]
  have hct : c = (1 - t) * a + t * b := by
    simp only [t]; field_simp; ring
  have hcv := hconc.2 (show h + a ∈ Icc (0:ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show h + b ∈ Icc (0:ℝ) 1 from ⟨by linarith, hb⟩) (show (0:ℝ) ≤ 1 - t by linarith) ht0
    (by ring)
  simp only [smul_eq_mul] at hcv
  have he : (1 - t) * (h + a) + t * (h + b) = h + c := by rw [hct]; ring
  rw [he] at hcv
  have := hu c hc
  have hlin : α + β * c = (1 - t) * (α + β * a) + t * (α + β * b) := by rw [hct]; ring
  nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ 1 - t),
    mul_le_mul_of_nonneg_left hB ht0]

/-! ## (P_h) on a linear piece -/

lemma integrable_div {f : ℝ → ℝ} (hf : Continuous f) {h p q : ℝ} (hpq : p ≤ q) (hq : q < 2 * h) :
    IntervalIntegrable (fun a => f a / (2 * h - a)) volume p q := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hpq]
  exact hf.continuousOn.div (by fun_prop) fun a ha => by linarith [ha.2]

lemma integral_term {m j : ℕ} {h p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 2 * h) :
    ∫ a in p..q, term m j a / (2 * h - a) =
      (cos (j * π / m) * (q - p) + (1 - 2 * h * cos (j * π / m)) *
        log ((2 * h - p) / (2 * h - q))) / sin (j * π / m) := by
  set c := cos (j * π / m)
  set s := sin (j * π / m)
  have e : ∀ a ∈ uIcc p q, term m j a / (2 * h - a) =
      (c + (1 - 2 * h * c) * (2 * h - a)⁻¹) / s := by
    intro a ha
    rw [uIcc_of_le hpq] at ha
    have ha0 : 0 ≤ a := hp.trans ha.1
    have hd : 2 * h - a ≠ 0 := by linarith [ha.2]
    simp only [term, abs_of_nonneg ha0]
    field_simp
    ring
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_div,
    intervalIntegral.integral_add intervalIntegrable_const, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) (2 * h),
    integral_inv_of_pos (by linarith) (by linarith)]
  · simp only [smul_eq_mul]; ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    refine continuousOn_const.mul (ContinuousOn.inv₀ (f := fun x => 2 * h - x) (by fun_prop) ?_)
    intro a ha
    have := ha.2
    exact ne_of_gt (by linarith)

/-- Bounds for `log ((2h - p)/(2h - q))` from the series of `log (1 - x)`,
`x = (q - p)/(2h - p)`. -/
lemma log_bounds {h p q : ℝ} (n : ℕ) (hpq : p ≤ q) (hq : q < 2 * h) :
    (∑ i ∈ Finset.range n, ((q - p) / (2 * h - p)) ^ (i + 1) / (i + 1)) -
      ((q - p) / (2 * h - p)) ^ (n + 1) / (1 - (q - p) / (2 * h - p)) ≤
        log ((2 * h - p) / (2 * h - q)) ∧
    log ((2 * h - p) / (2 * h - q)) ≤
      (∑ i ∈ Finset.range n, ((q - p) / (2 * h - p)) ^ (i + 1) / (i + 1)) +
        ((q - p) / (2 * h - p)) ^ (n + 1) / (1 - (q - p) / (2 * h - p)) := by
  set x := (q - p) / (2 * h - p)
  have hd : 0 < 2 * h - p := by linarith
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hd.le
  have hx1 : x < 1 := by rw [div_lt_one hd]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have H := Real.abs_log_sub_add_sum_range_le habs n
  rw [abs_of_nonneg hx0] at H
  have h1x : 1 - x = (2 * h - q) / (2 * h - p) := by simp only [x]; field_simp; ring
  have hl : log (1 - x) = -log ((2 * h - p) / (2 * h - q)) := by
    rw [h1x, ← log_inv, inv_div]
  rw [hl] at H
  constructor <;> linarith [(abs_le.1 H).1, (abs_le.1 H).2]

lemma aff_le {x lo hi K M N : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) (hlo : K + M * lo ≤ N)
    (hhi : K + M * hi ≤ N) : K + M * x ≤ N := by
  rcases le_total 0 M with hM | hM <;> nlinarith

/-- (P_h) on one linear piece `[p, q]`, where the side `j` bounds the profile. -/
lemma P_piece {m j : ℕ} (hj : j ∈ idx m) {cl cu sl su : ℝ}
    (H : TB m j cl cu sl su) (hsl : 0 < sl) {h p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : q < 2 * h) {Ll Lu Nb : ℝ}
    (hLl : Ll ≤ log ((2 * h - p) / (2 * h - q))) (hLu : log ((2 * h - p) / (2 * h - q)) ≤ Lu)
    (hNb : 0 ≤ Nb) (h1 : cl * (q - p) + (1 - 2 * h * cl) * Ll ≤ Nb)
    (h2 : cl * (q - p) + (1 - 2 * h * cl) * Lu ≤ Nb)
    (h3 : cu * (q - p) + (1 - 2 * h * cu) * Ll ≤ Nb)
    (h4 : cu * (q - p) + (1 - 2 * h * cu) * Lu ≤ Nb) :
    ∫ a in p..q, prof m a / (2 * h - a) ≤ Nb / sl := by
  have hs : 0 < sin (j * π / m) := hsl.trans_le H.sl
  have hmono : ∫ a in p..q, prof m a / (2 * h - a) ≤ ∫ a in p..q, term m j a / (2 * h - a) :=
    intervalIntegral.integral_mono_on hpq (integrable_div (continuous_prof m) hpq hq)
      (integrable_div continuous_term hpq hq) fun a ha =>
        div_le_div_of_nonneg_right (prof_le_term hj a) (by linarith [ha.2])
  refine hmono.trans ?_
  rw [integral_term hp hpq hq]
  set c := cos (j * π / m)
  set L := log ((2 * h - p) / (2 * h - q))
  have hN : c * (q - p) + (1 - 2 * h * c) * L ≤ Nb := by
    have hc1 := H.cl; have hc2 := H.cu
    have eL : ∀ L', ∀ c', c' * (q - p) + (1 - 2 * h * c') * L' = L' + (q - p - 2 * h * L') * c' :=
      fun _ _ => by ring
    have eC : ∀ c', c * (q - p) + (1 - 2 * h * c) * c' = c * (q - p) + (1 - 2 * h * c) * c' :=
      fun _ => rfl
    have hLl' : c * (q - p) + (1 - 2 * h * c) * Ll ≤ Nb := by
      rw [eL]; rw [eL] at h1 h3; exact aff_le hc1 hc2 h1 h3
    have hLu' : c * (q - p) + (1 - 2 * h * c) * Lu ≤ Nb := by
      rw [eL]; rw [eL] at h2 h4; exact aff_le hc1 hc2 h2 h4
    exact aff_le hLl hLu hLl' hLu'
  calc _ ≤ Nb / sin (j * π / m) := div_le_div_of_nonneg_right hN hs.le
    _ ≤ Nb / sl := div_le_div_of_nonneg_left hNb hsl H.sl

/-! ## The polygons of Table `g:tab:polygons` -/

/-! ### The regular 6-gon, `h = 0.7725` -/

lemma tb_3_1 : TB 3 1 0.499999899 0.500000189 0.866025294 0.866025462 := by
  have H := tb_of 3 1 (ylo := 1 * 3.141592 / 3) (yhi := 1 * 3.141593 / 3) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma le_prof_3 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.500000189) / 0.866025462)
    :
    L ≤ prof 3 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_3_1.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 6-gon at `h = 0.7725`. -/
theorem condF_3 : Scaled.CondF (prof 3) 0.7725 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 3) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.708697239:ℝ) ≤ prof 3 (0.7725) := le_prof_3 (by norm_num) (by norm_num)
      (by norm_num)
  have hL0 : (0.708697239:ℝ) ≤ prof 3 (0.7725 + (0)) := le_prof_3 (by norm_num) (by norm_num)
      (by norm_num)
  have hL1 : (0.577350012:ℝ) ≤ prof 3 (0.7725 + (1 - 0.7725)) := le_prof_3 (by norm_num)
      (by norm_num) (by norm_num)
  intro c hc0 hc1
  exact F_piece hconc (h := 0.7725) (a := 0) (b := 1 - 0.7725) (α := 1 / 0.866025294) (β :=
      -0.499999899 / 0.866025294)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_3_1 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.866025294 : ℝ) + -0.499999899 / 0.866025294 * (0) ≤ 0.708697239 +
          0.708697239 by norm_num])
      (by linarith [show (1 / 0.866025294 : ℝ) + -0.499999899 / 0.866025294 * (1 - 0.7725) ≤
          0.708697239 + 0.577350012 by norm_num])
      c ⟨hc0, hc1⟩

/-- (P_h) for the regular 6-gon at `h = 0.7725`. -/
theorem condP_3 : Scaled.CondP (prof 3) 0.7725 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 3) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.7725) (b := 0.965625) (c := 1)
    (integrable_div (continuous_prof 3) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 3) (by norm_num) (by norm_num))]
  have hLh : (0.708697239:ℝ) ≤ prof 3 (0.7725) := le_prof_3 (by norm_num) (by norm_num)
      (by norm_num)
  have hlog0 := log_bounds (h := 0.7725) (p := 0.7725) (q := 0.965625) 16 (by norm_num)
      (by norm_num)
  have hP0 := P_piece (by simp [idx] : 1 ∈ idx 3) tb_3_1 (by norm_num)
    (h := 0.7725) (p := 0.7725) (q := 0.965625) (Nb := 0.162010197) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682072:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.287682073:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.7725) (p := 0.965625) (q := 1) 8 (by norm_num) (by norm_num)
  have hP1 := P_piece (by simp [idx] : 1 ∈ idx 3) tb_3_1 (by norm_num)
    (h := 0.7725) (p := 0.965625) (q := 1) (Nb := 0.031102349) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.061164141:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.061164142:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith

/-! ### The regular 8-gon, `h = 0.707` -/

lemma tb_4_1 : TB 4 1 0.707106719 0.707106897 0.707106665 0.707106843 := by
  have H := tb_of 4 1 (ylo := 1 * 3.141592 / 4) (yhi := 1 * 3.141593 / 4) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_4_2 : TB 4 2 0 0 1 1 := tb_half 4 2 (by norm_num) (by norm_num)

lemma le_prof_4 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.707106897) / 0.707106843)
    (h2 : L ≤ (1 - x * 0) / 1) :
    L ≤ prof 4 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_4_1.term_ge hx (by norm_num) (by nlinarith))
  · exact h2.trans (tb_4_2.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 8-gon at `h = 0.707`. -/
theorem condF_4 : Scaled.CondF (prof 4) 0.707 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 4) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.707213384:ℝ) ≤ prof 4 (0.707) := le_prof_4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hL0 : (0.707213384:ℝ) ≤ prof 4 (0.707 + (0)) := le_prof_4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hL1 : (0.414213362:ℝ) ≤ prof 4 (0.707 + (1 - 0.707)) := le_prof_4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  intro c hc0 hc1
  exact F_piece hconc (h := 0.707) (a := 0) (b := 1 - 0.707) (α := 1 / 1) (β := -0 / 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_4_2 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0) ≤ 0.707213384 + 0.707213384 by norm_num])
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (1 - 0.707) ≤ 0.707213384 + 0.414213362
          by norm_num])
      c ⟨hc0, hc1⟩

/-- (P_h) for the regular 8-gon at `h = 0.707`. -/
theorem condP_4 : Scaled.CondP (prof 4) 0.707 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 4) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.707) (b := 0.88375) (c := 1)
    (integrable_div (continuous_prof 4) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 4) (by norm_num) (by norm_num))]
  have hLh : (0.707213384:ℝ) ≤ prof 4 (0.707) := le_prof_4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hlog0 := log_bounds (h := 0.707) (p := 0.707) (q := 0.88375) 16 (by norm_num) (by norm_num)
  have hP0 := P_piece (by simp [idx] : 1 ∈ idx 4) tb_4_1 (by norm_num)
    (h := 0.707) (p := 0.707) (q := 0.88375) (Nb := 0.125024582) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682072:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.287682073:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.707) (p := 0.88375) (q := 1) 15 (by norm_num) (by norm_num)
  have hP1 := P_piece (by simp [idx] : 1 ∈ idx 4) tb_4_1 (by norm_num)
    (h := 0.707) (p := 0.88375) (q := 1) (Nb := 0.082238551) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.247482619:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.24748262:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith

/-! ### The regular 10-gon, `h = 0.6885` -/

lemma tb_5_1 : TB 5 1 0.809016953 0.809017072 0.587785146 0.587785309 := by
  have H := tb_of 5 1 (ylo := 1 * 3.141592 / 5) (yhi := 1 * 3.141593 / 5) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_5_2 : TB 5 2 0.309016862 0.309017244 0.951056435 0.95105656 := by
  have H := tb_of 5 2 (ylo := 2 * 3.141592 / 5) (yhi := 2 * 3.141593 / 5) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma le_prof_5 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.809017072) / 0.587785309)
    (h2 : L ≤ (1 - x * 0.309017244) / 0.95105656) :
    L ≤ prof 5 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_5_1.term_ge hx (by norm_num) (by nlinarith))
  · exact h2.trans (tb_5_2.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 10-gon at `h = 0.6885`. -/
theorem condF_5 : Scaled.CondF (prof 5) 0.6885 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 5) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.7536625:ℝ) ≤ prof 5 (0.6885) := le_prof_5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hL0 : (0.7536625:ℝ) ≤ prof 5 (0.6885 + (0)) := le_prof_5 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hL1 : (0.324919532:ℝ) ≤ prof 5 (0.6885 + (1 - 0.6885)) := le_prof_5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  intro c hc0 hc1
  exact F_piece hconc (h := 0.6885) (a := 0) (b := 1 - 0.6885) (α := 1 / 0.951056435) (β :=
      -0.309016862 / 0.951056435)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_5_2 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.951056435 : ℝ) + -0.309016862 / 0.951056435 * (0) ≤ 0.7536625 +
          0.7536625 by norm_num])
      (by linarith [show (1 / 0.951056435 : ℝ) + -0.309016862 / 0.951056435 * (1 - 0.6885) ≤
          0.7536625 + 0.324919532 by norm_num])
      c ⟨hc0, hc1⟩

/-- (P_h) for the regular 10-gon at `h = 0.6885`. -/
theorem condP_5 : Scaled.CondP (prof 5) 0.6885 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 5) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.6885) (b := 0.860625) (c := 1)
    (integrable_div (continuous_prof 5) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 5) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.860625) (b := 0.989719) (c := 1)
    (integrable_div (continuous_prof 5) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 5) (by norm_num) (by norm_num))]
  have hLh : (0.7536625:ℝ) ≤ prof 5 (0.6885) := le_prof_5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hlog0 := log_bounds (h := 0.6885) (p := 0.6885) (q := 0.860625) 16 (by norm_num)
      (by norm_num)
  have hP0 := P_piece (by simp [idx] : 1 ∈ idx 5) tb_5_1 (by norm_num)
    (h := 0.6885) (p := 0.6885) (q := 0.860625) (Nb := 0.106451585) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682072:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.287682073:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.6885) (p := 0.860625) (q := 0.989719) 16 (by norm_num)
      (by norm_num)
  have hP1 := P_piece (by simp [idx] : 1 ∈ idx 5) tb_5_1 (by norm_num)
    (h := 0.6885) (p := 0.860625) (q := 0.989719) (Nb := 0.071638703) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682717:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.287682719:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog2 := log_bounds (h := 0.6885) (p := 0.989719) (q := 1) 6 (by norm_num) (by norm_num)
  have hP2 := P_piece (by simp [idx] : 1 ∈ idx 5) tb_5_1 (by norm_num)
    (h := 0.6885) (p := 0.989719) (q := 1) (Nb := 0.005249855) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.02690534:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog2.1)
    (hlog2.2.trans (show _ ≤ (0.026905341:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith

/-! ### The regular 12-gon, `h = 0.671` -/

lemma tb_6_1 : TB 6 1 0.866025374 0.866025459 0.499999905 0.500000051 := by
  have H := tb_of 6 1 (ylo := 1 * 3.141592 / 6) (yhi := 1 * 3.141593 / 6) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_6_2 : TB 6 2 0.499999899 0.500000189 0.866025294 0.866025462 := by
  have H := tb_of 6 2 (ylo := 2 * 3.141592 / 6) (yhi := 2 * 3.141593 / 6) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_6_3 : TB 6 3 0 0 1 1 := tb_half 6 3 (by norm_num) (by norm_num)

lemma le_prof_6 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.866025459) / 0.500000051)
    (h2 : L ≤ (1 - x * 0.500000189) / 0.866025462) (h3 : L ≤ (1 - x * 0) / 1) :
    L ≤ prof 6 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_6_1.term_ge hx (by norm_num) (by nlinarith))
  · exact h2.trans (tb_6_2.term_ge hx (by norm_num) (by nlinarith))
  · exact h3.trans (tb_6_3.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 12-gon at `h = 0.671`. -/
theorem condF_6 : Scaled.CondF (prof 6) 0.671 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 6) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.767298309:ℝ) ≤ prof 6 (0.671) := le_prof_6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hL0 : (0.767298309:ℝ) ≤ prof 6 (0.671 + (0)) := le_prof_6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hL1 : (0.732050318:ℝ) ≤ prof 6 (0.671 + (0.061051)) := le_prof_6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hL2 : (0.373692484:ℝ) ≤ prof 6 (0.671 + (0.267949)) := le_prof_6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hL3 : (0.267949054:ℝ) ≤ prof 6 (0.671 + (1 - 0.671)) := le_prof_6 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro c hc0 hc1
  rcases le_total c (0.061051) with g0 | g0
  · exact F_piece hconc (h := 0.671) (a := 0) (b := 0.061051) (α := 1 / 1) (β := -0 / 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_6_3 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0) ≤ 0.767298309 + 0.767298309 by norm_num])
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0.061051) ≤ 0.767298309 + 0.732050318 by norm_num])
      c ⟨hc0, g0⟩
  rcases le_total c (0.267949) with g1 | g1
  · exact F_piece hconc (h := 0.671) (a := 0.061051) (b := 0.267949) (α := 1 / 1) (β := -0 / 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_6_3 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0.061051) ≤ 0.767298309 + 0.732050318 by norm_num])
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0.267949) ≤ 0.767298309 + 0.373692484 by norm_num])
      c ⟨g0, g1⟩
  exact F_piece hconc (h := 0.671) (a := 0.267949) (b := 1 - 0.671) (α := 1 / 0.866025294) (β :=
      -0.499999899 / 0.866025294)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_6_2 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.866025294 : ℝ) + -0.499999899 / 0.866025294 * (0.267949) ≤
          0.767298309 + 0.373692484 by norm_num])
      (by linarith [show (1 / 0.866025294 : ℝ) + -0.499999899 / 0.866025294 * (1 - 0.671) ≤
          0.767298309 + 0.267949054 by norm_num])
      c ⟨g1, hc1⟩

/-- (P_h) for the regular 12-gon at `h = 0.671`. -/
theorem condP_6 : Scaled.CondP (prof 6) 0.671 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 6) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.671) (b := 0.732051) (c := 1)
    (integrable_div (continuous_prof 6) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 6) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.732051) (b := 0.884538) (c := 1)
    (integrable_div (continuous_prof 6) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 6) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.884538) (b := 0.998904) (c := 1)
    (integrable_div (continuous_prof 6) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 6) (by norm_num) (by norm_num))]
  have hLh : (0.767298309:ℝ) ≤ prof 6 (0.671) := le_prof_6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hlog0 := log_bounds (h := 0.671) (p := 0.671) (q := 0.732051) 9 (by norm_num) (by norm_num)
  have hP0 := P_piece (by simp [idx] : 2 ∈ idx 6) tb_6_2 (by norm_num)
    (h := 0.671) (p := 0.671) (q := 0.732051) (Nb := 0.061910064) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.095393789:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.09539379:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.671) (p := 0.732051) (q := 0.884538) 16 (by norm_num)
      (by norm_num)
  have hP1 := P_piece (by simp [idx] : 1 ∈ idx 6) tb_6_1 (by norm_num)
    (h := 0.671) (p := 0.732051) (q := 0.884538) (Nb := 0.085393927) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287681525:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.287681527:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog2 := log_bounds (h := 0.671) (p := 0.884538) (q := 0.998904) 16 (by norm_num)
      (by norm_num)
  have hP2 := P_piece (by simp [idx] : 1 ∈ idx 6) tb_6_1 (by norm_num)
    (h := 0.671) (p := 0.884538) (q := 0.998904) (Nb := 0.052379849) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287683529:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog2.1)
    (hlog2.2.trans (show _ ≤ (0.28768353:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog3 := log_bounds (h := 0.671) (p := 0.998904) (q := 1) 4 (by norm_num) (by norm_num)
  have hP3 := P_piece (by simp [idx] : 1 ∈ idx 6) tb_6_1 (by norm_num)
    (h := 0.671) (p := 0.998904) (q := 1) (Nb := 0.000430177) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.003199554:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog3.1)
    (hlog3.2.trans (show _ ≤ (0.003199555:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith

/-! ### The regular 14-gon, `h = 0.6635` -/

lemma tb_7_1 : TB 7 1 0.900968846 0.900968909 0.433883654 0.433883784 := by
  have H := tb_of 7 1 (ylo := 1 * 3.141592 / 7) (yhi := 1 * 3.141593 / 7) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_7_2 : TB 7 2 0.623489724 0.623489948 0.781831366 0.781831545 := by
  have H := tb_of 7 2 (ylo := 2 * 3.141592 / 7) (yhi := 2 * 3.141593 / 7) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_7_3 : TB 7 3 0.222520789 0.222521208 0.974927849 0.974927946 := by
  have H := tb_of 7 3 (ylo := 3 * 3.141592 / 7) (yhi := 3 * 3.141593 / 7) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma le_prof_7 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.900968909) / 0.433883784)
    (h2 : L ≤ (1 - x * 0.623489948) / 0.781831545) (h3 : L ≤ (1 - x * 0.222521208) / 0.974927946) :
    L ≤ prof 7 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_7_1.term_ge hx (by norm_num) (by nlinarith))
  · exact h2.trans (tb_7_2.term_ge hx (by norm_num) (by nlinarith))
  · exact h3.trans (tb_7_3.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 14-gon at `h = 0.6635`. -/
theorem condF_7 : Scaled.CondF (prof 7) 0.6635 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 7) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.74992423:ℝ) ≤ prof 7 (0.6635) := le_prof_7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hL0 : (0.74992423:ℝ) ≤ prof 7 (0.6635 + (0)) := le_prof_7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hL1 : (0.639523313:ℝ) ≤ prof 7 (0.6635 + (0.138438)) := le_prof_7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL2 : (0.228243356:ℝ) ≤ prof 7 (0.6635 + (1 - 0.6635)) := le_prof_7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro c hc0 hc1
  rcases le_total c (0.138438) with g0 | g0
  · exact F_piece hconc (h := 0.6635) (a := 0) (b := 0.138438) (α := 1 / 0.974927849) (β :=
      -0.222520789 / 0.974927849)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_7_3 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.974927849 : ℝ) + -0.222520789 / 0.974927849 * (0) ≤ 0.74992423 +
          0.74992423 by norm_num])
      (by linarith [show (1 / 0.974927849 : ℝ) + -0.222520789 / 0.974927849 * (0.138438) ≤
          0.74992423 + 0.639523313 by norm_num])
      c ⟨hc0, g0⟩
  exact F_piece hconc (h := 0.6635) (a := 0.138438) (b := 1 - 0.6635) (α := 1 / 0.974927849) (β :=
      -0.222520789 / 0.974927849)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_7_3 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.974927849 : ℝ) + -0.222520789 / 0.974927849 * (0.138438) ≤
          0.74992423 + 0.639523313 by norm_num])
      (by linarith [show (1 / 0.974927849 : ℝ) + -0.222520789 / 0.974927849 * (1 - 0.6635) ≤
          0.74992423 + 0.228243356 by norm_num])
      c ⟨g0, hc1⟩

/-- (P_h) for the regular 14-gon at `h = 0.6635`. -/
theorem condP_7 : Scaled.CondP (prof 7) 0.6635 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 7) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.6635) (b := 0.801938) (c := 1)
    (integrable_div (continuous_prof 7) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 7) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.801938) (b := 0.933204) (c := 1)
    (integrable_div (continuous_prof 7) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 7) (by norm_num) (by norm_num))]
  have hLh : (0.74992423:ℝ) ≤ prof 7 (0.6635) := le_prof_7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hlog0 := log_bounds (h := 0.6635) (p := 0.6635) (q := 0.801938) 14 (by norm_num)
      (by norm_num)
  have hP0 := P_piece (by simp [idx] : 2 ∈ idx 7) tb_7_2 (by norm_num)
    (h := 0.6635) (p := 0.6635) (q := 0.801938) (Nb := 0.126712047) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.234012502:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.234012503:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.6635) (p := 0.801938) (q := 0.933204) 16 (by norm_num)
      (by norm_num)
  have hP1 := P_piece (by simp [idx] : 1 ∈ idx 7) tb_7_1 (by norm_num)
    (h := 0.6635) (p := 0.801938) (q := 0.933204) (Nb := 0.061999841) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287683342:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.287683343:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog2 := log_bounds (h := 0.6635) (p := 0.933204) (q := 1) 13 (by norm_num) (by norm_num)
  have hP2 := P_piece (by simp [idx] : 1 ∈ idx 7) tb_7_1 (by norm_num)
    (h := 0.6635) (p := 0.933204) (q := 1) (Nb := 0.023827054) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.185872837:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog2.1)
    (hlog2.2.trans (show _ ≤ (0.185872838:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith

/-! ### The regular 16-gon, `h = 0.6575` -/

lemma tb_8_1 : TB 8 1 0.923879515 0.923879564 0.382683356 0.382683473 := by
  have H := tb_of 8 1 (ylo := 1 * 3.141592 / 8) (yhi := 1 * 3.141593 / 8) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_8_2 : TB 8 2 0.707106719 0.707106897 0.707106665 0.707106843 := by
  have H := tb_of 8 2 (ylo := 2 * 3.141592 / 8) (yhi := 2 * 3.141593 / 8) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_8_3 : TB 8 3 0.382683312 0.382683659 0.923879438 0.923879583 := by
  have H := tb_of 8 3 (ylo := 3 * 3.141592 / 8) (yhi := 3 * 3.141593 / 8) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_8_4 : TB 8 4 0 0 1 1 := tb_half 8 4 (by norm_num) (by norm_num)

lemma le_prof_8 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.923879564) / 0.382683473)
    (h2 : L ≤ (1 - x * 0.707106897) / 0.707106843) (h3 : L ≤ (1 - x * 0.382683659) / 0.923879583)
    (h4 : L ≤ (1 - x * 0) / 1) :
    L ≤ prof 8 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_8_1.term_ge hx (by norm_num) (by nlinarith))
  · exact h2.trans (tb_8_2.term_ge hx (by norm_num) (by nlinarith))
  · exact h3.trans (tb_8_3.term_ge hx (by norm_num) (by nlinarith))
  · exact h4.trans (tb_8_4.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 16-gon at `h = 0.6575`. -/
theorem condF_8 : Scaled.CondF (prof 8) 0.6575 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 8) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.756713388:ℝ) ≤ prof 8 (0.6575) := le_prof_8 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL0 : (0.756713388:ℝ) ≤ prof 8 (0.6575 + (0)) := le_prof_8 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL1 : (0.566454374:ℝ) ≤ prof 8 (0.6575 + (0.190259)) := le_prof_8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL2 : (0.545564335:ℝ) ≤ prof 8 (0.6575 + (0.198912)) := le_prof_8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL3 : (0.198912263:ℝ) ≤ prof 8 (0.6575 + (1 - 0.6575)) := le_prof_8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro c hc0 hc1
  rcases le_total c (0.190259) with g0 | g0
  · exact F_piece hconc (h := 0.6575) (a := 0) (b := 0.190259) (α := 1 / 1) (β := -0 / 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_8_4 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0) ≤ 0.756713388 + 0.756713388 by norm_num])
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0.190259) ≤ 0.756713388 + 0.566454374 by norm_num])
      c ⟨hc0, g0⟩
  rcases le_total c (0.198912) with g1 | g1
  · exact F_piece hconc (h := 0.6575) (a := 0.190259) (b := 0.198912) (α := 1 / 1) (β := -0 / 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_8_4 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0.190259) ≤ 0.756713388 + 0.566454374 by norm_num])
      (by linarith [show (1 / 1 : ℝ) + -0 / 1 * (0.198912) ≤ 0.756713388 + 0.545564335 by norm_num])
      c ⟨g0, g1⟩
  exact F_piece hconc (h := 0.6575) (a := 0.198912) (b := 1 - 0.6575) (α := 1 / 0.923879438) (β :=
      -0.382683312 / 0.923879438)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_8_3 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.923879438 : ℝ) + -0.382683312 / 0.923879438 * (0.198912) ≤
          0.756713388 + 0.545564335 by norm_num])
      (by linarith [show (1 / 0.923879438 : ℝ) + -0.382683312 / 0.923879438 * (1 - 0.6575) ≤
          0.756713388 + 0.198912263 by norm_num])
      c ⟨g1, hc1⟩

/-- (P_h) for the regular 16-gon at `h = 0.6575`. -/
theorem condP_8 : Scaled.CondP (prof 8) 0.6575 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 8) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.6575) (b := 0.821875) (c := 1)
    (integrable_div (continuous_prof 8) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 8) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.821875) (b := 0.847759) (c := 1)
    (integrable_div (continuous_prof 8) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 8) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.847759) (b := 0.964569) (c := 1)
    (integrable_div (continuous_prof 8) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 8) (by norm_num) (by norm_num))]
  have hLh : (0.756713388:ℝ) ≤ prof 8 (0.6575) := le_prof_8 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog0 := log_bounds (h := 0.6575) (p := 0.6575) (q := 0.821875) 16 (by norm_num)
      (by norm_num)
  have hP0 := P_piece (by simp [idx] : 2 ∈ idx 8) tb_8_2 (by norm_num)
    (h := 0.6575) (p := 0.6575) (q := 0.821875) (Nb := 0.136412907) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682072:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.287682073:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.6575) (p := 0.821875) (q := 0.847759) 7 (by norm_num)
      (by norm_num)
  have hP1 := P_piece (by simp [idx] : 2 ∈ idx 8) tb_8_2 (by norm_num)
    (h := 0.6575) (p := 0.821875) (q := 0.847759) (Nb := 0.022085315) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.053917507:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.053917508:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog2 := log_bounds (h := 0.6575) (p := 0.847759) (q := 0.964569) 16 (by norm_num)
      (by norm_num)
  have hP2 := P_piece (by simp [idx] : 1 ∈ idx 8) tb_8_1 (by norm_num)
    (h := 0.6575) (p := 0.847759) (q := 0.964569) (Nb := 0.046095193) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287681358:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog2.1)
    (hlog2.2.trans (show _ ≤ (0.28768136:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog3 := log_bounds (h := 0.6575) (p := 0.964569) (q := 1) 10 (by norm_num) (by norm_num)
  have hP3 := P_piece (by simp [idx] : 1 ∈ idx 8) tb_8_1 (by norm_num)
    (h := 0.6575) (p := 0.964569) (q := 1) (Nb := 0.009827363) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.106591186:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog3.1)
    (hlog3.2.trans (show _ ≤ (0.106591187:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith

/-! ### The regular 18-gon, `h = 0.6505` -/

lemma tb_9_1 : TB 9 1 0.939692607 0.939692646 0.342020075 0.34202018 := by
  have H := tb_of 9 1 (ylo := 1 * 3.141592 / 9) (yhi := 1 * 3.141593 / 9) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_9_2 : TB 9 2 0.766044393 0.766044537 0.642787498 0.642787669 := by
  have H := tb_of 9 2 (ylo := 2 * 3.141592 / 9) (yhi := 2 * 3.141593 / 9) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_9_3 : TB 9 3 0.499999899 0.500000189 0.866025294 0.866025462 := by
  have H := tb_of 9 3 (ylo := 3 * 3.141592 / 9) (yhi := 3 * 3.141593 / 9) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma tb_9_4 : TB 9 4 0.173648026 0.173648465 0.984807702 0.98480778 := by
  have H := tb_of 9 4 (ylo := 4 * 3.141592 / 9) (yhi := 4 * 3.141593 / 9) (by norm_num)
    (by push_cast; linarith [pi_gt_d6]) (by push_cast; linarith [pi_lt_d6]) (by norm_num)
  exact ⟨le_trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]) H.cl,
    H.cu.trans (by norm_num [cosS, Finset.sum_range_succ, Nat.factorial]),
    le_trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial]) H.sl,
    H.su.trans (by norm_num [sinS, Finset.sum_range_succ, Nat.factorial])⟩

lemma le_prof_9 {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (h1 : L ≤ (1 - x * 0.939692646) / 0.34202018)
    (h2 : L ≤ (1 - x * 0.766044537) / 0.642787669) (h3 : L ≤ (1 - x * 0.500000189) / 0.866025462)
    (h4 : L ≤ (1 - x * 0.173648465) / 0.98480778) :
    L ≤ prof 9 x := by
  refine le_prof_iff.2 fun j hj => ?_
  simp only [idx, Finset.mem_Icc] at hj
  norm_num at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact h1.trans (tb_9_1.term_ge hx (by norm_num) (by nlinarith))
  · exact h2.trans (tb_9_2.term_ge hx (by norm_num) (by nlinarith))
  · exact h3.trans (tb_9_3.term_ge hx (by norm_num) (by nlinarith))
  · exact h4.trans (tb_9_4.term_ge hx (by norm_num) (by nlinarith))

/-- (F_h) for the regular 18-gon at `h = 0.6505`. -/
theorem condF_9 : Scaled.CondF (prof 9) 0.6505 := by
  have hconc : ConcaveOn ℝ (Icc 0 1) (prof 9) :=
    (concaveOn_prof (by norm_num)).subset (subset_univ _) (convex_Icc _ _)
  have hLh : (0.779133993:ℝ) ≤ prof 9 (0.6505) := le_prof_9 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL0 : (0.779133993:ℝ) ≤ prof 9 (0.6505 + (0)) := le_prof_9 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL1 : (0.777861322:ℝ) ≤ prof 9 (0.6505 + (0.002204)) := le_prof_9 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL2 : (0.507713418:ℝ) ≤ prof 9 (0.6505 + (0.228885)) := le_prof_9 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL3 : (0.182382327:ℝ) ≤ prof 9 (0.6505 + (0.347296)) := le_prof_9 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL4 : (0.176326888:ℝ) ≤ prof 9 (0.6505 + (1 - 0.6505)) := le_prof_9 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro c hc0 hc1
  rcases le_total c (0.002204) with g0 | g0
  · exact F_piece hconc (h := 0.6505) (a := 0) (b := 0.002204) (α := 1 / 0.984807702) (β :=
      -0.173648026 / 0.984807702)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_9_4 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.984807702 : ℝ) + -0.173648026 / 0.984807702 * (0) ≤ 0.779133993 +
          0.779133993 by norm_num])
      (by linarith [show (1 / 0.984807702 : ℝ) + -0.173648026 / 0.984807702 * (0.002204) ≤
          0.779133993 + 0.777861322 by norm_num])
      c ⟨hc0, g0⟩
  rcases le_total c (0.228885) with g1 | g1
  · exact F_piece hconc (h := 0.6505) (a := 0.002204) (b := 0.228885) (α := 1 / 0.984807702) (β :=
      -0.173648026 / 0.984807702)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_9_4 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.984807702 : ℝ) + -0.173648026 / 0.984807702 * (0.002204) ≤
          0.779133993 + 0.777861322 by norm_num])
      (by linarith [show (1 / 0.984807702 : ℝ) + -0.173648026 / 0.984807702 * (0.228885) ≤
          0.779133993 + 0.507713418 by norm_num])
      c ⟨g0, g1⟩
  rcases le_total c (0.347296) with g2 | g2
  · exact F_piece hconc (h := 0.6505) (a := 0.228885) (b := 0.347296) (α := 1 / 0.984807702) (β :=
      -0.173648026 / 0.984807702)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_9_4 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.984807702 : ℝ) + -0.173648026 / 0.984807702 * (0.228885) ≤
          0.779133993 + 0.507713418 by norm_num])
      (by linarith [show (1 / 0.984807702 : ℝ) + -0.173648026 / 0.984807702 * (0.347296) ≤
          0.779133993 + 0.182382327 by norm_num])
      c ⟨g1, g2⟩
  exact F_piece hconc (h := 0.6505) (a := 0.347296) (b := 1 - 0.6505) (α := 1 / 0.866025294) (β :=
      -0.499999899 / 0.866025294)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun c hc => prof_le_aff tb_9_3 (by simp [idx]) (by norm_num) (by norm_num) (by norm_num)
        (by linarith [hc.1]) (by linarith [hc.2]))
      (by linarith [show (1 / 0.866025294 : ℝ) + -0.499999899 / 0.866025294 * (0.347296) ≤
          0.779133993 + 0.182382327 by norm_num])
      (by linarith [show (1 / 0.866025294 : ℝ) + -0.499999899 / 0.866025294 * (1 - 0.6505) ≤
          0.779133993 + 0.176326888 by norm_num])
      c ⟨g2, hc1⟩

/-- (P_h) for the regular 18-gon at `h = 0.6505`. -/
theorem condP_9 : Scaled.CondP (prof 9) 0.6505 2 := by
  simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  refine ⟨integrable_div (continuous_prof 9) (by norm_num) (by norm_num), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.6505) (b := 0.652704) (c := 1)
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.652704) (b := 0.814778) (c := 1)
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.814778) (b := 0.879385) (c := 1)
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0.879385) (b := 0.984789) (c := 1)
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))
    (integrable_div (continuous_prof 9) (by norm_num) (by norm_num))]
  have hLh : (0.779133993:ℝ) ≤ prof 9 (0.6505) := le_prof_9 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog0 := log_bounds (h := 0.6505) (p := 0.6505) (q := 0.652704) 4 (by norm_num) (by norm_num)
  have hP0 := P_piece (by simp [idx] : 3 ∈ idx 9) tb_9_3 (by norm_num)
    (h := 0.6505) (p := 0.6505) (q := 0.652704) (Nb := 0.002288174) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.003393915:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog0.1)
    (hlog0.2.trans (show _ ≤ (0.003393916:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog1 := log_bounds (h := 0.6505) (p := 0.652704) (q := 0.814778) 16 (by norm_num)
      (by norm_num)
  have hP1 := P_piece (by simp [idx] : 2 ∈ idx 9) tb_9_2 (by norm_num)
    (h := 0.6505) (p := 0.652704) (q := 0.814778) (Nb := 0.125127165) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682072:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog1.1)
    (hlog1.2.trans (show _ ≤ (0.287682073:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog2 := log_bounds (h := 0.6505) (p := 0.814778) (q := 0.879385) 11 (by norm_num)
      (by norm_num)
  have hP2 := P_piece (by simp [idx] : 2 ∈ idx 9) tb_9_2 (by norm_num)
    (h := 0.6505) (p := 0.814778) (q := 0.879385) (Nb := 0.049973191) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.142572734:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog2.1)
    (hlog2.2.trans (show _ ≤ (0.142572735:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog3 := log_bounds (h := 0.6505) (p := 0.879385) (q := 0.984789) 16 (by norm_num)
      (by norm_num)
  have hP3 := P_piece (by simp [idx] : 1 ∈ idx 9) tb_9_1 (by norm_num)
    (h := 0.6505) (p := 0.879385) (q := 0.984789) (Nb := 0.035026392) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.287682862:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog3.1)
    (hlog3.2.trans (show _ ≤ (0.287682864:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog4 := log_bounds (h := 0.6505) (p := 0.984789) (q := 1) 7 (by norm_num) (by norm_num)
  have hP4 := P_piece (by simp [idx] : 1 ∈ idx 9) tb_9_1 (by norm_num)
    (h := 0.6505) (p := 0.984789) (q := 1) (Nb := 0.003322562) (by norm_num) (by norm_num)
        (by norm_num)
    (le_trans (show (0.049299447:ℝ) ≤ _ by norm_num [Finset.sum_range_succ]) hlog4.1)
    (hlog4.2.trans (show _ ≤ (0.049299448:ℝ) by norm_num [Finset.sum_range_succ]))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  linarith


/-! ## Corollary 84 (f) -/

/-- The values of `h` of Table `g:tab:polygons`: (P_h) and (F_h) hold for the regular `2m`-gon,
`2m = 6, 8, …, 18`, at `h = 0.7725, 0.707, 0.6885, 0.671, 0.6635, 0.6575, 0.6505`. -/
theorem table_conditions :
    (Scaled.CondP (prof 3) 0.7725 2 ∧ Scaled.CondF (prof 3) 0.7725) ∧
    (Scaled.CondP (prof 4) 0.707 2 ∧ Scaled.CondF (prof 4) 0.707) ∧
    (Scaled.CondP (prof 5) 0.6885 2 ∧ Scaled.CondF (prof 5) 0.6885) ∧
    (Scaled.CondP (prof 6) 0.671 2 ∧ Scaled.CondF (prof 6) 0.671) ∧
    (Scaled.CondP (prof 7) 0.6635 2 ∧ Scaled.CondF (prof 7) 0.6635) ∧
    (Scaled.CondP (prof 8) 0.6575 2 ∧ Scaled.CondF (prof 8) 0.6575) ∧
    (Scaled.CondP (prof 9) 0.6505 2 ∧ Scaled.CondF (prof 9) 0.6505) :=
  ⟨⟨condP_3, condF_3⟩, ⟨condP_4, condF_4⟩, ⟨condP_5, condF_5⟩, ⟨condP_6, condF_6⟩,
    ⟨condP_7, condF_7⟩, ⟨condP_8, condF_8⟩, ⟨condP_9, condF_9⟩⟩

/-- **Corollary 84 (f)** (`g:cor:flat`): for `k = 2` and `K` the regular `2m`-gon with inradius
`1`, `2m ≤ 18` (`2 ≤ m ≤ 9`), the uniform distribution on `K` is `n`-completely mixable for every
`n ≥ 2`. For `3 ≤ m ≤ 9` this is Theorem 83 for the slicing perpendicular to two opposite sides,
with the values of `h` of Table `g:tab:polygons` (`table_conditions`); the square (`m = 2`,
constant profile `r = 1`, not in the table) is added, by Theorem 83 with `h = 3/4`. -/
theorem cor84f {m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ 9) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (regPoly m)) := by
  rw [← bodyK_prof hm2]
  interval_cases m
  · -- the square: `prof 2 = 1`; (P_{1/2}) fails (the integral diverges), `h = 3/4` works
    have hp : ∀ z, prof 2 z = 1 := fun z => by
      have h1 : prof 2 z = term 2 1 z := by
        simp [prof, idx]
      rw [h1, term]
      have e : ((1:ℕ):ℝ) * π / (2:ℕ) = π / 2 := by push_cast; ring
      rw [e, cos_pi_div_two, sin_pi_div_two]; simp
    refine flat_mixable (h := 3 / 4) le_rfl (by norm_num) (by norm_num) ?_ ?_ hn
    · simp only [Scaled.CondP, show (2:ℕ) - 1 = 1 from rfl, pow_one, hp]
      refine ⟨integrable_div continuous_const (by norm_num) (by norm_num), ?_⟩
      have := log_bounds (h := 3 / 4) (p := 3 / 4) (q := 1) 1 (by norm_num) (by norm_num)
      have e : (fun a : ℝ => 1 / (2 * (3 / 4) - a)) = fun a => (2 * (3 / 4) - a)⁻¹ := by
        funext a; rw [one_div]
      rw [e, intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) (2 * (3 / 4)),
        integral_inv_of_pos (by norm_num) (by norm_num)]
      norm_num [Finset.sum_range_succ] at this ⊢
      linarith [this.2]
    · intro c _ _; simp only [hp]; norm_num
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_3 condF_3 hn
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_4 condF_4 hn
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_5 condF_5 hn
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_6 condF_6 hn
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_7 condF_7 hn
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_8 condF_8 hn
  · exact flat_mixable (by norm_num) (by norm_num) (by norm_num) condP_9 condF_9 hn

/-- **Corollary 84 (f)**, the named cases: the regular octagon, decagon, `14`-gon and `16`-gon
(no rotation of order `3`) are `n`-completely mixable for every `n ≥ 2`. -/
theorem cor84f_named {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (regPoly 4)) ∧ CompletelyMixable n (unifSet (regPoly 5)) ∧
    CompletelyMixable n (unifSet (regPoly 7)) ∧ CompletelyMixable n (unifSet (regPoly 8)) :=
  ⟨cor84f (by norm_num) (by norm_num) hn, cor84f (by norm_num) (by norm_num) hn,
    cor84f (by norm_num) (by norm_num) hn, cor84f (by norm_num) (by norm_num) hn⟩

end Flat

end Mixes
