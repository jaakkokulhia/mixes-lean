import Mixes.Defs

/-!
# Room for partners, symmetrisation and the fibre inequality of the bipyramids

Items M1i (Theorem 70, `o:thm:bipyr`, the fibre inequality) and M1k (Lemma 88, `st:lem:tuples`,
Lemma 89, `st:lem:room`, Lemma 92, `st:lem:symm`) of `mixes/LEAN_VERIFICATION_PRIORITIES.md`.

* `fibre_core`, `fibre_triple`: the fibre inequality `r(C) ≤ r(A) + r(B)` for `A = B + C`,
  `C ≤ B ≤ 1/2`, and the fibre condition `2 max r(Z_i) ≤ ∑ r(Z_i)` for levels summing to `0`
  of which two lie in `[-1/2, 1/2]` (Theorem 70).
* `reflect_mem_of_asymLE`, `room`: Lemma 89 (`-K ⊂ as(K) K` by separation; the room `ρ₀`, `α`).
* `affine_of_mean_third`, `affine_of_convex_concave`: the planar equality case of Lemma 89,
  one-dimensional core and planar step.
* `planar_asym`: for a compact convex `K ⊂ ℝ²` of positive area, `as(K) ≤ 2` (Minkowski–Radon
  in the plane, proved) and `as(K) < 2` unless `K` is a triangle (`IsTriangle`, a statement
  about sets), via `fst_core`/`dir_core` (Fubini, `mean_third_ge`, `isTriangle_of_chordLen`)
  and compactness of the unit circle; `room_planar_three`: Lemma 89 for `n = 3` in the plane.
* `completelyMixable_iff_tuples`, `completelyMixable_unif_iff`: Lemma 88.
* `symm_room` (measure-theoretic core) and `symm_robust`: Lemma 92, with `λ` the Lebesgue
  measure on `𝒯_n(K)` (`lebTuples`), whose coordinates have densities at most `|K|^{n-2}`
  (`lebTuples_coord_le`).
-/

open MeasureTheory Set Metric

set_option linter.unusedSectionVars false

noncomputable section

namespace Mixes

namespace Room

/-! ## The fibre inequality of Theorem 70 -/

section Fibre

variable {r : ℝ → ℝ}

lemma concave_comb {s : Set ℝ} (hr : ConcaveOn ℝ s r) {x y a b : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a * r x + b * r y ≤ r (a * x + b * y) := by
  simpa [smul_eq_mul] using hr.2 hx hy ha hb hab

/-- The chord bound: a function concave on `[0,1]` with `r 1 = 0` lies above the chord from
`(C, r C)` to `(1, 0)` on `[C, 1]`, in the form `r(C)(1 - t) ≤ r(t)(1 - C)`. -/
lemma chord_bound (hr : ConcaveOn ℝ (Icc 0 1) r) (h1 : 0 ≤ r 1) {C t : ℝ} (hC0 : 0 ≤ C)
    (hCt : C ≤ t) (ht1 : t ≤ 1) : r C * (1 - t) ≤ r t * (1 - C) := by
  rcases eq_or_lt_of_le (hCt.trans ht1) with hC1 | hC1
  · subst hC1
    have : t = 1 := le_antisymm ht1 hCt
    subst this; simp
  have hpos : 0 < 1 - C := by linarith
  have key := concave_comb hr (show C ∈ Icc (0:ℝ) 1 from ⟨hC0, hC1.le⟩)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    (show 0 ≤ (1 - t) / (1 - C) from div_nonneg (by linarith) hpos.le)
    (show 0 ≤ (t - C) / (1 - C) from div_nonneg (by linarith) hpos.le)
    (by field_simp; ring)
  have hpt : (1 - t) / (1 - C) * C + (t - C) / (1 - C) * (1 : ℝ) = t := by
    field_simp; ring
  rw [hpt] at key
  have hb : 0 ≤ (t - C) / (1 - C) * r 1 := mul_nonneg (div_nonneg (by linarith) hpos.le) h1
  have key' : (1 - t) / (1 - C) * r C ≤ r t := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at key'
  linarith

/-- **Fibre inequality of Theorem 70.** If `r` is concave on `[0,1]`, `r 1 = 0` and `r C ≥ 0`,
then `r(C) ≤ r(A) + r(B)` for `A = B + C` and `0 ≤ C ≤ B ≤ 1/2`. -/
theorem fibre_core (hr : ConcaveOn ℝ (Icc 0 1) r) (h1 : r 1 = 0) {B C : ℝ} (hC0 : 0 ≤ C)
    (hCB : C ≤ B) (hB : B ≤ 1 / 2) (hrC : 0 ≤ r C) : r C ≤ r (B + C) + r B := by
  have hA := chord_bound hr h1.symm.le hC0 (by linarith : C ≤ B + C) (by linarith)
  have hB' := chord_bound hr h1.symm.le hC0 hCB (by linarith)
  have hpos : 0 < 1 - C := by linarith
  have : r C * (1 - C) ≤ (r (B + C) + r B) * (1 - C) := by nlinarith
  exact le_of_mul_le_mul_right this hpos

/-- A function that is even and concave on `[-1,1]` and vanishes at `1` is nonnegative there. -/
lemma nonneg_of_even (hr : ConcaveOn ℝ (Icc (-1) 1) r) (hev : ∀ z, r (-z) = r z) (h1 : r 1 = 0)
    {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : 0 ≤ r z := by
  have key := concave_comb hr (show (-1:ℝ) ∈ Icc (-1:ℝ) 1 from ⟨le_rfl, by norm_num⟩)
    (show (1:ℝ) ∈ Icc (-1:ℝ) 1 from ⟨by norm_num, le_rfl⟩)
    (show 0 ≤ (1 - z) / 2 by linarith [hz.2]) (show 0 ≤ (1 + z) / 2 by linarith [hz.1])
    (by ring)
  have hp : (1 - z) / 2 * (-1 : ℝ) + (1 + z) / 2 * (1 : ℝ) = z := by ring
  rw [hp, hev, h1] at key
  simpa using key

/-- An even function concave on `[-1,1]` is non-increasing in `|z|`. -/
lemma antitone_abs (hr : ConcaveOn ℝ (Icc (-1) 1) r) (hev : ∀ z, r (-z) = r z) {u v : ℝ}
    (huv : |u| ≤ |v|) (hv : |v| ≤ 1) : r v ≤ r u := by
  have habs : ∀ w, r |w| = r w := fun w => by
    rcases abs_choice w with h | h <;> rw [h]; exact hev w
  rw [← habs u, ← habs v]
  rcases eq_or_lt_of_le (abs_nonneg v) with h0 | h0
  · have : |u| = 0 := le_antisymm (h0 ▸ huv) (abs_nonneg u)
    rw [this, ← h0]
  have hmem : |v| ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [abs_nonneg v], hv⟩
  have hmem' : -|v| ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith [abs_nonneg v]⟩
  have key := concave_comb hr hmem hmem'
    (show 0 ≤ (|v| + |u|) / (2 * |v|) from div_nonneg (by linarith [abs_nonneg u]) (by linarith))
    (show 0 ≤ (|v| - |u|) / (2 * |v|) from div_nonneg (by linarith) (by linarith))
    (by field_simp; ring)
  have hp : (|v| + |u|) / (2 * |v|) * |v| + (|v| - |u|) / (2 * |v|) * -|v| = |u| := by
    field_simp; ring
  rw [hp, hev] at key
  have : (|v| + |u|) / (2 * |v|) * r |v| + (|v| - |u|) / (2 * |v|) * r |v| = r |v| := by
    field_simp; ring
  linarith

/-- The three fibre inequalities for absolute values `b + c, b, c` with `0 ≤ b, c ≤ 1/2`. -/
lemma fibre_abs (hr : ConcaveOn ℝ (Icc (-1) 1) r) (hev : ∀ z, r (-z) = r z) (h1 : r 1 = 0)
    {b c : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hb : b ≤ 1 / 2) (hc : c ≤ 1 / 2) :
    r c ≤ r (b + c) + r b ∧ r b ≤ r (b + c) + r c ∧ r (b + c) ≤ r b + r c := by
  have hr01 : ConcaveOn ℝ (Icc 0 1) r :=
    hr.subset (Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc 0 1)
  have nn : ∀ z, 0 ≤ z → z ≤ 1 → 0 ≤ r z := fun z h0 h1' =>
    nonneg_of_even hr hev h1 ⟨by linarith, h1'⟩
  have mono : ∀ u v, 0 ≤ u → u ≤ v → v ≤ 1 → r v ≤ r u := fun u v hu huv hv =>
    antitone_abs hr hev (by rwa [abs_of_nonneg hu, abs_of_nonneg (hu.trans huv)])
      (by rwa [abs_of_nonneg (hu.trans huv)])
  have hbc1 : b + c ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rcases le_total c b with h | h
    · exact fibre_core hr01 h1 hc0 h hb (nn c hc0 (by linarith))
    · linarith [mono b c hb0 h (by linarith), nn (b + c) (by linarith) hbc1]
  · rcases le_total b c with h | h
    · have := fibre_core hr01 h1 hb0 h hc (nn b hb0 (by linarith))
      rw [add_comm c b] at this; exact this
    · linarith [mono c b hc0 h (by linarith), nn (b + c) (by linarith) hbc1]
  · linarith [mono b (b + c) hb0 (by linarith) hbc1, nn c hc0 (by linarith)]

/-- **Fibre condition of Theorem 70.** Let `r` be even, concave on `[-1,1]`, with `r 1 = 0`
(the profile of the body). For levels `x, y, -(x+y)` with `|x|, |y| ≤ 1/2`, as produced by
Lemma 69 (two of the three levels in the central half of the range), the fibre condition
`2 r(z_i) ≤ r(z_1) + r(z_2) + r(z_3)` holds for every `i`. -/
theorem fibre_triple (hr : ConcaveOn ℝ (Icc (-1) 1) r) (hev : ∀ z, r (-z) = r z) (h1 : r 1 = 0)
    {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    ∀ i : Fin 3, 2 * r (![x, y, -(x + y)] i) ≤ ∑ j, r (![x, y, -(x + y)] j) := by
  have habs : ∀ w, r |w| = r w := fun w => by
    rcases abs_choice w with h | h <;> rw [h]; exact hev w
  have e' : r (-y + -x) = r (x + y) := by rw [← hev (x + y)]; ring_nf
  -- the three inequalities `r(z_i) ≤` sum of the other two, in absolute values
  suffices h : r |x| ≤ r |y| + r |x + y| ∧ r |y| ≤ r |x| + r |x + y| ∧
      r |x + y| ≤ r |x| + r |y| by
    intro i
    simp only [habs] at h
    fin_cases i <;> simp [Fin.sum_univ_three, e'] <;> linarith [h.1, h.2.1, h.2.2]
  have same : |x + y| = |x| + |y| → r |x| ≤ r |y| + r |x + y| ∧ r |y| ≤ r |x| + r |x + y| ∧
      r |x + y| ≤ r |x| + r |y| := fun he => by
    obtain ⟨a1, a2, a3⟩ := fibre_abs hr hev h1 (abs_nonneg x) (abs_nonneg y) hx hy
    rw [he]; exact ⟨by linarith, by linarith, by linarith⟩
  have opp : |x + y| ≤ 1 / 2 → (|x| = |x + y| + |y| ∨ |y| = |x + y| + |x|) →
      r |x| ≤ r |y| + r |x + y| ∧ r |y| ≤ r |x| + r |x + y| ∧
      r |x + y| ≤ r |x| + r |y| := fun hs he => by
    rcases he with he | he
    · obtain ⟨a1, a2, a3⟩ := fibre_abs hr hev h1 (abs_nonneg (x + y)) (abs_nonneg y) hs hy
      rw [he]; exact ⟨by linarith, by linarith, by linarith⟩
    · obtain ⟨a1, a2, a3⟩ := fibre_abs hr hev h1 (abs_nonneg (x + y)) (abs_nonneg x) hs hx
      rw [he]; exact ⟨by linarith, by linarith, by linarith⟩
  rw [abs_le] at hx hy
  rcases le_total 0 x with h0 | h0 <;> rcases le_total 0 y with h0' | h0'
  · exact same (by rw [abs_of_nonneg h0, abs_of_nonneg h0', abs_of_nonneg (by linarith)])
  · apply opp (by rw [abs_le]; constructor <;> linarith)
    rcases le_total 0 (x + y) with h2 | h2
    · left; rw [abs_of_nonneg h0, abs_of_nonpos h0', abs_of_nonneg h2]; ring
    · right; rw [abs_of_nonneg h0, abs_of_nonpos h0', abs_of_nonpos h2]; ring
  · apply opp (by rw [abs_le]; constructor <;> linarith)
    rcases le_total 0 (x + y) with h2 | h2
    · right; rw [abs_of_nonpos h0, abs_of_nonneg h0', abs_of_nonneg h2]; ring
    · left; rw [abs_of_nonpos h0, abs_of_nonneg h0', abs_of_nonpos h2]; ring
  · exact same (by rw [abs_of_nonpos h0, abs_of_nonpos h0', abs_of_nonpos (by linarith)]; ring)

end Fibre

/-! ## Room for partners (Lemma 89) -/

section RoomSec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inner parallel body `K_ρ = {x : x + ρB ⊂ K}`. -/
def innerBody (K : Set E) (ρ : ℝ) : Set E := {x | closedBall x ρ ⊆ K}

/-- `AsymLE K c a`: Minkowski's measure of asymmetry of `K` about `c` is at most `a`, i.e.
`max_K u - u(c) ≤ a (u(c) - min_K u)` for every continuous linear functional `u`, written without
maxima and minima: for each `x ∈ K` there is `y ∈ K` with `u x - u c ≤ a (u c - u y)`. For a
compact `K` this is exactly `as(K) ≤ a` in the notation of the remark `g:rem:asym`. -/
def AsymLE (K : Set E) (c : E) (a : ℝ) : Prop :=
  ∀ u : StrongDual ℝ E, ∀ x ∈ K, ∃ y ∈ K, u x - u c ≤ a * (u c - u y)

/-- "By the definition of `as(K)`, `-K ⊂ as(K) K`" (with `c = 0`): for closed convex `K`, the
asymmetry bound gives `c - (x - c)/a ∈ K` for every `x ∈ K`. Proof by separation. -/
theorem reflect_mem_of_asymLE {K : Set E} (hKc : Convex ℝ K) (hKcl : IsClosed K) {c : E}
    {a : ℝ} (ha : 0 < a) (hK : AsymLE K c a) {x : E} (hx : x ∈ K) :
    c - a⁻¹ • (x - c) ∈ K := by
  by_contra hz
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed hKc hKcl hz
  obtain ⟨y, hy, hxy⟩ := hK f x hx
  have h1 := hb y hy
  have : f (c - a⁻¹ • (x - c)) = f c - a⁻¹ * (f x - f c) := by
    simp [map_sub, map_smul, smul_eq_mul]
  rw [this] at hfu
  have h2 : a⁻¹ * (f x - f c) ≤ f c - f y := by
    rw [inv_mul_le_iff₀ ha]; linarith
  linarith

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- **Lemma 89 (room for partners).** Let `n ≥ 3`, let `K` be closed and convex, containing the
ball `c + sB` (`s > 0`), with asymmetry `as(K) ≤ a < n - 1` about `c`. There are `ρ₀ > 0` and
`α > 0` such that for `0 < ρ ≤ ρ₀` and every `p ∈ K + ρ₀B`, the point `c - (p - c)/(n-1)` lies in
the interior of `K_{2ρ}`, and the set of `y = (x₂, …, x_{n-1})` with all `xᵢ ∈ K_{2ρ}` and
`nc - p - x₂ - ⋯ - x_{n-1} ∈ K_{2ρ}` has measure at least `α`, for any additive Haar measure
`μ` on `E` (product measure on `(Fin (n-2) → E)`). -/
theorem room {n : ℕ} (hn : 3 ≤ n) {K : Set E} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    {c : E} {s a : ℝ} (hs : 0 < s) (hball : closedBall c s ⊆ K) (ha : 0 < a)
    (han : a < n - 1) (hasym : AsymLE K c a) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ ρ₀ > 0, ∃ α : ENNReal, 0 < α ∧ ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ p : E,
      (∃ x ∈ K, dist p x ≤ ρ₀) →
      c - ((n : ℝ) - 1)⁻¹ • (p - c) ∈ interior (innerBody K (2 * ρ)) ∧
      α ≤ Measure.pi (fun _ : Fin (n - 2) => μ)
        {y | (∀ i, y i ∈ innerBody K (2 * ρ)) ∧
          (n : ℝ) • c - p - ∑ i, y i ∈ innerBody K (2 * ρ)} := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set θ := a / ((n : ℝ) - 1) with hθ
  have hθ0 : 0 < θ := div_pos ha hn1
  have hθ1 : θ < 1 := (div_lt_one hn1).2 han
  set ρ₀ := (1 - θ) * s / 8 with hρ₀
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; have := mul_pos (sub_pos.2 hθ1) hs; linarith
  set r' := 4 * ρ₀ / n with hr'
  have hnpos : (0 : ℝ) < n := by linarith
  have hr'pos : 0 < r' := div_pos (by linarith) hnpos
  refine ⟨ρ₀, hρ₀pos, (μ (ball (0 : E) r')) ^ (n - 2), ?_, ?_⟩
  · exact ENNReal.pow_pos (measure_ball_pos μ _ hr'pos) _
  intro ρ hρ hρρ₀ p ⟨x, hx, hpx⟩
  set q := c - ((n : ℝ) - 1)⁻¹ • (p - c) with hq
  -- the point `q_x = c - (x - c)/(n-1)` has a ball of radius `(1-θ)s` inside `K`
  have hqx : closedBall (c - ((n : ℝ) - 1)⁻¹ • (x - c)) ((1 - θ) * s) ⊆ K := by
    intro z hz
    have hk := reflect_mem_of_asymLE hKc hKcl ha hasym hx
    set k' := c - a⁻¹ • (x - c)
    -- `z = θ k' + (1 - θ) w` with `w ∈ c + sB`
    set w := c + (1 - θ)⁻¹ • (z - (c - ((n : ℝ) - 1)⁻¹ • (x - c))) with hw
    have hw' : w ∈ K := by
      apply hball
      rw [mem_closedBall, dist_eq_norm, hw, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 (sub_pos.2 hθ1))]
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [inv_mul_le_iff₀ (sub_pos.2 hθ1)]; exact hz
    have hz' : z = θ • k' + (1 - θ) • w := by
      have h1θ : (1 - θ) ≠ 0 := (sub_pos.2 hθ1).ne'
      rw [hw]
      simp only [k']
      have hna : (n : ℝ) - 1 - a ≠ 0 := by linarith
      match_scalars <;> simp only [hθ] <;> field_simp <;> ring
    rw [hz']
    exact hKc hk hw' hθ0.le (sub_pos.2 hθ1).le (by ring)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdq : dist q (c - ((n : ℝ) - 1)⁻¹ • (x - c)) ≤ ρ₀ := by
    rw [hq, dist_eq_norm]
    have : c - ((n : ℝ) - 1)⁻¹ • (p - c) - (c - ((n : ℝ) - 1)⁻¹ • (x - c)) =
        ((n : ℝ) - 1)⁻¹ • (x - p) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1), ← dist_eq_norm,
      dist_comm, inv_mul_le_iff₀ hn1]
    nlinarith
  have hq7 : closedBall q (7 * ρ₀) ⊆ K := by
    refine (closedBall_subset_closedBall' ?_).trans hqx
    rw [hρ₀] at hdq ⊢; linarith
  have hinner : ∀ z, dist z q ≤ 5 * ρ₀ → z ∈ innerBody K (2 * ρ) := by
    intro z hz
    exact (closedBall_subset_closedBall' (by linarith)).trans hq7
  refine ⟨?_, ?_⟩
  · refine mem_interior.2 ⟨ball q (5 * ρ₀), fun z hz => hinner z (le_of_lt hz), isOpen_ball,
      mem_ball_self (by linarith)⟩
  -- the box of radius `r' = 4ρ₀/n` around `(q, …, q)` lies in the set
  have hbox : Set.pi univ (fun _ : Fin (n - 2) => ball q r') ⊆
      {y | (∀ i, y i ∈ innerBody K (2 * ρ)) ∧
        (n : ℝ) • c - p - ∑ i, y i ∈ innerBody K (2 * ρ)} := by
    intro y hy
    simp only [Set.mem_pi, mem_univ, true_implies, mem_ball] at hy
    have hr'5 : r' ≤ 5 * ρ₀ := by
      rw [hr', div_le_iff₀ hnpos]; nlinarith
    refine ⟨fun i => hinner _ ((hy i).le.trans hr'5), hinner _ ?_⟩
    have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hid : (n : ℝ) • c - p - ∑ i, y i - q = ∑ i : Fin (n - 2), (q - y i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, hcast, hq]
      have := hn1.ne'
      match_scalars <;> field_simp <;> ring
    rw [dist_eq_norm, hid]
    calc ‖∑ i : Fin (n - 2), (q - y i)‖ ≤ ∑ i : Fin (n - 2), ‖q - y i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (n - 2), r' := Finset.sum_le_sum fun i _ => by
          rw [← dist_eq_norm, dist_comm]; exact (hy i).le
      _ = ((n : ℝ) - 2) * r' := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcast]
      _ ≤ 5 * ρ₀ := by
          rw [hr', mul_div_assoc']
          rw [div_le_iff₀ hnpos]; nlinarith
  refine le_trans ?_ (measure_mono hbox)
  rw [Measure.pi_pi]
  simp only [Measure.addHaar_ball_center, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact le_rfl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The condition `as(K) < n - 1` of Lemma 89 for `n ≥ d + 2`, given the theorem of Minkowski and
Radon `as(K) ≤ d` (remark `g:rem:asym`), stated as the hypothesis `AsymLE K c d`. -/
lemma asym_lt_of_dim {K : Set E} {c : E} {d n : ℕ} (hMR : AsymLE K c d) (hn : d + 2 ≤ n) :
    AsymLE K c d ∧ (d : ℝ) < n - 1 :=
  ⟨hMR, by have : ((d + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
           push_cast at this; linarith⟩

end RoomSec

/-! ## The planar equality case of Lemma 89

If `d = 2` and `as(K) = 2`, after an affine change of the level the projection of `U(K)` on the
maximising direction has the density `g / ∫ g` on `[0,1]`, `g` the (concave) chord length, with
mean `1/3`. The one-dimensional core is `affine_of_mean_third`: then `g(s) = κ(1 - s)`. It
replaces the equality case of Chebyshev's inequality by the pointwise inequality
`(s - 1/3)(g(s) - κ(1-s)) ≥ 0`, whose integral vanishes. The planar step is
`affine_of_convex_concave`: the ends of the chords, a convex and a concave function with affine
difference, are both affine, so `K` is a triangle. -/

section Planar

lemma poly_integral : ∫ s in (0:ℝ)..1, (s - 1 / 3) * (1 - s) = 0 := by
  have : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => -1 / 3 * s ^ 3 + 2 / 3 * s ^ 2 - 1 / 3 * s) ((x - 1 / 3) * (1 - x)) x := by
    intro x _
    have := (((hasDerivAt_pow 3 x).const_mul (-1 / 3)).add
      ((hasDerivAt_pow 2 x).const_mul (2 / 3))).sub ((hasDerivAt_id x).const_mul (1 / 3))
    convert this using 1
    · funext s; simp only [Pi.add_apply, Pi.sub_apply, id]
    · norm_num; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    ((by fun_prop : Continuous fun x : ℝ => (x - 1 / 3) * (1 - x)).intervalIntegrable _ _)]
  norm_num

/-- **Equality case behind Lemma 89 (one-dimensional core).** Let `g ≥ 0` be concave on `[0,1]`
with `∫₀¹ s g(s) ds = (1/3) ∫₀¹ g`, i.e. the density proportional to `g` has mean `1/3`. Then
`g(s) = κ (1 - s)` on `(0,1)`, with `κ = (3/2) g(1/3)`. -/
theorem affine_of_mean_third {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (hint : IntervalIntegrable g volume 0 1)
    (hmean : ∫ s in (0:ℝ)..1, s * g s = (1 / 3) * ∫ s in (0:ℝ)..1, g s) :
    ∀ s ∈ Ioo (0:ℝ) 1, g s = 3 / 2 * g (1 / 3) * (1 - s) := by
  set κ := 3 / 2 * g (1 / 3) with hκ
  set φ : ℝ → ℝ := fun s => (s - 1 / 3) * (g s - κ * (1 - s)) with hφ
  have g1 : 0 ≤ g 1 := h0 1 ⟨zero_le_one, le_rfl⟩
  have hφnn : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ φ s := by
    intro s hs
    simp only [hφ]
    rcases le_total s (1 / 3) with h | h
    · have := chord_bound hg g1 hs.1 h (by norm_num)
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      rw [hκ]; nlinarith
    · have := chord_bound hg g1 (by norm_num) h hs.2
      apply mul_nonneg (by linarith)
      rw [hκ]; nlinarith
  -- integrability
  have hpoly : IntervalIntegrable (fun s : ℝ => κ * ((s - 1 / 3) * (1 - s))) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => κ * ((s - 1 / 3) * (1 - s))).intervalIntegrable _ _
  have hsg : IntervalIntegrable (fun s => s * g s) volume 0 1 :=
    hint.continuousOn_mul continuous_id.continuousOn
  have hφeq : φ = fun s => s * g s - (1 / 3) * g s - κ * ((s - 1 / 3) * (1 - s)) := by
    funext s; simp only [hφ]; ring
  have hφint : IntervalIntegrable φ volume 0 1 := by
    rw [hφeq]; exact (hsg.sub (hint.const_mul _)).sub hpoly
  have hI : ∫ s in (0:ℝ)..1, φ s = 0 := by
    rw [hφeq, intervalIntegral.integral_sub (hsg.sub (hint.const_mul _)) hpoly,
      intervalIntegral.integral_sub hsg (hint.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, poly_integral, hmean]
    ring
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun s hs => hφnn s ⟨hs.1.le, hs.2⟩)) hφint).1 hI
  have hae' : φ =ᵐ[volume.restrict (Ioo 0 1)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae
  have hcont : ContinuousOn φ (Ioo 0 1) := by
    have hgc : ContinuousOn g (Ioo 0 1) := by
      simpa [interior_Icc] using hg.continuousOn_interior
    exact ((continuousOn_id.sub continuousOn_const).mul
      (hgc.sub (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))))
  have hEq := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hcont continuousOn_const
  intro s hs
  have := hEq hs
  simp only [hφ, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h | h
  · have : s = 1 / 3 := by linarith
    subst this; rw [hκ]; ring
  · linarith

/-- **Planar step of the equality case.** If the lower end `l` of the chords is convex and the
upper end `u` concave on an interval `I`, and their difference is affine, then `l` and `u` are
both convex and concave on `I`, i.e. affine: the body is a triangle (for `κ > 0`,
`u - l = κ(1 - t)` vanishes at `t = 1`). -/
theorem affine_of_convex_concave {l u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hl : ConvexOn ℝ I l) (hu : ConcaveOn ℝ I u) {κ : ℝ}
    (hdiff : ∀ t ∈ I, u t - l t = κ * (1 - t)) :
    (ConvexOn ℝ I l ∧ ConcaveOn ℝ I l) ∧ (ConvexOn ℝ I u ∧ ConcaveOn ℝ I u) := by
  refine ⟨⟨hl, hI, fun x hx y hy a b ha hb hab => ?_⟩, ⟨hI, fun x hx y hy a b ha hb hab => ?_⟩,
    hu⟩
  · have h := hu.2 hx hy ha hb hab
    have hm := hI hx hy ha hb hab
    have e1 := hdiff x hx; have e2 := hdiff y hy; have e3 := hdiff _ hm
    simp only [smul_eq_mul] at h e3 ⊢
    obtain rfl : b = 1 - a := by linarith
    nlinarith
  · have h := hl.2 hx hy ha hb hab
    have hm := hI hx hy ha hb hab
    have e1 := hdiff x hx; have e2 := hdiff y hy; have e3 := hdiff _ hm
    simp only [smul_eq_mul] at h e3 ⊢
    obtain rfl : b = 1 - a := by linarith
    nlinarith

end Planar

/-! ## Tuples, marginals and symmetrisation (Lemma 88) -/

section Generic

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- A measure on tuples invariant under the permutations of the coordinates. -/
def PermInvariant (β : Measure (Fin n → E)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), β.map (fun x => x ∘ σ) = β

/-- The marginal `β̄`, with `∫ f dβ̄ = ∫ (1/n) ∑ᵢ f(xᵢ) dβ`. -/
def marginal (β : Measure (Fin n → E)) : Measure E :=
  (n : ENNReal)⁻¹ • ∑ i, β.map (fun x => x i)

/-- The average of a measure on tuples over the permutations of the coordinates. -/
def symmetrise (P : Measure (Fin n → E)) : Measure (Fin n → E) :=
  (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
    P.map (fun x => x ∘ σ)

lemma measurable_perm (σ : Equiv.Perm (Fin n)) : Measurable (fun x : Fin n → E => x ∘ σ) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (σ i)

lemma symmetrise_apply (P : Measure (Fin n → E)) {S : Set (Fin n → E)} (hS : MeasurableSet S) :
    symmetrise P S = (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), P ((fun x => x ∘ σ) ⁻¹' S) := by
  rw [symmetrise, smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => Measure.map_apply (measurable_perm σ) hS

lemma marginal_apply (β : Measure (Fin n → E)) {S : Set E} (hS : MeasurableSet S) :
    marginal β S = (n : ENNReal)⁻¹ * ∑ i, β ((fun x => x i) ⁻¹' S) := by
  rw [marginal, smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Measure.map_apply (measurable_pi_apply i) hS

lemma card_perm_ne_zero : (Fintype.card (Equiv.Perm (Fin n)) : ENNReal) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

lemma permInvariant_symmetrise (P : Measure (Fin n → E)) : PermInvariant (symmetrise P) := by
  intro τ
  ext S hS
  rw [Measure.map_apply (measurable_perm τ) hS, symmetrise_apply P (measurable_perm τ hS),
    symmetrise_apply P hS]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => by
    congr 1

lemma map_eval_symmetrise (P : Measure (Fin n → E)) {F : Measure E}
    (hP : ∀ j, P.map (fun x => x j) = F) (i : Fin n) :
    (symmetrise P).map (fun x => x i) = F := by
  ext S hS
  rw [Measure.map_apply (measurable_pi_apply i) hS,
    symmetrise_apply P (measurable_pi_apply i hS)]
  have : ∀ σ : Equiv.Perm (Fin n), P ((fun x => x ∘ σ) ⁻¹' ((fun x => x i) ⁻¹' S)) = F S :=
    fun σ => by
      rw [← hP (σ i), Measure.map_apply (measurable_pi_apply (σ i)) hS]; rfl
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel card_perm_ne_zero (ENNReal.natCast_ne_top _), one_mul]

lemma symmetrise_null (P : Measure (Fin n → E)) {S : Set (Fin n → E)} (hS : MeasurableSet S)
    (hinv : ∀ σ : Equiv.Perm (Fin n), (fun x => x ∘ σ) ⁻¹' S = S) (hP : P S = 0) :
    symmetrise P S = 0 := by
  rw [symmetrise_apply P hS]
  simp [hinv, hP]

lemma symmetrise_isProb (P : Measure (Fin n → E)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (symmetrise P) := by
  constructor
  rw [symmetrise_apply P MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel card_perm_ne_zero (ENNReal.natCast_ne_top _)

lemma map_eval_eq_of_permInvariant {β : Measure (Fin n → E)} (hβ : PermInvariant β)
    (i j : Fin n) : β.map (fun x => x i) = β.map (fun x => x j) := by
  conv_lhs => rw [← hβ (Equiv.swap i j)]
  rw [Measure.map_map (measurable_pi_apply i) (measurable_perm _)]
  congr 1
  funext x
  simp

lemma marginal_eq_of_permInvariant {β : Measure (Fin n → E)} (hβ : PermInvariant β)
    (j : Fin n) : marginal β = β.map (fun x => x j) := by
  ext S hS
  rw [marginal_apply β hS]
  have : ∀ i, β ((fun x => x i) ⁻¹' S) = β.map (fun x => x j) S := fun i => by
    rw [← map_eval_eq_of_permInvariant hβ i j, Measure.map_apply (measurable_pi_apply i) hS]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ENNReal) ≠ 0 := by
    have := j.pos; exact_mod_cast this.ne'
  rw [← mul_assoc, ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top _), one_mul]

end Generic

section Tuples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {n : ℕ}

/-- `𝒯_n(K)`: the tuples of points of `K` with sum `n c`. -/
def tuples (n : ℕ) (K : Set E) (c : E) : Set (Fin n → E) :=
  {x | (∀ i, x i ∈ K) ∧ ∑ i, x i = (n : ℝ) • c}

omit [MeasurableSpace E] in
lemma tuples_perm (K : Set E) (c : E) (σ : Equiv.Perm (Fin n)) :
    (fun x => x ∘ σ) ⁻¹' (tuples n K c)ᶜ = (tuples n K c)ᶜ := by
  ext x
  simp only [tuples, mem_preimage, mem_compl_iff, mem_ofPred_eq, Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => x i)]
  constructor
  · rintro h ⟨h1, h2⟩; exact h ⟨fun i => h1 (σ i), h2⟩
  · rintro h ⟨h1, h2⟩; exact h ⟨fun i => by simpa using h1 (σ⁻¹ i), h2⟩

variable [BorelSpace E] [FiniteDimensional ℝ E] in
lemma measurableSet_tuples {K : Set E} (hK : MeasurableSet K) (c : E) :
    MeasurableSet (tuples n K c) := by
  have h1 : MeasurableSet {x : Fin n → E | ∀ i, x i ∈ K} := by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i => measurable_pi_apply i hK
  have h2 : MeasurableSet {x : Fin n → E | ∑ i, x i = (n : ℝ) • c} :=
    (measurableSet_singleton _).preimage
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  exact h1.inter h2

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- **Lemma 88 (general form).** Let `F` be a probability measure on `E` with finite mean,
concentrated on a measurable set `K`, and `n ≥ 1`. Then `F` is `n`-completely mixable if and only
if `F = β̄` for a permutation-invariant probability measure `β` on `𝒯_n(K)`, the tuples of points of
`K` with sum `n · mean(F)`. -/
theorem completelyMixable_iff_tuples (hn : 0 < n) {F : Measure E} [IsProbabilityMeasure F]
    (hF : Integrable id F) {K : Set E} (hK : MeasurableSet K) (hFK : F Kᶜ = 0) :
    CompletelyMixable n F ↔ ∃ β : Measure (Fin n → E), IsProbabilityMeasure β ∧
      β (tuples n K (∫ x, x ∂F))ᶜ = 0 ∧ PermInvariant β ∧ marginal β = F := by
  constructor
  · rintro ⟨P, hprob, ⟨s, hs⟩, hmar⟩
    replace hmar : ∀ j, P.map (fun x => x j) = F := hmar
    have hint : ∀ j, Integrable (fun x : Fin n → E => x j) P := fun j => by
      have h := hF
      rw [← hmar j] at h
      exact (integrable_map_measure h.aestronglyMeasurable
        (measurable_pi_apply j).aemeasurable).1 h
    have hsum : s = (n : ℝ) • ∫ x, x ∂F := by
      have h1 : ∫ x, ∑ j, x j ∂P = s := by
        rw [integral_congr_ae hs, integral_const]; simp
      rw [integral_finsetSum _ fun j _ => hint j] at h1
      have h2 : ∀ j, ∫ x, x j ∂P = ∫ x, x ∂F := fun j => by
        have hm : Measurable (fun x : Fin n → E => x j) := measurable_pi_apply j
        rw [← hmar j]
        exact (integral_map hm.aemeasurable aestronglyMeasurable_id).symm
      simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
      rw [← h1, Nat.cast_smul_eq_nsmul]
    have hnull : P (tuples n K (∫ x, x ∂F))ᶜ = 0 := by
      have hsub : (tuples n K (∫ x, x ∂F))ᶜ ⊆
          (⋃ i, (fun x : Fin n → E => x i) ⁻¹' Kᶜ) ∪ {x | ¬ ∑ j, x j = s} := by
        intro x hx
        simp only [tuples, mem_compl_iff, mem_ofPred_eq, not_and_or, not_forall] at hx
        rcases hx with ⟨i, hi⟩ | h
        · exact Or.inl (mem_iUnion.2 ⟨i, hi⟩)
        · exact Or.inr (by rw [hsum]; exact h)
      refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun i => ?_)
        (ae_iff.1 hs))
      rw [← Measure.map_apply (measurable_pi_apply i) hK.compl, hmar i, hFK]
    refine ⟨symmetrise P, symmetrise_isProb P,
      symmetrise_null P (measurableSet_tuples hK _).compl (tuples_perm K _) hnull,
      permInvariant_symmetrise P, ?_⟩
    rw [marginal_eq_of_permInvariant (permInvariant_symmetrise P) ⟨0, hn⟩]
    exact map_eval_symmetrise P hmar _
  · rintro ⟨β, hprob, hnull, hinv, hmar⟩
    refine ⟨β, hprob, ⟨(n : ℝ) • ∫ x, x ∂F, ?_⟩, fun j => ?_⟩
    · have : ∀ᵐ x ∂β, x ∈ tuples n K (∫ x, x ∂F) := by
        rw [ae_iff]; exact hnull
      exact this.mono fun x hx => hx.2
    · rw [← marginal_eq_of_permInvariant hinv j, hmar]

end Tuples

/-! ## Lemma 88 for uniform distributions -/

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {n : ℕ}

lemma unifSet_isProb {K : Set E} (hK : IsCompact K) (hpos : 0 < volume K) :
    IsProbabilityMeasure (unifSet K) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hK.measure_lt_top.ne

lemma unifSet_compl {K : Set E} (hK : MeasurableSet K) : unifSet K Kᶜ = 0 := by
  rw [unifSet, smul_apply, Measure.restrict_apply hK.compl]; simp

lemma unifSet_integrable {K : Set E} (hK : IsCompact K) (hpos : 0 < volume K) :
    Integrable id (unifSet K) :=
  (continuous_id.continuousOn.integrableOn_compact hK).smul_measure
    (ENNReal.inv_ne_top.2 hpos.ne')

/-- The centroid of `K`, the mean of `U(K)`. -/
def centroid (K : Set E) : E := ∫ x, x ∂(unifSet K)

/-- **Lemma 88 (`st:lem:tuples`).** For a compact `K` of positive volume and `n ≥ 1`, `U(K)` is
`n`-completely mixable if and only if `U(K) = β̄` for a probability measure `β` on `𝒯_n(K)`
(the tuples of points of `K` with sum `n c`, `c` the centroid) that is invariant under
permutations. -/
theorem completelyMixable_unif_iff (hn : 0 < n) {K : Set E} (hK : IsCompact K)
    (hpos : 0 < volume K) :
    CompletelyMixable n (unifSet K) ↔ ∃ β : Measure (Fin n → E), IsProbabilityMeasure β ∧
      β (tuples n K (centroid K))ᶜ = 0 ∧ PermInvariant β ∧ marginal β = unifSet K := by
  have := unifSet_isProb hK hpos
  exact completelyMixable_iff_tuples hn (unifSet_integrable hK hpos) hK.measurableSet
    (unifSet_compl hK.measurableSet)

end Uniform

/-! ## Lemma 92: an affine symmetry provides room -/

section SymmSec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- Remark 81: if `L^n = I` and `L` has no eigenvalue `1`, then `∑_{i<n} Lⁱ = 0`. -/
lemma orbit_sum_zero (L : E →L[ℝ] E) (hLn : L ^ n = 1) (hfix : ∀ x, L x = x → x = 0) (x : E) :
    ∑ i : Fin n, (L ^ (i : ℕ)) x = 0 := by
  have h := mul_geom_sum L n
  rw [hLn, sub_self] at h
  have hx := congrArg (fun T : E →L[ℝ] E => T x) h
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, zero_apply,
    sub_eq_zero] at hx
  have := hfix _ hx
  rw [sum_apply] at this
  rw [Fin.sum_univ_eq_sum_range (fun i => (L ^ i) x)]
  exact this

/-- The orbit tuple `(x, Lx, …, L^{n-1}x)`. -/
def orbit (L : E →L[ℝ] E) (x : E) : Fin n → E := fun i => (L ^ (i : ℕ)) x

lemma measurable_orbit (L : E →L[ℝ] E) : Measurable (orbit (n := n) L) :=
  measurable_pi_iff.2 fun i => (L ^ (i : ℕ)).continuous.measurable

lemma marginal_add (β γ : Measure (Fin n → E)) : marginal (β + γ) = marginal β + marginal γ := by
  ext S hS
  simp only [marginal_apply _ hS, add_apply, Finset.sum_add_distrib, mul_add]

lemma marginal_smul (b : ENNReal) (β : Measure (Fin n → E)) :
    marginal (b • β) = b • marginal β := by
  ext S hS
  simp only [marginal_apply _ hS, smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma marginal_univ (hn : 0 < n) (β : Measure (Fin n → E)) : marginal β univ = β univ := by
  rw [marginal_apply _ MeasurableSet.univ]
  simp only [preimage_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, ENNReal.inv_mul_cancel this (ENNReal.natCast_ne_top _), one_mul]

lemma marginal_map_diag (L : E →L[ℝ] E) (β : Measure (Fin n → E)) :
    (marginal β).map L = marginal (β.map (fun x => ⇑L ∘ x)) := by
  have hd : Measurable (fun x : Fin n → E => ⇑L ∘ x) :=
    measurable_pi_iff.2 fun i => L.continuous.measurable.comp (measurable_pi_apply i)
  ext S hS
  rw [Measure.map_apply L.continuous.measurable hS, marginal_apply _ (L.continuous.measurable hS),
    marginal_apply _ hS]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [Measure.map_apply hd (measurable_pi_apply i hS)]; rfl

lemma permInvariant_add {β γ : Measure (Fin n → E)} (hβ : PermInvariant β)
    (hγ : PermInvariant γ) : PermInvariant (β + γ) := fun σ => by
  rw [Measure.map_add _ _ (measurable_perm σ), hβ σ, hγ σ]

lemma permInvariant_smul (b : ENNReal) {β : Measure (Fin n → E)} (hβ : PermInvariant β) :
    PermInvariant (b • β) := fun σ => by
  rw [Measure.map_smul, hβ σ]
  exact (measurable_perm σ).aemeasurable

/-- **Lemma 92 (`st:lem:symm`), measure-theoretic core.** Let `L` be linear with `L^n = I` and
no eigenvalue `1`, mapping `K` into itself (the centroid is `0`), and let `F` be an
`L`-invariant probability measure concentrated on `K` (here `U(K)`). Let `λ` be any finite
measure on `𝒯_n(K)` that is invariant under permutations and under the diagonal action of `L`,
with marginal `λ̄ ≤ M · F` (for the Lebesgue measure on `𝒯_n(K)`, `M = |K|^{n-1}`, from
`a ≤ |K|^{n-2}`). Then there are `b > 0` and a permutation-invariant probability measure `β` on
`𝒯_n(K)` with `β̄ = F` and `β ≥ b λ`. -/
theorem symm_room (hn : 0 < n) (L : E →L[ℝ] E) (hLn : L ^ n = 1)
    (hfix : ∀ x, L x = x → x = 0) {K : Set E} (hK : MeasurableSet K)
    (hLK : ∀ x ∈ K, L x ∈ K) (F : Measure E) [IsProbabilityMeasure F] (hFK : F Kᶜ = 0)
    (hFL : F.map L = F) (lam : Measure (Fin n → E)) [IsFiniteMeasure lam]
    (hlamP : PermInvariant lam) (hlamL : lam.map (fun x => ⇑L ∘ x) = lam)
    (hlamT : lam (tuples n K 0)ᶜ = 0) {M : ENNReal} (hM : M ≠ ⊤) (hmar : marginal lam ≤ M • F) :
    ∃ b : ENNReal, 0 < b ∧ b ≠ ⊤ ∧ ∃ β : Measure (Fin n → E), IsProbabilityMeasure β ∧
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
  have hνF : ν ≤ F := Measure.sub_le
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_of_le F hνF
  have hLm : Measurable L := L.continuous.measurable
  -- invariance of `X` and `ν` under `L`
  have hXL : X.map L = X := by
    rw [hX, Measure.map_smul, marginal_map_diag, hlamL]
    exact hLm.aemeasurable
  have hνL : ν.map L = ν := by
    have h : (ν + X).map L = F.map L := by rw [hνX]
    rw [Measure.map_add _ _ hLm, hXL, hFL, ← hνX] at h
    ext S hS
    have hS' := congrArg (fun μ : Measure E => μ S) h
    simp only [add_apply] at hS'
    exact (ENNReal.add_left_inj (measure_ne_top X S)).1 hS'
  -- the orbit measure
  set γ := ν.map (orbit (n := n) L) with hγ
  have hpowL : ∀ i : ℕ, ν.map ⇑(L ^ i) = ν := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : ⇑(L ^ (i + 1)) = ⇑(L ^ i) ∘ ⇑L := by
        rw [pow_succ]; rfl
      rw [this, ← Measure.map_map (L ^ i).continuous.measurable hLm, hνL, ih]
  have hγmar : ∀ j : Fin n, γ.map (fun x => x j) = ν := fun j => by
    rw [hγ, Measure.map_map (measurable_pi_apply j) (measurable_orbit L)]
    exact hpowL j
  have hpowK : ∀ i : ℕ, ∀ x ∈ K, (L ^ i) x ∈ K := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro x hx; rw [pow_succ]; exact ih _ (hLK x hx)
  have hγT : γ (tuples n K 0)ᶜ = 0 := by
    rw [hγ, Measure.map_apply (measurable_orbit L) (measurableSet_tuples hK 0).compl]
    have hνK : ν Kᶜ = 0 := le_antisymm ((Measure.le_iff'.1 hνF _).trans hFK.le) zero_le
    refine measure_mono_null ?_ hνK
    intro x hx
    by_contra hxK
    apply hx
    refine ⟨fun i => hpowK i x (not_not.1 hxK), ?_⟩
    rw [smul_zero]
    exact orbit_sum_zero L hLn hfix x
  -- the complete mix
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

end SymmSec

/-! ## Lebesgue measure on the tuples -/

section Leb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Replace the coordinate `0` of `y` by `-∑ᵢ yᵢ`. -/
def reflect0 {m : ℕ} (y : Fin (m + 1) → E) : Fin (m + 1) → E := Fin.cons (-∑ i, y i) (Fin.tail y)

/-- `reflect0` preserves the product of an additive Haar measure (Fubini, with the map
`a ↦ -s - a` in the coordinate `0`, which preserves the measure). -/
lemma measurePreserving_reflect0 (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ} :
    MeasurePreserving (reflect0 (m := m)) (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  set ν := Measure.pi fun _ : Fin m => μ
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E) 0
  have hΨ : MeasurePreserving (fun q : (Fin m → E) × E => (q.1, -∑ j, q.1 j - q.2))
      (ν.prod μ) (ν.prod μ) := by
    refine (MeasurePreserving.id ν).skew_product (g := fun r a => -∑ j, r j - a) ?_
      (Filter.Eventually.of_forall fun r => (Measure.measurePreserving_sub_left μ _).map_eq)
    exact ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).neg.comp
      measurable_fst).sub measurable_snd
  have hΦ : MeasurePreserving (fun p : E × (Fin m → E) => (-∑ j, p.2 j - p.1, p.2))
      (μ.prod ν) (μ.prod ν) :=
    (Measure.measurePreserving_swap.comp hΨ).comp Measure.measurePreserving_swap
  have hcomp := (he.symm e).comp (hΦ.comp he)
  convert hcomp using 1
  funext y
  simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    MeasurableEquiv.piFinSuccAbove_apply]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [reflect0, Fin.sum_univ_succ, Fin.insertNthEquiv, Fin.tail]; abel
  · simp [reflect0, Fin.insertNthEquiv, Fin.tail]

/-- `(x₁, …, x_{n-1}) ↦ (x₁, …, x_{n-1}, nc - x₁ - ⋯ - x_{n-1})`, with `n = m + 1`: the
identification of `𝒯_n(K)` with a subset of `E^{n-1}`. -/
def embed {m : ℕ} (c : E) (y : Fin m → E) : Fin (m + 1) → E :=
  Fin.snoc (α := fun _ => E) y (((m + 1 : ℕ) : ℝ) • c - ∑ i, y i)

lemma measurable_embed {m : ℕ} (c : E) : Measurable (embed (m := m) c) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [embed, Fin.snoc_last]
    exact measurable_const.sub (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
  · simp only [embed, Fin.snoc_castSucc]
    exact measurable_pi_apply k

lemma embed_castSucc {m : ℕ} (c : E) (y : Fin m → E) (k : Fin m) :
    embed c y k.castSucc = y k := by simp [embed]

lemma embed_last {m : ℕ} (c : E) (y : Fin m → E) :
    embed c y (Fin.last m) = ((m + 1 : ℕ) : ℝ) • c - ∑ i, y i := by simp [embed]

lemma mem_embed_preimage_tuples {m : ℕ} {K : Set E} {c : E} {y : Fin m → E} :
    y ∈ embed c ⁻¹' tuples (m + 1) K c ↔
      (∀ i, y i ∈ K) ∧ ((m + 1 : ℕ) : ℝ) • c - ∑ i, y i ∈ K := by
  simp only [mem_preimage, tuples, mem_ofPred_eq, Fin.forall_fin_succ', embed_castSucc,
    embed_last, Fin.sum_univ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by abel⟩

/-- The Lebesgue measure `λ` on `𝒯_n(K)`, `n = m + 1`, identified with a subset of `E^{n-1}`
through the first `n - 1` coordinates (`μ` an additive Haar measure on `E`). -/
def lebTuples (μ : Measure E) (m : ℕ) (K : Set E) (c : E) : Measure (Fin (m + 1) → E) :=
  ((Measure.pi fun _ : Fin m => μ).restrict (embed c ⁻¹' tuples (m + 1) K c)).map (embed c)

lemma lebTuples_apply (μ : Measure E) {m : ℕ} (K : Set E) (c : E)
    {S : Set (Fin (m + 1) → E)} (hS : MeasurableSet S) :
    lebTuples μ m K c S = Measure.pi (fun _ : Fin m => μ)
      (embed c ⁻¹' S ∩ embed c ⁻¹' tuples (m + 1) K c) := by
  rw [lebTuples, Measure.map_apply (measurable_embed c) hS,
    Measure.restrict_apply (measurable_embed c hS)]

lemma lebTuples_null (μ : Measure E) {m : ℕ} {K : Set E} (hK : MeasurableSet K) (c : E) :
    lebTuples μ m K c (tuples (m + 1) K c)ᶜ = 0 := by
  rw [lebTuples_apply μ K c (measurableSet_tuples hK c).compl, preimage_compl,
    compl_inter_self, measure_empty]

lemma lebTuples_finite (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ} {K : Set E}
    (hK : IsCompact K) (c : E) : IsFiniteMeasure (lebTuples μ m K c) := by
  constructor
  rw [lebTuples_apply μ K c MeasurableSet.univ, preimage_univ, univ_inter]
  refine lt_of_le_of_lt (measure_mono (t := Set.pi univ fun _ => K) fun y hy => ?_) ?_
  · exact fun i _ => (mem_embed_preimage_tuples.1 hy).1 i
  · rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun i _ => hK.measure_lt_top

lemma lebTuples_diag (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ} {K : Set E}
    (hK : MeasurableSet K) (L : E →L[ℝ] E) (hμL : μ.map L = μ) (hLK : L ⁻¹' K = K) :
    (lebTuples μ m K 0).map (fun x => ⇑L ∘ x) = lebTuples μ m K 0 := by
  have hLm : Measurable L := L.continuous.measurable
  have hd : ∀ k : ℕ, Measurable (fun x : Fin k → E => ⇑L ∘ x) := fun k =>
    measurable_pi_iff.2 fun i => hLm.comp (measurable_pi_apply i)
  set T' := embed (m := m) (0 : E) ⁻¹' tuples (m + 1) K 0 with hT'
  have hT'm : MeasurableSet T' := measurable_embed 0 (measurableSet_tuples hK 0)
  have hcomm : (fun x => ⇑L ∘ x) ∘ embed (m := m) (0 : E) =
      embed (0 : E) ∘ (fun y => ⇑L ∘ y) := by
    funext y
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [embed_last, map_sum]
    · simp [embed_castSucc]
  have hpre : (fun y : Fin m → E => ⇑L ∘ y) ⁻¹' T' = T' := by
    ext y
    have hK' : ∀ x, L x ∈ K ↔ x ∈ K := fun x => by
      rw [← mem_preimage, hLK]
    show (⇑L ∘ y) ∈ embed (0:E) ⁻¹' tuples (m + 1) K 0 ↔
      y ∈ embed (0:E) ⁻¹' tuples (m + 1) K 0
    rw [mem_embed_preimage_tuples, mem_embed_preimage_tuples]
    have : ((m + 1 : ℕ) : ℝ) • (0:E) - ∑ i, (⇑L ∘ y) i =
        L (((m + 1 : ℕ) : ℝ) • (0:E) - ∑ i, y i) := by simp [map_sum]
    rw [this, hK']
    simp only [Function.comp_apply, hK']
  have hpi : (Measure.pi fun _ : Fin m => μ).map (fun y => ⇑L ∘ y) =
      Measure.pi fun _ : Fin m => μ := by
    have : SigmaFinite (μ.map L) := by rw [hμL]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : Fin m => μ) (f := fun _ => ⇑L)
      (fun _ => hLm.aemeasurable)
    simp only [hμL] at this
    exact this
  have hmp : MeasurePreserving (fun y : Fin m → E => ⇑L ∘ y) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => μ) := ⟨hd m, hpi⟩
  have hres := hmp.restrict_preimage hT'm
  rw [hpre] at hres
  rw [lebTuples, Measure.map_map (hd _) (measurable_embed 0), hcomm,
    ← Measure.map_map (measurable_embed 0) (hd m), hres.map_eq]

/-- Each coordinate of `λ` has a density at most `|K|^{n-2}` on `K`: the measure of the tuples
with `xᵢ ∈ S` is at most `|S ∩ K| |K|^{n-2}`. For the last coordinate this uses `reflect0`. -/
lemma lebTuples_coord_le (μ : Measure E) [μ.IsAddHaarMeasure] {k : ℕ} {K : Set E}
    (hK : MeasurableSet K) (i : Fin (k + 2)) {S : Set E} (hS : MeasurableSet S) :
    lebTuples μ (k + 1) K 0 ((fun x => x i) ⁻¹' S) ≤ μ (S ∩ K) * μ K ^ k := by
  rw [lebTuples_apply μ K 0 (measurable_pi_apply i hS)]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · -- the last coordinate: reflect coordinate `0` of `y`
    set P : Set (Fin (k + 1) → E) :=
      Set.pi univ (Fin.cons (S ∩ K) (fun _ : Fin k => K) : Fin (k + 1) → Set E) with hP
    have hsub : embed (0 : E) ⁻¹' ((fun x => x (Fin.last (k + 1))) ⁻¹' S) ∩
        embed 0 ⁻¹' tuples (k + 1 + 1) K 0 ⊆ reflect0 ⁻¹' P := by
      rintro y ⟨hy1, hy2⟩
      rw [mem_embed_preimage_tuples] at hy2
      simp only [mem_preimage, embed_last, smul_zero, zero_sub] at hy1
      simp only [smul_zero, zero_sub] at hy2
      intro l _
      refine Fin.cases ?_ (fun l' => ?_) l
      · simp [reflect0]; exact ⟨hy1, hy2.2⟩
      · simp [reflect0, Fin.tail]; exact hy2.1 _
    have hPm : MeasurableSet P :=
      MeasurableSet.univ_pi fun l => by
        refine Fin.cases ?_ (fun l' => ?_) l
        · simpa using hS.inter hK
        · simpa using hK
    calc _ ≤ Measure.pi (fun _ : Fin (k + 1) => μ) (reflect0 ⁻¹' P) := measure_mono hsub
      _ = Measure.pi (fun _ : Fin (k + 1) => μ) P :=
          (measurePreserving_reflect0 μ).measure_preimage hPm.nullMeasurableSet
      _ = μ (S ∩ K) * μ K ^ k := by
          rw [hP, Measure.pi_pi, Fin.prod_univ_succ]
          simp
  · -- a free coordinate
    set P : Set (Fin (k + 1) → E) :=
      Set.pi univ (Function.update (fun _ => K) j (S ∩ K)) with hP
    have hsub : embed (0 : E) ⁻¹' ((fun x => x j.castSucc) ⁻¹' S) ∩
        embed 0 ⁻¹' tuples (k + 1 + 1) K 0 ⊆ P := by
      rintro y ⟨hy1, hy2⟩
      rw [mem_embed_preimage_tuples] at hy2
      simp only [mem_preimage, embed_castSucc] at hy1
      intro l _
      rcases eq_or_ne l j with h | h
      · subst h; simp; exact ⟨hy1, hy2.1 _⟩
      · simp [h]; exact hy2.1 _
    calc _ ≤ Measure.pi (fun _ : Fin (k + 1) => μ) P := measure_mono hsub
      _ = μ (S ∩ K) * μ K ^ k := by
          rw [hP, Measure.pi_pi]
          have h : ∀ l, μ (Function.update (fun _ => K) j (S ∩ K) l) =
              Function.update (fun _ => μ K) j (μ (S ∩ K)) l := fun l => by
            rcases eq_or_ne l j with h | h
            · subst h; simp
            · simp [h]
          simp_rw [h]
          rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
          simp [Finset.prod_const, Finset.card_sdiff]

lemma lebTuples_marginal_le (μ : Measure E) [μ.IsAddHaarMeasure] {k : ℕ} {K : Set E}
    (hK : IsCompact K) (hpos : 0 < μ K) :
    marginal (lebTuples μ (k + 1) K 0) ≤ (μ K ^ (k + 1)) • ((μ K)⁻¹ • μ.restrict K) := by
  rw [Measure.le_iff]
  intro S hS
  rw [marginal_apply _ hS, smul_apply, smul_apply, Measure.restrict_apply hS, smul_eq_mul,
    smul_eq_mul]
  have hne : μ K ≠ 0 := hpos.ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  calc ((k + 2 : ℕ) : ENNReal)⁻¹ * ∑ i : Fin (k + 2),
        lebTuples μ (k + 1) K 0 ((fun x => x i) ⁻¹' S)
      ≤ ((k + 2 : ℕ) : ENNReal)⁻¹ * ∑ _i : Fin (k + 2), μ (S ∩ K) * μ K ^ k := by
        gcongr with i
        exact lebTuples_coord_le μ hK.measurableSet i hS
    _ = μ (S ∩ K) * μ K ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.succ_ne_zero (k + 1)))
            (ENNReal.natCast_ne_top _), one_mul]
    _ = μ K ^ (k + 1) * ((μ K)⁻¹ * μ (S ∩ K)) := by
        rw [pow_succ, mul_assoc, ← mul_assoc (μ K), ENNReal.mul_inv_cancel hne htop, one_mul,
          mul_comm]

end Leb

section Symmetrise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

lemma marginal_symmetrise (P : Measure (Fin n → E)) : marginal (symmetrise P) = marginal P := by
  ext S hS
  rw [marginal_apply _ hS, marginal_apply _ hS]
  congr 1
  simp_rw [symmetrise_apply P (measurable_pi_apply _ hS)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have : ∀ σ : Equiv.Perm (Fin n), ∑ i : Fin n, P ((fun x => x ∘ σ) ⁻¹' ((fun x => x i) ⁻¹' S))
      = ∑ i : Fin n, P ((fun x => x i) ⁻¹' S) := fun σ =>
    Fintype.sum_equiv σ _ _ fun i => rfl
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  rw [ENNReal.inv_mul_cancel card_perm_ne_zero (ENNReal.natCast_ne_top _), one_mul]

lemma symmetrise_diag (L : E →L[ℝ] E) (P : Measure (Fin n → E)) :
    (symmetrise P).map (fun x => ⇑L ∘ x) = symmetrise (P.map (fun x => ⇑L ∘ x)) := by
  have hd : Measurable (fun x : Fin n → E => ⇑L ∘ x) :=
    measurable_pi_iff.2 fun i => L.continuous.measurable.comp (measurable_pi_apply i)
  ext S hS
  rw [Measure.map_apply hd hS, symmetrise_apply _ (hd hS), symmetrise_apply _ hS]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by
    rw [Measure.map_apply hd (measurable_perm σ hS)]; rfl

lemma le_symmetrise (P : Measure (Fin n → E)) :
    (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹ • P ≤ symmetrise P := by
  rw [Measure.le_iff]
  intro S hS
  rw [smul_apply, smul_eq_mul, symmetrise_apply P hS]
  gcongr
  exact Finset.single_le_sum (f := fun σ : Equiv.Perm (Fin n) => P ((fun x => x ∘ σ) ⁻¹' S))
    (fun _ _ => zero_le) (Finset.mem_univ 1)

end Symmetrise


/-! ## Lemma 92 for the uniform distribution and the Lebesgue measure on the tuples -/

section SymmConcrete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- `L^n = I` forces `|det L| = 1`, so `L` preserves Lebesgue measure. -/
lemma volume_map_eq (L : E →L[ℝ] E) {n : ℕ} (hn : 0 < n) (hLn : L ^ n = 1) :
    (volume : Measure E).map L = volume := by
  have hdet : |LinearMap.det (L : E →ₗ[ℝ] E)| = 1 := by
    have h : (LinearMap.det (L : E →ₗ[ℝ] E)) ^ n = 1 := by
      rw [← map_pow, ← ContinuousLinearMap.toLinearMap_pow, hLn]
      simp
    have := congrArg abs h
    rw [abs_pow, abs_one] at this
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hn.ne').1 this
  have hne : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := by
    intro h; rw [h, abs_zero] at hdet; norm_num at hdet
  rw [show (⇑L : E → E) = ⇑(L : E →ₗ[ℝ] E) from rfl,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, abs_inv, hdet]
  simp

lemma unifSet_map (L : E →L[ℝ] E) (hvol : (volume : Measure E).map L = volume) {K : Set E}
    (hK : MeasurableSet K) (hLK : L ⁻¹' K = K) : (unifSet K).map L = unifSet K := by
  have hLm : Measurable L := L.continuous.measurable
  rw [unifSet, Measure.map_smul]
  congr 1
  ext S hS
  rw [Measure.map_apply hLm hS, Measure.restrict_apply (hLm hS), Measure.restrict_apply hS]
  conv_lhs => rw [← hLK]
  rw [← preimage_inter, ← Measure.map_apply hLm (hS.inter hK), hvol]
  exact hLm.aemeasurable

/-- As in Remark 81, `L` fixes the centroid, which is therefore `0`. -/
lemma centroid_eq_zero (L : E →L[ℝ] E) (hfix : ∀ x, L x = x → x = 0) {K : Set E}
    (hK : IsCompact K) (hpos : 0 < volume K) (hU : (unifSet K).map L = unifSet K) :
    centroid K = 0 := by
  apply hfix
  have hint := unifSet_integrable hK hpos
  calc L (centroid K) = ∫ x, L x ∂(unifSet K) := (L.integral_comp_comm hint).symm
    _ = ∫ x, x ∂((unifSet K).map L) :=
        (integral_map L.continuous.measurable.aemeasurable aestronglyMeasurable_id).symm
    _ = centroid K := by rw [hU]; rfl

/-- **Lemma 92 (`st:lem:symm`).** Let `n = k + 2 ≥ 2`, let `K` be compact with positive volume
and let `L` be linear with `L^n = I`, no eigenvalue `1`, mapping `K` onto itself
(`L⁻¹(K) = K`); this is the paper's affine map `A` after translating its fixed point to `0`.
Then the centroid of `K` is `0`, and there are `b > 0` and a permutation-invariant probability
measure `β` on `𝒯_n(K)` with `β̄ = U(K)` and `β ≥ b λ` on all of `𝒯_n(K)`, `λ` the Lebesgue
measure on `𝒯_n(K)` through the first `n - 1` coordinates. In particular `U(K)` is robustly
`n`-completely mixable (Definition 90). -/
theorem symm_robust {k : ℕ} (L : E →L[ℝ] E) (hLn : L ^ (k + 2) = 1)
    (hfix : ∀ x, L x = x → x = 0) {K : Set E} (hK : IsCompact K) (hpos : 0 < volume K)
    (hLK : L ⁻¹' K = K) :
    centroid K = 0 ∧ ∃ b : ENNReal, 0 < b ∧ b ≠ ⊤ ∧ ∃ β : Measure (Fin (k + 2) → E),
      IsProbabilityMeasure β ∧ β (tuples (k + 2) K (centroid K))ᶜ = 0 ∧ PermInvariant β ∧
      marginal β = unifSet K ∧ b • lebTuples volume (k + 1) K (centroid K) ≤ β := by
  have hvol := volume_map_eq L (by omega : 0 < k + 2) hLn
  have hU := unifSet_map L hvol hK.measurableSet hLK
  have hc := centroid_eq_zero L hfix hK hpos hU
  refine ⟨hc, ?_⟩
  rw [hc]
  have := unifSet_isProb hK hpos
  set lam0 := lebTuples (volume : Measure E) (k + 1) K 0 with hlam0
  have := lebTuples_finite (volume : Measure E) (m := k + 1) hK 0
  set N : ENNReal := (Fintype.card (Equiv.Perm (Fin (k + 2))) : ENNReal) with hN
  set lam := symmetrise lam0 with hlam
  have hlamfin : IsFiniteMeasure lam := by
    constructor
    rw [hlam, symmetrise_apply _ MeasurableSet.univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by
      rw [pos_iff_ne_zero]; exact card_perm_ne_zero))
      (ENNReal.sum_lt_top.2 fun σ _ => measure_lt_top _ _)
  have hlamL : lam.map (fun x => ⇑L ∘ x) = lam := by
    rw [hlam, symmetrise_diag, hlam0, lebTuples_diag volume hK.measurableSet L hvol hLK]
  have hlamT : lam (tuples (k + 2) K 0)ᶜ = 0 :=
    symmetrise_null _ (measurableSet_tuples hK.measurableSet 0).compl (tuples_perm K 0)
      (lebTuples_null _ hK.measurableSet 0)
  have hmar : marginal lam ≤ (volume K ^ (k + 1)) • unifSet K := by
    rw [hlam, marginal_symmetrise]
    exact lebTuples_marginal_le volume hK hpos
  have hLK' : ∀ x ∈ K, L x ∈ K := fun x hx => by
    have : x ∈ L ⁻¹' K := by rw [hLK]; exact hx
    exact this
  obtain ⟨b, hb, hbt, β, h1, h2, h3, h4, h5⟩ := symm_room (n := k + 2) (by omega) L hLn hfix
    hK.measurableSet hLK' (unifSet K) (unifSet_compl hK.measurableSet) hU lam
    (permInvariant_symmetrise lam0) hlamL hlamT
    (ENNReal.pow_ne_top hK.measure_lt_top.ne) hmar
  refine ⟨b * N⁻¹, ENNReal.mul_pos hb.ne' (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)),
    ENNReal.mul_ne_top hbt (ENNReal.inv_ne_top.2 card_perm_ne_zero), β, h1, h2, h3, h4, ?_⟩
  refine le_trans ?_ h5
  rw [Measure.le_iff]
  intro S hS
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  gcongr
  have := Measure.le_iff.1 (le_symmetrise lam0) S hS
  rwa [smul_apply, smul_eq_mul] at this

end SymmConcrete

/-! ## The planar equality case of Lemma 89 as a statement about sets

For a compact convex `K ⊂ ℝ²` of positive area: slices, chord ends `lo`, `hi` (convex and
concave), Fubini for the projection (`integral_fst`, `volume_eq`), the one-dimensional
inequality `mean_third_ge` with its equality case, the triangle from affine chord ends
(`isTriangle_of_chordLen`), the coordinate core `fst_core`, its transfer to every direction by
a rotation (`dir_core`), and `planar_asym`: `as(K) ≤ 2`, with `as(K) < 2` unless `K` is a
triangle (maximum over the directions by compactness). -/

open Filter Topology

section PlanarBody

/-- The slice `{y : (s, y) ∈ K}` of a planar set at the level `s` (first coordinate). -/
def slice (K : Set (ℝ × ℝ)) (s : ℝ) : Set ℝ := Prod.mk s ⁻¹' K

/-- Lower and upper end of the chord at the level `s`. -/
def lo (K : Set (ℝ × ℝ)) (s : ℝ) : ℝ := sInf (slice K s)
def hi (K : Set (ℝ × ℝ)) (s : ℝ) : ℝ := sSup (slice K s)

variable {K : Set (ℝ × ℝ)}

lemma isCompact_slice (hK : IsCompact K) (s : ℝ) : IsCompact (slice K s) := by
  refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage (by fun_prop)) ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0:ℝ)) (r := R)).subset fun y hy => ?_
  have := hR hy
  simp only [mem_closedBall, dist_zero_right] at this ⊢
  exact (norm_snd_le (s, y)).trans this

lemma convex_slice (hKc : Convex ℝ K) (s : ℝ) : Convex ℝ (slice K s) := by
  intro y hy z hz a b ha hb hab
  have := hKc hy hz ha hb hab
  simp only [slice, mem_preimage, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this ⊢
  rwa [← add_mul, hab, one_mul] at this

lemma slice_eq_Icc (hKc : Convex ℝ K) (hK : IsCompact K) {s : ℝ} (hs : (slice K s).Nonempty) :
    slice K s = Icc (lo K s) (hi K s) := by
  have hc := isCompact_slice hK s
  refine Subset.antisymm (fun y hy => ⟨csInf_le hc.bddBelow hy, le_csSup hc.bddAbove hy⟩) ?_
  exact (convex_slice hKc s).ordConnected.out (hc.sInf_mem hs) (hc.sSup_mem hs)

lemma lo_mem (hK : IsCompact K) {s : ℝ} (hs : (slice K s).Nonempty) : (s, lo K s) ∈ K :=
  (isCompact_slice hK s).sInf_mem hs

lemma hi_mem (hK : IsCompact K) {s : ℝ} (hs : (slice K s).Nonempty) : (s, hi K s) ∈ K :=
  (isCompact_slice hK s).sSup_mem hs

/-- The projection of `K` on the first coordinate. -/
def projLo (K : Set (ℝ × ℝ)) : ℝ := sInf (Prod.fst '' K)
def projHi (K : Set (ℝ × ℝ)) : ℝ := sSup (Prod.fst '' K)

lemma slice_nonempty (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) {s : ℝ}
    (hs : s ∈ Icc (projLo K) (projHi K)) : (slice K s).Nonempty := by
  have hc : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hcv : Convex ℝ (Prod.fst '' K) := hKc.linear_image (LinearMap.fst ℝ ℝ ℝ)
  have := hcv.ordConnected.out (hc.sInf_mem (hne.image _)) (hc.sSup_mem (hne.image _)) hs
  obtain ⟨x, hx, rfl⟩ := this
  exact ⟨x.2, by simpa [slice] using hx⟩

lemma fst_mem_Icc {x : ℝ × ℝ} (hK : IsCompact K) (hx : x ∈ K) :
    x.1 ∈ Icc (projLo K) (projHi K) :=
  ⟨csInf_le (hK.image continuous_fst).bddBelow ⟨x, hx, rfl⟩,
    le_csSup (hK.image continuous_fst).bddAbove ⟨x, hx, rfl⟩⟩

lemma slice_empty (hK : IsCompact K) {s : ℝ} (hs : s ∉ Icc (projLo K) (projHi K)) :
    slice K s = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hy => hs (fst_mem_Icc hK hy)

lemma hi_concave (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) :
    ConcaveOn ℝ (Icc (projLo K) (projHi K)) (hi K) := by
  refine ⟨convex_Icc _ _, fun s hs t ht a b ha hb hab => ?_⟩
  have h := hKc (hi_mem hK (slice_nonempty hKc hK hne hs))
    (hi_mem hK (slice_nonempty hKc hK hne ht)) ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h ⊢
  exact le_csSup (isCompact_slice hK _).bddAbove h

lemma lo_convex (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) :
    ConvexOn ℝ (Icc (projLo K) (projHi K)) (lo K) := by
  refine ⟨convex_Icc _ _, fun s hs t ht a b ha hb hab => ?_⟩
  have h := hKc (lo_mem hK (slice_nonempty hKc hK hne hs))
    (lo_mem hK (slice_nonempty hKc hK hne ht)) ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h ⊢
  exact csInf_le (isCompact_slice hK _).bddBelow h

/-- The chord length at the level `s`. -/
def chordLen (K : Set (ℝ × ℝ)) (s : ℝ) : ℝ := hi K s - lo K s

lemma chordLen_concave (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) :
    ConcaveOn ℝ (Icc (projLo K) (projHi K)) (chordLen K) :=
  (hi_concave hKc hK hne).sub (lo_convex hKc hK hne)

lemma chordLen_nonneg (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) {s : ℝ}
    (hs : s ∈ Icc (projLo K) (projHi K)) : 0 ≤ chordLen K s := by
  have h := slice_nonempty hKc hK hne hs
  obtain ⟨y, hy⟩ := h
  rw [slice_eq_Icc hKc hK ⟨y, hy⟩] at hy
  unfold chordLen; linarith [hy.1, hy.2]

lemma volume_slice (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) (s : ℝ) :
    volume (slice K s) = (Icc (projLo K) (projHi K)).indicator
      (fun s => ENNReal.ofReal (chordLen K s)) s := by
  by_cases hs : s ∈ Icc (projLo K) (projHi K)
  · rw [indicator_of_mem hs, slice_eq_Icc hKc hK (slice_nonempty hKc hK hne hs), Real.volume_Icc]
    rfl
  · rw [indicator_of_notMem hs, slice_empty hK hs, measure_empty]

/-- **Fubini for a planar convex body.** For every continuous `φ`, `∫_K φ(x₁) dx` equals
`∫ φ(s) g(s) ds` over the projection, with `g` the chord length. -/
lemma integral_fst (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) {φ : ℝ → ℝ}
    (hφ : Continuous φ) :
    ∫ x in K, φ x.1 = ∫ s in Icc (projLo K) (projHi K), φ s * chordLen K s := by
  have hint : Integrable (K.indicator fun x : ℝ × ℝ => φ x.1) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, integrable_indicator_iff hK.measurableSet]
    exact (hφ.comp continuous_fst).continuousOn.integrableOn_compact hK
  rw [← integral_indicator hK.measurableSet, Measure.volume_eq_prod, integral_prod _ hint,
    ← integral_indicator measurableSet_Icc]
  congr 1; funext s
  have : (fun y => K.indicator (fun x : ℝ × ℝ => φ x.1) (s, y)) =
      (slice K s).indicator fun _ => φ s := by
    funext y; by_cases hy : (s, y) ∈ K
    · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ slice K s from hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show y ∉ slice K s from hy)]
  rw [this, integral_indicator_const _ ((isCompact_slice hK s).measurableSet), smul_eq_mul,
    Measure.real, volume_slice hKc hK hne]
  by_cases hs : s ∈ Icc (projLo K) (projHi K)
  · rw [indicator_of_mem hs, indicator_of_mem hs, ENNReal.toReal_ofReal
      (chordLen_nonneg hKc hK hne hs), mul_comm]
  · rw [indicator_of_notMem hs, indicator_of_notMem hs]; simp

lemma volume_eq (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) :
    volume K = ∫⁻ s in Icc (projLo K) (projHi K), ENNReal.ofReal (chordLen K s) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply hK.measurableSet,
    ← lintegral_indicator measurableSet_Icc]
  congr 1; funext s
  exact volume_slice hKc hK hne s

end PlanarBody

section MeanThird

variable {g : ℝ → ℝ} {m M : ℝ}

lemma poly_integral' (m M : ℝ) :
    ∫ s in Icc m M, (s - (2 * m + M) / 3) * (M - s) = 0 := by
  rcases le_or_gt m M with hmM | hmM
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hmM]
    set p := (2 * m + M) / 3
    have : ∀ x ∈ uIcc m M, HasDerivAt
        (fun s : ℝ => -1 / 3 * s ^ 3 + (p + M) / 2 * s ^ 2 - p * M * s) ((x - p) * (M - x)) x := by
      intro x _
      have := (((hasDerivAt_pow 3 x).const_mul (-1 / 3)).add
        ((hasDerivAt_pow 2 x).const_mul ((p + M) / 2))).sub ((hasDerivAt_id x).const_mul (p * M))
      convert this using 1
      · funext s; simp only [Pi.add_apply, Pi.sub_apply, id]
      · ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
      ((by fun_prop : Continuous fun x : ℝ => (x - p) * (M - x)).intervalIntegrable _ _)]
    simp only [p]; ring
  · rw [Icc_eq_empty (not_le.2 hmM)]; simp

/-- **One-dimensional Grünbaum inequality.** A density proportional to a nonnegative concave
`g` on `[m, M]` has mean at least `m + (M - m)/3`, i.e. `∫ (s - p) g(s) ds ≥ 0` for
`p = (2m + M)/3`; and if equality holds, `g(s) = κ (M - s)` on `(m, M)`. -/
theorem mean_third_ge (hmM : m < M) (hg : ConcaveOn ℝ (Icc m M) g)
    (h0 : ∀ x ∈ Icc m M, 0 ≤ g x) (hint : IntegrableOn g (Icc m M)) :
    0 ≤ ∫ s in Icc m M, (s - (2 * m + M) / 3) * g s ∧
      ((∫ s in Icc m M, (s - (2 * m + M) / 3) * g s) = 0 →
        ∀ s ∈ Ioo m M, g s = g ((2 * m + M) / 3) / (M - (2 * m + M) / 3) * (M - s)) := by
  set p := (2 * m + M) / 3 with hp
  have hpm : m < p := by rw [hp]; linarith
  have hpM : p < M := by rw [hp]; linarith
  set κ := g p / (M - p) with hκ
  have hMp : 0 < M - p := by linarith
  set φ : ℝ → ℝ := fun s => (s - p) * (g s - κ * (M - s)) with hφ
  have gM : 0 ≤ g M := h0 M ⟨hmM.le, le_rfl⟩
  have pI : p ∈ Icc m M := ⟨hpm.le, hpM.le⟩
  have MI : M ∈ Icc m M := ⟨hmM.le, le_rfl⟩
  -- chord inequality: for `x ≤ y ≤ M` in `[m, M]`, `g x (M - y) ≤ g y (M - x)`
  have chord : ∀ x ∈ Icc m M, ∀ y, x ≤ y → y ≤ M → g x * (M - y) ≤ g y * (M - x) := by
    intro x hx y hxy hyM
    rcases eq_or_lt_of_le (hxy.trans hyM) with hxM | hxM
    · subst hxM; have : y = x := le_antisymm hyM hxy
      subst this; simp
    have hpos : 0 < M - x := by linarith
    have key := hg.2 hx MI (show 0 ≤ (M - y) / (M - x) from div_nonneg (by linarith) hpos.le)
      (show 0 ≤ (y - x) / (M - x) from div_nonneg (by linarith) hpos.le) (by field_simp; ring)
    have hpt : ((M - y) / (M - x)) • x + ((y - x) / (M - x)) • M = y := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt] at key
    simp only [smul_eq_mul] at key
    have hb : 0 ≤ (y - x) / (M - x) * g M := mul_nonneg (div_nonneg (by linarith) hpos.le) gM
    have key' : (M - y) / (M - x) * g x ≤ g y := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at key'
    linarith
  have hφnn : ∀ s ∈ Icc m M, 0 ≤ φ s := by
    intro s hs
    simp only [hφ]
    rcases le_total s p with h | h
    · have := chord s hs p h hpM.le
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      rw [hκ, sub_nonpos, div_mul_eq_mul_div, le_div_iff₀ hMp]; linarith
    · have := chord p pI s h hs.2
      apply mul_nonneg (by linarith)
      rw [hκ, sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hMp]; linarith
  have hpoly : IntegrableOn (fun s : ℝ => κ * ((s - p) * (M - s))) (Icc m M) :=
    (by fun_prop : Continuous fun s : ℝ => κ * ((s - p) * (M - s))).integrableOn_Icc
  have hsg : IntegrableOn (fun s => (s - p) * g s) (Icc m M) :=
    hint.continuousOn_mul (by fun_prop) isCompact_Icc
  have hφeq : φ = fun s => (s - p) * g s - κ * ((s - p) * (M - s)) := by
    funext s; simp only [hφ]; ring
  have hφint : IntegrableOn φ (Icc m M) := by rw [hφeq]; exact hsg.sub hpoly
  have hI : ∫ s in Icc m M, φ s = ∫ s in Icc m M, (s - p) * g s := by
    rw [hφeq, integral_sub hsg hpoly, integral_const_mul, hp, poly_integral']; ring
  have hge : 0 ≤ ∫ s in Icc m M, φ s := setIntegral_nonneg measurableSet_Icc hφnn
  refine ⟨hI ▸ hge, fun h0' => ?_⟩
  rw [← hI] at h0'
  have hae : φ =ᵐ[volume.restrict (Icc m M)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hφnn)) hφint).1 h0'
  have hae' : φ =ᵐ[volume.restrict (Ioo m M)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hae
  have hcont : ContinuousOn φ (Ioo m M) := by
    have hgc : ContinuousOn g (Ioo m M) := by
      simpa [interior_Icc] using hg.continuousOn_interior
    exact ((continuousOn_id.sub continuousOn_const).mul
      (hgc.sub (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))))
  have hEq := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hcont continuousOn_const
  intro s hs
  have := hEq hs
  simp only [hφ, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h | h
  · have : s = p := by linarith
    subst this; rw [hκ]; field_simp
  · linarith

end MeanThird

section Core

variable {K : Set (ℝ × ℝ)}

lemma interp_le {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) {x y z : ℝ} (hx : x ∈ I)
    (hz : z ∈ I) (hxy : x ≤ y) (hyz : y ≤ z) : f y * (z - x) ≤ f x * (z - y) + f z * (y - x) := by
  rcases eq_or_lt_of_le (hxy.trans hyz) with hxz | hxz
  · subst hxz; have : y = x := le_antisymm hyz hxy
    subst this; simp
  have hpos : 0 < z - x := by linarith
  have key := hf.2 hx hz (show 0 ≤ (z - y) / (z - x) from div_nonneg (by linarith) hpos.le)
    (show 0 ≤ (y - x) / (z - x) from div_nonneg (by linarith) hpos.le) (by field_simp; ring)
  have hpt : ((z - y) / (z - x)) • x + ((y - x) / (z - x)) • z = y := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hpt] at key
  simp only [smul_eq_mul] at key
  have e : f y ≤ ((z - y) * f x + (y - x) * f z) / (z - x) := by
    rw [add_div, mul_div_right_comm, mul_div_right_comm]; linarith
  rw [le_div_iff₀ hpos] at e; linarith

lemma le_interp {f : ℝ → ℝ} {I : Set ℝ} (hf : ConcaveOn ℝ I f) {x y z : ℝ} (hx : x ∈ I)
    (hz : z ∈ I) (hxy : x ≤ y) (hyz : y ≤ z) : f x * (z - y) + f z * (y - x) ≤ f y * (z - x) := by
  have := interp_le hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this; linarith

/-- `K` is a triangle (possibly degenerate): the convex hull of three points. -/
def IsTriangle (K : Set (ℝ × ℝ)) : Prop := ∃ A B C : ℝ × ℝ, K = convexHull ℝ {A, B, C}

lemma mem_hull3 {A B C : ℝ × ℝ} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : a • A + b • B + c • C ∈ convexHull ℝ {A, B, C} := by
  have := (convex_convexHull ℝ ({A, B, C} : Set (ℝ × ℝ))).sum_mem (t := Finset.univ)
    (w := ![a, b, c]) (z := ![A, B, C]) (by intro i _; fin_cases i <;> simp [ha, hb, hc])
    (by simp [Fin.sum_univ_three, h]) (by
      intro i _; apply subset_convexHull; fin_cases i <;> simp)
  simpa [Fin.sum_univ_three] using this

/-- **Affine chord ends make a triangle.** If the chord length of a compact convex planar `K`
is `κ (M - s)` with `κ > 0` on the open projection `(m, M)`, then `K` is a triangle. -/
theorem isTriangle_of_chordLen (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty)
    (hmM : projLo K < projHi K) {κ : ℝ} (hκ : 0 < κ)
    (hg : ∀ s ∈ Ioo (projLo K) (projHi K), chordLen K s = κ * (projHi K - s)) :
    IsTriangle K := by
  set m := projLo K with hm
  set M := projHi K with hM
  have Isub : Ioo m M ⊆ Icc m M := Ioo_subset_Icc_self
  have hloC : ConvexOn ℝ (Ioo m M) (lo K) := (lo_convex hKc hK hne).subset Isub (convex_Ioo _ _)
  have hhiC : ConcaveOn ℝ (Ioo m M) (hi K) := (hi_concave hKc hK hne).subset Isub (convex_Ioo _ _)
  have hhi : ∀ s ∈ Ioo m M, hi K s = lo K s + κ * (M - s) := fun s hs => by
    have := hg s hs; unfold chordLen at this; linarith
  -- `lo` is affine on `(m, M)`
  have interp : ∀ x ∈ Ioo m M, ∀ y z, z ∈ Ioo m M → x ≤ y → y ≤ z →
      lo K y * (z - x) = lo K x * (z - y) + lo K z * (y - x) := by
    intro x hx y z hz hxy hyz
    have hy : y ∈ Ioo m M := ⟨hx.1.trans_le hxy, hyz.trans_lt hz.2⟩
    have h1 := interp_le hloC hx hz hxy hyz
    have h2 := le_interp hhiC hx hz hxy hyz
    rw [hhi x hx, hhi y hy, hhi z hz] at h2
    nlinarith
  set a₁ := (2 * m + M) / 3
  set a₂ := (m + 2 * M) / 3
  have ha₁ : a₁ ∈ Ioo m M := ⟨by simp only [a₁]; linarith, by simp only [a₁]; linarith⟩
  have ha₂ : a₂ ∈ Ioo m M := ⟨by simp only [a₂]; linarith, by simp only [a₂]; linarith⟩
  have h12 : 0 < a₂ - a₁ := by simp only [a₁, a₂]; linarith
  set L : ℝ → ℝ := fun s => (lo K a₁ * (a₂ - s) - lo K a₂ * (a₁ - s)) / (a₂ - a₁) with hL
  have hLc : Continuous L := by simp only [hL]; fun_prop
  have hlo : ∀ s ∈ Ioo m M, lo K s = L s := by
    intro s hs
    simp only [hL]; rw [eq_div_iff h12.ne']
    rcases le_total s a₁ with h | h
    · have := interp s hs a₁ a₂ ha₂ h (by simp only [a₁, a₂]; linarith); linarith
    rcases le_total s a₂ with h' | h'
    · have := interp a₁ ha₁ s a₂ ha₂ h h'; linarith
    · have := interp a₁ ha₁ a₂ s hs (by simp only [a₁, a₂]; linarith) h'; linarith
  set A : ℝ × ℝ := (m, L m)
  set B : ℝ × ℝ := (m, L m + κ * (M - m))
  set C : ℝ × ℝ := (M, L M)
  refine ⟨A, B, C, Subset.antisymm ?_ ?_⟩
  · -- `K ⊆ T`
    set T := convexHull ℝ ({A, B, C} : Set (ℝ × ℝ))
    have hT : IsClosed T := ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)).isClosed
    have inner : ∀ x ∈ K, x.1 ∈ Ioo m M → x ∈ T := by
      intro x hx hs
      have hsl : x.2 ∈ slice K x.1 := by simpa [slice] using hx
      rw [slice_eq_Icc hKc hK ⟨_, hsl⟩] at hsl
      have hl := hsl.1; have hu := hsl.2
      rw [hlo _ hs] at hl
      rw [hhi _ hs, hlo _ hs] at hu
      have hMm : 0 < M - m := by linarith
      set t := (x.1 - m) / (M - m)
      set b := (x.2 - L x.1) / (κ * (M - m))
      have ht0 : 0 ≤ t := div_nonneg (by linarith [hs.1]) hMm.le
      have hb0 : 0 ≤ b := div_nonneg (by linarith) (by positivity)
      have ha0 : 0 ≤ 1 - t - b := by
        simp only [t, b]
        rw [sub_sub, sub_nonneg]
        have : (x.1 - m) / (M - m) + (x.2 - L x.1) / (κ * (M - m)) =
            ((x.1 - m) * κ + (x.2 - L x.1)) / (κ * (M - m)) := by field_simp
        rw [this, div_le_one (by positivity)]; nlinarith
      have := mem_hull3 (A := A) (B := B) (C := C) ha0 hb0 ht0 (by ring)
      convert this using 1
      simp only [A, B, C, t, b, hL, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      ext
      · simp only; field_simp; ring
      · simp only; field_simp; ring
    intro x hx
    have hx1 : x.1 ∈ Icc m M := fst_mem_Icc hK hx
    set z : ℝ × ℝ := (a₁, lo K a₁)
    have hz : z ∈ K := lo_mem hK (slice_nonempty hKc hK hne (Isub ha₁))
    refine hT.mem_of_tendsto (f := fun t : ℝ => x + t • (z - x)) (b := 𝓝[>] (0:ℝ)) ?_ ?_
    · have : Continuous fun t : ℝ => x + t • (z - x) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 from one_pos)] with t ht
      have hw : x + t • (z - x) ∈ K := by
        have := hKc hx hz (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le (by ring)
        convert this using 1; module
      refine inner _ hw ⟨?_, ?_⟩
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, z]
        nlinarith [mul_pos ht.1 (sub_pos.2 ha₁.1),
          mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hx1.1)]
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, z]
        nlinarith [mul_pos ht.1 (sub_pos.2 ha₁.2),
          mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hx1.2)]
  · -- `T ⊆ K`
    refine convexHull_min ?_ hKc
    have tend : ∀ (F : Filter ℝ) [F.NeBot] (a : ℝ) (f : ℝ → ℝ), Continuous f →
        F ≤ 𝓝 a → (∀ᶠ s in F, s ∈ Ioo m M) → (∀ s ∈ Ioo m M, (s, f s) ∈ K) → (a, f a) ∈ K := by
      intro F _ a f hf hF hev hmem
      refine hK.isClosed.mem_of_tendsto (f := fun s => (s, f s)) (b := F) ?_ ?_
      · exact ((continuous_id.prodMk hf).tendsto a).mono_left hF
      · filter_upwards [hev] with s hs using hmem s hs
    have hlomem : ∀ s ∈ Ioo m M, (s, L s) ∈ K := fun s hs => by
      rw [← hlo s hs]; exact lo_mem hK (slice_nonempty hKc hK hne (Isub hs))
    have himem : ∀ s ∈ Ioo m M, (s, L s + κ * (M - s)) ∈ K := fun s hs => by
      rw [← hlo s hs, ← hhi s hs]; exact hi_mem hK (slice_nonempty hKc hK hne (Isub hs))
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact tend (𝓝[>] m) m L hLc nhdsWithin_le_nhds (Ioo_mem_nhdsGT hmM) hlomem
    · exact tend (𝓝[>] m) m (fun s => L s + κ * (M - s)) (by fun_prop) nhdsWithin_le_nhds
        (Ioo_mem_nhdsGT hmM) himem
    · exact tend (𝓝[<] M) M L hLc nhdsWithin_le_nhds (Ioo_mem_nhdsLT hmM) hlomem

lemma chordLen_integrableOn (hKc : Convex ℝ K) (hK : IsCompact K) (hne : K.Nonempty) :
    IntegrableOn (chordLen K) (Icc (projLo K) (projHi K)) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hb : ∀ x ∈ K, |x.2| ≤ R := fun x hx => by
    have := hR hx
    simp only [mem_closedBall, dist_zero_right] at this
    exact (norm_snd_le x).trans this
  have hcont : ContinuousOn (chordLen K) (Ioo (projLo K) (projHi K)) := by
    simpa [interior_Icc] using (chordLen_concave hKc hK hne).continuousOn_interior
  refine IntegrableOn.of_bound measure_Icc_lt_top ?_ (2 * R) ?_
  · rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have h1 := hb _ (hi_mem hK (slice_nonempty hKc hK hne hs))
    have h2 := hb _ (lo_mem hK (slice_nonempty hKc hK hne hs))
    rw [Real.norm_eq_abs, abs_le] at *
    unfold chordLen; constructor <;> linarith

/-- **Coordinate core of the planar case.** Let `K ⊂ ℝ²` be compact and convex with positive
area, projecting onto `[m, M]` along the second coordinate, with centroid `c`. Then `m < M`,
`c₁ - m ≥ (M - m)/3`, and equality forces `K` to be a triangle. -/
theorem fst_core (hKc : Convex ℝ K) (hK : IsCompact K) (hvol : 0 < volume K) :
    projLo K < projHi K ∧ (projHi K - projLo K) / 3 ≤ (centroid K).1 - projLo K ∧
      ((centroid K).1 - projLo K = (projHi K - projLo K) / 3 → IsTriangle K) := by
  have hne : K.Nonempty := nonempty_of_measure_ne_zero hvol.ne'
  set m := projLo K with hm
  set M := projHi K with hM
  set g := chordLen K
  have hgi := chordLen_integrableOn hKc hK hne
  have hfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  set V := ∫ s in Icc m M, g s with hV
  have hVK : (volume K).toReal = V := by
    have := integral_fst hKc hK hne (φ := fun _ => (1:ℝ)) continuous_const
    simp only [one_mul, integral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, mul_one, Measure.real] at this
    exact this
  have hVpos : 0 < V := by rw [← hVK]; exact ENNReal.toReal_pos hvol.ne' hfin
  have hmM : m < M := by
    by_contra h
    have : volume (Icc m M) = 0 := by
      rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
    rw [hV, Measure.restrict_eq_zero.2 this, integral_zero_measure] at hVpos
    exact lt_irrefl _ hVpos
  have hidK : Integrable id (volume.restrict K) :=
    continuous_id.continuousOn.integrableOn_compact hK
  have hc1 : (centroid K).1 * V = ∫ s in Icc m M, s * g s := by
    refine Eq.trans ?_ (integral_fst hKc hK hne (φ := fun s => s) continuous_id)
    have e := (ContinuousLinearMap.fst ℝ ℝ ℝ).integral_comp_comm hidK
    simp only [ContinuousLinearMap.coe_fst', id] at e
    rw [centroid, unifSet, integral_smul_measure, Prod.smul_fst, ← e, ← hVK, smul_eq_mul,
      ENNReal.toReal_inv]
    field_simp [(ENNReal.toReal_pos hvol.ne' hfin).ne']
  have hsg : IntegrableOn (fun s => s * g s) (Icc m M) :=
    hgi.continuousOn_mul continuousOn_id isCompact_Icc
  have hkey : ∫ s in Icc m M, (s - (2 * m + M) / 3) * g s =
      V * ((centroid K).1 - (2 * m + M) / 3) := by
    have : (fun s => (s - (2 * m + M) / 3) * g s) =
        fun s => s * g s - (2 * m + M) / 3 * g s := by funext s; ring
    rw [this, integral_sub hsg (hgi.const_mul _), integral_const_mul, ← hc1, ← hV]; ring
  obtain ⟨hge, heq⟩ := mean_third_ge hmM (chordLen_concave hKc hK hne)
    (fun x hx => chordLen_nonneg hKc hK hne hx) hgi
  rw [hkey] at hge heq
  refine ⟨hmM, ?_, fun h => ?_⟩
  · have := (mul_nonneg_iff_of_pos_left hVpos).1 hge; linarith
  have hg := heq (by rw [show (centroid K).1 - (2 * m + M) / 3 = 0 by linarith, mul_zero])
  set κ := g ((2 * m + M) / 3) / (M - (2 * m + M) / 3)
  have hκ0 : 0 ≤ κ := div_nonneg (chordLen_nonneg hKc hK hne ⟨by linarith, by linarith⟩)
    (by linarith)
  rcases eq_or_lt_of_le hκ0 with hκ | hκ
  · exfalso
    have : V = 0 := by
      rw [hV, integral_Icc_eq_integral_Ioo]
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      show chordLen K s = 0
      rw [hg s hs, ← hκ, zero_mul]
    linarith
  exact isTriangle_of_chordLen hKc hK hne hmM hκ hg

end Core

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The uniform distribution is equivariant under invertible linear maps. -/
lemma unifSet_image (f : E →ₗ[ℝ] E) (hf : LinearMap.det f ≠ 0) (K : Set E) :
    unifSet (f '' K) = (unifSet K).map f := by
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  set D := ENNReal.ofReal |LinearMap.det f|
  have hD0 : D ≠ 0 := by simp [D, hf]
  have hDt : D ≠ ⊤ := ENNReal.ofReal_ne_top
  ext S hS
  rw [Measure.map_apply hfm hS]
  simp only [unifSet, smul_apply, smul_eq_mul, Measure.restrict_apply hS,
    Measure.restrict_apply (hS.preimage hfm)]
  rw [← image_preimage_inter, Measure.addHaar_image_linearMap, Measure.addHaar_image_linearMap,
    ENNReal.mul_inv (Or.inl hD0) (Or.inl hDt), mul_mul_mul_comm, ENNReal.inv_mul_cancel hD0 hDt,
    one_mul]

/-- The centroid is equivariant under invertible linear maps. -/
lemma centroid_image (f : E →ₗ[ℝ] E) (hf : LinearMap.det f ≠ 0) {K : Set E} (hK : IsCompact K)
    (hpos : 0 < volume K) : centroid (f '' K) = f (centroid K) := by
  have e := integral_map (μ := unifSet K) (φ := f)
    f.continuous_of_finiteDimensional.aemeasurable (f := id) aestronglyMeasurable_id
  simp only [id] at e
  rw [centroid, unifSet_image f hf K, e]
  exact (LinearMap.toContinuousLinearMap f).integral_comp_comm (unifSet_integrable hK hpos)

end Transfer

section Directions

variable {K : Set (ℝ × ℝ)}

/-- The linear form `x ↦ p₁ x₁ + p₂ x₂`. -/
def lin (p x : ℝ × ℝ) : ℝ := p.1 * x.1 + p.2 * x.2

/-- The map `x ↦ (p₁ x₁ + p₂ x₂, -p₂ x₁ + p₁ x₂)`, a rotation followed by a homothety. -/
def rotL (p : ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
  (p.1 • LinearMap.fst ℝ ℝ ℝ + p.2 • LinearMap.snd ℝ ℝ ℝ).prod
    ((-p.2) • LinearMap.fst ℝ ℝ ℝ + p.1 • LinearMap.snd ℝ ℝ ℝ)

/-- Its inverse for `p ≠ 0`. -/
def rotInv (p : ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
  (p.1 ^ 2 + p.2 ^ 2)⁻¹ • ((p.1 • LinearMap.fst ℝ ℝ ℝ - p.2 • LinearMap.snd ℝ ℝ ℝ).prod
    (p.2 • LinearMap.fst ℝ ℝ ℝ + p.1 • LinearMap.snd ℝ ℝ ℝ))

lemma rotL_apply (p x : ℝ × ℝ) : rotL p x = (lin p x, -p.2 * x.1 + p.1 * x.2) := rfl

lemma rotInv_apply (p x : ℝ × ℝ) : rotInv p x =
    (p.1 ^ 2 + p.2 ^ 2)⁻¹ • (p.1 * x.1 - p.2 * x.2, p.2 * x.1 + p.1 * x.2) := rfl

lemma normSq_pos {p : ℝ × ℝ} (hp : p ≠ 0) : 0 < p.1 ^ 2 + p.2 ^ 2 := by
  rcases p with ⟨a, b⟩
  have : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h; exact hp (by simp [h.1, h.2])
  rcases this with h | h
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity

lemma rotInv_rotL {p : ℝ × ℝ} (hp : p ≠ 0) (x : ℝ × ℝ) : rotInv p (rotL p x) = x := by
  have := (normSq_pos hp).ne'
  rw [rotInv_apply, rotL_apply]
  ext <;> simp only [lin, Prod.smul_mk, smul_eq_mul] <;> field_simp <;> ring

lemma rotL_rotInv {p : ℝ × ℝ} (hp : p ≠ 0) (x : ℝ × ℝ) : rotL p (rotInv p x) = x := by
  have := (normSq_pos hp).ne'
  rw [rotInv_apply, rotL_apply]
  ext <;> simp only [lin, Prod.smul_mk, smul_eq_mul] <;> field_simp <;> ring

lemma det_rotL_ne {p : ℝ × ℝ} (hp : p ≠ 0) : LinearMap.det (rotL p) ≠ 0 := by
  have h : rotL p ∘ₗ rotInv p = LinearMap.id := LinearMap.ext (rotL_rotInv hp)
  have := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_id] at this
  exact left_ne_zero_of_mul_eq_one this

/-- **The planar case in one direction.** For a compact convex `K ⊂ ℝ²` of positive area with
centroid `c` and a direction `p ≠ 0`, the linear form `u = ⟨p, ·⟩` has `min_K u < max_K u`,
`u(c) - min_K u ≥ (max_K u - min_K u)/3`, and equality forces `K` to be a triangle. -/
theorem dir_core (hKc : Convex ℝ K) (hK : IsCompact K) (hvol : 0 < volume K) {p : ℝ × ℝ}
    (hp : p ≠ 0) :
    sInf (lin p '' K) < sSup (lin p '' K) ∧
      (sSup (lin p '' K) - sInf (lin p '' K)) / 3 ≤ lin p (centroid K) - sInf (lin p '' K) ∧
      (lin p (centroid K) - sInf (lin p '' K) = (sSup (lin p '' K) - sInf (lin p '' K)) / 3 →
        IsTriangle K) := by
  set K' := rotL p '' K
  have hdet := det_rotL_ne hp
  have hK'c : Convex ℝ K' := hKc.linear_image _
  have hK' : IsCompact K' := hK.image (rotL p).continuous_of_finiteDimensional
  have hvol' : 0 < volume K' := by
    rw [Measure.addHaar_image_linearMap]
    exact ENNReal.mul_pos (by simp [hdet]) hvol.ne'
  have hproj : Prod.fst '' K' = lin p '' K := by rw [image_image]; rfl
  have hc : (centroid K').1 = lin p (centroid K) := by
    rw [centroid_image _ hdet hK hvol]; rfl
  obtain ⟨h1, h2, h3⟩ := fst_core hK'c hK' hvol'
  simp only [projLo, projHi, hproj, hc] at h1 h2 h3
  refine ⟨h1, h2, fun h => ?_⟩
  obtain ⟨A, B, C, hT⟩ := h3 h
  refine ⟨rotInv p A, rotInv p B, rotInv p C, ?_⟩
  have hKK : K = rotInv p '' K' := by
    rw [image_image]; simp only [rotInv_rotL hp, image_id']
  rw [hKK, hT, LinearMap.image_convexHull, image_insert_eq, image_insert_eq, image_singleton]

lemma strongDual_eq_lin (u : StrongDual ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    u x = lin (u (1, 0), u (0, 1)) x := by
  have : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, lin]; ring

lemma exists_min_lin (hK : IsCompact K) (hne : K.Nonempty) (p : ℝ × ℝ) :
    ∃ y ∈ K, sInf (lin p '' K) = lin p y ∧ ∀ x ∈ K, lin p x ≤ sSup (lin p '' K) := by
  have hc : Continuous (lin p) := by unfold lin; fun_prop
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  refine ⟨y, hy, IsLeast.csInf_eq ⟨⟨y, hy, rfl⟩, ?_⟩, fun x hx =>
    le_csSup (hK.image hc).bddAbove ⟨x, hx, rfl⟩⟩
  rintro _ ⟨z, hz, rfl⟩; exact hmin hz

lemma lin_smul (r : ℝ) (p x : ℝ × ℝ) : lin (r • p) x = r * lin p x := by
  simp only [lin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **Lemma 89, planar case (`as(K) < 2` unless `K` is a triangle).** Let `K ⊂ ℝ²` be compact
and convex with positive area and centroid `c`. Then `as(K) ≤ 2` (the theorem of Minkowski and
Radon in the plane), and if `K` is not a triangle there is `a < 2` with `as(K) ≤ a`. The
maximum over the directions is attained by compactness of the unit circle; in a direction
where the ratio is `2`, the projection of `U(K)`, with density proportional to the chord length,
has mean `1/3` of the way, the chord length is affine (`mean_third_ge`) and `K` is a triangle
(`isTriangle_of_chordLen`). -/
theorem planar_asym (hKc : Convex ℝ K) (hK : IsCompact K) (hvol : 0 < volume K) :
    AsymLE K (centroid K) 2 ∧
      (¬ IsTriangle K → ∃ a : ℝ, 0 < a ∧ a < 2 ∧ AsymLE K (centroid K) a) := by
  have hne : K.Nonempty := nonempty_of_measure_ne_zero hvol.ne'
  set c := centroid K
  refine ⟨fun u x hx => ?_, fun hT => ?_⟩
  · set p : ℝ × ℝ := (u (1, 0), u (0, 1))
    by_cases hp : p = 0
    · refine ⟨x, hx, ?_⟩
      rw [strongDual_eq_lin u x, strongDual_eq_lin u c]
      have h1 : u (1, 0) = 0 := congrArg Prod.fst hp
      have h2 : u (0, 1) = 0 := congrArg Prod.snd hp
      simp [lin, h1, h2]
    obtain ⟨y, hy, hinf, hsup⟩ := exists_min_lin hK hne p
    obtain ⟨-, h2, -⟩ := dir_core hKc hK hvol hp
    refine ⟨y, hy, ?_⟩
    rw [strongDual_eq_lin u x, strongDual_eq_lin u c, strongDual_eq_lin u y]
    have := hsup x hx
    rw [hinf] at h2; linarith
  -- compactness of the unit circle
  set S1 : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}
  have hS1 : IsCompact S1 := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq (by fun_prop) continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset fun p hp => ?_
    simp only [S1, mem_ofPred_eq] at hp
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff]
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hS1ne : ∀ p ∈ S1, p ≠ 0 := by
    intro p hp h; simp [S1, h] at hp
  have hunc : Continuous (Function.uncurry fun (p x : ℝ × ℝ) => lin p x) := by
    simp only [lin]; fun_prop
  set sup : ℝ × ℝ → ℝ := fun p => sSup ((fun x => lin p x) '' K)
  set inf : ℝ × ℝ → ℝ := fun p => sInf ((fun x => lin p x) '' K)
  have hsupc : Continuous sup := hK.continuous_sSup hunc
  have hinfc : Continuous inf := hK.continuous_sInf hunc
  have hlinc : Continuous fun p => lin p c := by unfold lin; fun_prop
  set F : ℝ × ℝ → ℝ := fun p => (sup p - lin p c) / (lin p c - inf p)
  have hden : ∀ p ∈ S1, 0 < lin p c - inf p := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := dir_core hKc hK hvol (hS1ne p hp)
    simp only [inf]; linarith
  have hFc : ContinuousOn F S1 :=
    ((hsupc.sub hlinc).continuousOn).div ((hlinc.sub hinfc).continuousOn)
      fun p hp => (hden p hp).ne'
  have hF2 : ∀ p ∈ S1, F p < 2 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := dir_core hKc hK hvol (hS1ne p hp)
    have hne3 : lin p c - inf p ≠ (sup p - inf p) / 3 := fun h => hT (h3 h)
    have hlt : (sup p - inf p) / 3 < lin p c - inf p := lt_of_le_of_ne h2 (Ne.symm hne3)
    simp only [F]; rw [div_lt_iff₀ (hden p hp)]; linarith
  obtain ⟨p₀, hp₀, hmax⟩ := hS1.exists_isMaxOn ⟨(1, 0), by simp [S1]⟩ hFc
  refine ⟨max 1 (F p₀), by positivity, max_lt (by norm_num) (hF2 p₀ hp₀), fun u x hx => ?_⟩
  set p : ℝ × ℝ := (u (1, 0), u (0, 1))
  by_cases hp : p = 0
  · refine ⟨x, hx, ?_⟩
    rw [strongDual_eq_lin u x, strongDual_eq_lin u c]
    have h1 : u (1, 0) = 0 := congrArg Prod.fst hp
    have h2 : u (0, 1) = 0 := congrArg Prod.snd hp
    simp [lin, h1, h2]
  set r := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 (normSq_pos hp)
  set q := r⁻¹ • p
  have hq : q ∈ S1 := by
    simp only [S1, mem_ofPred_eq, q, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow,
      ← mul_add]
    rw [inv_pow, Real.sq_sqrt (normSq_pos hp).le, inv_mul_cancel₀ (normSq_pos hp).ne']
  obtain ⟨y, hy, hinf, hsup⟩ := exists_min_lin hK hne q
  refine ⟨y, hy, ?_⟩
  rw [strongDual_eq_lin u x, strongDual_eq_lin u c, strongDual_eq_lin u y]
  change lin p x - lin p c ≤ _ * (lin p c - lin p y)
  have e : ∀ z, lin p z = r * lin q z := fun z => by
    simp only [q, lin_smul]; field_simp
  rw [e x, e c, e y]
  have hFq : F q ≤ max 1 (F p₀) := (hmax hq).trans (le_max_right _ _)
  have hd := hden q hq
  have hxs := hsup x hx
  have key : lin q x - lin q c ≤ max 1 (F p₀) * (lin q c - lin q y) := by
    have e : sup q - lin q c = F q * (lin q c - inf q) := by
      simp only [F]; field_simp
    simp only [sup, inf] at e hd
    rw [hinf] at e hd
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hr.le]

/-- **Lemma 89 for `n = 3` in the plane.** If `K ⊂ ℝ²` is a compact convex body that is not a
triangle and contains the ball `c + sB` about its centroid, the room `ρ₀`, `α` of Lemma 89 exists
for `n = 3`, for any additive Haar measure `μ`. -/
theorem room_planar_three (hKc : Convex ℝ K) (hK : IsCompact K) (hvol : 0 < volume K)
    (hT : ¬ IsTriangle K) {s : ℝ} (hs : 0 < s) (hball : closedBall (centroid K) s ⊆ K)
    (μ : Measure (ℝ × ℝ)) [μ.IsAddHaarMeasure] :
    ∃ ρ₀ > 0, ∃ α : ENNReal, 0 < α ∧ ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ p : ℝ × ℝ,
      (∃ x ∈ K, dist p x ≤ ρ₀) →
      centroid K - ((3 : ℕ) - 1 : ℝ)⁻¹ • (p - centroid K) ∈ interior (innerBody K (2 * ρ)) ∧
      α ≤ Measure.pi (fun _ : Fin (3 - 2) => μ)
        {y | (∀ i, y i ∈ innerBody K (2 * ρ)) ∧
          ((3 : ℕ) : ℝ) • centroid K - p - ∑ i, y i ∈ innerBody K (2 * ρ)} := by
  obtain ⟨a, ha, ha2, hasym⟩ := (planar_asym hKc hK hvol).2 hT
  exact room le_rfl hKc hK.isClosed hs hball ha (by norm_num; linarith) hasym μ

end Directions

end Room

end Mixes
